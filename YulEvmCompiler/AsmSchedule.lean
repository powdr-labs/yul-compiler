import YulEvmCompiler.Asm
set_option warningAsError true
/-!
# YulEvmCompiler.AsmSchedule

**PROTOTYPE, UNPROVEN.** An Asm→Asm *per-window operand-stack scheduler*,
designed around a translation-validation architecture so that soundness later
reduces to a single lemma about the symbolic executor (not about the
scheduler's cleverness).

The pipeline (`scheduleAsm`) splits the program into maximal **windows** —
straight-line runs of pure, label-free, jump-free instructions (`push`, pure
`op`, `dup`, `swap`, `pop`). Everything outside a window is copied verbatim, so
labels, jumps, calls, and every effectful op are untouched.

For each window it:

1. runs a **symbolic executor** (`symExec`) that evaluates the window over a
   symbolic stack (`Term` DAGs over input leaves `inp i` and literal words),
   producing a `SymState` — the output stack as DAG terms plus `inputs`, the
   number of below-window slots the window reaches into;
2. asks an **untrusted scheduler** (`scheduleWindow`) for a cheaper candidate;
3. **validates** the candidate by re-running `symExec` on it and accepting only
   if the resulting `SymState` is *syntactically equal* (same terms, same
   `inputs`) — this is what guarantees the net stack transformation is
   identical, including that the untouched REST below the window is preserved
   (equal `inputs` ⇒ equal split point);
4. additionally requires the candidate to be strictly cheaper by the gas model
   **and** no larger in bytes (so `codeSize` never grows and every lowering /
   `wfCheck` size invariant is preserved).

Because acceptance is gated on validation + strict gas improvement + size
non-growth, the pass is behavior-preserving (modulo the future executor
soundness lemma) and can never regress a window: on any doubt it keeps the
original. Depth limits are enforced by construction — `dup`/`swap` indices are
`Fin 16`, so a scheduler needing a deeper reach simply cannot emit it.

## Future soundness (the one lemma)

`symExec_sound`: if `symExec w = some s`, then for any concrete `AVal` stack
`ι ++ REST` with `ι.length = s.inputs`, `ASteps prog ⟨w ++ c, ι ++ REST, yst⟩
⟨c, realize s.stack ι ++ REST, yst⟩` where `realize` substitutes `inp i ↦ ι[i]`
and evaluates pure ops via `stepOp`. Given that, `symExec w = symExec w'`
(structurally) implies `w` and `w'` have the same net transformation on every
concrete stack, hence are interchangeable inside `prog` — the translation
validation is discharged once, for the executor, independent of the scheduler.
-/

namespace YulEvmCompiler.Schedule

open YulSemantics.EVM (U256 Op)

/-! ### Symbolic terms -/

/-- A symbolic stack value: an input leaf (`inp i` = the `i`-th slot the window
reaches into, counted from the incoming top), a literal word, or a pure op
applied to argument terms (first argument = top-of-stack at the op). -/
inductive Term
  | inp (i : Nat)
  | lit (v : U256)
  | app (op : Op) (args : List Term)

mutual
/-- Structural equality on `Term`. -/
def Term.beq : Term → Term → Bool
  | .inp a,      .inp b      => a == b
  | .lit a,      .lit b      => a == b
  | .app o1 as1, .app o2 as2 => o1 == o2 && Term.beqList as1 as2
  | _,           _           => false
/-- Structural equality on term lists. -/
def Term.beqList : List Term → List Term → Bool
  | [],      []      => true
  | x :: xs, y :: ys => Term.beq x y && Term.beqList xs ys
  | _,       _       => false
end

instance : BEq Term := ⟨Term.beq⟩

/-! ### Op purity / arity

Only deterministic, state-independent, single-output ops are admitted into a
window; every other `op` (memory, storage, env, hashing, calls, halts) is a
window barrier. The arities mirror `YulSemantics.EVM.stepOp` (`bin`/`ter`/`un`).
-/

/-- Argument count of a pure op, or `none` if the op is not window-admissible. -/
def pureArity : Op → Option Nat
  | .add | .sub | .mul | .div | .sdiv | .mod | .smod | .exp | .signextend
  | .lt | .gt | .slt | .sgt | .eq
  | .and | .or | .xor | .byte | .shl | .shr | .sar => some 2
  | .addmod | .mulmod => some 3
  | .clz | .iszero | .not => some 1
  | _ => none

/-- A rough per-instruction gas cost for choosing between candidates. For pure
windows this is the exact runtime gas of one execution (no dynamic/memory
costs), so minimizing it minimizes real per-execution gas. -/
def opGas : Op → Nat
  | .mul | .div | .sdiv | .mod | .smod | .signextend => 5
  | .addmod | .mulmod => 8
  | .exp => 10
  | _ => 3

/-- Per-instruction gas (window instructions; others default to 3). -/
def instrGas : Asm → Nat
  | .push v => if v = 0 then 2 else 3
  | .op yop => opGas yop
  | .dup _ => 3
  | .swap _ => 3
  | .pop => 2
  | _ => 3

/-- Total gas of an instruction sequence under `instrGas`. -/
def windowGas (w : List Asm) : Nat := (w.map instrGas).sum

/-- Is an instruction window-admissible (pure, straight-line)? -/
def schedulable : Asm → Bool
  | .push _ | .dup _ | .swap _ | .pop => true
  | .op yop => (pureArity yop).isSome
  | _ => false

/-! ### Symbolic executor -/

/-- The symbolic state during window execution: the realized stack (top first)
and the number of input leaves materialized so far (= how deep the window has
reached below its start). -/
structure SymState where
  stack : List Term
  inputs : Nat

/-- Materialize input leaves at the bottom until the realized stack has at least
`need` elements, so an access at depth `need-1` is in range. Growth increments
`inputs`. -/
def pad (s : SymState) (need : Nat) : SymState :=
  if s.stack.length ≥ need then s
  else
    let extra := need - s.stack.length
    { stack := s.stack ++ (List.range extra).map (fun j => Term.inp (s.inputs + j)),
      inputs := s.inputs + extra }

/-- One symbolic step. Mirrors `AStep`: `push`/`pop`/`dup`/`swap` shuffle the
stack; a pure `op` consumes `k` argument terms (first = top) and pushes one
`app` term. Any non-admissible instruction yields `none` (should not occur
inside an extracted window). -/
def symStep (s : SymState) : Asm → Option SymState
  | .push v => some { s with stack := .lit v :: s.stack }
  | .pop =>
      let s := pad s 1
      some { s with stack := s.stack.drop 1 }
  | .dup ⟨n, _⟩ =>
      let s := pad s (n + 1)
      match s.stack[n]? with
      | some t => some { s with stack := t :: s.stack }
      | none => none
  | .swap ⟨n, _⟩ =>
      let s := pad s (n + 2)
      match s.stack[0]?, s.stack[n + 1]? with
      | some a, some b => some { s with stack := (s.stack.set 0 b).set (n + 1) a }
      | _, _ => none
  | .op yop =>
      match pureArity yop with
      | some k =>
          let s := pad s k
          some { stack := .app yop (s.stack.take k) :: s.stack.drop k,
                 inputs := s.inputs }
      | none => none
  | _ => none

/-- Run a window symbolically from the empty stack. `none` if it contains any
non-admissible instruction. -/
def symExec (w : List Asm) : Option SymState :=
  w.foldlM symStep { stack := [], inputs := 0 }

/-- Structural equality of symbolic states: same output terms and same input
reach (the latter guarantees the untouched REST below the window lines up). -/
def symStateBeq (a b : SymState) : Bool :=
  a.inputs == b.inputs && Term.beqList a.stack b.stack

/-! ### The scheduler (untrusted) + validation gate -/

/-- The untrusted rescheduler: given the window's symbolic output, propose a
cheaper instruction sequence, or `none` to keep the original. **Identity for
now** (commit 1: infrastructure + provable core). A real DAG scheduler replaces
this; correctness never depends on it, only on the validation gate below. -/
def scheduleWindow (_target : SymState) : Option (List Asm) := none

/-- Optimize a single extracted window: keep the original unless a proposed
candidate validates (same symbolic state), is strictly cheaper, and does not
grow bytes. -/
def optimizeWindow (w : List Asm) : List Asm :=
  match symExec w with
  | none => w
  | some target =>
      match scheduleWindow target with
      | none => w
      | some cand =>
          match symExec cand with
          | some tcand =>
              if symStateBeq tcand target
                  && windowGas cand < windowGas w
                  && codeSize cand ≤ codeSize w then
                cand
              else w
          | none => w

/-- Split the program into maximal windows and non-window instructions, running
`optimizeWindow` on each window. Fuel-bounded for a trivial termination
argument; the bound `p.length + 1` always suffices. -/
def scheduleAsmFuel : Nat → List Asm → List Asm
  | 0, p => p
  | _ + 1, [] => []
  | fuel + 1, i :: rest =>
      if schedulable i then
        let win := (i :: rest).takeWhile schedulable
        let tail := (i :: rest).dropWhile schedulable
        optimizeWindow win ++ scheduleAsmFuel fuel tail
      else
        i :: scheduleAsmFuel fuel rest

/-- The Asm-level window scheduler run by `compile`, after `optimizeAsm` and
before the `stackOK2` overflow gate (so the bound is checked on the final code).
Total; on any doubt it returns its input unchanged. -/
def scheduleAsm (p : List Asm) : List Asm := scheduleAsmFuel (p.length + 1) p

end YulEvmCompiler.Schedule
