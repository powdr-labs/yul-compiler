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
  -- `exp` is really `10 + 50·(exponent bytes)`; this static underestimate is
  -- safe because candidates are only ever compared against the ORIGINAL window
  -- (strictly-cheaper, never accepted on estimated ties), so a candidate that
  -- recomputes an `exp` instead of reusing it scores no better here.
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
reach (the latter guarantees the untouched REST below the window lines up).
Requiring equal `inputs` is conservative — it rejects a candidate that
legitimately reaches FEWER below-window slots than the original. A future
relaxation would normalize both states to the max input reach (materializing the
extra deep leaves as identities) before comparing. -/
def symStateBeq (a b : SymState) : Bool :=
  a.inputs == b.inputs && Term.beqList a.stack b.stack

/-! ### The scheduler (untrusted) + validation gate -/

/-! ### The DAG rescheduler (untrusted)

Correctness never depends on any of this — the validation gate below re-checks
every candidate. The scheduler targets canonical→canonical windows (`m = k`,
non-changed slots are identity), which is exactly the shape the backend emits for
straight-line reassignment blocks (e.g. TickMath's log2 section, where symbolic
execution collapses 14 store/reload cycles into one DAG per updated slot). It
computes each *changed* slot's collapsed DAG once (with common-subexpression
sharing via the running model stack, consuming shared values in place) and stores
it, instead of the backend's per-statement DUP/store/reload. On any difficulty
(a move/permutation, a needed reach past `DUP16`/`SWAP16`, `m ≠ k`) it returns
`none` and the original window is kept. -/

/-! Structural size of a term (for a topological fuel bound). -/
mutual
def Term.size : Term → Nat
  | .inp _ | .lit _ => 1
  | .app _ args => 1 + Term.sizeList args
def Term.sizeList : List Term → Nat
  | [] => 0
  | x :: xs => Term.size x + Term.sizeList xs
end

/-- First index of a structurally-equal term in the model stack. -/
def findIdxBeq (t : Term) : List Term → Option Nat
  | [] => none
  | x :: xs => if Term.beq t x then some 0 else (findIdxBeq t xs).map (· + 1)

/-- Emitter state: emitted code (reversed) and the running symbolic model. -/
structure ES where
  rcode : List Asm
  model : SymState

def ES.code (es : ES) : List Asm := es.rcode.reverse

/-- Append one instruction, keeping the model in lockstep via `symStep`. -/
def emit (es : ES) (i : Asm) : Option ES :=
  (symStep es.model i).map (fun m => ⟨i :: es.rcode, m⟩)

/-! `genValue` emits code leaving the value of `t` on top of the model stack
(model height +1). It reuses any structurally-equal value already on the stack
(`DUP`), otherwise builds it: literals via `PUSH`, `app` by emitting its
arguments (reversed, so the first argument ends on top) then the op. It fails
past the `DUP16` reach or on an input leaf that is not present (should not occur
from the seeded model). -/
mutual
def genValue : Nat → ES → Term → Option ES
  | 0, _, _ => none
  | fuel + 1, es, t =>
      match findIdxBeq t es.model.stack with
      | some d => if h : d < 16 then emit es (.dup ⟨d, h⟩) else none
      | none =>
          match t with
          | .lit v => emit es (.push v)
          | .inp _ => none
          | .app op args =>
              match genArgs fuel es args with
              | some es' => emit es' (.op op)
              | none => none
/-- Build an op's arguments so the top-n become `[arg0, …, arg(n-1)]`. The
deepest operand `arg(n-1)` is built first; if it is an already-computed
INTERMEDIATE (`app`) sitting on top of the model, it is CONSUMED IN PLACE (no
`DUP`) — the op will take it as its deepest operand — instead of copied. This is
the chain-accumulator win: `mul(r,r)` on an intermediate `r` becomes `dup;mul`
(1 DUP, `r` consumed) instead of two DUPs leaving `r` behind. Only intermediates
are consumed this way, so the fixed `k`-input cleanup is unaffected; the gate
rejects any consume that was not actually a last use. -/
def genArgs : Nat → ES → List Term → Option ES
  | 0, _, _ => none
  | fuel + 1, es, args =>
      match args.reverse with
      | [] => some es
      | first :: restRev =>
          let firstES :=
            match first, es.model.stack.head? with
            | .app _ _, some h => if Term.beq first h then some es else genValue fuel es first
            | _, _ => genValue fuel es first
          match firstES with
          | none => none
          | some e => restRev.foldlM (fun acc a => genValue fuel acc a) e
end

/-- Emit `n` pops. -/
def emitPops : ES → Nat → Option ES
  | es, 0 => some es
  | es, n + 1 => (emit es .pop).bind (fun es' => emitPops es' n)

/-- The window's inputs sit below the freshly-built `m` outputs. Remove them
with `swap⟨m-1⟩; pop`, repeated `b` times: each iteration deletes the shallowest
input and rotates the top-`m` block left by one, so after `b = k` iterations the
inputs are gone and the outputs are rotated left by `k` (which the builder
pre-compensates). Requires `0 < m ≤ 16`. -/
def emitCleanup (m : Nat) : ES → Nat → Option ES
  | es, 0 => some es
  | es, b + 1 =>
      if h : 0 < m ∧ m - 1 < 16 then
        match emit es (.swap ⟨m - 1, h.2⟩) with
        | some es' =>
            match emit es' .pop with
            | some es'' => emitCleanup m es'' b
            | none => none
        | none => none
      else none

/-- The DAG rescheduler proper. Rebuilds the window's `m` symbolic outputs from
its `k` inputs, with common-subexpression sharing inside each output (so a
collapsed reassignment chain is computed once instead of via the backend's
per-statement store/reload), then removes the inputs. Outputs are built
pre-rotated by `k mod m` so the `emitCleanup` rotation lands them in order. -/
def scheduleWindowReal (target : SymState) : Option (List Asm) :=
  let k := target.inputs
  let T := target.stack
  let m := T.length
  if m > 16 then none else
  let fuel := 8 * (Term.sizeList T) + 100
  let init : ES := ⟨[], { stack := (List.range k).map Term.inp, inputs := k }⟩
  if m == 0 then
    (emitPops init k).map ES.code
  else
    let rot := k % m
    -- build O[m-1] (deepest) first … O[0] (top) last, where the cleanup rotation
    -- makes the final top-m equal T:  O[j] = T[(j + (m - rot)) % m].
    match (List.range m).reverse.foldlM
        (fun es j => genValue fuel es ((T[(j + (m - rot)) % m]?).getD (.lit 0))) init with
    | none => none
    | some es1 => (emitCleanup m es1 k).map ES.code

/-- The untrusted rescheduler: given the window's symbolic output, propose a
cheaper instruction sequence, or `none` to keep the original. Correctness never
depends on it, only on the validation gate below. -/
def scheduleWindow (target : SymState) : Option (List Asm) := scheduleWindowReal target

/-- Skip windows longer than this. `Term` is a tree, so a long run of squarings
(`r := shr(127, mul(r,r))`, no barrier between blocks) would build terms of size
~2^(#blocks); capping the window length splits such a run into per-block windows
(where the backend's per-statement DUP/store/reload waste actually lives) and
keeps `symExec`/`Term.beq`/`Term.size` cost bounded, so the pass adds only
bounded compile time. -/
def maxWindowLen : Nat := 48

/-- Bail out of scheduling a window whose symbolic output DAG exceeds this many
nodes (belt-and-suspenders against tree blowup within the length cap). -/
def maxTermNodes : Nat := 4096

/-- Optimize one extracted window: keep the original unless a proposed candidate
validates (same symbolic state), is strictly cheaper, and does not grow bytes. -/
def optimizeWindow (w : List Asm) : List Asm :=
  if w.length > maxWindowLen then w else
  match symExec w with
  | none => w
  | some target =>
      if Term.sizeList target.stack > maxTermNodes then w else
      match scheduleWindow target with
      | none => w
      | some cand =>
          match symExec cand with
          | some tcand =>
              -- Accept only a translation-validated candidate (same symbolic
              -- state, incl. equal input reach) that is STRICTLY cheaper than the
              -- ORIGINAL and no larger in bytes. Comparing only against the
              -- original (never accepting estimated ties) is what makes the
              -- `opGas` `exp` underestimate safe.
              if symStateBeq tcand target
                  && windowGas cand < windowGas w
                  && codeSize cand ≤ codeSize w then cand else w
          | none => w

/-- Split the program into maximal windows and non-window instructions, running
`optimizeWindow` on each window. Fuel-bounded for a trivial termination
argument; the bound `p.length + 1` always suffices. -/
def scheduleAsmFuel : Nat → List Asm → List Asm
  | 0, p => p
  | _ + 1, [] => []
  | fuel + 1, i :: rest =>
      if schedulable i then
        -- Cut a maximal schedulable run, but CAP its length so a long run (e.g.
        -- the whole log2 squaring section) is split into bounded chunks that are
        -- each scheduled — rather than skipped for being too big.
        let win := ((i :: rest).takeWhile schedulable).take maxWindowLen
        let tail := (i :: rest).drop win.length
        optimizeWindow win ++ scheduleAsmFuel fuel tail
      else
        i :: scheduleAsmFuel fuel rest

/-- The Asm-level window scheduler run by `compile`, after `optimizeAsm` and
before the `stackOK2` overflow gate (so the bound is checked on the final code).
Total; on any doubt it returns its input unchanged. -/
def scheduleAsm (p : List Asm) : List Asm := scheduleAsmFuel (p.length + 1) p

end YulEvmCompiler.Schedule
