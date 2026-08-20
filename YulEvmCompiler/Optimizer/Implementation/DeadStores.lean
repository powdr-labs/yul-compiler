import YulEvmCompiler.Optimizer.Implementation.DeadPure
import YulEvmCompiler.Optimizer.Implementation.StorageForwardResolve
import YulEvmCompiler.Optimizer.Implementation.StructurePasses
import YulEvmCompiler.Optimizer.Implementation.CoalesceCopies
import YulEvmCompiler.Optimizer.Implementation.DeadStoresSound
set_option warningAsError true
/-!
# YulEvmCompiler.Optimizer.Implementation.DeadStores

**Dead-store elimination** — the write-side complement of `DeadPure`.

`DeadPure` removes a *binding* whose name is never mentioned again. The
dominant residue in the Yul that actually reaches the backend is the opposite
shape: a name that **is** mentioned again, but whose next occurrence is a
*write*. Two rewrites, on a name declared by an earlier `let` of the very same
statement sequence:

* **R1 (dead assignment)** `x := e` is deleted when `x` is dead from there on
  and `e` is total and state-preserving (`alwaysEval`);
* **R2 (dead initialiser)** `let x := e` becomes `let x` under the same
  conditions — the binder has to survive, because a later assignment refers to
  it. That is exactly the case `DeadPure` cannot take.

## Why this is where the gas is

`compileStmt` charges `compileAssigns`' `swap_k; pop` for every `.assign`, so a
dead `x := <lit>` is `push; swap; pop` = 7-8 gas and a dead `x := <var>` is
`dup; swap; pop` = 8 gas. Opcode attribution against solc (`traceSolidityGas`)
puts `POP` at 70-78% of the two largest Aave v4 gaps, and a backward liveness
over the Yul that actually compiles traces most of it to dead stores
**created by `stackLayoutBlock`**: `iterateStackLayout`'s slot reuse and
`StackV2`'s live-range splitting introduce `x := y` copies and shared slots,
and — because the layout pass runs *after* the whole optimizer pipeline, inside
`compileSource`'s `tryLayouts` — nothing runs behind them. 43 of the surviving
dead stores in `PositionStatusMap` sit inside its 10,000-trip loops.

## The deadness test, and why scope exit is free

`dsDead x rest` walks the *remainder of the current sequence* forward and
answers "is `x`'s value here unobservable?":

* a write to `x` (`.assign` targets, before any read) ⇒ dead;
* any read of `x` ⇒ not dead;
* end of the sequence, or a `break`/`continue`/`leave` ⇒ **dead**;
* a compound statement mentioning `x` at all ⇒ not dead (conservative: the
  branch may or may not run, so a write inside it cannot kill `x`).

The third clause is the reason this pass needs no escape-set bookkeeping. Both
rewrites fire only on a name in `owned` — declared by an earlier `letDecl` of
this same sequence — and such a name is removed by the sequence's `restore` at
*every* exit, normal or non-local. So a value that survives to the end of the
sequence is not observable, and the `EquivBlock` tier stays reachable for the
same reason it does in `DeadPure`: the difference is confined to bindings the
enclosing block erases.

Requiring `owned` also protects exactly the names that must be protected:
function returns and parameters, `for`-init declarations (loop-carried across
iterations), and anything bound in an ambient environment `EquivBlock`
quantifies over. None of them is declared by a `letDecl` of the sequence being
rewritten.

`for`-`init` sequences are left untouched, mirroring `DeadPure` and `DeadLits`:
their scope spans the whole loop, so the "dies at the end of the sequence"
argument does not apply to them. `bound` is likewise passed into `post`/`body`
unchanged rather than extended with `init`'s declarations: `ForInitEmpty` is a
field of `NormalForm.Normalized`, so on pipeline input there are none, and
extending it would cost exactly the two `forLoop` master-induction cases for no
measured gain.

## What R2 is for

On its own R2 is nearly free: `.letDecl xs none` lowers to one `push 0` per
name, and `Instr.pushMin` makes that a `PUSH0`, so `let x := 0` becomes
`let x` for 0 gas and `let x := y` for 1. R2 also *keeps* the binder, hence
keeps its slot and its scope-exit `pop`. It pays because `FuseDeclAssign.sink`
runs behind it: `let x` plus a later same-level `x := e` with no intervening
mention — exactly `dsDead`'s kill condition — fuses back to `let x := e`,
which removes the `PUSH0`, removes that store's `swap; pop`, and compiles `e`
one slot shallower. So R2 is only wired where `fuseDeclAssign` follows it.

Shadowing is treated as a hard stop (a re-declaration of `x` in `rest` makes
`x` not dead) rather than tracked, so the pass is correct without
`NormalForm.UniqueNames`; on normalized input the case never arises.

## The soundness proof

The pass changes *values*, not the shape of the environment, so the desync it
creates is not `DeadPure`'s insertion relation but the value-change relation
`VChg` of `DeadStoresSound`: two environments sharing a tail of length `k`, with
the same names in the same order above it, differing only at positions holding a
`dead` — and *innermost* — name. Innermost-ness is what survives a write: once
both sides store to `x`, no difference at `x` can remain, so `x` may leave the
dead set (`VChg.set_kill`). `vchgStep` is the frame lemma for it, and the sweep
never rewrites a compound statement, so every compound statement is transported
by that single lemma at *identical* code — no relation on nested syntax, and no
relation on function environments, is needed for the sweep itself.

The proof is then three layers:

* `dsSweep_fwd`/`dsSweep_bwd` — one sequence, by induction on it. `owned` enters
  through `AboveK`: the deleted store's target is above the shared tail, which is
  what `VChg.set_left` needs. `alwaysEval` supplies `dcEvalInv` (the dropped
  right-hand side cannot halt or change state) forwards and `dcEvalRun` (it does
  evaluate) backwards.
* `dsSweep_bequivBlock` — the same sweep as a block. Because the shared tail is
  exactly the block's entry environment, `VChg.restore_eq` makes the two exit
  environments **equal**, so this is a real equivalence and not merely a
  simulation.
* `dsStmt_bequiv`/`dsStmts_bequiv`/… — the recursion into sub-sequences, closed
  under `funDef` by `BEquivBlock.of_stmts_funs`. Everything is stated relative to
  `bound` (`BEquivBlock`), because `alwaysEval`'s variable leaves are only total
  on environments that bind them — the reason `EquivBlock` alone cannot carry a
  rewrite inside a function body (see `DeadPure`'s module docstring).
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM

variable {calls : ExternalCalls} {creates : ExternalCreates} {gasOracle : ExternalGas}

local notation "D" => evmWithExternal calls creates gasOracle

/-! ### The deadness test -/

/-- Is `x`'s current value unobservable over the rest of this sequence? See
the module docstring for the four clauses. -/
def dsDead (x : Ident) : List (Stmt Op) → Bool
  | [] => true
  | .assign ys e :: rest =>
      if exprMentions x e then false
      else if ys.contains x then true
      else dsDead x rest
  | .letDecl ys none :: rest =>
      if ys.contains x then false else dsDead x rest
  | .letDecl ys (some e) :: rest =>
      if exprMentions x e then false
      else if ys.contains x then false
      else dsDead x rest
  | .exprStmt e :: rest =>
      if exprMentions x e then false else dsDead x rest
  | .«break» :: _ => true
  | .«continue» :: _ => true
  | .leave :: _ => true
  | .block body :: rest =>
      if stmtsMentions x body then false else dsDead x rest
  | .cond c body :: rest =>
      if exprMentions x c || stmtsMentions x body then false else dsDead x rest
  | .switch c cases dflt :: rest =>
      if exprMentions x c || casesMentions x cases || optBlockMentions x dflt
      then false else dsDead x rest
  | .forLoop init c post body :: rest =>
      if stmtsMentions x init || exprMentions x c || stmtsMentions x post ||
        stmtsMentions x body then false else dsDead x rest
  -- Dead conservatism, kept for locality of reasoning: a callee environment is
  -- `params.zip argvals ++ bindZeros rets`, so a nested definition can never
  -- read a caller local anyway.
  | .funDef _ ps rs body :: rest =>
      if ps.contains x || rs.contains x || stmtsMentions x body then false
      else dsDead x rest

/-! ### The sequence sweep

`bound` is `DeadPure`'s provably-bound set, threaded along the sequence so
`alwaysEval` can certify variable leaves. `owned` is the set of names declared
by earlier `letDecl`s of *this* sequence — the only names either rewrite may
touch. Compound statements are passed through untouched here; `dsStmt` below
does the recursion. -/
def dsSweep (bound owned : List Ident) : List (Stmt Op) → List (Stmt Op)
  | [] => []
  | .assign [x] e :: rest =>
      if owned.contains x && alwaysEval bound e && dsDead x rest then
        dsSweep bound owned rest
      else .assign [x] e :: dsSweep bound owned rest
  | .letDecl [x] (some e) :: rest =>
      if alwaysEval bound e && dsDead x rest then
        .letDecl [x] none :: dsSweep (x :: bound) (x :: owned) rest
      else .letDecl [x] (some e) :: dsSweep (x :: bound) (x :: owned) rest
  | .letDecl xs v :: rest =>
      .letDecl xs v :: dsSweep (xs ++ bound) (xs ++ owned) rest
  | s :: rest => s :: dsSweep bound owned rest

/-! ### Recursion into every sequence

Each nested sequence is first rewritten recursively, then swept from an
**empty** `owned` (only its own declarations are erased by its own `restore`).
A function body additionally restarts `bound` at the callee's parameters and
returns, which is exactly what the call rule's `callOk` environment binds. -/

mutual

/-- Rewrite a compound statement's sub-sequences, then sweep each of them. -/
def dsStmt (bound : List Ident) : Stmt Op → Stmt Op
  | .block body => .block (dsSweep bound [] (dsStmts bound body))
  | .funDef f ps rs body =>
      .funDef f ps rs (dsSweep (ps ++ rs) [] (dsStmts (ps ++ rs) body))
  | .cond c body => .cond c (dsSweep bound [] (dsStmts bound body))
  | .switch c cases dflt => .switch c (dsCases bound cases) (dsDflt bound dflt)
  | .forLoop init c post body =>
      .forLoop init c (dsSweep bound [] (dsStmts bound post))
        (dsSweep bound [] (dsStmts bound body))
  | s => s

/-- Rewrite each statement of a sequence. -/
def dsStmts (bound : List Ident) : List (Stmt Op) → List (Stmt Op)
  | [] => []
  | s :: rest => dsStmt bound s :: dsStmts bound rest

/-- Rewrite every `switch` case body. -/
def dsCases (bound : List Ident) : List (Literal × Block Op) → List (Literal × Block Op)
  | [] => []
  | (l, b) :: rest => (l, dsSweep bound [] (dsStmts bound b)) :: dsCases bound rest

/-- Rewrite a `switch` default body. -/
def dsDflt (bound : List Ident) : Option (Block Op) → Option (Block Op)
  | none => none
  | some b => some (dsSweep bound [] (dsStmts bound b))

end

/-- One dead-store sweep over a whole block. -/
def dsOnce (b : Block Op) : Block Op :=
  dsSweep [] [] (dsStmts [] b)

/-- `dsDead` deliberately consults the **unrewritten** remainder: a name whose
store this sweep drops was then already unread on *both* sides, which keeps the
soundness relation down to "the two environments differ only on names neither
side reads". The price is that store chains (`y := f(x)` keeps `x` alive until
that store itself goes) need more than one sweep. Iterating the sweep on its own
was measured to gain exactly **zero** gas on Uniswap v4, so it is not iterated
here; the compounding that does pay comes from alternating it with
`fuseDeclAssign`/`coalesceCopies`/`deadPure` in `cleanupAfterLayout` below.

Eliminate dead stores in a top-level block. The whole block must be free
of unresolved `dataoffset`/`datasize` so that layout resolution is the
identity on input and output alike; that is what makes this an object-path
stage (the `StorageForward`/`RejoinPairs` recipe). -/
def deadStoresBlock (b : Block Op) : Block Op :=
  if storageLayoutFreeStmts b then dsOnce b else b

/-! ### Object trees -/

mutual
  /-- Eliminate dead stores in every code block of an object tree. -/
  def deadStoresObject : Object Op → Object Op
    | .mk name code subs segs =>
        .mk name (deadStoresBlock code) (deadStoresObjects subs) segs

  def deadStoresObjects : List (Object Op) → List (Object Op)
    | [] => []
    | o :: os => deadStoresObject o :: deadStoresObjects os
end

/-! ### Soundness -/

/-! ### `dsDead` bookkeeping -/

/-- A kept assignment: its right-hand side never mentions a dead name, and a
dead name the assignment does not write stays dead. -/
theorem dsDead_assign {x : Ident} {ys : List Ident} {e : Expr Op} {rest : List (Stmt Op)}
    (h : dsDead x (.assign ys e :: rest) = true) :
    exprMentions x e = false ∧ (x ∉ ys → dsDead x rest = true) := by
  simp only [dsDead] at h
  split at h
  · exact absurd h (by simp)
  · next hm =>
      refine ⟨by simpa using hm, ?_⟩
      intro hnot
      split at h
      · next hc => exact absurd (by simpa using hc) hnot
      · exact h

/-- A `let` with an initialiser does not shadow or read a dead name. -/
theorem dsDead_letSome {x : Ident} {ys : List Ident} {e : Expr Op} {rest : List (Stmt Op)}
    (h : dsDead x (.letDecl ys (some e) :: rest) = true) :
    exprMentions x e = false ∧ x ∉ ys ∧ dsDead x rest = true := by
  simp only [dsDead] at h
  split at h
  · exact absurd h (by simp)
  · next hm =>
      split at h
      · exact absurd h (by simp)
      · next hc => exact ⟨by simpa using hm, by simpa using hc, h⟩

/-- A bare `let` does not shadow a dead name. -/
theorem dsDead_letNone {x : Ident} {ys : List Ident} {rest : List (Stmt Op)}
    (h : dsDead x (.letDecl ys none :: rest) = true) :
    x ∉ ys ∧ dsDead x rest = true := by
  simp only [dsDead] at h
  split at h
  · exact absurd h (by simp)
  · next hc => exact ⟨by simpa using hc, h⟩

/-- Every other statement shape is passed through: a dead name is unmentioned by
it and stays dead afterwards. -/
theorem dsDead_pass {x : Ident} {s : Stmt Op} {rest : List (Stmt Op)}
    (h : dsDead x (s :: rest) = true)
    (hshape : (∃ b, s = .block b) ∨ (∃ n ps rs b, s = .funDef n ps rs b) ∨
      (∃ c b, s = .cond c b) ∨ (∃ c cs d, s = .switch c cs d) ∨
      (∃ i c p b, s = .forLoop i c p b) ∨ (∃ e, s = .exprStmt e)) :
    stmtMentions x s = false ∧ dsDead x rest = true := by
  rcases hshape with ⟨b, rfl⟩ | ⟨n, ps, rs, b, rfl⟩ | ⟨c, b, rfl⟩ | ⟨c, cs, d, rfl⟩ |
    ⟨i, c, p, b, rfl⟩ | ⟨e, rfl⟩
  · simp only [dsDead] at h
    split at h
    · exact absurd h (by simp)
    · next hm => exact ⟨by simpa [stmtMentions] using hm, h⟩
  · simp only [dsDead] at h
    split at h
    · exact absurd h (by simp)
    · next hm => exact ⟨by simpa [stmtMentions] using hm, h⟩
  · simp only [dsDead] at h
    split at h
    · exact absurd h (by simp)
    · next hm => exact ⟨by simpa [stmtMentions] using hm, h⟩
  · simp only [dsDead] at h
    split at h
    · exact absurd h (by simp)
    · next hm => exact ⟨by simpa [stmtMentions] using hm, h⟩
  · simp only [dsDead] at h
    split at h
    · exact absurd h (by simp)
    · next hm => exact ⟨by simpa [stmtMentions] using hm, h⟩
  · simp only [dsDead] at h
    split at h
    · exact absurd h (by simp)
    · next hm => exact ⟨by simpa [stmtMentions] using hm, h⟩

/-! ### Small execution facts -/

/-- A singleton multi-assignment is a single in-place update. -/
theorem setMany_single (V : VEnv D) (x : Ident) (v : U256) :
    VEnv.setMany V [x] [v] = VEnv.set V x v := rfl

/-- A zero-initialising singleton `let` pushes one binding. -/
theorem bindZeros_single (x : Ident) (V : VEnv D) :
    bindZeros D [x] ++ V = (x, (evmWithExternal calls creates gasOracle).zero) :: V := rfl

/-- A normally-terminating `let` prepends exactly its declared names. -/
theorem letStep_keys {xs : List Ident} {val : Option (Expr Op)} {funs : FunEnv D}
    {V Vm : VEnv D} {st stm : EvmState}
    (h : Step D funs V st (.stmt (.letDecl xs val)) (.sres Vm stm .normal)) :
    Vm.map Prod.fst = xs ++ V.map Prod.fst := by
  cases h with
  | letZero => rw [List.map_append, bindZeros_fst]
  | letVal he hlen => rw [List.map_append, List.map_fst_zip (by omega)]

/-! ### The sequence sweep: forward simulation -/

/-- The forward simulation's conclusion, as a predicate on the source sequence,
so the per-shape cases factor out of the induction. `k` is the height of the
environment the enclosing block will `restore` to; `owned` names live above it. -/
def SweepFwd (ss : List (Stmt Op)) : Prop :=
  ∀ {bound owned : List Ident} {funs : FunEnv D} {dead : Ident → Prop} {k : Nat}
    {V1 V2 : VEnv D} {st : EvmState} {V1' : VEnv D} {st' : EvmState} {o : Outcome},
    BoundOK V1 bound → (∀ x, x ∈ owned → AboveK k x V1) →
    VChg dead k (fun _ => False) V1 V2 →
    (∀ x, dead x → dsDead x ss = true) →
    Step D funs V1 st (.stmts ss) (.sres V1' st' o) →
    ∃ (V2' : VEnv D) (dead' : Ident → Prop),
      Step D funs V2 st (.stmts (dsSweep bound owned ss)) (.sres V2' st' o) ∧
      VChg dead' k (fun _ => False) V1' V2'

/-- A statement the sweep passes through that changes neither `bound` nor
`owned`: transport it with the value-change frame lemma. -/
theorem sweepKeep_fwd {s : Stmt Op} {rest : List (Stmt Op)}
    (ih : SweepFwd (calls := calls) (creates := creates) (gasOracle := gasOracle) rest)
    {bound owned : List Ident} {funs : FunEnv D} {dead : Ident → Prop} {k : Nat}
    {V1 V2 : VEnv D} {st : EvmState} {V1' : VEnv D} {st' : EvmState} {o : Outcome}
    (hsweep : dsSweep bound owned (s :: rest) = s :: dsSweep bound owned rest)
    (hb : BoundOK V1 bound) (how : ∀ x, x ∈ owned → AboveK k x V1)
    (hrel : VChg dead k (fun _ => False) V1 V2)
    (hments : ∀ x, dead x → stmtMentions x s = false)
    (hadv : ∀ {Vm : VEnv D} {stm : EvmState},
      Step D funs V1 st (.stmt s) (.sres Vm stm .normal) → ∀ x, dead x → dsDead x rest = true)
    (hstep : Step D funs V1 st (.stmts (s :: rest)) (.sres V1' st' o)) :
    ∃ (V2' : VEnv D) (dead' : Ident → Prop),
      Step D funs V2 st (.stmts (dsSweep bound owned (s :: rest))) (.sres V2' st' o) ∧
      VChg dead' k (fun _ => False) V1' V2' := by
  rw [hsweep]
  have hfree : DeadFree dead (Code.stmt s) := fun x hx => hments x hx
  cases hstep with
  | seqCons hs hrest =>
      obtain ⟨res2, hs2, hr2⟩ := vchgStep hs hrel hfree
      obtain ⟨Vm2, rfl, hrelm⟩ := hr2.sres
      obtain ⟨V2', dead', hstep2, hrel2⟩ := ih (hb.mono hs)
        (fun x hx => (how x hx).mono_step hs) hrelm (hadv hs) hrest
      exact ⟨V2', dead', Step.seqCons hs2 hstep2, hrel2⟩
  | seqStop hs hne =>
      obtain ⟨res2, hs2, hr2⟩ := vchgStep hs hrel hfree
      obtain ⟨V2', rfl, hrel2⟩ := hr2.sres
      exact ⟨V2', dead, Step.seqStop hs2 hne, hrel2⟩

/-- A `let` the sweep keeps: same as `sweepKeep_fwd`, but the declared names join
`bound` and `owned`. -/
theorem sweepLetKeep_fwd {xs : List Ident} {val : Option (Expr Op)} {rest : List (Stmt Op)}
    (ih : SweepFwd (calls := calls) (creates := creates) (gasOracle := gasOracle) rest)
    {bound owned : List Ident} {funs : FunEnv D} {dead : Ident → Prop} {k : Nat}
    {V1 V2 : VEnv D} {st : EvmState} {V1' : VEnv D} {st' : EvmState} {o : Outcome}
    (hsweep : dsSweep bound owned (.letDecl xs val :: rest)
      = .letDecl xs val :: dsSweep (xs ++ bound) (xs ++ owned) rest)
    (hb : BoundOK V1 bound) (how : ∀ x, x ∈ owned → AboveK k x V1)
    (hrel : VChg dead k (fun _ => False) V1 V2)
    (hments : ∀ x, dead x → stmtMentions x (.letDecl xs val) = false)
    (hadv : ∀ x, dead x → dsDead x rest = true)
    (hstep : Step D funs V1 st (.stmts (.letDecl xs val :: rest)) (.sres V1' st' o)) :
    ∃ (V2' : VEnv D) (dead' : Ident → Prop),
      Step D funs V2 st (.stmts (dsSweep bound owned (.letDecl xs val :: rest)))
        (.sres V2' st' o) ∧
      VChg dead' k (fun _ => False) V1' V2' := by
  rw [hsweep]
  have hfree : DeadFree dead (Code.stmt (.letDecl xs val)) := fun x hx => hments x hx
  have hk : k ≤ V1.length := hrel.tail_le
  cases hstep with
  | seqCons hs hrest =>
      obtain ⟨res2, hs2, hr2⟩ := vchgStep hs hrel hfree
      obtain ⟨Vm2, rfl, hrelm⟩ := hr2.sres
      have hkeys := letStep_keys hs
      obtain ⟨V2', dead', hstep2, hrel2⟩ := ih
        (bound := xs ++ bound) (owned := xs ++ owned)
        (fun y hy => by
          rw [hkeys]
          rcases List.mem_append.mp hy with hy | hy
          · exact List.mem_append_left _ hy
          · exact List.mem_append_right _ (hb y hy))
        (fun y hy => by
          rcases List.mem_append.mp hy with hy | hy
          · exact AboveK.of_keys_head hkeys hk hy
          · exact AboveK.of_keys_mono hkeys (how y hy))
        hrelm hadv hrest
      exact ⟨V2', dead', Step.seqCons hs2 hstep2, hrel2⟩
  | seqStop hs hne =>
      obtain ⟨res2, hs2, hr2⟩ := vchgStep hs hrel hfree
      obtain ⟨V2', rfl, hrel2⟩ := hr2.sres
      exact ⟨V2', dead, Step.seqStop hs2 hne, hrel2⟩

/-- An assignment the sweep keeps. Its right-hand side mentions no dead name, so
it evaluates identically on both sides; the write then kills every dead name it
targets. -/
theorem sweepAssignKeep_fwd {ys : List Ident} {e : Expr Op} {rest : List (Stmt Op)}
    (ih : SweepFwd (calls := calls) (creates := creates) (gasOracle := gasOracle) rest)
    {bound owned : List Ident} {funs : FunEnv D} {dead : Ident → Prop} {k : Nat}
    {V1 V2 : VEnv D} {st : EvmState} {V1' : VEnv D} {st' : EvmState} {o : Outcome}
    (hsweep : dsSweep bound owned (.assign ys e :: rest)
      = .assign ys e :: dsSweep bound owned rest)
    (hb : BoundOK V1 bound) (how : ∀ x, x ∈ owned → AboveK k x V1)
    (hrel : VChg dead k (fun _ => False) V1 V2)
    (hd : ∀ x, dead x → dsDead x (.assign ys e :: rest) = true)
    (hstep : Step D funs V1 st (.stmts (.assign ys e :: rest)) (.sres V1' st' o)) :
    ∃ (V2' : VEnv D) (dead' : Ident → Prop),
      Step D funs V2 st (.stmts (dsSweep bound owned (.assign ys e :: rest)))
        (.sres V2' st' o) ∧
      VChg dead' k (fun _ => False) V1' V2' := by
  rw [hsweep]
  have hfree : DeadFree dead (Code.expr e) := fun x hx => (dsDead_assign (hd x hx)).1
  cases hstep with
  | seqCons hs hrest =>
      cases hs with
      | @assignVal _ _ _ _ _ vals st1 he hlen =>
          obtain ⟨r2, he2, hr2⟩ := vchgStep he hrel hfree
          obtain rfl := hr2.eres
          have hrelm : VChg (fun y => dsDead y rest = true) k (fun _ => False)
              (VEnv.setMany V1 ys vals) (VEnv.setMany V2 ys vals) :=
            VChg.setMany ys vals hrel hlen.symm
              (fun y hy hn => (dsDead_assign (hd y hy)).2 hn)
          obtain ⟨V2', dead', hstep2, hrel2⟩ := ih
            (fun y hy => by rw [VEnv.setMany_keys V1]; exact hb y hy)
            (fun y hy => AboveK.of_keys_eq (VEnv.setMany_keys V1 _ _) (how y hy))
            hrelm (fun y hy => hy) hrest
          exact ⟨V2', dead', Step.seqCons (Step.assignVal he2 hlen) hstep2, hrel2⟩
  | seqStop hs hne =>
      cases hs with
      | assignVal _ _ => exact absurd rfl hne
      | @assignHalt _ _ _ _ _ st1 he =>
          obtain ⟨r2, he2, hr2⟩ := vchgStep he hrel hfree
          obtain rfl := hr2.eres
          exact ⟨V2, dead, Step.seqStop (Step.assignHalt he2) hne, hrel⟩

/-- **R1.** The dead store is deleted: the source assigns, the target does not.
`alwaysEval` makes the right-hand side total and state-preserving, and `owned`
puts the target above the tail the enclosing block restores to. -/
theorem sweepAssignDrop_fwd {x : Ident} {e : Expr Op} {rest : List (Stmt Op)}
    (ih : SweepFwd (calls := calls) (creates := creates) (gasOracle := gasOracle) rest)
    {bound owned : List Ident} {funs : FunEnv D} {dead : Ident → Prop} {k : Nat}
    {V1 V2 : VEnv D} {st : EvmState} {V1' : VEnv D} {st' : EvmState} {o : Outcome}
    (hcond : (owned.contains x && alwaysEval bound e && dsDead x rest) = true)
    (hb : BoundOK V1 bound) (how : ∀ y, y ∈ owned → AboveK k y V1)
    (hrel : VChg dead k (fun _ => False) V1 V2)
    (hd : ∀ y, dead y → dsDead y (.assign [x] e :: rest) = true)
    (hstep : Step D funs V1 st (.stmts (.assign [x] e :: rest)) (.sres V1' st' o)) :
    ∃ (V2' : VEnv D) (dead' : Ident → Prop),
      Step D funs V2 st (.stmts (dsSweep bound owned (.assign [x] e :: rest)))
        (.sres V2' st' o) ∧
      VChg dead' k (fun _ => False) V1' V2' := by
  have hc := hcond
  rw [Bool.and_eq_true, Bool.and_eq_true] at hc
  obtain ⟨⟨hown, hae⟩, hdead⟩ := hc
  have hsweep : dsSweep bound owned (.assign [x] e :: rest) = dsSweep bound owned rest := by
    simp only [dsSweep, hcond, if_true]
  rw [hsweep]
  have hmono : ∀ y, dead y → dsDead y rest = true := by
    intro y hy
    by_cases hyx : y = x
    · subst hyx; exact hdead
    · exact (dsDead_assign (hd y hy)).2 (by simp [hyx])
  have hab : AboveK k x V1 := how x (by simpa using hown)
  cases hstep with
  | seqCons hs hrest =>
      cases hs with
      | @assignVal _ _ _ _ _ vals st1 he hlen =>
          obtain ⟨v, hv⟩ := dcEvalInv e hae he
          injection hv with hvals hst
          subst hvals; subst hst
          have hrelm : VChg (fun y => dsDead y rest = true) k (fun _ => False)
              (VEnv.setMany V1 [x] [v]) V2 :=
            hrel.set_left v hab (fun h => h) hdead hmono
          obtain ⟨V2', dead', hstep2, hrel2⟩ := ih
            (fun y hy => by rw [VEnv.setMany_keys V1]; exact hb y hy)
            (fun y hy => AboveK.of_keys_eq (VEnv.setMany_keys V1 _ _) (how y hy))
            hrelm (fun y hy => hy) hrest
          exact ⟨V2', dead', hstep2, hrel2⟩
  | seqStop hs hne =>
      cases hs with
      | assignVal _ _ => exact absurd rfl hne
      | @assignHalt _ _ _ _ _ st1 he =>
          obtain ⟨v, hv⟩ := dcEvalInv e hae he
          exact absurd hv (by simp)

/-- **R2.** The dead initialiser is dropped, keeping the binder: the source binds
the right-hand side's value, the target binds zero, and the name is unread until
its next write or the sequence's exit. -/
theorem sweepLetDrop_fwd {x : Ident} {e : Expr Op} {rest : List (Stmt Op)}
    (ih : SweepFwd (calls := calls) (creates := creates) (gasOracle := gasOracle) rest)
    {bound owned : List Ident} {funs : FunEnv D} {dead : Ident → Prop} {k : Nat}
    {V1 V2 : VEnv D} {st : EvmState} {V1' : VEnv D} {st' : EvmState} {o : Outcome}
    (hcond : (alwaysEval bound e && dsDead x rest) = true)
    (hb : BoundOK V1 bound) (how : ∀ y, y ∈ owned → AboveK k y V1)
    (hrel : VChg dead k (fun _ => False) V1 V2)
    (hd : ∀ y, dead y → dsDead y (.letDecl [x] (some e) :: rest) = true)
    (hstep : Step D funs V1 st (.stmts (.letDecl [x] (some e) :: rest)) (.sres V1' st' o)) :
    ∃ (V2' : VEnv D) (dead' : Ident → Prop),
      Step D funs V2 st (.stmts (dsSweep bound owned (.letDecl [x] (some e) :: rest)))
        (.sres V2' st' o) ∧
      VChg dead' k (fun _ => False) V1' V2' := by
  have hc := hcond
  rw [Bool.and_eq_true] at hc
  obtain ⟨hae, hdead⟩ := hc
  have hsweep : dsSweep bound owned (.letDecl [x] (some e) :: rest)
      = .letDecl [x] none :: dsSweep (x :: bound) (x :: owned) rest := by
    simp only [dsSweep, hcond, if_true]
  rw [hsweep]
  have hk : k ≤ V1.length := hrel.tail_le
  cases hstep with
  | seqCons hs hrest =>
      cases hs with
      | @letVal _ _ _ _ _ vals st1 he hlen =>
          obtain ⟨v, hv⟩ := dcEvalInv e hae he
          injection hv with hvals hst
          subst hvals; subst hst
          have hgrow : VChg dead k (fun y => (fun _ : Ident => False) y ∨ y = x) V1 V2 :=
            hrel.grow_seen (extra := fun y => y = x)
              (fun y hy hc2 => (dsDead_letSome (hd y hy)).2.1 (by simp [hc2]))
          have hnew : VChg (fun y => dsDead y rest = true) k (fun _ => False)
              ((x, v) :: V1) ((x, (evmWithExternal calls creates gasOracle).zero) :: V2) :=
            VChg.diff hdead (fun h => h)
              (hgrow.mono_seen (fun y _ hy => (dsDead_letSome (hd y hy)).2.2))
          obtain ⟨V2', dead', hstep2, hrel2⟩ := ih
            (bound := x :: bound) (owned := x :: owned)
            (fun y hy => by
              rcases List.mem_cons.mp hy with rfl | hy
              · simp
              · exact List.mem_cons_of_mem _ (hb y hy))
            (fun y hy => by
              rcases List.mem_cons.mp hy with rfl | hy
              · exact AboveK.head hk
              · exact AboveK.prepend (pre := [(x, v)]) (how y hy))
            hnew (fun y hy => hy) hrest
          exact ⟨V2', dead', Step.seqCons Step.letZero hstep2, hrel2⟩
  | seqStop hs hne =>
      cases hs with
      | letVal _ _ => exact absurd rfl hne
      | @letHalt _ _ _ _ _ st1 he =>
          obtain ⟨v, hv⟩ := dcEvalInv e hae he
          exact absurd hv (by simp)

/-- **Forward simulation of one sweep.** Every source derivation of the sequence
has a target derivation of the swept sequence with the same state and outcome,
and environments that still differ only at dead names above the tail. -/
theorem dsSweep_fwd : ∀ ss : List (Stmt Op), SweepFwd (calls := calls) (creates := creates) (gasOracle := gasOracle) ss := by
  intro ss
  induction ss with
  | nil =>
      intro bound owned funs dead k V1 V2 st V1' st' o hb how hrel hd hstep
      cases hstep with
      | seqNil => exact ⟨V2, dead, Step.seqNil, hrel⟩
  | cons s rest ih =>
      intro bound owned funs dead k V1 V2 st V1' st' o hb how hrel hd hstep
      cases s with
      | block body =>
          exact sweepKeep_fwd ih (by simp only [dsSweep]) hb how hrel
            (fun x hx => (dsDead_pass (hd x hx) (Or.inl ⟨body, rfl⟩)).1)
            (fun _ x hx => (dsDead_pass (hd x hx) (Or.inl ⟨body, rfl⟩)).2) hstep
      | funDef n ps rs body =>
          exact sweepKeep_fwd ih (by simp only [dsSweep]) hb how hrel
            (fun x hx => (dsDead_pass (hd x hx) (Or.inr (Or.inl ⟨n, ps, rs, body, rfl⟩))).1)
            (fun _ x hx => (dsDead_pass (hd x hx) (Or.inr (Or.inl ⟨n, ps, rs, body, rfl⟩))).2)
            hstep
      | cond c body =>
          exact sweepKeep_fwd ih (by simp only [dsSweep]) hb how hrel
            (fun x hx => (dsDead_pass (hd x hx) (Or.inr (Or.inr (Or.inl ⟨c, body, rfl⟩)))).1)
            (fun _ x hx => (dsDead_pass (hd x hx) (Or.inr (Or.inr (Or.inl ⟨c, body, rfl⟩)))).2)
            hstep
      | «switch» c cs dflt =>
          exact sweepKeep_fwd ih (by simp only [dsSweep]) hb how hrel
            (fun x hx =>
              (dsDead_pass (hd x hx) (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, cs, dflt, rfl⟩))))).1)
            (fun _ x hx =>
              (dsDead_pass (hd x hx) (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, cs, dflt, rfl⟩))))).2)
            hstep
      | forLoop init c post body =>
          exact sweepKeep_fwd ih (by simp only [dsSweep]) hb how hrel
            (fun x hx => (dsDead_pass (hd x hx)
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨init, c, post, body, rfl⟩)))))).1)
            (fun _ x hx => (dsDead_pass (hd x hx)
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨init, c, post, body, rfl⟩)))))).2)
            hstep
      | exprStmt e =>
          exact sweepKeep_fwd ih (by simp only [dsSweep]) hb how hrel
            (fun x hx => (dsDead_pass (hd x hx)
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e, rfl⟩)))))).1)
            (fun _ x hx => (dsDead_pass (hd x hx)
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e, rfl⟩)))))).2)
            hstep
      | «break» =>
          exact sweepKeep_fwd ih (by simp only [dsSweep]) hb how hrel
            (fun _ _ => rfl) (fun h => by cases h) hstep
      | «continue» =>
          exact sweepKeep_fwd ih (by simp only [dsSweep]) hb how hrel
            (fun _ _ => rfl) (fun h => by cases h) hstep
      | «leave» =>
          exact sweepKeep_fwd ih (by simp only [dsSweep]) hb how hrel
            (fun _ _ => rfl) (fun h => by cases h) hstep
      | assign ys e =>
          rcases ys with _ | ⟨x, ys'⟩
          · exact sweepAssignKeep_fwd ih (by simp only [dsSweep]) hb how hrel hd hstep
          · rcases ys' with _ | ⟨y, ys''⟩
            · by_cases hcond : (owned.contains x && alwaysEval bound e && dsDead x rest) = true
              · exact sweepAssignDrop_fwd ih hcond hb how hrel hd hstep
              · rw [Bool.not_eq_true] at hcond
                exact sweepAssignKeep_fwd ih
                  (by simp only [dsSweep, hcond, Bool.false_eq_true, if_false]) hb how hrel hd hstep
            · exact sweepAssignKeep_fwd ih (by simp only [dsSweep]) hb how hrel hd hstep
      | letDecl xs val =>
          cases val with
          | none =>
              exact sweepLetKeep_fwd ih (by simp only [dsSweep]) hb how hrel
                (fun x hx => by
                  have h1 := (dsDead_letNone (hd x hx)).1
                  simp [stmtMentions, optExprMentions, h1])
                (fun x hx => (dsDead_letNone (hd x hx)).2) hstep
          | some e =>
              rcases xs with _ | ⟨x, xs'⟩
              · exact sweepLetKeep_fwd ih (by simp only [dsSweep]) hb how hrel
                  (fun z hz => by
                    have h1 := dsDead_letSome (hd z hz)
                    simp [stmtMentions, optExprMentions, h1.1, h1.2.1])
                  (fun z hz => (dsDead_letSome (hd z hz)).2.2) hstep
              · rcases xs' with _ | ⟨y, xs''⟩
                · by_cases hcond : (alwaysEval bound e && dsDead x rest) = true
                  · exact sweepLetDrop_fwd ih hcond hb how hrel hd hstep
                  · rw [Bool.not_eq_true] at hcond
                    exact sweepLetKeep_fwd ih
                      (by simp only [dsSweep, hcond, Bool.false_eq_true, if_false,
                        List.singleton_append]) hb how hrel
                      (fun z hz => by
                        have h1 := dsDead_letSome (hd z hz)
                        simp [stmtMentions, optExprMentions, h1.1, h1.2.1])
                      (fun z hz => (dsDead_letSome (hd z hz)).2.2) hstep
                · exact sweepLetKeep_fwd ih (by simp only [dsSweep]) hb how hrel
                    (fun z hz => by
                      have h1 := dsDead_letSome (hd z hz)
                      simp [stmtMentions, optExprMentions, h1.1, h1.2.1])
                    (fun z hz => (dsDead_letSome (hd z hz)).2.2) hstep

/-! ### The sequence sweep: backward simulation -/

/-- The backward simulation's conclusion, as a predicate on the source sequence. -/
def SweepBwd (ss : List (Stmt Op)) : Prop :=
  ∀ {bound owned : List Ident} {funs : FunEnv D} {dead : Ident → Prop} {k : Nat}
    {V1 V2 : VEnv D} {st : EvmState} {V2' : VEnv D} {st' : EvmState} {o : Outcome},
    BoundOK V1 bound → (∀ x, x ∈ owned → AboveK k x V1) →
    VChg dead k (fun _ => False) V1 V2 →
    (∀ x, dead x → dsDead x ss = true) →
    Step D funs V2 st (.stmts (dsSweep bound owned ss)) (.sres V2' st' o) →
    ∃ (V1' : VEnv D) (dead' : Ident → Prop),
      Step D funs V1 st (.stmts ss) (.sres V1' st' o) ∧
      VChg dead' k (fun _ => False) V1' V2'

/-- Backward counterpart of `sweepKeep_fwd`. -/
theorem sweepKeep_bwd {s : Stmt Op} {rest : List (Stmt Op)}
    (ih : SweepBwd (calls := calls) (creates := creates) (gasOracle := gasOracle) rest)
    {bound owned : List Ident} {funs : FunEnv D} {dead : Ident → Prop} {k : Nat}
    {V1 V2 : VEnv D} {st : EvmState} {V2' : VEnv D} {st' : EvmState} {o : Outcome}
    (hsweep : dsSweep bound owned (s :: rest) = s :: dsSweep bound owned rest)
    (hb : BoundOK V1 bound) (how : ∀ x, x ∈ owned → AboveK k x V1)
    (hrel : VChg dead k (fun _ => False) V1 V2)
    (hments : ∀ x, dead x → stmtMentions x s = false)
    (hadv : ∀ {Vm : VEnv D} {stm : EvmState},
      Step D funs V1 st (.stmt s) (.sres Vm stm .normal) → ∀ x, dead x → dsDead x rest = true)
    (hstep : Step D funs V2 st (.stmts (dsSweep bound owned (s :: rest))) (.sres V2' st' o)) :
    ∃ (V1' : VEnv D) (dead' : Ident → Prop),
      Step D funs V1 st (.stmts (s :: rest)) (.sres V1' st' o) ∧
      VChg dead' k (fun _ => False) V1' V2' := by
  rw [hsweep] at hstep
  have hfree : DeadFree dead (Code.stmt s) := fun x hx => hments x hx
  cases hstep with
  | seqCons hs hrest =>
      obtain ⟨res1, hs1, hr1⟩ := vchgStep hs hrel.symm hfree
      obtain ⟨Vm1, rfl, hrelm⟩ := hr1.sres
      obtain ⟨V1', dead', hstep1, hrel1⟩ := ih (hb.mono hs1)
        (fun x hx => (how x hx).mono_step hs1) hrelm.symm (hadv hs1) hrest
      exact ⟨V1', dead', Step.seqCons hs1 hstep1, hrel1⟩
  | seqStop hs hne =>
      obtain ⟨res1, hs1, hr1⟩ := vchgStep hs hrel.symm hfree
      obtain ⟨V1', rfl, hrel1⟩ := hr1.sres
      exact ⟨V1', dead, Step.seqStop hs1 hne, hrel1.symm⟩

/-- Backward counterpart of `sweepLetKeep_fwd`. -/
theorem sweepLetKeep_bwd {xs : List Ident} {val : Option (Expr Op)} {rest : List (Stmt Op)}
    (ih : SweepBwd (calls := calls) (creates := creates) (gasOracle := gasOracle) rest)
    {bound owned : List Ident} {funs : FunEnv D} {dead : Ident → Prop} {k : Nat}
    {V1 V2 : VEnv D} {st : EvmState} {V2' : VEnv D} {st' : EvmState} {o : Outcome}
    (hsweep : dsSweep bound owned (.letDecl xs val :: rest)
      = .letDecl xs val :: dsSweep (xs ++ bound) (xs ++ owned) rest)
    (hb : BoundOK V1 bound) (how : ∀ x, x ∈ owned → AboveK k x V1)
    (hrel : VChg dead k (fun _ => False) V1 V2)
    (hments : ∀ x, dead x → stmtMentions x (.letDecl xs val) = false)
    (hadv : ∀ x, dead x → dsDead x rest = true)
    (hstep : Step D funs V2 st (.stmts (dsSweep bound owned (.letDecl xs val :: rest)))
      (.sres V2' st' o)) :
    ∃ (V1' : VEnv D) (dead' : Ident → Prop),
      Step D funs V1 st (.stmts (.letDecl xs val :: rest)) (.sres V1' st' o) ∧
      VChg dead' k (fun _ => False) V1' V2' := by
  rw [hsweep] at hstep
  have hfree : DeadFree dead (Code.stmt (.letDecl xs val)) := fun x hx => hments x hx
  have hk : k ≤ V1.length := hrel.tail_le
  cases hstep with
  | seqCons hs hrest =>
      obtain ⟨res1, hs1, hr1⟩ := vchgStep hs hrel.symm hfree
      obtain ⟨Vm1, rfl, hrelm⟩ := hr1.sres
      have hkeys := letStep_keys hs1
      obtain ⟨V1', dead', hstep1, hrel1⟩ := ih
        (bound := xs ++ bound) (owned := xs ++ owned)
        (fun y hy => by
          rw [hkeys]
          rcases List.mem_append.mp hy with hy | hy
          · exact List.mem_append_left _ hy
          · exact List.mem_append_right _ (hb y hy))
        (fun y hy => by
          rcases List.mem_append.mp hy with hy | hy
          · exact AboveK.of_keys_head hkeys hk hy
          · exact AboveK.of_keys_mono hkeys (how y hy))
        hrelm.symm hadv hrest
      exact ⟨V1', dead', Step.seqCons hs1 hstep1, hrel1⟩
  | seqStop hs hne =>
      obtain ⟨res1, hs1, hr1⟩ := vchgStep hs hrel.symm hfree
      obtain ⟨V1', rfl, hrel1⟩ := hr1.sres
      exact ⟨V1', dead, Step.seqStop hs1 hne, hrel1.symm⟩

/-- Backward counterpart of `sweepAssignKeep_fwd`. -/
theorem sweepAssignKeep_bwd {ys : List Ident} {e : Expr Op} {rest : List (Stmt Op)}
    (ih : SweepBwd (calls := calls) (creates := creates) (gasOracle := gasOracle) rest)
    {bound owned : List Ident} {funs : FunEnv D} {dead : Ident → Prop} {k : Nat}
    {V1 V2 : VEnv D} {st : EvmState} {V2' : VEnv D} {st' : EvmState} {o : Outcome}
    (hsweep : dsSweep bound owned (.assign ys e :: rest)
      = .assign ys e :: dsSweep bound owned rest)
    (hb : BoundOK V1 bound) (how : ∀ x, x ∈ owned → AboveK k x V1)
    (hrel : VChg dead k (fun _ => False) V1 V2)
    (hd : ∀ x, dead x → dsDead x (.assign ys e :: rest) = true)
    (hstep : Step D funs V2 st (.stmts (dsSweep bound owned (.assign ys e :: rest)))
      (.sres V2' st' o)) :
    ∃ (V1' : VEnv D) (dead' : Ident → Prop),
      Step D funs V1 st (.stmts (.assign ys e :: rest)) (.sres V1' st' o) ∧
      VChg dead' k (fun _ => False) V1' V2' := by
  rw [hsweep] at hstep
  have hfree : DeadFree dead (Code.expr e) := fun x hx => (dsDead_assign (hd x hx)).1
  cases hstep with
  | seqCons hs hrest =>
      cases hs with
      | @assignVal _ _ _ _ _ vals st1 he hlen =>
          obtain ⟨r1, he1, hr1⟩ := vchgStep he hrel.symm hfree
          obtain rfl := hr1.eres
          have hrelm : VChg (fun y => dsDead y rest = true) k (fun _ => False)
              (VEnv.setMany V1 ys vals) (VEnv.setMany V2 ys vals) :=
            VChg.setMany ys vals hrel hlen.symm
              (fun y hy hn => (dsDead_assign (hd y hy)).2 hn)
          obtain ⟨V1', dead', hstep1, hrel1⟩ := ih
            (fun y hy => by rw [VEnv.setMany_keys V1]; exact hb y hy)
            (fun y hy => AboveK.of_keys_eq (VEnv.setMany_keys V1 _ _) (how y hy))
            hrelm (fun y hy => hy) hrest
          exact ⟨V1', dead', Step.seqCons (Step.assignVal he1 hlen) hstep1, hrel1⟩
  | seqStop hs hne =>
      cases hs with
      | assignVal _ _ => exact absurd rfl hne
      | @assignHalt _ _ _ _ _ st1 he =>
          obtain ⟨r1, he1, hr1⟩ := vchgStep he hrel.symm hfree
          obtain rfl := hr1.eres
          exact ⟨V1, dead, Step.seqStop (Step.assignHalt he1) hne, hrel⟩

/-- Backward counterpart of `sweepAssignDrop_fwd` (**R1**): the deleted store is
put back, which `alwaysEval` and `BoundOK` make possible. -/
theorem sweepAssignDrop_bwd {x : Ident} {e : Expr Op} {rest : List (Stmt Op)}
    (ih : SweepBwd (calls := calls) (creates := creates) (gasOracle := gasOracle) rest)
    {bound owned : List Ident} {funs : FunEnv D} {dead : Ident → Prop} {k : Nat}
    {V1 V2 : VEnv D} {st : EvmState} {V2' : VEnv D} {st' : EvmState} {o : Outcome}
    (hcond : (owned.contains x && alwaysEval bound e && dsDead x rest) = true)
    (hb : BoundOK V1 bound) (how : ∀ y, y ∈ owned → AboveK k y V1)
    (hrel : VChg dead k (fun _ => False) V1 V2)
    (hd : ∀ y, dead y → dsDead y (.assign [x] e :: rest) = true)
    (hstep : Step D funs V2 st (.stmts (dsSweep bound owned (.assign [x] e :: rest)))
      (.sres V2' st' o)) :
    ∃ (V1' : VEnv D) (dead' : Ident → Prop),
      Step D funs V1 st (.stmts (.assign [x] e :: rest)) (.sres V1' st' o) ∧
      VChg dead' k (fun _ => False) V1' V2' := by
  have hc := hcond
  rw [Bool.and_eq_true, Bool.and_eq_true] at hc
  obtain ⟨⟨hown, hae⟩, hdead⟩ := hc
  have hsweep : dsSweep bound owned (.assign [x] e :: rest) = dsSweep bound owned rest := by
    simp only [dsSweep, hcond, if_true]
  rw [hsweep] at hstep
  have hmono : ∀ y, dead y → dsDead y rest = true := by
    intro y hy
    by_cases hyx : y = x
    · subst hyx; exact hdead
    · exact (dsDead_assign (hd y hy)).2 (by simp [hyx])
  have hab : AboveK k x V1 := how x (by simpa using hown)
  obtain ⟨v, hv⟩ := dcEvalRun hb funs st e hae
  have hrelm : VChg (fun y => dsDead y rest = true) k (fun _ => False)
      (VEnv.setMany V1 [x] [v]) V2 :=
    hrel.set_left v hab (fun h => h) hdead hmono
  obtain ⟨V1', dead', hstep1, hrel1⟩ := ih
    (fun y hy => by rw [VEnv.setMany_keys V1]; exact hb y hy)
    (fun y hy => AboveK.of_keys_eq (VEnv.setMany_keys V1 _ _) (how y hy))
    hrelm (fun y hy => hy) hstep
  exact ⟨V1', dead', Step.seqCons (Step.assignVal hv rfl) hstep1, hrel1⟩

/-- Backward counterpart of `sweepLetDrop_fwd` (**R2**): the dropped initialiser
is put back. -/
theorem sweepLetDrop_bwd {x : Ident} {e : Expr Op} {rest : List (Stmt Op)}
    (ih : SweepBwd (calls := calls) (creates := creates) (gasOracle := gasOracle) rest)
    {bound owned : List Ident} {funs : FunEnv D} {dead : Ident → Prop} {k : Nat}
    {V1 V2 : VEnv D} {st : EvmState} {V2' : VEnv D} {st' : EvmState} {o : Outcome}
    (hcond : (alwaysEval bound e && dsDead x rest) = true)
    (hb : BoundOK V1 bound) (how : ∀ y, y ∈ owned → AboveK k y V1)
    (hrel : VChg dead k (fun _ => False) V1 V2)
    (hd : ∀ y, dead y → dsDead y (.letDecl [x] (some e) :: rest) = true)
    (hstep : Step D funs V2 st (.stmts (dsSweep bound owned (.letDecl [x] (some e) :: rest)))
      (.sres V2' st' o)) :
    ∃ (V1' : VEnv D) (dead' : Ident → Prop),
      Step D funs V1 st (.stmts (.letDecl [x] (some e) :: rest)) (.sres V1' st' o) ∧
      VChg dead' k (fun _ => False) V1' V2' := by
  have hc := hcond
  rw [Bool.and_eq_true] at hc
  obtain ⟨hae, hdead⟩ := hc
  have hsweep : dsSweep bound owned (.letDecl [x] (some e) :: rest)
      = .letDecl [x] none :: dsSweep (x :: bound) (x :: owned) rest := by
    simp only [dsSweep, hcond, if_true]
  rw [hsweep] at hstep
  have hk : k ≤ V1.length := hrel.tail_le
  obtain ⟨v, hv⟩ := dcEvalRun hb funs st e hae
  have hgrow : VChg dead k (fun y => (fun _ : Ident => False) y ∨ y = x) V1 V2 :=
    hrel.grow_seen (extra := fun y => y = x)
      (fun y hy hc2 => (dsDead_letSome (hd y hy)).2.1 (by simp [hc2]))
  have hnew : VChg (fun y => dsDead y rest = true) k (fun _ => False)
      ((x, v) :: V1) ((x, (evmWithExternal calls creates gasOracle).zero) :: V2) :=
    VChg.diff hdead (fun h => h)
      (hgrow.mono_seen (fun y _ hy => (dsDead_letSome (hd y hy)).2.2))
  cases hstep with
  | seqCons hs hrest =>
      cases hs with
      | letZero =>
          obtain ⟨V1', dead', hstep1, hrel1⟩ := ih
            (bound := x :: bound) (owned := x :: owned)
            (fun y hy => by
              rcases List.mem_cons.mp hy with rfl | hy
              · simp
              · exact List.mem_cons_of_mem _ (hb y hy))
            (fun y hy => by
              rcases List.mem_cons.mp hy with rfl | hy
              · exact AboveK.head hk
              · exact AboveK.prepend (pre := [(x, v)]) (how y hy))
            hnew (fun y hy => hy) hrest
          exact ⟨V1', dead', Step.seqCons (Step.letVal hv rfl) hstep1, hrel1⟩
  | seqStop hs hne =>
      cases hs with
      | letZero => exact absurd rfl hne

/-- **Backward simulation of one sweep.** -/
theorem dsSweep_bwd : ∀ ss : List (Stmt Op), SweepBwd (calls := calls) (creates := creates) (gasOracle := gasOracle) ss := by
  intro ss
  induction ss with
  | nil =>
      intro bound owned funs dead k V1 V2 st V2' st' o hb how hrel hd hstep
      cases hstep with
      | seqNil => exact ⟨V1, dead, Step.seqNil, hrel⟩
  | cons s rest ih =>
      intro bound owned funs dead k V1 V2 st V2' st' o hb how hrel hd hstep
      cases s with
      | block body =>
          exact sweepKeep_bwd ih (by simp only [dsSweep]) hb how hrel
            (fun x hx => (dsDead_pass (hd x hx) (Or.inl ⟨body, rfl⟩)).1)
            (fun _ x hx => (dsDead_pass (hd x hx) (Or.inl ⟨body, rfl⟩)).2) hstep
      | funDef n ps rs body =>
          exact sweepKeep_bwd ih (by simp only [dsSweep]) hb how hrel
            (fun x hx => (dsDead_pass (hd x hx) (Or.inr (Or.inl ⟨n, ps, rs, body, rfl⟩))).1)
            (fun _ x hx => (dsDead_pass (hd x hx) (Or.inr (Or.inl ⟨n, ps, rs, body, rfl⟩))).2)
            hstep
      | cond c body =>
          exact sweepKeep_bwd ih (by simp only [dsSweep]) hb how hrel
            (fun x hx => (dsDead_pass (hd x hx) (Or.inr (Or.inr (Or.inl ⟨c, body, rfl⟩)))).1)
            (fun _ x hx => (dsDead_pass (hd x hx) (Or.inr (Or.inr (Or.inl ⟨c, body, rfl⟩)))).2)
            hstep
      | «switch» c cs dflt =>
          exact sweepKeep_bwd ih (by simp only [dsSweep]) hb how hrel
            (fun x hx =>
              (dsDead_pass (hd x hx) (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, cs, dflt, rfl⟩))))).1)
            (fun _ x hx =>
              (dsDead_pass (hd x hx) (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, cs, dflt, rfl⟩))))).2)
            hstep
      | forLoop init c post body =>
          exact sweepKeep_bwd ih (by simp only [dsSweep]) hb how hrel
            (fun x hx => (dsDead_pass (hd x hx)
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨init, c, post, body, rfl⟩)))))).1)
            (fun _ x hx => (dsDead_pass (hd x hx)
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨init, c, post, body, rfl⟩)))))).2)
            hstep
      | exprStmt e =>
          exact sweepKeep_bwd ih (by simp only [dsSweep]) hb how hrel
            (fun x hx => (dsDead_pass (hd x hx)
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e, rfl⟩)))))).1)
            (fun _ x hx => (dsDead_pass (hd x hx)
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e, rfl⟩)))))).2)
            hstep
      | «break» =>
          exact sweepKeep_bwd ih (by simp only [dsSweep]) hb how hrel
            (fun _ _ => rfl) (fun h => by cases h) hstep
      | «continue» =>
          exact sweepKeep_bwd ih (by simp only [dsSweep]) hb how hrel
            (fun _ _ => rfl) (fun h => by cases h) hstep
      | «leave» =>
          exact sweepKeep_bwd ih (by simp only [dsSweep]) hb how hrel
            (fun _ _ => rfl) (fun h => by cases h) hstep
      | assign ys e =>
          rcases ys with _ | ⟨x, ys'⟩
          · exact sweepAssignKeep_bwd ih (by simp only [dsSweep]) hb how hrel hd hstep
          · rcases ys' with _ | ⟨y, ys''⟩
            · by_cases hcond : (owned.contains x && alwaysEval bound e && dsDead x rest) = true
              · exact sweepAssignDrop_bwd ih hcond hb how hrel hd hstep
              · rw [Bool.not_eq_true] at hcond
                exact sweepAssignKeep_bwd ih
                  (by simp only [dsSweep, hcond, Bool.false_eq_true, if_false]) hb how hrel hd hstep
            · exact sweepAssignKeep_bwd ih (by simp only [dsSweep]) hb how hrel hd hstep
      | letDecl xs val =>
          cases val with
          | none =>
              exact sweepLetKeep_bwd ih (by simp only [dsSweep]) hb how hrel
                (fun x hx => by
                  have h1 := (dsDead_letNone (hd x hx)).1
                  simp [stmtMentions, optExprMentions, h1])
                (fun x hx => (dsDead_letNone (hd x hx)).2) hstep
          | some e =>
              rcases xs with _ | ⟨x, xs'⟩
              · exact sweepLetKeep_bwd ih (by simp only [dsSweep]) hb how hrel
                  (fun z hz => by
                    have h1 := dsDead_letSome (hd z hz)
                    simp [stmtMentions, optExprMentions, h1.1, h1.2.1])
                  (fun z hz => (dsDead_letSome (hd z hz)).2.2) hstep
              · rcases xs' with _ | ⟨y, xs''⟩
                · by_cases hcond : (alwaysEval bound e && dsDead x rest) = true
                  · exact sweepLetDrop_bwd ih hcond hb how hrel hd hstep
                  · rw [Bool.not_eq_true] at hcond
                    exact sweepLetKeep_bwd ih
                      (by simp only [dsSweep, hcond, Bool.false_eq_true, if_false,
                        List.singleton_append]) hb how hrel
                      (fun z hz => by
                        have h1 := dsDead_letSome (hd z hz)
                        simp [stmtMentions, optExprMentions, h1.1, h1.2.1])
                      (fun z hz => (dsDead_letSome (hd z hz)).2.2) hstep
                · exact sweepLetKeep_bwd ih (by simp only [dsSweep]) hb how hrel
                    (fun z hz => by
                      have h1 := dsDead_letSome (hd z hz)
                      simp [stmtMentions, optExprMentions, h1.1, h1.2.1])
                    (fun z hz => (dsDead_letSome (hd z hz)).2.2) hstep

/-! ### One sweep, at the block level

The sweep's two rewrites only ever change the value of a name the sequence
itself declared, so at the block's `restore` the two environments become
*equal* — which is what lifts the sequence-level simulation to a genuine
(bound-relative) block equivalence. -/

/-- A block's hoisted scope splits along the head statement. -/
theorem hoist_cons (s : Stmt Op) (rest : List (Stmt Op)) :
    hoist D (s :: rest) = hoist D [s] ++ hoist D rest := by
  cases s <;> simp [hoist]

/-- The sweep leaves every top-level `funDef` in place, so a block's hoisted
scope is unchanged. -/
theorem dsSweep_hoist : ∀ (bound owned : List Ident) (ss : List (Stmt Op)),
    hoist D (dsSweep bound owned ss) = hoist D ss := by
  intro bound owned ss
  induction bound, owned, ss using dsSweep.induct with
  | case1 bound owned => rfl
  | case2 bound owned x e rest hg ih =>
      rw [show dsSweep bound owned (Stmt.assign [x] e :: rest) = dsSweep bound owned rest from by
        simp only [dsSweep, hg, if_true], hoist_cons (Stmt.assign [x] e) rest, ih]
      simp [hoist]
  | case3 bound owned x e rest hg ih =>
      rw [Bool.not_eq_true] at hg
      simp only [dsSweep, hg, Bool.false_eq_true, if_false]
      rw [hoist_cons (Stmt.assign [x] e) (dsSweep bound owned rest),
        hoist_cons (Stmt.assign [x] e) rest, ih]
  | case4 bound owned x e rest hg ih =>
      simp only [dsSweep, hg, if_true]
      rw [hoist_cons (Stmt.letDecl [x] none) (dsSweep (x :: bound) (x :: owned) rest),
        hoist_cons (Stmt.letDecl [x] (some e)) rest, ih]
      simp [hoist]
  | case5 bound owned x e rest hg ih =>
      rw [Bool.not_eq_true] at hg
      simp only [dsSweep, hg, Bool.false_eq_true, if_false]
      rw [hoist_cons (Stmt.letDecl [x] (some e)) (dsSweep (x :: bound) (x :: owned) rest),
        hoist_cons (Stmt.letDecl [x] (some e)) rest, ih]
  | case6 bound owned xs v rest hne ih =>
      rw [show dsSweep bound owned (Stmt.letDecl xs v :: rest)
          = .letDecl xs v :: dsSweep (xs ++ bound) (xs ++ owned) rest from by
        simp only [dsSweep], hoist_cons (Stmt.letDecl xs v)
          (dsSweep (xs ++ bound) (xs ++ owned) rest), hoist_cons (Stmt.letDecl xs v) rest, ih]
  | case7 bound owned s rest h1 h2 h3 ih =>
      rw [show dsSweep bound owned (s :: rest) = s :: dsSweep bound owned rest from by
        simp only [dsSweep], hoist_cons s (dsSweep bound owned rest), hoist_cons s rest, ih]

/-- **The sweep is sound at the block level.** -/
theorem dsSweep_bequivBlock (bound : List Ident) (ss : Block Op) :
    BEquivBlock D bound ss (dsSweep bound [] ss) := by
  have hh : hoist D (dsSweep bound [] ss) = hoist D ss := dsSweep_hoist bound [] ss
  intro funs V st V' st' o hb
  constructor
  · intro h
    cases h with
    | block hbody =>
        obtain ⟨Vb2, dead', hstep2, hrel2⟩ := dsSweep_fwd ss hb
          (fun x hx => absurd hx List.not_mem_nil)
          (VChg.rfl_len (fun _ => False) (fun _ => False) V)
          (fun x hx => hx.elim) hbody
        rw [hrel2.restore_eq (venvLen_mono hbody rfl)]
        exact Step.block (hh ▸ hstep2)
  · intro h
    cases h with
    | block hbody =>
        have hbody' := hh ▸ hbody
        obtain ⟨Vb, dead', hstep1, hrel1⟩ := dsSweep_bwd ss hb
          (fun x hx => absurd hx List.not_mem_nil)
          (VChg.rfl_len (fun _ => False) (fun _ => False) V)
          (fun x hx => hx.elim) hbody'
        rw [← hrel1.restore_eq (venvLen_mono hstep1 rfl)]
        exact Step.block hstep1

/-! ### Recursion into every sequence -/

/-- One rewritten sequence, as a block: recurse, then sweep. -/
theorem dsBody_of (bound : List Ident) (body : Block Op)
    (h₁ : BEquivStmts D bound body (dsStmts bound body))
    (h₂ : SbScopeRel (hoist D body) (hoist D (dsStmts bound body))) :
    BEquivBlock D bound body (dsSweep bound [] (dsStmts bound body)) :=
  (BEquivBlock.of_stmts_funs h₁ h₂).trans (dsSweep_bequivBlock bound (dsStmts bound body))

mutual

/-- Recursing into a statement's sub-sequences is sound. -/
theorem dsStmt_bequiv (bound : List Ident) : ∀ s : Stmt Op,
    BEquivStmt D bound s (dsStmt bound s)
  | .block body =>
      dsBody_of bound body (dsStmts_bequiv bound body) (dsStmts_scopeRel bound body)
  | .funDef n ps rs _ => BEquivStmt.funDef_any bound n ps rs _ _
  | .letDecl _ _ => BEquivStmt.refl bound _
  | .assign _ _ => BEquivStmt.refl bound _
  | .cond c body =>
      BEquivStmt.cond_congr c
        (dsBody_of bound body (dsStmts_bequiv bound body) (dsStmts_scopeRel bound body))
  | .switch c cs d =>
      BEquivStmt.switch_congr c (dsCases_bequiv bound cs) (dsDflt_bequiv bound d)
  | .forLoop init c post body =>
      BEquivStmt.forLoop_congr init c
        (dsBody_of bound post (dsStmts_bequiv bound post) (dsStmts_scopeRel bound post))
        (dsBody_of bound body (dsStmts_bequiv bound body) (dsStmts_scopeRel bound body))
  | .exprStmt _ => BEquivStmt.refl bound _
  | .break => BEquivStmt.refl bound _
  | .continue => BEquivStmt.refl bound _
  | .leave => BEquivStmt.refl bound _

/-- Recursing into a sequence's statements is sound. -/
theorem dsStmts_bequiv (bound : List Ident) : ∀ ss : List (Stmt Op),
    BEquivStmts D bound ss (dsStmts bound ss)
  | [] => BEquivStmts.refl bound _
  | s :: rest =>
      BEquivStmts.cons_congr (dsStmt_bequiv bound s) (dsStmts_bequiv bound rest)

/-- Every `switch` case body stays related. -/
theorem dsCases_bequiv (bound : List Ident) : ∀ cs : List (Literal × Block Op),
    Forall₂ (fun p q => p.1 = q.1 ∧ BEquivBlock D bound p.2 q.2) cs (dsCases bound cs)
  | [] => List.Forall₂.nil
  | (_, b) :: rest =>
      List.Forall₂.cons
        ⟨rfl, dsBody_of bound b (dsStmts_bequiv bound b) (dsStmts_scopeRel bound b)⟩
        (dsCases_bequiv bound rest)

/-- The `switch` default stays related. -/
theorem dsDflt_bequiv (bound : List Ident) : ∀ d : Option (Block Op),
    BEquivBlock D bound (d.getD []) ((dsDflt bound d).getD [])
  | none => BEquivBlock.refl bound _
  | some b => dsBody_of bound b (dsStmts_bequiv bound b) (dsStmts_scopeRel bound b)

/-- A single statement contributes a related hoisted scope. -/
theorem dsStmt_scope (bound : List Ident) : ∀ s : Stmt Op,
    SbScopeRel (hoist D [s]) (hoist D [dsStmt bound s])
  | .funDef _ ps rs body =>
      List.Forall₂.cons
        ⟨rfl, rfl, rfl,
          dsBody_of (ps ++ rs) body (dsStmts_bequiv (ps ++ rs) body)
            (dsStmts_scopeRel (ps ++ rs) body)⟩
        List.Forall₂.nil
  | .block _ => List.Forall₂.nil
  | .letDecl _ _ => List.Forall₂.nil
  | .assign _ _ => List.Forall₂.nil
  | .cond _ _ => List.Forall₂.nil
  | .switch _ _ _ => List.Forall₂.nil
  | .forLoop _ _ _ _ => List.Forall₂.nil
  | .exprStmt _ => List.Forall₂.nil
  | .break => List.Forall₂.nil
  | .continue => List.Forall₂.nil
  | .leave => List.Forall₂.nil

/-- A rewritten sequence hoists a related function scope. -/
theorem dsStmts_scopeRel (bound : List Ident) : ∀ ss : List (Stmt Op),
    SbScopeRel (hoist D ss) (hoist D (dsStmts bound ss))
  | [] => List.Forall₂.nil
  | s :: rest => by
      show SbScopeRel (hoist D (s :: rest)) (hoist D (dsStmt bound s :: dsStmts bound rest))
      rw [hoist_cons s rest, hoist_cons (dsStmt bound s) (dsStmts bound rest)]
      exact SbScopeRel.append (dsStmt_scope bound s) (dsStmts_scopeRel bound rest)

end

/-! ### Layout-freedom is preserved -/

/-- The sweep only deletes statements and turns `let x := e` into `let x`, so it
cannot introduce an unresolved `dataoffset`/`datasize`. -/
theorem dsSweep_layoutFree : ∀ (bound owned : List Ident) (ss : List (Stmt Op)),
    storageLayoutFreeStmts ss = true → storageLayoutFreeStmts (dsSweep bound owned ss) = true := by
  intro bound owned ss
  induction bound, owned, ss using dsSweep.induct with
  | case1 bound owned => exact fun h => h
  | case2 bound owned x e rest hg ih =>
      intro h
      simp only [storageLayoutFreeStmts, Bool.and_eq_true] at h
      rw [show dsSweep bound owned (Stmt.assign [x] e :: rest) = dsSweep bound owned rest from by
        simp only [dsSweep, hg, if_true]]
      exact ih h.2
  | case3 bound owned x e rest hg ih =>
      intro h
      simp only [storageLayoutFreeStmts, Bool.and_eq_true] at h
      rw [Bool.not_eq_true] at hg
      simp only [dsSweep, hg, Bool.false_eq_true, if_false, storageLayoutFreeStmts,
        Bool.and_eq_true]
      exact ⟨h.1, ih h.2⟩
  | case4 bound owned x e rest hg ih =>
      intro h
      simp only [storageLayoutFreeStmts, Bool.and_eq_true] at h
      simp only [dsSweep, hg, if_true, storageLayoutFreeStmts, Bool.and_eq_true]
      exact ⟨by simp [storageLayoutFreeStmt], ih h.2⟩
  | case5 bound owned x e rest hg ih =>
      intro h
      simp only [storageLayoutFreeStmts, Bool.and_eq_true] at h
      rw [Bool.not_eq_true] at hg
      simp only [dsSweep, hg, Bool.false_eq_true, if_false, storageLayoutFreeStmts,
        Bool.and_eq_true]
      exact ⟨h.1, ih h.2⟩
  | case6 bound owned xs v rest hne ih =>
      intro h
      simp only [storageLayoutFreeStmts, Bool.and_eq_true] at h
      rw [show dsSweep bound owned (Stmt.letDecl xs v :: rest)
          = .letDecl xs v :: dsSweep (xs ++ bound) (xs ++ owned) rest from by simp only [dsSweep]]
      simp only [storageLayoutFreeStmts, Bool.and_eq_true]
      exact ⟨h.1, ih h.2⟩
  | case7 bound owned s rest h1 h2 h3 ih =>
      intro h
      simp only [storageLayoutFreeStmts, Bool.and_eq_true] at h
      rw [show dsSweep bound owned (s :: rest) = s :: dsSweep bound owned rest from by
        simp only [dsSweep]]
      simp only [storageLayoutFreeStmts, Bool.and_eq_true]
      exact ⟨h.1, ih h.2⟩

mutual

/-- Recursion preserves layout-freedom of a statement. -/
theorem dsStmt_layoutFree (bound : List Ident) : ∀ s : Stmt Op,
    storageLayoutFreeStmt s = true → storageLayoutFreeStmt (dsStmt bound s) = true
  | .block body, h => by
      show storageLayoutFreeStmts (dsSweep bound [] (dsStmts bound body)) = true
      exact dsSweep_layoutFree _ _ _ (dsStmts_layoutFree bound body h)
  | .funDef _ ps rs body, h => by
      show storageLayoutFreeStmts (dsSweep (ps ++ rs) [] (dsStmts (ps ++ rs) body)) = true
      exact dsSweep_layoutFree _ _ _ (dsStmts_layoutFree (ps ++ rs) body h)
  | .letDecl _ _, h => h
  | .assign _ _, h => h
  | .cond c body, h => by
      simp only [dsStmt, storageLayoutFreeStmt, Bool.and_eq_true] at h ⊢
      exact ⟨h.1, dsSweep_layoutFree _ _ _ (dsStmts_layoutFree bound body h.2)⟩
  | .switch c cs d, h => by
      simp only [dsStmt, storageLayoutFreeStmt, Bool.and_eq_true] at h ⊢
      exact ⟨⟨h.1.1, dsCases_layoutFree bound cs h.1.2⟩, dsDflt_layoutFree bound d h.2⟩
  | .forLoop init c post body, h => by
      simp only [dsStmt, storageLayoutFreeStmt, Bool.and_eq_true] at h ⊢
      exact ⟨⟨⟨h.1.1.1, h.1.1.2⟩,
        dsSweep_layoutFree _ _ _ (dsStmts_layoutFree bound post h.1.2)⟩,
        dsSweep_layoutFree _ _ _ (dsStmts_layoutFree bound body h.2)⟩
  | .exprStmt _, h => h
  | .break, h => h
  | .continue, h => h
  | .leave, h => h

/-- Recursion preserves layout-freedom of a sequence. -/
theorem dsStmts_layoutFree (bound : List Ident) : ∀ ss : List (Stmt Op),
    storageLayoutFreeStmts ss = true → storageLayoutFreeStmts (dsStmts bound ss) = true
  | [], h => h
  | s :: rest, h => by
      simp only [dsStmts, storageLayoutFreeStmts, Bool.and_eq_true] at h ⊢
      exact ⟨dsStmt_layoutFree bound s h.1, dsStmts_layoutFree bound rest h.2⟩

/-- Recursion preserves layout-freedom of the `switch` cases. -/
theorem dsCases_layoutFree (bound : List Ident) : ∀ cs : List (Literal × Block Op),
    storageLayoutFreeCases cs = true → storageLayoutFreeCases (dsCases bound cs) = true
  | [], h => h
  | (_, b) :: rest, h => by
      simp only [dsCases, storageLayoutFreeCases, Bool.and_eq_true] at h ⊢
      exact ⟨dsSweep_layoutFree _ _ _ (dsStmts_layoutFree bound b h.1),
        dsCases_layoutFree bound rest h.2⟩

/-- Recursion preserves layout-freedom of the `switch` default. -/
theorem dsDflt_layoutFree (bound : List Ident) : ∀ d : Option (Block Op),
    storageLayoutFreeDflt d = true → storageLayoutFreeDflt (dsDflt bound d) = true
  | none, h => h
  | some b, h => dsSweep_layoutFree _ _ _ (dsStmts_layoutFree bound b h)

end

/-- One whole-block sweep preserves layout-freedom. -/
theorem dsOnce_layoutFree (b : Block Op) (h : storageLayoutFreeStmts b = true) :
    storageLayoutFreeStmts (dsOnce b) = true :=
  dsSweep_layoutFree [] [] _ (dsStmts_layoutFree [] b h)

/-! ### The two obligations -/

/-- **Soundness.** Both rewrites only change the value bound to a name that (a) is
declared by a `letDecl` of the sequence being rewritten, so the sequence's
`restore` erases it at every exit, and (b) is not read before its next write or
that exit. `alwaysEval` makes the dropped right-hand side total and
state-preserving, so no halt or `EvmState` change is lost. -/
theorem deadStoresBlock_equiv (b : Block Op) : EquivBlock D b (deadStoresBlock b) := by
  unfold deadStoresBlock
  by_cases hlf : storageLayoutFreeStmts b
  · rw [if_pos hlf]
    exact (dsBody_of [] b (dsStmts_bequiv [] b) (dsStmts_scopeRel [] b)).toEquiv
  · rw [if_neg hlf]
    exact @EquivBlock.refl (evmWithExternal calls creates gasOracle) _ b

/-- **Resolution congruence.** `deadStoresBlock` guards on
`storageLayoutFreeStmts` and preserves it, so on layout-free input resolution is
the identity on both sides and the congruence is the pass's own soundness; off
the guard the transform is the identity. -/
theorem resolveDeadStoresBlock_equiv (L : Layout) (b : Block Op) :
    EquivBlock D (resolveForLayoutStmts L b)
      (resolveForLayoutStmts L (deadStoresBlock b)) := by
  unfold deadStoresBlock
  by_cases hlf : storageLayoutFreeStmts b
  · rw [if_pos hlf, resolve_storageLayoutFreeStmts L b hlf,
      resolve_storageLayoutFreeStmts L _ (dsOnce_layoutFree b hlf)]
    exact (dsBody_of [] b (dsStmts_bequiv [] b) (dsStmts_scopeRel [] b)).toEquiv
  · rw [if_neg hlf]
    exact @EquivBlock.refl (evmWithExternal calls creates gasOracle) _ _

/-! ### The pass -/

/-- The **DeadStores pass**: dead assignment and dead initialiser elimination. -/
def deadStores : LocalPass D where
  run := deadStoresBlock
  sound := fun b => deadStoresBlock_equiv (calls := calls) (creates := creates) (gasOracle := gasOracle) b

@[simp] theorem deadStores_run (b : Block Op) :
    (deadStores (calls := calls) (creates := creates) (gasOracle := gasOracle)).run b = deadStoresBlock b := rfl

/-! ### The post-layout cleanup

`stackLayoutBlock` runs *after* the whole optimizer pipeline, so nothing has
cleaned up behind its slot reuse and live-range splitting. The cleanup is this
pass plus three passes that were already proved, in the order that makes them
compound:

* `deadStores` deletes the dead stores and turns dead initialisers into bare
  binders;
* `fuseDeclAssign` fuses each bare binder back onto its next same-level
  assignment, which is what actually removes the slot's `push 0` and that
  store's `swap; pop`;
* `coalesceCopies` collapses the copy chains live-range splitting introduces;
* `deadPure` removes any binding left with no reader at all — the only one of
  the four that removes a scope-exit `pop`.

Iterating twice lets `deadPure`'s deletions expose fresh dead stores and vice
versa. Every stage is a `LocalPass`, so the composition is sound by
`LocalPass.ofList` with no new proof obligation beyond `deadStores`' own. -/
def cleanupAfterLayout : LocalPass D :=
  LocalPass.ofList
    [deadStores, fuseDeclAssign, coalesceCopies, deadPure,
     deadStores, fuseDeclAssign, coalesceCopies, deadPure]

/-- `cleanupAfterLayout` on a block. -/
def cleanupAfterLayoutBlock (b : Block Op) : Block Op :=
  (cleanupAfterLayout (calls := calls) (creates := creates) (gasOracle := gasOracle)).run b

mutual
  /-- `cleanupAfterLayout` on every code block of an object tree. -/
  def cleanupAfterLayoutObject : Object Op → Object Op
    | .mk name code subs segs =>
        .mk name (cleanupAfterLayoutBlock (calls := calls) (creates := creates) (gasOracle := gasOracle) code)
          (cleanupAfterLayoutObjects subs) segs

  def cleanupAfterLayoutObjects : List (Object Op) → List (Object Op)
    | [] => []
    | o :: os => cleanupAfterLayoutObject o :: cleanupAfterLayoutObjects os
end

/-! ### Regression examples (checked at build time) -/

-- R1: a dead assignment to a sequence-local name goes; so does the last store
-- before the end of the sequence, whose value the `restore` discards.
example : dsSweep [] [] [.letDecl ["x"] (some (.lit (.number 1))),
    .assign ["x"] (.lit (.number 2)),
    .exprStmt (.builtin .sstore [.lit (.number 0), .var "x"]),
    .assign ["x"] (.lit (.number 3))]
  = [.letDecl ["x"] none,
     .assign ["x"] (.lit (.number 2)),
     .exprStmt (.builtin .sstore [.lit (.number 0), .var "x"])] := rfl

-- An assignment to a name this sequence does not declare stays: it may be
-- observable in the ambient environment `EquivBlock` quantifies over.
example : dsSweep [] [] [.assign ["x"] (.lit (.number 2)),
    .assign ["x"] (.lit (.number 3))]
  = [.assign ["x"] (.lit (.number 2)), .assign ["x"] (.lit (.number 3))] := rfl

-- An effectful right-hand side is never dropped, dead or not.
example : dsSweep [] [] [.letDecl ["x"] (some (.lit (.number 1))),
    .assign ["x"] (.builtin .mload [.lit (.number 0)]),
    .exprStmt (.builtin .sstore [.lit (.number 0), .var "x"])]
  = [.letDecl ["x"] none,
     .assign ["x"] (.builtin .mload [.lit (.number 0)]),
     .exprStmt (.builtin .sstore [.lit (.number 0), .var "x"])] := rfl

-- A conditional that mentions the name blocks the rewrite (the branch may not
-- run, so a write inside it cannot kill the outer value).
example : dsSweep [] [] [.letDecl ["x"] (some (.lit (.number 1))),
    .assign ["x"] (.lit (.number 2)),
    .cond (.lit (.number 1)) [.exprStmt (.builtin .sstore [.lit (.number 0), .var "x"])]]
  = [.letDecl ["x"] none,
     .assign ["x"] (.lit (.number 2)),
     .cond (.lit (.number 1)) [.exprStmt (.builtin .sstore [.lit (.number 0), .var "x"])]] := rfl

-- A `break` ends the sequence's scope, so the store before it is dead.
example : dsSweep [] [] [.letDecl ["x"] (some (.lit (.number 1))),
    .assign ["x"] (.lit (.number 2)), .«break»]
  = [.letDecl ["x"] none, .«break»] := rfl

-- Function returns are not `owned`, so a store to one survives.
example : dsStmt [] (.funDef "f" [] ["r"] [.assign ["r"] (.lit (.number 1))])
  = .funDef "f" [] ["r"] [.assign ["r"] (.lit (.number 1))] := rfl

-- A `for`-init declaration is loop-carried and not `owned` by the body.
example : dsStmt [] (.forLoop [.letDecl ["i"] (some (.lit (.number 0)))]
    (.lit (.number 1)) [] [.assign ["i"] (.lit (.number 2))])
  = .forLoop [.letDecl ["i"] (some (.lit (.number 0)))]
      (.lit (.number 1)) [] [.assign ["i"] (.lit (.number 2))] := rfl

-- The measured `stackLayout` residue: a body-local slot written twice with a
-- `break` test between, and an initialiser whose value is overwritten.
example : dsSweep ["v19"] []
    [.letDecl ["v20"] (some (.var "v19")),
     .assign ["v20"] (.var "v19"),
     .cond (.builtin .iszero [.var "v19"]) [.«break»],
     .assign ["v20"] (.var "v19"),
     .exprStmt (.builtin .sstore [.lit (.number 0), .var "v20"])]
  = [.letDecl ["v20"] none,
     .cond (.builtin .iszero [.var "v19"]) [.«break»],
     .assign ["v20"] (.var "v19"),
     .exprStmt (.builtin .sstore [.lit (.number 0), .var "v20"])] := rfl

end YulEvmCompiler.Optimizer
