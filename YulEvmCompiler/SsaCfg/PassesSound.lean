import YulEvmCompiler.SsaCfg.Passes
import YulEvmCompiler.SsaCfg.Sem
import YulSemantics.Dialect.EVM
/-!
# YulEvmCompiler.SsaCfg.PassesSound

Soundness metatheory for the `yul-ssa-cfg` optimization passes
(`SsaCfg/Passes.lean`), i.e. the material behind the `sorry`'d
`SsaCfg.optimizeProg_sound` of `SsaCfg/Correctness.lean`.

## ⚠ Headline result: `optimizeProg_sound` is FALSE as stated

The statement

    P.wfCheck = true → Run P yst0 yst' o → Run (optimizeProg P) yst0 yst' o

is **refuted** here — see `Counterexample.optimizeProg_sound_false`, a fully
machine-checked counterexample (no `sorry`, no `native_decide`, no axioms beyond
Lean's own). The reason is not a coding mistake in a pass: it is a *missing
hypothesis*. Pass 1 (trivial block-parameter elimination) and pass 3 (local CSE)
are only sound for programs that respect **SSA dominance** (every use of a value
is dominated by its definition), and `Prog.wfCheck` deliberately does *not* check
dominance — `Ir.lean` says so explicitly:

> Dominance ("every use is dominated by its definition") is deliberately *not*
> checked structurally here; the semantics gets stuck on an unbound `ValId` read …

But "gets stuck on an unbound read" is not the only way dominance can be
violated: in this semantics **registers persist across blocks** and a block
parameter is *re-bound* on every visit, so a use that its definition does not
dominate can legitimately read a **stale** binding left over from an earlier
visit. Substituting such a use (pass 1 replaces the parameter `p` by the value
`v` that every in-edge passes; pass 3 replaces a repeated computation by an
earlier `ValId`) then reads the *current* value instead of the stale one, which
changes the program's behavior. The defensive `Prog.wfCheck` re-check inside
`optimizeProg` does not catch it: the rewritten program is perfectly well-formed.

The counterexample program (`Counterexample.P`) is exactly that shape: block 3
reads the parameter `p` of block 2, which does not dominate block 3.

### What the fix looks like

Either
* strengthen `Prog.wfCheck` with a dominance check (and re-derive the extra
  invariant in `ofBlock_wfCheck`), or
* keep `wfCheck` as is and give `optimizeProg_sound` an extra hypothesis stating
  that `P` respects SSA dominance, discharged for the construction's output by a
  new lemma next to `ofBlock_wfCheck`.

Passes 2 (constant folding) and 4 (dead value elimination) do *not* need
dominance: `constFold` only rewrites an op into the constant its operands'
`const` definitions already force (single assignment is enough), and `dve` only
deletes definitions that nothing reads.

## What is proved here

* `Regs` plumbing: `setMany_cons`, `getMany_congr`, `set_congr`, `setMany_congr`.
* The **frame lemma** `exec_congr`: `Exec` only reads registers named in the
  current fragment or somewhere in the enclosing function, so two register files
  agreeing there give the same execution. This is the reusable "Regs agreement"
  lemma passes 1, 3 and 4 all need.
* The **purity leaves**, transported from the pinned dialect's own
  `effects_sound_withExternal`:
  * `builtin_of_pure` — a pure op is never an open-world (`call`/`create`/`gas`)
    op, so its combined relation *is* the executable `stepOp` graph;
  * `pure_state_eq` — a pure op leaves the machine state alone;
  * `pure_rets_eq` — **CSE leaf**: equal `(op, args)` ⇒ equal results, in any
    two states;
  * `evalPure_stepOp` / `evalPure_transport` — **constant-folding leaf**: what
    the folder computed on `EvmState.init` is what the op returns in *any* state.
* The **defensive-fallback case** of the pipeline (`optimizeProg_of_wfCheck_false`,
  `optimizeProg_sound_of_fallback`): when the pipeline output fails `wfCheck`,
  `optimizeProg` returns the original program and soundness is reflexivity.
* The **counterexample** (§ `Counterexample`), end to end: `P.wfCheck = true`,
  `optimizeProg P = Popt` (the whole 3-round, 4-pass pipeline, evaluated inside
  the kernel), `Run P yst yst .normal`, `¬ Run Popt yst yst .normal`.

Remaining `sorry`s are the per-pass simulation arguments, each marked with what
it needs; `optimizeProg_sound'` itself is kept only to mirror
`Correctness.optimizeProg_sound` and **must not be closed** — it is false.
-/

namespace YulEvmCompiler.SsaCfg

open YulSemantics.EVM (U256 EvmState Op builtinWithExternal stepOp ExternalCalls
  ExternalCreates)
open YulSemantics (Outcome)

/-! ## `Regs` plumbing -/

namespace Regs

theorem setMany_nil_left (R : Regs) (vs : List U256) : R.setMany [] vs = R := rfl

theorem setMany_nil_right (R : Regs) (xs : List ValId) : R.setMany xs [] = R := by
  cases xs <;> rfl

theorem setMany_cons (R : Regs) (x : ValId) (xs : List ValId) (v : U256) (vs : List U256) :
    R.setMany (x :: xs) (v :: vs) = (R.set x v).setMany xs vs := rfl

/-- Reading a list of ids only depends on the register file at those ids. -/
theorem getMany_congr {R1 R2 : Regs} {xs : List ValId} (h : ∀ x ∈ xs, R1 x = R2 x) :
    R1.getMany xs = R2.getMany xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [getMany_cons, getMany_cons, h x (by simp), ih (fun y hy => h y (by simp [hy]))]

/-- Agreement on a set of ids survives one binding (the same one on both sides). -/
theorem set_congr {S : ValId → Prop} {R1 R2 : Regs} (h : ∀ x, S x → R1 x = R2 x)
    (d : ValId) (v : U256) : ∀ x, S x → (R1.set d v) x = (R2.set d v) x := by
  intro x hx
  by_cases hxd : x = d
  · simp [set, hxd]
  · simp [set, hxd, h x hx]

/-- Agreement on a set of ids survives a parallel binding. -/
theorem setMany_congr {S : ValId → Prop} {R1 R2 : Regs} (h : ∀ x, S x → R1 x = R2 x)
    (xs : List ValId) (vs : List U256) :
    ∀ x, S x → (R1.setMany xs vs) x = (R2.setMany xs vs) x := by
  induction xs generalizing R1 R2 vs with
  | nil => simpa [setMany_nil_left] using h
  | cons y ys ih =>
    cases vs with
    | nil => simpa [setMany_nil_right] using h
    | cons v vs => simpa [setMany_cons] using ih (set_congr h y v) (vs := vs)

end Regs

/-! ## Read sets -/

/-- The values the rest of a block reads directly. -/
def Rest.uses (r : Rest) : List ValId := r.instrs.flatMap Instr.uses ++ r.term.uses

/-- Every value read anywhere in a function (all blocks, instructions and
terminators). A jump can transfer control to any block of `f`, so this is the
read set the frame lemma has to fix. -/
def Func.allUses (f : Func) : List ValId :=
  f.blocks.toList.flatMap fun b => b.instrs.flatMap Instr.uses ++ b.term.uses

theorem Rest.uses_tail {i : Instr} {is : List Instr} {t : Term} {x : ValId}
    (h : x ∈ (Rest.mk is t).uses) : x ∈ (Rest.mk (i :: is) t).uses := by
  simp only [Rest.uses, List.mem_append, List.mem_flatMap] at h ⊢
  rcases h with ⟨j, hj, hx⟩ | h
  · exact Or.inl ⟨j, by simp [hj], hx⟩
  · exact Or.inr h

theorem Rest.mem_uses_of_instr {i : Instr} {is : List Instr} {t : Term} {x : ValId}
    (h : x ∈ i.uses) : x ∈ (Rest.mk (i :: is) t).uses := by
  simp only [Rest.uses, List.mem_append, List.mem_flatMap]
  exact Or.inl ⟨i, by simp, h⟩

theorem Rest.mem_uses_of_term {is : List Instr} {t : Term} {x : ValId} (h : x ∈ t.uses) :
    x ∈ (Rest.mk is t).uses := by
  simp only [Rest.uses, List.mem_append]
  exact Or.inr h

theorem Func.mem_allUses_of_block {f : Func} {i : BlockId} {b : Block} {x : ValId}
    (hb : f.blocks[i]? = some b) (hx : x ∈ (Rest.mk b.instrs b.term).uses) :
    x ∈ f.allUses := by
  have hmem : b ∈ f.blocks.toList := by
    obtain ⟨hlt, hget⟩ := Array.getElem?_eq_some_iff.mp hb
    exact List.mem_iff_getElem.mpr ⟨i, by simpa using hlt, by simpa using hget⟩
  simp only [Func.allUses, List.mem_flatMap]
  exact ⟨b, hmem, by simpa [Rest.uses] using hx⟩

/-! ## The frame lemma -/

section Frame
variable [model : ExternalModel]

/-- **Regs agreement (frame lemma)**. An `Exec` derivation reads registers only
through the `uses` of the instruction/terminator it is currently at, and control
never leaves the enclosing function's blocks, so two register files that agree on
`f.allUses` and on the current fragment's uses admit the *same* executions.

This is the central reusable lemma for the passes that delete definitions
(pass 4) or reroute uses (passes 1 and 3): it lets one replace the original
register file by the optimized one wherever the two agree on what is read. -/
theorem exec_congr {P : Prog} {f : Func} {R1 : Regs} {st : EvmState} {rest : Rest}
    {res : FRes} (h : Exec (model := model) P f R1 st rest res) :
    ∀ R2 : Regs, (∀ x ∈ f.allUses, R1 x = R2 x) → (∀ x ∈ rest.uses, R1 x = R2 x) →
      Exec (model := model) P f R2 st rest res := by
  induction h with
  | @const f R st d v is t res _ ih =>
    intro R2 hU hR
    refine Exec.const (ih (R2.set d v) ?_ ?_)
    · exact Regs.set_congr (S := fun x => x ∈ f.allUses) hU d v
    · exact Regs.set_congr (S := fun x => x ∈ (Rest.mk is t).uses)
        (fun x hx => hR x (Rest.uses_tail hx)) d v
  | @op f R st st' ds yop as args rets is t res hg hb hlen _ ih =>
    intro R2 hU hR
    refine Exec.op (args := args) (rets := rets) ?_ hb hlen (ih _ ?_ ?_)
    · rw [← Regs.getMany_congr (R1 := R) (R2 := R2)
        (fun x hx => hR x (Rest.mem_uses_of_instr (i := .op ds yop as)
          (by simpa [Instr.uses] using hx)))]
      exact hg
    · exact Regs.setMany_congr (S := fun x => x ∈ f.allUses) hU ds rets
    · exact Regs.setMany_congr (S := fun x => x ∈ (Rest.mk is t).uses)
        (fun x hx => hR x (Rest.uses_tail hx)) ds rets
  | @opHalt f R st st' ds yop as args is t hg hb =>
    intro R2 _ hR
    refine Exec.opHalt (args := args) ?_ hb
    rw [← Regs.getMany_congr (R1 := R) (R2 := R2)
      (fun x hx => hR x (Rest.mem_uses_of_instr (i := .op ds yop as)
        (by simpa [Instr.uses] using hx)))]
    exact hg
  | @call f g R st st' ds as fid args rvals eb is t res hfid hg hplen heb _ hlen _ ihbody ih =>
    intro R2 hU hR
    refine Exec.call (args := args) (rvals := rvals) (g := g) (eb := eb) hfid ?_ hplen heb
      (ihbody _ (fun _ _ => rfl) (fun _ _ => rfl)) hlen (ih _ ?_ ?_)
    · rw [← Regs.getMany_congr (R1 := R) (R2 := R2)
        (fun x hx => hR x (Rest.mem_uses_of_instr (i := .call ds fid as)
          (by simpa [Instr.uses] using hx)))]
      exact hg
    · exact Regs.setMany_congr (S := fun x => x ∈ f.allUses) hU ds rvals
    · exact Regs.setMany_congr (S := fun x => x ∈ (Rest.mk is t).uses)
        (fun x hx => hR x (Rest.uses_tail hx)) ds rvals
  | @callHalt f g R st st' ds as fid args eb is t hfid hg hplen heb _ ihbody =>
    intro R2 _ hR
    refine Exec.callHalt (args := args) (g := g) (eb := eb) hfid ?_ hplen heb
      (ihbody _ (fun _ _ => rfl) (fun _ _ => rfl))
    rw [← Regs.getMany_congr (R1 := R) (R2 := R2)
      (fun x hx => hR x (Rest.mem_uses_of_instr (i := .call ds fid as)
        (by simpa [Instr.uses] using hx)))]
    exact hg
  | @jump f R st e tb args res htb hg hplen _ ih =>
    intro R2 hU hR
    refine Exec.jump (args := args) (tb := tb) htb ?_ hplen (ih _ ?_ ?_)
    · rw [← Regs.getMany_congr (R1 := R) (R2 := R2)
        (fun x hx => hR x (Rest.mem_uses_of_term (by simpa [Term.uses] using hx)))]
      exact hg
    · exact Regs.setMany_congr (S := fun x => x ∈ f.allUses) hU tb.params args
    · exact Regs.setMany_congr (S := fun x => x ∈ (Rest.mk tb.instrs tb.term).uses)
        (fun x hx => hU x (Func.mem_allUses_of_block htb hx)) tb.params args
  | @branchTrue f R st c v et ef tb args res hc hv htb hg hplen _ ih =>
    intro R2 hU hR
    have hcU : c ∈ (Rest.mk ([] : List Instr) (Term.branch c et ef)).uses := by
      simp [Rest.uses, Term.uses]
    refine Exec.branchTrue (v := v) (args := args) (tb := tb) (by rw [← hR c hcU]; exact hc) hv
      htb ?_ hplen (ih _ ?_ ?_)
    · rw [← Regs.getMany_congr (R1 := R) (R2 := R2)
        (fun x hx => hR x (Rest.mem_uses_of_term (by simp [Term.uses]; exact Or.inr (Or.inl hx))))]
      exact hg
    · exact Regs.setMany_congr (S := fun x => x ∈ f.allUses) hU tb.params args
    · exact Regs.setMany_congr (S := fun x => x ∈ (Rest.mk tb.instrs tb.term).uses)
        (fun x hx => hU x (Func.mem_allUses_of_block htb hx)) tb.params args
  | @branchFalse f R st c et ef tb args res hc htb hg hplen _ ih =>
    intro R2 hU hR
    have hcU : c ∈ (Rest.mk ([] : List Instr) (Term.branch c et ef)).uses := by
      simp [Rest.uses, Term.uses]
    refine Exec.branchFalse (args := args) (tb := tb) (by rw [← hR c hcU]; exact hc) htb ?_ hplen
      (ih _ ?_ ?_)
    · rw [← Regs.getMany_congr (R1 := R) (R2 := R2)
        (fun x hx => hR x (Rest.mem_uses_of_term (by simp [Term.uses]; exact Or.inr (Or.inr hx))))]
      exact hg
    · exact Regs.setMany_congr (S := fun x => x ∈ f.allUses) hU tb.params args
    · exact Regs.setMany_congr (S := fun x => x ∈ (Rest.mk tb.instrs tb.term).uses)
        (fun x hx => hU x (Func.mem_allUses_of_block htb hx)) tb.params args
  | @ret f R st xs vals hg =>
    intro R2 _ hR
    refine Exec.ret ?_
    rw [← Regs.getMany_congr (R1 := R) (R2 := R2)
      (fun x hx => hR x (Rest.mem_uses_of_term (by simpa [Term.uses] using hx)))]
    exact hg
  | @halt f R st st' yop as args hg hb =>
    intro R2 _ hR
    refine Exec.halt (args := args) ?_ hb
    rw [← Regs.getMany_congr (R1 := R) (R2 := R2)
      (fun x hx => hR x (Rest.mem_uses_of_term (by simpa [Term.uses] using hx)))]
    exact hg

end Frame

/-! ## Purity leaves

Everything the value-level passes need about built-ins comes from the pinned
dialect's own `effects_sound_withExternal`: a `pure` op (per the dialect's
`effects` table, which is what `Passes.pureOp` reads) is deterministic,
non-reading, non-writing and non-halting. -/

namespace Passes

theorem pureOp_flags {yop : Op} (h : pureOp yop = true) :
    (YulSemantics.EVM.effects yop).deterministic = true
    ∧ (YulSemantics.EVM.effects yop).reads = false
    ∧ (YulSemantics.EVM.effects yop).writes = false
    ∧ (YulSemantics.EVM.effects yop).halts = false := by
  simp only [pureOp, YulSemantics.Effects.pure, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- A pure built-in is never one of the open-world operations (`call`-family,
`create`-family, `gas`), so its combined local/external relation is exactly the
executable `stepOp` graph — which is what `evalPure` folds with. -/
theorem builtin_of_pure {calls : ExternalCalls} {creates : ExternalCreates} {yop : Op}
    (h : pureOp yop = true) {args : List U256} {st : EvmState}
    {r : YulSemantics.BuiltinResult U256 EvmState} :
    builtinWithExternal calls creates yop args st r ↔ stepOp yop args st = some r := by
  cases yop <;> first
    | exact Iff.rfl
    | (exfalso; revert h; decide)

/-- A pure built-in leaves the machine state untouched. -/
theorem pure_state_eq {calls : ExternalCalls} {creates : ExternalCreates} {yop : Op}
    (hp : pureOp yop = true) {args : List U256} {st st' : EvmState} {rets : List U256}
    (hb : builtinWithExternal calls creates yop args st (.ok rets st')) : st' = st :=
  (YulSemantics.EVM.effects_sound_withExternal calls creates).write yop
    (pureOp_flags hp).2.2.1 args st (.ok rets st') hb

/-- **CSE leaf**: a pure built-in's results are a function of its arguments
alone, so two evaluations of the same `(op, args)` — in *any* two states, hence
at any two program points — return the same values. -/
theorem pure_rets_eq {calls : ExternalCalls} {creates : ExternalCreates} {yop : Op}
    (hp : pureOp yop = true) {args : List U256} {st1 st2 st1' st2' : EvmState}
    {rets1 rets2 : List U256}
    (h1 : builtinWithExternal calls creates yop args st1 (.ok rets1 st1'))
    (h2 : builtinWithExternal calls creates yop args st2 (.ok rets2 st2')) : rets1 = rets2 :=
  (YulSemantics.EVM.effects_sound_withExternal calls creates).read yop
    (pureOp_flags hp).2.1 args st1 st2 rets1 st1' rets2 st2' h1 h2

/-- Invert a successful `evalPure`: the folder saw a clean single-value return
from the dialect's own step function on the initial state. -/
theorem evalPure_stepOp {yop : Op} {args : List U256} {v : U256}
    (h : evalPure yop args = some v) :
    ∃ st', stepOp yop args YulSemantics.EVM.EvmState.init = some (.ok [v] st') := by
  unfold evalPure at h
  rw [ite_eq_iff] at h
  rcases h with ⟨-, h⟩ | ⟨-, h⟩
  · exact absurd h (by simp)
  · rcases hs : stepOp yop args YulSemantics.EVM.EvmState.init with _ | r <;> rw [hs] at h
    · exact absurd h (by simp)
    · rcases r with ⟨rets, st'⟩ | st'
      · rcases rets with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> simp at h
        exact ⟨st', by rw [h]⟩
      · exact absurd h (by simp)

/-- **Constant-folding leaf**: whatever the folder computed on `EvmState.init` is
what the built-in returns in *any* state, and the state is untouched. This is the
transport that lets `constFold` replace `.op [d] yop args` by `.const d v`. -/
theorem evalPure_transport {calls : ExternalCalls} {creates : ExternalCreates} {yop : Op}
    (hp : pureOp yop = true) {args : List U256} {v : U256}
    (he : evalPure yop args = some v) {st st' : EvmState} {rets : List U256}
    (hb : builtinWithExternal calls creates yop args st (.ok rets st')) :
    rets = [v] ∧ st' = st := by
  obtain ⟨s0, hstep⟩ := evalPure_stepOp he
  have hb0 : builtinWithExternal calls creates yop args YulSemantics.EVM.EvmState.init
      (.ok [v] s0) := (builtin_of_pure hp).mpr hstep
  exact ⟨pure_rets_eq hp hb hb0, pure_state_eq hp hb⟩

end Passes

/-! ## The defensive fallback

`optimizeProg` re-runs `Prog.wfCheck` on the pipeline's output and returns the
*original* program when the check fails, so that case of pass soundness is
reflexivity. -/

theorem optimizeProg_of_wfCheck_false {P : Prog}
    (h : (Prog.mk (optimizeFunc P.main) (P.funcs.map optimizeFunc)).wfCheck = false) :
    optimizeProg P = P := by
  unfold optimizeProg
  simp only [h, Bool.false_eq_true, if_false]

section
variable [model : ExternalModel]

/-- The fallback branch of pass soundness, fully proved. -/
theorem optimizeProg_sound_of_fallback {P : Prog} {yst0 yst' : EvmState} {o : Outcome}
    (h : (Prog.mk (optimizeFunc P.main) (P.funcs.map optimizeFunc)).wfCheck = false)
    (hrun : Run (model := model) P yst0 yst' o) :
    Run (model := model) (optimizeProg P) yst0 yst' o := by
  rw [optimizeProg_of_wfCheck_false h]; exact hrun

end

/-! ## The counterexample

A `wfCheck`-clean program whose optimized form has a *different* observable
behavior. The witness is a stale block-parameter read: block `3` reads `p`, the
parameter of block `2`, on a path that does not go through block `2` — legal
under `wfCheck` (which does not check dominance) and not stuck (a previous visit
to block `2` left `p` bound). Pass 1 sees that block `2`'s only in-edge passes
`v`, declares `p` trivial and substitutes `p := v`; by the time block `3` runs,
`v` has been re-bound by the loop back-edge, so the substituted program branches
the other way: the original returns normally, the optimized one halts.

Every step below is checked by the kernel, including the syntactic claim
`optimizeProg P = Popt` — the whole 3-round, 4-pass pipeline. The `simp only
[… forIn_eq_forIn_range' …]` rewrites turn `Std.Legacy.Range` `for` loops (whose
`loop` is well-founded, hence irreducible) into list loops, and `unseal
Array.anyM.loop` lets `Array.all` — used by `wfCheck` — reduce. -/

namespace Counterexample

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-- entry: `c10 ← 1`, `c11 ← 0`; `jump B1(c10)`. -/
def b0 : Block := ⟨[], [.const 10 1, .const 11 0], .jump ⟨1, [10]⟩⟩
/-- `B1(v)`: `branch v → B2(v) : B3()`. -/
def b1 : Block := ⟨[1], [], .branch 1 ⟨2, [1]⟩ ⟨3, []⟩⟩
/-- `B2(p)`: `jump B1(c11)` — the back-edge that re-binds `v` to `0`. -/
def b2 : Block := ⟨[2], [], .jump ⟨1, [11]⟩⟩
/-- `B3()`: `branch p → B4 : B5`. **`B2` does not dominate `B3`**, yet `B3`
reads `B2`'s parameter `p` — the stale read. -/
def b3 : Block := ⟨[], [], .branch 2 ⟨4, []⟩ ⟨5, []⟩⟩
def b4 : Block := ⟨[], [], .ret []⟩
def b5 : Block := ⟨[], [], .halt .invalid []⟩

def fMain : Func := { params := [], nrets := 0, entry := 0, blocks := #[b0,b1,b2,b3,b4,b5] }

/-- The counterexample program. -/
def P : Prog := { main := fMain, funcs := #[] }

/-- `B1` after pass 1: the argument position for `B2`'s dropped parameter is gone. -/
def b1' : Block := ⟨[1], [], .branch 1 ⟨2, []⟩ ⟨3, []⟩⟩
/-- `B2` after pass 1: no parameters. -/
def b2' : Block := ⟨[], [], .jump ⟨1, [11]⟩⟩
/-- `B3` after pass 1: `p` has been substituted by `v` — this is the bug. -/
def b3' : Block := ⟨[], [], .branch 1 ⟨4, []⟩ ⟨5, []⟩⟩

def fMain' : Func := { params := [], nrets := 0, entry := 0, blocks := #[b0,b1',b2',b3',b4,b5] }

/-- What the pipeline turns `P` into. -/
def Popt : Prog := { main := fMain', funcs := #[] }

/-! ### The syntactic half: `optimizeProg P = Popt`, in the kernel -/

theorem r2 : List.range' 0 2 1 = [0,1] := by rfl
theorem r3 : List.range' 0 3 1 = [0,1,2] := by rfl
theorem r6 : List.range' 0 6 1 = [0,1,2,3,4,5] := by rfl
theorem r9 : List.range' 0 9 1 = [0,1,2,3,4,5,6,7,8] := by rfl

theorem findT : Passes.findTrivialParam fMain = some (2,0,2,1) := by
  simp only [Passes.findTrivialParam, Std.Legacy.Range.forIn_eq_forIn_range']; rfl

theorem findT' : Passes.findTrivialParam fMain' = none := by
  simp only [Passes.findTrivialParam, Std.Legacy.Range.forIn_eq_forIn_range']; rfl

theorem hsub : Passes.substFunc ((∅ : Passes.Subst).insert 2 1)
    (Passes.removeParam fMain 2 0) = fMain' := by
  simp [Passes.substFunc, Passes.substBlock, Passes.substTerm, Passes.substEdge,
    Passes.substVs, Passes.substInstr, Passes.substV, Passes.removeParam, Passes.mapEdges,
    fMain, fMain', b0,b1,b2,b3,b4,b5, b1',b2',b3', Std.HashMap.getD_insert]

theorem hfuel : fMain.blocks.foldl (fun n b => n + b.params.length) 0 = 2 := by rfl
theorem hfuel' : fMain'.blocks.foldl (fun n b => n + b.params.length) 0 = 1 := by rfl

theorem hetp : Passes.elimTrivialParams fMain = fMain' := by
  simp only [Passes.elimTrivialParams, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, hfuel]
  simp [show (2 + 1 - 0 + 1 - 1) / 1 = 3 from rfl, r3, findT, findT', hsub]

theorem hetp' : Passes.elimTrivialParams fMain' = fMain' := by
  simp only [Passes.elimTrivialParams, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, hfuel']
  simp [show (1 + 1 - 0 + 1 - 1) / 1 = 2 from rfl, r2, findT']

theorem hcf : Passes.constFold fMain' = fMain' := by
  simp [Passes.constFold, fMain', b0, b1', b2', b3', b4, b5, Passes.pureOp]

theorem hsrc : Passes.inEdgeSources fMain' = #[[], [2,0], [1], [1], [3], [3]] := by
  simp only [Passes.inEdgeSources, Std.Legacy.Range.forIn_eq_forIn_range']; rfl

unseal Array.anyM.loop in
theorem hcse : Passes.cse fMain' = fMain' := by
  simp only [Passes.cse, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, hsrc]
  simp [show (fMain'.blocks.size - 0 + 1 - 1) / 1 = 6 from rfl, r6, fMain',
    b0,b1',b2',b3',b4,b5, Passes.pureOp, Passes.substFunc, Passes.substBlock, Passes.substTerm,
    Passes.substEdge, Passes.substVs, Passes.substInstr, Passes.substV,
    Std.HashMap.getD_insert]

unseal Array.anyM.loop in
theorem hdve : Passes.dve fMain' = fMain' := by
  simp only [Passes.dve, Passes.liveSet, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size]
  simp [r9, fMain', b0,b1',b2',b3',b4,b5, Passes.pureOp, Passes.liveStep,
    Passes.mapEdges, Func.allDefs, Instr.defs, Instr.uses, Term.uses, Term.edges,
    Std.HashSet.size_insert, Std.HashSet.mem_insert, Std.HashSet.size_empty]

theorem hrun1 : Passes.runOnce fMain = fMain' := by
  simp only [Passes.runOnce, hetp, hcf, hcse, hdve]

theorem hrun2 : Passes.runOnce fMain' = fMain' := by
  simp only [Passes.runOnce, hetp', hcf, hcse, hdve]

theorem hoptf : optimizeFunc fMain = fMain' := by
  simp only [optimizeFunc, Passes.pipelineRounds, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size]
  simp [show (3 - 0 + 1 - 1) / 1 = 3 from rfl, r3, hrun1, hrun2]

unseal Array.anyM.loop in
/-- The counterexample program passes the well-formedness gate. -/
theorem hwf : P.wfCheck = true := by rfl

unseal Array.anyM.loop in
/-- …and so does its optimized form, so the defensive fallback does not fire. -/
theorem hwfopt : Popt.wfCheck = true := by rfl

/-- The pipeline really does produce `Popt`. -/
theorem hopt : optimizeProg P = Popt := by
  have h : ({ main := optimizeFunc P.main, funcs := P.funcs.map optimizeFunc } : Prog) = Popt := by
    simp only [P, Popt, hoptf]
    simp
  simp only [optimizeProg, h, hwfopt, if_true]

/-! ### The semantic half -/

theorem setMany_nn (R : Regs) : R.setMany [] [] = R := rfl

variable [model : ExternalModel]

/-- the register file at the first visit of `B1` (`v ↦ 1`, `p` unbound) -/
abbrev Ra : Regs := ((Regs.empty.set 10 1).set 11 0).setMany [1] [1]
/-- the register file at the second visit of `B1` (`v ↦ 0`, `p ↦ 1` — stale) -/
abbrev Rc : Regs := Ra.setMany [1] [0]

/-- The original program returns normally, leaving the machine state untouched:
`B3` reads the stale `p = 1` and takes the `B4` (`ret`) edge. -/
theorem cx_run (yst : EvmState) : Run (model := model) P yst yst .normal := by
  refine Run.normal (eb := b0) rfl ?_
  refine Exec.const ?_
  refine Exec.const ?_
  refine Exec.jump (tb := b1) (args := [1]) rfl rfl rfl ?_
  refine Exec.branchTrue (v := 1) (tb := b2) (args := [1]) rfl (by decide) rfl rfl rfl ?_
  refine Exec.jump (tb := b1) (args := [0]) rfl rfl rfl ?_
  refine Exec.branchFalse (tb := b3) (args := []) rfl rfl rfl rfl ?_
  refine Exec.branchTrue (v := 1) (tb := b4) (args := []) rfl (by decide) rfl rfl rfl ?_
  exact Exec.ret rfl

/-- The optimized program cannot do that: `B3` now reads `v = 0` and is forced
down the `B5` edge, whose `halt` can never produce a `ret` result. -/
theorem cx_no_run (yst : EvmState) : ¬ Run (model := model) Popt yst yst .normal := by
  intro h
  cases h with
  | normal heb hexec =>
    rw [show Popt.main.blocks[Popt.main.entry]? = some b0 from rfl] at heb
    obtain rfl := Option.some.inj heb
    simp only [b0] at hexec
    cases hexec with
    | const h1 =>
    cases h1 with
    | const h2 =>
    cases h2 with
    | jump hb hg hl h3 =>
      simp only [show (Popt.main.blocks[1]? = some b1') from rfl, Option.some.injEq] at hb
      subst hb
      simp only [show (((Regs.empty.set 10 1).set 11 0).getMany [10] = some [(1:U256)])
        from rfl, Option.some.injEq] at hg
      subst hg
      simp only [b1'] at h3
      cases h3 with
      | branchFalse hc hb2 hg2 hl2 h4 =>
        simp only [show (Ra 1 = some (1:U256)) from rfl, Option.some.injEq] at hc
        exact absurd hc (by decide)
      | branchTrue hc hv hb2 hg2 hl2 h4 =>
        simp only [show (Popt.main.blocks[2]? = some b2') from rfl, Option.some.injEq] at hb2
        subst hb2
        simp only [Regs.getMany_nil, Option.some.injEq] at hg2
        subst hg2
        simp only [b2', setMany_nn] at h4
        cases h4 with
        | jump hb3 hg3 hl3 h5 =>
          simp only [show (Popt.main.blocks[1]? = some b1') from rfl, Option.some.injEq] at hb3
          subst hb3
          simp only [show (Ra.getMany [11] = some [(0:U256)]) from rfl, Option.some.injEq] at hg3
          subst hg3
          simp only [b1'] at h5
          cases h5 with
          | branchTrue hc2 hv2 hb4 hg4 hl4 h6 =>
            simp only [show (Rc 1 = some (0:U256)) from rfl, Option.some.injEq] at hc2
            exact hv2 hc2.symm
          | branchFalse hc2 hb4 hg4 hl4 h6 =>
            simp only [show (Popt.main.blocks[3]? = some b3') from rfl, Option.some.injEq] at hb4
            subst hb4
            simp only [Regs.getMany_nil, Option.some.injEq] at hg4
            subst hg4
            simp only [b3', setMany_nn] at h6
            cases h6 with
            | branchTrue hc3 hv3 hb5 hg5 hl5 h7 =>
              simp only [show (Rc 1 = some (0:U256)) from rfl, Option.some.injEq] at hc3
              exact hv3 hc3.symm
            | branchFalse hc3 hb5 hg5 hl5 h7 =>
              simp only [show (Popt.main.blocks[5]? = some b5) from rfl, Option.some.injEq] at hb5
              subst hb5
              simp only [Regs.getMany_nil, Option.some.injEq] at hg5
              subst hg5
              simp only [b5, setMany_nn] at h7
              cases h7

/-- **`optimizeProg_sound` is false.** The pass pipeline does not preserve
executions of `wfCheck`-clean SSA programs: `P` is well-formed and runs to
`.normal` with the state unchanged, but its optimized form has no such run.

The missing side condition is SSA dominance — see this module's header. -/
theorem optimizeProg_sound_false :
    ¬ ∀ (P : Prog) (yst0 yst' : EvmState) (o : Outcome), P.wfCheck = true →
        Run (model := model) P yst0 yst' o →
        Run (model := model) (optimizeProg P) yst0 yst' o := by
  intro hsound
  have := hsound P YulSemantics.EVM.EvmState.init YulSemantics.EVM.EvmState.init .normal hwf
    (cx_run _)
  rw [hopt] at this
  exact cx_no_run _ this

end Counterexample

/-! ## Per-pass soundness

What remains. Passes 2 and 4 are stated as they stand (they need no dominance
hypothesis); passes 1 and 3 are *not* stated as unconditional lemmas, because
the counterexample above refutes exactly that reading of pass 1 — they need the
dominance side condition described in the module header, which `Prog.wfCheck`
does not provide and which this module deliberately does not invent a definition
for. -/

variable [model : ExternalModel]

/-- **Pass 2 (constant folding) soundness.**

`sorry`: needs the forward-walk invariant "for every `(d, v)` in the folder's
`consts` map, the register file maps `d` to `v` or leaves it unbound". That
invariant is dominance-free — it rests only on single assignment (`allDefs.Nodup`
from `wfCheck`), which makes the `const d v` instruction the *unique* binder of
`d`, so any binding of `d` in any reachable state is `v`. Its proof needs a
`Nodup`-based unique-definition-site lemma for `Func.allDefs` (the list plumbing
is the bulk of the work), after which each folded instruction is discharged by
`Passes.evalPure_transport` and each folded `branch` by inversion of
`Exec.branchTrue`/`branchFalse` on a known-constant condition. -/
theorem constFold_sound {P : Prog} {f : Func} {args : List U256} {st : EvmState} {res : FRes}
    {eb eb' : Block} (hwf : f.wfCheck P.funcs.size = true)
    (heb : f.blocks[f.entry]? = some eb)
    (heb' : (Passes.constFold f).blocks[f.entry]? = some eb')
    (hexec : Exec (model := model) P f (Regs.empty.setMany f.params args) st
      ⟨eb.instrs, eb.term⟩ res) :
    Exec (model := model) P (Passes.constFold f) (Regs.empty.setMany f.params args) st
      ⟨eb'.instrs, eb'.term⟩ res := by
  sorry

/-- **Pass 4 (dead value elimination) soundness.**

`sorry`: the shape of the argument is a simulation whose invariant is
"`R` (original) and `R'` (optimized) agree on every *live* value", stepped with
the frame lemma `exec_congr`; the deleted instructions are exactly those whose
destinations no value read anywhere depends on, so the invariant is preserved.
What is missing is the liveness side: `Passes.liveSet` is a fixed point computed
with fuel, and the proof needs (i) that the returned set is `liveStep`-closed
(the fuel loop exits only on a size fixpoint, and `liveStep` is monotone), and
(ii) that closure implies "every value read by a kept instruction, terminator, or
live target parameter is in the set". No dominance hypothesis is needed. -/
theorem dve_sound {P : Prog} {f : Func} {args : List U256} {st : EvmState} {res : FRes}
    {eb eb' : Block} (hwf : f.wfCheck P.funcs.size = true)
    (heb : f.blocks[f.entry]? = some eb)
    (heb' : (Passes.dve f).blocks[f.entry]? = some eb')
    (hexec : Exec (model := model) P f (Regs.empty.setMany f.params args) st
      ⟨eb.instrs, eb.term⟩ res) :
    Exec (model := model) P (Passes.dve f) (Regs.empty.setMany f.params args) st
      ⟨eb'.instrs, eb'.term⟩ res := by
  sorry

/-- **The statement of `SsaCfg.optimizeProg_sound`, reproduced verbatim.**

⚠ **This theorem is FALSE and must not be closed.** It is refuted by
`Counterexample.optimizeProg_sound_false` above (a `wfCheck`-clean program, a
`Run` derivation for it, and a proof that the optimized program has no such
run). It is kept here only so that the repair can be tracked against the
statement `Correctness.lean` currently `sorry`s. Fix the *statement* first — see
the module header: either `Prog.wfCheck` gains a dominance check, or this lemma
(and `compileViaSsa_correct`, which consumes it) gains a dominance hypothesis
discharged for `ofBlock`'s output. -/
theorem optimizeProg_sound' {P : Prog} {yst0 yst' : EvmState} {o : Outcome}
    (hwf : P.wfCheck = true)
    (hrun : Run (model := model) P yst0 yst' o) :
    Run (model := model) (optimizeProg P) yst0 yst' o := by
  sorry

end YulEvmCompiler.SsaCfg
