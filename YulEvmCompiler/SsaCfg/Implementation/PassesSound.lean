import YulEvmCompiler.SsaCfg.Implementation.Passes
import YulEvmCompiler.SsaCfg.Spec.Sem
import YulEvmCompiler.SsaCfg.Implementation.ToAsm
import YulSemantics.Dialect.EVM
/-!
# YulEvmCompiler.SsaCfg.Implementation.PassesSound

Soundness metatheory for the `yul-ssa-cfg` optimization passes
(`SsaCfg/Passes.lean`), i.e. the material behind the `sorry`'d
`SsaCfg.optimizeProg_sound` of `SsaCfg/Correctness.lean`.

## Why `optimizeProg_sound` carries a dominance hypothesis

`wfCheck` alone does **not** make the pipeline sound. The statement

    P.wfCheck = true → Run P yst0 yst' o → Run (optimizeProg P) yst0 yst' o

is **refuted** in § `Counterexample`
(`optimizeProg_sound_false_without_dom`) — fully machine-checked, no `sorry`, no
`native_decide`, no axioms beyond Lean's own. That refutation is what motivated
`ToAsm.Func.domCheck`/`Prog.domCheck` and the `hdom` hypothesis the statement
now carries; the counterexample is kept here as the standing witness that the
hypothesis cannot be dropped.

The failure is not a coding mistake in a pass. Pass 1 (trivial block-parameter
elimination) and pass 3 (local CSE) are sound only for programs respecting **SSA
dominance**, and `Prog.wfCheck` deliberately does not check it — `Ir.lean` argued
that an undominated use is harmless because "the semantics gets stuck on an
unbound `ValId` read". It is not: in this semantics **registers persist across
blocks** and block parameters are *re-bound on every visit*, so an undominated
use is not stuck — it reads a **stale** binding from an earlier visit. Rerouting
such a use (pass 1 substitutes the parameter `p` by the value `v` all in-edges
pass; pass 3 substitutes a repeated computation by an earlier `ValId`) makes it
read the *current* value instead. `Counterexample.P` is exactly that shape:
block 3 reads block 2's parameter `p` on a path that does not go through block 2.

Two things the defensive gate does *not* do, both recorded in § `Counterexample`:

* it checks the *output*, so it cannot see that the *input* violated dominance —
  `hdomPopt` shows the rewritten program passes `wfCheck && domCheck` happily
  (`hdomP` shows the input does not);
* consequently no downstream check can substitute for `hdom`.

Passes 2 (constant folding) and 4 (dead value elimination) need no dominance:
`constFold` only rewrites an op into the constant its operands' `const`
definitions already force (single assignment suffices), and `dve` only deletes
definitions nothing reads.

## What is proved here

* `Regs` plumbing: `setMany_cons`, `getMany_congr`, `set_congr`, `setMany_congr`.
* The **frame lemma** `exec_congr`: `Exec` only reads registers named in the
  current fragment or somewhere in the enclosing function, so two register files
  agreeing there give the same execution. This is the reusable "Regs agreement"
  lemma passes 1, 3 and 4 all need.
* **The dominance check, unpacked** (§ `ToAsm`) — the bridge from the decidable
  `domCheck` to the fact the passes actually use:
  * `mem_insertSorted` / `mem_unionS` / `mem_diffS` / `mem_blockUses` /
    `mem_blockDefs` / `mem_lout` — membership in the sorted-set helpers;
  * `liveInSets_fix` — `liveInSets` returns a genuine fixed point of the backward
    liveness step (the fuel loop exits only on `next == cur`);
  * `liveStep_get_eq` / `liveIn_eq` — the fixed-point equation at one block;
  * `liveIn_of_uses`, `liveIn_of_succ` — the two propagation steps: what a block
    reads and does not define is live in, and liveness crosses edges backwards;
  * `domCheck_entry` — under the check, `liveIn(entry) ⊆ f.params`. Chaining the
    two propagation lemmas along a definition-free path and hitting this is
    precisely "no use is undominated";
  * `liveStep_mono` and `liveInSets_least` — `liveInSets` is the *least* fixed
    point, the engine for the dominance-*preservation* obligations;
  * `LiveAgree` and `liveAgree_entry` — the passes' liveness-indexed simulation
    invariant and its (proved) base case at a function's entry.
* The **purity leaves**, transported from the pinned dialect's own
  `effects_sound_withExternal`:
  * `builtin_of_pure` — a pure op is never an open-world (`call`/`create`/`gas`)
    op, so its combined relation *is* the executable `stepOp` graph;
  * `pure_state_eq` — a pure op leaves the machine state alone;
  * `pure_rets_eq` — **CSE leaf**: equal `(op, args)` ⇒ equal results, in any
    two states;
  * `evalPure_stepOp` / `evalPure_transport` — **constant-folding leaf**: what
    the folder computed on `EvmState.init` is what the op returns in *any* state.
* The **pipeline gate**, factored through `optimizeCandidate` so that the
  pipeline's shape is tracked in exactly one place (`optimizeProg_candidate`,
  definitional — it already survived one shape change, the addition of
  `Passes.inlineProg` in front): `optimizeProg_of_gate_true`,
  `optimizeProg_of_gate_false`, `optimizeProg_sound_of_fallback`, and the
  corresponding branch inside `optimizeProg_sound'` — when the candidate fails
  `wfCheck && domCheck`, `optimizeProg` returns the original and soundness is
  reflexivity.
* `runOnce_dom` — dominance preservation for a pipeline round, by composition of
  the four per-pass obligations, and **`constFold_dom`** — the first of those four,
  proved via `ToAsm.domCheck_of_shrinking` and pass 2's structural specification
  (`Passes.constFold_spec`: every output block is a `CFRel`-rewrite of the input
  block at the same index; `cfTerm_cases`, `cfInstrStep_cons`, `cfInstr_fold`,
  `cfBlockStep_spec`, `cfBlock_fold`).
* Both **`forIn` bridges**: `Id.forIn_eq_foldl` for pure-`yield` loops and
  `Id.forIn_eq_loopWith` for **early-return** loops (with `loopWith` as the pure
  model, `loopWith_yield` relating the two, and the `MProd (Option ρ) σ`
  early-return protocol recorded as a worked example). The second unblocks
  `findTrivialParam`, `inlineOnce` and `inlineFunc`, which all `return` early.
* **`ToAsm.liveInSets_isSome` — the liveness fixed point always converges.**
  `Func.domCheck` is `false` by definition when `liveInSets` exhausts its fuel,
  so this is a prerequisite of *every* dominance-preservation statement. Proved
  by the Kleene argument: the sorted-set helpers produce `Pairwise (· < ·)` lists
  (`insertSorted_pairwise`, `unionS_pairwise`, `diffS_pairwise`), such a list is
  determined by its elements (`pairwise_lt_ext`), every iterate stays inside the
  finite `liveUniverse` (`liveStep_liveUniverse`), so `liveMeasure` — the sum of
  the live-set sizes — strictly increases at each non-exiting round
  (`measure_lt`) while staying bounded (`measure_le`, `liveUniverse_length_le`).
  The fuel `blocks.size * (total + 1) + 2` therefore always suffices
  (`go_isSome`).
* **`ToAsm.domCheck_of_shrinking`** — a reusable dominance-preservation
  criterion, built on the two above: a rewrite that keeps `params`/`entry`, only
  shrinks what each block reads, only keeps what each block defines, and only
  drops outgoing edges, preserves `Func.domCheck`. This is `constFold_dom`
  modulo that pass's structural specification.
* **Pass 4's structural specification** (`Passes.dve_blocks_get` and friends):
  `dve` is the one pass written without an `Id.run` loop, so its output is
  directly readable — `dveBlock_uses_sub` (uses only shrink),
  `dveBlock_defs_sub` / `dveBlock_defs_of_live` (definitions only shrink, and a
  live definition is always kept), `dveBlock_edge_target` (edge targets are
  untouched). This is the complete structural half of both `dve_sound` and
  `dve_dom`.
* The **counterexample**, end to end: `P.wfCheck = true`,
  `ToAsm.Prog.domCheck P = false`, `optimizeProg P = Popt` — the *whole*
  optimizer evaluated **inside the kernel**: `Passes.inlineProg` (proved to be
  the identity here, `hinline`: `P` has no `call`, so `siteCounts` is empty,
  `inlineOnce` finds nothing and `pruneFuncs` keeps everything), then three
  rounds of the four-pass pipeline, then the gate — plus
  `Run P yst yst .normal` and `¬ Run Popt yst yst .normal`.

## The remaining frontier

Two `sorry`s remain, each documented at its declaration:

* pass 3: `cse_sound`;
* the gate-accepted branch of `optimizeProg_sound'`.

Two kinds of obligation remain, and it is worth separating them.

**(a) Loop inversion.** Every pass except `dve` is written as an `Id.run` loop.
The generic tool now exists — `Id.forIn_eq_foldl` / `Id.forIn_array_eq_foldl`,
with the recipe recorded at their declaration (`dsimp only` first, state the step
function over `MProd`, pass `h` as a tactic block, `grind` for the
`pure`-inside-a-`match` branches). It is applied end to end for `constFold`
(`constFold_blocks_eq`), `inlineOnce`, `inlineFunc`, and `pruneFuncs`; `cse`
and `elimTrivialParams` still need the same treatment.

**(b) DVE execution alignment.** Both fixed-point facts are now proved:
`ToAsm.liveInSets_isSome` and `Passes.liveSet_closed`.  Closure has also been
unpacked into `dveBlock_uses_live`, including the `wfCheck`-backed positional
edge argument case.  What remains for `dve_sound` is the runtime counterpart:
filter target parameters, edge ids, and the values returned by `Regs.getMany`
with the same mask, then carry live-register agreement across `setMany`.

The semantic ingredients that all of these feed into — the frame lemma, the
purity leaves, the liveness fixed point with its propagation and
least-fixed-point lemmas, and the `LiveAgree` base case — are proved here.
-/

namespace YulEvmCompiler.SsaCfg

open YulSemantics.EVM (U256 EvmState Op builtinWithExternal stepOp ExternalCalls
  ExternalCreates)
open YulSemantics (Outcome)

/-! ## Call-depth-indexed execution

`ExecN P n f R st rest res` is the ordinary `Exec` judgment equipped with an
upper bound on the dynamic user-call depth.  Instructions and intra-function
control flow preserve the bound.  At a returning call, the callee runs at
bound `n` while the caller continuation (and the complete call) runs at bound
`n + 1`; a halting call only has the callee premise.  Leaf rules are available
at every bound, which makes the judgment monotone.

This separate inductive is needed below because an `Exec` proof lives in
`Prop`, so its call depth cannot be computed by eliminating it into `Nat`.
-/

inductive ExecN (P : Prog) [model : ExternalModel] :
    Nat → Func → Regs → EvmState → Rest → FRes → Prop
  | const {n : Nat} {f : Func} {R : Regs} {st : EvmState} {d : ValId} {v : U256}
      {is : List Instr} {t : Term} {res : FRes} :
      ExecN P n f (R.set d v) st ⟨is, t⟩ res →
      ExecN P n f R st ⟨.const d v :: is, t⟩ res
  | op {n : Nat} {f : Func} {R : Regs} {st st' : EvmState} {ds : List ValId}
      {yop : Op} {as : List ValId} {args rets : List U256} {is : List Instr}
      {t : Term} {res : FRes} :
      R.getMany as = some args →
      builtinWithExternal model.calls model.creates yop args st (.ok rets st') →
      ds.length = rets.length →
      ExecN P n f (R.setMany ds rets) st' ⟨is, t⟩ res →
      ExecN P n f R st ⟨.op ds yop as :: is, t⟩ res
  | opHalt {n : Nat} {f : Func} {R : Regs} {st st' : EvmState}
      {ds : List ValId} {yop : Op} {as : List ValId} {args : List U256}
      {is : List Instr} {t : Term} :
      R.getMany as = some args →
      builtinWithExternal model.calls model.creates yop args st (.halt st') →
      ExecN P n f R st ⟨.op ds yop as :: is, t⟩ (.halt st')
  | call {n : Nat} {f g : Func} {R : Regs} {st st' : EvmState}
      {ds as : List ValId} {fid : FuncId} {args rvals : List U256} {eb : Block}
      {is : List Instr} {t : Term} {res : FRes} :
      P.funcs[fid]? = some g →
      R.getMany as = some args →
      g.params.length = args.length →
      g.blocks[g.entry]? = some eb →
      ExecN P n g (Regs.empty.setMany g.params args) st
        ⟨eb.instrs, eb.term⟩ (.ret rvals st') →
      ds.length = rvals.length →
      ExecN P (n + 1) f (R.setMany ds rvals) st' ⟨is, t⟩ res →
      ExecN P (n + 1) f R st ⟨.call ds fid as :: is, t⟩ res
  | callHalt {n : Nat} {f g : Func} {R : Regs} {st st' : EvmState}
      {ds as : List ValId} {fid : FuncId} {args : List U256} {eb : Block}
      {is : List Instr} {t : Term} :
      P.funcs[fid]? = some g →
      R.getMany as = some args →
      g.params.length = args.length →
      g.blocks[g.entry]? = some eb →
      ExecN P n g (Regs.empty.setMany g.params args) st
        ⟨eb.instrs, eb.term⟩ (.halt st') →
      ExecN P (n + 1) f R st ⟨.call ds fid as :: is, t⟩ (.halt st')
  | jump {n : Nat} {f : Func} {R : Regs} {st : EvmState} {e : Edge}
      {tb : Block} {args : List U256} {res : FRes} :
      f.blocks[e.target]? = some tb →
      R.getMany e.args = some args →
      tb.params.length = args.length →
      ExecN P n f (R.setMany tb.params args) st ⟨tb.instrs, tb.term⟩ res →
      ExecN P n f R st ⟨[], .jump e⟩ res
  | branchTrue {n : Nat} {f : Func} {R : Regs} {st : EvmState}
      {c : ValId} {v : U256} {et ef : Edge} {tb : Block} {args : List U256}
      {res : FRes} :
      R c = some v → v ≠ 0 →
      f.blocks[et.target]? = some tb →
      R.getMany et.args = some args →
      tb.params.length = args.length →
      ExecN P n f (R.setMany tb.params args) st ⟨tb.instrs, tb.term⟩ res →
      ExecN P n f R st ⟨[], .branch c et ef⟩ res
  | branchFalse {n : Nat} {f : Func} {R : Regs} {st : EvmState}
      {c : ValId} {et ef : Edge} {tb : Block} {args : List U256} {res : FRes} :
      R c = some 0 →
      f.blocks[ef.target]? = some tb →
      R.getMany ef.args = some args →
      tb.params.length = args.length →
      ExecN P n f (R.setMany tb.params args) st ⟨tb.instrs, tb.term⟩ res →
      ExecN P n f R st ⟨[], .branch c et ef⟩ res
  | ret {n : Nat} {f : Func} {R : Regs} {st : EvmState} {xs : List ValId}
      {vals : List U256} :
      R.getMany xs = some vals →
      ExecN P n f R st ⟨[], .ret xs⟩ (.ret vals st)
  | halt {n : Nat} {f : Func} {R : Regs} {st st' : EvmState} {yop : Op}
      {as : List ValId} {args : List U256} :
      R.getMany as = some args →
      builtinWithExternal model.calls model.creates yop args st (.halt st') →
      ExecN P n f R st ⟨[], .halt yop as⟩ (.halt st')

/-- A call-depth bound can always be enlarged. -/
theorem ExecN.mono {P : Prog} {n m : Nat} {f : Func} {R : Regs}
    {st : EvmState} {rest : Rest} {res : FRes}
    (h : ExecN (model := model) P n f R st rest res) (hnm : n ≤ m) :
    ExecN (model := model) P m f R st rest res := by
  induction h generalizing m with
  | const htail ih => exact ExecN.const (ih hnm)
  | op hget hop hlen htail ih => exact ExecN.op hget hop hlen (ih hnm)
  | opHalt hget hop => exact ExecN.opHalt hget hop
  | @call n f g R st st' ds as fid args rvals eb is t res
      hfid hget hplen heb hbody hlen htail ihbody ih =>
      have hmpos : 0 < m := lt_of_lt_of_le (Nat.zero_lt_succ n) (by simpa using hnm)
      obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hmpos)
      exact ExecN.call hfid hget hplen heb (ihbody (by omega)) hlen (ih (by omega))
  | @callHalt n f g R st st' ds as fid args eb is t
      hfid hget hplen heb hbody ihbody =>
      have hmpos : 0 < m := lt_of_lt_of_le (Nat.zero_lt_succ n) (by simpa using hnm)
      obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hmpos)
      exact ExecN.callHalt hfid hget hplen heb (ihbody (by omega))
  | jump htb hget hplen htail ih => exact ExecN.jump htb hget hplen (ih hnm)
  | branchTrue hc hv htb hget hplen htail ih =>
      exact ExecN.branchTrue hc hv htb hget hplen (ih hnm)
  | branchFalse hc htb hget hplen htail ih =>
      exact ExecN.branchFalse hc htb hget hplen (ih hnm)
  | ret hget => exact ExecN.ret hget
  | halt hget hop => exact ExecN.halt hget hop

/-- Forgetting the call-depth index recovers the ordinary semantics. -/
theorem ExecN.toExec {P : Prog} {n : Nat} {f : Func} {R : Regs}
    {st : EvmState} {rest : Rest} {res : FRes}
    (h : ExecN (model := model) P n f R st rest res) :
    Exec (model := model) P f R st rest res := by
  induction h with
  | const htail ih => exact Exec.const ih
  | op hget hop hlen htail ih => exact Exec.op hget hop hlen ih
  | opHalt hget hop => exact Exec.opHalt hget hop
  | call hfid hget hplen heb hbody hlen htail ihbody ih =>
      exact Exec.call hfid hget hplen heb ihbody hlen ih
  | callHalt hfid hget hplen heb hbody ihbody =>
      exact Exec.callHalt hfid hget hplen heb ihbody
  | jump htb hget hplen htail ih => exact Exec.jump htb hget hplen ih
  | branchTrue hc hv htb hget hplen htail ih =>
      exact Exec.branchTrue hc hv htb hget hplen ih
  | branchFalse hc htb hget hplen htail ih =>
      exact Exec.branchFalse hc htb hget hplen ih
  | ret hget => exact Exec.ret hget
  | halt hget hop => exact Exec.halt hget hop

/-- Every terminating execution admits a finite call-depth bound. -/
theorem Exec.toExecN {P : Prog} {f : Func} {R : Regs} {st : EvmState}
    {rest : Rest} {res : FRes} (h : Exec (model := model) P f R st rest res) :
    ∃ n, ExecN (model := model) P n f R st rest res := by
  induction h with
  | const htail ih => obtain ⟨n, hn⟩ := ih; exact ⟨n, ExecN.const hn⟩
  | op hget hop hlen htail ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n, ExecN.op hget hop hlen hn⟩
  | opHalt hget hop => exact ⟨0, ExecN.opHalt hget hop⟩
  | call hfid hget hplen heb hbody hlen htail ihbody ih =>
      obtain ⟨nb, hnb⟩ := ihbody
      obtain ⟨nt, hnt⟩ := ih
      refine ⟨nb + nt + 1, ExecN.call hfid hget hplen heb
        (hnb.mono (by omega)) hlen ?_⟩
      exact hnt.mono (by omega)
  | callHalt hfid hget hplen heb hbody ihbody =>
      obtain ⟨n, hn⟩ := ihbody
      exact ⟨n + 1, ExecN.callHalt hfid hget hplen heb hn⟩
  | jump htb hget hplen htail ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n, ExecN.jump htb hget hplen hn⟩
  | branchTrue hc hv htb hget hplen htail ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n, ExecN.branchTrue hc hv htb hget hplen hn⟩
  | branchFalse hc htb hget hplen htail ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n, ExecN.branchFalse hc htb hget hplen hn⟩
  | ret hget => exact ⟨0, ExecN.ret hget⟩
  | halt hget hop => exact ⟨0, ExecN.halt hget hop⟩

/-! ## `Regs` plumbing -/

namespace Regs

theorem setMany_nil_left (R : Regs) (vs : List U256) : R.setMany [] vs = R := rfl

theorem setMany_nil_right (R : Regs) (xs : List ValId) : R.setMany xs [] = R := by
  cases xs <;> rfl

theorem setMany_cons (R : Regs) (x : ValId) (xs : List ValId) (v : U256) (vs : List U256) :
    R.setMany (x :: xs) (v :: vs) = (R.set x v).setMany xs vs := rfl

/-- Parallel binding leaves an id outside the destination list untouched. -/
theorem setMany_of_not_mem (R : Regs) {d : ValId} (xs : List ValId) (vs : List U256)
    (hd : d ∉ xs) : (R.setMany xs vs) d = R d := by
  induction xs generalizing R vs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mem_cons, not_or] at hd
    cases vs with
    | nil => rw [setMany_nil_right]
    | cons v vs =>
      rw [setMany_cons, ih (R := R.set x v) (vs := vs) hd.2]
      exact set_other R v hd.1

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

/-- Read a use list after substitution when the two register files agree on
the original uses modulo that substitution. -/
theorem getMany_substVs {σ : Passes.Subst} {R R' : Regs}
    {xs : List ValId} {vs : List U256}
    (hagree : ∀ x ∈ xs, R x = R' (Passes.substV σ x))
    (hget : R.getMany xs = some vs) :
    R'.getMany (Passes.substVs σ xs) = some vs := by
  induction xs generalizing vs with
  | nil => simpa [Passes.substVs] using hget
  | cons x xs ih =>
      rw [getMany_cons] at hget
      cases hx : R x with
      | none => simp [hx] at hget
      | some v =>
          cases htail : R.getMany xs with
          | none => simp [hx, htail] at hget
          | some vals =>
              simp only [hx, htail, Option.bind_some, Option.map_some,
                Option.some.injEq] at hget
              subst vs
              have hx' : R' (Passes.substV σ x) = some v := by
                rw [← hagree x (by simp), hx]
              have ht' := ih (fun y hy => hagree y (by simp [hy])) htail
              simpa [Passes.substVs, getMany_cons, hx'] using ht'

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

/-! ## Single assignment

`wfCheck` gives `Func.allDefs.Nodup`; these lemmas turn that into the form the
value-level passes need — a value has exactly one definition site, so any
binding of it in any execution comes from *that* instruction. The argument is by
counting occurrences in `allDefs`, which avoids index arithmetic through the
nested `flatMap`. -/

theorem one_le_count_flatMap {α β : Type} [DecidableEq β] {l : List α} {g : α → List β}
    {x : α} {d : β} (hx : x ∈ l) (hd : d ∈ g x) : 1 ≤ (l.flatMap g).count d :=
  List.count_pos_iff.mpr (List.mem_flatMap.mpr ⟨x, hx, hd⟩)

theorem count_le_count_flatMap {α β : Type} [DecidableEq β] {l : List α} {g : α → List β}
    {x : α} {d : β} (hx : x ∈ l) : (g x).count d ≤ (l.flatMap g).count d := by
  induction l with
  | nil => simp at hx
  | cons a rest ih =>
    rw [List.flatMap_cons, List.count_append]
    rcases List.mem_cons.mp hx with rfl | hx'
    · omega
    · have := ih hx'; omega

theorem two_le_count_flatMap {α β : Type} [DecidableEq β] {l : List α} {g : α → List β}
    {x y : α} {d : β} (hx : x ∈ l) (hy : y ∈ l) (hne : x ≠ y)
    (hdx : d ∈ g x) (hdy : d ∈ g y) : 2 ≤ (l.flatMap g).count d := by
  induction l with
  | nil => simp at hx
  | cons a rest ih =>
    rw [List.flatMap_cons, List.count_append]
    rcases List.mem_cons.mp hx with rfl | hx'
    · have hy' : y ∈ rest := by
        rcases List.mem_cons.mp hy with rfl | h
        · exact absurd rfl hne
        · exact h
      have h1 : 1 ≤ (g x).count d := List.count_pos_iff.mpr hdx
      have h2 : 1 ≤ (rest.flatMap g).count d := one_le_count_flatMap hy' hdy
      omega
    · rcases List.mem_cons.mp hy with rfl | hy'
      · have h1 : 1 ≤ (g y).count d := List.count_pos_iff.mpr hdy
        have h2 : 1 ≤ (rest.flatMap g).count d := one_le_count_flatMap hx' hdx
        omega
      · have := ih hx' hy'
        omega

/-! ### Single assignment: one definition site per value -/

/-- The per-block contribution to `Func.allDefs`. -/
abbrev blockAllDefs (b : Block) : List ValId := b.params ++ b.instrs.flatMap Instr.defs

theorem allDefs_eq (f : Func) :
    f.allDefs = f.params ++ f.blocks.toList.flatMap blockAllDefs := rfl

theorem two_le_count_allDefs {f : Func} {d : ValId}
    (h2 : 2 ≤ (f.blocks.toList.flatMap blockAllDefs).count d) : ¬ f.allDefs.Nodup := by
  intro hnd
  have hle := List.nodup_iff_count_le_one.mp hnd d
  rw [allDefs_eq, List.count_append] at hle
  omega

/-- **Single assignment, instruction form**: two instructions of a well-formed
function that define the same value are the same instruction. -/
theorem instr_def_unique {f : Func} (h : f.allDefs.Nodup)
    {b1 b2 : Block} (hb1 : b1 ∈ f.blocks.toList) (hb2 : b2 ∈ f.blocks.toList)
    {x1 x2 : Instr} (hx1 : x1 ∈ b1.instrs) (hx2 : x2 ∈ b2.instrs)
    {d : ValId} (hd1 : d ∈ x1.defs) (hd2 : d ∈ x2.defs) : x1 = x2 := by
  by_contra hne
  refine two_le_count_allDefs (f := f) (d := d) ?_ h
  by_cases hb : b1 = b2
  · subst hb
    have h2 : 2 ≤ (b1.instrs.flatMap Instr.defs).count d :=
      two_le_count_flatMap hx1 hx2 hne hd1 hd2
    have hle : (blockAllDefs b1).count d ≤ (f.blocks.toList.flatMap blockAllDefs).count d :=
      count_le_count_flatMap hb1
    rw [show blockAllDefs b1 = b1.params ++ b1.instrs.flatMap Instr.defs from rfl,
      List.count_append] at hle
    omega
  · refine two_le_count_flatMap hb1 hb2 hb ?_ ?_ <;>
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, by assumption, by assumption⟩)

/-- **Single assignment, parameter form**: a block parameter is never also an
instruction destination. -/
theorem param_not_instr_def {f : Func} (h : f.allDefs.Nodup)
    {b1 b2 : Block} (hb1 : b1 ∈ f.blocks.toList) (hb2 : b2 ∈ f.blocks.toList)
    {x : Instr} (hx : x ∈ b2.instrs) {d : ValId} (hp : d ∈ b1.params) (hd : d ∈ x.defs) :
    False := by
  refine two_le_count_allDefs (f := f) (d := d) ?_ h
  by_cases hb : b1 = b2
  · subst hb
    have h1 : 1 ≤ b1.params.count d := List.count_pos_iff.mpr hp
    have h2 : 1 ≤ (b1.instrs.flatMap Instr.defs).count d := one_le_count_flatMap hx hd
    have hle : (blockAllDefs b1).count d ≤ (f.blocks.toList.flatMap blockAllDefs).count d :=
      count_le_count_flatMap hb1
    rw [show blockAllDefs b1 = b1.params ++ b1.instrs.flatMap Instr.defs from rfl,
      List.count_append] at hle
    omega
  · exact two_le_count_flatMap hb1 hb2 hb (List.mem_append_left _ hp)
      (List.mem_append_right _ (List.mem_flatMap.mpr ⟨x, hx, hd⟩))

/-- **Single assignment, function-parameter form**. -/
theorem funcParam_not_instr_def {f : Func} (h : f.allDefs.Nodup)
    {b : Block} (hb : b ∈ f.blocks.toList) {x : Instr} (hx : x ∈ b.instrs)
    {d : ValId} (hp : d ∈ f.params) (hd : d ∈ x.defs) : False := by
  have hle := List.nodup_iff_count_le_one.mp h d
  rw [allDefs_eq, List.count_append] at hle
  have h1 : 1 ≤ f.params.count d := List.count_pos_iff.mpr hp
  have h2 : 1 ≤ (f.blocks.toList.flatMap blockAllDefs).count d :=
    one_le_count_flatMap hb (List.mem_append_right _ (List.mem_flatMap.mpr ⟨x, hx, hd⟩))
  omega

/-! ## Dominance: the backward-liveness fixed point

`ToAsm.Func.domCheck` decides SSA dominance as "nothing but the function's
parameters is live into the entry block" (backward liveness, `ToAsm.liveInSets`).
This section unpacks that check into the three facts a pass proof needs:

* `ToAsm.liveIn_of_uses` — a value a block reads and does not define is live
  into it;
* `ToAsm.liveIn_of_succ` — liveness propagates backwards along edges;
* `ToAsm.domCheck_entry` — under the check, `liveIn(entry) ⊆ f.params`.

Chaining the first two along a definition-free path and hitting the third is
exactly the argument "a non-dominated use is impossible"; `liveAgree_entry`
below is the corresponding base case for the passes' simulation invariant. -/

namespace ToAsm

/-! ### Sorted-set membership -/

theorem mem_insertSorted {x v : ValId} {l : List ValId} :
    x ∈ insertSorted v l ↔ x = v ∨ x ∈ l := by
  induction l with
  | nil => simp [insertSorted]
  | cons w rest ih =>
    by_cases h1 : v < w
    · simp [insertSorted, h1]
    · by_cases h2 : v = w
      · subst h2; simp [insertSorted]
      · simp only [insertSorted, h1, h2, if_false, List.mem_cons, ih]
        constructor
        · rintro (rfl | rfl | h) <;> simp_all
        · rintro (rfl | rfl | h) <;> simp_all

theorem mem_unionS {x : ValId} {xs ys : List ValId} :
    x ∈ unionS xs ys ↔ x ∈ xs ∨ x ∈ ys := by
  unfold unionS
  induction xs generalizing ys with
  | nil => simp
  | cons a as ih =>
    simp only [List.foldl_cons, ih, mem_insertSorted, List.mem_cons]
    tauto

theorem mem_diffS {x : ValId} {xs ys : List ValId} :
    x ∈ diffS xs ys ↔ x ∈ xs ∧ x ∉ ys := by
  simp [diffS, List.mem_filter]

theorem mem_blockUses {x : ValId} {b : Block} :
    x ∈ blockUses b ↔ x ∈ b.instrs.flatMap Instr.uses ∨ x ∈ b.term.uses := by
  simp [blockUses, mem_unionS]

theorem mem_blockDefs {x : ValId} {b : Block} :
    x ∈ blockDefs b ↔ x ∈ b.params ∨ x ∈ b.instrs.flatMap Instr.defs := by
  simp [blockDefs, mem_unionS, List.mem_append]

/-! ### The liveness fixed point -/

theorem liveInSets_go_fix {f : Func} {fuel : Nat} {cur li : Array (List ValId)}
    (h : liveInSets.go f fuel cur = some li) : liveStep f li = li := by
  induction fuel generalizing cur with
  | zero => simp [liveInSets.go] at h
  | succ n ih =>
    rw [liveInSets.go] at h
    split at h
    · rename_i heq
      obtain rfl := Option.some.inj h
      exact (beq_iff_eq).mp heq
    · exact ih h

/-- `liveInSets` returns a genuine fixed point of the backward liveness step. -/
theorem liveInSets_fix {f : Func} {li : Array (List ValId)} (h : liveInSets f = some li) :
    liveStep f li = li := liveInSets_go_fix (by unfold liveInSets at h; exact h)

theorem liveStep_size {f : Func} {li : Array (List ValId)} :
    (liveStep f li).size = f.blocks.size := by simp [liveStep]

theorem liveInSets_size {f : Func} {li : Array (List ValId)} (h : liveInSets f = some li) :
    li.size = f.blocks.size := by
  rw [← liveInSets_fix h]; exact liveStep_size

/-- One liveness step read off at one block. -/
theorem liveStep_get_eq {f : Func} {A : Array (List ValId)} {i : Nat} {b : Block}
    (hb : f.blocks[i]? = some b) :
    (liveStep f A)[i]?.getD [] =
      diffS (unionS (blockUses b)
        (b.term.edges.foldl (init := []) fun acc (e : Edge) => unionS (A[e.target]?.getD []) acc))
        (blockDefs b) := by
  have hlt : i < f.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  have hsz : i < (liveStep f A).size := by rw [liveStep_size]; exact hlt
  rw [Array.getElem?_eq_getElem hsz]
  simp only [Option.getD_some, liveStep, Array.getElem_ofFn]
  simp [hb]

theorem liveStep_get_none {f : Func} {A : Array (List ValId)} {i : Nat}
    (hb : f.blocks[i]? = none) : (liveStep f A)[i]?.getD [] = [] := by
  rcases h : (liveStep f A)[i]? with _ | l
  · simp
  · have hlt : i < (liveStep f A).size := (Array.getElem?_eq_some_iff.mp h).1
    have hlt' : i < f.blocks.size := by rw [liveStep_size] at hlt; exact hlt
    exact absurd hb (by simp [Array.getElem?_eq_getElem hlt'])

/-- The fixed-point equation, at one block. -/
theorem liveIn_eq {f : Func} {li : Array (List ValId)} (h : liveInSets f = some li)
    {i : BlockId} {b : Block} (hb : f.blocks[i]? = some b) :
    li[i]?.getD [] =
      diffS (unionS (blockUses b)
        (b.term.edges.foldl (init := []) fun acc (e : Edge) => unionS (li[e.target]?.getD []) acc))
        (blockDefs b) := by
  conv_lhs => rw [← liveInSets_fix h]
  exact liveStep_get_eq hb

/-- Membership in the `liveOut` union over a block's outgoing edges. -/
theorem mem_lout {li : Array (List ValId)} {x : ValId} {edges : List Edge}
    {acc0 : List ValId} :
    x ∈ edges.foldl (fun acc (e : Edge) => unionS (li[e.target]?.getD []) acc) acc0 ↔
      (∃ e ∈ edges, x ∈ li[e.target]?.getD []) ∨ x ∈ acc0 := by
  induction edges generalizing acc0 with
  | nil => simp
  | cons e es ih =>
    simp only [List.foldl_cons, ih, mem_unionS, List.mem_cons]
    constructor
    · rintro (⟨e', he', hx'⟩ | hx | hacc)
      · exact Or.inl ⟨e', Or.inr he', hx'⟩
      · exact Or.inl ⟨e, Or.inl rfl, hx⟩
      · exact Or.inr hacc
    · rintro (⟨e', (rfl | he'), hx'⟩ | hacc)
      · exact Or.inr (Or.inl hx')
      · exact Or.inl ⟨e', he', hx'⟩
      · exact Or.inr (Or.inr hacc)

/-- A value a block reads but does not define is live into that block. -/
theorem liveIn_of_uses {f : Func} {li : Array (List ValId)} (h : liveInSets f = some li)
    {i : BlockId} {b : Block} (hb : f.blocks[i]? = some b) {x : ValId}
    (hu : x ∈ blockUses b) (hd : x ∉ blockDefs b) : x ∈ li[i]?.getD [] := by
  rw [liveIn_eq h hb, mem_diffS]
  exact ⟨mem_unionS.mpr (Or.inl hu), hd⟩

/-- A value live into a successor and not defined by the block is live into the block. -/
theorem liveIn_of_succ {f : Func} {li : Array (List ValId)} (h : liveInSets f = some li)
    {i : BlockId} {b : Block} (hb : f.blocks[i]? = some b) {e : Edge} {x : ValId}
    (he : e ∈ b.term.edges) (hx : x ∈ li[e.target]?.getD []) (hd : x ∉ blockDefs b) :
    x ∈ li[i]?.getD [] := by
  rw [liveIn_eq h hb, mem_diffS]
  exact ⟨mem_unionS.mpr (Or.inr (mem_lout.mpr (Or.inl ⟨e, he, hx⟩))), hd⟩

/-- **The content of the dominance check**: nothing but the function's own
parameters is live into the entry block. Together with `liveIn_of_uses` and
`liveIn_of_succ` this is the whole of "every use is dominated by its
definition": a use whose definition does not dominate it induces a
definition-free path back to the entry, along which backward liveness carries
the value into `liveIn(entry)`. -/
theorem domCheck_entry {f : Func} {li : Array (List ValId)} (hli : liveInSets f = some li)
    (hdom : Func.domCheck f = true) {x : ValId} (hx : x ∈ li[f.entry]?.getD []) :
    x ∈ f.params := by
  unfold Func.domCheck at hdom
  rw [hli] at hdom
  simp only [decide_eq_true_eq] at hdom
  by_contra hp
  have : x ∈ diffS (li[f.entry]?.getD []) f.params := mem_diffS.mpr ⟨hx, hp⟩
  rw [hdom] at this
  exact absurd this (by simp)

theorem Prog.domCheck_main {P : Prog} (h : Prog.domCheck P = true) :
    Func.domCheck P.main = true := ((Bool.and_eq_true _ _).mp h).1

theorem Prog.domCheck_funcs {P : Prog} (h : Prog.domCheck P = true) {g : Func}
    (hg : g ∈ P.funcs) : Func.domCheck g = true := by
  have hall := ((Bool.and_eq_true _ _).mp h).2
  rw [Array.all_eq_true] at hall
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hg
  exact hall i hi

/-! ### Least fixed point (for dominance *preservation*) -/

/-- Pointwise inclusion of liveness maps (total: an out-of-range read is `[]`). -/
def Sub (A B : Array (List ValId)) : Prop :=
  ∀ (i : Nat) (x : ValId), x ∈ A[i]?.getD [] → x ∈ B[i]?.getD []

theorem Sub.refl (A : Array (List ValId)) : Sub A A := fun _ _ h => h

theorem sub_replicate {n : Nat} {B : Array (List ValId)} :
    Sub (Array.replicate n []) B := by
  intro i x hx
  rcases h : (Array.replicate n ([] : List ValId))[i]? with _ | l
  · rw [h] at hx; simp at hx
  · rw [h] at hx
    have hl : l = [] := by
      obtain ⟨hlt, hget⟩ := Array.getElem?_eq_some_iff.mp h
      simpa using hget.symm
    rw [hl] at hx; simp at hx

/-- The backward liveness step is monotone. -/
theorem liveStep_mono {f : Func} {A B : Array (List ValId)} (h : Sub A B) :
    Sub (liveStep f A) (liveStep f B) := by
  intro i x hx
  rcases hb : f.blocks[i]? with _ | b
  · rw [liveStep_get_none hb] at hx; simp at hx
  · rw [liveStep_get_eq hb] at hx ⊢
    rw [mem_diffS] at hx ⊢
    refine ⟨?_, hx.2⟩
    rcases mem_unionS.mp hx.1 with hu | hl
    · exact mem_unionS.mpr (Or.inl hu)
    · rcases mem_lout.mp hl with ⟨e, he, hxe⟩ | hnil
      · exact mem_unionS.mpr (Or.inr (mem_lout.mpr (Or.inl ⟨e, he, h _ _ hxe⟩)))
      · simp at hnil

/-- **`liveInSets` is the least fixed point**: it is bounded by every pre-fixed
point of the liveness step. This is the engine for dominance *preservation* — to
show a rewritten function still passes `domCheck` it suffices to exhibit a
pre-fixed point built from the original's live sets. -/
theorem liveInSets_least {f : Func} {li ub : Array (List ValId)}
    (h : liveInSets f = some li) (hub : Sub (liveStep f ub) ub) : Sub li ub := by
  have key : ∀ (fuel : Nat) (cur : Array (List ValId)), Sub cur ub →
      ∀ {out}, liveInSets.go f fuel cur = some out → Sub out ub := by
    intro fuel
    induction fuel with
    | zero => intro cur _ out hgo; simp [liveInSets.go] at hgo
    | succ n ih =>
      intro cur hcur out hgo
      rw [liveInSets.go] at hgo
      split at hgo
      · obtain rfl := Option.some.inj hgo; exact hcur
      · exact ih _ (fun i x hx => hub i x (liveStep_mono hcur i x hx)) hgo
  unfold liveInSets at h
  exact key _ _ sub_replicate h

/-! ### Convergence of the liveness fixed point

`Func.domCheck` is `false` *by definition* when `liveInSets` runs out of fuel, so
every statement about dominance preservation first needs to know that it never
does. `liveInSets_isSome` below closes that gap: the iterates increase (Kleene,
from `liveStep_mono`), each is contained in the finite universe of ids the
function mentions, and the sum of their sizes strictly increases at every
non-exiting round — so the fuel `blocks.size * (total + 1) + 2` always
suffices. -/

/-! ### Sortedness of the helper sets -/

theorem nodup_of_pairwise_lt {l : List ValId} (h : l.Pairwise (· < ·)) : l.Nodup :=
  h.imp (fun hlt => Nat.ne_of_lt hlt)

theorem insertSorted_pairwise {v : ValId} {l : List ValId} (h : l.Pairwise (· < ·)) :
    (insertSorted v l).Pairwise (· < ·) := by
  induction l with
  | nil => simp [insertSorted]
  | cons w rest ih =>
    rw [List.pairwise_cons] at h
    by_cases h1 : v < w
    · simp only [insertSorted, h1, if_true]
      refine List.pairwise_cons.mpr ⟨?_, List.pairwise_cons.mpr ⟨h.1, h.2⟩⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact h1
      · exact Nat.lt_trans h1 (h.1 y hy)
    · by_cases h2 : v = w
      · subst h2
        simp only [insertSorted, h1, if_false]
        exact List.pairwise_cons.mpr ⟨h.1, h.2⟩
      · simp only [insertSorted, h1, h2, if_false]
        refine List.pairwise_cons.mpr ⟨?_, ih h.2⟩
        intro y hy
        rcases mem_insertSorted.mp hy with rfl | hy
        · exact Nat.lt_of_le_of_ne (Nat.not_lt.mp h1) (fun heq => h2 heq.symm)
        · exact h.1 y hy

theorem unionS_pairwise {xs ys : List ValId} (h : ys.Pairwise (· < ·)) :
    (unionS xs ys).Pairwise (· < ·) := by
  unfold unionS
  induction xs generalizing ys with
  | nil => exact h
  | cons a as ih => exact ih (insertSorted_pairwise h)

theorem diffS_pairwise {xs ys : List ValId} (h : xs.Pairwise (· < ·)) :
    (diffS xs ys).Pairwise (· < ·) :=
  h.sublist List.filter_sublist

theorem nil_pairwise : ([] : List ValId).Pairwise (· < ·) := List.Pairwise.nil

/-! ### Extensionality: a sorted list is determined by its elements -/

theorem pairwise_lt_ext : ∀ {l1 l2 : List ValId}, l1.Pairwise (· < ·) → l2.Pairwise (· < ·) →
    (∀ x, x ∈ l1 ↔ x ∈ l2) → l1 = l2 := by
  intro l1
  induction l1 with
  | nil =>
    intro l2 _ _ hmem
    cases l2 with
    | nil => rfl
    | cons b t2 => exact absurd ((hmem b).mpr (by simp)) (by simp)
  | cons a t ih =>
    intro l2 h1 h2 hmem
    cases l2 with
    | nil => exact absurd ((hmem a).mp (by simp)) (by simp)
    | cons b t2 =>
      rw [List.pairwise_cons] at h1 h2
      have hab : a = b := by
        by_contra hne
        have ha : a ∈ b :: t2 := (hmem a).mp (by simp)
        have hb : b ∈ a :: t := (hmem b).mpr (by simp)
        rcases List.mem_cons.mp ha with rfl | ha'
        · exact hne rfl
        rcases List.mem_cons.mp hb with rfl | hb'
        · exact hne rfl
        exact absurd (Nat.lt_trans (h1.1 b hb') (h2.1 a ha')) (Nat.lt_irrefl _)
      subst hab
      refine congrArg (a :: ·) (ih h1.2 h2.2 ?_)
      intro x
      constructor
      · intro hx
        rcases List.mem_cons.mp ((hmem x).mp (by simp [hx])) with rfl | hx'
        · exact absurd (h1.1 x hx) (Nat.lt_irrefl _)
        · exact hx'
      · intro hx
        rcases List.mem_cons.mp ((hmem x).mpr (by simp [hx])) with rfl | hx'
        · exact absurd (h2.1 x hx) (Nat.lt_irrefl _)
        · exact hx'

/-! ### Iterate invariants -/

/-- Every id any liveness iterate can contain. -/
def liveUniverse (f : Func) : List ValId := f.blocks.toList.flatMap blockUses

theorem mem_liveUniverse {f : Func} {i : BlockId} {b : Block} {x : ValId}
    (hb : f.blocks[i]? = some b) (hx : x ∈ blockUses b) : x ∈ liveUniverse f := by
  have hmem : b ∈ f.blocks.toList := by
    obtain ⟨hlt, hget⟩ := Array.getElem?_eq_some_iff.mp hb
    exact List.mem_iff_getElem.mpr ⟨i, by simpa using hlt, by simpa using hget⟩
  simp only [liveUniverse, List.mem_flatMap]
  exact ⟨b, hmem, hx⟩

theorem lout_pairwise {li : Array (List ValId)} (edges : List Edge) {acc : List ValId}
    (h : acc.Pairwise (· < ·)) :
    (edges.foldl (fun acc (e : Edge) => unionS (li[e.target]?.getD []) acc) acc).Pairwise
      (· < ·) := by
  induction edges generalizing acc with
  | nil => exact h
  | cons e es ih => exact ih (unionS_pairwise h)

theorem liveStep_pairwise {f : Func} {A : Array (List ValId)} (i : Nat) :
    ((liveStep f A)[i]?.getD []).Pairwise (· < ·) := by
  rcases hb : f.blocks[i]? with _ | b
  · rw [liveStep_get_none hb]; exact List.Pairwise.nil
  · rw [liveStep_get_eq hb]
    exact diffS_pairwise (unionS_pairwise (lout_pairwise _ List.Pairwise.nil))

theorem liveStep_liveUniverse {f : Func} {A : Array (List ValId)}
    (hA : ∀ (i : Nat) (x : ValId), x ∈ A[i]?.getD [] → x ∈ liveUniverse f) :
    ∀ (i : Nat) (x : ValId), x ∈ (liveStep f A)[i]?.getD [] → x ∈ liveUniverse f := by
  intro i x hx
  rcases hb : f.blocks[i]? with _ | b
  · rw [liveStep_get_none hb] at hx; simp at hx
  · rw [liveStep_get_eq hb, mem_diffS] at hx
    rcases mem_unionS.mp hx.1 with hu | hl
    · exact mem_liveUniverse hb hu
    · rcases mem_lout.mp hl with ⟨e, -, hxe⟩ | hnil
      · exact hA _ _ hxe
      · simp at hnil

/-! ### The measure -/

/-- Sum of the live-set sizes over the first `n` blocks. -/
def liveMeasure (n : Nat) (A : Array (List ValId)) : Nat :=
  ((List.range n).map fun i => (A[i]?.getD []).length).sum

theorem sum_le_sum {l : List Nat} {F G : Nat → Nat} (h : ∀ i ∈ l, F i ≤ G i) :
    ((l.map F).sum) ≤ ((l.map G).sum) := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h a (by simp)) (ih fun i hi => h i (by simp [hi]))

theorem sum_lt_sum {l : List Nat} {F G : Nat → Nat} (hle : ∀ i ∈ l, F i ≤ G i)
    {j : Nat} (hj : j ∈ l) (hlt : F j < G j) : ((l.map F).sum) < ((l.map G).sum) := by
  induction l with
  | nil => simp at hj
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hj with rfl | hj'
    · exact Nat.add_lt_add_of_lt_of_le hlt (sum_le_sum fun i hi => hle i (by simp [hi]))
    · exact Nat.add_lt_add_of_le_of_lt (hle a (by simp))
        (ih (fun i hi => hle i (by simp [hi])) hj')

theorem sum_le_const {l : List Nat} {F : Nat → Nat} {c : Nat} (h : ∀ i ∈ l, F i ≤ c) :
    ((l.map F).sum) ≤ l.length * c := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := ih fun i hi => h i (by simp [hi])
    have ha := h a (by simp)
    calc F a + (as.map F).sum ≤ c + as.length * c := Nat.add_le_add ha this
      _ = (as.length + 1) * c := by ring


theorem length_le_liveUniverse {f : Func} {l : List ValId} (hp : l.Pairwise (· < ·))
    (hs : ∀ x ∈ l, x ∈ liveUniverse f) : l.length ≤ (liveUniverse f).length :=
  (List.subperm_of_subset (nodup_of_pairwise_lt hp) hs).length_le

theorem measure_le {f : Func} {n : Nat} {A : Array (List ValId)}
    (hp : ∀ (i : Nat), (A[i]?.getD []).Pairwise (· < ·))
    (hu : ∀ (i : Nat) (x : ValId), x ∈ A[i]?.getD [] → x ∈ liveUniverse f) :
    liveMeasure n A ≤ n * (liveUniverse f).length := by
  have h := sum_le_const (l := List.range n) (F := fun i => (A[i]?.getD []).length)
    (c := (liveUniverse f).length) (fun i _ => length_le_liveUniverse (hp i) (fun x hx => hu i x hx))
  simpa [liveMeasure] using h

theorem measure_lt {n : Nat} {A B : Array (List ValId)}
    (hsub : Sub A B) (hpA : ∀ (i : Nat), (A[i]?.getD []).Pairwise (· < ·))
    (hpB : ∀ (i : Nat), (B[i]?.getD []).Pairwise (· < ·))
    (hsA : A.size = n) (hsB : B.size = n) (hne : A ≠ B) :
    liveMeasure n A < liveMeasure n B := by
  have hle : ∀ (i : Nat), (A[i]?.getD []).length ≤ (B[i]?.getD []).length := fun i =>
    (List.subperm_of_subset (nodup_of_pairwise_lt (hpA i)) (fun x hx => hsub i x hx)).length_le
  have hex : ∃ (i : Nat), A[i]? ≠ B[i]? := by
    by_contra hc
    exact hne (Array.ext_getElem? fun i => by by_contra h; exact hc ⟨i, h⟩)
  obtain ⟨i, hi⟩ := hex
  have hin : i < n := by
    by_contra hge
    have hge' : n ≤ i := Nat.not_lt.mp hge
    have h1 : A[i]? = none := by rw [Array.getElem?_eq_none_iff]; omega
    have h2 : B[i]? = none := by rw [Array.getElem?_eq_none_iff]; omega
    exact hi (h1.trans h2.symm)
  have hAi : A[i]? = some (A[i]?.getD []) := by
    rw [Array.getElem?_eq_getElem (by omega)]; simp
  have hBi : B[i]? = some (B[i]?.getD []) := by
    rw [Array.getElem?_eq_getElem (by omega)]; simp
  have hne' : A[i]?.getD [] ≠ B[i]?.getD [] := by
    intro heq; exact hi (hAi.trans (heq ▸ hBi.symm))
  -- a member of B[i] outside A[i]
  have hmem : ∃ (x : ValId), x ∈ B[i]?.getD [] ∧ x ∉ A[i]?.getD [] := by
    by_contra hc
    refine hne' (pairwise_lt_ext (hpA i) (hpB i) (fun x => ⟨fun hx => hsub i x hx, fun hx => ?_⟩))
    by_contra hxA
    exact hc ⟨x, hx, hxA⟩
  obtain ⟨x, hxB, hxA⟩ := hmem
  have hlt : (A[i]?.getD []).length < (B[i]?.getD []).length := by
    have hsub' : A[i]?.getD [] ⊆ (B[i]?.getD []).erase x := by
      intro y hy
      refine (List.mem_erase_of_ne (fun h => hxA ?_)).mpr (hsub i y hy)
      rw [← h]; exact hy
    have h1 := (List.subperm_of_subset (nodup_of_pairwise_lt (hpA i)) hsub').length_le
    rw [List.length_erase_of_mem hxB] at h1
    have h2 : 0 < (B[i]?.getD []).length := List.length_pos_of_mem hxB
    omega
  exact sum_lt_sum (l := List.range n) (fun j _ => hle j) (List.mem_range.mpr hin) hlt


theorem replicate_getD (n i : Nat) :
    ((Array.replicate n ([] : List ValId))[i]?.getD []) = [] := by
  rcases h : (Array.replicate n ([] : List ValId))[i]? with _ | l
  · simp
  · obtain ⟨hlt, hget⟩ := Array.getElem?_eq_some_iff.mp h
    simp only [Option.getD_some]
    simpa using hget.symm

theorem liveUniverse_length_le (f : Func) :
    (liveUniverse f).length ≤
      f.blocks.foldl (init := 0)
        (fun acc b => acc + (blockDefs b).length + (blockUses b).length) := by
  have key : ∀ (l : List Block) (acc : Nat),
      acc + ((l.map fun b => (blockUses b).length).sum) ≤
        l.foldl (fun acc b => acc + (blockDefs b).length + (blockUses b).length) acc := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons b bs ih =>
      intro acc
      simp only [List.map_cons, List.sum_cons, List.foldl_cons]
      have h := ih (acc + (blockDefs b).length + (blockUses b).length)
      omega
  rw [← Array.foldl_toList]
  simp only [liveUniverse, List.length_flatMap]
  simpa using key f.blocks.toList 0

theorem go_isSome {f : Func} :
    ∀ (fuel : Nat) (cur : Array (List ValId)),
      cur.size = f.blocks.size →
      (∀ (i : Nat), (cur[i]?.getD []).Pairwise (· < ·)) →
      (∀ (i : Nat) (x : ValId), x ∈ cur[i]?.getD [] → x ∈ liveUniverse f) →
      Sub cur (liveStep f cur) →
      f.blocks.size * (liveUniverse f).length < liveMeasure f.blocks.size cur + fuel →
      ∃ li, liveInSets.go f fuel cur = some li := by
  intro fuel
  induction fuel with
  | zero =>
    intro cur hsz hp hu hsub hfuel
    have := measure_le (f := f) (n := f.blocks.size) hp hu
    omega
  | succ k ih =>
    intro cur hsz hp hu hsub hfuel
    rw [liveInSets.go]
    split
    · exact ⟨cur, rfl⟩
    · rename_i hbeq
      have hne : liveStep f cur ≠ cur := fun h => hbeq (by simp [h])
      have hlt : liveMeasure f.blocks.size cur < liveMeasure f.blocks.size (liveStep f cur) :=
        measure_lt hsub hp (fun i => liveStep_pairwise i) hsz liveStep_size (Ne.symm hne)
      exact ih (liveStep f cur) liveStep_size (fun i => liveStep_pairwise i)
        (liveStep_liveUniverse hu) (liveStep_mono hsub) (by omega)

/-- **`liveInSets` always converges.** The fuel `blocks.size * (total + 1) + 2`
always suffices: the iterates increase (Kleene, via `liveStep_mono`), each is
contained in the finite universe of mentioned ids, so the sum of their sizes —
which strictly increases at every non-exiting round — is bounded by
`blocks.size * total`. -/
theorem liveInSets_isSome (f : Func) : ∃ li, liveInSets f = some li := by
  refine go_isSome _ _ (by simp) (fun i => by rw [replicate_getD]; exact List.Pairwise.nil)
    (fun i x hx => by rw [replicate_getD] at hx; simp at hx) sub_replicate ?_
  have h0 : liveMeasure f.blocks.size (Array.replicate f.blocks.size []) = 0 := by
    simp [liveMeasure, replicate_getD]
  have hU := liveUniverse_length_le f
  rw [h0]
  have : f.blocks.size * (liveUniverse f).length
      ≤ f.blocks.size * (f.blocks.foldl (init := 0)
          fun acc b => acc + (blockDefs b).length + (blockUses b).length) :=
    Nat.mul_le_mul_left _ hU
  have hexp : f.blocks.size * ((f.blocks.foldl (init := 0)
      fun acc b => acc + (blockDefs b).length + (blockUses b).length) + 1)
      = f.blocks.size * (f.blocks.foldl (init := 0)
          fun acc b => acc + (blockDefs b).length + (blockUses b).length) + f.blocks.size := by
    ring
  omega


/-! ### A reusable dominance-preservation criterion -/

/-- **Dominance preservation criterion.** A rewrite that keeps the function's
parameters and entry, only ever *shrinks* what a block reads, only ever *keeps*
what a block defines, and only ever drops outgoing edges, preserves
`Func.domCheck`. -/
theorem domCheck_of_shrinking {f g : Func}
    (hdom : Func.domCheck f = true)
    (hparams : g.params = f.params) (hentry : g.entry = f.entry)
    (hrel : ∀ (i : BlockId) (b' : Block), g.blocks[i]? = some b' →
      ∃ b, f.blocks[i]? = some b
        ∧ (∀ x ∈ blockUses b', x ∈ blockUses b)
        ∧ (∀ x ∈ blockDefs b, x ∈ blockDefs b')
        ∧ (∀ e ∈ b'.term.edges, ∃ e0 ∈ b.term.edges, e0.target = e.target)) :
    Func.domCheck g = true := by
  obtain ⟨li, hli⟩ := liveInSets_isSome f
  obtain ⟨li', hli'⟩ := liveInSets_isSome g
  -- the original's live sets are a pre-fixed point for the rewritten function
  have hub : Sub (liveStep g li) li := by
    intro i x hx
    rcases hb' : g.blocks[i]? with _ | b'
    · rw [liveStep_get_none hb'] at hx; simp at hx
    · rw [liveStep_get_eq hb', mem_diffS] at hx
      obtain ⟨b, hb, huses, hdefs, hedges⟩ := hrel i b' hb'
      rw [liveIn_eq hli hb, mem_diffS]
      refine ⟨?_, fun hmem => hx.2 (hdefs x hmem)⟩
      rcases mem_unionS.mp hx.1 with hu | hl
      · exact mem_unionS.mpr (Or.inl (huses x hu))
      · rcases mem_lout.mp hl with ⟨e, he, hxe⟩ | hnil
        · obtain ⟨e0, he0, hteq⟩ := hedges e he
          exact mem_unionS.mpr (Or.inr (mem_lout.mpr (Or.inl ⟨e0, he0, by rw [hteq]; exact hxe⟩)))
        · simp at hnil
  have hsub : Sub li' li := liveInSets_least hli' hub
  -- hence nothing beyond the parameters is live into the rewritten entry
  unfold Func.domCheck
  rw [hli']
  simp only [decide_eq_true_eq]
  rw [List.eq_nil_iff_forall_not_mem]
  intro x hx
  rw [mem_diffS] at hx
  refine hx.2 ?_
  rw [hparams]
  refine domCheck_entry hli hdom ?_
  rw [← hentry]
  exact hsub _ _ hx.1

/-- **Dominance preservation under use substitution.**  In addition to the
image of the old live-in set, `avail i` contains representatives made available
by a dominating CSE table on entry to block `i`.  A replaced definition either
has its representative defined earlier in the same output block, or finds it in
that entry table.  Entry availability is empty, and availability inherited by a
successor either was already available to its predecessor or is defined there.

This is the substitution-aware counterpart of `domCheck_of_shrinking`.  Its
pre-fixed point is `σ '' liveIn(f) ∪ avail`; `liveInSets_least` then does the
fixed-point work. -/
theorem domCheck_of_substitution {f g : Func} (σ : ValId → ValId)
    (avail : BlockId → List ValId)
    (hdom : Func.domCheck f = true)
    (hparams : g.params = f.params) (hentry : g.entry = f.entry)
    (hσparams : ∀ x ∈ f.params, σ x = x)
    (havailEntry : avail g.entry = [])
    (hrel : ∀ (i : BlockId) (b' : Block), g.blocks[i]? = some b' →
      ∃ b, f.blocks[i]? = some b
        ∧ (∀ x ∈ blockUses b', ∃ y ∈ blockUses b, σ y = x)
        ∧ (∀ y ∈ blockDefs b, σ y ∈ blockDefs b' ∨ σ y ∈ avail i)
        ∧ (∀ e ∈ b'.term.edges, ∃ e0 ∈ b.term.edges, e0.target = e.target)
        ∧ (∀ e ∈ b'.term.edges, ∀ x ∈ avail e.target,
            x ∈ blockDefs b' ∨ x ∈ avail i)) :
    Func.domCheck g = true := by
  obtain ⟨li, hli⟩ := liveInSets_isSome f
  obtain ⟨li', hli'⟩ := liveInSets_isSome g
  let ub : Array (List ValId) := Array.ofFn fun i : Fin g.blocks.size =>
    unionS ((li[i.1]?.getD []).map σ) (avail i.1)
  have mem_ub (i : Nat) (x : ValId) :
      x ∈ ub[i]?.getD [] ↔
        i < g.blocks.size ∧ ((∃ y ∈ li[i]?.getD [], σ y = x) ∨ x ∈ avail i) := by
    by_cases hi : i < g.blocks.size
    · have hiub : i < ub.size := by simpa [ub] using hi
      rw [Array.getElem?_eq_getElem hiub]
      simp only [Option.getD_some, ub, Array.getElem_ofFn, mem_unionS, List.mem_map]
      constructor
      · rintro (⟨y, hy, rfl⟩ | hx)
        · exact ⟨hi, Or.inl ⟨y, hy, rfl⟩⟩
        · exact ⟨hi, Or.inr hx⟩
      · rintro ⟨-, ⟨y, hy, rfl⟩ | hx⟩
        · exact Or.inl ⟨y, hy, rfl⟩
        · exact Or.inr hx
    · have hgeub : ub.size ≤ i := by simpa [ub] using Nat.not_lt.mp hi
      rw [Array.getElem?_eq_none_iff.mpr hgeub]
      simp [hi]
  have hub : Sub (liveStep g ub) ub := by
    intro i x hx
    rcases hb' : g.blocks[i]? with _ | b'
    · rw [liveStep_get_none hb'] at hx; simp at hx
    · have hi : i < g.blocks.size := (Array.getElem?_eq_some_iff.mp hb').1
      rw [liveStep_get_eq hb', mem_diffS] at hx
      obtain ⟨b, hb, huses, hdefs, hedges, havail⟩ := hrel i b' hb'
      rw [mem_ub]
      refine ⟨hi, ?_⟩
      rcases mem_unionS.mp hx.1 with hu | hl
      · obtain ⟨y, hy, hσ⟩ := huses x hu
        by_cases hyd : y ∈ blockDefs b
        · rcases hdefs y hyd with hd | ha
          · exact absurd (hσ ▸ hd) hx.2
          · exact Or.inr (hσ ▸ ha)
        · exact Or.inl ⟨y, liveIn_of_uses hli hb hy hyd, hσ⟩
      · rcases mem_lout.mp hl with ⟨e, he, hxe⟩ | hnil
        · rw [mem_ub] at hxe
          rcases hxe.2 with ⟨y, hy, hσ⟩ | ha
          · obtain ⟨e0, he0, htarget⟩ := hedges e he
            by_cases hyd : y ∈ blockDefs b
            · rcases hdefs y hyd with hd | hav
              · exact absurd (hσ ▸ hd) hx.2
              · exact Or.inr (hσ ▸ hav)
            · exact Or.inl ⟨y, liveIn_of_succ hli hb he0
                (by rw [htarget]; exact hy) hyd, hσ⟩
          · rcases havail e he x ha with hd | hav
            · exact absurd hd hx.2
            · exact Or.inr hav
        · simp at hnil
  have hsub : Sub li' ub := liveInSets_least hli' hub
  unfold Func.domCheck
  rw [hli']
  simp only [decide_eq_true_eq]
  rw [List.eq_nil_iff_forall_not_mem]
  intro x hx
  rw [mem_diffS] at hx
  have hxub := hsub _ _ hx.1
  rw [mem_ub] at hxub
  rcases hxub.2 with ⟨y, hy, hσ⟩ | ha
  · have hyp : y ∈ f.params := domCheck_entry hli hdom (by rw [← hentry]; exact hy)
    exact hx.2 (by rw [hparams, ← hσ, hσparams y hyp]; exact hyp)
  · rw [havailEntry] at ha
    simp at ha


end ToAsm

/-- **The passes' simulation invariant**: two register files agree on everything
live into block `i`, modulo the use-substitution `σ` a pass applies. This is the
liveness-indexed strengthening of `exec_congr`'s agreement hypothesis: the frame
lemma needs agreement on *all* uses of the function, which a pass that reroutes
uses cannot give — but it only ever needs it for the values that are live at the
point it is looking at, and `domCheck` is exactly what makes the live sets
propagate soundly. -/
def LiveAgree (li : Array (List ValId)) (i : BlockId) (σ : ValId → ValId) (R R' : Regs) : Prop :=
  ∀ x ∈ li[i]?.getD [], R x = R' (σ x)

/-- **Base case of the dominance bridge**, fully proved: at a function's entry
block, under `domCheck`, the invariant holds for any substitution that fixes the
function's parameters — because the check says nothing else is live there. -/
theorem liveAgree_entry {f : Func} {li : Array (List ValId)}
    (hli : ToAsm.liveInSets f = some li) (hdom : ToAsm.Func.domCheck f = true)
    {σ : ValId → ValId} (hσ : ∀ x ∈ f.params, σ x = x) (args : List U256) :
    LiveAgree li f.entry σ (Regs.empty.setMany f.params args)
      (Regs.empty.setMany f.params args) := by
  intro x hx
  rw [hσ x (ToAsm.domCheck_entry hli hdom hx)]

/-! ### Entry-rooted definition provenance

`LiveAgree` is deliberately local to one block.  The two substitution passes
also need the history fact which justifies that local invariant: a live value
at a reached block did not appear in the persistent register file by accident;
its unique definition has occurred on the path from the function entry (unless
it is a function parameter).  Keeping the path explicit retains repeated block
visits, which is essential for loop-carried block parameters and CSE values.

The statement below is the common, pass-independent part of that provenance
argument.  It uses only the CFG and the liveness fixed point, so both trivial
parameter elimination and CSE can instantiate it. -/

/-- A finite CFG path rooted at the function entry.  `path` contains the
visited predecessor blocks, in execution order; `i` is the currently reached
block. -/
inductive EntryPath (f : Func) : List BlockId → BlockId → Prop
  | entry : EntryPath f [] f.entry
  | edge {path : List BlockId} {i : BlockId} {b : Block} {e : Edge} :
      EntryPath f path i →
      f.blocks[i]? = some b →
      e ∈ b.term.edges →
      EntryPath f (path ++ [i]) e.target

/-- A value has crossed a defining block on an entry-rooted path. -/
def DefinedOnPath (f : Func) (path : List BlockId) (x : ValId) : Prop :=
  ∃ i ∈ path, ∃ b, f.blocks[i]? = some b ∧ x ∈ ToAsm.blockDefs b

theorem DefinedOnPath.snoc {f : Func} {path : List BlockId} {i : BlockId}
    {b : Block} {x : ValId} (hb : f.blocks[i]? = some b)
    (hx : x ∈ ToAsm.blockDefs b) : DefinedOnPath f (path ++ [i]) x := by
  exact ⟨i, by simp, b, hb, hx⟩

theorem DefinedOnPath.mono_snoc {f : Func} {path : List BlockId}
    {i : BlockId} {x : ValId} (h : DefinedOnPath f path x) :
    DefinedOnPath f (path ++ [i]) x := by
  obtain ⟨j, hj, b, hb, hx⟩ := h
  exact ⟨j, List.mem_append_left _ hj, b, hb, hx⟩

/-- **Entry-rooted provenance invariant.**  Under `domCheck`, every value live
at a block reached from entry is either an entry parameter or its definition
has occurred in one of the predecessor blocks on the concrete path.  The proof
is the forward/path form of the usual backwards-liveness dominance argument:
crossing an edge either crosses the unique definition or propagates liveness to
the predecessor. -/
theorem EntryPath.live_origin {f : Func} {li : Array (List ValId)}
    (hli : ToAsm.liveInSets f = some li)
    (hdom : ToAsm.Func.domCheck f = true)
    {path : List BlockId} {i : BlockId} (hp : EntryPath f path i)
    {x : ValId} (hx : x ∈ li[i]?.getD []) :
    x ∈ f.params ∨ DefinedOnPath f path x := by
  induction hp with
  | entry =>
      exact Or.inl (ToAsm.domCheck_entry hli hdom hx)
  | @edge path i b e hp hb he ih =>
      by_cases hd : x ∈ ToAsm.blockDefs b
      · exact Or.inr (DefinedOnPath.snoc hb hd)
      · rcases ih (ToAsm.liveIn_of_succ hli hb he hx hd) with hparam | hpath
        · exact Or.inl hparam
        · exact Or.inr hpath.mono_snoc

/-- Register-domain part of entry-rooted provenance.  At a configuration in
block `b`, after the instructions in `done` have executed, every bound id came
from a function parameter, a predecessor block on the concrete path, a current
block parameter, or an already-executed instruction in this block. -/
def BindingProvenance (f : Func) (path : List BlockId) (b : Block)
    (done : List Instr) (R : Regs) : Prop :=
  ∀ {x : ValId} {v : U256}, R x = some v →
    x ∈ f.params ∨ DefinedOnPath f path x ∨ x ∈ b.params ∨
      x ∈ done.flatMap Instr.defs

theorem Regs.eq_some_setMany {R : Regs} {xs : List ValId} {vs : List U256}
    {x : ValId} {v : U256} (h : (R.setMany xs vs) x = some v) :
    R x = some v ∨ x ∈ xs := by
  by_cases hx : x ∈ xs
  · exact Or.inr hx
  · left
    rw [Regs.setMany_of_not_mem R xs vs hx] at h
    exact h

theorem Regs.eq_some_of_getMany {R : Regs} {xs : List ValId} {vals : List U256}
    (hget : R.getMany xs = some vals) {x : ValId} (hx : x ∈ xs) :
    ∃ v, R x = some v := by
  induction xs generalizing vals with
  | nil => simp at hx
  | cons y ys ih =>
      rw [Regs.getMany_cons] at hget
      cases hy : R y with
      | none => simp [hy] at hget
      | some w =>
          cases hys : R.getMany ys with
          | none => simp [hy, hys] at hget
          | some ws =>
              rcases List.mem_cons.mp hx with rfl | hx
              · exact ⟨w, hy⟩
              · exact ih hys hx

/-- Any successful register read is backed by one of the concrete provenance
sites carried by `BindingProvenance`. -/
theorem BindingProvenance.read {f : Func} {path : List BlockId} {b : Block}
    {done : List Instr} {R : Regs} (h : BindingProvenance f path b done R)
    {xs : List ValId} {vals : List U256} (hget : R.getMany xs = some vals)
    {x : ValId} (hx : x ∈ xs) :
    x ∈ f.params ∨ DefinedOnPath f path x ∨ x ∈ b.params ∨
      x ∈ done.flatMap Instr.defs := by
  obtain ⟨v, hv⟩ := Regs.eq_some_of_getMany hget hx
  exact h hv

theorem bindingProvenance_entry {f : Func} {b : Block} (args : List U256) :
    BindingProvenance f [] b [] (Regs.empty.setMany f.params args) := by
  intro x v hx
  rcases Regs.eq_some_setMany hx with hempty | hp
  · simp [Regs.empty] at hempty
  · exact Or.inl hp

/-- Executing one instruction preserves binding provenance and records its
destinations in the completed prefix.  This lemma is independent of the
instruction's value semantics: those semantics determine the words, while SSA
shape determines their provenance sites. -/
theorem BindingProvenance.setMany_instr {f : Func} {path : List BlockId}
    {b : Block} {done : List Instr} {R : Regs} (h : BindingProvenance f path b done R)
    {i : Instr} {vals : List U256} :
    BindingProvenance f path b (done ++ [i]) (R.setMany i.defs vals) := by
  intro x v hx
  rcases Regs.eq_some_setMany hx with hold | hnew
  · rcases h hold with hp | hpath | hparam | hdone
    · exact Or.inl hp
    · exact Or.inr (Or.inl hpath)
    · exact Or.inr (Or.inr (Or.inl hparam))
    · exact Or.inr (Or.inr (Or.inr (by
        rw [List.flatMap_append]
        exact List.mem_append_left _ hdone)))
  · exact Or.inr (Or.inr (Or.inr (by
      rw [List.flatMap_append]
      exact List.mem_append_right _ (by simpa using hnew))))

theorem BindingProvenance.set_const {f : Func} {path : List BlockId}
    {b : Block} {done : List Instr} {R : Regs} (h : BindingProvenance f path b done R)
    {d : ValId} {w : U256} :
    BindingProvenance f path b (done ++ [.const d w]) (R.set d w) := by
  change BindingProvenance f path b (done ++ [.const d w])
    (R.setMany (Instr.defs (.const d w)) [w])
  exact h.setMany_instr (i := .const d w) (vals := [w])

/-- At a terminator, an edge turns everything defined in the source block into
path provenance and introduces precisely the target block parameters. -/
theorem BindingProvenance.edge {f : Func} {path : List BlockId}
    {i : BlockId} {b tb : Block} {R : Regs}
    (hb : f.blocks[i]? = some b)
    (h : BindingProvenance f path b b.instrs R)
    (vals : List U256) :
    BindingProvenance f (path ++ [i]) tb [] (R.setMany tb.params vals) := by
  intro x v hx
  rcases Regs.eq_some_setMany hx with hold | hparam
  · rcases h hold with hp | hpath | hbparam | hdone
    · exact Or.inl hp
    · exact Or.inr (Or.inl hpath.mono_snoc)
    · exact Or.inr (Or.inl (DefinedOnPath.snoc hb
        (ToAsm.mem_blockDefs.mpr (Or.inl hbparam))))
    · exact Or.inr (Or.inl (DefinedOnPath.snoc hb
        (ToAsm.mem_blockDefs.mpr (Or.inr hdone))))
  · exact Or.inr (Or.inr (Or.inl hparam))

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

def removedBlock (bi i j : Nat) (b : Block) : Block :=
  let b0 := if j = bi then { b with params := b.params.eraseIdx i } else b
  { b0 with term := mapEdges (fun e =>
    if e.target = bi then { e with args := e.args.eraseIdx i } else e) b0.term }

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


/-! ## The pipeline gate

`optimizeProg` is `inlineProg` (program-level function inlining), then the
per-function four-pass pipeline, then a **defensive gate**: the candidate is
returned only if it re-checks `wfCheck && domCheck`, otherwise the *original*
program is. Naming the candidate keeps the lemmas below (and the top-level
proof) independent of the exact pipeline shape — only `optimizeProg_candidate`
mentions it. -/

/-- The pipeline's output *before* the defensive gate. -/
def optimizeCandidate (P : Prog) : Prog :=
  let P0 := Passes.inlineProg P
  { main := optimizeFunc P0.main, funcs := P0.funcs.map optimizeFunc }

/-- `optimizeProg`, refactored through `optimizeCandidate`. Definitional: this
is the single place that tracks the pipeline's shape. -/
theorem optimizeProg_candidate (P : Prog) :
    optimizeProg P =
      if (optimizeCandidate P).wfCheck && ToAsm.Prog.domCheck (optimizeCandidate P)
      then optimizeCandidate P else P := rfl

/-- Gate rejected ⇒ the optimizer is the identity. -/
theorem optimizeProg_of_gate_false {P : Prog}
    (h : ((optimizeCandidate P).wfCheck && ToAsm.Prog.domCheck (optimizeCandidate P)) = false) :
    optimizeProg P = P := by
  rw [optimizeProg_candidate, h]; simp

/-- Gate accepted ⇒ the optimizer is the candidate. -/
theorem optimizeProg_of_gate_true {P : Prog}
    (h : ((optimizeCandidate P).wfCheck && ToAsm.Prog.domCheck (optimizeCandidate P)) = true) :
    optimizeProg P = optimizeCandidate P := by
  rw [optimizeProg_candidate, h]; simp

section
variable [model : ExternalModel]

/-! ### Location-indexed caller replay

The source caller location is a block id together with the number of
instructions already consumed in that block.  This is deliberately positional:
the instruction at the selected site need not be syntactically unique. -/

/-- The rest corresponding to source location `(j,k)` after splicing the call
at `(bi,ci)`.  Locations before (or at) the call run the remaining prefix and
then jump into the copied callee; locations after it are continuations and all
other locations are unchanged. -/
def Passes.inlineCallerRest (bi ci calleeEntry j k : Nat) (site : Block)
    (r : Rest) : Rest :=
  if j = bi ∧ k ≤ ci then
    ⟨(site.instrs.take ci).drop k, .jump ⟨calleeEntry, []⟩⟩
  else r

omit model in
theorem Passes.inlineCallerBlock_get_site {f f' : Func} {bi : Nat}
    {callBlock : Block} {tail : Array Block}
    (hbi : bi < f.blocks.size)
    (hblocks : f'.blocks = (f.blocks.set! bi callBlock) ++ tail) :
    f'.blocks[bi]? = some callBlock := by
  rw [hblocks, Array.getElem?_append_left (by simp [hbi])]
  simp [Array.set!, hbi]

omit model in
theorem Passes.inlineCallerBlock_get_other {f f' : Func} {bi j : Nat}
    {callBlock b : Block} {tail : Array Block}
    (hj : f.blocks[j]? = some b) (hne : j ≠ bi)
    (hblocks : f'.blocks = (f.blocks.set! bi callBlock) ++ tail) :
    f'.blocks[j]? = some b := by
  have hjlt : j < f.blocks.size := (Array.getElem?_eq_some_iff.mp hj).1
  rw [hblocks, Array.getElem?_append_left (by simp [hjlt])]
  simpa [Array.set!, Array.getElem?_setIfInBounds_ne (Ne.symm hne)] using hj

omit model in
theorem Passes.inlineCallerBlock_get_site₂ {f f' : Func} {bi : Nat}
    {callBlock : Block} {mid tail : Array Block}
    (hbi : bi < f.blocks.size)
    (hblocks : f'.blocks = (f.blocks.set! bi callBlock) ++ mid ++ tail) :
    f'.blocks[bi]? = some callBlock := by
  rw [hblocks, Array.getElem?_append_left (by simp; omega),
    Array.getElem?_append_left (by simp [hbi])]
  simp [Array.set!, hbi]

omit model in
theorem Passes.inlineCallerBlock_get_other₂ {f f' : Func} {bi j : Nat}
    {callBlock b : Block} {mid tail : Array Block}
    (hj : f.blocks[j]? = some b) (hne : j ≠ bi)
    (hblocks : f'.blocks = (f.blocks.set! bi callBlock) ++ mid ++ tail) :
    f'.blocks[j]? = some b := by
  have hjlt : j < f.blocks.size := (Array.getElem?_eq_some_iff.mp hj).1
  rw [hblocks, Array.getElem?_append_left (by simp; omega),
    Array.getElem?_append_left (by simp [hjlt])]
  simpa [Array.set!, Array.getElem?_setIfInBounds_ne (Ne.symm hne)] using hj

omit model in
theorem Passes.wfCheck_entry_params_nil {f : Func} {n : Nat}
    (hwf : f.wfCheck n = true) {b : Block}
    (hb : f.blocks[f.entry]? = some b) : b.params = [] := by
  unfold Func.wfCheck at hwf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hwf
  simpa [hb] using hwf.1.2

omit model in
theorem Passes.wfCheck_ret_arity {f : Func} {n : Nat}
    (hwf : f.wfCheck n = true) {b : Block} (hb : b ∈ f.blocks.toList)
    {xs : List ValId} (ht : b.term = .ret xs) : xs.length = f.nrets := by
  unfold Func.wfCheck at hwf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hwf
  have hblock := Array.all_eq_true_iff_forall_mem.mp hwf.2 b (by simpa using hb)
  simp only [Bool.and_eq_true] at hblock
  simpa [ht] using hblock.1.1

/-- The fallback branch of pass soundness, fully proved. -/
theorem optimizeProg_sound_of_fallback {P : Prog} {yst0 yst' : EvmState} {o : Outcome}
    (h : ((optimizeCandidate P).wfCheck && ToAsm.Prog.domCheck (optimizeCandidate P)) = false)
    (hrun : Run (model := model) P yst0 yst' o) :
    Run (model := model) (optimizeProg P) yst0 yst' o := by
  rw [optimizeProg_of_gate_false h]; exact hrun

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

theorem r1 : List.range' 0 1 1 = [0] := by rfl
theorem r2 : List.range' 0 2 1 = [0,1] := by rfl
theorem r8 : List.range' 0 8 1 = [0,1,2,3,4,5,6,7] := by rfl
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
/-- …and so does its optimized form, so the defensive `wfCheck` gate does not
fire. -/
theorem hwfopt : Popt.wfCheck = true := by rfl

unseal Array.anyM.loop in
/-- **`P` is exactly what the new dominance gate rejects**: `liveInSets P.main`
is `#[[2], [2, 11], [11], [2], [], []]`, i.e. the stale value `p = 2` is live
into the entry block while `main` has no parameters. So this program is *not* a
counterexample to the repaired `optimizeProg_sound` (which assumes
`ToAsm.Prog.domCheck P = true`) — it is the witness that the assumption is
necessary. -/
theorem hdomP : ToAsm.Prog.domCheck P = false := by rfl

unseal Array.anyM.loop in
/-- The *optimized* program, by contrast, passes the dominance check
(`liveInSets` is `#[[], [11], [11], [1], [], []]`), so `optimizeProg`'s
defensive gate — which checks the pipeline's *output* — does not fire either.
That is why the un-hypothesised statement really is refuted: nothing downstream
of the pass notices. -/
theorem hdomPopt : ToAsm.Prog.domCheck Popt = true := by rfl

/-! #### The inliner is the identity here

`P` contains no `call`, so the program-level inlining pass in front of the
per-function pipeline does nothing — the counterexample still exercises exactly
the pass it is about. -/

theorem hsites : Passes.siteCounts { main := fMain, funcs := #[] } = #[] := by rfl

theorem hio : Passes.inlineOnce #[] #[] fMain = none := by
  simp only [Passes.inlineOnce, Std.Legacy.Range.forIn_eq_forIn_range']; rfl

theorem hinlineFunc : Passes.inlineFunc #[] #[] fMain = fMain := by
  simp only [Passes.inlineFunc, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size]
  simp [show (8 - 0 + 1 - 1) / 1 = 8 from rfl, r8, hio]

theorem hprune : Passes.pruneFuncs { main := fMain, funcs := #[] }
    = { main := fMain, funcs := #[] } := by
  simp only [Passes.pruneFuncs, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size]
  simp [r1]

theorem hinline : Passes.inlineProg P = P := by
  simp only [P, Passes.inlineProg, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size]
  simp [show (3 - 0 + 1 - 1) / 1 = 3 from rfl, r3, hsites, hinlineFunc, hprune]

/-- The pipeline really does produce `Popt`. -/
theorem hopt : optimizeProg P = Popt := by
  have h : optimizeCandidate P = Popt := by
    simp only [optimizeCandidate, hinline]
    simp [P, Popt, hoptf]
  rw [optimizeProg_of_gate_true (P := P) (by rw [h, hwfopt, hdomPopt]; rfl), h]

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

/-- **Pass soundness from `wfCheck` alone is false** — the statement
`optimizeProg_sound` had before the dominance gate was introduced. `P` is
well-formed and runs to `.normal` with the state unchanged, but its optimized
form has no such run.

This does **not** contradict the repaired `optimizeProg_sound`
(`optimizeProg_sound'` below): `hdomP` says `P` fails
`ToAsm.Prog.domCheck`, so the repaired statement does not apply to it. What this
theorem shows is that the dominance hypothesis is *necessary* — it cannot be
weakened back to `wfCheck`, and the defensive gate on the pipeline's output
cannot substitute for it (`hdomPopt`). -/
theorem optimizeProg_sound_false_without_dom :
    ¬ ∀ (P : Prog) (yst0 yst' : EvmState) (o : Outcome), P.wfCheck = true →
        Run (model := model) P yst0 yst' o →
        Run (model := model) (optimizeProg P) yst0 yst' o := by
  intro hsound
  have := hsound P YulSemantics.EVM.EvmState.init YulSemantics.EVM.EvmState.init .normal hwf
    (cx_run _)
  rw [hopt] at this
  exact cx_no_run _ this

omit model in
/-- The same statement with the dominance hypothesis *added* is not refuted by
this program — vacuously, because the hypothesis fails for it. Recorded so the
two statements cannot be confused. -/
theorem dom_hypothesis_excludes_counterexample :
    ¬ (ToAsm.Prog.domCheck P = true) := by simp [hdomP]

end Counterexample

namespace Passes

/-! ### Pass 4's structural specification

`dve` is the one pass written *without* an `Id.run` loop — a `mapIdx` with
filters — so its output is directly readable, and these lemmas are the complete
structural half of both `dve_sound` and `dve_dom`. -/

/-- The block rewrite `dve` performs, as a function (its `mapIdx` body). -/
def dveBlock (f : Func) (bi : BlockId) (b : Block) : Block :=
  let live := liveSet f
  let keepParam : BlockId → Nat → Bool := fun bi i =>
    match f.blocks[bi]? with
    | some b =>
      match b.params[i]? with
      | some p => live.contains p
      | none => true
    | none => true
  { params := if bi == f.entry then b.params else b.params.filter live.contains
    instrs := b.instrs.filter fun i =>
      match i with
      | .const d _ => live.contains d
      | .op ds yop _ => !pureOp yop || ds.any live.contains
      | .call .. => true
    term := mapEdges (fun (e : Edge) =>
      { e with args := (e.args.zipIdx.filter fun ai => keepParam e.target ai.2).map (·.1) }) b.term }

/-- `dve` is a plain `mapIdx`: block `i` of the output is `dveBlock f i` of block
`i` of the input. -/
theorem dve_blocks_get (f : Func) (i : BlockId) :
    (dve f).blocks[i]? = (f.blocks[i]?).map (dveBlock f i) := by
  simp only [dve, Array.getElem?_mapIdx]
  rfl

theorem dve_params (f : Func) : (dve f).params = f.params := rfl
theorem dve_entry (f : Func) : (dve f).entry = f.entry := rfl
theorem dve_size (f : Func) : (dve f).blocks.size = f.blocks.size := by simp [dve]

/-! ### What the rewrite does to the liveness data -/

theorem mem_filterArgs {p : Nat → Bool} {as : List ValId} {x : ValId}
    (h : x ∈ (as.zipIdx.filter fun ai => p ai.2).map (·.1)) : x ∈ as := by
  simp only [List.mem_map, List.mem_filter] at h
  obtain ⟨ai, ⟨hmem, -⟩, rfl⟩ := h
  exact List.fst_mem_of_mem_zipIdx hmem

theorem mapEdges_uses_sub {g : Edge → Edge} (hargs : ∀ e x, x ∈ (g e).args → x ∈ e.args)
    (t : Term) {x : ValId} (h : x ∈ (mapEdges g t).uses) : x ∈ t.uses := by
  cases t with
  | jump e => exact hargs _ _ h
  | branch c t0 f0 =>
    have h' : x = c ∨ x ∈ (g t0).args ∨ x ∈ (g f0).args := by
      simpa [mapEdges, Term.uses] using h
    have h'' : x = c ∨ x ∈ t0.args ∨ x ∈ f0.args := by
      rcases h' with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl (hargs _ _ h1))
      · exact Or.inr (Or.inr (hargs _ _ h1))
    simpa [Term.uses] using h''
  | ret vs => exact h
  | halt yop as => exact h

theorem mapEdges_edges {g : Edge → Edge} (t : Term) {e : Edge}
    (h : e ∈ (mapEdges g t).edges) : ∃ e0 ∈ t.edges, g e0 = e := by
  cases t with
  | jump e0 =>
    have he : e = g e0 := by simpa [mapEdges, Term.edges] using h
    exact ⟨e0, by simp [Term.edges], he.symm⟩
  | branch c t0 f0 =>
    have he : e = g t0 ∨ e = g f0 := by simpa [mapEdges, Term.edges] using h
    rcases he with rfl | rfl
    · exact ⟨t0, by simp [Term.edges], rfl⟩
    · exact ⟨f0, by simp [Term.edges], rfl⟩
  | ret vs => simp [mapEdges, Term.edges] at h
  | halt yop as => simp [mapEdges, Term.edges] at h


/-- Uses can only shrink: `dve` deletes instructions and drops edge arguments. -/
theorem dveBlock_uses_sub {f : Func} {i : BlockId} {b : Block} {x : ValId}
    (h : x ∈ ToAsm.blockUses (dveBlock f i b)) : x ∈ ToAsm.blockUses b := by
  rw [ToAsm.mem_blockUses] at h ⊢
  rcases h with h | h
  · refine Or.inl ?_
    simp only [List.mem_flatMap] at h ⊢
    obtain ⟨ins, hins, hx⟩ := h
    exact ⟨ins, List.mem_of_mem_filter hins, hx⟩
  · refine Or.inr (mapEdges_uses_sub ?_ b.term h)
    intro e y hy
    simp only [List.mem_map, List.mem_filter] at hy
    obtain ⟨ai, ⟨hmem, -⟩, rfl⟩ := hy
    exact List.fst_mem_of_mem_zipIdx hmem

/-- Definitions can only shrink: `dve` deletes definitions, never adds one. -/
theorem dveBlock_defs_sub {f : Func} {i : BlockId} {b : Block} {x : ValId}
    (h : x ∈ ToAsm.blockDefs (dveBlock f i b)) : x ∈ ToAsm.blockDefs b := by
  rw [ToAsm.mem_blockDefs] at h ⊢
  rcases h with h | h
  · refine Or.inl ?_
    by_cases he : (i == f.entry) = true
    · simpa [dveBlock, he] using h
    · have : x ∈ b.params.filter (liveSet f).contains := by simpa [dveBlock, he] using h
      exact List.mem_of_mem_filter this
  · refine Or.inr ?_
    simp only [List.mem_flatMap] at h ⊢
    obtain ⟨ins, hins, hx⟩ := h
    exact ⟨ins, List.mem_of_mem_filter hins, hx⟩

/-- …and a **live** definition is always kept. -/
theorem dveBlock_defs_of_live {f : Func} {i : BlockId} {b : Block} {x : ValId}
    (hlive : (liveSet f).contains x = true) (h : x ∈ ToAsm.blockDefs b) :
    x ∈ ToAsm.blockDefs (dveBlock f i b) := by
  rw [ToAsm.mem_blockDefs] at h ⊢
  rcases h with h | h
  · refine Or.inl ?_
    by_cases he : (i == f.entry) = true
    · simpa [dveBlock, he] using h
    · have : x ∈ b.params.filter (liveSet f).contains := List.mem_filter.mpr ⟨h, by simpa using hlive⟩
      simpa [dveBlock, he] using this
  · refine Or.inr ?_
    simp only [List.mem_flatMap] at h ⊢
    obtain ⟨ins, hins, hx⟩ := h
    refine ⟨ins, List.mem_filter.mpr ⟨hins, ?_⟩, hx⟩
    cases ins with
    | const d v =>
      simp only [Instr.defs, List.mem_singleton] at hx
      subst hx
      simpa using hlive
    | op ds yop as =>
      simp only [Instr.defs] at hx
      by_cases hp : pureOp yop
      · simp only [hp, Bool.not_true, Bool.false_or]
        exact List.any_eq_true.mpr ⟨x, hx, hlive⟩
      · simp [hp]
    | call ds g as => simp

/-- Edge targets are untouched (only argument *positions* are dropped). -/
theorem dveBlock_edge_target {f : Func} {i : BlockId} {b : Block} {e : Edge}
    (h : e ∈ (dveBlock f i b).term.edges) : ∃ e0 ∈ b.term.edges, e0.target = e.target := by
  obtain ⟨e0, hmem, rfl⟩ := mapEdges_edges b.term h
  exact ⟨e0, hmem, rfl⟩

end Passes

/-! ## `forIn`-to-`foldl`

Every pass in `Passes.lean` is written as an `Id.run do` loop, so every
structural specification has to turn a `forIn` into something inductive. These
two lemmas do it once. The step function `g` is a *parameter* rather than
inferred, because a `match`-shaped loop body keeps its `pure` inside each branch
and so never matches the pattern `fun a b => pure (.yield (?g a b))`; the caller
supplies `g` and discharges `h` by case analysis. Pass `h` as a tactic block
(`h := by …`) so that its elaboration is postponed until `rw` has unified `body`
with the goal.

Two things worth recording for the next pass: the do-elaborator packs mutable
state in `MProd`, not `Prod`, and `dsimp only` is needed first to zeta-reduce
the `have`s that otherwise leave the loop under binders. -/

theorem Id.forIn_eq_foldl {α β : Type} {body : α → β → Id (ForInStep β)} {g : α → β → β}
    (h : ∀ a b, body a b = pure (ForInStep.yield (g a b))) (l : List α) (init : β) :
    (forIn l init body : Id β) = l.foldl (fun b a => g a b) init := by
  induction l generalizing init with
  | nil => rfl
  | cons a as ih => simp only [List.forIn_cons, h a init, List.foldl_cons]; exact ih (g a init)

theorem Id.forIn_array_eq_foldl {α β : Type} {body : α → β → Id (ForInStep β)} {g : α → β → β}
    (h : ∀ a b, body a b = pure (ForInStep.yield (g a b))) (as : Array α) (init : β) :
    (forIn as init body : Id β) = as.toList.foldl (fun b a => g a b) init := by
  rw [← Array.forIn_toList]; exact Id.forIn_eq_foldl h _ init


/-! ### Early-return loops -/

/-- The pure model of a `for` loop whose body may break: fold until a step
returns `.done`, then stop. -/
def loopWith {α β : Type} (g : α → β → ForInStep β) : List α → β → β
  | [], b => b
  | a :: as, b =>
    match g a b with
    | .yield b' => loopWith g as b'
    | .done b' => b'

@[simp] theorem loopWith_nil {α β : Type} (g : α → β → ForInStep β) (b : β) :
    loopWith g [] b = b := rfl

theorem loopWith_cons {α β : Type} (g : α → β → ForInStep β) (a : α) (as : List α) (b : β) :
    loopWith g (a :: as) b =
      match g a b with
      | .yield b' => loopWith g as b'
      | .done b' => b' := rfl

/-- **`forIn`-to-`loopWith` bridge**: the early-return counterpart of
`Id.forIn_eq_foldl`. A `for` loop in `Id` whose body may `return` is
`loopWith`. -/
theorem Id.forIn_eq_loopWith {α β : Type} {body : α → β → Id (ForInStep β)}
    {g : α → β → ForInStep β} (h : ∀ a b, body a b = pure (g a b)) (l : List α) (init : β) :
    (forIn l init body : Id β) = loopWith g l init := by
  induction l generalizing init with
  | nil => rfl
  | cons a as ih =>
    rw [List.forIn_cons, h a init, loopWith_cons]
    cases g a init with
    | yield b' => simpa using ih b'
    | done b' => rfl

theorem Id.forIn_array_eq_loopWith {α β : Type} {body : α → β → Id (ForInStep β)}
    {g : α → β → ForInStep β} (h : ∀ a b, body a b = pure (g a b)) (as : Array α) (init : β) :
    (forIn as init body : Id β) = loopWith g as.toList init := by
  rw [← Array.forIn_toList]; exact Id.forIn_eq_loopWith h _ init

/-- The yielding bridge is the special case where no step is `.done`. -/
theorem loopWith_yield {α β : Type} (g : α → β → β) (l : List α) (init : β) :
    loopWith (fun a b => ForInStep.yield (g a b)) l init = l.foldl (fun b a => g a b) init := by
  induction l generalizing init with
  | nil => rfl
  | cons a as ih => rw [loopWith_cons]; exact ih (g a init)

/-! ### The early-return protocol

`return` inside a `for` compiles to a loop whose state is
`MProd (Option ρ) σ` — an `Option` holding the returned value alongside the real
mutable state — with `.done` carrying `some result`. This example records the
shape (it is what `findTrivialParam`, `inlineOnce` and `inlineFunc` all use), so
the next application of the bridge does not have to rediscover it. -/

private example (l : List Nat) (init : MProd (Option (Option Nat)) PUnit) :
    (forIn l init (fun (x : Nat) (_ : MProd (Option (Option Nat)) PUnit) =>
        (if x > 10 then pure (ForInStep.done ⟨some (some x), PUnit.unit⟩)
         else pure (ForInStep.yield ⟨none, PUnit.unit⟩) : Id _)))
      = loopWith (fun (x : Nat) (_ : MProd (Option (Option Nat)) PUnit) =>
          if x > 10 then ForInStep.done ⟨some (some x), PUnit.unit⟩
          else ForInStep.yield ⟨none, PUnit.unit⟩) l init :=
  Id.forIn_eq_loopWith (fun x r => by split <;> rfl) l init

namespace Passes

/-! ### Pass 4's liveness loop, as folds -/

def dveLiveInstrStep (ins : Instr) (live : Std.HashSet ValId) : Std.HashSet ValId :=
  match ins with
  | .const _ _ => live
  | .op ds yop args =>
      if !pureOp yop || ds.any live.contains then
        args.foldl (fun s a => s.insert a) live
      else live
  | .call _ _ args => args.foldl (fun s a => s.insert a) live

def dveLiveTermStep (t : Term) (live : Std.HashSet ValId) : Std.HashSet ValId :=
  match t with
  | .jump _ => live
  | .branch c _ _ => live.insert c
  | .ret vs => vs.foldl (fun s a => s.insert a) live
  | .halt _ as => as.foldl (fun s a => s.insert a) live

def dveLiveEdgeStep (f : Func) (e : Edge) (live : Std.HashSet ValId) : Std.HashSet ValId :=
  match f.blocks[e.target]? with
  | none => live
  | some tb =>
      (tb.params.zip e.args).foldl (fun live pa =>
        if live.contains pa.1 then live.insert pa.2 else live) live

def dveLiveBlockStep (f : Func) (b : Block) (live : Std.HashSet ValId) : Std.HashSet ValId :=
  b.term.edges.foldl (fun live e => dveLiveEdgeStep f e live)
    (dveLiveTermStep b.term
      (b.instrs.foldl (fun live ins => dveLiveInstrStep ins live) live))

theorem dveLiveInstrLoop_eq (is : List Instr) (live : Std.HashSet ValId) :
    (forIn is live (fun ins live =>
      match ins with
      | .const _ _ => do pure (); pure (.yield live)
      | .op ds yop args =>
          if !pureOp yop || ds.any live.contains then
            do pure PUnit.unit; pure (.yield (args.foldl (fun s a => s.insert a) live))
          else do pure PUnit.unit; pure (.yield live)
      | .call _ _ args =>
          do pure PUnit.unit; pure (.yield (args.foldl (fun s a => s.insert a) live))) :
        Id (Std.HashSet ValId)) =
      pure (is.foldl (fun live ins => dveLiveInstrStep ins live) live) := by
  simp only [LawfulMonad.pure_bind]
  apply Eq.trans (Id.forIn_eq_foldl (g := dveLiveInstrStep) (h := by
    intro ins live
    cases ins with
    | const d v => rfl
    | op ds yop args => simp only [dveLiveInstrStep]; split <;> rfl
    | call ds fid args => rfl) is live)
  rfl

theorem dveLiveEdgeLoop_eq (f : Func) (es : List Edge) (live : Std.HashSet ValId) :
    (forIn es live (fun e live =>
      match f.blocks[e.target]? with
      | some tb => do
          let live ← forIn (tb.params.zip e.args) live (fun pa live =>
            if live.contains pa.1 then pure (.yield (live.insert pa.2))
            else pure (.yield live))
          pure (.yield live)
      | _ => pure (.yield live)) : Id (Std.HashSet ValId)) =
      pure (es.foldl (fun live e => dveLiveEdgeStep f e live) live) := by
  apply Eq.trans (Id.forIn_eq_foldl (g := dveLiveEdgeStep f) (h := by
    intro e live
    rcases hb : f.blocks[e.target]? with _ | tb
    · simp [dveLiveEdgeStep, hb]
    · simp only [dveLiveEdgeStep, hb]
      rw [Id.forIn_eq_foldl (g := fun pa live =>
        if live.contains pa.1 then live.insert pa.2 else live) (h := by
          intro pa (live : Std.HashSet ValId)
          split <;> rfl)]
      rfl) es live)
  rfl

theorem liveStep_eq_fold (f : Func) (live : Std.HashSet ValId) :
    liveStep f live =
      f.blocks.toList.foldl (fun live b => dveLiveBlockStep f b live) live := by
  unfold liveStep
  dsimp only
  rw [Id.forIn_array_eq_foldl (g := dveLiveBlockStep f) (h := by
    intro b live
    dsimp only [dveLiveBlockStep]
    conv_lhs =>
      congr
      · exact dveLiveInstrLoop_eq b.instrs live
    simp only [LawfulMonad.pure_bind]
    cases b.term <;>
      simp only [Term.edges, dveLiveTermStep] <;>
      (conv_lhs =>
        congr
        · exact dveLiveEdgeLoop_eq f _ _) <;>
      exact LawfulMonad.pure_bind _ _)]
  rfl

def HashSub (A B : Std.HashSet ValId) : Prop := ∀ x, x ∈ A → x ∈ B

theorem HashSub.refl (A : Std.HashSet ValId) : HashSub A A := fun _ h => h

theorem HashSub.trans {A B C : Std.HashSet ValId} (hAB : HashSub A B)
    (hBC : HashSub B C) : HashSub A C := fun x hx => hBC x (hAB x hx)

theorem fold_insert_sub (xs : List ValId) (s : Std.HashSet ValId) :
    HashSub s (xs.foldl (fun s x => s.insert x) s) := by
  induction xs generalizing s with
  | nil => exact HashSub.refl s
  | cons x xs ih =>
      exact HashSub.trans (fun y hy => Std.HashSet.mem_insert.mpr (Or.inr hy)) (ih (s.insert x))

theorem fold_sub {α : Type} {step : α → Std.HashSet ValId → Std.HashSet ValId}
    (hstep : ∀ a s, HashSub s (step a s)) (xs : List α) (s : Std.HashSet ValId) :
    HashSub s (xs.foldl (fun s a => step a s) s) := by
  induction xs generalizing s with
  | nil => exact HashSub.refl s
  | cons a xs ih => exact HashSub.trans (hstep a s) (ih (step a s))

theorem dveLiveInstrStep_inflationary (i : Instr) (s : Std.HashSet ValId) :
    HashSub s (dveLiveInstrStep i s) := by
  cases i with
  | const d v => exact HashSub.refl s
  | op ds yop args =>
      simp only [dveLiveInstrStep]
      split
      · exact fold_insert_sub args s
      · exact HashSub.refl s
  | call ds fid args => exact fold_insert_sub args s

theorem dveLiveTermStep_inflationary (t : Term) (s : Std.HashSet ValId) :
    HashSub s (dveLiveTermStep t s) := by
  cases t with
  | jump e => exact HashSub.refl s
  | branch c et ef => exact fun x hx => Std.HashSet.mem_insert.mpr (Or.inr hx)
  | ret vs => exact fold_insert_sub vs s
  | halt yop args => exact fold_insert_sub args s

theorem dveLiveEdgeStep_inflationary (f : Func) (e : Edge) (s : Std.HashSet ValId) :
    HashSub s (dveLiveEdgeStep f e s) := by
  simp only [dveLiveEdgeStep]
  split
  · exact HashSub.refl s
  · exact fold_sub (fun pa live => by
      split
      · exact fun x hx => Std.HashSet.mem_insert.mpr (Or.inr hx)
      · exact HashSub.refl live) _ s

theorem dveLiveBlockStep_inflationary (f : Func) (b : Block) (s : Std.HashSet ValId) :
    HashSub s (dveLiveBlockStep f b s) := by
  exact HashSub.trans
    (fold_sub dveLiveInstrStep_inflationary b.instrs s |>.trans
      (dveLiveTermStep_inflationary b.term _))
    (fold_sub (dveLiveEdgeStep_inflationary f) b.term.edges _)

theorem liveStep_inflationary (f : Func) (s : Std.HashSet ValId) :
    HashSub s (liveStep f s) := by
  rw [liveStep_eq_fold]
  exact fold_sub (dveLiveBlockStep_inflationary f) f.blocks.toList s

theorem hashEquiv_of_sub_size_eq {A B : Std.HashSet ValId} (hsub : HashSub A B)
    (hsize : A.size = B.size) : A.Equiv B := by
  have hnd : A.toList.Nodup :=
    (Std.HashSet.distinct_toList (m := A)).imp (by simp_all)
  have hsp : A.toList.Subperm B.toList := List.subperm_of_subset hnd (fun x hx => by
    rw [Std.HashSet.mem_toList] at hx ⊢
    exact hsub x hx)
  have hp : A.toList.Perm B.toList := hsp.perm_of_length_le (by simpa using hsize.symm.le)
  exact (Std.HashSet.equiv_iff_toList_perm).mpr hp

def HashBound (s : Std.HashSet ValId) (U : List ValId) : Prop := ∀ x, x ∈ s → x ∈ U

theorem fold_insert_bound {xs U : List ValId} {s : Std.HashSet ValId}
    (hs : HashBound s U) (hxs : ∀ x ∈ xs, x ∈ U) :
    HashBound (xs.foldl (fun s x => s.insert x) s) U := by
  induction xs generalizing s with
  | nil => exact hs
  | cons a xs ih =>
      apply ih (s := s.insert a)
      · intro x hx
        rw [Std.HashSet.mem_insert] at hx
        rcases hx with hx | hx
        · have : a = x := (beq_iff_eq).mp hx
          subst x
          exact hxs a (by simp)
        · exact hs x hx
      · exact fun x hx => hxs x (by simp [hx])

theorem fold_bound {α : Type} {step : α → Std.HashSet ValId → Std.HashSet ValId}
    {xs : List α} {U : List ValId} {s : Std.HashSet ValId}
    (hs : HashBound s U)
    (hstep : ∀ a ∈ xs, ∀ s, HashBound s U → HashBound (step a s) U) :
    HashBound (xs.foldl (fun s a => step a s) s) U := by
  induction xs generalizing s with
  | nil => exact hs
  | cons a xs ih =>
      exact ih (hstep a (by simp) s hs) (fun x hx => hstep x (by simp [hx]))

theorem snd_mem_of_mem_zip {α β : Type} {xs : List α} {ys : List β} {p : α × β}
    (h : p ∈ xs.zip ys) : p.2 ∈ ys := by
  induction xs generalizing ys with
  | nil => simp at h
  | cons x xs ih =>
      cases ys with
      | nil => simp at h
      | cons y ys =>
          simp only [List.zip_cons_cons, List.mem_cons] at h
          rcases h with rfl | h
          · simp
          · exact List.mem_cons_of_mem _ (ih h)

theorem dveLiveInstrStep_bound {i : Instr} {s : Std.HashSet ValId} {U : List ValId}
    (hs : HashBound s U) (hi : ∀ x ∈ i.uses, x ∈ U) :
    HashBound (dveLiveInstrStep i s) U := by
  cases i with
  | const d v => exact hs
  | op ds yop args =>
      simp only [dveLiveInstrStep]
      split
      · exact fold_insert_bound hs (by simpa [Instr.uses] using hi)
      · exact hs
  | call ds fid args => exact fold_insert_bound hs (by simpa [Instr.uses] using hi)

theorem dveLiveTermStep_bound {t : Term} {s : Std.HashSet ValId} {U : List ValId}
    (hs : HashBound s U) (ht : ∀ x ∈ t.uses, x ∈ U) :
    HashBound (dveLiveTermStep t s) U := by
  cases t with
  | jump e => exact hs
  | branch c et ef =>
    intro x hx
    simp only [dveLiveTermStep] at hx
    rw [Std.HashSet.mem_insert] at hx
    rcases hx with hx | hx
    · have : c = x := (beq_iff_eq).mp hx
      subst x
      exact ht c (by simp [Term.uses])
    · exact hs x hx
  | ret vs => exact fold_insert_bound hs (by simpa [Term.uses] using ht)
  | halt yop args => exact fold_insert_bound hs (by simpa [Term.uses] using ht)

theorem dveLiveEdgeStep_bound {f : Func} {e : Edge} {s : Std.HashSet ValId}
    {U : List ValId} (hs : HashBound s U) (he : ∀ x ∈ e.args, x ∈ U) :
    HashBound (dveLiveEdgeStep f e s) U := by
  simp only [dveLiveEdgeStep]
  split
  · exact hs
  · apply fold_bound hs
    intro pa hpa live hlive
    split
    · intro x hx
      rw [Std.HashSet.mem_insert] at hx
      rcases hx with hx | hx
      · have heq : pa.2 = x := (beq_iff_eq).mp hx
        rw [← heq]
        exact he pa.2 (snd_mem_of_mem_zip hpa)
      · exact hlive x hx
    · exact hlive

theorem edge_args_mem_term_uses {t : Term} {e : Edge} (he : e ∈ t.edges)
    {x : ValId} (hx : x ∈ e.args) : x ∈ t.uses := by
  cases t with
  | jump e' =>
      simp only [Term.edges, List.mem_singleton] at he
      subst e
      exact hx
  | branch c et ef =>
      simp [Term.edges] at he
      rcases he with rfl | rfl
      · simp [Term.uses, hx]
      · simp [Term.uses, hx]
  | ret vs => simp [Term.edges] at he
  | halt yop args => simp [Term.edges] at he

theorem dveLiveBlockStep_bound {f : Func} {b : Block} {s : Std.HashSet ValId}
    {U : List ValId} (hs : HashBound s U)
    (hi : ∀ i ∈ b.instrs, ∀ x ∈ i.uses, x ∈ U)
    (ht : ∀ x ∈ b.term.uses, x ∈ U) : HashBound (dveLiveBlockStep f b s) U := by
  have hiBound : HashBound
      (b.instrs.foldl (fun live i => dveLiveInstrStep i live) s) U :=
    fold_bound hs (by
      intro i him live hlive
      exact dveLiveInstrStep_bound hlive (hi i him))
  have htBound := dveLiveTermStep_bound hiBound ht
  apply fold_bound htBound
  intro e he live hlive
  apply dveLiveEdgeStep_bound hlive
  intro x hx
  exact ht x (edge_args_mem_term_uses he hx)

theorem liveStep_bound {f : Func} {s : Std.HashSet ValId}
    (hs : HashBound s f.allUses) : HashBound (liveStep f s) f.allUses := by
  rw [liveStep_eq_fold]
  apply fold_bound hs
  intro b hb live hlive
  apply dveLiveBlockStep_bound hlive
  · intro i hi x hx
    simp only [Func.allUses, List.mem_flatMap]
    exact ⟨b, hb, List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr ⟨i, hi, hx⟩))⟩
  · intro x hx
    simp only [Func.allUses, List.mem_flatMap]
    exact ⟨b, hb, List.mem_append.mpr (Or.inr hx)⟩

theorem hashSize_le_of_bound {s : Std.HashSet ValId} {U : List ValId}
    (h : HashBound s U) : s.size ≤ U.length := by
  rw [← Std.HashSet.length_toList]
  exact (List.subperm_of_subset
    ((Std.HashSet.distinct_toList (m := s)).imp (by simp_all))
    (fun x hx => h x (Std.HashSet.mem_toList.mp hx))).length_le

def dveFuel (f : Func) : Nat :=
  f.blocks.foldl (init := f.allDefs.length + 2) fun n b =>
    n + b.instrs.foldl (fun m i => m + i.uses.length) b.term.uses.length

abbrev DVELoopState := MProd (Option (Std.HashSet ValId)) (Std.HashSet ValId)

def dveLoopStep (f : Func) (_ : Nat) (r : DVELoopState) : ForInStep DVELoopState :=
  let next := liveStep f r.2
  if next.size == r.2.size then .done ⟨some r.2, r.2⟩
  else .yield ⟨none, next⟩

def dveLoopResult (r : DVELoopState) : Std.HashSet ValId := r.1.getD r.2

theorem dveLoopFinish_eq (r : Id DVELoopState) :
    Id.run (do
      let s ← r
      match s.1 with
      | none => do
          pure PUnit.unit
          pure s.2
      | some live => pure live) = dveLoopResult (Id.run r) := by
  change (match r.1 with | none => r.2 | some live => live) = r.1.getD r.2
  cases r.1 <;> rfl

theorem liveSet_eq_loop (f : Func) :
    liveSet f = dveLoopResult
      (loopWith (dveLoopStep f) (List.range' 0 (dveFuel f) 1) ⟨none, ∅⟩) := by
  unfold liveSet
  dsimp only [dveFuel]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  rw [Id.forIn_eq_loopWith (g := dveLoopStep f) (h := by
    intro i r
    simp only [dveLoopStep]
    split <;> rfl)]
  dsimp only [Id.run, Id.instMonad, Id.hasBind]
  simp only [Std.Legacy.Range.size, dveLoopResult]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  exact dveLoopFinish_eq
    (loopWith (dveLoopStep f) (List.range' 0 (dveFuel f) 1) ⟨none, ∅⟩)

theorem instrUseFuel_eq (is : List Instr) (n : Nat) :
    is.foldl (fun m i => m + i.uses.length) n =
      n + (is.flatMap Instr.uses).length := by
  induction is generalizing n with
  | nil => simp
  | cons i is ih =>
      rw [List.foldl_cons, ih]
      simp only [List.flatMap_cons, List.length_append]
      omega

theorem blockUseFuel_eq (bs : List Block) (n : Nat) :
    bs.foldl (fun n b =>
        n + b.instrs.foldl (fun m i => m + i.uses.length) b.term.uses.length) n =
      n + (bs.flatMap fun b => b.instrs.flatMap Instr.uses ++ b.term.uses).length := by
  induction bs generalizing n with
  | nil => simp
  | cons b bs ih =>
      rw [List.foldl_cons, instrUseFuel_eq, ih]
      simp only [List.flatMap_cons, List.length_append]
      omega

theorem dveFuel_eq (f : Func) : dveFuel f = f.allDefs.length + 2 + f.allUses.length := by
  simp only [dveFuel, ← Array.foldl_toList, blockUseFuel_eq, Func.allUses]

theorem dveLoop_closed (f : Func) :
    ∀ (l : List Nat) (cur : Std.HashSet ValId),
      HashBound cur f.allUses → f.allUses.length < cur.size + l.length →
      ∃ live, (loopWith (dveLoopStep f) l ⟨none, cur⟩).1 = some live ∧
        live.Equiv (liveStep f live) := by
  intro l
  induction l with
  | nil =>
      intro cur hbound hfuel
      have := hashSize_le_of_bound hbound
      simp at hfuel
      omega
  | cons i is ih =>
      intro cur hbound hfuel
      rw [loopWith_cons]
      by_cases hsize : ((liveStep f cur).size == cur.size) = true
      · rw [show dveLoopStep f i ⟨none, cur⟩ = .done ⟨some cur, cur⟩ by
          simp [dveLoopStep, hsize]]
        refine ⟨cur, rfl, hashEquiv_of_sub_size_eq (liveStep_inflationary f cur) ?_⟩
        exact (beq_iff_eq).mp hsize |>.symm
      · have hsize' : ((liveStep f cur).size == cur.size) = false :=
          Bool.eq_false_of_not_eq_true hsize
        rw [show dveLoopStep f i ⟨none, cur⟩ = .yield ⟨none, liveStep f cur⟩ by
          simp [dveLoopStep, hsize']]
        have hle : cur.size ≤ (liveStep f cur).size := by
          have h := (List.subperm_of_subset
            ((Std.HashSet.distinct_toList (m := cur)).imp (by simp_all))
            (fun x hx => by
              rw [Std.HashSet.mem_toList] at hx ⊢
              exact liveStep_inflationary f cur x hx)).length_le
          simpa using h
        have hlt : cur.size < (liveStep f cur).size := by
          have hne : (liveStep f cur).size ≠ cur.size := by
            intro h
            exact hsize (by simpa [h])
          omega
        exact ih (liveStep f cur) (liveStep_bound hbound) (by simp only [List.length_cons] at hfuel ⊢; omega)

theorem liveSet_closed (f : Func) : (liveSet f).Equiv (liveStep f (liveSet f)) := by
  rw [liveSet_eq_loop]
  obtain ⟨live, hlive, hclosed⟩ := dveLoop_closed f (List.range' 0 (dveFuel f) 1) ∅
    (by intro x hx; simp at hx) (by simp [dveFuel_eq])
  have hresult : dveLoopResult
      (loopWith (dveLoopStep f) (List.range' 0 (dveFuel f) 1) ⟨none, ∅⟩) = live := by
    simp only [dveLoopResult]
    rw [hlive]
    rfl
  rw [hresult]
  exact hclosed

theorem liveSet_mem_step_iff {f : Func} {x : ValId} :
    x ∈ liveStep f (liveSet f) ↔ x ∈ liveSet f :=
  (liveSet_closed f).mem_iff.symm

theorem mem_fold_insert_of_mem {xs : List ValId} {s : Std.HashSet ValId} {x : ValId}
    (hx : x ∈ xs) : x ∈ xs.foldl (fun s a => s.insert a) s := by
  induction xs generalizing s with
  | nil => simp at hx
  | cons a as ih =>
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hx with hx | hx
      · subst x
        exact fold_insert_sub as (s.insert a) a
          (Std.HashSet.mem_insert.mpr (Or.inl (beq_iff_eq.mpr rfl)))
      · exact ih hx

/-- If a selected fold step puts `x` in the accumulator whenever the
accumulator contains `base`, then the complete inflationary fold contains
`x`. -/
theorem mem_fold_of_selected_step {alpha : Type}
    {step : alpha → Std.HashSet ValId → Std.HashSet ValId}
    (hinfl : ∀ a s, HashSub s (step a s)) {base s : Std.HashSet ValId}
    (hbase : HashSub base s) {xs : List alpha} {a : alpha} (ha : a ∈ xs)
    {x : ValId} (hstep : ∀ s, HashSub base s → x ∈ step a s) :
    x ∈ xs.foldl (fun s a => step a s) s := by
  induction xs generalizing s with
  | nil => simp at ha
  | cons b bs ih =>
      rw [List.foldl_cons]
      rcases List.mem_cons.mp ha with rfl | ha
      · exact fold_sub hinfl bs (step a s) x (hstep s hbase)
      · exact ih (HashSub.trans hbase (hinfl b s)) ha

def dveKeepInstr (live : Std.HashSet ValId) : Instr → Bool
  | .const d _ => live.contains d
  | .op ds yop _ => !pureOp yop || ds.any live.contains
  | .call .. => true

theorem dveLiveInstrStep_mem_use {live s : Std.HashSet ValId}
    (hsub : HashSub live s) {i : Instr}
    (hkeep : dveKeepInstr live i = true) {x : ValId} (hx : x ∈ i.uses) :
    x ∈ dveLiveInstrStep i s := by
  cases i with
  | const d v => simp [Instr.uses] at hx
  | op ds yop args =>
      simp only [dveKeepInstr] at hkeep
      simp only [Instr.uses] at hx
      simp only [dveLiveInstrStep]
      have hk : (!pureOp yop || ds.any s.contains) = true := by
        simp only [Bool.or_eq_true] at hkeep ⊢
        rcases hkeep with hp | hd
        · exact Or.inl hp
        · obtain ⟨d, hd, hdlive⟩ := List.any_eq_true.mp hd
          exact Or.inr (List.any_eq_true.mpr
            ⟨d, hd, Std.HashSet.mem_iff_contains.mp (hsub d
              (Std.HashSet.contains_iff_mem.mp hdlive))⟩)
      rw [if_pos hk]
      exact mem_fold_insert_of_mem hx
  | call ds fid args =>
      exact mem_fold_insert_of_mem (by simpa [Instr.uses] using hx)

theorem wfCheck_edge_arity {f : Func} {n : Nat} (hwf : f.wfCheck n = true)
    {b : Block} (hb : b ∈ f.blocks.toList) {e : Edge} (he : e ∈ b.term.edges) :
    ∃ tb, f.blocks[e.target]? = some tb ∧ e.args.length = tb.params.length := by
  unfold Func.wfCheck at hwf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hwf
  have hb' : b ∈ f.blocks := by simpa using hb
  have hblock := Array.all_eq_true_iff_forall_mem.mp hwf.2 b hb'
  simp only [Bool.and_eq_true] at hblock
  have hedge := List.all_eq_true.mp hblock.1.2 e he
  cases hopt : f.blocks[e.target]? with
  | none => simp [hopt] at hedge
  | some tb =>
      refine ⟨tb, rfl, ?_⟩
      simpa [hopt] using hedge

/-- Under the edge-arity invariant, an argument retained by DVE is propagated
by the forward liveness step from its live target parameter. -/
theorem dveLiveEdgeStep_mem_filtered {f : Func} {e : Edge} {tb : Block}
    (htb : f.blocks[e.target]? = some tb) (hlen : e.args.length = tb.params.length)
    {s : Std.HashSet ValId} (hsub : HashSub (liveSet f) s)
    {x : ValId}
    (hx : x ∈ (e.args.zipIdx.filter fun ai =>
      match tb.params[ai.2]? with
      | some p => (liveSet f).contains p
      | none => true).map (fun ai => ai.1)) :
    x ∈ dveLiveEdgeStep f e s := by
  simp only [List.mem_map, List.mem_filter] at hx
  obtain ⟨ai, ⟨hai, hkeep⟩, haix⟩ := hx
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hai
  have hiArgs : i < e.args.length := by simpa using hi
  have hpair : ai = (e.args[i], i) := by
    rw [← hget, List.getElem_zipIdx hi]
    simp
  have hxarg : e.args[i] = x := by simpa [hpair] using haix
  have hiParams : i < tb.params.length := by omega
  have hparam : tb.params[i]? = some tb.params[i] := List.getElem?_eq_getElem hiParams
  have hpLive : tb.params[i] ∈ liveSet f := by
    rw [hpair, hparam] at hkeep
    exact Std.HashSet.contains_iff_mem.mp hkeep
  have hpai : (tb.params[i], x) ∈ tb.params.zip e.args := by
    rw [List.mem_iff_getElem]
    refine ⟨i, ?_, ?_⟩
    · simp only [List.length_zip]
      omega
    · rw [List.getElem_zip]
      simp [hxarg]
  simp only [dveLiveEdgeStep, htb]
  apply mem_fold_of_selected_step
    (fun pa s => by
      split
      · exact fun y hy => Std.HashSet.mem_insert.mpr (Or.inr hy)
      · exact HashSub.refl s)
    hsub hpai
  intro s hs
  have hpS : tb.params[i] ∈ s := hs _ hpLive
  rw [if_pos (Std.HashSet.mem_iff_contains.mp hpS)]
  exact Std.HashSet.mem_insert.mpr (Or.inl (by simp))

theorem dveLiveBlockStep_mem_term {f : Func} {n : Nat} (hwf : f.wfCheck n = true)
    {bi : BlockId} {b : Block} (hb : f.blocks[bi]? = some b)
    {s : Std.HashSet ValId} (hsub : HashSub (liveSet f) s) {x : ValId}
    (hx : x ∈ (dveBlock f bi b).term.uses) :
    x ∈ b.term.edges.foldl (fun s e => dveLiveEdgeStep f e s)
      (dveLiveTermStep b.term s) := by
  have hbmem : b ∈ f.blocks.toList := by
    obtain ⟨hlt, hget⟩ := Array.getElem?_eq_some_iff.mp hb
    exact List.mem_iff_getElem.mpr ⟨bi, by simpa using hlt, by simpa using hget⟩
  cases hterm : b.term with
  | jump e =>
      simp only [dveBlock, hterm, mapEdges, Term.uses] at hx
      obtain ⟨tb, htb, hlen⟩ := wfCheck_edge_arity hwf hbmem (e := e)
        (by simp [hterm, Term.edges])
      simp only [htb] at hx
      simpa [hterm, Term.edges, dveLiveTermStep] using
        dveLiveEdgeStep_mem_filtered htb hlen hsub hx
  | branch c et ef =>
      simp only [dveBlock, hterm, mapEdges, Term.uses, List.mem_cons, List.mem_append] at hx
      rcases hx with hxct | hxf
      · rcases hxct with hxc | hxt
        · subst x
          simpa [hterm, Term.edges, dveLiveTermStep] using
            fold_sub (dveLiveEdgeStep_inflationary f) [et, ef] (s.insert c) c
            (Std.HashSet.mem_insert.mpr (Or.inl (by simp)))
        · obtain ⟨tb, htb, hlen⟩ := wfCheck_edge_arity hwf hbmem (e := et)
            (by simp [hterm, Term.edges])
          simp only [htb] at hxt
          simp only [hterm, Term.edges, dveLiveTermStep]
          apply mem_fold_of_selected_step (dveLiveEdgeStep_inflationary f)
            (HashSub.trans hsub (dveLiveTermStep_inflationary (.branch c et ef) s))
            (xs := [et, ef]) (a := et) (by simp)
          intro s' hs'
          exact dveLiveEdgeStep_mem_filtered htb hlen hs' hxt
      · obtain ⟨tb, htb, hlen⟩ := wfCheck_edge_arity hwf hbmem (e := ef)
          (by simp [hterm, Term.edges])
        simp only [htb] at hxf
        simp only [hterm, Term.edges, dveLiveTermStep]
        apply mem_fold_of_selected_step (dveLiveEdgeStep_inflationary f)
          (HashSub.trans hsub (dveLiveTermStep_inflationary (.branch c et ef) s))
          (xs := [et, ef]) (a := ef) (by simp)
        intro s' hs'
        exact dveLiveEdgeStep_mem_filtered htb hlen hs' hxf
  | ret vs =>
      simpa [hterm, Term.edges, dveLiveTermStep] using
        mem_fold_insert_of_mem (by simpa [dveBlock, hterm, mapEdges, Term.uses] using hx)
  | halt yop as =>
      simpa [hterm, Term.edges, dveLiveTermStep] using
        mem_fold_insert_of_mem (by simpa [dveBlock, hterm, mapEdges, Term.uses] using hx)

theorem dveBlock_instr_keep {f : Func} {bi : BlockId} {b : Block} {i : Instr}
    (h : i ∈ (dveBlock f bi b).instrs) :
    dveKeepInstr (liveSet f) i = true := by
  change i ∈ b.instrs.filter (dveKeepInstr (liveSet f)) at h
  exact (List.mem_filter.mp h).2

/-- Every value read by the DVE output is in the closed forward live set.  The
well-formedness premise is used only for positional edge-argument alignment. -/
theorem dveBlock_uses_live {f : Func} {n : Nat} (hwf : f.wfCheck n = true)
    {bi : BlockId} {b : Block} (hb : f.blocks[bi]? = some b) {x : ValId}
    (hx : x ∈ ToAsm.blockUses (dveBlock f bi b)) : x ∈ liveSet f := by
  apply liveSet_mem_step_iff.mp
  rw [liveStep_eq_fold]
  have hbmem : b ∈ f.blocks.toList := by
    obtain ⟨hlt, hget⟩ := Array.getElem?_eq_some_iff.mp hb
    exact List.mem_iff_getElem.mpr ⟨bi, by simpa using hlt, by simpa using hget⟩
  apply mem_fold_of_selected_step (dveLiveBlockStep_inflationary f)
    (HashSub.refl (liveSet f)) hbmem
  intro s hsub
  rw [ToAsm.mem_blockUses] at hx
  rcases hx with hi | ht
  · simp only [List.mem_flatMap] at hi
    obtain ⟨ins, hins, huse⟩ := hi
    have hins' : ins ∈ b.instrs := List.mem_of_mem_filter hins
    have hkeep : dveKeepInstr (liveSet f) ins = true := dveBlock_instr_keep hins
    have hinner : x ∈ b.instrs.foldl (fun s i => dveLiveInstrStep i s) s := by
      apply mem_fold_of_selected_step dveLiveInstrStep_inflationary hsub hins'
      intro s' hs'
      exact dveLiveInstrStep_mem_use hs' hkeep huse
    exact fold_sub (dveLiveEdgeStep_inflationary f) b.term.edges _ x
      (dveLiveTermStep_inflationary b.term _ x hinner)
  · exact dveLiveBlockStep_mem_term hwf hb
      (HashSub.trans hsub (fold_sub dveLiveInstrStep_inflationary b.instrs s)) ht

/-! ### Pass 2's loop, as a fold -/

abbrev CFInner := MProd (Std.HashMap ValId U256) (List Instr)
abbrev CFOuter := MProd (Array Block) (Std.HashMap ValId U256)

/-- The instruction step of `constFold`'s inner loop. -/
def cfInstrStep (ins : Instr) (st : CFInner) : CFInner :=
  match ins with
  | .const d v => ⟨st.1.insert d v, .const d v :: st.2⟩
  | .op [d] yop args =>
    match (if pureOp yop then
            (match args.mapM (st.1[·]?) with
             | some vs => evalPure yop vs
             | none => none)
           else none) with
    | some v => ⟨st.1.insert d v, .const d v :: st.2⟩
    | none => ⟨st.1, .op [d] yop args :: st.2⟩
  | ins => ⟨st.1, ins :: st.2⟩

/-- The block step of `constFold`'s outer loop, with the inner loop already
expressed as a fold. -/
def cfTerm (b : Block) (m : Std.HashMap ValId U256) : Term :=
  match b.term with
  | .branch c t e =>
    match m[c]? with
    | some v => .jump (if v == 0 then e else t)
    | none => b.term
  | t => t

def cfBlockStep (b : Block) (st : CFOuter) : CFOuter :=
  let r := b.instrs.foldl (fun s i => cfInstrStep i s) ⟨st.2, []⟩
  ⟨st.1.push { b with instrs := r.2.reverse, term := cfTerm b r.1 }, r.1⟩

/-- **`constFold`'s loop, as a fold.** The `do`-block's mutable state is an
`MProd`, and both loop bodies are pure-`yield`, so the bridge applies twice:
once under the outer body's binder (for the instruction loop) and once at the
top level. -/
theorem constFold_blocks_eq (f : Func) :
    (constFold f).blocks = (f.blocks.toList.foldl (fun st b => cfBlockStep b st) ⟨#[], ∅⟩).1 := by
  unfold constFold
  dsimp only
  rw [Id.forIn_array_eq_foldl (g := cfBlockStep) (h := by
    intro b st
    dsimp only [cfBlockStep]
    rw [Id.forIn_eq_foldl (g := cfInstrStep) (h := by
      intro i s
      cases i with
      | const d v => rfl
      | op ds yop args =>
        cases ds with
        | nil => rfl
        | cons d rest => cases rest with
          | nil =>
            simp only [cfInstrStep]
            split <;> split <;> grind
          | cons e es => rfl
      | call ds fid args => rfl)]
    rfl)]
  rfl


/-- One instruction step conses a *replacement* with the same definitions and no
new uses. -/
theorem cfInstrStep_cons (i : Instr) (s : CFInner) :
    ∃ i', (cfInstrStep i s).2 = i' :: s.2 ∧ i'.defs = i.defs ∧ (∀ x ∈ i'.uses, x ∈ i.uses) := by
  cases i with
  | const d v => exact ⟨_, rfl, rfl, fun x hx => hx⟩
  | op ds yop args =>
    cases ds with
    | nil => exact ⟨_, rfl, rfl, fun x hx => hx⟩
    | cons d rest =>
      cases rest with
      | nil =>
        simp only [cfInstrStep]
        split
        · exact ⟨_, rfl, rfl, by simp [Instr.uses]⟩
        · exact ⟨_, rfl, rfl, fun x hx => hx⟩
      | cons e es => exact ⟨_, rfl, rfl, fun x hx => hx⟩
  | call ds fid args => exact ⟨_, rfl, rfl, fun x hx => hx⟩

/-- The instruction fold preserves definitions and never invents a use. -/
theorem cfInstr_fold (l : List Instr) (s : CFInner) :
    (∀ x, x ∈ (l.foldl (fun s i => cfInstrStep i s) s).2.flatMap Instr.defs ↔
        x ∈ s.2.flatMap Instr.defs ∨ x ∈ l.flatMap Instr.defs)
    ∧ (∀ x, x ∈ (l.foldl (fun s i => cfInstrStep i s) s).2.flatMap Instr.uses →
        x ∈ s.2.flatMap Instr.uses ∨ x ∈ l.flatMap Instr.uses) := by
  induction l generalizing s with
  | nil => simp
  | cons i is ih =>
    obtain ⟨i', hi', hdefs, huses⟩ := cfInstrStep_cons i s
    have hstep : (List.foldl (fun s i => cfInstrStep i s) s (i :: is))
        = List.foldl (fun s i => cfInstrStep i s) (cfInstrStep i s) is := rfl
    rw [hstep]
    obtain ⟨ihd, ihu⟩ := ih (cfInstrStep i s)
    constructor
    · intro x
      rw [ihd x, hi']
      simp only [List.flatMap_cons, List.mem_append, hdefs]
      tauto
    · intro x hx
      rcases ihu x hx with h | h
      · rw [hi'] at h
        simp only [List.flatMap_cons, List.mem_append] at h ⊢
        rcases h with h | h
        · exact Or.inr (Or.inl (huses x h))
        · exact Or.inl h
      · simp only [List.flatMap_cons, List.mem_append] at h ⊢
        exact Or.inr (Or.inr h)


/-- The relation `constFold` establishes between a source block and its rewrite;
exactly the hypothesis shape of `ToAsm.domCheck_of_shrinking`. -/
def CFRel (b b' : Block) : Prop :=
  (∀ x ∈ ToAsm.blockUses b', x ∈ ToAsm.blockUses b)
  ∧ (∀ x ∈ ToAsm.blockDefs b, x ∈ ToAsm.blockDefs b')
  ∧ (∀ e ∈ b'.term.edges, ∃ e0 ∈ b.term.edges, e0.target = e.target)

theorem mem_flatMap_reverse {α β} [BEq β] {l : List α} {f : α → List β} {x : β} :
    x ∈ l.reverse.flatMap f ↔ x ∈ l.flatMap f := by
  simp only [List.mem_flatMap, List.mem_reverse]

/-! ### The terminator rewrite, one constructor at a time -/

theorem cfTerm_jump (b : Block) (m : Std.HashMap ValId U256) {e : Edge} (hb : b.term = .jump e) :
    cfTerm b m = b.term := by simp only [cfTerm, hb]

theorem cfTerm_ret (b : Block) (m : Std.HashMap ValId U256) {vs : List ValId}
    (hb : b.term = .ret vs) : cfTerm b m = b.term := by simp only [cfTerm, hb]

theorem cfTerm_halt (b : Block) (m : Std.HashMap ValId U256) {yop : Op} {as : List ValId}
    (hb : b.term = .halt yop as) : cfTerm b m = b.term := by simp only [cfTerm, hb]

theorem cfTerm_branch (b : Block) (m : Std.HashMap ValId U256) {c : ValId} {t e : Edge}
    (hb : b.term = .branch c t e) :
    cfTerm b m = b.term ∨ cfTerm b m = .jump t ∨ cfTerm b m = .jump e := by
  simp only [cfTerm, hb]
  split
  · rename_i v _
    by_cases hv : (v == 0) = true
    · exact Or.inr (Or.inr (by rw [if_pos hv]))
    · exact Or.inr (Or.inl (by rw [if_neg hv]))
  · exact Or.inl rfl

/-- Constant folding either leaves a terminator alone or replaces a `branch` by a
`jump` along one of its own edges. -/
theorem cfTerm_cases (b : Block) (m : Std.HashMap ValId U256) :
    cfTerm b m = b.term ∨ ∃ e0 ∈ b.term.edges, cfTerm b m = .jump e0 := by
  rcases hb : b.term with e | ⟨c, t, e⟩ | vs | ⟨yop, as⟩
  · exact Or.inl ((cfTerm_jump b m hb).trans hb)
  · rcases cfTerm_branch b m hb with h | h | h
    · exact Or.inl (h.trans hb)
    · exact Or.inr ⟨t, by simp [Term.edges], h⟩
    · exact Or.inr ⟨e, by simp [Term.edges], h⟩
  · exact Or.inl ((cfTerm_ret b m hb).trans hb)
  · exact Or.inl ((cfTerm_halt b m hb).trans hb)

theorem cfTerm_uses (b : Block) (m : Std.HashMap ValId U256) {x : ValId}
    (hx : x ∈ (cfTerm b m).uses) : x ∈ b.term.uses := by
  rcases cfTerm_cases b m with h | ⟨e0, he0, h⟩
  · rwa [h] at hx
  · rw [h] at hx
    simp only [Term.uses] at hx
    rcases hb : b.term with e | ⟨c, t, e⟩ | vs | ⟨yop, as⟩ <;> rw [hb] at he0 <;>
      simp only [Term.edges, List.mem_cons] at he0 <;>
      simp only [Term.uses, List.mem_cons, List.mem_append] <;> grind

theorem cfTerm_edges (b : Block) (m : Std.HashMap ValId U256) {e : Edge}
    (he : e ∈ (cfTerm b m).edges) : ∃ e0 ∈ b.term.edges, e0.target = e.target := by
  rcases cfTerm_cases b m with h | ⟨e0, he0, h⟩
  · rw [h] at he; exact ⟨e, he, rfl⟩
  · rw [h] at he
    simp only [Term.edges, List.mem_singleton] at he
    exact ⟨e0, he0, by rw [he]⟩


/-! ### Pass 2's step-by-step correspondence -/

/-- The constant map after one folded instruction. -/
def cfInstrMap (i : Instr) (m : Std.HashMap ValId U256) : Std.HashMap ValId U256 :=
  match i with
  | .const d v => m.insert d v
  | .op [d] yop args =>
    match (if pureOp yop then
            (match args.mapM (m[·]?) with
             | some vs => evalPure yop vs
             | none => none)
           else none) with
    | some v => m.insert d v
    | none => m
  | _ => m

/-- The instruction `constFold` emits for one source instruction. -/
def cfInstrOut (i : Instr) (m : Std.HashMap ValId U256) : Instr :=
  match i with
  | .const d v => .const d v
  | .op [d] yop args =>
    match (if pureOp yop then
            (match args.mapM (m[·]?) with
             | some vs => evalPure yop vs
             | none => none)
           else none) with
    | some v => .const d v
    | none => .op [d] yop args
  | i => i

/-- **The step-by-step correspondence**: one fold step updates the map and
conses one rewritten instruction, both determined by the *incoming map alone*. -/
theorem cfInstrStep_eq (i : Instr) (m : Std.HashMap ValId U256) (acc : List Instr) :
    cfInstrStep i ⟨m, acc⟩ = ⟨cfInstrMap i m, cfInstrOut i m :: acc⟩ := by
  cases i with
  | const d v => rfl
  | op ds yop args =>
    cases ds with
    | nil => rfl
    | cons d rest =>
      cases rest with
      | nil =>
        simp only [cfInstrStep, cfInstrMap, cfInstrOut]
        split <;> (try split) <;> grind
      | cons e es => rfl
  | call ds fid args => rfl

/-- The accumulator only ever grows at the front, so a fold started from `acc`
is the fold started from `[]`, appended. -/
theorem cfInstr_fold_split (l : List Instr) (m : Std.HashMap ValId U256) (acc : List Instr) :
    (l.foldl (fun s i => cfInstrStep i s) ⟨m, acc⟩).2
      = (l.foldl (fun s i => cfInstrStep i s) ⟨m, []⟩).2 ++ acc := by
  induction l generalizing m acc with
  | nil => rfl
  | cons i is ih =>
    have hstep : ∀ a : List Instr,
        (List.foldl (fun s i => cfInstrStep i s) ⟨m, a⟩ (i :: is))
          = List.foldl (fun s i => cfInstrStep i s) ⟨cfInstrMap i m, cfInstrOut i m :: a⟩ is := by
      intro a; rw [List.foldl_cons, cfInstrStep_eq]
    rw [hstep acc, hstep [], ih (cfInstrMap i m) (cfInstrOut i m :: acc),
      ih (cfInstrMap i m) [cfInstrOut i m]]
    simp

/-- The block's rewritten instruction list, one step at a time: the head is the
rewrite of the head under the incoming map, and the tail is the rewrite of the
tail under the *updated* map. This is the shape a simulation over `Exec`
consumes. -/
theorem cfInstr_fold_cons (i : Instr) (is : List Instr) (m : Std.HashMap ValId U256) :
    ((i :: is).foldl (fun s i => cfInstrStep i s) ⟨m, []⟩).2.reverse
      = cfInstrOut i m ::
        (is.foldl (fun s i => cfInstrStep i s) ⟨cfInstrMap i m, []⟩).2.reverse := by
  rw [List.foldl_cons, cfInstrStep_eq, cfInstr_fold_split]
  simp

/-- The empty case. -/
theorem cfInstr_fold_nil (m : Std.HashMap ValId U256) :
    (([] : List Instr).foldl (fun s i => cfInstrStep i s) ⟨m, []⟩).2.reverse = [] := rfl

/-- The map after a fold, step by step. -/
theorem cfInstr_foldMap_cons (i : Instr) (is : List Instr) (m : Std.HashMap ValId U256) :
    ((i :: is).foldl (fun s i => cfInstrStep i s) ⟨m, []⟩).1
      = (is.foldl (fun s i => cfInstrStep i s) ⟨cfInstrMap i m, []⟩).1 := by
  rw [List.foldl_cons, cfInstrStep_eq]
  have : ∀ (a : List Instr) (m' : Std.HashMap ValId U256),
      (is.foldl (fun s i => cfInstrStep i s) ⟨m', a⟩).1
        = (is.foldl (fun s i => cfInstrStep i s) ⟨m', []⟩).1 := by
    intro a m'
    induction is generalizing m' a with
    | nil => rfl
    | cons j js ih => rw [List.foldl_cons, List.foldl_cons, cfInstrStep_eq, cfInstrStep_eq,
        ih (cfInstrOut j m' :: a) (cfInstrMap j m'), ih [cfInstrOut j m'] (cfInstrMap j m')]
  exact this _ _

/-- A fold step can only change the lookup of an instruction destination. -/
theorem cfInstrMap_get_of_not_def (i : Instr) (m : Std.HashMap ValId U256) {d : ValId}
    (hd : d ∉ i.defs) : (cfInstrMap i m)[d]? = m[d]? := by
  cases i with
  | const x v =>
    simp only [Instr.defs, List.mem_singleton] at hd
    have hxd : (x == d) = false := by simp [Ne.symm hd]
    simp [cfInstrMap, Std.HashMap.getElem?_insert, hxd]
  | op ds yop args =>
    cases ds with
    | nil => rfl
    | cons x xs =>
      cases xs with
      | nil =>
        simp only [Instr.defs, List.mem_singleton] at hd
        simp only [cfInstrMap]
        split
        · have hxd : (x == d) = false := by simp [Ne.symm hd]
          simp [Std.HashMap.getElem?_insert, hxd]
        · rfl
      | cons y ys => rfl
  | call ds fid args => rfl

/-- If a lookup appears in one step from an absent input lookup, the
instruction defines that key. -/
theorem cfInstrMap_def_of_get (i : Instr) (m : Std.HashMap ValId U256) {d : ValId} {v : U256}
    (h0 : m[d]? = none) (h : (cfInstrMap i m)[d]? = some v) : d ∈ i.defs := by
  by_contra hd
  rw [cfInstrMap_get_of_not_def i m hd, h0] at h
  simp at h

/-- A whole instruction fold preserves a lookup when none of its instructions
defines the key. -/
theorem cfInstr_foldMap_get_of_not_def (l : List Instr) (m : Std.HashMap ValId U256)
    {d : ValId} (hd : d ∉ l.flatMap Instr.defs) :
    (l.foldl (fun s i => cfInstrStep i s) ⟨m, []⟩).1[d]? = m[d]? := by
  induction l generalizing m with
  | nil => rfl
  | cons i is ih =>
    simp only [List.flatMap_cons, List.mem_append, not_or] at hd
    have hacc := cfInstr_foldMap_cons i is m
    rw [List.foldl_cons, cfInstrStep_eq] at hacc
    rw [List.foldl_cons, cfInstrStep_eq, hacc, ih (cfInstrMap i m) hd.2,
      cfInstrMap_get_of_not_def i m hd.1]

/-- Every key in a fold map either came from the incoming map or is defined by
one of the folded instructions. -/
theorem cfInstr_foldMap_domain (l : List Instr) (m : Std.HashMap ValId U256)
    {d : ValId} {v : U256}
    (h : (l.foldl (fun s i => cfInstrStep i s) ⟨m, []⟩).1[d]? = some v) :
    (∃ w, m[d]? = some w) ∨ d ∈ l.flatMap Instr.defs := by
  by_cases h0 : m[d]? = none
  · right
    by_contra hd
    rw [cfInstr_foldMap_get_of_not_def l m hd, h0] at h
    simp at h
  · left
    exact Option.ne_none_iff_exists'.mp h0

/-- Instruction definitions, flattened out of the blocks, form a sublist of
`allDefs`. -/
theorem instrDefs_sublist_allDefs (f : Func) :
    (f.blocks.toList.flatMap fun b => b.instrs.flatMap Instr.defs).Sublist f.allDefs := by
  rw [allDefs_eq]
  apply List.Sublist.trans _ (List.sublist_append_right f.params _)
  induction f.blocks.toList with
  | nil => exact .slnil
  | cons b bs ih =>
    simp only [List.flatMap_cons]
    exact List.Sublist.append (List.sublist_append_right b.params _) ih

/-- The instruction-definition traversal is duplicate-free in an SSA
function. -/
theorem instrDefs_nodup {f : Func} (h : f.allDefs.Nodup) :
    (f.blocks.toList.flatMap fun b => b.instrs.flatMap Instr.defs).Nodup :=
  h.sublist (instrDefs_sublist_allDefs f)

/-- The instruction accumulator does not affect the map component of a fold. -/
theorem cfInstr_foldMap_acc (l : List Instr) (m : Std.HashMap ValId U256)
    (acc : List Instr) :
    (l.foldl (fun s i => cfInstrStep i s) ⟨m, acc⟩).1 =
      (l.foldl (fun s i => cfInstrStep i s) ⟨m, []⟩).1 := by
  induction l generalizing m acc with
  | nil => rfl
  | cons i is ih =>
    rw [List.foldl_cons, List.foldl_cons, cfInstrStep_eq, cfInstrStep_eq,
      ih (cfInstrMap i m) (cfInstrOut i m :: acc),
      ih (cfInstrMap i m) [cfInstrOut i m]]

/-- The exact block and map produced from a given incoming constant map. -/
def cfBlockOut (b : Block) (m : Std.HashMap ValId U256) : Block :=
  let r := b.instrs.foldl (fun s i => cfInstrStep i s) ⟨m, []⟩
  { b with instrs := r.2.reverse, term := cfTerm b r.1 }

def cfBlockMap (b : Block) (m : Std.HashMap ValId U256) : Std.HashMap ValId U256 :=
  (b.instrs.foldl (fun s i => cfInstrStep i s) ⟨m, []⟩).1

theorem cfBlockStep_eq' (b : Block) (st : CFOuter) :
    cfBlockStep b st = ⟨st.1.push (cfBlockOut b st.2), cfBlockMap b st.2⟩ := by
  simp only [cfBlockStep, cfBlockOut, cfBlockMap]

/-- Later block steps preserve every already-emitted block. -/
theorem cfBlock_fold_get_old (l : List Block) (st : CFOuter) {i : Nat} {b : Block}
    (h : st.1[i]? = some b) :
    (l.foldl (fun st b => cfBlockStep b st) st).1[i]? = some b := by
  induction l generalizing st with
  | nil => exact h
  | cons x xs ih =>
    apply ih (st := cfBlockStep x st)
    rw [cfBlockStep_eq', Array.getElem?_push]
    have hi : i < st.1.size := (Array.getElem?_eq_some_iff.mp h).1
    have hne : i ≠ st.1.size := Nat.ne_of_lt hi
    rw [Array.getElem?_eq_getElem hi] at h
    simp only [hne, ↓reduceIte]
    rw [Array.getElem?_eq_getElem hi]
    exact h

/-- Exact, index-preserving correspondence for a source block in the outer
fold. -/
theorem cfBlock_fold_get (l : List Block) (st : CFOuter) {j : Nat} {b : Block}
    (h : l[j]? = some b) :
    ∃ m, (l.foldl (fun st b => cfBlockStep b st) st).1[st.1.size + j]? =
        some (cfBlockOut b m) := by
  induction l generalizing st j with
  | nil => simp at h
  | cons x xs ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst x
      refine ⟨st.2, ?_⟩
      rw [List.foldl_cons]
      apply cfBlock_fold_get_old
      rw [cfBlockStep_eq', Array.getElem?_push]
      simp
    | succ j =>
      simp only [List.getElem?_cons_succ] at h
      rw [List.foldl_cons]
      obtain ⟨m, hm⟩ := ih (st := cfBlockStep x st) h
      refine ⟨m, ?_⟩
      rw [cfBlockStep_eq'] at hm ⊢
      simp only [Array.size_push] at hm
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hm

/-- Every source block has the exact folded block at the same index. -/
theorem constFold_block_get {f : Func} {i : BlockId} {b : Block}
    (h : f.blocks[i]? = some b) :
    ∃ m, (constFold f).blocks[i]? = some (cfBlockOut b m) := by
  rw [constFold_blocks_eq]
  have hl : f.blocks.toList[i]? = some b := by simpa using h
  obtain ⟨m, hm⟩ := cfBlock_fold_get f.blocks.toList ⟨#[], ∅⟩ hl
  refine ⟨m, ?_⟩
  simpa using hm

/-! ### Static constant certificates -/

/-- A value forced by a definition in `f`.  The recursive `op` constructor is
well-founded in exactly the folder's instruction order: all argument
certificates already occur in the incoming map. -/
inductive ConstDef (f : Func) : ValId → U256 → Prop
  | const {b : Block} {d : ValId} {v : U256} :
      b ∈ f.blocks.toList → .const d v ∈ b.instrs → ConstDef f d v
  | op {b : Block} {d : ValId} {yop : Op} {as : List ValId} {vs : List U256} {v : U256} :
      b ∈ f.blocks.toList → .op [d] yop as ∈ b.instrs → pureOp yop = true →
      List.Forall₂ (ConstDef f) as vs → evalPure yop vs = some v → ConstDef f d v

/-- Every certificate names an actual instruction destination. -/
theorem ConstDef.site {f : Func} {d : ValId} {v : U256} (h : ConstDef f d v) :
    ∃ b ∈ f.blocks.toList, ∃ i ∈ b.instrs, d ∈ i.defs := by
  cases h with
  | const hb hi => exact ⟨_, hb, _, hi, by simp [Instr.defs]⟩
  | op hb hi hp hvs he => exact ⟨_, hb, _, hi, by simp [Instr.defs]⟩

/-- A constant map is sound when each successful lookup carries a static
certificate. -/
def CFMapSound (f : Func) (m : Std.HashMap ValId U256) : Prop :=
  ∀ {d v}, m[d]? = some v → ConstDef f d v

theorem cfMapSound_empty (f : Func) : CFMapSound f ∅ := by
  intro d v h
  simp at h

/-- Successful `mapM` lookups in a sound map produce pointwise constant
certificates. -/
theorem cfMapSound_mapM {f : Func} {m : Std.HashMap ValId U256}
    (hm : CFMapSound f m) {as : List ValId} {vs : List U256}
    (h : as.mapM (m[·]?) = some vs) : List.Forall₂ (ConstDef f) as vs := by
  induction as generalizing vs with
  | nil => simp at h; subst vs; exact .nil
  | cons a as ih =>
    simp only [List.mapM_cons] at h
    cases ha : m[a]? with
    | none => simp [ha] at h
    | some v =>
      cases ht : as.mapM (m[·]?) with
      | none => simp [ha, ht] at h
      | some ws =>
        simp [ha, ht] at h
        subst vs
        exact .cons (hm ha) (ih ht)

/-- One folder step extends a sound map when its instruction belongs to the
function. -/
theorem cfInstrMap_sound {f : Func} {b : Block} (hb : b ∈ f.blocks.toList)
    {i : Instr} (hi : i ∈ b.instrs) {m : Std.HashMap ValId U256}
    (hm : CFMapSound f m) : CFMapSound f (cfInstrMap i m) := by
  intro d v hd
  cases i with
  | const x w =>
    rw [cfInstrMap, Std.HashMap.getElem?_insert] at hd
    split at hd
    · rename_i hxd
      have : x = d := by simpa using hxd
      subst d
      simp at hd
      subst v
      exact .const hb hi
    · exact hm hd
  | op ds yop as =>
    cases ds with
    | nil => exact hm hd
    | cons x xs =>
      cases xs with
      | cons y ys => exact hm hd
      | nil =>
        simp only [cfInstrMap] at hd
        split at hd
        · rename_i w hfold
          rw [Std.HashMap.getElem?_insert] at hd
          split at hd
          · rename_i hxd
            have : x = d := by simpa using hxd
            subst d
            simp at hd
            subst v
            by_cases hp : pureOp yop = true
            · cases hs : as.mapM (m[·]?) with
              | none => simp [hp, hs] at hfold
              | some vs =>
                simp [hp, hs] at hfold
                exact .op hb hi hp (cfMapSound_mapM hm hs) hfold
            · have hp' : pureOp yop = false := Bool.eq_false_of_not_eq_true hp
              simp [hp'] at hfold
          · exact hm hd
        · exact hm hd
  | call ds fid as => exact hm hd

/-- Folding a list of instructions from a sound map preserves soundness. -/
theorem cfInstr_foldMap_sound {f : Func} {b : Block} (hb : b ∈ f.blocks.toList)
    {l : List Instr} (hl : ∀ i ∈ l, i ∈ b.instrs) {m : Std.HashMap ValId U256}
    (hm : CFMapSound f m) :
    CFMapSound f (l.foldl (fun s i => cfInstrStep i s) ⟨m, []⟩).1 := by
  induction l generalizing m with
  | nil => exact hm
  | cons i is ih =>
    rw [List.foldl_cons, cfInstrStep_eq]
    rw [cfInstr_foldMap_acc]
    apply ih (fun j hj => hl j (by simp [hj]))
    exact cfInstrMap_sound hb (hl i (by simp)) hm

theorem cfBlockMap_sound {f : Func} {b : Block} (hb : b ∈ f.blocks.toList)
    {m : Std.HashMap ValId U256} (hm : CFMapSound f m) :
    CFMapSound f (cfBlockMap b m) := by
  exact cfInstr_foldMap_sound hb (fun i hi => hi) hm

/-- Strengthening of `cfBlock_fold_get`: the incoming map at the selected
block is sound. -/
theorem cfBlock_fold_get_sound {f : Func} {l : List Block}
    (hl : ∀ b ∈ l, b ∈ f.blocks.toList) (st : CFOuter)
    (hst : CFMapSound f st.2) {j : Nat} {b : Block} (h : l[j]? = some b) :
    ∃ m, (l.foldl (fun st b => cfBlockStep b st) st).1[st.1.size + j]? =
        some (cfBlockOut b m) ∧ CFMapSound f m := by
  induction l generalizing st j with
  | nil => simp at h
  | cons x xs ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst x
      refine ⟨st.2, ?_, hst⟩
      rw [List.foldl_cons]
      apply cfBlock_fold_get_old
      rw [cfBlockStep_eq', Array.getElem?_push]
      simp
    | succ j =>
      simp only [List.getElem?_cons_succ] at h
      rw [List.foldl_cons]
      have hx : x ∈ f.blocks.toList := hl x (by simp)
      have hsound : CFMapSound f (cfBlockStep x st).2 := by
        rw [cfBlockStep_eq']
        exact cfBlockMap_sound hx hst
      obtain ⟨m, hm, hms⟩ := ih (fun y hy => hl y (by simp [hy]))
        (cfBlockStep x st) hsound h
      refine ⟨m, ?_, hms⟩
      rw [cfBlockStep_eq'] at hm ⊢
      simp only [Array.size_push] at hm
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hm

theorem constFold_block_get_sound {f : Func} {i : BlockId} {b : Block}
    (h : f.blocks[i]? = some b) :
    ∃ m, (constFold f).blocks[i]? = some (cfBlockOut b m) ∧ CFMapSound f m := by
  rw [constFold_blocks_eq]
  have hl : f.blocks.toList[i]? = some b := by simpa using h
  obtain ⟨m, hm, hms⟩ := cfBlock_fold_get_sound
    (f := f) (fun b hb => hb) ⟨#[], ∅⟩ (cfMapSound_empty f) hl
  exact ⟨m, by simpa using hm, hms⟩

/-! ### Pass 2's structural specification -/

/-- One block step pushes a `CFRel`-rewrite of the source block. -/
theorem cfBlockStep_spec (b : Block) (st : CFOuter) :
    ∃ b', (cfBlockStep b st).1 = st.1.push b' ∧ CFRel b b' := by
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · intro x hx
    rw [ToAsm.mem_blockUses] at hx ⊢
    rcases hx with hx | hx
    · refine Or.inl ?_
      have h := (cfInstr_fold b.instrs ⟨st.2, []⟩).2 x (by
        simpa [mem_flatMap_reverse] using hx)
      simpa using h
    · exact Or.inr (cfTerm_uses b _ hx)
  · intro x hx
    rw [ToAsm.mem_blockDefs] at hx ⊢
    rcases hx with hx | hx
    · exact Or.inl hx
    · refine Or.inr ?_
      have h := ((cfInstr_fold b.instrs ⟨st.2, []⟩).1 x).mpr (Or.inr hx)
      simpa [mem_flatMap_reverse] using h
  · intro e he
    exact cfTerm_edges b _ he

/-- The block fold builds the output array index by index. -/
theorem cfBlock_fold (l : List Block) (st : CFOuter) (i : Nat) (b' : Block)
    (h : (l.foldl (fun st b => cfBlockStep b st) st).1[i]? = some b') :
    st.1[i]? = some b' ∨
      ∃ (j : Nat) (b : Block), l[j]? = some b ∧ i = st.1.size + j ∧ CFRel b b' := by
  induction l generalizing st with
  | nil => exact Or.inl h
  | cons b bs ih =>
    obtain ⟨b'', hpush, hrel⟩ := cfBlockStep_spec b st
    have hstep : (List.foldl (fun st b => cfBlockStep b st) st (b :: bs))
        = List.foldl (fun st b => cfBlockStep b st) (cfBlockStep b st) bs := rfl
    rw [hstep] at h
    rcases ih (cfBlockStep b st) h with h1 | ⟨j, b0, hj, hij, hrel0⟩
    · rw [hpush, Array.getElem?_push] at h1
      split at h1
      · rename_i hi
        obtain rfl := Option.some.inj h1
        exact Or.inr ⟨0, b, rfl, by omega, hrel⟩
      · exact Or.inl h1
    · refine Or.inr ⟨j + 1, b0, by simpa using hj, ?_, hrel0⟩
      rw [hpush] at hij
      simp only [Array.size_push] at hij
      omega

/-- **Pass 2's structural specification**: every block of the output is a
`CFRel`-rewrite of the block at the same index of the input. -/
theorem constFold_spec (f : Func) (i : BlockId) (b' : Block)
    (h : (constFold f).blocks[i]? = some b') : ∃ b, f.blocks[i]? = some b ∧ CFRel b b' := by
  rw [constFold_blocks_eq] at h
  rcases cfBlock_fold f.blocks.toList ⟨#[], ∅⟩ i b' h with h1 | ⟨j, b, hj, hij, hrel⟩
  · simp at h1
  · refine ⟨b, ?_, hrel⟩
    have : i = j := by simpa using hij
    subst this
    simpa using hj

/-! ### Pass 3's loop, as a fold -/

abbrev CSEInner :=
  MProd (List Instr)
    (MProd CseTab
      (MProd (Std.HashSet ValId)
        (MProd Subst (MProd (Std.HashSet ValId) (Std.HashSet ValId)))))
abbrev CSEOuter := MProd (Array Block) (MProd (Array CseTab) Subst)

def cseBlockDefs (b : Block) : Std.HashSet ValId :=
  b.instrs.foldl (fun s i => i.defs.foldl (fun s d => s.insert d) s) ∅

def cseEntryTab (f : Func) (srcs : Array (List BlockId))
    (tables : Array CseTab) (bi : BlockId) : CseTab :=
  if bi == f.entry then {}
  else match srcs[bi]! with
    | [p] => if p < bi then
        Passes.inheritTab tables[p]! f.blocks[bi]!.params
      else {}
    | _ => {}

/-! The source collector used by `cseEntryTab`, exposed as folds. -/

def sourceEdgeStep (bi : BlockId) (acc : Array (List BlockId)) (e : Edge) :
    Array (List BlockId) :=
  acc.setIfInBounds e.target (bi :: acc[e.target]!)

def sourceBlockStep (f : Func) (acc : Array (List BlockId)) (bi : BlockId) :
    Array (List BlockId) :=
  f.blocks[bi]!.term.edges.foldl (sourceEdgeStep bi) acc

theorem inEdgeSources_eq_fold (f : Func) :
    inEdgeSources f =
      (List.range' 0 f.blocks.size 1).foldl (sourceBlockStep f)
        (Array.replicate f.blocks.size []) := by
  unfold inEdgeSources
  dsimp only [sourceBlockStep, sourceEdgeStep]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rw [Id.forIn_eq_foldl (g := fun bi acc =>
    f.blocks[bi]!.term.edges.foldl
      (fun acc e => acc.setIfInBounds e.target (bi :: acc[e.target]!)) acc) (h := by
    intro bi acc
    rw [Id.forIn_eq_foldl (g := fun e acc =>
      acc.setIfInBounds e.target (bi :: acc[e.target]!)) (h := by
      intro e acc
      rfl)]
    rfl)]
  simp [Id.run, bind, pure]
  congr 1

def cseInstrStep (ins0 : Instr) (st : CSEInner) : CSEInner :=
  let used := ins0.uses.foldl (fun s a => s.insert a) st.2.2.1
  let defined := ins0.defs.foldl (fun s d => s.insert d) st.2.2.2.2.1
  match substInstr st.2.2.2.1 ins0 with
  | .const d v =>
    match st.2.1.consts.find? (·.1 == v) with
    | some (_, d0) =>
      ⟨st.1, st.2.1, used, st.2.2.2.1.insert d d0, defined, st.2.2.2.2.2⟩
    | none =>
      ⟨.const d v :: st.1, { st.2.1 with consts := (v, d) :: st.2.1.consts },
        used, st.2.2.2.1, defined, st.2.2.2.2.2⟩
  | .op [d] yop args =>
    if pureOp yop then
      match st.2.1.ops.find? (·.1 == (yop, args)) with
      | some (_, d0) =>
        if st.2.2.1.contains d then
          ⟨.op [d] yop args :: st.1, st.2.1, used, st.2.2.2.1,
            defined, st.2.2.2.2.2⟩
        else
          ⟨st.1, st.2.1, used, st.2.2.2.1.insert d d0,
            defined, st.2.2.2.2.2⟩
      | none =>
        if args.all (fun a =>
            st.2.2.2.2.1.contains a || !st.2.2.2.2.2.contains a) then
          ⟨.op [d] yop args :: st.1,
            { st.2.1 with ops := ((yop, args), d) :: st.2.1.ops },
            used, st.2.2.2.1, defined, st.2.2.2.2.2⟩
        else
          ⟨.op [d] yop args :: st.1, st.2.1, used, st.2.2.2.1,
            defined, st.2.2.2.2.2⟩
    else
      ⟨.op [d] yop args :: st.1, st.2.1, used, st.2.2.2.1,
        defined, st.2.2.2.2.2⟩
  | ins =>
    ⟨ins :: st.1, st.2.1, used, st.2.2.2.1, defined, st.2.2.2.2.2⟩

/-- The implementation keeps `definedSoFar` first because it is declared before
the mutable instruction/table state.  The proof model keeps the historical
four projections first and appends the two new guard accumulators. -/
abbrev CSEImplInner :=
  MProd (Std.HashSet ValId)
    (MProd (List Instr) (MProd CseTab (MProd (Std.HashSet ValId) Subst)))

def cseImplToModel (blockDefs : Std.HashSet ValId) (st : CSEImplInner) : CSEInner :=
  ⟨st.2.1, st.2.2.1, st.2.2.2.1, st.2.2.2.2, st.1, blockDefs⟩

def cseModelToImpl (st : CSEInner) : CSEImplInner :=
  ⟨st.2.2.2.2.1, st.1, st.2.1, st.2.2.1, st.2.2.2.1⟩

def cseImplInstrStep (blockDefs : Std.HashSet ValId) (ins : Instr)
    (st : CSEImplInner) : CSEImplInner :=
  cseModelToImpl (cseInstrStep ins (cseImplToModel blockDefs st))

@[simp] theorem cseImplToModel_step (blockDefs : Std.HashSet ValId)
    (ins : Instr) (st : CSEImplInner) :
    cseImplToModel blockDefs (cseImplInstrStep blockDefs ins st) =
      cseInstrStep ins (cseImplToModel blockDefs st) := by
  unfold cseImplInstrStep cseImplToModel cseModelToImpl cseInstrStep
  cases hs : substInstr st.2.2.2.2 ins with
  | const d v => simp only [hs]; split <;> rfl
  | op ds yop args =>
      cases ds with
      | nil => simp [hs]
      | cons d rest =>
          cases rest with
          | nil =>
              simp only [hs]
              split <;> (try split <;> (try split <;> (try split))) <;> rfl
          | cons e es => simp [hs]
  | call ds fid args => simp [hs]

theorem cseImplFold_toModel (blockDefs : Std.HashSet ValId) (l : List Instr)
    (st : CSEImplInner) :
    cseImplToModel blockDefs
        (l.foldl (fun st ins => cseImplInstrStep blockDefs ins st) st) =
      l.foldl (fun st ins => cseInstrStep ins st) (cseImplToModel blockDefs st) := by
  induction l generalizing st with
  | nil => rfl
  | cons i is ih =>
      rw [List.foldl_cons, List.foldl_cons, ← cseImplToModel_step, ih]

theorem mem_fold_insert_iff {xs : List ValId} {s : Std.HashSet ValId}
    {x : ValId} :
    x ∈ xs.foldl (fun s a => s.insert a) s ↔ x ∈ s ∨ x ∈ xs := by
  induction xs generalizing s with
  | nil => simp
  | cons a as ih =>
      rw [List.foldl_cons, ih, Std.HashSet.mem_insert]
      simp only [List.mem_cons]
      simp only [beq_iff_eq]
      tauto

@[simp] theorem cseInstrStep_used (i : Instr) (st : CSEInner) :
    (cseInstrStep i st).2.2.1 =
      i.uses.foldl (fun s a => s.insert a) st.2.2.1 := by
  unfold cseInstrStep
  split <;> (try split <;> (try split <;> (try split))) <;> rfl

@[simp] theorem cseInstrStep_defined (i : Instr) (st : CSEInner) :
    (cseInstrStep i st).2.2.2.2.1 =
      i.defs.foldl (fun s d => s.insert d) st.2.2.2.2.1 := by
  unfold cseInstrStep
  split <;> (try split <;> (try split <;> (try split))) <;> rfl

@[simp] theorem cseInstrStep_blockDefs (i : Instr) (st : CSEInner) :
    (cseInstrStep i st).2.2.2.2.2 = st.2.2.2.2.2 := by
  unfold cseInstrStep
  split <;> (try split <;> (try split <;> (try split))) <;> rfl

theorem cseInstrFold_used (l : List Instr) (st : CSEInner) {x : ValId} :
    x ∈ (l.foldl (fun s i => cseInstrStep i s) st).2.2.1 ↔
      x ∈ st.2.2.1 ∨ x ∈ l.flatMap Instr.uses := by
  induction l generalizing st with
  | nil => simp
  | cons i is ih =>
      rw [List.foldl_cons, ih, cseInstrStep_used, mem_fold_insert_iff,
        List.flatMap_cons, List.mem_append]
      tauto

theorem cseInstrFold_defined (l : List Instr) (st : CSEInner) {x : ValId} :
    x ∈ (l.foldl (fun s i => cseInstrStep i s) st).2.2.2.2.1 ↔
      x ∈ st.2.2.2.2.1 ∨ x ∈ l.flatMap Instr.defs := by
  induction l generalizing st with
  | nil => simp
  | cons i is ih =>
      rw [List.foldl_cons, ih, cseInstrStep_defined, mem_fold_insert_iff,
        List.flatMap_cons, List.mem_append]
      tauto

theorem cseInstrFold_blockDefs (l : List Instr) (st : CSEInner) :
    (l.foldl (fun s i => cseInstrStep i s) st).2.2.2.2.2 = st.2.2.2.2.2 := by
  induction l generalizing st with
  | nil => rfl
  | cons i is ih =>
      rw [List.foldl_cons, ih, cseInstrStep_blockDefs]

theorem mem_cseBlockDefs {b : Block} {x : ValId} :
    x ∈ cseBlockDefs b ↔ x ∈ b.instrs.flatMap Instr.defs := by
  have go : ∀ (l : List Instr) (s : Std.HashSet ValId),
      x ∈ l.foldl
          (fun s i => i.defs.foldl (fun s d => s.insert d) s) s ↔
        x ∈ s ∨ x ∈ l.flatMap Instr.defs := by
    intro l
    induction l with
    | nil => simp
    | cons i is ih =>
        intro s
        rw [List.foldl_cons, ih, mem_fold_insert_iff,
          List.flatMap_cons, List.mem_append]
        tauto
  unfold cseBlockDefs
  simpa using go b.instrs ∅

/-- The drop guard is exactly the strict-prefix use fact needed by the
simulation: a destination accepted for elimination was not read by any
already-processed instruction in its block. -/
theorem cse_drop_dest_not_used_prefix {pre : List Instr} {i : Instr}
    {acc : List Instr} {tab : CseTab} {used defined blockDefs : Std.HashSet ValId}
    {σ : Subst} {d d0 : ValId} {yop : Op} {args : List ValId}
    (hused0 : d ∉ used)
    (hs : substInstr
      (pre.foldl (fun s i => cseInstrStep i s)
        ⟨acc, tab, used, σ, defined, blockDefs⟩).2.2.2.1 i =
        .op [d] yop args)
    (hfind :
      (pre.foldl (fun s i => cseInstrStep i s)
        ⟨acc, tab, used, σ, defined, blockDefs⟩).2.1.ops.find?
          (·.1 == (yop, args)) = some ((yop, args), d0))
    (hdrop :
      ¬ (pre.foldl (fun s i => cseInstrStep i s)
        ⟨acc, tab, used, σ, defined, blockDefs⟩).2.2.1.contains d = true) :
    d ∉ pre.flatMap Instr.uses := by
  intro hd
  have hm : d ∈ (pre.foldl (fun s i => cseInstrStep i s)
      ⟨acc, tab, used, σ, defined, blockDefs⟩).2.2.1 :=
    (cseInstrFold_used pre _).mpr (Or.inr hd)
  exact hdrop (Std.HashSet.mem_iff_contains.mp hm)

/-- An operation admitted to the table has no argument defined in the
unprocessed suffix.  This is the static stability half of the entry-add
guard. -/
theorem cse_entry_args_not_defined_later {pre post : List Instr} {i : Instr}
    {acc : List Instr} {tab : CseTab} {used : Std.HashSet ValId} {σ : Subst}
    {defined blockDefs : Std.HashSet ValId} {args : List ValId}
    (hdefs : blockDefs = cseBlockDefs ⟨[], pre ++ i :: post, .ret []⟩)
    (hdefined0 : ∀ x, x ∉ defined)
    (hnd : (pre ++ i :: post).flatMap Instr.defs |>.Nodup)
    (hguard : args.all (fun a =>
      (pre.foldl (fun s i => cseInstrStep i s)
        ⟨acc, tab, used, σ, defined, blockDefs⟩).2.2.2.2.1.contains a ||
        !blockDefs.contains a) = true) :
    ∀ a ∈ args, a ∉ (i :: post).flatMap Instr.defs := by
  intro a ha hpost
  have hg := List.all_eq_true.mp hguard a ha
  rw [Bool.or_eq_true] at hg
  have hablock : a ∈ blockDefs := by
    rw [hdefs, mem_cseBlockDefs]
    simp only [List.flatMap_append, List.flatMap_cons, List.mem_append]
    exact Or.inr (by simpa [List.flatMap_cons] using hpost)
  rcases hg with hpre | hnot
  · have hpre' : a ∈ pre.flatMap Instr.defs := by
      have hm := Std.HashSet.contains_iff_mem.mp hpre
      rcases (cseInstrFold_defined pre _).mp hm with hbase | hp
      · exact False.elim (hdefined0 a hbase)
      · exact hp
    simp only [List.flatMap_append, List.flatMap_cons] at hnd
    rw [List.nodup_append] at hnd
    exact (hnd.2.2 a hpre' a hpost) rfl
  · have hc := Std.HashSet.mem_iff_contains.mp hablock
    rw [hc] at hnot
    simp at hnot

def cseBlockStep (f : Func) (srcs : Array (List BlockId))
    (bi : BlockId) (st : CSEOuter) : CSEOuter :=
  let b := f.blocks[bi]!
  let tab := cseEntryTab f srcs st.2.1 bi
  let r := b.instrs.foldl (fun s i => cseInstrStep i s)
    ⟨[], tab, ∅, st.2.2, ∅, cseBlockDefs b⟩
  ⟨st.1.push { b with instrs := r.1.reverse },
    st.2.1.setIfInBounds bi r.2.1, r.2.2.2.1⟩

theorem cse_eq (f : Func) :
    cse f =
      let srcs := inEdgeSources f
      let r := (List.range' 0 f.blocks.size 1).foldl
        (fun st bi => cseBlockStep f srcs bi st)
        ⟨#[], Array.replicate f.blocks.size {}, (∅ : Subst)⟩
      substFunc r.2.2 { f with blocks := r.1 } := by
  unfold cse
  dsimp only
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rw [Id.forIn_eq_foldl (g := fun bi st => cseBlockStep f (inEdgeSources f) bi st)
    (h := by
      intro bi st
      dsimp only [cseBlockStep, cseEntryTab]
      let bdefs :=
        f.blocks[bi]!.instrs.foldl
          (fun (s : Std.HashSet ValId) i =>
            i.defs.foldl (fun s d => s.insert d) s) ∅
      rw [Id.forIn_eq_foldl
        (g := fun ins s => cseImplInstrStep bdefs ins s) (h := by
        intro i s
        dsimp only [bdefs, cseBlockDefs]
        cases hs : substInstr s.2.2.2.2 i with
        | const d v =>
          simp only [cseImplInstrStep, cseImplToModel, cseModelToImpl,
            cseInstrStep, hs]
          split <;> rename_i hfind <;> simp only [hfind] <;> rfl
        | op ds yop args =>
          cases ds with
          | nil => simp [cseImplInstrStep, cseImplToModel, cseModelToImpl,
              cseInstrStep, hs]
          | cons d rest =>
            cases rest with
            | nil =>
              simp only [cseImplInstrStep, cseImplToModel, cseModelToImpl,
                cseInstrStep, hs]
              split
              · split <;> rename_i hfind <;> simp only [hfind]
                · split <;> rfl
                · split <;> rfl
              · rfl
            | cons e es => simp [cseImplInstrStep, cseImplToModel,
                cseModelToImpl, cseInstrStep, hs]
        | call ds fid args => simp [cseImplInstrStep, cseImplToModel,
            cseModelToImpl, cseInstrStep, hs])]
      have hc := cseImplFold_toModel bdefs f.blocks[bi]!.instrs
        ⟨∅, [],
          if bi == f.entry then {}
          else match (inEdgeSources f)[bi]! with
            | [p] => if p < bi then
                Passes.inheritTab st.2.1[p]! f.blocks[bi]!.params
              else {}
            | _ => {},
          ∅, st.2.2⟩
      dsimp only [cseImplToModel] at hc
      have hbdefs : bdefs = cseBlockDefs f.blocks[bi]! := by
        simp [bdefs, cseBlockDefs]
      rw [← hbdefs]
      rw [← hc]
      rfl)]
  simp [Id.run, bind, pure]

def csePrefix (f : Func) (n : Nat) : CSEOuter :=
  (List.range' 0 n 1).foldl
    (fun st bi => cseBlockStep f (inEdgeSources f) bi st)
    ⟨#[], Array.replicate f.blocks.size {}, (∅ : Subst)⟩

@[simp] theorem csePrefix_zero (f : Func) :
    csePrefix f 0 = ⟨#[], Array.replicate f.blocks.size {}, (∅ : Subst)⟩ := rfl

theorem csePrefix_succ (f : Func) (n : Nat) :
    csePrefix f (n + 1) = cseBlockStep f (inEdgeSources f) n (csePrefix f n) := by
  simp [csePrefix, List.range'_concat, List.foldl_append]

@[simp] theorem csePrefix_blocks_size (f : Func) (n : Nat) :
    (csePrefix f n).1.size = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show n + 1 = Nat.succ n from rfl, csePrefix_succ]
    simp [cseBlockStep, ih]

theorem cseBlockStep_get_old (f : Func) (srcs : Array (List BlockId))
    (bi : BlockId) (st : CSEOuter) {i : Nat} {b : Block}
    (h : st.1[i]? = some b) : (cseBlockStep f srcs bi st).1[i]? = some b := by
  rw [cseBlockStep, Array.getElem?_push]
  have hi : i < st.1.size := (Array.getElem?_eq_some_iff.mp h).1
  have hne : i ≠ st.1.size := Nat.ne_of_lt hi
  rw [if_neg hne]
  exact h

theorem cseOuter_fold_get_old (f : Func) (srcs : Array (List BlockId))
    (l : List BlockId) (st : CSEOuter) {i : Nat} {b : Block}
    (h : st.1[i]? = some b) :
    (l.foldl (fun st bi => cseBlockStep f srcs bi st) st).1[i]? = some b := by
  induction l generalizing st with
  | nil => exact h
  | cons bi bis ih =>
    rw [List.foldl_cons]
    exact ih _ (cseBlockStep_get_old f srcs bi st h)

def cseBlockOut (f : Func) (bi : BlockId) : Block :=
  let b := f.blocks[bi]!
  let st := csePrefix f bi
  let tab := cseEntryTab f (inEdgeSources f) st.2.1 bi
  let r := b.instrs.foldl (fun s i => cseInstrStep i s)
    ⟨[], tab, ∅, st.2.2, ∅, cseBlockDefs b⟩
  { b with instrs := r.1.reverse }

inductive CseExpr
  | const (v : U256)
  | op (yop : Op) (args : List ValId)

/-- A certificate that a CSE table entry came from an actual, strictly earlier
instruction in the fold.  Operation arguments record the substitution that was
in force when that instruction entered the table. -/
inductive CseDef (f : Func) : CseExpr → ValId → Prop
  | const {b : Block} {d : ValId} {v : U256} :
      b ∈ f.blocks.toList → .const d v ∈ b.instrs → CseDef f (.const v) d
  | op {b : Block} {d : ValId} {yop : Op} {args : List ValId} {σ : Subst} :
      b ∈ f.blocks.toList → .op [d] yop args ∈ b.instrs → pureOp yop = true →
      CseDef f (.op yop (substVs σ args)) d

theorem CseDef.site {f : Func} {e : CseExpr} {d : ValId} (h : CseDef f e d) :
    ∃ b ∈ f.blocks.toList, ∃ i ∈ b.instrs, d ∈ i.defs := by
  cases h with
  | const hb hi => exact ⟨_, hb, _, hi, by simp [Instr.defs]⟩
  | op hb hi hp => exact ⟨_, hb, _, hi, by simp [Instr.defs]⟩

def cseTabVals (tab : CseTab) : List ValId :=
  tab.ops.map (·.2) ++ tab.consts.map (·.2)

def CseTabDefSound (f : Func) (tab : CseTab) : Prop :=
  (∀ {yop args d}, ((yop, args), d) ∈ tab.ops → CseDef f (.op yop args) d) ∧
  (∀ {v d}, (v, d) ∈ tab.consts → CseDef f (.const v) d)

def CseSubDefSound (f : Func) (σ : Subst) : Prop :=
  ∀ {d d0}, σ[d]? = some d0 → ∃ e, CseDef f e d ∧ CseDef f e d0

/-- The fold-position certificate retained for an operation-table entry.  The
stored arguments are stable through the remainder of the source block in
which the entry was created. -/
inductive CseEntryPos (f : Func) : CseExpr → ValId → Prop
  | op {b : Block} {pre post : List Instr} {i : Instr} {σ : Subst}
      {d : ValId} {yop : Op} {args : List ValId} :
      b ∈ f.blocks.toList → b.instrs = pre ++ i :: post →
      substInstr σ i = .op [d] yop args →
      (∀ a ∈ args, a ∉ (i :: post).flatMap Instr.defs) →
      CseEntryPos f (.op yop args) d

/-- The fold-position certificate retained for a dropped definition.  Constants
need no prefix guard: after their first execution every dynamic occurrence has
the advertised fixed value.  A dropped operation destination, by contrast,
must not have been read earlier in its source block. -/
inductive CseDropPos (f : Func) : CseExpr → ValId → Prop
  | const {b : Block} {pre post : List Instr} {i : Instr} {σ : Subst}
      {d : ValId} {v : U256} :
      b ∈ f.blocks.toList → b.instrs = pre ++ i :: post →
      substInstr σ i = .const d v → CseDropPos f (.const v) d
  | op {b : Block} {pre post : List Instr} {i : Instr} {σ : Subst}
      {d : ValId} {yop : Op} {args : List ValId} :
      b ∈ f.blocks.toList → b.instrs = pre ++ i :: post →
      substInstr σ i = .op [d] yop args →
      σ[d]? = none →
      d ∉ pre.flatMap Instr.uses →
      CseDropPos f (.op yop args) d

def CseTabPosSound (f : Func) (tab : CseTab) : Prop :=
  ∀ {yop args d}, ((yop, args), d) ∈ tab.ops →
    CseEntryPos f (.op yop args) d

def CseSubPosSound (f : Func) (σ : Subst) : Prop :=
  ∀ {d d0}, σ[d]? = some d0 →
    ∃ e, CseDropPos f e d ∧
      ∀ {yop args}, e = .op yop args → CseEntryPos f (.op yop args) d0

/-- Full CSE certificates: semantic definition provenance plus the guard fact
from the exact fold position at which an entry/alias was created. -/
def CseTabSound (f : Func) (tab : CseTab) : Prop :=
  CseTabDefSound f tab ∧ CseTabPosSound f tab

def CseSubSound (f : Func) (σ : Subst) : Prop :=
  CseSubDefSound f σ ∧ CseSubPosSound f σ

theorem CseTabPosSound.empty (f : Func) : CseTabPosSound f {} := by
  simp [CseTabPosSound]

theorem CseTabPosSound.inheritTab {f : Func} {tab : CseTab}
    (h : CseTabPosSound f tab) (ps : List ValId) :
    CseTabPosSound f (Passes.inheritTab tab ps) := by
  intro yop args d hm
  exact h (List.mem_filter.mp hm).1

theorem CseTabPosSound.addOp {f : Func} {tab : CseTab}
    (h : CseTabPosSound f tab) {yop : Op} {args : List ValId} {d : ValId}
    (hp : CseEntryPos f (.op yop args) d) :
    CseTabPosSound f { tab with ops := ((yop, args), d) :: tab.ops } := by
  intro yop0 args0 d0 hm
  rcases List.mem_cons.mp hm with hnew | hold
  · obtain ⟨hkey, rfl⟩ := Prod.mk.inj hnew
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hkey
    exact hp
  · exact h hold

theorem CseSubPosSound.insert {f : Func} {σ : Subst}
    (h : CseSubPosSound f σ) {d d0 : ValId} {e : CseExpr}
    (hp : CseDropPos f e d)
    (he : ∀ {yop args}, e = .op yop args → CseEntryPos f (.op yop args) d0) :
    CseSubPosSound f (σ.insert d d0) := by
  intro x y hxy
  rw [Std.HashMap.getElem?_insert] at hxy
  split at hxy
  · rename_i heq
    have hxd : x = d := (beq_iff_eq.mp heq).symm
    subst x
    have hyd : y = d0 := (Option.some.inj hxy).symm
    subst y
    exact ⟨e, hp, he⟩
  · exact h hxy

def SubstExt (σ τ : Subst) : Prop :=
  ∀ {x y : ValId}, σ[x]? = some y → τ[x]? = some y

def RangeFree (σ : Subst) : Prop :=
  ∀ {x y : ValId}, σ[x]? = some y → σ[y]? = none

def CSEInv (f : Func) (seen : List ValId) (tab : CseTab) (σ : Subst) : Prop :=
  CseTabDefSound f tab ∧ CseSubDefSound f σ ∧ RangeFree σ
    ∧ (∀ {x y : ValId}, σ[x]? = some y → x ∈ seen ∧ y ∈ seen)
    ∧ (∀ x ∈ cseTabVals tab, x ∈ seen ∧ σ[x]? = none)

theorem cseInv_empty (f : Func) : CSEInv f [] {} (∅ : Subst) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · intro d d0 h
    simp at h
  · intro x y h
    simp at h
  · intro x y h
    simp at h
  · simp [cseTabVals]

theorem CSEInv.weaken {f : Func} {seen seen' : List ValId} {tab : CseTab} {σ : Subst}
    (h : CSEInv f seen tab σ) (hsub : ∀ x ∈ seen, x ∈ seen') :
    CSEInv f seen' tab σ := by
  refine ⟨h.1, h.2.1, h.2.2.1, ?_, ?_⟩
  · intro x y hxy
    exact ⟨hsub x (h.2.2.2.1 hxy).1, hsub y (h.2.2.2.1 hxy).2⟩
  · intro x hx
    exact ⟨hsub x (h.2.2.2.2 x hx).1, (h.2.2.2.2 x hx).2⟩

theorem CSEInv.insert {f : Func} {seen : List ValId} {tab : CseTab} {σ : Subst}
    {d d0 : ValId} {e : CseExpr} (h : CSEInv f seen tab σ)
    (hd : d ∉ seen) (hd0 : d0 ∈ seen)
    (hd0none : σ[d0]? = none)
    (hc : CseDef f e d) (hc0 : CseDef f e d0) :
    CSEInv f (seen ++ [d]) tab (σ.insert d d0) := by
  have hdne : d ≠ d0 := fun heq => hd (heq ▸ hd0)
  have hdnone : σ[d]? = none := by
    by_contra hn
    obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp hn
    exact hd (h.2.2.2.1 hy).1
  refine ⟨h.1, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    rw [Std.HashMap.getElem?_insert] at hxy
    split at hxy
    · rename_i heq
      have hxd : x = d := (beq_iff_eq.mp heq).symm
      subst x
      obtain rfl := Option.some.inj hxy
      exact ⟨e, hc, hc0⟩
    · exact h.2.1 hxy
  · intro x y hxy
    rw [Std.HashMap.getElem?_insert] at hxy
    split at hxy
    · rename_i heq
      have hxd : x = d := (beq_iff_eq.mp heq).symm
      subst x
      obtain rfl := Option.some.inj hxy
      simp [Std.HashMap.getElem?_insert, hdne, hd0none]
    · rename_i hne
      have holdnone : σ[y]? = none := h.2.2.1 hxy
      have hyd : (d == y) = false := by
        apply Bool.eq_false_of_not_eq_true
        intro heq
        have hdy : d = y := beq_iff_eq.mp heq
        exact hd (hdy ▸ (h.2.2.2.1 hxy).2)
      simp [Std.HashMap.getElem?_insert, hyd, holdnone]
  · intro x y hxy
    rw [Std.HashMap.getElem?_insert] at hxy
    split at hxy
    · rename_i heq
      have hxd : x = d := (beq_iff_eq.mp heq).symm
      subst x
      obtain rfl := Option.some.inj hxy
      exact ⟨by simp, by simp [hd0]⟩
    · have hseen := h.2.2.2.1 hxy
      exact ⟨by simp [hseen.1], by simp [hseen.2]⟩
  · intro x hx
    have htab := h.2.2.2.2 x hx
    refine ⟨by simp [htab.1], ?_⟩
    have hdx : (d == x) = false := by
      apply Bool.eq_false_of_not_eq_true
      intro heq
      exact hd (beq_iff_eq.mp heq ▸ htab.1)
    simp [Std.HashMap.getElem?_insert, hdx, htab.2]

theorem CSEInv.insert_ext {f : Func} {seen : List ValId} {tab : CseTab} {σ : Subst}
    {d : ValId} (d0 : ValId) (h : CSEInv f seen tab σ) (hd : d ∉ seen) :
    SubstExt σ (σ.insert d d0) := by
  intro x y hxy
  have hxd : (d == x) = false := by
    apply Bool.eq_false_of_not_eq_true
    intro heq
    exact hd (beq_iff_eq.mp heq ▸ (h.2.2.2.1 hxy).1)
  simp [Std.HashMap.getElem?_insert, hxd, hxy]

theorem CSEInv.addConst {f : Func} {seen : List ValId} {tab : CseTab} {σ : Subst}
    {d : ValId} {v : U256} (h : CSEInv f seen tab σ) (hd : d ∉ seen)
    (hc : CseDef f (.const v) d) :
    CSEInv f (seen ++ [d]) { tab with consts := (v, d) :: tab.consts } σ := by
  have hdnone : σ[d]? = none := by
    by_contra hn
    obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp hn
    exact hd (h.2.2.2.1 hy).1
  refine ⟨?_, h.2.1, h.2.2.1, ?_, ?_⟩
  · refine ⟨h.1.1, ?_⟩
    intro w x hx
    rcases List.mem_cons.mp hx with hhead | htail
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hhead
      exact hc
    · exact h.1.2 htail
  · intro x y hxy
    have hs := h.2.2.2.1 hxy
    exact ⟨by simp [hs.1], by simp [hs.2]⟩
  · intro x hx
    simp only [cseTabVals, List.map_cons, List.mem_append, List.mem_cons] at hx
    rcases hx with hx | rfl | hx
    · have ho : x ∈ cseTabVals tab := by
        simp only [cseTabVals, List.mem_append]
        exact Or.inl hx
      have hs := h.2.2.2.2 x ho
      exact ⟨by simp [hs.1], hs.2⟩
    · exact ⟨by simp, hdnone⟩
    · have ho : x ∈ cseTabVals tab := by
        simp only [cseTabVals, List.mem_append]
        exact Or.inr hx
      have hs := h.2.2.2.2 x ho
      exact ⟨by simp [hs.1], hs.2⟩

theorem CSEInv.addOp {f : Func} {seen : List ValId} {tab : CseTab} {σ : Subst}
    {d : ValId} {yop : Op} {args : List ValId} (h : CSEInv f seen tab σ)
    (hd : d ∉ seen) (hc : CseDef f (.op yop args) d) :
    CSEInv f (seen ++ [d]) { tab with ops := ((yop, args), d) :: tab.ops } σ := by
  have hdnone : σ[d]? = none := by
    by_contra hn
    obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp hn
    exact hd (h.2.2.2.1 hy).1
  refine ⟨?_, h.2.1, h.2.2.1, ?_, ?_⟩
  · refine ⟨?_, h.1.2⟩
    intro op as x hx
    rcases List.mem_cons.mp hx with hhead | htail
    · obtain ⟨hopargs, rfl⟩ := Prod.mk.inj hhead
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hopargs
      exact hc
    · exact h.1.1 htail
  · intro x y hxy
    have hs := h.2.2.2.1 hxy
    exact ⟨by simp [hs.1], by simp [hs.2]⟩
  · intro x hx
    simp only [cseTabVals, List.map_cons, List.mem_append, List.mem_cons] at hx
    rcases hx with (rfl | hx) | hx
    · exact ⟨by simp, hdnone⟩
    · have ho : x ∈ cseTabVals tab := by
        simp only [cseTabVals, List.mem_append]
        exact Or.inl hx
      have hs := h.2.2.2.2 x ho
      exact ⟨by simp [hs.1], hs.2⟩
    · have ho : x ∈ cseTabVals tab := by
        simp only [cseTabVals, List.mem_append]
        exact Or.inr hx
      have hs := h.2.2.2.2 x ho
      exact ⟨by simp [hs.1], hs.2⟩

theorem cseInstrStep_inv {f : Func} {b : Block} (hb : b ∈ f.blocks.toList)
    {seen : List ValId} {tab : CseTab} {used : Std.HashSet ValId} {σ : Subst}
    {defined blockDefs : Std.HashSet ValId}
    (hinv : CSEInv f seen tab σ)
    (i : Instr) (hi : i ∈ b.instrs) (hnd : (seen ++ i.defs).Nodup) :
    let r := cseInstrStep i ⟨[], tab, used, σ, defined, blockDefs⟩
    CSEInv f (seen ++ i.defs) r.2.1 r.2.2.2.1 ∧ SubstExt σ r.2.2.2.1 := by
  have ext_refl : SubstExt σ σ := fun h => h
  cases i with
  | const d v =>
    have hd : d ∉ seen := by
      rw [List.nodup_append] at hnd
      exact fun hm => (hnd.2.2 d hm d (by simp [Instr.defs])) rfl
    have hc : CseDef f (.const v) d := .const hb hi
    simp only [cseInstrStep, substInstr]
    split
    · rename_i w d0 hfind
      have hpw : (w == v) = true := List.find?_some
        (p := fun x : U256 × ValId => x.1 == v) (a := (w, d0)) hfind
      have hw : w = v := beq_iff_eq.mp hpw
      subst w
      have hm : (v, d0) ∈ tab.consts := List.mem_of_find?_eq_some hfind
      have hc0 : CseDef f (.const v) d0 := hinv.1.2 hm
      have htv : d0 ∈ cseTabVals tab := by
        unfold cseTabVals
        exact List.mem_append_right _ (List.mem_map.mpr ⟨(v, d0), hm, rfl⟩)
      have hd0 := hinv.2.2.2.2 d0 htv
      exact ⟨hinv.insert hd hd0.1 hd0.2 hc hc0,
        CSEInv.insert_ext d0 hinv hd⟩
    · exact ⟨hinv.addConst hd hc, ext_refl⟩
  | op ds yop args =>
    cases ds with
    | nil =>
      simp only [cseInstrStep, substInstr]
      exact ⟨hinv.weaken (fun x hx => List.mem_append_left _ hx), ext_refl⟩
    | cons d rest =>
      cases rest with
      | cons e es =>
        simp only [cseInstrStep, substInstr]
        exact ⟨hinv.weaken (fun x hx => List.mem_append_left _ hx), ext_refl⟩
      | nil =>
        have hd : d ∉ seen := by
          rw [List.nodup_append] at hnd
          exact fun hm => (hnd.2.2 d hm d (by simp [Instr.defs])) rfl
        simp only [cseInstrStep, substInstr]
        by_cases hp : pureOp yop = true
        · rw [if_pos hp]
          have hc : CseDef f (.op yop (substVs σ args)) d := .op hb hi hp
          split
          · rename_i key d0 hfind
            obtain ⟨yop0, args0⟩ := key
            have hpkey : ((yop0, args0) == (yop, substVs σ args)) = true :=
              List.find?_some
                (p := fun x : (Op × List ValId) × ValId =>
                  x.1 == (yop, substVs σ args))
                (a := ((yop0, args0), d0)) hfind
            have hkey : (yop0, args0) = (yop, substVs σ args) :=
              beq_iff_eq.mp hpkey
            have hm : ((yop0, args0), d0) ∈ tab.ops :=
              List.mem_of_find?_eq_some hfind
            have hc0 : CseDef f (.op yop0 args0) d0 := hinv.1.1 hm
            have hc' : CseDef f (.op yop0 args0) d := by
              have hyop : yop0 = yop := congrArg Prod.fst hkey
              have hargs : args0 = substVs σ args := congrArg Prod.snd hkey
              subst yop0
              subst args0
              exact hc
            have htv : d0 ∈ cseTabVals tab := by
              unfold cseTabVals
              exact List.mem_append_left _ (List.mem_map.mpr ⟨((yop0, args0), d0), hm, rfl⟩)
            have hd0 := hinv.2.2.2.2 d0 htv
            by_cases hu : used.contains d = true
            · rw [if_pos hu]
              exact ⟨hinv.weaken (fun x hx => List.mem_append_left _ hx), ext_refl⟩
            · rw [if_neg hu]
              exact ⟨hinv.insert hd hd0.1 hd0.2 hc' hc0,
                CSEInv.insert_ext d0 hinv hd⟩
          · split
            · exact ⟨hinv.addOp hd hc, ext_refl⟩
            · exact ⟨hinv.weaken (fun x hx => List.mem_append_left _ hx), ext_refl⟩
        · rw [if_neg hp]
          exact ⟨hinv.weaken (fun x hx => List.mem_append_left _ hx), ext_refl⟩
  | call ds fid args =>
    simp only [cseInstrStep, substInstr]
    exact ⟨hinv.weaken (by
      intro x hx
      exact List.mem_append_left _ hx), ext_refl⟩

theorem cseInstrStep_state (i : Instr) (acc : List Instr) (tab : CseTab)
    (used : Std.HashSet ValId) (σ : Subst)
    (defined blockDefs : Std.HashSet ValId) :
    (cseInstrStep i ⟨acc, tab, used, σ, defined, blockDefs⟩).2 =
      (cseInstrStep i ⟨[], tab, used, σ, defined, blockDefs⟩).2 := by
  cases i with
  | const d v => simp only [cseInstrStep, substInstr]; split <;> rfl
  | op ds yop args =>
    cases ds with
    | nil => rfl
    | cons d rest =>
      cases rest with
      | cons e es => rfl
      | nil =>
        simp only [cseInstrStep, substInstr]
        split <;> (try split <;> (try split)) <;> rfl
  | call ds fid args => rfl

theorem SubstExt.trans {σ τ υ : Subst} (h1 : SubstExt σ τ) (h2 : SubstExt τ υ) :
    SubstExt σ υ := fun h => h2 (h1 h)

def SubstStable (seen : List ValId) (σ τ : Subst) : Prop :=
  ∀ x ∈ seen, τ[x]? = σ[x]?

theorem SubstStable.trans {seen : List ValId} {σ τ υ : Subst}
    (h1 : SubstStable seen σ τ) (h2 : SubstStable seen τ υ) :
    SubstStable seen σ υ := by
  intro x hx
  rw [h2 x hx, h1 x hx]

theorem cseInstrStep_stable {seen : List ValId} {tab : CseTab}
    {used : Std.HashSet ValId} {σ : Subst} {defined blockDefs : Std.HashSet ValId}
    (i : Instr) (hnd : (seen ++ i.defs).Nodup) :
    SubstStable seen σ
      (cseInstrStep i ⟨[], tab, used, σ, defined, blockDefs⟩).2.2.2.1 := by
  have fresh {d : ValId} (hd : d ∈ i.defs) : d ∉ seen := by
    rw [List.nodup_append] at hnd
    exact fun hm => (hnd.2.2 d hm d hd) rfl
  intro x hx
  cases i with
  | const d v =>
    simp only [cseInstrStep, substInstr]
    split
    · have hne : d ≠ x := by
        intro hdx
        subst x
        exact fresh (by simp [Instr.defs]) hx
      have hdx : (d == x) = false := by simp [hne]
      simp [Std.HashMap.getElem?_insert, hdx]
    · rfl
  | op ds yop args =>
    cases ds with
    | nil => rfl
    | cons d rest =>
      cases rest with
      | cons e es => rfl
      | nil =>
        simp only [cseInstrStep, substInstr]
        split
        · split
          · split
            · rfl
            · have hne : d ≠ x := by
                intro hdx
                subst x
                exact fresh (by simp [Instr.defs]) hx
              have hdx : (d == x) = false := by simp [hne]
              simp [Std.HashMap.getElem?_insert, hdx]
          · split <;> rfl
        · rfl
  | call ds fid args => rfl

theorem cseInstrFold_inv {f : Func} {b : Block} (hb : b ∈ f.blocks.toList)
    {seen : List ValId} {tab : CseTab} {σ : Subst} (hinv : CSEInv f seen tab σ)
    (l : List Instr) (hmem : ∀ i ∈ l, i ∈ b.instrs)
    (hnd : (seen ++ l.flatMap Instr.defs).Nodup) (acc : List Instr)
    (used defined blockDefs : Std.HashSet ValId) :
    let r := l.foldl (fun s i => cseInstrStep i s)
      ⟨acc, tab, used, σ, defined, blockDefs⟩
    CSEInv f (seen ++ l.flatMap Instr.defs) r.2.1 r.2.2.2.1 ∧
      SubstExt σ r.2.2.2.1 := by
  induction l generalizing seen tab σ acc used defined blockDefs with
  | nil => simpa using And.intro hinv (show SubstExt σ σ from fun h => h)
  | cons i is ih =>
    simp only [List.flatMap_cons] at hnd ⊢
    have hprefix : (seen ++ i.defs).Nodup := by
      apply List.Nodup.of_append_left (l₂ := is.flatMap Instr.defs)
      simpa [List.append_assoc] using hnd
    have hone := cseInstrStep_inv hb (used := used) (defined := defined)
      (blockDefs := blockDefs) hinv i
      (hmem i (by simp)) hprefix
    have hstate := cseInstrStep_state i acc tab used σ defined blockDefs
    let s1 := cseInstrStep i ⟨acc, tab, used, σ, defined, blockDefs⟩
    have hinv1 : CSEInv f (seen ++ i.defs) s1.2.1 s1.2.2.2.1 := by
      rw [hstate]
      exact hone.1
    have hext1 : SubstExt σ s1.2.2.2.1 := by
      rw [hstate]
      exact hone.2
    have htail : ((seen ++ i.defs) ++ is.flatMap Instr.defs).Nodup := by
      simpa [List.append_assoc] using hnd
    have hrest := ih hinv1 (fun j hj => hmem j (by simp [hj])) htail
      s1.1 s1.2.2.1 s1.2.2.2.2.1 s1.2.2.2.2.2
    rw [List.foldl_cons]
    refine ⟨?_, hext1.trans hrest.2⟩
    simpa [List.append_assoc] using hrest.1

/-- The positional half of the instruction-fold certificate.  Unlike
`cseInstrFold_inv`, this induction retains the exact processed prefix.  That is
what turns the two executable guards into durable proof fields. -/
theorem cseInstrFold_pos {f : Func} {b : Block} (hb : b ∈ f.blocks.toList)
    (pre l : List Instr) (hseq : b.instrs = pre ++ l)
    (hdefsNodup : b.instrs.flatMap Instr.defs |>.Nodup)
    {seen : List ValId}
    (hseenNodup : (seen ++ l.flatMap Instr.defs).Nodup)
    (acc : List Instr) (tab : CseTab) (used : Std.HashSet ValId) (σ : Subst)
    (defined blockDefs : Std.HashSet ValId)
    (hused : ∀ x, x ∈ used ↔ x ∈ pre.flatMap Instr.uses)
    (hdefined : ∀ x, x ∈ defined ↔ x ∈ pre.flatMap Instr.defs)
    (hblockDefs : ∀ x, x ∈ blockDefs ↔ x ∈ b.instrs.flatMap Instr.defs)
    (hinv : CSEInv f seen tab σ)
    (htab : CseTabPosSound f tab) (hsub : CseSubPosSound f σ) :
    let r := l.foldl (fun s i => cseInstrStep i s)
      ⟨acc, tab, used, σ, defined, blockDefs⟩
    CseTabPosSound f r.2.1 ∧ CseSubPosSound f r.2.2.2.1 := by
  induction l generalizing pre seen acc tab used σ defined blockDefs with
  | nil => exact ⟨htab, hsub⟩
  | cons i is ih =>
    let s1 := cseInstrStep i ⟨acc, tab, used, σ, defined, blockDefs⟩
    have hprefix : (seen ++ i.defs).Nodup := by
      apply List.Nodup.of_append_left (l₂ := is.flatMap Instr.defs)
      simpa [List.append_assoc] using hseenNodup
    have hstepInv := cseInstrStep_inv hb (used := used) (defined := defined)
      (blockDefs := blockDefs) hinv i
      (by rw [hseq]; simp) hprefix
    have hinv1 : CSEInv f (seen ++ i.defs) s1.2.1 s1.2.2.2.1 := by
      have hstate := cseInstrStep_state i acc tab used σ defined blockDefs
      rw [hstate]
      exact hstepInv.1
    have hpos1 : CseTabPosSound f s1.2.1 ∧
        CseSubPosSound f s1.2.2.2.1 := by
      cases hs : substInstr σ i with
      | const d v =>
          simp only [s1, cseInstrStep, hs]
          split
          · exact ⟨htab, hsub.insert (.const hb hseq hs) (by
              intro yop args he
              cases he)⟩
          · exact ⟨htab, hsub⟩
      | op ds yop args =>
          cases ds with
          | nil =>
              simp only [s1, cseInstrStep, hs]
              exact ⟨htab, hsub⟩
          | cons d rest =>
              cases rest with
              | cons e es =>
                  simp only [s1, cseInstrStep, hs]
                  exact ⟨htab, hsub⟩
              | nil =>
                  simp only [s1, cseInstrStep, hs]
                  by_cases hp : pureOp yop = true
                  · rw [if_pos hp]
                    cases hfind : tab.ops.find? (fun x => x.1 == (yop, args)) with
                    | some entry =>
                        obtain ⟨key, d0⟩ := entry
                        by_cases hu : used.contains d = true
                        · simp only [hfind, hu]
                          exact ⟨htab, hsub⟩
                        · have hdpre : d ∉ pre.flatMap Instr.uses := by
                            intro hd
                            have hm : d ∈ used := (hused d).mpr hd
                            exact hu (Std.HashSet.mem_iff_contains.mp hm)
                          have hdnone : σ[d]? = none := by
                            by_contra hn
                            obtain ⟨d1, hd1⟩ := Option.ne_none_iff_exists'.mp hn
                            have hdseen := (hinv.2.2.2.1 hd1).1
                            have hddef : d ∈ i.defs := by
                              have hm : d ∈ (substInstr σ i).defs := by
                                rw [hs]
                                simp [Instr.defs]
                              cases i <;> simpa [substInstr, Instr.defs] using hm
                            have hdfresh : d ∉ seen := by
                              rw [List.nodup_append] at hprefix
                              exact fun hd => hprefix.2.2 d hd d
                                hddef rfl
                            exact hdfresh hdseen
                          have hdrop : CseDropPos f (.op yop args) d :=
                            .op hb hseq hs hdnone hdpre
                          have hm : (key, d0) ∈ tab.ops :=
                            List.mem_of_find?_eq_some hfind
                          have hkey : key = (yop, args) :=
                            beq_iff_eq.mp (List.find?_some
                              (p := fun x : (Op × List ValId) × ValId =>
                                x.1 == (yop, args))
                              (a := (key, d0)) hfind)
                          have hentry0 := htab hm
                          have hentry : CseEntryPos f (.op yop args) d0 := by
                            rw [hkey] at hentry0
                            exact hentry0
                          simp only [hfind, hu]
                          exact ⟨htab, hsub.insert hdrop (d0 := d0) (by
                            intro yop' args' he
                            cases he
                            exact hentry)⟩
                    | none =>
                        by_cases hg : args.all (fun a =>
                            defined.contains a || !blockDefs.contains a) = true
                        · have hargs : ∀ a ∈ args,
                              a ∉ (i :: is).flatMap Instr.defs := by
                            intro a ha hais
                            have hga := List.all_eq_true.mp hg a ha
                            rw [Bool.or_eq_true] at hga
                            have hablock : a ∈ blockDefs := by
                              apply (hblockDefs a).mpr
                              rw [hseq]
                              simp only [List.flatMap_append, List.flatMap_cons,
                                List.mem_append]
                              exact Or.inr (by simpa [List.flatMap_cons] using hais)
                            rcases hga with hbefore | houtside
                            · have hapre : a ∈ pre.flatMap Instr.defs :=
                                (hdefined a).mp
                                  (Std.HashSet.contains_iff_mem.mp hbefore)
                              have hnd := hdefsNodup
                              rw [hseq, List.flatMap_append,
                                List.nodup_append] at hnd
                              exact (hnd.2.2 a hapre a hais) rfl
                            · have hc := Std.HashSet.mem_iff_contains.mp hablock
                              rw [hc] at houtside
                              simp at houtside
                          have hentry : CseEntryPos f (.op yop args) d :=
                            .op hb hseq hs hargs
                          simp only [hfind, hg]
                          exact ⟨htab.addOp hentry, hsub⟩
                        · simp only [hfind, hg]
                          exact ⟨htab, hsub⟩
                  · rw [if_neg hp]
                    exact ⟨htab, hsub⟩
      | call ds fid args =>
          simp only [s1, cseInstrStep, hs]
          exact ⟨htab, hsub⟩
    have hused1 : ∀ x, x ∈ s1.2.2.1 ↔
        x ∈ (pre ++ [i]).flatMap Instr.uses := by
      intro x
      simp only [s1, cseInstrStep_used, mem_fold_insert_iff, hused]
      simp
    have hdefined1 : ∀ x, x ∈ s1.2.2.2.2.1 ↔
        x ∈ (pre ++ [i]).flatMap Instr.defs := by
      intro x
      simp only [s1, cseInstrStep_defined, mem_fold_insert_iff, hdefined]
      simp
    have hseq1 : b.instrs = (pre ++ [i]) ++ is := by
      simpa [List.append_assoc] using hseq
    have hseenNodup1 : ((seen ++ i.defs) ++ is.flatMap Instr.defs).Nodup := by
      simpa [List.append_assoc] using hseenNodup
    have hblockDefs1 : ∀ x, x ∈ s1.2.2.2.2.2 ↔
        x ∈ b.instrs.flatMap Instr.defs := by
      intro x
      simp only [s1, cseInstrStep_blockDefs]
      exact hblockDefs x
    rw [List.foldl_cons]
    exact ih (pre := pre ++ [i]) (hseq := hseq1)
      (seen := seen ++ i.defs) (hseenNodup := hseenNodup1)
      (acc := s1.1) (tab := s1.2.1) (used := s1.2.2.1)
      (σ := s1.2.2.2.1) (defined := s1.2.2.2.2.1)
      (blockDefs := s1.2.2.2.2.2) hused1 hdefined1 hblockDefs1
      hinv1 hpos1.1 hpos1.2

theorem cseInstrFold_stable {f : Func} {b : Block} (hb : b ∈ f.blocks.toList)
    {seen : List ValId} {tab : CseTab} {σ : Subst} (hinv : CSEInv f seen tab σ)
    (l : List Instr) (hmem : ∀ i ∈ l, i ∈ b.instrs)
    (hnd : (seen ++ l.flatMap Instr.defs).Nodup) (acc : List Instr)
    (used defined blockDefs : Std.HashSet ValId) :
    SubstStable seen σ
      (l.foldl (fun s i => cseInstrStep i s)
        ⟨acc, tab, used, σ, defined, blockDefs⟩).2.2.2.1 := by
  induction l generalizing seen tab σ acc used defined blockDefs with
  | nil => intro x hx; rfl
  | cons i is ih =>
    simp only [List.flatMap_cons] at hnd
    have hprefix : (seen ++ i.defs).Nodup := by
      apply List.Nodup.of_append_left (l₂ := is.flatMap Instr.defs)
      simpa [List.append_assoc] using hnd
    have hone := cseInstrStep_inv hb (used := used) (defined := defined)
      (blockDefs := blockDefs) hinv i
      (hmem i (by simp)) hprefix
    have hstate := cseInstrStep_state i acc tab used σ defined blockDefs
    let s1 := cseInstrStep i ⟨acc, tab, used, σ, defined, blockDefs⟩
    have hinv1 : CSEInv f (seen ++ i.defs) s1.2.1 s1.2.2.2.1 := by
      rw [hstate]
      exact hone.1
    have htail : ((seen ++ i.defs) ++ is.flatMap Instr.defs).Nodup := by
      simpa [List.append_assoc] using hnd
    have hs1 : SubstStable seen σ s1.2.2.2.1 := by
      rw [hstate]
      exact cseInstrStep_stable i hprefix
    have hrest := ih hinv1 (fun j hj => hmem j (by simp [hj])) htail
      s1.1 s1.2.2.1 s1.2.2.2.2.1 s1.2.2.2.2.2
    rw [List.foldl_cons]
    exact hs1.trans (fun x hx => hrest x (List.mem_append_left _ hx))

theorem CSEInv.emptyTab {f : Func} {seen : List ValId} {tab : CseTab} {σ : Subst}
    (h : CSEInv f seen tab σ) : CSEInv f seen {} σ := by
  refine ⟨⟨by simp, by simp⟩, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
  simp [cseTabVals]

theorem cseTabVals_inheritTab {tab : CseTab} {ps : List ValId} {x : ValId}
    (hx : x ∈ cseTabVals (Passes.inheritTab tab ps)) :
    x ∈ cseTabVals tab := by
  simp only [cseTabVals, Passes.inheritTab, List.mem_append, List.mem_map,
    List.mem_filter] at hx ⊢
  rcases hx with ⟨e, ⟨he, -⟩, rfl⟩ | ⟨e, ⟨he, -⟩, rfl⟩
  · exact Or.inl ⟨e, he, rfl⟩
  · exact Or.inr ⟨e, he, rfl⟩

theorem CSEInv.inheritTab {f : Func} {seen : List ValId} {tab : CseTab}
    {σ : Subst} (h : CSEInv f seen tab σ) (ps : List ValId) :
    CSEInv f seen (Passes.inheritTab tab ps) σ := by
  refine ⟨⟨?_, ?_⟩, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
  · intro yop args d hm
    exact h.1.1 (List.mem_filter.mp hm).1
  · intro v d hm
    exact h.1.2 (List.mem_filter.mp hm).1
  · intro x hx
    exact h.2.2.2.2 x (cseTabVals_inheritTab hx)

theorem CSEInv.transportTable {f : Func} {seen seen' : List ValId}
    {tab tab' : CseTab} {σ τ : Subst}
    (hold : CSEInv f seen tab σ) (hnew : CSEInv f seen' tab' τ)
    (hseen : ∀ x ∈ seen, x ∈ seen') (hstable : SubstStable seen σ τ) :
    CSEInv f seen' tab τ := by
  refine ⟨hold.1, hnew.2.1, hnew.2.2.1, hnew.2.2.2.1, ?_⟩
  intro x hx
  have ho := hold.2.2.2.2 x hx
  refine ⟨hseen x ho.1, ?_⟩
  rw [hstable x ho.1]
  exact ho.2

def cseSeen (f : Func) (n : Nat) : List ValId :=
  (f.blocks.toList.take n).flatMap fun b => b.instrs.flatMap Instr.defs

theorem cseSeen_succ {f : Func} {n : Nat} {b : Block} (h : f.blocks[n]? = some b) :
    cseSeen f (n + 1) = cseSeen f n ++ b.instrs.flatMap Instr.defs := by
  have hl : f.blocks.toList[n]? = some b := by simpa using h
  simp [cseSeen, List.take_add_one, hl]

theorem cseSeen_sublist (f : Func) (n : Nat) :
    (cseSeen f n).Sublist
      (f.blocks.toList.flatMap fun b => b.instrs.flatMap Instr.defs) :=
  (List.take_sublist n f.blocks.toList).flatMap _

theorem getElem!_eq_getElem {α : Type} [Inhabited α] {a : Array α} {i : Nat}
    (h : i < a.size) : a[i]! = a[i] := by
  simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_getElem h]

@[simp] theorem sourceEdgeStep_size (bi : BlockId) (acc : Array (List BlockId))
    (e : Edge) : (sourceEdgeStep bi acc e).size = acc.size := by
  simp [sourceEdgeStep]

theorem sourceEdgeStep_mem_self {bi : BlockId} {acc : Array (List BlockId)}
    {e : Edge} (ht : e.target < acc.size) :
    bi ∈ (sourceEdgeStep bi acc e)[e.target]! := by
  rw [sourceEdgeStep, getElem!_eq_getElem (by simp [ht]),
    Array.getElem_setIfInBounds_self]
  simp

theorem sourceEdgeStep_mem_preserve {bi x q : BlockId}
    {acc : Array (List BlockId)} {e : Edge} (hq : q < acc.size)
    (hx : x ∈ acc[q]!) : x ∈ (sourceEdgeStep bi acc e)[q]! := by
  by_cases heq : q = e.target
  · subst q
    rw [sourceEdgeStep, getElem!_eq_getElem (by simp [hq]),
      Array.getElem_setIfInBounds_self]
    exact List.mem_cons_of_mem _ hx
  · rw [sourceEdgeStep, getElem!_eq_getElem (by simp [hq]),
      Array.getElem_setIfInBounds_ne hq (Ne.symm heq), ← getElem!_eq_getElem hq]
    exact hx

theorem sourceEdgeFold_mem_preserve {bi x q : BlockId}
    {acc : Array (List BlockId)} (hq : q < acc.size) (hx : x ∈ acc[q]!)
    (es : List Edge) :
    x ∈ (es.foldl (sourceEdgeStep bi) acc)[q]! := by
  induction es generalizing acc with
  | nil => exact hx
  | cons e es ih =>
      rw [List.foldl_cons]
      exact ih (by simpa using hq) (sourceEdgeStep_mem_preserve hq hx)

theorem sourceEdgeFold_mem {bi : BlockId} {acc : Array (List BlockId)}
    {e : Edge} {es : List Edge} (he : e ∈ es) (ht : e.target < acc.size) :
    bi ∈ (es.foldl (sourceEdgeStep bi) acc)[e.target]! := by
  induction es generalizing acc with
  | nil => simp at he
  | cons e0 es ih =>
      rw [List.foldl_cons]
      rcases List.mem_cons.mp he with rfl | he
      · exact sourceEdgeFold_mem_preserve (by simpa using ht)
          (sourceEdgeStep_mem_self ht) es
      · exact ih he (by simpa using ht)

@[simp] theorem sourceBlockStep_size (f : Func) (acc : Array (List BlockId))
    (bi : BlockId) : (sourceBlockStep f acc bi).size = acc.size := by
  unfold sourceBlockStep
  induction f.blocks[bi]!.term.edges generalizing acc with
  | nil => rfl
  | cons e es ih => simpa using ih (sourceEdgeStep bi acc e)

theorem sourceBlockStep_mem_preserve {f : Func} {x q : BlockId}
    {acc : Array (List BlockId)} (hq : q < acc.size) (hx : x ∈ acc[q]!)
    (bi : BlockId) : x ∈ (sourceBlockStep f acc bi)[q]! := by
  exact sourceEdgeFold_mem_preserve hq hx _

theorem sourceBlockStep_mem {f : Func} {bi : BlockId} {acc : Array (List BlockId)}
    {e : Edge} (he : e ∈ f.blocks[bi]!.term.edges) (ht : e.target < acc.size) :
    bi ∈ (sourceBlockStep f acc bi)[e.target]! := by
  exact sourceEdgeFold_mem he ht

theorem sourceBlockFold_mem_preserve {f : Func} {x q : BlockId}
    {acc : Array (List BlockId)} (hq : q < acc.size) (hx : x ∈ acc[q]!)
    (bis : List BlockId) : x ∈ (bis.foldl (sourceBlockStep f) acc)[q]! := by
  induction bis generalizing acc with
  | nil => exact hx
  | cons bi bis ih =>
      rw [List.foldl_cons]
      exact ih (by simpa using hq) (sourceBlockStep_mem_preserve hq hx bi)

theorem sourceBlockFold_mem {f : Func} {bi : BlockId} {acc : Array (List BlockId)}
    {e : Edge} {bis : List BlockId} (hbi : bi ∈ bis)
    (he : e ∈ f.blocks[bi]!.term.edges) (ht : e.target < acc.size) :
    bi ∈ (bis.foldl (sourceBlockStep f) acc)[e.target]! := by
  induction bis generalizing acc with
  | nil => simp at hbi
  | cons bj bis ih =>
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hbi with rfl | hbi
      · exact sourceBlockFold_mem_preserve (by simpa using ht)
          (sourceBlockStep_mem he ht) bis
      · exact ih hbi (by simpa using ht)

theorem mem_inEdgeSources {f : Func} {bi : BlockId} {b : Block} {e : Edge}
    (hb : f.blocks[bi]? = some b) (he : e ∈ b.term.edges)
    (ht : e.target < f.blocks.size) : bi ∈ (inEdgeSources f)[e.target]! := by
  have hbi : bi ∈ List.range' 0 f.blocks.size 1 := by
    rw [List.mem_range'_1]
    exact ⟨Nat.zero_le _, by simpa using (Array.getElem?_eq_some_iff.mp hb).1⟩
  have hbang : f.blocks[bi]! = b := by
    rw [getElem!_eq_getElem (Array.getElem?_eq_some_iff.mp hb).1]
    exact (Array.getElem?_eq_some_iff.mp hb).2
  rw [inEdgeSources_eq_fold]
  apply sourceBlockFold_mem hbi (ht := by simpa using ht)
  simpa [hbang] using he

theorem inEdgeSources_single_eq {f : Func} {bi p : BlockId} {b : Block} {e : Edge}
    (hb : f.blocks[bi]? = some b) (he : e ∈ b.term.edges)
    (ht : e.target < f.blocks.size) (hs : (inEdgeSources f)[e.target]! = [p]) :
    bi = p := by
  have hm := mem_inEdgeSources hb he ht
  rw [hs] at hm
  simpa using hm

def CSEPrefixInv (f : Func) (n : Nat) : Prop :=
  let st := csePrefix f n
  CSEInv f (cseSeen f n) {} st.2.2
    ∧ st.2.1.size = f.blocks.size
    ∧ ∀ p < n, CSEInv f (cseSeen f n) st.2.1[p]! st.2.2

theorem csePrefixInv_zero (f : Func) : CSEPrefixInv f 0 := by
  refine ⟨cseInv_empty f, by simp [csePrefix], ?_⟩
  intro p hp
  omega

theorem cseEntryTab_inv {f : Func} {n : Nat} (hpre : CSEPrefixInv f n) :
    CSEInv f (cseSeen f n)
      (cseEntryTab f (inEdgeSources f) (csePrefix f n).2.1 n)
      (csePrefix f n).2.2 := by
  by_cases he : (n == f.entry) = true
  · rw [cseEntryTab, if_pos he]
    exact hpre.1.emptyTab
  · cases hs : (inEdgeSources f)[n]! with
    | nil =>
      rw [cseEntryTab, if_neg he, hs]
      exact hpre.1.emptyTab
    | cons p ps =>
      cases ps with
      | nil =>
        by_cases hp : p < n
        · simpa [cseEntryTab, he, hs, hp] using
            (hpre.2.2 p hp).inheritTab f.blocks[n]!.params
        · simpa [cseEntryTab, he, hs, hp] using hpre.1.emptyTab
      | cons q qs =>
        rw [cseEntryTab, if_neg he, hs]
        exact hpre.1.emptyTab

theorem csePrefixInv_succ {f : Func} {n : Nat} (hnd : f.allDefs.Nodup)
    (hpre : CSEPrefixInv f n) (hn : n < f.blocks.size) :
    CSEPrefixInv f (n + 1) := by
  let b := f.blocks[n]
  have hbget : f.blocks[n]? = some b := by
    rw [Array.getElem?_eq_getElem hn]
  have hbBang : f.blocks[n]! = b := by
    rw [getElem!_eq_getElem hn]
  have hbmem : b ∈ f.blocks.toList := by
    obtain ⟨hlt, hget⟩ := Array.getElem?_eq_some_iff.mp hbget
    exact List.mem_iff_getElem.mpr ⟨n, by simpa using hlt, by simpa using hget⟩
  have hseen : cseSeen f (n + 1) =
      cseSeen f n ++ b.instrs.flatMap Instr.defs := cseSeen_succ hbget
  have hseenNodup : (cseSeen f n ++ b.instrs.flatMap Instr.defs).Nodup := by
    rw [← hseen]
    exact (instrDefs_nodup hnd).sublist (cseSeen_sublist f (n + 1))
  let tab := cseEntryTab f (inEdgeSources f) (csePrefix f n).2.1 n
  let r := b.instrs.foldl (fun s i => cseInstrStep i s)
    ⟨[], tab, ∅, (csePrefix f n).2.2, ∅, cseBlockDefs b⟩
  have htab : CSEInv f (cseSeen f n) tab (csePrefix f n).2.2 :=
    cseEntryTab_inv hpre
  have hr := cseInstrFold_inv hbmem htab b.instrs (fun i hi => hi)
    hseenNodup [] ∅ ∅ (cseBlockDefs b)
  have hstable := cseInstrFold_stable hbmem htab b.instrs (fun i hi => hi)
    hseenNodup [] ∅ ∅ (cseBlockDefs b)
  change CSEPrefixInv f (n + 1)
  rw [CSEPrefixInv, csePrefix_succ]
  simp only [cseBlockStep]
  rw [hbBang, hseen]
  change CSEInv f (cseSeen f n ++ b.instrs.flatMap Instr.defs) {} r.2.2.2.1
      ∧ ((csePrefix f n).2.1.setIfInBounds n r.2.1).size = f.blocks.size
      ∧ ∀ p < n + 1,
        CSEInv f (cseSeen f n ++ b.instrs.flatMap Instr.defs)
          ((csePrefix f n).2.1.setIfInBounds n r.2.1)[p]! r.2.2.2.1
  refine ⟨hr.1.emptyTab, by simpa using hpre.2.1, ?_⟩
  intro p hp
  by_cases hpn : p = n
  · subst p
    have hn0 : n < (csePrefix f n).2.1.size := by rw [hpre.2.1]; exact hn
    have hn1 : n < ((csePrefix f n).2.1.setIfInBounds n r.2.1).size := by simpa
    rw [getElem!_eq_getElem hn1, Array.getElem_setIfInBounds_self]
    exact hr.1
  · have hplt : p < n := by omega
    have hp0 : p < (csePrefix f n).2.1.size := by rw [hpre.2.1]; omega
    have hp1 : p < ((csePrefix f n).2.1.setIfInBounds n r.2.1).size := by simpa
    rw [getElem!_eq_getElem hp1,
      Array.getElem_setIfInBounds_ne hp0 (Ne.symm hpn), ← getElem!_eq_getElem hp0]
    exact (hpre.2.2 p hplt).transportTable hr.1
      (fun x hx => List.mem_append_left _ hx) hstable

theorem csePrefixInv {f : Func} (hnd : f.allDefs.Nodup) :
    ∀ n ≤ f.blocks.size, CSEPrefixInv f n := by
  intro n
  induction n with
  | zero => intro _; exact csePrefixInv_zero f
  | succ n ih =>
    intro hn
    exact csePrefixInv_succ hnd (ih (by omega)) (by omega)

/-- The guard-projection companion to `CSEPrefixInv`.  Tables retain the
suffix-stability witness from the instruction that created each entry, while
the global substitution retains the prefix-use witness from every dropped
operation. -/
def CSEPrefixPosInv (f : Func) (n : Nat) : Prop :=
  let st := csePrefix f n
  CseSubPosSound f st.2.2 ∧
    ∀ p < n, CseTabPosSound f st.2.1[p]!

theorem csePrefixPosInv_zero (f : Func) : CSEPrefixPosInv f 0 := by
  refine ⟨?_, ?_⟩
  · intro d d0 h
    simp at h
  · intro p hp
    omega

theorem cseEntryTab_pos {f : Func} {n : Nat}
    (hpre : CSEPrefixPosInv f n) :
    CseTabPosSound f
      (cseEntryTab f (inEdgeSources f) (csePrefix f n).2.1 n) := by
  by_cases he : (n == f.entry) = true
  · rw [cseEntryTab, if_pos he]
    exact CseTabPosSound.empty f
  · cases hs : (inEdgeSources f)[n]! with
    | nil =>
        rw [cseEntryTab, if_neg he, hs]
        exact CseTabPosSound.empty f
    | cons p ps =>
        cases ps with
        | nil =>
            by_cases hp : p < n
            · have htab : CseTabPosSound f (csePrefix f n).2.1[p]! :=
                hpre.2 p hp
              simpa [cseEntryTab, he, hs, hp] using
                CseTabPosSound.inheritTab htab f.blocks[n]!.params
            · simpa [cseEntryTab, he, hs, hp] using CseTabPosSound.empty f
        | cons q qs =>
            rw [cseEntryTab, if_neg he, hs]
            exact CseTabPosSound.empty f

theorem csePrefixPosInv_succ {f : Func} {n : Nat}
    (hnd : f.allDefs.Nodup) (hpre : CSEPrefixPosInv f n)
    (hn : n < f.blocks.size) : CSEPrefixPosInv f (n + 1) := by
  let b := f.blocks[n]
  have hbget : f.blocks[n]? = some b := Array.getElem?_eq_getElem hn
  have hbBang : f.blocks[n]! = b := by rw [getElem!_eq_getElem hn]
  have hbmem : b ∈ f.blocks.toList := by
    exact List.mem_iff_getElem.mpr ⟨n, by simpa using hn,
      by simpa using (Array.getElem?_eq_some_iff.mp hbget).2⟩
  have hregular := csePrefixInv hnd n (Nat.le_of_lt hn)
  let tab := cseEntryTab f (inEdgeSources f) (csePrefix f n).2.1 n
  let r := b.instrs.foldl (fun s i => cseInstrStep i s)
    ⟨[], tab, ∅, (csePrefix f n).2.2, ∅, cseBlockDefs b⟩
  have hbdefs : b.instrs.flatMap Instr.defs |>.Nodup := by
    have hall := instrDefs_nodup hnd
    have hsub : (b.instrs.flatMap Instr.defs).Sublist
        (f.blocks.toList.flatMap fun b => b.instrs.flatMap Instr.defs) := by
      simpa using (List.Sublist.flatMap (List.singleton_sublist.mpr hbmem)
        (fun b : Block => b.instrs.flatMap Instr.defs))
    exact hall.sublist hsub
  have hseenNodup :
      (cseSeen f n ++ b.instrs.flatMap Instr.defs).Nodup := by
    rw [← cseSeen_succ hbget]
    exact (instrDefs_nodup hnd).sublist (cseSeen_sublist f (n + 1))
  have hr := cseInstrFold_pos hbmem [] b.instrs rfl hbdefs
    (seen := cseSeen f n) hseenNodup [] tab ∅
    (csePrefix f n).2.2 ∅ (cseBlockDefs b)
    (by simp) (by simp) (fun x => mem_cseBlockDefs)
    (cseEntryTab_inv hregular) (cseEntryTab_pos hpre) hpre.1
  change CSEPrefixPosInv f (n + 1)
  rw [CSEPrefixPosInv, csePrefix_succ]
  simp only [cseBlockStep]
  rw [hbBang]
  change CseSubPosSound f r.2.2.2.1 ∧
    ∀ p < n + 1,
      CseTabPosSound f
        ((csePrefix f n).2.1.setIfInBounds n r.2.1)[p]!
  refine ⟨hr.2, ?_⟩
  intro p hp
  by_cases hpn : p = n
  · subst p
    have hn0 : n < (csePrefix f n).2.1.size := by
      rw [hregular.2.1]
      exact hn
    have hn1 : n < ((csePrefix f n).2.1.setIfInBounds n r.2.1).size := by
      simpa
    rw [getElem!_eq_getElem hn1, Array.getElem_setIfInBounds_self]
    exact hr.1
  · have hplt : p < n := by omega
    have hp0 : p < (csePrefix f n).2.1.size := by
      rw [hregular.2.1]
      omega
    have hp1 : p < ((csePrefix f n).2.1.setIfInBounds n r.2.1).size := by
      simpa
    rw [getElem!_eq_getElem hp1,
      Array.getElem_setIfInBounds_ne hp0 (Ne.symm hpn), ← getElem!_eq_getElem hp0]
    exact hpre.2 p hplt

theorem csePrefixPosInv {f : Func} (hnd : f.allDefs.Nodup) :
    ∀ n ≤ f.blocks.size, CSEPrefixPosInv f n := by
  intro n
  induction n with
  | zero => intro _; exact csePrefixPosInv_zero f
  | succ n ih =>
      intro hn
      exact csePrefixPosInv_succ hnd (ih (by omega)) (by omega)

theorem cseFinalSubSound {f : Func} (hnd : f.allDefs.Nodup) :
    CseSubSound f (csePrefix f f.blocks.size).2.2 := by
  have hfinal := csePrefixInv hnd f.blocks.size (Nat.le_refl _)
  have hdef : CseSubDefSound f (csePrefix f f.blocks.size).2.2 :=
    hfinal.1.2.1
  have hposFinal := csePrefixPosInv hnd f.blocks.size (Nat.le_refl _)
  have hpos : CseSubPosSound f (csePrefix f f.blocks.size).2.2 :=
    hposFinal.1
  exact ⟨hdef, hpos⟩

/-- The representative of every final CSE alias was processed strictly before
its dropped destination.  This is the global fold-order companion to the local
prefix/suffix certificates in `CseSubPosSound`. -/
def AliasOrdered (seen : List ValId) (σ : Subst) : Prop :=
  ∀ d d0, σ[d]? = some d0 →
    ∃ pre mid post, seen = pre ++ (d0 :: mid) ++ d :: post

theorem AliasOrdered.empty : AliasOrdered [] (∅ : Subst) := by
  intro d d0 h
  simp at h

theorem AliasOrdered.insert {seen : List ValId} {σ : Subst}
    (ho : AliasOrdered seen σ) {d d0 : ValId}
    (hd : d ∉ seen) (hd0 : d0 ∈ seen) :
    AliasOrdered (seen ++ [d]) (σ.insert d d0) := by
  intro x y hxy
  rw [Std.HashMap.getElem?_insert] at hxy
  split at hxy
  · rename_i heq
    have hxd : x = d := (beq_iff_eq.mp heq).symm
    subst x
    have hyd : y = d0 := (Option.some.inj hxy).symm
    subst y
    obtain ⟨pre, post, hseen⟩ := List.mem_iff_append.mp hd0
    exact ⟨pre, post, [], by simp [hseen, List.append_assoc]⟩
  · obtain ⟨pre, mid, post, hseen⟩ := ho x y hxy
    exact ⟨pre, mid, post ++ [d], by simp [hseen, List.append_assoc]⟩

theorem AliasOrdered.weaken {seen seen' : List ValId} {σ : Subst}
    (ho : AliasOrdered seen σ) (hs : ∃ tail, seen' = seen ++ tail) :
    AliasOrdered seen' σ := by
  obtain ⟨tail, rfl⟩ := hs
  intro d d0 h
  obtain ⟨pre, mid, post, hseen⟩ := ho d d0 h
  exact ⟨pre, mid, post ++ tail, by simp [hseen, List.append_assoc]⟩

theorem AliasOrdered.step {f : Func} {b : Block} (hb : b ∈ f.blocks.toList)
    {seen : List ValId} {tab : CseTab} {used : Std.HashSet ValId} {σ : Subst}
    {defined blockDefs : Std.HashSet ValId}
    (hinv : CSEInv f seen tab σ) (ho : AliasOrdered seen σ)
    (i : Instr) (_hi : i ∈ b.instrs) (hnd : (seen ++ i.defs).Nodup) :
    let r := cseInstrStep i ⟨[], tab, used, σ, defined, blockDefs⟩
    AliasOrdered (seen ++ i.defs) r.2.2.2.1 := by
  have hkeep : AliasOrdered (seen ++ i.defs) σ :=
    ho.weaken ⟨i.defs, rfl⟩
  cases i with
  | const d v =>
      have hd : d ∉ seen := by
        rw [List.nodup_append] at hnd
        exact fun hm => (hnd.2.2 d hm d (by simp [Instr.defs])) rfl
      simp only [cseInstrStep, substInstr]
      split
      · rename_i w d0 hfind
        have hm : (w, d0) ∈ tab.consts := List.mem_of_find?_eq_some hfind
        have hd0 : d0 ∈ seen := (hinv.2.2.2.2 d0 (by
          exact List.mem_append_right _
            (List.mem_map.mpr ⟨(w, d0), hm, rfl⟩))).1
        change AliasOrdered (seen ++ [d]) (σ.insert d d0)
        exact ho.insert hd hd0
      · change AliasOrdered (seen ++ [d]) σ
        exact hkeep
  | op ds yop args =>
      cases ds with
      | nil =>
          simp only [cseInstrStep, substInstr, Instr.defs, List.append_nil]
          intro d d0 h
          exact ho d d0 h
      | cons d rest =>
          cases rest with
          | cons e es =>
              change AliasOrdered (seen ++ d :: e :: es) σ
              exact hkeep
          | nil =>
              have hd : d ∉ seen := by
                rw [List.nodup_append] at hnd
                exact fun hm => (hnd.2.2 d hm d (by simp [Instr.defs])) rfl
              simp only [cseInstrStep, substInstr]
              split
              · split
                · rename_i key d0 hfind
                  split
                  · change AliasOrdered (seen ++ [d]) σ
                    exact hkeep
                  · have hm : (key, d0) ∈ tab.ops :=
                      List.mem_of_find?_eq_some hfind
                    have hd0 : d0 ∈ seen := (hinv.2.2.2.2 d0 (by
                      exact List.mem_append_left _
                        (List.mem_map.mpr ⟨(key, d0), hm, rfl⟩))).1
                    change AliasOrdered (seen ++ [d]) (σ.insert d d0)
                    exact ho.insert hd hd0
                · split <;> change AliasOrdered (seen ++ [d]) σ <;>
                    exact hkeep
              · change AliasOrdered (seen ++ [d]) σ
                exact hkeep
  | call ds fid args =>
      change AliasOrdered (seen ++ ds) σ
      exact hkeep

theorem cseInstrFold_ordered {f : Func} {b : Block}
    (hb : b ∈ f.blocks.toList) {seen : List ValId} {tab : CseTab} {σ : Subst}
    (hinv : CSEInv f seen tab σ) (ho : AliasOrdered seen σ)
    (l : List Instr) (hmem : ∀ i ∈ l, i ∈ b.instrs)
    (hnd : (seen ++ l.flatMap Instr.defs).Nodup) (acc : List Instr)
    (used defined blockDefs : Std.HashSet ValId) :
    let r := l.foldl (fun s i => cseInstrStep i s)
      ⟨acc, tab, used, σ, defined, blockDefs⟩
    AliasOrdered (seen ++ l.flatMap Instr.defs) r.2.2.2.1 := by
  induction l generalizing seen tab σ acc used defined blockDefs with
  | nil =>
      simp only [List.foldl_nil, List.flatMap_nil, List.append_nil]
      intro d d0 h
      exact ho d d0 h
  | cons i is ih =>
      have hprefix : (seen ++ i.defs).Nodup := by
        apply List.Nodup.of_append_left (l₂ := is.flatMap Instr.defs)
        simpa [List.append_assoc] using hnd
      have hstep := cseInstrStep_inv hb (used := used) (defined := defined)
        (blockDefs := blockDefs) hinv i (hmem i (by simp)) hprefix
      have hord := AliasOrdered.step hb (used := used) (defined := defined)
        (blockDefs := blockDefs) hinv ho i (hmem i (by simp)) hprefix
      let s1 := cseInstrStep i ⟨acc, tab, used, σ, defined, blockDefs⟩
      have hstate := cseInstrStep_state i acc tab used σ defined blockDefs
      have hinv1 : CSEInv f (seen ++ i.defs) s1.2.1 s1.2.2.2.1 := by
        rw [hstate]
        exact hstep.1
      have hord1 : AliasOrdered (seen ++ i.defs) s1.2.2.2.1 := by
        rw [hstate]
        exact hord
      rw [List.foldl_cons]
      simpa [List.flatMap_cons, List.append_assoc] using
        ih hinv1 hord1 (fun j hj => hmem j (by simp [hj]))
          (by simpa [List.flatMap_cons, List.append_assoc] using hnd)
          s1.1 s1.2.2.1 s1.2.2.2.2.1 s1.2.2.2.2.2

theorem csePrefix_ordered {f : Func} (hnd : f.allDefs.Nodup) :
    ∀ n ≤ f.blocks.size,
      AliasOrdered (cseSeen f n) (csePrefix f n).2.2 := by
  intro n hn
  induction n with
  | zero => exact AliasOrdered.empty
  | succ n ih =>
      have hnlt : n < f.blocks.size := by omega
      let b := f.blocks[n]
      have hb : f.blocks[n]? = some b := Array.getElem?_eq_getElem hnlt
      have hbmem : b ∈ f.blocks.toList := by
        exact List.mem_iff_getElem.mpr ⟨n, by simpa using hnlt,
          by simpa using (Array.getElem?_eq_some_iff.mp hb).2⟩
      have hpre := csePrefixInv hnd n (Nat.le_of_lt hnlt)
      let tab := cseEntryTab f (inEdgeSources f) (csePrefix f n).2.1 n
      let r := b.instrs.foldl (fun s i => cseInstrStep i s)
        ⟨[], tab, ∅, (csePrefix f n).2.2, ∅, cseBlockDefs b⟩
      have hoN : AliasOrdered (cseSeen f n) (csePrefix f n).2.2 :=
        ih (Nat.le_of_lt hnlt)
      have hr := cseInstrFold_ordered hbmem
        (hinv := cseEntryTab_inv hpre) (ho := hoN)
        b.instrs (fun i hi => hi)
        (by
          rw [← cseSeen_succ hb]
          exact (instrDefs_nodup hnd).sublist (cseSeen_sublist f (n + 1)))
        [] ∅ ∅ (cseBlockDefs b)
      rw [csePrefix_succ]
      simp only [cseBlockStep]
      have hbang : f.blocks[n]! = b := by
        rw [getElem!_eq_getElem hnlt]
      rw [hbang]
      rw [cseSeen_succ hb]
      exact hr

theorem cseEntryTab_sound {f : Func} (hnd : f.allDefs.Nodup)
    {n : Nat} (hn : n ≤ f.blocks.size) :
    CseTabSound f
      (cseEntryTab f (inEdgeSources f) (csePrefix f n).2.1 n) := by
  have hregular := csePrefixInv hnd n hn
  have hpos := csePrefixPosInv hnd n hn
  exact ⟨(cseEntryTab_inv hregular).1, cseEntryTab_pos hpos⟩

theorem csePrefix_ext_succ {f : Func} {n : Nat} (hnd : f.allDefs.Nodup)
    (hn : n < f.blocks.size) :
    SubstExt (csePrefix f n).2.2 (csePrefix f (n + 1)).2.2 := by
  let b := f.blocks[n]
  have hbget : f.blocks[n]? = some b := by rw [Array.getElem?_eq_getElem hn]
  have hbmem : b ∈ f.blocks.toList := by
    obtain ⟨hlt, hget⟩ := Array.getElem?_eq_some_iff.mp hbget
    exact List.mem_iff_getElem.mpr ⟨n, by simpa using hlt, by simpa using hget⟩
  have hseen := cseSeen_succ hbget
  have hseenNodup : (cseSeen f n ++ b.instrs.flatMap Instr.defs).Nodup := by
    rw [← hseen]
    exact (instrDefs_nodup hnd).sublist (cseSeen_sublist f (n + 1))
  have hpre := csePrefixInv hnd n (Nat.le_of_lt hn)
  let tab := cseEntryTab f (inEdgeSources f) (csePrefix f n).2.1 n
  have htab : CSEInv f (cseSeen f n) tab (csePrefix f n).2.2 :=
    cseEntryTab_inv hpre
  have hr := cseInstrFold_inv hbmem htab b.instrs (fun i hi => hi)
    hseenNodup [] ∅ ∅ (cseBlockDefs b)
  rw [csePrefix_succ]
  simp only [cseBlockStep]
  have hbBang : f.blocks[n]! = b := by rw [getElem!_eq_getElem hn]
  rw [hbBang]
  intro x y hxy
  exact hr.2 hxy

theorem csePrefix_stable_succ {f : Func} {n : Nat} (hnd : f.allDefs.Nodup)
    (hn : n < f.blocks.size) :
    SubstStable (cseSeen f n) (csePrefix f n).2.2 (csePrefix f (n + 1)).2.2 := by
  let b := f.blocks[n]
  have hbget : f.blocks[n]? = some b := by rw [Array.getElem?_eq_getElem hn]
  have hbmem : b ∈ f.blocks.toList := by
    obtain ⟨hlt, hget⟩ := Array.getElem?_eq_some_iff.mp hbget
    exact List.mem_iff_getElem.mpr ⟨n, by simpa using hlt, by simpa using hget⟩
  have hseen := cseSeen_succ hbget
  have hseenNodup : (cseSeen f n ++ b.instrs.flatMap Instr.defs).Nodup := by
    rw [← hseen]
    exact (instrDefs_nodup hnd).sublist (cseSeen_sublist f (n + 1))
  have hpre := csePrefixInv hnd n (Nat.le_of_lt hn)
  let tab := cseEntryTab f (inEdgeSources f) (csePrefix f n).2.1 n
  have htab : CSEInv f (cseSeen f n) tab (csePrefix f n).2.2 :=
    cseEntryTab_inv hpre
  have hr := cseInstrFold_stable hbmem htab b.instrs (fun i hi => hi)
    hseenNodup [] ∅ ∅ (cseBlockDefs b)
  rw [csePrefix_succ]
  simp only [cseBlockStep]
  have hbBang : f.blocks[n]! = b := by rw [getElem!_eq_getElem hn]
  rw [hbBang]
  exact hr

theorem csePrefix_ext_to {f : Func} (hnd : f.allDefs.Nodup) {n m : Nat}
    (hle : n ≤ m) (hm : m ≤ f.blocks.size) :
    SubstExt (csePrefix f n).2.2 (csePrefix f m).2.2 := by
  induction m generalizing n with
  | zero =>
    have hn : n = 0 := by omega
    subst n
    intro x y hxy
    exact hxy
  | succ m ih =>
    by_cases hn : n = m + 1
    · subst n
      intro hxy
      exact hxy
    · have hnm : n ≤ m := by omega
      have hleft : SubstExt (csePrefix f n).2.2 (csePrefix f m).2.2 :=
        ih hnm (by omega)
      exact SubstExt.trans hleft (csePrefix_ext_succ hnd (by omega))

theorem cseSeen_mono {f : Func} {n m : Nat} (h : n ≤ m) :
    ∀ x ∈ cseSeen f n, x ∈ cseSeen f m := by
  intro x hx
  unfold cseSeen at hx ⊢
  exact ((List.take_sublist_take_left h).flatMap
    (fun b : Block => b.instrs.flatMap Instr.defs)).subset hx

theorem csePrefix_stable_to {f : Func} (hnd : f.allDefs.Nodup) {n m : Nat}
    (hle : n ≤ m) (hm : m ≤ f.blocks.size) :
    SubstStable (cseSeen f n) (csePrefix f n).2.2 (csePrefix f m).2.2 := by
  induction m generalizing n with
  | zero =>
      have hn : n = 0 := by omega
      subst n
      intro x hx
      rfl
  | succ m ih =>
      by_cases hn : n = m + 1
      · subst n
        intro x hx
        rfl
      · have hnm : n ≤ m := by omega
        have hleft := ih hnm (by omega)
        have hright := csePrefix_stable_succ hnd (n := m) (by omega)
        exact hleft.trans (fun x hx => hright x (cseSeen_mono hnm x hx))

theorem substV_absorb {σ τ : Subst} (hext : SubstExt σ τ) (hrange : RangeFree τ)
    (x : ValId) : substV τ (substV σ x) = substV τ x := by
  unfold substV
  cases hs : σ[x]? with
  | none => simp [Std.HashMap.getD_eq_getD_getElem?, hs]
  | some y =>
    have ht : τ[x]? = some y := hext hs
    have hy : τ[y]? = none := hrange ht
    simp [Std.HashMap.getD_eq_getD_getElem?, hs, ht, hy]

theorem substVs_absorb {σ τ : Subst} (hext : SubstExt σ τ) (hrange : RangeFree τ)
    (xs : List ValId) : substVs τ (substVs σ xs) = substVs τ xs := by
  simp [substVs, substV_absorb hext hrange]

theorem substInstr_absorb {σ τ : Subst} (hext : SubstExt σ τ)
    (hrange : RangeFree τ) (i : Instr) :
    substInstr τ (substInstr σ i) = substInstr τ i := by
  cases i <;> simp [substInstr, substVs_absorb hext hrange]

theorem substEdge_absorb {σ τ : Subst} (hext : SubstExt σ τ)
    (hrange : RangeFree τ) (e : Edge) :
    substEdge τ (substEdge σ e) = substEdge τ e := by
  simp [substEdge, substVs_absorb hext hrange]

theorem substTerm_absorb {σ τ : Subst} (hext : SubstExt σ τ)
    (hrange : RangeFree τ) (t : Term) :
    substTerm τ (substTerm σ t) = substTerm τ t := by
  cases t <;> simp [substTerm, substV_absorb hext hrange,
    substEdge_absorb hext hrange, substVs_absorb hext hrange]

@[simp] theorem substInstr_defs (σ : Subst) (i : Instr) :
    (substInstr σ i).defs = i.defs := by
  cases i <;> rfl

theorem substInstr_use {σ : Subst} {i : Instr} {x : ValId}
    (hx : x ∈ (substInstr σ i).uses) : ∃ y ∈ i.uses, substV σ y = x := by
  cases i with
  | const d v => simp [substInstr, Instr.uses] at hx
  | op ds yop args =>
      simp only [substInstr, Instr.uses, substVs, List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨y, hy, rfl⟩
  | call ds fid args =>
      simp only [substInstr, Instr.uses, substVs, List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨y, hy, rfl⟩

theorem substEdge_use {σ : Subst} {e : Edge} {x : ValId}
    (hx : x ∈ (substEdge σ e).args) : ∃ y ∈ e.args, substV σ y = x := by
  simpa [substEdge, substVs, List.mem_map] using hx

theorem substTerm_use {σ : Subst} {t : Term} {x : ValId}
    (hx : x ∈ (substTerm σ t).uses) : ∃ y ∈ t.uses, substV σ y = x := by
  cases t with
  | jump e =>
      simp only [substTerm, Term.uses]
      exact substEdge_use hx
  | branch c et ef =>
      simp only [substTerm, Term.uses, List.mem_cons, List.mem_append] at hx ⊢
      rcases hx with (hc | hx) | hx
      · exact ⟨c, Or.inl (Or.inl rfl), hc.symm⟩
      · obtain ⟨y, hy, hxy⟩ := substEdge_use hx
        exact ⟨y, Or.inl (Or.inr hy), hxy⟩
      · obtain ⟨y, hy, hxy⟩ := substEdge_use hx
        exact ⟨y, Or.inr hy, hxy⟩
  | ret xs =>
      simpa [substTerm, Term.uses, substVs, List.mem_map] using hx
  | halt yop xs =>
      simpa [substTerm, Term.uses, substVs, List.mem_map] using hx

theorem substTerm_edge {σ : Subst} {t : Term} {e : Edge}
    (he : e ∈ (substTerm σ t).edges) :
    ∃ e0 ∈ t.edges, e0.target = e.target := by
  cases t with
  | jump e0 =>
      simp only [substTerm, Term.edges, List.mem_singleton] at he ⊢
      subst e
      exact ⟨e0, rfl, rfl⟩
  | branch c et ef =>
      simp only [substTerm, Term.edges, List.mem_cons, List.mem_singleton] at he ⊢
      rcases he with rfl | he
      · exact ⟨et, Or.inl rfl, rfl⟩
      · have he' : e = substEdge σ ef := by simpa using he
        subst e
        exact ⟨ef, by simp, rfl⟩
  | ret xs => simp [substTerm, Term.edges] at he
  | halt yop xs => simp [substTerm, Term.edges] at he

theorem cseInstrStep_out {i : Instr} {acc : List Instr} {tab : CseTab}
    {used : Std.HashSet ValId} {σ : Subst} {defined blockDefs : Std.HashSet ValId} :
    let r := cseInstrStep i ⟨acc, tab, used, σ, defined, blockDefs⟩
    r.1 = acc ∨ r.1 = substInstr σ i :: acc := by
  cases i with
  | const d v =>
      simp only [cseInstrStep, substInstr]
      split <;> simp
  | op ds yop args =>
      cases ds with
      | nil => simp [cseInstrStep, substInstr]
      | cons d rest =>
          cases rest with
          | nil =>
              simp only [cseInstrStep, substInstr]
              split <;> (try split <;> (try split <;> (try split))) <;> simp
          | cons e es => simp [cseInstrStep, substInstr]
  | call ds fid args => simp [cseInstrStep, substInstr]

theorem cseInstrStep_acc_sublist {i : Instr} {acc : List Instr} {tab : CseTab}
    {used : Std.HashSet ValId} {σ : Subst} {defined blockDefs : Std.HashSet ValId} :
    acc.Sublist
      (cseInstrStep i ⟨acc, tab, used, σ, defined, blockDefs⟩).1 := by
  rcases cseInstrStep_out (i := i) (acc := acc) (tab := tab)
      (used := used) (σ := σ) with h | h
  · rw [h]
  · rw [h]
    exact List.Sublist.cons _ (List.Sublist.refl _)

theorem cseInstrStep_tabVals {i : Instr} {acc : List Instr} {tab : CseTab}
    {used : Std.HashSet ValId} {σ : Subst} {defined blockDefs : Std.HashSet ValId}
    {x : ValId}
    (hx : x ∈ cseTabVals
      (cseInstrStep i ⟨acc, tab, used, σ, defined, blockDefs⟩).2.1) :
    x ∈ cseTabVals tab ∨
      x ∈ (cseInstrStep i
        ⟨acc, tab, used, σ, defined, blockDefs⟩).1.flatMap Instr.defs := by
  cases i with
  | const d v =>
      cases hfind : tab.consts.find? (fun x => x.1 == v) with
      | some a =>
          have hx' : x ∈ cseTabVals tab := by
            simpa [cseInstrStep, substInstr, hfind] using hx
          exact Or.inl hx'
      | none =>
          simp only [cseInstrStep, substInstr, hfind, cseTabVals, List.map_cons,
            List.mem_append, List.mem_cons, Instr.defs, List.flatMap_cons] at hx ⊢
          tauto
  | op ds yop args =>
      cases ds with
      | nil => exact Or.inl hx
      | cons d rest =>
          cases rest with
          | cons e es => exact Or.inl hx
          | nil =>
              by_cases hp : pureOp yop = true
              · cases hfind : tab.ops.find? (fun x => x.1 == (yop, substVs σ args)) with
                | some a =>
                    have hx' : x ∈ cseTabVals tab := by
                      by_cases hu : used.contains d = true
                      · simpa [cseInstrStep, substInstr, hp, hfind, hu] using hx
                      · simpa [cseInstrStep, substInstr, hp, hfind, hu] using hx
                    exact Or.inl hx'
                | none =>
                    by_cases hg : (substVs σ args).all (fun a =>
                        defined.contains a || !blockDefs.contains a) = true
                    · simp only [cseInstrStep, substInstr, hp, if_true, hfind, hg,
                        cseTabVals, List.map_cons, List.mem_append, List.mem_cons,
                        Instr.defs, List.flatMap_cons] at hx ⊢
                      tauto
                    · have hx' : x ∈ cseTabVals tab := by
                        simpa [cseInstrStep, substInstr, hp, hfind, hg] using hx
                      exact Or.inl hx'
              · have hx' : x ∈ cseTabVals tab := by
                  simpa [cseInstrStep, substInstr, hp] using hx
                exact Or.inl hx'
  | call ds fid args => exact Or.inl hx

theorem cseInstrStep_defs_resolve {f : Func} {seen : List ValId} {i : Instr}
    {acc : List Instr} {tab : CseTab} {used : Std.HashSet ValId} {σ : Subst}
    {defined blockDefs : Std.HashSet ValId}
    (hinv : CSEInv f seen tab σ)
    (hnd : (seen ++ i.defs).Nodup) {d : ValId} (hd : d ∈ i.defs) :
    let r := cseInstrStep i ⟨acc, tab, used, σ, defined, blockDefs⟩
    substV r.2.2.2.1 d ∈ r.1.flatMap Instr.defs ∨
      substV r.2.2.2.1 d ∈ cseTabVals tab := by
  have hfresh : d ∉ seen := by
    rw [List.nodup_append] at hnd
    exact fun hm => (hnd.2.2 d hm d hd) rfl
  have hdnone : σ[d]? = none := by
    by_contra hn
    obtain ⟨d0, hd0⟩ := Option.ne_none_iff_exists'.mp hn
    exact hfresh (hinv.2.2.2.1 hd0).1
  cases i with
  | const d' v =>
      simp only [Instr.defs, List.mem_singleton] at hd
      subst d'
      cases hfind : tab.consts.find? (fun x => x.1 == v) with
      | none =>
          left
          simp [cseInstrStep, substInstr, hfind, substV,
            Std.HashMap.getD_eq_getD_getElem?, hdnone]
          exact Or.inl (by simp [Instr.defs])
      | some a =>
          obtain ⟨v0, d0⟩ := a
          right
          have hm : (v0, d0) ∈ tab.consts := List.mem_of_find?_eq_some hfind
          have hd0mem : d0 ∈ cseTabVals tab := by
            exact List.mem_append_right _ (List.mem_map.mpr ⟨(v0, d0), hm, rfl⟩)
          simpa [cseInstrStep, substInstr, hfind, substV,
            Std.HashMap.getD_eq_getD_getElem?, Std.HashMap.getElem?_insert] using hd0mem
  | op ds yop args =>
      cases ds with
      | nil => simp [Instr.defs] at hd
      | cons d' rest =>
          cases rest with
          | nil =>
              simp only [Instr.defs, List.mem_singleton] at hd
              subst d'
              by_cases hp : pureOp yop = true
              · cases hfind : tab.ops.find? (fun x => x.1 == (yop, substVs σ args)) with
                | none =>
                    left
                    by_cases hg : (substVs σ args).all (fun a =>
                        defined.contains a || !blockDefs.contains a) = true
                    · simp [cseInstrStep, substInstr, hp, hfind, hg, substV,
                        Std.HashMap.getD_eq_getD_getElem?, hdnone, Instr.defs]
                    · simp [cseInstrStep, substInstr, hp, hfind, hg, substV,
                        Std.HashMap.getD_eq_getD_getElem?, hdnone, Instr.defs]
                | some a =>
                    obtain ⟨key, d0⟩ := a
                    have hm : (key, d0) ∈ tab.ops := List.mem_of_find?_eq_some hfind
                    have hd0mem : d0 ∈ cseTabVals tab :=
                      List.mem_append_left _ (List.mem_map.mpr ⟨(key, d0), hm, rfl⟩)
                    by_cases hu : used.contains d = true
                    · left
                      simp [cseInstrStep, substInstr, hp, hfind, hu, substV,
                        Std.HashMap.getD_eq_getD_getElem?, hdnone]
                      exact Or.inl (by simp [Instr.defs])
                    · right
                      simpa [cseInstrStep, substInstr, hp, hfind, hu, substV,
                        Std.HashMap.getD_eq_getD_getElem?,
                        Std.HashMap.getElem?_insert] using hd0mem
              · left
                simp [cseInstrStep, substInstr, hp, substV,
                  Std.HashMap.getD_eq_getD_getElem?, hdnone]
                exact Or.inl (by simp [Instr.defs])
          | cons e es =>
              left
              simp only [Instr.defs] at hd
              simp [cseInstrStep, substInstr, substV,
                Std.HashMap.getD_eq_getD_getElem?, hdnone, hd]
              exact Or.inl (by simpa [Instr.defs] using hd)
  | call ds fid args =>
      left
      simp only [Instr.defs] at hd
      simp [cseInstrStep, substInstr, substV,
        Std.HashMap.getD_eq_getD_getElem?, hdnone, hd]
      exact Or.inl (by simpa [Instr.defs] using hd)

theorem cseInstrFold_acc_sublist (l : List Instr) (acc : List Instr)
    (tab : CseTab) (used : Std.HashSet ValId) (σ : Subst)
    (defined blockDefs : Std.HashSet ValId) :
    acc.Sublist
      (l.foldl (fun s i => cseInstrStep i s)
        ⟨acc, tab, used, σ, defined, blockDefs⟩).1 := by
  induction l generalizing acc tab used σ defined blockDefs with
  | nil => exact List.Sublist.refl _
  | cons i is ih =>
      rw [List.foldl_cons]
      exact (cseInstrStep_acc_sublist (i := i)).trans
        (ih _ _ _ _ _ _)

theorem cseInstrFold_tabVals (l : List Instr) (acc : List Instr)
    (tab : CseTab) (used : Std.HashSet ValId) (σ : Subst)
    (defined blockDefs : Std.HashSet ValId) {x : ValId}
    (hx : x ∈ cseTabVals
      (l.foldl (fun s i => cseInstrStep i s)
        ⟨acc, tab, used, σ, defined, blockDefs⟩).2.1) :
    x ∈ cseTabVals tab ∨
      x ∈ (l.foldl (fun s i => cseInstrStep i s)
        ⟨acc, tab, used, σ, defined, blockDefs⟩).1.flatMap Instr.defs := by
  induction l generalizing acc tab used σ defined blockDefs with
  | nil => exact Or.inl hx
  | cons i is ih =>
      rw [List.foldl_cons] at hx ⊢
      let s1 := cseInstrStep i ⟨acc, tab, used, σ, defined, blockDefs⟩
      rcases ih s1.1 s1.2.1 s1.2.2.1 s1.2.2.2.1
          s1.2.2.2.2.1 s1.2.2.2.2.2 hx with htab | hout
      · rcases cseInstrStep_tabVals htab with hold | hnew
        · exact Or.inl hold
        · exact Or.inr
            (((cseInstrFold_acc_sublist is s1.1 s1.2.1 s1.2.2.1
              s1.2.2.2.1 s1.2.2.2.2.1 s1.2.2.2.2.2).flatMap _).subset hnew)
      · exact Or.inr hout

theorem cseInstrFold_defs_resolve {f : Func} {b : Block}
    (hb : b ∈ f.blocks.toList) {seen : List ValId} {tab : CseTab} {σ : Subst}
    (hinv : CSEInv f seen tab σ) (l : List Instr)
    (hmem : ∀ i ∈ l, i ∈ b.instrs)
    (hnd : (seen ++ l.flatMap Instr.defs).Nodup) (acc : List Instr)
    (used defined blockDefs : Std.HashSet ValId) {d : ValId}
    (hd : d ∈ l.flatMap Instr.defs) :
    let r := l.foldl (fun s i => cseInstrStep i s)
      ⟨acc, tab, used, σ, defined, blockDefs⟩
    substV r.2.2.2.1 d ∈ r.1.flatMap Instr.defs ∨
      substV r.2.2.2.1 d ∈ cseTabVals tab := by
  induction l generalizing seen tab σ acc used defined blockDefs with
  | nil => simp at hd
  | cons i is ih =>
      simp only [List.flatMap_cons, List.mem_append] at hd
      have hprefix : (seen ++ i.defs).Nodup := by
        apply List.Nodup.of_append_left (l₂ := is.flatMap Instr.defs)
        simpa [List.append_assoc] using hnd
      have hone := cseInstrStep_inv hb (used := used) (defined := defined)
        (blockDefs := blockDefs) hinv i
        (hmem i (by simp)) hprefix
      have hstate := cseInstrStep_state i acc tab used σ defined blockDefs
      let s1 := cseInstrStep i ⟨acc, tab, used, σ, defined, blockDefs⟩
      have hinv1 : CSEInv f (seen ++ i.defs) s1.2.1 s1.2.2.2.1 := by
        rw [hstate]
        exact hone.1
      have htail : ((seen ++ i.defs) ++ is.flatMap Instr.defs).Nodup := by
        simpa [List.append_assoc] using hnd
      have hstable := cseInstrFold_stable hb hinv1 is
        (fun j hj => hmem j (by simp [hj])) htail s1.1 s1.2.2.1
        s1.2.2.2.2.1 s1.2.2.2.2.2
      rw [List.foldl_cons]
      dsimp only
      rcases hd with hd | hd
      · have hnow := cseInstrStep_defs_resolve hinv hprefix hd
          (acc := acc) (used := used) (defined := defined) (blockDefs := blockDefs)
        have hsubst : substV
            (is.foldl (fun s i => cseInstrStep i s) s1).2.2.2.1 d =
              substV s1.2.2.2.1 d := by
          simp only [substV, Std.HashMap.getD_eq_getD_getElem?]
          rw [hstable d (List.mem_append_right _ hd)]
        rw [hsubst]
        rcases hnow with hout | htab
        · exact Or.inl
            (((cseInstrFold_acc_sublist is s1.1 s1.2.1 s1.2.2.1
              s1.2.2.2.1 s1.2.2.2.2.1 s1.2.2.2.2.2).flatMap _).subset hout)
        · exact Or.inr htab
      · have hrest := ih hinv1 (fun j hj => hmem j (by simp [hj])) htail
          s1.1 s1.2.2.1 s1.2.2.2.2.1 s1.2.2.2.2.2 hd
        rcases hrest with hout | htab1
        · exact Or.inl hout
        · rcases cseInstrStep_tabVals htab1 with htab | hnew
          · exact Or.inr htab
          · exact Or.inl
              (((cseInstrFold_acc_sublist is s1.1 s1.2.1 s1.2.2.1
                s1.2.2.2.1 s1.2.2.2.2.1 s1.2.2.2.2.2).flatMap _).subset hnew)

theorem cseInstrFold_origin {f : Func} {b : Block}
    (hb : b ∈ f.blocks.toList) {seen : List ValId} {tab : CseTab} {σ : Subst}
    (hinv : CSEInv f seen tab σ) (l : List Instr)
    (hmem : ∀ i ∈ l, i ∈ b.instrs)
    (hnd : (seen ++ l.flatMap Instr.defs).Nodup) (acc : List Instr)
    (used defined blockDefs : Std.HashSet ValId)
    {τ : Subst}
    (hext : SubstExt
      (l.foldl (fun s i => cseInstrStep i s)
        ⟨acc, tab, used, σ, defined, blockDefs⟩).2.2.2.1 τ)
    (hrange : RangeFree τ) {j : Instr}
    (hj : j ∈ (l.foldl (fun s i => cseInstrStep i s)
      ⟨acc, tab, used, σ, defined, blockDefs⟩).1) :
    j ∈ acc ∨ ∃ i ∈ l, substInstr τ j = substInstr τ i := by
  induction l generalizing seen tab σ acc used defined blockDefs with
  | nil => exact Or.inl hj
  | cons i is ih =>
      have hprefix : (seen ++ i.defs).Nodup := by
        apply List.Nodup.of_append_left (l₂ := is.flatMap Instr.defs)
        simpa [List.append_assoc] using hnd
      have hone := cseInstrStep_inv hb (used := used) (defined := defined)
        (blockDefs := blockDefs) hinv i
        (hmem i (by simp)) hprefix
      have hstate := cseInstrStep_state i acc tab used σ defined blockDefs
      let s1 := cseInstrStep i ⟨acc, tab, used, σ, defined, blockDefs⟩
      have hinv1 : CSEInv f (seen ++ i.defs) s1.2.1 s1.2.2.2.1 := by
        rw [hstate]
        exact hone.1
      have htail : ((seen ++ i.defs) ++ is.flatMap Instr.defs).Nodup := by
        simpa [List.append_assoc] using hnd
      have hfoldInv := cseInstrFold_inv hb hinv1 is
        (fun k hk => hmem k (by simp [hk])) htail s1.1 s1.2.2.1
        s1.2.2.2.2.1 s1.2.2.2.2.2
      rw [List.foldl_cons] at hext hj
      rcases ih hinv1 (fun k hk => hmem k (by simp [hk])) htail s1.1
          s1.2.2.1 s1.2.2.2.2.1 s1.2.2.2.2.2 hext hj with
        hj1 | ⟨k, hk, heq⟩
      · rcases cseInstrStep_out (i := i) (acc := acc) (tab := tab)
          (used := used) (σ := σ) with
          hout | hout
        · exact Or.inl (hout ▸ hj1)
        · rw [hout] at hj1
          rcases List.mem_cons.mp hj1 with rfl | hjacc
          · right
            refine ⟨i, by simp, ?_⟩
            apply substInstr_absorb
            have honeExt : SubstExt σ s1.2.2.2.1 := by
              rw [hstate]
              exact hone.2
            have htailExt : SubstExt s1.2.2.2.1 τ :=
              SubstExt.trans (σ := s1.2.2.2.1)
                (τ := (is.foldl (fun s i => cseInstrStep i s) s1).2.2.2.1)
                (υ := τ) hfoldInv.2 hext
            intro x y hxy
            exact htailExt (honeExt hxy)
            exact hrange
          · exact Or.inl hjacc
      · exact Or.inr ⟨k, by simp [hk], heq⟩

theorem csePrefix_next_block (f : Func) (i : Nat) :
    (csePrefix f (i + 1)).1[i]? = some (cseBlockOut f i) := by
  rw [csePrefix_succ]
  simp only [cseBlockStep, cseBlockOut]
  rw [Array.getElem?_push]
  simp [csePrefix_blocks_size]

theorem cseFinal_raw_block {f : Func} {i : BlockId} (hi : i < f.blocks.size) :
    (csePrefix f f.blocks.size).1[i]? = some (cseBlockOut f i) := by
  have hn : f.blocks.size = (i + 1) + (f.blocks.size - (i + 1)) :=
    (Nat.add_sub_of_le (Nat.succ_le_of_lt hi)).symm
  rw [hn, csePrefix]
  rw [← List.range'_append_1, List.foldl_append]
  apply cseOuter_fold_get_old
  simpa [csePrefix] using csePrefix_next_block f i

theorem cse_block_get {f : Func} {i : BlockId} {b : Block}
    (h : f.blocks[i]? = some b) :
    (cse f).blocks[i]? = some
      (substBlock (csePrefix f f.blocks.size).2.2 (cseBlockOut f i)) := by
  have hi : i < f.blocks.size := (Array.getElem?_eq_some_iff.mp h).1
  rw [cse_eq]
  change ((substFunc (csePrefix f f.blocks.size).2.2
    { f with blocks := (csePrefix f f.blocks.size).1 }).blocks[i]?) = _
  simp only [substFunc, Array.getElem?_map]
  rw [cseFinal_raw_block hi]
  rfl

@[simp] theorem cse_blocks_size (f : Func) : (cse f).blocks.size = f.blocks.size := by
  rw [cse_eq]
  simp only [substFunc, Array.size_map]
  simpa [csePrefix] using csePrefix_blocks_size f f.blocks.size

def cseAvail (f : Func) (i : BlockId) : List ValId :=
  cseTabVals (cseEntryTab f (inEdgeSources f) (csePrefix f i).2.1 i)

def cseBlockTabOut (f : Func) (i : BlockId) : CseTab :=
  let b := f.blocks[i]!
  let st := csePrefix f i
  let tab := cseEntryTab f (inEdgeSources f) st.2.1 i
  (b.instrs.foldl (fun s ins => cseInstrStep ins s)
    ⟨[], tab, ∅, st.2.2, ∅, cseBlockDefs b⟩).2.1

theorem csePrefix_table_next {f : Func} (hnd : f.allDefs.Nodup)
    {i : BlockId} (hi : i < f.blocks.size) :
    (csePrefix f (i + 1)).2.1[i]! = cseBlockTabOut f i := by
  have hpre := csePrefixInv hnd i (Nat.le_of_lt hi)
  rw [csePrefix_succ]
  simp only [cseBlockStep, cseBlockTabOut]
  have hi0 : i < (csePrefix f i).2.1.size := by rw [hpre.2.1]; exact hi
  have hi1 : i < ((csePrefix f i).2.1.setIfInBounds i
      ((f.blocks[i]!.instrs.foldl (fun s ins => cseInstrStep ins s)
        ⟨[], cseEntryTab f (inEdgeSources f) (csePrefix f i).2.1 i,
          ∅, (csePrefix f i).2.2, ∅, cseBlockDefs f.blocks[i]!⟩).2.1)).size := by simpa
  rw [getElem!_eq_getElem hi1, Array.getElem_setIfInBounds_self]

theorem cseBlockTabOut_sound {f : Func} (hnd : f.allDefs.Nodup)
    {i : BlockId} (hi : i < f.blocks.size) :
    CseTabSound f (cseBlockTabOut f i) := by
  have hnext := csePrefixInv hnd (i + 1) (Nat.succ_le_of_lt hi)
  have hnextPos := csePrefixPosInv hnd (i + 1) (Nat.succ_le_of_lt hi)
  have htabEq := csePrefix_table_next hnd hi
  refine ⟨?_, ?_⟩
  · rw [← htabEq]
    exact (hnext.2.2 i (by omega)).1
  · rw [← htabEq]
    exact hnextPos.2 i (by omega)

theorem csePrefix_table_to {f : Func} (hnd : f.allDefs.Nodup)
    {p n : BlockId} (hp : p < n) (hn : n ≤ f.blocks.size) :
    (csePrefix f n).2.1[p]! = cseBlockTabOut f p := by
  induction n generalizing p with
  | zero => exact (Nat.not_lt_zero p hp).elim
  | succ n ih =>
      by_cases hpn : p = n
      · subst p
        exact csePrefix_table_next hnd (Nat.lt_of_succ_le hn)
      · have hple : p ≤ n := Nat.le_of_lt_succ hp
        have hp' : p < n := Nat.lt_of_le_of_ne hple hpn
        have hn' : n ≤ f.blocks.size := Nat.le_trans (Nat.le_succ n) hn
        have hold := ih hp' hn'
        have hpre := csePrefixInv hnd n hn'
        rw [show Nat.succ n = n + 1 from rfl, csePrefix_succ]
        simp only [cseBlockStep]
        have hp0 : p < (csePrefix f n).2.1.size := by
          rw [hpre.2.1]
          exact Nat.lt_of_lt_of_le hp' hn'
        have hp1 : p < ((csePrefix f n).2.1.setIfInBounds n
            ((f.blocks[n]!.instrs.foldl (fun s ins => cseInstrStep ins s)
              ⟨[], cseEntryTab f (inEdgeSources f) (csePrefix f n).2.1 n,
                ∅, (csePrefix f n).2.2, ∅, cseBlockDefs f.blocks[n]!⟩).2.1)).size := by simpa
        rw [getElem!_eq_getElem hp1,
          Array.getElem_setIfInBounds_ne hp0 (Ne.symm hpn),
          ← getElem!_eq_getElem hp0]
        exact hold

theorem cseBlock_spec {f : Func} (hnd : f.allDefs.Nodup)
    {i : BlockId} {b : Block} (hb : f.blocks[i]? = some b) :
    let τ := (csePrefix f f.blocks.size).2.2
    let b' := substBlock τ (cseBlockOut f i)
    (∀ x ∈ ToAsm.blockUses b', ∃ y ∈ ToAsm.blockUses b, substV τ y = x)
      ∧ (∀ y ∈ ToAsm.blockDefs b,
          substV τ y ∈ ToAsm.blockDefs b' ∨ substV τ y ∈ cseAvail f i)
      ∧ (∀ e ∈ b'.term.edges, ∃ e0 ∈ b.term.edges, e0.target = e.target)
      ∧ (∀ x ∈ cseTabVals (cseBlockTabOut f i),
          x ∈ ToAsm.blockDefs b' ∨ x ∈ cseAvail f i) := by
  let τ := (csePrefix f f.blocks.size).2.2
  let st := csePrefix f i
  let tab := cseEntryTab f (inEdgeSources f) st.2.1 i
  let r := b.instrs.foldl (fun s ins => cseInstrStep ins s)
    ⟨[], tab, ∅, st.2.2, ∅, cseBlockDefs b⟩
  have hi : i < f.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  have hbang : f.blocks[i]! = b := by
    rw [getElem!_eq_getElem hi]
    exact (Array.getElem?_eq_some_iff.mp hb).2
  have hbmem : b ∈ f.blocks.toList := by
    exact List.mem_iff_getElem.mpr ⟨i, by simpa using hi,
      by simpa using (Array.getElem?_eq_some_iff.mp hb).2⟩
  have hpre := csePrefixInv hnd i (Nat.le_of_lt hi)
  have htab : CSEInv f (cseSeen f i) tab st.2.2 := cseEntryTab_inv hpre
  have hseen : cseSeen f (i + 1) = cseSeen f i ++ b.instrs.flatMap Instr.defs :=
    cseSeen_succ hb
  have hndBlock : (cseSeen f i ++ b.instrs.flatMap Instr.defs).Nodup := by
    rw [← hseen]
    exact (instrDefs_nodup hnd).sublist (cseSeen_sublist f (i + 1))
  have hrInv := cseInstrFold_inv hbmem htab b.instrs (fun ins hins => hins)
    hndBlock [] ∅ ∅ (cseBlockDefs b)
  have hrPrefix : (csePrefix f (i + 1)).2.2 = r.2.2.2.1 := by
    rw [csePrefix_succ]
    simp only [cseBlockStep]
    rw [hbang]
  have hext : SubstExt r.2.2.2.1 τ := by
    rw [← hrPrefix]
    exact csePrefix_ext_to hnd (Nat.succ_le_of_lt hi) (Nat.le_refl _)
  have hfinalInv := (csePrefixInv hnd f.blocks.size (Nat.le_refl _)).1
  have hrange : RangeFree τ := hfinalInv.2.2.1
  have hstable : SubstStable (cseSeen f (i + 1)) r.2.2.2.1 τ := by
    rw [← hrPrefix]
    exact csePrefix_stable_to hnd (Nat.succ_le_of_lt hi) (Nat.le_refl _)
  have hraw : cseBlockOut f i = { b with instrs := r.1.reverse } := by
    simp [cseBlockOut, hbang, st, tab, r]
  have param_fixed {p : ValId} (hp : p ∈ b.params) : substV τ p = p := by
    have hpnone : τ[p]? = none := by
      by_contra hn
      obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hn
      have hpseen := (hfinalInv.2.2.2.1 hq).1
      unfold cseSeen at hpseen
      have htake : f.blocks.toList.take f.blocks.size = f.blocks.toList := by simp
      rw [htake] at hpseen
      simp only [List.mem_flatMap] at hpseen
      obtain ⟨b2, hb2, ins, hins, hpdef⟩ := hpseen
      exact param_not_instr_def hnd hbmem hb2 hins hp hpdef
    simp [substV, Std.HashMap.getD_eq_getD_getElem?, hpnone]
  dsimp only
  rw [hraw]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [ToAsm.mem_blockUses] at hx
    rcases hx with hx | hx
    · simp only [substBlock] at hx
      obtain ⟨j, hj, hxj⟩ := List.mem_flatMap.mp hx
      obtain ⟨j0, hj0, hjeq⟩ := List.mem_map.mp hj
      have hjr : j0 ∈ r.1 := by simpa using hj0
      have hxj0 : x ∈ (substInstr τ j0).uses := by rw [hjeq]; exact hxj
      have horigin := cseInstrFold_origin hbmem htab b.instrs (fun ins hins => hins)
        hndBlock [] ∅ ∅ (cseBlockDefs b) hext hrange hjr
      rcases horigin with hjnil | ⟨ins, hins, heq⟩
      · simp at hjnil
      · have hxins : x ∈ (substInstr τ ins).uses := by
          rw [← heq]
          exact hxj0
        obtain ⟨y, hy, hxy⟩ := substInstr_use hxins
        exact ⟨y, ToAsm.mem_blockUses.mpr
          (Or.inl (List.mem_flatMap.mpr ⟨ins, hins, hy⟩)), hxy⟩
    · obtain ⟨y, hy, hxy⟩ := substTerm_use hx
      exact ⟨y, ToAsm.mem_blockUses.mpr (Or.inr hy), hxy⟩
  · intro y hy
    rw [ToAsm.mem_blockDefs] at hy
    rcases hy with hp | hd
    · left
      rw [param_fixed hp]
      exact ToAsm.mem_blockDefs.mpr (Or.inl hp)
    · obtain ⟨ins, hins, hyd⟩ := List.mem_flatMap.mp hd
      have hres := cseInstrFold_defs_resolve hbmem htab b.instrs
        (fun ins hins => hins) hndBlock [] ∅ ∅ (cseBlockDefs b)
          (List.mem_flatMap.mpr ⟨ins, hins, hyd⟩)
      have hymem : y ∈ cseSeen f (i + 1) := by
        rw [hseen]
        exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨ins, hins, hyd⟩)
      have hsubst : substV τ y = substV r.2.2.2.1 y := by
        simp only [substV, Std.HashMap.getD_eq_getD_getElem?]
        rw [hstable y hymem]
      rw [hsubst]
      rcases hres with hout | hav
      · left
        apply ToAsm.mem_blockDefs.mpr
        right
        obtain ⟨j, hj, hjd⟩ := List.mem_flatMap.mp hout
        refine List.mem_flatMap.mpr ⟨substInstr τ j, ?_, ?_⟩
        · exact List.mem_map.mpr ⟨j, by simpa using hj, rfl⟩
        · simpa using hjd
      · exact Or.inr hav
  · intro e he
    exact substTerm_edge he
  · intro x hx
    have htabOut : cseBlockTabOut f i = r.2.1 := by
      simp [cseBlockTabOut, hbang, st, tab, r]
    rw [htabOut] at hx
    rcases cseInstrFold_tabVals b.instrs [] tab ∅ st.2.2 ∅
        (cseBlockDefs b) hx with hav | hout
    · exact Or.inr hav
    · left
      apply ToAsm.mem_blockDefs.mpr
      right
      obtain ⟨j, hj, hjd⟩ := List.mem_flatMap.mp hout
      refine List.mem_flatMap.mpr ⟨substInstr τ j, ?_, ?_⟩
      · exact List.mem_map.mpr ⟨j, by simpa using hj, rfl⟩
      · simpa using hjd

theorem cseAvail_entry (f : Func) : cseAvail f f.entry = [] := by
  simp [cseAvail, cseEntryTab, cseTabVals]

theorem cseAvail_succ {f : Func} (hnd : f.allDefs.Nodup)
    (hwf : f.wfCheck n = true) {i : BlockId} {b : Block}
    (hb : f.blocks[i]? = some b) {e : Edge} (he : e ∈ b.term.edges)
    {x : ValId} (hx : x ∈ cseAvail f e.target) :
    let τ := (csePrefix f f.blocks.size).2.2
    let b' := substBlock τ (cseBlockOut f i)
    x ∈ ToAsm.blockDefs b' ∨ x ∈ cseAvail f i := by
  obtain ⟨tb, htb, -⟩ := wfCheck_edge_arity hwf (b := b) (by
    exact List.mem_iff_getElem.mpr ⟨i, by
      simpa using (Array.getElem?_eq_some_iff.mp hb).1,
      by simpa using (Array.getElem?_eq_some_iff.mp hb).2⟩) he
  have ht : e.target < f.blocks.size := (Array.getElem?_eq_some_iff.mp htb).1
  unfold cseAvail at hx
  rw [cseEntryTab] at hx
  split at hx
  · simp [cseTabVals] at hx
  · cases hs : (inEdgeSources f)[e.target]! with
    | nil => simp [hs, cseTabVals] at hx
    | cons p ps =>
        cases ps with
        | cons q qs => simp [hs, cseTabVals] at hx
        | nil =>
            by_cases hp : p < e.target
            · simp only [hs, hp, if_true] at hx
              have hip : i = p := inEdgeSources_single_eq hb he ht hs
              subst p
              rw [csePrefix_table_to hnd hp (Nat.le_of_lt ht)] at hx
              exact (cseBlock_spec hnd hb).2.2.2 x (cseTabVals_inheritTab hx)
            · simp [hs, hp, cseTabVals] at hx

end Passes

/-! ## Pass 0: program-level inlining

`Passes.inlineProg` runs *before* the per-function pipeline: `inlineFunc`
splices eligible call sites (`inlineOnce`, budgeted fixed point), then
`pruneFuncs` drops functions no longer reachable from `main` and remaps the
surviving ids. It needs **no dominance hypothesis** — it only ever splices a
callee body along the unique edge that reaches it — but it does need `wfCheck`
(`inlineOnce` additionally re-checks the arity conditions
`g.params.length == as.length`, `g.nrets == ds.length`, `g.entry == 0` at the
site, so those come for free from the guard rather than from `wfCheck`).

I audited the splice for the same stale-read hazard the counterexample exhibits
and did not find one: the spliced blocks are reachable only through the call
block, `contBlock` is reachable only through the spliced `ret` edges, and the
callee's non-parameter ids are renamed by `+ off` with
`off > max (maxVal f) (maxVal g)`, so they cannot capture a caller id. Duplicate
actual arguments (`g(x, x)`) map two callee parameters onto one caller id, which
is harmless because both were bound to the same word at the call. None of this is
*proved* — it is the content of the `sorry`s below.

There is one additional precondition that the original provisional statement of
`inlineOnce_sound` missed. The renaming table is `g.params.zip as` followed by
`List.find?`, so it sends a duplicated callee parameter to its *first* actual
argument. `Regs.setMany`, on the other hand, binds left-to-right and therefore
leaves the *last* actual argument in that register. Caller well-formedness alone
is therefore insufficient: a malformed callee with duplicate parameters is a
direct counterexample. The production entry point already has `P.wfCheck =
true`, which supplies `g.allDefs.Nodup`; the one-step and fixed-point statements
below carry that whole-program hypothesis explicitly. -/

/-- Whole-program well-formedness supplies the per-callee fact needed by the
inliner. Unlike caller well-formedness, this rules out duplicate callee
parameters and collisions between parameters and local definitions. -/
theorem progWf_func {P : Prog} (hwf : P.wfCheck = true) {fid : FuncId} {g : Func}
    (hg : P.funcs[fid]? = some g) : g.wfCheck P.funcs.size = true := by
  simp only [Prog.wfCheck, Bool.and_eq_true] at hwf
  have hi : fid < P.funcs.size := (Array.getElem?_eq_some_iff.mp hg).1
  rw [Array.getElem?_eq_getElem hi] at hg
  obtain rfl := Option.some.inj hg
  rw [Array.all_eq_true] at hwf
  exact hwf.2 fid hi

/-- In particular, the parameter side of an inliner's renaming table has no
duplicate keys. -/
theorem progWf_func_params_nodup {P : Prog} (hwf : P.wfCheck = true)
    {fid : FuncId} {g : Func} (hg : P.funcs[fid]? = some g) : g.params.Nodup := by
  have hgf := progWf_func hwf hg
  unfold Func.wfCheck at hgf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hgf
  unfold Func.allDefs at hgf
  exact (List.nodup_append.mp hgf.1.1.1).1

/-- Lookup in `params.zip actuals` returns the unique pair carrying a given
parameter. This is the list-level fact that reconciles `inlineOnce`'s `find?`
renaming with call semantics' positional `setMany`. -/
theorem findParam_zip_of_mem {ps as : List ValId} (hnd : ps.Nodup)
    {p a : ValId} (hm : (p, a) ∈ ps.zip as) :
    (ps.zip as).find? (fun pa => pa.1 == p) = some (p, a) := by
  induction ps generalizing as with
  | nil => simp at hm
  | cons q qs ih =>
      cases as with
      | nil => simp at hm
      | cons b bs =>
          rw [List.nodup_cons] at hnd
          rcases List.mem_cons.mp hm with hhead | htail
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hhead
            simp
          · have hpqs : p ∈ qs := by
              exact (List.of_mem_zip htail).1
            have hqp : q ≠ p := fun heq => hnd.1 (heq ▸ hpqs)
            simpa [hqp] using ih hnd.2 htail

/-- Binding formal parameters to the values read from actual parameters agrees
at corresponding positions. The arbitrary base register file makes the lemma
stable under the caller-register frame used by an inlined body. -/
theorem Regs.setMany_getMany_of_mem_zip {R S : Regs} {ps as : List ValId}
    {vals : List U256} (hnd : ps.Nodup) (hlen : ps.length = as.length)
    (hget : R.getMany as = some vals) {p a : ValId} (hm : (p, a) ∈ ps.zip as) :
    (S.setMany ps vals) p = R a := by
  induction ps generalizing S as vals with
  | nil => simp at hm
  | cons q qs ih =>
      cases as with
      | nil => simp at hlen
      | cons b bs =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          rw [Regs.getMany_cons] at hget
          cases hb : R b with
          | none => simp [hb] at hget
          | some v =>
              cases ht : R.getMany bs with
              | none => simp [hb, ht] at hget
              | some vs =>
                  simp only [hb, ht, Option.bind_some, Option.map_some,
                    Option.some.injEq] at hget
                  subst vals
                  rw [List.nodup_cons] at hnd
                  rcases List.mem_cons.mp hm with hhead | htail
                  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hhead
                    rw [Regs.setMany_cons,
                      Regs.setMany_of_not_mem (S.set p v) qs vs hnd.1,
                      Regs.set_same, hb]
                  · exact ih hnd.2 hlen ht htail (S := S.set q v)

/-- The concrete value-renaming function used by `inlineOnce` sends a callee
parameter to its corresponding caller actual. -/
theorem inlineRho_param {ps as : List ValId} (hnd : ps.Nodup) {p a : ValId}
    (hm : (p, a) ∈ ps.zip as) (off : Nat) :
    (match (ps.zip as).find? (fun pa => pa.1 == p) with
      | some pa => pa.2
      | none => p + off) = a := by
  rw [findParam_zip_of_mem hnd hm]

/-- Entry-register agreement for a renamed inlined callee parameter. This is
the base case of the eventual callee-body renaming simulation. -/
theorem inlineParam_regs_agree {R S : Regs} {ps as : List ValId} {vals : List U256}
    (hnd : ps.Nodup) (hlen : ps.length = as.length)
    (hget : R.getMany as = some vals) {p a : ValId} (hm : (p, a) ∈ ps.zip as)
    (off : Nat) :
    (S.setMany ps vals) p =
      R (match (ps.zip as).find? (fun pa => pa.1 == p) with
        | some pa => pa.2
        | none => p + off) := by
  rw [inlineRho_param hnd hm off]
  exact Regs.setMany_getMany_of_mem_zip hnd hlen hget hm

/-- Generic read transport through a value-id renaming. -/
theorem Regs.getMany_map_of_agree {R R' : Regs} {ρ : ValId → ValId}
    {xs : List ValId} {vals : List U256}
    (hagree : ∀ x ∈ xs, R x = R' (ρ x)) (hget : R.getMany xs = some vals) :
    R'.getMany (xs.map ρ) = some vals := by
  induction xs generalizing vals with
  | nil => simpa using hget
  | cons x xs ih =>
      rw [Regs.getMany_cons] at hget
      cases hx : R x with
      | none => simp [hx] at hget
      | some v =>
          cases ht : R.getMany xs with
          | none => simp [hx, ht] at hget
          | some vs =>
              simp only [hx, ht, Option.bind_some, Option.map_some,
                Option.some.injEq] at hget
              subst vals
              have hx' : R' (ρ x) = some v := by
                rw [← hagree x (by simp), hx]
              have ht' := ih (fun y hy => hagree y (by simp [hy])) ht
              simpa [Regs.getMany_cons, hx'] using ht'

/-- Register agreement is preserved when corresponding destinations are bound
through an injective renaming. -/
theorem Regs.setMany_rename_congr {R R' : Regs} {ρ : ValId → ValId}
    (hinj : Function.Injective ρ) (hagree : ∀ x, R x = R' (ρ x))
    (xs : List ValId) (vals : List U256) :
    ∀ x, (R.setMany xs vals) x = (R'.setMany (xs.map ρ) vals) (ρ x) := by
  induction xs generalizing R R' vals with
  | nil =>
      intro x
      change R x = R'.setMany [] vals (ρ x)
      rw [Regs.setMany_nil_left]
      exact hagree x
  | cons d ds ih =>
      cases vals with
      | nil =>
          intro x
          rw [Regs.setMany_nil_right, Regs.setMany_nil_right]
          exact hagree x
      | cons v vs =>
          rw [Regs.setMany_cons, List.map_cons, Regs.setMany_cons]
          apply ih (vals := vs)
          intro x
          by_cases hxd : x = d
          · subst x
            simp
          · have hrho : ρ x ≠ ρ d := fun h => hxd (hinj h)
            rw [Regs.set_other _ _ hxd, Regs.set_other _ _ hrho]
            exact hagree x

@[simp] theorem Passes.renameInstr_defs (ρ : ValId → ValId) (i : Instr) :
    (renameInstr ρ i).defs = i.defs.map ρ := by
  cases i <;> simp [renameInstr, Instr.defs]

@[simp] theorem Passes.renameInstr_uses (ρ : ValId → ValId) (i : Instr) :
    (renameInstr ρ i).uses = i.uses.map ρ := by
  cases i <;> simp [renameInstr, Instr.uses]

@[simp] theorem Passes.renameEdge_args (ρ : ValId → ValId)
    (β : BlockId → BlockId) (e : Edge) :
    (renameEdge ρ β e).args = e.args.map ρ := rfl

@[simp] theorem Passes.renameEdge_target (ρ : ValId → ValId)
    (β : BlockId → BlockId) (e : Edge) :
    (renameEdge ρ β e).target = β e.target := rfl

@[simp] theorem Passes.renameTerm_uses (ρ : ValId → ValId)
    (β : BlockId → BlockId) (t : Term) :
    (renameTerm ρ β t).uses = t.uses.map ρ := by
  cases t <;> simp [renameTerm, Term.uses, renameEdge, List.map_append]

/-! ### Fresh-value bounds used by inlining -/

/-- Folding `Nat.max` over a list never decreases its accumulator. -/
theorem foldl_max_start_le (xs : List Nat) (n : Nat) :
    n ≤ xs.foldl Nat.max n := by
  induction xs generalizing n with
  | nil => exact Nat.le_refl n
  | cons x xs ih =>
      exact le_trans (Nat.le_max_left n x) (ih (Nat.max n x))

/-- Every member is bounded by a `Nat.max` fold, independently of the initial
accumulator. -/
theorem foldl_max_mem_le {xs : List Nat} {x n : Nat} (hx : x ∈ xs) :
    x ≤ xs.foldl Nat.max n := by
  induction xs generalizing n with
  | nil => simp at hx
  | cons y ys ih =>
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hx with rfl | hx
      · exact le_trans (Nat.le_max_right n x) (foldl_max_start_le ys (Nat.max n x))
      · exact ih hx

/-- One block's contribution to `maxVal`, with an explicit initial bound. -/
def Passes.maxBlockVal (acc : ValId) (b : Block) : ValId :=
  let m := fun a (vs : List ValId) => vs.foldl Nat.max a
  m (m (b.instrs.foldl (fun a i => m (m a i.defs) i.uses) acc) b.params)
    b.term.uses

theorem Passes.instrFold_start_le (is : List Instr) (n : ValId) :
    n ≤ is.foldl
      (fun a i => i.uses.foldl Nat.max (i.defs.foldl Nat.max a)) n := by
  induction is generalizing n with
  | nil => exact Nat.le_refl n
  | cons i is ih =>
      rw [List.foldl_cons]
      exact le_trans
        (le_trans (foldl_max_start_le i.defs n)
          (foldl_max_start_le i.uses (i.defs.foldl Nat.max n)))
        (ih _)

theorem Passes.maxBlockVal_start_le (b : Block) (n : ValId) :
    n ≤ maxBlockVal n b := by
  exact le_trans (instrFold_start_le b.instrs n)
    (le_trans (foldl_max_start_le b.params _) (foldl_max_start_le b.term.uses _))

theorem Passes.maxBlockVal_param_le {b : Block} {x : ValId} (hx : x ∈ b.params)
    (n : ValId) : x ≤ maxBlockVal n b := by
  exact le_trans (foldl_max_mem_le (n := b.instrs.foldl
    (fun a i => i.uses.foldl Nat.max (i.defs.foldl Nat.max a)) n) hx)
    (foldl_max_start_le b.term.uses _)

theorem Passes.maxBlockVal_termUse_le {b : Block} {x : ValId} (hx : x ∈ b.term.uses)
    (n : ValId) : x ≤ maxBlockVal n b :=
  foldl_max_mem_le hx

theorem Passes.instrFold_def_le {is : List Instr} {i : Instr} (hi : i ∈ is)
    {x : ValId} (hx : x ∈ i.defs) (n : ValId) :
    x ≤ is.foldl
      (fun a j => j.uses.foldl Nat.max (j.defs.foldl Nat.max a)) n := by
  induction is generalizing n with
  | nil => simp at hi
  | cons j js ih =>
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hi with rfl | hi
      · exact le_trans
          (le_trans (foldl_max_mem_le (n := n) hx)
            (foldl_max_start_le i.uses _))
          (instrFold_start_le js _)
      · exact ih hi _

theorem Passes.instrFold_use_le {is : List Instr} {i : Instr} (hi : i ∈ is)
    {x : ValId} (hx : x ∈ i.uses) (n : ValId) :
    x ≤ is.foldl
      (fun a j => j.uses.foldl Nat.max (j.defs.foldl Nat.max a)) n := by
  induction is generalizing n with
  | nil => simp at hi
  | cons j js ih =>
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hi with rfl | hi
      · exact le_trans (foldl_max_mem_le (n := i.defs.foldl Nat.max n) hx)
          (instrFold_start_le js _)
      · exact ih hi _

theorem Passes.maxBlockVal_instrDef_le {b : Block} {i : Instr} (hi : i ∈ b.instrs)
    {x : ValId} (hx : x ∈ i.defs) (n : ValId) : x ≤ maxBlockVal n b := by
  exact le_trans (instrFold_def_le hi hx n)
    (le_trans (foldl_max_start_le b.params _) (foldl_max_start_le b.term.uses _))

theorem Passes.maxBlockVal_instrUse_le {b : Block} {i : Instr} (hi : i ∈ b.instrs)
    {x : ValId} (hx : x ∈ i.uses) (n : ValId) : x ≤ maxBlockVal n b := by
  exact le_trans (instrFold_use_le hi hx n)
    (le_trans (foldl_max_start_le b.params _) (foldl_max_start_le b.term.uses _))

theorem Passes.blocksFold_start_le (bs : List Block) (n : ValId) :
    n ≤ bs.foldl maxBlockVal n := by
  induction bs generalizing n with
  | nil => exact Nat.le_refl n
  | cons b bs ih =>
      rw [List.foldl_cons]
      exact le_trans (maxBlockVal_start_le b n) (ih _)

theorem Passes.blocksFold_block_le {bs : List Block} {b : Block} (hb : b ∈ bs)
    {x : ValId} (hx : ∀ n, x ≤ maxBlockVal n b) (n : ValId) :
    x ≤ bs.foldl maxBlockVal n := by
  induction bs generalizing n with
  | nil => simp at hb
  | cons c cs ih =>
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hb with rfl | hb
      · exact le_trans (hx n) (blocksFold_start_le cs _)
      · exact ih hb _

theorem Passes.maxVal_eq (f : Func) :
    maxVal f = f.blocks.toList.foldl maxBlockVal
      ([].foldl Nat.max (f.params.foldl Nat.max 0)) := by
  unfold maxVal maxBlockVal
  rw [Array.foldl_toList]

/-- Every function parameter is at most the function's `maxVal`. -/
theorem Passes.param_le_maxVal {f : Func} {x : ValId} (hx : x ∈ f.params) :
    x ≤ maxVal f := by
  rw [maxVal_eq]
  exact le_trans (foldl_max_mem_le (n := 0) hx)
    (blocksFold_start_le f.blocks.toList _)

/-- Every block parameter is at most the enclosing function's `maxVal`. -/
theorem Passes.blockParam_le_maxVal {f : Func} {b : Block}
    (hb : b ∈ f.blocks.toList) {x : ValId} (hx : x ∈ b.params) : x ≤ maxVal f := by
  rw [maxVal_eq]
  exact blocksFold_block_le hb (fun n => maxBlockVal_param_le hx n) _

/-- Every instruction destination is at most the enclosing function's
`maxVal`. -/
theorem Passes.instrDef_le_maxVal {f : Func} {b : Block}
    (hb : b ∈ f.blocks.toList) {i : Instr} (hi : i ∈ b.instrs)
    {x : ValId} (hx : x ∈ i.defs) : x ≤ maxVal f := by
  rw [maxVal_eq]
  exact blocksFold_block_le hb (fun n => maxBlockVal_instrDef_le hi hx n) _

/-- Every instruction operand is at most the enclosing function's `maxVal`. -/
theorem Passes.instrUse_le_maxVal {f : Func} {b : Block}
    (hb : b ∈ f.blocks.toList) {i : Instr} (hi : i ∈ b.instrs)
    {x : ValId} (hx : x ∈ i.uses) : x ≤ maxVal f := by
  rw [maxVal_eq]
  exact blocksFold_block_le hb (fun n => maxBlockVal_instrUse_le hi hx n) _

/-- Every terminator operand is at most the enclosing function's `maxVal`. -/
theorem Passes.termUse_le_maxVal {f : Func} {b : Block}
    (hb : b ∈ f.blocks.toList) {x : ValId} (hx : x ∈ b.term.uses) : x ≤ maxVal f := by
  rw [maxVal_eq]
  exact blocksFold_block_le hb (fun n => maxBlockVal_termUse_le hx n) _

/-- The splice offset is strictly above every value id mentioned by either the
caller or the callee. -/
theorem Passes.maxVal_lt_inlineOffset_left (f g : Func) :
    maxVal f < Nat.max (maxVal f) (maxVal g) + 1 :=
  Nat.lt_succ_of_le (Nat.le_max_left _ _)

theorem Passes.maxVal_lt_inlineOffset_right (f g : Func) :
    maxVal g < Nat.max (maxVal f) (maxVal g) + 1 :=
  Nat.lt_succ_of_le (Nat.le_max_right _ _)

/-! ### Partitioned register agreement -/

/-- The value renaming used by an inline splice, named so its two partitions
can be stated without repeating the `find?` expression. -/
def Passes.inlineRho (ps as : List ValId) (off : Nat) (v : ValId) : ValId :=
  match (ps.zip as).find? (fun pa => pa.1 == v) with
  | some pa => pa.2
  | none => v + off

theorem Passes.inlineRho_of_not_param {ps as : List ValId} {off v : Nat}
    (hv : v ∉ ps) : inlineRho ps as off v = v + off := by
  unfold inlineRho
  have hnone : (ps.zip as).find? (fun pa => pa.1 == v) = none := by
    apply List.find?_eq_none.mpr
    intro pa hpa
    have hp : pa.1 ∈ ps := (List.of_mem_zip hpa).1
    simpa [beq_iff_eq, hv] using (show pa.1 ≠ v from fun h => hv (h ▸ hp))
  rw [hnone]

theorem mem_zip_left_of_length_eq {ps as : List Nat} (hlen : ps.length = as.length)
    {p : Nat} (hp : p ∈ ps) : ∃ a, (p, a) ∈ ps.zip as := by
  induction ps generalizing as with
  | nil => simp at hp
  | cons q qs ih =>
      cases as with
      | nil => simp at hlen
      | cons a as =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          rcases List.mem_cons.mp hp with rfl | hp
          · exact ⟨a, by simp⟩
          · obtain ⟨b, hb⟩ := ih hlen hp
            exact ⟨b, by simp [hb]⟩

theorem Passes.inlineRho_lt_of_param_nodup {ps as : List ValId} {off p : Nat}
    (hnd : ps.Nodup) (hlen : ps.length = as.length)
    (has : ∀ a ∈ as, a < off) (hp : p ∈ ps) : inlineRho ps as off p < off := by
  obtain ⟨a, hpa⟩ := mem_zip_left_of_length_eq hlen hp
  rw [show inlineRho ps as off p = a by
    exact inlineRho_param hnd hpa off]
  exact has a (List.of_mem_zip hpa).2

theorem Passes.inlineRho_ge_of_not_param {ps as : List ValId} {off v : Nat}
    (hv : v ∉ ps) : off ≤ inlineRho ps as off v := by
  rw [inlineRho_of_not_param hv]
  omega

/-- The shifted partition is injective against every callee id when the
destination is not a formal parameter. -/
theorem Passes.inlineRho_eq_of_not_param {ps as : List ValId} {off x d : Nat}
    (hnd : ps.Nodup) (hlen : ps.length = as.length)
    (has : ∀ a ∈ as, a < off) (hd : d ∉ ps)
    (heq : inlineRho ps as off x = inlineRho ps as off d) : x = d := by
  by_cases hx : x ∈ ps
  · have hxl := inlineRho_lt_of_param_nodup hnd hlen has hx
    have hdr := inlineRho_ge_of_not_param (as := as) (off := off) hd
    rw [heq] at hxl
    exact (Nat.not_le_of_lt hxl hdr).elim
  · rw [inlineRho_of_not_param hx, inlineRho_of_not_param hd] at heq
    exact Nat.add_right_cancel heq

/-- One-way agreement is sufficient for replay: every successful callee read
has the same value in the renamed high partition. -/
def Passes.RenamedAgree (ps as : List ValId) (off : Nat)
    (Rc Ri : Regs) : Prop :=
  ∀ x v, Rc x = some v → Ri (inlineRho ps as off x) = some v

/-- The low partition is the caller frame and must remain unchanged while the
spliced callee executes. -/
def Passes.CallerFrame (off : Nat) (Rcaller Ri : Regs) : Prop :=
  ∀ x, x < off → Ri x = Rcaller x

/-- Corresponding parallel bindings preserve one-way renamed agreement when
no destination image aliases another source id's image. -/
theorem Regs.setMany_rename_some {R R' : Regs} {ρ : ValId → ValId}
    (hagree : ∀ x v, R x = some v → R' (ρ x) = some v)
    (xs : List ValId) (vals : List U256)
    (hsep : ∀ x d, d ∈ xs → ρ x = ρ d → x = d) :
    ∀ x v, (R.setMany xs vals) x = some v →
      (R'.setMany (xs.map ρ) vals) (ρ x) = some v := by
  induction xs generalizing R R' vals with
  | nil =>
      simpa [Regs.setMany_nil_left] using hagree
  | cons d ds ih =>
      cases vals with
      | nil => simpa [Regs.setMany_nil_right] using hagree
      | cons w ws =>
          rw [Regs.setMany_cons, List.map_cons, Regs.setMany_cons]
          apply ih (vals := ws)
          · intro x v hx
            by_cases hxd : x = d
            · subst x
              simpa using hx
            · have hrho : ρ x ≠ ρ d := fun h => hxd (hsep x d (by simp) h)
              rw [Regs.set_other _ _ hxd] at hx
              rw [Regs.set_other _ _ hrho]
              exact hagree x v hx
          · intro x q hq heq
            exact hsep x q (by simp [hq]) heq

/-- High-partition writes preserve every caller register below the offset. -/
theorem Regs.setMany_below {R : Regs} {ρ : ValId → ValId} {off : Nat}
    (xs : List ValId) (vals : List U256)
    (hhigh : ∀ d ∈ xs, off ≤ ρ d) :
    ∀ x, x < off → (R.setMany (xs.map ρ) vals) x = R x := by
  intro x hx
  apply Regs.setMany_of_not_mem
  intro hm
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hm
  exact (Nat.not_le_of_lt hx) (hhigh d hd)

/-- Function parameters and block parameters are disjoint under the inliner's
single-assignment hypothesis. -/
theorem funcParam_not_blockParam {f : Func} (hnd : f.allDefs.Nodup)
    {b : Block} (hb : b ∈ f.blocks.toList) {d : ValId}
    (hf : d ∈ f.params) (hbparam : d ∈ b.params) : False := by
  have hall := List.nodup_iff_count_le_one.mp hnd d
  rw [allDefs_eq, List.count_append] at hall
  have h1 : 1 ≤ f.params.count d := List.count_pos_iff.mpr hf
  have h2 : 1 ≤ (f.blocks.toList.flatMap blockAllDefs).count d :=
    one_le_count_flatMap hb (List.mem_append_left _ hbparam)
  omega

theorem params_nodup_of_allDefs {f : Func} {ps : List ValId}
    (hnd : f.allDefs.Nodup) (hps : ps = f.params) : ps.Nodup := by
  subst ps
  rw [allDefs_eq] at hnd
  exact (List.nodup_append.mp hnd).1

theorem Passes.renamedAgree_entry {R : Regs} {ps as : List ValId}
    {vals : List U256} {off : Nat} (hnd : ps.Nodup)
    (hlen : ps.length = as.length) (hget : R.getMany as = some vals) :
    RenamedAgree ps as off (Regs.empty.setMany ps vals) R := by
  intro x v hx
  rcases Regs.eq_some_setMany hx with hempty | hp
  · simp [Regs.empty] at hempty
  · obtain ⟨a, hpa⟩ := mem_zip_left_of_length_eq hlen hp
    have heq := inlineParam_regs_agree (S := Regs.empty) hnd hlen hget hpa off
    exact heq.symm.trans hx

theorem Passes.renamedAgree_getMany {Rc Ri : Regs} {ps as : List ValId}
    {off : Nat} (hagree : RenamedAgree ps as off Rc Ri)
    {xs : List ValId} {vals : List U256} (hget : Rc.getMany xs = some vals) :
    Ri.getMany (xs.map (inlineRho ps as off)) = some vals := by
  apply Regs.getMany_map_of_agree (hget := hget)
  intro x hx
  obtain ⟨v, hv⟩ := Regs.eq_some_of_getMany hget hx
  rw [hv, hagree x v hv]

theorem Passes.renamedAgree_setMany {Rc Ri : Regs} {ps as : List ValId}
    {off : Nat} (hnd : ps.Nodup) (hlen : ps.length = as.length)
    (has : ∀ a ∈ as, a < off) {ds : List ValId}
    (hds : ∀ d ∈ ds, d ∉ ps) (vals : List U256)
    (hagree : RenamedAgree ps as off Rc Ri) :
    RenamedAgree ps as off (Rc.setMany ds vals)
      (Ri.setMany (ds.map (inlineRho ps as off)) vals) := by
  exact Regs.setMany_rename_some hagree ds vals fun x d hd heq =>
    inlineRho_eq_of_not_param hnd hlen has (hds d hd) heq

theorem Passes.callerFrame_setMany {Rcaller Ri : Regs} {ps as : List ValId}
    {off : Nat} {ds : List ValId} (hds : ∀ d ∈ ds, d ∉ ps)
    (hframe : CallerFrame off Rcaller Ri) (vals : List U256) :
    CallerFrame off Rcaller
      (Ri.setMany (ds.map (inlineRho ps as off)) vals) := by
  intro x hx
  rw [Regs.setMany_below ds vals (fun d hd => inlineRho_ge_of_not_param
    (as := as) (off := off) (hds d hd)) x hx]
  exact hframe x hx

def Passes.inlineReplayTerm (ρ : ValId → ValId) (β : BlockId → BlockId)
    (contId : BlockId) : Term → Term
  | .ret vs => .jump ⟨contId, vs.map ρ⟩
  | t => renameTerm ρ β t

def Passes.inlineReplayBlock (ρ : ValId → ValId) (β : BlockId → BlockId)
    (contId : BlockId) (b : Block) : Block :=
  { params := b.params.map ρ
    instrs := b.instrs.map (renameInstr ρ)
    term := inlineReplayTerm ρ β contId b.term }

/-- The current rest really is a suffix of one block of the callee. -/
def Rest.IsSuffixOf (r : Rest) (b : Block) : Prop :=
  ∃ pre, b.instrs = pre ++ r.instrs ∧ b.term = r.term

theorem Rest.IsSuffixOf.tail {r : Rest} {b : Block} {i : Instr}
    (h : (Rest.mk (i :: r.instrs) r.term).IsSuffixOf b) : r.IsSuffixOf b := by
  obtain ⟨pre, his, ht⟩ := h
  refine ⟨pre ++ [i], ?_, ht⟩
  simpa [List.append_assoc] using his

theorem Rest.IsSuffixOf.head_mem {r : Rest} {b : Block} {i : Instr}
    (h : (Rest.mk (i :: r.instrs) r.term).IsSuffixOf b) : i ∈ b.instrs := by
  obtain ⟨pre, his, -⟩ := h
  rw [his]
  simp

theorem Regs.getMany_length {R : Regs} {xs : List ValId} {vs : List U256}
    (h : R.getMany xs = some vs) : xs.length = vs.length := by
  induction xs generalizing vs with
  | nil =>
      have : vs = [] := by simpa using h.symm
      subst vs
      rfl
  | cons x xs ih =>
      rw [Regs.getMany_cons] at h
      cases hx : R x with
      | none => simp [hx] at h
      | some v =>
          cases hxs : R.getMany xs with
          | none => simp [hx, hxs] at h
          | some ws =>
              have hvs : vs = v :: ws := by simpa [hx, hxs] using h.symm
              subst vs
              simp [ih hxs]

theorem Passes.inlineReplayBlock_get {f' g : Func} {preBlocks : Array Block}
    {ρ : ValId → ValId} {β : BlockId → BlockId} {contId i : BlockId}
    {gb : Block} {cont : Block}
    (hblocks : f'.blocks = preBlocks ++ g.blocks.map (inlineReplayBlock ρ β contId) ++ #[cont])
    (hg : g.blocks[i]? = some gb) :
    f'.blocks[preBlocks.size + i]? = some (inlineReplayBlock ρ β contId gb) := by
  rw [hblocks, Array.getElem?_append_left (by
    have hi := (Array.getElem?_eq_some_iff.mp hg).1
    simp
    omega)]
  rw [Array.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  simpa using congrArg (Option.map (inlineReplayBlock ρ β contId)) hg

theorem Passes.inlineContBlock_get {f' g : Func} {preBlocks : Array Block}
    {ρ : ValId → ValId} {β : BlockId → BlockId} {contId : BlockId}
    {cont : Block}
    (hblocks : f'.blocks = preBlocks ++ g.blocks.map (inlineReplayBlock ρ β contId) ++ #[cont]) :
    f'.blocks[preBlocks.size + g.blocks.size]? = some cont := by
  rw [hblocks, Array.getElem?_append_right (by simp)]
  simp only [Array.size_append, Array.size_map, Nat.add_sub_cancel_left]
  simp

theorem block_mem_of_getElem? {f : Func} {i : BlockId} {b : Block}
    (h : f.blocks[i]? = some b) : b ∈ f.blocks.toList :=
  List.mem_of_getElem? (Array.getElem?_toList.trans h)

/-- Replay a callee execution in the renamed, appended block partition.  A
callee return is interpreted in CPS: it jumps to `cont`, binds `ds`, and hands
control to `hk`; a halt remains a halt. -/
theorem Passes.inlineReplay_exec [model : ExternalModel]
    {P : Prog} {g f' : Func} {preBlocks : Array Block} {cont : Block}
    {ps as ds : List ValId} {off contId : Nat}
    {ρ : ValId → ValId} {β : BlockId → BlockId}
    {Rc Ri Rcaller : Regs} {st : EvmState} {rest : Rest} {cres final : FRes}
    (hρ : ρ = inlineRho ps as off)
    (hβ : ∀ i, β i = preBlocks.size + i)
    (hcontId : contId = preBlocks.size + g.blocks.size)
    (hblocks : f'.blocks = preBlocks ++ g.blocks.map (inlineReplayBlock ρ β contId) ++ #[cont])
    (hcontParams : cont.params = ds)
    (hnd : g.allDefs.Nodup) (hps : ps = g.params)
    (hlen : ps.length = as.length) (has : ∀ a ∈ as, a < off)
    (hret : ∀ {b : Block}, b ∈ g.blocks.toList → ∀ {xs}, b.term = .ret xs →
      xs.length = ds.length)
    (hexec : Exec (model := model) P g Rc st rest cres)
    {b : Block} (hb : b ∈ g.blocks.toList) (horigin : rest.IsSuffixOf b)
    (hagree : RenamedAgree ps as off Rc Ri)
    (hframe : CallerFrame off Rcaller Ri)
    (hfinal : ∀ st', cres = .halt st' → final = .halt st')
    (hk : ∀ (Rout : Regs) (vals : List U256) (st' : EvmState),
      cres = .ret vals st' → CallerFrame off Rcaller Rout →
      Exec (model := model) P f' (Rout.setMany ds vals) st'
        ⟨cont.instrs, cont.term⟩ final) :
    Exec (model := model) P f' Ri st
      ⟨rest.instrs.map (renameInstr ρ), inlineReplayTerm ρ β contId rest.term⟩ final := by
  subst ρ
  induction hexec generalizing Ri b with
  | @const fcur R st d v is t res htail ih =>
      have hi : Instr.const d v ∈ b.instrs :=
        Rest.IsSuffixOf.head_mem (r := ⟨is, t⟩) horigin
      have hd : d ∉ ps := by
        rw [hps]
        exact fun hp => funcParam_not_instr_def hnd hb hi hp (by simp [Instr.defs])
      refine Exec.const (ih hcontId hnd hps hret hb
        (Rest.IsSuffixOf.tail (r := ⟨is, t⟩) horigin)
        (renamedAgree_setMany (params_nodup_of_allDefs hnd hps) hlen has
          (ds := [d]) (by simpa using hd) [v] hagree)
        (callerFrame_setMany (as := as) (ds := [d]) (by simpa using hd) hframe [v])
        hfinal hk hblocks)
  | @op fcur R st st' ods yop oas oargs rets is t res hget hop hlenRet htail ih =>
      have hi : Instr.op ods yop oas ∈ b.instrs :=
        Rest.IsSuffixOf.head_mem (r := ⟨is, t⟩) horigin
      have hds : ∀ d ∈ ods, d ∉ ps := by
        intro d hd hp
        rw [hps] at hp
        exact funcParam_not_instr_def hnd hb hi hp (by simpa [Instr.defs] using hd)
      refine Exec.op (args := oargs) (rets := rets)
        (renamedAgree_getMany hagree hget) hop (by simpa using hlenRet)
        (ih hcontId hnd hps hret hb
          (Rest.IsSuffixOf.tail (r := ⟨is, t⟩) horigin)
          (renamedAgree_setMany (params_nodup_of_allDefs hnd hps) hlen has
            hds rets hagree)
          (callerFrame_setMany (as := as) hds hframe rets) hfinal hk hblocks)
  | @opHalt fcur R st st' ods yop oas oargs is t hget hop =>
      have hf := hfinal st' rfl
      subst final
      simpa [renameInstr, inlineReplayTerm, renameTerm] using
        (Exec.opHalt (f := f') (ds := ods.map (inlineRho ps as off))
          (args := oargs) (renamedAgree_getMany hagree hget) hop)
  | @call _ callee R st st' ods oas fid oargs rvals eb is t res
      hfid hget hplen heb hbody hlenRet htail ihbody ih =>
      have hi : Instr.call ods fid oas ∈ b.instrs :=
        Rest.IsSuffixOf.head_mem (r := ⟨is, t⟩) horigin
      have hds : ∀ d ∈ ods, d ∉ ps := by
        intro d hd hp
        rw [hps] at hp
        exact funcParam_not_instr_def hnd hb hi hp (by simpa [Instr.defs] using hd)
      refine Exec.call (args := oargs) (rvals := rvals) (g := callee) (eb := eb)
        hfid (renamedAgree_getMany hagree hget) hplen heb hbody
        (by simpa using hlenRet)
        (ih hcontId hnd hps hret hb
          (Rest.IsSuffixOf.tail (r := ⟨is, t⟩) horigin)
          (renamedAgree_setMany (params_nodup_of_allDefs hnd hps) hlen has
            hds rvals hagree)
          (callerFrame_setMany (as := as) hds hframe rvals) hfinal hk hblocks)
  | @callHalt _ callee R st st' ods oas fid oargs eb is t
      hfid hget hplen heb hbody ihbody =>
      have hf := hfinal st' rfl
      subst final
      simpa [renameInstr, inlineReplayTerm, renameTerm] using
        (Exec.callHalt (f := f') (ds := ods.map (inlineRho ps as off))
          (args := oargs) (g := callee) (eb := eb) hfid
          (renamedAgree_getMany hagree hget) hplen heb hbody)
  | @jump _ R st e tb vals res htb hget hplen htail ih =>
      have htbmem := block_mem_of_getElem? htb
      have hparams : ∀ d ∈ tb.params, d ∉ ps := by
        intro d hd hp
        rw [hps] at hp
        exact funcParam_not_blockParam hnd htbmem hp hd
      refine Exec.jump (args := vals) (tb := inlineReplayBlock
          (inlineRho ps as off) β contId tb) ?_
        (renamedAgree_getMany hagree hget) (by simpa [inlineReplayBlock] using hplen)
        (ih hcontId hnd hps hret htbmem ⟨[], rfl, rfl⟩
          (renamedAgree_setMany (params_nodup_of_allDefs hnd hps) hlen has
            hparams vals hagree)
          (callerFrame_setMany (as := as) hparams hframe vals) hfinal hk hblocks)
      change f'.blocks[β e.target]? = some _
      rw [hβ e.target]
      exact inlineReplayBlock_get hblocks htb
  | @branchTrue _ R st c v et ef tb vals res hc hv htb hget hplen htail ih =>
      have htbmem := block_mem_of_getElem? htb
      have hparams : ∀ d ∈ tb.params, d ∉ ps := by
        intro d hd hp
        rw [hps] at hp
        exact funcParam_not_blockParam hnd htbmem hp hd
      refine Exec.branchTrue (v := v) (args := vals)
        (tb := inlineReplayBlock (inlineRho ps as off) β contId tb)
        (hagree c v hc) hv ?_ (renamedAgree_getMany hagree hget)
        (by simpa [inlineReplayBlock] using hplen)
        (ih hcontId hnd hps hret htbmem ⟨[], rfl, rfl⟩
          (renamedAgree_setMany (params_nodup_of_allDefs hnd hps) hlen has
            hparams vals hagree)
          (callerFrame_setMany (as := as) hparams hframe vals) hfinal hk hblocks)
      change f'.blocks[β et.target]? = some _
      rw [hβ et.target]
      exact inlineReplayBlock_get hblocks htb
  | @branchFalse _ R st c et ef tb vals res hc htb hget hplen htail ih =>
      have htbmem := block_mem_of_getElem? htb
      have hparams : ∀ d ∈ tb.params, d ∉ ps := by
        intro d hd hp
        rw [hps] at hp
        exact funcParam_not_blockParam hnd htbmem hp hd
      refine Exec.branchFalse (args := vals)
        (tb := inlineReplayBlock (inlineRho ps as off) β contId tb)
        (hagree c 0 hc) ?_
        (renamedAgree_getMany hagree hget)
        (by simpa [inlineReplayBlock] using hplen)
        (ih hcontId hnd hps hret htbmem ⟨[], rfl, rfl⟩
          (renamedAgree_setMany (params_nodup_of_allDefs hnd hps) hlen has
            hparams vals hagree)
          (callerFrame_setMany (as := as) hparams hframe vals) hfinal hk hblocks)
      change f'.blocks[β ef.target]? = some _
      rw [hβ ef.target]
      exact inlineReplayBlock_get hblocks htb
  | @ret _ R st xs vals hget =>
      have ht : b.term = .ret xs := horigin.choose_spec.2
      have hlenVals : ds.length = vals.length := by
        rw [← Regs.getMany_length hget, hret hb ht]
      have hk' := hk Ri vals st rfl hframe
      rw [← hcontParams] at hk'
      refine Exec.jump (args := vals) (tb := cont) ?_
        (renamedAgree_getMany hagree hget) (by simpa [hcontParams] using hlenVals)
        hk'
      rw [hcontId]
      exact inlineContBlock_get hblocks
  | @halt _ R st st' yop oas oargs hget hop =>
      have hf := hfinal st' rfl
      subst final
      simpa [inlineReplayTerm, renameTerm] using
        (Exec.halt (f := f') (args := oargs) (renamedAgree_getMany hagree hget) hop)

/-- The indexed replay raises the callee bound once to accommodate the CPS continuation. -/
theorem Passes.inlineReplay_execN [model : ExternalModel]
    {P : Prog} {n : Nat} {g f' : Func} {preBlocks : Array Block} {cont : Block}
    {ps as ds : List ValId} {off contId : Nat}
    {ρ : ValId → ValId} {β : BlockId → BlockId}
    {Rc Ri Rcaller : Regs} {st : EvmState} {rest : Rest} {cres final : FRes}
    (hρ : ρ = inlineRho ps as off)
    (hβ : ∀ i, β i = preBlocks.size + i)
    (hcontId : contId = preBlocks.size + g.blocks.size)
    (hblocks : f'.blocks = preBlocks ++ g.blocks.map (inlineReplayBlock ρ β contId) ++ #[cont])
    (hcontParams : cont.params = ds)
    (hnd : g.allDefs.Nodup) (hps : ps = g.params)
    (hlen : ps.length = as.length) (has : ∀ a ∈ as, a < off)
    (hret : ∀ {b : Block}, b ∈ g.blocks.toList → ∀ {xs}, b.term = .ret xs →
      xs.length = ds.length)
    (hexec : ExecN (model := model) P n g Rc st rest cres)
    {b : Block} (hb : b ∈ g.blocks.toList) (horigin : rest.IsSuffixOf b)
    (hagree : RenamedAgree ps as off Rc Ri)
    (hframe : CallerFrame off Rcaller Ri)
    (hfinal : ∀ st', cres = .halt st' → final = .halt st')
    (hk : ∀ (Rout : Regs) (vals : List U256) (st' : EvmState),
      cres = .ret vals st' → CallerFrame off Rcaller Rout →
      ExecN (model := model) P (n + 1) f' (Rout.setMany ds vals) st'
        ⟨cont.instrs, cont.term⟩ final) :
    ExecN (model := model) P (n + 1) f' Ri st
      ⟨rest.instrs.map (renameInstr ρ), inlineReplayTerm ρ β contId rest.term⟩ final := by
  subst ρ
  induction hexec generalizing Ri b with
  | @const n fcur R st d v is t res htail ih =>
      have hi : Instr.const d v ∈ b.instrs :=
        Rest.IsSuffixOf.head_mem (r := ⟨is, t⟩) horigin
      have hd : d ∉ ps := by
        rw [hps]
        exact fun hp => funcParam_not_instr_def hnd hb hi hp (by simp [Instr.defs])
      refine ExecN.const (ih hcontId hnd hps hret hb
        (Rest.IsSuffixOf.tail (r := ⟨is, t⟩) horigin)
        (renamedAgree_setMany (params_nodup_of_allDefs hnd hps) hlen has
          (ds := [d]) (by simpa using hd) [v] hagree)
        (callerFrame_setMany (as := as) (ds := [d]) (by simpa using hd) hframe [v])
        hfinal hk hblocks)
  | @op n fcur R st st' ods yop oas oargs rets is t res hget hop hlenRet htail ih =>
      have hi : Instr.op ods yop oas ∈ b.instrs :=
        Rest.IsSuffixOf.head_mem (r := ⟨is, t⟩) horigin
      have hds : ∀ d ∈ ods, d ∉ ps := by
        intro d hd hp
        rw [hps] at hp
        exact funcParam_not_instr_def hnd hb hi hp (by simpa [Instr.defs] using hd)
      refine ExecN.op (args := oargs) (rets := rets)
        (renamedAgree_getMany hagree hget) hop (by simpa using hlenRet)
        (ih hcontId hnd hps hret hb
          (Rest.IsSuffixOf.tail (r := ⟨is, t⟩) horigin)
          (renamedAgree_setMany (params_nodup_of_allDefs hnd hps) hlen has
            hds rets hagree)
          (callerFrame_setMany (as := as) hds hframe rets) hfinal hk hblocks)
  | @opHalt n fcur R st st' ods yop oas oargs is t hget hop =>
      have hf := hfinal st' rfl
      subst final
      simpa [renameInstr, inlineReplayTerm, renameTerm] using
        (ExecN.opHalt (f := f') (ds := ods.map (inlineRho ps as off))
          (args := oargs) (renamedAgree_getMany hagree hget) hop)
  | @call n _ callee R st st' ods oas fid oargs rvals eb is t res
      hfid hget hplen heb hbody hlenRet htail ihbody ih =>
      have hi : Instr.call ods fid oas ∈ b.instrs :=
        Rest.IsSuffixOf.head_mem (r := ⟨is, t⟩) horigin
      have hds : ∀ d ∈ ods, d ∉ ps := by
        intro d hd hp
        rw [hps] at hp
        exact funcParam_not_instr_def hnd hb hi hp (by simpa [Instr.defs] using hd)
      refine ExecN.call (args := oargs) (rvals := rvals) (g := callee) (eb := eb)
        hfid (renamedAgree_getMany hagree hget) hplen heb (hbody.mono (by omega))
        (by simpa using hlenRet)
        (ih hcontId hnd hps hret hb
          (Rest.IsSuffixOf.tail (r := ⟨is, t⟩) horigin)
          (renamedAgree_setMany (params_nodup_of_allDefs hnd hps) hlen has
            hds rvals hagree)
          (callerFrame_setMany (as := as) hds hframe rvals) hfinal hk hblocks)
  | @callHalt n _ callee R st st' ods oas fid oargs eb is t
      hfid hget hplen heb hbody ihbody =>
      have hf := hfinal st' rfl
      subst final
      simpa [renameInstr, inlineReplayTerm, renameTerm] using
        (ExecN.callHalt (f := f') (ds := ods.map (inlineRho ps as off))
          (args := oargs) (g := callee) (eb := eb) hfid
          (renamedAgree_getMany hagree hget) hplen heb (hbody.mono (by omega)))
  | @jump n _ R st e tb vals res htb hget hplen htail ih =>
      have htbmem := block_mem_of_getElem? htb
      have hparams : ∀ d ∈ tb.params, d ∉ ps := by
        intro d hd hp
        rw [hps] at hp
        exact funcParam_not_blockParam hnd htbmem hp hd
      refine ExecN.jump (args := vals) (tb := inlineReplayBlock
          (inlineRho ps as off) β contId tb) ?_
        (renamedAgree_getMany hagree hget) (by simpa [inlineReplayBlock] using hplen)
        (ih hcontId hnd hps hret htbmem ⟨[], rfl, rfl⟩
          (renamedAgree_setMany (params_nodup_of_allDefs hnd hps) hlen has
            hparams vals hagree)
          (callerFrame_setMany (as := as) hparams hframe vals) hfinal hk hblocks)
      change f'.blocks[β e.target]? = some _
      rw [hβ e.target]
      exact inlineReplayBlock_get hblocks htb
  | @branchTrue n _ R st c v et ef tb vals res hc hv htb hget hplen htail ih =>
      have htbmem := block_mem_of_getElem? htb
      have hparams : ∀ d ∈ tb.params, d ∉ ps := by
        intro d hd hp
        rw [hps] at hp
        exact funcParam_not_blockParam hnd htbmem hp hd
      refine ExecN.branchTrue (v := v) (args := vals)
        (tb := inlineReplayBlock (inlineRho ps as off) β contId tb)
        (hagree c v hc) hv ?_ (renamedAgree_getMany hagree hget)
        (by simpa [inlineReplayBlock] using hplen)
        (ih hcontId hnd hps hret htbmem ⟨[], rfl, rfl⟩
          (renamedAgree_setMany (params_nodup_of_allDefs hnd hps) hlen has
            hparams vals hagree)
          (callerFrame_setMany (as := as) hparams hframe vals) hfinal hk hblocks)
      change f'.blocks[β et.target]? = some _
      rw [hβ et.target]
      exact inlineReplayBlock_get hblocks htb
  | @branchFalse n _ R st c et ef tb vals res hc htb hget hplen htail ih =>
      have htbmem := block_mem_of_getElem? htb
      have hparams : ∀ d ∈ tb.params, d ∉ ps := by
        intro d hd hp
        rw [hps] at hp
        exact funcParam_not_blockParam hnd htbmem hp hd
      refine ExecN.branchFalse (args := vals)
        (tb := inlineReplayBlock (inlineRho ps as off) β contId tb)
        (hagree c 0 hc) ?_
        (renamedAgree_getMany hagree hget)
        (by simpa [inlineReplayBlock] using hplen)
        (ih hcontId hnd hps hret htbmem ⟨[], rfl, rfl⟩
          (renamedAgree_setMany (params_nodup_of_allDefs hnd hps) hlen has
            hparams vals hagree)
          (callerFrame_setMany (as := as) hparams hframe vals) hfinal hk hblocks)
      change f'.blocks[β ef.target]? = some _
      rw [hβ ef.target]
      exact inlineReplayBlock_get hblocks htb
  | @ret n _ R st xs vals hget =>
      have ht : b.term = .ret xs := horigin.choose_spec.2
      have hlenVals : ds.length = vals.length := by
        rw [← Regs.getMany_length hget, hret hb ht]
      have hk' := hk Ri vals st rfl hframe
      rw [← hcontParams] at hk'
      refine ExecN.jump (args := vals) (tb := cont) ?_
        (renamedAgree_getMany hagree hget) (by simpa [hcontParams] using hlenVals)
        hk'
      rw [hcontId]
      exact inlineContBlock_get hblocks
  | @halt n _ R st st' yop oas oargs hget hop =>
      have hf := hfinal st' rfl
      subst final
      simpa [inlineReplayTerm, renameTerm] using
        (ExecN.halt (f := f') (args := oargs) (renamedAgree_getMany hagree hget) hop)


/-! ### Inverting one inlining splice

`inlineOnce` is a pair of nested early-return loops.  As with
`findTrivialParam`, exposing a pure `loopWith` model keeps the inversion local:
the successful result must have been produced by one concrete instruction
step, and unfolding that step gives the complete splice equation. -/

namespace Passes

abbrev InlineState := MProd (Option (Option Func)) PUnit

theorem loopWith_inline_done {α : Type} {g : α → InlineState →
    ForInStep InlineState} {xs : List α} {f : Func}
    (hg : ∀ a, g a ⟨none, PUnit.unit⟩ = .yield ⟨none, PUnit.unit⟩ ∨
      ∃ f, g a ⟨none, PUnit.unit⟩ = .done ⟨some (some f), PUnit.unit⟩)
    (h : (loopWith g xs ⟨none, PUnit.unit⟩).1 = some (some f)) :
    ∃ a ∈ xs, g a ⟨none, PUnit.unit⟩ =
      .done ⟨some (some f), PUnit.unit⟩ := by
  induction xs with
  | nil => simp [loopWith] at h
  | cons a as ih =>
      rw [loopWith_cons] at h
      rcases hg a with ha | ⟨f', ha⟩
      · rw [ha] at h
        obtain ⟨b, hb, hdone⟩ := ih h
        exact ⟨b, by simp [hb], hdone⟩
      · rw [ha] at h
        have hf : f' = f := by simpa using h
        subst f'
        exact ⟨a, by simp, ha⟩

theorem loopWith_inline_cases {α : Type} {g : α → InlineState →
    ForInStep InlineState} {xs : List α}
    (hg : ∀ a, g a ⟨none, PUnit.unit⟩ = .yield ⟨none, PUnit.unit⟩ ∨
      ∃ f, g a ⟨none, PUnit.unit⟩ = .done ⟨some (some f), PUnit.unit⟩) :
    (loopWith g xs ⟨none, PUnit.unit⟩).1 = none ∨
      ∃ f, (loopWith g xs ⟨none, PUnit.unit⟩).1 = some (some f) := by
  induction xs with
  | nil => exact Or.inl rfl
  | cons a as ih =>
      rw [loopWith_cons]
      rcases hg a with ha | ⟨f, ha⟩
      · rw [ha]
        exact ih
      · rw [ha]
        exact Or.inr ⟨f, rfl⟩

def inlineInstrStep (counts : Array Nat) (funcs : Array Func) (f : Func)
    (bi ci : Nat) (_ : InlineState) : ForInStep InlineState :=
  let b := f.blocks[bi]!
  match b.instrs[ci]! with
  | .call ds fid as =>
      match funcs[fid]? with
      | some g =>
          if inlinable (counts[fid]?.getD 0) g && g.params.length == as.length
              && g.nrets == ds.length && g.entry == 0 then
            let off := Nat.max (maxVal f) (maxVal g) + 1
            let paramMap := g.params.zip as
            let ρ := fun v =>
              match paramMap.find? (·.1 == v) with
              | some pa => pa.2
              | none => v + off
            let nCaller := f.blocks.size
            let contId := nCaller + g.blocks.size
            let β := fun (b : BlockId) => nCaller + b
            let spliced := g.blocks.map fun gb =>
              { params := gb.params.map ρ
                instrs := gb.instrs.map (renameInstr ρ)
                term :=
                  match gb.term with
                  | .ret vs => .jump ⟨contId, vs.map ρ⟩
                  | t => renameTerm ρ β t }
            let contBlock : Block :=
              { params := ds
                instrs := b.instrs.drop (ci + 1)
                term := b.term }
            let callBlock : Block :=
              { params := b.params
                instrs := b.instrs.take ci
                term := .jump ⟨nCaller + g.entry, []⟩ }
            let blocks := (f.blocks.set! bi callBlock) ++ spliced ++ #[contBlock]
            .done ⟨some (some { f with blocks }), PUnit.unit⟩
          else .yield ⟨none, PUnit.unit⟩
      | none => .yield ⟨none, PUnit.unit⟩
  | _ => .yield ⟨none, PUnit.unit⟩

def inlineBlockStep (counts : Array Nat) (funcs : Array Func) (f : Func)
    (bi : Nat) (_ : InlineState) : ForInStep InlineState :=
  let b := f.blocks[bi]!
  let r := loopWith (inlineInstrStep counts funcs f bi)
    (List.range' 0 b.instrs.length 1) ⟨none, PUnit.unit⟩
  match r.1 with
  | none => .yield ⟨none, PUnit.unit⟩
  | some a => .done ⟨some a, PUnit.unit⟩

theorem inlineOnce_eq_loop (counts : Array Nat) (funcs : Array Func) (f : Func) :
    inlineOnce counts funcs f =
      (loopWith (inlineBlockStep counts funcs f)
        (List.range' 0 f.blocks.size 1) ⟨none, PUnit.unit⟩).1.getD none := by
  unfold inlineOnce
  dsimp only
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rw [Id.forIn_eq_loopWith (g := inlineBlockStep counts funcs f) (h := by
    intro bi r
    unfold inlineBlockStep
    rw [Id.forIn_eq_loopWith (g := inlineInstrStep counts funcs f bi) (h := by
      intro ci s
      simp only [LawfulMonad.pure_bind]
      cases hi : f.blocks[bi]!.instrs[ci]! with
      | const d v => simp [inlineInstrStep, hi]
      | op ds yop as => simp [inlineInstrStep, hi]
      | call ds fid as =>
          cases hg : funcs[fid]? with
          | none => simp [inlineInstrStep, hi, hg]
          | some g =>
              by_cases hc : inlinable (counts[fid]?.getD 0) g &&
                  g.params.length == as.length && g.nrets == ds.length && g.entry == 0
              · simp [inlineInstrStep, hi, hg, hc]
                rfl
              · simp [inlineInstrStep, hi, hg, hc])]
    simp_all [Id.run, bind, pure]
    split <;> simp_all)]
  simp [Id.run, bind, pure, Option.getD]
  split <;> simp_all

theorem inlineInstrStep_cases (counts : Array Nat) (funcs : Array Func)
    (f : Func) (bi ci : Nat) :
    inlineInstrStep counts funcs f bi ci ⟨none, PUnit.unit⟩ =
        .yield ⟨none, PUnit.unit⟩ ∨
      ∃ f', inlineInstrStep counts funcs f bi ci ⟨none, PUnit.unit⟩ =
        .done ⟨some (some f'), PUnit.unit⟩ := by
  unfold inlineInstrStep
  dsimp only
  split <;> try { exact Or.inl rfl }
  split <;> try { exact Or.inl rfl }
  split
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inl rfl

theorem inlineBlockStep_cases (counts : Array Nat) (funcs : Array Func)
    (f : Func) (bi : Nat) :
    inlineBlockStep counts funcs f bi ⟨none, PUnit.unit⟩ =
        .yield ⟨none, PUnit.unit⟩ ∨
      ∃ f', inlineBlockStep counts funcs f bi ⟨none, PUnit.unit⟩ =
        .done ⟨some (some f'), PUnit.unit⟩ := by
  unfold inlineBlockStep
  dsimp only
  rcases loopWith_inline_cases
      (fun ci => inlineInstrStep_cases counts funcs f bi ci)
      (xs := List.range' 0 f.blocks[bi]!.instrs.length 1) with hr | ⟨f', hr⟩
  · left
    simp [hr]
  · right
    exact ⟨f', by simp [hr]⟩

/-- Successful `inlineOnce` inversion.  The final equality is the five-part
splice definition (renaming, copied blocks, continuation, split call block,
and concatenated block array) in a form callers can unfold selectively. -/
theorem inlineOnce_inv {counts : Array Nat} {funcs : Array Func} {f f' : Func}
    (h : inlineOnce counts funcs f = some f') :
    ∃ bi b ci ds fid as g,
      bi < f.blocks.size ∧ f.blocks[bi]? = some b ∧
      ci < b.instrs.length ∧ b.instrs[ci]? = some (.call ds fid as) ∧
      funcs[fid]? = some g ∧
      inlinable (counts[fid]?.getD 0) g = true ∧
      g.params.length = as.length ∧ g.nrets = ds.length ∧ g.entry = 0 ∧
      f' =
        let off := Nat.max (maxVal f) (maxVal g) + 1
        let paramMap := g.params.zip as
        let ρ := fun v =>
          match paramMap.find? (·.1 == v) with
          | some pa => pa.2
          | none => v + off
        let nCaller := f.blocks.size
        let contId := nCaller + g.blocks.size
        let β := fun (b : BlockId) => nCaller + b
        let spliced := g.blocks.map fun gb =>
          { params := gb.params.map ρ
            instrs := gb.instrs.map (renameInstr ρ)
            term := match gb.term with
              | .ret vs => .jump ⟨contId, vs.map ρ⟩
              | t => renameTerm ρ β t }
        let contBlock : Block :=
          { params := ds, instrs := b.instrs.drop (ci + 1), term := b.term }
        let callBlock : Block :=
          { params := b.params, instrs := b.instrs.take ci,
            term := .jump ⟨nCaller + g.entry, []⟩ }
        { f with blocks := (f.blocks.set! bi callBlock) ++ spliced ++ #[contBlock] } := by
  rw [inlineOnce_eq_loop] at h
  have hout :
      (loopWith (inlineBlockStep counts funcs f)
        (List.range' 0 f.blocks.size 1) ⟨none, PUnit.unit⟩).1 =
        some (some f') := by
    cases hr : (loopWith (inlineBlockStep counts funcs f)
        (List.range' 0 f.blocks.size 1) ⟨none, PUnit.unit⟩).1 with
    | none => simp [hr, Option.getD] at h
    | some r =>
        cases r with
        | none => simp [hr, Option.getD] at h
        | some q =>
            have hq : q = f' := by simpa [hr, Option.getD] using h
            simpa [hq] using hr
  obtain ⟨bi, hbimem, hbistep⟩ := loopWith_inline_done
    (fun j => inlineBlockStep_cases counts funcs f j) hout
  unfold inlineBlockStep at hbistep
  dsimp only at hbistep
  split at hbistep
  · cases hbistep
  · rename_i r hr
    have hr' : r = some f' := by simpa using hbistep
    rw [hr'] at hr
    obtain ⟨ci, hcimem, hcistep⟩ := loopWith_inline_done
      (fun j => inlineInstrStep_cases counts funcs f bi j) hr
    unfold inlineInstrStep at hcistep
    dsimp only at hcistep
    split at hcistep <;> try { cases hcistep }
    rename_i ds fid as hcall
    split at hcistep <;> try { cases hcistep }
    rename_i g hg
    split at hcistep <;> try { cases hcistep }
    rename_i hguard
    have hbi : bi < f.blocks.size := by simpa using hbimem
    have hci : ci < f.blocks[bi]!.instrs.length := by simpa using hcimem
    have hbget : f.blocks[bi]? = some f.blocks[bi]! := by
      rw [Array.getElem?_eq_getElem hbi, getElem!_eq_getElem hbi]
    have hparts : inlinable (counts[fid]?.getD 0) g = true ∧
        g.params.length = as.length ∧ g.nrets = ds.length ∧ g.entry = 0 := by
      have hpraw := (by simpa only [Bool.and_eq_true, beq_iff_eq] using hguard)
      exact ⟨hpraw.1.1.1, hpraw.1.1.2, hpraw.1.2, hpraw.2⟩
    refine ⟨bi, f.blocks[bi]!, ci, ds, fid, as, g, hbi, hbget, hci, ?_, hg,
      ?_, ?_, ?_, ?_, ?_⟩
    · apply List.getElem?_eq_some_iff.mpr
      refine ⟨hci, ?_⟩
      rw [getElem!_pos (f.blocks[bi]!.instrs) ci hci] at hcall
      exact hcall
    · exact hparts.1
    · exact hparts.2.1
    · exact hparts.2.2.1
    · exact hparts.2.2.2
    · simpa using hcistep.symm

/-! ### Well-formedness of one inlining splice -/

theorem blockAllDefs_rename (b : Block) (rho : ValId → ValId) (t : Term) :
    blockAllDefs
        { params := b.params.map rho
          instrs := b.instrs.map (renameInstr rho)
          term := t } =
      (blockAllDefs b).map rho := by
  simp only [blockAllDefs, List.map_append, List.map_map, renameInstr_defs,
    List.flatMap_map]
  rw [List.map_flatMap]

theorem flatMap_set_append_perm {alpha beta : Type} (l : List alpha)
    (k : alpha → List beta) {i : Nat} (hi : i < l.length)
    (new : alpha) (extra : List beta)
    (hpart : List.Perm (k new ++ extra) (k l[i])) :
    List.Perm ((l.set i new).flatMap k ++ extra) (l.flatMap k) := by
  rw [List.set_eq_take_append_cons_drop, if_pos hi]
  simp only [List.flatMap_append, List.flatMap_cons]
  have hswap : List.Perm
      ((l.take i).flatMap k ++ k new ++ (l.drop (i + 1)).flatMap k ++ extra)
      ((l.take i).flatMap k ++ (k new ++ extra) ++
        (l.drop (i + 1)).flatMap k) := by
    simpa only [List.append_assoc] using
      ((List.perm_append_comm : List.Perm
          ((l.drop (i + 1)).flatMap k ++ extra)
          (extra ++ (l.drop (i + 1)).flatMap k))).append_left
        ((l.take i).flatMap k ++ k new)
  have hrepl : List.Perm
      ((l.take i).flatMap k ++ (k new ++ extra) ++
        (l.drop (i + 1)).flatMap k)
      ((l.take i).flatMap k ++ k l[i] ++
        (l.drop (i + 1)).flatMap k) := by
    simpa only [List.append_assoc] using
      (hpart.append_right ((l.drop (i + 1)).flatMap k)).append_left
        ((l.take i).flatMap k)
  have hfinal :
      (l.take i).flatMap k ++ k l[i] ++ (l.drop (i + 1)).flatMap k =
        l.flatMap k := by
    have hl : l = l.take i ++ l[i] :: l.drop (i + 1) := by
      calc
        l = l.take (i + 1) ++ l.drop (i + 1) :=
          (List.take_append_drop (i + 1) l).symm
        _ = l.take i ++ l[i] :: l.drop (i + 1) := by
          rw [List.take_succ_eq_append_getElem hi]
          simp
    conv_rhs => rw [hl]
    simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.append_assoc]
  simpa only [List.append_assoc] using
    hswap.trans (hrepl.trans (List.Perm.of_eq hfinal))

theorem inlineSite_allDefs_perm {f : Func} {bi ci : Nat} {site : Block}
    {ds as : List ValId} (hbi : bi < f.blocks.size)
    (hsite : f.blocks[bi]? = some site) (hci : ci < site.instrs.length)
    (hcall : site.instrs[ci]? = some (.call ds fid as)) :
    let callBlock : Block :=
      { params := site.params, instrs := site.instrs.take ci,
        term := .jump ⟨f.blocks.size + entry, []⟩ }
    let contBlock : Block :=
      { params := ds, instrs := site.instrs.drop (ci + 1), term := site.term }
    List.Perm
      ((f.blocks.set! bi callBlock).toList.flatMap blockAllDefs ++
        blockAllDefs contBlock)
      (f.blocks.toList.flatMap blockAllDefs) := by
  dsimp only
  have hget : site.instrs[ci] = .call ds fid as := by
    rw [List.getElem?_eq_getElem hci] at hcall
    exact Option.some.inj hcall
  have his : site.instrs = site.instrs.take ci ++
      .call ds fid as :: site.instrs.drop (ci + 1) := by
    calc
      site.instrs = site.instrs.take ci ++ site.instrs.drop ci :=
        (List.take_append_drop ci site.instrs).symm
      _ = site.instrs.take ci ++
          .call ds fid as :: site.instrs.drop (ci + 1) := by
        rw [List.drop_eq_getElem_cons hci, hget]
  have hdefs : site.instrs.flatMap Instr.defs =
      (site.instrs.take ci).flatMap Instr.defs ++ ds ++
        (site.instrs.drop (ci + 1)).flatMap Instr.defs := by
    conv_lhs => rw [his]
    simp [Instr.defs, List.append_assoc]
  have hpart : List.Perm
      (blockAllDefs
          { params := site.params, instrs := site.instrs.take ci,
            term := .jump ⟨f.blocks.size + entry, []⟩ } ++
        blockAllDefs
          { params := ds, instrs := site.instrs.drop (ci + 1), term := site.term })
      (blockAllDefs site) := by
    apply List.Perm.of_eq
    unfold blockAllDefs
    rw [hdefs]
    simp only [List.append_assoc]
  have hlistGet : f.blocks.toList[bi] = site := by
    rw [Array.getElem?_eq_getElem hbi] at hsite
    exact Option.some.inj hsite
  have hpart' : List.Perm
      (blockAllDefs
          { params := site.params, instrs := site.instrs.take ci,
            term := .jump ⟨f.blocks.size + entry, []⟩ } ++
        blockAllDefs
          { params := ds, instrs := site.instrs.drop (ci + 1), term := site.term })
      (blockAllDefs f.blocks.toList[bi]) := by
    rw [hlistGet]
    exact hpart
  simpa [Array.set!, Array.toList_setIfInBounds] using
    flatMap_set_append_perm f.blocks.toList blockAllDefs
      (by simpa using hbi)
      { params := site.params, instrs := site.instrs.take ci,
        term := .jump ⟨f.blocks.size + entry, []⟩ }
      (blockAllDefs
        { params := ds, instrs := site.instrs.drop (ci + 1), term := site.term })
      hpart'

theorem mem_allDefs_le_maxVal {f : Func} {x : ValId} (hx : x ∈ f.allDefs) :
    x ≤ maxVal f := by
  rw [allDefs_eq] at hx
  rcases List.mem_append.mp hx with hp | hb
  · exact param_le_maxVal hp
  · obtain ⟨b, hb, hx⟩ := List.mem_flatMap.mp hb
    rcases List.mem_append.mp hx with hp | hi
    · exact blockParam_le_maxVal hb hp
    · obtain ⟨i, hi, hd⟩ := List.mem_flatMap.mp hi
      exact instrDef_le_maxVal hb hi hd

theorem inlineReplayBlock_allDefs (rho : ValId → ValId)
    (beta : BlockId → BlockId) (contId : BlockId) (b : Block) :
    blockAllDefs (inlineReplayBlock rho beta contId b) =
      (blockAllDefs b).map rho := by
  exact blockAllDefs_rename b rho _

theorem inlineReplayBlocks_allDefs (rho : ValId → ValId)
    (beta : BlockId → BlockId) (contId : BlockId) (g : Func) :
    (g.blocks.map (inlineReplayBlock rho beta contId)).toList.flatMap blockAllDefs =
      (g.blocks.toList.flatMap blockAllDefs).map rho := by
  simp only [Array.toList_map, List.flatMap_map, inlineReplayBlock_allDefs]
  rw [List.map_flatMap]

theorem calleeBody_not_param {g : Func} (hnd : g.allDefs.Nodup)
    {x : ValId} (hx : x ∈ g.blocks.toList.flatMap blockAllDefs) : x ∉ g.params := by
  rw [allDefs_eq] at hnd
  exact fun hp => (List.nodup_append.mp hnd).2.2 x hp x hx rfl

theorem inlineBody_map_eq_shift {g : Func} {as : List ValId} {off : Nat}
    (hnd : g.allDefs.Nodup) :
    (g.blocks.toList.flatMap blockAllDefs).map (inlineRho g.params as off) =
      (g.blocks.toList.flatMap blockAllDefs).map (fun x => x + off) := by
  apply List.map_congr_left
  intro x hx
  exact inlineRho_of_not_param (calleeBody_not_param hnd hx)

theorem inlineSplice_allDefs_perm {f g f' : Func} {bi ci : Nat}
    {site : Block} {ds as : List ValId} {off contId : Nat}
    {rho : ValId → ValId} {beta : BlockId → BlockId}
    {callBlock cont : Block}
    (hbi : bi < f.blocks.size) (hsite : f.blocks[bi]? = some site)
    (hci : ci < site.instrs.length)
    (hcall : site.instrs[ci]? = some (.call ds fid as))
    (hoff : off = Nat.max (maxVal f) (maxVal g) + 1)
    (hrho : rho = inlineRho g.params as off)
    (hcallBlock : callBlock =
      { params := site.params, instrs := site.instrs.take ci,
        term := .jump ⟨f.blocks.size + g.entry, []⟩ })
    (hcont : cont =
      { params := ds, instrs := site.instrs.drop (ci + 1), term := site.term })
    (hblocks : f'.blocks =
      (f.blocks.set! bi callBlock) ++
        g.blocks.map (inlineReplayBlock rho beta contId) ++ #[cont])
    (hparams : f'.params = f.params) (hgnd : g.allDefs.Nodup) :
    List.Perm f'.allDefs
      (f.allDefs ++
        (g.blocks.toList.flatMap blockAllDefs).map (fun x => x + off)) := by
  have hsiteDefs := inlineSite_allDefs_perm (fid := fid) (entry := g.entry)
    hbi hsite hci hcall
  rw [← hcallBlock, ← hcont] at hsiteDefs
  have hspliced :
      (g.blocks.map (inlineReplayBlock rho beta contId)).toList.flatMap blockAllDefs =
        (g.blocks.toList.flatMap blockAllDefs).map (fun x => x + off) := by
    rw [inlineReplayBlocks_allDefs, hrho, inlineBody_map_eq_shift hgnd]
  have hbody : List.Perm
      ((f.blocks.set! bi callBlock).toList.flatMap blockAllDefs ++
        (g.blocks.map (inlineReplayBlock rho beta contId)).toList.flatMap blockAllDefs ++
        blockAllDefs cont)
      (f.blocks.toList.flatMap blockAllDefs ++
        (g.blocks.toList.flatMap blockAllDefs).map (fun x => x + off)) := by
    let A := (f.blocks.set! bi callBlock).toList.flatMap blockAllDefs
    let S := (g.blocks.map (inlineReplayBlock rho beta contId)).toList.flatMap blockAllDefs
    let C := blockAllDefs cont
    have hswap : List.Perm (A ++ S ++ C) (A ++ C ++ S) := by
      simpa only [List.append_assoc] using
        ((List.perm_append_comm : List.Perm (S ++ C) (C ++ S))).append_left A
    have hrepl : List.Perm (A ++ C ++ S)
        (f.blocks.toList.flatMap blockAllDefs ++ S) :=
      hsiteDefs.append_right S
    simpa only [A, S, C, hspliced] using hswap.trans hrepl
  unfold Func.allDefs
  rw [hparams, hblocks, Array.toList_append, Array.toList_append]
  simp only [show #[cont].toList = [cont] from rfl, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]
  simpa only [List.append_assoc] using hbody.append_left f.params

theorem inlineSplice_allDefs_nodup {f g f' : Func} {bi ci : Nat}
    {site : Block} {ds as : List ValId} {off contId : Nat}
    {rho : ValId → ValId} {beta : BlockId → BlockId}
    {callBlock cont : Block}
    (hbi : bi < f.blocks.size) (hsite : f.blocks[bi]? = some site)
    (hci : ci < site.instrs.length)
    (hcall : site.instrs[ci]? = some (.call ds fid as))
    (hoff : off = Nat.max (maxVal f) (maxVal g) + 1)
    (hrho : rho = inlineRho g.params as off)
    (hcallBlock : callBlock =
      { params := site.params, instrs := site.instrs.take ci,
        term := .jump ⟨f.blocks.size + g.entry, []⟩ })
    (hcont : cont =
      { params := ds, instrs := site.instrs.drop (ci + 1), term := site.term })
    (hblocks : f'.blocks =
      (f.blocks.set! bi callBlock) ++
        g.blocks.map (inlineReplayBlock rho beta contId) ++ #[cont])
    (hparams : f'.params = f.params)
    (hfnd : f.allDefs.Nodup) (hgnd : g.allDefs.Nodup) : f'.allDefs.Nodup := by
  have hp := inlineSplice_allDefs_perm (fid := fid) hbi hsite hci hcall
    hoff hrho hcallBlock hcont hblocks hparams hgnd
  apply hp.nodup_iff.mpr
  apply List.nodup_append.mpr
  refine ⟨hfnd, ?_, ?_⟩
  · have hbody : (g.blocks.toList.flatMap blockAllDefs).Nodup := by
      rw [allDefs_eq] at hgnd
      exact (List.nodup_append.mp hgnd).2.1
    exact hbody.map (fun _ _ h => Nat.add_right_cancel h)
  · intro x hx y hy hxy
    have hxlt : x < off := by
      rw [hoff]
      exact lt_of_le_of_lt (mem_allDefs_le_maxVal hx)
        (maxVal_lt_inlineOffset_left f g)
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
    have hge : off ≤ z + off := by omega
    apply Nat.not_le_of_lt hxlt
    rw [hxy]
    exact hge

def blockCheckB (blocks : Array Block) (nrets nFuncs : Nat) (b : Block) : Bool :=
  (match b.term with
   | .ret vs => vs.length = nrets
   | _ => true)
  && (b.term.edges.all fun e =>
      match blocks[e.target]? with
      | some tb => e.args.length = tb.params.length
      | none => false)
  && b.instrs.all fun i =>
    match i with
    | .op ds _ _ => ds.length ≤ 1
    | .call _ g _ => g < nFuncs
    | _ => true

def BlockWF (blocks : Array Block) (nrets nFuncs : Nat) (b : Block) : Prop :=
  (match b.term with
   | .ret vs => vs.length = nrets
   | _ => True)
  ∧ (∀ e ∈ b.term.edges, ∃ tb, blocks[e.target]? = some tb ∧
      e.args.length = tb.params.length)
  ∧ ∀ i ∈ b.instrs,
    match i with
    | .op ds _ _ => ds.length ≤ 1
    | .call _ g _ => g < nFuncs
    | _ => True

theorem blockCheckB_eq_true {blocks : Array Block} {nrets nFuncs : Nat}
    {b : Block} : blockCheckB blocks nrets nFuncs b = true ↔
      BlockWF blocks nrets nFuncs b := by
  unfold blockCheckB BlockWF
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨hret, hedge⟩, hinstr⟩
    refine ⟨?_, ?_, ?_⟩
    · cases ht : b.term <;> simp_all [ht]
    · intro e he
      have h := hedge e he
      split at h <;> simp_all
    · intro i hi
      have h := hinstr i hi
      cases i <;> simpa using h
  · rintro ⟨hret, hedge, hinstr⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · cases ht : b.term <;> simp_all [ht]
    · intro e he
      obtain ⟨tb, htb, hlen⟩ := hedge e he
      rw [htb]
      simpa using hlen
    · intro i hi
      have h := hinstr i hi
      cases i <;> simpa using h

theorem func_wfCheck_iff {f : Func} {nFuncs : Nat} :
    f.wfCheck nFuncs = true ↔
      f.allDefs.Nodup ∧ f.entry < f.blocks.size ∧
      (∃ eb, f.blocks[f.entry]? = some eb ∧ eb.params = []) ∧
      ∀ b ∈ f.blocks.toList, BlockWF f.blocks f.nrets nFuncs b := by
  unfold Func.wfCheck
  change (f.allDefs.Nodup && f.entry < f.blocks.size &&
      (match f.blocks[f.entry]? with
       | some b => b.params.isEmpty
       | none => false) &&
      f.blocks.all (blockCheckB f.blocks f.nrets nFuncs)) = true ↔ _
  simp only [Bool.and_eq_true, decide_eq_true_eq, Array.all_eq_true_iff_forall_mem,
    blockCheckB_eq_true]
  constructor
  · rintro ⟨⟨⟨hnd, hentry⟩, hempty⟩, hall⟩
    rcases hget : f.blocks[f.entry]? with _ | eb
    · simp [hget] at hempty
    · refine ⟨hnd, hentry, ⟨eb, rfl, ?_⟩, ?_⟩
      · exact List.isEmpty_iff.mp (by simpa [hget] using hempty)
      · intro b hb
        exact hall b (by simpa using hb)
  · rintro ⟨hnd, hentry, ⟨eb, heb, hempty⟩, hall⟩
    refine ⟨⟨⟨hnd, hentry⟩, ?_⟩, ?_⟩
    · rw [heb]
      simp [hempty]
    · intro i hi
      exact hall i (by simpa using hi)

theorem inlineBlocks_old_lookup {f f' g : Func} {bi : Nat} {site callBlock cont : Block}
    {rho : ValId → ValId} {beta : BlockId → BlockId} {contId : Nat}
    (hbi : bi < f.blocks.size) (hsite : f.blocks[bi]? = some site)
    (hcallParams : callBlock.params = site.params)
    (hblocks : f'.blocks =
      (f.blocks.set! bi callBlock) ++
        g.blocks.map (inlineReplayBlock rho beta contId) ++ #[cont])
    {i : BlockId} {b : Block} (hb : f.blocks[i]? = some b) :
    ∃ b', f'.blocks[i]? = some b' ∧ b'.params = b.params := by
  have hi : i < f.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  have hprefix : f'.blocks[i]? = (f.blocks.set! bi callBlock)[i]? := by
    have hout : i < ((f.blocks.set! bi callBlock) ++
        g.blocks.map (inlineReplayBlock rho beta contId)).size := by
      simpa using lt_of_lt_of_le hi (Nat.le_add_right f.blocks.size g.blocks.size)
    rw [hblocks, Array.getElem?_append_left hout,
      Array.getElem?_append_left (by simpa using hi)]
  by_cases h : i = bi
  · subst i
    refine ⟨callBlock, ?_, ?_⟩
    · rw [hprefix]
      simp [Array.set!, hbi]
    · have hbsite : b = site := Option.some.inj (hb.symm.trans hsite)
      subst b
      exact hcallParams
  · refine ⟨b, ?_, rfl⟩
    rw [hprefix]
    simpa [Array.set!, Array.getElem?_setIfInBounds_ne (Ne.symm h)] using hb

theorem BlockWF.with_new_targets {old new : Array Block} {nrets nFuncs : Nat}
    {b : Block} (h : BlockWF old nrets nFuncs b)
    (htarget : ∀ {e tb}, e ∈ b.term.edges → old[e.target]? = some tb →
      ∃ tb', new[e.target]? = some tb' ∧ tb'.params = tb.params) :
    BlockWF new nrets nFuncs b := by
  refine ⟨h.1, ?_, h.2.2⟩
  intro e he
  obtain ⟨tb, htb, hlen⟩ := h.2.1 e he
  obtain ⟨tb', htb', hp⟩ := htarget he htb
  exact ⟨tb', htb', by simpa [hp] using hlen⟩

theorem inlineCallBlock_wf {f f' g : Func} {bi ci : Nat} {site callBlock cont : Block}
    {rho : ValId → ValId} {beta : BlockId → BlockId} {contId nFuncs : Nat}
    (hsiteWf : BlockWF f.blocks f.nrets nFuncs site)
    (hgentry : g.entry = 0) (hgentryParams : ∃ eb, g.blocks[g.entry]? = some eb ∧ eb.params = [])
    (hcallBlock : callBlock =
      { params := site.params, instrs := site.instrs.take ci,
        term := .jump ⟨f.blocks.size + g.entry, []⟩ })
    (hblocks : f'.blocks =
      (f.blocks.set! bi callBlock) ++
        g.blocks.map (inlineReplayBlock rho beta contId) ++ #[cont])
    (hnrets : f'.nrets = f.nrets) :
    BlockWF f'.blocks f'.nrets nFuncs callBlock := by
  subst callBlock
  refine ⟨by simp, ?_, ?_⟩
  · intro e he
    simp only [Term.edges, List.mem_singleton] at he
    subst e
    obtain ⟨eb, heb, hp⟩ := hgentryParams
    have hget := inlineReplayBlock_get
      (f' := f') (preBlocks := f.blocks.set! bi
        { params := site.params, instrs := site.instrs.take ci,
          term := .jump ⟨f.blocks.size + g.entry, []⟩ })
      (ρ := rho) (β := beta) (contId := contId) (cont := cont)
      hblocks heb
    rw [hgentry] at hget ⊢
    refine ⟨inlineReplayBlock rho beta contId eb, by simpa using hget, ?_⟩
    simp [inlineReplayBlock, hp]
  · intro i hi
    exact hsiteWf.2.2 i (List.mem_of_mem_take hi)

theorem inlineContBlock_wf {f f' g : Func} {bi ci : Nat} {site callBlock cont : Block}
    {rho : ValId → ValId} {beta : BlockId → BlockId} {contId nFuncs : Nat}
    (hbi : bi < f.blocks.size) (hsite : f.blocks[bi]? = some site)
    (hsiteWf : BlockWF f.blocks f.nrets nFuncs site)
    (hcallParams : callBlock.params = site.params)
    (hcont : cont =
      { params := ds, instrs := site.instrs.drop (ci + 1), term := site.term })
    (hblocks : f'.blocks =
      (f.blocks.set! bi callBlock) ++
        g.blocks.map (inlineReplayBlock rho beta contId) ++ #[cont])
    (hnrets : f'.nrets = f.nrets) :
    BlockWF f'.blocks f'.nrets nFuncs cont := by
  subst cont
  rw [hnrets]
  refine ⟨hsiteWf.1, ?_, ?_⟩
  · intro e he
    obtain ⟨tb, htb, hlen⟩ := hsiteWf.2.1 e he
    obtain ⟨tb', htb', hp⟩ := inlineBlocks_old_lookup hbi hsite hcallParams
      hblocks htb
    exact ⟨tb', htb', by simpa [hp] using hlen⟩
  · intro i hi
    exact hsiteWf.2.2 i (List.mem_of_mem_drop hi)

theorem inlineReplayBlock_wf {f f' g : Func} {bi : Nat} {callBlock cont gb : Block}
    {rho : ValId → ValId} {beta : BlockId → BlockId} {contId nFuncs : Nat}
    (hgb : gb ∈ g.blocks.toList) (hgbWf : BlockWF g.blocks g.nrets nFuncs gb)
    (hbeta : ∀ i, beta i = f.blocks.size + i)
    (hcontId : contId = f.blocks.size + g.blocks.size)
    (hcontParams : cont.params = ds) (hnrets : g.nrets = ds.length)
    (hblocks : f'.blocks =
      (f.blocks.set! bi callBlock) ++
        g.blocks.map (inlineReplayBlock rho beta contId) ++ #[cont])
    (hfNrets : f'.nrets = f.nrets) :
    BlockWF f'.blocks f'.nrets nFuncs (inlineReplayBlock rho beta contId gb) := by
  refine ⟨?_, ?_, ?_⟩
  · cases ht : gb.term <;>
      simp [inlineReplayBlock, inlineReplayTerm, renameTerm, ht, hfNrets]
  · intro e he
    cases ht : gb.term with
    | jump old =>
        simp only [inlineReplayBlock, inlineReplayTerm, ht, renameTerm, Term.edges,
          List.mem_singleton] at he
        subst e
        obtain ⟨tb, htb, hlen⟩ := hgbWf.2.1 old (by rw [ht]; simp [Term.edges])
        have hget := inlineReplayBlock_get
          (f' := f') (preBlocks := f.blocks.set! bi callBlock)
          (ρ := rho) (β := beta) (contId := contId) (cont := cont) hblocks htb
        refine ⟨inlineReplayBlock rho beta contId tb, ?_, ?_⟩
        · change f'.blocks[beta old.target]? = _
          rw [hbeta]
          simpa using hget
        · simpa [inlineReplayBlock] using hlen
    | branch c et ef =>
        simp only [inlineReplayBlock, inlineReplayTerm, ht, renameTerm, Term.edges,
          List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl
        · obtain ⟨tb, htb, hlen⟩ := hgbWf.2.1 et (by rw [ht]; simp [Term.edges])
          have hget := inlineReplayBlock_get
            (f' := f') (preBlocks := f.blocks.set! bi callBlock)
            (ρ := rho) (β := beta) (contId := contId) (cont := cont) hblocks htb
          refine ⟨inlineReplayBlock rho beta contId tb, ?_, ?_⟩
          · change f'.blocks[beta et.target]? = _
            rw [hbeta]
            simpa using hget
          · simpa [inlineReplayBlock] using hlen
        · obtain ⟨tb, htb, hlen⟩ := hgbWf.2.1 ef (by rw [ht]; simp [Term.edges])
          have hget := inlineReplayBlock_get
            (f' := f') (preBlocks := f.blocks.set! bi callBlock)
            (ρ := rho) (β := beta) (contId := contId) (cont := cont) hblocks htb
          refine ⟨inlineReplayBlock rho beta contId tb, ?_, ?_⟩
          · change f'.blocks[beta ef.target]? = _
            rw [hbeta]
            simpa using hget
          · simpa [inlineReplayBlock] using hlen
    | ret vals =>
        simp only [inlineReplayBlock, inlineReplayTerm, ht, Term.edges,
          List.mem_singleton] at he
        subst e
        have hget := inlineContBlock_get
          (f' := f') (g := g) (preBlocks := f.blocks.set! bi callBlock)
          (ρ := rho) (β := beta) (contId := contId) (cont := cont) hblocks
        refine ⟨cont, ?_, ?_⟩
        · rw [hcontId]
          simpa using hget
        · have hret := hgbWf.1
          simp only [ht] at hret
          simpa [hcontParams, hnrets] using hret
    | halt yop args =>
        simp [inlineReplayBlock, inlineReplayTerm, renameTerm, ht, Term.edges] at he
  · intro i hi
    simp only [inlineReplayBlock] at hi
    obtain ⟨old, hold, heq⟩ := List.mem_map.mp hi
    subst i
    have hold := hgbWf.2.2 old hold
    cases old <;> simpa [renameInstr] using hold

theorem inlineOnce_nrets {counts : Array Nat} {funcs : Array Func}
    {f f' : Func} (hio : inlineOnce counts funcs f = some f') :
    f'.nrets = f.nrets := by
  obtain ⟨bi, site, ci, ds, fid, as, g, hbi, hsite, hci, hcall, hfunc,
    hcount, hlen, hnrets, hentry, hf'⟩ := inlineOnce_inv hio
  rw [hf']

theorem inlineReplayBlock_eq (rho : ValId → ValId) (beta : BlockId → BlockId)
    (contId : BlockId) (gb : Block) :
    inlineReplayBlock rho beta contId gb =
      { params := gb.params.map rho
        instrs := gb.instrs.map (renameInstr rho)
        term := match gb.term with
          | .ret vs => .jump ⟨contId, vs.map rho⟩
          | t => renameTerm rho beta t } := by
  rcases gb with ⟨params, instrs, term⟩
  cases term <;> rfl

theorem inlineOnce_wf {counts : Array Nat} {funcs : Array Func}
    {f f' : Func} {nFuncs : Nat}
    (hfuncs : ∀ {fid : FuncId} {g : Func},
      funcs[fid]? = some g → g.wfCheck nFuncs = true)
    (hfwf : f.wfCheck nFuncs = true)
    (hio : inlineOnce counts funcs f = some f') :
    f'.wfCheck nFuncs = true := by
  obtain ⟨bi, site, ci, ds, fid, as, g, hbi, hsite, hci, hcall, hfunc,
    hcount, hlen, hnrets, hentry, hf'⟩ := inlineOnce_inv hio
  let off := Nat.max (maxVal f) (maxVal g) + 1
  let rho := fun v =>
    match (g.params.zip as).find? (fun pa => pa.1 == v) with
    | some pa => pa.2
    | none => v + off
  let beta : BlockId → BlockId := fun i => f.blocks.size + i
  let contId := f.blocks.size + g.blocks.size
  let callBlock : Block :=
    { params := site.params, instrs := site.instrs.take ci,
      term := .jump ⟨f.blocks.size + g.entry, []⟩ }
  let cont : Block :=
    { params := ds, instrs := site.instrs.drop (ci + 1), term := site.term }
  let replay : Block → Block := fun gb =>
    { params := gb.params.map rho
      instrs := gb.instrs.map (renameInstr rho)
      term := match gb.term with
        | .ret vs => .jump ⟨contId, vs.map rho⟩
        | t => renameTerm rho beta t }
  have hfRaw : f' =
      { f with blocks := (f.blocks.set! bi callBlock) ++
          g.blocks.map replay ++ #[cont] } := by
    simpa [off, rho, beta, contId, callBlock, cont, replay, inlineRho] using hf'
  have hreplay : g.blocks.map replay =
      g.blocks.map (inlineReplayBlock rho beta contId) := by
    apply congrArg (fun k : Block → Block => g.blocks.map k)
    funext gb
    exact (inlineReplayBlock_eq rho beta contId gb).symm
  have hfNamed : f' =
      { f with blocks := (f.blocks.set! bi callBlock) ++
          g.blocks.map (inlineReplayBlock rho beta contId) ++ #[cont] } := by
    rw [hfRaw, hreplay]
  have hblocks : f'.blocks =
      (f.blocks.set! bi callBlock) ++
        g.blocks.map (inlineReplayBlock rho beta contId) ++ #[cont] := by
    rw [hfNamed]
  have hparams : f'.params = f.params := by rw [hfNamed]
  have hnrets' : f'.nrets = f.nrets := by rw [hfNamed]
  have hentry' : f'.entry = f.entry := by rw [hfNamed]
  have hcallBlock : callBlock =
      { params := site.params, instrs := site.instrs.take ci,
        term := .jump ⟨f.blocks.size + g.entry, []⟩ } := rfl
  have hcont : cont =
      { params := ds, instrs := site.instrs.drop (ci + 1), term := site.term } := rfl
  have hcallParams : callBlock.params = site.params := rfl
  have hcontParams : cont.params = ds := rfl
  have hgwf := hfuncs hfunc
  obtain ⟨hfnd, hfentry, ⟨feb, hfeb, hfempty⟩, hfblocks⟩ :=
    func_wfCheck_iff.mp hfwf
  obtain ⟨hgnd, hgentryLt, ⟨geb, hgeb, hgempty⟩, hgblocks⟩ :=
    func_wfCheck_iff.mp hgwf
  have hsiteWf : BlockWF f.blocks f.nrets nFuncs site :=
    hfblocks site (block_mem_of_getElem? hsite)
  apply func_wfCheck_iff.mpr
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact inlineSplice_allDefs_nodup (fid := fid) hbi hsite hci hcall rfl rfl
      hcallBlock hcont hblocks hparams hfnd hgnd
  · rw [hentry']
    exact lt_of_lt_of_le hfentry (by rw [hblocks]; simp)
  · obtain ⟨feb', hfeb', hp⟩ := inlineBlocks_old_lookup hbi hsite hcallParams
      hblocks hfeb
    exact ⟨feb', by simpa [hentry'] using hfeb', by simpa [hp] using hfempty⟩
  · intro b hb
    have hbarr : b ∈ f'.blocks := by simpa using hb
    rw [hblocks] at hbarr
    simp only [Array.mem_append, Array.mem_map, Array.mem_singleton] at hbarr
    rcases hbarr with (hbset | ⟨gb, hgb, rfl⟩) | rfl
    · rcases Array.mem_or_eq_of_mem_setIfInBounds hbset with hold | rfl
      · rw [hnrets']
        apply (hfblocks b (by simpa using hold)).with_new_targets
        intro e tb he htb
        exact inlineBlocks_old_lookup hbi hsite hcallParams hblocks htb
      · exact inlineCallBlock_wf hsiteWf hentry ⟨geb, hgeb, hgempty⟩
          hcallBlock hblocks hnrets'
    · exact inlineReplayBlock_wf (by simpa using hgb)
        (hgblocks gb (by simpa using hgb)) (fun _ => rfl) rfl hcontParams hnrets
        hblocks hnrets'
    · exact inlineContBlock_wf hbi hsite hsiteWf hcallParams hcont hblocks hnrets'

end Passes

section
variable [model : ExternalModel]

/- **One splice preserves executions.**

The callee-side part of the interesting `Exec.call` / `Exec.callHalt` node is
now proved by `Passes.inlineReplay_exec`. In the inlined function that node
becomes: `jump` into the
spliced callee entry, the callee's own derivation re-played inside the caller,
and its `Exec.ret` re-played as the `jump ⟨contId, vs.map ρ⟩` that binds `ds` in
`contBlock`. The register-file obligation is exactly `LiveAgree`-style
reasoning under the renaming `ρ`: the callee ran from the *fresh* file
`Regs.empty.setMany g.params args`, while the splice runs from the caller's file
extended at `ρ`-images, and the two agree on everything the callee body reads
because (i) `ρ` sends the callee's parameters to the caller ids holding `args`
and (ii) `ρ` sends everything else above `maxVal f`, so no caller binding is
disturbed — `Regs.setMany_congr` plus `exec_congr` (both proved) are the
work-horses. The `.halt` case is the same derivation truncated.

`Passes.inlineOnce_inv` above supplies the site inversion:
`bi`, `ci`, the selected call/callee, every guard, and the complete splice
equation.  The remaining first proof object is the renamed-callee `Exec` replay.
The non-injective-formal problem is discharged by the partitioned invariants
`Passes.RenamedAgree` and `Passes.CallerFrame`: the former is one-way (only a
successful callee read must be reproduced), while the latter preserves every
caller register below `off`. `Passes.inlineReplay_exec` carries both through
renamed instructions and block edges, proves appended-block lookups, turns
callee `ret` into the continuation jump, and propagates halts.

The caller-side proof below is indexed by execution location.  Its induction
over the enclosing `Exec` derivation distinguishes four locations:
an ordinary caller block, the prefix before `(bi, ci)`, the selected call itself,
and the new continuation containing `drop (ci + 1)`.  On a back-edge to `bi` it
must re-enter the prefix case (and inline the call again); on a return it must
enter the continuation case with the `CallerFrame` produced by
`inlineReplay_exec`.  A plain structural equality test on the current
instruction is insufficient because an equal call instruction may occur in the
prefix at a different position. -/
omit model in
theorem Passes.inlineCallerRest_before {bi ci entry k : Nat} {site : Block}
    {i : Instr} {is : List Instr} {t : Term} (hk : k < ci)
    (hdrop : site.instrs.drop k = i :: is) :
    inlineCallerRest bi ci entry bi k site ⟨i :: is, t⟩ =
      ⟨i :: (site.instrs.take ci).drop (k + 1), .jump ⟨entry, []⟩⟩ := by
  have hki : k < site.instrs.length := by
    have hlen := congrArg List.length hdrop
    simp at hlen
    omega
  have hkt : k < (site.instrs.take ci).length := by simp; omega
  have hi : site.instrs[k] = i := by
    rw [List.drop_eq_getElem_cons hki] at hdrop
    exact (List.cons.inj hdrop).1
  simp only [inlineCallerRest, true_and, le_of_lt hk, if_true]
  congr 1
  rw [List.drop_eq_getElem_cons hkt]
  congr
  simpa using hi

omit model in
theorem Passes.inlineCallerRest_site (bi ci entry : Nat) (site : Block)
    (r : Rest) :
    inlineCallerRest bi ci entry bi ci site r = ⟨[], .jump ⟨entry, []⟩⟩ := by
  simp [inlineCallerRest]

omit model in
theorem Passes.inlineCallerRest_cons_of_not_site
    {bi ci entry j k : Nat} {site cur : Block} {i : Instr}
    {is : List Instr} {t : Term}
    (hcur : j = bi → cur = site) (hne : j ≠ bi ∨ k ≠ ci)
    (hdrop : cur.instrs.drop k = i :: is) :
    inlineCallerRest bi ci entry j k site ⟨i :: is, t⟩ =
      let r := inlineCallerRest bi ci entry j (k + 1) site ⟨is, t⟩
      ⟨i :: r.instrs, r.term⟩ := by
  by_cases hj : j = bi
  · subst j
    have hcur' : cur = site := hcur rfl
    subst cur
    rcases hne with hne | hne
    · exact (hne rfl).elim
    · rcases Nat.lt_or_gt_of_ne hne with hk | hk
      · rw [inlineCallerRest_before hk hdrop]
        simp [inlineCallerRest, Nat.succ_le_iff.mpr hk]
      · simp [inlineCallerRest, Nat.not_le_of_lt hk,
          Nat.not_le_of_lt (lt_trans hk (Nat.lt_succ_self k))]
  · simp [inlineCallerRest, hj]

omit model in
theorem Passes.head_eq_of_drop_eq_cons {xs : List α} {k : Nat} {x y : α}
    {ys : List α} (hx : xs[k]? = some x) (hdrop : xs.drop k = y :: ys) :
    y = x := by
  have hk : k < xs.length := (List.getElem?_eq_some_iff.mp hx).1
  rw [List.drop_eq_getElem_cons hk] at hdrop
  have hy := (List.cons.inj hdrop).1
  rw [List.getElem?_eq_getElem hk] at hx
  exact hy.symm.trans (Option.some.inj hx)

omit model in
theorem Passes.drop_succ_eq_of_drop_eq_cons {xs : List α} {k : Nat}
    {x : α} {ys : List α} (hdrop : xs.drop k = x :: ys) :
    xs.drop (k + 1) = ys := by
  rw [← List.drop_drop, hdrop]
  rfl

omit model in
theorem Passes.mem_of_drop_eq_cons {xs : List α} {k : Nat}
    {x : α} {ys : List α} (hdrop : xs.drop k = x :: ys) : x ∈ xs := by
  rw [← List.take_append_drop k xs, hdrop]
  simp

omit model in
theorem Passes.CallerFrame.getMany {off : Nat} {R R' : Regs}
    (h : CallerFrame off R R') {xs : List ValId}
    (hxs : ∀ x ∈ xs, x < off) : R.getMany xs = R'.getMany xs := by
  exact Regs.getMany_congr fun x hx => (h x (hxs x hx)).symm

omit model in
theorem Passes.CallerFrame.setMany {off : Nat} {R R' : Regs}
    (h : CallerFrame off R R') {xs : List ValId} (vals : List U256) :
    CallerFrame off (R.setMany xs vals) (R'.setMany xs vals) := by
  intro x hx
  exact Regs.setMany_congr (S := fun y => y < off) h xs vals x hx

/-- Caller execution replay indexed by the exact source location `(j,k)`.
This is the positional invariant needed to identify the unique splice site. -/
theorem Passes.inlineCaller_exec
    {P : Prog} {f f' g : Func} {bi ci : Nat} {site : Block}
    {ds as : List ValId} {fid off contId : Nat}
    {ρ : ValId → ValId} {β : BlockId → BlockId} {cont callBlock : Block}
    {R Ri : Regs} {st : EvmState} {rest : Rest} {res : FRes}
    (hsite : f.blocks[bi]? = some site)
    (hci : ci < site.instrs.length)
    (hcall : site.instrs[ci]? = some (.call ds fid as))
    (hfunc : P.funcs[fid]? = some g)
    (hgwf : g.wfCheck P.funcs.size = true)
    (hoff : off = Nat.max (Passes.maxVal f) (Passes.maxVal g) + 1)
    (hρ : ρ = inlineRho g.params as off)
    (hβ : ∀ i, β i = f.blocks.size + i)
    (hcontId : contId = f.blocks.size + g.blocks.size)
    (hentry : g.entry = 0)
    (hlen : g.params.length = as.length)
    (hnrets : g.nrets = ds.length)
    (hcallBlock : callBlock =
      { params := site.params, instrs := site.instrs.take ci,
        term := .jump ⟨f.blocks.size + g.entry, []⟩ })
    (hcont : cont =
      { params := ds, instrs := site.instrs.drop (ci + 1), term := site.term })
    (hblocks : f'.blocks =
      (f.blocks.set! bi callBlock) ++
        g.blocks.map (inlineReplayBlock ρ β contId) ++ #[cont])
    (hexec : Exec (model := model) P f R st rest res)
    {j k : Nat} {cur : Block}
    (hcur : f.blocks[j]? = some cur)
    (hdrop : cur.instrs.drop k = rest.instrs)
    (hterm : cur.term = rest.term)
    (hframe : CallerFrame off R Ri) :
    Exec (model := model) P f' Ri st
      (inlineCallerRest bi ci (f.blocks.size + g.entry) j k site rest) res := by
  have hoffCaller : Passes.maxVal f < off := by
    rw [hoff]
    exact maxVal_lt_inlineOffset_left f g
  have hoffCallee : Passes.maxVal g < off := by
    rw [hoff]
    exact maxVal_lt_inlineOffset_right f g
  have hsiteMem := block_mem_of_getElem? hsite
  have hnd : g.allDefs.Nodup := by
    unfold Func.wfCheck at hgwf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hgwf
    exact hgwf.1.1.1
  have hpsnd : g.params.Nodup := by
    exact params_nodup_of_allDefs hnd rfl
  have hret : ∀ {b : Block}, b ∈ g.blocks.toList → ∀ {xs},
      b.term = .ret xs → xs.length = ds.length := by
    intro b hb xs ht
    rw [← hnrets]
    exact wfCheck_ret_arity hgwf hb ht
  induction hexec generalizing j k cur Ri with
  | @const _ R st d v is t res htail ih =>
      have himem : Instr.const d v ∈ cur.instrs := mem_of_drop_eq_cons hdrop
      have hcurSite : j = bi → cur = site := by
        intro hj
        subst j
        exact Option.some.inj (hcur.symm.trans hsite)
      have hne : j ≠ bi ∨ k ≠ ci := by
        by_contra hn
        simp only [not_or, not_ne_iff] at hn
        obtain ⟨rfl, rfl⟩ := hn
        have hcureq := hcurSite rfl
        subst cur
        have heq := head_eq_of_drop_eq_cons hcall hdrop
        cases heq
      rw [inlineCallerRest_cons_of_not_site hcurSite hne hdrop]
      refine Exec.const (ih hsite hoff hβ hcontId hcallBlock hblocks hcur
        (drop_succ_eq_of_drop_eq_cons hdrop) hterm ?_ hoffCaller hsiteMem)
      simpa [Regs.setMany_cons, Regs.setMany_nil_left] using
        (hframe.setMany (xs := [d]) [v])
  | @op _ R st st' ods yop oas oargs rets is t res hget hop hlenRet htail ih =>
      have himem : Instr.op ods yop oas ∈ cur.instrs := mem_of_drop_eq_cons hdrop
      have hcurSite : j = bi → cur = site := by
        intro hj; subst j; exact Option.some.inj (hcur.symm.trans hsite)
      have hne : j ≠ bi ∨ k ≠ ci := by
        by_contra hn
        simp only [not_or, not_ne_iff] at hn
        obtain ⟨rfl, rfl⟩ := hn
        have hcureq := hcurSite rfl
        subst cur
        have heq := head_eq_of_drop_eq_cons hcall hdrop
        cases heq
      have hoas : ∀ x ∈ oas, x < off := by
        intro x hx
        exact lt_of_le_of_lt (instrUse_le_maxVal (block_mem_of_getElem? hcur)
          himem (by simpa [Instr.uses] using hx)) hoffCaller
      rw [inlineCallerRest_cons_of_not_site hcurSite hne hdrop]
      refine Exec.op (args := oargs) (rets := rets)
        (by rw [← hframe.getMany hoas]; exact hget) hop hlenRet
        (ih hsite hoff hβ hcontId hcallBlock hblocks hcur
          (drop_succ_eq_of_drop_eq_cons hdrop) hterm ?_ hoffCaller hsiteMem)
      exact hframe.setMany rets
  | @opHalt _ R st st' ods yop oas oargs is t hget hop =>
      have himem : Instr.op ods yop oas ∈ cur.instrs := mem_of_drop_eq_cons hdrop
      have hcurSite : j = bi → cur = site := by
        intro hj; subst j; exact Option.some.inj (hcur.symm.trans hsite)
      have hne : j ≠ bi ∨ k ≠ ci := by
        by_contra hn
        simp only [not_or, not_ne_iff] at hn
        obtain ⟨rfl, rfl⟩ := hn
        have hcureq := hcurSite rfl
        subst cur
        have heq := head_eq_of_drop_eq_cons hcall hdrop
        cases heq
      have hoas : ∀ x ∈ oas, x < off := by
        intro x hx
        exact lt_of_le_of_lt (instrUse_le_maxVal (block_mem_of_getElem? hcur)
          himem (by simpa [Instr.uses] using hx)) hoffCaller
      rw [inlineCallerRest_cons_of_not_site hcurSite hne hdrop]
      exact Exec.opHalt (args := oargs) (by rw [← hframe.getMany hoas]; exact hget) hop
  | @call fcur callee R st st' ods oas ofid oargs rvals eb is t res
      hfid hget hplen heb hbody hlenRet htail ihbody ih =>
      have himem : Instr.call ods ofid oas ∈ cur.instrs := mem_of_drop_eq_cons hdrop
      have hcurSite : j = bi → cur = site := by
        intro hj; subst j; exact Option.some.inj (hcur.symm.trans hsite)
      by_cases hat : j = bi ∧ k = ci
      · obtain ⟨rfl, rfl⟩ := hat
        have hcureq := hcurSite rfl
        subst cur
        have heq := head_eq_of_drop_eq_cons hcall hdrop
        cases heq
        have hgEq : callee = g := Option.some.inj (hfid.symm.trans hfunc)
        subst callee
        rw [inlineCallerRest_site]
        have hoas : ∀ x ∈ as, x < off := by
          intro x hx
          exact lt_of_le_of_lt (instrUse_le_maxVal hsiteMem himem
            (by simpa [Instr.uses] using hx)) hoffCaller
        have hgetRi : Ri.getMany as = some oargs := by
          rw [← hframe.getMany hoas]
          exact hget
        have hentryParams : eb.params = [] := wfCheck_entry_params_nil hgwf (by
          simpa [hentry] using heb)
        refine Exec.jump (args := [])
          (tb := inlineReplayBlock ρ β contId eb) ?_ (by simp)
          (by simp [inlineReplayBlock, hentryParams]) ?_
        · have hbcopy := inlineReplayBlock_get hblocks heb
          simpa using hbcopy
        · have hreplay := inlineReplay_exec (g := g) (f' := f')
            (preBlocks := fcur.blocks.set! j callBlock)
            (cont := cont) (ps := g.params) (as := as) (ds := ds)
            (off := off) (ρ := ρ) (β := β) (contId := contId)
            (Rc := Regs.empty.setMany g.params oargs) (Rcaller := R)
            (cres := .ret rvals st') (final := res) (b := eb)
            hρ (fun i => by simpa using hβ i) (by simpa using hcontId) hblocks
            (by rw [hcont]) hnd rfl hlen hoas
            (fun {_} hb {_} ht => hret hb ht) hbody (block_mem_of_getElem? heb)
            ⟨[], rfl, rfl⟩ (renamedAgree_entry hpsnd hlen hgetRi) hframe
            (fun s hs => by cases hs)
            (fun Rout vals s heq hRout => by
              cases heq
              have htailDrop := drop_succ_eq_of_drop_eq_cons hdrop
              rw [hcont]
              simpa [inlineCallerRest, htailDrop, hterm] using
                (ih hsite hoff hβ hcontId hcallBlock hblocks
                (j := j) (k := k + 1) (cur := site) hsite
                (drop_succ_eq_of_drop_eq_cons hdrop) hterm
                (hRout.setMany rvals) hoffCaller hsiteMem))
          simpa [inlineReplayBlock, hentryParams, Regs.setMany_nil_left] using hreplay
      · have hne : j ≠ bi ∨ k ≠ ci := by omega
        have hoas : ∀ x ∈ oas, x < off := by
          intro x hx
          exact lt_of_le_of_lt (instrUse_le_maxVal (block_mem_of_getElem? hcur)
            himem (by simpa [Instr.uses] using hx)) hoffCaller
        rw [inlineCallerRest_cons_of_not_site hcurSite hne hdrop]
        refine Exec.call (args := oargs) (rvals := rvals) (g := callee) (eb := eb)
          hfid (by rw [← hframe.getMany hoas]; exact hget) hplen heb hbody hlenRet
          (ih hsite hoff hβ hcontId hcallBlock hblocks hcur
            (drop_succ_eq_of_drop_eq_cons hdrop) hterm
            (hframe.setMany rvals) hoffCaller hsiteMem)
  | @callHalt fcur callee R st st' ods oas ofid oargs eb is t
      hfid hget hplen heb hbody ihbody =>
      have himem : Instr.call ods ofid oas ∈ cur.instrs := mem_of_drop_eq_cons hdrop
      have hcurSite : j = bi → cur = site := by
        intro hj; subst j; exact Option.some.inj (hcur.symm.trans hsite)
      by_cases hat : j = bi ∧ k = ci
      · obtain ⟨rfl, rfl⟩ := hat
        have hcureq := hcurSite rfl
        subst cur
        have heq := head_eq_of_drop_eq_cons hcall hdrop
        cases heq
        have hgEq : callee = g := Option.some.inj (hfid.symm.trans hfunc)
        subst callee
        rw [inlineCallerRest_site]
        have hoas : ∀ x ∈ as, x < off := by
          intro x hx
          exact lt_of_le_of_lt (instrUse_le_maxVal hsiteMem himem
            (by simpa [Instr.uses] using hx)) hoffCaller
        have hgetRi : Ri.getMany as = some oargs := by
          rw [← hframe.getMany hoas]
          exact hget
        have hentryParams : eb.params = [] := wfCheck_entry_params_nil hgwf (by
          simpa [hentry] using heb)
        refine Exec.jump (args := [])
          (tb := inlineReplayBlock ρ β contId eb) ?_ (by simp)
          (by simp [inlineReplayBlock, hentryParams]) ?_
        · have hbcopy := inlineReplayBlock_get hblocks heb
          simpa using hbcopy
        · have hreplay := inlineReplay_exec (g := g) (f' := f')
            (preBlocks := fcur.blocks.set! j callBlock)
            (cont := cont) (ps := g.params) (as := as) (ds := ds)
            (off := off) (ρ := ρ) (β := β) (contId := contId)
            (Rc := Regs.empty.setMany g.params oargs) (Rcaller := R)
            (cres := .halt st') (final := .halt st') (b := eb)
            hρ (fun i => by simpa using hβ i) (by simpa using hcontId) hblocks
            (by rw [hcont]) hnd rfl hlen hoas
            (fun {_} hb {_} ht => hret hb ht) hbody (block_mem_of_getElem? heb)
            ⟨[], rfl, rfl⟩ (renamedAgree_entry hpsnd hlen hgetRi) hframe
            (fun _ h => h)
            (fun Rout vals s heq _ => by cases heq)
          simpa [inlineReplayBlock, hentryParams, Regs.setMany_nil_left] using hreplay
      · have hne : j ≠ bi ∨ k ≠ ci := by omega
        have hoas : ∀ x ∈ oas, x < off := by
          intro x hx
          exact lt_of_le_of_lt (instrUse_le_maxVal (block_mem_of_getElem? hcur)
            himem (by simpa [Instr.uses] using hx)) hoffCaller
        rw [inlineCallerRest_cons_of_not_site hcurSite hne hdrop]
        exact Exec.callHalt (args := oargs) (g := callee) (eb := eb) hfid
          (by rw [← hframe.getMany hoas]; exact hget) hplen heb hbody
  | @jump fcur R st e tb vals res htb hget hplen htail ih =>
      have hbefore : ¬ (j = bi ∧ k ≤ ci) := by
        rintro ⟨rfl, hk⟩
        have hcureq : cur = site := Option.some.inj (hcur.symm.trans hsite)
        subst cur
        have hlenDrop := congrArg List.length hdrop
        simp at hlenDrop
        omega
      simp only [inlineCallerRest, if_neg hbefore]
      have htmem := block_mem_of_getElem? htb
      have hargs : ∀ x ∈ e.args, x < off := by
        intro x hx
        exact lt_of_le_of_lt (termUse_le_maxVal (block_mem_of_getElem? hcur)
          (by simpa [hterm, Term.uses] using hx)) hoffCaller
      by_cases he : e.target = bi
      · have htbSite : fcur.blocks[bi]? = some tb := by simpa [he] using htb
        have htbeq : tb = site := Option.some.inj (htbSite.symm.trans hsite)
        subst tb
        have htb' : f'.blocks[e.target]? = some callBlock := by
          rw [he]
          exact inlineCallerBlock_get_site₂ (f := fcur) (f' := f')
            (mid := g.blocks.map (inlineReplayBlock ρ β contId)) (tail := #[cont])
            (Array.getElem?_eq_some_iff.mp hsite).1 hblocks
        rw [hcallBlock] at htb'
        refine Exec.jump (e := e) (args := vals) htb'
          (by rw [← hframe.getMany hargs]; exact hget)
          (by simpa [hcallBlock] using hplen) ?_
        simpa [inlineCallerRest, hcallBlock] using
          (ih hsite hoff hβ hcontId hcallBlock hblocks
          (j := bi) (k := 0) (cur := site) hsite rfl rfl
          (hframe.setMany vals) hoffCaller hsiteMem)
      · have htb' := inlineCallerBlock_get_other₂ (f := fcur) (f' := f')
          (callBlock := callBlock) (mid :=
            g.blocks.map (inlineReplayBlock ρ β contId)) (tail := #[cont]) htb he hblocks
        refine Exec.jump (e := e) (args := vals) htb'
          (by rw [← hframe.getMany hargs]; exact hget) hplen ?_
        simpa [inlineCallerRest, he] using
          (ih hsite hoff hβ hcontId hcallBlock hblocks
          (j := e.target) (k := 0) (cur := tb) htb rfl rfl
          (hframe.setMany vals) hoffCaller hsiteMem)
  | @branchTrue fcur R st c v et ef tb vals res hc hv htb hget hplen htail ih =>
      have hbefore : ¬ (j = bi ∧ k ≤ ci) := by
        rintro ⟨rfl, hk⟩
        have hcureq : cur = site := Option.some.inj (hcur.symm.trans hsite)
        subst cur
        have hlenDrop := congrArg List.length hdrop
        simp at hlenDrop
        omega
      simp only [inlineCallerRest, if_neg hbefore]
      have hcLt : c < off := lt_of_le_of_lt
        (termUse_le_maxVal (block_mem_of_getElem? hcur) (by simp [hterm, Term.uses]))
        hoffCaller
      have hargs : ∀ x ∈ et.args, x < off := by
        intro x hx
        exact lt_of_le_of_lt (termUse_le_maxVal (block_mem_of_getElem? hcur)
          (by simp [hterm, Term.uses, hx])) hoffCaller
      by_cases he : et.target = bi
      · have htbSite : fcur.blocks[bi]? = some tb := by simpa [he] using htb
        have htbeq : tb = site := Option.some.inj (htbSite.symm.trans hsite)
        subst tb
        have htb' : f'.blocks[et.target]? = some callBlock := by
          rw [he]
          exact inlineCallerBlock_get_site₂ (f := fcur) (f' := f')
            (mid := g.blocks.map (inlineReplayBlock ρ β contId)) (tail := #[cont])
            (Array.getElem?_eq_some_iff.mp hsite).1 hblocks
        rw [hcallBlock] at htb'
        refine Exec.branchTrue (et := et) (ef := ef) (v := v) (args := vals)
          (by rw [hframe c hcLt]; exact hc) hv htb'
          (by rw [← hframe.getMany hargs]; exact hget)
          (by simpa [hcallBlock] using hplen) ?_
        simpa [inlineCallerRest, hcallBlock] using
          (ih hsite hoff hβ hcontId hcallBlock hblocks
          (j := bi) (k := 0) (cur := site) hsite rfl rfl
          (hframe.setMany vals) hoffCaller hsiteMem)
      · have htb' := inlineCallerBlock_get_other₂ (f := fcur) (f' := f')
          (callBlock := callBlock) (mid :=
            g.blocks.map (inlineReplayBlock ρ β contId)) (tail := #[cont]) htb he hblocks
        refine Exec.branchTrue (et := et) (ef := ef) (v := v) (args := vals)
          (by rw [hframe c hcLt]; exact hc) hv htb'
          (by rw [← hframe.getMany hargs]; exact hget) hplen ?_
        simpa [inlineCallerRest, he] using
          (ih hsite hoff hβ hcontId hcallBlock hblocks
          (j := et.target) (k := 0) (cur := tb) htb rfl rfl
          (hframe.setMany vals) hoffCaller hsiteMem)
  | @branchFalse fcur R st c et ef tb vals res hc htb hget hplen htail ih =>
      have hbefore : ¬ (j = bi ∧ k ≤ ci) := by
        rintro ⟨rfl, hk⟩
        have hcureq : cur = site := Option.some.inj (hcur.symm.trans hsite)
        subst cur
        have hlenDrop := congrArg List.length hdrop
        simp at hlenDrop
        omega
      simp only [inlineCallerRest, if_neg hbefore]
      have hcLt : c < off := lt_of_le_of_lt
        (termUse_le_maxVal (block_mem_of_getElem? hcur) (by simp [hterm, Term.uses]))
        hoffCaller
      have hargs : ∀ x ∈ ef.args, x < off := by
        intro x hx
        exact lt_of_le_of_lt (termUse_le_maxVal (block_mem_of_getElem? hcur)
          (by simp [hterm, Term.uses, hx])) hoffCaller
      by_cases he : ef.target = bi
      · have htbSite : fcur.blocks[bi]? = some tb := by simpa [he] using htb
        have htbeq : tb = site := Option.some.inj (htbSite.symm.trans hsite)
        subst tb
        have htb' : f'.blocks[ef.target]? = some callBlock := by
          rw [he]
          exact inlineCallerBlock_get_site₂ (f := fcur) (f' := f')
            (mid := g.blocks.map (inlineReplayBlock ρ β contId)) (tail := #[cont])
            (Array.getElem?_eq_some_iff.mp hsite).1 hblocks
        rw [hcallBlock] at htb'
        refine Exec.branchFalse (et := et) (ef := ef) (args := vals)
          (by rw [hframe c hcLt]; exact hc) htb'
          (by rw [← hframe.getMany hargs]; exact hget)
          (by simpa [hcallBlock] using hplen) ?_
        simpa [inlineCallerRest, hcallBlock] using
          (ih hsite hoff hβ hcontId hcallBlock hblocks
          (j := bi) (k := 0) (cur := site) hsite rfl rfl
          (hframe.setMany vals) hoffCaller hsiteMem)
      · have htb' := inlineCallerBlock_get_other₂ (f := fcur) (f' := f')
          (callBlock := callBlock) (mid :=
            g.blocks.map (inlineReplayBlock ρ β contId)) (tail := #[cont]) htb he hblocks
        refine Exec.branchFalse (et := et) (ef := ef) (args := vals)
          (by rw [hframe c hcLt]; exact hc) htb'
          (by rw [← hframe.getMany hargs]; exact hget) hplen ?_
        simpa [inlineCallerRest, he] using
          (ih hsite hoff hβ hcontId hcallBlock hblocks
          (j := ef.target) (k := 0) (cur := tb) htb rfl rfl
          (hframe.setMany vals) hoffCaller hsiteMem)
  | @ret fcur R st xs vals hget =>
      have hbefore : ¬ (j = bi ∧ k ≤ ci) := by
        rintro ⟨rfl, hk⟩
        have hcureq : cur = site := Option.some.inj (hcur.symm.trans hsite)
        subst cur
        have hlenDrop := congrArg List.length hdrop
        simp at hlenDrop
        omega
      simp only [inlineCallerRest, if_neg hbefore]
      have hxs : ∀ x ∈ xs, x < off := by
        intro x hx
        exact lt_of_le_of_lt (termUse_le_maxVal (block_mem_of_getElem? hcur)
          (by simpa [hterm, Term.uses] using hx)) hoffCaller
      exact Exec.ret (by rw [← hframe.getMany hxs]; exact hget)
  | @halt fcur R st st' yop oas oargs hget hop =>
      have hbefore : ¬ (j = bi ∧ k ≤ ci) := by
        rintro ⟨rfl, hk⟩
        have hcureq : cur = site := Option.some.inj (hcur.symm.trans hsite)
        subst cur
        have hlenDrop := congrArg List.length hdrop
        simp at hlenDrop
        omega
      simp only [inlineCallerRest, if_neg hbefore]
      have hoas : ∀ x ∈ oas, x < off := by
        intro x hx
        exact lt_of_le_of_lt (termUse_le_maxVal (block_mem_of_getElem? hcur)
          (by simpa [hterm, Term.uses] using hx)) hoffCaller
      exact Exec.halt (args := oargs) (by rw [← hframe.getMany hoas]; exact hget) hop

/-- The positional caller replay preserves the call-depth bound. -/
theorem Passes.inlineCaller_execN
    {P : Prog} {n : Nat} {f f' g : Func} {bi ci : Nat} {site : Block}
    {ds as : List ValId} {fid off contId : Nat}
    {ρ : ValId → ValId} {β : BlockId → BlockId} {cont callBlock : Block}
    {R Ri : Regs} {st : EvmState} {rest : Rest} {res : FRes}
    (hsite : f.blocks[bi]? = some site)
    (hci : ci < site.instrs.length)
    (hcall : site.instrs[ci]? = some (.call ds fid as))
    (hfunc : P.funcs[fid]? = some g)
    (hgwf : g.wfCheck P.funcs.size = true)
    (hoff : off = Nat.max (Passes.maxVal f) (Passes.maxVal g) + 1)
    (hρ : ρ = inlineRho g.params as off)
    (hβ : ∀ i, β i = f.blocks.size + i)
    (hcontId : contId = f.blocks.size + g.blocks.size)
    (hentry : g.entry = 0)
    (hlen : g.params.length = as.length)
    (hnrets : g.nrets = ds.length)
    (hcallBlock : callBlock =
      { params := site.params, instrs := site.instrs.take ci,
        term := .jump ⟨f.blocks.size + g.entry, []⟩ })
    (hcont : cont =
      { params := ds, instrs := site.instrs.drop (ci + 1), term := site.term })
    (hblocks : f'.blocks =
      (f.blocks.set! bi callBlock) ++
        g.blocks.map (inlineReplayBlock ρ β contId) ++ #[cont])
    (hexec : ExecN (model := model) P n f R st rest res)
    {j k : Nat} {cur : Block}
    (hcur : f.blocks[j]? = some cur)
    (hdrop : cur.instrs.drop k = rest.instrs)
    (hterm : cur.term = rest.term)
    (hframe : CallerFrame off R Ri) :
    ExecN (model := model) P n f' Ri st
      (inlineCallerRest bi ci (f.blocks.size + g.entry) j k site rest) res := by
  have hoffCaller : Passes.maxVal f < off := by
    rw [hoff]
    exact maxVal_lt_inlineOffset_left f g
  have hoffCallee : Passes.maxVal g < off := by
    rw [hoff]
    exact maxVal_lt_inlineOffset_right f g
  have hsiteMem := block_mem_of_getElem? hsite
  have hnd : g.allDefs.Nodup := by
    unfold Func.wfCheck at hgwf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hgwf
    exact hgwf.1.1.1
  have hpsnd : g.params.Nodup := by
    exact params_nodup_of_allDefs hnd rfl
  have hret : ∀ {b : Block}, b ∈ g.blocks.toList → ∀ {xs},
      b.term = .ret xs → xs.length = ds.length := by
    intro b hb xs ht
    rw [← hnrets]
    exact wfCheck_ret_arity hgwf hb ht
  induction hexec generalizing j k cur Ri with
  | @const n _ R st d v is t res htail ih =>
      have himem : Instr.const d v ∈ cur.instrs := mem_of_drop_eq_cons hdrop
      have hcurSite : j = bi → cur = site := by
        intro hj
        subst j
        exact Option.some.inj (hcur.symm.trans hsite)
      have hne : j ≠ bi ∨ k ≠ ci := by
        by_contra hn
        simp only [not_or, not_ne_iff] at hn
        obtain ⟨rfl, rfl⟩ := hn
        have hcureq := hcurSite rfl
        subst cur
        have heq := head_eq_of_drop_eq_cons hcall hdrop
        cases heq
      rw [inlineCallerRest_cons_of_not_site hcurSite hne hdrop]
      refine ExecN.const (ih hsite hoff hβ hcontId hcallBlock hblocks hcur
        (drop_succ_eq_of_drop_eq_cons hdrop) hterm ?_ hoffCaller hsiteMem)
      simpa [Regs.setMany_cons, Regs.setMany_nil_left] using
        (hframe.setMany (xs := [d]) [v])
  | @op n _ R st st' ods yop oas oargs rets is t res hget hop hlenRet htail ih =>
      have himem : Instr.op ods yop oas ∈ cur.instrs := mem_of_drop_eq_cons hdrop
      have hcurSite : j = bi → cur = site := by
        intro hj; subst j; exact Option.some.inj (hcur.symm.trans hsite)
      have hne : j ≠ bi ∨ k ≠ ci := by
        by_contra hn
        simp only [not_or, not_ne_iff] at hn
        obtain ⟨rfl, rfl⟩ := hn
        have hcureq := hcurSite rfl
        subst cur
        have heq := head_eq_of_drop_eq_cons hcall hdrop
        cases heq
      have hoas : ∀ x ∈ oas, x < off := by
        intro x hx
        exact lt_of_le_of_lt (instrUse_le_maxVal (block_mem_of_getElem? hcur)
          himem (by simpa [Instr.uses] using hx)) hoffCaller
      rw [inlineCallerRest_cons_of_not_site hcurSite hne hdrop]
      refine ExecN.op (args := oargs) (rets := rets)
        (by rw [← hframe.getMany hoas]; exact hget) hop hlenRet
        (ih hsite hoff hβ hcontId hcallBlock hblocks hcur
          (drop_succ_eq_of_drop_eq_cons hdrop) hterm ?_ hoffCaller hsiteMem)
      exact hframe.setMany rets
  | @opHalt n _ R st st' ods yop oas oargs is t hget hop =>
      have himem : Instr.op ods yop oas ∈ cur.instrs := mem_of_drop_eq_cons hdrop
      have hcurSite : j = bi → cur = site := by
        intro hj; subst j; exact Option.some.inj (hcur.symm.trans hsite)
      have hne : j ≠ bi ∨ k ≠ ci := by
        by_contra hn
        simp only [not_or, not_ne_iff] at hn
        obtain ⟨rfl, rfl⟩ := hn
        have hcureq := hcurSite rfl
        subst cur
        have heq := head_eq_of_drop_eq_cons hcall hdrop
        cases heq
      have hoas : ∀ x ∈ oas, x < off := by
        intro x hx
        exact lt_of_le_of_lt (instrUse_le_maxVal (block_mem_of_getElem? hcur)
          himem (by simpa [Instr.uses] using hx)) hoffCaller
      rw [inlineCallerRest_cons_of_not_site hcurSite hne hdrop]
      exact ExecN.opHalt (args := oargs) (by rw [← hframe.getMany hoas]; exact hget) hop
  | @call n fcur callee R st st' ods oas ofid oargs rvals eb is t res
      hfid hget hplen heb hbody hlenRet htail ihbody ih =>
      have himem : Instr.call ods ofid oas ∈ cur.instrs := mem_of_drop_eq_cons hdrop
      have hcurSite : j = bi → cur = site := by
        intro hj; subst j; exact Option.some.inj (hcur.symm.trans hsite)
      by_cases hat : j = bi ∧ k = ci
      · obtain ⟨rfl, rfl⟩ := hat
        have hcureq := hcurSite rfl
        subst cur
        have heq := head_eq_of_drop_eq_cons hcall hdrop
        cases heq
        have hgEq : callee = g := Option.some.inj (hfid.symm.trans hfunc)
        subst callee
        rw [inlineCallerRest_site]
        have hoas : ∀ x ∈ as, x < off := by
          intro x hx
          exact lt_of_le_of_lt (instrUse_le_maxVal hsiteMem himem
            (by simpa [Instr.uses] using hx)) hoffCaller
        have hgetRi : Ri.getMany as = some oargs := by
          rw [← hframe.getMany hoas]
          exact hget
        have hentryParams : eb.params = [] := wfCheck_entry_params_nil hgwf (by
          simpa [hentry] using heb)
        refine ExecN.jump (args := [])
          (tb := inlineReplayBlock ρ β contId eb) ?_ (by simp)
          (by simp [inlineReplayBlock, hentryParams]) ?_
        · have hbcopy := inlineReplayBlock_get hblocks heb
          simpa using hbcopy
        · have hreplay := inlineReplay_execN (g := g) (f' := f')
            (preBlocks := fcur.blocks.set! j callBlock)
            (cont := cont) (ps := g.params) (as := as) (ds := ds)
            (off := off) (ρ := ρ) (β := β) (contId := contId)
            (Rc := Regs.empty.setMany g.params oargs) (Rcaller := R)
            (cres := .ret rvals st') (final := res) (b := eb)
            hρ (fun i => by simpa using hβ i) (by simpa using hcontId) hblocks
            (by rw [hcont]) hnd rfl hlen hoas
            (fun {_} hb {_} ht => hret hb ht) hbody (block_mem_of_getElem? heb)
            ⟨[], rfl, rfl⟩ (renamedAgree_entry hpsnd hlen hgetRi) hframe
            (fun s hs => by cases hs)
            (fun Rout vals s heq hRout => by
              cases heq
              have htailDrop := drop_succ_eq_of_drop_eq_cons hdrop
              rw [hcont]
              simpa [inlineCallerRest, htailDrop, hterm] using
                (ih hsite hoff hβ hcontId hcallBlock hblocks
                (j := j) (k := k + 1) (cur := site) hsite
                (drop_succ_eq_of_drop_eq_cons hdrop) hterm
                (hRout.setMany rvals) hoffCaller hsiteMem))
          simpa [inlineReplayBlock, hentryParams, Regs.setMany_nil_left] using hreplay
      · have hne : j ≠ bi ∨ k ≠ ci := by omega
        have hoas : ∀ x ∈ oas, x < off := by
          intro x hx
          exact lt_of_le_of_lt (instrUse_le_maxVal (block_mem_of_getElem? hcur)
            himem (by simpa [Instr.uses] using hx)) hoffCaller
        rw [inlineCallerRest_cons_of_not_site hcurSite hne hdrop]
        refine ExecN.call (args := oargs) (rvals := rvals) (g := callee) (eb := eb)
          hfid (by rw [← hframe.getMany hoas]; exact hget) hplen heb hbody hlenRet
          (ih hsite hoff hβ hcontId hcallBlock hblocks hcur
            (drop_succ_eq_of_drop_eq_cons hdrop) hterm
            (hframe.setMany rvals) hoffCaller hsiteMem)
  | @callHalt n fcur callee R st st' ods oas ofid oargs eb is t
      hfid hget hplen heb hbody ihbody =>
      have himem : Instr.call ods ofid oas ∈ cur.instrs := mem_of_drop_eq_cons hdrop
      have hcurSite : j = bi → cur = site := by
        intro hj; subst j; exact Option.some.inj (hcur.symm.trans hsite)
      by_cases hat : j = bi ∧ k = ci
      · obtain ⟨rfl, rfl⟩ := hat
        have hcureq := hcurSite rfl
        subst cur
        have heq := head_eq_of_drop_eq_cons hcall hdrop
        cases heq
        have hgEq : callee = g := Option.some.inj (hfid.symm.trans hfunc)
        subst callee
        rw [inlineCallerRest_site]
        have hoas : ∀ x ∈ as, x < off := by
          intro x hx
          exact lt_of_le_of_lt (instrUse_le_maxVal hsiteMem himem
            (by simpa [Instr.uses] using hx)) hoffCaller
        have hgetRi : Ri.getMany as = some oargs := by
          rw [← hframe.getMany hoas]
          exact hget
        have hentryParams : eb.params = [] := wfCheck_entry_params_nil hgwf (by
          simpa [hentry] using heb)
        refine ExecN.jump (args := [])
          (tb := inlineReplayBlock ρ β contId eb) ?_ (by simp)
          (by simp [inlineReplayBlock, hentryParams]) ?_
        · have hbcopy := inlineReplayBlock_get hblocks heb
          simpa using hbcopy
        · have hreplay := inlineReplay_execN (g := g) (f' := f')
            (preBlocks := fcur.blocks.set! j callBlock)
            (cont := cont) (ps := g.params) (as := as) (ds := ds)
            (off := off) (ρ := ρ) (β := β) (contId := contId)
            (Rc := Regs.empty.setMany g.params oargs) (Rcaller := R)
            (cres := .halt st') (final := .halt st') (b := eb)
            hρ (fun i => by simpa using hβ i) (by simpa using hcontId) hblocks
            (by rw [hcont]) hnd rfl hlen hoas
            (fun {_} hb {_} ht => hret hb ht) hbody (block_mem_of_getElem? heb)
            ⟨[], rfl, rfl⟩ (renamedAgree_entry hpsnd hlen hgetRi) hframe
            (fun _ h => h)
            (fun Rout vals s heq _ => by cases heq)
          simpa [inlineReplayBlock, hentryParams, Regs.setMany_nil_left] using hreplay
      · have hne : j ≠ bi ∨ k ≠ ci := by omega
        have hoas : ∀ x ∈ oas, x < off := by
          intro x hx
          exact lt_of_le_of_lt (instrUse_le_maxVal (block_mem_of_getElem? hcur)
            himem (by simpa [Instr.uses] using hx)) hoffCaller
        rw [inlineCallerRest_cons_of_not_site hcurSite hne hdrop]
        exact ExecN.callHalt (args := oargs) (g := callee) (eb := eb) hfid
          (by rw [← hframe.getMany hoas]; exact hget) hplen heb hbody
  | @jump n fcur R st e tb vals res htb hget hplen htail ih =>
      have hbefore : ¬ (j = bi ∧ k ≤ ci) := by
        rintro ⟨rfl, hk⟩
        have hcureq : cur = site := Option.some.inj (hcur.symm.trans hsite)
        subst cur
        have hlenDrop := congrArg List.length hdrop
        simp at hlenDrop
        omega
      simp only [inlineCallerRest, if_neg hbefore]
      have htmem := block_mem_of_getElem? htb
      have hargs : ∀ x ∈ e.args, x < off := by
        intro x hx
        exact lt_of_le_of_lt (termUse_le_maxVal (block_mem_of_getElem? hcur)
          (by simpa [hterm, Term.uses] using hx)) hoffCaller
      by_cases he : e.target = bi
      · have htbSite : fcur.blocks[bi]? = some tb := by simpa [he] using htb
        have htbeq : tb = site := Option.some.inj (htbSite.symm.trans hsite)
        subst tb
        have htb' : f'.blocks[e.target]? = some callBlock := by
          rw [he]
          exact inlineCallerBlock_get_site₂ (f := fcur) (f' := f')
            (mid := g.blocks.map (inlineReplayBlock ρ β contId)) (tail := #[cont])
            (Array.getElem?_eq_some_iff.mp hsite).1 hblocks
        rw [hcallBlock] at htb'
        refine ExecN.jump (e := e) (args := vals) htb'
          (by rw [← hframe.getMany hargs]; exact hget)
          (by simpa [hcallBlock] using hplen) ?_
        simpa [inlineCallerRest, hcallBlock] using
          (ih hsite hoff hβ hcontId hcallBlock hblocks
          (j := bi) (k := 0) (cur := site) hsite rfl rfl
          (hframe.setMany vals) hoffCaller hsiteMem)
      · have htb' := inlineCallerBlock_get_other₂ (f := fcur) (f' := f')
          (callBlock := callBlock) (mid :=
            g.blocks.map (inlineReplayBlock ρ β contId)) (tail := #[cont]) htb he hblocks
        refine ExecN.jump (e := e) (args := vals) htb'
          (by rw [← hframe.getMany hargs]; exact hget) hplen ?_
        simpa [inlineCallerRest, he] using
          (ih hsite hoff hβ hcontId hcallBlock hblocks
          (j := e.target) (k := 0) (cur := tb) htb rfl rfl
          (hframe.setMany vals) hoffCaller hsiteMem)
  | @branchTrue n fcur R st c v et ef tb vals res hc hv htb hget hplen htail ih =>
      have hbefore : ¬ (j = bi ∧ k ≤ ci) := by
        rintro ⟨rfl, hk⟩
        have hcureq : cur = site := Option.some.inj (hcur.symm.trans hsite)
        subst cur
        have hlenDrop := congrArg List.length hdrop
        simp at hlenDrop
        omega
      simp only [inlineCallerRest, if_neg hbefore]
      have hcLt : c < off := lt_of_le_of_lt
        (termUse_le_maxVal (block_mem_of_getElem? hcur) (by simp [hterm, Term.uses]))
        hoffCaller
      have hargs : ∀ x ∈ et.args, x < off := by
        intro x hx
        exact lt_of_le_of_lt (termUse_le_maxVal (block_mem_of_getElem? hcur)
          (by simp [hterm, Term.uses, hx])) hoffCaller
      by_cases he : et.target = bi
      · have htbSite : fcur.blocks[bi]? = some tb := by simpa [he] using htb
        have htbeq : tb = site := Option.some.inj (htbSite.symm.trans hsite)
        subst tb
        have htb' : f'.blocks[et.target]? = some callBlock := by
          rw [he]
          exact inlineCallerBlock_get_site₂ (f := fcur) (f' := f')
            (mid := g.blocks.map (inlineReplayBlock ρ β contId)) (tail := #[cont])
            (Array.getElem?_eq_some_iff.mp hsite).1 hblocks
        rw [hcallBlock] at htb'
        refine ExecN.branchTrue (et := et) (ef := ef) (v := v) (args := vals)
          (by rw [hframe c hcLt]; exact hc) hv htb'
          (by rw [← hframe.getMany hargs]; exact hget)
          (by simpa [hcallBlock] using hplen) ?_
        simpa [inlineCallerRest, hcallBlock] using
          (ih hsite hoff hβ hcontId hcallBlock hblocks
          (j := bi) (k := 0) (cur := site) hsite rfl rfl
          (hframe.setMany vals) hoffCaller hsiteMem)
      · have htb' := inlineCallerBlock_get_other₂ (f := fcur) (f' := f')
          (callBlock := callBlock) (mid :=
            g.blocks.map (inlineReplayBlock ρ β contId)) (tail := #[cont]) htb he hblocks
        refine ExecN.branchTrue (et := et) (ef := ef) (v := v) (args := vals)
          (by rw [hframe c hcLt]; exact hc) hv htb'
          (by rw [← hframe.getMany hargs]; exact hget) hplen ?_
        simpa [inlineCallerRest, he] using
          (ih hsite hoff hβ hcontId hcallBlock hblocks
          (j := et.target) (k := 0) (cur := tb) htb rfl rfl
          (hframe.setMany vals) hoffCaller hsiteMem)
  | @branchFalse n fcur R st c et ef tb vals res hc htb hget hplen htail ih =>
      have hbefore : ¬ (j = bi ∧ k ≤ ci) := by
        rintro ⟨rfl, hk⟩
        have hcureq : cur = site := Option.some.inj (hcur.symm.trans hsite)
        subst cur
        have hlenDrop := congrArg List.length hdrop
        simp at hlenDrop
        omega
      simp only [inlineCallerRest, if_neg hbefore]
      have hcLt : c < off := lt_of_le_of_lt
        (termUse_le_maxVal (block_mem_of_getElem? hcur) (by simp [hterm, Term.uses]))
        hoffCaller
      have hargs : ∀ x ∈ ef.args, x < off := by
        intro x hx
        exact lt_of_le_of_lt (termUse_le_maxVal (block_mem_of_getElem? hcur)
          (by simp [hterm, Term.uses, hx])) hoffCaller
      by_cases he : ef.target = bi
      · have htbSite : fcur.blocks[bi]? = some tb := by simpa [he] using htb
        have htbeq : tb = site := Option.some.inj (htbSite.symm.trans hsite)
        subst tb
        have htb' : f'.blocks[ef.target]? = some callBlock := by
          rw [he]
          exact inlineCallerBlock_get_site₂ (f := fcur) (f' := f')
            (mid := g.blocks.map (inlineReplayBlock ρ β contId)) (tail := #[cont])
            (Array.getElem?_eq_some_iff.mp hsite).1 hblocks
        rw [hcallBlock] at htb'
        refine ExecN.branchFalse (et := et) (ef := ef) (args := vals)
          (by rw [hframe c hcLt]; exact hc) htb'
          (by rw [← hframe.getMany hargs]; exact hget)
          (by simpa [hcallBlock] using hplen) ?_
        simpa [inlineCallerRest, hcallBlock] using
          (ih hsite hoff hβ hcontId hcallBlock hblocks
          (j := bi) (k := 0) (cur := site) hsite rfl rfl
          (hframe.setMany vals) hoffCaller hsiteMem)
      · have htb' := inlineCallerBlock_get_other₂ (f := fcur) (f' := f')
          (callBlock := callBlock) (mid :=
            g.blocks.map (inlineReplayBlock ρ β contId)) (tail := #[cont]) htb he hblocks
        refine ExecN.branchFalse (et := et) (ef := ef) (args := vals)
          (by rw [hframe c hcLt]; exact hc) htb'
          (by rw [← hframe.getMany hargs]; exact hget) hplen ?_
        simpa [inlineCallerRest, he] using
          (ih hsite hoff hβ hcontId hcallBlock hblocks
          (j := ef.target) (k := 0) (cur := tb) htb rfl rfl
          (hframe.setMany vals) hoffCaller hsiteMem)
  | @ret n fcur R st xs vals hget =>
      have hbefore : ¬ (j = bi ∧ k ≤ ci) := by
        rintro ⟨rfl, hk⟩
        have hcureq : cur = site := Option.some.inj (hcur.symm.trans hsite)
        subst cur
        have hlenDrop := congrArg List.length hdrop
        simp at hlenDrop
        omega
      simp only [inlineCallerRest, if_neg hbefore]
      have hxs : ∀ x ∈ xs, x < off := by
        intro x hx
        exact lt_of_le_of_lt (termUse_le_maxVal (block_mem_of_getElem? hcur)
          (by simpa [hterm, Term.uses] using hx)) hoffCaller
      exact ExecN.ret (by rw [← hframe.getMany hxs]; exact hget)
  | @halt n fcur R st st' yop oas oargs hget hop =>
      have hbefore : ¬ (j = bi ∧ k ≤ ci) := by
        rintro ⟨rfl, hk⟩
        have hcureq : cur = site := Option.some.inj (hcur.symm.trans hsite)
        subst cur
        have hlenDrop := congrArg List.length hdrop
        simp at hlenDrop
        omega
      simp only [inlineCallerRest, if_neg hbefore]
      have hoas : ∀ x ∈ oas, x < off := by
        intro x hx
        exact lt_of_le_of_lt (termUse_le_maxVal (block_mem_of_getElem? hcur)
          (by simpa [hterm, Term.uses] using hx)) hoffCaller
      exact ExecN.halt (args := oargs) (by rw [← hframe.getMany hoas]; exact hget) hop


theorem inlineOnce_sound {P : Prog} {counts : Array Nat} {f f' : Func} {args : List U256}
    {st : EvmState} {res : FRes} {eb eb' : Block}
    (hPwf : P.wfCheck = true)
    (hio : Passes.inlineOnce counts P.funcs f = some f')
    (heb : f.blocks[f.entry]? = some eb)
    (heb' : f'.blocks[f'.entry]? = some eb')
    (hexec : Exec (model := model) P f (Regs.empty.setMany f.params args) st
      ⟨eb.instrs, eb.term⟩ res) :
    Exec (model := model) P f' (Regs.empty.setMany f'.params args) st
      ⟨eb'.instrs, eb'.term⟩ res := by
  obtain ⟨bi, site, ci, ds, fid, as, g, hbi, hsite, hci, hcall, hfunc,
    -, hlen, hnrets, hentry, hf'⟩ := Passes.inlineOnce_inv hio
  let off := Nat.max (Passes.maxVal f) (Passes.maxVal g) + 1
  let ρ : ValId → ValId := fun v =>
    match (g.params.zip as).find? (fun pa => pa.1 == v) with
    | some pa => pa.2
    | none => v + off
  let β := fun i : BlockId => f.blocks.size + i
  let contId := f.blocks.size + g.blocks.size
  let callBlock : Block :=
    { params := site.params, instrs := site.instrs.take ci,
      term := .jump ⟨f.blocks.size + g.entry, []⟩ }
  let cont : Block :=
    { params := ds, instrs := site.instrs.drop (ci + 1), term := site.term }
  have hreplayFn :
      (fun gb : Block =>
        { params := gb.params.map ρ
          instrs := gb.instrs.map (Passes.renameInstr ρ)
          term := match gb.term with
            | .ret vs => .jump ⟨contId, vs.map ρ⟩
            | t => Passes.renameTerm ρ β t }) =
        Passes.inlineReplayBlock ρ β contId := by
    funext gb
    cases gb with
    | mk params instrs term => cases term <;> rfl
  have hfshapeRaw : f' =
      { f with blocks := (f.blocks.set! bi callBlock) ++
        g.blocks.map (fun gb =>
          { params := gb.params.map ρ
            instrs := gb.instrs.map (Passes.renameInstr ρ)
            term := match gb.term with
              | .ret vs => .jump ⟨contId, vs.map ρ⟩
              | t => Passes.renameTerm ρ β t }) ++ #[cont] } := by
    simpa [off, ρ, β, contId, callBlock, cont] using hf'
  have hfshape : f' =
      { f with blocks := (f.blocks.set! bi callBlock) ++
        g.blocks.map (Passes.inlineReplayBlock ρ β contId) ++ #[cont] } := by
    rw [hfshapeRaw, hreplayFn]
  have hblocks : f'.blocks = (f.blocks.set! bi callBlock) ++
      g.blocks.map (Passes.inlineReplayBlock ρ β contId) ++ #[cont] := by
    rw [hfshape]
  have hparams : f'.params = f.params := by rw [hfshape]
  have hentry' : f'.entry = f.entry := by rw [hfshape]
  have hstart :
      Passes.inlineCallerRest bi ci (f.blocks.size + g.entry) f.entry 0 site
          ⟨eb.instrs, eb.term⟩ = ⟨eb'.instrs, eb'.term⟩ := by
    by_cases he : f.entry = bi
    · have hebsite : eb = site := by
        rw [he] at heb
        exact Option.some.inj (heb.symm.trans hsite)
      subst eb
      have heb'call : eb' = callBlock := by
        have hout : f'.blocks[f'.entry]? = some callBlock := by
          rw [hentry', he]
          exact Passes.inlineCallerBlock_get_site₂ (f := f) (f' := f')
            (mid := g.blocks.map (Passes.inlineReplayBlock ρ β contId))
            (tail := #[cont]) hbi hblocks
        exact Option.some.inj (heb'.symm.trans hout)
      subst eb'
      simp [Passes.inlineCallerRest, he, callBlock]
    · have hout : f'.blocks[f'.entry]? = some eb := by
        rw [hentry']
        exact Passes.inlineCallerBlock_get_other₂ (f := f) (f' := f')
          (callBlock := callBlock)
          (mid := g.blocks.map (Passes.inlineReplayBlock ρ β contId))
          (tail := #[cont]) heb he hblocks
      have hebeq : eb' = eb := Option.some.inj (heb'.symm.trans hout)
      subst eb'
      simp [Passes.inlineCallerRest, he]
  have hgwf := progWf_func hPwf hfunc
  have hsim := Passes.inlineCaller_exec (model := model)
    (f' := f') (bi := bi) (ci := ci) (site := site) (ds := ds) (as := as)
    (fid := fid) (off := off) (contId := contId) (ρ := ρ) (β := β)
    (cont := cont) (callBlock := callBlock)
    hsite hci hcall hfunc hgwf rfl rfl (fun _ => rfl) rfl hentry hlen hnrets
    rfl rfl hblocks hexec (j := f.entry) (k := 0) (cur := eb)
    heb rfl rfl (fun _ _ => rfl)
  rw [hstart] at hsim
  simpa [hparams] using hsim

/-- One splice preserves an existing call-depth bound. -/
theorem inlineOnce_soundN {P : Prog} {n : Nat} {counts : Array Nat} {f f' : Func} {args : List U256}
    {st : EvmState} {res : FRes} {eb eb' : Block}
    (hPwf : P.wfCheck = true)
    (hio : Passes.inlineOnce counts P.funcs f = some f')
    (heb : f.blocks[f.entry]? = some eb)
    (heb' : f'.blocks[f'.entry]? = some eb')
    (hexec : ExecN (model := model) P n f (Regs.empty.setMany f.params args) st
      ⟨eb.instrs, eb.term⟩ res) :
    ExecN (model := model) P n f' (Regs.empty.setMany f'.params args) st
      ⟨eb'.instrs, eb'.term⟩ res := by
  obtain ⟨bi, site, ci, ds, fid, as, g, hbi, hsite, hci, hcall, hfunc,
    -, hlen, hnrets, hentry, hf'⟩ := Passes.inlineOnce_inv hio
  let off := Nat.max (Passes.maxVal f) (Passes.maxVal g) + 1
  let ρ : ValId → ValId := fun v =>
    match (g.params.zip as).find? (fun pa => pa.1 == v) with
    | some pa => pa.2
    | none => v + off
  let β := fun i : BlockId => f.blocks.size + i
  let contId := f.blocks.size + g.blocks.size
  let callBlock : Block :=
    { params := site.params, instrs := site.instrs.take ci,
      term := .jump ⟨f.blocks.size + g.entry, []⟩ }
  let cont : Block :=
    { params := ds, instrs := site.instrs.drop (ci + 1), term := site.term }
  have hreplayFn :
      (fun gb : Block =>
        { params := gb.params.map ρ
          instrs := gb.instrs.map (Passes.renameInstr ρ)
          term := match gb.term with
            | .ret vs => .jump ⟨contId, vs.map ρ⟩
            | t => Passes.renameTerm ρ β t }) =
        Passes.inlineReplayBlock ρ β contId := by
    funext gb
    cases gb with
    | mk params instrs term => cases term <;> rfl
  have hfshapeRaw : f' =
      { f with blocks := (f.blocks.set! bi callBlock) ++
        g.blocks.map (fun gb =>
          { params := gb.params.map ρ
            instrs := gb.instrs.map (Passes.renameInstr ρ)
            term := match gb.term with
              | .ret vs => .jump ⟨contId, vs.map ρ⟩
              | t => Passes.renameTerm ρ β t }) ++ #[cont] } := by
    simpa [off, ρ, β, contId, callBlock, cont] using hf'
  have hfshape : f' =
      { f with blocks := (f.blocks.set! bi callBlock) ++
        g.blocks.map (Passes.inlineReplayBlock ρ β contId) ++ #[cont] } := by
    rw [hfshapeRaw, hreplayFn]
  have hblocks : f'.blocks = (f.blocks.set! bi callBlock) ++
      g.blocks.map (Passes.inlineReplayBlock ρ β contId) ++ #[cont] := by
    rw [hfshape]
  have hparams : f'.params = f.params := by rw [hfshape]
  have hentry' : f'.entry = f.entry := by rw [hfshape]
  have hstart :
      Passes.inlineCallerRest bi ci (f.blocks.size + g.entry) f.entry 0 site
          ⟨eb.instrs, eb.term⟩ = ⟨eb'.instrs, eb'.term⟩ := by
    by_cases he : f.entry = bi
    · have hebsite : eb = site := by
        rw [he] at heb
        exact Option.some.inj (heb.symm.trans hsite)
      subst eb
      have heb'call : eb' = callBlock := by
        have hout : f'.blocks[f'.entry]? = some callBlock := by
          rw [hentry', he]
          exact Passes.inlineCallerBlock_get_site₂ (f := f) (f' := f')
            (mid := g.blocks.map (Passes.inlineReplayBlock ρ β contId))
            (tail := #[cont]) hbi hblocks
        exact Option.some.inj (heb'.symm.trans hout)
      subst eb'
      simp [Passes.inlineCallerRest, he, callBlock]
    · have hout : f'.blocks[f'.entry]? = some eb := by
        rw [hentry']
        exact Passes.inlineCallerBlock_get_other₂ (f := f) (f' := f')
          (callBlock := callBlock)
          (mid := g.blocks.map (Passes.inlineReplayBlock ρ β contId))
          (tail := #[cont]) heb he hblocks
      have hebeq : eb' = eb := Option.some.inj (heb'.symm.trans hout)
      subst eb'
      simp [Passes.inlineCallerRest, he]
  have hgwf := progWf_func hPwf hfunc
  have hsim := Passes.inlineCaller_execN (model := model)
    (f' := f') (bi := bi) (ci := ci) (site := site) (ds := ds) (as := as)
    (fid := fid) (off := off) (contId := contId) (ρ := ρ) (β := β)
    (cont := cont) (callBlock := callBlock)
    hsite hci hcall hfunc hgwf rfl rfl (fun _ => rfl) rfl hentry hlen hnrets
    rfl rfl hblocks hexec (j := f.entry) (k := 0) (cur := eb)
    heb rfl rfl (fun _ _ => rfl)
  rw [hstart] at hsim
  simpa [hparams] using hsim

/-- Pure iteration model for `inlineFunc`.  Repeating an unsuccessful step is
the identity, so it is equivalent to the implementation's early return. -/
def Passes.inlineN (counts : Array Nat) (funcs : Array Func) : Nat → Func → Func
  | 0, f => f
  | n + 1, f =>
      match inlineOnce counts funcs f with
      | some f' => inlineN counts funcs n f'
      | none => f

def Passes.inlineFuncStep (counts : Array Nat) (funcs : Array Func)
    (_ : Nat) (f : Func) : ForInStep Func :=
  match inlineOnce counts funcs f with
  | some f' => .yield f'
  | none => .done f

def Passes.inlineFuncRawStep (counts : Array Nat) (funcs : Array Func)
    (_ : Nat) (s : MProd (Option Func) Func) : ForInStep (MProd (Option Func) Func) :=
  match inlineOnce counts funcs s.2 with
  | some f' => .yield ⟨none, f'⟩
  | none => .done ⟨some s.2, s.2⟩

theorem Passes.inlineFuncRaw_loop (counts : Array Nat) (funcs : Array Func)
    (l : List Nat) (f : Func) :
    let r := loopWith (inlineFuncRawStep counts funcs) l ⟨none, f⟩
    r.1.getD r.2 = loopWith (inlineFuncStep counts funcs) l f := by
  induction l generalizing f with
  | nil => rfl
  | cons i is ih =>
      rw [loopWith_cons, loopWith_cons]
      cases hio : inlineOnce counts funcs f with
      | none => simp [inlineFuncRawStep, inlineFuncStep, hio]
      | some f' =>
          simp only [inlineFuncRawStep, inlineFuncStep, hio]
          exact ih f'

theorem Passes.inlineFuncStep_loop (counts : Array Nat) (funcs : Array Func)
    (l : List Nat) (f : Func) :
    loopWith (inlineFuncStep counts funcs) l f = inlineN counts funcs l.length f := by
  induction l generalizing f with
  | nil => rfl
  | cons i is ih =>
      rw [loopWith_cons]
      cases hio : inlineOnce counts funcs f with
      | none => simp [inlineFuncStep, inlineN, hio]
      | some f' => simp [inlineFuncStep, inlineN, hio, ih]

theorem Passes.inlineFunc_eq_inlineN (counts : Array Nat) (funcs : Array Func) (f : Func) :
    inlineFunc counts funcs f = inlineN counts funcs 8 f := by
  unfold inlineFunc
  dsimp only
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rw [Id.forIn_eq_loopWith (g := inlineFuncRawStep counts funcs) (h := by
    intro i s
    cases hio : inlineOnce counts funcs s.2 <;>
      simp [inlineFuncRawStep, hio])]
  simp only [Id.run, bind, pure]
  let l := List.range' 0 ((8 - 0 + 1 - 1) / 1) 1
  let r := loopWith (inlineFuncRawStep counts funcs) l ⟨none, f⟩
  change (match r.1 with | none => r.2 | some a => a) = _
  have hm : (match r.1 with | none => r.2 | some a => a) = r.1.getD r.2 := by
    cases r.1 <;> rfl
  rw [hm]
  have hr := inlineFuncRaw_loop counts funcs l f
  change r.1.getD r.2 = _ at hr
  rw [hr, inlineFuncStep_loop]
  rfl

theorem Passes.inlineN_nrets (counts : Array Nat) (funcs : Array Func)
    (n : Nat) (f : Func) :
    (inlineN counts funcs n f).nrets = f.nrets := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
      cases hio : inlineOnce counts funcs f with
      | none => simp [inlineN, hio]
      | some f' =>
          simpa [inlineN, hio, inlineOnce_nrets hio] using ih f'

theorem Passes.inlineN_wf (counts : Array Nat) (funcs : Array Func)
    {nFuncs : Nat}
    (hfuncs : ∀ {fid : FuncId} {g : Func},
      funcs[fid]? = some g → g.wfCheck nFuncs = true) :
    ∀ (n : Nat) (f : Func), f.wfCheck nFuncs = true →
      (inlineN counts funcs n f).wfCheck nFuncs = true := by
  intro n
  induction n with
  | zero => intro f hfwf; exact hfwf
  | succ n ih =>
      intro f hfwf
      cases hio : inlineOnce counts funcs f with
      | none => simpa [inlineN, hio] using hfwf
      | some f' =>
          simpa [inlineN, hio] using ih f' (inlineOnce_wf hfuncs hfwf hio)

theorem Passes.inlineFunc_wf (counts : Array Nat) (funcs : Array Func)
    {f : Func} {nFuncs : Nat}
    (hfuncs : ∀ {fid : FuncId} {g : Func},
      funcs[fid]? = some g → g.wfCheck nFuncs = true)
    (hfwf : f.wfCheck nFuncs = true) :
    (inlineFunc counts funcs f).wfCheck nFuncs = true := by
  rw [inlineFunc_eq_inlineN]
  exact inlineN_wf counts funcs hfuncs 8 f hfwf

theorem Passes.inlineFunc_nrets (counts : Array Nat) (funcs : Array Func)
    (f : Func) : (inlineFunc counts funcs f).nrets = f.nrets := by
  rw [inlineFunc_eq_inlineN]
  exact inlineN_nrets counts funcs 8 f

/-- A successful splice preserves the existence of the caller entry block. -/
theorem Passes.inlineOnce_entry {counts : Array Nat} {funcs : Array Func}
    {f f' : Func} {eb : Block} (hio : inlineOnce counts funcs f = some f')
    (heb : f.blocks[f.entry]? = some eb) :
    ∃ eb', f'.blocks[f'.entry]? = some eb' := by
  obtain ⟨bi, site, ci, ds, fid, as, g, hbi, hsite, hci, hcall, hfunc,
    hcount, hlen, hnrets, hentry, hf'⟩ := inlineOnce_inv hio
  have hlt : f.entry < f.blocks.size := (Array.getElem?_eq_some_iff.mp heb).1
  have hsetSize :
      (f.blocks.set! bi
        { params := site.params, instrs := site.instrs.take ci,
          term := .jump ⟨f.blocks.size + g.entry, []⟩ }).size = f.blocks.size := by
    simp
  have hentryEq : f'.entry = f.entry := by rw [hf']
  have hlt' : f'.entry < f'.blocks.size := by
    rw [hentryEq]
    apply lt_of_lt_of_le hlt
    rw [hf']
    apply le_trans (le_of_eq hsetSize.symm)
    simp
  refine ⟨f'.blocks[f'.entry], ?_⟩
  exact Array.getElem?_eq_getElem hlt'

theorem Passes.inlineOnce_params_entry {counts : Array Nat} {funcs : Array Func}
    {f f' : Func} (hio : inlineOnce counts funcs f = some f') :
    f'.params = f.params ∧ f'.entry = f.entry := by
  obtain ⟨bi, site, ci, ds, fid, as, g, hbi, hsite, hci, hcall, hfunc,
    hcount, hlen, hnrets, hentry, hf'⟩ := inlineOnce_inv hio
  rw [hf']
  exact ⟨rfl, rfl⟩

theorem Passes.inlineN_params_entry (counts : Array Nat) (funcs : Array Func)
    (n : Nat) (f : Func) :
    (inlineN counts funcs n f).params = f.params ∧
      (inlineN counts funcs n f).entry = f.entry := by
  induction n generalizing f with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
      cases hio : inlineOnce counts funcs f with
      | none => simp [inlineN, hio]
      | some f' =>
          have hs := inlineOnce_params_entry hio
          have hi := ih f'
          simpa [inlineN, hio, hs.1, hs.2] using hi

theorem Passes.inlineN_sound {P : Prog} {counts : Array Nat}
    (hPwf : P.wfCheck = true) :
    ∀ (n : Nat) (f : Func) (args : List U256) (st : EvmState) (res : FRes)
      (eb eb' : Block),
      f.blocks[f.entry]? = some eb →
      (inlineN counts P.funcs n f).blocks[(inlineN counts P.funcs n f).entry]? = some eb' →
      Exec (model := model) P f (Regs.empty.setMany f.params args) st
        ⟨eb.instrs, eb.term⟩ res →
      Exec (model := model) P (inlineN counts P.funcs n f)
        (Regs.empty.setMany (inlineN counts P.funcs n f).params args) st
        ⟨eb'.instrs, eb'.term⟩ res := by
  intro n
  induction n with
  | zero =>
      intro f args st res eb eb' heb heb' hexec
      simp only [inlineN] at heb' ⊢
      have heq : eb' = eb := Option.some.inj (heb'.symm.trans heb)
      subst eb'
      exact hexec
  | succ n ih =>
      intro f args st res eb eb' heb heb' hexec
      cases hio : inlineOnce counts P.funcs f with
      | none =>
          simp only [inlineN, hio, Option.getD_none] at heb' ⊢
          have heq : eb' = eb := Option.some.inj (heb'.symm.trans heb)
          subst eb'
          exact hexec
      | some f' =>
          obtain ⟨e', he'⟩ := inlineOnce_entry hio heb
          have hexec' := inlineOnce_sound (model := model) hPwf hio heb he' hexec
          have heb'' :
              (inlineN counts P.funcs n f').blocks[
                (inlineN counts P.funcs n f').entry]? = some eb' := by
            simpa only [inlineN, hio, Option.getD_some] using heb'
          simpa only [inlineN, hio] using
            (ih f' args st res e' eb' he' heb'' hexec')

/-- Iterated local inlining preserves the same call-depth bound. -/
theorem Passes.inlineN_soundN {P : Prog} {depth : Nat} {counts : Array Nat}
    (hPwf : P.wfCheck = true) :
    ∀ (n : Nat) (f : Func) (args : List U256) (st : EvmState) (res : FRes)
      (eb eb' : Block),
      f.blocks[f.entry]? = some eb →
      (inlineN counts P.funcs n f).blocks[(inlineN counts P.funcs n f).entry]? = some eb' →
      ExecN (model := model) P depth f (Regs.empty.setMany f.params args) st
        ⟨eb.instrs, eb.term⟩ res →
      ExecN (model := model) P depth (inlineN counts P.funcs n f)
        (Regs.empty.setMany (inlineN counts P.funcs n f).params args) st
        ⟨eb'.instrs, eb'.term⟩ res := by
  intro n
  induction n with
  | zero =>
      intro f args st res eb eb' heb heb' hexec
      simp only [inlineN] at heb' ⊢
      have heq : eb' = eb := Option.some.inj (heb'.symm.trans heb)
      subst eb'
      exact hexec
  | succ n ih =>
      intro f args st res eb eb' heb heb' hexec
      cases hio : inlineOnce counts P.funcs f with
      | none =>
          simp only [inlineN, hio, Option.getD_none] at heb' ⊢
          have heq : eb' = eb := Option.some.inj (heb'.symm.trans heb)
          subst eb'
          exact hexec
      | some f' =>
          obtain ⟨e', he'⟩ := inlineOnce_entry hio heb
          have hexec' := inlineOnce_soundN (model := model) hPwf hio heb he' hexec
          have heb'' :
              (inlineN counts P.funcs n f').blocks[
                (inlineN counts P.funcs n f').entry]? = some eb' := by
            simpa only [inlineN, hio, Option.getD_some] using heb'
          simpa only [inlineN, hio] using
            (ih f' args st res e' eb' he' heb'' hexec')

/-- **The budgeted fixed point preserves executions**: iterate
`inlineOnce_sound` at most eight times. -/
theorem inlineFunc_sound {P : Prog} {counts : Array Nat} {f : Func} {args : List U256}
    {st : EvmState} {res : FRes} {eb eb' : Block}
    (hPwf : P.wfCheck = true) (_hwf : f.wfCheck P.funcs.size = true)
    (heb : f.blocks[f.entry]? = some eb)
    (heb' : (Passes.inlineFunc counts P.funcs f).blocks[f.entry]? = some eb')
    (hexec : Exec (model := model) P f (Regs.empty.setMany f.params args) st
      ⟨eb.instrs, eb.term⟩ res) :
    Exec (model := model) P (Passes.inlineFunc counts P.funcs f)
      (Regs.empty.setMany f.params args) st ⟨eb'.instrs, eb'.term⟩ res := by
  have hpe := Passes.inlineN_params_entry counts P.funcs 8 f
  have heb'' :
      (Passes.inlineN counts P.funcs 8 f).blocks[
        (Passes.inlineN counts P.funcs 8 f).entry]? = some eb' := by
    rw [hpe.2]
    simpa only [Passes.inlineFunc_eq_inlineN] using heb'
  have hs := Passes.inlineN_sound (model := model) (counts := counts) hPwf
    8 f args st res eb eb' heb heb'' hexec
  simpa only [Passes.inlineFunc_eq_inlineN, hpe.1] using hs

/-- The production local inliner preserves the same call-depth bound. -/
theorem inlineFunc_soundN {P : Prog} {depth : Nat} {counts : Array Nat} {f : Func} {args : List U256}
    {st : EvmState} {res : FRes} {eb eb' : Block}
    (hPwf : P.wfCheck = true) (_hwf : f.wfCheck P.funcs.size = true)
    (heb : f.blocks[f.entry]? = some eb)
    (heb' : (Passes.inlineFunc counts P.funcs f).blocks[f.entry]? = some eb')
    (hexec : ExecN (model := model) P depth f (Regs.empty.setMany f.params args) st
      ⟨eb.instrs, eb.term⟩ res) :
    ExecN (model := model) P depth (Passes.inlineFunc counts P.funcs f)
      (Regs.empty.setMany f.params args) st ⟨eb'.instrs, eb'.term⟩ res := by
  have hpe := Passes.inlineN_params_entry counts P.funcs 8 f
  have heb'' :
      (Passes.inlineN counts P.funcs 8 f).blocks[
        (Passes.inlineN counts P.funcs 8 f).entry]? = some eb' := by
    rw [hpe.2]
    simpa only [Passes.inlineFunc_eq_inlineN] using heb'
  have hs := Passes.inlineN_soundN (model := model) (counts := counts) hPwf
    8 f args st res eb eb' heb heb'' hexec
  simpa only [Passes.inlineFunc_eq_inlineN, hpe.1] using hs

/-- The unpruned program produced by one inlining round. -/
def Passes.inlineMap (counts : Array Nat) (P : Prog) : Prog :=
  { main := inlineFunc counts P.funcs P.main
    funcs := P.funcs.map (inlineFunc counts P.funcs) }

theorem Passes.inlineMap_lookup {counts : Array Nat} {P : Prog}
    {fid : FuncId} {g : Func} (h : P.funcs[fid]? = some g) :
    (inlineMap counts P).funcs[fid]? = some (inlineFunc counts P.funcs g) := by
  simp [inlineMap, h]

theorem Passes.inlineMap_wf {counts : Array Nat} {P : Prog}
    (hPwf : P.wfCheck = true) : (inlineMap counts P).wfCheck = true := by
  have hparts := hPwf
  simp only [Prog.wfCheck, Bool.and_eq_true] at hparts ⊢
  have hcallees : ∀ {fid : FuncId} {g : Func},
      P.funcs[fid]? = some g → g.wfCheck P.funcs.size = true := by
    intro fid g hget
    exact progWf_func hPwf hget
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · have hp := inlineN_params_entry counts P.funcs 8 P.main
    simpa [inlineMap, inlineFunc_eq_inlineN, hp.1] using hparts.1.1.1
  · simpa [inlineMap, inlineFunc_nrets] using hparts.1.1.2
  · simpa [inlineMap] using
      (inlineFunc_wf counts P.funcs hcallees hparts.1.2)
  · rw [Array.all_eq_true]
    intro i hi
    have hi' : i < P.funcs.size := by simpa [inlineMap] using hi
    have hfi : P.funcs[i].wfCheck P.funcs.size = true := by
      rw [Array.all_eq_true] at hparts
      exact hparts.2 i hi'
    simpa [inlineMap] using inlineFunc_wf counts P.funcs hcallees hfi

/-- Iteration preserves existence of a function's entry block. -/
theorem Passes.inlineN_entry {counts : Array Nat} {funcs : Array Func} :
    ∀ (k : Nat) (f : Func) {eb : Block}, f.blocks[f.entry]? = some eb →
      ∃ eb', (inlineN counts funcs k f).blocks[(inlineN counts funcs k f).entry]? =
        some eb' := by
  intro k
  induction k with
  | zero =>
      intro f eb heb
      exact ⟨eb, heb⟩
  | succ k ih =>
      intro f eb heb
      cases hio : inlineOnce counts funcs f with
      | none =>
          exact ⟨eb, by simpa [inlineN, hio] using heb⟩
      | some f' =>
          obtain ⟨eb', heb'⟩ := inlineOnce_entry hio heb
          simpa [inlineN, hio] using ih f' heb'

theorem Passes.inlineFunc_entry {counts : Array Nat} {funcs : Array Func}
    {f : Func} {eb : Block} (heb : f.blocks[f.entry]? = some eb) :
    ∃ eb', (inlineFunc counts funcs f).blocks[(inlineFunc counts funcs f).entry]? =
      some eb' := by
  rw [inlineFunc_eq_inlineN]
  exact inlineN_entry 8 f heb

/-- Change the ambient program from `P` to its one-round function map while
leaving the currently executing function text fixed.  At a call, the callee
is first locally inlined under `P`; the outer strong induction then changes
the ambient program for that new callee at the strictly smaller body bound.
The caller continuation is handled by the structural induction hypothesis. -/
theorem Passes.inlineMap_execN {P : Prog} {counts : Array Nat}
    (hPwf : P.wfCheck = true) :
    ∀ (n : Nat) (f : Func) (R : Regs) (st : EvmState) (rest : Rest) (res : FRes),
      ExecN (model := model) P n f R st rest res →
      ExecN (model := model) (inlineMap counts P) n f R st rest res := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n hdepth =>
      intro f R st rest res hexec
      induction hexec with
      | const htail ih => exact ExecN.const (ih hdepth)
      | op hget hop hlen htail ih => exact ExecN.op hget hop hlen (ih hdepth)
      | opHalt hget hop => exact ExecN.opHalt hget hop
      | @call k f g R st st' ds as fid args rvals eb is t res
          hfid hget hplen heb hbody hlen htail ihbody ih =>
          obtain ⟨eb', heb'⟩ := inlineFunc_entry
            (counts := counts) (funcs := P.funcs) heb
          have hpe := inlineN_params_entry counts P.funcs 8 g
          have heb'' : (inlineFunc counts P.funcs g).blocks[g.entry]? = some eb' := by
            simpa only [inlineFunc_eq_inlineN, hpe.2] using heb'
          have hbodyLocal := inlineFunc_soundN (model := model)
            (depth := k) (counts := counts) hPwf (progWf_func hPwf hfid)
            heb heb'' hbody
          have hbodyLocal' : ExecN (model := model) P k
              (inlineFunc counts P.funcs g)
              (Regs.empty.setMany (inlineFunc counts P.funcs g).params args)
              st ⟨eb'.instrs, eb'.term⟩ (.ret rvals st') := by
            simpa only [inlineFunc_eq_inlineN, hpe.1] using hbodyLocal
          have hbodyMap := hdepth k (by omega)
            (inlineFunc counts P.funcs g)
            (Regs.empty.setMany (inlineFunc counts P.funcs g).params args)
            st ⟨eb'.instrs, eb'.term⟩ (.ret rvals st') hbodyLocal'
          refine ExecN.call (g := inlineFunc counts P.funcs g) (eb := eb')
            (inlineMap_lookup hfid) hget ?_ heb' hbodyMap hlen (ih hdepth)
          simpa only [inlineFunc_eq_inlineN, hpe.1] using hplen
      | @callHalt k f g R st st' ds as fid args eb is t
          hfid hget hplen heb hbody ihbody =>
          obtain ⟨eb', heb'⟩ := inlineFunc_entry
            (counts := counts) (funcs := P.funcs) heb
          have hpe := inlineN_params_entry counts P.funcs 8 g
          have heb'' : (inlineFunc counts P.funcs g).blocks[g.entry]? = some eb' := by
            simpa only [inlineFunc_eq_inlineN, hpe.2] using heb'
          have hbodyLocal := inlineFunc_soundN (model := model)
            (depth := k) (counts := counts) hPwf (progWf_func hPwf hfid)
            heb heb'' hbody
          have hbodyLocal' : ExecN (model := model) P k
              (inlineFunc counts P.funcs g)
              (Regs.empty.setMany (inlineFunc counts P.funcs g).params args)
              st ⟨eb'.instrs, eb'.term⟩ (.halt st') := by
            simpa only [inlineFunc_eq_inlineN, hpe.1] using hbodyLocal
          have hbodyMap := hdepth k (by omega)
            (inlineFunc counts P.funcs g)
            (Regs.empty.setMany (inlineFunc counts P.funcs g).params args)
            st ⟨eb'.instrs, eb'.term⟩ (.halt st') hbodyLocal'
          refine ExecN.callHalt (g := inlineFunc counts P.funcs g) (eb := eb')
            (inlineMap_lookup hfid) hget ?_ heb' hbodyMap
          simpa only [inlineFunc_eq_inlineN, hpe.1] using hplen
      | jump htb hget hplen htail ih => exact ExecN.jump htb hget hplen (ih hdepth)
      | branchTrue hc hv htb hget hplen htail ih =>
          exact ExecN.branchTrue hc hv htb hget hplen (ih hdepth)
      | branchFalse hc htb hget hplen htail ih =>
          exact ExecN.branchFalse hc htb hget hplen (ih hdepth)
      | ret hget => exact ExecN.ret hget
      | halt hget hop => exact ExecN.halt hget hop

/-- One unpruned whole-program inlining map preserves a run. -/
theorem Passes.inlineMap_sound {P : Prog} {counts : Array Nat}
    {yst0 yst' : EvmState} {o : Outcome} (hPwf : P.wfCheck = true)
    (hrun : Run (model := model) P yst0 yst' o) :
    Run (model := model) (inlineMap counts P) yst0 yst' o := by
  have hPwf' := hPwf
  simp only [Prog.wfCheck, Bool.and_eq_true] at hPwf'
  have hmainWf : P.main.wfCheck P.funcs.size = true := by
    exact hPwf'.1.2
  have hmainParams : P.main.params = [] := by
    exact List.isEmpty_iff.mp hPwf'.1.1.1
  cases hrun with
  | normal heb hexec =>
      rename_i eb
      obtain ⟨n, hexecN⟩ := hexec.toExecN
      obtain ⟨eb', heb'⟩ := inlineFunc_entry
        (counts := counts) (funcs := P.funcs) heb
      have hpe := inlineN_params_entry counts P.funcs 8 P.main
      have heb'' : (inlineFunc counts P.funcs P.main).blocks[P.main.entry]? =
          some eb' := by
        simpa only [inlineFunc_eq_inlineN, hpe.2] using heb'
      have hlocal := inlineFunc_soundN (model := model) (depth := n)
        (counts := counts) (args := []) hPwf hmainWf heb heb''
        (by simpa [hmainParams, Regs.setMany_nil_left] using hexecN)
      have hlocal' : ExecN (model := model) P n
          (inlineFunc counts P.funcs P.main) Regs.empty yst0
          ⟨eb'.instrs, eb'.term⟩ (.ret [] yst') := by
        simpa only [inlineFunc_eq_inlineN, hpe.1, hmainParams,
          Regs.setMany_nil_left] using hlocal
      have hmapped := inlineMap_execN (model := model) (counts := counts)
        hPwf n (inlineFunc counts P.funcs P.main) Regs.empty yst0
        ⟨eb'.instrs, eb'.term⟩ (.ret [] yst') hlocal'
      exact Run.normal (by simpa [inlineMap] using heb') hmapped.toExec
  | halt heb hexec =>
      rename_i eb
      obtain ⟨n, hexecN⟩ := hexec.toExecN
      obtain ⟨eb', heb'⟩ := inlineFunc_entry
        (counts := counts) (funcs := P.funcs) heb
      have hpe := inlineN_params_entry counts P.funcs 8 P.main
      have heb'' : (inlineFunc counts P.funcs P.main).blocks[P.main.entry]? =
          some eb' := by
        simpa only [inlineFunc_eq_inlineN, hpe.2] using heb'
      have hlocal := inlineFunc_soundN (model := model) (depth := n)
        (counts := counts) (args := []) hPwf hmainWf heb heb''
        (by simpa [hmainParams, Regs.setMany_nil_left] using hexecN)
      have hlocal' : ExecN (model := model) P n
          (inlineFunc counts P.funcs P.main) Regs.empty yst0
          ⟨eb'.instrs, eb'.term⟩ (.halt yst') := by
        simpa only [inlineFunc_eq_inlineN, hpe.1, hmainParams,
          Regs.setMany_nil_left] using hlocal
      have hmapped := inlineMap_execN (model := model) (counts := counts)
        hPwf n (inlineFunc counts P.funcs P.main) Regs.empty yst0
        ⟨eb'.instrs, eb'.term⟩ (.halt yst') hlocal'
      exact Run.halt (by simpa [inlineMap] using heb') hmapped.toExec

/-! ### Function pruning: pure models of the mutable loops -/

def Passes.pruneCallees (f : Func) : List FuncId :=
  f.blocks.toList.flatMap fun b =>
    b.instrs.filterMap fun i => match i with | .call _ fid _ => some fid | _ => none

def Passes.pruneWorkOne (P : Prog) (n : Nat) (fid : FuncId)
    (s : MProd (List FuncId) (Array Bool)) : MProd (List FuncId) (Array Bool) :=
  if h : fid < n then
    if !s.2[fid]! then
      ⟨s.1 ++ (P.funcs[fid]?.map pruneCallees).getD [], s.2.set! fid true⟩
    else s
  else s

def Passes.pruneRound (P : Prog) (n : Nat) (_ : Nat)
    (s : MProd (Array Bool) (List FuncId)) : ForInStep (MProd (Array Bool) (List FuncId)) :=
  let r := s.2.foldl (fun r fid => pruneWorkOne P n fid r) ⟨[], s.1⟩
  let out := ⟨r.2, r.1⟩
  if r.1.isEmpty then .done out else .yield out

def Passes.pruneState (P : Prog) : MProd (Array Bool) (List FuncId) :=
  loopWith (pruneRound P P.funcs.size)
    (List.range' 0 (P.funcs.size + 1) 1)
    ⟨Array.replicate P.funcs.size false,
      P.main.blocks.toList.flatMap fun b =>
        b.instrs.filterMap fun i =>
          match i with | .call _ fid _ => some fid | _ => none⟩

def Passes.pruneKeepOne (P : Prog) (used : Array Bool) (fid : FuncId)
    (s : MProd (Array Func) (Array (Option FuncId))) :
    MProd (Array Func) (Array (Option FuncId)) :=
  if used[fid]! then
    ⟨s.1.push P.funcs[fid]!, s.2.set! fid (some s.1.size)⟩
  else s

def Passes.pruneKeep (P : Prog) (used : Array Bool) :
    MProd (Array Func) (Array (Option FuncId)) :=
  (List.range' 0 P.funcs.size 1).foldl
    (fun s fid => pruneKeepOne P used fid s)
    ⟨#[], Array.replicate P.funcs.size none⟩

def Passes.pruneInstr (remap : Array (Option FuncId)) : Instr → Instr
  | .call ds fid as => .call ds ((remap[fid]?.join).getD fid) as
  | i => i

def Passes.pruneBlock (remap : Array (Option FuncId)) (b : Block) : Block :=
  { b with instrs := b.instrs.map (pruneInstr remap) }

def Passes.pruneFix (remap : Array (Option FuncId)) (f : Func) : Func :=
  { f with blocks := f.blocks.map (pruneBlock remap) }

def Passes.pruneModel (P : Prog) : Prog :=
  let used := (pruneState P).1
  if used.all id then P
  else
    let kept := (pruneKeep P used).1
    let remap := (pruneKeep P used).2
    { main := pruneFix remap P.main, funcs := kept.map (pruneFix remap) }

theorem Passes.pruneFuncs_eq_model (P : Prog) : pruneFuncs P = pruneModel P := by
  unfold pruneFuncs pruneModel pruneState
  dsimp only
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rw [Id.forIn_eq_loopWith (g := pruneRound P P.funcs.size) (h := by
    intro i s
    rw [Id.forIn_eq_foldl (g := pruneWorkOne P P.funcs.size) (h := by
      intro fid r
      simp only [pruneWorkOne]
      split <;> rename_i hlt
      · split <;> rfl
      · rfl)]
    simp only [pruneRound]
    rfl)]
  simp only [Id.run, bind, pure]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [Id.forIn_eq_foldl (g := pruneKeepOne P (pruneState P).1) (h := by
    intro fid r
    simp only [pruneState, pruneKeepOne]
    split <;> rename_i hc
    · change ForInStep.yield _ = ForInStep.yield _
      congr 1
      exact (if_pos hc).symm
    · change ForInStep.yield _ = ForInStep.yield _
      congr 1
      exact (if_neg hc).symm)]
  rfl

theorem Passes.mem_pruneCallees {f : Func} {fid : FuncId} :
    fid ∈ pruneCallees f ↔
      ∃ b ∈ f.blocks.toList, ∃ ds as, Instr.call ds fid as ∈ b.instrs := by
  simp only [pruneCallees, List.mem_flatMap, List.mem_filterMap]
  constructor
  · rintro ⟨b, hb, i, hi, hcall⟩
    cases i with
    | const => simp at hcall
    | op => simp at hcall
    | call ds fid' as =>
        simp only at hcall
        obtain rfl := Option.some.inj hcall
        exact ⟨b, hb, ds, as, hi⟩
  · rintro ⟨b, hb, ds, as, hi⟩
    exact ⟨b, hb, .call ds fid as, hi, rfl⟩

theorem Passes.wfCheck_callee_lt {f : Func} {n fid : Nat}
    (hwf : f.wfCheck n = true) (hfid : fid ∈ pruneCallees f) : fid < n := by
  obtain ⟨b, hb, ds, as, hi⟩ := mem_pruneCallees.mp hfid
  unfold Func.wfCheck at hwf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hwf
  have hblock := Array.all_eq_true_iff_forall_mem.mp hwf.2 b (by simpa using hb)
  simp only [Bool.and_eq_true] at hblock
  have hins := List.all_eq_true.mp hblock.2 (.call ds fid as) hi
  simpa using hins

def Passes.MarkSub (A B : Array Bool) : Prop :=
  ∀ (i : Nat), A[i]? = some true → B[i]? = some true

def Passes.UsedAt (A : Array Bool) (i : FuncId) : Prop := A[i]? = some true

theorem Passes.markSub_refl (A : Array Bool) : MarkSub A A := fun _ h => h

theorem Passes.markSub_trans {A B C : Array Bool} (hAB : MarkSub A B)
    (hBC : MarkSub B C) : MarkSub A C := fun i hi => hBC i (hAB i hi)

theorem Passes.pruneWorkOne_size (P : Prog) (n fid : Nat)
    (s : MProd (List FuncId) (Array Bool)) :
    (pruneWorkOne P n fid s).2.size = s.2.size := by
  simp only [pruneWorkOne]
  split
  · split <;> simp
  · rfl

theorem Passes.pruneWorkOne_mono (P : Prog) (n fid : Nat)
    (s : MProd (List FuncId) (Array Bool)) :
    MarkSub s.2 (pruneWorkOne P n fid s).2 := by
  intro i hi
  simp only [pruneWorkOne]
  split
  · rename_i hfid
    split
    · by_cases h : fid = i
      · subst i
        have hin : fid < s.2.size := (Array.getElem?_eq_some_iff.mp hi).1
        simp [Array.set!, hin]
      · simpa [Array.set!, Array.getElem?_setIfInBounds_ne h] using hi
    · exact hi
  · exact hi

theorem Passes.pruneWorkOne_marks (P : Prog) {n fid : Nat}
    (s : MProd (List FuncId) (Array Bool)) (hfid : fid < n)
    (hsz : s.2.size = n) :
    UsedAt (pruneWorkOne P n fid s).2 fid := by
  simp only [UsedAt, pruneWorkOne, hfid, dite_true]
  split
  · simp [Array.set!, hsz, hfid]
  · rename_i hn
    have hu : s.2[fid]! = true := by
      cases h : s.2[fid]! <;> simp_all
    have hin : fid < s.2.size := by omega
    rw [Array.getElem?_eq_getElem hin]
    simpa [Array.getElem!_eq_getD, Array.getD, hin] using hu

theorem Passes.pruneWorkOne_new_origin (P : Prog) {n fid j : Nat}
    (s : MProd (List FuncId) (Array Bool))
    (hj : UsedAt (pruneWorkOne P n fid s).2 j) (hnot : ¬ UsedAt s.2 j) :
    j = fid := by
  simp only [UsedAt, pruneWorkOne] at hj
  split at hj
  · rename_i hfid
    split at hj
    · by_contra hne
      apply hnot
      unfold UsedAt
      simpa [Array.set!, Array.getElem?_setIfInBounds_ne (Ne.symm hne)] using hj
    · exact absurd hj (by simpa [UsedAt] using hnot)
  · exact absurd hj (by simpa [UsedAt] using hnot)

theorem Passes.pruneWorkOne_emits (P : Prog) {n fid : Nat}
    (s : MProd (List FuncId) (Array Bool)) (hfid : fid < n)
    (hsz : s.2.size = n)
    (hnot : ¬ UsedAt s.2 fid) {g : Func} (hg : P.funcs[fid]? = some g)
    {callee : FuncId} (hc : callee ∈ pruneCallees g) :
    callee ∈ (pruneWorkOne P n fid s).1 := by
  have hfalse : s.2[fid]! = false := by
    by_contra ht
    have ht' : s.2[fid]! = true := Bool.eq_true_of_not_eq_false ht
    apply hnot
    unfold UsedAt
    have hin : fid < s.2.size := by omega
    rw [Array.getElem?_eq_getElem hin]
    simpa [Array.getElem!_eq_getD, Array.getD, hin] using ht'
  simp only [pruneWorkOne, hfid, dite_true, Bool.not_eq_true, hfalse,
    Bool.not_false, if_true]
  apply List.mem_append_right
  rw [hg]
  simpa using hc

def Passes.pruneWorkFrom (P : Prog) (n : Nat) (work : List FuncId)
    (s : MProd (List FuncId) (Array Bool)) : MProd (List FuncId) (Array Bool) :=
  work.foldl (fun r fid => pruneWorkOne P n fid r) s

def Passes.pruneWork (P : Prog) (n : Nat) (work : List FuncId)
    (used : Array Bool) : MProd (List FuncId) (Array Bool) :=
  pruneWorkFrom P n work ⟨[], used⟩

theorem Passes.pruneWorkFrom_size (P : Prog) (n : Nat) (work : List FuncId)
    (s : MProd (List FuncId) (Array Bool)) :
    (pruneWorkFrom P n work s).2.size = s.2.size := by
  induction work generalizing s with
  | nil => rfl
  | cons fid work ih =>
      simp only [pruneWorkFrom, List.foldl_cons]
      change (pruneWorkFrom P n work (pruneWorkOne P n fid s)).2.size = s.2.size
      rw [ih, pruneWorkOne_size]

theorem Passes.pruneWorkFrom_mono (P : Prog) (n : Nat) (work : List FuncId)
    (s : MProd (List FuncId) (Array Bool)) :
    MarkSub s.2 (pruneWorkFrom P n work s).2 := by
  induction work generalizing s with
  | nil => exact markSub_refl s.2
  | cons fid work ih =>
      simp only [pruneWorkFrom, List.foldl_cons]
      exact markSub_trans (pruneWorkOne_mono P n fid s)
        (ih (pruneWorkOne P n fid s))

theorem Passes.pruneWorkFrom_marks (P : Prog) {n : Nat} {work : List FuncId}
    {s : MProd (List FuncId) (Array Bool)} (hsz : s.2.size = n) {fid : FuncId}
    (hm : fid ∈ work) (hlt : fid < n) :
    UsedAt (pruneWorkFrom P n work s).2 fid := by
  induction work generalizing s with
  | nil => simp at hm
  | cons j work ih =>
      simp only [pruneWorkFrom, List.foldl_cons]
      rcases List.mem_cons.mp hm with rfl | hm
      · exact (pruneWorkFrom_mono P n work (pruneWorkOne P n fid s)) fid
          (pruneWorkOne_marks P s hlt hsz)
      · exact ih (s := pruneWorkOne P n j s)
          (by rw [pruneWorkOne_size, hsz]) hm

theorem Passes.pruneWorkOne_next_mono (P : Prog) (n fid : Nat)
    (s : MProd (List FuncId) (Array Bool)) :
    ∀ x ∈ s.1, x ∈ (pruneWorkOne P n fid s).1 := by
  intro x hx
  simp only [pruneWorkOne]
  split
  · split
    · exact List.mem_append_left _ hx
    · exact hx
  · exact hx

theorem Passes.pruneWorkFrom_next_mono (P : Prog) (n : Nat) (work : List FuncId)
    (s : MProd (List FuncId) (Array Bool)) :
    ∀ x ∈ s.1, x ∈ (pruneWorkFrom P n work s).1 := by
  induction work generalizing s with
  | nil => exact fun _ h => h
  | cons fid work ih =>
      intro x hx
      exact ih (pruneWorkOne P n fid s) x (pruneWorkOne_next_mono P n fid s x hx)

theorem Passes.pruneWorkFrom_new_origin (P : Prog) {n : Nat}
    {work : List FuncId} {s : MProd (List FuncId) (Array Bool)} {j : FuncId}
    (hj : UsedAt (pruneWorkFrom P n work s).2 j) (hnot : ¬ UsedAt s.2 j) :
    j ∈ work := by
  induction work generalizing s with
  | nil => exact absurd hj hnot
  | cons fid work ih =>
      simp only [pruneWorkFrom, List.foldl_cons] at hj
      by_cases hm : UsedAt (pruneWorkOne P n fid s).2 j
      · exact List.mem_cons.mpr (Or.inl (pruneWorkOne_new_origin P s hm hnot))
      · exact List.mem_cons.mpr (Or.inr (ih (s := pruneWorkOne P n fid s) hj hm))

theorem Passes.pruneWorkFrom_emits (P : Prog) {n : Nat}
    {work : List FuncId} {s : MProd (List FuncId) (Array Bool)}
    (hsz : s.2.size = n) {fid : FuncId} (hm : fid ∈ work) (hlt : fid < n)
    (hnot : ¬ UsedAt s.2 fid) {g : Func} (hg : P.funcs[fid]? = some g)
    {callee : FuncId} (hc : callee ∈ pruneCallees g) :
    callee ∈ (pruneWorkFrom P n work s).1 := by
  induction work generalizing s with
  | nil => simp at hm
  | cons j work ih =>
      simp only [pruneWorkFrom, List.foldl_cons]
      rcases List.mem_cons.mp hm with rfl | hm
      · exact pruneWorkFrom_next_mono P n work (pruneWorkOne P n fid s) callee
          (pruneWorkOne_emits P s hlt hsz hnot hg hc)
      · by_cases hj : UsedAt (pruneWorkOne P n j s).2 fid
        · have heq : fid = j := pruneWorkOne_new_origin P s hj hnot
          subst j
          exact pruneWorkFrom_next_mono P n work (pruneWorkOne P n fid s) callee
            (pruneWorkOne_emits P s hlt hsz hnot hg hc)
        · exact ih (s := pruneWorkOne P n j s)
            (by rw [pruneWorkOne_size, hsz]) hm hj

inductive Passes.PruneReach (P : Prog) : FuncId → Prop
  | main {fid : FuncId} : fid ∈ pruneCallees P.main → PruneReach P fid
  | step {src fid : FuncId} {f : Func} : PruneReach P src →
      P.funcs[src]? = some f → fid ∈ pruneCallees f → PruneReach P fid

def Passes.PruneOrigin (P : Prog)
    (s : MProd (List FuncId) (Array Bool)) : Prop :=
  (∀ fid, UsedAt s.2 fid → PruneReach P fid) ∧
  ∀ fid ∈ s.1, PruneReach P fid

theorem Passes.pruneWorkOne_origin {P : Prog} {n fid : Nat}
    {s : MProd (List FuncId) (Array Bool)}
    (hfid : PruneReach P fid) (hs : PruneOrigin P s) :
    PruneOrigin P (pruneWorkOne P n fid s) := by
  constructor
  · intro j hj
    by_cases hold : UsedAt s.2 j
    · exact hs.1 j hold
    · have : j = fid := pruneWorkOne_new_origin P s hj hold
      simpa [this] using hfid
  · intro j hj
    simp only [pruneWorkOne] at hj
    split at hj
    · split at hj
      · rcases List.mem_append.mp hj with hj | hj
        · exact hs.2 j hj
        · rcases hg : P.funcs[fid]? with _ | g
          · simp [hg] at hj
          · exact PruneReach.step hfid hg (by simpa [hg] using hj)
      · exact hs.2 j hj
    · exact hs.2 j hj

theorem Passes.pruneWorkFrom_origin {P : Prog} {n : Nat}
    {work : List FuncId} {s : MProd (List FuncId) (Array Bool)}
    (hwork : ∀ fid ∈ work, PruneReach P fid) (hs : PruneOrigin P s) :
    PruneOrigin P (pruneWorkFrom P n work s) := by
  induction work generalizing s with
  | nil => exact hs
  | cons fid work ih =>
      simp only [pruneWorkFrom, List.foldl_cons]
      apply ih
      · intro j hj
        exact hwork j (by simp [hj])
      · exact pruneWorkOne_origin (hwork fid (by simp)) hs

def Passes.PruneFrontier (P : Prog) (used : Array Bool)
    (work : List FuncId) : Prop :=
  (∀ fid ∈ pruneCallees P.main, UsedAt used fid ∨ fid ∈ work) ∧
  (∀ src f, UsedAt used src → P.funcs[src]? = some f →
    ∀ fid ∈ pruneCallees f, UsedAt used fid ∨ fid ∈ work)

def Passes.WorkValid (n : Nat) (work : List FuncId) : Prop :=
  ∀ fid ∈ work, fid < n

theorem Passes.pruneFrontier_init (P : Prog) :
    PruneFrontier P (Array.replicate P.funcs.size false) (pruneCallees P.main) := by
  constructor
  · exact fun fid h => Or.inr h
  · intro src f hs
    unfold UsedAt at hs
    rcases Array.getElem?_eq_some_iff.mp hs with ⟨hlt, hget⟩
    simp at hget

theorem Passes.workValid_init {P : Prog} (hwf : P.wfCheck = true) :
    WorkValid P.funcs.size (pruneCallees P.main) := by
  intro fid hfid
  apply wfCheck_callee_lt (f := P.main) (n := P.funcs.size)
  · simp only [Prog.wfCheck, Bool.and_eq_true] at hwf
    exact hwf.1.2
  · exact hfid

theorem Passes.pruneWorkFrom_next_valid {P : Prog} (hwf : P.wfCheck = true)
    {n : Nat} (hn : n = P.funcs.size) {work : List FuncId}
    (hwork : WorkValid n work) {s : MProd (List FuncId) (Array Bool)}
    (hnext : WorkValid n s.1) :
    WorkValid n (pruneWorkFrom P n work s).1 := by
  induction work generalizing s with
  | nil => exact hnext
  | cons fid work ih =>
      have hfid : fid < n := hwork fid (by simp)
      apply ih (s := pruneWorkOne P n fid s)
      · exact fun j hj => hwork j (by simp [hj])
      · intro j hj
        by_cases hf : fid < n
        · by_cases hu : (!s.2[fid]!) = true
          · simp only [pruneWorkOne, hf, dite_true, hu, if_true] at hj
            rcases List.mem_append.mp hj with hj | hj
            · exact hnext j hj
            · rcases hget : P.funcs[fid]? with _ | g
              · simp [hget] at hj
              · have hjlt := wfCheck_callee_lt (f := g) (n := P.funcs.size)
                  (progWf_func hwf hget) (by simpa [hget] using hj)
                simpa [hn] using hjlt
          · simp only [pruneWorkOne, hf, dite_true, hu, if_false] at hj
            exact hnext j hj
        · simp only [pruneWorkOne, hf, dite_false] at hj
          exact hnext j hj

theorem Passes.pruneFrontier_advance {P : Prog} (hwf : P.wfCheck = true)
    {used : Array Bool} {work : List FuncId} (hsz : used.size = P.funcs.size)
    (hvalid : WorkValid P.funcs.size work) (hfront : PruneFrontier P used work) :
    let r := pruneWork P P.funcs.size work used
    PruneFrontier P r.2 r.1 := by
  let r := pruneWork P P.funcs.size work used
  have hmono : MarkSub used r.2 := by
    exact pruneWorkFrom_mono P P.funcs.size work ⟨[], used⟩
  have hmarks : ∀ fid ∈ work, UsedAt r.2 fid := by
    intro fid hm
    exact pruneWorkFrom_marks P hsz hm (hvalid fid hm)
  constructor
  · intro fid hm
    rcases hfront.1 fid hm with hu | hw
    · exact Or.inl (hmono fid hu)
    · exact Or.inl (hmarks fid hw)
  · intro src f hsrc hg fid hfid
    by_cases hold : UsedAt used src
    · rcases hfront.2 src f hold hg fid hfid with hu | hw
      · exact Or.inl (hmono fid hu)
      · exact Or.inl (hmarks fid hw)
    · have hsrcWork : src ∈ work :=
        pruneWorkFrom_new_origin P hsrc hold
      have hsrcLt := hvalid src hsrcWork
      exact Or.inr (pruneWorkFrom_emits P hsz hsrcWork hsrcLt hold hg hfid)

def Passes.pruneAdvance (P : Prog) (n : Nat)
    (s : MProd (Array Bool) (List FuncId)) : MProd (Array Bool) (List FuncId) :=
  let r := pruneWork P n s.2 s.1
  ⟨r.2, r.1⟩

theorem Passes.pruneRound_eq (P : Prog) (n i : Nat)
    (s : MProd (Array Bool) (List FuncId)) :
    pruneRound P n i s =
      if (pruneAdvance P n s).2.isEmpty then .done (pruneAdvance P n s)
      else .yield (pruneAdvance P n s) := by
  rfl

theorem Passes.pruneAdvance_size (P : Prog) (n : Nat)
    (s : MProd (Array Bool) (List FuncId)) :
    (pruneAdvance P n s).1.size = s.1.size := by
  exact pruneWorkFrom_size P n s.2 ⟨[], s.1⟩

theorem Passes.pruneAdvance_mono (P : Prog) (n : Nat)
    (s : MProd (Array Bool) (List FuncId)) :
    MarkSub s.1 (pruneAdvance P n s).1 := by
  exact pruneWorkFrom_mono P n s.2 ⟨[], s.1⟩

theorem Passes.pruneAdvance_empty {P : Prog} {n : Nat}
    {s : MProd (Array Bool) (List FuncId)} (h : s.2.isEmpty = true) :
    pruneAdvance P n s = s := by
  cases s with
  | mk used work =>
      have hw : work = [] := List.isEmpty_iff.mp h
      subst work
      rfl

theorem Passes.pruneFold_empty {P : Prog} {n : Nat}
    {s : MProd (Array Bool) (List FuncId)} (h : s.2.isEmpty = true)
    (l : List Nat) : l.foldl (fun s _ => pruneAdvance P n s) s = s := by
  induction l generalizing s with
  | nil => rfl
  | cons i is ih =>
      simp only [List.foldl_cons]
      rw [pruneAdvance_empty h]
      exact ih h

theorem Passes.loopWith_pruneRound_eq_fold (P : Prog) (n : Nat)
    (l : List Nat) (s : MProd (Array Bool) (List FuncId)) :
    loopWith (pruneRound P n) l s =
      l.foldl (fun s _ => pruneAdvance P n s) s := by
  induction l generalizing s with
  | nil => rfl
  | cons i is ih =>
      rw [loopWith_cons, pruneRound_eq]
      by_cases h : (pruneAdvance P n s).2.isEmpty = true
      · rw [if_pos h]
        symm
        exact pruneFold_empty h is
      · rw [if_neg h, List.foldl_cons]
        exact ih (pruneAdvance P n s)

def Passes.pruneIter (P : Prog) (n : Nat) :
    Nat → MProd (Array Bool) (List FuncId) → MProd (Array Bool) (List FuncId)
  | 0, s => s
  | k + 1, s => pruneIter P n k (pruneAdvance P n s)

theorem Passes.pruneFold_eq_iter (P : Prog) (n : Nat) (l : List Nat)
    (s : MProd (Array Bool) (List FuncId)) :
    l.foldl (fun s _ => pruneAdvance P n s) s = pruneIter P n l.length s := by
  induction l generalizing s with
  | nil => rfl
  | cons i is ih => simpa [pruneIter] using ih (pruneAdvance P n s)

theorem Passes.pruneState_eq_iter (P : Prog) :
    pruneState P = pruneIter P P.funcs.size (P.funcs.size + 1)
      ⟨Array.replicate P.funcs.size false, pruneCallees P.main⟩ := by
  unfold pruneState
  rw [loopWith_pruneRound_eq_fold, pruneFold_eq_iter]
  simp [pruneCallees]

def Passes.PruneStateOrigin (P : Prog)
    (s : MProd (Array Bool) (List FuncId)) : Prop :=
  (∀ fid, UsedAt s.1 fid → PruneReach P fid) ∧
  ∀ fid ∈ s.2, PruneReach P fid

theorem Passes.pruneAdvance_origin {P : Prog} {n : Nat}
    {s : MProd (Array Bool) (List FuncId)} (hs : PruneStateOrigin P s) :
    PruneStateOrigin P (pruneAdvance P n s) := by
  exact pruneWorkFrom_origin hs.2 ⟨hs.1, by simp⟩

theorem Passes.pruneIter_origin {P : Prog} {n : Nat} :
    ∀ (k : Nat) (s : MProd (Array Bool) (List FuncId)),
      PruneStateOrigin P s → PruneStateOrigin P (pruneIter P n k s) := by
  intro k
  induction k with
  | zero => intro s hs; exact hs
  | succ k ih =>
      intro s hs
      exact ih (pruneAdvance P n s) (pruneAdvance_origin hs)

theorem Passes.pruneState_used_reach {P : Prog} {fid : FuncId}
    (hused : UsedAt (pruneState P).1 fid) : PruneReach P fid := by
  rw [pruneState_eq_iter] at hused
  have hinit : PruneStateOrigin P
      ⟨Array.replicate P.funcs.size false, pruneCallees P.main⟩ := by
    constructor
    · intro j hj
      unfold UsedAt at hj
      have hjlt : j < P.funcs.size := by
        simpa using (Array.getElem?_eq_some_iff.mp hj).1
      simp [Array.getElem?_replicate, hjlt] at hj
    · intro j hj
      exact PruneReach.main hj
  exact (pruneIter_origin (P := P) (n := P.funcs.size)
    (P.funcs.size + 1) _ hinit).1 fid hused

def Passes.PruneInv (P : Prog) (s : MProd (Array Bool) (List FuncId)) : Prop :=
  s.1.size = P.funcs.size ∧ WorkValid P.funcs.size s.2 ∧
    PruneFrontier P s.1 s.2

theorem Passes.pruneInv_init {P : Prog} (hwf : P.wfCheck = true) :
    PruneInv P ⟨Array.replicate P.funcs.size false, pruneCallees P.main⟩ := by
  exact ⟨by simp, workValid_init hwf, pruneFrontier_init P⟩

theorem Passes.pruneInv_advance {P : Prog} (hwf : P.wfCheck = true)
    {s : MProd (Array Bool) (List FuncId)} (h : PruneInv P s) :
    PruneInv P (pruneAdvance P P.funcs.size s) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [pruneAdvance_size, h.1]
  · exact pruneWorkFrom_next_valid hwf rfl h.2.1 (fun _ h => by simp at h)
  · exact pruneFrontier_advance hwf h.1 h.2.1 h.2.2

theorem Passes.pruneReach_lt {P : Prog} (hwf : P.wfCheck = true)
    {fid : FuncId} (h : PruneReach P fid) : fid < P.funcs.size := by
  induction h with
  | main hcall => exact workValid_init hwf _ hcall
  | @step src fid f _ hg hcall ih =>
      exact wfCheck_callee_lt (progWf_func hwf hg) hcall

theorem Passes.PruneFrontier.missing {P : Prog} {used : Array Bool}
    {work : List FuncId} (hfront : PruneFrontier P used work)
    {fid : FuncId} (hr : PruneReach P fid) (hnot : ¬ UsedAt used fid) :
    ∃ j ∈ work, ¬ UsedAt used j := by
  induction hr with
  | main hcall =>
      rcases hfront.1 _ hcall with hu | hw
      · exact absurd hu hnot
      · exact ⟨_, hw, hnot⟩
  | @step src fid f hr hg hcall ih =>
      by_cases hs : UsedAt used src
      · rcases hfront.2 src f hs hg fid hcall with hu | hw
        · exact absurd hu hnot
        · exact ⟨_, hw, hnot⟩
      · exact ih hs

def Passes.pruneMeasure (n : Nat) (used : Array Bool) : Nat :=
  ((List.range n).map fun i => if used[i]? = some true then 1 else 0).sum

theorem Passes.pruneMeasure_le (n : Nat) (used : Array Bool) :
    pruneMeasure n used ≤ n := by
  unfold pruneMeasure
  have hle : ((List.range n).map fun i => if used[i]? = some true then 1 else 0).sum ≤
      ((List.range n).map fun _ => 1).sum :=
    List.sum_le_sum (fun i hi => by split <;> omega)
  simpa using hle

theorem Passes.pruneMeasure_mono {n : Nat} {A B : Array Bool}
    (h : MarkSub A B) : pruneMeasure n A ≤ pruneMeasure n B := by
  unfold pruneMeasure
  exact List.sum_le_sum (fun i hi => by
    by_cases hA : UsedAt A i
    · have hB : UsedAt B i := h i hA
      simp [UsedAt] at hA hB ⊢
      simp [hA, hB]
    · simp [UsedAt] at hA ⊢
      simp [hA])

theorem Passes.pruneMeasure_lt {n : Nat} {A B : Array Bool}
    (hsub : MarkSub A B) {j : Nat} (hj : j < n)
    (hA : ¬ UsedAt A j) (hB : UsedAt B j) :
    pruneMeasure n A < pruneMeasure n B := by
  unfold pruneMeasure
  apply List.sum_lt_sum
  · intro i hi
    by_cases hiA : UsedAt A i
    · have hiB := hsub i hiA
      simp [UsedAt] at hiA hiB ⊢
      simp [hiA, hiB]
    · simp [UsedAt] at hiA ⊢
      simp [hiA]
  · refine ⟨j, List.mem_range.mpr hj, ?_⟩
    simp [UsedAt] at hA hB ⊢
    simp [hA, hB]

theorem Passes.pruneIter_mono (P : Prog) (n k : Nat)
    (s : MProd (Array Bool) (List FuncId)) :
    MarkSub s.1 (pruneIter P n k s).1 := by
  induction k generalizing s with
  | zero => exact markSub_refl s.1
  | succ k ih =>
      exact markSub_trans (pruneAdvance_mono P n s)
        (ih (pruneAdvance P n s))

theorem Passes.pruneIter_measure_growth {P : Prog} (hwf : P.wfCheck = true) :
    ∀ (k : Nat) (s : MProd (Array Bool) (List FuncId)), PruneInv P s →
      ∀ {fid : FuncId}, PruneReach P fid →
        ¬ UsedAt (pruneIter P P.funcs.size k s).1 fid →
        pruneMeasure P.funcs.size s.1 + k ≤
          pruneMeasure P.funcs.size (pruneIter P P.funcs.size k s).1 := by
  intro k
  induction k with
  | zero => intro s hinv fid hr hnot; simp [pruneIter]
  | succ k ih =>
      intro s hinv fid hr hfinal
      let s' := pruneAdvance P P.funcs.size s
      have hinv' : PruneInv P s' := pruneInv_advance hwf hinv
      have hmonoTail : MarkSub s'.1 (pruneIter P P.funcs.size k s').1 :=
        pruneIter_mono P P.funcs.size k s'
      have hnot' : ¬ UsedAt s'.1 fid := fun h => hfinal (hmonoTail fid h)
      have hmissing := hinv.2.2.missing hr
        (fun h => hnot' (pruneAdvance_mono P P.funcs.size s fid h))
      obtain ⟨j, hjw, hjnot⟩ := hmissing
      have hjlt : j < P.funcs.size := hinv.2.1 j hjw
      have hjmark : UsedAt s'.1 j :=
        pruneWorkFrom_marks P hinv.1 hjw hjlt
      have hstep : pruneMeasure P.funcs.size s.1 < pruneMeasure P.funcs.size s'.1 :=
        pruneMeasure_lt (pruneAdvance_mono P P.funcs.size s) hjlt hjnot hjmark
      have htail := ih s' hinv' hr hfinal
      simp only [pruneIter] at htail ⊢
      dsimp only [s'] at hstep htail
      omega

theorem Passes.pruneState_marks {P : Prog} (hwf : P.wfCheck = true)
    {fid : FuncId} (hr : PruneReach P fid) : UsedAt (pruneState P).1 fid := by
  rw [pruneState_eq_iter]
  by_contra hnot
  have hgrow := pruneIter_measure_growth hwf (P.funcs.size + 1)
    ⟨Array.replicate P.funcs.size false, pruneCallees P.main⟩
    (pruneInv_init hwf) hr hnot
  have hzero : pruneMeasure P.funcs.size (Array.replicate P.funcs.size false) = 0 := by
    unfold pruneMeasure
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have hlt := List.mem_range.mp hi
    simp [Array.getElem?_replicate, hlt]
  have hbound := pruneMeasure_le P.funcs.size
    (pruneIter P P.funcs.size (P.funcs.size + 1)
      ⟨Array.replicate P.funcs.size false, pruneCallees P.main⟩).1
  rw [hzero] at hgrow
  omega

theorem Passes.usedAt_getElem! {A : Array Bool} {i : Nat}
    (h : UsedAt A i) : A[i]! = true := by
  unfold UsedAt at h
  obtain ⟨hlt, hget⟩ := Array.getElem?_eq_some_iff.mp h
  simpa [Array.getElem!_eq_getD, Array.getD, hlt] using hget

def Passes.pruneKeepN (P : Prog) (used : Array Bool) (m : Nat) :
    MProd (Array Func) (Array (Option FuncId)) :=
  (List.range m).foldl (fun s fid => pruneKeepOne P used fid s)
    ⟨#[], Array.replicate P.funcs.size none⟩

theorem Passes.pruneKeep_eq_keepN (P : Prog) (used : Array Bool) :
    pruneKeep P used = pruneKeepN P used P.funcs.size := by
  simp [pruneKeep, pruneKeepN, List.range_eq_range']

theorem Passes.pruneKeepN_remap_size (P : Prog) (used : Array Bool) (m : Nat) :
    (pruneKeepN P used m).2.size = P.funcs.size := by
  unfold pruneKeepN
  have key : ∀ (l : List Nat) (s : MProd (Array Func) (Array (Option FuncId))),
      (l.foldl (fun s fid => pruneKeepOne P used fid s) s).2.size = s.2.size := by
    intro l
    induction l with
    | nil => exact fun _ => rfl
    | cons fid l ih =>
        intro s
        simp only [List.foldl_cons]
        rw [ih]
        simp only [pruneKeepOne]
        split <;> simp
  rw [key]
  simp

theorem Passes.pruneKeepN_lookup {P : Prog} {used : Array Bool}
    (husedSize : used.size = P.funcs.size) :
    ∀ (m : Nat), m ≤ P.funcs.size → ∀ {fid : FuncId} {g : Func}, fid < m →
      P.funcs[fid]? = some g → UsedAt used fid →
      ∃ fid', (pruneKeepN P used m).2[fid]? = some (some fid') ∧
        (pruneKeepN P used m).1[fid']? = some g := by
  intro m
  induction m with
  | zero =>
      intro hm fid g hfid hfunc hused
      exact (Nat.not_lt_zero fid hfid).elim
  | succ m ih =>
      intro hm fid g hfid hfunc hused
      have hmle : m ≤ P.funcs.size := by omega
      rw [pruneKeepN, List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      let s := pruneKeepN P used m
      change ∃ fid', (pruneKeepOne P used m s).2[fid]? = some (some fid') ∧
        (pruneKeepOne P used m s).1[fid']? = some g
      have hsRemap : s.2.size = P.funcs.size := pruneKeepN_remap_size P used m
      rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hfid) with heq | hfidm
      · subst fid
        have hmu : used[m]! = true := usedAt_getElem! hused
        have hmf : P.funcs[m]! = g := by
          obtain ⟨hlt, hget⟩ := Array.getElem?_eq_some_iff.mp hfunc
          simpa [Array.getElem!_eq_getD, Array.getD, hlt] using hget
        refine ⟨s.1.size, ?_, ?_⟩
        · simp [pruneKeepOne, hmu, Array.set!, hsRemap, show m < P.funcs.size by omega]
        · simp [pruneKeepOne, hmu, hmf]
      · have heq : fid ≠ m := Nat.ne_of_lt hfidm
        obtain ⟨fid', hremap, hkept⟩ := ih hmle
          (fid := fid) (g := g) hfidm hfunc hused
        by_cases hmu : used[m]! = true
        · refine ⟨fid', ?_, ?_⟩
          · simpa [s, pruneKeepOne, hmu,
              Array.getElem?_setIfInBounds_ne (Ne.symm heq)] using hremap
          · rw [show pruneKeepOne P used m s =
                ⟨s.1.push P.funcs[m]!, s.2.set! m (some s.1.size)⟩ by
                  simp [pruneKeepOne, hmu]]
            simp only
            rw [Array.getElem?_push]
            have hlt : fid' < s.1.size := (Array.getElem?_eq_some_iff.mp hkept).1
            rw [if_neg (Nat.ne_of_lt hlt)]
            exact hkept
        · refine ⟨fid', ?_, ?_⟩
          · simpa [s, pruneKeepOne, hmu] using hremap
          · simpa [s, pruneKeepOne, hmu] using hkept

theorem Passes.pruneKeep_lookup {P : Prog} {used : Array Bool}
    (husedSize : used.size = P.funcs.size) {fid : FuncId} {g : Func}
    (hfunc : P.funcs[fid]? = some g) (hused : UsedAt used fid) :
    ∃ fid', (pruneKeep P used).2[fid]? = some (some fid') ∧
      (pruneKeep P used).1[fid']? = some g := by
  rw [pruneKeep_eq_keepN]
  apply pruneKeepN_lookup husedSize P.funcs.size (le_refl _) _ hfunc hused
  exact (Array.getElem?_eq_some_iff.mp hfunc).1

theorem Passes.pruneKeepN_mem {P : Prog} {used : Array Bool}
    (husedSize : used.size = P.funcs.size) :
    ∀ (m : Nat), m ≤ P.funcs.size → ∀ {g : Func},
      g ∈ (pruneKeepN P used m).1 →
      ∃ fid, fid < m ∧ P.funcs[fid]? = some g ∧ UsedAt used fid := by
  intro m
  induction m with
  | zero => intro hm g hg; simp [pruneKeepN] at hg
  | succ m ih =>
      intro hm g hg
      have hmle : m ≤ P.funcs.size := by omega
      rw [pruneKeepN, List.range_succ, List.foldl_append] at hg
      simp only [List.foldl_cons, List.foldl_nil] at hg
      let s := pruneKeepN P used m
      change g ∈ (pruneKeepOne P used m s).1 at hg
      by_cases hmu : used[m]! = true
      · rw [show pruneKeepOne P used m s =
            ⟨s.1.push P.funcs[m]!, s.2.set! m (some s.1.size)⟩ by
              simp [pruneKeepOne, hmu]] at hg
        rcases Array.mem_push.mp hg with hold | heq
        · obtain ⟨fid, hfid, hfunc, hu⟩ := ih hmle hold
          exact ⟨fid, by omega, hfunc, hu⟩
        · have hmlt : m < P.funcs.size := by omega
          have hfunc : P.funcs[m]? = some P.funcs[m]! := by
            rw [Array.getElem?_eq_getElem hmlt, getElem!_eq_getElem hmlt]
          have hu : UsedAt used m := by
            unfold UsedAt
            have hult : m < used.size := by omega
            rw [Array.getElem?_eq_getElem hult]
            simpa [Array.getElem!_eq_getD, Array.getD, hult] using hmu
          exact ⟨m, by omega, by simpa [heq] using hfunc, hu⟩
      · have hold : g ∈ s.1 := by
          simpa [pruneKeepOne, hmu] using hg
        obtain ⟨fid, hfid, hfunc, hu⟩ := ih hmle hold
        exact ⟨fid, by omega, hfunc, hu⟩

theorem Passes.pruneKeep_mem {P : Prog} {used : Array Bool}
    (husedSize : used.size = P.funcs.size) {g : Func}
    (hg : g ∈ (pruneKeep P used).1) :
    ∃ fid, P.funcs[fid]? = some g ∧ UsedAt used fid := by
  rw [pruneKeep_eq_keepN] at hg
  obtain ⟨fid, hfid, hfunc, hu⟩ :=
    pruneKeepN_mem husedSize P.funcs.size (le_refl _) hg
  exact ⟨fid, hfunc, hu⟩

theorem Passes.pruneIter_size (P : Prog) (n k : Nat)
    (s : MProd (Array Bool) (List FuncId)) :
    (pruneIter P n k s).1.size = s.1.size := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
      rw [pruneIter, ih, pruneAdvance_size]

theorem Passes.pruneState_used_size (P : Prog) :
    (pruneState P).1.size = P.funcs.size := by
  rw [pruneState_eq_iter, pruneIter_size]
  simp

def Passes.pruneRest (remap : Array (Option FuncId)) (r : Rest) : Rest :=
  ⟨r.instrs.map (pruneInstr remap), r.term⟩

theorem Passes.pruneFix_params (remap : Array (Option FuncId)) (f : Func) :
    (pruneFix remap f).params = f.params := rfl

theorem Passes.pruneFix_entry (remap : Array (Option FuncId)) (f : Func) :
    (pruneFix remap f).entry = f.entry := rfl

theorem Passes.pruneFix_block {remap : Array (Option FuncId)} {f : Func}
    {i : BlockId} {b : Block} (hb : f.blocks[i]? = some b) :
    (pruneFix remap f).blocks[i]? = some (pruneBlock remap b) := by
  simp [pruneFix, hb]

theorem Passes.pruneFix_kept_lookup {remap : Array (Option FuncId)}
    {kept : Array Func} {fid : FuncId} {g : Func} (hg : kept[fid]? = some g) :
    (kept.map (pruneFix remap))[fid]? = some (pruneFix remap g) := by
  simp [hg]

theorem Passes.pruneRemap_value {remap : Array (Option FuncId)}
    {fid fid' : FuncId} (h : remap[fid]? = some (some fid')) :
    (remap[fid]?.join).getD fid = fid' := by
  rw [h]
  rfl

def Passes.PruneFuncReach (P : Prog) (f : Func) : Prop :=
  f = P.main ∨ ∃ fid, PruneReach P fid ∧ P.funcs[fid]? = some f

def Passes.PruneRestReach (P : Prog) (r : Rest) : Prop :=
  ∀ ds fid as, Instr.call ds fid as ∈ r.instrs → PruneReach P fid

theorem Passes.pruneFuncReach_call {P : Prog} {f : Func}
    (hf : PruneFuncReach P f) {b : Block} (hb : b ∈ f.blocks.toList)
    {ds : List ValId} {fid : FuncId} {as : List ValId}
    (hi : Instr.call ds fid as ∈ b.instrs) : PruneReach P fid := by
  rcases hf with rfl | ⟨src, hsrc, hlookup⟩
  · exact PruneReach.main (mem_pruneCallees.mpr ⟨b, hb, ds, as, hi⟩)
  · exact PruneReach.step hsrc hlookup
      (mem_pruneCallees.mpr ⟨b, hb, ds, as, hi⟩)

theorem Passes.pruneInstr_defs (remap : Array (Option FuncId)) (i : Instr) :
    (pruneInstr remap i).defs = i.defs := by
  cases i <;> rfl

theorem Passes.pruneBlock_allDefs (remap : Array (Option FuncId)) (b : Block) :
    blockAllDefs (pruneBlock remap b) = blockAllDefs b := by
  simp only [blockAllDefs, pruneBlock, List.flatMap_map, pruneInstr_defs]

theorem Passes.pruneFix_allDefs (remap : Array (Option FuncId)) (f : Func) :
    (pruneFix remap f).allDefs = f.allDefs := by
  unfold Func.allDefs pruneFix
  simp only [Array.toList_map, List.flatMap_map, pruneBlock_allDefs]

theorem Passes.pruneBlock_wf {remap : Array (Option FuncId)} {f : Func}
    {b : Block} {oldN newN : Nat}
    (hbwf : BlockWF f.blocks f.nrets oldN b)
    (hcall : ∀ ds fid as, Instr.call ds fid as ∈ b.instrs →
      (remap[fid]?.join).getD fid < newN) :
    BlockWF (pruneFix remap f).blocks (pruneFix remap f).nrets newN
      (pruneBlock remap b) := by
  refine ⟨hbwf.1, ?_, ?_⟩
  · intro e he
    obtain ⟨tb, htb, hlen⟩ := hbwf.2.1 e (by simpa [pruneBlock] using he)
    exact ⟨pruneBlock remap tb, pruneFix_block htb,
      by simpa [pruneBlock] using hlen⟩
  · intro i hi
    simp only [pruneBlock] at hi
    obtain ⟨old, hold, heq⟩ := List.mem_map.mp hi
    subst i
    cases old with
    | const => trivial
    | op ds yop as => simpa [pruneInstr] using hbwf.2.2 (.op ds yop as) hold
    | call ds fid as => exact hcall ds fid as hold

theorem Passes.pruneFix_wf {remap : Array (Option FuncId)} {f : Func}
    {oldN newN : Nat} (hfwf : f.wfCheck oldN = true)
    (hcall : ∀ b ∈ f.blocks.toList, ∀ ds fid as,
      Instr.call ds fid as ∈ b.instrs →
      (remap[fid]?.join).getD fid < newN) :
    (pruneFix remap f).wfCheck newN = true := by
  obtain ⟨hnd, hentry, ⟨eb, heb, hempty⟩, hblocks⟩ :=
    func_wfCheck_iff.mp hfwf
  apply func_wfCheck_iff.mpr
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [pruneFix_allDefs] using hnd
  · simpa [pruneFix] using hentry
  · exact ⟨pruneBlock remap eb, by simpa [pruneFix] using pruneFix_block heb,
      by simpa [pruneBlock] using hempty⟩
  · intro b hb
    have hbarr : b ∈ (pruneFix remap f).blocks := by simpa using hb
    obtain ⟨old, hold, rfl⟩ := Array.mem_map.mp (by simpa [pruneFix] using hbarr)
    exact pruneBlock_wf (hblocks old (by simpa using hold))
      (fun ds fid as hi => hcall old (by simpa using hold) ds fid as hi)

theorem Passes.pruneFix_wf_reach {P : Prog} {used : Array Bool}
    (hwf : P.wfCheck = true) (husedSize : used.size = P.funcs.size)
    (hall : ∀ fid, PruneReach P fid → UsedAt used fid)
    {f : Func} (hreach : PruneFuncReach P f)
    (hfwf : f.wfCheck P.funcs.size = true) :
    let kept := (pruneKeep P used).1
    let remap := (pruneKeep P used).2
    (pruneFix remap f).wfCheck kept.size = true := by
  let kept := (pruneKeep P used).1
  let remap := (pruneKeep P used).2
  apply pruneFix_wf hfwf
  intro b hb ds fid as hi
  have hr : PruneReach P fid := pruneFuncReach_call hreach hb hi
  have hu : UsedAt used fid := hall fid hr
  have hlt : fid < P.funcs.size := pruneReach_lt hwf hr
  have hfunc : P.funcs[fid]? = some P.funcs[fid] :=
    Array.getElem?_eq_getElem hlt
  obtain ⟨fid', hremap, hkept⟩ := pruneKeep_lookup husedSize hfunc hu
  rw [pruneRemap_value hremap]
  exact (Array.getElem?_eq_some_iff.mp hkept).1

theorem Passes.pruneRestReach_block {P : Prog} {f : Func}
    (hf : PruneFuncReach P f) {b : Block} (hb : b ∈ f.blocks.toList) :
    PruneRestReach P ⟨b.instrs, b.term⟩ := by
  intro ds fid as hi
  exact pruneFuncReach_call hf hb hi

theorem Passes.pruneRestReach_tail {P : Prog} {i : Instr} {is : List Instr}
    {t : Term} (h : PruneRestReach P ⟨i :: is, t⟩) :
    PruneRestReach P ⟨is, t⟩ := by
  intro ds fid as hi
  exact h ds fid as (by simp [hi])

theorem Passes.pruneRestReach_head {P : Prog} {ds : List ValId}
    {fid : FuncId} {as : List ValId} {is : List Instr} {t : Term}
    (h : PruneRestReach P ⟨Instr.call ds fid as :: is, t⟩) :
    PruneReach P fid := h ds fid as (by simp)

theorem Passes.pruneExec {P : Prog} {used : Array Bool}
    (husedSize : used.size = P.funcs.size)
    (hall : ∀ fid, PruneReach P fid → UsedAt used fid)
    {f : Func} {R : Regs} {st : EvmState} {rest : Rest} {res : FRes}
    (hexec : Exec (model := model) P f R st rest res) :
    ∀ (hfunc : PruneFuncReach P f) (hrest : PruneRestReach P rest),
      let kept := (pruneKeep P used).1
      let remap := (pruneKeep P used).2
      let Q : Prog :=
        { main := pruneFix remap P.main
          funcs := kept.map (pruneFix remap) }
      Exec (model := model) Q (pruneFix remap f) R st (pruneRest remap rest) res := by
  induction hexec with
  | @const f R st d v is t res htail ih =>
      intro hfunc hrest
      exact Exec.const (ih hfunc (pruneRestReach_tail hrest))
  | @op f R st st' ds yop as args rets is t res hget hop hlen htail ih =>
      intro hfunc hrest
      exact Exec.op hget hop hlen (ih hfunc (pruneRestReach_tail hrest))
  | @opHalt f R st st' ds yop as args is t hget hop =>
      intro hfunc hrest
      exact Exec.opHalt hget hop
  | @call f g R st st' ds as fid args rvals eb is t res hlookup hget hplen heb
      hbody hlen htail ihbody ih =>
      intro hfunc hrest
      have hreach : PruneReach P fid := pruneRestReach_head hrest
      have hused : UsedAt used fid := hall fid hreach
      obtain ⟨fid', hremap, hkept⟩ := pruneKeep_lookup husedSize hlookup hused
      let kept := (pruneKeep P used).1
      let remap := (pruneKeep P used).2
      have hnewLookup : (kept.map (pruneFix remap))[fid']? =
          some (pruneFix remap g) := pruneFix_kept_lookup hkept
      have hfidValue : (remap[fid]?.join).getD fid = fid' := pruneRemap_value hremap
      have hcalleeReach : PruneFuncReach P g := Or.inr ⟨fid, hreach, hlookup⟩
      have hebMem : eb ∈ g.blocks.toList := by
        simpa using block_mem_of_getElem? heb
      have hbody' := ihbody hcalleeReach (pruneRestReach_block hcalleeReach hebMem)
      have htail' := ih hfunc (pruneRestReach_tail hrest)
      change Exec _ _ _ _
        ⟨Instr.call ds ((remap[fid]?.join).getD fid) as ::
          (pruneRest remap ⟨is, t⟩).instrs, t⟩ res
      rw [hfidValue]
      exact Exec.call hnewLookup hget (by simpa [pruneFix] using hplen)
        (pruneFix_block heb) hbody' hlen htail'
  | @callHalt f g R st st' ds as fid args eb is t hlookup hget hplen heb hbody ihbody =>
      intro hfunc hrest
      have hreach : PruneReach P fid := pruneRestReach_head hrest
      have hused : UsedAt used fid := hall fid hreach
      obtain ⟨fid', hremap, hkept⟩ := pruneKeep_lookup husedSize hlookup hused
      let kept := (pruneKeep P used).1
      let remap := (pruneKeep P used).2
      have hnewLookup : (kept.map (pruneFix remap))[fid']? =
          some (pruneFix remap g) := pruneFix_kept_lookup hkept
      have hfidValue : (remap[fid]?.join).getD fid = fid' := pruneRemap_value hremap
      have hcalleeReach : PruneFuncReach P g := Or.inr ⟨fid, hreach, hlookup⟩
      have hebMem : eb ∈ g.blocks.toList := by
        simpa using block_mem_of_getElem? heb
      have hbody' := ihbody hcalleeReach (pruneRestReach_block hcalleeReach hebMem)
      change Exec _ _ _ _
        ⟨Instr.call ds ((remap[fid]?.join).getD fid) as ::
          (pruneRest remap ⟨is, t⟩).instrs, t⟩ (.halt st')
      rw [hfidValue]
      exact Exec.callHalt hnewLookup hget (by simpa [pruneFix] using hplen)
        (pruneFix_block heb) hbody'
  | @jump f R st e tb args res htb hget hplen htail ih =>
      intro hfunc hrest
      have htbMem : tb ∈ f.blocks.toList := by simpa using block_mem_of_getElem? htb
      exact Exec.jump (pruneFix_block htb) hget (by simpa [pruneBlock] using hplen)
        (ih hfunc (pruneRestReach_block hfunc htbMem))
  | @branchTrue f R st c v et ef tb args res hc hv htb hget hplen htail ih =>
      intro hfunc hrest
      have htbMem : tb ∈ f.blocks.toList := by simpa using block_mem_of_getElem? htb
      exact Exec.branchTrue hc hv (pruneFix_block htb) hget
        (by simpa [pruneBlock] using hplen)
        (ih hfunc (pruneRestReach_block hfunc htbMem))
  | @branchFalse f R st c et ef tb args res hc htb hget hplen htail ih =>
      intro hfunc hrest
      have htbMem : tb ∈ f.blocks.toList := by simpa using block_mem_of_getElem? htb
      exact Exec.branchFalse hc (pruneFix_block htb) hget
        (by simpa [pruneBlock] using hplen)
        (ih hfunc (pruneRestReach_block hfunc htbMem))
  | @ret f R st xs vals hget =>
      intro hfunc hrest
      exact Exec.ret hget
  | @halt f R st st' yop as args hget hop =>
      intro hfunc hrest
      exact Exec.halt hget hop

theorem Passes.pruneFuncs_wf {P : Prog} (hwf : P.wfCheck = true) :
    (pruneFuncs P).wfCheck = true := by
  rw [pruneFuncs_eq_model]
  unfold pruneModel
  let used := (pruneState P).1
  by_cases hallUsed : used.all id = true
  · rw [if_pos hallUsed]
    exact hwf
  · rw [if_neg hallUsed]
    let kept := (pruneKeep P used).1
    let remap := (pruneKeep P used).2
    have husedSize : used.size = P.funcs.size := pruneState_used_size P
    have hmarks : ∀ fid, PruneReach P fid → UsedAt used fid := by
      intro fid hr
      exact pruneState_marks hwf hr
    have horigin : ∀ fid, UsedAt used fid → PruneReach P fid := by
      intro fid hu
      exact pruneState_used_reach hu
    have hparts := hwf
    simp only [Prog.wfCheck, Bool.and_eq_true] at hparts ⊢
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · simpa [pruneFix, kept, remap] using hparts.1.1.1
    · simpa [pruneFix, kept, remap] using hparts.1.1.2
    · have hm := pruneFix_wf_reach hwf husedSize hmarks
          (f := P.main) (Or.inl rfl) hparts.1.2
      simpa [kept, remap] using hm
    · rw [Array.all_eq_true_iff_forall_mem]
      intro q hq
      obtain ⟨g, hg, rfl⟩ := Array.mem_map.mp hq
      obtain ⟨fid, hfunc, hu⟩ := pruneKeep_mem husedSize hg
      have hr : PruneReach P fid := horigin fid hu
      have hgwf : g.wfCheck P.funcs.size = true := progWf_func hwf hfunc
      have hnew := pruneFix_wf_reach hwf husedSize hmarks
        (f := g) (Or.inr ⟨fid, hr, hfunc⟩) hgwf
      simpa [kept, remap] using hnew

/-- **Pruning preserves whole-program runs.** The worklist invariant proves
that every function transitively reachable from `main` is marked within the
`n + 1` rounds.  `pruneKeep_lookup` then relates each marked old index to its
new index and original function, and `pruneExec` transports the complete call
tree while rewriting every call instruction through that remap. -/
theorem pruneFuncs_sound {P : Prog} {yst0 yst' : EvmState} {o : Outcome}
    (hwf : P.wfCheck = true) (hrun : Run (model := model) P yst0 yst' o) :
    Run (model := model) (Passes.pruneFuncs P) yst0 yst' o := by
  rw [Passes.pruneFuncs_eq_model]
  unfold Passes.pruneModel
  let used := (Passes.pruneState P).1
  by_cases hallUsed : used.all id = true
  · change Run (model := model) (if used.all id then P else _) yst0 yst' o
    rw [if_pos hallUsed]
    exact hrun
  · change Run (model := model) (if used.all id then P else _) yst0 yst' o
    rw [if_neg hallUsed]
    have husedSize : used.size = P.funcs.size := by
      exact Passes.pruneState_used_size P
    have hmarks : ∀ fid, Passes.PruneReach P fid → Passes.UsedAt used fid := by
      intro fid hr
      exact Passes.pruneState_marks hwf hr
    cases hrun with
    | normal heb hexec =>
        rename_i eb
        refine Run.normal (Passes.pruneFix_block heb) ?_
        have hebMem : eb ∈ P.main.blocks.toList := by
          simpa using block_mem_of_getElem? heb
        exact Passes.pruneExec (model := model) husedSize hmarks hexec
          (Or.inl rfl) (Passes.pruneRestReach_block (Or.inl rfl) hebMem)
    | halt heb hexec =>
        rename_i eb
        refine Run.halt (Passes.pruneFix_block heb) ?_
        have hebMem : eb ∈ P.main.blocks.toList := by
          simpa using block_mem_of_getElem? heb
        exact Passes.pruneExec (model := model) husedSize hmarks hexec
          (Or.inl rfl) (Passes.pruneRestReach_block (Or.inl rfl) hebMem)

def Passes.inlineRound (P : Prog) : Prog :=
  pruneFuncs (inlineMap (siteCounts P) P)

def Passes.inlineSame (P Q : Prog) : Bool :=
  Q.funcs.size == P.funcs.size && siteCounts Q == siteCounts P

theorem Passes.inlineRound_wf {P : Prog} (hwf : P.wfCheck = true) :
    (inlineRound P).wfCheck = true := by
  exact pruneFuncs_wf (inlineMap_wf hwf)

theorem Passes.pruneFuncs_inlineMap_wf {P : Prog} (hwf : P.wfCheck = true) :
    (pruneFuncs (inlineMap (siteCounts P) P)).wfCheck = true := by
  exact inlineRound_wf hwf

theorem inlineRound_sound {P : Prog} {yst0 yst' : EvmState} {o : Outcome}
    (hwf : P.wfCheck = true) (hrun : Run (model := model) P yst0 yst' o) :
    Run (model := model) (Passes.inlineRound P) yst0 yst' o := by
  apply pruneFuncs_sound (Passes.inlineMap_wf hwf)
  exact Passes.inlineMap_sound hwf hrun

def Passes.inlineProgN : Nat → Prog → Prog
  | 0, P => P
  | n + 1, P =>
      let Q := inlineRound P
      if inlineSame P Q then Q else inlineProgN n Q

def Passes.inlineProgStep (_ : Nat) (P : Prog) : ForInStep Prog :=
  let Q := inlineRound P
  if inlineSame P Q then .done Q else .yield Q

def Passes.inlineProgRawStep (_ : Nat)
    (s : MProd (Option Prog) Prog) : ForInStep (MProd (Option Prog) Prog) :=
  let Q := inlineRound s.2
  if inlineSame s.2 Q then .done ⟨some Q, Q⟩ else .yield ⟨none, Q⟩

theorem Passes.inlineProgRaw_loop (l : List Nat) (P : Prog) :
    let r := loopWith inlineProgRawStep l ⟨none, P⟩
    r.1.getD r.2 = loopWith inlineProgStep l P := by
  induction l generalizing P with
  | nil => rfl
  | cons i is ih =>
      rw [loopWith_cons, loopWith_cons]
      by_cases hs : inlineSame P (inlineRound P) = true
      · simp [inlineProgRawStep, inlineProgStep, hs]
      · simpa [inlineProgRawStep, inlineProgStep, hs] using ih (inlineRound P)

theorem Passes.inlineProgStep_loop (l : List Nat) (P : Prog) :
    loopWith inlineProgStep l P = inlineProgN l.length P := by
  induction l generalizing P with
  | nil => rfl
  | cons i is ih =>
      rw [loopWith_cons]
      by_cases hs : inlineSame P (inlineRound P) = true
      · simp [inlineProgStep, inlineProgN, hs]
      · simpa [inlineProgStep, inlineProgN, hs] using ih (inlineRound P)

theorem Passes.inlineProg_eq_inlineProgN (P : Prog) :
    inlineProg P = inlineProgN 3 P := by
  unfold inlineProg
  dsimp only
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rw [Id.forIn_eq_loopWith (g := inlineProgRawStep) (h := by
    intro i s
    simp only [inlineProgRawStep, inlineRound, inlineMap, inlineSame]
    split <;> rfl)]
  simp only [Id.run, bind, pure]
  let l := List.range' 0 ((3 - 0 + 1 - 1) / 1) 1
  let r := loopWith inlineProgRawStep l ⟨none, P⟩
  change (match r.1 with | none => r.2 | some a => a) = _
  have hm : (match r.1 with | none => r.2 | some a => a) = r.1.getD r.2 := by
    cases r.1 <;> rfl
  rw [hm]
  have hr := inlineProgRaw_loop l P
  change r.1.getD r.2 = _ at hr
  rw [hr, inlineProgStep_loop]
  rfl

theorem inlineProgN_sound {P : Prog} {yst0 yst' : EvmState} {o : Outcome} :
    ∀ n, P.wfCheck = true → Run (model := model) P yst0 yst' o →
      Run (model := model) (Passes.inlineProgN n P) yst0 yst' o := by
  intro n
  induction n generalizing P with
  | zero => intro hwf hrun; exact hrun
  | succ n ih =>
      intro hwf hrun
      have hroundWf := Passes.inlineRound_wf hwf
      have hroundRun := inlineRound_sound hwf hrun
      simp only [Passes.inlineProgN]
      split
      · exact hroundRun
      · exact ih hroundWf hroundRun

/-- **Inlining soundness**, the statement the top-level proof consumes.

The indexed replay chain proves one simultaneous `inlineMap` round.  The
syntactic `inlineMap_wf` and `pruneFuncs_wf` lemmas preserve the hypothesis
needed by the next round, while `inlineProg_eq_inlineProgN` exposes the
implementation's three-round early-return loop as a pure recursion. -/
theorem inlineProg_sound {P : Prog} {yst0 yst' : EvmState} {o : Outcome}
    (hwf : P.wfCheck = true) (hrun : Run (model := model) P yst0 yst' o) :
    Run (model := model) (Passes.inlineProg P) yst0 yst' o := by
  rw [Passes.inlineProg_eq_inlineProgN]
  exact inlineProgN_sound 3 hwf hrun

end

/-! ## Per-pass soundness

Each pass is stated at the *function-entry* level: an execution of `f` from its
entry block, with the register file that binds exactly `f.params`, maps to an
execution of the rewritten function from *its* entry block with the same result.
That is the granularity the whole-program statement needs (`Run` starts `main`
that way, and `Exec.call` starts a callee that way), and it is where the
liveness invariant `LiveAgree` has its base case (`liveAgree_entry`).

Passes 1 and 3 carry `ToAsm.Func.domCheck` — the counterexample above shows they
must. Passes 2 and 4 do not need it.

Composing the four into `optimizeProg_sound'` needs two further ingredients:

* the **preservation** lemmas below (`*_wf`, `*_dom`), because `runOnce` chains
  four passes and `optimizeFunc` iterates that three times, so each pass has to
  hand the next one its hypotheses; and
* a **simultaneous** induction over the whole program rather than a
  per-function composition, because `Exec` recurses into callees through `P`
  (`Exec.call` looks up `P.funcs[fid]?`), so the callee's derivation has to be
  transported at the same time as the caller's. The per-function lemmas below
  are the block-level content of that induction, not a decomposition of it.
-/

variable [model : ExternalModel]

namespace Passes

def inEdgeArgsEdgeStep (acc : Array (List (List ValId))) (e : Edge) :
    Array (List (List ValId)) :=
  acc.setIfInBounds e.target (e.args :: acc[e.target]!)

def inEdgeArgsBlockStep (acc : Array (List (List ValId))) (b : Block) :
    Array (List (List ValId)) :=
  b.term.edges.foldl inEdgeArgsEdgeStep acc

omit model in
theorem inEdgeArgs_eq_fold (f : Func) :
    inEdgeArgs f = f.blocks.toList.foldl inEdgeArgsBlockStep
      (Array.replicate f.blocks.size []) := by
  unfold inEdgeArgs
  dsimp only
  rw [Id.forIn_array_eq_foldl (g := fun b acc => inEdgeArgsBlockStep acc b) (h := by
    intro b acc
    rw [Id.forIn_eq_foldl (g := fun e acc => inEdgeArgsEdgeStep acc e) (h := by
      intro e acc
      rfl)]
    rfl)]
  rfl

omit model in
@[simp] theorem inEdgeArgsEdgeStep_size (acc : Array (List (List ValId))) (e : Edge) :
    (inEdgeArgsEdgeStep acc e).size = acc.size := by
  simp [inEdgeArgsEdgeStep]

omit model in
@[simp] theorem inEdgeArgsEdgeFold_size (acc : Array (List (List ValId))) (es : List Edge) :
    (es.foldl inEdgeArgsEdgeStep acc).size = acc.size := by
  induction es generalizing acc with
  | nil => rfl
  | cons e es ih => simp only [List.foldl_cons, ih, inEdgeArgsEdgeStep_size]

omit model in
@[simp] theorem inEdgeArgsBlockStep_size (acc : Array (List (List ValId))) (b : Block) :
    (inEdgeArgsBlockStep acc b).size = acc.size := by
  unfold inEdgeArgsBlockStep
  induction b.term.edges generalizing acc with
  | nil => rfl
  | cons e es ih => simp only [List.foldl_cons, ih, inEdgeArgsEdgeStep_size]

omit model in
theorem inEdgeArgsEdgeStep_mem {acc : Array (List (List ValId))} {t : BlockId}
    (ht : t < acc.size) {xs : List ValId} (hx : xs ∈ acc[t]!) (e : Edge) :
    xs ∈ (inEdgeArgsEdgeStep acc e)[t]! := by
  have hx' : xs ∈ acc[t] := by
    simpa [Array.getElem!_eq_getD, Array.getElem?_eq_getElem ht] using hx
  by_cases het : e.target = t
  · subst t
    simp [inEdgeArgsEdgeStep, ht, hx']
  · simpa [inEdgeArgsEdgeStep, het, ht] using hx'

omit model in
theorem inEdgeArgsEdgeStep_self {acc : Array (List (List ValId))} {e : Edge}
    (he : e.target < acc.size) :
    e.args ∈ (inEdgeArgsEdgeStep acc e)[e.target]! := by
  simp [inEdgeArgsEdgeStep, he, Array.getElem!_eq_getD]

omit model in
theorem inEdgeArgsEdgeFold_mem {acc : Array (List (List ValId))} {t : BlockId}
    (ht : t < acc.size) {xs : List ValId} (hx : xs ∈ acc[t]!) (es : List Edge) :
    xs ∈ (es.foldl inEdgeArgsEdgeStep acc)[t]! := by
  induction es generalizing acc with
  | nil => exact hx
  | cons e es ih =>
      rw [List.foldl_cons]
      exact ih (by simpa using ht) (inEdgeArgsEdgeStep_mem ht hx e)

omit model in
theorem inEdgeArgsEdgeFold_of_mem {acc : Array (List (List ValId))} {e : Edge}
    (helt : e.target < acc.size) {es : List Edge} (he : e ∈ es) :
    e.args ∈ (es.foldl inEdgeArgsEdgeStep acc)[e.target]! := by
  induction es generalizing acc with
  | nil => simp at he
  | cons e' es ih =>
      rw [List.foldl_cons]
      rcases List.mem_cons.mp he with rfl | he
      · exact inEdgeArgsEdgeFold_mem (by simpa using helt)
          (inEdgeArgsEdgeStep_self helt) es
      · exact ih (by simpa using helt) he

omit model in
theorem inEdgeArgsBlockFold_mem {acc : Array (List (List ValId))} {t : BlockId}
    (ht : t < acc.size) {xs : List ValId} (hx : xs ∈ acc[t]!) (bs : List Block) :
    xs ∈ (bs.foldl inEdgeArgsBlockStep acc)[t]! := by
  induction bs generalizing acc with
  | nil => exact hx
  | cons b bs ih =>
      rw [List.foldl_cons]
      exact ih (by simpa using ht)
        (inEdgeArgsEdgeFold_mem ht hx b.term.edges)

omit model in
theorem inEdgeArgsBlockFold_of_mem {acc : Array (List (List ValId))}
    {b : Block} {e : Edge} (helt : e.target < acc.size) {bs : List Block}
    (hb : b ∈ bs) (he : e ∈ b.term.edges) :
    e.args ∈ (bs.foldl inEdgeArgsBlockStep acc)[e.target]! := by
  induction bs generalizing acc with
  | nil => simp at hb
  | cons b' bs ih =>
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hb with rfl | hb
      · exact inEdgeArgsBlockFold_mem (by simpa using helt)
          (inEdgeArgsEdgeFold_of_mem helt he) bs
      · exact ih (by
          rw [inEdgeArgsBlockStep_size]
          exact helt) hb

omit model in
theorem inEdgeArgs_mem_of_edge {f : Func} {b : Block} (hb : b ∈ f.blocks.toList)
    {e : Edge} (he : e ∈ b.term.edges) (het : e.target < f.blocks.size) :
    e.args ∈ (inEdgeArgs f)[e.target]! := by
  rw [inEdgeArgs_eq_fold]
  exact inEdgeArgsBlockFold_of_mem (by simpa using het) hb he

abbrev TrivialCandidate := BlockId × Nat × ValId × ValId
abbrev FindTrivialState := MProd (Option (Option TrivialCandidate)) PUnit

def findTrivialParamStep (f : Func) (bi i : Nat) (_ : FindTrivialState) :
    ForInStep FindTrivialState :=
  let argLists := (inEdgeArgs f)[bi]!
  let p := f.blocks[bi]!.params[i]!
  let ith := argLists.filterMap (·[i]?)
  if ith.length == argLists.length then
    match (ith.filter (· != p)).eraseDups with
    | [v] =>
        let selfOnly := (List.range f.blocks.size).all fun j =>
          j == bi || (f.blocks[j]!.term.edges.all fun e =>
            e.target != bi || e.args[i]? != some p)
        if selfOnly then .done ⟨some (some (bi, i, p, v)), PUnit.unit⟩
        else .yield ⟨none, PUnit.unit⟩
    | _ => .yield ⟨none, PUnit.unit⟩
  else .yield ⟨none, PUnit.unit⟩

def findTrivialBlockStep (f : Func) (bi : Nat) (_ : FindTrivialState) :
    ForInStep FindTrivialState :=
  if bi != f.entry then
    let argLists := (inEdgeArgs f)[bi]!
    if !argLists.isEmpty then
      let r := loopWith (findTrivialParamStep f bi)
        (List.range' 0 f.blocks[bi]!.params.length 1) ⟨none, PUnit.unit⟩
      match r.1 with
      | none => .yield ⟨none, PUnit.unit⟩
      | some a => .done ⟨some a, PUnit.unit⟩
    else .yield ⟨none, PUnit.unit⟩
  else .yield ⟨none, PUnit.unit⟩

omit model in
theorem findTrivialParam_eq_loop (f : Func) :
    findTrivialParam f =
      (loopWith (findTrivialBlockStep f)
        (List.range' 0 f.blocks.size 1) ⟨none, PUnit.unit⟩).1.getD none := by
  unfold findTrivialParam
  dsimp only
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rw [Id.forIn_eq_loopWith (g := findTrivialBlockStep f) (h := by
    intro bi r
    unfold findTrivialBlockStep
    split
    · split
      · rw [Id.forIn_eq_loopWith (g := findTrivialParamStep f bi) (h := by
          intro i s
          simp only [LawfulMonad.pure_bind]
          rfl)]
        simp_all [Id.run, bind, pure]
        split <;> simp_all
      · simp_all [Id.run, bind, pure]
    · simp_all [Id.run, bind, pure])]
  simp [Id.run, bind, pure, Option.getD]
  split <;> simp_all

omit model in
theorem loopWith_findTrivial_done {α : Type} {g : α → FindTrivialState →
    ForInStep FindTrivialState} {xs : List α} {c : TrivialCandidate}
    (hg : ∀ a, g a ⟨none, PUnit.unit⟩ = .yield ⟨none, PUnit.unit⟩ ∨
      ∃ c, g a ⟨none, PUnit.unit⟩ = .done ⟨some (some c), PUnit.unit⟩)
    (h : (loopWith g xs ⟨none, PUnit.unit⟩).1 = some (some c)) :
    ∃ a ∈ xs, g a ⟨none, PUnit.unit⟩ =
      .done ⟨some (some c), PUnit.unit⟩ := by
  induction xs with
  | nil => simp [loopWith] at h
  | cons a as ih =>
      rw [loopWith_cons] at h
      rcases hg a with ha | ⟨c', ha⟩
      · rw [ha] at h
        obtain ⟨b, hb, hdone⟩ := ih h
        exact ⟨b, by simp [hb], hdone⟩
      · rw [ha] at h
        have hc : c' = c := by simpa using h
        subst c'
        exact ⟨a, by simp, ha⟩

omit model in
theorem loopWith_findTrivial_cases {α : Type} {g : α → FindTrivialState →
    ForInStep FindTrivialState} {xs : List α}
    (hg : ∀ a, g a ⟨none, PUnit.unit⟩ = .yield ⟨none, PUnit.unit⟩ ∨
      ∃ c, g a ⟨none, PUnit.unit⟩ = .done ⟨some (some c), PUnit.unit⟩) :
    (loopWith g xs ⟨none, PUnit.unit⟩).1 = none ∨
      ∃ c, (loopWith g xs ⟨none, PUnit.unit⟩).1 = some (some c) := by
  induction xs with
  | nil => exact Or.inl rfl
  | cons a as ih =>
      rw [loopWith_cons]
      rcases hg a with ha | ⟨c, ha⟩
      · rw [ha]
        exact ih
      · rw [ha]
        exact Or.inr ⟨c, rfl⟩

omit model in
theorem findTrivialParamStep_cases (f : Func) (bi i : Nat) :
    findTrivialParamStep f bi i ⟨none, PUnit.unit⟩ =
        .yield ⟨none, PUnit.unit⟩ ∨
      ∃ c, findTrivialParamStep f bi i ⟨none, PUnit.unit⟩ =
        .done ⟨some (some c), PUnit.unit⟩ := by
  unfold findTrivialParamStep
  dsimp only
  split
  · split
    · split
      · right
        exact ⟨_, rfl⟩
      · left
        rfl
    · left
      rfl
  · left
    rfl

omit model in
theorem findTrivialBlockStep_cases (f : Func) (bi : Nat) :
    findTrivialBlockStep f bi ⟨none, PUnit.unit⟩ =
        .yield ⟨none, PUnit.unit⟩ ∨
      ∃ c, findTrivialBlockStep f bi ⟨none, PUnit.unit⟩ =
        .done ⟨some (some c), PUnit.unit⟩ := by
  unfold findTrivialBlockStep
  dsimp only
  split
  · split
    · rcases loopWith_findTrivial_cases
          (fun i => findTrivialParamStep_cases f bi i)
          (xs := List.range' 0 f.blocks[bi]!.params.length 1) with hr | ⟨c, hr⟩
      · left
        simp [hr]
      · right
        exact ⟨c, by simp [hr]⟩
    · left
      rfl
  · left
    rfl

omit model in
theorem findTrivialParam_inv {f : Func} {bi i p v : Nat}
    (h : findTrivialParam f = some (bi, i, p, v)) :
    bi < f.blocks.size ∧ bi ≠ f.entry ∧
    i < (f.blocks[bi]!).params.length ∧ (f.blocks[bi]!).params[i]! = p ∧
    let argLists := (inEdgeArgs f)[bi]!
    argLists ≠ [] ∧
    (argLists.filterMap (·[i]?)).length = argLists.length ∧
    ((argLists.filterMap (·[i]?)).filter (· != p)).eraseDups = [v] ∧
    (List.range f.blocks.size).all (fun j =>
      j == bi || (f.blocks[j]!.term.edges.all fun e =>
        e.target != bi || e.args[i]? != some p)) = true := by
  rw [findTrivialParam_eq_loop] at h
  have hout :
      (loopWith (findTrivialBlockStep f) (List.range' 0 f.blocks.size 1)
        ⟨none, PUnit.unit⟩).1 = some (some (bi, i, p, v)) := by
    cases hr : (loopWith (findTrivialBlockStep f) (List.range' 0 f.blocks.size 1)
        ⟨none, PUnit.unit⟩).1 with
    | none => simp [hr, Option.getD] at h
    | some r =>
        cases r with
        | none => simp [hr, Option.getD] at h
        | some c =>
            have hc : c = (bi, i, p, v) := by simpa [hr, Option.getD] using h
            simpa [hc] using hr
  obtain ⟨bi', hbi'mem, hbi'step⟩ := loopWith_findTrivial_done
    (fun j => findTrivialBlockStep_cases f j) hout
  unfold findTrivialBlockStep at hbi'step
  dsimp only at hbi'step
  split at hbi'step
  · split at hbi'step
    · split at hbi'step
      · contradiction
      · rename_i _ a hloop
        have ha : a = some (bi, i, p, v) := by simpa using hbi'step
        rw [ha] at hloop
        obtain ⟨i', hi'mem, hi'step⟩ := loopWith_findTrivial_done
          (fun j => findTrivialParamStep_cases f bi' j) hloop
        unfold findTrivialParamStep at hi'step
        dsimp only at hi'step
        split at hi'step
        · split at hi'step
          · split at hi'step
            · rename_i _ replacement hsingle hself
              have hcand :
                  (bi', i', f.blocks[bi']!.params[i']!, replacement) =
                    (bi, i, p, v) := by
                simpa using hi'step
              obtain ⟨rfl, rfl, rfl, rfl⟩ := hcand
              simp_all
            · cases hi'step
          · cases hi'step
        · cases hi'step
    · cases hbi'step
  · cases hbi'step

omit model in
theorem filterMap_length_eq_of_mem {α β : Type} {g : α → Option β} {xs : List α}
    (hlen : (xs.filterMap g).length = xs.length) {x : α} (hx : x ∈ xs) :
    ∃ y, g x = some y := by
  have hs := List.filterMap_length_eq_length.mp hlen x hx
  cases hg : g x with
  | none => simp [hg] at hs
  | some y => exact ⟨y, rfl⟩

omit model in
/-- Edge-level form of `findTrivialParam_inv`.  Every incoming edge carries
position `i`; its value is `p` or the unique non-self value `v`; and a `p`
argument can only originate in the selected block itself. -/
theorem findTrivialParam_edge {f : Func} {bi i p v : Nat}
    (hfind : findTrivialParam f = some (bi, i, p, v))
    {bj : BlockId} {b : Block} (hb : f.blocks[bj]? = some b)
    {e : Edge} (he : e ∈ b.term.edges) (het : e.target = bi) :
    ∃ a, e.args[i]? = some a ∧ (a = p ∨ a = v) ∧ (a = p → bj = bi) := by
  obtain ⟨hbi, _, _, _, hnonempty, hcoverage, hsingle, hself⟩ :=
    findTrivialParam_inv hfind
  have hbj : bj < f.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  have hbmem : b ∈ f.blocks.toList := by
    exact List.mem_iff_getElem.mpr ⟨bj, by simpa using hbj,
      by simpa using (Array.getElem?_eq_some_iff.mp hb).2⟩
  have heargs : e.args ∈ (inEdgeArgs f)[bi]! := by
    rw [← het]
    exact inEdgeArgs_mem_of_edge hbmem he (het ▸ hbi)
  obtain ⟨a, ha⟩ := filterMap_length_eq_of_mem hcoverage heargs
  refine ⟨a, ha, ?_, ?_⟩
  · by_cases hap : a = p
    · exact Or.inl hap
    · right
      have haith : a ∈ ((inEdgeArgs f)[bi]!).filterMap (·[i]?) :=
        List.mem_filterMap.mpr ⟨e.args, heargs, ha⟩
      have hafilter : a ∈ (((inEdgeArgs f)[bi]!).filterMap (·[i]?)).filter (· != p) := by
        exact List.mem_filter.mpr ⟨haith, by simpa [hap]⟩
      have haerase : a ∈ ((((inEdgeArgs f)[bi]!).filterMap (·[i]?)).filter
          (· != p)).eraseDups := List.mem_eraseDups.mpr hafilter
      rw [hsingle] at haerase
      simpa using haerase
  · intro hap
    have hjall := List.all_eq_true.mp hself bj (List.mem_range.mpr hbj)
    simp only [Bool.or_eq_true, beq_iff_eq] at hjall
    rcases hjall with hj | hj
    · exact hj
    · have hbang : f.blocks[bj]! = b := by
        simp [Array.getElem!_eq_getD, hb]
      rw [hbang] at hj
      have heall := List.all_eq_true.mp hj e he
      simp only [Bool.or_eq_true, bne_iff_ne] at heall
      rcases heall with htarget | harg
      · exact absurd het htarget
      · exact absurd (ha.trans (congrArg some hap)) harg

abbrev ElimTrivialLoopState := MProd (Option Func) Func

def elimTrivialStep (_ : Nat) (r : ElimTrivialLoopState) :
    ForInStep ElimTrivialLoopState :=
  match findTrivialParam r.2 with
  | none => .done ⟨some r.2, r.2⟩
  | some (bi, i, p, v) =>
      .yield ⟨none, substFunc ((∅ : Subst).insert p v) (removeParam r.2 bi i)⟩

def elimTrivialFuel (f : Func) : Nat :=
  f.blocks.foldl (fun n b => n + b.params.length) 0 + 1

omit model in
theorem elimTrivialParams_eq_loop (f : Func) :
    elimTrivialParams f =
      let r := loopWith elimTrivialStep
        (List.range' 0 (elimTrivialFuel f) 1) ⟨none, f⟩
      r.1.getD r.2 := by
  unfold elimTrivialParams elimTrivialFuel
  dsimp only
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rw [Id.forIn_eq_loopWith (g := elimTrivialStep)
    (h := by
      intro _ r
      cases hfind : findTrivialParam r.2 with
      | none => simp [elimTrivialStep, hfind]
      | some q =>
          obtain ⟨bi, i, p, v⟩ := q
          simp [elimTrivialStep, hfind])]
  simp [Id.run, bind, pure, Option.getD]
  cases h : (loopWith elimTrivialStep
      (List.range' 0 (f.blocks.foldl (fun n b => n + b.params.length) 0 + 1))
      ⟨none, f⟩).1 <;> simp [h]

end Passes

namespace Passes

omit model in
@[simp] theorem substV_single (p v x : ValId) :
    substV ((∅ : Subst).insert p v) x = if x = p then v else x := by
  by_cases h : x = p
  · subst x
    simp [substV, Std.HashMap.getD_eq_getD_getElem?]
  · unfold substV
    simp only [Std.HashMap.getD_eq_getD_getElem?]
    rw [Std.HashMap.getElem?_insert]
    simp [h, Ne.symm h]

omit model in
theorem removeParam_blocks_get {f : Func} {bi i j : Nat} {b : Block}
    (hb : f.blocks[j]? = some b) :
    (removeParam f bi i).blocks[j]? = some (removedBlock bi i j b) := by
  simp only [removeParam, Array.getElem?_mapIdx, hb, Option.map_some]
  simp only [beq_iff_eq, removedBlock]

omit model in
theorem elimStep_blocks_get {f : Func} {bi i p v j : Nat} {b : Block}
    (hb : f.blocks[j]? = some b) :
    (substFunc ((∅ : Subst).insert p v) (removeParam f bi i)).blocks[j]? =
      some (substBlock ((∅ : Subst).insert p v) (removedBlock bi i j b)) := by
  simp only [substFunc, Array.getElem?_map, removeParam_blocks_get hb, Option.map_some]

omit model in
theorem removedBlock_use {bi i j : Nat} {b : Block} {x : ValId}
    (hx : x ∈ ToAsm.blockUses (removedBlock bi i j b)) :
    x ∈ ToAsm.blockUses b := by
  have finish (hx : x ∈ ToAsm.blockUses
      { b with term := mapEdges (fun e =>
        if e.target = bi then { e with args := e.args.eraseIdx i } else e) b.term }) :
      x ∈ ToAsm.blockUses b := by
    rw [ToAsm.mem_blockUses] at hx ⊢
    rcases hx with hx | hx
    · exact Or.inl hx
    · refine Or.inr (mapEdges_uses_sub ?_ _ hx)
      intro e y hy
      split at hy
      · exact List.mem_of_mem_eraseIdx hy
      · exact hy
  apply finish
  rw [ToAsm.mem_blockUses] at hx ⊢
  by_cases hj : j = bi <;> simpa [removedBlock, hj] using hx

omit model in
theorem removedBlock_edge {bi i j : Nat} {b : Block} {e : Edge}
    (he : e ∈ (removedBlock bi i j b).term.edges) :
    ∃ e0 ∈ b.term.edges, e0.target = e.target := by
  have he' : e ∈ (mapEdges (fun e =>
      if e.target = bi then { e with args := e.args.eraseIdx i } else e) b.term).edges := by
    by_cases hj : j = bi <;> simpa [removedBlock, hj] using he
  obtain ⟨e0, he0, hmap⟩ := mapEdges_edges _ he'
  refine ⟨e0, he0, ?_⟩
  rw [← hmap]
  split <;> rfl

omit model in
theorem mem_removedBlock_defs {bi i j : Nat} {b : Block} {p x : ValId}
    (hp : b.params[i]? = some p) (hx : x ∈ ToAsm.blockDefs b) (hxp : x ≠ p) :
    x ∈ ToAsm.blockDefs (removedBlock bi i j b) := by
  rw [ToAsm.mem_blockDefs] at hx ⊢
  rcases hx with hx | hx
  · left
    by_cases hj : j = bi
    · simp only [removedBlock, hj, if_true]
      rw [List.mem_eraseIdx_iff_getElem?]
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hx
      refine ⟨k, ?_, hk⟩
      intro hki
      subst k
      exact hxp (Option.some.inj (hk.symm.trans hp))
    · simpa [removedBlock, hj] using hx
  · right
    by_cases hj : j = bi <;> simpa [removedBlock, hj] using hx

omit model in
theorem substBlock_use {σ : Subst} {b : Block} {x : ValId}
    (hx : x ∈ ToAsm.blockUses (substBlock σ b)) :
    ∃ y ∈ ToAsm.blockUses b, substV σ y = x := by
  rw [ToAsm.mem_blockUses] at hx
  rcases hx with hx | hx
  · simp only [substBlock, List.mem_flatMap] at hx
    obtain ⟨ins, hins, hxu⟩ := hx
    obtain ⟨ins0, hins0, rfl⟩ := List.mem_map.mp hins
    obtain ⟨y, hy, rfl⟩ := substInstr_use hxu
    exact ⟨y, ToAsm.mem_blockUses.mpr
      (Or.inl (List.mem_flatMap.mpr ⟨ins0, hins0, hy⟩)), rfl⟩
  · obtain ⟨y, hy, rfl⟩ := substTerm_use hx
    exact ⟨y, ToAsm.mem_blockUses.mpr (Or.inr hy), rfl⟩

omit model in
theorem mem_substBlock_defs {σ : Subst} {b : Block} {x : ValId}
    (hx : x ∈ ToAsm.blockDefs b) :
    x ∈ ToAsm.blockDefs (substBlock σ b) := by
  rw [ToAsm.mem_blockDefs] at hx ⊢
  rcases hx with hx | hx
  · exact Or.inl hx
  · right
    obtain ⟨ins, hins, hxd⟩ := List.mem_flatMap.mp hx
    exact List.mem_flatMap.mpr
      ⟨substInstr σ ins, List.mem_map.mpr ⟨ins, hins, rfl⟩, by simpa using hxd⟩

omit model in
theorem block_def_index_unique {f : Func} (hnd : f.allDefs.Nodup)
    {i j : Nat} {b c : Block} (hb : f.blocks[i]? = some b)
    (hc : f.blocks[j]? = some c) {x : ValId}
    (hxb : x ∈ ToAsm.blockDefs b) (hxc : x ∈ ToAsm.blockDefs c) : i = j := by
  have hi : i < f.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  have hj : j < f.blocks.size := (Array.getElem?_eq_some_iff.mp hc).1
  have hbget : f.blocks.toList[i] = b := by
    simpa using (Array.getElem?_eq_some_iff.mp hb).2
  have hcget : f.blocks.toList[j] = c := by
    simpa using (Array.getElem?_eq_some_iff.mp hc).2
  have hflat : (f.blocks.toList.flatMap blockAllDefs).Nodup :=
    (List.nodup_append.mp hnd).2.1
  have hpw := (List.nodup_flatMap.mp hflat).2
  by_contra hne
  have hxb' : x ∈ blockAllDefs b := by
    simpa [blockAllDefs, ToAsm.mem_blockDefs] using hxb
  have hxc' : x ∈ blockAllDefs c := by
    simpa [blockAllDefs, ToAsm.mem_blockDefs] using hxc
  rcases Nat.lt_or_gt_of_ne hne with hij | hji
  · have hd := (List.pairwise_iff_getElem.mp hpw i j (by simpa using hi)
      (by simpa using hj) hij)
    rw [hbget, hcget] at hd
    exact (List.disjoint_left.mp hd hxb') hxc'
  · have hd := (List.pairwise_iff_getElem.mp hpw j i (by simpa using hj)
      (by simpa using hi) hji)
    rw [hcget, hbget] at hd
    exact (List.disjoint_left.mp hd hxc') hxb'

omit model in
theorem blockAllDefs_substBlock (σ : Subst) (b : Block) :
    blockAllDefs (substBlock σ b) = blockAllDefs b := by
  simp only [blockAllDefs, substBlock]
  congr 1
  induction b.instrs with
  | nil => rfl
  | cons ins is ih => simp [ih]

omit model in
theorem blockAllDefs_removedBlock (bi i j : Nat) (b : Block) :
    List.Sublist (blockAllDefs (removedBlock bi i j b)) (blockAllDefs b) := by
  by_cases hj : j = bi
  · simp only [blockAllDefs, removedBlock, hj, if_true]
    exact (List.eraseIdx_sublist b.params i).append_right _
  · simpa [blockAllDefs, removedBlock, hj] using
      (List.Sublist.refl (blockAllDefs b))

omit model in
theorem flatMap_mapIdx_removedBlock (bi i off : Nat) : ∀ bs : List Block,
    List.Sublist
      ((bs.mapIdx fun j b => removedBlock bi i (off + j) b).flatMap blockAllDefs)
      (bs.flatMap blockAllDefs)
  | [] => List.Sublist.refl []
  | b :: bs => by
      simp only [List.mapIdx_cons, List.flatMap_cons]
      exact (blockAllDefs_removedBlock bi i off b).append
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          flatMap_mapIdx_removedBlock bi i (off + 1) bs)

omit model in
theorem removeParam_allDefs_sublist (f : Func) (bi i : Nat) :
    List.Sublist (removeParam f bi i).allDefs f.allDefs := by
  unfold Func.allDefs removeParam
  apply List.Sublist.append (.refl _)
  rw [Array.toList_mapIdx]
  simpa [removedBlock, beq_iff_eq] using
    flatMap_mapIdx_removedBlock bi i 0 f.blocks.toList

omit model in
theorem substFunc_allDefs (σ : Subst) (f : Func) :
    (substFunc σ f).allDefs = f.allDefs := by
  unfold Func.allDefs substFunc
  simp only [Array.toList_map, List.flatMap_map]
  simp_rw [blockAllDefs_substBlock]

end Passes

/-! ### Block dominance and the stale-zone cut -/

/-- `d` dominates the entry of block `i`: every entry-rooted path to `i`
has already visited `d` (with the reflexive `d = i` case explicit). -/
def BlockDom (f : Func) (d i : BlockId) : Prop :=
  ∀ path, EntryPath f path i → d = i ∨ d ∈ path

/-- Strict block dominance, as supplied by a value on every incoming edge. -/
def StrictBlockDom (f : Func) (d i : BlockId) : Prop :=
  ∀ path, EntryPath f path i → d ∈ path

theorem BlockDom.refl (f : Func) (i : BlockId) : BlockDom f i i := by
  intro path hp
  exact Or.inl rfl

theorem BlockDom.pred {f : Func} {d i : BlockId} (h : BlockDom f d i)
    {path : List BlockId} {j : BlockId} {b : Block} (hp : EntryPath f path j)
    (hb : f.blocks[j]? = some b) {e : Edge} (he : e ∈ b.term.edges)
    (het : e.target = i) (hdi : d ≠ i) : BlockDom f d j := by
  intro pre hpre
  have hnext : EntryPath f (pre ++ [j]) i := by
    rw [← het]
    exact .edge hpre hb he
  rcases h (pre ++ [j]) hnext with hbad | hd
  · exact False.elim (hdi hbad)
  · rw [List.mem_append] at hd
    rcases hd with hd | hd
    · exact Or.inr hd
    · exact Or.inl (by simpa using hd)

/-- A block in an `EntryPath` predecessor list is reached by a strictly
shorter prefix. -/
theorem EntryPath.prefix_of_mem {f : Func} {path : List BlockId} {i j : BlockId}
    (hp : EntryPath f path i) (hj : j ∈ path) :
    ∃ pre, EntryPath f pre j ∧ pre.length < path.length ∧
      ∀ x, x ∈ pre → x ∈ path := by
  induction hp with
  | entry => simp at hj
  | @edge path i b e hp hb he ih =>
      rw [List.mem_append] at hj
      rcases hj with hj | hj
      · obtain ⟨pre, hpre, hlen, hsub⟩ := ih hj
        refine ⟨pre, hpre, ?_, fun x hx => List.mem_append_left _ (hsub x hx)⟩
        simp only [List.length_append, List.length_singleton]
        omega
      · have hji : j = i := by simpa using hj
        subst j
        refine ⟨path, hp, ?_, fun x hx => List.mem_append_left _ hx⟩
        simp

/-- Every reachable block has a path ending at its first visit. -/
theorem EntryPath.first_visit {f : Func} {path : List BlockId} {i : BlockId}
    (hp : EntryPath f path i) :
    ∃ pre, EntryPath f pre i ∧ i ∉ pre := by
  by_cases hi : i ∈ path
  · obtain ⟨pre, hpre, hlen, -⟩ := hp.prefix_of_mem hi
    exact hpre.first_visit
  · exact ⟨path, hp, hi⟩
termination_by path.length
decreasing_by exact hlen

/-- A strict dominator cannot be dominated back by its target at a reachable
site. -/
theorem StrictBlockDom.not_reverse {f : Func} {d i : BlockId}
    (hs : StrictBlockDom f d i) {path : List BlockId}
    (hp : EntryPath f path d) : ¬ BlockDom f i d := by
  intro hr
  obtain ⟨pre, hpre, hdnot⟩ := hp.first_visit
  rcases hr pre hpre with hid | hi
  · subst i
    exact hdnot (hs pre hpre)
  · obtain ⟨prei, hprei, -, hsub⟩ := hpre.prefix_of_mem hi
    exact hdnot (hsub d (hs prei hprei))

/-- Under `domCheck`, the unique block defining `x` dominates every block
that reads `x`. -/
theorem blockDef_dominates_use {f : Func} {li : Array (List ValId)}
    (hnd : f.allDefs.Nodup) (hli : ToAsm.liveInSets f = some li)
    (hdom : ToAsm.Func.domCheck f = true)
    {di : BlockId} {db : Block} (hdb : f.blocks[di]? = some db)
    {x : ValId} (hxdef : x ∈ ToAsm.blockDefs db)
    {i : BlockId} {b : Block} (hb : f.blocks[i]? = some b)
    (hxuse : x ∈ ToAsm.blockUses b) : BlockDom f di i := by
  intro path hp
  by_cases hieq : di = i
  · exact Or.inl hieq
  · right
    have hxnot : x ∉ ToAsm.blockDefs b := by
      intro hxb
      exact hieq (Passes.block_def_index_unique hnd hdb hb hxdef hxb)
    have hxlive := ToAsm.liveIn_of_uses hli hb hxuse hxnot
    rcases hp.live_origin hli hdom hxlive with hparam | horigin
    · have hxflat : x ∈ f.blocks.toList.flatMap blockAllDefs := by
        apply List.mem_flatMap.mpr
        refine ⟨db, block_mem_of_getElem? hdb, ?_⟩
        simpa [blockAllDefs, ToAsm.mem_blockDefs] using hxdef
      exact False.elim ((List.nodup_append.mp hnd).2.2 x hparam x hxflat rfl)
    · obtain ⟨j, hj, c, hc, hxc⟩ := horigin
      have hji := Passes.block_def_index_unique hnd hdb hc hxdef hxc
      simpa [hji] using hj

theorem edge_arg_mem_blockUses {b : Block} {e : Edge} (he : e ∈ b.term.edges)
    {x : ValId} (hx : x ∈ e.args) : x ∈ ToAsm.blockUses b := by
  rw [ToAsm.mem_blockUses]
  right
  cases ht : b.term with
  | jump ej =>
      simp only [ht, Term.edges, List.mem_singleton] at he
      subst e
      simpa [ht, Term.uses] using hx
  | branch c et ef =>
      simp only [ht, Term.edges, List.mem_cons, List.mem_singleton,
        List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · simp [ht, Term.uses, hx]
      · simp [ht, Term.uses, hx]
  | ret xs => simp [ht, Term.edges] at he
  | halt yop as => simp [ht, Term.edges] at he

theorem instr_use_mem_blockUses {b : Block} {ins : Instr} (hi : ins ∈ b.instrs)
    {x : ValId} (hx : x ∈ ins.uses) : x ∈ ToAsm.blockUses b := by
  rw [ToAsm.mem_blockUses]
  exact Or.inl (List.mem_flatMap.mpr ⟨ins, hi, hx⟩)

theorem term_use_mem_blockUses {b : Block} {x : ValId} (hx : x ∈ b.term.uses) :
    x ∈ ToAsm.blockUses b := by
  rw [ToAsm.mem_blockUses]
  exact Or.inr hx

/-- The unique definition of a selected trivial parameter's replacement is a
strict dominator of the parameter block.  A first arrival cannot use the
allowed self value `p`; it therefore reads `v`, while later self arrivals
inherit the fact from the earlier visit. -/
theorem trivial_replacement_strict_dom {f : Func} {li : Array (List ValId)}
    (hnd : f.allDefs.Nodup) (hli : ToAsm.liveInSets f = some li)
    (hdom : ToAsm.Func.domCheck f = true)
    {bi i p v : Nat} (hfind : Passes.findTrivialParam f = some (bi, i, p, v))
    {vi : BlockId} {vb : Block} (hvb : f.blocks[vi]? = some vb)
    (hvdef : v ∈ ToAsm.blockDefs vb) : StrictBlockDom f vi bi := by
  obtain ⟨-, hbientry, -, -, -, -, -, -⟩ := Passes.findTrivialParam_inv hfind
  intro path hp
  have go : ∀ {path j}, EntryPath f path j → j = bi → vi ∈ path := by
    intro path j hp
    induction hp with
    | entry =>
        intro hentry
        exact False.elim (hbientry hentry.symm)
    | @edge path j b e hp hb he ih =>
        intro htarget
        by_cases hj : j = bi
        · have hprev := ih hj
          exact List.mem_append_left _ hprev
        · obtain ⟨a, ha, hapv, hapself⟩ :=
            Passes.findTrivialParam_edge hfind hb he htarget
          have hav : a = v := by
            rcases hapv with hap | hav
            · exact False.elim (hj (hapself hap))
            · exact hav
          have hvarg : v ∈ e.args := by
            subst a
            exact List.mem_iff_getElem?.mpr ⟨i, ha⟩
          have hvuse := edge_arg_mem_blockUses he hvarg
          rcases blockDef_dominates_use hnd hli hdom hvb hvdef hb hvuse path hp with
            hvi | hvi
          · subst j
            exact List.mem_append_right _ (by simp)
          · exact List.mem_append_left _ hvi
  exact go hp rfl

/-- Register relation for one trivial-parameter removal.  Outside `p` the
two executions are in exact lockstep.  The alias itself is required only in
the dominance region of `p`; outside that region it is the bounded stale
zone. -/
def TrivialAgree (f : Func) (bi : BlockId) (p v : ValId) (cur : BlockId)
    (R R' : Regs) : Prop :=
  (∀ x, x ≠ p → R x = R' x) ∧
  (BlockDom f bi cur → R p = R' v)

theorem TrivialAgree.getMany {f : Func} {li : Array (List ValId)}
    (hnd : f.allDefs.Nodup) (hli : ToAsm.liveInSets f = some li)
    (hdom : ToAsm.Func.domCheck f = true)
    {bi i p v cur : Nat} (hfind : Passes.findTrivialParam f = some (bi, i, p, v))
    {pb b : Block} (hpb : f.blocks[bi]? = some pb)
    (hpdef : p ∈ ToAsm.blockDefs pb) (hb : f.blocks[cur]? = some b)
    {R R' : Regs} (ha : TrivialAgree f bi p v cur R R')
    {xs : List ValId} (hxs : ∀ x ∈ xs, x ∈ ToAsm.blockUses b)
    {vals : List U256} (hg : R.getMany xs = some vals) :
    R'.getMany (Passes.substVs ((∅ : Passes.Subst).insert p v) xs) = some vals := by
  apply Regs.getMany_substVs (hget := hg)
  intro x hx
  rw [Passes.substV_single]
  by_cases hxp : x = p
  · subst x
    simp only [if_true]
    exact ha.2 (blockDef_dominates_use hnd hli hdom hpb hpdef hb (hxs p hx))
  · simp [hxp, ha.1 x hxp]

theorem TrivialAgree.get {f : Func} {li : Array (List ValId)}
    (hnd : f.allDefs.Nodup) (hli : ToAsm.liveInSets f = some li)
    (hdom : ToAsm.Func.domCheck f = true)
    {bi p v cur : Nat} {pb b : Block} (hpb : f.blocks[bi]? = some pb)
    (hpdef : p ∈ ToAsm.blockDefs pb) (hb : f.blocks[cur]? = some b)
    {R R' : Regs} (ha : TrivialAgree f bi p v cur R R')
    {x : ValId} (hxuse : x ∈ ToAsm.blockUses b) {w : U256}
    (hx : R x = some w) :
    R' (Passes.substV ((∅ : Passes.Subst).insert p v) x) = some w := by
  rw [Passes.substV_single]
  by_cases hxp : x = p
  · subst x
    simp only [if_true]
    rw [← ha.2 (blockDef_dominates_use hnd hli hdom hpb hpdef hb hxuse)]
    exact hx
  · simp [hxp, ← ha.1 x hxp, hx]

/-- Equal bindings preserve `TrivialAgree`.  If the instruction redefines
the replacement `v`, its block strictly dominates `bi`; hence it lies outside
`p`'s dominance region and the alias clause is intentionally dormant. -/
theorem TrivialAgree.setMany_instr {f : Func} {li : Array (List ValId)}
    (hnd : f.allDefs.Nodup) (hli : ToAsm.liveInSets f = some li)
    (hdom : ToAsm.Func.domCheck f = true)
    {bi k p v cur : Nat} (hfind : Passes.findTrivialParam f = some (bi, k, p, v))
    {pb b : Block} (hpb : f.blocks[bi]? = some pb) (hp : p ∈ pb.params)
    (hb : f.blocks[cur]? = some b) {path : List BlockId}
    (hpath : EntryPath f path cur)
    {ins : Instr} (hins : ins ∈ b.instrs)
    {R R' : Regs} (ha : TrivialAgree f bi p v cur R R')
    (vals : List U256) :
    TrivialAgree f bi p v cur (R.setMany ins.defs vals)
      (R'.setMany ins.defs vals) := by
  have hpnot : p ∉ ins.defs := by
    intro hpd
    exact param_not_instr_def hnd (block_mem_of_getElem? hpb)
      (block_mem_of_getElem? hb) hins hp hpd
  refine ⟨?_, ?_⟩
  · intro x hxp
    exact Regs.setMany_congr (S := fun y => y ≠ p) ha.1 ins.defs vals x hxp
  · intro hcur
    have hvnot : v ∉ ins.defs := by
      intro hvd
      have hvblock : v ∈ ToAsm.blockDefs b := by
        rw [ToAsm.mem_blockDefs]
        exact Or.inr (List.mem_flatMap.mpr ⟨ins, hins, hvd⟩)
      have hs := trivial_replacement_strict_dom hnd hli hdom hfind hb hvblock
      exact (hs.not_reverse hpath) hcur
    rw [Regs.setMany_of_not_mem R ins.defs vals hpnot,
      Regs.setMany_of_not_mem R' ins.defs vals hvnot]
    exact ha.2 hcur

theorem Regs.getMany_eraseIdx {R : Regs} {xs : List ValId} {vals : List U256}
    (hg : R.getMany xs = some vals) (i : Nat) :
    R.getMany (xs.eraseIdx i) = some (vals.eraseIdx i) := by
  induction xs generalizing vals i with
  | nil =>
      simp only [Regs.getMany_nil, Option.some.injEq] at hg
      subst vals
      simp
  | cons x xs ih =>
      rw [Regs.getMany_cons] at hg
      cases hx : R x with
      | none => simp [hx] at hg
      | some w =>
          cases ht : R.getMany xs with
          | none => simp [hx, ht] at hg
          | some ws =>
              simp only [hx, ht, Option.bind_some, Option.map_some,
                Option.some.injEq] at hg
              subst vals
              cases i with
              | zero => exact ht
              | succ i =>
                  simp only [List.eraseIdx]
                  simpa [Regs.getMany_cons, hx] using ih ht i

/-- Removing the same parameter/value position preserves every binding except
the removed parameter. -/
theorem Regs.setMany_eraseIdx_agree {R R' : Regs} {ps : List ValId}
    {vals : List U256} (hnd : ps.Nodup) (hlen : vals.length = ps.length)
    {i : Nat} {p : ValId} (hp : ps[i]? = some p)
    (ha : ∀ x, x ≠ p → R x = R' x) :
    ∀ x, x ≠ p →
      (R.setMany ps vals) x =
        (R'.setMany (ps.eraseIdx i) (vals.eraseIdx i)) x := by
  induction ps generalizing R R' vals i with
  | nil => simp at hp
  | cons q qs ih =>
      cases vals with
      | nil => simp at hlen
      | cons w ws =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          rw [List.nodup_cons] at hnd
          cases i with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hp
              subst q
              intro x hxp
              simp only [List.eraseIdx_zero, Regs.setMany_cons]
              apply Regs.setMany_congr (S := fun y => y ≠ p) _ qs ws x hxp
              intro y hyp
              rw [Regs.set_other _ _ hyp]
              exact ha y hyp
          | succ i =>
              simp only [List.getElem?_cons_succ] at hp
              have hqp : q ≠ p := by
                intro heq
                subst q
                exact hnd.1 (List.mem_iff_getElem?.mpr ⟨i, hp⟩)
              simp only [List.eraseIdx, Regs.setMany_cons]
              exact ih hnd.2 hlen hp
                (Regs.set_congr (S := fun y => y ≠ p) ha q w)

theorem mem_zip_of_getElem?_eq {ps : List ValId} {xs : List ValId}
    {i : Nat} {p a : ValId} (hp : ps[i]? = some p) (ha : xs[i]? = some a) :
    (p, a) ∈ ps.zip xs := by
  induction i generalizing ps xs with
  | zero =>
      cases ps <;> cases xs <;> simp_all
  | succ i ih =>
      cases ps <;> cases xs <;> simp_all [ih]

theorem blockParams_nodup_of_defs {f : Func} (hnd : f.allDefs.Nodup)
    {bi : BlockId} {b : Block} (hb : f.blocks[bi]? = some b) : b.params.Nodup := by
  have hbmem : b ∈ f.blocks.toList := block_mem_of_getElem? hb
  rw [List.nodup_iff_count_le_one]
  intro d
  have hall := List.nodup_iff_count_le_one.mp hnd d
  rw [allDefs_eq, List.count_append] at hall
  have hblock := count_le_count_flatMap
    (g := fun b : Block => blockAllDefs b) (d := d) hbmem
  change (b.params ++ b.instrs.flatMap Instr.defs).count d ≤
    (f.blocks.toList.flatMap blockAllDefs).count d at hblock
  rw [List.count_append] at hblock
  omega

namespace Passes

def elimEdge (bi i : Nat) (e : Edge) : Edge :=
  if e.target = bi then { e with args := e.args.eraseIdx i } else e

@[simp] theorem elimEdge_target (bi i : Nat) (e : Edge) :
    (elimEdge bi i e).target = e.target := by
  unfold elimEdge
  split <;> rfl

def elimTerm (bi i : Nat) (t : Term) : Term := mapEdges (elimEdge bi i) t

def elimRest (bi i : Nat) (σ : Subst) (r : Rest) : Rest :=
  ⟨r.instrs.map (substInstr σ), substTerm σ (elimTerm bi i r.term)⟩

theorem elimBlock_rest (bi i j : Nat) (σ : Subst) (b : Block) :
    Rest.mk (substBlock σ (removedBlock bi i j b)).instrs
        (substBlock σ (removedBlock bi i j b)).term =
      elimRest bi i σ ⟨b.instrs, b.term⟩ := by
  have hedge : (fun e : Edge =>
      if e.target = bi then { e with args := e.args.eraseIdx i } else e) =
      elimEdge bi i := by
    funext e
    rfl
  by_cases hj : j = bi <;>
    simp [substBlock, removedBlock, elimRest, elimTerm, hj, hedge]

end Passes

theorem TrivialAgree.edge {f : Func} {li : Array (List ValId)}
    (hnd : f.allDefs.Nodup) (hli : ToAsm.liveInSets f = some li)
    (hdom : ToAsm.Func.domCheck f = true)
    {bi k p v cur : Nat} (hfind : Passes.findTrivialParam f = some (bi, k, p, v))
    {pb b tb : Block} (hpb : f.blocks[bi]? = some pb)
    (hp : p ∈ pb.params) (hpdef : p ∈ ToAsm.blockDefs pb)
    (hb : f.blocks[cur]? = some b) {path : List BlockId}
    (hpath : EntryPath f path cur)
    {e : Edge} (he : e ∈ b.term.edges) (htb : f.blocks[e.target]? = some tb)
    {R R' : Regs} (ha : TrivialAgree f bi p v cur R R')
    {vals : List U256} (hg : R.getMany e.args = some vals)
    (hlen : tb.params.length = vals.length) :
    let σ := ((∅ : Passes.Subst).insert p v)
    let e' := Passes.substEdge σ (Passes.elimEdge bi k e)
    let vals' := if e.target = bi then vals.eraseIdx k else vals
    R'.getMany e'.args = some vals' ∧
    (Passes.substBlock σ (Passes.removedBlock bi k e.target tb)).params.length =
      vals'.length ∧
    TrivialAgree f bi p v e.target
      (R.setMany tb.params vals)
      (R'.setMany
        (Passes.substBlock σ (Passes.removedBlock bi k e.target tb)).params vals') := by
  dsimp only
  have hread : R'.getMany
      (Passes.substVs ((∅ : Passes.Subst).insert p v) e.args) = some vals :=
    ha.getMany hnd hli hdom hfind hpb hpdef hb
      (fun x hx => edge_arg_mem_blockUses he hx) hg
  obtain ⟨hbi, -, hk, hpget, -, -, -, -⟩ := Passes.findTrivialParam_inv hfind
  have hvp : v ≠ p := by
    intro hvp
    subst v
    obtain ⟨_, _, _, _, _, _, hsingle, _⟩ := Passes.findTrivialParam_inv hfind
    have hm : p ∈ ((((Passes.inEdgeArgs f)[bi]!).filterMap (·[k]?)).filter
        (· != p)).eraseDups := by simpa [hsingle]
    have hm' := List.mem_filter.mp (List.mem_eraseDups.mp hm)
    simpa using hm'.2
  by_cases het : e.target = bi
  · rw [het] at htb ⊢
    have htbeq : tb = pb := Option.some.inj (htb.symm.trans hpb)
    subst tb
    have hpgetQ : pb.params[k]? = some p := by
      have hbidx : f.blocks[bi] = pb := (Array.getElem?_eq_some_iff.mp hpb).2
      have hbang : f.blocks[bi]! = pb :=
        (Passes.getElem!_eq_getElem hbi).trans hbidx
      have hk' : k < pb.params.length := by simpa [hbang] using hk
      have hpEq : pb.params[k] = p := by
        have hpget' := hpget
        rw [hbang] at hpget'
        simpa [List.getElem!_eq_getElem?_getD,
          List.getElem?_eq_getElem hk'] using hpget'
      rw [List.getElem?_eq_getElem hk', hpEq]
    have hndp := blockParams_nodup_of_defs hnd hpb
    have hargslen : e.args.length = vals.length := Regs.getMany_length hg
    have hpa : pb.params.length = e.args.length := by omega
    obtain ⟨a, haidx, hapv, -⟩ :=
      Passes.findTrivialParam_edge hfind hb he het
    have hpair : (p, a) ∈ pb.params.zip e.args :=
      mem_zip_of_getElem?_eq hpgetQ haidx
    have hkpb : k < pb.params.length := (List.getElem?_eq_some_iff.mp hpgetQ).1
    have hvnot : v ∉ pb.params := by
      intro hv
      have hvdef : v ∈ ToAsm.blockDefs pb :=
        ToAsm.mem_blockDefs.mpr (Or.inl hv)
      have hs := trivial_replacement_strict_dom hnd hli hdom hfind hpb hvdef
      have hnext0 : EntryPath f (path ++ [cur]) e.target := .edge hpath hb he
      have hnext : EntryPath f (path ++ [cur]) bi := by simpa [het] using hnext0
      exact (hs.not_reverse hnext) (BlockDom.refl f bi)
    have hgetErase := Regs.getMany_eraseIdx hread k
    have hgetOut : R'.getMany
        (Passes.substEdge ((∅ : Passes.Subst).insert p v)
          (Passes.elimEdge bi k e)).args = some (vals.eraseIdx k) := by
      simpa [Passes.elimEdge, Passes.substEdge, Passes.substVs,
        List.eraseIdx_map, het] using hgetErase
    simp only [if_pos rfl]
    refine ⟨hgetOut, ?_, ?_⟩
    · simp [Passes.substBlock, Passes.removedBlock, List.length_eraseIdx,
        hkpb, hlen]
    · refine ⟨?_, ?_⟩
      · simpa [Passes.substBlock, Passes.removedBlock] using
          Regs.setMany_eraseIdx_agree hndp (by omega) hpgetQ ha.1
      · intro _
        simp [Passes.substBlock, Passes.removedBlock]
        rw [Regs.setMany_of_not_mem R' (pb.params.eraseIdx k)
          (vals.eraseIdx k) (fun hm => hvnot (List.mem_of_mem_eraseIdx hm))]
        rw [Regs.setMany_getMany_of_mem_zip hndp hpa hg hpair]
        rcases hapv with hap | hav
        · subst a
          have hpdom := blockDef_dominates_use hnd hli hdom hpb hpdef hb
              (edge_arg_mem_blockUses he
                (List.mem_iff_getElem?.mpr ⟨k, haidx⟩))
          exact ha.2 hpdom
        · subst a
          exact ha.1 v hvp
  · have hgetOut : R'.getMany
        (Passes.substEdge ((∅ : Passes.Subst).insert p v)
          (Passes.elimEdge bi k e)).args = some vals := by
      simpa [Passes.elimEdge, het, Passes.substEdge] using hread
    simp only [het, if_false]
    have hpnot : p ∉ tb.params := by
      intro hpt
      have hptdef : p ∈ ToAsm.blockDefs tb := ToAsm.mem_blockDefs.mpr (Or.inl hpt)
      exact het (Passes.block_def_index_unique (i := bi) (j := e.target)
        hnd hpb htb hpdef hptdef).symm
    refine ⟨hgetOut, by simpa [Passes.substBlock, Passes.removedBlock, het] using hlen,
      ?_⟩
    refine ⟨?_, ?_⟩
    · simpa [Passes.substBlock, Passes.removedBlock, het] using
        Regs.setMany_congr (S := fun x => x ≠ p) ha.1 tb.params vals
    · intro htarget
      have hcur := htarget.pred hpath hb he rfl (Ne.symm het)
      have hvnot : v ∉ tb.params := by
        intro hv
        have hvdef : v ∈ ToAsm.blockDefs tb := ToAsm.mem_blockDefs.mpr (Or.inl hv)
        have hs := trivial_replacement_strict_dom hnd hli hdom hfind htb hvdef
        have hnext : EntryPath f (path ++ [cur]) e.target := .edge hpath hb he
        exact (hs.not_reverse hnext) htarget
      simp only [Passes.substBlock, Passes.removedBlock, het, if_false]
      rw [Regs.setMany_of_not_mem R tb.params vals hpnot,
        Regs.setMany_of_not_mem R' tb.params vals hvnot]
      exact ha.2 hcur

/-- Lockstep replay for one selected trivial parameter. -/
theorem elimTrivialParam_one_exec {P : Prog} {f : Func} {li : Array (List ValId)}
    (hnd : f.allDefs.Nodup) (hli : ToAsm.liveInSets f = some li)
    (hdom : ToAsm.Func.domCheck f = true)
    {bi k p v : Nat} (hfind : Passes.findTrivialParam f = some (bi, k, p, v))
    {pb : Block} (hpb : f.blocks[bi]? = some pb) (hp : p ∈ pb.params)
    (hpdef : p ∈ ToAsm.blockDefs pb)
    {R : Regs} {st : EvmState} {rest : Rest} {res : FRes}
    (h : Exec (model := model) P f R st rest res) :
    ∀ {cur : BlockId} {b : Block} {path : List BlockId},
      f.blocks[cur]? = some b → EntryPath f path cur →
      (∀ ins ∈ rest.instrs, ins ∈ b.instrs) → rest.term = b.term →
      ∀ {R' : Regs}, TrivialAgree f bi p v cur R R' →
      Exec (model := model) P
        (Passes.substFunc ((∅ : Passes.Subst).insert p v)
          (Passes.removeParam f bi k)) R' st
        (Passes.elimRest bi k ((∅ : Passes.Subst).insert p v) rest) res := by
  induction h with
  | @const f R st d w is t res htail ih =>
      intro cur b path hb hpath hmem hterm R' ha
      have hi : Instr.const d w ∈ b.instrs := hmem _ (by simp)
      rw [Passes.elimRest]
      simp only [List.map_cons, Passes.substInstr]
      refine Exec.const (ih hnd hli hdom hfind hpb hb hpath
        (fun ins hins => hmem ins (List.mem_cons_of_mem _ hins)) hterm ?_)
      simpa [Instr.defs, Regs.setMany_cons, Regs.setMany_nil_left] using
        ha.setMany_instr hnd hli hdom hfind hpb hp hb hpath hi [w]
  | @op f R st st' ds yop as args rets is t res hg hop hlen htail ih =>
      intro cur b path hb hpath hmem hterm R' ha
      have hi : Instr.op ds yop as ∈ b.instrs := hmem _ (by simp)
      have hg' := ha.getMany hnd hli hdom hfind hpb hpdef hb
        (fun x hx => instr_use_mem_blockUses hi (by simpa [Instr.uses] using hx)) hg
      rw [Passes.elimRest]
      simp only [List.map_cons, Passes.substInstr]
      refine Exec.op hg' hop hlen (ih hnd hli hdom hfind hpb hb hpath
        (fun ins hins => hmem ins (List.mem_cons_of_mem _ hins)) hterm ?_)
      exact ha.setMany_instr hnd hli hdom hfind hpb hp hb hpath hi rets
  | @opHalt f R st st' ds yop as args is t hg hop =>
      intro cur b path hb hpath hmem hterm R' ha
      have hi : Instr.op ds yop as ∈ b.instrs := hmem _ (by simp)
      have hg' := ha.getMany hnd hli hdom hfind hpb hpdef hb
        (fun x hx => instr_use_mem_blockUses hi (by simpa [Instr.uses] using hx)) hg
      rw [Passes.elimRest]
      simp only [List.map_cons, Passes.substInstr]
      exact Exec.opHalt hg' hop
  | @call f g R st st' ds as fid args rvals eb is t res hfid hg hplen heb
      hbody hlen htail ihbody ih =>
      intro cur b path hb hpath hmem hterm R' ha
      have hi : Instr.call ds fid as ∈ b.instrs := hmem _ (by simp)
      have hg' := ha.getMany hnd hli hdom hfind hpb hpdef hb
        (fun x hx => instr_use_mem_blockUses hi (by simpa [Instr.uses] using hx)) hg
      rw [Passes.elimRest]
      simp only [List.map_cons, Passes.substInstr]
      refine Exec.call hfid hg' hplen heb hbody hlen
        (ih hnd hli hdom hfind hpb hb hpath
        (fun ins hins => hmem ins (List.mem_cons_of_mem _ hins)) hterm ?_)
      exact ha.setMany_instr hnd hli hdom hfind hpb hp hb hpath hi rvals
  | @callHalt f g R st st' ds as fid args eb is t hfid hg hplen heb hbody ihbody =>
      intro cur b path hb hpath hmem hterm R' ha
      have hi : Instr.call ds fid as ∈ b.instrs := hmem _ (by simp)
      have hg' := ha.getMany hnd hli hdom hfind hpb hpdef hb
        (fun x hx => instr_use_mem_blockUses hi (by simpa [Instr.uses] using hx)) hg
      rw [Passes.elimRest]
      simp only [List.map_cons, Passes.substInstr]
      exact Exec.callHalt hfid hg' hplen heb hbody
  | @jump f R st e tb vals res htb hg hlen htail ih =>
      intro cur b path hb hpath hmem hterm R' ha
      have he : e ∈ b.term.edges := by rw [← hterm]; simp [Term.edges]
      obtain ⟨hg', hlen', ha'⟩ :=
        ha.edge hnd hli hdom hfind hpb hp hpdef hb hpath he htb hg hlen
      have htb' := Passes.elimStep_blocks_get
        (f := f) (bi := bi) (i := k) (p := p) (v := v) htb
      have htb'' : (Passes.substFunc ((∅ : Passes.Subst).insert p v)
          (Passes.removeParam f bi k)).blocks[
            (Passes.substEdge ((∅ : Passes.Subst).insert p v)
              (Passes.elimEdge bi k e)).target]? =
          some (Passes.substBlock ((∅ : Passes.Subst).insert p v)
            (Passes.removedBlock bi k e.target tb)) := by
        simpa [Passes.substEdge] using htb'
      have htail' := ih hnd hli hdom hfind hpb htb
        (.edge hpath hb he) (fun ins hins => hins) rfl ha'
      have htail'' : Exec (model := model) P
          (Passes.substFunc ((∅ : Passes.Subst).insert p v)
            (Passes.removeParam f bi k))
          (R'.setMany
            (Passes.substBlock ((∅ : Passes.Subst).insert p v)
              (Passes.removedBlock bi k e.target tb)).params
            (if e.target = bi then vals.eraseIdx k else vals)) st
          ⟨(Passes.substBlock ((∅ : Passes.Subst).insert p v)
              (Passes.removedBlock bi k e.target tb)).instrs,
            (Passes.substBlock ((∅ : Passes.Subst).insert p v)
              (Passes.removedBlock bi k e.target tb)).term⟩ res := by
        rw [Passes.elimBlock_rest]
        exact htail'
      simpa [Passes.elimRest, Passes.elimTerm, Passes.elimEdge,
        Passes.substTerm, Passes.mapEdges] using
        (Exec.jump
          (e := Passes.substEdge ((∅ : Passes.Subst).insert p v)
            (Passes.elimEdge bi k e)) htb'' hg' hlen' htail'')
  | @branchTrue f R st c w et ef tb vals res hc hw htb hg hlen htail ih =>
      intro cur b path hb hpath hmem hterm R' ha
      have het : et ∈ b.term.edges := by rw [← hterm]; simp [Term.edges]
      have hcuse : c ∈ ToAsm.blockUses b := term_use_mem_blockUses (b := b) (by
        rw [← hterm]
        simp [Term.uses])
      have hc' := ha.get hnd hli hdom hpb hpdef hb hcuse hc
      obtain ⟨hg', hlen', ha'⟩ :=
        ha.edge hnd hli hdom hfind hpb hp hpdef hb hpath het htb hg hlen
      have htb' := Passes.elimStep_blocks_get
        (f := f) (bi := bi) (i := k) (p := p) (v := v) htb
      have htb'' : (Passes.substFunc ((∅ : Passes.Subst).insert p v)
          (Passes.removeParam f bi k)).blocks[
            (Passes.substEdge ((∅ : Passes.Subst).insert p v)
              (Passes.elimEdge bi k et)).target]? =
          some (Passes.substBlock ((∅ : Passes.Subst).insert p v)
            (Passes.removedBlock bi k et.target tb)) := by
        simpa [Passes.substEdge] using htb'
      have htail' := ih hnd hli hdom hfind hpb htb
        (.edge hpath hb het) (fun ins hins => hins) rfl ha'
      have htail'' : Exec (model := model) P
          (Passes.substFunc ((∅ : Passes.Subst).insert p v)
            (Passes.removeParam f bi k))
          (R'.setMany
            (Passes.substBlock ((∅ : Passes.Subst).insert p v)
              (Passes.removedBlock bi k et.target tb)).params
            (if et.target = bi then vals.eraseIdx k else vals)) st
          ⟨(Passes.substBlock ((∅ : Passes.Subst).insert p v)
              (Passes.removedBlock bi k et.target tb)).instrs,
            (Passes.substBlock ((∅ : Passes.Subst).insert p v)
              (Passes.removedBlock bi k et.target tb)).term⟩ res := by
        rw [Passes.elimBlock_rest]
        exact htail'
      simpa [Passes.elimRest, Passes.elimTerm, Passes.elimEdge,
        Passes.substTerm, Passes.mapEdges] using
        (Exec.branchTrue
          (et := Passes.substEdge ((∅ : Passes.Subst).insert p v)
            (Passes.elimEdge bi k et))
          (ef := Passes.substEdge ((∅ : Passes.Subst).insert p v)
            (Passes.elimEdge bi k ef))
          hc' hw htb'' hg' hlen' htail'')
  | @branchFalse f R st c et ef tb vals res hc htb hg hlen htail ih =>
      intro cur b path hb hpath hmem hterm R' ha
      have hef : ef ∈ b.term.edges := by rw [← hterm]; simp [Term.edges]
      have hcuse : c ∈ ToAsm.blockUses b := term_use_mem_blockUses (b := b) (by
        rw [← hterm]
        simp [Term.uses])
      have hc' := ha.get hnd hli hdom hpb hpdef hb hcuse hc
      obtain ⟨hg', hlen', ha'⟩ :=
        ha.edge hnd hli hdom hfind hpb hp hpdef hb hpath hef htb hg hlen
      have htb' := Passes.elimStep_blocks_get
        (f := f) (bi := bi) (i := k) (p := p) (v := v) htb
      have htb'' : (Passes.substFunc ((∅ : Passes.Subst).insert p v)
          (Passes.removeParam f bi k)).blocks[
            (Passes.substEdge ((∅ : Passes.Subst).insert p v)
              (Passes.elimEdge bi k ef)).target]? =
          some (Passes.substBlock ((∅ : Passes.Subst).insert p v)
            (Passes.removedBlock bi k ef.target tb)) := by
        simpa [Passes.substEdge] using htb'
      have htail' := ih hnd hli hdom hfind hpb htb
        (.edge hpath hb hef) (fun ins hins => hins) rfl ha'
      have htail'' : Exec (model := model) P
          (Passes.substFunc ((∅ : Passes.Subst).insert p v)
            (Passes.removeParam f bi k))
          (R'.setMany
            (Passes.substBlock ((∅ : Passes.Subst).insert p v)
              (Passes.removedBlock bi k ef.target tb)).params
            (if ef.target = bi then vals.eraseIdx k else vals)) st
          ⟨(Passes.substBlock ((∅ : Passes.Subst).insert p v)
              (Passes.removedBlock bi k ef.target tb)).instrs,
            (Passes.substBlock ((∅ : Passes.Subst).insert p v)
              (Passes.removedBlock bi k ef.target tb)).term⟩ res := by
        rw [Passes.elimBlock_rest]
        exact htail'
      simpa [Passes.elimRest, Passes.elimTerm, Passes.elimEdge,
        Passes.substTerm, Passes.mapEdges] using
        (Exec.branchFalse
          (et := Passes.substEdge ((∅ : Passes.Subst).insert p v)
            (Passes.elimEdge bi k et))
          (ef := Passes.substEdge ((∅ : Passes.Subst).insert p v)
            (Passes.elimEdge bi k ef))
          hc' htb'' hg' hlen' htail'')
  | @ret f R st xs vals hg =>
      intro cur b path hb hpath hmem hterm R' ha
      have hg' := ha.getMany hnd hli hdom hfind hpb hpdef hb
        (fun x hx => term_use_mem_blockUses (b := b) (by
          rw [← hterm]
          simpa [Term.uses] using hx)) hg
      simpa [Passes.elimRest, Passes.elimTerm, Passes.substTerm,
        Passes.substVs, Passes.mapEdges] using (Exec.ret hg')
  | @halt f R st st' yop as args hg hop =>
      intro cur b path hb hpath hmem hterm R' ha
      have hg' := ha.getMany hnd hli hdom hfind hpb hpdef hb
        (fun x hx => term_use_mem_blockUses (b := b) (by
          rw [← hterm]
          simpa [Term.uses] using hx)) hg
      simpa [Passes.elimRest, Passes.elimTerm, Passes.substTerm,
        Passes.substVs, Passes.mapEdges] using (Exec.halt hg' hop)

/-- **Pass 1 (trivial block-parameter elimination) soundness**, under dominance.

**Proved below.** The invariant refines `LiveAgree` into a lockstep relation
with a dominance-delimited stale zone for `σ = (p ↦ v)`, carried
through the derivation block by block:

* base case: `liveAgree_entry` (proved) — `domCheck` says only `f.params` is live
  into the entry, and `σ` fixes them (`p` is a *block* parameter, so single
  assignment puts it outside `f.params`);
* at a jump into the rewritten block, the eliminated position carried either `v`
  — and then both sides bind the same word, because `v ∈ blockUses pred` so
  `ToAsm.liveIn_of_uses` puts it in the predecessor's live-in where the
  invariant applies — or `p` itself, and then the original re-binds `p` to its
  own current value while the optimized program reads `v`, which the invariant
  again equates (this is precisely the step the counterexample breaks without
  dominance: there `p` is read on a path where the binding is stale);
* every other instruction/terminator either preserves the invariant pointwise
  (`Regs.setMany_congr`) or reads only values the invariant covers
  (`Regs.getMany_congr`).

`Passes.elimTrivialParams_eq_loop` above supplies the fixed-point-loop
inversion, and `Passes.findTrivialParam_inv` / `findTrivialParam_edge` now
supply the complete candidate inversion, including `selfOnly`.

The block-lookup half of the one-removal transport is now
`Passes.elimStep_blocks_get`.  The precise remaining obstruction is its
sequential/register half: an induction over `Exec` must strengthen
`LiveAgree` with an intra-block relation that distinguishes values already
defined in the current instruction prefix (block live-in deliberately excludes
all definitions in the block), then prove the paired `getMany`/`setMany` lemma
for `eraseIdx i`.  At a jump, `_edge` gives the required split: a non-self edge
carries `v`, while a self edge may carry `p` and preserves the already-related
word.

The remaining path-sensitive case is now isolated more precisely.  On a jump
from `bi` to another block where `p` is live, that target may itself define
`v` (in particular as a block parameter), so `setMany` can rebind `v` while
leaving `p` unchanged.  `LiveAgree` alone does not exclude this local state.
An entry-rooted successful execution must exclude it because the candidate's
non-self `v` edge into `bi` and the later `p` use would otherwise require the
two distinct definition blocks to dominate each other; operationally, the
first traversal is stuck before both bindings exist.  The missing lemma must
make that history/reachability fact available to the `Exec` induction (or give
an equivalent binding-provenance invariant).  The outer loop can then thread
the now-proved one-step `allDefs.Nodup` and `domCheck` preservation facts through
`elimTrivialParams_eq_loop`; no search inversion remains missing. -/
/-
**Value-provenance preservation still missing (2026-08-01).**
`EntryPath.live_origin` and `BindingProvenance` above now prove, and preserve
across instruction bindings and edges, the complete *site* provenance needed
here.  The lift from sites to current words fails at a revisited definition:
after the path executes the unique definition of `v` again, the preservation
goal is `R p = R v`, but `BindingProvenance` yields only that the current `p`
came from an earlier visit to `bi`.  `findTrivialParam_edge` establishes the
equality when that visit binds `p`; it does not show that no later dynamic
occurrence of `v` intervenes.  Closing this requires the path to carry binding
events (including their words) and a last-occurrence theorem derived from
`domCheck`; merely adding another block-local `LiveAgree` field repeats the
same failed step.

This is the shared missing preservation lemma with CSE below, not a remaining
loop-inversion or edge-arity obligation. -/
theorem elimTrivialParam_one_sound {P : Prog} {f : Func} {args : List U256}
    {st : EvmState} {res : FRes} {bi k p v : Nat}
    (hnd : f.allDefs.Nodup) (hdom : ToAsm.Func.domCheck f = true)
    (hfind : Passes.findTrivialParam f = some (bi, k, p, v))
    {eb eb' : Block}
    (heb : f.blocks[f.entry]? = some eb)
    (heb' : (Passes.substFunc ((∅ : Passes.Subst).insert p v)
      (Passes.removeParam f bi k)).blocks[f.entry]? = some eb')
    (hexec : Exec (model := model) P f (Regs.empty.setMany f.params args) st
      ⟨eb.instrs, eb.term⟩ res) :
    Exec (model := model) P
      (Passes.substFunc ((∅ : Passes.Subst).insert p v)
        (Passes.removeParam f bi k))
      (Regs.empty.setMany f.params args) st ⟨eb'.instrs, eb'.term⟩ res := by
  obtain ⟨hbi, hbientry, hk, hpget, -, -, -, -⟩ :=
    Passes.findTrivialParam_inv hfind
  let pb := f.blocks[bi]
  have hpb : f.blocks[bi]? = some pb := Array.getElem?_eq_getElem hbi
  have hbang : f.blocks[bi]! = pb := Passes.getElem!_eq_getElem hbi
  have hk' : k < pb.params.length := by simpa [hbang] using hk
  have hpEq : pb.params[k] = p := by
    have hpget' := hpget
    rw [hbang] at hpget'
    simpa [List.getElem!_eq_getElem?_getD,
      List.getElem?_eq_getElem hk'] using hpget'
  have hp : p ∈ pb.params := by rw [← hpEq]; exact List.getElem_mem hk'
  have hpdef : p ∈ ToAsm.blockDefs pb := ToAsm.mem_blockDefs.mpr (Or.inl hp)
  obtain ⟨li, hli⟩ := ToAsm.liveInSets_isSome f
  have ha : TrivialAgree f bi p v f.entry
      (Regs.empty.setMany f.params args) (Regs.empty.setMany f.params args) := by
    refine ⟨fun _ _ => rfl, ?_⟩
    intro hd
    rcases hd [] EntryPath.entry with heq | hm
    · exact False.elim (hbientry heq)
    · simp at hm
  have hsim := elimTrivialParam_one_exec hnd hli hdom hfind hpb hp hpdef
    hexec heb EntryPath.entry (fun ins hins => hins) rfl ha
  have hout := Passes.elimStep_blocks_get
    (bi := bi) (i := k) (p := p) (v := v) heb
  rw [heb'] at hout
  have heq : eb' = Passes.substBlock ((∅ : Passes.Subst).insert p v)
      (Passes.removedBlock bi k f.entry eb) := by
    exact Option.some.inj hout
  subst eb'
  rw [Passes.elimBlock_rest]
  exact hsim

/-! ### Constant-folding execution invariant -/

theorem wfCheck_defs_nodup {f : Func} {n : Nat} (h : f.wfCheck n = true) :
    f.allDefs.Nodup := by
  unfold Func.wfCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1

theorem wfCheck_op_arity {f : Func} {n : Nat} (h : f.wfCheck n = true)
    {b : Block} (hb : b ∈ f.blocks.toList) {ds : List ValId} {yop : Op} {as : List ValId}
    (hi : .op ds yop as ∈ b.instrs) : ds.length ≤ 1 := by
  unfold Func.wfCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have hb' : b ∈ f.blocks := by simpa using hb
  have hblock := Array.all_eq_true_iff_forall_mem.mp h.2 b hb'
  simp only [Bool.and_eq_true] at hblock
  have hins := List.all_eq_true.mp hblock.2 (Instr.op ds yop as) hi
  simpa using hins

/-- Register consistency consumes the static certificates constructed by the
folder. -/
def ConstRegs (f : Func) (R : Regs) : Prop :=
  ∀ {d v w}, Passes.ConstDef f d v → R d = some w → w = v

theorem constRegs_entry {f : Func} (hnd : f.allDefs.Nodup) (args : List U256) :
    ConstRegs f (Regs.empty.setMany f.params args) := by
  intro d v w hc hr
  obtain ⟨b, hb, i, hi, hd⟩ := hc.site
  have hnot : d ∉ f.params := by
    intro hp
    exact funcParam_not_instr_def hnd hb hi hp hd
  rw [Regs.setMany_of_not_mem _ f.params args hnot] at hr
  simp [Regs.empty] at hr

theorem constRegs_setMany_params {f : Func} (hnd : f.allDefs.Nodup)
    {R : Regs} (hR : ConstRegs f R) {b : Block} (hb : b ∈ f.blocks.toList)
    (vs : List U256) : ConstRegs f (R.setMany b.params vs) := by
  intro d v w hc hr
  obtain ⟨b', hb', i, hi, hd⟩ := hc.site
  have hnot : d ∉ b.params := by
    intro hp
    exact param_not_instr_def hnd hb hb' hi hp hd
  rw [Regs.setMany_of_not_mem _ b.params vs hnot] at hr
  exact hR hc hr

/-- The exact rewrite of an arbitrary instruction suffix and its terminator. -/
def Passes.cfRest (is : List Instr) (t : Term) (m : Std.HashMap ValId U256) : Rest :=
  let r := is.foldl (fun s i => Passes.cfInstrStep i s) ⟨m, []⟩
  ⟨r.2.reverse, Passes.cfTerm { params := [], instrs := is, term := t } r.1⟩

theorem Passes.cfRest_cons (i : Instr) (is : List Instr) (t : Term)
    (m : Std.HashMap ValId U256) :
    cfRest (i :: is) t m =
      ⟨cfInstrOut i m :: (cfRest is t (cfInstrMap i m)).instrs,
        (cfRest is t (cfInstrMap i m)).term⟩ := by
  simp only [cfRest]
  rw [cfInstr_fold_cons, cfInstr_foldMap_cons]
  cases t <;> rfl

theorem Passes.cfRest_nil (t : Term) (m : Std.HashMap ValId U256) :
    cfRest [] t m = ⟨[], cfTerm { params := [], instrs := [], term := t } m⟩ := rfl

theorem Passes.cfBlockOut_rest (b : Block) (m : Std.HashMap ValId U256) :
    Rest.mk (cfBlockOut b m).instrs (cfBlockOut b m).term = cfRest b.instrs b.term m := by
  rfl

/-- A certified destination's unique instruction site determines which kind of
certificate it carries. -/
theorem constDef_instr_cases {f : Func} (hnd : f.allDefs.Nodup)
    {b : Block} (hb : b ∈ f.blocks.toList) {i : Instr} (hi : i ∈ b.instrs)
    {d : ValId} (hd : d ∈ i.defs) {v : U256} (hc : Passes.ConstDef f d v) :
    i = .const d v ∨
      ∃ yop as vs, i = .op [d] yop as ∧ Passes.pureOp yop = true ∧
        List.Forall₂ (Passes.ConstDef f) as vs ∧ Passes.evalPure yop vs = some v := by
  cases hc with
  | @const b' _ _ hb' hi' =>
    have heq := instr_def_unique hnd hb hb' hi hi' hd (by simp [Instr.defs])
    exact Or.inl heq
  | @op b' _ yop as vs _ hb' hi' hp hvs he =>
    have heq := instr_def_unique hnd hb hb' hi hi' hd (by simp [Instr.defs])
    exact Or.inr ⟨yop, as, vs, heq, hp, hvs, he⟩

theorem constRegs_getMany {f : Func} {R : Regs} (hR : ConstRegs f R)
    {as : List ValId} {vs args : List U256}
    (hc : List.Forall₂ (Passes.ConstDef f) as vs) (hg : R.getMany as = some args) :
    args = vs := by
  induction hc generalizing args with
  | nil => simp at hg; exact hg
  | @cons a v as vs hav htail ih =>
    rw [Regs.getMany_cons] at hg
    cases ha : R a with
    | none => simp [ha] at hg
    | some w =>
      cases hs : R.getMany as with
      | none => simp [ha, hs] at hg
      | some ws =>
        simp [ha, hs] at hg
        subst args
        rw [hR hav ha, ih hs]

theorem constRegs_const {f : Func} (hnd : f.allDefs.Nodup)
    {b : Block} (hb : b ∈ f.blocks.toList) {d : ValId} {v : U256}
    (hi : .const d v ∈ b.instrs) {R : Regs} (hR : ConstRegs f R) :
    ConstRegs f (R.set d v) := by
  intro x u w hc hr
  by_cases hxd : x = d
  · subst x
    simp at hr
    subst w
    rcases constDef_instr_cases hnd hb hi (by simp [Instr.defs]) hc with h | ⟨yop, as, vs, h, -⟩
    · injection h
    · cases h
  · rw [Regs.set_other _ _ hxd] at hr
    exact hR hc hr

theorem constRegs_call {f : Func} (hnd : f.allDefs.Nodup)
    {b : Block} (hb : b ∈ f.blocks.toList) {ds : List ValId} {fid : FuncId}
    {as : List ValId} (hi : .call ds fid as ∈ b.instrs) {R : Regs}
    (hR : ConstRegs f R) (rets : List U256) : ConstRegs f (R.setMany ds rets) := by
  intro d v w hc hr
  have hnot : d ∉ ds := by
    intro hd
    rcases constDef_instr_cases hnd hb hi (by simpa [Instr.defs] using hd) hc with h | ⟨yop, as', vs, h, -⟩
    · cases h
    · cases h
  rw [Regs.setMany_of_not_mem _ ds rets hnot] at hr
  exact hR hc hr

theorem constRegs_op {f : Func} (hwf : f.wfCheck n = true) (hnd : f.allDefs.Nodup)
    {b : Block} (hb : b ∈ f.blocks.toList) {ds : List ValId} {yop : Op}
    {as : List ValId} (hi : .op ds yop as ∈ b.instrs) {R : Regs} (hR : ConstRegs f R)
    {st st' : EvmState} {args rets : List U256} (hg : R.getMany as = some args)
    (hbi : builtinWithExternal model.calls model.creates yop args st (.ok rets st'))
    (hlen : ds.length = rets.length) : ConstRegs f (R.setMany ds rets) := by
  have harity := wfCheck_op_arity hwf hb hi
  cases ds with
  | nil =>
    intro d v w hc hr
    exact hR hc hr
  | cons d ds =>
    cases ds with
    | cons e es => simp at harity
    | nil =>
      cases rets with
      | nil => simp at hlen
      | cons r rs =>
        cases rs with
        | cons s ss => simp at hlen
        | nil =>
          intro x u w hc hr
          by_cases hxd : x = d
          · subst x
            simp [Regs.setMany, Regs.set] at hr
            subst w
            rcases constDef_instr_cases hnd hb hi (by simp [Instr.defs]) hc with h | ⟨yop', as', vs, h, hp, hvs, he⟩
            · cases h
            · injection h with _ hyop has
              subst yop'
              subst as'
              have hargs : args = vs := constRegs_getMany hR hvs hg
              subst args
              have hv := (Passes.evalPure_transport hp he hbi).1
              simpa using hv
          · rw [Regs.setMany_of_not_mem _ [d] [r] (by simp [hxd])] at hr
            exact hR hc hr

theorem Passes.pure_no_halt {yop : Op} (hp : pureOp yop = true) {args : List U256}
    {st st' : EvmState}
    (h : builtinWithExternal model.calls model.creates yop args st (.halt st')) : False := by
  have hn := (YulSemantics.EVM.effects_sound_withExternal model.calls model.creates).halt yop
    (pureOp_flags hp).2.2.2 args st (.halt st') h
  simp [YulSemantics.BuiltinResult.isHalt] at hn

/-- Lockstep simulation of an arbitrary suffix.  `CFMapSound` was established
statically by the fold-order induction; `ConstRegs` merely records that the
original execution has respected those certificates so far. -/
theorem constFold_exec_aux {P : Prog} {f : Func} {R : Regs} {st : EvmState}
    {rest : Rest} {res : FRes} (hwf : f.wfCheck n = true) (hnd : f.allDefs.Nodup)
    (h : Exec (model := model) P f R st rest res) :
    ∀ {b}, b ∈ f.blocks.toList → (∀ i ∈ rest.instrs, i ∈ b.instrs) →
      ∀ {m}, Passes.CFMapSound f m → ConstRegs f R →
        Exec (model := model) P (Passes.constFold f) R st
          (Passes.cfRest rest.instrs rest.term m) res := by
  induction h with
  | @const f R st d v is t res htail ih =>
    intro b hb hmem m hm hR
    rw [Passes.cfRest_cons]
    simp only [Passes.cfInstrOut, Passes.cfInstrMap]
    have hi0 : Instr.const d v ∈ b.instrs := hmem _ (by simp)
    refine Exec.const (ih hwf hnd hb
      (fun i hi => hmem i (List.mem_cons_of_mem _ hi))
      (Passes.cfInstrMap_sound hb hi0 hm)
      (constRegs_const hnd hb hi0 hR))
  | @op f R st st' ds yop as args rets is t res hg hbi hlen htail ih =>
    intro b hb hmem m hm hR
    rw [Passes.cfRest_cons]
    have hi : Instr.op ds yop as ∈ b.instrs := hmem _ (by simp)
    have hR' : ConstRegs f (R.setMany ds rets) :=
      constRegs_op hwf hnd hb hi hR hg hbi hlen
    cases ds with
    | nil =>
      simp only [Passes.cfInstrOut, Passes.cfInstrMap]
      exact Exec.op hg hbi hlen
        (ih hwf hnd hb (fun i hi' => hmem i (List.mem_cons_of_mem _ hi')) hm hR')
    | cons d ds =>
      cases ds with
      | cons e es =>
        simp only [Passes.cfInstrOut, Passes.cfInstrMap]
        exact Exec.op hg hbi hlen
          (ih hwf hnd hb (fun i hi' => hmem i (List.mem_cons_of_mem _ hi')) hm hR')
      | nil =>
        simp only [Passes.cfInstrOut, Passes.cfInstrMap]
        split
        · rename_i v hfold
          have hp : Passes.pureOp yop = true := by
            by_contra hp
            have hp' : Passes.pureOp yop = false := Bool.eq_false_of_not_eq_true hp
            simp [hp'] at hfold
          cases hs : as.mapM (m[·]?) with
          | none => simp [hp, hs] at hfold
          | some vs =>
            have hargs : args = vs := constRegs_getMany hR
              (Passes.cfMapSound_mapM hm hs) hg
            subst args
            have hv := Passes.evalPure_transport hp (by simpa [hp, hs] using hfold) hbi
            have hre : rets = [v] := hv.1
            have hst : st' = st := hv.2
            subst rets
            subst st'
            refine Exec.const ?_
            have hm' : Passes.CFMapSound f (m.insert d v) := by
              have hsnd : Passes.CFMapSound f
                  (Passes.cfInstrMap (.op [d] yop as) m) :=
                Passes.cfInstrMap_sound hb hi hm
              intro x u hx
              apply hsnd
              simpa [Passes.cfInstrMap, hfold] using hx
            exact ih hwf hnd hb (fun i hi' => hmem i (List.mem_cons_of_mem _ hi'))
              hm' hR'
        · exact Exec.op hg hbi hlen
            (ih hwf hnd hb (fun i hi' => hmem i (List.mem_cons_of_mem _ hi')) hm hR')
  | @opHalt f R st st' ds yop as args is t hg hbi =>
    intro b hb hmem m hm hR
    rw [Passes.cfRest_cons]
    cases ds with
    | nil =>
      simp only [Passes.cfInstrOut, Passes.cfInstrMap]
      exact Exec.opHalt hg hbi
    | cons d ds =>
      cases ds with
      | cons e es =>
        simp only [Passes.cfInstrOut, Passes.cfInstrMap]
        exact Exec.opHalt hg hbi
      | nil =>
        simp only [Passes.cfInstrOut, Passes.cfInstrMap]
        split
        · rename_i v hfold
          have hp : Passes.pureOp yop = true := by
            by_contra hp
            have hp' : Passes.pureOp yop = false := Bool.eq_false_of_not_eq_true hp
            simp [hp'] at hfold
          exact absurd hbi (Passes.pure_no_halt hp)
        · exact Exec.opHalt hg hbi
  | @call f g R st st' ds as fid args rvals eb is t res hfid hg hplen heb hbody hlen htail
      ihbody ih =>
    intro b hb hmem m hm hR
    rw [Passes.cfRest_cons]
    simp only [Passes.cfInstrOut, Passes.cfInstrMap]
    have hi : Instr.call ds fid as ∈ b.instrs := hmem _ (by simp)
    refine Exec.call hfid hg hplen heb hbody hlen ?_
    exact ih hwf hnd hb (fun i hi' => hmem i (List.mem_cons_of_mem _ hi')) hm
      (constRegs_call hnd hb hi hR rvals)
  | @callHalt f g R st st' ds as fid args eb is t hfid hg hplen heb hbody ihbody =>
    intro b hb hmem m hm hR
    rw [Passes.cfRest_cons]
    simp only [Passes.cfInstrOut, Passes.cfInstrMap]
    exact Exec.callHalt hfid hg hplen heb hbody
  | @jump f R st e tb args res htb hg hplen hbody ih =>
    intro b hb hmem m hm hR
    rw [Passes.cfRest_nil]
    obtain ⟨m', htb', hm'⟩ := Passes.constFold_block_get_sound htb
    have htbmem : tb ∈ f.blocks.toList := by
      obtain ⟨hlt, hget⟩ := Array.getElem?_eq_some_iff.mp htb
      exact List.mem_iff_getElem.mpr ⟨e.target, by simpa using hlt, by simpa using hget⟩
    refine Exec.jump htb' hg hplen ?_
    rw [Passes.cfBlockOut_rest]
    exact ih hwf hnd htbmem (fun i hi => hi) hm'
      (constRegs_setMany_params hnd hR htbmem args)
  | @branchTrue f R st c v et ef tb args res hc hv htb hg hplen hbody ih =>
    intro b hb hmem m hm hR
    rw [Passes.cfRest_nil]
    obtain ⟨m', htb', hm'⟩ := Passes.constFold_block_get_sound htb
    have htbmem : tb ∈ f.blocks.toList := by
      obtain ⟨hlt, hget⟩ := Array.getElem?_eq_some_iff.mp htb
      exact List.mem_iff_getElem.mpr ⟨et.target, by simpa using hlt, by simpa using hget⟩
    have hnext := ih hwf hnd htbmem (fun i hi => hi) hm'
      (constRegs_setMany_params hnd hR htbmem args)
    simp only [Passes.cfTerm]
    split
    · rename_i w hw
      have hwv : v = w := hR (hm hw) hc
      subst w
      have hvb : ¬ (v == 0) = true := by simpa [beq_iff_eq] using hv
      rw [if_neg hvb]
      rw [← Passes.cfBlockOut_rest] at hnext
      exact Exec.jump htb' hg hplen hnext
    · exact Exec.branchTrue hc hv htb' hg hplen
        (by rw [← Passes.cfBlockOut_rest] at hnext; exact hnext)
  | @branchFalse f R st c et ef tb args res hc htb hg hplen hbody ih =>
    intro b hb hmem m hm hR
    rw [Passes.cfRest_nil]
    obtain ⟨m', htb', hm'⟩ := Passes.constFold_block_get_sound htb
    have htbmem : tb ∈ f.blocks.toList := by
      obtain ⟨hlt, hget⟩ := Array.getElem?_eq_some_iff.mp htb
      exact List.mem_iff_getElem.mpr ⟨ef.target, by simpa using hlt, by simpa using hget⟩
    have hnext := ih hwf hnd htbmem (fun i hi => hi) hm'
      (constRegs_setMany_params hnd hR htbmem args)
    simp only [Passes.cfTerm]
    split
    · rename_i w hw
      have hw0 : w = 0 := (hR (hm hw) hc).symm
      subst w
      rw [if_pos (by simp)]
      rw [← Passes.cfBlockOut_rest] at hnext
      exact Exec.jump htb' hg hplen hnext
    · exact Exec.branchFalse hc htb' hg hplen
        (by rw [← Passes.cfBlockOut_rest] at hnext; exact hnext)
  | @ret f R st xs vals hg =>
    intro b hb hmem m hm hR
    rw [Passes.cfRest_nil]
    exact Exec.ret hg
  | @halt f R st st' yop as args hg hbi =>
    intro b hb hmem m hm hR
    rw [Passes.cfRest_nil]
    exact Exec.halt hg hbi

/-- **Pass 2 (constant folding) soundness.** No dominance hypothesis.

The loop is no longer in the way: `constFold_blocks_eq` (proved) turns it into a
`List.foldl` over `cfBlockStep`, and `constFold_spec` (proved) relates output
blocks to input blocks index by index — that is what closed `constFold_dom`.

What soundness additionally needs, and what the remaining `sorry` is. The
single-assignment lemmas (`instr_def_unique`, `param_not_instr_def`,
`funcParam_not_instr_def`) and the step-by-step correspondence
(`Passes.cfInstrStep_eq`, `cfInstr_fold_cons`, `cfInstr_foldMap_cons`) are now
proved; what is left is the invariant that ties them together.

* The invariant is **consistency**, not containment: `m[d]? = some v → R d =
  some w → w = v`. Entries for not-yet-executed definitions are unconstrained
  (`R d = none`), and a use of such a `d` is stuck in the original too.
* Consistency is used in *both* directions, and both are already available:
  forward at a folded op (`args.mapM (m[·]?) = some vs` together with
  `R.getMany args = some argvals` forces `argvals = vs`, and then
  `Passes.evalPure_transport` gives the value and leaves the state alone), and
  backward at a binding (`instr_def_unique` says the instruction now binding `d`
  *is* `d`'s only definition site, and `param_not_instr_def` /
  `funcParam_not_instr_def` rule out a jump or a function parameter re-binding
  something in the map's domain).
* The remaining difficulty is that the map is **not flow-sensitive**: `constFold`
  threads it in *block-index* order while an execution visits blocks in
  *control-flow* order, so the map in force at block `k` was computed from blocks
  `0..k-1` whether or not the execution visited them. Consistency therefore
  cannot be carried by the forward simulation alone; it has to be established
  once, by induction over the **fold order** (block index, then instruction
  index), and only then consumed by the simulation. That induction is
  well-founded because a folded op's arguments are entered into the map strictly
  earlier in the same fold — `cfInstr_foldMap_cons` is the step lemma it needs.
* With consistency in hand the simulation itself is routine: register files stay
  *equal* on the two sides (a folded op binds the same destination to the same
  word), so `exec_congr` handles the register side and the machine state is
  untouched. -/
theorem constFold_sound {P : Prog} {f : Func} {args : List U256} {st : EvmState} {res : FRes}
    {eb eb' : Block} (hwf : f.wfCheck P.funcs.size = true)
    (heb : f.blocks[f.entry]? = some eb)
    (heb' : (Passes.constFold f).blocks[f.entry]? = some eb')
    (hexec : Exec (model := model) P f (Regs.empty.setMany f.params args) st
      ⟨eb.instrs, eb.term⟩ res) :
    Exec (model := model) P (Passes.constFold f) (Regs.empty.setMany f.params args) st
      ⟨eb'.instrs, eb'.term⟩ res := by
  have hnd : f.allDefs.Nodup := wfCheck_defs_nodup hwf
  obtain ⟨m, hebo, hm⟩ := Passes.constFold_block_get_sound heb
  rw [heb'] at hebo
  have heq : eb' = Passes.cfBlockOut eb m := Option.some.inj hebo
  subst eb'
  have hebmem : eb ∈ f.blocks.toList := by
    obtain ⟨hlt, hget⟩ := Array.getElem?_eq_some_iff.mp heb
    exact List.mem_iff_getElem.mpr ⟨f.entry, by simpa using hlt, by simpa using hget⟩
  rw [Passes.cfBlockOut_rest]
  exact constFold_exec_aux hwf hnd hexec hebmem (fun i hi => hi) hm
    (constRegs_entry hnd args)

/-! ### CSE execution invariant -/

/-- Runtime meaning of a CSE expression.  For an operation entry we retain one
actual evaluation of the pure operation.  Its arguments are read through the
final substitution, exactly as they are in the emitted block, and the entry's
representative contains its (necessarily singleton) result.  Keeping the
historic state in the witness is intentional: `pure_rets_eq` transports the
result to a later occurrence without requiring the two machine states to be
equal. -/
def CseExprRuntime (τ : Passes.Subst) (R : Regs) :
    Passes.CseExpr → ValId → Prop
  | .const v, d => R d = some v
  | .op yop as, d =>
      ∃ vals w s s',
        R.getMany (Passes.substVs τ as) = some vals ∧
        builtinWithExternal model.calls model.creates yop vals s (.ok [w] s') ∧
        R d = some w

/-- Every entry in the currently available CSE table has its advertised
runtime meaning.  This is the semantic counterpart of `CseTabSound`: the
latter supplies the definition-site certificate, while this predicate records
that the certified representative has actually executed on the current path. -/
def CseTabRuntime (τ : Passes.Subst) (R : Regs) (tab : Passes.CseTab) : Prop :=
  (∀ {yop as d}, ((yop, as), d) ∈ tab.ops →
    CseExprRuntime τ R (.op yop as) d) ∧
  (∀ {v d}, (v, d) ∈ tab.consts → CseExprRuntime τ R (.const v) d)

/-- Registers read by the operation expressions in a runtime CSE table, after
the final use substitution. -/
def cseTabRuntimeUses (τ : Passes.Subst) (tab : Passes.CseTab) : List ValId :=
  tab.ops.flatMap fun e => Passes.substVs τ e.1.2

theorem CseTabRuntime.empty (τ : Passes.Subst) (R : Regs) :
    CseTabRuntime τ R {} := by
  simp [CseTabRuntime]

theorem CseTabRuntime.inheritTab {τ : Passes.Subst} {R : Regs}
    {tab : Passes.CseTab} (h : CseTabRuntime τ R tab) (ps : List ValId) :
    CseTabRuntime τ R (Passes.inheritTab tab ps) := by
  refine ⟨?_, ?_⟩
  · intro yop as d hm
    exact h.1 (List.mem_filter.mp hm).1
  · intro v d hm
    exact h.2 (List.mem_filter.mp hm).1

theorem Passes.substV_not_blockParam {f : Func} {τ : Passes.Subst}
    (hnd : f.allDefs.Nodup) (hsub : Passes.CseSubSound f τ)
    {b : Block} (hb : b ∈ f.blocks.toList) {x : ValId}
    (hx : x ∉ b.params) : Passes.substV τ x ∉ b.params := by
  intro hp
  unfold Passes.substV at hp
  cases ht : τ[x]? with
  | none =>
      simp [Std.HashMap.getD_eq_getD_getElem?, ht] at hp
      exact hx hp
  | some y =>
      simp [Std.HashMap.getD_eq_getD_getElem?, ht] at hp
      obtain ⟨e, -, hy⟩ := hsub.1 ht
      obtain ⟨b0, hb0, i, hi, hyd⟩ := hy.site
      exact param_not_instr_def hnd hb hb0 hi hp hyd

/-- Binding a register outside both the table representatives and the
substituted expression arguments preserves the runtime table invariant. -/
theorem CseTabRuntime.set_of_fresh {τ : Passes.Subst} {R : Regs}
    {tab : Passes.CseTab} (h : CseTabRuntime τ R tab) {d : ValId} {w : U256}
    (hvals : d ∉ Passes.cseTabVals tab) (huses : d ∉ cseTabRuntimeUses τ tab) :
    CseTabRuntime τ (R.set d w) tab := by
  refine ⟨?_, ?_⟩
  · intro yop as d0 hm
    obtain ⟨vals, v, s, s', hg, hb, hd0⟩ := h.1 hm
    have hd0ne : d0 ≠ d := by
      intro heq
      apply hvals
      subst d0
      exact List.mem_append_left _ (List.mem_map.mpr ⟨((yop, as), d), hm, rfl⟩)
    have harg : ∀ x ∈ Passes.substVs τ as, x ≠ d := by
      intro x hx heq
      apply huses
      subst x
      exact List.mem_flatMap.mpr ⟨((yop, as), d0), hm, hx⟩
    refine ⟨vals, v, s, s', ?_, hb, ?_⟩
    · rw [← Regs.getMany_congr (R1 := R) (R2 := R.set d w) (by
        intro x hx
        rw [Regs.set_other _ _ (harg x hx)])]
      exact hg
    · rw [Regs.set_other _ _ hd0ne]
      exact hd0
  · intro v d0 hm
    have hd0ne : d0 ≠ d := by
      intro heq
      apply hvals
      subst d0
      exact List.mem_append_right _ (List.mem_map.mpr ⟨(v, d), hm, rfl⟩)
    rw [CseExprRuntime, Regs.set_other _ _ hd0ne]
    exact h.2 hm

theorem CseTabRuntime.setMany_of_fresh {τ : Passes.Subst} {R : Regs}
    {tab : Passes.CseTab} (h : CseTabRuntime τ R tab)
    {ds : List ValId} {vals : List U256}
    (hfresh : ∀ d ∈ ds, d ∉ Passes.cseTabVals tab ∧
      d ∉ cseTabRuntimeUses τ tab) :
    CseTabRuntime τ (R.setMany ds vals) tab := by
  induction ds generalizing R vals with
  | nil => exact h
  | cons d ds ih =>
      cases vals with
      | nil => rw [Regs.setMany_nil_right]; exact h
      | cons v vals =>
          rw [Regs.setMany_cons]
          apply ih (h := h.set_of_fresh (hfresh d (by simp)).1
            (hfresh d (by simp)).2)
          intro x hx
          exact hfresh x (by simp [hx])

theorem CseTabRuntime.setMany_inheritTab {f : Func} {τ : Passes.Subst}
    {R : Regs} {tab : Passes.CseTab} {b : Block}
    (hnd : f.allDefs.Nodup) (hsub : Passes.CseSubSound f τ)
    (hb : b ∈ f.blocks.toList) (h : CseTabRuntime τ R tab)
    (vs : List U256) :
    CseTabRuntime τ (R.setMany b.params vs)
      (Passes.inheritTab tab b.params) := by
  have h0 := h.inheritTab b.params
  have hvals : ∀ p ∈ b.params,
      p ∉ Passes.cseTabVals (Passes.inheritTab tab b.params) := by
    intro p hp hmem
    simp only [Passes.cseTabVals, Passes.inheritTab, List.mem_append,
      List.mem_map, List.mem_filter] at hmem
    rcases hmem with ⟨e, ⟨-, he⟩, rfl⟩ | ⟨e, ⟨-, he⟩, rfl⟩ <;>
      simp [hp] at he
  have huses : ∀ p ∈ b.params,
      p ∉ cseTabRuntimeUses τ (Passes.inheritTab tab b.params) := by
    intro p hp hmem
    simp only [cseTabRuntimeUses, List.mem_flatMap] at hmem
    obtain ⟨⟨⟨yop, as⟩, d⟩, he, hx⟩ := hmem
    have he0 := (List.mem_filter.mp he).2
    rw [Bool.not_eq_true', Bool.or_eq_false_iff] at he0
    have hstored : ∀ x ∈ as, x ∉ b.params := by
      intro x hxa hxp
      exact (List.any_eq_false.mp he0.1 x hxa) (by simpa using hxp)
    have hxmem : ∃ x ∈ as, Passes.substV τ x = p := by
      simpa [Passes.substVs] using hx
    obtain ⟨x, hxa, hxp⟩ := hxmem
    exact (Passes.substV_not_blockParam hnd hsub hb (hstored x hxa)) (hxp ▸ hp)
  have go : ∀ (qs : List ValId) (vs : List U256) (R0 : Regs),
      (∀ q ∈ qs, q ∈ b.params) →
      CseTabRuntime τ R0 (Passes.inheritTab tab b.params) →
      CseTabRuntime τ (R0.setMany qs vs) (Passes.inheritTab tab b.params) := by
    intro qs
    induction qs with
    | nil => intro vs R0 hqs hr; exact hr
    | cons p ps ih =>
        intro vs R0 hqs hr
        cases vs with
        | nil => rw [Regs.setMany_nil_right]; exact hr
        | cons v vs =>
            rw [Regs.setMany_cons]
            apply ih vs (R0.set p v) (fun q hq => hqs q (by simp [hq]))
            exact CseTabRuntime.set_of_fresh hr
              (hvals p (hqs p (by simp))) (huses p (hqs p (by simp)))
  exact go b.params vs R (fun q hq => hq) h0

theorem CseTabRuntime.addConst {τ : Passes.Subst} {R : Regs}
    {tab : Passes.CseTab} (h : CseTabRuntime τ R tab) {d : ValId} {v : U256}
    (hvals : d ∉ Passes.cseTabVals tab) (huses : d ∉ cseTabRuntimeUses τ tab) :
    CseTabRuntime τ (R.set d v) { tab with consts := (v, d) :: tab.consts } := by
  have hold := h.set_of_fresh hvals huses (w := v)
  refine ⟨hold.1, ?_⟩
  intro v0 d0 hm
  rcases List.mem_cons.mp hm with hhead | htail
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hhead
    simp [CseExprRuntime]
  · exact hold.2 htail

theorem CseTabRuntime.addOp {τ : Passes.Subst} {R : Regs}
    {tab : Passes.CseTab} (h : CseTabRuntime τ R tab)
    {d : ValId} {yop : Op} {as : List ValId} {vals : List U256} {w : U256}
    {s s' : EvmState}
    (hvals : d ∉ Passes.cseTabVals tab) (huses : d ∉ cseTabRuntimeUses τ tab)
    (hg : (R.set d w).getMany (Passes.substVs τ as) = some vals)
    (hb : builtinWithExternal model.calls model.creates yop vals s (.ok [w] s')) :
    CseTabRuntime τ (R.set d w) { tab with ops := ((yop, as), d) :: tab.ops } := by
  have hold := h.set_of_fresh hvals huses (w := w)
  refine ⟨?_, hold.2⟩
  intro yop0 as0 d0 hm
  rcases List.mem_cons.mp hm with hhead | htail
  · obtain ⟨hkey, rfl⟩ := Prod.mk.inj hhead
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hkey
    exact ⟨vals, w, s, s', hg, hb, by simp⟩
  · exact hold.1 htail

theorem CseTabRuntime.const_of_find {τ : Passes.Subst} {R : Regs}
    {tab : Passes.CseTab} (h : CseTabRuntime τ R tab)
    {v v0 : U256} {d : ValId}
    (hf : tab.consts.find? (fun x => x.1 == v) = some (v0, d)) :
    v0 = v ∧ R d = some v := by
  have hm : (v0, d) ∈ tab.consts := List.mem_of_find?_eq_some hf
  have hv : v0 = v := beq_iff_eq.mp (List.find?_some
    (p := fun x : U256 × ValId => x.1 == v) (a := (v0, d)) hf)
  subst v0
  exact ⟨rfl, h.2 hm⟩

theorem CseTabRuntime.op_of_find {τ : Passes.Subst} {R : Regs}
    {tab : Passes.CseTab} (h : CseTabRuntime τ R tab)
    {yop yop0 : Op} {as as0 : List ValId} {d : ValId}
    (hf : tab.ops.find? (fun x => x.1 == (yop, as)) = some ((yop0, as0), d)) :
    yop0 = yop ∧ as0 = as ∧ CseExprRuntime τ R (.op yop as) d := by
  have hm : ((yop0, as0), d) ∈ tab.ops := List.mem_of_find?_eq_some hf
  have heq : (yop0, as0) = (yop, as) :=
    beq_iff_eq.mp (List.find?_some
      (p := fun x : (Op × List ValId) × ValId => x.1 == (yop, as))
      (a := ((yop0, as0), d)) hf)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
  exact ⟨rfl, rfl, h.1 hm⟩

/-- Consume an operation-table runtime certificate at a repeated pure
operation.  The stored and current evaluations have the same arguments, so
purity fixes the result; well-formed CSE operations have one destination and
therefore one result. -/
theorem CseExprRuntime.op_result {τ : Passes.Subst} {R : Regs}
    {yop : Op} {as : List ValId} {d : ValId}
    (hr : CseExprRuntime τ R (.op yop as) d)
    (hp : Passes.pureOp yop = true) {vals rets : List U256} {st st' : EvmState}
    (hg : R.getMany (Passes.substVs τ as) = some vals)
    (hb : builtinWithExternal model.calls model.creates yop vals st (.ok rets st')) :
    ∃ w, rets = [w] ∧ R d = some w := by
  obtain ⟨vals0, w0, s, s', hg0, hb0, hd⟩ := hr
  have hvals : vals0 = vals := Option.some.inj (hg0.symm.trans hg)
  subst vals0
  have hrets : [w0] = rets := Passes.pure_rets_eq hp hb0 hb
  exact ⟨w0, hrets.symm, hd⟩

/-! The executable view of the instruction fold.  Keeping this recursive
form separate from `cseBlockOut` makes the semantic induction follow the
source instruction list one constructor at a time; the lemma below reconnects
it to the accumulator/reverse implementation used by the pass. -/

namespace Passes

def cseInstrsOut (τ : Subst) :
    List Instr → CseTab → Std.HashSet ValId → Subst →
      Std.HashSet ValId → Std.HashSet ValId → List Instr
  | [], _, _, _, _, _ => []
  | i :: is, tab, used, σ, defined, blockDefs =>
      let s := cseInstrStep i ⟨[], tab, used, σ, defined, blockDefs⟩
      s.1.reverse.map (substInstr τ) ++
        cseInstrsOut τ is s.2.1 s.2.2.1 s.2.2.2.1
          s.2.2.2.2.1 s.2.2.2.2.2

omit model in
theorem cseInstrStep_acc_eq (i : Instr) (acc : List Instr)
    (tab : CseTab) (used : Std.HashSet ValId) (σ : Subst)
    (defined blockDefs : Std.HashSet ValId) :
    cseInstrStep i ⟨acc, tab, used, σ, defined, blockDefs⟩ =
      let s := cseInstrStep i ⟨[], tab, used, σ, defined, blockDefs⟩
      ⟨s.1 ++ acc, s.2.1, s.2.2.1, s.2.2.2.1,
        s.2.2.2.2.1, s.2.2.2.2.2⟩ := by
  cases i with
  | const d v =>
      simp only [cseInstrStep, substInstr]
      split <;> rfl
  | op ds yop args =>
      cases ds with
      | nil => rfl
      | cons d rest =>
          cases rest with
          | cons e es => rfl
          | nil =>
              simp only [cseInstrStep, substInstr]
              split <;> (try split <;> (try split <;> (try split))) <;> rfl
  | call ds fid args => rfl

omit model in
theorem cseInstrFold_acc_state (l : List Instr) (acc : List Instr)
    (tab : CseTab) (used : Std.HashSet ValId) (σ : Subst)
    (defined blockDefs : Std.HashSet ValId) :
    let r := l.foldl (fun s i => cseInstrStep i s)
      ⟨acc, tab, used, σ, defined, blockDefs⟩
    let r0 := l.foldl (fun s i => cseInstrStep i s)
      ⟨[], tab, used, σ, defined, blockDefs⟩
    r = ⟨r0.1 ++ acc, r0.2.1, r0.2.2.1, r0.2.2.2.1,
      r0.2.2.2.2.1, r0.2.2.2.2.2⟩ := by
  induction l generalizing acc tab used σ defined blockDefs with
  | nil => rfl
  | cons i is ih =>
      rw [List.foldl_cons, List.foldl_cons, cseInstrStep_acc_eq]
      let s := cseInstrStep i ⟨[], tab, used, σ, defined, blockDefs⟩
      rw [ih (acc := s.1 ++ acc), ih (acc := s.1)]
      simp [List.append_assoc]

omit model in
theorem cseInstrFold_acc (τ : Subst) (l : List Instr) (acc : List Instr)
    (tab : CseTab) (used : Std.HashSet ValId) (σ : Subst)
    (defined blockDefs : Std.HashSet ValId) :
    let r := l.foldl (fun s i => cseInstrStep i s)
      ⟨acc, tab, used, σ, defined, blockDefs⟩
    let r0 := l.foldl (fun s i => cseInstrStep i s)
      ⟨[], tab, used, σ, defined, blockDefs⟩
    r.1.reverse.map (substInstr τ) =
      acc.reverse.map (substInstr τ) ++ r0.1.reverse.map (substInstr τ)
      ∧ r.2 = r0.2 := by
  rw [cseInstrFold_acc_state]
  simp [List.reverse_append, List.map_append]

omit model in
theorem cseInstrsOut_eq_fold (τ : Subst) (l : List Instr) (tab : CseTab)
    (used : Std.HashSet ValId) (σ : Subst)
    (defined blockDefs : Std.HashSet ValId) :
    cseInstrsOut τ l tab used σ defined blockDefs =
      (l.foldl (fun s i => cseInstrStep i s)
        ⟨[], tab, used, σ, defined, blockDefs⟩).1.reverse.map
        (substInstr τ) := by
  induction l generalizing tab used σ defined blockDefs with
  | nil => rfl
  | cons i is ih =>
      rw [cseInstrsOut]
      let s := cseInstrStep i ⟨[], tab, used, σ, defined, blockDefs⟩
      rw [ih]
      have hacc := cseInstrFold_acc τ is s.1 s.2.1 s.2.2.1 s.2.2.2.1
        s.2.2.2.2.1 s.2.2.2.2.2
      rw [List.foldl_cons]
      exact hacc.1.symm

end Passes

namespace Passes

omit model in
theorem cseInstrFold_defs_source (l : List Instr) (acc : List Instr)
    (tab : CseTab) (used : Std.HashSet ValId) (σ : Subst)
    (defined blockDefs : Std.HashSet ValId) {x : ValId}
    (hx : x ∈ (l.foldl (fun s i => cseInstrStep i s)
      ⟨acc, tab, used, σ, defined, blockDefs⟩).1.flatMap Instr.defs) :
    x ∈ acc.flatMap Instr.defs ∨ x ∈ l.flatMap Instr.defs := by
  induction l generalizing acc tab used σ defined blockDefs with
  | nil => exact Or.inl hx
  | cons i is ih =>
      rw [List.foldl_cons] at hx
      rcases ih _ _ _ _ _ _ hx with hold | htail
      · rcases cseInstrStep_out (i := i) (acc := acc) (tab := tab)
          (used := used) (σ := σ) with hs | hs
        · change x ∈ (cseInstrStep i
            ⟨acc, tab, used, σ, defined, blockDefs⟩).1.flatMap Instr.defs at hold
          rw [hs] at hold
          exact Or.inl hold
        · change x ∈ (cseInstrStep i
            ⟨acc, tab, used, σ, defined, blockDefs⟩).1.flatMap Instr.defs at hold
          rw [hs, List.flatMap_cons] at hold
          rcases List.mem_append.mp hold with hnew | hold
          · exact Or.inr (by
              rw [List.flatMap_cons]
              apply List.mem_append_left
              simpa using hnew)
          · exact Or.inl hold
      · exact Or.inr (by
          rw [List.flatMap_cons]
          exact List.mem_append_right _ htail)

omit model in
theorem cseBlockOut_def_source {f : Func} {i : BlockId} {b : Block}
    (hb : f.blocks[i]? = some b) {x : ValId}
    (hx : x ∈ ToAsm.blockDefs
      (substBlock (csePrefix f f.blocks.size).2.2 (cseBlockOut f i))) :
    x ∈ ToAsm.blockDefs b := by
  have hi : i < f.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  have hbang : f.blocks[i]! = b := by
    rw [getElem!_eq_getElem hi]
    exact (Array.getElem?_eq_some_iff.mp hb).2
  rw [ToAsm.mem_blockDefs] at hx ⊢
  rcases hx with hp | hd
  · exact Or.inl (by simpa [substBlock, cseBlockOut, hbang] using hp)
  · right
    simp only [substBlock, List.mem_flatMap] at hd
    obtain ⟨j, hj, hxj⟩ := hd
    obtain ⟨j0, hj0, rfl⟩ := List.mem_map.mp hj
    have hxj0 : x ∈ j0.defs := by simpa using hxj
    let st := csePrefix f i
    let tab := cseEntryTab f (inEdgeSources f) st.2.1 i
    let r := b.instrs.foldl (fun s ins => cseInstrStep ins s)
      ⟨[], tab, ∅, st.2.2, ∅, cseBlockDefs b⟩
    have hjr : j0 ∈ r.1 := by
      simpa [cseBlockOut, hbang, st, tab, r] using hj0
    have hflat : x ∈ r.1.flatMap Instr.defs :=
      List.mem_flatMap.mpr ⟨j0, hjr, hxj0⟩
    rcases cseInstrFold_defs_source b.instrs [] tab ∅ st.2.2 ∅
        (cseBlockDefs b) hflat with hnil | hout
    · simp at hnil
    · exact hout

end Passes

/-- Runtime-independent stale-zone fact for inherited CSE entries: the
representative's unique defining block strictly dominates the block at which
the entry is available. -/
theorem cseAvail_strict_dom {f : Func} (hnd : f.allDefs.Nodup)
    (hwf : f.wfCheck n = true) {di : BlockId} {db : Block}
    (hdb : f.blocks[di]? = some db) {x : ValId}
    (hxdef : x ∈ ToAsm.blockDefs db) {i : BlockId}
    (hx : x ∈ Passes.cseAvail f i) : StrictBlockDom f di i := by
  intro path hp
  induction hp with
  | entry =>
      rw [Passes.cseAvail_entry] at hx
      simp at hx
  | @edge path j b e hp hb he ih =>
      rcases Passes.cseAvail_succ hnd hwf hb he hx with hlocal | havail
      · have horigin := Passes.cseBlockOut_def_source hb hlocal
        have hji := Passes.block_def_index_unique hnd hdb hb hxdef horigin
        subst j
        exact List.mem_append_right _ (by simp)
      · exact List.mem_append_left _ (ih havail)

/-- Every final CSE alias is either represented earlier in the same block or
by a definition in a strict predecessor chain. -/
theorem cse_alias_zone {f : Func} (hnd : f.allDefs.Nodup)
    (hwf : f.wfCheck n = true) {d d0 : ValId}
    (hmap : (Passes.csePrefix f f.blocks.size).2.2[d]? = some d0)
    {di : BlockId} {db : Block} (hdb : f.blocks[di]? = some db)
    (hddef : d ∈ ToAsm.blockDefs db) {ri : BlockId} {rb : Block}
    (hrb : f.blocks[ri]? = some rb) (hrdef : d0 ∈ ToAsm.blockDefs rb) :
    ri = di ∨ StrictBlockDom f ri di := by
  let τ := (Passes.csePrefix f f.blocks.size).2.2
  have hsubst : Passes.substV τ d = d0 := by
    simp [τ, Passes.substV, Std.HashMap.getD_eq_getD_getElem?, hmap]
  have hresolve := (Passes.cseBlock_spec hnd hdb).2.1 d hddef
  rw [hsubst] at hresolve
  rcases hresolve with hlocal | havail
  · have horigin := Passes.cseBlockOut_def_source hdb hlocal
    exact Or.inl (Passes.block_def_index_unique hnd hrb hdb hrdef horigin)
  · exact Or.inr (cseAvail_strict_dom hnd hwf hrb hrdef havail)

namespace Passes

def Before (a b : ValId) (xs : List ValId) : Prop :=
  ∃ pre mid post, xs = pre ++ a :: mid ++ b :: post

theorem Before.asymm {a b : ValId} {xs : List ValId} (hn : xs.Nodup)
    (hab : Before a b xs) : ¬ Before b a xs := by
  rcases hab with ⟨pre, mid, post, rfl⟩
  rintro ⟨pre', mid', post', heq⟩
  let ia := pre.length
  let ib := pre.length + 1 + mid.length
  let ib' := pre'.length
  let ia' := pre'.length + 1 + mid'.length
  have hiaQ : (pre ++ a :: mid ++ b :: post)[ia]? = some a := by
    simp [ia]
  have hibQ : (pre ++ a :: mid ++ b :: post)[ib]? = some b := by
    rw [show pre ++ a :: mid ++ b :: post =
      (pre ++ [a] ++ mid) ++ (b :: post) by simp [List.append_assoc]]
    have hib_eq : ib = (pre ++ [a] ++ mid).length := by
      simp [ib]
      omega
    rw [hib_eq]
    simp
  have hibQ' : (pre ++ a :: mid ++ b :: post)[ib']? = some b := by
    rw [heq]
    simp [ib']
  have hiaQ' : (pre ++ a :: mid ++ b :: post)[ia']? = some a := by
    rw [heq]
    rw [show pre' ++ b :: mid' ++ a :: post' =
      (pre' ++ [b] ++ mid') ++ (a :: post') by simp [List.append_assoc]]
    have hia_eq : ia' = (pre' ++ [b] ++ mid').length := by
      simp [ia']
      omega
    rw [hia_eq]
    simp
  obtain ⟨hia_lt, hia⟩ := List.getElem?_eq_some_iff.mp hiaQ
  obtain ⟨hib_lt, hib⟩ := List.getElem?_eq_some_iff.mp hibQ
  obtain ⟨hib'_lt, hib'⟩ := List.getElem?_eq_some_iff.mp hibQ'
  obtain ⟨hia'_lt, hia'⟩ := List.getElem?_eq_some_iff.mp hiaQ'
  have hea : ia = ia' :=
    (hn.getElem_inj_iff (hi := hia_lt) (hj := hia'_lt)).mp (hia.trans hia'.symm)
  have heb : ib = ib' :=
    (hn.getElem_inj_iff (hi := hib_lt) (hj := hib'_lt)).mp (hib.trans hib'.symm)
  dsimp [ia, ib, ia', ib'] at hea heb
  omega

theorem substInstr_use_source_of_rangeFree {sigma tau : Subst}
    (hext : SubstExt sigma tau) (hrange : RangeFree tau)
    {d d0 : ValId} (hmap : tau[d]? = some d0)
    {i : Instr} (hd : d ∈ (substInstr sigma i).uses) : d ∈ i.uses := by
  obtain ⟨x, hx, hxd⟩ := substInstr_use hd
  unfold substV at hxd
  cases hsx : sigma[x]? with
  | none =>
      simp [Std.HashMap.getD_eq_getD_getElem?, hsx] at hxd
      simpa [hxd] using hx
  | some y =>
      have hty : tau[x]? = some y := hext hsx
      have hynone : tau[y]? = none := hrange hty
      simp [Std.HashMap.getD_eq_getD_getElem?, hsx] at hxd
      subst y
      rw [hmap] at hynone
      contradiction

theorem instr_order_before {f : Func} {b : Block}
    (hb : b ∈ f.blocks.toList) {pre mid post : List Instr} {i j : Instr}
    (his : b.instrs = pre ++ i :: mid ++ j :: post)
    {d e : ValId} (hdi : i.defs = [d]) (hej : j.defs = [e]) :
    Before d e (cseSeen f f.blocks.size) := by
  obtain ⟨bs, bt, hbs⟩ := List.mem_iff_append.mp hb
  refine ⟨bs.flatMap (fun b : Block => b.instrs.flatMap Instr.defs) ++
      pre.flatMap Instr.defs,
    mid.flatMap Instr.defs,
    post.flatMap Instr.defs ++
      bt.flatMap (fun b : Block => b.instrs.flatMap Instr.defs), ?_⟩
  have htake : f.blocks.toList.take f.blocks.size = f.blocks.toList := by simp
  rw [cseSeen, htake, hbs]
  simp [his, hdi, hej, List.append_assoc]

theorem instr_order_before_mem {f : Func} {b : Block}
    (hb : b ∈ f.blocks.toList) {pre mid post : List Instr} {i j : Instr}
    (his : b.instrs = pre ++ i :: mid ++ j :: post)
    {d e : ValId} (hdi : d ∈ i.defs) (hej : e ∈ j.defs) :
    Before d e (cseSeen f f.blocks.size) := by
  obtain ⟨bs, bt, hbs⟩ := List.mem_iff_append.mp hb
  obtain ⟨di0, di1, hdiSplit⟩ := List.mem_iff_append.mp hdi
  obtain ⟨ej0, ej1, hejSplit⟩ := List.mem_iff_append.mp hej
  refine ⟨bs.flatMap (fun b : Block => b.instrs.flatMap Instr.defs) ++
      pre.flatMap Instr.defs ++ di0,
    di1 ++ mid.flatMap Instr.defs ++ ej0,
    ej1 ++ post.flatMap Instr.defs ++
      bt.flatMap (fun b : Block => b.instrs.flatMap Instr.defs), ?_⟩
  have htake : f.blocks.toList.take f.blocks.size = f.blocks.toList := by simp
  rw [cseSeen, htake, hbs]
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]
  rw [his]
  simp only [List.flatMap_append, List.flatMap_cons]
  rw [hdiSplit, hejSplit]
  simp [List.flatMap_append, List.append_assoc]

inductive CseDomainDef (f : Func) (tau : Subst) : CseExpr → ValId → Prop
  | op {b : Block} {i : Instr} {sigma : Subst} {d : ValId}
      {yop : Op} {args : List ValId} :
      b ∈ f.blocks.toList → i ∈ b.instrs →
      substInstr sigma i = .op [d] yop args →
      (∀ a ∈ args, tau[a]? ≠ none → a ∈ i.uses) →
      (∀ a ∈ args, ∃ x ∈ i.uses, substV tau x = substV tau a) →
      CseDomainDef f tau (.op yop args) d

def CseTabDomainSound (f : Func) (tau : Subst) (tab : CseTab) : Prop :=
  ∀ {yop args d}, ((yop, args), d) ∈ tab.ops →
    CseDomainDef f tau (.op yop args) d

theorem CseTabDomainSound.empty (f : Func) (tau : Subst) :
    CseTabDomainSound f tau {} := by simp [CseTabDomainSound]

theorem CseTabDomainSound.inheritTab {f : Func} {tau : Subst} {tab : CseTab}
    (h : CseTabDomainSound f tau tab) (ps : List ValId) :
    CseTabDomainSound f tau (inheritTab tab ps) := by
  intro yop args d hm
  exact h (List.mem_filter.mp hm).1

theorem CseTabDomainSound.addOp {f : Func} {tau : Subst} {tab : CseTab}
    (h : CseTabDomainSound f tau tab) {yop : Op} {args : List ValId}
    {d : ValId} (hd : CseDomainDef f tau (.op yop args) d) :
    CseTabDomainSound f tau { tab with ops := ((yop, args), d) :: tab.ops } := by
  intro yop0 args0 d0 hm
  rcases List.mem_cons.mp hm with hnew | hold
  · obtain ⟨hkey, rfl⟩ := Prod.mk.inj hnew
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hkey
    exact hd
  · exact h hold

theorem cseInstrStep_domain {f : Func} {b : Block} (hb : b ∈ f.blocks.toList)
    {tau : Subst} (hrange : RangeFree tau)
    {tab : CseTab} {used : Std.HashSet ValId} {sigma : Subst}
    {defined blockDefs : Std.HashSet ValId}
    (htab : CseTabDomainSound f tau tab) (i : Instr) (hi : i ∈ b.instrs)
    (hext : SubstExt sigma tau) :
    let r := cseInstrStep i ⟨[], tab, used, sigma, defined, blockDefs⟩
    CseTabDomainSound f tau r.2.1 := by
  cases i with
  | const d v =>
      simp only [cseInstrStep, substInstr]
      split <;> exact htab
  | call ds fid args => exact htab
  | op ds yop args =>
      cases ds with
      | nil => exact htab
      | cons d rest =>
        cases rest with
        | cons e es => exact htab
        | nil =>
          simp only [cseInstrStep, substInstr]
          split
          · split
            · split <;> exact htab
            · split
              · apply htab.addOp
                apply CseDomainDef.op hb hi rfl
                · intro a ha hta
                  obtain ⟨a0, ha0⟩ := Option.ne_none_iff_exists'.mp hta
                  have ha' : a ∈ (substInstr sigma (.op [d] yop args)).uses := by
                    simpa [substInstr, Instr.uses] using ha
                  exact substInstr_use_source_of_rangeFree hext hrange ha0 ha'
                · intro a ha
                  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
                  exact ⟨x, hx, (substV_absorb hext hrange x).symm⟩
              · exact htab
          · exact htab

theorem cseInstrFold_domain {f : Func} {b : Block} (hb : b ∈ f.blocks.toList)
    {tau : Subst} (hrange : RangeFree tau)
    {seen : List ValId} {tab : CseTab} {sigma : Subst}
    (hinv : CSEInv f seen tab sigma) (htab : CseTabDomainSound f tau tab)
    (l : List Instr) (hmem : ∀ i ∈ l, i ∈ b.instrs)
    (hnd : (seen ++ l.flatMap Instr.defs).Nodup)
    (acc : List Instr) (used defined blockDefs : Std.HashSet ValId) :
    let r := l.foldl (fun s i => cseInstrStep i s)
      ⟨acc, tab, used, sigma, defined, blockDefs⟩
    SubstExt r.2.2.2.1 tau → CseTabDomainSound f tau r.2.1 := by
  dsimp only
  induction l generalizing seen tab sigma acc used defined blockDefs with
  | nil => intro _; exact htab
  | cons i is ih =>
      simp only [List.flatMap_cons] at hnd
      have hprefix : (seen ++ i.defs).Nodup := by
        apply List.Nodup.of_append_left (l₂ := is.flatMap Instr.defs)
        simpa [List.append_assoc] using hnd
      have hone := cseInstrStep_inv hb (used := used) (defined := defined)
        (blockDefs := blockDefs) hinv i (hmem i (by simp)) hprefix
      have hstate := cseInstrStep_state i acc tab used sigma defined blockDefs
      let s1 := cseInstrStep i ⟨acc, tab, used, sigma, defined, blockDefs⟩
      have hinv1 : CSEInv f (seen ++ i.defs) s1.2.1 s1.2.2.2.1 := by
        rw [hstate]
        exact hone.1
      rw [List.foldl_cons]
      intro hout
      have htailInv := cseInstrFold_inv hb hinv1 is
        (fun j hj => hmem j (by simp [hj]))
        (by simpa [List.append_assoc] using hnd)
        s1.1 s1.2.2.1 s1.2.2.2.2.1 s1.2.2.2.2.2
      have hext1tau : SubstExt s1.2.2.2.1 tau := by
        intro x y hxy
        exact hout (htailInv.2 hxy)
      have hext0tau : SubstExt sigma tau := by
        have hext01 : SubstExt sigma s1.2.2.2.1 := by rw [hstate]; exact hone.2
        intro x y hxy
        exact hext1tau (hext01 hxy)
      have htab1 : CseTabDomainSound f tau s1.2.1 := by
        rw [hstate]
        exact cseInstrStep_domain hb hrange htab i (hmem i (by simp)) hext0tau
      have hs1eta : (⟨s1.1, s1.2.1, s1.2.2.1, s1.2.2.2.1,
          s1.2.2.2.2.1, s1.2.2.2.2.2⟩ : CSEInner) = s1 := by
        rcases s1 with ⟨a, tab1, used1, sigma1, defined1, blockDefs1⟩
        rfl
      change CseTabDomainSound f tau
        (is.foldl (fun s i => cseInstrStep i s) s1).2.1
      rw [← hs1eta]
      exact ih hinv1 htab1
        (fun j hj => hmem j (by simp [hj]))
        (by simpa [List.append_assoc] using hnd)
        s1.1 s1.2.2.1 s1.2.2.2.2.1 s1.2.2.2.2.2 (by
          rw [hs1eta]
          exact hout)

def CSEPrefixDomainInv (f : Func) (tau : Subst) (n : Nat) : Prop :=
  ∀ p < n, CseTabDomainSound f tau (csePrefix f n).2.1[p]!

theorem csePrefixDomainInv {f : Func} (hnd : f.allDefs.Nodup) :
    ∀ n ≤ f.blocks.size,
      CSEPrefixDomainInv f (csePrefix f f.blocks.size).2.2 n := by
  let tau := (csePrefix f f.blocks.size).2.2
  have hrange : RangeFree tau :=
    (csePrefixInv hnd f.blocks.size (Nat.le_refl _)).1.2.2.1
  intro n hn
  induction n with
  | zero => intro p hp; omega
  | succ n ih =>
      have hnlt : n < f.blocks.size := by omega
      let b := f.blocks[n]
      have hbget : f.blocks[n]? = some b := Array.getElem?_eq_getElem hnlt
      have hbmem : b ∈ f.blocks.toList := block_mem_of_getElem? hbget
      have hpre := csePrefixInv hnd n (Nat.le_of_lt hnlt)
      let tab := cseEntryTab f (inEdgeSources f) (csePrefix f n).2.1 n
      have htab : CseTabDomainSound f tau tab := by
        by_cases he : (n == f.entry) = true
        · simp only [tab, cseEntryTab, if_pos he]
          exact CseTabDomainSound.empty f tau
        · cases hs : (inEdgeSources f)[n]! with
          | nil =>
              simp only [tab, cseEntryTab, if_neg he, hs]
              exact CseTabDomainSound.empty f tau
          | cons p ps =>
              cases ps with
              | nil =>
                  by_cases hp : p < n
                  · simpa [tab, cseEntryTab, he, hs, hp] using
                      (CseTabDomainSound.inheritTab (ih (by omega) p hp)
                        f.blocks[n]!.params)
                  · simpa [tab, cseEntryTab, he, hs, hp] using
                      CseTabDomainSound.empty f tau
              | cons q qs =>
                  simp only [tab, cseEntryTab, if_neg he, hs]
                  exact CseTabDomainSound.empty f tau
      let r := b.instrs.foldl (fun s i => cseInstrStep i s)
        ⟨[], tab, ∅, (csePrefix f n).2.2, ∅, cseBlockDefs b⟩
      have hseenNodup :
          (cseSeen f n ++ b.instrs.flatMap Instr.defs).Nodup := by
        rw [← cseSeen_succ hbget]
        exact (instrDefs_nodup hnd).sublist (cseSeen_sublist f (n + 1))
      have hrEq : (csePrefix f (n + 1)).2.2 = r.2.2.2.1 := by
        rw [csePrefix_succ]
        simp only [cseBlockStep]
        have hbang : f.blocks[n]! = b := by rw [getElem!_eq_getElem hnlt]
        rw [hbang]
      have hrExt : SubstExt r.2.2.2.1 tau := by
        rw [← hrEq]
        exact csePrefix_ext_to hnd (Nat.succ_le_of_lt hnlt) (Nat.le_refl _)
      have hrDom : CseTabDomainSound f tau r.2.1 :=
        cseInstrFold_domain hbmem hrange (cseEntryTab_inv hpre) htab
          b.instrs (fun i hi => hi) hseenNodup [] ∅ ∅ (cseBlockDefs b) hrExt
      intro p hp
      rw [csePrefix_succ]
      simp only [cseBlockStep]
      have hbang : f.blocks[n]! = b := by rw [getElem!_eq_getElem hnlt]
      rw [hbang]
      change CseTabDomainSound f tau
        ((csePrefix f n).2.1.setIfInBounds n r.2.1)[p]!
      by_cases hpn : p = n
      · subst p
        have hn0 : n < (csePrefix f n).2.1.size := by rw [hpre.2.1]; exact hnlt
        have hn1 : n < ((csePrefix f n).2.1.setIfInBounds n r.2.1).size := by simpa
        rw [getElem!_eq_getElem hn1, Array.getElem_setIfInBounds_self]
        exact hrDom
      · have hp0 : p < (csePrefix f n).2.1.size := by
          rw [hpre.2.1]
          omega
        have hp1 : p < ((csePrefix f n).2.1.setIfInBounds n r.2.1).size := by simpa
        rw [getElem!_eq_getElem hp1,
          Array.getElem_setIfInBounds_ne hp0 (Ne.symm hpn), ← getElem!_eq_getElem hp0]
        exact ih (by omega) p (by omega)

theorem source_use_mem_substInstr_of_none {sigma : Subst} {i : Instr}
    {x : ValId} (hn : sigma[x]? = none) (hx : x ∈ i.uses) :
    x ∈ (substInstr sigma i).uses := by
  cases i with
  | const d v => simp [Instr.uses] at hx
  | op ds yop args =>
      simp only [Instr.uses] at hx ⊢
      simp only [substInstr, substVs, List.mem_map]
      exact ⟨x, hx, by simp [substV, Std.HashMap.getD_eq_getD_getElem?, hn]⟩
  | call ds fid args =>
      simp only [Instr.uses] at hx ⊢
      simp only [substInstr, substVs, List.mem_map]
      exact ⟨x, hx, by simp [substV, Std.HashMap.getD_eq_getD_getElem?, hn]⟩

theorem cse_drop_not_self_use {f : Func} {li : Array (List ValId)}
    (hnd : f.allDefs.Nodup) (hwf : f.wfCheck n = true)
    (hli : ToAsm.liveInSets f = some li) (hdom : ToAsm.Func.domCheck f = true)
    (hrange : RangeFree (csePrefix f f.blocks.size).2.2)
    (horder : AliasOrdered (cseSeen f f.blocks.size) (csePrefix f f.blocks.size).2.2)
    {d d0 : ValId} (hmap : (csePrefix f f.blocks.size).2.2[d]? = some d0)
    {yop : Op} {args : List ValId}
    (hdrop : CseDropPos f (.op yop args) d)
    (hentry : CseEntryPos f (.op yop args) d0)
    (hdomain : CseDomainDef f (csePrefix f f.blocks.size).2.2 (.op yop args) d0)
    {di : BlockId} {db : Block} (hdb : f.blocks[di]? = some db)
    {path : List BlockId} (hpath : EntryPath f path di) :
    ∀ {i : Instr}, i ∈ db.instrs → d ∈ i.defs → d ∉ i.uses := by
  intro i hi hddef hdUse
  cases hdrop with
  | @op b pre post idrop sigmaDrop _ _ _ hbDrop hseqDrop hsubstDrop
      hdropNone hprefix =>
    have hidropDef : idrop.defs = [d] := by
      rw [← substInstr_defs sigmaDrop idrop, hsubstDrop]
      rfl
    have hiEq : i = idrop := instr_def_unique hnd
      (block_mem_of_getElem? hdb) hbDrop hi (by
        rw [hseqDrop]
        simp) hddef (by simp [hidropDef])
    subst i
    have hbIndex : b = db := by
      obtain ⟨bi, hblt, hbget⟩ := List.mem_iff_getElem.mp hbDrop
      have hbg : f.blocks[bi]? = some b := Array.getElem?_eq_some_iff.mpr
        ⟨by simpa using hblt, by simpa using hbget⟩
      have hbDef : d ∈ ToAsm.blockDefs b := ToAsm.mem_blockDefs.mpr
        (Or.inr (List.mem_flatMap.mpr ⟨idrop, by rw [hseqDrop]; simp,
          by rw [hidropDef]; simp⟩))
      have hdbDef : d ∈ ToAsm.blockDefs db := ToAsm.mem_blockDefs.mpr
        (Or.inr (List.mem_flatMap.mpr ⟨idrop, hi, by rw [hidropDef]; simp⟩))
      have hbi : bi = di := block_def_index_unique hnd hbg hdb hbDef hdbDef
      subst bi
      exact Option.some.inj (hbg.symm.trans hdb)
    subst b
    have hdArgs : d ∈ args := by
      have hs := source_use_mem_substInstr_of_none hdropNone hdUse
      rw [hsubstDrop] at hs
      simpa [Instr.uses] using hs
    cases hentry with
    | @op br preR postR irep sigmaRep _ _ _ hbRep hseqRep hsubstRep hstable =>
      cases hdomain with
      | @op bu iuse sigmaUse _ _ _ hbUse hiUse hsubstUse hdirect horigin =>
        have hdUseRep0 : d ∈ iuse.uses := hdirect d hdArgs (by rw [hmap]; simp)
        have hiUseDef : iuse.defs = [d0] := by
          rw [← substInstr_defs sigmaUse iuse, hsubstUse]
          rfl
        have hiRepDef : irep.defs = [d0] := by
          rw [← substInstr_defs sigmaRep irep, hsubstRep]
          rfl
        have hd0UseDef : d0 ∈ iuse.defs := by rw [hiUseDef]; simp
        have hd0RepDef : d0 ∈ irep.defs := by rw [hiRepDef]; simp
        have hiUseEq : iuse = irep := instr_def_unique hnd hbUse hbRep hiUse
          (by rw [hseqRep]; simp) hd0UseDef hd0RepDef
        subst iuse
        have hdUseRep : d ∈ irep.uses := hdUseRep0
        obtain ⟨ri, hrlt, hrget⟩ := List.mem_iff_getElem.mp hbRep
        have hrb : f.blocks[ri]? = some br := by
          apply Array.getElem?_eq_some_iff.mpr
          exact ⟨by simpa using hrlt, by simpa using hrget⟩
        have hdBlockDef : d ∈ ToAsm.blockDefs db :=
          ToAsm.mem_blockDefs.mpr (Or.inr (List.mem_flatMap.mpr
            ⟨idrop, hi, by simp [hidropDef]⟩))
        have hrBlockDef : d0 ∈ ToAsm.blockDefs br :=
          ToAsm.mem_blockDefs.mpr (Or.inr (List.mem_flatMap.mpr
            ⟨irep, by rw [hseqRep]; simp, by simp [hiRepDef]⟩))
        rcases cse_alias_zone hnd hwf hmap hdb hdBlockDef hrb hrBlockDef with hre | hrs
        · subst ri
          have hbr : br = db := Option.some.inj (hrb.symm.trans hdb)
          rw [hbr] at hseqRep
          rw [hbr] at hbRep
          rw [hbr] at hrBlockDef
          have hirep : irep ∈ pre := by
            have hm : irep ∈ pre ++ idrop :: post := by simpa [hseqDrop] using
              (show irep ∈ db.instrs from by rw [hseqRep]; simp)
            rcases List.mem_append.mp hm with hp | ht
            · exact hp
            · rcases List.mem_cons.mp ht with heq | hpost
              · subst irep
                have hdd0 : d = d0 := by simpa [hidropDef] using hiRepDef
                subst d0
                exact False.elim (by have := hrange hmap; rw [hmap] at this; contradiction)
              · obtain ⟨mid, tail, hpostEq⟩ := List.mem_iff_append.mp hpost
                have hrev : Before d d0 (cseSeen f f.blocks.size) :=
                  instr_order_before (block_mem_of_getElem? hdb)
                    (pre := pre) (mid := mid) (post := tail)
                    (i := idrop) (j := irep) (by
                      rw [hseqDrop, hpostEq]
                      simp [List.append_assoc])
                    hidropDef hiRepDef
                obtain ⟨a, m, z, hord⟩ := horder d d0 hmap
                have hforward : Before d0 d (cseSeen f f.blocks.size) :=
                  ⟨a, m, z, hord⟩
                have hseenNodup : (cseSeen f f.blocks.size).Nodup := by
                  have htake : f.blocks.toList.take f.blocks.size = f.blocks.toList := by simp
                  simpa [cseSeen, htake] using instrDefs_nodup hnd
                exact False.elim ((Before.asymm hseenNodup hforward) hrev)
          exact hprefix (List.mem_flatMap.mpr ⟨irep, hirep, hdUseRep⟩)
        · have hduseBlock : d ∈ ToAsm.blockUses br :=
            instr_use_mem_blockUses (by rw [hseqRep]; simp) hdUseRep
          have hdr : BlockDom f di ri :=
            blockDef_dominates_use hnd hli hdom hdb hdBlockDef hrb hduseBlock
          have hrmem : ri ∈ path := hrs path hpath
          obtain ⟨prePath, hpRi, -, -⟩ := hpath.prefix_of_mem hrmem
          exact False.elim ((hrs.not_reverse hpRi) hdr)

end Passes

/-! ### The CSE substitution, its seen-set guard, and the register invariant

These are the pieces of the `cse_sound` lockstep that are independent of the
instruction fold: what the final substitution can contain, when a dropped
definition's site has already been passed, and how the two register files are
related at every point.  See the note above `cse_sound` for how they compose. -/

namespace Passes

/-- The final CSE substitution of `f`: the dropped-definition map accumulated
after every block has been processed.  `Passes.cse f` applies it to all uses. -/
def cseSub (f : Func) : Subst := (csePrefix f f.blocks.size).2.2

omit model in
theorem cseSub_inv {f : Func} (hnd : f.allDefs.Nodup) :
    CSEInv f (cseSeen f f.blocks.size) {} (cseSub f) :=
  (csePrefixInv hnd f.blocks.size (Nat.le_refl _)).1

omit model in
theorem cseSub_rangeFree {f : Func} (hnd : f.allDefs.Nodup) :
    RangeFree (cseSub f) := (cseSub_inv hnd).2.2.1

omit model in
/-- Both ends of a final alias are instruction destinations. -/
theorem cseSub_def_site {f : Func} (hnd : f.allDefs.Nodup) {d d0 : ValId}
    (h : (cseSub f)[d]? = some d0) :
    (∃ b ∈ f.blocks.toList, ∃ i ∈ b.instrs, d ∈ i.defs) ∧
      (∃ b ∈ f.blocks.toList, ∃ i ∈ b.instrs, d0 ∈ i.defs) := by
  obtain ⟨e, hd, hd0⟩ := (cseSub_inv hnd).2.1 h
  exact ⟨hd.site, hd0.site⟩

omit model in
/-- No block parameter is ever dropped. -/
theorem cseSub_blockParam_none {f : Func} (hnd : f.allDefs.Nodup)
    {b : Block} (hb : b ∈ f.blocks.toList) {p : ValId} (hp : p ∈ b.params) :
    (cseSub f)[p]? = none := by
  by_contra hn
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hn
  obtain ⟨⟨b0, hb0, i, hi, hpd⟩, -⟩ := cseSub_def_site hnd hq
  exact param_not_instr_def hnd hb hb0 hi hp hpd

omit model in
/-- No function parameter is ever dropped. -/
theorem cseSub_funcParam_none {f : Func} (hnd : f.allDefs.Nodup)
    {p : ValId} (hp : p ∈ f.params) : (cseSub f)[p]? = none := by
  by_contra hn
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hn
  obtain ⟨⟨b0, hb0, i, hi, hpd⟩, -⟩ := cseSub_def_site hnd hq
  exact funcParam_not_instr_def hnd hb0 hi hp hpd

omit model in
theorem block_index_of_mem {f : Func} {b : Block} (hb : b ∈ f.blocks.toList) :
    ∃ i : Nat, f.blocks[i]? = some b := by
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hb
  refine ⟨i, ?_⟩
  rw [Array.getElem?_eq_getElem (by simpa using hi)]
  simpa using hget

omit model in
/-- The substitution in force at a mid-block fold position is a restriction of
the final one.  With `Passes.substVs_absorb` this is what lets a stored (already
substituted) table argument be replaced by the corresponding *source* use. -/
theorem cseFold_substExt {f : Func} (hnd : f.allDefs.Nodup)
    {cur : BlockId} {b : Block} (hb : f.blocks[cur]? = some b)
    {pre post : List Instr} (hsplit : b.instrs = pre ++ post) :
    SubstExt (pre.foldl (fun s i => cseInstrStep i s)
      ⟨[], cseEntryTab f (inEdgeSources f) (csePrefix f cur).2.1 cur, ∅,
        (csePrefix f cur).2.2, ∅, cseBlockDefs b⟩).2.2.2.1 (cseSub f) := by
  have hcur : cur < f.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  have hbmem : b ∈ f.blocks.toList := block_mem_of_getElem? hb
  have hseenSucc : cseSeen f (cur + 1) = cseSeen f cur ++ b.instrs.flatMap Instr.defs :=
    cseSeen_succ hb
  have hseenNodup : (cseSeen f cur ++ b.instrs.flatMap Instr.defs).Nodup := by
    rw [← hseenSucc]
    exact (instrDefs_nodup hnd).sublist (cseSeen_sublist f (cur + 1))
  have hflat : b.instrs.flatMap Instr.defs =
      pre.flatMap Instr.defs ++ post.flatMap Instr.defs := by
    rw [hsplit, List.flatMap_append]
  have hpreNodup : (cseSeen f cur ++ pre.flatMap Instr.defs).Nodup := by
    refine hseenNodup.sublist ?_
    exact (List.Sublist.refl _).append (by rw [hflat]; exact List.sublist_append_left _ _)
  have hpostNodup : ((cseSeen f cur ++ pre.flatMap Instr.defs) ++
      post.flatMap Instr.defs).Nodup := by
    rw [List.append_assoc, ← hflat]
    exact hseenNodup
  have hpreInv := csePrefixInv hnd cur (Nat.le_of_lt hcur)
  have htab : CSEInv f (cseSeen f cur)
      (cseEntryTab f (inEdgeSources f) (csePrefix f cur).2.1 cur)
      (csePrefix f cur).2.2 := cseEntryTab_inv hpreInv
  have hpreMem : ∀ i ∈ pre, i ∈ b.instrs := by
    intro i hi; rw [hsplit]; exact List.mem_append_left _ hi
  have hpostMem : ∀ i ∈ post, i ∈ b.instrs := by
    intro i hi; rw [hsplit]; exact List.mem_append_right _ hi
  have hr1 := cseInstrFold_inv hbmem htab pre hpreMem hpreNodup [] ∅ ∅ (cseBlockDefs b)
  set s1 := pre.foldl (fun s i => cseInstrStep i s)
    (⟨[], cseEntryTab f (inEdgeSources f) (csePrefix f cur).2.1 cur, ∅,
      (csePrefix f cur).2.2, ∅, cseBlockDefs b⟩ : CSEInner) with hs1
  have hr2 := cseInstrFold_inv hbmem hr1.1 post hpostMem hpostNodup
    s1.1 s1.2.2.1 s1.2.2.2.2.1 s1.2.2.2.2.2
  have hfull : post.foldl (fun s i => cseInstrStep i s)
      (⟨s1.1, s1.2.1, s1.2.2.1, s1.2.2.2.1, s1.2.2.2.2.1, s1.2.2.2.2.2⟩ : CSEInner) =
      b.instrs.foldl (fun s i => cseInstrStep i s)
        (⟨[], cseEntryTab f (inEdgeSources f) (csePrefix f cur).2.1 cur, ∅,
          (csePrefix f cur).2.2, ∅, cseBlockDefs b⟩ : CSEInner) := by
    rw [hsplit, List.foldl_append, ← hs1]
  have hend : SubstExt s1.2.2.2.1 (csePrefix f (cur + 1)).2.2 := by
    have h2 : SubstExt s1.2.2.2.1
        (post.foldl (fun s i => cseInstrStep i s)
          (⟨s1.1, s1.2.1, s1.2.2.1, s1.2.2.2.1, s1.2.2.2.2.1, s1.2.2.2.2.2⟩ :
            CSEInner)).2.2.2.1 := hr2.2
    rw [hfull] at h2
    have hbBang : f.blocks[cur]! = b := by
      rw [getElem!_eq_getElem hcur]
      exact (Array.getElem?_eq_some_iff.mp hb).2
    rw [csePrefix_succ]
    simp only [cseBlockStep, hbBang]
    intro x y hxy
    exact h2 hxy
  intro x y hxy
  exact csePrefix_ext_to hnd (Nat.succ_le_of_lt hcur) (Nat.le_refl _) (hend hxy)

end Passes

/-! ### Dominance plumbing -/

theorem BlockDom.trans {f : Func} {a b c : BlockId}
    (hab : BlockDom f a b) (hbc : BlockDom f b c) : BlockDom f a c := by
  intro path hp
  rcases hbc path hp with rfl | hb
  · exact hab path hp
  · obtain ⟨pre, hpre, -, hsub⟩ := hp.prefix_of_mem hb
    rcases hab pre hpre with rfl | ha
    · exact Or.inr hb
    · exact Or.inr (hsub _ ha)

omit model in
theorem StrictBlockDom.blockDom {f : Func} {a b : BlockId}
    (h : StrictBlockDom f a b) : BlockDom f a b := fun path hp => Or.inr (h path hp)

theorem StrictBlockDom.trans_left {f : Func} {a b c : BlockId}
    (hab : BlockDom f a b) (hbc : StrictBlockDom f b c) : StrictBlockDom f a c := by
  intro path hp
  have hb := hbc path hp
  obtain ⟨pre, hpre, -, hsub⟩ := hp.prefix_of_mem hb
  rcases hab pre hpre with rfl | ha
  · exact hb
  · exact hsub _ ha

/-! ### Two list lemmas for the intra-block alias order -/

omit model in
/-- In a duplicate-free list, an element occurring before a member of an initial
segment lies in that initial segment itself. -/
theorem mem_left_of_before {α : Type} {x y : α} :
    ∀ {l1 l2 p q : List α}, (l1 ++ l2).Nodup → l1 ++ l2 = p ++ x :: q →
      y ∈ q → y ∈ l1 → x ∈ l1 := by
  intro l1
  induction l1 with
  | nil => intro l2 p q _ _ _ hy; simp at hy
  | cons a l1 ih =>
      intro l2 p q hnd heq hyq hy1
      cases p with
      | nil =>
          have hax : a = x := by simpa using congrArg (·.head?) heq
          simp [hax]
      | cons a' p' =>
          have ha : a' = a := by simpa using (congrArg (·.head?) heq).symm
          subst ha
          have heq' : l1 ++ l2 = p' ++ x :: q := by
            simpa using congrArg (·.tail) heq
          have hnd' : (l1 ++ l2).Nodup := (List.nodup_cons.mp hnd).2
          have hane : y ≠ a' := by
            intro hya
            subst y
            have hmem : a' ∈ l1 ++ l2 := by
              rw [heq']
              exact List.mem_append_right _ (List.mem_cons_of_mem _ hyq)
            exact (List.nodup_cons.mp hnd).1 hmem
          have hy1' : y ∈ l1 := by
            rcases List.mem_cons.mp hy1 with h | h
            · exact absurd h hane
            · exact h
          exact List.mem_cons_of_mem _ (ih hnd' heq' hyq hy1')

omit model in
theorem sublist_flatMap_of_mem {α β : Type} (g : α → List β) :
    ∀ {l : List α} {a : α}, a ∈ l → (g a).Sublist (l.flatMap g)
  | [], _, h => absurd h (by simp)
  | c :: cs, a, h => by
      rw [List.flatMap_cons]
      rcases List.mem_cons.mp h with rfl | h'
      · exact List.sublist_append_left _ _
      · exact (sublist_flatMap_of_mem g h').trans (List.sublist_append_right _ _)

omit model in
/-- Comparing two decompositions of the same list: if `j` occurs after the
distinguished `i`, but not at or before it, then `i` belongs to the prefix of
the decomposition distinguished at `j`. -/
theorem mem_prefix_of_later {α : Type} {l pre post pre' post' : List α}
    {i j : α} (h : l = pre ++ i :: post) (hj : j ∈ post)
    (hjpre : j ∉ pre) (hji : j ≠ i) (h' : l = pre' ++ j :: post') :
    i ∈ pre' := by
  subst l
  induction pre generalizing pre' with
  | nil =>
      cases pre' with
      | nil =>
          have heq : i = j := by simpa using congrArg List.head? h'
          exact absurd heq.symm hji
      | cons a as =>
          have heq : a = i := by simpa using (congrArg List.head? h').symm
          simp [heq]
  | cons a pre ih =>
      cases pre' with
      | nil =>
          have heq : a = j := by simpa using congrArg List.head? h'
          exact absurd (by simp [heq] : j ∈ a :: pre) hjpre
      | cons a' pre' =>
          have heq : a' = a := by simpa using (congrArg List.head? h').symm
          subst a'
          have htail : pre ++ i :: post = pre' ++ j :: post' := by
            simpa using congrArg List.tail h'
          exact List.mem_cons_of_mem _
            (ih (fun hm => hjpre (by simp [hm])) htail)

omit model in
theorem blockInstrDefs_nodup {f : Func} (hnd : f.allDefs.Nodup)
    {b : Block} (hb : b ∈ f.blocks.toList) :
    (b.instrs.flatMap Instr.defs).Nodup :=
  (Passes.instrDefs_nodup hnd).sublist
    (sublist_flatMap_of_mem (fun c => c.instrs.flatMap Instr.defs) hb)

omit model in
/-- Within a block, the representative of a final CSE alias is produced by a
strictly earlier instruction than the alias itself.  This is the intra-block
projection of `Passes.csePrefix_ordered`. -/
theorem cseSub_rep_before {f : Func} (hnd : f.allDefs.Nodup)
    {d d0 : ValId} (hmap : (Passes.cseSub f)[d]? = some d0)
    {b : Block} (hb : b ∈ f.blocks.toList)
    {pre post : List Instr} (hsplit : b.instrs = pre ++ post)
    (hd : d ∈ pre.flatMap Instr.defs)
    (hd0 : d0 ∈ b.instrs.flatMap Instr.defs) :
    d0 ∈ pre.flatMap Instr.defs := by
  classical
  set g : Block → List ValId := fun c => c.instrs.flatMap Instr.defs with hgdef
  have hLnd : (f.blocks.toList.flatMap g).Nodup := Passes.instrDefs_nodup hnd
  have htake : f.blocks.toList.take f.blocks.size = f.blocks.toList := by simp
  have hseenEq : Passes.cseSeen f f.blocks.size = f.blocks.toList.flatMap g := by
    simp only [Passes.cseSeen, htake, hgdef]
  obtain ⟨p, m, q, hord⟩ :=
    Passes.csePrefix_ordered hnd f.blocks.size (Nat.le_refl _) d d0 hmap
  rw [hseenEq] at hord
  obtain ⟨s, t, hst⟩ := List.append_of_mem hb
  have hLsplit : f.blocks.toList.flatMap g =
      (s.flatMap g ++ pre.flatMap Instr.defs) ++
        (post.flatMap Instr.defs ++ t.flatMap g) := by
    rw [hst]
    simp only [List.flatMap_append, List.flatMap_cons]
    have hgb : g b = pre.flatMap Instr.defs ++ post.flatMap Instr.defs := by
      simp [hgdef, hsplit, List.flatMap_append]
    rw [hgb]
    simp [List.append_assoc]
  have hnd2 : ((s.flatMap g ++ pre.flatMap Instr.defs) ++
      (post.flatMap Instr.defs ++ t.flatMap g)).Nodup := by
    rw [← hLsplit]; exact hLnd
  have heq2 : (s.flatMap g ++ pre.flatMap Instr.defs) ++
      (post.flatMap Instr.defs ++ t.flatMap g) = p ++ d0 :: (m ++ d :: q) := by
    rw [← hLsplit, hord]
    simp [List.append_assoc]
  have hdq : d ∈ m ++ d :: q := List.mem_append_right _ (by simp)
  have hd1 : d ∈ s.flatMap g ++ pre.flatMap Instr.defs :=
    List.mem_append_right _ hd
  have hmem := mem_left_of_before hnd2 heq2 hdq hd1
  rcases List.mem_append.mp hmem with hs | hpre
  · exfalso
    have hLsplit2 : f.blocks.toList.flatMap g =
        s.flatMap g ++ (g b ++ t.flatMap g) := by
      rw [hst]; simp [List.flatMap_append, List.flatMap_cons]
    have hnd3 : (s.flatMap g ++ (g b ++ t.flatMap g)).Nodup := by
      rw [← hLsplit2]; exact hLnd
    exact (List.nodup_append.mp hnd3).2.2 d0 hs d0
      (List.mem_append_left _ hd0) rfl
  · exact hpre

/-! ### The CSE register invariant -/

/-- `d`'s definition site has already been passed when block `cur` is being
executed with processed instruction prefix `pre`: the unique block defining `d`
dominates `cur`, and when that block *is* `cur` the defining instruction lies in
the processed prefix. -/
def CseSeen (f : Func) (cur : BlockId) (pre : List Instr) (d : ValId) : Prop :=
  ∃ di db, f.blocks[di]? = some db ∧ d ∈ db.instrs.flatMap Instr.defs ∧
    BlockDom f di cur ∧ (di = cur → d ∈ pre.flatMap Instr.defs)

omit model in
theorem CseSeen.mono {f : Func} {cur : BlockId} {pre pre' : List Instr}
    {d : ValId} (h : CseSeen f cur pre d)
    (hsub : ∀ x ∈ pre.flatMap Instr.defs, x ∈ pre'.flatMap Instr.defs) :
    CseSeen f cur pre' d := by
  obtain ⟨di, db, hdb, hdef, hdom, hloc⟩ := h
  exact ⟨di, db, hdb, hdef, hdom, fun heq => hsub _ (hloc heq)⟩

omit model in
/-- Nothing is seen before the first instruction of the entry block. -/
theorem CseSeen.entry_elim {f : Func} {d : ValId}
    (h : CseSeen f f.entry [] d) : False := by
  obtain ⟨di, db, hdb, hdef, hdom, hloc⟩ := h
  rcases hdom [] EntryPath.entry with heq | hmem
  · simpa using hloc heq
  · simp at hmem

/-- A value read in block `cur` is seen there: its defining block dominates
`cur`, and the caller supplies the same-block prefix guard. -/
theorem cseSeen_of_use {f : Func} {li : Array (List ValId)}
    (hnd : f.allDefs.Nodup) (hli : ToAsm.liveInSets f = some li)
    (hdom : ToAsm.Func.domCheck f = true)
    {cur : BlockId} {b : Block} (hb : f.blocks[cur]? = some b)
    {pre : List Instr} {x d0 : ValId}
    (hmap : (Passes.cseSub f)[x]? = some d0)
    (hxuse : x ∈ ToAsm.blockUses b)
    (hlocal : x ∈ b.instrs.flatMap Instr.defs → x ∈ pre.flatMap Instr.defs) :
    CseSeen f cur pre x := by
  obtain ⟨⟨b1, hb1, i, hi, hxd⟩, -⟩ := Passes.cseSub_def_site hnd hmap
  obtain ⟨di, hdi⟩ := Passes.block_index_of_mem hb1
  have hxflat : x ∈ b1.instrs.flatMap Instr.defs := List.mem_flatMap.mpr ⟨i, hi, hxd⟩
  have hxdef : x ∈ ToAsm.blockDefs b1 := ToAsm.mem_blockDefs.mpr (Or.inr hxflat)
  refine ⟨di, b1, hdi, hxflat,
    blockDef_dominates_use hnd hli hdom hdi hxdef hb hxuse, ?_⟩
  intro heq
  subst di
  have hbb : b1 = b := Option.some.inj (hdi.symm.trans hb)
  subst b1
  exact hlocal hxflat

omit model in
/-- A seen definition is not produced by any instruction still ahead of it in
its own block. -/
theorem CseSeen.not_defined_later {f : Func} (hnd : f.allDefs.Nodup)
    {cur : BlockId} {b : Block} (hb : f.blocks[cur]? = some b)
    {pre post : List Instr} (hsplit : b.instrs = pre ++ post)
    {d : ValId} (h : CseSeen f cur pre d) : d ∉ post.flatMap Instr.defs := by
  intro hd
  obtain ⟨di, db, hdb, hddef, hdom, hloc⟩ := h
  have hdb1 : d ∈ ToAsm.blockDefs db := ToAsm.mem_blockDefs.mpr (Or.inr hddef)
  have hdb2 : d ∈ ToAsm.blockDefs b := by
    refine ToAsm.mem_blockDefs.mpr (Or.inr ?_)
    rw [hsplit, List.flatMap_append]
    exact List.mem_append_right _ hd
  have heq : di = cur := Passes.block_def_index_unique hnd hdb hb hdb1 hdb2
  have hpre := hloc heq
  have hnodup : (b.instrs.flatMap Instr.defs).Nodup :=
    blockInstrDefs_nodup hnd (block_mem_of_getElem? hb)
  rw [hsplit, List.flatMap_append, List.nodup_append] at hnodup
  exact hnodup.2.2 d hpre d hd rfl

/-- Whenever a dropped definition is seen, so is its representative.  Same-block
representatives use the intra-block alias order; inherited ones use the
dominance zone of `cse_alias_zone`. -/
theorem CseSeen.rep {f : Func} {n : Nat} (hnd : f.allDefs.Nodup)
    (hwf : f.wfCheck n = true)
    {cur : BlockId} {b : Block} (hb : f.blocks[cur]? = some b)
    {path : List BlockId} (hpath : EntryPath f path cur)
    {pre post : List Instr} (hsplit : b.instrs = pre ++ post)
    {d d0 : ValId} (hmap : (Passes.cseSub f)[d]? = some d0)
    (h : CseSeen f cur pre d) : CseSeen f cur pre d0 := by
  obtain ⟨di, db, hdb, hddef, hdom, hloc⟩ := h
  obtain ⟨-, ⟨rb, hrbmem, i0, hi0, hr0⟩⟩ := Passes.cseSub_def_site hnd hmap
  obtain ⟨ri, hrb⟩ := Passes.block_index_of_mem hrbmem
  have hrflat : d0 ∈ rb.instrs.flatMap Instr.defs := List.mem_flatMap.mpr ⟨i0, hi0, hr0⟩
  have hzone := cse_alias_zone (model := model) hnd hwf hmap hdb
    (ToAsm.mem_blockDefs.mpr (Or.inr hddef)) hrb
    (ToAsm.mem_blockDefs.mpr (Or.inr hrflat))
  rcases hzone with heq | hs
  · subst heq
    have hrbdb : rb = db := Option.some.inj (hrb.symm.trans hdb)
    subst rb
    refine ⟨ri, db, hdb, hrflat, hdom, ?_⟩
    intro hcur
    have hdbb : db = b := by
      subst hcur
      exact Option.some.inj (hdb.symm.trans hb)
    subst db
    exact cseSub_rep_before hnd hmap (block_mem_of_getElem? hb) hsplit
      (hloc hcur) hrflat
  · refine ⟨ri, rb, hrb, hrflat, BlockDom.trans hs.blockDom hdom, ?_⟩
    intro hcur
    subst hcur
    exact absurd hdom (hs.not_reverse hpath)

/-- Register agreement between the source function and its CSE'd form.  Off the
substitution's domain the two register files are *equal*; on it, a dropped
definition agrees with its representative once its definition site is passed. -/
def CseAgree (f : Func) (cur : BlockId) (pre : List Instr) (R R' : Regs) : Prop :=
  (∀ x, (Passes.cseSub f)[x]? = none → R x = R' x) ∧
  (∀ {d d0 : ValId}, (Passes.cseSub f)[d]? = some d0 → CseSeen f cur pre d →
    R d = R' d0)

omit model in
theorem CseAgree.of_entry {f : Func} {cur : BlockId} {R : Regs}
    (hcur : cur = f.entry) : CseAgree f cur [] R R := by
  refine ⟨fun x _ => rfl, ?_⟩
  intro d d0 _ hseen
  subst hcur
  exact absurd hseen (fun h => h.entry_elim)

omit model in
/-- The read leaf: a source read of `x` transports to a read of `substV τ x`. -/
theorem CseAgree.get {f : Func} {cur : BlockId} {pre : List Instr} {R R' : Regs}
    (ha : CseAgree f cur pre R R') {x : ValId}
    (hx : (Passes.cseSub f)[x]? = none ∨ CseSeen f cur pre x) :
    R x = R' (Passes.substV (Passes.cseSub f) x) := by
  cases hxm : (Passes.cseSub f)[x]? with
  | none =>
      rw [Passes.substV, Std.HashMap.getD_eq_getD_getElem?, hxm]
      exact ha.1 x hxm
  | some d0 =>
      rw [Passes.substV, Std.HashMap.getD_eq_getD_getElem?, hxm]
      rcases hx with hn | hs
      · rw [hn] at hxm; exact absurd hxm (by simp)
      · exact ha.2 hxm hs

omit model in
theorem CseAgree.getMany {f : Func} {cur : BlockId} {pre : List Instr} {R R' : Regs}
    (ha : CseAgree f cur pre R R') {xs : List ValId}
    (hx : ∀ x ∈ xs, (Passes.cseSub f)[x]? = none ∨ CseSeen f cur pre x)
    {vs : List U256} (hg : R.getMany xs = some vs) :
    R'.getMany (Passes.substVs (Passes.cseSub f) xs) = some vs :=
  Regs.getMany_substVs (fun x hxm => ha.get (hx x hxm)) hg


/-- Stepping past a *kept* instruction: both sides bind the same destinations to
the same words. -/
theorem CseAgree.step_kept {f : Func} {n : Nat} (hnd : f.allDefs.Nodup)
    (hwf : f.wfCheck n = true)
    {cur : BlockId} {b : Block} (hb : f.blocks[cur]? = some b)
    {path : List BlockId} (hpath : EntryPath f path cur)
    {pre post : List Instr} {i : Instr} (hsplit : b.instrs = pre ++ i :: post)
    {R R' : Regs} (ha : CseAgree f cur pre R R')
    (hkept : ∀ x ∈ i.defs, (Passes.cseSub f)[x]? = none) (vs : List U256) :
    CseAgree f cur (pre ++ [i]) (R.setMany i.defs vs) (R'.setMany i.defs vs) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    exact Regs.setMany_congr (S := fun y => (Passes.cseSub f)[y]? = none)
      ha.1 _ _ x hx
  · intro d d0 hmap hseen
    have hdold : CseSeen f cur pre d := by
      obtain ⟨di, db, hdb, hddef, hdom, hloc⟩ := hseen
      refine ⟨di, db, hdb, hddef, hdom, ?_⟩
      intro heq
      have hmem := hloc heq
      rw [List.flatMap_append] at hmem
      rcases List.mem_append.mp hmem with h | h
      · exact h
      · exfalso
        have hdi : d ∈ i.defs := by simpa using h
        rw [hkept d hdi] at hmap
        exact absurd hmap (by simp)
    have hd0old : CseSeen f cur pre d0 :=
      CseSeen.rep (model := model) hnd hwf hb hpath hsplit hmap hdold
    have hdnot : d ∉ i.defs := fun hdi =>
      (CseSeen.not_defined_later hnd hb hsplit hdold) (by simp [hdi])
    have hd0not : d0 ∉ i.defs := fun hdi =>
      (CseSeen.not_defined_later hnd hb hsplit hd0old) (by simp [hdi])
    rw [Regs.setMany_of_not_mem R i.defs vs hdnot,
      Regs.setMany_of_not_mem R' i.defs vs hd0not]
    exact ha.2 hmap hdold

omit model in
/-- Stepping past a *dropped* instruction: only the source binds its
destination, and the representative already holds the value. -/
theorem CseAgree.step_dropped {f : Func} {cur : BlockId}
    {pre : List Instr} {i : Instr} {d d0 : ValId} {w : U256}
    (hidefs : i.defs = [d]) (hmapd : (Passes.cseSub f)[d]? = some d0)
    {R R' : Regs} (ha : CseAgree f cur pre R R') (hval : R' d0 = some w) :
    CseAgree f cur (pre ++ [i]) (R.set d w) R' := by
  refine ⟨?_, ?_⟩
  · intro x hx
    have hxd : x ≠ d := by
      intro heq; subst x; rw [hmapd] at hx; exact absurd hx (by simp)
    rw [Regs.set_other _ _ hxd]
    exact ha.1 x hx
  · intro d1 d1' hmap1 hseen1
    by_cases hd1 : d1 = d
    · subst d1
      have : d1' = d0 := Option.some.inj (hmap1.symm.trans hmapd)
      subst d1'
      rw [Regs.set_same]
      exact hval.symm
    · have hold : CseSeen f cur pre d1 := by
        obtain ⟨di, db, hdb, hddef, hdom, hloc⟩ := hseen1
        refine ⟨di, db, hdb, hddef, hdom, ?_⟩
        intro heq
        have hmem := hloc heq
        rw [List.flatMap_append] at hmem
        rcases List.mem_append.mp hmem with h | h
        · exact h
        · exact absurd (by simpa [hidefs] using h) hd1
      rw [Regs.set_other _ _ hd1]
      exact ha.2 hmap1 hold

/-- Crossing an edge: block parameters are never dropped, so the two register
files are extended identically, and the target's seen set is transported back
across the edge by `BlockDom.pred`. -/
theorem CseAgree.jump {f : Func} (hnd : f.allDefs.Nodup)
    {cur : BlockId} {b : Block} (hb : f.blocks[cur]? = some b)
    {path : List BlockId} (hpath : EntryPath f path cur)
    {e : Edge} (he : e ∈ b.term.edges)
    {tb : Block} (htb : f.blocks[e.target]? = some tb)
    {R R' : Regs} (ha : CseAgree f cur b.instrs R R') (vals : List U256) :
    CseAgree f e.target [] (R.setMany tb.params vals) (R'.setMany tb.params vals) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    exact Regs.setMany_congr (S := fun y => (Passes.cseSub f)[y]? = none)
      ha.1 _ _ x hx
  · intro d d0 hmap hseen
    obtain ⟨di, db, hdb, hddef, hdom, hloc⟩ := hseen
    have hne : di ≠ e.target := by
      intro heq; simpa using hloc heq
    have hcur : CseSeen f cur b.instrs d := by
      refine ⟨di, db, hdb, hddef, hdom.pred hpath hb he rfl hne, ?_⟩
      intro heq
      subst heq
      have hdbb : db = b := Option.some.inj (hdb.symm.trans hb)
      subst db
      exact hddef
    have hdnot : d ∉ tb.params := by
      intro hp
      obtain ⟨i1, hi1, hd1⟩ := List.mem_flatMap.mp hddef
      exact param_not_instr_def hnd (block_mem_of_getElem? htb)
        (block_mem_of_getElem? hdb) hi1 hp hd1
    have hd0not : d0 ∉ tb.params := by
      intro hp
      obtain ⟨-, ⟨rb, hrbmem, i0, hi0, hr0⟩⟩ := Passes.cseSub_def_site hnd hmap
      exact param_not_instr_def hnd (block_mem_of_getElem? htb) hrbmem hi0 hp hr0
    rw [Regs.setMany_of_not_mem R tb.params vals hdnot,
      Regs.setMany_of_not_mem R' tb.params vals hd0not]
    exact ha.2 hmap hcur

/-- The block defining the representative of a rewritten use dominates the block
that reads it: this is the runtime counterpart of `cse_dom`. -/
theorem cseSub_use_dom {f : Func} {li : Array (List ValId)} {n : Nat}
    (hnd : f.allDefs.Nodup) (hli : ToAsm.liveInSets f = some li)
    (hdomc : ToAsm.Func.domCheck f = true) (hwf : f.wfCheck n = true)
    {i : BlockId} {b : Block} (hb : f.blocks[i]? = some b)
    {x d0 : ValId} (hmap : (Passes.cseSub f)[x]? = some d0)
    (hx : x ∈ ToAsm.blockUses b)
    {ri : BlockId} {rb : Block} (hrb : f.blocks[ri]? = some rb)
    (hrdef : d0 ∈ ToAsm.blockDefs rb) : BlockDom f ri i := by
  obtain ⟨⟨b1, hb1, i1, hi1, hxd⟩, -⟩ := Passes.cseSub_def_site hnd hmap
  obtain ⟨xi, hxi⟩ := Passes.block_index_of_mem hb1
  have hxdef : x ∈ ToAsm.blockDefs b1 :=
    ToAsm.mem_blockDefs.mpr (Or.inr (List.mem_flatMap.mpr ⟨i1, hi1, hxd⟩))
  have hdomx : BlockDom f xi i := blockDef_dominates_use hnd hli hdomc hxi hxdef hb hx
  rcases cse_alias_zone (model := model) hnd hwf hmap hxi hxdef hrb hrdef with rfl | hs
  · exact hdomx
  · exact BlockDom.trans hs.blockDom hdomx

/-- The drop leaf: at a dropped pure operation the source's own evaluation is
transported onto the table representative.  `hkey` is the fold's key equation —
the entry was matched on the current instruction's substituted arguments — after
the final substitution has absorbed the intermediate one. -/
theorem CseAgree.drop_value {f : Func} {cur : BlockId} {pre : List Instr}
    {R R' : Regs} (ha : CseAgree f cur pre R R')
    {yop : Op} {as args : List ValId} {d0 : ValId}
    (hrt : CseExprRuntime (model := model) (Passes.cseSub f) R' (.op yop args) d0)
    (hkey : Passes.substVs (Passes.cseSub f) args = Passes.substVs (Passes.cseSub f) as)
    (hp : Passes.pureOp yop = true)
    (hargs : ∀ x ∈ as, (Passes.cseSub f)[x]? = none ∨ CseSeen f cur pre x)
    {vals rets : List U256} {st st' : EvmState}
    (hg : R.getMany as = some vals)
    (hbi : builtinWithExternal model.calls model.creates yop vals st (.ok rets st')) :
    ∃ w, rets = [w] ∧ R' d0 = some w := by
  have hg' : R'.getMany (Passes.substVs (Passes.cseSub f) args) = some vals := by
    rw [hkey]
    exact ha.getMany hargs hg
  exact CseExprRuntime.op_result hrt hp hg' hbi

/-- Every representative available at a mid-block fold position has already been
defined: either by an already-processed instruction of the current block, or in
a block that strictly dominates it.  This is the mid-block refinement of
`Passes.cseBlock_spec`'s table clause, and it is what supplies `CseSeen` for a
representative at the moment its alias is dropped. -/
theorem cseSeen_of_tabVal {f : Func} {n : Nat} (hnd : f.allDefs.Nodup)
    (hwf : f.wfCheck n = true)
    {cur : BlockId} {b : Block} (hb : f.blocks[cur]? = some b)
    {path : List BlockId} (hpath : EntryPath f path cur)
    {pre post : List Instr} (hsplit : b.instrs = pre ++ post)
    {used defined blockDefs : Std.HashSet ValId} {σ : Passes.Subst}
    {x : ValId}
    (hx : x ∈ Passes.cseTabVals (pre.foldl (fun s i => Passes.cseInstrStep i s)
      ⟨[], Passes.cseEntryTab f (Passes.inEdgeSources f)
        (Passes.csePrefix f cur).2.1 cur, used, σ, defined, blockDefs⟩).2.1) :
    CseSeen f cur pre x := by
  have hcur : cur < f.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  rcases Passes.cseInstrFold_tabVals pre [] _ used σ defined blockDefs hx with
    havail | hout
  · -- inherited from a strictly dominating block
    have hsound := Passes.cseEntryTab_sound hnd (Nat.le_of_lt hcur)
    have hdef : ∃ e, Passes.CseDef f e x := by
      rcases List.mem_append.mp havail with h | h
      · obtain ⟨⟨⟨yop, as⟩, d⟩, hm, hxd⟩ := List.mem_map.mp h
        have hd : d = x := hxd
        subst hd
        exact ⟨_, hsound.1.1 hm⟩
      · obtain ⟨⟨v, d⟩, hm, hxd⟩ := List.mem_map.mp h
        have hd : d = x := hxd
        subst hd
        exact ⟨_, hsound.1.2 hm⟩
    obtain ⟨e, hcd⟩ := hdef
    obtain ⟨b1, hb1, i1, hi1, hxd⟩ := hcd.site
    obtain ⟨di, hdi⟩ := Passes.block_index_of_mem hb1
    have hxflat : x ∈ b1.instrs.flatMap Instr.defs := List.mem_flatMap.mpr ⟨i1, hi1, hxd⟩
    have hs : StrictBlockDom f di cur := cseAvail_strict_dom hnd hwf hdi
      (ToAsm.mem_blockDefs.mpr (Or.inr hxflat)) havail
    refine ⟨di, b1, hdi, hxflat, hs.blockDom, ?_⟩
    intro heq
    subst heq
    exact absurd (BlockDom.refl f di) (hs.not_reverse hpath)
  · rcases Passes.cseInstrFold_defs_source pre [] _ used σ defined blockDefs hout with
      hnil | hlocal
    · simp at hnil
    · refine ⟨cur, b, hb, ?_, BlockDom.refl f cur, fun _ => hlocal⟩
      rw [hsplit, List.flatMap_append]
      exact List.mem_append_left _ hlocal

/-- Values whose CSE certificate is a literal constant can only contain that
literal once bound.  This is the small value-sensitive companion to the
site-only `BindingProvenance` invariant. -/
def CseConstRegs (f : Func) (R : Regs) : Prop :=
  ∀ {d v w}, Passes.CseDef f (.const v) d → R d = some w → w = v

theorem cseConstRegs_entry {f : Func} (hnd : f.allDefs.Nodup)
    (args : List U256) : CseConstRegs f (Regs.empty.setMany f.params args) := by
  intro d v w hc hr
  obtain ⟨b, hb, i, hi, hd⟩ := hc.site
  have hnot : d ∉ f.params := by
    intro hp
    exact funcParam_not_instr_def hnd hb hi hp hd
  rw [Regs.setMany_of_not_mem _ f.params args hnot] at hr
  simp [Regs.empty] at hr

theorem CseConstRegs.params {f : Func} (hnd : f.allDefs.Nodup)
    {R : Regs} (hR : CseConstRegs f R) {b : Block}
    (hb : b ∈ f.blocks.toList) (vals : List U256) :
    CseConstRegs f (R.setMany b.params vals) := by
  intro d v w hc hr
  obtain ⟨b0, hb0, i, hi, hd⟩ := hc.site
  have hnot : d ∉ b.params := by
    intro hp
    exact param_not_instr_def hnd hb hb0 hi hp hd
  rw [Regs.setMany_of_not_mem _ b.params vals hnot] at hr
  exact hR hc hr

theorem CseConstRegs.const {f : Func} (hnd : f.allDefs.Nodup)
    {b : Block} (hb : b ∈ f.blocks.toList) {d : ValId} {v : U256}
    (hi : .const d v ∈ b.instrs) {R : Regs} (hR : CseConstRegs f R) :
    CseConstRegs f (R.set d v) := by
  intro x u w hc hr
  by_cases hxd : x = d
  · subst x
    simp at hr
    subst w
    cases hc with
    | @const b0 _ u hb0 hi0 =>
        have heq : Instr.const d v = Instr.const d u :=
          instr_def_unique (d := d) hnd hb hb0 hi hi0
          (by simp [Instr.defs]) (by simp [Instr.defs])
        injection heq
  · rw [Regs.set_other _ _ hxd] at hr
    exact hR hc hr

theorem CseConstRegs.nonconst {f : Func} (hnd : f.allDefs.Nodup)
    {b : Block} (hb : b ∈ f.blocks.toList) {i : Instr} (hi : i ∈ b.instrs)
    (hn : ∀ d v, i ≠ .const d v) {R : Regs} (hR : CseConstRegs f R)
    (vals : List U256) : CseConstRegs f (R.setMany i.defs vals) := by
  intro d v w hc hr
  have hnot : d ∉ i.defs := by
    intro hd
    cases hc with
    | @const b0 _ v hb0 hi0 =>
        have heq := instr_def_unique hnd hb hb0 hi hi0 hd (by simp [Instr.defs])
        exact hn _ _ heq
  rw [Regs.setMany_of_not_mem _ i.defs vals hnot] at hr
  exact hR hc hr

/-- Constant aliases agree globally, including the stale interval before their
definition on a loop revisit.  Operation aliases use `CseSeen`; constants need
this stronger clause because re-executing their representative writes the same
literal and therefore cannot invalidate an already-bound alias. -/
def CseConstAgree (f : Func) (R R' : Regs) : Prop :=
  ∀ {d d0 v}, (Passes.cseSub f)[d]? = some d0 →
    Passes.CseDef f (.const v) d → Passes.CseDef f (.const v) d0 →
    R d = none ∨ R d = R' d0

theorem cseConstAgree_entry {f : Func} (hnd : f.allDefs.Nodup)
    (args : List U256) :
    CseConstAgree f (Regs.empty.setMany f.params args)
      (Regs.empty.setMany f.params args) := by
  intro d d0 v hmap hd hd0
  obtain ⟨b, hb, i, hi, hdd⟩ := hd.site
  have hnot : d ∉ f.params := by
    intro hp
    exact funcParam_not_instr_def hnd hb hi hp hdd
  left
  rw [Regs.setMany_of_not_mem _ f.params args hnot]
  rfl

theorem CseConstAgree.params {f : Func} (hnd : f.allDefs.Nodup)
    {R R' : Regs} (ha : CseConstAgree f R R') {b : Block}
    (hb : b ∈ f.blocks.toList) (vals : List U256) :
    CseConstAgree f (R.setMany b.params vals) (R'.setMany b.params vals) := by
  intro d d0 v hmap hd hd0
  obtain ⟨bd, hbd, id, hid, hdd⟩ := hd.site
  obtain ⟨br, hbr, ir, hir, hdr⟩ := hd0.site
  have hdn : d ∉ b.params := fun hp => param_not_instr_def hnd hb hbd hid hp hdd
  have hd0n : d0 ∉ b.params := fun hp => param_not_instr_def hnd hb hbr hir hp hdr
  rw [Regs.setMany_of_not_mem _ b.params vals hdn,
    Regs.setMany_of_not_mem _ b.params vals hd0n]
  exact ha hmap hd hd0

theorem CseConstAgree.nonconst {f : Func} (hnd : f.allDefs.Nodup)
    {R R' : Regs} (ha : CseConstAgree f R R')
    {b : Block} (hb : b ∈ f.blocks.toList) {i : Instr} (hi : i ∈ b.instrs)
    (hn : ∀ d v, i ≠ .const d v) (vals : List U256) :
    CseConstAgree f (R.setMany i.defs vals) (R'.setMany i.defs vals) := by
  intro d d0 v hmap hd hd0
  have hdn : d ∉ i.defs := by
    intro hdi
    cases hd with
    | @const bd _ v hbd hid =>
        exact hn _ _ (instr_def_unique hnd hb hbd hi hid hdi (by simp [Instr.defs]))
  have hd0n : d0 ∉ i.defs := by
    intro hdi
    cases hd0 with
    | @const br _ v hbr hir =>
        exact hn _ _ (instr_def_unique hnd hb hbr hi hir hdi (by simp [Instr.defs]))
  rw [Regs.setMany_of_not_mem _ i.defs vals hdn,
    Regs.setMany_of_not_mem _ i.defs vals hd0n]
  exact ha hmap hd hd0

theorem CseConstAgree.nonconst_left {f : Func} (hnd : f.allDefs.Nodup)
    {R R' : Regs} (ha : CseConstAgree f R R')
    {b : Block} (hb : b ∈ f.blocks.toList) {i : Instr} (hi : i ∈ b.instrs)
    (hn : ∀ d v, i ≠ .const d v) (vals : List U256) :
    CseConstAgree f (R.setMany i.defs vals) R' := by
  intro d d0 v hmap hd hd0
  have hdn : d ∉ i.defs := by
    intro hdi
    cases hd with
    | @const bd _ v hbd hid =>
        exact hn _ _ (instr_def_unique hnd hb hbd hi hid hdi (by simp [Instr.defs]))
  rw [Regs.setMany_of_not_mem _ i.defs vals hdn]
  exact ha hmap hd hd0

theorem CseConstAgree.const_kept {f : Func} (hnd : f.allDefs.Nodup)
    {R R' : Regs} (ha : CseConstAgree f R R') (hR : CseConstRegs f R)
    {b : Block} (hb : b ∈ f.blocks.toList) {d : ValId} {v : U256}
    (hi : .const d v ∈ b.instrs) (hdnone : (Passes.cseSub f)[d]? = none) :
    CseConstAgree f (R.set d v) (R'.set d v) := by
  intro x x0 u hmap hx hx0
  have hxd : x ≠ d := by
    intro heq
    subst x
    rw [hdnone] at hmap
    contradiction
  by_cases hx0d : x0 = d
  · subst x0
    have huv : u = v := by
      cases hx0 with
      | @const b0 _ u hb0 hi0 =>
          have heq : Instr.const d v = Instr.const d u :=
            instr_def_unique (d := d) hnd hb hb0 hi hi0
              (by simp [Instr.defs]) (by simp [Instr.defs])
          cases heq
          rfl
    subst u
    cases hrx : R x with
    | none =>
        left
        simpa [Regs.set, hxd] using hrx
    | some w =>
        have hw : w = v := hR hx hrx
        subst w
        right
        rw [Regs.set_other _ _ hxd, Regs.set_same]
        exact hrx
  · rw [Regs.set_other _ _ hxd, Regs.set_other _ _ hx0d]
    exact ha hmap hx hx0

theorem CseConstAgree.const_dropped {f : Func} (hnd : f.allDefs.Nodup)
    {R R' : Regs} (ha : CseConstAgree f R R')
    {b : Block} (hb : b ∈ f.blocks.toList) {d d0 : ValId} {v : U256}
    (hi : .const d v ∈ b.instrs) (hmapd : (Passes.cseSub f)[d]? = some d0)
    (hval : R' d0 = some v) : CseConstAgree f (R.set d v) R' := by
  intro x x0 u hmap hx hx0
  by_cases hxd : x = d
  · subst x
    have hx0eq : x0 = d0 := Option.some.inj (hmap.symm.trans hmapd)
    subst x0
    have huv : u = v := by
      cases hx with
      | @const b0 _ u hb0 hi0 =>
          have heq : Instr.const d v = Instr.const d u :=
            instr_def_unique (d := d) hnd hb hb0 hi hi0
              (by simp [Instr.defs]) (by simp [Instr.defs])
          cases heq
          rfl
    subst u
    right
    simpa using hval.symm
  · rw [Regs.set_other _ _ hxd]
    exact ha hmap hx hx0

/-- Successful reads consume the two register clauses: operation aliases must
be past their certified site, while constant aliases use global literal
agreement and therefore also cover a loop's stale pre-definition interval. -/
theorem cseGetMany {f : Func} (hnd : f.allDefs.Nodup)
    {cur : BlockId} {pre : List Instr} {R R' : Regs}
    (ha : CseAgree f cur pre R R') (hc : CseConstAgree f R R')
    {xs : List ValId} {vals : List U256}
    (hseen : ∀ {x d0 yop as}, x ∈ xs → (Passes.cseSub f)[x]? = some d0 →
      Passes.CseDef f (.op yop as) x → CseSeen f cur pre x)
    (hg : R.getMany xs = some vals) :
    R'.getMany (Passes.substVs (Passes.cseSub f) xs) = some vals := by
  apply Regs.getMany_substVs (R := R) (R' := R')
  · intro x hx
    cases hm : (Passes.cseSub f)[x]? with
    | none =>
        rw [Passes.substV, Std.HashMap.getD_eq_getD_getElem?, hm]
        exact ha.1 x hm
    | some d0 =>
        rw [Passes.substV, Std.HashMap.getD_eq_getD_getElem?, hm]
        obtain ⟨e, hdx, hd0⟩ := (Passes.cseFinalSubSound hnd).1 hm
        cases e with
        | const v =>
            rcases hc hm hdx hd0 with hn | heq
            · obtain ⟨w, hw⟩ := Regs.eq_some_of_getMany hg hx
              rw [hn] at hw
              contradiction
            · exact heq
        | op yop as => exact ha.2 hm (hseen hx hm hdx)
  · exact hg

/-- A read of an operation alias is past its certified drop site.  The only
borderline case is a self-read at that site; the caller supplies exactly the
`cse_drop_not_self_use` consequence for the current fold step. -/
theorem cseSeen_of_op_use {f : Func} {li : Array (List ValId)} {n : Nat}
    (hnd : f.allDefs.Nodup) (hli : ToAsm.liveInSets f = some li)
    (hdom : ToAsm.Func.domCheck f = true) (hwf : f.wfCheck n = true)
    {cur : BlockId} {b : Block} (hb : f.blocks[cur]? = some b)
    {pre post : List Instr} {i : Instr} (hsplit : b.instrs = pre ++ i :: post)
    {x d0 yop as} (huse : x ∈ i.uses)
    (hmap : (Passes.cseSub f)[x]? = some d0)
    (hdef : Passes.CseDef f (.op yop as) x)
    (hself : x ∈ i.defs → x ∉ i.uses) : CseSeen f cur pre x := by
  apply cseSeen_of_use hnd hli hdom hb hmap
  · rw [ToAsm.mem_blockUses]
    exact Or.inl (List.mem_flatMap.mpr ⟨i, by rw [hsplit]; simp, huse⟩)
  · intro hlocal
    obtain ⟨e, hdrop, -⟩ := (Passes.cseFinalSubSound hnd).2 hmap
    cases hdrop with
    | @const bd preD postD idrop sigma d v hbD hseqD hsubstD =>
        cases hdef with
        | @op b0 _ yop0 args0 sigma0 hb0 hi0 hp =>
            have hiddefs : idrop.defs = [x] := by
              calc
                idrop.defs = (Passes.substInstr sigma idrop).defs :=
                  (Passes.substInstr_defs sigma idrop).symm
                _ = (Instr.const x v).defs := congrArg Instr.defs hsubstD
                _ = [x] := rfl
            have hidmem : idrop ∈ bd.instrs := by rw [hseqD]; simp
            have heq := instr_def_unique (d := x) hnd hbD hb0 hidmem hi0
              (by rw [hiddefs]; simp) (by simp [Instr.defs])
            subst idrop
            simp [Passes.substInstr] at hsubstD
    | @op bd preD postD idrop sigma d yopD argsD hbD hseqD hsubstD hnone hprefix =>
        have hiddefs : idrop.defs = [x] := by
          rw [← Passes.substInstr_defs sigma idrop, hsubstD]
          rfl
        obtain ⟨di, hdi⟩ := Passes.block_index_of_mem hbD
        have hxbd : x ∈ ToAsm.blockDefs bd := ToAsm.mem_blockDefs.mpr
          (Or.inr (List.mem_flatMap.mpr ⟨idrop, by rw [hseqD]; simp,
            by rw [hiddefs]; simp⟩))
        have hxb : x ∈ ToAsm.blockDefs b := ToAsm.mem_blockDefs.mpr (Or.inr hlocal)
        have hdicur : di = cur := Passes.block_def_index_unique hnd hdi hb hxbd hxb
        subst di
        have hbdb : bd = b := Option.some.inj (hdi.symm.trans hb)
        subst bd
        have hidmem : idrop ∈ pre ++ i :: post := by
          rw [← hsplit, hseqD]
          simp
        rcases List.mem_append.mp hidmem with hidpre | hidtail
        · exact List.mem_flatMap.mpr ⟨idrop, hidpre, by rw [hiddefs]; simp⟩
        · rcases List.mem_cons.mp hidtail with hideq | hidpost
          · subst idrop
            exfalso
            exact hself (by simpa [hiddefs]) huse
          · by_cases hidpre : idrop ∈ pre
            · exact List.mem_flatMap.mpr ⟨idrop, hidpre, by rw [hiddefs]; simp⟩
            · have hne : idrop ≠ i := by
                intro heq
                subst idrop
                exact hself (by simpa [hiddefs]) huse
              have himem : i ∈ preD :=
                mem_prefix_of_later hsplit hidpost hidpre hne hseqD
              exact False.elim (hprefix (List.mem_flatMap.mpr ⟨i, himem, huse⟩))

/-- Runtime entry-table transport along an actually taken CFG edge.  The only
nonempty case of `cseEntryTab` is a unique lower-index predecessor; the source
collector identifies that predecessor with the block just executed. -/
theorem CseTabRuntime.entry_of_edge {f : Func} (hnd : f.allDefs.Nodup)
    {cur : BlockId} {b : Block} (hb : f.blocks[cur]? = some b)
    {e : Edge} (he : e ∈ b.term.edges) {tb : Block}
    (htb : f.blocks[e.target]? = some tb)
    {R : Regs}
    (hr : CseTabRuntime (model := model) (Passes.cseSub f) R
      (Passes.cseBlockTabOut f cur))
    (vals : List U256) :
    CseTabRuntime (model := model) (Passes.cseSub f) (R.setMany tb.params vals)
      (Passes.cseEntryTab f (Passes.inEdgeSources f)
        (Passes.csePrefix f e.target).2.1 e.target) := by
  have ht : e.target < f.blocks.size := (Array.getElem?_eq_some_iff.mp htb).1
  have htbang : f.blocks[e.target]! = tb := by
    rw [Passes.getElem!_eq_getElem ht]
    exact (Array.getElem?_eq_some_iff.mp htb).2
  rw [Passes.cseEntryTab]
  split
  · exact CseTabRuntime.empty _ _
  · rename_i hentry
    cases hs : (Passes.inEdgeSources f)[e.target]! with
    | nil => exact CseTabRuntime.empty _ _
    | cons p ps =>
        cases ps with
        | cons q qs => exact CseTabRuntime.empty _ _
        | nil =>
            by_cases hp : p < e.target
            · simp only [hs, hp, if_true]
              have hcurp : cur = p := Passes.inEdgeSources_single_eq hb he ht hs
              subst p
              rw [Passes.csePrefix_table_to hnd hp (Nat.le_of_lt ht)]
              simpa [Passes.cseSub, htbang] using
                (CseTabRuntime.setMany_inheritTab hnd
                  (Passes.cseFinalSubSound hnd) (block_mem_of_getElem? htb) hr vals)
            · simp only [hs, hp, if_false]
              exact CseTabRuntime.empty _ _

namespace Passes

/-- The CSE fold state at a source instruction boundary, with the emitted-list
accumulator reset (only the other five projections affect subsequent steps). -/
def cseAt (f : Func) (cur : BlockId) (b : Block) (pre : List Instr) : CSEInner :=
  let r := pre.foldl (fun s i => cseInstrStep i s)
    ⟨[], cseEntryTab f (inEdgeSources f) (csePrefix f cur).2.1 cur, ∅,
      (csePrefix f cur).2.2, ∅, cseBlockDefs b⟩
  ⟨[], r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1, r.2.2.2.2.2⟩

def CseFresh (f : Func) : Prop :=
  ∀ {cur : BlockId} {b : Block}, f.blocks[cur]? = some b →
    ∀ {path : List BlockId}, EntryPath f path cur →
    ∀ {pre post : List Instr} {i : Instr}, b.instrs = pre ++ i :: post →
    ∀ d ∈ i.defs,
      (∀ v, i ≠ .const d v) →
      d ∉ cseTabVals (cseAt f cur b pre).2.1 ∧
      d ∉ cseTabRuntimeUses (cseSub f) (cseAt f cur b pre).2.1 ∧
      ((cseInstrStep i (cseAt f cur b pre)).2.1 ≠
        (cseAt f cur b pre).2.1 → d ∉ (substInstr (cseSub f) i).uses)

omit model in
theorem cseAt_nil (f : Func) (cur : BlockId) (b : Block) :
    cseAt f cur b [] =
      ⟨[], cseEntryTab f (inEdgeSources f) (csePrefix f cur).2.1 cur, ∅,
      (csePrefix f cur).2.2, ∅, cseBlockDefs b⟩ := rfl

omit model in
@[simp] theorem cseAt_fst (f : Func) (cur : BlockId) (b : Block)
    (pre : List Instr) : (cseAt f cur b pre).1 = [] := rfl

omit model in
theorem cseAt_full {f : Func} {cur : BlockId} {b : Block}
    (hb : f.blocks[cur]? = some b) :
    (cseAt f cur b b.instrs).2.1 = cseBlockTabOut f cur := by
  have hcur : cur < f.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  have hbang : f.blocks[cur]! = b := by
    rw [getElem!_eq_getElem hcur]
    exact (Array.getElem?_eq_some_iff.mp hb).2
  simp [cseAt, cseBlockTabOut, hbang]

omit model in
theorem cseAt_snoc (f : Func) (cur : BlockId) (b : Block)
    (pre : List Instr) (i : Instr) :
    cseAt f cur b (pre ++ [i]) =
      let s := cseInstrStep i (cseAt f cur b pre)
      ⟨[], s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2⟩ := by
  unfold cseAt
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  let r := pre.foldl (fun s i => cseInstrStep i s)
    ⟨[], cseEntryTab f (inEdgeSources f) (csePrefix f cur).2.1 cur, ∅,
      (csePrefix f cur).2.2, ∅, cseBlockDefs b⟩
  have hs := cseInstrStep_state i r.1 r.2.1 r.2.2.1 r.2.2.2.1
    r.2.2.2.2.1 r.2.2.2.2.2
  change
    (⟨[], (cseInstrStep i r).2.1, (cseInstrStep i r).2.2.1,
      (cseInstrStep i r).2.2.2.1, (cseInstrStep i r).2.2.2.2.1,
      (cseInstrStep i r).2.2.2.2.2⟩ : CSEInner) =
    ⟨[], (cseInstrStep i
      ⟨[], r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1, r.2.2.2.2.2⟩).2.1,
      (cseInstrStep i
        ⟨[], r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1, r.2.2.2.2.2⟩).2.2.1,
      (cseInstrStep i
        ⟨[], r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1, r.2.2.2.2.2⟩).2.2.2.1,
      (cseInstrStep i
        ⟨[], r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1, r.2.2.2.2.2⟩).2.2.2.2.1,
      (cseInstrStep i
        ⟨[], r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1, r.2.2.2.2.2⟩).2.2.2.2.2⟩
  rw [hs]

def CseTabLE (a b : CseTab) : Prop :=
  (∀ e, e ∈ a.ops → e ∈ b.ops) ∧ (∀ e, e ∈ a.consts → e ∈ b.consts)

omit model in
theorem CseTabLE.refl (a : CseTab) : CseTabLE a a :=
  ⟨fun _ h => h, fun _ h => h⟩

omit model in
theorem CseTabLE.trans {a b c : CseTab} (hab : CseTabLE a b)
    (hbc : CseTabLE b c) : CseTabLE a c :=
  ⟨fun e h => hbc.1 e (hab.1 e h), fun e h => hbc.2 e (hab.2 e h)⟩

omit model in
theorem cseInstrStep_tab_mono (i : Instr) (st : CSEInner) :
    CseTabLE st.2.1 (cseInstrStep i st).2.1 := by
  cases i with
  | const d v =>
      simp only [cseInstrStep, substInstr]
      split
      · exact CseTabLE.refl _
      · exact ⟨fun _ h => h, fun e h => by simp [h]⟩
  | call ds fid as => exact CseTabLE.refl _
  | op ds yop as =>
      cases ds with
      | nil => exact CseTabLE.refl _
      | cons d ds =>
          cases ds with
          | cons e es => exact CseTabLE.refl _
          | nil =>
              simp only [cseInstrStep, substInstr]
              split
              · split
                · split <;> exact CseTabLE.refl _
                · split
                  · exact ⟨fun e h => by simp [h], fun _ h => h⟩
                  · exact CseTabLE.refl _
              · exact CseTabLE.refl _

omit model in
theorem cseInstrFold_tab_mono (l : List Instr) (st : CSEInner) :
    CseTabLE st.2.1 (l.foldl (fun s i => cseInstrStep i s) st).2.1 := by
  induction l generalizing st with
  | nil => exact CseTabLE.refl _
  | cons i is ih =>
      rw [List.foldl_cons]
      exact (cseInstrStep_tab_mono i st).trans (ih _)

omit model in
theorem cseInstrFold_snd_congr (l : List Instr) {a b : CSEInner}
    (h : a.2 = b.2) :
    (l.foldl (fun s i => cseInstrStep i s) a).2 =
      (l.foldl (fun s i => cseInstrStep i s) b).2 := by
  induction l generalizing a b with
  | nil => exact h
  | cons i is ih =>
      rw [List.foldl_cons, List.foldl_cons]
      apply ih
      rcases a with ⟨acca, taba, useda, siga, defa, blocka⟩
      rcases b with ⟨accb, tabb, usedb, sigb, defb, blockb⟩
      simp only at h
      cases h
      exact (cseInstrStep_state i acca taba useda siga defa blocka).trans
        (cseInstrStep_state i accb taba useda siga defa blocka).symm

omit model in
theorem CseTabSound.mono {f : Func} {a b : CseTab}
    (h : CseTabSound f b) (hle : CseTabLE a b) : CseTabSound f a := by
  exact ⟨⟨fun hm => h.1.1 (hle.1 _ hm), fun hm => h.1.2 (hle.2 _ hm)⟩,
    fun hm => h.2 (hle.1 _ hm)⟩

omit model in
theorem CseTabDomainSound.mono {f : Func} {τ : Subst} {a b : CseTab}
    (h : CseTabDomainSound f τ b) (hle : CseTabLE a b) :
    CseTabDomainSound f τ a := fun hm => h (hle.1 _ hm)

omit model in
theorem cseAt_tab_le {f : Func} {cur : BlockId} {b : Block}
    (hb : f.blocks[cur]? = some b) {pre post : List Instr}
    (hsplit : b.instrs = pre ++ post) :
    CseTabLE (cseAt f cur b pre).2.1 (cseBlockTabOut f cur) := by
  have hcur : cur < f.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  have hbang : f.blocks[cur]! = b := by
    rw [getElem!_eq_getElem hcur]
    exact (Array.getElem?_eq_some_iff.mp hb).2
  let base : CSEInner :=
    ⟨[], cseEntryTab f (inEdgeSources f) (csePrefix f cur).2.1 cur, ∅,
      (csePrefix f cur).2.2, ∅, cseBlockDefs b⟩
  let r := pre.foldl (fun s i => cseInstrStep i s) base
  let q : CSEInner := ⟨[], r.2.1, r.2.2.1, r.2.2.2.1,
    r.2.2.2.2.1, r.2.2.2.2.2⟩
  have hacc := cseInstrFold_acc_state post r.1 r.2.1 r.2.2.1 r.2.2.2.1
    r.2.2.2.2.1 r.2.2.2.2.2
  have htab : (post.foldl (fun s i => cseInstrStep i s) q).2.1 =
      (b.instrs.foldl (fun s i => cseInstrStep i s) base).2.1 := by
    rw [hsplit, List.foldl_append]
    change (post.foldl (fun s i => cseInstrStep i s) q).2.1 =
      (post.foldl (fun s i => cseInstrStep i s) r).2.1
    have htabeq := congrArg (fun s : CSEInner => s.2.1) hacc
    simpa [q] using htabeq.symm
  have hm := cseInstrFold_tab_mono post q
  simpa [cseAt, cseBlockTabOut, hbang, base, r, q, htab] using hm

omit model in
theorem cseAt_tab_sound {f : Func} (hnd : f.allDefs.Nodup)
    {cur : BlockId} {b : Block} (hb : f.blocks[cur]? = some b)
    {pre post : List Instr} (hsplit : b.instrs = pre ++ post) :
    CseTabSound f (cseAt f cur b pre).2.1 := by
  have hcur : cur < f.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  exact (cseBlockTabOut_sound hnd hcur).mono (cseAt_tab_le hb hsplit)

omit model in
theorem cseAt_inv {f : Func} (hnd : f.allDefs.Nodup)
    {cur : BlockId} {b : Block} (hb : f.blocks[cur]? = some b)
    {pre post : List Instr} (hsplit : b.instrs = pre ++ post) :
    CSEInv f (cseSeen f cur ++ pre.flatMap Instr.defs)
      (cseAt f cur b pre).2.1 (cseAt f cur b pre).2.2.2.1 := by
  have hcur : cur < f.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  have hbmem : b ∈ f.blocks.toList := block_mem_of_getElem? hb
  have hpre := csePrefixInv hnd cur (Nat.le_of_lt hcur)
  have hentry := cseEntryTab_inv hpre
  have hseenNodup : (cseSeen f cur ++ pre.flatMap Instr.defs).Nodup := by
    have hall : (cseSeen f cur ++ b.instrs.flatMap Instr.defs).Nodup := by
      rw [← cseSeen_succ hb]
      exact (instrDefs_nodup hnd).sublist (cseSeen_sublist f (cur + 1))
    refine hall.sublist ?_
    rw [hsplit, List.flatMap_append]
    exact (List.Sublist.refl _).append (List.sublist_append_left _ _)
  have hr := cseInstrFold_inv hbmem hentry pre
    (fun i hi => by rw [hsplit]; exact List.mem_append_left _ hi)
    hseenNodup [] ∅ ∅ (cseBlockDefs b)
  simpa [cseAt] using hr.1

omit model in
theorem cseAt_dest_none {f : Func} (hnd : f.allDefs.Nodup)
    {cur : BlockId} {b : Block} (hb : f.blocks[cur]? = some b)
    {pre post : List Instr} {i : Instr} (hsplit : b.instrs = pre ++ i :: post)
    {d : ValId} (hd : d ∈ i.defs) : (cseAt f cur b pre).2.2.2.1[d]? = none := by
  have hinv := cseAt_inv hnd hb
    (show b.instrs = pre ++ (i :: post) from hsplit)
  by_contra hn
  obtain ⟨d0, hmap⟩ := Option.ne_none_iff_exists'.mp hn
  have hseen := (hinv.2.2.2.1 hmap).1
  have hall : (cseSeen f cur ++ b.instrs.flatMap Instr.defs).Nodup := by
    rw [← cseSeen_succ hb]
    exact (instrDefs_nodup hnd).sublist (cseSeen_sublist f (cur + 1))
  have hall' : ((cseSeen f cur ++ pre.flatMap Instr.defs) ++
      (i.defs ++ post.flatMap Instr.defs)).Nodup := by
    simpa [hsplit, List.flatMap_append, List.flatMap_cons, List.append_assoc] using hall
  have hcurNot : d ∉ cseSeen f cur ++ pre.flatMap Instr.defs := by
    rw [List.nodup_append] at hall'
    intro hm
    exact hall'.2.2 d hm d (List.mem_append_left _ hd) rfl
  exact hcurNot hseen

omit model in
theorem cseAt_substExt {f : Func} (hnd : f.allDefs.Nodup)
    {cur : BlockId} {b : Block} (hb : f.blocks[cur]? = some b)
    {pre post : List Instr} (hsplit : b.instrs = pre ++ post) :
    SubstExt (cseAt f cur b pre).2.2.2.1 (cseSub f) := by
  change SubstExt
    (pre.foldl (fun s i => cseInstrStep i s)
      ⟨[], cseEntryTab f (inEdgeSources f) (csePrefix f cur).2.1 cur, ∅,
        (csePrefix f cur).2.2, ∅, cseBlockDefs b⟩).2.2.2.1 (cseSub f)
  exact cseFold_substExt hnd hb hsplit

omit model in
theorem cseInstrsOut_at_drop {f : Func} {cur : BlockId} {b : Block}
    {pre : List Instr} {i : Instr} {is : List Instr}
    (hs : (cseInstrStep i (cseAt f cur b pre)).1 = []) :
    cseInstrsOut (cseSub f) (i :: is) (cseAt f cur b pre).2.1
        (cseAt f cur b pre).2.2.1 (cseAt f cur b pre).2.2.2.1
        (cseAt f cur b pre).2.2.2.2.1 (cseAt f cur b pre).2.2.2.2.2 =
      cseInstrsOut (cseSub f) is (cseAt f cur b (pre ++ [i])).2.1
        (cseAt f cur b (pre ++ [i])).2.2.1
        (cseAt f cur b (pre ++ [i])).2.2.2.1
        (cseAt f cur b (pre ++ [i])).2.2.2.2.1
        (cseAt f cur b (pre ++ [i])).2.2.2.2.2 := by
  have hs' : (cseInstrStep i
      ⟨[], (cseAt f cur b pre).2.1, (cseAt f cur b pre).2.2.1,
        (cseAt f cur b pre).2.2.2.1, (cseAt f cur b pre).2.2.2.2.1,
        (cseAt f cur b pre).2.2.2.2.2⟩).1 = [] := by
    simpa only [cseAt] using hs
  rw [cseInstrsOut, hs']
  simp only [List.reverse_nil, List.map_nil, List.nil_append, cseAt_snoc]
  rfl

omit model in
theorem cseInstrsOut_at_keep {f : Func} (hnd : f.allDefs.Nodup)
    {cur : BlockId} {b : Block} (hb : f.blocks[cur]? = some b)
    {pre : List Instr} {i : Instr} {is post : List Instr}
    (hsplit : b.instrs = pre ++ i :: post)
    (hs : (cseInstrStep i (cseAt f cur b pre)).1 =
      [substInstr (cseAt f cur b pre).2.2.2.1 i]) :
    cseInstrsOut (cseSub f) (i :: is) (cseAt f cur b pre).2.1
        (cseAt f cur b pre).2.2.1 (cseAt f cur b pre).2.2.2.1
        (cseAt f cur b pre).2.2.2.2.1 (cseAt f cur b pre).2.2.2.2.2 =
      substInstr (cseSub f) i ::
        cseInstrsOut (cseSub f) is (cseAt f cur b (pre ++ [i])).2.1
          (cseAt f cur b (pre ++ [i])).2.2.1
          (cseAt f cur b (pre ++ [i])).2.2.2.1
          (cseAt f cur b (pre ++ [i])).2.2.2.2.1
          (cseAt f cur b (pre ++ [i])).2.2.2.2.2 := by
  have hs' : (cseInstrStep i
      ⟨[], (cseAt f cur b pre).2.1, (cseAt f cur b pre).2.2.1,
        (cseAt f cur b pre).2.2.2.1, (cseAt f cur b pre).2.2.2.2.1,
        (cseAt f cur b pre).2.2.2.2.2⟩).1 =
      [substInstr (cseAt f cur b pre).2.2.2.1 i] := by
    simpa only [cseAt] using hs
  rw [cseInstrsOut, hs']
  simp only [List.reverse_singleton, List.map_singleton, List.singleton_append,
    cseAt_snoc]
  rw [substInstr_absorb (cseAt_substExt hnd hb
    (show b.instrs = pre ++ (i :: post) from hsplit)) (cseSub_rangeFree hnd)]
  rfl

theorem cseAt_tab_domain {f : Func} (hnd : f.allDefs.Nodup)
    {cur : BlockId} {b : Block} (hb : f.blocks[cur]? = some b)
    {pre post : List Instr} (hsplit : b.instrs = pre ++ post) :
    CseTabDomainSound f (cseSub f) (cseAt f cur b pre).2.1 := by
  have hcur : cur < f.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  have hinv : CSEPrefixDomainInv f (cseSub f) (cur + 1) :=
    csePrefixDomainInv hnd (cur + 1) (Nat.succ_le_of_lt hcur)
  have hfull : CseTabDomainSound f (cseSub f)
      (csePrefix f (cur + 1)).2.1[cur]! := hinv cur (by omega)
  rw [csePrefix_table_next hnd hcur] at hfull
  intro yop args d hm
  exact hfull ((cseAt_tab_le hb hsplit).1 _ hm)

omit model in
/-- Once the unique instruction defining `d` has been stepped, no later fold
step can change its substitution entry. -/
theorem cseAt_dest_final {f : Func} (hnd : f.allDefs.Nodup)
    {cur : BlockId} {b : Block} (hb : f.blocks[cur]? = some b)
    {pre post : List Instr} {i : Instr} (hsplit : b.instrs = pre ++ i :: post)
    {d : ValId} (hd : d ∈ i.defs) :
    (cseSub f)[d]? =
      (cseInstrStep i (cseAt f cur b pre)).2.2.2.1[d]? := by
  have hcur : cur < f.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  have hbmem : b ∈ f.blocks.toList := block_mem_of_getElem? hb
  have hbang : f.blocks[cur]! = b := by
    rw [getElem!_eq_getElem hcur]
    exact (Array.getElem?_eq_some_iff.mp hb).2
  let base : CSEInner :=
    ⟨[], cseEntryTab f (inEdgeSources f) (csePrefix f cur).2.1 cur, ∅,
      (csePrefix f cur).2.2, ∅, cseBlockDefs b⟩
  let r := pre.foldl (fun s i => cseInstrStep i s) base
  let q : CSEInner := ⟨[], r.2.1, r.2.2.1, r.2.2.2.1,
    r.2.2.2.2.1, r.2.2.2.2.2⟩
  let s := cseInstrStep i q
  have hpre0 := csePrefixInv hnd cur (Nat.le_of_lt hcur)
  have hentry : CSEInv f (cseSeen f cur) base.2.1 base.2.2.2.1 := by
    simpa [base] using cseEntryTab_inv hpre0
  have hseenNodup :
      (cseSeen f cur ++ b.instrs.flatMap Instr.defs).Nodup := by
    rw [← cseSeen_succ hb]
    exact (instrDefs_nodup hnd).sublist (cseSeen_sublist f (cur + 1))
  have hpreNodup :
      (cseSeen f cur ++ pre.flatMap Instr.defs).Nodup := by
    refine hseenNodup.sublist ?_
    rw [hsplit, List.flatMap_append, List.flatMap_cons]
    exact (List.Sublist.refl _).append (List.sublist_append_left _ _)
  have hrInv := cseInstrFold_inv hbmem hentry pre
    (fun j hj => by rw [hsplit]; exact List.mem_append_left _ hj)
    hpreNodup [] ∅ ∅ (cseBlockDefs b)
  have hqInv : CSEInv f (cseSeen f cur ++ pre.flatMap Instr.defs)
      q.2.1 q.2.2.2.1 := by simpa [q, r, base] using hrInv.1
  have hstepNodup :
      ((cseSeen f cur ++ pre.flatMap Instr.defs) ++ i.defs).Nodup := by
    refine hseenNodup.sublist ?_
    rw [hsplit, List.flatMap_append, List.flatMap_cons]
    simp [List.append_assoc]
  have hsInv := cseInstrStep_inv hbmem
    (used := q.2.2.1) (defined := q.2.2.2.2.1)
    (blockDefs := q.2.2.2.2.2) hqInv i
    (by rw [hsplit]; simp) hstepNodup
  have hsState := cseInstrStep_state i q.1 q.2.1 q.2.2.1 q.2.2.2.1
    q.2.2.2.2.1 q.2.2.2.2.2
  have hsInv' : CSEInv f
      ((cseSeen f cur ++ pre.flatMap Instr.defs) ++ i.defs) s.2.1 s.2.2.2.1 := by
    dsimp only [s]
    rw [hsState]
    exact hsInv.1
  have htailNodup :
      (((cseSeen f cur ++ pre.flatMap Instr.defs) ++ i.defs) ++
        post.flatMap Instr.defs).Nodup := by
    simpa [hsplit, List.flatMap_append, List.flatMap_cons, List.append_assoc] using
      hseenNodup
  have htailStable := cseInstrFold_stable hbmem hsInv' post
    (fun j hj => by rw [hsplit]; simp [hj]) htailNodup
    s.1 s.2.2.1 s.2.2.2.2.1 s.2.2.2.2.2
  let rend := post.foldl (fun z j => cseInstrStep j z) s
  have hdseen : d ∈ (cseSeen f cur ++ pre.flatMap Instr.defs) ++ i.defs := by
    simp [hd]
  have htailD : rend.2.2.2.1[d]? = s.2.2.2.1[d]? := by
    exact htailStable d hdseen
  have hfullSigma : (csePrefix f (cur + 1)).2.2 = rend.2.2.2.1 := by
    rw [csePrefix_succ]
    simp only [cseBlockStep, hbang]
    rw [hsplit, List.foldl_append, List.foldl_cons]
    change (post.foldl (fun z j => cseInstrStep j z)
      (cseInstrStep i (pre.foldl (fun z j => cseInstrStep j z) base))).2.2.2.1 =
        rend.2.2.2.1
    have hstepSecond := cseInstrStep_state i r.1 r.2.1 r.2.2.1 r.2.2.2.1
      r.2.2.2.2.1 r.2.2.2.2.2
    have hfoldSecond :
        (post.foldl (fun z j => cseInstrStep j z) (cseInstrStep i r)).2 =
          (post.foldl (fun z j => cseInstrStep j z) s).2 := by
      apply cseInstrFold_snd_congr
      simpa [s, q] using hstepSecond
    exact congrArg (fun z => z.2.2.1) hfoldSecond
  have hprefixStable := csePrefix_stable_to hnd (Nat.succ_le_of_lt hcur)
    (Nat.le_refl f.blocks.size)
  have hdSeenGlobal : d ∈ cseSeen f (cur + 1) := by
    rw [cseSeen_succ hb, hsplit, List.flatMap_append, List.flatMap_cons]
    simp [hd]
  rw [cseSub, hprefixStable d hdSeenGlobal, hfullSigma, htailD]
  rfl

theorem cseAt_rep_fresh {f : Func} {n : Nat} (hnd : f.allDefs.Nodup)
    (hwf : f.wfCheck n = true) {cur : BlockId} {b : Block}
    (hb : f.blocks[cur]? = some b) {path : List BlockId}
    (hpath : EntryPath f path cur) {pre post : List Instr} {i : Instr}
    (hsplit : b.instrs = pre ++ i :: post) {d : ValId} (hd : d ∈ i.defs) :
    d ∉ cseTabVals (cseAt f cur b pre).2.1 := by
  intro hm
  have hseen := cseSeen_of_tabVal hnd hwf hb hpath
    (show b.instrs = pre ++ (i :: post) from hsplit) (used := ∅)
    (defined := ∅) (blockDefs := cseBlockDefs b)
    (σ := (csePrefix f cur).2.2) (x := d) (by
      simpa [cseAt] using hm)
  exact hseen.not_defined_later hnd hb hsplit (by
    rw [List.flatMap_cons]
    exact List.mem_append_left _ hd)

/-- The defining instruction of an operation-table representative is either
already in the current prefix or lies in a block dominating the current one. -/
theorem cseAt_entry_before {f : Func} {n : Nat} (hnd : f.allDefs.Nodup)
    (hwf : f.wfCheck n = true) {cur : BlockId} {b : Block}
    (hb : f.blocks[cur]? = some b) {path : List BlockId}
    (hpath : EntryPath f path cur) {pre post : List Instr}
    (hsplit : b.instrs = pre ++ post) {yop : Op} {args : List ValId}
    {r : ValId} (hm : ((yop, args), r) ∈ (cseAt f cur b pre).2.1.ops)
    (he : CseEntryPos f (.op yop args) r) :
    ∃ ri rb j, f.blocks[ri]? = some rb ∧ j ∈ rb.instrs ∧ r ∈ j.defs ∧
      BlockDom f ri cur ∧ (ri = cur → j ∈ pre) := by
  cases he with
  | @op rb preR postR j sigma _ _ _ hbR hseq hsubst hstable =>
      obtain ⟨ri, hri⟩ := block_index_of_mem hbR
      have hjmem : j ∈ rb.instrs := by rw [hseq]; simp
      have hjdef : r ∈ j.defs := by
        rw [← substInstr_defs sigma j, hsubst]
        simp [Instr.defs]
      have hrTab : r ∈ cseTabVals (cseAt f cur b pre).2.1 :=
        List.mem_append_left _ (List.mem_map.mpr ⟨_, hm, rfl⟩)
      obtain ⟨di, db, hdb, hrdef, hrdom, hloc⟩ :=
        cseSeen_of_tabVal hnd hwf hb hpath hsplit (used := ∅)
          (defined := ∅) (blockDefs := cseBlockDefs b)
          (σ := (csePrefix f cur).2.2) hrTab
      have hrbDef : r ∈ ToAsm.blockDefs rb := ToAsm.mem_blockDefs.mpr
        (Or.inr (List.mem_flatMap.mpr ⟨j, hjmem, hjdef⟩))
      have hdbDef : r ∈ ToAsm.blockDefs db :=
        ToAsm.mem_blockDefs.mpr (Or.inr hrdef)
      have hir : ri = di := block_def_index_unique hnd hri hdb hrbDef hdbDef
      subst di
      refine ⟨ri, rb, j, hri, hjmem, hjdef, hrdom, ?_⟩
      intro hcur
      have hrpre := hloc hcur
      obtain ⟨k, hkpre, hkdef⟩ := List.mem_flatMap.mp hrpre
      have hkBlock : k ∈ rb.instrs := by
        have hrbb : rb = b := by
          subst ri
          exact Option.some.inj (hri.symm.trans hb)
        subst rb
        rw [hsplit]
        exact List.mem_append_left _ hkpre
      have heq := instr_def_unique (d := r) hnd hbR hbR hjmem hkBlock hjdef hkdef
      simpa [heq] using hkpre

/-- A non-constant destination cannot overwrite an argument read by an
operation entry already live at the current CSE boundary. -/
theorem cseAt_runtimeUse_fresh_nonconst {f : Func} {li : Array (List ValId)}
    {n : Nat} (hnd : f.allDefs.Nodup) (hwf : f.wfCheck n = true)
    (hli : ToAsm.liveInSets f = some li) (hdom : ToAsm.Func.domCheck f = true)
    {cur : BlockId} {b : Block} (hb : f.blocks[cur]? = some b)
    {path : List BlockId} (hpath : EntryPath f path cur)
    {pre post : List Instr} {i : Instr}
    (hsplit : b.instrs = pre ++ i :: post) {d : ValId} (hd : d ∈ i.defs)
    (hnconst : ∀ v, i ≠ .const d v) :
    d ∉ cseTabRuntimeUses (cseSub f) (cseAt f cur b pre).2.1 := by
  intro huseTab
  simp only [cseTabRuntimeUses, List.mem_flatMap] at huseTab
  obtain ⟨⟨⟨yop, sargs⟩, r⟩, hm, hdargs⟩ := huseTab
  have htabSound := cseAt_tab_sound hnd hb
    (show b.instrs = pre ++ (i :: post) from hsplit)
  have hentry := htabSound.2 hm
  have hdomain := cseAt_tab_domain hnd hb
    (show b.instrs = pre ++ (i :: post) from hsplit) hm
  have hbefore := cseAt_entry_before hnd hwf hb hpath
    (show b.instrs = pre ++ (i :: post) from hsplit) hm hentry
  cases hentry with
  | @op rb preR postR j sigma r yop sargs hbR hseq hsubst hstable =>
      obtain ⟨ri, rb0, j0, hri, hj0mem, hj0def, hrdom, hj0pre⟩ := hbefore
      obtain ⟨rbi, hrbi⟩ := block_index_of_mem hbR
      have hjmem : j ∈ rb.instrs := by rw [hseq]; simp
      have hjdef : r ∈ j.defs := by
        rw [← substInstr_defs sigma j, hsubst]
        simp [Instr.defs]
      have hrbDef : r ∈ ToAsm.blockDefs rb := ToAsm.mem_blockDefs.mpr
        (Or.inr (List.mem_flatMap.mpr ⟨j, hjmem, hjdef⟩))
      have hrb0Def : r ∈ ToAsm.blockDefs rb0 := ToAsm.mem_blockDefs.mpr
        (Or.inr (List.mem_flatMap.mpr ⟨j0, hj0mem, hj0def⟩))
      have hrbiEq : rbi = ri :=
        block_def_index_unique hnd hrbi hri hrbDef hrb0Def
      subst rbi
      have hrbeq : rb = rb0 := Option.some.inj (hrbi.symm.trans hri)
      subst rb0
      have hjeq : j = j0 :=
        instr_def_unique (d := r) hnd hbR hbR hjmem hj0mem hjdef hj0def
      subst j0
      cases hdomain with
      | @op bu ju sigmaU r yop sargs hbU hju hsubstU hdirect horigin =>
          obtain ⟨ui, hui⟩ := block_index_of_mem hbU
          have hjuDef : r ∈ ju.defs := by
            rw [← substInstr_defs sigmaU ju, hsubstU]
            simp [Instr.defs]
          have hbuDef : r ∈ ToAsm.blockDefs bu := ToAsm.mem_blockDefs.mpr
            (Or.inr (List.mem_flatMap.mpr ⟨ju, hju, hjuDef⟩))
          have huiEq : ui = ri :=
            block_def_index_unique hnd hui hri hbuDef hrbDef
          subst ui
          have hbueq : bu = rb := Option.some.inj (hui.symm.trans hri)
          subst bu
          have hjueq : ju = j :=
            instr_def_unique (d := r) hnd hbR hbR hju hjmem hjuDef hjdef
          subst ju
          have hpathRi : ∃ p, EntryPath f p ri := by
            by_cases heq : ri = cur
            · subst ri; exact ⟨path, hpath⟩
            · have hs : StrictBlockDom f ri cur := by
                intro p hp
                exact (hrdom p hp).resolve_left heq
              have hrmem := hs path hpath
              obtain ⟨p, hp, -, -⟩ := hpath.prefix_of_mem hrmem
              exact ⟨p, hp⟩
          obtain ⟨pathRi, hpathRi⟩ := hpathRi
          have hseenNodup : (cseSeen f f.blocks.size).Nodup := by
            have htake : f.blocks.toList.take f.blocks.size = f.blocks.toList := by simp
            simpa [cseSeen, htake] using instrDefs_nodup hnd
          have local_bad (heq : ri = cur)
              (hdpreR : d ∈ preR.flatMap Instr.defs) : False := by
            have hrbb : rb = b := by
              subst ri
              exact Option.some.inj (hri.symm.trans hb)
            have hjpre : j ∈ pre := hj0pre heq
            obtain ⟨k, hkpreR, hkdef⟩ := List.mem_flatMap.mp hdpreR
            have hkBlock : k ∈ b.instrs := by
              rw [← hrbb, hseq]
              exact List.mem_append_left _ hkpreR
            have hieq : i = k :=
              instr_def_unique (d := d) hnd (block_mem_of_getElem? hb)
                (block_mem_of_getElem? hb) (by rw [hsplit]; simp) hkBlock hd hkdef
            have hipreR : i ∈ preR := by simpa [hieq] using hkpreR
            obtain ⟨pa, qa, hpa⟩ := List.mem_iff_append.mp hipreR
            obtain ⟨pb, qb, hpb⟩ := List.mem_iff_append.mp hjpre
            have hDR : Before d r (cseSeen f f.blocks.size) :=
              instr_order_before_mem (block_mem_of_getElem? hb)
                (pre := pa) (mid := qa) (post := postR) (i := i) (j := j)
                (by rw [← hrbb, hseq, hpa]) hd hjdef
            have hRD : Before r d (cseSeen f f.blocks.size) :=
              instr_order_before_mem (block_mem_of_getElem? hb)
                (pre := pb) (mid := qb) (post := post) (i := j) (j := i)
                (by rw [hsplit, hpb]) hjdef hd
            exact (Before.asymm hseenNodup hDR) hRD
          have cross_bad (hne : ri ≠ cur) (hrev : BlockDom f cur ri) : False := by
            have hs : StrictBlockDom f ri cur := by
              intro p hp
              exact (hrdom p hp).resolve_left hne
            exact (hs.not_reverse hpathRi) hrev
          simp only [substVs, List.mem_map] at hdargs
          obtain ⟨a, ha, had⟩ := hdargs
          cases hma : (cseSub f)[a]? with
          | none =>
              have had' : a = d := by
                simpa [substV, Std.HashMap.getD_eq_getD_getElem?, hma] using had
              subst a
              have hnotTail := hstable d ha
              by_cases heq : ri = cur
              · apply local_bad heq
                have hrbb : rb = b := by
                  subst ri
                  exact Option.some.inj (hri.symm.trans hb)
                have hiBlock : i ∈ rb.instrs := by
                  rw [hrbb, hsplit]
                  simp
                rw [hseq] at hiBlock
                rcases List.mem_append.mp hiBlock with hipre | hitail
                · exact List.mem_flatMap.mpr ⟨i, hipre, hd⟩
                · exact False.elim (hnotTail
                    (List.mem_flatMap.mpr ⟨i, hitail, hd⟩))
              · obtain ⟨x, hxj, hxd⟩ := horigin d ha
                have hrev : BlockDom f cur ri := by
                  cases hmx : (cseSub f)[x]? with
                  | none =>
                      have hxeq : x = d := by
                        have := hxd.trans had
                        simpa [substV, Std.HashMap.getD_eq_getD_getElem?,
                          hmx, hma] using this
                      subst x
                      exact blockDef_dominates_use hnd hli hdom hb
                        (ToAsm.mem_blockDefs.mpr (Or.inr
                          (List.mem_flatMap.mpr ⟨i, by rw [hsplit]; simp, hd⟩)))
                        hri (instr_use_mem_blockUses hjmem hxj)
                  | some y =>
                      have hyeq : y = d := by
                        have := hxd.trans had
                        simpa [substV, Std.HashMap.getD_eq_getD_getElem?,
                          hmx, hma] using this
                      subst y
                      exact cseSub_use_dom hnd hli hdom hwf hri hmx
                        (instr_use_mem_blockUses hjmem hxj) hb
                        (ToAsm.mem_blockDefs.mpr (Or.inr
                          (List.mem_flatMap.mpr ⟨i, by rw [hsplit]; simp, hd⟩)))
                exact False.elim (cross_bad heq hrev)
          | some d0 =>
              have hd0 : d0 = d := by
                simpa [substV, Std.HashMap.getD_eq_getD_getElem?, hma] using had
              subst d0
              obtain ⟨e, hdefA, hdefD⟩ := (cseFinalSubSound hnd).1 hma
              cases e with
              | const v =>
                  cases hdefD with
                  | @const bd _ v hbd hid =>
                      have heqi := instr_def_unique (d := d) hnd
                        (block_mem_of_getElem? hb) hbd (by rw [hsplit]; simp) hid
                        hd (by simp [Instr.defs])
                      exact hnconst v heqi
              | op yo aa =>
                  have haju : a ∈ j.uses := hdirect a ha (by rw [hma]; simp)
                  have hself : a ∈ j.defs → a ∉ j.uses := by
                    intro hajdef hajuse
                    exact (hstable a ha)
                      (List.mem_flatMap.mpr ⟨j, by simp, hajdef⟩)
                  have hseenA := cseSeen_of_op_use hnd hli hdom hwf hri hseq
                    haju hma hdefA hself
                  have hseenD := CseSeen.rep (model := model) hnd hwf hri hpathRi
                    hseq hma hseenA
                  obtain ⟨di, db, hdb, hdflat, hdomD, hlocD⟩ := hseenD
                  have hdcur : d ∈ ToAsm.blockDefs b := ToAsm.mem_blockDefs.mpr
                    (Or.inr (List.mem_flatMap.mpr
                      ⟨i, by rw [hsplit]; simp, hd⟩))
                  have hddb : d ∈ ToAsm.blockDefs db :=
                    ToAsm.mem_blockDefs.mpr (Or.inr hdflat)
                  have hdicur : di = cur :=
                    block_def_index_unique hnd hdb hb hddb hdcur
                  subst di
                  by_cases heq : ri = cur
                  · apply local_bad heq
                    exact hlocD heq.symm
                  · exact False.elim (cross_bad heq hdomD)

/-- If a non-constant instruction grows the operation table, its destination
is not among the final-substituted operands of that newly recorded entry. -/
theorem cseStep_dest_use_fresh_nonconst {f : Func} {li : Array (List ValId)}
    {n : Nat} (hnd : f.allDefs.Nodup) (hwf : f.wfCheck n = true)
    (hli : ToAsm.liveInSets f = some li) (hdom : ToAsm.Func.domCheck f = true)
    {cur : BlockId} {b : Block} (hb : f.blocks[cur]? = some b)
    {path : List BlockId} (hpath : EntryPath f path cur)
    {pre post : List Instr} {i : Instr}
    (hsplit : b.instrs = pre ++ i :: post) {d : ValId} (hd : d ∈ i.defs)
    (hnconst : ∀ v, i ≠ .const d v)
    (hchg : (cseInstrStep i (cseAt f cur b pre)).2.1 ≠
      (cseAt f cur b pre).2.1) :
    d ∉ (substInstr (cseSub f) i).uses := by
  cases i with
  | const d0 v =>
      have heq : d = d0 := by simpa [Instr.defs] using hd
      subst d0
      exact False.elim (hnconst v rfl)
  | call ds fid as =>
      exact False.elim (hchg rfl)
  | op ds yop as =>
      cases ds with
      | nil => simp [Instr.defs] at hd
      | cons d0 ds =>
          cases ds with
          | cons e es => exact False.elim (hchg rfl)
          | nil =>
              have heq : d = d0 := by simpa [Instr.defs] using hd
              subst d0
              let q := cseAt f cur b pre
              have hdpre : q.2.2.2.1[d]? = none :=
                cseAt_dest_none hnd hb hsplit (by simp [Instr.defs])
              by_cases hp : pureOp yop = true
              · cases hfind : q.2.1.ops.find? (fun x => x.1 ==
                    (yop, substVs q.2.2.2.1 as)) with
                | some entry =>
                    by_cases hu : q.2.2.1.contains d = true
                    · exfalso
                      apply hchg
                      simp [q, cseInstrStep, substInstr, hp, hfind, hu]
                    · exfalso
                      apply hchg
                      simp [q, cseInstrStep, substInstr, hp, hfind, hu]
                | none =>
                    by_cases hgadd : (substVs q.2.2.2.1 as).all (fun a =>
                        q.2.2.2.2.1.contains a ||
                          !q.2.2.2.2.2.contains a) = true
                    · intro hdUse
                      simp only [substInstr, Instr.uses, substVs,
                        List.mem_map] at hdUse
                      obtain ⟨x, hx, hxd⟩ := hdUse
                      cases hmx : (cseSub f)[x]? with
                      | none =>
                          have hxeq : x = d := by
                            simpa [substV, Std.HashMap.getD_eq_getD_getElem?,
                              hmx] using hxd
                          subst x
                          have hdBlock : d ∈ q.2.2.2.2.2 := by
                            have hdb : d ∈ cseBlockDefs b := by
                              rw [mem_cseBlockDefs]
                              rw [hsplit, List.flatMap_append, List.flatMap_cons]
                              simp [hd]
                            dsimp only [q, cseAt]
                            rw [cseInstrFold_blockDefs]
                            exact hdb
                          have hdNotDefined : d ∉ q.2.2.2.2.1 := by
                            intro hm
                            have hdPre : d ∈ pre.flatMap Instr.defs := by
                              simpa [q, cseAt] using
                                ((cseInstrFold_defined pre
                                  (⟨[], cseEntryTab f (inEdgeSources f)
                                    (csePrefix f cur).2.1 cur, ∅,
                                    (csePrefix f cur).2.2, ∅, cseBlockDefs b⟩ :
                                      CSEInner)).1 hm)
                            have hndb := blockInstrDefs_nodup hnd
                              (block_mem_of_getElem? hb)
                            rw [hsplit, List.flatMap_append, List.flatMap_cons,
                              List.nodup_append] at hndb
                            exact hndb.2.2 d hdPre d
                              (List.mem_append_left _ hd) rfl
                          have hdMid : d ∈ substVs q.2.2.2.1 as := by
                            simp only [substVs, List.mem_map]
                            exact ⟨d, hx, by
                              simp [substV, Std.HashMap.getD_eq_getD_getElem?,
                                hdpre]⟩
                          have hg := List.all_eq_true.mp hgadd d hdMid
                          rw [Bool.or_eq_true] at hg
                          rcases hg with hdefined | hout
                          · exact hdNotDefined
                              (Std.HashSet.contains_iff_mem.mp hdefined)
                          · have hc := Std.HashSet.mem_iff_contains.mp hdBlock
                            rw [hc] at hout
                            simp at hout
                      | some y =>
                          have hyeq : y = d := by
                            simpa [substV, Std.HashMap.getD_eq_getD_getElem?,
                              hmx] using hxd
                          subst y
                          obtain ⟨expr, hdefX, hdefD⟩ :=
                            (cseFinalSubSound hnd).1 hmx
                          cases expr with
                          | const v =>
                              cases hdefD with
                              | @const bd _ v hbd hid =>
                                  have heqi := instr_def_unique (d := d) hnd
                                    (block_mem_of_getElem? hb) hbd
                                    (by rw [hsplit]; simp) hid hd
                                    (by simp [Instr.defs])
                                  exact hnconst v heqi
                          | op yo aa =>
                              have hself : x ∈ (Instr.op [d] yop as).defs →
                                  x ∉ (Instr.op [d] yop as).uses := by
                                intro hxdef
                                have hxeq : x = d := by
                                  simpa [Instr.defs] using hxdef
                                subst x
                                have := cseSub_rangeFree hnd hmx
                                rw [hmx] at this
                                contradiction
                              have hseenX := cseSeen_of_op_use hnd hli hdom hwf
                                hb hsplit (by simpa [Instr.uses] using hx)
                                hmx hdefX hself
                              have hseenD := CseSeen.rep (model := model) hnd hwf
                                hb hpath hsplit hmx hseenX
                              exact hseenD.not_defined_later hnd hb
                                (show b.instrs = pre ++ (Instr.op [d] yop as :: post)
                                  from hsplit)
                                (by rw [List.flatMap_cons]
                                    exact List.mem_append_left _ hd)
                    · exfalso
                      apply hchg
                      simp [q, cseInstrStep, substInstr, hp, hfind, hgadd]
              · exfalso
                apply hchg
                simp [q, cseInstrStep, substInstr, hp]

theorem cseFresh {f : Func} {li : Array (List ValId)} {n : Nat}
    (hnd : f.allDefs.Nodup) (hwf : f.wfCheck n = true)
    (hli : ToAsm.liveInSets f = some li) (hdom : ToAsm.Func.domCheck f = true) :
    CseFresh f := by
  intro cur b hb path hpath pre post i hsplit d hd hnconst
  exact ⟨cseAt_rep_fresh hnd hwf hb hpath hsplit hd,
    cseAt_runtimeUse_fresh_nonconst hnd hwf hli hdom hb hpath hsplit hd hnconst,
    fun hchg => cseStep_dest_use_fresh_nonconst hnd hwf hli hdom hb hpath
      hsplit hd hnconst hchg⟩

end Passes

/-- Rebinding a certified constant destination preserves old table entries even
when a loop revisit has made that destination occur in an expression key: if it
is already bound, constant provenance says that it already contains the same
literal; if it is unbound, no successfully-readable runtime expression can use
it. -/
theorem CseTabRuntime.addConst_rebind {f : Func} {R R' : Regs}
    {tab : Passes.CseTab} {d : ValId} {v : U256}
    (h : CseTabRuntime (model := model) (Passes.cseSub f) R' tab)
    (hvals : d ∉ Passes.cseTabVals tab)
    (hdnone : (Passes.cseSub f)[d]? = none)
    (ha : R d = R' d) (hconst : CseConstRegs f R)
    (hdef : Passes.CseDef f (.const v) d) :
    CseTabRuntime (model := model) (Passes.cseSub f) (R'.set d v)
      {tab with consts := (v, d) :: tab.consts} := by
  cases hrd : R' d with
  | none =>
      apply h.addConst hvals
      intro hu
      simp only [cseTabRuntimeUses, List.mem_flatMap] at hu
      obtain ⟨⟨⟨yop, as⟩, d0⟩, hm, hx⟩ := hu
      obtain ⟨vals, w, s, s', hg, -, -⟩ := h.1 hm
      obtain ⟨wd, hwd⟩ := Regs.eq_some_of_getMany hg hx
      rw [hrd] at hwd
      contradiction
  | some w =>
      have hr : R d = some w := ha.trans hrd
      have hw : w = v := hconst hdef hr
      subst w
      have hset : R'.set d v = R' := by
        funext x
        by_cases hxd : x = d
        · subst x
          rw [Regs.set_same, hrd]
        · rw [Regs.set_other _ _ hxd]
      rw [hset]
      refine ⟨h.1, ?_⟩
      intro v0 d0 hm
      rcases List.mem_cons.mp hm with hhead | htail
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hhead
        simpa [CseExprRuntime] using hrd
      · exact h.2 htail

namespace Passes

/-- Lockstep execution of a source suffix against the CSE fold state at the
corresponding source boundary.  `CseFresh` is the static fold certificate used
only when a kept instruction binds registers while table entries remain live. -/
theorem cse_exec_aux {P : Prog} {f : Func} (hwf : f.wfCheck P.funcs.size = true)
    (hnd : f.allDefs.Nodup) {li : Array (List ValId)}
    (hli : ToAsm.liveInSets f = some li) (hdom : ToAsm.Func.domCheck f = true)
    (hfresh : CseFresh f) {R : Regs} {st : EvmState} {rest : Rest} {res : FRes}
    (hexec : Exec (model := model) P f R st rest res) :
    ∀ {cur : BlockId} {b : Block} {path : List BlockId} {pre : List Instr}
      {R' : Regs},
      f.blocks[cur]? = some b → EntryPath f path cur →
      b.instrs = pre ++ rest.instrs → rest.term = b.term →
      CseAgree f cur pre R R' → CseConstAgree f R R' →
      CseConstRegs f R →
      CseTabRuntime (model := model) (cseSub f) R' (cseAt f cur b pre).2.1 →
      Exec (model := model) P (cse f) R' st
        ⟨cseInstrsOut (cseSub f) rest.instrs (cseAt f cur b pre).2.1
          (cseAt f cur b pre).2.2.1 (cseAt f cur b pre).2.2.2.1
          (cseAt f cur b pre).2.2.2.2.1 (cseAt f cur b pre).2.2.2.2.2,
          substTerm (cseSub f) rest.term⟩ res := by
  induction hexec with
  | @const f R st d v is t res htail ih =>
      intro cur b path pre R' hb hpath hsplit ht ha hc hconst htab
      have hi : Instr.const d v ∈ b.instrs := by rw [hsplit]; simp
      have hbmem := block_mem_of_getElem? hb
      let q := cseAt f cur b pre
      have hdpre : q.2.2.2.1[d]? = none := cseAt_dest_none hnd hb hsplit
        (by simp [Instr.defs])
      cases hfind : q.2.1.consts.find? (fun x => x.1 == v) with
      | some entry =>
          obtain ⟨v0, d0⟩ := entry
          obtain ⟨hv0, hval⟩ := htab.const_of_find hfind
          subst v0
          have hsout : (cseInstrStep (.const d v) q).1 = [] := by
            simp [q, cseInstrStep, substInstr, hfind]
          have hmap : (cseSub f)[d]? = some d0 := by
            rw [cseAt_dest_final hnd hb hsplit (by simp [Instr.defs])]
            simp [q, cseInstrStep, substInstr, hfind, hdpre]
          have hsplit' : b.instrs = (pre ++ [.const d v]) ++ is := by
            simpa [List.append_assoc] using hsplit
          have hnext := ih hwf hnd hli hdom hfresh hb hpath hsplit' ht
            (CseAgree.step_dropped (i := .const d v) (by simp [Instr.defs])
              hmap ha hval)
            (hc.const_dropped hnd hbmem hi hmap hval)
            (hconst.const hnd hbmem hi)
            (by simpa [cseAt_snoc, q, cseInstrStep, substInstr,
                hfind] using htab)
          rw [cseInstrsOut_at_drop hsout]
          simpa [Regs.setMany, Instr.defs] using hnext
      | none =>
          have hsout : (cseInstrStep (.const d v) q).1 =
              [substInstr q.2.2.2.1 (.const d v)] := by
            simp [q, cseInstrStep, substInstr, hfind]
          have hdnone : (cseSub f)[d]? = none := by
            rw [cseAt_dest_final hnd hb hsplit (by simp [Instr.defs])]
            simp [q, cseInstrStep, substInstr, hfind, hdpre]
          have hfr := cseAt_rep_fresh hnd hwf hb hpath hsplit
            (d := d) (by simp [Instr.defs])
          have hsplit' : b.instrs = (pre ++ [.const d v]) ++ is := by
            simpa [List.append_assoc] using hsplit
          have hnext := ih hwf hnd hli hdom hfresh hb hpath hsplit' ht
            (by simpa [Regs.setMany, Instr.defs] using
              (ha.step_kept hnd hwf hb hpath hsplit
                (fun x hx => by
                  have : x = d := by simpa [Instr.defs] using hx
                  subst x
                  exact hdnone) [v]))
            (hc.const_kept hnd hconst hbmem hi hdnone)
            (hconst.const hnd hbmem hi)
            (by simpa [cseAt_snoc, q, cseInstrStep, substInstr, hfind,
                Regs.setMany, Instr.defs] using
              (htab.addConst_rebind hfr hdnone (ha.1 d hdnone) hconst
                (.const hbmem hi)))
          rw [cseInstrsOut_at_keep hnd hb hsplit hsout]
          exact Exec.const hnext
  | @op f R st st' ds yop as args rets is t res hg hbi hlen htail ih =>
      intro cur b path pre R' hb hpath hsplit ht ha hc hconst htab
      have hi : Instr.op ds yop as ∈ b.instrs := by rw [hsplit]; simp
      have hbmem := block_mem_of_getElem? hb
      have harity := wfCheck_op_arity hwf hbmem hi
      cases ds with
      | nil =>
          let q := cseAt f cur b pre
          have hsout : (cseInstrStep (.op [] yop as) q).1 =
              [substInstr q.2.2.2.1 (.op [] yop as)] := by rfl
          have hget' := cseGetMany hnd ha hc (xs := as) (by
            intro x d0 yo aa hx hm hd
            apply cseSeen_of_op_use hnd hli hdom hwf hb hsplit
              (by simpa [Instr.uses] using hx) hm hd
            simp [Instr.defs]) hg
          have hsplit' : b.instrs = (pre ++ [.op [] yop as]) ++ is := by
            simpa [List.append_assoc] using hsplit
          have hnext := ih hwf hnd hli hdom hfresh hb hpath hsplit' ht
            (ha.step_kept hnd hwf hb hpath hsplit (by simp [Instr.defs]) rets)
            (hc.nonconst hnd hbmem hi (by intro d v h; cases h) rets)
            (hconst.nonconst hnd hbmem hi (by intro d v h; cases h) rets)
            (by simpa [cseAt_snoc, q, cseInstrStep, substInstr,
                Regs.setMany, Instr.defs] using htab)
          rw [cseInstrsOut_at_keep hnd hb hsplit hsout]
          exact Exec.op hget' hbi hlen hnext
      | cons d ds =>
          cases ds with
          | cons e es => simp at harity
          | nil =>
              let q := cseAt f cur b pre
              have hdpre : q.2.2.2.1[d]? = none := cseAt_dest_none hnd hb hsplit
                (by simp [Instr.defs])
              by_cases hp : pureOp yop = true
              · cases hfind : q.2.1.ops.find? (fun x => x.1 ==
                    (yop, substVs q.2.2.2.1 as)) with
                | some entry =>
                    obtain ⟨⟨yop0, as0⟩, d0⟩ := entry
                    by_cases hu : q.2.2.1.contains d = true
                    · have hsout : (cseInstrStep (.op [d] yop as) q).1 =
                          [substInstr q.2.2.2.1 (.op [d] yop as)] := by
                        simp [q, cseInstrStep, substInstr, hp, hfind, hu]
                      have hdnone : (cseSub f)[d]? = none := by
                        rw [cseAt_dest_final hnd hb hsplit (by simp [Instr.defs])]
                        simp [q, cseInstrStep, substInstr, hp, hfind, hu, hdpre]
                      have hget' := cseGetMany hnd ha hc (xs := as) (by
                        intro x d1 yo aa hx hm hd
                        apply cseSeen_of_op_use hnd hli hdom hwf hb hsplit
                          (by simpa [Instr.uses] using hx) hm hd
                        intro hxd
                        have : x = d := by simpa [Instr.defs] using hxd
                        subst x
                        rw [hdnone] at hm
                        contradiction) hg
                      have hfr := hfresh hb hpath hsplit d (by simp [Instr.defs])
                        (by intro v h; cases h)
                      have hsplit' : b.instrs = (pre ++ [.op [d] yop as]) ++ is := by
                        simpa [List.append_assoc] using hsplit
                      have hnext := ih hwf hnd hli hdom hfresh hb hpath hsplit' ht
                        (ha.step_kept hnd hwf hb hpath hsplit
                          (fun x hx => by
                            have : x = d := by simpa [Instr.defs] using hx
                            subst x
                            exact hdnone) rets)
                        (hc.nonconst hnd hbmem hi (by intro x v h; cases h) rets)
                        (hconst.nonconst hnd hbmem hi (by intro x v h; cases h) rets)
                        (by
                          have hr := htab.setMany_of_fresh (ds := [d])
                            (vals := rets) (fun x hx => by
                              have : x = d := by simpa using hx
                              subst x
                              exact ⟨hfr.1, hfr.2.1⟩)
                          simpa [cseAt_snoc, q, cseInstrStep,
                            substInstr, hp, hfind, hu, Instr.defs] using hr)
                      rw [cseInstrsOut_at_keep hnd hb hsplit hsout]
                      exact Exec.op hget' hbi hlen hnext
                    · have hsout : (cseInstrStep (.op [d] yop as) q).1 = [] := by
                        simp [q, cseInstrStep, substInstr, hp, hfind, hu]
                      have hmap : (cseSub f)[d]? = some d0 := by
                        rw [cseAt_dest_final hnd hb hsplit (by simp [Instr.defs])]
                        simp [q, cseInstrStep, substInstr, hp, hfind, hu, hdpre]
                      obtain ⟨hyop0, has0, hrt⟩ := htab.op_of_find hfind
                      subst yop0
                      subst as0
                      have htabSound := cseAt_tab_sound hnd hb
                        (show b.instrs = pre ++ (.op [d] yop as :: is) from hsplit)
                      have hentry := htabSound.2 (List.mem_of_find?_eq_some hfind)
                      have hdomain := cseAt_tab_domain hnd hb
                        (show b.instrs = pre ++ (.op [d] yop as :: is) from hsplit)
                        (List.mem_of_find?_eq_some hfind)
                      have hdrop : CseDropPos f
                          (.op yop (substVs q.2.2.2.1 as)) d :=
                        .op hbmem hsplit rfl hdpre (by
                          intro hm
                          apply hu
                          apply Std.HashSet.mem_iff_contains.mp
                          have hmUsed : d ∈ q.2.2.1 := by
                            simpa [q, cseAt] using
                              ((cseInstrFold_used pre
                                (⟨[], cseEntryTab f (inEdgeSources f)
                                  (csePrefix f cur).2.1 cur, ∅,
                                  (csePrefix f cur).2.2, ∅, cseBlockDefs b⟩ :
                                    CSEInner)).2 (Or.inr hm))
                          exact hmUsed)
                      have hself : d ∉ (Instr.op [d] yop as).uses :=
                        cse_drop_not_self_use hnd hwf hli hdom (cseSub_rangeFree hnd)
                          (csePrefix_ordered hnd f.blocks.size (Nat.le_refl _))
                          hmap hdrop hentry hdomain hb hpath hi (by simp [Instr.defs])
                      have hget' := cseGetMany hnd ha hc (xs := as) (by
                        intro x d1 yo aa hx hm hd
                        apply cseSeen_of_op_use hnd hli hdom hwf hb hsplit
                          (by simpa [Instr.uses] using hx) hm hd
                        intro hxd
                        have : x = d := by simpa [Instr.defs] using hxd
                        subst x
                        exact hself) hg
                      have hgStored : R'.getMany
                          (substVs (cseSub f) (substVs q.2.2.2.1 as)) = some args := by
                        rw [substVs_absorb (cseAt_substExt hnd hb
                          (show b.instrs = pre ++ (Instr.op [d] yop as :: is)
                            from hsplit)) (cseSub_rangeFree hnd)]
                        exact hget'
                      obtain ⟨w, hrets, hval⟩ :=
                        CseExprRuntime.op_result hrt hp hgStored hbi
                      subst rets
                      have hst : st' = st := pure_state_eq hp hbi
                      subst st'
                      have hsplit' : b.instrs = (pre ++ [.op [d] yop as]) ++ is := by
                        simpa [List.append_assoc] using hsplit
                      have hnext := ih hwf hnd hli hdom hfresh hb hpath hsplit' ht
                        (by simpa [Regs.setMany, Instr.defs] using
                          (CseAgree.step_dropped (i := .op [d] yop as)
                            (by simp [Instr.defs]) hmap ha hval))
                        (hc.nonconst_left hnd hbmem hi (by intro x v h; cases h) [w])
                        (hconst.nonconst hnd hbmem hi (by intro x v h; cases h) [w])
                        (by simpa [cseAt_snoc, q, cseInstrStep,
                            substInstr, hp, hfind, hu] using htab)
                      rw [cseInstrsOut_at_drop hsout]
                      simpa [Regs.setMany, Instr.defs] using hnext
                | none =>
                    by_cases hgadd : (substVs q.2.2.2.1 as).all (fun a =>
                        q.2.2.2.2.1.contains a || !q.2.2.2.2.2.contains a) = true
                    · have hsout : (cseInstrStep (.op [d] yop as) q).1 =
                          [substInstr q.2.2.2.1 (.op [d] yop as)] := by
                        simp [q, cseInstrStep, substInstr, hp, hfind, hgadd]
                      have hdnone : (cseSub f)[d]? = none := by
                        rw [cseAt_dest_final hnd hb hsplit (by simp [Instr.defs])]
                        simp [q, cseInstrStep, substInstr, hp, hfind, hgadd, hdpre]
                      have hget' := cseGetMany hnd ha hc (xs := as) (by
                        intro x d1 yo aa hx hm hd
                        apply cseSeen_of_op_use hnd hli hdom hwf hb hsplit
                          (by simpa [Instr.uses] using hx) hm hd
                        intro hxd
                        have : x = d := by simpa [Instr.defs] using hxd
                        subst x
                        rw [hdnone] at hm
                        contradiction) hg
                      cases rets with
                      | nil => simp at hlen
                      | cons w ws =>
                          cases ws with
                          | cons z zs => simp at hlen
                          | nil =>
                              have hfr := hfresh hb hpath hsplit d (by simp [Instr.defs])
                                (by intro v h; cases h)
                              have hgetSet : (R'.set d w).getMany
                                  (substVs (cseSub f) (substVs q.2.2.2.1 as)) = some args := by
                                rw [substVs_absorb (cseAt_substExt hnd hb
                                  (show b.instrs = pre ++ (.op [d] yop as :: is)
                                    from hsplit)) (cseSub_rangeFree hnd)]
                                rw [← hget']
                                apply Regs.getMany_congr
                                intro x hx
                                rw [Regs.set_other]
                                intro heq
                                subst x
                                exact hfr.2.2 (by
                                  intro heqTab
                                  have hlenTab := congrArg
                                    (fun tab : CseTab => tab.ops.length) heqTab
                                  simp [q, cseInstrStep, substInstr, hp, hfind,
                                    hgadd] at hlenTab)
                                  (by simpa [substInstr, Instr.uses] using hx)
                              have hsplit' : b.instrs = (pre ++ [.op [d] yop as]) ++ is := by
                                simpa [List.append_assoc] using hsplit
                              have hnext := ih hwf hnd hli hdom hfresh hb hpath hsplit' ht
                                (by simpa [Regs.setMany, Instr.defs] using
                                  (ha.step_kept hnd hwf hb hpath hsplit
                                    (fun x hx => by
                                      have : x = d := by simpa [Instr.defs] using hx
                                      subst x
                                      exact hdnone) [w]))
                                (hc.nonconst hnd hbmem hi (by intro x v h; cases h) [w])
                                (hconst.nonconst hnd hbmem hi (by intro x v h; cases h) [w])
                                (by
                                  have hr := htab.addOp hfr.1 hfr.2.1 hgetSet (by
                                    simpa [substVs_absorb (cseAt_substExt hnd hb
                                      (show b.instrs = pre ++ (.op [d] yop as :: is)
                                        from hsplit)) (cseSub_rangeFree hnd)] using hbi)
                                  simpa [cseAt_snoc, q, cseInstrStep,
                                    substInstr, hp, hfind, hgadd, Instr.defs,
                                    Regs.setMany] using hr)
                              rw [cseInstrsOut_at_keep hnd hb hsplit hsout]
                              exact Exec.op hget' hbi hlen hnext
                    · have hsout : (cseInstrStep (.op [d] yop as) q).1 =
                          [substInstr q.2.2.2.1 (.op [d] yop as)] := by
                        simp [q, cseInstrStep, substInstr, hp, hfind, hgadd]
                      have hdnone : (cseSub f)[d]? = none := by
                        rw [cseAt_dest_final hnd hb hsplit (by simp [Instr.defs])]
                        simp [q, cseInstrStep, substInstr, hp, hfind, hgadd, hdpre]
                      have hget' := cseGetMany hnd ha hc (xs := as) (by
                        intro x d1 yo aa hx hm hd
                        apply cseSeen_of_op_use hnd hli hdom hwf hb hsplit
                          (by simpa [Instr.uses] using hx) hm hd
                        intro hxd
                        have : x = d := by simpa [Instr.defs] using hxd
                        subst x
                        rw [hdnone] at hm
                        contradiction) hg
                      have hfr := hfresh hb hpath hsplit d (by simp [Instr.defs])
                        (by intro v h; cases h)
                      have hsplit' : b.instrs = (pre ++ [.op [d] yop as]) ++ is := by
                        simpa [List.append_assoc] using hsplit
                      have hnext := ih hwf hnd hli hdom hfresh hb hpath hsplit' ht
                        (ha.step_kept hnd hwf hb hpath hsplit
                          (fun x hx => by
                            have : x = d := by simpa [Instr.defs] using hx
                            subst x
                            exact hdnone) rets)
                        (hc.nonconst hnd hbmem hi (by intro x v h; cases h) rets)
                        (hconst.nonconst hnd hbmem hi (by intro x v h; cases h) rets)
                        (by
                          have hr := htab.setMany_of_fresh (ds := [d])
                            (vals := rets) (fun x hx => by
                              have : x = d := by simpa using hx
                              subst x
                              exact ⟨hfr.1, hfr.2.1⟩)
                          simpa [cseAt_snoc, q, cseInstrStep,
                            substInstr, hp, hfind, hgadd, Instr.defs] using hr)
                      rw [cseInstrsOut_at_keep hnd hb hsplit hsout]
                      exact Exec.op hget' hbi hlen hnext
              · have hsout : (cseInstrStep (.op [d] yop as) q).1 =
                    [substInstr q.2.2.2.1 (.op [d] yop as)] := by
                  simp [q, cseInstrStep, substInstr, hp]
                have hdnone : (cseSub f)[d]? = none := by
                  rw [cseAt_dest_final hnd hb hsplit (by simp [Instr.defs])]
                  simp [q, cseInstrStep, substInstr, hp, hdpre]
                have hget' := cseGetMany hnd ha hc (xs := as) (by
                  intro x d1 yo aa hx hm hd
                  apply cseSeen_of_op_use hnd hli hdom hwf hb hsplit
                    (by simpa [Instr.uses] using hx) hm hd
                  intro hxd
                  have : x = d := by simpa [Instr.defs] using hxd
                  subst x
                  rw [hdnone] at hm
                  contradiction) hg
                have hfr := hfresh hb hpath hsplit d (by simp [Instr.defs])
                  (by intro v h; cases h)
                have hsplit' : b.instrs = (pre ++ [.op [d] yop as]) ++ is := by
                  simpa [List.append_assoc] using hsplit
                have hnext := ih hwf hnd hli hdom hfresh hb hpath hsplit' ht
                  (ha.step_kept hnd hwf hb hpath hsplit
                    (fun x hx => by
                      have : x = d := by simpa [Instr.defs] using hx
                      subst x
                      exact hdnone) rets)
                  (hc.nonconst hnd hbmem hi (by intro x v h; cases h) rets)
                  (hconst.nonconst hnd hbmem hi (by intro x v h; cases h) rets)
                  (by
                    have hr := htab.setMany_of_fresh (ds := [d])
                      (vals := rets) (fun x hx => by
                        have : x = d := by simpa using hx
                        subst x
                        exact ⟨hfr.1, hfr.2.1⟩)
                    simpa [cseAt_snoc, q, cseInstrStep,
                      substInstr, hp, Instr.defs] using hr)
                rw [cseInstrsOut_at_keep hnd hb hsplit hsout]
                exact Exec.op hget' hbi hlen hnext
  | @opHalt f R st st' ds yop as args is t hg hbi =>
      intro cur b path pre R' hb hpath hsplit ht ha hc hconst htab
      have hi : Instr.op ds yop as ∈ b.instrs := by rw [hsplit]; simp
      have hpureFalse : pureOp yop = false := by
        by_contra hp
        exact pure_no_halt (Bool.eq_true_of_not_eq_false hp) hbi
      let q := cseAt f cur b pre
      have hsout : (cseInstrStep (.op ds yop as) q).1 =
          [substInstr q.2.2.2.1 (.op ds yop as)] := by
        cases ds with
        | nil => rfl
        | cons d ds =>
            cases ds with
            | nil => simp [q, cseInstrStep, substInstr, hpureFalse]
            | cons e es => rfl
      have hget' := cseGetMany hnd ha hc (xs := as) (by
        intro x d0 yo aa hx hm hd
        apply cseSeen_of_op_use hnd hli hdom hwf hb hsplit
          (by simpa [Instr.uses] using hx) hm hd
        intro hxd
        have hdnone : (cseSub f)[x]? = none := by
          rw [cseAt_dest_final hnd hb hsplit hxd]
          cases ds with
          | nil => simp [Instr.defs] at hxd
          | cons d ds =>
              cases ds with
              | nil =>
                  simpa [q, cseInstrStep, substInstr, hpureFalse] using
                    (cseAt_dest_none hnd hb hsplit hxd)
              | cons e es => simp [q, cseInstrStep, substInstr,
                  cseAt_dest_none hnd hb hsplit hxd]
        rw [hdnone] at hm
        contradiction) hg
      rw [cseInstrsOut_at_keep hnd hb hsplit hsout]
      exact Exec.opHalt hget' hbi
  | @call f g R st st' ds as fid args rvals eb is t res hfid hg hplen heb hbody hlen htail ihbody ih =>
      intro cur b path pre R' hb hpath hsplit ht ha hc hconst htab
      let q := cseAt f cur b pre
      have hi : Instr.call ds fid as ∈ b.instrs := by rw [hsplit]; simp
      have hsout : (cseInstrStep (.call ds fid as) q).1 =
          [substInstr q.2.2.2.1 (.call ds fid as)] := by
        simp [q, cseInstrStep, substInstr]
      have hget' := cseGetMany hnd ha hc (xs := as) (by
        intro x d0 yo aa hx hm hd
        apply cseSeen_of_op_use hnd hli hdom hwf hb hsplit
          (by simpa [Instr.uses] using hx) hm hd
        intro hxd
        have hdnone : (cseSub f)[x]? = none := by
          rw [cseAt_dest_final hnd hb hsplit hxd]
          simp [q, cseInstrStep, substInstr,
            cseAt_dest_none hnd hb hsplit hxd]
        rw [hdnone] at hm
        contradiction) hg
      have hkept : ∀ x ∈ (Instr.call ds fid as).defs, (cseSub f)[x]? = none := by
        intro x hx
        rw [cseAt_dest_final hnd hb hsplit hx]
        simp [q, cseInstrStep, substInstr,
          cseAt_dest_none hnd hb hsplit hx]
      have hfr : ∀ x ∈ ds, x ∉ cseTabVals q.2.1 ∧
          x ∉ cseTabRuntimeUses (cseSub f) q.2.1 := by
        intro x hx
        have h := hfresh hb hpath hsplit x (by simpa [Instr.defs] using hx)
          (by intro v h; cases h)
        exact ⟨h.1, h.2.1⟩
      have hsplit' : b.instrs = (pre ++ [.call ds fid as]) ++ is := by
        simpa [List.append_assoc] using hsplit
      have hnext := ih hwf hnd hli hdom hfresh hb hpath hsplit' ht
        (ha.step_kept hnd hwf hb hpath hsplit hkept rvals)
        (hc.nonconst hnd (block_mem_of_getElem? hb) hi (by intro x v h; cases h) rvals)
        (hconst.nonconst hnd (block_mem_of_getElem? hb) hi
          (by intro x v h; cases h) rvals)
        (by
          have hr := htab.setMany_of_fresh (ds := ds) (vals := rvals) hfr
          simpa [cseAt_snoc, q, cseInstrStep, substInstr,
            Instr.defs] using hr)
      rw [cseInstrsOut_at_keep hnd hb hsplit hsout]
      exact Exec.call hfid hget' hplen heb hbody hlen hnext
  | @callHalt f g R st st' ds as fid args eb is t hfid hg hplen heb hbody ihbody =>
      intro cur b path pre R' hb hpath hsplit ht ha hc hconst htab
      let q := cseAt f cur b pre
      have hsout : (cseInstrStep (.call ds fid as) q).1 =
          [substInstr q.2.2.2.1 (.call ds fid as)] := by
        simp [q, cseInstrStep, substInstr]
      have hget' := cseGetMany hnd ha hc (xs := as) (by
        intro x d0 yo aa hx hm hd
        apply cseSeen_of_op_use hnd hli hdom hwf hb hsplit
          (by simpa [Instr.uses] using hx) hm hd
        intro hxd
        have hdnone : (cseSub f)[x]? = none := by
          rw [cseAt_dest_final hnd hb hsplit hxd]
          simp [q, cseInstrStep, substInstr,
            cseAt_dest_none hnd hb hsplit hxd]
        rw [hdnone] at hm
        contradiction) hg
      rw [cseInstrsOut_at_keep hnd hb hsplit hsout]
      exact Exec.callHalt hfid hget' hplen heb hbody
  | @jump f R st e tb vals res htb hg hplen hbody ih =>
      intro cur b path pre R' hb hpath hsplit ht ha hc hconst htab
      have hpre : pre = b.instrs := by simpa using hsplit.symm
      subst pre
      have he : e ∈ b.term.edges := by rw [← ht]; simp [Term.edges]
      have hget' := cseGetMany hnd ha hc (xs := e.args) (by
        intro x d0 yo aa hx hm hd
        apply cseSeen_of_use hnd hli hdom hb hm
        · rw [ToAsm.mem_blockUses]
          exact Or.inr (by rw [← ht]; simpa [Term.uses] using hx)
        · intro hlocal
          exact hlocal) hg
      let tb' := substBlock (csePrefix f f.blocks.size).2.2
        (cseBlockOut f e.target)
      have htb' : (cse f).blocks[e.target]? = some tb' := cse_block_get htb
      have htbBang : f.blocks[e.target]! = tb := by
        have hlt := (Array.getElem?_eq_some_iff.mp htb).1
        rw [getElem!_eq_getElem hlt]
        exact (Array.getElem?_eq_some_iff.mp htb).2
      have hpath' := EntryPath.edge hpath hb he
      have ha' := ha.jump hnd hb hpath he htb vals
      have hc' : CseConstAgree f (R.setMany tb.params vals)
          (R'.setMany tb.params vals) :=
        hc.params hnd (block_mem_of_getElem? htb) vals
      have hconst' : CseConstRegs f (R.setMany tb.params vals) :=
        hconst.params hnd (block_mem_of_getElem? htb) vals
      have htab' := CseTabRuntime.entry_of_edge hnd hb he htb
        (by simpa [cseAt_full hb] using htab) vals
      have hnext := ih hwf hnd hli hdom hfresh htb hpath' rfl rfl ha' hc'
        hconst' htab'
      have hnext' : Exec (model := model) P (cse f)
          (R'.setMany tb'.params vals) st ⟨tb'.instrs, tb'.term⟩ res := by
        simpa [tb', substBlock, cseBlockOut, htbBang, cseAt_nil,
          cseInstrsOut_eq_fold, cseSub] using hnext
      simpa [substTerm, substEdge, substVs, cseAt_nil, cseBlockOut,
        cseInstrsOut_eq_fold, cseSub] using
        (Exec.jump (P := P) (f := cse f) (e := substEdge (cseSub f) e)
          (args := vals) htb' (by simpa [substEdge] using hget')
          (by simpa [tb', substBlock, cseBlockOut, htbBang] using hplen) hnext')
  | @branchTrue f R st c v et ef tb vals res hc0 hv htb hg hplen hbody ih =>
      intro cur b path pre R' hb hpath hsplit ht ha hc hconst htab
      have hpre : pre = b.instrs := by simpa using hsplit.symm
      subst pre
      have he : et ∈ b.term.edges := by rw [← ht]; simp [Term.edges]
      have hread (xs : List ValId) (hxs : ∀ x ∈ xs, x ∈ b.term.uses) {vs}
          (hget : R.getMany xs = some vs) := cseGetMany hnd ha hc (xs := xs) (by
            intro x d0 yo aa hx hm hd
            apply cseSeen_of_use hnd hli hdom hb hm
            · rw [ToAsm.mem_blockUses]; exact Or.inr (hxs x hx)
            · intro hlocal; exact hlocal) hget
      have hc' : R' (substV (cseSub f) c) = some v := by
        have hg1 : R.getMany [c] = some [v] := by simp [Regs.getMany, hc0]
        have := hread [c] (by
          intro x hx
          have hxc : x = c := by simpa using hx
          subst x
          rw [← ht]
          simp [Term.uses]) hg1
        cases hcse : R' (substV (cseSub f) c) with
        | none => simp [Regs.getMany, substVs, hcse] at this
        | some w =>
            simp [Regs.getMany, substVs, hcse] at this
            subst w
            rfl
      have hget' := hread et.args (by intro x hx; rw [← ht]; simp [Term.uses, hx]) hg
      let tb' := substBlock (csePrefix f f.blocks.size).2.2
        (cseBlockOut f et.target)
      have htb' : (cse f).blocks[et.target]? = some tb' := cse_block_get htb
      have htbBang : f.blocks[et.target]! = tb := by
        have hlt := (Array.getElem?_eq_some_iff.mp htb).1
        rw [getElem!_eq_getElem hlt]
        exact (Array.getElem?_eq_some_iff.mp htb).2
      have hpath' := EntryPath.edge hpath hb he
      have ha' := ha.jump hnd hb hpath he htb vals
      have hcA : CseConstAgree f (R.setMany tb.params vals)
          (R'.setMany tb.params vals) :=
        hc.params hnd (block_mem_of_getElem? htb) vals
      have hconst' : CseConstRegs f (R.setMany tb.params vals) :=
        hconst.params hnd (block_mem_of_getElem? htb) vals
      have htab' := CseTabRuntime.entry_of_edge hnd hb he htb
        (by simpa [cseAt_full hb] using htab) vals
      have hnext := ih hwf hnd hli hdom hfresh htb hpath' rfl rfl ha' hcA
        hconst' htab'
      have hnext' : Exec (model := model) P (cse f)
          (R'.setMany tb'.params vals) st ⟨tb'.instrs, tb'.term⟩ res := by
        simpa [tb', substBlock, cseBlockOut, htbBang, cseAt_nil,
          cseInstrsOut_eq_fold, cseSub] using hnext
      simpa [substTerm, substEdge, substVs, cseAt_nil, cseBlockOut,
        cseInstrsOut_eq_fold, cseSub] using
        (Exec.branchTrue (P := P) (f := cse f)
          (c := substV (cseSub f) c) (et := substEdge (cseSub f) et)
          (ef := substEdge (cseSub f) ef) (args := vals) hc' hv htb'
          (by simpa [substEdge] using hget')
          (by simpa [tb', substBlock, cseBlockOut, htbBang] using hplen) hnext')
  | @branchFalse f R st c et ef tb vals res hc0 htb hg hplen hbody ih =>
      intro cur b path pre R' hb hpath hsplit ht ha hc hconst htab
      have hpre : pre = b.instrs := by simpa using hsplit.symm
      subst pre
      have he : ef ∈ b.term.edges := by rw [← ht]; simp [Term.edges]
      have hread (xs : List ValId) (hxs : ∀ x ∈ xs, x ∈ b.term.uses) {vs}
          (hget : R.getMany xs = some vs) := cseGetMany hnd ha hc (xs := xs) (by
            intro x d0 yo aa hx hm hd
            apply cseSeen_of_use hnd hli hdom hb hm
            · rw [ToAsm.mem_blockUses]; exact Or.inr (hxs x hx)
            · intro hlocal; exact hlocal) hget
      have hc' : R' (substV (cseSub f) c) = some 0 := by
        have hg1 : R.getMany [c] = some [0] := by simp [Regs.getMany, hc0]
        have := hread [c] (by
          intro x hx
          have hxc : x = c := by simpa using hx
          subst x
          rw [← ht]
          simp [Term.uses]) hg1
        cases hcse : R' (substV (cseSub f) c) with
        | none => simp [Regs.getMany, substVs, hcse] at this
        | some w =>
            simp [Regs.getMany, substVs, hcse] at this
            subst w
            rfl
      have hget' := hread ef.args (by intro x hx; rw [← ht]; simp [Term.uses, hx]) hg
      let tb' := substBlock (csePrefix f f.blocks.size).2.2
        (cseBlockOut f ef.target)
      have htb' : (cse f).blocks[ef.target]? = some tb' := cse_block_get htb
      have htbBang : f.blocks[ef.target]! = tb := by
        have hlt := (Array.getElem?_eq_some_iff.mp htb).1
        rw [getElem!_eq_getElem hlt]
        exact (Array.getElem?_eq_some_iff.mp htb).2
      have hpath' := EntryPath.edge hpath hb he
      have ha' := ha.jump hnd hb hpath he htb vals
      have hcA : CseConstAgree f (R.setMany tb.params vals)
          (R'.setMany tb.params vals) :=
        hc.params hnd (block_mem_of_getElem? htb) vals
      have hconst' : CseConstRegs f (R.setMany tb.params vals) :=
        hconst.params hnd (block_mem_of_getElem? htb) vals
      have htab' := CseTabRuntime.entry_of_edge hnd hb he htb
        (by simpa [cseAt_full hb] using htab) vals
      have hnext := ih hwf hnd hli hdom hfresh htb hpath' rfl rfl ha' hcA
        hconst' htab'
      have hnext' : Exec (model := model) P (cse f)
          (R'.setMany tb'.params vals) st ⟨tb'.instrs, tb'.term⟩ res := by
        simpa [tb', substBlock, cseBlockOut, htbBang, cseAt_nil,
          cseInstrsOut_eq_fold, cseSub] using hnext
      simpa [substTerm, substEdge, substVs, cseAt_nil, cseBlockOut,
        cseInstrsOut_eq_fold, cseSub] using
        (Exec.branchFalse (P := P) (f := cse f)
          (c := substV (cseSub f) c) (et := substEdge (cseSub f) et)
          (ef := substEdge (cseSub f) ef) (args := vals) hc' htb'
          (by simpa [substEdge] using hget')
          (by simpa [tb', substBlock, cseBlockOut, htbBang] using hplen) hnext')
  | @ret f R st xs vals hg =>
      intro cur b path pre R' hb hpath hsplit ht ha hc hconst htab
      have hpre : pre = b.instrs := by simpa using hsplit.symm
      subst pre
      have hget' := cseGetMany hnd ha hc (xs := xs) (by
        intro x d0 yo aa hx hm hd
        apply cseSeen_of_use hnd hli hdom hb hm
        · rw [ToAsm.mem_blockUses]; exact Or.inr (by rw [← ht]; simpa [Term.uses] using hx)
        · intro hlocal; exact hlocal) hg
      simpa [substTerm, cseInstrsOut, substVs] using
        (Exec.ret (P := P) (f := cse f) hget')
  | @halt f R st st' yop as args hg hbi =>
      intro cur b path pre R' hb hpath hsplit ht ha hc hconst htab
      have hpre : pre = b.instrs := by simpa using hsplit.symm
      subst pre
      have hget' := cseGetMany hnd ha hc (xs := as) (by
        intro x d0 yo aa hx hm hd
        apply cseSeen_of_use hnd hli hdom hb hm
        · rw [ToAsm.mem_blockUses]; exact Or.inr (by rw [← ht]; simpa [Term.uses] using hx)
        · intro hlocal; exact hlocal) hg
      simpa [substTerm, cseInstrsOut, substVs] using
        (Exec.halt (P := P) (f := cse f) hget' hbi)

end Passes

/-! ### Historical non-positional witness

The positional def-before-use lemma cannot be proved from the present
`wfCheck` and `domCheck` alone.  `ToAsm.liveStep` computes

    blockUses b \\ blockDefs b

after collecting the uses of *all* instructions in the block.  Consequently a
use before a later definition is removed by that later definition and never
reaches `liveIn(entry)`.  The following checked witness is deliberately kept
next to the blocked theorem: value `1` is read by the first instruction and
defined by the second, yet both checks accept and the sole live-in set is
empty.  The implementation's `usedSoFar` guard now prevents this witness from
creating a dropped *operation* destination: after the first instruction,
`usedSoFar.contains 1` is true.  The witness remains useful for documenting
why the proof must consume that guard rather than ask `domCheck` for a
sequential fact it does not establish. -/

private def cseLaterDefCounterexampleBlock : Block :=
  ⟨[], [.op [0] .add [1, 1], .const 1 0], .ret []⟩

private def cseLaterDefCounterexample : Func :=
  { params := [], nrets := 0, entry := 0
    blocks := #[cseLaterDefCounterexampleBlock] }

omit model in
private theorem cseLaterDefCounterexample_checks :
    cseLaterDefCounterexample.wfCheck 0 = true ∧
    ToAsm.Func.domCheck cseLaterDefCounterexample = true ∧
    ToAsm.liveInSets cseLaterDefCounterexample = some #[[]] ∧
    1 ∈ cseLaterDefCounterexampleBlock.instrs[0]!.uses ∧
    1 ∈ cseLaterDefCounterexampleBlock.instrs[1]!.defs := by
  native_decide

/-- **Pass 3 (local CSE) soundness**, under dominance.

`sorry`. Same `LiveAgree` invariant as pass 1, with `σ` the accumulated
dropped-definition substitution `d ↦ d₀`. The value-level obligation — that the
two computations agree — is `Passes.pure_rets_eq` (proved: a pure op's results
are a function of its arguments alone, in any state). What dominance buys is that
`d₀`'s binding is still the *current* one at every use of `d`: the pass only
inherits a table across a **single**-predecessor edge (`Passes.inEdgeSources`
returning `[p]` with `p < bi`), so `d₀`'s block dominates `d`'s block, and
`ToAsm.liveIn_of_succ` propagates that into the invariant. Without dominance the
substituted use can read a stale `d₀`, exactly as in the counterexample.

The static provenance obligation is now proved below: `Passes.cseBlock_spec`
resolves every dropped definition to either an earlier emitted definition in the
same block or `cseAvail`, while `Passes.cseAvail_succ` proves that inherited
availability comes from the actual unique predecessor; these facts close
`cse_dom`.  What remains here is their runtime analogue: carry, alongside the
register substitution invariant, that every entry-table representative contains
the value certified by its `CseDef`.  A kept instruction then steps on substituted
arguments, while a dropped `const`/pure op is skipped using that table fact and
`pure_rets_eq`; jumps hand the end-table fact to `cseAvail_succ`.

The runtime predicate and its lookup leaf are explicit above as
`CseTabRuntime` and `CseExprRuntime.op_result`.  Inherited tables are now
filtered by `Passes.inheritTab`.  `CseTabRuntime.setMany_inheritTab` proves the
corresponding jump frame directly: filter membership excludes target parameters
from both representatives and stored expression arguments, and
`Passes.substV_not_blockParam` shows that the final substitution cannot map an
avoided argument back to a target parameter.  Thus `Regs.setMany` preserves the
whole inherited runtime table without a reachability/path witness.

`cseInstrsOut`/`cseInstrsOut_eq_fold` above now expose the requested
intra-block fold as a recursive instruction list, so the kept/dropped cases can
be matched directly against `Exec`.

The repaired fold now also tracks `blockDefs` and `definedSoFar`; the checked
boundary immediately below records the remaining static-to-runtime bridge. -/

/-
**Current checked boundary after guard-certificate threading.**

The certificate loss described in the previous round is closed above:
`CseDropPos` and `CseEntryPos` retain the exact prefix/suffix witnesses,
`CseSubSound` and `CseTabSound` pair them with definition provenance, and
`csePrefixPosInv` preserves them through `csePrefix_succ` (including
`inheritTab`).  `cseFinalSubSound`, `cseEntryTab_sound`, and
`cseBlockTabOut_sound` expose the resulting final projections.

The remaining missing lemma is now purely the runtime three-way invariant.  At
each source configuration and for every final alias `τ[d]? = some d₀`, it
must retain exactly one of

    R d = none ∨ R d = R' d₀ ∨
      (the current point is before d's certified operation site ∧
       d is absent from the processed-prefix uses).

The local third branch follows directly from `CseDropPos.op`.  When a table
representative is rebound in an earlier block, `cse_alias_zone` supplies the
cross-block window; a read of `d` there would make d's defining block dominate
the reader via `blockDef_dominates_use`, contradicting that zone.  At the
certified drop site, `CseExprRuntime.op_result` changes the third branch to the
synced branch.  In parallel, `CseEntryPos.op` supplies the freshness premise for
`CseTabRuntime.set_of_fresh`; inherited entries use the same dominance
contradiction to show that none of their arguments is defined in the target
block.  These two projection lemmas, followed by the routine `Exec` induction,
were the intended final assembly.

**Current checked boundary.**  No table history is needed.  At every dynamic
block entry the runtime table is re-established: empty entry tables use
`CseTabRuntime.empty`, and a table inherited from the edge just taken uses
`CseTabRuntime.setMany_inheritTab`.  Within a block, `set_of_fresh`, `addConst`,
and `addOp` are the required local preservation leaves, while a dropped op is
discharged directly by `CseExprRuntime.op_result` against the *current* table.

The remaining unassembled goal is the register half of the lockstep.  For the
current source instruction `i`, its processed prefix `pre`, and a final alias,
the three-way clause must eliminate its window at an actual read:

    τ[d]? = some d0 → d ∈ i.uses → R d = some w → R' d0 = some w

The synced branch is immediate.  The same-block window is contradicted by the
`CseDropPos.op` prefix guard (and the entry argument guard for the drop
instruction itself); the cross-block window is contradicted by
`blockDef_dominates_use` together with `cse_alias_zone`.  After the dropped
instruction, `CseExprRuntime.op_result` establishes the synced branch.  This is
a per-visit preservation/consumption goal, not a path-indexed stored-argument
history theorem.

The fold certificate now additionally records that the dropped destination was
unmapped immediately before the operation (`CseDropPos.op`'s `σ[d]? = none`
field).  Independently, `AliasOrdered` and `csePrefix_ordered` prove that every
representative occurs strictly earlier in the global instruction-definition
order than its alias.  Both facts are checked above.

The former intermediate-alias leaf is now discharged by
`Passes.CseTabDomainSound` and `Passes.cse_drop_not_self_use`.  The former is
derived from the real instruction/block folds and proves the range-kept fact:
if a stored expression argument later becomes an alias key, it was a direct
source use at the kept representative instruction.  Thus an apparent snapshot
chain `x ↦ d ↦ d0` contradicts final `RangeFree`; same-block representatives
then contradict the prefix/order certificates, and inherited representatives
contradict dominance plus `cse_alias_zone`.

What remains is to package the already stated three-way register relation,
thread it together with `CseTabRuntime` through `cseInstrsOut`, and perform the
`Exec` induction.  At the `sorry` below Lean's exact target is

    Exec (model := model) P (Passes.cse f)
      (Regs.empty.setMany f.params args) st
      ⟨eb'.instrs, eb'.term⟩ res

under precisely the hypotheses displayed in `cse_sound`'s signature.
-/
theorem cse_sound {P : Prog} {f : Func} {args : List U256} {st : EvmState} {res : FRes}
    {eb eb' : Block} (hwf : f.wfCheck P.funcs.size = true)
    (hdom : ToAsm.Func.domCheck f = true)
    (heb : f.blocks[f.entry]? = some eb)
    (heb' : (Passes.cse f).blocks[f.entry]? = some eb')
    (hexec : Exec (model := model) P f (Regs.empty.setMany f.params args) st
      ⟨eb.instrs, eb.term⟩ res) :
    Exec (model := model) P (Passes.cse f) (Regs.empty.setMany f.params args) st
      ⟨eb'.instrs, eb'.term⟩ res := by
  have hnd : f.allDefs.Nodup := wfCheck_defs_nodup hwf
  obtain ⟨li, hli⟩ := ToAsm.liveInSets_isSome f
  have hfresh : Passes.CseFresh f := Passes.cseFresh hnd hwf hli hdom
  have hbout := Passes.cse_block_get heb
  rw [heb'] at hbout
  have heb'eq : eb' = Passes.substBlock (Passes.cseSub f)
      (Passes.cseBlockOut f f.entry) := by
    simpa [Passes.cseSub] using Option.some.inj hbout
  subst eb'
  have htab : CseTabRuntime (model := model) (Passes.cseSub f)
      (Regs.empty.setMany f.params args)
      (Passes.cseAt f f.entry eb []).2.1 := by
    simp [Passes.cseAt_nil, Passes.cseEntryTab, CseTabRuntime]
  have hsim := Passes.cse_exec_aux hwf hnd hli hdom hfresh hexec heb
    EntryPath.entry rfl rfl (CseAgree.of_entry rfl)
    (cseConstAgree_entry hnd args) (cseConstRegs_entry hnd args) htab
  have hentry : f.entry < f.blocks.size :=
    (Array.getElem?_eq_some_iff.mp heb).1
  have hbang : f.blocks[f.entry]! = eb := by
    rw [Passes.getElem!_eq_getElem hentry]
    exact (Array.getElem?_eq_some_iff.mp heb).2
  simpa [Passes.substBlock, Passes.cseBlockOut, hbang,
    Passes.cseInstrsOut_eq_fold, Passes.cseAt_nil,
    Passes.cseEntryTab] using hsim

/- **Pass 4 (dead value elimination) soundness.** No dominance hypothesis.

The proved simulation uses the invariant "`R` (original) and `R'` (optimized)
agree on every value in `Passes.liveSet f`", stepped with the frame lemma
`exec_congr`; the deleted instructions are exactly those whose destinations
nothing reads, so the invariant is preserved by construction and no dominance is
needed. `liveSet_closed` and `dveBlock_uses_live` now discharge the static
liveness half.  The remaining part is the runtime edge/parameter alignment
lemma: `dve` masks target parameters, incoming argument ids, and hence the values
returned by `Regs.getMany` at the same positions; the proof must show the two
filtered lists have equal length and that `Regs.setMany` preserves agreement on
the live set. -/

namespace Passes

/-- The positional parameter predicate used by DVE on every incoming edge. -/
def dveKeepParam (f : Func) (bi : BlockId) (i : Nat) : Bool :=
  match f.blocks[bi]? with
  | some b =>
    match b.params[i]? with
    | some p => (liveSet f).contains p
    | none => true
  | none => true

/-- The edge and terminator portions of `dveBlock`, named for the execution
simulation below. -/
def dveEdge (f : Func) (e : Edge) : Edge :=
  { e with args :=
      (e.args.zipIdx.filter fun ai => dveKeepParam f e.target ai.2).map (·.1) }

def dveTerm (f : Func) (t : Term) : Term := mapEdges (dveEdge f) t

theorem dveBlock_term (f : Func) (bi : BlockId) (b : Block) :
    (dveBlock f bi b).term = dveTerm f b.term := by
  rfl

theorem dveBlock_instrs (f : Func) (bi : BlockId) (b : Block) :
    (dveBlock f bi b).instrs = b.instrs.filter (dveKeepInstr (liveSet f)) := by
  rfl

/-- The slightly unusual `zipIdx` presentation of an edge mask is extensionally
the ordinary filtering of the zipped target parameters and edge arguments. -/
theorem dveEdge_args_eq_zip {f : Func} {e : Edge} {tb : Block}
    (htb : f.blocks[e.target]? = some tb)
    (hlen : e.args.length = tb.params.length) :
    (dveEdge f e).args =
      (tb.params.zip e.args |>.filter fun pa => (liveSet f).contains pa.1).map (·.2) := by
  simp only [dveEdge, dveKeepParam, htb]
  generalize tb.params = ps at hlen ⊢
  generalize e.args = xs at hlen ⊢
  induction xs generalizing ps with
  | nil =>
    have : ps = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
    simp [this]
  | cons a as ih =>
    cases ps with
    | nil => simp at hlen
    | cons p ps =>
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      simp only [List.zipIdx_cons]
      rw [show as.zipIdx 1 = as.zipIdx.map (fun ai => (ai.1, 1 + ai.2)) by
        simpa using (List.zipIdx_eq_map_add (l := as) (i := 1))]
      simp only [List.zipIdx_cons, List.getElem?_cons_zero, Option.some, List.filter_cons,
        List.map_cons, List.zip_cons_cons]
      simp only [List.filter_map]
      have hpred :
          ((fun ai : ValId × Nat =>
              match (p :: ps)[ai.2]? with
              | some p => (liveSet f).contains p
              | none => true) ∘ fun ai => (ai.1, 1 + ai.2)) =
            (fun ai : ValId × Nat =>
              match ps[ai.2]? with
              | some p => (liveSet f).contains p
              | none => true) := by
        funext ai
        simp [Function.comp_def, Nat.add_comm]
      rw [hpred]
      have hmap : ((fun x : ValId × Nat => x.1) ∘
          fun ai : ValId × Nat => (ai.1, 1 + ai.2)) =
          (fun x : ValId × Nat => x.1) := by rfl
      split
      · simp only [List.map_cons, List.map_map, hmap]
        exact congrArg (a :: ·) (ih ps hlen)
      · simp only [List.map_map, hmap]
        exact ih ps hlen

/-- Reading an edge after masking it returns the correspondingly masked values. -/
theorem filterGetMany {live : Std.HashSet ValId} {R R' : Regs}
    {ps xs : List ValId} {vs : List U256}
    (hlen : xs.length = ps.length) (hget : R.getMany xs = some vs)
    (hagree : ∀ x ∈ live, R x = R' x)
    (hselected : ∀ x ∈ (ps.zip xs |>.filter fun pa => live.contains pa.1).map (·.2),
      x ∈ live) :
    R'.getMany ((ps.zip xs |>.filter fun pa => live.contains pa.1).map (·.2)) =
      some ((ps.zip vs |>.filter fun pv => live.contains pv.1).map (·.2)) := by
  induction ps generalizing xs vs with
  | nil =>
    have hxs : xs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst xs
    simp only [Regs.getMany_nil, Option.some.injEq] at hget
    subst vs
    rfl
  | cons p ps ih =>
    cases xs with
    | nil => simp at hlen
    | cons a xs =>
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      rw [Regs.getMany_cons] at hget
      cases ha : R a with
      | none => simp [ha] at hget
      | some v =>
        cases htail : R.getMany xs with
        | none => simp [ha, htail] at hget
        | some vals =>
          simp only [ha, htail, Option.bind_some, Option.map_some, Option.some.injEq] at hget
          subst vs
          by_cases hp : p ∈ live
          · have hpB : live.contains p = true := Std.HashSet.mem_iff_contains.mp hp
            have haLive : a ∈ live := hselected a (by simp [hpB])
            have ha' : R' a = some v := by rw [← hagree a haLive, ha]
            simpa [hpB, Regs.getMany_cons, ha'] using
              ih hlen htail (fun x hx => hselected x (by simp [hpB, hx]))
          · have hpB : live.contains p = false := by
              exact Bool.eq_false_of_not_eq_true (fun h => hp (Std.HashSet.contains_iff_mem.mp h))
            simpa [hpB] using ih hlen htail
              (fun x hx => hselected x (by simp [hpB, hx]))

/-- Parallel binding by all target parameters agrees on live values with
binding only the live parameters and their positionally filtered values. -/
theorem filterSetMany {live : Std.HashSet ValId} {R R' : Regs}
    {ps : List ValId} {vs : List U256} (hnodup : ps.Nodup)
    (hlen : vs.length = ps.length) (hagree : ∀ x ∈ live, R x = R' x) :
    (ps.filter live.contains).length =
        ((ps.zip vs |>.filter fun pv => live.contains pv.1).map (·.2)).length
    ∧ ∀ x ∈ live,
      (R.setMany ps vs) x =
        (R'.setMany (ps.filter live.contains)
          ((ps.zip vs |>.filter fun pv => live.contains pv.1).map (·.2))) x := by
  induction ps generalizing R R' vs with
  | nil =>
    have hvs : vs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst vs
    exact ⟨rfl, hagree⟩
  | cons p ps ih =>
    cases vs with
    | nil => simp at hlen
    | cons v vs =>
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      rw [List.nodup_cons] at hnodup
      by_cases hp : p ∈ live
      · have hpB : live.contains p = true := Std.HashSet.mem_iff_contains.mp hp
        obtain ⟨hlen', hagree'⟩ := ih hnodup.2 hlen (Regs.set_congr hagree p v)
        exact ⟨by simp [hpB, hlen'], by simpa [hpB, Regs.setMany_cons] using hagree'⟩
      · have hpB : live.contains p = false := by
          exact Bool.eq_false_of_not_eq_true (fun h => hp (Std.HashSet.contains_iff_mem.mp h))
        have hagreeHead : ∀ x ∈ live, (R.set p v) x = R' x := by
          intro x hx
          rw [Regs.set_other _ _ (by intro heq; subst x; exact hp hx)]
          exact hagree x hx
        obtain ⟨hlen', hagree'⟩ := ih hnodup.2 hlen hagreeHead
        exact ⟨by simpa [hpB] using hlen',
          by simpa [hpB, Regs.setMany_cons] using hagree'⟩

theorem dveBlock_params {f : Func} {n : Nat} (hwf : f.wfCheck n = true)
    {bi : BlockId} {b : Block} (hb : f.blocks[bi]? = some b) :
    (dveBlock f bi b).params = b.params.filter (liveSet f).contains := by
  by_cases hi : bi = f.entry
  · subst bi
    unfold Func.wfCheck at hwf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hwf
    have he := hwf.1.2
    rw [hb] at he
    have hempty : b.params = [] := List.isEmpty_iff.mp he
    simp [dveBlock, hempty]
  · simp [dveBlock, hi]

theorem blockParams_nodup {f : Func} {n : Nat} (hwf : f.wfCheck n = true)
    {bi : BlockId} {b : Block} (hb : f.blocks[bi]? = some b) : b.params.Nodup := by
  have hnd := wfCheck_defs_nodup hwf
  have hbmem : b ∈ f.blocks.toList :=
    List.mem_of_getElem? (Array.getElem?_toList.trans hb)
  rw [List.nodup_iff_count_le_one]
  intro d
  have hall := List.nodup_iff_count_le_one.mp hnd d
  rw [allDefs_eq, List.count_append] at hall
  have hblock := count_le_count_flatMap
    (g := fun b : Block => blockAllDefs b) (d := d) hbmem
  change (b.params ++ b.instrs.flatMap Instr.defs).count d ≤
    (f.blocks.toList.flatMap blockAllDefs).count d at hblock
  rw [List.count_append] at hblock
  omega

theorem dveInstr_uses_live {f : Func} {n : Nat} (hwf : f.wfCheck n = true)
    {bi : BlockId} {b : Block} (hb : f.blocks[bi]? = some b)
    {i : Instr} (hi : i ∈ b.instrs) (hkeep : dveKeepInstr (liveSet f) i = true)
    {x : ValId} (hx : x ∈ i.uses) : x ∈ liveSet f := by
  apply dveBlock_uses_live hwf hb
  rw [ToAsm.mem_blockUses]
  exact Or.inl (List.mem_flatMap.mpr
    ⟨i, List.mem_filter.mpr ⟨hi, hkeep⟩, hx⟩)

theorem dveTerm_uses_live {f : Func} {n : Nat} (hwf : f.wfCheck n = true)
    {bi : BlockId} {b : Block} (hb : f.blocks[bi]? = some b)
    {x : ValId} (hx : x ∈ (dveTerm f b.term).uses) : x ∈ liveSet f := by
  apply dveBlock_uses_live hwf hb
  rw [ToAsm.mem_blockUses]
  exact Or.inr (by simpa [dveBlock_term] using hx)

theorem dveEdge_args_live {f : Func} {n : Nat} (hwf : f.wfCheck n = true)
    {bi : BlockId} {b : Block} (hb : f.blocks[bi]? = some b)
    {e : Edge} (he : e ∈ b.term.edges) {x : ValId} (hx : x ∈ (dveEdge f e).args) :
    x ∈ liveSet f := by
  apply dveTerm_uses_live hwf hb
  cases ht : b.term with
  | jump ej =>
    simp only [ht, Term.edges, List.mem_singleton] at he
    subst ej
    simpa [dveTerm, mapEdges, Term.uses] using hx
  | branch c et ef =>
    simp only [ht, Term.edges, List.mem_cons] at he
    rcases he with rfl | he
    · simp [dveTerm, ht, mapEdges, Term.uses, hx]
    · have he' : e = ef := by simpa using he
      subst e
      simp [dveTerm, ht, mapEdges, Term.uses, hx]
  | ret vs => simp [ht, Term.edges] at he
  | halt yop as => simp [ht, Term.edges] at he

theorem getMany_length_dve {R : Regs} {xs : List ValId} {vs : List U256}
    (h : R.getMany xs = some vs) : xs.length = vs.length := by
  induction xs generalizing vs with
  | nil => simp only [Regs.getMany_nil, Option.some.injEq] at h; subst vs; rfl
  | cons x xs ih =>
    rw [Regs.getMany_cons] at h
    cases hx : R x with
    | none => simp [hx] at h
    | some v =>
      cases hxs : R.getMany xs with
      | none => simp [hx, hxs] at h
      | some vals =>
        simp only [hx, hxs, Option.bind_some, Option.map_some, Option.some.injEq] at h
        subst vs
        simp [ih hxs]

/-- DVE simulates any suffix of a source block while the two register files
agree on the closed live set. -/
theorem dve_exec_aux {P : Prog} {f : Func} (hwf : f.wfCheck P.funcs.size = true)
    {R : Regs} {st : EvmState} {rest : Rest} {res : FRes}
    (hexec : Exec (model := model) P f R st rest res) :
    ∀ {bi : BlockId} {b : Block} {R' : Regs},
      f.blocks[bi]? = some b → rest.term = b.term → rest.instrs <:+ b.instrs →
      (∀ x ∈ liveSet f, R x = R' x) →
      Exec (model := model) P (dve f) R' st
        ⟨rest.instrs.filter (dveKeepInstr (liveSet f)), dveTerm f rest.term⟩ res := by
  induction hexec with
  | @const f R st d v is t res hnext ih =>
    intro bi b R' hb ht hs hagree
    have hs' : is <:+ b.instrs :=
      List.IsSuffix.trans (show is <:+ .const d v :: is from ⟨[.const d v], rfl⟩) hs
    by_cases hd : d ∈ liveSet f
    · have hdB : (liveSet f).contains d = true := Std.HashSet.mem_iff_contains.mp hd
      simp only [List.filter_cons, dveKeepInstr, hdB, if_true]
      exact Exec.const (ih hwf hb ht hs' (Regs.set_congr hagree d v))
    · have hdB : (liveSet f).contains d = false := by
        exact Bool.eq_false_of_not_eq_true (fun h => hd (Std.HashSet.contains_iff_mem.mp h))
      simp only [List.filter_cons, dveKeepInstr, hdB, if_false]
      apply ih hwf hb ht hs'
      intro x hx
      rw [Regs.set_other _ _ (by intro heq; subst x; exact hd hx)]
      exact hagree x hx
  | @op f R st st' ds yop as args rets is t res hget hbi hlen hnext ih =>
    intro bi b R' hb ht hs hagree
    have hs' : is <:+ b.instrs :=
      List.IsSuffix.trans (show is <:+ .op ds yop as :: is from ⟨[.op ds yop as], rfl⟩) hs
    have hi : .op ds yop as ∈ b.instrs := hs.mem (by simp)
    by_cases hk : (!pureOp yop || ds.any (liveSet f).contains) = true
    · have hargs : ∀ x ∈ as, x ∈ liveSet f := by
        intro x hx
        exact dveInstr_uses_live hwf hb hi (by simpa [dveKeepInstr] using hk)
          (by simpa [Instr.uses] using hx)
      have hget' : R'.getMany as = some args := by
        rw [← Regs.getMany_congr (R1 := R) (R2 := R')
          (fun x hx => hagree x (hargs x hx))]
        exact hget
      simp only [List.filter_cons, dveKeepInstr, hk, if_true]
      exact Exec.op hget' hbi hlen
        (ih hwf hb ht hs' (Regs.setMany_congr hagree ds rets))
    · have hk' : (!pureOp yop || ds.any (liveSet f).contains) = false :=
        Bool.eq_false_of_not_eq_true hk
      have hp : pureOp yop = true := by
        cases hpy : pureOp yop <;> simp_all
      have hds : ∀ x ∈ liveSet f, x ∉ ds := by
        intro x hx hxd
        have : ds.any (liveSet f).contains = true :=
          List.any_eq_true.mpr ⟨x, hxd, Std.HashSet.mem_iff_contains.mp hx⟩
        simp [this] at hk'
      have hst : st' = st := pure_state_eq hp hbi
      subst st'
      simp only [List.filter_cons, dveKeepInstr, hk', if_false]
      apply ih hwf hb ht hs'
      intro x hx
      rw [Regs.setMany_of_not_mem _ ds rets (hds x hx)]
      exact hagree x hx
  | @opHalt f R st st' ds yop as args is t hget hbi =>
    intro bi b R' hb ht hs hagree
    have hi : .op ds yop as ∈ b.instrs := hs.mem (by simp)
    have hkeep : (!pureOp yop || ds.any (liveSet f).contains) = true := by
      by_contra hk
      have hk' : (!pureOp yop || ds.any (liveSet f).contains) = false := by
        exact Bool.eq_false_of_not_eq_true hk
      have hp : pureOp yop = true := by
        cases hpy : pureOp yop <;> simp_all
      exact Passes.pure_no_halt hp hbi
    have hargs : ∀ x ∈ as, x ∈ liveSet f := by
      intro x hx
      exact dveInstr_uses_live hwf hb hi (by simpa [dveKeepInstr] using hkeep)
        (by simpa [Instr.uses] using hx)
    have hget' : R'.getMany as = some args := by
      rw [← Regs.getMany_congr (R1 := R) (R2 := R')
        (fun x hx => hagree x (hargs x hx))]
      exact hget
    simp only [List.filter_cons, dveKeepInstr, hkeep, if_true]
    exact Exec.opHalt hget' hbi
  | @call f g R st st' ds as fid args rvals eb is t res hfid hget hplen heb hbody hlen hnext ihbody ih =>
    intro bi b R' hb ht hs hagree
    have hs' : is <:+ b.instrs :=
      List.IsSuffix.trans (show is <:+ .call ds fid as :: is from ⟨[.call ds fid as], rfl⟩) hs
    have hi : .call ds fid as ∈ b.instrs := hs.mem (by simp)
    have hargs : ∀ x ∈ as, x ∈ liveSet f := by
      intro x hx
      exact dveInstr_uses_live hwf hb hi (by simp [dveKeepInstr])
        (by simpa [Instr.uses] using hx)
    have hget' : R'.getMany as = some args := by
      rw [← Regs.getMany_congr (R1 := R) (R2 := R')
        (fun x hx => hagree x (hargs x hx))]
      exact hget
    simp only [List.filter_cons, dveKeepInstr, Bool.true_eq, if_true]
    exact Exec.call hfid hget' hplen heb hbody hlen
      (ih hwf hb ht hs' (Regs.setMany_congr hagree ds rvals))
  | @callHalt f g R st st' ds as fid args eb is t hfid hget hplen heb hbody ihbody =>
    intro bi b R' hb ht hs hagree
    have hi : .call ds fid as ∈ b.instrs := hs.mem (by simp)
    have hargs : ∀ x ∈ as, x ∈ liveSet f := by
      intro x hx
      exact dveInstr_uses_live hwf hb hi (by simp [dveKeepInstr])
        (by simpa [Instr.uses] using hx)
    have hget' : R'.getMany as = some args := by
      rw [← Regs.getMany_congr (R1 := R) (R2 := R')
        (fun x hx => hagree x (hargs x hx))]
      exact hget
    simp only [List.filter_cons, dveKeepInstr, Bool.true_eq, if_true]
    exact Exec.callHalt hfid hget' hplen heb hbody
  | @jump f R st e tb vals res htb hget hlen hnext ih =>
    intro bi b R' hb ht hs hagree
    have he : e ∈ b.term.edges := by rw [← ht]; simp [Term.edges]
    have harity : e.args.length = tb.params.length := by
      rw [getMany_length_dve hget, hlen]
    have hedge := dveEdge_args_eq_zip htb harity
    have hselected :
        ∀ x ∈ (tb.params.zip e.args |>.filter fun pa => (liveSet f).contains pa.1).map (·.2),
          x ∈ liveSet f := by
      intro x hx
      apply dveEdge_args_live hwf hb he
      rw [hedge]
      exact hx
    have hget' := filterGetMany harity hget hagree hselected
    obtain ⟨hlen', hagree'⟩ := filterSetMany (blockParams_nodup hwf htb) hlen.symm hagree
    have htb' : (dve f).blocks[e.target]? = some (dveBlock f e.target tb) := by
      rw [dve_blocks_get, htb]
      rfl
    have hbody := ih hwf htb rfl (show tb.instrs <:+ tb.instrs from ⟨[], rfl⟩) hagree'
    have hout : Exec (model := model) P (dve f) R' st
        ⟨[], .jump (dveEdge f e)⟩ res := by
      refine Exec.jump (args :=
        (tb.params.zip vals |>.filter fun pv => (liveSet f).contains pv.1).map (·.2))
        htb' ?_ ?_ ?_
      · rw [hedge]
        exact hget'
      · rw [dveBlock_params hwf htb]
        exact hlen'
      · rw [dveBlock_params hwf htb]
        simpa [dveBlock_instrs, dveBlock_term] using hbody
    simpa [dveTerm, mapEdges] using hout
  | @branchTrue f R st c v et ef tb vals res hc hv htb hget hlen hnext ih =>
    intro bi b R' hb ht hs hagree
    have hcLive : c ∈ liveSet f := by
      apply dveTerm_uses_live hwf hb
      rw [← ht]
      simp [dveTerm, mapEdges, Term.uses]
    have hc' : R' c = some v := by rw [← hagree c hcLive]; exact hc
    have he : et ∈ b.term.edges := by rw [← ht]; simp [Term.edges]
    have harity : et.args.length = tb.params.length := by
      rw [getMany_length_dve hget, hlen]
    have hedge := dveEdge_args_eq_zip htb harity
    have hselected :
        ∀ x ∈ (tb.params.zip et.args |>.filter fun pa => (liveSet f).contains pa.1).map (·.2),
          x ∈ liveSet f := by
      intro x hx
      apply dveEdge_args_live hwf hb he
      rw [hedge]
      exact hx
    have hget' := filterGetMany harity hget hagree hselected
    obtain ⟨hlen', hagree'⟩ := filterSetMany (blockParams_nodup hwf htb) hlen.symm hagree
    have htb' : (dve f).blocks[et.target]? = some (dveBlock f et.target tb) := by
      rw [dve_blocks_get, htb]
      rfl
    have hbody := ih hwf htb rfl (show tb.instrs <:+ tb.instrs from ⟨[], rfl⟩) hagree'
    have hout : Exec (model := model) P (dve f) R' st
        ⟨[], .branch c (dveEdge f et) (dveEdge f ef)⟩ res := by
      refine Exec.branchTrue (v := v) (args :=
        (tb.params.zip vals |>.filter fun pv => (liveSet f).contains pv.1).map (·.2))
        hc' hv htb' ?_ ?_ ?_
      · rw [hedge]
        exact hget'
      · rw [dveBlock_params hwf htb]
        exact hlen'
      · rw [dveBlock_params hwf htb]
        simpa [dveBlock_instrs, dveBlock_term] using hbody
    simpa [dveTerm, mapEdges] using hout
  | @branchFalse f R st c et ef tb vals res hc htb hget hlen hnext ih =>
    intro bi b R' hb ht hs hagree
    have hcLive : c ∈ liveSet f := by
      apply dveTerm_uses_live hwf hb
      rw [← ht]
      simp [dveTerm, mapEdges, Term.uses]
    have hc' : R' c = some 0 := by rw [← hagree c hcLive]; exact hc
    have he : ef ∈ b.term.edges := by rw [← ht]; simp [Term.edges]
    have harity : ef.args.length = tb.params.length := by
      rw [getMany_length_dve hget, hlen]
    have hedge := dveEdge_args_eq_zip htb harity
    have hselected :
        ∀ x ∈ (tb.params.zip ef.args |>.filter fun pa => (liveSet f).contains pa.1).map (·.2),
          x ∈ liveSet f := by
      intro x hx
      apply dveEdge_args_live hwf hb he
      rw [hedge]
      exact hx
    have hget' := filterGetMany harity hget hagree hselected
    obtain ⟨hlen', hagree'⟩ := filterSetMany (blockParams_nodup hwf htb) hlen.symm hagree
    have htb' : (dve f).blocks[ef.target]? = some (dveBlock f ef.target tb) := by
      rw [dve_blocks_get, htb]
      rfl
    have hbody := ih hwf htb rfl (show tb.instrs <:+ tb.instrs from ⟨[], rfl⟩) hagree'
    have hout : Exec (model := model) P (dve f) R' st
        ⟨[], .branch c (dveEdge f et) (dveEdge f ef)⟩ res := by
      refine Exec.branchFalse (args :=
        (tb.params.zip vals |>.filter fun pv => (liveSet f).contains pv.1).map (·.2))
        hc' htb' ?_ ?_ ?_
      · rw [hedge]
        exact hget'
      · rw [dveBlock_params hwf htb]
        exact hlen'
      · rw [dveBlock_params hwf htb]
        simpa [dveBlock_instrs, dveBlock_term] using hbody
    simpa [dveTerm, mapEdges] using hout
  | @ret f R st xs vals hget =>
    intro bi b R' hb ht hs hagree
    have hxs : ∀ x ∈ xs, x ∈ liveSet f := by
      intro x hx
      apply dveTerm_uses_live hwf hb
      rw [← ht]
      simpa [dveTerm, mapEdges, Term.uses] using hx
    have hget' : R'.getMany xs = some vals := by
      rw [← Regs.getMany_congr (R1 := R) (R2 := R')
        (fun x hx => hagree x (hxs x hx))]
      exact hget
    simpa [dveTerm, mapEdges] using (Exec.ret (P := P) (f := dve f) hget')
  | @halt f R st st' yop as args hget hbi =>
    intro bi b R' hb ht hs hagree
    have has : ∀ x ∈ as, x ∈ liveSet f := by
      intro x hx
      apply dveTerm_uses_live hwf hb
      rw [← ht]
      simpa [dveTerm, mapEdges, Term.uses] using hx
    have hget' : R'.getMany as = some args := by
      rw [← Regs.getMany_congr (R1 := R) (R2 := R')
        (fun x hx => hagree x (has x hx))]
      exact hget
    simpa [dveTerm, mapEdges] using
      (Exec.halt (P := P) (f := dve f) hget' hbi)

end Passes

theorem dve_sound {P : Prog} {f : Func} {args : List U256} {st : EvmState} {res : FRes}
    {eb eb' : Block} (hwf : f.wfCheck P.funcs.size = true)
    (heb : f.blocks[f.entry]? = some eb)
    (heb' : (Passes.dve f).blocks[f.entry]? = some eb')
    (hexec : Exec (model := model) P f (Regs.empty.setMany f.params args) st
      ⟨eb.instrs, eb.term⟩ res) :
    Exec (model := model) P (Passes.dve f) (Regs.empty.setMany f.params args) st
      ⟨eb'.instrs, eb'.term⟩ res := by
  rw [Passes.dve_blocks_get, heb] at heb'
  have hebEq : eb' = Passes.dveBlock f f.entry eb := by
    simpa using (Option.some.inj heb').symm
  subst eb'
  have hsim := Passes.dve_exec_aux hwf hexec heb rfl
    (show eb.instrs <:+ eb.instrs from ⟨[], rfl⟩)
    (fun _ _ => rfl)
  simpa [Passes.dveBlock_instrs, Passes.dveBlock_term] using hsim

/-! ### Well-formedness preservation for the four local passes -/

namespace Passes

omit model in
@[simp] theorem substTerm_edges_eq (σ : Subst) (t : Term) :
    (substTerm σ t).edges = t.edges.map (substEdge σ) := by
  cases t <;> rfl

omit model in
theorem BlockWF.subst {σ : Subst} {f : Func} {b : Block} {n : Nat}
    (h : BlockWF f.blocks f.nrets n b) :
    BlockWF (substFunc σ f).blocks (substFunc σ f).nrets n (substBlock σ b) := by
  refine ⟨?_, ?_, ?_⟩
  · rcases ht : b.term with e | ⟨c, et, ef⟩ | xs | ⟨yop, as⟩ <;>
      simpa [substBlock, substTerm, substVs, substFunc, ht] using h.1
  · intro e he
    simp only [substBlock, substTerm_edges_eq, List.mem_map] at he
    obtain ⟨e0, he0, rfl⟩ := he
    obtain ⟨tb, htb, hlen⟩ := h.2.1 e0 he0
    refine ⟨substBlock σ tb, ?_, ?_⟩
    · change (f.blocks.map (substBlock σ))[e0.target]? = some (substBlock σ tb)
      rw [Array.getElem?_map, htb]
      rfl
    · simpa [substEdge, substVs, substBlock] using hlen
  · intro i hi
    simp only [substBlock, List.mem_map] at hi
    obtain ⟨i0, hi0, rfl⟩ := hi
    have hw := h.2.2 i0 hi0
    cases i0 <;> simpa [substInstr] using hw

omit model in
theorem substFunc_wf {σ : Subst} {f : Func} {n : Nat}
    (hwf : f.wfCheck n = true) : (substFunc σ f).wfCheck n = true := by
  obtain ⟨hnd, hentry, ⟨eb, heb, hempty⟩, hall⟩ := func_wfCheck_iff.mp hwf
  apply func_wfCheck_iff.mpr
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [substFunc_allDefs] using hnd
  · simpa [substFunc] using hentry
  · refine ⟨substBlock σ eb, ?_, ?_⟩
    · simp [substFunc, heb]
    · simpa [substBlock] using hempty
  · intro b' hb'
    simp only [substFunc, Array.toList_map, List.mem_map] at hb'
    obtain ⟨b, hb, rfl⟩ := hb'
    exact (hall b hb).subst

omit model in
theorem removedBlock_instrs (bi i j : Nat) (b : Block) :
    (removedBlock bi i j b).instrs = b.instrs := by
  by_cases h : j = bi <;> simp only [removedBlock, h, if_true, if_false]

omit model in
theorem removedBlock_term (bi i j : Nat) (b : Block) :
    (removedBlock bi i j b).term = mapEdges (elimEdge bi i) b.term := by
  by_cases h : j = bi <;> simp only [removedBlock, h, if_true, if_false]
  all_goals rfl

omit model in
theorem removeParam_wf {f : Func} {n bi i p v : Nat}
    (hwf : f.wfCheck n = true)
    (hfind : findTrivialParam f = some (bi, i, p, v)) :
    (removeParam f bi i).wfCheck n = true := by
  obtain ⟨hbi, hbientry, hi, hp, -, -, -, -⟩ := findTrivialParam_inv hfind
  obtain ⟨hnd, hentry, ⟨eb, heb, hempty⟩, hall⟩ := func_wfCheck_iff.mp hwf
  have hpb : f.blocks[bi]? = some f.blocks[bi] := Array.getElem?_eq_getElem hbi
  have hi' : i < f.blocks[bi].params.length := by
    simpa [getElem!_eq_getElem hbi] using hi
  apply func_wfCheck_iff.mpr
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hnd.sublist (removeParam_allDefs_sublist f bi i)
  · simpa [removeParam] using hentry
  · refine ⟨removedBlock bi i f.entry eb, removeParam_blocks_get heb, ?_⟩
    simpa [removedBlock, Ne.symm hbientry] using hempty
  · intro b' hb'
    have hbmem : b' ∈ (removeParam f bi i).blocks := by simpa using hb'
    obtain ⟨j, hjlt, rfl⟩ := Array.mem_iff_getElem.mp hbmem
    have hjlt' : j < f.blocks.size := by simpa [removeParam] using hjlt
    let b := f.blocks[j]
    have hb : f.blocks[j]? = some b := Array.getElem?_eq_getElem hjlt'
    have hbout := removeParam_blocks_get (bi := bi) (i := i) hb
    have hb'eq : (removeParam f bi i).blocks[j] = removedBlock bi i j b := by
      have hget : (removeParam f bi i).blocks[j]? =
          some (removeParam f bi i).blocks[j] := Array.getElem?_eq_getElem hjlt
      exact Option.some.inj (hget.symm.trans hbout)
    rw [hb'eq]
    have hbwf := hall b (block_mem_of_getElem? hb)
    refine ⟨?_, ?_, ?_⟩
    · cases ht : b.term <;>
        simpa [removedBlock_term, removeParam, mapEdges, ht] using hbwf.1
    · intro e he
      rw [removedBlock_term] at he
      obtain ⟨e0, he0, rfl⟩ := mapEdges_edges b.term he
      obtain ⟨tb, htb, hlen⟩ := hbwf.2.1 e0 he0
      refine ⟨removedBlock bi i e0.target tb, ?_, ?_⟩
      · have htarget : (elimEdge bi i e0).target = e0.target := by
          unfold elimEdge
          split <;> rfl
        rw [htarget]
        exact removeParam_blocks_get htb
      · by_cases het : e0.target = bi
        · rw [het] at htb
          have htbeq : tb = f.blocks[bi] := Option.some.inj (htb.symm.trans hpb)
          subst tb
          have hargs : (elimEdge bi i e0).args = e0.args.eraseIdx i := by
            simp [elimEdge, het]
          rw [hargs, List.length_eraseIdx, hlen]
          rw [if_pos hi']
          unfold removedBlock
          dsimp only
          rw [if_pos het]
          rw [List.length_eraseIdx, if_pos hi']
        · simpa [elimEdge, removedBlock, het] using hlen
    · intro ins hins
      rw [removedBlock_instrs] at hins
      exact hbwf.2.2 ins hins

omit model in
/-- Pass 1 preserves the backend well-formedness check at every removal. -/
theorem elimTrivialParams_wf {f : Func} {n : Nat}
    (hwf : f.wfCheck n = true) :
    (elimTrivialParams f).wfCheck n = true := by
  have loopInv : ∀ (xs : List Nat) (r : ElimTrivialLoopState),
      r.2.wfCheck n = true → r.1.getD r.2 = r.2 →
      let out := loopWith elimTrivialStep xs r
      out.2.wfCheck n = true ∧ out.1.getD out.2 = out.2 := by
    intro xs
    induction xs with
    | nil => intro r hr hrout; exact ⟨hr, hrout⟩
    | cons k ks ih =>
        intro r hr hrout
        rw [loopWith_cons]
        unfold elimTrivialStep
        cases hfind : findTrivialParam r.2 with
        | none => exact ⟨hr, by simp⟩
        | some q =>
            obtain ⟨bi, i, p, v⟩ := q
            apply ih
            · exact substFunc_wf (removeParam_wf hr hfind)
            · rfl
  rw [elimTrivialParams_eq_loop]
  let r := loopWith elimTrivialStep
    (List.range' 0 (elimTrivialFuel f) 1) (⟨none, f⟩ : ElimTrivialLoopState)
  have hr := loopInv (List.range' 0 (elimTrivialFuel f) 1)
    (⟨none, f⟩ : ElimTrivialLoopState) hwf rfl
  change r.2.wfCheck n = true ∧ r.1.getD r.2 = r.2 at hr
  rw [hr.2]
  exact hr.1

omit model in
theorem cfInstrOut_defs (i : Instr) (m : Std.HashMap ValId U256) :
    (cfInstrOut i m).defs = i.defs := by
  cases i with
  | const => rfl
  | call => rfl
  | op ds yop as =>
      cases ds with
      | nil => rfl
      | cons d ds =>
          cases ds with
          | nil => simp only [cfInstrOut]; split <;> rfl
          | cons e es => rfl

omit model in
theorem cfInstrs_defs (is : List Instr) (m : Std.HashMap ValId U256) :
    (is.foldl (fun s i => cfInstrStep i s) ⟨m, []⟩).2.reverse.flatMap Instr.defs =
      is.flatMap Instr.defs := by
  induction is generalizing m with
  | nil => rfl
  | cons i is ih =>
      rw [cfInstr_fold_cons, List.flatMap_cons, List.flatMap_cons,
        cfInstrOut_defs, ih]

omit model in
theorem cfBlockOut_allDefs (b : Block) (m : Std.HashMap ValId U256) :
    blockAllDefs (cfBlockOut b m) = blockAllDefs b := by
  simp only [blockAllDefs, cfBlockOut]
  rw [cfInstrs_defs]

omit model in
theorem cfBlock_fold_allDefs (bs : List Block) (st : CFOuter) :
    ((bs.foldl (fun s b => cfBlockStep b s) st).1.toList.flatMap blockAllDefs) =
      st.1.toList.flatMap blockAllDefs ++ bs.flatMap blockAllDefs := by
  induction bs generalizing st with
  | nil => simp
  | cons b bs ih =>
      rw [List.foldl_cons, ih]
      simp only [cfBlockStep_eq', Array.toList_push, List.flatMap_append,
        List.flatMap_singleton, cfBlockOut_allDefs, List.append_assoc]
      simp [blockAllDefs, List.append_assoc]

omit model in
theorem constFold_allDefs (f : Func) : (constFold f).allDefs = f.allDefs := by
  unfold Func.allDefs
  rw [constFold_blocks_eq, cfBlock_fold_allDefs]
  rfl

omit model in
theorem cfBlock_fold_size (bs : List Block) (st : CFOuter) :
    (bs.foldl (fun s b => cfBlockStep b s) st).1.size = st.1.size + bs.length := by
  induction bs generalizing st with
  | nil => simp
  | cons b bs ih =>
      rw [List.foldl_cons, ih]
      simp only [cfBlockStep_eq', Array.size_push, List.length_cons]
      omega

omit model in
theorem constFold_size (f : Func) : (constFold f).blocks.size = f.blocks.size := by
  rw [constFold_blocks_eq, cfBlock_fold_size]
  simp

omit model in
theorem cfInstrOut_check {n : Nat} {i : Instr} {m : Std.HashMap ValId U256}
    (h : match i with
      | .op ds _ _ => ds.length ≤ 1
      | .call _ g _ => g < n
      | _ => True) :
    match cfInstrOut i m with
    | .op ds _ _ => ds.length ≤ 1
    | .call _ g _ => g < n
    | _ => True := by
  cases i with
  | const => trivial
  | call => exact h
  | op ds yop as =>
      cases ds with
      | nil => exact h
      | cons d ds =>
          cases ds with
          | nil =>
              simp only [cfInstrOut]
              split <;> grind
          | cons e es => exact h

omit model in
theorem cfInstrs_check {n : Nat} {is : List Instr} {m : Std.HashMap ValId U256}
    (h : ∀ i ∈ is, match i with
      | .op ds _ _ => ds.length ≤ 1
      | .call _ g _ => g < n
      | _ => True) :
    ∀ i ∈ (is.foldl (fun s i => cfInstrStep i s) ⟨m, []⟩).2.reverse,
      match i with
      | .op ds _ _ => ds.length ≤ 1
      | .call _ g _ => g < n
      | _ => True := by
  induction is generalizing m with
  | nil => simp
  | cons i is ih =>
      rw [cfInstr_fold_cons]
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact cfInstrOut_check (h i (by simp))
      · exact ih (fun k hk => h k (by simp [hk])) j hj

omit model in
theorem cfTerm_edge_mem (b : Block) (m : Std.HashMap ValId U256) {e : Edge}
    (he : e ∈ (cfTerm b m).edges) : e ∈ b.term.edges := by
  rcases cfTerm_cases b m with h | ⟨e0, he0, h⟩
  · simpa [h] using he
  · have heq : e = e0 := by simpa [h, Term.edges] using he
    simpa [heq] using he0

omit model in
theorem cfBlockOut_wf {f : Func} {b : Block} {m : Std.HashMap ValId U256}
    {n : Nat} (hwf : f.wfCheck n = true) (hb : b ∈ f.blocks.toList)
    (h : BlockWF f.blocks f.nrets n b) :
    BlockWF (constFold f).blocks (constFold f).nrets n (cfBlockOut b m) := by
  refine ⟨?_, ?_, ?_⟩
  · rcases ht : b.term with e | ⟨c, et, ef⟩ | xs | ⟨yop, as⟩
    · simp [cfBlockOut, cfTerm, ht]
    · cases hc : (b.instrs.foldl (fun s i => cfInstrStep i s) ⟨m, []⟩).1[c]?
        <;> simp [cfBlockOut, cfTerm, ht, hc, constFold]
    · simpa [cfBlockOut, cfTerm, constFold, ht] using h.1
    · simp [cfBlockOut, cfTerm, ht]
  · intro e he
    have hecf : e ∈ (cfTerm b
        (b.instrs.foldl (fun s i => cfInstrStep i s) ⟨m, []⟩).1).edges := by
      simpa [cfBlockOut] using he
    have he0 := cfTerm_edge_mem b _ hecf
    obtain ⟨tb, htb, hlen⟩ := h.2.1 e he0
    obtain ⟨mt, htb', -⟩ := constFold_block_get_sound htb
    refine ⟨cfBlockOut tb mt, htb', ?_⟩
    simpa [cfBlockOut] using hlen
  · intro i hi
    apply cfInstrs_check h.2.2 i
    simpa [cfBlockOut] using hi

omit model in
/-- Pass 2 preserves the backend well-formedness check. -/
theorem constFold_wf {f : Func} {n : Nat} (hwf : f.wfCheck n = true) :
    (constFold f).wfCheck n = true := by
  obtain ⟨hnd, hentry, ⟨eb, heb, hempty⟩, hall⟩ := func_wfCheck_iff.mp hwf
  apply func_wfCheck_iff.mpr
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [constFold_allDefs] using hnd
  · change f.entry < (constFold f).blocks.size
    rw [constFold_size]
    exact hentry
  · obtain ⟨m, heb', -⟩ := constFold_block_get_sound heb
    refine ⟨cfBlockOut eb m, heb', ?_⟩
    simpa [cfBlockOut] using hempty
  · intro b' hb'
    have hbmem : b' ∈ (constFold f).blocks := by simpa using hb'
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hbmem
    have hout : (constFold f).blocks[i]? = some (constFold f).blocks[i] :=
      Array.getElem?_eq_getElem hi
    obtain ⟨b, hb, hrel⟩ := constFold_spec f i (constFold f).blocks[i] hout
    obtain ⟨m, hbout, -⟩ := constFold_block_get_sound hb
    have heq : (constFold f).blocks[i] = cfBlockOut b m :=
      Option.some.inj (hout.symm.trans hbout)
    rw [heq]
    exact cfBlockOut_wf hwf (block_mem_of_getElem? hb) (hall b (block_mem_of_getElem? hb))

omit model in
@[simp] theorem substInstr_defs_eq (σ : Subst) (i : Instr) :
    (substInstr σ i).defs = i.defs := by
  cases i <;> rfl

omit model in
@[simp] theorem flatMap_substInstr_defs (σ : Subst) (is : List Instr) :
    (is.map (substInstr σ)).flatMap Instr.defs = is.flatMap Instr.defs := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [ih]

omit model in
theorem substInstr_check {n : Nat} {σ : Subst} {i : Instr}
    (h : match i with
      | .op ds _ _ => ds.length ≤ 1
      | .call _ g _ => g < n
      | _ => True) :
    match substInstr σ i with
    | .op ds _ _ => ds.length ≤ 1
    | .call _ g _ => g < n
    | _ => True := by
  cases i <;> exact h

omit model in
theorem cseInstrsOut_defs_sublist (τ : Subst) (is : List Instr)
    (tab : CseTab) (used : Std.HashSet ValId) (σ : Subst)
    (defined blockDefs : Std.HashSet ValId) :
    List.Sublist
      ((cseInstrsOut τ is tab used σ defined blockDefs).flatMap Instr.defs)
      (is.flatMap Instr.defs) := by
  induction is generalizing tab used σ defined blockDefs with
  | nil => exact .slnil
  | cons i is ih =>
      let s := cseInstrStep i ⟨[], tab, used, σ, defined, blockDefs⟩
      have hs : s.1 = [] ∨ s.1 = [substInstr σ i] := by
        simpa [s] using (cseInstrStep_out (i := i) (acc := []) (tab := tab)
          (used := used) (σ := σ) (defined := defined) (blockDefs := blockDefs))
      rw [cseInstrsOut]
      rcases hs with hs | hs
      · rw [hs]
        simp only [List.reverse_nil, List.map_nil, List.nil_append, List.flatMap_cons]
        exact (ih s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2.1 s.2.2.2.2.2).trans
          (List.sublist_append_right _ _)
      · rw [hs]
        simp only [List.reverse_singleton, List.map_singleton, List.singleton_append,
          List.flatMap_cons, substInstr_defs_eq]
        exact (List.Sublist.refl i.defs).append
          (ih s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2.1 s.2.2.2.2.2)

omit model in
theorem cseInstrsOut_check {n : Nat} (τ : Subst) (is : List Instr)
    (tab : CseTab) (used : Std.HashSet ValId) (σ : Subst)
    (defined blockDefs : Std.HashSet ValId)
    (h : ∀ i ∈ is, match i with
      | .op ds _ _ => ds.length ≤ 1
      | .call _ g _ => g < n
      | _ => True) :
    ∀ i ∈ cseInstrsOut τ is tab used σ defined blockDefs,
      match i with
      | .op ds _ _ => ds.length ≤ 1
      | .call _ g _ => g < n
      | _ => True := by
  induction is generalizing tab used σ defined blockDefs with
  | nil => simp [cseInstrsOut]
  | cons i is ih =>
      let s := cseInstrStep i ⟨[], tab, used, σ, defined, blockDefs⟩
      have hs : s.1 = [] ∨ s.1 = [substInstr σ i] := by
        simpa [s] using (cseInstrStep_out (i := i) (acc := []) (tab := tab)
          (used := used) (σ := σ) (defined := defined) (blockDefs := blockDefs))
      rw [cseInstrsOut]
      intro j hj
      rw [List.mem_append] at hj
      rcases hj with hj | hj
      · have hj' : j ∈ s.1.reverse.map (substInstr τ) := by simpa [s] using hj
        rcases hs with hs | hs
        · simp [hs] at hj'
        · simp only [hs, List.reverse_singleton, List.map_singleton,
            List.mem_singleton] at hj'
          have hj := hj'
          subst j
          exact substInstr_check (substInstr_check (h i (by simp)))
      · exact ih s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2.1 s.2.2.2.2.2
          (fun k hk => h k (by simp [hk])) j hj

omit model in
theorem cseBlockOut_defs_sublist (f : Func) (i : BlockId) :
    List.Sublist (blockAllDefs (cseBlockOut f i)) (blockAllDefs f.blocks[i]!) := by
  let b := f.blocks[i]!
  let st := csePrefix f i
  let tab := cseEntryTab f (inEdgeSources f) st.2.1 i
  have hs := cseInstrsOut_defs_sublist (∅ : Subst) b.instrs tab ∅ st.2.2 ∅
    (cseBlockDefs b)
  rw [cseInstrsOut_eq_fold] at hs
  simp only [flatMap_substInstr_defs] at hs
  unfold cseBlockOut
  dsimp only
  apply List.Sublist.append (.refl _)
  simpa [b, st, tab] using hs

omit model in
theorem flatMap_sublist_of_getElem? {α β : Type} (F G : α → List β)
    {xs ys : List α} (hlen : xs.length = ys.length)
    (h : ∀ (i : Nat) (a b : α), xs[i]? = some a → ys[i]? = some b →
      List.Sublist (F a) (G b)) :
    List.Sublist (xs.flatMap F) (ys.flatMap G) := by
  induction xs generalizing ys with
  | nil =>
      have hy : ys = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
      subst ys
      exact .slnil
  | cons a xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons b ys =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          simp only [List.flatMap_cons]
          exact (h 0 a b (by simp) (by simp)).append
            (ih hlen (fun i x y hx hy => h (i + 1) x y (by simpa using hx)
              (by simpa using hy)))

omit model in
theorem cseRaw_allDefs_sublist (f : Func) :
    let raw : Func := { f with blocks := (csePrefix f f.blocks.size).1 }
    List.Sublist raw.allDefs f.allDefs := by
  dsimp only
  unfold Func.allDefs
  apply List.Sublist.append (.refl _)
  apply flatMap_sublist_of_getElem? blockAllDefs blockAllDefs
  · simpa using csePrefix_blocks_size f f.blocks.size
  · intro i b' b hb' hb
    have hi : i < f.blocks.size := (List.getElem?_eq_some_iff.mp hb).1
    have hbraw : (csePrefix f f.blocks.size).1.toList[i]? =
        some (cseBlockOut f i) := by
      simpa using cseFinal_raw_block (f := f) hi
    have heq' : b' = cseBlockOut f i := Option.some.inj (hb'.symm.trans hbraw)
    have hbang : f.blocks[i]! = b := by
      rw [getElem!_eq_getElem hi]
      exact (List.getElem?_eq_some_iff.mp hb).2
    subst b'
    rw [← hbang]
    exact cseBlockOut_defs_sublist f i

omit model in
theorem cseBlockOut_wf {f : Func} {n : Nat} (hwf : f.wfCheck n = true)
    {i : BlockId} {b : Block} (hb : f.blocks[i]? = some b)
    (h : BlockWF f.blocks f.nrets n b) :
    let raw : Func := { f with blocks := (csePrefix f f.blocks.size).1 }
    BlockWF raw.blocks raw.nrets n (cseBlockOut f i) := by
  let raw : Func := { f with blocks := (csePrefix f f.blocks.size).1 }
  have hi : i < f.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  have hbang : f.blocks[i]! = b := by
    rw [getElem!_eq_getElem hi]
    exact (Array.getElem?_eq_some_iff.mp hb).2
  let st := csePrefix f i
  let tab := cseEntryTab f (inEdgeSources f) st.2.1 i
  let r := b.instrs.foldl (fun s ins => cseInstrStep ins s)
    ⟨[], tab, ∅, st.2.2, ∅, cseBlockDefs b⟩
  have hout : cseBlockOut f i = { b with instrs := r.1.reverse } := by
    simp [cseBlockOut, hbang, st, tab, r]
  rw [hout]
  refine ⟨h.1, ?_, ?_⟩
  · intro e he
    obtain ⟨tb, htb, hlen⟩ := h.2.1 e he
    have ht : e.target < f.blocks.size := (Array.getElem?_eq_some_iff.mp htb).1
    have htbang : f.blocks[e.target]! = tb := by
      rw [getElem!_eq_getElem ht]
      exact (Array.getElem?_eq_some_iff.mp htb).2
    refine ⟨cseBlockOut f e.target, ?_, ?_⟩
    · exact cseFinal_raw_block ht
    · simpa [raw, cseBlockOut, htbang] using hlen
  · intro ins hins
    have hc := cseInstrsOut_check (n := n) (∅ : Subst) b.instrs tab ∅ st.2.2 ∅
      (cseBlockDefs b) h.2.2
    rw [cseInstrsOut_eq_fold] at hc
    have hmapped : substInstr (∅ : Subst) ins ∈ r.1.reverse.map (substInstr ∅) :=
      List.mem_map.mpr ⟨ins, hins, rfl⟩
    have houtcheck := hc (substInstr ∅ ins) (by simpa [r] using hmapped)
    cases ins <;> simpa [substInstr] using houtcheck

omit model in
/-- Pass 3 preserves the backend well-formedness check. -/
theorem cse_wf {f : Func} {n : Nat} (hwf : f.wfCheck n = true) :
    (cse f).wfCheck n = true := by
  let raw : Func := { f with blocks := (csePrefix f f.blocks.size).1 }
  have hraw : raw.wfCheck n = true := by
    obtain ⟨hnd, hentry, ⟨eb, heb, hempty⟩, hall⟩ := func_wfCheck_iff.mp hwf
    apply func_wfCheck_iff.mpr
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact hnd.sublist (cseRaw_allDefs_sublist f)
    · simpa [raw] using hentry
    · have hi : f.entry < f.blocks.size := hentry
      refine ⟨cseBlockOut f f.entry, cseFinal_raw_block hi, ?_⟩
      have hbang : f.blocks[f.entry]! = eb := by
        rw [getElem!_eq_getElem hi]
        exact (Array.getElem?_eq_some_iff.mp heb).2
      simpa [cseBlockOut, hbang] using hempty
    · intro b' hb'
      have hbmem : b' ∈ raw.blocks := by simpa using hb'
      obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hbmem
      have hi' : i < f.blocks.size := by simpa [raw] using hi
      let b := f.blocks[i]
      have hb : f.blocks[i]? = some b := Array.getElem?_eq_getElem hi'
      have hbraw := cseFinal_raw_block (f := f) hi'
      have hget : raw.blocks[i]? = some raw.blocks[i] := Array.getElem?_eq_getElem hi
      have heq : raw.blocks[i] = cseBlockOut f i := Option.some.inj (hget.symm.trans hbraw)
      rw [heq]
      exact cseBlockOut_wf hwf hb (hall b (block_mem_of_getElem? hb))
  rw [cse_eq]
  change (substFunc (csePrefix f f.blocks.size).2.2 raw).wfCheck n = true
  exact substFunc_wf hraw

omit model in
theorem dveBlock_allDefs_sublist (f : Func) (i : BlockId) (b : Block) :
    List.Sublist (blockAllDefs (dveBlock f i b)) (blockAllDefs b) := by
  unfold blockAllDefs dveBlock
  apply List.Sublist.append
  · split
    · exact List.Sublist.refl _
    · exact List.filter_sublist
  · exact (List.filter_sublist (l := b.instrs)).flatMap Instr.defs

omit model in
theorem dve_allDefs_sublist (f : Func) : (dve f).allDefs.Sublist f.allDefs := by
  unfold Func.allDefs
  apply List.Sublist.append (.refl _)
  apply flatMap_sublist_of_getElem? blockAllDefs blockAllDefs
  · simp [dve]
  · intro i b' b hb' hb
    have hi : i < f.blocks.size := (List.getElem?_eq_some_iff.mp hb).1
    have hbA : f.blocks[i]? = some b := by simpa using hb
    have hbout := dve_blocks_get f i
    rw [hbA] at hbout
    have hbout' : (dve f).blocks.toList[i]? = some (dveBlock f i b) := by
      simpa using hbout
    have heq : b' = dveBlock f i b := Option.some.inj (hb'.symm.trans hbout')
    subst b'
    exact dveBlock_allDefs_sublist f i b

omit model in
theorem filterZip_length {α β : Type} (p : α → Bool)
    {xs : List α} {ys : List β} (hlen : xs.length = ys.length) :
    ((xs.zip ys).filter fun xy => p xy.1).length = (xs.filter p).length := by
  induction xs generalizing ys with
  | nil =>
      have hy : ys = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
      subst ys
      rfl
  | cons x xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          simp only [List.zip_cons_cons, List.filter_cons]
          split <;> simp [ih hlen]

theorem dveBlock_wf {f : Func} {n : Nat} (hwf : f.wfCheck n = true)
    {i : BlockId} {b : Block} (hb : f.blocks[i]? = some b)
    (h : BlockWF f.blocks f.nrets n b) :
    BlockWF (dve f).blocks (dve f).nrets n (dveBlock f i b) := by
  refine ⟨?_, ?_, ?_⟩
  · rcases ht : b.term with e | ⟨c, et, ef⟩ | xs | ⟨yop, as⟩ <;>
      simpa [dveBlock, mapEdges, dve, ht] using h.1
  · intro e he
    obtain ⟨e0, he0, heq⟩ := mapEdges_edges b.term (by simpa [dveBlock] using he)
    have heqD : e = dveEdge f e0 := by
      rw [← heq]
      rfl
    obtain ⟨tb, htb, hlen⟩ := h.2.1 e0 he0
    rw [heqD]
    refine ⟨dveBlock f e0.target tb, ?_, ?_⟩
    · change (dve f).blocks[e0.target]? = some (dveBlock f e0.target tb)
      rw [dve_blocks_get, htb]
      rfl
    · change (dveEdge f e0).args.length = (dveBlock f e0.target tb).params.length
      rw [dveEdge_args_eq_zip htb hlen, dveBlock_params hwf htb,
        List.length_map, filterZip_length (liveSet f).contains hlen.symm]
  · intro ins hins
    have hins' : ins ∈ b.instrs := by
      change ins ∈ b.instrs.filter (dveKeepInstr (liveSet f)) at hins
      exact List.mem_of_mem_filter hins
    exact h.2.2 ins hins'

/-- Pass 4 preserves the backend well-formedness check. -/
theorem dve_wf {f : Func} {n : Nat} (hwf : f.wfCheck n = true) :
    (dve f).wfCheck n = true := by
  obtain ⟨hnd, hentry, ⟨eb, heb, hempty⟩, hall⟩ := func_wfCheck_iff.mp hwf
  apply func_wfCheck_iff.mpr
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hnd.sublist (dve_allDefs_sublist f)
  · simpa [dve_entry, dve_size] using hentry
  · have heb' := dve_blocks_get f f.entry
    rw [heb] at heb'
    refine ⟨dveBlock f f.entry eb, heb', ?_⟩
    rw [dveBlock_params hwf heb]
    simp [hempty]
  · intro b' hb'
    have hbmem : b' ∈ (dve f).blocks := by simpa using hb'
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hbmem
    have hi' : i < f.blocks.size := by simpa [dve_size] using hi
    let b := f.blocks[i]
    have hb : f.blocks[i]? = some b := Array.getElem?_eq_getElem hi'
    have hbout := dve_blocks_get f i
    rw [hb] at hbout
    have hget : (dve f).blocks[i]? = some (dve f).blocks[i] :=
      Array.getElem?_eq_getElem hi
    have heq : (dve f).blocks[i] = dveBlock f i b :=
      Option.some.inj (hget.symm.trans (by simpa using hbout))
    rw [heq]
    exact dveBlock_wf hwf hb (hall b (block_mem_of_getElem? hb))

/-- One complete local pipeline round preserves `Func.wfCheck`. -/
theorem runOnce_wf {f : Func} {n : Nat} (hwf : f.wfCheck n = true) :
    (runOnce f).wfCheck n = true := by
  exact dve_wf (cse_wf (constFold_wf (elimTrivialParams_wf hwf)))

end Passes

/-! ### Dominance preservation

Not needed for top-level soundness — `optimizeProg`'s gate re-checks
`wfCheck && domCheck` on the output and falls back otherwise
(`optimizeProg_sound_of_fallback`, proved) — but needed to *compose* the four
pass lemmas inside `runOnce`, and the reason the gate essentially never fires in
practice. Each pass only ever removes definitions or reroutes a use to a value
that already dominates it, so `liveIn(entry)` can only shrink; the proofs are
computations on `ToAsm.liveInSets` of the rewritten function, in the same style
as `ToAsm.liveIn_of_uses`/`liveIn_of_succ`. -/

omit model in
/-- One removal uses a custom pre-fixed point: the substituted old live-in
sets, plus `v` at the selected block.  `_edge` supplies `v` as an old use on
non-self predecessors and carries the added availability around self loops;
`block_def_index_unique` handles the removed definition.  The public theorem
below iterates this fact while preserving `allDefs.Nodup`. -/
private theorem elimTrivialParam_one_dom {f : Func} (hnd : f.allDefs.Nodup)
    (hdom : ToAsm.Func.domCheck f = true) {bi i p v : Nat}
    (hfind : Passes.findTrivialParam f = some (bi, i, p, v)) :
    ToAsm.Func.domCheck (Passes.substFunc ((∅ : Passes.Subst).insert p v)
      (Passes.removeParam f bi i)) = true := by
  let σ : ValId → ValId := Passes.substV ((∅ : Passes.Subst).insert p v)
  let g := Passes.substFunc ((∅ : Passes.Subst).insert p v)
    (Passes.removeParam f bi i)
  obtain ⟨hbi, hbientry, hi, hpget, -, -, hsingle, -⟩ :=
    Passes.findTrivialParam_inv hfind
  have hbang : f.blocks[bi]! = f.blocks[bi] := by
    rw [Passes.getElem!_eq_getElem hbi]
  have hi' : i < f.blocks[bi].params.length := by simpa [hbang] using hi
  have hpEq : f.blocks[bi].params[i] = p := by
    have hpget' := hpget
    rw [hbang] at hpget'
    simpa [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi'] using hpget'
  have hpgetQ : f.blocks[bi].params[i]? = some p := by
    rw [List.getElem?_eq_getElem hi', hpEq]
  have hbsel : f.blocks[bi]? = some f.blocks[bi] :=
    Array.getElem?_eq_getElem hbi
  have hpmem : p ∈ ToAsm.blockDefs f.blocks[bi] := by
    rw [ToAsm.mem_blockDefs]
    left
    rw [← hpEq]
    exact List.getElem_mem hi'
  have hpnot : p ∉ f.params := by
    intro hp
    have hpflat : p ∈ f.blocks.toList.flatMap blockAllDefs := by
      apply List.mem_flatMap.mpr
      refine ⟨f.blocks[bi], ?_, ?_⟩
      · exact List.mem_iff_getElem.mpr ⟨bi, by simpa using hbi, rfl⟩
      · apply List.mem_append_left
        rw [← hpEq]
        exact List.getElem_mem hi'
    exact (List.nodup_append.mp hnd).2.2 p hp p hpflat rfl
  have hσparam : ∀ x ∈ f.params, σ x = x := by
    intro x hx
    have hxp : x ≠ p := fun h => hpnot (h ▸ hx)
    simp [σ, Passes.substV_single, hxp]
  have hvp : v ≠ p := by
    intro hvp
    subst v
    have hm : p ∈ (((Passes.inEdgeArgs f)[bi]!.filterMap (·[i]?)).filter
        (· != p)).eraseDups := by simpa [hsingle]
    have hm' := List.mem_filter.mp (List.mem_eraseDups.mp hm)
    simpa using hm'.2
  obtain ⟨li, hli⟩ := ToAsm.liveInSets_isSome f
  obtain ⟨li', hli'⟩ := ToAsm.liveInSets_isSome g
  let ub : Array (List ValId) := Array.ofFn fun j : Fin f.blocks.size =>
    ToAsm.unionS ((li[j.1]?.getD []).map σ) (if j.1 = bi then [v] else [])
  have mem_ub (j : Nat) (x : ValId) :
      x ∈ ub[j]?.getD [] ↔ j < f.blocks.size ∧
        ((∃ y ∈ li[j]?.getD [], σ y = x) ∨ (j = bi ∧ x = v)) := by
    by_cases hj : j < f.blocks.size
    · rw [Array.getElem?_eq_getElem (by simpa [ub] using hj)]
      simp only [Option.getD_some, ub, Array.getElem_ofFn, ToAsm.mem_unionS,
        List.mem_map]
      constructor
      · intro hx
        refine ⟨hj, ?_⟩
        by_cases hji : j = bi
        · simpa [hji] using hx
        · simpa [hji] using hx
      · rintro ⟨-, hx⟩
        by_cases hji : j = bi
        · simpa [hji] using hx
        · simpa [hji] using hx
    · rw [Array.getElem?_eq_none_iff.mpr (by simpa [ub] using Nat.not_lt.mp hj)]
      simp [hj]
  have hsize : g.blocks.size = f.blocks.size := by simp [g, Passes.substFunc,
    Passes.removeParam]
  have hub : ToAsm.Sub (ToAsm.liveStep g ub) ub := by
    intro j x hx
    rcases hb' : g.blocks[j]? with _ | b'
    · rw [ToAsm.liveStep_get_none hb'] at hx
      simp at hx
    · have hjg : j < g.blocks.size := (Array.getElem?_eq_some_iff.mp hb').1
      have hj : j < f.blocks.size := by simpa [hsize] using hjg
      let b := f.blocks[j]
      have hb : f.blocks[j]? = some b := Array.getElem?_eq_getElem hj
      have hbraw := Passes.elimStep_blocks_get (bi := bi) (i := i) (p := p) (v := v) hb
      rw [hb'] at hbraw
      have hb'eq : b' = Passes.substBlock ((∅ : Passes.Subst).insert p v)
          (Passes.removedBlock bi i j b) := Option.some.inj hbraw
      subst b'
      rw [ToAsm.liveStep_get_eq hb', ToAsm.mem_diffS] at hx
      rw [mem_ub]
      refine ⟨hj, ?_⟩
      have resolveDef {y : ValId} (hydef : y ∈ ToAsm.blockDefs b)
          (hσyx : σ y = x) :
          (∃ z ∈ li[j]?.getD [], σ z = x) ∨ (j = bi ∧ x = v) := by
        by_cases hyp : y = p
        · subst y
          have hji := Passes.block_def_index_unique hnd hb hbsel hydef hpmem
          exact Or.inr ⟨hji, by simpa [σ, Passes.substV_single] using hσyx.symm⟩
        · have hyraw : y ∈ ToAsm.blockDefs (Passes.removedBlock bi i j b) := by
            by_cases hji : j = bi
            · subst j
              have hbeq : b = f.blocks[bi] := Option.some.inj (hb.symm.trans hbsel)
              subst b
              apply Passes.mem_removedBlock_defs (x := y) (p := p)
              · exact hpgetQ
              · exact hydef
              · exact hyp
            · rw [ToAsm.mem_blockDefs] at hydef ⊢
              simpa [Passes.removedBlock, hji] using hydef
          have hyout := Passes.mem_substBlock_defs
            (σ := ((∅ : Passes.Subst).insert p v)) hyraw
          have hσy : σ y = y := by simp [σ, Passes.substV_single, hyp]
          exact absurd (hσy ▸ hyout) (hσyx ▸ hx.2)
      rcases ToAsm.mem_unionS.mp hx.1 with hu | hl
      · obtain ⟨y, hyraw, hσyx⟩ := Passes.substBlock_use hu
        have hyuse := Passes.removedBlock_use hyraw
        by_cases hydef : y ∈ ToAsm.blockDefs b
        · exact resolveDef hydef hσyx
        · exact Or.inl ⟨y, ToAsm.liveIn_of_uses hli hb hyuse hydef, hσyx⟩
      · rcases ToAsm.mem_lout.mp hl with ⟨e, he, hxe⟩ | hnil
        · have het : ∃ e0 ∈ b.term.edges, e0.target = e.target := by
            obtain ⟨er, her, hert⟩ := Passes.substTerm_edge
              (t := (Passes.removedBlock bi i j b).term) he
            obtain ⟨e0, he0, he0t⟩ := Passes.removedBlock_edge her
            exact ⟨e0, he0, he0t.trans hert⟩
          obtain ⟨e0, he0, he0t⟩ := het
          rw [mem_ub] at hxe
          rcases hxe.2 with ⟨y, hy, hσyx⟩ | ⟨hetbi, hxv⟩
          · by_cases hydef : y ∈ ToAsm.blockDefs b
            · exact resolveDef hydef hσyx
            · exact Or.inl ⟨y, ToAsm.liveIn_of_succ hli hb he0
                (by rw [he0t]; exact hy) hydef, hσyx⟩
          · by_cases hji : j = bi
            · exact Or.inr ⟨hji, hxv⟩
            · have he0bi : e0.target = bi := he0t.trans hetbi
              obtain ⟨a, ha, hapv, hapself⟩ :=
                Passes.findTrivialParam_edge hfind hb he0 he0bi
              have hav : a = v := by
                rcases hapv with rfl | hav
                · exact absurd (hapself rfl) hji
                · exact hav
              have hvuse : v ∈ ToAsm.blockUses b := by
                rw [ToAsm.mem_blockUses]
                right
                have : v ∈ e0.args := by
                  subst a
                  exact List.mem_iff_getElem?.mpr ⟨i, ha⟩
                cases ht : b.term with
                | jump ej =>
                    simp only [ht, Term.edges, List.mem_singleton] at he0
                    subst e0
                    simpa [ht, Term.uses] using this
                | branch c et ef =>
                    simp only [ht, Term.edges, List.mem_cons] at he0
                    rcases he0 with rfl | he0
                    · simp [Term.uses, this]
                    · have : e0 = ef := by simpa using he0
                      subst e0
                      simp [Term.uses, this]
                | ret xs => simp [ht, Term.edges] at he0
                | halt yop as => simp [ht, Term.edges] at he0
              by_cases hvdef : v ∈ ToAsm.blockDefs b
              · have hvraw : v ∈ ToAsm.blockDefs
                    (Passes.removedBlock bi i j b) := by
                  rw [ToAsm.mem_blockDefs] at hvdef ⊢
                  simpa [Passes.removedBlock, hji] using hvdef
                have hvout := Passes.mem_substBlock_defs
                  (σ := ((∅ : Passes.Subst).insert p v)) hvraw
                exact absurd (hxv ▸ hvout) hx.2
              · exact Or.inl ⟨v, ToAsm.liveIn_of_uses hli hb hvuse hvdef,
                  by simpa [σ, Passes.substV_single, hvp] using hxv.symm⟩
        · simp at hnil
  have hsub : ToAsm.Sub li' ub := ToAsm.liveInSets_least hli' hub
  unfold ToAsm.Func.domCheck
  rw [hli']
  simp only [decide_eq_true_eq]
  rw [List.eq_nil_iff_forall_not_mem]
  intro x hx
  rw [ToAsm.mem_diffS] at hx
  have hxub := hsub _ _ hx.1
  rw [mem_ub] at hxub
  rcases hxub.2 with ⟨y, hy, hσyx⟩ | ⟨hentry, -⟩
  · have hyp := ToAsm.domCheck_entry hli hdom hy
    have hyx : y = x := (hσparam y hyp).symm.trans hσyx
    exact hx.2 (by simpa [g, Passes.substFunc, Passes.removeParam] using hyx ▸ hyp)
  · exact hbientry hentry.symm

omit model in
theorem elimTrivialParams_dom {f : Func} (hwf : f.wfCheck n = true)
    (hdom : ToAsm.Func.domCheck f = true) :
    ToAsm.Func.domCheck (Passes.elimTrivialParams f) = true := by
  have hnd : f.allDefs.Nodup := by
    unfold Func.wfCheck at hwf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hwf
    exact hwf.1.1.1
  have loopInv : ∀ (xs : List Nat) (r : Passes.ElimTrivialLoopState),
      r.2.allDefs.Nodup → ToAsm.Func.domCheck r.2 = true →
      r.1.getD r.2 = r.2 →
      let out := loopWith Passes.elimTrivialStep xs r
      out.2.allDefs.Nodup ∧ ToAsm.Func.domCheck out.2 = true ∧
        out.1.getD out.2 = out.2 := by
    intro xs
    induction xs with
    | nil =>
        intro r hrnd hrdom hr
        exact ⟨hrnd, hrdom, hr⟩
    | cons k ks ih =>
        intro r hrnd hrdom hr
        rw [loopWith_cons]
        unfold Passes.elimTrivialStep
        cases hfind : Passes.findTrivialParam r.2 with
        | none =>
            exact ⟨hrnd, hrdom, by simp⟩
        | some q =>
            obtain ⟨bi, i, p, v⟩ := q
            apply ih
            · rw [Passes.substFunc_allDefs]
              exact hrnd.sublist (Passes.removeParam_allDefs_sublist r.2 bi i)
            · exact elimTrivialParam_one_dom hrnd hrdom hfind
            · rfl
  rw [Passes.elimTrivialParams_eq_loop]
  let r := loopWith Passes.elimTrivialStep
    (List.range' 0 (Passes.elimTrivialFuel f) 1) ⟨none, f⟩
  have hr := loopInv (List.range' 0 (Passes.elimTrivialFuel f) 1)
    (⟨none, f⟩ : Passes.ElimTrivialLoopState) hnd hdom rfl
  change r.2.allDefs.Nodup ∧ ToAsm.Func.domCheck r.2 = true ∧
    r.1.getD r.2 = r.2 at hr
  rw [hr.2.2]
  exact hr.2.1

/-- **Pass 1 (trivial block-parameter elimination) soundness.**  The loop
threads the one-removal lockstep theorem together with single-assignment and
dominance preservation. -/
theorem elimTrivialParams_sound {P : Prog} {f : Func} {args : List U256}
    {st : EvmState} {res : FRes} {eb eb' : Block}
    (hwf : f.wfCheck P.funcs.size = true)
    (hdom : ToAsm.Func.domCheck f = true)
    (heb : f.blocks[f.entry]? = some eb)
    (heb' : (Passes.elimTrivialParams f).blocks[f.entry]? = some eb')
    (hexec : Exec (model := model) P f (Regs.empty.setMany f.params args) st
      ⟨eb.instrs, eb.term⟩ res) :
    Exec (model := model) P (Passes.elimTrivialParams f)
      (Regs.empty.setMany f.params args) st ⟨eb'.instrs, eb'.term⟩ res := by
  have hnd : f.allDefs.Nodup := wfCheck_defs_nodup hwf
  have loopSound : ∀ (xs : List Nat) (r : Passes.ElimTrivialLoopState),
      r.2.params = f.params → r.2.entry = f.entry →
      r.2.allDefs.Nodup → ToAsm.Func.domCheck r.2 = true →
      r.1.getD r.2 = r.2 →
      ∀ {b : Block}, r.2.blocks[f.entry]? = some b →
        Exec (model := model) P r.2 (Regs.empty.setMany f.params args) st
          ⟨b.instrs, b.term⟩ res →
        let out := loopWith Passes.elimTrivialStep xs r
        ∃ b', out.2.blocks[f.entry]? = some b' ∧
          Exec (model := model) P out.2 (Regs.empty.setMany f.params args) st
            ⟨b'.instrs, b'.term⟩ res ∧
          out.1.getD out.2 = out.2 := by
    intro xs
    induction xs with
    | nil =>
        intro r hparams hentry hrnd hrdom hr b hb hrun
        exact ⟨b, hb, hrun, hr⟩
    | cons n ns ih =>
        intro r hparams hentry hrnd hrdom hr b hb hrun
        rw [loopWith_cons]
        unfold Passes.elimTrivialStep
        cases hfind : Passes.findTrivialParam r.2 with
        | none =>
            exact ⟨b, hb, hrun, by simp⟩
        | some q =>
            obtain ⟨bi, k, p, v⟩ := q
            let g := Passes.substFunc ((∅ : Passes.Subst).insert p v)
              (Passes.removeParam r.2 bi k)
            have hentryCur : r.2.entry = f.entry := hentry
            have hbcur : r.2.blocks[r.2.entry]? = some b := by simpa [hentryCur] using hb
            have hrunCur : Exec (model := model) P r.2
                (Regs.empty.setMany r.2.params args) st ⟨b.instrs, b.term⟩ res := by
              simpa [hparams] using hrun
            have hentrylt : r.2.entry < g.blocks.size := by
              simpa [g, Passes.substFunc, Passes.removeParam] using
                (Array.getElem?_eq_some_iff.mp hbcur).1
            let b' := g.blocks[r.2.entry]
            have hb' : g.blocks[r.2.entry]? = some b' := by
              exact Array.getElem?_eq_getElem hentrylt
            have hrun' := elimTrivialParam_one_sound hrnd hrdom hfind
              hbcur hb' hrunCur
            apply ih (⟨none, g⟩ : Passes.ElimTrivialLoopState)
            · simpa [g, Passes.substFunc, Passes.removeParam] using hparams
            · simpa [g, Passes.substFunc, Passes.removeParam] using hentry
            · change g.allDefs.Nodup
              simp only [g, Passes.substFunc_allDefs]
              exact hrnd.sublist (Passes.removeParam_allDefs_sublist r.2 bi k)
            · exact elimTrivialParam_one_dom hrnd hrdom hfind
            · rfl
            · simpa [hentry] using hb'
            · simpa [hparams] using hrun'
  rw [Passes.elimTrivialParams_eq_loop] at heb' ⊢
  let r := loopWith Passes.elimTrivialStep
    (List.range' 0 (Passes.elimTrivialFuel f) 1)
    (⟨none, f⟩ : Passes.ElimTrivialLoopState)
  have hs := loopSound (List.range' 0 (Passes.elimTrivialFuel f) 1)
    (⟨none, f⟩ : Passes.ElimTrivialLoopState) rfl rfl hnd hdom rfl heb hexec
  change ∃ b', r.2.blocks[f.entry]? = some b' ∧
    Exec (model := model) P r.2 (Regs.empty.setMany f.params args) st
      ⟨b'.instrs, b'.term⟩ res ∧ r.1.getD r.2 = r.2 at hs
  obtain ⟨bout, hbout, hrunout, hr⟩ := hs
  rw [hr] at heb' ⊢
  have heq : eb' = bout := Option.some.inj (heb'.symm.trans hbout)
  subst eb'
  exact hrunout

omit model in
/-- **Dominance preservation for pass 2** — proved. `ToAsm.domCheck_of_shrinking`
reduces it to `Passes.CFRel` block by block, and `Passes.constFold_spec`
(the pass's structural specification, obtained from the `forIn`-to-`foldl`
bridge) supplies exactly that. -/
theorem constFold_dom {f : Func} (hdom : ToAsm.Func.domCheck f = true) :
    ToAsm.Func.domCheck (Passes.constFold f) = true := by
  refine ToAsm.domCheck_of_shrinking hdom rfl rfl ?_
  intro i b' hb'
  obtain ⟨b, hb, hrel⟩ := Passes.constFold_spec f i b' hb'
  exact ⟨b, hb, hrel.1, hrel.2.1, hrel.2.2⟩

omit model in
theorem cse_dom {f : Func} (hwf : f.wfCheck n = true)
    (hdom : ToAsm.Func.domCheck f = true) :
    ToAsm.Func.domCheck (Passes.cse f) = true := by
  let τ := (Passes.csePrefix f f.blocks.size).2.2
  have hnd : f.allDefs.Nodup := by
    have hwf' := hwf
    unfold Func.wfCheck at hwf'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hwf'
    exact hwf'.1.1.1
  have hfinalInv := (Passes.csePrefixInv hnd f.blocks.size (Nat.le_refl _)).1
  have hparam (p : ValId) (hp : p ∈ f.params) : Passes.substV τ p = p := by
    have hpnone : τ[p]? = none := by
      by_contra hn
      obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hn
      have hpseen := (hfinalInv.2.2.2.1 hq).1
      unfold Passes.cseSeen at hpseen
      have htake : f.blocks.toList.take f.blocks.size = f.blocks.toList := by simp
      rw [htake] at hpseen
      simp only [List.mem_flatMap] at hpseen
      obtain ⟨b, hb, ins, hins, hpdef⟩ := hpseen
      exact funcParam_not_instr_def hnd hb hins hp hpdef
    simp [Passes.substV, Std.HashMap.getD_eq_getD_getElem?, hpnone]
  apply ToAsm.domCheck_of_substitution (f := f) (g := Passes.cse f)
    (Passes.substV τ) (Passes.cseAvail f)
    hdom rfl rfl hparam (Passes.cseAvail_entry f)
  intro i b' hb'
  have hi : i < f.blocks.size := by
    have hi' : i < (Passes.cse f).blocks.size :=
      (Array.getElem?_eq_some_iff.mp hb').1
    simpa using hi'
  let b := f.blocks[i]
  have hb : f.blocks[i]? = some b := Array.getElem?_eq_getElem hi
  have hbout := Passes.cse_block_get hb
  rw [hb'] at hbout
  have heq : b' = Passes.substBlock τ (Passes.cseBlockOut f i) := by
    simpa [τ] using Option.some.inj hbout
  subst b'
  have hspec := Passes.cseBlock_spec hnd hb
  refine ⟨b, hb, hspec.1, hspec.2.1, hspec.2.2.1, ?_⟩
  intro e he x hx
  obtain ⟨e0, he0, htarget⟩ := hspec.2.2.1 e he
  have hs := Passes.cseAvail_succ hnd hwf hb he0 (x := x) (by
    rw [htarget]
    exact hx)
  simpa [τ] using hs

private def dveDomCounterexample : Func :=
  { params := [], nrets := 0, entry := 0
    blocks := #[
      ⟨[], [.const 0 0], .jump ⟨1, [0]⟩⟩,
      ⟨[], [], .ret []⟩] }

private example :
    ToAsm.Func.domCheck dveDomCounterexample = true ∧
      ToAsm.Func.domCheck (Passes.dve dveDomCounterexample) = false := by
  native_decide

omit model in
/-- `wfCheck` is required here because DVE filters edge arguments positionally;
without matching edge/target arities the documented counterexample applies. -/
theorem dve_dom {f : Func} (hwf : f.wfCheck n = true)
    (hdom : ToAsm.Func.domCheck f = true) :
    ToAsm.Func.domCheck (Passes.dve f) = true := by
  obtain ⟨li, hli⟩ := ToAsm.liveInSets_isSome f
  obtain ⟨li', hli'⟩ := ToAsm.liveInSets_isSome (Passes.dve f)
  let ub := li.map (fun xs => xs.filter (Passes.liveSet f).contains)
  have mem_ub (i : Nat) (x : ValId) :
      x ∈ ub[i]?.getD [] ↔ x ∈ li[i]?.getD [] ∧ x ∈ Passes.liveSet f := by
    by_cases hi : i < li.size
    · have hiub : i < ub.size := by simpa [ub] using hi
      rw [Array.getElem?_eq_getElem hiub, Array.getElem?_eq_getElem hi]
      simp only [Option.getD_some, ub, Array.getElem_map, List.mem_filter]
      exact and_congr_right (fun _ => Std.HashSet.contains_iff_mem)
    · have hge : li.size ≤ i := Nat.not_lt.mp hi
      have hgeub : ub.size ≤ i := by simpa [ub] using hge
      rw [Array.getElem?_eq_none_iff.mpr hge, Array.getElem?_eq_none_iff.mpr hgeub]
      simp
  have hub : ToAsm.Sub (ToAsm.liveStep (Passes.dve f) ub) ub := by
    intro i x hx
    rcases hb' : (Passes.dve f).blocks[i]? with _ | b'
    · rw [ToAsm.liveStep_get_none hb'] at hx
      simp at hx
    · rw [ToAsm.liveStep_get_eq hb', ToAsm.mem_diffS] at hx
      rw [Passes.dve_blocks_get] at hb'
      rcases hb : f.blocks[i]? with _ | b
      · simp [hb] at hb'
      · have hb'eq : b' = Passes.dveBlock f i b := by
          symm
          simpa [hb] using hb'
        subst b'
        rw [mem_ub]
        have finish (hxLive : x ∈ Passes.liveSet f) (hxOld : x ∈ li[i]?.getD []) :
            x ∈ li[i]?.getD [] ∧ x ∈ Passes.liveSet f := ⟨hxOld, hxLive⟩
        rcases ToAsm.mem_unionS.mp hx.1 with hu | hl
        · have hxLive := Passes.dveBlock_uses_live hwf hb hu
          have huOld := Passes.dveBlock_uses_sub hu
          have hnot : x ∉ ToAsm.blockDefs b := by
            intro hd
            have hd' := Passes.dveBlock_defs_of_live (i := i)
              (Std.HashSet.mem_iff_contains.mp hxLive) hd
            exact hx.2 hd'
          exact finish hxLive (ToAsm.liveIn_of_uses hli hb huOld hnot)
        · rcases ToAsm.mem_lout.mp hl with ⟨e, he, hxe⟩ | hnil
          · rw [mem_ub] at hxe
            obtain ⟨e0, he0, htarget⟩ := Passes.dveBlock_edge_target he
            have hnot : x ∉ ToAsm.blockDefs b := by
              intro hd
              have hd' := Passes.dveBlock_defs_of_live (i := i)
                (Std.HashSet.mem_iff_contains.mp hxe.2) hd
              exact hx.2 hd'
            exact finish hxe.2 (ToAsm.liveIn_of_succ hli hb he0
              (by rw [htarget]; exact hxe.1) hnot)
          · simp at hnil
  have hsub : ToAsm.Sub li' ub := ToAsm.liveInSets_least hli' hub
  unfold ToAsm.Func.domCheck
  rw [hli']
  simp only [decide_eq_true_eq]
  rw [List.eq_nil_iff_forall_not_mem]
  intro x hx
  rw [ToAsm.mem_diffS] at hx
  have hxub := hsub _ _ hx.1
  rw [mem_ub] at hxub
  exact hx.2 (ToAsm.domCheck_entry hli hdom hxub.1)

omit model in
/-- Dominance preservation for one pipeline round, including the intermediate
`wfCheck` facts supplied by the four preservation lemmas above. -/
theorem runOnce_dom {f : Func} {n : Nat} (hwf : f.wfCheck n = true)
    (hdom : ToAsm.Func.domCheck f = true) :
    ToAsm.Func.domCheck (Passes.runOnce f) = true := by
  have hwf1 := Passes.elimTrivialParams_wf hwf
  have hwf3 := Passes.constFold_wf hwf1
  have hwf4 := Passes.cse_wf hwf3
  unfold Passes.runOnce
  exact dve_dom hwf4 (cse_dom hwf3 (constFold_dom (elimTrivialParams_dom hwf hdom)))

omit model in
theorem Passes.elimTrivialParams_params_entry (f : Func) :
    (elimTrivialParams f).params = f.params ∧
      (elimTrivialParams f).entry = f.entry := by
  have loopInv : ∀ (xs : List Nat) (r : ElimTrivialLoopState),
      r.2.params = f.params → r.2.entry = f.entry →
      r.1.getD r.2 = r.2 →
      let out := loopWith elimTrivialStep xs r
      out.2.params = f.params ∧ out.2.entry = f.entry ∧
        out.1.getD out.2 = out.2 := by
    intro xs
    induction xs with
    | nil =>
        intro r hp he hr
        exact ⟨hp, he, hr⟩
    | cons k ks ih =>
        intro r hp he hr
        rw [loopWith_cons]
        unfold elimTrivialStep
        cases hfind : findTrivialParam r.2 with
        | none => exact ⟨hp, he, by simp⟩
        | some q =>
            obtain ⟨bi, i, p, v⟩ := q
            apply ih
            · simpa [substFunc, removeParam] using hp
            · simpa [substFunc, removeParam] using he
            · rfl
  rw [elimTrivialParams_eq_loop]
  let r := loopWith elimTrivialStep
    (List.range' 0 (elimTrivialFuel f) 1) (⟨none, f⟩ : ElimTrivialLoopState)
  have hr := loopInv (List.range' 0 (elimTrivialFuel f) 1)
    (⟨none, f⟩ : ElimTrivialLoopState) rfl rfl rfl
  change r.2.params = f.params ∧ r.2.entry = f.entry ∧
    r.1.getD r.2 = r.2 at hr
  rw [hr.2.2]
  exact ⟨hr.1, hr.2.1⟩

/-- The four local simulations composed in the order used by `runOnce`. -/
theorem runOnce_sound {P : Prog} {f : Func} {args : List U256}
    {st : EvmState} {res : FRes} {eb eb' : Block}
    (hwf : f.wfCheck P.funcs.size = true)
    (hdom : ToAsm.Func.domCheck f = true)
    (heb : f.blocks[f.entry]? = some eb)
    (heb' : (Passes.runOnce f).blocks[(Passes.runOnce f).entry]? = some eb')
    (hexec : Exec (model := model) P f (Regs.empty.setMany f.params args) st
      ⟨eb.instrs, eb.term⟩ res) :
    Exec (model := model) P (Passes.runOnce f)
      (Regs.empty.setMany (Passes.runOnce f).params args) st
      ⟨eb'.instrs, eb'.term⟩ res := by
  let f1 := Passes.elimTrivialParams f
  let f2 := Passes.constFold f1
  let f3 := Passes.cse f2
  have hwf1 : f1.wfCheck P.funcs.size = true := Passes.elimTrivialParams_wf hwf
  have hwf2 : f2.wfCheck P.funcs.size = true := Passes.constFold_wf hwf1
  have hwf3 : f3.wfCheck P.funcs.size = true := Passes.cse_wf hwf2
  have hdom1 : ToAsm.Func.domCheck f1 = true := elimTrivialParams_dom hwf hdom
  have hdom2 : ToAsm.Func.domCheck f2 = true := constFold_dom hdom1
  have hdom3 : ToAsm.Func.domCheck f3 = true := cse_dom hwf2 hdom2
  obtain ⟨-, -, ⟨eb1, heb1, -⟩, -⟩ := Passes.func_wfCheck_iff.mp hwf1
  obtain ⟨-, -, ⟨eb2, heb2, -⟩, -⟩ := Passes.func_wfCheck_iff.mp hwf2
  obtain ⟨-, -, ⟨eb3, heb3, -⟩, -⟩ := Passes.func_wfCheck_iff.mp hwf3
  have hfields1 := Passes.elimTrivialParams_params_entry f
  have hparams1 : f1.params = f.params := by simpa [f1] using hfields1.1
  have hentry1 : f1.entry = f.entry := by simpa [f1] using hfields1.2
  have hparams2 : f2.params = f1.params := by rfl
  have hentry2 : f2.entry = f1.entry := by rfl
  have hparams3 : f3.params = f2.params := by rfl
  have hentry3 : f3.entry = f2.entry := by rfl
  have heb1' : (Passes.elimTrivialParams f).blocks[f.entry]? = some eb1 := by
    simpa [f1, hentry1] using heb1
  have heb2' : (Passes.constFold f1).blocks[f1.entry]? = some eb2 := by
    simpa [f2, hentry2] using heb2
  have heb3' : (Passes.cse f2).blocks[f2.entry]? = some eb3 := by
    simpa [f3, hentry3] using heb3
  have h1 := elimTrivialParams_sound hwf hdom heb heb1' hexec
  have h1' : Exec (model := model) P f1 (Regs.empty.setMany f1.params args) st
      ⟨eb1.instrs, eb1.term⟩ res := by simpa [f1, hparams1] using h1
  have h2 := constFold_sound hwf1 heb1 heb2' h1'
  have h2' : Exec (model := model) P f2 (Regs.empty.setMany f2.params args) st
      ⟨eb2.instrs, eb2.term⟩ res := by simpa [f2, hparams2] using h2
  have h3 := cse_sound hwf2 hdom2 heb2 heb3' h2'
  have h3' : Exec (model := model) P f3 (Regs.empty.setMany f3.params args) st
      ⟨eb3.instrs, eb3.term⟩ res := by simpa [f3, hparams3] using h3
  have heb4 : (Passes.dve f3).blocks[f3.entry]? = some eb' := by
    simpa [Passes.runOnce, f1, f2, f3, Passes.dve_entry] using heb'
  have h4 := dve_sound hwf3 heb3 heb4 h3'
  simpa [Passes.runOnce, f1, f2, f3, Passes.dve_params] using h4

omit model in
theorem Passes.runOnce_params (f : Func) : (runOnce f).params = f.params := by
  unfold runOnce
  rw [dve_params]
  change (cse (constFold (elimTrivialParams f))).params = f.params
  change (constFold (elimTrivialParams f)).params = f.params
  change (elimTrivialParams f).params = f.params
  exact (elimTrivialParams_params_entry f).1

omit model in
theorem Passes.runOnce_nrets (f : Func) : (runOnce f).nrets = f.nrets := by
  have loopInv : ∀ (xs : List Nat) (r : ElimTrivialLoopState),
      r.2.nrets = f.nrets → r.1.getD r.2 = r.2 →
      let out := loopWith elimTrivialStep xs r
      out.2.nrets = f.nrets ∧ out.1.getD out.2 = out.2 := by
    intro xs
    induction xs with
    | nil => intro r hn hr; exact ⟨hn, hr⟩
    | cons k ks ih =>
        intro r hn hr
        rw [loopWith_cons]
        unfold elimTrivialStep
        cases hfind : findTrivialParam r.2 with
        | none => exact ⟨hn, by simp⟩
        | some q =>
            obtain ⟨bi, i, p, v⟩ := q
            apply ih
            · simpa [substFunc, removeParam] using hn
            · rfl
  have he : (elimTrivialParams f).nrets = f.nrets := by
    rw [elimTrivialParams_eq_loop]
    let r := loopWith elimTrivialStep
      (List.range' 0 (elimTrivialFuel f) 1) (⟨none, f⟩ : ElimTrivialLoopState)
    have hr := loopInv (List.range' 0 (elimTrivialFuel f) 1)
      (⟨none, f⟩ : ElimTrivialLoopState) rfl rfl
    change r.2.nrets = f.nrets ∧ r.1.getD r.2 = r.2 at hr
    rw [hr.2]
    exact hr.1
  unfold runOnce
  change (elimTrivialParams f).nrets = f.nrets
  exact he

/-- Map one local pipeline round over every function without changing function
indices. -/
def Passes.runOnceProg (P : Prog) : Prog :=
  { main := runOnce P.main, funcs := P.funcs.map runOnce }

omit model in
theorem Passes.runOnceProg_lookup {P : Prog} {fid : FuncId} {g : Func}
    (h : P.funcs[fid]? = some g) :
    (runOnceProg P).funcs[fid]? = some (runOnce g) := by
  simp [runOnceProg, h]

theorem Passes.runOnceProg_wf {P : Prog} (hwf : P.wfCheck = true) :
    (runOnceProg P).wfCheck = true := by
  have hparts := hwf
  simp only [Prog.wfCheck, Bool.and_eq_true] at hparts ⊢
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · simpa [runOnceProg, runOnce_params] using hparts.1.1.1
  · simpa [runOnceProg, runOnce_nrets] using hparts.1.1.2
  · simpa [runOnceProg] using runOnce_wf hparts.1.2
  · rw [Array.all_eq_true]
    intro i hi
    have hi' : i < P.funcs.size := by simpa [runOnceProg] using hi
    have hfi : P.funcs[i].wfCheck P.funcs.size = true := by
      rw [Array.all_eq_true] at hparts
      exact hparts.2 i hi'
    simpa [runOnceProg] using runOnce_wf hfi

set_option maxHeartbeats 800000 in
theorem Passes.runOnceProg_dom {P : Prog} (hwf : P.wfCheck = true)
    (hdom : ToAsm.Prog.domCheck P = true) :
    ToAsm.Prog.domCheck (runOnceProg P) = true := by
  have hparts := hwf
  have hdom0 := hdom
  simp only [Prog.wfCheck, Bool.and_eq_true] at hparts
  unfold ToAsm.Prog.domCheck at hdom ⊢
  simp only [Bool.and_eq_true] at hdom ⊢
  refine ⟨?_, ?_⟩
  · exact runOnce_dom (f := P.main) (n := P.funcs.size) hparts.1.2 hdom.1
  · rw [Array.all_eq_true_iff_forall_mem]
    intro g' hg'
    obtain ⟨g, hg, rfl⟩ := Array.mem_map.mp hg'
    have hfi : g.wfCheck P.funcs.size = true :=
      Array.all_eq_true_iff_forall_mem.mp hparts.2 g hg
    have hdi : ToAsm.Func.domCheck g = true :=
      ToAsm.Prog.domCheck_funcs hdom0 hg
    exact runOnce_dom (f := g) (n := P.funcs.size) hfi hdi

/-- Change the ambient program to its one-round map while leaving the current
function text fixed.  At calls, the structural induction first replays the
callee under the mapped ambient program and `runOnce_sound` then rewrites that
callee's entry execution. -/
theorem Passes.runOnceProg_exec {P : Prog} (hPwf : P.wfCheck = true)
    (hPdom : ToAsm.Prog.domCheck P = true) {f : Func} {R : Regs}
    {st : EvmState} {rest : Rest} {res : FRes}
    (hexec : Exec (model := model) P f R st rest res) :
    Exec (model := model) (runOnceProg P) f R st rest res := by
  induction hexec with
  | const htail ih => exact Exec.const ih
  | op hget hop hlen htail ih => exact Exec.op hget hop hlen ih
  | opHalt hget hop => exact Exec.opHalt hget hop
  | @call f g R st st' ds as fid args rvals eb is t res
      hfid hget hplen heb hbody hlen htail ihbody ih =>
      have hgwf0 := progWf_func hPwf hfid
      have hgwf : g.wfCheck (runOnceProg P).funcs.size = true := by
        simpa [runOnceProg] using hgwf0
      have hgmem : g ∈ P.funcs := by
        obtain ⟨hi, hget⟩ := Array.getElem?_eq_some_iff.mp hfid
        exact Array.mem_iff_getElem.mpr ⟨fid, hi, hget⟩
      have hgdom : ToAsm.Func.domCheck g = true :=
        ToAsm.Prog.domCheck_funcs hPdom hgmem
      obtain ⟨-, -, ⟨eb', heb', -⟩, -⟩ :=
        func_wfCheck_iff.mp (runOnce_wf hgwf)
      have hbody' := runOnce_sound hgwf hgdom heb heb' ihbody
      refine Exec.call (g := runOnce g) (eb := eb') (runOnceProg_lookup hfid)
        hget ?_ heb' hbody' hlen ih
      simpa [runOnce_params] using hplen
  | @callHalt f g R st st' ds as fid args eb is t
      hfid hget hplen heb hbody ihbody =>
      have hgwf0 := progWf_func hPwf hfid
      have hgwf : g.wfCheck (runOnceProg P).funcs.size = true := by
        simpa [runOnceProg] using hgwf0
      have hgmem : g ∈ P.funcs := by
        obtain ⟨hi, hget⟩ := Array.getElem?_eq_some_iff.mp hfid
        exact Array.mem_iff_getElem.mpr ⟨fid, hi, hget⟩
      have hgdom : ToAsm.Func.domCheck g = true :=
        ToAsm.Prog.domCheck_funcs hPdom hgmem
      obtain ⟨-, -, ⟨eb', heb', -⟩, -⟩ :=
        func_wfCheck_iff.mp (runOnce_wf hgwf)
      have hbody' := runOnce_sound hgwf hgdom heb heb' ihbody
      refine Exec.callHalt (g := runOnce g) (eb := eb')
        (runOnceProg_lookup hfid) hget ?_ heb' hbody'
      simpa [runOnce_params] using hplen
  | jump htb hget hplen htail ih => exact Exec.jump htb hget hplen ih
  | branchTrue hc hv htb hget hplen htail ih =>
      exact Exec.branchTrue hc hv htb hget hplen ih
  | branchFalse hc htb hget hplen htail ih =>
      exact Exec.branchFalse hc htb hget hplen ih
  | ret hget => exact Exec.ret hget
  | halt hget hop => exact Exec.halt hget hop

theorem Passes.runOnceProg_sound {P : Prog} {yst0 yst' : EvmState}
    {o : Outcome} (hwf : P.wfCheck = true)
    (hdom : ToAsm.Prog.domCheck P = true)
    (hrun : Run (model := model) P yst0 yst' o) :
    Run (model := model) (runOnceProg P) yst0 yst' o := by
  have hparts := hwf
  simp only [Prog.wfCheck, Bool.and_eq_true] at hparts
  have hmainWf : P.main.wfCheck (runOnceProg P).funcs.size = true := by
    simpa [runOnceProg] using hparts.1.2
  have hmainDom := ToAsm.Prog.domCheck_main hdom
  have hmainParams : P.main.params = [] := List.isEmpty_iff.mp hparts.1.1.1
  cases hrun with
  | normal heb hexec =>
      rename_i eb
      obtain ⟨-, -, ⟨eb', heb', -⟩, -⟩ :=
        func_wfCheck_iff.mp (runOnce_wf hmainWf)
      have hamb := runOnceProg_exec hwf hdom hexec
      have hlocal := runOnce_sound (args := []) hmainWf hmainDom heb heb'
        (by simpa [hmainParams, Regs.setMany_nil_left] using hamb)
      exact Run.normal (by simpa [runOnceProg] using heb')
        (by simpa [runOnceProg, runOnce_params, hmainParams,
          Regs.setMany_nil_left] using hlocal)
  | halt heb hexec =>
      rename_i eb
      obtain ⟨-, -, ⟨eb', heb', -⟩, -⟩ :=
        func_wfCheck_iff.mp (runOnce_wf hmainWf)
      have hamb := runOnceProg_exec hwf hdom hexec
      have hlocal := runOnce_sound (args := []) hmainWf hmainDom heb heb'
        (by simpa [hmainParams, Regs.setMany_nil_left] using hamb)
      exact Run.halt (by simpa [runOnceProg] using heb')
        (by simpa [runOnceProg, runOnce_params, hmainParams,
          Regs.setMany_nil_left] using hlocal)

def Passes.runOnceProgN : Nat → Prog → Prog
  | 0, P => P
  | n + 1, P => runOnceProgN n (runOnceProg P)

theorem Passes.runOnceProgN_wf : ∀ (n : Nat) {P : Prog}, P.wfCheck = true →
    (runOnceProgN n P).wfCheck = true := by
  intro n
  induction n with
  | zero => exact fun h => h
  | succ n ih =>
      intro P hwf
      exact ih (runOnceProg_wf hwf)

theorem Passes.runOnceProgN_dom : ∀ (n : Nat) {P : Prog},
    P.wfCheck = true → ToAsm.Prog.domCheck P = true →
      ToAsm.Prog.domCheck (runOnceProgN n P) = true := by
  intro n
  induction n with
  | zero => exact fun _ h => h
  | succ n ih =>
      intro P hwf hdom
      exact ih (runOnceProg_wf hwf) (runOnceProg_dom hwf hdom)

theorem Passes.runOnceProgN_sound : ∀ (n : Nat) {P : Prog}
    {yst0 yst' : EvmState} {o : Outcome},
    P.wfCheck = true → ToAsm.Prog.domCheck P = true →
      Run (model := model) P yst0 yst' o →
      Run (model := model) (runOnceProgN n P) yst0 yst' o := by
  intro n
  induction n with
  | zero => exact fun _ _ h => h
  | succ n ih =>
      intro P yst0 yst' o hwf hdom hrun
      exact ih (runOnceProg_wf hwf) (runOnceProg_dom hwf hdom)
        (runOnceProg_sound hwf hdom hrun)

omit model in
theorem Passes.optimizeFunc_eq_runOnce3 (f : Func) :
    optimizeFunc f = runOnce (runOnce (runOnce f)) := by
  simp only [optimizeFunc, pipelineRounds,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp only [show (3 - 0 + 1 - 1) / 1 = 3 from rfl]
  rw [show List.range' 0 3 1 = [0, 1, 2] from rfl]
  rfl

omit model in
theorem optimizeCandidate_eq_rounds (P : Prog) :
    optimizeCandidate P = Passes.runOnceProgN 3 (Passes.inlineProg P) := by
  simp [optimizeCandidate, Passes.runOnceProgN, Passes.runOnceProg,
    Passes.optimizeFunc_eq_runOnce3, Array.map_map, Function.comp_def]

theorem Passes.inlineProgN_wf : ∀ (n : Nat) {P : Prog}, P.wfCheck = true →
    (inlineProgN n P).wfCheck = true := by
  intro n
  induction n with
  | zero => exact fun h => h
  | succ n ih =>
      intro P hwf
      have hround := inlineRound_wf hwf
      simp only [inlineProgN]
      split
      · exact hround
      · exact ih hround

theorem Passes.inlineProg_wf {P : Prog} (hwf : P.wfCheck = true) :
    (inlineProg P).wfCheck = true := by
  rw [inlineProg_eq_inlineProgN]
  exact inlineProgN_wf 3 hwf

/-! ### The top-level statement -/

/-- **`SsaCfg.optimizeProg_sound`, reproduced verbatim** (post-fix signature:
`hwf` *and* `hdom`).

The defensive-fallback half is **proved** here; the remaining `sorry` is the
branch where the pipeline's output passes the gate, which is where the four
per-pass lemmas above (plus the simultaneous whole-program induction described in
this section's header) do their work.

**Current obstruction.**  The four per-pass `_wf` preservation declarations
and their `runOnce_wf` composition are now proved, and `runOnce_dom` derives its
intermediate checks internally.  This branch still depends immediately on the
register-side final assembly of `cse_sound` recorded above, followed by the
simultaneous whole-program replay required to transport recursive calls.

With `hdom` this statement is, to the best of my analysis, true — the
counterexample `Counterexample.optimizeProg_sound_false_without_dom` refutes only
the version without it. -/
theorem optimizeProg_sound' {P : Prog} {yst0 yst' : EvmState} {o : Outcome}
    (hwf : P.wfCheck = true) (hdom : ToAsm.Prog.domCheck P = true)
    (hrun : Run (model := model) P yst0 yst' o) :
    Run (model := model) (optimizeProg P) yst0 yst' o := by
  by_cases hgate : ((optimizeCandidate P).wfCheck
      && ToAsm.Prog.domCheck (optimizeCandidate P)) = true
  · -- the gate accepted the pipeline's output: this is the real content
    rw [optimizeProg_of_gate_true hgate]
    let P0 := Passes.inlineProg P
    have hwf0 : P0.wfCheck = true := Passes.inlineProg_wf hwf
    have hrun0 : Run (model := model) P0 yst0 yst' o :=
      inlineProg_sound hwf hrun
    /- The remaining preservation goal is not supplied by any proved inliner
    declaration in this file.  Neither the accepted output gate nor
    `runOnce_dom` can be used backwards (trivial-parameter elimination has a
    checked counterexample to precisely that converse).  Lean's exact missing
    target is:

        ToAsm.Prog.domCheck (Passes.inlineProg P) = true

    under `hwf : P.wfCheck = true` and
    `hdom : ToAsm.Prog.domCheck P = true`.
    -/
    have hdom0 : ToAsm.Prog.domCheck P0 = true := by
      sorry
    rw [optimizeCandidate_eq_rounds]
    exact Passes.runOnceProgN_sound 3 hwf0 hdom0 hrun0
  · -- the gate rejected it: `optimizeProg` returned `P` unchanged
    simp only [Bool.not_eq_true] at hgate
    exact optimizeProg_sound_of_fallback hgate hrun

#print axioms optimizeProg_sound'

end YulEvmCompiler.SsaCfg
