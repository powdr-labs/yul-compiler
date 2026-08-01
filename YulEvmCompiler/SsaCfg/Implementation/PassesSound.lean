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

Eight `sorry`s, each documented at its declaration:

* pass 0 (inlining): `inlineOnce_sound`, `inlineFunc_sound`, `pruneFuncs_sound`,
  `inlineProg_sound`;
* passes 1 and 3: `elimTrivialParams_sound`, `cse_sound`;
* dominance preservation: `elimTrivialParams_dom`
  (`constFold_dom`, `cse_dom`, `dve_dom`, and `runOnce_dom` *are* proved);
* the gate-accepted branch of `optimizeProg_sound'`.

Two kinds of obligation remain, and it is worth separating them.

**(a) Loop inversion.** Every pass except `dve` is written as an `Id.run` loop.
The generic tool now exists — `Id.forIn_eq_foldl` / `Id.forIn_array_eq_foldl`,
with the recipe recorded at their declaration (`dsimp only` first, state the step
function over `MProd`, pass `h` as a tactic block, `grind` for the
`pure`-inside-a-`match` branches). It is applied end to end for `constFold`
(`constFold_blocks_eq`); `cse`, `elimTrivialParams`, `inlineOnce` and
`pruneFuncs` still need the same treatment, and the early-return loops
(`findTrivialParam`, `inlineFunc`) need the `ForInStep.done` variant of the
bridge, which is not proved here.

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

abbrev CSEInner := MProd (List Instr) (MProd CseTab Subst)
abbrev CSEOuter := MProd (Array Block) (MProd (Array CseTab) Subst)

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
  match substInstr st.2.2 ins0 with
  | .const d v =>
    match st.2.1.consts.find? (·.1 == v) with
    | some (_, d0) => ⟨st.1, st.2.1, st.2.2.insert d d0⟩
    | none =>
      ⟨.const d v :: st.1, { st.2.1 with consts := (v, d) :: st.2.1.consts }, st.2.2⟩
  | .op [d] yop args =>
    if pureOp yop then
      match st.2.1.ops.find? (·.1 == (yop, args)) with
      | some (_, d0) => ⟨st.1, st.2.1, st.2.2.insert d d0⟩
      | none =>
        ⟨.op [d] yop args :: st.1,
          { st.2.1 with ops := ((yop, args), d) :: st.2.1.ops }, st.2.2⟩
    else ⟨.op [d] yop args :: st.1, st.2.1, st.2.2⟩
  | ins => ⟨ins :: st.1, st.2.1, st.2.2⟩

def cseBlockStep (f : Func) (srcs : Array (List BlockId))
    (bi : BlockId) (st : CSEOuter) : CSEOuter :=
  let b := f.blocks[bi]!
  let tab := cseEntryTab f srcs st.2.1 bi
  let r := b.instrs.foldl (fun s i => cseInstrStep i s) ⟨[], tab, st.2.2⟩
  ⟨st.1.push { b with instrs := r.1.reverse },
    st.2.1.setIfInBounds bi r.2.1, r.2.2⟩

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
      rw [Id.forIn_eq_foldl (g := cseInstrStep) (h := by
        intro i s
        cases hs : substInstr s.2.2 i with
        | const d v =>
          simp only [cseInstrStep, hs]
          split <;> rename_i hfind <;> simp only [hfind] <;> rfl
        | op ds yop args =>
          cases ds with
          | nil => simp [cseInstrStep, hs]
          | cons d rest =>
            cases rest with
            | nil =>
              simp only [cseInstrStep, hs]
              split
              · split <;> rename_i hfind <;> simp only [hfind] <;> rfl
              · rfl
            | cons e es => simp [cseInstrStep, hs]
        | call ds fid args => simp [cseInstrStep, hs])]
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
  let r := b.instrs.foldl (fun s i => cseInstrStep i s) ⟨[], tab, st.2.2⟩
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

def CseTabSound (f : Func) (tab : CseTab) : Prop :=
  (∀ {yop args d}, ((yop, args), d) ∈ tab.ops → CseDef f (.op yop args) d) ∧
  (∀ {v d}, (v, d) ∈ tab.consts → CseDef f (.const v) d)

def CseSubSound (f : Func) (σ : Subst) : Prop :=
  ∀ {d d0}, σ[d]? = some d0 → ∃ e, CseDef f e d ∧ CseDef f e d0

def SubstExt (σ τ : Subst) : Prop :=
  ∀ {x y : ValId}, σ[x]? = some y → τ[x]? = some y

def RangeFree (σ : Subst) : Prop :=
  ∀ {x y : ValId}, σ[x]? = some y → σ[y]? = none

def CSEInv (f : Func) (seen : List ValId) (tab : CseTab) (σ : Subst) : Prop :=
  CseTabSound f tab ∧ CseSubSound f σ ∧ RangeFree σ
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
    {seen : List ValId} {tab : CseTab} {σ : Subst} (hinv : CSEInv f seen tab σ)
    (i : Instr) (hi : i ∈ b.instrs) (hnd : (seen ++ i.defs).Nodup) :
    let r := cseInstrStep i ⟨[], tab, σ⟩
    CSEInv f (seen ++ i.defs) r.2.1 r.2.2 ∧ SubstExt σ r.2.2 := by
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
            exact ⟨hinv.insert hd hd0.1 hd0.2 hc' hc0,
              CSEInv.insert_ext d0 hinv hd⟩
          · exact ⟨hinv.addOp hd hc, ext_refl⟩
        · rw [if_neg hp]
          exact ⟨hinv.weaken (fun x hx => List.mem_append_left _ hx), ext_refl⟩
  | call ds fid args =>
    simp only [cseInstrStep, substInstr]
    exact ⟨hinv.weaken (by
      intro x hx
      exact List.mem_append_left _ hx), ext_refl⟩

theorem cseInstrStep_state (i : Instr) (acc : List Instr) (tab : CseTab) (σ : Subst) :
    (cseInstrStep i ⟨acc, tab, σ⟩).2 = (cseInstrStep i ⟨[], tab, σ⟩).2 := by
  cases i with
  | const d v => simp only [cseInstrStep, substInstr]; split <;> rfl
  | op ds yop args =>
    cases ds with
    | nil => rfl
    | cons d rest =>
      cases rest with
      | cons e es => rfl
      | nil => simp only [cseInstrStep, substInstr]; split <;> (try split) <;> rfl
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

theorem cseInstrStep_stable {seen : List ValId} {tab : CseTab} {σ : Subst}
    (i : Instr) (hnd : (seen ++ i.defs).Nodup) :
    SubstStable seen σ (cseInstrStep i ⟨[], tab, σ⟩).2.2 := by
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
          · have hne : d ≠ x := by
              intro hdx
              subst x
              exact fresh (by simp [Instr.defs]) hx
            have hdx : (d == x) = false := by simp [hne]
            simp [Std.HashMap.getElem?_insert, hdx]
          · rfl
        · rfl
  | call ds fid args => rfl

theorem cseInstrFold_inv {f : Func} {b : Block} (hb : b ∈ f.blocks.toList)
    {seen : List ValId} {tab : CseTab} {σ : Subst} (hinv : CSEInv f seen tab σ)
    (l : List Instr) (hmem : ∀ i ∈ l, i ∈ b.instrs)
    (hnd : (seen ++ l.flatMap Instr.defs).Nodup) (acc : List Instr) :
    let r := l.foldl (fun s i => cseInstrStep i s) ⟨acc, tab, σ⟩
    CSEInv f (seen ++ l.flatMap Instr.defs) r.2.1 r.2.2 ∧ SubstExt σ r.2.2 := by
  induction l generalizing seen tab σ acc with
  | nil => simpa using And.intro hinv (show SubstExt σ σ from fun h => h)
  | cons i is ih =>
    simp only [List.flatMap_cons] at hnd ⊢
    have hprefix : (seen ++ i.defs).Nodup := by
      apply List.Nodup.of_append_left (l₂ := is.flatMap Instr.defs)
      simpa [List.append_assoc] using hnd
    have hone := cseInstrStep_inv hb hinv i (hmem i (by simp)) hprefix
    have hstate := cseInstrStep_state i acc tab σ
    let s1 := cseInstrStep i ⟨acc, tab, σ⟩
    have hinv1 : CSEInv f (seen ++ i.defs) s1.2.1 s1.2.2 := by
      rw [hstate]
      exact hone.1
    have hext1 : SubstExt σ s1.2.2 := by
      rw [hstate]
      exact hone.2
    have htail : ((seen ++ i.defs) ++ is.flatMap Instr.defs).Nodup := by
      simpa [List.append_assoc] using hnd
    have hrest := ih hinv1 (fun j hj => hmem j (by simp [hj])) htail s1.1
    rw [List.foldl_cons]
    refine ⟨?_, hext1.trans hrest.2⟩
    simpa [List.append_assoc] using hrest.1

theorem cseInstrFold_stable {f : Func} {b : Block} (hb : b ∈ f.blocks.toList)
    {seen : List ValId} {tab : CseTab} {σ : Subst} (hinv : CSEInv f seen tab σ)
    (l : List Instr) (hmem : ∀ i ∈ l, i ∈ b.instrs)
    (hnd : (seen ++ l.flatMap Instr.defs).Nodup) (acc : List Instr) :
    SubstStable seen σ
      (l.foldl (fun s i => cseInstrStep i s) ⟨acc, tab, σ⟩).2.2 := by
  induction l generalizing seen tab σ acc with
  | nil => intro x hx; rfl
  | cons i is ih =>
    simp only [List.flatMap_cons] at hnd
    have hprefix : (seen ++ i.defs).Nodup := by
      apply List.Nodup.of_append_left (l₂ := is.flatMap Instr.defs)
      simpa [List.append_assoc] using hnd
    have hone := cseInstrStep_inv hb hinv i (hmem i (by simp)) hprefix
    have hstate := cseInstrStep_state i acc tab σ
    let s1 := cseInstrStep i ⟨acc, tab, σ⟩
    have hinv1 : CSEInv f (seen ++ i.defs) s1.2.1 s1.2.2 := by
      rw [hstate]
      exact hone.1
    have htail : ((seen ++ i.defs) ++ is.flatMap Instr.defs).Nodup := by
      simpa [List.append_assoc] using hnd
    have hs1 : SubstStable seen σ s1.2.2 := by
      rw [hstate]
      exact cseInstrStep_stable i hprefix
    have hrest := ih hinv1 (fun j hj => hmem j (by simp [hj])) htail s1.1
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
    ⟨[], tab, (csePrefix f n).2.2⟩
  have htab : CSEInv f (cseSeen f n) tab (csePrefix f n).2.2 :=
    cseEntryTab_inv hpre
  have hr := cseInstrFold_inv hbmem htab b.instrs (fun i hi => hi)
    hseenNodup []
  have hstable := cseInstrFold_stable hbmem htab b.instrs (fun i hi => hi)
    hseenNodup []
  change CSEPrefixInv f (n + 1)
  rw [CSEPrefixInv, csePrefix_succ]
  simp only [cseBlockStep]
  rw [hbBang, hseen]
  change CSEInv f (cseSeen f n ++ b.instrs.flatMap Instr.defs) {} r.2.2
      ∧ ((csePrefix f n).2.1.setIfInBounds n r.2.1).size = f.blocks.size
      ∧ ∀ p < n + 1,
        CSEInv f (cseSeen f n ++ b.instrs.flatMap Instr.defs)
          ((csePrefix f n).2.1.setIfInBounds n r.2.1)[p]! r.2.2
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
    hseenNodup []
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
    hseenNodup []
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

theorem cseInstrStep_out {i : Instr} {acc : List Instr} {tab : CseTab} {σ : Subst} :
    let r := cseInstrStep i ⟨acc, tab, σ⟩
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
              split <;> (try split) <;> simp
          | cons e es => simp [cseInstrStep, substInstr]
  | call ds fid args => simp [cseInstrStep, substInstr]

theorem cseInstrStep_acc_sublist {i : Instr} {acc : List Instr} {tab : CseTab}
    {σ : Subst} : acc.Sublist (cseInstrStep i ⟨acc, tab, σ⟩).1 := by
  rcases cseInstrStep_out (i := i) (acc := acc) (tab := tab) (σ := σ) with h | h
  · rw [h]
  · rw [h]
    exact List.Sublist.cons _ (List.Sublist.refl _)

theorem cseInstrStep_tabVals {i : Instr} {acc : List Instr} {tab : CseTab}
    {σ : Subst} {x : ValId} (hx : x ∈ cseTabVals (cseInstrStep i ⟨acc, tab, σ⟩).2.1) :
    x ∈ cseTabVals tab ∨ x ∈ (cseInstrStep i ⟨acc, tab, σ⟩).1.flatMap Instr.defs := by
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
                      simpa [cseInstrStep, substInstr, hp, hfind] using hx
                    exact Or.inl hx'
                | none =>
                    simp only [cseInstrStep, substInstr, hp, if_true, hfind, cseTabVals,
                      List.map_cons, List.mem_append, List.mem_cons, Instr.defs,
                      List.flatMap_cons] at hx ⊢
                    tauto
              · have hx' : x ∈ cseTabVals tab := by
                  simpa [cseInstrStep, substInstr, hp] using hx
                exact Or.inl hx'
  | call ds fid args => exact Or.inl hx

theorem cseInstrStep_defs_resolve {f : Func} {seen : List ValId} {i : Instr}
    {acc : List Instr} {tab : CseTab} {σ : Subst} (hinv : CSEInv f seen tab σ)
    (hnd : (seen ++ i.defs).Nodup) {d : ValId} (hd : d ∈ i.defs) :
    let r := cseInstrStep i ⟨acc, tab, σ⟩
    substV r.2.2 d ∈ r.1.flatMap Instr.defs ∨ substV r.2.2 d ∈ cseTabVals tab := by
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
                    simp [cseInstrStep, substInstr, hp, hfind, substV,
                      Std.HashMap.getD_eq_getD_getElem?, hdnone]
                    exact Or.inl (by simp [Instr.defs])
                | some a =>
                    obtain ⟨key, d0⟩ := a
                    right
                    have hm : (key, d0) ∈ tab.ops := List.mem_of_find?_eq_some hfind
                    have hd0mem : d0 ∈ cseTabVals tab :=
                      List.mem_append_left _ (List.mem_map.mpr ⟨(key, d0), hm, rfl⟩)
                    simpa [cseInstrStep, substInstr, hp, hfind, substV,
                      Std.HashMap.getD_eq_getD_getElem?, Std.HashMap.getElem?_insert] using hd0mem
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
    (tab : CseTab) (σ : Subst) :
    acc.Sublist (l.foldl (fun s i => cseInstrStep i s) ⟨acc, tab, σ⟩).1 := by
  induction l generalizing acc tab σ with
  | nil => exact List.Sublist.refl _
  | cons i is ih =>
      rw [List.foldl_cons]
      exact (cseInstrStep_acc_sublist (i := i)).trans (ih _ _ _)

theorem cseInstrFold_tabVals (l : List Instr) (acc : List Instr)
    (tab : CseTab) (σ : Subst) {x : ValId}
    (hx : x ∈ cseTabVals
      (l.foldl (fun s i => cseInstrStep i s) ⟨acc, tab, σ⟩).2.1) :
    x ∈ cseTabVals tab ∨
      x ∈ (l.foldl (fun s i => cseInstrStep i s) ⟨acc, tab, σ⟩).1.flatMap Instr.defs := by
  induction l generalizing acc tab σ with
  | nil => exact Or.inl hx
  | cons i is ih =>
      rw [List.foldl_cons] at hx ⊢
      let s1 := cseInstrStep i ⟨acc, tab, σ⟩
      rcases ih s1.1 s1.2.1 s1.2.2 hx with htab | hout
      · rcases cseInstrStep_tabVals htab with hold | hnew
        · exact Or.inl hold
        · exact Or.inr
            (((cseInstrFold_acc_sublist is s1.1 s1.2.1 s1.2.2).flatMap _).subset hnew)
      · exact Or.inr hout

theorem cseInstrFold_defs_resolve {f : Func} {b : Block}
    (hb : b ∈ f.blocks.toList) {seen : List ValId} {tab : CseTab} {σ : Subst}
    (hinv : CSEInv f seen tab σ) (l : List Instr)
    (hmem : ∀ i ∈ l, i ∈ b.instrs)
    (hnd : (seen ++ l.flatMap Instr.defs).Nodup) (acc : List Instr) {d : ValId}
    (hd : d ∈ l.flatMap Instr.defs) :
    let r := l.foldl (fun s i => cseInstrStep i s) ⟨acc, tab, σ⟩
    substV r.2.2 d ∈ r.1.flatMap Instr.defs ∨ substV r.2.2 d ∈ cseTabVals tab := by
  induction l generalizing seen tab σ acc with
  | nil => simp at hd
  | cons i is ih =>
      simp only [List.flatMap_cons, List.mem_append] at hd
      have hprefix : (seen ++ i.defs).Nodup := by
        apply List.Nodup.of_append_left (l₂ := is.flatMap Instr.defs)
        simpa [List.append_assoc] using hnd
      have hone := cseInstrStep_inv hb hinv i (hmem i (by simp)) hprefix
      have hstate := cseInstrStep_state i acc tab σ
      let s1 := cseInstrStep i ⟨acc, tab, σ⟩
      have hinv1 : CSEInv f (seen ++ i.defs) s1.2.1 s1.2.2 := by
        rw [hstate]
        exact hone.1
      have htail : ((seen ++ i.defs) ++ is.flatMap Instr.defs).Nodup := by
        simpa [List.append_assoc] using hnd
      have hstable := cseInstrFold_stable hb hinv1 is
        (fun j hj => hmem j (by simp [hj])) htail s1.1
      rw [List.foldl_cons]
      dsimp only
      rcases hd with hd | hd
      · have hnow := cseInstrStep_defs_resolve hinv hprefix hd (acc := acc)
        have hsubst : substV
            (is.foldl (fun s i => cseInstrStep i s) s1).2.2 d = substV s1.2.2 d := by
          simp only [substV, Std.HashMap.getD_eq_getD_getElem?]
          rw [hstable d (List.mem_append_right _ hd)]
        rw [hsubst]
        rcases hnow with hout | htab
        · exact Or.inl
            (((cseInstrFold_acc_sublist is s1.1 s1.2.1 s1.2.2).flatMap _).subset hout)
        · exact Or.inr htab
      · have hrest := ih hinv1 (fun j hj => hmem j (by simp [hj])) htail s1.1 hd
        rcases hrest with hout | htab1
        · exact Or.inl hout
        · rcases cseInstrStep_tabVals htab1 with htab | hnew
          · exact Or.inr htab
          · exact Or.inl
              (((cseInstrFold_acc_sublist is s1.1 s1.2.1 s1.2.2).flatMap _).subset hnew)

theorem cseInstrFold_origin {f : Func} {b : Block}
    (hb : b ∈ f.blocks.toList) {seen : List ValId} {tab : CseTab} {σ : Subst}
    (hinv : CSEInv f seen tab σ) (l : List Instr)
    (hmem : ∀ i ∈ l, i ∈ b.instrs)
    (hnd : (seen ++ l.flatMap Instr.defs).Nodup) (acc : List Instr)
    {τ : Subst}
    (hext : SubstExt
      (l.foldl (fun s i => cseInstrStep i s) ⟨acc, tab, σ⟩).2.2 τ)
    (hrange : RangeFree τ) {j : Instr}
    (hj : j ∈ (l.foldl (fun s i => cseInstrStep i s) ⟨acc, tab, σ⟩).1) :
    j ∈ acc ∨ ∃ i ∈ l, substInstr τ j = substInstr τ i := by
  induction l generalizing seen tab σ acc with
  | nil => exact Or.inl hj
  | cons i is ih =>
      have hprefix : (seen ++ i.defs).Nodup := by
        apply List.Nodup.of_append_left (l₂ := is.flatMap Instr.defs)
        simpa [List.append_assoc] using hnd
      have hone := cseInstrStep_inv hb hinv i (hmem i (by simp)) hprefix
      have hstate := cseInstrStep_state i acc tab σ
      let s1 := cseInstrStep i ⟨acc, tab, σ⟩
      have hinv1 : CSEInv f (seen ++ i.defs) s1.2.1 s1.2.2 := by
        rw [hstate]
        exact hone.1
      have htail : ((seen ++ i.defs) ++ is.flatMap Instr.defs).Nodup := by
        simpa [List.append_assoc] using hnd
      have hfoldInv := cseInstrFold_inv hb hinv1 is
        (fun k hk => hmem k (by simp [hk])) htail s1.1
      rw [List.foldl_cons] at hext hj
      rcases ih hinv1 (fun k hk => hmem k (by simp [hk])) htail s1.1 hext hj with
        hj1 | ⟨k, hk, heq⟩
      · rcases cseInstrStep_out (i := i) (acc := acc) (tab := tab) (σ := σ) with
          hout | hout
        · exact Or.inl (hout ▸ hj1)
        · rw [hout] at hj1
          rcases List.mem_cons.mp hj1 with rfl | hjacc
          · right
            refine ⟨i, by simp, ?_⟩
            apply substInstr_absorb
            have honeExt : SubstExt σ s1.2.2 := by
              rw [hstate]
              exact hone.2
            have htailExt : SubstExt s1.2.2 τ :=
              SubstExt.trans (σ := s1.2.2)
                (τ := (is.foldl (fun s i => cseInstrStep i s) s1).2.2)
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
  (b.instrs.foldl (fun s ins => cseInstrStep ins s) ⟨[], tab, st.2.2⟩).2.1

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
          (csePrefix f i).2.2⟩).2.1)).size := by simpa
  rw [getElem!_eq_getElem hi1, Array.getElem_setIfInBounds_self]

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
                (csePrefix f n).2.2⟩).2.1)).size := by simpa
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
  let r := b.instrs.foldl (fun s ins => cseInstrStep ins s) ⟨[], tab, st.2.2⟩
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
    hndBlock []
  have hrPrefix : (csePrefix f (i + 1)).2.2 = r.2.2 := by
    rw [csePrefix_succ]
    simp only [cseBlockStep]
    rw [hbang]
  have hext : SubstExt r.2.2 τ := by
    rw [← hrPrefix]
    exact csePrefix_ext_to hnd (Nat.succ_le_of_lt hi) (Nat.le_refl _)
  have hfinalInv := (csePrefixInv hnd f.blocks.size (Nat.le_refl _)).1
  have hrange : RangeFree τ := hfinalInv.2.2.1
  have hstable : SubstStable (cseSeen f (i + 1)) r.2.2 τ := by
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
        hndBlock [] hext hrange hjr
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
        (fun ins hins => hins) hndBlock [] (List.mem_flatMap.mpr ⟨ins, hins, hyd⟩)
      have hymem : y ∈ cseSeen f (i + 1) := by
        rw [hseen]
        exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨ins, hins, hyd⟩)
      have hsubst : substV τ y = substV r.2.2 y := by
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
    rcases cseInstrFold_tabVals b.instrs [] tab st.2.2 hx with hav | hout
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

section
variable [model : ExternalModel]

/-- **One splice preserves executions.**

`sorry`. The interesting step is the `Exec.call` / `Exec.callHalt` node of the
original derivation. In the inlined function that node becomes: `jump` into the
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

The precise first missing proof object is an `inlineOnce = some f'` site
inversion exporting `bi`, `ci`, the selected call/callee and the five splice
equations.  It then feeds a renamed-callee `Exec` replay lemma.  That replay
must handle the deliberately non-injective parameter part of `ρ` (duplicate
actual arguments) with `inlineParam_regs_agree`, use freshness only for the
offset-renamed non-parameters, prove appended-block lookup equations, and turn
callee `ret` into the continuation jump. -/
theorem inlineOnce_sound {P : Prog} {counts : Array Nat} {f f' : Func} {args : List U256}
    {st : EvmState} {res : FRes} {eb eb' : Block}
    (hPwf : P.wfCheck = true) (hwf : f.wfCheck P.funcs.size = true)
    (hio : Passes.inlineOnce counts P.funcs f = some f')
    (heb : f.blocks[f.entry]? = some eb)
    (heb' : f'.blocks[f'.entry]? = some eb')
    (hexec : Exec (model := model) P f (Regs.empty.setMany f.params args) st
      ⟨eb.instrs, eb.term⟩ res) :
    Exec (model := model) P f' (Regs.empty.setMany f'.params args) st
      ⟨eb'.instrs, eb'.term⟩ res := by
  sorry

/-- **The budgeted fixed point preserves executions**: iterate
`inlineOnce_sound` at most eight times.  Besides the early-return loop
inversion, applying the one-step theorem repeatedly requires a preservation
lemma `inlineOnce ... f = some f' → f.wfCheck n = true → f'.wfCheck n = true`;
that lemma is not yet present, so the dependency chain cannot currently be
closed from the initial `hwf` alone. -/
theorem inlineFunc_sound {P : Prog} {counts : Array Nat} {f : Func} {args : List U256}
    {st : EvmState} {res : FRes} {eb eb' : Block}
    (hPwf : P.wfCheck = true) (hwf : f.wfCheck P.funcs.size = true)
    (heb : f.blocks[f.entry]? = some eb)
    (heb' : (Passes.inlineFunc counts P.funcs f).blocks[f.entry]? = some eb')
    (hexec : Exec (model := model) P f (Regs.empty.setMany f.params args) st
      ⟨eb.instrs, eb.term⟩ res) :
    Exec (model := model) P (Passes.inlineFunc counts P.funcs f)
      (Regs.empty.setMany f.params args) st ⟨eb'.instrs, eb'.term⟩ res := by
  sorry

/-- **Pruning preserves whole-program runs.** Dead-code elimination at function
granularity: `Exec` reaches `P.funcs` only through `Exec.call`'s
`P.funcs[fid]? = some g`, so it suffices that (i) the reachability fixed point
in `pruneFuncs` marks every id reachable from `main` — a `used`-monotonicity
argument on its worklist loop, the same shape as `ToAsm.liveInSets_least` — and
(ii) `remap` is a bijection between marked ids and the kept array, which the
`fix` rewrite applies uniformly to every call instruction. `sorry`. -/
theorem pruneFuncs_sound {P : Prog} {yst0 yst' : EvmState} {o : Outcome}
    (hwf : P.wfCheck = true) (hrun : Run (model := model) P yst0 yst' o) :
    Run (model := model) (Passes.pruneFuncs P) yst0 yst' o := by
  sorry

/-- **Inlining soundness**, the statement the top-level proof consumes.

`sorry`: composes `inlineFunc_sound` (for `main` and for every element of
`funcs` — a *simultaneous* induction over the derivation, because `Exec.call`
recurses into a callee that is itself being inlined) with `pruneFuncs_sound`,
around the three-round loop of `Passes.inlineProg`. No dominance hypothesis. -/
theorem inlineProg_sound {P : Prog} {yst0 yst' : EvmState} {o : Outcome}
    (hwf : P.wfCheck = true) (hrun : Run (model := model) P yst0 yst' o) :
    Run (model := model) (Passes.inlineProg P) yst0 yst' o := by
  sorry

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

/-- **Pass 1 (trivial block-parameter elimination) soundness**, under dominance.

`sorry`. The invariant is `LiveAgree li i σ R R'` for `σ = (p ↦ v)`, carried
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
theorem elimTrivialParams_sound {P : Prog} {f : Func} {args : List U256} {st : EvmState}
    {res : FRes} {eb eb' : Block} (hwf : f.wfCheck P.funcs.size = true)
    (hdom : ToAsm.Func.domCheck f = true)
    (heb : f.blocks[f.entry]? = some eb)
    (heb' : (Passes.elimTrivialParams f).blocks[f.entry]? = some eb')
    (hexec : Exec (model := model) P f (Regs.empty.setMany f.params args) st
      ⟨eb.instrs, eb.term⟩ res) :
    Exec (model := model) P (Passes.elimTrivialParams f) (Regs.empty.setMany f.params args) st
      ⟨eb'.instrs, eb'.term⟩ res := by
  sorry

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
      obtain ⟨e, -, hy⟩ := hsub ht
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

def cseInstrsOut (τ : Subst) : List Instr → CseTab → Subst → List Instr
  | [], _, _ => []
  | i :: is, tab, σ =>
      let s := cseInstrStep i ⟨[], tab, σ⟩
      s.1.reverse.map (substInstr τ) ++ cseInstrsOut τ is s.2.1 s.2.2

omit model in
theorem cseInstrStep_acc_eq (i : Instr) (acc : List Instr)
    (tab : CseTab) (σ : Subst) :
    cseInstrStep i ⟨acc, tab, σ⟩ =
      let s := cseInstrStep i ⟨[], tab, σ⟩
      ⟨s.1 ++ acc, s.2.1, s.2.2⟩ := by
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
              split <;> (try split) <;> rfl
  | call ds fid args => rfl

omit model in
theorem cseInstrFold_acc_state (l : List Instr) (acc : List Instr)
    (tab : CseTab) (σ : Subst) :
    let r := l.foldl (fun s i => cseInstrStep i s) ⟨acc, tab, σ⟩
    let r0 := l.foldl (fun s i => cseInstrStep i s) ⟨[], tab, σ⟩
    r = ⟨r0.1 ++ acc, r0.2.1, r0.2.2⟩ := by
  induction l generalizing acc tab σ with
  | nil => rfl
  | cons i is ih =>
      rw [List.foldl_cons, List.foldl_cons, cseInstrStep_acc_eq]
      let s := cseInstrStep i ⟨[], tab, σ⟩
      rw [ih (acc := s.1 ++ acc), ih (acc := s.1)]
      simp [List.append_assoc]

omit model in
theorem cseInstrFold_acc (τ : Subst) (l : List Instr) (acc : List Instr)
    (tab : CseTab) (σ : Subst) :
    let r := l.foldl (fun s i => cseInstrStep i s) ⟨acc, tab, σ⟩
    let r0 := l.foldl (fun s i => cseInstrStep i s) ⟨[], tab, σ⟩
    r.1.reverse.map (substInstr τ) =
      acc.reverse.map (substInstr τ) ++ r0.1.reverse.map (substInstr τ)
      ∧ r.2 = r0.2 := by
  rw [cseInstrFold_acc_state]
  simp [List.reverse_append, List.map_append]

omit model in
theorem cseInstrsOut_eq_fold (τ : Subst) (l : List Instr)
    (tab : CseTab) (σ : Subst) :
    cseInstrsOut τ l tab σ =
      (l.foldl (fun s i => cseInstrStep i s) ⟨[], tab, σ⟩).1.reverse.map
        (substInstr τ) := by
  induction l generalizing tab σ with
  | nil => rfl
  | cons i is ih =>
      rw [cseInstrsOut]
      let s := cseInstrStep i ⟨[], tab, σ⟩
      rw [ih]
      have hacc := cseInstrFold_acc τ is s.1 s.2.1 s.2.2
      rw [List.foldl_cons]
      exact hacc.1.symm

end Passes

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

**Remaining obstruction (2026-08-01).**  `CseTabRuntime` is sufficient for a
dropped definition and `setMany_inheritTab` is sufficient at a jump, but the
actual output is finally rewritten by the *whole-function* substitution `τ`.
Consequently an instruction earlier in fold order is rewritten even when the
domain definition that inserted `d ↦ d₀` occurs later.  To transport its
`getMany`, the induction needs `R d = R' (substV τ d)` for every actually-read
`d`, not merely for representatives in the current table.  This is not implied
by `CseTabRuntime`: on loop re-entry a representative can be rebound before the
duplicate definition is encountered again.  It is safe for executions starting
at the function entry because a use before the first execution of its unique
definition is stuck, but the present `LiveAgree`/`domCheck` API is
block-granular (`blockUses \\ blockDefs`) and does not expose that
reachable-execution / intra-block def-before-use fact.  The next required lemma
is therefore a history-sensitive strengthening saying that every substituted
use reached by an entry-rooted `Exec` has already crossed its unique `CseDef`
site (or an equivalent sequential-liveness lemma plus preservation around
backedges).  Without it the kept-op case cannot establish the substituted
argument read after a representative is rebound; this is independent of the
now-closed target-parameter inheritance case.

`BindingProvenance` now closes the "has already crossed its unique definition
site" half.  The exact remaining preservation step is the same as for
`elimTrivialParams_sound`: if a loop dynamically re-executes representative
`d0` after the last execution of dropped definition `d`, site provenance no
longer implies `R d = R' d0`.  `CseTabRuntime` can re-establish the equality at
the next dropped instruction, but a whole-function substitution may rewrite a
use before that point.  A binding-event/last-occurrence refinement of the
entry path must rule such a use out from a successful entry-rooted `Exec`; the
present invariant intentionally does not claim that unproved value fact. -/
theorem cse_sound {P : Prog} {f : Func} {args : List U256} {st : EvmState} {res : FRes}
    {eb eb' : Block} (hwf : f.wfCheck P.funcs.size = true)
    (hdom : ToAsm.Func.domCheck f = true)
    (heb : f.blocks[f.entry]? = some eb)
    (heb' : (Passes.cse f).blocks[f.entry]? = some eb')
    (hexec : Exec (model := model) P f (Regs.empty.setMany f.params args) st
      ⟨eb.instrs, eb.term⟩ res) :
    Exec (model := model) P (Passes.cse f) (Regs.empty.setMany f.params args) st
      ⟨eb'.instrs, eb'.term⟩ res := by
  sorry

/- **Pass 4 (dead value elimination) soundness.** No dominance hypothesis.

`sorry`: a simulation whose invariant is "`R` (original) and `R'` (optimized)
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
/-- Dominance preservation for one pipeline round, **proved** by composition of
the four obligations above. The three `wfCheck` hypotheses are the ones passes
1, 3, and 4 need; supplying them is what the (separate) well-formedness preservation
lemmas are for — `Correctness.optimizeProg_wf` gets the top-level version for
free from the gate. -/
theorem runOnce_dom {f : Func} {n : Nat} (hwf : f.wfCheck n = true)
    (hwf3 : (Passes.constFold (Passes.elimTrivialParams f)).wfCheck n = true)
    (hwf4 : (Passes.cse (Passes.constFold (Passes.elimTrivialParams f))).wfCheck n = true)
    (hdom : ToAsm.Func.domCheck f = true) :
    ToAsm.Func.domCheck (Passes.runOnce f) = true := by
  unfold Passes.runOnce
  exact dve_dom hwf4 (cse_dom hwf3 (constFold_dom (elimTrivialParams_dom hwf hdom)))

/-! ### The top-level statement -/

/-- **`SsaCfg.optimizeProg_sound`, reproduced verbatim** (post-fix signature:
`hwf` *and* `hdom`).

The defensive-fallback half is **proved** here; the remaining `sorry` is the
branch where the pipeline's output passes the gate, which is where the four
per-pass lemmas above (plus the simultaneous whole-program induction described in
this section's header) do their work.

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
    sorry
  · -- the gate rejected it: `optimizeProg` returned `P` unchanged
    simp only [Bool.not_eq_true] at hgate
    exact optimizeProg_sound_of_fallback hgate hrun

end YulEvmCompiler.SsaCfg
