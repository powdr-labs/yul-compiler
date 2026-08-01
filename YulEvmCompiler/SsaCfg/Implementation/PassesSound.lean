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
  the four per-pass obligations.
* The **counterexample**, end to end: `P.wfCheck = true`,
  `ToAsm.Prog.domCheck P = false`, `optimizeProg P = Popt` — the *whole*
  optimizer evaluated **inside the kernel**: `Passes.inlineProg` (proved to be
  the identity here, `hinline`: `P` has no `call`, so `siteCounts` is empty,
  `inlineOnce` finds nothing and `pruneFuncs` keeps everything), then three
  rounds of the four-pass pipeline, then the gate — plus
  `Run P yst yst .normal` and `¬ Run Popt yst yst .normal`.

## The remaining frontier

Thirteen `sorry`s, each documented at its declaration:

* pass 0 (inlining): `inlineOnce_sound`, `inlineFunc_sound`, `pruneFuncs_sound`,
  `inlineProg_sound`;
* passes 1–4: `elimTrivialParams_sound`, `constFold_sound`, `cse_sound`,
  `dve_sound`;
* dominance preservation: `elimTrivialParams_dom`, `constFold_dom`, `cse_dom`,
  `dve_dom` (`runOnce_dom` composes them and *is* proved);
* the gate-accepted branch of `optimizeProg_sound'`.

The recurring blocker is not semantic: it is that every pass is written as an
`Id.run` loop (`findTrivialParam`'s early-return search, the `cse` walk's
threaded `CseTab`/`Subst`, `inlineOnce`'s site search, `pruneFuncs`' worklist),
so each proof must first *invert* a monadic loop into a specification. The
semantic ingredients those specifications feed into — the frame lemma, the purity
leaves, the liveness fixed point with its propagation and least-fixed-point
lemmas, and the `LiveAgree` base case — are all proved here.
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

/-- `liveInSets` cannot fail on a program that passes the dominance check. -/
theorem liveInSets_isSome {f : Func} (hdom : Func.domCheck f = true) :
    ∃ li, liveInSets f = some li := by
  unfold Func.domCheck at hdom
  rcases h : liveInSets f with _ | li
  · rw [h] at hdom; exact absurd hdom (by simp)
  · exact ⟨li, rfl⟩

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
*proved* — it is the content of the `sorry`s below. -/

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
work-horses. The `.halt` case is the same derivation truncated. -/
theorem inlineOnce_sound {P : Prog} {counts : Array Nat} {f f' : Func} {args : List U256}
    {st : EvmState} {res : FRes} {eb eb' : Block}
    (hwf : f.wfCheck P.funcs.size = true)
    (hio : Passes.inlineOnce counts P.funcs f = some f')
    (heb : f.blocks[f.entry]? = some eb)
    (heb' : f'.blocks[f'.entry]? = some eb')
    (hexec : Exec (model := model) P f (Regs.empty.setMany f.params args) st
      ⟨eb.instrs, eb.term⟩ res) :
    Exec (model := model) P f' (Regs.empty.setMany f'.params args) st
      ⟨eb'.instrs, eb'.term⟩ res := by
  sorry

/-- **The budgeted fixed point preserves executions**: iterate
`inlineOnce_sound` at most eight times. `sorry` only because the loop inversion
(`for _ in [0:8]` with early return) still has to be threaded, exactly as in
`Counterexample.hinlineFunc`. -/
theorem inlineFunc_sound {P : Prog} {counts : Array Nat} {f : Func} {args : List U256}
    {st : EvmState} {res : FRes} {eb eb' : Block}
    (hwf : f.wfCheck P.funcs.size = true)
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

The remaining engineering is a *specification* for `Passes.findTrivialParam`:
inverting its nested `Id.run` early-return search into "every in-edge argument at
position `i` of block `bi` is `v` or `p`", and then an induction on the
fixed-point loop of `elimTrivialParams`. -/
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

/-- **Pass 2 (constant folding) soundness.** No dominance hypothesis.

`sorry`: needs the forward-walk invariant "for every `(d, v)` in the folder's
`consts` map, the register file maps `d` to `v` or leaves it unbound". That
invariant rests only on single assignment (`allDefs.Nodup` from `wfCheck`), which
makes the `const d v` instruction the *unique* binder of `d`, so any binding of
`d` in any reachable state is `v` — no dominance needed, which is why the
counterexample above leaves this pass alone. Its proof needs a `Nodup`-based
unique-definition-site lemma for `Func.allDefs` (the list plumbing is the bulk of
the work), after which each folded instruction is discharged by
`Passes.evalPure_transport` (proved) and each folded `branch` by inversion of
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

Remaining engineering: a specification for the `cse` walk (a stateful `Id.run`
fold over blocks accumulating `CseTab` and `σ`), i.e. "every `(op, args) ↦ d₀` in
the table at block `bi` was emitted by an instruction of a block that dominates
`bi`, and `σ`'s domain is disjoint from its range". -/
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

/-- **Pass 4 (dead value elimination) soundness.** No dominance hypothesis.

`sorry`: a simulation whose invariant is "`R` (original) and `R'` (optimized)
agree on every value in `Passes.liveSet f`", stepped with the frame lemma
`exec_congr`; the deleted instructions are exactly those whose destinations
nothing reads, so the invariant is preserved by construction and no dominance is
needed. The missing part is the liveness side of `Passes.liveSet` (a *forward*
`Std.HashSet` fixed point, distinct from `ToAsm.liveInSets` used by `domCheck`):
the proof needs (i) that the returned set is `Passes.liveStep`-closed — the fuel
loop exits on a *size* fixpoint and `liveStep` only ever inserts, so equal size
forces equal sets — and (ii) that closure implies "every value read by a kept
instruction, by a terminator, or through a live target parameter is in the set".
Plus the edge/parameter *alignment* lemma for dropped dead parameters: `dve`
masks parameters and in-edge arguments with the same predicate computed from the
**pre-pass** blocks, so `tb.params.length = args.length` survives. -/
theorem dve_sound {P : Prog} {f : Func} {args : List U256} {st : EvmState} {res : FRes}
    {eb eb' : Block} (hwf : f.wfCheck P.funcs.size = true)
    (heb : f.blocks[f.entry]? = some eb)
    (heb' : (Passes.dve f).blocks[f.entry]? = some eb')
    (hexec : Exec (model := model) P f (Regs.empty.setMany f.params args) st
      ⟨eb.instrs, eb.term⟩ res) :
    Exec (model := model) P (Passes.dve f) (Regs.empty.setMany f.params args) st
      ⟨eb'.instrs, eb'.term⟩ res := by
  sorry

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
theorem elimTrivialParams_dom {f : Func} (hwf : f.wfCheck n = true)
    (hdom : ToAsm.Func.domCheck f = true) :
    ToAsm.Func.domCheck (Passes.elimTrivialParams f) = true := by
  sorry

omit model in
theorem constFold_dom {f : Func} (hdom : ToAsm.Func.domCheck f = true) :
    ToAsm.Func.domCheck (Passes.constFold f) = true := by
  sorry

omit model in
theorem cse_dom {f : Func} (hwf : f.wfCheck n = true)
    (hdom : ToAsm.Func.domCheck f = true) :
    ToAsm.Func.domCheck (Passes.cse f) = true := by
  sorry

omit model in
theorem dve_dom {f : Func} (hdom : ToAsm.Func.domCheck f = true) :
    ToAsm.Func.domCheck (Passes.dve f) = true := by
  sorry

omit model in
/-- Dominance preservation for one pipeline round, **proved** by composition of
the four obligations above. The two `wfCheck` hypotheses are the ones passes 1
and 3 need; supplying them is what the (separate) well-formedness preservation
lemmas are for — `Correctness.optimizeProg_wf` gets the top-level version for
free from the gate. -/
theorem runOnce_dom {f : Func} {n : Nat} (hwf : f.wfCheck n = true)
    (hwf3 : (Passes.constFold (Passes.elimTrivialParams f)).wfCheck n = true)
    (hdom : ToAsm.Func.domCheck f = true) :
    ToAsm.Func.domCheck (Passes.runOnce f) = true := by
  unfold Passes.runOnce
  exact dve_dom (cse_dom hwf3 (constFold_dom (elimTrivialParams_dom hwf hdom)))

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
