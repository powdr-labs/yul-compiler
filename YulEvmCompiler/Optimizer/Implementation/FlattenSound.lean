import YulEvmCompiler.Optimizer.Implementation.Flatten
import YulEvmCompiler.Optimizer.Implementation.FuseDeclAssignSound
import YulEvmCompiler.Optimizer.Implementation.StackLayoutSound
set_option warningAsError true
/-!
# Soundness of block flattening — the rename transport

`Flatten.renameAll` renames each promoted binder `x` of a spliced block to a
globally fresh `x'`.  The guards (`shadowedTop`) ensure every occurrence of
`x` in the renamed sequence refers to the sequence's own top-level
declaration: `x` is not redeclared in any nested scope, is declared exactly
once at the top level, and is not mentioned before that declaration.  The
statements before the declaration therefore contain no `x` at all — renaming
leaves them **syntactically unchanged** — and from the declaration onward the
rename is a keyed environment bijection over the newer-than-entry segment.

`RnRel x x'` captures the environment shape during the renamed suffix:

* source: `C₁ ++ base`, target: `C₂ ++ base` with `C₂ = renKeys C₁`
  (every `x` key becomes `x'`, values equal, order preserved);
* `x'` occurs nowhere in the source code, so the source never reads or
  writes it; reads of `x`/`x'` resolve to corresponding entries; reads of
  other names agree (`renKeys` only changes `x` keys);
* the common `base` may bind both `x` (an outer shadow, unreachable from the
  renamed occurrences once the local declaration exists) and `x'`
  (unreachable from the source, and shadowed on the target).

The subtlety mirroring `MvRel`: `restore` is positional, and the segment/base
split is length-stable under execution, so block exits keep the relation.
-/

namespace YulEvmCompiler.Optimizer.Flatten

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler.Optimizer.FuseDeclAssign (set_append_of_found
  set_append_of_none)

variable {calls : ExternalCalls} {creates : ExternalCreates}
local notation "D" => evmWithExternal calls creates ExternalGas.any

/-! ### Keyed renaming of an environment segment -/

/-- Rename every `x` key to `x'` (values untouched). -/
def renKeys (x x' : Ident) (V : VEnv D) : VEnv D :=
  V.map (fun p => (renVar x x' p.1, p.2))

@[simp] theorem renKeys_nil (x x' : Ident) :
    renKeys (calls := calls) (creates := creates) x x' [] = [] := rfl

@[simp] theorem renKeys_cons (x x' : Ident)
    (p : Ident × (evmWithExternal calls creates .any).Value) (V : VEnv D) :
    renKeys x x' (p :: V) = (renVar x x' p.1, p.2) :: renKeys x x' V := rfl

@[simp] theorem renKeys_append (x x' : Ident) (V W : VEnv D) :
    renKeys x x' (V ++ W) = renKeys x x' V ++ renKeys x x' W := by
  simp [renKeys]

@[simp] theorem renKeys_length (x x' : Ident) (V : VEnv D) :
    (renKeys x x' V).length = V.length := by
  simp [renKeys]

/-- The environment relation for the renamed suffix: a rename-keyed newer
segment over a common base of pinned length `n`. The segment provably binds
`x` (the declaration executed) and never binds `x'` (globally fresh). -/
inductive RnRel (x x' : Ident) (n : Nat) : VEnv D → VEnv D → Prop
  | mk (C base : VEnv D)
      (hx : (C.find? (fun p => p.1 = x)).isSome)
      (hx' : ∀ p ∈ C, p.1 ≠ x')
      (hn : base.length = n) :
      RnRel x x' n (C ++ base) (renKeys x x' C ++ base)

theorem RnRel.length {x x' : Ident} {n : Nat} {V₁ V₂ : VEnv D}
    (h : RnRel x x' n V₁ V₂) : V₁.length = V₂.length := by
  cases h with
  | mk C base hx hx' hn => simp [renKeys]

/-- Push corresponding bindings (`y` is neither `x` nor `x'`). -/
theorem RnRel.push {x x' : Ident} {n : Nat} {V₁ V₂ : VEnv D}
    (h : RnRel x x' n V₁ V₂)
    {y : Ident} (hyx : y ≠ x) (hyx' : y ≠ x')
    (v : (evmWithExternal calls creates .any).Value) :
    RnRel x x' n ((y, v) :: V₁) ((y, v) :: V₂) := by
  cases h with
  | mk C base hx hx' hn =>
      have : (y, v) :: (renKeys x x' C ++ base) =
          renKeys x x' ((y, v) :: C) ++ base := by
        simp [renKeys, renVar, hyx]
      rw [this]
      refine RnRel.mk ((y, v) :: C) base ?_ ?_ hn
      · rw [List.find?_cons_of_neg (by simp [hyx])]
        exact hx
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp'
        · simpa using hyx'
        · exact hx' p hp'

/-- Push corresponding binding lists (pairwise `≠ x`, `≠ x'`). -/
theorem RnRel.pushMany {x x' : Ident} {n : Nat} {V₁ V₂ : VEnv D}
    (h : RnRel x x' n V₁ V₂)
    {ps : VEnv D} (hps : ∀ p ∈ ps, p.1 ≠ x ∧ p.1 ≠ x') :
    RnRel x x' n (ps ++ V₁) (ps ++ V₂) := by
  induction ps with
  | nil => exact h
  | cons p rest ih =>
      obtain ⟨p1, p2⟩ := p
      have := (ih (fun q hq => hps q (List.mem_cons_of_mem _ hq))).push
        (hps (p1, p2) (List.mem_cons_self ..)).1
        (hps (p1, p2) (List.mem_cons_self ..)).2 p2
      simpa using this

/-- Push the declaration itself: `x` on the source, `x'` on the target. -/
theorem RnRel.pushDecl {x x' : Ident} (hxx' : x ≠ x') {n : Nat}
    {C base : VEnv D}
    (hx' : ∀ p ∈ C, p.1 ≠ x') (hn : base.length = n)
    (v : (evmWithExternal calls creates .any).Value) :
    RnRel x x' n ((x, v) :: (C ++ base))
      ((x', v) :: (renKeys x x' C ++ base)) := by
  have : (x', v) :: (renKeys x x' C ++ base) =
      renKeys x x' ((x, v) :: C) ++ base := by
    simp [renKeys, renVar]
  rw [this]
  refine RnRel.mk ((x, v) :: C) base ?_ ?_ hn
  · rw [List.find?_cons_of_pos (by simp)]
    simp
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp'
    · simpa using hxx'
    · exact hx' p hp'

/-! ### `find?` facts about the keyed rename -/

theorem renKeys_find_x' {x x' : Ident} : ∀ {C : VEnv D}
    {p : Ident × (evmWithExternal calls creates .any).Value},
    C.find? (fun q => q.1 = x) = some p →
    (∀ q ∈ C, q.1 ≠ x') →
    (renKeys x x' C).find? (fun q => q.1 = x') = some (x', p.2)
  | [], p, hp, _ => by cases hp
  | q :: rest, p, hp, hx' => by
      by_cases hq : q.1 = x
      · rw [List.find?_cons_of_pos (by simp [hq])] at hp
        injection hp with hp'
        subst hp'
        rw [renKeys_cons, List.find?_cons_of_pos (by simp [renVar, hq])]
        simp [renVar, hq]
      · rw [List.find?_cons_of_neg (by simp [hq])] at hp
        rw [renKeys_cons, List.find?_cons_of_neg (by
          simp only [renVar, if_neg hq, decide_eq_true_eq]
          exact hx' q (List.mem_cons_self ..))]
        exact renKeys_find_x' hp (fun r hr => hx' r (List.mem_cons_of_mem _ hr))

theorem renKeys_find_x'_none {x x' : Ident} : ∀ {C : VEnv D},
    C.find? (fun q => q.1 = x) = none →
    (∀ q ∈ C, q.1 ≠ x') →
    (renKeys x x' C).find? (fun q => q.1 = x') = none
  | [], _, _ => rfl
  | q :: rest, hp, hx' => by
      by_cases hq : q.1 = x
      · rw [List.find?_cons_of_pos (by simp [hq])] at hp
        cases hp
      · rw [List.find?_cons_of_neg (by simp [hq])] at hp
        rw [renKeys_cons, List.find?_cons_of_neg (by
          simp only [renVar, if_neg hq, decide_eq_true_eq]
          exact hx' q (List.mem_cons_self ..))]
        exact renKeys_find_x'_none hp
          (fun r hr => hx' r (List.mem_cons_of_mem _ hr))

theorem renKeys_find_other {x x' y : Ident} (hyx : y ≠ x) (hyx' : y ≠ x') :
    ∀ {C : VEnv D},
    (renKeys x x' C).find? (fun q => q.1 = y) = C.find? (fun q => q.1 = y)
  | [] => rfl
  | q :: rest => by
      by_cases hq : q.1 = y
      · rw [List.find?_cons_of_pos (by simp [hq]), renKeys_cons,
          List.find?_cons_of_pos (by
            simp only [renVar, decide_eq_true_eq]
            rw [if_neg (by rw [hq]; exact hyx)]
            exact hq)]
        obtain ⟨q1, q2⟩ := q
        simp only at hq
        simp [renVar, show q1 ≠ x from by rw [hq]; exact hyx]
      · rw [List.find?_cons_of_neg (by simp [hq]), renKeys_cons,
          List.find?_cons_of_neg (by
            simp only [renVar, decide_eq_true_eq]
            split
            · exact fun hc => hyx' hc.symm
            · exact fun hc => hq hc)]
        exact renKeys_find_other hyx hyx'

/-- Key membership form of a successful keyed `find?`. -/
theorem find_key_isSome_iff {x : Ident} : ∀ {C : VEnv D},
    (C.find? (fun p => p.1 = x)).isSome ↔ x ∈ C.map Prod.fst := by
  intro C
  induction C with
  | nil => simp
  | cons q rest ih =>
      by_cases hq : q.1 = x
      · rw [List.find?_cons_of_pos (by simp [hq])]
        simp [hq]
      · rw [List.find?_cons_of_neg (by simp [hq])]
        simp only [List.map_cons, List.mem_cons]
        rw [ih]
        constructor
        · exact Or.inr
        · rintro (hc | hc)
          · exact absurd hc.symm hq
          · exact hc

/-- Keyed `find?` success survives `VEnv.set`. -/
theorem find_isSome_set {x y : Ident} {C : VEnv D}
    (hx : (C.find? (fun p => p.1 = x)).isSome)
    (v : (evmWithExternal calls creates .any).Value) :
    ((VEnv.set C y v).find? (fun p => p.1 = x)).isSome := by
  rw [find_key_isSome_iff, VEnv.set_keys («D» := D)]
  exact find_key_isSome_iff.mp hx

/-- Renaming commutes with an update to `x`/`x'` (the segment never binds
`x'`, so the target's first `x'` is the rename of the source's first `x`). -/
theorem renKeys_set_x {x x' : Ident}
    (v : (evmWithExternal calls creates .any).Value) : ∀ {C : VEnv D},
    (∀ q ∈ C, q.1 ≠ x') →
    VEnv.set (renKeys x x' C) x' v = renKeys x x' (VEnv.set C x v)
  | [], _ => rfl
  | (k, w) :: rest, hx' => by
      by_cases hk : k = x
      · subst hk
        simp [VEnv.set, renKeys, renVar]
      · have hkx' : k ≠ x' := hx' (k, w) (List.mem_cons_self ..)
        have ih := renKeys_set_x (x := x) (x' := x') v
          (fun q hq => hx' q (List.mem_cons_of_mem _ hq))
        rw [show VEnv.set ((k, w) :: rest) x v =
            (k, w) :: VEnv.set rest x v from by simp [VEnv.set, hk],
          renKeys_cons, renKeys_cons,
          show renVar x x' k = k from by simp [renVar, hk],
          show VEnv.set ((k, w) :: renKeys x x' rest) x' v =
            (k, w) :: VEnv.set (renKeys x x' rest) x' v from by
              simp [VEnv.set, hkx'],
          ih]

/-- Renaming commutes with an update to an unrelated name. -/
theorem renKeys_set_other {x x' y : Ident} (hyx : y ≠ x) (hyx' : y ≠ x')
    (v : (evmWithExternal calls creates .any).Value) : ∀ {C : VEnv D},
    (∀ q ∈ C, q.1 ≠ x') →
    VEnv.set (renKeys x x' C) y v = renKeys x x' (VEnv.set C y v)
  | [], _ => rfl
  | (k, w) :: rest, hx' => by
      have ih := renKeys_set_other (x := x) (x' := x') hyx hyx' v
        (fun q hq => hx' q (List.mem_cons_of_mem _ hq))
      by_cases hk : k = y
      · subst hk
        have hkx : k ≠ x := hyx
        rw [renKeys_cons, show renVar x x' k = k from by simp [renVar, hkx],
          show VEnv.set ((k, w) :: renKeys x x' rest) k v =
            (k, v) :: renKeys x x' rest from by simp [VEnv.set],
          show VEnv.set ((k, w) :: rest) k v = (k, v) :: rest from by
            simp [VEnv.set],
          renKeys_cons, show renVar x x' k = k from by simp [renVar, hkx]]
      · by_cases hkx : k = x
        · subst hkx
          rw [renKeys_cons, show renVar k x' k = x' from by simp [renVar],
            show VEnv.set ((x', w) :: renKeys k x' rest) y v =
              (x', w) :: VEnv.set (renKeys k x' rest) y v from by
                simp only [VEnv.set]
                rw [if_neg (fun hc : x' = y => hyx' hc.symm)],
            show VEnv.set ((k, w) :: rest) y v =
              (k, w) :: VEnv.set rest y v from by
                simp [VEnv.set, fun hc : k = y => hk hc],
            renKeys_cons, show renVar k x' k = x' from by simp [renVar], ih]
        · rw [renKeys_cons, show renVar x x' k = k from by simp [renVar, hkx],
            show VEnv.set ((k, w) :: renKeys x x' rest) y v =
              (k, w) :: VEnv.set (renKeys x x' rest) y v from by
                simp [VEnv.set, hk],
            show VEnv.set ((k, w) :: rest) y v =
              (k, w) :: VEnv.set rest y v from by simp [VEnv.set, hk],
            renKeys_cons, show renVar x x' k = k from by simp [renVar, hkx],
            ih]

/-! ### Reads and writes across the relation -/

/-- A source read of `x` matches a target read of `x'`. -/
theorem RnRel.get_x {x x' : Ident} {n : Nat} {V₁ V₂ : VEnv D}
    (h : RnRel x x' n V₁ V₂) :
    VEnv.get V₁ x = VEnv.get V₂ x' := by
  cases h with
  | mk C base hx hx' hn =>
      unfold VEnv.get
      simp only [List.find?_append]
      obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hx
      rw [hp, renKeys_find_x' hp hx']
      rfl

/-- A source read of `y ∉ {x, x'}` matches the target read of `y`. -/
theorem RnRel.get_other {x x' : Ident} {n : Nat} {V₁ V₂ : VEnv D}
    (h : RnRel x x' n V₁ V₂) {y : Ident} (hyx : y ≠ x) (hyx' : y ≠ x') :
    VEnv.get V₁ y = VEnv.get V₂ y := by
  cases h with
  | mk C base hx hx' hn =>
      unfold VEnv.get
      simp only [List.find?_append]
      rw [renKeys_find_other hyx hyx']

/-- Reads dispatched on the renamed name. -/
theorem RnRel.get_ren {x x' : Ident} {n : Nat} {V₁ V₂ : VEnv D}
    (h : RnRel x x' n V₁ V₂) {y : Ident} (hyx' : y ≠ x') :
    VEnv.get V₁ y = VEnv.get V₂ (renVar x x' y) := by
  by_cases hyx : y = x
  · subst hyx
    rw [show renVar y x' y = x' from by simp [renVar]]
    exact h.get_x
  · rw [show renVar x x' y = y from by simp [renVar, hyx]]
    exact h.get_other hyx hyx'

/-- A source write to `y` matches the target write to `renVar y`
(`y ≠ x'`: the source never mentions `x'`). -/
theorem RnRel.set_ren {x x' : Ident} {n : Nat} {V₁ V₂ : VEnv D}
    (h : RnRel x x' n V₁ V₂) {y : Ident} (hyx' : y ≠ x')
    (v : (evmWithExternal calls creates .any).Value) :
    RnRel x x' n (VEnv.set V₁ y v) (VEnv.set V₂ (renVar x x' y) v) := by
  cases h with
  | mk C base hx hx' hn =>
      by_cases hyx : y = x
      · subst hyx
        rw [show renVar y x' y = x' from by simp [renVar]]
        obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hx
        rw [set_append_of_found (by simp [hp]) v,
          set_append_of_found (by simp [renKeys_find_x' hp hx']) v,
          renKeys_set_x v hx']
        refine RnRel.mk (VEnv.set C y v) base (find_isSome_set hx v) ?_ hn
        intro p hp
        obtain ⟨q, hq, hqe⟩ :=
          YulEvmCompiler.Optimizer.FuseDeclAssign.mem_set_key hp
        rw [← hqe]
        exact hx' q hq
      · rw [show renVar x x' y = y from by simp [renVar, hyx]]
        cases hC : C.find? (fun q => q.1 = y) with
        | some p =>
            rw [set_append_of_found (by simp [hC]) v,
              set_append_of_found (by
                simp [renKeys_find_other hyx hyx', hC]) v,
              renKeys_set_other hyx hyx' v hx']
            refine RnRel.mk (VEnv.set C y v) base (find_isSome_set hx v) ?_ hn
            intro p hp
            obtain ⟨q, hq, hqe⟩ :=
              YulEvmCompiler.Optimizer.FuseDeclAssign.mem_set_key hp
            rw [← hqe]
            exact hx' q hq
        | none =>
            rw [set_append_of_none hC v,
              set_append_of_none (by rw [renKeys_find_other hyx hyx']; exact hC) v]
            exact RnRel.mk C (VEnv.set base y v) hx hx'
              (by rw [VEnv.set_length («D» := D)]; exact hn)

/-- Source `setMany` matches target `setMany` on the renamed targets. -/
theorem RnRel.setMany_ren {x x' : Ident} {n : Nat} :
    ∀ {ys : List Ident} {V₁ V₂ : VEnv D},
    RnRel x x' n V₁ V₂ →
    (∀ y ∈ ys, y ≠ x') →
    ∀ (vs : List (evmWithExternal calls creates .any).Value),
    RnRel x x' n (VEnv.setMany V₁ ys vs)
      (VEnv.setMany V₂ (ys.map (renVar x x')) vs)
  | [], V₁, V₂, h, _, vs => by
      simpa [VEnv.setMany] using h
  | y :: ys, V₁, V₂, h, hys, [] => by
      simpa [VEnv.setMany] using h
  | y :: ys, V₁, V₂, h, hys, v :: vs => by
      have h1 := h.set_ren (hys y (List.mem_cons_self ..)) v
      have := RnRel.setMany_ren (ys := ys) h1
        (fun z hz => hys z (List.mem_cons_of_mem _ hz)) vs
      simpa [VEnv.setMany] using this

/-! ### `restore` compatibility -/

theorem renKeys_drop (x x' : Ident) (k : Nat) (C : VEnv D) :
    (renKeys x x' C).drop k = renKeys x x' (C.drop k) := by
  simp [renKeys, List.map_drop]

/-- Related exits restore (to related entries) to related environments; the
source keys-suffix fact pins the cut to the segment. -/
theorem RnRel.restore_compat {x x' : Ident} {n : Nat}
    {Ve₁ Ve₂ Vb₁ Vb₂ : VEnv D}
    (hentry : RnRel x x' n Ve₁ Ve₂) (hexit : RnRel x x' n Vb₁ Vb₂)
    (hgrow : Ve₁.length ≤ Vb₁.length)
    (hkeys : Ve₁.map Prod.fst <:+ Vb₁.map Prod.fst) :
    RnRel x x' n (restore Ve₁ Vb₁) (restore Ve₂ Vb₂) := by
  obtain ⟨Ce, base, hxe, hx'e, hne⟩ := hentry
  obtain ⟨C', base', hx, hx', hn'⟩ := hexit
  have hCe : Ce.length ≤ C'.length := by
    simp only [List.length_append] at hgrow
    omega
  set k := C'.length - Ce.length with hk
  have hdrop₁ : restore (Ce ++ base) (C' ++ base') = C'.drop k ++ base' := by
    unfold restore
    have : (C' ++ base').length - (Ce ++ base).length = k := by
      simp [List.length_append]; omega
    rw [this, List.drop_append_of_le_length (by omega)]
  have hdrop₂ : restore (renKeys x x' Ce ++ base)
      (renKeys x x' C' ++ base') = renKeys x x' (C'.drop k) ++ base' := by
    unfold restore
    have : (renKeys x x' C' ++ base').length -
        (renKeys x x' Ce ++ base).length = k := by
      simp [List.length_append, renKeys]; omega
    rw [this, List.drop_append_of_le_length (by simp [renKeys]; omega),
      renKeys_drop]
  rw [hdrop₁, hdrop₂]
  -- The kept segment's keys are the entry segment's keys.
  obtain ⟨pre, hpre⟩ := hkeys
  have hprelen : pre.length = k := by
    have := congrArg List.length hpre
    simp only [List.length_append, List.length_map] at this
    omega
  have hsplit : C'.map Prod.fst = pre ++ Ce.map Prod.fst := by
    have h1 : C'.map Prod.fst ++ base'.map Prod.fst =
        (pre ++ Ce.map Prod.fst) ++ base.map Prod.fst := by
      have := hpre
      simp only [List.map_append] at this
      rw [← this]
      simp [List.append_assoc]
    have hlen : (C'.map Prod.fst).length =
        (pre ++ Ce.map Prod.fst).length := by
      simp only [List.length_append, List.length_map]
      omega
    exact (List.append_inj h1 hlen).1
  have hkeep : (C'.drop k).map Prod.fst = Ce.map Prod.fst := by
    rw [List.map_drop, hsplit,
      show k = pre.length from hprelen.symm,
      show pre.length = pre.length + 0 from by omega, List.drop_append]
    simp
  refine RnRel.mk (C'.drop k) base' ?_ ?_ hn'
  · rw [find_key_isSome_iff, hkeep]
    exact find_key_isSome_iff.mp hxe
  · intro p hp
    exact hx' p (List.mem_of_mem_drop hp)

/-! ### Frame-level mentions, skipping `funDef`s

The transport's freshness side condition only protects *executing* frames:
reads, writes, and binders at the statement level. `funDef` statements are
execution-inert and their bodies run in fresh callee environments, so they
are excluded — which is exactly what lets the backward transport reuse the
forward one with the rename's roles swapped (the renamed code may still
mention the old name inside unrenamed function bodies). -/

mutual
def rnMStmt (z : Ident) : Stmt Op → Bool
  | .block body => rnMStmts z body
  | .funDef _ _ _ _ => false
  | .letDecl vars val => (z ∈ vars) || optExprMentions z val
  | .assign vars val => (z ∈ vars) || exprMentions z val
  | .cond c body => exprMentions z c || rnMStmts z body
  | .switch c cases dflt =>
      exprMentions z c || rnMCases z cases || rnMDflt z dflt
  | .forLoop init c post body =>
      rnMStmts z init || exprMentions z c || rnMStmts z post ||
        rnMStmts z body
  | .exprStmt e => exprMentions z e
  | .«break» => false
  | .«continue» => false
  | .leave => false

def rnMStmts (z : Ident) : List (Stmt Op) → Bool
  | [] => false
  | s :: rest => rnMStmt z s || rnMStmts z rest

def rnMCases (z : Ident) : List (Literal × List (Stmt Op)) → Bool
  | [] => false
  | (_, b) :: rest => rnMStmts z b || rnMCases z rest

def rnMDflt (z : Ident) : Option (List (Stmt Op)) → Bool
  | some b => rnMStmts z b
  | none => false
end

def rnMCode (z : Ident) : Code Op → Bool
  | .expr e => exprMentions z e
  | .args es => argsMentions z es
  | .stmt s => rnMStmt z s
  | .stmts ss => rnMStmts z ss
  | .loop c post body =>
      exprMentions z c || rnMStmts z post || rnMStmts z body

/-- The selected switch block inherits mention-freeness. -/
theorem selectSwitch_not_rnM {z : Ident} {cv : U256}
    {cases : List (Literal × Block Op)} {dflt : Option (Block Op)}
    (hcs : rnMCases z cases = false) (hd : rnMDflt z dflt = false) :
    rnMStmts z (selectSwitch D cv cases dflt) = false := by
  unfold selectSwitch
  cases hfind : cases.find? (fun p => decide (cv = Dialect.litValue D p.1)) with
  | none =>
      cases dflt with
      | none => rfl
      | some b => exact hd
  | some p =>
      have hmem := List.mem_of_find?_eq_some hfind
      revert hcs
      clear hfind
      induction cases with
      | nil => intro _; cases hmem
      | cons q rest ih =>
          intro hcs
          simp only [rnMCases, Bool.or_eq_false_iff] at hcs
          rcases List.mem_cons.mp hmem with rfl | hmem'
          · exact hcs.1
          · exact ih hmem' hcs.2

/-! ### The rename on code, and its side conditions -/

/-- The rename lifted to the five code classes. -/
def renCode (x x' : Ident) : Code Op → Code Op
  | .expr e => .expr (renExpr x x' e)
  | .args es => .args (renArgs x x' es)
  | .stmt s => .stmt (renStmt x x' s)
  | .stmts ss => .stmts (renStmts x x' ss)
  | .loop c post body =>
      .loop (renExpr x x' c) (renStmts x x' post) (renStmts x x' body)

/-- Does the code declare `x` anywhere (excluding `funDef` bodies)? -/
def codeRedecl (x : Ident) : Code Op → Bool
  | .expr _ => false
  | .args _ => false
  | .stmt s => redeclStmt x s
  | .stmts ss => redeclStmts x ss
  | .loop _ post body => redeclStmts x post || redeclStmts x body

/-- Renaming never touches function definitions, so hoisting is stable. -/
theorem renStmts_hoist (x x' : Ident) : ∀ (ss : List (Stmt Op)),
    hoist D (renStmts x x' ss) = hoist D ss
  | [] => rfl
  | s :: rest => by
      have ih := renStmts_hoist x x' rest
      unfold hoist at ih ⊢
      rw [show renStmts x x' (s :: rest) =
        renStmt x x' s :: renStmts x x' rest from rfl,
        List.filterMap_cons, List.filterMap_cons]
      cases s <;> simp [renStmt, ih]

/-- Renaming commutes with switch-case selection (labels are untouched). -/
theorem selectSwitch_ren (x x' : Ident) (cv : U256) :
    ∀ (cases : List (Literal × Block Op)) (dflt : Option (Block Op)),
    selectSwitch D cv (renCases x x' cases) (renDflt x x' dflt) =
      renStmts x x' (selectSwitch D cv cases dflt) := by
  intro cases dflt
  unfold selectSwitch
  induction cases with
  | nil =>
      simp only [renCases, List.find?_nil]
      cases dflt with
      | none => rfl
      | some b => rfl
  | cons p rest ih =>
      obtain ⟨l, b⟩ := p
      by_cases hl : cv = Dialect.litValue D l
      · rw [show renCases x x' ((l, b) :: rest) =
          (l, renStmts x x' b) :: renCases x x' rest from rfl,
          List.find?_cons_of_pos (by simpa using hl),
          List.find?_cons_of_pos (by simpa using hl)]
      · rw [show renCases x x' ((l, b) :: rest) =
          (l, renStmts x x' b) :: renCases x x' rest from rfl,
          List.find?_cons_of_neg (by simpa using hl),
          List.find?_cons_of_neg (by simpa using hl)]
        exact ih

/-- The selected block of redecl-free cases/default is redecl-free. -/
theorem selectSwitch_not_redecl {x : Ident} {cv : U256}
    {cases : List (Literal × Block Op)} {dflt : Option (Block Op)}
    (hcs : redeclCases x cases = false) (hd : redeclDflt x dflt = false) :
    redeclStmts x (selectSwitch D cv cases dflt) = false := by
  unfold selectSwitch
  cases hfind : cases.find? (fun p => decide (cv = Dialect.litValue D p.1)) with
  | none =>
      cases dflt with
      | none => rfl
      | some b => exact hd
  | some p =>
      have hmem := List.mem_of_find?_eq_some hfind
      revert hcs
      clear hfind
      induction cases with
      | nil => intro _; cases hmem
      | cons q rest ih =>
          intro hcs
          simp only [redeclCases, Bool.or_eq_false_iff] at hcs
          rcases List.mem_cons.mp hmem with rfl | hmem'
          · exact hcs.1
          · exact ih hmem' hcs.2

/-- Names left fixed by the rename map to themselves, listwise. -/
theorem map_renVar_id {x x' : Ident} {ys : List Ident}
    (h : ∀ y ∈ ys, y ≠ x) : ys.map (renVar x x') = ys := by
  induction ys with
  | nil => rfl
  | cons y rest ih =>
      simp only [List.map_cons, renVar,
        if_neg (h y (List.mem_cons_self ..))]
      rw [ih (fun z hz => h z (List.mem_cons_of_mem _ hz))]

/-! ### The result relation and the transport -/

inductive RnRes (x x' : Ident) (n : Nat) : Res D → Res D → Prop
  | eres (r : EResult D) : RnRes x x' n (.eres r) (.eres r)
  | sres {V₁ V₂ : VEnv D} (st : EvmState) (o : Outcome)
      (h : RnRel x x' n V₁ V₂) :
      RnRes x x' n (.sres V₁ st o) (.sres V₂ st o)

theorem RnRes.eres_inv {x x' : Ident} {n : Nat} {r : EResult D} {res₂ : Res D}
    (h : RnRes x x' n (.eres r) res₂) : res₂ = .eres r := by
  cases h; rfl

theorem RnRes.sres_inv {x x' : Ident} {n : Nat} {V₁ : VEnv D} {st o}
    {res₂ : Res D} (h : RnRes x x' n (.sres V₁ st o) res₂) :
    ∃ V₂, res₂ = .sres V₂ st o ∧ RnRel x x' n V₁ V₂ := by
  cases h with
  | sres _ _ hrel => exact ⟨_, rfl, hrel⟩

set_option maxHeartbeats 3200000 in
/-- **The rename transport**: a source derivation yields one for the renamed
code over a rename-related environment, provided the source never mentions
`x'` and never declares `x` (outside `funDef` bodies). Function environments
are literally shared: the rename skips definitions, and callee bodies run in
fresh environments. -/
theorem Step.rn_congr {x x' : Ident} {n : Nat}
    {funs : FunEnv D} {V₁ : VEnv D} {st : EvmState} {code : Code Op}
    {res₁ : Res D}
    (h : Step D funs V₁ st code res₁) :
    ∀ {V₂}, RnRel x x' n V₁ V₂ →
      rnMCode x' code = false →
      codeRedecl x code = false →
      ∃ res₂, Step D funs V₂ st (renCode x x' code) res₂ ∧
        RnRes x x' n res₁ res₂ := by
  induction h with
  | lit => intro _ _ _ _; exact ⟨_, Step.lit, .eres _⟩
  | @var _ _ _ y v hv =>
      intro V₂ hR hm _
      refine ⟨_, Step.var ?_, .eres _⟩
      rw [← hR.get_ren (by
        simp only [rnMCode, exprMentions, decide_eq_false_iff_not] at hm
        exact fun hc => hm hc.symm)]
      exact hv
  | builtinOk ha hb iha =>
      intro V₂ hR hm hd
      obtain ⟨r₂, h₂, hrel⟩ := iha hR
        (by simpa [rnMCode, exprMentions] using hm) rfl
      rw [hrel.eres_inv] at h₂
      exact ⟨_, Step.builtinOk h₂ hb, .eres _⟩
  | builtinHalt ha hb iha =>
      intro V₂ hR hm hd
      obtain ⟨r₂, h₂, hrel⟩ := iha hR
        (by simpa [rnMCode, exprMentions] using hm) rfl
      rw [hrel.eres_inv] at h₂
      exact ⟨_, Step.builtinHalt h₂ hb, .eres _⟩
  | builtinArgsHalt ha iha =>
      intro V₂ hR hm hd
      obtain ⟨r₂, h₂, hrel⟩ := iha hR
        (by simpa [rnMCode, exprMentions] using hm) rfl
      rw [hrel.eres_inv] at h₂
      exact ⟨_, Step.builtinArgsHalt h₂, .eres _⟩
  | callOk ha hl hlen hbody ho iha ihbody =>
      intro V₂ hR hm hd
      obtain ⟨r₂, h₂, hrel⟩ := iha hR
        (by simpa [rnMCode, exprMentions] using hm) rfl
      rw [hrel.eres_inv] at h₂
      exact ⟨_, Step.callOk h₂ hl hlen hbody ho, .eres _⟩
  | callHalt ha hl hlen hbody iha ihbody =>
      intro V₂ hR hm hd
      obtain ⟨r₂, h₂, hrel⟩ := iha hR
        (by simpa [rnMCode, exprMentions] using hm) rfl
      rw [hrel.eres_inv] at h₂
      exact ⟨_, Step.callHalt h₂ hl hlen hbody, .eres _⟩
  | callArgsHalt ha iha =>
      intro V₂ hR hm hd
      obtain ⟨r₂, h₂, hrel⟩ := iha hR
        (by simpa [rnMCode, exprMentions] using hm) rfl
      rw [hrel.eres_inv] at h₂
      exact ⟨_, Step.callArgsHalt h₂, .eres _⟩
  | argsNil => intro _ _ _ _; exact ⟨_, Step.argsNil, .eres _⟩
  | argsCons ha he iha ihe =>
      intro V₂ hR hm hd
      simp only [rnMCode, argsMentions, Bool.or_eq_false_iff] at hm
      obtain ⟨r₂, h₂, hrel⟩ := iha hR (by simpa [rnMCode] using hm.2) rfl
      rw [hrel.eres_inv] at h₂
      obtain ⟨r₃, h₃, hrel'⟩ := ihe hR (by simpa [rnMCode] using hm.1) rfl
      rw [hrel'.eres_inv] at h₃
      exact ⟨_, Step.argsCons h₂ h₃, .eres _⟩
  | argsRestHalt ha iha =>
      intro V₂ hR hm hd
      simp only [rnMCode, argsMentions, Bool.or_eq_false_iff] at hm
      obtain ⟨r₂, h₂, hrel⟩ := iha hR (by simpa [rnMCode] using hm.2) rfl
      rw [hrel.eres_inv] at h₂
      exact ⟨_, Step.argsRestHalt h₂, .eres _⟩
  | argsHeadHalt ha he iha ihe =>
      intro V₂ hR hm hd
      simp only [rnMCode, argsMentions, Bool.or_eq_false_iff] at hm
      obtain ⟨r₂, h₂, hrel⟩ := iha hR (by simpa [rnMCode] using hm.2) rfl
      rw [hrel.eres_inv] at h₂
      obtain ⟨r₃, h₃, hrel'⟩ := ihe hR (by simpa [rnMCode] using hm.1) rfl
      rw [hrel'.eres_inv] at h₃
      exact ⟨_, Step.argsHeadHalt h₂ h₃, .eres _⟩
  | funDef => intro V₂ hR _ _; exact ⟨_, Step.funDef, .sres _ _ hR⟩
  | @block _ V _ body Vb stb o hbody ihbody =>
      intro V₂ hR hm hd
      simp only [rnMCode, rnMStmt] at hm
      simp only [codeRedecl, redeclStmt] at hd
      obtain ⟨r₂, h₂, hrel⟩ := ihbody hR
        (by simpa [rnMCode] using hm)
        (by simpa [codeRedecl] using hd)
      obtain ⟨Vb₂, rfl, hrel'⟩ := hrel.sres_inv
      exact ⟨_, Step.block (by rwa [renStmts_hoist]), .sres _ _
        (hR.restore_compat hrel' (venvLen_mono hbody rfl)
          (venvKeys_suffix hbody rfl))⟩
  | @letZero _ V _ vars =>
      intro V₂ hR hm hd
      simp only [rnMCode, rnMStmt, Bool.or_eq_false_iff,
        decide_eq_false_iff_not] at hm
      simp only [codeRedecl, redeclStmt] at hd
      have hxv : ∀ y ∈ vars, y ≠ x := by
        intro y hy hc
        subst hc
        rw [List.contains_eq_mem] at hd
        simp [hy] at hd
      have hx'v : ∀ y ∈ vars, y ≠ x' := by
        intro y hy hc
        subst hc
        exact hm.1 hy
      refine ⟨_, ?_, .sres _ _ (hR.pushMany (ps := bindZeros _ vars) ?_)⟩
      · have hmap : vars.map (renVar x x') = vars := map_renVar_id hxv
        show Step D _ _ _ (.stmt (.letDecl (vars.map (renVar x x')) none)) _
        rw [hmap]
        exact Step.letZero
      · intro p hp
        have hkey : p.1 ∈ vars := by
          simp only [bindZeros, List.mem_map] at hp
          obtain ⟨y, hy, rfl⟩ := hp
          exact hy
        exact ⟨hxv p.1 hkey, hx'v p.1 hkey⟩
  | @letVal _ V _ vars e vals st1 he hlen ihe =>
      intro V₂ hR hm hd
      simp only [rnMCode, rnMStmt, Bool.or_eq_false_iff,
        decide_eq_false_iff_not] at hm
      simp only [codeRedecl, redeclStmt] at hd
      have hxv : ∀ y ∈ vars, y ≠ x := by
        intro y hy hc
        subst hc
        rw [List.contains_eq_mem] at hd
        simp [hy] at hd
      have hx'v : ∀ y ∈ vars, y ≠ x' := by
        intro y hy hc
        subst hc
        exact hm.1 hy
      obtain ⟨r₂, h₂, hrel⟩ := ihe hR
        (by simpa [rnMCode, optExprMentions] using hm.2) rfl
      rw [hrel.eres_inv] at h₂
      refine ⟨_, ?_, .sres _ _ (hR.pushMany (ps := vars.zip vals) ?_)⟩
      · have hmap : vars.map (renVar x x') = vars := map_renVar_id hxv
        show Step D _ _ _
          (Code.stmt (Stmt.letDecl (vars.map (renVar x x'))
            (some (renExpr x x' e)))) _
        rw [hmap]
        exact Step.letVal h₂ hlen
      · intro p hp
        have hkey : p.1 ∈ vars := by
          have := List.of_mem_zip hp
          exact this.1
        exact ⟨hxv p.1 hkey, hx'v p.1 hkey⟩
  | letHalt he ihe =>
      intro V₂ hR hm hd
      simp only [rnMCode, rnMStmt, Bool.or_eq_false_iff] at hm
      obtain ⟨r₂, h₂, hrel⟩ := ihe hR
        (by simpa [rnMCode, optExprMentions] using hm.2) rfl
      rw [hrel.eres_inv] at h₂
      exact ⟨_, Step.letHalt h₂, .sres _ _ hR⟩
  | assignVal he hlen ihe =>
      intro V₂ hR hm hd
      simp only [rnMCode, rnMStmt, Bool.or_eq_false_iff,
        decide_eq_false_iff_not] at hm
      obtain ⟨r₂, h₂, hrel⟩ := ihe hR
        (by simpa [rnMCode] using hm.2) rfl
      rw [hrel.eres_inv] at h₂
      refine ⟨_, Step.assignVal h₂ (by simpa using hlen), .sres _ _ ?_⟩
      exact hR.setMany_ren (fun y hy hc => hm.1 (hc ▸ hy)) _
  | assignHalt he ihe =>
      intro V₂ hR hm hd
      simp only [rnMCode, rnMStmt, Bool.or_eq_false_iff] at hm
      obtain ⟨r₂, h₂, hrel⟩ := ihe hR
        (by simpa [rnMCode] using hm.2) rfl
      rw [hrel.eres_inv] at h₂
      exact ⟨_, Step.assignHalt h₂, .sres _ _ hR⟩
  | exprStmt he ihe =>
      intro V₂ hR hm hd
      obtain ⟨r₂, h₂, hrel⟩ := ihe hR
        (by simpa [rnMCode, rnMStmt] using hm) rfl
      rw [hrel.eres_inv] at h₂
      exact ⟨_, Step.exprStmt h₂, .sres _ _ hR⟩
  | exprStmtHalt he ihe =>
      intro V₂ hR hm hd
      obtain ⟨r₂, h₂, hrel⟩ := ihe hR
        (by simpa [rnMCode, rnMStmt] using hm) rfl
      rw [hrel.eres_inv] at h₂
      exact ⟨_, Step.exprStmtHalt h₂, .sres _ _ hR⟩
  | ifTrue hc hnz hb ihc ihb =>
      intro V₂ hR hm hd
      simp only [rnMCode, rnMStmt, Bool.or_eq_false_iff] at hm
      simp only [codeRedecl, redeclStmt] at hd
      obtain ⟨r₂, h₂, hrel⟩ := ihc hR (by simpa [rnMCode] using hm.1) rfl
      rw [hrel.eres_inv] at h₂
      obtain ⟨r₃, h₃, hrel'⟩ := ihb hR
        (by simpa [rnMCode, rnMStmt] using hm.2)
        (by simpa [codeRedecl, redeclStmt] using hd)
      obtain ⟨Vb₂, rfl, hrel''⟩ := hrel'.sres_inv
      exact ⟨_, Step.ifTrue h₂ hnz h₃, .sres _ _ hrel''⟩
  | ifFalse hc hz ihc =>
      intro V₂ hR hm hd
      simp only [rnMCode, rnMStmt, Bool.or_eq_false_iff] at hm
      obtain ⟨r₂, h₂, hrel⟩ := ihc hR (by simpa [rnMCode] using hm.1) rfl
      rw [hrel.eres_inv] at h₂
      exact ⟨_, Step.ifFalse h₂ hz, .sres _ _ hR⟩
  | ifHalt hc ihc =>
      intro V₂ hR hm hd
      simp only [rnMCode, rnMStmt, Bool.or_eq_false_iff] at hm
      obtain ⟨r₂, h₂, hrel⟩ := ihc hR (by simpa [rnMCode] using hm.1) rfl
      rw [hrel.eres_inv] at h₂
      exact ⟨_, Step.ifHalt h₂, .sres _ _ hR⟩
  | switchExec hc hb ihc ihb =>
      intro V₂ hR hm hd
      simp only [rnMCode, rnMStmt, Bool.or_eq_false_iff] at hm
      simp only [codeRedecl, redeclStmt, Bool.or_eq_false_iff] at hd
      obtain ⟨r₂, h₂, hrel⟩ := ihc hR
        (by simpa [rnMCode] using hm.1.1) rfl
      rw [hrel.eres_inv] at h₂
      obtain ⟨r₃, h₃, hrel'⟩ := ihb hR
        (by
          simp only [rnMCode, rnMStmt]
          exact selectSwitch_not_rnM hm.1.2 hm.2)
        (by
          simp only [codeRedecl, redeclStmt]
          exact selectSwitch_not_redecl hd.1 hd.2)
      obtain ⟨Vb₂, rfl, hrel''⟩ := hrel'.sres_inv
      refine ⟨_, Step.switchExec h₂ ?_, .sres _ _ hrel''⟩
      rw [selectSwitch_ren]
      exact h₃
  | switchHalt hc ihc =>
      intro V₂ hR hm hd
      simp only [rnMCode, rnMStmt, Bool.or_eq_false_iff] at hm
      obtain ⟨r₂, h₂, hrel⟩ := ihc hR
        (by simpa [rnMCode] using hm.1.1) rfl
      rw [hrel.eres_inv] at h₂
      exact ⟨_, Step.switchHalt h₂, .sres _ _ hR⟩
  | @forLoop _ V _ init c post body Vinit stinit Vend stend o hinit hloop ihinit ihloop =>
      intro V₂ hR hm hd
      simp only [rnMCode, rnMStmt, Bool.or_eq_false_iff] at hm
      simp only [codeRedecl, redeclStmt, Bool.or_eq_false_iff] at hd
      obtain ⟨r₂, h₂, hrel⟩ := ihinit hR
        (by simpa [rnMCode] using hm.1.1.1)
        (by simpa [codeRedecl] using hd.1.1)
      obtain ⟨Vi₂, rfl, hrel'⟩ := hrel.sres_inv
      obtain ⟨r₃, h₃, hrel₂⟩ := ihloop hrel'
        (by
          simp only [rnMCode, Bool.or_eq_false_iff]
          exact ⟨⟨hm.1.1.2, hm.1.2⟩, hm.2⟩)
        (by
          simp only [codeRedecl, Bool.or_eq_false_iff]
          exact ⟨hd.1.2, hd.2⟩)
      obtain ⟨Ve₂, rfl, hrel₃⟩ := hrel₂.sres_inv
      exact ⟨_, Step.forLoop (by rwa [renStmts_hoist])
          (by rwa [renStmts_hoist]), .sres _ _
        (hR.restore_compat hrel₃
          (Nat.le_trans (venvLen_mono hinit rfl) (venvLen_mono hloop rfl))
          ((venvKeys_suffix hinit rfl).trans (venvKeys_suffix hloop rfl)))⟩
  | @forInitHalt _ V _ init c post body Vinit stinit hinit ihinit =>
      intro V₂ hR hm hd
      simp only [rnMCode, rnMStmt, Bool.or_eq_false_iff] at hm
      simp only [codeRedecl, redeclStmt, Bool.or_eq_false_iff] at hd
      obtain ⟨r₂, h₂, hrel⟩ := ihinit hR
        (by simpa [rnMCode] using hm.1.1.1)
        (by simpa [codeRedecl] using hd.1.1)
      obtain ⟨Vi₂, rfl, hrel'⟩ := hrel.sres_inv
      exact ⟨_, Step.forInitHalt (by rwa [renStmts_hoist]), .sres _ _
        (hR.restore_compat hrel' (venvLen_mono hinit rfl)
          (venvKeys_suffix hinit rfl))⟩
  | «break» => intro V₂ hR _ _; exact ⟨_, Step.break, .sres _ _ hR⟩
  | «continue» => intro V₂ hR _ _; exact ⟨_, Step.continue, .sres _ _ hR⟩
  | «leave» => intro V₂ hR _ _; exact ⟨_, Step.leave, .sres _ _ hR⟩
  | seqNil => intro V₂ hR _ _; exact ⟨_, Step.seqNil, .sres _ _ hR⟩
  | seqCons hs hrest ihs ihrest =>
      intro V₂ hR hm hd
      simp only [rnMCode, rnMStmts, Bool.or_eq_false_iff] at hm
      simp only [codeRedecl, redeclStmts, Bool.or_eq_false_iff] at hd
      obtain ⟨r₂, h₂, hrel⟩ := ihs hR
        (by simpa [rnMCode] using hm.1)
        (by simpa [codeRedecl] using hd.1)
      obtain ⟨V₂', rfl, hrel'⟩ := hrel.sres_inv
      obtain ⟨r₃, h₃, hrel₂⟩ := ihrest hrel'
        (by simpa [rnMCode] using hm.2)
        (by simpa [codeRedecl] using hd.2)
      obtain ⟨V₂'', rfl, hrel₃⟩ := hrel₂.sres_inv
      exact ⟨_, Step.seqCons h₂ h₃, .sres _ _ hrel₃⟩
  | seqStop hs hne ihs =>
      intro V₂ hR hm hd
      simp only [rnMCode, rnMStmts, Bool.or_eq_false_iff] at hm
      simp only [codeRedecl, redeclStmts, Bool.or_eq_false_iff] at hd
      obtain ⟨r₂, h₂, hrel⟩ := ihs hR
        (by simpa [rnMCode] using hm.1)
        (by simpa [codeRedecl] using hd.1)
      obtain ⟨V₂', rfl, hrel'⟩ := hrel.sres_inv
      exact ⟨_, Step.seqStop h₂ hne, .sres _ _ hrel'⟩
  | loopDone hc hz ihc =>
      intro V₂ hR hm hd
      simp only [rnMCode, Bool.or_eq_false_iff] at hm
      obtain ⟨r₂, h₂, hrel⟩ := ihc hR
        (by simpa [rnMCode] using hm.1.1) rfl
      rw [hrel.eres_inv] at h₂
      exact ⟨_, Step.loopDone h₂ hz, .sres _ _ hR⟩
  | loopCondHalt hc ihc =>
      intro V₂ hR hm hd
      simp only [rnMCode, Bool.or_eq_false_iff] at hm
      obtain ⟨r₂, h₂, hrel⟩ := ihc hR
        (by simpa [rnMCode] using hm.1.1) rfl
      rw [hrel.eres_inv] at h₂
      exact ⟨_, Step.loopCondHalt h₂, .sres _ _ hR⟩
  | loopStep hc hnz hb hob hp hr ihc ihb ihp ihr =>
      intro V₂ hR hm hd
      simp only [rnMCode, Bool.or_eq_false_iff] at hm
      simp only [codeRedecl, Bool.or_eq_false_iff] at hd
      obtain ⟨r₂, h₂, hrel⟩ := ihc hR
        (by simpa [rnMCode] using hm.1.1) rfl
      rw [hrel.eres_inv] at h₂
      obtain ⟨r₃, h₃, hrelB⟩ := ihb hR
        (by simpa [rnMCode, rnMStmt] using hm.2)
        (by simpa [codeRedecl, redeclStmt] using hd.2)
      obtain ⟨Vb₂, rfl, hrelB'⟩ := hrelB.sres_inv
      obtain ⟨r₄, h₄, hrelP⟩ := ihp hrelB'
        (by simpa [rnMCode, rnMStmt] using hm.1.2)
        (by simpa [codeRedecl, redeclStmt] using hd.1)
      obtain ⟨Vp₂, rfl, hrelP'⟩ := hrelP.sres_inv
      obtain ⟨r₅, h₅, hrelE⟩ := ihr hrelP'
        (by
          simp only [rnMCode, Bool.or_eq_false_iff]
          exact ⟨⟨hm.1.1, hm.1.2⟩, hm.2⟩)
        (by
          simp only [codeRedecl, Bool.or_eq_false_iff]
          exact ⟨hd.1, hd.2⟩)
      obtain ⟨Ve₂, rfl, hrelE'⟩ := hrelE.sres_inv
      exact ⟨_, Step.loopStep h₂ hnz h₃ hob h₄ h₅, .sres _ _ hrelE'⟩
  | loopPostHalt hc hnz hb hob hp ihc ihb ihp =>
      intro V₂ hR hm hd
      simp only [rnMCode, Bool.or_eq_false_iff] at hm
      simp only [codeRedecl, Bool.or_eq_false_iff] at hd
      obtain ⟨r₂, h₂, hrel⟩ := ihc hR
        (by simpa [rnMCode] using hm.1.1) rfl
      rw [hrel.eres_inv] at h₂
      obtain ⟨r₃, h₃, hrelB⟩ := ihb hR
        (by simpa [rnMCode, rnMStmt] using hm.2)
        (by simpa [codeRedecl, redeclStmt] using hd.2)
      obtain ⟨Vb₂, rfl, hrelB'⟩ := hrelB.sres_inv
      obtain ⟨r₄, h₄, hrelP⟩ := ihp hrelB'
        (by simpa [rnMCode, rnMStmt] using hm.1.2)
        (by simpa [codeRedecl, redeclStmt] using hd.1)
      obtain ⟨Vp₂, rfl, hrelP'⟩ := hrelP.sres_inv
      exact ⟨_, Step.loopPostHalt h₂ hnz h₃ hob h₄, .sres _ _ hrelP'⟩
  | loopBreak hc hnz hb ihc ihb =>
      intro V₂ hR hm hd
      simp only [rnMCode, Bool.or_eq_false_iff] at hm
      simp only [codeRedecl, Bool.or_eq_false_iff] at hd
      obtain ⟨r₂, h₂, hrel⟩ := ihc hR
        (by simpa [rnMCode] using hm.1.1) rfl
      rw [hrel.eres_inv] at h₂
      obtain ⟨r₃, h₃, hrelB⟩ := ihb hR
        (by simpa [rnMCode, rnMStmt] using hm.2)
        (by simpa [codeRedecl, redeclStmt] using hd.2)
      obtain ⟨Vb₂, rfl, hrelB'⟩ := hrelB.sres_inv
      exact ⟨_, Step.loopBreak h₂ hnz h₃, .sres _ _ hrelB'⟩
  | loopLeave hc hnz hb ihc ihb =>
      intro V₂ hR hm hd
      simp only [rnMCode, Bool.or_eq_false_iff] at hm
      simp only [codeRedecl, Bool.or_eq_false_iff] at hd
      obtain ⟨r₂, h₂, hrel⟩ := ihc hR
        (by simpa [rnMCode] using hm.1.1) rfl
      rw [hrel.eres_inv] at h₂
      obtain ⟨r₃, h₃, hrelB⟩ := ihb hR
        (by simpa [rnMCode, rnMStmt] using hm.2)
        (by simpa [codeRedecl, redeclStmt] using hd.2)
      obtain ⟨Vb₂, rfl, hrelB'⟩ := hrelB.sres_inv
      exact ⟨_, Step.loopLeave h₂ hnz h₃, .sres _ _ hrelB'⟩
  | loopBodyHalt hc hnz hb ihc ihb =>
      intro V₂ hR hm hd
      simp only [rnMCode, Bool.or_eq_false_iff] at hm
      simp only [codeRedecl, Bool.or_eq_false_iff] at hd
      obtain ⟨r₂, h₂, hrel⟩ := ihc hR
        (by simpa [rnMCode] using hm.1.1) rfl
      rw [hrel.eres_inv] at h₂
      obtain ⟨r₃, h₃, hrelB⟩ := ihb hR
        (by simpa [rnMCode, rnMStmt] using hm.2)
        (by simpa [codeRedecl, redeclStmt] using hd.2)
      obtain ⟨Vb₂, rfl, hrelB'⟩ := hrelB.sres_inv
      exact ⟨_, Step.loopBodyHalt h₂ hnz h₃, .sres _ _ hrelB'⟩

theorem RnRes.eres_inv_right {x x' : Ident} {n : Nat} {r : EResult D}
    {res₁ : Res D} (h : RnRes x x' n res₁ (.eres r)) : res₁ = .eres r := by
  cases h; rfl

theorem RnRes.sres_inv_right {x x' : Ident} {n : Nat} {V₂ : VEnv D} {st o}
    {res₁ : Res D} (h : RnRes x x' n res₁ (.sres V₂ st o)) :
    ∃ V₁, res₁ = .sres V₁ st o ∧ RnRel x x' n V₁ V₂ := by
  cases h with
  | sres _ _ hrel => exact ⟨_, rfl, hrel⟩

/-! ### The rename is an involution under freshness -/

theorem renVar_invol {x x' y : Ident} (hy : y ≠ x') :
    renVar x' x (renVar x x' y) = y := by
  by_cases hyx : y = x
  · subst hyx
    simp [renVar]
  · simp [renVar, hyx, hy]

mutual
theorem renExpr_invol {x x' : Ident} : ∀ {e : Expr Op},
    exprMentions x' e = false → renExpr x' x (renExpr x x' e) = e
  | .lit l, _ => rfl
  | .var y, h => by
      simp only [exprMentions, decide_eq_false_iff_not] at h
      simp [renExpr, renVar_invol (fun hc : y = x' => h hc.symm)]
  | .builtin op args, h => by
      simp only [exprMentions] at h
      simp only [renExpr]
      rw [renArgs_invol h]
  | .call f args, h => by
      simp only [exprMentions] at h
      simp only [renExpr]
      rw [renArgs_invol h]

theorem renArgs_invol {x x' : Ident} : ∀ {args : List (Expr Op)},
    argsMentions x' args = false → renArgs x' x (renArgs x x' args) = args
  | [], _ => rfl
  | e :: rest, h => by
      simp only [argsMentions, Bool.or_eq_false_iff] at h
      simp only [renArgs]
      rw [renExpr_invol h.1, renArgs_invol h.2]
end

theorem renVars_invol {x x' : Ident} {ys : List Ident}
    (h : ∀ y ∈ ys, y ≠ x') :
    (ys.map (renVar x x')).map (renVar x' x) = ys := by
  induction ys with
  | nil => rfl
  | cons y rest ih =>
      simp only [List.map_cons,
        renVar_invol (h y (List.mem_cons_self ..))]
      rw [ih (fun z hz => h z (List.mem_cons_of_mem _ hz))]

mutual
theorem renStmt_invol {x x' : Ident} : ∀ {s : Stmt Op},
    stmtMentions x' s = false → renStmt x' x (renStmt x x' s) = s
  | .block body, h => by
      simp only [stmtMentions] at h
      simp only [renStmt]
      rw [renStmts_invol h]
  | .funDef n ps rs body, _ => by simp [renStmt]
  | .letDecl vars none, h => by
      simp only [stmtMentions, Bool.or_eq_false_iff,
        decide_eq_false_iff_not] at h
      simp only [renStmt, Option.map_none]
      rw [renVars_invol (fun y hy hc => h.1 (by rw [← hc]; exact hy))]
  | .letDecl vars (some e), h => by
      simp only [stmtMentions, Bool.or_eq_false_iff,
        decide_eq_false_iff_not, optExprMentions] at h
      simp only [renStmt, Option.map_some]
      rw [renVars_invol (fun y hy hc => h.1 (by rw [← hc]; exact hy)), renExpr_invol h.2]
  | .assign vars e, h => by
      simp only [stmtMentions, Bool.or_eq_false_iff,
        decide_eq_false_iff_not] at h
      simp only [renStmt]
      rw [renVars_invol (fun y hy hc => h.1 (by rw [← hc]; exact hy)), renExpr_invol h.2]
  | .cond c body, h => by
      simp only [stmtMentions, Bool.or_eq_false_iff] at h
      simp only [renStmt]
      rw [renExpr_invol h.1, renStmts_invol h.2]
  | .switch c cases dflt, h => by
      simp only [stmtMentions, Bool.or_eq_false_iff] at h
      simp only [renStmt]
      rw [renExpr_invol h.1.1, renCases_invol h.1.2, renDflt_invol h.2]
  | .forLoop init c post body, h => by
      simp only [stmtMentions, Bool.or_eq_false_iff] at h
      simp only [renStmt]
      rw [renStmts_invol h.1.1.1, renExpr_invol h.1.1.2,
        renStmts_invol h.1.2, renStmts_invol h.2]
  | .exprStmt e, h => by
      simp only [stmtMentions] at h
      simp only [renStmt]
      rw [renExpr_invol h]
  | .break, _ => rfl
  | .continue, _ => rfl
  | .leave, _ => rfl

theorem renStmts_invol {x x' : Ident} : ∀ {ss : List (Stmt Op)},
    stmtsMentions x' ss = false → renStmts x' x (renStmts x x' ss) = ss
  | [], _ => rfl
  | s :: rest, h => by
      simp only [stmtsMentions, Bool.or_eq_false_iff] at h
      simp only [renStmts]
      rw [renStmt_invol h.1, renStmts_invol h.2]

theorem renCases_invol {x x' : Ident} : ∀ {cs : List (Literal × Block Op)},
    casesMentions x' cs = false → renCases x' x (renCases x x' cs) = cs
  | [], _ => rfl
  | (l, b) :: rest, h => by
      simp only [casesMentions, Bool.or_eq_false_iff] at h
      simp only [renCases]
      rw [renStmts_invol h.1, renCases_invol h.2]

theorem renDflt_invol {x x' : Ident} : ∀ {d : Option (Block Op)},
    optBlockMentions x' d = false → renDflt x' x (renDflt x x' d) = d
  | none, _ => rfl
  | some b, h => by
      simp only [optBlockMentions] at h
      simp only [renDflt]
      rw [renStmts_invol h]
end

theorem renCode_invol {x x' : Ident} {code : Code Op}
    (h : codeMentions x' code = false) :
    renCode x' x (renCode x x' code) = code := by
  cases code with
  | expr e => simp only [renCode]; rw [renExpr_invol (by exact h)]
  | args es => simp only [renCode]; rw [renArgs_invol (by exact h)]
  | stmt s => simp only [renCode]; rw [renStmt_invol (by exact h)]
  | stmts ss => simp only [renCode]; rw [renStmts_invol (by exact h)]
  | loop c post body =>
      simp only [codeMentions, Bool.or_eq_false_iff] at h
      simp only [renCode]
      rw [renExpr_invol h.1.1, renStmts_invol h.1.2, renStmts_invol h.2]

/-! ### Relation symmetry (rename roles swapped) -/

theorem renKeys_invol {x x' : Ident} {C : VEnv D}
    (h : ∀ p ∈ C, p.1 ≠ x') :
    renKeys x' x (renKeys x x' C) = C := by
  induction C with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨k, v⟩ := p
      rw [renKeys_cons, renKeys_cons,
        renVar_invol (h (k, v) (List.mem_cons_self ..)),
        ih (fun q hq => h q (List.mem_cons_of_mem _ hq))]

theorem RnRel.symm {x x' : Ident} (hxx' : x ≠ x') {n : Nat}
    {V₁ V₂ : VEnv D} (h : RnRel x x' n V₁ V₂) :
    RnRel x' x n V₂ V₁ := by
  obtain ⟨C, base, hx, hx', hn⟩ := h
  have hC₁ : renKeys x' x (renKeys x x' C) = C := renKeys_invol hx'
  have hmk := RnRel.mk (calls := calls) (creates := creates)
    (x := x') (x' := x) (renKeys x x' C) base ?_ ?_ hn
  · rwa [hC₁] at hmk
  · obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hx
    rw [renKeys_find_x' hp hx']
    simp
  · intro p hp
    simp only [renKeys, List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    simp only [renVar]
    split
    · exact fun hc => hxx' hc.symm
    · rename_i hqx
      exact fun hc => hqx (by rw [hc])

theorem RnRes.symm {x x' : Ident} (hxx' : x ≠ x') {n : Nat}
    {res₁ res₂ : Res D} (h : RnRes x x' n res₁ res₂) :
    RnRes x' x n res₂ res₁ := by
  cases h with
  | eres r => exact .eres r
  | sres st o hrel => exact .sres st o (hrel.symm hxx')

/-! ### Syntactic facts about the renamed code -/

theorem renVar_ne_x {x x' y : Ident} (hxx' : x ≠ x') :
    renVar x x' y ≠ x := by
  simp only [renVar]
  split
  · exact fun hc => hxx' hc.symm
  · rename_i hy
    exact hy

theorem renVars_not_mem_x {x x' : Ident} (hxx' : x ≠ x')
    (ys : List Ident) : x ∉ ys.map (renVar x x') := by
  intro hc
  obtain ⟨y, _, hy⟩ := List.mem_map.mp hc
  exact renVar_ne_x hxx' hy

mutual
theorem exprMentions_ren {x x' : Ident} (hxx' : x ≠ x') : ∀ (e : Expr Op),
    exprMentions x (renExpr x x' e) = false
  | .lit _ => rfl
  | .var y => by
      simp only [renExpr, exprMentions, decide_eq_false_iff_not]
      exact fun hc => renVar_ne_x hxx' hc.symm
  | .builtin op args => by
      simp only [renExpr, exprMentions]
      exact argsMentions_ren hxx' args
  | .call f args => by
      simp only [renExpr, exprMentions]
      exact argsMentions_ren hxx' args

theorem argsMentions_ren {x x' : Ident} (hxx' : x ≠ x') :
    ∀ (args : List (Expr Op)),
    argsMentions x (renArgs x x' args) = false
  | [] => rfl
  | e :: rest => by
      simp only [renArgs, argsMentions, Bool.or_eq_false_iff]
      exact ⟨exprMentions_ren hxx' e, argsMentions_ren hxx' rest⟩
end

theorem optExprMentions_ren {x x' : Ident} (hxx' : x ≠ x') :
    ∀ (rhs : Option (Expr Op)),
    optExprMentions x (rhs.map (renExpr x x')) = false
  | none => rfl
  | some e => exprMentions_ren hxx' e

mutual
theorem rnMStmt_ren {x x' : Ident} (hxx' : x ≠ x') : ∀ (s : Stmt Op),
    rnMStmt x (renStmt x x' s) = false
  | .block body => by
      simp only [renStmt, rnMStmt]
      exact rnMStmts_ren hxx' body
  | .funDef n ps rs body => by simp [renStmt, rnMStmt]
  | .letDecl vars rhs => by
      simp only [renStmt, rnMStmt, Bool.or_eq_false_iff,
        decide_eq_false_iff_not]
      exact ⟨renVars_not_mem_x hxx' vars, optExprMentions_ren hxx' rhs⟩
  | .assign vars e => by
      simp only [renStmt, rnMStmt, Bool.or_eq_false_iff,
        decide_eq_false_iff_not]
      exact ⟨renVars_not_mem_x hxx' vars, exprMentions_ren hxx' e⟩
  | .cond c body => by
      simp only [renStmt, rnMStmt, Bool.or_eq_false_iff]
      exact ⟨exprMentions_ren hxx' c, rnMStmts_ren hxx' body⟩
  | .switch c cases dflt => by
      simp only [renStmt, rnMStmt, Bool.or_eq_false_iff]
      exact ⟨⟨exprMentions_ren hxx' c, rnMCases_ren hxx' cases⟩,
        rnMDflt_ren hxx' dflt⟩
  | .forLoop init c post body => by
      simp only [renStmt, rnMStmt, Bool.or_eq_false_iff]
      exact ⟨⟨⟨rnMStmts_ren hxx' init, exprMentions_ren hxx' c⟩,
        rnMStmts_ren hxx' post⟩, rnMStmts_ren hxx' body⟩
  | .exprStmt e => by
      simp only [renStmt, rnMStmt]
      exact exprMentions_ren hxx' e
  | .break => rfl
  | .continue => rfl
  | .leave => rfl

theorem rnMStmts_ren {x x' : Ident} (hxx' : x ≠ x') : ∀ (ss : List (Stmt Op)),
    rnMStmts x (renStmts x x' ss) = false
  | [] => rfl
  | s :: rest => by
      simp only [renStmts, rnMStmts, Bool.or_eq_false_iff]
      exact ⟨rnMStmt_ren hxx' s, rnMStmts_ren hxx' rest⟩

theorem rnMCases_ren {x x' : Ident} (hxx' : x ≠ x') :
    ∀ (cs : List (Literal × Block Op)),
    rnMCases x (renCases x x' cs) = false
  | [] => rfl
  | (l, b) :: rest => by
      simp only [renCases, rnMCases, Bool.or_eq_false_iff]
      exact ⟨rnMStmts_ren hxx' b, rnMCases_ren hxx' rest⟩

theorem rnMDflt_ren {x x' : Ident} (hxx' : x ≠ x') :
    ∀ (d : Option (Block Op)),
    rnMDflt x (renDflt x x' d) = false
  | none => rfl
  | some b => rnMStmts_ren hxx' b
end

/-- The renamed code never mentions `x` at the executing-frame level. -/
theorem rnM_renCode {x x' : Ident} (hxx' : x ≠ x') (code : Code Op) :
    rnMCode x (renCode x x' code) = false := by
  cases code with
  | expr e => exact exprMentions_ren hxx' e
  | args es => exact argsMentions_ren hxx' es
  | stmt s => exact rnMStmt_ren hxx' s
  | stmts ss => exact rnMStmts_ren hxx' ss
  | loop c post body =>
      simp only [renCode, rnMCode, Bool.or_eq_false_iff]
      exact ⟨⟨exprMentions_ren hxx' c, rnMStmts_ren hxx' post⟩,
        rnMStmts_ren hxx' body⟩

/-! Renamed declarations avoid `x'` (original binders avoid it by freshness,
and the rename only produces `x'` from `x` binders, which redecl-freeness
excludes — in fact the *rename target itself* would be a legitimate `x'`
declaration, but sequences the transform renames always declare `x`, and this
lemma is applied to the *pre-splice code that contains no `x` declarations*
outside the renamed sequence). -/

mutual
theorem redeclStmt_ren {x x' : Ident} : ∀ {s : Stmt Op},
    rnMStmt x' s = false → redeclStmt x s = false →
    redeclStmt x' (renStmt x x' s) = false
  | .block body, hm, hd => by
      simp only [rnMStmt] at hm
      simp only [redeclStmt] at hd ⊢
      exact redeclStmts_ren hm hd
  | .funDef n ps rs body, _, _ => by simp [renStmt, redeclStmt]
  | .letDecl vars rhs, hm, hd => by
      simp only [rnMStmt, Bool.or_eq_false_iff,
        decide_eq_false_iff_not] at hm
      simp only [redeclStmt] at hd
      simp only [renStmt, redeclStmt, List.contains_eq_mem,
        decide_eq_false_iff_not]
      intro hc
      obtain ⟨y, hy, hye⟩ := List.mem_map.mp hc
      by_cases hyx : y = x
      · subst hyx
        rw [List.contains_eq_mem] at hd
        simp [hy] at hd
      · rw [show renVar x x' y = y from by simp [renVar, hyx]] at hye
        exact hm.1 (hye ▸ hy)
  | .assign vars e, _, _ => by simp [renStmt, redeclStmt]
  | .cond c body, hm, hd => by
      simp only [rnMStmt, Bool.or_eq_false_iff] at hm
      simp only [redeclStmt] at hd ⊢
      exact redeclStmts_ren hm.2 hd
  | .switch c cases dflt, hm, hd => by
      simp only [rnMStmt, Bool.or_eq_false_iff] at hm
      simp only [redeclStmt, Bool.or_eq_false_iff] at hd
      simp only [renStmt, redeclStmt, Bool.or_eq_false_iff]
      exact ⟨redeclCases_ren hm.1.2 hd.1, redeclDflt_ren hm.2 hd.2⟩
  | .forLoop init c post body, hm, hd => by
      simp only [rnMStmt, Bool.or_eq_false_iff] at hm
      simp only [redeclStmt, Bool.or_eq_false_iff] at hd
      simp only [renStmt, redeclStmt, Bool.or_eq_false_iff]
      exact ⟨⟨redeclStmts_ren hm.1.1.1 hd.1.1,
        redeclStmts_ren hm.1.2 hd.1.2⟩, redeclStmts_ren hm.2 hd.2⟩
  | .exprStmt e, _, _ => by simp [renStmt, redeclStmt]
  | .break, _, _ => rfl
  | .continue, _, _ => rfl
  | .leave, _, _ => rfl

theorem redeclStmts_ren {x x' : Ident} : ∀ {ss : List (Stmt Op)},
    rnMStmts x' ss = false → redeclStmts x ss = false →
    redeclStmts x' (renStmts x x' ss) = false
  | [], _, _ => rfl
  | s :: rest, hm, hd => by
      simp only [rnMStmts, Bool.or_eq_false_iff] at hm
      simp only [redeclStmts, Bool.or_eq_false_iff] at hd
      simp only [renStmts, redeclStmts, Bool.or_eq_false_iff]
      exact ⟨redeclStmt_ren hm.1 hd.1, redeclStmts_ren hm.2 hd.2⟩

theorem redeclCases_ren {x x' : Ident} : ∀ {cs : List (Literal × Block Op)},
    rnMCases x' cs = false → redeclCases x cs = false →
    redeclCases x' (renCases x x' cs) = false
  | [], _, _ => rfl
  | (l, b) :: rest, hm, hd => by
      simp only [rnMCases, Bool.or_eq_false_iff] at hm
      simp only [redeclCases, Bool.or_eq_false_iff] at hd
      simp only [renCases, redeclCases, Bool.or_eq_false_iff]
      exact ⟨redeclStmts_ren hm.1 hd.1, redeclCases_ren hm.2 hd.2⟩

theorem redeclDflt_ren {x x' : Ident} : ∀ {d : Option (Block Op)},
    rnMDflt x' d = false → redeclDflt x d = false →
    redeclDflt x' (renDflt x x' d) = false
  | none, _, _ => rfl
  | some b, hm, hd => by
      simp only [rnMDflt] at hm
      simp only [redeclDflt] at hd
      simp only [renDflt, redeclDflt]
      exact redeclStmts_ren hm hd
end

theorem redecl_renCode {x x' : Ident} {code : Code Op}
    (hm : rnMCode x' code = false) (hd : codeRedecl x code = false) :
    codeRedecl x' (renCode x x' code) = false := by
  cases code with
  | expr e => rfl
  | args es => rfl
  | stmt s => exact redeclStmt_ren hm hd
  | stmts ss => exact redeclStmts_ren hm hd
  | loop c post body =>
      simp only [rnMCode, Bool.or_eq_false_iff] at hm
      simp only [codeRedecl, Bool.or_eq_false_iff] at hd
      simp only [renCode, codeRedecl, Bool.or_eq_false_iff]
      exact ⟨redeclStmts_ren hm.1.2 hd.1, redeclStmts_ren hm.2 hd.2⟩

/-! Frame-level mentions imply the weaker executing-frame notion. -/

mutual
theorem rnMStmt_of_mentions {z : Ident} : ∀ {s : Stmt Op},
    stmtMentions z s = false → rnMStmt z s = false
  | .block body, h => by
      simp only [stmtMentions] at h
      simp only [rnMStmt]
      exact rnMStmts_of_mentions h
  | .funDef n ps rs body, _ => rfl
  | .letDecl vars rhs, h => by
      simp only [stmtMentions] at h
      simpa only [rnMStmt] using h
  | .assign vars e, h => by
      simp only [stmtMentions] at h
      simpa only [rnMStmt] using h
  | .cond c body, h => by
      simp only [stmtMentions, Bool.or_eq_false_iff] at h
      simp only [rnMStmt, Bool.or_eq_false_iff]
      exact ⟨h.1, rnMStmts_of_mentions h.2⟩
  | .switch c cases dflt, h => by
      simp only [stmtMentions, Bool.or_eq_false_iff] at h
      simp only [rnMStmt, Bool.or_eq_false_iff]
      exact ⟨⟨h.1.1, rnMCases_of_mentions h.1.2⟩, rnMDflt_of_mentions h.2⟩
  | .forLoop init c post body, h => by
      simp only [stmtMentions, Bool.or_eq_false_iff] at h
      simp only [rnMStmt, Bool.or_eq_false_iff]
      exact ⟨⟨⟨rnMStmts_of_mentions h.1.1.1, h.1.1.2⟩,
        rnMStmts_of_mentions h.1.2⟩, rnMStmts_of_mentions h.2⟩
  | .exprStmt e, h => by
      simp only [stmtMentions] at h
      simpa only [rnMStmt] using h
  | .break, _ => rfl
  | .continue, _ => rfl
  | .leave, _ => rfl

theorem rnMStmts_of_mentions {z : Ident} : ∀ {ss : List (Stmt Op)},
    stmtsMentions z ss = false → rnMStmts z ss = false
  | [], _ => rfl
  | s :: rest, h => by
      simp only [stmtsMentions, Bool.or_eq_false_iff] at h
      simp only [rnMStmts, Bool.or_eq_false_iff]
      exact ⟨rnMStmt_of_mentions h.1, rnMStmts_of_mentions h.2⟩

theorem rnMCases_of_mentions {z : Ident} : ∀ {cs : List (Literal × Block Op)},
    casesMentions z cs = false → rnMCases z cs = false
  | [], _ => rfl
  | (l, b) :: rest, h => by
      simp only [casesMentions, Bool.or_eq_false_iff] at h
      simp only [rnMCases, Bool.or_eq_false_iff]
      exact ⟨rnMStmts_of_mentions h.1, rnMCases_of_mentions h.2⟩

theorem rnMDflt_of_mentions {z : Ident} : ∀ {d : Option (Block Op)},
    optBlockMentions z d = false → rnMDflt z d = false
  | none, _ => rfl
  | some b, h => by
      simp only [optBlockMentions] at h
      simp only [rnMDflt]
      exact rnMStmts_of_mentions h
end

theorem rnMCode_of_mentions {z : Ident} {code : Code Op}
    (h : codeMentions z code = false) : rnMCode z code = false := by
  cases code with
  | expr e => exact h
  | args es => exact h
  | stmt s => exact rnMStmt_of_mentions h
  | stmts ss => exact rnMStmts_of_mentions h
  | loop c post body =>
      simp only [codeMentions, Bool.or_eq_false_iff] at h
      simp only [rnMCode, Bool.or_eq_false_iff]
      exact ⟨⟨h.1.1, rnMStmts_of_mentions h.1.2⟩, rnMStmts_of_mentions h.2⟩

/-- **The backward rename transport**, by role-swap through the involution. -/
theorem Step.rn_congr_bwd {x x' : Ident} (hxx' : x ≠ x') {n : Nat}
    {funs : FunEnv D} {V₂ : VEnv D} {st : EvmState} {code : Code Op}
    {res₂ : Res D}
    (h : Step D funs V₂ st (renCode x x' code) res₂) :
    ∀ {V₁}, RnRel x x' n V₁ V₂ →
      codeMentions x' code = false →
      codeRedecl x code = false →
      ∃ res₁, Step D funs V₁ st code res₁ ∧ RnRes x x' n res₁ res₂ := by
  intro V₁ hR hmfull hd
  have hm : rnMCode x' code = false := rnMCode_of_mentions hmfull
  obtain ⟨res₁, h₁, hrel⟩ := Step.rn_congr h (hR.symm hxx')
    (rnM_renCode hxx' code) (redecl_renCode hm hd)
  rw [renCode_invol hmfull] at h₁
  exact ⟨res₁, h₁, hrel.symm hxx'.symm⟩

/-! ### Rename identity on non-mentioning code -/

mutual
theorem renExpr_id {x x' : Ident} : ∀ {e : Expr Op},
    exprMentions x e = false → renExpr x x' e = e
  | .lit _, _ => rfl
  | .var y, h => by
      simp only [exprMentions, decide_eq_false_iff_not] at h
      simp only [renExpr, renVar]
      rw [if_neg (fun hc : y = x => h hc.symm)]
  | .builtin op args, h => by
      simp only [exprMentions] at h
      simp only [renExpr]
      rw [renArgs_id h]
  | .call f args, h => by
      simp only [exprMentions] at h
      simp only [renExpr]
      rw [renArgs_id h]

theorem renArgs_id {x x' : Ident} : ∀ {args : List (Expr Op)},
    argsMentions x args = false → renArgs x x' args = args
  | [], _ => rfl
  | e :: rest, h => by
      simp only [argsMentions, Bool.or_eq_false_iff] at h
      simp only [renArgs]
      rw [renExpr_id h.1, renArgs_id h.2]
end

theorem renVars_id {x x' : Ident} {ys : List Ident}
    (h : ∀ y ∈ ys, y ≠ x) : ys.map (renVar x x') = ys :=
  map_renVar_id h

mutual
theorem renStmt_id {x x' : Ident} : ∀ {s : Stmt Op},
    rnMStmt x s = false → renStmt x x' s = s
  | .block body, h => by
      simp only [rnMStmt] at h
      simp only [renStmt]
      rw [renStmts_id h]
  | .funDef n ps rs body, _ => rfl
  | .letDecl vars rhs, h => by
      simp only [rnMStmt, Bool.or_eq_false_iff,
        decide_eq_false_iff_not, optExprMentions] at h
      simp only [renStmt]
      rw [renVars_id (fun y hy hc => h.1 (by rw [← hc]; exact hy))]
      cases rhs with
      | none => rfl
      | some e =>
          simp only [Option.map_some]
          rw [renExpr_id h.2]
  | .assign vars e, h => by
      simp only [rnMStmt, Bool.or_eq_false_iff,
        decide_eq_false_iff_not] at h
      simp only [renStmt]
      rw [renVars_id (fun y hy hc => h.1 (by rw [← hc]; exact hy)), renExpr_id h.2]
  | .cond c body, h => by
      simp only [rnMStmt, Bool.or_eq_false_iff] at h
      simp only [renStmt]
      rw [renExpr_id h.1, renStmts_id h.2]
  | .switch c cases dflt, h => by
      simp only [rnMStmt, Bool.or_eq_false_iff] at h
      simp only [renStmt]
      rw [renExpr_id h.1.1, renCases_id h.1.2, renDflt_id h.2]
  | .forLoop init c post body, h => by
      simp only [rnMStmt, Bool.or_eq_false_iff] at h
      simp only [renStmt]
      rw [renStmts_id h.1.1.1, renExpr_id h.1.1.2,
        renStmts_id h.1.2, renStmts_id h.2]
  | .exprStmt e, h => by
      simp only [rnMStmt] at h
      simp only [renStmt]
      rw [renExpr_id h]
  | .break, _ => rfl
  | .continue, _ => rfl
  | .leave, _ => rfl

theorem renStmts_id {x x' : Ident} : ∀ {ss : List (Stmt Op)},
    rnMStmts x ss = false → renStmts x x' ss = ss
  | [], _ => rfl
  | s :: rest, h => by
      simp only [rnMStmts, Bool.or_eq_false_iff] at h
      simp only [renStmts]
      rw [renStmt_id h.1, renStmts_id h.2]

theorem renCases_id {x x' : Ident} : ∀ {cs : List (Literal × Block Op)},
    rnMCases x cs = false → renCases x x' cs = cs
  | [], _ => rfl
  | (l, b) :: rest, h => by
      simp only [rnMCases, Bool.or_eq_false_iff] at h
      simp only [renCases]
      rw [renStmts_id h.1, renCases_id h.2]

theorem renDflt_id {x x' : Ident} : ∀ {d : Option (Block Op)},
    rnMDflt x d = false → renDflt x x' d = d
  | none, _ => rfl
  | some b, h => by
      simp only [rnMDflt] at h
      simp only [renDflt]
      rw [renStmts_id h]
end

/-- Restoring both sides to a base at or below the pinned length erases the
rename. -/
theorem restore_rn_eq {x x' : Ident} {n : Nat} {V₀ V₁ V₂ : VEnv D}
    (h : RnRel x x' n V₁ V₂) (hb : V₀.length ≤ n) :
    restore V₀ V₁ = restore V₀ V₂ := by
  obtain ⟨C, base, hx, hx', hn⟩ := h
  unfold restore
  rw [YulEvmCompiler.Optimizer.FuseDeclAssign.drop_to_base C base (by omega),
    YulEvmCompiler.Optimizer.FuseDeclAssign.drop_to_base
      (renKeys x x' C) base (by omega)]

/-! ### Splice machinery — bridges

`mentionsBeforeDecl`'s generic arm speaks `stmtIdents`; the rename-identity
lemmas speak `rnMStmt`.  `stmtIdents` is the coarsest scan, so it bounds the
funDef-skipping one. -/

mutual
theorem exprMentions_mem_idents {z : Ident} : ∀ {e : Expr Op},
    exprMentions z e = true → z ∈ exprIdents e
  | .var y, h => by
      simp only [exprMentions, decide_eq_true_eq] at h
      simp [exprIdents, h]
  | .builtin op args, h =>
      argsMentions_mem_idents (by simpa [exprMentions] using h)
  | .call f args, h => by
      simp only [exprIdents, List.mem_cons]
      exact Or.inr (argsMentions_mem_idents (by simpa [exprMentions] using h))

theorem argsMentions_mem_idents {z : Ident} : ∀ {es : List (Expr Op)},
    argsMentions z es = true → z ∈ argsIdents es
  | e :: rest, h => by
      simp only [argsMentions, Bool.or_eq_true] at h
      simp only [argsIdents, List.mem_append]
      rcases h with h | h
      · exact Or.inl (exprMentions_mem_idents h)
      · exact Or.inr (argsMentions_mem_idents h)
end

mutual
theorem rnMStmt_mem_idents {z : Ident} : ∀ {s : Stmt Op},
    rnMStmt z s = true → z ∈ stmtIdents s
  | .block body, h => rnMStmts_mem_idents h
  | .funDef _ _ _ _, h => by simp [rnMStmt] at h
  | .letDecl vars rhs, h => by
      simp only [rnMStmt, Bool.or_eq_true, decide_eq_true_eq] at h
      cases rhs with
      | none =>
          simp only [stmtIdents]
          rcases h with h | h
          · exact h
          · simp [optExprMentions] at h
      | some e =>
          simp only [stmtIdents, List.mem_append]
          rcases h with h | h
          · exact Or.inl h
          · exact Or.inr (exprMentions_mem_idents
              (by simpa [optExprMentions] using h))
  | .assign vars e, h => by
      simp only [rnMStmt, Bool.or_eq_true, decide_eq_true_eq] at h
      simp only [stmtIdents, List.mem_append]
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (exprMentions_mem_idents h)
  | .cond c body, h => by
      simp only [rnMStmt, Bool.or_eq_true] at h
      simp only [stmtIdents, List.mem_append]
      rcases h with h | h
      · exact Or.inl (exprMentions_mem_idents h)
      · exact Or.inr (rnMStmts_mem_idents h)
  | .switch c cases dflt, h => by
      simp only [rnMStmt, Bool.or_eq_true] at h
      simp only [stmtIdents, List.mem_append]
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl (exprMentions_mem_idents h))
      · exact Or.inl (Or.inr (rnMCases_mem_idents h))
      · exact Or.inr (rnMDflt_mem_idents h)
  | .forLoop init c post body, h => by
      simp only [rnMStmt, Bool.or_eq_true] at h
      simp only [stmtIdents, List.mem_append]
      rcases h with ((h | h) | h) | h
      · exact Or.inl (Or.inl (Or.inl (rnMStmts_mem_idents h)))
      · exact Or.inl (Or.inl (Or.inr (exprMentions_mem_idents h)))
      · exact Or.inl (Or.inr (rnMStmts_mem_idents h))
      · exact Or.inr (rnMStmts_mem_idents h)
  | .exprStmt e, h => exprMentions_mem_idents (by simpa [rnMStmt] using h)
  | .«break», h => by simp [rnMStmt] at h
  | .«continue», h => by simp [rnMStmt] at h
  | .leave, h => by simp [rnMStmt] at h

theorem rnMStmts_mem_idents {z : Ident} : ∀ {ss : List (Stmt Op)},
    rnMStmts z ss = true → z ∈ stmtsIdents ss
  | s :: rest, h => by
      simp only [rnMStmts, Bool.or_eq_true] at h
      simp only [stmtsIdents, List.mem_append]
      rcases h with h | h
      · exact Or.inl (rnMStmt_mem_idents h)
      · exact Or.inr (rnMStmts_mem_idents h)

theorem rnMCases_mem_idents {z : Ident} :
    ∀ {cs : List (Literal × Block Op)},
    rnMCases z cs = true → z ∈ casesIdents cs
  | (l, b) :: rest, h => by
      simp only [rnMCases, Bool.or_eq_true] at h
      simp only [casesIdents, List.mem_append]
      rcases h with h | h
      · exact Or.inl (rnMStmts_mem_idents h)
      · exact Or.inr (rnMCases_mem_idents h)

theorem rnMDflt_mem_idents {z : Ident} : ∀ {dflt : Option (Block Op)},
    rnMDflt z dflt = true → z ∈ dfltIdents dflt
  | some b, h => rnMStmts_mem_idents (by simpa [rnMDflt] using h)
end


/-- Contrapositive form used at guard sites. -/
theorem rnMStmt_of_not_idents {z : Ident} {s : Stmt Op}
    (h : z ∉ stmtIdents s) : rnMStmt z s = false := by
  cases hr : rnMStmt z s with
  | false => rfl
  | true => exact absurd (rnMStmt_mem_idents hr) h

theorem rnMStmts_of_not_idents {z : Ident} {ss : List (Stmt Op)}
    (h : z ∉ stmtsIdents ss) : rnMStmts z ss = false := by
  cases hr : rnMStmts z ss with
  | false => rfl
  | true => exact absurd (rnMStmts_mem_idents hr) h

/-- `stmtsMentions` distributes over append. -/
theorem stmtsMentions_append (z : Ident) (a b : List (Stmt Op)) :
    stmtsMentions (Op := Op) z (a ++ b) =
      (stmtsMentions z a || stmtsMentions z b) := by
  induction a with
  | nil => simp [stmtsMentions]
  | cons s rest ih =>
      simp only [List.cons_append, stmtsMentions, ih, Bool.or_assoc]

/-! ### New surviving bindings come from top-level `let`s

Control constructs `restore` on exit and assignments update in place, so the
segment of the final environment above the entry length is keyed by the
sequence's own top-level binders — the promoted names of a spliced block. -/

theorem topDecls_cons (s : Stmt Op) (rest : List (Stmt Op)) :
    topDecls (s :: rest) = topDecls [s] ++ topDecls rest := by
  cases s <;> simp [topDecls]

private theorem take_len_sub_nil {V V' : VEnv D} (hle : V'.length ≤ V.length) :
    V'.take (V'.length - V.length) = [] := by
  rw [Nat.sub_eq_zero_of_le hle, List.take_zero]

private theorem restore_len_le (V Vb : VEnv D) :
    (restore V Vb).length ≤ V.length := by
  unfold restore
  rw [List.length_drop]
  omega

theorem step_stmt_new_keys {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    {s : Stmt Op} {V' : VEnv D} {st' : EvmState} {o : Outcome}
    (h : Step D funs V st (.stmt s) (.sres V' st' o)) :
    ∀ p ∈ V'.take (V'.length - V.length), p.1 ∈ topDecls [s] := by
  cases h with
  | funDef => simp
  | block hb => simp [take_len_sub_nil (restore_len_le _ _)]
  | @letZero _ _ _ vars =>
      intro p hp
      rw [show (bindZeros D vars ++ V).length - V.length =
          (bindZeros D vars).length from by
            rw [List.length_append]; omega,
        List.take_left' rfl] at hp
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hp
      simpa [topDecls] using hy
  | @letVal _ _ _ vars e vals _ hev hlen =>
      intro p hp
      rw [show (vars.zip vals ++ V).length - V.length =
          (vars.zip vals).length from by
            rw [List.length_append]; omega,
        List.take_left' rfl] at hp
      obtain ⟨a, b⟩ := p
      simpa [topDecls] using (List.of_mem_zip hp).1
  | letHalt _ => simp
  | assignVal _ hlen =>
      simp [take_len_sub_nil (Nat.le_of_eq (VEnv.setMany_length _ _ _))]
  | assignHalt _ => simp
  | exprStmt _ => simp
  | exprStmtHalt _ => simp
  | ifTrue _ hnz hb =>
      cases hb with
      | block _ => simp [take_len_sub_nil (restore_len_le _ _)]
  | ifFalse _ hz => simp
  | ifHalt _ => simp
  | switchExec _ hb =>
      cases hb with
      | block _ => simp [take_len_sub_nil (restore_len_le _ _)]
  | switchHalt _ => simp
  | forLoop _ _ => simp [take_len_sub_nil (restore_len_le _ _)]
  | forInitHalt _ => simp [take_len_sub_nil (restore_len_le _ _)]
  | «break» => simp
  | «continue» => simp
  | «leave» => simp

theorem step_stmts_new_keys {funs : FunEnv D} :
    ∀ {ss : List (Stmt Op)} {V : VEnv D} {st : EvmState} {V' st' o},
    Step D funs V st (.stmts ss) (.sres V' st' o) →
    ∀ p ∈ V'.take (V'.length - V.length), p.1 ∈ topDecls ss := by
  intro ss
  induction ss with
  | nil =>
      intro V st V' st' o h
      cases h with
      | seqNil => simp
  | cons s rest ih =>
      intro V st V' st' o h
      cases h with
      | @seqCons _ _ _ _ _ V1 st1 _ _ _ hs htail =>
          intro p hp
          have h01 : V.length ≤ V1.length := venvLen_mono hs rfl
          have h12 : V1.length ≤ V'.length := venvLen_mono htail rfl
          rw [show V'.length - V.length =
              (V'.length - V1.length) + (V1.length - V.length) from by omega,
            List.take_add] at hp
          rw [topDecls_cons, List.mem_append]
          rcases List.mem_append.mp hp with hp | hp
          · exact Or.inr (ih htail p hp)
          · have hdrop : V'.drop (V'.length - V1.length) = restore V1 V' := rfl
            rw [hdrop] at hp
            have hkeys : (restore V1 V').map Prod.fst = V1.map Prod.fst :=
              restore_keys (venvKeys_suffix htail rfl) h12
            have hp1 : p.1 ∈ ((V1.take (V1.length - V.length)).map Prod.fst) := by
              have hm := List.mem_map_of_mem (f := Prod.fst) hp
              rw [List.map_take, hkeys, ← List.map_take] at hm
              exact hm
            obtain ⟨q, hq, hq1⟩ := List.mem_map.mp hp1
            rw [← hq1]
            exact Or.inl (step_stmt_new_keys hs q hq)
      | seqStop hs hne =>
          intro p hp
          rw [topDecls_cons, List.mem_append]
          exact Or.inl (step_stmt_new_keys hs p hp)

/-! ### Multi-insertion frame transport

The spliced tail runs over the promoted bindings prepended to the entry
environment; each is invisible to the tail (`stmtsMentions` guard), so
iterated `frameAdd`/`frameRemove` transports the tail derivation across the
whole region, with results related by an insertion chain at entry depth. -/

theorem _root_.YulEvmCompiler.Optimizer.InsChain.trans {n : Nat}
    {V₁ V₂ V₃ : VEnv D}
    (h₁ : InsChain (calls := calls) (creates := creates) n V₁ V₂)
    (h₂ : InsChain (calls := calls) (creates := creates) n V₂ V₃) :
    InsChain n V₁ V₃ := by
  induction h₂ with
  | refl => exact h₁
  | snoc _ hins hd ih => exact .snoc ih hins hd

/-- Prepending a whole region is an insertion chain at base depth. -/
theorem insChain_prepend (A V : VEnv D) :
    InsChain (calls := calls) (creates := creates) V.length V (A ++ V) := by
  induction A with
  | nil => exact .refl _
  | cons p A ih =>
      refine .snoc (V₀ := p :: (A ++ V)) ih
        ⟨[], A ++ V, rfl, rfl, rfl⟩ ?_
      rw [List.length_append]
      exact Nat.le_add_left _ _

/-- Result relation: statement results carry an insertion chain at depth
`≥ n`; expression results are equal. -/
def InsRes (n : Nat) : Res D → Res D → Prop
  | .eres r₁, .eres r₂ => r₁ = r₂
  | .sres V₁ st₁ o₁, .sres V₂ st₂ o₂ =>
      InsChain n V₁ V₂ ∧ st₁ = st₂ ∧ o₁ = o₂
  | _, _ => False

theorem InsRes.refl (n : Nat) : ∀ res : Res D, InsRes n res res
  | .eres _ => rfl
  | .sres _ _ _ => ⟨.refl _, rfl, rfl⟩

theorem InsRes.of_relAt {n d : Nat} {x : Ident}
    {v : (evmWithExternal calls creates .any).Value} {res₁ res₂ res₃ : Res D}
    (h₁ : InsRes n res₁ res₂) (h₂ : ResRelAt d x v res₂ res₃) (hd : n ≤ d) :
    InsRes n res₁ res₃ := by
  cases res₂ with
  | eres r =>
      obtain rfl := h₂.eres
      cases res₁ with
      | eres r₁ => exact h₁
      | sres _ _ _ => exact h₁.elim
  | sres V₂ st₂ o₂ =>
      obtain ⟨V₃, rfl, hins⟩ := h₂.sres
      cases res₁ with
      | eres _ => exact h₁.elim
      | sres V₁ st₁ o₁ =>
          obtain ⟨hc, rfl, rfl⟩ := h₁
          exact ⟨hc.snoc hins hd, rfl, rfl⟩

theorem frameAddAll {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    {code : Code Op} {res₁ : Res D}
    (h : Step D funs V st code res₁) :
    ∀ A : VEnv D, (∀ p ∈ A, codeMentions p.1 code = false) →
      ∃ res₂, Step D funs (A ++ V) st code res₂ ∧
        InsRes V.length res₁ res₂ := by
  intro A
  induction A with
  | nil => intro _; exact ⟨res₁, h, InsRes.refl _ _⟩
  | cons p A ih =>
      intro hm
      obtain ⟨res₂, h₂, hrel₂⟩ := ih (fun q hq => hm q (List.mem_cons_of_mem _ hq))
      obtain ⟨res₃, h₃, hrel₃⟩ := frameAdd h₂
        (⟨[], A ++ V, rfl, rfl, rfl⟩ :
          InsAt (A ++ V).length p.1 p.2 (A ++ V) ((p.1, p.2) :: (A ++ V)))
        (hm p List.mem_cons_self)
      refine ⟨res₃, h₃, hrel₂.of_relAt hrel₃ ?_⟩
      rw [List.length_append]
      exact Nat.le_add_left _ _

theorem frameRemoveAll {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    {code : Code Op} :
    ∀ (A : VEnv D) {res₂ : Res D},
      Step D funs (A ++ V) st code res₂ →
      (∀ p ∈ A, codeMentions p.1 code = false) →
      ∃ res₁, Step D funs V st code res₁ ∧ InsRes V.length res₁ res₂
  | [], res₂, h, _ => ⟨res₂, h, InsRes.refl _ _⟩
  | p :: A, res₂, h, hm => by
      obtain ⟨res₁', h₁', hrel'⟩ := frameRemove h
        (⟨[], A ++ V, rfl, rfl, rfl⟩ :
          InsAt (A ++ V).length p.1 p.2 (A ++ V) ((p.1, p.2) :: (A ++ V)))
        (hm p List.mem_cons_self)
      obtain ⟨res₁, h₁, hrel⟩ := frameRemoveAll A h₁'
        (fun q hq => hm q (List.mem_cons_of_mem _ hq))
      refine ⟨res₁, h₁, hrel.of_relAt hrel' ?_⟩
      rw [List.length_append]
      exact Nat.le_add_left _ _

/-! ### Guard decomposition

`shadowedTop x ss = false` splits into the three facts the rename walk
needs: no nested redeclaration, at most one top-level declaration, and no
mention before it. -/

theorem shadowedTop_false {x : Ident} {ss : List (Stmt Op)}
    (h : shadowedTop x ss = false) :
    shadowedTop.nested x ss = false ∧ shadowedTop.topCount x ss ≤ 1 ∧
      mentionsBeforeDecl x ss = false := by
  unfold shadowedTop at h
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Nat.not_lt] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- Locate the unique top-level declaration. -/
theorem topCount_one_split {x : Ident} : ∀ {ss : List (Stmt Op)},
    shadowedTop.topCount x ss = 1 →
    ∃ pre xs rhs suf, ss = pre ++ .letDecl xs rhs :: suf ∧
      xs.contains x = true ∧ shadowedTop.topCount x pre = 0 ∧
      shadowedTop.topCount x suf = 0
  | [], h => by simp [shadowedTop.topCount] at h
  | s :: rest, h => by
      cases s
      case letDecl xs rhs =>
        simp only [shadowedTop.topCount] at h
        by_cases hxs : xs.contains x = true
        · rw [if_pos hxs] at h
          exact ⟨[], xs, rhs, rest, rfl, hxs, rfl, by omega⟩
        · rw [if_neg hxs] at h
          obtain ⟨pre, xs', rhs', suf, hss, hc, hp, hsuf⟩ :=
            topCount_one_split (x := x) (ss := rest) (by omega)
          subst hss
          exact ⟨.letDecl xs rhs :: pre, xs', rhs', suf, rfl, hc,
            by simp only [shadowedTop.topCount, hp]; rw [if_neg hxs], hsuf⟩
      all_goals (
        simp only [shadowedTop.topCount] at h;
        obtain ⟨pre, xs', rhs', suf, hss, hc, hp, hsuf⟩ :=
          topCount_one_split (x := x) (ss := rest) h;
        subst hss;
        exact ⟨_ :: pre, xs', rhs', suf, rfl, hc,
          by simp [shadowedTop.topCount, hp], hsuf⟩)

/-- Facts about the segment before the declaration: it never touches `x`
(so the rename leaves it unchanged), and the guards descend to the rest. -/
theorem pre_facts {x : Ident} : ∀ {pre rest : List (Stmt Op)},
    shadowedTop.nested x (pre ++ rest) = false →
    shadowedTop.topCount x pre = 0 →
    mentionsBeforeDecl x (pre ++ rest) = false →
    rnMStmts x pre = false ∧ shadowedTop.nested x rest = false ∧
      mentionsBeforeDecl x rest = false
  | [], rest, hn, _, hm => ⟨rfl, hn, hm⟩
  | s :: pre, rest, hn, htc, hm => by
      cases s
      case letDecl xs rhs =>
        simp only [shadowedTop.topCount] at htc
        have hxs : xs.contains x = false := by
          by_cases hc : xs.contains x = true
          · rw [if_pos hc] at htc; omega
          · simpa using hc
        rw [if_neg (by simpa using hxs)] at htc
        simp only [List.cons_append, mentionsBeforeDecl] at hm
        rw [if_neg (by simpa using hxs)] at hm
        simp only [Bool.or_eq_false_iff] at hm
        simp only [List.cons_append, shadowedTop.nested] at hn
        obtain ⟨i1, i2, i3⟩ :=
          pre_facts (x := x) (pre := pre) hn (by omega) hm.2
        refine ⟨?_, i2, i3⟩
        simp only [rnMStmts, Bool.or_eq_false_iff]
        refine ⟨?_, i1⟩
        simp only [rnMStmt, Bool.or_eq_false_iff]
        refine ⟨by simpa using hxs, ?_⟩
        cases rhs with
        | none => rfl
        | some e =>
            simp only [Option.map_some, Option.getD_some] at hm
            cases hexp : exprMentions x e with
            | false => simpa [optExprMentions] using hexp
            | true =>
                exact absurd (exprMentions_mem_idents hexp)
                  (by simpa using hm.1)
      case funDef n ps rs b =>
        simp only [shadowedTop.topCount] at htc
        simp only [List.cons_append, shadowedTop.nested] at hn
        simp only [List.cons_append, mentionsBeforeDecl,
          Bool.or_eq_false_iff] at hm
        obtain ⟨i1, i2, i3⟩ := pre_facts (x := x) (pre := pre) hn htc hm.2
        exact ⟨by simp only [rnMStmts, Bool.or_eq_false_iff]
                  exact ⟨by simp [rnMStmt], i1⟩, i2, i3⟩
      all_goals (
        simp only [shadowedTop.topCount] at htc;
        simp only [List.cons_append, shadowedTop.nested,
          Bool.or_eq_false_iff] at hn;
        simp only [List.cons_append, mentionsBeforeDecl,
          Bool.or_eq_false_iff] at hm;
        obtain ⟨i1, i2, i3⟩ := pre_facts (x := x) (pre := pre) hn.2 htc hm.2;
        exact ⟨by simp only [rnMStmts, Bool.or_eq_false_iff]
                  exact ⟨rnMStmt_of_not_idents (by simpa using hm.1), i1⟩,
          i2, i3⟩)

/-- The declaring statement's initializer never reads `x` (it still refers
to the outer binding at that point). -/
theorem decl_facts {x : Ident} {xs : List Ident} {rhs : Option (Expr Op)}
    {suf : List (Stmt Op)}
    (hxs : xs.contains x = true)
    (hm : mentionsBeforeDecl x (.letDecl xs rhs :: suf) = false) :
    optExprMentions x rhs = false := by
  simp only [mentionsBeforeDecl] at hm
  rw [if_pos hxs] at hm
  cases rhs with
  | none => rfl
  | some e =>
      simp only [Option.map_some, Option.getD_some] at hm
      cases hexp : exprMentions x e with
      | false => simpa [optExprMentions] using hexp
      | true =>
          exact absurd (exprMentions_mem_idents hexp) (by simpa using hm)

/-- After the declaration, `x` is never redeclared. -/
theorem redecl_of_nested_top0 {x : Ident} : ∀ {suf : List (Stmt Op)},
    shadowedTop.nested x suf = false → shadowedTop.topCount x suf = 0 →
    redeclStmts x suf = false
  | [], _, _ => rfl
  | s :: suf, hn, htc => by
      cases s
      case letDecl xs rhs =>
        simp only [shadowedTop.topCount] at htc
        have hxs : xs.contains x = false := by
          by_cases hc : xs.contains x = true
          · rw [if_pos hc] at htc; omega
          · simpa using hc
        rw [if_neg (by simpa using hxs)] at htc
        simp only [shadowedTop.nested] at hn
        simp only [redeclStmts, Bool.or_eq_false_iff]
        refine ⟨?_, redecl_of_nested_top0 (x := x) hn (by omega)⟩
        simp only [redeclStmt]
        exact hxs
      case funDef n ps rs b =>
        simp only [shadowedTop.topCount] at htc
        simp only [shadowedTop.nested] at hn
        simp only [redeclStmts, Bool.or_eq_false_iff]
        exact ⟨by simp [redeclStmt], redecl_of_nested_top0 (x := x) hn htc⟩
      all_goals (
        simp only [shadowedTop.topCount] at htc;
        simp only [shadowedTop.nested, Bool.or_eq_false_iff] at hn;
        simp only [redeclStmts, Bool.or_eq_false_iff];
        exact ⟨hn.1, redecl_of_nested_top0 (x := x) hn.2 htc⟩)

/-- `topCount` distributes over append. -/
theorem topCount_append (x : Ident) : ∀ (a b : List (Stmt Op)),
    shadowedTop.topCount x (a ++ b) =
      shadowedTop.topCount x a + shadowedTop.topCount x b
  | [], b => by simp [shadowedTop.topCount]
  | s :: a, b => by
      cases s <;>
        simp [shadowedTop.topCount, topCount_append x a b, Nat.add_assoc]

/-- `renStmts` distributes over append. -/
theorem renStmts_append (x x' : Ident) : ∀ (a b : List (Stmt Op)),
    renStmts x x' (a ++ b) = renStmts x x' a ++ renStmts x x' b
  | [], _ => rfl
  | s :: a, b => by
      simp only [List.cons_append, renStmts, renStmts_append x x' a b]

/-- Renaming binder lists commutes with `zip`. -/
theorem renKeys_zip (x x' : Ident) : ∀ (xs : List Ident)
    (vals : List (evmWithExternal calls creates .any).Value),
    renKeys (calls := calls) (creates := creates) x x' (xs.zip vals) =
      (xs.map (renVar x x')).zip vals
  | [], _ => rfl
  | _ :: _, [] => rfl
  | y :: xs, v :: vals => by
      show (renVar x x' y, v) :: renKeys x x' (xs.zip vals) = _
      rw [renKeys_zip x x' xs vals]
      rfl

/-- Renaming binder lists commutes with zero-binding. -/
theorem renKeys_bindZeros (x x' : Ident) (xs : List Ident) :
    renKeys (calls := calls) (creates := creates) x x' (bindZeros D xs) =
      bindZeros D (xs.map (renVar x x')) := by
  simp [renKeys, bindZeros, List.map_map, Function.comp_def]

/-! ### The single-binder alpha rename, at block level -/

/-- Shape of the renamed sequence across the declaration split: the prefix
and the initializer are untouched, the binder list and the suffix are
renamed. -/
theorem renStmts_split_shape {x x' : Ident} {pre suf : List (Stmt Op)}
    {xs : List Ident} {rhs : Option (Expr Op)}
    (hpre : rnMStmts x pre = false) (hrhs : optExprMentions x rhs = false) :
    renStmts x x' (pre ++ .letDecl xs rhs :: suf) =
      pre ++ .letDecl (xs.map (renVar x x')) rhs :: renStmts x x' suf := by
  rw [renStmts_append, renStmts_id hpre]
  congr 1
  show renStmt x x' (.letDecl xs rhs) :: renStmts x x' suf = _
  congr 1
  show Stmt.letDecl (xs.map (renVar x x')) (rhs.map (renExpr x x')) = _
  congr 1
  cases rhs with
  | none => rfl
  | some e =>
      simpa [Option.map_some] using congrArg some
        (renExpr_id (by simpa [optExprMentions] using hrhs))

/-- Facts delivered by `shadowedTop x ss = false` across the split. -/
theorem split_guard_facts {x : Ident} {pre suf : List (Stmt Op)}
    {xs : List Ident} {rhs : Option (Expr Op)}
    (hsh : shadowedTop x (pre ++ .letDecl xs rhs :: suf) = false)
    (hxs : xs.contains x = true)
    (htcp : shadowedTop.topCount x pre = 0)
    (htcs : shadowedTop.topCount x suf = 0) :
    rnMStmts x pre = false ∧ optExprMentions x rhs = false ∧
      redeclStmts x suf = false := by
  obtain ⟨hn, _, hm⟩ := shadowedTop_false hsh
  obtain ⟨h1, h2, h3⟩ := pre_facts (x := x) (pre := pre) hn htcp hm
  refine ⟨h1, decl_facts hxs h3, ?_⟩
  have hnsuf : shadowedTop.nested x suf = false := by
    simpa [shadowedTop.nested] using h2
  exact redecl_of_nested_top0 (x := x) hnsuf htcs

/-- Freshness facts across the split. -/
theorem fresh_split_facts {x' : Ident} {pre suf : List (Stmt Op)}
    {xs : List Ident} {rhs : Option (Expr Op)}
    (hfr : stmtsMentions x' (pre ++ .letDecl xs rhs :: suf) = false) :
    x' ∉ xs ∧ stmtsMentions x' suf = false := by
  rw [stmtsMentions_append] at hfr
  simp only [Bool.or_eq_false_iff] at hfr
  have hd := hfr.2
  simp only [stmtsMentions, stmtMentions, Bool.or_eq_false_iff] at hd
  exact ⟨by simpa using hd.1.1, hd.2⟩

/-- Build the rename relation at a declaration site. -/
theorem rnRel_decl {x x' : Ident} {xs : List Ident} {C V₁ : VEnv D}
    (hkeys : C.map Prod.fst = xs) (hxs : xs.contains x = true)
    (hx' : x' ∉ xs) :
    RnRel x x' V₁.length (C ++ V₁) (renKeys x x' C ++ V₁) := by
  refine .mk C V₁ ?_ ?_ rfl
  · rw [find_key_isSome_iff, hkeys]
    simpa using hxs
  · intro p hp hc
    exact hx' (by
      rw [← hc, ← hkeys]
      exact List.mem_map_of_mem hp)

/-- **Forward rename walk**: a source run of the sequence yields a run of
the renamed sequence with the same state and outcome, and an environment
that restores identically to any prefix of the entry environment. -/
theorem renSeq_fwd {x x' : Ident} {ss : List (Stmt Op)}
    (hsh : shadowedTop x ss = false) (hfr : stmtsMentions x' ss = false)
    {funs : FunEnv D} {V : VEnv D} {st : EvmState} {Vb : VEnv D}
    {stb : EvmState} {o : Outcome}
    (h : Step D funs V st (.stmts ss) (.sres Vb stb o)) :
    ∃ Vb', Step D funs V st (.stmts (renStmts x x' ss)) (.sres Vb' stb o) ∧
      restore V Vb = restore V Vb' := by
  obtain ⟨hn, htc, hm⟩ := shadowedTop_false hsh
  rcases Nat.lt_or_ge (shadowedTop.topCount x ss) 1 with h0 | h1
  · -- no top-level declaration of x: x occurs nowhere, rename is identity
    have htc0 : shadowedTop.topCount x ss = 0 := by omega
    obtain ⟨hid, -, -⟩ := pre_facts (x := x) (pre := ss) (rest := [])
      (by simpa using hn) htc0 (by simpa using hm)
    rw [renStmts_id hid]
    exact ⟨Vb, h, rfl⟩
  · have htc1 : shadowedTop.topCount x ss = 1 := by omega
    obtain ⟨pre, xs, rhs, suf, rfl, hxs, htcp, htcs⟩ := topCount_one_split htc1
    obtain ⟨hpre, hrhs, hred⟩ := split_guard_facts hsh hxs htcp htcs
    obtain ⟨hx'xs, hfrsuf⟩ := fresh_split_facts hfr
    rw [renStmts_split_shape hpre hrhs]
    rcases stmts_append_fwd h with
      ⟨V₁, st₁, hpre_step, hrest⟩ | ⟨hne, hpre_step⟩
    · -- prefix ran to completion; the declaration is next
      have hVlen : V.length ≤ V₁.length := venvLen_mono hpre_step rfl
      cases hrest with
      | seqCons hdecl htail =>
          cases hdecl with
          | letZero =>
              have hR : RnRel x x' V₁.length (bindZeros D xs ++ V₁)
                  (renKeys x x' (bindZeros D xs) ++ V₁) :=
                rnRel_decl (by simp [bindZeros, Function.comp_def]) hxs hx'xs
              obtain ⟨res₂, htail₂, hrel⟩ := Step.rn_congr htail hR
                (rnMCode_of_mentions (code := .stmts suf) hfrsuf)
                (show codeRedecl x (.stmts suf) = false from hred)
              obtain ⟨Vb', rfl, hR'⟩ := hrel.sres_inv
              refine ⟨Vb', ?_, ?_⟩
              · refine stmts_append_normal hpre_step (Step.seqCons Step.letZero ?_)
                rw [renKeys_bindZeros] at htail₂
                exact htail₂
              · exact restore_rn_eq hR' hVlen
          | @letVal _ _ _ _ e vals st₂ hev hlen =>
              have hR : RnRel x x' V₁.length (xs.zip vals ++ V₁)
                  (renKeys x x' (xs.zip vals) ++ V₁) :=
                rnRel_decl (List.map_fst_zip (l₂ := vals) (by omega)) hxs hx'xs
              obtain ⟨res₂, htail₂, hrel⟩ := Step.rn_congr htail hR
                (rnMCode_of_mentions (code := .stmts suf) hfrsuf)
                (show codeRedecl x (.stmts suf) = false from hred)
              obtain ⟨Vb', rfl, hR'⟩ := hrel.sres_inv
              refine ⟨Vb', ?_, ?_⟩
              · refine stmts_append_normal hpre_step (Step.seqCons
                  (Step.letVal hev (by simpa using hlen)) ?_)
                rw [renKeys_zip] at htail₂
                exact htail₂
              · exact restore_rn_eq hR' hVlen
      | seqStop hdecl hne =>
          cases hdecl with
          | letZero => exact absurd rfl hne
          | letVal hev hlen => exact absurd rfl hne
          | letHalt hev =>
              refine ⟨Vb, ?_, rfl⟩
              exact stmts_append_normal hpre_step
                (Step.seqStop (Step.letHalt hev) hne)
    · -- the prefix stopped early: it is untouched by the rename
      exact ⟨Vb, stmts_append_early hpre_step hne, rfl⟩

/-- **Backward rename walk**: a run of the renamed sequence yields a source
run with the same state and outcome, and a restore-equal environment. -/
theorem renSeq_bwd {x x' : Ident} (hxx' : x ≠ x') {ss : List (Stmt Op)}
    (hsh : shadowedTop x ss = false) (hfr : stmtsMentions x' ss = false)
    {funs : FunEnv D} {V : VEnv D} {st : EvmState} {Vb' : VEnv D}
    {stb : EvmState} {o : Outcome}
    (h : Step D funs V st (.stmts (renStmts x x' ss)) (.sres Vb' stb o)) :
    ∃ Vb, Step D funs V st (.stmts ss) (.sres Vb stb o) ∧
      restore V Vb = restore V Vb' := by
  obtain ⟨hn, htc, hm⟩ := shadowedTop_false hsh
  rcases Nat.lt_or_ge (shadowedTop.topCount x ss) 1 with h0 | h1
  · have htc0 : shadowedTop.topCount x ss = 0 := by omega
    obtain ⟨hid, -, -⟩ := pre_facts (x := x) (pre := ss) (rest := [])
      (by simpa using hn) htc0 (by simpa using hm)
    rw [renStmts_id hid] at h
    exact ⟨Vb', h, rfl⟩
  · have htc1 : shadowedTop.topCount x ss = 1 := by omega
    obtain ⟨pre, xs, rhs, suf, rfl, hxs, htcp, htcs⟩ := topCount_one_split htc1
    obtain ⟨hpre, hrhs, hred⟩ := split_guard_facts hsh hxs htcp htcs
    obtain ⟨hx'xs, hfrsuf⟩ := fresh_split_facts hfr
    rw [renStmts_split_shape hpre hrhs] at h
    rcases stmts_append_fwd h with
      ⟨V₁, st₁, hpre_step, hrest⟩ | ⟨hne, hpre_step⟩
    · have hVlen : V.length ≤ V₁.length := venvLen_mono hpre_step rfl
      cases hrest with
      | seqCons hdecl htail =>
          cases hdecl with
          | letZero =>
              rw [← renKeys_bindZeros] at htail
              have hR : RnRel x x' V₁.length (bindZeros D xs ++ V₁)
                  (renKeys x x' (bindZeros D xs) ++ V₁) :=
                rnRel_decl (by simp [bindZeros, Function.comp_def]) hxs hx'xs
              obtain ⟨res₁, htail₁, hrel⟩ := Step.rn_congr_bwd hxx'
                (code := .stmts suf) htail hR hfrsuf
                (show codeRedecl x (.stmts suf) = false from hred)
              obtain ⟨Vb, rfl, hR'⟩ := hrel.sres_inv_right
              refine ⟨Vb, ?_, restore_rn_eq hR' hVlen⟩
              exact stmts_append_normal hpre_step
                (Step.seqCons Step.letZero htail₁)
          | @letVal _ _ _ _ e vals st₂ hev hlen =>
              rw [← renKeys_zip] at htail
              have hR : RnRel x x' V₁.length (xs.zip vals ++ V₁)
                  (renKeys x x' (xs.zip vals) ++ V₁) :=
                rnRel_decl (List.map_fst_zip (l₂ := vals)
                  (by simpa using hlen.symm.le)) hxs hx'xs
              obtain ⟨res₁, htail₁, hrel⟩ := Step.rn_congr_bwd hxx'
                (code := .stmts suf) htail hR hfrsuf
                (show codeRedecl x (.stmts suf) = false from hred)
              obtain ⟨Vb, rfl, hR'⟩ := hrel.sres_inv_right
              refine ⟨Vb, ?_, restore_rn_eq hR' hVlen⟩
              exact stmts_append_normal hpre_step
                (Step.seqCons (Step.letVal hev (by simpa using hlen)) htail₁)
      | seqStop hdecl hne =>
          cases hdecl with
          | letZero => exact absurd rfl hne
          | letVal hev hlen => exact absurd rfl hne
          | letHalt hev =>
              refine ⟨Vb', ?_, rfl⟩
              exact stmts_append_normal hpre_step
                (Step.seqStop (Step.letHalt hev) hne)
    · exact ⟨Vb', stmts_append_early hpre_step hne, rfl⟩

/-- **Single-binder alpha conversion at block level.** -/
theorem renBlock_equiv {x x' : Ident} (hxx' : x ≠ x') {ss : List (Stmt Op)}
    (hsh : shadowedTop x ss = false) (hfr : stmtsMentions x' ss = false) :
    EquivStmt D (.block ss) (.block (renStmts x x' ss)) := by
  intro funs V st V' st' o
  constructor
  · intro h
    cases h with
    | block hb =>
        obtain ⟨Vb', hb', heq⟩ := renSeq_fwd hsh hfr hb
        rw [heq]
        exact Step.block (by rw [renStmts_hoist]; exact hb')
  · intro h
    cases h with
    | block hb =>
        rw [renStmts_hoist] at hb
        obtain ⟨Vb, hb', heq⟩ := renSeq_bwd hxx' hsh hfr hb
        rw [← heq]
        exact Step.block hb'

/-! ### `renameAll`: a fold of single-binder alpha conversions -/

theorem renameAll_go_equiv (P : String) : ∀ (binders : List Ident)
    (ss : List (Stmt Op)) (c : Nat) {ss' : List (Stmt Op)} {c' : Nat},
    renameAll.go P binders ss c = some (ss', c') →
    EquivStmt D (.block ss) (.block ss')
  | [], ss, c, ss', c', h => by
      simp only [renameAll.go, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact EquivStmt.refl _
  | y :: rest, ss, c, ss', c', h => by
      simp only [renameAll.go] at h
      by_cases hg : (shadowedTop y ss || y == s!"{P}{c}" ||
          stmtsMentions s!"{P}{c}" ss) = true
      · rw [if_pos hg] at h
        exact absurd h (by simp)
      · rw [if_neg hg] at h
        simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hg
        obtain ⟨⟨hsh, hne⟩, hfr⟩ := hg
        exact (renBlock_equiv (by simpa using hne) hsh hfr).trans
          (renameAll_go_equiv P rest _ (c + 1) h)

theorem renameAll_go_hoist (P : String) : ∀ (binders : List Ident)
    (ss : List (Stmt Op)) (c : Nat) {ss' : List (Stmt Op)} {c' : Nat},
    renameAll.go P binders ss c = some (ss', c') →
    hoist D ss' = hoist D ss
  | [], ss, c, ss', c', h => by
      simp only [renameAll.go, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
  | y :: rest, ss, c, ss', c', h => by
      simp only [renameAll.go] at h
      by_cases hg : (shadowedTop y ss || y == s!"{P}{c}" ||
          stmtsMentions s!"{P}{c}" ss) = true
      · rw [if_pos hg] at h
        exact absurd h (by simp)
      · rw [if_neg hg] at h
        rw [renameAll_go_hoist P rest _ (c + 1) h, renStmts_hoist]

/-- A sequence without top-level function definitions hoists nothing. -/
theorem hoist_nil_of_no_topFunDef : ∀ {ss : List (Stmt Op)},
    hasTopFunDef ss = false → hoist D ss = []
  | [], _ => rfl
  | s :: rest, h => by
      cases s
      case funDef n ps rs b => exact absurd h (by simp [hasTopFunDef])
      all_goals
        exact hoist_nil_of_no_topFunDef (ss := rest)
          (by simpa [hasTopFunDef] using h)

theorem InsRes.sres_inv {n : Nat} {V₁ : VEnv D} {st : EvmState} {o : Outcome}
    {res₂ : Res D} (h : InsRes n (.sres V₁ st o) res₂) :
    ∃ V₂, res₂ = .sres V₂ st o ∧ InsChain n V₁ V₂ := by
  cases res₂ with
  | eres => exact h.elim
  | sres V₂ st₂ o₂ =>
      obtain ⟨hc, rfl, rfl⟩ := h
      exact ⟨V₂, rfl, hc⟩

/-! ### The splice, forward -/

/-- A run of the input sequence yields a run of the spliced sequence: same
state and outcome, with the promoted bindings as extra insertions at entry
depth (erased by the enclosing block's `restore`). -/
theorem spliceSeq_fwd (P : String) : ∀ (ss : List (Stmt Op)) (c : Nat)
    {funs : FunEnv D} {V : VEnv D} {st : EvmState} {Vb : VEnv D}
    {stb : EvmState} {o : Outcome},
    Step D funs V st (.stmts ss) (.sres Vb stb o) →
    ∃ Vb', Step D funs V st (.stmts (spliceSeq P ss c).1) (.sres Vb' stb o) ∧
      InsChain V.length Vb Vb'
  | [], c, funs, V, st, Vb, stb, o, h => ⟨Vb, h, .refl _⟩
  | s :: rest, c, funs, V, st, Vb, stb, o, h => by
      cases s
      case block inner =>
          by_cases hf : hasTopFunDef inner = true
          · -- kept as-is
            rcases hsp : spliceSeq P rest c with ⟨rest', c'⟩
            rw [show (spliceSeq P (.block inner :: rest) c).1 =
              .block inner :: rest' from by simp [spliceSeq, hf, hsp]]
            cases h with
            | seqCons hs htail =>
                obtain ⟨Vb', htail', hchain⟩ := spliceSeq_fwd P rest c htail
                rw [hsp] at htail'
                exact ⟨Vb', Step.seqCons hs htail',
                  hchain.mono (venvLen_mono hs rfl)⟩
            | seqStop hs hne => exact ⟨Vb, Step.seqStop hs hne, .refl _⟩
          · rcases hren : renameAll P c (topDecls inner) inner with _ | ⟨inner', c'⟩
            · -- rename declined
              rcases hsp : spliceSeq P rest c with ⟨rest', c'⟩
              rw [show (spliceSeq P (.block inner :: rest) c).1 =
                .block inner :: rest' from by simp [spliceSeq, hf, hren, hsp]]
              cases h with
              | seqCons hs htail =>
                  obtain ⟨Vb', htail', hchain⟩ := spliceSeq_fwd P rest c htail
                  rw [hsp] at htail'
                  exact ⟨Vb', Step.seqCons hs htail',
                    hchain.mono (venvLen_mono hs rfl)⟩
              | seqStop hs hne => exact ⟨Vb, Step.seqStop hs hne, .refl _⟩
            · rcases hsp : spliceSeq P rest c' with ⟨rest', c''⟩
              by_cases hall : (topDecls inner').all
                  (fun y => !stmtsMentions y rest') = true
              · -- the splice
                rw [show (spliceSeq P (.block inner :: rest) c).1 =
                  inner' ++ rest' from by simp [spliceSeq, hf, hren, hsp, hall]]
                simp only [renameAll] at hren
                have hequiv := renameAll_go_equiv (calls := calls)
                  (creates := creates) P (topDecls inner) inner c hren
                have hhoist : hoist D inner' = [] := by
                  rw [renameAll_go_hoist P (topDecls inner) inner c hren]
                  exact hoist_nil_of_no_topFunDef (by simpa using hf)
                cases h with
                | seqCons hblk htail =>
                    have hblk' := (hequiv funs V st _ _ _).mp hblk
                    cases hblk' with
                    | @block _ _ _ _ Vb₀ _ _ hb' =>
                        rw [hhoist] at hb'
                        have hb'' : Step D funs V st (.stmts inner')
                            (.sres Vb₀ _ .normal) :=
                          Step.emptyScope_congr hb' (.drop _)
                        have hlen0 : V.length ≤ Vb₀.length :=
                          venvLen_mono hb'' rfl
                        have hVb₀ : Vb₀ = Vb₀.take (Vb₀.length - V.length) ++
                            restore V Vb₀ :=
                          (List.take_append_drop _ _).symm
                        obtain ⟨Vr', htail', hchain⟩ :=
                          spliceSeq_fwd P rest c' htail
                        rw [hsp] at htail'
                        have hments : ∀ p ∈ Vb₀.take (Vb₀.length - V.length),
                            codeMentions p.1 (Code.stmts rest') = false := by
                          intro p hp
                          have hpd := step_stmts_new_keys hb'' p hp
                          have hy := List.all_eq_true.mp hall p.1 hpd
                          show stmtsMentions p.1 rest' = false
                          simpa using hy
                        obtain ⟨res₂, hrest₂, hres⟩ := frameAddAll htail' _ hments
                        obtain ⟨Vr'', rfl, hchain₂⟩ := hres.sres_inv
                        rw [← hVb₀] at hrest₂
                        refine ⟨Vr'', stmts_append_normal hb'' hrest₂, ?_⟩
                        have hVlen : (restore V Vb₀).length = V.length :=
                          restore_length hlen0
                        rw [hVlen] at hchain hchain₂
                        exact hchain.trans hchain₂
                | seqStop hblk hne =>
                    have hblk' := (hequiv funs V st _ _ _).mp hblk
                    cases hblk' with
                    | @block _ _ _ _ Vb₀ _ _ hb' =>
                        rw [hhoist] at hb'
                        have hb'' : Step D funs V st (.stmts inner')
                            (.sres Vb₀ _ _) :=
                          Step.emptyScope_congr hb' (.drop _)
                        have hlen0 : V.length ≤ Vb₀.length :=
                          venvLen_mono hb'' rfl
                        refine ⟨Vb₀, stmts_append_early hb'' hne, ?_⟩
                        have hVb₀ : Vb₀ = Vb₀.take (Vb₀.length - V.length) ++
                            restore V Vb₀ :=
                          (List.take_append_drop _ _).symm
                        have hpre := insChain_prepend
                          (Vb₀.take (Vb₀.length - V.length)) (restore V Vb₀)
                        rw [restore_length hlen0, ← hVb₀] at hpre
                        exact hpre
              · -- splice declined by the mention check
                rw [show (spliceSeq P (.block inner :: rest) c).1 =
                  .block inner :: rest' from by simp [spliceSeq, hf, hren, hsp, hall]]
                cases h with
                | seqCons hs htail =>
                    obtain ⟨Vb', htail', hchain⟩ := spliceSeq_fwd P rest c' htail
                    rw [hsp] at htail'
                    exact ⟨Vb', Step.seqCons hs htail',
                      hchain.mono (venvLen_mono hs rfl)⟩
                | seqStop hs hne => exact ⟨Vb, Step.seqStop hs hne, .refl _⟩
      all_goals (
        rcases hsp : spliceSeq P rest c with ⟨rest', c'⟩;
        simp only [spliceSeq, hsp];
        cases h with
        | seqCons hs htail =>
            obtain ⟨Vb', htail', hchain⟩ := spliceSeq_fwd P rest c htail
            rw [hsp] at htail'
            exact ⟨Vb', Step.seqCons hs htail',
              hchain.mono (venvLen_mono hs rfl)⟩
        | seqStop hs hne => exact ⟨Vb, Step.seqStop hs hne, .refl _⟩)
theorem InsRes.sres_inv_right {n : Nat} {res₁ : Res D} {V₂ : VEnv D}
    {st : EvmState} {o : Outcome} (h : InsRes n res₁ (.sres V₂ st o)) :
    ∃ V₁, res₁ = .sres V₁ st o ∧ InsChain n V₁ V₂ := by
  cases res₁ with
  | eres => exact h.elim
  | sres V₁ st₁ o₁ =>
      obtain ⟨hc, rfl, rfl⟩ := h
      exact ⟨V₁, rfl, hc⟩

/-! ### The splice, backward -/

theorem spliceSeq_bwd (P : String) : ∀ (ss : List (Stmt Op)) (c : Nat)
    {funs : FunEnv D} {V : VEnv D} {st : EvmState} {Vb' : VEnv D}
    {stb : EvmState} {o : Outcome},
    Step D funs V st (.stmts (spliceSeq P ss c).1) (.sres Vb' stb o) →
    ∃ Vb, Step D funs V st (.stmts ss) (.sres Vb stb o) ∧
      InsChain V.length Vb Vb'
  | [], c, funs, V, st, Vb', stb, o, h => ⟨Vb', h, .refl _⟩
  | s :: rest, c, funs, V, st, Vb', stb, o, h => by
      cases s
      case block inner =>
        by_cases hf : hasTopFunDef inner = true
        · rcases hsp : spliceSeq P rest c with ⟨rest', c'⟩
          rw [show (spliceSeq P (.block inner :: rest) c).1 =
            .block inner :: rest' from by simp [spliceSeq, hf, hsp]] at h
          cases h with
          | seqCons hs htail =>
              obtain ⟨Vb, htail₁, hchain⟩ := spliceSeq_bwd P rest c
                (by rw [hsp]; exact htail)
              exact ⟨Vb, Step.seqCons hs htail₁,
                hchain.mono (venvLen_mono hs rfl)⟩
          | seqStop hs hne => exact ⟨Vb', Step.seqStop hs hne, .refl _⟩
        · rcases hren : renameAll P c (topDecls inner) inner
            with _ | ⟨inner', c'⟩
          · rcases hsp : spliceSeq P rest c with ⟨rest', c'⟩
            rw [show (spliceSeq P (.block inner :: rest) c).1 =
              .block inner :: rest' from by simp [spliceSeq, hf, hren, hsp]] at h
            cases h with
            | seqCons hs htail =>
                obtain ⟨Vb, htail₁, hchain⟩ := spliceSeq_bwd P rest c
                  (by rw [hsp]; exact htail)
                exact ⟨Vb, Step.seqCons hs htail₁,
                  hchain.mono (venvLen_mono hs rfl)⟩
            | seqStop hs hne => exact ⟨Vb', Step.seqStop hs hne, .refl _⟩
          · rcases hsp : spliceSeq P rest c' with ⟨rest', c''⟩
            by_cases hall : (topDecls inner').all
                (fun y => !stmtsMentions y rest') = true
            · rw [show (spliceSeq P (.block inner :: rest) c).1 =
                inner' ++ rest' from by simp [spliceSeq, hf, hren, hsp, hall]] at h
              simp only [renameAll] at hren
              have hequiv := renameAll_go_equiv (calls := calls)
                (creates := creates) P (topDecls inner) inner c hren
              have hhoist : hoist D inner' = [] := by
                rw [renameAll_go_hoist P (topDecls inner) inner c hren]
                exact hoist_nil_of_no_topFunDef (by simpa using hf)
              rcases stmts_append_fwd h with
                ⟨V₂, st₁, hin, hrest'⟩ | ⟨hne, hin⟩
              · have hlen0 : V.length ≤ V₂.length := venvLen_mono hin rfl
                have hV₂ : V₂ = V₂.take (V₂.length - V.length) ++
                    restore V V₂ :=
                  (List.take_append_drop _ _).symm
                have hments : ∀ p ∈ V₂.take (V₂.length - V.length),
                    codeMentions p.1 (Code.stmts rest') = false := by
                  intro p hp
                  have hpd := step_stmts_new_keys hin p hp
                  have hy := List.all_eq_true.mp hall p.1 hpd
                  show stmtsMentions p.1 rest' = false
                  simpa using hy
                rw [hV₂] at hrest'
                obtain ⟨res₁, hrest₁, hres⟩ := frameRemoveAll _ hrest' hments
                obtain ⟨Vr₁, rfl, hchain₂⟩ := hres.sres_inv_right
                obtain ⟨Vb, htail₁, hchain⟩ := spliceSeq_bwd P rest c'
                  (by rw [hsp]; exact hrest₁)
                have hb' : Step D (hoist D inner' :: funs) V st
                    (.stmts inner') (.sres V₂ st₁ .normal) := by
                  rw [hhoist]
                  exact Step.emptyScope_congr hin (.add _)
                have hblk := (hequiv funs V st _ _ _).mpr (Step.block hb')
                refine ⟨Vb, Step.seqCons hblk htail₁, ?_⟩
                have hVlen : (restore V V₂).length = V.length :=
                  restore_length hlen0
                rw [hVlen] at hchain hchain₂
                exact hchain.trans hchain₂
              · have hb' : Step D (hoist D inner' :: funs) V st
                    (.stmts inner') (.sres Vb' stb o) := by
                  rw [hhoist]
                  exact Step.emptyScope_congr hin (.add _)
                have hblk := (hequiv funs V st _ _ _).mpr (Step.block hb')
                refine ⟨restore V Vb', Step.seqStop hblk hne, ?_⟩
                have hlen0 : V.length ≤ Vb'.length := venvLen_mono hin rfl
                have hVb' : Vb' = Vb'.take (Vb'.length - V.length) ++
                    restore V Vb' :=
                  (List.take_append_drop _ _).symm
                have hpre := insChain_prepend
                  (Vb'.take (Vb'.length - V.length)) (restore V Vb')
                rw [restore_length hlen0, ← hVb'] at hpre
                exact hpre
            · rcases hsp2 : spliceSeq P rest c' with ⟨rest2, c2⟩
              rw [show (spliceSeq P (.block inner :: rest) c).1 =
                .block inner :: rest' from by
                  simp [spliceSeq, hf, hren, hsp, hall]] at h
              cases h with
              | seqCons hs htail =>
                  obtain ⟨Vb, htail₁, hchain⟩ := spliceSeq_bwd P rest c'
                    (by rw [hsp]; exact htail)
                  exact ⟨Vb, Step.seqCons hs htail₁,
                    hchain.mono (venvLen_mono hs rfl)⟩
              | seqStop hs hne => exact ⟨Vb', Step.seqStop hs hne, .refl _⟩
      all_goals (
        rcases hsp : spliceSeq P rest c with ⟨rest', c'⟩;
        simp only [spliceSeq, hsp] at h;
        cases h with
        | seqCons hs htail =>
            obtain ⟨Vb, htail₁, hchain⟩ := spliceSeq_bwd P rest c
              (by rw [hsp]; exact htail)
            exact ⟨Vb, Step.seqCons hs htail₁,
              hchain.mono (venvLen_mono hs rfl)⟩
        | seqStop hs hne => exact ⟨Vb', Step.seqStop hs hne, .refl _⟩)

/-! ### Assembly: splice as a block rewrite, and the structural lifting -/

theorem spliceSeq_hoist (P : String) : ∀ (ss : List (Stmt Op)) (c : Nat),
    hoist D (spliceSeq P ss c).1 = hoist D ss
  | [], _ => rfl
  | s :: rest, c => by
      cases s
      case block inner =>
        by_cases hf : hasTopFunDef inner = true
        · rcases hsp : spliceSeq P rest c with ⟨rest', c'⟩
          rw [show (spliceSeq P (.block inner :: rest) c).1 =
            .block inner :: rest' from by simp [spliceSeq, hf, hsp]]
          have ih := spliceSeq_hoist P rest c
          rw [hsp] at ih
          simpa [hoist] using ih
        · rcases hren : renameAll P c (topDecls inner) inner
            with _ | ⟨inner', c'⟩
          · rcases hsp : spliceSeq P rest c with ⟨rest', c'⟩
            rw [show (spliceSeq P (.block inner :: rest) c).1 =
              .block inner :: rest' from by simp [spliceSeq, hf, hren, hsp]]
            have ih := spliceSeq_hoist P rest c
            rw [hsp] at ih
            simpa [hoist] using ih
          · rcases hsp : spliceSeq P rest c' with ⟨rest', c''⟩
            by_cases hall : (topDecls inner').all
                (fun y => !stmtsMentions y rest') = true
            · rw [show (spliceSeq P (.block inner :: rest) c).1 =
                inner' ++ rest' from by simp [spliceSeq, hf, hren, hsp, hall]]
              have hhoist : hoist D inner' = [] := by
                simp only [renameAll] at hren
                rw [renameAll_go_hoist P (topDecls inner) inner c hren]
                exact hoist_nil_of_no_topFunDef (by simpa using hf)
              have ih := spliceSeq_hoist P rest c'
              rw [hsp] at ih
              rw [YulEvmCompiler.Optimizer.hoist_append, hhoist,
                List.nil_append, ih]
              simp [hoist]
            · rw [show (spliceSeq P (.block inner :: rest) c).1 =
                .block inner :: rest' from by
                  simp [spliceSeq, hf, hren, hsp, hall]]
              have ih := spliceSeq_hoist P rest c'
              rw [hsp] at ih
              simpa [hoist] using ih
      all_goals (
        rcases hsp : spliceSeq P rest c with ⟨rest', c'⟩;
        simp only [spliceSeq, hsp];
        have ih := spliceSeq_hoist P rest c;
        rw [hsp] at ih;
        simpa [hoist] using ih)

/-- The splice pass is a sound block rewrite. -/
theorem spliceSeq_blockEquiv (P : String) (ss : List (Stmt Op)) (c : Nat) :
    EquivBlock D ss (spliceSeq P ss c).1 := by
  intro funs V st V' st' o
  constructor
  · intro h
    cases h with
    | block hb =>
        obtain ⟨Vb', hb', hchain⟩ := spliceSeq_fwd P ss c hb
        rw [← hchain.restore_eq]
        exact Step.block (by rw [spliceSeq_hoist]; exact hb')
  · intro h
    cases h with
    | block hb =>
        rw [spliceSeq_hoist] at hb
        obtain ⟨Vb, hb', hchain⟩ := spliceSeq_bwd P ss c hb
        rw [hchain.restore_eq]
        exact Step.block hb'

/- Projection equations for the counter-threaded sweep (the definitions are
compiled through destructuring `let`s, so the pair components are exposed
via explicit equations). -/

theorem flStmts_eq (P : String) (body : List (Stmt Op)) (c : Nat) :
    flStmts P body c =
      spliceSeq P (flEach P body c).1 (flEach P body c).2 := by
  unfold flStmts
  rcases h : flEach P body c with ⟨b, c'⟩
  simp

theorem flStmt_block (P : String) (body : List (Stmt Op)) (c : Nat) :
    flStmt P (.block body) c =
      (.block (flStmts P body c).1, (flStmts P body c).2) := by
  unfold flStmt
  rcases h : flStmts P body c with ⟨b, c'⟩
  simp

theorem flStmt_funDef (P : String) (n : Ident) (ps rs : List Ident)
    (body : List (Stmt Op)) (c : Nat) :
    flStmt P (.funDef n ps rs body) c =
      (.funDef n ps rs (flStmts P body c).1, (flStmts P body c).2) := by
  unfold flStmt
  rcases h : flStmts P body c with ⟨b, c'⟩
  simp

theorem flStmt_cond (P : String) (e : Expr Op) (body : List (Stmt Op))
    (c : Nat) :
    flStmt P (.cond e body) c =
      (.cond e (flStmts P body c).1, (flStmts P body c).2) := by
  unfold flStmt
  rcases h : flStmts P body c with ⟨b, c'⟩
  simp

theorem flStmt_switch (P : String) (e : Expr Op)
    (cs : List (Literal × Block Op)) (dflt : Option (Block Op)) (c : Nat) :
    flStmt P (.switch e cs dflt) c =
      (.switch e (flCases P cs c).1
        (flDflt P dflt (flCases P cs c).2).1,
       (flDflt P dflt (flCases P cs c).2).2) := by
  unfold flStmt
  rcases h1 : flCases P cs c with ⟨cs', c1⟩
  rcases h2 : flDflt P dflt c1 with ⟨d', c2⟩
  simp [h2]

theorem flStmt_forLoop (P : String) (init : List (Stmt Op)) (e : Expr Op)
    (post body : List (Stmt Op)) (c : Nat) :
    flStmt P (.forLoop init e post body) c =
      (.forLoop init e (flStmts P post c).1
        (flStmts P body (flStmts P post c).2).1,
       (flStmts P body (flStmts P post c).2).2) := by
  unfold flStmt
  rcases h1 : flStmts P post c with ⟨p', c1⟩
  rcases h2 : flStmts P body c1 with ⟨b', c2⟩
  simp [h2]

theorem flEach_cons (P : String) (s : Stmt Op) (rest : List (Stmt Op))
    (c : Nat) :
    flEach P (s :: rest) c =
      ((flStmt P s c).1 :: (flEach P rest (flStmt P s c).2).1,
       (flEach P rest (flStmt P s c).2).2) := by
  conv_lhs => unfold flEach

theorem flCases_cons (P : String) (l : Literal) (b : List (Stmt Op))
    (rest : List (Literal × Block Op)) (c : Nat) :
    flCases P ((l, b) :: rest) c =
      ((l, (flStmts P b c).1) :: (flCases P rest (flStmts P b c).2).1,
       (flCases P rest (flStmts P b c).2).2) := by
  conv_lhs => unfold flCases

theorem flDflt_none (P : String) (c : Nat) :
    flDflt P (none : Option (Block Op)) c = (none, c) := by
  unfold flDflt
  rfl

theorem flDflt_some (P : String) (b : List (Stmt Op)) (c : Nat) :
    flDflt P (some b) c =
      (some (flStmts P b c).1, (flStmts P b c).2) := by
  unfold flDflt
  rcases h : flStmts P b c with ⟨b', c'⟩
  simp

mutual

theorem flStmt_equiv (P : String) : ∀ (s : Stmt Op) (c : Nat),
    EquivStmt D s (flStmt P s c).1
  | .block body, c => by
      rw [flStmt_block]
      show EquivBlock D body (flStmts P body c).1
      rw [flStmts_eq]
      exact (EquivBlock.of_stmts_funs
        (EquivStmts.of_forall₂ (flEach_forall2 P body c))
        (flScopeRel P body c)).trans
        (spliceSeq_blockEquiv P (flEach P body c).1 (flEach P body c).2)
  | .funDef n ps rs body, c => by
      rw [flStmt_funDef]
      intro funs V st V' st' o
      constructor
      · intro h; cases h; exact Step.funDef
      · intro h; cases h; exact Step.funDef
  | .cond e body, c => by
      rw [flStmt_cond]
      refine EquivStmt.cond_congr
        (@EquivExpr.refl (evmWithExternal calls creates .any) _ e) ?_
      rw [flStmts_eq]
      exact (EquivBlock.of_stmts_funs
        (EquivStmts.of_forall₂ (flEach_forall2 P body c))
        (flScopeRel P body c)).trans
        (spliceSeq_blockEquiv P (flEach P body c).1 (flEach P body c).2)
  | .switch e cases dflt, c => by
      rw [flStmt_switch]
      refine EquivStmt.switch_congr
        (@EquivExpr.refl (evmWithExternal calls creates .any) _ e)
        (flCases_forall2 P cases c) ?_
      cases dflt with
      | none =>
          rw [flDflt_none]
          exact @EquivBlock.refl (evmWithExternal calls creates .any) _ _
      | some b =>
          rw [flDflt_some]
          show EquivBlock D b (flStmts P b (flCases P cases c).2).1
          rw [flStmts_eq]
          exact (EquivBlock.of_stmts_funs
            (EquivStmts.of_forall₂
              (flEach_forall2 P b (flCases P cases c).2))
            (flScopeRel P b (flCases P cases c).2)).trans
            (spliceSeq_blockEquiv P
              (flEach P b (flCases P cases c).2).1
              (flEach P b (flCases P cases c).2).2)
  | .forLoop init e post body, c => by
      rw [flStmt_forLoop]
      refine EquivStmt.forLoop_congr init
        (@EquivExpr.refl (evmWithExternal calls creates .any) _ e) ?_ ?_
      · rw [flStmts_eq]
        exact (EquivBlock.of_stmts_funs
          (EquivStmts.of_forall₂ (flEach_forall2 P post c))
          (flScopeRel P post c)).trans
          (spliceSeq_blockEquiv P (flEach P post c).1 (flEach P post c).2)
      · rw [flStmts_eq]
        exact (EquivBlock.of_stmts_funs
          (EquivStmts.of_forall₂
            (flEach_forall2 P body (flStmts P post c).2))
          (flScopeRel P body (flStmts P post c).2)).trans
          (spliceSeq_blockEquiv P
            (flEach P body (flStmts P post c).2).1
            (flEach P body (flStmts P post c).2).2)
  | .letDecl xs v, c => by
      unfold flStmt
      exact @EquivStmt.refl (evmWithExternal calls creates .any) _ _
  | .assign xs e, c => by
      unfold flStmt
      exact @EquivStmt.refl (evmWithExternal calls creates .any) _ _
  | .exprStmt e, c => by
      unfold flStmt
      exact @EquivStmt.refl (evmWithExternal calls creates .any) _ _
  | .«break», c => by
      unfold flStmt
      exact @EquivStmt.refl (evmWithExternal calls creates .any) _ _
  | .«continue», c => by
      unfold flStmt
      exact @EquivStmt.refl (evmWithExternal calls creates .any) _ _
  | .leave, c => by
      unfold flStmt
      exact @EquivStmt.refl (evmWithExternal calls creates .any) _ _

theorem flEach_forall2 (P : String) : ∀ (ss : List (Stmt Op)) (c : Nat),
    Forall₂ (EquivStmt D) ss (flEach P ss c).1
  | [], _ => by
      unfold flEach
      exact .nil
  | s :: rest, c => by
      rw [flEach_cons]
      exact .cons (flStmt_equiv P s c)
        (flEach_forall2 P rest (flStmt P s c).2)

theorem flCases_forall2 (P : String) :
    ∀ (cs : List (Literal × Block Op)) (c : Nat),
    Forall₂ (fun p q => p.1 = q.1 ∧ EquivBlock D p.2 q.2) cs
      (flCases P cs c).1
  | [], _ => by
      unfold flCases
      exact .nil
  | (l, b) :: rest, c => by
      rw [flCases_cons]
      refine .cons ⟨rfl, ?_⟩ (flCases_forall2 P rest (flStmts P b c).2)
      show EquivBlock D b (flStmts P b c).1
      rw [flStmts_eq]
      exact (EquivBlock.of_stmts_funs
        (EquivStmts.of_forall₂ (flEach_forall2 P b c))
        (flScopeRel P b c)).trans
        (spliceSeq_blockEquiv P (flEach P b c).1 (flEach P b c).2)

theorem flScopeRel (P : String) : ∀ (ss : List (Stmt Op)) (c : Nat),
    ScopeRel D (hoist D ss) (hoist D (flEach P ss c).1)
  | [], _ => by
      unfold flEach
      exact .nil
  | .funDef n ps rs body :: rest, c => by
      rw [flEach_cons, flStmt_funDef]
      dsimp only
      simp only [hoist, List.filterMap_cons]
      refine List.Forall₂.cons ⟨rfl, rfl, rfl, ?_⟩
        (flScopeRel P rest (flStmts P body c).2)
      show EquivBlock D body (flStmts P body c).1
      rw [flStmts_eq]
      exact (EquivBlock.of_stmts_funs
        (EquivStmts.of_forall₂ (flEach_forall2 P body c))
        (flScopeRel P body c)).trans
        (spliceSeq_blockEquiv P (flEach P body c).1 (flEach P body c).2)
  | .block body :: rest, c => by
      rw [flEach_cons, flStmt_block]
      dsimp only
      simpa [hoist] using flScopeRel P rest (flStmts P body c).2
  | .letDecl xs v :: rest, c => by
      rw [flEach_cons]
      show ScopeRel D _ (hoist D ((flStmt P (.letDecl xs v) c).1 :: _))
      rw [show (flStmt P (.letDecl xs v) c).1 = .letDecl xs v from by
        unfold flStmt; rfl]
      simpa [hoist] using flScopeRel P rest (flStmt P (.letDecl xs v) c).2
  | .assign xs e :: rest, c => by
      rw [flEach_cons]
      rw [show (flStmt P (.assign xs e) c).1 = .assign xs e from by
        unfold flStmt; rfl]
      simpa [hoist] using flScopeRel P rest (flStmt P (.assign xs e) c).2
  | .cond e body :: rest, c => by
      rw [flEach_cons, flStmt_cond]
      dsimp only
      simpa [hoist] using flScopeRel P rest (flStmts P body c).2
  | .«switch» e cs dflt :: rest, c => by
      rw [flEach_cons, flStmt_switch]
      dsimp only
      simpa [hoist] using
        flScopeRel P rest (flDflt P dflt (flCases P cs c).2).2
  | .forLoop init e post body :: rest, c => by
      rw [flEach_cons, flStmt_forLoop]
      dsimp only
      simpa [hoist] using
        flScopeRel P rest (flStmts P body (flStmts P post c).2).2
  | .exprStmt e :: rest, c => by
      rw [flEach_cons]
      rw [show (flStmt P (.exprStmt e) c).1 = .exprStmt e from by
        unfold flStmt; rfl]
      simpa [hoist] using flScopeRel P rest (flStmt P (.exprStmt e) c).2
  | .«break» :: rest, c => by
      rw [flEach_cons]
      rw [show (flStmt P .«break» c).1 = .«break» from by
        unfold flStmt; rfl]
      simpa [hoist] using flScopeRel P rest (flStmt P .«break» c).2
  | .«continue» :: rest, c => by
      rw [flEach_cons]
      rw [show (flStmt P .«continue» c).1 = .«continue» from by
        unfold flStmt; rfl]
      simpa [hoist] using flScopeRel P rest (flStmt P .«continue» c).2
  | .leave :: rest, c => by
      rw [flEach_cons]
      rw [show (flStmt P .leave c).1 = .leave from by
        unfold flStmt; rfl]
      simpa [hoist] using flScopeRel P rest (flStmt P .leave c).2

end

/-- **Soundness of block flattening.** -/
theorem flattenBlock_equiv (b : Block Op) :
    EquivBlock D b (flattenBlock b) := by
  unfold flattenBlock
  by_cases h1 : YulEvmCompiler.Optimizer.storageLayoutFreeStmts b
  · rw [if_pos h1]
    by_cases h2 : YulEvmCompiler.Optimizer.storageLayoutFreeStmts
        (flattenCore b)
    · simp only [if_pos h2]
      unfold flattenCore
      cases hP : YulEvmCompiler.Optimizer.freshPrefix
          (YulEvmCompiler.Optimizer.stmtsIdents b) with
      | none => exact EquivBlock.refl _
      | some P =>
          show EquivBlock D b (flStmts P b 0).1
          rw [flStmts_eq]
          exact (EquivBlock.of_stmts_funs
            (EquivStmts.of_forall₂ (flEach_forall2 P b 0))
            (flScopeRel P b 0)).trans
            (spliceSeq_blockEquiv P (flEach P b 0).1 (flEach P b 0).2)
    · simp only [if_neg h2]
      exact EquivBlock.refl _
  · rw [if_neg h1]
    exact EquivBlock.refl _

end YulEvmCompiler.Optimizer.Flatten
