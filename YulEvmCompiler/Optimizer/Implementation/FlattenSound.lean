import YulEvmCompiler.Optimizer.Implementation.Flatten
import YulEvmCompiler.Optimizer.Implementation.FuseDeclAssignSound
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
local notation "D" => evmWithExternal calls creates

/-! ### Keyed renaming of an environment segment -/

/-- Rename every `x` key to `x'` (values untouched). -/
def renKeys (x x' : Ident) (V : VEnv D) : VEnv D :=
  V.map (fun p => (renVar x x' p.1, p.2))

@[simp] theorem renKeys_nil (x x' : Ident) :
    renKeys (calls := calls) (creates := creates) x x' [] = [] := rfl

@[simp] theorem renKeys_cons (x x' : Ident)
    (p : Ident × (evmWithExternal calls creates).Value) (V : VEnv D) :
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
    (v : (evmWithExternal calls creates).Value) :
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
    (v : (evmWithExternal calls creates).Value) :
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
    {p : Ident × (evmWithExternal calls creates).Value},
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
    (v : (evmWithExternal calls creates).Value) :
    ((VEnv.set C y v).find? (fun p => p.1 = x)).isSome := by
  rw [find_key_isSome_iff, VEnv.set_keys]
  exact find_key_isSome_iff.mp hx

/-- Renaming commutes with an update to `x`/`x'` (the segment never binds
`x'`, so the target's first `x'` is the rename of the source's first `x`). -/
theorem renKeys_set_x {x x' : Ident}
    (v : (evmWithExternal calls creates).Value) : ∀ {C : VEnv D},
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
    (v : (evmWithExternal calls creates).Value) : ∀ {C : VEnv D},
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
    (v : (evmWithExternal calls creates).Value) :
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
              (by rw [VEnv.set_length]; exact hn)

/-- Source `setMany` matches target `setMany` on the renamed targets. -/
theorem RnRel.setMany_ren {x x' : Ident} {n : Nat} :
    ∀ {ys : List Ident} {V₁ V₂ : VEnv D},
    RnRel x x' n V₁ V₂ →
    (∀ y ∈ ys, y ≠ x') →
    ∀ (vs : List (evmWithExternal calls creates).Value),
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

end YulEvmCompiler.Optimizer.Flatten
