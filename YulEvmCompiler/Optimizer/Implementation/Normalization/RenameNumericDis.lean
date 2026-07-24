import YulEvmCompiler.Optimizer.Implementation.Normalization.RenameNumeric
set_option warningAsError true
/-!
# Toward `disambiguate (rename b) = disambiguate b`: the alignment invariant

The syntactic crux of `RenameNumeric` soundness (equation (B) of
`RenameNumericSound.lean`) is that the NUL canonicalizer `disambiguate` absorbs
the collision-only α-renaming `rename`. This file develops the **state
alignment** that drives that proof, and discharges its **expression layer**:

At corresponding traversal points, `disambiguate`-on-source, `rename`, and
`disambiguate`-on-renamed hold substitutions of the *same length in the same
order*, related entrywise as

```
st_source : (xᵢ, dᵢ)      -- source name ↦ dsName
ren.σ     : (xᵢ, yᵢ)      -- source name ↦ renamed name (same keys!)
st_renamed: (yᵢ, dᵢ)      -- renamed name ↦ the same dsName
```

(`Align` below). Under two side conditions — the renamed names `yᵢ` are pairwise
distinct (they are committed sequentially to `rename`'s global `taken`), and
each is either *kept* (`yᵢ = xᵢ`) or *program-fresh* (`yᵢ ∉ orig`) — name-keyed
first-match lookup resolves at the same position on both sides
(`substOf_align`), so renaming-then-canonicalizing an expression equals
canonicalizing it directly (`dsExpr_align`). The statement layer threads the
same invariant through the mutual traversal and is the follow-up.
-/

namespace YulEvmCompiler.Optimizer.RenameNumeric

open YulSemantics
open YulEvmCompiler.Optimizer.Normalize (Subst substOf dsExpr dsArgs)

variable {Op : Type}

/-! ## The alignment relation and its side conditions -/

/-- Entrywise alignment of the three substitutions (see module docstring):
same keys/order between the source canonicalizer state and the renamer, and the
renamed canonicalizer state maps each renamed name to the same `dsName`. -/
inductive Align : Subst → List (Ident × Ident) → Subst → Prop
  | nil : Align [] [] []
  | cons {x y d : Ident} {sb sv sr : List (Ident × Ident)} :
      Align sb sv sr →
      Align ((x, d) :: sb) ((x, y) :: sv) ((y, d) :: sr)

/-- Each renamer entry either keeps the name or maps it outside the program's
identifiers (`orig`) — the capture-avoidance discipline of `assignName`. -/
def KeptOrFresh (orig : List Ident) (sv : List (Ident × Ident)) : Prop :=
  ∀ p ∈ sv, p.2 = p.1 ∨ p.2 ∉ orig

/-- Head hit: looking up the head's key returns the head's value. -/
theorem substOf_cons_eq {y d : Ident} {s : Subst} : substOf ((y, d) :: s) y = d := by
  simp [substOf, List.find?_cons_of_pos]

/-- Head miss: a non-matching head is skipped. -/
theorem substOf_cons_ne {k d x : Ident} {s : Subst} (h : k ≠ x) :
    substOf ((k, d) :: s) x = substOf s x := by
  simp [substOf, List.find?_cons_of_neg, h]

/-- A lookup either misses (returns the name itself) or returns one of the
substitution's values. -/
theorem substOf_self_or_mem (sv : Subst) (x : Ident) :
    substOf sv x = x ∨ substOf sv x ∈ sv.map Prod.snd := by
  induction sv with
  | nil => exact Or.inl rfl
  | cons p rest ih =>
      by_cases hp : p.1 = x
      · refine Or.inr ?_
        obtain ⟨k, d⟩ := p
        simp only at hp
        subst hp
        rw [substOf_cons_eq]
        exact List.mem_cons_self ..
      · obtain ⟨k, d⟩ := p
        rw [substOf_cons_ne hp]
        rcases ih with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)

/-- **The central lookup lemma.** Under alignment, distinct renamed values, the
kept-or-fresh discipline, and `x` occurring in the program, renaming then
looking up in the renamed state equals looking up in the source state:
`substOf sr (substOf sv x) = substOf sb x`. -/
theorem substOf_align {orig : List Ident} :
    ∀ {sb : Subst} {sv : List (Ident × Ident)} {sr : Subst},
    Align sb sv sr → (sv.map Prod.snd).Nodup → KeptOrFresh orig sv →
    ∀ {x : Ident}, x ∈ orig → substOf sr (substOf sv x) = substOf sb x := by
  intro sb sv sr hA
  induction hA with
  | nil => intro _ _ x _; rfl
  | @cons x' y' d' sb sv sr _ ih =>
      intro hnd hkf x hx
      have hnd' : (y' :: sv.map Prod.snd).Nodup := by simpa using hnd
      have hndTail : (sv.map Prod.snd).Nodup := hnd'.of_cons
      have hy'Tail : y' ∉ sv.map Prod.snd := (List.nodup_cons.mp hnd').1
      have hkfTail : KeptOrFresh orig sv := fun p hp => hkf p (List.mem_cons_of_mem _ hp)
      by_cases hxx : x' = x
      · -- head hit: both sides resolve at the head, to `d'`.
        subst hxx
        rw [substOf_cons_eq, substOf_cons_eq, substOf_cons_eq]
      · -- head miss on the source side; show the renamed side also misses.
        rw [substOf_cons_ne hxx, substOf_cons_ne hxx]
        -- the tail lookup's result is ≠ y', so the renamed head is skipped
        have hne : y' ≠ substOf sv x := by
          rcases substOf_self_or_mem sv x with hself | hmem
          · rw [hself]
            rcases hkf (x', y') (List.mem_cons_self ..) with hk | hf
            · simp only at hk
              rw [hk]
              exact fun h => hxx h
            · simp only at hf
              exact fun h => hf (h.symm ▸ hx)
          · exact fun h => hy'Tail (h ▸ hmem)
        rw [substOf_cons_ne hne]
        exact ih hndTail hkfTail hx

/-! ## The expression layer of equation (B) -/

section ExprLayer

variable {orig : List Ident}
variable {sbv sbf : Subst} {svv svf : List (Ident × Ident)} {srv srf : Subst}

mutual
/-- Renaming then canonicalizing an expression equals canonicalizing it
directly, under aligned variable and function states. -/
theorem dsExpr_align
    (hAv : Align sbv svv srv) (hndv : (svv.map Prod.snd).Nodup)
    (hkfv : KeptOrFresh orig svv)
    (hAf : Align sbf svf srf) (hndf : (svf.map Prod.snd).Nodup)
    (hkff : KeptOrFresh orig svf) :
    ∀ (e : Expr Op), (∀ x ∈ identsE e, x ∈ orig) →
      dsExpr (srv, srf) (renExpr ⟨svv, svf⟩ e) = dsExpr (sbv, sbf) e
  | .lit _, _ => rfl
  | .var x, hids => by
      have hx : x ∈ orig := hids x (by simp [identsE])
      show Expr.var (substOf srv (substOf svv x)) = Expr.var (substOf sbv x)
      rw [substOf_align hAv hndv hkfv hx]
  | .builtin op args, hids => by
      show Expr.builtin op _ = Expr.builtin op _
      rw [dsArgs_align hAv hndv hkfv hAf hndf hkff args
        (fun x hx => hids x (by simpa [identsE] using hx))]
  | .call fn args, hids => by
      have hfn : fn ∈ orig := hids fn (by simp [identsE])
      show Expr.call (substOf srf (substOf svf fn)) _ = Expr.call (substOf sbf fn) _
      rw [substOf_align hAf hndf hkff hfn,
        dsArgs_align hAv hndv hkfv hAf hndf hkff args
          (fun x hx => hids x (by simp [identsE]; exact Or.inr hx))]

/-- `dsExpr_align`, argument-list form. -/
theorem dsArgs_align
    (hAv : Align sbv svv srv) (hndv : (svv.map Prod.snd).Nodup)
    (hkfv : KeptOrFresh orig svv)
    (hAf : Align sbf svf srf) (hndf : (svf.map Prod.snd).Nodup)
    (hkff : KeptOrFresh orig svf) :
    ∀ (es : List (Expr Op)), (∀ x ∈ identsA es, x ∈ orig) →
      dsArgs (srv, srf) (renArgs ⟨svv, svf⟩ es) = dsArgs (sbv, sbf) es
  | [], _ => rfl
  | e :: rest, hids => by
      show _ :: _ = _ :: _
      rw [dsExpr_align hAv hndv hkfv hAf hndf hkff e
          (fun x hx => hids x (by simp [identsA]; exact Or.inl hx)),
        dsArgs_align hAv hndv hkfv hAf hndf hkff rest
          (fun x hx => hids x (by simp [identsA]; exact Or.inr hx))]
end

end ExprLayer

end YulEvmCompiler.Optimizer.RenameNumeric
