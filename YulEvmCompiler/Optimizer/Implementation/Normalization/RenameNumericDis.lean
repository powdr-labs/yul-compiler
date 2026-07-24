import YulEvmCompiler.Optimizer.Implementation.Normalization.RenameNumeric
import YulEvmCompiler.Optimizer.Implementation.Normalization.RenameNumericFresh
set_option warningAsError true
/-!
# Toward `disambiguate (rename b) = disambiguate b`: the alignment invariant

The syntactic crux of `RenameNumeric` soundness (equation (B) of
`RenameNumericSound.lean`) is that the NUL canonicalizer `disambiguate` absorbs
the collision-only α-renaming `rename`. This file develops the **state
alignment** driving that proof, its preservation under binder batches, and the
**expression layer**.

The invariant is *functional*, not positional (the renamer stores no entry for a
*kept* binder, so the three substitutions do not align entrywise):

```
LookupAligned orig sb sv sr  :=  ∀ x ∈ orig, substOf sr (substOf sv x) = substOf sb x
```

— renaming a program name and looking it up in the canonicalizer state of the
*renamed* program (`sr`) gives the same `dsName` as looking it up directly in
the canonicalizer state of the *source* (`sb`). Its two preservation inputs:

* `SubstBelow taken sv` — every renamer entry's key and value are already
  committed (`taken` only grows, so this is monotone);
* the `assignName` discipline: a batch's outputs are fresh w.r.t. entry-`taken`,
  and each renamed output avoids the whole program (`orig`).

The centerpiece is `lookupAligned_batch`: declaring one binder batch — `vars` on
the source side, the `assignNames` outputs on the renamed side, the *same*
`dsName` payload `ds` on both (the canonicalizer's fresh names depend only on
position) — preserves the invariant. The expression layer (`dsExpr_align`)
then says renaming-then-canonicalizing equals canonicalizing, and the statement
layer (follow-up) threads exactly these two lemmas through the mutual traversal.
-/

namespace YulEvmCompiler.Optimizer.RenameNumeric

open YulSemantics
open YulEvmCompiler.Optimizer.Normalize (Subst substOf dsExpr dsArgs)

variable {Op : Type}

/-! ## `substOf` basics -/

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

/-- A lookup with no matching key is the identity. -/
theorem substOf_not_mem_keys {sv : Subst} {x : Ident}
    (h : x ∉ sv.map Prod.fst) : substOf sv x = x := by
  induction sv with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨k, d⟩ := p
      have hk : k ≠ x := fun h' => h (by simp [h'])
      have hrest : x ∉ rest.map Prod.fst := fun h' => h (by simp [h'])
      rw [substOf_cons_ne hk, ih hrest]

/-- A prefix with no matching key is skipped. -/
theorem substOf_append_skip {l s : Subst} {x : Ident}
    (h : x ∉ l.map Prod.fst) : substOf (l ++ s) x = substOf s x := by
  induction l with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨k, d⟩ := p
      have hk : k ≠ x := fun h' => h (by simp [h'])
      have hrest : x ∉ rest.map Prod.fst := fun h' => h (by simp [h'])
      rw [List.cons_append, substOf_cons_ne hk, ih hrest]

/-! ## The invariant -/

/-- **The alignment invariant** (see module docstring): renaming then looking up
in the renamed canonicalizer state equals looking up in the source state, on
every program identifier. -/
def LookupAligned (orig : List Ident) (sb : Subst) (sv : List (Ident × Ident))
    (sr : Subst) : Prop :=
  ∀ x ∈ orig, substOf sr (substOf sv x) = substOf sb x

/-- The empty states are aligned. -/
theorem LookupAligned.nil {orig : List Ident} : LookupAligned orig [] [] [] :=
  fun _ _ => rfl

/-- Every renamer entry's key and value are committed names. Keys: an entry is
created only when its key collides (`∈ taken`). Values: each output is
committed on creation. Monotone in `taken`. -/
def SubstBelow (taken : List Ident) (sv : List (Ident × Ident)) : Prop :=
  ∀ p ∈ sv, p.1 ∈ taken ∧ p.2 ∈ taken

/-- `SubstBelow` is monotone in the (growing) committed set. -/
theorem SubstBelow.mono {t t' : List Ident} {sv : List (Ident × Ident)}
    (hsub : ∀ y ∈ t, y ∈ t') (h : SubstBelow t sv) : SubstBelow t' sv :=
  fun p hp => ⟨hsub _ (h p hp).1, hsub _ (h p hp).2⟩

/-! ## `assignName`/`assignNames` toolkit -/

/-- The two shapes of `assignName`: kept (`x ∉ taken`) or renamed to a
program-fresh, uncommitted name. -/
theorem assignName_cases (orig taken : List Ident) (x : Ident) :
    (x ∉ taken ∧ assignName orig taken x = (x, [], x :: taken)) ∨
    (x ∈ taken ∧
      assignName orig taken x =
        (freshName (taken ++ orig) x, [(x, freshName (taken ++ orig) x)],
          freshName (taken ++ orig) x :: taken)) := by
  unfold assignName
  by_cases hx : x ∈ taken
  · exact Or.inr ⟨hx, by rw [if_pos hx]⟩
  · exact Or.inl ⟨hx, by rw [if_neg hx]⟩

/-- The fresh replacement name is neither committed nor a program identifier. -/
theorem freshName_split {taken orig : List Ident} {x : Ident} :
    freshName (taken ++ orig) x ∉ taken ∧ freshName (taken ++ orig) x ∉ orig :=
  ⟨fun h => freshName_not_mem (taken ++ orig) x (List.mem_append_left orig h),
   fun h => freshName_not_mem (taken ++ orig) x (List.mem_append_right taken h)⟩

/-- `assignName`'s output is never an already-committed name. -/
theorem assignName_not_taken (orig taken : List Ident) (x : Ident) :
    (assignName orig taken x).1 ∉ taken := by
  rcases assignName_cases orig taken x with ⟨hx, he⟩ | ⟨_, he⟩ <;> rw [he]
  · exact hx
  · exact freshName_split.1

/-- Keys of an entry list all fail a predicate its entries' keys satisfy. -/
theorem not_mem_keys_of_spec {l : List (Ident × Ident)} {P : Ident → Prop}
    (spec : ∀ p ∈ l, P p.1) {x : Ident} (hx : ¬ P x) : x ∉ l.map Prod.fst := by
  intro hmem
  obtain ⟨p, hp, hpk⟩ := List.mem_map.mp hmem
  exact hx (hpk ▸ spec p hp)

/-- `assignNames` unfolded one step (head assignment, then the tail batch). -/
theorem assignNames_cons_eq (orig taken : List Ident) (x : Ident) (xs : List Ident)
    {x' : Ident} {sub : List (Ident × Ident)} {t1 : List Ident}
    (h : assignName orig taken x = (x', sub, t1)) :
    assignNames orig (x :: xs) taken =
      (x' :: (assignNames orig xs t1).1,
        sub ++ (assignNames orig xs t1).2.1,
        (assignNames orig xs t1).2.2) := by
  simp only [assignNames, h]

/-- `assignNames` preserves the batch length. -/
theorem assignNames_length (orig : List Ident) :
    ∀ (vars taken : List Ident), (assignNames orig vars taken).1.length = vars.length
  | [], _ => rfl
  | x :: xs, taken => by
      rcases h : assignName orig taken x with ⟨x', sub, t1⟩
      rw [assignNames_cons_eq orig taken x xs h]
      simp [assignNames_length orig xs t1]

/-- `taken` only grows across a batch. -/
theorem assignNames_taken_mono (orig : List Ident) :
    ∀ (vars taken : List Ident) (y : Ident),
      y ∈ taken → y ∈ (assignNames orig vars taken).2.2
  | [], _, _, hy => hy
  | x :: xs, taken, y, hy => by
      rcases h : assignName orig taken x with ⟨x', sub, t1⟩
      rw [assignNames_cons_eq orig taken x xs h]
      refine assignNames_taken_mono orig xs t1 y ?_
      have ht1 : t1 = x' :: taken := by
        rcases assignName_cases orig taken x with ⟨_, he⟩ | ⟨_, he⟩ <;>
          (rw [he] at h; cases h; rfl)
      rw [ht1]
      exact List.mem_cons_of_mem _ hy

/-- Batch substitution entries: every entry's key is one of the batch's binders,
and its value avoids both the entry-`taken` and the whole program. -/
theorem assignNames_sub_spec (orig : List Ident) :
    ∀ (vars taken : List Ident),
      ∀ p ∈ (assignNames orig vars taken).2.1,
        p.1 ∈ vars ∧ p.2 ∉ taken ∧ p.2 ∉ orig
  | [], _, p, hp => by simp [assignNames] at hp
  | x :: xs, taken, p, hp => by
      rcases h : assignName orig taken x with ⟨x', sub, t1⟩
      rw [assignNames_cons_eq orig taken x xs h] at hp
      simp only [List.mem_append] at hp
      rcases hp with hp | hp
      · rcases assignName_cases orig taken x with ⟨_, he⟩ | ⟨hx, he⟩ <;>
          rw [he] at h <;> cases h
        · simp at hp
        · simp only [List.mem_singleton] at hp
          subst hp
          exact ⟨List.mem_cons_self .., freshName_split.1, freshName_split.2⟩
      · have ht1 : t1 = x' :: taken := by
          rcases assignName_cases orig taken x with ⟨_, he⟩ | ⟨_, he⟩ <;>
            (rw [he] at h; cases h; rfl)
        obtain ⟨hk, hnt, hno⟩ := assignNames_sub_spec orig xs t1 p hp
        refine ⟨List.mem_cons_of_mem _ hk, ?_, hno⟩
        intro hmem
        exact hnt (by rw [ht1]; exact List.mem_cons_of_mem _ hmem)

/-! ## The centerpiece: batch extension preserves alignment -/

/-- **Binder-batch extension.** Declaring one batch — the source binders `vars`
with `dsName` payload `ds` on the source side, the `assignNames` outputs with
the *same* payload on the renamed side, the batch's substitution entries on the
renamer — preserves the alignment invariant. Requires the batch to be
duplicate-free and made of program identifiers, and the standing `SubstBelow`
bookkeeping. -/
theorem lookupAligned_batch {orig : List Ident} :
    ∀ (vars : List Ident) (ds : List Ident) (taken : List Ident)
      {sb : Subst} {sv : List (Ident × Ident)} {sr : Subst},
      ds.length = vars.length →
      LookupAligned orig sb sv sr → SubstBelow taken sv →
      vars.Nodup → (∀ x ∈ vars, x ∈ orig) →
      LookupAligned orig
        (vars.zip ds ++ sb)
        ((assignNames orig vars taken).2.1 ++ sv)
        (((assignNames orig vars taken).1).zip ds ++ sr)
  | [], ds, taken, sb, sv, sr, _, hLA, _, _, _ => by
      simpa [assignNames] using hLA
  | x :: xs, [], _, _, _, _, hlen, _, _, _, _ => by simp at hlen
  | x :: xs, d :: ds, taken, sb, sv, sr, hlen, hLA, hSB, hnd, hvars => by
      intro z hz
      have hx_orig : x ∈ orig := hvars x (List.mem_cons_self ..)
      have hxs_orig : ∀ y ∈ xs, y ∈ orig := fun y hy => hvars y (List.mem_cons_of_mem _ hy)
      have hxs_nd : xs.Nodup := hnd.of_cons
      have hx_xs : x ∉ xs := (List.nodup_cons.mp hnd).1
      have hlen' : ds.length = xs.length := by simpa using hlen
      rcases h : assignName orig taken x with ⟨x', sub, t1⟩
      have ht1 : t1 = x' :: taken := by
        rcases assignName_cases orig taken x with ⟨_, he⟩ | ⟨_, he⟩ <;>
          (rw [he] at h; cases h; rfl)
      have hx'_taken : x' ∉ taken := by
        have := assignName_not_taken orig taken x
        rw [h] at this
        exact this
      rw [assignNames_cons_eq orig taken x xs h]
      simp only [List.zip_cons_cons, List.cons_append, List.append_assoc]
      -- tail IH at the extended committed set
      have hSB1 : SubstBelow t1 sv :=
        hSB.mono (fun y hy => by rw [ht1]; exact List.mem_cons_of_mem _ hy)
      have hIH := lookupAligned_batch xs ds t1 hlen' hLA hSB1 hxs_nd hxs_orig
      have hsubs_spec := assignNames_sub_spec orig xs t1
      by_cases hzx : x = z
      · -- the head binder itself: both outer heads hit
        rw [← hzx]
        rw [substOf_cons_eq]
        rcases assignName_cases orig taken x with ⟨hxk, he⟩ | ⟨hxk, he⟩ <;>
          rw [he] at h <;> cases h
        · -- kept: no key `x` anywhere in the middle; renamed head hits at `x`
          have hx_subs := not_mem_keys_of_spec
            (fun p hp => (hsubs_spec p hp).1) (P := (· ∈ xs)) hx_xs
          have hx_sv := not_mem_keys_of_spec
            (fun p hp => (hSB p hp).1) (P := (· ∈ taken)) hxk
          rw [List.nil_append, substOf_append_skip hx_subs, substOf_not_mem_keys hx_sv,
            substOf_cons_eq]
        · -- renamed: middle head hits, renamed head hits at the fresh name
          rw [List.cons_append, List.nil_append, substOf_cons_eq, substOf_cons_eq]
      · -- some other name: skip heads on all three sides, apply the IH
        rw [substOf_cons_ne hzx]
        have hmid : substOf (sub ++ ((assignNames orig xs t1).2.1 ++ sv)) z =
            substOf ((assignNames orig xs t1).2.1 ++ sv) z := by
          rcases assignName_cases orig taken x with ⟨_, he⟩ | ⟨_, he⟩ <;>
            rw [he] at h <;> cases h
          · rw [List.nil_append]
          · rw [List.cons_append, List.nil_append, substOf_cons_ne hzx]
        rw [hmid]
        have hne : x' ≠ substOf ((assignNames orig xs t1).2.1 ++ sv) z := by
          rcases substOf_self_or_mem ((assignNames orig xs t1).2.1 ++ sv) z with hself | hmem
          · rw [hself]
            rcases assignName_cases orig taken x with ⟨_, he⟩ | ⟨hxk, he⟩ <;>
              rw [he] at h <;> cases h
            · exact hzx
            · exact fun hcontra => freshName_split.2 (hcontra ▸ hz)
          · rw [List.map_append, List.mem_append] at hmem
            rcases hmem with hmem | hmem
            · obtain ⟨p, hp, hpv⟩ := List.mem_map.mp hmem
              have := (hsubs_spec p hp).2.1
              intro hcontra
              exact this (by rw [hpv, ← hcontra, ht1]; exact List.mem_cons_self ..)
            · obtain ⟨p, hp, hpv⟩ := List.mem_map.mp hmem
              exact fun hcontra => hx'_taken (by rw [hcontra, ← hpv]; exact (hSB p hp).2)
        rw [substOf_cons_ne hne]
        exact hIH z hz

/-! ## The expression layer of equation (B) -/

section ExprLayer

variable {orig : List Ident}
variable {sbv sbf : Subst} {svv svf : List (Ident × Ident)} {srv srf : Subst}

mutual
/-- Renaming then canonicalizing an expression equals canonicalizing it
directly, under aligned variable and function states. -/
theorem dsExpr_align (hv : LookupAligned orig sbv svv srv)
    (hf : LookupAligned orig sbf svf srf) :
    ∀ (e : Expr Op), (∀ x ∈ identsE e, x ∈ orig) →
      dsExpr (srv, srf) (renExpr ⟨svv, svf⟩ e) = dsExpr (sbv, sbf) e
  | .lit _, _ => rfl
  | .var x, hids => by
      have hx : x ∈ orig := hids x (by simp [identsE])
      show Expr.var (substOf srv (substOf svv x)) = Expr.var (substOf sbv x)
      rw [hv x hx]
  | .builtin op args, hids => by
      show Expr.builtin op _ = Expr.builtin op _
      rw [dsArgs_align hv hf args (fun x hx => hids x (by simpa [identsE] using hx))]
  | .call fn args, hids => by
      have hfn : fn ∈ orig := hids fn (by simp [identsE])
      show Expr.call (substOf srf (substOf svf fn)) _ = Expr.call (substOf sbf fn) _
      rw [hf fn hfn,
        dsArgs_align hv hf args
          (fun x hx => hids x (by simp [identsE]; exact Or.inr hx))]

/-- `dsExpr_align`, argument-list form. -/
theorem dsArgs_align (hv : LookupAligned orig sbv svv srv)
    (hf : LookupAligned orig sbf svf srf) :
    ∀ (es : List (Expr Op)), (∀ x ∈ identsA es, x ∈ orig) →
      dsArgs (srv, srf) (renArgs ⟨svv, svf⟩ es) = dsArgs (sbv, sbf) es
  | [], _ => rfl
  | e :: rest, hids => by
      show _ :: _ = _ :: _
      rw [dsExpr_align hv hf e (fun x hx => hids x (by simp [identsA]; exact Or.inl hx)),
        dsArgs_align hv hf rest (fun x hx => hids x (by simp [identsA]; exact Or.inr hx))]
end

end ExprLayer

end YulEvmCompiler.Optimizer.RenameNumeric
