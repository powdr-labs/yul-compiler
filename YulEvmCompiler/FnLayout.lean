import YulEvmCompiler.FnProof

/-!
# YulEvmCompiler.FnLayout

Phase 2 of the function-verification plan (see `FUNCTIONS_PLAN.md`): the
whole-program layout arithmetic. `compileProgF` lays a program out as
`main ; STOP ; f₁ ; f₂ ; …` and records each function's entry byte-position in
the `FnTable` via the two-pass `entryPositions`. This file proves the arithmetic
that makes those recorded positions agree with the actual byte offsets in the
assembled code — the foundation for the `ProgLayout` invariant.
-/

namespace YulEvmCompiler

open YulSemantics (Expr Stmt Block Ident)
open YulSemantics.EVM (Op)

/-- The `entryPositions` accumulator only prepends: folding from `(acc, cur)`
gives `acc` followed by the fold from `([], cur)`. -/
private theorem ep_foldl_acc (acc : List Nat) (cur : Nat) (lens : List Nat) :
    (lens.foldl (fun a len => (a.1 ++ [a.2], a.2 + len)) (acc, cur)).1
      = acc ++ (lens.foldl (fun a len => (a.1 ++ [a.2], a.2 + len)) ([], cur)).1 := by
  induction lens generalizing acc cur with
  | nil => simp
  | cons len rest ih =>
      show (List.foldl _ (acc ++ [cur], cur + len) rest).1
        = acc ++ (List.foldl _ ([cur], cur + len) rest).1
      rw [ih (acc ++ [cur]) (cur + len), ih [cur] (cur + len), List.append_assoc]

@[simp] theorem entryPositions_nil (mainLen : Nat) : entryPositions mainLen [] = [] := rfl

/-- `entryPositions` peels off the first entry at `mainLen+1`, then continues
with the base advanced by the first function's length. -/
theorem entryPositions_cons (mainLen len : Nat) (lens : List Nat) :
    entryPositions mainLen (len :: lens)
      = (mainLen + 1) :: entryPositions (mainLen + len) lens := by
  unfold entryPositions
  show (List.foldl _ ([mainLen + 1], mainLen + 1 + len) lens).1
    = (mainLen + 1) :: (List.foldl _ ([], mainLen + len + 1) lens).1
  rw [ep_foldl_acc [mainLen + 1] (mainLen + 1 + len) lens]
  have : mainLen + 1 + len = mainLen + len + 1 := by omega
  rw [this]
  rfl

@[simp] theorem entryPositions_length (mainLen : Nat) (lens : List Nat) :
    (entryPositions mainLen lens).length = lens.length := by
  induction lens generalizing mainLen with
  | nil => rfl
  | cons len rest ih => rw [entryPositions_cons]; simp [ih]

/-- `FnTable.get?` on a cons. -/
theorem FnTable.get?_cons (k : Ident) (v : FnInfo) (t : FnTable) (n : Ident) :
    FnTable.get? ((k, v) :: t) n = if k = n then some v else FnTable.get? t n := by
  unfold FnTable.get?
  rw [List.find?_cons]
  by_cases h : k = n
  · simp [h]
  · simp [h]

/-- The two passes' function tables built by `compileProgF` are
signature-equivalent: they share names and per-function param/return arities,
differing only in the recorded entry position (`0` in pass 1 vs. the real
offset in pass 2). This is what lets the Phase-1.3 `*_lenSig` lemmas transfer
pass-1 code lengths to pass-2 code lengths. -/
theorem sigEq_dummy_real
    (fns : List (Ident × List Ident × List Ident × Block Op)) :
    ∀ (entries : List Nat), entries.length = fns.length →
      FnTable.SigEq
        (fns.map (fun p => (p.1, (⟨p.2.1, p.2.2.1, p.2.2.2, 0⟩ : FnInfo))))
        ((fns.zip entries).map
          (fun pe => (pe.1.1, (⟨pe.1.2.1, pe.1.2.2.1, pe.1.2.2.2, pe.2⟩ : FnInfo)))) := by
  induction fns with
  | nil => intro entries _ n; rfl
  | cons p rest ih =>
      intro entries hlen n
      cases entries with
      | nil => simp at hlen
      | cons e erest =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
          simp only [List.map_cons, List.zip_cons_cons, FnTable.get?_cons]
          by_cases hpn : p.1 = n
          · simp [hpn]
          · simp only [hpn, if_false]
            exact ih erest hlen n

end YulEvmCompiler
