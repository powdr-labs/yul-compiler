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

end YulEvmCompiler
