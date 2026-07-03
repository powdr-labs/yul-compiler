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

/-! ### Flattened-layout offset lemmas -/

/-- Indexed characterization of `entryPositions`: the `i`-th entry is
`mainLen + 1 + (sum of the first i function lengths)`. -/
theorem entryPositions_getElem? (mainLen : Nat) (lens : List Nat) (i : Nat)
    (hi : i < lens.length) :
    (entryPositions mainLen lens)[i]? = some (mainLen + 1 + (lens.take i).sum) := by
  induction lens generalizing mainLen i with
  | nil => simp at hi
  | cons len rest ih =>
      rw [entryPositions_cons]
      cases i with
      | zero => simp
      | succ k =>
          simp only [List.getElem?_cons_succ, List.take_succ_cons, List.sum_cons]
          rw [ih (mainLen + len) k (by simpa using hi)]
          congr 1
          omega

/-- The assembled length of a flattened chunk list is the sum of the chunks'
assembled lengths. -/
theorem length_assembleBytes_flatten (cs : List (List Instr)) :
    (assembleBytes cs.flatten).length
      = (cs.map (fun c => (assembleBytes c).length)).sum := by
  induction cs with
  | nil => rfl
  | cons c rest ih =>
      rw [List.flatten_cons, assembleBytes_append, List.length_append, ih,
        List.map_cons, List.sum_cons]

/-- Splitting a chunk list's flatten at index `i`. -/
theorem flatten_split {α} (cs : List (List α)) (i : Nat) (hi : i < cs.length) :
    cs.flatten = (cs.take i).flatten ++ cs[i] ++ (cs.drop (i + 1)).flatten := by
  conv_lhs => rw [← List.take_append_drop i cs]
  rw [List.flatten_append, List.append_assoc]
  congr 1
  rw [List.drop_eq_getElem_cons hi, List.flatten_cons]

/-- **Each chunk sits at a known byte offset in the flattened, assembled code.**
Chunk `i` is preceded by exactly the assembled lengths of the earlier chunks. -/
theorem assembleBytes_flatten_embed (cs : List (List Instr)) (i : Nat)
    (hi : i < cs.length) :
    ∃ pre post, assembleBytes cs.flatten = pre ++ assembleBytes cs[i] ++ post
      ∧ pre.length = ((cs.take i).map (fun c => (assembleBytes c).length)).sum := by
  refine ⟨assembleBytes (cs.take i).flatten, assembleBytes (cs.drop (i + 1)).flatten, ?_, ?_⟩
  · rw [flatten_split cs i hi, assembleBytes_append, assembleBytes_append]
  · rw [length_assembleBytes_flatten]

/-! ### Two-pass length agreement -/

set_option maxHeartbeats 1000000 in
/-- The pass-2 function codes have exactly the pass-1 recorded lengths: for each
function, `compileFn` at the real entry and at entry `0` produce equal-length
code (Phase-1.3 `compileFn_lenSig`, transported across the signature-equivalent
tables `hsig`). -/
theorem fnCodes_lens_eq (dummyFt realFt : FnTable) (hsig : FnTable.SigEq dummyFt realFt)
    (fns : List (Ident × List Ident × List Ident × Block Op)) :
    ∀ (entries : List Nat) (lens : List Nat) (fnCodes : List (List Instr)),
      entries.length = fns.length →
      fns.mapM (fun p => (compileFn dummyFt 0 p.2.1 p.2.2.1 p.2.2.2).map
        (fun c => (assembleBytes c).length)) = some lens →
      (fns.zip entries).mapM
        (fun x => compileFn realFt x.2 x.1.2.1 x.1.2.2.1 x.1.2.2.2) = some fnCodes →
      fnCodes.map (fun c => (assembleBytes c).length) = lens := by
  induction fns with
  | nil =>
      intro entries lens fnCodes _ hl hf
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hl
      simp only [List.zip_nil_left, List.mapM_nil, Option.pure_def, Option.some.injEq] at hf
      subst hl; subst hf; rfl
  | cons p rest ih =>
      intro entries lens fnCodes hlen hl hf
      cases entries with
      | nil => simp at hlen
      | cons e erest =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
          rw [List.mapM_cons] at hl
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.map_eq_some_iff,
            Option.pure_def, Option.some.injEq] at hl
          obtain ⟨b, ⟨a, ha, hab⟩, bs, hbs, hlens_eq⟩ := hl
          rw [List.zip_cons_cons, List.mapM_cons] at hf
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
            Option.some.injEq] at hf
          obtain ⟨fc1, hfc1, restCodes, hrc, hfc_eq⟩ := hf
          subst hab; subst hlens_eq; subst hfc_eq
          obtain ⟨fc1', hfc1', hlen1⟩ := compileFn_lenSig dummyFt realFt hsig 0 e
            p.2.1 p.2.2.1 p.2.2.2 a ha
          rw [hfc1] at hfc1'
          simp only [Option.some.injEq] at hfc1'
          subst hfc1'
          simp only [List.map_cons]
          rw [ih erest bs restCodes hlen hbs hrc, hlen1]

end YulEvmCompiler
