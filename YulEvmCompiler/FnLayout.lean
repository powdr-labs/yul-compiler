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
open EvmSemantics EvmSemantics.EVM

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
      fns.mapM (fun p => (compileFn dummyFt 0 p.2.1 p.2.2.1 p.2.2.2).bind
        (fun code => some (assembleBytes code).length)) = some lens →
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
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff,
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


/-! ### `mapM` indexing helpers and the whole-program layout invariant -/

theorem mapM_option_getElem? {α β} (f : α → Option β) (l : List α) (r : List β)
    (h : l.mapM f = some r) (i : Nat) : r[i]? = (l[i]?).bind f := by
  induction l generalizing r i with
  | nil => simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h; subst h; simp
  | cons a l ih =>
      rw [List.mapM_cons] at h
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨b, hb, rs, hrs, rfl⟩ := h
      cases i with
      | zero => simp [hb]
      | succ k => simpa using ih rs hrs k

theorem mapM_option_length {α β} (f : α → Option β) (l : List α) (r : List β)
    (h : l.mapM f = some r) : r.length = l.length := by
  induction l generalizing r with
  | nil => simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h; subst h; rfl
  | cons a l ih =>
      rw [List.mapM_cons] at h
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨b, hb, rs, hrs, rfl⟩ := h
      simp [ih rs hrs]

set_option maxHeartbeats 2000000

/-- The whole-program layout established by a successful `compileProgF`:
there is a function table `ft` such that (1) the pass-2 `mainCode` compiled
against `ft` is the prefix of `fullIs`, and (2) every function `ft` resolves
has its compiled body embedded at exactly its recorded entry byte-position. -/
def ProgLayout (prog : Block Op) (fullIs : List Instr) : Prop :=
  ∃ (ft : FnTable) (mainCode : List Instr) (mainΓ : List Ident),
    compileStmtsF ft 0 [] prog = some (mainCode, mainΓ) ∧
    (∃ post, fullIs = mainCode ++ post) ∧
    (∀ fn info, ft.get? fn = some info →
      ∃ code, compileFn ft info.entry info.params info.rets info.body = some code ∧
        ∃ preIs postIs, fullIs = preIs ++ code ++ postIs
          ∧ (assembleBytes preIs).length = info.entry)

theorem compileProgF_layout (prog : Block Op) (fullIs : List Instr)
    (hcomp : compileProgF prog = some fullIs) : ProgLayout prog fullIs := by
  simp only [compileProgF, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hcomp
  obtain ⟨⟨mainCode0, Γ0⟩, hmain0, lens, hlens, ⟨mainCode, Γm⟩, hmain, fnCodes, hfn, hfull⟩ := hcomp
  set fns := collectFns prog with hfns
  set dummyFt : FnTable :=
    fns.map (fun p => (p.1, (⟨p.2.1, p.2.2.1, p.2.2.2, 0⟩ : FnInfo))) with hdummy
  set mainLen0 := (assembleBytes mainCode0).length with hmainLen0
  set entries := entryPositions mainLen0 lens with hentries
  set realFt : FnTable :=
    (fns.zip entries).map (fun x => (x.1.1, (⟨x.1.2.1, x.1.2.2.1, x.1.2.2.2, x.2⟩ : FnInfo)))
    with hrealFt
  have hlens_len : lens.length = fns.length := mapM_option_length _ _ _ hlens
  have hentries_len : entries.length = fns.length := by
    rw [hentries, entryPositions_length, hlens_len]
  have hsig : FnTable.SigEq dummyFt realFt := sigEq_dummy_real fns entries hentries_len
  have hfnCodes_len : fnCodes.length = fns.length := by
    rw [mapM_option_length _ _ _ hfn, List.length_zip, hentries_len, Nat.min_self]
  have hmainlen : (assembleBytes mainCode).length = mainLen0 := by
    obtain ⟨is₂, his₂, hl⟩ := compileStmtsF_lenSig dummyFt realFt hsig 0 [] prog 0 mainCode0 Γ0 hmain0
    rw [hmain] at his₂
    simp only [Option.some.injEq, Prod.mk.injEq] at his₂
    rw [hmainLen0, his₂.1]; exact hl
  have hmaps : fnCodes.map (fun c => (assembleBytes c).length) = lens :=
    fnCodes_lens_eq dummyFt realFt hsig fns entries lens fnCodes hentries_len hlens hfn
  refine ⟨realFt, mainCode, Γm, hmain,
    ⟨[Instr.op .STOP] ++ fnCodes.flatten, ?_⟩, ?_⟩
  · rw [← hfull, List.append_assoc]
  · intro fn info hget
    -- locate the index of fn in the zipped list
    unfold FnTable.get? at hget
    rw [Option.map_eq_some_iff] at hget
    obtain ⟨p, hfindp, hp2⟩ := hget
    have hpred : p.1 = fn := by have := List.find?_some hfindp; simpa using this
    have hpmem : p ∈ realFt := List.mem_of_find?_eq_some hfindp
    obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hpmem
    have hrealFt_len : realFt.length = fns.length := by
      rw [hrealFt, List.length_map, List.length_zip, hentries_len, Nat.min_self]
    have hi_fns : i < fns.length := by rw [hrealFt_len] at hi; exact hi
    have hi_ent : i < entries.length := by rw [hentries_len]; exact hi_fns
    have hi_fc : i < fnCodes.length := by rw [hfnCodes_len]; exact hi_fns
    have hi_lens : i < lens.length := by rw [hlens_len]; exact hi_fns
    have hi_zip : i < (fns.zip entries).length := by
      rw [List.length_zip, hentries_len, Nat.min_self]; exact hi_fns
    -- realFt[i] as an explicit pair
    have hrealFt_i : realFt[i] =
        (fns[i].1, (⟨fns[i].2.1, fns[i].2.2.1, fns[i].2.2.2, entries[i]⟩ : FnInfo)) := by
      simp only [hrealFt, List.getElem_map, List.getElem_zip]
    -- so info is the second component
    have hpeq : p = (fns[i].1, (⟨fns[i].2.1, fns[i].2.2.1, fns[i].2.2.2, entries[i]⟩ : FnInfo)) := by
      rw [← hpi, hrealFt_i]
    have hinfo : info = ⟨fns[i].2.1, fns[i].2.2.1, fns[i].2.2.2, entries[i]⟩ := by
      rw [← hp2, hpeq]
    -- fnCodes[i] is compileFn realFt entries[i] (fns[i] sig) …
    have hfnc : compileFn realFt entries[i] fns[i].2.1 fns[i].2.2.1 fns[i].2.2.2 = some fnCodes[i] := by
      have hget := mapM_option_getElem? _ _ _ hfn i
      rw [List.getElem?_eq_getElem hi_fc, List.getElem?_eq_getElem hi_zip,
        List.getElem_zip] at hget
      exact hget.symm
    -- entry offset
    have hentry_val : entries[i] = mainLen0 + 1 + (lens.take i).sum := by
      have := entryPositions_getElem? mainLen0 lens i hi_lens
      rw [← hentries, List.getElem?_eq_getElem hi_ent, Option.some.injEq] at this
      exact this
    -- prefix-sum of function code lengths = prefix-sum of recorded lens
    have hsum : ((fnCodes.take i).map (fun c => (assembleBytes c).length)).sum
        = (lens.take i).sum := by
      rw [List.map_take, hmaps]
    -- embed fnCodes[i] in the flattened code (instruction level)
    refine ⟨fnCodes[i], ?_, ?_⟩
    · rw [hinfo]; exact hfnc
    · refine ⟨mainCode ++ [Instr.op .STOP] ++ (fnCodes.take i).flatten,
        (fnCodes.drop (i + 1)).flatten, ?_, ?_⟩
      · rw [← hfull, flatten_split fnCodes i hi_fc]
        simp only [List.append_assoc]
      · rw [show info.entry = entries[i] from by rw [hinfo], hentry_val]
        simp only [assembleBytes_append, List.length_append, hmainlen,
          length_assembleBytes_flatten, hsum, assembleBytes_cons, assembleBytes_nil,
          List.length_nil, Instr.length_bytes_op]

/-! ### Source/compile-time function-environment correspondence -/

/-- `collectFns` collects exactly the top-level function definitions, in order,
matching the source semantics' `hoist` (up to `FDecl`/tuple packaging). This is
the static half of the funenv↔`FnTable` correspondence: at the top level the
source resolves calls against `hoist yul prog`, whose entries are precisely the
param/return/body triples that `compileProgF`'s table is built from. -/
theorem hoist_eq_collectFns (prog : Block Op) :
    YulSemantics.hoist yul prog
      = (collectFns prog).map
          (fun p => (p.1, (⟨p.2.1, p.2.2.1, p.2.2.2⟩ : YulSemantics.FDecl yul))) := by
  unfold YulSemantics.hoist
  induction prog with
  | nil => rfl
  | cons s rest ih =>
      cases s
      case funDef n ps rs b =>
          simp only [List.filterMap_cons]
          rw [ih]; rfl
      all_goals (simp only [List.filterMap_cons]; exact ih)

/-! ### Function entries are valid jump destinations -/

/-- A compiled function body begins with a `JUMPDEST` byte. -/
theorem compileFn_head_jumpdest {ft : FnTable} {entry : Nat} {ps rs : List Ident}
    {b : Block Op} {code : List Instr} (h : compileFn ft entry ps rs b = some code) :
    ∃ rest, assembleBytes code = (Instr.op .JUMPDEST).bytes ++ rest := by
  simp only [compileFn, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨bodyCode, Γb⟩, hbc, h⟩ := h
  split at h
  · rename_i hrs
    simp only [Option.pure_def, Option.some.injEq] at h
    subst h
    simp only [assembleBytes_append, assembleBytes_cons, assembleBytes_nil,
      List.append_nil, List.append_assoc]
    exact ⟨_, rfl⟩
  · exact absurd h (by simp)

/-- **A function entry is a valid `JUMPDEST`.** Whenever the whole program
`fullIs` decomposes as `preIs ++ code ++ postIs` with `code` a compiled function
body, the byte position `(assembleBytes preIs).length` is a valid jump
destination — exactly the recorded entry the call scaffold jumps to. -/
theorem entry_isValidJumpDest {ft : FnTable} {entry : Nat} {ps rs : List Ident}
    {b : Block Op} {code preIs postIs fullIs : List Instr}
    (hcode : compileFn ft entry ps rs b = some code)
    (hfull : fullIs = preIs ++ code ++ postIs) :
    Decode.isValidJumpDest (assemble fullIs) (assembleBytes preIs).length = true := by
  obtain ⟨rest, hrest⟩ := compileFn_head_jumpdest hcode
  have hrw : assemble fullIs
      = mkCode (assembleBytes preIs ++ (Instr.op .JUMPDEST).bytes
          ++ (rest ++ assembleBytes postIs)) := by
    show mkCode (assembleBytes fullIs) = _
    rw [hfull, assembleBytes_append, assembleBytes_append, hrest]
    simp only [List.append_assoc]
  rw [hrw]
  exact isValidJumpDest_boundary preIs (rest ++ assembleBytes postIs)

end YulEvmCompiler
