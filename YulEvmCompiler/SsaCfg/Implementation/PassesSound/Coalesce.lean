import YulEvmCompiler.SsaCfg.Implementation.PassesSound.Dve
set_option warningAsError true

/-!
# YulEvmCompiler.SsaCfg.Implementation.PassesSound.Coalesce

Support lemmas for **straight-line block coalescing** (`Passes.coalesce`).

The pass is a fuel-bounded loop of single merges (`Passes.mergeOnce`), so
everything here has the same two-layer shape as the trivial-parameter
elimination proofs: a fact about one merge, then the `loopWith` induction
that lifts it to the fixed point.

`dropUnreachable` is deliberately factored as
`{ f with entry := _, blocks := _ }` over a separate search
(`dropUnreachableCore`), which makes `params`/`nrets` preservation `rfl`
rather than an induction through its do-block.
-/

namespace YulEvmCompiler.SsaCfg

open YulSemantics.EVM (U256 EvmState Op builtinWithExternal stepOp ExternalCalls
  ExternalCreates)
open YulSemantics (Outcome)

namespace Passes

/-! ### One merge preserves the function's non-block fields -/

theorem params_with (f : Func) (e : BlockId) (bs : Array Block) :
    ({ f with entry := e, blocks := bs } : Func).params = f.params := rfl

theorem nrets_with (f : Func) (e : BlockId) (bs : Array Block) :
    ({ f with entry := e, blocks := bs } : Func).nrets = f.nrets := rfl

@[simp] theorem dropUnreachable_params (f : Func) :
    (dropUnreachable f).params = f.params := by
  simp only [dropUnreachable]

@[simp] theorem dropUnreachable_nrets (f : Func) :
    (dropUnreachable f).nrets = f.nrets := by
  simp only [dropUnreachable]

@[simp] theorem substFunc_params (σ : Subst) (f : Func) :
    (substFunc σ f).params = f.params := rfl

@[simp] theorem substFunc_nrets (σ : Subst) (f : Func) :
    (substFunc σ f).nrets = f.nrets := rfl

/-- Invert one merge: it fires only at a pair satisfying `mergeOK`, and its
result is the two-block update. Everything the well-formedness and
soundness proofs need is read off this, not off `findMerge`'s search. -/
theorem mergeOnce_inv {f g : Func} (h : mergeOnce f = some g) :
    ∃ bi t, mergeOK f bi t ∧
      g = { f with blocks :=
        (f.blocks.set! bi
          { params := f.blocks[bi]!.params,
            instrs := f.blocks[bi]!.instrs ++ f.blocks[t]!.instrs,
            term := f.blocks[t]!.term }).set! t blankBlock } := by
  unfold mergeOnce at h
  cases hm : findMerge f with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some q =>
      obtain ⟨bi, t⟩ := q
      rw [hm] at h
      dsimp only at h
      by_cases hok : mergeOK f bi t
      · rw [dif_pos hok] at h
        exact ⟨bi, t, hok, (Option.some.inj h).symm⟩
      · rw [dif_neg hok] at h
        exact absurd h (by simp)

theorem mergeOnce_entry {f g : Func} (h : mergeOnce f = some g) :
    g.entry = f.entry := by
  obtain ⟨bi, t, -, rfl⟩ := mergeOnce_inv h
  rfl

/-- Every function `mergeOnce` can produce keeps `params` and `nrets`. -/
theorem mergeOnce_fields {f g : Func} (h : mergeOnce f = some g) :
    g.params = f.params ∧ g.nrets = f.nrets := by
  obtain ⟨bi, t, -, rfl⟩ := mergeOnce_inv h
  exact ⟨rfl, rfl⟩

/-! ### The fixed-point loop -/

/-- The loop state of `coalesce`: an early-return slot plus the current
function (the same shape as `ElimTrivialLoopState`). -/
def coalesceStep (_ : Nat) (r : ElimTrivialLoopState) :
    ForInStep ElimTrivialLoopState :=
  match mergeOnce r.2 with
  | some f' => .yield ⟨none, f'⟩
  | none => .done ⟨some r.2, r.2⟩

theorem coalesceRaw_eq_loop (f : Func) :
    coalesceRaw f =
      let r := loopWith coalesceStep (List.range' 0 f.blocks.size 1) ⟨none, f⟩
      r.1.getD r.2 := by
  unfold coalesceRaw
  dsimp only
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rw [Id.forIn_eq_loopWith (g := coalesceStep)
    (h := by
      intro _ r
      cases hm : mergeOnce r.2 with
      | none => simp [coalesceStep, hm]
      | some f' => simp [coalesceStep, hm])]
  simp [Id.run, bind, pure, Option.getD]
  cases h : (loopWith coalesceStep
      (List.range' 0 f.blocks.size 1) (⟨none, f⟩ : ElimTrivialLoopState)).1 <;> simp

/-- Lift a property preserved by one merge to the whole fixed point. -/
theorem coalesceRaw_induction {motive : Func → Prop} (f : Func) (hf : motive f)
    (step : ∀ g g', motive g → mergeOnce g = some g' → motive g') :
    motive (coalesceRaw f) := by
  have loopInv : ∀ (xs : List Nat) (r : ElimTrivialLoopState),
      motive r.2 → (∀ h, r.1 = some h → motive h) →
      let out := loopWith coalesceStep xs r
      motive (out.1.getD out.2) := by
    intro xs
    induction xs with
    | nil =>
        intro r hr hr1
        dsimp only [loopWith_nil]
        cases h : r.1 with
        | none => simpa [h] using hr
        | some g => simpa [h] using hr1 g h
    | cons k ks ih =>
        intro r hr hr1
        rw [loopWith_cons]
        unfold coalesceStep
        cases hm : mergeOnce r.2 with
        | none => simpa using hr
        | some g' =>
            exact ih ⟨none, g'⟩ (step r.2 g' hr hm) (by simp)
  rw [coalesceRaw_eq_loop]
  exact loopInv (List.range' 0 f.blocks.size 1) ⟨none, f⟩ hf (by simp)

theorem coalesceRaw_params (f : Func) : (coalesceRaw f).params = f.params :=
  coalesceRaw_induction (motive := fun g => g.params = f.params) f rfl
    (fun _ _ hg hm => (mergeOnce_fields hm).1.trans hg)

theorem coalesceRaw_nrets (f : Func) : (coalesceRaw f).nrets = f.nrets :=
  coalesceRaw_induction (motive := fun g => g.nrets = f.nrets) f rfl
    (fun _ _ hg hm => (mergeOnce_fields hm).2.trans hg)

theorem coalesceRaw_entry (f : Func) : (coalesceRaw f).entry = f.entry :=
  coalesceRaw_induction (motive := fun g => g.entry = f.entry) f rfl
    (fun _ _ hg hm => (mergeOnce_entry hm).trans hg)

/-- The guard leaves only two possibilities: the coalesced function (with
its checks passing) or the input untouched. -/
theorem coalesce_cases (f : Func) :
    (coalesce f = coalesceRaw f ∧ (coalesceRaw f).allDefs.Nodup ∧
        ToAsm.Func.domCheck (coalesceRaw f) = true)
      ∨ coalesce f = f := by
  unfold coalesce
  dsimp only
  by_cases hg : (decide (coalesceRaw f).allDefs.Nodup
      && ToAsm.Func.domCheck (coalesceRaw f)) = true
  · rw [if_pos hg]
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
    exact Or.inl ⟨rfl, hg.1, hg.2⟩
  · rw [if_neg hg]
    exact Or.inr rfl

theorem coalesce_params (f : Func) : (coalesce f).params = f.params := by
  rcases coalesce_cases f with ⟨h, -, -⟩ | h
  · rw [h]; exact coalesceRaw_params f
  · rw [h]

theorem coalesce_nrets (f : Func) : (coalesce f).nrets = f.nrets := by
  rcases coalesce_cases f with ⟨h, -, -⟩ | h
  · rw [h]; exact coalesceRaw_nrets f
  · rw [h]

theorem coalesce_entry (f : Func) : (coalesce f).entry = f.entry := by
  rcases coalesce_cases f with ⟨h, -, -⟩ | h
  · rw [h]; exact coalesceRaw_entry f
  · rw [h]

/-! ### Structural facts about branch-sense normalization

`invertTerm` only ever swaps a `branch`'s two edges and rewrites its
condition, so it preserves the edge *set*, the `ret` arity, and (lifted
through the `Array.map`) every block's `params` and `instrs`. -/

theorem invertTerm_go_edges (m : Std.HashMap ValId ValId) :
    ∀ (n : Nat) (c : ValId) (t fe : Edge),
      (invertTerm.go m c t fe n).edges = [t, fe] ∨
        (invertTerm.go m c t fe n).edges = [fe, t]
  | 0, _, _, _ => Or.inl rfl
  | n + 1, c, t, fe => by
      unfold invertTerm.go
      cases hm : m[c]? with
      | none => exact Or.inl rfl
      | some x =>
          rcases invertTerm_go_edges m n x fe t with h | h
          · exact Or.inr h
          · exact Or.inl h

/-- The rewritten terminator has exactly the same edges, possibly swapped. -/
theorem invertTerm_mem_edges {m : Std.HashMap ValId ValId} {t : Term} {e : Edge}
    (he : e ∈ (invertTerm m t).edges) : e ∈ t.edges := by
  cases t with
  | branch c et ef =>
      rcases invertTerm_go_edges m 8 c et ef with h | h <;>
        · rw [show invertTerm m (.branch c et ef) = invertTerm.go m c et ef 8 from rfl,
            h] at he
          simp only [List.mem_cons, List.not_mem_nil, or_false] at he
          rcases he with rfl | rfl <;> simp [Term.edges]
  | jump e' => simpa [invertTerm] using he
  | ret vs => simpa [invertTerm] using he
  | halt yop as => simpa [invertTerm] using he

/-- `ret` terminators are untouched, so the return arity is unchanged. -/
theorem invertTerm_ret {m : Std.HashMap ValId ValId} {t : Term} {vs : List ValId}
    (h : invertTerm m t = .ret vs) : t = .ret vs := by
  cases t with
  | branch c et ef =>
      rcases invertTerm_go_edges m 8 c et ef with hg | hg <;>
        · rw [show invertTerm m (Term.branch c et ef) = invertTerm.go m c et ef 8 from rfl] at h
          rw [h] at hg
          simp [Term.edges] at hg
  | jump e' => simp [invertTerm] at h
  | ret ws => simp [invertTerm] at h; simp [h]
  | halt yop as => simp [invertTerm] at h

@[simp] theorem invertBranches_nrets (f : Func) :
    (invertBranches f).nrets = f.nrets := rfl

@[simp] theorem invertBranches_params (f : Func) :
    (invertBranches f).params = f.params := rfl

@[simp] theorem invertBranches_entry (f : Func) :
    (invertBranches f).entry = f.entry := rfl

@[simp] theorem invertBranches_size (f : Func) :
    (invertBranches f).blocks.size = f.blocks.size := by
  simp [invertBranches]

theorem invertBranches_get {f : Func} {i : Nat} {b : Block}
    (h : f.blocks[i]? = some b) :
    (invertBranches f).blocks[i]? =
      some { b with term := invertTerm (blockIszeroSources (useCounts f) b) b.term } := by
  simp [invertBranches, Array.getElem?_map, h]

/-- The argument of an `iszero` instruction is one of its operands. -/
theorem iszeroPair_uses {i : Instr} {d a : ValId} (h : iszeroPair i = some (d, a)) :
    a ∈ i.uses := by
  cases i with
  | const _ _ => simp [iszeroPair] at h
  | call _ _ _ => simp [iszeroPair] at h
  | op ds yop as =>
      cases ds with
      | nil => simp [iszeroPair] at h
      | cons d0 ds0 =>
        cases ds0 with
        | cons _ _ => simp [iszeroPair] at h
        | nil =>
          cases as with
          | nil => simp [iszeroPair] at h
          | cons a0 as0 =>
            cases as0 with
            | cons _ _ => simp [iszeroPair] at h
            | nil => cases yop <;> simp_all [iszeroPair, Instr.uses]

/-- `allDefs` only reads `params` and instruction `defs`, neither of which
the pass touches. -/
@[simp] theorem invertBranches_allDefs (f : Func) :
    (invertBranches f).allDefs = f.allDefs := by
  simp only [Func.allDefs, invertBranches, Array.toList_map, List.flatMap_map]

/-- Everything the per-block `iszero` table maps to is an operand of one of
that block's own instructions — in fact of its *last* one. This is what
makes the pass's use set shrink (and its soundness local). -/
theorem blockIszeroSources_mem {uses : Std.HashMap ValId Nat} {b : Block}
    {c x : ValId} (h : (blockIszeroSources uses b)[c]? = some x) :
    ∃ i ∈ b.instrs, x ∈ i.uses := by
  unfold blockIszeroSources at h
  split at h
  case _ i hlast =>
      split at h
      case _ d a heq =>
          by_cases hu : uses.getD d 0 == 1
          · rw [if_pos hu, Std.HashMap.getElem?_insert] at h
            by_cases hcd : c = d
            · subst hcd
              simp only [beq_self_eq_true, if_pos] at h
              exact ⟨i, List.mem_of_getLast? hlast,
                (Option.some.inj h).symm ▸ iszeroPair_uses heq⟩
            · rw [if_neg (by simpa using Ne.symm hcd)] at h; simp at h
          · rw [if_neg hu] at h; simp at h
      case _ => simp at h
  case _ => simp at h

/-- The rewritten terminator's uses are the original's, except that the
condition may have been replaced by something the `iszero` table maps to. -/
theorem invertTerm_go_uses (m : Std.HashMap ValId ValId) :
    ∀ (n : Nat) (c : ValId) (t fe : Edge) (y : ValId),
      y ∈ (invertTerm.go m c t fe n).uses →
        y ∈ (Term.branch c t fe).uses ∨ ∃ d : ValId, m[d]? = some y
  | 0, _, _, _, _, h => Or.inl h
  | n + 1, c, t, fe, y, h => by
      unfold invertTerm.go at h
      split at h
      case _ x hm =>
          rcases invertTerm_go_uses m n x fe t y h with h' | h'
          · simp only [Term.uses, List.mem_cons, List.mem_append] at h' ⊢
            rcases h' with (rfl | h') | h'
            · exact Or.inr ⟨c, hm⟩
            · exact Or.inl (Or.inr h')
            · exact Or.inl (Or.inl (Or.inr h'))
          · exact Or.inr h'
      case _ => exact Or.inl h

theorem invertTerm_uses {m : Std.HashMap ValId ValId} {t : Term} {y : ValId}
    (h : y ∈ (invertTerm m t).uses) : y ∈ t.uses ∨ ∃ d : ValId, m[d]? = some y := by
  cases t with
  | branch c et ef => exact invertTerm_go_uses m 8 c et ef y h
  | jump e' => exact Or.inl h
  | ret vs => exact Or.inl h
  | halt yop as => exact Or.inl h

/-- Branch-sense normalization can only *shrink* a block's use set: the new
condition is already used by the `iszero` instruction, which lives in the
same block. -/
theorem invertBranches_blockUses {f : Func} {b : Block} {y : ValId}
    (h : y ∈ ToAsm.blockUses
      { b with term := invertTerm (blockIszeroSources (useCounts f) b) b.term }) :
    y ∈ ToAsm.blockUses b := by
  rw [ToAsm.blockUses, ToAsm.mem_unionS] at h ⊢
  rcases h with hi | ht
  · exact Or.inl hi
  · rw [ToAsm.mem_unionS] at ht
    rcases ht with ht | hnil
    · rcases invertTerm_uses ht with h' | ⟨d, hd⟩
      · exact Or.inr (ToAsm.mem_unionS.mpr (Or.inl h'))
      · obtain ⟨i, hi, hyi⟩ := blockIszeroSources_mem hd
        exact Or.inl (List.mem_flatMap.mpr ⟨i, hi, hyi⟩)
    · simp at hnil

/-! ### Well-formedness

The one non-structural conjunct (`allDefs.Nodup`) comes from the pass's own
guard; the rest is preserved by every single merge, because no block's
`params` changes (the merged block keeps its own, and the absorbed block
already had none) and the merged block's instructions and terminator are
exactly ones that were already present. -/

/-- Updating two positions of a block array, where the new blocks have the
same parameter lists as the old ones, leaves every parameter list alone. -/
theorem params_get_two_set (bs : Array Block) (bi t : BlockId) (mb : Block)
    (hbi : bi < bs.size) (ht : t < bs.size) (hne : t ≠ bi)
    (hmb : mb.params = bs[bi].params) (htp : bs[t].params = []) (j : Nat) :
    (((bs.set! bi mb).set! t blankBlock)[j]?.map Block.params)
      = (bs[j]?.map Block.params) := by
  by_cases hjt : j = t
  · subst hjt
    simp [Array.set!, ht, blankBlock, htp]
  · by_cases hjb : j = bi
    · subst hjb
      simp [Array.set!, Ne.symm hjt, hbi, hmb]
    · simp [Array.set!, Ne.symm hjt, Ne.symm hjb]

/-- No block's parameter list changes across a merge, so every edge's
argument count still matches its target's arity. -/
theorem mergeOnce_params_get {f g : Func} (h : mergeOnce f = some g) (j : Nat) :
    (g.blocks[j]?.map Block.params) = (f.blocks[j]?.map Block.params) := by
  obtain ⟨bi, t, hok, rfl⟩ := mergeOnce_inv h
  obtain ⟨hbi, ht, -, hne, -, htp⟩ := hok
  exact params_get_two_set f.blocks bi t _ hbi ht hne
    (by simp [getElem!_eq_getElem hbi]) (by simpa [getElem!_eq_getElem ht] using htp) j

/-- Structural well-formedness (everything except single assignment). -/
def WfStruct (f : Func) (n : Nat) : Prop :=
  f.entry < f.blocks.size ∧ (∃ eb, f.blocks[f.entry]? = some eb ∧ eb.params = []) ∧
    ∀ b ∈ f.blocks.toList, BlockWF f.blocks f.nrets n b

/-- Look up the same index in a parameter-preserving rewrite of a block
array: the block is still there, with the same parameters. -/
theorem params_transfer {bs bs' : Array Block} {k : Nat} {b : Block}
    (hp : ∀ j : Nat, bs'[j]?.map Block.params = bs[j]?.map Block.params)
    (h : bs[k]? = some b) : ∃ b', bs'[k]? = some b' ∧ b'.params = b.params := by
  have hk0 := hp k
  rw [h] at hk0
  rcases hk : bs'[k]? with _ | b'
  · rw [hk] at hk0; simp at hk0
  · rw [hk] at hk0
    exact ⟨b', rfl, Option.some.inj (by simpa using hk0)⟩

/-- Transfer an edge's arity obligation across such a rewrite. -/
theorem edge_ok_transfer {bs bs' : Array Block} {k L : Nat}
    (hp : ∀ j : Nat, bs'[j]?.map Block.params = bs[j]?.map Block.params)
    (h : ∃ tb, bs[k]? = some tb ∧ L = tb.params.length) :
    ∃ tb', bs'[k]? = some tb' ∧ L = tb'.params.length := by
  obtain ⟨tb, htb, hlen⟩ := h
  obtain ⟨tb', htb', hpp⟩ := params_transfer hp htb
  exact ⟨tb', htb', by rw [hpp]; exact hlen⟩

theorem mergeOnce_size {f g : Func} (h : mergeOnce f = some g) :
    g.blocks.size = f.blocks.size := by
  obtain ⟨bi, t, -, rfl⟩ := mergeOnce_inv h
  simp [Array.set!]

/-- One merge preserves structural well-formedness. -/
theorem mergeOnce_wfStruct {f g : Func} {n : Nat}
    (hs : WfStruct f n) (h : mergeOnce f = some g) : WfStruct g n := by
  obtain ⟨hentry, ⟨eb, heb, hebp⟩, hall⟩ := hs
  have hp := mergeOnce_params_get h
  obtain ⟨bi, t, hok, hgdef⟩ := mergeOnce_inv h
  obtain ⟨hbi, ht, hte, hne, hjump, htp⟩ := hok
  subst hgdef
  have hmemf : ∀ k : Nat, k < f.blocks.size → f.blocks[k]! ∈ f.blocks.toList :=
    fun k hk => by
      rw [getElem!_eq_getElem hk]
      exact List.mem_iff_getElem.mpr ⟨k, by simpa using hk, by simp⟩
  refine ⟨by simpa [Array.set!] using hentry, ?_, ?_⟩
  · obtain ⟨eb', heb', hpp⟩ := params_transfer hp heb
    exact ⟨eb', heb', by rw [hpp]; exact hebp⟩
  · intro b' hb'
    obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp hb'
    rw [← hjeq, Array.getElem_toList]
    have hjf : j < f.blocks.size := by
      have : j < ((f.blocks.set! bi
        ⟨f.blocks[bi]!.params, f.blocks[bi]!.instrs ++ f.blocks[t]!.instrs,
          f.blocks[t]!.term⟩).set! t blankBlock).size := by simpa using hj
      simpa [Array.set!] using this
    by_cases hjt : j = t
    · subst hjt
      have hb : ((f.blocks.set! bi
          ⟨f.blocks[bi]!.params, f.blocks[bi]!.instrs ++ f.blocks[j]!.instrs,
            f.blocks[j]!.term⟩).set! j blankBlock)[j] = blankBlock := by
        simp [Array.set!, ht]
      rw [hb]
      exact ⟨by simp [blankBlock], by simp [blankBlock, Term.edges], by simp [blankBlock]⟩
    · by_cases hjb : j = bi
      · have hb : ((f.blocks.set! bi
            ⟨f.blocks[bi]!.params, f.blocks[bi]!.instrs ++ f.blocks[t]!.instrs,
              f.blocks[t]!.term⟩).set! t blankBlock)[j] =
            ⟨f.blocks[bi]!.params, f.blocks[bi]!.instrs ++ f.blocks[t]!.instrs,
              f.blocks[t]!.term⟩ := by
          simp [Array.set!, hjb, hbi, Array.getElem_setIfInBounds_ne, hne]
        rw [hb]
        have hbwfB := hall _ (hmemf bi hbi)
        have hbwfT := hall _ (hmemf t ht)
        refine ⟨hbwfT.1, ?_, ?_⟩
        · intro e he
          exact edge_ok_transfer hp (hbwfT.2.1 e he)
        · intro i hi
          rcases List.mem_append.mp hi with hi | hi
          · exact hbwfB.2.2 i hi
          · exact hbwfT.2.2 i hi
      · have hb : ((f.blocks.set! bi
            ⟨f.blocks[bi]!.params, f.blocks[bi]!.instrs ++ f.blocks[t]!.instrs,
              f.blocks[t]!.term⟩).set! t blankBlock)[j] = f.blocks[j]! := by
          rw [getElem!_eq_getElem hjf]
          simp only [Array.set!]
          rw [Array.getElem_setIfInBounds_ne (by simpa using hjf) (Ne.symm hjt),
            Array.getElem_setIfInBounds_ne hjf (Ne.symm hjb)]
        rw [hb]
        have hbwf := hall _ (hmemf j hjf)
        refine ⟨hbwf.1, ?_, hbwf.2.2⟩
        intro e he
        exact edge_ok_transfer hp (hbwf.2.1 e he)

theorem coalesceRaw_wfStruct {f : Func} {n : Nat} (hs : WfStruct f n) :
    WfStruct (coalesceRaw f) n :=
  coalesceRaw_induction (motive := fun g => WfStruct g n) f hs
    (fun _ _ hg hm => mergeOnce_wfStruct hg hm)

/-- **Well-formedness preservation for block coalescing.** The structural
conjuncts are preserved by every merge; single assignment — the one that
would otherwise need a permutation argument over two array updates — is read
off the pass's own guard. -/
theorem coalesce_wf {f : Func} {n : Nat} (hwf : f.wfCheck n = true) :
    (coalesce f).wfCheck n = true := by
  obtain ⟨hnd, hentry, hebq, hall⟩ := func_wfCheck_iff.mp hwf
  rcases coalesce_cases f with ⟨heq, hnd', -⟩ | heq
  · rw [heq]
    obtain ⟨he, hebq', hall'⟩ := coalesceRaw_wfStruct (n := n) ⟨hentry, hebq, hall⟩
    exact func_wfCheck_iff.mpr ⟨hnd', he, hebq', hall'⟩
  · rw [heq]; exact hwf

end Passes

end YulEvmCompiler.SsaCfg
