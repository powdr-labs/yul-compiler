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

/-- Every function `mergeOnce` can produce keeps `params` and `nrets`: the
merge only ever rebuilds `blocks` (and renumbers `entry`). -/
theorem mergeOnce_entry {f g : Func} (h : mergeOnce f = some g) :
    g.entry = f.entry := by
  unfold mergeOnce at h
  cases hm : findMerge f with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some q =>
      obtain ⟨bi, t⟩ := q
      rw [hm] at h
      dsimp only [Option.bind] at h
      obtain rfl := (Option.some.inj h).symm
      rfl

theorem mergeOnce_fields {f g : Func} (h : mergeOnce f = some g) :
    g.params = f.params ∧ g.nrets = f.nrets := by
  unfold mergeOnce at h
  cases hm : findMerge f with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some q =>
      obtain ⟨bi, t⟩ := q
      rw [hm] at h
      dsimp only [Option.bind] at h
      obtain rfl := (Option.some.inj h).symm
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

end Passes

end YulEvmCompiler.SsaCfg
