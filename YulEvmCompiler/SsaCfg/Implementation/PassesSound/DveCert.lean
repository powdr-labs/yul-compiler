import YulEvmCompiler.SsaCfg.Implementation.PassesSound.Counterexample
set_option warningAsError true

/-!
# YulEvmCompiler.SsaCfg.Implementation.PassesSound.DveCert

Pass 4's structural specification, and its liveness loop as folds.

`dveBlock` and what the rewrite does to the liveness data, the generic
`forIn`-to-`foldl` bridge (`Id.forIn_eq_foldl`, `loopWith`), and the pure
fold model of the backward-liveness loop with its inflationary/bounded
convergence argument.
-/

namespace YulEvmCompiler.SsaCfg
open YulSemantics.EVM (U256 EvmState Op builtinWithExternal stepOp ExternalCalls
  ExternalCreates)
open YulSemantics (Outcome)

namespace Passes

/-! ### Pass 4's structural specification

`dve` is the one pass written *without* an `Id.run` loop — a `mapIdx` with
filters — so its output is directly readable, and these lemmas are the complete
structural half of both `dve_sound` and `dve_dom`. -/

/-- The block rewrite `dve` performs, as a function (its `mapIdx` body). -/
def dveBlock (f : Func) (bi : BlockId) (b : Block) : Block :=
  let live := liveSet f
  let keepParam : BlockId → Nat → Bool := fun bi i =>
    match f.blocks[bi]? with
    | some b =>
      match b.params[i]? with
      | some p => live.contains p
      | none => true
    | none => true
  { params := if bi == f.entry then b.params else b.params.filter live.contains
    instrs := b.instrs.filter fun i =>
      match i with
      | .const d _ => live.contains d
      | .op ds yop _ => !pureOp yop || ds.any live.contains
      | .call .. => true
    term := mapEdges (fun (e : Edge) =>
      { e with args := (e.args.zipIdx.filter fun ai => keepParam e.target ai.2).map (·.1) }) b.term }

/-- `dve` is a plain `mapIdx`: block `i` of the output is `dveBlock f i` of block
`i` of the input. -/
theorem dve_blocks_get (f : Func) (i : BlockId) :
    (dve f).blocks[i]? = (f.blocks[i]?).map (dveBlock f i) := by
  simp only [dve, Array.getElem?_mapIdx]
  rfl

theorem dve_params (f : Func) : (dve f).params = f.params := rfl
theorem dve_entry (f : Func) : (dve f).entry = f.entry := rfl
theorem dve_size (f : Func) : (dve f).blocks.size = f.blocks.size := by simp [dve]

/-! ### What the rewrite does to the liveness data -/

theorem mapEdges_uses_sub {g : Edge → Edge} (hargs : ∀ e x, x ∈ (g e).args → x ∈ e.args)
    (t : Term) {x : ValId} (h : x ∈ (mapEdges g t).uses) : x ∈ t.uses := by
  cases t with
  | jump e => exact hargs _ _ h
  | branch c t0 f0 =>
    have h' : x = c ∨ x ∈ (g t0).args ∨ x ∈ (g f0).args := by
      simpa [mapEdges, Term.uses] using h
    have h'' : x = c ∨ x ∈ t0.args ∨ x ∈ f0.args := by
      rcases h' with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl (hargs _ _ h1))
      · exact Or.inr (Or.inr (hargs _ _ h1))
    simpa [Term.uses] using h''
  | ret vs => exact h
  | halt yop as => exact h

theorem mapEdges_edges {g : Edge → Edge} (t : Term) {e : Edge}
    (h : e ∈ (mapEdges g t).edges) : ∃ e0 ∈ t.edges, g e0 = e := by
  cases t with
  | jump e0 =>
    have he : e = g e0 := by simpa [mapEdges, Term.edges] using h
    exact ⟨e0, by simp [Term.edges], he.symm⟩
  | branch c t0 f0 =>
    have he : e = g t0 ∨ e = g f0 := by simpa [mapEdges, Term.edges] using h
    rcases he with rfl | rfl
    · exact ⟨t0, by simp [Term.edges], rfl⟩
    · exact ⟨f0, by simp [Term.edges], rfl⟩
  | ret vs => simp [mapEdges, Term.edges] at h
  | halt yop as => simp [mapEdges, Term.edges] at h


/-- Uses can only shrink: `dve` deletes instructions and drops edge arguments. -/
theorem dveBlock_uses_sub {f : Func} {i : BlockId} {b : Block} {x : ValId}
    (h : x ∈ ToAsm.blockUses (dveBlock f i b)) : x ∈ ToAsm.blockUses b := by
  rw [ToAsm.mem_blockUses] at h ⊢
  rcases h with h | h
  · refine Or.inl ?_
    simp only [List.mem_flatMap] at h ⊢
    obtain ⟨ins, hins, hx⟩ := h
    exact ⟨ins, List.mem_of_mem_filter hins, hx⟩
  · refine Or.inr (mapEdges_uses_sub ?_ b.term h)
    intro e y hy
    simp only [List.mem_map, List.mem_filter] at hy
    obtain ⟨ai, ⟨hmem, -⟩, rfl⟩ := hy
    exact List.fst_mem_of_mem_zipIdx hmem

/-- …and a **live** definition is always kept. -/
theorem dveBlock_defs_of_live {f : Func} {i : BlockId} {b : Block} {x : ValId}
    (hlive : (liveSet f).contains x = true) (h : x ∈ ToAsm.blockDefs b) :
    x ∈ ToAsm.blockDefs (dveBlock f i b) := by
  rw [ToAsm.mem_blockDefs] at h ⊢
  rcases h with h | h
  · refine Or.inl ?_
    by_cases he : (i == f.entry) = true
    · simpa [dveBlock, he] using h
    · have : x ∈ b.params.filter (liveSet f).contains := List.mem_filter.mpr ⟨h, by simpa using hlive⟩
      simpa [dveBlock, he] using this
  · refine Or.inr ?_
    simp only [List.mem_flatMap] at h ⊢
    obtain ⟨ins, hins, hx⟩ := h
    refine ⟨ins, List.mem_filter.mpr ⟨hins, ?_⟩, hx⟩
    cases ins with
    | const d v =>
      simp only [Instr.defs, List.mem_singleton] at hx
      subst hx
      simpa using hlive
    | op ds yop as =>
      simp only [Instr.defs] at hx
      by_cases hp : pureOp yop
      · simp only [hp, Bool.not_true, Bool.false_or]
        exact List.any_eq_true.mpr ⟨x, hx, hlive⟩
      · simp [hp]
    | call ds g as => simp

/-- Edge targets are untouched (only argument *positions* are dropped). -/
theorem dveBlock_edge_target {f : Func} {i : BlockId} {b : Block} {e : Edge}
    (h : e ∈ (dveBlock f i b).term.edges) : ∃ e0 ∈ b.term.edges, e0.target = e.target := by
  obtain ⟨e0, hmem, rfl⟩ := mapEdges_edges b.term h
  exact ⟨e0, hmem, rfl⟩

end Passes

/-! ## `forIn`-to-`foldl`

Every pass in `Passes.lean` is written as an `Id.run do` loop, so every
structural specification has to turn a `forIn` into something inductive. These
two lemmas do it once. The step function `g` is a *parameter* rather than
inferred, because a `match`-shaped loop body keeps its `pure` inside each branch
and so never matches the pattern `fun a b => pure (.yield (?g a b))`; the caller
supplies `g` and discharges `h` by case analysis. Pass `h` as a tactic block
(`h := by …`) so that its elaboration is postponed until `rw` has unified `body`
with the goal.

Two things worth recording for the next pass: the do-elaborator packs mutable
state in `MProd`, not `Prod`, and `dsimp only` is needed first to zeta-reduce
the `have`s that otherwise leave the loop under binders. -/

theorem Id.forIn_eq_foldl {α β : Type} {body : α → β → Id (ForInStep β)} {g : α → β → β}
    (h : ∀ a b, body a b = pure (ForInStep.yield (g a b))) (l : List α) (init : β) :
    (forIn l init body : Id β) = l.foldl (fun b a => g a b) init := by
  induction l generalizing init with
  | nil => rfl
  | cons a as ih => simp only [List.forIn_cons, h a init, List.foldl_cons]; exact ih (g a init)

theorem Id.forIn_array_eq_foldl {α β : Type} {body : α → β → Id (ForInStep β)} {g : α → β → β}
    (h : ∀ a b, body a b = pure (ForInStep.yield (g a b))) (as : Array α) (init : β) :
    (forIn as init body : Id β) = as.toList.foldl (fun b a => g a b) init := by
  rw [← Array.forIn_toList]; exact Id.forIn_eq_foldl h _ init


/-! ### Early-return loops -/

/-- The pure model of a `for` loop whose body may break: fold until a step
returns `.done`, then stop. -/
def loopWith {α β : Type} (g : α → β → ForInStep β) : List α → β → β
  | [], b => b
  | a :: as, b =>
    match g a b with
    | .yield b' => loopWith g as b'
    | .done b' => b'

@[simp] theorem loopWith_nil {α β : Type} (g : α → β → ForInStep β) (b : β) :
    loopWith g [] b = b := rfl

theorem loopWith_cons {α β : Type} (g : α → β → ForInStep β) (a : α) (as : List α) (b : β) :
    loopWith g (a :: as) b =
      match g a b with
      | .yield b' => loopWith g as b'
      | .done b' => b' := rfl

/-- **`forIn`-to-`loopWith` bridge**: the early-return counterpart of
`Id.forIn_eq_foldl`. A `for` loop in `Id` whose body may `return` is
`loopWith`. -/
theorem Id.forIn_eq_loopWith {α β : Type} {body : α → β → Id (ForInStep β)}
    {g : α → β → ForInStep β} (h : ∀ a b, body a b = pure (g a b)) (l : List α) (init : β) :
    (forIn l init body : Id β) = loopWith g l init := by
  induction l generalizing init with
  | nil => rfl
  | cons a as ih =>
    rw [List.forIn_cons, h a init, loopWith_cons]
    cases g a init with
    | yield b' => simpa using ih b'
    | done b' => rfl

/-! ### The early-return protocol

`return` inside a `for` compiles to a loop whose state is
`MProd (Option ρ) σ` — an `Option` holding the returned value alongside the real
mutable state — with `.done` carrying `some result`. This example records the
shape (it is what `findTrivialParam`, `inlineOnce` and `inlineFunc` all use), so
the next application of the bridge does not have to rediscover it. -/

private example (l : List Nat) (init : MProd (Option (Option Nat)) PUnit) :
    (forIn l init (fun (x : Nat) (_ : MProd (Option (Option Nat)) PUnit) =>
        (if x > 10 then pure (ForInStep.done ⟨some (some x), PUnit.unit⟩)
         else pure (ForInStep.yield ⟨none, PUnit.unit⟩) : Id _)))
      = loopWith (fun (x : Nat) (_ : MProd (Option (Option Nat)) PUnit) =>
          if x > 10 then ForInStep.done ⟨some (some x), PUnit.unit⟩
          else ForInStep.yield ⟨none, PUnit.unit⟩) l init :=
  Id.forIn_eq_loopWith (fun x r => by split <;> rfl) l init

namespace Passes

/-! ### Pass 4's liveness loop, as folds -/

def dveLiveInstrStep (ins : Instr) (live : Std.HashSet ValId) : Std.HashSet ValId :=
  match ins with
  | .const _ _ => live
  | .op ds yop args =>
      if !pureOp yop || ds.any live.contains then
        args.foldl (fun s a => s.insert a) live
      else live
  | .call _ _ args => args.foldl (fun s a => s.insert a) live

def dveLiveTermStep (t : Term) (live : Std.HashSet ValId) : Std.HashSet ValId :=
  match t with
  | .jump _ => live
  | .branch c _ _ => live.insert c
  | .ret vs => vs.foldl (fun s a => s.insert a) live
  | .halt _ as => as.foldl (fun s a => s.insert a) live

def dveLiveEdgeStep (f : Func) (e : Edge) (live : Std.HashSet ValId) : Std.HashSet ValId :=
  match f.blocks[e.target]? with
  | none => live
  | some tb =>
      (tb.params.zip e.args).foldl (fun live pa =>
        if live.contains pa.1 then live.insert pa.2 else live) live

def dveLiveBlockStep (f : Func) (b : Block) (live : Std.HashSet ValId) : Std.HashSet ValId :=
  b.term.edges.foldl (fun live e => dveLiveEdgeStep f e live)
    (dveLiveTermStep b.term
      (b.instrs.foldl (fun live ins => dveLiveInstrStep ins live) live))

theorem dveLiveInstrLoop_eq (is : List Instr) (live : Std.HashSet ValId) :
    (forIn is live (fun ins live =>
      match ins with
      | .const _ _ => do pure (); pure (.yield live)
      | .op ds yop args =>
          if !pureOp yop || ds.any live.contains then
            do pure PUnit.unit; pure (.yield (args.foldl (fun s a => s.insert a) live))
          else do pure PUnit.unit; pure (.yield live)
      | .call _ _ args =>
          do pure PUnit.unit; pure (.yield (args.foldl (fun s a => s.insert a) live))) :
        Id (Std.HashSet ValId)) =
      pure (is.foldl (fun live ins => dveLiveInstrStep ins live) live) := by
  simp only [LawfulMonad.pure_bind]
  apply Eq.trans (Id.forIn_eq_foldl (g := dveLiveInstrStep) (h := by
    intro ins live
    cases ins with
    | const d v => rfl
    | op ds yop args => simp only [dveLiveInstrStep]; split <;> rfl
    | call ds fid args => rfl) is live)
  rfl

theorem dveLiveEdgeLoop_eq (f : Func) (es : List Edge) (live : Std.HashSet ValId) :
    (forIn es live (fun e live =>
      match f.blocks[e.target]? with
      | some tb => do
          let live ← forIn (tb.params.zip e.args) live (fun pa live =>
            if live.contains pa.1 then pure (.yield (live.insert pa.2))
            else pure (.yield live))
          pure (.yield live)
      | _ => pure (.yield live)) : Id (Std.HashSet ValId)) =
      pure (es.foldl (fun live e => dveLiveEdgeStep f e live) live) := by
  apply Eq.trans (Id.forIn_eq_foldl (g := dveLiveEdgeStep f) (h := by
    intro e live
    rcases hb : f.blocks[e.target]? with _ | tb
    · simp [dveLiveEdgeStep, hb]
    · simp only [dveLiveEdgeStep, hb]
      rw [Id.forIn_eq_foldl (g := fun pa live =>
        if live.contains pa.1 then live.insert pa.2 else live) (h := by
          intro pa (live : Std.HashSet ValId)
          split <;> rfl)]
      rfl) es live)
  rfl

theorem liveStep_eq_fold (f : Func) (live : Std.HashSet ValId) :
    liveStep f live =
      f.blocks.toList.foldl (fun live b => dveLiveBlockStep f b live) live := by
  unfold liveStep
  dsimp only
  rw [Id.forIn_array_eq_foldl (g := dveLiveBlockStep f) (h := by
    intro b live
    dsimp only [dveLiveBlockStep]
    conv_lhs =>
      congr
      · exact dveLiveInstrLoop_eq b.instrs live
    simp only [LawfulMonad.pure_bind]
    cases b.term <;>
      simp only [Term.edges, dveLiveTermStep] <;>
      (conv_lhs =>
        congr
        · exact dveLiveEdgeLoop_eq f _ _) <;>
      exact LawfulMonad.pure_bind _ _)]
  rfl

def HashSub (A B : Std.HashSet ValId) : Prop := ∀ x, x ∈ A → x ∈ B

theorem HashSub.refl (A : Std.HashSet ValId) : HashSub A A := fun _ h => h

theorem HashSub.trans {A B C : Std.HashSet ValId} (hAB : HashSub A B)
    (hBC : HashSub B C) : HashSub A C := fun x hx => hBC x (hAB x hx)

theorem fold_insert_sub (xs : List ValId) (s : Std.HashSet ValId) :
    HashSub s (xs.foldl (fun s x => s.insert x) s) := by
  induction xs generalizing s with
  | nil => exact HashSub.refl s
  | cons x xs ih =>
      exact HashSub.trans (fun y hy => Std.HashSet.mem_insert.mpr (Or.inr hy)) (ih (s.insert x))

theorem fold_sub {α : Type} {step : α → Std.HashSet ValId → Std.HashSet ValId}
    (hstep : ∀ a s, HashSub s (step a s)) (xs : List α) (s : Std.HashSet ValId) :
    HashSub s (xs.foldl (fun s a => step a s) s) := by
  induction xs generalizing s with
  | nil => exact HashSub.refl s
  | cons a xs ih => exact HashSub.trans (hstep a s) (ih (step a s))

theorem dveLiveInstrStep_inflationary (i : Instr) (s : Std.HashSet ValId) :
    HashSub s (dveLiveInstrStep i s) := by
  cases i with
  | const d v => exact HashSub.refl s
  | op ds yop args =>
      simp only [dveLiveInstrStep]
      split
      · exact fold_insert_sub args s
      · exact HashSub.refl s
  | call ds fid args => exact fold_insert_sub args s

theorem dveLiveTermStep_inflationary (t : Term) (s : Std.HashSet ValId) :
    HashSub s (dveLiveTermStep t s) := by
  cases t with
  | jump e => exact HashSub.refl s
  | branch c et ef => exact fun x hx => Std.HashSet.mem_insert.mpr (Or.inr hx)
  | ret vs => exact fold_insert_sub vs s
  | halt yop args => exact fold_insert_sub args s

theorem dveLiveEdgeStep_inflationary (f : Func) (e : Edge) (s : Std.HashSet ValId) :
    HashSub s (dveLiveEdgeStep f e s) := by
  simp only [dveLiveEdgeStep]
  split
  · exact HashSub.refl s
  · exact fold_sub (fun pa live => by
      split
      · exact fun x hx => Std.HashSet.mem_insert.mpr (Or.inr hx)
      · exact HashSub.refl live) _ s

theorem dveLiveBlockStep_inflationary (f : Func) (b : Block) (s : Std.HashSet ValId) :
    HashSub s (dveLiveBlockStep f b s) := by
  exact HashSub.trans
    (fold_sub dveLiveInstrStep_inflationary b.instrs s |>.trans
      (dveLiveTermStep_inflationary b.term _))
    (fold_sub (dveLiveEdgeStep_inflationary f) b.term.edges _)

theorem liveStep_inflationary (f : Func) (s : Std.HashSet ValId) :
    HashSub s (liveStep f s) := by
  rw [liveStep_eq_fold]
  exact fold_sub (dveLiveBlockStep_inflationary f) f.blocks.toList s

theorem hashEquiv_of_sub_size_eq {A B : Std.HashSet ValId} (hsub : HashSub A B)
    (hsize : A.size = B.size) : A.Equiv B := by
  have hnd : A.toList.Nodup :=
    (Std.HashSet.distinct_toList (m := A)).imp (by simp_all)
  have hsp : A.toList.Subperm B.toList := List.subperm_of_subset hnd (fun x hx => by
    rw [Std.HashSet.mem_toList] at hx ⊢
    exact hsub x hx)
  have hp : A.toList.Perm B.toList := hsp.perm_of_length_le (by simpa using hsize.symm.le)
  exact (Std.HashSet.equiv_iff_toList_perm).mpr hp

def HashBound (s : Std.HashSet ValId) (U : List ValId) : Prop := ∀ x, x ∈ s → x ∈ U

theorem fold_insert_bound {xs U : List ValId} {s : Std.HashSet ValId}
    (hs : HashBound s U) (hxs : ∀ x ∈ xs, x ∈ U) :
    HashBound (xs.foldl (fun s x => s.insert x) s) U := by
  induction xs generalizing s with
  | nil => exact hs
  | cons a xs ih =>
      apply ih (s := s.insert a)
      · intro x hx
        rw [Std.HashSet.mem_insert] at hx
        rcases hx with hx | hx
        · have : a = x := (beq_iff_eq).mp hx
          subst x
          exact hxs a (by simp)
        · exact hs x hx
      · exact fun x hx => hxs x (by simp [hx])

theorem fold_bound {α : Type} {step : α → Std.HashSet ValId → Std.HashSet ValId}
    {xs : List α} {U : List ValId} {s : Std.HashSet ValId}
    (hs : HashBound s U)
    (hstep : ∀ a ∈ xs, ∀ s, HashBound s U → HashBound (step a s) U) :
    HashBound (xs.foldl (fun s a => step a s) s) U := by
  induction xs generalizing s with
  | nil => exact hs
  | cons a xs ih =>
      exact ih (hstep a (by simp) s hs) (fun x hx => hstep x (by simp [hx]))

theorem snd_mem_of_mem_zip {α β : Type} {xs : List α} {ys : List β} {p : α × β}
    (h : p ∈ xs.zip ys) : p.2 ∈ ys := by
  induction xs generalizing ys with
  | nil => simp at h
  | cons x xs ih =>
      cases ys with
      | nil => simp at h
      | cons y ys =>
          simp only [List.zip_cons_cons, List.mem_cons] at h
          rcases h with rfl | h
          · simp
          · exact List.mem_cons_of_mem _ (ih h)

theorem dveLiveInstrStep_bound {i : Instr} {s : Std.HashSet ValId} {U : List ValId}
    (hs : HashBound s U) (hi : ∀ x ∈ i.uses, x ∈ U) :
    HashBound (dveLiveInstrStep i s) U := by
  cases i with
  | const d v => exact hs
  | op ds yop args =>
      simp only [dveLiveInstrStep]
      split
      · exact fold_insert_bound hs (by simpa [Instr.uses] using hi)
      · exact hs
  | call ds fid args => exact fold_insert_bound hs (by simpa [Instr.uses] using hi)

theorem dveLiveTermStep_bound {t : Term} {s : Std.HashSet ValId} {U : List ValId}
    (hs : HashBound s U) (ht : ∀ x ∈ t.uses, x ∈ U) :
    HashBound (dveLiveTermStep t s) U := by
  cases t with
  | jump e => exact hs
  | branch c et ef =>
    intro x hx
    simp only [dveLiveTermStep] at hx
    rw [Std.HashSet.mem_insert] at hx
    rcases hx with hx | hx
    · have : c = x := (beq_iff_eq).mp hx
      subst x
      exact ht c (by simp [Term.uses])
    · exact hs x hx
  | ret vs => exact fold_insert_bound hs (by simpa [Term.uses] using ht)
  | halt yop args => exact fold_insert_bound hs (by simpa [Term.uses] using ht)

theorem dveLiveEdgeStep_bound {f : Func} {e : Edge} {s : Std.HashSet ValId}
    {U : List ValId} (hs : HashBound s U) (he : ∀ x ∈ e.args, x ∈ U) :
    HashBound (dveLiveEdgeStep f e s) U := by
  simp only [dveLiveEdgeStep]
  split
  · exact hs
  · apply fold_bound hs
    intro pa hpa live hlive
    split
    · intro x hx
      rw [Std.HashSet.mem_insert] at hx
      rcases hx with hx | hx
      · have heq : pa.2 = x := (beq_iff_eq).mp hx
        rw [← heq]
        exact he pa.2 (snd_mem_of_mem_zip hpa)
      · exact hlive x hx
    · exact hlive

theorem edge_args_mem_term_uses {t : Term} {e : Edge} (he : e ∈ t.edges)
    {x : ValId} (hx : x ∈ e.args) : x ∈ t.uses := by
  cases t with
  | jump e' =>
      simp only [Term.edges, List.mem_singleton] at he
      subst e
      exact hx
  | branch c et ef =>
      simp [Term.edges] at he
      rcases he with rfl | rfl
      · simp [Term.uses, hx]
      · simp [Term.uses, hx]
  | ret vs => simp [Term.edges] at he
  | halt yop args => simp [Term.edges] at he

theorem dveLiveBlockStep_bound {f : Func} {b : Block} {s : Std.HashSet ValId}
    {U : List ValId} (hs : HashBound s U)
    (hi : ∀ i ∈ b.instrs, ∀ x ∈ i.uses, x ∈ U)
    (ht : ∀ x ∈ b.term.uses, x ∈ U) : HashBound (dveLiveBlockStep f b s) U := by
  have hiBound : HashBound
      (b.instrs.foldl (fun live i => dveLiveInstrStep i live) s) U :=
    fold_bound hs (by
      intro i him live hlive
      exact dveLiveInstrStep_bound hlive (hi i him))
  have htBound := dveLiveTermStep_bound hiBound ht
  apply fold_bound htBound
  intro e he live hlive
  apply dveLiveEdgeStep_bound hlive
  intro x hx
  exact ht x (edge_args_mem_term_uses he hx)

theorem liveStep_bound {f : Func} {s : Std.HashSet ValId}
    (hs : HashBound s f.allUses) : HashBound (liveStep f s) f.allUses := by
  rw [liveStep_eq_fold]
  apply fold_bound hs
  intro b hb live hlive
  apply dveLiveBlockStep_bound hlive
  · intro i hi x hx
    simp only [Func.allUses, List.mem_flatMap]
    exact ⟨b, hb, List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr ⟨i, hi, hx⟩))⟩
  · intro x hx
    simp only [Func.allUses, List.mem_flatMap]
    exact ⟨b, hb, List.mem_append.mpr (Or.inr hx)⟩

theorem hashSize_le_of_bound {s : Std.HashSet ValId} {U : List ValId}
    (h : HashBound s U) : s.size ≤ U.length := by
  rw [← Std.HashSet.length_toList]
  exact (List.subperm_of_subset
    ((Std.HashSet.distinct_toList (m := s)).imp (by simp_all))
    (fun x hx => h x (Std.HashSet.mem_toList.mp hx))).length_le

def dveFuel (f : Func) : Nat :=
  f.blocks.foldl (init := f.allDefs.length + 2) fun n b =>
    n + b.instrs.foldl (fun m i => m + i.uses.length) b.term.uses.length

abbrev DVELoopState := MProd (Option (Std.HashSet ValId)) (Std.HashSet ValId)

def dveLoopStep (f : Func) (_ : Nat) (r : DVELoopState) : ForInStep DVELoopState :=
  let next := liveStep f r.2
  if next.size == r.2.size then .done ⟨some r.2, r.2⟩
  else .yield ⟨none, next⟩

def dveLoopResult (r : DVELoopState) : Std.HashSet ValId := r.1.getD r.2

theorem dveLoopFinish_eq (r : Id DVELoopState) :
    Id.run (do
      let s ← r
      match s.1 with
      | none => do
          pure PUnit.unit
          pure s.2
      | some live => pure live) = dveLoopResult (Id.run r) := by
  change (match r.1 with | none => r.2 | some live => live) = r.1.getD r.2
  cases r.1 <;> rfl

theorem liveSet_eq_loop (f : Func) :
    liveSet f = dveLoopResult
      (loopWith (dveLoopStep f) (List.range' 0 (dveFuel f) 1) ⟨none, ∅⟩) := by
  unfold liveSet
  dsimp only [dveFuel]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  rw [Id.forIn_eq_loopWith (g := dveLoopStep f) (h := by
    intro i r
    simp only [dveLoopStep]
    split <;> rfl)]
  dsimp only [Id.run, Id.instMonad, Id.hasBind]
  simp only [Std.Legacy.Range.size, dveLoopResult]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  exact dveLoopFinish_eq
    (loopWith (dveLoopStep f) (List.range' 0 (dveFuel f) 1) ⟨none, ∅⟩)

theorem instrUseFuel_eq (is : List Instr) (n : Nat) :
    is.foldl (fun m i => m + i.uses.length) n =
      n + (is.flatMap Instr.uses).length := by
  induction is generalizing n with
  | nil => simp
  | cons i is ih =>
      rw [List.foldl_cons, ih]
      simp only [List.flatMap_cons, List.length_append]
      omega

theorem blockUseFuel_eq (bs : List Block) (n : Nat) :
    bs.foldl (fun n b =>
        n + b.instrs.foldl (fun m i => m + i.uses.length) b.term.uses.length) n =
      n + (bs.flatMap fun b => b.instrs.flatMap Instr.uses ++ b.term.uses).length := by
  induction bs generalizing n with
  | nil => simp
  | cons b bs ih =>
      rw [List.foldl_cons, instrUseFuel_eq, ih]
      simp only [List.flatMap_cons, List.length_append]
      omega

theorem dveFuel_eq (f : Func) : dveFuel f = f.allDefs.length + 2 + f.allUses.length := by
  simp only [dveFuel, ← Array.foldl_toList, blockUseFuel_eq, Func.allUses]

theorem dveLoop_closed (f : Func) :
    ∀ (l : List Nat) (cur : Std.HashSet ValId),
      HashBound cur f.allUses → f.allUses.length < cur.size + l.length →
      ∃ live, (loopWith (dveLoopStep f) l ⟨none, cur⟩).1 = some live ∧
        live.Equiv (liveStep f live) := by
  intro l
  induction l with
  | nil =>
      intro cur hbound hfuel
      have := hashSize_le_of_bound hbound
      simp at hfuel
      omega
  | cons i is ih =>
      intro cur hbound hfuel
      rw [loopWith_cons]
      by_cases hsize : ((liveStep f cur).size == cur.size) = true
      · rw [show dveLoopStep f i ⟨none, cur⟩ = .done ⟨some cur, cur⟩ by
          simp [dveLoopStep, hsize]]
        refine ⟨cur, rfl, hashEquiv_of_sub_size_eq (liveStep_inflationary f cur) ?_⟩
        exact (beq_iff_eq).mp hsize |>.symm
      · have hsize' : ((liveStep f cur).size == cur.size) = false :=
          Bool.eq_false_of_not_eq_true hsize
        rw [show dveLoopStep f i ⟨none, cur⟩ = .yield ⟨none, liveStep f cur⟩ by
          simp [dveLoopStep, hsize']]
        have hle : cur.size ≤ (liveStep f cur).size := by
          have h := (List.subperm_of_subset
            ((Std.HashSet.distinct_toList (m := cur)).imp (by simp_all))
            (fun x hx => by
              rw [Std.HashSet.mem_toList] at hx ⊢
              exact liveStep_inflationary f cur x hx)).length_le
          simpa using h
        have hlt : cur.size < (liveStep f cur).size := by
          have hne : (liveStep f cur).size ≠ cur.size := by
            intro h
            exact hsize (by simp [h])
          omega
        exact ih (liveStep f cur) (liveStep_bound hbound) (by simp only [List.length_cons] at hfuel ⊢; omega)

theorem liveSet_closed (f : Func) : (liveSet f).Equiv (liveStep f (liveSet f)) := by
  rw [liveSet_eq_loop]
  obtain ⟨live, hlive, hclosed⟩ := dveLoop_closed f (List.range' 0 (dveFuel f) 1) ∅
    (by intro x hx; simp at hx) (by simp [dveFuel_eq])
  have hresult : dveLoopResult
      (loopWith (dveLoopStep f) (List.range' 0 (dveFuel f) 1) ⟨none, ∅⟩) = live := by
    simp only [dveLoopResult]
    rw [hlive]
    rfl
  rw [hresult]
  exact hclosed

theorem liveSet_mem_step_iff {f : Func} {x : ValId} :
    x ∈ liveStep f (liveSet f) ↔ x ∈ liveSet f :=
  (liveSet_closed f).mem_iff.symm

theorem mem_fold_insert_of_mem {xs : List ValId} {s : Std.HashSet ValId} {x : ValId}
    (hx : x ∈ xs) : x ∈ xs.foldl (fun s a => s.insert a) s := by
  induction xs generalizing s with
  | nil => simp at hx
  | cons a as ih =>
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hx with hx | hx
      · subst x
        exact fold_insert_sub as (s.insert a) a
          (Std.HashSet.mem_insert.mpr (Or.inl (beq_iff_eq.mpr rfl)))
      · exact ih hx

/-- If a selected fold step puts `x` in the accumulator whenever the
accumulator contains `base`, then the complete inflationary fold contains
`x`. -/
theorem mem_fold_of_selected_step {alpha : Type}
    {step : alpha → Std.HashSet ValId → Std.HashSet ValId}
    (hinfl : ∀ a s, HashSub s (step a s)) {base s : Std.HashSet ValId}
    (hbase : HashSub base s) {xs : List alpha} {a : alpha} (ha : a ∈ xs)
    {x : ValId} (hstep : ∀ s, HashSub base s → x ∈ step a s) :
    x ∈ xs.foldl (fun s a => step a s) s := by
  induction xs generalizing s with
  | nil => simp at ha
  | cons b bs ih =>
      rw [List.foldl_cons]
      rcases List.mem_cons.mp ha with rfl | ha
      · exact fold_sub hinfl bs (step a s) x (hstep s hbase)
      · exact ih (HashSub.trans hbase (hinfl b s)) ha

def dveKeepInstr (live : Std.HashSet ValId) : Instr → Bool
  | .const d _ => live.contains d
  | .op ds yop _ => !pureOp yop || ds.any live.contains
  | .call .. => true

theorem dveLiveInstrStep_mem_use {live s : Std.HashSet ValId}
    (hsub : HashSub live s) {i : Instr}
    (hkeep : dveKeepInstr live i = true) {x : ValId} (hx : x ∈ i.uses) :
    x ∈ dveLiveInstrStep i s := by
  cases i with
  | const d v => simp [Instr.uses] at hx
  | op ds yop args =>
      simp only [dveKeepInstr] at hkeep
      simp only [Instr.uses] at hx
      simp only [dveLiveInstrStep]
      have hk : (!pureOp yop || ds.any s.contains) = true := by
        simp only [Bool.or_eq_true] at hkeep ⊢
        rcases hkeep with hp | hd
        · exact Or.inl hp
        · obtain ⟨d, hd, hdlive⟩ := List.any_eq_true.mp hd
          exact Or.inr (List.any_eq_true.mpr
            ⟨d, hd, Std.HashSet.mem_iff_contains.mp (hsub d
              (Std.HashSet.contains_iff_mem.mp hdlive))⟩)
      rw [if_pos hk]
      exact mem_fold_insert_of_mem hx
  | call ds fid args =>
      exact mem_fold_insert_of_mem (by simpa [Instr.uses] using hx)

theorem wfCheck_edge_arity {f : Func} {n : Nat} (hwf : f.wfCheck n = true)
    {b : Block} (hb : b ∈ f.blocks.toList) {e : Edge} (he : e ∈ b.term.edges) :
    ∃ tb, f.blocks[e.target]? = some tb ∧ e.args.length = tb.params.length := by
  unfold Func.wfCheck at hwf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hwf
  have hb' : b ∈ f.blocks := by simpa using hb
  have hblock := Array.all_eq_true_iff_forall_mem.mp hwf.2 b hb'
  simp only [Bool.and_eq_true] at hblock
  have hedge := List.all_eq_true.mp hblock.1.2 e he
  cases hopt : f.blocks[e.target]? with
  | none => simp [hopt] at hedge
  | some tb =>
      refine ⟨tb, rfl, ?_⟩
      simpa [hopt] using hedge

/-- Under the edge-arity invariant, an argument retained by DVE is propagated
by the forward liveness step from its live target parameter. -/
theorem dveLiveEdgeStep_mem_filtered {f : Func} {e : Edge} {tb : Block}
    (htb : f.blocks[e.target]? = some tb) (hlen : e.args.length = tb.params.length)
    {s : Std.HashSet ValId} (hsub : HashSub (liveSet f) s)
    {x : ValId}
    (hx : x ∈ (e.args.zipIdx.filter fun ai =>
      match tb.params[ai.2]? with
      | some p => (liveSet f).contains p
      | none => true).map (fun ai => ai.1)) :
    x ∈ dveLiveEdgeStep f e s := by
  simp only [List.mem_map, List.mem_filter] at hx
  obtain ⟨ai, ⟨hai, hkeep⟩, haix⟩ := hx
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hai
  have hiArgs : i < e.args.length := by simpa using hi
  have hpair : ai = (e.args[i], i) := by
    rw [← hget, List.getElem_zipIdx hi]
    simp
  have hxarg : e.args[i] = x := by simpa [hpair] using haix
  have hiParams : i < tb.params.length := by omega
  have hparam : tb.params[i]? = some tb.params[i] := List.getElem?_eq_getElem hiParams
  have hpLive : tb.params[i] ∈ liveSet f := by
    rw [hpair, hparam] at hkeep
    exact Std.HashSet.contains_iff_mem.mp hkeep
  have hpai : (tb.params[i], x) ∈ tb.params.zip e.args := by
    rw [List.mem_iff_getElem]
    refine ⟨i, ?_, ?_⟩
    · simp only [List.length_zip]
      omega
    · rw [List.getElem_zip]
      simp [hxarg]
  simp only [dveLiveEdgeStep, htb]
  apply mem_fold_of_selected_step
    (fun pa s => by
      split
      · exact fun y hy => Std.HashSet.mem_insert.mpr (Or.inr hy)
      · exact HashSub.refl s)
    hsub hpai
  intro s hs
  have hpS : tb.params[i] ∈ s := hs _ hpLive
  rw [if_pos (Std.HashSet.mem_iff_contains.mp hpS)]
  exact Std.HashSet.mem_insert.mpr (Or.inl (by simp))

theorem dveLiveBlockStep_mem_term {f : Func} {n : Nat} (hwf : f.wfCheck n = true)
    {bi : BlockId} {b : Block} (hb : f.blocks[bi]? = some b)
    {s : Std.HashSet ValId} (hsub : HashSub (liveSet f) s) {x : ValId}
    (hx : x ∈ (dveBlock f bi b).term.uses) :
    x ∈ b.term.edges.foldl (fun s e => dveLiveEdgeStep f e s)
      (dveLiveTermStep b.term s) := by
  have hbmem : b ∈ f.blocks.toList := by
    obtain ⟨hlt, hget⟩ := Array.getElem?_eq_some_iff.mp hb
    exact List.mem_iff_getElem.mpr ⟨bi, by simpa using hlt, by simpa using hget⟩
  cases hterm : b.term with
  | jump e =>
      simp only [dveBlock, hterm, mapEdges, Term.uses] at hx
      obtain ⟨tb, htb, hlen⟩ := wfCheck_edge_arity hwf hbmem (e := e)
        (by simp [hterm, Term.edges])
      simp only [htb] at hx
      simpa [hterm, Term.edges, dveLiveTermStep] using
        dveLiveEdgeStep_mem_filtered htb hlen hsub hx
  | branch c et ef =>
      simp only [dveBlock, hterm, mapEdges, Term.uses, List.mem_cons, List.mem_append] at hx
      rcases hx with hxct | hxf
      · rcases hxct with hxc | hxt
        · subst x
          simpa [hterm, Term.edges, dveLiveTermStep] using
            fold_sub (dveLiveEdgeStep_inflationary f) [et, ef] (s.insert c) c
            (Std.HashSet.mem_insert.mpr (Or.inl (by simp)))
        · obtain ⟨tb, htb, hlen⟩ := wfCheck_edge_arity hwf hbmem (e := et)
            (by simp [hterm, Term.edges])
          simp only [htb] at hxt
          simp only [Term.edges, dveLiveTermStep]
          apply mem_fold_of_selected_step (dveLiveEdgeStep_inflationary f)
            (HashSub.trans hsub (dveLiveTermStep_inflationary (.branch c et ef) s))
            (xs := [et, ef]) (a := et) (by simp)
          intro s' hs'
          exact dveLiveEdgeStep_mem_filtered htb hlen hs' hxt
      · obtain ⟨tb, htb, hlen⟩ := wfCheck_edge_arity hwf hbmem (e := ef)
          (by simp [hterm, Term.edges])
        simp only [htb] at hxf
        simp only [Term.edges, dveLiveTermStep]
        apply mem_fold_of_selected_step (dveLiveEdgeStep_inflationary f)
          (HashSub.trans hsub (dveLiveTermStep_inflationary (.branch c et ef) s))
          (xs := [et, ef]) (a := ef) (by simp)
        intro s' hs'
        exact dveLiveEdgeStep_mem_filtered htb hlen hs' hxf
  | ret vs =>
      simpa [hterm, Term.edges, dveLiveTermStep] using
        mem_fold_insert_of_mem (by simpa [dveBlock, hterm, mapEdges, Term.uses] using hx)
  | halt yop as =>
      simpa [hterm, Term.edges, dveLiveTermStep] using
        mem_fold_insert_of_mem (by simpa [dveBlock, hterm, mapEdges, Term.uses] using hx)

theorem dveBlock_instr_keep {f : Func} {bi : BlockId} {b : Block} {i : Instr}
    (h : i ∈ (dveBlock f bi b).instrs) :
    dveKeepInstr (liveSet f) i = true := by
  change i ∈ b.instrs.filter (dveKeepInstr (liveSet f)) at h
  exact (List.mem_filter.mp h).2

/-- Every value read by the DVE output is in the closed forward live set.  The
well-formedness premise is used only for positional edge-argument alignment. -/
theorem dveBlock_uses_live {f : Func} {n : Nat} (hwf : f.wfCheck n = true)
    {bi : BlockId} {b : Block} (hb : f.blocks[bi]? = some b) {x : ValId}
    (hx : x ∈ ToAsm.blockUses (dveBlock f bi b)) : x ∈ liveSet f := by
  apply liveSet_mem_step_iff.mp
  rw [liveStep_eq_fold]
  have hbmem : b ∈ f.blocks.toList := by
    obtain ⟨hlt, hget⟩ := Array.getElem?_eq_some_iff.mp hb
    exact List.mem_iff_getElem.mpr ⟨bi, by simpa using hlt, by simpa using hget⟩
  apply mem_fold_of_selected_step (dveLiveBlockStep_inflationary f)
    (HashSub.refl (liveSet f)) hbmem
  intro s hsub
  rw [ToAsm.mem_blockUses] at hx
  rcases hx with hi | ht
  · simp only [List.mem_flatMap] at hi
    obtain ⟨ins, hins, huse⟩ := hi
    have hins' : ins ∈ b.instrs := List.mem_of_mem_filter hins
    have hkeep : dveKeepInstr (liveSet f) ins = true := dveBlock_instr_keep hins
    have hinner : x ∈ b.instrs.foldl (fun s i => dveLiveInstrStep i s) s := by
      apply mem_fold_of_selected_step dveLiveInstrStep_inflationary hsub hins'
      intro s' hs'
      exact dveLiveInstrStep_mem_use hs' hkeep huse
    exact fold_sub (dveLiveEdgeStep_inflationary f) b.term.edges _ x
      (dveLiveTermStep_inflationary b.term _ x hinner)
  · exact dveLiveBlockStep_mem_term hwf hb
      (HashSub.trans hsub (fold_sub dveLiveInstrStep_inflationary b.instrs s)) ht

end Passes
end YulEvmCompiler.SsaCfg
