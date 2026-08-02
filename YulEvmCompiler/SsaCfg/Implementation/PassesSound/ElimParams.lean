import YulEvmCompiler.SsaCfg.Implementation.PassesSound.Inline
set_option warningAsError true

/-!
# YulEvmCompiler.SsaCfg.Implementation.PassesSound.ElimParams

Pass 1: trivial block-parameter elimination.

The `findTrivialParam`/`elimTrivialParams` loops as folds, the block
dominance relation and the stale-zone cut that the pass needs, the
`TrivialAgree` register invariant, and `elimTrivialParam_one_sound`.
-/

namespace YulEvmCompiler.SsaCfg
open YulSemantics.EVM (U256 EvmState Op builtinWithExternal stepOp ExternalCalls
  ExternalCreates)
open YulSemantics (Outcome)

/-! ## Per-pass soundness

Each pass is stated at the *function-entry* level: an execution of `f` from its
entry block, with the register file that binds exactly `f.params`, maps to an
execution of the rewritten function from *its* entry block with the same result.
That is the granularity the whole-program statement needs (`Run` starts `main`
that way, and `Exec.call` starts a callee that way), and it is where each pass's
register invariant has its base case.

Passes 1 and 3 carry `ToAsm.Func.domCheck` — the counterexample above shows they
must. Passes 2 and 4 do not need it.

Composing the four into `optimizeProg_sound'` needs two further ingredients:

* the **preservation** lemmas below (`*_wf`, `*_dom`), because `runOnce` chains
  four passes and `optimizeFunc` iterates that three times, so each pass has to
  hand the next one its hypotheses; and
* a **simultaneous** induction over the whole program rather than a
  per-function composition, because `Exec` recurses into callees through `P`
  (`Exec.call` looks up `P.funcs[fid]?`), so the callee's derivation has to be
  transported at the same time as the caller's. The per-function lemmas below
  are the block-level content of that induction, not a decomposition of it.
-/

variable [model : ExternalModel]

namespace Passes

def inEdgeArgsEdgeStep (acc : Array (List (List ValId))) (e : Edge) :
    Array (List (List ValId)) :=
  acc.setIfInBounds e.target (e.args :: acc[e.target]!)

def inEdgeArgsBlockStep (acc : Array (List (List ValId))) (b : Block) :
    Array (List (List ValId)) :=
  b.term.edges.foldl inEdgeArgsEdgeStep acc

omit model in
theorem inEdgeArgs_eq_fold (f : Func) :
    inEdgeArgs f = f.blocks.toList.foldl inEdgeArgsBlockStep
      (Array.replicate f.blocks.size []) := by
  unfold inEdgeArgs
  dsimp only
  rw [Id.forIn_array_eq_foldl (g := fun b acc => inEdgeArgsBlockStep acc b) (h := by
    intro b acc
    rw [Id.forIn_eq_foldl (g := fun e acc => inEdgeArgsEdgeStep acc e) (h := by
      intro e acc
      rfl)]
    rfl)]
  rfl

omit model in
@[simp] theorem inEdgeArgsEdgeStep_size (acc : Array (List (List ValId))) (e : Edge) :
    (inEdgeArgsEdgeStep acc e).size = acc.size := by
  simp [inEdgeArgsEdgeStep]

omit model in
@[simp] theorem inEdgeArgsEdgeFold_size (acc : Array (List (List ValId))) (es : List Edge) :
    (es.foldl inEdgeArgsEdgeStep acc).size = acc.size := by
  induction es generalizing acc with
  | nil => rfl
  | cons e es ih => simp only [List.foldl_cons, ih, inEdgeArgsEdgeStep_size]

omit model in
@[simp] theorem inEdgeArgsBlockStep_size (acc : Array (List (List ValId))) (b : Block) :
    (inEdgeArgsBlockStep acc b).size = acc.size := by
  unfold inEdgeArgsBlockStep
  induction b.term.edges generalizing acc with
  | nil => rfl
  | cons e es ih => simp only [List.foldl_cons, ih, inEdgeArgsEdgeStep_size]

omit model in
theorem inEdgeArgsEdgeStep_mem {acc : Array (List (List ValId))} {t : BlockId}
    (ht : t < acc.size) {xs : List ValId} (hx : xs ∈ acc[t]!) (e : Edge) :
    xs ∈ (inEdgeArgsEdgeStep acc e)[t]! := by
  have hx' : xs ∈ acc[t] := by
    simpa [Array.getElem!_eq_getD, Array.getElem?_eq_getElem ht] using hx
  by_cases het : e.target = t
  · subst t
    simp [inEdgeArgsEdgeStep, ht, hx']
  · simpa [inEdgeArgsEdgeStep, het, ht] using hx'

omit model in
theorem inEdgeArgsEdgeStep_self {acc : Array (List (List ValId))} {e : Edge}
    (he : e.target < acc.size) :
    e.args ∈ (inEdgeArgsEdgeStep acc e)[e.target]! := by
  simp [inEdgeArgsEdgeStep, he]

omit model in
theorem inEdgeArgsEdgeFold_mem {acc : Array (List (List ValId))} {t : BlockId}
    (ht : t < acc.size) {xs : List ValId} (hx : xs ∈ acc[t]!) (es : List Edge) :
    xs ∈ (es.foldl inEdgeArgsEdgeStep acc)[t]! := by
  induction es generalizing acc with
  | nil => exact hx
  | cons e es ih =>
      rw [List.foldl_cons]
      exact ih (by simpa using ht) (inEdgeArgsEdgeStep_mem ht hx e)

omit model in
theorem inEdgeArgsEdgeFold_of_mem {acc : Array (List (List ValId))} {e : Edge}
    (helt : e.target < acc.size) {es : List Edge} (he : e ∈ es) :
    e.args ∈ (es.foldl inEdgeArgsEdgeStep acc)[e.target]! := by
  induction es generalizing acc with
  | nil => simp at he
  | cons e' es ih =>
      rw [List.foldl_cons]
      rcases List.mem_cons.mp he with rfl | he
      · exact inEdgeArgsEdgeFold_mem (by simpa using helt)
          (inEdgeArgsEdgeStep_self helt) es
      · exact ih (by simpa using helt) he

omit model in
theorem inEdgeArgsBlockFold_mem {acc : Array (List (List ValId))} {t : BlockId}
    (ht : t < acc.size) {xs : List ValId} (hx : xs ∈ acc[t]!) (bs : List Block) :
    xs ∈ (bs.foldl inEdgeArgsBlockStep acc)[t]! := by
  induction bs generalizing acc with
  | nil => exact hx
  | cons b bs ih =>
      rw [List.foldl_cons]
      exact ih (by simpa using ht)
        (inEdgeArgsEdgeFold_mem ht hx b.term.edges)

omit model in
theorem inEdgeArgsBlockFold_of_mem {acc : Array (List (List ValId))}
    {b : Block} {e : Edge} (helt : e.target < acc.size) {bs : List Block}
    (hb : b ∈ bs) (he : e ∈ b.term.edges) :
    e.args ∈ (bs.foldl inEdgeArgsBlockStep acc)[e.target]! := by
  induction bs generalizing acc with
  | nil => simp at hb
  | cons b' bs ih =>
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hb with rfl | hb
      · exact inEdgeArgsBlockFold_mem (by simpa using helt)
          (inEdgeArgsEdgeFold_of_mem helt he) bs
      · exact ih (by
          rw [inEdgeArgsBlockStep_size]
          exact helt) hb

omit model in
theorem inEdgeArgs_mem_of_edge {f : Func} {b : Block} (hb : b ∈ f.blocks.toList)
    {e : Edge} (he : e ∈ b.term.edges) (het : e.target < f.blocks.size) :
    e.args ∈ (inEdgeArgs f)[e.target]! := by
  rw [inEdgeArgs_eq_fold]
  exact inEdgeArgsBlockFold_of_mem (by simpa using het) hb he

abbrev TrivialCandidate := BlockId × Nat × ValId × ValId
abbrev FindTrivialState := MProd (Option (Option TrivialCandidate)) PUnit

def findTrivialParamStep (f : Func) (bi i : Nat) (_ : FindTrivialState) :
    ForInStep FindTrivialState :=
  let argLists := (inEdgeArgs f)[bi]!
  let p := f.blocks[bi]!.params[i]!
  let ith := argLists.filterMap (·[i]?)
  if ith.length == argLists.length then
    match (ith.filter (· != p)).eraseDups with
    | [v] =>
        let selfOnly := (List.range f.blocks.size).all fun j =>
          j == bi || (f.blocks[j]!.term.edges.all fun e =>
            e.target != bi || e.args[i]? != some p)
        if selfOnly then .done ⟨some (some (bi, i, p, v)), PUnit.unit⟩
        else .yield ⟨none, PUnit.unit⟩
    | _ => .yield ⟨none, PUnit.unit⟩
  else .yield ⟨none, PUnit.unit⟩

def findTrivialBlockStep (f : Func) (bi : Nat) (_ : FindTrivialState) :
    ForInStep FindTrivialState :=
  if bi != f.entry then
    let argLists := (inEdgeArgs f)[bi]!
    if !argLists.isEmpty then
      let r := loopWith (findTrivialParamStep f bi)
        (List.range' 0 f.blocks[bi]!.params.length 1) ⟨none, PUnit.unit⟩
      match r.1 with
      | none => .yield ⟨none, PUnit.unit⟩
      | some a => .done ⟨some a, PUnit.unit⟩
    else .yield ⟨none, PUnit.unit⟩
  else .yield ⟨none, PUnit.unit⟩

omit model in
theorem findTrivialParam_eq_loop (f : Func) :
    findTrivialParam f =
      (loopWith (findTrivialBlockStep f)
        (List.range' 0 f.blocks.size 1) ⟨none, PUnit.unit⟩).1.getD none := by
  unfold findTrivialParam
  dsimp only
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rw [Id.forIn_eq_loopWith (g := findTrivialBlockStep f) (h := by
    intro bi r
    unfold findTrivialBlockStep
    split
    · split
      · rw [Id.forIn_eq_loopWith (g := findTrivialParamStep f bi) (h := by
          intro i s
          simp only [LawfulMonad.pure_bind]
          rfl)]
        simp_all [bind, pure]
        split <;> simp_all
      · simp_all [bind, pure]
    · simp_all [bind, pure])]
  simp [Id.run, bind, pure, Option.getD]
  split <;> simp_all

omit model in
theorem loopWith_findTrivial_done {α : Type} {g : α → FindTrivialState →
    ForInStep FindTrivialState} {xs : List α} {c : TrivialCandidate}
    (hg : ∀ a, g a ⟨none, PUnit.unit⟩ = .yield ⟨none, PUnit.unit⟩ ∨
      ∃ c, g a ⟨none, PUnit.unit⟩ = .done ⟨some (some c), PUnit.unit⟩)
    (h : (loopWith g xs ⟨none, PUnit.unit⟩).1 = some (some c)) :
    ∃ a ∈ xs, g a ⟨none, PUnit.unit⟩ =
      .done ⟨some (some c), PUnit.unit⟩ := by
  induction xs with
  | nil => simp [loopWith] at h
  | cons a as ih =>
      rw [loopWith_cons] at h
      rcases hg a with ha | ⟨c', ha⟩
      · rw [ha] at h
        obtain ⟨b, hb, hdone⟩ := ih h
        exact ⟨b, by simp [hb], hdone⟩
      · rw [ha] at h
        have hc : c' = c := by simpa using h
        subst c'
        exact ⟨a, by simp, ha⟩

omit model in
theorem loopWith_findTrivial_cases {α : Type} {g : α → FindTrivialState →
    ForInStep FindTrivialState} {xs : List α}
    (hg : ∀ a, g a ⟨none, PUnit.unit⟩ = .yield ⟨none, PUnit.unit⟩ ∨
      ∃ c, g a ⟨none, PUnit.unit⟩ = .done ⟨some (some c), PUnit.unit⟩) :
    (loopWith g xs ⟨none, PUnit.unit⟩).1 = none ∨
      ∃ c, (loopWith g xs ⟨none, PUnit.unit⟩).1 = some (some c) := by
  induction xs with
  | nil => exact Or.inl rfl
  | cons a as ih =>
      rw [loopWith_cons]
      rcases hg a with ha | ⟨c, ha⟩
      · rw [ha]
        exact ih
      · rw [ha]
        exact Or.inr ⟨c, rfl⟩

omit model in
theorem findTrivialParamStep_cases (f : Func) (bi i : Nat) :
    findTrivialParamStep f bi i ⟨none, PUnit.unit⟩ =
        .yield ⟨none, PUnit.unit⟩ ∨
      ∃ c, findTrivialParamStep f bi i ⟨none, PUnit.unit⟩ =
        .done ⟨some (some c), PUnit.unit⟩ := by
  unfold findTrivialParamStep
  dsimp only
  split
  · split
    · split
      · right
        exact ⟨_, rfl⟩
      · left
        rfl
    · left
      rfl
  · left
    rfl

omit model in
theorem findTrivialBlockStep_cases (f : Func) (bi : Nat) :
    findTrivialBlockStep f bi ⟨none, PUnit.unit⟩ =
        .yield ⟨none, PUnit.unit⟩ ∨
      ∃ c, findTrivialBlockStep f bi ⟨none, PUnit.unit⟩ =
        .done ⟨some (some c), PUnit.unit⟩ := by
  unfold findTrivialBlockStep
  dsimp only
  split
  · split
    · rcases loopWith_findTrivial_cases
          (fun i => findTrivialParamStep_cases f bi i)
          (xs := List.range' 0 f.blocks[bi]!.params.length 1) with hr | ⟨c, hr⟩
      · left
        simp [hr]
      · right
        exact ⟨c, by simp [hr]⟩
    · left
      rfl
  · left
    rfl

omit model in
theorem findTrivialParam_inv {f : Func} {bi i p v : Nat}
    (h : findTrivialParam f = some (bi, i, p, v)) :
    bi < f.blocks.size ∧ bi ≠ f.entry ∧
    i < (f.blocks[bi]!).params.length ∧ (f.blocks[bi]!).params[i]! = p ∧
    let argLists := (inEdgeArgs f)[bi]!
    argLists ≠ [] ∧
    (argLists.filterMap (·[i]?)).length = argLists.length ∧
    ((argLists.filterMap (·[i]?)).filter (· != p)).eraseDups = [v] ∧
    (List.range f.blocks.size).all (fun j =>
      j == bi || (f.blocks[j]!.term.edges.all fun e =>
        e.target != bi || e.args[i]? != some p)) = true := by
  rw [findTrivialParam_eq_loop] at h
  have hout :
      (loopWith (findTrivialBlockStep f) (List.range' 0 f.blocks.size 1)
        ⟨none, PUnit.unit⟩).1 = some (some (bi, i, p, v)) := by
    cases hr : (loopWith (findTrivialBlockStep f) (List.range' 0 f.blocks.size 1)
        ⟨none, PUnit.unit⟩).1 with
    | none => simp [hr, Option.getD] at h
    | some r =>
        cases r with
        | none => simp [hr, Option.getD] at h
        | some c =>
            have hc : c = (bi, i, p, v) := by simpa [hr, Option.getD] using h
            simp [hc]
  obtain ⟨bi', hbi'mem, hbi'step⟩ := loopWith_findTrivial_done
    (fun j => findTrivialBlockStep_cases f j) hout
  unfold findTrivialBlockStep at hbi'step
  dsimp only at hbi'step
  split at hbi'step
  · split at hbi'step
    · split at hbi'step
      · contradiction
      · rename_i _ a hloop
        have ha : a = some (bi, i, p, v) := by simpa using hbi'step
        rw [ha] at hloop
        obtain ⟨i', hi'mem, hi'step⟩ := loopWith_findTrivial_done
          (fun j => findTrivialParamStep_cases f bi' j) hloop
        unfold findTrivialParamStep at hi'step
        dsimp only at hi'step
        split at hi'step
        · split at hi'step
          · split at hi'step
            · rename_i _ replacement hsingle hself
              have hcand :
                  (bi', i', f.blocks[bi']!.params[i']!, replacement) =
                    (bi, i, p, v) := by
                simpa using hi'step
              obtain ⟨rfl, rfl, rfl, rfl⟩ := hcand
              simp_all
            · cases hi'step
          · cases hi'step
        · cases hi'step
    · cases hbi'step
  · cases hbi'step

omit model in
theorem filterMap_length_eq_of_mem {α β : Type} {g : α → Option β} {xs : List α}
    (hlen : (xs.filterMap g).length = xs.length) {x : α} (hx : x ∈ xs) :
    ∃ y, g x = some y := by
  have hs := List.filterMap_length_eq_length.mp hlen x hx
  cases hg : g x with
  | none => simp [hg] at hs
  | some y => exact ⟨y, rfl⟩

omit model in
/-- Edge-level form of `findTrivialParam_inv`.  Every incoming edge carries
position `i`; its value is `p` or the unique non-self value `v`; and a `p`
argument can only originate in the selected block itself. -/
theorem findTrivialParam_edge {f : Func} {bi i p v : Nat}
    (hfind : findTrivialParam f = some (bi, i, p, v))
    {bj : BlockId} {b : Block} (hb : f.blocks[bj]? = some b)
    {e : Edge} (he : e ∈ b.term.edges) (het : e.target = bi) :
    ∃ a, e.args[i]? = some a ∧ (a = p ∨ a = v) ∧ (a = p → bj = bi) := by
  obtain ⟨hbi, _, _, _, hnonempty, hcoverage, hsingle, hself⟩ :=
    findTrivialParam_inv hfind
  have hbj : bj < f.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  have hbmem : b ∈ f.blocks.toList := by
    exact List.mem_iff_getElem.mpr ⟨bj, by simpa using hbj,
      by simpa using (Array.getElem?_eq_some_iff.mp hb).2⟩
  have heargs : e.args ∈ (inEdgeArgs f)[bi]! := by
    rw [← het]
    exact inEdgeArgs_mem_of_edge hbmem he (het ▸ hbi)
  obtain ⟨a, ha⟩ := filterMap_length_eq_of_mem hcoverage heargs
  refine ⟨a, ha, ?_, ?_⟩
  · by_cases hap : a = p
    · exact Or.inl hap
    · right
      have haith : a ∈ ((inEdgeArgs f)[bi]!).filterMap (·[i]?) :=
        List.mem_filterMap.mpr ⟨e.args, heargs, ha⟩
      have hafilter : a ∈ (((inEdgeArgs f)[bi]!).filterMap (·[i]?)).filter (· != p) := by
        exact List.mem_filter.mpr ⟨haith, by simp [hap]⟩
      have haerase : a ∈ ((((inEdgeArgs f)[bi]!).filterMap (·[i]?)).filter
          (· != p)).eraseDups := List.mem_eraseDups.mpr hafilter
      rw [hsingle] at haerase
      simpa using haerase
  · intro hap
    have hjall := List.all_eq_true.mp hself bj (List.mem_range.mpr hbj)
    simp only [Bool.or_eq_true, beq_iff_eq] at hjall
    rcases hjall with hj | hj
    · exact hj
    · have hbang : f.blocks[bj]! = b := by
        simp [Array.getElem!_eq_getD, hb]
      rw [hbang] at hj
      have heall := List.all_eq_true.mp hj e he
      simp only [Bool.or_eq_true, bne_iff_ne] at heall
      rcases heall with htarget | harg
      · exact absurd het htarget
      · exact absurd (ha.trans (congrArg some hap)) harg

abbrev ElimTrivialLoopState := MProd (Option Func) Func

def elimTrivialStep (_ : Nat) (r : ElimTrivialLoopState) :
    ForInStep ElimTrivialLoopState :=
  match findTrivialParam r.2 with
  | none => .done ⟨some r.2, r.2⟩
  | some (bi, i, p, v) =>
      .yield ⟨none, substFunc ((∅ : Subst).insert p v) (removeParam r.2 bi i)⟩

def elimTrivialFuel (f : Func) : Nat :=
  f.blocks.foldl (fun n b => n + b.params.length) 0 + 1

omit model in
theorem elimTrivialParams_eq_loop (f : Func) :
    elimTrivialParams f =
      let r := loopWith elimTrivialStep
        (List.range' 0 (elimTrivialFuel f) 1) ⟨none, f⟩
      r.1.getD r.2 := by
  unfold elimTrivialParams elimTrivialFuel
  dsimp only
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rw [Id.forIn_eq_loopWith (g := elimTrivialStep)
    (h := by
      intro _ r
      cases hfind : findTrivialParam r.2 with
      | none => simp [elimTrivialStep, hfind]
      | some q =>
          obtain ⟨bi, i, p, v⟩ := q
          simp [elimTrivialStep, hfind])]
  simp [Id.run, bind, pure, Option.getD]
  cases h : (loopWith elimTrivialStep
      (List.range' 0 (f.blocks.foldl (fun n b => n + b.params.length) 0 + 1))
      ⟨none, f⟩).1 <;> simp

end Passes

namespace Passes

omit model in
@[simp] theorem substV_single (p v x : ValId) :
    substV ((∅ : Subst).insert p v) x = if x = p then v else x := by
  by_cases h : x = p
  · subst x
    simp [substV, Std.HashMap.getD_eq_getD_getElem?]
  · unfold substV
    simp only [Std.HashMap.getD_eq_getD_getElem?]
    rw [Std.HashMap.getElem?_insert]
    simp [h, Ne.symm h]

omit model in
theorem removeParam_blocks_get {f : Func} {bi i j : Nat} {b : Block}
    (hb : f.blocks[j]? = some b) :
    (removeParam f bi i).blocks[j]? = some (removedBlock bi i j b) := by
  simp only [removeParam, Array.getElem?_mapIdx, hb, Option.map_some]
  simp only [beq_iff_eq, removedBlock]

omit model in
theorem elimStep_blocks_get {f : Func} {bi i p v j : Nat} {b : Block}
    (hb : f.blocks[j]? = some b) :
    (substFunc ((∅ : Subst).insert p v) (removeParam f bi i)).blocks[j]? =
      some (substBlock ((∅ : Subst).insert p v) (removedBlock bi i j b)) := by
  simp only [substFunc, Array.getElem?_map, removeParam_blocks_get hb, Option.map_some]

omit model in
theorem removedBlock_use {bi i j : Nat} {b : Block} {x : ValId}
    (hx : x ∈ ToAsm.blockUses (removedBlock bi i j b)) :
    x ∈ ToAsm.blockUses b := by
  have finish (hx : x ∈ ToAsm.blockUses
      { b with term := mapEdges (fun e =>
        if e.target = bi then { e with args := e.args.eraseIdx i } else e) b.term }) :
      x ∈ ToAsm.blockUses b := by
    rw [ToAsm.mem_blockUses] at hx ⊢
    rcases hx with hx | hx
    · exact Or.inl hx
    · refine Or.inr (mapEdges_uses_sub ?_ _ hx)
      intro e y hy
      split at hy
      · exact List.mem_of_mem_eraseIdx hy
      · exact hy
  apply finish
  rw [ToAsm.mem_blockUses] at hx ⊢
  by_cases hj : j = bi <;> simpa [removedBlock, hj] using hx

omit model in
theorem removedBlock_edge {bi i j : Nat} {b : Block} {e : Edge}
    (he : e ∈ (removedBlock bi i j b).term.edges) :
    ∃ e0 ∈ b.term.edges, e0.target = e.target := by
  have he' : e ∈ (mapEdges (fun e =>
      if e.target = bi then { e with args := e.args.eraseIdx i } else e) b.term).edges := by
    by_cases hj : j = bi <;> simpa [removedBlock, hj] using he
  obtain ⟨e0, he0, hmap⟩ := mapEdges_edges _ he'
  refine ⟨e0, he0, ?_⟩
  rw [← hmap]
  split <;> rfl

omit model in
theorem mem_removedBlock_defs {bi i j : Nat} {b : Block} {p x : ValId}
    (hp : b.params[i]? = some p) (hx : x ∈ ToAsm.blockDefs b) (hxp : x ≠ p) :
    x ∈ ToAsm.blockDefs (removedBlock bi i j b) := by
  rw [ToAsm.mem_blockDefs] at hx ⊢
  rcases hx with hx | hx
  · left
    by_cases hj : j = bi
    · simp only [removedBlock, hj, if_true]
      rw [List.mem_eraseIdx_iff_getElem?]
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hx
      refine ⟨k, ?_, hk⟩
      intro hki
      subst k
      exact hxp (Option.some.inj (hk.symm.trans hp))
    · simpa [removedBlock, hj] using hx
  · right
    by_cases hj : j = bi <;> simpa [removedBlock, hj] using hx

omit model in
theorem substBlock_use {σ : Subst} {b : Block} {x : ValId}
    (hx : x ∈ ToAsm.blockUses (substBlock σ b)) :
    ∃ y ∈ ToAsm.blockUses b, substV σ y = x := by
  rw [ToAsm.mem_blockUses] at hx
  rcases hx with hx | hx
  · simp only [substBlock, List.mem_flatMap] at hx
    obtain ⟨ins, hins, hxu⟩ := hx
    obtain ⟨ins0, hins0, rfl⟩ := List.mem_map.mp hins
    obtain ⟨y, hy, rfl⟩ := substInstr_use hxu
    exact ⟨y, ToAsm.mem_blockUses.mpr
      (Or.inl (List.mem_flatMap.mpr ⟨ins0, hins0, hy⟩)), rfl⟩
  · obtain ⟨y, hy, rfl⟩ := substTerm_use hx
    exact ⟨y, ToAsm.mem_blockUses.mpr (Or.inr hy), rfl⟩

omit model in
theorem mem_substBlock_defs {σ : Subst} {b : Block} {x : ValId}
    (hx : x ∈ ToAsm.blockDefs b) :
    x ∈ ToAsm.blockDefs (substBlock σ b) := by
  rw [ToAsm.mem_blockDefs] at hx ⊢
  rcases hx with hx | hx
  · exact Or.inl hx
  · right
    obtain ⟨ins, hins, hxd⟩ := List.mem_flatMap.mp hx
    exact List.mem_flatMap.mpr
      ⟨substInstr σ ins, List.mem_map.mpr ⟨ins, hins, rfl⟩, by simpa using hxd⟩

omit model in
theorem block_def_index_unique {f : Func} (hnd : f.allDefs.Nodup)
    {i j : Nat} {b c : Block} (hb : f.blocks[i]? = some b)
    (hc : f.blocks[j]? = some c) {x : ValId}
    (hxb : x ∈ ToAsm.blockDefs b) (hxc : x ∈ ToAsm.blockDefs c) : i = j := by
  have hi : i < f.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  have hj : j < f.blocks.size := (Array.getElem?_eq_some_iff.mp hc).1
  have hbget : f.blocks.toList[i] = b := by
    simpa using (Array.getElem?_eq_some_iff.mp hb).2
  have hcget : f.blocks.toList[j] = c := by
    simpa using (Array.getElem?_eq_some_iff.mp hc).2
  have hflat : (f.blocks.toList.flatMap blockAllDefs).Nodup :=
    (List.nodup_append.mp hnd).2.1
  have hpw := (List.nodup_flatMap.mp hflat).2
  by_contra hne
  have hxb' : x ∈ blockAllDefs b := by
    simpa [blockAllDefs, ToAsm.mem_blockDefs] using hxb
  have hxc' : x ∈ blockAllDefs c := by
    simpa [blockAllDefs, ToAsm.mem_blockDefs] using hxc
  rcases Nat.lt_or_gt_of_ne hne with hij | hji
  · have hd := (List.pairwise_iff_getElem.mp hpw i j (by simpa using hi)
      (by simpa using hj) hij)
    rw [hbget, hcget] at hd
    exact (List.disjoint_left.mp hd hxb') hxc'
  · have hd := (List.pairwise_iff_getElem.mp hpw j i (by simpa using hj)
      (by simpa using hi) hji)
    rw [hcget, hbget] at hd
    exact (List.disjoint_left.mp hd hxc') hxb'

omit model in
theorem blockAllDefs_substBlock (σ : Subst) (b : Block) :
    blockAllDefs (substBlock σ b) = blockAllDefs b := by
  simp only [blockAllDefs, substBlock]
  congr 1
  induction b.instrs with
  | nil => rfl
  | cons ins is ih => simp [ih]

omit model in
theorem blockAllDefs_removedBlock (bi i j : Nat) (b : Block) :
    List.Sublist (blockAllDefs (removedBlock bi i j b)) (blockAllDefs b) := by
  by_cases hj : j = bi
  · simp only [blockAllDefs, removedBlock, hj, if_true]
    exact (List.eraseIdx_sublist b.params i).append_right _
  · simp [blockAllDefs, removedBlock, hj]

omit model in
theorem flatMap_mapIdx_removedBlock (bi i off : Nat) : ∀ bs : List Block,
    List.Sublist
      ((bs.mapIdx fun j b => removedBlock bi i (off + j) b).flatMap blockAllDefs)
      (bs.flatMap blockAllDefs)
  | [] => List.Sublist.refl []
  | b :: bs => by
      simp only [List.mapIdx_cons, List.flatMap_cons]
      exact (blockAllDefs_removedBlock bi i off b).append
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          flatMap_mapIdx_removedBlock bi i (off + 1) bs)

omit model in
theorem removeParam_allDefs_sublist (f : Func) (bi i : Nat) :
    List.Sublist (removeParam f bi i).allDefs f.allDefs := by
  unfold Func.allDefs removeParam
  apply List.Sublist.append (.refl _)
  rw [Array.toList_mapIdx]
  simpa [removedBlock, beq_iff_eq] using
    flatMap_mapIdx_removedBlock bi i 0 f.blocks.toList

omit model in
theorem substFunc_allDefs (σ : Subst) (f : Func) :
    (substFunc σ f).allDefs = f.allDefs := by
  unfold Func.allDefs substFunc
  simp only [Array.toList_map, List.flatMap_map]
  simp_rw [blockAllDefs_substBlock]

end Passes

/-! ### Block dominance and the stale-zone cut -/

/-- `d` dominates the entry of block `i`: every entry-rooted path to `i`
has already visited `d` (with the reflexive `d = i` case explicit). -/
def BlockDom (f : Func) (d i : BlockId) : Prop :=
  ∀ path, EntryPath f path i → d = i ∨ d ∈ path

/-- Strict block dominance, as supplied by a value on every incoming edge. -/
def StrictBlockDom (f : Func) (d i : BlockId) : Prop :=
  ∀ path, EntryPath f path i → d ∈ path

omit model in
theorem BlockDom.refl (f : Func) (i : BlockId) : BlockDom f i i := by
  intro path hp
  exact Or.inl rfl

omit model in
theorem BlockDom.pred {f : Func} {d i : BlockId} (h : BlockDom f d i)
    {path : List BlockId} {j : BlockId} {b : Block} (_hp : EntryPath f path j)
    (hb : f.blocks[j]? = some b) {e : Edge} (he : e ∈ b.term.edges)
    (het : e.target = i) (hdi : d ≠ i) : BlockDom f d j := by
  intro pre hpre
  have hnext : EntryPath f (pre ++ [j]) i := by
    rw [← het]
    exact .edge hpre hb he
  rcases h (pre ++ [j]) hnext with hbad | hd
  · exact False.elim (hdi hbad)
  · rw [List.mem_append] at hd
    rcases hd with hd | hd
    · exact Or.inr hd
    · exact Or.inl (by simpa using hd)

omit model in
/-- A block in an `EntryPath` predecessor list is reached by a strictly
shorter prefix. -/
theorem EntryPath.prefix_of_mem {f : Func} {path : List BlockId} {i j : BlockId}
    (hp : EntryPath f path i) (hj : j ∈ path) :
    ∃ pre, EntryPath f pre j ∧ pre.length < path.length ∧
      ∀ x, x ∈ pre → x ∈ path := by
  induction hp with
  | entry => simp at hj
  | @edge path i b e hp hb he ih =>
      rw [List.mem_append] at hj
      rcases hj with hj | hj
      · obtain ⟨pre, hpre, hlen, hsub⟩ := ih hj
        refine ⟨pre, hpre, ?_, fun x hx => List.mem_append_left _ (hsub x hx)⟩
        simp only [List.length_append, List.length_singleton]
        omega
      · have hji : j = i := by simpa using hj
        subst j
        refine ⟨path, hp, ?_, fun x hx => List.mem_append_left _ hx⟩
        simp

omit model in
/-- Every reachable block has a path ending at its first visit. -/
theorem EntryPath.first_visit {f : Func} {path : List BlockId} {i : BlockId}
    (hp : EntryPath f path i) :
    ∃ pre, EntryPath f pre i ∧ i ∉ pre := by
  by_cases hi : i ∈ path
  · obtain ⟨pre, hpre, hlen, -⟩ := hp.prefix_of_mem hi
    exact hpre.first_visit
  · exact ⟨path, hp, hi⟩
termination_by path.length
decreasing_by exact hlen

omit model in
/-- A strict dominator cannot be dominated back by its target at a reachable
site. -/
theorem StrictBlockDom.not_reverse {f : Func} {d i : BlockId}
    (hs : StrictBlockDom f d i) {path : List BlockId}
    (hp : EntryPath f path d) : ¬ BlockDom f i d := by
  intro hr
  obtain ⟨pre, hpre, hdnot⟩ := hp.first_visit
  rcases hr pre hpre with hid | hi
  · subst i
    exact hdnot (hs pre hpre)
  · obtain ⟨prei, hprei, -, hsub⟩ := hpre.prefix_of_mem hi
    exact hdnot (hsub d (hs prei hprei))

omit model in
/-- Under `domCheck`, the unique block defining `x` dominates every block
that reads `x`. -/
theorem blockDef_dominates_use {f : Func} {li : Array (List ValId)}
    (hnd : f.allDefs.Nodup) (hli : ToAsm.liveInSets f = some li)
    (hdom : ToAsm.Func.domCheck f = true)
    {di : BlockId} {db : Block} (hdb : f.blocks[di]? = some db)
    {x : ValId} (hxdef : x ∈ ToAsm.blockDefs db)
    {i : BlockId} {b : Block} (hb : f.blocks[i]? = some b)
    (hxuse : x ∈ ToAsm.blockUses b) : BlockDom f di i := by
  intro path hp
  by_cases hieq : di = i
  · exact Or.inl hieq
  · right
    have hxnot : x ∉ ToAsm.blockDefs b := by
      intro hxb
      exact hieq (Passes.block_def_index_unique hnd hdb hb hxdef hxb)
    have hxlive := ToAsm.liveIn_of_uses hli hb hxuse hxnot
    rcases hp.live_origin hli hdom hxlive with hparam | horigin
    · have hxflat : x ∈ f.blocks.toList.flatMap blockAllDefs := by
        apply List.mem_flatMap.mpr
        refine ⟨db, block_mem_of_getElem? hdb, ?_⟩
        simpa [blockAllDefs, ToAsm.mem_blockDefs] using hxdef
      exact False.elim ((List.nodup_append.mp hnd).2.2 x hparam x hxflat rfl)
    · obtain ⟨j, hj, c, hc, hxc⟩ := horigin
      have hji := Passes.block_def_index_unique hnd hdb hc hxdef hxc
      simpa [hji] using hj

omit model in
theorem edge_arg_mem_blockUses {b : Block} {e : Edge} (he : e ∈ b.term.edges)
    {x : ValId} (hx : x ∈ e.args) : x ∈ ToAsm.blockUses b := by
  rw [ToAsm.mem_blockUses]
  right
  cases ht : b.term with
  | jump ej =>
      simp only [ht, Term.edges, List.mem_singleton] at he
      subst e
      simpa [ht, Term.uses] using hx
  | branch c et ef =>
      simp only [ht, Term.edges, List.mem_cons,
        List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · simp [Term.uses, hx]
      · simp [Term.uses, hx]
  | ret xs => simp [ht, Term.edges] at he
  | halt yop as => simp [ht, Term.edges] at he

omit model in
theorem instr_use_mem_blockUses {b : Block} {ins : Instr} (hi : ins ∈ b.instrs)
    {x : ValId} (hx : x ∈ ins.uses) : x ∈ ToAsm.blockUses b := by
  rw [ToAsm.mem_blockUses]
  exact Or.inl (List.mem_flatMap.mpr ⟨ins, hi, hx⟩)

omit model in
theorem term_use_mem_blockUses {b : Block} {x : ValId} (hx : x ∈ b.term.uses) :
    x ∈ ToAsm.blockUses b := by
  rw [ToAsm.mem_blockUses]
  exact Or.inr hx

omit model in
/-- The unique definition of a selected trivial parameter's replacement is a
strict dominator of the parameter block.  A first arrival cannot use the
allowed self value `p`; it therefore reads `v`, while later self arrivals
inherit the fact from the earlier visit. -/
theorem trivial_replacement_strict_dom {f : Func} {li : Array (List ValId)}
    (hnd : f.allDefs.Nodup) (hli : ToAsm.liveInSets f = some li)
    (hdom : ToAsm.Func.domCheck f = true)
    {bi i p v : Nat} (hfind : Passes.findTrivialParam f = some (bi, i, p, v))
    {vi : BlockId} {vb : Block} (hvb : f.blocks[vi]? = some vb)
    (hvdef : v ∈ ToAsm.blockDefs vb) : StrictBlockDom f vi bi := by
  obtain ⟨-, hbientry, -, -, -, -, -, -⟩ := Passes.findTrivialParam_inv hfind
  intro path hp
  have go : ∀ {path j}, EntryPath f path j → j = bi → vi ∈ path := by
    intro path j hp
    induction hp with
    | entry =>
        intro hentry
        exact False.elim (hbientry hentry.symm)
    | @edge path j b e hp hb he ih =>
        intro htarget
        by_cases hj : j = bi
        · have hprev := ih hj
          exact List.mem_append_left _ hprev
        · obtain ⟨a, ha, hapv, hapself⟩ :=
            Passes.findTrivialParam_edge hfind hb he htarget
          have hav : a = v := by
            rcases hapv with hap | hav
            · exact False.elim (hj (hapself hap))
            · exact hav
          have hvarg : v ∈ e.args := by
            subst a
            exact List.mem_iff_getElem?.mpr ⟨i, ha⟩
          have hvuse := edge_arg_mem_blockUses he hvarg
          rcases blockDef_dominates_use hnd hli hdom hvb hvdef hb hvuse path hp with
            hvi | hvi
          · subst j
            exact List.mem_append_right _ (by simp)
          · exact List.mem_append_left _ hvi
  exact go hp rfl

/-- Register relation for one trivial-parameter removal.  Outside `p` the
two executions are in exact lockstep.  The alias itself is required only in
the dominance region of `p`; outside that region it is the bounded stale
zone. -/
def TrivialAgree (f : Func) (bi : BlockId) (p v : ValId) (cur : BlockId)
    (R R' : Regs) : Prop :=
  (∀ x, x ≠ p → R x = R' x) ∧
  (BlockDom f bi cur → R p = R' v)

omit model in
theorem TrivialAgree.getMany {f : Func} {li : Array (List ValId)}
    (hnd : f.allDefs.Nodup) (hli : ToAsm.liveInSets f = some li)
    (hdom : ToAsm.Func.domCheck f = true)
    {bi i p v cur : Nat} (_hfind : Passes.findTrivialParam f = some (bi, i, p, v))
    {pb b : Block} (hpb : f.blocks[bi]? = some pb)
    (hpdef : p ∈ ToAsm.blockDefs pb) (hb : f.blocks[cur]? = some b)
    {R R' : Regs} (ha : TrivialAgree f bi p v cur R R')
    {xs : List ValId} (hxs : ∀ x ∈ xs, x ∈ ToAsm.blockUses b)
    {vals : List U256} (hg : R.getMany xs = some vals) :
    R'.getMany (Passes.substVs ((∅ : Passes.Subst).insert p v) xs) = some vals := by
  apply Regs.getMany_substVs (hget := hg)
  intro x hx
  rw [Passes.substV_single]
  by_cases hxp : x = p
  · subst x
    simp only [if_true]
    exact ha.2 (blockDef_dominates_use hnd hli hdom hpb hpdef hb (hxs p hx))
  · simp [hxp, ha.1 x hxp]

omit model in
theorem TrivialAgree.get {f : Func} {li : Array (List ValId)}
    (hnd : f.allDefs.Nodup) (hli : ToAsm.liveInSets f = some li)
    (hdom : ToAsm.Func.domCheck f = true)
    {bi p v cur : Nat} {pb b : Block} (hpb : f.blocks[bi]? = some pb)
    (hpdef : p ∈ ToAsm.blockDefs pb) (hb : f.blocks[cur]? = some b)
    {R R' : Regs} (ha : TrivialAgree f bi p v cur R R')
    {x : ValId} (hxuse : x ∈ ToAsm.blockUses b) {w : U256}
    (hx : R x = some w) :
    R' (Passes.substV ((∅ : Passes.Subst).insert p v) x) = some w := by
  rw [Passes.substV_single]
  by_cases hxp : x = p
  · subst x
    simp only [if_true]
    rw [← ha.2 (blockDef_dominates_use hnd hli hdom hpb hpdef hb hxuse)]
    exact hx
  · simp [hxp, ← ha.1 x hxp, hx]

omit model in
/-- Equal bindings preserve `TrivialAgree`.  If the instruction redefines
the replacement `v`, its block strictly dominates `bi`; hence it lies outside
`p`'s dominance region and the alias clause is intentionally dormant. -/
theorem TrivialAgree.setMany_instr {f : Func} {li : Array (List ValId)}
    (hnd : f.allDefs.Nodup) (hli : ToAsm.liveInSets f = some li)
    (hdom : ToAsm.Func.domCheck f = true)
    {bi k p v cur : Nat} (hfind : Passes.findTrivialParam f = some (bi, k, p, v))
    {pb b : Block} (hpb : f.blocks[bi]? = some pb) (hp : p ∈ pb.params)
    (hb : f.blocks[cur]? = some b) {path : List BlockId}
    (hpath : EntryPath f path cur)
    {ins : Instr} (hins : ins ∈ b.instrs)
    {R R' : Regs} (ha : TrivialAgree f bi p v cur R R')
    (vals : List U256) :
    TrivialAgree f bi p v cur (R.setMany ins.defs vals)
      (R'.setMany ins.defs vals) := by
  have hpnot : p ∉ ins.defs := by
    intro hpd
    exact param_not_instr_def hnd (block_mem_of_getElem? hpb)
      (block_mem_of_getElem? hb) hins hp hpd
  refine ⟨?_, ?_⟩
  · intro x hxp
    exact Regs.setMany_congr (S := fun y => y ≠ p) ha.1 ins.defs vals x hxp
  · intro hcur
    have hvnot : v ∉ ins.defs := by
      intro hvd
      have hvblock : v ∈ ToAsm.blockDefs b := by
        rw [ToAsm.mem_blockDefs]
        exact Or.inr (List.mem_flatMap.mpr ⟨ins, hins, hvd⟩)
      have hs := trivial_replacement_strict_dom hnd hli hdom hfind hb hvblock
      exact (hs.not_reverse hpath) hcur
    rw [Regs.setMany_of_not_mem R ins.defs vals hpnot,
      Regs.setMany_of_not_mem R' ins.defs vals hvnot]
    exact ha.2 hcur

omit model in
theorem Regs.getMany_eraseIdx {R : Regs} {xs : List ValId} {vals : List U256}
    (hg : R.getMany xs = some vals) (i : Nat) :
    R.getMany (xs.eraseIdx i) = some (vals.eraseIdx i) := by
  induction xs generalizing vals i with
  | nil =>
      simp only [Regs.getMany_nil, Option.some.injEq] at hg
      subst vals
      simp
  | cons x xs ih =>
      rw [Regs.getMany_cons] at hg
      cases hx : R x with
      | none => simp [hx] at hg
      | some w =>
          cases ht : R.getMany xs with
          | none => simp [hx, ht] at hg
          | some ws =>
              simp only [hx, ht, Option.bind_some, Option.map_some,
                Option.some.injEq] at hg
              subst vals
              cases i with
              | zero => exact ht
              | succ i =>
                  simp only [List.eraseIdx]
                  simpa [Regs.getMany_cons, hx] using ih ht i

omit model in
/-- Removing the same parameter/value position preserves every binding except
the removed parameter. -/
theorem Regs.setMany_eraseIdx_agree {R R' : Regs} {ps : List ValId}
    {vals : List U256} (hnd : ps.Nodup) (hlen : vals.length = ps.length)
    {i : Nat} {p : ValId} (hp : ps[i]? = some p)
    (ha : ∀ x, x ≠ p → R x = R' x) :
    ∀ x, x ≠ p →
      (R.setMany ps vals) x =
        (R'.setMany (ps.eraseIdx i) (vals.eraseIdx i)) x := by
  induction ps generalizing R R' vals i with
  | nil => simp at hp
  | cons q qs ih =>
      cases vals with
      | nil => simp at hlen
      | cons w ws =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          rw [List.nodup_cons] at hnd
          cases i with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hp
              subst q
              intro x hxp
              simp only [List.eraseIdx_zero, Regs.setMany_cons]
              apply Regs.setMany_congr (S := fun y => y ≠ p) _ qs ws x hxp
              intro y hyp
              rw [Regs.set_other _ _ hyp]
              exact ha y hyp
          | succ i =>
              simp only [List.getElem?_cons_succ] at hp
              have hqp : q ≠ p := by
                intro heq
                subst q
                exact hnd.1 (List.mem_iff_getElem?.mpr ⟨i, hp⟩)
              simp only [List.eraseIdx, Regs.setMany_cons]
              exact ih hnd.2 hlen hp
                (Regs.set_congr (S := fun y => y ≠ p) ha q w)

omit model in
theorem mem_zip_of_getElem?_eq {ps : List ValId} {xs : List ValId}
    {i : Nat} {p a : ValId} (hp : ps[i]? = some p) (ha : xs[i]? = some a) :
    (p, a) ∈ ps.zip xs := by
  induction i generalizing ps xs with
  | zero =>
      cases ps <;> cases xs <;> simp_all
  | succ i ih =>
      cases ps <;> cases xs <;> simp_all

omit model in
theorem blockParams_nodup_of_defs {f : Func} (hnd : f.allDefs.Nodup)
    {bi : BlockId} {b : Block} (hb : f.blocks[bi]? = some b) : b.params.Nodup := by
  have hbmem : b ∈ f.blocks.toList := block_mem_of_getElem? hb
  rw [List.nodup_iff_count_le_one]
  intro d
  have hall := List.nodup_iff_count_le_one.mp hnd d
  rw [allDefs_eq, List.count_append] at hall
  have hblock := count_le_count_flatMap
    (g := fun b : Block => blockAllDefs b) (d := d) hbmem
  change (b.params ++ b.instrs.flatMap Instr.defs).count d ≤
    (f.blocks.toList.flatMap blockAllDefs).count d at hblock
  rw [List.count_append] at hblock
  omega

namespace Passes

def elimEdge (bi i : Nat) (e : Edge) : Edge :=
  if e.target = bi then { e with args := e.args.eraseIdx i } else e

omit model in
@[simp] theorem elimEdge_target (bi i : Nat) (e : Edge) :
    (elimEdge bi i e).target = e.target := by
  unfold elimEdge
  split <;> rfl

def elimTerm (bi i : Nat) (t : Term) : Term := mapEdges (elimEdge bi i) t

def elimRest (bi i : Nat) (σ : Subst) (r : Rest) : Rest :=
  ⟨r.instrs.map (substInstr σ), substTerm σ (elimTerm bi i r.term)⟩

omit model in
theorem elimBlock_rest (bi i j : Nat) (σ : Subst) (b : Block) :
    Rest.mk (substBlock σ (removedBlock bi i j b)).instrs
        (substBlock σ (removedBlock bi i j b)).term =
      elimRest bi i σ ⟨b.instrs, b.term⟩ := by
  have hedge : (fun e : Edge =>
      if e.target = bi then { e with args := e.args.eraseIdx i } else e) =
      elimEdge bi i := by
    funext e
    rfl
  by_cases hj : j = bi <;>
    simp [substBlock, removedBlock, elimRest, elimTerm, hj, hedge]

end Passes

omit model in
theorem TrivialAgree.edge {f : Func} {li : Array (List ValId)}
    (hnd : f.allDefs.Nodup) (hli : ToAsm.liveInSets f = some li)
    (hdom : ToAsm.Func.domCheck f = true)
    {bi k p v cur : Nat} (hfind : Passes.findTrivialParam f = some (bi, k, p, v))
    {pb b tb : Block} (hpb : f.blocks[bi]? = some pb)
    (_hp : p ∈ pb.params) (hpdef : p ∈ ToAsm.blockDefs pb)
    (hb : f.blocks[cur]? = some b) {path : List BlockId}
    (hpath : EntryPath f path cur)
    {e : Edge} (he : e ∈ b.term.edges) (htb : f.blocks[e.target]? = some tb)
    {R R' : Regs} (ha : TrivialAgree f bi p v cur R R')
    {vals : List U256} (hg : R.getMany e.args = some vals)
    (hlen : tb.params.length = vals.length) :
    let σ := ((∅ : Passes.Subst).insert p v)
    let e' := Passes.substEdge σ (Passes.elimEdge bi k e)
    let vals' := if e.target = bi then vals.eraseIdx k else vals
    R'.getMany e'.args = some vals' ∧
    (Passes.substBlock σ (Passes.removedBlock bi k e.target tb)).params.length =
      vals'.length ∧
    TrivialAgree f bi p v e.target
      (R.setMany tb.params vals)
      (R'.setMany
        (Passes.substBlock σ (Passes.removedBlock bi k e.target tb)).params vals') := by
  dsimp only
  have hread : R'.getMany
      (Passes.substVs ((∅ : Passes.Subst).insert p v) e.args) = some vals :=
    ha.getMany hnd hli hdom hfind hpb hpdef hb
      (fun x hx => edge_arg_mem_blockUses he hx) hg
  obtain ⟨hbi, -, hk, hpget, -, -, -, -⟩ := Passes.findTrivialParam_inv hfind
  have hvp : v ≠ p := by
    intro hvp
    subst v
    obtain ⟨_, _, _, _, _, _, hsingle, _⟩ := Passes.findTrivialParam_inv hfind
    have hm : p ∈ ((((Passes.inEdgeArgs f)[bi]!).filterMap (·[k]?)).filter
        (· != p)).eraseDups := by simp [hsingle]
    have hm' := List.mem_filter.mp (List.mem_eraseDups.mp hm)
    simpa using hm'.2
  by_cases het : e.target = bi
  · rw [het] at htb ⊢
    have htbeq : tb = pb := Option.some.inj (htb.symm.trans hpb)
    subst tb
    have hpgetQ : pb.params[k]? = some p := by
      have hbidx : f.blocks[bi] = pb := (Array.getElem?_eq_some_iff.mp hpb).2
      have hbang : f.blocks[bi]! = pb :=
        (Passes.getElem!_eq_getElem hbi).trans hbidx
      have hk' : k < pb.params.length := by simpa [hbang] using hk
      have hpEq : pb.params[k] = p := by
        have hpget' := hpget
        rw [hbang] at hpget'
        simpa [List.getElem!_eq_getElem?_getD,
          List.getElem?_eq_getElem hk'] using hpget'
      rw [List.getElem?_eq_getElem hk', hpEq]
    have hndp := blockParams_nodup_of_defs hnd hpb
    have hargslen : e.args.length = vals.length := Regs.getMany_length hg
    have hpa : pb.params.length = e.args.length := by omega
    obtain ⟨a, haidx, hapv, -⟩ :=
      Passes.findTrivialParam_edge hfind hb he het
    have hpair : (p, a) ∈ pb.params.zip e.args :=
      mem_zip_of_getElem?_eq hpgetQ haidx
    have hkpb : k < pb.params.length := (List.getElem?_eq_some_iff.mp hpgetQ).1
    have hvnot : v ∉ pb.params := by
      intro hv
      have hvdef : v ∈ ToAsm.blockDefs pb :=
        ToAsm.mem_blockDefs.mpr (Or.inl hv)
      have hs := trivial_replacement_strict_dom hnd hli hdom hfind hpb hvdef
      have hnext0 : EntryPath f (path ++ [cur]) e.target := .edge hpath hb he
      have hnext : EntryPath f (path ++ [cur]) bi := by simpa [het] using hnext0
      exact (hs.not_reverse hnext) (BlockDom.refl f bi)
    have hgetErase := Regs.getMany_eraseIdx hread k
    have hgetOut : R'.getMany
        (Passes.substEdge ((∅ : Passes.Subst).insert p v)
          (Passes.elimEdge bi k e)).args = some (vals.eraseIdx k) := by
      simpa [Passes.elimEdge, Passes.substEdge, Passes.substVs,
        List.eraseIdx_map, het] using hgetErase
    simp only []
    refine ⟨hgetOut, ?_, ?_⟩
    · simp [Passes.substBlock, Passes.removedBlock, List.length_eraseIdx, hlen]
    · refine ⟨?_, ?_⟩
      · simpa [Passes.substBlock, Passes.removedBlock] using
          Regs.setMany_eraseIdx_agree hndp (by omega) hpgetQ ha.1
      · intro _
        simp [Passes.substBlock, Passes.removedBlock]
        rw [Regs.setMany_of_not_mem R' (pb.params.eraseIdx k)
          (vals.eraseIdx k) (fun hm => hvnot (List.mem_of_mem_eraseIdx hm))]
        rw [Regs.setMany_getMany_of_mem_zip hndp hpa hg hpair]
        rcases hapv with hap | hav
        · subst a
          have hpdom := blockDef_dominates_use hnd hli hdom hpb hpdef hb
              (edge_arg_mem_blockUses he
                (List.mem_iff_getElem?.mpr ⟨k, haidx⟩))
          exact ha.2 hpdom
        · subst a
          exact ha.1 v hvp
  · have hgetOut : R'.getMany
        (Passes.substEdge ((∅ : Passes.Subst).insert p v)
          (Passes.elimEdge bi k e)).args = some vals := by
      simpa [Passes.elimEdge, het, Passes.substEdge] using hread
    simp only [het, if_false]
    have hpnot : p ∉ tb.params := by
      intro hpt
      have hptdef : p ∈ ToAsm.blockDefs tb := ToAsm.mem_blockDefs.mpr (Or.inl hpt)
      exact het (Passes.block_def_index_unique (i := bi) (j := e.target)
        hnd hpb htb hpdef hptdef).symm
    refine ⟨hgetOut, by simpa [Passes.substBlock, Passes.removedBlock, het] using hlen,
      ?_⟩
    refine ⟨?_, ?_⟩
    · simpa [Passes.substBlock, Passes.removedBlock, het] using
        Regs.setMany_congr (S := fun x => x ≠ p) ha.1 tb.params vals
    · intro htarget
      have hcur := htarget.pred hpath hb he rfl (Ne.symm het)
      have hvnot : v ∉ tb.params := by
        intro hv
        have hvdef : v ∈ ToAsm.blockDefs tb := ToAsm.mem_blockDefs.mpr (Or.inl hv)
        have hs := trivial_replacement_strict_dom hnd hli hdom hfind htb hvdef
        have hnext : EntryPath f (path ++ [cur]) e.target := .edge hpath hb he
        exact (hs.not_reverse hnext) htarget
      simp only [Passes.substBlock, Passes.removedBlock, het, if_false]
      rw [Regs.setMany_of_not_mem R tb.params vals hpnot,
        Regs.setMany_of_not_mem R' tb.params vals hvnot]
      exact ha.2 hcur

/-- Lockstep replay for one selected trivial parameter. -/
theorem elimTrivialParam_one_exec {P : Prog} {f : Func} {li : Array (List ValId)}
    (hnd : f.allDefs.Nodup) (hli : ToAsm.liveInSets f = some li)
    (hdom : ToAsm.Func.domCheck f = true)
    {bi k p v : Nat} (hfind : Passes.findTrivialParam f = some (bi, k, p, v))
    {pb : Block} (hpb : f.blocks[bi]? = some pb) (hp : p ∈ pb.params)
    (hpdef : p ∈ ToAsm.blockDefs pb)
    {R : Regs} {st : EvmState} {rest : Rest} {res : FRes}
    (h : Exec (model := model) P f R st rest res) :
    ∀ {cur : BlockId} {b : Block} {path : List BlockId},
      f.blocks[cur]? = some b → EntryPath f path cur →
      (∀ ins ∈ rest.instrs, ins ∈ b.instrs) → rest.term = b.term →
      ∀ {R' : Regs}, TrivialAgree f bi p v cur R R' →
      Exec (model := model) P
        (Passes.substFunc ((∅ : Passes.Subst).insert p v)
          (Passes.removeParam f bi k)) R' st
        (Passes.elimRest bi k ((∅ : Passes.Subst).insert p v) rest) res := by
  induction h with
  | @const f R st d w is t res htail ih =>
      intro cur b path hb hpath hmem hterm R' ha
      have hi : Instr.const d w ∈ b.instrs := hmem _ (by simp)
      rw [Passes.elimRest]
      simp only [List.map_cons, Passes.substInstr]
      refine Exec.const (ih hnd hli hdom hfind hpb hb hpath
        (fun ins hins => hmem ins (List.mem_cons_of_mem _ hins)) hterm ?_)
      simpa [Instr.defs, Regs.setMany_cons, Regs.setMany_nil_left] using
        ha.setMany_instr hnd hli hdom hfind hpb hp hb hpath hi [w]
  | @op f R st st' ds yop as args rets is t res hg hop hlen htail ih =>
      intro cur b path hb hpath hmem hterm R' ha
      have hi : Instr.op ds yop as ∈ b.instrs := hmem _ (by simp)
      have hg' := ha.getMany hnd hli hdom hfind hpb hpdef hb
        (fun x hx => instr_use_mem_blockUses hi (by simpa [Instr.uses] using hx)) hg
      rw [Passes.elimRest]
      simp only [List.map_cons, Passes.substInstr]
      refine Exec.op hg' hop hlen (ih hnd hli hdom hfind hpb hb hpath
        (fun ins hins => hmem ins (List.mem_cons_of_mem _ hins)) hterm ?_)
      exact ha.setMany_instr hnd hli hdom hfind hpb hp hb hpath hi rets
  | @opHalt f R st st' ds yop as args is t hg hop =>
      intro cur b path hb hpath hmem hterm R' ha
      have hi : Instr.op ds yop as ∈ b.instrs := hmem _ (by simp)
      have hg' := ha.getMany hnd hli hdom hfind hpb hpdef hb
        (fun x hx => instr_use_mem_blockUses hi (by simpa [Instr.uses] using hx)) hg
      rw [Passes.elimRest]
      simp only [List.map_cons, Passes.substInstr]
      exact Exec.opHalt hg' hop
  | @call f g R st st' ds as fid args rvals eb is t res hfid hg hplen heb
      hbody hlen htail ihbody ih =>
      intro cur b path hb hpath hmem hterm R' ha
      have hi : Instr.call ds fid as ∈ b.instrs := hmem _ (by simp)
      have hg' := ha.getMany hnd hli hdom hfind hpb hpdef hb
        (fun x hx => instr_use_mem_blockUses hi (by simpa [Instr.uses] using hx)) hg
      rw [Passes.elimRest]
      simp only [List.map_cons, Passes.substInstr]
      refine Exec.call hfid hg' hplen heb hbody hlen
        (ih hnd hli hdom hfind hpb hb hpath
        (fun ins hins => hmem ins (List.mem_cons_of_mem _ hins)) hterm ?_)
      exact ha.setMany_instr hnd hli hdom hfind hpb hp hb hpath hi rvals
  | @callHalt f g R st st' ds as fid args eb is t hfid hg hplen heb hbody ihbody =>
      intro cur b path hb hpath hmem hterm R' ha
      have hi : Instr.call ds fid as ∈ b.instrs := hmem _ (by simp)
      have hg' := ha.getMany hnd hli hdom hfind hpb hpdef hb
        (fun x hx => instr_use_mem_blockUses hi (by simpa [Instr.uses] using hx)) hg
      rw [Passes.elimRest]
      simp only [List.map_cons, Passes.substInstr]
      exact Exec.callHalt hfid hg' hplen heb hbody
  | @jump f R st e tb vals res htb hg hlen htail ih =>
      intro cur b path hb hpath hmem hterm R' ha
      have he : e ∈ b.term.edges := by rw [← hterm]; simp [Term.edges]
      obtain ⟨hg', hlen', ha'⟩ :=
        ha.edge hnd hli hdom hfind hpb hp hpdef hb hpath he htb hg hlen
      have htb' := Passes.elimStep_blocks_get
        (f := f) (bi := bi) (i := k) (p := p) (v := v) htb
      have htb'' : (Passes.substFunc ((∅ : Passes.Subst).insert p v)
          (Passes.removeParam f bi k)).blocks[
            (Passes.substEdge ((∅ : Passes.Subst).insert p v)
              (Passes.elimEdge bi k e)).target]? =
          some (Passes.substBlock ((∅ : Passes.Subst).insert p v)
            (Passes.removedBlock bi k e.target tb)) := by
        simpa [Passes.substEdge] using htb'
      have htail' := ih hnd hli hdom hfind hpb htb
        (.edge hpath hb he) (fun ins hins => hins) rfl ha'
      have htail'' : Exec (model := model) P
          (Passes.substFunc ((∅ : Passes.Subst).insert p v)
            (Passes.removeParam f bi k))
          (R'.setMany
            (Passes.substBlock ((∅ : Passes.Subst).insert p v)
              (Passes.removedBlock bi k e.target tb)).params
            (if e.target = bi then vals.eraseIdx k else vals)) st
          ⟨(Passes.substBlock ((∅ : Passes.Subst).insert p v)
              (Passes.removedBlock bi k e.target tb)).instrs,
            (Passes.substBlock ((∅ : Passes.Subst).insert p v)
              (Passes.removedBlock bi k e.target tb)).term⟩ res := by
        rw [Passes.elimBlock_rest]
        exact htail'
      simpa [Passes.elimRest, Passes.elimTerm, Passes.elimEdge,
        Passes.substTerm, Passes.mapEdges] using
        (Exec.jump
          (e := Passes.substEdge ((∅ : Passes.Subst).insert p v)
            (Passes.elimEdge bi k e)) htb'' hg' hlen' htail'')
  | @branchTrue f R st c w et ef tb vals res hc hw htb hg hlen htail ih =>
      intro cur b path hb hpath hmem hterm R' ha
      have het : et ∈ b.term.edges := by rw [← hterm]; simp [Term.edges]
      have hcuse : c ∈ ToAsm.blockUses b := term_use_mem_blockUses (b := b) (by
        rw [← hterm]
        simp [Term.uses])
      have hc' := ha.get hnd hli hdom hpb hpdef hb hcuse hc
      obtain ⟨hg', hlen', ha'⟩ :=
        ha.edge hnd hli hdom hfind hpb hp hpdef hb hpath het htb hg hlen
      have htb' := Passes.elimStep_blocks_get
        (f := f) (bi := bi) (i := k) (p := p) (v := v) htb
      have htb'' : (Passes.substFunc ((∅ : Passes.Subst).insert p v)
          (Passes.removeParam f bi k)).blocks[
            (Passes.substEdge ((∅ : Passes.Subst).insert p v)
              (Passes.elimEdge bi k et)).target]? =
          some (Passes.substBlock ((∅ : Passes.Subst).insert p v)
            (Passes.removedBlock bi k et.target tb)) := by
        simpa [Passes.substEdge] using htb'
      have htail' := ih hnd hli hdom hfind hpb htb
        (.edge hpath hb het) (fun ins hins => hins) rfl ha'
      have htail'' : Exec (model := model) P
          (Passes.substFunc ((∅ : Passes.Subst).insert p v)
            (Passes.removeParam f bi k))
          (R'.setMany
            (Passes.substBlock ((∅ : Passes.Subst).insert p v)
              (Passes.removedBlock bi k et.target tb)).params
            (if et.target = bi then vals.eraseIdx k else vals)) st
          ⟨(Passes.substBlock ((∅ : Passes.Subst).insert p v)
              (Passes.removedBlock bi k et.target tb)).instrs,
            (Passes.substBlock ((∅ : Passes.Subst).insert p v)
              (Passes.removedBlock bi k et.target tb)).term⟩ res := by
        rw [Passes.elimBlock_rest]
        exact htail'
      simpa [Passes.elimRest, Passes.elimTerm, Passes.elimEdge,
        Passes.substTerm, Passes.mapEdges] using
        (Exec.branchTrue
          (et := Passes.substEdge ((∅ : Passes.Subst).insert p v)
            (Passes.elimEdge bi k et))
          (ef := Passes.substEdge ((∅ : Passes.Subst).insert p v)
            (Passes.elimEdge bi k ef))
          hc' hw htb'' hg' hlen' htail'')
  | @branchFalse f R st c et ef tb vals res hc htb hg hlen htail ih =>
      intro cur b path hb hpath hmem hterm R' ha
      have hef : ef ∈ b.term.edges := by rw [← hterm]; simp [Term.edges]
      have hcuse : c ∈ ToAsm.blockUses b := term_use_mem_blockUses (b := b) (by
        rw [← hterm]
        simp [Term.uses])
      have hc' := ha.get hnd hli hdom hpb hpdef hb hcuse hc
      obtain ⟨hg', hlen', ha'⟩ :=
        ha.edge hnd hli hdom hfind hpb hp hpdef hb hpath hef htb hg hlen
      have htb' := Passes.elimStep_blocks_get
        (f := f) (bi := bi) (i := k) (p := p) (v := v) htb
      have htb'' : (Passes.substFunc ((∅ : Passes.Subst).insert p v)
          (Passes.removeParam f bi k)).blocks[
            (Passes.substEdge ((∅ : Passes.Subst).insert p v)
              (Passes.elimEdge bi k ef)).target]? =
          some (Passes.substBlock ((∅ : Passes.Subst).insert p v)
            (Passes.removedBlock bi k ef.target tb)) := by
        simpa [Passes.substEdge] using htb'
      have htail' := ih hnd hli hdom hfind hpb htb
        (.edge hpath hb hef) (fun ins hins => hins) rfl ha'
      have htail'' : Exec (model := model) P
          (Passes.substFunc ((∅ : Passes.Subst).insert p v)
            (Passes.removeParam f bi k))
          (R'.setMany
            (Passes.substBlock ((∅ : Passes.Subst).insert p v)
              (Passes.removedBlock bi k ef.target tb)).params
            (if ef.target = bi then vals.eraseIdx k else vals)) st
          ⟨(Passes.substBlock ((∅ : Passes.Subst).insert p v)
              (Passes.removedBlock bi k ef.target tb)).instrs,
            (Passes.substBlock ((∅ : Passes.Subst).insert p v)
              (Passes.removedBlock bi k ef.target tb)).term⟩ res := by
        rw [Passes.elimBlock_rest]
        exact htail'
      simpa [Passes.elimRest, Passes.elimTerm, Passes.elimEdge,
        Passes.substTerm, Passes.mapEdges] using
        (Exec.branchFalse
          (et := Passes.substEdge ((∅ : Passes.Subst).insert p v)
            (Passes.elimEdge bi k et))
          (ef := Passes.substEdge ((∅ : Passes.Subst).insert p v)
            (Passes.elimEdge bi k ef))
          hc' htb'' hg' hlen' htail'')
  | @ret f R st xs vals hg =>
      intro cur b path hb hpath hmem hterm R' ha
      have hg' := ha.getMany hnd hli hdom hfind hpb hpdef hb
        (fun x hx => term_use_mem_blockUses (b := b) (by
          rw [← hterm]
          simpa [Term.uses] using hx)) hg
      simpa [Passes.elimRest, Passes.elimTerm, Passes.substTerm,
        Passes.substVs, Passes.mapEdges] using (Exec.ret hg')
  | @halt f R st st' yop as args hg hop =>
      intro cur b path hb hpath hmem hterm R' ha
      have hg' := ha.getMany hnd hli hdom hfind hpb hpdef hb
        (fun x hx => term_use_mem_blockUses (b := b) (by
          rw [← hterm]
          simpa [Term.uses] using hx)) hg
      simpa [Passes.elimRest, Passes.elimTerm, Passes.substTerm,
        Passes.substVs, Passes.mapEdges] using (Exec.halt hg' hop)

/-- **Pass 1 (trivial block-parameter elimination) soundness**, under dominance.

The invariant is a lockstep relation with a dominance-delimited stale zone for
`σ = (p ↦ v)`, carried through the derivation block by block:

* base case: `domCheck` says only `f.params` is live into the entry, and `σ`
  fixes them (`p` is a *block* parameter, so single assignment puts it outside
  `f.params`);
* at a jump into the rewritten block, the eliminated position carried either `v`
  — and then both sides bind the same word, because `v ∈ blockUses pred` so
  `ToAsm.liveIn_of_uses` puts it in the predecessor's live-in where the
  invariant applies — or `p` itself, and then the original re-binds `p` to its
  own current value while the optimized program reads `v`, which the invariant
  again equates (this is precisely the step the counterexample breaks without
  dominance: there `p` is read on a path where the binding is stale);
* every other instruction/terminator either preserves the invariant pointwise
  (`Regs.setMany_congr`) or reads only values the invariant covers
  (`Regs.getMany_congr`).

`Passes.elimTrivialParams_eq_loop` above supplies the fixed-point-loop
inversion, `Passes.findTrivialParam_inv` / `findTrivialParam_edge` supply the
complete candidate inversion including `selfOnly`, and
`Passes.elimStep_blocks_get` is the block-lookup half of the one-removal
transport.  At a jump, `_edge` gives the required split: a non-self edge
carries `v`, while a self edge may carry `p` and preserves the already-related
word. -/
theorem elimTrivialParam_one_sound {P : Prog} {f : Func} {args : List U256}
    {st : EvmState} {res : FRes} {bi k p v : Nat}
    (hnd : f.allDefs.Nodup) (hdom : ToAsm.Func.domCheck f = true)
    (hfind : Passes.findTrivialParam f = some (bi, k, p, v))
    {eb eb' : Block}
    (heb : f.blocks[f.entry]? = some eb)
    (heb' : (Passes.substFunc ((∅ : Passes.Subst).insert p v)
      (Passes.removeParam f bi k)).blocks[f.entry]? = some eb')
    (hexec : Exec (model := model) P f (Regs.empty.setMany f.params args) st
      ⟨eb.instrs, eb.term⟩ res) :
    Exec (model := model) P
      (Passes.substFunc ((∅ : Passes.Subst).insert p v)
        (Passes.removeParam f bi k))
      (Regs.empty.setMany f.params args) st ⟨eb'.instrs, eb'.term⟩ res := by
  obtain ⟨hbi, hbientry, hk, hpget, -, -, -, -⟩ :=
    Passes.findTrivialParam_inv hfind
  let pb := f.blocks[bi]
  have hpb : f.blocks[bi]? = some pb := Array.getElem?_eq_getElem hbi
  have hbang : f.blocks[bi]! = pb := Passes.getElem!_eq_getElem hbi
  have hk' : k < pb.params.length := by simpa [hbang] using hk
  have hpEq : pb.params[k] = p := by
    have hpget' := hpget
    rw [hbang] at hpget'
    simpa [List.getElem!_eq_getElem?_getD,
      List.getElem?_eq_getElem hk'] using hpget'
  have hp : p ∈ pb.params := by rw [← hpEq]; exact List.getElem_mem hk'
  have hpdef : p ∈ ToAsm.blockDefs pb := ToAsm.mem_blockDefs.mpr (Or.inl hp)
  obtain ⟨li, hli⟩ := ToAsm.liveInSets_isSome f
  have ha : TrivialAgree f bi p v f.entry
      (Regs.empty.setMany f.params args) (Regs.empty.setMany f.params args) := by
    refine ⟨fun _ _ => rfl, ?_⟩
    intro hd
    rcases hd [] EntryPath.entry with heq | hm
    · exact False.elim (hbientry heq)
    · simp at hm
  have hsim := elimTrivialParam_one_exec hnd hli hdom hfind hpb hp hpdef
    hexec heb EntryPath.entry (fun ins hins => hins) rfl ha
  have hout := Passes.elimStep_blocks_get
    (bi := bi) (i := k) (p := p) (v := v) heb
  rw [heb'] at hout
  have heq : eb' = Passes.substBlock ((∅ : Passes.Subst).insert p v)
      (Passes.removedBlock bi k f.entry eb) := by
    exact Option.some.inj hout
  subst eb'
  rw [Passes.elimBlock_rest]
  exact hsim

end YulEvmCompiler.SsaCfg
