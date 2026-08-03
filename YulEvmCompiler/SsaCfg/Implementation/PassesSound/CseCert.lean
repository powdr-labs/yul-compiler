import YulEvmCompiler.SsaCfg.Implementation.PassesSound.ConstFoldCert
set_option warningAsError true

/-!
# YulEvmCompiler.SsaCfg.Implementation.PassesSound.CseCert

Pass 3's loop as a fold, and its static certificates.

The `cseInstrStep`/`cseBlockStep` fold model, the substitution/table
soundness invariants (`CSEInv`, `CseTabDefSound`, `CseSubDefSound`,
`CseTabPosSound`), the intra-block alias order (`AliasOrdered`), and
`cseBlock_spec`.
-/

namespace YulEvmCompiler.SsaCfg
open YulSemantics.EVM (U256 EvmState Op builtinWithExternal stepOp ExternalCalls
  ExternalCreates)
open YulSemantics (Outcome)

namespace Passes

/-! ### Pass 3's loop, as a fold -/

abbrev CSEInner :=
  MProd (List Instr)
    (MProd CseTab
      (MProd (Std.HashSet ValId)
        (MProd Subst (MProd (Std.HashSet ValId) (Std.HashSet ValId)))))
abbrev CSEOuter := MProd (Array Block) (MProd (Array CseTab) Subst)

def cseBlockDefs (b : Block) : Std.HashSet ValId :=
  b.instrs.foldl (fun s i => i.defs.foldl (fun s d => s.insert d) s) ∅

def cseEntryTab (f : Func) (srcs : Array (List BlockId))
    (tables : Array CseTab) (bi : BlockId) : CseTab :=
  if bi == f.entry then {}
  else match srcs[bi]! with
    | [p] => if p < bi then
        Passes.inheritTab tables[p]! f.blocks[bi]!.params
      else {}
    | _ => {}

/-! The source collector used by `cseEntryTab`, exposed as folds. -/

def sourceEdgeStep (bi : BlockId) (acc : Array (List BlockId)) (e : Edge) :
    Array (List BlockId) :=
  acc.setIfInBounds e.target (bi :: acc[e.target]!)

def sourceBlockStep (f : Func) (acc : Array (List BlockId)) (bi : BlockId) :
    Array (List BlockId) :=
  f.blocks[bi]!.term.edges.foldl (sourceEdgeStep bi) acc

theorem inEdgeSources_eq_fold (f : Func) :
    inEdgeSources f =
      (List.range' 0 f.blocks.size 1).foldl (sourceBlockStep f)
        (Array.replicate f.blocks.size []) := by
  unfold inEdgeSources
  dsimp only [sourceBlockStep, sourceEdgeStep]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rw [Id.forIn_eq_foldl (g := fun bi acc =>
    f.blocks[bi]!.term.edges.foldl
      (fun acc e => acc.setIfInBounds e.target (bi :: acc[e.target]!)) acc) (h := by
    intro bi acc
    rw [Id.forIn_eq_foldl (g := fun e acc =>
      acc.setIfInBounds e.target (bi :: acc[e.target]!)) (h := by
      intro e acc
      rfl)]
    rfl)]
  simp [Id.run, bind, pure]
  congr 1

def cseInstrStep (ins0 : Instr) (st : CSEInner) : CSEInner :=
  let used := ins0.uses.foldl (fun s a => s.insert a) st.2.2.1
  let defined := ins0.defs.foldl (fun s d => s.insert d) st.2.2.2.2.1
  match substInstr st.2.2.2.1 ins0 with
  | .const d v =>
    match st.2.1.consts.find? (·.1 == v) with
    | some (_, d0) =>
      ⟨st.1, st.2.1, used, st.2.2.2.1.insert d d0, defined, st.2.2.2.2.2⟩
    | none =>
      ⟨.const d v :: st.1, { st.2.1 with consts := (v, d) :: st.2.1.consts },
        used, st.2.2.2.1, defined, st.2.2.2.2.2⟩
  | .op [d] yop args =>
    if pureOp yop then
      match st.2.1.ops.find? (·.1 == (yop, args)) with
      | some (_, d0) =>
        if st.2.2.1.contains d then
          ⟨.op [d] yop args :: st.1, st.2.1, used, st.2.2.2.1,
            defined, st.2.2.2.2.2⟩
        else
          ⟨st.1, st.2.1, used, st.2.2.2.1.insert d d0,
            defined, st.2.2.2.2.2⟩
      | none =>
        if args.all (fun a =>
            st.2.2.2.2.1.contains a || !st.2.2.2.2.2.contains a) then
          ⟨.op [d] yop args :: st.1,
            { st.2.1 with ops := ((yop, args), d) :: st.2.1.ops },
            used, st.2.2.2.1, defined, st.2.2.2.2.2⟩
        else
          ⟨.op [d] yop args :: st.1, st.2.1, used, st.2.2.2.1,
            defined, st.2.2.2.2.2⟩
    else
      ⟨.op [d] yop args :: st.1, st.2.1, used, st.2.2.2.1,
        defined, st.2.2.2.2.2⟩
  | ins =>
    ⟨ins :: st.1, st.2.1, used, st.2.2.2.1, defined, st.2.2.2.2.2⟩

/-- The implementation keeps `definedSoFar` first because it is declared before
the mutable instruction/table state.  The proof model keeps the historical
four projections first and appends the two new guard accumulators. -/
abbrev CSEImplInner :=
  MProd (Std.HashSet ValId)
    (MProd (List Instr) (MProd CseTab (MProd (Std.HashSet ValId) Subst)))

def cseImplToModel (blockDefs : Std.HashSet ValId) (st : CSEImplInner) : CSEInner :=
  ⟨st.2.1, st.2.2.1, st.2.2.2.1, st.2.2.2.2, st.1, blockDefs⟩

def cseModelToImpl (st : CSEInner) : CSEImplInner :=
  ⟨st.2.2.2.2.1, st.1, st.2.1, st.2.2.1, st.2.2.2.1⟩

def cseImplInstrStep (blockDefs : Std.HashSet ValId) (ins : Instr)
    (st : CSEImplInner) : CSEImplInner :=
  cseModelToImpl (cseInstrStep ins (cseImplToModel blockDefs st))

@[simp] theorem cseImplToModel_step (blockDefs : Std.HashSet ValId)
    (ins : Instr) (st : CSEImplInner) :
    cseImplToModel blockDefs (cseImplInstrStep blockDefs ins st) =
      cseInstrStep ins (cseImplToModel blockDefs st) := by
  unfold cseImplInstrStep cseImplToModel cseModelToImpl cseInstrStep
  cases hs : substInstr st.2.2.2.2 ins with
  | const d v => simp only []; split <;> rfl
  | op ds yop args =>
      cases ds with
      | nil => simp
      | cons d rest =>
          cases rest with
          | nil =>
              simp only []
              split <;> (try split <;> (try split)) <;> rfl
          | cons e es => simp
  | call ds fid args => simp

theorem cseImplFold_toModel (blockDefs : Std.HashSet ValId) (l : List Instr)
    (st : CSEImplInner) :
    cseImplToModel blockDefs
        (l.foldl (fun st ins => cseImplInstrStep blockDefs ins st) st) =
      l.foldl (fun st ins => cseInstrStep ins st) (cseImplToModel blockDefs st) := by
  induction l generalizing st with
  | nil => rfl
  | cons i is ih =>
      rw [List.foldl_cons, List.foldl_cons, ← cseImplToModel_step, ih]

theorem mem_fold_insert_iff {xs : List ValId} {s : Std.HashSet ValId}
    {x : ValId} :
    x ∈ xs.foldl (fun s a => s.insert a) s ↔ x ∈ s ∨ x ∈ xs := by
  induction xs generalizing s with
  | nil => simp
  | cons a as ih =>
      rw [List.foldl_cons, ih, Std.HashSet.mem_insert]
      simp only [List.mem_cons]
      simp only [beq_iff_eq]
      tauto

@[simp] theorem cseInstrStep_used (i : Instr) (st : CSEInner) :
    (cseInstrStep i st).2.2.1 =
      i.uses.foldl (fun s a => s.insert a) st.2.2.1 := by
  unfold cseInstrStep
  split <;> (try split <;> (try split <;> (try split))) <;> rfl

@[simp] theorem cseInstrStep_defined (i : Instr) (st : CSEInner) :
    (cseInstrStep i st).2.2.2.2.1 =
      i.defs.foldl (fun s d => s.insert d) st.2.2.2.2.1 := by
  unfold cseInstrStep
  split <;> (try split <;> (try split <;> (try split))) <;> rfl

@[simp] theorem cseInstrStep_blockDefs (i : Instr) (st : CSEInner) :
    (cseInstrStep i st).2.2.2.2.2 = st.2.2.2.2.2 := by
  unfold cseInstrStep
  split <;> (try split <;> (try split <;> (try split))) <;> rfl

theorem cseInstrFold_used (l : List Instr) (st : CSEInner) {x : ValId} :
    x ∈ (l.foldl (fun s i => cseInstrStep i s) st).2.2.1 ↔
      x ∈ st.2.2.1 ∨ x ∈ l.flatMap Instr.uses := by
  induction l generalizing st with
  | nil => simp
  | cons i is ih =>
      rw [List.foldl_cons, ih, cseInstrStep_used, mem_fold_insert_iff,
        List.flatMap_cons, List.mem_append]
      tauto

theorem cseInstrFold_defined (l : List Instr) (st : CSEInner) {x : ValId} :
    x ∈ (l.foldl (fun s i => cseInstrStep i s) st).2.2.2.2.1 ↔
      x ∈ st.2.2.2.2.1 ∨ x ∈ l.flatMap Instr.defs := by
  induction l generalizing st with
  | nil => simp
  | cons i is ih =>
      rw [List.foldl_cons, ih, cseInstrStep_defined, mem_fold_insert_iff,
        List.flatMap_cons, List.mem_append]
      tauto

theorem cseInstrFold_blockDefs (l : List Instr) (st : CSEInner) :
    (l.foldl (fun s i => cseInstrStep i s) st).2.2.2.2.2 = st.2.2.2.2.2 := by
  induction l generalizing st with
  | nil => rfl
  | cons i is ih =>
      rw [List.foldl_cons, ih, cseInstrStep_blockDefs]

theorem mem_cseBlockDefs {b : Block} {x : ValId} :
    x ∈ cseBlockDefs b ↔ x ∈ b.instrs.flatMap Instr.defs := by
  have go : ∀ (l : List Instr) (s : Std.HashSet ValId),
      x ∈ l.foldl
          (fun s i => i.defs.foldl (fun s d => s.insert d) s) s ↔
        x ∈ s ∨ x ∈ l.flatMap Instr.defs := by
    intro l
    induction l with
    | nil => simp
    | cons i is ih =>
        intro s
        rw [List.foldl_cons, ih, mem_fold_insert_iff,
          List.flatMap_cons, List.mem_append]
        tauto
  unfold cseBlockDefs
  simpa using go b.instrs ∅

def cseBlockStep (f : Func) (srcs : Array (List BlockId))
    (bi : BlockId) (st : CSEOuter) : CSEOuter :=
  let b := f.blocks[bi]!
  let tab := cseEntryTab f srcs st.2.1 bi
  let r := b.instrs.foldl (fun s i => cseInstrStep i s)
    ⟨[], tab, ∅, st.2.2, ∅, cseBlockDefs b⟩
  ⟨st.1.push { b with instrs := r.1.reverse },
    st.2.1.setIfInBounds bi r.2.1, r.2.2.2.1⟩

theorem cse_eq (f : Func) :
    cse f =
      let srcs := inEdgeSources f
      let r := (List.range' 0 f.blocks.size 1).foldl
        (fun st bi => cseBlockStep f srcs bi st)
        ⟨#[], Array.replicate f.blocks.size {}, (∅ : Subst)⟩
      substFunc r.2.2 { f with blocks := r.1 } := by
  unfold cse
  dsimp only
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rw [Id.forIn_eq_foldl (g := fun bi st => cseBlockStep f (inEdgeSources f) bi st)
    (h := by
      intro bi st
      dsimp only [cseBlockStep, cseEntryTab]
      let bdefs :=
        f.blocks[bi]!.instrs.foldl
          (fun (s : Std.HashSet ValId) i =>
            i.defs.foldl (fun s d => s.insert d) s) ∅
      rw [Id.forIn_eq_foldl
        (g := fun ins s => cseImplInstrStep bdefs ins s) (h := by
        intro i s
        dsimp only [bdefs, cseBlockDefs]
        cases hs : substInstr s.2.2.2.2 i with
        | const d v =>
          simp only [cseImplInstrStep, cseImplToModel, cseModelToImpl,
            cseInstrStep, hs]
          split <;> rename_i hfind <;> simp only [hfind] <;> rfl
        | op ds yop args =>
          cases ds with
          | nil => simp [cseImplInstrStep, cseImplToModel, cseModelToImpl,
              cseInstrStep, hs]
          | cons d rest =>
            cases rest with
            | nil =>
              simp only [cseImplInstrStep, cseImplToModel, cseModelToImpl,
                cseInstrStep, hs]
              split
              · split <;> rename_i hfind <;> simp only [hfind]
                · split <;> rfl
                · split <;> rfl
              · rfl
            | cons e es => simp [cseImplInstrStep, cseImplToModel,
                cseModelToImpl, cseInstrStep, hs]
        | call ds fid args => simp [cseImplInstrStep, cseImplToModel,
            cseModelToImpl, cseInstrStep, hs])]
      have hc := cseImplFold_toModel bdefs f.blocks[bi]!.instrs
        ⟨∅, [],
          if bi == f.entry then {}
          else match (inEdgeSources f)[bi]! with
            | [p] => if p < bi then
                Passes.inheritTab st.2.1[p]! f.blocks[bi]!.params
              else {}
            | _ => {},
          ∅, st.2.2⟩
      dsimp only [cseImplToModel] at hc
      have hbdefs : bdefs = cseBlockDefs f.blocks[bi]! := by
        simp [bdefs, cseBlockDefs]
      rw [← hbdefs]
      rw [← hc]
      rfl)]
  simp [Id.run, bind, pure]

def csePrefix (f : Func) (n : Nat) : CSEOuter :=
  (List.range' 0 n 1).foldl
    (fun st bi => cseBlockStep f (inEdgeSources f) bi st)
    ⟨#[], Array.replicate f.blocks.size {}, (∅ : Subst)⟩

@[simp] theorem csePrefix_zero (f : Func) :
    csePrefix f 0 = ⟨#[], Array.replicate f.blocks.size {}, (∅ : Subst)⟩ := rfl

theorem csePrefix_succ (f : Func) (n : Nat) :
    csePrefix f (n + 1) = cseBlockStep f (inEdgeSources f) n (csePrefix f n) := by
  simp [csePrefix, List.range'_concat, List.foldl_append]

@[simp] theorem csePrefix_blocks_size (f : Func) (n : Nat) :
    (csePrefix f n).1.size = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show n + 1 = Nat.succ n from rfl, csePrefix_succ]
    simp [cseBlockStep, ih]

theorem cseBlockStep_get_old (f : Func) (srcs : Array (List BlockId))
    (bi : BlockId) (st : CSEOuter) {i : Nat} {b : Block}
    (h : st.1[i]? = some b) : (cseBlockStep f srcs bi st).1[i]? = some b := by
  rw [cseBlockStep, Array.getElem?_push]
  have hi : i < st.1.size := (Array.getElem?_eq_some_iff.mp h).1
  have hne : i ≠ st.1.size := Nat.ne_of_lt hi
  rw [if_neg hne]
  exact h

theorem cseOuter_fold_get_old (f : Func) (srcs : Array (List BlockId))
    (l : List BlockId) (st : CSEOuter) {i : Nat} {b : Block}
    (h : st.1[i]? = some b) :
    (l.foldl (fun st bi => cseBlockStep f srcs bi st) st).1[i]? = some b := by
  induction l generalizing st with
  | nil => exact h
  | cons bi bis ih =>
    rw [List.foldl_cons]
    exact ih _ (cseBlockStep_get_old f srcs bi st h)

def cseBlockOut (f : Func) (bi : BlockId) : Block :=
  let b := f.blocks[bi]!
  let st := csePrefix f bi
  let tab := cseEntryTab f (inEdgeSources f) st.2.1 bi
  let r := b.instrs.foldl (fun s i => cseInstrStep i s)
    ⟨[], tab, ∅, st.2.2, ∅, cseBlockDefs b⟩
  { b with instrs := r.1.reverse }

def SubstExt (σ τ : Subst) : Prop :=
  ∀ {x y : ValId}, σ[x]? = some y → τ[x]? = some y

def RangeFree (σ : Subst) : Prop :=
  ∀ {x y : ValId}, σ[x]? = some y → σ[y]? = none

inductive CseExpr
  | const (v : U256)
  | op (yop : Op) (args : List ValId)

/-- A certificate that a CSE table entry came from an actual, strictly earlier
instruction in the fold.  Operation arguments record the substitution that was
in force when that instruction entered the table. -/
inductive CseDef (f : Func) : CseExpr → ValId → Prop
  | const {b : Block} {d : ValId} {v : U256} :
      b ∈ f.blocks.toList → .const d v ∈ b.instrs → CseDef f (.const v) d
  | op {b : Block} {d : ValId} {yop : Op} {args : List ValId} {σ : Subst} :
      b ∈ f.blocks.toList → .op [d] yop args ∈ b.instrs → pureOp yop = true →
      CseDef f (.op yop (substVs σ args)) d

theorem CseDef.site {f : Func} {e : CseExpr} {d : ValId} (h : CseDef f e d) :
    ∃ b ∈ f.blocks.toList, ∃ i ∈ b.instrs, d ∈ i.defs := by
  cases h with
  | const hb hi => exact ⟨_, hb, _, hi, by simp [Instr.defs]⟩
  | op hb hi hp => exact ⟨_, hb, _, hi, by simp [Instr.defs]⟩

def cseTabVals (tab : CseTab) : List ValId :=
  tab.ops.map (·.2) ++ tab.consts.map (·.2)

def CseTabDefSound (f : Func) (tab : CseTab) : Prop :=
  (∀ {yop args d}, ((yop, args), d) ∈ tab.ops → CseDef f (.op yop args) d) ∧
  (∀ {v d}, (v, d) ∈ tab.consts → CseDef f (.const v) d)

def CseSubDefSound (f : Func) (σ : Subst) : Prop :=
  ∀ {d d0}, σ[d]? = some d0 → ∃ e, CseDef f e d ∧ CseDef f e d0

/-- The fold-position certificate retained for an operation-table entry.  The
stored arguments are stable through the remainder of the source block in which
the entry was created, and the substitution `σ` they were rewritten through is
a restriction of the final substitution `tau`.  That last clause is what lets a
reader of the entry pull its arguments back to uses of the defining
instruction (see `CseEntryPos.arg_use` / `CseEntryPos.arg_origin`). -/
inductive CseEntryPos (f : Func) (tau : Subst) : CseExpr → ValId → Prop
  | op {b : Block} {pre post : List Instr} {i : Instr} {σ : Subst}
      {d : ValId} {yop : Op} {args : List ValId} :
      b ∈ f.blocks.toList → b.instrs = pre ++ i :: post →
      substInstr σ i = .op [d] yop args →
      (∀ a ∈ args, a ∉ (i :: post).flatMap Instr.defs) →
      SubstExt σ tau →
      CseEntryPos f tau (.op yop args) d

/-- The fold-position certificate retained for a dropped definition.  Constants
need no prefix guard: after their first execution every dynamic occurrence has
the advertised fixed value.  A dropped operation destination, by contrast,
must not have been read earlier in its source block. -/
inductive CseDropPos (f : Func) : CseExpr → ValId → Prop
  | const {b : Block} {pre post : List Instr} {i : Instr} {σ : Subst}
      {d : ValId} {v : U256} :
      b ∈ f.blocks.toList → b.instrs = pre ++ i :: post →
      substInstr σ i = .const d v → CseDropPos f (.const v) d
  | op {b : Block} {pre post : List Instr} {i : Instr} {σ : Subst}
      {d : ValId} {yop : Op} {args : List ValId} :
      b ∈ f.blocks.toList → b.instrs = pre ++ i :: post →
      substInstr σ i = .op [d] yop args →
      σ[d]? = none →
      d ∉ pre.flatMap Instr.uses →
      CseDropPos f (.op yop args) d

def CseTabPosSound (f : Func) (tau : Subst) (tab : CseTab) : Prop :=
  ∀ {yop args d}, ((yop, args), d) ∈ tab.ops →
    CseEntryPos f tau (.op yop args) d

/-- Every alias in the substitution has a certified drop site.  The
representative's own entry certificate is carried by `CseTabPosSound` on the
table the alias was read from, so it is not duplicated here. -/
def CseSubPosSound (f : Func) (σ : Subst) : Prop :=
  ∀ {d d0}, σ[d]? = some d0 → ∃ e, CseDropPos f e d

theorem CseTabPosSound.empty (f : Func) (tau : Subst) :
    CseTabPosSound f tau {} := by
  simp [CseTabPosSound]

theorem CseTabPosSound.inheritTab {f : Func} {tau : Subst} {tab : CseTab}
    (h : CseTabPosSound f tau tab) (ps : List ValId) :
    CseTabPosSound f tau (Passes.inheritTab tab ps) := by
  intro yop args d hm
  exact h (List.mem_filter.mp hm).1

theorem CseTabPosSound.addOp {f : Func} {tau : Subst} {tab : CseTab}
    (h : CseTabPosSound f tau tab) {yop : Op} {args : List ValId} {d : ValId}
    (hp : CseEntryPos f tau (.op yop args) d) :
    CseTabPosSound f tau { tab with ops := ((yop, args), d) :: tab.ops } := by
  intro yop0 args0 d0 hm
  rcases List.mem_cons.mp hm with hnew | hold
  · obtain ⟨hkey, rfl⟩ := Prod.mk.inj hnew
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hkey
    exact hp
  · exact h hold

theorem CseSubPosSound.insert {f : Func} {σ : Subst}
    (h : CseSubPosSound f σ) {d d0 : ValId} {e : CseExpr}
    (hp : CseDropPos f e d) :
    CseSubPosSound f (σ.insert d d0) := by
  intro x y hxy
  rw [Std.HashMap.getElem?_insert] at hxy
  split at hxy
  · rename_i heq
    have hxd : x = d := (beq_iff_eq.mp heq).symm
    subst x
    exact ⟨e, hp⟩
  · exact h hxy

def CSEInv (f : Func) (seen : List ValId) (tab : CseTab) (σ : Subst) : Prop :=
  CseTabDefSound f tab ∧ CseSubDefSound f σ ∧ RangeFree σ
    ∧ (∀ {x y : ValId}, σ[x]? = some y → x ∈ seen ∧ y ∈ seen)
    ∧ (∀ x ∈ cseTabVals tab, x ∈ seen ∧ σ[x]? = none)

theorem cseInv_empty (f : Func) : CSEInv f [] {} (∅ : Subst) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · intro d d0 h
    simp at h
  · intro x y h
    simp at h
  · intro x y h
    simp at h
  · simp [cseTabVals]

theorem CSEInv.weaken {f : Func} {seen seen' : List ValId} {tab : CseTab} {σ : Subst}
    (h : CSEInv f seen tab σ) (hsub : ∀ x ∈ seen, x ∈ seen') :
    CSEInv f seen' tab σ := by
  refine ⟨h.1, h.2.1, h.2.2.1, ?_, ?_⟩
  · intro x y hxy
    exact ⟨hsub x (h.2.2.2.1 hxy).1, hsub y (h.2.2.2.1 hxy).2⟩
  · intro x hx
    exact ⟨hsub x (h.2.2.2.2 x hx).1, (h.2.2.2.2 x hx).2⟩

theorem CSEInv.insert {f : Func} {seen : List ValId} {tab : CseTab} {σ : Subst}
    {d d0 : ValId} {e : CseExpr} (h : CSEInv f seen tab σ)
    (hd : d ∉ seen) (hd0 : d0 ∈ seen)
    (hd0none : σ[d0]? = none)
    (hc : CseDef f e d) (hc0 : CseDef f e d0) :
    CSEInv f (seen ++ [d]) tab (σ.insert d d0) := by
  have hdne : d ≠ d0 := fun heq => hd (heq ▸ hd0)
  have hdnone : σ[d]? = none := by
    by_contra hn
    obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp hn
    exact hd (h.2.2.2.1 hy).1
  refine ⟨h.1, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    rw [Std.HashMap.getElem?_insert] at hxy
    split at hxy
    · rename_i heq
      have hxd : x = d := (beq_iff_eq.mp heq).symm
      subst x
      obtain rfl := Option.some.inj hxy
      exact ⟨e, hc, hc0⟩
    · exact h.2.1 hxy
  · intro x y hxy
    rw [Std.HashMap.getElem?_insert] at hxy
    split at hxy
    · rename_i heq
      have hxd : x = d := (beq_iff_eq.mp heq).symm
      subst x
      obtain rfl := Option.some.inj hxy
      simp [Std.HashMap.getElem?_insert, hdne, hd0none]
    · rename_i hne
      have holdnone : σ[y]? = none := h.2.2.1 hxy
      have hyd : (d == y) = false := by
        apply Bool.eq_false_of_not_eq_true
        intro heq
        have hdy : d = y := beq_iff_eq.mp heq
        exact hd (hdy ▸ (h.2.2.2.1 hxy).2)
      simp [Std.HashMap.getElem?_insert, hyd, holdnone]
  · intro x y hxy
    rw [Std.HashMap.getElem?_insert] at hxy
    split at hxy
    · rename_i heq
      have hxd : x = d := (beq_iff_eq.mp heq).symm
      subst x
      obtain rfl := Option.some.inj hxy
      exact ⟨by simp, by simp [hd0]⟩
    · have hseen := h.2.2.2.1 hxy
      exact ⟨by simp [hseen.1], by simp [hseen.2]⟩
  · intro x hx
    have htab := h.2.2.2.2 x hx
    refine ⟨by simp [htab.1], ?_⟩
    have hdx : (d == x) = false := by
      apply Bool.eq_false_of_not_eq_true
      intro heq
      exact hd (beq_iff_eq.mp heq ▸ htab.1)
    simp [Std.HashMap.getElem?_insert, hdx, htab.2]

theorem CSEInv.insert_ext {f : Func} {seen : List ValId} {tab : CseTab} {σ : Subst}
    {d : ValId} (d0 : ValId) (h : CSEInv f seen tab σ) (hd : d ∉ seen) :
    SubstExt σ (σ.insert d d0) := by
  intro x y hxy
  have hxd : (d == x) = false := by
    apply Bool.eq_false_of_not_eq_true
    intro heq
    exact hd (beq_iff_eq.mp heq ▸ (h.2.2.2.1 hxy).1)
  simp [Std.HashMap.getElem?_insert, hxd, hxy]

theorem CSEInv.addConst {f : Func} {seen : List ValId} {tab : CseTab} {σ : Subst}
    {d : ValId} {v : U256} (h : CSEInv f seen tab σ) (hd : d ∉ seen)
    (hc : CseDef f (.const v) d) :
    CSEInv f (seen ++ [d]) { tab with consts := (v, d) :: tab.consts } σ := by
  have hdnone : σ[d]? = none := by
    by_contra hn
    obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp hn
    exact hd (h.2.2.2.1 hy).1
  refine ⟨?_, h.2.1, h.2.2.1, ?_, ?_⟩
  · refine ⟨h.1.1, ?_⟩
    intro w x hx
    rcases List.mem_cons.mp hx with hhead | htail
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hhead
      exact hc
    · exact h.1.2 htail
  · intro x y hxy
    have hs := h.2.2.2.1 hxy
    exact ⟨by simp [hs.1], by simp [hs.2]⟩
  · intro x hx
    simp only [cseTabVals, List.map_cons, List.mem_append, List.mem_cons] at hx
    rcases hx with hx | rfl | hx
    · have ho : x ∈ cseTabVals tab := by
        simp only [cseTabVals, List.mem_append]
        exact Or.inl hx
      have hs := h.2.2.2.2 x ho
      exact ⟨by simp [hs.1], hs.2⟩
    · exact ⟨by simp, hdnone⟩
    · have ho : x ∈ cseTabVals tab := by
        simp only [cseTabVals, List.mem_append]
        exact Or.inr hx
      have hs := h.2.2.2.2 x ho
      exact ⟨by simp [hs.1], hs.2⟩

theorem CSEInv.addOp {f : Func} {seen : List ValId} {tab : CseTab} {σ : Subst}
    {d : ValId} {yop : Op} {args : List ValId} (h : CSEInv f seen tab σ)
    (hd : d ∉ seen) (hc : CseDef f (.op yop args) d) :
    CSEInv f (seen ++ [d]) { tab with ops := ((yop, args), d) :: tab.ops } σ := by
  have hdnone : σ[d]? = none := by
    by_contra hn
    obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp hn
    exact hd (h.2.2.2.1 hy).1
  refine ⟨?_, h.2.1, h.2.2.1, ?_, ?_⟩
  · refine ⟨?_, h.1.2⟩
    intro op as x hx
    rcases List.mem_cons.mp hx with hhead | htail
    · obtain ⟨hopargs, rfl⟩ := Prod.mk.inj hhead
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hopargs
      exact hc
    · exact h.1.1 htail
  · intro x y hxy
    have hs := h.2.2.2.1 hxy
    exact ⟨by simp [hs.1], by simp [hs.2]⟩
  · intro x hx
    simp only [cseTabVals, List.map_cons, List.mem_append, List.mem_cons] at hx
    rcases hx with (rfl | hx) | hx
    · exact ⟨by simp, hdnone⟩
    · have ho : x ∈ cseTabVals tab := by
        simp only [cseTabVals, List.mem_append]
        exact Or.inl hx
      have hs := h.2.2.2.2 x ho
      exact ⟨by simp [hs.1], hs.2⟩
    · have ho : x ∈ cseTabVals tab := by
        simp only [cseTabVals, List.mem_append]
        exact Or.inr hx
      have hs := h.2.2.2.2 x ho
      exact ⟨by simp [hs.1], hs.2⟩

theorem cseInstrStep_inv {f : Func} {b : Block} (hb : b ∈ f.blocks.toList)
    {seen : List ValId} {tab : CseTab} {used : Std.HashSet ValId} {σ : Subst}
    {defined blockDefs : Std.HashSet ValId}
    (hinv : CSEInv f seen tab σ)
    (i : Instr) (hi : i ∈ b.instrs) (hnd : (seen ++ i.defs).Nodup) :
    let r := cseInstrStep i ⟨[], tab, used, σ, defined, blockDefs⟩
    CSEInv f (seen ++ i.defs) r.2.1 r.2.2.2.1 ∧ SubstExt σ r.2.2.2.1 := by
  have ext_refl : SubstExt σ σ := fun h => h
  cases i with
  | const d v =>
    have hd : d ∉ seen := by
      rw [List.nodup_append] at hnd
      exact fun hm => (hnd.2.2 d hm d (by simp [Instr.defs])) rfl
    have hc : CseDef f (.const v) d := .const hb hi
    simp only [cseInstrStep, substInstr]
    split
    · rename_i w d0 hfind
      have hpw : (w == v) = true := List.find?_some
        (p := fun x : U256 × ValId => x.1 == v) (a := (w, d0)) hfind
      have hw : w = v := beq_iff_eq.mp hpw
      subst w
      have hm : (v, d0) ∈ tab.consts := List.mem_of_find?_eq_some hfind
      have hc0 : CseDef f (.const v) d0 := hinv.1.2 hm
      have htv : d0 ∈ cseTabVals tab := by
        unfold cseTabVals
        exact List.mem_append_right _ (List.mem_map.mpr ⟨(v, d0), hm, rfl⟩)
      have hd0 := hinv.2.2.2.2 d0 htv
      exact ⟨hinv.insert hd hd0.1 hd0.2 hc hc0,
        CSEInv.insert_ext d0 hinv hd⟩
    · exact ⟨hinv.addConst hd hc, ext_refl⟩
  | op ds yop args =>
    cases ds with
    | nil =>
      simp only [cseInstrStep, substInstr]
      exact ⟨hinv.weaken (fun x hx => List.mem_append_left _ hx), ext_refl⟩
    | cons d rest =>
      cases rest with
      | cons e es =>
        simp only [cseInstrStep, substInstr]
        exact ⟨hinv.weaken (fun x hx => List.mem_append_left _ hx), ext_refl⟩
      | nil =>
        have hd : d ∉ seen := by
          rw [List.nodup_append] at hnd
          exact fun hm => (hnd.2.2 d hm d (by simp [Instr.defs])) rfl
        simp only [cseInstrStep, substInstr]
        by_cases hp : pureOp yop = true
        · rw [if_pos hp]
          have hc : CseDef f (.op yop (substVs σ args)) d := .op hb hi hp
          split
          · rename_i key d0 hfind
            obtain ⟨yop0, args0⟩ := key
            have hpkey : ((yop0, args0) == (yop, substVs σ args)) = true :=
              List.find?_some
                (p := fun x : (Op × List ValId) × ValId =>
                  x.1 == (yop, substVs σ args))
                (a := ((yop0, args0), d0)) hfind
            have hkey : (yop0, args0) = (yop, substVs σ args) :=
              beq_iff_eq.mp hpkey
            have hm : ((yop0, args0), d0) ∈ tab.ops :=
              List.mem_of_find?_eq_some hfind
            have hc0 : CseDef f (.op yop0 args0) d0 := hinv.1.1 hm
            have hc' : CseDef f (.op yop0 args0) d := by
              have hyop : yop0 = yop := congrArg Prod.fst hkey
              have hargs : args0 = substVs σ args := congrArg Prod.snd hkey
              subst yop0
              subst args0
              exact hc
            have htv : d0 ∈ cseTabVals tab := by
              unfold cseTabVals
              exact List.mem_append_left _ (List.mem_map.mpr ⟨((yop0, args0), d0), hm, rfl⟩)
            have hd0 := hinv.2.2.2.2 d0 htv
            by_cases hu : used.contains d = true
            · rw [if_pos hu]
              exact ⟨hinv.weaken (fun x hx => List.mem_append_left _ hx), ext_refl⟩
            · rw [if_neg hu]
              exact ⟨hinv.insert hd hd0.1 hd0.2 hc' hc0,
                CSEInv.insert_ext d0 hinv hd⟩
          · split
            · exact ⟨hinv.addOp hd hc, ext_refl⟩
            · exact ⟨hinv.weaken (fun x hx => List.mem_append_left _ hx), ext_refl⟩
        · rw [if_neg hp]
          exact ⟨hinv.weaken (fun x hx => List.mem_append_left _ hx), ext_refl⟩
  | call ds fid args =>
    simp only [cseInstrStep, substInstr]
    exact ⟨hinv.weaken (by
      intro x hx
      exact List.mem_append_left _ hx), ext_refl⟩

theorem cseInstrStep_state (i : Instr) (acc : List Instr) (tab : CseTab)
    (used : Std.HashSet ValId) (σ : Subst)
    (defined blockDefs : Std.HashSet ValId) :
    (cseInstrStep i ⟨acc, tab, used, σ, defined, blockDefs⟩).2 =
      (cseInstrStep i ⟨[], tab, used, σ, defined, blockDefs⟩).2 := by
  cases i with
  | const d v => simp only [cseInstrStep, substInstr]; split <;> rfl
  | op ds yop args =>
    cases ds with
    | nil => rfl
    | cons d rest =>
      cases rest with
      | cons e es => rfl
      | nil =>
        simp only [cseInstrStep, substInstr]
        split <;> (try split <;> (try split)) <;> rfl
  | call ds fid args => rfl

theorem SubstExt.trans {σ τ υ : Subst} (h1 : SubstExt σ τ) (h2 : SubstExt τ υ) :
    SubstExt σ υ := fun h => h2 (h1 h)

def SubstStable (seen : List ValId) (σ τ : Subst) : Prop :=
  ∀ x ∈ seen, τ[x]? = σ[x]?

theorem SubstStable.trans {seen : List ValId} {σ τ υ : Subst}
    (h1 : SubstStable seen σ τ) (h2 : SubstStable seen τ υ) :
    SubstStable seen σ υ := by
  intro x hx
  rw [h2 x hx, h1 x hx]

theorem cseInstrStep_stable {seen : List ValId} {tab : CseTab}
    {used : Std.HashSet ValId} {σ : Subst} {defined blockDefs : Std.HashSet ValId}
    (i : Instr) (hnd : (seen ++ i.defs).Nodup) :
    SubstStable seen σ
      (cseInstrStep i ⟨[], tab, used, σ, defined, blockDefs⟩).2.2.2.1 := by
  have fresh {d : ValId} (hd : d ∈ i.defs) : d ∉ seen := by
    rw [List.nodup_append] at hnd
    exact fun hm => (hnd.2.2 d hm d hd) rfl
  intro x hx
  cases i with
  | const d v =>
    simp only [cseInstrStep, substInstr]
    split
    · have hne : d ≠ x := by
        intro hdx
        subst x
        exact fresh (by simp [Instr.defs]) hx
      have hdx : (d == x) = false := by simp [hne]
      simp [Std.HashMap.getElem?_insert, hdx]
    · rfl
  | op ds yop args =>
    cases ds with
    | nil => rfl
    | cons d rest =>
      cases rest with
      | cons e es => rfl
      | nil =>
        simp only [cseInstrStep, substInstr]
        split
        · split
          · split
            · rfl
            · have hne : d ≠ x := by
                intro hdx
                subst x
                exact fresh (by simp [Instr.defs]) hx
              have hdx : (d == x) = false := by simp [hne]
              simp [Std.HashMap.getElem?_insert, hdx]
          · split <;> rfl
        · rfl
  | call ds fid args => rfl

theorem cseInstrFold_inv {f : Func} {b : Block} (hb : b ∈ f.blocks.toList)
    {seen : List ValId} {tab : CseTab} {σ : Subst} (hinv : CSEInv f seen tab σ)
    (l : List Instr) (hmem : ∀ i ∈ l, i ∈ b.instrs)
    (hnd : (seen ++ l.flatMap Instr.defs).Nodup) (acc : List Instr)
    (used defined blockDefs : Std.HashSet ValId) :
    let r := l.foldl (fun s i => cseInstrStep i s)
      ⟨acc, tab, used, σ, defined, blockDefs⟩
    CSEInv f (seen ++ l.flatMap Instr.defs) r.2.1 r.2.2.2.1 ∧
      SubstExt σ r.2.2.2.1 := by
  induction l generalizing seen tab σ acc used defined blockDefs with
  | nil => simpa using And.intro hinv (show SubstExt σ σ from fun h => h)
  | cons i is ih =>
    simp only [List.flatMap_cons] at hnd ⊢
    have hprefix : (seen ++ i.defs).Nodup := by
      apply List.Nodup.of_append_left (l₂ := is.flatMap Instr.defs)
      simpa [List.append_assoc] using hnd
    have hone := cseInstrStep_inv hb (used := used) (defined := defined)
      (blockDefs := blockDefs) hinv i
      (hmem i (by simp)) hprefix
    have hstate := cseInstrStep_state i acc tab used σ defined blockDefs
    let s1 := cseInstrStep i ⟨acc, tab, used, σ, defined, blockDefs⟩
    have hinv1 : CSEInv f (seen ++ i.defs) s1.2.1 s1.2.2.2.1 := by
      rw [hstate]
      exact hone.1
    have hext1 : SubstExt σ s1.2.2.2.1 := by
      rw [hstate]
      exact hone.2
    have htail : ((seen ++ i.defs) ++ is.flatMap Instr.defs).Nodup := by
      simpa [List.append_assoc] using hnd
    have hrest := ih hinv1 (fun j hj => hmem j (by simp [hj])) htail
      s1.1 s1.2.2.1 s1.2.2.2.2.1 s1.2.2.2.2.2
    rw [List.foldl_cons]
    refine ⟨?_, hext1.trans hrest.2⟩
    simpa [List.append_assoc] using hrest.1

/-- The positional half of the instruction-fold certificate.  Unlike
`cseInstrFold_inv`, this induction retains the exact processed prefix.  That is
what turns the two executable guards into durable proof fields. -/
theorem cseInstrFold_pos {f : Func} {b : Block} (hb : b ∈ f.blocks.toList)
    (pre l : List Instr) (hseq : b.instrs = pre ++ l)
    (hdefsNodup : b.instrs.flatMap Instr.defs |>.Nodup)
    {seen : List ValId}
    (hseenNodup : (seen ++ l.flatMap Instr.defs).Nodup)
    (acc : List Instr) (tab : CseTab) (used : Std.HashSet ValId) (σ : Subst)
    (defined blockDefs : Std.HashSet ValId)
    (hused : ∀ x, x ∈ used ↔ x ∈ pre.flatMap Instr.uses)
    (hdefined : ∀ x, x ∈ defined ↔ x ∈ pre.flatMap Instr.defs)
    (hblockDefs : ∀ x, x ∈ blockDefs ↔ x ∈ b.instrs.flatMap Instr.defs)
    {tau : Subst} (hinv : CSEInv f seen tab σ)
    (htab : CseTabPosSound f tau tab) (hsub : CseSubPosSound f σ) :
    let r := l.foldl (fun s i => cseInstrStep i s)
      ⟨acc, tab, used, σ, defined, blockDefs⟩
    SubstExt r.2.2.2.1 tau →
      CseTabPosSound f tau r.2.1 ∧ CseSubPosSound f r.2.2.2.1 := by
  dsimp only
  induction l generalizing pre seen acc tab used σ defined blockDefs with
  | nil => intro _; exact ⟨htab, hsub⟩
  | cons i is ih =>
    let s1 := cseInstrStep i ⟨acc, tab, used, σ, defined, blockDefs⟩
    have hprefix : (seen ++ i.defs).Nodup := by
      apply List.Nodup.of_append_left (l₂ := is.flatMap Instr.defs)
      simpa [List.append_assoc] using hseenNodup
    have hstepInv := cseInstrStep_inv hb (used := used) (defined := defined)
      (blockDefs := blockDefs) hinv i
      (by rw [hseq]; simp) hprefix
    have hstate := cseInstrStep_state i acc tab used σ defined blockDefs
    have hinv1 : CSEInv f (seen ++ i.defs) s1.2.1 s1.2.2.2.1 := by
      rw [hstate]
      exact hstepInv.1
    have hseq1 : b.instrs = (pre ++ [i]) ++ is := by
      simpa [List.append_assoc] using hseq
    have hseenNodup1 : ((seen ++ i.defs) ++ is.flatMap Instr.defs).Nodup := by
      simpa [List.append_assoc] using hseenNodup
    rw [List.foldl_cons]
    intro hout
    have htailInv := cseInstrFold_inv hb hinv1 is
      (fun j hj => by rw [hseq1]; simp [hj])
      hseenNodup1 s1.1 s1.2.2.1 s1.2.2.2.2.1 s1.2.2.2.2.2
    have hext1 : SubstExt σ s1.2.2.2.1 := by
      intro x y hxy
      have h := hstepInv.2 hxy
      rw [hstate]
      exact h
    have hextTau : SubstExt σ tau := fun hxy => hout (htailInv.2 (hext1 hxy))
    have hpos1 : CseTabPosSound f tau s1.2.1 ∧
        CseSubPosSound f s1.2.2.2.1 := by
      cases hs : substInstr σ i with
      | const d v =>
          simp only [s1, cseInstrStep, hs]
          split
          · exact ⟨htab, hsub.insert (.const hb hseq hs)⟩
          · exact ⟨htab, hsub⟩
      | op ds yop args =>
          cases ds with
          | nil =>
              simp only [s1, cseInstrStep, hs]
              exact ⟨htab, hsub⟩
          | cons d rest =>
              cases rest with
              | cons e es =>
                  simp only [s1, cseInstrStep, hs]
                  exact ⟨htab, hsub⟩
              | nil =>
                  simp only [s1, cseInstrStep, hs]
                  by_cases hp : pureOp yop = true
                  · rw [if_pos hp]
                    cases hfind : tab.ops.find? (fun x => x.1 == (yop, args)) with
                    | some entry =>
                        obtain ⟨key, d0⟩ := entry
                        by_cases hu : used.contains d = true
                        · simp only [hu]
                          exact ⟨htab, hsub⟩
                        · have hdpre : d ∉ pre.flatMap Instr.uses := by
                            intro hd
                            have hm : d ∈ used := (hused d).mpr hd
                            exact hu (Std.HashSet.mem_iff_contains.mp hm)
                          have hdnone : σ[d]? = none := by
                            by_contra hn
                            obtain ⟨d1, hd1⟩ := Option.ne_none_iff_exists'.mp hn
                            have hdseen := (hinv.2.2.2.1 hd1).1
                            have hddef : d ∈ i.defs := by
                              have hm : d ∈ (substInstr σ i).defs := by
                                rw [hs]
                                simp [Instr.defs]
                              cases i <;> simpa [substInstr, Instr.defs] using hm
                            have hdfresh : d ∉ seen := by
                              rw [List.nodup_append] at hprefix
                              exact fun hd => hprefix.2.2 d hd d
                                hddef rfl
                            exact hdfresh hdseen
                          have hdrop : CseDropPos f (.op yop args) d :=
                            .op hb hseq hs hdnone hdpre
                          simp only [hu]
                          exact ⟨htab, hsub.insert hdrop (d0 := d0)⟩
                    | none =>
                        by_cases hg : args.all (fun a =>
                            defined.contains a || !blockDefs.contains a) = true
                        · have hargs : ∀ a ∈ args,
                              a ∉ (i :: is).flatMap Instr.defs := by
                            intro a ha hais
                            have hga := List.all_eq_true.mp hg a ha
                            rw [Bool.or_eq_true] at hga
                            have hablock : a ∈ blockDefs := by
                              apply (hblockDefs a).mpr
                              rw [hseq]
                              simp only [List.flatMap_append, List.flatMap_cons,
                                List.mem_append]
                              exact Or.inr (by simpa [List.flatMap_cons] using hais)
                            rcases hga with hbefore | houtside
                            · have hapre : a ∈ pre.flatMap Instr.defs :=
                                (hdefined a).mp
                                  (Std.HashSet.contains_iff_mem.mp hbefore)
                              have hnd := hdefsNodup
                              rw [hseq, List.flatMap_append,
                                List.nodup_append] at hnd
                              exact (hnd.2.2 a hapre a hais) rfl
                            · have hc := Std.HashSet.mem_iff_contains.mp hablock
                              rw [hc] at houtside
                              simp at houtside
                          have hentry : CseEntryPos f tau (.op yop args) d :=
                            .op hb hseq hs hargs hextTau
                          simp only [hg]
                          exact ⟨htab.addOp hentry, hsub⟩
                        · simp only [hg]
                          exact ⟨htab, hsub⟩
                  · rw [if_neg hp]
                    exact ⟨htab, hsub⟩
      | call ds fid args =>
          simp only [s1, cseInstrStep, hs]
          exact ⟨htab, hsub⟩
    have hused1 : ∀ x, x ∈ s1.2.2.1 ↔
        x ∈ (pre ++ [i]).flatMap Instr.uses := by
      intro x
      simp only [s1, cseInstrStep_used, mem_fold_insert_iff, hused]
      simp
    have hdefined1 : ∀ x, x ∈ s1.2.2.2.2.1 ↔
        x ∈ (pre ++ [i]).flatMap Instr.defs := by
      intro x
      simp only [s1, cseInstrStep_defined, mem_fold_insert_iff, hdefined]
      simp
    have hblockDefs1 : ∀ x, x ∈ s1.2.2.2.2.2 ↔
        x ∈ b.instrs.flatMap Instr.defs := by
      intro x
      simp only [s1, cseInstrStep_blockDefs]
      exact hblockDefs x
    exact ih (pre := pre ++ [i]) (hseq := hseq1)
      (seen := seen ++ i.defs) (hseenNodup := hseenNodup1)
      (acc := s1.1) (tab := s1.2.1) (used := s1.2.2.1)
      (σ := s1.2.2.2.1) (defined := s1.2.2.2.2.1)
      (blockDefs := s1.2.2.2.2.2) hused1 hdefined1 hblockDefs1
      hinv1 hpos1.1 hpos1.2 hout

theorem cseInstrFold_stable {f : Func} {b : Block} (hb : b ∈ f.blocks.toList)
    {seen : List ValId} {tab : CseTab} {σ : Subst} (hinv : CSEInv f seen tab σ)
    (l : List Instr) (hmem : ∀ i ∈ l, i ∈ b.instrs)
    (hnd : (seen ++ l.flatMap Instr.defs).Nodup) (acc : List Instr)
    (used defined blockDefs : Std.HashSet ValId) :
    SubstStable seen σ
      (l.foldl (fun s i => cseInstrStep i s)
        ⟨acc, tab, used, σ, defined, blockDefs⟩).2.2.2.1 := by
  induction l generalizing seen tab σ acc used defined blockDefs with
  | nil => intro x hx; rfl
  | cons i is ih =>
    simp only [List.flatMap_cons] at hnd
    have hprefix : (seen ++ i.defs).Nodup := by
      apply List.Nodup.of_append_left (l₂ := is.flatMap Instr.defs)
      simpa [List.append_assoc] using hnd
    have hone := cseInstrStep_inv hb (used := used) (defined := defined)
      (blockDefs := blockDefs) hinv i
      (hmem i (by simp)) hprefix
    have hstate := cseInstrStep_state i acc tab used σ defined blockDefs
    let s1 := cseInstrStep i ⟨acc, tab, used, σ, defined, blockDefs⟩
    have hinv1 : CSEInv f (seen ++ i.defs) s1.2.1 s1.2.2.2.1 := by
      rw [hstate]
      exact hone.1
    have htail : ((seen ++ i.defs) ++ is.flatMap Instr.defs).Nodup := by
      simpa [List.append_assoc] using hnd
    have hs1 : SubstStable seen σ s1.2.2.2.1 := by
      rw [hstate]
      exact cseInstrStep_stable i hprefix
    have hrest := ih hinv1 (fun j hj => hmem j (by simp [hj])) htail
      s1.1 s1.2.2.1 s1.2.2.2.2.1 s1.2.2.2.2.2
    rw [List.foldl_cons]
    exact hs1.trans (fun x hx => hrest x (List.mem_append_left _ hx))

theorem CSEInv.emptyTab {f : Func} {seen : List ValId} {tab : CseTab} {σ : Subst}
    (h : CSEInv f seen tab σ) : CSEInv f seen {} σ := by
  refine ⟨⟨by simp, by simp⟩, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
  simp [cseTabVals]

theorem cseTabVals_inheritTab {tab : CseTab} {ps : List ValId} {x : ValId}
    (hx : x ∈ cseTabVals (Passes.inheritTab tab ps)) :
    x ∈ cseTabVals tab := by
  simp only [cseTabVals, Passes.inheritTab, List.mem_append, List.mem_map,
    List.mem_filter] at hx ⊢
  rcases hx with ⟨e, ⟨he, -⟩, rfl⟩ | ⟨e, ⟨he, -⟩, rfl⟩
  · exact Or.inl ⟨e, he, rfl⟩
  · exact Or.inr ⟨e, he, rfl⟩

theorem CSEInv.inheritTab {f : Func} {seen : List ValId} {tab : CseTab}
    {σ : Subst} (h : CSEInv f seen tab σ) (ps : List ValId) :
    CSEInv f seen (Passes.inheritTab tab ps) σ := by
  refine ⟨⟨?_, ?_⟩, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
  · intro yop args d hm
    exact h.1.1 (List.mem_filter.mp hm).1
  · intro v d hm
    exact h.1.2 (List.mem_filter.mp hm).1
  · intro x hx
    exact h.2.2.2.2 x (cseTabVals_inheritTab hx)

theorem CSEInv.transportTable {f : Func} {seen seen' : List ValId}
    {tab tab' : CseTab} {σ τ : Subst}
    (hold : CSEInv f seen tab σ) (hnew : CSEInv f seen' tab' τ)
    (hseen : ∀ x ∈ seen, x ∈ seen') (hstable : SubstStable seen σ τ) :
    CSEInv f seen' tab τ := by
  refine ⟨hold.1, hnew.2.1, hnew.2.2.1, hnew.2.2.2.1, ?_⟩
  intro x hx
  have ho := hold.2.2.2.2 x hx
  refine ⟨hseen x ho.1, ?_⟩
  rw [hstable x ho.1]
  exact ho.2

def cseSeen (f : Func) (n : Nat) : List ValId :=
  (f.blocks.toList.take n).flatMap fun b => b.instrs.flatMap Instr.defs

theorem cseSeen_succ {f : Func} {n : Nat} {b : Block} (h : f.blocks[n]? = some b) :
    cseSeen f (n + 1) = cseSeen f n ++ b.instrs.flatMap Instr.defs := by
  have hl : f.blocks.toList[n]? = some b := by simpa using h
  simp [cseSeen, List.take_add_one, hl]

theorem cseSeen_sublist (f : Func) (n : Nat) :
    (cseSeen f n).Sublist
      (f.blocks.toList.flatMap fun b => b.instrs.flatMap Instr.defs) :=
  (List.take_sublist n f.blocks.toList).flatMap _

theorem getElem!_eq_getElem {α : Type} [Inhabited α] {a : Array α} {i : Nat}
    (h : i < a.size) : a[i]! = a[i] := by
  simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_getElem h]

@[simp] theorem sourceEdgeStep_size (bi : BlockId) (acc : Array (List BlockId))
    (e : Edge) : (sourceEdgeStep bi acc e).size = acc.size := by
  simp [sourceEdgeStep]

theorem sourceEdgeStep_mem_self {bi : BlockId} {acc : Array (List BlockId)}
    {e : Edge} (ht : e.target < acc.size) :
    bi ∈ (sourceEdgeStep bi acc e)[e.target]! := by
  rw [sourceEdgeStep, getElem!_eq_getElem (by simp [ht]),
    Array.getElem_setIfInBounds_self]
  simp

theorem sourceEdgeStep_mem_preserve {bi x q : BlockId}
    {acc : Array (List BlockId)} {e : Edge} (hq : q < acc.size)
    (hx : x ∈ acc[q]!) : x ∈ (sourceEdgeStep bi acc e)[q]! := by
  by_cases heq : q = e.target
  · subst q
    rw [sourceEdgeStep, getElem!_eq_getElem (by simp [hq]),
      Array.getElem_setIfInBounds_self]
    exact List.mem_cons_of_mem _ hx
  · rw [sourceEdgeStep, getElem!_eq_getElem (by simp [hq]),
      Array.getElem_setIfInBounds_ne hq (Ne.symm heq), ← getElem!_eq_getElem hq]
    exact hx

theorem sourceEdgeFold_mem_preserve {bi x q : BlockId}
    {acc : Array (List BlockId)} (hq : q < acc.size) (hx : x ∈ acc[q]!)
    (es : List Edge) :
    x ∈ (es.foldl (sourceEdgeStep bi) acc)[q]! := by
  induction es generalizing acc with
  | nil => exact hx
  | cons e es ih =>
      rw [List.foldl_cons]
      exact ih (by simpa using hq) (sourceEdgeStep_mem_preserve hq hx)

theorem sourceEdgeFold_mem {bi : BlockId} {acc : Array (List BlockId)}
    {e : Edge} {es : List Edge} (he : e ∈ es) (ht : e.target < acc.size) :
    bi ∈ (es.foldl (sourceEdgeStep bi) acc)[e.target]! := by
  induction es generalizing acc with
  | nil => simp at he
  | cons e0 es ih =>
      rw [List.foldl_cons]
      rcases List.mem_cons.mp he with rfl | he
      · exact sourceEdgeFold_mem_preserve (by simpa using ht)
          (sourceEdgeStep_mem_self ht) es
      · exact ih he (by simpa using ht)

@[simp] theorem sourceBlockStep_size (f : Func) (acc : Array (List BlockId))
    (bi : BlockId) : (sourceBlockStep f acc bi).size = acc.size := by
  unfold sourceBlockStep
  induction f.blocks[bi]!.term.edges generalizing acc with
  | nil => rfl
  | cons e es ih => simpa using ih (sourceEdgeStep bi acc e)

theorem sourceBlockStep_mem_preserve {f : Func} {x q : BlockId}
    {acc : Array (List BlockId)} (hq : q < acc.size) (hx : x ∈ acc[q]!)
    (bi : BlockId) : x ∈ (sourceBlockStep f acc bi)[q]! := by
  exact sourceEdgeFold_mem_preserve hq hx _

theorem sourceBlockStep_mem {f : Func} {bi : BlockId} {acc : Array (List BlockId)}
    {e : Edge} (he : e ∈ f.blocks[bi]!.term.edges) (ht : e.target < acc.size) :
    bi ∈ (sourceBlockStep f acc bi)[e.target]! := by
  exact sourceEdgeFold_mem he ht

theorem sourceBlockFold_mem_preserve {f : Func} {x q : BlockId}
    {acc : Array (List BlockId)} (hq : q < acc.size) (hx : x ∈ acc[q]!)
    (bis : List BlockId) : x ∈ (bis.foldl (sourceBlockStep f) acc)[q]! := by
  induction bis generalizing acc with
  | nil => exact hx
  | cons bi bis ih =>
      rw [List.foldl_cons]
      exact ih (by simpa using hq) (sourceBlockStep_mem_preserve hq hx bi)

theorem sourceBlockFold_mem {f : Func} {bi : BlockId} {acc : Array (List BlockId)}
    {e : Edge} {bis : List BlockId} (hbi : bi ∈ bis)
    (he : e ∈ f.blocks[bi]!.term.edges) (ht : e.target < acc.size) :
    bi ∈ (bis.foldl (sourceBlockStep f) acc)[e.target]! := by
  induction bis generalizing acc with
  | nil => simp at hbi
  | cons bj bis ih =>
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hbi with rfl | hbi
      · exact sourceBlockFold_mem_preserve (by simpa using ht)
          (sourceBlockStep_mem he ht) bis
      · exact ih hbi (by simpa using ht)

theorem mem_inEdgeSources {f : Func} {bi : BlockId} {b : Block} {e : Edge}
    (hb : f.blocks[bi]? = some b) (he : e ∈ b.term.edges)
    (ht : e.target < f.blocks.size) : bi ∈ (inEdgeSources f)[e.target]! := by
  have hbi : bi ∈ List.range' 0 f.blocks.size 1 := by
    rw [List.mem_range'_1]
    exact ⟨Nat.zero_le _, by simpa using (Array.getElem?_eq_some_iff.mp hb).1⟩
  have hbang : f.blocks[bi]! = b := by
    rw [getElem!_eq_getElem (Array.getElem?_eq_some_iff.mp hb).1]
    exact (Array.getElem?_eq_some_iff.mp hb).2
  rw [inEdgeSources_eq_fold]
  apply sourceBlockFold_mem hbi (ht := by simpa using ht)
  simpa [hbang] using he

theorem inEdgeSources_single_eq {f : Func} {bi p : BlockId} {b : Block} {e : Edge}
    (hb : f.blocks[bi]? = some b) (he : e ∈ b.term.edges)
    (ht : e.target < f.blocks.size) (hs : (inEdgeSources f)[e.target]! = [p]) :
    bi = p := by
  have hm := mem_inEdgeSources hb he ht
  rw [hs] at hm
  simpa using hm

def CSEPrefixInv (f : Func) (n : Nat) : Prop :=
  let st := csePrefix f n
  CSEInv f (cseSeen f n) {} st.2.2
    ∧ st.2.1.size = f.blocks.size
    ∧ ∀ p < n, CSEInv f (cseSeen f n) st.2.1[p]! st.2.2

theorem csePrefixInv_zero (f : Func) : CSEPrefixInv f 0 := by
  refine ⟨cseInv_empty f, by simp [csePrefix], ?_⟩
  intro p hp
  omega

theorem cseEntryTab_inv {f : Func} {n : Nat} (hpre : CSEPrefixInv f n) :
    CSEInv f (cseSeen f n)
      (cseEntryTab f (inEdgeSources f) (csePrefix f n).2.1 n)
      (csePrefix f n).2.2 := by
  by_cases he : (n == f.entry) = true
  · rw [cseEntryTab, if_pos he]
    exact hpre.1.emptyTab
  · cases hs : (inEdgeSources f)[n]! with
    | nil =>
      rw [cseEntryTab, if_neg he, hs]
      exact hpre.1.emptyTab
    | cons p ps =>
      cases ps with
      | nil =>
        by_cases hp : p < n
        · simpa [cseEntryTab, he, hs, hp] using
            (hpre.2.2 p hp).inheritTab f.blocks[n]!.params
        · simpa [cseEntryTab, he, hs, hp] using hpre.1.emptyTab
      | cons q qs =>
        rw [cseEntryTab, if_neg he, hs]
        exact hpre.1.emptyTab

theorem csePrefixInv_succ {f : Func} {n : Nat} (hnd : f.allDefs.Nodup)
    (hpre : CSEPrefixInv f n) (hn : n < f.blocks.size) :
    CSEPrefixInv f (n + 1) := by
  let b := f.blocks[n]
  have hbget : f.blocks[n]? = some b := by
    rw [Array.getElem?_eq_getElem hn]
  have hbBang : f.blocks[n]! = b := by
    rw [getElem!_eq_getElem hn]
  have hbmem : b ∈ f.blocks.toList := by
    obtain ⟨hlt, hget⟩ := Array.getElem?_eq_some_iff.mp hbget
    exact List.mem_iff_getElem.mpr ⟨n, by simpa using hlt, by simpa using hget⟩
  have hseen : cseSeen f (n + 1) =
      cseSeen f n ++ b.instrs.flatMap Instr.defs := cseSeen_succ hbget
  have hseenNodup : (cseSeen f n ++ b.instrs.flatMap Instr.defs).Nodup := by
    rw [← hseen]
    exact (instrDefs_nodup hnd).sublist (cseSeen_sublist f (n + 1))
  let tab := cseEntryTab f (inEdgeSources f) (csePrefix f n).2.1 n
  let r := b.instrs.foldl (fun s i => cseInstrStep i s)
    ⟨[], tab, ∅, (csePrefix f n).2.2, ∅, cseBlockDefs b⟩
  have htab : CSEInv f (cseSeen f n) tab (csePrefix f n).2.2 :=
    cseEntryTab_inv hpre
  have hr := cseInstrFold_inv hbmem htab b.instrs (fun i hi => hi)
    hseenNodup [] ∅ ∅ (cseBlockDefs b)
  have hstable := cseInstrFold_stable hbmem htab b.instrs (fun i hi => hi)
    hseenNodup [] ∅ ∅ (cseBlockDefs b)
  change CSEPrefixInv f (n + 1)
  rw [CSEPrefixInv, csePrefix_succ]
  simp only [cseBlockStep]
  rw [hbBang, hseen]
  change CSEInv f (cseSeen f n ++ b.instrs.flatMap Instr.defs) {} r.2.2.2.1
      ∧ ((csePrefix f n).2.1.setIfInBounds n r.2.1).size = f.blocks.size
      ∧ ∀ p < n + 1,
        CSEInv f (cseSeen f n ++ b.instrs.flatMap Instr.defs)
          ((csePrefix f n).2.1.setIfInBounds n r.2.1)[p]! r.2.2.2.1
  refine ⟨hr.1.emptyTab, by simpa using hpre.2.1, ?_⟩
  intro p hp
  by_cases hpn : p = n
  · subst p
    have hn0 : n < (csePrefix f n).2.1.size := by rw [hpre.2.1]; exact hn
    have hn1 : n < ((csePrefix f n).2.1.setIfInBounds n r.2.1).size := by simpa
    rw [getElem!_eq_getElem hn1, Array.getElem_setIfInBounds_self]
    exact hr.1
  · have hplt : p < n := by omega
    have hp0 : p < (csePrefix f n).2.1.size := by rw [hpre.2.1]; omega
    have hp1 : p < ((csePrefix f n).2.1.setIfInBounds n r.2.1).size := by simpa
    rw [getElem!_eq_getElem hp1,
      Array.getElem_setIfInBounds_ne hp0 (Ne.symm hpn), ← getElem!_eq_getElem hp0]
    exact (hpre.2.2 p hplt).transportTable hr.1
      (fun x hx => List.mem_append_left _ hx) hstable

theorem csePrefixInv {f : Func} (hnd : f.allDefs.Nodup) :
    ∀ n ≤ f.blocks.size, CSEPrefixInv f n := by
  intro n
  induction n with
  | zero => intro _; exact csePrefixInv_zero f
  | succ n ih =>
    intro hn
    exact csePrefixInv_succ hnd (ih (by omega)) (by omega)

theorem csePrefix_ext_succ {f : Func} {n : Nat} (hnd : f.allDefs.Nodup)
    (hn : n < f.blocks.size) :
    SubstExt (csePrefix f n).2.2 (csePrefix f (n + 1)).2.2 := by
  let b := f.blocks[n]
  have hbget : f.blocks[n]? = some b := by rw [Array.getElem?_eq_getElem hn]
  have hbmem : b ∈ f.blocks.toList := by
    obtain ⟨hlt, hget⟩ := Array.getElem?_eq_some_iff.mp hbget
    exact List.mem_iff_getElem.mpr ⟨n, by simpa using hlt, by simpa using hget⟩
  have hseen := cseSeen_succ hbget
  have hseenNodup : (cseSeen f n ++ b.instrs.flatMap Instr.defs).Nodup := by
    rw [← hseen]
    exact (instrDefs_nodup hnd).sublist (cseSeen_sublist f (n + 1))
  have hpre := csePrefixInv hnd n (Nat.le_of_lt hn)
  let tab := cseEntryTab f (inEdgeSources f) (csePrefix f n).2.1 n
  have htab : CSEInv f (cseSeen f n) tab (csePrefix f n).2.2 :=
    cseEntryTab_inv hpre
  have hr := cseInstrFold_inv hbmem htab b.instrs (fun i hi => hi)
    hseenNodup [] ∅ ∅ (cseBlockDefs b)
  rw [csePrefix_succ]
  simp only [cseBlockStep]
  have hbBang : f.blocks[n]! = b := by rw [getElem!_eq_getElem hn]
  rw [hbBang]
  intro x y hxy
  exact hr.2 hxy

theorem csePrefix_ext_to {f : Func} (hnd : f.allDefs.Nodup) {n m : Nat}
    (hle : n ≤ m) (hm : m ≤ f.blocks.size) :
    SubstExt (csePrefix f n).2.2 (csePrefix f m).2.2 := by
  induction m generalizing n with
  | zero =>
    have hn : n = 0 := by omega
    subst n
    intro x y hxy
    exact hxy
  | succ m ih =>
    by_cases hn : n = m + 1
    · subst n
      intro hxy
      exact hxy
    · have hnm : n ≤ m := by omega
      have hleft : SubstExt (csePrefix f n).2.2 (csePrefix f m).2.2 :=
        ih hnm (by omega)
      exact SubstExt.trans hleft (csePrefix_ext_succ hnd (by omega))

/-- The guard-projection companion to `CSEPrefixInv`.  Tables retain the
suffix-stability witness from the instruction that created each entry, while
the global substitution retains the prefix-use witness from every dropped
operation. -/
def CSEPrefixPosInv (f : Func) (n : Nat) : Prop :=
  let tau := (csePrefix f f.blocks.size).2.2
  let st := csePrefix f n
  CseSubPosSound f st.2.2 ∧
    ∀ p < n, CseTabPosSound f tau st.2.1[p]!

theorem csePrefixPosInv_zero (f : Func) : CSEPrefixPosInv f 0 := by
  refine ⟨?_, ?_⟩
  · intro d d0 h
    simp at h
  · intro p hp
    omega

theorem cseEntryTab_pos {f : Func} {n : Nat}
    (hpre : CSEPrefixPosInv f n) :
    CseTabPosSound f (csePrefix f f.blocks.size).2.2
      (cseEntryTab f (inEdgeSources f) (csePrefix f n).2.1 n) := by
  by_cases he : (n == f.entry) = true
  · rw [cseEntryTab, if_pos he]
    exact CseTabPosSound.empty f _
  · cases hs : (inEdgeSources f)[n]! with
    | nil =>
        rw [cseEntryTab, if_neg he, hs]
        exact CseTabPosSound.empty f _
    | cons p ps =>
        cases ps with
        | nil =>
            by_cases hp : p < n
            · have htab : CseTabPosSound f (csePrefix f f.blocks.size).2.2
                  (csePrefix f n).2.1[p]! := hpre.2 p hp
              simpa [cseEntryTab, he, hs, hp] using
                CseTabPosSound.inheritTab htab f.blocks[n]!.params
            · simp [cseEntryTab, he, hs, hp]
        | cons q qs =>
            rw [cseEntryTab, if_neg he, hs]
            exact CseTabPosSound.empty f _

theorem csePrefixPosInv_succ {f : Func} {n : Nat}
    (hnd : f.allDefs.Nodup) (hpre : CSEPrefixPosInv f n)
    (hn : n < f.blocks.size) : CSEPrefixPosInv f (n + 1) := by
  let b := f.blocks[n]
  have hbget : f.blocks[n]? = some b := Array.getElem?_eq_getElem hn
  have hbBang : f.blocks[n]! = b := by rw [getElem!_eq_getElem hn]
  have hbmem : b ∈ f.blocks.toList := by
    exact List.mem_iff_getElem.mpr ⟨n, by simpa using hn,
      by simpa using (Array.getElem?_eq_some_iff.mp hbget).2⟩
  have hregular := csePrefixInv hnd n (Nat.le_of_lt hn)
  let tab := cseEntryTab f (inEdgeSources f) (csePrefix f n).2.1 n
  let r := b.instrs.foldl (fun s i => cseInstrStep i s)
    ⟨[], tab, ∅, (csePrefix f n).2.2, ∅, cseBlockDefs b⟩
  have hbdefs : b.instrs.flatMap Instr.defs |>.Nodup := by
    have hall := instrDefs_nodup hnd
    have hsub : (b.instrs.flatMap Instr.defs).Sublist
        (f.blocks.toList.flatMap fun b => b.instrs.flatMap Instr.defs) := by
      simpa using (List.Sublist.flatMap (List.singleton_sublist.mpr hbmem)
        (fun b : Block => b.instrs.flatMap Instr.defs))
    exact hall.sublist hsub
  have hseenNodup :
      (cseSeen f n ++ b.instrs.flatMap Instr.defs).Nodup := by
    rw [← cseSeen_succ hbget]
    exact (instrDefs_nodup hnd).sublist (cseSeen_sublist f (n + 1))
  have hgate : SubstExt r.2.2.2.1 (csePrefix f f.blocks.size).2.2 := by
    have h : SubstExt (csePrefix f (n + 1)).2.2 (csePrefix f f.blocks.size).2.2 :=
      csePrefix_ext_to hnd (Nat.succ_le_of_lt hn) (Nat.le_refl f.blocks.size)
    rw [csePrefix_succ] at h
    simp only [cseBlockStep] at h
    rw [hbBang] at h
    exact fun {_ _} hxy => h hxy
  have hr := cseInstrFold_pos hbmem [] b.instrs rfl hbdefs
    (seen := cseSeen f n) hseenNodup [] tab ∅
    (csePrefix f n).2.2 ∅ (cseBlockDefs b)
    (by simp) (by simp) (fun x => mem_cseBlockDefs)
    (cseEntryTab_inv hregular) (cseEntryTab_pos hpre) hpre.1 hgate
  change CSEPrefixPosInv f (n + 1)
  rw [CSEPrefixPosInv, csePrefix_succ]
  simp only [cseBlockStep]
  rw [hbBang]
  change CseSubPosSound f r.2.2.2.1 ∧
    ∀ p < n + 1,
      CseTabPosSound f (csePrefix f f.blocks.size).2.2
        ((csePrefix f n).2.1.setIfInBounds n r.2.1)[p]!
  refine ⟨hr.2, ?_⟩
  intro p hp
  by_cases hpn : p = n
  · subst p
    have hn0 : n < (csePrefix f n).2.1.size := by
      rw [hregular.2.1]
      exact hn
    have hn1 : n < ((csePrefix f n).2.1.setIfInBounds n r.2.1).size := by
      simpa
    rw [getElem!_eq_getElem hn1, Array.getElem_setIfInBounds_self]
    exact hr.1
  · have hplt : p < n := by omega
    have hp0 : p < (csePrefix f n).2.1.size := by
      rw [hregular.2.1]
      omega
    have hp1 : p < ((csePrefix f n).2.1.setIfInBounds n r.2.1).size := by
      simpa
    rw [getElem!_eq_getElem hp1,
      Array.getElem_setIfInBounds_ne hp0 (Ne.symm hpn), ← getElem!_eq_getElem hp0]
    exact hpre.2 p hplt

theorem csePrefixPosInv {f : Func} (hnd : f.allDefs.Nodup) :
    ∀ n ≤ f.blocks.size, CSEPrefixPosInv f n := by
  intro n
  induction n with
  | zero => intro _; exact csePrefixPosInv_zero f
  | succ n ih =>
      intro hn
      exact csePrefixPosInv_succ hnd (ih (by omega)) (by omega)

theorem cseFinalSubDefSound {f : Func} (hnd : f.allDefs.Nodup) :
    CseSubDefSound f (csePrefix f f.blocks.size).2.2 :=
  (csePrefixInv hnd f.blocks.size (Nat.le_refl _)).1.2.1

theorem cseFinalSubPosSound {f : Func} (hnd : f.allDefs.Nodup) :
    CseSubPosSound f (csePrefix f f.blocks.size).2.2 :=
  (csePrefixPosInv hnd f.blocks.size (Nat.le_refl _)).1

/-- The representative of every final CSE alias was processed strictly before
its dropped destination.  This is the global fold-order companion to the local
prefix/suffix certificates in `CseSubPosSound`. -/
def AliasOrdered (seen : List ValId) (σ : Subst) : Prop :=
  ∀ d d0, σ[d]? = some d0 →
    ∃ pre mid post, seen = pre ++ (d0 :: mid) ++ d :: post

theorem AliasOrdered.empty : AliasOrdered [] (∅ : Subst) := by
  intro d d0 h
  simp at h

theorem AliasOrdered.insert {seen : List ValId} {σ : Subst}
    (ho : AliasOrdered seen σ) {d d0 : ValId}
    (_hd : d ∉ seen) (hd0 : d0 ∈ seen) :
    AliasOrdered (seen ++ [d]) (σ.insert d d0) := by
  intro x y hxy
  rw [Std.HashMap.getElem?_insert] at hxy
  split at hxy
  · rename_i heq
    have hxd : x = d := (beq_iff_eq.mp heq).symm
    subst x
    have hyd : y = d0 := (Option.some.inj hxy).symm
    subst y
    obtain ⟨pre, post, hseen⟩ := List.mem_iff_append.mp hd0
    exact ⟨pre, post, [], by simp [hseen, List.append_assoc]⟩
  · obtain ⟨pre, mid, post, hseen⟩ := ho x y hxy
    exact ⟨pre, mid, post ++ [d], by simp [hseen, List.append_assoc]⟩

theorem AliasOrdered.weaken {seen seen' : List ValId} {σ : Subst}
    (ho : AliasOrdered seen σ) (hs : ∃ tail, seen' = seen ++ tail) :
    AliasOrdered seen' σ := by
  obtain ⟨tail, rfl⟩ := hs
  intro d d0 h
  obtain ⟨pre, mid, post, hseen⟩ := ho d d0 h
  exact ⟨pre, mid, post ++ tail, by simp [hseen, List.append_assoc]⟩

theorem AliasOrdered.step {f : Func} {b : Block} (_hb : b ∈ f.blocks.toList)
    {seen : List ValId} {tab : CseTab} {used : Std.HashSet ValId} {σ : Subst}
    {defined blockDefs : Std.HashSet ValId}
    (hinv : CSEInv f seen tab σ) (ho : AliasOrdered seen σ)
    (i : Instr) (_hi : i ∈ b.instrs) (hnd : (seen ++ i.defs).Nodup) :
    let r := cseInstrStep i ⟨[], tab, used, σ, defined, blockDefs⟩
    AliasOrdered (seen ++ i.defs) r.2.2.2.1 := by
  have hkeep : AliasOrdered (seen ++ i.defs) σ :=
    ho.weaken ⟨i.defs, rfl⟩
  cases i with
  | const d v =>
      have hd : d ∉ seen := by
        rw [List.nodup_append] at hnd
        exact fun hm => (hnd.2.2 d hm d (by simp [Instr.defs])) rfl
      simp only [cseInstrStep, substInstr]
      split
      · rename_i w d0 hfind
        have hm : (w, d0) ∈ tab.consts := List.mem_of_find?_eq_some hfind
        have hd0 : d0 ∈ seen := (hinv.2.2.2.2 d0 (by
          exact List.mem_append_right _
            (List.mem_map.mpr ⟨(w, d0), hm, rfl⟩))).1
        change AliasOrdered (seen ++ [d]) (σ.insert d d0)
        exact ho.insert hd hd0
      · change AliasOrdered (seen ++ [d]) σ
        exact hkeep
  | op ds yop args =>
      cases ds with
      | nil =>
          simp only [cseInstrStep, substInstr, Instr.defs, List.append_nil]
          intro d d0 h
          exact ho d d0 h
      | cons d rest =>
          cases rest with
          | cons e es =>
              change AliasOrdered (seen ++ d :: e :: es) σ
              exact hkeep
          | nil =>
              have hd : d ∉ seen := by
                rw [List.nodup_append] at hnd
                exact fun hm => (hnd.2.2 d hm d (by simp [Instr.defs])) rfl
              simp only [cseInstrStep, substInstr]
              split
              · split
                · rename_i key d0 hfind
                  split
                  · change AliasOrdered (seen ++ [d]) σ
                    exact hkeep
                  · have hm : (key, d0) ∈ tab.ops :=
                      List.mem_of_find?_eq_some hfind
                    have hd0 : d0 ∈ seen := (hinv.2.2.2.2 d0 (by
                      exact List.mem_append_left _
                        (List.mem_map.mpr ⟨(key, d0), hm, rfl⟩))).1
                    change AliasOrdered (seen ++ [d]) (σ.insert d d0)
                    exact ho.insert hd hd0
                · split <;> change AliasOrdered (seen ++ [d]) σ <;>
                    exact hkeep
              · change AliasOrdered (seen ++ [d]) σ
                exact hkeep
  | call ds fid args =>
      change AliasOrdered (seen ++ ds) σ
      exact hkeep

theorem cseInstrFold_ordered {f : Func} {b : Block}
    (hb : b ∈ f.blocks.toList) {seen : List ValId} {tab : CseTab} {σ : Subst}
    (hinv : CSEInv f seen tab σ) (ho : AliasOrdered seen σ)
    (l : List Instr) (hmem : ∀ i ∈ l, i ∈ b.instrs)
    (hnd : (seen ++ l.flatMap Instr.defs).Nodup) (acc : List Instr)
    (used defined blockDefs : Std.HashSet ValId) :
    let r := l.foldl (fun s i => cseInstrStep i s)
      ⟨acc, tab, used, σ, defined, blockDefs⟩
    AliasOrdered (seen ++ l.flatMap Instr.defs) r.2.2.2.1 := by
  induction l generalizing seen tab σ acc used defined blockDefs with
  | nil =>
      simp only [List.foldl_nil, List.flatMap_nil, List.append_nil]
      intro d d0 h
      exact ho d d0 h
  | cons i is ih =>
      have hprefix : (seen ++ i.defs).Nodup := by
        apply List.Nodup.of_append_left (l₂ := is.flatMap Instr.defs)
        simpa [List.append_assoc] using hnd
      have hstep := cseInstrStep_inv hb (used := used) (defined := defined)
        (blockDefs := blockDefs) hinv i (hmem i (by simp)) hprefix
      have hord := AliasOrdered.step hb (used := used) (defined := defined)
        (blockDefs := blockDefs) hinv ho i (hmem i (by simp)) hprefix
      let s1 := cseInstrStep i ⟨acc, tab, used, σ, defined, blockDefs⟩
      have hstate := cseInstrStep_state i acc tab used σ defined blockDefs
      have hinv1 : CSEInv f (seen ++ i.defs) s1.2.1 s1.2.2.2.1 := by
        rw [hstate]
        exact hstep.1
      have hord1 : AliasOrdered (seen ++ i.defs) s1.2.2.2.1 := by
        rw [hstate]
        exact hord
      rw [List.foldl_cons]
      simpa [List.flatMap_cons, List.append_assoc] using
        ih hinv1 hord1 (fun j hj => hmem j (by simp [hj]))
          (by simpa [List.flatMap_cons, List.append_assoc] using hnd)
          s1.1 s1.2.2.1 s1.2.2.2.2.1 s1.2.2.2.2.2

theorem csePrefix_ordered {f : Func} (hnd : f.allDefs.Nodup) :
    ∀ n ≤ f.blocks.size,
      AliasOrdered (cseSeen f n) (csePrefix f n).2.2 := by
  intro n hn
  induction n with
  | zero => exact AliasOrdered.empty
  | succ n ih =>
      have hnlt : n < f.blocks.size := by omega
      let b := f.blocks[n]
      have hb : f.blocks[n]? = some b := Array.getElem?_eq_getElem hnlt
      have hbmem : b ∈ f.blocks.toList := by
        exact List.mem_iff_getElem.mpr ⟨n, by simpa using hnlt,
          by simpa using (Array.getElem?_eq_some_iff.mp hb).2⟩
      have hpre := csePrefixInv hnd n (Nat.le_of_lt hnlt)
      let tab := cseEntryTab f (inEdgeSources f) (csePrefix f n).2.1 n
      let r := b.instrs.foldl (fun s i => cseInstrStep i s)
        ⟨[], tab, ∅, (csePrefix f n).2.2, ∅, cseBlockDefs b⟩
      have hoN : AliasOrdered (cseSeen f n) (csePrefix f n).2.2 :=
        ih (Nat.le_of_lt hnlt)
      have hr := cseInstrFold_ordered hbmem
        (hinv := cseEntryTab_inv hpre) (ho := hoN)
        b.instrs (fun i hi => hi)
        (by
          rw [← cseSeen_succ hb]
          exact (instrDefs_nodup hnd).sublist (cseSeen_sublist f (n + 1)))
        [] ∅ ∅ (cseBlockDefs b)
      rw [csePrefix_succ]
      simp only [cseBlockStep]
      have hbang : f.blocks[n]! = b := by
        rw [getElem!_eq_getElem hnlt]
      rw [hbang]
      rw [cseSeen_succ hb]
      exact hr

theorem cseEntryTab_sound {f : Func} (hnd : f.allDefs.Nodup)
    {n : Nat} (hn : n ≤ f.blocks.size) :
    CseTabDefSound f
      (cseEntryTab f (inEdgeSources f) (csePrefix f n).2.1 n) :=
  (cseEntryTab_inv (csePrefixInv hnd n hn)).1

theorem csePrefix_stable_succ {f : Func} {n : Nat} (hnd : f.allDefs.Nodup)
    (hn : n < f.blocks.size) :
    SubstStable (cseSeen f n) (csePrefix f n).2.2 (csePrefix f (n + 1)).2.2 := by
  let b := f.blocks[n]
  have hbget : f.blocks[n]? = some b := by rw [Array.getElem?_eq_getElem hn]
  have hbmem : b ∈ f.blocks.toList := by
    obtain ⟨hlt, hget⟩ := Array.getElem?_eq_some_iff.mp hbget
    exact List.mem_iff_getElem.mpr ⟨n, by simpa using hlt, by simpa using hget⟩
  have hseen := cseSeen_succ hbget
  have hseenNodup : (cseSeen f n ++ b.instrs.flatMap Instr.defs).Nodup := by
    rw [← hseen]
    exact (instrDefs_nodup hnd).sublist (cseSeen_sublist f (n + 1))
  have hpre := csePrefixInv hnd n (Nat.le_of_lt hn)
  let tab := cseEntryTab f (inEdgeSources f) (csePrefix f n).2.1 n
  have htab : CSEInv f (cseSeen f n) tab (csePrefix f n).2.2 :=
    cseEntryTab_inv hpre
  have hr := cseInstrFold_stable hbmem htab b.instrs (fun i hi => hi)
    hseenNodup [] ∅ ∅ (cseBlockDefs b)
  rw [csePrefix_succ]
  simp only [cseBlockStep]
  have hbBang : f.blocks[n]! = b := by rw [getElem!_eq_getElem hn]
  rw [hbBang]
  exact hr

theorem cseSeen_mono {f : Func} {n m : Nat} (h : n ≤ m) :
    ∀ x ∈ cseSeen f n, x ∈ cseSeen f m := by
  intro x hx
  unfold cseSeen at hx ⊢
  exact ((List.take_sublist_take_left h).flatMap
    (fun b : Block => b.instrs.flatMap Instr.defs)).subset hx

theorem csePrefix_stable_to {f : Func} (hnd : f.allDefs.Nodup) {n m : Nat}
    (hle : n ≤ m) (hm : m ≤ f.blocks.size) :
    SubstStable (cseSeen f n) (csePrefix f n).2.2 (csePrefix f m).2.2 := by
  induction m generalizing n with
  | zero =>
      have hn : n = 0 := by omega
      subst n
      intro x hx
      rfl
  | succ m ih =>
      by_cases hn : n = m + 1
      · subst n
        intro x hx
        rfl
      · have hnm : n ≤ m := by omega
        have hleft := ih hnm (by omega)
        have hright := csePrefix_stable_succ hnd (n := m) (by omega)
        exact hleft.trans (fun x hx => hright x (cseSeen_mono hnm x hx))

theorem substV_absorb {σ τ : Subst} (hext : SubstExt σ τ) (hrange : RangeFree τ)
    (x : ValId) : substV τ (substV σ x) = substV τ x := by
  unfold substV
  cases hs : σ[x]? with
  | none => simp [Std.HashMap.getD_eq_getD_getElem?, hs]
  | some y =>
    have ht : τ[x]? = some y := hext hs
    have hy : τ[y]? = none := hrange ht
    simp [Std.HashMap.getD_eq_getD_getElem?, hs, ht, hy]

theorem substVs_absorb {σ τ : Subst} (hext : SubstExt σ τ) (hrange : RangeFree τ)
    (xs : List ValId) : substVs τ (substVs σ xs) = substVs τ xs := by
  simp [substVs, substV_absorb hext hrange]

theorem substInstr_absorb {σ τ : Subst} (hext : SubstExt σ τ)
    (hrange : RangeFree τ) (i : Instr) :
    substInstr τ (substInstr σ i) = substInstr τ i := by
  cases i <;> simp [substInstr, substVs_absorb hext hrange]

@[simp] theorem substInstr_defs (σ : Subst) (i : Instr) :
    (substInstr σ i).defs = i.defs := by
  cases i <;> rfl

theorem substInstr_use {σ : Subst} {i : Instr} {x : ValId}
    (hx : x ∈ (substInstr σ i).uses) : ∃ y ∈ i.uses, substV σ y = x := by
  cases i with
  | const d v => simp [substInstr, Instr.uses] at hx
  | op ds yop args =>
      simp only [substInstr, Instr.uses, substVs, List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨y, hy, rfl⟩
  | call ds fid args =>
      simp only [substInstr, Instr.uses, substVs, List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨y, hy, rfl⟩

theorem substEdge_use {σ : Subst} {e : Edge} {x : ValId}
    (hx : x ∈ (substEdge σ e).args) : ∃ y ∈ e.args, substV σ y = x := by
  simpa [substEdge, substVs, List.mem_map] using hx

theorem substTerm_use {σ : Subst} {t : Term} {x : ValId}
    (hx : x ∈ (substTerm σ t).uses) : ∃ y ∈ t.uses, substV σ y = x := by
  cases t with
  | jump e =>
      simp only [Term.uses]
      exact substEdge_use hx
  | branch c et ef =>
      simp only [substTerm, Term.uses, List.mem_cons, List.mem_append] at hx ⊢
      rcases hx with (hc | hx) | hx
      · exact ⟨c, Or.inl (Or.inl rfl), hc.symm⟩
      · obtain ⟨y, hy, hxy⟩ := substEdge_use hx
        exact ⟨y, Or.inl (Or.inr hy), hxy⟩
      · obtain ⟨y, hy, hxy⟩ := substEdge_use hx
        exact ⟨y, Or.inr hy, hxy⟩
  | ret xs =>
      simpa [substTerm, Term.uses, substVs, List.mem_map] using hx
  | halt yop xs =>
      simpa [substTerm, Term.uses, substVs, List.mem_map] using hx

theorem substTerm_edge {σ : Subst} {t : Term} {e : Edge}
    (he : e ∈ (substTerm σ t).edges) :
    ∃ e0 ∈ t.edges, e0.target = e.target := by
  cases t with
  | jump e0 =>
      simp only [substTerm, Term.edges, List.mem_singleton] at he ⊢
      subst e
      exact ⟨e0, rfl, rfl⟩
  | branch c et ef =>
      simp only [substTerm, Term.edges, List.mem_cons] at he ⊢
      rcases he with rfl | he
      · exact ⟨et, Or.inl rfl, rfl⟩
      · have he' : e = substEdge σ ef := by simpa using he
        subst e
        exact ⟨ef, by simp, rfl⟩
  | ret xs => simp [substTerm, Term.edges] at he
  | halt yop xs => simp [substTerm, Term.edges] at he

theorem cseInstrStep_out {i : Instr} {acc : List Instr} {tab : CseTab}
    {used : Std.HashSet ValId} {σ : Subst} {defined blockDefs : Std.HashSet ValId} :
    let r := cseInstrStep i ⟨acc, tab, used, σ, defined, blockDefs⟩
    r.1 = acc ∨ r.1 = substInstr σ i :: acc := by
  cases i with
  | const d v =>
      simp only [cseInstrStep, substInstr]
      split <;> simp
  | op ds yop args =>
      cases ds with
      | nil => simp [cseInstrStep, substInstr]
      | cons d rest =>
          cases rest with
          | nil =>
              simp only [cseInstrStep, substInstr]
              split <;> (try split <;> (try split)) <;> simp
          | cons e es => simp [cseInstrStep, substInstr]
  | call ds fid args => simp [cseInstrStep, substInstr]

theorem cseInstrStep_acc_sublist {i : Instr} {acc : List Instr} {tab : CseTab}
    {used : Std.HashSet ValId} {σ : Subst} {defined blockDefs : Std.HashSet ValId} :
    acc.Sublist
      (cseInstrStep i ⟨acc, tab, used, σ, defined, blockDefs⟩).1 := by
  rcases cseInstrStep_out (i := i) (acc := acc) (tab := tab)
      (used := used) (σ := σ) with h | h
  · rw [h]
  · rw [h]
    exact List.Sublist.cons _ (List.Sublist.refl _)

theorem cseInstrStep_tabVals {i : Instr} {acc : List Instr} {tab : CseTab}
    {used : Std.HashSet ValId} {σ : Subst} {defined blockDefs : Std.HashSet ValId}
    {x : ValId}
    (hx : x ∈ cseTabVals
      (cseInstrStep i ⟨acc, tab, used, σ, defined, blockDefs⟩).2.1) :
    x ∈ cseTabVals tab ∨
      x ∈ (cseInstrStep i
        ⟨acc, tab, used, σ, defined, blockDefs⟩).1.flatMap Instr.defs := by
  cases i with
  | const d v =>
      cases hfind : tab.consts.find? (fun x => x.1 == v) with
      | some a =>
          have hx' : x ∈ cseTabVals tab := by
            simpa [cseInstrStep, substInstr, hfind] using hx
          exact Or.inl hx'
      | none =>
          simp only [cseInstrStep, substInstr, hfind, cseTabVals, List.map_cons,
            List.mem_append, List.mem_cons, Instr.defs, List.flatMap_cons] at hx ⊢
          tauto
  | op ds yop args =>
      cases ds with
      | nil => exact Or.inl hx
      | cons d rest =>
          cases rest with
          | cons e es => exact Or.inl hx
          | nil =>
              by_cases hp : pureOp yop = true
              · cases hfind : tab.ops.find? (fun x => x.1 == (yop, substVs σ args)) with
                | some a =>
                    have hx' : x ∈ cseTabVals tab := by
                      by_cases hu : used.contains d = true
                      · simpa [cseInstrStep, substInstr, hp, hfind, hu] using hx
                      · simpa [cseInstrStep, substInstr, hp, hfind, hu] using hx
                    exact Or.inl hx'
                | none =>
                    by_cases hg : (substVs σ args).all (fun a =>
                        defined.contains a || !blockDefs.contains a) = true
                    · simp only [cseInstrStep, substInstr, hp, if_true, hfind, hg,
                        cseTabVals, List.map_cons, List.mem_append, List.mem_cons,
                        Instr.defs, List.flatMap_cons] at hx ⊢
                      tauto
                    · have hx' : x ∈ cseTabVals tab := by
                        simpa [cseInstrStep, substInstr, hp, hfind, hg] using hx
                      exact Or.inl hx'
              · have hx' : x ∈ cseTabVals tab := by
                  simpa [cseInstrStep, substInstr, hp] using hx
                exact Or.inl hx'
  | call ds fid args => exact Or.inl hx

theorem cseInstrStep_defs_resolve {f : Func} {seen : List ValId} {i : Instr}
    {acc : List Instr} {tab : CseTab} {used : Std.HashSet ValId} {σ : Subst}
    {defined blockDefs : Std.HashSet ValId}
    (hinv : CSEInv f seen tab σ)
    (hnd : (seen ++ i.defs).Nodup) {d : ValId} (hd : d ∈ i.defs) :
    let r := cseInstrStep i ⟨acc, tab, used, σ, defined, blockDefs⟩
    substV r.2.2.2.1 d ∈ r.1.flatMap Instr.defs ∨
      substV r.2.2.2.1 d ∈ cseTabVals tab := by
  have hfresh : d ∉ seen := by
    rw [List.nodup_append] at hnd
    exact fun hm => (hnd.2.2 d hm d hd) rfl
  have hdnone : σ[d]? = none := by
    by_contra hn
    obtain ⟨d0, hd0⟩ := Option.ne_none_iff_exists'.mp hn
    exact hfresh (hinv.2.2.2.1 hd0).1
  cases i with
  | const d' v =>
      simp only [Instr.defs, List.mem_singleton] at hd
      subst d'
      cases hfind : tab.consts.find? (fun x => x.1 == v) with
      | none =>
          left
          simp [cseInstrStep, substInstr, hfind, substV,
            Std.HashMap.getD_eq_getD_getElem?, hdnone]
          exact Or.inl (by simp [Instr.defs])
      | some a =>
          obtain ⟨v0, d0⟩ := a
          right
          have hm : (v0, d0) ∈ tab.consts := List.mem_of_find?_eq_some hfind
          have hd0mem : d0 ∈ cseTabVals tab := by
            exact List.mem_append_right _ (List.mem_map.mpr ⟨(v0, d0), hm, rfl⟩)
          simpa [cseInstrStep, substInstr, hfind, substV,
            Std.HashMap.getD_eq_getD_getElem?, Std.HashMap.getElem?_insert] using hd0mem
  | op ds yop args =>
      cases ds with
      | nil => simp [Instr.defs] at hd
      | cons d' rest =>
          cases rest with
          | nil =>
              simp only [Instr.defs, List.mem_singleton] at hd
              subst d'
              by_cases hp : pureOp yop = true
              · cases hfind : tab.ops.find? (fun x => x.1 == (yop, substVs σ args)) with
                | none =>
                    left
                    by_cases hg : (substVs σ args).all (fun a =>
                        defined.contains a || !blockDefs.contains a) = true
                    · simp [cseInstrStep, substInstr, hp, hfind, hg, substV,
                        Std.HashMap.getD_eq_getD_getElem?, hdnone, Instr.defs]
                    · simp [cseInstrStep, substInstr, hp, hfind, hg, substV,
                        Std.HashMap.getD_eq_getD_getElem?, hdnone, Instr.defs]
                | some a =>
                    obtain ⟨key, d0⟩ := a
                    have hm : (key, d0) ∈ tab.ops := List.mem_of_find?_eq_some hfind
                    have hd0mem : d0 ∈ cseTabVals tab :=
                      List.mem_append_left _ (List.mem_map.mpr ⟨(key, d0), hm, rfl⟩)
                    by_cases hu : used.contains d = true
                    · left
                      simp [cseInstrStep, substInstr, hp, hfind, hu, substV,
                        Std.HashMap.getD_eq_getD_getElem?, hdnone]
                      exact Or.inl (by simp [Instr.defs])
                    · right
                      simpa [cseInstrStep, substInstr, hp, hfind, hu, substV,
                        Std.HashMap.getD_eq_getD_getElem?,
                        Std.HashMap.getElem?_insert] using hd0mem
              · left
                simp [cseInstrStep, substInstr, hp, substV,
                  Std.HashMap.getD_eq_getD_getElem?, hdnone]
                exact Or.inl (by simp [Instr.defs])
          | cons e es =>
              left
              simp only [Instr.defs] at hd
              simp [cseInstrStep, substInstr, substV,
                Std.HashMap.getD_eq_getD_getElem?, hdnone]
              exact Or.inl (by simpa [Instr.defs] using hd)
  | call ds fid args =>
      left
      simp only [Instr.defs] at hd
      simp [cseInstrStep, substInstr, substV,
        Std.HashMap.getD_eq_getD_getElem?, hdnone]
      exact Or.inl (by simpa [Instr.defs] using hd)

theorem cseInstrFold_acc_sublist (l : List Instr) (acc : List Instr)
    (tab : CseTab) (used : Std.HashSet ValId) (σ : Subst)
    (defined blockDefs : Std.HashSet ValId) :
    acc.Sublist
      (l.foldl (fun s i => cseInstrStep i s)
        ⟨acc, tab, used, σ, defined, blockDefs⟩).1 := by
  induction l generalizing acc tab used σ defined blockDefs with
  | nil => exact List.Sublist.refl _
  | cons i is ih =>
      rw [List.foldl_cons]
      exact (cseInstrStep_acc_sublist (i := i)).trans
        (ih _ _ _ _ _ _)

theorem cseInstrFold_tabVals (l : List Instr) (acc : List Instr)
    (tab : CseTab) (used : Std.HashSet ValId) (σ : Subst)
    (defined blockDefs : Std.HashSet ValId) {x : ValId}
    (hx : x ∈ cseTabVals
      (l.foldl (fun s i => cseInstrStep i s)
        ⟨acc, tab, used, σ, defined, blockDefs⟩).2.1) :
    x ∈ cseTabVals tab ∨
      x ∈ (l.foldl (fun s i => cseInstrStep i s)
        ⟨acc, tab, used, σ, defined, blockDefs⟩).1.flatMap Instr.defs := by
  induction l generalizing acc tab used σ defined blockDefs with
  | nil => exact Or.inl hx
  | cons i is ih =>
      rw [List.foldl_cons] at hx ⊢
      let s1 := cseInstrStep i ⟨acc, tab, used, σ, defined, blockDefs⟩
      rcases ih s1.1 s1.2.1 s1.2.2.1 s1.2.2.2.1
          s1.2.2.2.2.1 s1.2.2.2.2.2 hx with htab | hout
      · rcases cseInstrStep_tabVals htab with hold | hnew
        · exact Or.inl hold
        · exact Or.inr
            (((cseInstrFold_acc_sublist is s1.1 s1.2.1 s1.2.2.1
              s1.2.2.2.1 s1.2.2.2.2.1 s1.2.2.2.2.2).flatMap _).subset hnew)
      · exact Or.inr hout

theorem cseInstrFold_defs_resolve {f : Func} {b : Block}
    (hb : b ∈ f.blocks.toList) {seen : List ValId} {tab : CseTab} {σ : Subst}
    (hinv : CSEInv f seen tab σ) (l : List Instr)
    (hmem : ∀ i ∈ l, i ∈ b.instrs)
    (hnd : (seen ++ l.flatMap Instr.defs).Nodup) (acc : List Instr)
    (used defined blockDefs : Std.HashSet ValId) {d : ValId}
    (hd : d ∈ l.flatMap Instr.defs) :
    let r := l.foldl (fun s i => cseInstrStep i s)
      ⟨acc, tab, used, σ, defined, blockDefs⟩
    substV r.2.2.2.1 d ∈ r.1.flatMap Instr.defs ∨
      substV r.2.2.2.1 d ∈ cseTabVals tab := by
  induction l generalizing seen tab σ acc used defined blockDefs with
  | nil => simp at hd
  | cons i is ih =>
      simp only [List.flatMap_cons, List.mem_append] at hd
      have hprefix : (seen ++ i.defs).Nodup := by
        apply List.Nodup.of_append_left (l₂ := is.flatMap Instr.defs)
        simpa [List.append_assoc] using hnd
      have hone := cseInstrStep_inv hb (used := used) (defined := defined)
        (blockDefs := blockDefs) hinv i
        (hmem i (by simp)) hprefix
      have hstate := cseInstrStep_state i acc tab used σ defined blockDefs
      let s1 := cseInstrStep i ⟨acc, tab, used, σ, defined, blockDefs⟩
      have hinv1 : CSEInv f (seen ++ i.defs) s1.2.1 s1.2.2.2.1 := by
        rw [hstate]
        exact hone.1
      have htail : ((seen ++ i.defs) ++ is.flatMap Instr.defs).Nodup := by
        simpa [List.append_assoc] using hnd
      have hstable := cseInstrFold_stable hb hinv1 is
        (fun j hj => hmem j (by simp [hj])) htail s1.1 s1.2.2.1
        s1.2.2.2.2.1 s1.2.2.2.2.2
      rw [List.foldl_cons]
      dsimp only
      rcases hd with hd | hd
      · have hnow := cseInstrStep_defs_resolve hinv hprefix hd
          (acc := acc) (used := used) (defined := defined) (blockDefs := blockDefs)
        have hsubst : substV
            (is.foldl (fun s i => cseInstrStep i s) s1).2.2.2.1 d =
              substV s1.2.2.2.1 d := by
          simp only [substV, Std.HashMap.getD_eq_getD_getElem?]
          rw [hstable d (List.mem_append_right _ hd)]
        rw [hsubst]
        rcases hnow with hout | htab
        · exact Or.inl
            (((cseInstrFold_acc_sublist is s1.1 s1.2.1 s1.2.2.1
              s1.2.2.2.1 s1.2.2.2.2.1 s1.2.2.2.2.2).flatMap _).subset hout)
        · exact Or.inr htab
      · have hrest := ih hinv1 (fun j hj => hmem j (by simp [hj])) htail
          s1.1 s1.2.2.1 s1.2.2.2.2.1 s1.2.2.2.2.2 hd
        rcases hrest with hout | htab1
        · exact Or.inl hout
        · rcases cseInstrStep_tabVals htab1 with htab | hnew
          · exact Or.inr htab
          · exact Or.inl
              (((cseInstrFold_acc_sublist is s1.1 s1.2.1 s1.2.2.1
                s1.2.2.2.1 s1.2.2.2.2.1 s1.2.2.2.2.2).flatMap _).subset hnew)

theorem cseInstrFold_origin {f : Func} {b : Block}
    (hb : b ∈ f.blocks.toList) {seen : List ValId} {tab : CseTab} {σ : Subst}
    (hinv : CSEInv f seen tab σ) (l : List Instr)
    (hmem : ∀ i ∈ l, i ∈ b.instrs)
    (hnd : (seen ++ l.flatMap Instr.defs).Nodup) (acc : List Instr)
    (used defined blockDefs : Std.HashSet ValId)
    {τ : Subst}
    (hext : SubstExt
      (l.foldl (fun s i => cseInstrStep i s)
        ⟨acc, tab, used, σ, defined, blockDefs⟩).2.2.2.1 τ)
    (hrange : RangeFree τ) {j : Instr}
    (hj : j ∈ (l.foldl (fun s i => cseInstrStep i s)
      ⟨acc, tab, used, σ, defined, blockDefs⟩).1) :
    j ∈ acc ∨ ∃ i ∈ l, substInstr τ j = substInstr τ i := by
  induction l generalizing seen tab σ acc used defined blockDefs with
  | nil => exact Or.inl hj
  | cons i is ih =>
      have hprefix : (seen ++ i.defs).Nodup := by
        apply List.Nodup.of_append_left (l₂ := is.flatMap Instr.defs)
        simpa [List.append_assoc] using hnd
      have hone := cseInstrStep_inv hb (used := used) (defined := defined)
        (blockDefs := blockDefs) hinv i
        (hmem i (by simp)) hprefix
      have hstate := cseInstrStep_state i acc tab used σ defined blockDefs
      let s1 := cseInstrStep i ⟨acc, tab, used, σ, defined, blockDefs⟩
      have hinv1 : CSEInv f (seen ++ i.defs) s1.2.1 s1.2.2.2.1 := by
        rw [hstate]
        exact hone.1
      have htail : ((seen ++ i.defs) ++ is.flatMap Instr.defs).Nodup := by
        simpa [List.append_assoc] using hnd
      have hfoldInv := cseInstrFold_inv hb hinv1 is
        (fun k hk => hmem k (by simp [hk])) htail s1.1 s1.2.2.1
        s1.2.2.2.2.1 s1.2.2.2.2.2
      rw [List.foldl_cons] at hext hj
      rcases ih hinv1 (fun k hk => hmem k (by simp [hk])) htail s1.1
          s1.2.2.1 s1.2.2.2.2.1 s1.2.2.2.2.2 hext hj with
        hj1 | ⟨k, hk, heq⟩
      · rcases cseInstrStep_out (i := i) (acc := acc) (tab := tab)
          (used := used) (σ := σ) with
          hout | hout
        · exact Or.inl (hout ▸ hj1)
        · rw [hout] at hj1
          rcases List.mem_cons.mp hj1 with rfl | hjacc
          · right
            refine ⟨i, by simp, ?_⟩
            apply substInstr_absorb
            have honeExt : SubstExt σ s1.2.2.2.1 := by
              rw [hstate]
              exact hone.2
            have htailExt : SubstExt s1.2.2.2.1 τ :=
              SubstExt.trans (σ := s1.2.2.2.1)
                (τ := (is.foldl (fun s i => cseInstrStep i s) s1).2.2.2.1)
                (υ := τ) hfoldInv.2 hext
            intro x y hxy
            exact htailExt (honeExt hxy)
            exact hrange
          · exact Or.inl hjacc
      · exact Or.inr ⟨k, by simp [hk], heq⟩

theorem csePrefix_next_block (f : Func) (i : Nat) :
    (csePrefix f (i + 1)).1[i]? = some (cseBlockOut f i) := by
  rw [csePrefix_succ]
  simp only [cseBlockStep, cseBlockOut]
  rw [Array.getElem?_push]
  simp [csePrefix_blocks_size]

theorem cseFinal_raw_block {f : Func} {i : BlockId} (hi : i < f.blocks.size) :
    (csePrefix f f.blocks.size).1[i]? = some (cseBlockOut f i) := by
  have hn : f.blocks.size = (i + 1) + (f.blocks.size - (i + 1)) :=
    (Nat.add_sub_of_le (Nat.succ_le_of_lt hi)).symm
  rw [hn, csePrefix]
  rw [← List.range'_append_1, List.foldl_append]
  apply cseOuter_fold_get_old
  simpa [csePrefix] using csePrefix_next_block f i

theorem cse_block_get {f : Func} {i : BlockId} {b : Block}
    (h : f.blocks[i]? = some b) :
    (cse f).blocks[i]? = some
      (substBlock (csePrefix f f.blocks.size).2.2 (cseBlockOut f i)) := by
  have hi : i < f.blocks.size := (Array.getElem?_eq_some_iff.mp h).1
  rw [cse_eq]
  change ((substFunc (csePrefix f f.blocks.size).2.2
    { f with blocks := (csePrefix f f.blocks.size).1 }).blocks[i]?) = _
  simp only [substFunc, Array.getElem?_map]
  rw [cseFinal_raw_block hi]
  rfl

@[simp] theorem cse_blocks_size (f : Func) : (cse f).blocks.size = f.blocks.size := by
  rw [cse_eq]
  simp only [substFunc, Array.size_map]
  simpa [csePrefix] using csePrefix_blocks_size f f.blocks.size

def cseAvail (f : Func) (i : BlockId) : List ValId :=
  cseTabVals (cseEntryTab f (inEdgeSources f) (csePrefix f i).2.1 i)

def cseBlockTabOut (f : Func) (i : BlockId) : CseTab :=
  let b := f.blocks[i]!
  let st := csePrefix f i
  let tab := cseEntryTab f (inEdgeSources f) st.2.1 i
  (b.instrs.foldl (fun s ins => cseInstrStep ins s)
    ⟨[], tab, ∅, st.2.2, ∅, cseBlockDefs b⟩).2.1

theorem csePrefix_table_next {f : Func} (hnd : f.allDefs.Nodup)
    {i : BlockId} (hi : i < f.blocks.size) :
    (csePrefix f (i + 1)).2.1[i]! = cseBlockTabOut f i := by
  have hpre := csePrefixInv hnd i (Nat.le_of_lt hi)
  rw [csePrefix_succ]
  simp only [cseBlockStep, cseBlockTabOut]
  have hi0 : i < (csePrefix f i).2.1.size := by rw [hpre.2.1]; exact hi
  have hi1 : i < ((csePrefix f i).2.1.setIfInBounds i
      ((f.blocks[i]!.instrs.foldl (fun s ins => cseInstrStep ins s)
        ⟨[], cseEntryTab f (inEdgeSources f) (csePrefix f i).2.1 i,
          ∅, (csePrefix f i).2.2, ∅, cseBlockDefs f.blocks[i]!⟩).2.1)).size := by simpa
  rw [getElem!_eq_getElem hi1, Array.getElem_setIfInBounds_self]

theorem cseBlockTabOut_sound {f : Func} (hnd : f.allDefs.Nodup)
    {i : BlockId} (hi : i < f.blocks.size) :
    CseTabPosSound f (csePrefix f f.blocks.size).2.2 (cseBlockTabOut f i) := by
  rw [← csePrefix_table_next hnd hi]
  exact (csePrefixPosInv hnd (i + 1) (Nat.succ_le_of_lt hi)).2 i (by omega)

theorem csePrefix_table_to {f : Func} (hnd : f.allDefs.Nodup)
    {p n : BlockId} (hp : p < n) (hn : n ≤ f.blocks.size) :
    (csePrefix f n).2.1[p]! = cseBlockTabOut f p := by
  induction n generalizing p with
  | zero => exact (Nat.not_lt_zero p hp).elim
  | succ n ih =>
      by_cases hpn : p = n
      · subst p
        exact csePrefix_table_next hnd (Nat.lt_of_succ_le hn)
      · have hple : p ≤ n := Nat.le_of_lt_succ hp
        have hp' : p < n := Nat.lt_of_le_of_ne hple hpn
        have hn' : n ≤ f.blocks.size := Nat.le_trans (Nat.le_succ n) hn
        have hold := ih hp' hn'
        have hpre := csePrefixInv hnd n hn'
        rw [show Nat.succ n = n + 1 from rfl, csePrefix_succ]
        simp only [cseBlockStep]
        have hp0 : p < (csePrefix f n).2.1.size := by
          rw [hpre.2.1]
          exact Nat.lt_of_lt_of_le hp' hn'
        have hp1 : p < ((csePrefix f n).2.1.setIfInBounds n
            ((f.blocks[n]!.instrs.foldl (fun s ins => cseInstrStep ins s)
              ⟨[], cseEntryTab f (inEdgeSources f) (csePrefix f n).2.1 n,
                ∅, (csePrefix f n).2.2, ∅, cseBlockDefs f.blocks[n]!⟩).2.1)).size := by simpa
        rw [getElem!_eq_getElem hp1,
          Array.getElem_setIfInBounds_ne hp0 (Ne.symm hpn),
          ← getElem!_eq_getElem hp0]
        exact hold

theorem cseBlock_spec {f : Func} (hnd : f.allDefs.Nodup)
    {i : BlockId} {b : Block} (hb : f.blocks[i]? = some b) :
    let τ := (csePrefix f f.blocks.size).2.2
    let b' := substBlock τ (cseBlockOut f i)
    (∀ x ∈ ToAsm.blockUses b', ∃ y ∈ ToAsm.blockUses b, substV τ y = x)
      ∧ (∀ y ∈ ToAsm.blockDefs b,
          substV τ y ∈ ToAsm.blockDefs b' ∨ substV τ y ∈ cseAvail f i)
      ∧ (∀ e ∈ b'.term.edges, ∃ e0 ∈ b.term.edges, e0.target = e.target)
      ∧ (∀ x ∈ cseTabVals (cseBlockTabOut f i),
          x ∈ ToAsm.blockDefs b' ∨ x ∈ cseAvail f i) := by
  let τ := (csePrefix f f.blocks.size).2.2
  let st := csePrefix f i
  let tab := cseEntryTab f (inEdgeSources f) st.2.1 i
  let r := b.instrs.foldl (fun s ins => cseInstrStep ins s)
    ⟨[], tab, ∅, st.2.2, ∅, cseBlockDefs b⟩
  have hi : i < f.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  have hbang : f.blocks[i]! = b := by
    rw [getElem!_eq_getElem hi]
    exact (Array.getElem?_eq_some_iff.mp hb).2
  have hbmem : b ∈ f.blocks.toList := by
    exact List.mem_iff_getElem.mpr ⟨i, by simpa using hi,
      by simpa using (Array.getElem?_eq_some_iff.mp hb).2⟩
  have hpre := csePrefixInv hnd i (Nat.le_of_lt hi)
  have htab : CSEInv f (cseSeen f i) tab st.2.2 := cseEntryTab_inv hpre
  have hseen : cseSeen f (i + 1) = cseSeen f i ++ b.instrs.flatMap Instr.defs :=
    cseSeen_succ hb
  have hndBlock : (cseSeen f i ++ b.instrs.flatMap Instr.defs).Nodup := by
    rw [← hseen]
    exact (instrDefs_nodup hnd).sublist (cseSeen_sublist f (i + 1))
  have hrInv := cseInstrFold_inv hbmem htab b.instrs (fun ins hins => hins)
    hndBlock [] ∅ ∅ (cseBlockDefs b)
  have hrPrefix : (csePrefix f (i + 1)).2.2 = r.2.2.2.1 := by
    rw [csePrefix_succ]
    simp only [cseBlockStep]
    rw [hbang]
  have hext : SubstExt r.2.2.2.1 τ := by
    rw [← hrPrefix]
    exact csePrefix_ext_to hnd (Nat.succ_le_of_lt hi) (Nat.le_refl _)
  have hfinalInv := (csePrefixInv hnd f.blocks.size (Nat.le_refl _)).1
  have hrange : RangeFree τ := hfinalInv.2.2.1
  have hstable : SubstStable (cseSeen f (i + 1)) r.2.2.2.1 τ := by
    rw [← hrPrefix]
    exact csePrefix_stable_to hnd (Nat.succ_le_of_lt hi) (Nat.le_refl _)
  have hraw : cseBlockOut f i = { b with instrs := r.1.reverse } := by
    simp [cseBlockOut, hbang, st, tab, r]
  have param_fixed {p : ValId} (hp : p ∈ b.params) : substV τ p = p := by
    have hpnone : τ[p]? = none := by
      by_contra hn
      obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hn
      have hpseen := (hfinalInv.2.2.2.1 hq).1
      unfold cseSeen at hpseen
      have htake : f.blocks.toList.take f.blocks.size = f.blocks.toList := by simp
      rw [htake] at hpseen
      simp only [List.mem_flatMap] at hpseen
      obtain ⟨b2, hb2, ins, hins, hpdef⟩ := hpseen
      exact param_not_instr_def hnd hbmem hb2 hins hp hpdef
    simp [substV, Std.HashMap.getD_eq_getD_getElem?, hpnone]
  dsimp only
  rw [hraw]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [ToAsm.mem_blockUses] at hx
    rcases hx with hx | hx
    · simp only [substBlock] at hx
      obtain ⟨j, hj, hxj⟩ := List.mem_flatMap.mp hx
      obtain ⟨j0, hj0, hjeq⟩ := List.mem_map.mp hj
      have hjr : j0 ∈ r.1 := by simpa using hj0
      have hxj0 : x ∈ (substInstr τ j0).uses := by rw [hjeq]; exact hxj
      have horigin := cseInstrFold_origin hbmem htab b.instrs (fun ins hins => hins)
        hndBlock [] ∅ ∅ (cseBlockDefs b) hext hrange hjr
      rcases horigin with hjnil | ⟨ins, hins, heq⟩
      · simp at hjnil
      · have hxins : x ∈ (substInstr τ ins).uses := by
          rw [← heq]
          exact hxj0
        obtain ⟨y, hy, hxy⟩ := substInstr_use hxins
        exact ⟨y, ToAsm.mem_blockUses.mpr
          (Or.inl (List.mem_flatMap.mpr ⟨ins, hins, hy⟩)), hxy⟩
    · obtain ⟨y, hy, hxy⟩ := substTerm_use hx
      exact ⟨y, ToAsm.mem_blockUses.mpr (Or.inr hy), hxy⟩
  · intro y hy
    rw [ToAsm.mem_blockDefs] at hy
    rcases hy with hp | hd
    · left
      rw [param_fixed hp]
      exact ToAsm.mem_blockDefs.mpr (Or.inl hp)
    · obtain ⟨ins, hins, hyd⟩ := List.mem_flatMap.mp hd
      have hres := cseInstrFold_defs_resolve hbmem htab b.instrs
        (fun ins hins => hins) hndBlock [] ∅ ∅ (cseBlockDefs b)
          (List.mem_flatMap.mpr ⟨ins, hins, hyd⟩)
      have hymem : y ∈ cseSeen f (i + 1) := by
        rw [hseen]
        exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨ins, hins, hyd⟩)
      have hsubst : substV τ y = substV r.2.2.2.1 y := by
        simp only [substV, Std.HashMap.getD_eq_getD_getElem?]
        rw [hstable y hymem]
      rw [hsubst]
      rcases hres with hout | hav
      · left
        apply ToAsm.mem_blockDefs.mpr
        right
        obtain ⟨j, hj, hjd⟩ := List.mem_flatMap.mp hout
        refine List.mem_flatMap.mpr ⟨substInstr τ j, ?_, ?_⟩
        · exact List.mem_map.mpr ⟨j, by simpa using hj, rfl⟩
        · simpa using hjd
      · exact Or.inr hav
  · intro e he
    exact substTerm_edge he
  · intro x hx
    have htabOut : cseBlockTabOut f i = r.2.1 := by
      simp [cseBlockTabOut, hbang, st, tab, r]
    rw [htabOut] at hx
    rcases cseInstrFold_tabVals b.instrs [] tab ∅ st.2.2 ∅
        (cseBlockDefs b) hx with hav | hout
    · exact Or.inr hav
    · left
      apply ToAsm.mem_blockDefs.mpr
      right
      obtain ⟨j, hj, hjd⟩ := List.mem_flatMap.mp hout
      refine List.mem_flatMap.mpr ⟨substInstr τ j, ?_, ?_⟩
      · exact List.mem_map.mpr ⟨j, by simpa using hj, rfl⟩
      · simpa using hjd

theorem cseAvail_entry (f : Func) : cseAvail f f.entry = [] := by
  simp [cseAvail, cseEntryTab, cseTabVals]

theorem cseAvail_succ {f : Func} (hnd : f.allDefs.Nodup)
    (hwf : f.wfCheck n = true) {i : BlockId} {b : Block}
    (hb : f.blocks[i]? = some b) {e : Edge} (he : e ∈ b.term.edges)
    {x : ValId} (hx : x ∈ cseAvail f e.target) :
    let τ := (csePrefix f f.blocks.size).2.2
    let b' := substBlock τ (cseBlockOut f i)
    x ∈ ToAsm.blockDefs b' ∨ x ∈ cseAvail f i := by
  obtain ⟨tb, htb, -⟩ := wfCheck_edge_arity hwf (b := b) (by
    exact List.mem_iff_getElem.mpr ⟨i, by
      simpa using (Array.getElem?_eq_some_iff.mp hb).1,
      by simpa using (Array.getElem?_eq_some_iff.mp hb).2⟩) he
  have ht : e.target < f.blocks.size := (Array.getElem?_eq_some_iff.mp htb).1
  unfold cseAvail at hx
  rw [cseEntryTab] at hx
  split at hx
  · simp [cseTabVals] at hx
  · cases hs : (inEdgeSources f)[e.target]! with
    | nil => simp [hs, cseTabVals] at hx
    | cons p ps =>
        cases ps with
        | cons q qs => simp [hs, cseTabVals] at hx
        | nil =>
            by_cases hp : p < e.target
            · simp only [hs, hp, if_true] at hx
              have hip : i = p := inEdgeSources_single_eq hb he ht hs
              subst p
              rw [csePrefix_table_to hnd hp (Nat.le_of_lt ht)] at hx
              exact (cseBlock_spec hnd hb).2.2.2 x (cseTabVals_inheritTab hx)
            · simp [hs, hp, cseTabVals] at hx

end Passes

end YulEvmCompiler.SsaCfg
