import YulEvmCompiler.SsaCfg.Implementation.OfYulSound.Leaves
set_option warningAsError true

/-!
# YulEvmCompiler.SsaCfg.Implementation.OfYulSound.FuncTable

Function environments and the top-level build inversion.

`FuncOK`/`FEnvOK`, the `buildMain`/`ofBlock` inversion lemmas,
`FuncTableComplete` and its consumers, and the `allocScope` bridge from the
hoisted function names to the motive's inputs.
-/

namespace YulEvmCompiler.SsaCfg
open YulSemantics (Ident Literal Expr Stmt VEnv Outcome)
open YulSemantics.EVM (U256 EvmState Op builtinWithExternal evmWithExternal)

section Semantics
variable [model : ExternalModel]
local notation "yulD" => evmWithExternal model.calls model.creates

/-! ## Function environments

`FMap` mirrors `FunEnv` scope by scope, exactly like `SimAsm.FEnvOK` mirrors it
for the classic backend. Unlike `lookupF`, `FMap.get` does not hand back the
scope tail visible at the definition site, so the correspondence lemma
existentially produces it. -/

/-- What the construction guarantees about the slot a function name resolves
to: the slot holds the `trFunc` translation of that source declaration against
the scopes visible at its definition site, and the nested slots that
translation filled survived into the finished program. -/
def FuncOK (P : Prog) (fenv : FMap) (decl : YulSemantics.FDecl yulD)
    (fid : FuncId) : Prop :=
  ∃ (g : Func) (s₀ s₁ : BState),
    P.funcs[fid]? = some g
    ∧ trFunc fenv decl.params decl.rets decl.body s₀ = some (g, s₁)
    ∧ (∀ i : FuncId, s₁.funcs[i]? = some none → i < s₀.funcs.size)
    ∧ ∀ (i : Nat) (g' : Func), s₁.funcs[i]? = some (some g') → P.funcs[i]? = some g'

/-- Scopewise agreement between the semantic function environment and the
construction's. Each function's `FMap` is its own scope outward — exactly what
`lookupFun` returns as the callee environment. -/
inductive FEnvOK (P : Prog) : YulSemantics.FunEnv yulD → FMap → Prop
  | nil : FEnvOK P [] []
  | cons {scope : YulSemantics.FScope yulD} {mp : List (Ident × FuncId)}
      {rest : YulSemantics.FunEnv yulD} {restM : FMap} :
      List.Forall₂ (fun (p : Ident × YulSemantics.FDecl yulD) (q : Ident × FuncId) =>
        p.1 = q.1 ∧ FuncOK (model := model) P (mp :: restM) p.2 q.2) scope mp →
      FEnvOK P rest restM →
      FEnvOK P (scope :: rest) (mp :: restM)

/-- The two scope searches agree, entry by entry. -/
private theorem find?_agree {P : Prog} {fenv : FMap} {x : Ident} :
    ∀ {scope : YulSemantics.FScope yulD} {mp : List (Ident × FuncId)},
      List.Forall₂ (fun (p : Ident × YulSemantics.FDecl yulD) (q : Ident × FuncId) =>
        p.1 = q.1 ∧ FuncOK (model := model) P fenv p.2 q.2) scope mp →
      (scope.find? (fun p => p.1 = x) = none ∧ mp.find? (fun q => q.1 = x) = none)
      ∨ (∃ p q, scope.find? (fun p => p.1 = x) = some p
          ∧ mp.find? (fun q => q.1 = x) = some q
          ∧ FuncOK (model := model) P fenv p.2 q.2) := by
  intro scope mp h
  induction h with
  | nil => exact Or.inl ⟨rfl, rfl⟩
  | @cons p q scope' mp' hpq _ ih =>
    obtain ⟨hname, hok⟩ := hpq
    by_cases hf : p.1 = x
    · refine Or.inr ⟨p, q, ?_, ?_, hok⟩
      · rw [List.find?_cons_of_pos (by simpa using hf)]
      · rw [List.find?_cons_of_pos (by simp [← hname, hf])]
    · rw [show scope'.find? (fun p => p.1 = x)
          = (p :: scope').find? (fun p => p.1 = x) from by
        rw [List.find?_cons_of_neg (by simpa using hf)]] at ih
      rw [show mp'.find? (fun q => q.1 = x)
          = (q :: mp').find? (fun q => q.1 = x) from by
        rw [List.find?_cons_of_neg (by simp [← hname, hf])]] at ih
      exact ih

/-- Successful lookups on corresponding environments correspond: the source
resolves `x` to `decl` with callee environment `cenv` exactly when the
construction resolves it to a slot translated against a `FMap` mirroring
`cenv`. -/
theorem FMap.get_ok {P : Prog} {funs : YulSemantics.FunEnv yulD} {fenv : FMap}
    (h : FEnvOK (model := model) P funs fenv) {x : Ident}
    {decl : YulSemantics.FDecl yulD} {cenv : YulSemantics.FunEnv yulD}
    (hlk : YulSemantics.lookupFun funs x = some (decl, cenv)) :
    ∃ (fid : FuncId) (fenv' : FMap),
      FMap.get fenv x = some fid ∧ FuncOK (model := model) P fenv' decl fid
        ∧ FEnvOK (model := model) P cenv fenv' := by
  induction h with
  | nil => exact absurd hlk (by simp [YulSemantics.lookupFun])
  | @cons scope mp rest restM hscope hrest ih =>
    rw [YulSemantics.lookupFun] at hlk
    rw [FMap.get]
    rcases find?_agree hscope (x := x) with ⟨hn1, hn2⟩ | ⟨p, q, hs1, hs2, hok⟩
    · rw [hn1] at hlk
      rw [hn2]
      exact ih hlk
    · rw [hs1] at hlk
      rw [hs2]
      obtain ⟨rfl, rfl⟩ : p.2 = decl ∧ scope :: rest = cenv := by
        refine ⟨?_, ?_⟩ <;> · injection hlk with h'; cases h'; rfl
      exact ⟨q.2, mp :: restM, rfl, hok, .cons hscope hrest⟩

/-! ## Inverting the top-level build -/

/-- The builder state the top level hands to `trScope`: block `0` reserved and
current, nothing else allocated. -/
def initBState : BState :=
  { fn := { blocks := #[⟨[], [], .ret []⟩], curId := 0, cur := [], nextVal := 0 },
    funcs := #[] }

/-- The top-level build action (the `let build := …` of `ofBlockRaw`). -/
def buildMain (prog : List (Stmt Op)) : M Func := do
  let entry ← newBlock []
  moveTo entry
  let renv ← trScope [] [] none none prog
  if let some _ := renv then sealCur (.ret [])
  let done ← getFn
  pure { params := [], nrets := 0, entry := entry, blocks := done.blocks }

omit model in
/-- The top-level build, decomposed: the whole program is one `trScope` over
`prog` from `initBState`, followed by the fall-through `ret []` seal when
control was not diverted. -/
theorem buildMain_inv {prog : List (Stmt Op)} {main : Func} {s : BState}
    (h : buildMain prog {} = some (main, s)) :
    ∃ (renv : Option VMap) (s₁ : BState),
      trScope [] [] none none prog initBState = some (renv, s₁)
      ∧ main.params = [] ∧ main.nrets = 0 ∧ main.entry = 0
      ∧ s.funcs = s₁.funcs
      ∧ (match renv with
          | some _ => ∃ b, s₁.fn.blocks[s₁.fn.curId]? = some b
              ∧ main.blocks
                  = s₁.fn.blocks.set! s₁.fn.curId ⟨b.params, s₁.fn.cur.reverse, .ret []⟩
          | none => main.blocks = s₁.fn.blocks) := by
  rw [buildMain] at h
  obtain ⟨entry, sA, h1, h⟩ := M.bind_inv h
  rw [M.newBlock_apply] at h1
  obtain ⟨rfl, rfl⟩ : entry = 0 ∧ sA = initBState := by
    have h' := Option.some.inj h1
    exact ⟨(congrArg Prod.fst h').symm, (congrArg Prod.snd h').symm⟩
  obtain ⟨u, sB, h2, h⟩ := M.bind_inv h
  rw [M.moveTo_apply] at h2
  obtain rfl : sB = initBState := (congrArg Prod.snd (Option.some.inj h2)).symm
  obtain ⟨renv, s₁, h3, h⟩ := M.bind_inv h
  refine ⟨renv, s₁, h3, ?_⟩
  cases renv with
  | none =>
    -- the `if let` takes its `pure ()` branch, and `getFn`/`pure` are total, so
    -- the whole tail computes
    have h' : some ((⟨[], 0, 0, s₁.fn.blocks⟩ : Func), s₁) = some (main, s) := h
    have he := Option.some.inj h'
    obtain rfl : main = (⟨[], 0, 0, s₁.fn.blocks⟩ : Func) :=
      (congrArg Prod.fst he).symm
    obtain rfl : s = s₁ := (congrArg Prod.snd he).symm
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | some e =>
    obtain ⟨u', s₂, h4, h⟩ := M.bind_inv h
    obtain ⟨b, hb, rfl⟩ := M.sealCur_inv h4
    obtain ⟨fnv, s₃, h5, h⟩ := M.bind_inv h
    rw [M.getFn_apply] at h5
    obtain ⟨rfl, rfl⟩ :
        fnv = { s₁.fn with
                  blocks := s₁.fn.blocks.set! s₁.fn.curId
                    ⟨b.params, s₁.fn.cur.reverse, .ret []⟩, cur := [] }
          ∧ s₃ = { s₁ with fn := { s₁.fn with
                  blocks := s₁.fn.blocks.set! s₁.fn.curId
                    ⟨b.params, s₁.fn.cur.reverse, .ret []⟩, cur := [] } } := by
      have h' := Option.some.inj h5
      exact ⟨(congrArg Prod.fst h').symm, (congrArg Prod.snd h').symm⟩
    obtain ⟨rfl, rfl⟩ := M.pure_inv h
    exact ⟨rfl, rfl, rfl, rfl, ⟨b, hb, rfl⟩⟩

omit model in
/-- The public entry point, inverted: `wfCheck` passed, and the build ran as
`buildMain_inv` describes with all function slots filled. -/
theorem ofBlock_inv {prog : List (Stmt Op)} {P : Prog}
    (hof : ofBlock prog = some P) :
    P.wfCheck = true ∧ ∃ (main : Func) (s : BState),
      buildMain prog {} = some (main, s)
      ∧ s.funcs.mapM id = some P.funcs ∧ P.main = main := by
  refine ⟨ofBlock_wfCheck hof, ?_⟩
  unfold ofBlock at hof
  rcases hraw : ofBlockRaw prog with _ | Q <;> rw [hraw] at hof
  · exact absurd hof (by simp)
  have hQ : Q = P := by
    by_cases hwf : Q.wfCheck
    · simp only [Option.bind_some, hwf, if_true] at hof; exact Option.some.inj hof
    · simp only [Option.bind_some, hwf, Bool.false_eq_true, if_false] at hof
      exact absurd hof (by simp)
  rw [hQ] at hraw
  unfold ofBlockRaw at hraw
  simp only [bind, Option.bind] at hraw
  split at hraw
  · exact absurd hraw (by simp)
  · rename_i p hp
    have hp' : buildMain prog {} = some p := hp
    dsimp only at hraw
    split at hraw
    · exact absurd hraw (by simp)
    · rename_i fs hfs
      obtain rfl : P = ⟨p.1, fs⟩ := (Option.some.inj hraw).symm
      exact ⟨p.1, p.2, hp', hfs, rfl⟩

omit model in
/-- Elementwise consequence of a successful whole-table `mapM id`: every slot
was filled, with the function the finished program records. -/
theorem funcs_mapM_getElem? {a : Array (Option Func)} {fs : Array Func}
    (h : a.mapM id = some fs) {i : Nat} {g : Func}
    (hi : a[i]? = some (some g)) : fs[i]? = some g := by
  have hlist : a.toList.mapM id = some fs.toList := by
    have := congrArg (Option.map Array.toList) h
    simpa [Array.mapM_eq_mapM_toList, Option.map_some] using this
  have : ∀ (l : List (Option Func)) (l' : List Func), l.mapM id = some l' →
      ∀ (j : Nat) (x : Func), l[j]? = some (some x) → l'[j]? = some x := by
    intro l
    induction l with
    | nil => intro l' hl j x hj; exact absurd hj (by simp)
    | cons o l ih =>
      intro l' hl j x hj
      rw [List.mapM_cons] at hl
      cases o with
      | none => exact absurd hl (by simp)
      | some y =>
        rcases ht : l.mapM id with _ | t <;> rw [ht] at hl
        · exact absurd hl (by simp)
        · obtain rfl : l' = y :: t := by simpa using hl.symm
          cases j with
          | zero => simpa using hj
          | succ j => simpa using ih t ht j x (by simpa using hj)
  have := this a.toList fs.toList hlist i g (by simpa using hi)
  simpa using this

omit model in
/-- Converse elementwise consequence of a successful whole-table `mapM id`:
every function recorded in the erased table came from the corresponding
filled builder slot. -/
theorem funcs_mapM_getElem?_rev {a : Array (Option Func)} {fs : Array Func}
    (h : a.mapM id = some fs) {i : Nat} {g : Func}
    (hi : fs[i]? = some g) : a[i]? = some (some g) := by
  have hlist : a.toList.mapM id = some fs.toList := by
    have hm := congrArg (Option.map Array.toList) h
    simpa [Array.mapM_eq_mapM_toList, Option.map_some] using hm
  have : ∀ (l : List (Option Func)) (l' : List Func), l.mapM id = some l' →
      ∀ (j : Nat) (x : Func), l'[j]? = some x → l[j]? = some (some x) := by
    intro l
    induction l with
    | nil =>
      intro l' hl j x hj
      obtain rfl : l' = [] := (Option.some.inj hl).symm
      exact absurd hj (by simp)
    | cons o l ih =>
      intro l' hl j x hj
      rw [List.mapM_cons] at hl
      cases o with
      | none => exact absurd hl (by simp)
      | some y =>
        rcases ht : l.mapM id with _ | t <;> rw [ht] at hl
        · exact absurd hl (by simp)
        · obtain rfl : l' = y :: t := by simpa using hl.symm
          cases j with
          | zero => simpa using hj
          | succ j => simpa using ih t ht j x (by simpa using hj)
  have hm := this a.toList fs.toList hlist i g (by simpa using hi)
  simpa using hm

/-- A builder function table is *complete for* `P` when every allocated slot
has been filled and erasing the `Option` layer gives exactly `P.funcs`.

This is deliberately a fact about one fixed, completed table rather than the
table of each intermediate builder state.  `allocScope` reserves all of a
scope's slots before its statement walk fills them, and `trFunc` may reserve
further slots while outer ones are still pending.  The construction simulation
therefore keeps the eventual completed table fixed across every recursive IH;
the hoist/call bridges only have to prove that their filled slots survive into
that table. -/
def FuncTableComplete (P : Prog) (done : Array (Option Func)) : Prop :=
  done.mapM id = some P.funcs

omit model in
theorem FuncTableComplete.get {P : Prog} {done : Array (Option Func)}
    (h : FuncTableComplete P done) {i : Nat} {g : Func}
    (hi : done[i]? = some (some g)) : P.funcs[i]? = some g :=
  funcs_mapM_getElem? h hi

omit model in
theorem FuncTableComplete.get_rev {P : Prog} {done : Array (Option Func)}
    (h : FuncTableComplete P done) {i : Nat} {g : Func}
    (hi : P.funcs[i]? = some g) : done[i]? = some (some g) :=
  funcs_mapM_getElem?_rev h hi

omit model in
/-- A completed table has no pending reservations, hence owns the empty
budget.  This is the top-level instantiation of the slot-ownership invariant. -/
theorem FuncTableComplete.owned_nil {P : Prog} {done : Array (Option Func)}
    (h : FuncTableComplete P done) : FOwned [] { fn := {}, funcs := done }
      { fn := {}, funcs := done } := by
  apply FOwned.rfl_of_no_pending
  intro i hi
  have hlist : done.toList.mapM id = some P.funcs.toList := by
    have hm := congrArg (Option.map Array.toList) h
    simpa [Array.mapM_eq_mapM_toList, Option.map_some] using hm
  have noNone : ∀ (l : List (Option Func)) (fs : List Func),
      l.mapM id = some fs → ∀ j : Nat, l[j]? ≠ some none := by
    intro l
    induction l with
    | nil => simp
    | cons x xs ih =>
      intro fs hm j
      rw [List.mapM_cons] at hm
      cases x with
      | none => simp at hm
      | some g =>
        cases ht : xs.mapM id with
        | none => rw [ht] at hm; simp at hm
        | some gs =>
          rw [ht] at hm
          obtain rfl : fs = g :: gs := by simpa using hm.symm
          cases j with
          | zero => simp
          | succ j => simpa using ih gs ht j
  exact noNone done.toList P.funcs.toList hlist i (by simpa using hi)

/-- Package the function-table half of `FuncOK` once the structural hoist walk
has shown that the translated function and every nested function it allocated
survive into the fixed completed table. -/
theorem FuncTableComplete.funcOK {P : Prog} {done : Array (Option Func)}
    (h : FuncTableComplete P done) {fenv : FMap}
    {decl : YulSemantics.FDecl yulD} {fid : FuncId} {g : Func}
    {s₀ s₁ : BState}
    (htr : trFunc fenv decl.params decl.rets decl.body s₀ = some (g, s₁))
    (hbudget : ∀ i : FuncId, s₁.funcs[i]? = some none → i < s₀.funcs.size)
    (hslot : done[fid]? = some (some g))
    (hnested : ∀ (i : Nat) (g' : Func),
      s₁.funcs[i]? = some (some g') → done[i]? = some (some g')) :
    FuncOK (model := model) P fenv decl fid :=
  ⟨g, s₀, s₁, h.get hslot, htr, hbudget,
    fun i g' hi => h.get (hnested i g' hi)⟩

/-- Content refinement is the local-to-final transport consumed by hoisted
scope construction: once the just-filled declaration slot and every nested
slot are present in a local builder table, `FContents` moves them to the one
completed table and `FuncTableComplete` erases the `Option` layer. -/
theorem FuncTableComplete.funcOK_of_contents {P : Prog}
    {done : Array (Option Func)} (h : FuncTableComplete P done)
    {fenv : FMap} {decl : YulSemantics.FDecl yulD} {fid : FuncId}
    {g : Func} {s₀ s₁ sLocal sDone : BState}
    (htr : trFunc fenv decl.params decl.rets decl.body s₀ = some (g, s₁))
    (hbudget : ∀ i : FuncId, s₁.funcs[i]? = some none → i < s₀.funcs.size)
    (hslot : sLocal.funcs[fid]? = some (some g))
    (hnested : ∀ (i : Nat) (g' : Func),
      s₁.funcs[i]? = some (some g') → sLocal.funcs[i]? = some (some g'))
    (href : FContents sLocal sDone) (hdone : sDone.funcs = done) :
    FuncOK (model := model) P fenv decl fid := by
  apply h.funcOK htr hbudget
  · rw [← hdone]
    exact href fid g hslot
  · intro i g' hi
    rw [← hdone]
    exact href i g' (hnested i g' hi)

omit model in
theorem stmtFuncIds_mem {fenv : FMap} {ss : List (Stmt Op)}
    {n : Ident} {ps rs : List Ident} {body : List (Stmt Op)}
    (hmem : Stmt.funDef n ps rs body ∈ ss) :
    (fenv.get n).toList ⊆ stmtFuncIds fenv ss := by
  induction ss with
  | nil => simp at hmem
  | cons st rest ih =>
    cases st with
    | funDef n' ps' rs' body' =>
      simp only [List.mem_cons] at hmem
      rcases hmem with heq | hmem
      · cases heq
        simp [stmtFuncIds]
      · exact fun i hi => by
          simp only [stmtFuncIds, List.mem_append]
          exact Or.inr (ih hmem hi)
    | block b | letDecl ps' e | assign ps' e | cond e b
    | forLoop b e post body' | «break» | «continue» | leave
    | switch e cases dflt | exprStmt e =>
      simp only [List.mem_cons] at hmem
      rcases hmem with heq | hmem
      · cases heq
      · simpa only [stmtFuncIds] using ih hmem

theorem stmtFuncIds_length_of_trStmts (fenv : FMap) (env : VMap)
    (lctx : Option LoopCtx) (rets : Option (List Ident)) (d : Bool) :
    ∀ (ss : List (Stmt Op)) (s s' : BState) (r : Option VMap),
      trStmts fenv env lctx rets d ss s = some (r, s') →
      (stmtFuncIds fenv ss).length = (YulSemantics.hoist yulD ss).length := by
  intro ss
  induction ss generalizing env d with
  | nil => intro s s' r _; rfl
  | cons st rest ih =>
    intro s s' r htr
    cases st with
    | funDef n ps rs body =>
      rw [trStmts] at htr
      obtain ⟨fid, s1, h1, htr⟩ := M.bind_inv htr
      obtain ⟨g, s2, h2, htr⟩ := M.bind_inv htr
      obtain ⟨u, s3, h3, htail⟩ := M.bind_inv htr
      obtain ⟨hget, -⟩ := M.liftO_inv h1
      have hh := congrArg Nat.succ (ih env d s3 s' r htail)
      simpa [stmtFuncIds, hget, YulSemantics.hoist, Nat.add_comm] using hh
    | block b | letDecl ps e | assign ps e | cond e b
    | forLoop b e post body | «break» | «continue» | leave
    | switch e cases dflt | exprStmt e =>
      simp only [stmtFuncIds, YulSemantics.hoist, List.filterMap_cons]
      rw [trStmts] at htr
      · split at htr
        · exact ih env true s s' r htr
        · obtain ⟨renv, s1, h1, h2⟩ := M.bind_inv htr
          cases renv with
          | none => exact ih env true s1 s' r h2
          | some env' => exact ih env' false s1 s' r h2
      · intro n ps rs body heq
        cases heq

theorem allocScope_length {ss : List (Stmt Op)} {s s' : BState}
    {scope : List (Ident × FuncId)} (h : allocScope ss s = some (scope, s')) :
    scope.length = (YulSemantics.hoist yulD ss).length := by
  rw [allocScope] at h
  have fold : ∀ (l : List (Stmt Op)) (acc : List (Ident × FuncId))
      (s0 s1 : BState) (out : List (Ident × FuncId)),
      (l.foldlM (init := acc) fun acc (st : Stmt Op) =>
        match st with
        | Stmt.funDef n _ _ _ => do
            let fid ← allocFunc
            pure (acc ++ [(n, fid)])
        | _ => pure acc) s0 = some (out, s1) →
      out.length = acc.length + (YulSemantics.hoist yulD l).length := by
    intro l
    induction l with
    | nil =>
      intro acc s0 s1 out hl
      obtain ⟨rfl, rfl⟩ := M.pure_inv hl
      simp [YulSemantics.hoist]
    | cons st rest ih =>
      intro acc s0 s1 out hl
      rw [List.foldlM_cons] at hl
      obtain ⟨acc', t, hst, hrest⟩ := M.bind_inv hl
      cases st with
      | funDef n ps rs body =>
        obtain ⟨fid, u, ha, hp⟩ := M.bind_inv hst
        obtain ⟨rfl, rfl⟩ := M.pure_inv hp
        have hh := ih (acc ++ [(n, fid)]) t s1 out hrest
        simp [YulSemantics.hoist] at *
        omega
      | block b | letDecl ps e | assign ps e | cond e b
      | forLoop b e post body | «break» | «continue» | leave
      | switch e cases dflt | exprStmt e =>
        obtain ⟨rfl, rfl⟩ := M.pure_inv hst
        simpa [YulSemantics.hoist] using ih _ _ _ _ hrest
  simpa using fold ss [] s s' scope h

theorem allocScope_forall2 {ss : List (Stmt Op)} {s s' : BState}
    {scope : List (Ident × FuncId)} (h : allocScope ss s = some (scope, s')) :
    List.Forall₂ (fun (p : Ident × YulSemantics.FDecl yulD)
      (q : Ident × FuncId) => p.1 = q.1)
      (YulSemantics.hoist yulD ss) scope := by
  rw [allocScope] at h
  have fold : ∀ (l : List (Stmt Op)) (acc : List (Ident × FuncId))
      (s0 s1 : BState) (out : List (Ident × FuncId)),
      (l.foldlM (init := acc) fun acc (st : Stmt Op) =>
        match st with
        | Stmt.funDef n _ _ _ => do
            let fid ← allocFunc
            pure (acc ++ [(n, fid)])
        | _ => pure acc) s0 = some (out, s1) →
      ∃ added, out = acc ++ added ∧
        List.Forall₂ (fun (p : Ident × YulSemantics.FDecl yulD)
          (q : Ident × FuncId) => p.1 = q.1)
          (YulSemantics.hoist yulD l) added := by
    intro l
    induction l with
    | nil =>
      intro acc s0 s1 out hl
      obtain ⟨rfl, rfl⟩ := M.pure_inv hl
      exact ⟨[], by simp [YulSemantics.hoist]⟩
    | cons st rest ih =>
      intro acc s0 s1 out hl
      rw [List.foldlM_cons] at hl
      obtain ⟨acc', t, hst, hrest⟩ := M.bind_inv hl
      cases st with
      | funDef n ps rs body =>
        obtain ⟨fid, u, ha, hp⟩ := M.bind_inv hst
        obtain ⟨rfl, rfl⟩ := M.pure_inv hp
        obtain ⟨added, hout, hrel⟩ := ih (acc ++ [(n, fid)]) t s1 out hrest
        refine ⟨(n, fid) :: added, ?_, ?_⟩
        · simpa [List.append_assoc] using hout
        · have hc : List.Forall₂
              (fun (p : Ident × YulSemantics.FDecl yulD)
                (q : Ident × FuncId) => p.1 = q.1)
              ((n, { params := ps, rets := rs, body := body }) ::
                YulSemantics.hoist yulD rest)
              ((n, fid) :: added) := .cons rfl hrel
          simpa [YulSemantics.hoist] using hc
      | block b | letDecl ps e | assign ps e | cond e b
      | forLoop b e post body | «break» | «continue» | leave
      | switch e cases dflt | exprStmt e =>
        obtain ⟨rfl, rfl⟩ := M.pure_inv hst
        obtain ⟨added, hout, hrel⟩ := ih _ _ _ _ hrest
        exact ⟨added, hout, by simpa [YulSemantics.hoist] using hrel⟩
  obtain ⟨added, hout, hrel⟩ := fold ss [] s s' scope h
  simpa using hout ▸ hrel

theorem mem_hoist_names {ss : List (Stmt Op)} {n : Ident}
    (h : n ∈ (YulSemantics.hoist yulD ss).map Prod.fst) :
    ∃ ps rs body, Stmt.funDef n ps rs body ∈ ss := by
  induction ss with
  | nil => simp [YulSemantics.hoist] at h
  | cons st rest ih =>
    cases st with
    | funDef n' ps rs body =>
      simp only [YulSemantics.hoist, List.filterMap_cons, List.map_cons,
        List.mem_cons] at h
      rcases h with h | h
      · exact ⟨ps, rs, body, by simp [h]⟩
      · obtain ⟨ps', rs', body', hm⟩ := ih h
        exact ⟨ps', rs', body', List.mem_cons_of_mem _ hm⟩
    | block b | letDecl ps e | assign ps e | cond e b
    | forLoop b e post body | «break» | «continue» | leave
    | switch e cases dflt | exprStmt e =>
      have hh : n ∈ (YulSemantics.hoist yulD rest).map Prod.fst := by
        simpa [YulSemantics.hoist] using h
      obtain ⟨ps', rs', body', hm⟩ := ih hh
      exact ⟨ps', rs', body', List.mem_cons_of_mem _ hm⟩

theorem hoist_names_nodup_of_stmtFuncIds (fenv : FMap) (env : VMap)
    (lctx : Option LoopCtx) (rets : Option (List Ident)) (d : Bool) :
    ∀ (ss : List (Stmt Op)) (s s' : BState) (r : Option VMap),
      (stmtFuncIds fenv ss).Nodup →
      trStmts fenv env lctx rets d ss s = some (r, s') →
      ((YulSemantics.hoist yulD ss).map Prod.fst).Nodup := by
  intro ss
  induction ss generalizing env d with
  | nil => intro s s' r _ _; simp [YulSemantics.hoist]
  | cons st rest ih =>
    intro s s' r hnd htr
    cases st with
    | funDef n ps rs body =>
      rw [trStmts] at htr
      obtain ⟨fid, s1, h1, htr⟩ := M.bind_inv htr
      obtain ⟨g, s2, h2, htr⟩ := M.bind_inv htr
      obtain ⟨u, s3, h3, htail⟩ := M.bind_inv htr
      obtain ⟨hget, -⟩ := M.liftO_inv h1
      simp only [stmtFuncIds, hget, Option.toList_some,
        List.singleton_append] at hnd
      have hndTail := (List.nodup_cons.mp hnd).2
      have hnmem : n ∉ (YulSemantics.hoist yulD rest).map Prod.fst := by
        intro hn
        obtain ⟨ps', rs', body', hm⟩ := mem_hoist_names hn
        apply (List.nodup_cons.mp hnd).1
        apply stmtFuncIds_mem hm
        simp [hget]
      simpa [YulSemantics.hoist] using
        (List.nodup_cons.mpr ⟨hnmem, ih env d s3 s' r hndTail htail⟩)
    | block b | letDecl ps e | assign ps e | cond e b
    | forLoop b e post body | «break» | «continue» | leave
    | switch e cases dflt | exprStmt e =>
      simp only [stmtFuncIds] at hnd
      rw [trStmts] at htr
      · split at htr
        · simpa [YulSemantics.hoist] using ih env true s s' r hnd htr
        · obtain ⟨renv, s1, h1, h2⟩ := M.bind_inv htr
          cases renv with
          | none => simpa [YulSemantics.hoist] using ih env true s1 s' r hnd h2
          | some env' =>
            simpa [YulSemantics.hoist] using ih env' false s1 s' r hnd h2
      · intro n ps rs body heq
        cases heq

omit model in
theorem allocScope_slots {ss : List (Stmt Op)} {s s' : BState}
    {scope : List (Ident × FuncId)} (h : allocScope ss s = some (scope, s')) :
    (scope.map Prod.snd).Nodup ∧
      ∀ i : FuncId, i ∈ scope.map Prod.snd →
        s.funcs.size ≤ i ∧ s'.funcs[i]? = some none := by
  rw [allocScope] at h
  have fold : ∀ (l : List (Stmt Op)) (acc : List (Ident × FuncId))
      (s0 s1 : BState) (out : List (Ident × FuncId)) (base : Nat),
      base ≤ s0.funcs.size →
      (acc.map Prod.snd).Nodup →
      (∀ i : FuncId, i ∈ acc.map Prod.snd →
        base ≤ i ∧ s0.funcs[i]? = some none) →
      (l.foldlM (init := acc) fun acc (st : Stmt Op) =>
        match st with
        | Stmt.funDef n _ _ _ => do
            let fid ← allocFunc
            pure (acc ++ [(n, fid)])
        | _ => pure acc) s0 = some (out, s1) →
      (out.map Prod.snd).Nodup ∧
        ∀ i : FuncId, i ∈ out.map Prod.snd →
          base ≤ i ∧ s1.funcs[i]? = some none := by
    intro l
    induction l with
    | nil =>
      intro acc s0 s1 out base _ hnd hslots hl
      obtain ⟨rfl, rfl⟩ := M.pure_inv hl
      exact ⟨hnd, hslots⟩
    | cons st rest ih =>
      intro acc s0 s1 out base hbase hnd hslots hl
      rw [List.foldlM_cons] at hl
      obtain ⟨acc', t, hst, hrest⟩ := M.bind_inv hl
      cases st with
      | funDef n ps rs body =>
        obtain ⟨fid, u, ha, hp⟩ := M.bind_inv hst
        rw [M.allocFunc_apply] at ha
        obtain ⟨rfl, rfl⟩ := M.some_pair_inj ha
        obtain ⟨rfl, rfl⟩ := M.pure_inv hp
        have hnot : s0.funcs.size ∉ acc.map Prod.snd := by
          intro hm
          exact Nat.ne_of_lt (lt_size_of_getElem? (hslots _ hm).2) rfl
        have hnd' : ((acc ++ [(n, s0.funcs.size)]).map Prod.snd).Nodup := by
          rw [List.map_append]
          simp only [List.map_singleton]
          rw [List.nodup_append]
          refine ⟨hnd, by simp, ?_⟩
          intro a ha b hb
          simp only [List.mem_singleton] at hb
          subst b
          exact fun he => hnot (he ▸ ha)
        have hslots' : ∀ i : FuncId,
            i ∈ (acc ++ [(n, s0.funcs.size)]).map Prod.snd →
            base ≤ i ∧ (s0.funcs.push none)[i]? = some none := by
          intro i hi
          simp only [List.map_append, List.map_singleton, List.mem_append,
            List.mem_singleton] at hi
          rcases hi with hi | rfl
          · refine ⟨(hslots i hi).1, ?_⟩
            rw [Array.getElem?_push, if_neg]
            · exact (hslots i hi).2
            · exact Nat.ne_of_lt (lt_size_of_getElem? (hslots i hi).2)
          · exact ⟨hbase, by simp⟩
        exact ih (acc ++ [(n, s0.funcs.size)]) _ s1 out base
          (Nat.le_trans hbase (by simp)) hnd' hslots' hrest
      | block b | letDecl ps e | assign ps e | cond e b
      | forLoop b e post body | «break» | «continue» | leave
      | switch e cases dflt | exprStmt e =>
        obtain ⟨rfl, rfl⟩ := M.pure_inv hst
        exact ih _ _ _ _ base hbase hnd hslots hrest
  exact fold ss [] s s' scope s.funcs.size (Nat.le_refl _) (by simp) (by simp) h

theorem allocScope_stmtFuncIds_perm {fenv : FMap} {env : VMap}
    {lctx : Option LoopCtx} {rets : Option (List Ident)} {d : Bool}
    {ss : List (Stmt Op)} {s0 sA s1 done : BState}
    {scope : List (Ident × FuncId)} {r : Option VMap}
    {owned : List FuncId}
    (hbound : ∀ i : FuncId, i ∈ owned → i < s0.funcs.size)
    (ha : allocScope ss s0 = some (scope, sA))
    (ht : trStmts (scope :: fenv) env lctx rets d ss sA = some (r, s1))
    (ho1 : FOwned owned s1 done) :
    (stmtFuncIds (scope :: fenv) ss).Perm (scope.map Prod.snd) := by
  let selected := stmtFuncIds (scope :: fenv) ss
  let slots := scope.map Prod.snd
  have hraw := allocScope_slots ha
  have hndSlots : slots.Nodup := hraw.1
  have hsub : slots ⊆ selected := by
    intro i hi
    by_contra hnot
    have hiA : sA.funcs[i]? = some none := (hraw.2 i hi).2
    have hskip : ∀ (n : Ident) (ps rs : List Ident)
        (body : List (Stmt Op)),
        Stmt.funDef n ps rs body ∈ ss → FMap.get (scope :: fenv) n ≠ some i := by
      intro n ps rs body hmem hget
      apply hnot
      apply stmtFuncIds_mem hmem
      simp [hget]
    have hi1 : s1.funcs[i]? = some none :=
      trStmts_pending_survives (scope :: fenv) env lctx rets d
        ss sA s1 r i hiA hskip ht
    have hio : i ∈ owned := (ho1.pending i).mpr hi1
    exact Nat.not_lt_of_ge (hraw.2 i hi).1 (hbound i hio)
  have hlen : selected.length = slots.length := by
    dsimp [selected, slots]
    rw [List.length_map, stmtFuncIds_length_of_trStmts
      (scope :: fenv) env lctx rets d ss sA s1 r ht,
      ← allocScope_length ha]
  have hs : slots.Subperm selected := hndSlots.subperm hsub
  exact (hs.perm_of_length_le hlen.le).symm

theorem forall2_hoist_scope_names
    {as : List (Ident × YulSemantics.FDecl yulD)}
    {bs : List (Ident × FuncId)}
    (h : List.Forall₂ (fun p q => p.1 = q.1) as bs) :
    as.map Prod.fst = bs.map Prod.fst := by
  induction h with
  | nil => rfl
  | cons hh ht ih => simp [hh, ih]

omit model in
private theorem find?_scope_suffix_nodup {top : List (Ident × FuncId)}
    {n : Ident} {fid : FuncId} {tl : List (Ident × FuncId)}
    (hnd : (top.map Prod.fst).Nodup)
    (hsuf : (n, fid) :: tl <:+ top) :
    top.find? (fun q => q.1 = n) = some (n, fid) := by
  obtain ⟨pre, hpre⟩ := hsuf
  subst hpre
  have hnp : n ∉ pre.map Prod.fst := by
    rw [List.map_append, List.map_cons] at hnd
    exact fun hm => (List.nodup_append.mp hnd).2.2 n hm n (by simp) rfl
  clear hnd
  induction pre with
  | nil => simp
  | cons a pre ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hnp
    rw [List.cons_append, List.find?_cons_of_neg (by
      simp only [decide_eq_true_eq]
      exact fun he => hnp.1 he.symm)]
    exact ih hnp.2

theorem trStmts_hoist_owned {P : Prog}
    {doneFuncs : Array (Option Func)}
    (hfuncs : FuncTableComplete P doneFuncs)
    {done : BState} (hdone : done.funcs = doneFuncs)
    {top : List (Ident × FuncId)} {fenv : FMap}
    (htop : (top.map Prod.fst).Nodup) :
    ∀ (ss : List (Stmt Op)) (rem : List (Ident × FuncId))
      (env : VMap) (lctx : Option LoopCtx) (rets : Option (List Ident))
      (d : Bool) (s s' : BState) (r : Option VMap) (owned : List FuncId),
      List.Forall₂ (fun (p : Ident × YulSemantics.FDecl yulD)
        (q : Ident × FuncId) => p.1 = q.1)
        (YulSemantics.hoist yulD ss) rem →
      rem <:+ top →
      (∀ i : FuncId, i ∈ rem.map Prod.snd → s.funcs[i]? = some none) →
      (∀ i : FuncId, i ∈ rem.map Prod.snd ++ owned →
        i < s.funcs.size) →
      (rem.map Prod.snd ++ owned).Nodup →
      FOwned owned s' done →
      trStmts (top :: fenv) env lctx rets d ss s = some (r, s') →
      List.Forall₂
        (fun (p : Ident × YulSemantics.FDecl yulD) (q : Ident × FuncId) =>
          p.1 = q.1 ∧ FuncOK (model := model) P (top :: fenv) p.2 q.2)
        (YulSemantics.hoist yulD ss) rem
        ∧ FOwned (rem.map Prod.snd ++ owned) s done := by
  intro ss
  induction ss with
  | nil =>
    intro rem env lctx rets d s s' r owned hrel _ _ _ hnd ho htr
    cases hrel
    rw [trStmts] at htr
    obtain ⟨-, rfl⟩ := M.pure_inv htr
    exact ⟨List.Forall₂.nil, by simpa using ho⟩
  | cons st rest ih =>
    intro rem env lctx rets d s s' r owned hrel hsuf hslots hbound hnd ho htr
    cases st with
    | funDef n ps rs body =>
      cases hrel with
      | cons hname hrelTail =>
        rename_i q remTail
        obtain ⟨qn, qfid⟩ := q
        dsimp only at hname
        subst qn
        have hsufHead : (n, qfid) :: remTail <:+ top := hsuf
        have hfind := find?_scope_suffix_nodup htop hsufHead
        have hget : FMap.get (top :: fenv) n = some qfid := by
          rw [FMap.get, hfind]
          rfl
        rw [trStmts] at htr
        obtain ⟨fid, s1, h1, htr⟩ := M.bind_inv htr
        obtain ⟨g, s2, h2, htr⟩ := M.bind_inv htr
        obtain ⟨u, s3, h3, htail⟩ := M.bind_inv htr
        obtain ⟨hget1, hs1⟩ := M.liftO_inv h1
        have hfidEq : fid = qfid := Option.some.inj (hget1.symm.trans hget)
        subst fid
        subst s1
        have hp := trFunc_prefix (top :: fenv) ps rs body h2
        have hq0 : s.funcs[qfid]? = some none := hslots qfid (by simp)
        have hq2 : s2.funcs[qfid]? = some none := by
          rw [hp qfid (lt_size_of_getElem? hq0)]
          exact hq0
        obtain ⟨hqLt, hs3⟩ := M.fillFunc_inv h3
        have hndTail : (remTail.map Prod.snd ++ owned).Nodup := by
          simpa using (List.nodup_cons.mp (by simpa using hnd)).2
        have hqNot : qfid ∉ remTail.map Prod.snd ++ owned :=
          (List.nodup_cons.mp (by simpa using hnd)).1
        have hslotsTail : ∀ i : FuncId, i ∈ remTail.map Prod.snd →
            s3.funcs[i]? = some none := by
          intro i hi
          have hi0 := hslots i (by simp [hi])
          have hi2 : s2.funcs[i]? = some none := by
            rw [hp i (lt_size_of_getElem? hi0)]
            exact hi0
          have hine : i ≠ qfid := by
            intro he
            subst i
            exact hqNot (List.mem_append_left _ hi)
          rw [hs3, Array.getElem?_set (h := hqLt), if_neg (Ne.symm hine)]
          exact hi2
        have hboundTail : ∀ i : FuncId, i ∈ remTail.map Prod.snd ++ owned →
            i < s3.funcs.size := by
          intro i hi
          have hi0 : i < s.funcs.size := hbound i (by simp [hi])
          have hsizes : s.funcs.size ≤ s2.funcs.size := hp.size (Nat.le_refl _)
          rw [hs3]
          simpa using Nat.lt_of_lt_of_le hi0 hsizes
        have hsufTail : remTail <:+ top := (List.suffix_cons _ _).trans hsufHead
        obtain ⟨hrelOut, ho3⟩ := ih remTail env lctx rets d s3 s' r owned
          hrelTail hsufTail hslotsTail hboundTail hndTail ho htail
        have hslot3 : s3.funcs[qfid]? = some (some g) := by
          rw [hs3]
          simp
        have hfillContents : FContents s2 s3 :=
          FContents.of_fillFunc_empty hq2 h3
        have ho2 : FOwned (qfid :: (remTail.map Prod.snd ++ owned)) s2 done :=
          FOwned.back_fillFunc hq2 h3 ho3
        have hbound2 : ∀ i : FuncId,
            i ∈ qfid :: (remTail.map Prod.snd ++ owned) → i < s.funcs.size := by
          intro i hi
          exact hbound i (by simpa using hi)
        have ho0 := FOwned.back_fprefix hp hbound2 ho2
        have hbudget : ∀ i : FuncId, s2.funcs[i]? = some none →
            i < s.funcs.size := by
          intro i hi
          exact hbound2 i ((ho2.pending i).mpr hi)
        have hok : FuncOK (model := model) P (top :: fenv)
            { params := ps, rets := rs, body := body } qfid := by
          apply hfuncs.funcOK_of_contents h2 hbudget hslot3
          · intro i g' hi
            exact hfillContents i g' hi
          · exact ho3.filled
          · exact hdone
        refine ⟨?_, ?_⟩
        · exact .cons ⟨rfl, hok⟩ hrelOut
        · simpa using ho0
    | block body | letDecl vars val | assign vars e | cond e body
    | forLoop init e post body | «break» | «continue» | leave
    | switch e cases dflt | exprStmt e =>
      simp only [YulSemantics.hoist, List.filterMap_cons] at hrel
      rw [trStmts] at htr
      · split at htr
        · exact ih rem env lctx rets true s s' r owned hrel hsuf hslots
            hbound hnd ho htr
        · obtain ⟨renv, s1, h1, h2⟩ := M.bind_inv htr
          have hp := trStmt_fprefix (top :: fenv) env lctx rets _ s.funcs.size
            s renv s1 (Nat.le_refl _) h1
          have hslots1 : ∀ i : FuncId, i ∈ rem.map Prod.snd →
              s1.funcs[i]? = some none := by
            intro i hi
            rw [hp i (hbound i (List.mem_append_left _ hi))]
            exact hslots i hi
          have hbound1 : ∀ i : FuncId, i ∈ rem.map Prod.snd ++ owned →
              i < s1.funcs.size := by
            intro i hi
            exact Nat.lt_of_lt_of_le (hbound i hi) (hp.size (Nat.le_refl _))
          cases renv with
          | none =>
            obtain ⟨hrelOut, ho1⟩ := ih rem env lctx rets true s1 s' r owned
              hrel hsuf hslots1 hbound1 hnd ho h2
            exact ⟨hrelOut, FOwned.back_fprefix hp hbound ho1⟩
          | some env' =>
            obtain ⟨hrelOut, ho1⟩ := ih rem env' lctx rets false s1 s' r owned
              hrel hsuf hslots1 hbound1 hnd ho h2
            exact ⟨hrelOut, FOwned.back_fprefix hp hbound ho1⟩
      · intro n ps rs body heq
        cases heq

/-- Relate `allocScope`'s fresh reservations to the declarations selected by
`trStmts`, reconstruct the caller's pending-slot ownership, and realize the
hoisted semantic scope in the completed function table. -/
theorem allocScope_bridge {P : Prog}
    {doneFuncs : Array (Option Func)}
    (hfuncs : FuncTableComplete P doneFuncs)
    {funs : YulSemantics.FunEnv yulD} {fenv : FMap}
    (hfe : FEnvOK (model := model) P funs fenv)
    {env : VMap} {lctx : Option LoopCtx} {rets : Option (List Ident)} {d : Bool}
    {ss : List (Stmt Op)} {s0 sA s1 done : BState}
    {scope : List (Ident × FuncId)} {r : Option VMap}
    {owned : List FuncId}
    (hdone : done.funcs = doneFuncs)
    (hbound : ∀ i : FuncId, i ∈ owned → i < s0.funcs.size)
    (ho1 : FOwned owned s1 done)
    (ha : allocScope ss s0 = some (scope, sA))
    (ht : trStmts (scope :: fenv) env lctx rets d ss sA = some (r, s1)) :
    FEnvOK (model := model) P (YulSemantics.hoist yulD ss :: funs)
      (scope :: fenv) ∧ FOwned owned s0 done := by
  let selected := stmtFuncIds (scope :: fenv) ss
  let slots := scope.map Prod.snd
  have hraw := allocScope_slots ha
  have hperm : selected.Perm slots :=
    allocScope_stmtFuncIds_perm hbound ha ht ho1
  have hndSlots : slots.Nodup := hraw.1
  have hndSelected : (stmtFuncIds (scope :: fenv) ss).Nodup :=
    hperm.nodup_iff.mpr hndSlots
  have hndHoist := hoist_names_nodup_of_stmtFuncIds
    (scope :: fenv) env lctx rets d ss sA s1 r hndSelected ht
  have hrel := allocScope_forall2 ha
  have hnames : (YulSemantics.hoist yulD ss).map Prod.fst =
      scope.map Prod.fst := forall2_hoist_scope_names hrel
  have hndNames : (scope.map Prod.fst).Nodup := by rwa [← hnames]
  have hslots : ∀ i : FuncId, i ∈ scope.map Prod.snd →
      sA.funcs[i]? = some none := fun i hi => (hraw.2 i hi).2
  have hslotsSelected : ∀ i : FuncId,
      i ∈ stmtFuncIds (scope :: fenv) ss → sA.funcs[i]? = some none := by
    intro i hi
    exact hslots i (hperm.mem_iff.mp hi)
  have hsizeA : s0.funcs.size ≤ sA.funcs.size := (allocScope_funcsOnly ha).2
  have hboundSelected : ∀ i : FuncId,
      i ∈ stmtFuncIds (scope :: fenv) ss ++ owned → i < sA.funcs.size := by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact lt_size_of_getElem? (hslotsSelected i hi)
    · exact Nat.lt_of_lt_of_le (hbound i hi) hsizeA
  have hndAll : (stmtFuncIds (scope :: fenv) ss ++ owned).Nodup := by
    rw [List.nodup_append]
    refine ⟨hndSelected, ho1.nodup, ?_⟩
    intro i hi j hj heq
    subst j
    have hislot : i ∈ slots := hperm.mem_iff.mp hi
    exact Nat.not_lt_of_ge (hraw.2 i hislot).1 (hbound i hj)
  have hoSelected := trStmts_owned_back (scope :: fenv) lctx rets ss env d
    sA s1 done r owned hboundSelected hslotsSelected hndAll ho1 ht
  have hoScope : FOwned (scope.map Prod.snd ++ owned) sA done :=
    FOwned.perm (hperm.append_right owned) hoSelected
  have hboundScope : ∀ i : FuncId, i ∈ scope.map Prod.snd ++ owned →
      i < sA.funcs.size := by
    intro i hi
    exact lt_size_of_getElem? ((hoScope.pending i).mp hi)
  obtain ⟨hrelOK, -⟩ := trStmts_hoist_owned hfuncs hdone hndNames
    ss scope env lctx rets d sA s1 r owned hrel (List.suffix_refl _)
      hslots hboundScope hoScope.nodup ho1 ht
  have hoAlloc : FOwned (owned ++ scope.map Prod.snd) sA done :=
    FOwned.perm List.perm_append_comm hoScope
  have ho0 : FOwned owned s0 done := FOwned.back_allocScope ha hoAlloc
  exact ⟨FEnvOK.cons hrelOK hfe, ho0⟩

/-- The exact initializer premises consumed by the statement-list clause of
`Motive`, reconstructed from an enclosing `allocScope` and the completed
function table. -/
theorem allocScope_motive_inputs {P : Prog}
    {doneFuncs : Array (Option Func)}
    (hfuncs : FuncTableComplete P doneFuncs)
    {funs : YulSemantics.FunEnv yulD} {fenv : FMap}
    (hfe : FEnvOK (model := model) P funs fenv)
    {env : VMap} {lctx : Option LoopCtx} {rets : Option (List Ident)} {d : Bool}
    {ss : List (Stmt Op)} {s0 sA s1 done : BState}
    {scope : List (Ident × FuncId)} {r : Option VMap}
    {owned : List FuncId}
    (hdone : done.funcs = doneFuncs)
    (hbound : ∀ i : FuncId, i ∈ owned → i < s0.funcs.size)
    (ho1 : FOwned owned s1 done)
    (ha : allocScope ss s0 = some (scope, sA))
    (ht : trStmts (scope :: fenv) env lctx rets d ss sA = some (r, s1)) :
    FEnvOK (model := model) P (YulSemantics.hoist yulD ss :: funs)
        (scope :: fenv)
      ∧ (∀ i : FuncId, i ∈ stmtFuncIds (scope :: fenv) ss ++ owned →
          i < sA.funcs.size)
      ∧ (∀ i : FuncId, i ∈ stmtFuncIds (scope :: fenv) ss →
          sA.funcs[i]? = some none)
      ∧ (stmtFuncIds (scope :: fenv) ss ++ owned).Nodup
      ∧ FOwned owned s0 done := by
  let selected := stmtFuncIds (scope :: fenv) ss
  let slots := scope.map Prod.snd
  have hraw := allocScope_slots ha
  have hperm : selected.Perm slots :=
    allocScope_stmtFuncIds_perm hbound ha ht ho1
  have hslots : ∀ i : FuncId, i ∈ scope.map Prod.snd →
      sA.funcs[i]? = some none := fun i hi => (hraw.2 i hi).2
  have hslotsSelected : ∀ i : FuncId,
      i ∈ stmtFuncIds (scope :: fenv) ss → sA.funcs[i]? = some none := by
    intro i hi
    exact hslots i (hperm.mem_iff.mp hi)
  have hsizeA : s0.funcs.size ≤ sA.funcs.size := (allocScope_funcsOnly ha).2
  have hboundSelected : ∀ i : FuncId,
      i ∈ stmtFuncIds (scope :: fenv) ss ++ owned → i < sA.funcs.size := by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact lt_size_of_getElem? (hslotsSelected i hi)
    · exact Nat.lt_of_lt_of_le (hbound i hi) hsizeA
  have hndSelected : (stmtFuncIds (scope :: fenv) ss).Nodup :=
    hperm.nodup_iff.mpr hraw.1
  have hndAll : (stmtFuncIds (scope :: fenv) ss ++ owned).Nodup := by
    rw [List.nodup_append]
    refine ⟨hndSelected, ho1.nodup, ?_⟩
    intro i hi j hj heq
    subst j
    have hislot : i ∈ slots := hperm.mem_iff.mp hi
    exact Nat.not_lt_of_ge (hraw.2 i hislot).1 (hbound i hj)
  obtain ⟨hfe', ho0⟩ := allocScope_bridge hfuncs hfe hdone hbound ho1 ha ht
  exact ⟨hfe', hboundSelected, hslotsSelected, hndAll, ho0⟩

end Semantics
end YulEvmCompiler.SsaCfg
