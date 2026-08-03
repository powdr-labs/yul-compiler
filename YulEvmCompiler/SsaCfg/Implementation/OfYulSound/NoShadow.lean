import YulEvmCompiler.SsaCfg.Implementation.OfYulSound.CurInduction
set_option warningAsError true

/-!
# YulEvmCompiler.SsaCfg.Implementation.OfYulSound.NoShadow

The no-shadowing producer.

`NSOut`, `NSMotive` and the `ns_sim` induction: a source derivation over a
scope-checked program never shadows a name the construction has already
bound.
-/

namespace YulEvmCompiler.SsaCfg
open YulSemantics (Ident Literal Expr Stmt VEnv Outcome)
open YulSemantics.EVM (U256 EvmState Op builtinWithExternal evmWithExternal)

section Semantics
variable [model : ExternalModel]
local notation "yulD" => evmWithExternal model.calls model.creates

/-! ## The no-shadowing producer -/

/-- The names a fragment adds to the environment, with the disjointness the
construction's shadowing rejection guarantees. -/
def NSOut (V V' : VEnv yulD) : Prop :=
  ∃ W : List Ident, VEnv.names V' = W ++ VEnv.names V ∧ ∀ x ∈ W, x ∉ VEnv.names V

theorem NSOut.rfl' (V : VEnv yulD) : NSOut (model := model) V V :=
  ⟨[], rfl, by simp⟩

theorem NSOut.trans {V V₁ V₂ : VEnv yulD} (h₁ : NSOut (model := model) V V₁)
    (h₂ : NSOut (model := model) V₁ V₂) : NSOut (model := model) V V₂ := by
  obtain ⟨W₁, hn₁, hd₁⟩ := h₁
  obtain ⟨W₂, hn₂, hd₂⟩ := h₂
  refine ⟨W₂ ++ W₁, by rw [hn₂, hn₁, List.append_assoc], ?_⟩
  intro x hx hmem
  rcases List.mem_append.mp hx with hx | hx
  · exact hd₂ x hx (by rw [hn₁]; exact List.mem_append_right _ hmem)
  · exact hd₁ x hx hmem

theorem NSOut.of_names_eq {V V' : VEnv yulD}
    (h : VEnv.names V' = VEnv.names V) : NSOut (model := model) V V' :=
  ⟨[], by simpa using h, by simp⟩

/-- `NSOut` is the form of `NoShadow` the scope combinator consumes. -/
theorem noShadow_of_NSOut {V V' : VEnv yulD}
    (h : NSOut (model := model) V V') : NoShadow (model := model) V V' := by
  obtain ⟨W, hn, hd⟩ := h
  intro x hx
  have hlen : W.length = V'.length - V.length := by
    have := congrArg List.length hn
    simp [VEnv.length_names] at this
    omega
  have hw : VEnv.names (V'.take (V'.length - V.length)) = W := by
    rw [VEnv.names, List.map_take, show List.map Prod.fst V' = VEnv.names V' from rfl,
      hn, ← hlen]
    simp
  rw [hw] at hx
  exact hd x hx

/-- The motive of the no-shadowing producer: against any accepted construction
run, a source statement fragment only adds names the enclosing environment does
not already have, and (when it falls through) the construction's environment
tracks the source's names. -/
def NSMotive (V : VEnv yulD) :
    YulSemantics.Code Op → YulSemantics.Res yulD → Prop
  | .stmt st, .sres V' _ o =>
      ∀ (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
        (rets : Option (List Ident)) (s s' : BState) (renv : Option VMap),
        env.map Prod.fst = VEnv.names V →
        trStmt fenv env lctx rets st s = some (renv, s') →
        NSOut (model := model) V V'
          ∧ (o = .normal → ∃ e, renv = some e ∧ e.map Prod.fst = VEnv.names V')
  | .stmts ss, .sres V' _ o =>
      ∀ (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
        (rets : Option (List Ident)) (s s' : BState) (renv : Option VMap),
        env.map Prod.fst = VEnv.names V →
        trStmts fenv env lctx rets false ss s = some (renv, s') →
        NSOut (model := model) V V'
          ∧ (o = .normal → ∃ e, renv = some e ∧ e.map Prod.fst = VEnv.names V')
  | _, _ => True

omit model in
/-- The right-hand side of a `let`/`assign` produces exactly `n` ids. -/
theorem trExprN_length {fenv : FMap} {env : VMap} {n : Nat} {e : Expr Op}
    {s s' : BState} {ids : List ValId}
    (h : trExprN fenv env n e s = some (ids, s')) : ids.length = n := by
  cases e with
  | call fn args =>
    rw [trExprN] at h
    obtain ⟨as, sA, h1, h⟩ := M.bind_inv h
    obtain ⟨fid, sB, h2, h⟩ := M.bind_inv h
    obtain ⟨ds, sC, h3, h⟩ := M.bind_inv h
    obtain ⟨u, sD, h4, h5⟩ := M.bind_inv h
    obtain ⟨rfl, rfl⟩ := M.pure_inv h5
    obtain ⟨hlen, -, -⟩ := M.mapM_freshVal_length h3
    simpa using hlen
  | lit l =>
    obtain ⟨rfl, i, rfl, -⟩ := trExprN_nonCall_inv (by intro fn args; simp) h
    simp
  | var x =>
    obtain ⟨rfl, i, rfl, -⟩ := trExprN_nonCall_inv (by intro fn args; simp) h
    simp
  | builtin op args =>
    obtain ⟨rfl, i, rfl, -⟩ := trExprN_nonCall_inv (by intro fn args; simp) h
    simp

omit model in
/-- Names of a `zip`-prefixed environment. -/
theorem names_zip_append (vars : List Ident) (ids : List ValId) (env : VMap)
    (hlen : vars.length ≤ ids.length) :
    (vars.zip ids ++ env).map Prod.fst = vars ++ env.map Prod.fst := by
  rw [List.map_append, List.map_fst_zip]
  exact hlen

theorem names_bindZeros (vars : List Ident) :
    VEnv.names (YulSemantics.bindZeros yulD vars) = vars := by
  simp only [YulSemantics.bindZeros, VEnv.names, List.map_map]
  induction vars with
  | nil => rfl
  | cons x xs ih => simpa using ih

set_option maxHeartbeats 1000000 in
/-- **The no-shadowing producer.**  Against any accepted construction run, a
source statement fragment only introduces names the enclosing environment does
not already carry, and when it falls through the construction's environment
tracks the source's name spine. -/
theorem ns_sim {funs : YulSemantics.FunEnv yulD} {V : VEnv yulD}
    {yst : EvmState} {c : YulSemantics.Code Op} {res : YulSemantics.Res yulD}
    (h : YulSemantics.Step yulD funs V yst c res) :
    NSMotive (model := model) V c res := by
  induction h with
  | @funDef funs V st n ps rs b =>
    intro fenv env lctx rets s s' renv _ htr
    rw [trStmt] at htr
    exact absurd htr (by simp [reject])
  | @block funs V st body Vb stb o hb ihb =>
    intro fenv env lctx rets s s' renv hnames htr
    rw [trStmt, trScope] at htr
    obtain ⟨scope, sA, ha, htr⟩ := M.bind_inv htr
    obtain ⟨renvI, sB, htrS, hend⟩ := M.bind_inv htr
    obtain ⟨hns, hren⟩ := ihb (scope :: fenv) env lctx rets sA sB renvI hnames htrS
    obtain ⟨W, hW, hd⟩ := hns
    have hlenV : V.length ≤ Vb.length := by
      have h1 := congrArg List.length hW
      rw [VEnv.length_names, List.length_append, VEnv.length_names] at h1
      omega
    have hrest : VEnv.names (YulSemantics.restore V Vb) = VEnv.names V :=
      names_restore hlenV hW
    refine ⟨NSOut.of_names_eq hrest, ?_⟩
    intro ho
    obtain ⟨e, he, hne⟩ := hren ho
    subst he
    obtain ⟨hrenv, -⟩ := M.pure_inv hend
    refine ⟨e.drop (e.length - env.length), hrenv, ?_⟩
    have hlenE : e.length = Vb.length := by
      have := congrArg List.length hne
      rwa [List.length_map, VEnv.length_names] at this
    have hlenEnv : env.length = V.length := by
      have := congrArg List.length hnames
      rwa [List.length_map, VEnv.length_names] at this
    have hWlen : W.length = Vb.length - V.length := by
      have h1 := congrArg List.length hW
      rw [VEnv.length_names, List.length_append, VEnv.length_names] at h1
      omega
    rw [List.map_drop, hne, hW, hlenE, hlenEnv, ← hWlen, List.drop_left, hrest]
  | @letZero funs V st vars =>
    intro fenv env lctx rets s s' renv hnames htr
    rw [trStmt] at htr
    by_cases hgate : (vars.any env.mem || !decide vars.Nodup) = true
    · rw [if_pos hgate] at htr
      obtain ⟨u, sA, h1, -⟩ := M.bind_inv htr
      exact absurd h1 (by simp [reject])
    rw [if_neg hgate] at htr
    obtain ⟨u, sA, h1, htr⟩ := M.bind_inv htr
    obtain ⟨-, hsA⟩ := M.pure_inv h1
    rw [hsA] at htr
    obtain ⟨ids, sB, h2, h3⟩ := M.bind_inv htr
    rw [mapM_constZero_spec] at h2
    obtain ⟨hids, -⟩ := M.some_pair_inj h2
    subst hids
    obtain ⟨hrenv, -⟩ := M.pure_inv h3
    have ha : vars.any env.mem = false := by
      cases hv : vars.any env.mem with
      | false => rfl
      | true => exact False.elim (hgate (by simp [hv]))
    have hdis : ∀ x ∈ vars, x ∉ VEnv.names V := by
      intro x hx hmem
      have : env.mem x = true := by
        simp only [VMap.mem, List.any_eq_true]
        rw [← hnames] at hmem
        obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hmem
        exact ⟨p, hp, by simpa using hpe⟩
      exact List.any_eq_false.mp ha x hx this
    have hnamesV' : VEnv.names (YulSemantics.bindZeros yulD vars ++ V)
        = vars ++ VEnv.names V := by
      rw [VEnv.names_append, names_bindZeros]
    have hlen : vars.length ≤ (List.range' s.fn.nextVal vars.length).length := by
      simp
    refine ⟨⟨vars, hnamesV', hdis⟩, ?_⟩
    intro _
    refine ⟨_, hrenv, ?_⟩
    rw [names_zip_append vars (List.range' s.fn.nextVal vars.length) env hlen,
      hnames, hnamesV']
  | @letVal funs V st vars e vals st1 he hlen ihe =>
    intro fenv env lctx rets s s' renv hnames htr
    rw [trStmt] at htr
    by_cases hgate : (vars.any env.mem || !decide vars.Nodup) = true
    · rw [if_pos hgate] at htr
      obtain ⟨u, sA, h1, -⟩ := M.bind_inv htr
      exact absurd h1 (by simp [reject])
    rw [if_neg hgate] at htr
    obtain ⟨u, sA, h1, htr⟩ := M.bind_inv htr
    obtain ⟨-, hsA⟩ := M.pure_inv h1
    rw [hsA] at htr
    obtain ⟨ids, sB, h2, h3⟩ := M.bind_inv htr
    obtain ⟨hrenv, -⟩ := M.pure_inv h3
    have hidlen : ids.length = vars.length := trExprN_length h2
    have ha : vars.any env.mem = false := by
      cases hv : vars.any env.mem with
      | false => rfl
      | true => exact False.elim (hgate (by simp [hv]))
    have hdis : ∀ x ∈ vars, x ∉ VEnv.names V := by
      intro x hx hmem
      have : env.mem x = true := by
        simp only [VMap.mem, List.any_eq_true]
        rw [← hnames] at hmem
        obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hmem
        exact ⟨p, hp, by simpa using hpe⟩
      exact List.any_eq_false.mp ha x hx this
    have hnamesV' : VEnv.names (vars.zip vals ++ V) = vars ++ VEnv.names V := by
      rw [VEnv.names, List.map_append, List.map_fst_zip]
      · rfl
      · omega
    refine ⟨⟨vars, hnamesV', hdis⟩, ?_⟩
    intro _
    refine ⟨_, hrenv, ?_⟩
    rw [names_zip_append vars ids env (by omega), hnames, hnamesV']
  | @letHalt funs V st vars e st1 he ihe =>
    intro fenv env lctx rets s s' renv hnames htr
    exact ⟨NSOut.rfl' V, by intro ho; exact absurd ho (by simp)⟩
  | @assignVal funs V st vars e vals st1 he hlen ihe =>
    intro fenv env lctx rets s s' renv hnames htr
    rw [trStmt] at htr
    by_cases hgate : (!vars.all env.mem) = true
    · rw [if_pos hgate] at htr
      obtain ⟨u, sA, h1, -⟩ := M.bind_inv htr
      exact absurd h1 (by simp [reject])
    rw [if_neg hgate] at htr
    obtain ⟨u, sA, h1, htr⟩ := M.bind_inv htr
    obtain ⟨-, hsA⟩ := M.pure_inv h1
    rw [hsA] at htr
    obtain ⟨ids, sB, h2, h3⟩ := M.bind_inv htr
    obtain ⟨hrenv, -⟩ := M.pure_inv h3
    have hnamesV' : VEnv.names (YulSemantics.VEnv.setMany V vars vals)
        = VEnv.names V := VEnv.names_setMany
    refine ⟨NSOut.of_names_eq hnamesV', ?_⟩
    intro _
    exact ⟨_, hrenv, by rw [VMap.names_setMany, hnames, hnamesV']⟩
  | @assignHalt funs V st vars e st1 he ihe =>
    intro fenv env lctx rets s s' renv hnames htr
    exact ⟨NSOut.rfl' V, by intro ho; exact absurd ho (by simp)⟩
  | @exprStmt funs V st e st1 he ihe =>
    intro fenv env lctx rets s s' renv hnames htr
    refine ⟨NSOut.rfl' V, ?_⟩
    intro _
    cases e with
    | lit l =>
      rw [trStmt] at htr
      · exact absurd htr (by simp [reject])
      · intro op args hc; cases hc
      · intro fn args hc; cases hc
    | var x =>
      rw [trStmt] at htr
      · exact absurd htr (by simp [reject])
      · intro op args hc; cases hc
      · intro fn args hc; cases hc
    | builtin op args =>
      rw [trStmt] at htr
      obtain ⟨as, sA, h1, htr⟩ := M.bind_inv htr
      by_cases hop : isHaltingOp op = true
      · exfalso
        cases he with
        | builtinOk hargs hb =>
          obtain ⟨st', hbad⟩ := isHaltingOp_halts (model := model) hop hb
          cases hbad
      · rw [if_neg hop] at htr
        obtain ⟨u, sB, h2, h3⟩ := M.bind_inv htr
        obtain ⟨hrenv, -⟩ := M.pure_inv h3
        exact ⟨env, hrenv, hnames⟩
    | call fn args =>
      rw [trStmt] at htr
      obtain ⟨as, sA, h1, htr⟩ := M.bind_inv htr
      obtain ⟨fid, sB, h2, htr⟩ := M.bind_inv htr
      obtain ⟨u, sC, h3, h4⟩ := M.bind_inv htr
      obtain ⟨hrenv, -⟩ := M.pure_inv h4
      exact ⟨env, hrenv, hnames⟩
  | @exprStmtHalt funs V st e st1 he ihe =>
    intro fenv env lctx rets s s' renv hnames htr
    exact ⟨NSOut.rfl' V, by intro ho; exact absurd ho (by simp)⟩
  | @ifTrue funs V st c body cv st1 V' st2 o hc hnz hbody ihc ihb =>
    intro fenv env lctx rets s s' renv hnames htr
    have hnamesV' : VEnv.names V' = VEnv.names V := by
      have hm := (mod_sim hbody).1
      simpa [declsOfStmt] using hm
    refine ⟨NSOut.of_names_eq hnamesV', ?_⟩
    intro _
    rw [trStmt] at htr
    obtain ⟨cvId, sA, h1, htr⟩ := M.bind_inv htr
    obtain ⟨xvals, sB, h2, htr⟩ := M.bind_inv htr
    obtain ⟨bodyId, sC, h3, htr⟩ := M.bind_inv htr
    obtain ⟨joinParams, sD, h4, htr⟩ := M.bind_inv htr
    obtain ⟨joinId, sE, h5, htr⟩ := M.bind_inv htr
    obtain ⟨uF, sF, h6, htr⟩ := M.bind_inv htr
    obtain ⟨uG, sG, h7, htr⟩ := M.bind_inv htr
    obtain ⟨bodyEnv, sH, h8, htr⟩ := M.bind_inv htr
    cases bodyEnv with
    | none =>
      obtain ⟨ua, sa, ha, htr⟩ := M.bind_inv htr
      obtain ⟨ub, sb, hbb, hc'⟩ := M.bind_inv htr
      obtain ⟨hrenv, -⟩ := M.pure_inv hc'
      exact ⟨_, hrenv, by rw [VMap.names_setMany, hnames, hnamesV']⟩
    | some envB =>
      obtain ⟨xvB, sI, h9, htr⟩ := M.bind_inv htr
      obtain ⟨uJ, sJ, h10, htr⟩ := M.bind_inv htr
      obtain ⟨uK, sK, h11, htr⟩ := M.bind_inv htr
      obtain ⟨hrenv, -⟩ := M.pure_inv htr
      exact ⟨_, hrenv, by rw [VMap.names_setMany, hnames, hnamesV']⟩
  | @ifFalse funs V st c body cv st1 hc hz ihc =>
    intro fenv env lctx rets s s' renv hnames htr
    refine ⟨NSOut.rfl' V, ?_⟩
    intro _
    rw [trStmt] at htr
    obtain ⟨cvId, sA, h1, htr⟩ := M.bind_inv htr
    obtain ⟨xvals, sB, h2, htr⟩ := M.bind_inv htr
    obtain ⟨bodyId, sC, h3, htr⟩ := M.bind_inv htr
    obtain ⟨joinParams, sD, h4, htr⟩ := M.bind_inv htr
    obtain ⟨joinId, sE, h5, htr⟩ := M.bind_inv htr
    obtain ⟨uF, sF, h6, htr⟩ := M.bind_inv htr
    obtain ⟨uG, sG, h7, htr⟩ := M.bind_inv htr
    obtain ⟨bodyEnv, sH, h8, htr⟩ := M.bind_inv htr
    cases bodyEnv with
    | none =>
      obtain ⟨ua, sa, ha, htr⟩ := M.bind_inv htr
      obtain ⟨ub, sb, hbb, hc'⟩ := M.bind_inv htr
      obtain ⟨hrenv, -⟩ := M.pure_inv hc'
      exact ⟨_, hrenv, by rw [VMap.names_setMany, hnames]⟩
    | some envB =>
      obtain ⟨xvB, sI, h9, htr⟩ := M.bind_inv htr
      obtain ⟨uJ, sJ, h10, htr⟩ := M.bind_inv htr
      obtain ⟨uK, sK, h11, htr⟩ := M.bind_inv htr
      obtain ⟨hrenv, -⟩ := M.pure_inv htr
      exact ⟨_, hrenv, by rw [VMap.names_setMany, hnames]⟩
  | @ifHalt funs V st c body st1 hc ihc =>
    intro fenv env lctx rets s s' renv hnames htr
    exact ⟨NSOut.rfl' V, by intro ho; exact absurd ho (by simp)⟩
  | @switchExec funs V st c cases dflt cv st1 V' st2 o hc hsel ihc ihs =>
    intro fenv env lctx rets s s' renv hnames htr
    have hnamesV' : VEnv.names V' = VEnv.names V := by
      have hm := (mod_sim hsel).1
      simpa [declsOfStmt] using hm
    refine ⟨NSOut.of_names_eq hnamesV', ?_⟩
    intro _
    unfold trStmt at htr
    obtain ⟨svId, sA, h1, htr⟩ := M.bind_inv htr
    obtain ⟨joinParams, sB, h2, htr⟩ := M.bind_inv htr
    obtain ⟨joinId, sC, h3, htr⟩ := M.bind_inv htr
    obtain ⟨uD, sD, h4, htr⟩ := M.bind_inv htr
    obtain ⟨uE, sE, h5, htr⟩ := M.bind_inv htr
    obtain ⟨hrenv, -⟩ := M.pure_inv htr
    exact ⟨_, hrenv, by rw [VMap.names_setMany, hnames, hnamesV']⟩
  | @switchHalt funs V st c cases dflt st1 hc ihc =>
    intro fenv env lctx rets s s' renv hnames htr
    exact ⟨NSOut.rfl' V, by intro ho; exact absurd ho (by simp)⟩
  | @forLoop funs V st init c post body Vinit stinit Vend stend o hinit hloop ihi ihl =>
    intro fenv env lctx rets s s' renv hnames htr
    have hnamesV' : VEnv.names (YulSemantics.restore V Vend) = VEnv.names V := by
      have hm := (mod_sim (YulSemantics.Step.forLoop hinit hloop)).1
      simpa [declsOfStmt] using hm
    refine ⟨NSOut.of_names_eq hnamesV', ?_⟩
    intro _
    unfold trStmt at htr
    obtain ⟨scope, sA, ha, htr⟩ := M.bind_inv htr
    obtain ⟨rinit, sB, hinitTr, htr⟩ := M.bind_inv htr
    obtain ⟨hnsI, hrenI⟩ := ihi (scope :: fenv) env lctx rets sA sB rinit hnames hinitTr
    obtain ⟨envI, hEnvI, hnamesI⟩ := hrenI rfl
    subst hEnvI
    obtain ⟨W, hW, hd⟩ := hnsI
    have hlenEnv : env.length = V.length := by
      have := congrArg List.length hnames
      rwa [List.length_map, VEnv.length_names] at this
    have hWlen : W.length = Vinit.length - V.length := by
      have h1 := congrArg List.length hW
      rw [VEnv.length_names, List.length_append, VEnv.length_names] at h1
      omega
    have key : ∀ m : VMap, m.map Prod.fst = VEnv.names Vinit →
        (m.drop (m.length - env.length)).map Prod.fst
          = VEnv.names (YulSemantics.restore V Vend) := by
      intro m hm
      have hlenm : m.length = Vinit.length := by
        have := congrArg List.length hm
        rwa [List.length_map, VEnv.length_names] at this
      rw [List.map_drop, hm, hW, hlenm, hlenEnv, ← hWlen, List.drop_left, hnamesV']
    have hkeyI : ∀ ep : List ValId,
        ((envI.setMany (modifiedX envI [post, body]) ep)).map Prod.fst
          = VEnv.names Vinit := by
      intro ep; rw [VMap.names_setMany, hnamesI]
    obtain ⟨xvals, s1, hx1, htr⟩ := M.bind_inv htr
    obtain ⟨hParams, s2, hx2, htr⟩ := M.bind_inv htr
    obtain ⟨hId, s3, hx3, htr⟩ := M.bind_inv htr
    obtain ⟨exitParams, s4, hx4, htr⟩ := M.bind_inv htr
    obtain ⟨exitId, s5, hx5, htr⟩ := M.bind_inv htr
    obtain ⟨postParams, s6, hx6, htr⟩ := M.bind_inv htr
    obtain ⟨postId, s7, hx7, htr⟩ := M.bind_inv htr
    obtain ⟨u8, s8, hx8, htr⟩ := M.bind_inv htr
    obtain ⟨u9, s9, hx9, htr⟩ := M.bind_inv htr
    obtain ⟨cvId, s10, hx10, htr⟩ := M.bind_inv htr
    obtain ⟨bodyId, s11, hx11, htr⟩ := M.bind_inv htr
    obtain ⟨hX, s12, hx12, htr⟩ := M.bind_inv htr
    obtain ⟨u13, s13, hx13, htr⟩ := M.bind_inv htr
    obtain ⟨u14, s14, hx14, htr⟩ := M.bind_inv htr
    obtain ⟨renvB, s15, hx15, htr⟩ := M.bind_inv htr
    cases renvB with
    | none =>
      obtain ⟨u16, s16, hx16, htr⟩ := M.bind_inv htr
      obtain ⟨u17, s17, hx17, htr⟩ := M.bind_inv htr
      obtain ⟨renvP, s18, hx18, htr⟩ := M.bind_inv htr
      cases renvP with
      | none =>
        obtain ⟨u19, s19, hx19, htr⟩ := M.bind_inv htr
        obtain ⟨u20, s20, hx20, htr⟩ := M.bind_inv htr
        obtain ⟨hrenv, -⟩ := M.pure_inv htr
        exact ⟨_, hrenv, key _ (hkeyI _)⟩
      | some envP' =>
        obtain ⟨u19, s19, hx19, htr⟩ := M.bind_inv htr
        obtain ⟨u20, s20, hx20, htr⟩ := M.bind_inv htr
        obtain ⟨u21, s21, hx21, htr⟩ := M.bind_inv htr
        obtain ⟨hrenv, -⟩ := M.pure_inv htr
        exact ⟨_, hrenv, key _ (hkeyI _)⟩
    | some envB =>
      obtain ⟨u16, s16, hx16, htr⟩ := M.bind_inv htr
      obtain ⟨u17, s17, hx17, htr⟩ := M.bind_inv htr
      obtain ⟨u18, s18, hx18, htr⟩ := M.bind_inv htr
      obtain ⟨renvP, s19, hx19, htr⟩ := M.bind_inv htr
      cases renvP with
      | none =>
        obtain ⟨u20, s20, hx20, htr⟩ := M.bind_inv htr
        obtain ⟨u21, s21, hx21, htr⟩ := M.bind_inv htr
        obtain ⟨hrenv, -⟩ := M.pure_inv htr
        exact ⟨_, hrenv, key _ (hkeyI _)⟩
      | some envP' =>
        obtain ⟨u20, s20, hx20, htr⟩ := M.bind_inv htr
        obtain ⟨u21, s21, hx21, htr⟩ := M.bind_inv htr
        obtain ⟨u22, s22, hx22, htr⟩ := M.bind_inv htr
        obtain ⟨hrenv, -⟩ := M.pure_inv htr
        exact ⟨_, hrenv, key _ (hkeyI _)⟩
  | @forInitHalt funs V st init c post body Vinit stinit hinit ihi =>
    intro fenv env lctx rets s s' renv hnames htr
    have hnamesV' : VEnv.names (YulSemantics.restore V Vinit) = VEnv.names V := by
      have hm := (mod_sim (YulSemantics.Step.forInitHalt hinit
        (c := c) (post := post) (body := body))).1
      simpa [declsOfStmt] using hm
    exact ⟨NSOut.of_names_eq hnamesV', by intro ho; exact absurd ho (by simp)⟩
  | @«break» funs V st =>
    intro fenv env lctx rets s s' renv hnames htr
    exact ⟨NSOut.rfl' V, by intro ho; exact absurd ho (by simp)⟩
  | @«continue» funs V st =>
    intro fenv env lctx rets s s' renv hnames htr
    exact ⟨NSOut.rfl' V, by intro ho; exact absurd ho (by simp)⟩
  | @leave funs V st =>
    intro fenv env lctx rets s s' renv hnames htr
    exact ⟨NSOut.rfl' V, by intro ho; exact absurd ho (by simp)⟩
  | @seqNil funs V st =>
    intro fenv env lctx rets s s' renv hnames htr
    rw [trStmts] at htr
    obtain ⟨hrenv, -⟩ := M.pure_inv htr
    exact ⟨NSOut.rfl' V, fun _ => ⟨env, by simpa using hrenv, hnames⟩⟩
  | @seqCons funs V st st0 rest V1 st1 V2 st2 o h1 h2 ih1 ih2 =>
    intro fenv env lctx rets s s' renv hnames htr
    cases st0 with
    | funDef n ps rs body =>
      cases h1
      rw [trStmts] at htr
      obtain ⟨fid, sA, hA, htr⟩ := M.bind_inv htr
      obtain ⟨g, sB, hB, htr⟩ := M.bind_inv htr
      obtain ⟨u, sC, hC, htail⟩ := M.bind_inv htr
      exact ih2 fenv env lctx rets sC s' renv hnames htail
    | block body | letDecl vars val | assign vars e | cond e body
    | forLoop init e post body | «break» | «continue» | leave
    | switch e cases dflt | exprStmt e =>
      all_goals (
        obtain ⟨renvA, sA, hhead, htail⟩ := trStmts_false_cons_inv
          (by intros; simp) htr
        obtain ⟨hns1, hren1⟩ := ih1 fenv env lctx rets s sA renvA hnames hhead
        obtain ⟨envA, hEnvA, hnamesA⟩ := hren1 rfl
        subst hEnvA
        obtain ⟨hns2, hren2⟩ := ih2 fenv envA lctx rets sA s' renv hnamesA htail
        exact ⟨hns1.trans hns2, hren2⟩)
  | @seqStop funs V st st0 rest V1 st1 o h1 hne ih1 =>
    intro fenv env lctx rets s s' renv hnames htr
    cases st0 with
    | funDef n ps rs body =>
      cases h1
      exact absurd rfl hne
    | block body | letDecl vars val | assign vars e | cond e body
    | forLoop init e post body | «break» | «continue» | leave
    | switch e cases dflt | exprStmt e =>
      all_goals (
        obtain ⟨renvA, sA, hhead, htail⟩ := trStmts_false_cons_inv
          (by intros; simp) htr
        obtain ⟨hns1, -⟩ := ih1 fenv env lctx rets s sA renvA hnames hhead
        exact ⟨hns1, fun ho => absurd ho hne⟩)
  | _ => exact trivial

end Semantics
end YulEvmCompiler.SsaCfg
