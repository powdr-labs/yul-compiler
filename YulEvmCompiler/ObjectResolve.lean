import YulSemantics.Determinism
import YulSemantics.ObjectRun
set_option warningAsError true
/-!
# YulEvmCompiler.ObjectResolve

Semantic preservation for object-layout reference resolution.

`resolveForLayout` replaces `dataoffset("name")` and `datasize("name")`
with the concrete word recorded by a selected `Layout`.  The transformation
is total and descends into hoisted function bodies.  The main theorem in this
module proves that this replacement preserves the complete Yul big-step
derivation when the state's object maps are the maps from that layout.
-/

namespace YulEvmCompiler

open YulSemantics
open YulSemantics.EVM (Op U256 Layout EvmState litValue stepOp evm)

mutual
  def resolveForLayoutExpr (L : Layout) : Expr Op → Expr Op
    | .lit literal => .lit literal
    | .var name => .var name
    | .builtin op args =>
        let args' := resolveForLayoutExprs L args
        match op, args with
        | .dataoffset, [.lit (.string name)] =>
            .lit (.number (L.dataOffset (litValue (.string name))).toNat)
        | .datasize, [.lit (.string name)] =>
            .lit (.number (L.dataSize (litValue (.string name))).toNat)
        | _, _ => .builtin op args'
    | .call name args => .call name (resolveForLayoutExprs L args)

  def resolveForLayoutExprs (L : Layout) : List (Expr Op) → List (Expr Op)
    | [] => []
    | expression :: expressions =>
        resolveForLayoutExpr L expression :: resolveForLayoutExprs L expressions
end

mutual
  def resolveForLayoutStmt (L : Layout) : Stmt Op → Stmt Op
    | .block body => .block (resolveForLayoutStmts L body)
    | .funDef name params returns body =>
        .funDef name params returns (resolveForLayoutStmts L body)
    | .letDecl names value =>
        .letDecl names (value.map (resolveForLayoutExpr L))
    | .assign names value => .assign names (resolveForLayoutExpr L value)
    | .cond condition body =>
        .cond (resolveForLayoutExpr L condition) (resolveForLayoutStmts L body)
    | .switch condition cases fallback =>
        .switch (resolveForLayoutExpr L condition)
          (resolveForLayoutCases L cases)
          (match fallback with
          | none => none
          | some body => some (resolveForLayoutStmts L body))
    | .forLoop init condition post body =>
        .forLoop (resolveForLayoutStmts L init)
          (resolveForLayoutExpr L condition) (resolveForLayoutStmts L post)
          (resolveForLayoutStmts L body)
    | .exprStmt expression => .exprStmt (resolveForLayoutExpr L expression)
    | .«break» => .«break»
    | .«continue» => .«continue»
    | .leave => .leave
    termination_by statement => 2 * sizeOf statement + 1
    decreasing_by all_goals simp_wf <;> omega

  def resolveForLayoutStmts (L : Layout) : List (Stmt Op) → List (Stmt Op)
    | [] => []
    | statement :: statements =>
        resolveForLayoutStmt L statement :: resolveForLayoutStmts L statements
    termination_by statements => 2 * sizeOf statements

  def resolveForLayoutCases (L : Layout) :
      List (Literal × List (Stmt Op)) → List (Literal × List (Stmt Op))
    | [] => []
    | (literal, body) :: cases =>
        (literal, resolveForLayoutStmts L body) :: resolveForLayoutCases L cases
    termination_by cases => 2 * sizeOf cases
end

def resolveForLayoutDecl (L : Layout) (decl : FDecl evm) : FDecl evm :=
  { decl with body := resolveForLayoutStmts L decl.body }

def resolveForLayoutScope (L : Layout) (scope : FScope evm) : FScope evm :=
  scope.map fun entry => (entry.1, resolveForLayoutDecl L entry.2)

def resolveForLayoutFuns (L : Layout) (funs : FunEnv evm) : FunEnv evm :=
  funs.map (resolveForLayoutScope L)

def resolveForLayoutCode (L : Layout) : Code Op → Code Op
  | .expr expression => .expr (resolveForLayoutExpr L expression)
  | .args expressions => .args (resolveForLayoutExprs L expressions)
  | .stmt statement => .stmt (resolveForLayoutStmt L statement)
  | .stmts statements => .stmts (resolveForLayoutStmts L statements)
  | .loop condition post body => .loop (resolveForLayoutExpr L condition)
      (resolveForLayoutStmts L post) (resolveForLayoutStmts L body)

@[simp] theorem resolveForLayoutCode_expr (L : Layout) (expression : Expr Op) :
    resolveForLayoutCode L (.expr expression) =
      .expr (resolveForLayoutExpr L expression) := rfl

@[simp] theorem resolveForLayoutCode_args (L : Layout) (expressions : List (Expr Op)) :
    resolveForLayoutCode L (.args expressions) =
      .args (resolveForLayoutExprs L expressions) := rfl

@[simp] theorem resolveForLayoutCode_stmt (L : Layout) (statement : Stmt Op) :
    resolveForLayoutCode L (.stmt statement) =
      .stmt (resolveForLayoutStmt L statement) := rfl

@[simp] theorem resolveForLayoutCode_stmts (L : Layout) (statements : Block Op) :
    resolveForLayoutCode L (.stmts statements) =
      .stmts (resolveForLayoutStmts L statements) := rfl

@[simp] theorem resolveForLayoutCode_loop (L : Layout) (condition : Expr Op)
    (post body : Block Op) :
    resolveForLayoutCode L (.loop condition post body) =
      .loop (resolveForLayoutExpr L condition)
        (resolveForLayoutStmts L post) (resolveForLayoutStmts L body) := rfl

@[simp] theorem resolveForLayoutStmt_block (L : Layout) (body : Block Op) :
    resolveForLayoutStmt L (.block body) = .block (resolveForLayoutStmts L body) := by
  rw [resolveForLayoutStmt.eq_def]

@[simp] theorem resolveForLayoutStmt_funDef (L : Layout) (name : Ident)
    (params returns : List Ident) (body : Block Op) :
    resolveForLayoutStmt L (.funDef name params returns body) =
      .funDef name params returns (resolveForLayoutStmts L body) := by
  rw [resolveForLayoutStmt.eq_def]

@[simp] theorem resolveForLayoutStmt_letDecl (L : Layout) (names : List Ident)
    (value : Option (Expr Op)) :
    resolveForLayoutStmt L (.letDecl names value) =
      .letDecl names (value.map (resolveForLayoutExpr L)) := by
  rw [resolveForLayoutStmt.eq_def]

@[simp] theorem resolveForLayoutStmt_assign (L : Layout) (names : List Ident)
    (value : Expr Op) :
    resolveForLayoutStmt L (.assign names value) =
      .assign names (resolveForLayoutExpr L value) := by
  rw [resolveForLayoutStmt.eq_def]

@[simp] theorem resolveForLayoutStmt_cond (L : Layout) (condition : Expr Op)
    (body : Block Op) :
    resolveForLayoutStmt L (.cond condition body) =
      .cond (resolveForLayoutExpr L condition) (resolveForLayoutStmts L body) := by
  rw [resolveForLayoutStmt.eq_def]

@[simp] theorem resolveForLayoutStmt_switch (L : Layout) (condition : Expr Op)
    (cases : List (Literal × Block Op)) (fallback : Option (Block Op)) :
    resolveForLayoutStmt L (.switch condition cases fallback) =
      .switch (resolveForLayoutExpr L condition) (resolveForLayoutCases L cases)
        (fallback.map (resolveForLayoutStmts L)) := by
  rw [resolveForLayoutStmt.eq_def]
  cases fallback <;> rfl

@[simp] theorem resolveForLayoutStmt_forLoop (L : Layout) (init : Block Op)
    (condition : Expr Op) (post body : Block Op) :
    resolveForLayoutStmt L (.forLoop init condition post body) =
      .forLoop (resolveForLayoutStmts L init) (resolveForLayoutExpr L condition)
        (resolveForLayoutStmts L post) (resolveForLayoutStmts L body) := by
  rw [resolveForLayoutStmt.eq_def]

@[simp] theorem resolveForLayoutStmt_exprStmt (L : Layout) (expression : Expr Op) :
    resolveForLayoutStmt L (.exprStmt expression) =
      .exprStmt (resolveForLayoutExpr L expression) := by
  rw [resolveForLayoutStmt.eq_def]

@[simp] theorem resolveForLayoutStmt_break (L : Layout) :
    resolveForLayoutStmt L .«break» = .«break» := by
  rw [resolveForLayoutStmt.eq_def]

@[simp] theorem resolveForLayoutStmt_continue (L : Layout) :
    resolveForLayoutStmt L .«continue» = .«continue» := by
  rw [resolveForLayoutStmt.eq_def]

@[simp] theorem resolveForLayoutStmt_leave (L : Layout) :
    resolveForLayoutStmt L .leave = .leave := by
  rw [resolveForLayoutStmt.eq_def]

@[simp] theorem resolveForLayoutStmts_nil (L : Layout) :
    resolveForLayoutStmts L [] = [] := by
  rw [resolveForLayoutStmts]

@[simp] theorem resolveForLayoutStmts_cons (L : Layout) (statement : Stmt Op)
    (statements : Block Op) :
    resolveForLayoutStmts L (statement :: statements) =
      resolveForLayoutStmt L statement :: resolveForLayoutStmts L statements := by
  rw [resolveForLayoutStmts]

/-- The state is executing with the object maps selected by `L`. -/
def UsesLayout (L : Layout) (st : EvmState) : Prop :=
  st.env.dataOffset = L.dataOffset ∧ st.env.dataSize = L.dataSize

private theorem find_scope_resolved (L : Layout) (scope : FScope evm) (fn : Ident) :
    (resolveForLayoutScope L scope).find? (fun p => p.1 = fn) =
      (scope.find? (fun p => p.1 = fn)).map
        (fun p => (p.1, resolveForLayoutDecl L p.2)) := by
  induction scope with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨name, decl⟩
      change List.find? (fun p => p.1 = fn)
          ((name, resolveForLayoutDecl L decl) :: resolveForLayoutScope L rest) = _
      simp only [List.find?_cons]
      by_cases h : name = fn
      · simp [h]
      · simp [h, ih]

theorem lookupFun_resolveForLayout {funs : FunEnv evm} {fn : Ident}
    {decl : FDecl evm} {cenv : FunEnv evm}
    (h : lookupFun funs fn = some (decl, cenv)) (L : Layout) :
    lookupFun (resolveForLayoutFuns L funs) fn =
      some (resolveForLayoutDecl L decl, resolveForLayoutFuns L cenv) := by
  induction funs with
  | nil => simp [lookupFun] at h
  | cons scope rest ih =>
      simp only [lookupFun] at h
      rw [show resolveForLayoutFuns L (scope :: rest) =
        resolveForLayoutScope L scope :: resolveForLayoutFuns L rest from rfl]
      simp only [lookupFun]
      rw [find_scope_resolved]
      cases hs : scope.find? (fun p => p.1 = fn) with
      | none =>
          simp only [Option.map_none]
          simp [hs] at h
          exact ih h
      | some entry =>
          simp only [Option.map_some]
          rcases entry with ⟨name, found⟩
          simp [hs] at h
          simp only [Option.some.injEq] at h ⊢
          rcases h with ⟨hdecl, hcenv⟩
          subst decl
          subst cenv
          rfl

theorem hoist_resolveForLayout (L : Layout) (body : Block Op) :
    hoist evm (resolveForLayoutStmts L body) =
      resolveForLayoutScope L (hoist evm body) := by
  induction body with
  | nil => rw [resolveForLayoutStmts]; rfl
  | cons statement rest ih =>
      rw [resolveForLayoutStmts]
      cases statement <;>
        rw [resolveForLayoutStmt.eq_def] <;>
        simp only [hoist, List.filterMap_cons, resolveForLayoutScope,
          List.map_cons, resolveForLayoutDecl] <;>
        simpa [hoist, resolveForLayoutScope, resolveForLayoutDecl] using ih

private theorem selectSwitch_resolveForLayout (L : Layout) (value : U256)
    (cases : List (Literal × Block Op)) (fallback : Option (Block Op)) :
    resolveForLayoutStmts L (selectSwitch evm value cases fallback) =
      selectSwitch evm value (resolveForLayoutCases L cases)
        (fallback.map (resolveForLayoutStmts L)) := by
  induction cases with
  | nil => cases fallback <;>
      simp [selectSwitch, resolveForLayoutCases]
  | cons head rest ih =>
      rcases head with ⟨literal, body⟩
      by_cases h : decide (value = litValue literal) = true
      · simp [selectSwitch, resolveForLayoutCases, h]
      · simpa [selectSwitch, resolveForLayoutCases, h] using ih

private def SameEnvResult (st : EvmState) :
    BuiltinResult U256 EvmState → Prop
  | .ok _ st' => st'.env.dataOffset = st.env.dataOffset ∧
      st'.env.dataSize = st.env.dataSize
  | .halt st' => st'.env.dataOffset = st.env.dataOffset ∧
      st'.env.dataSize = st.env.dataSize

private theorem un_sameEnv (f : U256 → U256) (args : List U256)
    (st : EvmState) {r} (h : YulSemantics.EVM.un f args st = some r) :
    SameEnvResult st r := by
  cases args with
  | nil => simp [YulSemantics.EVM.un] at h
  | cons a rest =>
      cases rest with
      | nil => simp [YulSemantics.EVM.un] at h; cases h; exact ⟨rfl, rfl⟩
      | cons => simp [YulSemantics.EVM.un] at h

private theorem bin_sameEnv (f : U256 → U256 → U256) (args : List U256)
    (st : EvmState) {r} (h : YulSemantics.EVM.bin f args st = some r) :
    SameEnvResult st r := by
  cases args with
  | nil => simp [YulSemantics.EVM.bin] at h
  | cons a rest =>
      cases rest with
      | nil => simp [YulSemantics.EVM.bin] at h
      | cons b rest =>
          cases rest with
          | nil => simp [YulSemantics.EVM.bin] at h; cases h; exact ⟨rfl, rfl⟩
          | cons => simp [YulSemantics.EVM.bin] at h

private theorem ter_sameEnv (f : U256 → U256 → U256 → U256)
    (args : List U256) (st : EvmState) {r}
    (h : YulSemantics.EVM.ter f args st = some r) : SameEnvResult st r := by
  cases args with
  | nil => simp [YulSemantics.EVM.ter] at h
  | cons a rest =>
      cases rest with
      | nil => simp [YulSemantics.EVM.ter] at h
      | cons b rest =>
          cases rest with
          | nil => simp [YulSemantics.EVM.ter] at h
          | cons c rest =>
              cases rest with
              | nil => simp [YulSemantics.EVM.ter] at h; cases h; exact ⟨rfl, rfl⟩
              | cons => simp [YulSemantics.EVM.ter] at h

private theorem rd0_sameEnv (value : U256) (args : List U256)
    (st : EvmState) {r} (h : YulSemantics.EVM.rd0 value args st = some r) :
    SameEnvResult st r := by
  cases args with
  | nil => simp [YulSemantics.EVM.rd0] at h; cases h; exact ⟨rfl, rfl⟩
  | cons => simp [YulSemantics.EVM.rd0] at h

private theorem rd1_sameEnv (f : U256 → U256) (args : List U256)
    (st : EvmState) {r} (h : YulSemantics.EVM.rd1 f args st = some r) :
    SameEnvResult st r := by
  cases args with
  | nil => simp [YulSemantics.EVM.rd1] at h
  | cons a rest =>
      cases rest with
      | nil => simp [YulSemantics.EVM.rd1] at h; cases h; exact ⟨rfl, rfl⟩
      | cons => simp [YulSemantics.EVM.rd1] at h

private theorem stepOp_sameEnv {op : Op} {args : List U256}
    {st : EvmState} {r} (h : stepOp op args st = some r) :
    SameEnvResult st r := by
  cases op <;> simp only [stepOp, YulSemantics.EVM.guardStatic] at h <;>
    first
    | exact un_sameEnv _ _ _ h
    | exact bin_sameEnv _ _ _ h
    | exact ter_sameEnv _ _ _ h
    | exact rd0_sameEnv _ _ _ h
    | exact rd1_sameEnv _ _ _ h
    | (repeat' split at h) <;>
        simp_all [SameEnvResult, YulSemantics.EVM.appendLog] <;>
        try { cases h; exact ⟨rfl, rfl⟩ }

private theorem stepOp_ok_env {op : Op} {args returns : List U256}
    {st st' : EvmState} (h : stepOp op args st = some (.ok returns st')) :
    st'.env.dataOffset = st.env.dataOffset ∧
      st'.env.dataSize = st.env.dataSize := stepOp_sameEnv h

private theorem stepOp_halt_env {op : Op} {args : List U256}
    {st st' : EvmState} (h : stepOp op args st = some (.halt st')) :
    st'.env.dataOffset = st.env.dataOffset ∧
      st'.env.dataSize = st.env.dataSize := stepOp_sameEnv h

/-- Every executable Yul step preserves the immutable object-layout maps. -/
theorem evmStep_env {funs : FunEnv evm} {V : VEnv evm} {st : EvmState}
    {code : Code Op} {res : Res evm} (h : Step evm funs V st code res) :
    match res with
    | .eres (.vals _ st') => st'.env.dataOffset = st.env.dataOffset ∧
        st'.env.dataSize = st.env.dataSize
    | .eres (.halt st') => st'.env.dataOffset = st.env.dataOffset ∧
        st'.env.dataSize = st.env.dataSize
    | .sres _ st' _ => st'.env.dataOffset = st.env.dataOffset ∧
        st'.env.dataSize = st.env.dataSize := by
  induction h <;> simp_all
  case builtinOk hargs hbuiltin ih =>
    exact ⟨(stepOp_ok_env hbuiltin).1.trans ih.1,
      (stepOp_ok_env hbuiltin).2.trans ih.2⟩
  case builtinHalt hargs hbuiltin ih =>
    exact ⟨(stepOp_halt_env hbuiltin).1.trans ih.1,
      (stepOp_halt_env hbuiltin).2.trans ih.2⟩

private theorem resolveForLayoutExpr_builtin_other (L : Layout) (op : Op)
    (args : List (Expr Op))
    (hoff : ∀ name, op ≠ .dataoffset ∨ args ≠ [.lit (.string name)])
    (hsize : ∀ name, op ≠ .datasize ∨ args ≠ [.lit (.string name)]) :
    resolveForLayoutExpr L (.builtin op args) =
      .builtin op (resolveForLayoutExprs L args) := by
  cases op <;> try rfl
  · case datasize =>
      cases args with
      | nil => rfl
      | cons expression rest =>
          cases expression <;> try rfl
          case lit literal =>
            cases literal <;> try rfl
            case string name =>
              cases rest with
              | nil => exfalso; simpa using hsize name
              | cons => rfl
  · case dataoffset =>
      cases args with
      | nil => rfl
      | cons expression rest =>
          cases expression <;> try rfl
          case lit literal =>
            cases literal <;> try rfl
            case string name =>
              cases rest with
              | nil => exfalso; simpa using hoff name
              | cons => rfl

private theorem literalArgs_det {funs : FunEnv evm} {V : VEnv evm}
    {st st' : EvmState} {name : String} {values : List U256}
    (h : Step evm funs V st (.args [.lit (.string name)])
      (.eres (.vals values st'))) :
    values = [litValue (.string name)] ∧ st' = st := by
  have canonical : Step evm funs V st (.args [.lit (.string name)])
      (.eres (.vals [litValue (.string name)] st)) :=
    .argsCons .argsNil .lit
  have heq := Step.det YulSemantics.EVM.evm_deterministic h canonical
  injection heq with hinner
  injection hinner with hvalues hstate
  exact ⟨hvalues, hstate⟩

private theorem UsesLayout.after_vals {L : Layout} {funs : FunEnv evm}
    {V : VEnv evm} {st st' : EvmState} {expressions : List (Expr Op)} {values}
    (hL : UsesLayout L st)
    (h : Step evm funs V st (.args expressions) (.eres (.vals values st'))) :
    UsesLayout L st' := by
  have henv := evmStep_env h
  exact ⟨henv.1.trans hL.1, henv.2.trans hL.2⟩

private theorem UsesLayout.after_expr_vals {L : Layout} {funs : FunEnv evm}
    {V : VEnv evm} {st st' : EvmState} {expression : Expr Op} {values}
    (hL : UsesLayout L st)
    (h : Step evm funs V st (.expr expression) (.eres (.vals values st'))) :
    UsesLayout L st' := by
  have henv := evmStep_env h
  exact ⟨henv.1.trans hL.1, henv.2.trans hL.2⟩

private theorem UsesLayout.after_stmt {L : Layout} {funs : FunEnv evm}
    {V V' : VEnv evm} {st st' : EvmState} {statement : Stmt Op} {outcome}
    (hL : UsesLayout L st)
    (h : Step evm funs V st (.stmt statement) (.sres V' st' outcome)) :
    UsesLayout L st' := by
  have henv := evmStep_env h
  exact ⟨henv.1.trans hL.1, henv.2.trans hL.2⟩

private theorem UsesLayout.after_stmts {L : Layout} {funs : FunEnv evm}
    {V V' : VEnv evm} {st st' : EvmState} {statements : Block Op} {outcome}
    (hL : UsesLayout L st)
    (h : Step evm funs V st (.stmts statements) (.sres V' st' outcome)) :
    UsesLayout L st' := by
  have henv := evmStep_env h
  exact ⟨henv.1.trans hL.1, henv.2.trans hL.2⟩

private theorem UsesLayout.after_loop {L : Layout} {funs : FunEnv evm}
    {V V' : VEnv evm} {st st' : EvmState} {condition : Expr Op}
    {post body : Block Op} {outcome}
    (hL : UsesLayout L st)
    (h : Step evm funs V st (.loop condition post body) (.sres V' st' outcome)) :
    UsesLayout L st' := by
  have henv := evmStep_env h
  exact ⟨henv.1.trans hL.1, henv.2.trans hL.2⟩

private theorem not_offset_ref {op : Op} {args : List (Expr Op)}
    (h : ¬ ∃ name, op = .dataoffset ∧ args = [.lit (.string name)]) :
    ∀ name, op ≠ .dataoffset ∨ args ≠ [.lit (.string name)] := by
  intro name
  by_contra hn
  push Not at hn
  exact h ⟨name, hn⟩

private theorem not_size_ref {op : Op} {args : List (Expr Op)}
    (h : ¬ ∃ name, op = .datasize ∧ args = [.lit (.string name)]) :
    ∀ name, op ≠ .datasize ∨ args ≠ [.lit (.string name)] := by
  intro name
  by_contra hn
  push Not at hn
  exact h ⟨name, hn⟩

/-- Replacing object-layout reads by the selected layout's concrete words
preserves every Yul derivation, including calls into transformed hoisted
function bodies. -/
theorem resolveForLayout_step (L : Layout)
    {funs : FunEnv evm} {V : VEnv evm} {st : EvmState}
    {code : Code Op} {res : Res evm}
    (hL : UsesLayout L st) (h : Step evm funs V st code res) :
    Step evm (resolveForLayoutFuns L funs) V st
      (resolveForLayoutCode L code) res := by
  revert hL
  induction h with
  | lit =>
      intro _
      exact .lit
  | var hget =>
      intro _
      exact .var hget
  | @builtinOk funs V st op args argvals st1 returns st2 hargs hop ih =>
      intro hL
      by_cases hoff : ∃ name, op = .dataoffset ∧ args = [.lit (.string name)]
      · obtain ⟨name, rfl, rfl⟩ := hoff
        obtain ⟨rfl, rfl⟩ := literalArgs_det hargs
        simp only [stepOp, YulSemantics.EVM.rd1, Option.some.injEq,
          BuiltinResult.ok.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        have hmap : L.dataOffset (litValue (.string name)) =
            st1.env.dataOffset (litValue (.string name)) :=
          (congrFun hL.1 _).symm
        have hword : evm.litValue (.number
              (L.dataOffset (litValue (.string name))).toNat) =
            st1.env.dataOffset (litValue (.string name)) := by
          simpa [litValue] using hmap
        have hlit :=
          Step.lit (D := evm) (funs := resolveForLayoutFuns L funs)
            (V := V) (st := st1) (l := .number
              (L.dataOffset (litValue (.string name))).toNat)
        rw [hword] at hlit
        simpa [resolveForLayoutCode, resolveForLayoutExpr, litValue] using hlit
      · by_cases hsize : ∃ name, op = .datasize ∧ args = [.lit (.string name)]
        · obtain ⟨name, rfl, rfl⟩ := hsize
          obtain ⟨rfl, rfl⟩ := literalArgs_det hargs
          simp only [stepOp, YulSemantics.EVM.rd1, Option.some.injEq,
            BuiltinResult.ok.injEq] at hop
          obtain ⟨rfl, rfl⟩ := hop
          have hmap : L.dataSize (litValue (.string name)) =
              st1.env.dataSize (litValue (.string name)) :=
            (congrFun hL.2 _).symm
          have hword : evm.litValue (.number
                (L.dataSize (litValue (.string name))).toNat) =
              st1.env.dataSize (litValue (.string name)) := by
            simpa [litValue] using hmap
          have hlit :=
            Step.lit (D := evm) (funs := resolveForLayoutFuns L funs)
              (V := V) (st := st1) (l := .number
                (L.dataSize (litValue (.string name))).toNat)
          rw [hword] at hlit
          simpa [resolveForLayoutCode, resolveForLayoutExpr, litValue] using hlit
        · rw [resolveForLayoutCode,
            resolveForLayoutExpr_builtin_other L op args
              (not_offset_ref hoff) (not_size_ref hsize)]
          exact .builtinOk (ih hL) hop
  | @builtinHalt funs V st op args argvals st1 st2 hargs hop ih =>
      intro hL
      by_cases hoff : ∃ name, op = .dataoffset ∧ args = [.lit (.string name)]
      · obtain ⟨name, rfl, rfl⟩ := hoff
        obtain ⟨rfl, rfl⟩ := literalArgs_det hargs
        simp [stepOp, YulSemantics.EVM.rd1] at hop
      · by_cases hsize : ∃ name, op = .datasize ∧ args = [.lit (.string name)]
        · obtain ⟨name, rfl, rfl⟩ := hsize
          obtain ⟨rfl, rfl⟩ := literalArgs_det hargs
          simp [stepOp, YulSemantics.EVM.rd1] at hop
        · rw [resolveForLayoutCode,
            resolveForLayoutExpr_builtin_other L op args
              (not_offset_ref hoff) (not_size_ref hsize)]
          exact .builtinHalt (ih hL) hop
  | @builtinArgsHalt funs V st op args st1 hargs ih =>
      intro hL
      by_cases hoff : ∃ name, op = .dataoffset ∧ args = [.lit (.string name)]
      · obtain ⟨name, rfl, rfl⟩ := hoff
        have canonical : Step evm funs V st (.args [.lit (.string name)])
            (.eres (.vals [litValue (.string name)] st)) :=
          .argsCons .argsNil .lit
        have := Step.det YulSemantics.EVM.evm_deterministic hargs canonical
        contradiction
      · by_cases hsize : ∃ name, op = .datasize ∧ args = [.lit (.string name)]
        · obtain ⟨name, rfl, rfl⟩ := hsize
          have canonical : Step evm funs V st (.args [.lit (.string name)])
              (.eres (.vals [litValue (.string name)] st)) :=
            .argsCons .argsNil .lit
          have := Step.det YulSemantics.EVM.evm_deterministic hargs canonical
          contradiction
        · rw [resolveForLayoutCode,
            resolveForLayoutExpr_builtin_other L op args
              (not_offset_ref hoff) (not_size_ref hsize)]
          exact .builtinArgsHalt (ih hL)
  | @callOk funs V st fn args argvals st1 decl cenv Vend st2 outcome
      hargs hlookup hlen hbody hout ihArgs ihBody =>
      intro hL
      have hL1 := hL.after_vals hargs
      have hlookup' := lookupFun_resolveForLayout hlookup L
      have hbody' := ihBody hL1
      have hbody'' : Step evm (resolveForLayoutFuns L cenv)
          ((resolveForLayoutDecl L decl).params.zip argvals ++
            bindZeros evm (resolveForLayoutDecl L decl).rets) st1
          (.stmt (.block (resolveForLayoutDecl L decl).body))
          (.sres Vend st2 outcome) := by
        simpa [resolveForLayoutDecl] using hbody'
      simpa [resolveForLayoutCode, resolveForLayoutExpr,
        resolveForLayoutDecl, resolveForLayoutStmt.eq_def] using
          (Step.callOk (ihArgs hL) hlookup' hlen hbody'' hout)
  | @callHalt funs V st fn args argvals st1 decl cenv Vend st2
      hargs hlookup hlen hbody ihArgs ihBody =>
      intro hL
      have hL1 := hL.after_vals hargs
      have hlookup' := lookupFun_resolveForLayout hlookup L
      have hbody' := ihBody hL1
      have hbody'' : Step evm (resolveForLayoutFuns L cenv)
          ((resolveForLayoutDecl L decl).params.zip argvals ++
            bindZeros evm (resolveForLayoutDecl L decl).rets) st1
          (.stmt (.block (resolveForLayoutDecl L decl).body))
          (.sres Vend st2 .halt) := by
        simpa [resolveForLayoutDecl] using hbody'
      simpa [resolveForLayoutCode, resolveForLayoutExpr,
        resolveForLayoutDecl, resolveForLayoutStmt.eq_def] using
          (Step.callHalt (ihArgs hL) hlookup' hlen hbody'')
  | callArgsHalt hargs ih =>
      intro hL
      exact .callArgsHalt (ih hL)
  | argsNil =>
      intro _
      exact .argsNil
  | argsCons hrest hhead ihRest ihHead =>
      intro hL
      exact .argsCons (ihRest hL) (ihHead (hL.after_vals hrest))
  | argsRestHalt hrest ih =>
      intro hL
      exact .argsRestHalt (ih hL)
  | argsHeadHalt hrest hhead ihRest ihHead =>
      intro hL
      exact .argsHeadHalt (ihRest hL) (ihHead (hL.after_vals hrest))
  | funDef =>
      intro _
      simpa using (Step.funDef (D := evm))
  | block hbody ih =>
      intro hL
      have hbody' := ih hL
      rw [resolveForLayoutCode, resolveForLayoutStmt.eq_def]
      apply Step.block
      simpa [resolveForLayoutFuns, hoist_resolveForLayout] using hbody'
  | letZero =>
      intro _
      simpa using (Step.letZero (D := evm))
  | letVal hexpr hlen ih =>
      intro hL
      simpa using (Step.letVal (ih hL) hlen)
  | letHalt hexpr ih =>
      intro hL
      simpa using (Step.letHalt (ih hL))
  | assignVal hexpr hlen ih =>
      intro hL
      simpa using (Step.assignVal (ih hL) hlen)
  | assignHalt hexpr ih =>
      intro hL
      simpa using (Step.assignHalt (ih hL))
  | exprStmt hexpr ih =>
      intro hL
      simpa using (Step.exprStmt (ih hL))
  | exprStmtHalt hexpr ih =>
      intro hL
      simpa using (Step.exprStmtHalt (ih hL))
  | ifTrue hcond htrue hbody ihCond ihBody =>
      intro hL
      have hbody' := ihBody (hL.after_expr_vals hcond)
      simp only [resolveForLayoutCode_stmt, resolveForLayoutStmt_block] at hbody'
      simpa using (Step.ifTrue (ihCond hL) htrue hbody')
  | ifFalse hcond hfalse ih =>
      intro hL
      simpa using (Step.ifFalse (ih hL) hfalse)
  | ifHalt hcond ih =>
      intro hL
      simpa using (Step.ifHalt (ih hL))
  | switchExec hcond hbody ihCond ihBody =>
      intro hL
      rw [resolveForLayoutCode, resolveForLayoutStmt_switch]
      apply Step.switchExec (ihCond hL)
      have hbody' := ihBody (hL.after_expr_vals hcond)
      simpa [resolveForLayoutStmt.eq_def, selectSwitch_resolveForLayout] using hbody'
  | switchHalt hcond ih =>
      intro hL
      simpa using (Step.switchHalt (ih hL))
  | forLoop hinit hloop ihInit ihLoop =>
      intro hL
      rw [resolveForLayoutCode, resolveForLayoutStmt.eq_def]
      apply Step.forLoop
      · simpa [resolveForLayoutFuns, hoist_resolveForLayout] using ihInit hL
      · simpa [resolveForLayoutFuns, hoist_resolveForLayout] using
          ihLoop (hL.after_stmts hinit)
  | forInitHalt hinit ih =>
      intro hL
      rw [resolveForLayoutCode, resolveForLayoutStmt.eq_def]
      apply Step.forInitHalt
      simpa [resolveForLayoutFuns, hoist_resolveForLayout] using ih hL
  | «break» => intro _; simpa using (Step.break (D := evm))
  | «continue» => intro _; simpa using (Step.continue (D := evm))
  | «leave» => intro _; simpa using (Step.leave (D := evm))
  | seqNil => intro _; simpa using (Step.seqNil (D := evm))
  | seqCons hhead hrest ihHead ihRest =>
      intro hL
      simpa using (Step.seqCons (ihHead hL) (ihRest (hL.after_stmt hhead)))
  | seqStop hhead hstop ih =>
      intro hL
      simpa using (Step.seqStop (ih hL) hstop)
  | loopDone hcond hzero ih =>
      intro hL
      simpa using (Step.loopDone (ih hL) hzero)
  | loopCondHalt hcond ih =>
      intro hL
      simpa using (Step.loopCondHalt (ih hL))
  | loopStep hcond htrue hbody hcontinue hpost hloop
      ihCond ihBody ihPost ihLoop =>
      intro hL
      have hL1 := hL.after_expr_vals hcond
      have hL2 := hL1.after_stmt hbody
      have hL3 := hL2.after_stmt hpost
      have hbody' := ihBody hL1
      simp only [resolveForLayoutCode_stmt, resolveForLayoutStmt_block] at hbody'
      have hpost' := ihPost hL2
      simp only [resolveForLayoutCode_stmt, resolveForLayoutStmt_block] at hpost'
      simpa using (Step.loopStep (ihCond hL) htrue hbody' hcontinue
        hpost' (ihLoop hL3))
  | loopPostHalt hcond htrue hbody hcontinue hpost ihCond ihBody ihPost =>
      intro hL
      have hL1 := hL.after_expr_vals hcond
      have hL2 := hL1.after_stmt hbody
      have hbody' := ihBody hL1
      simp only [resolveForLayoutCode_stmt, resolveForLayoutStmt_block] at hbody'
      have hpost' := ihPost hL2
      simp only [resolveForLayoutCode_stmt, resolveForLayoutStmt_block] at hpost'
      simpa using (Step.loopPostHalt (ihCond hL) htrue hbody'
        hcontinue hpost')
  | loopBreak hcond htrue hbody ihCond ihBody =>
      intro hL
      have hbody' := ihBody (hL.after_expr_vals hcond)
      simp only [resolveForLayoutCode_stmt, resolveForLayoutStmt_block] at hbody'
      simpa using (Step.loopBreak (ihCond hL) htrue hbody')
  | loopLeave hcond htrue hbody ihCond ihBody =>
      intro hL
      have hbody' := ihBody (hL.after_expr_vals hcond)
      simp only [resolveForLayoutCode_stmt, resolveForLayoutStmt_block] at hbody'
      simpa using (Step.loopLeave (ihCond hL) htrue hbody')
  | loopBodyHalt hcond htrue hbody ihCond ihBody =>
      intro hL
      have hbody' := ihBody (hL.after_expr_vals hcond)
      simp only [resolveForLayoutCode_stmt, resolveForLayoutStmt_block] at hbody'
      simpa using (Step.loopBodyHalt (ihCond hL) htrue hbody')

/-- Whole-program form of `resolveForLayout_step`. -/
theorem resolveForLayout_run (L : Layout) {program : Block Op}
    {V : VEnv evm} {st st' : EvmState} {outcome : Outcome}
    (hL : UsesLayout L st)
    (h : Run evm program st V st' outcome) :
    Run evm (resolveForLayoutStmts L program) st V st' outcome := by
  simpa [Run, resolveForLayoutCode, resolveForLayoutFuns,
    resolveForLayoutStmt.eq_def] using resolveForLayout_step L hL h

end YulEvmCompiler
