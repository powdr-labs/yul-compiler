import YulEvmCompiler.Optimizer.Implementation.Simplify

set_option warningAsError true

/-!
# Scoped zero absorption

This pass implements the first optimization that is sound because of Core's
scope invariant rather than as an unconditional raw-Yul expression identity:
`mul(x, 0) → 0` and `mul(0, x) → 0`.

The raw source semantics gets stuck on an unbound `x`, so the rewrite is only
applied under a context whose names are known to occur in the runtime `VEnv`.
The statement traversal establishes that fact from preceding `let` bindings;
it deliberately forgets the context after other statements until the general
dataflow environment is introduced. Function bodies are processed from an
empty context, retaining whole-block soundness for arbitrary input ASTs.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM

variable {calls : ExternalCalls} {creates : ExternalCreates}
local notation "D" => evmWithExternal calls creates

namespace Core

/-- Absorb multiplication by zero on either side. -/
def absorbZeroRewrite {Γ : Ctx} : Term Γ 1 → Option (Term Γ 1)
  | .atom _ => none
  | .builtin op args =>
      match op with
      | .mul =>
          match args.values with
          | [.var _, .lit literal] | [.lit literal, .var _] =>
              if litValue literal = 0 then some (.atom (.lit (.number 0))) else none
          | _ => none
      | _ => none

/-- `mul(x, 0)` is equivalent to zero when the typed variable is bound. -/
theorem mul_var_zero_scoped (ref : Var Γ) (literal : Literal)
    (hzero : litValue literal = 0) :
    ScopedEquivExpr Γ
      (.builtin .mul [.var ref.name, .lit literal]) (.lit (.number 0)) := by
  intro calls creates funs V st result hbound
  obtain ⟨value, hget⟩ := hbound.get ref
  have hpure : pureFn .mul [value, litValue literal] = some 0 := by
    simp [pureFn, hzero]
  constructor
  · intro hstep
    cases hstep with
    | builtinOk hargs hbuiltin =>
        obtain ⟨actual, _, hresult⟩ := var_lit_inv hargs
        injection hresult with hvalues hstate
        subst hvalues
        subst hstate
        have hdet := pureFn_builtin_inv
          (calls := calls) (creates := creates)
          (op := Op.mul) (vs := [actual, litValue literal])
          (w := 0) (by simp [pureFn, hzero]) hbuiltin
        injection hdet with hvalues hstate
        subst hvalues
        subst hstate
        exact Step.lit
    | builtinHalt hargs hbuiltin =>
        obtain ⟨actual, _, hresult⟩ := var_lit_inv hargs
        injection hresult with hvalues hstate
        subst hvalues
        subst hstate
        have hdet := pureFn_builtin_inv
          (calls := calls) (creates := creates)
          (op := Op.mul) (vs := [actual, litValue literal])
          (w := 0) (by simp [pureFn, hzero]) hbuiltin
        contradiction
    | builtinArgsHalt hargs =>
        obtain ⟨_, _, hresult⟩ := var_lit_inv hargs
        contradiction
  · intro hstep
    cases hstep with
    | lit =>
        simpa [litValue] using
          (Step.builtinOk
            (Step.argsCons (Step.argsCons Step.argsNil Step.lit) (Step.var hget))
            (pureFn_builtin (calls := calls) (creates := creates) hpure _))

/-- `mul(0, x)` is equivalent to zero when the typed variable is bound. -/
theorem mul_zero_var_scoped (ref : Var Γ) (literal : Literal)
    (hzero : litValue literal = 0) :
    ScopedEquivExpr Γ
      (.builtin .mul [.lit literal, .var ref.name]) (.lit (.number 0)) := by
  intro calls creates funs V st result hbound
  obtain ⟨value, hget⟩ := hbound.get ref
  have hpure : pureFn .mul [litValue literal, value] = some 0 := by
    simp [pureFn, hzero]
  constructor
  · intro hstep
    cases hstep with
    | builtinOk hargs hbuiltin =>
        obtain ⟨actual, _, hresult⟩ := lit_var_inv hargs
        injection hresult with hvalues hstate
        subst hvalues
        subst hstate
        have hdet := pureFn_builtin_inv
          (calls := calls) (creates := creates)
          (op := Op.mul) (vs := [litValue literal, actual])
          (w := 0) (by simp [pureFn, hzero]) hbuiltin
        injection hdet with hvalues hstate
        subst hvalues
        subst hstate
        exact Step.lit
    | builtinHalt hargs hbuiltin =>
        obtain ⟨actual, _, hresult⟩ := lit_var_inv hargs
        injection hresult with hvalues hstate
        subst hvalues
        subst hstate
        have hdet := pureFn_builtin_inv
          (calls := calls) (creates := creates)
          (op := Op.mul) (vs := [litValue literal, actual])
          (w := 0) (by simp [pureFn, hzero]) hbuiltin
        contradiction
    | builtinArgsHalt hargs =>
        obtain ⟨_, _, hresult⟩ := lit_var_inv hargs
        contradiction
  · intro hstep
    cases hstep with
    | lit =>
        simpa [litValue] using
          (Step.builtinOk
            (Step.argsCons (Step.argsCons Step.argsNil (Step.var hget)) Step.lit)
            (pureFn_builtin (calls := calls) (creates := creates) hpure _))

/-- The zero-absorption rewrite carries its scoped soundness proof. -/
theorem absorbZeroRewrite_sound {input output : Term Γ 1}
    (h : absorbZeroRewrite input = some output) :
    ScopedEquivExpr Γ input.emit output.emit := by
  cases input with
  | atom value => simp [absorbZeroRewrite] at h
  | builtin op args =>
      cases op <;> try simp [absorbZeroRewrite] at h
      case mul =>
        cases hvalues : args.values with
        | nil => simp [hvalues] at h
        | cons first rest =>
            cases rest with
            | nil => simp [hvalues] at h
            | cons second tail =>
                cases tail with
                | cons third tail => simp [hvalues] at h
                | nil =>
                    cases first <;> cases second <;>
                      simp [hvalues] at h
                    · rename_i literal ref
                      obtain ⟨hzero, rfl⟩ := h
                      intro calls creates funs V st result hbound
                      simpa [Term.emit, Args.emit, Value.emit, Var.emit, PureOp.toOp, hvalues]
                        using (mul_zero_var_scoped ref literal hzero
                          (calls := calls) (creates := creates) funs V st result hbound)
                    · rename_i ref literal
                      obtain ⟨hzero, rfl⟩ := h
                      intro calls creates funs V st result hbound
                      simpa [Term.emit, Args.emit, Value.emit, Var.emit, PureOp.toOp, hvalues]
                        using (mul_var_zero_scoped ref literal hzero
                          (calls := calls) (creates := creates) funs V st result hbound)

/-- The proved absorption rule. -/
def absorbZeroRule : ScopedRule where
  rewrite := absorbZeroRewrite
  sound := absorbZeroRewrite_sound

/-- Current scoped simplification policy. -/
def scopedRules : List ScopedRule := [absorbZeroRule]

end Core

/-- Apply scoped Core rules to a flat expression, or leave unsupported syntax
unchanged. -/
def absorbZeroExpr (Γ : Core.Ctx) (source : Expr Op) : Expr Op :=
  match Core.ingest Γ source with
  | some core => (Core.scopedRun Core.scopedRules core).emit
  | none => source

/-- Expression absorption is sound when the Core context is runtime-bound. -/
theorem absorbZeroExpr_sound (Γ : Core.Ctx) (source : Expr Op) :
    Core.ScopedEquivExpr Γ source (absorbZeroExpr Γ source) := by
  intro calls creates funs V st result hbound
  simp only [absorbZeroExpr]
  cases hcore : Core.ingest Γ source with
  | none => simp
  | some core =>
      have herase := Core.ingest_emit hcore
      simpa only [herase] using
        (Core.scopedRun_sound Core.scopedRules core
          (calls := calls) (creates := creates) funs V st result hbound)

/-! ## Context-tracking statement traversal -/

/-- The next statement may rely on bindings introduced by a preceding `let`.
After any other statement the conservative first implementation forgets its
context rather than proving general environment preservation. -/
def absorbNextCtx (Γ : Core.Ctx) : Stmt Op → Core.Ctx
  | .letDecl vars _ => vars ++ Γ
  | _ => []

mutual
  /-- Rewrite expression positions whose current context is known. -/
  def absorbZeroStmt (Γ : Core.Ctx) : Stmt Op → Stmt Op
    | .funDef name params rets body =>
        .funDef name params rets (absorbZeroStmts [] body)
    | .letDecl vars (some value) =>
        .letDecl vars (some (absorbZeroExpr Γ value))
    | .assign vars value => .assign vars (absorbZeroExpr Γ value)
    | .exprStmt value => .exprStmt (absorbZeroExpr Γ value)
    | stmt => stmt

  /-- Track bindings through consecutive declarations and one following
  statement. -/
  def absorbZeroStmts (Γ : Core.Ctx) : Block Op → Block Op
    | [] => []
    | stmt :: rest =>
        absorbZeroStmt Γ stmt :: absorbZeroStmts (absorbNextCtx Γ stmt) rest
end

/-- Scoped statement equivalence. -/
def ScopedEquivStmt (Γ : Core.Ctx) (left right : Stmt Op) : Prop :=
  ∀ {calls : ExternalCalls} {creates : ExternalCreates} funs V st V' st' outcome,
    Core.VarsBound Γ V →
    (Step (evmWithExternal calls creates) funs V st (.stmt left)
        (.sres V' st' outcome) ↔
      Step (evmWithExternal calls creates) funs V st (.stmt right)
        (.sres V' st' outcome))

/-- Scoped sequence equivalence. -/
def ScopedEquivStmts (Γ : Core.Ctx) (left right : Block Op) : Prop :=
  ∀ {calls : ExternalCalls} {creates : ExternalCreates} funs V st V' st' outcome,
    Core.VarsBound Γ V →
    (Step (evmWithExternal calls creates) funs V st (.stmts left)
        (.sres V' st' outcome) ↔
      Step (evmWithExternal calls creates) funs V st (.stmts right)
        (.sres V' st' outcome))

theorem varsBound_nil (V : VEnv D) : Core.VarsBound [] V := by simp [Core.VarsBound]

/-- Normal completion of a `let` realizes its newly extended Core context. -/
theorem varsBound_after_let {Γ vars init funs V st V' st'}
    (hbound : Core.VarsBound Γ V)
    (hstep : Step D funs V st (.stmt (.letDecl vars init)) (.sres V' st' .normal)) :
    Core.VarsBound (vars ++ Γ) V' := by
  cases hstep with
  | letZero =>
      intro name hname
      simp only [List.mem_append] at hname
      simp only [bindZeros, List.map_append, List.map_map, List.mem_append]
      rcases hname with hnew | hold
      · left
        simpa using hnew
      · exact Or.inr (hbound name hold)
  | letVal _ hlen =>
      intro name hname
      simp only [List.mem_append] at hname
      simp only [List.map_append, List.mem_append]
      rcases hname with hnew | hold
      · left
        rw [List.map_fst_zip (by omega)]
        exact hnew
      · exact Or.inr (hbound name hold)

/-- The syntactic next-context policy is realized after normal execution. -/
theorem absorbNextCtx_bound {Γ funs V st stmt V' st'}
    (hbound : Core.VarsBound Γ V)
    (hstep : Step D funs V st (.stmt stmt) (.sres V' st' .normal)) :
    Core.VarsBound (absorbNextCtx Γ stmt) V' := by
  cases stmt <;> try exact varsBound_nil V'
  case letDecl vars init => exact varsBound_after_let hbound hstep

/-- Each transformed statement is equivalent under its realized context. -/
theorem absorbZeroStmt_sound (Γ : Core.Ctx) (stmt : Stmt Op) :
    ScopedEquivStmt Γ stmt (absorbZeroStmt Γ stmt) := by
  intro calls creates funs V st V' st' outcome hbound
  cases stmt with
  | funDef name params rets body =>
      constructor <;> (intro h; cases h; exact Step.funDef)
  | letDecl vars init =>
      cases init with
      | none => simp [absorbZeroStmt]
      | some value =>
          constructor
          · intro h
            cases h with
            | letVal hvalue hlen =>
                exact Step.letVal
                  ((absorbZeroExpr_sound Γ value funs V st _ hbound).mp hvalue) hlen
            | letHalt hvalue =>
                exact Step.letHalt
                  ((absorbZeroExpr_sound Γ value funs V st _ hbound).mp hvalue)
          · intro h
            cases h with
            | letVal hvalue hlen =>
                exact Step.letVal
                  ((absorbZeroExpr_sound Γ value funs V st _ hbound).mpr hvalue) hlen
            | letHalt hvalue =>
                exact Step.letHalt
                  ((absorbZeroExpr_sound Γ value funs V st _ hbound).mpr hvalue)
  | assign vars value =>
      constructor
      · intro h
        cases h with
        | assignVal hvalue hlen =>
            exact Step.assignVal
              ((absorbZeroExpr_sound Γ value funs V st _ hbound).mp hvalue) hlen
        | assignHalt hvalue =>
            exact Step.assignHalt
              ((absorbZeroExpr_sound Γ value funs V st _ hbound).mp hvalue)
      · intro h
        cases h with
        | assignVal hvalue hlen =>
            exact Step.assignVal
              ((absorbZeroExpr_sound Γ value funs V st _ hbound).mpr hvalue) hlen
        | assignHalt hvalue =>
            exact Step.assignHalt
              ((absorbZeroExpr_sound Γ value funs V st _ hbound).mpr hvalue)
  | exprStmt value =>
      constructor
      · intro h
        cases h with
        | exprStmt hvalue =>
            exact Step.exprStmt
              ((absorbZeroExpr_sound Γ value funs V st _ hbound).mp hvalue)
        | exprStmtHalt hvalue =>
            exact Step.exprStmtHalt
              ((absorbZeroExpr_sound Γ value funs V st _ hbound).mp hvalue)
      · intro h
        cases h with
        | exprStmt hvalue =>
            exact Step.exprStmt
              ((absorbZeroExpr_sound Γ value funs V st _ hbound).mpr hvalue)
        | exprStmtHalt hvalue =>
            exact Step.exprStmtHalt
              ((absorbZeroExpr_sound Γ value funs V st _ hbound).mpr hvalue)
  | block body => simp [absorbZeroStmt]
  | cond condition body => simp [absorbZeroStmt]
  | switch condition cases dflt => simp [absorbZeroStmt]
  | forLoop init condition post body => simp [absorbZeroStmt]
  | «break» => simp [absorbZeroStmt]
  | «continue» => simp [absorbZeroStmt]
  | leave => simp [absorbZeroStmt]

/-- Context-tracking absorption preserves statement-sequence execution. -/
theorem absorbZeroStmts_sound (Γ : Core.Ctx) (stmts : Block Op) :
    ScopedEquivStmts Γ stmts (absorbZeroStmts Γ stmts) := by
  intro calls creates funs V st V' st' outcome hbound
  induction stmts generalizing V st V' st' outcome Γ with
  | nil => simp [absorbZeroStmts]
  | cons stmt rest ih =>
      constructor
      · intro h
        cases h with
        | seqCons hstmt hrest =>
            have hstmt' := (absorbZeroStmt_sound Γ stmt funs V st _ _ _ hbound).mp hstmt
            have hnext := absorbNextCtx_bound hbound hstmt
            exact Step.seqCons hstmt'
              ((ih (absorbNextCtx Γ stmt) _ _ _ _ _ hnext).mp hrest)
        | seqStop hstmt hnormal =>
            exact Step.seqStop
              ((absorbZeroStmt_sound Γ stmt funs V st _ _ _ hbound).mp hstmt) hnormal
      · intro h
        cases h with
        | seqCons hstmt hrest =>
            have hstmt' := (absorbZeroStmt_sound Γ stmt funs V st _ _ _ hbound).mpr hstmt
            have hnext := absorbNextCtx_bound hbound hstmt'
            exact Step.seqCons hstmt'
              ((ih (absorbNextCtx Γ stmt) _ _ _ _ _ hnext).mpr hrest)
        | seqStop hstmt hnormal =>
            exact Step.seqStop
              ((absorbZeroStmt_sound Γ stmt funs V st _ _ _ hbound).mpr hstmt) hnormal

/-- An empty Core context is realized by every environment, so the scoped
sequence theorem becomes ordinary pointwise equivalence. -/
theorem absorbZeroStmts_equiv (stmts : Block Op) :
    EquivStmts D stmts (absorbZeroStmts [] stmts) := by
  intro funs V st V' st' outcome
  exact absorbZeroStmts_sound [] stmts funs V st V' st' outcome (varsBound_nil V)

mutual

/-- A whole block is equivalent to scoped zero absorption started without
assumptions about its incoming environment. -/
theorem absorbZeroBlock_equiv (body : Block Op) :
    EquivBlock D body (absorbZeroStmts [] body) :=
  EquivBlock.of_stmts_funs (absorbZeroStmts_equiv body)
    (scopeRel_hoistAbsorb [] body)

/-- Function bodies are transformed from an empty context and remain
equivalent in the hoisted function scope. -/
theorem scopeRel_hoistAbsorb (Γ : Core.Ctx) : ∀ body : Block Op,
    ScopeRel D (hoist D body) (hoist D (absorbZeroStmts Γ body))
  | [] => by simp [absorbZeroStmts, hoist]; exact .nil
  | .funDef name params rets fnBody :: rest => by
      simp only [absorbZeroStmts, absorbZeroStmt, absorbNextCtx, hoist,
        List.filterMap_cons]
      exact .cons ⟨rfl, rfl, rfl, absorbZeroBlock_equiv fnBody⟩
        (scopeRel_hoistAbsorb [] rest)
  | .block body :: rest => by
      simp only [absorbZeroStmts, absorbZeroStmt, absorbNextCtx, hoist,
        List.filterMap_cons]
      exact scopeRel_hoistAbsorb [] rest
  | .letDecl vars (some value) :: rest => by
      simp only [absorbZeroStmts, absorbZeroStmt, absorbNextCtx, hoist,
        List.filterMap_cons]
      exact scopeRel_hoistAbsorb (vars ++ Γ) rest
  | .letDecl vars none :: rest => by
      simp only [absorbZeroStmts, absorbZeroStmt, absorbNextCtx, hoist,
        List.filterMap_cons]
      exact scopeRel_hoistAbsorb (vars ++ Γ) rest
  | .assign vars value :: rest => by
      simp only [absorbZeroStmts, absorbZeroStmt, absorbNextCtx, hoist,
        List.filterMap_cons]
      exact scopeRel_hoistAbsorb [] rest
  | .cond condition body :: rest => by
      simp only [absorbZeroStmts, absorbZeroStmt, absorbNextCtx, hoist,
        List.filterMap_cons]
      exact scopeRel_hoistAbsorb [] rest
  | .switch condition cases dflt :: rest => by
      simp only [absorbZeroStmts, absorbZeroStmt, absorbNextCtx, hoist,
        List.filterMap_cons]
      exact scopeRel_hoistAbsorb [] rest
  | .forLoop init condition post body :: rest => by
      simp only [absorbZeroStmts, absorbZeroStmt, absorbNextCtx, hoist,
        List.filterMap_cons]
      exact scopeRel_hoistAbsorb [] rest
  | .exprStmt value :: rest => by
      simp only [absorbZeroStmts, absorbZeroStmt, absorbNextCtx, hoist,
        List.filterMap_cons]
      exact scopeRel_hoistAbsorb [] rest
  | .break :: rest => by
      simp only [absorbZeroStmts, absorbZeroStmt, absorbNextCtx, hoist,
        List.filterMap_cons]
      exact scopeRel_hoistAbsorb [] rest
  | .continue :: rest => by
      simp only [absorbZeroStmts, absorbZeroStmt, absorbNextCtx, hoist,
        List.filterMap_cons]
      exact scopeRel_hoistAbsorb [] rest
  | .leave :: rest => by
      simp only [absorbZeroStmts, absorbZeroStmt, absorbNextCtx, hoist,
        List.filterMap_cons]
      exact scopeRel_hoistAbsorb [] rest

end

/-- Verified scoped zero-absorption pass. -/
def absorbZero : Pass D where
  run := absorbZeroStmts []
  sound := absorbZeroBlock_equiv

/-- The public **Simplify pass**: unconditional local simplification followed
by context-dependent Core absorption. -/
def simplify : Pass D := Pass.comp absorbZero simplifyLocal

@[simp] theorem simplify_run (body : Block Op) :
    (simplify (calls := calls) (creates := creates)).run body =
      absorbZeroStmts [] (simplifyStmts body) := rfl

/-! ### Regression examples -/

-- A preceding declaration realizes `x`, so absorption fires.
example : absorbZeroStmts []
    [.letDecl ["x"] (some (.builtin .calldataload [.lit (.number 0)])),
      .letDecl ["y"] (some (.builtin .mul [.var "x", .lit (.number 0)]))] =
  [.letDecl ["x"] (some (.builtin .calldataload [.lit (.number 0)])),
    .letDecl ["y"] (some (.lit (.number 0)))] := rfl

-- A free raw variable remains untouched, preserving stuckness on malformed ASTs.
example : absorbZeroStmts []
    [.letDecl ["y"] (some (.builtin .mul [.var "x", .lit (.number 0)]))] =
  [.letDecl ["y"] (some (.builtin .mul [.var "x", .lit (.number 0)]))] := rfl

end YulEvmCompiler.Optimizer
