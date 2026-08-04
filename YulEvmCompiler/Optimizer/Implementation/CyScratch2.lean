import YulEvmCompiler.Optimizer.Implementation.CyScratch
set_option warningAsError false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM

variable {calls : ExternalCalls} {creates : ExternalCreates}

local notation "D" => evmWithExternal calls creates

/-- Backward mirror of `cyRel_stmts_cons_inv`: invert a `CyRel` whose **target**
is a non-empty statement list, returning the target head/tail shape as
**equations** (keeping the principal derivation's code index a bare variable so
`cy_bwd`'s structural recursion still threads `brecOn`). -/
theorem cyRel_stmts_cons_inv_bwd {Δ : DEnv} {s₂ : Stmt Op} {rest₂ : List (Stmt Op)}
    {pc : PCode Op} (hrel : CyRel Δ pc (.stmts (s₂ :: rest₂))) :
    (∃ s rest, pc = .stmts (s :: rest) ∧
        CyRel Δ (.stmt s) (.stmt s₂) ∧ CyRel Δ (.stmts rest) (.stmts rest₂))
  ∨ (∃ (f : Ident) (d : IDecl) (xs : List Ident) (as : List (Expr Op))
        (rest : List (Stmt Op)),
        pc = .stmts (.letDecl xs (some (.call f as)) :: rest) ∧
        s₂ = .letDecl xs none ∧
        lookupDelta Δ f = some d ∧ (d.ps ++ d.rs).Nodup ∧
        carryStmts (d.ps ++ d.rs) d.ss = true ∧ siteOK d xs as true = true ∧
        CyRel Δ (.stmts (.assign xs (.call f as) :: rest)) (.stmts rest₂))
  ∨ (∃ (f : Ident) (d : IDecl) (xs : List Ident) (as : List (Expr Op))
        (rest : List (Stmt Op)),
        pc = .stmts (.assign xs (.call f as) :: rest) ∧
        s₂ = inlineCore d xs as ∧
        lookupDelta Δ f = some d ∧ (d.ps ++ d.rs).Nodup ∧
        carryStmts (d.ps ++ d.rs) d.ss = true ∧ siteOK d xs as false = true ∧
        CyRel Δ (.stmts rest) (.stmts rest₂))
  ∨ (∃ (f : Ident) (d : IDecl) (as : List (Expr Op)) (rest : List (Stmt Op)),
        pc = .stmts (.exprStmt (.call f as) :: rest) ∧
        s₂ = inlineCore d [] as ∧
        lookupDelta Δ f = some d ∧ (d.ps ++ d.rs).Nodup ∧
        carryStmts (d.ps ++ d.rs) d.ss = true ∧ siteOK d [] as false = true ∧
        CyRel Δ (.stmts rest) (.stmts rest₂)) := by
  cases hrel with
  | consSS hs hrest => exact Or.inl ⟨_, _, rfl, hs, hrest⟩
  | siteLet hld hnd hsc hok hrest =>
      exact Or.inr (Or.inl ⟨_, _, _, _, _, rfl, rfl, hld, hnd, hsc, hok,
        CyRel.siteAssign hld hnd hsc (siteOK_weaken hok) hrest⟩)
  | siteAssign hld hnd hsc hok hrest =>
      exact Or.inr (Or.inr (Or.inl ⟨_, _, _, _, _, rfl, rfl, hld, hnd, hsc, hok, hrest⟩))
  | siteExpr hld hnd hsc hok hrest =>
      exact Or.inr (Or.inr (Or.inr ⟨_, _, _, _, rfl, rfl, hld, hnd, hsc, hok, hrest⟩))

/-- Prepend a list of (unevaluated) arguments to a halting `.args` run. -/
theorem args_prepend_halt {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    {suffix : List (Expr Op)} {st1 : EvmState}
    (h : Step D funs V st (.args suffix) (.eres (.halt st1))) :
    ∀ (pre : List (Expr Op)),
      Step D funs V st (.args (pre ++ suffix)) (.eres (.halt st1)) := by
  intro pre
  induction pre with
  | nil => exact h
  | cons e pre' ih => exact Step.argsRestHalt ih

/-- From a global `argsHaveCall … = false`, an element is call-free. -/
theorem argsHaveCall_split {a : Expr Op} {post : List (Expr Op)} :
    ∀ {pre : List (Expr Op)}, argsHaveCall (pre ++ a :: post) = false →
      exprHasCall a = false := by
  intro pre
  induction pre with
  | nil =>
      intro h
      rw [List.nil_append,
        show argsHaveCall (a :: post) = (exprHasCall a || argsHaveCall post) from rfl,
        Bool.or_eq_false_iff] at h
      exact h.1
  | cons e pre' ih =>
      intro h
      rw [List.cons_append,
        show argsHaveCall (e :: (pre' ++ a :: post)) =
          (exprHasCall e || argsHaveCall (pre' ++ a :: post)) from rfl,
        Bool.or_eq_false_iff] at h
      exact ih h.2

/-- `argsShadowOK` gives that a pair's argument avoids the parameters strictly
after it. -/
theorem argsShadowOK_after {rs : List Ident} {p : Ident} {a : Expr Op}
    {post : List (Ident × Expr Op)} :
    ∀ {pre : List (Ident × Expr Op)},
      argsShadowOK rs (pre ++ (p, a) :: post) = true →
      ∀ y ∈ exprVars a, y ∉ post.map Prod.fst := by
  intro pre
  induction pre with
  | nil =>
      intro h y hy
      rw [List.nil_append,
        show argsShadowOK rs ((p, a) :: post) =
          ((exprVars a).all (fun v => !(post.map Prod.fst).contains v && !rs.contains v) &&
            argsShadowOK rs post) from rfl,
        Bool.and_eq_true] at h
      have hall := List.all_eq_true.mp h.1 y hy
      rw [Bool.and_eq_true] at hall
      simpa using hall.1
  | cons pr pre' ih =>
      intro h y hy
      rcases pr with ⟨q, b⟩
      rw [List.cons_append,
        show argsShadowOK rs ((q, b) :: (pre' ++ (p, a) :: post)) =
          ((exprVars b).all
              (fun v => !((pre' ++ (p, a) :: post).map Prod.fst).contains v && !rs.contains v) &&
            argsShadowOK rs (pre' ++ (p, a) :: post)) from rfl,
        Bool.and_eq_true] at h
      exact ih h.2 y hy

/-- `letZero` result inversion, returning equations (so no sibling index gets
refined by a `cases` in the caller's structural recursion). -/
theorem letZero_inv {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    {xs : List Ident} {res : Res D}
    (h : Step D funs V st (.stmt (.letDecl xs none)) res) :
    res = .sres (bindZeros D xs ++ V) st .normal := by
  cases h with
  | letZero => rfl

theorem varsList_append (a b : List (Expr Op)) :
    varsList (a ++ b) = varsList a ++ varsList b := by
  induction a with
  | nil => rfl
  | cons e rest ih =>
      rw [List.cons_append,
        show varsList (e :: (rest ++ b)) = exprVars e ++ varsList (rest ++ b) from rfl, ih,
        show varsList (e :: rest) = exprVars e ++ varsList rest from rfl, List.append_assoc]

/-- Invert a `halt` `TResL` from the **target** (second) side. -/
theorem TResL.halt_inv' {W W' : VEnv D} {post : List Ident} {res₁ : Res D}
    {V₂ : VEnv D} {st₂ : EvmState}
    (h : TResL (calls := calls) (creates := creates) W W' post res₁
      (.sres V₂ st₂ .halt)) :
    ∃ A', V₂ = A' ++ W' ∧ res₁ = .sres (A' ++ W) st₂ .halt := by
  cases h with
  | halt => exact ⟨_, rfl, rfl⟩

/-- Invert a `normal` `TResL` from the **target** (second) side. -/
theorem TResL.norm_inv' {W W' : VEnv D} {post : List Ident} {res₁ : Res D}
    {V₂ : VEnv D} {st₂ : EvmState}
    (h : TResL (calls := calls) (creates := creates) W W' post res₁
      (.sres V₂ st₂ .normal)) :
    ∃ A', V₂ = A' ++ W' ∧ res₁ = .sres (A' ++ W) st₂ .normal ∧
      (∀ x ∈ post, x ∈ A'.map Prod.fst) := by
  cases h with
  | norm hk => exact ⟨_, rfl, rfl, hk⟩

mutual

/-- **Backward simulation** across `CyRel`: a target derivation transports back
to the source. -/
theorem cy_bwd {funs₂ : FunEnv D} {V : VEnv D} {st : EvmState}
    {code₂ : Code Op} {res₂ : Res D} (h : Step D funs₂ V st code₂ res₂) :
    ∀ {funs₁ : FunEnv D} {Δ : DEnv} {pc : PCode Op},
      CyFunsRel (calls := calls) (creates := creates) funs₁ funs₂ →
      CarryCompat (calls := calls) (creates := creates) Δ funs₁ →
      CyRel Δ pc (toPCode code₂) →
      ∃ res₁, Step D funs₁ V st (ofPCode pc) res₁ ∧
        cyResOK (calls := calls) (creates := creates) code₂ res₁ res₂ := by
  match h with
  | .lit =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | expr => exact ⟨_, Step.lit, rfl⟩
  | .var hv =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | expr => exact ⟨_, Step.var hv, rfl⟩
  | .builtinOk ha hbi =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | expr =>
          obtain ⟨res₁, hs, heq⟩ := cy_bwd ha hR hΔ CyRel.args
          have heqX : _ = res₁ := heq; rw [← heqX] at hs
          exact ⟨_, Step.builtinOk hs hbi, rfl⟩
  | .builtinHalt ha hbi =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | expr =>
          obtain ⟨res₁, hs, heq⟩ := cy_bwd ha hR hΔ CyRel.args
          have heqX : _ = res₁ := heq; rw [← heqX] at hs
          exact ⟨_, Step.builtinHalt hs hbi, rfl⟩
  | .builtinArgsHalt ha =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | expr =>
          obtain ⟨res₁, hs, heq⟩ := cy_bwd ha hR hΔ CyRel.args
          have heqX : _ = res₁ := heq; rw [← heqX] at hs
          exact ⟨_, Step.builtinArgsHalt hs, rfl⟩
  | @Step.callOk _ _ funs V st fn args argvals st1 decl cenv Vend st2 o ha hlk harity hbody ho =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | expr =>
          obtain ⟨resa, hs, heqa⟩ := cy_bwd ha hR hΔ CyRel.args
          have heqaX : _ = resa := heqa; rw [← heqaX] at hs
          obtain ⟨decl₁, cenv₁, hlk₁, hdecl, hcenvR⟩ := lookupFun_cyFunsRel_bwd hR hlk
          obtain ⟨hps, hrs, Δf, hΔf, hbrel⟩ := hdecl
          obtain ⟨resb, hsb, heqb⟩ := cy_bwd hbody hcenvR hΔf (CyRel.blockS hbrel)
          have heqbX : _ = resb := heqb; rw [← heqbX] at hsb
          have hsb' : Step D cenv₁ (decl₁.params.zip argvals ++ bindZeros D decl₁.rets)
              st1 (.stmt (.block decl₁.body)) (.sres Vend st2 o) := by
            rw [hps, hrs]; exact hsb
          have harity' : argvals.length = decl₁.params.length := by rw [hps]; exact harity
          refine ⟨_, Step.callOk hs hlk₁ harity' hsb' ho, ?_⟩
          show Res.eres (.vals (decl.rets.map _) st2) = Res.eres (.vals (decl₁.rets.map _) st2)
          rw [hrs]
  | @Step.callHalt _ _ funs V st fn args argvals st1 decl cenv Vend st2 ha hlk harity hbody =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | expr =>
          obtain ⟨resa, hs, heqa⟩ := cy_bwd ha hR hΔ CyRel.args
          have heqaX : _ = resa := heqa; rw [← heqaX] at hs
          obtain ⟨decl₁, cenv₁, hlk₁, hdecl, hcenvR⟩ := lookupFun_cyFunsRel_bwd hR hlk
          obtain ⟨hps, hrs, Δf, hΔf, hbrel⟩ := hdecl
          obtain ⟨resb, hsb, heqb⟩ := cy_bwd hbody hcenvR hΔf (CyRel.blockS hbrel)
          have heqbX : _ = resb := heqb; rw [← heqbX] at hsb
          have hsb' : Step D cenv₁ (decl₁.params.zip argvals ++ bindZeros D decl₁.rets)
              st1 (.stmt (.block decl₁.body)) (.sres Vend st2 .halt) := by
            rw [hps, hrs]; exact hsb
          have harity' : argvals.length = decl₁.params.length := by rw [hps]; exact harity
          exact ⟨_, Step.callHalt hs hlk₁ harity' hsb', rfl⟩
  | .callArgsHalt ha =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | expr =>
          obtain ⟨resa, hs, heqa⟩ := cy_bwd ha hR hΔ CyRel.args
          have heqaX : _ = resa := heqa; rw [← heqaX] at hs
          exact ⟨_, Step.callArgsHalt hs, rfl⟩
  | .argsNil =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | args => exact ⟨_, Step.argsNil, rfl⟩
  | .argsCons hrest he =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | args =>
          obtain ⟨res₁, hs₁, heq₁⟩ := cy_bwd hrest hR hΔ CyRel.args
          have heq₁X : _ = res₁ := heq₁; rw [← heq₁X] at hs₁
          obtain ⟨res₂', hs₂, heq₂⟩ := cy_bwd he hR hΔ CyRel.expr
          have heq₂X : _ = res₂' := heq₂; rw [← heq₂X] at hs₂
          exact ⟨_, Step.argsCons hs₁ hs₂, rfl⟩
  | .argsRestHalt hrest =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | args =>
          obtain ⟨res₁, hs₁, heq₁⟩ := cy_bwd hrest hR hΔ CyRel.args
          have heq₁X : _ = res₁ := heq₁; rw [← heq₁X] at hs₁
          exact ⟨_, Step.argsRestHalt hs₁, rfl⟩
  | .argsHeadHalt hrest he =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | args =>
          obtain ⟨res₁, hs₁, heq₁⟩ := cy_bwd hrest hR hΔ CyRel.args
          have heq₁X : _ = res₁ := heq₁; rw [← heq₁X] at hs₁
          obtain ⟨res₂', hs₂, heq₂⟩ := cy_bwd he hR hΔ CyRel.expr
          have heq₂X : _ = res₂' := heq₂; rw [← heq₂X] at hs₂
          exact ⟨_, Step.argsHeadHalt hs₁ hs₂, rfl⟩
  | .funDef =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | funDefS hbrel => exact ⟨_, Step.funDef, rfl⟩
  | @Step.block _ _ funs V st body' Vb stb o hb =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | @blockS _ body _ hbrel =>
          have hcompat := CarryCompat.extend (calls := calls) (creates := creates) hΔ body
          have hfr := CyFunsRel.cons (calls := calls) (creates := creates)
            (cyScopeRel_of_block hbrel hcompat) hR
          obtain ⟨res₁, hs, hres⟩ := cy_bwd hb hfr hcompat hbrel
          cases hres with
          | refl => exact ⟨_, Step.block hs, rfl⟩
          | haltIns Zp V₁ _ =>
              have hb1 := Step.block (funs := funs₁) hs
              refine ⟨_, hb1, ?_⟩
              show Res.sres (restore V (Zp ++ V₁)) stb .halt = Res.sres (restore V V₁) stb .halt
              rw [restore_prefix_le (venvLen_mono hs rfl)]
  | .letZero =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | letS => exact ⟨_, Step.letZero, rfl⟩
  | .letVal he hlen =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | letS =>
          obtain ⟨res₁, hs, heq⟩ := cy_bwd he hR hΔ CyRel.expr
          have heqX : _ = res₁ := heq; rw [← heqX] at hs
          exact ⟨_, Step.letVal hs hlen, rfl⟩
  | .letHalt he =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | letS =>
          obtain ⟨res₁, hs, heq⟩ := cy_bwd he hR hΔ CyRel.expr
          have heqX : _ = res₁ := heq; rw [← heqX] at hs
          exact ⟨_, Step.letHalt hs, rfl⟩
  | .assignVal he hlen =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | assignS =>
          obtain ⟨res₁, hs, heq⟩ := cy_bwd he hR hΔ CyRel.expr
          have heqX : _ = res₁ := heq; rw [← heqX] at hs
          exact ⟨_, Step.assignVal hs hlen, rfl⟩
  | .assignHalt he =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | assignS =>
          obtain ⟨res₁, hs, heq⟩ := cy_bwd he hR hΔ CyRel.expr
          have heqX : _ = res₁ := heq; rw [← heqX] at hs
          exact ⟨_, Step.assignHalt hs, rfl⟩
  | .exprStmt he =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | exprStmtS =>
          obtain ⟨res₁, hs, heq⟩ := cy_bwd he hR hΔ CyRel.expr
          have heqX : _ = res₁ := heq; rw [← heqX] at hs
          exact ⟨_, Step.exprStmt hs, rfl⟩
  | .exprStmtHalt he =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | exprStmtS =>
          obtain ⟨res₁, hs, heq⟩ := cy_bwd he hR hΔ CyRel.expr
          have heqX : _ = res₁ := heq; rw [← heqX] at hs
          exact ⟨_, Step.exprStmtHalt hs, rfl⟩
  | .ifTrue hc hcv hbody =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | @condS _ _ body _ hbrel =>
          obtain ⟨res₁, hs₁, heq₁⟩ := cy_bwd hc hR hΔ CyRel.expr
          have heq₁X : _ = res₁ := heq₁; rw [← heq₁X] at hs₁
          obtain ⟨res₂', hs₂, heq₂⟩ := cy_bwd hbody hR hΔ (CyRel.blockS hbrel)
          have heq₂X : _ = res₂' := heq₂; rw [← heq₂X] at hs₂
          exact ⟨_, Step.ifTrue hs₁ hcv hs₂, rfl⟩
  | .ifFalse hc hcv =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | condS hbrel =>
          obtain ⟨res₁, hs₁, heq₁⟩ := cy_bwd hc hR hΔ CyRel.expr
          have heq₁X : _ = res₁ := heq₁; rw [← heq₁X] at hs₁
          exact ⟨_, Step.ifFalse hs₁ hcv, rfl⟩
  | .ifHalt hc =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | condS hbrel =>
          obtain ⟨res₁, hs₁, heq₁⟩ := cy_bwd hc hR hΔ CyRel.expr
          have heq₁X : _ = res₁ := heq₁; rw [← heq₁X] at hs₁
          exact ⟨_, Step.ifHalt hs₁, rfl⟩
  | .switchExec hc hsel =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | switchS hcs hd =>
          obtain ⟨res₁, hs₁, heq₁⟩ := cy_bwd hc hR hΔ CyRel.expr
          have heq₁X : _ = res₁ := heq₁; rw [← heq₁X] at hs₁
          obtain ⟨res₂', hs₂, heq₂⟩ := cy_bwd hsel hR hΔ (CyRel.selectRel hcs hd _)
          have heq₂X : _ = res₂' := heq₂; rw [← heq₂X] at hs₂
          exact ⟨_, Step.switchExec hs₁ hs₂, rfl⟩
  | .switchHalt hc =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | switchS hcs hd =>
          obtain ⟨res₁, hs₁, heq₁⟩ := cy_bwd hc hR hΔ CyRel.expr
          have heq₁X : _ = res₁ := heq₁; rw [← heq₁X] at hs₁
          exact ⟨_, Step.switchHalt hs₁, rfl⟩
  | @Step.forLoop _ _ funs V st init c post' body' Vinit stinit Vend stend o hinit hloop =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | @forS _ _ _ post _ body _ hpost hbody =>
          have hfr := CyFunsRel.cons (calls := calls) (creates := creates)
            (cyScopeRel_refl (hoist D init :: funs₁) (hoist D init)) hR
          obtain ⟨res₁, hs₁, hres₁⟩ := cy_bwd hinit hfr (CarryCompat.nil _)
            (CyRel.reflStmts [] init)
          cases hres₁ with
          | refl =>
              obtain ⟨res₂', hs₂, heq₂⟩ := cy_bwd hloop hfr (CarryCompat.pruneInit hΔ init)
                (CyRel.loopL hpost hbody)
              have heq₂X : _ = res₂' := heq₂; rw [← heq₂X] at hs₂
              exact ⟨_, Step.forLoop hs₁ hs₂, rfl⟩
  | @Step.forInitHalt _ _ funs V st init c post' body' Vinit stinit hinit =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | @forS _ _ _ post _ body _ hpost hbody =>
          have hfr := CyFunsRel.cons (calls := calls) (creates := creates)
            (cyScopeRel_refl (hoist D init :: funs₁) (hoist D init)) hR
          obtain ⟨res₁, hs₁, hres₁⟩ := cy_bwd hinit hfr (CarryCompat.nil _)
            (CyRel.reflStmts [] init)
          cases hres₁ with
          | refl => exact ⟨_, Step.forInitHalt hs₁, rfl⟩
          | haltIns Zp V₁ _ =>
              have hb1 := Step.forInitHalt (c := c) (post := post) (body := body)
                (funs := funs₁) hs₁
              refine ⟨_, hb1, ?_⟩
              show Res.sres (restore V (Zp ++ V₁)) stinit .halt =
                Res.sres (restore V V₁) stinit .halt
              rw [restore_prefix_le (venvLen_mono hs₁ rfl)]
  | .«break» =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | breakS => exact ⟨_, Step.break, rfl⟩
  | .«continue» =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | continueS => exact ⟨_, Step.continue, rfl⟩
  | .«leave» =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | leaveS => exact ⟨_, Step.leave, rfl⟩
  | .seqNil =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | nilSS => exact ⟨_, Step.seqNil, .refl _⟩
  | @Step.seqCons _ _ _ V st s₂ rest₂ V1 st1 V2 st2 o hs hrest =>
      intro funs₁ Δ pc hR hΔ hrel
      rcases cyRel_stmts_cons_inv_bwd hrel with
        ⟨s, rest, rfl, hsrel, hrestrel⟩
        | ⟨f, d, xs, as, rest, hpc, hs₂eq, hld, hnd, hsc, hok, hsiteA⟩
        | ⟨f, d, xs, as, rest, hpc, hs₂eq, hld, hnd, hsc, hok, hrestrel⟩
        | ⟨f, d, as, rest, hpc, hs₂eq, hld, hnd, hsc, hok, hrestrel⟩
      · obtain ⟨res₁, hs₁, heq₁⟩ := cy_bwd hs hR hΔ hsrel
        have heq₁X : _ = res₁ := heq₁; rw [← heq₁X] at hs₁
        obtain ⟨res₂', hs₂, hres₂⟩ := cy_bwd hrest hR hΔ hrestrel
        cases hres₂ with
        | refl => exact ⟨_, Step.seqCons hs₁ hs₂, .refl _⟩
        | haltIns Zp => exact ⟨_, Step.seqCons hs₁ hs₂, .haltIns _ _ _⟩
      · -- siteLet, seqCons: thin wrapper — after letZero re-relate the tail to
        -- the assign-form site, then convert the source assign run to let form.
        subst hpc
        obtain ⟨hlen_as, hlen_xs, hxnd, hnc, hsh, hxout, hxlet⟩ := siteOK_inv hok
        have hVst : (Res.sres V1 st1 Outcome.normal) =
            .sres (bindZeros D xs ++ V) st .normal := letZero_inv (hs₂eq ▸ hs)
        simp only [Res.sres.injEq] at hVst
        obtain ⟨hV1eq, hst1eq, -⟩ := hVst
        obtain ⟨res₁', hs₁', hres'⟩ := cy_bwd hrest hR hΔ hsiteA
        rw [hV1eq, hst1eq] at hs₁'
        have hNx : ∀ y ∈ varsList as, y ∉ (bindZeros D xs).map Prod.fst := by
          intro y hy; rw [bindZeros_keys]; exact hxlet rfl y hy
        rcases res₁' with r | ⟨V₁', st₁', o₁'⟩
        · cases hres'
        · cases hs₁' with
          | @seqCons _ _ _ _ _ Va sta _ _ _ hassign htail₁ =>
              cases hassign with
              | @assignVal _ _ _ _ _ vals _ he hlenv =>
                  have hcall := callExpr_extend_bwd he hnc hNx
                  have henv : VEnv.setMany (bindZeros D xs ++ V) xs vals =
                      xs.zip vals ++ V :=
                    VEnv.setMany_bindZeros hxnd (by omega) V
                  have hlet : Step D funs₁ V st
                      (.stmt (.letDecl xs (some (.call f as))))
                      (.sres (xs.zip vals ++ V) sta .normal) :=
                    Step.letVal hcall hlenv
                  rw [henv] at htail₁
                  cases hres' with
                  | refl => exact ⟨_, Step.seqCons hlet htail₁, .refl _⟩
                  | haltIns Zp => exact ⟨_, Step.seqCons hlet htail₁, .haltIns _ _ _⟩
          | @seqStop _ _ _ _ _ Va sta oa hassign hnea =>
              cases hassign with
              | @assignVal _ _ _ _ _ vals _ he hlenv => exact absurd rfl hnea
              | @assignHalt _ _ _ _ _ _ he =>
                  have hcall := callExpr_extend_bwd he hnc hNx
                  have hlet : Step D funs₁ V st
                      (.stmt (.letDecl xs (some (.call f as))))
                      (.sres V st₁' .halt) := Step.letHalt hcall
                  cases hres' with
                  | refl =>
                      refine ⟨_, Step.seqStop hlet (by simp), ?_⟩
                      exact .haltIns (bindZeros D xs) _ _
                  | haltIns Zp =>
                      refine ⟨_, Step.seqStop hlet (by simp), ?_⟩
                      rw [show Zp ++ (bindZeros D xs ++ V) =
                        (Zp ++ bindZeros D xs) ++ V from
                        (List.append_assoc _ _ _).symm]
                      exact .haltIns (Zp ++ bindZeros D xs) _ _
      · -- siteAssign, seqCons
        subst hpc
        obtain ⟨hlen_as, hlen_xs, hxnd, hnc, hsh, hxout, -⟩ := siteOK_inv hok
        obtain ⟨body₀, cenv₀, hlk₀X, hb₀X, hagbody⟩ := hΔ (f, d) (lookupDelta_mem hld)
        have hlk₀ : lookupFun funs₁ f = some (⟨d.ps, d.rs, body₀⟩, cenv₀) := hlk₀X
        have hb₀ : body₀ = d.ss ∨ body₀ = d.ss ++ [.leave] := hb₀X
        have hZv : ∀ y ∈ varsList as, y ∉ (([] : VEnv D)).map Prod.fst := by
          intro y hy; simp
        rcases peelBody hs (List.nil_append V).symm (by rw [hs₂eq]) hsc hlen_as hnc hsh hxout hlen_xs hZv
            funs₁ cenv₀ hagbody hR
          with ⟨argvals, st1', Vend, strp, hargs, hbody, hEq⟩
            | ⟨argvals, st1', Vend, strp, hargs, hbody, hEq⟩
            | ⟨strp, hargs, hEq⟩
        · obtain ⟨oc, hbody', hoc⟩ := body_denormalize_ok hb₀ hbody
          simp only [List.nil_append] at hEq
          injection hEq with hV1 hst1
          have hcall : Step D funs₁ V st (.expr (.call f as))
              (.eres (.vals (d.rs.map (fun r => (VEnv.get Vend r).getD
                (evmWithExternal calls creates).zero)) strp)) := by
            refine Step.callOk hargs hlk₀ ?_ hbody' hoc
            show argvals.length = d.ps.length
            have := args_length hargs; omega
          have hassign : Step D funs₁ V st (.stmt (.assign xs (.call f as)))
              (.sres (VEnv.setMany V xs (d.rs.map (fun r => (VEnv.get Vend r).getD
                (evmWithExternal calls creates).zero))) strp .normal) :=
            Step.assignVal hcall (by simp only [List.length_map]; omega)
          obtain ⟨res₂', hs₂', hres₂⟩ := cy_bwd hrest hR hΔ hrestrel
          rw [hV1, hst1] at hs₂'
          cases hres₂ with
          | refl => exact ⟨_, Step.seqCons hassign hs₂', .refl _⟩
          | haltIns Zp => exact ⟨_, Step.seqCons hassign hs₂', .haltIns _ _ _⟩
        · injection hEq with _ _ ho; exact absurd ho (by simp)
        · injection hEq with _ _ ho; exact absurd ho (by simp)
      · -- siteExpr, seqCons
        subst hpc
        obtain ⟨hlen_as, hlen_xs, -, hnc, hsh, -, -⟩ := siteOK_inv hok
        obtain ⟨body₀, cenv₀, hlk₀X, hb₀X, hagbody⟩ := hΔ (f, d) (lookupDelta_mem hld)
        have hlk₀ : lookupFun funs₁ f = some (⟨d.ps, d.rs, body₀⟩, cenv₀) := hlk₀X
        have hb₀ : body₀ = d.ss ∨ body₀ = d.ss ++ [.leave] := hb₀X
        have hrs0 : d.rs = [] := by
          cases hrs : d.rs with
          | nil => rfl
          | cons r rs' => rw [hrs] at hlen_xs; simp at hlen_xs
        have hZv : ∀ y ∈ varsList as, y ∉ (([] : VEnv D)).map Prod.fst := by
          intro y hy; simp
        rcases peelBody hs (List.nil_append V).symm (by rw [hs₂eq]) hsc hlen_as hnc hsh
            (fun x hx => by cases hx) hlen_xs hZv funs₁ cenv₀ hagbody hR
          with ⟨argvals, st1', Vend, strp, hargs, hbody, hEq⟩
            | ⟨argvals, st1', Vend, strp, hargs, hbody, hEq⟩
            | ⟨strp, hargs, hEq⟩
        · obtain ⟨oc, hbody', hoc⟩ := body_denormalize_ok hb₀ hbody
          injection hEq with hV1 hst1
          have hcall : Step D funs₁ V st (.expr (.call f as)) (.eres (.vals [] strp)) := by
            have hc := Step.callOk hargs hlk₀ (by
              show argvals.length = d.ps.length
              have := args_length hargs; omega) hbody' hoc
            rw [show (⟨d.ps, d.rs, body₀⟩ : FDecl D).rets = d.rs from rfl, hrs0] at hc
            exact hc
          have hstmt : Step D funs₁ V st (.stmt (.exprStmt (.call f as)))
              (.sres V strp .normal) := Step.exprStmt hcall
          have hV1' : V1 = V := by rw [hV1]; rfl
          obtain ⟨res₂', hs₂', hres₂⟩ := cy_bwd hrest hR hΔ hrestrel
          rw [hV1', hst1] at hs₂'
          cases hres₂ with
          | refl => exact ⟨_, Step.seqCons hstmt hs₂', .refl _⟩
          | haltIns Zp => exact ⟨_, Step.seqCons hstmt hs₂', .haltIns _ _ _⟩
        · injection hEq with _ _ ho; exact absurd ho (by simp)
        · injection hEq with _ _ ho; exact absurd ho (by simp)
  | @Step.seqStop _ _ _ V st s₂ rest₂ V1 st1 o hs hne =>
      intro funs₁ Δ pc hR hΔ hrel
      rcases cyRel_stmts_cons_inv_bwd hrel with
        ⟨s, rest, rfl, hsrel, hrestrel⟩
        | ⟨f, d, xs, as, rest, hpc, hs₂eq, hld, hnd, hsc, hok, hsiteA⟩
        | ⟨f, d, xs, as, rest, hpc, hs₂eq, hld, hnd, hsc, hok, hrestrel⟩
        | ⟨f, d, as, rest, hpc, hs₂eq, hld, hnd, hsc, hok, hrestrel⟩
      · obtain ⟨res₁, hs₁, heq₁⟩ := cy_bwd hs hR hΔ hsrel
        have heq₁X : _ = res₁ := heq₁; rw [← heq₁X] at hs₁
        exact ⟨_, Step.seqStop hs₁ hne, .refl _⟩
      · rw [hs₂eq] at hs; cases hs; exact absurd rfl hne
      · -- siteAssign, seqStop
        subst hpc
        obtain ⟨hlen_as, hlen_xs, hxnd, hnc, hsh, hxout, -⟩ := siteOK_inv hok
        obtain ⟨body₀, cenv₀, hlk₀X, hb₀X, hagbody⟩ := hΔ (f, d) (lookupDelta_mem hld)
        have hlk₀ : lookupFun funs₁ f = some (⟨d.ps, d.rs, body₀⟩, cenv₀) := hlk₀X
        have hb₀ : body₀ = d.ss ∨ body₀ = d.ss ++ [.leave] := hb₀X
        have hZv : ∀ y ∈ varsList as, y ∉ (([] : VEnv D)).map Prod.fst := by
          intro y hy; simp
        rcases peelBody hs (List.nil_append V).symm (by rw [hs₂eq]) hsc hlen_as hnc hsh hxout hlen_xs hZv
            funs₁ cenv₀ hagbody hR
          with ⟨argvals, st1', Vend, strp, hargs, hbody, hEq⟩
            | ⟨argvals, st1', Vend, strp, hargs, hbody, hEq⟩
            | ⟨strp, hargs, hEq⟩
        · injection hEq with _ _ ho; exact absurd ho hne
        · have hbody' := body_denormalize_halt hb₀ hbody
          injection hEq with hV1 hst1 ho
          have hcall : Step D funs₁ V st (.expr (.call f as)) (.eres (.halt strp)) := by
            refine Step.callHalt hargs hlk₀ ?_ hbody'
            show argvals.length = d.ps.length
            have := args_length hargs; omega
          subst hV1 hst1 ho
          exact ⟨_, Step.seqStop (Step.assignHalt hcall) (by simp), .refl _⟩
        · injection hEq with hV1 hst1 ho
          have hcall : Step D funs₁ V st (.expr (.call f as)) (.eres (.halt strp)) :=
            Step.callArgsHalt hargs
          subst hV1 hst1 ho
          exact ⟨_, Step.seqStop (Step.assignHalt hcall) (by simp), .refl _⟩
      · -- siteExpr, seqStop
        subst hpc
        obtain ⟨hlen_as, hlen_xs, -, hnc, hsh, -, -⟩ := siteOK_inv hok
        obtain ⟨body₀, cenv₀, hlk₀X, hb₀X, hagbody⟩ := hΔ (f, d) (lookupDelta_mem hld)
        have hlk₀ : lookupFun funs₁ f = some (⟨d.ps, d.rs, body₀⟩, cenv₀) := hlk₀X
        have hb₀ : body₀ = d.ss ∨ body₀ = d.ss ++ [.leave] := hb₀X
        have hZv : ∀ y ∈ varsList as, y ∉ (([] : VEnv D)).map Prod.fst := by
          intro y hy; simp
        rcases peelBody hs (List.nil_append V).symm (by rw [hs₂eq]) hsc hlen_as hnc hsh
            (fun x hx => by cases hx) hlen_xs hZv funs₁ cenv₀ hagbody hR
          with ⟨argvals, st1', Vend, strp, hargs, hbody, hEq⟩
            | ⟨argvals, st1', Vend, strp, hargs, hbody, hEq⟩
            | ⟨strp, hargs, hEq⟩
        · injection hEq with _ _ ho; exact absurd ho hne
        · have hbody' := body_denormalize_halt hb₀ hbody
          injection hEq with hV1 hst1 ho
          have hcall : Step D funs₁ V st (.expr (.call f as)) (.eres (.halt strp)) := by
            refine Step.callHalt hargs hlk₀ ?_ hbody'
            show argvals.length = d.ps.length
            have := args_length hargs; omega
          subst hV1 hst1 ho
          exact ⟨_, Step.seqStop (Step.exprStmtHalt hcall) (by simp), .refl _⟩
        · injection hEq with hV1 hst1 ho
          have hcall : Step D funs₁ V st (.expr (.call f as)) (.eres (.halt strp)) :=
            Step.callArgsHalt hargs
          subst hV1 hst1 ho
          exact ⟨_, Step.seqStop (Step.exprStmtHalt hcall) (by simp), .refl _⟩
  | .loopDone hc hcz =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | loopL hpost hbody =>
          obtain ⟨res₁, hs₁, heq₁⟩ := cy_bwd hc hR hΔ CyRel.expr
          have heq₁X : _ = res₁ := heq₁; rw [← heq₁X] at hs₁
          exact ⟨_, Step.loopDone hs₁ hcz, rfl⟩
  | .loopCondHalt hc =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | loopL hpost hbody =>
          obtain ⟨res₁, hs₁, heq₁⟩ := cy_bwd hc hR hΔ CyRel.expr
          have heq₁X : _ = res₁ := heq₁; rw [← heq₁X] at hs₁
          exact ⟨_, Step.loopCondHalt hs₁, rfl⟩
  | .loopStep hc hcv hbody hob hpost hnext =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | @loopL _ _ post _ body _ hpostrel hbodyrel =>
          obtain ⟨res₁, hs₁, heq₁⟩ := cy_bwd hc hR hΔ CyRel.expr
          have heq₁X : _ = res₁ := heq₁; rw [← heq₁X] at hs₁
          obtain ⟨res₂', hs₂, heq₂⟩ := cy_bwd hbody hR hΔ (CyRel.blockS hbodyrel)
          have heq₂X : _ = res₂' := heq₂; rw [← heq₂X] at hs₂
          obtain ⟨res₃, hs₃, heq₃⟩ := cy_bwd hpost hR hΔ (CyRel.blockS hpostrel)
          have heq₃X : _ = res₃ := heq₃; rw [← heq₃X] at hs₃
          obtain ⟨res₄, hs₄, heq₄⟩ := cy_bwd hnext hR hΔ (CyRel.loopL hpostrel hbodyrel)
          have heq₄X : _ = res₄ := heq₄; rw [← heq₄X] at hs₄
          exact ⟨_, Step.loopStep hs₁ hcv hs₂ hob hs₃ hs₄, rfl⟩
  | .loopPostHalt hc hcv hbody hob hpost =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | loopL hpostrel hbodyrel =>
          obtain ⟨res₁, hs₁, heq₁⟩ := cy_bwd hc hR hΔ CyRel.expr
          have heq₁X : _ = res₁ := heq₁; rw [← heq₁X] at hs₁
          obtain ⟨res₂', hs₂, heq₂⟩ := cy_bwd hbody hR hΔ (CyRel.blockS hbodyrel)
          have heq₂X : _ = res₂' := heq₂; rw [← heq₂X] at hs₂
          obtain ⟨res₃, hs₃, heq₃⟩ := cy_bwd hpost hR hΔ (CyRel.blockS hpostrel)
          have heq₃X : _ = res₃ := heq₃; rw [← heq₃X] at hs₃
          exact ⟨_, Step.loopPostHalt hs₁ hcv hs₂ hob hs₃, rfl⟩
  | .loopBreak hc hcv hbody =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | loopL hpostrel hbodyrel =>
          obtain ⟨res₁, hs₁, heq₁⟩ := cy_bwd hc hR hΔ CyRel.expr
          have heq₁X : _ = res₁ := heq₁; rw [← heq₁X] at hs₁
          obtain ⟨res₂', hs₂, heq₂⟩ := cy_bwd hbody hR hΔ (CyRel.blockS hbodyrel)
          have heq₂X : _ = res₂' := heq₂; rw [← heq₂X] at hs₂
          exact ⟨_, Step.loopBreak hs₁ hcv hs₂, rfl⟩
  | .loopLeave hc hcv hbody =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | loopL hpostrel hbodyrel =>
          obtain ⟨res₁, hs₁, heq₁⟩ := cy_bwd hc hR hΔ CyRel.expr
          have heq₁X : _ = res₁ := heq₁; rw [← heq₁X] at hs₁
          obtain ⟨res₂', hs₂, heq₂⟩ := cy_bwd hbody hR hΔ (CyRel.blockS hbodyrel)
          have heq₂X : _ = res₂' := heq₂; rw [← heq₂X] at hs₂
          exact ⟨_, Step.loopLeave hs₁ hcv hs₂, rfl⟩
  | .loopBodyHalt hc hcv hbody =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | loopL hpostrel hbodyrel =>
          obtain ⟨res₁, hs₁, heq₁⟩ := cy_bwd hc hR hΔ CyRel.expr
          have heq₁X : _ = res₁ := heq₁; rw [← heq₁X] at hs₁
          obtain ⟨res₂', hs₂, heq₂⟩ := cy_bwd hbody hR hΔ (CyRel.blockS hbodyrel)
          have heq₂X : _ = res₂' := heq₂; rw [← heq₂X] at hs₂
          exact ⟨_, Step.loopBodyHalt hs₁ hcv hs₂, rfl⟩
  termination_by structural h

/-- Callee-body backward transfer with call simulation. -/
theorem carry_body_bwd {funs₂ : FunEnv D} {V₂ : VEnv D} {st : EvmState}
    {code : Code Op} {res₂ : Res D} (h : Step D funs₂ V₂ st code res₂) :
    ∀ {A W' : VEnv D} {bound : List Ident} (cenv funs₁ : FunEnv D) (W : VEnv D),
      V₂ = A ++ W' → carryBodyCode bound code →
      (∀ x ∈ bound, x ∈ A.map Prod.fst) →
      FunsAgree (calls := calls) (creates := creates) cenv funs₁ (carryCallNames code) →
      CyFunsRel (calls := calls) (creates := creates) funs₁ funs₂ →
      ∃ res₁, Step D cenv (A ++ W) st code res₁ ∧
        TResL (calls := calls) (creates := creates) W W'
          (carryPostBound bound code) res₁ res₂ := by
  match h with
  | .lit =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      exact ⟨_, Step.lit, .eres _⟩
  | @Step.var _ _ _ _ _ x v hv =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      subst hV
      have hx : x ∈ bound := by
        have h2 : carryExpr bound (.var x) = true := hsc
        have := List.all_eq_true.mp h2 x (by simp [exprVars])
        simpa using this
      have hxA : x ∈ A.map Prod.fst := hb x hx
      have hgv : VEnv.get A x = some v := by
        rw [← VEnv.get_append_mem hxA W']; exact hv
      refine ⟨_, Step.var ?_, .eres _⟩
      rw [VEnv.get_append_mem hxA W]; exact hgv
  | @Step.builtinOk _ _ _ _ _ op args argvals st1 rets st2 ha hbi =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      have hargs : carryArgs bound args = true := carryExpr_builtin_args hsc
      obtain ⟨res₁, hstep, htr⟩ := carry_body_bwd ha cenv funs₁ W hV
        (by simpa [carryBodyCode, carryCode] using hargs) hb
        (by simpa [carryCallNames, exprCallNames] using hag) hR
      subst hV
      cases htr with
      | eres => exact ⟨_, Step.builtinOk hstep hbi, .eres _⟩
  | @Step.builtinHalt _ _ _ _ _ op args argvals st1 st2 ha hbi =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      have hargs : carryArgs bound args = true := carryExpr_builtin_args hsc
      obtain ⟨res₁, hstep, htr⟩ := carry_body_bwd ha cenv funs₁ W hV
        (by simpa [carryBodyCode, carryCode] using hargs) hb
        (by simpa [carryCallNames, exprCallNames] using hag) hR
      subst hV
      cases htr with
      | eres => exact ⟨_, Step.builtinHalt hstep hbi, .eres _⟩
  | @Step.builtinArgsHalt _ _ _ _ _ op args st1 ha =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      have hargs : carryArgs bound args = true := carryExpr_builtin_args hsc
      obtain ⟨res₁, hstep, htr⟩ := carry_body_bwd ha cenv funs₁ W hV
        (by simpa [carryBodyCode, carryCode] using hargs) hb
        (by simpa [carryCallNames, exprCallNames] using hag) hR
      subst hV
      cases htr with
      | eres => exact ⟨_, Step.builtinArgsHalt hstep, .eres _⟩
  | @Step.callOk _ _ _ _ _ fn args argvals st1 decl cenv_c Vend st2 o ha hlk harity hbody ho =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      have hargs : carryArgs bound args = true := carryExpr_call_args hsc
      obtain ⟨res₁, hstep, htr⟩ := carry_body_bwd ha cenv funs₁ W hV
        (by simpa [carryBodyCode, carryCode] using hargs) hb
        (by refine hag.mono ?_; intro y hy;
            show y ∈ carryCallNames (Code.expr (.call fn args));
            simp only [carryCallNames, exprCallNames];
            exact List.mem_cons_of_mem fn (by simpa [carryCallNames] using hy)) hR
      subst hV
      cases htr with
      | eres =>
          have hagfn : lookupFun cenv fn = lookupFun funs₁ fn :=
            hag fn (by simp [carryCallNames, exprCallNames])
          obtain ⟨decl₁, cenv₁, hlk₁, hdecl, hcenvR⟩ := lookupFun_cyFunsRel_bwd hR hlk
          rw [← hagfn] at hlk₁
          obtain ⟨hps, hrs, Δf, hΔf, hbrel⟩ := hdecl
          obtain ⟨resb, hsb, heqb⟩ := cy_bwd hbody hcenvR hΔf (CyRel.blockS hbrel)
          have heqbX : _ = resb := heqb; rw [← heqbX] at hsb
          have hsb' : Step D cenv₁ (decl₁.params.zip argvals ++ bindZeros D decl₁.rets)
              st1 (.stmt (.block decl₁.body)) (.sres Vend st2 o) := by
            rw [hps, hrs]; exact hsb
          have harity' : argvals.length = decl₁.params.length := by rw [hps]; exact harity
          refine ⟨_, Step.callOk hstep hlk₁ harity' hsb' ho, ?_⟩
          rw [hrs]; exact .eres _
  | @Step.callHalt _ _ _ _ _ fn args argvals st1 decl cenv_c Vend st2 ha hlk harity hbody =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      have hargs : carryArgs bound args = true := carryExpr_call_args hsc
      obtain ⟨res₁, hstep, htr⟩ := carry_body_bwd ha cenv funs₁ W hV
        (by simpa [carryBodyCode, carryCode] using hargs) hb
        (by refine hag.mono ?_; intro y hy;
            show y ∈ carryCallNames (Code.expr (.call fn args));
            simp only [carryCallNames, exprCallNames];
            exact List.mem_cons_of_mem fn (by simpa [carryCallNames] using hy)) hR
      subst hV
      cases htr with
      | eres =>
          have hagfn : lookupFun cenv fn = lookupFun funs₁ fn :=
            hag fn (by simp [carryCallNames, exprCallNames])
          obtain ⟨decl₁, cenv₁, hlk₁, hdecl, hcenvR⟩ := lookupFun_cyFunsRel_bwd hR hlk
          rw [← hagfn] at hlk₁
          obtain ⟨hps, hrs, Δf, hΔf, hbrel⟩ := hdecl
          obtain ⟨resb, hsb, heqb⟩ := cy_bwd hbody hcenvR hΔf (CyRel.blockS hbrel)
          have heqbX : _ = resb := heqb; rw [← heqbX] at hsb
          have hsb' : Step D cenv₁ (decl₁.params.zip argvals ++ bindZeros D decl₁.rets)
              st1 (.stmt (.block decl₁.body)) (.sres Vend st2 .halt) := by
            rw [hps, hrs]; exact hsb
          have harity' : argvals.length = decl₁.params.length := by rw [hps]; exact harity
          exact ⟨_, Step.callHalt hstep hlk₁ harity' hsb', .eres _⟩
  | @Step.callArgsHalt _ _ _ _ _ fn args st1 ha =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      have hargs : carryArgs bound args = true := carryExpr_call_args hsc
      obtain ⟨res₁, hstep, htr⟩ := carry_body_bwd ha cenv funs₁ W hV
        (by simpa [carryBodyCode, carryCode] using hargs) hb
        (by refine hag.mono ?_; intro y hy;
            show y ∈ carryCallNames (Code.expr (.call fn args));
            simp only [carryCallNames, exprCallNames];
            exact List.mem_cons_of_mem fn (by simpa [carryCallNames] using hy)) hR
      subst hV
      cases htr with
      | eres => exact ⟨_, Step.callArgsHalt hstep, .eres _⟩
  | .argsNil =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      exact ⟨_, Step.argsNil, .eres _⟩
  | @Step.argsCons _ _ _ _ _ e rest restvals st1 v st2 hrest he =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      have hsc2 : (carryExpr bound e && carryArgs bound rest) = true := hsc
      rw [Bool.and_eq_true] at hsc2
      have hagE : FunsAgree (calls := calls) (creates := creates) cenv funs₁ (exprCallNames e) :=
        hag.mono (fun y hy => by
          show y ∈ argsCallNames (e :: rest); exact List.mem_append.mpr (Or.inl hy))
      have hagR : FunsAgree (calls := calls) (creates := creates) cenv funs₁ (argsCallNames rest) :=
        hag.mono (fun y hy => by
          show y ∈ argsCallNames (e :: rest); exact List.mem_append.mpr (Or.inr hy))
      obtain ⟨res₁, hstep₁, htr₁⟩ := carry_body_bwd hrest cenv funs₁ W hV
        (by simpa [carryBodyCode, carryCode] using hsc2.2) hb
        (by simpa [carryCallNames] using hagR) hR
      obtain ⟨res₃, hstep₂, htr₂⟩ := carry_body_bwd he cenv funs₁ W hV
        (by simpa [carryBodyCode, carryCode] using hsc2.1) hb
        (by simpa [carryCallNames] using hagE) hR
      cases htr₁ with
      | eres => cases htr₂ with
        | eres => exact ⟨_, Step.argsCons hstep₁ hstep₂, .eres _⟩
  | @Step.argsRestHalt _ _ _ _ _ e rest st1 hrest =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      have hsc2 : (carryExpr bound e && carryArgs bound rest) = true := hsc
      rw [Bool.and_eq_true] at hsc2
      have hagR : FunsAgree (calls := calls) (creates := creates) cenv funs₁ (argsCallNames rest) :=
        hag.mono (fun y hy => by
          show y ∈ argsCallNames (e :: rest); exact List.mem_append.mpr (Or.inr hy))
      obtain ⟨res₁, hstep₁, htr₁⟩ := carry_body_bwd hrest cenv funs₁ W hV
        (by simpa [carryBodyCode, carryCode] using hsc2.2) hb
        (by simpa [carryCallNames] using hagR) hR
      cases htr₁ with
      | eres => exact ⟨_, Step.argsRestHalt hstep₁, .eres _⟩
  | @Step.argsHeadHalt _ _ _ _ _ e rest restvals st1 st2 hrest he =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      have hsc2 : (carryExpr bound e && carryArgs bound rest) = true := hsc
      rw [Bool.and_eq_true] at hsc2
      have hagE : FunsAgree (calls := calls) (creates := creates) cenv funs₁ (exprCallNames e) :=
        hag.mono (fun y hy => by
          show y ∈ argsCallNames (e :: rest); exact List.mem_append.mpr (Or.inl hy))
      have hagR : FunsAgree (calls := calls) (creates := creates) cenv funs₁ (argsCallNames rest) :=
        hag.mono (fun y hy => by
          show y ∈ argsCallNames (e :: rest); exact List.mem_append.mpr (Or.inr hy))
      obtain ⟨res₁, hstep₁, htr₁⟩ := carry_body_bwd hrest cenv funs₁ W hV
        (by simpa [carryBodyCode, carryCode] using hsc2.2) hb
        (by simpa [carryCallNames] using hagR) hR
      obtain ⟨res₃, hstep₂, htr₂⟩ := carry_body_bwd he cenv funs₁ W hV
        (by simpa [carryBodyCode, carryCode] using hsc2.1) hb
        (by simpa [carryCallNames] using hagE) hR
      cases htr₁ with
      | eres => cases htr₂ with
        | eres => exact ⟨_, Step.argsHeadHalt hstep₁ hstep₂, .eres _⟩
  | .funDef =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      exact absurd hsc (by simp [carryBodyCode, carryCode, carryStmt])
  | @Step.block _ _ _ _ _ body Vb stb o hbody =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      have hstmts : carryLeaveStmts bound body := hsc
      have hpost : carryPostBound bound (Code.stmt (.block body)) = bound :=
        carryPostBound_block bound body
      have hhoist : hoist D body = [] := carryLeaveStmts_hoist_nil hstmts
      have hagb : FunsAgree (calls := calls) (creates := creates)
          (hoist D body :: cenv) (hoist D body :: funs₁) (carryCallNames (.stmts body)) := by
        rw [hhoist]
        exact FunsAgree.cons_nil (by simpa [carryCallNames, stmtCallNames] using hag)
      have hRb : CyFunsRel (calls := calls) (creates := creates)
          (hoist D body :: funs₁) (hoist D body :: funs₂) := by
        rw [hhoist]; exact CyFunsRel.cons_nil hR
      obtain ⟨res₁, hstep, htr⟩ :=
        carry_body_bwd hbody (hoist D body :: cenv) (hoist D body :: funs₁) W hV
          hstmts hb hagb hRb
      have hlenV : V₂.length ≤ Vb.length := venvLen_mono hbody rfl
      have hkeysV := venvKeys_suffix hbody rfl
      subst hV
      cases htr with
      | @norm A' st' hk =>
          have hlen : A.length ≤ A'.length := by
            rw [List.length_append, List.length_append] at hlenV; omega
          refine ⟨_, Step.block hstep, ?_⟩
          rw [hpost, restore_append hlen, restore_append hlen]
          exact .norm (fun x hx => by
            rw [restore_keys (keys_suffix_cancel hkeysV) hlen]; exact hb x hx)
      | @halt A' st' =>
          have hlen : A.length ≤ A'.length := by
            rw [List.length_append, List.length_append] at hlenV; omega
          refine ⟨_, Step.block hstep, ?_⟩
          rw [restore_append hlen, restore_append hlen]; exact .halt
      | @«leave» A' st' =>
          have hlen : A.length ≤ A'.length := by
            rw [List.length_append, List.length_append] at hlenV; omega
          refine ⟨_, Step.block hstep, ?_⟩
          rw [restore_append hlen, restore_append hlen]; exact TResL.leave
  | @Step.letZero _ _ _ _ _ vars =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      subst hV
      refine ⟨_, Step.letZero, ?_⟩
      rw [show bindZeros D vars ++ (A ++ W) = (bindZeros D vars ++ A) ++ W from
            (List.append_assoc _ _ _).symm,
          show bindZeros D vars ++ (A ++ W') = (bindZeros D vars ++ A) ++ W' from
            (List.append_assoc _ _ _).symm]
      refine .norm (fun x hx => ?_)
      have hpost : carryPostBound bound (Code.stmt (.letDecl vars none)) = vars ++ bound := by
        simp [carryPostBound, carryStmt]
      rw [hpost] at hx
      rw [List.map_append, bindZeros_keys]
      rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_append.mpr (Or.inl hx)
      · exact List.mem_append.mpr (Or.inr (hb x hx))
  | @Step.letVal _ _ _ _ _ vars e vals st1 he hlen =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      have hse : carryExpr bound e = true := by
        have h2 : (carryStmt bound (.letDecl vars (some e))).isSome = true := hsc
        by_cases hc : carryExpr bound e = true
        · exact hc
        · simp [carryStmt, hc] at h2
      obtain ⟨res₁, hstep, htr⟩ := carry_body_bwd he cenv funs₁ W hV
        (by simpa [carryBodyCode, carryCode] using hse) hb
        (by simpa [carryCallNames, stmtCallNames] using hag) hR
      subst hV
      cases htr with
      | eres =>
          refine ⟨_, Step.letVal hstep hlen, ?_⟩
          rw [show vars.zip vals ++ (A ++ W) = (vars.zip vals ++ A) ++ W from
                (List.append_assoc _ _ _).symm,
              show vars.zip vals ++ (A ++ W') = (vars.zip vals ++ A) ++ W' from
                (List.append_assoc _ _ _).symm]
          refine .norm (fun x hx => ?_)
          have hpost : carryPostBound bound (Code.stmt (.letDecl vars (some e))) =
              vars ++ bound := by simp [carryPostBound, carryStmt, hse]
          rw [hpost] at hx
          rw [List.map_append, List.map_fst_zip (by omega)]
          rcases List.mem_append.mp hx with hx | hx
          · exact List.mem_append.mpr (Or.inl hx)
          · exact List.mem_append.mpr (Or.inr (hb x hx))
  | @Step.letHalt _ _ _ _ _ vars e st1 he =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      have hse : carryExpr bound e = true := by
        have h2 : (carryStmt bound (.letDecl vars (some e))).isSome = true := hsc
        by_cases hc : carryExpr bound e = true
        · exact hc
        · simp [carryStmt, hc] at h2
      obtain ⟨res₁, hstep, htr⟩ := carry_body_bwd he cenv funs₁ W hV
        (by simpa [carryBodyCode, carryCode] using hse) hb
        (by simpa [carryCallNames, stmtCallNames] using hag) hR
      subst hV
      cases htr with
      | eres => exact ⟨_, Step.letHalt hstep, .halt⟩
  | @Step.assignVal _ _ _ _ _ vars e vals st1 he hlen =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      have hsc' : vars.all bound.contains = true ∧ carryExpr bound e = true := by
        have h2 : (carryStmt bound (.assign vars e)).isSome = true := hsc
        by_cases hc : (vars.all bound.contains && carryExpr bound e) = true
        · rw [Bool.and_eq_true] at hc; exact hc
        · simp [carryStmt, hc] at h2
      have hvars : ∀ x ∈ vars, x ∈ A.map Prod.fst := fun x hx =>
        hb x (all_contains_subset hsc'.1 x hx)
      obtain ⟨res₁, hstep, htr⟩ := carry_body_bwd he cenv funs₁ W hV
        (by simpa [carryBodyCode, carryCode] using hsc'.2) hb
        (by simpa [carryCallNames, stmtCallNames] using hag) hR
      subst hV
      cases htr with
      | eres =>
          refine ⟨_, Step.assignVal hstep hlen, ?_⟩
          rw [VEnv.setMany_append_mem hvars, VEnv.setMany_append_mem hvars]
          refine .norm (fun x hx => ?_)
          have hpost : carryPostBound bound (Code.stmt (.assign vars e)) = bound := by
            simp [carryPostBound, carryStmt, hsc'.1, hsc'.2]
          rw [hpost] at hx
          rw [VEnv.setMany_keys («D» := D)]
          exact hb x hx
  | @Step.assignHalt _ _ _ _ _ vars e st1 he =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      have hse : carryExpr bound e = true := by
        have h2 : (carryStmt bound (.assign vars e)).isSome = true := hsc
        by_cases hc : (vars.all bound.contains && carryExpr bound e) = true
        · rw [Bool.and_eq_true] at hc; exact hc.2
        · simp [carryStmt, hc] at h2
      obtain ⟨res₁, hstep, htr⟩ := carry_body_bwd he cenv funs₁ W hV
        (by simpa [carryBodyCode, carryCode] using hse) hb
        (by simpa [carryCallNames, stmtCallNames] using hag) hR
      subst hV
      cases htr with
      | eres => exact ⟨_, Step.assignHalt hstep, .halt⟩
  | @Step.exprStmt _ _ _ _ _ e st1 he =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      have hse : carryExpr bound e = true := by
        have h2 : (carryStmt bound (.exprStmt e)).isSome = true := hsc
        by_cases hc : carryExpr bound e = true
        · exact hc
        · simp [carryStmt, hc] at h2
      obtain ⟨res₁, hstep, htr⟩ := carry_body_bwd he cenv funs₁ W hV
        (by simpa [carryBodyCode, carryCode] using hse) hb
        (by simpa [carryCallNames, stmtCallNames] using hag) hR
      subst hV
      cases htr with
      | eres =>
          refine ⟨_, Step.exprStmt hstep, ?_⟩
          refine .norm (fun x hx => ?_)
          have hpost : carryPostBound bound (Code.stmt (.exprStmt e)) = bound := by
            simp [carryPostBound, carryStmt, hse]
          rw [hpost] at hx
          exact hb x hx
  | @Step.exprStmtHalt _ _ _ _ _ e st1 he =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      have hse : carryExpr bound e = true := by
        have h2 : (carryStmt bound (.exprStmt e)).isSome = true := hsc
        by_cases hc : carryExpr bound e = true
        · exact hc
        · simp [carryStmt, hc] at h2
      obtain ⟨res₁, hstep, htr⟩ := carry_body_bwd he cenv funs₁ W hV
        (by simpa [carryBodyCode, carryCode] using hse) hb
        (by simpa [carryCallNames, stmtCallNames] using hag) hR
      subst hV
      cases htr with
      | eres => exact ⟨_, Step.exprStmtHalt hstep, .halt⟩
  | @Step.ifTrue _ _ _ _ _ c body cv st1 V' st2 o hc hcv hbody =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      have hsc' : carryExpr bound c = true ∧ carryStmts bound body = true := by
        have h2 : (carryStmt bound (.cond c body)).isSome = true := hsc
        by_cases hcnd : (carryExpr bound c && carryStmts bound body) = true
        · rw [Bool.and_eq_true] at hcnd; exact hcnd
        · simp [carryStmt, hcnd] at h2
      have hagc : FunsAgree (calls := calls) (creates := creates) cenv funs₁ (exprCallNames c) :=
        hag.mono (fun y hy => by
          show y ∈ stmtCallNames (.cond c body); exact List.mem_append.mpr (Or.inl hy))
      have hagb : FunsAgree (calls := calls) (creates := creates) cenv funs₁
          (carryCallNames (.stmt (.block body))) :=
        hag.mono (fun y hy => by
          show y ∈ stmtCallNames (.cond c body)
          exact List.mem_append.mpr (Or.inr (by simpa [carryCallNames, stmtCallNames] using hy)))
      obtain ⟨res₁, hstepc, htrc⟩ := carry_body_bwd hc cenv funs₁ W hV
        (by simpa [carryBodyCode, carryCode] using hsc'.1) hb hagc hR
      have hscb : carryBodyCode bound (Code.stmt (.block body)) := Or.inl hsc'.2
      obtain ⟨res₃, hstepb, htrb⟩ := carry_body_bwd hbody cenv funs₁ W hV hscb hb hagb hR
      subst hV
      cases htrc with
      | eres =>
          have hpostb : carryPostBound bound (Code.stmt (.block body)) = bound :=
            carryPostBound_block bound body
          have hpost : carryPostBound bound (Code.stmt (.cond c body)) = bound := by
            simp [carryPostBound, carryStmt, hsc'.1, hsc'.2]
          rw [hpostb] at htrb
          rw [hpost]
          cases htrb with
          | norm hk => exact ⟨_, Step.ifTrue hstepc hcv hstepb, .norm hk⟩
          | halt => exact ⟨_, Step.ifTrue hstepc hcv hstepb, .halt⟩
          | «leave» => exact ⟨_, Step.ifTrue hstepc hcv hstepb, TResL.leave⟩
  | @Step.ifFalse _ _ _ _ _ c body cv st1 hc hcv =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      have hsc' : carryExpr bound c = true := by
        have h2 : (carryStmt bound (.cond c body)).isSome = true := hsc
        by_cases hcnd : (carryExpr bound c && carryStmts bound body) = true
        · rw [Bool.and_eq_true] at hcnd; exact hcnd.1
        · simp [carryStmt, hcnd] at h2
      have hagc : FunsAgree (calls := calls) (creates := creates) cenv funs₁ (exprCallNames c) :=
        hag.mono (fun y hy => by
          show y ∈ stmtCallNames (.cond c body); exact List.mem_append.mpr (Or.inl hy))
      obtain ⟨res₁, hstepc, htrc⟩ := carry_body_bwd hc cenv funs₁ W hV
        (by simpa [carryBodyCode, carryCode] using hsc') hb hagc hR
      subst hV
      cases htrc with
      | eres =>
          refine ⟨_, Step.ifFalse hstepc hcv, .norm (fun x hx => ?_)⟩
          exact hb x (by
            have : carryPostBound bound (Code.stmt (.cond c body)) = bound := by
              simp only [carryPostBound, carryStmt]; split <;> rfl
            rwa [this] at hx)
  | @Step.ifHalt _ _ _ _ _ c body st1 hc =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      have hsc' : carryExpr bound c = true := by
        have h2 : (carryStmt bound (.cond c body)).isSome = true := hsc
        by_cases hcnd : (carryExpr bound c && carryStmts bound body) = true
        · rw [Bool.and_eq_true] at hcnd; exact hcnd.1
        · simp [carryStmt, hcnd] at h2
      have hagc : FunsAgree (calls := calls) (creates := creates) cenv funs₁ (exprCallNames c) :=
        hag.mono (fun y hy => by
          show y ∈ stmtCallNames (.cond c body); exact List.mem_append.mpr (Or.inl hy))
      obtain ⟨res₁, hstepc, htrc⟩ := carry_body_bwd hc cenv funs₁ W hV
        (by simpa [carryBodyCode, carryCode] using hsc') hb hagc hR
      subst hV
      cases htrc with
      | eres => exact ⟨_, Step.ifHalt hstepc, .halt⟩
  | @Step.switchExec _ _ _ _ _ c cases' dflt cv st1 V' st2 o hc hsel =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      have hsc' : carryExpr bound c = true ∧ carryCases bound cases' = true ∧
          carryDflt bound dflt = true := by
        have h2 : (carryStmt bound (.switch c cases' dflt)).isSome = true := hsc
        by_cases hcnd : (carryExpr bound c && carryCases bound cases' &&
            carryDflt bound dflt) = true
        · rw [Bool.and_eq_true, Bool.and_eq_true] at hcnd; exact ⟨hcnd.1.1, hcnd.1.2, hcnd.2⟩
        · simp [carryStmt, hcnd] at h2
      have hagc : FunsAgree (calls := calls) (creates := creates) cenv funs₁ (exprCallNames c) :=
        hag.mono (fun y hy => by
          show y ∈ stmtCallNames (.switch c cases' dflt)
          exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hy))))
      have hagsel : FunsAgree (calls := calls) (creates := creates) cenv funs₁
          (carryCallNames (.stmt (.block (selectSwitch D cv cases' dflt)))) := by
        refine hag.mono (fun y hy => ?_)
        show y ∈ stmtCallNames (.switch c cases' dflt)
        have hsub := selectSwitch_callNames_sub (calls := calls) (creates := creates)
          (cv := cv) (cases := cases') (dflt := dflt) y
          (by simpa [carryCallNames, stmtCallNames] using hy)
        rcases List.mem_append.mp hsub with hh | hh
        · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hh)))
        · exact List.mem_append.mpr (Or.inr hh)
      obtain ⟨res₁, hstepc, htrc⟩ := carry_body_bwd hc cenv funs₁ W hV
        (by simpa [carryBodyCode, carryCode] using hsc'.1) hb hagc hR
      have hsels : carryStmts bound (selectSwitch D cv cases' dflt) = true :=
        carry_selectSwitch hsc'.2.1 hsc'.2.2
      have hscb : carryBodyCode bound (Code.stmt (.block (selectSwitch D cv cases' dflt))) :=
        Or.inl hsels
      obtain ⟨res₃, hstepb, htrb⟩ := carry_body_bwd hsel cenv funs₁ W hV hscb hb hagsel hR
      subst hV
      cases htrc with
      | eres =>
          have hpostb : carryPostBound bound
              (Code.stmt (.block (selectSwitch D cv cases' dflt))) = bound :=
            carryPostBound_block bound _
          have hpost : carryPostBound bound (Code.stmt (.switch c cases' dflt)) = bound := by
            simp [carryPostBound, carryStmt, hsc'.1, hsc'.2.1, hsc'.2.2]
          rw [hpostb] at htrb
          rw [hpost]
          cases htrb with
          | norm hk => exact ⟨_, Step.switchExec hstepc hstepb, .norm hk⟩
          | halt => exact ⟨_, Step.switchExec hstepc hstepb, .halt⟩
          | «leave» => exact ⟨_, Step.switchExec hstepc hstepb, TResL.leave⟩
  | @Step.switchHalt _ _ _ _ _ c cases' dflt st1 hc =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      have hsc' : carryExpr bound c = true := by
        have h2 : (carryStmt bound (.switch c cases' dflt)).isSome = true := hsc
        by_cases hcnd : (carryExpr bound c && carryCases bound cases' &&
            carryDflt bound dflt) = true
        · rw [Bool.and_eq_true, Bool.and_eq_true] at hcnd; exact hcnd.1.1
        · simp [carryStmt, hcnd] at h2
      have hagc : FunsAgree (calls := calls) (creates := creates) cenv funs₁ (exprCallNames c) :=
        hag.mono (fun y hy => by
          show y ∈ stmtCallNames (.switch c cases' dflt)
          exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hy))))
      obtain ⟨res₁, hstepc, htrc⟩ := carry_body_bwd hc cenv funs₁ W hV
        (by simpa [carryBodyCode, carryCode] using hsc') hb hagc hR
      subst hV
      cases htrc with
      | eres => exact ⟨_, Step.switchHalt hstepc, .halt⟩
  | @Step.forLoop _ _ _ _ _ init c post body Vinit stinit Vend stend o hinit hloop =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      exact absurd hsc (by simp [carryBodyCode, carryCode, carryStmt])
  | @Step.forInitHalt _ _ _ _ _ init c post body Vinit stinit hinit =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      exact absurd hsc (by simp [carryBodyCode, carryCode, carryStmt])
  | .«break» =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      exact absurd hsc (by simp [carryBodyCode, carryCode, carryStmt])
  | .«continue» =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      exact absurd hsc (by simp [carryBodyCode, carryCode, carryStmt])
  | .«leave» =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      exact absurd hsc (by simp [carryBodyCode, carryCode, carryStmt])
  | .seqNil =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      subst hV
      exact ⟨_, Step.seqNil, .norm (fun x hx => by simp [carryPostBound] at hx)⟩
  | @Step.seqCons _ _ _ _ _ s rest V1 st1 V2 st2 o hs hrest =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      have hlv : carryLeaveStmts bound (s :: rest) := hsc
      rcases carryLeaveStmts_cons_inv hlv with ⟨bound₁, hstmt, hrest'⟩ | ⟨rfl, rfl⟩
      · have hags : FunsAgree (calls := calls) (creates := creates) cenv funs₁ (stmtCallNames s) :=
          hag.mono (fun y hy => by
            show y ∈ stmtsCallNames (s :: rest); exact List.mem_append.mpr (Or.inl hy))
        have hagr : FunsAgree (calls := calls) (creates := creates) cenv funs₁
            (stmtsCallNames rest) :=
          hag.mono (fun y hy => by
            show y ∈ stmtsCallNames (s :: rest); exact List.mem_append.mpr (Or.inr hy))
        obtain ⟨res₁, hstep₁, htr₁⟩ := carry_body_bwd hs cenv funs₁ W hV
          (carryBodyCode_of_stmt hstmt) hb
          (by simpa [carryCallNames] using hags) hR
        have hpost₁ : carryPostBound bound (Code.stmt s) = bound₁ := by
          simp [carryPostBound, hstmt]
        rw [hpost₁] at htr₁
        obtain ⟨A₁, hV1, hres₁, hk⟩ := TResL.norm_inv' htr₁
        obtain ⟨res₃, hstep₂, htr₂⟩ := carry_body_bwd hrest cenv funs₁ W hV1
          hrest' hk (by simpa [carryCallNames] using hagr) hR
        subst hres₁
        cases htr₂ with
        | norm hk₂ => exact ⟨_, Step.seqCons hstep₁ hstep₂, .norm hk₂⟩
        | halt => exact ⟨_, Step.seqCons hstep₁ hstep₂, .halt⟩
        | «leave» => exact ⟨_, Step.seqCons hstep₁ hstep₂, TResL.leave⟩
      · cases hs
  | @Step.seqStop _ _ _ _ _ s rest V1 st1 o hs hne =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      have hlv : carryLeaveStmts bound (s :: rest) := hsc
      rcases carryLeaveStmts_cons_inv hlv with ⟨bound₁, hstmt, hrest'⟩ | ⟨rfl, rfl⟩
      · have hags : FunsAgree (calls := calls) (creates := creates) cenv funs₁ (stmtCallNames s) :=
          hag.mono (fun y hy => by
            show y ∈ stmtsCallNames (s :: rest); exact List.mem_append.mpr (Or.inl hy))
        obtain ⟨res₁, hstep₁, htr₁⟩ := carry_body_bwd hs cenv funs₁ W hV
          (carryBodyCode_of_stmt hstmt) hb
          (by simpa [carryCallNames] using hags) hR
        cases htr₁ with
        | norm hk => exact absurd rfl hne
        | halt => exact ⟨_, Step.seqStop hstep₁ (by simp), .halt⟩
        | «leave» => exact ⟨_, Step.seqStop hstep₁ (by simp), TResL.leave⟩
      · cases hs with
        | «leave» => subst hV; exact ⟨_, Step.seqStop Step.leave (by simp), TResL.leave⟩
  | .loopDone hc hcz =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      exact absurd hsc (by simp [carryBodyCode, carryCode])
  | .loopCondHalt hc =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      exact absurd hsc (by simp [carryBodyCode, carryCode])
  | .loopStep hc hcv hbody hob hpost hnext =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      exact absurd hsc (by simp [carryBodyCode, carryCode])
  | .loopPostHalt hc hcv hbody hob hpost =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      exact absurd hsc (by simp [carryBodyCode, carryCode])
  | .loopBreak hc hcv hbody =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      exact absurd hsc (by simp [carryBodyCode, carryCode])
  | .loopLeave hc hcv hbody =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      exact absurd hsc (by simp [carryBodyCode, carryCode])
  | .loopBodyHalt hc hcv hbody =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      exact absurd hsc (by simp [carryBodyCode, carryCode])
  termination_by structural h

/-- **Structural inlineCore inversion.** A target run of `inlineCore d xs as`
dissects into the source call's constituents (argument evaluation, callee body
run under the *source* callee env `cenv₀`, read-out), with the carry body
transferred back via `carry_body_bwd`. Structural on the whole block derivation
(so the callee body stays a genuine subterm). -/
theorem peelBody {d : IDecl} {xs : List Ident} {as : List (Expr Op)}
    {funs₂ : FunEnv D} {V Z E : VEnv D} {st : EvmState}
    {codeP : Code Op} {res : Res D}
    (hs : Step D funs₂ E st codeP res)
    (hE : E = Z ++ V)
    (hcodeP : codeP = .stmt (inlineCore d xs as))
    (hsc : carryStmts (d.ps ++ d.rs) d.ss = true)
    (hlen_as : as.length = d.ps.length) (hnc : argsHaveCall as = false)
    (hsh : argsShadowOK d.rs (d.ps.zip as) = true)
    (hxout : ∀ x ∈ xs, x ∉ d.ps ++ d.rs) (hlen_xs : xs.length = d.rs.length)
    (hZ : ∀ y ∈ varsList as, y ∉ Z.map Prod.fst)
    (funs₁ cenv₀ : FunEnv D)
    (hagbody : ∀ g ∈ stmtsCallNames d.ss, lookupFun funs₁ g = lookupFun cenv₀ g)
    (hR : CyFunsRel (calls := calls) (creates := creates) funs₁ funs₂) :
    (∃ argvals st1 Vend str,
      Step D funs₁ V st (.args as) (.eres (.vals argvals st1)) ∧
      Step D cenv₀ (d.ps.zip argvals ++ bindZeros D d.rs) st1
        (.stmt (.block d.ss)) (.sres Vend str .normal) ∧
      res = .sres (VEnv.setMany (Z ++ V) xs (d.rs.map
        (fun r => (VEnv.get Vend r).getD (evmWithExternal calls creates).zero))) str .normal) ∨
    (∃ argvals st1 Vend str,
      Step D funs₁ V st (.args as) (.eres (.vals argvals st1)) ∧
      Step D cenv₀ (d.ps.zip argvals ++ bindZeros D d.rs) st1
        (.stmt (.block d.ss)) (.sres Vend str .halt) ∧
      res = .sres (Z ++ V) str .halt) ∨
    (∃ str, Step D funs₁ V st (.args as) (.eres (.halt str)) ∧
      res = .sres (Z ++ V) str .halt) := by
  match hs with
  | @Step.block _ _ _ _ _ ib Vb stb ob hb =>
      injection hcodeP with hc1
      injection hc1 with hinner
      subst hinner
      have hhoist : hoist D ([Stmt.letDecl d.rs none]
          ++ (d.ps.zip as).reverse.map (fun pa => Stmt.letDecl [pa.1] (some pa.2))
          ++ [Stmt.block d.ss]
          ++ (xs.zip d.rs).map (fun xr => Stmt.assign [xr.1] (Expr.var xr.2))) = [] :=
        inlineStmts_hoist_nil d xs as
      cases hb with
      | seqStop hlet hne => cases hlet with | letZero => exact absurd rfl hne
      | seqCons hlet htail =>
          cases hlet with
          | letZero =>
              have hRb : CyFunsRel (calls := calls) (creates := creates)
                  (hoist D ([Stmt.letDecl d.rs none]
                    ++ (d.ps.zip as).reverse.map (fun pa => Stmt.letDecl [pa.1] (some pa.2))
                    ++ [Stmt.block d.ss]
                    ++ (xs.zip d.rs).map (fun xr => Stmt.assign [xr.1] (Expr.var xr.2))) :: funs₁)
                  (hoist D ([Stmt.letDecl d.rs none]
                    ++ (d.ps.zip as).reverse.map (fun pa => Stmt.letDecl [pa.1] (some pa.2))
                    ++ [Stmt.block d.ss]
                    ++ (xs.zip d.rs).map (fun xr => Stmt.assign [xr.1] (Expr.var xr.2))) :: funs₂) := by
                rw [hhoist]; exact CyFunsRel.cons_nil hR
              have hag_body : ∀ g ∈ stmtsCallNames d.ss,
                  lookupFun cenv₀ g = lookupFun (hoist D ([Stmt.letDecl d.rs none]
                    ++ (d.ps.zip as).reverse.map (fun pa => Stmt.letDecl [pa.1] (some pa.2))
                    ++ [Stmt.block d.ss]
                    ++ (xs.zip d.rs).map (fun xr => Stmt.assign [xr.1] (Expr.var xr.2))) :: funs₁) g := by
                intro g hg
                rw [hhoist]
                exact (hagbody g hg).symm
              rcases peelArgs htail (V := V) (Z := Z) (Pfr := (d.ps.zip as).reverse)
                  (Ppeeled := []) (valsDone := []) (by simp) rfl (by rw [hE]; simp)
                  Step.argsNil (by simp) hsc hlen_as hnc hsh hxout hlen_xs hZ hRb hag_body
                with ⟨argvals, st1, Vend, hargs, hbody, hVb, hoeq⟩
                  | ⟨argvals, st1, Vend, hargs, hbody, hVb, hoeq⟩
                  | ⟨M, hargs, hVb, hoeq⟩
              · refine Or.inl ⟨argvals, st1, Vend, stb, hargs, hbody, ?_⟩
                rw [hoeq, hE, hVb, restore_exact (VEnv.setMany_length _ _ _)]
              · refine Or.inr (Or.inl ⟨argvals, st1, Vend, stb, hargs, hbody, ?_⟩)
                rw [hoeq, hE, hVb, restore_exact rfl]
              · refine Or.inr (Or.inr ⟨stb, hargs, ?_⟩)
                rw [hoeq, hE, hVb, restore_exact rfl]
  | .lit => cases hcodeP
  | .var .. => cases hcodeP
  | .builtinOk .. => cases hcodeP
  | .builtinHalt .. => cases hcodeP
  | .builtinArgsHalt .. => cases hcodeP
  | .callOk .. => cases hcodeP
  | .callHalt .. => cases hcodeP
  | .callArgsHalt .. => cases hcodeP
  | .argsNil => cases hcodeP
  | .argsCons .. => cases hcodeP
  | .argsRestHalt .. => cases hcodeP
  | .argsHeadHalt .. => cases hcodeP
  | .funDef => cases hcodeP
  | .letZero => cases hcodeP
  | .letVal .. => cases hcodeP
  | .letHalt .. => cases hcodeP
  | .assignVal .. => cases hcodeP
  | .assignHalt .. => cases hcodeP
  | .exprStmt .. => cases hcodeP
  | .exprStmtHalt .. => cases hcodeP
  | .ifTrue .. => cases hcodeP
  | .ifFalse .. => cases hcodeP
  | .ifHalt .. => cases hcodeP
  | .switchExec .. => cases hcodeP
  | .switchHalt .. => cases hcodeP
  | .forLoop .. => cases hcodeP
  | .forInitHalt .. => cases hcodeP
  | .«break» => cases hcodeP
  | .«continue» => cases hcodeP
  | .«leave» => cases hcodeP
  | .seqNil => cases hcodeP
  | .seqCons .. => cases hcodeP
  | .seqStop .. => cases hcodeP
  | .loopDone .. => cases hcodeP
  | .loopCondHalt .. => cases hcodeP
  | .loopStep .. => cases hcodeP
  | .loopPostHalt .. => cases hcodeP
  | .loopBreak .. => cases hcodeP
  | .loopLeave .. => cases hcodeP
  | .loopBodyHalt .. => cases hcodeP
  termination_by structural hs

/-- The argument-let peel + carry body transfer + read-out, structural on the
statement-sequence derivation.  `Pfr` are the still-to-peel argument pairs in
argLets order; `Ppeeled`/`valsDone` the already-peeled ones, threaded via the
source-side accumulator `hacc`. -/
theorem peelArgs {d : IDecl} {xs : List Ident} {as : List (Expr Op)}
    {funs₁ cenv₀ funsI Sfuns : FunEnv D} {V Z : VEnv D} {st : EvmState}
    {Ecur : VEnv D} {st_cur : EvmState} {Lrem : List (Stmt Op)}
    {Vinner : VEnv D} {str : EvmState} {o : Outcome}
    (hseq : Step D Sfuns Ecur st_cur (.stmts Lrem) (.sres Vinner str o))
    {Pfr Ppeeled : List (Ident × Expr Op)} {valsDone : List U256}
    (hP : Pfr.reverse ++ Ppeeled = d.ps.zip as)
    (hLrem : Lrem = Pfr.map (fun pa => Stmt.letDecl [pa.1] (some pa.2))
      ++ [Stmt.block d.ss] ++ (xs.zip d.rs).map (fun xr => Stmt.assign [xr.1] (Expr.var xr.2)))
    (hEcur : Ecur = (Ppeeled.map Prod.fst).zip valsDone ++ (bindZeros D d.rs ++ (Z ++ V)))
    (hacc : Step D funs₁ V st (.args (Ppeeled.map Prod.snd))
      (.eres (.vals valsDone st_cur)))
    (hvlen : valsDone.length = Ppeeled.length)
    (hsc : carryStmts (d.ps ++ d.rs) d.ss = true)
    (hlen_as : as.length = d.ps.length) (hnc : argsHaveCall as = false)
    (hsh : argsShadowOK d.rs (d.ps.zip as) = true)
    (hxout : ∀ x ∈ xs, x ∉ d.ps ++ d.rs) (hlen_xs : xs.length = d.rs.length)
    (hZ : ∀ y ∈ varsList as, y ∉ Z.map Prod.fst)
    (hRb : CyFunsRel (calls := calls) (creates := creates) funsI Sfuns)
    (hag_body : ∀ g ∈ stmtsCallNames d.ss, lookupFun cenv₀ g = lookupFun funsI g) :
    (∃ argvals st1 Vend,
      Step D funs₁ V st (.args as) (.eres (.vals argvals st1)) ∧
      Step D cenv₀ (d.ps.zip argvals ++ bindZeros D d.rs) st1
        (.stmt (.block d.ss)) (.sres Vend str .normal) ∧
      Vinner = Vend ++ VEnv.setMany (Z ++ V) xs (d.rs.map
        (fun r => (VEnv.get Vend r).getD (evmWithExternal calls creates).zero)) ∧
      o = .normal) ∨
    (∃ argvals st1 Vend,
      Step D funs₁ V st (.args as) (.eres (.vals argvals st1)) ∧
      Step D cenv₀ (d.ps.zip argvals ++ bindZeros D d.rs) st1
        (.stmt (.block d.ss)) (.sres Vend str .halt) ∧
      Vinner = Vend ++ (Z ++ V) ∧ o = .halt) ∨
    (∃ M : VEnv D, Step D funs₁ V st (.args as) (.eres (.halt str)) ∧
      Vinner = M ++ (Z ++ V) ∧ o = .halt) := by
  sorry

end

end YulEvmCompiler.Optimizer
