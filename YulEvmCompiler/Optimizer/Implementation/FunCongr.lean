import YulSemantics.Equiv

set_option warningAsError true

/-!
# YulEvmCompiler.Optimizer.Implementation.FunCongr

The **function-environment congruence** that `YulSemantics.Equiv` explicitly
defers: replacing function bodies by `EquivBlock`-equivalent bodies (same
signatures) preserves whole-program semantics. This is what lets an optimizer
pass rewrite *inside* `funDef` bodies — without it, `EquivBlock.of_stmts` only
covers rewrites that leave the hoisted function scope untouched.

## Contents

* `FunsRel` — a pointwise relation on function environments: related scopes of
  functions with equal names/signatures and `EquivBlock`-equivalent bodies.
* `Step.funs_congr` — the big rule induction: a `Step` derivation transports
  across `FunsRel` (same code, related function environments).
* `EquivBlock.of_stmts_funs` — the block congruence that *does* allow the hoisted
  scope to change, as long as the two scopes are `ScopeRel`-related.

Nothing here is dialect-specific; it is generic Yul meta-theory (kept in this
repo rather than the pinned semantics). It is only used to *discharge* a pass's
`Sound` obligation, so it is not part of the audited surface.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics

variable {D : Dialect} [DecidableEq D.Value]

/-! ### The relation on function environments -/

/-- Two function declarations agree on signature and have equivalent bodies. -/
def FDeclRel (D : Dialect) [DecidableEq D.Value] (d₁ d₂ : FDecl D) : Prop :=
  d₁.params = d₂.params ∧ d₁.rets = d₂.rets ∧ EquivBlock D d₁.body d₂.body

/-- Two scopes are related when, pairwise, they bind the same names to
signature-equal, body-equivalent declarations. -/
def ScopeRel (D : Dialect) [DecidableEq D.Value] (s₁ s₂ : FScope D) : Prop :=
  List.Forall₂ (fun p q => p.1 = q.1 ∧ FDeclRel D p.2 q.2) s₁ s₂

/-- Two function environments are related scope-by-scope. -/
def FunsRel (D : Dialect) [DecidableEq D.Value] (f₁ f₂ : FunEnv D) : Prop :=
  List.Forall₂ (ScopeRel D) f₁ f₂

theorem FDeclRel.refl (d : FDecl D) : FDeclRel D d d := ⟨rfl, rfl, EquivBlock.refl _⟩

theorem FDeclRel.symm {d₁ d₂ : FDecl D} (h : FDeclRel D d₁ d₂) : FDeclRel D d₂ d₁ :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

theorem ScopeRel.refl (s : FScope D) : ScopeRel D s s := by
  induction s with
  | nil => exact .nil
  | cons p t ih => exact .cons ⟨rfl, FDeclRel.refl _⟩ ih

theorem ScopeRel.symm {s₁ s₂ : FScope D} (h : ScopeRel D s₁ s₂) : ScopeRel D s₂ s₁ := by
  induction h with
  | nil => exact .nil
  | cons hpq _ ih => exact .cons ⟨hpq.1.symm, hpq.2.symm⟩ ih

theorem FunsRel.refl (f : FunEnv D) : FunsRel D f f := by
  induction f with
  | nil => exact .nil
  | cons s t ih => exact .cons (ScopeRel.refl _) ih

theorem FunsRel.symm {f₁ f₂ : FunEnv D} (h : FunsRel D f₁ f₂) : FunsRel D f₂ f₁ := by
  induction h with
  | nil => exact .nil
  | cons hs _ ih => exact .cons hs.symm ih

/-- Extend related environments by a common outer scope. -/
theorem FunsRel.cons_same (s : FScope D) {f₁ f₂ : FunEnv D} (h : FunsRel D f₁ f₂) :
    FunsRel D (s :: f₁) (s :: f₂) := .cons (ScopeRel.refl s) h

/-! ### `lookupFun` transports across `FunsRel` -/

/-- A scope lookup transports across `ScopeRel`: the same name resolves in both
scopes (or in neither) to signature-equal, body-equivalent declarations. -/
theorem scopeRel_find {s₁ s₂ : FScope D} (h : ScopeRel D s₁ s₂) (fn : Ident) :
    (s₁.find? (fun p => p.1 = fn) = none ∧ s₂.find? (fun p => p.1 = fn) = none) ∨
    (∃ p q, s₁.find? (fun p => p.1 = fn) = some p ∧ s₂.find? (fun p => p.1 = fn) = some q ∧
      p.1 = q.1 ∧ FDeclRel D p.2 q.2) := by
  induction h with
  | nil => left; simp
  | @cons p q u₁ u₂ hpq _ ih =>
      by_cases hp : p.1 = fn
      · right
        refine ⟨p, q, ?_, ?_, hpq.1, hpq.2⟩
        · exact List.find?_cons_of_pos (by simp [hp])
        · exact List.find?_cons_of_pos (by simp [← hpq.1, hp])
      · rw [List.find?_cons_of_neg (by simp [hp]),
            List.find?_cons_of_neg (by simp [← hpq.1, hp])]
        exact ih

/-- `lookupFun` transports across `FunsRel`: a resolved function has a related
counterpart with an equal signature, an equivalent body, and a related closure
environment. -/
theorem lookupFun_funsRel {f₁ f₂ : FunEnv D} (hR : FunsRel D f₁ f₂) :
    ∀ {fn : Ident} {decl : FDecl D} {cenv : FunEnv D},
      lookupFun f₁ fn = some (decl, cenv) →
      ∃ decl' cenv', lookupFun f₂ fn = some (decl', cenv') ∧
        decl'.params = decl.params ∧ decl'.rets = decl.rets ∧
        EquivBlock D decl.body decl'.body ∧ FunsRel D cenv cenv' := by
  induction hR with
  | nil => intro fn decl cenv h; simp [lookupFun] at h
  | @cons s₁ s₂ t₁ t₂ hs hR' ih =>
      intro fn decl cenv h
      rcases scopeRel_find hs fn with ⟨hn₁, hn₂⟩ | ⟨p, q, hp₁, hp₂, hkey, hd⟩
      · -- name not in this scope: recurse into the tails
        rw [lookupFun, hn₁] at h
        obtain ⟨decl', cenv', hl', hpar, hret, hbody, hRc⟩ := ih h
        exact ⟨decl', cenv', by rw [lookupFun, hn₂]; exact hl', hpar, hret, hbody, hRc⟩
      · -- name found in this scope
        rw [lookupFun, hp₁] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hd_eq, hcenv_eq⟩ := h
        subst hd_eq; subst hcenv_eq
        refine ⟨q.2, s₂ :: t₂, by rw [lookupFun, hp₂], hd.1.symm, hd.2.1.symm,
          hd.2.2, List.Forall₂.cons hs hR'⟩

/-! ### The congruence -/

/-- **Function-environment congruence.** A `Step` derivation transports across a
`FunsRel`: running the *same* code under a related function environment yields the
*same* result. -/
theorem Step.funs_congr {funs₁ : FunEnv D} {V st code res}
    (h : Step D funs₁ V st code res) :
    ∀ {funs₂}, FunsRel D funs₁ funs₂ → Step D funs₂ V st code res := by
  induction h with
  | lit => intro _ _; exact Step.lit
  | var hv => intro _ _; exact Step.var hv
  | builtinOk _ hb iha => intro _ hR; exact Step.builtinOk (iha hR) hb
  | builtinHalt _ hb iha => intro _ hR; exact Step.builtinHalt (iha hR) hb
  | builtinArgsHalt _ iha => intro _ hR; exact Step.builtinArgsHalt (iha hR)
  | @callOk funs V st fn args argvals st1 decl cenv Vend st2 o ha hl hlen hbody ho iha ihbody =>
      intro funs₂ hR
      obtain ⟨decl', cenv', hl', hpar, hret, hbodyEq, hRcenv⟩ := lookupFun_funsRel hR hl
      have hstep : Step D cenv' (decl.params.zip argvals ++ bindZeros D decl.rets) st1
          (.stmt (.block decl.body)) (.sres Vend st2 o) := ihbody hRcenv
      have hstep' : Step D cenv' (decl.params.zip argvals ++ bindZeros D decl.rets) st1
          (.stmt (.block decl'.body)) (.sres Vend st2 o) :=
        (hbodyEq cenv' _ st1 Vend st2 o).mp hstep
      have hbody' : Step D cenv' (decl'.params.zip argvals ++ bindZeros D decl'.rets) st1
          (.stmt (.block decl'.body)) (.sres Vend st2 o) := by rw [hpar, hret]; exact hstep'
      have hres := Step.callOk (iha hR) hl' (by rw [hpar]; exact hlen) hbody' ho
      rw [hret] at hres; exact hres
  | @callHalt funs V st fn args argvals st1 decl cenv Vend st2 ha hl hlen hbody iha ihbody =>
      intro funs₂ hR
      obtain ⟨decl', cenv', hl', hpar, hret, hbodyEq, hRcenv⟩ := lookupFun_funsRel hR hl
      have hstep : Step D cenv' (decl.params.zip argvals ++ bindZeros D decl.rets) st1
          (.stmt (.block decl.body)) (.sres Vend st2 .halt) := ihbody hRcenv
      have hstep' : Step D cenv' (decl.params.zip argvals ++ bindZeros D decl.rets) st1
          (.stmt (.block decl'.body)) (.sres Vend st2 .halt) :=
        (hbodyEq cenv' _ st1 Vend st2 .halt).mp hstep
      have hbody' : Step D cenv' (decl'.params.zip argvals ++ bindZeros D decl'.rets) st1
          (.stmt (.block decl'.body)) (.sres Vend st2 .halt) := by rw [hpar, hret]; exact hstep'
      exact Step.callHalt (iha hR) hl' (by rw [hpar]; exact hlen) hbody'
  | callArgsHalt _ iha => intro _ hR; exact Step.callArgsHalt (iha hR)
  | argsNil => intro _ _; exact Step.argsNil
  | argsCons _ _ iha ihe => intro _ hR; exact Step.argsCons (iha hR) (ihe hR)
  | argsRestHalt _ iha => intro _ hR; exact Step.argsRestHalt (iha hR)
  | argsHeadHalt _ _ iha ihe => intro _ hR; exact Step.argsHeadHalt (iha hR) (ihe hR)
  | funDef => intro _ _; exact Step.funDef
  | @block funs V st body Vb stb o hbody ihbody =>
      intro funs₂ hR; exact Step.block (ihbody (FunsRel.cons_same (hoist D body) hR))
  | letZero => intro _ _; exact Step.letZero
  | letVal _ hlen ihe => intro _ hR; exact Step.letVal (ihe hR) hlen
  | letHalt _ ihe => intro _ hR; exact Step.letHalt (ihe hR)
  | assignVal _ hlen ihe => intro _ hR; exact Step.assignVal (ihe hR) hlen
  | assignHalt _ ihe => intro _ hR; exact Step.assignHalt (ihe hR)
  | exprStmt _ ihe => intro _ hR; exact Step.exprStmt (ihe hR)
  | exprStmtHalt _ ihe => intro _ hR; exact Step.exprStmtHalt (ihe hR)
  | ifTrue _ hnz _ ihc ihb => intro _ hR; exact Step.ifTrue (ihc hR) hnz (ihb hR)
  | ifFalse _ hz ihc => intro _ hR; exact Step.ifFalse (ihc hR) hz
  | ifHalt _ ihc => intro _ hR; exact Step.ifHalt (ihc hR)
  | switchExec _ _ ihc ihb => intro _ hR; exact Step.switchExec (ihc hR) (ihb hR)
  | switchHalt _ ihc => intro _ hR; exact Step.switchHalt (ihc hR)
  | @forLoop funs V st init c post body Vinit stinit Vend stend o hinit hloop ihinit ihloop =>
      intro funs₂ hR
      exact Step.forLoop (ihinit (FunsRel.cons_same (hoist D init) hR))
        (ihloop (FunsRel.cons_same (hoist D init) hR))
  | @forInitHalt funs V st init c post body Vinit stinit hinit ihinit =>
      intro funs₂ hR
      exact Step.forInitHalt (ihinit (FunsRel.cons_same (hoist D init) hR))
  | «break» => intro _ _; exact Step.break
  | «continue» => intro _ _; exact Step.continue
  | leave => intro _ _; exact Step.leave
  | seqNil => intro _ _; exact Step.seqNil
  | seqCons _ _ ihs ihrest => intro _ hR; exact Step.seqCons (ihs hR) (ihrest hR)
  | seqStop _ hne ihs => intro _ hR; exact Step.seqStop (ihs hR) hne
  | loopDone _ hz ihc => intro _ hR; exact Step.loopDone (ihc hR) hz
  | loopCondHalt _ ihc => intro _ hR; exact Step.loopCondHalt (ihc hR)
  | loopStep _ hnz _ hob _ _ ihc ihb ihp ihr =>
      intro _ hR; exact Step.loopStep (ihc hR) hnz (ihb hR) hob (ihp hR) (ihr hR)
  | loopPostHalt _ hnz _ hob _ ihc ihb ihp =>
      intro _ hR; exact Step.loopPostHalt (ihc hR) hnz (ihb hR) hob (ihp hR)
  | loopBreak _ hnz _ ihc ihb => intro _ hR; exact Step.loopBreak (ihc hR) hnz (ihb hR)
  | loopLeave _ hnz _ ihc ihb => intro _ hR; exact Step.loopLeave (ihc hR) hnz (ihb hR)
  | loopBodyHalt _ hnz _ ihc ihb => intro _ hR; exact Step.loopBodyHalt (ihc hR) hnz (ihb hR)

/-- **Block congruence with a changing function scope.** Equivalent statement
lists whose hoisted scopes are `ScopeRel`-related form equivalent blocks — the
generalization of `EquivBlock.of_stmts` that permits rewriting inside `funDef`
bodies. -/
theorem EquivBlock.of_stmts_funs {b₁ b₂ : Block D.Op}
    (hstmts : EquivStmts D b₁ b₂) (hR : ScopeRel D (hoist D b₁) (hoist D b₂)) :
    EquivBlock D b₁ b₂ := by
  intro funs V st V' st' o
  constructor
  · intro h
    cases h with
    | block hb =>
        refine Step.block ?_
        have h1 := Step.funs_congr hb (List.Forall₂.cons hR (FunsRel.refl funs))
        exact (hstmts (hoist D b₂ :: funs) V st _ _ _).mp h1
  · intro h
    cases h with
    | block hb =>
        refine Step.block ?_
        have h1 := Step.funs_congr hb (List.Forall₂.cons hR.symm (FunsRel.refl funs))
        exact (hstmts (hoist D b₁ :: funs) V st _ _ _).mpr h1

end YulEvmCompiler.Optimizer
