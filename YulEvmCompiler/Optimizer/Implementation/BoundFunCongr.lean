import YulEvmCompiler.Optimizer.Implementation.DeadPure
import YulEvmCompiler.Optimizer.Implementation.FunCongr
set_option warningAsError true

namespace YulEvmCompiler.Optimizer.BoundFun

open YulSemantics

variable {D : Dialect} [DecidableEq D.Value]

/-! ### The relation on function environments -/

/-- Function bodies start from exactly their parameter/return layout.  Keeping
the order here (rather than mere set membership) lets layout rewrites use
fresh-name and slot-depth facts while remaining closed under function calls. -/
def BoundOK (V : VEnv D) (bound : List Ident) : Prop :=
  V.map Prod.fst = bound

/-- Two function declarations agree on signature and have equivalent bodies. -/
def BoundEquivBlock (D : Dialect) [DecidableEq D.Value] (bound : List Ident)
    (b₁ b₂ : Block D.Op) : Prop :=
  ∀ funs V st, BoundOK V bound →
    (∀ V' st' o, o ≠ .halt →
      (Step D funs V st (.stmt (.block b₁)) (.sres V' st' o) ↔
        Step D funs V st (.stmt (.block b₂)) (.sres V' st' o))) ∧
    (∀ st',
      ((∃ V', Step D funs V st (.stmt (.block b₁)) (.sres V' st' .halt)) ↔
        ∃ V', Step D funs V st (.stmt (.block b₂)) (.sres V' st' .halt)))

def BoundFDeclRel (D : Dialect) [DecidableEq D.Value] (d₁ d₂ : FDecl D) : Prop :=
  d₁.params = d₂.params ∧ d₁.rets = d₂.rets ∧
    BoundEquivBlock D (d₁.params ++ d₁.rets) d₁.body d₂.body

theorem BoundEquivBlock.refl (bound : List Ident) (b : Block D.Op) :
    BoundEquivBlock D bound b b :=
  fun _ _ _ _ => ⟨fun _ _ _ _ => Iff.rfl, fun _ => Iff.rfl⟩

theorem BoundEquivBlock.trans {bound : List Ident} {b₁ b₂ b₃ : Block D.Op}
    (h₁₂ : BoundEquivBlock D bound b₁ b₂)
    (h₂₃ : BoundEquivBlock D bound b₂ b₃) :
    BoundEquivBlock D bound b₁ b₃ := by
  intro funs V st hb
  obtain ⟨hn₁₂, hh₁₂⟩ := h₁₂ funs V st hb
  obtain ⟨hn₂₃, hh₂₃⟩ := h₂₃ funs V st hb
  exact ⟨fun V' st' o ho => (hn₁₂ V' st' o ho).trans (hn₂₃ V' st' o ho),
    fun st' => (hh₁₂ st').trans (hh₂₃ st')⟩

theorem BoundEquivBlock.of_equiv {bound : List Ident} {b₁ b₂ : Block D.Op}
    (h : EquivBlock D b₁ b₂) : BoundEquivBlock D bound b₁ b₂ := by
  intro funs V st _
  exact ⟨fun V' st' o _ => h funs V st V' st' o,
    fun st' => ⟨
      fun ⟨V', hs⟩ => ⟨V', (h funs V st V' st' .halt).mp hs⟩,
      fun ⟨V', hs⟩ => ⟨V', (h funs V st V' st' .halt).mpr hs⟩⟩⟩

/-- Two scopes are related when, pairwise, they bind the same names to
signature-equal, body-equivalent declarations. -/
def BoundScopeRel (D : Dialect) [DecidableEq D.Value] (s₁ s₂ : FScope D) : Prop :=
  List.Forall₂ (fun p q => p.1 = q.1 ∧ BoundFDeclRel D p.2 q.2) s₁ s₂

/-- Two function environments are related scope-by-scope. -/
def BoundFunsRel (D : Dialect) [DecidableEq D.Value] (f₁ f₂ : FunEnv D) : Prop :=
  List.Forall₂ (BoundScopeRel D) f₁ f₂

theorem BoundFDeclRel.refl (d : FDecl D) : BoundFDeclRel D d d :=
  ⟨rfl, rfl, BoundEquivBlock.refl _ _⟩

theorem BoundFDeclRel.symm {d₁ d₂ : FDecl D} (h : BoundFDeclRel D d₁ d₂) : BoundFDeclRel D d₂ d₁ :=
  ⟨h.1.symm, h.2.1.symm, by
    intro funs V st hb
    have hb' : BoundOK V (d₁.params ++ d₁.rets) := by
      rw [h.1, h.2.1]
      exact hb
    obtain ⟨hn, hh⟩ := h.2.2 funs V st hb'
    exact ⟨fun V' st' o ho => (hn V' st' o ho).symm,
      fun st' => (hh st').symm⟩⟩

theorem BoundScopeRel.refl (s : FScope D) : BoundScopeRel D s s := by
  induction s with
  | nil => exact .nil
  | cons p t ih => exact .cons ⟨rfl, BoundFDeclRel.refl _⟩ ih

theorem BoundScopeRel.symm {s₁ s₂ : FScope D} (h : BoundScopeRel D s₁ s₂) : BoundScopeRel D s₂ s₁ := by
  induction h with
  | nil => exact .nil
  | cons hpq _ ih => exact .cons ⟨hpq.1.symm, hpq.2.symm⟩ ih

theorem BoundFunsRel.refl (f : FunEnv D) : BoundFunsRel D f f := by
  induction f with
  | nil => exact .nil
  | cons s t ih => exact .cons (BoundScopeRel.refl _) ih

theorem BoundFunsRel.symm {f₁ f₂ : FunEnv D} (h : BoundFunsRel D f₁ f₂) : BoundFunsRel D f₂ f₁ := by
  induction h with
  | nil => exact .nil
  | cons hs _ ih => exact .cons hs.symm ih

/-- Extend related environments by a common outer scope. -/
theorem BoundFunsRel.cons_same (s : FScope D) {f₁ f₂ : FunEnv D} (h : BoundFunsRel D f₁ f₂) :
    BoundFunsRel D (s :: f₁) (s :: f₂) := .cons (BoundScopeRel.refl s) h

/-! ### `lookupFun` transports across `BoundFunsRel` -/

/-- A scope lookup transports across `BoundScopeRel`: the same name resolves in both
scopes (or in neither) to signature-equal, body-equivalent declarations. -/
theorem scopeRel_find {s₁ s₂ : FScope D} (h : BoundScopeRel D s₁ s₂) (fn : Ident) :
    (s₁.find? (fun p => p.1 = fn) = none ∧ s₂.find? (fun p => p.1 = fn) = none) ∨
    (∃ p q, s₁.find? (fun p => p.1 = fn) = some p ∧ s₂.find? (fun p => p.1 = fn) = some q ∧
      p.1 = q.1 ∧ BoundFDeclRel D p.2 q.2) := by
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

/-- `lookupFun` transports across `BoundFunsRel`: a resolved function has a related
counterpart with an equal signature, an equivalent body, and a related closure
environment. -/
theorem lookupFun_funsRel {f₁ f₂ : FunEnv D} (hR : BoundFunsRel D f₁ f₂) :
    ∀ {fn : Ident} {decl : FDecl D} {cenv : FunEnv D},
      lookupFun f₁ fn = some (decl, cenv) →
      ∃ decl' cenv', lookupFun f₂ fn = some (decl', cenv') ∧
        decl'.params = decl.params ∧ decl'.rets = decl.rets ∧
        BoundEquivBlock D (decl.params ++ decl.rets) decl.body decl'.body ∧ BoundFunsRel D cenv cenv' := by
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
`BoundFunsRel`: running the *same* code under a related function environment yields the
*same* result. -/
theorem Step.bound_funs_congr {funs₁ : FunEnv D} {V st code res}
    (h : Step D funs₁ V st code res) :
    ∀ {funs₂}, BoundFunsRel D funs₁ funs₂ → Step D funs₂ V st code res := by
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
      have hbOK : BoundOK (decl.params.zip argvals ++ bindZeros D decl.rets)
          (decl.params ++ decl.rets) := by
        unfold BoundOK
        rw [List.map_append, List.map_fst_zip (by omega)]
        simp [bindZeros, Function.comp_def]
      have hstep' : Step D cenv' (decl.params.zip argvals ++ bindZeros D decl.rets) st1
          (.stmt (.block decl'.body)) (.sres Vend st2 o) :=
        ((hbodyEq cenv' _ st1 hbOK).1 Vend st2 o (by cases ho <;> simp_all)).mp hstep
      have hbody' : Step D cenv' (decl'.params.zip argvals ++ bindZeros D decl'.rets) st1
          (.stmt (.block decl'.body)) (.sres Vend st2 o) := by rw [hpar, hret]; exact hstep'
      have hres := Step.callOk (iha hR) hl' (by rw [hpar]; exact hlen) hbody' ho
      rw [hret] at hres; exact hres
  | @callHalt funs V st fn args argvals st1 decl cenv Vend st2 ha hl hlen hbody iha ihbody =>
      intro funs₂ hR
      obtain ⟨decl', cenv', hl', hpar, hret, hbodyEq, hRcenv⟩ := lookupFun_funsRel hR hl
      have hstep : Step D cenv' (decl.params.zip argvals ++ bindZeros D decl.rets) st1
          (.stmt (.block decl.body)) (.sres Vend st2 .halt) := ihbody hRcenv
      have hbOK : BoundOK (decl.params.zip argvals ++ bindZeros D decl.rets)
          (decl.params ++ decl.rets) := by
        unfold BoundOK
        rw [List.map_append, List.map_fst_zip (by omega)]
        simp [bindZeros, Function.comp_def]
      obtain ⟨Vend', hstep'⟩ := ((hbodyEq cenv' _ st1 hbOK).2 st2).mp ⟨Vend, hstep⟩
      have hbody' : Step D cenv' (decl'.params.zip argvals ++ bindZeros D decl'.rets) st1
          (.stmt (.block decl'.body)) (.sres Vend' st2 .halt) := by
        rw [hpar, hret]; exact hstep'
      exact Step.callHalt (iha hR) hl' (by rw [hpar]; exact hlen) hbody'
  | callArgsHalt _ iha => intro _ hR; exact Step.callArgsHalt (iha hR)
  | argsNil => intro _ _; exact Step.argsNil
  | argsCons _ _ iha ihe => intro _ hR; exact Step.argsCons (iha hR) (ihe hR)
  | argsRestHalt _ iha => intro _ hR; exact Step.argsRestHalt (iha hR)
  | argsHeadHalt _ _ iha ihe => intro _ hR; exact Step.argsHeadHalt (iha hR) (ihe hR)
  | funDef => intro _ _; exact Step.funDef
  | @block funs V st body Vb stb o hbody ihbody =>
      intro funs₂ hR; exact Step.block (ihbody (BoundFunsRel.cons_same (hoist D body) hR))
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
      exact Step.forLoop (ihinit (BoundFunsRel.cons_same (hoist D init) hR))
        (ihloop (BoundFunsRel.cons_same (hoist D init) hR))
  | @forInitHalt funs V st init c post body Vinit stinit hinit ihinit =>
      intro funs₂ hR
      exact Step.forInitHalt (ihinit (BoundFunsRel.cons_same (hoist D init) hR))
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
lists whose hoisted scopes are `BoundScopeRel`-related form equivalent blocks — the
generalization of `EquivBlock.of_stmts` that permits rewriting inside `funDef`
bodies. -/
theorem EquivBlock.of_stmts_bound_funs {b₁ b₂ : Block D.Op}
    (hstmts : EquivStmts D b₁ b₂) (hR : BoundScopeRel D (hoist D b₁) (hoist D b₂)) :
    EquivBlock D b₁ b₂ := by
  intro funs V st V' st' o
  constructor
  · intro h
    cases h with
    | block hb =>
        refine Step.block ?_
        have h1 := Step.bound_funs_congr hb (List.Forall₂.cons hR (BoundFunsRel.refl funs))
        exact (hstmts (hoist D b₂ :: funs) V st _ _ _).mp h1
  · intro h
    cases h with
    | block hb =>
        refine Step.block ?_
        have h1 := Step.bound_funs_congr hb (List.Forall₂.cons hR.symm (BoundFunsRel.refl funs))
        exact (hstmts (hoist D b₁ :: funs) V st _ _ _).mpr h1



end YulEvmCompiler.Optimizer.BoundFun
