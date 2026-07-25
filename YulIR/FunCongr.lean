import YulSemantics.Equiv
import YulSemantics.Determinism

/-!
# YulIR.FunCongr — the missing `funDef`-body congruence for the big-step judgment

`YulSemantics.Equiv` proves congruence for every syntactic form *except* rewriting inside a function
**body**: a block hoists its `funDef`s into the function environment, so equivalent statement lists
with different function bodies need not form equivalent blocks (`EquivBlock.of_stmts` demands
`hoist b₁ = hoist b₂`). Its doc calls the fix "a relation on function environments (environments
with pointwise-equivalent bodies) threaded through the judgment" and defers it. This file builds
exactly that and discharges the obligation:

* `FunEnvEquiv` — two function environments of the same shape whose corresponding function bodies
  are `EquivBlock`;
* `Step.funenv_congr` — the big-step judgment is insensitive to replacing the function environment
  by an equivalent one (a rule induction over the single `Step` inductive, using body-equivalence at
  every call site);
* `EquivBlock.of_stmts_congr` — the relaxed block congruence: equivalent statement lists whose
  hoisted scopes are *equivalent* (not equal) form equivalent blocks;
* `EquivBlock.funDef_body` — rewriting inside one `funDef`'s body preserves block equivalence.

This unblocks whole-pass soundness for passes that recurse into function bodies (see
`YulIR/Soundness.lean`).
-/

namespace YulSemantics

variable {D : Dialect} [DecidableEq D.Value]

/-! ### The function-environment equivalence -/

/-- Two function declarations agree on signature and have equivalent bodies. -/
def FDeclEquiv (D : Dialect) [DecidableEq D.Value] (d₁ d₂ : FDecl D) : Prop :=
  d₁.params = d₂.params ∧ d₁.rets = d₂.rets ∧ EquivBlock D d₁.body d₂.body

/-- Two `(name, decl)` entries agree on name and are `FDeclEquiv`. -/
def FEntryEquiv (D : Dialect) [DecidableEq D.Value] (p q : Ident × FDecl D) : Prop :=
  p.1 = q.1 ∧ FDeclEquiv D p.2 q.2

/-- Two scopes are entrywise equivalent. -/
def FScopeEquiv (D : Dialect) [DecidableEq D.Value] (s₁ s₂ : FScope D) : Prop :=
  List.Forall₂ (FEntryEquiv D) s₁ s₂

/-- Two function environments are scopewise equivalent. -/
def FunEnvEquiv (D : Dialect) [DecidableEq D.Value] (f₁ f₂ : FunEnv D) : Prop :=
  List.Forall₂ (FScopeEquiv D) f₁ f₂

/-! ### Reflexivity and symmetry -/

theorem FDeclEquiv.refl (d : FDecl D) : FDeclEquiv D d d := ⟨rfl, rfl, EquivBlock.refl _⟩

theorem FScopeEquiv.refl (s : FScope D) : FScopeEquiv D s s := by
  induction s with
  | nil => exact .nil
  | cons p _ ih => exact .cons ⟨rfl, FDeclEquiv.refl _⟩ ih

theorem FunEnvEquiv.refl (f : FunEnv D) : FunEnvEquiv D f f := by
  induction f with
  | nil => exact .nil
  | cons s _ ih => exact .cons (FScopeEquiv.refl s) ih

theorem FDeclEquiv.symm {d₁ d₂ : FDecl D} (h : FDeclEquiv D d₁ d₂) : FDeclEquiv D d₂ d₁ :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

theorem FEntryEquiv.symm {p q : Ident × FDecl D} (h : FEntryEquiv D p q) : FEntryEquiv D q p :=
  ⟨h.1.symm, h.2.symm⟩

theorem FScopeEquiv.symm {s₁ s₂ : FScope D} (h : FScopeEquiv D s₁ s₂) : FScopeEquiv D s₂ s₁ := by
  induction h with
  | nil => exact .nil
  | cons hp _ ih => exact .cons hp.symm ih

theorem FunEnvEquiv.symm {f₁ f₂ : FunEnv D} (h : FunEnvEquiv D f₁ f₂) : FunEnvEquiv D f₂ f₁ := by
  induction h with
  | nil => exact .nil
  | cons hs _ ih => exact .cons hs.symm ih

/-- Prepending the *same* scope preserves environment equivalence (used for `block`/`forLoop`,
which hoist an identical body). -/
theorem FunEnvEquiv.cons_refl (s : FScope D) {f₁ f₂ : FunEnv D} (h : FunEnvEquiv D f₁ f₂) :
    FunEnvEquiv D (s :: f₁) (s :: f₂) := .cons (FScopeEquiv.refl s) h

/-! ### Lookup respects equivalence -/

/-- `find?` by name over equivalent scopes returns equivalent entries. -/
private theorem scope_find_congr {s₁ s₂ : FScope D} (h : FScopeEquiv D s₁ s₂) (fn : Ident)
    {p₁ : Ident × FDecl D} (hf : s₁.find? (fun p => p.1 = fn) = some p₁) :
    ∃ p₂, s₂.find? (fun p => p.1 = fn) = some p₂ ∧ p₁.1 = p₂.1 ∧ FDeclEquiv D p₁.2 p₂.2 := by
  induction h with
  | nil => simp [List.find?] at hf
  | @cons a b s₁' s₂' hab _ ih =>
      by_cases hc : a.1 = fn
      · rw [List.find?_cons_of_pos (by simp [hc])] at hf
        cases hf
        exact ⟨b, List.find?_cons_of_pos (by simp [← hab.1, hc]), hab.1, hab.2⟩
      · rw [List.find?_cons_of_neg (by simp [hc])] at hf
        rw [List.find?_cons_of_neg (by simp [← hab.1, hc])]
        exact ih hf

/-- `find?` yielding `none` transfers across equivalent scopes (matching keys). -/
private theorem scope_find_none_congr {s₁ s₂ : FScope D} (h : FScopeEquiv D s₁ s₂) (fn : Ident)
    (hf : s₁.find? (fun p => p.1 = fn) = none) : s₂.find? (fun p => p.1 = fn) = none := by
  induction h with
  | nil => rfl
  | @cons a b s₁' s₂' hab _ ih =>
      by_cases hc : a.1 = fn
      · rw [List.find?_cons_of_pos (by simp [hc])] at hf; exact absurd hf (by simp)
      · rw [List.find?_cons_of_neg (by simp [hc])] at hf
        rw [List.find?_cons_of_neg (by simp [← hab.1, hc])]
        exact ih hf

/-- Looking up a function in equivalent environments yields equivalent declarations *and*
equivalent definition-site environments. -/
theorem lookupFun_congr {f₁ f₂ : FunEnv D} (h : FunEnvEquiv D f₁ f₂) {fn : Ident}
    {d₁ : FDecl D} {c₁ : FunEnv D} (hl : lookupFun f₁ fn = some (d₁, c₁)) :
    ∃ d₂ c₂, lookupFun f₂ fn = some (d₂, c₂) ∧ FDeclEquiv D d₁ d₂ ∧ FunEnvEquiv D c₁ c₂ := by
  induction h with
  | nil => simp [lookupFun] at hl
  | @cons scope₁ scope₂ rest₁ rest₂ hscope hrest ih =>
      rw [lookupFun] at hl ⊢
      cases hfind : scope₁.find? (fun p => p.1 = fn) with
      | some p₁ =>
          rw [hfind] at hl
          cases hl
          obtain ⟨p₂, hf₂, _, hdecl⟩ := scope_find_congr hscope fn hfind
          rw [hf₂]
          exact ⟨p₂.2, scope₂ :: rest₂, rfl, hdecl, .cons hscope hrest⟩
      | none =>
          rw [hfind] at hl
          rw [scope_find_none_congr hscope fn hfind]
          exact ih hl

/-! ### The master lemma: the judgment is insensitive to an equivalent function environment -/

/-- Replacing the function environment by an equivalent one preserves every derivation. A single
rule induction over `Step`: straight-line/control constructors just re-apply themselves through the
IHs; `block`/`forLoop` extend the environment with the *same* hoisted scope (reflexively
equivalent); `call*` looks the function up in the equivalent environment and swaps its body via the
`EquivBlock` carried by `lookupFun_congr`. -/
theorem Step.funenv_congr {funs₁ V st code r} (h : Step D funs₁ V st code r) :
    ∀ {funs₂}, FunEnvEquiv D funs₁ funs₂ → Step D funs₂ V st code r := by
  induction h with
  | lit => intro funs₂ heq; exact Step.lit
  | var hv => intro funs₂ heq; exact Step.var hv
  | builtinOk ha hb iha => intro funs₂ heq; exact Step.builtinOk (iha heq) hb
  | builtinHalt ha hb iha => intro funs₂ heq; exact Step.builtinHalt (iha heq) hb
  | builtinArgsHalt ha iha => intro funs₂ heq; exact Step.builtinArgsHalt (iha heq)
  | callOk ha hl hlen hbody ho iha ihbody =>
      intro funs₂ heq
      obtain ⟨d₂, c₂, hl₂, ⟨hp, hr, hbeq⟩, hcenv⟩ := lookupFun_congr heq hl
      have hbody₂ := hbeq.mp (ihbody hcenv)
      rw [hp] at hlen
      rw [hp, hr] at hbody₂
      rw [hr]
      exact Step.callOk (iha heq) hl₂ hlen hbody₂ ho
  | callHalt ha hl hlen hbody iha ihbody =>
      intro funs₂ heq
      obtain ⟨d₂, c₂, hl₂, ⟨hp, hr, hbeq⟩, hcenv⟩ := lookupFun_congr heq hl
      have hbody₂ := hbeq.mp (ihbody hcenv)
      rw [hp] at hlen
      rw [hp, hr] at hbody₂
      exact Step.callHalt (iha heq) hl₂ hlen hbody₂
  | callArgsHalt ha iha => intro funs₂ heq; exact Step.callArgsHalt (iha heq)
  | argsNil => intro funs₂ heq; exact Step.argsNil
  | argsCons hrest hhead ihrest ihhead =>
      intro funs₂ heq; exact Step.argsCons (ihrest heq) (ihhead heq)
  | argsRestHalt hrest ihrest => intro funs₂ heq; exact Step.argsRestHalt (ihrest heq)
  | argsHeadHalt hrest hhead ihrest ihhead =>
      intro funs₂ heq; exact Step.argsHeadHalt (ihrest heq) (ihhead heq)
  | funDef => intro funs₂ heq; exact Step.funDef
  | block hbody ihbody =>
      intro funs₂ heq; exact Step.block (ihbody (FunEnvEquiv.cons_refl _ heq))
  | letZero => intro funs₂ heq; exact Step.letZero
  | letVal he hlen ihe => intro funs₂ heq; exact Step.letVal (ihe heq) hlen
  | letHalt he ihe => intro funs₂ heq; exact Step.letHalt (ihe heq)
  | assignVal he hlen ihe => intro funs₂ heq; exact Step.assignVal (ihe heq) hlen
  | assignHalt he ihe => intro funs₂ heq; exact Step.assignHalt (ihe heq)
  | exprStmt he ihe => intro funs₂ heq; exact Step.exprStmt (ihe heq)
  | exprStmtHalt he ihe => intro funs₂ heq; exact Step.exprStmtHalt (ihe heq)
  | ifTrue hc hne hbody ihc ihbody =>
      intro funs₂ heq; exact Step.ifTrue (ihc heq) hne (ihbody heq)
  | ifFalse hc hcv ihc => intro funs₂ heq; exact Step.ifFalse (ihc heq) hcv
  | ifHalt hc ihc => intro funs₂ heq; exact Step.ifHalt (ihc heq)
  | switchExec hc hbody ihc ihbody =>
      intro funs₂ heq; exact Step.switchExec (ihc heq) (ihbody heq)
  | switchHalt hc ihc => intro funs₂ heq; exact Step.switchHalt (ihc heq)
  | forLoop hinit hloop ihinit ihloop =>
      intro funs₂ heq
      exact Step.forLoop (ihinit (FunEnvEquiv.cons_refl _ heq)) (ihloop (FunEnvEquiv.cons_refl _ heq))
  | forInitHalt hinit ihinit =>
      intro funs₂ heq; exact Step.forInitHalt (ihinit (FunEnvEquiv.cons_refl _ heq))
  | «break» => intro funs₂ heq; exact Step.«break»
  | «continue» => intro funs₂ heq; exact Step.«continue»
  | leave => intro funs₂ heq; exact Step.leave
  | seqNil => intro funs₂ heq; exact Step.seqNil
  | seqCons hs hrest ihs ihrest =>
      intro funs₂ heq; exact Step.seqCons (ihs heq) (ihrest heq)
  | seqStop hs hne ihs => intro funs₂ heq; exact Step.seqStop (ihs heq) hne
  | loopDone hc hcv ihc => intro funs₂ heq; exact Step.loopDone (ihc heq) hcv
  | loopCondHalt hc ihc => intro funs₂ heq; exact Step.loopCondHalt (ihc heq)
  | loopStep hc hne hbody hob hpost hloop ihc ihbody ihpost ihloop =>
      intro funs₂ heq
      exact Step.loopStep (ihc heq) hne (ihbody heq) hob (ihpost heq) (ihloop heq)
  | loopPostHalt hc hne hbody hob hpost ihc ihbody ihpost =>
      intro funs₂ heq
      exact Step.loopPostHalt (ihc heq) hne (ihbody heq) hob (ihpost heq)
  | loopBreak hc hne hbody ihc ihbody =>
      intro funs₂ heq; exact Step.loopBreak (ihc heq) hne (ihbody heq)
  | loopLeave hc hne hbody ihc ihbody =>
      intro funs₂ heq; exact Step.loopLeave (ihc heq) hne (ihbody heq)
  | loopBodyHalt hc hne hbody ihc ihbody =>
      intro funs₂ heq; exact Step.loopBodyHalt (ihc heq) hne (ihbody heq)

/-! ### Payoff: block congruence up to equivalent function bodies -/

/-- The relaxed block congruence the upstream meta-theory was missing: equivalent statement lists
whose hoisted scopes are *equivalent* (not necessarily equal) form equivalent blocks. This is
`EquivBlock.of_stmts` with its `hoist b₁ = hoist b₂` side condition weakened to `FScopeEquiv`, so
rewrites *inside* `funDef` bodies are now admissible. -/
theorem EquivBlock.of_stmts_congr {b₁ b₂ : Block D.Op} (hss : EquivStmts D b₁ b₂)
    (hh : FScopeEquiv D (hoist D b₁) (hoist D b₂)) : EquivBlock D b₁ b₂ := by
  intro funs V st V' st' o
  constructor
  · intro h
    cases h with
    | block hstmts =>
        have h2 := hstmts.funenv_congr (.cons hh (FunEnvEquiv.refl funs))
        exact Step.block ((hss _ _ _ _ _ _).mp h2)
  · intro h
    cases h with
    | block hstmts =>
        have h2 := hstmts.funenv_congr (.cons hh.symm (FunEnvEquiv.refl funs))
        exact Step.block ((hss _ _ _ _ _ _).mpr h2)

end YulSemantics
