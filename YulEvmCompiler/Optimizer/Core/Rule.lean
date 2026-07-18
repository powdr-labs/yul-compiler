import YulEvmCompiler.Optimizer.Core.Basic
import YulSemantics.Equiv

set_option warningAsError true

/-!
# Proof-carrying Core simplification rules

A `Rule` packages a Core rewrite with its exact `EquivExpr` proof.  The generic
first-match engine is proved once and knows nothing about individual arithmetic
identities.  Optimizer policy is the ordered rule list; extending that policy
requires constructing a new proved `Rule`, not changing the engine proof.
-/

namespace YulEvmCompiler.Optimizer.Core

open YulSemantics
open YulSemantics.EVM

/-- A shallow Core rewrite carrying its semantics-preservation proof for every
open-world call/create model. -/
structure Rule where
  rewrite : {Γ : Ctx} → Term Γ 1 → Option (Term Γ 1)
  sound : ∀ {calls : ExternalCalls} {creates : ExternalCreates} {Γ : Ctx}
      {input output : Term Γ 1}, rewrite input = some output →
      EquivExpr (evmWithExternal calls creates) input.emit output.emit

/-! ## Scoped rules

Some algebraic rules deliberately discard an ANF value.  They are valid once
the Core context is known to be realized by the runtime variable environment,
but not as raw `EquivExpr`s over arbitrary, possibly unbound Yul syntax. -/

/-- Every name certified by a Core context occurs in the runtime environment. -/
def VarsBound {D : Dialect} (Γ : Ctx) (V : VEnv D) : Prop :=
  ∀ x, x ∈ Γ → x ∈ V.map Prod.fst

/-- A certified Core variable has a runtime value in a realized context. -/
theorem VarsBound.get {D : Dialect} {Γ : Ctx} {V : VEnv D}
    (hbound : VarsBound Γ V) (ref : Var Γ) : ∃ value, VEnv.get V ref.name = some value := by
  have hmem := hbound ref.name ref.bound
  have get_of_mem : ∀ (env : VEnv D) (name : Ident),
      name ∈ env.map Prod.fst → ∃ value, VEnv.get env name = some value := by
    intro env name h
    induction env with
    | nil => simp at h
    | cons binding rest ih =>
        rcases binding with ⟨head, value⟩
        simp only [List.map_cons, List.mem_cons] at h
        by_cases hname : head = name
        · subst head
          exact ⟨value, by simp [VEnv.get]⟩
        · obtain htail := h.resolve_left (fun heq => hname heq.symm)
          obtain ⟨result, hget⟩ := ih htail
          exact ⟨result, by simpa [VEnv.get, hname] using hget⟩
  exact get_of_mem V ref.name hmem

/-- Expression equivalence under realization of the Core variable context. -/
def ScopedEquivExpr (Γ : Ctx) (e₁ e₂ : Expr Op) : Prop :=
  ∀ {calls : ExternalCalls} {creates : ExternalCreates} funs V st result,
    VarsBound Γ V →
    (Step (evmWithExternal calls creates) funs V st (.expr e₁) (.eres result) ↔
      Step (evmWithExternal calls creates) funs V st (.expr e₂) (.eres result))

/-- A Core rewrite that may rely on every typed variable being runtime-bound. -/
structure ScopedRule where
  rewrite : {Γ : Ctx} → Term Γ 1 → Option (Term Γ 1)
  sound : ∀ {Γ : Ctx} {input output : Term Γ 1}, rewrite input = some output →
    ScopedEquivExpr Γ input.emit output.emit

/-- Apply the first matching rule. -/
def first (rules : List Rule) (input : Term Γ 1) : Option (Term Γ 1) :=
  match rules with
  | [] => none
  | rule :: rest =>
      match rule.rewrite input with
      | some output => some output
      | none => first rest input

/-- The first-match engine preserves semantics for any list of proof-carrying
rules. -/
theorem first_sound {rules : List Rule} {input output : Term Γ 1}
    (h : first rules input = some output) :
    EquivExpr (evmWithExternal calls creates) input.emit output.emit := by
  induction rules with
  | nil => simp [first] at h
  | cons rule rest ih =>
      cases hrule : rule.rewrite input with
      | none =>
          simp [first, hrule] at h
          exact ih h
      | some rewritten =>
          simp [first, hrule] at h
          subst output
          exact rule.sound hrule

/-- Run an ordered rule set, leaving the input unchanged if no rule matches. -/
def run (rules : List Rule) (input : Term Γ 1) : Term Γ 1 :=
  (first rules input).getD input

/-- Running a proof-carrying rule set is semantics-preserving. -/
theorem run_sound (rules : List Rule) (input : Term Γ 1) :
    EquivExpr (evmWithExternal calls creates) input.emit (run rules input).emit := by
  cases h : first rules input with
  | none => simp [run, h, EquivExpr.refl]
  | some output =>
      simpa [run, h] using
        (first_sound (calls := calls) (creates := creates) h)

/-- Apply the first matching scoped rule. -/
def scopedFirst (rules : List ScopedRule) (input : Term Γ 1) : Option (Term Γ 1) :=
  match rules with
  | [] => none
  | rule :: rest =>
      match rule.rewrite input with
      | some output => some output
      | none => scopedFirst rest input

/-- The first matching scoped rule is sound under context realization. -/
theorem scopedFirst_sound {rules : List ScopedRule} {input output : Term Γ 1}
    (h : scopedFirst rules input = some output) :
    ScopedEquivExpr Γ input.emit output.emit := by
  induction rules with
  | nil => simp [scopedFirst] at h
  | cons rule rest ih =>
      cases hrule : rule.rewrite input with
      | none =>
          simp [scopedFirst, hrule] at h
          exact ih h
      | some rewritten =>
          simp [scopedFirst, hrule] at h
          subst output
          exact rule.sound hrule

/-- Run scoped rules, preserving the input if none matches. -/
def scopedRun (rules : List ScopedRule) (input : Term Γ 1) : Term Γ 1 :=
  (scopedFirst rules input).getD input

/-- Running scoped rules is sound whenever the Core context is realized. -/
theorem scopedRun_sound (rules : List ScopedRule) (input : Term Γ 1) :
    ScopedEquivExpr Γ input.emit (scopedRun rules input).emit := by
  intro calls creates funs V st result hbound
  cases h : scopedFirst rules input with
  | none => simp [scopedRun, h]
  | some output =>
      simpa [scopedRun, h] using
        (scopedFirst_sound h (calls := calls) (creates := creates)
          funs V st result hbound)

end YulEvmCompiler.Optimizer.Core
