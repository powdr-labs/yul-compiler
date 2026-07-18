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

end YulEvmCompiler.Optimizer.Core
