import YulEvmCompiler.Optimizer.Implementation.Normalization.HoistFunDefs
import YulEvmCompiler.Optimizer.Spec.Pass

/-!
# Semantic equivalence of function hoisting  (WORK IN PROGRESS — contains `sorry`)

Goal: `UniqueFunNames b → WellScoped b → EquivBlock D b (liftFunDefs b)`.

Yul functions capture no variables (a callee runs with a fresh `VEnv`), only the
*function environment* (`cenv`, the scopes visible at the definition site). So
hoisting is sound exactly when name resolution is preserved:

* **unique names** ⇒ the flattening is unambiguous and needs no renaming (a name
  resolves to the one function with that name, wherever it sits);
* **well-scoped** ⇒ every call the *lifted* program can make (all functions are
  now globally visible) was already resolvable in the original, so the original
  is not stuck where the lifted program runs — the direction that would
  otherwise fail (`{ { function g(){} }  g() }` is stuck originally but runs
  after hoisting).

## Proof architecture (being built)

The lifted top block hoists `flat := hoist (collectStmts b)` — the whole
program's functions, each with a `stripStmts`-ed body — while every stripped
nested block hoists `[]`. The heart is a bidirectional `Step` simulation
(`step_lift_sim`) transporting a derivation across a relation `FEnvLift flat`
that couples the original scope *stack* to the *flat* scope, while the code is
simultaneously `stripStmts`-ed. This differs from `FunCongr`/`EmptyScope`
(same code, related envs): here code and environment transform together, and the
`callOk` case re-establishes `FEnvLift` between the callee's original `cenv` and
`flat`.
-/

namespace YulEvmCompiler.Optimizer.Normalization

open YulSemantics

variable {D : Dialect} [DecidableEq D.Value]

/-! ### Well-scopedness -/

/-- Top-level function names of a block (what `hoist` brings into scope). -/
def funNamesTop (b : List (Stmt D.Op)) : List Ident :=
  b.filterMap (fun s => match s with | .funDef n _ _ _ => some n | _ => none)

mutual
/-- Every user-call name in an expression is in `scope`. -/
def ScopedExpr (scope : List Ident) : Expr D.Op → Prop
  | .lit _ => True
  | .var _ => True
  | .builtin _ args => ScopedArgs scope args
  | .call f args => f ∈ scope ∧ ScopedArgs scope args
def ScopedArgs (scope : List Ident) : List (Expr D.Op) → Prop
  | [] => True
  | e :: rest => ScopedExpr scope e ∧ ScopedArgs scope rest
end

mutual
/-- Every call in a statement resolves in the accumulated function scope. A block
extends the scope with its own top-level function names (mirroring `hoist`). -/
def ScopedStmt (scope : List Ident) : Stmt D.Op → Prop
  | .funDef _ _ _ body => ScopedStmts (funNamesTop body ++ scope) body
  | .block b => ScopedStmts (funNamesTop b ++ scope) b
  | .cond c b => ScopedExpr scope c ∧ ScopedStmts (funNamesTop b ++ scope) b
  | .switch c cases dflt =>
      ScopedExpr scope c ∧ ScopedCases scope cases ∧ ScopedDflt scope dflt
  | .forLoop init c post body =>
      -- init's functions are visible in cond/post/body (they share the loop scope)
      ScopedStmts (funNamesTop init ++ scope) init ∧
      ScopedExpr (funNamesTop init ++ scope) c ∧
      ScopedStmts (funNamesTop init ++ scope) post ∧
      ScopedStmts (funNamesTop init ++ scope) body
  | .letDecl _ val => match val with | none => True | some e => ScopedExpr scope e
  | .assign _ e => ScopedExpr scope e
  | .exprStmt e => ScopedExpr scope e
  | .break => True
  | .continue => True
  | .leave => True
def ScopedStmts (scope : List Ident) : List (Stmt D.Op) → Prop
  | [] => True
  | s :: rest => ScopedStmt scope s ∧ ScopedStmts scope rest
def ScopedCases (scope : List Ident) : List (Literal × Block D.Op) → Prop
  | [] => True
  | (_, b) :: rest => ScopedStmts (funNamesTop b ++ scope) b ∧ ScopedCases scope rest
def ScopedDflt (scope : List Ident) : Option (Block D.Op) → Prop
  | none => True
  | some b => ScopedStmts (funNamesTop b ++ scope) b
end

/-- The program is well scoped: every call resolves under the scope that starts
with the top block's own functions. -/
def WellScoped (b : Block D.Op) : Prop := ScopedStmts (funNamesTop b) b

/-! ### The equivalence (statement pinned; proof under construction) -/

/-- **Hoisting all function definitions to the top preserves semantics**, for
programs with globally unique function names that are well scoped. -/
theorem liftFunDefs_equiv {b : Block D.Op}
    (huniq : UniqueFunNames b) (hscoped : WellScoped b) :
    EquivBlock D b (liftFunDefs b) := by
  sorry

end YulEvmCompiler.Optimizer.Normalization
