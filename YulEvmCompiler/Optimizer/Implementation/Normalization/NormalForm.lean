import YulSemantics.Ast
set_option warningAsError true
/-!
# YulEvmCompiler.Optimizer.Implementation.Normalization.NormalForm

A single, reusable **normal-form specification** for Yul programs: a bundle of
independent syntactic properties that a program can be in, phrased so that an
optimization pass can *require* some of them as a precondition and *re-establish*
the whole bundle as a postcondition.

Each property is a `Prop`-valued predicate over the raw AST (`Stmt`/`Expr`/`Block`
from `YulSemantics`, parameterized by the dialect operation type `Op`). Nothing
here is semantic — these are decidable-in-principle syntactic shapes, kept in
`Prop` deliberately so they compose cleanly in theorem statements without
carrying `Bool`-decider baggage. (Where an in-flight pass exposes a `Bool`
decider — e.g. the ANF normalizer's `isANFStmts` — the intended bridge is a
`… ↔ … = true` lemma once that pass lands; see "Relationship to the in-flight
normalization passes" below.)

## The bundle

`Normalized b` conjoins the properties that together make `b` a well-behaved
input for later optimization:

* `WellScoped`        — every referenced variable and function name resolves to a
                        declaration visible at that point (your "all referenced
                        names exist"), honoring Yul's scoping: functions hoist
                        within a block, function bodies cannot see outer
                        variables, and a `for`-init's declarations scope over the
                        loop's condition/post/body.
* `UniqueNames`       — no variable or function name is declared twice anywhere
                        in the program (full disambiguation).
* `FunctionsHoisted`  — every function definition sits at the top level of the
                        root block; no function is nested inside a block, loop,
                        conditional, switch, or another function's body.
* `IsANF`             — administrative normal form: every operand of a call,
                        assignment, `let`, `if`/`switch` scrutinee, and expression
                        statement is *flat* (an atom, or a single call whose
                        arguments are all atoms). The one exception is a `for`
                        loop's condition, which is re-evaluated each iteration and
                        so is intentionally left un-flattened.
* `ForInitEmpty`      — every `for` loop's init block is empty (its declarations
                        have been rewritten out in front of the loop).
* `Flattened`         — no bare `block` statement remains; the only blocks left
                        are the grammar-required bodies of functions, loops,
                        conditionals, and switch cases.
* `ControlWellPlaced` — `break`/`continue` occur only inside a loop body and
                        `leave` only inside a function body.

The last two of these seven (`WellScoped`, `ControlWellPlaced`) are foundational
well-formedness invariants that most passes silently assume; the parser's
`YulParser.Validate` already enforces them on accepted input, but bundling them
here lets a pass state the assumption explicitly rather than re-deriving it.

Two further syntactic simplifications are provided as **standalone** predicates
but deliberately kept *out* of the default bundle, because they are closer to
optimizations than to a stable normal form a pass must preserve:

* `NoDeadCodeAtLevel` — no statement follows a `break`/`continue`/`leave` at the
                        same statement-list level (light unreachable-code
                        cleanup; only the dialect-independent terminators are
                        recognized — `revert`/`return`/`stop` are EVM built-ins
                        and out of scope for this `Op`-generic module).

## Design: why à la carte

Keeping the seven properties as separate predicates (rather than only the
conjunction) is the point. A pass that, say, only needs disambiguation and ANF
can take `UniqueNames b → IsANF b → …` as its precondition, while still proving
`Normalized (pass b)` as its postcondition by re-establishing each field. The
`Normalized` structure's named projections (`.wellScoped`, `.anf`, …) make those
proofs read field-by-field.

## Relationship to the in-flight normalization passes

Each property corresponds to a normalization pass currently on its own branch,
none yet merged:

| property            | pass / branch                          | that branch's own predicate |
| ------------------- | -------------------------------------- | --------------------------- |
| `IsANF`             | `anf-normalizer` (`Normalization/ANF`) | `isANFStmts _ = true` (Bool) |
| `UniqueNames`       | `disambiguate`                         | `Disambiguated _` (`.Nodup`) |
| `FunctionsHoisted`  | `normalization-hoist-funcs`            | *(none — characterized via the transform only)* |
| `ForInitEmpty`      | `hoist-for-init`                       | `ForInitOKs _` (a *conditional* variant) |
| `WellScoped`        | `normalization-hoist-funcs` (`Equiv`)  | `WellScoped` (functions only) |

This module intentionally defines its own predicates rather than importing those
branches (they are unmerged and use three different namespaces —
`Optimizer.ANF`, `Optimizer.Normalize`, `Optimizer.Normalization`). It lives in a
fresh `Optimizer.NormalForm` namespace to avoid clashes. When those passes land,
the follow-up work is to (a) prove each pass establishes the corresponding field
here, and (b) unify the duplicated name/scope collectors. Note two deliberate
strengthenings over the current passes: `ForInitEmpty` demands the init be
literally empty (not just "empty when simple"), and `IsANF` recurses into
function bodies (the `anf-normalizer` pass currently leaves them un-normalized).
These are the target the passes should be raised to, not a description of today's
behavior.
-/

namespace YulEvmCompiler.Optimizer.NormalForm

open YulSemantics

variable {Op : Type}

/-! ## Name collectors

Small, non-recursive-at-the-top helpers used by the scoping and uniqueness
predicates. `funDefName?`/`funDefNames` collect the function names *hoisted* at a
single block level (like `YulSemantics.hoist`, but names only). `declTopVars`
collects the variables a single statement introduces into its *current* block
scope — only `letDecl` does; assignments and nested blocks do not. -/

/-- The function name a statement defines at this level, if any. -/
def funDefName? : Stmt Op → Option Ident
  | .funDef n _ _ _ => some n
  | _ => none

/-- Names of the functions defined at the top level of a statement list
(hoisted; visible throughout the enclosing block). -/
def funDefNames (ss : List (Stmt Op)) : List Ident := ss.filterMap funDefName?

/-- Variables a single statement introduces into the current block scope. -/
def declTopVars : Stmt Op → List Ident
  | .letDecl vars _ => vars
  | _ => []

/-- Variables introduced at the top level of a statement list (used for the
`for`-init scope leak). -/
def declTopVarsL (ss : List (Stmt Op)) : List Ident := ss.flatMap declTopVars

/-! ## 1. Well-scoped — every referenced name exists

`vs` is the list of variables visible at a program point (innermost-first order
is irrelevant here — only membership matters); `fs` is the list of function names
visible there. A statement-list is checked with `fs` **already extended** by that
block's hoisted function names, so forward references and mutual recursion within
a block are accepted. Variables thread strictly left-to-right (no hoisting).
Function bodies drop `vs` to exactly `params ++ rets` (Yul functions cannot see
outer variables) but keep `fs` (functions are lexically visible into inner
bodies). A `for`-init's top-level declarations extend the scope of the condition,
post, and body. -/

mutual
/-- Every name referenced by an expression is in scope. -/
def ScopedExpr (vs fs : List Ident) : Expr Op → Prop
  | .lit _ => True
  | .var x => x ∈ vs
  | .builtin _ args => ScopedArgs vs fs args
  | .call fn args => fn ∈ fs ∧ ScopedArgs vs fs args
def ScopedArgs (vs fs : List Ident) : List (Expr Op) → Prop
  | [] => True
  | e :: es => ScopedExpr vs fs e ∧ ScopedArgs vs fs es
end

mutual
/-- `s` references only names in scope, given visible variables `vs` and visible
functions `fs` (with this block's functions already hoisted into `fs`). -/
def ScopedStmt (vs fs : List Ident) : Stmt Op → Prop
  | .block body => ScopedStmts vs (fs ++ funDefNames body) body
  | .funDef _ params rets body =>
      ScopedStmts (params ++ rets) (fs ++ funDefNames body) body
  | .letDecl _ (some e) => ScopedExpr vs fs e
  | .letDecl _ none => True
  | .assign vars e => (∀ x ∈ vars, x ∈ vs) ∧ ScopedExpr vs fs e
  | .cond c body => ScopedExpr vs fs c ∧ ScopedStmts vs (fs ++ funDefNames body) body
  | .switch c cases dflt =>
      ScopedExpr vs fs c ∧ ScopedCases vs fs cases ∧ ScopedDflt vs fs dflt
  | .forLoop init c post body =>
      let fsInit := fs ++ funDefNames init
      let vsInit := vs ++ declTopVarsL init
      ScopedStmts vs fsInit init ∧
      ScopedExpr vsInit fsInit c ∧
      ScopedStmts vsInit (fsInit ++ funDefNames post) post ∧
      ScopedStmts vsInit (fsInit ++ funDefNames body) body
  | .exprStmt e => ScopedExpr vs fs e
  | .«break» => True
  | .«continue» => True
  | .leave => True
/-- Thread variable scope left-to-right through a statement list. `fs` must
already include this list's hoisted function names. -/
def ScopedStmts (vs fs : List Ident) : List (Stmt Op) → Prop
  | [] => True
  | s :: rest => ScopedStmt vs fs s ∧ ScopedStmts (vs ++ declTopVars s) fs rest
def ScopedCases (vs fs : List Ident) : List (Literal × List (Stmt Op)) → Prop
  | [] => True
  | (_, b) :: cs => ScopedStmts vs (fs ++ funDefNames b) b ∧ ScopedCases vs fs cs
def ScopedDflt (vs fs : List Ident) : Option (List (Stmt Op)) → Prop
  | none => True
  | some b => ScopedStmts vs (fs ++ funDefNames b) b
end

/-- Every referenced variable and function name in the program resolves to a
declaration visible at that point. -/
def WellScoped (b : Block Op) : Prop := ScopedStmts [] (funDefNames b) b

/-! ## 2. Unique names — full disambiguation -/

mutual
/-- All names (function names, params, rets, `let`-vars) declared anywhere within
a statement. -/
def declaredNamesStmt : Stmt Op → List Ident
  | .block body => declaredNamesStmts body
  | .funDef name params rets body => name :: (params ++ rets ++ declaredNamesStmts body)
  | .letDecl vars _ => vars
  | .assign _ _ => []
  | .cond _ body => declaredNamesStmts body
  | .switch _ cases dflt => declaredNamesCases cases ++ declaredNamesDflt dflt
  | .forLoop init _ post body =>
      declaredNamesStmts init ++ declaredNamesStmts post ++ declaredNamesStmts body
  | .exprStmt _ => []
  | .«break» => []
  | .«continue» => []
  | .leave => []
def declaredNamesStmts : List (Stmt Op) → List Ident
  | [] => []
  | s :: rest => declaredNamesStmt s ++ declaredNamesStmts rest
def declaredNamesCases : List (Literal × List (Stmt Op)) → List Ident
  | [] => []
  | (_, b) :: cs => declaredNamesStmts b ++ declaredNamesCases cs
def declaredNamesDflt : Option (List (Stmt Op)) → List Ident
  | none => []
  | some b => declaredNamesStmts b
end

/-- No variable or function name is declared twice anywhere in the program. -/
def UniqueNames (b : Block Op) : Prop := (declaredNamesStmts b).Nodup

/-! ## 3. Functions hoisted -/

mutual
/-- No function definition appears anywhere in a statement's subtree. -/
def NoFunDefStmt : Stmt Op → Prop
  | .funDef _ _ _ _ => False
  | .block body => NoFunDefStmts body
  | .cond _ body => NoFunDefStmts body
  | .switch _ cases dflt => NoFunDefCases cases ∧ NoFunDefDflt dflt
  | .forLoop init _ post body =>
      NoFunDefStmts init ∧ NoFunDefStmts post ∧ NoFunDefStmts body
  | _ => True
def NoFunDefStmts : List (Stmt Op) → Prop
  | [] => True
  | s :: rest => NoFunDefStmt s ∧ NoFunDefStmts rest
def NoFunDefCases : List (Literal × List (Stmt Op)) → Prop
  | [] => True
  | (_, b) :: cs => NoFunDefStmts b ∧ NoFunDefCases cs
def NoFunDefDflt : Option (List (Stmt Op)) → Prop
  | none => True
  | some b => NoFunDefStmts b
end

/-- A root-level statement is well-placed for a hoisted program: a function
definition is allowed here provided its body contains no further function
definitions; any other statement must contain no function definitions at all. -/
def HoistedTop : Stmt Op → Prop
  | .funDef _ _ _ body => NoFunDefStmts body
  | s => NoFunDefStmt s

/-- Every function definition sits at the top level of the root block. -/
def FunctionsHoisted (b : Block Op) : Prop := ∀ s ∈ b, HoistedTop s

/-! ## 4. Administrative normal form (ANF) -/

/-- An atom: a variable or literal (never a call). -/
def IsAtom : Expr Op → Prop
  | .var _ => True
  | .lit _ => True
  | .builtin _ _ => False
  | .call _ _ => False

def AtomicArgs : List (Expr Op) → Prop
  | [] => True
  | e :: es => IsAtom e ∧ AtomicArgs es

/-- A flat right-hand side: an atom, or a single call/builtin all of whose
arguments are atoms (no nested calls). -/
def IsFlatRhs : Expr Op → Prop
  | .lit _ => True
  | .var _ => True
  | .builtin _ args => AtomicArgs args
  | .call _ args => AtomicArgs args

mutual
/-- Every operand of `s` is a flat right-hand side. The `for` condition is
exempt (it is re-evaluated per iteration and cannot be hoisted). -/
def AnfStmt : Stmt Op → Prop
  | .block body => AnfStmts body
  | .funDef _ _ _ body => AnfStmts body
  | .letDecl _ (some e) => IsFlatRhs e
  | .letDecl _ none => True
  | .assign _ e => IsFlatRhs e
  | .cond c body => IsFlatRhs c ∧ AnfStmts body
  | .switch c cases dflt => IsFlatRhs c ∧ AnfCases cases ∧ AnfDflt dflt
  | .forLoop init _ post body => AnfStmts init ∧ AnfStmts post ∧ AnfStmts body
  | .exprStmt e => IsFlatRhs e
  | .«break» => True
  | .«continue» => True
  | .leave => True
def AnfStmts : List (Stmt Op) → Prop
  | [] => True
  | s :: rest => AnfStmt s ∧ AnfStmts rest
def AnfCases : List (Literal × List (Stmt Op)) → Prop
  | [] => True
  | (_, b) :: cs => AnfStmts b ∧ AnfCases cs
def AnfDflt : Option (List (Stmt Op)) → Prop
  | none => True
  | some b => AnfStmts b
end

/-- The program is in administrative normal form. -/
def IsANF (b : Block Op) : Prop := AnfStmts b

/-! ## 5. Empty `for`-init -/

mutual
/-- Every `for` loop reachable from `s` has an empty init block. -/
def ForInitEmptyStmt : Stmt Op → Prop
  | .forLoop init _ post body =>
      init = [] ∧ ForInitEmptyStmts post ∧ ForInitEmptyStmts body
  | .block body => ForInitEmptyStmts body
  | .funDef _ _ _ body => ForInitEmptyStmts body
  | .cond _ body => ForInitEmptyStmts body
  | .switch _ cases dflt => ForInitEmptyCases cases ∧ ForInitEmptyDflt dflt
  | _ => True
def ForInitEmptyStmts : List (Stmt Op) → Prop
  | [] => True
  | s :: rest => ForInitEmptyStmt s ∧ ForInitEmptyStmts rest
def ForInitEmptyCases : List (Literal × List (Stmt Op)) → Prop
  | [] => True
  | (_, b) :: cs => ForInitEmptyStmts b ∧ ForInitEmptyCases cs
def ForInitEmptyDflt : Option (List (Stmt Op)) → Prop
  | none => True
  | some b => ForInitEmptyStmts b
end

/-- Every `for` loop in the program has an empty init block. -/
def ForInitEmpty (b : Block Op) : Prop := ForInitEmptyStmts b

/-! ## 6. Flattened blocks -/

mutual
/-- No bare `block` statement appears in `s`'s subtree (grammar-required bodies
of functions, loops, conditionals, and switch cases are allowed — they are
`List (Stmt Op)` payloads, not `block` statements). -/
def FlattenedStmt : Stmt Op → Prop
  | .block _ => False
  | .funDef _ _ _ body => FlattenedStmts body
  | .cond _ body => FlattenedStmts body
  | .switch _ cases dflt => FlattenedCases cases ∧ FlattenedDflt dflt
  | .forLoop init _ post body =>
      FlattenedStmts init ∧ FlattenedStmts post ∧ FlattenedStmts body
  | _ => True
def FlattenedStmts : List (Stmt Op) → Prop
  | [] => True
  | s :: rest => FlattenedStmt s ∧ FlattenedStmts rest
def FlattenedCases : List (Literal × List (Stmt Op)) → Prop
  | [] => True
  | (_, b) :: cs => FlattenedStmts b ∧ FlattenedCases cs
def FlattenedDflt : Option (List (Stmt Op)) → Prop
  | none => True
  | some b => FlattenedStmts b
end

/-- No bare `block` statement remains anywhere in the program. -/
def Flattened (b : Block Op) : Prop := FlattenedStmts b

/-! ## 7. Control-flow well-placed -/

mutual
/-- `break`/`continue` occur only where `inLoop` holds and `leave` only where
`inFunc` holds. A function body resets `inLoop` to `false` (a loop cannot be
exited across a function boundary) and sets `inFunc`. A `for` body sets
`inLoop`; its init and post keep the enclosing context. -/
def CtrlStmt (inLoop inFunc : Bool) : Stmt Op → Prop
  | .«break» => inLoop = true
  | .«continue» => inLoop = true
  | .leave => inFunc = true
  | .block body => CtrlStmts inLoop inFunc body
  | .funDef _ _ _ body => CtrlStmts false true body
  | .cond _ body => CtrlStmts inLoop inFunc body
  | .switch _ cases dflt => CtrlCases inLoop inFunc cases ∧ CtrlDflt inLoop inFunc dflt
  | .forLoop init _ post body =>
      CtrlStmts inLoop inFunc init ∧ CtrlStmts inLoop inFunc post ∧
      CtrlStmts true inFunc body
  | _ => True
def CtrlStmts (inLoop inFunc : Bool) : List (Stmt Op) → Prop
  | [] => True
  | s :: rest => CtrlStmt inLoop inFunc s ∧ CtrlStmts inLoop inFunc rest
def CtrlCases (inLoop inFunc : Bool) : List (Literal × List (Stmt Op)) → Prop
  | [] => True
  | (_, b) :: cs => CtrlStmts inLoop inFunc b ∧ CtrlCases inLoop inFunc cs
def CtrlDflt (inLoop inFunc : Bool) : Option (List (Stmt Op)) → Prop
  | none => True
  | some b => CtrlStmts inLoop inFunc b
end

/-- `break`/`continue` appear only inside loop bodies and `leave` only inside
function bodies. -/
def ControlWellPlaced (b : Block Op) : Prop := CtrlStmts false false b

/-! ## The bundle -/

/-- A Yul block in **normal form**: the conjunction of the seven normalization
properties above. Optimization passes take (a subset of) these fields as a
precondition and re-establish the whole structure as a postcondition. -/
structure Normalized (b : Block Op) : Prop where
  wellScoped : WellScoped b
  uniqueNames : UniqueNames b
  functionsHoisted : FunctionsHoisted b
  anf : IsANF b
  forInitEmpty : ForInitEmpty b
  flattened : Flattened b
  controlWellPlaced : ControlWellPlaced b

mutual
/-- An object is normalized when its own code block and every sub-object's code
(recursively) are normalized. -/
def NormalizedObject : Object Op → Prop
  | .mk _ code subs _ => Normalized code ∧ NormalizedObjects subs
/-- Every object in a list is normalized. -/
def NormalizedObjects : List (Object Op) → Prop
  | [] => True
  | o :: os => NormalizedObject o ∧ NormalizedObjects os
end

/-! ## Standalone (not part of `Normalized`)

Light unreachable-code cleanup: no statement follows a same-level terminator.
Only the dialect-independent terminators `break`/`continue`/`leave` are
recognized here; `revert`/`return`/`stop` are EVM built-ins and would need a
dialect-specific extension. Kept out of `Normalized` because it is an
optimization result, not an invariant a general pass must preserve. -/

def isTerminator : Stmt Op → Bool
  | .«break» => true
  | .«continue» => true
  | .leave => true
  | _ => false

mutual
def NoDeadCodeStmt : Stmt Op → Prop
  | .block body => NoDeadCodeStmts body
  | .funDef _ _ _ body => NoDeadCodeStmts body
  | .cond _ body => NoDeadCodeStmts body
  | .switch _ cases dflt => NoDeadCodeCases cases ∧ NoDeadCodeDflt dflt
  | .forLoop init _ post body =>
      NoDeadCodeStmts init ∧ NoDeadCodeStmts post ∧ NoDeadCodeStmts body
  | _ => True
def NoDeadCodeStmts : List (Stmt Op) → Prop
  | [] => True
  | s :: rest =>
      NoDeadCodeStmt s ∧ (if isTerminator s then rest = [] else NoDeadCodeStmts rest)
def NoDeadCodeCases : List (Literal × List (Stmt Op)) → Prop
  | [] => True
  | (_, b) :: cs => NoDeadCodeStmts b ∧ NoDeadCodeCases cs
def NoDeadCodeDflt : Option (List (Stmt Op)) → Prop
  | none => True
  | some b => NoDeadCodeStmts b
end

/-- No statement follows a `break`/`continue`/`leave` at the same level. -/
def NoDeadCodeAtLevel (b : Block Op) : Prop := NoDeadCodeStmts b

end YulEvmCompiler.Optimizer.NormalForm
