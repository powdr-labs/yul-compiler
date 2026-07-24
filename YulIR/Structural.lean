import YulIR.Ast
import YulSemantics.Dialect.EVM

/-!
# YulIR.Structural — structural / control-flow simplification

Local, per-statement rewrites that are only enabled once value numbering has propagated
constants into condition/scrutinee positions:

* `if 0 { … }`            → removed (the atom condition has no side effect);
* `if <nonzero-lit> { b }`→ `{ b }` (unconditional block; condition atom is a no-op);
* `if c { }`              → removed (empty body, pure atom condition);
* `switch <lit k> …`      → the selected case (or default) as a block;
* `{ }`                   → removed (empty block).

Each rewrite is a local, obviously behaviour-preserving transformation (an `Atom` condition
is side-effect-free, so evaluating and discarding it changes nothing). Runs after
`valueNumber` (which turns constant conditions into literals) and before `deadCode`.
-/

namespace YulIR

open YulSemantics (Ident Literal)
open YulSemantics.EVM (litValue)

/-- Is the atom a literal that is (non)zero by dialect value? -/
def Atom.isZeroLit : Atom → Bool
  | .lit l => litValue l == 0
  | .var _ => false

def Atom.isNonzeroLit : Atom → Bool
  | .lit l => litValue l != 0
  | .var _ => false

/-- Select a literal `switch`'s taken block: the first case whose label matches, else default. -/
def selectCase (k : Literal) (cases : List (Literal × Block)) (dflt : Option Block) : Block :=
  match cases.find? (fun p => litValue p.1 == litValue k) with
  | some p => p.2
  | none   => dflt.getD []

mutual
/-- Structurally simplify a statement, yielding zero or more replacement statements. -/
partial def structuralStmt : Stmt → List Stmt
  | .cond c body =>
      let body' := structuralBlock body
      if c.isZeroLit || body'.isEmpty then []          -- never taken, or empty ⇒ drop
      else if c.isNonzeroLit then [.block body']         -- always taken ⇒ unconditional block
      else [.cond c body']
  | .switch c cases dflt =>
      let cases' := cases.map (fun p => (p.1, structuralBlock p.2))
      let dflt' := dflt.map structuralBlock
      match c with
      | .lit k => [.block (selectCase k cases' dflt')]    -- constant scrutinee ⇒ take one branch
      | _      => [.switch c cases' dflt']
  | .block body =>
      let body' := structuralBlock body
      if body'.isEmpty then [] else [.block body']
  | .loop post body => [.loop (structuralBlock post) (structuralBlock body)]
  | .funDef n ps rs body => [.funDef n ps rs (structuralBlock body)]
  | s => [s]

/-- Structurally simplify a block. -/
partial def structuralBlock : Block → Block
  | []      => []
  | s :: ss => structuralStmt s ++ structuralBlock ss
end

/-- Structural simplification over a whole program. -/
def structural (b : Block) : Block := structuralBlock b

end YulIR
