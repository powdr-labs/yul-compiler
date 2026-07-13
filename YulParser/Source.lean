import YulParser.Obj

/-!
# YulParser.Source

A common source-text entry point for the two top-level forms accepted by Yul:
brace-delimited statement blocks and `object` trees.
-/

namespace YulParser

/-- A complete parsed Yul source file. -/
inductive Source where
  | block (statements : List (YulSemantics.Stmt YulSemantics.EVM.Op))
  | object (value : YulSemantics.Object YulSemantics.EVM.Op)

/-- Parse a complete Yul source file, including trailing whitespace or comments. -/
def parseSource (source : String) : Option Source :=
  match parseBlock source with
  | some statements => some (.block statements)
  | none => (parseObject source).map .object

end YulParser
