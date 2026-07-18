import YulParser.Validate

set_option warningAsError true

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

/-- Parse a complete Yul source file, including trailing whitespace or comments.
The verified block/object parsers are tried first, followed by the documented
lossy Solidity-compatibility parsers. -/
def parseSource (source : String) : Option Source :=
  match parseBlock source with
  | some statements =>
      if validateBlockSource source statements then some (.block statements)
      else (parseBlockCompat source).bind fun compat =>
        if validateBlockSource source compat then some (.block compat) else none
  | none =>
      match parseBlockCompat source with
      | some statements =>
          if validateBlockSource source statements then some (.block statements) else none
      | none =>
          match parseObject source with
          | some value =>
              if validateObjectSource source value then some (.object value)
              else (parseObjectCompat source).bind fun compat =>
                if validateObjectSource source compat then some (.object compat) else none
          | none =>
              match parseObjectCompat source with
              | some value => if validateObjectSource source value then some (.object value) else none
              | none => none

end YulParser
