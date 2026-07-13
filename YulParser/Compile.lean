import YulParser.Source
import YulEvmCompiler.Compile

/-!
# YulParser.Compile

The source-text entry point for the verified compiler. Compilation currently
accepts the brace-delimited form used by most solc Yul interpreter tests;
`parseSource` also accepts object-rooted files, whose layout is not yet
supported by the compiler.
-/

namespace YulParser

/-- Parse and compile a complete brace-delimited Yul source program, using the
hex-literal compatibility parser when the verified parser does not apply. -/
def compileSource (source : String) : Option (List YulEvmCompiler.Instr) := do
  let block ← parseBlock source <|> parseBlockCompat source
  YulEvmCompiler.compile block

end YulParser
