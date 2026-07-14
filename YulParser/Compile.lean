import YulParser.Source
import YulEvmCompiler.ObjectCompile

/-!
# YulParser.Compile

The source-text entry point for the compiler. Brace-delimited programs assemble
directly. Object-rooted programs are recursively laid out with their child
objects and data bytes, and `dataoffset`/`datasize` are resolved to constants
in that concrete layout.
-/

namespace YulParser

/-- Parse and compile a complete Yul source program to executable EVM bytecode,
using the documented compatibility parser when the verified parser does not
apply. -/
def compileSource (source : String) : Option ByteArray := do
  match parseSource source with
  | some (.block block) =>
      return YulEvmCompiler.assemble (← YulEvmCompiler.compile block)
  | some (.object o) =>
      let layout ← YulEvmCompiler.compileObject o
      return ByteArray.mk layout.code.toArray
  | none => none

end YulParser
