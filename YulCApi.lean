import YulParser.Compile
set_option warningAsError true
/-!
# YulCApi

C-ABI exports for embedding this compiler as a native library (see `c/` and
`scripts/build-c-lib.sh`). These are thin, total wrappers around the
production `compileSource` entry point; all C-side concerns (Lean runtime
initialization, string/byte buffer conversion, threading, and stack sizing)
live in the C shim `c/yulc.c`.

The exported status convention mirrors the `yulc` CLI: a program that fails
`compileSource` is classified as a parse failure when `parseSource` also
rejects it, and as "parsed, but uses unsupported compiler features" otherwise.
That classification is done by the shim via `yulc_lean_parses`.
-/

namespace YulCApi

open YulParser

/-- Compile a complete Yul source program (block- or object-rooted) to
executable EVM bytecode. `none` means the program was rejected, either by the
parser or by the compiler's supported-fragment boundary. -/
@[export yulc_lean_compile]
def leanCompile (source : String) : Option ByteArray :=
  compileSource source

/-- Whether the source parses at all. Used by the C shim to distinguish parse
failures from parsed-but-unsupported programs after `leanCompile` returns
`none`, with the same meaning as the `yulc` CLI's exit codes 1 and 2. -/
@[export yulc_lean_parses]
def leanParses (source : String) : Bool :=
  (parseSource source).isSome

end YulCApi
