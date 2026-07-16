import EvmSemantics.Data.Hex

/-!
# Driving a pinned `solc` as an external process

Shared helpers for the runners that compile the same strict-assembly Yul source
with `solc` and this compiler. Extracted so the behavioral differential and the
gas comparisons invoke `solc` identically: the same `--strict-assembly`,
`--evm-version osaka` invocation and the same pinned-version guard.
-/

namespace YulEvmCompilerTests.Solc

open EvmSemantics

private def isHexDigit (char : Char) : Bool :=
  ('0' <= char && char <= '9') ||
    ('a' <= char && char <= 'f') ||
    ('A' <= char && char <= 'F')

private def findBinary (marker : String) (afterMarker : Bool) : List String → Option String
  | [] => none
  | rawLine :: lines =>
      let line := rawLine.trimAscii.copy
      if afterMarker && !line.isEmpty then some line
      else findBinary marker (afterMarker || line == marker) lines

private def parseBinaryAfter (marker stdout : String) : Except String ByteArray := do
  let encoded ← match findBinary marker false (stdout.splitOn "\n") with
    | some encoded => pure encoded
    | none => throw s!"solc output did not contain '{marker}'"
  if encoded.isEmpty || !encoded.all isHexDigit || encoded.length % 2 != 0 then
    throw s!"solc returned malformed bytecode: {encoded}"
  return Hex.hexToBytes encoded

private def parseSolcBinary (stdout : String) : Except String ByteArray :=
  parseBinaryAfter "Binary representation:" stdout

/-- Compile one strict-assembly Yul source with `solc`, pinned to the same
Osaka target the executable EVM checks use, and return the emitted bytecode. -/
def compileWithSolc (solcPath source : String) : IO (Except String ByteArray) := do
  let output ← IO.Process.output {
    cmd := solcPath
    args := #["--strict-assembly", "--bin", "--evm-version", "osaka", "-"]
  } (some source)
  if output.exitCode != 0 then
    return .error s!"solc compilation failed: {output.stderr.trimAscii.copy}"
  return parseSolcBinary output.stdout

/-- Optimized Yul IR for a Solidity source, via solc's `--via-ir` pipeline with
the Yul optimizer enabled (`--ir-optimized --optimize`). Returned from the first
`object` line so it can be fed straight to this compiler; this is the same Yul
solc lowers to bytecode, so compiling it here is a fair basis for comparison. -/
def solcOptimizedIR (solcPath source : String) : IO (Except String String) := do
  let output ← IO.Process.output {
    cmd := solcPath
    args := #["--ir-optimized", "--optimize", "--evm-version", "osaka", "-"]
  } (some source)
  if output.exitCode != 0 then
    return .error s!"solc --ir-optimized failed: {output.stderr.trimAscii.copy}"
  let lines := output.stdout.splitOn "\n"
  let ir := lines.dropWhile (fun line => !line.startsWith "object ")
  if ir.isEmpty then
    return .error "solc --ir-optimized produced no object"
  return .ok (String.intercalate "\n" ir)

/-- solc's own optimized runtime bytecode for a Solidity source
(`--bin-runtime --optimize --via-ir`) — the reference for gas comparison. -/
def solcRuntimeBytecode (solcPath source : String) : IO (Except String ByteArray) := do
  let output ← IO.Process.output {
    cmd := solcPath
    args := #["--bin-runtime", "--optimize", "--via-ir", "--evm-version", "osaka", "-"]
  } (some source)
  if output.exitCode != 0 then
    return .error s!"solc --bin-runtime failed: {output.stderr.trimAscii.copy}"
  return parseBinaryAfter "Binary of the runtime part:" output.stdout

/-- Reject any `solc` other than the pinned version, so every checked-in gas
figure and every differential result reproduces from a single toolchain. -/
def checkSolcVersion (solcPath expectedVersion : String) : IO (Except String Unit) := do
  let output ← IO.Process.output { cmd := solcPath, args := #["--version"] }
  if output.exitCode != 0 then
    return .error s!"solc --version failed: {output.stderr.trimAscii.copy}"
  let marker := s!"Version: {expectedVersion}+"
  if !output.stdout.contains marker then
    return .error (s!"expected solc {expectedVersion}, got:\n" ++ output.stdout.trimAscii.copy)
  return .ok ()

end YulEvmCompilerTests.Solc
