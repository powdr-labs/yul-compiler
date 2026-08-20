import EvmSemantics.Data.Hex
set_option warningAsError true
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

/-- Fully *unoptimized* Yul IR for a Solidity source (`--ir`, solc's `--via-ir`
lowering with the Yul optimizer OFF). Returned from the first `object` line so
it can be fed straight to this compiler. Using the unoptimized IR means the
comparison exercises only solc's Solidity→Yul front-end and none of solc's Yul
optimizer: our (non-optimizing) compiler is measured against solc's fully
optimized bytecode. -/
def solcUnoptimizedIR (solcPath source : String) : IO (Except String String) := do
  let output ← IO.Process.output {
    cmd := solcPath
    args := #["--ir", "--evm-version", "osaka", "-"]
  } (some source)
  if output.exitCode != 0 then
    return .error s!"solc --ir failed: {output.stderr.trimAscii.copy}"
  -- With several contracts in one source (e.g. a contract plus libraries), solc
  -- emits one `IR:` block per contract, ordered by contract name. Keep only the
  -- first block — cut at the next unindented `IR:` header — so the result is a
  -- single well-formed object; the harness pairs it with the first `Binary:`
  -- section, which is the same contract.
  let lines := output.stdout.splitOn "\n"
  let ir := (lines.dropWhile (fun line => !line.startsWith "object ")).takeWhile
    (fun line => line != "IR:")
  if ir.isEmpty then
    return .error "solc --ir produced no object"
  return .ok (String.intercalate "\n" ir)

/-- External function selectors of a Solidity source (`solc --hashes`), each the
8-hex-digit selector. Used to build valid function-call calldata so the gas
comparison exercises the contract's real work instead of dispatch-and-revert. -/
def solcFunctionSelectors (solcPath source : String) : IO (Except String (List String)) := do
  let output ← IO.Process.output {
    cmd := solcPath
    args := #["--hashes", "--evm-version", "osaka", "-"]
  } (some source)
  if output.exitCode != 0 then
    return .error s!"solc --hashes failed: {output.stderr.trimAscii.copy}"
  -- Lines look like "4018d9aa: setX(uint256)"; keep the 8-hex-digit prefix.
  let selectors := (output.stdout.splitOn "\n").filterMap fun rawLine =>
    let line := rawLine.trimAscii.copy
    match line.splitOn ": " with
    | sel :: _ :: _ =>
        if sel.length == 8 && sel.all isHexDigit then some sel else none
    | _ => none
  return .ok selectors

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

/-- solc's own optimized creation bytecode (`--bin --optimize --via-ir`). Used
when a comparison must run the constructor (so constructor-initialized storage is
in place) before replaying calls. -/
def solcCreationBytecode (solcPath source : String) : IO (Except String ByteArray) := do
  let output ← IO.Process.output {
    cmd := solcPath
    args := #["--bin", "--optimize", "--via-ir", "--evm-version", "osaka", "-"]
  } (some source)
  if output.exitCode != 0 then
    return .error s!"solc --bin failed: {output.stderr.trimAscii.copy}"
  return parseBinaryAfter "Binary:" output.stdout

/-! ## Named per-contract sections (library linking)

A source with `// library:` directives compiles to several contracts. The
comparison must select a *named* contract's IR (for this compiler) and Binary
(for solc), and must deploy each declared library, so the single-block helpers
above are not enough. These section parsers split solc's multi-contract output
by name; the no-argument helpers above are left untouched so the no-library path
is byte-for-byte unchanged. -/

/-- Strip solc's `_<id>` object-name suffix (`"C_29" ↦ "C"`, `"L1_17" ↦ "L1"`),
leaving the plain contract name the `--bin` headers and `// library:` directives
use. A name with no numeric suffix is returned unchanged. -/
def objectBaseName (name : String) : String :=
  match (name.splitOn "_").reverse with
  | last :: rest@(_ :: _) =>
      if !last.isEmpty && last.toList.all (fun c => '0' ≤ c && c ≤ '9')
      then String.intercalate "_" rest.reverse else name
  | _ => name

/-- Split `solc --ir` stdout into `(contractName, objectSource)` sections in
emission order. Each section runs from its top-level `object "Name_id" {` line
to the next `IR:` header (matching `solcUnoptimizedIR`'s single-block cut), so
the text can be fed straight to `compileSource`. -/
def irSections (stdout : String) : List (String × String) := Id.run do
  let lines := (stdout.splitOn "\n").toArray
  let mut sections : Array (String × String) := #[]
  let mut i := 0
  while h : i < lines.size do
    let line := lines[i]
    if line.startsWith "object " then
      let mut j := i + 1
      while hj : j < lines.size do
        if lines[j] == "IR:" then break else j := j + 1
      let body := String.intercalate "\n" (lines.extract i j).toList
      -- Object name is the token between the first pair of quotes.
      let afterQuote := (line.splitOn "\"")
      let rawName := afterQuote[1]?.getD ""
      sections := sections.push (objectBaseName rawName, body)
      i := j
    else
      i := i + 1
  return sections.toList

/-- Split `solc --bin` stdout into `(contractName, hexBinary)` sections. Header
lines look like `======= <stdin>:C =======`; the binary is the first non-empty
line after that section's `Binary:` marker. -/
def binSections (stdout : String) : List (String × String) := Id.run do
  let lines := (stdout.splitOn "\n").toArray
  let mut sections : Array (String × String) := #[]
  let mut i := 0
  while h : i < lines.size do
    let line := lines[i].trimAscii.copy
    if line.startsWith "======= " && line.endsWith " =======" then
      -- `======= <stdin>:C =======` → `C`. `.toList` slicing keeps a `String`
      -- (Lean 4.33's `String.drop`/`dropRight` yield a `String.Slice`).
      let chars := line.toList
      let inner := String.ofList ((chars.take (chars.length - " =======".length)).drop "======= ".length)
      let name := match inner.splitOn ":" with
        | _ :: rest@(_ :: _) => String.intercalate ":" rest
        | _ => inner
      -- Find `Binary:` then the first non-empty line before the next header.
      let mut j := i + 1
      let mut hex : Option String := none
      let mut sawBinary := false
      while hj : j < lines.size do
        let l := lines[j].trimAscii.copy
        if l.startsWith "======= " && l.endsWith " =======" then break
        else if l == "Binary:" then sawBinary := true; j := j + 1
        else if sawBinary && !l.isEmpty then hex := some l; break
        else j := j + 1
      if let some h := hex then sections := sections.push (name, h)
      i := j
    else
      i := i + 1
  return sections.toList

/-- Like `binSections`, but preserves solc's *fully-qualified* section name
(`A:L`, `a.sol:C`, …) instead of stripping the leading `<stdin>:`/`<file>:`
qualifier. Multi-source fixtures link by the qualified name (`--libraries
"A:L=…"`, `linkersymbol("A:L")`), so the qualifier must survive. -/
def binSectionsQualified (stdout : String) : List (String × String) := Id.run do
  let lines := (stdout.splitOn "\n").toArray
  let mut sections : Array (String × String) := #[]
  let mut i := 0
  while h : i < lines.size do
    let line := lines[i].trimAscii.copy
    if line.startsWith "======= " && line.endsWith " =======" then
      let chars := line.toList
      let name := String.ofList
        ((chars.take (chars.length - " =======".length)).drop "======= ".length)
      let mut j := i + 1
      let mut hex : Option String := none
      let mut sawBinary := false
      while hj : j < lines.size do
        let l := lines[j].trimAscii.copy
        if l.startsWith "======= " && l.endsWith " =======" then break
        else if l == "Binary:" then sawBinary := true; j := j + 1
        else if sawBinary && !l.isEmpty then hex := some l; break
        else j := j + 1
      if let some h := hex then sections := sections.push (name, h)
      i := j
    else
      i := i + 1
  return sections.toList

/-- Decode one solc `Binary:` hex line, rejecting empty/odd/placeholder output
(an unlinked binary still contains `__$…$__`, which fails the hex-digit test). -/
def decodeSolcBinary (encoded : String) : Except String ByteArray :=
  if encoded.isEmpty || !encoded.all isHexDigit || encoded.length % 2 != 0 then
    throw s!"solc returned malformed/unlinked bytecode: {encoded}"
  else pure (Hex.hexToBytes encoded)

/-- The `--libraries "<fq>=0x<addr>,…"` argument fragment, empty when no
libraries are declared. Each `fqName` is solc's fully-qualified name
(`<stdin>:L`); each `addr` is a 40-hex-digit address without `0x`. solc 0.8.35
accepts the comma-separated `<name>=<address>` form in one argument. -/
def librariesArg (libs : List (String × String)) : Array String :=
  if libs.isEmpty then #[]
  else #["--libraries",
    String.intercalate "," (libs.map fun (fq, addr) => s!"{fq}=0x{addr}")]

/-- All `--ir` contract sections (unoptimized Yul), keyed by contract name.
`--libraries` is deliberately NOT passed: solc leaves `linkersymbol` in the IR
regardless, and this compiler resolves it from its own `LinkEnv`. -/
def solcIRSections (solcPath source : String)
    : IO (Except String (List (String × String))) := do
  let output ← IO.Process.output {
    cmd := solcPath
    args := #["--ir", "--evm-version", "osaka", "-"]
  } (some source)
  if output.exitCode != 0 then
    return .error s!"solc --ir failed: {output.stderr.trimAscii.copy}"
  return .ok (irSections output.stdout)

/-- All optimized creation `Binary:` sections (`--bin --optimize --via-ir`),
keyed by contract name, with `--libraries` linking applied. -/
def solcCreationSections (solcPath source : String) (libs : List (String × String))
    : IO (Except String (List (String × String))) := do
  let output ← IO.Process.output {
    cmd := solcPath
    args := #["--bin", "--optimize", "--via-ir", "--evm-version", "osaka"]
      ++ librariesArg libs ++ #["-"]
  } (some source)
  if output.exitCode != 0 then
    return .error s!"solc --bin failed: {output.stderr.trimAscii.copy}"
  return .ok (binSections output.stdout)

/-! ## Multi-source fixtures (`==== Source: NAME ====`)

A `semanticTests` fixture may hold several named sources. solc cannot read those
from stdin — each section is written to a file named `NAME` under a working
directory, and solc is invoked with the *bare file names* as arguments and its
cwd set to that directory, so `import "A" as M;` and friends resolve. Output
sections are then headed by solc's fully-qualified `NAME:Contract` (no `<stdin>:`
prefix), which the harness links and selects against. -/

/-- All `--ir` sections (unoptimized Yul) for a multi-source fixture, keyed by
solc's object base name (`objectBaseName`), in emission order. `files` are bare
names resolved relative to `workdir`. -/
def solcIRSectionsMulti (solcPath : String) (workdir : String) (files : List String)
    : IO (Except String (List (String × String))) := do
  let output ← IO.Process.output {
    cmd := solcPath
    args := #["--ir", "--evm-version", "osaka"] ++ files.toArray
    cwd := some workdir
  }
  if output.exitCode != 0 then
    return .error s!"solc --ir failed: {output.stderr.trimAscii.copy}"
  return .ok (irSections output.stdout)

/-- All optimized creation `Binary:` sections (`--bin --optimize --via-ir`) for a
multi-source fixture, keyed by solc's *fully-qualified* `NAME:Contract`, with
`--libraries` linking applied. -/
def solcCreationSectionsMulti (solcPath : String) (workdir : String)
    (files : List String) (libs : List (String × String))
    : IO (Except String (List (String × String))) := do
  let output ← IO.Process.output {
    cmd := solcPath
    args := #["--bin", "--optimize", "--via-ir", "--evm-version", "osaka"]
      ++ librariesArg libs ++ files.toArray
    cwd := some workdir
  }
  if output.exitCode != 0 then
    return .error s!"solc --bin failed: {output.stderr.trimAscii.copy}"
  return .ok (binSectionsQualified output.stdout)

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
