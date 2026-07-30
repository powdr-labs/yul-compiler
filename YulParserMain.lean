import YulParser.Compile

set_option warningAsError true
/-!
# yulc

A minimal command-line entry point for parser/compiler differential testing.
In parse-only mode it accepts both brace-delimited programs and object-rooted
files. Compilation accepts either form and prints the assembled EVM bytecode
as lowercase hex.
-/

open YulParser YulEvmCompiler

private def outputHexDigits : Array Char :=
  #['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f']

private def byteHex (b : UInt8) : String :=
  let n := b.toNat
  String.ofList [outputHexDigits[n / 16]!, outputHexDigits[n % 16]!]

private def codeHex (code : ByteArray) : String :=
  String.join (code.data.toList.map byteHex)

private def usage : String :=
  "usage: yulc [--parse-only] [--libraries=NAME=ADDR[,NAME=ADDR…]] <file.yul>"

private def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (10 + c.toNat - 'a'.toNat)
  else if 'A' ≤ c && c ≤ 'F' then some (10 + c.toNat - 'A'.toNat)
  else none

private def parseAddress? (text : String) : Option Nat :=
  let digits := (if text.startsWith "0x" || text.startsWith "0X" then
    (text.drop 2).copy else text).toList
  if digits.isEmpty then none
  else digits.foldl (fun acc c => do
    let acc ← acc
    let d ← hexDigit? c
    some (16 * acc + d)) (some 0)

/-- Parse solc's `--libraries` spelling: `file.sol:Lib=0xADDR` entries, comma
separated. A library name may itself contain `:`, so split on the *last* `=`. -/
private def parseLibraries? (spec : String) : Option LinkEnv :=
  if spec.isEmpty then some [] else
  (spec.splitOn ",").foldr (fun entry acc => do
    let acc ← acc
    let parts := entry.splitOn "="
    match parts.reverse with
    | address :: rest@(_ :: _) =>
        let name := String.intercalate "=" rest.reverse
        if name.isEmpty then none else
        return (name.trimAscii.copy, ← parseAddress? address.trimAscii.copy) :: acc
    | _ => none) (some [])

private def runFile (path : String) (parseOnly : Bool)
    (libraries : LinkEnv := []) : IO UInt32 := do
  let source ← IO.FS.readFile path
  if parseOnly then
    if (parseSource source).isSome then
      return 0
    else
      IO.eprintln s!"{path}: parse failed"
      return 1
  match compileSource source libraries with
  | none =>
      match parseSource source with
      | none =>
          IO.eprintln s!"{path}: parse failed"
          return 1
      | some _ =>
          IO.eprintln s!"{path}: parsed, but uses unsupported compiler features"
          return 2
  | some code =>
      IO.println (codeHex code)
      return 0

def main (args : List String) : IO UInt32 := do
  let parseOnly := args.contains "--parse-only"
  let libSpecs := args.filterMap fun arg =>
    if arg.startsWith "--libraries=" then
      some (arg.drop "--libraries=".length).copy
    else none
  let positional := args.filter fun arg => !arg.startsWith "--"
  match positional, libSpecs.mapM parseLibraries? with
  | [path], some libraries => runFile path parseOnly libraries.flatten
  | _, none => do
      IO.eprintln "yulc: malformed --libraries (expected NAME=0xADDR[,…])"
      return 64
  | _, _ => do
      IO.eprintln usage
      return 64
