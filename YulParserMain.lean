import YulParser.Compile

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

private def usage : String := "usage: yulc [--parse-only] <file.yul>"

private def runFile (path : String) (parseOnly : Bool) : IO UInt32 := do
  let source ← IO.FS.readFile path
  if parseOnly then
    if (parseSource source).isSome then
      return 0
    else
      IO.eprintln s!"{path}: parse failed"
      return 1
  match compileSource source with
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

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => runFile path false
  | ["--parse-only", path] => runFile path true
  | _ => do
      IO.eprintln usage
      return 64
