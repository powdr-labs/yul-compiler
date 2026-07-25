import EvmSemantics.Crypto.Keccak256
import EvmSemantics.Data.Hex
set_option warningAsError true
/-!
# Parsing Solidity semantic-test call specs

Solidity's `semanticTests` fixtures specify concrete calls in their `// ----`
section, e.g.

```
// ----
// constructor(): 1, 2 ->
// f(uint256): 42 -> 42
// g(), 1 ether: 0x20, 3, "abc" -> true
```

Each argument is already given in flattened ABI form (a word per number, offset
and length words spelled out for dynamic types, string/hex literals for the
tail). We parse these into calldata (`keccak256(sig)[:4]` ++ encoded args) plus a
call value, so the gas comparison replays the *real* calls the test intends
rather than synthetic inputs. Constructor args and value are captured too.

Unsupported argument spellings (rare builtins) make the value — and hence the
call — unparseable. `Spec.declaredCalls` retains the source count so callers
that require complete replay can distinguish that from a fixture with no calls.
-/

namespace YulEvmCompilerTests.SolTest

open EvmSemantics

/-- 32-byte big-endian word of `n mod 2^256`. -/
def natToWord (n : Nat) : ByteArray := Id.run do
  let n := n % (2 ^ 256)
  let mut bytes := ByteArray.empty
  for i in [0:32] do
    bytes := bytes.push (UInt8.ofNat ((n >>> (8 * (31 - i))) % 256))
  return bytes

/-- Right-pad bytes with zeros to a whole number of 32-byte words. -/
def padRight32 (bs : ByteArray) : ByteArray := Id.run do
  let rem := bs.size % 32
  if rem == 0 then return bs
  let mut out := bs
  for _ in [0:32 - rem] do
    out := out.push 0
  return out

private def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'
private def isHexDigit (c : Char) : Bool :=
  isDigit c || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

private def hexVal (c : Char) : Nat :=
  if isDigit c then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f' then 10 + c.toNat - 'a'.toNat
  else 10 + c.toNat - 'A'.toNat

private def parseDec (s : String) : Option Nat :=
  let cs := s.toList
  if cs.isEmpty || !cs.all isDigit then none
  else some (cs.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0)

private def parseHex (s : String) : Option Nat :=
  let cs := s.toList
  if cs.isEmpty || !cs.all isHexDigit then none
  else some (cs.foldl (fun n c => n * 16 + hexVal c) 0)

private def dropN (s : String) (n : Nat) : String := String.ofList (s.toList.drop n)
private def takeN (s : String) (n : Nat) : String := String.ofList (s.toList.take n)

private def stripPrefix (s p : String) : Option String :=
  if s.startsWith p then some (dropN s p.length) else none

private def dropSuffix (s p : String) : Option String :=
  if s.endsWith p then some (takeN s (s.length - p.length)) else none

/-- Encode one soltest value token into its ABI word(s), or `none` if the
spelling is one we do not handle. -/
def encodeValue (raw : String) : Option ByteArray := do
  let t := raw.trimAscii.copy
  if t == "true" then return natToWord 1
  if t == "false" then return natToWord 0
  if let some inner := stripPrefix t "hex\"" then
    let inner ← dropSuffix inner "\""
    if !inner.all isHexDigit || inner.length % 2 != 0 then failure
    return padRight32 (Hex.hexToBytes inner)
  if t.startsWith "\"" then
    let inner ← dropSuffix (dropN t 1) "\""
    return padRight32 inner.toUTF8
  if let some hex := stripPrefix t "0x" then
    return natToWord (← parseHex hex)
  if let some hex := stripPrefix t "0X" then
    return natToWord (← parseHex hex)
  if let some inner := stripPrefix t "right(" then
    return natToWord (← parseDec (← dropSuffix inner ")"))
  if let some neg := stripPrefix t "-" then
    return natToWord (2 ^ 256 - (← parseDec neg))
  return natToWord (← parseDec t)

/-- Split an argument list at top-level commas, ignoring commas inside quotes or
parentheses. -/
def splitArgs (s : String) : List String := Id.run do
  let mut parts : List String := []
  let mut cur : String := ""
  let mut depth := 0
  let mut inStr := false
  for c in s.toList do
    if inStr then
      cur := cur.push c
      if c == '"' then inStr := false
    else if c == '"' then inStr := true; cur := cur.push c
    else if c == '(' then depth := depth + 1; cur := cur.push c
    else if c == ')' then depth := depth - 1; cur := cur.push c
    else if c == ',' && depth == 0 then parts := cur :: parts; cur := ""
    else cur := cur.push c
  parts := cur :: parts
  return (parts.reverse.map (·.trimAscii.copy)).filter (!·.isEmpty)

/-- Encode a comma-separated argument list to concatenated ABI words. -/
def encodeArgs (s : String) : Option ByteArray := do
  let mut out := ByteArray.empty
  for tok in splitArgs s do
    out := out ++ (← encodeValue tok)
  return out

/-- 4-byte function selector `keccak256(sig)[:4]`. -/
def selector (sig : String) : ByteArray :=
  (natToWord (EvmSemantics.keccak256Impl sig.toUTF8).toNat).extract 0 4

private def parseValue (spec : String) : Nat :=
  let spec := spec.trimAscii.copy
  match spec.splitOn " " with
  | [amount, unit] =>
      let n := (parseDec amount).getD 0
      match unit with
      | "ether" => n * 10 ^ 18
      | "gwei" => n * 10 ^ 9
      | "wei" => n
      | _ => 0
  | _ => 0

structure Call where
  sig : String
  value : Nat
  calldata : ByteArray

structure Spec where
  ctorArgs : ByteArray := ByteArray.empty
  ctorValue : Nat := 0
  declaredCalls : Nat := 0
  calls : Array Call := #[]

/-- Parse one call/constructor line (already stripped of its `// ` prefix and
trailing `# … #` comment). `header` is everything before `:` (a signature and an
optional `, <value> <unit>`); `args` is the argument list (empty if none). -/
private def parseHeaderArgs (line : String) : Option (String × Nat × String) :=
  let (headerArgs, _rest) :=
    match (line.splitOn " -> ") with
    | h :: t => (h, t)
    | [] => (line, [])
  let (header, args) :=
    match headerArgs.splitOn ":" with
    | [h] => (h.trimAscii.copy, "")
    | h :: rest => (h.trimAscii.copy, (String.intercalate ":" rest).trimAscii.copy)
    | [] => ("", "")
  match header.splitOn ", " with
  | [sig] => some (sig.trimAscii.copy, 0, args)
  | [sig, value] => some (sig.trimAscii.copy, parseValue value, args)
  | _ => none

/-- Parse the `// ----` expectation section into a replayable spec. Lines that
are not calls (gas/storage/comments) are skipped. Unsupported calls are absent
from `calls` but remain included in `declaredCalls`. -/
def parseSpec (source : String) : Spec := Id.run do
  let lines := source.splitOn "\n"
  let body := lines.dropWhile (fun l => l.trimAscii.copy != "// ----")
  let mut spec : Spec := {}
  for raw in body do
    let line := raw.trimAscii.copy
    let some content := stripPrefix line "//" | continue
    let content := content.trimAscii.copy
    -- Drop trailing `# … #` inline comments.
    let content := (content.splitOn "#")[0]!.trimAscii.copy
    if content.isEmpty || content == "----" then continue
    if content.startsWith "gas " || content.startsWith "storage" ||
        content.startsWith "~ " || content.startsWith "left(" then continue
    let hasResult := (content.splitOn " -> ").length >= 2
    let isConstructor := content.startsWith "constructor("
    if hasResult && !isConstructor then
      spec := { spec with declaredCalls := spec.declaredCalls + 1 }
    let some (sig, value, args) := parseHeaderArgs content | continue
    if !sig.contains '(' then continue
    if isConstructor then
      match encodeArgs args with
      | some encoded => spec := { spec with ctorArgs := encoded, ctorValue := value }
      | none => pure ()
    -- A real call line always has a `->` result; without one this is a gas or
    -- storage annotation (e.g. gasTests' `a(): 2425`), not a call.
    else if !hasResult then continue
    else
      match encodeArgs args with
      | some encoded =>
          spec := { spec with
            calls := spec.calls.push { sig, value, calldata := selector sig ++ encoded } }
      | none => pure ()
  return spec

end YulEvmCompilerTests.SolTest
