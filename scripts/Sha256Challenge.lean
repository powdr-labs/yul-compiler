import YulEvmCompilerTests.InterpreterFixture
import EvmSemantics.Crypto.Sha256
set_option warningAsError true
/-!
# `sha256challenge` — the SHA-256 challenge scorer

Runs a candidate SHA-256 implementation in the pinned executable EVM
semantics and scores it against the canonical spec: the very function the
`0x02` precompile computes in `evm-semantics`
(`EvmSemantics.Crypto.Sha256.hash`).

```sh
lake exe sha256challenge                          # score the reference Yul
lake exe sha256challenge --yul=path/to/impl.yul   # score a Yul submission
lake exe sha256challenge --hex=path/to/impl.hex   # score raw bytecode
lake exe sha256challenge --csv                    # machine-readable rows
```

A candidate must, for every vector, halt with `Returned` and exactly the
32 bytes of `hash(calldata)`. Vectors cover the FIPS 180-4 published cases
and every padding boundary (`len % 64 ∈ {0, 55, 56, 63}`, empty input,
multi-block inputs), each run twice: once in a clean frame and once in a
frame with dirty storage, transient storage, and nonzero call value — a
correct implementation of a precompile cannot depend on any of that.

This is **Tier 1** of the challenge: falsification by execution. It is a
necessary condition for a submission, never a sufficient one — the
sufficient condition is a Lean proof of `Challenge.Sha256.Correct`.
-/

open EvmSemantics
open YulEvmCompilerTests.InterpreterFixture (initialState runEvm)

namespace Sha256Challenge

/-- Gas budget for one scored run. Generous: the reference is not optimized,
and a rejected candidate should fail on its digest, not on our budget. -/
def scoringGas : Nat := 3_000_000_000

/-- Step budget for one scored run. -/
def scoringFuel : Nat := 200_000_000

structure Vector where
  label : String
  input : ByteArray

/-- `n` bytes of a fixed, non-repeating pattern. -/
def patterned (n : Nat) : ByteArray := Id.run do
  let mut bs := ByteArray.empty
  for i in [:n] do
    bs := bs.push (UInt8.ofNat ((i * 37 + (i / 251) * 11 + 7) % 256))
  return bs

def repeated (n : Nat) (b : UInt8) : ByteArray := Id.run do
  let mut bs := ByteArray.empty
  for _ in [:n] do
    bs := bs.push b
  return bs

/-- The scored vectors. The lengths are chosen around the FIPS padding
boundaries: `55` is the largest one-block message, `56` is the smallest
message whose length field spills into a second block, `64` is an exact
block, and the larger ones exercise the block loop. -/
def vectors : List Vector :=
  [ { label := "empty", input := ByteArray.empty }
  , { label := "abc", input := "abc".toUTF8 }
  , { label := "1-byte", input := patterned 1 }
  , { label := "31-byte", input := patterned 31 }
  , { label := "32-byte", input := patterned 32 }
  , { label := "54-byte", input := patterned 54 }
  , { label := "55-byte (last one-block)", input := patterned 55 }
  , { label := "56-byte (length spills)", input := patterned 56 }
  , { label := "fips-b2 (56-byte)"
    , input := "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".toUTF8 }
  , { label := "63-byte", input := patterned 63 }
  , { label := "64-byte (exact block)", input := patterned 64 }
  , { label := "65-byte", input := patterned 65 }
  , { label := "119-byte", input := patterned 119 }
  , { label := "120-byte", input := patterned 120 }
  , { label := "127-byte", input := patterned 127 }
  , { label := "128-byte (two blocks)", input := patterned 128 }
  , { label := "256-byte", input := patterned 256 }
  , { label := "1000-byte", input := patterned 1000 }
  , { label := "1000 a's", input := repeated 1000 0x61 } ]

/-- Two FIPS 180-4 digests, hard-coded so that a scoring run also
re-validates the oracle it scores against. -/
def oracleChecks : List (ByteArray × String) :=
  [ (ByteArray.empty,
     "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
  , ("abc".toUTF8,
     "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad") ]

/-- A frame calling `code` with `calldata`. `dirty` additionally seeds
storage, transient storage, and a nonzero call value: a faithful SHA-256
must ignore all of it. -/
def frame (code calldata : ByteArray) (dirty : Bool) : EVM.State :=
  let state := initialState code
  let address := state.executionEnv.address
  let account := state.accountMap address
  let account := if !dirty then account else
    { account with
      storage := account.storage
        |>.set (UInt256.ofNat 0) (UInt256.ofNat 0xdeadbeef)
        |>.set (UInt256.ofNat 1) (UInt256.ofNat (2 ^ 255))
        |>.set (UInt256.ofNat 0x120) (UInt256.ofNat 0xffff)
      tstorage := account.tstorage
        |>.set (UInt256.ofNat 0) (UInt256.ofNat 7)
        |>.set (UInt256.ofNat 0x20) (UInt256.ofNat 9) }
  let accounts := state.accountMap.set address account
  { state with
    gasAvailable := scoringGas
    accountMap := accounts
    substate := { state.substate with originalAccountMap := accounts }
    executionEnv := {
      state.executionEnv with
      calldata
      weiValue := if dirty then UInt256.ofNat 0x1234 else UInt256.ofNat 0
    } }

inductive Outcome where
  | ok (gas : Nat)
  | wrongDigest (got : String) (gas : Nat)
  | badHalt (halt : String) (gas : Nat)
  | outOfFuel

def outcomeGas : Outcome → Option Nat
  | .ok gas | .wrongDigest _ gas | .badHalt _ gas => some gas
  | .outOfFuel => none

/-- Run one vector and compare the returned bytes with the canonical spec. -/
def score (code calldata : ByteArray) (dirty : Bool) : Outcome :=
  let start := frame code calldata dirty
  let final := runEvm scoringFuel start
  if !final.isDone then .outOfFuel else
  let gas := start.gasAvailable - final.gasAvailable
  match final.halt with
  | .Returned =>
      if final.hReturn == Crypto.Sha256.hash calldata then .ok gas
      else .wrongDigest (Hex.bytesToHex final.hReturn) gas
  | h => .badHalt (toString (repr h)) gas

end Sha256Challenge

open Sha256Challenge

private def hexToBytes? (text : String) : Option ByteArray :=
  let text := (if text.startsWith "0x" then text.drop 2 else text).trimAscii.copy
  let text := text.replace "\n" "" |>.replace " " ""
  if text.length % 2 != 0 then none
  else if !text.all fun c =>
      ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F') then none
  else some (Hex.hexToBytes text)

private def pad (text : String) (width : Nat) : String :=
  text ++ String.ofList (List.replicate (width - text.length) ' ')

private def usage : String :=
  "usage: sha256challenge [--yul=FILE | --hex=FILE] [--csv]\n" ++
  "  default: Challenge/Sha256/reference.yul"

def main (args : List String) : IO UInt32 := do
  let flag (name : String) : Option String :=
    args.findSome? fun arg =>
      if arg.startsWith s!"--{name}=" then some (arg.drop (name.length + 3)).copy else none
  let csv := args.contains "--csv"
  if args.contains "--help" then
    IO.println usage
    return 0
  -- The oracle re-check: a scoring run that disagrees with FIPS is not a
  -- scoring run at all.
  for (input, expected) in oracleChecks do
    if Hex.bytesToHex (Crypto.Sha256.hash input) != expected then
      IO.eprintln "sha256challenge: the canonical spec disagrees with FIPS 180-4"
      return 3
  let (name, code) ←
    match flag "hex", flag "yul" with
    | some _, some _ => do IO.eprintln usage; return 64
    | some path, none => do
        match hexToBytes? (← IO.FS.readFile path) with
        | none => do IO.eprintln s!"{path}: not a hex bytecode file"; return 64
        | some code => pure (path, code)
    | none, yulPath => do
        let path := yulPath.getD "Challenge/Sha256/reference.yul"
        let source ← IO.FS.readFile path
        match YulParser.compileSource source with
        | none => do
            IO.eprintln s!"{path}: rejected by the verified compiler"
            return 2
        | some code => pure (path, code)
  if csv then
    IO.println "vector,bytes,frame,status,gas"
  else
    IO.println s!"== {name} =="
    IO.println s!"bytecode: {code.size} bytes"
    IO.println ""
    IO.println s!"{pad "vector" 26}{pad "bytes" 7}{pad "clean gas" 12}{pad "dirty gas" 12}status"
  let mut failures := 0
  let mut totalGas := 0
  let mut totalBytes := 0
  for v in vectors do
    let clean := score code v.input false
    let dirty := score code v.input true
    let status :=
      match clean, dirty with
      | .ok g1, .ok g2 => if g1 == g2 then "ok" else s!"ok (state-dependent gas: {g1} vs {g2})"
      | .wrongDigest got _, _ => s!"WRONG DIGEST {got}"
      | _, .wrongDigest got _ => s!"WRONG DIGEST (dirty frame) {got}"
      | .badHalt h _, _ => s!"HALTED {h}"
      | _, .badHalt h _ => s!"HALTED (dirty frame) {h}"
      | .outOfFuel, _ | _, .outOfFuel => "OUT OF FUEL"
    let ok := status.startsWith "ok"
    if !ok then failures := failures + 1
    match clean with
    | .ok gas => do totalGas := totalGas + gas; totalBytes := totalBytes + v.input.size
    | _ => pure ()
    let gasText : Outcome → String
      | o => match outcomeGas o with | some g => toString g | none => "-"
    if csv then
      IO.println s!"{v.label},{v.input.size},clean,{status},{gasText clean}"
      IO.println s!"{v.label},{v.input.size},dirty,{status},{gasText dirty}"
    else
      IO.println s!"{pad v.label 26}{pad (toString v.input.size) 7}\
        {pad (gasText clean) 12}{pad (gasText dirty) 12}{status}"
  if !csv then
    IO.println ""
    IO.println s!"total gas over all vectors: {totalGas} ({totalBytes} input bytes)"
    if failures == 0 then
      IO.println "Tier 1: PASS — every vector matches EvmSemantics.Crypto.Sha256.hash"
    else
      IO.println s!"Tier 1: FAIL — {failures} vector(s) mismatched"
  return (if failures == 0 then 0 else 1)
