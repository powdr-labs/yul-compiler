import YulEvmCompiler.Correctness

/-!
# YulEvmCompiler.Examples

Sample straight-line programs run through the compiler, with their emitted
bytecode. Everything here is `#eval`-checked at build time.
-/

namespace YulEvmCompiler.Examples

open YulSemantics
open YulSemantics.EVM (Op)
open YulEvmCompiler

/-- Render assembled bytes as a hex string. -/
def hex (is : List Instr) : String :=
  (assembleBytes is).foldl
    (fun acc b =>
      let d := Nat.toDigits 16 b.toNat
      acc ++ (if d.length = 1 then "0" else "") ++ String.mk d) ""

/-- `sstore(0, add(1, 2))  return(0, 0)` -/
def storeSum : Block Op :=
  [ .exprStmt (.builtin .sstore
      [.lit (.number 0), .builtin .add [.lit (.number 1), .lit (.number 2)]]),
    .exprStmt (.builtin .ret [.lit (.number 0), .lit (.number 0)]) ]

/-- `tstore(42, eq(mload(0), 7))` — falls off the end (implicit STOP). -/
def transientFlag : Block Op :=
  [ .exprStmt (.builtin .tstore
      [.lit (.number 42),
       .builtin .eq [.builtin .mload [.lit (.number 0)], .lit (.number 7)]]) ]

/-- `revert(0, 32)` -/
def alwaysRevert : Block Op :=
  [ .exprStmt (.builtin .revert [.lit (.number 0), .lit (.number 32)]) ]

/-- A program using a not-yet-verified built-in (`sdiv`) is rejected. -/
def usesSdiv : Block Op :=
  [ .exprStmt (.builtin .pop [.builtin .sdiv [.lit (.number 1), .lit (.number 2)]]) ]

/-- A program with variables is rejected (milestone 2). -/
def usesVars : Block Op :=
  [ .letDecl ["x"] (some (.lit (.number 1))) ]

-- PUSH32 2, PUSH32 1, ADD, PUSH32 0, SSTORE, PUSH32 0, PUSH32 0, RETURN
#guard (compileProgram storeSum).isSome
#guard (compileProgram transientFlag).isSome
#guard (compileProgram alwaysRevert).isSome
#guard (compileProgram usesSdiv).isNone
#guard (compileProgram usesVars).isNone

#eval (compileProgram storeSum).map hex
#eval (compileProgram transientFlag).map hex
#eval (compileProgram alwaysRevert).map hex

end YulEvmCompiler.Examples
