import YulEvmCompiler.Correctness
import YulSemantics.Syntax

/-!
# YulEvmCompiler.Examples

Sample programs run through the compiler, with their emitted bytecode.
Everything here is `#eval`/`#guard`-checked at build time.
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

/-- `let x := 7  x := add(x, 1)  sstore(0, x)` — declaration, read, assign. -/
def letAssign : Block Op :=
  [ .letDecl ["x"] (some (.lit (.number 7))),
    .assign ["x"] (.builtin .add [.var "x", .lit (.number 1)]),
    .exprStmt (.builtin .sstore [.lit (.number 0), .var "x"]) ]

/-- `let a, b  { let c := 1  a := c }  sstore(0, a)` — nested block scoping. -/
def blockScope : Block Op :=
  [ .letDecl ["a", "b"] none,
    .block
      [ .letDecl ["c"] (some (.lit (.number 1))),
        .assign ["a"] (.var "c") ],
    .exprStmt (.builtin .sstore [.lit (.number 0), .var "a"]) ]

/-- 16 declarations, then a read of the deepest — exactly `DUP16`. -/
def deep16 : Block Op :=
  ((List.range 16).map fun i => .letDecl [s!"x{i}"] (some (.lit (.number i))))
    ++ [.exprStmt (.builtin .pop [.var "x0"])]

/-- 17 declarations, then a read of the deepest — beyond `DUP16`, rejected
(EIP-8024's `DUPN` would lift this once evm-semantics activates it). -/
def deep17 : Block Op :=
  ((List.range 17).map fun i => .letDecl [s!"x{i}"] (some (.lit (.number i))))
    ++ [.exprStmt (.builtin .pop [.var "x0"])]

/-- A program using a not-yet-verified built-in (`sdiv`) is rejected. -/
def usesSdiv : Block Op :=
  [ .exprStmt (.builtin .pop [.builtin .sdiv [.lit (.number 1), .lit (.number 2)]]) ]

#guard (compileProgram storeSum).isSome
#guard (compileProgram letAssign).isSome
#guard (compileProgram blockScope).isSome
#guard (compileProgram deep16).isSome
#guard (compileProgram deep17).isNone
#guard (compileProgram usesSdiv).isNone

/-- Written in the yul-semantics concrete-syntax DSL: `if` with a variable. -/
def maxStore : Block Op := yul% {
  let a := 3
  let b := 5
  if lt(a, b) { a := b }
  sstore(0, a)
}

/-- Nested `if`s, blocks, and an early `return`. -/
def guarded : Block Op := yul% {
  let x := sload(0)
  if iszero(x) { revert(0, 0) }
  if gt(x, 100) {
    let capped := 100
    sstore(1, capped)
    return(0, 0)
  }
  sstore(1, x)
}

#guard (compileProgram maxStore).isSome
#guard (compileProgram guarded).isSome

#eval (compileProgram maxStore).map hex

#eval (compileProgram storeSum).map hex
#eval (compileProgram letAssign).map hex
#eval (compileProgram blockScope).map hex

end YulEvmCompiler.Examples
