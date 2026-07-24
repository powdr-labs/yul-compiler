import YulIR
import YulSemantics.Syntax
import YulSemantics.PrettyPrint

/-!
# YulIR.Examples — round-trip smoke tests

`#eval` these to see a Yul program, its IR (re-emitted as Yul), and confirm the
Yul → IR → Yul round-trip is faithful. Run with `lake env lean YulIR/Examples.lean`.
-/

namespace YulIR.Examples

open YulSemantics EVM

/-- A `for`-loop with mutable, loop-carried variables (the ANF + for-init + condition
lowering case). -/
def loopProg := yul% {
  let x := 0
  let i := 0
  for { } lt(i, 10) { i := add(i, 1) } {
    x := add(x, i)
  }
  sstore(0, x)
}

/-- Nested expressions exercising ANF flattening and right-to-left arg evaluation. -/
def nestedProg := yul% {
  let a := add(sload(0), sload(1))
  sstore(a, mul(add(1, 2), 3))
}

/-- A user function call, a switch, and an if. -/
def mixedProg := yul% {
  function f(p, q) -> r {
    r := add(p, q)
  }
  let n := f(3, 4)
  if lt(n, 100) {
    switch n
    case 7 { sstore(0, 1) }
    default { sstore(0, 2) }
  }
}

/-- Show a program, its IR re-emitted to Yul (the round-trip), side by side. -/
def demo (name : String) (p : YulSemantics.Block YulSemantics.EVM.Op) : IO Unit := do
  IO.println s!"══════════ {name} ══════════"
  IO.println "── source Yul ──"
  IO.println (EVM.print p)
  IO.println "── IR re-emitted to Yul (ofYul ▸ toYul) ──"
  IO.println (EVM.print (YulIR.toYul (YulIR.ofYul p)))
  IO.println ""

#eval demo "loop" loopProg
#eval demo "nested / ANF" nestedProg
#eval demo "function + switch + if" mixedProg

end YulIR.Examples
