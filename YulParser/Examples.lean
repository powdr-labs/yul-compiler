import YulParser.Compile

/-!
# YulParser.Examples

End-to-end parser/compiler checks using source in the same form as Solidity's
`test/libyul/yulInterpreterTests` fixtures.
-/

namespace YulParser.Examples

/-- Solidity's `yulInterpreterTests/loop.yul`, including its trailing expected
trace comments. -/
def solidityLoop : String :=
  "{\n" ++
  "    for { let x := 2 } lt(x, 10) { x := add(x, 1) } {\n" ++
  "        mstore(mul(x, 5), mul(x, 0x1000))\n" ++
  "    }\n" ++
  "}\n" ++
  "// ----\n" ++
  "// Trace:\n" ++
  "// Memory dump:\n" ++
  "//     40: 0000000000000000000000900000000000000000000000000000000000000000\n" ++
  "// Storage dump:\n" ++
  "// Transient storage dump:\n"

#guard (parseBlock solidityLoop).isSome
#guard (parseSource solidityLoop).isSome
#guard (compileSource solidityLoop).isSome

/-- An object-rooted Solidity interpreter fixture shape, including nested
objects, a dotted data path, and trailing expectation comments. -/
def solidityObject : String :=
  "object \"main\" {\n" ++
  "  code { datacopy(not(datasize(\"sub.data\")), 0, 0) }\n" ++
  "  object \"sub\" { code {} data \"data\" \"\" }\n" ++
  "}\n" ++
  "// ----\n// Trace:\n"

#guard (parseSource solidityObject).isSome

end YulParser.Examples
