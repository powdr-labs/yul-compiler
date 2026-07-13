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

/-- Hex expression literals use Solidity's byte-string left alignment and can
be compiled through the source entry point. -/
def solidityHexExpression : String := "{ pop(hex\"2233\") }"

#guard hexLiteralValue "2233".toList = 0x2233 * 2 ^ (8 * 30)
#guard (parseSource solidityHexExpression).isSome
#guard (compileSource solidityHexExpression).isSome

/-- Object compatibility covers escaped names, hex data, and data/sub-object
interleaving even though the current AST stores the two item classes apart. -/
def solidityCompatObject : String :=
  "object \"root\\\"name\" {\n" ++
  "  code {}\n" ++
  "  data \"first\" hex\"001122\"\n" ++
  "  object \"child\" { code {} }\n" ++
  "  data \"last\" \"text\"\n" ++
  "}\n"

#guard (parseSource solidityCompatObject).isSome

end YulParser.Examples
