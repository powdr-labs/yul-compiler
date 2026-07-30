import YulParser.Compile
set_option warningAsError true
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
#guard (compileSource solidityObject).isSome

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
#guard (compileSource solidityCompatObject).isSome

/-- A dead `linkersymbol` binding — solc's unoptimized IR emits one for every
qualified internal library call — is pruned before compilation, but a program
that references the value stays outside the supported fragment. -/
def deadLinkerObject : String :=
  "object \"A\" { code { let a := linkersymbol(\"file.sol:L\") sstore(0, 1) } }"

def usedLinkerObject : String :=
  "object \"A\" { code { let a := linkersymbol(\"file.sol:L\") sstore(0, a) } }"

#guard (parseSource deadLinkerObject).isSome
#guard (compileSource deadLinkerObject).isSome
#guard (parseSource usedLinkerObject).isSome
#guard (compileSource usedLinkerObject).isNone

/-! Nested layout entries are keyed by `litValue (.string ·)`, which keeps only
32 UTF-8 bytes. A grandchild object plus the `.metadata` segment solc emits in
every object contributes two qualified names sharing a 32-byte prefix, whose
keys therefore alias — which used to fail the whole tree's key-uniqueness check
even though neither name is referenceable (`litWF` caps a string literal at 32
bytes, so the validator rejects any `dataoffset`/`datasize` naming them). -/
def nestedMetadataObject : String :=
  "object \"Wrap\" { code { stop() } " ++
  "object \"PreviewHub_9270\" { " ++
  "code { let s := datasize(\"PreviewHub_9270_deployed\") " ++
  "datacopy(0, dataoffset(\"PreviewHub_9270_deployed\"), s) return(0, s) } " ++
  "object \"PreviewHub_9270_deployed\" { code { sstore(0, 1) } " ++
  "data \".metadata\" hex\"a2646970667358221220\" } } }"

#guard (parseSource nestedMetadataObject).isSome
#guard (compileSource nestedMetadataObject).isSome

/-! A *referenceable* qualified name must survive, however long it is. Layout
references are validated by `objectNameAllowed`, not `literalWordWF`, so a name
over 32 bytes is legal: this is Solidity's own `yulInterpreterTests`
`long_object_name.yul`, resolving the 33-byte
`"object2.object3.object4.datablock"`. Filtering propagated entries by *length*
rather than by referenceability would reject it. -/
def longObjectName : String :=
  "object \"t\" { code { " ++
  "datacopy(not(datasize(\"object2.object3.object4.datablock\")), 0, 0) } " ++
  "object \"object2\" { code{} object \"object3\" { code{} " ++
  "object \"object4\" { code{} data \"datablock\" \"\" } } } }"

#guard (parseSource longObjectName).isSome
#guard (compileSource longObjectName).isSome

/-! Shortening either generated name brings both keys under 32 bytes; the same
tree compiled before the fix too, so this pins that the fix did not change it. -/
#guard (compileSource
  ("object \"Wrap\" { code { stop() } object \"P\" { " ++
   "code { let s := datasize(\"Pd\") datacopy(0, dataoffset(\"Pd\"), s) return(0, s) } " ++
   "object \"Pd\" { code { sstore(0, 1) } " ++
   "data \".metadata\" hex\"a2646970667358221220\" } } }")).isSome

/-! The prune is shadowing-proof by over-approximation: if the bound name is
referenced anywhere in the program — even a write — the binding is kept and the
program is rejected rather than miscompiled. -/
#guard (compileSource
  "object \"A\" { code { let a := linkersymbol(\"file.sol:L\") a := 1 sstore(0, a) } }").isNone

/-! The source entry point also runs Solidity-compatible validation after the
grammar has produced an AST.  These checks pin representative scope, arity,
control-flow, literal, switch, object, and EVM-version rules locally; CI covers
the complete upstream syntax corpus. -/

#guard (parseSource "{ function f(a) -> r { r := a } let x := f(1) }").isSome
#guard (parseSource "{ let x := add(1) }").isNone
#guard (parseSource "{ break }").isNone
#guard (parseSource "{ let x := 1 let x := 2 }").isNone
#guard (parseSource "{ switch 0 case 0 {} case \"\" {} }").isNone
#guard (parseSource "{ let x := 0100 }").isNone
#guard (parseSource "object \"A\" { code { pop(datasize(\"missing\")) } }").isNone
#guard (parseSource ("{ function mcopy() {} mcopy() }\n" ++
  "// ====\n// EVMVersion: <cancun\n// ----\n")).isSome

end YulParser.Examples
