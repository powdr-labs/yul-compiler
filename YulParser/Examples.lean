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
#guard compileSource solidityLoop ==
  compileSourceWithBackend solidityLoop [] .automatic
#guard (compileSourceWithBackend solidityLoop [] .classic).isSome

/-- A small program for which automatic selection prefers SSA. Keep the two
outputs distinct so the explicit classic policy cannot become a no-op. -/
def backendSelectionProbe : String :=
  "{ let a := calldataload(0) let b := calldataload(32) " ++
  "let c := add(a, b) mstore(0, c) return(0, 32) }"

#guard compileSourceWithBackend backendSelectionProbe [] .automatic !=
  compileSourceWithBackend backendSelectionProbe [] .classic

/-! `slotnum` is introduced after Osaka. It remains a legal identifier for
pre-Amsterdam syntax fixtures, but is reserved when Amsterdam is selected. -/
#guard (parseSource
  "{ function slotnum() {} }\n// ====\n// EVMVersion: <amsterdam\n// ----\n").isSome
#guard (parseSource
  "{ function slotnum() {} }\n// ====\n// EVMVersion: >=amsterdam\n// ----\n").isNone

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
#guard (compileSourceWithBackend solidityObject [] .classic).isSome

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

/-! Immutables. `loadimmutable` compiles to a fixed-width `PUSH32` placeholder
in the deployed object, and the constructor's `setimmutable` becomes one
`mstore` per recorded placeholder offset — so the returned runtime carries the
value the constructor computed. -/
def immutablePair : String :=
  "object \"A\" {\n" ++
  "  code { let s := datasize(\"A_deployed\") codecopy(0, dataoffset(\"A_deployed\"), s)\n" ++
  "         setimmutable(0, \"42\", caller()) return(0, s) }\n" ++
  "  object \"A_deployed\" { code { sstore(0, loadimmutable(\"42\")) } }\n" ++
  "}\n"

#guard (parseSource immutablePair).isSome
#guard (compileSource immutablePair).isSome

/-! A block-rooted program has no object tree, so nothing could ever patch a
placeholder: a `loadimmutable` there is rejected rather than compiled to a
hard-coded zero. The *grammar* still accepts it — upstream's syntax corpus has a
fixture for exactly this — so the limit lives in compilation, not parsing. -/
#guard (parseSource "{ sstore(0, loadimmutable(\"x\")) }").isSome
#guard (compileSource "{ sstore(0, loadimmutable(\"x\")) }").isNone

/-! The root has no parent to copy and patch its code, so a `loadimmutable` in
the root's own code could only ever read the unpatched placeholder — however
many setters the tree contains. -/
#guard (compileSource
  ("object \"A\" { code { setimmutable(0, \"x\", caller()) " ++
   "sstore(0, loadimmutable(\"x\")) stop() } }")).isNone

/-! Only `setimmutable`'s middle argument names the immutable; the target and
the stored value are ordinary expressions. An escaped string value must be
patched in as its *bytes*, not as the characters of its escape spelling — so
`"\\x01"` must compile exactly like `hex"01"`, the same bytes spelled without
escapes. -/
def escapedImmutableValue (spelling : String) : String :=
  "object \"A\" {\n" ++
  "  code { let s := datasize(\"B\") codecopy(0, dataoffset(\"B\"), s)\n" ++
  "         setimmutable(0, \"x\", " ++ spelling ++ ") return(0, s) }\n" ++
  "  object \"B\" { code { sstore(0, loadimmutable(\"x\")) } }\n" ++
  "}\n"

#guard (compileSource (escapedImmutableValue "\"\\x01\"")).isSome
#guard (compileSource (escapedImmutableValue "\"\\x01\"")) ==
       (compileSource (escapedImmutableValue "hex\"01\""))

/-! An immutable is patched by the **parent** of the object that reads it.
Validation pairs reads with writes only globally, so a setter sitting in an
unrelated sibling satisfies it while patching nothing — the reader would deploy
with its placeholder still zero. The pairing is re-checked per scope. -/
def crossScopeImmutable : String :=
  "object \"A\" {\n" ++
  "  code { let s := datasize(\"B\") codecopy(0, dataoffset(\"B\"), s) return(0, s) }\n" ++
  "  object \"B\" { code { sstore(0, loadimmutable(\"x\")) } }\n" ++
  "  object \"C\" { code { setimmutable(0, \"x\", caller()) stop() } }\n" ++
  "}\n"

#guard (parseSource crossScopeImmutable).isSome
#guard (compileSource crossScopeImmutable).isNone

/-! Two sibling objects declaring the same immutable put its placeholder at
different offsets, but `setimmutable(base, name, value)` names no child and
`base` points at a copy of one of them. Patching one at the other's offsets
would overwrite its code, so the ambiguous name is rejected. -/
def siblingImmutables : String :=
  "object \"A\" {\n" ++
  "  code { let s := datasize(\"B\") codecopy(0, dataoffset(\"B\"), s)\n" ++
  "         setimmutable(0, \"x\", caller()) return(0, s) }\n" ++
  "  object \"B\" { code { sstore(0, loadimmutable(\"x\")) } }\n" ++
  "  object \"C\" { code { sstore(1, 1) sstore(2, 2) sstore(3, loadimmutable(\"x\")) } }\n" ++
  "}\n"

#guard (parseSource siblingImmutables).isSome
#guard (compileSource siblingImmutables).isNone

/-! A `loadimmutable` with no matching `setimmutable` is rejected by validation:
nothing would ever write that placeholder. -/
#guard (parseSource
  "object \"A\" { code { sstore(0, loadimmutable(\"42\")) } }").isNone

/-! `setimmutable` alone is fine — it simply patches nothing. -/
#guard (compileSource
  "object \"A\" { code { setimmutable(0, \"42\", 7) stop() } }").isSome

/-! The prune is shadowing-proof by over-approximation: if the bound name is
referenced anywhere in the program — even a write — the binding is kept and the
program is rejected rather than miscompiled. -/
#guard (compileSource
  "object \"A\" { code { let a := linkersymbol(\"file.sol:L\") a := 1 sstore(0, a) } }").isNone

/-! Supplying the library's link-time address makes the *used* form compile:
the occurrence is substituted with that address before anything else runs, so
what reaches the optimizer and the backend is ordinary Yul. Only the named
library is resolved; a different one is still rejected. -/
def linkedL : LinkEnv := [("file.sol:L", 0x1234567890abcdef1234567890abcdef12345678)]

#guard (compileSource usedLinkerObject linkedL).isSome
#guard (compileSource
  "object \"A\" { code { let a := linkersymbol(\"file.sol:Other\") sstore(0, a) } }"
  linkedL).isNone

/-! Linking is a substitution, so the linked program is exactly the one with
the address written out by hand. -/
#guard (compileSource usedLinkerObject linkedL) ==
  (compileSource
    ("object \"A\" { code { let a := 0x1234567890abcdef1234567890abcdef12345678 " ++
      "sstore(0, a) } }"))

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
