# yul-evm-compiler

A **verified compiler from Yul to EVM bytecode**, written in Lean 4.

* Source semantics: [powdr-labs/yul-semantics] — the big-step relational
  judgment `YulSemantics.Step` over the gas-free EVM dialect
  (`Value := BitVec 256`).
* Target semantics: [powdr-labs/evm-semantics] — the small-step relation
  `EvmSemantics.EVM.Step` and its big-step closure `Eval`.

Both repos are ordinary Lake dependencies (same toolchain `v4.31.0`, same
Mathlib revision), so the correctness theorem quantifies over *both semantics
as they are* — nothing is re-encoded.

## Pipeline

Compilation goes through a **labeled-assembly intermediate layer**, so all
control-flow and calling-convention reasoning is byte- and gas-free, while all
gas/decode/layout arithmetic is a single generic per-instruction simulation:

```
Yul --compileStmts--> List Asm --lowerProg--> List Instr --assemble--> ByteArray
        (phase A proof)            (phase B proof)          (Decode lemmas)
```

`compile` is the full pipeline; `compileProgram` produces the labeled
assembly (and runs a decidable `wfCheck` on it, which hands the proof unique
and defined jump labels with zero freshness bookkeeping).

## Current scope

A non-optimizing compiler for programs with **variables, nested blocks,
`if`, `switch`, `for` loops (with `break`/`continue`), and user-defined
`function`s (with `leave`, recursion, calls, and up to 16 return values)**:

* `let` declarations (initialized or zeroed), single- and multi-variable
  assignments, built-in expression statements, `{ … }` scoping;
* `if` → `ISZERO; PUSH32 dest; JUMPI … JUMPDEST`;
* `switch` → a verified chain of literal comparisons and conditional jumps,
  with an optional `default` block;
* `for {init} c {post} {body}` with backward jumps, `break`/`continue`
  compiling to statically-known `pop`s down to the loop scope + a `jump`;
* `function f(ps) -> rs { body }` compiled inline (jumped over), called with a
  pushed return address (`pushLabel`) and a `dynJump` back; `leave` pops to
  the function frame and jumps to the epilogue; a `SWAP1 … SWAPk` rotation
  returns `k ≤ 16` values in source order.

Literals compile to `PUSH32`; a built-in call compiles its arguments
right-to-left (Yul's evaluation order, which also puts the first argument on
top of the stack) followed by the built-in's opcode; a program that falls off
the end of its bytecode performs the EVM's implicit `STOP`, matching Yul's
`.normal` outcome.

Variables live on the operand stack: the compile-time layout mirrors the
semantics' `VEnv` exactly. Reads compile to `DUP(off+idx+1)`, assignments to
`SWAP(idx+1); POP`, `let x := e` is free (the value stays put), and block
exit pops the block's locals. Because EIP-8024 (`DUPN`/`SWAPN`) is not yet
activated on any fork modeled by evm-semantics, accesses deeper than
`DUP16`/`SWAP16` are **rejected at compile time** (`compile = none`);
lifting that restriction is a codegen-only change once the fork table
activates EIP-8024.

The object layer has a verified foundation in
`YulEvmCompiler/ObjectCompile.lean`: `compileObject` appends an object's data
segments to its compiled code, builds the layout maps, and proves that every
segment is placed at its recorded offset and size. `codesize`, `codecopy`, and
`datacopy` are verified built-ins. Full object execution is still out of
scope: references to `dataoffset`/`datasize` are not yet resolved to layout
constants inside compiled code, nested sub-object bytecode is not laid out,
and the end-to-end EVM theorem does not yet admit a trailing data suffix.
Verified optimization passes and the remaining hash/log/environment ops and
memory writers are also deferred.

`YulParser.parseSource` parses brace-delimited programs and object-rooted files
in the supported grammar into the `yul-semantics` AST. `parseBlock` and
`parseObject` have verified canonical round-trip theorems: input accepted by
those parsers is preserved up to whitespace, comments, and number base,
including the source spelling of string escapes. The public source entry point
additionally has a compatibility fallback for `hex"..."` expression literals
and object data, and interleaved sub-objects/data. Hex expression literals are
lowered to their left-aligned 256-bit numeric value; interleaved items are normalized into the
AST's separate sub-object and data lists. This lossy fallback is intentionally
outside the canonical round-trip theorem. Public entry points cap recursive
grammar fuel at 256, rejecting excessively nested input. Parsing remains
mostly syntactic: it does not generally perform name resolution, scope or
control-context checks, built-in arity checking, or other Solidity semantic
validation. Type annotations are still deferred.
`YulParser.compileSource` connects brace-delimited programs directly to
`compile`. Object roots can be passed as ASTs to the foundational
`compileObject`, but the source entry point deliberately remains block-only
until layout-reference resolution and nested-object layout are implemented.

The verified built-in set (the domain of `opTable` in
`YulEvmCompiler/OpTable.lean`):

| group      | ops |
|------------|-----|
| arithmetic | `add sub mul div sdiv mod smod addmod mulmod exp clz` |
| comparison | `lt gt slt sgt eq iszero` |
| bitwise    | `and or xor not byte shl shr sar` |
| stack      | `pop` |
| storage    | `sload sstore tload tstore` |
| memory     | `mload mstore` |
| calldata   | `calldataload` |
| code       | `codesize codecopy datacopy` |
| env/block  | `address origin caller callvalue gasprice coinbase timestamp number prevrandao gaslimit chainid basefee blobbasefee` |
| halting    | `stop return revert invalid` |

Everything else is rejected (`compile = none`) — see `PLAN.md` for exactly
why each remaining op is deferred (some are plain proof debt; the rest are
blocked on upstream issues found during this work). The `MSTORE` correctness
proof rests on two `ByteArray` reduction facts about evm-semantics'
`natToBytesPadded`, proved in `YulEvmCompiler.BytesLemmas`, plus the
`writeBytes` read-after-write lemma that now lives upstream
(`EvmSemantics.MachineState.writeBytes_getElem?_getD`). No project-specific
axioms remain — the `#print axioms` footprint is just the standard classical
axioms.

## The theorem

`YulEvmCompiler.compile_correct` (in `YulEvmCompiler/Correctness.lean`):

> If `compile prog = some is` and the Yul semantics runs `prog` from
> machine state `st₀` to `st'` with outcome `o`
> (`YulSemantics.Run yul prog st₀ V' st' o`), then there is a gas bound `b`
> such that from **every** initial EVM state that matches `st₀`
> (`StateMatch`), executes `assemble is` (`FrameOK`), starts at `pc = 0` with
> an empty stack, and holds at least `b` gas, the EVM semantics reaches
> (`Steps`) a final state that matches `st'` and halts the way `o` prescribes:
> `.Success` via the implicit `STOP` for `o = .normal`, or exactly the halt
> recorded in `st'.halted` (`stop`/`return`+payload/`revert`+payload/
> `invalid`) for `o = .halt`.

`compile_correct_eval` restates the conclusion through evm-semantics'
result-level big-step judgment: `Eval s₀ .success`, resp.
`Eval s₀ (resultOf hk)`.

The proof is a two-phase forward simulation:

* **Phase A** (`YulEvmCompiler/SimAsm.lean`, `SimA.sim`): the Yul derivation
  is simulated by the byte-free, gas-free Asm machine (`AsmSem.lean`). Jumps
  resolve labels to code suffixes; function environments are tracked by
  `FEnvOK`, established at each block via `hoist_ok`.
* **Phase B** (`YulEvmCompiler/LowerCorrect.lean`, `asteps_sim`/
  `arun_halt_sim`): each Asm step maps to 1–3 EVM steps on the assembled
  bytecode, preserving `ConfMatch`, with existential gas bounds that add along
  the execution.

The correspondence `StateMatch` relates memory pointwise (total function vs.
zero-padded `ByteArray`), Yul's flat storage/transient storage to the
executing account's storage, and calldata and executing code pointwise (with
an exact code-length agreement). Gas is existentially bounded because
yul-semantics deliberately does not model gas. Per-instruction facts live in
`OpStep.lean`, byte-level decoding facts in `Decode.lean`, and the
`BitVec 256` ↔ `UInt256` arithmetic agreements in `Value.lean`.

Both theorems check with no `sorry`. Their `#print axioms` footprint is exactly
the three standard classical axioms (`propext`, `Classical.choice`,
`Quot.sound`) and nothing else — the `ByteArray` facts used by `MSTORE` are all
genuine theorems (`writeBytes` upstream, the two `natToBytesPadded` lemmas in
`YulEvmCompiler.BytesLemmas`). `Checks.lean` pins that exact set in CI.

## Building

```sh
lake exe cache get   # prebuilt Mathlib oleans
lake build           # builds both semantics deps + the compiler + proofs
lake env lean --run YulParserMain.lean --parse-only program.yul
```

The last command checks either accepted top-level source form without the
native executable build. `lake build yulc` additionally builds a CLI that
emits compiled bytecode for brace-delimited programs.

CI also sparse-checks out Solidity's moving `develop` version of
`test/libyul/yulSyntaxTests` and runs `parseSource` on every fixture. A fixture
is treated as an expected rejection when its expectation section after
`// ----` contains an `*Error` diagnostic; warnings remain expected successes.
This deliberately includes Solidity semantic and code-generation errors even
though this project currently provides only a syntax parser. The exact set of
known disagreements is pinned in
`test/solidity-yul-syntax-known-mismatches.txt`: CI fails if a new mismatch
appears or an existing entry becomes stale. The comparison logic lives in
`scripts/CheckSoliditySyntaxTests.lean`.

CI also attempts to compile and execute every upstream Yul interpreter fixture.
The exact set that does not yet pass is pinned in
`test/solidity-yul-interpreter-known-failures.txt`; CI fails for both new
failures and stale entries. The reusable runner in
`YulEvmCompilerTests/InterpreterFixture.lean` constructs Solidity's fixed Yul
test environment, runs the assembled bytecode with `evm-semantics`, and
exactly compares every nonzero memory word, persistent-storage entry, and
transient-storage entry with the dumps embedded after `// ----`.

`YulEvmCompiler/Examples.lean` compiles sample programs at build time
(`#guard`/`#eval`), including `switch`, multi-value returns and assignments,
a `for` loop, a recursive function, and an iterative Fibonacci over storage —
each run **differentially** through both the Yul interpreter and
evm-semantics' `stepF` on the compiled bytecode, with storage compared. It
also compiles yul-semantics' own
`FibExample.fibContract` (the calldata/memory Fibonacci contract proved
correct upstream) all the way to bytecode and checks, differentially, that the
compiled code returns the same bytes as the interpreter for several inputs.

## Roadmap

See `PLAN.md` for the full design, the upstream findings (EIP-8024
`DUPN`/`SWAPN` not yet activated on any modeled fork; the two repos' distinct
opaque keccaks; and the `writeBytes`/`natToBytesPadded` byte-array lemmas that
`MSTORE` needs — `writeBytes` now upstream, `natToBytesPadded` proved locally in
`YulEvmCompiler.BytesLemmas`). The next integration milestones are completing
the object pipeline (layout-reference resolution, nested objects, trailing
data, and constructors), typed parser syntax and verification of the lossy
compatibility path, and then verified optimization passes on the Yul side.

## License

Apache 2.0, matching the two semantics repositories.

[powdr-labs/yul-semantics]: https://github.com/powdr-labs/yul-semantics
[powdr-labs/evm-semantics]: https://github.com/powdr-labs/evm-semantics
