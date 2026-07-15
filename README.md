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

The object layer in `YulEvmCompiler/ObjectCompile.lean` recursively compiles
sub-objects, resolves `dataoffset`/`datasize` to actual layout constants, emits
a `STOP` seam before embedded child/data bytes, and exposes real offset/size
maps. `compileObject_consistent` proves that every direct data segment is at
its recorded byte range. `codesize`, `codecopy`, and `datacopy` are verified
built-ins. `compileObject_correct` proves the complete execution statement:
every `RunObject` derivation under the generated layout is simulated by the
emitted EVM bytecode. The proof covers layout-reference resolution, the
executable prefix, normal fall-through through the `STOP` seam, exact
source-level halts, and recursively embedded child/data payload bytes.

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
`YulParser.compileSource` compiles either brace-delimited programs or complete
object roots and returns executable EVM bytecode.

The verified built-in set (the domain of `opTable` in
`YulEvmCompiler/OpTable.lean`):

| group      | ops |
|------------|-----|
| arithmetic | `add sub mul div sdiv mod smod addmod mulmod exp signextend clz` |
| comparison | `lt gt slt sgt eq iszero` |
| bitwise    | `and or xor not byte shl shr sar` |
| hashing    | `keccak256` |
| stack      | `pop` |
| storage    | `sload sstore tload tstore` |
| memory     | `mload mstore mstore8 mcopy msize` |
| calldata   | `calldataload calldatasize calldatacopy` |
| returndata | `returndatasize returndatacopy` |
| code       | `codesize codecopy datacopy extcodesize extcodecopy extcodehash` |
| env/block  | `address origin caller callvalue gasprice selfbalance coinbase timestamp number prevrandao gaslimit chainid basefee blobbasefee blockhash` |
| world/tx   | `balance blobhash` |
| logging    | `log0 log1 log2 log3 log4` |
| calls      | `call callcode delegatecall staticcall` |
| creation   | `create create2` |
| halting    | `stop return revert invalid selfdestruct` |

Everything else in the direct built-in path is rejected (`compile = none`).
Object-relative `dataoffset`/`datasize` calls are resolved separately by the
verified object compiler; `gas` remains blocked because the source semantics
does not model its execution. CALL- and CREATE-family
operations use the open-world relational model described below. The
memory-write proofs
use the `writeBytes` read-after-write lemma that now lives upstream
(`EvmSemantics.MachineState.writeBytes_getElem?_getD`); `MSTORE` additionally
rests on two `ByteArray` reduction facts about evm-semantics'
`natToBytesPadded`, proved in `YulEvmCompiler.BytesLemmas`. No project-specific
axioms remain — the `#print axioms` footprint is just the standard classical
axioms.

## The theorem

`YulEvmCompiler.compile_correct` (in `YulEvmCompiler/Correctness.lean`):

> If `compile prog = some is` and the Yul semantics runs `prog` from
> machine state `st₀` to `st'` with outcome `o`
> under external call/create relations whose responses are realized by complete
> target executions, then there is a gas bound `b`
> such that from **every** initial EVM state that matches `st₀`
> (`StateMatch`), executes `assemble is` (`FrameOK`), starts at `pc = 0` with
> an empty stack, and holds at least `b` gas, the EVM semantics reaches
> (`Steps`) a final state that matches `st'` and halts the way `o` prescribes:
> `.Success` via the implicit `STOP` for `o = .normal`, or exactly the halt
> recorded in `st'.halted` (`stop`/`return`+payload/`revert`+payload/
> `invalid`/`invalidMemoryAccess`/`selfdestruct`) for `o = .halt`.

`compile_correct_eval` restates the conclusion through evm-semantics'
result-level big-step judgment: `Eval s₀ .success`, resp.
`Eval s₀ (resultOf hk)`.

`YulEvmCompiler.compileObject_correct` lifts the same guarantee to recursively
compiled objects. If `compileObject o = some L` and `RunObject o L V st' out`,
then EVM execution of the complete `L.code` simulates that run. The proof first
replaces `dataoffset`/`datasize` by the exact words in `L`, then runs the block
simulation on the executable prefix; normal fall-through executes the explicit
`STOP` seam, while children and data remain available as the trailing code
payload used by `codesize`, `codecopy`, and `datacopy`.

The proof is a two-phase forward simulation:

* **Phase A** (`YulEvmCompiler/SimAsm.lean`, `SimA.sim`): the Yul derivation
  is simulated by the byte-free, gas-free Asm machine (`AsmSem.lean`). Jumps
  resolve labels to code suffixes; function environments are tracked by
  `FEnvOK`, established at each block via `hoist_ok`.
* **Phase B** (`YulEvmCompiler/LowerCorrect.lean`, `asteps_sim`/
  `arun_halt_sim`): each local Asm step maps to 1–3 EVM steps; a call or
  creation maps to a complete `Steps` trace. `ConfMatch` is restored at the
  caller/creator, and existential gas bounds add along the execution.

`ExternalsRealized` packages the endpoint conditions `CallsRealized` and
`CreatesRealized`: they constrain the state before a CALL/CREATE-family opcode
and the restored caller/creator afterward, but do not constrain intermediate
call stacks. Consequently the theorem covers arbitrary callee and init code,
nested calls and creations, and reentrant executions of the creator.

The correspondence `StateMatch` relates memory pointwise (total function vs.
zero-padded `ByteArray`) and its active-word high-water mark, Yul's flat
storage/transient storage to the executing account's storage, calldata and
executing code pointwise (with exact lengths), and every account's nonce,
persistent/transient storage, code bytes, lengths, and hashes through the
account map. It also relates historical block hashes and emitted
logs and scheduled self-destructing addresses in order, plus returndata
byte-for-byte with its exact length. `EnvMatch` also requires the source
environment's
configurable Keccak oracle to agree pointwise with the target hash primitive. Gas is
existentially bounded because yul-semantics deliberately does not model gas.
Per-instruction facts live in
`OpStep.lean`, byte-level decoding facts in `Decode.lean`, and the
`BitVec 256` ↔ `UInt256` arithmetic agreements in `Value.lean`.

`selfdestruct` follows the pinned Osaka/Cancun EIP-6780 behavior: the opcode
immediately transfers (or, for a same-address beneficiary, conditionally
retains/burns) the executing account's balance, records the address for
transaction cleanup, and halts successfully. The proof covers both contracts
created in the current transaction and pre-existing contracts. Actual account
deletion is a transaction-finalization operation in evm-semantics and lies
outside this frame-level compiler theorem.

The headline theorems check with no `sorry`. Their `#print axioms` footprint is
exactly the three standard classical axioms (`propext`, `Classical.choice`,
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
`parseSource` follows parsing with the strict-assembly validation needed for
these fixtures: identifier and literal rules, scopes and function signatures,
builtin arities and direct-literal arguments, control-flow placement, switch
cases, object names/data references, immutable references, and version-gated
builtin names. The mismatch baseline is currently empty. CI fails if a new
entry appears or a stale entry remains in
`test/solidity-yul-syntax-known-mismatches.txt`; the comparison logic lives in
`scripts/CheckSoliditySyntaxTests.lean`.

CI also attempts to compile and execute every upstream Yul interpreter fixture
whose `EVMVersion` range includes the latest supported fork (Osaka). The exact
set that does not yet pass is pinned in
`test/solidity-yul-interpreter-known-failures.txt`; CI fails for both new
failures and stale entries. The reusable runner in
`YulEvmCompilerTests/InterpreterFixture.lean` constructs Solidity's fixed Yul
test environment, runs the assembled bytecode with `evm-semantics`, and
exactly compares every nonzero memory word, persistent-storage entry, and
transient-storage entry with the dumps embedded after `// ----`. Object roots
go through the production object compiler. The current baseline contains 21
fixtures; three of those are object fixtures whose AST-interpreter dumps
deliberately use synthetic hash offsets/sizes and a dummy code buffer rather
than the state produced by compiled object bytecode. The remaining entries are
unsupported operations, resource-limit cases, or environment/runner gaps and
are listed explicitly in the baseline file.

CI additionally compiles every latest-fork source fixture in Solidity's
positive `yulOptimizerTests`, `objectCompiler`, and `evmCodeTransform`
corpora. `scripts/CheckSolidityCompileTests.lean` strips solc's settings and
golden-output sections, invokes the production `compileSource` entry point,
and compares all failures with three exact baselines under `test/`. The check
does not require our optimizer output, assembly, or bytecode to match solc:
those are implementation-specific, while accepting and compiling the same
valid Yul source is the compatibility property being tracked. New failures
and stale baseline entries both fail CI.

For all three suites, CI also performs an independent behavioral comparison
against solc 0.8.35, installed with pinned
[`svm-rs`](https://github.com/alloy-rs/svm-rs) 0.5.26. Both compilers receive
the same Yul source; their bytecode executes in `evm-semantics` from six
identical pre-states: Solidity's interpreter-test default, one fixed patterned
state, and four states derived reproducibly from the fixture path. The latter
cover calldata lengths 1, 31, 32, and 33 plus varied call values, balances,
persistent storage, and transient storage. The runner compares termination,
return/revert bytes, returndata, nonzero memory, account state, logs,
self-destructs, and storage refunds. It deliberately ignores exact code bytes,
PCs, operand stacks, remaining gas, and zero-only memory expansion. For
`yulOptimizerTests` this checks backend behavior over the original fixture
source; it does not run the configured solc optimization step or claim
optimizer equivalence. Exact baselines track unsupported programs,
layout-introspection differences, and bounded-divergence differences; a new
failure or stale entry fails CI. Deterministic hash-based CI shards cover each
fixture and baseline entry exactly once while running the expanded suite in
parallel.

`YulEvmCompiler/Examples.lean` compiles sample programs at build time
(`#guard`/`#eval`), including `switch`, multi-value returns and assignments,
a `for` loop, a recursive function, and an iterative Fibonacci over storage —
each run **differentially** through both the Yul interpreter and
evm-semantics' `stepF` on the compiled bytecode, with affected state compared. It
also compiles yul-semantics' own
`FibExample.fibContract` (the calldata/memory Fibonacci contract proved
correct upstream) all the way to bytecode, differentially checks a concrete
`keccak256("abc")`, checks all five log arities including exact emitted log
contents, checks CREATE/CREATE2 compilation, and checks that the compiled
Fibonacci code returns the same bytes as the interpreter for several inputs.

## Roadmap

See `PLAN.md` for the full design and upstream findings (including EIP-8024
`DUPN`/`SWAPN` not yet being activated on any modeled fork, and the
`writeBytes`/`natToBytesPadded` byte-array lemmas used by `MSTORE`). The next
integration milestones are typed parser
syntax and verification of the lossy compatibility path, broader built-in
coverage, and then verified optimization passes on the Yul side.

## License

Apache 2.0, matching the two semantics repositories.

[powdr-labs/yul-semantics]: https://github.com/powdr-labs/yul-semantics
[powdr-labs/evm-semantics]: https://github.com/powdr-labs/evm-semantics
