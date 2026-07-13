# Working on `yul-compiler`

This repository is a Lean 4 implementation and proof of a non-optimizing Yul-to-EVM compiler. Treat compiler code, its intermediate semantics, and its simulation proofs as one feature: accepting a program without extending the relevant proof is not a completed change.

## Repository map

The end-to-end pipeline is:

```text
Yul source
  -> YulParser.parseBlock / parseBlockCompat
  -> yul-semantics AST (Block YulSemantics.EVM.Op)
  -> compileProgram / compileStmts
  -> List Asm                         symbolic, gas-free, byte-free control flow
  -> lowerProg
  -> List Instr                       PUSH32 or one-byte EVM operation
  -> assemble
  -> ByteArray                        executable EVM bytecode
```

The proof follows the same split:

```text
YulSemantics.Step/Run
  -> SimA.sim                         Yul execution simulates to Asm execution
  -> asteps_sim / arun_halt_sim       Asm execution simulates to EVM Steps
  -> compile_correct / compile_correct_eval
```

Important files:

- `YulEvmCompiler/Compile.lean`: Yul AST to labeled `Asm`; stack layout, label allocation, function and loop contexts.
- `YulEvmCompiler/Asm.lean`: labeled IR, fixed byte widths, label well-formedness, label resolution, and lowering to `Instr`.
- `YulEvmCompiler/AsmSem.lean`: gas-free semantics for `Asm`, using the Yul dialect's own `stepOp` for built-ins.
- `YulEvmCompiler/SimAsm.lean`: Phase A proof. Its `Motive` mirrors the source big-step derivation and its accepted compile equations.
- `YulEvmCompiler/Instr.lean`: minimal byte-level IR and assembler.
- `YulEvmCompiler/Decode.lean`: byte layout, decoding, and valid-jump-destination lemmas.
- `YulEvmCompiler/Value.lean`: agreement between Yul `BitVec 256` values and evm-semantics `UInt256` operations.
- `YulEvmCompiler/StateRel.lean`: `MemMatch`, `EnvMatch`, `StateMatch`, `FrameOK`, and halt/result correspondence.
- `YulEvmCompiler/OpTable.lean`: single source of truth for supported Yul built-ins and their EVM opcodes.
- `YulEvmCompiler/OpStep.lean`: one-op EVM simulations, dynamic gas bounds, and state-preservation proofs.
- `YulEvmCompiler/LowerDefs.lean`: Phase B configuration/stack correspondence and bytecode location lemmas.
- `YulEvmCompiler/LowerCorrect.lean`: Phase B simulation, one `Asm` constructor at a time, then trace composition.
- `YulEvmCompiler/Correctness.lean`: composition into the public correctness theorems.
- `YulEvmCompiler/ObjectCompile.lean`: foundational object/data layout and its data-segment consistency theorem; full object execution remains incomplete.
- `YulEvmCompiler/Examples.lean`: build-time compilation guards and executable differential tests between both semantics.
- `YulParser/`: parser library. `Canon.lean` supports verified canonical round trips; `Compat.lean` is an intentionally lossy Solidity-compatibility fallback.
- `YulEvmCompilerTests/InterpreterFixture.lean`: runner for Solidity's Yul interpreter fixtures.
- `scripts/CheckSoliditySyntaxTests.lean` and `scripts/CheckSolidityInterpreterTests.lean`: corpus/baseline drivers used by CI.
- `Checks.lean`: exact axiom-footprint checks for the headline compiler and parser theorems.
- `README.md`: user-facing current scope. `PLAN.md`: design rationale, proof architecture, blockers, and roadmap.

The source and target semantics are ordinary pinned Lake dependencies in `lakefile.toml`; inspect their actual definitions under `.lake/packages/yul-semantics` and `.lake/packages/evm_semantics` instead of guessing their AST, opcode, gas, or state APIs.

## Design invariants

Preserve these invariants unless the change deliberately redesigns them and updates all proofs and documentation:

- Compilation is `Option`-valued. Unsupported or unproved behavior must produce `none`; never broaden acceptance ahead of the proof.
- `opTable` is the supported-built-in boundary. An `.op` can exist in `Asm`, but lowering rejects it until `opTable` maps it to a proved target opcode.
- The compile-time variable layout `Γ : List Ident` is the source `VEnv` name order, innermost binding and operand-stack top first. `SimA.names` and `SimA.wimg` make this correspondence explicit.
- `off` in `compileExpr`/`compileArgs` counts temporary stack entries above variables, including pending arguments, return addresses, and return slots. A wrong `off` can silently select the wrong variable.
- Yul arguments evaluate right-to-left. This also leaves the first argument at the top in the order expected by `stepOp` and EVM opcode rules.
- Blocks hoist functions into a fresh function scope before compiling statements. Forward references and mutual recursion depend on `hoistInfos` matching `YulSemantics.hoist`.
- Locals live on the operand stack. Block exit and non-local control flow statically emit the exact `pop`s needed to restore the appropriate depth.
- Function calls use an opaque Asm code address, zeroed return slots, arguments, a symbolic entry jump, and `retRot`/`dynJump` on return. Return count is currently limited to 16.
- Classic `DUP1`-`DUP16` and `SWAP1`-`SWAP16` are the only active deep-stack operations. Reject deeper accesses; EIP-8024 operations are not active on any fork in the pinned target semantics.
- Every `Asm` constructor has a fixed lowered byte width in `Asm.size`. Phase B locates a suffix by `codeSize prog - codeSize suffix`; variable-width lowering breaks that invariant.
- Labels are generated with a counter but freshness is not threaded through proofs. `compileProgram` runs `wfCheck`, which must continue to guarantee unique definitions, defined references, and code size below `2^256`.
- Literal and label-address pushes are always `PUSH32`. Do not introduce shorter pushes as a local peephole change: instruction width, decode, jump positions, and proofs all depend on the current encoding.
- Phase A is intentionally byte-free and gas-free. Built-ins execute via the source `stepOp`; byte decoding, `UInt256` conversion, target state layout, and gas belong in Phase B.
- `StateMatch` currently relates memory, calldata, environment readers, and the executing account's persistent/transient storage. Extend it before proving operations that observe or mutate other state such as returndata, logs, account data, or code sizes.
- The correctness theorem is a forward simulation with an existential gas bound. Yul semantics has no gas, and target `Step` is not used as a deterministic equivalence.
- Normal source fall-through becomes the EVM's implicit past-the-end `STOP`; source halts must preserve the exact halt kind and payload.
- This repository must remain free of `sorry` and project-specific axioms. Do not use `axiom`, `unsafe`, or an opaque bridge to bypass proof obligations.

## Implementing compiler changes

Start by classifying the feature. The required files differ substantially for a new built-in, a new Yul construct, a new `Asm` primitive, an optimization pass, or object layout.

### Adding a Yul built-in that lowers to one EVM opcode

1. Confirm that the pinned `yul-semantics` `stepOp` models the operation and that the pinned `evm-semantics` opcode has an executable and relational rule and is available in the `.Osaka` fork. If either side lacks semantics, the operation cannot enter the verified fragment here.
2. For a pure word operation, prove a `conv_*` agreement lemma in `Value.lean`. Reuse the `unPure`, `binPure`, or `terPure` helpers in `OpStep.lean` when their stack/result shape fits.
3. For a read or state mutation, first extend `EnvMatch`/`StateMatch` and prove the representation-specific lemmas in `StateRel.lean`. Byte writes normally need explicit `ByteArray` layout/read-after-write lemmas, following `MemMatch.storeWord` and `BytesLemmas.lean`.
4. Add any dynamic memory or opcode cost to `opBound` and prove a target-state-independent upper bound. The bound may depend on source argument values, but not on arbitrary target state.
5. Add the operation's case to `opStep`, including arity inversion of source `stepOp`, opcode decoding/availability, the target `StepRunning` constructor, gas, stack shape, and preservation of every field in `StateMatch`/`FrameOK`.
6. Only after the proof case exists, add the `Op -> Operation` row to `opTable`. Its round-trip and fork-availability lemmas in `Decode.lean` are designed to discharge from a concrete successful `opTable` equation.
7. Add a focused program and differential `#guard` in `Examples.lean`, then see whether one or more Solidity interpreter baseline entries now pass.

Adding a direct built-in normally requires no Phase A case: `.builtin` already compiles to `.op`, and `AsmSem.AStep.op` uses the same source `stepOp`. It does require Phase B because `opTable` and `opStep` are what justify the concrete opcode.

Do not try to support `keccak256` merely by proving byte encoding: the two pinned semantics expose unrelated opaque hash functions. Operations unmodeled by source `stepOp` also cannot be justified by a source execution derivation. See `OpTable.lean` and `PLAN.md` for the current blockers before starting.

### Adding a Yul expression or statement form

The AST lives in `yul-semantics`; first verify the constructor and its source big-step rules there.

1. Specify the stack effect, scope effect, evaluation order, outcomes, and failure cases. Make the code generator reject invalid scope/control contexts and stack depths.
2. Add or change `compileExpr`, `compileArgs`, `compileStmt`, `compileStmts`, or `compileBlock` in `Compile.lean`. Thread `Γ`, `off`, `Φ`, `F`, `L`, and the label counter consistently. Preserve the termination measures of the mutual definitions.
3. Prefer expressing control flow with existing symbolic labels and existing `Asm` instructions. Draw the emitted layout in a module doc comment before proving it; these layouts serve as the proof blueprint.
4. In `SimAsm.lean`, add inversion lemmas for the successful compiler equation. Extend `Motive`, `SOut`, or `LOut` if the source result shape is new, then handle the corresponding constructor in `SimA.sim` using small reusable execution lemmas.
5. Use the successful final `wfCheck`/label `Nodup` fact with `findLabel_boundary`; do not introduce a parallel label-freshness proof unless the architecture is intentionally changing.
6. Add both compile-acceptance and differential-execution examples. Include nested scopes and non-local outcomes when relevant, not just the happy straight-line case.
7. Update the supported-fragment text in `README.md`, theorem doc comments, and the current design in `PLAN.md` if behavior or scope changed.

Phase A is a large induction, so keep additions local: compiler-equation inversion, a small Asm execution lemma, then one induction branch. Avoid unfolding the whole compiler repeatedly inside `SimA.sim`.

### Adding or changing an `Asm` instruction

This crosses both proof phases. Update all of the following:

1. `Asm` plus `Asm.size`, `defines`, and `references` in `Asm.lean`.
2. `lowerInstr` and `lowerInstr_length`; add decode/layout lemmas when the emitted `Instr` sequence has a new shape.
3. `AStep` or `AHalt` in `AsmSem.lean`, plus the suffix-preservation proof.
4. `StkOK`/`mapAVal`/`mapStk` in `LowerDefs.lean` if the instruction introduces a new stack-value kind or code address.
5. The corresponding `astep_sim` or `ahalt_sim` branch in `LowerCorrect.lean`, composing one or more target steps and their gas bounds.
6. Phase A compiler output and simulation helpers that emit/execute the new instruction.

Keep the lowered width fixed for each constructor. If that is impossible, redesign the program-location invariant and all affected decode/jump proofs explicitly rather than patching `Asm.size` to an approximate value.

### Adding a real optimization or normalization pass

There is currently no verified optimizer in front of the backend. A new source-to-source pass should be a separate total transformation with a theorem relating its input and output under `YulSemantics.Run` (including halt payloads, environments, and all outcomes it can encounter). Compose that theorem with `compile_correct`; do not silently call an unproved transformation from `compile`.

For an Asm-to-Asm optimization, preserve `AStep` behavior, symbolic control flow, stack shape, label well-formedness, and fixed-width location assumptions, or state and prove the replacement invariants. Bytecode peepholes are especially sensitive to jump addresses and valid `JUMPDEST` analysis.

Object parsing is not end-to-end object compilation. `ObjectCompile.lean`
provides the flat code-plus-data layout foundation and proves data-segment
consistency, but object-rooted source still requires layout-reference
resolution, nested-object layout, trailing-data backend correctness, and a
`RunObject`-to-EVM theorem. Do not make `compileSource` discard object
structure and compile only a nested block.

## Parser changes

The parser is a separate Lean library targeting the upstream AST:

- Public recursive grammar entry points have a fuel cap of 256.
- `parseBlock` and `parseObject` have canonical round-trip theorems. Preserve escape spelling and canonical-token behavior when changing their accepted grammar.
- `parseBlockCompat`/`parseObjectCompat` handle lossy Solidity compatibility such as hex literals and interleaved object/data items. Keep lossy normalization isolated and documented; it is outside the canonical theorem unless a new proof is added.
- Parsing is mostly syntactic. Do not claim that acceptance matches Solidity's name resolution, scope/control checks, built-in arity validation, or type checks.
- If canonical parser behavior changes, update its proof and `Checks.lean` expectations if and only if the genuine axiom footprint changes. A new axiom is not an acceptable update.

## Testing and verification

There is no separate `lake test` suite. `lake build` type-checks the libraries and executes the `#guard` checks imported from `Examples.lean`.

For a normal compiler change, run:

```sh
lake exe cache get
lake build
lake env lean Checks.lean
```

`lake exe cache get` is mainly needed on a fresh dependency build. For quick iteration, type-check the changed leaf module with `lake env lean path/to/File.lean`, but finish with the full build because downstream proofs and build-time differential guards are the actual integration check. Build the CLI with `lake build yulc`; run it without a native build using:

```sh
lake env lean --run YulParserMain.lean --parse-only program.yul
lake env lean --run YulParserMain.lean program.yul
```

Before finishing, scan changed Lean library/test sources for `sorry` and ensure `Checks.lean` still reports exactly `propext`, `Classical.choice`, and `Quot.sound` for the public theorems.

### Local differential examples

`YulEvmCompiler/Examples.lean` is the fastest end-to-end regression layer:

- `compileProgram` guards test Yul-to-Asm acceptance and label checking.
- `compile` guards also test lowering through `opTable`.
- `agreeOn` runs the source interpreter and assembled bytecode through `EVM.stepF`, then compares selected storage slots.
- `agreeReturn` compares exact return bytes for halting programs.

Use adequate interpreter and target fuel, assert that the EVM halted without exception, and compare every state component the feature affects. These executable checks support the proof; they do not replace it.

### Solidity syntax corpus

CI checks every `.yul` file under Solidity's `test/libyul/yulSyntaxTests` on the moving `develop` branch. The runner treats a fixture as an expected rejection when the section after `// ----` contains a comment diagnostic with `Error`; warnings remain expected successes. Because this parser is syntax-oriented, the corpus deliberately exposes semantic-validation differences too.

Run it against a local Solidity checkout with:

```sh
lake env lean --run scripts/CheckSoliditySyntaxTests.lean \
  /path/to/solidity/test/libyul/yulSyntaxTests \
  test/solidity-yul-syntax-known-mismatches.txt
```

`test/solidity-yul-syntax-known-mismatches.txt` is an exact, sorted set, not a skip list. The run fails if there is a new mismatch or if a listed mismatch has become stale. Review unexpected cases individually. Add an entry only for an understood, intentionally deferred difference; remove it as soon as the parser agrees.

### Solidity interpreter corpus

CI also attempts every fixture under `test/libyul/yulInterpreterTests`:

```sh
lake env lean --run scripts/CheckSolidityInterpreterTests.lean \
  /path/to/solidity/test/libyul/yulInterpreterTests \
  test/solidity-yul-interpreter-known-failures.txt
```

For each fixture, `checkFixture`:

1. parses the required memory, storage, and transient-storage dumps after `// ----`;
2. parses and compiles the brace-delimited source with `compileSource`;
3. assembles it and executes `EVM.stepF` in a concrete environment matching Solidity's fixed Yul interpreter defaults, with 100,000,000 gas and 100,000 instruction fuel;
4. rejects nontermination, remaining `.Running`, and EVM exceptions; and
5. exactly compares sorted nonzero state: memory as aligned 32-byte words, plus persistent and transient storage entries.

The harness installs compiled bytecode as the executing account's code, unlike Solidity's AST interpreter dummy code. Calldata, memory, and storage start empty. Consult `InterpreterFixture.initialState` before diagnosing environment-reader differences.

`test/solidity-yul-interpreter-known-failures.txt` is also an exact baseline: every fixture still runs, known failures are allowed, unexpected failures fail, and stale entries fail. A newly supported feature should normally remove baseline paths. Never update either baseline just to make CI green without explaining the semantic or unsupported-feature reason.

To reproduce CI's corpus checkout:

```sh
git clone --depth 1 --filter=blob:none --sparse --branch develop \
  https://github.com/argotorg/solidity.git /tmp/solidity
git -C /tmp/solidity sparse-checkout set \
  test/libyul/yulSyntaxTests \
  test/libyul/yulInterpreterTests
```

## Change discipline

- Keep imports layered; avoid making Phase A depend on EVM byte/gas modules.
- Prefer small named lemmas at representation boundaries over large tactic blocks in the end-to-end theorem.
- Match existing namespaces, theorem naming, module doc comments, and explicit stack/state shapes.
- Preserve unrelated working-tree changes.
- Update `README.md` when supported syntax/opcodes or commands change, and update `PLAN.md` when an architectural decision, blocker, or milestone changes.
- When a failure comes from a pinned upstream semantics definition, document the exact blocker rather than approximating different behavior locally.
