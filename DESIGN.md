# Yul → EVM compiler — Design

A **non-optimizing compiler from a fragment of Yul to EVM bytecode**, written
in Lean 4, with a machine-checked proof that compilation preserves semantics.
This document describes the correctness statement, the two semantics it plugs
into, the repository architecture, the intermediate representations and
compilation scheme, the two-phase proof, the verified built-in set, and — at
the end — what is and is not proven, and why.

## Overview

The compiler connects two independent, pinned formalizations:

* **Source semantics**: [powdr-labs/yul-semantics] — the big-step relational
  judgment `YulSemantics.Run`/`Step` over the gas-free EVM dialect
  (`YulSemantics.EVM.evm`, `Value := BitVec 256`).
* **Target semantics**: [powdr-labs/evm-semantics] — the small-step relation
  `EvmSemantics.EVM.Step` (and its big-step closure `Eval`), a real 120-opcode
  EVM over `UInt256 := Fin (2^256)` words, with gas.

Both repos pin the same toolchain (`leanprover/lean4:v4.31.0`) and the same
Mathlib revision, so this project depends on both as ordinary Lake packages and
states one theorem quantifying over both semantics as they are — nothing about
either is re-encoded.

Compilation is `Option`-valued: it *rejects* what it cannot yet verify
(`compile = none`) rather than emitting unverified code, so the repository stays
free of `sorry` and project-specific axioms while coverage grows. Rejection is
never miscompilation.

## The correctness statement

For a program `prog` in the supported fragment with `compile prog = some code`,
the headline theorem `compile_correct` (`YulEvmCompiler/Correctness.lean`) says:

> If the Yul big-step semantics runs `prog` from machine state `yst0` to `yst'`
> with outcome `o` (`Run EVM.evm prog yst0 V' yst' o`), then there is a gas
> bound `b` such that from **every** initial EVM state `s0` that matches `yst0`
> (`StateMatch`), executes the assembled bytecode `assemble code` (`FrameOK`),
> starts at `pc = 0` with an empty stack, and has `b ≤ s0.gasAvailable`, there
> is an execution `Steps s0 s'` ending in a done state (`callStack = []`) whose
> world state matches `yst'` and whose halt matches `o`/`yst'.halted`.

`compile_correct_eval` restates the conclusion through evm-semantics'
result-level big-step judgment (`Eval s0 .success`, resp. `Eval s0 (resultOf hk)`);
`compile_correct_withPayload` exposes the returned/reverted payload bytes.

### Remaining preconditions of the statement

The theorem holds under these frame-level side conditions (`FrameOK`), all of
which are honest scoping of the guarantee rather than modeling gaps:

* `fork = .Osaka` — all supported opcodes are active there; parameterizing over
  a range of compatible forks is a later generalization;
* the call stack is empty (`callStack = []`) — this is the top-level frame;
* the executing address is not a precompile;
* `pc = 0` and the initial operand stack is empty;
* at least `b` gas is available.

The frame's mutation permission is **not** constrained: `FrameOK` says nothing
about `permitStateMutation`, so both ordinary (`= true`) and static (`= false`)
frames are covered with no carve-out.

### Design decisions baked into the statement

* **Forward simulation (∃ target run), not equivalence.** The target `Step`
  relation is mildly non-deterministic (overlapping exception rules such as
  `outOfGas` vs. `stackUnderflow` may both fire), so "the compiled code *may*
  produce the matching result" is what is provable. Combined with the source
  derivation this is the standard compiler-correctness direction.
* **Gas is existentially bounded.** yul-semantics deliberately does not model
  gas; evm-semantics charges it. The theorem therefore holds *for all
  sufficiently large initial gas*. Internally the simulation invariant is: each
  compiled fragment, run from any matching state with `gas ≥ bound(D)` (a bound
  computed from the *source derivation* `D`, since memory-expansion costs depend
  on the argument values pinned by `D`), consumes at most `bound(D)` gas. Bounds
  compose by addition across sequencing. The SSTORE EIP-2200 sentry
  (`gas ≤ 2300 → OOG`) is absorbed into the per-op bound.
* **Match relation** `yst ∼ s` between `YulSemantics.EVM.EvmState` and
  `EvmSemantics.EVM.State` (`StateMatch`). It is comprehensive; via the faithful
  injective coercion `conv : BitVec 256 → UInt256` it relates:
  - memory: `yst.memory a = s.memory[a]?.getD 0` pointwise;
  - active memory: `yst.activeWords = s.activeWords`, so zero-valued accesses
    that expand memory and `msize` agree even when the memory bytes do not
    change;
  - storage / transient storage: Yul's single flat storage/transient store maps
    to the *executing account's* storage in the target account map, pointwise;
  - every account's nonce, persistent/transient storage, code bytes, lengths,
    and hashes through the account map (so hidden callee/CREATE state cannot vary
    between matching worlds);
  - calldata and executing code pointwise, with exact lengths; returndata
    byte-for-byte with its exact length;
  - self/balance, external code and its EIP-161-aware hash, historical-block
    hash;
  - ordered logs (each emitter address, topics, data) and ordered scheduled
    self-destructs (address plus the EIP-6780 `createdThisTx` bit);
  - environment/header readers, the source static-context flag against the
    target frame's mutation permission (`static = !permitStateMutation`), and
    the configurable Keccak oracle against the target hash primitive; blob and
    block-hash fields.
* **Static frames.** In a static frame the state-modifying built-ins the source
  forbids (`sstore`/`tstore`/`log0`–`log4`/`selfdestruct`, value-bearing
  `call`, `create`/`create2`) halt with `Exception .StaticModeViolation`,
  matching the source `HaltKind.staticViolation`; the value-free
  `callcode`/`delegatecall`/`staticcall` proceed.
* **Implicit STOP.** A Yul `.normal` outcome means the compiled code runs off
  the end of the bytecode; `Decode.decodeAt` yields an implicit `STOP` there
  (Yellow-Paper zero padding), so the target halts with `.Success` — i.e.
  straight-line Yul that falls through behaves like `stop()`.

## The two semantics it plugs into

**yul-semantics** (`YulSemantics.*`):

- `Ast.lean`: `Expr Op` (lit / var / builtin / call), `Stmt Op`, `Outcome`.
- `Dialect.lean`: dialect interface; `BuiltinResult` (`ok rets st` / `halt st`).
- `Dialect/EVM.lean`: the `Op` enum covering the full user-facing Yul EVM
  dialect — arithmetic/comparison/bitwise/`clz`, `keccak256` (via the
  configurable `ExecEnv.keccakOf` oracle), `pop`, memory
  (`mload/mstore/mstore8/mcopy/msize`, with an active-memory high-water mark),
  storage and transient storage, calldata/code/returndata reads and copies,
  environment readers, world-state reads, `log0`–`log4`, the object-data ops
  (`dataoffset`/`datasize`/`datacopy`), and halting ops including deterministic
  Osaka/Cancun `selfdestruct`. CALL- and CREATE-family operations use the
  open-world `ExternalCalls`/`ExternalCreates` relations; `gas` is a
  nondeterministic oracle in that open-world relation and is deliberately absent
  from deterministic `stepOp`. Static-context write protection is represented by
  `ExecEnv.static`.
- `BigStep.lean`: a single indexed inductive `Step D funs V st code res`
  covering expressions, argument lists (**right-to-left**), statements,
  sequences, and loops; `Run` for whole programs. Induction over a derivation is
  a standard `induction … with`.

**evm-semantics** (`EvmSemantics.*`):

- `EVM/State.lean`: `State extends SharedState` with `pc`, `stack : List UInt256`,
  `halt : HaltKind`, `callStack`.
- `EVM/Step.lean`: `StepRunning` (one constructor per opcode; premises for the
  decoded op, `cost ≤ gasAvailable`, and stack shape; post-state subtracts the
  exact cost), `StepReturn`, and the wrapper `Step` (a `running` guard: not
  halted and not a precompile frame).
- `EVM/BigStep.lean`: `Steps` (reflexive-transitive closure), `Eval s r` (ends
  in a done state, projected through `State.toResult`).
- `EVM/Decode.lean`: `decodeAt code pc`; past-the-end ⇒ implicit `STOP`; PUSH
  immediates via `bytesToBigEndianNat`; DUPN/SWAPN immediates folded into the
  `Operation` value.
- `Data/UInt256.lean`: a `Fin (2^256)` wrapper with per-opcode arithmetic.
- Storage is `Std.HashMap`; the world is `AccountMap`; memory is a `ByteArray`
  with zero-padded reads (`readPadded`, `readWord`) and `writeBytes` for writes.

Two facts about the pinned target semantics shape the compiler:

1. **EIP-8024 (`DUPN`/`SWAPN`/`EXCHANGE`) is not activated on any modeled fork.**
   `Operation.availableInFork` returns `false` for all three on every fork
   (Frontier … Osaka), so bytes `0xe6..0xe8` always halt with
   `InvalidInstruction`. The raw backend therefore uses classic
   `DUP1`–`DUP16` and `SWAP1`–`SWAP16`, and rejects accesses beyond that range.
   The production source entry point can instead invoke the proved guarded
   spilling fallback described below. Activating EIP-8024 upstream would let a
   later code-generation extension remove this depth restriction without that
   source rewrite and scratch contract.
2. **`MachineState.writeBytes` is a total, kernel-transparent `def`**, so
   memory-write proofs are possible. `mstore`'s `MemMatch` preservation rests on
   the upstream read-after-write lemma
   `EvmSemantics.MachineState.writeBytes_getElem?_getD` and two big-endian
   indexing facts about `natToBytesPadded` proved locally in
   `YulEvmCompiler.BytesLemmas`; no axioms are involved. `mstore8` uses a
   low-byte write lemma; `mcopy` an overlap-safe intermediate-buffer
   correspondence. Reads (`readPadded`/`readWord`) are total, so `mload`,
   `return`, and `revert` are verified and compose with `mstore`.

## Architecture of this repo

```
YulEvmCompiler/
  Asm.lean          -- labeled control-flow IR + label resolution/lowering
  AsmSem.lean       -- byte-free, gas-free semantics of labeled assembly
  Compile.lean      -- Yul AST → labeled assembly (Option-valued)
  SimAsm.lean       -- Phase A: Yul execution → assembly execution
  Instr.lean        -- tiny byte-level IR: PUSH32 or one-byte operation
  Decode.lean       -- assembled-code decoding and jump-destination lemmas
  LowerDefs.lean    -- assembly/EVM configuration correspondence
  LowerCorrect.lean -- Phase B: assembly execution → EVM execution
  OpTable.lean      -- exact verified built-in set
  Value.lean        -- BitVec 256 ↔ UInt256 operation agreements
  StateRel.lean     -- memory/storage/byte-region/environment correspondence
  OpStep.lean       -- per-op EVM simulation lemmas and gas bounds
  BytesLemmas.lean  -- local natToBytesPadded byte-indexing facts
  Correctness.lean  -- end-to-end compile_correct / compile_correct_eval
  ObjectCompile.lean -- object/data layout + consistency and execution proofs
  ObjectResolve.lean -- dataoffset/datasize resolution preserves derivations
  Examples.lean     -- compile-time and differential execution checks
YulParser/
  Canon.lean        -- independent canonical token stream for round-trip proofs
  Atoms.lean        -- identifiers and literal parsers
  Expr.lean         -- fuel-bounded expression parser
  Stmt.lean         -- statements, block entry point, and round-trip theorem
  Obj.lean          -- object entry point and round-trip theorem
  Compat.lean       -- lossy Solidity hex/interleaved-object compatibility path
  Validate.lean     -- strict-assembly scope/signature/object validation
  Source.lean       -- common parsed-and-validated block/object entry point
  Compile.lean      -- block/object source-to-bytecode connection
scripts/
  Check*.lean       -- Solidity corpus expectation/differential runners
test/
  *-known-*.txt     -- exact corpus baselines
```

The parser targets the lossy, single-sorted `yul-semantics` AST. Its grammar
entry points use at most 256 units of recursive fuel. The statement and
ordered-object parsers have verified canonical round-trip theorems
(`parse_canon_block`, `parse_canon_obj`), including escape-preserving strings.
`parseSource` also has a deliberately lossy compatibility fallback for
`hex"..."` expression literals and interleaved object/data items, followed by
strict-assembly validation (lexical/identifier rules, scopes and signatures,
control-flow placement, built-in calls, switches, object/data references,
immutables, and version-gated names). CI exercises Solidity's complete
`yulSyntaxTests` directory.

## The IRs and the compilation scheme

Compilation uses two IRs. `Asm` carries symbolic labels, classic stack
operations, Yul built-ins, and function return addresses. Every constructor has
a fixed lowered width:

```
inductive Asm
  | push | op | dup (Fin 16) | swap (Fin 16) | pop
  | label | jump | jumpi | pushLabel | dynJump
```

Because widths are fixed per constructor (`push`/`pushLabel` 33, `jump`/`jumpi`
34, others 1), the byte position of any *suffix* `c` of the program is
`codeSize prog - codeSize c` — independent of label resolution. `lowerProg`
resolves labels and maps `Asm` to the deliberately tiny byte-level `Instr`
(`push UInt256 | op Operation`), which `assemble` encodes as EVM bytecode.
Literal and label-address pushes are always `PUSH32`.

Label well-formedness (`WFProg`: `defs` nodup, `refs ⊆ defs`, `codeSize` small)
is **decidable and checked**, not proved: the compiler runs `wfCheck` on its
output and rejects on failure, so the proof reads label uniqueness and
definedness off the successful check with no freshness bookkeeping.

The compiler covers literals, variables, built-ins, calls, nested blocks, zero-
and value-initialized `let`, multi-value declarations and assignments, `if`,
`switch`, `for`, `break`/`continue`, functions, recursion, and `leave`.
Functions may return up to 16 values. Arguments are evaluated right-to-left,
matching Yul semantics (this also leaves the first argument on top of the
stack). Variables live on the operand stack: the compile-time layout `Γ` mirrors
the semantics' `VEnv` exactly; reads compile to `DUP(off+idx+1)`, assignments to
`SWAP(idx+1); POP`, `let x := e` is free, and block exit pops the block's
locals.

The emitted layouts for the control constructs:

* **Blocks** are compiled two-pass: first hoist the block's `funDef`s into a new
  function scope (matching the semantics' `hoist`, so forward references and
  recursion work), then compile statements under it.
* **`for {init} c {post} {body}`** emits `init`, then `label Lcond: <c>; iszero;
  jumpi Lexit`, the body under a loop context `{brk Lexit, cont Lpost}`,
  `label Lpost: <post>`, `jump Lcond`, and `label Lexit:` with pops back to the
  pre-`init` depth. `break`/`continue` in `post` are rejected (no loop context
  there).
* **`break`/`continue`** are `pop × (depth delta); jump L.brk/L.cont`.
* **`function f(ps) -> rs { body }`** is compiled inline, jumped over: a prologue
  jumps past the body; the body runs with `Γf = ps ++ rs` and a function context;
  the epilogue pops params, rotates the `k ≤ 16` return values into source order
  (`SWAP1 … SWAPk`), and `dynJump`s back to the caller.
* **`leave`** is `pop × (depth delta); jump F.exit`.
* **`call f args`** pushes a return address (`pushLabel`), zeroes the `k` return
  slots, evaluates arguments right-to-left, and `jump`s to the entry label;
  execution resumes at the return label with the results in place.
* **`switch c cases default`** evaluates `c` once, keeps the scrutinee on the
  stack, and emits a chain of `DUP1; PUSH case; EQ; ISZERO; JUMPI next` blocks;
  a matched case pops the scrutinee, runs its block, and jumps to a common end;
  fall-through runs the optional default.

## Proof structure

Compilation and its proof share the same split:

```
Yul --compileStmts--> List Asm --lowerProg--> List Instr --assemble--> ByteArray
        (Phase A proof)          (Phase B proof)          (Decode lemmas)
```

Supporting the two phases:

1. **Decode/layout lemmas** (`Decode.lean`). For `code = pre ++ assemble is ++ post`
   and `pc = pre.size`, `decodeAt code pc` returns the head instruction's
   operation (and, for `push`, the immediate). All `ByteArray` index arithmetic
   is isolated here.
2. **Value agreement** (`Value.lean`). `conv : BitVec 256 → UInt256` (a
   `toNat`-based injection) with one independent lemma per supported op,
   including the signed operations `sdiv`, `smod`, `sar`, `signextend`. An op
   enters the supported set exactly when its lemma exists.
3. **State correspondence** (`StateRel.lean`), plus preservation lemmas for each
   state-touching op.

**Phase A** (`SimAsm.lean`, `SimA.sim`): Yul big-step ⇒ Asm execution. This
contains *all* control-flow and environment reasoning and is **gas-free and
byte-free** — jumps go to labels via `findLabel`, positions never appear. It
inducts over the Yul derivation. The fragment-execution shapes (`ASimE`/`ASimS`
and the non-local-outcome shape `ASimNL`) are placed by list appends
(`prog = pre ++ asm ++ c`); function environments are tracked by `FEnvOK`,
established at each block via `hoist_ok`; the statically-emitted pops realize the
semantics' `restore` chain for `break`/`continue`/`leave`.

**Phase B** (`LowerDefs.lean` + `LowerCorrect.lean`, `asteps_sim`/`arun_halt_sim`):
Asm execution ⇒ EVM `Steps` over the assembled bytecode. This is a *generic*
per-instruction simulation, proved once by induction over the Asm trace; all gas
accounting, decode/layout arithmetic, and jumpdest analysis live here. The
simulation invariant relates an Asm configuration `⟨c, σ, yst⟩` to an EVM state:
`c` is a suffix of `prog`, `s.pc` is the suffix's byte position, `s.stack` is the
pointwise image of `σ` (`conv` on words, resolved label address on code
addresses), and `FrameOK`/`StateMatch` hold. Each local `AStep` maps to 1–3 EVM
steps with an existential gas bound; bounds add along the trace.

`Correctness.lean` composes the phases and caps a fall-through `.normal` with the
implicit `STOP`.

### Object execution

`ObjectResolve.lean` proves that replacing `dataoffset`/`datasize` references
with the generated layout values preserves every Yul derivation. The backend
simulation admits the explicit `STOP` seam plus recursively embedded child/data
payload, and `compileObject_correct` composes them into the `RunObject`-to-EVM
theorem: every `RunObject` derivation under the generated layout is simulated by
the emitted EVM bytecode, covering layout-reference resolution, the executable
prefix, normal fall-through through the `STOP` seam, exact source-level halts,
and the trailing payload used by `codesize`/`codecopy`/`datacopy`.
`compileObject_consistent` separately proves that every direct data segment sits
at its recorded byte range.

### Open-world CALL- and CREATE-family correctness

The source and Asm semantics are parameterized by `ExternalCalls` and
`ExternalCreates`. Phase B separates local opcodes (which keep their one-step
`opStep` proof) from external instructions. The CALL family consumes
`CallsRealized` and `create`/`create2` consume `CreatesRealized`; each supplies a
complete target `Steps` trace from immediately before the opcode to the restored
caller/creator after return. Only the trace endpoints are constrained (`FrameOK`,
`StateMatch`, next `pc`, and the returned flag/address word); intermediate states
are unrestricted, so a trace may execute unknown runtime or init code, perform
arbitrarily nested calls and creations, and re-enter the caller/creator.
`StateMatch` relates the full account projection for every address, so hidden
callee state and CREATE collision inputs cannot vary between matching worlds.
`compile_correct` quantifies over both external relations and assumes realization
for every response they admit (`ExternalsRealized`). The empty closed-world
model `ExternalsRealized.none` provides the vacuous realization (its relation
admits no response).

The interface is also demonstrably inhabited by a real EVM behavior, not just
vacuously: the library proves `ExternalsRealized.insufficientBalanceCall`, a
genuinely non-empty witness. Its `insufficientBalanceCalls` relation admits, for
a value-bearing `call` whose caller balance is below the transferred value,
exactly the EVM's immediate-fail response — success flag `0`, empty return data,
world unchanged — and `CallsRealized.insufficientBalance` realizes it with a
single concrete `StepRunning.callFail` step (no callee frame, no `StepReturn`
resume), discharging the real interface: matching `StateMatch`/`FrameOK` at both
endpoints, `pc + 1`, the `0` result word on the stack, and the existential gas
bound. The insufficient-balance trigger is keyed on the caller `selfBalance`,
which is observable from the source state, so `callFail`'s `balance < value`
precondition is derivable; the other silent-fail trigger, the 1024-frame depth
limit, is invisible to a source-state relation (the source `EvmState` has no
depth). This witness therefore covers the insufficient-balance `.call` fail class
only. Fully general realization (arbitrary callee/init code with
success-and-return, nested calls, reentrancy) remains the client's
responsibility, so end-to-end open-world call/create coverage is still
conditional on supplying such a model.

## The verified built-in set

The single source of truth is `opTable` in `OpTable.lean`. The verified
fragment is the **domain of `opTable`**: every EVM built-in **except**

* `gas` — modeled by yul-semantics as a nondeterministic open-world oracle; it
  needs a realization condition tying the chosen oracle word to the target
  frame's remaining-gas counter before it can enter the fragment; and
* `datasize`/`dataoffset` — resolved to layout constants at compile time by the
  object compiler, not runtime opcodes.

Ops outside the domain compile to `none`. The covered set, by group:

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

`keccak256` uses the `EnvMatch.keccak` oracle agreement (with a proved concrete
`targetKeccakOracle` for executable tests). `log0`–`log4` preserve an ordered
correspondence over emitting address, topics, and memory-slice data, including
active-memory expansion. `selfdestruct` follows the pinned Osaka/Cancun EIP-6780
behavior: the opcode transfers (or, for a same-address beneficiary, conditionally
retains/burns) the balance, records the address plus its `createdThisTx` bit, and
halts; actual account deletion is a transaction-finalization step outside this
frame-level theorem. CALL-/CREATE-family operations use the open-world
realization interface above.

## What is proven

The headline theorems check with no `sorry`. Their `#print axioms` footprint is
exactly the three standard classical axioms `[propext, Classical.choice,
Quot.sound]` and nothing else — the `ByteArray` facts used by `MSTORE` are all
genuine theorems. `Checks.lean` pins that exact set for each theorem in CI:

* `compile_correct`, `compile_correct_withPayload`, `compile_correct_eval`
  (`Correctness.lean`) — end-to-end compiler correctness for the supported
  fragment;
* `compileObject_correct`, `compileObject_consistent`,
  `compiled_constructor_returns` (`ObjectCompile.lean`) — object execution,
  data-segment consistency, and the canonical `datacopy`/`return` constructor;
* `parse_canon_block`, `parse_canon_obj` (`YulParser`) — canonical parser
  round-trip theorems;
* `CallsRealized.complete_allows_reentrancy` and
  `CreatesRealized.complete_allows_initcode_reentrancy` — that the open-world
  realization interface admits reentrant traces.

## The optimizer specification

The verified backend is non-optimizing, while the production source entry point
runs a verified Yul→Yul pipeline in front of it. The repository fixes, once and
formally, what every such pass must prove. `YulEvmCompiler/Optimizer/` is
split so the contract and its implementations stay separate — the same
audited-surface-vs-artifact distinction the spec closure already makes:

* **`Optimizer/Spec/`** — the *stable contract*; an auditor reads this and nothing
  under `Implementation/`.
  * **`Spec/Pass.lean`** — a pass is a total transform
    `run : Block D.Op → Block D.Op`; it is **sound** when
    `Sound D run := ∀ b, EquivBlock D b (run b)`, and the `Pass` structure bundles a
    transform with that proof, so a value of `Pass` *is* a verified optimizer — there
    is no way to build one without discharging `Sound`. `EquivBlock` (from the pinned
    `YulSemantics.Equiv`) is *pointwise* big-step equivalence: identical final
    environment, final state (hence halt payloads), and outcome from every
    configuration — strictly stronger than observational equivalence, hence stable
    under any context. Passes compose (`Pass.comp`, unit `Pass.id`) by transitivity,
    a pipeline is one pass (`Pass.ofList`), and `Pass.preservesRun` extracts the
    whole-program `YulSemantics.Run` guarantee.
  * **`Spec/Backend.lean`** — the payoff. `Pass.optimize_then_compile_correct`
    composes any sound pass with `compile_correct`: the bytecode compiled from the
    *optimized* program correctly simulates the *original* program's Yul semantics.
    This is the `Run`-interface composition `AGENTS.md` prescribes; no backend proof
    is reopened.
  * **`Spec/Observe.lean`** — the *observational tier*, additive and (so far)
    outside the pinned audit roots. `ObsEquivBlock` compares runs only on what a
    caller or the transaction can see — the committed (`committedState`) storage,
    transient storage, logs, self-destructs, returndata, halt payload, and world
    projections — quantifying away raw memory, `msize`, and the final variable
    environment, under every external oracle. This is the contract for passes
    `EquivBlock` provably cannot express (dead-binding removal, scratch-memory
    reuse, dead stores before `revert`). The strong tier embeds
    (`ObsEquivBlock.ofEquiv`), `ObsPass` composes, and
    `ObsPass.optimize_then_compile_correct` restates the backend payoff
    observationally: the compiled optimized program reaches a state matching a
    Yul state with the *same run observables* as the source's. Admitting an
    `ObsPass` into the production pipeline is a deliberate, human-reviewed
    weakening of the headline guarantee; the theorem is ready for that review.
* **`Optimizer/Core/`** — the incrementally introduced optimizer IR, behind the
  unchanged `Pass` boundary.
  * **`Core/Basic.lean`** — the first intrinsically checked fragment: ANF values
    are literals or variables carrying membership in an explicit context; pure
    EVM operations carry their input arity in the type; and their arguments are
    values, making nested/effectful arguments unrepresentable. `ingest` is
    deliberately partial, while `ingest_emit` proves that successful ingestion
    erases to exactly the original Yul expression. The current simplifier leaves
    unsupported syntax—including calls and recursive calls—unchanged; later
    passes may use the same partial boundary with their own total fallback policy.
  * **`Core/Rule.lean`** — a shallow rewrite bundled with its `EquivExpr` proof.
    The generic first-match engine is proved once for any ordered rule list, so
    optimizer policy can change without changing the engine proof.
  * **`Core/Subst.lean`** — closed-term instantiation of parameter contexts:
    substituting caller arguments for a Core term's context is first-occurrence
    name lookup (deliberately mirroring `VEnv.get`), so no capture, renaming, or
    freshness discipline exists to prove anything about. `valueEval` reflects the
    `Step` judgment on value-shaped expressions (variables/non-string literals)
    into `Option`-equational reasoning; `substEmit_value_correspond` is the heart
    of the inliner's β argument — a substituted value evaluates in the caller
    environment exactly as the original evaluates in the callee frame.
* **`Optimizer/Implementation/`** — concrete passes, *not* part of what an auditor
  must read: because every `Pass` is sound by construction, a pass is trusted the
  moment it type-checks against the spec.
  * **`Implementation/Identity.lean`** — the identity pass, the first inhabitant:
    returns its input unchanged, sound by reflexivity (definitionally `Pass.id`). A
    real pass replaces `run` with a transformation and `sound` with an equivalence
    proof of the same shape.
  * **`Implementation/FunCongr.lean`** — the **function-environment congruence**
    upstream defers: `FunsRel` (function environments related scope-by-scope, with
    equal signatures and `EquivBlock` bodies), `Step.funs_congr` (a `Step`
    derivation transports across `FunsRel`), and `EquivBlock.of_stmts_funs` (a block
    congruence that lets the hoisted scope change). This is what lets a pass rewrite
    *inside* `funDef` bodies; it is reusable by any future pass.
  * **`Implementation/Simplify.lean`** — the first *real* pass: local **constant
    folding** (a pure built-in on all-literal arguments → the folded literal) and
    **neutral-element identities** (`add(x,0)`, `mul(x,1)`, `and(x,2²⁵⁶−1)`, … → `x`,
    with the variable kept on the right-hand side so the rewrite is sound on every
    environment), plus **literal control-flow selection** (`if` → chosen/empty
    block and `switch` → selected case/default). It also removes the
    always-false `if iszero(eq(x,x))` validator residue while evaluating and
    discarding the original condition, preserving its unbound-variable
    stuckness. Flat pure applications are now
    ingested into Core and run through proof-carrying fold/neutral rules. This
    replaces the old raw-AST rewrite driver: syntax outside the current Core
    fragment is simply unchanged.
    It recurses through the whole
    program **including `funDef` bodies**
    (via `FunCongr`); only a `for`-loop's `init` is left untouched (it is executed
    *and* hoisted, so it needs a `for`-specific congruence — a small follow-up).
    `compileSource` runs it on block-rooted programs; `IDEAS.md` logs the running
    list of passes tried and to try.
  * **`Implementation/InlineHelpers.lean`** — scope-aware inlining of pure
    expression-body helpers, classified through the Core boundary
    (`helper?` ingests the body into `Term params 1` and certifies distinct,
    all-read parameters and string-freeness). A bare-parameter body
    (`r := p`) rewrites `f(e)` to `add(e, 0)` for any single argument — the
    arity-preserving fence the old identity pass used; a pure built-in body
    (`r := op(…)`) rewrites a flat call `f(v₁, …, vₙ)` to the body with
    arguments substituted (`Term.substEmit`) — closed-term instantiation, with
    a β equivalence (`helper_call_subst_iff`) whose right-hand side consults
    *no* function environment. Recursive helpers, effectful or multi-statement
    bodies, and non-flat call sites keep the ordinary verified call. The
    bidirectional `Step` simulation follows hoisted ordered scopes, closure
    environments, shadowing, and `for` initializer scopes; classified helpers
    are fixed points of the transform, so call sites may consult the callee's
    original body after the whole program has been rewritten. The `litOK` flag
    selects between full classification (block path) and the
    resolution-stable, variables-only fragment (object path).
  * **`Implementation/InlineHelpersResolve.lean`** — proves strict commutation
    between layout resolution and helper inlining in its resolution-stable
    mode, including invariance of classification and of the rewrite condition
    under resolution: resolution can neither create nor destroy the bare-var
    shapes that mode accepts, whereas it *does* create literals (from
    `dataoffset`/`datasize`), which is exactly why the object path must not
    classify literal-carrying bodies or literal call arguments.
  * **`Implementation/HoistCalls.lean`** — normalizes the direct unary nested
    call shape `x := f(g(args))` when both helpers pass the existing
    stack-pressure gate. The inner call is evaluated into a globally fresh
    block-local temporary, preserving Yul's right-to-left evaluation order;
    the following `FreshenCalls → InlineCalls` stages can then inline both
    sites. Its pointwise statement proof covers normal results and halts, and
    its object-path proof transports the normalization through layout
    resolution.
  * **`Implementation/DeadPure.lean` / `DeadResults.lean`** — perform scoped
    dead-code elimination while retaining the strong `EquivBlock` contract.
    `DeadPure` removes unused singleton bindings whose right-hand sides are
    provably total and state-preserving (including `sload`). `DeadResults`
    recognizes the `let result; { ... result := value }` residue produced by
    statement-level inlining and removes the whole adjacent region when its
    result is unused, its locals and assignments are confined to the region,
    and its suffix cannot observe a changed function environment. Both passes
    have bidirectional source-semantics simulations and layout-resolution
    closure for object compilation.
  * **`Implementation/StorageForward.lean`** — forwards cheap values from
    literal-key `sstore` operations to later `sload`s. The cache stores only
    literals, variables, and `add(variable, literal)`; aliasing stores and
    stateful or joining control flow clear it. Assignments to known-bound
    variables establish and rebind matching facts using the pre-assignment
    value; nested blocks export facts after filtering dependencies on their
    direct declarations, matching the variables removed by `restore`. Loop
    post/body blocks remain separate optimization regions.
    `StorageForwardSound.lean` proves the bidirectional state-and-environment
    simulation, including the block declaration-frame invariant, and
    `StorageForwardResolve.lean` supplies the object-layout congruence by
    leaving layout-sensitive regions unchanged.
  * **`Implementation/StackLayout.lean` / `StackLayoutSound.lean`** — the smart
    fallback for classic-stack pressure. A Sethi--Ullman-style scheduler
    right-associates `add` spines, preserving the exact right-to-left leaf
    order even for state-changing or halting subexpressions. A structured
    liveness scan then colors a singleton local onto an earlier reachable
    block-local slot when the old value is dead, replacing `let y := e` by
    `x := e` and consistently renaming `y`'s remaining live range. The proof is
    a bidirectional big-step simulation over source/target variable
    environments, including nested scopes, functions, loops, every outcome,
    and exact block restoration.
  * **`Implementation/MemorySpill*.lean`** — the last-resort classic-stack
    fallback. `MemorySpillSelect` accepts only a consistent literal
    `memoryguard(n)`, rejects `msize`, recursive call graphs, malformed
    signatures, invalid selected-binding scopes, and partial tuple groups,
    then allocates word-aligned cells by
    lexical interference and active call-path need. Sibling scopes and sibling
    callees reuse addresses; a caller's live cells sit above the largest direct
    callee requirement. The rewrite covers locals, parameters, returns,
    assignments, `leave`, loops, and calls. Its simulation uses a guarded Yul
    dialect in which the marker raises the free-memory boundary, relates source
    and target states by equality outside the reserved interval, and proves the
    same committed run observables. Resolution lemmas and a plan-indexed object
    theorem allow spilled and ordinary optimized nodes to share one recursive
    object layout. Because the spilling candidate is tried only after every
    existing candidate fails, previously emitted bytecode is unchanged.
  * **`Implementation/Pipeline.lean`** — composes the verified stages
    (`optimizerPipeline` for blocks, `objectPipeline` for object code blocks,
    applied recursively over the tree), with the full original-object
    execution theorem `optimizerPipelineObject_correct`.
  * **`Implementation/ObjectPass.lean`** — the object path. `simplifyObject` (in
    `Simplify`) runs the pass on *every* code block of an object tree (deploy and
    runtime); `compileSource` uses it for object-rooted programs.
    `simplifyObject_correct` proves the emitted bytecode correctly simulates the
    **original** object's resolved execution under the compiler's layout — the object
    analogue of `optimize_then_compile_correct`. The bridge over the object
    compiler's layout-coupling (code length ↔ baked-in offsets) is the **resolution
    congruence** `ResolveCongr.resolveSimplifyBlock_equiv`
    (`EquivBlock (resolve L b) (resolve L (simplify b))`), proved because
    expression rewrites are disjoint from `dataoffset`/`datasize` resolution;
    resolution is structurally the identity on every Core term; and
    resolving switch cases commutes with literal case selection.

The soundness obligation and its congruence machinery live upstream in
`YulSemantics.Equiv`/`YulSemantics.Rewrites`; this repo supplies the pass
abstraction, the identity instance, and the backend composition. All of it checks
with the same `[propext, Classical.choice, Quot.sound]` footprint and no `sorry`.

## The audited specification boundary

`Checks.lean` pins what the proofs are trusted *modulo* (the axiom base).
`SpecClosure.lean` pins the dual: the **specification** the theorems are stated
*in terms of* — the minimal set of declarations a human must read and agree with
to believe the guarantees say what they should. It walks each headline theorem's
*statement* (never its proof), so the hundreds of preservation lemmas drop out
automatically; what remains is the match relations (`StateMatch`, `FrameOK`,
`HaltMatch`, …), the outcome maps (`resultOf`), the AST/target data types, the
external-call model (`ExternalsRealized`), and the entry points of the two
pinned semantics the guarantee quantifies over.

The extraction is emitted to [`SPEC.md`](./SPEC.md) (a manifest plus a tiered
boundary diagram) and its compact signature is pinned by a `#guard_msgs` block,
exactly as `Checks.lean` pins the axiom set. CI (`lake env lean SpecClosure.lean`
plus a `git diff` on `SPEC.md`) fails if a declaration enters or leaves the
audited surface, or an audited declaration's meaning changes — but **not** when
the compiler algorithm or any proof changes. That is the intended contract for
automated refactoring: code and proofs may change freely; the audited spec is
the fixed point that must be re-approved by a human when it moves.

When a change to the specification is intended, a maintainer runs
[`scripts/update-spec.sh`](./scripts/update-spec.sh), which regenerates `SPEC.md`
and re-pins `SpecClosure.lean` in one step; the resulting diff is the audit
artifact to review. The trust-boundary files (`SpecClosure.lean`, `SPEC.md`,
`Checks.lean`, the updater, the workflow, and the semantics pins) are guarded by
[`.github/CODEOWNERS`](./.github/CODEOWNERS) and flagged human-approval-only in
`AGENTS.md`, so an automated agent cannot re-pin a spec change to approve it.

This is a "does nothing it shouldn't" guarantee. The complementary "does
everything it should" side — that compilation is not vacuously rejecting
programs — is not part of the spec closure; it is enforced separately by the
Solidity differential corpora and their checked-in baselines (below and in
CI), which must stay in sync as coverage grows.

## What is not done, and why

* **`gas`.** yul-semantics models `gas()` as a nondeterministic open-world
  oracle; entering the verified fragment needs a realization condition tying the
  chosen oracle word to the target frame's actual remaining gas. Until then
  `gas` compiles to `none` (safe partiality, not miscompilation).
* **Open-world call/create coverage is conditional.** The CALL/CREATE/selfdestruct
  correctness is real and general, but it is *conditional on* the
  `ExternalsRealized` hypothesis — it requires every source-admitted call/create
  response to be realized by a real target `Steps` trace. Two models are
  exhibited in-repo: the vacuous `ExternalsRealized.none`, and the genuinely
  non-empty `ExternalsRealized.insufficientBalanceCall` (the insufficient-balance
  `.call` fail class, realized by a real `StepRunning.callFail` trace — see the
  open-world section above). A fully general model is still the client's job, so
  end-to-end open-world coverage remains conditional on supplying one.
* **Deep stack access.** The raw backend uses up to `DUP16` for variable reads
  and `SWAP16` for stores; functions return up to 16 values. A raw deeper
  access is *rejected* (`compile = none`), not miscompiled, because EIP-8024
  (`DUPN`/`SWAPN`) is not activated on any modeled fork. The production source
  entry point first uses
  the verified smart layout fallback described above, then the guarded memory
  spilling fallback when a safe scratch reservation is available. Irreducible
  frames without that contract still need EIP-8024 activation upstream.
  Independent unsupported operations such as `gas`, immutables, and live
  linker-symbol values are not accepted merely because spilling succeeds.
* **Optimizer.** A verified `Simplify → InlineIdentity → Simplify` pipeline runs
  in front of the backend for block-rooted
  `compileSource` inputs. The spec every pass must meet is fixed and inhabited
  (see *The optimizer specification* above): a sound `Optimizer.Pass` is a total
  source-to-source transform proved semantics-preserving (`EquivBlock`) and
  composed with `compile_correct`. Object-rooted inputs run the same pipeline on
  every deploy/runtime code block; resolver congruence connects the optimized
  artifact to the original resolved object execution. `compile`/`compileObject`
  never silently call an unproved transformation.
* **Fork range.** The theorem fixes `fork = .Osaka`; parameterizing over a range
  of compatible forks is a later generalization.
* **Gas is existential, not closed-form.** By design (yul-semantics is gas-free,
  evm-semantics charges gas), the guarantee is "for all sufficiently large
  initial gas". No closed-form gas equivalence is claimed.
* **Parser coverage.** The lossy `hex"..."`/interleaved-object compatibility
  fallback is intentionally outside the canonical round-trip theorems; typed
  identifiers and a verified compatibility path are future work.

Structural side conditions that are enforced rather than deferred: function and
parameter/return names must be `Nodup`, and the top-level frame conditions of
`FrameOK` (empty call stack, non-precompile address, Osaka fork) hold at entry.

## Tests

`YulEvmCompiler/Examples.lean` compiles sample programs at build time
(`#guard`/`#eval`) — including `switch`, multi-value returns and assignments, a
`for` loop, a recursive function, an iterative Fibonacci over storage,
CREATE/CREATE2 compilation, all five log arities, and a concrete
`keccak256("abc")` — and runs each **differentially** through both the Yul
interpreter and evm-semantics' `stepF` on the compiled bytecode, comparing the
affected state. It also compiles yul-semantics' own `FibExample.fibContract` all
the way to bytecode and checks it returns the interpreter's bytes for several
inputs.

CI additionally runs, against exact baselines that honestly track unsupported
constructs, deep-stack rejections, recursion/resource divergence,
synthetic-value fixtures, and genuine behavioral mismatches:

* Solidity's `yulSyntaxTests` (accept/reject expectations);
* the Solidity Yul interpreter fixtures (memory/storage/transient dumps
  compared exactly against compiled-bytecode execution);
* Solidity's positive `yulOptimizerTests`, `objectCompiler`, and
  `evmCodeTransform` corpora (compilation acceptance); and
* an independent behavioral differential against solc 0.8.35 over six seeded
  pre-states per fixture, comparing termination, return/revert bytes,
  returndata, nonzero memory, account state, logs, self-destructs, and storage
  refunds. It deliberately does **not** compare exact bytecode, PCs, operand
  stacks, or remaining gas: this is a source-compatibility and behavioral check,
  not a claim of optimizer or bytecode equivalence.

[powdr-labs/yul-semantics]: https://github.com/powdr-labs/yul-semantics
[powdr-labs/evm-semantics]: https://github.com/powdr-labs/evm-semantics
