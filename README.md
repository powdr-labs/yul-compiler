# yul-evm-compiler

A **verified non-optimizing compiler for a fragment of Yul to EVM bytecode**,
written in Lean 4.

* Source semantics: [powdr-labs/yul-semantics] — the big-step relational
  judgment `YulSemantics.Run`/`Step` over the gas-free EVM dialect
  (`Value := BitVec 256`).
* Target semantics: [powdr-labs/evm-semantics] — the small-step relation
  `EvmSemantics.EVM.Step` and its big-step closure `Eval`, a real EVM with gas.

Both repos are ordinary Lake dependencies (same toolchain `v4.31.0`, same
Mathlib revision), so the correctness theorem quantifies over *both semantics as
they are* — nothing is re-encoded. See [`DESIGN.md`](./DESIGN.md) for the full
design, proof structure, and rationale.

Compilation goes through a **labeled-assembly intermediate layer**, so all
control-flow and calling-convention reasoning is byte- and gas-free, while all
gas/decode/layout arithmetic is a single generic per-instruction simulation:

```
Yul --compileStmts--> List Asm --lowerProg--> List Instr --assemble--> ByteArray
        (Phase A proof)          (Phase B proof)          (Decode lemmas)
```

Compilation is `Option`-valued: it **rejects** what it cannot yet verify
(`compile = none`) rather than emitting unverified code. Rejection is never
miscompilation.

## Building

```sh
lake exe cache get   # prebuilt Mathlib oleans
lake build           # builds both semantics deps + the compiler + proofs
lake env lean Checks.lean         # re-checks the axiom footprint
lake env lean --run YulParserMain.lean --parse-only program.yul
lake build yulc                   # CLI that emits compiled bytecode
```

`lake build` also executes the `#guard`/`#eval` differential checks in
`Examples.lean`. Requires the Lean toolchain pinned in
[`lean-toolchain`](./lean-toolchain) (managed by
[`elan`](https://github.com/leanprover/elan)).

## What is implemented

A non-optimizing compiler for programs with **variables, nested blocks, `if`,
`switch`, `for` loops (with `break`/`continue`), and user-defined `function`s
(with `leave`, recursion, calls, and up to 16 return values)**:

- `let` declarations (initialized or zeroed), single- and multi-variable
  assignments, built-in expression statements, `{ … }` scoping;
- `if` → `ISZERO; PUSH32 dest; JUMPI … JUMPDEST`;
- `switch` → a verified chain of literal comparisons and conditional jumps, with
  an optional `default` block;
- `for {init} c {post} {body}` with backward jumps; `break`/`continue` compile
  to statically-known `pop`s down to the loop scope plus a `jump`;
- `function f(ps) -> rs { body }` compiled inline (jumped over), called with a
  pushed return address (`pushLabel`) and a `dynJump` back; `leave` pops to the
  function frame and jumps to the epilogue; a `SWAP1 … SWAPk` rotation returns
  `k ≤ 16` values in source order.

Literals compile to `PUSH32`; a built-in call compiles its arguments
right-to-left (Yul's evaluation order, which puts the first argument on top of
the stack) followed by the built-in's opcode; a program that falls off the end
of its bytecode performs the EVM's implicit `STOP`, matching Yul's `.normal`
outcome. Variables live on the operand stack, mirroring the semantics' `VEnv`
exactly: reads compile to `DUP(off+idx+1)`, assignments to `SWAP(idx+1); POP`,
`let x := e` is free, and block exit pops the block's locals.

**Full static support.** The theorem covers both ordinary and static
(`STATICCALL`) frames with no carve-out — `FrameOK` no longer constrains
`permitStateMutation` at all. In a static frame every state-modifying built-in
the source forbids (`sstore`/`tstore`/`log0`–`log4`/`selfdestruct`,
value-bearing `call`, `create`/`create2`) halts with
`Exception .StaticModeViolation`, matching the source's `HaltKind.staticViolation`;
the value-free calls `callcode`/`delegatecall`/`staticcall` proceed, propagating
the static flag into the callee.

The object layer (`YulEvmCompiler/ObjectCompile.lean`) recursively compiles
sub-objects, resolves `dataoffset`/`datasize` to layout constants, emits a `STOP`
seam before embedded child/data bytes, and exposes real offset/size maps.
`compileObject_correct` proves the complete execution statement: every
`RunObject` derivation under the generated layout is simulated by the emitted
EVM bytecode. `compileObject_consistent` proves every direct data segment sits
at its recorded byte range.

`YulParser.parseSource` parses brace-delimited programs and object-rooted files
into the `yul-semantics` AST. `parseBlock` and `parseObject` have verified
canonical round-trip theorems (`parse_canon_block`, `parse_canon_obj`): accepted
input is preserved up to whitespace, comments, and number base, including string
escape spelling. A lossy compatibility fallback handles `hex"..."` literals and
interleaved sub-objects/data (intentionally outside the round-trip theorem).
`YulParser.compileSource` compiles either form to executable bytecode.

The **verified built-in set** is the domain of `opTable`
(`YulEvmCompiler/OpTable.lean`):

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

The pure word operations (including the signed `sdiv`/`smod`/`sar`/`signextend`)
and the local state operations are verified as flat single-op simulations, on
the same footing as `add`. **The CALL-, CREATE-, and `selfdestruct`-family
operations are different**: their correctness is *conditional on* the
`ExternalsRealized` hypothesis — see the next section.

## What is not (yet) done, and why

- **`gas`.** yul-semantics models `gas()` as a nondeterministic open-world
  oracle; verifying it needs a realization condition tying the chosen oracle word
  to the target frame's actual remaining gas. Until then it compiles to `none`.
  (`datasize`/`dataoffset` are also outside `opTable`, but only because the
  object compiler resolves them to layout constants at compile time rather than
  runtime opcodes.)
- **Open-world call/create coverage is conditional.** The
  CALL/CREATE/`selfdestruct` correctness is sound and general — the theorem
  quantifies over the external `ExternalCalls`/`ExternalCreates` relations and
  assumes an `ExternalsRealized` hypothesis: every source-admitted call/create
  response must be realized by a complete target `Steps` trace (with no
  restriction on intermediate call stacks, so arbitrary callee/init code, nested
  calls/creations, and reentrancy are covered). The interface is inhabited by a
  real EVM behavior, not just satisfiable in principle: besides the vacuous
  closed-world `ExternalsRealized.none`, the library proves the *genuinely
  non-empty* `ExternalsRealized.insufficientBalanceCall` — its relation admits
  the EVM's immediate-fail response for a value-bearing `call` the caller cannot
  afford (success flag `0`, empty return data, world unchanged), realized by a
  single concrete `StepRunning.callFail` step. That witness covers the
  insufficient-balance `.call` fail class only; a fully general model (arbitrary
  callee/init code with success-and-return) is still the client's responsibility,
  so end-to-end open-world call/create coverage remains conditional on supplying
  such a realization. This is a genuine distinction from the flat built-ins above.
- **Deep stack access.** Variable reads use up to `DUP16`, stores up to
  `SWAP16`, and functions return up to 16 values. Deeper accesses are *rejected*
  (`compile = none`), not miscompiled, because EIP-8024 (`DUPN`/`SWAPN`) is not
  activated on any fork modeled by evm-semantics. Lifting the restriction is a
  codegen-only change once the fork table activates EIP-8024, or a spilling pass.
- **Optimizer.** A verified `Optimizer.simplify` pass (constant folding +
  neutral-element identities, recursing through the whole program including
  function bodies) runs in front of the backend for **block-rooted** source
  programs (`compileSource`); it is a total source-to-source transformation proved
  semantics-preserving (`EquivBlock`) and composed with the backend via
  `Pass.optimize_then_compile_correct`. Reaching into function bodies rests on a
  locally-proved function-environment congruence (`Optimizer.FunCongr`). For
  **object-rooted** programs (Solidity's `--via-ir` artifacts), `compileSource`
  runs the pass on *every* code block of the tree — deploy and runtime — via
  `Optimizer.simplifyObject`. `simplifyObject_correct` proves the emitted bytecode
  correctly simulates the **original** object's resolved execution under the
  compiler's layout (the object analogue of `optimize_then_compile_correct`),
  bridged by a resolution congruence (`Optimizer.resolveSimplifyBlock_equiv`).
  `compile`/`compileObject` never silently call an unproved transformation.
- **Fork range.** The theorem fixes `fork = .Osaka`. Function/param/return names
  must be `Nodup`.
- **Gas is existentially bounded, not closed-form.** By design (yul-semantics is
  gas-free, evm-semantics charges gas), the guarantee holds for all sufficiently
  large initial gas; no closed-form gas equivalence is claimed.
- **Parser coverage.** The lossy `hex"..."`/interleaved-object compatibility
  fallback is outside the canonical round-trip theorems; typed identifiers and a
  verified compatibility path are future work.

## Tests

Correctness is carried by the theorems below. In addition:

- `YulEvmCompiler/Examples.lean` compiles sample programs at build time
  (`#guard`/`#eval`) — `switch`, multi-value returns and assignments, a `for`
  loop, a recursive function, an iterative Fibonacci over storage,
  CREATE/CREATE2 compilation, all five log arities with exact emitted contents,
  and a concrete `keccak256("abc")` — each run **differentially** through both
  the Yul interpreter and evm-semantics' `stepF` on the compiled bytecode, with
  affected state compared. It also compiles yul-semantics' own
  `FibExample.fibContract` all the way to bytecode and checks it returns the
  interpreter's bytes for several inputs.
- CI checks every `.yul` fixture in Solidity's `yulSyntaxTests` (accept/reject
  expectations), with an exact mismatch baseline.
- CI runs the Solidity Yul interpreter fixtures whose `EVMVersion` range includes
  Osaka: it compiles and executes each with evm-semantics and compares nonzero
  memory words and persistent/transient storage against the embedded dumps. The
  baseline lists the fixtures that do not pass, with reasons (unsupported ops,
  resource limits, and three object fixtures whose AST-interpreter dumps use
  synthetic hash offsets/sizes and a dummy code buffer rather than real compiled
  state).
- CI compiles every latest-fork fixture in Solidity's positive
  `yulOptimizerTests`, `objectCompiler`, and `evmCodeTransform` corpora
  (compilation acceptance), and separately runs a **behavioral differential
  against solc 0.8.35** over six identical pre-states per fixture (Solidity's
  default, one patterned state, and four path-seeded states covering calldata
  lengths 1/31/32/33 with varied call values, balances, and storage). It
  compares termination, return/revert bytes, returndata, nonzero memory, account
  state, logs, self-destructs, and storage refunds, and deliberately ignores
  exact bytecode, PCs, operand stacks, and remaining gas.

The differential baselines track **genuine behavioral mismatches vs solc** —
halt/memory/storage differences under the seeded states and a
return-stack-overflow divergence — alongside unsupported constructs, deep-stack
rejections, layout-introspection differences, and synthetic-value fixtures. Each
baseline is exact: a new failure or a stale entry fails CI. This is a
source-compatibility and behavioral check; it does **not** claim optimizer or
bytecode equivalence with solc. For `yulOptimizerTests` it compiles the original
source and does not reproduce the fixture's configured optimization step.

## The theorem

`YulEvmCompiler.compile_correct` (in `YulEvmCompiler/Correctness.lean`):

> If `compile prog = some is` and the Yul semantics runs `prog` from machine
> state `yst0` to `yst'` with outcome `o` (under external call/create relations
> whose responses are realized by complete target executions), then there is a
> gas bound `b` such that from **every** initial EVM state that matches `yst0`
> (`StateMatch`), executes `assemble is` (`FrameOK`), starts at `pc = 0` with an
> empty stack, and holds at least `b` gas, the EVM semantics reaches (`Steps`) a
> final state that matches `yst'` and halts the way `o` prescribes: `.Success`
> via the implicit `STOP` for `o = .normal`, or exactly the halt recorded in
> `yst'.halted` for `o = .halt`.

Its **remaining preconditions** are all honest scoping, not modeling gaps:
`fork = .Osaka`, an empty call stack (top-level frame), a non-precompile
executing address, `pc = 0`, an empty initial stack, and sufficient gas.
`FrameOK` does **not** constrain `permitStateMutation`, so static and non-static
frames are both covered (see "Full static support" above).

`compile_correct_eval` restates the conclusion through evm-semantics'
result-level big-step judgment; `compile_correct_withPayload` exposes the
returned/reverted payload bytes.

`YulEvmCompiler.compileObject_correct` lifts the same guarantee to recursively
compiled objects.

The proof is a **two-phase forward simulation**:

- **Phase A** (`SimAsm.lean`, `SimA.sim`): the Yul derivation is simulated by the
  byte-free, gas-free Asm machine. Jumps resolve labels to code suffixes;
  function environments are tracked by `FEnvOK`, established at each block via
  `hoist_ok`.
- **Phase B** (`LowerCorrect.lean`, `asteps_sim`/`arun_halt_sim`): each local Asm
  step maps to 1–3 EVM steps; a call or creation maps to a complete `Steps`
  trace. Existential gas bounds add along the execution.

`StateMatch` is comprehensive: memory (total function vs. zero-padded `ByteArray`)
and its active-word high-water mark, Yul's flat storage/transient storage to the
executing account's storage, calldata and executing code pointwise (with exact
lengths), every account's nonce/storage/transient/code/hashes through the account
map, historical block hashes, the source static flag against the target mutation
permission, ordered logs, ordered self-destruct records (address plus the
EIP-6780 `createdThisTx` bit), returndata byte-for-byte, and the configurable
Keccak oracle against the target hash primitive — all via the faithful injective
`conv : BitVec 256 → UInt256`. Gas is existentially bounded because yul-semantics
does not track execution gas.

The headline theorems check with no `sorry`. Their `#print axioms` footprint is
exactly the three standard classical axioms (`propext`, `Classical.choice`,
`Quot.sound`) and nothing else — the `ByteArray` facts used by `MSTORE` are all
genuine theorems (`writeBytes` upstream, the two `natToBytesPadded` lemmas in
`YulEvmCompiler.BytesLemmas`). `Checks.lean` pins that exact set in CI.

## Worked examples

`YulEvmCompiler/Examples.lean` compiles and differentially executes sample
programs at build time, including `switch`, multi-value returns and assignments,
a `for` loop, a recursive function, and an iterative Fibonacci over storage. It
also compiles yul-semantics' own `FibExample.fibContract` — the calldata/memory
Fibonacci contract proved correct upstream — all the way to bytecode and checks
that the compiled code returns the same bytes as the interpreter for several
inputs.

## License

Apache 2.0, matching the two semantics repositories.

[powdr-labs/yul-semantics]: https://github.com/powdr-labs/yul-semantics
[powdr-labs/evm-semantics]: https://github.com/powdr-labs/evm-semantics
