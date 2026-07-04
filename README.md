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
`if`, `for` loops (with `break`/`continue`), and user-defined `function`s
(with `leave`, recursion, and calls, single return value)**:

* `let` declarations (initialized or zeroed), single-variable assignments,
  built-in expression statements, `{ … }` scoping;
* `if` → `ISZERO; PUSH32 dest; JUMPI … JUMPDEST`;
* `for {init} c {post} {body}` with backward jumps, `break`/`continue`
  compiling to statically-known `pop`s down to the loop scope + a `jump`;
* `function f(ps) -> rs { body }` compiled inline (jumped over), called with a
  pushed return address (`pushLabel`) and a `dynJump` back; `leave` pops to
  the function frame and jumps to the epilogue.

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

Still out of scope: `switch` (an if-chain, mechanical), multi-value returns,
and the memory/hash/log/environment ops blocked upstream.

The verified built-in set (the domain of `opTable` in
`YulEvmCompiler/OpTable.lean`):

| group      | ops |
|------------|-----|
| arithmetic | `add sub mul div mod addmod mulmod exp clz` |
| comparison | `lt gt slt sgt eq iszero` |
| bitwise    | `and or xor not byte shl shr` |
| stack      | `pop` |
| storage    | `sload sstore tload tstore` |
| memory     | `mload` |
| halting    | `stop return revert invalid` |

Everything else is rejected (`compile = none`) — see `PLAN.md` for exactly
why each remaining op is deferred (four are plain proof debt; the rest are
blocked on upstream issues found during this work).

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
zero-padded `ByteArray`), and Yul's flat storage/transient storage to the
executing account's storage. Gas is existentially bounded because
yul-semantics deliberately does not model gas. Per-instruction facts live in
`OpStep.lean`, byte-level decoding facts in `Decode.lean`, and the
`BitVec 256` ↔ `UInt256` arithmetic agreements in `Value.lean`.

Both theorems check with no `sorry` and no extra axioms
(`#print axioms` → `propext`, `Classical.choice`, `Quot.sound`); `Checks.lean`
pins that axiom set in CI.

## Building

```sh
lake exe cache get   # prebuilt Mathlib oleans
lake build           # builds both semantics deps + the compiler + proofs
```

`YulEvmCompiler/Examples.lean` compiles a few sample programs at build time
(`#guard`/`#eval`), including a `for` loop, a recursive function, and an
iterative Fibonacci over storage — each run **differentially** through both
the Yul interpreter and evm-semantics' `stepF` on the compiled bytecode, with
storage compared. It also references yul-semantics' own `FibExample.fibContract`
(the calldata/memory Fibonacci contract proved correct upstream) to show it is
correctly *rejected* at lowering: `calldataload`/`mstore` are outside the
verified op set, so `compile` returns `none` rather than emit unverified code.

## Roadmap

See `PLAN.md` for the full design, the upstream findings (EIP-8024
`DUPN`/`SWAPN` not yet activated on any modeled fork; `writeBytes` being a
`partial def` blocks all memory-write proofs; the two repos' distinct opaque
keccaks), and the remaining milestones: `switch` and multi-value returns,
objects/`datacopy`/constructors, then verified optimization passes on the Yul
side.

## License

Apache 2.0, matching the two semantics repositories.

[powdr-labs/yul-semantics]: https://github.com/powdr-labs/yul-semantics
[powdr-labs/evm-semantics]: https://github.com/powdr-labs/evm-semantics
