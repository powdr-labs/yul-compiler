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

## Current scope

A non-optimizing compiler for **straight-line programs with variables and
nested blocks**: `let` declarations (initialized or zeroed), single-variable
assignments, built-in expression statements, and `{ … }` scoping — no
user-defined functions and no control flow yet. Literals compile to `PUSH32`; a built-in call compiles its arguments
right-to-left (Yul's evaluation order, which also puts the first argument on
top of the stack) followed by the built-in's opcode; a program that falls off
the end of its bytecode performs the EVM's implicit `STOP`, matching Yul's
`.normal` outcome.

Variables live on the operand stack: the compile-time layout mirrors the
semantics' `VEnv` exactly. Reads compile to `DUP(off+idx+1)`, assignments to
`SWAP(idx+1); POP`, `let x := e` is free (the value stays put), and block
exit pops the block's locals. Because EIP-8024 (`DUPN`/`SWAPN`) is not yet
activated on any fork modeled by evm-semantics, accesses deeper than
`DUP16`/`SWAP16` are **rejected at compile time** (`compileProgram = none`);
lifting that restriction is a codegen-only change once the fork table
activates EIP-8024.

The verified built-in set (the domain of `opTable` in
`YulEvmCompiler/Compile.lean`):

| group      | ops |
|------------|-----|
| arithmetic | `add sub mul div mod addmod mulmod exp clz` |
| comparison | `lt gt slt sgt eq iszero` |
| bitwise    | `and or xor not byte shl shr` |
| stack      | `pop` |
| storage    | `sload sstore tload tstore` |
| memory     | `mload` |
| halting    | `stop return revert invalid` |

Everything else is rejected (`compile* = none`) — see `PLAN.md` for exactly
why each remaining op is deferred (four are plain proof debt; the rest are
blocked on upstream issues found during this work).

## The theorem

`YulEvmCompiler.compile_correct` (in `YulEvmCompiler/Correctness.lean`):

> If `compileProgram prog = some is` and the Yul semantics runs `prog` from
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

The correspondence `StateMatch` relates memory pointwise (total function vs.
zero-padded `ByteArray`), and Yul's flat storage/transient storage to the
executing account's storage. Gas is existentially bounded because
yul-semantics deliberately does not model gas. The proof is a forward
simulation over the Yul derivation; per-instruction facts live in
`OpStep.lean`, byte-level decoding facts in `Decode.lean`, and the
`BitVec 256` ↔ `UInt256` arithmetic agreements in `Value.lean`.

Both theorems check with no `sorry` and no extra axioms
(`#print axioms` → `propext`, `Classical.choice`, `Quot.sound`).

## Building

```sh
lake exe cache get   # prebuilt Mathlib oleans
lake build           # builds both semantics deps + the compiler + proofs
```

`YulEvmCompiler/Examples.lean` compiles a few sample programs at build time
(`#guard`/`#eval`), e.g. `sstore(0, add(1, 2)) return(0, 0)`.

## Roadmap

See `PLAN.md` for the full design, the upstream findings (EIP-8024
`DUPN`/`SWAPN` not yet activated on any modeled fork; `writeBytes` being a
`partial def` blocks all memory-write proofs; the two repos' distinct opaque
keccaks), and the milestone plan: variables via `DUPN`/`SWAPN` stack
scheduling, control flow via `JUMP`/`JUMPI`/`JUMPDEST`, user-defined
functions, objects, then verified optimization passes on the Yul side.

## License

Apache 2.0, matching the two semantics repositories.

[powdr-labs/yul-semantics]: https://github.com/powdr-labs/yul-semantics
[powdr-labs/evm-semantics]: https://github.com/powdr-labs/evm-semantics
