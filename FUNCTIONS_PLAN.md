# Verifying the function calling convention

The codegen for user-defined functions (`YulEvmCompiler/Functions.lean`, the
caller-side-zeroing convention) is implemented and validated by execution on
the evm-semantics EVM. This plan tracks turning that into a *machine-checked*
correctness result against `YulSemantics.Run`, done in stages that each keep
the build green and `sorry`-free, with the compiler accepting a construct only
once it is proven.

## Convention recap

```
call   x₁..xₘ := f(a₁..aₙ):
  caller: PUSH retaddr; PUSH 0 (×m); <a₁..aₙ right-to-left>; PUSH entry_f; JUMP; JUMPDEST
  callee: JUMPDEST(entry_f); <body as block, layout params++rets>;
          POP(×n); SWAP1;…;SWAPm; JUMP
layout: main ; STOP ; f₁ ; f₂ ; …   (functions reached only by JUMP)
```
Entry stack `= vimg(params.zip argvals ++ bindZeros rets) ++ [retaddr] ++ σ`,
so the body reuses the existing variable/block machinery with a bare
`JUMPDEST` prologue.

## Phase 1 — Foundational, self-contained lemmas (no new framework)

1. **`jumpStep`** — executing an embedded unconditional `JUMP` to a
   statically-valid `JUMPDEST` target moves `pc` to the target, stack `= rest`.
   Mirrors `jumpiTakenStep`; uses `StepRunning.jump` + `isValidJumpDest_boundary`.
   *(first item)*
2. **`retSwaps` correctness** — `SWAP1;…;SWAPm` sends
   `[r₁,…,rₘ, ret] ++ σ` to `[ret, r₁,…,rₘ] ++ σ`. A clean induction on `m`
   over `List.exchange`; the rotation is already confirmed numerically.
3. **Layout arithmetic** — `PUSH32` is fixed-width, so a program's compiled
   length is independent of the concrete entry/return-address values; the
   two-pass `entryPositions` place each function body at a known offset.

## Phase 2 — Whole-program layout invariant

4. **`ProgLayout code prog`** — `code` decomposes as
   `main ++ [STOP] ++ f₁ ++ …`, each `fᵢ` is `compileFn` of its definition at
   its entry position, and each `entry_fᵢ` is a valid `JUMPDEST` in `code`
   (via `isValidJumpDest_boundary`). Plus a **function-environment
   correspondence** relating the source `hoist`ed `FScope` to the compile-time
   `FnTable`, so `lookupFun` at any call site agrees with the compiled entry.

## Phase 3 — Call/return simulation (the crux)

5. **`SimCall`** — the call fragment `Steps` from the call site: set up
   retaddr+zeros+args, `JUMP` to `entry_f`, run the callee body (its simulation
   supplied by the induction hypothesis on the *body sub-derivation* — this is
   how recursion is handled), `POP`/reshuffle/`JUMP` back to the retaddr
   `JUMPDEST`, leaving the `m` results on top. Consumes `ProgLayout` +
   `jumpStep` + `retSwaps` + the body IH.

## Phase 4 — Integrate into the `sim` induction

6. Add the source rules: `funDef` (no-op), `block` with `hoist`, `leave`
   (early return), and `callOk`/`callHalt`/`callArgsHalt`; plus multi-`let` /
   assign-of-call binding the `m` results. The whole program is
   `ExecStmt [] [] st₀ (.block prog)`, so the top-level theorem threads
   `ProgLayout` through.

## Phase 5 — Turn on compiler acceptance, by generality

Each sub-stage flips the compiler from `none` to accepting-and-proven, and is
its own green commit:

- **5a** procedures (0 params, 0 rets), recursion allowed;
- **5b** + parameters;
- **5c** + a single return value;
- **5d** + multiple return values (needs the `retSwaps` reshuffle from 1.2).

## Status

- [x] Codegen implemented + execution-validated (`Functions.lean`, committed).
- [ ] Phase 1.1 `jumpStep` — **in progress**.
- [ ] everything else.
