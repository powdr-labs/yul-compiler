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
- [x] Phase 1.1 `jumpStep` (`OpStep.lean`).
- [x] Phase 1.2 `retSwapsSteps` return-value reshuffle (`FnProof.lean`).
- [x] Phase 1.3 layout arithmetic: position/entry length-independence at every
      codegen level — `length_assembleBytes_{replicate_push,callScaffold}`,
      `FnTable.SigEq`, and `compile{ExprF,ArgsF,CallStmt,StmtF,StmtsF,Fn}_lenSig`
      (`FnProof.lean`). The `entryPositions` offset arithmetic (a small pure
      computation over these lengths) folds into Phase 2's `ProgLayout`.
- [~] Phase 2 `ProgLayout` — **in progress** (`FnLayout.lean`):
      - [x] `entryPositions_{nil,cons,length}` — the two-pass entry-offset
        recursion (induct over the function list head-first).
      - [x] `sigEq_dummy_real` — pass-1 (dummy entries) and pass-2 (real
        entries) tables are `FnTable.SigEq`, so the Phase-1.3 `*_lenSig`
        lemmas transfer pass-1 lengths to pass-2 lengths.
      - [ ] `ProgLayout code prog`: decompose `compileProgF` output as
        `main ++ [STOP] ++ fnCodes.flatten`, show each `fnCodes[i]` sits at
        its recorded `entryᵢ` (offset-match via the two lemmas above +
        `compileFn_lenSig`/`compileStmtsF_lenSig`), and each `entryᵢ` is a
        valid `JUMPDEST` (`isValidJumpDest_boundary`).
      - [ ] funenv↔`FnTable` correspondence: relate the source `hoist prog`
        (`FScope`/`FDecl`) to the compile-time `collectFns`/`realFt`, so
        `lookupFun [hoist prog] fn` agrees with `realFt.get? fn`.
- [ ] Phases 3–5 — SimCall, integrate into `sim` (extend `Motive` to the
      `FnTable` compiler), turn on acceptance by generality. These extend the
      core simulation framework and are the largest remaining pieces.
