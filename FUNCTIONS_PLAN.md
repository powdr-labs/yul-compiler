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
- [x] Phase 2 `ProgLayout` (`FnLayout.lean`):
      - [x] `entryPositions_{nil,cons,length}` — two-pass entry-offset recursion.
      - [x] `sigEq_dummy_real` — pass-1/pass-2 tables are `FnTable.SigEq`.
      - [x] offset machinery — `entryPositions_getElem?`,
        `length_assembleBytes_flatten`, `flatten_split`,
        `assembleBytes_flatten_embed`.
      - [x] `fnCodes_lens_eq` + `mapM_option_{getElem?,length}` — pass-1 =
        pass-2 function code lengths.
      - [x] **`ProgLayout` / `compileProgF_layout`** — from
        `compileProgF prog = some fullIs`: the pass-2 `mainCode` is the prefix,
        and every `ft.get?`-resolved function's compiled body is embedded at
        exactly its recorded entry byte-position.
      - [x] `hoist_eq_collectFns` — static funenv↔table correspondence: the
        source's `hoist yul prog` equals the `collectFns` table (up to
        `FDecl`/tuple packaging).
      - Deferred to Phase 3 (needs the threaded funenv): the *dynamic*
        `lookupFun [hoist prog] fn` ↔ `realFt.get? fn` correspondence, plus
        `JUMPDEST`-validity of entries at the call site (via
        `isValidJumpDest_boundary` on the `ProgLayout` embedding).
- [~] Phase 3 SimCall (`FnLayout.lean`) — ingredients landed:
      - [x] `compileFn_head_jumpdest` + `entry_isValidJumpDest` — a function's
        recorded entry is a valid `JUMPDEST`, so the scaffold's `JUMP` to a
        callee fires (`jumpStep`).
      - [x] `lookupFun_single`, `find?_hoist_get?`, `lookupFun_realFt_corr` —
        the dynamic funenv↔table bridge: a call the source resolves against
        `hoist yul prog` resolves in `compileProgF`'s table to an `FnInfo` with
        the same signature/body, so the compiled callee is the one the source
        runs.
      - [ ] the `SimCall` combinator itself — the call fragment `Steps`: push
        retaddr + `m` zeros + args, `JUMP` to entry, run the callee body via the
        body simulation hypothesis, `POP` params, `retSwaps`, `JUMP` back. This
        composes the above + `jumpStep` + `retSwapsSteps` + `SimE`/`SimSP`, and
        is co-designed with Phase 4 (which supplies the body hypothesis).
- [ ] Phases 4–5 — integrate into `sim` (a new `simF` induction over the source
      `Step` threading the `FnTable` + `ProgLayout`, extending `Motive` to the
      `compileStmtF` compiler; recursion via the body sub-derivation IH), then
      turn on compiler acceptance by generality (procedures → +params → +single
      → +multi-return). Largest remaining pieces; reworks the core simulation.
