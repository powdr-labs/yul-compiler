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
- [~] Phase 3 SimCall — all discrete step-lemmas landed:
      - [x] `compileFn_head_jumpdest` + `entry_isValidJumpDest` (`FnLayout`) —
        a function's recorded entry is a valid `JUMPDEST`, so the scaffold's
        `JUMP` to a callee fires (`jumpStep`).
      - [x] `lookupFun_single`, `find?_hoist_get?`, `lookupFun_realFt_corr`
        (`FnLayout`) — the dynamic funenv↔table bridge: a call the source
        resolves against `hoist yul prog` resolves in `compileProgF`'s table to
        an `FnInfo` with the same signature/body.
      - [x] `pushZerosSteps` (`FnProof`) — prologue return-slot zero-init.
      - [x] `popsSteps` (`FnProof`) — parameter drop.
      - [x] `calleeEpilogueSteps` (`FnProof`) — the whole return sequence
        `POP×n ; SWAP1..SWAPm ; JUMP`, composing `popsSteps` + `retSwapsSteps` +
        `jumpStep` end to end.
      - [ ] the `SimCall` combinator itself — compose prologue
        (`pushStep` retaddr, `pushZerosSteps`, args-sim, `pushStep` entry),
        `jumpStep` to entry (via the `ProgLayout` embedding +
        `entry_isValidJumpDest`), the callee body (body-sim), and
        `calleeEpilogueSteps`. The args-sim and body-sim hypotheses are supplied
        by Phase 4's `simF`, so `SimCall` is finished together with it.
- [ ] Phases 4–5 — the `simF` induction + `SimCall`, then turn on acceptance by
      generality (procedures → +params → +single → +multi-return).

  **Key architectural finding (before writing `simF`):** the existing `SimE` /
  `SimSP` relations are *code-quantified* — `∃ b, ∀ code preIs post …, code =
  mkCode (… ++ is ++ post) → …`. That is exactly what makes them
  position-independent and composable for the function-free fragment, but it
  also means they **cannot express a call**: the callee body lives inside the
  universally-quantified `post`, so the relation has no way to know it is there
  or to jump to it. Therefore `simF`'s statement/expression motive must be
  relative to a **fixed** whole-program `code` that satisfies `ProgLayout`
  (which locates every callee), rather than the code-quantified `SimSP`.

  Concretely Phase 4 needs:
    1. a code-fixed simulation relation `SimSPC code pcc yst V is yst' V'`
       (like `SimSP` but with `code` fixed and a `ProgLayout code` hypothesis),
       plus its composition lemmas (`comp`, embargo of `pushStep`/etc. lifted to
       fixed code) — most existing step lemmas already take a concrete `code`,
       so they lift directly;
    2. the `SimCall` combinator, now a wiring of the proven step-lemmas —
       `pushStep`(retaddr) · `pushZerosSteps` · args-sim · `pushStep`(entry) ·
       `jumpStep`→entry (`ProgLayout` embed + `entry_isValidJumpDest`) ·
       callee body-sim · `calleeEpilogueSteps` · land on the scaffold `JUMPDEST`
       (`isValidJumpDest_of_split`); the args-sim and body-sim come from the
       `simF` IH;
    3. a funenv↔table invariant threaded through `simF` so every *compiled*
       call resolves in the source to the matching `decl`
       (`lookupFun_realFt_corr` gives the top-level case; nested/shadowing
       function definitions must be excluded — the compiler already fails to
       resolve calls to non-top-level functions, so the accepted fragment has
       `funs` agreeing with `realFt`).

  All the mechanical lemmas these three steps consume are already proven and
  committed; Phase 4 is the architectural assembly.

  **Phase 4 progress (`FnSim.lean`):**
    - [x] `SimSPC` — the code-fixed statement simulation + `SimSP.toSimSPC`
      bridge + `SimSPC.comp` + `SimSPC.nil`.
    - [x] `calleeRunProc` — **the callee half of a procedure call is proven**:
      run entry `JUMPDEST` → body (`SimSPC` over the empty region) → return
      `JUMP`, reaching `retaddr` with the caller stack restored. This is the
      first machine-checked "a function call executes correctly" (no
      params/rets).
    - [x] `callerReachEntry` — the prologue `PUSH retaddr ; PUSH entry ; JUMP`
      reaches the callee entry with `retaddr` on top.
    - [x] **`SimCallProc`** — the *whole* procedure call scaffold as a `SimSPC`:
      prologue → callee entry `JUMPDEST` → body (`SimSPC`) → return `JUMP` →
      landing `JUMPDEST`. The first fully machine-checked "a function call is
      correct." Landing validity via `isValidJumpDest_boundary` +
      `toNat_ofNat_of_lt`/`codeSmall`.
    - [x] `compileExprF_extends` / `compileStmtF_extends` (`FnExtends.lean`) —
      the function-aware compiler produces exactly what the function-free one
      does on the call-free fragment. With `SimSP.toSimSPC` this carries every
      `Correctness.sim` result into `SimSPC`, so `simF` only has to *add* the
      call case (`SimCallProc`).
    - [x] case combinators (all committed, `sorry`-free): `simSPC_nil`/
      `simSPC_cons` (sequences), `simF_call` (procedure call scaffold via
      `SimCallProc`), `SimSPC_ifTrue` + `simSP_ifFalse` (conditionals, via
      `compileStmtF_cond_inv`), `SimSPC_block` (blocks, via
      `compileStmtsF_suffix`), `stmtF_reuse` + `compileExprF_rev` (call-free
      leaves reuse `Correctness.sim`), `compileStmtF_outcome` (a compiled body
      can't `break`/`continue`/`leave`), and the `FunAgree` funenv invariant.
    - [x] **`simF`** — the whole induction over the source `Step` producing
      `SimSPC` for `compileStmtF` (`FnSimInduction.lean`). `callOk` →
      `simF_call` with the callee body-sim from the body sub-derivation IH
      (this discharges recursion) and the embedding/`JUMPDEST`-validity from
      `ProgLayout`+`lookupFun_realFt_corr`; every other rule uses the
      combinators above; `switch`/`for`/`break`/`continue`/`leave` compile to
      `none` (vacuous).
    - [x] **`simProg_correct`** — the end-to-end top-level theorem: a source
      `Run` to a normal outcome is simulated by the assembled bytecode running
      to `.Success` (inverts the top-level `block`, runs `simF` on the body,
      extracts the EVM `Steps` from the `SimSPC`, terminates on the explicit
      `STOP` after `main` via the new `stopExplicitStep`).

  **Milestone reached — procedures with recursion, machine-checked.** `simF`
  and `simProg_correct` are `sorry`-free and depend only on
  `[propext, Classical.choice, Quot.sound]`. The proven fragment (Phase 5a):
  top-level 0-param/0-ret procedures, recursion allowed, calls in statement
  position, with `let`/`assign`/`exprStmt`/`block`/`if`/`funDef` bodies. The
  sound-fragment side conditions are explicit hypotheses of `simProg_correct`:
  `hproc` (top-level functions are procedures), `hcons` (blocks hoist no
  functions ⇒ no nested/shadowing definitions), `hsize` (entries in range).

  Remaining (Phase 5b–5d, future work): discharge `simProg_correct`'s
  hypotheses directly from `compileProgF prog = some fullIs` (the
  `compileProgF_layout`↔`realFtOf` entries bridge), then the `+params` /
  `+single-return` / `+multi-return` generalisations (`pushZerosSteps`,
  args-sim via `SimEC`, `popsSteps`, `retSwapsSteps`, `calleeEpilogueSteps`).

  Note: "implemented and working" is already done — `compileProgF` is executable
  and `FunctionsExamples` runs recursion/procedures/multi-return/nested calls on
  the evm-semantics EVM with the expected results. The remaining work is purely
  the machine-checked proof (`SimCallProc` → `simF` → top-level theorem).
