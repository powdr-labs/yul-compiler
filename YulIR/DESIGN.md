# YulIR — an experimental optimizer IR for the Yul→EVM compiler

## Why

Optimizing Yul directly, and proving those optimizations correct against the
`yul-semantics` big-step judgment, is hard: expressions, effects and halting are
entangled, variables are named+mutable with scoped shadowing, and the meta-theory has
no `funDef` congruence. This experiment tests whether a small, ANF, structured IR makes
optimizations easier to write and (later) to prove, while producing EVM bytecode
competitive with the existing (solc-comparable) Yul optimizer.

**Goal:** IR optimizer performance comparable to solc's Yul optimizer.

## Pipeline

```
Yul  ──ofYul──▶  YulIR  ──optimize──▶  YulIR  ──toYul──▶  Yul  ──(verified backend)──▶  EVM
     (trusted)          (this work)          (erasure)         (YulEvmCompiler.compile)
```

`ofYul`/`toYul` are trusted (unproven) today; `toYul` is a structural **erasure**, so IR
optimizations are measured as real EVM code-size/gas changes through the existing verified
backend. Semantic soundness of `ofYul∘toYul` and of `optimize` is checked with the
`yul-semantics` interpreter (`YulIR/CheckBaseline.lean`), not yet proven.

## IR (`YulIR/Ast.lean`)

- **ANF**: every built-in/call argument is an `Atom` (literal or variable); nested
  expressions are lifted to `let`-temporaries. Fixes evaluation order syntactically.
- **Right-to-left** argument flattening in `ofYul` preserves Yul's observable arg order.
- **Structured control, no `for`-init**: `loop post body` ≙ `for {} 1 { post } { body }`,
  the condition folded into `body` as `if iszero(c) { break }`.
- **Named** variables (erasure to Yul is trivial). The intrinsically-scoped `Var Γ`
  refinement (à la `Optimizer.Core.Term`) is deferred to proof time.

## Passes (`YulIR/Optimize.lean` = `optimize`)

Order: `uniquify` → (`valueNumber` → `structural` → `deadCode`) ×2.

| Pass | File | What | Provability notes |
|---|---|---|---|
| Uniquify | `Uniquify.lean` | α-rename every declaration to a globally fresh name; removes shadowing | α-renaming; behaviour-preserving |
| Simplify | `Simplify.lean` | local constant folding (via dialect `stepOp`) + algebraic identities | per-`Rhs`, local; folding delegates to the semantics |
| ValueNumber | `ValueNumber.lean` | const/copy propagation, folding across `let`s, CSE — tracks only *immutable* values so no invalidation is ever needed | forward, monotone; immutability = never an `assign` target |
| Structural | `Structural.lean` | dead-branch removal (`if 0`), constant `switch` selection, `if 1`→block, empty-block/if removal | local, per-statement rewrites |
| DeadCode | `DeadCode.lean` | remove unused pure bindings (global check under unique names), to a fixpoint | pure ⇒ no observable effect |

### Design decisions of note

- **CSE is kept on despite growing code on some categories** (`equalStoreEliminator`,
  `unusedStoreEliminator`): on a stack machine, reusing a value via a copy extends its live
  range and adds DUP/SWAP shuffling. A later **rematerialization / cost model** (and
  gas-weighted, not size-weighted, accounting on expensive reused ops) is expected to make
  CSE net-positive. See `ValueNumber.recordLet`.
- **Soundness by immutability**: value numbering only tracks variables that are never
  reassigned, so tracked facts never go stale — the key trick that keeps the pass simple and
  (later) provable without dataflow invalidation lemmas.

## Measuring

`current` = today's `YulEvmCompiler.Optimizer.optimizerPipeline` (solc-comparable, the target).

- **Correctness gate** (CI, fast): `YulIR/CheckBaseline.lean` — round-trip and `optimize`
  both preserve interpreter behaviour over `YulIR/Corpus.lean`.
- **Optimization tracking** (CI, drift-robust): `scripts/YulIRCorpus.lean check` over
  Solidity's `yulOptimizerTests`, per optimizer-step category, gated on a source-fingerprinted
  `test/yulir-corpus-size-baseline.txt`. Columns: `current` / `ir-noopt` / `ir-opt`.
- **Behaviour sweep** (local, slow): `scripts/YulIRCorpus.lean behaviour <dir>` — IR-opt
  vs current bytecode over the whole corpus (`compareBytecode`). Step-cap/gas-bound diffs are
  classified separately from real observable divergences.

Run in the interpreter (`lake env lean --run …`); a native `lean_exe` would be faster at
runtime but requires compiling the whole mathlib closure with the C backend (~13 min), so it
is reserved for CI-cached heavy runs, not local iteration.

## Roadmap toward parity

Biggest remaining `ir-opt` vs `current` gaps and the passes that close them:

- [ ] **Unused-assignment / dead-store elimination** (`unusedAssignEliminator`,
      `unusedStoreEliminator`): backward liveness on locals; remove dead `assign`s.
- [ ] **Function inlining** (`fullInliner`, `expressionInliner`, `functionSpecializer`):
      capture-avoiding (unique names make this clean); also unlocks cross-call propagation.
- [ ] **Load resolver** (`loadResolver`): memory/storage store→load forwarding + redundant
      store elimination (needs an effect/aliasing model; the pure/effect split helps).
- [ ] **Loop-invariant code motion** (`loopInvariantCodeMotion`): hoist invariant pure
      computations; must weigh stack-pressure like CSE.
- [ ] **Rematerialization + a stack-aware cost model**: undo CSE/LICM where they cost more
      than they save on the EVM stack.
- [ ] If the backend's **stack allocation** is the bottleneck, improve it (the point where
      IR values are laid onto the EVM stack — DUP/SWAP/POP scheduling).

Each pass: implement → interpreter-validate → measure on the corpus → re-pin baseline →
commit & push → update this file.
