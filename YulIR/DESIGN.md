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
- **Functions are not statements.** `Stmt` has no `funDef`. A `Program` is a table of
  `functions : Std.HashMap Ident Function` (keyed by name) plus a `main` block; an `Object`
  holds a `Program` (+ sub-objects/data). `ofYul` lifts every `funDef`, at any nesting depth,
  into this flat table — sound because Yul functions capture no enclosing *variables*, only
  their params/rets/locals and the functions in scope. This makes function-name uniqueness
  **structural** (a `HashMap` key), gives O(1) call-target lookup, and removes `funDef`
  hoisting/scoping from every pass (each pass now runs over `main` and each function body). To
  keep output deterministic despite `HashMap`'s unordered iteration, `toYul` **sorts functions
  by name** before emitting them at the top of the code block (Yul hoisting then makes them
  mutually visible). *Assumption:* distinct source function names (solc `--via-ir` guarantees
  this; `uniquify` maintains it). A colliding name would overwrite in the table — handled by a
  future rename-on-flatten if the corpus needs it.
- **Named** variables (erasure to Yul is trivial). The intrinsically-scoped `Var Γ`
  refinement (à la `Optimizer.Core.Term`) is deferred to proof time.

## Passes (`YulIR/Optimize.lean` = `optimize`)

`ofYul` already delivers **uniquely-named, block-free** IR (variable disambiguation and block
flattening happen during translation — see below), so the pipeline is just:

Order: (`valueNumber` → `structural` → `deadStore` → `deadCode`) ×2.

| Pass | File | What | Provability notes |
|---|---|---|---|
| Simplify | `Simplify.lean` | local constant folding (via dialect `stepOp`) + algebraic identities | per-`Rhs`, local; folding delegates to the semantics |
| ValueNumber | `ValueNumber.lean` | const/copy propagation, folding across `let`s, CSE — tracks only *immutable* values so no invalidation is ever needed | forward, monotone; immutability = never an `assign` target |
| Structural | `Structural.lean` | dead-branch (`if 0`), constant `switch` selection, `if 1`→splice, empty removal, and unreachable-code elimination (drop stmts after a terminator) | local, per-statement rewrites |
| DeadStore | `DeadStore.lean` | remove `x := <pure rhs>` whose value is never observed (backward liveness; conservative for loops/`break`/`continue`; return vars protected) | only removes a provably-dead pure store |
| DeadCode | `DeadCode.lean` | remove unused pure bindings, and pure statements like `pop(x)`; fixpoint | pure ⇒ no observable effect |

Variable **disambiguation** (α-rename every binder to a fresh `_ir_<n>`, resolve refs through a
scoped map) and **block flattening** (splice every Yul `{ … }` inline — sound once names are unique)
are done *in `ofYul`*, not as separate passes, which is what lets the IR have **no `block`
constructor** at all (a type-level invariant). No pipeline pass introduces a duplicate name, so no
re-`uniquify` is ever needed.

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

## Status & roadmap toward parity

Current, on Solidity's `yulOptimizerTests`:

* **Gas ≈ parity**: total EVM execution gas `ir-opt` 1,203,801,947 vs `current` 1,203,697,922
  (**+0.009%**) — the metric solc's optimizer actually targets (`scripts/YulIRCorpus.lean gas`).
* **Code size within ~1.2%**: `ir-opt` 221,001 vs `current` 218,372 (**−9%** vs `ir-noopt` 240,892);
  several categories *beat* `current` (`structuralSimplifier`, `deadCodeEliminator`,
  `unusedAssignEliminator`, `unusedPruner`, `fullSuite`).
* **Correctness**: full-corpus behaviour sweep = **0 miscompiles**; interp gate green on 57 progs.

Done: uniquify · simplify · value-numbering (const/copy-prop, fold, CSE) · structural +
unreachable-code · dead-store (unused-assignment) · dead pure bindings/statements.

**Where the residual size gap is** (measured): dominated by `loopInvariantCodeMotion` (+4170) and
`equalStore`/`unusedStore`. It is *not* CSE alone — gating CSE to expensive ops did not remove it,
and it persists from copy-propagation/uniquify changing variable liveness/naming in ways the
**backend stack allocator** lowers less well. I.e. the remaining gap is now as much a *backend
stack-scheduling* problem as a missing IR pass.

Remaining to reach/exceed parity:

- [ ] **Function inlining** (`fullInliner`, `expressionInliner`, `functionSpecializer`):
      capture-avoiding (unique names make this clean); mainly valuable for *unlocking*
      cross-call propagation. `leave` handling is the crux (restrict to leave-free,
      non-recursive, small bodies first).
- [ ] **Load resolver** (`loadResolver`, `equalStoreEliminator`, `unusedStoreEliminator`):
      memory/storage store→load forwarding + redundant/overwritten-store elimination
      (needs an effect/aliasing model; the pure/effect split helps). Also recovers the
      CSE-inflated storage-store categories.
- [ ] **Rematerialization + a stack-aware cost model**: undo CSE (and later LICM) where the
      live-range extension costs more DUP/SWAP than recomputation saves. (CSE is kept on
      deliberately; this is its counterpart.)
- [ ] **Gas measurement** alongside code size: LICM and CSE trade size for gas, so the size
      metric under-credits them. Add a gas column (execution over the corpus; likely a native
      `lean_exe` since interpreter execution is minutes).
- [ ] **Loop-invariant code motion** (`loopInvariantCodeMotion`): gas-oriented; gate on the
      gas metric + cost model.
- [ ] If the backend's **stack allocation** is the bottleneck, improve the Yul→EVM
      DUP/SWAP/POP scheduling.

Each pass: implement → interpreter-validate → measure on the corpus → behaviour-sweep →
re-pin baseline → commit & push → update this file.
