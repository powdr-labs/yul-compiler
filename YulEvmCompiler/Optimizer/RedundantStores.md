# Verified Redundant-Store Elimination — design & plan

Status: **M0 + M1 done; M2 forwarding-soundness core landed** (semantics pinned;
abstract domain + `Valid` in `Domain.lean`; load→value-forwarding equivalence in
`Forward.lean`). **IR decision revised — see §"IR form" below.**

## IR form (revised)

An earlier draft argued against a statement-level Core IR for a single pass. For
redundant-store elimination that call is **reversed**, on optimization-quality
grounds, not proof convenience:

* **Run the pass on ANF-normalized Yul** — every operand a variable or literal.
  Then the abstract store is `keyVar → valueVar`, and forwarding `sload(k)` is a
  *variable reference* (`let y := x`).
* **Soundness collapses**: a variable operand is trivially pure — nothing to
  re-evaluate, halt, or read — so forwarding needs no purity side-proof (the
  general `cleanEval` purity machinery is off the critical path).
* **Unconditional profit**: `SLOAD` (100–2100 gas) → `DUP` (~3). Forwarding a
  re-*computable* value expression can be *worse* than the load (re-emitting a
  `keccak`/`mulmod`), so values must be **variables**, not arbitrary pure terms.
  Handling "any argument" is the ANF normalizer's job (bind every non-trivial
  subexpression to a fresh variable), not the forwarder's.
* Keys reduce to **value-numbering on key variables** instead of `splitKey`
  arithmetic — where the aliasing intelligence now lives.

Prerequisite this moves upfront: a verified **ANF / expression-splitting**
normalization (cf. solc `ExpressionSplitter`), shared infrastructure many passes
want. That is the next build after the M2 forwarding core.

This document plans a single verified dataflow pass that subsumes today's
`StorageForward` (read forwarding) and `DeadStore` (write removal) passes with a
symbolic abstract store, and records the M0 semantics findings that gate the
design.

---

## 1. What "proper" means here

Collapse three overlapping optimizations into **one verified abstract-store
dataflow pass**:

- **Store-to-load forwarding** — replace `sload(k)` by the symbolic value last
  written to `k` (generalizes `StorageForward` beyond literals).
- **Value resolution / constant propagation through the store** — when a
  loaded/known value is a literal or a pure `Term`, substitute it so downstream
  `simplify` can fold.
- **Redundant + dead store elimination** — drop `sstore(k, v)` when `k` already
  holds `v` (redundant), or when `k` is overwritten before any read (dead).

The engine threads a symbolic store `σ` through the block, driven by the proved
aliasing oracle in `KeyDiff`. The novelty vs. today is not the idea — it is
doing it with a machine-checked soundness proof against the pinned Yul big-step
semantics.

## 2. Non-negotiables (inherited from the repo)

- Every pass is `Pass D` with `sound : ∀ b, EquivBlock D b (run b)`, composed into
  `compile_correct` via `preservesRun`. No `sorry`, no new axioms.
- **Never broaden acceptance ahead of the proof** — each milestone enables only
  what it proves.
- **Trust boundary**: do not touch `Checks.lean`, `SpecClosure.lean`, `SPEC.md`,
  `lakefile.toml`. Keep the pass internal so the audited theorem *statements* do
  not move; if the spec surface changes, stop and get a human re-pin.

## 3. Central design: certificate-guided rewriting

The abstract store is a **certificate generator, not a trusted analysis**. We
never prove the analysis is an optimal or even sound abstract-interpretation
fixpoint. We prove only that *whenever σ licenses a rewrite, that individual
rewrite is semantics-preserving* — the shape of today's
`deadAt_sound`/`cancel_tail`/`commute_tail`, generalized from a single tracked
key to a threaded map.

Abstract state per straight-line region:

```
σ = { avail    : Key ⇀ AbsVal      -- for forwarding / resolution
    , pending  : Key ⇀ StoreSite   -- for dead-store elimination
    , nonStatic: Bool }            -- proven not in a STATICCALL frame
```

- `AbsVal = ⊤ | known (v : Core.Term Γ 1)` — `known v` means "slot contents equal
  the value of pure expression `v`", where `v` is **intrinsically scoped in Γ**
  (Core IR — §6). Scope exit / rebind kills are then a *typing* obligation, not a
  freshness side-condition.
- `Key` is a must-alias class canonicalized through `KeyDiff`.
- `pending[k] = site` means a store to `k` is emitted and not yet observed; it
  dies if overwritten (must-alias) or if the region ends safely, with no
  intervening read.

## 4. The three hard problems

### (a) Static-context write protection — the linchpin (see §M0)

`sstore`/`tstore` in a static frame halt with `.staticViolation` and take no
effect. Deleting such a store changes the observable outcome. Two proved facts
make it tractable (both confirmed in M0):

1. `env.static` is **immutable within a frame** — nothing in `stepOp` writes it;
   calls open fresh frames. So a whole block runs under one fixed `static`.
2. `.staticViolation` is **non-committing**: `committedState` rolls the frame
   back to its entry state `st0`, exposing only the halt marker + return data.

Consequences:

- **Non-static established** (`nonStatic = true`): after any *surviving* guarded
  mutation we know `static = false`, so `sstore` never halts and dead/redundant
  removal is pure last-writer-wins on the storage map (`upd_absorb`), free to
  cross benign statements. This is the case that fixes
  `sstore(0,1); let x := sload(0); sstore(0,2)`.
- **Leading region** (`static` unknown): deleting a dead store whose slot is
  later re-stored is still sound if the intervening statements are provably
  halt-free and terminating — in a static frame *both* the original store and
  the covering store roll back to the *same* `st0` with `.staticViolation`, so
  the outcomes coincide. (v1 may keep the conservative "cross only reverting
  statements" here and rely on `nonStatic` for the general case.)

### (b) Control-flow joins

Forward analysis with a **meet** at `if`/`switch`/loop-exit: a key survives only
if available with the *same* `known v` on every incoming edge; `nonStatic`
survives only if true on all. Loops v1: conservatively kill every key the body
may write on entry/exit and analyze the body as its own sub-region (like today's
per-block regions). Refine to a fixpoint only if measurement justifies it.

### (c) Calls & scoping

User/external calls conservatively **kill all** region entries (reentrancy can
touch our storage) v1; optionally refine with a proved read/write effect summary
later. Scope exit and rebinds fall out of the Core `Γ` discipline.

## 5. Proof architecture

Forward simulation with an invariant, at the statement-list level (generalizing
`deadAt_sound_storage`):

- `Valid σ V st` : σ soundly describes concrete env `V`, state `st` — for each
  `avail[k] = known v`, `valueEval v V = st.storage (evalKey k V)`;
  `nonStatic ⟹ st.env.static = false`; `pending` matches not-yet-observed stores.
- **Transfer lemma**: if `Valid σ V st` and original `s` steps
  `(V,st) ⟶ (V',st',o)`, then rewritten `s' = rewrite σ s` steps to the *same*
  `(V',st',o)` and `Valid (transfer σ s) V' st'`. Deletion cases discharge via
  `upd_absorb` (redundant/dead), `upd_comm` (disjoint commute), and the
  static-violation rollback (P1/P3).
- Induct over the statement list threading σ; recurse into control flow with the
  merged σ; lift `EquivStmts ⟶ EquivBlock` through the hoist-congruence
  machinery (`hoist_cons_dseStmt`-style) so function hoisting is preserved.

## 6. What to reuse (concrete)

- **Core IR** (`Optimizer/Core/Basic.lean`): `Value Γ`, `Term Γ 1`, `PureOp`,
  `ingest`/`emit`, boundary theorem `ingest_emit` — the well-scoped value
  language for `avail`. `ingestSelf`'s docstring already anticipates dataflow
  passes ingesting with a threaded lexical context.
- **`Optimizer/Core/Subst.lean`**: `valueEval` + `valueEval_eval_iff` — the
  functional evaluator to phrase `Valid` against.
- **`Optimizer/Core/Rule.lean`**: `Rule` + `first_sound` — proof-carrying
  normalization of forwarded values.
- **`KeyDiff`**: `mustAliasWord`/`mustNotAliasWord` (word) and
  `mustCoverMem`/`mustNotAliasMem` (0x20-window memory) with soundness lemmas.
- **Today's `DeadStore` lemmas**: `sstoreEff_absorb`, `sstoreEff_comm`,
  `updAccount_*`, `cancel_tail`, `commute_tail`.
- **`Pass`/`RPass`** + object-path `resolveForLayout` congruence
  (`resolveDeadStoreObj_equiv`).

## 7. Milestones (each independently landable, fully proved)

| # | Week | Deliverable |
|---|------|-------------|
| **M0** | 0 | **Semantics memo (this doc §M0) + machine-checked probes** (`Implementation/RedundantStore/M0Semantics.lean`). **DONE.** |
| **M1** | 1 | Abstract domain + key-classes via `KeyDiff` + `Valid` relation, in `Implementation/RedundantStore/Domain.lean`. **DONE.** `Avail`/`Fact` (known-only word-region store; `⊤` = absence), `find?`/`kill`/`store` via `mustAliasWord`/`mustNotAliasWord`, and `Valid` anchored on `EvalExpr`. Structural lemmas `Valid_nil`/`Valid_cons`/`Valid.filter`/`Valid.kill`/`Valid.store`/`Valid.find?` — axiom-clean (`propext`, `Quot.sound`; no `sorryAx`). |
| **M2** | 1 | **Forwarding + value resolution**, straight-line only. Core landed in `Forward.lean`: `sload_lit_eval` (exact `sload` evaluation on a literal slot) and `forward_atom_sound` (under `Valid`, reading a slot and evaluating the stored variable/literal are interchangeable — both directions, axiom-clean). **Remaining**: variable-slot keys via value-numbering, and the straight-line statement-list simulation threading `Valid`. Depends on the ANF normalizer (see §"IR form"). |
| **M3** | 2 | Add `pending` + `nonStatic`. **Redundant-store** (`upd_absorb`) and **dead-store** deletion crossing benign statements. Fixes the motivating example. |
| **M4** | 2 | Enable **transient** region (same word machinery + `nonStatic`); retires today's staged-transient no-op. |
| **M5** | 3 | Control-flow **merge/meet** at `if`/`switch`, conservative loop kill. Join simulation proof. |
| **M6** | 3 | Call/external-call effect kill; scope/rebind kills via Core `Γ`. |
| **M7** | 4 | **Memory** byte-range region via `mustCoverMem`/`mustNotAliasMem`; no static-revert issue, but `msize`/`mcopy`/`keccak`/returndata windows are barriers. Enables today's disabled memory region. |
| **M8** | 4 | Pipeline integration: unify into `blockRound`/`objectRound`, object `RPass` congruence, `compileSource` fallbacks; **subsume/retire** `StorageForward` + `DeadStore`. Full `lake build` + `Checks`/`SpecClosure` green. Re-measure gas incl. native `CheckSolidityGas` **unoptimized-IR** path. |

## 8. Risks & decision points

- **Static-revert model (highest risk).** Resolved in M0; fallback is to enable
  deletion only after a proven-successful mutation.
- **Escape hatch — translation validation.** If the invariant-based CFG proof
  (M5) proves too heavy, pivot: untrusted fixpoint computes availability, emit
  the rewritten program + per-edit certificates, prove only a checker.
- **Loop precision vs. proof cost.** v1 kills loop-written keys; verified
  fixpoint only if measurement demands.
- **Performance/termination.** Maps as sorted assoc-lists, structural recursion
  (no fuel); the pipeline already iterates 6 rounds.
- **Trust boundary.** Keep everything internal; escalate if the audited surface
  moves.

## 9. Success metrics

- The motivating example reduces to `let x := 1; sstore(0,2)` in one pass (added
  as an `agreeOn` guard).
- Measurable gas wins on the `CheckSolidityGas` unoptimized-`--via-ir` corpora
  (today's pass moved only 2/616 fixtures on the tidy differential corpora).
- `StorageForward` and `DeadStore` deleted, guarantees subsumed, axiom footprint
  in `Checks.lean` unchanged.

---

## M0 — Semantics findings (pinned)

Source: pinned `yul-semantics`
`.lake/packages/yul-semantics/YulSemantics/Dialect/EVM.lean`. Every claim below
is machine-checked in
`YulEvmCompiler/Optimizer/Implementation/RedundantStore/M0Semantics.lean`
(verify with `lake env lean` on that file).

### Static-context write protection

- `sstore`/`tstore`/`log0`–`log4`/`selfdestruct` (and value-`call`/`create`) are
  wrapped in `guardStatic`: in a frame with `env.static = true` they **halt with
  `HaltKind.staticViolation` and take no effect**; otherwise they act.
  Probe: `sstore_static`, `sstore_static_storage`.
- `sload`/`tload`/`mload`/`mstore`/`mstore8`/`mcopy` are **not** guarded — reads
  and *memory* writes are permitted in a static frame.
  Probe: `mstore_permitted_in_static`.
- `env.static` is set at frame entry and never mutated by `stepOp` (the store
  cases preserve `env` except `storageOf`/`transientOf`). So one block executes
  under a single fixed `static`.

### Commit vs. rollback

- `HaltKind.commits`: `stop`/`ret`/`selfdestruct` commit; `revert`/`invalid`/
  `invalidMemoryAccess`/`staticViolation` **do not**.
- `committedState st0 st'` returns `st'` on a committing/absent halt, and
  otherwise **rolls back to `{ st0 with halted, returndata }`** — all memory,
  storage, transient, logs, selfdestructs are discarded on a non-committing halt
  (including `staticViolation`). Probe: `staticViolation_rolls_back`
  (via upstream `committedState_rollback`).

### Store/load algebra (word regions)

- Non-static `sstore` writes `upd st.storage k v` and never halts.
  Probe: `sstore_nonstatic_ok`, `sstore_nonstatic_storage`.
- `sload k` returns `st.storage k` and changes nothing. Probe: `sload_reads`.
- Map algebra powering the rewrites: `upd (upd f k v₁) k v₂ = upd f k v₂`
  (absorb) and, for `k ≠ p`, `upd (upd f k v₁) p v₂ = upd (upd f p v₂) k v₁`
  (commute). Probes: `upd_absorb`, `upd_comm`.

### Design consequences

1. The `nonStatic` flag is sound: any surviving guarded mutation proves
   `env.static = false` for the rest of the (single-`static`) block, after which
   dead/redundant store removal is pure map algebra and may cross benign
   statements — fixing the motivating example.
2. In the leading region, a dead store followed (before any read) by a covering
   store is still removable across provably halt-free, terminating statements,
   because in the static case both the removed and the covering store roll back
   to the same `st0` with `.staticViolation`.
3. The **memory** region has no static barrier (P7), but `touchMemory` updates
   the `msize` high-water mark on every access, so an `mstore` is only removable
   when its extent is provably unobserved — a distinct obligation handled in M7.
