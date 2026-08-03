import YulEvmCompiler.SsaCfg.Implementation.PassesSound.Common
import YulEvmCompiler.SsaCfg.Implementation.PassesSound.Gate
import YulEvmCompiler.SsaCfg.Implementation.PassesSound.Counterexample
import YulEvmCompiler.SsaCfg.Implementation.PassesSound.DveCert
import YulEvmCompiler.SsaCfg.Implementation.PassesSound.ConstFoldCert
import YulEvmCompiler.SsaCfg.Implementation.PassesSound.CseCert
import YulEvmCompiler.SsaCfg.Implementation.PassesSound.InlineBounds
import YulEvmCompiler.SsaCfg.Implementation.PassesSound.Inline
import YulEvmCompiler.SsaCfg.Implementation.PassesSound.ElimParams
import YulEvmCompiler.SsaCfg.Implementation.PassesSound.ConstFold
import YulEvmCompiler.SsaCfg.Implementation.PassesSound.CseRuntime
import YulEvmCompiler.SsaCfg.Implementation.PassesSound.Cse
import YulEvmCompiler.SsaCfg.Implementation.PassesSound.Dve
import YulEvmCompiler.SsaCfg.Implementation.PassesSound.Wf
import YulEvmCompiler.SsaCfg.Implementation.PassesSound.Pipeline
set_option warningAsError true
/-!
# YulEvmCompiler.SsaCfg.Implementation.PassesSound

Soundness metatheory for the `yul-ssa-cfg` optimization passes
(`SsaCfg/Passes.lean`), including the proof consumed by
`SsaCfg.optimizeProg_sound`.

## Why `optimizeProg_sound` carries a dominance hypothesis

`wfCheck` alone does **not** make the pipeline sound. The statement

    P.wfCheck = true → Run P yst0 yst' o → Run (optimizeProg P) yst0 yst' o

is **refuted** in § `Counterexample`
(`optimizeProg_sound_false_without_dom`) — fully machine-checked, with no
`native_decide` and no axioms beyond Lean's own. That refutation is what motivated
`ToAsm.Func.domCheck`/`Prog.domCheck` and the `hdom` hypothesis the statement
now carries; the counterexample is kept here as the standing witness that the
hypothesis cannot be dropped.

The failure is not a coding mistake in a pass. Pass 1 (trivial block-parameter
elimination) and pass 3 (local CSE) are sound only for programs respecting **SSA
dominance**, and `Prog.wfCheck` deliberately does not check it — `Ir.lean` argued
that an undominated use is harmless because "the semantics gets stuck on an
unbound `ValId` read". It is not: in this semantics **registers persist across
blocks** and block parameters are *re-bound on every visit*, so an undominated
use is not stuck — it reads a **stale** binding from an earlier visit. Rerouting
such a use (pass 1 substitutes the parameter `p` by the value `v` all in-edges
pass; pass 3 substitutes a repeated computation by an earlier `ValId`) makes it
read the *current* value instead. `Counterexample.P` is exactly that shape:
block 3 reads block 2's parameter `p` on a path that does not go through block 2.

Two things the defensive gate does *not* do, both recorded in § `Counterexample`:

* it checks the *output*, so it cannot see that the *input* violated dominance —
  `hdomPopt` shows the rewritten program passes `wfCheck && domCheck` happily
  (`hdomP` shows the input does not);
* consequently no downstream check can substitute for `hdom`.

Passes 2 (constant folding) and 4 (dead value elimination) need no dominance:
`constFold` only rewrites an op into the constant its operands' `const`
definitions already force (single assignment suffices), and `dve` only deletes
definitions nothing reads.

## What is proved here

* `Regs` plumbing: `setMany_cons`, `getMany_congr`, `set_congr`, `setMany_congr`.
* **The dominance check, unpacked** (§ `ToAsm`) — the bridge from the decidable
  `domCheck` to the fact the passes actually use:
  * `mem_insertSorted` / `mem_unionS` / `mem_diffS` / `mem_blockUses` /
    `mem_blockDefs` / `mem_lout` — membership in the sorted-set helpers;
  * `liveInSets_fix` — `liveInSets` returns a genuine fixed point of the backward
    liveness step (the fuel loop exits only on `next == cur`);
  * `liveStep_get_eq` / `liveIn_eq` — the fixed-point equation at one block;
  * `liveIn_of_uses`, `liveIn_of_succ` — the two propagation steps: what a block
    reads and does not define is live in, and liveness crosses edges backwards;
  * `domCheck_entry` — under the check, `liveIn(entry) ⊆ f.params`. Chaining the
    two propagation lemmas along a definition-free path and hitting this is
    precisely "no use is undominated";
  * `liveStep_mono` and `liveInSets_least` — `liveInSets` is the *least* fixed
    point, the engine for the dominance-*preservation* obligations.
* The **purity leaves**, transported from the pinned dialect's own
  `effects_sound_withExternal`:
  * `builtin_of_pure` — a pure op is never an open-world (`call`/`create`/`gas`)
    op, so its combined relation *is* the executable `stepOp` graph;
  * `pure_state_eq` — a pure op leaves the machine state alone;
  * `pure_rets_eq` — **CSE leaf**: equal `(op, args)` ⇒ equal results, in any
    two states;
  * `evalPure_stepOp` / `evalPure_transport` — **constant-folding leaf**: what
    the folder computed on `EvmState.init` is what the op returns in *any* state.
* The **pipeline gate**, factored through `optimizeCandidate` so that the
  pipeline's shape is tracked in exactly one place (`optimizeProg_candidate`,
  definitional — it already survived one shape change, the addition of
  `Passes.inlineProg` in front): `optimizeProg_of_gate_true`,
  `optimizeProg_of_gate_false`, `optimizeProg_sound_of_fallback`, and the
  corresponding branch inside `optimizeProg_sound'` — when the candidate fails
  `wfCheck && domCheck`, `optimizeProg` returns the original and soundness is
  reflexivity.
* `runOnce_dom` — dominance preservation for a pipeline round, by composition of
  the four per-pass obligations, and **`constFold_dom`** — the first of those four,
  proved via `ToAsm.domCheck_of_shrinking` and pass 2's structural specification
  (`Passes.constFold_spec`: every output block is a `CFRel`-rewrite of the input
  block at the same index; `cfTerm_cases`, `cfInstrStep_cons`, `cfInstr_fold`,
  `cfBlockStep_spec`, `cfBlock_fold`).
* Both **`forIn` bridges**: `Id.forIn_eq_foldl` for pure-`yield` loops and
  `Id.forIn_eq_loopWith` for **early-return** loops (with `loopWith` as the pure
  model and the `MProd (Option ρ) σ` early-return protocol recorded as a worked
  example). The second unblocks
  `findTrivialParam`, `inlineOnce` and `inlineFunc`, which all `return` early.
* **`ToAsm.liveInSets_isSome` — the liveness fixed point always converges.**
  `Func.domCheck` is `false` by definition when `liveInSets` exhausts its fuel,
  so this is a prerequisite of *every* dominance-preservation statement. Proved
  by the Kleene argument: the sorted-set helpers produce `Pairwise (· < ·)` lists
  (`insertSorted_pairwise`, `unionS_pairwise`, `diffS_pairwise`), such a list is
  determined by its elements (`pairwise_lt_ext`), every iterate stays inside the
  finite `liveUniverse` (`liveStep_liveUniverse`), so `liveMeasure` — the sum of
  the live-set sizes — strictly increases at each non-exiting round
  (`measure_lt`) while staying bounded (`measure_le`, `liveUniverse_length_le`).
  The fuel `blocks.size * (total + 1) + 2` therefore always suffices
  (`go_isSome`).
* **`ToAsm.domCheck_of_shrinking`** — a reusable dominance-preservation
  criterion, built on the two above: a rewrite that keeps `params`/`entry`, only
  shrinks what each block reads, only keeps what each block defines, and only
  drops outgoing edges, preserves `Func.domCheck`. This is `constFold_dom`
  modulo that pass's structural specification.
* **Pass 4's structural specification** (`Passes.dve_blocks_get` and friends):
  `dve` is the one pass written without an `Id.run` loop, so its output is
  directly readable — `dveBlock_uses_sub` (uses only shrink),
  `dveBlock_defs_of_live` (a live definition is always kept),
  `dveBlock_edge_target` (edge targets are
  untouched). This is the complete structural half of both `dve_sound` and
  `dve_dom`.
* The **counterexample**, end to end: `P.wfCheck = true`,
  `ToAsm.Prog.domCheck P = false`, `optimizeProg P = Popt` — the *whole*
  optimizer evaluated **inside the kernel**: `Passes.inlineProg` (proved to be
  the identity here, `hinline`: `P` has no `call`, so `siteCounts` is empty,
  `inlineOnce` finds nothing and `pruneFuncs` keeps everything), then three
  rounds of the four-pass pipeline, then the gate — plus
  `Run P yst yst .normal` and `¬ Run Popt yst yst .normal`.

## Closure

All four per-function passes, program-level inlining, their well-formedness and
dominance preservation chains, whole-program replay, and both defensive-gate
branches are proved here. In particular, `cse_sound`, `runOnceProgN_sound`,
`inlineProg_sound`, and `optimizeProg_sound'` contain no admitted proof steps.
-/
