# solc via-IR optimizer coverage map

What of solc's optimizer this compiler has adopted (or natively covers), what it
has not, and why. Compiled from a systematic sweep of solc 0.8.35's default
via-IR step sequence (`libsolidity/interface/OptimiserSettings.h`, abbreviation
map `libyul/optimiser/Suite.cpp`) with each step's *implementation* read, not
just its name, cross-checked against this repo's passes and the uniswap-gas-2
campaign's measurements. Statuses: ✅ covered (by an existing pass), 🟡 partial,
🔨 adopted during the campaign, ❌ measured & rejected, 🅿️ parked (implemented,
below threshold), ⬜ not adopted (with reason).

solc's default sequence backbone is repeated
`ExpressionSplitter → SSATransform → simplify (CSE/LoadResolver/…) →
SSAReverser → ExpressionJoiner`, interleaved with three FullInliner rounds and
one FunctionSpecializer pass. This compiler deliberately takes the opposite
architecture — big expressions + on-stack locals, no SSA phase — so several
rows below are "architectural non-goals" rather than gaps.

## Step-by-step coverage

| solc step | What it does | Status here | Reason / where |
|---|---|---|---|
| ExpressionSplitter `x` | ANF-split every nested expr (enables SSA + solc's backend) | ⬜ non-goal | Opposite of our design; RejoinPairs/ReuseValues go the other way. Only pays as SSA enabler. |
| SSATransform `a` | Reassignments → fresh SSA decls + φ-joins | ⬜ non-goal | Foundation for solc's precision passes; adopting it would fight our backend's slot discipline. Revisit only if LICM/UnusedStore's simple forms prove too weak. |
| UnusedAssignEliminator `r` | CF-aware dead-assignment removal | 🟡 partial | DeadPure/DeadResults/CoalesceCopies cover the non-CF subset; general store-liveness not adopted (proof-heavy, tail-sized payoff). |
| EqualStoreEliminator `E` | Drop `mstore`/`sstore` writing the already-present value | 🅿️ parked | Implemented def-only (EqualStoreElim.lean), exact-state- and refund-neutral. Measured **−144** on uniswap (only spill-slot identity mstores fire; PoolSwap's sstores are real changes). Below threshold; wiring removed. Possible future: aave `PositionStatusMap` identity sstores via the main arm (unmeasured — solc cache timeout). |
| ExpressionSimplifier `s` | Hundreds of algebraic/strength rules (RuleList.h) | 🔨 adopted (subset) + 🟡 | Simplify already had const-fold/neutral identities/EXP family (PR#129: div/mod/mul-by-2^k, eq→iszero, absorbing-zero). Campaign added the operand-preserving byte/mask group: `and(and(e,c1),c2)→and(e,c1&c2)`, `byte(31,e)→and(e,0xff)` — **−1,032 uniswap / −300 gasTests / −52,462 semanticTests**, 0 regressions. Not ported: value-erasing rules (violate the operand-preservation soundness convention), `iszero(iszero(cmp))→cmp` (prior null result; needs bool-range lemma), two-operand mulmod/addmod folds (scaffolding > value), general `byte(k,·)` (gas-neutral or worse). |
| CommonSubexpressionEliminator `c` | DFA value-numbering, whole-function | 🟡 partial | ReuseValues does scoped content-keyed reuse (pure exprs, scratch cells, keccak, sload). Full value-numbering not adopted; measured residue is small next to shuffle/spill costs. |
| LoadResolver `L` | Forward sload/mload to known values; fold small keccak at compile time | 🟡 partial / ❌ for mload | StorageForward + ReuseValues cover sload/scratch. General mload forwarding implemented and **measured −703 → parked** (PR #131): the real loads are branch-dependent spill accumulators, unforwardable; stores can't be removed (final nonzero memory is observed). Compile-time keccak folding not adopted (niche). |
| LoopInvariantCodeMotion `M` | Hoist movable decls out of loops | ⬜ not yet | Highest per-row potential on aave 10k-iteration loops (invariant keccak/sload address computation). Hardest proof (loop congruence + write-set disjointness); campaign prioritized uniswap levers. Top of the future list. |
| UnusedStoreEliminator `S` | Remove stores dead on all paths / covered before read | 🔨 adopted (safe subset) | Covered-before-read (same literal slot rewritten, nothing between may read) is exact-state-preserving. SpillStoreElim.lean, straight-line runs, spill arm: **−632**, 0 regressions. solc's full path-sensitive version (incl. revert-path stores, above-msize stores) not adopted — its legality argument doesn't transfer to our exact-final-memory bar. |
| FunctionSpecializer `F` | Clone functions on literal args | ⬜ not adopted | Would unblock folding in non-inlinable helpers (aave `next`). Moderate value, moderate proof; queued behind LICM for an aave-focused campaign. |
| FullInliner `i` | Aggressive inlining (memoryguard-gated) | ✅ covered (differently) | InlineCalls inlines call-free helpers; measured *ahead* of solc on JUMP costs (TickMath). Pressure-*reducing* gate variants measured ❌: thresholds 13/6/1 monotonically worse; at threshold 1 spill count unchanged — spills are the main body's own locals, not inlined helpers. |
| ExpressionInliner `e` | Inline single-expression functions | ✅ | InlineHelpers (Core β-substitution). |
| ExpressionJoiner `j` | Fold single-use decls back into expressions | ✅ | RejoinPairs (incl. assign/if-cond consumer forms, PR #128). |
| Rematerialiser `m` | Replace var reads by their defining expr (cost-modeled) | 🔨 adopted (targeted) | RematSpill.lean: multi-use cheap-pure rematerialization on would-spill objects only (pre-spill ladder arm) — shrinks the live-local set that drives spilling. **−10,816 uniswap** (PoolSwap spills 637→233, MSTORE −53%), 0 regressions, non-spilling objects byte-identical. Known issue being fixed: needs spill(raw) fallback rung — 9 semanticTests fixtures currently go unsupported. General (non-spill-gated) remat not adopted: deepens use sites, no payoff without pressure. |
| LiteralRematerialiser `T` | Vars known-literal → literal | ✅ | Propagate. |
| StructuralSimplifier `t` | Constant control-flow folding | ✅ | Simplify. |
| ControlFlowSimplifier `n` | if-empty→pop, switch→if, for→if, trailing-leave | 🟡 partial | Slivers via self-eq residue + AsmPeephole. Rest is small-fixture-tail material; unprioritized. |
| DeadCodeEliminator `D` | Drop code after terminators | 🟡 partial | Constant-branch folding removes dead branches; general post-terminator sweep not adopted (rare in our pipeline's output). |
| ConditionalSimplifier `C`/`U` | Infer `cond := value` from control flow | ⬜ | Low value (solc's own admission); needs bool typing. |
| ForLoopConditionIntoBody `I`/`O` | Loop-condition placement | ⬜ | Pure enabler for the splitter/SSA path we don't take. |
| EquivalentFunctionCombiner `v` | Merge syntactically-equal functions | ⬜ | Modest size/dispatch payoff; unprioritized. |
| UnusedFunctionParameterPruner `p` | Drop unused params | ⬜ | Low-moderate; queued behind bigger levers. |
| CircularReferencesPruner `l` | Drop unreferenced recursive fns | ✅ | PruneDefs (transitive reachability subsumes it). |
| UnusedPruner `u` | Remove unused vars/fns | ✅ | DeadPure/DeadLits/PruneDefs. |
| VarDeclInitializer/ForLoopInitRewriter/BlockFlattener/Hoister/Grouper | Normalization | ✅ | Normalize + Flatten. |
| SSAReverser `V` | Undo SSA pre-backend | n/a | No SSA. |

## Backend (solc's OptimizedEVMCodeTransform vs ours)

| solc behavior | Status here | Reason / where |
|---|---|---|
| StackLayoutGenerator (per-block near-optimal shuffle) | 🔨 in progress | The single biggest measured gap (~62k on the TickMath sweep alone: our POP 12,111 vs solc 310). Adopted as a translation-validated Asm→Asm window scheduler (AsmSchedule.lean): untrusted scheduler + symbolic-executor gate. Banked so far: **−4,506** (store-in-place, identity-slot-preserving). Executor+gate soundness proven (AsmScheduleSound.lean, sorry-free), incl. three gate conjuncts that fix real soundness gaps found during proving. Remaining ceiling needs the interleaved-layout algorithm (inputs currently pinned at stack bottom → DUP16 bails on the hottest windows); evict-by-recompute in progress. |
| Binary-search dispatch | 🔨 adopted (≥8 cases) / ❌ below | DispatchTree.lean, fully proven. At <8 cases measured **+270** (uniswap dispatchers are 4-6 cases; the cost is block-lowering JUMPs, not compares). At ≥8: gasTests −6,856, semanticTests −14,904, aave −231; uniswap byte-identical. |
| LiteralSlot (literals never occupy slots) | 🟡 partial | Falls out of window scheduling where windows cover the uses; not a global policy. |
| StackToMemoryMover (memoryguard spilling) | ✅ | MemorySpill* (same design, proven). Victim-selection variants measured ❌ (+46k aggressive / −6 conservative — depth policy already near-optimal; hot accumulators sit far below the DUP16 frontier). |
| StackCompressor (rematerialize before memory rescue) | 🔨 adopted | This is RematSpill (above). |

## Measured dead ends (do not revisit without new evidence)

Recorded in detail in `IDEAS.md`:
- mload forwarding beyond straight lines (−703; unforwardable branch-dependent accumulators).
- Spill victim selection (depth policy near-optimal; the lever is spill *count*).
- Pressure-gated inlining (spills are main-body locals; thresholds monotonically worse).
- Binary dispatch under 8 cases (+270; JUMP-dominated).
- Sub-1k parked passes: EqualStoreElim (−144), kept-but-marginal SpillStoreElim (−632, kept since def-only).
- Yul-level iszero simplification on rejoin patterns (0 on top of the AsmPeephole rule).
- dead-let→pop lifetime shortening (pre-campaign: regressed halt paths).

## Priority of the not-adopted remainder

1. Interleaved-layout window scheduling (backend) — the remaining ~55k of the sweep gap.
2. LoopInvariantCodeMotion — the aave lever (needs the loop congruence).
3. FunctionSpecializer — unblocks non-inlinable helper folding (aave).
4. ControlFlowSimplifier subset + general DCE — small-fixture tail.
5. SSA adoption — only as a last resort if 2-3's simple forms prove too weak.
