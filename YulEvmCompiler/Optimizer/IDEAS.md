# Optimizer ideas log

A running log of Yul→Yul optimizer passes we have tried, are trying, or might try.
Each pass is a value of `Optimizer.Pass` (`Spec/Pass.lean`): a total
`run : Block → Block` bundled with `Sound D run : ∀ b, EquivBlock D b (run b)`.
Possessing a `Pass` *is* possessing a verified optimizer — soundness is the only
proof obligation, and it composes with the verified backend via
`Pass.optimize_then_compile_correct` (`Spec/Backend.lean`).

The goal is to reduce **runtime gas** of contracts compiled by this compiler.
The gas harnesses (see `AGENTS.md`) compile solc's *fully unoptimized* IR (or the
Yul corpora directly) and compare against solc's *optimized* output, so there is
a lot of structural slack to remove.

## Framework facts worth knowing before adding a pass

- `Optimizer/Core/Basic.lean` provides the first typed optimizer boundary:
  intrinsically scoped ANF values and arity-indexed pure operations. Successful
  ingestion erases exactly to its Yul input; unsupported, nested, effectful, and
  call syntax remains outside Core, and `Simplify` leaves it unchanged to keep
  the public pass total. `Core/Rule.lean` supplies a generic first-match engine
  whose rules carry their own `EquivExpr` proofs. `Simplify` now uses that path
  instead of retaining a second raw-AST rewrite driver.
- `Core/Subst.lean` provides closed-term instantiation of Core parameter
  contexts (`Term.substEmit`) plus the functional reflection `valueEval` of
  `Step` on value-shaped expressions — the β machinery behind the helper
  inliner. `Spec/Observe.lean` adds the **observational tier** (`ObsPass`,
  `ObsEquivBlock` over committed run observables, memory/`msize`/final-`VEnv`
  quantified away) with the strong tier embedded and the backend payoff
  restated; use it for passes `EquivBlock` cannot express (dead bindings,
  scratch memory), pending a human decision to admit it into the audited roots.
- `EquivExpr`/`EquivStmt`/`EquivStmts`/`EquivBlock` are pointwise big-step
  equivalences with congruence lemmas in `YulSemantics.Equiv`. Local expression
  rewrites lift through `builtin_congr`/`call_congr` and the statement
  congruences.
- Pure EVM ops (`add sub mul div sdiv mod smod addmod mulmod exp signextend clz
  lt gt slt sgt eq iszero and or xor not byte shl shr sar`) reduce via `stepOp`
  to `some (.ok [f args] st)` — **state-independent value, state unchanged**. This
  is exactly what makes constant folding and neutral-element rewrites sound.
- Algebraic identities are only sound when they **keep the operand on the RHS**
  (both sides then require the same variables to be bound). `add(x,0) ≈ x` is
  sound; `mul(x,0) ≈ 0` is **not** (RHS does not require `x` bound, so it differs
  on environments where `x` is unbound — `EquivExpr` quantifies over *all* envs).
  See the note in upstream `YulSemantics.Rewrites`.
- `EquivBlock.of_stmts` needs `hoist b₁ = hoist b₂`. Rewriting *inside a `funDef`
  body* changes `hoist`, so it is **not** liftable by the upstream congruences —
  there is no `funDef`-body congruence upstream (explicitly deferred). We prove
  that missing **function-environment congruence** locally in
  `Implementation/FunCongr.lean` (`FunsRel` + `Step.funs_congr` +
  `EquivBlock.of_stmts_funs`); it lets a pass rewrite inside `funDef` bodies and
  is the reusable foundation for every future pass that does so.
- Object path: `RunObject o L = Run evm o.codeBlock L.initState`, so an
  `EquivBlock` on a code block lifts to object behavior *under a fixed layout*.
  But optimizing a **sub-object** whose compiled byte length changes shifts
  `datasize`/`dataoffset` and therefore the layout `compileObject` produces — so
  the object path needs a length-stable argument or a cross-layout relation. Top
  code-block optimization under a fixed layout is the safe first step.

## Gas targets (which baseline a pass can move)

- `test/solidity-yul-optimizer-gas-baseline.txt` — `yulOptimizerTests`, ~552 rows,
  **644/651 fixtures block-rooted** → moved by a top-level `Block` pass through
  the `compile` (block) path. **Biggest, easiest target.**
- `test/solidity-yul-evm-code-transform-gas-baseline.txt` — `evmCodeTransform`,
  ~40 rows, mostly block-rooted (smaller, stack-transform oriented).
- `test/solidity-yul-object-compiler-gas-baseline.txt` — `objectCompiler`, mostly
  object-rooted → needs the object path.
- `test/solidity-gas-baseline.txt`, `test/solidity-semantic-gas-baseline.txt` —
  real `.sol` via solc `--via-ir`, object-rooted → needs the object path.
- `measureGas` runs the compiled bytecode *directly* (no deploy), so a block
  pass's savings show up immediately in the two Yul block-rooted baselines.

## Passes

### ✅ `identity` (`Implementation/Identity.lean`) — landed
The do-nothing pass; validates the spec is inhabited. Sound by reflexivity.

### ✅ `FunCongr` (`Implementation/FunCongr.lean`) — landed (this branch)
The **function-environment congruence** upstream defers: `FunsRel` (related
function environments — equal signatures, `EquivBlock` bodies), `Step.funs_congr`
(a `Step` transports across `FunsRel`), and `EquivBlock.of_stmts_funs` (block
congruence that lets the hoisted scope change). Enables optimizing inside `funDef`
bodies. Reusable by any future pass.

### 🚧 `Simplify` (`Implementation/Simplify.lean`) — IN PROGRESS (this branch)
A local **constant-folding + neutral-element** expression simplifier that
recurses through the whole program, **including function bodies** (via
`FunCongr`). Only a `for`-loop's `init` is left untouched (it is both executed
and hoisted; changing it needs a `for`-specific congruence — see below).

- **Constant folding**: `builtin op args` with every arg a literal and `op` pure
  → replace with the literal `number (v.toNat)` where `v = f (args.map litValue)`.
  One uniform soundness lemma over the pure-op set (result value is a total
  function of the literal args, state unchanged).
- **Neutral-element identities** (operand is a `var`, kept on the RHS):
  `add(x,0)`, `add(0,x)`, `sub(x,0)`, `mul(x,1)`, `mul(1,x)`, `div(x,1)`,
  `or(x,0)`, `or(0,x)`, `xor(x,0)`, `xor(0,x)`, `and(x,MAX)`, `and(MAX,x)`,
  `shl(0,x)`, `shr(0,x)` → `x`. Collapsed to two parameterized lemmas
  (`[var,lit]` and `[lit,var]`) discharged by a per-identity `stepOp` reduction.
- **Wiring**: inserted into `compileSource`'s block branch (`compile (P.run …)`);
  soundness is `Pass.optimize_then_compile_correct`.
- **Constant control flow**: after expression simplification, literal `if`
  conditions select the body/empty block and literal `switch` conditions select
  the matching case/default block.
- **Target**: `solidity-yul-optimizer-gas-baseline.txt` (+ evmCodeTransform).
- **`for`-loop `init`**: left untouched. `init` is executed *and* hoisted into the
  loop's scope, and upstream `EquivStmt.forLoop_congr` fixes it. A `for`-specific
  congruence (init changes with a `ScopeRel` side condition, like
  `of_stmts_funs`) would let us reach it — small follow-up.

### ✅ `ObjectPass` + `simplifyObject` — object path WIRED (this branch)
`simplifyObject` (in `Simplify`) runs the pass on **every** code block of an
object tree — the deploy object *and* every nested sub-object (the `*_deployed`
runtime of a Solidity artifact). It is wired into `compileSource`'s object branch,
so **both deploy and runtime code are optimized**. Soundness (`ObjectPass`):
`simplifyObject_compileObject_correct` (the artifact is the verified compilation
of the optimized tree, via `compileObject_correct`) + `simplifyObject_topEquiv`
(every object's top code block is `EquivBlock`-equivalent to the original, via
`blockEquiv`). So the bytecode faithfully runs a program each of whose code blocks
is provably equivalent to the source.

**Full end-to-end soundness** (`simplifyObject_correct`): compiling
`simplifyObject o` yields bytecode that correctly simulates the **original**
object `o`'s resolved run under the compiler's layout — the object analogue of
`Pass.optimize_then_compile_correct`, with **no caveat**. The bridge is the
**resolution congruence** `ResolveCongr.resolveSimplifyBlock_equiv`:
`EquivBlock (resolveForLayoutStmts L b) (resolveForLayoutStmts L (simplifyStmts b))`
— proved by a structural induction using that expression rewrites are disjoint
from `dataoffset`/`datasize`, the pass never manufactures a string literal, and
resolving switch cases commutes with selecting a literal case.

Gas (real Solidity contracts, `checkSolidityGas`): `libsolidity/semanticTests`
619/648 down (−185,438 gas); `libsolidity/gasTests` 12/12 down; `objectCompiler`
3 down. All zero-regression.

`Pass.optimizeTopCode` + `Pass.optimizeTop_compileObject_correct` remain as an
alternative single-object theorem for the offset-free/leaf fragment.

### ✅ Constant control-flow folding (`agent/optimizer-control-flow`)

Extend `Simplify` with bottom-up folding of control flow whose condition becomes
literal after expression simplification:

- `if 0 { body }` → an empty block;
- `if <nonzero literal> { body }` → `body` as a block; and
- `switch <literal> ...` → the selected case/default as a block.

This removes the condition dispatch and, more importantly, all unreachable
branch bytecode.  It is distinct from the copy-propagation/dead-`let` work in
PR #52 and directly targets existing constant-control-flow fixtures in the Yul
optimizer and EVM code-transform gas suites.

Soundness is local and exact: invert the source `if`/`switch` big-step rule,
use literal evaluation to rule out the untaken `if` arm or fix the switch value,
and reconstruct the chosen block execution in both directions.  These local
equivalences compose after the existing expression/body congruences, including
the function-environment relation for rewritten function bodies.  The object
path additionally uses the structural fact that resolving a selected switch
block equals selecting from the resolved cases; this preserves
`resolveSimplifyBlock_equiv`, so the existing whole-tree object correctness
theorem continues to cover both deploy and runtime code.

Gas results are zero-regression: 9 `yulOptimizerTests` fixtures improve by
2,292 total gas, 2 `evmCodeTransform` fixtures improve by 240, and 11 real
Solidity `semanticTests` contracts improve by 15,400.  The largest local wins
are literal switches (up to 408 gas in the Yul scenarios); all solc fingerprint
columns are unchanged.  The curated Solidity `gasTests` and `objectCompiler`
rows are unchanged.

## The layout-coupling (why the end-to-end object theorem is subtle)

`planObject` derives every sub-object/data **offset** from the top code block's
compiled `codeSize`, and `resolveForLayoutStmts` bakes those offsets into the code
as `PUSH32` literals. Consequences (verified against the code, see the analysis
that produced `ObjectPass`):

- Optimizing code that any `dataoffset`/`datasize`/`datacopy` observes **shifts
  the layout** (`L → L'`). There is **no `EquivBlock`-congruence for resolution**,
  and none is generally provable (folding reads the offset immediates), so a raw
  `EquivBlock` on the code block does **not** lift across resolution to two
  different layouts.
- Sound optimization is clean **only** when the top block makes no layout
  references (`ObjectPass`'s `hres₀`/`hres₁`).
- Real solc output nests a **constructor** object (whose top code `datacopy`s the
  runtime — not offset-free) around the **runtime** sub-object (where execution
  gas is spent). Optimizing the runtime shifts the constructor's baked offsets;
  optimizing the constructor is offset-*ful* at the top. So neither the "top code
  only" nor the "leaf" fragment reaches real-contract runtime gas.

To move `solidity-gas`/`solidity-semantic` (object-rooted, the real solc
comparison) we need one of: (a) a **cross-layout object equivalence** relating the
offsets an optimization shifts (major); or (b) restructuring `planObject` to apply
the pass *after* resolution and recompute `codeSize` from its output (breaks the
current fixed-width-`PUSH32` layout fixpoint for offset-sensitive passes). This is
the real object-path frontier.

### ✅ `Propagate` — constant propagation, binding-preserving (this branch)

**Forward substitution of known bindings, keeping every binding in place.** After
`let x := <number literal>`, later reads of `x` (until invalidated) become the
literal; `let x` (no initializer) yields `x ↦ 0` (Yul zero-initializes); at
`x := <literal>` with `x` already tracked, the entry is *refreshed*
(σ-membership proves `x` is bound, so `VEnv.set` really updates) — capturing
solc's reassignment chains (`ssaPlusCleanup/multi_reassign.yul`). A
fold-at-let step (reusing `pureFold`) collapses literal chains in one
traversal, so copy chains rooted at a constant collapse too. (Bare *copy*
entries `y ↦ x` are proven sound but disabled in production — see the depth
lesson below.) Invalidation is syntactic and
conservative: shadowing lets, assignments (key *and* rhs-source of copy entries),
and, per construct, the assigned/declared sets of nested bodies; loops rewrite
cond/body/post under a σ pruned by the loop's whole write set (invariant by
construction); `funDef` bodies restart at σ = ∅ (fresh callee env).

**Why sound in the unchanged pointwise spec** (where binding *removal* died,
PR #52): the kept `let` guarantees the variable is bound to the known value in
every execution reaching the use site, on both sides — no stuckness asymmetry,
no well-scopedness assumption. Invariant: `Compat V σ` (each entry's key is bound
and agrees with its rhs). One bidirectional `Step` simulation, with `FunsRel`
(`FunCongr`) for rewritten function bodies.

**Object path without weakening**: soundness is proven for a *relation*
`PropRel σ ss ss'` (transform rules + skip alternatives; pruning mandatory), with
`propStmts` inhabiting it. Since resolution maps number literals and vars to
themselves and only rewrites `dataoffset`/`datasize` string-calls *into* number
literals, `PropRel` is closed under `resolveForLayoutStmts` by a purely syntactic
induction — the skip rules absorb resolution-created literals. So the object
pipeline gets the **full** pass (no `litOK`-style restriction), and the whole-tree
correctness theorem extends stage-wise as before.

**Why it pays**: vars are stack slots (read = DUP = 3 gas, literal = PUSH = 3 gas),
so each substitution is gas-neutral until the existing `Simplify` folding /
constant-control-flow folding / `InlineHelpers` fire — then folded sites save
~6 gas each, folded branches remove dispatch + dead bytecode, inlined calls save
~25+ gas. Corpus: 558 literal-lets (347 safe + 78 refresh-recoverable), ≥26
baseline fixtures with concrete fold unlocks, and the pervasive solc `let _N := 0`
idiom (also all over real via-IR output → object-rooted baselines). Substitution
also relieves the DUP16 depth limit (deep var reads currently fail to compile).

**Pipelines**: block `[simplify, propagate, inline(litOK), simplify]` (propagate
first feeds the literal-friendly inliner); object
`[simplify, inline(var-only), propagate, simplify]` (inline first — propagation
would turn var args into literals and starve the var-only object inliner).

Known non-targets (left in this list): LICM, full inlining of multi-statement
helpers, block flattening — these dominate the largest remaining gas-ratio rows.

**Results** (with `DeadLits` below; re-pinned, zero regressions everywhere,
cumulative): `yulOptimizerTests` 179 rows −10,300 gas; `evmCodeTransform` 16
rows −840; Solidity `gasTests` 12/12 rows −1,733; `semanticTests` **534 rows
−616,030** plus **81 contracts that newly compile**; `objectCompiler` 1 row
−18. All solc columns unchanged; the axiom gate is clean.

### ✅ `DeadLits` — dead literal-binding elimination (this branch)

The removal companion: delete a singleton `let x := <literal>` (or zero-init
`let x`) whose variable never occurs afterward in its block — exactly the
leftovers `Propagate` creates, and exactly the removable class that needs **no
spec change**: a literal binding always evaluates, changes no state, and its
binding dies at the enclosing block's `restore` anyway, so the pointwise iff
holds with no `WellScoped` assumption (contrast PR #52, whose *arbitrary*-rhs
removal genuinely needed the rejected spec weakening — its `Frame.lean`
toolkit, `InsAt` with depth-from-the-bottom indexing plus
`frameAdd`/`frameRemove`, is salvaged verbatim as the semantic core here).
Soundness: the skip-rule relation `DlRel` (same architecture as `PropRel`;
closed under layout resolution, so the object path gets the full pass), with
removal steps discharged by `removeLit_equivBlock` — sequence split at the
binding, frame simulation across the insertion, `restore` alignment
(`restore_insAt_le`) — chained under an arbitrary common prefix, and kept
steps by the pointwise congruences. Wired as the final stage of both
pipelines. Each removed binding saves its PUSH+POP and **frees a stack
slot** — 81 real `semanticTests` contracts that used to die at the DUP16
limit now compile.

**The copy-propagation depth lesson** (measured the hard way): *copy* entries
(`y ↦ x`) are proven sound end-to-end — the relation, both simulations, and
the resolution closure all cover them — but the production transform creates
**literal entries only**. Substituting a copy replaces a read of a recently
bound (stack-shallow) variable with a read of an older (deeper) one, and this
backend's variable reads are `DUP`s hard-limited at depth 16: with copies
enabled, solc's `dispatch_*.sol` gasTests stopped compiling. Literal
substitution can only relieve depth (a literal is a `PUSH`, and folded sites
shrink expression stacks). Re-enabling copy entries behind a depth analysis
(only propagate copies whose source provably stays within `DUP16` at every
use site) is a logged follow-up; any future substitution-based pass must run
this same check.

### ✅ `InlineCalls` — statement-level inlining of call-free helpers (this branch)

**The dominant remaining gap is function-call protocol overhead.** The verified
backend's call protocol costs ≈ `24 + 2·|args| + 6·|rets|` gas per call (PUSH32
ret-addr, zeroed ret slots, jumps, JUMPDEST, param pops, ret rotation, dynJump,
+11 for `leave`), and solc's unoptimized IR routes every external call through
~15 tiny helpers (`external_fun_*` → `abi_decode_tuple_*` → `abi_decode_t_*` →
`validator_revert_*` → `cleanup_*`, `fun_X` → `fun_Y` wrappers, `zero_value_*`,
`revert_error_*`). Measured on the Uniswap v4 suite: `UnsafeMath.sol` ours
780 gas/tx vs solc 154 — ~75–85 % of the gap is call protocol + copy-`let`s.
solc's FullInliner collapses all of it; our `InlineHelpers` only inlines
single-*expression* bodies (var-only on the object path).

The pass inlines *statement-level* calls (`let xs := f(as)` / `xs := f(as)` /
`f(as)`) to functions whose body is **call-free** (no `.call` anywhere — the
body's execution is then independent of the function environment, killing all
closure/scope-resolution obligations), has **no
loops/funDefs/leave/break/continue** (`if`/`switch`/nested blocks fine; one
trailing `leave` allowed and dropped), and is **binder-aware well-scoped**
within `params ∪ rets` (a soundness condition, not hygiene: inlining an
ill-scoped body converts callee stuckness into caller execution). Replacement
(let-form): `let xs` then
`{ let rs (zero-init); let pₙ := aₙ; …; let p₁ := a₁; { ss }; x₁ := r₁; … }` —
the inner env is exactly `callOk`'s `params.zip argvals ++ bindZeros rets`, the
`{ ss }` wrap mirrors the call's body-block `restore`, arg evaluation stays
right-to-left, and per-site conditions (`(vars(as) ∪ xs) ∩ (ps ∪ rs) = ∅`,
`vars(as) ∩ xs = ∅` for let-form, `xs.Nodup`, exact arities) rule out the
capture/stuckness asymmetries. `for`-init sites are skipped (as in `DlRel`).
Helper chains collapse leaf-first by iterating the pipeline (a call-free
callee inlines this round, making its caller call-free for the next round).

Soundness: PropRel-style skip-rule relation `IcRel Δ` (Δ = syntactic decl map
from enclosing hoisted scopes; original decls, so `lookupFun funs₁ f` matches
Δ syntactically), fwd+bwd `Step` simulations with two new semantic tools:
`Step.funs_irrel` (call/funDef-free code ignores the function env) and
`Step.append_frame` (scoped weakening: well-scoped code runs identically with
an arbitrary caller env appended below — `frameAdd`'s mention-freeness cannot
work here since the caller env is arbitrary; shadowing-aware well-scopedness
is the right condition). Halt-in-body leaves the site's temporaries on the env
until the enclosing block's `restore` — a prefix generalization of DeadLits'
`ResRelAt`, confined to the `.stmts` class. Object path: `IcRel` is closed
under layout resolution (`dataoffset`/`datasize` are *builtins* in this AST,
so resolution never changes the call count; all classification conditions are
resolution-invariant), giving the full pass on object code, no litOK-style
weakening. Transform-only heuristics (skip rules absorb them): a size bound
and a live-local depth guard so aggressive inlining does not push callers past
the backend's DUP16/SWAP16 hard limit (see the known-compile-failures lists).

**Results** (fully proven, no sorries, axiom gate clean; pipelines iterated
6 rounds; transform-only guards `rets ≤ 2` and `liveMax ≤ 10` plus a
compile-fallback in `compileSource` — optimized program first, unoptimized if
the backend rejects it — so stack-pressure blowups cannot cost coverage):
`semanticTests` **842 rows −3,354,775 gas, zero regressions**; `gasTests`
12/12 rows −15,874 (e.g. `exp.sol` 3,576 → 2,700, `dispatch_large.sol`
92,572 → 88,362); Uniswap v4 6/6 rows −4,823 (`UnsafeMath.sol` 3,900 → 2,908,
`BitMath.sol` 6,186 → 4,902, `SafeCast.sol` 6,509 → 5,442);
`yulOptimizerTests` ~57 rows −16k; `evmCodeTransform` 6 rows −1,668;
`objectCompiler` 2 rows −240. All solc fingerprint columns unchanged.

Proof lessons for future passes: the **`scoped_transfer` engine** (one
induction giving funs-irrelevance + scoped weakening over an arbitrary
appended environment + the normal/halt outcome restriction for the checked
fragment) is reusable for any pass that relocates code between environments;
the **backward let-form reduction** (after the zero-init runs, a `let`-site
is exactly its assign-form site, so the backward simulation reuses the
`siteAssign` relation one statement in — no two-level induction needed); and
inlining bodies are inserted *unchanged* (call-free bodies contain no sites),
so `Δ` entries always match `lookupFun` on the source side syntactically.

Follow-ups logged, not in v1: bodies containing calls (needs Δ-compat across
closures), arg substitution instead of `let p := a` copies (capture/depth),
`InlineHelpers` litOK upgrade via a skip-rule relation (would inline
literal-bodied expression helpers — `shr(224, v)`, address masks — on the
object path; also unblocks chain collapse for non-uint256 cleanup types and
would let more `validator_revert_*` chains collapse), the
`if iszero(eq(x,x)) {halt-body}` → `pop(x)` validator residue, copy-chain
cleanup (`let _2 := var_x; let expr := _2` residue is now the dominant
remaining cost — copy propagation behind a depth analysis), and smarter
guards (whole-caller live-local analysis instead of the per-callee bound).

## Candidate next ideas (not started)

### 🚧 `StackLayout` — liveness-guided stack-slot reuse ([#61](https://github.com/powdr-labs/yul-compiler/issues/61))

Treat block-local Yul bindings as virtual stack registers and color their
live ranges onto the existing local slots.  At a singleton `let y := e`, a
dead, reachable local `x` may be reused by emitting the source-level equivalent
`x := e` and consistently renaming the remainder of `y`'s live range to `x`.
The allocation policy is separate from the semantic mechanism: a backwards
liveness analysis scores legal slots by resulting `DUP`/`SWAP` reach and
prefers no rewrite unless reuse lowers peak stack pressure.  This keeps the
common shallow case byte-for-byte stable while compressing the large solc IR
frames that currently fail at `DUP16`/`SWAP16`.

The proof is a bidirectional `Step` simulation over a slot-renaming relation on
variable environments.  The overwritten value is unobservable because the
chosen slot is dead; the original environment's extra binding and the reused
environment agree on every renamed live variable; declarations and assignments
preserve that relation; and the enclosing block's `restore` erases the local
layout difference.  The transform is conservative around shadowing,
multi-value declarations, function boundaries, loop-carried values, and
non-local control until their side conditions are proved.  It will be an
ordinary strong `Pass`, plus resolution closure for the production object path.

Acceptance target: issue #61's nine-local reproducer and the five Uniswap v4
known stack-too-deep fixtures.  Performance gates: no lost compilation, no gas
baseline increases, and reuse enabled only where the compiler's exact classic
stack-depth model predicts a lower peak or turns rejection into acceptance.

### ✅ `InlineHelpers` (`Implementation/InlineHelpers.lean`) — landed (this branch)

Generalizes (and **replaces**) `InlineIdentity` through the Core boundary:
`helper?` classifies any `function f(ps) -> r { r := e }` whose body ingests
into `Core.Term ps 1` (nodup, all-read params; string-free). A bare-parameter
body keeps the old `f(e) → add(e, 0)` fence at any single-argument site; a
pure built-in body is **substituted** into flat (value-argument) call sites by
`Term.substEmit` — solc's `wrapping_*`/shift/cleanup wrapper helpers inline
without paying the call protocol. Recursion, effectful/multi-statement bodies,
and non-flat sites keep the call (the fragment Core does not yet cover). The
`litOK` flag separates the block pipeline (literals allowed in bodies and
arguments) from the object pipeline (variables only), because layout
resolution *creates* literals from `dataoffset`/`datasize`, and the
resolution commutation (`InlineHelpersResolve.lean`) needs classification and
the rewrite condition to be resolution-stable. Pipelines live in
`Implementation/Pipeline.lean` (`optimizerPipeline`, `objectPipeline`,
`optimizerPipelineObject_correct`).

### ✅ Inline exact identity helpers (`codex/semantic-gas-optimizer`) — superseded by `InlineHelpers`

Solc's unoptimized IR contains many helpers of the exact form
`function f(p) -> r { r := p }`.  Each use currently pays the full verified
Yul function-call protocol even though the body only returns its argument.  The
semantic gas rows with the largest current `ours / solc` ratios are especially
dense in these helpers: user-defined operator wrappers, cleanup/conversion
chains, and loop bookkeeping.

The planned pass preserves every declaration and rewrites a lexically resolved
identity call `f(e)` to `add(e, 0)`.  The `add` is intentional: unlike the
generally-unsound raw rewrite `f(e) → e`, it preserves the requirement that `e`
produce exactly one value, while also preserving stuckness, halts, value, and
state.  A following `Simplify` run can remove the `add` for the already-proved
variable/literal cases.  Lookup uses the same ordered stack of ordered hoisted
scopes as `lookupFun`, including first-definition behavior, shadowing, function
closures, and the special `for`-initializer scope.

Measurement-only prototype results on 15 of the highest-ratio semantic
benchmarks were all improvements, including:

- `operators/userDefined/all_possible_operators.sol`: 50,489 → 40,160
  (−10,329 gas);
- `statements/empty_for_loop.sol`: 6,580 → 3,095 (−3,485);
- `viaYul/conditional/conditional_multiple.sol`: 1,709 → 1,188 (−521); and
- `operators/userDefined/multiple_operator_definitions_different_types_different_functions_separate_directives.sol`:
  4,205 → 2,319 (−1,886).

The proof will be a bidirectional `Step` simulation indexed by the static scope
stack, because function bodies that call sibling identities are not pointwise
equivalent under arbitrary unrelated `FunEnv`s.  A local identity-call lemma
handles the rewrite; other calls recursively simulate transformed bodies under
corresponding closure environments.  The object path will prove that identity
classification and transformation commute with `resolveForLayoutStmts`, then
compose that result with the existing `Simplify` resolution congruence for the
`Simplify → InlineIdentity → Simplify` pipeline on every object code block.

- **`for`-loop `init`**: a `for`-specific congruence to simplify `init` too.
- **Higher-impact passes**: dead/unused-`let` elimination, redundant `pop`/store
  elimination, branch/switch folding, common-subexpression elimination.
- **Dead `pop`/unused `let` elimination**: remove `let x := <pure e>` when `x`
  is never used and `e` is side-effect-free; drop `pop(<pure e>)`.
- **`iszero(iszero(x))` in boolean position** → `x` when the value is only used
  for truthiness (condition of `if`/`for`, arg of `iszero`).
- **Double-negation / `not(not(x))` → x**, `xor(x,x) → 0`, `sub(x,x) → 0`
  (var-only, value-preserving where sound).
- **Block flattening** of nested `{ … }` with no `funDef`s and no shadowing.
- **Asm-level peepholes** (separate, Asm→Asm soundness contract).
