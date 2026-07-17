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
— proved by a structural induction using that the pass touches only pure ops and
`var`/`lit` neutral operands (disjoint from the `dataoffset`/`datasize` nodes
resolution rewrites, and the pass never manufactures a string literal so the
layout-keyed shape is preserved).

Gas (real Solidity contracts, `checkSolidityGas`): `libsolidity/semanticTests`
619/648 down (−185,438 gas); `libsolidity/gasTests` 12/12 down; `objectCompiler`
3 down. All zero-regression.

`Pass.optimizeTopCode` + `Pass.optimizeTop_compileObject_correct` remain as an
alternative single-object theorem for the offset-free/leaf fragment.

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

### 🚧 `CopyProp` + `DeadCode` (`Implementation/Frame.lean`, +Subst) — IN PROGRESS (branch `optimizer-dce`)
**Copy propagation of single-use `let` temporaries + dead-`let`/dead-code
elimination.** Data-driven target: solc's unoptimized `--via-ir` runtime IR is
dominated by single-assignment `let` temporaries — e.g. dispatch_large's runtime
has 315 `let`s of which **82 are var→var copies** (`let x := y`) and 62 are
const-lets; abiv2 has 25 copies. These are the bulk of the redundancy.

Honest gas ceiling: each eliminated copy saves ~one `DUP`+`POP` (~5 gas) in our
codegen, so ≈0.2–0.5% on dispatch-heavy contracts (more inside hot loops). The
big gaps vs solc are codegen/algorithmic, not local rewrites — this is the best
*provable-local* lever, labeled honestly.

**Reusable rewrite-proof tooling** (usable by any future env-dependent pass —
the point is a toolkit, not one-off code). All in `Implementation/Frame.lean`,
`sorry`-free:
- `mentions`/`stmtMentions`/`codeMentions` free-variable analysis (with the
  `optExprMentions`/`optBlockMentions` helpers — inline `match`es in a def break
  kernel-checking of `simp`-rewritten hypotheses inside big inductions).
- The VEnv **insertion relation** `InsAt d x v V1 V2` (`V2` is `V1` with `(x,v)`
  spliced in at depth `d = |below|`), with `get_ne`/`set`/`setMany`/`prepend`/
  `length`/`restore` preservation lemmas. **Depth-indexing is essential**: the
  general existential splice loses the depth needed for the `restore` case;
  fixing `d` makes `restore` drop the same prefix on both sides. **No freshness
  of `x` in `V1`** is required (unmentioned code never touches `x`, so the insert
  is invisible even when shadowing) — which is what lets a rewrite stay sound
  with no no-shadowing precondition. **Done.**
- `venvLen_mono` (env never shrinks — the invariant the semantics leaves implicit
  in `restore`'s docstring) and `restore_length`. **Done.**
- The **frame lemma, both directions**: `frameAdd`/`frameRemove` — running
  `x`-unmentioned `code` from `V1` vs from `V2` (`= V1 + (x,v)`) stays in
  lock-step (`eres` equal, `sres` `InsAt d`-related, `restore` aligned). Full
  35-case inductions over `Step`. **Done.**
- These join `FunCongr` and `ResolveCongr` as the reusable meta-theory layer.

**Soundness constraint discovered (shapes the pass design).** `EquivBlock` is
*pointwise on the raw `VEnv`*, so:
1. Any binding-*removing* transform (dead-`let`, copy-prop-then-drop) is
   **block-level only** — it changes the statement-sequence's output env, so it is
   *not* an `EquivStmts` congruence; it only becomes an equivalence after the
   block's `restore` drops the extra binding. Proofs go through `EquivBlock`
   (= `EquivStmt (.block ·)`), not `EquivStmts.cons_congr`.
2. Removing `let x := e` is **unsound when `e` can get stuck** (e.g. `e = var y`
   with `y ∉ V`): the equivalence quantifies over *all* `V`, including ill-scoped
   ones, where the original is stuck but the reduced program runs — breaking the
   `↔`. Only *always-evaluable* `e` (literals, closed total builtins) is
   unconditionally droppable — which is rare in solc output, so low gas.
3. The **gas-relevant** transform is therefore **copy-propagation with
   substitution**: `let y := x; rest` → `rest[y↦x]`. This is sound because the
   substituted `rest` *reads `x` exactly where the `let` did*, so stuck-ness is
   preserved. It needs a **variable-substitution lemma** (`rest[y↦x]` preserves
   semantics while the aliasing invariant `V.get y = V.get x` holds and neither
   `y` nor `x` is reassigned/reshadowed), on top of the frame lemma for the
   block-level `restore`.

**Next**: the substitution lemma, then the `copyProp` pass (`let y := x; rest`
→ `rest[y↦x]`, block-level soundness via substitution + `frameRemove`/`frameAdd`
for the dropped binding), wired into the pipeline, gas re-measured.

### ✅ Spec change + dead-`let` DCE (branch `optimizer-dce`, PR #52) — DONE

**The verified `deadCode : Pass` is landed, `sorry`-free, wired into
`compileSource`.** A well-scoped `let x := e` with `x` unused in the rest of its
block and `e` side-effect-free (var/lit) is dropped; sound via the whole-program
simulation (both directions) + the block `restore` erasing the removed binding,
and scope-preserving. Functional check: `{ let y:=7 let x:=y let z:=5 sstore(0,z) }`
→ dce drops `let x:=y` (4→3 statements).

Follow-ups (each a bounded extension of the same machinery): recurse into
`switch` (needs `selectSwitch` via well-founded recursion), `forLoop` bodies
(loop-iteration sim), and `funDef` bodies (a `FunsRel`/`ScopeRel` thread);
widen `SideEffectFree` to total pure builtins; the object-level soundness theorem
for `dceObject` (mirrors `simplifyObject_compileObject_correct`); gas re-pin via
the CI gas job (needs solc + corpus). Also the natural next pass, **copy
propagation** (`let y := x; rest` → `rest[y↦x]`), via the substitution lemma +
this dead-let removal.

---
### (historical) Spec change + dead-`let` (branch `optimizer-dce`, PR #52) — owner-approved

The owner authorized **weakening the spec** so binding-removal is sound (the
pointwise `EquivBlock` iff is unsound for binding-removal on ill-scoped envs;
restricting to well-scoped programs fixes it — all `solc` output is well-scoped).

**Done, `sorry`-free, `lake build` green:**
- `Spec/Scoped.lean`: the `WellScoped` judgment (`ScopedExpr/Stmt/Stmts/Cases/…`,
  over `Op`), Yul scoping rules exact (let leaks to block rest; block/if/for/
  switch bodies inner; for-init visible in cond/post/body; funDef body =
  params+rets only).
- `Spec/Pass.lean`: `Sound run := ∀ b, WellScoped b → EquivBlock b (run b)`;
  `Pass` gains `preservesScoped` (closed under `comp`/`ofList`).
- `Spec/Backend.lean` + `ObjectPass`: headline theorems gain a `WellScoped`
  precondition. **`SpecClosure.lean`/`SPEC.md` are stale — a code-owner must run
  `scripts/update-spec.sh` and approve; an agent must not self-approve.**
- `Simplify`: proven to preserve `WellScoped` (never introduces a read; keeps
  decl structure).
- `DeadCode.lean`: `SideEffectFree` fragment (var/lit) + `sef_eval` **evaluation
  adequacy** (a scoped side-effect-free expr always evaluates) — the ingredient
  the *backward* direction of dead-let removal needs.

**Ingredients — all done, `sorry`-free, committed:**
- `sef_eval` (adequacy), `stmts_append_fwd`/`_normal` (sequence split/join),
  `dom_mono`/`venvKeys_suffix` (a scoped read stays evaluable), `stmt_declVars_dom`
  /`stmts_declVars_dom` (declared vars land in the domain), `map_fst_zip_eq`.
- Plus the frame lemma (`frameAdd`/`frameRemove`) and the `restore`/`drop`
  arithmetic (worked out: `restore V VbWith = restore V VbWithout` when the
  removed binding sits at depth `|Vp|`).

**Remaining (the last big proof) — must be a *whole-program* simulation, not a
per-block congruence.** Key finding: `EquivBlock` (the `Pass.Sound` obligation
*and* what the `EquivStmt` congruences require) quantifies over **all** `V`.
Removing `let x := var y` from a block scoped in a *non-empty* `Γ` is UNSOUND
∀`V`: for `V` missing `y`, the original is stuck on `y` but the reduced program
(which no longer reads `y`) runs — breaking the iff. This is only sound because
the *top-level* block is scoped in `[]`, so during its execution every nested
block runs from an environment that already contains its scope `Γ` (`Γ ⊆ dom V`
holds by construction). Therefore DCE soundness cannot be decomposed through the
existing per-block congruences (`cond_congr`, `of_stmts`, …); it must be one
`Step`-induction over the whole top-level execution, threading `Γ ⊆ dom V` from
`Γ = []`, using `frameRemove`/`frameAdd` per removed binding and the `restore`
computation, and recursing into nested blocks/functions inline (with a `hoist`
`ScopeRel` for funDef bodies, as `Simplify` does). Then `preservesScoped`, wire
into the pipeline, re-measure gas.

## Candidate next ideas (not started)

- **`for`-loop `init`**: a `for`-specific congruence to simplify `init` too.
- **Higher-impact passes**: redundant `pop`/store elimination, branch/switch
  folding, common-subexpression elimination, trivial-function inlining
  (`cleanup_*` identity helpers, via `FunCongr`).
- **Dead `pop`/unused `let` elimination**: remove `let x := <pure e>` when `x`
  is never used and `e` is side-effect-free; drop `pop(<pure e>)`.
- **`iszero(iszero(x))` in boolean position** → `x` when the value is only used
  for truthiness (condition of `if`/`for`, arg of `iszero`).
- **Double-negation / `not(not(x))` → x**, `xor(x,x) → 0`, `sub(x,x) → 0`
  (var-only, value-preserving where sound).
- **Branch folding**: `if 0 {…}` → removed; `if <nonzero-const> {…}` → inline the
  block; `switch <const>` → selected case. Sound via the `cond`/`switch`
  congruences plus `selectSwitch` evaluation.
- **Block flattening** of nested `{ … }` with no `funDef`s and no shadowing.
- **Asm-level peepholes** (separate, Asm→Asm soundness contract).
