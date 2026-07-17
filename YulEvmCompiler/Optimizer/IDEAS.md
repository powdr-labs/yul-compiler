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

Gas (real Solidity contracts, `checkSolidityGas`): `libsolidity/gasTests` — 12/12
fixtures down, 0 regressions (`dispatch_large` 97748→97586, `abiv2` 9377→9341, …).
`objectCompiler` yul corpus — 3 down. The single end-to-end "bytecode simulates
the *original object*" theorem would additionally want a resolution congruence
`EquivBlock (resolve L b) (resolve L (P.run b))`; the layout-coupling below blocks
that as a general lemma, but it does not weaken the shipped guarantee (correct
compilation of a per-block-equivalent tree).

`Pass.optimizeTopCode` + `Pass.optimizeTop_compileObject_correct` remain as the
stricter single-object theorem for the offset-free/leaf fragment.

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

## Candidate next ideas (not started)

- **Resolution congruence** `EquivBlock (resolve L b) (resolve L (P.run b))` (a
  structural induction mirroring the pass, using that resolution touches only
  `dataoffset`/`datasize`/`datacopy` — disjoint from the pure ops the pass folds).
  Gives the single end-to-end "artifact simulates the *original* object" theorem.
- **`for`-loop `init`**: a `for`-specific congruence to simplify `init` too.
- **Higher-impact passes** (the real gas lever): dead/unused-`let` elimination,
  redundant `pop`/store elimination, branch/switch folding.
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
