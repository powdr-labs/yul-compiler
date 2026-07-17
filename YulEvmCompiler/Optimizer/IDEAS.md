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
  there is no `funDef`-body congruence upstream (explicitly deferred). To recurse
  into function bodies soundly we prove a **function-environment congruence**
  locally (see `Simplify`, below).
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

### 🚧 `Simplify` (`Implementation/Simplify.lean`) — IN PROGRESS (this branch)
A local **constant-folding + neutral-element** expression simplifier that
recurses through the whole program, *including function bodies*.

- **Constant folding**: `builtin op args` with every arg a literal and `op` pure
  → replace with the literal `number (v.toNat)` where `v = f (args.map litValue)`.
  One uniform soundness lemma over the pure-op set (result value is a total
  function of the literal args, state unchanged).
- **Neutral-element identities** (operand is a `var`, kept on the RHS):
  `add(x,0)`, `add(0,x)`, `sub(x,0)`, `mul(x,1)`, `mul(1,x)`, `div(x,1)`,
  `or(x,0)`, `or(0,x)`, `xor(x,0)`, `xor(0,x)`, `and(x,MAX)`, `and(MAX,x)`,
  `shl(0,x)`, `shr(0,x)` → `x`. Collapsed to two parameterized lemmas
  (`[var,lit]` and `[lit,var]`) discharged by a per-identity `stepOp` reduction.
- **Foundation contributed**: a **function-environment congruence**
  (`FunsRel` + `Step.funs_congr` + `EquivBlock.of_stmts_funs`) proving that
  replacing function bodies by `EquivBlock`-equivalent bodies (same signatures)
  preserves whole-block semantics. This is the machinery `YulSemantics.Equiv`
  explicitly defers, and it unlocks *any* pass that rewrites inside functions.
- **Wiring**: inserted into `compileSource`'s block branch (`compile (P.run …)`);
  soundness is `Pass.optimize_then_compile_correct`. Object path left unchanged.
- **Target**: `solidity-yul-optimizer-gas-baseline.txt` (+ evmCodeTransform).

## Candidate next ideas (not started)

- **Object-path wiring**: apply `Simplify` to object code blocks. Needs the
  layout-stability argument above (fold before/independent of resolution, or a
  cross-layout relation) to keep `compileObject_correct`. Unlocks the real `.sol`
  gas baselines.
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
