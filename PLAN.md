# Verified Yul → EVM bytecode compiler

A non-optimizing compiler from Yul to EVM bytecode, written in Lean 4, with a
machine-checked proof that compilation preserves semantics:

* **Source semantics**: [powdr-labs/yul-semantics] — the big-step relational judgment
  `YulSemantics.Step` over the gas-free EVM dialect (`YulSemantics.EVM.evm`,
  `Value := BitVec 256`).
* **Target semantics**: [powdr-labs/evm-semantics] — the small-step relation
  `EvmSemantics.EVM.Step` (and its big-step closure `Eval`), over
  `UInt256 := Fin (2^256)` words, with gas.

Both repos pin the same toolchain (`leanprover/lean4:v4.31.0`) and the same Mathlib
revision (`v4.31.0`), so this project depends on both as ordinary Lake packages and
states one theorem quantifying over both semantics — no shallow re-encoding of either.

## The correctness statement (shape)

For a program `prog` in the supported fragment with `compile prog = some code`:

> If the Yul big-step semantics runs `prog` from machine state `st₀` to `st'` with
> outcome `o` (`Run EVM.evm prog st₀ V' st' o`), then there is a gas bound `g₀` such
> that from **every** initial EVM state `s₀` that matches `st₀`, executes the
> assembled bytecode `assemble code`, and has `g₀ ≤ s₀.gasAvailable`, there is an
> execution `Steps s₀ s'ᵉ` ending in a done state (`halt ≠ Running`, `callStack = []`)
> whose world state matches `st'` and whose `ExecutionResult` matches `o`/`st'.halted`.

Design decisions baked into that statement:

* **Forward simulation (∃ target run), not equivalence.** The target `Step` relation is
  mildly non-deterministic (overlapping exception rules such as `outOfGas` vs.
  `stackUnderflow` may both fire), so "the compiled code *may* produce the matching
  result" is what is provable. Combined with the source derivation this is the standard
  compiler-correctness direction. A strengthening pass (using target-side determinism
  restricted to non-exception runs) can come later.
* **Gas is existentially bounded.** yul-semantics deliberately does not model gas;
  evm-semantics charges it. The theorem therefore holds *for all sufficiently large
  initial gas*. Internally the simulation invariant is: each compiled fragment, run
  from any matching state with `gas ≥ bound(D)` (a bound computed from the *source
  derivation* `D`, since memory-expansion costs depend on the argument values pinned by
  `D`), consumes at most `bound(D)` gas. Bounds compose by addition across sequencing.
  The SSTORE EIP-2200 sentry (`gas ≤ 2300 → OOG`) is absorbed into the per-op bound.
* **Match relation** `st ∼ s` between `YulSemantics.EVM.EvmState` and
  `EvmSemantics.EVM.State`:
  - memory: `st.memory a = (s.memory[a] or 0 beyond size)` pointwise;
  - storage / transient storage: `st.storage k = (s.accountMap s.executionEnv.address).storage (conv k)`
    pointwise (Yul's single flat storage is the *executing account's* storage);
  - halt: `st.halted` corresponds to `s.halt`/`s.hReturn`
    (`stop ↦ Success`, `return ↦ Returned+payload`, `revert ↦ Reverted+payload`,
    `invalid ↦ Exception InvalidInstruction`; `none ↦ Running`);
  - plus frame-level side conditions: `callStack = []`, `permitStateMutation = true`,
    `codeAddr` is not a precompile, `fork = Cancun` (all supported ops are active
    there; parameterizing over `fork ≥ Cancun` is a later generalization).
* A Yul `.normal` outcome means the compiled code runs off the end of the bytecode;
  `Decode.decodeAt` yields an implicit `STOP` there (Yellow-Paper zero padding), so the
  target halts with `.Success` — i.e. straight-line Yul that falls through behaves
  like `stop()`.

## Survey of the two semantics (what the proof plugs into)

**yul-semantics** (`YulSemantics.*`):
- `Ast.lean`: `Expr Op` (lit / var / builtin / call), `Stmt Op`, `Outcome`.
- `Dialect.lean`: dialect interface; `BuiltinResult` (`ok rets st` / `halt st`).
- `Dialect/EVM.lean` (rev `dc76dd5`, "Add more opcodes"): `Op` enum covering the
  full user-facing Yul EVM dialect — arithmetic/comparison/bitwise/`clz`,
  `keccak256` (via an **opaque** `keccakBytes`), `pop`, memory
  (`mload/mstore/mstore8/mcopy`), storage + transient storage, calldata/code/
  returndata reads and copies, environment readers (`address` … `blobbasefee`),
  world-state reads (`balance`/`extcodesize`/…, as abstract maps in `ExecEnv`),
  `log0`–`log4`, halting ops; `gas`/calls/creates/`selfdestruct`/`msize` are
  enumerated but unmodeled (`stepOp = none`). `EvmState` is
  `memory : Nat → UInt8`, `storage/transient : U256 → U256`, `env : ExecEnv`,
  `returndata : List UInt8`, `logs : List LogEntry`,
  `halted : Option (HaltKind × List UInt8)`; `evm : Dialect` has
  `Builtin op args st r ↔ stepOp op args st = some r`.
- `BigStep.lean`: single indexed inductive `Step D funs V st code res` covering
  expressions, argument lists (**right-to-left**), statements, sequences, loops;
  `Run` for whole programs. Induction over a derivation is a standard
  `induction … with`.

**evm-semantics** (`EvmSemantics.*`):
- `EVM/State.lean`: `State extends SharedState` with `pc`, `stack : List UInt256`,
  `halt : HaltKind`, `callStack`.
- `EVM/Step.lean`: `StepRunning` (one constructor per opcode; premises
  `h_op : s.decodedOp = some op`, `h_gas : cost ≤ s.gasAvailable`, `h_stack`;
  post-state a flat record update subtracting the exact cost), `StepReturn`,
  and the wrapper `Step` (`running` guard: `halt = .Running` **and**
  `isPrecompile … = false`).
- `EVM/BigStep.lean`: `Steps` (rtc), `Eval s r` (ends in done state, projected
  through `State.toResult`).
- `EVM/Decode.lean`: `decodeAt code pc`; past-the-end ⇒ implicit `STOP`;
  PUSH immediates via `bytesToBigEndianNat`; DUPN/SWAPN immediates folded into the
  `Operation` value.
- `Data/UInt256.lean`: `Fin (2^256)` wrapper with per-opcode arithmetic
  (`sdiv`/`smod` via `Int.tdiv`/`tmod`, `sar` via `Int` division, etc.).
- Storage is `Std.HashMap` with `get`/`set` + simp lemmas; the world is
  `AccountMap`; memory is a `ByteArray` with zero-padded reads (`readPadded`,
  `readWord`) and `writeBytes` for writes.

### Upstream findings (blockers discovered during the survey)

1. **EIP-8024 (`DUPN`/`SWAPN`/`EXCHANGE`) is not activated on any modeled fork.**
   `Operation.availableInFork` returns `false` for all three on every `Fork`
   (Frontier … Osaka), and `State.decoded` gates on it, so bytes `0xe6..0xe8`
   always halt with `InvalidInstruction`. The `Step`/`stepF` rules for them exist
   and are exercised nowhere. Milestone 1 (no variables) emits no DUPN/SWAPN, so
   this does not block it; **milestone 2 (variables) requires an upstream change**
   (e.g. an `Amsterdam` fork entry activating EIP-8024). The compiler IR and the
   planned stack-layout scheme already use them.
2. **`MachineState.writeBytes` is a `partial def`** and therefore opaque to the
   kernel: no lemma about the memory contents after `MSTORE`/`MSTORE8`(/`MCOPY`)
   is provable against the pinned evm-semantics. Until it is totalized upstream
   (the recursion is trivially structural) and equipped with a `getElem` lemma,
   `mstore`/`mstore8` cannot be in the *verified* op set. They remain in the IR
   and the compiler; `compile` simply reports them as unsupported for now.
3. Reads are unaffected: `readPadded`/`readWord` are total, so `mload`,
   `return(p,s)`, `revert(p,s)` **are** verifiable (their payloads only read
   memory), as long as no memory *write* precedes them.
4. **`keccak256` is opaque on both sides, but they are *different* opaques**:
   yul-semantics has `opaque keccakBytes : List UInt8 → U256`, evm-semantics has
   `opaque keccak256 : ByteArray → UInt256`. No agreement between two unrelated
   opaque constants is provable, so `keccak256` support needs either (a) an
   explicit agreement hypothesis on the main theorem, or (b) an upstream bridge
   (e.g. yul-semantics parameterizing the hash). Deferred.

## Architecture of this repo

```
YulEvmCompiler/
  Instr.lean        -- the tiny IR: PUSH32 v | plain single-byte op | DUPN n | SWAPN n
                    --   + assemble : List Instr → ByteArray
  Compile.lean      -- compileExpr / compileStmt / compileProgram : … → Option (List Instr)
  Decode.lean       -- layout lemmas: decoding assembled code at instruction boundaries
  Value.lean        -- conv : BitVec 256 → UInt256 + per-op agreement lemmas
                    --   (yul stepOp op ⟷ evm-semantics UInt256 ops)
  StateRel.lean     -- the match relation st ∼ s, init/final match, frame invariant
  Correctness.lean  -- gas-bound invariant + the simulation induction + main theorem
  Examples.lean     -- #eval'd sample programs and sanity checks
```

### The IR and the compilation scheme

`Instr` is deliberately minimal and *loss-free to assemble* (each constructor maps to
a fixed byte sequence, so decode lemmas are per-constructor):

```
inductive Instr
  | push  (v : UInt256)   -- PUSH32 (0x7f) + 32-byte big-endian immediate; non-optimizing
  | op    (o : Operation) -- any zero-immediate opcode, e.g. ADD, SLOAD, RETURN
  | dupN  (n : Fin 256)   -- 0xe6 n   (reserved for milestone 2: variable reads)
  | swapN (n : Fin 256)   -- 0xe7 n   (reserved for milestone 2: assignments)
```

Compilation (milestone 1, straight-line fragment):

* `lit l` ⇒ `push (conv (litValue l))` — the compiler pushes the *interpreted* literal,
  so all literal forms (number/bool/string) are supported without well-formedness
  side conditions.
* `builtin op [a₁, …, aₙ]` ⇒ `code(aₙ) … code(a₁) ; OP` — arguments are emitted last
  arg first, matching Yul's specified **right-to-left** argument evaluation *and*
  leaving `a₁`'s value on top, which is the EVM operand order (`sub(a,b)` compiles to
  a stack `[a, b]` and `SUB` computes `a - b`).
* `exprStmt e` ⇒ `code(e)` (the semantics guarantees `e` yields zero values).
* A program (list of statements) concatenates; falling off the end is the implicit
  `STOP`.
* `var` / `call` / control flow / declarations ⇒ `none` (later milestones).

Everything is `Option`-valued: the compiler *rejects* what it cannot yet verify, so
the repo stays sorry-free while coverage grows op by op.

### The simulation proof, decomposed

1. **Decode/layout lemmas** (`Decode.lean`). For `code = pre ++ assemble is ++ post`
   and `pc = pre.size` with `is = i :: rest`: `decodeAt code pc` returns `i`'s
   operation (and, for `push`, the immediate — via a `bytesToBigEndianNat`/32-byte
   round-trip lemma). This isolates all `ByteArray` index arithmetic in one file.
2. **Value agreement** (`Value.lean`). `conv : BitVec 256 → UInt256` (`toNat`-based,
   an injection) with one lemma per supported op, e.g.
   `conv (a + b) = conv a + conv b`, `conv (yul.b2w (a.ult b)) = UInt256.lt (conv a) (conv b)`, ….
   These are the only number-theoretic proofs, and each is independent. The hairy ones
   (`sdiv`, `smod`, `sar`, `signextend`) can land incrementally; an op enters the
   compiler's supported set exactly when its lemma exists.
3. **State correspondence** (`StateRel.lean`) as described above, plus preservation
   lemmas for each state-touching op (storage via the `Std.HashMap` simp lemmas).
4. **Simulation** (`Correctness.lean`). One induction over the Yul `Step` derivation
   with per-syntactic-class motives:
   - `args es ⇓ vals vs, st'` ⟹ compiled arg block takes any matching `s` (pc at
     block start, stack σ, gas ≥ bound) to `pc + len`, stack `map conv vs ++ σ`,
     matching `st'`, consuming ≤ bound.
   - `expr e ⇓ …` similarly (one pushed value, or a halted target state for `.halt`).
   - `stmt/stmts ⇓ …` with outcome `normal` (reach block end) or `halt` (target
     halted mid-way, matching payload).
   - Main theorem = the `stmts` case wrapped by `Run`, plus the implicit-`STOP`
     step for the `.normal` outcome, packaged into `Steps`/`Eval`.

### Extension path (how this design scales to full Yul)

* **Variables (milestone 2).** Standard stack scheduling for a non-optimizing
  compiler: the compile-time context is a stack layout `List Ident` mirroring the
  runtime operand stack. `var x` ⇒ `DUPN (depth x)`; `assign x` ⇒ `SWAPN (depth x); POP`;
  `let` grows the layout; block exit pops. DUPN/SWAPN's `Fin 256` range removes
  DUP16/SWAP16 ceiling concerns without slot spilling. The simulation invariant
  gains "runtime stack realizes the layout under `VEnv`". *Blocked on upstream
  finding 1.*
* **Control flow (milestone 3).** `if`/`switch`/`for` compile to
  `JUMPI`/`JUMP`/`JUMPDEST` with a label-then-resolve assembler pass; the decode
  lemmas extend to `isValidJumpDest` facts (jumpdest analysis over assembled code).
  `break`/`continue` need a compile-time loop-context; the Yul outcomes
  `break/continue/leave` enter the simulation motives.
* **Functions (milestone 4).** Non-optimizing calling convention: caller pushes a
  return label + args, `JUMP` to the function's `JUMPDEST`; callee body runs with a
  fresh layout; `leave` jumps to the epilogue that reorders rets and jumps back.
  Yul's scoping (functions see no outer variables) matches the fresh-layout scheme.
* **Objects / `datacopy` / constructors (milestone 5),** then optimization passes
  (each pass verified against the Yul semantics only, reusing
  `YulSemantics.Equiv`/`Rewrites`; the backend theorem composes at the end).

## Milestone 1 — this iteration

Deliverables:

1. Lake project depending on both semantics repos (pinned revs, toolchain v4.31.0).
2. `Instr`/`assemble`, the compiler for the straight-line fragment
   (no variables, no user functions, statements are built-in expression statements).
3. The main theorem, **proved without `sorry`** (`#print axioms` shows only
   `propext`, `Classical.choice`, `Quot.sound`), for the supported op set:
   - arithmetic: `add sub mul div mod addmod mulmod exp clz`,
   - comparison: `lt gt slt sgt eq iszero`,
   - bitwise: `and or xor not byte shl shr`,
   - stack: `pop`,
   - storage: `sload sstore tload tstore`,
   - memory reads: `mload`,
   - halting: `stop return revert invalid`.
   Ops outside the set compile to `none`; the table in `Compile.lean` is the single
   source of truth. **Remaining proof debt** (each is one `conv_*` lemma in
   `Value.lean` plus one `opTable` row + one `opStep` case): `sdiv`, `smod`,
   `signextend`, `sar` — the two's-complement agreements between `BitVec` ops and
   evm-semantics' `Int.tdiv`/`tmod`-based definitions. Mechanical follow-ups with
   the same proof shape: the nullary environment readers `address … blobbasefee`,
   `calldatasize`/`codesize`/`returndatasize`, `calldataload`,
   `balance`/`extcodesize`/`extcodehash`/`blockhash`/`blobhash`. Excluded until
   upstream changes land: memory/state writes through `writeBytes`
   (`mstore mstore8 mcopy calldatacopy codecopy returndatacopy extcodecopy`,
   upstream finding 2), `keccak256` (finding 4), `log*` (needs a log
   correspondence; addable later), `msize`/`gas`/calls/creates/`selfdestruct`
   (unmodeled in yul-semantics — no source derivation exists, so nothing to
   preserve).
4. Examples: compiled snippets (e.g. `sstore(0, add(1, 2)); return(0, 0)`) with
   `#eval` byte dumps.

Success criterion: `lake build` green, zero `sorry`/`axiom` in this repo, theorem
statement mentions only `YulSemantics.Run`, `compile`, `assemble`, and
`EvmSemantics.EVM.Steps`/`Eval` + the match relation.

[powdr-labs/yul-semantics]: https://github.com/powdr-labs/yul-semantics
[powdr-labs/evm-semantics]: https://github.com/powdr-labs/evm-semantics
