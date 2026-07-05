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
- `Dialect/EVM.lean` (rev `f4e6187`, `main`): `Op` enum covering the
  full user-facing Yul EVM dialect — arithmetic/comparison/bitwise/`clz`,
  `keccak256` (via an **opaque** `keccakBytes`), `pop`, memory
  (`mload/mstore/mstore8/mcopy`), storage + transient storage, calldata/code/
  returndata reads and copies, environment readers (`address` … `blobbasefee`),
  world-state reads (`balance`/`extcodesize`/…, as abstract maps in `ExecEnv`),
  `log0`–`log4`, the object-data ops (`dataoffset`/`datasize`/`datacopy`),
  halting ops; `gas`/calls/creates/`selfdestruct`/`msize` are
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
2. **`MachineState.writeBytes` is now a total `def`** (kernel-transparent) in
   the pinned evm-semantics, so memory-write proofs *are* possible: `mstore`
   is in the verified op set, its `MemMatch` preservation resting on a
   read-after-write lemma for `writeBytes` and a big-endian indexing lemma for
   `natToBytesPadded`. Those two `ByteArray` facts are currently local
   `YulEvmCompiler.Assumed` axioms (provable; see `notes/writeBytes-lemmas.md`)
   pending their move upstream. `mstore8`/`mcopy` and the copy family remain
   out until their own byte-layout lemmas are added.
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
   - arithmetic: `add sub mul div sdiv mod smod addmod mulmod exp clz`,
   - comparison: `lt gt slt sgt eq iszero`,
   - bitwise: `and or xor not byte shl shr sar`,
   - stack: `pop`,
   - storage: `sload sstore tload tstore`,
   - memory: `mload mstore`,
   - calldata: `calldataload`,
   - env/block readers: `address origin caller callvalue gasprice coinbase
     timestamp number prevrandao gaslimit chainid basefee blobbasefee`,
   - halting: `stop return revert invalid`.
   Ops outside the set compile to `none`; the `opTable` in `OpTable.lean` is the
   single source of truth. The signed arithmetic ops `sdiv`, `smod`, `sar` are
   covered (their `conv_*` lemmas bridge `BitVec.sdiv`/`srem`/`sshiftRight` to
   evm-semantics' `toSignedNat`/`ofSignedInt` via `BitVec.toInt`); the scalar
   environment/block readers go through the `EnvMatch` bundle in `StateMatch`.
   **Remaining proof debt** (one `conv_*` lemma in `Value.lean` + one `opTable`
   row + one `opStep` case each): `signextend` — a two-formulation bit-blast
   between Yul's `getLsbD`/mask form and evm-semantics' `toNat`-shift/mask form
   (blocked on a Nat all-ones-xor/complement lemma not in the pinned Mathlib).
   Follow-ups needing a further `StateMatch` extension: the size readers
   `calldatasize`/`codesize`/`returndatasize` (need length correspondences),
   `selfbalance`/`balance`/`extcodesize`/`extcodehash`/`blockhash`/`blobhash`
   (need account-map / abstract-map correspondences). Excluded until further
   work: the remaining memory/state writes through `writeBytes`
   (`mstore8 mcopy calldatacopy codecopy returndatacopy extcodecopy` — each
   needs its own byte-layout lemma, following `mstore`), `keccak256`
   (finding 4), `log*` (needs a log correspondence; addable later),
   `msize`/`gas`/calls/creates/`selfdestruct`
   (unmodeled in yul-semantics — no source derivation exists, so nothing to
   preserve).
4. Examples: compiled snippets (e.g. `sstore(0, add(1, 2)); return(0, 0)`) with
   `#eval` byte dumps.

Success criterion: `lake build` green, zero `sorry`/`axiom` in this repo, theorem
statement mentions only `YulSemantics.Run`, `compile`, `assemble`, and
`EvmSemantics.EVM.Steps`/`Eval` + the match relation.

## Milestones 3–4 — loops and functions via a labeled assembly layer

Status: **complete** (phase A + phase B sorry-free; the end-to-end theorems
`compile_correct`/`compile_correct_eval` are proved in
`YulEvmCompiler/Correctness.lean`, with axiom sets pinned in `Checks.lean`).
This section is the working design document; keep it updated as decisions
change.

### Why an intermediate layer

The milestone-1/2 pipeline compiles straight to `List Instr` and threads an
explicit byte position `pc` through `compileStmt` to compute jump targets
(`if` was the first user). That made the `if` proof reason about
fully-expanded byte arithmetic (`pc + |cCode| + 35 + |bodyCode| + pops`), and
it does not scale to loops (backward jumps to a position not yet known while
compiling) or functions (call sites far from bodies). The fix is a classic
**labeled assembly layer**:

```
Yul --compileS/compileE--> List Asm  --lowerProg (resolve labels)--> List Instr --assemble--> ByteArray
        (phase A proof)                    (phase B proof)                (existing Decode lemmas)
```

* **Phase A** (Yul big-step ⇒ Asm execution) contains *all* control-flow and
  environment reasoning — and is **gas-free and byte-free**: jumps go to
  labels, positions never appear.
* **Phase B** (Asm execution ⇒ EVM `Steps` over the assembled bytecode) is a
  *generic* per-instruction simulation proved once, by induction over the Asm
  trace; all gas accounting, decode/layout arithmetic, and jumpdest analysis
  live here, reusing `Decode.lean`/`OpStep.lean` leaves unchanged.

### The Asm IR (`YulEvmCompiler/Asm.lean`)

```
abbrev Label := Nat
inductive Asm
  | push (v : U256)       -- PUSH32 (value is *yul-side* BitVec; conv at lowering)
  | op (yop : Op)         -- a verified built-in (domain of opTable), incl. halting ops
  | dup (n : Fin 16) | swap (n : Fin 16) | pop
  | label (l : Label)     -- JUMPDEST, the target of jumps to l
  | jump (l : Label)      -- PUSH32 addr(l); JUMP
  | jumpi (l : Label)     -- PUSH32 addr(l); JUMPI   (pops the condition)
  | pushLabel (l : Label) -- PUSH32 addr(l)          (function return addresses)
  | dynJump               -- JUMP to a code address popped from the stack
```

Byte sizes are fixed per constructor (`push`/`pushLabel` 33, `jump`/`jumpi`
34, others 1), so the byte position of any *suffix* `c` of the program is
`codeSize prog - codeSize c` — independent of label resolution. Key defs:

* `defs prog : List Label` — labels defined (by `.label`), in order;
  `refs prog` — labels referenced (`jump`/`jumpi`/`pushLabel`).
* `resolve prog l : Option Nat` — byte position of the *first* `.label l`.
* `findLabel l prog : Option (List Asm)` — the suffix *after* the first
  `.label l` (CompCert-style; the Asm `jump` step lands there, and phase B
  charges PUSH+JUMP+JUMPDEST for it).
* `WFProg prog` (**decidable**, checked by the compiler at the end):
  `(defs prog).Nodup`, `refs prog ⊆ defs prog`, `codeSize prog` small.
  Because the compiler *checks* WF instead of us proving the label-counter
  discipline fresh, phase A gets `Nodup`/definedness for free from
  `compileProgram = some _` — no freshness bookkeeping anywhere.
* `lowerInstr prog : Asm → Option (List Instr)`, `lowerProg`.

### Asm semantics (`YulEvmCompiler/AsmSem.lean`)

Stack values are words or opaque code addresses (return addresses never leak
into arithmetic in compiled code):

```
inductive AVal | word (v : U256) | code (l : Label)
structure AConf where code : List Asm; stk : List AVal; yst : EvmState
inductive AStep (prog : List Asm) : AConf → AConf → Prop   -- one instruction
inductive AHalt (prog : List Asm) : AConf → EvmState → Prop -- halting op
def ASteps (prog) := Relation.ReflTransGen (AStep prog)     -- or bespoke rtc
```

`.op yop` steps by `stepOp yop args yst = some (.ok rets yst')` with stack
`args.map .word ++ σ → rets.map .word ++ σ` (halting ops go to `AHalt`).
`jump l` steps to `findLabel l prog`; `jumpi` pops a `.word`; `dynJump` pops
a `.code l`. `label` is a no-op step. The current code is always a suffix of
`prog`, which determines the byte position uniquely (suffixes of a list are
determined by their length).

### Compilation scheme (`YulEvmCompiler/Compile.lean`)

Compilation threads: layout `Γ : List Ident` (as today), a fresh-label
counter `n : Nat`, a **function-info environment** `Φ : List (List (Ident ×
FunInfo))` mirroring the semantics' `FunEnv` scope stack
(`FunInfo = {entry : Label, arity n, rets k}`, `k ≤ 1` for now), and optional
control contexts `F : Option FunCtx` (`exitLbl`, `depth = |Γ| of the function
frame`) and `L : Option LoopCtx` (`brkLbl`, `contLbl`, `depth = |Γ| at loop
scope`).

* **Blocks** two-pass: first hoist the block's `funDef`s into a new Φ-scope
  (assigning entry/exit labels), then compile statements under it — matches
  the semantics' `hoist`, supports forward references and recursion.
* **`for {init} c {post} {body}`** (at layout `Γ`, init grows it to `Γi`):
  ```
  <init>                                     -- new scope, like a block prefix
  label Lcond: <c>; op iszero; jumpi Lexit
  <body as block, L := {brk Lexit, cont Lpost, depth |Γi|}>
  label Lpost: <post as block, L := none>    -- break/continue in post: rejected
  jump Lcond
  label Lexit: pop × (|Γi| - |Γ|)
  ```
* **`break`/`continue`**: `pop × (|Γ| - L.depth); jump L.brkLbl / L.contLbl`.
* **`funDef f ps rs body`** (inline, jumped over):
  ```
  jump Lskip
  label Lentry: <body as block, Γf = ps ++ rs, F := {exit Lexit, depth |ps|+|rs|}, L := none>
  label Lexit: pop × |ps| ; (if k=1: swap1) ; dynJump
  label Lskip:
  ```
  Callee stack frame on entry: `[p1..pn, r1..rk (zeros), .code Lret, callerσ]`
  — the variable region literally mirrors the semantics' callee `VEnv`
  `params.zip args ++ bindZeros rets`, and the return address sits *below*
  it, in the callee's arbitrary `σ`.
* **`leave`**: `pop × (|Γ| - F.depth); jump F.exitLbl` (locals above the
  function frame are statically known at each site).
* **`call f args`** (expression position; `k = rets f ≤ 1`):
  ```
  pushLabel Lret; push 0 × k; <args right-to-left>; jump Lentry
  label Lret:                                -- stack: [r1..rk, τ, vars, σ]
  ```
* Everything else compiles as before (with `.op yop` now carrying the *Yul*
  op; `opTable` is consulted only at lowering).
* `compileProgram`: compile → **check `WFProg` (decidable)** → `lowerProg`.

### Phase A statement shapes (`YulEvmCompiler/SimAsm.lean`)

All relative to a fixed whole program `prog` with `(defs prog).Nodup`,
"fragment placement" expressed as `prog = pre ++ asm ++ c` (so label lookups
inside `asm` land where the compiler put them):

* `ASimE`: from `⟨asm ++ c, τ ++ wimg V ++ σ, yst⟩` reach
  `⟨c, vs.map .word ++ τ ++ wimg V ++ σ, yst'⟩` (`wimg V = vimg`-analog with
  `.word`; `τ : List AVal` may contain return addresses).
* `ASimS`: region `wimg V ++ σ → wimg V' ++ σ`, code `asm ++ c → c`.
* Halt variants end in `AHalt`.
* **New outcome shapes**: for `o ∈ {break, continue, leave}` the fragment
  ends at `⟨findLabel ctxLbl prog, wimg (V'.drop (V'.length - depth)) ++ σ, yst'⟩`
  — the statically-emitted pops realize the semantics' `restore` chain.
* **`FEnvOK prog funs Φ`**: scopewise agreement of the semantic `FunEnv`
  with Φ; for each resolvable `f`: its `FunInfo` labels anchor compiled
  prologue/body/epilogue fragments *somewhere in `prog`* (they were emitted
  inline, so containment follows from the enclosing block's containment),
  compiled against the Φ-tail matching the semantics' `cenv`. This is the
  hypothesis the `callOk`/`callHalt` cases consume; recursion is handled by
  the derivation induction as usual.
* The motive extends today's with the new outcome disjuncts and
  `FEnvOK`/context-realization hypotheses; loop iteration (`.loop c post
  body` code class, currently `trivial`) becomes a real case driving the
  `label Lcond … jump Lcond` cycle.

### Phase B statement (`YulEvmCompiler/LowerCorrect.lean`)

Simulation invariant between `AConf ⟨c, σ, yst⟩` and EVM `State s` (given
`WFProg prog`, `lowerProg prog = some is`, `code = assemble is`):

* `c` is a suffix of `prog`; `s.pc = UInt256.ofNat (codeSize prog - codeSize c)`;
* `s.stack = σ.map (mapAVal prog)` where `mapAVal (.word v) = conv v`,
  `mapAVal (.code l) = UInt256.ofNat (resolve prog l).get!` — total thanks to
  the stack invariant `StkOK` (every `.code l` on the stack has `l ∈ defs`),
  preserved because `pushLabel` only pushes referenced (⊆ defined) labels;
* `FrameOK code s`, `StateMatch yst s` as today.

Per `AStep` case: 1–3 EVM steps via the existing `pushStep`/`opStep`/
`dupStep`/`swapStep`/`popStep`/`jumpdestStep`/`jumpi*Step` (+ a new
unconditional `jumpStep` to add to `OpStep.lean`), with an existential gas
bound; `isValidJumpDest` at label positions from `isValidJumpDest_boundary`
(labels lower to `JUMPDEST` at instruction boundaries). Compose along
`ASteps` by induction (bounds add). `AHalt` maps to the halting `opStep`.
Gas stays derivation-bounded: the Asm trace pins every op's arguments, so
per-step bounds (`opBound`) sum along the trace.

### Phase A detailed design (settled while implementing; keep in sync)

Status: phase B (`LowerDefs.lean` + `LowerCorrect.lean`) is **done and
sorry-free**; `OpStep.lean` gained `pushStepU` (arbitrary-word push) and
`jumpStep`. Known pitfalls encountered: `congr 1` on `mkCode`/byte-term
equalities diverges (use `congrArg` + targeted `simp only`; see
`assemble_at₁/₂/₂'`), and `omega` diverges in the large multi-step contexts
(use the pure-term `gasChain₂'/₃'` from `LowerDefs.lean`).

Phase A status (`SimAsm.lean`, namespace `YulEvmCompiler.SimA`): **complete
and sorry-free.** All definitions, composition lemmas, leaf lemmas
(var/assign/zeros/pops/trim/if machinery/epilogue/`wimg_rets`),
compile-equation inversions, and the motive are in place. The `sim`
induction is proved for every case: lit, var, builtin{Ok,Halt,ArgsHalt},
args{Nil,Cons,RestHalt,HeadHalt}, funDef, block, letZero, letVal, letHalt,
assignVal, assignHalt, exprStmt(SHalt), ifTrue/ifFalse/ifHalt, switch
(vacuous), break, continue, leave, seqNil, seqCons, seqStop, forLoop,
forInitHalt, all 7 loop-class cases, callArgsHalt, **`callOk`, `callHalt`**,
and **`hoist_ok`**.

**Resolved `sorry`s** (all three now proved):
1. `hoist_ok` (block-entry FEnvOK extension): proved via the helper
   `hoist_forall2`, which walks the block's statements in lockstep with
   `hoist`/`hoistInfos`. The fixed outer scope (in `Φfull`) supplies each
   `funDef`'s label through `find?`; `find?_suffix_nodup` (Nodup +
   suffix ⇒ `find?` hits the entry) makes the compiled `lookupF` label and
   the hoisted entry coincide, so no counter arithmetic is needed. Each
   `funDef`'s inline `FunOK` comes from `stmt_funDef_inv` +
   fragment-infix reasoning.
2. `callOk`: `expr_call_inv` → `.pushLabel`/`push_zeros`/args-IH prologue →
   `jump info.entry` into the body (`FunOK.placed` + `findLabel_boundary`) →
   body-IH; normal and leave outcomes converge at the exit label
   (`block_len_le` makes leave's `trim |Γf|` a no-op), then `asim_epilogue`
   returns to the call site with `wimg_rets`-agreeing values.
3. `callHalt`: same prologue, body-IH halt arm.

After `sim`: the top-level theorems `compile_correct` /
`compile_correct_eval` (`YulEvmCompiler/Correctness.lean`) are **done**.
They invert the pipeline (`compileProgramAsm_inv`; `wfCheck` ⇒ `Nodup`),
take the `Run` = block rule to a `.stmts prog` derivation, establish the
initial `FEnvOK` via `hoist_ok`, run phase A `sim`, compose with phase B's
`asteps_sim`/`arun_halt_sim`, and cap a fall-through `.normal` with the
implicit-STOP `stopStep`. Axioms pinned in `Checks.lean` (classical only,
no `sorryAx`). The old milestone-1/2 pipeline has been **removed**:
`Compile.lean`/`Correctness.lean`/`Examples.lean` are gone, the shared
`opTable` moved to `OpTable.lean`, and `Checks.lean`/`README.md` now track
only the `compileA_*` theorems.

Phase A definitions (`SimAsm.lean`), all under section hypotheses
`prog : List Asm` and `hnodup : (labelDefs prog).Nodup`:

* `wimg (V : VEnv yul) : List AVal := V.map (fun p => .word p.2)`;
  `trim depth V := V.drop (V.length - depth)`.
* `ASimE yst V off asm vs yst'` — ∀ placement `prog = pre ++ asm ++ c` and
  `τ : List AVal` with `τ.length = off` (τ may contain return addresses):
  `ASteps ⟨asm ++ c, τ ++ wimg V ++ σ, yst⟩ ⟨c, words vs ++ τ ++ …, yst'⟩`.
* `ASimS yst V asm yst' V'` — region `wimg V ++ σ → wimg V' ++ σ`.
* `ASimEHalt`/`ASimSHalt` — end in `∃ conf, ASteps … conf ∧ AHalt conf yst'`.
* `ASimNL yst V asm yst' V' l depth` — non-local exit (break/continue/
  leave): ∀ placement and ∀ `cL` with `findLabel l prog = some cL`, steps to
  `⟨cL, wimg (trim depth V') ++ σ, yst'⟩`. The statically emitted pops
  realize the semantics' `restore` chain; σ is unchanged from the fragment's
  entry (statements only touch their region).
* Statement motive (per outcome `o` of `.sres V' yst' o`), hypotheses:
  `Γ = names V`, `FEnvOK prog funs Φ`, depth guards
  (`L`/`F`'s `.depth ≤ V.length`), compile equation. Conclusions:
  - normal: `Γ' = names V' ∧ ASimS …`;
  - halt: `ASimSHalt …`;
  - break/continue: `∃ lc, L = some lc ∧ V.length ≤ V'.length ∧
    ASimNL … lc.brk/lc.cont lc.depth`;
  - leave: `∃ fc, F = some fc ∧ V.length ≤ V'.length ∧ ASimNL … fc.exit
    fc.depth`.
  The `V.length ≤ V'.length` fact + `depth ≤ V.length` make the
  `trim`/`restore` composition at block boundaries go through
  (`trim d (restore V V') = trim d V'`).
* Loop motive (`.loop c post body` class): stated against the suffix
  `cIter` with `findLabel lcond prog = some cIter`, where
  `cIter = cCode ++ [.op .iszero, .jumpi lexit] ++ bodyAsm ++ .label lpost
  :: postAsm ++ .jump lcond :: cRest` and `findLabel lexit prog` =
  the suffix after the loop's exit label — self-contained across
  iterations (the trailing `jump lcond` re-enters `cIter`, so the loop IH
  applies verbatim). Conclusion for `o = normal`: reach that exit suffix
  with `wimg Vend ++ σ`; halt/leave analogous.
* **`FunOK prog decl info Φv`**: `info.arity = decl.params.length`,
  `info.rets = decl.rets.length ≤ 1`, `(params ++ rets).Nodup` (guarded at
  compile time — needed so the epilogue's stack region agrees with
  `VEnv.get`-based return values), and `placed`: the fragment
  `.label info.entry :: bodyAsm ++ .label lexit :: pops ++ swap? ++
  [.dynJump]` is an **infix** of `prog`, with the body's `compileBlock
  Φv (params ++ rets) (some ⟨lexit, |params|+|rets|⟩) none` equation.
* **`FEnvOK prog : FunEnv yul → FMap → Prop`** — inductive, scopewise
  `List.Forall₂` with `Φv := scopeI :: restI` for every entry (matching
  `lookupFun`'s returned `cenv`). Key lemmas: lookup consistency
  (`lookupFun`/`lookupF` results correspond) and **`hoist_ok`** (at block
  entry, `hoistInfos` + the block's `compileStmts` success + placement of
  the block's asm in `prog` ⇒ `FEnvOK (hoist body :: funs) (scope :: Φ)`)
  — proved by walking the block's statements, collecting each `funDef`'s
  inline fragment.
* Call execution sketch (`callOk`): `pushLabel lret` (definedness from the
  fragment's own `.label lret` placement) · `k` zero pushes · args-IH at
  `off + 1 + k` · `jump entry` (via `FunOK.placed` + `findLabel_boundary`)
  · body-IH (`Γf = params ++ rets`, `F = ⟨lexit, |Γf|⟩`, `L = none`;
  `names (params.zip argvals ++ bindZeros rets) = params ++ rets` needs the
  arity premise) · epilogue: `|params|` pops, `swap 0` if `k = 1`,
  `dynJump` back to `lret`'s suffix. Normal and leave outcomes converge at
  the exit label (leave's `trim |Γf|` is a no-op since the restored VEnv
  has length `|Γf|`).
* `break`/`continue` in a loop's `post`, and `switch`, stay rejected.

### Scope decisions

* Function return arity `k ≤ 1` (multi-value returns need multi-value
  `let`/assign machinery and a swap-network epilogue; deferred).
* `switch` still rejected (if-chains; mechanical, later).
* `break`/`continue` inside a loop's `post` block: rejected (no semantics
  rule; compile with `L := none` there).
* Old `Compile.lean`/`Correctness.lean`/`Examples.lean` have been **removed**
  now that the new pipeline's top-level theorem landed. The active file set is
  `OpTable.lean`, `Asm.lean`, `AsmSem.lean`, `Compile.lean`,
  `LowerDefs.lean`, `LowerCorrect.lean`, `SimAsm.lean`, `Correctness.lean`,
  and `Examples.lean`; `Instr/Decode/Value/StateRel/OpStep` survive
  (`OpStep` gained `pushStepU`/`jumpStep`, and the shared `opTable` moved from
  the old `Compile.lean` into `OpTable.lean`).

[powdr-labs/yul-semantics]: https://github.com/powdr-labs/yul-semantics
[powdr-labs/evm-semantics]: https://github.com/powdr-labs/evm-semantics
