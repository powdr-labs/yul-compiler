# The `yul-ssa-cfg` dialect — design and plan

> Status: landed and **sorry-free**. The code and tests landed first so the gas
> wins were measurable before the proof investment; the proofs have since
> caught up, and `SsaCfg.compileViaSsa_correct` now checks with the standard
> `[propext, Classical.choice, Quot.sound]` footprint. The "proof plan" section
> below is kept as the historical map of how the obligations were carved up.

## Why a second IR

The verified Yul→Yul optimizer has taken the source-level pipeline far, but
the remaining gas gap against solc (issue #65) is dominated by **stack
traffic**: POP/DUP/SWAP sequences the backend emits because variables live at
fixed operand-stack positions dictated by the source `VEnv` layout. Fixing
that at the Yul level is structurally impossible — Yul has named, scoped,
mutable variables, so any Yul→Yul pass must keep them; the freedom to place
values where the *uses* want them only exists in a representation where
variables have been dissolved into dataflow edges. That representation is an
SSA control-flow graph. solc's own next-generation backend
(`libyul/backends/evm/SSAControlFlowGraph*`) makes the same move for the same
reason.

Once the program is an SSA CFG, a family of optimizations that are hard or
impossible on Yul become one-pass dataflow problems, and — the actual payoff —
**stack scheduling** can lay values out per basic block driven by liveness
and next-use distance instead of by lexical scope.

## The dialect lattice

```
        Yul  ──────────────────────────►  EVM      (existing, verified)
         │        compile
         │
         │ toSsa (Option-valued)
         ▼
     yul-ssa-cfg  ──[SSA passes]──►  yul-ssa-cfg
         │
         │ fromSsa (codegen: SSA → labeled Asm)
         ▼
   List Asm ──wfCheck/stackOK2/lowerProg/assemble──►  EVM   (existing, reused)
```

* `{yul, yul-ssa-cfg}` both generate EVM.
* `yul` generates `yul-ssa-cfg`.
* `yul-ssa-cfg` is **not** re-lifted to Yul (out-of-SSA back into named
  scoped variables buys nothing and would need its own proof). The pipeline
  is therefore: optimize Yul→Yul as much as possible (today's verified
  pipeline), then lower once to `yul-ssa-cfg`, optimize there, then to EVM.

## Reuse: the SSA backend ends at the existing `Asm` layer

The single most important architectural decision: `fromSsa` targets the
**existing labeled `Asm` IR**, and the SSA entry point runs the exact same
final gates as `compile` — `wfCheck`, the `stackOK2` overflow certificate,
`lowerProg`, `assemble`. Consequences:

* Phase B (`asteps_sim`/`arun_halt_sim`: Asm execution → EVM `Steps`, all
  gas/byte/jumpdest reasoning) is reused **verbatim** — those proofs never
  mention who produced the Asm.
* The stack-overflow gate and the assembler are reused verbatim.
* The only new proof obligations are gas-free, byte-free, label-level
  simulations:
  1. `toSsa` sound: a Yul `Run` derivation maps to an SSA-CFG execution with
     the same final state and outcome;
  2. each SSA pass sound: SSA execution equivalence;
  3. `fromSsa` sound: an SSA-CFG execution maps to `ASteps` over the emitted
     Asm.

## Prior art (research digest)

The design tracks what solc's own next-generation backend converged on
(`libyul/backends/evm/ssa/`, PRs #15359 construction, #16464 stack layout,
#16498 codegen, #16767 spilling; experimental since 0.8.35) and the
literature it cites in-source:

* **Construction**: Braun et al., *Simple and Efficient Construction of
  Static Single Assignment Form*, CC 2013 — SSA directly from the AST, no
  dominance frontiers; on structured (hence reducible) Yul it yields pruned,
  minimal SSA. solc's builder cites it explicitly; there is a
  machine-checked precedent (Buchwald, Lohner, Ullrich, *Verified
  Construction of Static Single Assignment Form*, CC 2016, Isabelle/HOL,
  swapped into CompCertSSA).
* **φ encoding**: solc uses Pizlo-form Phi/Upsilon; MLIR/Cranelift use block
  arguments. Semantically equivalent; block arguments make the edge's
  parallel copy explicit at the jump site, which is both what the semantics
  rule and the shuffle codegen want — we use block arguments.
* **Liveness**: Rastello & Bouchez Tichadou (eds.), *SSA-based Compiler
  Design*, Springer 2022, Alg. 9.1 (two-pass, non-iterative on reducible
  CFGs); solc augments liveness with per-value **use counts** feeding the
  DUP-vs-consume decision — we adopt that.
* **Stack scheduling**: solc's new generator is a single **forward** pass in
  topological order: entry layouts inherited from predecessors (merge blocks
  pick the cheapest candidate by simulated shuffle cost), dead values become
  junk/POP, per-op shuffles computed against a symbolic stack. Antecedents:
  Koopman 1994 (intra-block stack scheduling), Shannon & Bailey 2006 (global
  stack allocation), Park et al. 2011 (treegraph scheduling); Sethi–Ullman
  gives the tree-order foundation and Bruno–Sethi (NP-completeness on DAGs)
  the license to stay greedy. COSTA/GreY (Albert, Kirchner et al.; SuperStack
  PLDI 2024) is the research line behind solc's greedy translation.
* **Verification**: CompCertSSA (Barthe, Demange, Pichardie, TOPLAS 2014)
  contributes the **equation lemma** — in strict SSA, a definition's
  equation holds at every point it dominates — the semantic backbone for
  sparse-pass proofs (SCCP/GVN verified on it in Demange et al., CC 2015).
  Edge shuffles are verified-parallel-move territory (Rideau, Serpette,
  Leroy, JAR 2008). Sea-of-nodes is contra-indicated (V8 retreated from it;
  scheduling onto a stack needs a scheduled CFG anyway).

## Layout: `Spec/` vs `Implementation/`

The subtree follows the optimizer's audit discipline (`Optimizer/Spec` vs
`Optimizer/Implementation`):

* **`Spec/`** — the audit surface: anything whose *meaning* a reviewer must
  read and agree with.
  * `Spec/Ir.lean` — what a `yul-ssa-cfg` program *is* (syntax,
    `Prog.wfCheck`).
  * `Spec/Sem.lean` — the dialect's ground-truth semantics (`Exec`/`Run`
    over the same Yul-side state and builtin relation as `AsmSem`).
  * `Spec/Dom.lean` — liveness and the decidable dominance check
    (`Prog.domCheck`), spec-tier because the pass obligations are stated
    under it.
  * `Spec/Backend.lean` — the guarantees: the three phase obligations
    (`ofBlock_sound`, `optimizeProg_sound`, `emitProg_asteps`/`_ahalt`),
    their fully-proved composition into `compileViaSsa_correct` (the exact
    `compile_correct` statement shape), and the `Optimizer.EvmBackend`
    packaging.
* **`Implementation/`** — anything that can change without moving the
  guarantee, caught by the theorems when wrong: the construction
  (`OfYul`), the SSA passes (`Passes`), the code generator (`ToAsm`), the
  pipeline/candidate selection (`Compile`), the object path (`Object`),
  the build-time differential guards (`Examples`), and the proof bodies
  (`OfYulSound`/`PassesSound`/`ToAsmSound` — like the optimizer's concrete
  passes, an auditor need not read them; they are trusted the moment the
  `Spec/Backend` obligations they discharge type-check).

## The IR

`YulEvmCompiler/SsaCfg/Ir.lean`. Values are `ValId := Nat`. Sea-of-nodes is
deliberately rejected (scheduling proofs are much harder); this is a classic
CFG of basic blocks in SSA form.

**Block arguments, not φ-nodes.** Join points receive values as *parameters
of the block* (Cranelift/MLIR style; solc uses φs with per-predecessor
entries — semantically identical). Block arguments are strictly better for
us: the parallel-copy semantics of a jump edge is explicit in the terminator
(`jump target (args)`), which is exactly the shape both the semantics rule
and the edge-shuffling codegen need, and no "all φs execute simultaneously"
side condition exists to get wrong in proofs.

```
Instr  := const (dst) (v : U256)
        | op (dsts) (yop : Op) (args : List ValId)      -- Yul builtin, incl. effects
        | call (dsts) (f : FuncId) (args : List ValId)  -- user function
Term   := jump (target : BlockId) (args : List ValId)
        | branch (cond : ValId) (ifNonzero ifZero : BlockId) (their args)
        | switch (scrut : ValId) (cases : List (U256 × BlockId × args)) (default)
        | ret (vals : List ValId)                        -- function return
        | halt (yop : Op) (args : List ValId)            -- stop/return/revert/invalid/selfdestruct
Block  := { params : List ValId, instrs : List Instr, term : Term }
Func   := { params, nRets, entry : BlockId, blocks : Array Block }
Program:= { main : Func, funcs : Array Func }
```

Yul's structured control flow (`if`/`switch`/`for`/`break`/`continue`/
`leave`) is compiled away at construction; the CFG is **reducible by
construction**, which the linearizer exploits (no relooper needed — we keep
the structured order as the block layout and only need conditional/
unconditional jumps that the `Asm` layer already has).

## Semantics

`SsaCfg/Sem.lean`: a small-step (per-instruction) relation over a register
file `Regs := ValId → Option U256` and the *same* Yul-side machine state
`YulSemantics.EVM.EvmState`, with builtins stepping by the same
`builtinWithExternal` relation `AsmSem` uses (so calls/creates stay
open-world, `keccak` stays an oracle, and no per-op agreement is owed
anywhere). Big-step closure `SsaRun` mirrors `Run`: final state + outcome
(`.normal` from falling out of `main`'s `ret`, `.halt` from a halting
builtin).

## Construction (`toSsa`)

Yul is structured, so we do **not** need Cytron dominance frontiers. We use
the structured variant of Braun et al. 2013 ("Simple and Efficient
Construction of Static Single Assignment Form"): a recursive walk with an
environment `Ident → ValId`,

* `let x := e` / `x := e` update the map (no memory, no versions);
* `if`: translate both arms from the same entry map; the join block takes
  one parameter per variable whose mapping *differs* between arms;
* `switch`: same, n-way;
* `for`: the loop header takes one parameter per variable assigned anywhere
  in the loop (cond/post/body) — a safe overapproximation of the loop-variant
  set, cleaned up by the copy-propagation/DCE passes afterwards (Braun's
  redundant-φ elimination, done as a pass instead of during construction);
* `break`/`continue`/`leave` become edges to exit/post/return blocks
  carrying the current map;
* functions are separate `Func`s (Yul functions can't see caller locals, so
  each function is its own SSA problem);
* nested expressions flatten into instruction chains (right-to-left argument
  order preserved — it is observable and solc has shipped miscompilations
  breaking it).

`toSsa` is Option-valued like everything else in this repo: anything not yet
supported rejects, never miscompiles.

## SSA optimization passes (the payoff, phase 1 set)

All of these are why the dialect exists — each is a short fixpoint-free walk
on SSA and either impossible or painfully scoped on Yul:

1. **Copy propagation + φ/param simplification** — replaces
   trivially-forwarded block params (all predecessors pass the same value)
   with the value itself. Also the cleanup pass for construction.
2. **Dominance-scoped GVN/CSE** — pure ops keyed by (op, args); Yul-level
   CSE is blocked by scoping/shadowing, on SSA it is a hash lookup walked in
   dominator-tree order. (The dominator tree of our reducible, structured
   CFG is cheap: it falls out of construction order.)
3. **SCCP (sparse conditional constant propagation)** — constant folding
   *through* control flow, including killing never-taken branches; strictly
   stronger than the Yul-level `Simplify` fold because information flows
   through block params.
4. **Dead value elimination** — mark-and-sweep from effectful instructions
   and terminators; subsumes the source-level `DeadPure`/`DeadResults`
   special cases.
5. **Stack scheduling in `fromSsa`** (not a pass, but *the* gas lever):
   per-block-entry stack layouts chosen by liveness + next-use distance,
   operands DUPed only when still live, edge shuffles computed as
   parallel-copy sequencing (SWAP/DUP/POP), dead values dropped eagerly.
   This is what removes the POP/DUP/SWAP traffic and the dead stores that
   dominate the aave/uniswap gap.

Later candidates once the frame exists: load/store forwarding on
memory/storage with an SSA effect chain, LICM, value-range-based bounds-check
removal, better-than-greedy scheduling (Koopman/treegraph).

## Codegen (`fromSsa`)

`SsaCfg/ToAsm.lean`. Blocks are laid out in construction order (reducible ⇒
forward branches except loop back-edges). Each block gets a `Label`; block
entry has a declared stack layout (a `List ValId`, top first); instructions
emit `dup`/`swap`/`push`/`op` against a symbolic stack the generator tracks;
terminators emit the parallel-copy shuffle to the target's layout then
`jump`/`jumpi`. Function calls keep the existing convention (return label
push, args, `jump` to entry, `dynJump` back) so `AsmSem`'s `AVal.code`
discipline is unchanged. DUP/SWAP depth >16 rejects (`none`), as today; the
scheduler makes that rare rather than the layout making it common.

## The spec extension

Currently the only backend contract is the concrete theorem
`compile_correct`, and the only pass contract is Yul→Yul (`LocalPass` /
`ObsPass`). The generalization (`Optimizer/Spec/EvmBackend.lean`):

```
structure EvmBackend where
  compile  : Block Op → Option (List Instr)
  correct  : (same statement shape as compile_correct)
```

* The existing pipeline is the first instance (`EvmBackend.classic`, its
  `correct` field *is* `compile_correct`).
* The SSA path is the second (`EvmBackend.ssa`, `compileViaSsa_correct`).
* `LocalPass.optimize_then_backend_correct` generalizes
  `optimize_then_compile_correct` to any `EvmBackend`, so the whole verified
  Yul→Yul pipeline composes in front of either backend unchanged.

Note what is *not* in the audited surface: the SSA IR, its semantics, and its
passes are implementation vocabulary. The audited statement of
`compileViaSsa_correct` is phrased in exactly the vocabulary of
`compile_correct` (`Run`, `StateMatch`, `FrameOK`, `Steps`, `HaltedMatch`).
The spec closure grows by the `EvmBackend` structure and one theorem
statement, nothing else. SSA-internal pass soundness (`SsaCfg/Spec.lean`, an
`SsaPass` structure mirroring `LocalPass` over `SsaRun` equivalence) is the
internal analogue that keeps individual SSA passes auditable, but it sits
below the boundary the same way `EquivBlock` machinery does.

## Integration

`compileSource` gains the SSA backend as a **candidate** in the existing
`<|>` chain: after the Yul→Yul pipeline, try
`compileViaSsa optimized <|> (existing classic candidates)`. Option-valued
rejection means behavior can only change where the SSA path succeeds; every
fixture that regresses in gas is a scheduler bug to fix, not a correctness
event. Object path: same per-code-block treatment, after layout resolution
(the SSA backend sees resolved literals, so `dataoffset`/`datasize`
congruence never interacts with it).

## Proof plan (last phase, sorry-tracked until then)

1. `toSsa_sound` : `Run yulD prog yst0 V' yst' o → toSsa prog = some P →
   SsaRun P yst0 yst' o` — induction over the `Step` derivation with an
   environment-correspondence invariant (`VEnv` vs `Ident → ValId` vs
   `Regs`). The SSA equational property (each `ValId` defined once,
   definition dominates uses) is what makes the invariant stable.
2. `ssaPass_sound` per pass: `SsaRun`-equivalence (same final state/outcome).
   SCCP/GVN/DCE proofs on SSA are dramatically simpler than their Yul
   counterparts — no scoping, no shadowing, no `restore`.
3. `fromSsa_sound` : `SsaRun P yst0 yst' o → fromSsa P = some asm →
   ASteps asm ⟨asm, [], yst0⟩ ⟨[], σfin, yst'⟩ (+ halt analogue)` — the
   symbolic-stack tracking in the generator is the simulation invariant.
4. Compose with the existing gates exactly as `Correctness.lean` does:
   `compileViaSsa_correct` = (1) ∘ (2) ∘ (3) ∘ `asteps_sim`/`arun_halt_sim`.

Verification strategy is **direct proof of the construction** (CompCertSSA
proved translation *validation* is also viable; we prefer direct proofs here
because the IR is small and the repo's house style is
constructions-with-simulations, with checked-not-proved escape hatches like
`wfCheck` where a decidable check is cheaper than a freshness proof — we use
the same trick for SSA well-formedness: a decidable `ssaWfCheck` run at
`toSsa` exit, so single-assignment/dominance facts are read off the check).

## What "working" means for this PR

* `lake build` green; existing headline theorems untouched and sorry-free.
* New sorrys confined to `YulEvmCompiler/SsaCfg/` + listed in the PR body.
* Differential `#guard` examples: SSA path vs interpreter on the
  `Examples.lean` suite programs.
* Corpus: interpreter fixtures pass with the SSA candidate enabled;
  measurable gas reduction on stack-traffic-bound fixtures (aave/uniswap
  suites are the benchmark; PR body carries numbers).
