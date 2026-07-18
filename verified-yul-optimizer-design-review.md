# Verified Yul Optimizer Design Review

## Recommendation

Implement a revised version of the design **on top of the existing optimizer infrastructure**, not instead of it.

Keep the current audited `Optimizer.Pass` contract, backend composition theorem, object compiler, and working production pipeline. Introduce the proposed Core IR as the internal implementation of a new verified pass. It may eventually supersede the current concrete passes if measurements justify that, but it should not replace the optimizer specification or introduce a second, weaker notion of correctness.

The design has excellent ideas for scaling to copy propagation, dead-code elimination, general inlining, and CSE. As written, however, it assumes a greenfield repository and misses several hard requirements already solved here.

## What already exists

The design document's premise is outdated. The repository now has:

- A stable, compositional pass contract: `Sound D run := ∀ b, EquivBlock D b (run b)`, bundled in `Pass`, with composition and pipelines in [`Pass.lean`](YulEvmCompiler/Optimizer/Spec/Pass.lean).
- End-to-end composition with the verified backend in [`Backend.lean`](YulEvmCompiler/Optimizer/Spec/Backend.lean).
- A real simplifier with constant folding, neutral identities, and constant control-flow selection in [`Simplify.lean`](YulEvmCompiler/Optimizer/Implementation/Simplify.lean).
- Scope-aware exact identity-function inlining, including forward/hoisted lookup, closure environments, shadowing, and loop scopes, in [`InlineIdentity.lean`](YulEvmCompiler/Optimizer/Implementation/InlineIdentity.lean).
- A verified `Simplify → InlineIdentity → Simplify` production pipeline in [`IdentityPipeline.lean`](YulEvmCompiler/Optimizer/Implementation/IdentityPipeline.lean).
- Resolver congruence and whole-object correctness, including deploy and runtime objects, in [`IdentityPipeline.lean`](YulEvmCompiler/Optimizer/Implementation/IdentityPipeline.lean).
- Production source compilation using that pipeline in [`YulParser/Compile.lean`](YulParser/Compile.lean).
- The optimizer contract and backend theorem in the audited specification boundary, visible in [`SPEC.md`](SPEC.md).

The current optimizer implementation is already about 4,300 lines, with exact identity inlining alone around 1,750 lines. That supports the design document's diagnosis: proving increasingly global transformations directly over the raw named Yul AST will become expensive.

The gas gap also remains large enough to justify stronger optimization. In the checked-in real Solidity semantic baseline, this compiler currently totals about 1.44× solc's optimized execution gas, with 647 of 648 rows more expensive. General inlining, propagation, pruning, and joining are therefore worthwhile targets.

## Comparison

| Area | Current infrastructure | Proposed design | Recommendation |
|---|---|---|---|
| Correctness | Exact `EquivBlock`: same environment, full state, halt payload, and outcome from every configuration | Event-based observational equivalence, omitting scratch memory and other state | Keep the existing stronger contract |
| Integration | Any `Pass` composes directly with `compile_correct` | New Core interpreter and adequacy chain | Package Core optimization as a `Pass` |
| Representation | Raw named Yul AST, invariants proved externally | Intrinsically scoped, arity-indexed ANF Core IR | Adopt for complex dataflow |
| Pass structure | Small independently composable passes | One fused optimizer and one mutual proof | Retain composition; allow fusion inside the Core pass |
| Rules | Ad hoc but proved simplifier cases | First-class rules carrying soundness proofs | Adopt |
| Analysis | Mostly recomputed locally | Certified effect, use-count, constant, copy, and availability information | Adopt incrementally |
| Functions | Lexically hoisted scopes, forward calls, recursion, mutual recursion | Globally topologically ordered functions | Redesign around lexical IDs and SCCs |
| Objects | Explicit layout resolution congruence | Largely absent from the architecture | Make resolver compatibility mandatory |
| Malformed ASTs | `Pass.run` is total on every block | Ingestion assumes well-scoped and arity-correct input | Use optional ingestion with identity fallback |
| Gas semantics | Source is gas-free; `gas()` is already an arbitrary oracle | Fuel-based equivalence modulo gas | Do not introduce fuel semantics |
| Production migration | Working pipeline with measured gains | Greenfield replacement | Add, compare, then promote |

## What is good in the design

The Core IR idea in [the design](verified-yul-optimizer-design.md#31-why-a-new-datatype-rather-than-the-yul-ast) is the most valuable part. Intrinsic scope and arity would:

- Eliminate repeated name-resolution and malformed-arity proof cases.
- Make bound-variable rewrites such as `mul(x, 0) → 0` sound inside validated code. That rewrite is deliberately unavailable under the current pointwise expression equivalence because an arbitrary raw environment may leave `x` unbound.
- Make use counts, copy propagation, dead-let elimination, substitution, and capture-free inlining substantially cleaner.
- Turn ANF expression metavariables into side-effect-free values, simplifying algebraic rewrite proofs.
- Provide a natural home for environment-based constants, copies, and available expressions.

The modular rule engine proposed in [section 7](verified-yul-optimizer-design.md#7-modular-simplification-rules) should also be adopted. The current `pureFn` and neutral-rewrite kernel are a good proof foundation, but a first-class `Rule` abstraction would make adding arithmetic identities much cheaper.

The separation between proof-covered mechanism and benchmark-tuned heuristics is also right. Inlining thresholds and join decisions should be freely adjustable once their possible actions are covered by generic soundness lemmas.

## What should not be adopted as written

### A new weaker semantics

The proposed observational equivalence in [section 4.2](verified-yul-optimizer-design.md#42-observational-equivalence-) is weaker than the audited contract. It omits at least exact memory state and potentially balances, account code/nonces, transient storage, returndata, refunds, logs in their full representation, and self-destruct scheduling.

Replacing `EquivBlock` with that relation would move the human-approved trust boundary and require a new backend theorem with a weaker conclusion. It is not necessary for constant propagation, DCE, CSE, or ordinary inlining.

The current source semantics is already gas-free, and `gas()` already returns an arbitrary word relationally. Consequently the proposed fuel quantification solves a problem the repository does not have.

### A separate fuel-based Core interpreter

A new interpreter would duplicate the pinned Yul semantics, including open-world calls and creates, halting behavior, multi-value expressions, loop outcomes, memory state, and function closures. An executable interpreter is also an awkward fit for the relational nondeterminism of external operations and `gas()`.

Prefer defining Core meaning through a verified erasure/emission into the existing Yul AST. If a direct Core relation later proves useful for induction, it should reuse the existing dialect state and builtin relation and be proved exactly equivalent to emitted Yul—not define a new event semantics.

### Globally topological functions

The sketch's `Program.funs` cannot represent the current language directly. This compiler supports recursion and mutual recursion, while Yul lookup depends on ordered lexical scopes and definition-site closures. The existing inliner's size is evidence that these details are semantically real, not merely raw-AST inconvenience.

A Core representation should instead resolve names to stable function IDs while preserving:

- Lexical scope ownership.
- Ordered first-definition lookup where applicable.
- Forward references.
- Recursive strongly connected components.
- Definition-site closure environments.
- Multi-parameter and multi-result signatures.

Inlining can process the SCC DAG bottom-up and decline to inline edges within a recursive SCC.

### A single fused pass as a universal solution

Proofs remove semantic mistrust, but they do not remove termination complexity, maintenance cost, performance regressions, or the difficulty of changing a giant mutual induction.

The claim that specialization reaches a fixpoint in one traversal is too strong. Specialized arguments can change inlining profitability, pruning can expose new opportunities, loop facts require conservative invariants or iteration, and copy invalidation must account for reassigned aliases.

Use fusion where a shared environment materially helps—propagation, DCE, and CSE—but keep the result packaged as one ordinary `Pass` alongside independently composable passes.

### Missing object-layout compatibility

This is the largest omission. Object compilation resolves `dataoffset` and `datasize` using code sizes that optimization itself changes. The existing pipeline therefore proves pass-specific resolution congruence.

A Core pass needs both:

1. Ordinary `EquivBlock` soundness.
2. A same-layout resolver theorem such as `EquivBlock (resolve L b) (resolve L (corePass b))`.

Without the second property, it cannot replace the production object pipeline regardless of how good its block theorem is.

## Proposed architecture

The revised architecture should look like:

```text
Yul AST
  → optional verified ingestion into scoped Core
      failure → original AST unchanged
      success → Core optimization → verified emission/joining
  → Yul AST
  → existing compile / compileObject
```

The whole transformation is then bundled as:

```lean
def corePass : Optimizer.Pass D
```

This preserves the current spec and all backend composition machinery. It also makes ingestion total at the pass level: malformed, open, unsupported, or unexpectedly complex input simply follows the identity path.

The Core types should additionally support:

- `Expr Γ k`, indexed by result arity, rather than assuming every expression returns one value.
- Single-valued `Val Γ` arguments in ANF.
- Mutable variables.
- Structured `break`, `continue`, `leave`, and halt propagation.
- Lexical function-scope IDs and recursive SCCs.
- Opaque object/layout-reference operations.
- Fresh temporary generation with a proof of non-capture.

## Recommended implementation order

1. Keep the current production pipeline unchanged.

2. Extract a reusable builtin fact layer from `pureFn`: arity, state independence, totality, possible halt/revert, reads, writes, and movability, each connected to the existing `Dialect.Builtin`.

3. Introduce the proved shallow rule engine and migrate the current arithmetic simplifier to it. Also finish the relatively small `for`-initializer congruence gap recorded in [`IDEAS.md`](YulEvmCompiler/Optimizer/IDEAS.md).

4. Build a Core boundary pilot only:

   - Optional scoped/arity-checked ingestion.
   - No-op Core transformation.
   - Emission back to Yul.
   - Exact `EquivBlock` theorem.
   - Resolver-compatibility theorem.
   - Recursion, multi-return, objects, and right-to-left argument tests.

   This is the critical go/no-go point. It tests the expensive assumptions before investing in the optimizer proper.

5. Add environment-based constant and copy propagation plus dead-let/dead-function pruning. These should be the first Core optimizations because they directly attack solc's unoptimized helper-heavy IR.

6. Add SCC-aware general inlining with explicit fuel or a well-founded budget. Do not rely on the document's informal "already optimized calls" termination argument.

7. Add pure-expression CSE and count-driven emission joining. Treat memory-dependent CSE separately, with explicit read/write conflict proofs.

8. Add `corePass` after the current pipeline initially. Compare gas, compilation acceptance, optimizer runtime, bytecode size, and proof/build time. Only remove redundant old stages once the Core pass demonstrably subsumes them without regressions.

## Final decision

The plan is directionally better for the next generation of optimizations, but it is not a better replacement for the infrastructure already present.

The right strategy is:

- **Keep** `Pass`, `EquivBlock`, `optimize_then_compile_correct`, resolver correctness, and the current pipeline.
- **Adopt** the intrinsic Core IR, certified fact layer, modular rules, environment-based dataflow, and heuristic/mechanism separation.
- **Reject or revise** the weaker observational semantics, separate fuel interpreter, globally topological function model, and single-fused-pass requirement.
- **Integrate incrementally** as a new `Pass`, promoting it only after semantic, object-layout, acceptance, and gas benchmarks pass.
