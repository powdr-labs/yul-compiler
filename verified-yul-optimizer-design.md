# A Verified Yul Optimizer in Lean — Design Document

## 1. Motivation and Guiding Principle

The Solidity compiler's Yul optimizer was designed under the assumption that any pass can be buggy. This led to a defensive architecture: roughly sixty small, individually reviewable passes, no state shared between them, invariants re-established and re-checked constantly, and a long iterated pipeline to reach a fixpoint. Every design decision trades performance and power for auditability.

Machine-checked correctness proofs dissolve that constraint. Once each transformation carries a proof of semantics preservation, there is no reason to keep passes small, stateless, or mutually distrustful. This document describes an optimizer designed around that freedom, targeting the unoptimized Yul IR emitted by `solc --ir` (which is dominated by tiny helper functions, constant offset arithmetic, and redundant temporaries — precisely the patterns cheap optimizations remove).

The guiding principle throughout:

> **Bake in what every pass needs and no pass changes; carry as proof-annotated data what passes compute and update; hold as transient environment what a traversal can reconstruct.**

Concretely: scoping, arity, flatness, and function hoisting become *structural* properties of the IR type, enforced by Lean's type checker. Analysis results (constants, purity, use counts) become *annotations paired with soundness proofs*. Dataflow facts (current value of a variable, available expressions) live only in the *recursion environment* of a single fused pass, kept true by the induction hypothesis rather than by a program invariant.

The end state is a single trusted entry theorem, `interpret (optimize p) ≈ interpret p`, with everything else — scoping, analysis soundness, rule soundness — internal lemmas.

---

## 2. Architecture Overview

```
 raw Yul (from solc --ir)
      │
      ▼
 ┌──────────────────────────────┐
 │ ingest: split + hoist +      │   verified translation
 │ scope-check into Core IR     │   (adequacy theorem, once)
 └──────────────────────────────┘
      │  Core IR (intrinsically scoped, ANF, hoisted)
      ▼
 ┌──────────────────────────────┐
 │ fused optimize pass          │   one mutual induction proof
 │  env ↓ : constants, copies,  │
 │          available exprs,    │
 │          optimized functions │
 │  summary ↑ : use counts,     │
 │          effect facts        │
 │  includes: constant folding, │
 │  copy prop, rule-based       │
 │  simplification, CSE,        │
 │  inlining, pruning,          │
 │  literal-switch collapse     │
 └──────────────────────────────┘
      │  optimized Core IR + final Summary
      ▼
 ┌──────────────────────────────┐
 │ emit: count-driven expression│   verified translation
 │ joining + nested Yul output  │   (two join lemmas + emitter theorem)
 └──────────────────────────────┘
      │
      ▼
 optimized Yul → stack layout / codegen
```

Only the middle box is where ongoing optimizer development happens; the two boundary boxes are proved once and rarely touched.

---

## 3. The Core IR

### 3.1 Why a new datatype rather than the Yul AST

Optimizing on a general Yul AST forces every invariant — well-scopedness, split expressions, hoisted functions, correct arities — into side conditions (`isSplit p`, `wellScoped p`, …) that every lemma must hypothesize and every transformation must re-establish. That is solc's architecture wearing Lean clothes: proofs dominated by invariant plumbing rather than semantics. Instead, the invariants are made unrepresentable to violate:

```lean
inductive Val (Γ : Ctx)                 -- what may appear as an argument
  | var  : Var Γ → Val Γ               -- a Var Γ *is* its scope proof
  | lit  : Word → Val Γ

inductive Expr (Γ : Ctx)
  | builtin : Builtin n → Vec (Val Γ) n → Expr Γ    -- arity-correct by type
  | call    : FunId sig → Vec (Val Γ) sig.args → Expr Γ

inductive Stmt (Γ : Ctx)                -- let extends Γ; assign requires Var Γ
  ...

structure Program where
  funs : ...                            -- topologically ordered by call graph,
                                        -- bodies closed over params only
  main : Stmt ∅
```

What each structural choice buys, per invariant:

- **Split form (ANF):** `Expr` takes `Val`s, not `Expr`s, so nested expressions are unrepresentable. No pass can un-split the program; nothing ever re-splits or re-proves flatness.
- **Scoping:** intrinsically well-scoped syntax (de Bruijn indices / membership proofs into a typed context). Substitution and inlining cannot capture or dangle by construction.
- **Arity:** the `Vec` index eliminates the malformed-arity case from every induction.
- **Hoisting:** `Program` has no nested function-definition constructor; the case simply does not exist in any proof.

Each of these replaces an entire solc pass *plus* a preservation proof per downstream transformation with zero lines.

One deliberate softness: statements are **not** indexed by effect facts or use counts. Dependent-type-driven analysis information forces every rewrite to recompute type indices; it is where intrinsically-typed developments go to die. Analysis results live in annotations and summaries with separate soundness proofs (§5, §6).

Yul's own scoping rules help enormously here: function bodies are closed over their parameters (no free variables from enclosing scopes), so function inlining is *closed-term instantiation* rather than general capture-avoiding substitution. Write the `Subst`/`Rename` infrastructure once, early, as a small library; everything else consumes it.

### 3.2 Why not SSA

SSA exists to make def-use facts trivial: one definition per variable turns "what value does `x` hold here" into a lookup. The fused pass (§6) already has this — its environment *is* SSA-on-the-fly, extended at definitions, weakened at reassignments, met at joins. The information SSA materializes into program text is instead held transiently in the recursion.

SSA is also unusually awkward for this project, twice over. First, Yul has no phi nodes: solc's `SSATransform` fakes SSA with fresh `x_1, x_2, …` plus a residual real assignment at joins, so the invariant is soft and loops still carry a mutable variable — one would be proving correctness of a transform whose output does not deliver the clean property. A genuine phi-based SSA IR means a second IR, two more translation proofs, and phi semantics, for structured control flow where phis are pure bookkeeping. Second, SSA's value is a *global* invariant ("one def per variable"), which every transformation would owe a preservation proof on top of its semantic proof. The env-based approach has a *local* invariant (`EnvSound`, §6.3) that lives only inside the induction and never constrains the output program.

Even global value numbering does not need SSA here: an available-expressions map in the env (§6.2) provides CSE with one extra soundness clause, not a new IR. The core IR therefore permits plain reassignment — `x := add(x, y)` in a loop body is legal — and the env handles it by weakening.

The one scenario that would revisit this decision: a future verified stack-layout/codegen phase wanting explicit liveness and single definitions. That property belongs on a *different, lower-level* IR at the end of the pipeline, not on the optimizer's IR.

### 3.3 Splitting and joining happen only at the boundaries

**Splitting — once, at ingestion.** Converting solc's Yul into the core IR names every intermediate result in evaluation order. Critical subtlety: Yul evaluates call arguments **right-to-left**, so `f(g(), h())` splits to

```
let t1 := h()
let t2 := g()
f(t2, t1)
```

Getting this wrong makes the ingestion proof wrong before the optimizer even runs. After ingestion, split form is a property of the type; it is never re-established.

**Joining — once, at emission, driven by final use counts.** Rebuilding nested expressions is not an optimization; it is the first step of codegen, done purely for the EVM stack (nested expressions map to stack pushes with no named slots; split form forces temporaries into stack slots, causing `DUP`/`SWAP` traffic and stack-too-deep risk). After the fused pass, the final `Summary` supplies exact reference counts. A `let x := e` with exactly one use of `x` may be substituted into its use site in exactly two cases, which together cover everything worthwhile:

1. **Movable `e`** (pure, non-reverting): may travel anywhere in scope. Requires one commutation lemma — "movable expressions commute with any statement" — proved once, cited per join.
2. **Effectful `e`** whose single use is in the *next* statement, in the position evaluated *first* under right-to-left order: deleting the `let` changes nothing about execution order. This is solc's `ExpressionJoiner` discipline; its lemma is pure let-inlining/β, no effect commutation needed.

Since joining is semantics-preserving in both directions under these two lemmas, the join *heuristic* is unverified by design: it should be stack-aware ("join when it shortens live ranges; don't drag expensive computations into deep nesting") and freely tunable against gas benchmarks without touching a proof. There is no "joined IR" datatype: the join decisions feed the emitter directly, and nested Yul is merely output syntax covered by the emitter's single correctness theorem.

**Ordering constraint worth noting:** CSE turns single-use temporaries into multi-use ones, so join decisions made before CSE would be invalidated — another reason joining must come last.

Slogan: **split form is where you think; joined form is merely how you speak EVM.**

---

## 4. Semantics and the Correctness Statement

Four new semantic artifacts are needed; everything else reuses the existing Yul semantics in the framework as the trusted reference.

### 4.1 A big-step core interpreter

Semantics-by-embedding (`⟦c⟧ := interpretYul (emit c)`) would avoid a new interpreter but make every optimizer proof reason about the Yul interpreter *through the emitter* — inductions fighting the translation instead of following the core IR. Instead: a direct fuel-based big-step interpreter over the core IR. It is *smaller* than the Yul one because the type has already discharged scoping, arity, and nesting: `Val` evaluation is total lookup, expression evaluation has no recursive expression case, and the function-call rule instantiates a closed body.

### 4.2 Observational equivalence `≈`

This is what "correctness" *means*, so it is the real design decision:

- **Observables are events, not machine states:** external calls, logs, and the halt (returned/reverted) with returndata and final storage. Memory is **not** observable per se — optimizations legitimately change scratch memory — except insofar as it flows into observables via `return`, `log`, `sha3`, or calls.
- **Equivalence modulo gas:** ∀ fuel, if the source terminates within that fuel, the target terminates in *some* fuel with the same observables. The optimizer changes gas by design. Consequence: `gas()` must be given an arbitrary-value (nondeterministic-ish) semantics, or rewrites become unsound for programs branching on it; equivalence quantifies over the value. `msize` gets the same treatment, or alternatively the solc convention: memory-touching code is immovable in the presence of `msize`.
- **Symmetric equivalence, not refinement:** for this pass set, plain equivalence with the fuel quantifier suffices, and symmetric relations are much easier to work with. Check early — against the pruning lemma specifically — whether removing potential out-of-fuel behavior forces a directed refinement; the fuel quantifier above is designed so it does not.
- **Dialect scope:** define semantics only for the Yul dialect actually needed — EVM dialect, objects, the builtins solc emits. Full Yul generality buys nothing.

### 4.3 One adequacy theorem

`interpretYul p ≈ interpretCore (ingest p)`, and its emission counterpart. This is the only place the two semantics meet, and where the right-to-left argument-order subtlety is nailed down permanently. Keep the Yul side minimal: verify the AST↔AST conversion; treat solc's textual output → Yul AST as trusted input handling, not a verified parser.

### 4.4 The builtin fact layer

The interpreter delegates builtins to a dialect table. The optimizer needs a *facts* layer over it: one classification function (reads/writes/reverts/movable per builtin), one soundness lemma per classification claim, and the algebraic lemmas rewrite rules cite (determinism, arithmetic semantics for folding, the movable-commutation lemma). Long but shallow, and the part extended forever — structure it as classification → per-claim soundness → rule lemmas on top.

### 4.5 The end-to-end theorem

```
interpretYul p
  ≈ interpretCore (ingest p)                       -- adequacy (once)
  ≈ interpretCore (optimize (ingest p))            -- the fused pass (§6)
  ≈ interpretYul (emit (optimize (ingest p)))      -- emission (once)
```

Only the middle link is touched by future optimizer work.

---

## 5. Proof-Carrying Analysis

Solc's stateless passes recompute reference counts, purity, movability, and escape information constantly. Here, analysis results are **annotations paired with soundness proofs**: an analysis record at each node together with a proof that the record is sound with respect to the semantics (e.g. "annotated pure, and here is the proof it does not touch state"). Transformations consume certified facts directly, and their correctness proofs cite the annotation's soundness proof instead of reproving side-effect-freedom locally. Each rewrite carries a lemma that it preserves annotation soundness, so annotations update incrementally during rewriting.

In the fused pass, this materializes as the upward `Summary` (use counts + effect facts, with a soundness clause in the main theorem) and the `OptimizedFn` records for already-processed functions (final body + facts like size, purity, single-use).

---

## 6. The Fused Optimization Pass

### 6.1 Why fusion

Inlining, constant folding, identity rewrites, copy propagation, CSE, and dead-code pruning are mutually enabling; solc iterates ~20 tiny passes to reach the fixpoint they jointly define. The reason solc could not fuse them is exactly that fused passes are hard to *trust* — which proofs solve. One recursive traversal doing all of them simultaneously achieves the fixpoint behavior in one or two passes and, crucially, costs **one mutual induction** instead of N pass-level proofs plus N well-formedness re-establishment lemmas. This is where the verified design most decisively beats solc's.

### 6.2 Shape of the pass

An environment flows **down**, a summary flows **up**:

```lean
structure Env where
  vals  : Var → Lattice            -- ⊤ | Const c | CopyOf v
  avail : ExprKey → Option Var     -- available expressions (CSE),
                                   --   keys canonicalized through copies
  funs  : FunId → OptimizedFn      -- already-optimized body + facts

structure Summary where
  uses    : Multiset Var           -- reference counts
  effects : EffectFacts            -- pure? movable? can-revert?

optimize : Env → Stmt Γ → (Stmt Γ × Summary)
```

**Downward, statement by statement:** each expression is rewritten under the current env — substitute constants and copies, then run the rule engine (§7), then consult `avail` for CSE. A `let x := 3` extends `vals` with `x ↦ Const 3`; a `let y := add(a,b)` whose key is already in `avail` becomes `let y := t` (recording `y ↦ CopyOf t`), otherwise `avail` gains the key. Reassignments weaken the assigned variable's entry toward ⊤ and invalidate `avail` entries mentioning it (or whose effects conflict). At `if`/`switch`/`for` joins, the env is the meet of the branch envs; a `switch` on a value the env knows to be a literal collapses to the matching case (one of a handful of bespoke statement-rewrite cases, §7's last paragraph).

**Upward:** `Summary` counts drive pruning — declarations nobody referenced are deleted, movable statements with dead results are dropped. Pruning is simply "the up-pass discards what the counts prove unused"; its lemma cites the effect facts.

**Function ordering:** function bodies are optimized bottom-up over the call graph (leaves first), so every call site sees the callee's *final* body and facts in `env.funs`.

### 6.3 Inlining, integrated

Inlining slots in at exactly one point, the call-expression case:

```lean
| .call f args =>
    let args' := args.map (rewrite env)
    let fn := env.funs f
    if worthInlining fn args' then
      let body := subst fn.body args'   -- closed-term instantiation
      optimize env body                 -- re-run on the specialized body
    else (.call f args', summaryOf fn args')
```

The recursive `optimize` on the substituted body is where mutual enablement lives: constant arguments fold the callee's guards, dead branches disappear, now-unused temporaries are pruned — in the same traversal, with no second pipeline iteration. `worthInlining` sees the *specialized* arguments, so "inline if single-use, or if body-size-after-obvious-folding is small" is an accurate estimate — smarter than solc's heuristic can afford to be. Combined with pruning of zero-reference function definitions, this directly attacks the dominant cost in solc's unoptimized IR: swarms of tiny single-use helpers (`cleanup_*`, `shift_*`, `abi_decode_*`, `checked_add_*`, …).

**Termination.** Bottom-up call-graph ordering means an inlined body contains no further inline-worthy calls (each call inside it was already inlined or rejected when that body was optimized), so the recursion on the substituted body only folds and prunes — strictly reducing AST size. In Lean: recursion on `(callGraphHeight f, sizeOf stmt)` lexicographically via `termination_by`, with recursive functions excluded from inlining (or given explicit fuel). No well-founded-recursion pain.

### 6.4 The single correctness proof

One mutual induction with a soundness invariant on the environment:

```lean
def EnvSound (env : Env) (σ : State) : Prop :=
  (∀ x c, env.vals x = Const c → σ x = c) ∧
  (∀ x v, env.vals x = CopyOf v → σ x = σ v) ∧
  (∀ e v, env.avail e = some v → evalE σ e = σ v) ∧
  (∀ f,   env.funs f ≈ original f)

theorem optimize_sound :
    EnvSound env σ →
    interpret σ stmt ≈ interpret σ (optimize env stmt).1
  -- plus: the returned Summary is sound
```

Each case cites one local lemma: constant folding cites builtin determinism; propagation and CSE cite their `EnvSound` clauses; pruning cites the effect facts; inlining cites a single β-like lemma — `interpret σ (call f args) ≈ interpret σ (subst f.body args)` — which falls directly out of the big-step function-call rule, after which the induction hypothesis covers re-optimization of the substituted body. One invariant, one induction, and every optimization solc needed a dozen passes for.

---

## 7. Modular Simplification Rules

Algebraic rewrites are the part of the optimizer extended forever, so they get an open architecture with a closed trust story: **each rule is a first-class value bundling pattern, result, side condition, and proof**, and the engine is one function with one theorem quantified over any rule list.

```lean
structure Rule where
  lhs   : Pat n                    -- pattern over n metavariables
  rhs   : Pat n                    -- may reuse the metavars
  cond  : Subst n Γ → Bool         -- decidable side condition
  sound : ∀ Γ (σ : Subst n Γ) (s : State),
      cond σ → evalE s (instP lhs σ) = evalE s (instP rhs σ)
```

**Patterns are a datatype, and shallow by construction.** `Pat n` is expressions over `Fin n` metavariables plus literal-metavars (matching only literals). Because the IR is split, patterns are one builtin over metavars/literals — matching is a trivial total function `match? : Pat n → Expr Γ → Option (Subst n Γ)` with a one-time lemma `match? p e = some σ → e = instP p σ`. That lemma plus each rule's own `sound` field is everything the engine needs: no rule reasons about the engine, the engine reasons about no rule.

**ANF eliminates an entire class of side conditions.** Metavariables only ever bind `Val`s (variables/literals), which are trivially pure — so dropping or duplicating a metavariable on the rhs is *always* sound. In solc's rule list every rule must fret about discarding subtrees with side effects; here that concern vanishes structurally. The only side conditions left are arithmetic ones on literals (e.g. "power of two" for `div(x, 2^k) → shr(k, x)`).

**Constant folding is a rule schema, not enumerated rules:** for each pure total builtin `b`, "all args literal → literal `⟦b⟧ args`", with one soundness lemma parametric in `b` citing determinism from the fact layer. Group the remaining rule families by shared lemma: unit laws (`add(x,0)→x`), absorption (`mul(x,0)→0`), involution (`not(not x)→x`), comparison-with-self (`sub(x,x)→0`, `eq(x,x)→1`), masking with `2^k−1` literals, strength reductions. Solc's `simplificationRules` list is the harvest source — port one lemma at a time, noting which preconditions simply disappear under ANF.

**One engine, one theorem:**

```lean
def simplify (rules : List Rule) : Expr Γ → Expr Γ    -- first match wins

theorem simplify_sound :
    ∀ rules e s, evalE s (simplify rules e) = evalE s e
```

Since `Rule` carries its proof intrinsically, the theorem has no per-rule hypotheses. Adding a rule = pattern + condition + one equation about two shallow expressions + append to the list. No engine change, no re-proof, no rule interaction.

**Integration with the fused pass, two details.** First, `simplify` runs *after* env-substitution, so rules see the literals the env exposed — that is how `add(x, 0)` actually fires on codegen output where the `0` arrived by propagation. Second, cascades ("`not(not x) → x` enables a rule one level up") cross statement boundaries in ANF, and the traversal handles them: the result lands in the env as a constant or copy, and the enclosing expression is simplified when *its* statement is visited. The engine therefore never iterates to fixpoint — one top-level match attempt per expression, trivial termination, induction-free soundness proof.

**Statement-level rewrites stay out of the engine.** Collapsing `switch` on a literal, turning `if 1 {…}` into its body, etc. are three or four fixed cases in the fused pass with bespoke lemmas. Generalizing the pattern language to statements buys little and costs a much hairier matching proof.

---

## 8. What Is Trusted, What Is Proved, What Is Heuristic

| Layer | Status |
|---|---|
| Yul semantics (existing framework) | Trusted reference |
| Textual Yul → Yul AST parsing | Trusted input handling |
| Builtin dialect table + fact layer | Proved (per-claim lemmas) |
| Ingestion (split, hoist, scope) | Proved once (adequacy) |
| Fused pass incl. inlining, CSE, pruning | Proved (one mutual induction) |
| Rule engine | Proved once; rules proved individually |
| Join decisions + `worthInlining` | **Heuristics, unverified by design** — any choice is covered by the same lemmas, so they are freely tunable against gas benchmarks |
| Emission (joining + nested Yul) | Proved once (two join lemmas + emitter theorem) |

The separation of *policy* (heuristics) from *mechanism* (proved transformations) is deliberate: performance tuning never touches a proof.

---

## 9. Known Sharp Edges

1. **Right-to-left argument evaluation** in Yul. Encode it correctly in the ingestion split and in join case 2, and pin it down in the adequacy theorem.
2. **`gas()` and `msize`.** Arbitrary-value semantics for `gas()` (equivalence quantifies over it); for `msize`, either the same treatment or the solc convention that its presence makes memory-touching code immovable.
3. **Equivalence modulo gas** must be stated with the fuel quantifier of §4.2, or pruning/inlining lemmas break on out-of-fuel behavior.
4. **Recursive functions** are excluded from inlining (or fueled) to keep the lexicographic termination measure.
5. **De Bruijn boilerplate.** Front-load the `Subst`/`Rename` library; exploit that Yul functions are closed to keep inlining a closed-term instantiation.
6. **Do not index types by analysis results** (effects, counts). Annotations + soundness proofs, always.

---

## 10. Suggested Build Order

1. Core IR datatypes + `Subst`/`Rename` library.
2. Core interpreter, `≈`, builtin table + fact layer (classification and its soundness lemmas).
3. Ingestion and emission with the adequacy theorems (emission initially *without* joining: emit split Yul verbatim — correct, just not stack-optimal).
4. Fused pass skeleton with env/summary, proving `optimize_sound` first for the constant/copy/prune fragment only.
5. Rule engine + an initial harvest of solc's simplification rules (unit laws and constant-folding schema first — they fire constantly on codegen output).
6. Inlining case + termination measure + β lemma. At this point the optimizer already beats solc's early pipeline on its own output, since single-use helper inlining plus pruning plus folding is where the bulk of the win is.
7. CSE clause in the env and its `EnvSound` clause.
8. Count-driven joining in the emitter (two lemmas), then heuristic tuning against gas benchmarks.
