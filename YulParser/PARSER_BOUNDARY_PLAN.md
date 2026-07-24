# Stream 2 — parser boundary `⟹ SourceValid`: analysis & plan

Goal: discharge the normalization pass's `SourceValid` precondition at the
front-end, so `compileSource` is unconditionally correct *and* the disambiguation
guard provably fires on every accepted program (not a silent identity).

`SourceValid b := SVStmts b ∧ WellFormed b ∧ NormalForm.WellScoped b ∧
WScopedStmts [] b ∧ FScopedStmts (funNames b) b`
(`YulEvmCompiler/Optimizer/Implementation/Normalization/Disambiguate/Pass.lean`).

## Key finding: the lemma cannot be `validateBlockSource src b = true → SourceValid b`

`validateBlockSource src b := sourceLexWF src && (validateBlock ctx0 b).isSome`.
Four of the five conjuncts of `SourceValid` are enforced by `validateBlock`, but
**`SVStmts` is not**:

`SVStmts` requires `NotFresh x` for every identifier `x` in the AST, where
`NotFresh x := ∀ k, x ≠ dsName k` and `dsName k = "\0v…v"` (leading `NUL`).
`validateBlock`/`validateStmt`/`exprOutputs` **never inspect for a leading
`NUL`** — `validIdentifier` only rejects a trailing `.`/`..`. NUL-freeness is a
guarantee of the **lexer**, not the validator:

```
YulParser/Lexer.lean:17   isIdStart c := c.isAlpha || c == '_' || c == '$'
```

`NUL = Char.ofNat 0` is not alpha/`_`/`$`, so `pIdentChars` (`token (pWhile1
isIdStart isIdCont)`) never produces an identifier that starts with `NUL`; hence
a *parsed* identifier is never any `dsName`, i.e. is `NotFresh`. But an arbitrary
`b : Block Op` handed to `validateBlockSource` together with a matching `src`
could contain a `NUL` identifier and still be accepted (validate ignores it,
`sourceLexWF` only reads `src`). **So `validateBlockSource src b = true` does NOT
imply `SVStmts b`.**

### Consequence
The honest statement is about the **parse relation**, not validation of an
arbitrary AST:

```
parseSource src = some (.block b) → SourceValid b        -- and the .object analogue
```

`parseSource` is `parseBlock`/`parseBlockCompat` **followed by**
`validateBlockSource`. NUL-freeness (the `NotFresh` half of `SVStmts`) must come
from `parseBlock`; the `Nodup`-binder half of `SVStmts` and all of
`WellFormed`/`WellScoped`/`WScoped`/`FScoped` come from `validateBlock`.

## Decomposition (recommended landing order)

Two independent halves, then a join:

1. **From `validateBlock` (no parser needed).** A generalized induction over the
   mutual `validateStmt`/`validateStmts`/`validateBlock`/`validateCases` (and
   `exprOutputs`/`validArgs`) with a **`ValidateCtx` invariant** tying the
   threaded context to the predicates' scope lists:
   - `ctx.vars`  ↔  the `vs` / `dom` of `WellScoped` / `WScoped`,
   - `ctx.funcs` (names) ↔ the `fs` / `fdom` of `WellScoped` / `FScoped`,
   - `prepareFunctions` + the per-statement `unique`/`!contains` checks ↔
     `WellFormed = (funNames b).Nodup ∧ WFInner b`.

   Target (generalized, then specialized at `ctx0`):
   ```
   validateStmts ctx ss = some ctx' →
       WScopedStmts ctx.vars ss ∧ FScopedStmts (funcNames ctx) ss ∧
       ScopedStmts ctx.vars (funcNames ctx) ss ∧ WFInner ss ∧
       (Nodup-of-declared parts of SVStmts)
   ```
   Each of the four predicates is its own generalized statement sharing the same
   `ValidateCtx` invariant; prove them as four inductions (parallelizable) over
   the same case structure. This is delicate but parser-free.

   Caveat surfaced during scoping: `validate` also tracks `funcs` with arities,
   `forbidFunctions`, `loopControl`, `objectNames`, `inactiveBuiltins`; the
   invariant must carry enough of these (or explicitly discard the ones the
   predicates don't constrain) for the induction to go through.

2. **From `parseBlock` (parser soundness).** The missing `NotFresh`/NUL-freeness
   invariant: prove that every identifier in `parseBlock src`'s output starts
   with an `isIdStart` character (hence `≠ dsName k` for all `k`). This threads
   an "all identifiers `NotFresh`" invariant through the parser combinators —
   new parser-soundness machinery in the spirit of `SoundC.lean`/`Canon.lean`.
   `pIdentChars = token (pWhile1 isIdStart isIdCont)` is the leaf fact
   (`isIdStart c → c ≠ NUL → identifier ≠ dsName k`).

3. **Join.** `parseSource = some (.block b)` unfolds to `parseBlock … = some b`
   (or the compat parser) `∧ validateBlockSource src b = true`; combine (1)+(2)
   into `SourceValid b`. Then the object version via `validateObjectTree` +
   `parseObject`, reusing (1)/(2) per code block plus the object/data-name
   conditions.

## Payoff once landed
- `compileSource`-level correctness with **no** `SourceValid` hypothesis (the
  block/object correctness theorems in `Pipeline.lean` are already unconditional
  in the pass; this removes the last floating assumption at the entry point).
- With `sourceValidB_complete` (already landed on
  `normalization-unconditional-guard`), the disambiguation guard is proved to
  fire on every parser-accepted program, so `normalize` is provably active, and
  `normalize_uniqueNames_of_sourceValid` applies to real compiled input.

## Status
Analysis + decomposition only (this file). No `sorry` is committed (the build
treats `sorry`/warnings as errors). Part (1) is a large but parser-free proof;
part (2) needs new parser-soundness lemmas. Both are self-contained follow-ups.
