# Working in `YulParser/`

Standalone Lean parser library: text → the pinned upstream Yul AST
(`Block YulSemantics.EVM.Op`). It is independent of the backend proofs; read the
root `AGENTS.md` "Parser changes" section for the rules that govern edits here.

## Two grammars, one validator

- **Canonical** — `parseBlock` / `parseObject`. Have canonical round-trip
  theorems (`Canon.lean`, `SoundC.lean`): parse-then-render is identity on
  canonical tokens. Preserve escape spelling and canonical-token behavior when
  changing the accepted grammar, and update the proof + `Checks.lean` *only* if
  the genuine axiom footprint changes (a new axiom is never an acceptable update).
- **Compat** — `parseBlockCompat` / `parseObjectCompat` (`Compat.lean`).
  Intentionally lossy Solidity compatibility (hex literals, interleaved
  object/data items). Keep lossy normalization isolated and documented; it is
  outside the canonical theorem unless a new proof is added.
- **Validate** — `Validate.lean`. `parseSource` runs either grammar through the
  strict-assembly checks: lexical/identifier validity, scopes and function
  signatures, control placement, built-in arities and direct-literal args, switch
  cases, object references, immutables, version-gated built-in names. Keep it
  independent of the round-trip theorems.

## File map

`Core.lean` (parser monad) · `Combinators.lean` · `Tokens.lean`/`Lexer.lean`
(lexing) · `Atoms.lean` · `Expr.lean`/`Stmt.lean`/`Obj.lean` (grammar) ·
`Canon.lean`/`SoundC.lean` (round-trip proofs) · `Compat.lean` (lossy fallback) ·
`Validate.lean` (strict checks) · `Compile.lean` (`compileSource` glue into the
backend, incl. the front-end dialect accommodations documented in the root
`AGENTS.md`) · `Examples.lean` (`#guard`s).

## Invariants

- Public recursive grammar entry points have a **fuel cap of 256**.
- The moving Solidity syntax corpus currently has **no known mismatches**
  (`test/solidity-yul-syntax-known-mismatches.txt` is an empty, exact baseline —
  not a skip list). Add an entry only for an understood, intentionally deferred
  difference; remove it the moment the parser agrees.

CLI: `YulParserMain.lean` builds the `yulc` executable (`--parse-only` or full
compile to hex bytecode).
