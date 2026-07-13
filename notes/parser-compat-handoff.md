# Parser compatibility handoff

Branch: `agent/yul-parser-false-rejects`

## Completed

- Made quoted-string scanning escape-aware without weakening the existing
  canonical round-trip proof. Escaped quotes no longer terminate a string;
  literal newlines and carriage returns remain rejected; escape spelling is
  retained in the current AST.
- Added a documented compatibility parser for Solidity forms that the current
  AST cannot round-trip faithfully:
  - `hex"..."` expression literals, lowered to Solidity's left-aligned 256-bit
    numeric value;
  - `hex"..."` object data, decoded to bytes; and
  - arbitrarily interleaved sub-objects and data, normalized into the AST's
    separate lists while preserving relative order within each list.
- Kept `parseBlock` and `parseObject` as the verified first-choice parsers.
  `parseSource` and `compileSource` use the compatibility path only as a
  fallback.
- Preserved the syntax corpus's previously correct rejections that became
  reachable through hex/object support: duplicate object item names,
  non-literal `dataoffset`/`datasize`, and malformed `verbatim_*` calls.
- Added build-time examples for compilation of `hex"2233"` and parsing an
  escaped, interleaved object containing hex data.
- Removed all eight old false-reject entries from the Solidity syntax baseline:
  `hex_expression.yul` plus the seven affected object fixtures.
- Updated `README.md`, `PLAN.md`, and parser module documentation to distinguish
  the verified canonical grammar from the lossy compatibility normalization.

## Validation at this checkpoint

- `lake build`: passes.
- Solidity `yulSyntaxTests`: 319 checked; 106 expected successes, 213 expected
  failures, 162 known mismatches, all 162 false accepts and **zero false
  rejects**. No unexpected or stale entries.
- Solidity `yulInterpreterTests`: 54 checked; 19 pass and 35 fail, exactly the
  checked-in known-failure set. No unexpected or stale entries.

## Still missing / follow-up work

- The compatibility parser itself does not yet have a canonical round-trip
  theorem. This is intentional because hex expressions are lowered and the
  current `Object` AST loses source interleaving. Either enrich the AST or prove
  the documented normalization relation.
- Escape sequences are retained in source spelling rather than decoded into
  their byte values. That is sufficient for parsing and canonical preservation,
  but byte-accurate string semantics should eventually get an explicit AST
  representation/decoder.
- The compatibility statement grammar currently mirrors the verified grammar;
  it can be factored to reduce duplication once a parameterized parser design
  is chosen.
- Parser compatibility still lacks typed identifiers. The remaining 162 syntax
  mismatches are semantic false accepts, not false rejects.
- Object roots still cannot be compiled: verified object layout and constructor
  support (`dataoffset`/`datasize`/`datacopy`) remain separate future work.

