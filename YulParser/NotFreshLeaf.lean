import YulParser.Lexer
import YulEvmCompiler.Optimizer.Implementation.Normalization.Disambiguate.Alpha
set_option warningAsError true
/-!
# Leaf lemma for the parser boundary: parsed identifiers are `NotFresh`

The `SVStmts` conjunct of `Normalize.SourceValid` requires every identifier to be
`NotFresh` (no leading `NUL`; the disambiguator's fresh names are `dsName k =
"\0v…v"`). `validateBlock` never checks this — it is a **lexer** guarantee: the
identifier lexer only accepts characters with `isIdStart`/`isIdCont`, and `NUL`
is neither. This file proves the leaf fact that closes that gap: an identifier
whose first character satisfies `isIdStart` cannot be any `dsName`, hence is
`NotFresh`. See `YulParser/PARSER_BOUNDARY_PLAN.md` for how this feeds the full
`parseSource ⟹ SourceValid` boundary (part 2).
-/

namespace YulParser

open YulEvmCompiler.Optimizer.Normalize (NotFresh dsName)

/-- `NUL` (`Char.ofNat 0`, the lead character of every `dsName`) is not a valid
identifier start. -/
theorem isIdStart_nul : isIdStart (Char.ofNat 0) = false := by decide

/-- **A lexed identifier is never a fresh name.** Any string whose first
character is a valid identifier start differs from every `dsName k` (which starts
with `NUL`), so it is `NotFresh`. This is the leaf the parser-boundary proof of
`SVStmts` rests on. -/
theorem notFresh_of_isIdStart_head {c : Char} {rest : List Char}
    (h : isIdStart c = true) : NotFresh (String.ofList (c :: rest)) := by
  intro k hk
  simp only [dsName, String.ofList_inj, List.cons.injEq] at hk
  rw [hk.1, isIdStart_nul] at h
  exact absurd h (by decide)

end YulParser
