import YulParser.Core

/-!
# YulParser.Combinators

Sequencing (`andThen`), choice (`orElse`), option (`opt`), and map (`pmap`).
-/

namespace YulParser

/-- A whitespace separator (a single space). -/
def sep : List Char := [' ']

/-- Run `p` then `q`, pairing the results. -/
def andThen {α β : Type} (p : Parser α) (q : Parser β) : Parser (α × β) := fun cs =>
  (p cs).bind fun ar => (q ar.2).bind fun br => some ((ar.1, br.1), br.2)

/-- Transform the result of a parser. -/
def pmap {α β : Type} (f : α → β) (p : Parser α) : Parser β := fun cs =>
  (p cs).bind fun ar => some (f ar.1, ar.2)

/-- Try `p`; on failure, try `q`. -/
def orElse {α : Type} (p q : Parser α) : Parser α := fun cs =>
  match p cs with
  | some r => some r
  | none => q cs

/-- Optionally run `p`. -/
def opt {α : Type} (p : Parser α) : Parser (Option α) := fun cs =>
  match p cs with
  | some (a, r) => some (some a, r)
  | none => some (none, cs)

end YulParser
