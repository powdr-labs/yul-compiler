set_option warningAsError true
/-! # YulParser.Core

Primitive parser combinators. A `Parser α` consumes a prefix of the input and returns a value with
the remaining suffix.
-/

namespace YulParser

/-- Whitespace characters (space, tab, newline, carriage return). -/
def isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- A parser consumes a prefix of the input, returning a value and the remaining suffix. -/
abbrev Parser (α : Type) := List Char → Option (α × List Char)

/-- The parser that consumes nothing and returns `a`. -/
def ppure {α : Type} (a : α) : Parser α := fun cs => some (a, cs)

/-- Consume one character satisfying `pred`. -/
def satisfy (pred : Char → Bool) : Parser Char := fun cs =>
  match cs with
  | [] => none
  | c :: rest => if pred c then some (c, rest) else none

/-- Consume a specific character `c`. -/
def pchar (c : Char) : Parser Char := satisfy (· == c)

end YulParser
