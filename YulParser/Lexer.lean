import YulParser.Tokens

/-!
# YulParser.Lexer

Character classes, greedy spans (`pWhile1`/`pWhile0`), the word-boundary check (`notIdCont`), and
keyword/symbol tokens.
-/

namespace YulParser

/-! ### Character classes -/

def isDigitC (c : Char) : Bool := '0' ≤ c ∧ c ≤ '9'
def isHexDigitC (c : Char) : Bool :=
  isDigitC c || ('a' ≤ c ∧ c ≤ 'f') || ('A' ≤ c ∧ c ≤ 'F')
def isIdStart (c : Char) : Bool := c.isAlpha || c == '_' || c == '$'
def isIdCont (c : Char) : Bool := isIdStart c || isDigitC c || c == '.'
/-- String content: anything but a double quote or newline. -/
def isStrChar (c : Char) : Bool := c != '"' && c != '\n' && c != '\r'

/-! ### Spans -/

/-- Consume one-or-more characters: the first satisfying `first`, the rest `cont`, greedily. -/
def pWhile1 (first cont : Char → Bool) : Parser (List Char) := fun cs =>
  match cs with
  | [] => none
  | c :: rest => if first c then some (c :: rest.takeWhile cont, rest.dropWhile cont) else none

/-- Consume zero-or-more characters satisfying `cont`, greedily. -/
def pWhile0 (cont : Char → Bool) : Parser (List Char) := fun cs =>
  some (cs.takeWhile cont, cs.dropWhile cont)

/-! ### Keywords and symbols -/

/-- Succeeds (consuming nothing) unless the next character continues an identifier — the boundary
check that keeps `true` from matching inside `trueValue`. -/
def notIdCont : Parser Unit := fun cs =>
  match cs with
  | [] => some ((), cs)
  | c :: _ => if isIdCont c then none else some ((), cs)

/-- A keyword: skip leading trivia, match `s`, and require a word boundary. -/
def keyword (s : List Char) : Parser Unit :=
  token (pmap (fun _ => ()) (andThen (pstr s) notIdCont))

/-- A symbol token (punctuation, no word boundary needed). -/
def symbol (s : List Char) : Parser Unit := token (pstr s)

end YulParser
