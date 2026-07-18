import YulParser.Tokens

set_option warningAsError true

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

/-! ### Quoted strings -/

/-- Scan the body of a quoted Yul string. Backslash escapes are retained in
their source spelling, but an escaped quote does not terminate the string.
Literal newlines and carriage returns are rejected. -/
def quotedBody : List Char → Option (List Char × List Char)
  | [] => none
  | '"' :: rest => some ([], rest)
  | '\\' :: escaped :: rest =>
      if escaped == '\n' || escaped == '\r' then none
      else
        match quotedBody rest with
        | some (body, after) => some ('\\' :: escaped :: body, after)
        | none => none
  | c :: rest =>
      if c == '\n' || c == '\r' then none
      else
        match quotedBody rest with
        | some (body, after) => some (c :: body, after)
        | none => none

/-- Parse a complete quoted string, returning its escape-preserving body. -/
def pQuotedChars : Parser (List Char) := fun cs =>
  match cs with
  | '"' :: rest => quotedBody rest
  | _ => none

theorem quotedBody_rest_lt {cs body rest}
    (h : quotedBody cs = some (body, rest)) : rest.length < cs.length := by
  fun_induction quotedBody cs generalizing body rest <;> simp_all <;> omega

theorem pQuotedChars_rest_lt {cs body rest}
    (h : pQuotedChars cs = some (body, rest)) : rest.length < cs.length := by
  cases cs with
  | nil => simp [pQuotedChars] at h
  | cons c cs =>
      simp only [pQuotedChars] at h
      split at h
      · have := quotedBody_rest_lt h; simp_all; omega
      · contradiction

structure QuotedScan (input : List Char) where
  body : List Char
  rest : List Char
  shorter : rest.length < input.length

/-- Proof-carrying wrapper used by the total canonical lexer. -/
def scanQuoted (input : List Char) : Option (QuotedScan input) :=
  match h : pQuotedChars input with
  | some (body, rest) => some ⟨body, rest, pQuotedChars_rest_lt h⟩
  | none => none

/-- Well-formed escape-preserving contents of a quoted string. -/
inductive QuotedBody : List Char → Prop where
  | nil : QuotedBody []
  | escaped {c rest} (hn : c ≠ '\n') (hr : c ≠ '\r')
      (tail : QuotedBody rest) : QuotedBody ('\\' :: c :: rest)
  | char {c rest} (hq : c ≠ '"') (hs : c ≠ '\\')
      (hn : c ≠ '\n') (hr : c ≠ '\r')
      (tail : QuotedBody rest) : QuotedBody (c :: rest)

theorem quotedBody_self {cs body rest}
    (h : quotedBody cs = some (body, rest)) : QuotedBody body := by
  fun_induction quotedBody cs generalizing body rest <;> simp_all
  case case2 => exact .nil
  case case4 =>
    rename_i escaped input parsedBody after hnr hparse ih
    obtain ⟨rfl, rfl⟩ := h
    exact .escaped hnr.1 hnr.2 ih
  case case7 =>
    rename_i c input parsedBody after hquote hslash hnr hparse ih
    obtain ⟨rfl, rfl⟩ := h
    have hs : c ≠ '\\' := by
      intro hc
      cases input with
      | nil => simp [quotedBody] at hparse
      | cons escaped tail => exact (hslash escaped tail hc) rfl
    exact .char hquote hs hnr.1 hnr.2 ih

theorem pQuotedChars_body {cs body rest}
    (h : pQuotedChars cs = some (body, rest)) : QuotedBody body := by
  cases cs with
  | nil => simp [pQuotedChars] at h
  | cons c input =>
      simp only [pQuotedChars] at h
      split at h
      · exact quotedBody_self h
      · contradiction

theorem QuotedBody.scan {body : List Char} (h : QuotedBody body) (rest : List Char) :
    quotedBody (body ++ '"' :: rest) = some (body, rest) := by
  induction h <;> simp_all [quotedBody]

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
