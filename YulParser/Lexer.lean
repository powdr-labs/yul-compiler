import YulParser.Tokens
import YulParser.Ast

/-!
# YulParser.Lexer

Character-class spans, identifiers, and literals, each sound for its printer.
The printers here are the *real* ones (no spurious separators inside atoms); a
combinator may glue with a whitespace `sep`, but `fws` deletes it, so `pmap`
soundness still lines up.
-/

namespace YulParser

/-! ### Character classes -/

def isDigitC (c : Char) : Bool := '0' ≤ c ∧ c ≤ '9'
def isHexDigitC (c : Char) : Bool :=
  isDigitC c || ('a' ≤ c ∧ c ≤ 'f') || ('A' ≤ c ∧ c ≤ 'F')
def isIdStart (c : Char) : Bool := c.isAlpha || c == '_' || c == '$'
def isIdCont (c : Char) : Bool := isIdStart c || isDigitC c || c == '.'
/-- String content: anything but a double quote or newline (no escapes). -/
def isStrChar (c : Char) : Bool := c != '"' && c != '\n' && c != '\r'

/-! ### Spans -/

/-- Consume one-or-more characters: the first satisfying `first`, the rest
`cont`, greedily. -/
def pWhile1 (first cont : Char → Bool) : Parser (List Char) := fun cs =>
  match cs with
  | [] => none
  | c :: rest => if first c then some (c :: rest.takeWhile cont, rest.dropWhile cont) else none

theorem pWhile1_sound (first cont : Char → Bool) : Sound (pWhile1 first cont) (fun s => s) := by
  intro cs a rest h
  cases cs with
  | nil => simp [pWhile1] at h
  | cons c cs' =>
    simp only [pWhile1] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      show fws (c :: cs'.takeWhile cont) ++ fws (cs'.dropWhile cont) = fws (c :: cs')
      rw [← fws_append, List.cons_append, List.takeWhile_append_dropWhile]
    · exact absurd h (by simp)

/-- Consume zero-or-more characters satisfying `cont`, greedily. -/
def pWhile0 (cont : Char → Bool) : Parser (List Char) := fun cs =>
  some (cs.takeWhile cont, cs.dropWhile cont)

theorem pWhile0_sound (cont : Char → Bool) : Sound (pWhile0 cont) (fun s => s) := by
  intro cs a rest h
  simp only [pWhile0, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  show fws (cs.takeWhile cont) ++ fws (cs.dropWhile cont) = fws cs
  rw [← fws_append, List.takeWhile_append_dropWhile]

/-! ### Identifiers -/

/-- A raw identifier (no leading-whitespace skipping). -/
def pidentRaw : Parser Id := pWhile1 isIdStart isIdCont

theorem pidentRaw_sound : Sound pidentRaw (fun s => s) := pWhile1_sound _ _

/-- Computational `fws` on a cons: keep `c` unless it is whitespace. Lets `simp`
evaluate `fws` on concrete printed strings. -/
@[simp] theorem fws_cons_simp (c : Char) (xs : List Char) :
    fws (c :: xs) = (if isWs c then [] else [c]) ++ fws xs := by
  simp only [fws, List.filter_cons]; split <;> simp_all

/-! ### Literal printer -/

/-- Re-print a literal exactly (no spurious separators). -/
def printLit : Lit → List Char
  | .dec d => d
  | .hex d => '0' :: 'x' :: d
  | .str c => '"' :: (c ++ ['"'])
  | .hexstr c => 'h' :: 'e' :: 'x' :: '"' :: (c ++ ['"'])
  | .true => ['t','r','u','e']
  | .false => ['f','a','l','s','e']

/-! ### Keywords and symbols -/

/-- Succeeds (consuming nothing) unless the next character continues an
identifier — the boundary check that keeps `true` from matching inside
`trueValue`. -/
def notIdCont : Parser Unit := fun cs =>
  match cs with
  | [] => some ((), cs)
  | c :: _ => if isIdCont c then none else some ((), cs)

theorem notIdCont_sound : Sound notIdCont (fun _ => []) := by
  intro cs a rest h
  cases cs with
  | nil => simp only [notIdCont, Option.some.injEq, Prod.mk.injEq] at h
           obtain ⟨_, rfl⟩ := h; simp
  | cons c cs' =>
    simp only [notIdCont] at h
    split at h
    · exact absurd h (by simp)
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h; simp

/-- A keyword: skip leading whitespace, match `s`, and require a word boundary. -/
def keyword (s : List Char) : Parser Unit :=
  token (pmap (fun _ => ()) (andThen (pstr s) notIdCont))

theorem keyword_sound (s : List Char) : Sound (keyword s) (fun _ => s) := by
  apply token_sound
  apply pmap_sound (andThen_sound (pstr_sound s) notIdCont_sound)
  intro a; simp [sep, fws_cons_simp, isWs]

/-- A symbol token (punctuation, no word boundary needed). -/
def symbol (s : List Char) : Parser Unit := token (pstr s)

theorem symbol_sound (s : List Char) : Sound (symbol s) (fun _ => s) :=
  token_sound (pstr_sound s)

/-! ### Literals -/

/-- Decimal number literal. -/
def pDec : Parser Lit := pmap Lit.dec (pWhile1 isDigitC isDigitC)

theorem pDec_sound : Sound pDec printLit :=
  pmap_sound (pWhile1_sound _ _) (fun _ => rfl)

/-- Hex number literal `0x…`. -/
def pHex : Parser Lit :=
  pmap (fun p => Lit.hex p.2) (andThen (pstr ['0','x']) (pWhile1 isHexDigitC isHexDigitC))

theorem pHex_sound : Sound pHex printLit := by
  apply pmap_sound (andThen_sound (pstr_sound ['0','x']) (pWhile1_sound _ _))
  intro a; simp [printLit, sep, fws_cons_simp, isWs]

/-- String literal `"…"` (no escapes; content excludes `"` and newlines). -/
def pStr : Parser Lit :=
  pmap (fun p => Lit.str p.1.2)
    (andThen (andThen (pchar '"') (pWhile0 isStrChar)) (pchar '"'))

theorem pStr_sound : Sound pStr printLit := by
  apply pmap_sound
    (andThen_sound (andThen_sound (pchar_sound '"') (pWhile0_sound _)) (pchar_sound '"'))
  intro a; simp [printLit, sep, fws_cons_simp, fws_append, isWs]

/-- Hex string literal `hex"…"`. -/
def pHexStr : Parser Lit :=
  pmap (fun p => Lit.hexstr p.1.2)
    (andThen (andThen (pstr ['h','e','x','"']) (pWhile0 isStrChar)) (pchar '"'))

theorem pHexStr_sound : Sound pHexStr printLit := by
  apply pmap_sound
    (andThen_sound (andThen_sound (pstr_sound _) (pWhile0_sound _)) (pchar_sound '"'))
  intro a; simp [printLit, sep, fws_cons_simp, fws_append, isWs]

/-- `true` literal. -/
def pTrue : Parser Lit := pmap (fun _ => Lit.true) (keyword ['t','r','u','e'])

theorem pTrue_sound : Sound pTrue printLit :=
  pmap_sound (keyword_sound _) (fun _ => rfl)

/-- `false` literal. -/
def pFalse : Parser Lit := pmap (fun _ => Lit.false) (keyword ['f','a','l','s','e'])

theorem pFalse_sound : Sound pFalse printLit :=
  pmap_sound (keyword_sound _) (fun _ => rfl)

/-- Any literal. Hex is tried before decimal (so `0x…` is not read as `0`). -/
def pLit : Parser Lit :=
  orElse pHex (orElse pDec (orElse pHexStr (orElse pStr (orElse pTrue pFalse))))

theorem pLit_sound : Sound pLit printLit :=
  orElse_sound pHex_sound (orElse_sound pDec_sound (orElse_sound pHexStr_sound
    (orElse_sound pStr_sound (orElse_sound pTrue_sound pFalse_sound))))

end YulParser
