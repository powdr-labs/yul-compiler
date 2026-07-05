import YulParser.Lexer

/-!
# YulSemParser.Canon

An **independent** syntactic canonical form for Yul source, defined with no reference to the
parser: a total maximal-munch lexer `canon : List Char → List CTok` that

* drops all whitespace,
* evaluates every number literal (decimal or `0x…` hex) to its `Nat` value, and
* strips type annotations (`:ident`).

Everything else (identifiers, strings, punctuation, `:=`) is preserved verbatim. Two sources are
"the same modulo whitespace / number-base / types" exactly when they have the same `canon`.

The load-bearing structural notion is `Closed x := ∀ y, canon (x ++ y) = canon x ++ canon y`: a
character list that never interacts with whatever follows it. `Closed` is closed under append, and
every complete token followed by a delimiter is `Closed`, so distributivity over the parser's
printed forms follows compositionally (no per-seam reasoning).
-/

namespace YulSemParser

open YulParser (isWs isIdStart isIdCont isDigitC isHexDigitC)

/-- A normalized token. Numbers are stored by value; whitespace and type annotations produce no
token at all. -/
inductive CTok
  | ident (s : List Char)
  | num   (n : Nat)
  | str   (c : List Char)
  | punct (s : List Char)
  deriving DecidableEq, Repr

/-! ### Number evaluation -/

/-- Value of a hex digit (`0` on a non-hex character; never reached on well-formed tokens). -/
def hexDigitVal (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else if 'A' ≤ c ∧ c ≤ 'F' then c.toNat - 'A'.toNat + 10
  else 0

/-- Value of a decimal digit. -/
def decDigitVal (c : Char) : Nat := c.toNat - '0'.toNat

/-- Evaluate a list of hex-digit characters, most-significant first. -/
def evalHex (ds : List Char) : Nat := ds.foldl (fun acc c => acc * 16 + hexDigitVal c) 0

/-- Evaluate a list of decimal-digit characters, most-significant first. -/
def evalDec (ds : List Char) : Nat := ds.foldl (fun acc c => acc * 10 + decDigitVal c) 0

/-- Characters that continue a number token: hex digits plus the `x` of a `0x` prefix. (A
well-formed number is all-decimal or `0x`-hex; on those this munches exactly the literal.) -/
def isNumCont (c : Char) : Bool := isHexDigitC c || c == 'x' || c == 'X'

/-- Value of a whole number token (decimal, or `0x…`/`0X…` hex). -/
def numVal : List Char → Nat
  | '0' :: 'x' :: ds => evalHex ds
  | '0' :: 'X' :: ds => evalHex ds
  | ds => evalDec ds

/-- `tail` never lengthens a list. -/
theorem tail_le {α} (l : List α) : l.tail.length ≤ l.length := by cases l <;> simp

/-- `dropWhile` never lengthens a list. -/
theorem dwle {α} (l : List α) (p : α → Bool) : (l.dropWhile p).length ≤ l.length := by
  have h : (l.takeWhile p ++ l.dropWhile p).length = l.length := by
    rw [List.takeWhile_append_dropWhile]
  rw [List.length_append] at h; omega

/-! ### The lexer -/

/-- Maximal-munch lexer to the canonical token list. Total. -/
def canon (cs : List Char) : List CTok :=
  match cs with
  | [] => []
  | c :: rest =>
    if isWs c then canon rest
    else if c == '"' then
      CTok.str (rest.takeWhile (· != '"')) :: canon (rest.dropWhile (· != '"')).tail
    else if isIdStart c then
      CTok.ident (c :: rest.takeWhile isIdCont) :: canon (rest.dropWhile isIdCont)
    else if isDigitC c then
      CTok.num (numVal (c :: rest.takeWhile isNumCont)) :: canon (rest.dropWhile isNumCont)
    else if c == ':' then
      match rest with
      | '=' :: r => CTok.punct [':', '='] :: canon r
      | d :: r =>
        if isIdStart d then canon (r.dropWhile isIdCont)      -- `:ident` type annotation, dropped
        else CTok.punct [':'] :: canon (d :: r)
      | [] => [CTok.punct [':']]
    else
      CTok.punct [c] :: canon rest
  termination_by cs.length
  decreasing_by
    all_goals simp_wf
    all_goals
      first
        | omega
        | exact Nat.lt_of_le_of_lt (dwle _ _) (by omega)
        | (have h1 := dwle rest (· != '"')
           have h2 := tail_le (rest.dropWhile (· != '"')); omega)

end YulSemParser
