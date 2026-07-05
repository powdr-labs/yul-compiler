import Mathlib
import YulParser.Lexer

/-!
# YulParser.Canon

An **independent** syntactic canonical form for Yul source, defined with no reference to the
parser: a total maximal-munch lexer `canon : List Char → List CTok` that

* drops all whitespace and C++-style comments (`//…` line, `/* … */` block), and
* evaluates every number literal (decimal or `0x…` hex) to its `Nat` value.

Everything else (identifiers, strings, punctuation, `:=`) is preserved verbatim. Two sources are
"the same modulo whitespace / comments / number-base" exactly when they have the same `canon`.

The load-bearing structural notion is `Closed x := ∀ y, canon (x ++ y) = canon x ++ canon y`: a
character list that never interacts with whatever follows it. `Closed` is closed under append, and
every complete token followed by a delimiter is `Closed`, so distributivity over the parser's
printed forms follows compositionally (no per-seam reasoning).
-/

namespace YulParser

open YulParser (isWs isIdStart isIdCont isDigitC isHexDigitC afterBlockComment afterBlockComment_le
  skipTrivia dropWhile_le)

/-- A normalized token. Numbers are stored by value; whitespace and comments produce no
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
      | other => CTok.punct [':'] :: canon other
    else if c == '/' then
      match rest with
      | '/' :: r => canon (r.dropWhile (· != '\n'))          -- `//` line comment, dropped
      | '*' :: r => canon (afterBlockComment r)              -- `/* … */` block comment, dropped
      | other => CTok.punct ['/'] :: canon other
    else
      CTok.punct [c] :: canon rest
  termination_by cs.length
  decreasing_by
    all_goals simp_wf
    all_goals
      first
        | omega
        | exact dwle _ _
        | exact Nat.le_succ_of_le (dwle _ _)
        | exact Nat.le_succ_of_le (Nat.le_succ_of_le (dwle _ _))
        | exact afterBlockComment_le _
        | exact Nat.le_succ_of_le (afterBlockComment_le _)
        | exact Nat.le_succ_of_le (Nat.le_succ_of_le (afterBlockComment_le _))
        | exact Nat.le_trans (tail_le _) (dwle _ _)
        | exact Nat.le_succ_of_le (Nat.le_trans (tail_le _) (dwle _ _))
        | exact Nat.lt_of_le_of_lt (dwle _ _) (Nat.lt_succ_self _)
        | exact Nat.lt_succ_of_le (Nat.le_trans (tail_le _) (dwle _ _))
        | (refine Nat.lt_of_le_of_lt (dwle _ _) ?_; omega)
        | (refine Nat.lt_of_le_of_lt (afterBlockComment_le _) ?_; omega)

@[simp] theorem canon_nil : canon [] = [] := by rw [canon.eq_def]

/-! ### One-step equations (reusable unfoldings) -/

theorem canon_ws {c : Char} {rest : List Char} (h : isWs c = true) :
    canon (c :: rest) = canon rest := by rw [canon.eq_def]; simp [h]

theorem canon_ident {c : Char} {rest : List Char}
    (hw : isWs c = false) (hq : (c == '"') = false) (hi : isIdStart c = true) :
    canon (c :: rest)
      = CTok.ident (c :: rest.takeWhile isIdCont) :: canon (rest.dropWhile isIdCont) := by
  rw [canon.eq_def]; simp [hw, hq, hi]

theorem canon_num {c : Char} {rest : List Char}
    (hw : isWs c = false) (hq : (c == '"') = false) (hi : isIdStart c = false)
    (hd : isDigitC c = true) :
    canon (c :: rest)
      = CTok.num (numVal (c :: rest.takeWhile isNumCont)) :: canon (rest.dropWhile isNumCont) := by
  rw [canon.eq_def]; simp [hw, hq, hi, hd]

theorem canon_punct {c : Char} {rest : List Char}
    (hw : isWs c = false) (hq : (c == '"') = false) (hi : isIdStart c = false)
    (hd : isDigitC c = false) (hc : (c == ':') = false) (hs : (c == '/') = false) :
    canon (c :: rest) = CTok.punct [c] :: canon rest := by
  rw [canon.eq_def]; simp [hw, hq, hi, hd, hc, hs]

theorem canon_assign {r : List Char} :
    canon (':' :: '=' :: r) = CTok.punct [':', '='] :: canon r := by
  rw [canon.eq_def]; simp [isWs, isIdStart, isDigitC]

theorem canon_str {rest : List Char} :
    canon ('"' :: rest)
      = CTok.str (rest.takeWhile (· != '"')) :: canon (rest.dropWhile (· != '"')).tail := by
  rw [canon.eq_def]; simp [isWs]

/-- `//` line comment: skip to end of line. -/
theorem canon_line_comment {r : List Char} :
    canon ('/' :: '/' :: r) = canon (r.dropWhile (· != '\n')) := by
  rw [canon.eq_def]; simp [isWs, isIdStart, isDigitC]

/-- `/* … */` block comment: skip past the terminator. -/
theorem canon_block_comment {r : List Char} :
    canon ('/' :: '*' :: r) = canon (afterBlockComment r) := by
  rw [canon.eq_def]; simp [isWs, isIdStart, isDigitC]

/-- `canon` ignores leading trivia (whitespace and comments) — it skips exactly what
`skipTrivia` removes. -/
theorem canon_skipTrivia (cs : List Char) : canon (skipTrivia cs) = canon cs := by
  fun_induction skipTrivia cs <;> simp_all
  · exact (canon_ws (by assumption)).symm
  · exact canon_line_comment.symm
  · exact canon_block_comment.symm

/-! ### `Closed`: prefixes that do not interact with their continuation -/

/-- `x` is *closed* when `canon` splits cleanly at the end of `x`: nothing following `x` can merge
into `x`'s last token. This is exactly the distributivity needed to compose the soundness
invariant, and it is preserved by append. -/
def Closed (x : List Char) : Prop := ∀ y, canon (x ++ y) = canon x ++ canon y

theorem closed_nil : Closed [] := by intro y; simp

theorem closed_append {x z : List Char} (hx : Closed x) (hz : Closed z) : Closed (x ++ z) := by
  intro y
  rw [List.append_assoc, hx (z ++ y), hz y, hx z, List.append_assoc]

/-- If `x` is closed then it absorbs trailing whitespace under `canon`. -/
theorem canon_append_of_closed {x : List Char} (hx : Closed x) (y : List Char) :
    canon (x ++ y) = canon x ++ canon y := hx y

/-! ### Character-class disjointness (needed to fire the one-step equations) -/

theorem idStart_not_ws {c : Char} (h : isIdStart c = true) : isWs c = false := by
  by_contra hc
  simp only [Bool.not_eq_false, isWs, Bool.or_eq_true, beq_iff_eq] at hc
  rcases hc with (((rfl | rfl) | rfl) | rfl) <;> exact absurd h (by decide)

theorem idStart_not_quote {c : Char} (h : isIdStart c = true) : (c == '"') = false := by
  by_contra hc; simp only [Bool.not_eq_false, beq_iff_eq] at hc; subst hc; exact absurd h (by decide)

theorem digit_not_ws {c : Char} (h : isDigitC c = true) : isWs c = false := by
  by_contra hc
  simp only [Bool.not_eq_false, isWs, Bool.or_eq_true, beq_iff_eq] at hc
  rcases hc with (((rfl | rfl) | rfl) | rfl) <;> exact absurd h (by decide)

theorem digit_not_quote {c : Char} (h : isDigitC c = true) : (c == '"') = false := by
  by_contra hc; simp only [Bool.not_eq_false, beq_iff_eq] at hc; subst hc; exact absurd h (by decide)

theorem digit_not_idStart {c : Char} (hd : isDigitC c = true) : isIdStart c = false := by
  by_contra h
  simp only [Bool.not_eq_false] at h
  simp only [isDigitC, decide_eq_true_eq] at hd
  simp only [isIdStart, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with (ha | rfl) | rfl
  · simp only [Char.isAlpha, Char.isUpper, Char.isLower, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq] at ha
    rcases ha with ⟨hA, _⟩ | ⟨ha2, _⟩
    · exact absurd (le_trans hA hd.2) (by decide)
    · exact absurd (le_trans ha2 hd.2) (by decide)
  · exact absurd hd.2 (by decide)
  · exact absurd hd.1 (by decide)

/-! ### `takeWhile`/`dropWhile` over an all-satisfying prefix -/

theorem takeWhile_append_all {α} {p : α → Bool} {ts : List α} (h : ∀ x ∈ ts, p x = true)
    (z : List α) : (ts ++ z).takeWhile p = ts ++ z.takeWhile p := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    have ht : p t = true := h t (by simp)
    rw [List.cons_append, List.takeWhile_cons, if_pos ht, ih (fun x hx => h x (by simp [hx])),
      List.cons_append]

theorem dropWhile_append_all {α} {p : α → Bool} {ts : List α} (h : ∀ x ∈ ts, p x = true)
    (z : List α) : (ts ++ z).dropWhile p = z.dropWhile p := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    have ht : p t = true := h t (by simp)
    rw [List.cons_append, List.dropWhile_cons, if_pos ht, ih (fun x hx => h x (by simp [hx]))]

/-! ### `Closed` for concrete tokens -/

/-- Whitespace is closed. -/
theorem closed_ws {c : Char} (h : isWs c = true) : Closed [c] := by
  intro y; rw [List.singleton_append, canon_ws h, canon_ws h, canon_nil, List.nil_append]

/-- A single punctuation character is closed (self-delimiting). -/
theorem closed_punct {c : Char} (hw : isWs c = false) (hq : (c == '"') = false)
    (hi : isIdStart c = false) (hd : isDigitC c = false) (hc : (c == ':') = false)
    (hs : (c == '/') = false) : Closed [c] := by
  intro y
  rw [List.singleton_append, canon_punct hw hq hi hd hc hs, canon_punct hw hq hi hd hc hs,
    canon_nil]
  simp

/-- The assignment token `:=` is closed. -/
theorem closed_assign : Closed [':', '='] := by
  intro y
  have : ([':', '='] ++ y) = ':' :: '=' :: y := rfl
  rw [this, canon_assign]
  show CTok.punct [':', '='] :: canon y = canon [':', '='] ++ canon y
  rw [show [':', '='] = ':' :: '=' :: ([] : List Char) from rfl, canon_assign]; simp

/-- An identifier token (followed by a delimiting space) is closed. -/
theorem closed_ident {c : Char} {ts : List Char} (hc : isIdStart c = true)
    (hts : ∀ x ∈ ts, isIdCont x = true) : Closed (c :: (ts ++ [' '])) := by
  have hns : isIdCont ' ' = false := by decide
  have key : ∀ y, canon (c :: (ts ++ ' ' :: y)) = CTok.ident (c :: ts) :: canon y := by
    intro y
    rw [canon_ident (idStart_not_ws hc) (idStart_not_quote hc) hc,
        takeWhile_append_all hts, dropWhile_append_all hts,
        List.takeWhile_cons, List.dropWhile_cons, hns]
    simp only [Bool.false_eq_true, if_false, List.append_nil]
    rw [canon_ws (by decide : isWs ' ' = true)]
  intro y
  have e1 : c :: (ts ++ [' ']) ++ y = c :: (ts ++ ' ' :: y) := by simp
  have e2 : c :: (ts ++ [' ']) = c :: (ts ++ ' ' :: []) := by simp
  rw [e1, key y, e2, key [], canon_nil]; simp

/-- A number token (followed by a delimiting space) is closed. -/
theorem closed_num {c : Char} {ns : List Char} (hc : isDigitC c = true)
    (hns : ∀ x ∈ ns, isNumCont x = true) : Closed (c :: (ns ++ [' '])) := by
  have hnsp : isNumCont ' ' = false := by decide
  have key : ∀ y, canon (c :: (ns ++ ' ' :: y))
      = CTok.num (numVal (c :: ns)) :: canon y := by
    intro y
    rw [canon_num (digit_not_ws hc) (digit_not_quote hc) (digit_not_idStart hc) hc,
        takeWhile_append_all hns, dropWhile_append_all hns,
        List.takeWhile_cons, List.dropWhile_cons, hnsp]
    simp only [Bool.false_eq_true, if_false, List.append_nil]
    rw [canon_ws (by decide : isWs ' ' = true)]
  intro y
  have e1 : c :: (ns ++ [' ']) ++ y = c :: (ns ++ ' ' :: y) := by simp
  have e2 : c :: (ns ++ [' ']) = c :: (ns ++ ' ' :: []) := by simp
  rw [e1, key y, e2, key [], canon_nil]; simp

/-- A string token `"…"` (followed by a delimiting space) is closed. -/
theorem closed_str {content : List Char} (hcont : ∀ x ∈ content, (x != '"') = true) :
    Closed ('"' :: (content ++ '"' :: [' '])) := by
  have key : ∀ y, canon ('"' :: (content ++ '"' :: ' ' :: y)) = CTok.str content :: canon y := by
    intro y
    rw [canon_str, takeWhile_append_all hcont, dropWhile_append_all hcont]
    simp only [List.takeWhile_cons, List.dropWhile_cons, (by decide : ('"' != '"') = false),
      Bool.false_eq_true, if_false, List.append_nil, List.tail_cons]
    rw [canon_ws (by decide : isWs ' ' = true)]
  intro y
  have e1 : '"' :: (content ++ '"' :: [' ']) ++ y = '"' :: (content ++ '"' :: ' ' :: y) := by simp
  have e2 : '"' :: (content ++ '"' :: [' ']) = '"' :: (content ++ '"' :: ' ' :: []) := by simp
  rw [e1, key y, e2, key [], canon_nil]; simp

end YulParser
