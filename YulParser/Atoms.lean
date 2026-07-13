import YulParser.SoundC
import YulSemantics.Ast

/-!
# YulParser.Atoms

Atomic parsers producing `yul-semantics` values (`Literal`, identifiers as
`String`), plus keyword and punctuation tokens.
Each atom prints its token followed by a delimiting space (so the printed form
is `Closed`), and is proven `SoundC`.
-/

namespace YulParser

open YulParser (Parser token pWhile1 pstr isWs isIdStart isIdCont isDigitC isHexDigitC pchar
  pWhile0 keyword notIdCont satisfy pmap)
open YulSemantics (Literal)

/-! ### Maximal-munch helper -/

/-- The head of a `dropWhile` fails the predicate, so a further `takeWhile` is empty. -/
theorem takeWhile_dropWhile_nil {α} (p : α → Bool) (l : List α) :
    (l.dropWhile p).takeWhile p = [] := by
  induction l with
  | nil => simp
  | cons a as ih =>
    rw [List.dropWhile_cons]
    split
    · exact ih
    · rename_i hpa; simp [hpa]

/-! ### Identifiers -/

/-- Raw identifier characters (whitespace-skipping). -/
def pIdentChars : Parser (List Char) := token (pWhile1 isIdStart isIdCont)

theorem pIdentChars_soundC : SoundC pIdentChars (fun d => d ++ [' ']) := by
  intro cs d rest h
  simp only [pIdentChars, token] at h
  set cs' := YulParser.skipTrivia cs with hcs'
  cases hc : cs' with
  | nil => rw [hc] at h; simp [pWhile1] at h
  | cons c r =>
    rw [hc] at h
    simp only [pWhile1] at h
    split at h
    · rename_i hfirst
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      set ts := r.takeWhile isIdCont with hts
      have htsAll : ∀ x ∈ ts, isIdCont x = true := fun x hx => List.mem_takeWhile_imp hx
      refine ⟨?_, closed_ident hfirst htsAll⟩
      -- canon of the printed token is a single ident
      have tokEq : canon (c :: ts ++ [' ']) = [CTok.ident (c :: ts)] := by
        have e : c :: ts ++ [' '] = c :: (ts ++ ' ' :: ([] : List Char)) := by simp
        rw [e, canon_ident (idStart_not_ws hfirst) (idStart_not_quote hfirst) hfirst,
          takeWhile_append_all htsAll, dropWhile_append_all htsAll]
        simp only [List.takeWhile_cons, List.dropWhile_cons, (by decide : isIdCont ' ' = false),
          Bool.false_eq_true, if_false, List.append_nil]
        rw [canon_ws (by decide : isWs ' ' = true), canon_nil]
      -- canon cs splits as that ident followed by the remainder
      have hcanon_cs : canon cs = CTok.ident (c :: ts) :: canon (r.dropWhile isIdCont) := by
        rw [← canon_skipTrivia cs, ← hcs', hc,
          canon_ident (idStart_not_ws hfirst) (idStart_not_quote hfirst) hfirst]
      rw [hcanon_cs, tokEq, List.singleton_append]
    · exact absurd h (by simp)

/-- An identifier as a `String` (the `yul-semantics` `Ident` type). -/
def pIdent : Parser String := YulParser.pmap String.ofList pIdentChars

theorem pIdent_soundC : SoundC pIdent (fun s => s.toList ++ [' ']) := by
  apply pmapC_eq pIdentChars_soundC
  intro d; rw [String.toList_ofList]

/-! ### Numbers -/

/-- The ASCII digit character for `d < 10`. -/
def digitChar (d : Nat) : Char := Char.ofNat (d + 48)

/-- Decimal digits of a natural number (most-significant first; `0` ↦ `['0']`). -/
def decDigits (n : Nat) : List Char :=
  if n < 10 then [digitChar n] else decDigits (n / 10) ++ [digitChar (n % 10)]
  termination_by n
  decreasing_by exact Nat.div_lt_self (by omega) (by omega)

theorem toNat_digitChar {d : Nat} (h : d < 10) : (digitChar d).toNat = d + 48 := by
  have hv : (d + 48).isValidChar := by left; omega
  rw [digitChar, Char.toNat_ofNat, if_pos hv]

theorem isDigitC_digitChar {d : Nat} (h : d < 10) : isDigitC (digitChar d) = true := by
  interval_cases d <;> decide

theorem decDigitVal_digitChar {d : Nat} (h : d < 10) : decDigitVal (digitChar d) = d := by
  interval_cases d <;> decide

theorem isDigitC_isNumCont {c : Char} (h : isDigitC c = true) : isNumCont c = true := by
  simp [isNumCont, isHexDigitC, h]

theorem decDigits_all_digitC (n : Nat) : ∀ x ∈ decDigits n, isDigitC x = true := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [decDigits]
    split
    · rename_i h; intro x hx
      simp only [List.mem_singleton] at hx; subst hx; exact isDigitC_digitChar h
    · rename_i h
      intro x hx
      rw [List.mem_append] at hx
      rcases hx with hx | hx
      · exact ih (n / 10) (Nat.div_lt_self (by omega) (by omega)) x hx
      · simp only [List.mem_singleton] at hx; subst hx
        exact isDigitC_digitChar (Nat.mod_lt _ (by omega))

theorem decDigits_ne_nil (n : Nat) : decDigits n ≠ [] := by
  rw [decDigits]; split
  · simp
  · simp

theorem evalDec_concat (a : List Char) (x : Char) :
    evalDec (a ++ [x]) = evalDec a * 10 + decDigitVal x := by
  simp only [evalDec, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem evalDec_decDigits (n : Nat) : evalDec (decDigits n) = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [decDigits]
    split
    · rename_i h; simp only [evalDec, List.foldl_cons, List.foldl_nil, Nat.zero_mul,
        Nat.zero_add, decDigitVal_digitChar h]
    · rename_i h
      rw [evalDec_concat, ih (n / 10) (Nat.div_lt_self (by omega) (by omega)),
        decDigitVal_digitChar (Nat.mod_lt _ (by omega))]
      omega

/-- On an all-decimal token, `numVal` is just `evalDec` (the `0x` guard cannot fire). -/
theorem numVal_eq_evalDec (l : List Char) (h : ∀ x ∈ l, isDigitC x = true) :
    numVal l = evalDec l := by
  unfold numVal
  split
  · exact absurd (h 'x' (by simp)) (by decide)
  · exact absurd (h 'X' (by simp)) (by decide)
  · rfl

theorem numVal_decDigits (n : Nat) : numVal (decDigits n) = n := by
  rw [numVal_eq_evalDec _ (decDigits_all_digitC n), evalDec_decDigits n]

/-- `canon` of a printed decimal number is a single `num` token. -/
theorem canon_decDigits (n : Nat) : canon (decDigits n ++ [' ']) = [CTok.num n] := by
  obtain ⟨c, ts, hcts⟩ : ∃ c ts, decDigits n = c :: ts := by
    cases h : decDigits n with
    | nil => exact absurd h (decDigits_ne_nil n)
    | cons c ts => exact ⟨c, ts, rfl⟩
  have hcd : isDigitC c = true := decDigits_all_digitC n c (by rw [hcts]; simp)
  have htsN : ∀ x ∈ ts, isNumCont x = true := fun x hx =>
    isDigitC_isNumCont (decDigits_all_digitC n x (by rw [hcts]; simp [hx]))
  have e : decDigits n ++ [' '] = c :: (ts ++ ' ' :: ([] : List Char)) := by rw [hcts]; simp
  rw [e, canon_num (digit_not_ws hcd) (digit_not_quote hcd) (digit_not_idStart hcd) hcd,
    takeWhile_append_all htsN, dropWhile_append_all htsN]
  simp only [List.takeWhile_cons, List.dropWhile_cons, (by decide : isNumCont ' ' = false),
    Bool.false_eq_true, if_false, List.append_nil]
  rw [canon_ws (by decide : isWs ' ' = true), canon_nil, ← hcts, numVal_decDigits]

theorem closed_decDigits (n : Nat) : Closed (decDigits n ++ [' ']) := by
  obtain ⟨c, ts, hcts⟩ : ∃ c ts, decDigits n = c :: ts := by
    cases h : decDigits n with
    | nil => exact absurd h (decDigits_ne_nil n)
    | cons c ts => exact ⟨c, ts, rfl⟩
  have hcd : isDigitC c = true := decDigits_all_digitC n c (by rw [hcts]; simp)
  have htsN : ∀ x ∈ ts, isNumCont x = true := fun x hx =>
    isDigitC_isNumCont (decDigits_all_digitC n x (by rw [hcts]; simp [hx]))
  have e : decDigits n ++ [' '] = c :: (ts ++ [' ']) := by rw [hcts]; simp
  rw [e]; exact closed_num hcd htsN

/-! ### The literal printer -/

/-- Escape-preserving quoted-string printer shared by literals and object names. -/
def printStringC (content : List Char) : List Char :=
  '"' :: (content ++ '"' :: [' '])

/-- Internal printer for literals: each token followed by a delimiting space. -/
def printLitC : Literal → List Char
  | .number k => decDigits k ++ [' ']
  | .bool true => ['t', 'r', 'u', 'e', ' ']
  | .bool false => ['f', 'a', 'l', 's', 'e', ' ']
  | .string s => printStringC s.toList

/-! ### `pstr` / `notIdCont` facts -/

theorem pchar_consumes {c : Char} {cs r : List Char} {x : Char}
    (h : pchar c cs = some (x, r)) : cs = c :: r := by
  cases cs with
  | nil => simp [pchar, satisfy] at h
  | cons d cs' =>
    simp only [pchar, satisfy] at h
    by_cases hp : (d == c) = true
    · rw [if_pos hp] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; rw [beq_iff_eq] at hp; rw [hp]
    · rw [if_neg hp] at h; exact absurd h (by simp)

theorem pstr_consumes : ∀ (s cs r : List Char), pstr s cs = some ((), r) → cs = s ++ r
  | [], cs, r, h => by simp only [pstr, YulParser.ppure, Option.some.injEq, Prod.mk.injEq] at h;
                       rw [h.2]; rfl
  | c :: s', cs, r, h => by
    simp only [pstr] at h
    cases hpc : pchar c cs with
    | none => rw [hpc] at h; simp at h
    | some xr =>
      obtain ⟨x, r1⟩ := xr
      rw [hpc] at h
      have := pchar_consumes hpc
      rw [this, pstr_consumes s' r1 r h, List.cons_append]

/-- A successful `notIdCont` consumes nothing and leaves a list that a further
identifier munch cannot extend. -/
theorem notIdCont_boundary {r r' : List Char} (h : notIdCont r = some ((), r')) :
    r' = r ∧ r.takeWhile isIdCont = [] ∧ r.dropWhile isIdCont = r := by
  cases r with
  | nil => simp only [notIdCont, Option.some.injEq, Prod.mk.injEq] at h
           obtain ⟨_, rfl⟩ := h; simp
  | cons c cs =>
    simp only [notIdCont] at h
    split at h
    · exact absurd h (by simp)
    · rename_i hcont
      simp only [Bool.not_eq_true] at hcont
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      refine ⟨rfl, ?_, ?_⟩
      · rw [List.takeWhile_cons, hcont]; rfl
      · rw [List.dropWhile_cons, hcont]; rfl

/-- `canon` of an identifier token followed by a space is a single `ident`. -/
theorem canon_ident_space {c : Char} {ts : List Char} (hc : isIdStart c = true)
    (hts : ∀ x ∈ ts, isIdCont x = true) : canon ((c :: ts) ++ [' ']) = [CTok.ident (c :: ts)] := by
  have e : (c :: ts) ++ [' '] = c :: (ts ++ ' ' :: ([] : List Char)) := by simp
  rw [e, canon_ident (idStart_not_ws hc) (idStart_not_quote hc) hc,
    takeWhile_append_all hts, dropWhile_append_all hts]
  simp only [List.takeWhile_cons, List.dropWhile_cons, (by decide : isIdCont ' ' = false),
    Bool.false_eq_true, if_false, List.append_nil]
  rw [canon_ws (by decide : isWs ' ' = true), canon_nil]

/-- `canon` of an identifier token followed by a boundary (non-`idCont`) continuation. -/
theorem canon_ident_boundary {c : Char} {ts rest : List Char} (hc : isIdStart c = true)
    (hts : ∀ x ∈ ts, isIdCont x = true)
    (htk : rest.takeWhile isIdCont = []) (hdw : rest.dropWhile isIdCont = rest) :
    canon ((c :: ts) ++ rest) = CTok.ident (c :: ts) :: canon rest := by
  have e : (c :: ts) ++ rest = c :: (ts ++ rest) := rfl
  rw [e, canon_ident (idStart_not_ws hc) (idStart_not_quote hc) hc,
    takeWhile_append_all hts, dropWhile_append_all hts, htk, hdw, List.append_nil]

/-! ### Keywords and symbols -/

/-- An identifier-shaped keyword `c :: ts` (letters), with a word-boundary check. -/
theorem keywordC {c : Char} {ts : List Char} (hc : isIdStart c = true)
    (hts : ∀ x ∈ ts, isIdCont x = true) :
    SoundC (keyword (c :: ts)) (fun _ => (c :: ts) ++ [' ']) := by
  intro cs a rest h
  simp only [keyword, token, pmap, YulParser.andThen] at h
  cases hp : pstr (c :: ts) (YulParser.skipTrivia cs) with
  | none => rw [hp] at h; simp at h
  | some pr1 =>
    rw [hp] at h; simp only [Option.bind_some] at h
    obtain ⟨up, r1⟩ := pr1
    cases hn : notIdCont r1 with
    | none => rw [hn] at h; simp at h
    | some nr =>
      obtain ⟨⟨⟩, r2⟩ := nr
      rw [hn] at h
      simp only [Option.bind_some] at h
      rw [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      obtain ⟨hr21, htk, hdw⟩ := notIdCont_boundary hn
      have hcons : YulParser.skipTrivia cs = (c :: ts) ++ r1 := pstr_consumes _ _ _ hp
      refine ⟨?_, closed_ident hc hts⟩
      rw [hr21, canon_ident_space hc hts, ← canon_skipTrivia cs, hcons,
        canon_ident_boundary hc hts htk hdw, List.singleton_append]

/-- Punctuation-shaped symbol (self-delimiting); needs the bare token to be `Closed`. -/
theorem symbolC {s : List Char} (hcs : Closed s) :
    SoundC (token (pstr s)) (fun _ => s ++ [' ']) := by
  intro cs a rest h
  simp only [token] at h
  have hcons := pstr_consumes s _ _ h
  refine ⟨?_, closed_append hcs (closed_ws (by decide))⟩
  rw [← canon_skipTrivia cs, hcons, hcs rest, hcs [' '], canon_ws (by decide : isWs ' ' = true),
    canon_nil, List.append_nil]

/-! ### Number and string literals -/

/-- A quoted string token, retaining the source spelling of escapes. -/
def pStringChars : Parser (List Char) := token pQuotedChars

theorem pStringChars_soundC : SoundC pStringChars printStringC := by
  intro cs content rest h
  simp only [pStringChars, token] at h
  have hbody := pQuotedChars_body h
  have hp : pQuotedChars (printStringC content) = some (content, [' ']) := by
    show quotedBody (content ++ '"' :: [' ']) = some (content, [' '])
    exact hbody.scan [' ']
  have hprint : canon (printStringC content) = [CTok.str content] := by
    rw [canon_pQuotedChars hp, canon_ws (by decide : isWs ' ' = true), canon_nil]
  have hinput := canon_pQuotedChars h
  refine ⟨?_, closed_str hbody⟩
  rw [hprint, ← canon_skipTrivia cs, hinput, List.singleton_append]

/-- A number literal (decimal or `0x…` hex), producing `Literal.number` of its value. -/
def pNum : Parser Literal :=
  token (pmap (fun d => Literal.number (numVal d)) (pWhile1 isDigitC isNumCont))

theorem pNum_soundC : SoundC pNum printLitC := by
  intro cs a rest h
  simp only [pNum, token, pmap, Option.bind_eq_some_iff] at h
  obtain ⟨⟨d, r'⟩, hpw, heq⟩ := h
  simp only [Option.some.injEq, Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  set cs' := YulParser.skipTrivia cs with hcs'
  cases hc : cs' with
  | nil => rw [hc] at hpw; simp [pWhile1] at hpw
  | cons c r =>
    rw [hc] at hpw
    simp only [pWhile1] at hpw
    split at hpw
    · rename_i hfirst
      simp only [Option.some.injEq, Prod.mk.injEq] at hpw
      obtain ⟨rfl, rfl⟩ := hpw
      set ts := r.takeWhile isNumCont with hts
      have htsAll : ∀ x ∈ ts, isNumCont x = true := fun x hx => List.mem_takeWhile_imp hx
      refine ⟨?_, closed_decDigits _⟩
      have hcanon_cs : canon cs
          = CTok.num (numVal (c :: ts)) :: canon (r.dropWhile isNumCont) := by
        rw [← canon_skipTrivia cs, ← hcs', hc,
          canon_num (digit_not_ws hfirst) (digit_not_quote hfirst) (digit_not_idStart hfirst)
            hfirst]
      show canon (printLitC (Literal.number (numVal (c :: ts)))) ++ _ = _
      rw [printLitC, canon_decDigits, hcanon_cs, List.singleton_append]
    · exact absurd hpw (by simp)

/-- A string literal `"…"`, including backslash-escaped quotes and control
sequences, producing `Literal.string` with the escape spelling retained. -/
def pStr : Parser Literal :=
  pmap (fun content => Literal.string (String.ofList content)) pStringChars

theorem pStr_soundC : SoundC pStr printLitC := by
  apply pmapC_eq pStringChars_soundC
  intro content
  simp [printLitC, printStringC]

/-! ### Booleans and the combined literal parser -/

/-- The `true` / `false` literals (parsed as boundary-checked keywords). -/
def pBool : Parser Literal :=
  YulParser.orElse (pmap (fun _ => Literal.bool true) (keyword ['t', 'r', 'u', 'e']))
    (pmap (fun _ => Literal.bool false) (keyword ['f', 'a', 'l', 's', 'e']))

theorem pBool_soundC : SoundC pBool printLitC :=
  orElseC
    (pmapC_eq (keywordC (by decide) (by intro x hx; fin_cases hx <;> decide)) (fun _ => rfl))
    (pmapC_eq (keywordC (by decide) (by intro x hx; fin_cases hx <;> decide)) (fun _ => rfl))

/-- Any literal: number, boolean, or string. (Type annotations are not accepted — a documented
deferral shared with the `yul-semantics` DSL, which is single-sorted.) -/
def pLit : Parser Literal := YulParser.orElse pNum (YulParser.orElse pBool pStr)

theorem pLit_soundC : SoundC pLit printLitC :=
  orElseC pNum_soundC (orElseC pBool_soundC pStr_soundC)

end YulParser
