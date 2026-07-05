/-!
# YulParser.Core

A tiny verified parser-combinator framework, specialised to the round-trip
property this development proves: *if the parser accepts, then re-printing the
result agrees with the input up to whitespace.*

## Whitespace equivalence

`fws` (“filter whitespace”) drops all whitespace characters. Two character
lists are whitespace-equivalent (`≈`) when they have the same non-whitespace
content: `fws s = fws t`. This is exactly “differ only in whitespace”.

## Soundness invariant

A parser `p : Parser α` is *sound for printer* `pr : α → List Char` when every
successful parse re-prints to the consumed input, modulo whitespace:

    p cs = some (a, rest) → fws (pr a) ++ fws rest = fws cs

This form has no existential and composes cleanly: sequencing two sound parsers
separated by whitespace stays sound, because `fws` distributes over `++` and
kills the separator. -/

namespace YulParser

/-- Whitespace characters (space, tab, newline, carriage return). -/
def isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- Drop whitespace characters, keeping the significant content in order. -/
def fws (cs : List Char) : List Char := cs.filter (fun c => !isWs c)

@[simp] theorem fws_nil : fws [] = [] := rfl

@[simp] theorem fws_append (a b : List Char) : fws (a ++ b) = fws a ++ fws b :=
  List.filter_append a b

theorem fws_cons_ws {c : Char} (h : isWs c = true) (cs : List Char) :
    fws (c :: cs) = fws cs := by
  simp only [fws, List.filter_cons]; rw [h]; rfl

theorem fws_cons_nonws {c : Char} (h : isWs c = false) (cs : List Char) :
    fws (c :: cs) = c :: fws cs := by
  simp only [fws, List.filter_cons]; rw [h]; rfl

/-- Whitespace-equivalence: same non-whitespace content. -/
def Approx (s t : List Char) : Prop := fws s = fws t

/-- A parser consumes a prefix of the input, returning a value and the
remaining (unconsumed) suffix. -/
abbrev Parser (α : Type) := List Char → Option (α × List Char)

/-- **Soundness.** Every successful parse re-prints (via `pr`) to the consumed
prefix, modulo whitespace. -/
def Sound {α : Type} (p : Parser α) (pr : α → List Char) : Prop :=
  ∀ cs a rest, p cs = some (a, rest) → fws (pr a) ++ fws rest = fws cs

/-! ### Primitive parsers -/

/-- The parser that consumes nothing and returns `a`. -/
def ppure {α : Type} (a : α) : Parser α := fun cs => some (a, cs)

theorem ppure_sound {α : Type} (a : α) : Sound (ppure a) (fun _ => []) := by
  intro cs a' rest h
  simp only [ppure, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨_, rfl⟩ := h
  simp

/-- Consume one character satisfying `pred`. -/
def satisfy (pred : Char → Bool) : Parser Char := fun cs =>
  match cs with
  | [] => none
  | c :: rest => if pred c then some (c, rest) else none

theorem satisfy_sound (pred : Char → Bool) : Sound (satisfy pred) (fun c => [c]) := by
  intro cs a rest h
  cases cs with
  | nil => simp [satisfy] at h
  | cons c cs' =>
    simp only [satisfy] at h
    by_cases hp : pred c
    · rw [if_pos hp] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      by_cases hw : isWs c
      · rw [fws_cons_ws hw, fws_cons_ws hw]; simp
      · simp only [Bool.not_eq_true] at hw
        rw [fws_cons_nonws hw, fws_cons_nonws hw]; simp
    · rw [if_neg hp] at h; exact absurd h (by simp)

/-- Consume a specific character `c`. -/
def pchar (c : Char) : Parser Char := satisfy (· == c)

theorem pchar_sound (c : Char) : Sound (pchar c) (fun _ => [c]) := by
  intro cs a rest h
  have ha : a = c := by
    cases cs with
    | nil => simp [pchar, satisfy] at h
    | cons d cs' =>
      simp only [pchar, satisfy] at h
      by_cases hp : (d == c) = true
      · rw [if_pos hp] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1]; exact beq_iff_eq.mp hp
      · rw [if_neg hp] at h; exact absurd h (by simp)
  have hs := satisfy_sound (· == c) cs a rest h
  rw [ha] at hs; exact hs

end YulParser
