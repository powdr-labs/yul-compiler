import YulParser.Combinators
set_option warningAsError true
/-!
# YulParser.Tokens

Literal-string matching (`pstr`), trivia skipping (`skipTrivia`: whitespace and C++-style `//`
line and `/* … */` block comments), whitespace-absorbing tokens (`token`), and repetition
(`many`/`manyP`).
-/

namespace YulParser

/-- Consume the exact character list `s`. -/
def pstr : List Char → Parser Unit
  | [] => ppure ()
  | c :: cs => fun input =>
    match pchar c input with
    | some (_, r) => pstr cs r
    | none => none

/-- Skip leading whitespace. -/
def skipWs : Parser Unit := fun cs => some ((), cs.dropWhile isWs)

/-- `dropWhile` never lengthens a list. -/
theorem dropWhile_le {α} (l : List α) (p : α → Bool) : (l.dropWhile p).length ≤ l.length := by
  have h : (l.takeWhile p ++ l.dropWhile p).length = l.length := by
    rw [List.takeWhile_append_dropWhile]
  rw [List.length_append] at h; omega

/-- The suffix following the first `*/` (all of the list if there is none). -/
def afterBlockComment : List Char → List Char
  | [] => []
  | '*' :: '/' :: r => r
  | _ :: r => afterBlockComment r

theorem afterBlockComment_le (l : List Char) : (afterBlockComment l).length ≤ l.length := by
  fun_induction afterBlockComment l <;> simp_all <;> omega

/-- Drop leading whitespace and comments (`//…` to end of line, `/* … */`), repeatedly. -/
def skipTrivia (cs : List Char) : List Char :=
  match cs with
  | [] => []
  | c :: rest =>
    if isWs c then skipTrivia rest
    else if c == '/' then
      match rest with
      | '/' :: r => skipTrivia (r.dropWhile (· != '\n'))
      | '*' :: r => skipTrivia (afterBlockComment r)
      | _ => c :: rest
    else c :: rest
  termination_by cs.length
  decreasing_by
    all_goals simp_wf
    all_goals
      first
        | omega
        | (refine Nat.lt_of_le_of_lt (dropWhile_le _ _) ?_; omega)
        | (refine Nat.lt_of_le_of_lt (afterBlockComment_le _) ?_; omega)

/-- Run `p` after skipping leading trivia (whitespace and comments). -/
def token {α : Type} (p : Parser α) : Parser α := fun cs => p (skipTrivia cs)

/-- Fuelled implementation of greedy repetition. `many` shares its input list
as the structural fuel, avoiding a length scan when repetition starts or
advances. -/
def manyFuel {α : Type} (p : Parser α) : List Char → List Char → List α × List Char
  | [], cs => ([], cs)
  | _ :: fuel, cs =>
      match p cs with
      | none => ([], cs)
      | some (a, rest) =>
          if rest == cs then ([a], rest)
          else
            let parsed := manyFuel p fuel rest
            (a :: parsed.1, parsed.2)

/-- Zero-or-more, greedy; always succeeds. Stops when `p` fails or fails to make progress. -/
def many {α : Type} (p : Parser α) (cs : List Char) : List α × List Char :=
  manyFuel p cs cs

/-- `many` as a (always-succeeding) parser. -/
def manyP {α : Type} (p : Parser α) : Parser (List α) := fun cs => some (many p cs)

end YulParser
