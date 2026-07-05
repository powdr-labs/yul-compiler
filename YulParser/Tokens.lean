import YulParser.Combinators

/-!
# YulParser.Tokens

Literal strings (`pstr`), whitespace skipping (`skipWs`, `token`), and
repetition (`many`, with its printer `printMany`), each with soundness lemmas.
-/

namespace YulParser

/-! ### Literal strings -/

/-- Consume the exact character list `s`. -/
def pstr : List Char → Parser Unit
  | [] => ppure ()
  | c :: cs => fun input =>
    match pchar c input with
    | some (_, r) => pstr cs r
    | none => none

theorem pstr_sound (s : List Char) : Sound (pstr s) (fun _ => s) := by
  induction s with
  | nil => intro cs a rest h; simp only [pstr] at h; exact ppure_sound () cs a rest h
  | cons c cs ih =>
    intro input a rest h
    simp only [pstr] at h
    cases hc : pchar c input with
    | none => rw [hc] at h; simp at h
    | some ar =>
      obtain ⟨x, r⟩ := ar
      rw [hc] at h
      have e1 := pchar_sound c input x r hc
      have e2 := ih r a rest h
      -- fws (c :: cs) = fws [c] ++ fws cs
      have : fws (c :: cs) = fws [c] ++ fws cs := by
        rw [show c :: cs = [c] ++ cs from rfl, fws_append]
      rw [this, List.append_assoc, e2, e1]

/-! ### Whitespace -/

theorem fws_dropWhile_isWs (cs : List Char) : fws (cs.dropWhile isWs) = fws cs := by
  induction cs with
  | nil => rfl
  | cons c cs' ih =>
    simp only [List.dropWhile]
    split
    · rename_i hw; rw [ih]; exact (fws_cons_ws hw cs').symm
    · rfl

/-- Skip leading whitespace. -/
def skipWs : Parser Unit := fun cs => some ((), cs.dropWhile isWs)

theorem skipWs_sound : Sound skipWs (fun _ => []) := by
  intro cs a rest h
  simp only [skipWs, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨_, rfl⟩ := h
  rw [fws_dropWhile_isWs]; simp

/-- Run `p` after skipping leading whitespace. A *token* thus absorbs the
whitespace that precedes it. -/
def token {α : Type} (p : Parser α) : Parser α := fun cs => p (cs.dropWhile isWs)

theorem token_sound {α : Type} {p : Parser α} {pr : α → List Char} (hp : Sound p pr) :
    Sound (token p) pr := by
  intro cs a rest h
  simp only [token] at h
  rw [hp _ a rest h, fws_dropWhile_isWs]

/-- A keyword / symbol token: skip leading whitespace, then match `s`. -/
def kw (s : List Char) : Parser Unit := token (pstr s)

theorem kw_sound (s : List Char) : Sound (kw s) (fun _ => s) := token_sound (pstr_sound s)

/-! ### Repetition -/

/-- Zero-or-more, greedy; always succeeds. Stops when `p` fails or fails to make
progress (so it is total). -/
def many {α : Type} (p : Parser α) : List Char → List α × List Char := fun cs =>
  match p cs with
  | none => ([], cs)
  | some (a, rest) =>
    if h : rest.length < cs.length then
      ((a :: (many p rest).1), (many p rest).2)
    else ([a], rest)
termination_by cs => cs.length
decreasing_by all_goals exact h

/-- `many` as a (always-succeeding) parser. -/
def manyP {α : Type} (p : Parser α) : Parser (List α) := fun cs => some (many p cs)

/-- Printer for a list: each element printed, separated by whitespace. -/
def printMany {α : Type} (pr : α → List Char) : List α → List Char
  | [] => []
  | a :: as => pr a ++ sep ++ printMany pr as

theorem fws_printMany_cons {α : Type} (pr : α → List Char) (a : α) (as : List α) :
    fws (printMany pr (a :: as)) = fws (pr a) ++ fws (printMany pr as) := by
  simp only [printMany]; rw [fws_glue]

/-- The core soundness fact for `many`, phrased on the raw `many` result. -/
theorem many_fws {α : Type} {p : Parser α} {pr : α → List Char} (hp : Sound p pr)
    (cs : List Char) :
    fws (printMany pr (many p cs).1) ++ fws (many p cs).2 = fws cs := by
  fun_induction many p cs with
  | case1 cs hpc => simp [hpc, printMany]
  | case2 cs a rest hpc hlt ih =>
    simp only [hpc, dif_pos hlt]
    rw [fws_printMany_cons, List.append_assoc, ih]
    exact hp cs a rest hpc
  | case3 cs a rest hpc hlt =>
    simp only [hpc, dif_neg hlt, printMany]
    rw [fws_glue]
    simpa using hp cs a rest hpc

theorem manyP_sound {α : Type} {p : Parser α} {pr : α → List Char} (hp : Sound p pr) :
    Sound (manyP p) (printMany pr) := by
  intro cs a rest h
  simp only [manyP, Option.some.injEq] at h
  have hm := many_fws hp cs
  rw [h] at hm; exact hm

end YulParser
