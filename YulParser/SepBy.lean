import YulParser.Lexer

/-!
# YulParser.SepBy

Comma-separated lists (`sepBy0` / `sepBy1`) and their printer `printSepList`,
with soundness. Commas are *significant* (kept by `fws`); the surrounding
whitespace is not.
-/

namespace YulParser

/-- Parse `, elem`. -/
def commaElem {α : Type} (p : Parser α) : Parser α :=
  pmap Prod.snd (andThen (symbol [',']) p)

theorem commaElem_sound {α : Type} {p : Parser α} {pr : α → List Char} (hp : Sound p pr) :
    Sound (commaElem p) (fun a => ',' :: sep ++ pr a) := by
  apply pmap_sound (andThen_sound (symbol_sound [',']) hp)
  intro a; simp [sep, fws_cons_simp, isWs, fws_append]

/-- Zero-or-more `elem` separated by commas, with an optional leading element. -/
def sepBy1 {α : Type} (p : Parser α) : Parser (List α) :=
  pmap (fun ah => ah.1 :: ah.2) (andThen p (manyP (commaElem p)))

/-- One-or-more (nonempty) list. -/
def sepBy0 {α : Type} (p : Parser α) : Parser (List α) :=
  pmap (fun o => o.getD []) (opt (sepBy1 p))

/-- Print a comma-separated list: first element bare, the rest as `, x`. -/
def printSepList {α : Type} (pr : α → List Char) : List α → List Char
  | [] => []
  | a :: as => pr a ++ printMany (fun x => ',' :: sep ++ pr x) as

theorem sepBy1_sound {α : Type} {p : Parser α} {pr : α → List Char} (hp : Sound p pr) :
    Sound (sepBy1 p) (printSepList pr) := by
  apply pmap_sound (andThen_sound hp (manyP_sound (commaElem_sound hp)))
  intro a
  obtain ⟨x, xs⟩ := a
  simp only [printSepList, fws_append, fws_sep, List.append_nil]

/-- One-or-more, returning the head and tail *separately* so the result is
nonempty by construction (used where an empty list must be distinguishable from
absence, e.g. function return lists after `->`). -/
def sepBy1P {α : Type} (p : Parser α) : Parser (α × List α) :=
  andThen p (manyP (commaElem p))

/-- Printer for `sepBy1P` (head then comma-tail). -/
def printSepList1 {α : Type} (pr : α → List Char) (x : α × List α) : List Char :=
  pr x.1 ++ sep ++ printMany (fun z => ',' :: sep ++ pr z) x.2

theorem sepBy1P_sound {α : Type} {p : Parser α} {pr : α → List Char} (hp : Sound p pr) :
    Sound (sepBy1P p) (printSepList1 pr) :=
  andThen_sound hp (manyP_sound (commaElem_sound hp))

theorem sepBy0_sound {α : Type} {p : Parser α} {pr : α → List Char} (hp : Sound p pr) :
    Sound (sepBy0 p) (printSepList pr) := by
  apply pmap_sound (opt_sound (sepBy1_sound hp))
  intro o
  cases o with
  | none => simp [printSepList]
  | some as => simp

end YulParser
