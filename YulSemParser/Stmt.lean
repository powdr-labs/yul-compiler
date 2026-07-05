import YulSemParser.Expr

/-!
# YulSemParser.Stmt

Statement parser producing `Stmt EVM.Op` (the full statement set), fuel-bounded through nested
blocks, with `SoundC` by induction on the fuel. `return(…)` is not special — it parses as an
expression statement whose call resolves to the `ret` built-in.
-/

namespace YulSemParser

open YulParser (Parser andThen orElse opt pmap token ppure manyP symbol)
open YulSemantics (Literal Expr Stmt)
open YulSemantics.EVM (Op)

/-! ### Generic comma-separated lists -/

/-- Parse `, x`. -/
def commaElem {α : Type} (p : Parser α) : Parser α := pmap Prod.snd (andThen (symbol [',']) p)

theorem commaElemC {α : Type} {p : Parser α} {pr : α → List Char} (hp : SoundC p pr) :
    SoundC (commaElem p) (fun y => [','] ++ [' '] ++ pr y) := by
  unfold commaElem
  refine pmapC (andThenC (symbolC closed_comma) hp) ?_ ?_
  · intro _; rfl
  · intro _ h; exact h

/-- One-or-more, head and tail separated (nonempty by construction). -/
def commaSep1 {α : Type} (p : Parser α) : Parser (α × List α) := andThen p (manyP (commaElem p))

/-- Zero-or-more. -/
def commaSep {α : Type} (p : Parser α) : Parser (List α) :=
  orElse (pmap (fun ab => ab.1 :: ab.2) (commaSep1 p)) (ppure [])

/-- Printer for `commaSep1`. -/
def printCS1 {α : Type} (pr : α → List Char) (x : α × List α) : List Char :=
  pr x.1 ++ printManyC (fun y => [','] ++ [' '] ++ pr y) x.2

/-- Printer for `commaSep`. -/
def printCS {α : Type} (pr : α → List Char) : List α → List Char
  | [] => []
  | a :: as => pr a ++ printManyC (fun y => [','] ++ [' '] ++ pr y) as

theorem commaSep1_soundC {α : Type} {p : Parser α} {pr : α → List Char} (hp : SoundC p pr) :
    SoundC (commaSep1 p) (printCS1 pr) :=
  andThenC hp (manyC (commaElemC hp))

theorem commaSep_soundC {α : Type} {p : Parser α} {pr : α → List Char} (hp : SoundC p pr) :
    SoundC (commaSep p) (printCS pr) := by
  apply orElseC
  · apply pmapC_eq (commaSep1_soundC hp)
    intro ab; obtain ⟨a, as⟩ := ab; rfl
  · intro cs a rest h
    simp only [ppure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by simp [printCS], by simp only [printCS]; exact closed_nil⟩

/-- Identifier-token printer (matches `pIdent`). -/
def printId (s : String) : List Char := s.toList ++ [' ']

/-! ### Keyword `Closed` facts -/

private theorem ckw (c : Char) (ts : List Char) (hc : YulParser.isIdStart c = true)
    (hts : ∀ x ∈ ts, YulParser.isIdCont x = true) : Closed ((c :: ts) ++ [' ']) := closed_ident hc hts

theorem closed_lbrace : Closed ['{'] :=
  closed_punct (by decide) (by decide) (by decide) (by decide) (by decide)
theorem closed_rbrace : Closed ['}'] :=
  closed_punct (by decide) (by decide) (by decide) (by decide) (by decide)
theorem closed_assignTok : Closed [':', '='] := closed_assign
theorem closed_arrow : Closed ['-', '>'] :=
  closed_append (closed_punct (by decide) (by decide) (by decide) (by decide) (by decide))
    (closed_punct (by decide) (by decide) (by decide) (by decide) (by decide))

/-! ### Printer -/

mutual
/-- Re-print a statement (layout mirrors the parser's `andThen` composition). -/
def printStmtC : Stmt Op → List Char
  | .block body => ['{'] ++ [' '] ++ (printStmtsC body ++ (['}'] ++ [' ']))
  | .funDef name ps rs body =>
      ['f','u','n','c','t','i','o','n'] ++ [' '] ++ printId name ++ ['('] ++ [' '] ++
        printCS printId ps ++ [')'] ++ [' '] ++
        (match rs with
          | [] => []
          | r :: rr => ['-','>'] ++ [' '] ++ printCS1 printId (r, rr)) ++
        ['{'] ++ [' '] ++ printStmtsC body ++ ['}'] ++ [' ']
  | .letDecl vars val =>
      (['l','e','t'] ++ [' ']) ++ (printCS printId vars ++
        (match val with | some e => (([':','='] ++ [' ']) ++ printExprC e) | none => []))
  | .assign vars val =>
      printCS printId vars ++ (([':','='] ++ [' ']) ++ printExprC val)
  | .cond c body =>
      (['i','f'] ++ [' ']) ++ (printExprC c ++ (['{'] ++ [' '] ++ (printStmtsC body ++ (['}'] ++ [' ']))))
  | .switch c cases dflt =>
      (['s','w','i','t','c','h'] ++ [' ']) ++ (printExprC c ++ (printCasesC cases ++
        (match dflt with
          | some d => (['d','e','f','a','u','l','t'] ++ [' ']) ++
              (['{'] ++ [' '] ++ (printStmtsC d ++ (['}'] ++ [' '])))
          | none => [])))
  | .forLoop init c post body =>
      (['f','o','r'] ++ [' ']) ++ ((['{'] ++ [' '] ++ (printStmtsC init ++ (['}'] ++ [' ']))) ++
        (printExprC c ++ ((['{'] ++ [' '] ++ (printStmtsC post ++ (['}'] ++ [' ']))) ++
          (['{'] ++ [' '] ++ (printStmtsC body ++ (['}'] ++ [' ']))))))
  | .exprStmt e => printExprC e
  | .«break» => ['b','r','e','a','k'] ++ [' ']
  | .«continue» => ['c','o','n','t','i','n','u','e'] ++ [' ']
  | .leave => ['l','e','a','v','e'] ++ [' ']
/-- A statement sequence. -/
def printStmtsC : List (Stmt Op) → List Char
  | [] => []
  | s :: ss => printStmtC s ++ printStmtsC ss
/-- Switch cases. -/
def printCasesC : List (Literal × List (Stmt Op)) → List Char
  | [] => []
  | (l, body) :: cs =>
      ((['c','a','s','e'] ++ [' ']) ++ (printLitC l ++
        (['{'] ++ [' '] ++ (printStmtsC body ++ (['}'] ++ [' ']))))) ++ printCasesC cs
end

theorem printStmtsC_eq (ss : List (Stmt Op)) : printStmtsC ss = printManyC printStmtC ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih => simp only [printStmtsC, printManyC, ih]

/-- Single-case printer, so `printCasesC = printManyC printCaseC`. -/
def printCaseC (c : Literal × List (Stmt Op)) : List Char :=
  (['c','a','s','e'] ++ [' ']) ++ (printLitC c.1 ++
    (['{'] ++ [' '] ++ (printStmtsC c.2 ++ (['}'] ++ [' ']))))

theorem printCasesC_eq (cs : List (Literal × List (Stmt Op))) :
    printCasesC cs = printManyC printCaseC cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => obtain ⟨l, b⟩ := c; simp only [printCasesC, printManyC, printCaseC, ih]

end YulSemParser
