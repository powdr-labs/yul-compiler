import YulParser.Expr

/-!
# YulParser.Stmt

Statement parser producing `Stmt EVM.Op` (the full statement set), fuel-bounded through nested
blocks, with `SoundC` by induction on the fuel. `return(…)` is not special — it parses as an
expression statement whose call resolves to the `ret` built-in.
-/

namespace YulParser

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
  closed_punct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem closed_rbrace : Closed ['}'] :=
  closed_punct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem closed_assignTok : Closed [':', '='] := closed_assign
theorem closed_arrow : Closed ['-', '>'] :=
  closed_append (closed_punct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (closed_punct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))

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

/-! ### Parser -/

open YulParser (keyword)

/-- A `{ … }` block body parser (shared by `for`). -/
def pBlockBody (inner : Parser (List (Stmt Op))) : Parser (List (Stmt Op)) :=
  pmap (fun p => p.2.1) (andThen (symbol ['{']) (andThen inner (symbol ['}'])))

mutual
/-- Statement parser, fuel-bounded; nested blocks recurse at one lower fuel. -/
def pStmtF : Nat → Parser (Stmt Op)
  | 0 => fun _ => none
  | n + 1 =>
    orElse
      (pmap (fun p => Stmt.block p.2.1)
        (andThen (symbol ['{']) (andThen (pStmtsF n) (symbol ['}'])))) <|
    orElse
      (pmap (fun p => Stmt.funDef p.2.1 p.2.2.2.1
          (match p.2.2.2.2.2.1 with | some ht => ht.1 :: ht.2 | none => []) p.2.2.2.2.2.2.2.1)
        (andThen (keyword ['f','u','n','c','t','i','o','n'])
          (andThen pIdent (andThen (symbol ['('])
            (andThen (commaSep pIdent) (andThen (symbol [')'])
              (andThen (opt (pmap Prod.snd (andThen (symbol ['-','>']) (commaSep1 pIdent))))
                (andThen (symbol ['{']) (andThen (pStmtsF n) (symbol ['}']))))))))))  <|
    orElse
      (pmap (fun p => Stmt.letDecl p.2.1 (p.2.2.map Prod.snd))
        (andThen (keyword ['l','e','t'])
          (andThen (commaSep pIdent) (opt (andThen (symbol [':','=']) (pExprF n)))))) <|
    orElse
      (pmap (fun p => Stmt.cond p.2.1 p.2.2.2.1)
        (andThen (keyword ['i','f'])
          (andThen (pExprF n) (andThen (symbol ['{']) (andThen (pStmtsF n) (symbol ['}'])))))) <|
    orElse
      (pmap (fun p => Stmt.switch p.2.1 p.2.2.1 (p.2.2.2.map (fun q => q.2.2.1)))
        (andThen (keyword ['s','w','i','t','c','h'])
          (andThen (pExprF n) (andThen (pCasesF n)
            (opt (andThen (keyword ['d','e','f','a','u','l','t'])
              (andThen (symbol ['{']) (andThen (pStmtsF n) (symbol ['}']))))))))) <|
    orElse
      (pmap (fun p => Stmt.forLoop p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
        (andThen (keyword ['f','o','r'])
          (andThen (pBlockBody (pStmtsF n))
            (andThen (pExprF n)
              (andThen (pBlockBody (pStmtsF n)) (pBlockBody (pStmtsF n))))))) <|
    orElse (pmap (fun _ => Stmt.«break») (keyword ['b','r','e','a','k'])) <|
    orElse (pmap (fun _ => Stmt.«continue») (keyword ['c','o','n','t','i','n','u','e'])) <|
    orElse (pmap (fun _ => Stmt.leave) (keyword ['l','e','a','v','e'])) <|
    orElse
      (pmap (fun p => Stmt.assign p.1 p.2.2)
        (andThen (commaSep pIdent) (andThen (symbol [':','=']) (pExprF n))))
      (pmap Stmt.exprStmt (pExprF n))
/-- A statement list. -/
def pStmtsF : Nat → Parser (List (Stmt Op)) := fun n => manyP (pStmtF n)
/-- A `case Lit { body }`. -/
def pCaseF : Nat → Parser (Literal × List (Stmt Op)) := fun n =>
  pmap (fun p => (p.2.1, p.2.2.2.1))
    (andThen (keyword ['c','a','s','e'])
      (andThen pLit (andThen (symbol ['{']) (andThen (pStmtsF n) (symbol ['}'])))))
/-- A list of `case`s. -/
def pCasesF : Nat → Parser (List (Literal × List (Stmt Op))) := fun n => manyP (pCaseF n)
end

/-! ### Soundness -/

/-- Rets sub-parser (`-> r, …`), nonempty by construction. -/
theorem hrets_soundC :
    SoundC (pmap Prod.snd (andThen (symbol ['-','>']) (commaSep1 pIdent)))
      (fun ht => ['-','>'] ++ [' '] ++ printCS1 printId ht) := by
  refine pmapC (andThenC (symbolC closed_arrow) (commaSep1_soundC pIdent_soundC)) ?_ ?_
  · intro _; rfl
  · intro _ h; exact h

/-- The `{ body }` block-body parser is sound for its brace-wrapped printer. -/
theorem pBlockBody_soundC {inner : Parser (List (Stmt Op))} {pr : List (Stmt Op) → List Char}
    (hin : SoundC inner pr) :
    SoundC (pBlockBody inner) (fun body => ['{'] ++ [' '] ++ (pr body ++ (['}'] ++ [' ']))) := by
  unfold pBlockBody
  refine pmapC (andThenC (symbolC closed_lbrace) (andThenC hin (symbolC closed_rbrace))) ?_ ?_
  · intro a; rfl
  · intro a h; exact h

theorem pStmtF_soundC : ∀ n, SoundC (pStmtF n) printStmtC := by
  intro n
  induction n with
  | zero => intro cs a rest h; simp [pStmtF] at h
  | succ n ih =>
    have hstmts : SoundC (pStmtsF n) printStmtsC := by
      simp only [pStmtsF, funext printStmtsC_eq]; exact manyC ih
    have hcase : SoundC (pCaseF n) printCaseC := by
      simp only [pCaseF]
      refine pmapC (andThenC (keywordC (by decide) (by intro x hx; fin_cases hx <;> decide))
        (andThenC pLit_soundC (andThenC (symbolC closed_lbrace)
          (andThenC hstmts (symbolC closed_rbrace))))) ?_ ?_
      · intro a; obtain ⟨_, l, _, body, _⟩ := a; simp only [printCaseC, List.append_assoc]
      · intro a hc; obtain ⟨_, l, _, body, _⟩ := a
        revert hc; simp only [printCaseC, List.append_assoc]; exact id
    have hcases : SoundC (pCasesF n) printCasesC := by
      simp only [pCasesF, funext printCasesC_eq]; exact manyC hcase
    have hids : SoundC (commaSep pIdent) (printCS printId) := commaSep_soundC pIdent_soundC
    have hexp : SoundC (pExprF n) printExprC := pExprF_soundC n
    have hblk : SoundC (pBlockBody (pStmtsF n))
        (fun body => ['{'] ++ [' '] ++ (printStmtsC body ++ (['}'] ++ [' ']))) :=
      pBlockBody_soundC hstmts
    simp only [pStmtF]
    refine orElseC ?block <| orElseC ?fundef <| orElseC ?letd <| orElseC ?ifs <| orElseC ?switch <|
      orElseC ?forl <| orElseC ?brk <| orElseC ?cont <| orElseC ?lv <| orElseC ?asgn ?estmt
    case block =>
      refine pmapC_eq (andThenC (symbolC closed_lbrace) (andThenC hstmts (symbolC closed_rbrace))) ?_
      intro a; obtain ⟨_, body, _⟩ := a; rfl
    case fundef =>
      refine pmapC_eq (andThenC (keywordC (by decide) (by intro x hx; fin_cases hx <;> decide))
        (andThenC pIdent_soundC (andThenC (symbolC closed_lparen) (andThenC hids
          (andThenC (symbolC closed_rparen) (andThenC (optC hrets_soundC)
            (andThenC (symbolC closed_lbrace) (andThenC hstmts (symbolC closed_rbrace))))))))) ?_
      intro a; obtain ⟨_, name, _, ps, _, orets, _, body, _⟩ := a
      cases orets with
      | none => simp [printStmtC, printId]
      | some ht => obtain ⟨h, t⟩ := ht; simp [printStmtC, printId, printCS1, List.append_assoc]
    case letd =>
      refine pmapC_eq (andThenC (keywordC (by decide) (by intro x hx; fin_cases hx <;> decide))
        (andThenC hids (optC (andThenC (symbolC closed_assignTok) hexp)))) ?_
      intro a; obtain ⟨_, vars, oval⟩ := a
      cases oval with
      | none => simp [printStmtC]
      | some ve => obtain ⟨_, e⟩ := ve; simp [printStmtC, List.append_assoc]
    case ifs =>
      refine pmapC_eq (andThenC (keywordC (by decide) (by intro x hx; fin_cases hx <;> decide))
        (andThenC hexp (andThenC (symbolC closed_lbrace)
          (andThenC hstmts (symbolC closed_rbrace))))) ?_
      intro a; obtain ⟨_, c, _, body, _⟩ := a; rfl
    case switch =>
      refine pmapC_eq (andThenC (keywordC (by decide) (by intro x hx; fin_cases hx <;> decide))
        (andThenC hexp (andThenC hcases (optC (andThenC
          (keywordC (by decide) (by intro x hx; fin_cases hx <;> decide))
          (andThenC (symbolC closed_lbrace) (andThenC hstmts (symbolC closed_rbrace)))))))) ?_
      intro a; obtain ⟨_, c, cases, odflt⟩ := a
      cases odflt with
      | none => simp [printStmtC]
      | some d => obtain ⟨_, _, body, _⟩ := d; simp [printStmtC, List.append_assoc]
    case forl =>
      refine pmapC_eq (andThenC (keywordC (by decide) (by intro x hx; fin_cases hx <;> decide))
        (andThenC hblk (andThenC hexp (andThenC hblk hblk)))) ?_
      intro a; obtain ⟨_, init, c, post, body⟩ := a; rfl
    case brk => exact pmapC_eq (keywordC (by decide) (by intro x hx; fin_cases hx <;> decide))
                  (fun _ => rfl)
    case cont => exact pmapC_eq (keywordC (by decide) (by intro x hx; fin_cases hx <;> decide))
                   (fun _ => rfl)
    case lv => exact pmapC_eq (keywordC (by decide) (by intro x hx; fin_cases hx <;> decide))
                 (fun _ => rfl)
    case asgn =>
      refine pmapC_eq (andThenC hids (andThenC (symbolC closed_assignTok) hexp)) ?_
      intro a; obtain ⟨vars, _, e⟩ := a; rfl
    case estmt => exact pmapC_eq hexp (fun _ => rfl)

theorem pStmtsF_soundC (n : Nat) : SoundC (pStmtsF n) printStmtsC := by
  simp only [pStmtsF, funext printStmtsC_eq]; exact manyC (pStmtF_soundC n)

end YulParser
