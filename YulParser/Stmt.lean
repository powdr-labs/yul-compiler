import YulParser.Expr

/-!
# YulParser.Stmt

Statement grammar: the full statement set (blocks, function definitions,
`let`/assignment, `if`, `switch`, `for`, `break`/`continue`/`leave`, and
expression statements), recursive through nested blocks via a fuel bound.
Soundness is by induction on the fuel, reusing the expression soundness.
-/

namespace YulParser

/-- Comma-separated identifier list printer. -/
def printIds : List Id → List Char := printSepList (fun s => s)

/-! ### Printers -/

mutual
/-- Re-print a statement. -/
def printStmt : Stmt → List Char
  | .block body => '{' :: (printStmts body ++ ['}'])
  | .funDef name ps rs body =>
      ['f','u','n','c','t','i','o','n'] ++ sep ++ name ++ '(' :: printIds ps ++ ')' :: sep ++
        (match rs with
          | [] => []
          | _ => '-' :: '>' :: sep ++ printIds rs ++ sep) ++
        '{' :: (printStmts body ++ ['}'])
  | .letDecl vars val =>
      ['l','e','t'] ++ sep ++ printIds vars ++
        (match val with | some e => sep ++ ':' :: '=' :: sep ++ printExpr e | none => [])
  | .assign vars val => printIds vars ++ sep ++ ':' :: '=' :: sep ++ printExpr val
  | .ifStmt c body =>
      ['i','f'] ++ sep ++ printExpr c ++ sep ++ '{' :: (printStmts body ++ ['}'])
  | .switchStmt c cases dflt =>
      ['s','w','i','t','c','h'] ++ sep ++ printExpr c ++ sep ++ printCases cases ++
        (match dflt with
          | some d => ['d','e','f','a','u','l','t'] ++ sep ++ '{' :: (printStmts d ++ ['}'])
          | none => [])
  | .forLoop init c post body =>
      ['f','o','r'] ++ sep ++ '{' :: (printStmts init ++ '}' :: sep) ++ printExpr c ++ sep ++
        '{' :: (printStmts post ++ '}' :: sep) ++ '{' :: (printStmts body ++ ['}'])
  | .exprStmt e => printExpr e
  | .breakStmt => ['b','r','e','a','k']
  | .continueStmt => ['c','o','n','t','i','n','u','e']
  | .leaveStmt => ['l','e','a','v','e']
/-- Re-print a statement list (matches `printMany printStmt`). -/
def printStmts : List Stmt → List Char
  | [] => []
  | s :: ss => printStmt s ++ sep ++ printStmts ss
/-- Re-print a switch's cases (matches `printMany` of the case printer). -/
def printCases : List (Lit × List Stmt) → List Char
  | [] => []
  | (l, body) :: cs =>
      (['c','a','s','e'] ++ sep ++ printLit l ++ sep ++ '{' :: (printStmts body ++ ['}']))
        ++ sep ++ printCases cs
end

theorem printStmts_eq (ss : List Stmt) : printStmts ss = printMany printStmt ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih => simp only [printStmts, printMany, ih]

/-- Single-case printer, so `printCases = printMany printCase`. -/
def printCase (c : Lit × List Stmt) : List Char :=
  ['c','a','s','e'] ++ sep ++ printLit c.1 ++ sep ++ '{' :: (printStmts c.2 ++ ['}'])

theorem printCases_eq (cs : List (Lit × List Stmt)) : printCases cs = printMany printCase cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => obtain ⟨l, body⟩ := c; simp only [printCases, printMany, printCase, ih]

/-! ### Parsers -/

mutual
/-- Statement parser, fuel-bounded; nested blocks recurse at one lower fuel. -/
def pStmtF : Nat → Parser Stmt
  | 0 => fun _ => none
  | n + 1 =>
    orElse
      (pmap (fun p => Stmt.block p.2.1)
        (andThen (symbol ['{']) (andThen (pStmtsF n) (symbol ['}'])))) <|
    orElse
      (pmap (fun p => Stmt.funDef p.2.1 p.2.2.2.1
          (match p.2.2.2.2.2.1 with | some ht => ht.1 :: ht.2 | none => []) p.2.2.2.2.2.2.2.1)
        (andThen (keyword ['f','u','n','c','t','i','o','n'])
          (andThen pident (andThen (symbol ['('])
            (andThen (sepBy0 pident) (andThen (symbol [')'])
              (andThen (opt (pmap Prod.snd (andThen (symbol ['-','>']) (sepBy1P pident))))
                (andThen (symbol ['{']) (andThen (pStmtsF n) (symbol ['}'])))))))))) <|
    orElse
      (pmap (fun p => Stmt.letDecl p.2.1 (p.2.2.map Prod.snd))
        (andThen (keyword ['l','e','t'])
          (andThen (sepBy0 pident) (opt (andThen (symbol [':','=']) (pExprF n)))))) <|
    orElse
      (pmap (fun p => Stmt.ifStmt p.2.1 p.2.2.2.1)
        (andThen (keyword ['i','f'])
          (andThen (pExprF n) (andThen (symbol ['{']) (andThen (pStmtsF n) (symbol ['}'])))))) <|
    orElse
      (pmap (fun p => Stmt.switchStmt p.2.1 p.2.2.1 (p.2.2.2.map (fun q => q.2.2.1)))
        (andThen (keyword ['s','w','i','t','c','h'])
          (andThen (pExprF n) (andThen (pCasesF n)
            (opt (andThen (keyword ['d','e','f','a','u','l','t'])
              (andThen (symbol ['{']) (andThen (pStmtsF n) (symbol ['}']))))))))) <|
    orElse
      (pmap (fun p => Stmt.forLoop p.2.1.2.1 p.2.2.1 p.2.2.2.1.2.1 p.2.2.2.2.2.1)
        (andThen (keyword ['f','o','r'])
          (andThen (andThen (symbol ['{']) (andThen (pStmtsF n) (symbol ['}'])))
            (andThen (pExprF n)
              (andThen (andThen (symbol ['{']) (andThen (pStmtsF n) (symbol ['}'])))
                (andThen (symbol ['{']) (andThen (pStmtsF n) (symbol ['}'])))))))) <|
    orElse (pmap (fun _ => Stmt.breakStmt) (keyword ['b','r','e','a','k'])) <|
    orElse (pmap (fun _ => Stmt.continueStmt) (keyword ['c','o','n','t','i','n','u','e'])) <|
    orElse (pmap (fun _ => Stmt.leaveStmt) (keyword ['l','e','a','v','e'])) <|
    orElse
      (pmap (fun p => Stmt.assign p.1 p.2.2)
        (andThen (sepBy0 pident) (andThen (symbol [':','=']) (pExprF n))))
      (pmap Stmt.exprStmt (pExprF n))
/-- A statement list. -/
def pStmtsF : Nat → Parser (List Stmt) := fun n => manyP (pStmtF n)
/-- A `case Lit { body }`. -/
def pCaseF : Nat → Parser (Lit × List Stmt) := fun n =>
  pmap (fun p => (p.2.1, p.2.2.2.1))
    (andThen (keyword ['c','a','s','e'])
      (andThen pLit (andThen (symbol ['{']) (andThen (pStmtsF n) (symbol ['}'])))))
/-- A list of `case`s. -/
def pCasesF : Nat → Parser (List (Lit × List Stmt)) := fun n => manyP (pCaseF n)
end

/-! ### Soundness -/

theorem pStmtF_sound : ∀ n, Sound (pStmtF n) printStmt := by
  intro n
  induction n with
  | zero => intro cs a rest h; simp [pStmtF] at h
  | succ n ih =>
    have hstmts : Sound (pStmtsF n) printStmts := by
      simp only [pStmtsF, funext printStmts_eq]; exact manyP_sound ih
    have hcase : Sound (pCaseF n) printCase := by
      simp only [pCaseF]
      apply pmap_sound (andThen_sound (keyword_sound _) (andThen_sound pLit_sound
        (andThen_sound (symbol_sound _) (andThen_sound hstmts (symbol_sound _)))))
      intro a; obtain ⟨_, l, _, body, _⟩ := a
      simp [printCase, sep, fws_cons_simp, fws_append, isWs]
    have hcases : Sound (pCasesF n) printCases := by
      simp only [pCasesF, funext printCases_eq]; exact manyP_sound hcase
    have hids : Sound (sepBy0 pident) printIds := sepBy0_sound pident_sound
    have hexp : Sound (pExprF n) printExpr := pExprF_sound n
    simp only [pStmtF]
    refine orElse_sound ?block (orElse_sound ?fundef (orElse_sound ?letd (orElse_sound ?ifs
      (orElse_sound ?switch (orElse_sound ?forl (orElse_sound ?brk (orElse_sound ?cont
        (orElse_sound ?lv (orElse_sound ?asgn ?estmt)))))))))
    case block =>
      apply pmap_sound (andThen_sound (symbol_sound _) (andThen_sound hstmts (symbol_sound _)))
      intro a; obtain ⟨_, body, _⟩ := a
      simp [printStmt, sep, fws_cons_simp, fws_append, isWs]
    case fundef =>
      have hrets : Sound (pmap Prod.snd (andThen (symbol ['-','>']) (sepBy1P pident)))
          (fun ht => '-' :: '>' :: sep ++ printSepList1 (fun s => s) ht) := by
        apply pmap_sound (andThen_sound (symbol_sound _) (sepBy1P_sound pident_sound))
        intro a; simp [sep, fws_cons_simp, isWs]
      apply pmap_sound (andThen_sound (keyword_sound _) (andThen_sound pident_sound
        (andThen_sound (symbol_sound _) (andThen_sound hids (andThen_sound (symbol_sound _)
          (andThen_sound (opt_sound hrets)
          (andThen_sound (symbol_sound _) (andThen_sound hstmts (symbol_sound _)))))))))
      intro a
      obtain ⟨_, name, _, ps, _, rets, _, body, _⟩ := a
      cases rets with
      | none => simp [printStmt, printIds, sep, fws_cons_simp, fws_append, isWs]
      | some ht => obtain ⟨h, t⟩ := ht
                   simp [printStmt, printIds, printSepList1, printSepList, sep,
                     fws_cons_simp, fws_append, isWs]
    case letd =>
      apply pmap_sound (andThen_sound (keyword_sound _) (andThen_sound hids
        (opt_sound (andThen_sound (symbol_sound _) hexp))))
      intro a; obtain ⟨_, vars, val⟩ := a
      cases val with
      | none => simp [printStmt, sep, fws_cons_simp, fws_append, isWs]
      | some ve => obtain ⟨_, e⟩ := ve
                   simp [printStmt, sep, fws_cons_simp, fws_append, isWs]
    case ifs =>
      apply pmap_sound (andThen_sound (keyword_sound _) (andThen_sound hexp
        (andThen_sound (symbol_sound _) (andThen_sound hstmts (symbol_sound _)))))
      intro a; obtain ⟨_, c, _, body, _⟩ := a
      simp [printStmt, sep, fws_cons_simp, fws_append, isWs]
    case switch =>
      apply pmap_sound (andThen_sound (keyword_sound _) (andThen_sound hexp
        (andThen_sound hcases (opt_sound (andThen_sound (keyword_sound _)
          (andThen_sound (symbol_sound _) (andThen_sound hstmts (symbol_sound _))))))))
      intro a; obtain ⟨_, c, cases, dflt⟩ := a
      cases dflt with
      | none => simp [printStmt, sep, fws_cons_simp, fws_append, isWs]
      | some d => obtain ⟨_, _, body, _⟩ := d
                  simp [printStmt, sep, fws_cons_simp, fws_append, isWs]
    case forl =>
      apply pmap_sound (andThen_sound (keyword_sound _)
        (andThen_sound (andThen_sound (symbol_sound _) (andThen_sound hstmts (symbol_sound _)))
          (andThen_sound hexp (andThen_sound
            (andThen_sound (symbol_sound _) (andThen_sound hstmts (symbol_sound _)))
            (andThen_sound (symbol_sound _) (andThen_sound hstmts (symbol_sound _)))))))
      intro a; obtain ⟨_, ⟨_, init, _⟩, c, ⟨_, post, _⟩, _, body, _⟩ := a
      simp [printStmt, sep, fws_cons_simp, fws_append, isWs]
    case brk => exact pmap_sound (keyword_sound _) (fun _ => by simp [printStmt])
    case cont => exact pmap_sound (keyword_sound _) (fun _ => by simp [printStmt])
    case lv => exact pmap_sound (keyword_sound _) (fun _ => by simp [printStmt])
    case asgn =>
      apply pmap_sound (andThen_sound hids (andThen_sound (symbol_sound _) hexp))
      intro a; obtain ⟨vars, _, e⟩ := a
      simp [printStmt, sep, fws_cons_simp, fws_append, isWs]
    case estmt => exact pmap_sound hexp (fun e => by simp [printStmt])

theorem pStmtsF_sound (n : Nat) : Sound (pStmtsF n) printStmts := by
  simp only [pStmtsF, funext printStmts_eq]; exact manyP_sound (pStmtF_sound n)

end YulParser
