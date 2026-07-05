import YulParser.SepBy

/-!
# YulParser.Expr

Expression parser and printer with soundness. Expressions are recursive through
call arguments, so the parser is defined with a fuel bound (which the top level
instantiates to the input length) and soundness is by induction on the fuel.
-/

namespace YulParser

/-! ### Printer -/

mutual
/-- Re-print an expression. Argument lists are printed exactly as
`printSepList printExpr` (see `printExprList_eq`). -/
def printExpr : Expr → List Char
  | .lit l => printLit l
  | .var x => x
  | .call fn args => fn ++ ('(' :: (printExprList args ++ [')']))
/-- Comma-separated argument list (matches `printSepList printExpr`). -/
def printExprList : List Expr → List Char
  | [] => []
  | a :: as => printExpr a ++ printExprListTail as
/-- Tail of a comma list (matches `printMany (fun x => ',' :: sep ++ printExpr x)`). -/
def printExprListTail : List Expr → List Char
  | [] => []
  | a :: as => (',' :: sep ++ printExpr a) ++ sep ++ printExprListTail as
end

theorem printExprList_eq (as : List Expr) : printExprList as = printSepList printExpr as := by
  cases as with
  | nil => rfl
  | cons a as =>
    simp only [printExprList, printSepList]
    congr 1
    induction as with
    | nil => rfl
    | cons b bs ih => simp only [printExprListTail, printMany, ih]

/-! ### Parser -/

/-- Identifier token (whitespace-skipping). -/
def pident : Parser Id := token pidentRaw

theorem pident_sound : Sound pident (fun s => s) := token_sound pidentRaw_sound

/-- Expression parser, fuel-bounded. `call` recurses (through the argument list)
at one lower fuel. -/
def pExprF : Nat → Parser Expr
  | 0 => fun _ => none
  | n + 1 =>
    -- a call `ident ( args )`, else a bare literal, else a variable
    orElse
      (pmap (fun p => Expr.call p.1 p.2.2.1)
        (andThen pident (andThen (symbol ['(']) (andThen (sepBy0 (pExprF n)) (symbol [')'])))))
      (orElse (pmap Expr.lit pLit) (pmap Expr.var pident))

theorem pExprF_sound : ∀ n, Sound (pExprF n) printExpr := by
  intro n
  induction n with
  | zero => intro cs a rest h; simp [pExprF] at h
  | succ n ih =>
    apply orElse_sound
    · -- call
      apply pmap_sound
        (andThen_sound pident_sound
          (andThen_sound (symbol_sound ['(']) (andThen_sound (sepBy0_sound ih) (symbol_sound [')']))))
      intro a
      obtain ⟨fn, u1, args, u2⟩ := a
      simp [printExpr, printExprList_eq, sep, fws_append, fws_cons_simp, isWs]
    · apply orElse_sound
      · exact pmap_sound pLit_sound (fun l => by simp [printExpr])
      · exact pmap_sound pident_sound (fun x => by simp [printExpr])

end YulParser
