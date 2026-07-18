import YulParser.Atoms
import YulSemantics.Dialect.EVM
set_option warningAsError true
/-!
# YulParser.Expr

Expression parser producing `Expr EVM.Op` (built-in calls resolved via `EVM.mkCall`), fuel-bounded
through the argument lists, with `SoundC` by induction on the fuel.

The printers are laid out to match the combinator composition (`andThenC` concatenates
`pr₁ ab.1 ++ pr₂ ab.2`, each atom already space-delimited), so the `pmap` bridge is definitional
except for rewriting a resolved built-in's name back via `opName_of_parse`.
-/

namespace YulParser

open YulParser (Parser andThen orElse opt pmap token ppure manyP symbol)
open YulSemantics (Literal Expr)
open YulSemantics.EVM (Op mkCall opName parse)

/-! ### Punctuation tokens -/

theorem closed_lparen : Closed ['('] :=
  closed_punct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem closed_rparen : Closed [')'] :=
  closed_punct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem closed_comma : Closed [','] :=
  closed_punct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-! ### Built-in name inversion -/

set_option maxHeartbeats 2000000 in
/-- `opName` inverts `parse`: the source name of a resolved built-in is recovered. -/
theorem opName_of_parse (s : String) (op : Op) (h : parse s = some op) : opName op = s := by
  unfold parse at h
  split at h <;> first | (rw [Option.some.injEq] at h; subst h; rfl) | simp at h

/-! ### Printer -/

mutual
/-- Re-print an expression. `call`/`builtin` print as `name ( args )`, laid out to match the
`andThen` composition of the parser (extra spaces are irrelevant under `canon`). -/
def printExprC : Expr Op → List Char
  | .lit l => printLitC l
  | .var x => x.toList ++ [' ']
  | .builtin op args =>
      (opName op).toList ++ [' '] ++ (['('] ++ [' '] ++ (printArgsC args ++ ([')'] ++ [' '])))
  | .call fn args =>
      fn.toList ++ [' '] ++ (['('] ++ [' '] ++ (printArgsC args ++ ([')'] ++ [' '])))
/-- Comma-separated argument list. -/
def printArgsC : List (Expr Op) → List Char
  | [] => []
  | e :: es => printExprC e ++ printArgsTailC es
/-- The tail of an argument list (each element prefixed by `, `). -/
def printArgsTailC : List (Expr Op) → List Char
  | [] => []
  | e :: es => ([','] ++ [' '] ++ printExprC e) ++ printArgsTailC es
end

/-- The argument-list tail matches `printManyC` of the comma-prefixed element printer. -/
theorem printArgsTailC_eq (es : List (Expr Op)) :
    printArgsTailC es = printManyC (fun e => [','] ++ [' '] ++ printExprC e) es := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [printArgsTailC, printManyC, ih]

/-! ### Argument-list combinator -/

/-- Parse `, e`. -/
def pComma (pe : Parser (Expr Op)) : Parser (Expr Op) := pmap Prod.snd (andThen (symbol [',']) pe)

theorem pComma_soundC {pe : Parser (Expr Op)} (hpe : SoundC pe printExprC) :
    SoundC (pComma pe) (fun e => [','] ++ [' '] ++ printExprC e) := by
  unfold pComma
  refine pmapC (andThenC (symbolC closed_comma) hpe) ?_ ?_
  · intro a; rfl
  · intro a h; exact h

/-- Zero-or-more comma-separated `pe`, printed by `printArgsC`. -/
def pArgs (pe : Parser (Expr Op)) : Parser (List (Expr Op)) :=
  orElse (pmap (fun ab => ab.1 :: ab.2) (andThen pe (manyP (pComma pe)))) (ppure [])

theorem pArgs_soundC {pe : Parser (Expr Op)} (hpe : SoundC pe printExprC) :
    SoundC (pArgs pe) printArgsC := by
  apply orElseC
  · apply pmapC_eq (andThenC hpe (manyC (pComma_soundC hpe)))
    intro ab
    obtain ⟨e, es⟩ := ab
    show printArgsC (e :: es) = _
    rw [printArgsC, printArgsTailC_eq]
  · intro cs a rest h
    simp only [ppure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by simp [printArgsC], by simp only [printArgsC]; exact closed_nil⟩

/-! ### The expression parser -/

/-- Fuel-bounded expression parser; recurses through argument lists at one lower fuel. -/
def pExprF : Nat → Parser (Expr Op)
  | 0 => fun _ => none
  | n + 1 =>
    orElse
      (pmap (fun p => mkCall p.1 p.2.2.1)
        (andThen pIdent (andThen (symbol ['(']) (andThen (pArgs (pExprF n)) (symbol [')'])))))
      (orElse (pmap Expr.lit pLit) (pmap Expr.var pIdent))

theorem pExprF_soundC : ∀ n, SoundC (pExprF n) printExprC := by
  intro n
  induction n with
  | zero => intro cs a rest h; simp [pExprF] at h
  | succ n ih =>
    apply orElseC
    · apply pmapC (andThenC pIdent_soundC (andThenC (symbolC closed_lparen)
        (andThenC (pArgs_soundC ih) (symbolC closed_rparen))))
      · intro a
        obtain ⟨name, _, args, _⟩ := a
        show canon (printExprC (mkCall name args)) = _
        rw [mkCall]
        cases hpar : parse name with
        | none => rfl
        | some op => rw [printExprC, opName_of_parse name op hpar]
      · intro a hc
        obtain ⟨name, _, args, _⟩ := a
        show Closed (printExprC (mkCall name args))
        rw [mkCall]
        cases hpar : parse name with
        | none => exact hc
        | some op => rw [printExprC, opName_of_parse name op hpar]; exact hc
    · apply orElseC
      · exact pmapC_eq pLit_soundC (fun _ => rfl)
      · exact pmapC_eq pIdent_soundC (fun _ => rfl)

end YulParser
