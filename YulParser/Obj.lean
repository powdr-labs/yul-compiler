import YulParser.Stmt
import YulSemantics.Object
set_option warningAsError true
/-!
# YulParser.Obj

Object parser producing `Object EVM.Op`, and the top-level `parseObject` with the main
round-trip theorem `parse_canon_obj`: if the parser accepts `s`, then re-printing the resulting
AST (with the faithful renderer `printObjC`) is `canon`-equal to `s` — i.e. the parser preserves
every token except whitespace, comments, and number base.

Scope notes for this verified parser: sub-objects are parsed before data segments (the
`Object` AST — and `yul-semantics`' own pretty-printer — do not preserve source interleaving of
the two), and `data` segments are string-valued (`hex"…"` data would require `canon` to also
normalize hex-string literals to bytes, since `Data.ofHex`/`toHex` canonicalise them). Type
annotations are not part of the accepted syntax (`yul-semantics` is single-sorted). The public
`parseSource` entry point provides a documented lossy fallback for the first two restrictions.
-/

namespace YulParser

open YulParser (Parser andThen orElse opt pmap token ppure manyP symbol keyword isWs)
open YulSemantics (Literal Stmt Object Data)
open YulSemantics.EVM (Op)

/-! ### String content (object / data names, string data) -/

/-- Parse a `"…"` name, retaining the spelling of backslash escapes. -/
def pName : Parser String := pmap String.ofList pStringChars

/-- Printer for a string token. -/
def printNameC (s : String) : List Char := printStringC s.toList

theorem pName_soundC : SoundC pName printNameC := by
  apply pmapC_eq pStringChars_soundC
  intro content
  simp [printNameC, printStringC]

/-! ### Data segments (string-valued) -/

/-- Parse `data "name" "content"` into a named string data segment. -/
def pData : Parser (String × Data) :=
  pmap (fun p => (p.2.1, Data.string p.2.2))
    (andThen (keyword ['d','a','t','a']) (andThen pName pName))

/-- Printer for a named data segment. -/
def printDataC : String × Data → List Char
  | (name, .string content) =>
      (['d','a','t','a'] ++ [' ']) ++ (printNameC name ++ printNameC content)
  | (name, .hex _bytes) =>  -- not produced by the parser; total-function placeholder
      (['d','a','t','a'] ++ [' ']) ++ (printNameC name ++ ('h' :: 'e' :: 'x' :: printNameC ""))

theorem pData_soundC : SoundC pData printDataC := by
  refine pmapC_eq (andThenC (keywordC (by decide) (by intro x hx; fin_cases hx <;> decide))
    (andThenC pName_soundC pName_soundC)) ?_
  intro a; obtain ⟨_, name, content⟩ := a; rfl

/-! ### Printer -/

mutual
/-- Re-print an object (`code`, then sub-objects, then data). -/
def printObjC : Object Op → List Char
  | .mk name code subs datas =>
      ['o','b','j','e','c','t'] ++ [' '] ++ printNameC name ++ ['{'] ++ [' '] ++
        ['c','o','d','e'] ++ [' '] ++ ['{'] ++ [' '] ++ printStmtsC code ++ ['}'] ++ [' '] ++
        printSubsC subs ++ printDatasC datas ++ ['}'] ++ [' ']
/-- Sub-object list. -/
def printSubsC : List (Object Op) → List Char
  | [] => []
  | o :: os => printObjC o ++ printSubsC os
/-- Data-segment list. -/
def printDatasC : List (String × Data) → List Char
  | [] => []
  | nd :: nds => printDataC nd ++ printDatasC nds
end

theorem printSubsC_eq (os : List (Object Op)) : printSubsC os = printManyC printObjC os := by
  induction os with
  | nil => rfl
  | cons o os ih => simp only [printSubsC, printManyC, ih]

theorem printDatasC_eq (nds : List (String × Data)) :
    printDatasC nds = printManyC printDataC nds := by
  induction nds with
  | nil => rfl
  | cons nd nds ih => simp only [printDatasC, printManyC, ih]

/-! ### Parser -/

/-- `data` segment closed fact. -/
theorem closed_data : Closed (['d','a','t','a'] ++ [' ']) :=
  closed_ident (by decide) (by intro x hx; fin_cases hx <;> decide)

mutual
/-- Object parser, fuel-bounded; sub-objects recurse at one lower fuel. -/
def pObjF : Nat → Parser (Object Op)
  | 0 => fun _ => none
  | n + 1 =>
    pmap (fun p => Object.mk p.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2.1)
      (andThen (keyword ['o','b','j','e','c','t'])
        (andThen pName (andThen (symbol ['{'])
          (andThen (keyword ['c','o','d','e']) (andThen (symbol ['{'])
            (andThen (pStmtsF n) (andThen (symbol ['}'])
              (andThen (pSubsF n) (andThen (manyP pData) (symbol ['}']))))))))))
/-- Sub-object list. -/
def pSubsF : Nat → Parser (List (Object Op)) := fun n => manyP (pObjF n)
end

theorem pObjF_soundC : ∀ n, SoundC (pObjF n) printObjC := by
  intro n
  induction n with
  | zero => intro cs a rest h; simp [pObjF] at h
  | succ n ih =>
    have hsubs : SoundC (pSubsF n) printSubsC := by
      simp only [pSubsF, funext printSubsC_eq]; exact manyC ih
    have hdatas : SoundC (manyP pData) printDatasC := by
      rw [funext printDatasC_eq]; exact manyC pData_soundC
    have hstmts : SoundC (pStmtsF n) printStmtsC := pStmtsF_soundC n
    simp only [pObjF]
    refine pmapC_eq (andThenC (keywordC (by decide) (by intro x hx; fin_cases hx <;> decide))
      (andThenC pName_soundC (andThenC (symbolC closed_lbrace)
        (andThenC (keywordC (by decide) (by intro x hx; fin_cases hx <;> decide))
          (andThenC (symbolC closed_lbrace) (andThenC hstmts (andThenC (symbolC closed_rbrace)
            (andThenC hsubs (andThenC hdatas (symbolC closed_rbrace)))))))))) ?_
    intro a
    obtain ⟨_, name, _, _, _, code, _, subs, datas, _⟩ := a
    simp only [printObjC, List.append_assoc]

/-! ### Top level -/

/-- Parse a full Yul object; the entire input must be consumed up to trailing
whitespace and comments. -/
def parseObject (s : String) : Option (Object Op) :=
  let cs := s.toList
  match pObjF (min cs.length maxParserFuel) cs with
  | some (o, rest) => if skipTrivia rest = [] then some o else none
  | none => none

/-- **Main theorem.** If `parseObject` accepts `s`, then re-printing the resulting AST is
`canon`-equal to `s`: the parser preserves every token except whitespace, comments, and number
base. -/
theorem parse_canon_obj (s : String) (o : Object Op) (h : parseObject s = some o) :
    canon (printObjC o) = canon s.toList := by
  unfold parseObject at h
  simp only at h
  split at h
  · rename_i o' rest heq
    split at h
    · rename_i hrest
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨he, _⟩ :=
        pObjF_soundC (min s.toList.length maxParserFuel) s.toList o' rest heq
      rw [← he, canon_eq_nil_of_skipTrivia_eq_nil hrest, List.append_nil]
    · exact absurd h (by simp)
  · exact absurd h (by simp)

end YulParser
