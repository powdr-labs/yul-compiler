import YulParser.Stmt

/-!
# YulParser.Obj

Object grammar: `object "name" { code { … } (object | data …)* }`, recursive
through nested sub-objects (fuel-bounded), with soundness by induction on the
fuel, reusing the statement soundness for the `code` block.
-/

namespace YulParser

/-! ### Printers -/

mutual
/-- Re-print an object. -/
def printObj : Obj → List Char
  | .mk name code items =>
      ['o','b','j','e','c','t'] ++ sep ++ '"' :: name ++ '"' :: sep ++ '{' :: sep ++
        ['c','o','d','e'] ++ sep ++ '{' :: (printStmts code ++ '}' :: sep) ++
        printObjItems items ++ ['}']
/-- Re-print the items following an object's `code` block. -/
def printObjItems : List ObjItem → List Char
  | [] => []
  | it :: its => printObjItem it ++ sep ++ printObjItems its
/-- Re-print one object item. -/
def printObjItem : ObjItem → List Char
  | .subObject o => printObj o
  | .dataItem d => ['d','a','t','a'] ++ sep ++ '"' :: d.name ++ '"' :: sep ++ printLit d.content
end

/-- Single-item printer, so `printObjItems = printMany printObjItem`. -/
theorem printObjItems_eq (its : List ObjItem) : printObjItems its = printMany printObjItem its := by
  induction its with
  | nil => rfl
  | cons it its ih => simp only [printObjItems, printMany, ih]

/-! ### String content -/

/-- A `"…"` string, returning the verbatim content (used for object and data
names). -/
def pStringContent : Parser (List Char) :=
  token (pmap (fun p => p.1.2) (andThen (andThen (pchar '"') (pWhile0 isStrChar)) (pchar '"')))

theorem pStringContent_sound : Sound pStringContent (fun c => '"' :: (c ++ ['"'])) := by
  apply token_sound
  apply pmap_sound
    (andThen_sound (andThen_sound (pchar_sound '"') (pWhile0_sound _)) (pchar_sound '"'))
  intro a; simp [sep, fws_cons_simp, fws_append, isWs]

/-- Data content: a string or hex-string literal. -/
def pDataLit : Parser Lit := token (orElse pHexStr pStr)

theorem pDataLit_sound : Sound pDataLit printLit :=
  token_sound (orElse_sound pHexStr_sound pStr_sound)

/-- Re-print a data item. -/
def printDataItem (d : DataItem) : List Char :=
  ['d','a','t','a'] ++ sep ++ '"' :: d.name ++ '"' :: sep ++ printLit d.content

/-! ### Parsers -/

mutual
/-- Object parser (fuel-bounded; sub-objects recurse at one lower fuel). -/
def pObjF : Nat → Parser Obj
  | 0 => fun _ => none
  | n + 1 =>
    pmap (fun p => Obj.mk p.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2.2.1)
      (andThen (keyword ['o','b','j','e','c','t'])
        (andThen pStringContent (andThen (symbol ['{'])
          (andThen (keyword ['c','o','d','e']) (andThen (symbol ['{'])
            (andThen (pStmtsF n) (andThen (symbol ['}'])
              (andThen (pObjItemsF n) (symbol ['}'])))))))))
/-- The item list following the `code` block. -/
def pObjItemsF : Nat → Parser (List ObjItem) := fun n => manyP (pObjItemF n)
/-- One item: a sub-object or a data segment. -/
def pObjItemF : Nat → Parser ObjItem := fun n =>
  orElse (pmap ObjItem.subObject (pObjF n))
    (pmap (fun p => ObjItem.dataItem ⟨p.2.1, p.2.2⟩)
      (andThen (keyword ['d','a','t','a']) (andThen pStringContent pDataLit)))
end

/-! ### Soundness -/

theorem pObjF_sound : ∀ n, Sound (pObjF n) printObj := by
  intro n
  induction n with
  | zero => intro cs a rest h; simp [pObjF] at h
  | succ n ih =>
    have hitem : Sound (pObjItemF n) printObjItem := by
      simp only [pObjItemF]
      refine orElse_sound ?sub ?dat
      case sub => exact pmap_sound ih (fun o => by simp [printObjItem])
      case dat =>
        apply pmap_sound (andThen_sound (keyword_sound _)
          (andThen_sound pStringContent_sound pDataLit_sound))
        intro a; obtain ⟨_, name, content⟩ := a
        simp [printObjItem, sep, fws_cons_simp, fws_append, isWs]
    have hitems : Sound (pObjItemsF n) printObjItems := by
      simp only [pObjItemsF, funext printObjItems_eq]; exact manyP_sound hitem
    have hstmts : Sound (pStmtsF n) printStmts := pStmtsF_sound n
    simp only [pObjF]
    apply pmap_sound (andThen_sound (keyword_sound _) (andThen_sound pStringContent_sound
      (andThen_sound (symbol_sound _) (andThen_sound (keyword_sound _) (andThen_sound (symbol_sound _)
        (andThen_sound hstmts (andThen_sound (symbol_sound _)
          (andThen_sound hitems (symbol_sound _)))))))))
    intro a
    obtain ⟨_, name, _, _, _, code, _, items, _⟩ := a
    simp [printObj, sep, fws_cons_simp, fws_append, isWs]

end YulParser
