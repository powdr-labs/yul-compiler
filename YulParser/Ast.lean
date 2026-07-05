/-!
# YulParser.Ast

A *concrete* (text-preserving) AST for Yul. Unlike a semantic AST, every token
keeps its exact characters — identifiers as their character list, numbers as
their digits, string contents verbatim — so that re-printing reproduces the
source up to whitespace. Covers the full (untyped, EVM-dialect) Yul grammar
including objects.
-/

namespace YulParser

/-- A Yul identifier, kept as its raw characters (`[a-zA-Z_$][a-zA-Z_$0-9.]*`). -/
abbrev Id := List Char

/-- A Yul literal, text-preserving. -/
inductive Lit where
  /-- Decimal number: the digit characters. -/
  | dec (digits : List Char)
  /-- Hex number `0x…`: the characters after `0x`. -/
  | hex (digits : List Char)
  /-- String literal `"…"`: the verbatim characters between the quotes. -/
  | str (content : List Char)
  /-- Hex string literal `hex"…"`: the verbatim characters between the quotes. -/
  | hexstr (content : List Char)
  /-- The `true` literal. -/
  | true
  /-- The `false` literal. -/
  | false
  deriving Repr, Inhabited

/-- A Yul expression: literal, variable, or call (built-in or user function —
same concrete syntax). -/
inductive Expr where
  | lit  (l : Lit)
  | var  (x : Id)
  | call (fn : Id) (args : List Expr)
  deriving Inhabited

/-- A Yul statement (the full statement grammar). -/
inductive Stmt where
  | block   (body : List Stmt)
  | funDef  (name : Id) (params : List Id) (rets : List Id) (body : List Stmt)
  | letDecl (vars : List Id) (val : Option Expr)
  | assign  (vars : List Id) (val : Expr)
  | ifStmt  (c : Expr) (body : List Stmt)
  | switchStmt (c : Expr) (cases : List (Lit × List Stmt)) (dflt : Option (List Stmt))
  | forLoop (init : List Stmt) (c : Expr) (post : List Stmt) (body : List Stmt)
  | exprStmt (e : Expr)
  | breakStmt
  | continueStmt
  | leaveStmt
  deriving Inhabited

/-- A named `data` segment (bytes written as a string or hex-string literal). -/
structure DataItem where
  name : List Char
  content : Lit
  deriving Inhabited

mutual
/-- A Yul object: a name, a `code` block, nested sub-objects, and data segments,
in source order (objects and data can interleave, so we keep a single item
list). -/
inductive Obj where
  | mk (name : List Char) (code : List Stmt) (items : List ObjItem)
/-- An item following the `code` block of an object: a nested object or a data
segment. -/
inductive ObjItem where
  | subObject (o : Obj)
  | dataItem (d : DataItem)
end

instance : Inhabited Obj := ⟨.mk [] [] []⟩
instance : Inhabited ObjItem := ⟨.dataItem default⟩

end YulParser
