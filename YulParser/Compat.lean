import YulParser.Obj

/-!
# YulParser.Compat

Compatibility parsers for Solidity Yul syntax that the canonical, round-trip
parser cannot represent faithfully in the current upstream AST:

* hex string literals in expression position are lowered to their left-aligned
  256-bit numeric value;
* hex-valued object data is decoded to bytes; and
* interleaved sub-objects and data items are normalized into the AST's separate
  `subObjects` and `data` lists.

The verified parsers in `Stmt` and `Obj` remain the first choice. These parsers
are used only as a fallback by the complete-source entry points.
-/

namespace YulParser

open YulParser (Parser andThen orElse opt pmap token manyP symbol keyword)
open YulSemantics (Literal Expr Stmt Object Data)
open YulSemantics.EVM (Op mkCall)

/-! ### Hex strings -/

def isHexBodyChar (c : Char) : Bool := isHexDigitC c || c == '_'

/-- Solidity permits underscores as visual separators in hex strings. They may
not lead, trail, or occur consecutively. -/
def validHexSeparators : List Char → Bool
  | [] => true
  | '_' :: _ => false
  | _ :: rest => validHexSeparatorsTail rest
where
  validHexSeparatorsTail : List Char → Bool
    | [] => true
    | ['_'] => false
    | '_' :: '_' :: _ => false
    | _ :: rest => validHexSeparatorsTail rest

def hexDigits (body : List Char) : List Char := body.filter (· != '_')

def validHexBody (body : List Char) : Bool :=
  validHexSeparators body && (hexDigits body).length % 2 == 0

/-- Raw `hex"…"` token parser. The prefix must be adjacent and the body must
contain complete bytes. -/
def pHexCharsRaw : Parser (List Char) := fun cs =>
  match cs with
  | 'h' :: 'e' :: 'x' :: '"' :: rest =>
      let body := rest.takeWhile isHexBodyChar
      match rest.dropWhile isHexBodyChar with
      | '"' :: after => if validHexBody body then some (hexDigits body, after) else none
      | _ => none
  | _ => none

def pHexChars : Parser (List Char) := token pHexCharsRaw

/-- Whether the next non-trivia token starts with the committed `hex"` prefix.
Once this is true, an invalid body must not fall back to parsing `hex` as an
identifier followed by an unrelated string. -/
def startsHexString (cs : List Char) : Bool :=
  match skipTrivia cs with
  | 'h' :: 'e' :: 'x' :: '"' :: _ => true
  | _ => false

/-- Yul hex string literals denote a byte sequence left-aligned in a 256-bit
word, just like ordinary string literals. -/
def hexLiteralValue (digits : List Char) : Nat :=
  let byteCount := digits.length / 2
  evalHex digits * 2 ^ (8 * (32 - byteCount))

def pHexLit : Parser Literal := fun cs =>
  match pHexChars cs with
  | some ([], _) => none
  | some (digits, rest) => some (.number (hexLiteralValue digits), rest)
  | none => none

/-! ### Expressions and statements with hex literal support -/

mutual
def pExprCompatF : Nat → Parser (Expr Op)
  | 0 => fun _ => none
  | n + 1 => fun cs =>
      if startsHexString cs then
        pmap Expr.lit pHexLit cs
      else
        orElse
          (pmap (fun p => mkCall p.1 p.2.2.1)
            (andThen pIdent
              (andThen (symbol ['(']) (andThen (pArgs (pExprCompatF n)) (symbol [')'])))))
          (orElse (pmap Expr.lit pLit) (pmap Expr.var pIdent)) cs

def pStmtCompatF : Nat → Parser (Stmt Op)
  | 0 => fun _ => none
  | n + 1 =>
    orElse
      (pmap (fun p => Stmt.block p.2.1)
        (andThen (symbol ['{']) (andThen (pStmtsCompatF n) (symbol ['}'])))) <|
    orElse
      (pmap (fun p => Stmt.funDef p.2.1 p.2.2.2.1
          (match p.2.2.2.2.2.1 with | some ht => ht.1 :: ht.2 | none => [])
          p.2.2.2.2.2.2.2.1)
        (andThen (keyword ['f','u','n','c','t','i','o','n'])
          (andThen pIdent (andThen (symbol ['('])
            (andThen (commaSep pIdent) (andThen (symbol [')'])
              (andThen (opt (pmap Prod.snd
                (andThen (symbol ['-', '>']) (commaSep1 pIdent))))
                (andThen (symbol ['{'])
                  (andThen (pStmtsCompatF n) (symbol ['}'])))))))))) <|
    orElse
      (pmap (fun p => Stmt.letDecl p.2.1 (p.2.2.map Prod.snd))
        (andThen (keyword ['l','e','t'])
          (andThen (commaSep pIdent)
            (opt (andThen (symbol [':','=']) (pExprCompatF n)))))) <|
    orElse
      (pmap (fun p => Stmt.cond p.2.1 p.2.2.2.1)
        (andThen (keyword ['i','f'])
          (andThen (pExprCompatF n)
            (andThen (symbol ['{']) (andThen (pStmtsCompatF n) (symbol ['}'])))))) <|
    orElse
      (pmap (fun p => Stmt.switch p.2.1 p.2.2.1
          (p.2.2.2.map (fun q => q.2.2.1)))
        (andThen (keyword ['s','w','i','t','c','h'])
          (andThen (pExprCompatF n) (andThen (pCasesCompatF n)
            (opt (andThen (keyword ['d','e','f','a','u','l','t'])
              (andThen (symbol ['{'])
                (andThen (pStmtsCompatF n) (symbol ['}']))))))))) <|
    orElse
      (pmap (fun p => Stmt.forLoop p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
        (andThen (keyword ['f','o','r'])
          (andThen (pBlockBody (pStmtsCompatF n))
            (andThen (pExprCompatF n)
              (andThen (pBlockBody (pStmtsCompatF n))
                (pBlockBody (pStmtsCompatF n))))))) <|
    orElse (pmap (fun _ => Stmt.«break») (keyword ['b','r','e','a','k'])) <|
    orElse (pmap (fun _ => Stmt.«continue») (keyword ['c','o','n','t','i','n','u','e'])) <|
    orElse (pmap (fun _ => Stmt.leave) (keyword ['l','e','a','v','e'])) <|
    orElse
      (pmap (fun p => Stmt.assign p.1 p.2.2)
        (andThen (commaSep pIdent)
          (andThen (symbol [':','=']) (pExprCompatF n))))
      (pmap Stmt.exprStmt (pExprCompatF n))

def pStmtsCompatF : Nat → Parser (List (Stmt Op)) := fun n => manyP (pStmtCompatF n)

def pCaseCompatF : Nat → Parser (Literal × List (Stmt Op)) := fun n cs =>
  match keyword ['c','a','s','e'] cs with
  | none => none
  | some (_, afterCase) =>
      let literalParser :=
        if startsHexString afterCase then pHexLit else pLit
      pmap (fun p => (p.1, p.2.2.1))
        (andThen literalParser
          (andThen (symbol ['{']) (andThen (pStmtsCompatF n) (symbol ['}'])))) afterCase

def pCasesCompatF : Nat → Parser (List (Literal × List (Stmt Op))) :=
  fun n => manyP (pCaseCompatF n)
end

/-! Solidity's syntax corpus includes a small number of checks performed after
parsing. Preserve those checks when the compatibility path makes their source
newly parseable. -/

def validDecimalSpelling : List Char → Bool
  | [] => false
  | ['0'] => true
  | '0' :: _ => false
  | digits => digits.all isDigitC

def validVerbatimName (name : String) : Bool :=
  let pre := "verbatim_".toList
  let chars := name.toList
  if chars.take pre.length != pre then false
  else
    let suffix := chars.drop pre.length
    let inputs := suffix.takeWhile isDigitC
    match suffix.dropWhile isDigitC with
    | 'i' :: '_' :: rest =>
        let outputs := rest.takeWhile isDigitC
        match rest.dropWhile isDigitC with
        | ['o'] => validDecimalSpelling inputs && validDecimalSpelling outputs
        | _ => false
    | _ => false

mutual
def exprCompatWF : Expr Op → Bool
  | .lit _ | .var _ => true
  | .builtin .dataoffset [.lit (.string _)] => true
  | .builtin .datasize [.lit (.string _)] => true
  | .builtin .dataoffset _ | .builtin .datasize _ => false
  | .builtin _ args => exprsCompatWF args
  | .call name args =>
      (!name.startsWith "verbatim_" || validVerbatimName name) && exprsCompatWF args

def exprsCompatWF : List (Expr Op) → Bool
  | [] => true
  | value :: values => exprCompatWF value && exprsCompatWF values
end

mutual
def stmtCompatWF : Stmt Op → Bool
  | .block body => stmtsCompatWF body
  | .funDef _ _ _ body => stmtsCompatWF body
  | .letDecl _ value => match value with | some e => exprCompatWF e | none => true
  | .assign _ value => exprCompatWF value
  | .cond condition body => exprCompatWF condition && stmtsCompatWF body
  | .switch condition cases dflt =>
      exprCompatWF condition && casesCompatWF cases &&
        match dflt with | some body => stmtsCompatWF body | none => true
  | .forLoop init condition post body =>
      stmtsCompatWF init && exprCompatWF condition && stmtsCompatWF post && stmtsCompatWF body
  | .exprStmt value => exprCompatWF value
  | .«break» | .«continue» | .leave => true

def stmtsCompatWF : List (Stmt Op) → Bool
  | [] => true
  | statement :: statements => stmtCompatWF statement && stmtsCompatWF statements

def casesCompatWF : List (Literal × List (Stmt Op)) → Bool
  | [] => true
  | (_, body) :: cases => stmtsCompatWF body && casesCompatWF cases
end

def parseBlockCompat (s : String) : Option (List (Stmt Op)) :=
  let cs := s.toList
  match pBlockBody (pStmtsCompatF (min cs.length maxParserFuel)) cs with
  | some (body, rest) =>
      if skipTrivia rest = [] && stmtsCompatWF body then some body else none
  | none => none

/-! ### Object data and source-item normalization -/

def pDataCompat : Parser (String × Data) :=
  fun cs =>
    match andThen (keyword ['d','a','t','a']) pName cs with
    | none => none
    | some ((_, name), rest) =>
        if startsHexString rest then
          match pHexChars rest with
          | some (digits, after) =>
              some ((name, Data.hex (Data.ofHex (String.ofList digits))), after)
          | none => none
        else
          match pName rest with
          | some (content, after) => some ((name, Data.string content), after)
          | none => none

inductive ObjItem where
  | sub (value : Object Op)
  | data (value : String × Data)

def ObjItem.subObjects : List ObjItem → List (Object Op)
  | [] => []
  | .sub o :: items => o :: subObjects items
  | .data _ :: items => subObjects items

def ObjItem.dataSegments : List ObjItem → List (String × Data)
  | [] => []
  | .sub _ :: items => dataSegments items
  | .data d :: items => d :: dataSegments items

def uniqueStrings : List String → Bool
  | [] => true
  | name :: names => !names.contains name && uniqueStrings names

mutual
def objectCompatWF : Object Op → Bool
  | .mk _ code subs datas =>
      let names := subs.map Object.name ++ datas.map Prod.fst
      stmtsCompatWF code && uniqueStrings names && objectsCompatWF subs

def objectsCompatWF : List (Object Op) → Bool
  | [] => true
  | object :: objects => objectCompatWF object && objectsCompatWF objects
end

mutual
def pObjCompatF : Nat → Parser (Object Op)
  | 0 => fun _ => none
  | n + 1 =>
      pmap (fun p =>
          let items := p.2.2.2.2.2.2.2.1
          Object.mk p.2.1 p.2.2.2.2.2.1
            (ObjItem.subObjects items) (ObjItem.dataSegments items))
        (andThen (keyword ['o','b','j','e','c','t'])
          (andThen pName (andThen (symbol ['{'])
            (andThen (keyword ['c','o','d','e']) (andThen (symbol ['{'])
              (andThen (pStmtsCompatF n) (andThen (symbol ['}'])
                (andThen (pObjItemsCompatF n) (symbol ['}'])))))))))

def pObjItemCompatF : Nat → Parser ObjItem := fun n =>
  orElse (pmap ObjItem.sub (pObjCompatF n)) (pmap ObjItem.data pDataCompat)

def pObjItemsCompatF : Nat → Parser (List ObjItem) := fun n => manyP (pObjItemCompatF n)
end

def parseObjectCompat (s : String) : Option (Object Op) :=
  let cs := s.toList
  match pObjCompatF (min cs.length maxParserFuel) cs with
  | some (o, rest) =>
      if skipTrivia rest = [] && objectCompatWF o then some o else none
  | none => none

end YulParser
