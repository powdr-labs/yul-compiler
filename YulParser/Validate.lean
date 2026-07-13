import YulParser.Compat

/-!
# YulParser.Validate

Post-parse validation for the strict-assembly rules that are not represented by
the `yul-semantics` AST.  Solidity calls many of these diagnostics parser or
syntax errors, although they need scopes and function signatures and therefore
cannot be enforced by the combinator grammar alone.
-/

namespace YulParser

open YulSemantics (Literal Expr Stmt Object)
open YulSemantics.EVM (Op)

structure FunctionSig where
  name : String
  inputs : Nat
  outputs : Nat

structure ValidateCtx where
  vars : List String := []
  funcs : List FunctionSig := []
  loopControl : Bool := false
  inFunction : Bool := false
  forbidFunctions : Bool := false
  objectNames : Option (List String) := none
  inactiveBuiltins : List String := []

private def findFunction (name : String) : List FunctionSig → Option FunctionSig
  | [] => none
  | fn :: fns => if fn.name == name then some fn else findFunction name fns

private def unique (names : List String) : Bool :=
  names.all fun name => names.count name == 1

private def validIdentifier (name : String) : Bool :=
  !name.endsWith "." && !name.contains ".."

private def lowLevelReserved (name : String) : Bool :=
  let numbered (prefixName : String) :=
    let suffix := name.toList.drop prefixName.length
    name.startsWith prefixName && !suffix.isEmpty && suffix.all isDigitC
  name == "pc" || name == "jump" || name == "jumpi" || name == "jumpdest" ||
    numbered "dup" || numbered "swap" || numbered "push"

private def specialBuiltin (name : String) : Bool :=
  name == "memoryguard" || name == "linkersymbol" || name == "loadimmutable" ||
    name == "setimmutable" || name.startsWith "verbatim_"

private def builtinName (ctx : ValidateCtx) (name : String) : Bool :=
  ((YulSemantics.EVM.parse name).isSome && !ctx.inactiveBuiltins.contains name) ||
    specialBuiltin name

private def validDeclaredName (ctx : ValidateCtx) (name : String) : Bool :=
  validIdentifier name && !builtinName ctx name && !lowLevelReserved name &&
    name != "verbatim"

private def opInputs : Op → Nat
  | .add | .sub | .mul | .div | .sdiv | .mod | .smod | .exp | .signextend
  | .lt | .gt | .slt | .sgt | .eq | .and | .or | .xor | .byte | .shl | .shr | .sar
  | .keccak256 | .mstore | .mstore8 | .sstore | .tstore | .ret | .revert => 2
  | .addmod | .mulmod | .mcopy | .calldatacopy | .codecopy | .returndatacopy
  | .datacopy | .create => 3
  | .extcodecopy | .create2 => 4
  | .call | .callcode => 7
  | .delegatecall | .staticcall => 6
  | .clz | .iszero | .not | .pop | .mload | .sload | .tload | .calldataload
  | .datasize | .dataoffset | .balance | .extcodesize | .extcodehash | .blockhash
  | .blobhash | .selfdestruct => 1
  | .log0 => 2
  | .log1 => 3
  | .log2 => 4
  | .log3 => 5
  | .log4 => 6
  | .stop | .invalid | .msize | .calldatasize | .codesize | .returndatasize
  | .address | .origin | .caller | .callvalue | .gasprice | .selfbalance | .coinbase
  | .timestamp | .number | .prevrandao | .gaslimit | .chainid | .basefee
  | .blobbasefee | .gas => 0

private def opOutputs : Op → Nat
  | .pop | .mstore | .mstore8 | .mcopy | .sstore | .tstore | .calldatacopy
  | .codecopy | .returndatacopy | .datacopy | .extcodecopy | .log0 | .log1 | .log2
  | .log3 | .log4 | .selfdestruct | .stop | .ret | .revert | .invalid => 0
  | _ => 1

private def escapedByteLength : List Char → Nat
  | [] => 0
  | '\\' :: 'x' :: _ :: _ :: rest => 1 + escapedByteLength rest
  | '\\' :: _ :: rest => 1 + escapedByteLength rest
  | c :: rest => (String.singleton c).toUTF8.size + escapedByteLength rest

private def literalWordWF : Literal → Bool
  | .number n => n < 2 ^ 256
  | .bool _ => true
  | .string s => escapedByteLength s.toList ≤ 32

private def directString : Expr Op → Option String
  | .lit (.string value) => some value
  | _ => none

private def decimalValue? (digits : List Char) : Option Nat :=
  if !digits.isEmpty && digits.all isDigitC then
    some (digits.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0)
  else none

private def verbatimSignature? (name : String) : Option (Nat × Nat) := do
  let prefixChars := "verbatim_".toList
  let chars := name.toList
  if chars.take prefixChars.length != prefixChars then none else
  let suffix := chars.drop prefixChars.length
  let inputDigits := suffix.takeWhile isDigitC
  let inputs ← decimalValue? inputDigits
  if inputDigits.length > 1 && inputDigits.head? == some '0' then none else
  match suffix.drop inputDigits.length with
  | 'i' :: '_' :: rest =>
      let outputDigits := rest.takeWhile isDigitC
      let outputs ← decimalValue? outputDigits
      if outputDigits.length > 1 && outputDigits.head? == some '0' then none
      else if rest.drop outputDigits.length == ['o'] then some (inputs + 1, outputs)
      else none
  | _ => none

private def objectNameAllowed (ctx : ValidateCtx) (name : String) : Bool :=
  match ctx.objectNames with
  | none => true
  | some names => !name.startsWith "." && !name.contains ".." && names.contains name

mutual
private def exprOutputs (ctx : ValidateCtx) : Expr Op → Option Nat
  | .lit literal => if literalWordWF literal then some 1 else none
  | .var name =>
      if validIdentifier name && ctx.vars.contains name && !builtinName ctx name then some 1 else none
  | .builtin op args => do
      let name := YulSemantics.EVM.opName op
      if ctx.inactiveBuiltins.contains name then
        let fn ← findFunction name ctx.funcs
        if args.length != fn.inputs then none
        validArgs ctx args
        some fn.outputs
      else if args.length != opInputs op then none
      else if op == .datasize || op == .dataoffset then
        match args with
        | [arg] =>
            let name ← directString arg
            if objectNameAllowed ctx name then some (opOutputs op) else none
        | _ => none
      else
        validArgs ctx args
        some (opOutputs op)
  | .call name args => do
      if !validIdentifier name || lowLevelReserved name then none
      if name == "memoryguard" then
        if args.length != 1 then none else validArgs ctx args; some 1
      else if name == "linkersymbol" || name == "loadimmutable" then
        match args with
        | [arg] => if (directString arg).isSome then some 1 else none
        | _ => none
      else if name == "setimmutable" then
        match args with
        | [offset, key, value] =>
            if (← exprOutputs ctx offset) != 1 || (directString key).isNone ||
                (← exprOutputs ctx value) != 1 then none
            some 0
        | _ => none
      else if name.startsWith "verbatim_" then
        let (inputs, outputs) ← verbatimSignature? name
        if args.length != inputs then none
        validArgs ctx args
        some outputs
      else
        let fn ← findFunction name ctx.funcs
        if args.length != fn.inputs then none
        validArgs ctx args
        some fn.outputs

private def validArgs (ctx : ValidateCtx) : List (Expr Op) → Option Unit
  | [] => some ()
  | arg :: args => do
      if (← exprOutputs ctx arg) != 1 then none
      validArgs ctx args

private def validateCases (ctx : ValidateCtx) : List (Literal × List (Stmt Op)) → Option Unit
  | [] => some ()
  | (literal, body) :: cases => do
      if !literalWordWF literal then none
      let _ ← validateBlock ctx body
      validateCases ctx cases

private def validateStmt (ctx : ValidateCtx) (stmt : Stmt Op) : Option ValidateCtx := do
  match stmt with
  | .block body =>
      let _ ← validateBlock ctx body
      some ctx
  | .funDef _ params rets body =>
      if ctx.forbidFunctions then none
      let names := params ++ rets
      if !unique names || !names.all (validDeclaredName ctx) ||
          names.any (ctx.vars.contains ·) || names.any (fun n => (findFunction n ctx.funcs).isSome) then
        none
      let fnCtx : ValidateCtx := {
        vars := names
        funcs := ctx.funcs
        inFunction := true
        objectNames := ctx.objectNames
        inactiveBuiltins := ctx.inactiveBuiltins
      }
      let _ ← validateBlock fnCtx body
      some ctx
  | .letDecl vars value =>
      if vars.isEmpty || !unique vars || !vars.all (validDeclaredName ctx) ||
          vars.any (ctx.vars.contains ·) || vars.any (fun n => (findFunction n ctx.funcs).isSome) then
        none
      match value with
      | some rhs => if (← exprOutputs ctx rhs) != vars.length then none
      | none => pure ()
      some { ctx with vars := vars ++ ctx.vars }
  | .assign vars value =>
      if vars.isEmpty || !unique vars || !vars.all validIdentifier ||
          !vars.all (ctx.vars.contains ·) || (← exprOutputs ctx value) != vars.length then
        none
      some ctx
  | .cond condition body =>
      if (← exprOutputs ctx condition) != 1 then none
      let _ ← validateBlock ctx body
      some ctx
  | .switch condition cases dflt =>
      if (← exprOutputs ctx condition) != 1 || (cases.isEmpty && dflt.isNone) then none
      let values := cases.map fun c => (YulSemantics.EVM.litValue c.1).toNat
      if values.any fun value => values.count value != 1 then none
      validateCases ctx cases
      match dflt with
      | some body => let _ ← validateBlock ctx body; pure ()
      | none => pure ()
      some ctx
  | .forLoop init condition post body =>
      let initCtx ← validateStmts { ctx with loopControl := false, forbidFunctions := true } init
      if (← exprOutputs initCtx condition) != 1 then none
      let _ ← validateBlock { initCtx with loopControl := false, forbidFunctions := false } post
      let _ ← validateBlock { initCtx with loopControl := true, forbidFunctions := false } body
      some ctx
  | .exprStmt value =>
      if (← exprOutputs ctx value) != 0 then none
      some ctx
  | .«break» | .«continue» => if ctx.loopControl then some ctx else none
  | .leave => if ctx.inFunction then some ctx else none

private def prepareFunctions (ctx : ValidateCtx) (statements : List (Stmt Op)) : Option ValidateCtx := do
  let defs := statements.filterMap fun
    | .funDef name params rets _ => some { name, inputs := params.length, outputs := rets.length }
    | _ => none
  let names := defs.map FunctionSig.name
  if !unique names || !names.all (validDeclaredName ctx) || names.any (ctx.vars.contains ·) ||
      names.any (fun n => (findFunction n ctx.funcs).isSome) then none
  some { ctx with funcs := defs ++ ctx.funcs }

private def validateStmts (ctx : ValidateCtx) : List (Stmt Op) → Option ValidateCtx
  | [] => some ctx
  | statement :: statements => do
      let next ← validateStmt ctx statement
      validateStmts next statements

private def validateBlock (ctx : ValidateCtx) (statements : List (Stmt Op)) : Option ValidateCtx := do
  let blockCtx ← prepareFunctions ctx statements
  validateStmts blockCtx statements
end

private def validNumberToken (digits : List Char) : Bool :=
  let value := numVal digits
  let spelling :=
    match digits with
    | '0' :: 'x' :: rest => !rest.isEmpty && rest.all isHexDigitC
    | '0' :: 'X' :: rest => !rest.isEmpty && rest.all isHexDigitC
    | ['0'] => true
    | '0' :: _ => false
    | _ => !digits.isEmpty && digits.all isDigitC
  spelling && value < 2 ^ 256

private partial def sourceNumbersWF : List Char → Bool
  | [] => true
  | '/' :: '/' :: rest => sourceNumbersWF (rest.dropWhile (· != '\n'))
  | '/' :: '*' :: rest => sourceNumbersWF (afterBlockComment rest)
  | '"' :: rest =>
      match quotedBody rest with
      | some (_, after) => sourceNumbersWF after
      | none => false
  | c :: rest =>
      if isDigitC c then
        let token := c :: rest.takeWhile isNumCont
        validNumberToken token && sourceNumbersWF (rest.dropWhile isNumCont)
      else sourceNumbersWF rest

private def forbiddenBidi (c : Char) : Bool :=
  let n := c.toNat
  (0x202a ≤ n && n ≤ 0x202e) || (0x2066 ≤ n && n ≤ 0x2069)

def sourceLexWF (source : String) : Bool :=
  sourceNumbersWF source.toList && !source.toList.any forbiddenBidi

private def inactiveBuiltins (source : String) : List String :=
  if source.contains "EVMVersion: <=berlin" then
    ["basefee", "blobbasefee", "blobhash", "mcopy", "tload", "tstore", "clz"]
  else if source.contains "EVMVersion: <=shanghai" || source.contains "EVMVersion: <cancun" then
    ["blobbasefee", "blobhash", "mcopy", "tload", "tstore", "clz"]
  else if source.contains "EVMVersion: <osaka" then
    ["clz"]
  else []

def validateBlockSource (source : String) (body : List (Stmt Op)) : Bool :=
  sourceLexWF source &&
    (validateBlock { inactiveBuiltins := inactiveBuiltins source } body).isSome

private def withPrefix (prefixName : String) (name : String) : String :=
  prefixName ++ "." ++ name

private def accessibleObjectNames : Object Op → List String
  | .mk name _ subs datas =>
      let dataNames := (datas.map Prod.fst).filter (fun n => !n.startsWith ".")
      let subNames := subs.flatMap fun sub =>
        let child := Object.name sub
        child :: ((accessibleObjectNames sub).filter (fun n => n != child && !n.startsWith ".")
          |>.map (withPrefix child))
      name :: dataNames ++ subNames

private def collectImmutableCallsExpr : Expr Op → List String × List String
  | .lit _ | .var _ | .builtin _ [] | .call _ [] => ([], [])
  | .builtin _ args => args.foldl (fun acc e =>
      let found := collectImmutableCallsExpr e
      (acc.1 ++ found.1, acc.2 ++ found.2)) ([], [])
  | .call name args =>
      let nested := args.foldl (fun acc e =>
        let found := collectImmutableCallsExpr e
        (acc.1 ++ found.1, acc.2 ++ found.2)) ([], [])
      if name == "loadimmutable" then
        match args with | [.lit (.string key)] => (key :: nested.1, nested.2) | _ => nested
      else if name == "setimmutable" then
        match args with | [_, .lit (.string key), _] => (nested.1, key :: nested.2) | _ => nested
      else nested

mutual
private partial def collectImmutableCallsStmt : Stmt Op → List String × List String
  | .block body | .funDef _ _ _ body => collectImmutableCallsStmts body
  | .letDecl _ value => value.map collectImmutableCallsExpr |>.getD ([], [])
  | .assign _ value | .exprStmt value => collectImmutableCallsExpr value
  | .cond condition body => combineImmutable (collectImmutableCallsExpr condition)
      (collectImmutableCallsStmts body)
  | .switch condition cases dflt =>
      let fromCases := cases.foldl (fun acc c => combineImmutable acc
        (collectImmutableCallsStmts c.2)) ([], [])
      let fromDefault := dflt.map collectImmutableCallsStmts |>.getD ([], [])
      combineImmutable (collectImmutableCallsExpr condition)
        (combineImmutable fromCases fromDefault)
  | .forLoop init condition post body => combineImmutable (collectImmutableCallsStmts init)
      (combineImmutable (collectImmutableCallsExpr condition)
        (combineImmutable (collectImmutableCallsStmts post) (collectImmutableCallsStmts body)))
  | .«break» | .«continue» | .leave => ([], [])

private partial def collectImmutableCallsStmts : List (Stmt Op) → List String × List String
  | [] => ([], [])
  | statement :: statements => combineImmutable (collectImmutableCallsStmt statement)
      (collectImmutableCallsStmts statements)

private partial def combineImmutable (a b : List String × List String) : List String × List String :=
  (a.1 ++ b.1, a.2 ++ b.2)
end

mutual
private partial def collectImmutableCallsObject : Object Op → List String × List String
  | .mk _ code subs _ => combineImmutable (collectImmutableCallsStmts code)
      (collectImmutableCallsObjects subs)

private partial def collectImmutableCallsObjects : List (Object Op) → List String × List String
  | [] => ([], [])
  | object :: objects => combineImmutable (collectImmutableCallsObject object)
      (collectImmutableCallsObjects objects)
end

mutual
private def validateObjectTree (inactive : List String) : Object Op → Bool
  | object@(.mk name code subs datas) =>
      let childNames := subs.map Object.name
      let dataNames := datas.map Prod.fst
      let allNames := childNames ++ dataNames
      let objectCtx : ValidateCtx := {
        objectNames := some (accessibleObjectNames object)
        inactiveBuiltins := inactive
      }
      unique allNames && !allNames.contains name &&
        (validateBlock objectCtx code).isSome &&
        validateObjects inactive subs

private def validateObjects (inactive : List String) : List (Object Op) → Bool
  | [] => true
  | object :: objects => validateObjectTree inactive object && validateObjects inactive objects
end

def validateObjectSource (source : String) (object : Object Op) : Bool :=
  let immutableCalls := collectImmutableCallsObject object
  sourceLexWF source && validateObjectTree (inactiveBuiltins source) object &&
    immutableCalls.1.all immutableCalls.2.contains

end YulParser
