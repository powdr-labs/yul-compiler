import YulParser.Source
import YulEvmCompiler.ObjectCompile
import YulEvmCompiler.Optimizer.Implementation.Pipeline
import YulEvmCompiler.Optimizer.Implementation.StackLayoutObject
import YulEvmCompiler.Optimizer.Implementation.MemorySpillSelect
import YulEvmCompiler.Optimizer.Implementation.MemorySpillSound
set_option warningAsError true
/-!
# YulParser.Compile

The source-text entry point for the compiler. Brace-delimited programs assemble
directly. Object-rooted programs are recursively laid out with their child
objects and data bytes, and `dataoffset`/`datasize` are resolved to constants
in that concrete layout.
-/

namespace YulParser

open YulSemantics (Expr Stmt Object)

/-
The canonical parser retains string escape spelling so its printer can round
trip the exact token. Source execution needs the bytes denoted by that spelling
instead. Convert expression-position string literals to their left-aligned word
value before optimization/compilation; object/data names and the literal-name
arguments of layout/linker/immutable extensions remain spelling-sensitive.
-/

private def escapeHexValue (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (10 + c.toNat - 'a'.toNat)
  else if 'A' ≤ c && c ≤ 'F' then some (10 + c.toNat - 'A'.toNat)
  else none

private def decodeEscapedBytes : List Char → Option (List UInt8)
  | [] => some []
  | '\\' :: 'x' :: a :: b :: rest => do
      let hi ← escapeHexValue a
      let lo ← escapeHexValue b
      return UInt8.ofNat (16 * hi + lo) :: (← decodeEscapedBytes rest)
  | '\\' :: 'u' :: a :: b :: c :: d :: rest => do
      let a ← escapeHexValue a
      let b ← escapeHexValue b
      let c ← escapeHexValue c
      let d ← escapeHexValue d
      let scalar := 4096 * a + 256 * b + 16 * c + d
      return (String.singleton (Char.ofNat scalar)).toUTF8.toList ++
        (← decodeEscapedBytes rest)
  | '\\' :: 'n' :: rest => return 10 :: (← decodeEscapedBytes rest)
  | '\\' :: 'r' :: rest => return 13 :: (← decodeEscapedBytes rest)
  | '\\' :: 't' :: rest => return 9 :: (← decodeEscapedBytes rest)
  | '\\' :: '"' :: rest => return 34 :: (← decodeEscapedBytes rest)
  | '\\' :: '\\' :: rest => return 92 :: (← decodeEscapedBytes rest)
  | '\\' :: _ => none
  | c :: rest => return c.toString.toUTF8.toList ++ (← decodeEscapedBytes rest)

/-- Decode an escape-preserving Yul string spelling to its left-aligned word. -/
def decodedStringValue? (s : String) : Option Nat := do
  let bytes ← decodeEscapedBytes s.toList
  if bytes.length > 32 then none
  else
    let value := bytes.foldl (fun n byte => n * 256 + byte.toNat) 0
    some (value * 2 ^ (8 * (32 - bytes.length)))

private def decodeValueLiteral : YulSemantics.Literal → YulSemantics.Literal
  | .string s => (decodedStringValue? s).map YulSemantics.Literal.number
      |>.getD (.string s)
  | literal => literal

private def literalNameCall (name : String) : Bool :=
  name == "linkersymbol" || name == "loadimmutable" || name == "setimmutable"

mutual
  def decodeValueExpr : Expr YulSemantics.EVM.Op → Expr YulSemantics.EVM.Op
    | .lit literal => .lit (decodeValueLiteral literal)
    | .var name => .var name
    | .call name args =>
        if literalNameCall name then .call name args
        else .call name (decodeValueArgs args)
    | .builtin op args =>
        if op == .dataoffset || op == .datasize then .builtin op args
        else .builtin op (decodeValueArgs args)

  def decodeValueArgs : List (Expr YulSemantics.EVM.Op) →
      List (Expr YulSemantics.EVM.Op)
    | [] => []
    | arg :: rest => decodeValueExpr arg :: decodeValueArgs rest
end

mutual
  def decodeValueStmt : Stmt YulSemantics.EVM.Op → Stmt YulSemantics.EVM.Op
    | .block body => .block (decodeValueStmts body)
    | .funDef name params returns body =>
        .funDef name params returns (decodeValueStmts body)
    | .letDecl names value => .letDecl names (value.map decodeValueExpr)
    | .assign names value => .assign names (decodeValueExpr value)
    | .cond condition body =>
        .cond (decodeValueExpr condition) (decodeValueStmts body)
    | .switch condition cases dflt =>
        .switch (decodeValueExpr condition)
          (decodeValueCases cases)
          (match dflt with
          | some body => some (decodeValueStmts body)
          | none => none)
    | .forLoop init condition post body =>
        .forLoop (decodeValueStmts init) (decodeValueExpr condition)
          (decodeValueStmts post) (decodeValueStmts body)
    | .exprStmt expression => .exprStmt (decodeValueExpr expression)
    | .break => .break
    | .continue => .continue
    | .leave => .leave
    termination_by statement => 2 * sizeOf statement

  def decodeValueStmts : List (Stmt YulSemantics.EVM.Op) →
      List (Stmt YulSemantics.EVM.Op)
    | [] => []
    | statement :: rest => decodeValueStmt statement :: decodeValueStmts rest
    termination_by statements => 2 * sizeOf statements + 1

  def decodeValueCases :
      List (YulSemantics.Literal × List (Stmt YulSemantics.EVM.Op)) →
      List (YulSemantics.Literal × List (Stmt YulSemantics.EVM.Op))
    | [] => []
    | (literal, body) :: rest =>
        (decodeValueLiteral literal, decodeValueStmts body) ::
          decodeValueCases rest
    termination_by cases => 2 * sizeOf cases + 1
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

mutual
  def decodeValueObject : Object YulSemantics.EVM.Op → Object YulSemantics.EVM.Op
    | .mk name code children segments =>
        .mk name (decodeValueStmts code) (decodeValueObjects children) segments

  def decodeValueObjects : List (Object YulSemantics.EVM.Op) →
      List (Object YulSemantics.EVM.Op)
    | [] => []
    | obj :: rest => decodeValueObject obj :: decodeValueObjects rest
end

#guard decodedStringValue? "`\\x01`\\x00\\xf3" ==
  some (0x60016000f3 * 2 ^ (8 * 27))

/-- Desugar solc-IR hint builtins that have no EVM value effect into core Yul
for the ordinary compilation candidates. `memoryguard(e)` returns `e` when no
optimizer scratch is reserved. The final spilling fallback instead retains the
raw marker, raises its result by the reserved call-path bound, and only then
hands the resulting core Yul to the compiler. Every other node is rebuilt
structurally, so programs that do not use such hints are unaffected. -/
def desugarExpr {Op : Type} : Expr Op → Expr Op :=
  YulEvmCompiler.Optimizer.MemorySpill.eraseMemoryGuardExpr

def desugarStmt {Op : Type} : Stmt Op → Stmt Op :=
  YulEvmCompiler.Optimizer.MemorySpill.eraseMemoryGuardStmt

def desugarObject {Op : Type} : Object Op → Object Op :=
  YulEvmCompiler.Optimizer.MemorySpill.eraseMemoryGuardObject

/-! ### Dead `linkersymbol` bindings

solc's unoptimized `--ir` output materializes every qualified mention of a
library (`Lib.f(x)` with `f` internal) as a dead placeholder binding
`let addr := linkersymbol("file:Lib")`, even though the call itself is a plain
internal Yul call and `addr` is never referenced. `linkersymbol` is a pure
link-time constant with no evaluation effect, so removing a binding whose
variable is never referenced anywhere afterwards cannot change behavior.

Only provably dead bindings are removed: the name must not occur — read or
written — anywhere else in the whole program (a conservative, shadowing-proof
over-approximation; solc generates globally unique names). A program that
actually uses a `linkersymbol` value keeps the call and is still rejected by
the compiler as unsupported, since with no linker there is no sound value to
give it. -/

/-- Variable names referenced by an expression. -/
partial def exprRefs {Op : Type} : Expr Op → List String
  | .var name => [name]
  | .call _ args => args.flatMap exprRefs
  | .builtin _ args => args.flatMap exprRefs
  | _ => []

/-- Names referenced by a statement: variable reads and assignment targets
(a later write to a declared name is a reference that keeps its declaration
alive). Declarations themselves do not count. -/
partial def stmtRefs {Op : Type} : Stmt Op → List String
  | .block body => body.flatMap stmtRefs
  | .funDef _ _ _ body => body.flatMap stmtRefs
  | .letDecl _ val => (val.map exprRefs).getD []
  | .assign vars val => vars ++ exprRefs val
  | .cond c body => exprRefs c ++ body.flatMap stmtRefs
  | .switch c cases dflt =>
      exprRefs c ++ cases.flatMap (fun cb => cb.2.flatMap stmtRefs) ++
        ((dflt.map (·.flatMap stmtRefs)).getD [])
  | .forLoop init c post body =>
      init.flatMap stmtRefs ++ exprRefs c ++ post.flatMap stmtRefs ++
        body.flatMap stmtRefs
  | .exprStmt e => exprRefs e
  | _ => []

partial def objectRefs {Op : Type} : Object Op → List String
  | .mk _ code subs _ => code.flatMap stmtRefs ++ subs.flatMap objectRefs

/-- Drop `let x := linkersymbol("…")` when `used x` is false. Every other
statement is rebuilt structurally. -/
partial def pruneLinkerStmts {Op : Type} (used : String → Bool) :
    List (Stmt Op) → List (Stmt Op)
  | [] => []
  | stmt :: stmts =>
      let rest := pruneLinkerStmts used stmts
      match stmt with
      | .letDecl [x] (some (.call "linkersymbol" _)) =>
          if used x then stmt :: rest else rest
      | .block body => .block (pruneLinkerStmts used body) :: rest
      | .funDef name params rets body =>
          .funDef name params rets (pruneLinkerStmts used body) :: rest
      | .cond c body => .cond c (pruneLinkerStmts used body) :: rest
      | .switch c cases dflt =>
          .switch c (cases.map (fun cb => (cb.1, pruneLinkerStmts used cb.2)))
            (dflt.map (pruneLinkerStmts used)) :: rest
      | .forLoop init c post body =>
          .forLoop (pruneLinkerStmts used init) c (pruneLinkerStmts used post)
            (pruneLinkerStmts used body) :: rest
      | s => s :: rest

partial def pruneLinkerObject {Op : Type} (used : String → Bool) :
    Object Op → Object Op
  | .mk name code subs segs =>
      .mk name (pruneLinkerStmts used code) (subs.map (pruneLinkerObject used)) segs

/-- Remove dead `linkersymbol` bindings from a block, per the module notes. -/
def pruneLinkerBlock {Op : Type} (block : List (Stmt Op)) : List (Stmt Op) :=
  let refs := block.flatMap stmtRefs
  pruneLinkerStmts (refs.contains ·) block

/-- Remove dead `linkersymbol` bindings from a whole object tree. -/
def pruneLinkerObjectTree {Op : Type} (o : Object Op) : Object Op :=
  let refs := objectRefs o
  pruneLinkerObject (refs.contains ·) o

/-- Parse and compile a complete Yul source program to executable EVM bytecode,
using the documented compatibility parser when the verified parser does not
apply. Hint builtins (`memoryguard`) are desugared for ordinary candidates and
retained as reservation authority for the final spilling fallback. Provably
dead `linkersymbol` bindings are dropped before either path.

Both block- and object-rooted programs first run the full **normalization**
front-end (`Normalize.normalize`: disambiguate every declared name, then hoist
every function definition to the root — semantics-preserving for valid source
programs, `normalize_optimizerPipelineRounds_runEquiv`; its `SourceValid`
hypotheses are assumed of the input, see `Normalization/Normalize.lean` and
`Normalization/Disambiguate/Pass.lean` for the limitation), then run the
verified production pipeline:
simplification and propagation, bounded helper/call inlining with the
normalization needed to expose it, then dead pure/result-region elimination.
The object path applies the pipeline's resolution-stable mode to every code
block in the tree. -/
def compileSource (source : String) : Option ByteArray := do
  match parseSource source with
  | some (.block block) =>
      let raw := pruneLinkerBlock (decodeValueStmts block)
      let b := YulEvmCompiler.Optimizer.Normalize.normalize
        (D := YulSemantics.EVM.evmWithExternal YulSemantics.EVM.ExternalCalls.none
          YulSemantics.EVM.ExternalCreates.none)
        (raw.map desugarStmt)
      -- Preserve bytecode stability for programs the full pipeline can already
      -- compile. On stack pressure, first retry its verified smart layout;
      -- then retry the shallower one-round pipeline, with and without smart
      -- layout, before retaining the historical unoptimized fallback. Every
      -- choice is covered by its own correctness theorem.
      let optimized := (YulEvmCompiler.Optimizer.optimizerPipeline
        (calls := YulSemantics.EVM.ExternalCalls.none)
        (creates := YulSemantics.EVM.ExternalCreates.none)).run b
      let noRejoin := (YulEvmCompiler.Optimizer.optimizerPipelineNoRejoin
        (calls := YulSemantics.EVM.ExternalCalls.none)
        (creates := YulSemantics.EVM.ExternalCreates.none)).run b
      let light := (YulEvmCompiler.Optimizer.optimizerPipelineLight
        (calls := YulSemantics.EVM.ExternalCalls.none)
        (creates := YulSemantics.EVM.ExternalCreates.none)).run b
      let asm := YulEvmCompiler.compile optimized
        <|> YulEvmCompiler.compile
          (YulEvmCompiler.Optimizer.stackLayoutBlock optimized)
        <|> YulEvmCompiler.compile noRejoin
        <|> YulEvmCompiler.compile
          (YulEvmCompiler.Optimizer.stackLayoutBlock noRejoin)
        <|> YulEvmCompiler.compile light
        <|> YulEvmCompiler.compile
          (YulEvmCompiler.Optimizer.stackLayoutBlock light)
        <|> YulEvmCompiler.compile b
        <|> (match YulEvmCompiler.Optimizer.MemorySpillSelect.spillBlock? raw with
          | some spilled =>
              -- The spilled program is ordinary Yul; give the optimizer a
              -- chance before compiling it verbatim.
              let spilledOpt := (YulEvmCompiler.Optimizer.optimizerPipeline
                (calls := YulSemantics.EVM.ExternalCalls.none)
                (creates := YulSemantics.EVM.ExternalCreates.none)).run
                  (YulEvmCompiler.Optimizer.Normalize.normalize
                    (D := YulSemantics.EVM.evmWithExternal
                      YulSemantics.EVM.ExternalCalls.none
                      YulSemantics.EVM.ExternalCreates.none)
                    spilled.block)
              YulEvmCompiler.compile spilledOpt
                <|> YulEvmCompiler.compile spilled.block
          | none => none)
      return YulEvmCompiler.assemble (← asm)
  | some (.object o) =>
      let raw := pruneLinkerObjectTree (decodeValueObject o)
      let o := YulEvmCompiler.Optimizer.Normalize.normalizeObject
        (D := YulSemantics.EVM.evmWithExternal YulSemantics.EVM.ExternalCalls.none
          YulSemantics.EVM.ExternalCreates.none)
        (desugarObject raw)
      let optimized := YulEvmCompiler.Optimizer.optimizerPipelineObject
        (calls := YulSemantics.EVM.ExternalCalls.none)
        (creates := YulSemantics.EVM.ExternalCreates.none) o
      let optimizedLayout :=
        YulEvmCompiler.Optimizer.stackLayoutObject optimized
      let noRejoin := YulEvmCompiler.Optimizer.optimizerPipelineObjectNoRejoin
        (calls := YulSemantics.EVM.ExternalCalls.none)
        (creates := YulSemantics.EVM.ExternalCreates.none) o
      let light := YulEvmCompiler.Optimizer.optimizerPipelineObjectLight
        (calls := YulSemantics.EVM.ExternalCalls.none)
        (creates := YulSemantics.EVM.ExternalCreates.none) o
      let layout ← YulEvmCompiler.compileObject optimized
        <|> YulEvmCompiler.compileObject optimizedLayout
        <|> YulEvmCompiler.compileObject noRejoin
        <|> YulEvmCompiler.compileObject
          (YulEvmCompiler.Optimizer.stackLayoutObject noRejoin)
        <|> YulEvmCompiler.compileObject light
        <|> YulEvmCompiler.compileObject
          (YulEvmCompiler.Optimizer.stackLayoutObject light)
        <|> YulEvmCompiler.compileObject o
        <|> (match YulEvmCompiler.Optimizer.MemorySpillSelect.spillObjectWithFallback
              raw optimized with
          | some spilled =>
              if spilled.selected = 0 then none
              else
                -- The spilled tree is ordinary Yul (guards resolved); give the
                -- optimizer a chance before compiling it verbatim. This is the
                -- only path large spill-only objects (PoolSwap) reach, so
                -- without it they never see the optimizer at all.
                let spilledOpt := YulEvmCompiler.Optimizer.optimizerPipelineObject
                  (calls := YulSemantics.EVM.ExternalCalls.none)
                  (creates := YulSemantics.EVM.ExternalCreates.none)
                  (YulEvmCompiler.Optimizer.Normalize.normalizeObject
                    (D := YulSemantics.EVM.evmWithExternal
                      YulSemantics.EVM.ExternalCalls.none
                      YulSemantics.EVM.ExternalCreates.none)
                    spilled.object)
                YulEvmCompiler.compileObject spilledOpt
                  <|> YulEvmCompiler.compileObject spilled.object
          | none => none)
      return ByteArray.mk layout.code.toArray
  | none => none

end YulParser
