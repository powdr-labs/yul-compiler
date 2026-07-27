import YulEvmCompiler.Optimizer.Implementation.FreshenCalls
/-!
# Block flattening (scaffold splicing)

Statement inlining (`InlineCalls`) wraps every inlined body in nested blocks:

```yul
let x1789 { let x1256 { mstore(0, x1788) mstore(32, 8) x1256 := keccak256(0, 64) } x1789 := x1256 }
```

Six rounds of this leave the hot loops as chains of readback regions 4–5
blocks deep.  The nesting is the structural blocker for every level-local
cleanup: `CoalesceCopies` and `RejoinPairs` only see adjacent same-level
pairs, `Propagate`/`StorageForward` facts die with each block's locals, and
available-value reuse cannot connect two identical groups whose carriers are
block-scoped.  solc's optimized output is flat.

This pass splices a bare `.block ss` statement into its parent sequence when

* `ss` declares no top-level functions (splicing would rehoist them into the
  parent scope); and
* every top-level binder of `ss` either does not occur anywhere else in the
  parent sequence, or can be **renamed** to a globally fresh name (the binder
  is not redeclared anywhere inside the block, so the rename is
  capture-free; function bodies cannot reference outer variables, so the
  rename does not descend into `funDef`s).

Renaming is needed because `InlineCalls` duplicates callee binder names at
every inline site: two sibling inlined copies of the same helper declare the
same locals, and only one of them could otherwise be spliced.  Fresh names
use the `FreshenCalls` scheme: a prefix (`fl<k>_`) no program identifier
starts with, plus a counter.

Semantically, splicing extends each promoted binder's lifetime from the inner
block's `restore` to the parent block's: the spliced program carries extra
bindings through the remainder of the parent sequence, which never mentions
them.  This is the `InsChain` frame argument of `CoalesceCopies`/`DeadPure`
(multi-insertion, erased by the enclosing block's `restore`, halts included).
The rename is a block-local alpha-conversion.

The lifetime extension is *not* free: promoted binders stay on the operand
stack until the parent block exits.  The pass is therefore only useful
together with the cleanup passes that consume the flattened residue
(`FuseDeclAssign`, `CoalesceCopies`, `RejoinPairs`, `DeadPure`), and
`compileSource`'s fallback ladder retains no-flatten candidates for objects
this pushes over the stack frontier.
-/

namespace YulEvmCompiler.Optimizer.Flatten

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler.Optimizer (exprIdents argsIdents stmtIdents stmtsIdents
  casesIdents dfltIdents freshPrefix)

/-! ### Occurrence and redeclaration scans -/

/-- Top-level binders of a statement sequence (`let`-declared names only;
`funDef`-free blocks are the only splice candidates). -/
def topDecls : List (Stmt Op) → List Ident
  | [] => []
  | .letDecl xs _ :: rest => xs ++ topDecls rest
  | _ :: rest => topDecls rest

/-- Does the sequence declare a function at its top level? -/
def hasTopFunDef : List (Stmt Op) → Bool
  | [] => false
  | .funDef _ _ _ _ :: _ => true
  | _ :: rest => hasTopFunDef rest

mutual
/-- Is `x` (re)declared anywhere in a statement, at any depth, excluding
`funDef` bodies (function bodies cannot reference outer variables, so a
declaration there never captures an outer rename)? -/
def redeclStmt (x : Ident) : Stmt Op → Bool
  | .block body => redeclStmts x body
  | .funDef _ _ _ _ => false
  | .letDecl xs _ => xs.contains x
  | .cond _ body => redeclStmts x body
  | .switch _ cases dflt => redeclCases x cases || redeclDflt x dflt
  | .forLoop init _ post body =>
      redeclStmts x init || redeclStmts x post || redeclStmts x body
  | _ => false

def redeclStmts (x : Ident) : List (Stmt Op) → Bool
  | [] => false
  | s :: rest => redeclStmt x s || redeclStmts x rest

def redeclCases (x : Ident) : List (Literal × Block Op) → Bool
  | [] => false
  | (_, b) :: rest => redeclStmts x b || redeclCases x rest

def redeclDflt (x : Ident) : Option (Block Op) → Bool
  | none => false
  | some b => redeclStmts x b
end

/-! ### Capture-free variable renaming (never descends into `funDef`s) -/

def renVar (x x' : Ident) (y : Ident) : Ident := if y = x then x' else y

mutual
def renExpr (x x' : Ident) : Expr Op → Expr Op
  | .lit l => .lit l
  | .var y => .var (renVar x x' y)
  | .builtin op args => .builtin op (renArgs x x' args)
  | .call f args => .call f (renArgs x x' args)

def renArgs (x x' : Ident) : List (Expr Op) → List (Expr Op)
  | [] => []
  | e :: rest => renExpr x x' e :: renArgs x x' rest
end

mutual
def renStmt (x x' : Ident) : Stmt Op → Stmt Op
  | .block body => .block (renStmts x x' body)
  | s@(.funDef _ _ _ _) => s
  | .letDecl xs rhs => .letDecl (xs.map (renVar x x')) (rhs.map (renExpr x x'))
  | .assign xs e => .assign (xs.map (renVar x x')) (renExpr x x' e)
  | .cond c body => .cond (renExpr x x' c) (renStmts x x' body)
  | .switch c cases dflt =>
      .switch (renExpr x x' c) (renCases x x' cases) (renDflt x x' dflt)
  | .forLoop init c post body =>
      .forLoop (renStmts x x' init) (renExpr x x' c)
        (renStmts x x' post) (renStmts x x' body)
  | .exprStmt e => .exprStmt (renExpr x x' e)
  | s => s

def renStmts (x x' : Ident) : List (Stmt Op) → List (Stmt Op)
  | [] => []
  | s :: rest => renStmt x x' s :: renStmts x x' rest

def renCases (x x' : Ident) : List (Literal × Block Op) → List (Literal × Block Op)
  | [] => []
  | (l, b) :: rest => (l, renStmts x x' b) :: renCases x x' rest

def renDflt (x x' : Ident) : Option (Block Op) → Option (Block Op)
  | none => none
  | some b => some (renStmts x x' b)
end

/-! ### The splice -/

/-- Rename the promoted binders of `body` that occur elsewhere in the parent
sequence (`clash`), producing the renamed statements. Declines (`none`) when a
clashing binder is redeclared inside the block (the rename would capture). -/
def renameClashes (P : String) (ctr : Nat) (clash : List Ident)
    (body : List (Stmt Op)) : Option (List (Stmt Op) × Nat) :=
  go clash body ctr
where
  go : List Ident → List (Stmt Op) → Nat → Option (List (Stmt Op) × Nat)
    | [], ss, c => some (ss, c)
    | x :: rest, ss, c =>
        if redeclStmts x ss then none
        else go rest (renStmts x s!"{P}{c}" ss) (c + 1)

/-- Splice pass over an already recursively-flattened sequence. `seen` is the
identifier list of the emitted prefix. Spliced statements were already
processed by their block's own sweep, so they are emitted as-is. -/
def spliceSeq (P : String) (seen : List Ident) :
    List (Stmt Op) → Nat → List (Stmt Op) × Nat
  | [], c => ([], c)
  | .block inner :: rest, c =>
      if hasTopFunDef inner then
        let (rest', c') := spliceSeq P (seen ++ stmtIdents (Stmt.block inner)) rest c
        (.block inner :: rest', c')
      else
        let others := seen ++ stmtsIdents rest
        let clash := (topDecls inner).filter others.contains
        match renameClashes P c clash inner with
        | some (inner', c') =>
            let (rest', c'') := spliceSeq P (seen ++ stmtsIdents inner') rest c'
            (inner' ++ rest', c'')
        | none =>
            let (rest', c') := spliceSeq P (seen ++ stmtIdents (Stmt.block inner)) rest c
            (.block inner :: rest', c')
  | s :: rest, c =>
      let (rest', c') := spliceSeq P (seen ++ stmtIdents s) rest c
      (s :: rest', c')


mutual

/-- Flatten inside one statement (children first). -/
def flStmt (P : String) : Stmt Op → Nat → Stmt Op × Nat
  | .block body, c => let (b, c) := flStmts P body c; (.block b, c)
  | .funDef n ps rs body, c =>
      let (b, c) := flStmts P body c; (.funDef n ps rs b, c)
  | .cond e body, c => let (b, c) := flStmts P body c; (.cond e b, c)
  | .switch e cases dflt, c =>
      let (cases, c) := flCases P cases c
      let (dflt, c) := flDflt P dflt c
      (.switch e cases dflt, c)
  | .forLoop init e post body, c =>
      -- `init` is left untouched (executed *and* hoisted; the usual
      -- convention). `post` and `body` are ordinary blocks.
      let (post, c) := flStmts P post c
      let (body, c) := flStmts P body c
      (.forLoop init e post body, c)
  | s, c => (s, c)

def flCases (P : String) : List (Literal × Block Op) → Nat →
    List (Literal × Block Op) × Nat
  | [], c => ([], c)
  | (l, b) :: rest, c =>
      let (b, c) := flStmts P b c
      let (rest, c) := flCases P rest c
      ((l, b) :: rest, c)

def flDflt (P : String) : Option (Block Op) → Nat → Option (Block Op) × Nat
  | none, c => (none, c)
  | some b, c => let (b, c) := flStmts P b c; (some b, c)

/-- Flatten a sequence: process every element, then splice bare blocks whose
promoted binders are (made) collision-free. `seen` accumulates the identifiers
of the already-emitted prefix. -/
def flStmts (P : String) (body : List (Stmt Op)) (c : Nat) :
    List (Stmt Op) × Nat :=
  let (body, c) := flEach P body c
  spliceSeq P [] body c

def flEach (P : String) : List (Stmt Op) → Nat → List (Stmt Op) × Nat
  | [], c => ([], c)
  | s :: rest, c =>
      let (s, c) := flStmt P s c
      let (rest, c) := flEach P rest c
      (s :: rest, c)

end

/-- The public transform. Chooses a fresh prefix once per root block; the
identity when none can be found (impossible in practice). -/
def flattenBlock (body : Block Op) : Block Op :=
  match freshPrefix (stmtsIdents body) with
  | some P => (flStmts P body 0).1
  | none => body

end YulEvmCompiler.Optimizer.Flatten
