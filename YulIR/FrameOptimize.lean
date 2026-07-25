import YulIR.FramePasses
import YulIR.Effects
import YulSemantics.Dialect.EVM

set_option warningAsError true
/-!
# YulIR.FrameOptimize — the frame-IR optimization pipeline

Ports the remaining passes onto the `Fin n`-frame IR and composes them, so the experimental
optimizer runs *on the frame IR* (the representation pass-soundness is proved against). Passes:

* `simplify`   — local constant folding (via the dialect's own `stepOp`) + algebraic identities;
* `valueNumber`— constant/copy propagation + CSE (`YulIR.FramePasses`);
* `structural` — dead `if 0`, `if 1`→splice, constant-`switch` selection, empty removal, and
  unreachable-code elimination (the rewrites proved sound in `YulIR.FrameSound`);
* `deadCode`   — remove pure writes to slots never read (protecting a function's return slots),
  to a fixpoint.

`optimize : Program → Program` runs `valueNumber → simplify → structural → deadCode` twice over
`main` and every function body. Every pass is `Block n → Block n` (frame-preserving), so no
weakening is needed. Correctness is validated by the interpreter/behaviour checks; soundness proofs
land incrementally in `YulIR.FrameSound`.
-/

namespace YulIR.FinFrame

open YulSemantics (Ident Literal)
open YulSemantics.EVM (litValue stepOp)
open YulSemantics.EVM

/-! ### Simplify — constant folding + identities -/

/-- Literal value of an atom, if literal. -/
def Atom.litVal? : Atom n → Option Literal
  | .lit l  => some l
  | .slot _ => none

/-- All operands as literals, or `none`. -/
def allLits (as : List (Atom n)) : Option (List Literal) := as.mapM Atom.litVal?

/-- Is the atom a literal equal to `k`? -/
def Atom.isVal (a : Atom n) (k : Nat) : Bool :=
  match a with | .lit l => litValue l == BitVec.ofNat 256 k | .slot _ => false

/-- Evaluate a pure built-in on literal operands via the dialect's own evaluator. -/
def evalConst (op : Op) (lits : List Literal) : Option Literal :=
  match stepOp op (lits.map litValue) EvmState.init with
  | some (.ok [r] _) => some (.number r.toNat)
  | _ => none

/-- Algebraic identities on a pure built-in with atom operands. -/
def simplifyIdentity (op : Op) (args : List (Atom n)) (orig : Rhs n) : Rhs n :=
  let z (a : Atom n) : Bool := a.isVal 0
  let o (a : Atom n) : Bool := a.isVal 1
  let zero : Atom n := .lit (.number 0)
  match op, args with
  | .add, [a, b] => if z a then .atom b else if z b then .atom a else orig
  | .sub, [a, b] => if z b then .atom a else if a == b then .atom zero else orig
  | .mul, [a, b] => if z a || z b then .atom zero else if o a then .atom b else if o b then .atom a else orig
  | .div, [a, b] => if z b then .atom zero else if o b then .atom a else orig
  | .or,  [a, b] => if z a then .atom b else if z b then .atom a else if a == b then .atom a else orig
  | .and, [a, b] => if z a || z b then .atom zero else if a == b then .atom a else orig
  | .xor, [a, b] => if z a then .atom b else if z b then .atom a else if a == b then .atom zero else orig
  | .shl, [a, b] => if z a then .atom b else if z b then .atom zero else orig
  | .shr, [a, b] => if z a then .atom b else if z b then .atom zero else orig
  | .sar, [a, b] => if z a then .atom b else if z b then .atom zero else orig
  | _, _ => orig

/-- Simplify one rhs: fold pure literal ops, else apply identities. -/
def simplifyRhs : Rhs n → Rhs n
  | .atom a       => .atom a
  | .call fn args => .call fn args
  | .builtin op args =>
      let orig : Rhs n := .builtin op args
      if ! Op.isPure op then orig
      else match allLits args with
        | some lits => match evalConst op lits with
            | some l => .atom (.lit l)
            | none   => simplifyIdentity op args orig
        | none => simplifyIdentity op args orig

mutual
partial def simplifyStmt : Stmt n → Stmt n
  | .write d rhs      => .write d (simplifyRhs rhs)
  | .writeMany ds rhs => .writeMany ds (simplifyRhs rhs)
  | .effect rhs       => .effect (simplifyRhs rhs)
  | .cond c body      => .cond c (simplifyBlock body)
  | .switch c cs df   => .switch c (cs.map (fun p => (p.1, simplifyBlock p.2))) (df.map simplifyBlock)
  | .loop post body   => .loop (simplifyBlock post) (simplifyBlock body)
  | s                 => s
partial def simplifyBlock : Block n → Block n
  | []      => []
  | s :: ss => simplifyStmt s :: simplifyBlock ss
end

def simplify (b : Block n) : Block n := simplifyBlock b

/-! ### Structural simplification -/

def Atom.isZeroLit : Atom n → Bool | .lit l => litValue l == 0 | .slot _ => false
def Atom.isNonzeroLit : Atom n → Bool | .lit l => litValue l != 0 | .slot _ => false

/-- The block a constant `switch` takes. -/
def selectLit (k : Literal) (cases : List (Literal × Block n)) (dflt : Option (Block n)) : Block n :=
  match cases.find? (fun p => litValue p.1 == litValue k) with
  | some p => p.2
  | none   => dflt.getD []

/-! Structural simplification. Non-`partial` (structurally recursive on the nested `Stmt`/`Block`),
so it has equation lemmas and a functional-induction principle — the soundness proof in
`YulIR.FrameStructuralSound` inducts on it. The `switch`-case and default recursion is factored
through the explicit list helpers `structuralCases`/`structuralDflt` rather than `List.map`, so the
recursion stays structural. -/
mutual
def structuralStmt : Stmt n → List (Stmt n)
  | .cond c body =>
      let b' := structuralBlock body
      if c.isZeroLit || b'.isEmpty then []
      else if c.isNonzeroLit then b'                     -- always taken ⇒ splice
      else [.cond c b']
  | .switch c cs df =>
      let cs' := structuralCases cs
      let df' := structuralDflt df
      match c with
      | .lit k => selectLit k cs' df'                    -- constant scrutinee ⇒ splice one branch
      | _      => [.switch c cs' df']
  | .loop post body => [.loop (structuralBlock post) (structuralBlock body)]
  | s => [s]
def structuralBlock : Block n → Block n
  | []      => []
  | s :: ss => structuralStmt s ++ structuralBlock ss
def structuralCases : List (Literal × Block n) → List (Literal × Block n)
  | []             => []
  | (l, b) :: rest => (l, structuralBlock b) :: structuralCases rest
def structuralDflt : Option (Block n) → Option (Block n)
  | none   => none
  | some b => some (structuralBlock b)
end

/-- Halting built-ins (control never continues after them). -/
def haltingOp : Op → Bool
  | .stop | .ret | .revert | .invalid | .selfdestruct => true
  | _ => false

def isTerminator : Stmt n → Bool
  | .«break» | .«continue» | .leave => true
  | .effect (.builtin op _)         => haltingOp op
  | _                               => false

mutual
def dropUnreachableStmt : Stmt n → Stmt n
  | .cond c b       => .cond c (dropUnreachableBlock b)
  | .switch c cs df => .switch c (dropUnreachableCases cs) (dropUnreachableDflt df)
  | .loop post body => .loop (dropUnreachableBlock post) (dropUnreachableBlock body)
  | s               => s
def dropUnreachableBlock : Block n → Block n
  | []      => []
  | s :: ss => let s' := dropUnreachableStmt s
               if isTerminator s' then [s'] else s' :: dropUnreachableBlock ss
def dropUnreachableCases : List (Literal × Block n) → List (Literal × Block n)
  | []             => []
  | (l, b) :: rest => (l, dropUnreachableBlock b) :: dropUnreachableCases rest
def dropUnreachableDflt : Option (Block n) → Option (Block n)
  | none   => none
  | some b => some (dropUnreachableBlock b)
end

def structural (b : Block n) : Block n := dropUnreachableBlock (structuralBlock b)

/-! ### Dead-code elimination (unused pure writes) -/

def atomSlot? : Atom n → Option (Fin n) | .slot i => some i | .lit _ => none
def rhsReads : Rhs n → List (Fin n)
  | .atom a       => (atomSlot? a).toList
  | .builtin _ as => as.filterMap atomSlot?
  | .call _ as    => as.filterMap atomSlot?

mutual
partial def stmtReads : Stmt n → List (Fin n)
  | .write _ rhs      => rhsReads rhs
  | .writeMany _ rhs  => rhsReads rhs
  | .effect rhs       => rhsReads rhs
  | .cond c body      => (atomSlot? c).toList ++ blockReads body
  | .switch c cs df   => (atomSlot? c).toList ++ cs.flatMap (fun p => blockReads p.2) ++ (df.map blockReads).getD []
  | .loop post body   => blockReads post ++ blockReads body
  | _                 => []
partial def blockReads : Block n → List (Fin n)
  | []      => []
  | s :: ss => stmtReads s ++ blockReads ss
end

/-- A statement that produces no observable effect and whose result is unused. -/
def isDead (reads prot : List (Fin n)) : Stmt n → Bool
  | .write d rhs => rhsPure rhs && ! reads.contains d && ! prot.contains d
  | .effect rhs  => rhsPure rhs
  | _            => false

mutual
partial def dceBlock (reads prot : List (Fin n)) : Block n → Block n
  | []      => []
  | s :: ss => if isDead reads prot s then dceBlock reads prot ss
               else dceStmt reads prot s :: dceBlock reads prot ss
partial def dceStmt (reads prot : List (Fin n)) : Stmt n → Stmt n
  | .cond c b       => .cond c (dceBlock reads prot b)
  | .switch c cs df => .switch c (cs.map (fun p => (p.1, dceBlock reads prot p.2))) (df.map (dceBlock reads prot))
  | .loop post body => .loop (dceBlock reads prot post) (dceBlock reads prot body)
  | s               => s
end

-- Total statement count, for fixpoint detection.
mutual
partial def stmtCount : Stmt n → Nat
  | .cond _ b       => 1 + blockCount b
  | .switch _ cs df => 1 + cs.foldl (fun a p => a + blockCount p.2) 0 + (df.map blockCount).getD 0
  | .loop post body => 1 + blockCount post + blockCount body
  | _               => 1
partial def blockCount : Block n → Nat
  | []      => 0
  | s :: ss => stmtCount s + blockCount ss
end

/-- Dead-code elimination to a fixpoint (bounded), protecting `prot` (a function's return slots). -/
partial def deadCode (prot : List (Fin n)) : Nat → Block n → Block n
  | 0,     b => b
  | fuel+1, b =>
    let b' := dceBlock (blockReads b) prot b
    if blockCount b' == blockCount b then b' else deadCode prot fuel b'

/-! ### The pipeline -/

/-- One optimization round over a block. `frozen` = the params+returns whose writes are
reassignments of an initial value: excluded from value-tracking and protected from dead-code. -/
def optRoundBody (frozen : List (Fin n)) (b : Block n) : Block n :=
  deadCode frozen 8 (structural (simplify (valueNumber frozen b)))

/-- Optimize a program: two rounds over `main` and every function body. A function's params+returns
are its `frozen` set; `main` has none. -/
def optimize (p : Program) : Program :=
  { functions := Std.HashMap.ofList (p.functions.toList.map (fun q =>
      let frozen := q.2.params ++ q.2.rets
      (q.1, { q.2 with body := optRoundBody frozen (optRoundBody frozen q.2.body) })))
    mainSlots := p.mainSlots
    main      := optRoundBody [] (optRoundBody [] p.main) }

end YulIR.FinFrame
