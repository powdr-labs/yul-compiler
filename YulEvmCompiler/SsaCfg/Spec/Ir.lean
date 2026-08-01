import YulSemantics.Dialect.EVM
set_option warningAsError true
/-!
# YulEvmCompiler.SsaCfg.Spec.Ir

The **`yul-ssa-cfg` dialect**: an SSA control-flow graph over the EVM Yul
operation set. See `YulEvmCompiler/SsaCfg/DESIGN.md` for the design rationale.

Shape:

* Values are numeric ids (`ValId`), each defined exactly once (single
  assignment — *checked* by `wfCheck`, not tracked by proofs, following the
  repo's `Asm.wfCheck` precedent).
* Basic blocks take **block arguments** (`params`) instead of φ-nodes: a
  control-flow edge (`jump`/`branch` target) carries the argument values it
  passes, so the parallel-copy semantics of the edge is explicit in the
  terminator — the shape both the semantics rule and the edge-shuffling code
  generator want.
* Instructions are `const`, a Yul built-in application (`op`, which may read
  and write the machine state and may halt — effects come from the dialect's
  own `effects` table), and a user-function `call`.
* Terminators are `jump`, two-way `branch`, function `ret`, and `halt` for
  the always-halting built-ins (`stop`/`return`/`revert`/`invalid`/
  `selfdestruct`). Yul's structured control flow (`if`/`switch`/`for`/
  `break`/`continue`/`leave`) is compiled away by construction
  (`SsaCfg/OfYul.lean`); switches become branch chains with explicit `eq`
  instructions. The CFG is reducible by construction.
* A `Func` is a self-contained SSA unit (Yul functions cannot see caller
  locals). `nrets` is the declared return arity; every `ret` carries exactly
  that many values (checked by `wfCheck`).
-/

namespace YulEvmCompiler.SsaCfg

open YulSemantics.EVM (U256 Op)

/-- An SSA value id. Defined exactly once (checked, not proved). -/
abbrev ValId := Nat

/-- A basic-block id: an index into the enclosing function's `blocks`. -/
abbrev BlockId := Nat

/-- A function id: an index into the program's `funcs`. -/
abbrev FuncId := Nat

/-- An SSA instruction. -/
inductive Instr
  /-- `dst ← v` — a word constant. -/
  | const (dst : ValId) (v : U256)
  /-- `dsts ← yop(args)` — a Yul built-in. May read/write the machine state
  and may halt (dialect `effects`); `dsts` is `[]` for value-less built-ins
  and a singleton otherwise (EVM built-ins return at most one word). -/
  | op (dsts : List ValId) (yop : Op) (args : List ValId)
  /-- `dsts ← f(args)` — a user-defined Yul function call. -/
  | call (dsts : List ValId) (f : FuncId) (args : List ValId)
  deriving Repr, DecidableEq, Inhabited

/-- A control-flow edge: the target block and the arguments passed to its
`params`. -/
structure Edge where
  target : BlockId
  args : List ValId
  deriving Repr, DecidableEq, Inhabited

/-- A block terminator. -/
inductive Term
  /-- Unconditional transfer along `e`. -/
  | jump (e : Edge)
  /-- Two-way branch on `cond`: nonzero → `t`, zero → `f`. -/
  | branch (cond : ValId) (t f : Edge)
  /-- Return from the enclosing function with `vals` (main "returns" `[]`,
  which is Yul's `.normal` fall-through). -/
  | ret (vals : List ValId)
  /-- An always-halting built-in (`stop`/`return`/`revert`/`invalid`/
  `selfdestruct`) applied to `args`. -/
  | halt (yop : Op) (args : List ValId)
  deriving Repr, DecidableEq, Inhabited

/-- A basic block: parameters (the block-argument form of φ-nodes), a
straight-line instruction body, and a terminator. -/
structure Block where
  params : List ValId
  instrs : List Instr
  term : Term
  deriving Repr, DecidableEq, Inhabited

/-- An SSA function: entry parameters, declared return arity, entry block,
and the block array. -/
structure Func where
  params : List ValId
  nrets : Nat
  entry : BlockId
  blocks : Array Block
  deriving Repr, Inhabited

/-- A whole program: the top-level `main` (no params, no returns) plus the
hoisted user functions. `Instr.call` indexes `funcs`. -/
structure Prog where
  main : Func
  funcs : Array Func
  deriving Repr, Inhabited

namespace Instr

/-- Values defined by an instruction. -/
def defs : Instr → List ValId
  | const d _ => [d]
  | op ds _ _ => ds
  | call ds _ _ => ds

/-- Values used by an instruction. -/
def uses : Instr → List ValId
  | const _ _ => []
  | op _ _ as => as
  | call _ _ as => as

end Instr

namespace Term

/-- Values used by a terminator (edge arguments included). -/
def uses : Term → List ValId
  | jump e => e.args
  | branch c t f => c :: t.args ++ f.args
  | ret vs => vs
  | halt _ as => as

/-- The outgoing edges of a terminator. -/
def edges : Term → List Edge
  | jump e => [e]
  | branch _ t f => [t, f]
  | ret _ => []
  | halt _ _ => []

end Term

/-! ## Well-formedness

Following the `Asm.wfCheck` precedent, SSA well-formedness is a decidable
check run by the construction and by every pass boundary, so proofs read
single-assignment/def-before-use facts off a successful check instead of
threading freshness through the construction. -/

/-- All values defined by a function: params, block params, instruction
defs, in a fixed traversal order. -/
def Func.allDefs (f : Func) : List ValId :=
  f.params ++ f.blocks.toList.flatMap fun b =>
    b.params ++ b.instrs.flatMap Instr.defs

/-- The decidable per-function well-formedness check:

1. **single assignment** — `allDefs` has no duplicates;
2. **edges in range**, with argument counts matching the target's `params`;
3. **`ret` arity** — every `ret` carries `nrets` values;
4. **entry in range**, and the entry block takes exactly the function's
   `params` (by convention the entry block's `params` are empty and the
   function's `params` are in scope throughout — we check entry params
   empty);
5. built-in `dsts` arity ≤ 1.

Dominance ("every use is dominated by its definition") is deliberately *not*
checked structurally here; the semantics gets stuck on an unbound `ValId`
read (`Regs` lookup fails), which is exactly how the Yul semantics treats
unbound identifiers, and the construction only ever emits dominated uses.
The codegen re-checks what it needs (a value must be on the tracked symbolic
stack to be materialized). -/
def Func.wfCheck (f : Func) (nFuncs : Nat) : Bool :=
  let defs := f.allDefs
  defs.Nodup
  && f.entry < f.blocks.size
  && (match f.blocks[f.entry]? with
      | some b => b.params.isEmpty
      | none => false)
  && f.blocks.all fun b =>
    (match b.term with
     | .ret vs => vs.length = f.nrets
     | _ => true)
    && (b.term.edges.all fun e =>
        match f.blocks[e.target]? with
        | some tb => e.args.length = tb.params.length
        | none => false)
    && b.instrs.all fun i =>
      match i with
      | .op ds _ _ => ds.length ≤ 1
      | .call _ g _ => g < nFuncs
      | _ => true

/-- Whole-program well-formedness: `main` takes and returns nothing, and
every function checks. -/
def Prog.wfCheck (P : Prog) : Bool :=
  P.main.params.isEmpty && P.main.nrets = 0
  && P.main.wfCheck P.funcs.size
  && P.funcs.all (·.wfCheck P.funcs.size)

end YulEvmCompiler.SsaCfg
