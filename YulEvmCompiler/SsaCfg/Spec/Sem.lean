import YulEvmCompiler.AsmSem
import YulEvmCompiler.SsaCfg.Spec.Ir
set_option warningAsError true
/-!
# YulEvmCompiler.SsaCfg.Spec.Sem

The big-step relational semantics of the `yul-ssa-cfg` dialect.

A configuration executes the **rest of the current block** (remaining
instructions plus the terminator) of a function `f`, over a register file
`Regs : ValId → Option U256` and the *same* Yul-side machine state the
source and Asm semantics use (`YulSemantics.EVM.EvmState`). Built-ins step
by the same combined local/external relation as `AsmSem`
(`builtinWithExternal`), so calls/creates stay open-world and no per-op
agreement is owed here.

Design notes:

* **Registers persist across blocks** — SSA values are function-scoped and a
  use may sit in any block dominated by its definition; a jump *adds* the
  target's parameter bindings. Single assignment (checked by `wfCheck`)
  means the "update" never overwrites a live value.
* **Big-step over terminating executions** only, exactly like the source
  `Run`: a derivation exists iff the execution terminates in a `ret` or a
  halt. Unbound register reads are stuck, mirroring the source semantics'
  treatment of unbound identifiers.
* Function calls recurse within the same single indexed inductive (the
  `BigStep.lean` trick), from a **fresh** register file binding only the
  callee's parameters.
* The whole-program judgment `Run` executes `main` from an empty register
  file; a `ret []` is Yul's `.normal` fall-through, a halting built-in is
  `.halt` with the payload in the final state.
-/

namespace YulEvmCompiler.SsaCfg

open YulSemantics.EVM (U256 EvmState Op builtinWithExternal)
open YulSemantics (Outcome)

/-- The register file: partial map from SSA ids to words. -/
abbrev Regs := ValId → Option U256

namespace Regs

/-- The empty register file. -/
def empty : Regs := fun _ => none

/-- Bind one value. -/
def set (R : Regs) (x : ValId) (v : U256) : Regs :=
  fun y => if y = x then some v else R y

/-- Bind a parameter list to a value list (pointwise, same length assumed —
enforced by the rules' `length` premises). -/
def setMany (R : Regs) (xs : List ValId) (vs : List U256) : Regs :=
  (xs.zip vs).foldl (fun acc p => acc.set p.1 p.2) R

/-- Read a list of ids, all-or-nothing. -/
def getMany (R : Regs) (xs : List ValId) : Option (List U256) :=
  xs.mapM R

@[simp] theorem set_same (R : Regs) (x : ValId) (v : U256) : (R.set x v) x = some v := by
  simp [set]

@[simp] theorem set_other (R : Regs) {x y : ValId} (v : U256) (h : y ≠ x) :
    (R.set x v) y = R y := by
  simp [set, h]

@[simp] theorem getMany_nil (R : Regs) : R.getMany [] = some [] := rfl

theorem getMany_cons (R : Regs) (x : ValId) (xs : List ValId) :
    R.getMany (x :: xs) =
      (R x).bind fun v => (R.getMany xs).map fun vs => v :: vs := by
  simp only [getMany, List.mapM_cons]
  cases R x <;> cases hxs : xs.mapM R <;>
    simp_all [Option.bind, Option.map, bind, pure]

end Regs

/-- The result of executing (the rest of) a function body: a function-level
return with its values, or a halt (payload in the state). -/
inductive FRes
  | ret (vals : List U256) (st : EvmState)
  | halt (st : EvmState)

/-- The rest of the current block: remaining instructions, then the
terminator. -/
structure Rest where
  instrs : List Instr
  term : Term

/-- Big-step execution of the rest of a block within function `f` of
program `P`. `Exec P f R st rest res`: from register file `R` and machine
state `st`, executing `rest` produces `res`.

Jumps look up the target block in `f.blocks` and bind its parameters;
calls execute the callee's entry block from a fresh register file. -/
inductive Exec (P : Prog) [model : ExternalModel] :
    Func → Regs → EvmState → Rest → FRes → Prop
  /-- `const`: bind and continue. -/
  | const {f : Func} {R : Regs} {st : EvmState} {d : ValId} {v : U256}
      {is : List Instr} {t : Term} {res : FRes} :
      Exec P f (R.set d v) st ⟨is, t⟩ res →
      Exec P f R st ⟨.const d v :: is, t⟩ res
  /-- A built-in that returns: read the arguments, step the machine state by
  the dialect's combined relation, bind the results (`dsts.length = rets.length`
  so value-less built-ins bind nothing). -/
  | op {f : Func} {R : Regs} {st st' : EvmState} {ds : List ValId} {yop : Op}
      {as : List ValId} {args rets : List U256} {is : List Instr} {t : Term}
      {res : FRes} :
      R.getMany as = some args →
      builtinWithExternal model.calls model.creates .any yop args st (.ok rets st') →
      ds.length = rets.length →
      Exec P f (R.setMany ds rets) st' ⟨is, t⟩ res →
      Exec P f R st ⟨.op ds yop as :: is, t⟩ res
  /-- A built-in that halts mid-block (e.g. an out-of-bounds
  `returndatacopy`): the function's execution ends with the halt. -/
  | opHalt {f : Func} {R : Regs} {st st' : EvmState} {ds : List ValId}
      {yop : Op} {as : List ValId} {args : List U256} {is : List Instr}
      {t : Term} :
      R.getMany as = some args →
      builtinWithExternal model.calls model.creates .any yop args st (.halt st') →
      Exec P f R st ⟨.op ds yop as :: is, t⟩ (.halt st')
  /-- A user-function call that returns: execute the callee's entry block
  from a fresh register file binding its parameters. -/
  | call {f g : Func} {R : Regs} {st st' : EvmState} {ds as : List ValId}
      {fid : FuncId} {args rvals : List U256} {eb : Block}
      {is : List Instr} {t : Term} {res : FRes} :
      P.funcs[fid]? = some g →
      R.getMany as = some args →
      g.params.length = args.length →
      g.blocks[g.entry]? = some eb →
      Exec P g (Regs.empty.setMany g.params args) st ⟨eb.instrs, eb.term⟩
        (.ret rvals st') →
      ds.length = rvals.length →
      Exec P f (R.setMany ds rvals) st' ⟨is, t⟩ res →
      Exec P f R st ⟨.call ds fid as :: is, t⟩ res
  /-- A user-function call whose body halts: the halt propagates. -/
  | callHalt {f g : Func} {R : Regs} {st st' : EvmState} {ds as : List ValId}
      {fid : FuncId} {args : List U256} {eb : Block} {is : List Instr}
      {t : Term} :
      P.funcs[fid]? = some g →
      R.getMany as = some args →
      g.params.length = args.length →
      g.blocks[g.entry]? = some eb →
      Exec P g (Regs.empty.setMany g.params args) st ⟨eb.instrs, eb.term⟩
        (.halt st') →
      Exec P f R st ⟨.call ds fid as :: is, t⟩ (.halt st')
  /-- `jump`: bind the target's parameters to the edge arguments and execute
  the target block. -/
  | jump {f : Func} {R : Regs} {st : EvmState} {e : Edge} {tb : Block}
      {args : List U256} {res : FRes} :
      f.blocks[e.target]? = some tb →
      R.getMany e.args = some args →
      tb.params.length = args.length →
      Exec P f (R.setMany tb.params args) st ⟨tb.instrs, tb.term⟩ res →
      Exec P f R st ⟨[], .jump e⟩ res
  /-- `branch`, nonzero: take the true edge. -/
  | branchTrue {f : Func} {R : Regs} {st : EvmState} {c : ValId} {v : U256}
      {et ef : Edge} {tb : Block} {args : List U256} {res : FRes} :
      R c = some v → v ≠ 0 →
      f.blocks[et.target]? = some tb →
      R.getMany et.args = some args →
      tb.params.length = args.length →
      Exec P f (R.setMany tb.params args) st ⟨tb.instrs, tb.term⟩ res →
      Exec P f R st ⟨[], .branch c et ef⟩ res
  /-- `branch`, zero: take the false edge. -/
  | branchFalse {f : Func} {R : Regs} {st : EvmState} {c : ValId}
      {et ef : Edge} {tb : Block} {args : List U256} {res : FRes} :
      R c = some 0 →
      f.blocks[ef.target]? = some tb →
      R.getMany ef.args = some args →
      tb.params.length = args.length →
      Exec P f (R.setMany tb.params args) st ⟨tb.instrs, tb.term⟩ res →
      Exec P f R st ⟨[], .branch c et ef⟩ res
  /-- `ret`: read the return values; the function's execution ends. -/
  | ret {f : Func} {R : Regs} {st : EvmState} {xs : List ValId}
      {vals : List U256} :
      R.getMany xs = some vals →
      Exec P f R st ⟨[], .ret xs⟩ (.ret vals st)
  /-- `halt`: an always-halting built-in terminator. -/
  | halt {f : Func} {R : Regs} {st st' : EvmState} {yop : Op}
      {as : List ValId} {args : List U256} :
      R.getMany as = some args →
      builtinWithExternal model.calls model.creates .any yop args st (.halt st') →
      Exec P f R st ⟨[], .halt yop as⟩ (.halt st')

/-- Whole-program execution: run `main` from an empty register file. The
outcome mirrors the source `Run`'s top-level outcomes — `ret []` is a
`.normal` fall-through, a halt is `.halt` with the payload in `st'`. -/
inductive Run (P : Prog) [model : ExternalModel] :
    EvmState → EvmState → Outcome → Prop
  | normal {st st' : EvmState} {eb : Block} :
      P.main.blocks[P.main.entry]? = some eb →
      Exec P P.main Regs.empty st ⟨eb.instrs, eb.term⟩ (.ret [] st') →
      Run P st st' .normal
  | halt {st st' : EvmState} {eb : Block} :
      P.main.blocks[P.main.entry]? = some eb →
      Exec P P.main Regs.empty st ⟨eb.instrs, eb.term⟩ (.halt st') →
      Run P st st' .halt

end YulEvmCompiler.SsaCfg
