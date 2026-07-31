import YulEvmCompiler.Compile
import YulEvmCompiler.SsaCfg.OfYul
import YulEvmCompiler.SsaCfg.Passes
import YulEvmCompiler.SsaCfg.ToAsm
set_option warningAsError true
/-!
# YulEvmCompiler.SsaCfg.Compile

The **SSA backend entry point**: Yul → `yul-ssa-cfg` → labeled `Asm` → EVM
bytecode, through the exact same final gates as the classic `compile` — the
Asm peephole (`optimizeAsm`), the stack-overflow certificate (`stackOK2`),
and label resolution (`lowerProg`) — so everything below the `Asm` layer
(Phase B, the certificate checker, the assembler) is shared, code and proof.

`compileViaSsa` is `Option`-valued like everything else in this repository:
any unsupported shape (construction rejection, shuffler depth overflow,
liveness anomaly, failed well-formedness or overflow check) yields `none`,
and the caller falls back to the classic backend. Rejection is never
miscompilation.

The SSA optimization pipeline (`SsaCfg/Passes.lean`) runs between the
construction and the code generator. Occasionally a *better* SSA program
emits *longer* code — removing a block parameter can change a block's
entry stack layout so that an edge needs an extra shuffle and a fused
conditional jump becomes an inverted branch — so both the optimized and
the unoptimized programs are emitted and the shorter result wins (ties go
to the optimized one).
-/

namespace YulEvmCompiler.SsaCfg

open YulSemantics.EVM (Op)

/-- Emit one SSA program through the shared final gates: `ToAsm`, `Asm`
well-formedness, the peephole, the overflow certificate, label
resolution. -/
def finishProg (P : Prog) : Option (List YulEvmCompiler.Instr) := do
  let asm ← ToAsm.emitProg P
  if !wfCheck asm then none else
  let opt := optimizeAsm asm
  if stackOK2 opt then lowerProg opt else none

/-- Compile a top-level Yul block through the SSA-CFG dialect. -/
def compileViaSsa (prog : YulSemantics.Block Op) :
    Option (List YulEvmCompiler.Instr) := do
  let P ← ofBlock prog
  match finishProg (optimizeProg P), finishProg P with
  | some a, some b => if a.length ≤ b.length then some a else some b
  | some a, none => some a
  | none, some b => some b
  | none, none => none

end YulEvmCompiler.SsaCfg
