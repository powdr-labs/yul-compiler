import YulEvmCompiler.Compile
import YulEvmCompiler.SsaCfg.OfYul
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
-/

namespace YulEvmCompiler.SsaCfg

open YulSemantics.EVM (Op)

/-- Compile a top-level Yul block through the SSA-CFG dialect. -/
def compileViaSsa (prog : YulSemantics.Block Op) :
    Option (List YulEvmCompiler.Instr) := do
  let P ← ofBlock prog
  let asm ← ToAsm.emitProg P
  if !wfCheck asm then none else
  let opt := optimizeAsm asm
  if stackOK2 opt then lowerProg opt else none

end YulEvmCompiler.SsaCfg
