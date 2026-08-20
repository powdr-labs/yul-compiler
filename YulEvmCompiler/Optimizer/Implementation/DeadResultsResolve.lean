import YulEvmCompiler.Optimizer.Implementation.DeadResults
import YulEvmCompiler.Optimizer.Implementation.DeadPureResolve
set_option warningAsError true

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler

variable {calls : ExternalCalls} {creates : ExternalCreates} {gasOracle : ExternalGas}

local notation "D" => evmWithExternal calls creates gasOracle

theorem resolveDeadResultsBlock_equiv (L : Layout) (b : Block Op) :
    EquivBlock D (resolveForLayoutStmts L b)
      (resolveForLayoutStmts L (drStmts [] b)) := by
  obtain ⟨b2, hrel⟩ := drStmts_rel [] b
  exact (hrel.resolve L).equivBlock

end YulEvmCompiler.Optimizer
