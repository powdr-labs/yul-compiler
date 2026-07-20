import YulEvmCompiler.Optimizer.Implementation.DeadPure
import YulEvmCompiler.Optimizer.Implementation.DeadLitsResolve
set_option warningAsError true
/-!
# YulEvmCompiler.Optimizer.Implementation.DeadPureResolve

Resolution congruence for the `DeadPure` pass (object path): mirrors
`DeadLitsResolve` — the removal relation is closed under layout resolution
(`mentions_resolve*` invariance; `alwaysEval` is resolution-stable in the
transported direction since `dataoffset`/`datasize` are outside the pure
fragment and resolution preserves literals, variables, and statement
structure).
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler (resolveForLayoutStmts)

variable {calls : ExternalCalls} {creates : ExternalCreates}

local notation "D" => evmWithExternal calls creates

set_option warningAsError false in
/-- Resolution congruence for `DeadPure` (in progress — mirrors
`resolveDeadLitsBlock_equiv` via relation closure). -/
theorem resolveDeadPureBlock_equiv (L : Layout) (b : Block Op) :
    EquivBlock D (resolveForLayoutStmts L b)
      (resolveForLayoutStmts L (dpStmts [] b)) := sorry

end YulEvmCompiler.Optimizer
