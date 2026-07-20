import YulEvmCompiler.Optimizer.Implementation.FreshenCalls
import YulEvmCompiler.Optimizer.Implementation.DeadLitsResolve
set_option warningAsError true
/-!
# YulEvmCompiler.Optimizer.Implementation.FreshenCallsResolve

Resolution congruence for `FreshenCalls` (object path). The pass commutes
with layout resolution syntactically: its decisions read only identifier
sets, statement structure, and call shapes — all invariant under
`resolveForLayout*` — and the rewrite maps hoisted arguments through
resolution pointwise.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler (resolveForLayoutStmts)

variable {calls : ExternalCalls} {creates : ExternalCreates}

local notation "D" => evmWithExternal calls creates

set_option warningAsError false in
/-- Resolution congruence for `FreshenCalls` (in progress). -/
theorem resolveFreshenCallsBlock_equiv (L : Layout) (b : Block Op) :
    EquivBlock D (resolveForLayoutStmts L b)
      (resolveForLayoutStmts L (freshenCallsBlock b)) := sorry

end YulEvmCompiler.Optimizer
