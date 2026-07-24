import YulIR.Ast

/-!
# YulIR.Effects — purity classification for IR right-hand sides

Reuses the dialect's own effect classifier (`YulSemantics.EVM.effects`, which is proved
to soundly over-approximate the built-in semantics) to decide when an `Rhs` is pure.

A *pure* rhs is a total function of its operands with no state read/write and no halt —
the class that common-subexpression elimination and dead-code elimination can move,
duplicate, or drop freely. User calls are conservatively treated as impure here; a
whole-program effect summary for user functions is future work.
-/

namespace YulIR

open YulSemantics.EVM (Op effects)

/-- Is a built-in `op` pure (no reads, no writes, no halt)? -/
def Op.isPure (op : Op) : Bool :=
  let e := effects op
  !e.reads && !e.writes && !e.halts

/-- Is an rhs pure? Atoms are pure; built-ins defer to `Op.isPure`; user calls are
conservatively impure (no effect summary yet). -/
def Rhs.isPure : Rhs → Bool
  | .atom _        => true
  | .builtin op _  => Op.isPure op
  | .call _ _      => false

end YulIR
