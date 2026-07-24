import YulIR.Object
import YulIR.Simplify

/-!
# YulIR.Optimize — the IR optimization pipeline (hook)

The single place IR→IR optimization passes are composed. It is currently the **identity**;
as passes land (CSE, inlining, redundant-store elimination, …) they are added here, and the
benchmark's `irOpt` column (`toYul ∘ optimize ∘ ofYul`) starts to diverge from `irNoOpt`
(`toYul ∘ ofYul`).

Keeping this hook here — rather than inlining `id` at call sites — is what lets the corpus
benchmark measure *optimization* effect (`irOpt` vs `irNoOpt`, which cancels IR→Yul
translation quality) separately from translation overhead (`irNoOpt` vs `current`).
-/

namespace YulIR

/-- The IR optimization pipeline on a top-level block. Currently: local expression
simplification (constant folding + algebraic identities). -/
def optimize (b : Block) : Block := simplifyBlock b

/-- The IR optimization pipeline on an object (optimizes every code block). -/
partial def optimizeObject : Object → Object
  | .mk name code subs data => .mk name (optimize code) (subs.map optimizeObject) data

end YulIR
