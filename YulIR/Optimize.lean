import YulIR.Object
import YulIR.Simplify
import YulIR.Uniquify
import YulIR.ValueNumber
import YulIR.Structural
import YulIR.DeadStore
import YulIR.DeadCode

set_option warningAsError true
/-!
# YulIR.Optimize — the IR optimization pipeline

Composes the IR→IR passes. Order:

1. `uniquify`      — make variable declarations globally unique (enables sound value tracking);
2. `valueNumber`   — constant/copy propagation + folding/identities + CSE;
3. `deadCode`      — remove the now-unused pure bindings;

steps 2–3 iterated once more, since DCE can expose further propagation/CSE. Every step is a
behaviour-preserving IR→IR transformation (validated by the interpreter check in
`YulIR.CheckBaseline`); the benchmark's `irOpt` column measures their effect.
-/

namespace YulIR

/-- One optimization round over a whole program: value numbering, structural simplification,
dead-store and dead-code elimination (each applied to every function body and `main`). -/
def optRound (p : Program) : Program :=
  deadCodeProgram (deadStoreProgram (structuralProgram (valueNumberProgram p)))

/-- The IR optimization pipeline on a `Program`. -/
def optimize (p : Program) : Program := optRound (optRound (uniquifyProgram p))

/-- The IR optimization pipeline on an object (optimizes its program and every sub-object). -/
partial def optimizeObject : Object → Object
  | .mk name program subs data => .mk name (optimize program) (subs.map optimizeObject) data

end YulIR
