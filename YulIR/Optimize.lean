import YulIR.Object
import YulIR.Simplify
import YulIR.Uniquify
import YulIR.ValueNumber
import YulIR.DeadCode

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

/-- One value-numbering + dead-code round. -/
def optRound (b : Block) : Block := deadCode (valueNumber b)

/-- The IR optimization pipeline on a top-level block. -/
def optimize (b : Block) : Block := optRound (optRound (uniquify b))

/-- The IR optimization pipeline on an object (optimizes every code block). -/
partial def optimizeObject : Object → Object
  | .mk name code subs data => .mk name (optimize code) (subs.map optimizeObject) data

end YulIR
