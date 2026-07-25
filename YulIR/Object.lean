import YulIR.OfYul
import YulIR.ToYul
import YulSemantics.Ast

set_option warningAsError true
/-!
# YulIR.Object — object-level translation

Real Yul compilation units are `Object`s: a named `code` block, nested sub-objects
(each a full object), and named `data` segments. The IR mirrors this structure so the
front-end and back-end translations go all the way from a Yul `Object` to an IR
`Object` and back.

The `code` block of each object (and recursively of every sub-object) is translated
with `YulIR.ofYul` / `YulIR.toYul`; data segments are opaque bytes and pass through
unchanged.
-/

namespace YulIR

open YulSemantics (Data)

/-- An IR object: a named `Program` (its lifted functions + `main` code), nested sub-objects, and
named data segments. Mirrors `YulSemantics.Object`, but the object's code is an IR `Program` — its
functions have been lifted out of the code block into `Program.functions`. -/
inductive Object
  | mk (name : String) (program : Program) (subObjects : List Object)
       (data : List (String × Data))
  deriving Inhabited

namespace Object

/-- The object's name. -/
def name : Object → String                 | .mk n _ _ _ => n
/-- The object's IR program (functions + main). -/
def program : Object → Program             | .mk _ p _ _ => p
/-- The object's nested sub-objects. -/
def subObjects : Object → List Object      | .mk _ _ s _ => s
/-- The object's named data segments. -/
def dataSegs : Object → List (String × Data) | .mk _ _ _ d => d

end Object

/-- Translate a Yul object into the IR (recursively through sub-objects). -/
partial def ofYulObject : YulSemantics.Object Op → Object
  | .mk name code subs data => .mk name (ofYul code) (subs.map ofYulObject) data

/-- Erase an IR object back to Yul (recursively through sub-objects). -/
partial def toYulObject : Object → YulSemantics.Object Op
  | .mk name program subs data => .mk name (toYul program) (subs.map toYulObject) data

end YulIR
