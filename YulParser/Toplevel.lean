import YulParser.Obj

/-!
# YulParser.Toplevel

The entry point `parseYul` and the main correctness theorem: whenever the
parser accepts a source string, re-printing the resulting AST yields a string
that is whitespace-equivalent to the original (`Approx`, i.e. equal after
deleting all whitespace).

Fuel is instantiated to the input length, which bounds the total nesting depth
(objects, statement blocks, and call arguments all consume the shared fuel), so
no well-formed program is rejected for lack of fuel.
-/

namespace YulParser

/-- A list is all-whitespace exactly when deleting whitespace empties it. -/
theorem fws_all_ws (cs : List Char) (h : cs.all isWs = true) : fws cs = [] := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨hc, hcs⟩ := h
    simp only [fws_cons_simp, hc, if_pos, ih hcs, List.nil_append]

/-- Parse a full Yul source string into an object. Succeeds only if the entire
input is consumed up to trailing whitespace. -/
def parseYul (s : String) : Option Obj :=
  let cs := s.toList
  match pObjF cs.length cs with
  | some (o, rest) => if rest.all isWs then some o else none
  | none => none

/-- **Round-trip soundness.** If `parseYul` accepts `s` and returns `o`, then
printing `o` reproduces `s` up to whitespace. -/
theorem parseYul_roundtrip (s : String) (o : Obj) (h : parseYul s = some o) :
    Approx (printObj o) s.toList := by
  unfold parseYul at h
  simp only at h
  split at h
  · rename_i o' rest heq
    split at h
    · rename_i hrest
      simp only [Option.some.injEq] at h; subst h
      have hsound := pObjF_sound s.toList.length s.toList o' rest heq
      show fws (printObj o') = fws s.toList
      rw [← hsound, fws_all_ws rest hrest, List.append_nil]
    · exact absurd h (by simp)
  · exact absurd h (by simp)

end YulParser
