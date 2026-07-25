import YulIR.Frame
import YulIR.OfYul
import YulIR.ToYul
import YulIR.Analysis

set_option warningAsError true
/-!
# YulIR.FrameTranslate — Yul ↔ frame-IR translation (both directions)

Both directions route through the existing **named** IR (`YulIR.Program`, already block-free and
uniquely-named), which keeps the intrinsic `Fin n` construction clean:

* `ofYul` = `YulIR.ofYul` (Yul → named IR) then `frameOfNamed` (assign each of a function's `k`
  distinct variables a slot `Fin k` via `List.finRange`, mapping references through the assignment);
* `toYul` = `namedOfFrame` (slot `i` ↦ the identifier `_s<i>`, `write` ↦ `assign`, with a
  zero-init `let` preamble declaring the non-param/ret slots) then `YulIR.toYul` (named IR → Yul).

Adequacy of this round-trip against the Yul semantics is **deferred** (these are trusted, as the
existing `ofYul`/`toYul` are). Names are not preserved — slots become `_s<i>`.
-/

namespace YulIR.FinFrame

open YulSemantics (Ident Literal)

/-! ### Yul → frame -/

/-- Map a named atom to a frame atom, resolving a variable to its slot (the fallback literal is
unreachable for well-scoped input — every variable is in the slot map). -/
def ofNamedAtom (idx : Ident → Option (Fin n)) : YulIR.Atom → Atom n
  | .lit l => .lit l
  | .var x => match idx x with | some i => .slot i | none => .lit (.number 0)

/-- Map a named rhs to a frame rhs. -/
def ofNamedRhs (idx : Ident → Option (Fin n)) : YulIR.Rhs → Rhs n
  | .atom a       => .atom (ofNamedAtom idx a)
  | .builtin op a => .builtin op (a.map (ofNamedAtom idx))
  | .call fn a    => .call fn (a.map (ofNamedAtom idx))

mutual
/-- Map a named statement to a frame statement (`letD`/`assign` both become `write`). -/
partial def ofNamedStmt (idx : Ident → Option (Fin n)) : YulIR.Stmt → Stmt n
  | .letD xs rhs    => .assign (xs.filterMap idx) (ofNamedRhs idx rhs)
  | .assign xs rhs  => .assign (xs.filterMap idx) (ofNamedRhs idx rhs)
  | .effect rhs     => .assign [] (ofNamedRhs idx rhs)
  | .cond c b       => .cond (ofNamedAtom idx c) (ofNamedBlock idx b)
  | .switch c cs df => .switch (ofNamedAtom idx c)
                         (cs.map (fun p => (p.1, ofNamedBlock idx p.2))) (df.map (ofNamedBlock idx))
  | .loop post body => .loop (ofNamedBlock idx post) (ofNamedBlock idx body)
  | .«break»        => .«break»
  | .«continue»     => .«continue»
  | .leave          => .leave
partial def ofNamedBlock (idx : Ident → Option (Fin n)) : YulIR.Block → Block n
  | []      => []
  | s :: ss => ofNamedStmt idx s :: ofNamedBlock idx ss
end

/-- Assign slots to a named body given its parameter/return names, and translate it. Returns the
frame size, the param/ret slot lists, and the frame body. -/
def frameBody (params rets : List Ident) (body : YulIR.Block) :
    (k : Nat) × (List (Fin k) × List (Fin k) × Block k) :=
  let names := (params ++ rets ++ YulIR.allIdents body).eraseDups
  let k := names.length
  let m : Std.HashMap Ident (Fin k) := Std.HashMap.ofList (names.zip (List.finRange k))
  let idx : Ident → Option (Fin k) := fun x => m[x]?
  ⟨k, params.filterMap idx, rets.filterMap idx, ofNamedBlock idx body⟩

/-- A named function → a frame `Function`. -/
def ofNamedFunction (fn : YulIR.Function) : Function :=
  let ⟨k, ps, rs, b⟩ := frameBody fn.params fn.rets fn.body
  { nslots := k, params := ps, rets := rs, body := b }

/-- A named program → a frame `Program`. -/
def frameOfNamed (p : YulIR.Program) : Program :=
  let ⟨k, _, _, mainB⟩ := frameBody [] [] p.main
  { functions := Std.HashMap.ofList (p.funList.map (fun q => (q.1, ofNamedFunction q.2)))
    mainSlots := k
    main      := mainB }

/-- Translate a Yul block into the frame IR. -/
def ofYul (b : YulSemantics.Block Op) : Program := frameOfNamed (YulIR.ofYul b)

/-! ### Frame → Yul -/

/-- The identifier for slot `i`: `_s<i>`. -/
def slotIdent (i : Fin n) : Ident := s!"_s{i.val}"

def toNamedAtom : Atom n → YulIR.Atom
  | .lit l  => .lit l
  | .slot i => .var (slotIdent i)

def toNamedRhs : Rhs n → YulIR.Rhs
  | .atom a       => .atom (toNamedAtom a)
  | .builtin op a => .builtin op (a.map toNamedAtom)
  | .call fn a    => .call fn (a.map toNamedAtom)

mutual
/-- Erase a frame statement to the named IR (`write` ↦ `assign`; slots are declared by the frame
preamble in `toNamedFunction`/`toNamedProgram`). -/
partial def toNamedStmt : Stmt n → YulIR.Stmt
  | .assign [] rhs    => .effect (toNamedRhs rhs)
  | .assign ds rhs    => .assign (ds.map slotIdent) (toNamedRhs rhs)
  | .cond c b         => .cond (toNamedAtom c) (toNamedBlock b)
  | .switch c cs df   => .switch (toNamedAtom c) (cs.map (fun p => (p.1, toNamedBlock p.2))) (df.map toNamedBlock)
  | .loop post body   => .loop (toNamedBlock post) (toNamedBlock body)
  | .«break»          => .«break»
  | .«continue»       => .«continue»
  | .leave            => .leave
partial def toNamedBlock : Block n → YulIR.Block
  | []      => []
  | s :: ss => toNamedStmt s :: toNamedBlock ss
end

/-- Zero-init `let`s declaring the slots in `slots` (the local, non-param/ret slots). -/
def slotPreamble (slots : List (Fin n)) : YulIR.Block :=
  slots.map (fun i => YulIR.Stmt.letD [slotIdent i] (.atom (.lit (.number 0))))

/-- Erase a frame function to a named function: params/rets come from the signature; the remaining
slots are declared by a zero-init preamble prepended to the body. -/
def toNamedFunction (fn : Function) : YulIR.Function :=
  let localSlots := (List.finRange fn.nslots).filter (fun i => ! fn.params.contains i && ! fn.rets.contains i)
  { params := fn.params.map slotIdent
    rets   := fn.rets.map slotIdent
    body   := slotPreamble localSlots ++ toNamedBlock fn.body }

/-- Erase a frame program to a named program (all `main` slots declared by a preamble). -/
def namedOfFrame (p : Program) : YulIR.Program :=
  { functions := Std.HashMap.ofList (p.functions.toList.map (fun q => (q.1, toNamedFunction q.2)))
    main      := slotPreamble (List.finRange p.mainSlots) ++ toNamedBlock p.main }

/-- Translate the frame IR back to Yul. -/
def toYul (p : Program) : YulSemantics.Block Op := YulIR.toYul (namedOfFrame p)

end YulIR.FinFrame
