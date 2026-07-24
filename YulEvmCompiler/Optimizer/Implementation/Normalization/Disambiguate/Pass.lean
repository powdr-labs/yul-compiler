import YulEvmCompiler.Optimizer.Implementation.Normalization.Disambiguate.Run
/-!
# Disambiguation as a whole-tree normalization step

`disambiguateObject` runs `disambiguate` on every code block of an object tree
(each object — the deploy artifact and every nested `*_deployed` runtime — is
its own root, so per-block renaming from counter `0` is the right scope).
`compileSource` applies it as the **first** optimizer step.

## Known limitation: conditional soundness, no decidable guard

Soundness (`disambiguateObject_objEquiv`) is **conditional** on the standing
validity facts for source Yul programs, bundled as `SourceValid`:

* `SVStmts` — identifiers are `NUL`-free and binder lists duplicate-free;
* `WellFormed` — per-block distinct function names;
* `NormalForm.WellScoped` — every referenced name resolves;
* `WScopedStmts []` / `FScopedStmts` — no variable or function shadows a
  visible one.

All hold for solc-generated (indeed, for any spec-valid) Yul, but only
`WellScoped` is forced by execution itself — the others are *assumed*, not
checked: the pass is deliberately **not** a `GlobalPass`, whose `sound` field
is unconditional. Two known upgrade paths, logged in `Optimizer/IDEAS.md`:

* **guard** — `Bool` deciders for the five predicates plus
  `GlobalPass.ofGuardedBlock` (the `hoistFunDefsPass` pattern); mechanical;
* **generalize** — prove soundness for every well-scoped program: replace the
  name-map α-relation (which cannot express shadowed environments) by a
  positional one and make fresh names program-fresh rather than `NUL`-based;
  a redesign of the simulation proofs.
-/

namespace YulEvmCompiler.Optimizer.Normalize

open YulSemantics

variable {Op : Type}

/-- The standing validity facts a source program owes `disambiguate` for its
soundness theorem (`disambiguate_runEquivBlock`) — see the module docstring. -/
def SourceValid (b : Block Op) : Prop :=
  SVStmts b ∧ WellFormed b ∧ NormalForm.WellScoped b ∧
    WScopedStmts ([] : List Ident) b ∧ FScopedStmts (funNames b) b

mutual
/-- `SourceValid` at every code block of an object tree. -/
def SourceValidObj : Object Op → Prop
  | .mk _ code subs _ => SourceValid code ∧ SourceValidObjs subs
def SourceValidObjs : List (Object Op) → Prop
  | [] => True
  | o :: rest => SourceValidObj o ∧ SourceValidObjs rest
end

/-! ### The transform -/

mutual
/-- Disambiguate every code block of an object tree (the object's own code
and, recursively, every sub-object's — each is its own root). -/
def disambiguateObject : Object Op → Object Op
  | .mk n code subs segs => .mk n (disambiguate code) (disambiguateObjects subs) segs

/-- Disambiguate every object in a list. -/
def disambiguateObjects : List (Object Op) → List (Object Op)
  | [] => []
  | o :: rest => disambiguateObject o :: disambiguateObjects rest
end

@[simp] theorem disambiguateObject_codeBlock (o : Object Op) :
    (disambiguateObject o).codeBlock = disambiguate o.codeBlock := by
  cases o; rfl

/-! ### Conditional soundness -/

variable {D : Dialect} [DecidableEq D.Value]

/-- `disambiguate_runEquivBlock` at the bundled hypothesis. -/
theorem sourceValid_runEquivBlock {b : Block D.Op} (h : SourceValid b) :
    Optimizer.RunEquivBlock D b (disambiguate b) :=
  disambiguate_runEquivBlock b h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

mutual
/-- **Conditional soundness of whole-tree disambiguation**: on a valid source
tree, every code block's whole-program behaviour is preserved. This is the
`GlobalPass.sound` obligation *minus* the unconditionality — see the module
docstring for why the pass stays outside the `GlobalPass` structure for now. -/
theorem disambiguateObject_objEquiv : ∀ (o : Object D.Op), SourceValidObj o →
    Optimizer.ObjEquiv D o (disambiguateObject o)
  | .mk _ code subs _, h =>
      ⟨rfl, rfl, sourceValid_runEquivBlock (b := code) h.1,
        disambiguateObjects_objEquivList subs h.2⟩
/-- `disambiguateObject_objEquiv`, list form. -/
theorem disambiguateObjects_objEquivList : ∀ (os : List (Object D.Op)), SourceValidObjs os →
    Optimizer.ObjEquivList D os (disambiguateObjects os)
  | [], _ => trivial
  | o :: rest, h =>
      ⟨disambiguateObject_objEquiv o h.1, disambiguateObjects_objEquivList rest h.2⟩
end

/-- The operative consequence at the object boundary (`RunObject`/
`RunResolvedObject` depend only on the top code block): validity of the **top**
block alone preserves the tree's top-level behaviour. -/
theorem disambiguateObject_topRunEquiv {o : Object D.Op} (h : SourceValid o.codeBlock) :
    Optimizer.RunEquivBlock D o.codeBlock (disambiguateObject o).codeBlock := by
  rw [disambiguateObject_codeBlock]
  exact sourceValid_runEquivBlock h

end YulEvmCompiler.Optimizer.Normalize
