import YulSemantics.BigStep
/-!
# ANF normalizer — soundness foundations (`VEnv` weakening atoms)

The ANF normalizer introduces `let` temporaries that stay in scope, so proving
`EquivBlock b (anfBlock b)` needs a **fresh-binding weakening** lemma for `Step`:
a temporary that no code reads threads through execution unchanged and is popped
by the enclosing block's `restore`.

That lemma is a large mutual induction over the whole `Step` relation. It bottoms
out in how `VEnv.get`/`VEnv.set` behave across a prepended (fresh) binding — the
self-contained facts proved here. The `Step`-level weakening lemma and the ANF
temp-tracking simulation build on top; this file is their base.
-/

namespace YulEvmCompiler.Optimizer.ANF

open YulSemantics

variable {D : Dialect}

/-- Reading a variable past a differently-named binding ignores that binding. -/
@[simp] theorem get_cons_ne {V : VEnv D} {x y : Ident} {w : D.Value} (h : y ≠ x) :
    VEnv.get ((y, w) :: V) x = VEnv.get V x := by
  simp [VEnv.get, List.find?, h]

/-- Reading a variable at its own (innermost) binding. -/
@[simp] theorem get_cons_self {V : VEnv D} {x : Ident} {w : D.Value} :
    VEnv.get ((x, w) :: V) x = some w := by
  simp [VEnv.get, List.find?]

/-- Assigning a variable past a differently-named binding leaves that binding and
recurses into the tail. -/
@[simp] theorem set_cons_ne {V : VEnv D} {x y : Ident} {w v : D.Value} (h : y ≠ x) :
    VEnv.set ((y, w) :: V) x v = (y, w) :: VEnv.set V x v := by
  simp [VEnv.set, h]

/-- Assigning a variable at its own (innermost) binding. -/
@[simp] theorem set_cons_self {V : VEnv D} {x : Ident} {w v : D.Value} :
    VEnv.set ((x, w) :: V) x v = (x, v) :: V := by
  simp [VEnv.set]

/-- A fresh binding is invisible to reads of any variable already in scope: if
`t` differs from `x`, prepending `(t, w)` does not change `x`'s value. This is
the read-side of the weakening lemma at a single binding. -/
theorem get_prepend_fresh {V : VEnv D} {x t : Ident} {w : D.Value} (h : t ≠ x) :
    VEnv.get ((t, w) :: V) x = VEnv.get V x :=
  get_cons_ne h

/-- Assigning an in-scope variable commutes with a fresh prepended binding: the
fresh binding is untouched and the assignment lands in the tail. This is the
write-side of the weakening lemma at a single binding. -/
theorem set_prepend_fresh {V : VEnv D} {x t : Ident} {w v : D.Value} (h : t ≠ x) :
    VEnv.set ((t, w) :: V) x v = (t, w) :: VEnv.set V x v :=
  set_cons_ne h

/-- `VEnv.set` preserves length — so `restore` (which truncates by length) is
insensitive to values written by an assignment. -/
theorem set_length (V : VEnv D) (x : Ident) (v : D.Value) :
    (VEnv.set V x v).length = V.length := by
  induction V with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨y, w⟩ := p
      by_cases h : y = x
      · subst h; simp [VEnv.set]
      · simp [VEnv.set, h, ih]

end YulEvmCompiler.Optimizer.ANF
