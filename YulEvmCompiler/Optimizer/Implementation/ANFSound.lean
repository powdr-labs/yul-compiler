import YulSemantics.BigStep
import YulEvmCompiler.Optimizer.Implementation.ANF
import YulEvmCompiler.Optimizer.Spec.Pass
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

/-! ### `restore` under a block-local prefix

`restore outer inner = inner.drop (inner.length - outer.length)`. The block-scoped
ANF design introduces temporaries as a *prefix* of the block-local environment,
so `restore` drops them: the observable post-block environment is exactly what it
would have been without the temporaries. -/

private theorem drop_length_append {α} (pre suf : List α) :
    (pre ++ suf).drop pre.length = suf := by
  induction pre with
  | nil => rfl
  | cons a as ih => simpa using ih

/-- Restoring past a block-local prefix recovers the enclosing environment. -/
theorem restore_prefix (V pre : VEnv D) : restore V (pre ++ V) = V := by
  unfold restore
  rw [List.length_append, Nat.add_sub_cancel]
  exact drop_length_append pre V

/-- `restore V V = V` (an empty block-local layer). -/
@[simp] theorem restore_self (V : VEnv D) : restore V V = V := by
  have := restore_prefix V ([] : VEnv D); simp only [List.nil_append] at this; exact this

end YulEvmCompiler.Optimizer.ANF

/-! ## Soundness scaffold

The end-to-end soundness statement and the wired `Pass`, scaffolded with a single
`sorry` at the semantic core so the architecture is verified to compose.

Discharging `anfNormalize_sound` for the *current* (persistent-temporary)
`anfBlock` requires, in order of difficulty:

1. a **fresh-binding weakening lemma for `Step`** — temporaries persist across
   statements within the block (so forwarding can reuse them), so the simulation
   threads them through execution; the `VEnv`/`restore` lemmas above are its base;
2. a **block congruence with *equivalent* (not identical) hoisted functions** —
   ANF rewrites `funDef` bodies, so `hoist b ≠ hoist (anfBlock b)`; `EquivBlock.of_stmts`
   (which needs `hoist` equal) does not apply directly;
3. the **flatten evaluation-correctness** simulation on top.

An alternative design (wrap each statement's flattening in its own sub-block)
makes temporaries block-local per statement, removing (1) entirely — but then
temporaries do not persist, defeating store-to-load forwarding. The persistent
design here is the one the redundant-store pass wants. -/

namespace YulEvmCompiler.Optimizer.ANF

open YulSemantics YulSemantics.EVM
open YulEvmCompiler.Optimizer (Pass)

variable {calls : ExternalCalls} {creates : ExternalCreates}
local notation "D" => evmWithExternal calls creates

/-- A program-fresh temporary prefix. A NUL character cannot occur in a Yul
source identifier, so no program identifier starts with it; the freshness fact
is proved when discharging `anfNormalize_sound`. -/
def anfPrefix (_b : Block Op) : String := String.ofList [Char.ofNat 0] ++ "anf"

/-- The wired ANF normalizer: flatten with a program-fresh prefix. -/
def anfNormalize (b : Block Op) : Block Op := anfBlock (anfPrefix b) b

/-- The normalizer's output is in ANF (from the structural proof). -/
theorem anfNormalize_isANF (b : Block Op) : isANFStmts (anfNormalize b) = true :=
  anfBlock_isANF _ b

/-- **ANF preserves behavior.** (Scaffolded; the `sorry` is the remaining work,
discharged via the block-scoped temp / `restore` lemmas above.) -/
theorem anfNormalize_sound (b : Block Op) :
    EquivBlock D b (anfNormalize b) := by
  sorry

/-- The ANF normalizer as a verified `Pass`. -/
def anfPass : Pass D where
  run := anfNormalize
  sound := anfNormalize_sound

end YulEvmCompiler.Optimizer.ANF
