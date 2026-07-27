import YulEvmCompiler.Optimizer.Implementation.Flatten
import YulEvmCompiler.Optimizer.Implementation.FuseDeclAssignSound
set_option warningAsError true
/-!
# Soundness of block flattening — the rename transport

`Flatten.renameAll` renames each promoted binder `x` of a spliced block to a
globally fresh `x'`.  The guards (`shadowedTop`) ensure every occurrence of
`x` in the renamed sequence refers to the sequence's own top-level
declaration: `x` is not redeclared in any nested scope, is declared exactly
once at the top level, and is not mentioned before that declaration.  The
statements before the declaration therefore contain no `x` at all — renaming
leaves them **syntactically unchanged** — and from the declaration onward the
rename is a keyed environment bijection over the newer-than-entry segment.

`RnRel x x'` captures the environment shape during the renamed suffix:

* source: `C₁ ++ base`, target: `C₂ ++ base` with `C₂ = renKeys C₁`
  (every `x` key becomes `x'`, values equal, order preserved);
* `x'` occurs nowhere in the source code, so the source never reads or
  writes it; reads of `x`/`x'` resolve to corresponding entries; reads of
  other names agree (`renKeys` only changes `x` keys);
* the common `base` may bind both `x` (an outer shadow, unreachable from the
  renamed occurrences once the local declaration exists) and `x'`
  (unreachable from the source, and shadowed on the target).

The subtlety mirroring `MvRel`: `restore` is positional, and the segment/base
split is length-stable under execution, so block exits keep the relation.
-/

namespace YulEvmCompiler.Optimizer.Flatten

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler.Optimizer.FuseDeclAssign (set_append_of_found
  set_append_of_none)

variable {calls : ExternalCalls} {creates : ExternalCreates}
local notation "D" => evmWithExternal calls creates

/-! ### Keyed renaming of an environment segment -/

/-- Rename every `x` key to `x'` (values untouched). -/
def renKeys (x x' : Ident) (V : VEnv D) : VEnv D :=
  V.map (fun p => (renVar x x' p.1, p.2))

@[simp] theorem renKeys_nil (x x' : Ident) :
    renKeys (calls := calls) (creates := creates) x x' [] = [] := rfl

@[simp] theorem renKeys_cons (x x' : Ident)
    (p : Ident × (evmWithExternal calls creates).Value) (V : VEnv D) :
    renKeys x x' (p :: V) = (renVar x x' p.1, p.2) :: renKeys x x' V := rfl

@[simp] theorem renKeys_append (x x' : Ident) (V W : VEnv D) :
    renKeys x x' (V ++ W) = renKeys x x' V ++ renKeys x x' W := by
  simp [renKeys]

@[simp] theorem renKeys_length (x x' : Ident) (V : VEnv D) :
    (renKeys x x' V).length = V.length := by
  simp [renKeys]

/-- The environment relation for the renamed suffix. -/
inductive RnRel (x x' : Ident) : VEnv D → VEnv D → Prop
  | mk (C base : VEnv D) :
      RnRel x x' (C ++ base) (renKeys x x' C ++ base)

theorem RnRel.length {x x' : Ident} {V₁ V₂ : VEnv D}
    (h : RnRel x x' V₁ V₂) : V₁.length = V₂.length := by
  cases h with
  | mk C base => simp [renKeys]

/-- Push corresponding bindings: the target key is the renamed source key. -/
theorem RnRel.push {x x' : Ident} {V₁ V₂ : VEnv D} (h : RnRel x x' V₁ V₂)
    (y : Ident) (v : (evmWithExternal calls creates).Value) :
    RnRel x x' ((y, v) :: V₁) ((renVar x x' y, v) :: V₂) := by
  cases h with
  | mk C base => exact RnRel.mk ((y, v) :: C) base

end YulEvmCompiler.Optimizer.Flatten
