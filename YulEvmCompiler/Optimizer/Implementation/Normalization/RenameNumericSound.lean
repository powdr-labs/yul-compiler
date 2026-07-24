import YulEvmCompiler.Optimizer.Implementation.Normalization.RenameNumeric
import YulEvmCompiler.Optimizer.Implementation.Normalization.RenameNumericFresh
import YulEvmCompiler.Optimizer.Implementation.Normalization.Disambiguate.Pass
import YulEvmCompiler.Optimizer.Implementation.Normalization.Disambiguate.Decide
import YulEvmCompiler.Optimizer.Spec.GlobalPass
-- WIP: this file is the in-progress soundness proof for `RenameNumeric.rename`.
-- Sorries below are scaffolding to be discharged over subsequent commits; the
-- warning-as-error gate is relaxed here so the branch keeps building meanwhile.
set_option warningAsError false
/-!
# Soundness of `RenameNumeric.rename` (WORK IN PROGRESS)

Goal: `RunEquivBlock D b (rename b)` on valid source programs — the
collision-only, program-fresh, printable disambiguator is semantics-preserving,
so it can become a verified `GlobalPass` (and eventually replace the NUL-based
`disambiguate` as the pipeline's normalization step).

## Architecture: compose with the existing verified simulation

We do **not** re-prove a `Step`-level simulation. The verified `disambiguate`
canonicalizes every declared name to a counter value determined by **traversal
position alone** — its output names are independent of the input's names, and
its reference resolution depends only on which binder each reference resolves
to. `rename` preserves exactly that resolution structure (it is a consistent,
capture-avoiding α-renaming). Hence disambiguation should be **invariant under
`rename`**:

```
disambiguate (rename b) = disambiguate b        -- (B), purely syntactic
```

With (A) `SourceValid` preservation, soundness composes out of the *existing*
`sim_fwd`/`sim_bwd` machinery, applied once forwards and once backwards:

```
b  ≈  disambiguate b  =  disambiguate (rename b)  ≈  rename b
   (existing thm, h)        (B)                 (existing thm, symm, A h)
```

## Milestones

1. **Fresh-name foundation** — `freshName_not_mem` (pigeonhole over the
   `avoid.length + 1` distinct candidates; needs decimal-`toString`
   injectivity) and `assignName_fresh` (done). *Self-contained; being proved in
   a parallel workstream.*
2. **(A) `rename_sourceValid`** — `SourceValid b → SourceValid (rename b)`:
   kept names stay `NotFresh`; fresh `x_k` names end in a digit so they are
   never a `dsName` (which ends in `'v'`); binder lists stay `Nodup` (committed
   sequentially to the monotone `taken`); the output is shadow-free (global
   uniqueness is stronger), scoped, and per-block `Nodup`-function-named.
3. **(B) `disambiguate_rename`** — the α-invariance of the canonicalizer, by
   the mutual induction with invariant: the two renaming states are equal after
   mapping keys through `rename`'s binder map, and both key sets are duplicate
   free (no shadowing, from `SourceValid`), so name-keyed first-match lookup
   resolves both sides at the same position to the same `dsName`.
4. **(C) assembly** — `rename_runEquivBlock` from (A) + (B) + the existing
   `sourceValid_runEquivBlock`, plus the guarded `GlobalPass` packaging
   (`renamePass`), mirroring `disambiguatePass`.

Also kept: `rename_uniqueNames` (the `NormalForm.UniqueNames` postcondition,
needed for `rename` to serve as the pipeline's normalizer in front of the
hoister — its guard `hoistGuard` requires unique names to fire).

**Precondition note.** Soundness is stated under `SourceValid` — the same
contract as the verified `disambiguate` — and packaged unconditionally via the
`sourceValidB` guard. A collision-only renamer genuinely needs the
no-duplicate-function (`WellFormed`) half: on the invalid input
`[funDef f …, funDef f …]` (same block) the name-keyed substitution maps both
definitions to the same fresh name, so even `UniqueNames` fails without it.
-/

namespace YulEvmCompiler.Optimizer.RenameNumeric

open YulSemantics
open YulEvmCompiler.Optimizer (RunEquivBlock GlobalPass)
open YulEvmCompiler.Optimizer.Normalize
  (SourceValid sourceValid_runEquivBlock disambiguate sourceValidB sourceValidB_sound)

variable {Op : Type}
variable {D : Dialect} [DecidableEq D.Value]

/-! ## Milestone 1 — fresh-name foundation

`natToString_inj`, `freshCand_inj`, and `freshName_not_mem` are proved
sorry-free in `RenameNumericFresh.lean` (imported above). -/

/-- Each `assignName` commits an output name that is new to `taken`. -/
theorem assignName_fresh (orig taken : List Ident) (x : Ident) :
    (assignName orig taken x).1 ∉ taken := by
  unfold assignName
  by_cases hx : x ∈ taken
  · rw [if_pos hx]
    exact fun hmem => freshName_not_mem (taken ++ orig) x (List.mem_append_left orig hmem)
  · rw [if_neg hx]; exact hx

/-! ## `UniqueNames` postcondition

Proved sorry-free as `rename_uniqueNames'` in `RenameNumericUnique.lean` (under
the `WellFormed` half of `SourceValid`, which is exactly what it needs — see the
precondition note above). Not imported here to keep this module's import graph
acyclic; the final assembly composes it alongside the theorems below. -/

/-! ## Milestone 2 — (A) `SourceValid` preservation -/

/-- **(A)** `rename` preserves source validity: kept identifiers stay `NotFresh`;
generated `x_k` names end in a decimal digit and so differ from every `dsName`
(which ends in `'v'`); binder `Nodup`, per-block function-name `Nodup`,
well-scopedness, and shadow-freedom all hold in the output (the last because the
output's declared names are globally distinct). -/
theorem rename_sourceValid {b : Block Op} (h : SourceValid b) :
    SourceValid (rename b) := by
  sorry

/-! ## Milestone 3 — (B) disambiguation is invariant under `rename` -/

/-- **(B) The canonicalizer absorbs the α-renaming.** `disambiguate` assigns
`dsName` values by traversal position (identical on both sides, since `rename`
preserves the tree shape and every binder-list length) and resolves references
by name-keyed first-match lookup, which — with both key sets duplicate-free (no
shadowing, from `SourceValid`) — resolves at the same position on both sides.
Proved by the mutual induction with state invariant
`st_renamed = (map (ρ × id)) st_source` for `rename`'s binder map `ρ`. -/
theorem disambiguate_rename {b : Block Op} (h : SourceValid b) :
    disambiguate (rename b) = disambiguate b := by
  sorry

/-! ## Milestone 4 — (C) assembly -/

/-- **Soundness of the collision-only numeric disambiguator** on valid source
programs, by composing the existing verified simulation with itself across the
syntactic equation (B):
`b ≈ disambiguate b = disambiguate (rename b) ≈ rename b`. -/
theorem rename_runEquivBlock {b : Block D.Op} (h : SourceValid b) :
    RunEquivBlock D b (rename b) := by
  have h1 : RunEquivBlock D b (disambiguate b) := sourceValid_runEquivBlock h
  have h2 : RunEquivBlock D (rename b) (disambiguate (rename b)) :=
    sourceValid_runEquivBlock (rename_sourceValid h)
  rw [disambiguate_rename h] at h2
  exact h1.trans h2.symm

/-- **The collision-only numeric disambiguator as an unconditionally sound
whole-tree `GlobalPass`**, guarded on the decidable `sourceValidB` exactly like
`disambiguatePass`. Once the milestones above are discharged this is a verified
drop-in replacement for the NUL-based pass. -/
def renamePass : GlobalPass D :=
  GlobalPass.ofGuardedBlock sourceValidB rename
    (fun _ hg => rename_runEquivBlock (sourceValidB_sound hg))

/-! ### Empirical regression checks for equation (B)

Build-time evidence for `disambiguate_rename` while its proof is in progress:
the canonicalizer absorbs the α-renaming on the demo programs, including the
adversarial `x`/`x_1` pre-collision. (`Stmt` has no `DecidableEq`; compare via
`Repr`.) -/

section ChecksB

/-- `Repr`-based equality of the two disambiguated forms (build-time check). -/
private def chkB (b : Block Unit) : Bool :=
  (repr (disambiguate (rename b))).pretty == (repr (disambiguate b)).pretty

/-- Name that already looks numeric-suffixed: `x` and `x_1` both present, then
`x` shadowed — the fresh name for the inner `x` must dodge the real `x_1`. -/
private def exTricky : Block Unit :=
  [ .letDecl ["x"] (some (.lit (.number 1))),
    .letDecl ["x_1"] (some (.var "x")),
    .block [ .letDecl ["x"] (some (.var "x_1")), .assign ["x"] (.var "x") ] ]

#guard chkB exNoCollision
#guard chkB exShadow
#guard chkB exSiblings
#guard chkB exTricky

end ChecksB

end YulEvmCompiler.Optimizer.RenameNumeric
