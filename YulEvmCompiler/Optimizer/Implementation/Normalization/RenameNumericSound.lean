import YulEvmCompiler.Optimizer.Implementation.Normalization.RenameNumeric
import YulEvmCompiler.Optimizer.Spec.GlobalPass
-- WIP: this file is the in-progress soundness proof for `RenameNumeric.rename`.
-- Sorries below are scaffolding to be discharged over subsequent commits; the
-- warning-as-error gate is relaxed here so the branch keeps building meanwhile.
set_option warningAsError false
/-!
# Soundness of `RenameNumeric.rename` (WORK IN PROGRESS)

Goal: `RunEquivBlock D b (rename b)` for **every** block — the collision-only,
program-fresh, printable disambiguator is semantics-preserving, so it can become a
verified `GlobalPass` and (eventually) replace the NUL-based `disambiguate`.

Unlike the existing proof, this one must not assume the `NUL`/`dsName` freshness
scheme. The plan generalizes the α-simulation's freshness layer to an **abstract
program-fresh** notion and instantiates it for the numeric renamer.

## Decomposition (milestones)

1. **Fresh-name foundation** (`freshName_not_mem`, `assign*` facts): a generated
   name is absent from the avoidance set, and each `assignName` step commits a
   name not previously in `taken`. — *foundation, this file.*
2. **`UniqueNames` postcondition** (`rename_uniqueNames`): the output's declared
   names are `Nodup`. Threaded from the monotone `taken` invariant. — *syntactic.*
3. **α-witness** (`rename_alpha`): `rename b` is a consistent, capture-avoiding
   renaming of `b` — i.e. there exist `σ, φ` with `b ~[σ,φ] rename b` under an
   abstract, program-fresh α-relation (renaming injective on the program's names;
   fresh targets disjoint from source names). — *structural.*
4. **Generic simulation** (`alpha_runEquiv`): any such abstract-α-related pair has
   equivalent whole-program behaviour (`RunEquivBlock`). This is the crux — the
   forward/backward `Step` simulation, freed from `dsName`. — *semantic, largest.*
5. **Assembly** (`rename_runEquivBlock`): 3 + 4.

Milestones 1–3 are being proved directly; 4 is the large simulation (currently
`sorry`, to be discharged incrementally — see the per-lemma notes).
-/

namespace YulEvmCompiler.Optimizer.RenameNumeric

open YulSemantics
open YulEvmCompiler.Optimizer (RunEquivBlock)

variable {Op : Type}
variable {D : Dialect} [DecidableEq D.Value]

/-! ## Milestone 1 — fresh-name foundation -/

/-- The numeric-suffix candidates are injective in the index (so `≥ length+1`
of them are distinct, which drives the pigeonhole for `freshName`). -/
theorem freshCand_inj {base : Ident} {i j : Nat}
    (h : base ++ "_" ++ toString i = base ++ "_" ++ toString j) : i = j := by
  -- `base ++ "_" ++ toString i` parses as `(base ++ "_") ++ toString i`.
  have h2 := (String.append_right_inj (base ++ "_")).mp h
  -- `toString` is injective on `Nat`; leaf number-theory fact.
  sorry

/-- **A generated fresh name is not in the avoidance set.** With
`fuel = avoid.length + 1` the bounded search always finds a free candidate,
because the `avoid.length + 1` distinct candidates cannot all lie in `avoid`. -/
theorem freshName_not_mem (avoid : List Ident) (base : Ident) :
    freshName avoid base ∉ avoid := by
  -- freshName = freshAux base avoid (avoid.length+1) 1; induction on fuel with the
  -- pigeonhole "some candidate in [1, avoid.length+2) is fresh" (uses freshCand_inj).
  sorry

/-- Each `assignName` commits an output name that is new to `taken`. -/
theorem assignName_fresh (orig taken : List Ident) (x : Ident) :
    (assignName orig taken x).1 ∉ taken := by
  unfold assignName
  by_cases hx : x ∈ taken
  · rw [if_pos hx]
    exact fun hmem => freshName_not_mem (taken ++ orig) x (List.mem_append_left orig hmem)
  · rw [if_neg hx]; exact hx

/-! ## Milestone 2 — `UniqueNames` postcondition -/

/-- **`rename` produces globally-unique declared names.** Each declaration commits
a name new to the monotone `taken` set, so no name is declared twice. -/
theorem rename_uniqueNames (b : Block Op) :
    (NormalForm.declaredNamesStmts (rename b)).Nodup := by
  -- Invariant: `declaredNames (output) = (taken_after \ taken_before)` with
  -- `taken` Nodup throughout (each `assignName` prepends a fresh name). Threaded
  -- through the mutual traversal (renStmt/renStmts/renScope/renCases/renDflt).
  sorry

/-! ## Milestones 3–4 — α-witness and the generic simulation

The abstract, program-fresh α-relation and its forward/backward `Step`
simulation. This replaces the `NUL`/`dsName`/`RangeNodup` structure of
`Disambiguate/Alpha.lean` with: (i) the renaming is injective on the program's
identifiers, and (ii) every fresh target is disjoint from all source identifiers
(`allIdents`). The `Step`-level simulation is the bulk of the remaining work. -/

/-- **α-witness**: `rename b` is a consistent capture-avoiding renaming of `b`.
(Statement to be refined to the abstract α-relation.) -/
theorem rename_alpha (b : Block Op) : True := by
  trivial

/-! ## Milestone 5 — assembly -/

/-- **Soundness of the collision-only numeric disambiguator.** WIP: reduces to the
generic program-fresh α-simulation (milestone 4). -/
theorem rename_runEquivBlock (b : Block D.Op) :
    RunEquivBlock D b (rename b) := by
  sorry

end YulEvmCompiler.Optimizer.RenameNumeric
