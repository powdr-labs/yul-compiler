import YulEvmCompiler.Optimizer.Implementation.Simplify
import YulEvmCompiler.Optimizer.Implementation.Normalization.NormalForm
import YulEvmCompiler.Optimizer.Spec.PrePostPass

set_option warningAsError true

/-!
# YulEvmCompiler.Optimizer.Implementation.SimplifyUniqueNames

The `simplify` pass **preserves** the `NormalForm.UniqueNames` invariant: if no
variable or function name is declared twice anywhere in a program, the same holds
after simplification.

## Why it holds

`UniqueNames b` is `(declaredNamesStmts b).Nodup`, where `declaredNamesStmts`
collects every declared name (function names, params, rets, `let`-vars) anywhere
in the subtree. The `simplify` pass never *introduces* a declared name:

* Expression rewrites (constant folding, neutral-element identities) touch only
  `Expr` positions, which declare nothing.
* Recursing into a sub-block, `funDef` body, `switch` case, `for`-loop `post`/`body`
  can only *shrink* the declared-name multiset (folding a `let x := e` keeps `x`).
* Literal control-flow selection replaces an `if`/`switch` by *one* of its
  sub-blocks (or the empty block / a `pop` residue), whose declared names already
  occurred — as a contiguous chunk — inside the original.

Consequently `declaredNamesStmts (simplify.run b)` is always a **sublist** of
`declaredNamesStmts b` (order-preserving; nothing is duplicated or lifted across a
scope). `List.Sublist.nodup` then transports `Nodup` from the input to the output.

The core content is the mutual family of `*_sublist` theorems establishing the
sublist relation; `simplify_preserves_uniqueNames` is the one-line corollary.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics YulSemantics.EVM
open NormalForm

/-! ## The selected `switch` block only shrinks the declared names -/

/-- The block a literal `switch` selects (`selectSwitch`) declares a *sublist* of the
names declared across all cases and the default: it is exactly one case body or the
default (or the empty block), each of which is a contiguous chunk of the
concatenation `declaredNamesCases cases ++ declaredNamesDflt dflt`. -/
theorem declaredNamesStmts_selectSwitch_sublist (cv : evm.Value) :
    ∀ (cs : List (Literal × Block Op)) (d : Option (Block Op)),
      (declaredNamesStmts (selectSwitch evm cv cs d)).Sublist
        (declaredNamesCases cs ++ declaredNamesDflt d)
  | [], none => List.nil_sublist _
  | [], some _ => List.Sublist.refl _
  | (l, b) :: rest, d => by
      have ih := declaredNamesStmts_selectSwitch_sublist cv rest d
      rw [show declaredNamesCases ((l, b) :: rest)
            = declaredNamesStmts b ++ declaredNamesCases rest from rfl]
      by_cases h : cv = evm.litValue l
      · have hfind : List.find? (fun p => decide (cv = litValue p.1)) ((l, b) :: rest)
            = some (l, b) := List.find?_cons_of_pos (by simpa using h)
        have hsel : selectSwitch evm cv ((l, b) :: rest) d = b := by
          simp only [selectSwitch, hfind]
        rw [hsel]
        exact (List.sublist_append_left _ _).trans (List.sublist_append_left _ _)
      · have hfind : List.find? (fun p => decide (cv = litValue p.1)) ((l, b) :: rest)
            = List.find? (fun p => decide (cv = litValue p.1)) rest :=
          List.find?_cons_of_neg (by simpa using h)
        have hsel : selectSwitch evm cv ((l, b) :: rest) d = selectSwitch evm cv rest d := by
          simp only [selectSwitch, hfind]
        rw [hsel, List.append_assoc]
        exact ih.trans (List.sublist_append_right _ _)

/-! ## `simplifyCond` / `simplifySwitch` only shrink the declared names -/

/-- `simplifyCond c body` declares a sublist of `body`'s names: it is one of
`.block []`, `.block body`, a `pop` residue, or `.cond c body` — none of which
introduces a name outside `declaredNamesStmts body`. -/
theorem declaredNamesStmt_simplifyCond_sublist (c : Expr Op) (body : Block Op) :
    (declaredNamesStmt (simplifyCond c body)).Sublist (declaredNamesStmts body) := by
  unfold simplifyCond
  split
  · split
    · exact List.nil_sublist _
    · exact List.Sublist.refl _
  · split
    · exact List.nil_sublist _
    · exact List.Sublist.refl _

/-- `simplifySwitch c cases dflt` declares a sublist of the names declared across
`cases` and `dflt`: either the selected block (`declaredNamesStmts_selectSwitch_sublist`)
or the rebuilt `switch` (which declares exactly those names). -/
theorem declaredNamesStmt_simplifySwitch_sublist (c : Expr Op)
    (cases : List (Literal × Block Op)) (dflt : Option (Block Op)) :
    (declaredNamesStmt (simplifySwitch c cases dflt)).Sublist
      (declaredNamesCases cases ++ declaredNamesDflt dflt) := by
  unfold simplifySwitch
  split
  · exact declaredNamesStmts_selectSwitch_sublist _ cases dflt
  · exact List.Sublist.refl _

/-! ## The pass only shrinks the declared names (mutual core) -/

mutual

/-- Simplifying a statement produces a sublist of its declared names. -/
theorem declaredNamesStmt_simplifyStmt_sublist :
    ∀ s : Stmt Op, (declaredNamesStmt (simplifyStmt s)).Sublist (declaredNamesStmt s)
  | .block body => declaredNamesStmts_simplifyStmts_sublist body
  | .funDef n ps rs body =>
      (((List.Sublist.refl (ps ++ rs)).append
        (declaredNamesStmts_simplifyStmts_sublist body)).cons_cons n)
  | .letDecl [_] (some _) => List.Sublist.refl _
  | .letDecl [] (some _) => List.Sublist.refl _
  | .letDecl (_ :: _ :: _) (some _) => List.Sublist.refl _
  | .letDecl [_] none => List.Sublist.refl _
  | .letDecl [] none => List.Sublist.refl _
  | .letDecl (_ :: _ :: _) none => List.Sublist.refl _
  | .assign [_] _ => List.Sublist.refl _
  | .assign [] _ => List.Sublist.refl _
  | .assign (_ :: _ :: _) _ => List.Sublist.refl _
  | .cond c body =>
      (declaredNamesStmt_simplifyCond_sublist (simplifyExpr c) (simplifyStmts body)).trans
        (declaredNamesStmts_simplifyStmts_sublist body)
  | .switch c cases dflt =>
      (declaredNamesStmt_simplifySwitch_sublist (simplifyExpr c)
          (simplifyCases cases) (simplifyDflt dflt)).trans
        ((declaredNamesCases_simplifyCases_sublist cases).append
          (declaredNamesDflt_simplifyDflt_sublist dflt))
  | .forLoop init _ post body =>
      ((List.Sublist.refl (declaredNamesStmts init)).append
        (declaredNamesStmts_simplifyStmts_sublist post)).append
        (declaredNamesStmts_simplifyStmts_sublist body)
  | .exprStmt _ => List.Sublist.refl _
  | .break => List.Sublist.refl _
  | .continue => List.Sublist.refl _
  | .leave => List.Sublist.refl _

/-- Simplifying a statement sequence produces a sublist of its declared names. -/
theorem declaredNamesStmts_simplifyStmts_sublist :
    ∀ ss : List (Stmt Op),
      (declaredNamesStmts (simplifyStmts ss)).Sublist (declaredNamesStmts ss)
  | [] => List.Sublist.refl _
  | s :: rest =>
      (declaredNamesStmt_simplifyStmt_sublist s).append
        (declaredNamesStmts_simplifyStmts_sublist rest)

/-- Simplifying `switch` cases produces a sublist of their declared names. -/
theorem declaredNamesCases_simplifyCases_sublist :
    ∀ cs : List (Literal × Block Op),
      (declaredNamesCases (simplifyCases cs)).Sublist (declaredNamesCases cs)
  | [] => List.Sublist.refl _
  | (_, b) :: rest =>
      (declaredNamesStmts_simplifyStmts_sublist b).append
        (declaredNamesCases_simplifyCases_sublist rest)

/-- Simplifying a `switch` default produces a sublist of its declared names. -/
theorem declaredNamesDflt_simplifyDflt_sublist :
    ∀ d : Option (Block Op),
      (declaredNamesDflt (simplifyDflt d)).Sublist (declaredNamesDflt d)
  | none => List.Sublist.refl _
  | some b => declaredNamesStmts_simplifyStmts_sublist b

end

/-! ## Invariant preservation -/

variable {calls : ExternalCalls} {creates : ExternalCreates}

/-- **The `simplify` pass preserves `NormalForm.UniqueNames`.** Since simplification
never introduces a declared name (`declaredNamesStmts_simplifyStmts_sublist`), the
output's declared-name list is a sublist of the input's, so `Nodup` transports. -/
theorem simplify_preserves_uniqueNames :
    Optimizer.Preserves (D := evmWithExternal calls creates)
      NormalForm.UniqueNames (simplify (calls := calls) (creates := creates)).run :=
  fun b hb => (declaredNamesStmts_simplifyStmts_sublist b).nodup hb

end YulEvmCompiler.Optimizer
