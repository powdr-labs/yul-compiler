import YulEvmCompiler.Optimizer.Implementation.DeadResults
import YulEvmCompiler.Optimizer.Implementation.Normalization.NormalForm
import YulEvmCompiler.Optimizer.Spec.PrePostPass

set_option warningAsError true

/-!
# YulEvmCompiler.Optimizer.Implementation.DeadCodeUniqueNames

The dead-code elimination passes `deadResults` and `deadPure` **preserve** the
`NormalForm.UniqueNames` invariant (no variable or function name is declared
twice anywhere in the program).

Both passes are pure *removal* transforms: they recurse into sub-blocks without
renaming or reordering any declaration, and the only non-structural rewrite
either drops a whole statement (`deadPure`) or drops a zero-init `let` together
with an adjacent nested region (`deadResults`). In every case the multiset of
declared names of the output is a **sublist** of that of the input. Hence
`declaredNamesStmts` can only shrink (in the sublist sense), and `Nodup` is
inherited downward along a sublist (`List.Nodup.sublist`).

The core content is the mutual family of `*_declaredNames_sublist` lemmas,
which mirror the mutual recursion of `drStmt`/`drStmts`/… and
`dpStmt`/`dpStmts`/… respectively. The two headline results are stated with the
optimizer framework's `Optimizer.Preserves` from
`YulEvmCompiler.Optimizer.Spec.PrePostPass`.
-/

namespace YulEvmCompiler.Optimizer.NormalForm

open YulSemantics
open YulSemantics.EVM

/-! ## `deadResults` shrinks the declared-name list -/

section DeadResults

mutual

/-- `drStmt` never introduces a declared name: the declared names of the
transformed statement form a sublist of the original's. -/
theorem drStmt_declaredNames_sublist (bound : List Ident) : ∀ s : Stmt Op,
    List.Sublist (declaredNamesStmt (drStmt bound s)) (declaredNamesStmt s)
  | .block body => by
      simp only [drStmt, declaredNamesStmt]
      exact drStmts_declaredNames_sublist bound body
  | .funDef n ps rs body => by
      simp only [drStmt, declaredNamesStmt]
      exact ((List.Sublist.refl (ps ++ rs)).append
        (drStmts_declaredNames_sublist (ps ++ rs) body)).cons_cons n
  | .cond c body => by
      simp only [drStmt, declaredNamesStmt]
      exact drStmts_declaredNames_sublist bound body
  | .switch c cases dflt => by
      simp only [drStmt, declaredNamesStmt]
      exact (drCases_declaredNames_sublist bound cases).append
        (drDflt_declaredNames_sublist bound dflt)
  | .forLoop init c post body => by
      simp only [drStmt, declaredNamesStmt]
      exact ((List.Sublist.refl (declaredNamesStmts init)).append
        (drStmts_declaredNames_sublist bound post)).append
        (drStmts_declaredNames_sublist bound body)
  | .letDecl _ _ => List.Sublist.refl _
  | .assign _ _ => List.Sublist.refl _
  | .exprStmt _ => List.Sublist.refl _
  | .break => List.Sublist.refl _
  | .continue => List.Sublist.refl _
  | .leave => List.Sublist.refl _

/-- `drStmts` (the block transform behind `deadResults.run`) only removes
declarations: its declared-name list is a sublist of the input's. -/
theorem drStmts_declaredNames_sublist (bound : List Ident) : ∀ ss : List (Stmt Op),
    List.Sublist (declaredNamesStmts (drStmts bound ss)) (declaredNamesStmts ss)
  | [] => List.Sublist.refl _
  | s :: rest => by
      cases s with
      | letDecl xs val =>
          cases xs with
          | nil =>
              simp only [drStmts, declaredNamesStmts]
              exact (List.Sublist.refl _).append
                (drStmts_declaredNames_sublist _ rest)
          | cons x xs =>
              cases xs with
              | cons y ys =>
                  simp only [drStmts, declaredNamesStmts]
                  exact (List.Sublist.refl _).append
                    (drStmts_declaredNames_sublist _ rest)
              | nil =>
                  cases val with
                  | some e =>
                      simp only [drStmts, declaredNamesStmts]
                      exact (List.Sublist.refl _).append
                        (drStmts_declaredNames_sublist _ rest)
                  | none =>
                      cases rest with
                      | nil =>
                          simp only [drStmts, declaredNamesStmts]
                          exact (List.Sublist.refl _).append
                            (drStmts_declaredNames_sublist (x :: bound) [])
                      | cons next tail =>
                          cases next with
                          | block body =>
                              by_cases hrem :
                                  removableResult bound x body tail = true
                              · rw [drStmts, if_pos hrem]
                                simp only [declaredNamesStmts]
                                exact (List.sublist_append_right _ _).trans
                                  (List.sublist_append_right _ _)
                              · rw [drStmts, if_neg hrem]
                                simp only [declaredNamesStmts]
                                exact (List.Sublist.refl _).append
                                  (drStmts_declaredNames_sublist _
                                    (.block body :: tail))
                          | funDef n ps rs body =>
                              simp only [drStmts, declaredNamesStmts]
                              exact (List.Sublist.refl _).append
                                (drStmts_declaredNames_sublist _
                                  (.funDef n ps rs body :: tail))
                          | letDecl ys rhs =>
                              simp only [drStmts, declaredNamesStmts]
                              exact (List.Sublist.refl _).append
                                (drStmts_declaredNames_sublist _
                                  (.letDecl ys rhs :: tail))
                          | assign ys rhs =>
                              simp only [drStmts, declaredNamesStmts]
                              exact (List.Sublist.refl _).append
                                (drStmts_declaredNames_sublist _
                                  (.assign ys rhs :: tail))
                          | cond c body =>
                              simp only [drStmts, declaredNamesStmts]
                              exact (List.Sublist.refl _).append
                                (drStmts_declaredNames_sublist _
                                  (.cond c body :: tail))
                          | switch c cases dflt =>
                              simp only [drStmts, declaredNamesStmts]
                              exact (List.Sublist.refl _).append
                                (drStmts_declaredNames_sublist _
                                  (.switch c cases dflt :: tail))
                          | forLoop init c post body =>
                              simp only [drStmts, declaredNamesStmts]
                              exact (List.Sublist.refl _).append
                                (drStmts_declaredNames_sublist _
                                  (.forLoop init c post body :: tail))
                          | exprStmt e =>
                              simp only [drStmts, declaredNamesStmts]
                              exact (List.Sublist.refl _).append
                                (drStmts_declaredNames_sublist _
                                  (.exprStmt e :: tail))
                          | «break» =>
                              simp only [drStmts, declaredNamesStmts]
                              exact (List.Sublist.refl _).append
                                (drStmts_declaredNames_sublist _ (.break :: tail))
                          | «continue» =>
                              simp only [drStmts, declaredNamesStmts]
                              exact (List.Sublist.refl _).append
                                (drStmts_declaredNames_sublist _
                                  (.continue :: tail))
                          | leave =>
                              simp only [drStmts, declaredNamesStmts]
                              exact (List.Sublist.refl _).append
                                (drStmts_declaredNames_sublist _ (.leave :: tail))
      | block body =>
          simp only [drStmts, declaredNamesStmts]
          exact (drStmt_declaredNames_sublist bound (.block body)).append
            (drStmts_declaredNames_sublist bound rest)
      | funDef n ps rs body =>
          simp only [drStmts, declaredNamesStmts]
          exact (drStmt_declaredNames_sublist bound (.funDef n ps rs body)).append
            (drStmts_declaredNames_sublist bound rest)
      | assign xs e =>
          simp only [drStmts, declaredNamesStmts]
          exact (drStmt_declaredNames_sublist bound (.assign xs e)).append
            (drStmts_declaredNames_sublist bound rest)
      | cond c body =>
          simp only [drStmts, declaredNamesStmts]
          exact (drStmt_declaredNames_sublist bound (.cond c body)).append
            (drStmts_declaredNames_sublist bound rest)
      | switch c cases dflt =>
          simp only [drStmts, declaredNamesStmts]
          exact (drStmt_declaredNames_sublist bound (.switch c cases dflt)).append
            (drStmts_declaredNames_sublist bound rest)
      | forLoop init c post body =>
          simp only [drStmts, declaredNamesStmts]
          exact (drStmt_declaredNames_sublist bound
            (.forLoop init c post body)).append
            (drStmts_declaredNames_sublist bound rest)
      | exprStmt e =>
          simp only [drStmts, declaredNamesStmts]
          exact (drStmt_declaredNames_sublist bound (.exprStmt e)).append
            (drStmts_declaredNames_sublist bound rest)
      | «break» =>
          simp only [drStmts, declaredNamesStmts]
          exact (drStmt_declaredNames_sublist bound .break).append
            (drStmts_declaredNames_sublist bound rest)
      | «continue» =>
          simp only [drStmts, declaredNamesStmts]
          exact (drStmt_declaredNames_sublist bound .continue).append
            (drStmts_declaredNames_sublist bound rest)
      | leave =>
          simp only [drStmts, declaredNamesStmts]
          exact (drStmt_declaredNames_sublist bound .leave).append
            (drStmts_declaredNames_sublist bound rest)

/-- `drCases` only removes declarations from each `switch` arm body. -/
theorem drCases_declaredNames_sublist (bound : List Ident) :
    ∀ cs : List (Literal × Block Op),
    List.Sublist (declaredNamesCases (drCases bound cs)) (declaredNamesCases cs)
  | [] => List.Sublist.refl _
  | (l, b) :: rest => by
      simp only [drCases, declaredNamesCases]
      exact (drStmts_declaredNames_sublist bound b).append
        (drCases_declaredNames_sublist bound rest)

/-- `drDflt` only removes declarations from a `switch` default body. -/
theorem drDflt_declaredNames_sublist (bound : List Ident) :
    ∀ d : Option (Block Op),
    List.Sublist (declaredNamesDflt (drDflt bound d)) (declaredNamesDflt d)
  | none => List.Sublist.refl _
  | some b => by
      simp only [drDflt, declaredNamesDflt]
      exact drStmts_declaredNames_sublist bound b

end

end DeadResults

/-! ## `deadPure` shrinks the declared-name list -/

section DeadPure

mutual

/-- `dpStmt` never introduces a declared name. -/
theorem dpStmt_declaredNames_sublist (bound : List Ident) : ∀ s : Stmt Op,
    List.Sublist (declaredNamesStmt (dpStmt bound s)) (declaredNamesStmt s)
  | .block body => by
      simp only [dpStmt, declaredNamesStmt]
      exact dpStmts_declaredNames_sublist bound body
  | .funDef n ps rs body => by
      simp only [dpStmt, declaredNamesStmt]
      exact ((List.Sublist.refl (ps ++ rs)).append
        (dpStmts_declaredNames_sublist (ps ++ rs) body)).cons_cons n
  | .cond c body => by
      simp only [dpStmt, declaredNamesStmt]
      exact dpStmts_declaredNames_sublist bound body
  | .switch c cases dflt => by
      simp only [dpStmt, declaredNamesStmt]
      exact (dpCases_declaredNames_sublist bound cases).append
        (dpDflt_declaredNames_sublist bound dflt)
  | .forLoop init c post body => by
      simp only [dpStmt, declaredNamesStmt]
      exact ((List.Sublist.refl (declaredNamesStmts init)).append
        (dpStmts_declaredNames_sublist bound post)).append
        (dpStmts_declaredNames_sublist bound body)
  | .letDecl _ _ => List.Sublist.refl _
  | .assign _ _ => List.Sublist.refl _
  | .exprStmt _ => List.Sublist.refl _
  | .break => List.Sublist.refl _
  | .continue => List.Sublist.refl _
  | .leave => List.Sublist.refl _

/-- `dpStmts` (the block transform behind `deadPure.run`) only removes
declarations: its declared-name list is a sublist of the input's. -/
theorem dpStmts_declaredNames_sublist (bound : List Ident) : ∀ ss : List (Stmt Op),
    List.Sublist (declaredNamesStmts (dpStmts bound ss)) (declaredNamesStmts ss)
  | [] => List.Sublist.refl _
  | s :: rest => by
      -- `cases s` first so the head is concrete: then `simp only [dpStmts]`
      -- reduces the inner `match`, leaving a single removal `if` for `split`.
      -- In the removal branch the whole statement disappears; in the kept
      -- branch either a `let`'s (unchanged) declared names sit in front of a
      -- shrunk tail, or a structural statement shrinks via `dpStmt`.
      cases s with
      | letDecl xs val =>
          simp only [dpStmts]
          split
          · refine (dpStmts_declaredNames_sublist bound rest).trans ?_
            simp only [declaredNamesStmts]
            exact List.sublist_append_right _ _
          · simp only [declaredNamesStmts]
            exact (List.Sublist.refl _).append
              (dpStmts_declaredNames_sublist (xs ++ bound) rest)
      | block body =>
          simp only [dpStmts]
          split
          · refine (dpStmts_declaredNames_sublist bound rest).trans ?_
            simp only [declaredNamesStmts]
            exact List.sublist_append_right _ _
          · simp only [declaredNamesStmts]
            exact (dpStmt_declaredNames_sublist bound (.block body)).append
              (dpStmts_declaredNames_sublist bound rest)
      | funDef n ps rs body =>
          simp only [dpStmts]
          split
          · refine (dpStmts_declaredNames_sublist bound rest).trans ?_
            simp only [declaredNamesStmts]
            exact List.sublist_append_right _ _
          · simp only [declaredNamesStmts]
            exact (dpStmt_declaredNames_sublist bound
              (.funDef n ps rs body)).append
              (dpStmts_declaredNames_sublist bound rest)
      | assign xs e =>
          simp only [dpStmts]
          split
          · refine (dpStmts_declaredNames_sublist bound rest).trans ?_
            simp only [declaredNamesStmts]
            exact List.sublist_append_right _ _
          · simp only [declaredNamesStmts]
            exact (dpStmt_declaredNames_sublist bound (.assign xs e)).append
              (dpStmts_declaredNames_sublist bound rest)
      | cond c body =>
          simp only [dpStmts]
          split
          · refine (dpStmts_declaredNames_sublist bound rest).trans ?_
            simp only [declaredNamesStmts]
            exact List.sublist_append_right _ _
          · simp only [declaredNamesStmts]
            exact (dpStmt_declaredNames_sublist bound (.cond c body)).append
              (dpStmts_declaredNames_sublist bound rest)
      | switch c cases dflt =>
          simp only [dpStmts]
          split
          · refine (dpStmts_declaredNames_sublist bound rest).trans ?_
            simp only [declaredNamesStmts]
            exact List.sublist_append_right _ _
          · simp only [declaredNamesStmts]
            exact (dpStmt_declaredNames_sublist bound
              (.switch c cases dflt)).append
              (dpStmts_declaredNames_sublist bound rest)
      | forLoop init c post body =>
          simp only [dpStmts]
          split
          · refine (dpStmts_declaredNames_sublist bound rest).trans ?_
            simp only [declaredNamesStmts]
            exact List.sublist_append_right _ _
          · simp only [declaredNamesStmts]
            exact (dpStmt_declaredNames_sublist bound
              (.forLoop init c post body)).append
              (dpStmts_declaredNames_sublist bound rest)
      | exprStmt e =>
          simp only [dpStmts]
          split
          · refine (dpStmts_declaredNames_sublist bound rest).trans ?_
            simp only [declaredNamesStmts]
            exact List.sublist_append_right _ _
          · simp only [declaredNamesStmts]
            exact (dpStmt_declaredNames_sublist bound (.exprStmt e)).append
              (dpStmts_declaredNames_sublist bound rest)
      | «break» =>
          simp only [dpStmts]
          split
          · refine (dpStmts_declaredNames_sublist bound rest).trans ?_
            simp only [declaredNamesStmts]
            exact List.sublist_append_right _ _
          · simp only [declaredNamesStmts]
            exact (dpStmt_declaredNames_sublist bound .break).append
              (dpStmts_declaredNames_sublist bound rest)
      | «continue» =>
          simp only [dpStmts]
          split
          · refine (dpStmts_declaredNames_sublist bound rest).trans ?_
            simp only [declaredNamesStmts]
            exact List.sublist_append_right _ _
          · simp only [declaredNamesStmts]
            exact (dpStmt_declaredNames_sublist bound .continue).append
              (dpStmts_declaredNames_sublist bound rest)
      | leave =>
          simp only [dpStmts]
          split
          · refine (dpStmts_declaredNames_sublist bound rest).trans ?_
            simp only [declaredNamesStmts]
            exact List.sublist_append_right _ _
          · simp only [declaredNamesStmts]
            exact (dpStmt_declaredNames_sublist bound .leave).append
              (dpStmts_declaredNames_sublist bound rest)

/-- `dpCases` only removes declarations from each `switch` arm body. -/
theorem dpCases_declaredNames_sublist (bound : List Ident) :
    ∀ cs : List (Literal × Block Op),
    List.Sublist (declaredNamesCases (dpCases bound cs)) (declaredNamesCases cs)
  | [] => List.Sublist.refl _
  | (l, b) :: rest => by
      simp only [dpCases, declaredNamesCases]
      exact (dpStmts_declaredNames_sublist bound b).append
        (dpCases_declaredNames_sublist bound rest)

/-- `dpDflt` only removes declarations from a `switch` default body. -/
theorem dpDflt_declaredNames_sublist (bound : List Ident) :
    ∀ d : Option (Block Op),
    List.Sublist (declaredNamesDflt (dpDflt bound d)) (declaredNamesDflt d)
  | none => List.Sublist.refl _
  | some b => by
      simp only [dpDflt, declaredNamesDflt]
      exact dpStmts_declaredNames_sublist bound b

end

end DeadPure

/-! ## Invariant preservation -/

variable {calls : ExternalCalls} {creates : ExternalCreates}

local notation "D" => evmWithExternal calls creates

/-- The dead read-only result-region elimination pass preserves
`NormalForm.UniqueNames`: it only removes declarations, so the declared-name
list stays a sublist of a `Nodup` list and hence stays `Nodup`. -/
theorem deadResults_preserves_uniqueNames :
    Optimizer.Preserves NormalForm.UniqueNames
      (deadResults (calls := calls) (creates := creates)).run :=
  fun b hb =>
    List.Nodup.sublist (drStmts_declaredNames_sublist [] b) hb

/-- The dead pure-binding elimination pass preserves `NormalForm.UniqueNames`,
for the same reason: it only removes declarations. -/
theorem deadPure_preserves_uniqueNames :
    Optimizer.Preserves NormalForm.UniqueNames
      (deadPure (calls := calls) (creates := creates)).run :=
  fun b hb =>
    List.Nodup.sublist (dpStmts_declaredNames_sublist [] b) hb

end YulEvmCompiler.Optimizer.NormalForm
