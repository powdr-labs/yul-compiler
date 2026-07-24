import YulEvmCompiler.Optimizer.Implementation.Normalization.Disambiguate
import YulEvmCompiler.Optimizer.Implementation.Normalization.NormalForm
/-!
# Disambiguation establishes `NormalForm.UniqueNames`

The `disambiguate` pass's *syntactic* normal-form obligation: after it, no name
is declared twice anywhere — `NormalForm.UniqueNames (disambiguate b)`.

Bridges the pass's own `Disambiguated` (proved in `Disambiguate.lean` with the
collector `declaredBlock`, which lists a block's top-level function names first)
to the shared spec's `NormalForm.UniqueNames` (collector `declaredNamesStmts`,
function names inline). The two enumerate the same declared names in a different
order, hence are `List.Perm`, and `Nodup` is permutation-invariant.
-/

namespace YulEvmCompiler.Optimizer.Normalize

open YulSemantics
open scoped List

variable {Op : Type}

/-- Swap the two inner blocks of a four-way concatenation, up to permutation. -/
theorem perm_interchange {α} (A B C D : List α) :
    (A ++ B) ++ (C ++ D) ~ (A ++ C) ++ (B ++ D) := by
  simp only [List.append_assoc]
  refine List.Perm.append_left A ?_
  rw [← List.append_assoc, ← List.append_assoc]
  exact List.Perm.append_right D List.perm_append_comm

mutual
theorem declaredNamesStmts_perm :
    ∀ ss : List (Stmt Op), (NormalForm.declaredNamesStmts ss).Perm (declaredBlock ss)
  | [] => by simp [NormalForm.declaredNamesStmts, declaredBlock, declaredInner, funNames]
  | s :: rest => by
      have ihs := declaredNamesStmt_perm s
      have ihrest := declaredNamesStmts_perm rest
      have hcombine :
          (NormalForm.declaredNamesStmt s ++ NormalForm.declaredNamesStmts rest).Perm
            ((funNames [s] ++ funNames rest) ++ (declaredInnerS s ++ declaredInner rest)) :=
        (ihs.append ihrest).trans (perm_interchange _ _ _ _)
      have hgoal : declaredBlock (s :: rest)
          = (funNames [s] ++ funNames rest) ++ (declaredInnerS s ++ declaredInner rest) := by
        rw [declaredBlock, funNames_cons_eq, declaredInner, List.append_assoc]
      rw [hgoal]
      exact hcombine
theorem declaredNamesStmt_perm :
    ∀ s : Stmt Op, (NormalForm.declaredNamesStmt s).Perm (funNames [s] ++ declaredInnerS s)
  | .funDef fn ps rs body => by
      have ihb := declaredNamesStmts_perm body
      simp only [NormalForm.declaredNamesStmt, funNames, declaredInnerS, List.cons_append,
        List.nil_append]
      exact List.Perm.cons fn (List.Perm.append_left (ps ++ rs) ihb)
  | .block body => by
      have ihb := declaredNamesStmts_perm body
      simpa only [NormalForm.declaredNamesStmt, funNames, declaredInnerS, declaredBlock,
        List.nil_append] using ihb
  | .cond c body => by
      have ihb := declaredNamesStmts_perm body
      simpa only [NormalForm.declaredNamesStmt, funNames, declaredInnerS, declaredBlock,
        List.nil_append] using ihb
  | .letDecl vars val => by simp [NormalForm.declaredNamesStmt, funNames, declaredInnerS]
  | .assign vars e => by simp [NormalForm.declaredNamesStmt, funNames, declaredInnerS]
  | .exprStmt e => by simp [NormalForm.declaredNamesStmt, funNames, declaredInnerS]
  | .«break» => by simp [NormalForm.declaredNamesStmt, funNames, declaredInnerS]
  | .«continue» => by simp [NormalForm.declaredNamesStmt, funNames, declaredInnerS]
  | .leave => by simp [NormalForm.declaredNamesStmt, funNames, declaredInnerS]
  | .switch c cases dflt => by
      have ihc := declaredNamesCases_perm cases
      have ihd := declaredNamesDflt_perm dflt
      simp only [NormalForm.declaredNamesStmt, funNames, declaredInnerS, List.nil_append]
      exact ihc.append ihd
  | .forLoop init c post body => by
      have ihi := declaredNamesStmts_perm init
      have ihp := declaredNamesStmts_perm post
      have ihbo := declaredNamesStmts_perm body
      simp only [NormalForm.declaredNamesStmt, funNames, declaredInnerS, List.nil_append]
      -- theirs: dNS init ++ dNS post ++ dNS body ; mine: (di ++ db) ++ dp (defeq to declaredBlock)
      refine ((ihi.append ihp).append ihbo).trans ?_
      calc (declaredBlock init ++ declaredBlock post) ++ declaredBlock body
          ~ declaredBlock init ++ (declaredBlock post ++ declaredBlock body) := by
              rw [List.append_assoc]
        _ ~ declaredBlock init ++ (declaredBlock body ++ declaredBlock post) :=
              List.Perm.append_left _ List.perm_append_comm
        _ = (declaredBlock init ++ declaredBlock body) ++ declaredBlock post := by
              rw [List.append_assoc]
theorem declaredNamesCases_perm :
    ∀ cs : List (Literal × List (Stmt Op)),
      (NormalForm.declaredNamesCases cs).Perm (declaredCases cs)
  | [] => by simp [NormalForm.declaredNamesCases, declaredCases]
  | (l, body) :: rest => by
      have ihb := declaredNamesStmts_perm body
      have ihr := declaredNamesCases_perm rest
      simp only [NormalForm.declaredNamesCases, declaredCases]
      exact ihb.append ihr
theorem declaredNamesDflt_perm :
    ∀ d : Option (List (Stmt Op)), (NormalForm.declaredNamesDflt d).Perm (declaredDflt d)
  | none => by simp [NormalForm.declaredNamesDflt, declaredDflt]
  | some body => by
      simpa only [NormalForm.declaredNamesDflt, declaredDflt, declaredBlock]
        using declaredNamesStmts_perm body
end

/-- **The disambiguation pass establishes the shared `UniqueNames` normal form.**
For a well-formed input, after `disambiguate` no name is declared twice anywhere. -/
theorem disambiguate_uniqueNames (b : Block Op) (h : WellFormed b) :
    NormalForm.UniqueNames (disambiguate b) :=
  ((declaredNamesStmts_perm (disambiguate b)).nodup_iff).mpr (disambiguate_disambiguated b h)

end YulEvmCompiler.Optimizer.Normalize
