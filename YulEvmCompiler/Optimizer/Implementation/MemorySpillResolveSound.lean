import YulEvmCompiler.ObjectResolve
import YulEvmCompiler.Optimizer.Implementation.MemorySpillSelect
set_option warningAsError true
/-!
# Object-layout resolution and memory spilling

The memory-spill rewrite neither introduces nor removes object-layout
references.  Consequently concrete `dataoffset`/`datasize` resolution may be
performed before or after every part of the rewrite, including generated
function entry/exit copies and tuple temporaries.  The final corollary records
the exact specialization to the guard-resolved blocks used by spill
certificates.
-/

namespace YulEvmCompiler.Optimizer.MemorySpillSelect

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler
open MemorySpill

mutual
  theorem resolveForLayout_rewriteExpr (L : EVM.Layout) (slots : SlotMap)
      (owner : Owner) (e : Expr Op) :
      resolveForLayoutExpr L (rewriteExpr slots owner e) =
        rewriteExpr slots owner (resolveForLayoutExpr L e) := by
    cases e with
    | lit l => rfl
    | var x =>
        cases h : slotFor? slots owner x <;>
          simp [rewriteExpr, h, load, word, resolveForLayoutExpr,
            resolveForLayoutExprs]
    | call f args =>
        simp [rewriteExpr, resolveForLayoutExpr,
          resolveForLayout_rewriteArgs L slots owner args]
    | builtin op args =>
        cases args with
        | nil =>
            cases op <;> rfl
        | cons e rest =>
            cases rest with
            | cons e' rest =>
                cases op <;>
                  simp [rewriteExpr, rewriteArgs, resolveForLayoutExpr,
                    resolveForLayoutExprs,
                    resolveForLayout_rewriteExpr L slots owner e,
                    resolveForLayout_rewriteExpr L slots owner e',
                    resolveForLayout_rewriteArgs L slots owner rest]
            | nil =>
                cases e with
                | lit l =>
                    cases l <;> cases op <;> rfl
                | var x =>
                    cases h : slotFor? slots owner x <;> cases op <;>
                      simp [rewriteExpr, rewriteArgs, h, load, word,
                        resolveForLayoutExpr, resolveForLayoutExprs]
                | builtin innerOp innerArgs =>
                    have hi := resolveForLayout_rewriteExpr L slots owner
                      (.builtin innerOp innerArgs)
                    cases op <;>
                      simpa [rewriteExpr, rewriteArgs, resolveForLayoutExpr,
                        resolveForLayoutExprs] using hi
                | call f innerArgs =>
                    have hi := resolveForLayout_rewriteExpr L slots owner
                      (.call f innerArgs)
                    cases op <;>
                      simpa [rewriteExpr, rewriteArgs, resolveForLayoutExpr,
                        resolveForLayoutExprs] using hi

  theorem resolveForLayout_rewriteArgs (L : EVM.Layout) (slots : SlotMap)
      (owner : Owner) (args : List (Expr Op)) :
      resolveForLayoutExprs L (rewriteArgs slots owner args) =
        rewriteArgs slots owner (resolveForLayoutExprs L args) := by
    cases args with
    | nil => rfl
    | cons e rest =>
        simp [rewriteArgs, resolveForLayoutExprs,
          resolveForLayout_rewriteExpr L slots owner e,
          resolveForLayout_rewriteArgs L slots owner rest]
end

private theorem resolveForLayoutStmts_append (L : EVM.Layout) (a b : Block Op) :
    resolveForLayoutStmts L (a ++ b) =
      resolveForLayoutStmts L a ++ resolveForLayoutStmts L b := by
  induction a with
  | nil => simp
  | cons s rest ih => simp [ih]

private theorem resolveForLayout_store (L : EVM.Layout) (slot : Nat)
    (e : Expr Op) :
    resolveForLayoutStmt L (store slot e) =
      store slot (resolveForLayoutExpr L e) := by
  simp [store, word, resolveForLayoutExpr, resolveForLayoutExprs]

private theorem resolveForLayout_initParams (L : EVM.Layout) (slots : SlotMap)
    (owner : Owner) (ps : List Ident) :
    resolveForLayoutStmts L (initParams slots owner ps) =
      initParams slots owner ps := by
  change resolveForLayoutStmts L
      (ps.filterMap fun p => (slotFor? slots owner p).map fun slot =>
        store slot (.var p)) =
    ps.filterMap fun p => (slotFor? slots owner p).map fun slot =>
      store slot (.var p)
  induction ps with
  | nil => simp
  | cons p rest ih =>
      cases h : slotFor? slots owner p
      · simpa [h] using ih
      · simp [h, resolveForLayout_store, ih, resolveForLayoutExpr]

private theorem resolveForLayout_initReturns (L : EVM.Layout) (slots : SlotMap)
    (owner : Owner) (rs : List Ident) :
    resolveForLayoutStmts L (initReturns slots owner rs) =
      initReturns slots owner rs := by
  change resolveForLayoutStmts L
      (rs.filterMap fun r => (slotFor? slots owner r).map fun slot =>
        store slot (word 0)) =
    rs.filterMap fun r => (slotFor? slots owner r).map fun slot =>
      store slot (word 0)
  induction rs with
  | nil => simp
  | cons r rest ih =>
      cases h : slotFor? slots owner r
      · simpa [h] using ih
      · rw [List.filterMap_cons, h]
        simp only [Option.map_some, resolveForLayoutStmts_cons]
        rw [resolveForLayout_store, ih]
        rfl

private theorem resolveForLayout_copyBackReturns (L : EVM.Layout)
    (slots : SlotMap) (owner : Owner) (rs : List Ident) :
    resolveForLayoutStmts L (copyBackReturns slots owner rs) =
      copyBackReturns slots owner rs := by
  change resolveForLayoutStmts L
      (rs.filterMap fun r => (slotFor? slots owner r).map fun slot =>
        .assign [r] (load slot)) =
    rs.filterMap fun r => (slotFor? slots owner r).map fun slot =>
      .assign [r] (load slot)
  induction rs with
  | nil => simp
  | cons r rest ih =>
      cases h : slotFor? slots owner r
      · simpa [h] using ih
      · rw [List.filterMap_cons, h]
        simp only [Option.map_some, resolveForLayoutStmts_cons]
        rw [ih]
        simp [load, word, resolveForLayoutExpr, resolveForLayoutExprs]

private theorem resolveForLayout_distributeTemps (L : EVM.Layout)
    (targets : List Nat) (temps : List Ident) :
    resolveForLayoutStmts L (distributeTemps targets temps) =
      distributeTemps targets temps := by
  induction targets generalizing temps with
  | nil => simp [distributeTemps]
  | cons target rest ih =>
      cases temps with
      | nil => simp [distributeTemps]
      | cons temp temps =>
          change resolveForLayoutStmts L
              (store target (.var temp) :: distributeTemps rest temps) =
            store target (.var temp) :: distributeTemps rest temps
          simp [resolveForLayout_store, resolveForLayoutExpr, ih]

private theorem resolveForLayout_zeroStores (L : EVM.Layout)
    (targets : List Nat) :
    resolveForLayoutStmts L (targets.map fun target => store target (word 0)) =
      targets.map fun target => store target (word 0) := by
  induction targets with
  | nil => simp
  | cons target rest ih =>
      change resolveForLayoutStmts L
          (store target (word 0) :: rest.map fun target => store target (word 0)) =
        store target (word 0) :: rest.map fun target => store target (word 0)
      rw [resolveForLayoutStmts_cons, resolveForLayout_store, ih]
      rfl

private theorem resolveForLayoutStmts_isEmpty (L : EVM.Layout) (body : Block Op) :
    (resolveForLayoutStmts L body).isEmpty = body.isEmpty := by
  cases body <;> simp

mutual
  theorem resolveForLayout_rewriteStmt (L : EVM.Layout) (slots : SlotMap)
      (owner : Owner) (exitCopies : Block Op) (s : Stmt Op) :
      resolveForLayoutStmts L (rewriteStmt slots owner exitCopies s) =
        rewriteStmt slots owner (resolveForLayoutStmts L exitCopies)
          (resolveForLayoutStmt L s) := by
    cases s with
    | block body =>
        simp [rewriteStmt, resolveForLayout_rewriteStmts L slots owner exitCopies body]
    | funDef f ps rs body =>
        simp [rewriteStmt, resolveForLayoutStmts_append,
          resolveForLayout_initParams, resolveForLayout_initReturns,
          resolveForLayout_copyBackReturns,
          resolveForLayout_rewriteStmts L slots (some f)
            (copyBackReturns slots (some f) rs) body]
    | letDecl xs val =>
        cases xs with
        | nil =>
            cases val <;>
              simp [rewriteStmt, targetSlots?, resolveForLayout_rewriteExpr,
                resolveForLayout_distributeTemps]
        | cons x rest =>
            cases rest with
            | nil =>
                cases h : slotFor? slots owner x <;> cases val <;>
                  simp [rewriteStmt, h, resolveForLayout_rewriteExpr,
                    resolveForLayout_store, word, resolveForLayoutExpr]
            | cons y ys =>
                cases h : targetSlots? slots owner (x :: y :: ys) <;>
                  cases val <;>
                  simp [rewriteStmt, h, resolveForLayout_rewriteExpr,
                    resolveForLayout_distributeTemps,
                    resolveForLayout_zeroStores]
    | assign xs e =>
        cases xs with
        | nil =>
            simp [rewriteStmt, targetSlots?, resolveForLayout_rewriteExpr,
              resolveForLayout_distributeTemps]
        | cons x rest =>
            cases rest with
            | nil =>
                cases h : slotFor? slots owner x <;>
                  simp [rewriteStmt, h, resolveForLayout_rewriteExpr,
                    resolveForLayout_store]
            | cons y ys =>
                cases h : targetSlots? slots owner (x :: y :: ys) <;>
                  simp [rewriteStmt, h, resolveForLayout_rewriteExpr,
                    resolveForLayout_distributeTemps]
    | cond c body =>
        simp [rewriteStmt, resolveForLayout_rewriteExpr,
          resolveForLayout_rewriteStmts L slots owner exitCopies body]
    | «switch» c cases dflt =>
        cases dflt <;>
          simp [rewriteStmt, resolveForLayout_rewriteExpr,
            resolveForLayout_rewriteCases L slots owner exitCopies cases,
            resolveForLayout_rewriteStmts]
    | forLoop init c post body =>
        simp [rewriteStmt, resolveForLayout_rewriteExpr,
          resolveForLayout_rewriteStmts]
    | exprStmt e =>
        simp [rewriteStmt, resolveForLayout_rewriteExpr]
    | «break» => simp [rewriteStmt]
    | «continue» => simp [rewriteStmt]
    | «leave» =>
        cases h : exitCopies.isEmpty <;>
          simp [rewriteStmt, h, resolveForLayoutStmts_append,
            resolveForLayoutStmts_isEmpty]

  theorem resolveForLayout_rewriteStmts (L : EVM.Layout) (slots : SlotMap)
      (owner : Owner) (exitCopies body : Block Op) :
      resolveForLayoutStmts L (rewriteStmts slots owner exitCopies body) =
        rewriteStmts slots owner (resolveForLayoutStmts L exitCopies)
          (resolveForLayoutStmts L body) := by
    cases body with
    | nil => simp [rewriteStmts]
    | cons s rest =>
        simp [rewriteStmts, resolveForLayoutStmts_append,
          resolveForLayout_rewriteStmt L slots owner exitCopies s,
          resolveForLayout_rewriteStmts L slots owner exitCopies rest]

  theorem resolveForLayout_rewriteCases (L : EVM.Layout) (slots : SlotMap)
      (owner : Owner) (exitCopies : Block Op)
      (cases : List (Literal × Block Op)) :
      resolveForLayoutCases L (rewriteCases slots owner exitCopies cases) =
        rewriteCases slots owner (resolveForLayoutStmts L exitCopies)
          (resolveForLayoutCases L cases) := by
    cases cases with
    | nil => simp [rewriteCases, resolveForLayoutCases]
    | cons head rest =>
        obtain ⟨l, body⟩ := head
        simp [rewriteCases, resolveForLayoutCases,
          resolveForLayout_rewriteStmts L slots owner exitCopies body,
          resolveForLayout_rewriteCases L slots owner exitCopies rest]
end

/-- The commutation theorem applies unchanged to the guard-resolved tree used
by a successful spill certificate. -/
theorem resolveForLayout_rewriteMemoryGuardStmts (L : EVM.Layout)
    (slots : SlotMap) (owner : Owner) (base reserved : Nat)
    (exitCopies body : Block Op) :
    resolveForLayoutStmts L
        (rewriteStmts slots owner
          (resolveMemoryGuardStmts base reserved exitCopies)
          (resolveMemoryGuardStmts base reserved body)) =
      rewriteStmts slots owner
        (resolveForLayoutStmts L
          (resolveMemoryGuardStmts base reserved exitCopies))
        (resolveForLayoutStmts L
          (resolveMemoryGuardStmts base reserved body)) :=
  resolveForLayout_rewriteStmts L slots owner
    (resolveMemoryGuardStmts base reserved exitCopies)
    (resolveMemoryGuardStmts base reserved body)

end YulEvmCompiler.Optimizer.MemorySpillSelect
