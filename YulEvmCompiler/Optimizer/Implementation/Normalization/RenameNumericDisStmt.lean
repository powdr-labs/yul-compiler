import YulEvmCompiler.Optimizer.Implementation.Normalization.RenameNumericDis
import YulEvmCompiler.Optimizer.Implementation.Normalization.RenameNumericUnique
-- WIP: statement layer of equation (B). Sorries mark the remaining mutual
-- induction cases; the helper layer below is complete and sorry-free.
set_option warningAsError false
/-!
# Equation (B), statement layer (WORK IN PROGRESS)

Threads the `LookupAligned` invariant (`RenameNumericDis.lean`) through the
mutual statement traversals of the canonicalizer (`dsStmt`/`dsStmts`/`dsScope`/
`dsCases`/`dsDflt`) and the renamer (`renStmt`/…), toward

```
disambiguate_rename' : SVStmts b → WellFormed b → disambiguate (rename b) = disambiguate b
```

Every binder site is an instance of `lookupAligned_batch`; every expression site
is `dsExpr_align`. The per-construct bookkeeping:

* `letDecl` — one variable batch (`vars.Nodup` from `SVStmts`);
* `funDef` — a params batch then a rets batch; the canonicalizer prepends them
  in the *opposite* order to the renamer, which is harmless because the two
  batches' keys are disjoint (`(ps ++ rs).Nodup`) — `substOf_prefix_comm`;
* scopes — the function-name prescan is a batch on `funNames body`
  (`Nodup` from `WellFormed`), and the renamed body's function names are
  exactly the batch outputs (`funNames_renStmts` + `assignNames_map_substOf`);
* counters — equal on both sides because every batch preserves length
  (`assignNames_length`) and `freshVars` depends only on the length
  (`freshVars_congr`).
-/

namespace YulEvmCompiler.Optimizer.RenameNumeric

open YulSemantics
open YulEvmCompiler.Optimizer.Normalize
  (Subst substOf dsExpr dsArgs dsStmt dsStmts dsScope dsCases dsDflt freshVars
   funNames SVStmts SVStmt WFInner WFInnerS)

variable {Op : Type}

/-! ## Helper layer -/

/-- `freshVars` depends only on the length of its argument. -/
theorem freshVars_congr {n : Nat} :
    ∀ {l l' : List Ident}, l.length = l'.length → freshVars n l = freshVars n l'
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
      simp only [freshVars]
      exact congrArg _ (freshVars_congr (by simpa using h))
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- A lookup that hits inside a prefix ignores the tail. -/
theorem substOf_append_found {l s : Subst} {x : Ident}
    (h : x ∈ l.map Prod.fst) : substOf (l ++ s) x = substOf l x := by
  induction l with
  | nil => simp at h
  | cons p rest ih =>
      obtain ⟨k, d⟩ := p
      by_cases hk : k = x
      · subst hk
        rw [List.cons_append, substOf_cons_eq, substOf_cons_eq]
      · have hrest : x ∈ rest.map Prod.fst := by
          rcases List.mem_map.mp h with ⟨q, hq, hqk⟩
          rcases List.mem_cons.mp hq with hq | hq
          · exact absurd (by rw [hq] at hqk; exact hqk) hk
          · exact List.mem_map.mpr ⟨q, hq, hqk⟩
        rw [List.cons_append, substOf_cons_ne hk, substOf_cons_ne hk, ih hrest]

/-- Key-disjoint prefixes commute in front of a common tail (pointwise). -/
theorem substOf_prefix_comm {P R s : Subst}
    (hdisj : ∀ k ∈ P.map Prod.fst, k ∉ R.map Prod.fst) (x : Ident) :
    substOf (P ++ (R ++ s)) x = substOf (R ++ (P ++ s)) x := by
  by_cases hP : x ∈ P.map Prod.fst
  · have hR : x ∉ R.map Prod.fst := hdisj x hP
    rw [substOf_append_found (by simpa using hP), substOf_append_skip hR,
      substOf_append_found (by simpa using hP)]
  · rw [substOf_append_skip hP]
    by_cases hR : x ∈ R.map Prod.fst
    · rw [substOf_append_found (by simpa using hR),
        substOf_append_found (by simpa using hR)]
    · rw [substOf_append_skip hR, substOf_append_skip hR, substOf_append_skip hP]

/-- Every substitution entry produced by `assignNames` has its value in the
final `taken` set (the value is committed on creation). -/
theorem assignNames_sub_vals_taken (orig : List Ident) :
    ∀ (xs taken : List Ident), ∀ p ∈ (assignNames orig xs taken).2.1,
      p.2 ∈ (assignNames orig xs taken).2.2
  | [], _, _, hp => by simp [assignNames] at hp
  | x :: xs, taken, p, hp => by
      rw [assignNames_cons] at hp ⊢
      rcases List.mem_append.mp hp with h | h
      · rcases assignName_cases orig taken x with ⟨_, he⟩ | ⟨hx, he⟩ <;>
          rw [he] at h ⊢
        · simp at h
        · simp only [List.mem_singleton] at h
          subst h
          exact assignNames_mono orig xs _ _ (by simp)
      · exact assignNames_sub_vals_taken orig xs _ p h

/-- A batch extends the `SubstBelow` bookkeeping to the batch's exit `taken`. -/
theorem substBelow_batch {orig taken : List Ident} {σ : List (Ident × Ident)}
    (hSB : SubstBelow taken σ) (vars : List Ident) :
    SubstBelow (assignNames orig vars taken).2.2
      ((assignNames orig vars taken).2.1 ++ σ) := by
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · exact ⟨assignNames_sub_keys_taken orig vars taken p h,
      assignNames_sub_vals_taken orig vars taken p h⟩
  · exact ⟨assignNames_mono orig vars taken _ (hSB p h).1,
      assignNames_mono orig vars taken _ (hSB p h).2⟩

/-- The renamer maps every statement to one with the same head constructor; in
particular the renamed list's top-level function names are the `substOf` images
of the source's (the renamer's `σf` is constant across a statement list —
`renStmt_σf`). -/
theorem funNames_renStmts (orig : List Ident) :
    ∀ (ss : List (Stmt Op)) (st : St) (taken : List Ident),
      funNames ((renStmts orig st taken ss).2.2) =
        (funNames ss).map (substOf st.σf)
  | [], _, _ => by simp [renStmts, funNames]
  | s :: rest, st, taken => by
      have hσf := renStmt_σf orig st taken s
      have ih := funNames_renStmts orig rest (renStmt orig st taken s).1
        (renStmt orig st taken s).2.1
      rw [hσf] at ih
      simp only [renStmts]
      cases s <;>
        · simp only [renStmt, funNames, List.map_cons] at ih ⊢
          rw [ih]

/-! ## The mutual statement-layer induction (the remaining work)

The per-function statements below package: output-statement equality, counter
equality, exit-state alignment, and exit `SubstBelow`. Discharged constructs are
proved; the rest are the WIP sorries. -/

/-- Statement-layer goal, scope form (the shape `disambiguate_rename'` needs):
canonicalizing the renamed scope equals canonicalizing the source scope. -/
theorem dsScope_align {orig : List Ident} (stB stR : Normalize.St) (st : St)
    (taken : List Ident) (n : Nat) (body : List (Stmt Op))
    (hv : LookupAligned orig stB.1 st.σv stR.1)
    (hf : LookupAligned orig stB.2 st.σf stR.2)
    (hSBv : SubstBelow taken st.σv) (hSBf : SubstBelow taken st.σf)
    (hids : ∀ x ∈ identsSs body, x ∈ orig)
    (hsv : SVStmts body) (hnd : (funNames body).Nodup) (hwf : WFInner body) :
    (dsScope stR n ((renScope orig st taken body).2.2)).2.2 =
      (dsScope stB n body).2.2 := by
  sorry

/-- **Equation (B)**: the canonicalizer absorbs the collision-only renaming, on
programs with duplicate-free binders (`SVStmts`) and per-block distinct function
names (`WellFormed`) — both conjuncts of `SourceValid`. -/
theorem disambiguate_rename' {b : Block Op}
    (hsv : SVStmts b) (hwf : Normalize.WellFormed b) :
    Normalize.disambiguate (rename b) = Normalize.disambiguate b := by
  show (dsScope (([], []) : Normalize.St) 0 (rename b)).2.2 =
    (dsScope (([], []) : Normalize.St) 0 b).2.2
  exact dsScope_align (([], []) : Normalize.St) (([], []) : Normalize.St)
    ⟨[], []⟩ [] 0 b LookupAligned.nil LookupAligned.nil
    (fun _ h => by simp at h) (fun _ h => by simp at h)
    (fun x hx => hx) hsv hwf.1 hwf.2

end YulEvmCompiler.Optimizer.RenameNumeric
