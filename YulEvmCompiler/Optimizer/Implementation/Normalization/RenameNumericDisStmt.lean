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

/-! ## More ds-side helpers -/

/-- `dsStmt` never changes the function substitution. -/
theorem dsStmt_snd (st : Normalize.St) (n : Nat) (s : Stmt Op) :
    (dsStmt st n s).1.2 = st.2 := by
  cases s <;> simp [dsStmt]

/-- Pointwise-equal states transport the alignment invariant. -/
theorem lookupAligned_congr {orig : List Ident}
    {sb sb' sr sr' : Subst} {sv : List (Ident × Ident)}
    (hb : ∀ x, substOf sb x = substOf sb' x) (hr : ∀ x, substOf sr x = substOf sr' x)
    (h : LookupAligned orig sb sv sr) : LookupAligned orig sb' sv sr' := by
  intro x hx
  rw [← hb x, ← hr (substOf sv x)]
  exact h x hx

/-- Function names of a scope body occur among its identifiers. -/
theorem funNames_subset_idents :
    ∀ (ss : List (Stmt Op)), ∀ f ∈ funNames ss, f ∈ identsSs ss
  | [], _, hf => by simp [funNames] at hf
  | s :: rest, f, hf => by
      cases s with
      | funDef fn ps rs body =>
          simp only [funNames] at hf
          rcases List.mem_cons.mp hf with h | h
          · subst h
            simp [identsSs, identsS]
          · simp only [identsSs, List.mem_append]
            exact Or.inr (funNames_subset_idents rest f h)
      | _ =>
          simp only [funNames] at hf
          simp only [identsSs, List.mem_append]
          exact Or.inr (funNames_subset_idents rest f hf)

/-! ## The conclusion bundle -/

/-- Conclusions of the statement-layer alignment at one traversal step: equal
canonicalized outputs, equal counters, exit-state alignment (variable and
function sides), and exit-`SubstBelow` bookkeeping. `outB`/`outR` are the
canonicalizer's results on the source and on the renamed program; `stR`/`tk`
are the renamer's exit state and committed set. -/
structure StAligned {α : Type} (orig : List Ident)
    (outB : Normalize.St × Nat × α) (stR : St) (tk : List Ident)
    (outR : Normalize.St × Nat × α) : Prop where
  stmts : outR.2.2 = outB.2.2
  counter : outR.2.1 = outB.2.1
  alignV : LookupAligned orig outB.1.1 stR.σv outR.1.1
  alignF : LookupAligned orig outB.1.2 stR.σf outR.1.2
  belowV : SubstBelow tk stR.σv
  belowF : SubstBelow tk stR.σf

/-! ## The mutual statement-layer induction (the remaining work)

Every binder site is a `lookupAligned_batch` instance; every expression site is
`dsExpr_align`; counters agree by `assignNames_length` + `freshVars_congr`.
The cases still to discharge are the WIP sorries. -/

mutual

/-- Statement-level alignment (see `StAligned`). -/
theorem dsStmt_align {orig : List Ident} :
    ∀ (n : Nat) (taken : List Ident) (sbv sbf srv srf : Subst)
      (σv σf : List (Ident × Ident)) (s : Stmt Op),
      LookupAligned orig sbv σv srv → LookupAligned orig sbf σf srf →
      SubstBelow taken σv → SubstBelow taken σf →
      (∀ x ∈ identsS s, x ∈ orig) → SVStmt s → WFInnerS s →
      StAligned orig (dsStmt (sbv, sbf) n s)
        (renStmt orig ⟨σv, σf⟩ taken s).1 (renStmt orig ⟨σv, σf⟩ taken s).2.1
        (dsStmt (srv, srf) n (renStmt orig ⟨σv, σf⟩ taken s).2.2) ∧
      (∀ y ∈ taken, y ∈ (renStmt orig ⟨σv, σf⟩ taken s).2.1) := by
  sorry

/-- Statement-list alignment. -/
theorem dsStmts_align {orig : List Ident} :
    ∀ (n : Nat) (taken : List Ident) (sbv sbf srv srf : Subst)
      (σv σf : List (Ident × Ident)) (ss : List (Stmt Op)),
      LookupAligned orig sbv σv srv → LookupAligned orig sbf σf srf →
      SubstBelow taken σv → SubstBelow taken σf →
      (∀ x ∈ identsSs ss, x ∈ orig) → SVStmts ss → WFInner ss →
      StAligned orig (dsStmts (sbv, sbf) n ss)
        (renStmts orig ⟨σv, σf⟩ taken ss).1 (renStmts orig ⟨σv, σf⟩ taken ss).2.1
        (dsStmts (srv, srf) n (renStmts orig ⟨σv, σf⟩ taken ss).2.2) ∧
      (∀ y ∈ taken, y ∈ (renStmts orig ⟨σv, σf⟩ taken ss).2.1)
  | n, taken, sbv, sbf, srv, srf, σv, σf, [], hv, hf, hSBv, hSBf, _, _, _ => by
      simp only [renStmts, dsStmts]
      exact ⟨⟨rfl, rfl, hv, hf, hSBv, hSBf⟩, fun y hy => hy⟩
  | n, taken, sbv, sbf, srv, srf, σv, σf, s :: rest, hv, hf, hSBv, hSBf, hids, hsv, hwf => by
      have hids_s : ∀ x ∈ identsS s, x ∈ orig := fun x hx =>
        hids x (by simp only [identsSs, List.mem_append]; exact Or.inl hx)
      have hids_r : ∀ x ∈ identsSs rest, x ∈ orig := fun x hx =>
        hids x (by simp only [identsSs, List.mem_append]; exact Or.inr hx)
      obtain ⟨hstep, hmono1⟩ := dsStmt_align n taken sbv sbf srv srf σv σf s
        hv hf hSBv hSBf hids_s hsv.1 hwf.1
      obtain ⟨hrest, hmono2⟩ := dsStmts_align (dsStmt (sbv, sbf) n s).2.1
        (renStmt orig ⟨σv, σf⟩ taken s).2.1
        (dsStmt (sbv, sbf) n s).1.1 (dsStmt (sbv, sbf) n s).1.2
        (dsStmt (srv, srf) n (renStmt orig ⟨σv, σf⟩ taken s).2.2).1.1
        (dsStmt (srv, srf) n (renStmt orig ⟨σv, σf⟩ taken s).2.2).1.2
        (renStmt orig ⟨σv, σf⟩ taken s).1.σv (renStmt orig ⟨σv, σf⟩ taken s).1.σf
        rest hstep.alignV hstep.alignF hstep.belowV hstep.belowF hids_r hsv.2 hwf.2
      -- expose the head/tail structure on all three traversals, then rewrite
      -- the renamed-side head results into the source-side ones
      simp only [renStmts, dsStmts]
      rw [show ((dsStmt (srv, srf) n (renStmt orig ⟨σv, σf⟩ taken s).2.2).1) =
          ((dsStmt (srv, srf) n (renStmt orig ⟨σv, σf⟩ taken s).2.2).1.1,
           (dsStmt (srv, srf) n (renStmt orig ⟨σv, σf⟩ taken s).2.2).1.2) from rfl,
        hstep.counter, hstep.stmts]
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, fun y hy => hmono2 y (hmono1 y hy)⟩
      · show _ :: _ = _ :: _
        rw [hrest.stmts]
      · exact hrest.counter
      · exact hrest.alignV
      · exact hrest.alignF
      · exact hrest.belowV
      · exact hrest.belowF

/-- Scope-level alignment: prescan both sides (the same `assignNames` batch,
by `funNames_renStmts` + `assignNames_map_substOf`), then the list case. -/
theorem dsScope_align' {orig : List Ident} :
    ∀ (n : Nat) (taken : List Ident) (sbv sbf srv srf : Subst)
      (σv σf : List (Ident × Ident)) (body : List (Stmt Op)),
      LookupAligned orig sbv σv srv → LookupAligned orig sbf σf srf →
      SubstBelow taken σv → SubstBelow taken σf →
      (∀ x ∈ identsSs body, x ∈ orig) → SVStmts body →
      (funNames body).Nodup → WFInner body →
      StAligned orig (dsScope (sbv, sbf) n body)
        (renScope orig ⟨σv, σf⟩ taken body).1 (renScope orig ⟨σv, σf⟩ taken body).2.1
        (dsScope (srv, srf) n (renScope orig ⟨σv, σf⟩ taken body).2.2) ∧
      (∀ y ∈ taken, y ∈ (renScope orig ⟨σv, σf⟩ taken body).2.1)
  | n, taken, sbv, sbf, srv, srf, σv, σf, body, hv, hf, hSBv, hSBf, hids, hsv, hnd, hwf => by
      -- the renamed body's function names are the prescan batch's outputs
      have hfn : funNames ((renStmts orig
            ⟨σv, (assignNames orig (funNames body) taken).2.1 ++ σf⟩
            (assignNames orig (funNames body) taken).2.2 body).2.2) =
          (assignNames orig (funNames body) taken).1 := by
        rw [funNames_renStmts]
        exact assignNames_map_substOf orig σf (funNames body) taken hnd
          (fun p hp => (hSBf p hp).1)
      have hlen : (assignNames orig (funNames body) taken).1.length =
          (funNames body).length := assignNames_length orig (funNames body) taken
      -- fun-side prescan alignment: one `lookupAligned_batch` instance
      have hbatch := lookupAligned_batch (orig := orig) (funNames body)
        (freshVars n (funNames body)) taken
        (by simp) hf hSBf hnd
        (fun x hx => hids x (funNames_subset_idents body x hx))
      -- bookkeeping at the prescan's exit
      have hSBv1 : SubstBelow (assignNames orig (funNames body) taken).2.2 σv :=
        hSBv.mono (assignNames_mono orig (funNames body) taken)
      have hSBf1 := substBelow_batch (orig := orig) hSBf (funNames body)
      -- the body, in the prescan-extended states
      obtain ⟨hb, hmono⟩ := dsStmts_align (n + (funNames body).length)
        (assignNames orig (funNames body) taken).2.2
        sbv ((funNames body).zip (freshVars n (funNames body)) ++ sbf)
        srv ((assignNames orig (funNames body) taken).1.zip
          (freshVars n (funNames body)) ++ srf)
        σv ((assignNames orig (funNames body) taken).2.1 ++ σf)
        body hv hbatch hSBv1 hSBf1 hids hsv hwf
      -- rewrite the goal's three `dsScope`/`renScope` into their unfoldings
      simp only [dsScope, renScope]
      rw [hfn, hlen, freshVars_congr (n := n) hlen]
      exact ⟨hb, fun y hy =>
        hmono y (assignNames_mono orig (funNames body) taken y hy)⟩

/-- Case-list alignment (`switch` arms; no state is returned). -/
theorem dsCases_align {orig : List Ident} :
    ∀ (n : Nat) (taken : List Ident) (sbv sbf srv srf : Subst)
      (σv σf : List (Ident × Ident)) (cs : List (Literal × List (Stmt Op))),
      LookupAligned orig sbv σv srv → LookupAligned orig sbf σf srf →
      SubstBelow taken σv → SubstBelow taken σf →
      (∀ x ∈ identsCs cs, x ∈ orig) → Normalize.SVCases cs → Normalize.WFCases cs →
      (dsCases (srv, srf) n (renCases orig ⟨σv, σf⟩ taken cs).2 =
        dsCases (sbv, sbf) n cs) ∧
      (∀ y ∈ taken, y ∈ (renCases orig ⟨σv, σf⟩ taken cs).1)
  | n, taken, sbv, sbf, srv, srf, σv, σf, [], _, _, _, _, _, _, _ => by
      simp only [renCases, dsCases]
      exact ⟨trivial, fun y hy => hy⟩
  | n, taken, sbv, sbf, srv, srf, σv, σf, (l, body) :: rest,
      hv, hf, hSBv, hSBf, hids, hsv, hwf => by
      have hids_b : ∀ x ∈ identsSs body, x ∈ orig := fun x hx =>
        hids x (by simp only [identsCs, List.mem_append]; exact Or.inl hx)
      have hids_r : ∀ x ∈ identsCs rest, x ∈ orig := fun x hx =>
        hids x (by simp only [identsCs, List.mem_append]; exact Or.inr hx)
      obtain ⟨hb, hmono1⟩ := dsScope_align' n taken sbv sbf srv srf σv σf body
        hv hf hSBv hSBf hids_b hsv.1 hwf.1.1 hwf.1.2
      obtain ⟨hrest, hmono2⟩ := dsCases_align (dsScope (sbv, sbf) n body).2.1
        (renScope orig ⟨σv, σf⟩ taken body).2.1 sbv sbf srv srf σv σf rest
        hv hf (hSBv.mono hmono1) (hSBf.mono hmono1) hids_r hsv.2 hwf.2
      simp only [renCases, dsCases]
      rw [hb.counter, hb.stmts, hrest]
      exact ⟨rfl, fun y hy => hmono2 y (hmono1 y hy)⟩

/-- Default-branch alignment. -/
theorem dsDflt_align {orig : List Ident} :
    ∀ (n : Nat) (taken : List Ident) (sbv sbf srv srf : Subst)
      (σv σf : List (Ident × Ident)) (dflt : Option (List (Stmt Op))),
      LookupAligned orig sbv σv srv → LookupAligned orig sbf σf srf →
      SubstBelow taken σv → SubstBelow taken σf →
      (∀ x ∈ (match dflt with | none => [] | some b => identsSs b), x ∈ orig) →
      Normalize.SVDflt dflt → Normalize.WFDflt dflt →
      (dsDflt (srv, srf) n (renDflt orig ⟨σv, σf⟩ taken dflt).2 =
        dsDflt (sbv, sbf) n dflt) ∧
      (∀ y ∈ taken, y ∈ (renDflt orig ⟨σv, σf⟩ taken dflt).1)
  | n, taken, sbv, sbf, srv, srf, σv, σf, none, _, _, _, _, _, _, _ => by
      simp only [renDflt, dsDflt]
      exact ⟨trivial, fun y hy => hy⟩
  | n, taken, sbv, sbf, srv, srf, σv, σf, some body,
      hv, hf, hSBv, hSBf, hids, hsv, hwf => by
      obtain ⟨hb, hmono⟩ := dsScope_align' n taken sbv sbf srv srf σv σf body
        hv hf hSBv hSBf hids hsv hwf.1 hwf.2
      simp only [renDflt, dsDflt]
      rw [hb.counter, hb.stmts]
      exact ⟨rfl, hmono⟩

end

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
      (dsScope stB n body).2.2 :=
  ((dsScope_align' n taken stB.1 stB.2 stR.1 stR.2 st.σv st.σf body
    hv hf hSBv hSBf hids hsv hnd hwf).1).stmts

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
