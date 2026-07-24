import YulEvmCompiler.Optimizer.Implementation.Normalization.RenameNumericSound
set_option warningAsError true
/-!
# `RenameNumeric.rename` produces globally-unique declared names

This module proves the `NormalForm.UniqueNames` postcondition for the
collision-only numeric disambiguator `RenameNumeric.rename`, under the
`Normalize.WellFormed` precondition (per-block distinct top-level function
names — which valid Yul guarantees, and which is genuinely required: on
`[funDef f …, funDef f …]` the name-keyed function substitution would merge the
two definitions into one output name).

The theorem is `rename_uniqueNames'` (primed to avoid clashing with the sorried
statement of the same fact kept in `RenameNumericSound`; the two are never
imported together yet).

## Proof shape

The renamer threads a *global, monotonically growing* `taken` set of committed
output names, and commits every declared name through `assignName`, which
always returns a name fresh with respect to the current `taken`
(`assignName_fresh`, from `RenameNumericSound`). The proof is a mutual
induction over the traversal (`renStmt`/`renStmts`/`renScope`/`renCases`/
`renDflt`) carrying the packaged invariant `Inv taken taken' decls allowed`:

* `taken ⊆ taken'` (the set only grows);
* the output's declared names `decls` are duplicate-free;
* every output declared name is committed to the exit set `taken'`;
* an output declared name may lie in the *entry* set `taken` only if it is in
  the short whitelist `allowed`.

The whitelist handles the one subtlety: a `funDef`'s output *name* is
`substOf st.σf fname`, committed earlier by the enclosing scope's prescan
(`renScope` runs `assignNames … (funNames body) …` first), so at the statement
it is already in `taken`. At the statement/list level `allowed` is exactly the
image `(funNames ss).map (substOf st.σf)` of the scope's own function names; at
scope granularity (`renScope`) the whitelist closes to `[]` because the prescan
itself committed those names fresh to the scope's entry set. Two side
hypotheses thread the prescan's effect through the statement list:

* `∀ f ∈ funNames ss, substOf st.σf f ∈ taken` (the image was prescan-committed);
* `((funNames ss).map (substOf st.σf)).Nodup` (the prescan image is
  duplicate-free, from `WellFormed`'s per-block `Nodup` and freshness of each
  successive `assignName` output).

Sequencing composes via `Inv.seq`: a later segment's names avoid the mid
`taken`, which already contains the earlier segment's names, so the two
segments are disjoint. Everything reduces to the `assignName`/`assignNames`
warm-up facts proved first, whose single leaf is `assignName_fresh` — itself
proved in `RenameNumericSound` modulo the `freshName_not_mem` lemma being
discharged in a parallel workstream (the only `sorry` this file depends on,
transitively; this file contains none).
-/

namespace YulEvmCompiler.Optimizer.RenameNumeric

open YulSemantics
open YulEvmCompiler.Optimizer.Normalize
  (substOf funNames Subst substOf_cons_eq substOf_cons_ne WFInner WFInnerS WFCases WFDflt)
open YulEvmCompiler.Optimizer.NormalForm
  (declaredNamesStmt declaredNamesStmts declaredNamesCases declaredNamesDflt)

variable {Op : Type}

/-! ## `substOf` helpers -/

/-- A substitution none of whose keys is `x` leaves `x` unchanged. -/
theorem substOf_eq_self {σ : Subst} {x : Ident} (h : ∀ p ∈ σ, p.1 ≠ x) :
    substOf σ x = x := by
  unfold YulEvmCompiler.Optimizer.Normalize.substOf
  rw [List.find?_eq_none.mpr (fun p hp => by simpa using h p hp)]
  rfl

/-! ## `assignName` warm-up facts -/

/-- `assignName` extends `taken` by exactly its chosen output name. -/
theorem assignName_taken (orig taken : List Ident) (x : Ident) :
    (assignName orig taken x).2.2 = (assignName orig taken x).1 :: taken := by
  unfold assignName
  split <;> rfl

/-- `assignName` on a name that is not yet taken keeps it (and adds no
substitution entry). -/
theorem assignName_of_not_mem {taken : List Ident} {x : Ident} (orig : List Ident)
    (h : x ∉ taken) : assignName orig taken x = (x, [], x :: taken) := by
  unfold assignName
  rw [if_neg h]

/-- Every substitution entry produced by `assignName` has key `x`, and is only
produced when `x` was already taken at the call. -/
theorem assignName_sub_keys {orig taken : List Ident} {x : Ident} :
    ∀ p ∈ (assignName orig taken x).2.1, p.1 = x ∧ x ∈ taken := by
  unfold assignName
  split
  · rename_i hx
    intro p hp
    rw [List.mem_singleton] at hp
    exact ⟨by rw [hp], hx⟩
  · intro p hp
    exact absurd hp List.not_mem_nil

/-! ## `assignNames` warm-up facts

`assignNames orig xs taken` returns `(outs, subs, taken')`: the chosen output
names, the substitution entries for the renamed ones, and the extended `taken`.
All facts below are small inductions threading `taken`; freshness bottoms out
at `assignName_fresh` (from `RenameNumericSound`). -/

/-- Projection-form unfolding of the `cons` case of `assignNames`. -/
theorem assignNames_cons (orig : List Ident) (x : Ident) (xs taken : List Ident) :
    assignNames orig (x :: xs) taken =
      ((assignName orig taken x).1 ::
          (assignNames orig xs (assignName orig taken x).2.2).1,
        (assignName orig taken x).2.1 ++
          (assignNames orig xs (assignName orig taken x).2.2).2.1,
        (assignNames orig xs (assignName orig taken x).2.2).2.2) := by
  rcases h : assignName orig taken x with ⟨x', sub, taken1⟩
  rcases h2 : assignNames orig xs taken1 with ⟨xs', subs, taken2⟩
  simp [assignNames, h, h2]

/-- `assignNames` only ever grows the `taken` set. -/
theorem assignNames_mono (orig : List Ident) :
    ∀ (xs taken : List Ident), ∀ y ∈ taken, y ∈ (assignNames orig xs taken).2.2
  | [], _, _, hy => by simpa [assignNames] using hy
  | x :: xs, taken, y, hy => by
      rw [assignNames_cons]
      exact assignNames_mono orig xs _ y (by rw [assignName_taken]; exact List.mem_cons_of_mem _ hy)

/-- Every output name of `assignNames` is fresh with respect to the *entry*
`taken` set. -/
theorem assignNames_outs_fresh (orig : List Ident) :
    ∀ (xs taken : List Ident), ∀ y ∈ (assignNames orig xs taken).1, y ∉ taken
  | [], _, _, hy => by simp [assignNames] at hy
  | x :: xs, taken, y, hy => by
      rw [assignNames_cons] at hy
      rcases List.mem_cons.mp hy with h | h
      · exact h ▸ assignName_fresh orig taken x
      · intro hyt
        exact assignNames_outs_fresh orig xs _ y h
          (by rw [assignName_taken]; exact List.mem_cons_of_mem _ hyt)

/-- Every output name of `assignNames` is committed to the final `taken` set. -/
theorem assignNames_outs_mem (orig : List Ident) :
    ∀ (xs taken : List Ident), ∀ y ∈ (assignNames orig xs taken).1,
      y ∈ (assignNames orig xs taken).2.2
  | [], _, _, hy => by simp [assignNames] at hy
  | x :: xs, taken, y, hy => by
      rw [assignNames_cons] at hy ⊢
      rcases List.mem_cons.mp hy with h | h
      · exact assignNames_mono orig xs _ _ (by rw [assignName_taken, h]; exact List.mem_cons_self ..)
      · exact assignNames_outs_mem orig xs _ y h

/-- The output names of `assignNames` are pairwise distinct. -/
theorem assignNames_outs_nodup (orig : List Ident) :
    ∀ (xs taken : List Ident), (assignNames orig xs taken).1.Nodup
  | [], _ => by simp [assignNames]
  | x :: xs, taken => by
      rw [assignNames_cons]
      refine List.nodup_cons.mpr ⟨fun hmem => ?_, assignNames_outs_nodup orig xs _⟩
      exact assignNames_outs_fresh orig xs _ _ hmem
        (by rw [assignName_taken]; exact List.mem_cons_self ..)

/-- Every substitution entry produced by `assignNames` has its key among the
input names. -/
theorem assignNames_sub_keys_mem (orig : List Ident) :
    ∀ (xs taken : List Ident), ∀ p ∈ (assignNames orig xs taken).2.1, p.1 ∈ xs
  | [], _, _, hp => by simp [assignNames] at hp
  | x :: xs, taken, p, hp => by
      rw [assignNames_cons] at hp
      rcases List.mem_append.mp hp with h | h
      · exact (assignName_sub_keys p h).1 ▸ List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (assignNames_sub_keys_mem orig xs _ p h)

/-- Every substitution entry produced by `assignNames` has its key in the final
`taken` set (the key was already taken when the entry was created). -/
theorem assignNames_sub_keys_taken (orig : List Ident) :
    ∀ (xs taken : List Ident), ∀ p ∈ (assignNames orig xs taken).2.1,
      p.1 ∈ (assignNames orig xs taken).2.2
  | [], _, _, hp => by simp [assignNames] at hp
  | x :: xs, taken, p, hp => by
      rw [assignNames_cons] at hp ⊢
      rcases List.mem_append.mp hp with h | h
      · obtain ⟨hkey, hx⟩ := assignName_sub_keys p h
        exact assignNames_mono orig xs _ _
          (by rw [assignName_taken]; exact List.mem_cons_of_mem _ (hkey ▸ hx))
      · exact assignNames_sub_keys_taken orig xs _ p h

/-- **The prescan bridge**: looking the input names up in the produced
substitution (over any tail `σ` whose keys are already taken) yields exactly
the produced output names. Kept names fall through both `subs` (its keys are
the *other*, distinct input names) and `σ` (its keys are taken, a kept name is
not); renamed names hit their own entry. -/
theorem assignNames_map_substOf (orig : List Ident) (σ : Subst) :
    ∀ (xs taken : List Ident), xs.Nodup → (∀ p ∈ σ, p.1 ∈ taken) →
      xs.map (substOf ((assignNames orig xs taken).2.1 ++ σ)) =
        (assignNames orig xs taken).1
  | [], _, _, _ => by simp [assignNames]
  | x :: xs, taken, hnd, hσ => by
      rw [assignNames_cons]
      obtain ⟨hx_notin, hnd'⟩ := List.nodup_cons.mp hnd
      have hσ1 : ∀ p ∈ σ, p.1 ∈ (assignName orig taken x).2.2 := fun p hp => by
        rw [assignName_taken]; exact List.mem_cons_of_mem _ (hσ p hp)
      have htail : ∀ y ∈ xs,
          substOf (((assignName orig taken x).2.1 ++
              (assignNames orig xs (assignName orig taken x).2.2).2.1) ++ σ) y =
            substOf ((assignNames orig xs (assignName orig taken x).2.2).2.1 ++ σ) y := by
        intro y hy
        by_cases hxt : x ∈ taken
        · unfold assignName
          rw [if_pos hxt]
          exact substOf_cons_ne _ _ (fun hxy => hx_notin (hxy ▸ hy))
        · simp [assignName_of_not_mem orig hxt]
      have hhead : substOf (((assignName orig taken x).2.1 ++
          (assignNames orig xs (assignName orig taken x).2.2).2.1) ++ σ) x =
            (assignName orig taken x).1 := by
        by_cases hxt : x ∈ taken
        · conv_lhs => rw [show (assignName orig taken x).2.1 =
            [(x, (assignName orig taken x).1)] by unfold assignName; rw [if_pos hxt]]
          exact substOf_cons_eq x _ _
        · simp only [assignName_of_not_mem orig hxt, List.nil_append]
          refine substOf_eq_self (fun p hp => ?_)
          rcases List.mem_append.mp hp with h | h
          · exact fun hpx => hx_notin (hpx ▸
              assignNames_sub_keys_mem orig xs _ p h)
          · exact fun hpx => hxt (hpx ▸ hσ p h)
      rw [List.map_cons, hhead]
      congr 1
      rw [List.map_congr_left htail]
      exact assignNames_map_substOf orig σ xs _ hnd' hσ1

/-! ## The packaged invariant -/

/-- The invariant satisfied by one traversal step running from entry set
`taken` to exit set `taken'`, whose output declares the names `decls`:

* `mono` — the global `taken` set only grows;
* `nodup` — the output's declared names are pairwise distinct;
* `committed` — every output declared name is committed to the exit set;
* `fresh` — an output declared name may predate the entry set only if it is in
  the whitelist `allowed` (the enclosing prescan's committed function names).
-/
structure Inv (taken taken' decls allowed : List Ident) : Prop where
  /-- The global `taken` set only grows. -/
  mono : ∀ x ∈ taken, x ∈ taken'
  /-- The output's declared names are pairwise distinct. -/
  nodup : decls.Nodup
  /-- Every output declared name is committed to the exit set. -/
  committed : ∀ x ∈ decls, x ∈ taken'
  /-- Declared names predating the entry set lie in the whitelist. -/
  fresh : ∀ x ∈ decls, x ∈ taken → x ∈ allowed

/-- A step that declares nothing and commits nothing satisfies the invariant
for any whitelist. -/
theorem Inv.nil (taken allowed : List Ident) : Inv taken taken [] allowed :=
  ⟨fun _ hx => hx, List.nodup_nil, fun _ hx => absurd hx List.not_mem_nil,
    fun _ hx => absurd hx List.not_mem_nil⟩

/-- A step that declares exactly one already-committed, whitelisted name
(a `funDef`'s prescan-committed output name). -/
theorem Inv.single {taken : List Ident} {x : Ident} (h : x ∈ taken) :
    Inv taken taken [x] [x] :=
  ⟨fun _ hx => hx, List.nodup_singleton x,
    fun _ hy => (List.mem_singleton.mp hy) ▸ h,
    fun _ hy _ => hy⟩

/-- **Sequencing.** Two consecutive steps compose: the second segment's
declared names avoid the mid `taken` set, which already contains the first
segment's names, so the segments are disjoint — provided the two whitelists are
jointly duplicate-free and the second whitelist was committed before entry. -/
theorem Inv.seq {taken t1 t2 A B alA alB : List Ident}
    (h1 : Inv taken t1 A alA) (h2 : Inv t1 t2 B alB)
    (halB : ∀ y ∈ alB, y ∈ taken) (hnd : (alA ++ alB).Nodup) :
    Inv taken t2 (A ++ B) (alA ++ alB) := by
  refine ⟨fun x hx => h2.mono x (h1.mono x hx), ?_, ?_, ?_⟩
  · refine List.nodup_append.mpr ⟨h1.nodup, h2.nodup, ?_⟩
    intro x hxA y hyB hxy
    subst hxy
    have hxB' : x ∈ alB := h2.fresh x hyB (h1.committed x hxA)
    exact (List.disjoint_of_nodup_append hnd) (h1.fresh x hxA (halB x hxB')) hxB'
  · intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact h2.mono x (h1.committed x h)
    · exact h2.committed x h
  · intro x hx hxt
    rcases List.mem_append.mp hx with h | h
    · exact List.mem_append_left _ (h1.fresh x h hxt)
    · exact List.mem_append_right _ (h2.fresh x h (h1.mono x hxt))

/-- Sequencing two steps with empty whitelists. -/
theorem Inv.seq0 {taken t1 t2 A B : List Ident}
    (h1 : Inv taken t1 A []) (h2 : Inv t1 t2 B []) : Inv taken t2 (A ++ B) [] := by
  simpa using h1.seq h2 (fun y hy => absurd hy List.not_mem_nil) (by simp)

/-- The invariant only depends on the declared-name list up to permutation
(needed because `declaredNamesStmt` lists a `for`-loop's `post` names before
its `body` names, while the traversal commits them in the opposite order). -/
theorem Inv.perm {taken t' d d' al : List Ident} (h : Inv taken t' d al)
    (hp : d.Perm d') : Inv taken t' d' al :=
  ⟨h.mono, hp.nodup_iff.mp h.nodup,
    fun x hx => h.committed x (hp.mem_iff.mpr hx),
    fun x hx => h.fresh x (hp.mem_iff.mpr hx)⟩

/-- `assignNames` itself is one invariant step with an empty whitelist: its
outputs are distinct, committed, and fresh with respect to the entry set. -/
theorem assignNames_inv (orig xs taken : List Ident) :
    Inv taken (assignNames orig xs taken).2.2 (assignNames orig xs taken).1 [] :=
  ⟨assignNames_mono orig xs taken, assignNames_outs_nodup orig xs taken,
    assignNames_outs_mem orig xs taken,
    fun x hx hxt => absurd hxt (assignNames_outs_fresh orig xs taken x hx)⟩

/-! ## Structural facts about the traversal -/

/-- `funNames` splits off the head statement's contribution. -/
theorem funNames_cons (s : Stmt Op) (rest : List (Stmt Op)) :
    funNames (s :: rest) = funNames [s] ++ funNames rest := by
  cases s <;> simp [funNames]

/-- `renStmt` never touches the function substitution: only `renScope`'s
prescan extends `σf` (and blocks discard the extension on exit). -/
theorem renStmt_σf (orig : List Ident) (st : St) (taken : List Ident) (s : Stmt Op) :
    (renStmt orig st taken s).1.σf = st.σf := by
  cases s with
  | letDecl vars val =>
      rcases h : assignNames orig vars taken with ⟨vars', vsub, taken1⟩
      simp [renStmt, h]
  | funDef fname params rets body =>
      rcases h1 : assignNames orig params taken with ⟨params', psub, takenP⟩
      rcases h2 : assignNames orig rets takenP with ⟨rets', rsub, takenR⟩
      simp [renStmt, h1, h2]
  | block body => simp [renStmt]
  | assign vars val => simp [renStmt]
  | cond c body => simp [renStmt]
  | switch c cs dflt => simp [renStmt]
  | forLoop init c post body => simp [renStmt]
  | exprStmt e => simp [renStmt]
  | «break» => simp [renStmt]
  | «continue» => simp [renStmt]
  | leave => simp [renStmt]

/-! ## The mutual induction

The invariant statements, one per traversal function, phrased as motives for
the generated functional induction principle `renStmt.mutual_induct`. Common
hypotheses: the input is well-formed and every key of the function substitution
`st.σf` is already taken (so a kept declared name — one not in `taken` — can
never collide with the target of an outer `σf` entry). At statement/list
granularity, two extra hypotheses describe the enclosing prescan (see the
module docstring); at scope granularity the whitelist closes to `[]`.
`renStmts`/`renScope` additionally conclude that the *result* state's `σf`
keys are committed — the `for`-loop case needs this for its `init`-scope state,
which leaks into `body` and `post`. -/

/-- Statement-level invariant: the whitelist is the (at most one)
prescan-committed output name of the statement's own `funDef`. -/
abbrev StmtInv (orig : List Ident) (st : St) (taken : List Ident) (s : Stmt Op) : Prop :=
  WFInnerS s → (∀ p ∈ st.σf, p.1 ∈ taken) →
  (∀ f ∈ funNames [s], substOf st.σf f ∈ taken) →
  Inv taken (renStmt orig st taken s).2.1
    (declaredNamesStmt (renStmt orig st taken s).2.2)
    ((funNames [s]).map (substOf st.σf))

/-- Invariant for a `switch`'s optional `default` body (a scope, so the
whitelist is `[]`). -/
abbrev DfltInv (orig : List Ident) (st : St) (taken : List Ident)
    (dflt : Option (List (Stmt Op))) : Prop :=
  WFDflt dflt → (∀ p ∈ st.σf, p.1 ∈ taken) →
  Inv taken (renDflt orig st taken dflt).1
    (declaredNamesDflt (renDflt orig st taken dflt).2) []

/-- Scope-level invariant: the prescan commits the block's (distinct, by
well-formedness) function names first — each fresh with respect to the running
`taken` — after which *no* declared name of the output predates the scope's
entry set, closing the whitelist to `[]`. Also concludes that the result
state's `σf` keys are committed. -/
abbrev ScopeInv (orig : List Ident) (st : St) (taken : List Ident)
    (body : List (Stmt Op)) : Prop :=
  (funNames body).Nodup → WFInner body → (∀ p ∈ st.σf, p.1 ∈ taken) →
  Inv taken (renScope orig st taken body).2.1
      (declaredNamesStmts (renScope orig st taken body).2.2) [] ∧
    ∀ p ∈ (renScope orig st taken body).1.σf, p.1 ∈ (renScope orig st taken body).2.1

/-- Statement-list invariant: the whitelist is the prescan image of the list's
own top-level function names, assumed committed and duplicate-free. Also
concludes that the result state's `σf` keys are committed. -/
abbrev StmtsInv (orig : List Ident) (st : St) (taken : List Ident)
    (ss : List (Stmt Op)) : Prop :=
  WFInner ss → (∀ p ∈ st.σf, p.1 ∈ taken) →
  (∀ f ∈ funNames ss, substOf st.σf f ∈ taken) →
  ((funNames ss).map (substOf st.σf)).Nodup →
  Inv taken (renStmts orig st taken ss).2.1
      (declaredNamesStmts (renStmts orig st taken ss).2.2)
      ((funNames ss).map (substOf st.σf)) ∧
    ∀ p ∈ (renStmts orig st taken ss).1.σf, p.1 ∈ (renStmts orig st taken ss).2.1

/-- Invariant for a `switch`'s case list: each case body is a scope, so the
whitelist is `[]`; the exit `taken` of one case feeds the next. -/
abbrev CasesInv (orig : List Ident) (st : St) (taken : List Ident)
    (cs : List (Literal × List (Stmt Op))) : Prop :=
  WFCases cs → (∀ p ∈ st.σf, p.1 ∈ taken) →
  Inv taken (renCases orig st taken cs).1
    (declaredNamesCases (renCases orig st taken cs).2) []

/-- **The mutual induction**: all five invariants hold, by
`renStmt.mutual_induct` over the traversal. -/
theorem ren_inv (orig : List Ident) :
    (∀ (st : St) (taken : List Ident) (s : Stmt Op), StmtInv orig st taken s) ∧
      (∀ (st : St) (taken : List Ident) (dflt : Option (List (Stmt Op))),
        DfltInv orig st taken dflt) ∧
      (∀ (st : St) (taken : List Ident) (body : List (Stmt Op)),
        ScopeInv orig st taken body) ∧
      (∀ (st : St) (taken : List Ident) (ss : List (Stmt Op)),
        StmtsInv orig st taken ss) ∧
      (∀ (st : St) (taken : List Ident) (cs : List (Literal × List (Stmt Op))),
        CasesInv orig st taken cs) := by
  apply renStmt.mutual_induct orig (motive1 := StmtInv orig) (motive2 := DfltInv orig)
    (motive3 := ScopeInv orig) (motive4 := StmtsInv orig) (motive5 := CasesInv orig)
  -- `letDecl`: exactly the freshly-assigned variables, all new.
  · intro st taken vars val vars' vsub taken1 hV _ _ _
    have vInv := assignNames_inv orig vars taken
    simp only [hV] at vInv
    simp only [renStmt, hV]
    simpa [declaredNamesStmt, funNames] using vInv
  -- `assign`: declares nothing.
  · intro st taken vars val _ _ _
    simpa [renStmt, declaredNamesStmt, funNames] using Inv.nil taken []
  -- `exprStmt`: declares nothing.
  · intro st taken e _ _ _
    simpa [renStmt, declaredNamesStmt, funNames] using Inv.nil taken []
  -- `block`: one nested scope.
  · intro st taken body ih hwf hkeys _
    try simp only [WFInnerS] at hwf
    simpa [renStmt, declaredNamesStmt, funNames] using (ih hwf.1 hwf.2 hkeys).1
  -- `cond`: one nested scope.
  · intro st taken c body ih hwf hkeys _
    try simp only [WFInnerS] at hwf
    simpa [renStmt, declaredNamesStmt, funNames] using (ih hwf.1 hwf.2 hkeys).1
  -- `switch`: the case list feeds its exit `taken` to the default scope.
  · intro st taken c cs dflt _rc ihC ihD hwf hkeys _
    try simp only [WFInnerS] at hwf
    have cInv := ihC hwf.1 hkeys
    have dInv := ihD hwf.2 (fun p hp => cInv.mono _ (hkeys p hp))
    simpa [renStmt, declaredNamesStmt, funNames] using cInv.seq0 dInv
  -- `funDef`: the already-committed (whitelisted) name, then fresh params,
  -- rets, and body scope, sequenced through the growing `taken`.
  · intro st taken fname params rets body params' psub takenP hP rets' rsub takenR hR
      _stBody ihB hwf hkeys hf
    simp only [_stBody] at ihB
    try simp only [WFInnerS] at hwf
    have hname : substOf st.σf fname ∈ taken := hf fname (by simp [funNames])
    have pInv := assignNames_inv orig params taken
    simp only [hP] at pInv
    have rInv := assignNames_inv orig rets takenP
    simp only [hR] at rInv
    have hkeysR : ∀ p ∈ st.σf, p.1 ∈ takenR :=
      fun p hp => rInv.mono _ (pInv.mono _ (hkeys p hp))
    have bInv := (ihB hwf.1 hwf.2 hkeysR).1
    have total := (Inv.single hname).seq (pInv.seq0 (rInv.seq0 bInv))
      (fun y hy => absurd hy List.not_mem_nil) (by simp)
    simp only [renStmt, hP, hR]
    simpa [declaredNamesStmt, funNames, List.append_assoc] using total
  -- `forLoop`: `init`'s scope state (and its prescan-extended `σf`, whose keys
  -- are committed by `init`'s conclusion) leaks into `body` and `post`; the
  -- three scopes sequence through the growing `taken`, and the declared-name
  -- collector lists `post` before `body`, hence the permutation.
  · intro st taken init c post body _ri _rb ihI _ihB ihB ihP hwf hkeys _
    try simp only [WFInnerS] at hwf
    obtain ⟨⟨hndI, hwfI⟩, ⟨hndB, hwfB⟩, hndP, hwfP⟩ := hwf
    obtain ⟨iInv, iK⟩ := ihI hndI hwfI hkeys
    obtain ⟨bInv, -⟩ := ihB hndB hwfB iK
    obtain ⟨pInv, -⟩ := ihP hndP hwfP (fun p hp => bInv.mono _ (iK p hp))
    simp only [renStmt, declaredNamesStmt, funNames, List.map_nil]
    refine (iInv.seq0 (bInv.seq0 pInv)).perm ?_
    rw [List.append_assoc]
    exact List.Perm.append_left _ List.perm_append_comm
  -- `break`, `continue`, `leave`: declare nothing.
  · intro st taken _ _ _
    simpa [renStmt, declaredNamesStmt, funNames] using Inv.nil taken []
  · intro st taken _ _ _
    simpa [renStmt, declaredNamesStmt, funNames] using Inv.nil taken []
  · intro st taken _ _ _
    simpa [renStmt, declaredNamesStmt, funNames] using Inv.nil taken []
  -- `default: none`: declares nothing.
  · intro st taken _ _
    simpa [renDflt, declaredNamesDflt] using Inv.nil taken []
  -- `default: some`: one nested scope.
  · intro st taken body ih hwf hkeys
    try simp only [WFDflt] at hwf
    simpa [renDflt, declaredNamesDflt] using (ih hwf.1 hwf.2 hkeys).1
  -- Scope: the prescan bridge. `assignNames` commits the block's function
  -- names; `assignNames_map_substOf` identifies their `σf`-images with the
  -- committed outputs, discharging the two prescan hypotheses of `StmtsInv`;
  -- freshness of the outputs closes the whitelist to `[]`.
  · intro st taken body fouts fsub taken1 hA ih hnd hwf hkeys
    have hmono1 := assignNames_mono orig (funNames body) taken
    have houts_mem := assignNames_outs_mem orig (funNames body) taken
    have houts_fresh := assignNames_outs_fresh orig (funNames body) taken
    have houts_nodup := assignNames_outs_nodup orig (funNames body) taken
    have hkeys_sub := assignNames_sub_keys_taken orig (funNames body) taken
    have hmap := assignNames_map_substOf orig st.σf (funNames body) taken hnd hkeys
    simp only [hA] at hmono1 houts_mem houts_fresh houts_nodup hkeys_sub hmap
    have hkeys' : ∀ p ∈ fsub ++ st.σf, p.1 ∈ taken1 := by
      intro p hp
      rcases List.mem_append.mp hp with h | h
      · exact hkeys_sub p h
      · exact hmono1 _ (hkeys p h)
    have hf' : ∀ f ∈ funNames body, substOf (fsub ++ st.σf) f ∈ taken1 := by
      intro f hfm
      exact houts_mem _ (hmap ▸ List.mem_map_of_mem hfm)
    have hnd' : ((funNames body).map (substOf (fsub ++ st.σf))).Nodup := by
      rw [hmap]; exact houts_nodup
    obtain ⟨sInv, sK⟩ := ih hwf hkeys' hf' hnd'
    simp only [renScope, hA]
    refine ⟨⟨fun x hx => sInv.mono x (hmono1 x hx), sInv.nodup, sInv.committed, ?_⟩, sK⟩
    intro x hx hxt
    have hx1 := sInv.fresh x hx (hmono1 x hxt)
    have hx2 : x ∈ fouts := by rw [← hmap]; simpa using hx1
    exact absurd hxt (houts_fresh x hx2)
  -- Empty statement list.
  · intro st taken _ hkeys _ _
    constructor
    · simpa [renStmts, declaredNamesStmts, funNames] using Inv.nil taken []
    · simpa [renStmts] using hkeys
  -- Statement cons: the head's whitelist and the tail's whitelist partition
  -- the list's prescan image, so `Inv.seq` applies.
  · intro st taken s rest _r ihS ihR hwf hkeys hf hnd
    try simp only [WFInner] at hwf
    have hσ : (renStmt orig st taken s).1.σf = st.σf := renStmt_σf orig st taken s
    have sInv := ihS hwf.1 hkeys
      (fun f hfm => hf f (by rw [funNames_cons]; exact List.mem_append_left _ hfm))
    have hkeys1 : ∀ p ∈ (renStmt orig st taken s).1.σf,
        p.1 ∈ (renStmt orig st taken s).2.1 := by
      rw [hσ]; exact fun p hp => sInv.mono _ (hkeys p hp)
    have hf1 : ∀ f ∈ funNames rest,
        substOf (renStmt orig st taken s).1.σf f ∈ (renStmt orig st taken s).2.1 := by
      rw [hσ]
      exact fun f hfm => sInv.mono _
        (hf f (by rw [funNames_cons]; exact List.mem_append_right _ hfm))
    have hnd1 : ((funNames rest).map (substOf (renStmt orig st taken s).1.σf)).Nodup := by
      rw [hσ]
      rw [funNames_cons, List.map_append] at hnd
      exact (List.nodup_append.mp hnd).2.1
    obtain ⟨rInv, rK⟩ := ihR hwf.2 hkeys1 hf1 hnd1
    rw [hσ] at rInv
    have halB : ∀ y ∈ (funNames rest).map (substOf st.σf), y ∈ taken := by
      intro y hy
      obtain ⟨f, hfm, rfl⟩ := List.mem_map.mp hy
      exact hf f (by rw [funNames_cons]; exact List.mem_append_right _ hfm)
    have hnd' : ((funNames [s]).map (substOf st.σf) ++
        (funNames rest).map (substOf st.σf)).Nodup := by
      rw [← List.map_append, ← funNames_cons]; exact hnd
    have total := sInv.seq rInv halB hnd'
    constructor
    · rw [funNames_cons, List.map_append]
      simpa [renStmts, declaredNamesStmts] using total
    · simpa [renStmts] using rK
  -- Empty case list.
  · intro st taken _ _
    simpa [renCases, declaredNamesCases] using Inv.nil taken []
  -- Case cons: two scopes in sequence.
  · intro st taken l body rest _r ihB ihR hwf hkeys
    try simp only [WFCases] at hwf
    have bInv := (ihB hwf.1.1 hwf.1.2 hkeys).1
    have rInv := ihR hwf.2 (fun p hp => bInv.mono _ (hkeys p hp))
    simpa [renCases, declaredNamesCases] using bInv.seq0 rInv

/-- Scope-level corollary of `ren_inv`, in the form used by the goal theorem
(and reusable by downstream `SourceValid`-preservation work). -/
theorem renScope_inv (orig : List Ident) (st : St) (taken : List Ident)
    (body : List (Stmt Op)) (hnd : (funNames body).Nodup) (hwf : WFInner body)
    (hkeys : ∀ p ∈ st.σf, p.1 ∈ taken) :
    Inv taken (renScope orig st taken body).2.1
        (declaredNamesStmts (renScope orig st taken body).2.2) [] ∧
      ∀ p ∈ (renScope orig st taken body).1.σf, p.1 ∈ (renScope orig st taken body).2.1 :=
  (ren_inv orig).2.2.1 st taken body hnd hwf hkeys

/-! ## The goal theorem -/

/-- **`rename` produces globally-unique declared names** on well-formed input
(`Normalize.WellFormed`: per-block distinct top-level function names, which
valid Yul guarantees). The whole program is one scope entered with empty
substitutions and an empty `taken` set, so `renScope_inv` applies directly.

(Primed to avoid clashing with the identically-named sorried statement kept in
`RenameNumericSound`.) -/
theorem rename_uniqueNames' {b : Block Op} (h : Normalize.WellFormed b) :
    NormalForm.UniqueNames (rename b) :=
  ((renScope_inv (allIdents b) { σv := [], σf := [] } [] b h.1 h.2
    (fun _ hp => absurd hp List.not_mem_nil)).1).nodup

end YulEvmCompiler.Optimizer.RenameNumeric
