import YulEvmCompiler.Optimizer.Implementation.Normalization.DisambiguateAlpha
/-!
# The disambiguation pass is an instance of the α-relation

Connects the concrete transform (`dsScope`/`dsStmts`/…) to the abstract
α-equivalence (`AlphaBlockExt`/…): for a valid source program, `disambiguate b`
is α-related to `b` at the pass's own renamings (`substOf` of the threaded
substitution state). This discharges, against the *real* pass, every side
condition the bisimulation's relation carries — freshness, `Nodup`s, and the
`NotFresh`-restricted collision-freedom.

Ingredients:
* `SubOK σ n` — the substitution-state invariant: every binding maps a source
  (`NotFresh`) name to a fresh name `dsName k` with `k < n` (the counter
  discipline that makes newly-allocated names collision-free);
* `SV*` — source validity: every identifier occurring in the program is a
  source name (no `dsName`s), `let` variables and function params/rets are
  duplicate-free;
* a transform-congruence family: the transform depends on the *variable* subst
  only through its values at the referenced variables (`NormalForm.Scoped*`),
  which lets a function body — closed except for its params/rets — be
  transformed as if from the trimmed state, matching the α-relation's
  `updRen id` base;
* the instance proper, by mutual structural recursion mirroring the transform.

Everything here is syntax-only (no semantics imports), so it builds fast.
-/

namespace YulEvmCompiler.Optimizer.Normalize

open YulSemantics

variable {Op : Type}

/-! ### `substOf` bridging lemmas -/

/-- `substOf` of an extended substitution is `updRen` of the tail's resolution. -/
theorem substOf_append (l m : Subst) : substOf (l ++ m) = updRen (substOf m) l := by
  funext z
  simp only [substOf, updRen, List.find?_append]
  cases h : l.find? (fun p => p.1 = z) with
  | some p => simp
  | none => simp [substOf]

@[simp] theorem substOf_nil : substOf ([] : Subst) = fun z => z := by
  funext z; simp [substOf]

/-- On the empty tail, `substOf` is `updRen` over the identity — the α-relation's
base renaming for a function body. -/
theorem substOf_eq_updRen_id (l : Subst) : substOf l = updRen id l := by
  have h := substOf_append l []
  rw [List.append_nil] at h
  rw [h, substOf_nil]
  rfl

/-! ### The substitution-state invariant -/

/-- Every binding maps a source (`NotFresh`) name to `dsName k`, `k < n`. -/
def SubOK (σ : Subst) (n : Nat) : Prop :=
  ∀ p ∈ σ, NotFresh p.1 ∧ ∃ k, k < n ∧ p.2 = dsName k

/-- Both components of the state satisfy the discipline. -/
def StOK (st : St) (n : Nat) : Prop := SubOK st.1 n ∧ SubOK st.2 n

theorem SubOK.mono {σ : Subst} {n m : Nat} (h : SubOK σ n) (hnm : n ≤ m) : SubOK σ m :=
  fun p hp => ⟨(h p hp).1, (h p hp).2.imp (fun k hk => ⟨Nat.lt_of_lt_of_le hk.1 hnm, hk.2⟩)⟩

theorem StOK.mono {st : St} {n m : Nat} (h : StOK st n) (hnm : n ≤ m) : StOK st m :=
  ⟨h.1.mono hnm, h.2.mono hnm⟩

/-- The invariant survives prepending fresh bindings for source names. -/
theorem SubOK.extend {σ : Subst} {n : Nat} (h : SubOK σ n) {l : Subst} {m : Nat}
    (hnm : n ≤ m)
    (hl : ∀ p ∈ l, NotFresh p.1 ∧ ∃ k, k < m ∧ p.2 = dsName k) :
    SubOK (l ++ σ) m := by
  intro p hp
  rcases List.mem_append.mp hp with hpl | hpσ
  · exact hl p hpl
  · exact (h.mono hnm) p hpσ

/-- **Collision-freedom of newly allocated names**: under the counter
discipline, no `NotFresh` name resolves to a fresh name at or above the
counter. Discharges the α-relation's `NotFresh`-restricted freshness
side conditions. -/
theorem SubOK.fresh_ne {σ : Subst} {n : Nat} (h : SubOK σ n) {z : Ident}
    (hz : NotFresh z) {k : Nat} (hk : n ≤ k) : substOf σ z ≠ dsName k := by
  simp only [substOf]
  cases hf : σ.find? (fun p => p.1 = z) with
  | none => simpa using hz k
  | some p =>
      obtain ⟨_, j, hj, hpj⟩ := h p (List.mem_of_find?_eq_some hf)
      simp only [Option.map_some, Option.getD_some, hpj]
      intro hc
      exact absurd (dsName_inj hc) (Nat.ne_of_lt (Nat.lt_of_lt_of_le hj hk))

/-! ### `freshVars` facts (via `RangeNodup`) -/

theorem freshVars_nodup (n : Nat) (vars : List Ident) : (freshVars n vars).Nodup :=
  (freshVars_rangeNodup n vars).2.1

theorem freshVars_mem {n : Nat} {vars : List Ident} {v : Ident}
    (h : v ∈ freshVars n vars) : ∃ k, n ≤ k ∧ k < n + vars.length ∧ v = dsName k :=
  (freshVars_rangeNodup n vars).1 v h

/-- The zip of source variables with their fresh names satisfies the binding
discipline at the advanced counter. -/
theorem zip_fresh_ok {vars : List Ident} (hNF : ∀ x ∈ vars, NotFresh x) (n : Nat) :
    ∀ p ∈ vars.zip (freshVars n vars),
      NotFresh p.1 ∧ ∃ k, k < n + vars.length ∧ p.2 = dsName k := by
  intro p hp
  obtain ⟨hp1, hp2⟩ := List.of_mem_zip hp
  obtain ⟨k, _, hk2, hk3⟩ := freshVars_mem hp2
  exact ⟨hNF p.1 hp1, k, hk2, hk3⟩

/-! ### Source validity

Every identifier occurring anywhere in the program is a source name
(`NotFresh` — no leading `NUL`), `let` variables are duplicate-free, and a
function's params/rets are duplicate-free. Valid Yul guarantees all of this
(identifiers cannot contain `NUL`; redeclaring within a scope is rejected). -/

mutual
def SVExpr : Expr Op → Prop
  | .lit _ => True
  | .var x => NotFresh x
  | .builtin _ args => SVArgs args
  | .call fn args => NotFresh fn ∧ SVArgs args
def SVArgs : List (Expr Op) → Prop
  | [] => True
  | e :: rest => SVExpr e ∧ SVArgs rest
end

mutual
def SVStmt : Stmt Op → Prop
  | .letDecl vars eo =>
      vars.Nodup ∧ (∀ x ∈ vars, NotFresh x) ∧ (∀ e, eo = some e → SVExpr e)
  | .assign vars e => (∀ x ∈ vars, NotFresh x) ∧ SVExpr e
  | .exprStmt e => SVExpr e
  | .funDef fn ps rs body =>
      NotFresh fn ∧ (ps ++ rs).Nodup ∧ (∀ x ∈ ps ++ rs, NotFresh x) ∧ SVStmts body
  | .block body => SVStmts body
  | .cond c body => SVExpr c ∧ SVStmts body
  | .switch c cases dflt => SVExpr c ∧ SVCases cases ∧ SVDflt dflt
  | .forLoop init c post body => SVStmts init ∧ SVExpr c ∧ SVStmts post ∧ SVStmts body
  | _ => True
def SVStmts : List (Stmt Op) → Prop
  | [] => True
  | s :: rest => SVStmt s ∧ SVStmts rest
def SVCases : List (Literal × List (Stmt Op)) → Prop
  | [] => True
  | (_, body) :: rest => SVStmts body ∧ SVCases rest
def SVDflt : Option (List (Stmt Op)) → Prop
  | none => True
  | some body => SVStmts body
end

/-- A valid source block's top-level function names are source names. -/
theorem funNames_notFresh : ∀ {ss : List (Stmt Op)}, SVStmts ss →
    ∀ fn ∈ funNames ss, NotFresh fn
  | [], _, fn, hfn => by simp [funNames] at hfn
  | s :: rest, hsv, fn, hfn => by
      have hs : SVStmt s := hsv.1
      have hrest := funNames_notFresh (ss := rest) hsv.2
      cases s with
      | funDef f ps rs body =>
          rw [funNames] at hfn
          rcases List.mem_cons.mp hfn with h | h
          · exact h ▸ hs.1
          · exact hrest fn h
      | letDecl vars eo => exact hrest fn hfn
      | assign vars e => exact hrest fn hfn
      | exprStmt e => exact hrest fn hfn
      | block body => exact hrest fn hfn
      | cond c body => exact hrest fn hfn
      | switch c cases dflt => exact hrest fn hfn
      | forLoop init c post body => exact hrest fn hfn
      | «break» => exact hrest fn hfn
      | «continue» => exact hrest fn hfn
      | leave => exact hrest fn hfn

/-! ### Transform congruence in the variable substitution

The transform's output (code and counter) depends on the variable substitution
only through its resolved values at the *referenced* variables
(`NormalForm.Scoped*`); the function substitution must agree exactly. This is
what lets a function body — reference-closed except for its params/rets — be
transformed from the trimmed state `(paramZips, δ)`, matching the α-relation's
`updRen id` base for callee bodies.

The congruence takes two whole states `st₁ st₂` with equal function components
and variable components agreeing on the visible variables `vs`, and reports the
same shape on the *output* state, so it threads left-to-right through a
sequence. Everything is stated at whole-state level because the transform's
mutual functions are compiled by well-founded recursion and do not reduce
definitionally. -/

/-- A full zip's `find?`-miss means the key is absent. -/
theorem find?_zip_none_not_mem {xs ys : List Ident} {x : Ident} (hlen : xs.length ≤ ys.length)
    (h : (xs.zip ys).find? (fun p => p.1 = x) = none) : x ∉ xs := by
  intro hx
  have hkeys : (xs.zip ys).map Prod.fst = xs := List.map_fst_zip hlen
  have hx' : x ∈ (xs.zip ys).map Prod.fst := by rw [hkeys]; exact hx
  obtain ⟨p, hp, hpx⟩ := List.mem_map.mp hx'
  have := List.find?_eq_none.mp h p hp
  simp [hpx] at this

/-- The function substitution passes through a statement list unchanged. -/
theorem dsStmts_st2 (st : St) (n : Nat) (ss : List (Stmt Op)) :
    (dsStmts st n ss).1.2 = st.2 := by
  induction ss generalizing st n with
  | nil => simp [dsStmts]
  | cons s rest ih =>
      show (dsStmts st n (s :: rest)).1.2 = st.2
      simp only [dsStmts]
      rw [ih, dsStmt_st2]

mutual
theorem dsExpr_congr {vs fs : List Ident} :
    ∀ (st₁ st₂ : St), st₁.2 = st₂.2 →
      (∀ x ∈ vs, substOf st₁.1 x = substOf st₂.1 x) →
      ∀ e : Expr Op, NormalForm.ScopedExpr vs fs e → dsExpr st₁ e = dsExpr st₂ e
  | st₁, st₂, hδ, hag, .lit l, _ => by simp only [dsExpr]
  | st₁, st₂, hδ, hag, .var x, hsc => by
      have hx : x ∈ vs := hsc
      simp only [dsExpr]
      rw [hag x hx]
  | st₁, st₂, hδ, hag, .builtin op args, hsc => by
      have ha : NormalForm.ScopedArgs vs fs args := hsc
      simp only [dsExpr]
      rw [dsArgs_congr st₁ st₂ hδ hag args ha]
  | st₁, st₂, hδ, hag, .call fn args, hsc => by
      have ha : NormalForm.ScopedArgs vs fs args := hsc.2
      simp only [dsExpr]
      rw [dsArgs_congr st₁ st₂ hδ hag args ha, hδ]
theorem dsArgs_congr {vs fs : List Ident} :
    ∀ (st₁ st₂ : St), st₁.2 = st₂.2 →
      (∀ x ∈ vs, substOf st₁.1 x = substOf st₂.1 x) →
      ∀ es : List (Expr Op), NormalForm.ScopedArgs vs fs es → dsArgs st₁ es = dsArgs st₂ es
  | st₁, st₂, hδ, hag, [], _ => by simp only [dsArgs]
  | st₁, st₂, hδ, hag, e :: rest, hsc => by
      obtain ⟨he, hr⟩ :=
        (hsc : NormalForm.ScopedExpr vs fs e ∧ NormalForm.ScopedArgs vs fs rest)
      simp only [dsArgs]
      rw [dsExpr_congr st₁ st₂ hδ hag e he, dsArgs_congr st₁ st₂ hδ hag rest hr]
end

theorem dsOExpr_congr {vs fs : List Ident} (st₁ st₂ : St) (hδ : st₁.2 = st₂.2)
    (hag : ∀ x ∈ vs, substOf st₁.1 x = substOf st₂.1 x) :
    ∀ eo : Option (Expr Op), (∀ e, eo = some e → NormalForm.ScopedExpr vs fs e) →
      eo.map (dsExpr st₁) = eo.map (dsExpr st₂)
  | none, _ => rfl
  | some e, hsc => by
      simp only [Option.map_some]
      rw [dsExpr_congr st₁ st₂ hδ hag e (hsc e rfl)]

mutual
theorem dsStmt_congr {vs fs : List Ident} :
    ∀ (st₁ st₂ : St) (n : Nat) (s : Stmt Op), st₁.2 = st₂.2 →
      (∀ x ∈ vs, substOf st₁.1 x = substOf st₂.1 x) →
      NormalForm.ScopedStmt vs fs s →
      (dsStmt st₁ n s).2 = (dsStmt st₂ n s).2 ∧
      (dsStmt st₁ n s).1.2 = (dsStmt st₂ n s).1.2 ∧
      (∀ x ∈ vs ++ NormalForm.declTopVars s,
        substOf (dsStmt st₁ n s).1.1 x = substOf (dsStmt st₂ n s).1.1 x)
  | st₁, st₂, n, .letDecl vars eo, hδ, hag, hsc => by
      have hsce : ∀ e, eo = some e → NormalForm.ScopedExpr vs fs e := by
        cases eo with
        | none => intro e he; cases he
        | some e0 =>
            intro e he
            cases he
            exact (hsc : NormalForm.ScopedExpr vs fs e0)
      refine ⟨?_, by rw [dsStmt_st2, dsStmt_st2]; exact hδ, ?_⟩
      · simp only [dsStmt]
        rw [dsOExpr_congr st₁ st₂ hδ hag eo hsce]
      · intro x hx
        simp only [dsStmt]
        rw [substOf_append, substOf_append]
        simp only [updRen]
        cases hfind : (vars.zip (freshVars n vars)).find? (fun p => p.1 = x) with
        | some p => rfl
        | none =>
            have hxv : x ∉ vars := find?_zip_none_not_mem (by rw [freshVars_length]; exact Nat.le_refl _) hfind
            have hxvs : x ∈ vs := by
              rcases List.mem_append.mp (by simpa [NormalForm.declTopVars] using hx :
                x ∈ vs ++ vars) with h | h
              · exact h
              · exact absurd h hxv
            exact hag x hxvs
  | st₁, st₂, n, .assign vars e, hδ, hag, hsc => by
      obtain ⟨hvars, he⟩ :=
        (hsc : (∀ x ∈ vars, x ∈ vs) ∧ NormalForm.ScopedExpr vs fs e)
      refine ⟨?_, by rw [dsStmt_st2, dsStmt_st2]; exact hδ, ?_⟩
      · simp only [dsStmt]
        rw [dsExpr_congr st₁ st₂ hδ hag e he,
          List.map_congr_left (fun x hx => hag x (hvars x hx))]
      · intro x hx
        simp only [dsStmt]
        exact hag x (by simpa [NormalForm.declTopVars] using hx)
  | st₁, st₂, n, .exprStmt e, hδ, hag, hsc => by
      refine ⟨?_, by rw [dsStmt_st2, dsStmt_st2]; exact hδ, ?_⟩
      · simp only [dsStmt]
        rw [dsExpr_congr st₁ st₂ hδ hag e (hsc : NormalForm.ScopedExpr vs fs e)]
      · intro x hx
        simp only [dsStmt]
        exact hag x (by simpa [NormalForm.declTopVars] using hx)
  | st₁, st₂, n, .block body, hδ, hag, hsc => by
      have hb : NormalForm.ScopedStmts vs (fs ++ NormalForm.funDefNames body) body := hsc
      have hS := dsScope_congr st₁ st₂ n body hδ hag hb
      refine ⟨?_, by rw [dsStmt_st2, dsStmt_st2]; exact hδ, ?_⟩
      · simp only [dsStmt]
        rw [hS.1]
      · intro x hx
        simp only [dsStmt]
        exact hag x (by simpa [NormalForm.declTopVars] using hx)
  | st₁, st₂, n, .cond c body, hδ, hag, hsc => by
      obtain ⟨hc, hb⟩ := (hsc : NormalForm.ScopedExpr vs fs c ∧
        NormalForm.ScopedStmts vs (fs ++ NormalForm.funDefNames body) body)
      have hS := dsScope_congr st₁ st₂ n body hδ hag hb
      refine ⟨?_, by rw [dsStmt_st2, dsStmt_st2]; exact hδ, ?_⟩
      · simp only [dsStmt]
        rw [dsExpr_congr st₁ st₂ hδ hag c hc, hS.1]
      · intro x hx
        simp only [dsStmt]
        exact hag x (by simpa [NormalForm.declTopVars] using hx)
  | st₁, st₂, n, .switch c cases dflt, hδ, hag, hsc => by
      obtain ⟨hc, hcs, hd⟩ := (hsc : NormalForm.ScopedExpr vs fs c ∧
        NormalForm.ScopedCases vs fs cases ∧ NormalForm.ScopedDflt vs fs dflt)
      have hcases := dsCases_congr st₁ st₂ n cases hδ hag hcs
      have hdflt := dsDflt_congr st₁ st₂ (dsCases st₂ n cases).1 dflt hδ hag hd
      refine ⟨?_, by rw [dsStmt_st2, dsStmt_st2]; exact hδ, ?_⟩
      · simp only [dsStmt]
        rw [dsExpr_congr st₁ st₂ hδ hag c hc, hcases, hdflt]
      · intro x hx
        simp only [dsStmt]
        exact hag x (by simpa [NormalForm.declTopVars] using hx)
  | st₁, st₂, n, .funDef fname params rets body, hδ, hag, hsc => by
      have hb : NormalForm.ScopedStmts (params ++ rets)
          (fs ++ NormalForm.funDefNames body) body := hsc
      have hagB : ∀ x ∈ params ++ rets,
          substOf (params.zip (freshVars n params) ++
              rets.zip (freshVars (n + params.length) rets) ++ st₁.1) x
          = substOf (params.zip (freshVars n params) ++
              rets.zip (freshVars (n + params.length) rets) ++ st₂.1) x := by
        intro x hx
        rw [substOf_append, substOf_append]
        simp only [updRen]
        cases hfind : (params.zip (freshVars n params) ++
            rets.zip (freshVars (n + params.length) rets)).find? (fun p => p.1 = x) with
        | some p => rfl
        | none =>
            exfalso
            rw [List.find?_append] at hfind
            have h1 : (params.zip (freshVars n params)).find? (fun p => p.1 = x) = none := by
              cases hh : (params.zip (freshVars n params)).find? (fun p => p.1 = x) with
              | none => rfl
              | some p => rw [hh] at hfind; simp at hfind
            have h2 : (rets.zip (freshVars (n + params.length) rets)).find?
                (fun p => p.1 = x) = none := by
              rw [h1] at hfind; simpa using hfind
            have hnp := find?_zip_none_not_mem (by rw [freshVars_length]; exact Nat.le_refl _) h1
            have hnr := find?_zip_none_not_mem (by rw [freshVars_length]; exact Nat.le_refl _) h2
            rcases List.mem_append.mp hx with h | h
            · exact hnp h
            · exact hnr h
      have hS := dsScope_congr
        (params.zip (freshVars n params) ++
          rets.zip (freshVars (n + params.length) rets) ++ st₁.1, st₁.2)
        (params.zip (freshVars n params) ++
          rets.zip (freshVars (n + params.length) rets) ++ st₂.1, st₂.2)
        (n + params.length + rets.length) body hδ hagB hb
      refine ⟨?_, by rw [dsStmt_st2, dsStmt_st2]; exact hδ, ?_⟩
      · simp only [dsStmt]
        rw [hS.1, hδ]
      · intro x hx
        simp only [dsStmt]
        exact hag x (by simpa [NormalForm.declTopVars] using hx)
  | st₁, st₂, n, .forLoop init c post body, hδ, hag, hsc => by
      obtain ⟨hinit, hc, hpost, hbody⟩ := (hsc :
        NormalForm.ScopedStmts vs (fs ++ NormalForm.funDefNames init) init ∧
        NormalForm.ScopedExpr (vs ++ NormalForm.declTopVarsL init)
          (fs ++ NormalForm.funDefNames init) c ∧
        NormalForm.ScopedStmts (vs ++ NormalForm.declTopVarsL init)
          ((fs ++ NormalForm.funDefNames init) ++ NormalForm.funDefNames post) post ∧
        NormalForm.ScopedStmts (vs ++ NormalForm.declTopVarsL init)
          ((fs ++ NormalForm.funDefNames init) ++ NormalForm.funDefNames body) body)
      have hI := dsScope_congr st₁ st₂ n init hδ hag hinit
      have hB := dsScope_congr (dsScope st₁ n init).1 (dsScope st₂ n init).1
        (dsScope st₂ n init).2.1 body hI.2.1 hI.2.2 hbody
      have hP := dsScope_congr (dsScope st₁ n init).1 (dsScope st₂ n init).1
        (dsScope (dsScope st₂ n init).1 (dsScope st₂ n init).2.1 body).2.1 post
        hI.2.1 hI.2.2 hpost
      refine ⟨?_, by rw [dsStmt_st2, dsStmt_st2]; exact hδ, ?_⟩
      · simp only [dsStmt]
        rw [hI.1, hB.1, hP.1,
          dsExpr_congr (dsScope st₁ n init).1 (dsScope st₂ n init).1 hI.2.1 hI.2.2 c hc]
      · intro x hx
        simp only [dsStmt]
        exact hag x (by simpa [NormalForm.declTopVars] using hx)
  | st₁, st₂, n, .«break», hδ, hag, _ => by
      refine ⟨by simp only [dsStmt], by rw [dsStmt_st2, dsStmt_st2]; exact hδ, ?_⟩
      intro x hx
      simp only [dsStmt]
      exact hag x (by simpa [NormalForm.declTopVars] using hx)
  | st₁, st₂, n, .«continue», hδ, hag, _ => by
      refine ⟨by simp only [dsStmt], by rw [dsStmt_st2, dsStmt_st2]; exact hδ, ?_⟩
      intro x hx
      simp only [dsStmt]
      exact hag x (by simpa [NormalForm.declTopVars] using hx)
  | st₁, st₂, n, .leave, hδ, hag, _ => by
      refine ⟨by simp only [dsStmt], by rw [dsStmt_st2, dsStmt_st2]; exact hδ, ?_⟩
      intro x hx
      simp only [dsStmt]
      exact hag x (by simpa [NormalForm.declTopVars] using hx)
theorem dsStmts_congr {vs fs : List Ident} :
    ∀ (st₁ st₂ : St) (n : Nat) (ss : List (Stmt Op)), st₁.2 = st₂.2 →
      (∀ x ∈ vs, substOf st₁.1 x = substOf st₂.1 x) →
      NormalForm.ScopedStmts vs fs ss →
      (dsStmts st₁ n ss).2 = (dsStmts st₂ n ss).2 ∧
      (dsStmts st₁ n ss).1.2 = (dsStmts st₂ n ss).1.2 ∧
      (∀ x ∈ vs ++ NormalForm.declTopVarsL ss,
        substOf (dsStmts st₁ n ss).1.1 x = substOf (dsStmts st₂ n ss).1.1 x)
  | st₁, st₂, n, [], hδ, hag, _ => by
      refine ⟨by simp only [dsStmts], by rw [dsStmts_st2, dsStmts_st2]; exact hδ, ?_⟩
      intro x hx
      simp only [dsStmts]
      exact hag x (by simpa [NormalForm.declTopVarsL] using hx)
  | st₁, st₂, n, s :: rest, hδ, hag, hsc => by
      obtain ⟨hs, hrest⟩ := (hsc : NormalForm.ScopedStmt vs fs s ∧
        NormalForm.ScopedStmts (vs ++ NormalForm.declTopVars s) fs rest)
      have hh := dsStmt_congr st₁ st₂ n s hδ hag hs
      have htail := dsStmts_congr (dsStmt st₁ n s).1 (dsStmt st₂ n s).1
        (dsStmt st₂ n s).2.1 rest hh.2.1 hh.2.2 hrest
      have hLcons : NormalForm.declTopVarsL (s :: rest)
          = NormalForm.declTopVars s ++ NormalForm.declTopVarsL rest := by
        simp [NormalForm.declTopVarsL]
      refine ⟨?_, by rw [dsStmts_st2, dsStmts_st2]; exact hδ, ?_⟩
      · simp only [dsStmts]
        rw [hh.1, htail.1]
      · intro x hx
        simp only [dsStmts]
        rw [hh.1]
        refine htail.2.2 x ?_
        rw [hLcons] at hx
        simpa [List.append_assoc] using hx
theorem dsScope_congr {vs fs : List Ident} :
    ∀ (st₁ st₂ : St) (n : Nat) (body : List (Stmt Op)), st₁.2 = st₂.2 →
      (∀ x ∈ vs, substOf st₁.1 x = substOf st₂.1 x) →
      NormalForm.ScopedStmts vs fs body →
      (dsScope st₁ n body).2 = (dsScope st₂ n body).2 ∧
      (dsScope st₁ n body).1.2 = (dsScope st₂ n body).1.2 ∧
      (∀ x ∈ vs ++ NormalForm.declTopVarsL body,
        substOf (dsScope st₁ n body).1.1 x = substOf (dsScope st₂ n body).1.1 x)
  | st₁, st₂, n, body, hδ, hag, hsc => by
      have hδ' : (st₁.1, (funNames body).zip (freshVars n (funNames body)) ++ st₁.2).2
          = (st₂.1, (funNames body).zip (freshVars n (funNames body)) ++ st₂.2).2 := by
        show (funNames body).zip (freshVars n (funNames body)) ++ st₁.2
          = (funNames body).zip (freshVars n (funNames body)) ++ st₂.2
        rw [hδ]
      have h := dsStmts_congr
        (st₁.1, (funNames body).zip (freshVars n (funNames body)) ++ st₁.2)
        (st₂.1, (funNames body).zip (freshVars n (funNames body)) ++ st₂.2)
        (n + (funNames body).length) body hδ' hag hsc
      refine ⟨?_, ?_, ?_⟩
      · simp only [dsScope]
        exact h.1
      · simp only [dsScope]
        exact h.2.1
      · intro x hx
        simp only [dsScope]
        exact h.2.2 x hx
theorem dsCases_congr {vs fs : List Ident} :
    ∀ (st₁ st₂ : St) (n : Nat) (cs : List (Literal × List (Stmt Op))), st₁.2 = st₂.2 →
      (∀ x ∈ vs, substOf st₁.1 x = substOf st₂.1 x) →
      NormalForm.ScopedCases vs fs cs →
      dsCases st₁ n cs = dsCases st₂ n cs
  | st₁, st₂, n, [], hδ, hag, _ => by simp only [dsCases]
  | st₁, st₂, n, (l, body) :: rest, hδ, hag, hsc => by
      obtain ⟨hb, hr⟩ := (hsc :
        NormalForm.ScopedStmts vs (fs ++ NormalForm.funDefNames body) body ∧
        NormalForm.ScopedCases vs fs rest)
      have hS := dsScope_congr st₁ st₂ n body hδ hag hb
      have hrest := dsCases_congr st₁ st₂ (dsScope st₂ n body).2.1 rest hδ hag hr
      simp only [dsCases]
      rw [hS.1, hrest]
theorem dsDflt_congr {vs fs : List Ident} :
    ∀ (st₁ st₂ : St) (n : Nat) (dflt : Option (List (Stmt Op))), st₁.2 = st₂.2 →
      (∀ x ∈ vs, substOf st₁.1 x = substOf st₂.1 x) →
      NormalForm.ScopedDflt vs fs dflt →
      dsDflt st₁ n dflt = dsDflt st₂ n dflt
  | st₁, st₂, n, none, hδ, hag, _ => by simp only [dsDflt]
  | st₁, st₂, n, some body, hδ, hag, hsc => by
      have hb : NormalForm.ScopedStmts vs (fs ++ NormalForm.funDefNames body) body := hsc
      have hS := dsScope_congr st₁ st₂ n body hδ hag hb
      simp only [dsDflt]
      rw [hS.1]
end

/-! ### The instance proper

By mutual structural recursion mirroring the transform: for a valid source
program, the transform's output is α-related to the source at the pass's own
renamings (`substOf` of the threaded state), and the output state satisfies the
counter discipline at the output counter. -/

/-- Counter monotonicity for a statement (from the `RangeNodup` invariant). -/
theorem dsStmt_counter_le (st : St) (n : Nat) (s : Stmt Op) (hwf : WFInnerS s) :
    n ≤ (dsStmt st n s).2.1 :=
  (dsStmtInner_rn st n s hwf).2.2

/-- Counter monotonicity for switch cases. -/
theorem dsCases_counter_le (st : St) (n : Nat) (cs : List (Literal × List (Stmt Op)))
    (hwf : WFCases cs) : n ≤ (dsCases st n cs).1 :=
  (dsCases_rn st n cs hwf).2.2

/-- Counter monotonicity for a switch default. -/
theorem dsDflt_counter_le (st : St) (n : Nat) (dflt : Option (List (Stmt Op)))
    (hwf : WFDflt dflt) : n ≤ (dsDflt st n dflt).1 :=
  (dsDflt_rn st n dflt hwf).2.2

/-- Counter monotonicity for a scope. -/
theorem dsScope_counter_le (st : St) (n : Nat) (body : List (Stmt Op))
    (hnd : (funNames body).Nodup) (hwf : WFInner body) :
    n ≤ (dsScope st n body).2.1 := by
  have h := scopeRN st n body hnd (by
    simp only [dsScope]
    exact dsStmtsInner_rn _ _ body hwf)
  exact h.2.2

mutual
theorem alpha_dsExpr (st : St) :
    ∀ e : Expr Op, SVExpr e →
      AlphaExpr (substOf st.1) (substOf st.2) e (dsExpr st e)
  | .lit l, _ => by simp only [dsExpr]; exact .lit
  | .var x, hsv => by
      simp only [dsExpr]
      exact .var (hsv : NotFresh x)
  | .builtin op args, hsv => by
      simp only [dsExpr]
      exact .builtin (alpha_dsArgs st args hsv)
  | .call fn args, hsv => by
      simp only [dsExpr]
      exact .call hsv.1 (alpha_dsArgs st args hsv.2)
theorem alpha_dsArgs (st : St) :
    ∀ es : List (Expr Op), SVArgs es →
      AlphaArgs (substOf st.1) (substOf st.2) es (dsArgs st es)
  | [], _ => by simp only [dsArgs]; exact .nil
  | e :: rest, hsv => by
      simp only [dsArgs]
      exact .cons (alpha_dsExpr st e hsv.1) (alpha_dsArgs st rest hsv.2)
end

mutual
theorem alpha_dsStmt {vs fs : List Ident} :
    ∀ (st : St) (n : Nat) (s : Stmt Op), StOK st n → SVStmt s → WFInnerS s →
      NormalForm.ScopedStmt vs fs s →
      AlphaStmt1 (substOf st.1) (substOf st.2) s (dsStmt st n s).2.2
        (substOf (dsStmt st n s).1.1) (substOf (dsStmt st n s).1.2) ∧
      StOK (dsStmt st n s).1 (dsStmt st n s).2.1
  | st, n, .letDecl vars eo, hst, hsv, hwf, hns => by
      obtain ⟨hvnd, hvNF, hsve⟩ := (hsv : vars.Nodup ∧ (∀ x ∈ vars, NotFresh x) ∧
        (∀ e, eo = some e → SVExpr e))
      have hoe : AlphaOExpr (substOf st.1) (substOf st.2) eo (eo.map (dsExpr st)) := by
        cases eo with
        | none => exact .none
        | some e => exact .some (alpha_dsExpr st e (hsve e rfl))
      have hStOK : StOK (vars.zip (freshVars n vars) ++ st.1, st.2) (n + vars.length) :=
        ⟨hst.1.extend (Nat.le_add_right _ _) (zip_fresh_ok hvNF n),
          hst.2.mono (Nat.le_add_right _ _)⟩
      constructor
      · simp only [dsStmt]
        rw [substOf_append]
        exact AlphaStmt1.letD hvnd (freshVars_nodup n vars)
          (freshVars_length n vars).symm hvNF
          (fun v' hv' => (freshVars_mem hv').imp (fun k hk => hk.2.2))
          (fun v' hv' z hz => by
            obtain ⟨k, hk1, _, hk3⟩ := freshVars_mem hv'
            rw [hk3]
            exact hst.1.fresh_ne hz hk1)
          hoe
      · simp only [dsStmt]
        exact hStOK
  | st, n, .assign vars e, hst, hsv, hwf, hns => by
      obtain ⟨hvNF, hsve⟩ := (hsv : (∀ x ∈ vars, NotFresh x) ∧ SVExpr e)
      constructor
      · simp only [dsStmt]
        exact AlphaStmt1.assignD hvNF (alpha_dsExpr st e hsve)
      · simp only [dsStmt]
        exact hst
  | st, n, .exprStmt e, hst, hsv, hwf, hns => by
      constructor
      · simp only [dsStmt]
        exact AlphaStmt1.exprD (alpha_dsExpr st e (hsv : SVExpr e))
      · simp only [dsStmt]
        exact hst
  | st, n, .block body, hst, hsv, hwf, hns => by
      obtain ⟨hnd, hwfI⟩ := (hwf : (funNames body).Nodup ∧ WFInner body)
      have hS := alpha_dsScope st n body hst (hsv : SVStmts body) hnd hwfI
        (hns : NormalForm.ScopedStmts vs (fs ++ NormalForm.funDefNames body) body)
      constructor
      · simp only [dsStmt]
        exact AlphaStmt1.blockD hS.1
      · simp only [dsStmt]
        exact hst.mono (dsScope_counter_le st n body hnd hwfI)
  | st, n, .cond c body, hst, hsv, hwf, hns => by
      obtain ⟨hsvc, hsvb⟩ := (hsv : SVExpr c ∧ SVStmts body)
      obtain ⟨hnd, hwfI⟩ := (hwf : (funNames body).Nodup ∧ WFInner body)
      obtain ⟨hnsc, hnsb⟩ := (hns : NormalForm.ScopedExpr vs fs c ∧
        NormalForm.ScopedStmts vs (fs ++ NormalForm.funDefNames body) body)
      have hS := alpha_dsScope st n body hst hsvb hnd hwfI hnsb
      constructor
      · simp only [dsStmt]
        exact AlphaStmt1.condD (alpha_dsExpr st c hsvc) hS.1
      · simp only [dsStmt]
        exact hst.mono (dsScope_counter_le st n body hnd hwfI)
  | st, n, .switch c cases dflt, hst, hsv, hwf, hns => by
      obtain ⟨hsvc, hsvcs, hsvd⟩ := (hsv : SVExpr c ∧ SVCases cases ∧ SVDflt dflt)
      obtain ⟨hwfcs, hwfd⟩ := (hwf : WFCases cases ∧ WFDflt dflt)
      obtain ⟨hnsc, hnscs, hnsd⟩ := (hns : NormalForm.ScopedExpr vs fs c ∧
        NormalForm.ScopedCases vs fs cases ∧ NormalForm.ScopedDflt vs fs dflt)
      have hCS := alpha_dsCases st n cases hst hsvcs hwfcs hnscs
      have hD := alpha_dsDflt st (dsCases st n cases).1 dflt hCS.2 hsvd hwfd hnsd
      constructor
      · simp only [dsStmt]
        exact AlphaStmt1.switchD (alpha_dsExpr st c hsvc) hCS.1 hD.1
      · simp only [dsStmt]
        exact hst.mono (Nat.le_trans (dsCases_counter_le st n cases hwfcs)
          (dsDflt_counter_le st _ dflt hwfd))
  | st, n, .funDef fname params rets body, hst, hsv, hwf, hns => by
      obtain ⟨hfNF, hprnd, hprNF, hsvb⟩ := (hsv : NotFresh fname ∧ (params ++ rets).Nodup ∧
        (∀ x ∈ params ++ rets, NotFresh x) ∧ SVStmts body)
      obtain ⟨hnd, hwfI⟩ := (hwf : (funNames body).Nodup ∧ WFInner body)
      have hnsb : NormalForm.ScopedStmts (params ++ rets)
          (fs ++ NormalForm.funDefNames body) body := hns
      -- the trimmed state: params/rets zips only (function bodies see no outer vars)
      have hagT : ∀ x ∈ params ++ rets,
          substOf (params.zip (freshVars n params) ++
              rets.zip (freshVars (n + params.length) rets) ++ st.1) x
          = substOf ((params.zip (freshVars n params) ++
              rets.zip (freshVars (n + params.length) rets), st.2) : St).1 x := by
        intro x hx
        show substOf (params.zip (freshVars n params) ++
            rets.zip (freshVars (n + params.length) rets) ++ st.1) x
          = substOf (params.zip (freshVars n params) ++
            rets.zip (freshVars (n + params.length) rets)) x
        rw [substOf_append]
        cases hfind : (params.zip (freshVars n params) ++
            rets.zip (freshVars (n + params.length) rets)).find? (fun p => p.1 = x) with
        | some p => simp [updRen, substOf, hfind]
        | none =>
            exfalso
            rw [List.find?_append] at hfind
            have h1 : (params.zip (freshVars n params)).find? (fun p => p.1 = x) = none := by
              cases hh : (params.zip (freshVars n params)).find? (fun p => p.1 = x) with
              | none => rfl
              | some p => rw [hh] at hfind; simp at hfind
            have h2 : (rets.zip (freshVars (n + params.length) rets)).find?
                (fun p => p.1 = x) = none := by
              rw [h1] at hfind; simpa using hfind
            have hnp := find?_zip_none_not_mem
              (by rw [freshVars_length]; exact Nat.le_refl _) h1
            have hnr := find?_zip_none_not_mem
              (by rw [freshVars_length]; exact Nat.le_refl _) h2
            rcases List.mem_append.mp hx with h | h
            · exact hnp h
            · exact hnr h
      have hcongr := dsScope_congr
        (params.zip (freshVars n params) ++
          rets.zip (freshVars (n + params.length) rets) ++ st.1, st.2)
        (params.zip (freshVars n params) ++
          rets.zip (freshVars (n + params.length) rets), st.2)
        (n + params.length + rets.length) body rfl hagT hnsb
      have hStT : StOK (params.zip (freshVars n params) ++
          rets.zip (freshVars (n + params.length) rets), st.2)
          (n + params.length + rets.length) := by
        constructor
        · intro p hp
          rcases List.mem_append.mp hp with h | h
          · exact ((zip_fresh_ok (fun x hx => hprNF x (List.mem_append.mpr (Or.inl hx))) n
              p h).imp_right (fun ⟨k, hk, he⟩ => ⟨k,
                Nat.lt_of_lt_of_le hk (Nat.le_add_right _ _), he⟩))
          · exact ((zip_fresh_ok (fun x hx => hprNF x (List.mem_append.mpr (Or.inr hx)))
              (n + params.length) p h).imp_right (fun ⟨k, hk, he⟩ => ⟨k, hk, he⟩))
        · exact hst.2.mono (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))
      have hS := alpha_dsScope
        (params.zip (freshVars n params) ++
          rets.zip (freshVars (n + params.length) rets), st.2)
        (n + params.length + rets.length) body hStT hsvb hnd hwfI hnsb
      constructor
      · simp only [dsStmt]
        rw [show (dsScope (params.zip (freshVars n params) ++
              rets.zip (freshVars (n + params.length) rets) ++ st.1, st.2)
              (n + params.length + rets.length) body).2.2
            = (dsScope (params.zip (freshVars n params) ++
              rets.zip (freshVars (n + params.length) rets), st.2)
              (n + params.length + rets.length) body).2.2 from
          congrArg Prod.snd hcongr.1]
        have hnd' : (freshVars n params ++ freshVars (n + params.length) rets).Nodup :=
          (RangeNodup.append (freshVars_rangeNodup n params)
            (freshVars_rangeNodup (n + params.length) rets)).2.1
        have hds' : ∀ v' ∈ freshVars n params ++ freshVars (n + params.length) rets,
            ∃ k, v' = dsName k := by
          intro v' hv'
          rcases List.mem_append.mp hv' with h | h
          · exact (freshVars_mem h).imp (fun k hk => hk.2.2)
          · exact (freshVars_mem h).imp (fun k hk => hk.2.2)
        exact AlphaStmt1.funD hprnd hnd' (freshVars_length n params).symm
          (freshVars_length (n + params.length) rets).symm hprNF hds'
          (by rw [← substOf_eq_updRen_id]; exact hS.1)
      · simp only [dsStmt]
        refine hst.mono ?_
        refine Nat.le_trans (Nat.le_trans (Nat.le_add_right n params.length)
          (Nat.le_add_right _ rets.length)) ?_
        exact dsScope_counter_le _ _ body hnd hwfI
  | st, n, .forLoop init c post body, hst, hsv, hwf, hns => by
      obtain ⟨hsvi, hsvc, hsvp, hsvb⟩ :=
        (hsv : SVStmts init ∧ SVExpr c ∧ SVStmts post ∧ SVStmts body)
      obtain ⟨⟨hndi, hwfi⟩, ⟨hndb, hwfb⟩, hndp, hwfp⟩ :=
        (hwf : ((funNames init).Nodup ∧ WFInner init) ∧
          ((funNames body).Nodup ∧ WFInner body) ∧
          ((funNames post).Nodup ∧ WFInner post))
      obtain ⟨hnsi, hnsc, hnsp, hnsb⟩ := (hns :
        NormalForm.ScopedStmts vs (fs ++ NormalForm.funDefNames init) init ∧
        NormalForm.ScopedExpr (vs ++ NormalForm.declTopVarsL init)
          (fs ++ NormalForm.funDefNames init) c ∧
        NormalForm.ScopedStmts (vs ++ NormalForm.declTopVarsL init)
          ((fs ++ NormalForm.funDefNames init) ++ NormalForm.funDefNames post) post ∧
        NormalForm.ScopedStmts (vs ++ NormalForm.declTopVarsL init)
          ((fs ++ NormalForm.funDefNames init) ++ NormalForm.funDefNames body) body)
      have hI := alpha_dsScope st n init hst hsvi hndi hwfi hnsi
      have hB := alpha_dsScope (dsScope st n init).1 (dsScope st n init).2.1 body
        hI.2 hsvb hndb hwfb hnsb
      have hP := alpha_dsScope (dsScope st n init).1
        (dsScope (dsScope st n init).1 (dsScope st n init).2.1 body).2.1 post
        (hI.2.mono (dsScope_counter_le _ _ body hndb hwfb)) hsvp hndp hwfp hnsp
      constructor
      · simp only [dsStmt]
        exact AlphaStmt1.forD hI.1 (alpha_dsExpr (dsScope st n init).1 c hsvc) hB.1 hP.1
      · simp only [dsStmt]
        refine hst.mono ?_
        refine Nat.le_trans (dsScope_counter_le st n init hndi hwfi) ?_
        refine Nat.le_trans (dsScope_counter_le (dsScope st n init).1
          (dsScope st n init).2.1 body hndb hwfb) ?_
        exact dsScope_counter_le (dsScope st n init).1
          (dsScope (dsScope st n init).1 (dsScope st n init).2.1 body).2.1 post hndp hwfp
  | st, n, .«break», hst, _, _, _ => by
      refine ⟨?_, by simp only [dsStmt]; exact hst⟩
      simp only [dsStmt]
      exact AlphaStmt1.breakD
  | st, n, .«continue», hst, _, _, _ => by
      refine ⟨?_, by simp only [dsStmt]; exact hst⟩
      simp only [dsStmt]
      exact AlphaStmt1.contD
  | st, n, .leave, hst, _, _, _ => by
      refine ⟨?_, by simp only [dsStmt]; exact hst⟩
      simp only [dsStmt]
      exact AlphaStmt1.leaveD
theorem alpha_dsStmts {vs fs : List Ident} :
    ∀ (st : St) (n : Nat) (ss : List (Stmt Op)), StOK st n → SVStmts ss → WFInner ss →
      NormalForm.ScopedStmts vs fs ss →
      AlphaSeqExt (substOf st.1) (substOf st.2) ss (dsStmts st n ss).2.2
        (substOf (dsStmts st n ss).1.1) (substOf (dsStmts st n ss).1.2) ∧
      StOK (dsStmts st n ss).1 (dsStmts st n ss).2.1
  | st, n, [], hst, _, _, _ => by
      refine ⟨?_, by simp only [dsStmts]; exact hst⟩
      simp only [dsStmts]
      exact AlphaSeqExt.nil
  | st, n, s :: rest, hst, hsv, hwf, hns => by
      obtain ⟨hsvs, hsvr⟩ := (hsv : SVStmt s ∧ SVStmts rest)
      obtain ⟨hwfs, hwfr⟩ := (hwf : WFInnerS s ∧ WFInner rest)
      obtain ⟨hnss, hnsr⟩ := (hns : NormalForm.ScopedStmt vs fs s ∧
        NormalForm.ScopedStmts (vs ++ NormalForm.declTopVars s) fs rest)
      have hh := alpha_dsStmt st n s hst hsvs hwfs hnss
      have ht := alpha_dsStmts (dsStmt st n s).1 (dsStmt st n s).2.1 rest hh.2 hsvr hwfr hnsr
      refine ⟨?_, by simp only [dsStmts]; exact ht.2⟩
      simp only [dsStmts]
      exact AlphaSeqExt.cons hh.1 ht.1
theorem alpha_dsScope {vs fs : List Ident} :
    ∀ (st : St) (n : Nat) (body : List (Stmt Op)), StOK st n → SVStmts body →
      (funNames body).Nodup → WFInner body →
      NormalForm.ScopedStmts vs fs body →
      AlphaBlockExt (substOf st.1) (substOf st.2) body (dsScope st n body).2.2
        (substOf (dsScope st n body).1.1) (substOf (dsScope st n body).1.2) ∧
      StOK (dsScope st n body).1 (dsScope st n body).2.1
  | st, n, body, hst, hsv, hnd, hwf, hns => by
      have hStOK : StOK (st.1, (funNames body).zip (freshVars n (funNames body)) ++ st.2)
          (n + (funNames body).length) :=
        ⟨hst.1.mono (Nat.le_add_right _ _),
          hst.2.extend (Nat.le_add_right _ _) (zip_fresh_ok (funNames_notFresh hsv) n)⟩
      have hSeq := alpha_dsStmts
        (st.1, (funNames body).zip (freshVars n (funNames body)) ++ st.2)
        (n + (funNames body).length) body hStOK hsv hwf hns
      have hfn2 : funNames (dsStmts (st.1,
            (funNames body).zip (freshVars n (funNames body)) ++ st.2)
            (n + (funNames body).length) body).2.2 = freshVars n (funNames body) := by
        rw [dsStmts_funNames]
        exact map_substOf_zip hnd (by rw [freshVars_length])
      refine ⟨?_, by simp only [dsScope]; exact hSeq.2⟩
      simp only [dsScope]
      refine AlphaBlockExt.mk hnd ?_ ?_ (funNames_notFresh hsv) ?_ ?_ ?_
      · rw [hfn2, freshVars_length]
      · rw [hfn2]
        exact freshVars_nodup _ _
      · rw [hfn2]
        intro v' hv'
        exact (freshVars_mem hv').imp (fun k hk => hk.2.2)
      · rw [hfn2]
        intro v' hv' z hz
        obtain ⟨k, hk1, _, hk3⟩ := freshVars_mem hv'
        rw [hk3]
        exact hst.2.fresh_ne hz hk1
      · rw [hfn2, ← substOf_append]
        exact hSeq.1
theorem alpha_dsCases {vs fs : List Ident} :
    ∀ (st : St) (n : Nat) (cs : List (Literal × List (Stmt Op))), StOK st n → SVCases cs →
      WFCases cs → NormalForm.ScopedCases vs fs cs →
      AlphaCases (substOf st.1) (substOf st.2) cs (dsCases st n cs).2 ∧
      StOK st (dsCases st n cs).1
  | st, n, [], hst, _, _, _ => by
      refine ⟨?_, by simp only [dsCases]; exact hst⟩
      simp only [dsCases]
      exact AlphaCases.nil
  | st, n, (l, body) :: rest, hst, hsv, hwf, hns => by
      obtain ⟨hsvb, hsvr⟩ := (hsv : SVStmts body ∧ SVCases rest)
      obtain ⟨⟨hndb, hwfb⟩, hwfr⟩ :=
        (hwf : ((funNames body).Nodup ∧ WFInner body) ∧ WFCases rest)
      obtain ⟨hnsb, hnsr⟩ := (hns :
        NormalForm.ScopedStmts vs (fs ++ NormalForm.funDefNames body) body ∧
        NormalForm.ScopedCases vs fs rest)
      have hB := alpha_dsScope st n body hst hsvb hndb hwfb hnsb
      have hR := alpha_dsCases st (dsScope st n body).2.1 rest
        (hst.mono (dsScope_counter_le st n body hndb hwfb)) hsvr hwfr hnsr
      refine ⟨?_, by simp only [dsCases]; exact hR.2⟩
      simp only [dsCases]
      exact AlphaCases.cons hB.1 hR.1
theorem alpha_dsDflt {vs fs : List Ident} :
    ∀ (st : St) (n : Nat) (dflt : Option (List (Stmt Op))), StOK st n → SVDflt dflt →
      WFDflt dflt → NormalForm.ScopedDflt vs fs dflt →
      AlphaDflt (substOf st.1) (substOf st.2) dflt (dsDflt st n dflt).2 ∧
      StOK st (dsDflt st n dflt).1
  | st, n, none, hst, _, _, _ => by
      refine ⟨?_, by simp only [dsDflt]; exact hst⟩
      simp only [dsDflt]
      exact AlphaDflt.none
  | st, n, some body, hst, hsv, hwf, hns => by
      obtain ⟨hndb, hwfb⟩ := (hwf : (funNames body).Nodup ∧ WFInner body)
      have hnsb : NormalForm.ScopedStmts vs (fs ++ NormalForm.funDefNames body) body := hns
      have hB := alpha_dsScope st n body hst (hsv : SVStmts body) hndb hwfb hnsb
      refine ⟨?_, ?_⟩
      · simp only [dsDflt]
        exact AlphaDflt.some hB.1
      · simp only [dsDflt]
        exact hst.mono (dsScope_counter_le st n body hndb hwfb)
end

/-- **The connection**: for a valid, well-formed, well-scoped source block, the
disambiguated program is α-related to the source from the empty renaming state. -/
theorem alpha_disambiguate (b : Block Op) (hsv : SVStmts b) (hwf : WellFormed b)
    (hns : NormalForm.WellScoped b) :
    AlphaBlockExt (substOf ([] : Subst)) (substOf ([] : Subst)) b (disambiguate b)
      (substOf (dsScope (([], []) : St) 0 b).1.1)
      (substOf (dsScope (([], []) : St) 0 b).1.2) :=
  (alpha_dsScope (([], []) : St) 0 b
    ⟨fun _ hp => (List.not_mem_nil hp).elim, fun _ hp => (List.not_mem_nil hp).elim⟩
    hsv hwf.1 hwf.2 hns).1

end YulEvmCompiler.Optimizer.Normalize
