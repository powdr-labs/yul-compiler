import YulSemantics.Ast
import Mathlib.Data.List.Basic
/-!
# Normalization pass: name disambiguation

Rename every *declared* name — all `let`-bound variables, every function's
parameters and returns, and every function's name — to a globally-fresh name,
consistently updating references, so that no two declarations in the whole
program share a name.

Freshness is driven by one monotonically-increasing counter threaded through the
whole syntax tree, so distinct declarations receive distinct indices (hence
distinct names). Two scoped substitutions carry the current renaming of in-scope
variables (`st.1`) and functions (`st.2`); references are rewritten to match
their binder, and extensions made inside a nested scope are discarded on exit
(the counter is *not* — uniqueness is global).

The postcondition is `Disambiguated`: the list of all declared names has no
duplicates. `disambiguate_disambiguated` proves the pass establishes it. This is
a structural / form guarantee (like `anfNormalize_isANF`); semantic soundness of
the renaming is separate future work.

**Scope note / current limitation.** Yul makes a function visible throughout its
whole enclosing block, including *before* its definition (forward references).
This pass resolves references left-to-right, so it renames the definition and
all *later* uses correctly, but does not yet rewire a call that textually
precedes its callee's definition in the same block. That affects renaming
*fidelity* (a follow-up two-pass version pre-scans each block's function names);
it does not affect the disambiguation *property* proved here.
-/

namespace YulEvmCompiler.Optimizer.Normalize

open YulSemantics

variable {Op : Type}

/-! ### Fresh names -/

/-- The `k`-th fresh name. A unary suffix makes distinctness a `List.length`
fact (avoiding `Nat`-to-`String` injectivity lemmas). -/
def dsName (k : Nat) : Ident := String.ofList (List.replicate (k + 1) 'v')

theorem dsName_inj {i j : Nat} (h : dsName i = dsName j) : i = j := by
  simp only [dsName, String.ofList_inj] at h
  have := congrArg List.length h
  simpa using this

/-- Fresh names for a list of variables, starting at index `n` (one per element). -/
def freshVars (n : Nat) : List Ident → List Ident
  | [] => []
  | _ :: rest => dsName n :: freshVars (n + 1) rest

@[simp] theorem freshVars_length (n : Nat) (vars : List Ident) :
    (freshVars n vars).length = vars.length := by
  induction vars generalizing n with
  | nil => rfl
  | cons _ rest ih => simp [freshVars, ih]

/-! ### The renaming state

`st.1` renames in-scope *variables*; `st.2` renames in-scope *functions*. Kept as
one pair so the transform's result tuples (and hence the proofs' projections)
have a fixed shape. -/

/-- One renaming binding (innermost first). -/
abbrev Subst := List (Ident × Ident)

/-- A pair of substitutions: variables and functions. -/
abbrev St := Subst × Subst

/-- Resolve a name to its current renaming (unbound names are kept). -/
def substOf (σ : Subst) (x : Ident) : Ident :=
  ((σ.find? (fun p => p.1 = x)).map Prod.snd).getD x

/-! ### The transform -/

mutual
def dsExpr (st : St) : Expr Op → Expr Op
  | .lit l => .lit l
  | .var x => .var (substOf st.1 x)
  | .builtin op args => .builtin op (dsArgs st args)
  | .call fn args => .call (substOf st.2 fn) (dsArgs st args)
def dsArgs (st : St) : List (Expr Op) → List (Expr Op)
  | [] => []
  | e :: rest => dsExpr st e :: dsArgs st rest
end

mutual
/-- Disambiguate one statement: returns the state extended with the statement's
declarations (for the rest of the *same* scope), the advanced counter, and the
renamed statement. Written with explicit projections (not pattern-`let`s) so the
equation lemmas reduce cleanly in proofs. -/
def dsStmt (st : St) (n : Nat) : Stmt Op → St × Nat × Stmt Op
  | .letDecl vars val =>
      (((vars.zip (freshVars n vars)) ++ st.1, st.2), n + vars.length,
        .letDecl (freshVars n vars) (val.map (dsExpr st)))
  | .assign vars val =>
      (st, n, .assign (vars.map (substOf st.1)) (dsExpr st val))
  | .exprStmt e => (st, n, .exprStmt (dsExpr st e))
  | .block body => (st, (dsBlock st n body).1, .block (dsBlock st n body).2)
  | .cond c body => (st, (dsBlock st n body).1, .cond (dsExpr st c) (dsBlock st n body).2)
  | .switch c cases dflt =>
      (st, (dsDflt st (dsCases st n cases).1 dflt).1,
        .switch (dsExpr st c) (dsCases st n cases).2 (dsDflt st (dsCases st n cases).1 dflt).2)
  | .funDef fname params rets body =>
      let stBody : St :=
        ((params.zip (freshVars (n + 1) params)) ++
          (rets.zip (freshVars (n + 1 + params.length) rets)) ++ st.1,
         (fname, dsName n) :: st.2)
      let nBody := n + 1 + params.length + rets.length
      ((st.1, (fname, dsName n) :: st.2), (dsBlock stBody nBody body).1,
        .funDef (dsName n) (freshVars (n + 1) params) (freshVars (n + 1 + params.length) rets)
          (dsBlock stBody nBody body).2)
  | .forLoop init c post body =>
      let st1 := (dsStmts st n init).1
      let n1 := (dsStmts st n init).2.1
      (st, (dsBlock st1 (dsBlock st1 n1 body).1 post).1,
        .forLoop (dsStmts st n init).2.2 (dsExpr st1 c)
          (dsBlock st1 (dsBlock st1 n1 body).1 post).2 (dsBlock st1 n1 body).2)
  | .«break» => (st, n, .«break»)
  | .«continue» => (st, n, .«continue»)
  | .leave => (st, n, .leave)
def dsStmts (st : St) (n : Nat) : List (Stmt Op) → St × Nat × List (Stmt Op)
  | [] => (st, n, [])
  | s :: rest =>
      ((dsStmts (dsStmt st n s).1 (dsStmt st n s).2.1 rest).1,
        (dsStmts (dsStmt st n s).1 (dsStmt st n s).2.1 rest).2.1,
        (dsStmt st n s).2.2 :: (dsStmts (dsStmt st n s).1 (dsStmt st n s).2.1 rest).2.2)
def dsBlock (st : St) (n : Nat) (body : List (Stmt Op)) : Nat × List (Stmt Op) :=
  ((dsStmts st n body).2.1, (dsStmts st n body).2.2)
def dsCases (st : St) (n : Nat) :
    List (Literal × List (Stmt Op)) → Nat × List (Literal × List (Stmt Op))
  | [] => (n, [])
  | (l, body) :: rest =>
      ((dsCases st (dsBlock st n body).1 rest).1,
        (l, (dsBlock st n body).2) :: (dsCases st (dsBlock st n body).1 rest).2)
def dsDflt (st : St) (n : Nat) :
    Option (List (Stmt Op)) → Nat × Option (List (Stmt Op))
  | none => (n, none)
  | some body => ((dsBlock st n body).1, some (dsBlock st n body).2)
end

/-- The disambiguation normalizer: rename from empty scopes with counter `0`. -/
def disambiguate (b : Block Op) : Block Op := (dsBlock (([], []) : St) 0 b).2

/-! ### The postcondition -/

mutual
/-- All names declared anywhere in a statement — variables *and* function names
(recursing into every scope). -/
def declaredS : Stmt Op → List Ident
  | .letDecl vars _ => vars
  | .funDef fn ps rs body => fn :: ps ++ rs ++ declaredSs body
  | .block body => declaredSs body
  | .cond _ body => declaredSs body
  | .switch _ cases dflt => declaredCases cases ++ declaredDflt dflt
  | .forLoop init _ post body => declaredSs init ++ declaredSs body ++ declaredSs post
  | _ => []
def declaredSs : List (Stmt Op) → List Ident
  | [] => []
  | s :: rest => declaredS s ++ declaredSs rest
def declaredCases : List (Literal × List (Stmt Op)) → List Ident
  | [] => []
  | (_, body) :: rest => declaredSs body ++ declaredCases rest
def declaredDflt : Option (List (Stmt Op)) → List Ident
  | none => []
  | some body => declaredSs body
end

/-- **The disambiguation property**: no name (variable or function) is declared
twice anywhere in the program. -/
def Disambiguated (b : Block Op) : Prop := (declaredSs b).Nodup

/-! ### Proof that the pass establishes `Disambiguated`

Invariant: the names declared by transforming a component with counter `lo`,
ending at `hi`, are `dsName` of *distinct* indices in `[lo, hi)`. Concatenating
components with consecutive ranges keeps them distinct (disjoint ranges +
`dsName` injective). -/

/-- Declared names lie in `dsName '' [lo, hi)`, are duplicate-free, and `lo ≤ hi`. -/
def RangeNodup (decl : List Ident) (lo hi : Nat) : Prop :=
  (∀ x ∈ decl, ∃ i, lo ≤ i ∧ i < hi ∧ x = dsName i) ∧ decl.Nodup ∧ lo ≤ hi

theorem RangeNodup.nil (lo : Nat) : RangeNodup [] lo lo :=
  ⟨fun _ hx => absurd hx List.not_mem_nil, List.nodup_nil, Nat.le_refl _⟩

theorem RangeNodup.singleton (n : Nat) : RangeNodup [dsName n] n (n + 1) :=
  ⟨fun x hx => by rw [List.mem_singleton] at hx; exact ⟨n, Nat.le_refl _, Nat.lt_succ_self _, hx⟩,
    by simp, Nat.le_succ _⟩

/-- Two components with consecutive ranges concatenate to a duplicate-free list. -/
theorem RangeNodup.append {a b : List Ident} {lo mid hi : Nat}
    (ha : RangeNodup a lo mid) (hb : RangeNodup b mid hi) : RangeNodup (a ++ b) lo hi := by
  obtain ⟨har, hand, halo⟩ := ha
  obtain ⟨hbr, hbnd, hbhi⟩ := hb
  refine ⟨?_, ?_, Nat.le_trans halo hbhi⟩
  · intro x hx
    rcases List.mem_append.mp hx with h | h
    · obtain ⟨i, h1, h2, h3⟩ := har x h; exact ⟨i, h1, Nat.lt_of_lt_of_le h2 hbhi, h3⟩
    · obtain ⟨i, h1, h2, h3⟩ := hbr x h; exact ⟨i, Nat.le_trans halo h1, h2, h3⟩
  · refine List.nodup_append.mpr ⟨hand, hbnd, ?_⟩
    intro x hxa y hyb heq
    subst heq
    obtain ⟨i, _, hi_lt, hxi⟩ := har x hxa
    obtain ⟨j, hj_ge, _, hxj⟩ := hbr x hyb
    have : i = j := dsName_inj (hxi ▸ hxj)
    omega

theorem freshVars_rangeNodup (n : Nat) (vars : List Ident) :
    RangeNodup (freshVars n vars) n (n + vars.length) := by
  induction vars generalizing n with
  | nil => simpa [freshVars] using RangeNodup.nil n
  | cons v rest ih =>
      have hcomb := RangeNodup.append (RangeNodup.singleton n) (ih (n + 1))
      have hlen : n + 1 + rest.length = n + (v :: rest).length := by simp [List.length_cons]; omega
      rw [hlen] at hcomb
      simpa [freshVars] using hcomb

/-! The main invariant, by mutual induction over the syntax. -/
mutual
theorem dsStmt_rn (st : St) (n : Nat) (s : Stmt Op) :
    RangeNodup (declaredS (dsStmt st n s).2.2) n (dsStmt st n s).2.1 := by
  cases s with
  | letDecl vars val => simp only [dsStmt, declaredS]; exact freshVars_rangeNodup n vars
  | assign vars val => simp only [dsStmt, declaredS]; exact RangeNodup.nil n
  | exprStmt e => simp only [dsStmt, declaredS]; exact RangeNodup.nil n
  | «break» => simp only [dsStmt, declaredS]; exact RangeNodup.nil n
  | «continue» => simp only [dsStmt, declaredS]; exact RangeNodup.nil n
  | leave => simp only [dsStmt, declaredS]; exact RangeNodup.nil n
  | block body => simp only [dsStmt, declaredS]; exact dsBlock_rn st n body
  | cond c body => simp only [dsStmt, declaredS]; exact dsBlock_rn st n body
  | switch c cases dflt =>
      simp only [dsStmt, declaredS]
      exact RangeNodup.append (dsCases_rn st n cases) (dsDflt_rn st _ dflt)
  | funDef fname params rets body =>
      simp only [dsStmt, declaredS]
      exact RangeNodup.append
        (RangeNodup.append
          (RangeNodup.append (RangeNodup.singleton n)
            (freshVars_rangeNodup (n + 1) params))
          (freshVars_rangeNodup (n + 1 + params.length) rets))
        (dsBlock_rn _ _ body)
  | forLoop init c post body =>
      simp only [dsStmt, declaredS]
      exact RangeNodup.append
        (RangeNodup.append (dsStmts_rn st n init) (dsBlock_rn _ _ body))
        (dsBlock_rn _ _ post)
theorem dsStmts_rn (st : St) (n : Nat) (ss : List (Stmt Op)) :
    RangeNodup (declaredSs (dsStmts st n ss).2.2) n (dsStmts st n ss).2.1 := by
  cases ss with
  | nil => simp only [dsStmts, declaredSs]; exact RangeNodup.nil n
  | cons s rest =>
      simp only [dsStmts, declaredSs]
      exact RangeNodup.append (dsStmt_rn st n s) (dsStmts_rn _ _ rest)
theorem dsBlock_rn (st : St) (n : Nat) (body : List (Stmt Op)) :
    RangeNodup (declaredSs (dsBlock st n body).2) n (dsBlock st n body).1 := by
  simp only [dsBlock]; exact dsStmts_rn st n body
theorem dsCases_rn (st : St) (n : Nat) (cases : List (Literal × List (Stmt Op))) :
    RangeNodup (declaredCases (dsCases st n cases).2) n (dsCases st n cases).1 := by
  cases cases with
  | nil => simp only [dsCases, declaredCases]; exact RangeNodup.nil n
  | cons c rest =>
      obtain ⟨l, body⟩ := c
      simp only [dsCases, declaredCases]
      exact RangeNodup.append (dsBlock_rn st n body) (dsCases_rn _ _ rest)
theorem dsDflt_rn (st : St) (n : Nat) (dflt : Option (List (Stmt Op))) :
    RangeNodup (declaredDflt (dsDflt st n dflt).2) n (dsDflt st n dflt).1 := by
  cases dflt with
  | none => simp only [dsDflt, declaredDflt]; exact RangeNodup.nil n
  | some body => simp only [dsDflt, declaredDflt]; exact dsBlock_rn st n body
end

/-- **The disambiguation pass establishes its postcondition.** After
`disambiguate`, no variable or function name is declared twice anywhere. -/
theorem disambiguate_disambiguated (b : Block Op) : Disambiguated (disambiguate b) :=
  (dsBlock_rn (([], []) : St) 0 b).2.1

end YulEvmCompiler.Optimizer.Normalize
