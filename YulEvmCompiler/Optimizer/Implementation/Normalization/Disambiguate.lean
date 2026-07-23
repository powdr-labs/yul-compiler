import YulSemantics.Ast
import Mathlib.Data.List.Basic
/-!
# Normalization pass: name disambiguation

Rename every *declared* name — all `let`-bound variables, every function's
parameters and returns, and every function's name — to a globally-fresh name,
consistently updating references, so that no two declarations in the whole
program share a name.

Freshness is driven by one monotonically-increasing counter threaded through the
whole syntax tree. Two scoped substitutions carry the current renaming of
in-scope variables (`st.1`) and functions (`st.2`). A *scope* (`dsScope`) first
**prescans** its top-level `funDef` names — Yul makes them visible throughout the
whole block, including before their definition — assigning each a fresh name,
then renames the block's statements; substitution extensions are discarded on
scope exit, the counter is not (uniqueness is global).

The postcondition is `Disambiguated`: the list of all declared names has no
duplicates. `disambiguate_disambiguated` proves the pass establishes it for a
well-formed program (no two functions of the same name in one block — which
valid Yul guarantees). Semantic soundness is proved separately.
-/

namespace YulEvmCompiler.Optimizer.Normalize

open YulSemantics

variable {Op : Type}

/-! ### Fresh names -/

/-- The `k`-th fresh name: a leading `NUL` (`Char.ofNat 0`), which cannot occur
in a valid Yul identifier, followed by a unary suffix. The `NUL` makes the name
disjoint from every source identifier (capture-avoidance, for soundness); the
unary suffix makes distinctness a `List.length` fact. -/
def dsName (k : Nat) : Ident := String.ofList (Char.ofNat 0 :: List.replicate (k + 1) 'v')

theorem dsName_inj {i j : Nat} (h : dsName i = dsName j) : i = j := by
  simp only [dsName, String.ofList_inj, List.cons.injEq, true_and] at h
  have := congrArg List.length h
  simpa using this

/-- Fresh names for a list, one per element, starting at index `n`. -/
def freshVars (n : Nat) : List Ident → List Ident
  | [] => []
  | _ :: rest => dsName n :: freshVars (n + 1) rest

@[simp] theorem freshVars_length (n : Nat) (vars : List Ident) :
    (freshVars n vars).length = vars.length := by
  induction vars generalizing n with
  | nil => rfl
  | cons _ rest ih => simp [freshVars, ih]

/-- The names of the `funDef`s declared directly in a block. -/
def funNames : List (Stmt Op) → List Ident
  | [] => []
  | .funDef fn _ _ _ :: rest => fn :: funNames rest
  | _ :: rest => funNames rest

/-! ### The renaming state -/

/-- One renaming binding (innermost first). -/
abbrev Subst := List (Ident × Ident)

/-- A pair of substitutions: variables (`.1`) and functions (`.2`). -/
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
/-- Disambiguate one statement (in a scope whose function names are already in
`st.2` from the enclosing `dsScope` prescan). Returns the state extended with the
statement's variable declarations, the advanced counter, and the renamed
statement. -/
def dsStmt (st : St) (n : Nat) : Stmt Op → St × Nat × Stmt Op
  | .letDecl vars val =>
      (((vars.zip (freshVars n vars)) ++ st.1, st.2), n + vars.length,
        .letDecl (freshVars n vars) (val.map (dsExpr st)))
  | .assign vars val =>
      (st, n, .assign (vars.map (substOf st.1)) (dsExpr st val))
  | .exprStmt e => (st, n, .exprStmt (dsExpr st e))
  | .block body => (st, (dsScope st n body).2.1, .block (dsScope st n body).2.2)
  | .cond c body => (st, (dsScope st n body).2.1, .cond (dsExpr st c) (dsScope st n body).2.2)
  | .switch c cases dflt =>
      (st, (dsDflt st (dsCases st n cases).1 dflt).1,
        .switch (dsExpr st c) (dsCases st n cases).2 (dsDflt st (dsCases st n cases).1 dflt).2)
  | .funDef fname params rets body =>
      let stBody : St :=
        ((params.zip (freshVars n params)) ++ (rets.zip (freshVars (n + params.length) rets)) ++ st.1,
         st.2)
      (st, (dsScope stBody (n + params.length + rets.length) body).2.1,
        .funDef (substOf st.2 fname) (freshVars n params) (freshVars (n + params.length) rets)
          (dsScope stBody (n + params.length + rets.length) body).2.2)
  | .forLoop init c post body =>
      let sc := dsScope st n init
      (st, (dsScope sc.1 (dsScope sc.1 sc.2.1 body).2.1 post).2.1,
        .forLoop sc.2.2 (dsExpr sc.1 c)
          (dsScope sc.1 (dsScope sc.1 sc.2.1 body).2.1 post).2.2 (dsScope sc.1 sc.2.1 body).2.2)
  | .«break» => (st, n, .«break»)
  | .«continue» => (st, n, .«continue»)
  | .leave => (st, n, .leave)
def dsStmts (st : St) (n : Nat) : List (Stmt Op) → St × Nat × List (Stmt Op)
  | [] => (st, n, [])
  | s :: rest =>
      ((dsStmts (dsStmt st n s).1 (dsStmt st n s).2.1 rest).1,
        (dsStmts (dsStmt st n s).1 (dsStmt st n s).2.1 rest).2.1,
        (dsStmt st n s).2.2 :: (dsStmts (dsStmt st n s).1 (dsStmt st n s).2.1 rest).2.2)
/-- A lexical scope: prescan its top-level function names (fresh), then rename
its statements. Returns the extended state (the `for`-loop `init` needs it). -/
def dsScope (st : St) (n : Nat) (body : List (Stmt Op)) : St × Nat × List (Stmt Op) :=
  dsStmts (st.1, (funNames body).zip (freshVars n (funNames body)) ++ st.2)
    (n + (funNames body).length) body
def dsCases (st : St) (n : Nat) :
    List (Literal × List (Stmt Op)) → Nat × List (Literal × List (Stmt Op))
  | [] => (n, [])
  | (l, body) :: rest =>
      ((dsCases st (dsScope st n body).2.1 rest).1,
        (l, (dsScope st n body).2.2) :: (dsCases st (dsScope st n body).2.1 rest).2)
def dsDflt (st : St) (n : Nat) :
    Option (List (Stmt Op)) → Nat × Option (List (Stmt Op))
  | none => (n, none)
  | some body => ((dsScope st n body).2.1, some (dsScope st n body).2.2)
end

/-- The disambiguation normalizer: rename from empty scopes with counter `0`. -/
def disambiguate (b : Block Op) : Block Op := (dsScope (([], []) : St) 0 b).2.2

/-! ### The postcondition -/

mutual
/-- Names declared inside a block *excluding* its own top-level `funDef` names
(collected separately, first, to mirror the prescan). -/
def declaredInner : List (Stmt Op) → List Ident
  | [] => []
  | s :: rest => declaredInnerS s ++ declaredInner rest
def declaredInnerS : Stmt Op → List Ident
  | .letDecl vars _ => vars
  | .funDef _ ps rs body => ps ++ rs ++ (funNames body ++ declaredInner body)
  | .block body => funNames body ++ declaredInner body
  | .cond _ body => funNames body ++ declaredInner body
  | .switch _ cases dflt => declaredCases cases ++ declaredDflt dflt
  | .forLoop init _ post body =>
      (funNames init ++ declaredInner init) ++ (funNames body ++ declaredInner body) ++
        (funNames post ++ declaredInner post)
  | _ => []
def declaredCases : List (Literal × List (Stmt Op)) → List Ident
  | [] => []
  | (_, body) :: rest => (funNames body ++ declaredInner body) ++ declaredCases rest
def declaredDflt : Option (List (Stmt Op)) → List Ident
  | none => []
  | some body => funNames body ++ declaredInner body
end

/-- All names declared anywhere in a block: its top-level `funDef` names first
(prescan order), then the rest. -/
def declaredBlock (body : List (Stmt Op)) : List Ident := funNames body ++ declaredInner body

/-- **The disambiguation property**: no name (variable or function) is declared
twice anywhere in the program. -/
def Disambiguated (b : Block Op) : Prop := (declaredBlock b).Nodup

/-! ### Well-formedness of the input

The pass renames a block's `funDef`s through a name-keyed substitution, so it can
make them distinct only when the source block has no two functions of the same
name — which valid Yul guarantees. `WellFormed` asserts exactly that at every
block. -/
mutual
def WFInner : List (Stmt Op) → Prop
  | [] => True
  | s :: rest => WFInnerS s ∧ WFInner rest
def WFInnerS : Stmt Op → Prop
  | .funDef _ _ _ body => (funNames body).Nodup ∧ WFInner body
  | .block body => (funNames body).Nodup ∧ WFInner body
  | .cond _ body => (funNames body).Nodup ∧ WFInner body
  | .switch _ cases dflt => WFCases cases ∧ WFDflt dflt
  | .forLoop init _ post body =>
      ((funNames init).Nodup ∧ WFInner init) ∧ ((funNames body).Nodup ∧ WFInner body) ∧
        ((funNames post).Nodup ∧ WFInner post)
  | _ => True
def WFCases : List (Literal × List (Stmt Op)) → Prop
  | [] => True
  | (_, body) :: rest => ((funNames body).Nodup ∧ WFInner body) ∧ WFCases rest
def WFDflt : Option (List (Stmt Op)) → Prop
  | none => True
  | some body => (funNames body).Nodup ∧ WFInner body
end

/-- Every block in the program has distinct top-level function names. -/
def WellFormed (b : Block Op) : Prop := (funNames b).Nodup ∧ WFInner b

/-! ### Proof that the pass establishes `Disambiguated`

Invariant `RangeNodup`: the names declared by transforming a component from
counter `lo` to `hi` are `dsName` of *distinct* indices in `[lo, hi)`.
Concatenating consecutive-range components keeps them distinct. -/

/-- Declared names lie in `dsName '' [lo, hi)`, are duplicate-free, and `lo ≤ hi`. -/
def RangeNodup (decl : List Ident) (lo hi : Nat) : Prop :=
  (∀ x ∈ decl, ∃ i, lo ≤ i ∧ i < hi ∧ x = dsName i) ∧ decl.Nodup ∧ lo ≤ hi

theorem RangeNodup.nil (lo : Nat) : RangeNodup [] lo lo :=
  ⟨fun _ hx => absurd hx List.not_mem_nil, List.nodup_nil, Nat.le_refl _⟩

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

theorem RangeNodup.singleton (n : Nat) : RangeNodup [dsName n] n (n + 1) :=
  ⟨fun x hx => by rw [List.mem_singleton] at hx; exact ⟨n, Nat.le_refl _, Nat.lt_succ_self _, hx⟩,
    by simp, Nat.le_succ _⟩

theorem freshVars_rangeNodup (n : Nat) (vars : List Ident) :
    RangeNodup (freshVars n vars) n (n + vars.length) := by
  induction vars generalizing n with
  | nil => simpa [freshVars] using RangeNodup.nil n
  | cons v rest ih =>
      have hcomb := RangeNodup.append (RangeNodup.singleton n) (ih (n + 1))
      have hlen : n + 1 + rest.length = n + (v :: rest).length := by simp [List.length_cons]; omega
      rw [hlen] at hcomb
      simpa [freshVars] using hcomb

/-! Prescan lemmas (function names are renamed to exactly the prescan fresh
names, using well-formedness). All non-mutual. -/

theorem substOf_cons_eq (a b : Ident) (σ : Subst) : substOf ((a, b) :: σ) a = b := by
  simp [substOf, List.find?]

theorem substOf_cons_ne {a z : Ident} (b : Ident) (σ : Subst) (h : ¬ a = z) :
    substOf ((a, b) :: σ) z = substOf σ z := by
  simp [substOf, List.find?, h]

theorem map_substOf_zip : ∀ {xs ys : List Ident} {rest : Subst}, xs.Nodup →
    xs.length = ys.length → xs.map (substOf (xs.zip ys ++ rest)) = ys
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, hlen => by simp at hlen
  | x :: xs, [], _, _, hlen => by simp at hlen
  | x :: xs, y :: ys, rest, hnd, hlen => by
      have hx_notin : x ∉ xs := (List.nodup_cons.mp hnd).1
      simp only [List.zip_cons_cons, List.cons_append, List.map_cons, substOf_cons_eq]
      have htail : xs.map (substOf ((x, y) :: (xs.zip ys ++ rest)))
          = xs.map (substOf (xs.zip ys ++ rest)) :=
        List.map_congr_left (fun z hz => substOf_cons_ne y _ (fun heq => hx_notin (heq ▸ hz)))
      rw [htail, map_substOf_zip (List.nodup_cons.mp hnd).2 (by simpa using hlen)]

theorem funNames_cons_eq (s : Stmt Op) (rest : List (Stmt Op)) :
    funNames (s :: rest) = funNames [s] ++ funNames rest := by
  cases s <;> simp [funNames]

theorem dsStmt_st2 (st : St) (n : Nat) (s : Stmt Op) : (dsStmt st n s).1.2 = st.2 := by
  cases s <;> simp only [dsStmt]

theorem dsStmt_funNames1 (st : St) (n : Nat) (s : Stmt Op) :
    funNames [(dsStmt st n s).2.2] = (funNames [s]).map (substOf st.2) := by
  cases s <;> simp [dsStmt, funNames]

theorem dsStmts_funNames (st : St) (n : Nat) (body : List (Stmt Op)) :
    funNames (dsStmts st n body).2.2 = (funNames body).map (substOf st.2) := by
  induction body generalizing st n with
  | nil => simp [dsStmts, funNames]
  | cons s rest ih =>
      simp only [dsStmts]
      rw [funNames_cons_eq, dsStmt_funNames1, ih, dsStmt_st2, funNames_cons_eq s rest,
        List.map_append]

theorem dsScope_funNames (st : St) (n : Nat) (body : List (Stmt Op))
    (h : (funNames body).Nodup) :
    funNames (dsScope st n body).2.2 = freshVars n (funNames body) := by
  simp only [dsScope]
  rw [dsStmts_funNames]
  exact map_substOf_zip h (by rw [freshVars_length])

/-- A scope's declared names are `RangeNodup`, given its (recursively verified)
inner declarations and well-formedness. Non-mutual: takes the inner range as a
hypothesis so it can be applied from the mutual proof without recursing on the
same block. -/
theorem scopeRN (st : St) (n : Nat) (body : List (Stmt Op)) (hwf : (funNames body).Nodup)
    (hinner : RangeNodup (declaredInner (dsScope st n body).2.2)
      (n + (funNames body).length) (dsScope st n body).2.1) :
    RangeNodup (funNames (dsScope st n body).2.2 ++ declaredInner (dsScope st n body).2.2)
      n (dsScope st n body).2.1 := by
  rw [dsScope_funNames st n body hwf]
  exact RangeNodup.append (freshVars_rangeNodup n (funNames body)) hinner

/-! The main invariant, by mutual induction (recursing only on strict subterms). -/
mutual
theorem dsStmtInner_rn (st : St) (n : Nat) (s : Stmt Op) (h : WFInnerS s) :
    RangeNodup (declaredInnerS (dsStmt st n s).2.2) n (dsStmt st n s).2.1 := by
  cases s with
  | letDecl vars val => simp only [dsStmt, declaredInnerS]; exact freshVars_rangeNodup n vars
  | assign vars val => simp only [dsStmt, declaredInnerS]; exact RangeNodup.nil n
  | exprStmt e => simp only [dsStmt, declaredInnerS]; exact RangeNodup.nil n
  | «break» => simp only [dsStmt, declaredInnerS]; exact RangeNodup.nil n
  | «continue» => simp only [dsStmt, declaredInnerS]; exact RangeNodup.nil n
  | leave => simp only [dsStmt, declaredInnerS]; exact RangeNodup.nil n
  | block body =>
      simp only [dsStmt, declaredInnerS, WFInnerS] at *
      exact scopeRN st n body h.1 (by simp only [dsScope]; exact dsStmtsInner_rn _ _ body h.2)
  | cond c body =>
      simp only [dsStmt, declaredInnerS, WFInnerS] at *
      exact scopeRN st n body h.1 (by simp only [dsScope]; exact dsStmtsInner_rn _ _ body h.2)
  | switch c cases dflt =>
      simp only [dsStmt, declaredInnerS, WFInnerS] at *
      exact RangeNodup.append (dsCases_rn st n cases h.1) (dsDflt_rn st _ dflt h.2)
  | funDef fname params rets body =>
      simp only [dsStmt, declaredInnerS, WFInnerS] at *
      exact RangeNodup.append
        (RangeNodup.append (freshVars_rangeNodup n params)
          (freshVars_rangeNodup (n + params.length) rets))
        (scopeRN _ _ body h.1 (by simp only [dsScope]; exact dsStmtsInner_rn _ _ body h.2))
  | forLoop init c post body =>
      simp only [dsStmt, declaredInnerS, WFInnerS] at *
      exact RangeNodup.append
        (RangeNodup.append
          (scopeRN st n init h.1.1 (by simp only [dsScope]; exact dsStmtsInner_rn _ _ init h.1.2))
          (scopeRN _ _ body h.2.1.1
            (by simp only [dsScope]; exact dsStmtsInner_rn _ _ body h.2.1.2)))
        (scopeRN _ _ post h.2.2.1 (by simp only [dsScope]; exact dsStmtsInner_rn _ _ post h.2.2.2))
theorem dsStmtsInner_rn (st : St) (n : Nat) (ss : List (Stmt Op)) (h : WFInner ss) :
    RangeNodup (declaredInner (dsStmts st n ss).2.2) n (dsStmts st n ss).2.1 := by
  cases ss with
  | nil => simp only [dsStmts, declaredInner]; exact RangeNodup.nil n
  | cons s rest =>
      simp only [dsStmts, declaredInner, WFInner] at *
      exact RangeNodup.append (dsStmtInner_rn st n s h.1) (dsStmtsInner_rn _ _ rest h.2)
theorem dsCases_rn (st : St) (n : Nat) (cases : List (Literal × List (Stmt Op)))
    (h : WFCases cases) :
    RangeNodup (declaredCases (dsCases st n cases).2) n (dsCases st n cases).1 := by
  cases cases with
  | nil => simp only [dsCases, declaredCases]; exact RangeNodup.nil n
  | cons c rest =>
      obtain ⟨l, body⟩ := c
      simp only [dsCases, declaredCases, WFCases] at *
      exact RangeNodup.append
        (scopeRN st n body h.1.1 (by simp only [dsScope]; exact dsStmtsInner_rn _ _ body h.1.2))
        (dsCases_rn _ _ rest h.2)
theorem dsDflt_rn (st : St) (n : Nat) (dflt : Option (List (Stmt Op))) (h : WFDflt dflt) :
    RangeNodup (declaredDflt (dsDflt st n dflt).2) n (dsDflt st n dflt).1 := by
  cases dflt with
  | none => simp only [dsDflt, declaredDflt]; exact RangeNodup.nil n
  | some body =>
      simp only [dsDflt, declaredDflt, WFDflt] at *
      exact scopeRN st n body h.1 (by simp only [dsScope]; exact dsStmtsInner_rn _ _ body h.2)
end

/-- **The disambiguation pass establishes its postcondition.** For a well-formed
program, after `disambiguate` no variable or function name is declared twice. -/
theorem disambiguate_disambiguated (b : Block Op) (h : WellFormed b) :
    Disambiguated (disambiguate b) :=
  (scopeRN ([], []) 0 b h.1 (by simp only [dsScope]; exact dsStmtsInner_rn _ _ b h.2)).2.1

end YulEvmCompiler.Optimizer.Normalize
