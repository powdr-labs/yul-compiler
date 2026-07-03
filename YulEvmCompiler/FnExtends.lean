import YulEvmCompiler.Functions
import YulEvmCompiler.Compile

namespace YulEvmCompiler

open YulSemantics (Expr Stmt Block Ident)
open YulSemantics.EVM (Op)

set_option maxHeartbeats 1000000

/-- The function-aware expression compiler extends the function-free one: whatever
`compileExpr` produces (which is only ever call-free code), `compileExprF`
produces identically, for any table and byte position. -/
theorem compileExprF_extends (ft : FnTable) (Γ : List Ident) (pc off : Nat) (e : Expr Op)
    (is : List Instr) (h : compileExpr Γ off e = some is) :
    compileExprF ft pc Γ off e = some is := by
  refine compileExprF.induct
    (motive_1 := fun pc off e => ∀ is, compileExpr Γ off e = some is →
      compileExprF ft pc Γ off e = some is)
    (motive_2 := fun pc off args => ∀ is, compileArgs Γ off args = some is →
      compileArgsF ft pc Γ off args = some is)
    ?lit ?var ?builtin ?call ?argsNil ?argsCons pc off e is h
  case lit => intro pc off l is h; rw [compileExprF]; rw [compileExpr] at h; exact h
  case var => intro pc off x is h; rw [compileExprF]; rw [compileExpr] at h; exact h
  case builtin =>
      intro pc off op args ihargs is h
      rw [compileExpr] at h
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨argCode, hargs, o, ho, his⟩ := h
      rw [compileExprF]
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff]
      exact ⟨argCode, ihargs argCode hargs, o, ho, his⟩
  case call => intro pc off f args _ is h; rw [compileExpr] at h; exact absurd h (by simp)
  case argsNil => intro pc off is h; rw [compileArgsF]; rw [compileArgs] at h; exact h
  case argsCons =>
      intro pc off e rest ihrest ihe is h
      rw [compileArgs] at h
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨restCode, hrest, eCode, he, his⟩ := h
      rw [compileArgsF]
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff]
      exact ⟨restCode, ihrest restCode hrest, eCode, ihe restCode eCode he, his⟩


/-- The function-aware statement compiler extends the function-free one. -/
theorem compileStmtF_extends (ft : FnTable) :
    ∀ (pc : Nat) (Γ : List Ident) (s : Stmt Op) (is : List Instr) (Γ' : List Ident),
      compileStmt pc Γ s = some (is, Γ') → compileStmtF ft pc Γ s = some (is, Γ') := by
  refine compileStmtF.induct
    (motive_1 := fun pc Γ s => ∀ is Γ', compileStmt pc Γ s = some (is, Γ') →
      compileStmtF ft pc Γ s = some (is, Γ'))
    (motive_2 := fun pc Γ ss => ∀ is Γ', compileStmts pc Γ ss = some (is, Γ') →
      compileStmtsF ft pc Γ ss = some (is, Γ'))
    ?funDef ?exprCall ?exprOther ?letNone ?letCall ?letSingle ?letOther
    ?assignSingle ?assignOther ?block ?cond ?catchAll ?stmtsNil ?stmtsCons
  case funDef => intro pc Γ n p r b is Γ' h; simp [compileStmt] at h
  case exprCall => intro pc Γ f args is Γ' h; simp [compileStmt, compileExpr] at h
  case exprOther =>
      intro pc Γ e hne is Γ' h
      rw [compileStmt] at h
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨c, hc, rfl, rfl⟩ := h
      cases e
      case call f args => exact absurd rfl (hne f args)
      all_goals
        simp only [compileStmtF, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def]
        exact ⟨c, compileExprF_extends ft Γ pc 0 _ c hc, rfl⟩
  case letNone => intro pc Γ xs is Γ' h; rw [compileStmt] at h; rw [compileStmtF]; exact h
  case letCall =>
      intro pc Γ xs f args is Γ' h
      cases xs with
      | nil => simp [compileStmt] at h
      | cons x xs =>
          cases xs with
          | nil => simp [compileStmt, compileExpr] at h
          | cons y ys => simp [compileStmt] at h
  case letSingle =>
      intro pc Γ x e hne is Γ' h
      rw [compileStmt] at h
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨c, hc, rfl, rfl⟩ := h
      cases e
      case call f args => exact absurd rfl (hne f args)
      all_goals
        simp only [compileStmtF, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def]
        exact ⟨c, compileExprF_extends ft Γ pc 0 _ c hc, rfl⟩
  case letOther =>
      intro pc Γ vars val hnecall hnesingle is Γ' h
      cases vars with
      | nil => simp [compileStmt] at h
      | cons x xs =>
          cases xs with
          | nil => exact absurd rfl (hnesingle x)
          | cons y ys => simp [compileStmt] at h
  case assignSingle =>
      intro pc Γ x e is Γ' h
      rw [compileStmt] at h
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨c, hc, idx, hidx, h⟩ := h
      rw [compileStmtF]
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff]
      exact ⟨c, compileExprF_extends ft Γ pc 0 e c hc, idx, hidx, h⟩
  case assignOther =>
      intro pc Γ vars val hnesingle is Γ' h
      cases vars with
      | nil => simp [compileStmt] at h
      | cons x xs =>
          cases xs with
          | nil => exact absurd rfl (hnesingle x)
          | cons y ys => simp [compileStmt] at h
  case block =>
      intro pc Γ body ihbody is Γ' h
      rw [compileStmt] at h
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨isb, Γb⟩, hbc, rfl, rfl⟩ := h
      rw [compileStmtF]
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def]
      exact ⟨(isb, Γb), ihbody isb Γb hbc, rfl⟩
  case cond =>
      intro pc Γ c body ihbody is Γ' h
      rw [compileStmt] at h
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨cCode, hc, ⟨bodyCode, Γb⟩, hbc, rfl, rfl⟩ := h
      rw [compileStmtF]
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def]
      exact ⟨cCode, compileExprF_extends ft Γ pc 0 c cCode hc, (bodyCode, Γb),
        ihbody cCode bodyCode Γb hbc, rfl⟩
  case catchAll =>
      intro t pc Γ hg1 _ hg3 hg4 _ _ hg7 _ hg9 hg10 hg11 is Γ' h
      cases t with
      | funDef n p r b => exact absurd rfl (hg1 n p r b)
      | exprStmt e => exact absurd rfl (hg3 e)
      | letDecl xs v => cases v with
          | none => exact absurd rfl (hg4 xs)
          | some val => exact absurd rfl (hg7 xs val)
      | assign vars val => exact absurd rfl (hg9 vars val)
      | block body => exact absurd rfl (hg10 body)
      | cond c body => exact absurd rfl (hg11 c body)
      | switch c cs d => simp [compileStmt] at h
      | forLoop i c p b => simp [compileStmt] at h
      | «break» => simp [compileStmt] at h
      | «continue» => simp [compileStmt] at h
      | leave => simp [compileStmt] at h
  case stmtsNil =>
      intro pc Γ is Γ' h; rw [compileStmts] at h; rw [compileStmtsF]; exact h
  case stmtsCons =>
      intro pc Γ s rest ihs ihrest is Γ' h
      rw [compileStmts] at h
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨is1, Γ1⟩, hs1, ⟨is2, Γ2⟩, hs2, rfl, rfl⟩ := h
      rw [compileStmtsF]
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def]
      exact ⟨(is1, Γ1), ihs is1 Γ1 hs1, (is2, Γ2), ihrest is1 Γ1 is2 Γ2 hs2, rfl⟩



/-- **Reverse of `extends` for expressions, in a table with no single-return
functions.** When `ft` has no function of return-arity 1, `compileExprF` can
only succeed on call-free expressions (the `.call` case requires
`rets.length = 1`), where it agrees with the function-free `compileExpr`. -/
theorem compileExprF_rev (ft : FnTable)
    (hft : ∀ n info, ft.get? n = some info → info.rets.length ≠ 1) (Γ : List Ident)
    (pc off : Nat) (e : Expr Op) (is : List Instr)
    (h : compileExprF ft pc Γ off e = some is) : compileExpr Γ off e = some is := by
  refine compileExprF.induct
    (motive_1 := fun pc off e => ∀ is, compileExprF ft pc Γ off e = some is →
      compileExpr Γ off e = some is)
    (motive_2 := fun pc off args => ∀ is, compileArgsF ft pc Γ off args = some is →
      compileArgs Γ off args = some is)
    ?lit ?var ?builtin ?call ?argsNil ?argsCons pc off e is h
  case lit => intro pc off l is h; rw [compileExpr]; rw [compileExprF] at h; exact h
  case var => intro pc off x is h; rw [compileExpr]; rw [compileExprF] at h; exact h
  case builtin =>
      intro pc off op args ihargs is h
      rw [compileExprF] at h
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨argCode, hargs, o, ho, his⟩ := h
      rw [compileExpr]
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff]
      exact ⟨argCode, ihargs argCode hargs, o, ho, his⟩
  case call =>
      intro pc off f args _ is h
      rw [compileExprF] at h
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨info, hget, h⟩ := h
      split at h
      · rename_i hcond
        exact absurd hcond.1 (hft f info hget)
      · exact absurd h (by simp)
  case argsNil => intro pc off is h; rw [compileArgs]; rw [compileArgsF] at h; exact h
  case argsCons =>
      intro pc off e rest ihrest ihe is h
      rw [compileArgsF] at h
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨restCode, hrest, eCode, he, his⟩ := h
      rw [compileArgs]
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff]
      exact ⟨restCode, ihrest restCode hrest, eCode, ihe restCode eCode he, his⟩

private theorem exprStmtF_suffix (ft : FnTable) {pc Γ} {e : Expr Op} {is Γ'}
    (h : compileStmtF ft pc Γ (.exprStmt e) = some (is, Γ')) : Γ' = Γ := by
  cases e with
  | call f args =>
      rw [compileStmtF] at h
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨c, m⟩, _, hb⟩ := h
      split at hb
      · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hb
        exact hb.2.symm
      · exact absurd hb (by simp)
  | lit l =>
      simp only [compileStmtF, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, _, _, hΓ⟩ := h; exact hΓ.symm
  | var x =>
      simp only [compileStmtF, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, _, _, hΓ⟩ := h; exact hΓ.symm
  | builtin op args =>
      simp only [compileStmtF, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, _, _, hΓ⟩ := h; exact hΓ.symm

private theorem letValF_suffix (ft : FnTable) {pc Γ} {x} {e : Expr Op} {is Γ'}
    (h : compileStmtF ft pc Γ (.letDecl [x] (some e)) = some (is, Γ')) : Γ' = x :: Γ := by
  cases e with
  | call f args =>
      rw [compileStmtF] at h
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨c, m⟩, _, hb⟩ := h
      split at hb
      · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hb
        exact hb.2.symm
      · exact absurd hb (by simp)
  | lit l =>
      simp only [compileStmtF, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, _, _, hΓ⟩ := h; exact hΓ.symm
  | var z =>
      simp only [compileStmtF, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, _, _, hΓ⟩ := h; exact hΓ.symm
  | builtin op args =>
      simp only [compileStmtF, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, _, _, hΓ⟩ := h; exact hΓ.symm

private theorem letDeclF_suffix (ft : FnTable) {pc Γ} {xs} {e : Expr Op} {is Γ'}
    (h : compileStmtF ft pc Γ (.letDecl xs (some e)) = some (is, Γ')) : ∃ Δ, Γ' = Δ ++ Γ := by
  match xs, e with
  | xs', .call f args =>
      rw [compileStmtF] at h
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨c, m⟩, _, hb⟩ := h
      split at hb
      · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hb
        exact ⟨xs', hb.2.symm⟩
      · exact absurd hb (by simp)
  | [x], .lit l => exact ⟨[x], letValF_suffix ft h⟩
  | [x], .var z => exact ⟨[x], letValF_suffix ft h⟩
  | [x], .builtin op args => exact ⟨[x], letValF_suffix ft h⟩
  | [], .lit l => simp [compileStmtF] at h
  | [], .var z => simp [compileStmtF] at h
  | [], .builtin op args => simp [compileStmtF] at h
  | x :: y :: t, .lit l => simp [compileStmtF] at h
  | x :: y :: t, .var z => simp [compileStmtF] at h
  | x :: y :: t, .builtin op args => simp [compileStmtF] at h

/-- Every statement the function-aware compiler accepts only *extends* the
layout (`Γ' = Δ ++ Γ`); a block therefore restores its outer layout by dropping
exactly `Δ`. -/
theorem compileStmtF_suffix (ft : FnTable) {pc : Nat} {Γ : List Ident} {s : Stmt Op}
    {is : List Instr} {Γ' : List Ident}
    (h : compileStmtF ft pc Γ s = some (is, Γ')) : ∃ Δ, Γ' = Δ ++ Γ := by
  cases s with
  | funDef n ps rs b =>
      rw [compileStmtF] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨[], by simp [h.2]⟩
  | exprStmt e => exact ⟨[], by simp [exprStmtF_suffix ft h]⟩
  | letDecl xs val =>
      cases val with
      | none =>
          rw [compileStmtF] at h
          simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
          exact ⟨xs, h.2.symm⟩
      | some e => exact letDeclF_suffix ft h
  | assign xs e =>
      cases xs with
      | nil => simp [compileStmtF] at h
      | cons x t => cases t with
        | nil =>
            rw [compileStmtF] at h
            simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
            obtain ⟨_, _, idx, _, hb⟩ := h
            split at hb
            · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hb
              exact ⟨[], by simp [hb.2]⟩
            · exact absurd hb (by simp)
        | cons y t => simp [compileStmtF] at h
  | block body =>
      rw [compileStmtF] at h
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, _, _, h2⟩ := h; exact ⟨[], by simp [h2]⟩
  | cond c body =>
      rw [compileStmtF] at h
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, _, _, _, h2⟩ := h; exact ⟨[], by simp [h2]⟩
  | switch c cases dflt => simp [compileStmtF] at h
  | forLoop init c post body => simp [compileStmtF] at h
  | «break» => simp [compileStmtF] at h
  | «continue» => simp [compileStmtF] at h
  | leave => simp [compileStmtF] at h

/-- Sequence version of `compileStmtF_suffix`. -/
theorem compileStmtsF_suffix (ft : FnTable) {ss : List (Stmt Op)} :
    ∀ {pc Γ is Γ'}, compileStmtsF ft pc Γ ss = some (is, Γ') → ∃ Δ, Γ' = Δ ++ Γ := by
  induction ss with
  | nil =>
    intro pc Γ is Γ' h
    rw [compileStmtsF] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨[], h.2.symm⟩
  | cons st rest ih =>
    intro pc Γ is Γ' h
    rw [compileStmtsF] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨is1, Γ1⟩, hs, ⟨is2, Γ2⟩, hr, _, rfl⟩ := h
    obtain ⟨Δ1, rfl⟩ := compileStmtF_suffix ft hs
    obtain ⟨Δ2, rfl⟩ := ih hr
    exact ⟨Δ2 ++ Δ1, by simp⟩

end YulEvmCompiler
