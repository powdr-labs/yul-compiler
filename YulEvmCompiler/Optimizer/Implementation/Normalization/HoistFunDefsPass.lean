import YulEvmCompiler.Optimizer.Implementation.Normalization.HoistFunDefsEquiv
import YulEvmCompiler.Optimizer.Spec.GlobalPass

/-!
# Function hoisting as a verified `GlobalPass`

Wraps the proven whole-program hoisting transform `liftFunDefs` (see
`Normalization/HoistFunDefsEquiv.lean`, theorem `liftFunDefs_run_equiv`) as a sound
`Optimizer.GlobalPass`.

`liftFunDefs` is semantics-preserving only when the program's function names are
**globally unique** (disambiguated) *and* it is **well scoped** — under those
assumptions hoisting every function to the top block changes no name resolution.
A `GlobalPass` must be *unconditionally* sound, so the pass **guards**: it applies
`liftFunDefs` exactly on inputs it can decide are unique-and-well-scoped, and is
the identity otherwise. Soundness is therefore total; on disambiguated,
well-scoped input the pass really does hoist. The guard is decided by the `Bool`
mirror of the `Scoped*` predicates (`wellScopedB`, sound by `wellScopedB_sound`)
together with the decidable `UniqueFunNames` (`Nodup`).
-/

namespace YulEvmCompiler.Optimizer.Normalization

open YulSemantics

variable {D : Dialect} [DecidableEq D.Value]

/-! ### A decidable mirror of well-scopedness -/

mutual
def scopedExprB (scope : List Ident) : Expr D.Op → Bool
  | .lit _ => true
  | .var _ => true
  | .builtin _ args => scopedArgsB scope args
  | .call f args => decide (f ∈ scope) && scopedArgsB scope args
def scopedArgsB (scope : List Ident) : List (Expr D.Op) → Bool
  | [] => true
  | e :: rest => scopedExprB scope e && scopedArgsB scope rest
end

mutual
def scopedStmtB (scope : List Ident) : Stmt D.Op → Bool
  | .funDef _ _ _ body => scopedStmtsB (funNamesTop body ++ scope) body
  | .block b => scopedStmtsB (funNamesTop b ++ scope) b
  | .cond c b => scopedExprB scope c && scopedStmtsB (funNamesTop b ++ scope) b
  | .switch c cases dflt =>
      scopedExprB scope c && scopedCasesB scope cases && scopedDfltB scope dflt
  | .forLoop init c post body =>
      scopedStmtsB (funNamesTop init ++ scope) init &&
      scopedExprB (funNamesTop init ++ scope) c &&
      scopedStmtsB (funNamesTop post ++ (funNamesTop init ++ scope)) post &&
      scopedStmtsB (funNamesTop body ++ (funNamesTop init ++ scope)) body
  | .letDecl _ val => match val with | none => true | some e => scopedExprB scope e
  | .assign _ e => scopedExprB scope e
  | .exprStmt e => scopedExprB scope e
  | .break => true
  | .continue => true
  | .leave => true
def scopedStmtsB (scope : List Ident) : List (Stmt D.Op) → Bool
  | [] => true
  | s :: rest => scopedStmtB scope s && scopedStmtsB scope rest
def scopedCasesB (scope : List Ident) : List (Literal × Block D.Op) → Bool
  | [] => true
  | (_, b) :: rest => scopedStmtsB (funNamesTop b ++ scope) b && scopedCasesB scope rest
def scopedDfltB (scope : List Ident) : Option (Block D.Op) → Bool
  | none => true
  | some b => scopedStmtsB (funNamesTop b ++ scope) b
end

/-- Decidable well-scopedness check. -/
def wellScopedB (b : Block D.Op) : Bool := scopedStmtsB (funNamesTop b) b

/-! ### Soundness of the mirror (`= true → Prop`) -/

mutual
theorem scopedExprB_sound : ∀ {scope : List Ident} (e : Expr D.Op),
    scopedExprB scope e = true → ScopedExpr scope e
  | _, .lit _, _ => by simp only [ScopedExpr]
  | _, .var _, _ => by simp only [ScopedExpr]
  | _, .builtin _ args, h => by
      simp only [scopedExprB] at h; simp only [ScopedExpr]; exact scopedArgsB_sound args h
  | _, .call _ args, h => by
      simp only [scopedExprB, Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [ScopedExpr]; exact ⟨h.1, scopedArgsB_sound args h.2⟩
theorem scopedArgsB_sound : ∀ {scope : List Ident} (es : List (Expr D.Op)),
    scopedArgsB scope es = true → ScopedArgs scope es
  | _, [], _ => by simp only [ScopedArgs]
  | _, e :: rest, h => by
      simp only [scopedArgsB, Bool.and_eq_true] at h
      simp only [ScopedArgs]; exact ⟨scopedExprB_sound e h.1, scopedArgsB_sound rest h.2⟩
end

mutual
theorem scopedStmtB_sound : ∀ {scope : List Ident} (s : Stmt D.Op),
    scopedStmtB scope s = true → ScopedStmt scope s
  | _, .funDef _ _ _ body, h => by
      simp only [scopedStmtB] at h; simp only [ScopedStmt]; exact scopedStmtsB_sound body h
  | _, .block b, h => by
      simp only [scopedStmtB] at h; simp only [ScopedStmt]; exact scopedStmtsB_sound b h
  | _, .cond c b, h => by
      simp only [scopedStmtB, Bool.and_eq_true] at h
      simp only [ScopedStmt]; exact ⟨scopedExprB_sound c h.1, scopedStmtsB_sound b h.2⟩
  | _, .switch c cases dflt, h => by
      simp only [scopedStmtB, Bool.and_eq_true] at h
      simp only [ScopedStmt]
      exact ⟨scopedExprB_sound c h.1.1, scopedCasesB_sound cases h.1.2, scopedDfltB_sound dflt h.2⟩
  | _, .forLoop init c post body, h => by
      simp only [scopedStmtB, Bool.and_eq_true] at h
      simp only [ScopedStmt]
      exact ⟨scopedStmtsB_sound init h.1.1.1, scopedExprB_sound c h.1.1.2,
        scopedStmtsB_sound post h.1.2, scopedStmtsB_sound body h.2⟩
  | _, .letDecl _ val, h => by
      cases val with
      | none => simp only [ScopedStmt]
      | some e => simp only [scopedStmtB] at h; simp only [ScopedStmt]; exact scopedExprB_sound e h
  | _, .assign _ e, h => by
      simp only [scopedStmtB] at h; simp only [ScopedStmt]; exact scopedExprB_sound e h
  | _, .exprStmt e, h => by
      simp only [scopedStmtB] at h; simp only [ScopedStmt]; exact scopedExprB_sound e h
  | _, .break, _ => by simp only [ScopedStmt]
  | _, .continue, _ => by simp only [ScopedStmt]
  | _, .leave, _ => by simp only [ScopedStmt]
theorem scopedStmtsB_sound : ∀ {scope : List Ident} (ss : List (Stmt D.Op)),
    scopedStmtsB scope ss = true → ScopedStmts scope ss
  | _, [], _ => by simp only [ScopedStmts]
  | _, s :: rest, h => by
      simp only [scopedStmtsB, Bool.and_eq_true] at h
      simp only [ScopedStmts]; exact ⟨scopedStmtB_sound s h.1, scopedStmtsB_sound rest h.2⟩
theorem scopedCasesB_sound : ∀ {scope : List Ident} (cs : List (Literal × Block D.Op)),
    scopedCasesB scope cs = true → ScopedCases scope cs
  | _, [], _ => by simp only [ScopedCases]
  | _, (_, b) :: rest, h => by
      simp only [scopedCasesB, Bool.and_eq_true] at h
      simp only [ScopedCases]; exact ⟨scopedStmtsB_sound b h.1, scopedCasesB_sound rest h.2⟩
theorem scopedDfltB_sound : ∀ {scope : List Ident} (d : Option (Block D.Op)),
    scopedDfltB scope d = true → ScopedDflt scope d
  | _, none, _ => by simp only [ScopedDflt]
  | _, some b, h => by simp only [scopedDfltB] at h; simp only [ScopedDflt]; exact scopedStmtsB_sound b h
end

theorem wellScopedB_sound {b : Block D.Op} (h : wellScopedB b = true) : WellScoped b :=
  scopedStmtsB_sound b h

/-! ### The guard and the pass -/

instance {b : Block D.Op} : Decidable (UniqueFunNames b) := by
  unfold UniqueFunNames; infer_instance

/-- Decidable guard implying the hypotheses of `liftFunDefs_run_equiv`. -/
def hoistGuard (b : Block D.Op) : Bool := decide (UniqueFunNames b) && wellScopedB b

theorem hoistGuard_sound {b : Block D.Op} (h : hoistGuard b = true) :
    UniqueFunNames b ∧ WellScoped b := by
  rw [hoistGuard, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, wellScopedB_sound h.2⟩

/-- Hoist all function definitions to the top **when** the block is unique and
well scoped; otherwise leave it unchanged. -/
def hoistBlock (b : Block D.Op) : Block D.Op :=
  if hoistGuard b = true then liftFunDefs b else b

/-- Hoisting a code block preserves its whole-program behaviour, unconditionally
(the guard makes the transform behavioural-identity where it cannot prove the
hoist sound). -/
theorem hoistBlock_runEquiv (b : Block D.Op) : RunEquivBlock D b (hoistBlock b) := by
  unfold hoistBlock
  by_cases hg : hoistGuard b = true
  · rw [if_pos hg]
    obtain ⟨hu, hs⟩ := hoistGuard_sound hg
    exact fun _ _ _ _ => liftFunDefs_run_equiv hu hs
  · rw [if_neg hg]; exact RunEquivBlock.refl b

/-- **Function hoisting as a verified global pass.** Applies `liftFunDefs` to
every code block of an object tree wherever the block is disambiguated and well
scoped; sound unconditionally. -/
def hoistFunDefsPass : GlobalPass D where
  run := mapObjCode hoistBlock
  sound := objEquiv_mapObjCode hoistBlock_runEquiv

@[simp] theorem hoistFunDefsPass_run (o : Object D.Op) :
    (hoistFunDefsPass (D := D)).run o = mapObjCode hoistBlock o := rfl

end YulEvmCompiler.Optimizer.Normalization
