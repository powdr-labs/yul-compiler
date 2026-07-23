import YulEvmCompiler.Optimizer.Implementation.Normalization.HoistFunDefs
import YulEvmCompiler.Optimizer.Spec.Pass

/-!
# Semantic equivalence of function hoisting  (WORK IN PROGRESS — contains `sorry`)

Goal: `UniqueFunNames b → WellScoped b → EquivBlock D b (liftFunDefs b)`.

Yul functions capture no variables (a callee runs with a fresh `VEnv`), only the
*function environment* (`cenv`, the scopes visible at the definition site). So
hoisting is sound exactly when name resolution is preserved:

* **unique names** ⇒ the flattening is unambiguous and needs no renaming (a name
  resolves to the one function with that name, wherever it sits);
* **well-scoped** ⇒ every call the *lifted* program can make (all functions are
  now globally visible) was already resolvable in the original, so the original
  is not stuck where the lifted program runs — the direction that would
  otherwise fail (`{ { function g(){} }  g() }` is stuck originally but runs
  after hoisting).

## Proof architecture (being built)

The lifted top block hoists `flat := hoist (collectStmts b)` — the whole
program's functions, each with a `stripStmts`-ed body — while every stripped
nested block hoists `[]`. The heart is a bidirectional `Step` simulation
(`step_lift_sim`) transporting a derivation across a relation `FEnvLift flat`
that couples the original scope *stack* to the *flat* scope, while the code is
simultaneously `stripStmts`-ed. This differs from `FunCongr`/`EmptyScope`
(same code, related envs): here code and environment transform together, and the
`callOk` case re-establishes `FEnvLift` between the callee's original `cenv` and
`flat`.
-/

namespace YulEvmCompiler.Optimizer.Normalization

open YulSemantics

variable {D : Dialect} [DecidableEq D.Value]

/-! ### Well-scopedness -/

/-- Top-level function names of a block (what `hoist` brings into scope). -/
def funNamesTop (b : List (Stmt D.Op)) : List Ident :=
  b.filterMap (fun s => match s with | .funDef n _ _ _ => some n | _ => none)

mutual
/-- Every user-call name in an expression is in `scope`. -/
def ScopedExpr (scope : List Ident) : Expr D.Op → Prop
  | .lit _ => True
  | .var _ => True
  | .builtin _ args => ScopedArgs scope args
  | .call f args => f ∈ scope ∧ ScopedArgs scope args
def ScopedArgs (scope : List Ident) : List (Expr D.Op) → Prop
  | [] => True
  | e :: rest => ScopedExpr scope e ∧ ScopedArgs scope rest
end

mutual
/-- Every call in a statement resolves in the accumulated function scope. A block
extends the scope with its own top-level function names (mirroring `hoist`). -/
def ScopedStmt (scope : List Ident) : Stmt D.Op → Prop
  | .funDef _ _ _ body => ScopedStmts (funNamesTop body ++ scope) body
  | .block b => ScopedStmts (funNamesTop b ++ scope) b
  | .cond c b => ScopedExpr scope c ∧ ScopedStmts (funNamesTop b ++ scope) b
  | .switch c cases dflt =>
      ScopedExpr scope c ∧ ScopedCases scope cases ∧ ScopedDflt scope dflt
  | .forLoop init c post body =>
      -- init's functions are visible in cond/post/body (they share the loop scope)
      ScopedStmts (funNamesTop init ++ scope) init ∧
      ScopedExpr (funNamesTop init ++ scope) c ∧
      ScopedStmts (funNamesTop init ++ scope) post ∧
      ScopedStmts (funNamesTop init ++ scope) body
  | .letDecl _ val => match val with | none => True | some e => ScopedExpr scope e
  | .assign _ e => ScopedExpr scope e
  | .exprStmt e => ScopedExpr scope e
  | .break => True
  | .continue => True
  | .leave => True
def ScopedStmts (scope : List Ident) : List (Stmt D.Op) → Prop
  | [] => True
  | s :: rest => ScopedStmt scope s ∧ ScopedStmts scope rest
def ScopedCases (scope : List Ident) : List (Literal × Block D.Op) → Prop
  | [] => True
  | (_, b) :: rest => ScopedStmts (funNamesTop b ++ scope) b ∧ ScopedCases scope rest
def ScopedDflt (scope : List Ident) : Option (Block D.Op) → Prop
  | none => True
  | some b => ScopedStmts (funNamesTop b ++ scope) b
end

/-- The program is well scoped: every call resolves under the scope that starts
with the top block's own functions. -/
def WellScoped (b : Block D.Op) : Prop := ScopedStmts (funNamesTop b) b

/-! ### Structural facts about `strip`/`collect`/`hoist` -/

/-- The flat top scope the lifted program hoists: every function of `b`, each
with a `stripStmts`-ed body. -/
def flat (b : Block D.Op) : FScope D := hoist D (collectStmts b)

omit [DecidableEq D.Value] in
theorem hoist_append (a c : List (Stmt D.Op)) :
    hoist D (a ++ c) = hoist D a ++ hoist D c := by
  simp only [hoist, List.filterMap_append]

omit [DecidableEq D.Value] in
/-- Stripping removes every top-level `funDef`, so the stripped block hoists
nothing. -/
theorem hoist_stripStmts (b : List (Stmt D.Op)) : hoist D (stripStmts b) = [] := by
  induction b with
  | nil => rfl
  | cons s rest ih =>
      cases s with
      | funDef n ps rs body => rw [stripStmts]; exact ih
      | block bb => simp only [stripStmts, stripStmt, hoist, List.filterMap_cons]; exact ih
      | cond c bb => simp only [stripStmts, stripStmt, hoist, List.filterMap_cons]; exact ih
      | switch c cs d => simp only [stripStmts, stripStmt, hoist, List.filterMap_cons]; exact ih
      | forLoop i c p bb => simp only [stripStmts, stripStmt, hoist, List.filterMap_cons]; exact ih
      | letDecl vs v => simp only [stripStmts, stripStmt, hoist, List.filterMap_cons]; exact ih
      | assign vs e => simp only [stripStmts, stripStmt, hoist, List.filterMap_cons]; exact ih
      | exprStmt e => simp only [stripStmts, stripStmt, hoist, List.filterMap_cons]; exact ih
      | «break» => simp only [stripStmts, stripStmt, hoist, List.filterMap_cons]; exact ih
      | «continue» => simp only [stripStmts, stripStmt, hoist, List.filterMap_cons]; exact ih
      | leave => simp only [stripStmts, stripStmt, hoist, List.filterMap_cons]; exact ih

omit [DecidableEq D.Value] in
/-- The lifted top block hoists exactly the flat scope. -/
theorem hoist_liftFunDefs (b : Block D.Op) : hoist D (liftFunDefs b) = flat b := by
  rw [liftFunDefs, hoist_append, hoist_stripStmts, List.append_nil, flat]

/-- Every statement `collectStmts` emits is a function definition. -/
def IsFunDef : Stmt D.Op → Prop
  | .funDef _ _ _ _ => True
  | _ => False

/-- Running a prefix of function definitions is a no-op (each `funDef`
statement steps to `.normal` with the environment and state unchanged). -/
theorem funDefs_noop {funs : FunEnv D} {fds rest : List (Stmt D.Op)}
    (hall : ∀ s ∈ fds, IsFunDef (D := D) s) {V st V2 st2 o} :
    Step D funs V st (.stmts (fds ++ rest)) (.sres V2 st2 o) ↔
      Step D funs V st (.stmts rest) (.sres V2 st2 o) := by
  induction fds with
  | nil => simp
  | cons s fds' ih =>
      obtain ⟨n, ps, rs, body, rfl⟩ : ∃ n ps rs body, s = .funDef n ps rs body := by
        have hmem := hall s (by simp)
        cases s with
        | funDef n ps rs body => exact ⟨n, ps, rs, body, rfl⟩
        | _ => exact absurd hmem (by simp [IsFunDef])
      have hall' : ∀ s ∈ fds', IsFunDef (D := D) s :=
        fun s hs => hall s (List.mem_cons_of_mem _ hs)
      constructor
      · intro h
        rw [List.cons_append] at h
        cases h with
        | seqCons hs htail => cases hs; exact (ih hall').mp htail
        | seqStop hs hne => cases hs; exact absurd rfl hne
      · intro h
        rw [List.cons_append]
        exact Step.seqCons Step.funDef ((ih hall').mpr h)

/- `collectStmts` (and friends) yield only function definitions. -/
mutual
theorem collectStmt_allFunDef : ∀ (s : Stmt D.Op), ∀ x ∈ collectStmt s, IsFunDef (D := D) x
  | .funDef n ps rs body => by
      intro x hx; simp only [collectStmt, List.mem_cons] at hx
      rcases hx with rfl | hx
      · simp [IsFunDef]
      · exact collectStmts_allFunDef body x hx
  | .block b => by
      intro x hx; simp only [collectStmt] at hx; exact collectStmts_allFunDef b x hx
  | .cond c b => by
      intro x hx; simp only [collectStmt] at hx; exact collectStmts_allFunDef b x hx
  | .switch c cs d => by
      intro x hx; simp only [collectStmt, List.mem_append] at hx
      rcases hx with hx | hx
      · exact collectCases_allFunDef cs x hx
      · exact collectDflt_allFunDef d x hx
  | .forLoop i c p bd => by
      intro x hx; simp only [collectStmt, List.mem_append] at hx
      rcases hx with (hx | hx) | hx
      · exact collectStmts_allFunDef i x hx
      · exact collectStmts_allFunDef p x hx
      · exact collectStmts_allFunDef bd x hx
  | .letDecl _ _ => by intro x hx; simp [collectStmt] at hx
  | .assign _ _ => by intro x hx; simp [collectStmt] at hx
  | .exprStmt _ => by intro x hx; simp [collectStmt] at hx
  | .break => by intro x hx; simp [collectStmt] at hx
  | .continue => by intro x hx; simp [collectStmt] at hx
  | .leave => by intro x hx; simp [collectStmt] at hx
theorem collectStmts_allFunDef :
    ∀ (b : List (Stmt D.Op)), ∀ x ∈ collectStmts b, IsFunDef (D := D) x
  | [] => by intro x hx; simp [collectStmts] at hx
  | s :: rest => by
      intro x hx; simp only [collectStmts, List.mem_append] at hx
      rcases hx with hx | hx
      · exact collectStmt_allFunDef s x hx
      · exact collectStmts_allFunDef rest x hx
theorem collectCases_allFunDef :
    ∀ (cs : List (Literal × Block D.Op)), ∀ x ∈ collectCases cs, IsFunDef (D := D) x
  | [] => by intro x hx; simp [collectCases] at hx
  | (_, b) :: rest => by
      intro x hx; simp only [collectCases, List.mem_append] at hx
      rcases hx with hx | hx
      · exact collectStmts_allFunDef b x hx
      · exact collectCases_allFunDef rest x hx
theorem collectDflt_allFunDef :
    ∀ (d : Option (Block D.Op)), ∀ x ∈ collectDflt d, IsFunDef (D := D) x
  | none => by intro x hx; simp [collectDflt] at hx
  | some b => by intro x hx; simp only [collectDflt] at hx; exact collectStmts_allFunDef b x hx
end

/-! ### The core simulation (under construction) -/

/-- **Core bidirectional simulation.** Running the original statements under the
lexical scope stack is equivalent to running the stripped statements under the
flat scope, provided the environments are `FEnvLift`-related and the code is well
scoped. This is the heart of the proof; `FEnvLift` and this lemma are being
built. -/
theorem inner_sim {flatSc : FScope D} {funs_o funs_h : FunEnv D}
    {b : List (Stmt D.Op)} {V st res}
    (hsim : True) :  -- placeholder for FEnvLift flatSc funs_o funs_h ∧ scoping
    Step D funs_o V st (.stmts b) res ↔
      Step D funs_h V st (.stmts (stripStmts b)) res := by
  sorry

/-! ### The equivalence -/

/-- **Hoisting all function definitions to the top preserves semantics**, for
programs with globally unique function names that are well scoped. -/
theorem liftFunDefs_equiv {b : Block D.Op}
    (huniq : UniqueFunNames b) (hscoped : WellScoped b) :
    EquivBlock D b (liftFunDefs b) := by
  intro funs V st V' st' o
  constructor
  · intro h
    cases h with
    | @block _ _ _ _ Vb stb _ hb =>
        refine Step.block ?_
        rw [hoist_liftFunDefs]
        simp only [liftFunDefs]
        rw [funDefs_noop (collectStmts_allFunDef b)]
        exact (inner_sim (flatSc := flat b) (b := b) trivial).mp hb
  · intro h
    cases h with
    | @block _ _ _ _ Vb stb _ hb =>
        refine Step.block ?_
        rw [hoist_liftFunDefs] at hb
        simp only [liftFunDefs] at hb
        rw [funDefs_noop (collectStmts_allFunDef b)] at hb
        exact (inner_sim (flatSc := flat b) (b := b) trivial).mpr hb

end YulEvmCompiler.Optimizer.Normalization
