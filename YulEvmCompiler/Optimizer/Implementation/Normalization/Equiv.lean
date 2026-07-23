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

omit [DecidableEq D.Value] in
theorem hoist_map_fst (b : List (Stmt D.Op)) :
    (hoist D b).map (·.1) = funNamesTop b := by
  simp only [hoist, funNamesTop, List.map_filterMap]
  congr 1
  funext s
  cases s <;> rfl

omit [DecidableEq D.Value] in
theorem funNamesTop_append (a c : List (Stmt D.Op)) :
    funNamesTop (a ++ c) = funNamesTop a ++ funNamesTop c := by
  simp only [funNamesTop, List.filterMap_append]

omit [DecidableEq D.Value] in
theorem funNamesTop_cons_funDef (n ps rs bd) (rest : List (Stmt D.Op)) :
    funNamesTop (D := D) (.funDef n ps rs bd :: rest) = n :: funNamesTop rest := by
  simp only [funNamesTop, List.filterMap_cons]

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


/-! ### The core simulation (Run-equivalence; base = []) -/

/-- A function declaration with its body stripped of nested definitions. -/
def stripDecl (d : FDecl D) : FDecl D := { d with body := stripStmts d.body }

/-- All function names bound anywhere in an environment (scope stack). -/
def funNamesEnv (funs : FunEnv D) : List Ident :=
  (funs.map (fun s => s.map (·.1))).flatten

/-- Resolve a name in the single flat scope. -/
def flatLookup (flatSc : FScope D) (f : Ident) : Option (FDecl D) :=
  (lookupFun [flatSc] f).map (·.1)

/-- Every function collected out of `code` is registered in the flat scope with
its (already-stripped) body. -/
def CodeInFlat (flatSc : FScope D) (code : List (Stmt D.Op)) : Prop :=
  ∀ n ps rs bd, (Stmt.funDef n ps rs bd) ∈ collectStmts code →
    flatLookup flatSc n = some { params := ps, rets := rs, body := bd }

/-- The original environment is a valid program scope stack for `flatSc`: every
function it resolves matches the flat scope (stripped), has a well-scoped body,
and a body whose own functions are registered in the flat scope. No ambient base
(this is the whole-program `Run` setting). -/
def GoodO (flatSc : FScope D) (funs : FunEnv D) : Prop :=
  ∀ f d cenv, lookupFun funs f = some (d, cenv) →
    flatLookup flatSc f = some (stripDecl d) ∧
    ScopedStmts (funNamesTop d.body ++ funNamesEnv cenv) d.body ∧
    CodeInFlat flatSc d.body

/-- The lifted environment resolves every name exactly as the single flat scope
does (nested stripped blocks only add empty scopes, transparent to lookup). -/
def ResEq (flatSc : FScope D) (funs_h : FunEnv D) : Prop :=
  ∀ f, lookupFun funs_h f = lookupFun [flatSc] f

/-- `stripStmt` on the `Code` wrapper. -/
def stripCode : Code D.Op → Code D.Op
  | .expr e => .expr e
  | .args es => .args es
  | .stmt s => .stmt (stripStmt s)
  | .stmts ss => .stmts (stripStmts ss)
  | .loop c post body => .loop c (stripStmts post) (stripStmts body)

/-- Well-scopedness lifted to the `Code` wrapper. -/
def ScopedCode (Γ : List Ident) : Code D.Op → Prop
  | .expr e => ScopedExpr Γ e
  | .args es => ScopedArgs Γ es
  | .stmt s => ScopedStmt Γ s
  | .stmts ss => ScopedStmts Γ ss
  | .loop c post body => ScopedExpr Γ c ∧ ScopedStmts Γ post ∧ ScopedStmts Γ body

/-- `CodeInFlat` lifted to the `Code` wrapper. -/
def CodeInFlatCode (flatSc : FScope D) : Code D.Op → Prop
  | .expr _ => True
  | .args _ => True
  | .stmt s => CodeInFlat flatSc [s]
  | .stmts ss => CodeInFlat flatSc ss
  | .loop _ post body => CodeInFlat flatSc post ∧ CodeInFlat flatSc body

omit [DecidableEq D.Value] in
theorem funNamesEnv_cons (s : FScope D) (rest : FunEnv D) :
    funNamesEnv (s :: rest) = s.map (·.1) ++ funNamesEnv rest := by
  simp only [funNamesEnv, List.map_cons, List.flatten_cons]

omit [DecidableEq D.Value] in
theorem mem_funNamesEnv_of_lookup {funs : FunEnv D} {f d c}
    (h : lookupFun funs f = some (d, c)) : f ∈ funNamesEnv funs := by
  induction funs with
  | nil => simp [lookupFun] at h
  | cons s rest ih =>
      rw [funNamesEnv_cons, List.mem_append]
      unfold lookupFun at h
      cases hfind : s.find? (fun p => p.1 = f) with
      | some p =>
          left
          have := List.find?_some (by rw [hfind])
          have hp := List.mem_of_find?_eq_some hfind
          exact (List.mem_map).mpr ⟨p, hp, by simpa using this⟩
      | none => rw [hfind] at h; exact Or.inr (ih h)

omit [DecidableEq D.Value] in
/-- Under unique names, resolving in the closure environment returned by a lookup
agrees with resolving in the whole environment. -/
theorem lookupFun_cenv_resolve : ∀ (funs : FunEnv D) {f d cenv f' d' cenv'},
    (funNamesEnv funs).Nodup → lookupFun funs f = some (d, cenv) →
    lookupFun cenv f' = some (d', cenv') → lookupFun funs f' = some (d', cenv')
  | [], _, _, _, _, _, _, _, h, _ => by simp [lookupFun] at h
  | s :: rest, f, d, cenv, f', d', cenv', hnd, hlk, hlk' => by
      rw [funNamesEnv_cons] at hnd
      have hnd_rest : (funNamesEnv rest).Nodup := (List.nodup_append.mp hnd).2.1
      have hdisj := (List.nodup_append.mp hnd).2.2
      unfold lookupFun at hlk ⊢
      cases hfind : s.find? (fun p => p.1 = f) with
      | some p =>
          rw [hfind] at hlk; simp only [Option.some.injEq, Prod.mk.injEq] at hlk
          obtain ⟨_, rfl⟩ := hlk
          unfold lookupFun at hlk'
          exact hlk'
      | none =>
          rw [hfind] at hlk
          have ihres := lookupFun_cenv_resolve rest hnd_rest hlk hlk'
          have hmem' : f' ∈ funNamesEnv rest := mem_funNamesEnv_of_lookup ihres
          cases hfind' : s.find? (fun p => p.1 = f') with
          | some p' =>
              exfalso
              have hp' := List.mem_of_find?_eq_some hfind'
              have hkey : p'.1 = f' := by simpa using List.find?_some hfind'
              exact hdisj f' (List.mem_map.mpr ⟨p', hp', hkey⟩) f' hmem' rfl
          | none => exact ihres

omit [DecidableEq D.Value] in
/-- `GoodO` is inherited by any closure environment a lookup returns. -/
theorem goodO_cenv {flatSc : FScope D} {funs : FunEnv D}
    (hnd : (funNamesEnv funs).Nodup) (hg : GoodO flatSc funs)
    {f d cenv} (hlk : lookupFun funs f = some (d, cenv)) : GoodO flatSc cenv :=
  fun f' d' cenv' hlk' => hg f' d' cenv' (lookupFun_cenv_resolve funs hnd hlk hlk')

/-- **Core bidirectional simulation.** Running the original code under its
lexical scope stack equals running the stripped code under the flat scope. The
invariants (unique names in the env, `GoodO`, `ResEq`, well-scopedness,
functions-in-flat) are preserved and re-established by the `block`/`callOk`
cases. Proof under construction. -/
theorem step_lift_sim {flatSc : FScope D} {funs_o funs_h : FunEnv D} {code V st res}
    (huniq : (funNamesEnv funs_o).Nodup)
    (hO : GoodO flatSc funs_o) (hH : ResEq flatSc funs_h)
    (hws : ScopedCode (funNamesEnv funs_o) code)
    (hcf : CodeInFlatCode flatSc code) :
    Step D funs_o V st code res ↔ Step D funs_h V st (stripCode code) res := by
  sorry

omit [DecidableEq D.Value] in
theorem funNamesTop_cons_other {s : Stmt D.Op} (h : ∀ n ps rs bd, s ≠ .funDef n ps rs bd)
    (rest : List (Stmt D.Op)) : funNamesTop (s :: rest) = funNamesTop rest := by
  cases s with
  | funDef n ps rs bd => exact absurd rfl (h n ps rs bd)
  | _ => simp only [funNamesTop, List.filterMap_cons]

omit [DecidableEq D.Value] in
/-- The top-level function names are a sublist of all function names, so global
uniqueness gives top-level uniqueness. -/
theorem funNamesTop_sublist (b : List (Stmt D.Op)) :
    List.Sublist (funNamesTop b) (funNamesStmts b) := by
  induction b with
  | nil => exact List.nil_sublist _
  | cons s rest ih =>
      have hs : funNamesStmts (s :: rest) = funNamesStmt s ++ funNamesStmts rest := rfl
      rw [hs]
      cases s with
      | funDef n ps rs body =>
          rw [funNamesTop_cons_funDef]
          have hfs : funNamesStmt (.funDef n ps rs body) = n :: funNamesStmts body := rfl
          rw [hfs, List.cons_append]
          exact (ih.trans (List.sublist_append_right _ _)).cons₂ n
      | block _ => rw [funNamesTop_cons_other (by simp)]
                   exact ih.trans (List.sublist_append_right _ _)
      | cond _ _ => rw [funNamesTop_cons_other (by simp)]
                    exact ih.trans (List.sublist_append_right _ _)
      | switch _ _ _ => rw [funNamesTop_cons_other (by simp)]
                        exact ih.trans (List.sublist_append_right _ _)
      | forLoop _ _ _ _ => rw [funNamesTop_cons_other (by simp)]
                           exact ih.trans (List.sublist_append_right _ _)
      | letDecl _ _ => rw [funNamesTop_cons_other (by simp)]
                       exact ih.trans (List.sublist_append_right _ _)
      | assign _ _ => rw [funNamesTop_cons_other (by simp)]
                      exact ih.trans (List.sublist_append_right _ _)
      | exprStmt _ => rw [funNamesTop_cons_other (by simp)]
                      exact ih.trans (List.sublist_append_right _ _)
      | «break» => rw [funNamesTop_cons_other (by simp)]
                   exact ih.trans (List.sublist_append_right _ _)
      | «continue» => rw [funNamesTop_cons_other (by simp)]
                      exact ih.trans (List.sublist_append_right _ _)
      | leave => rw [funNamesTop_cons_other (by simp)]
                 exact ih.trans (List.sublist_append_right _ _)

/-! ### Lookup infrastructure -/

omit [DecidableEq D.Value] in
/-- In a key-`Nodup` association list, a member is exactly what `find?` returns. -/
theorem find?_nodup_mem {β : Type _} {l : List (Ident × β)}
    (hnd : (l.map (·.1)).Nodup) {a : Ident} {v : β} (hmem : (a, v) ∈ l) :
    l.find? (fun p => p.1 = a) = some (a, v) := by
  induction l with
  | nil => simp at hmem
  | cons p rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnd
      rcases List.mem_cons.mp hmem with h | h
      · subst h; simp [List.find?_cons_of_pos]
      · have hne : p.1 ≠ a := by
          intro heq; exact hnd.1 (heq ▸ (List.mem_map.mpr ⟨(a, v), h, rfl⟩))
        rw [List.find?_cons_of_neg (by simp [hne])]
        exact ih hnd.2 h

/- Names collected by `collectStmts` are exactly the program's function names. -/
mutual
theorem funNamesTop_collectStmt (s : Stmt D.Op) :
    funNamesTop (collectStmt s) = funNamesStmt s := by
  cases s with
  | funDef n ps rs body =>
      rw [collectStmt, funNamesTop_cons_funDef, funNamesTop_collectStmts body]
      simp only [funNamesStmt]
  | block b => rw [collectStmt]; simp only [funNamesStmt]; exact funNamesTop_collectStmts b
  | cond c b => rw [collectStmt]; simp only [funNamesStmt]; exact funNamesTop_collectStmts b
  | switch c cs d =>
      rw [collectStmt, funNamesTop_append, funNamesTop_collectCases cs,
        funNamesTop_collectDflt d]
      simp only [funNamesStmt]
  | forLoop i c p bd =>
      rw [collectStmt, funNamesTop_append, funNamesTop_append,
        funNamesTop_collectStmts i, funNamesTop_collectStmts p, funNamesTop_collectStmts bd]
      simp only [funNamesStmt]
  | letDecl _ _ => rfl
  | assign _ _ => rfl
  | exprStmt _ => rfl
  | «break» => rfl
  | «continue» => rfl
  | leave => rfl
theorem funNamesTop_collectStmts (b : List (Stmt D.Op)) :
    funNamesTop (collectStmts b) = funNamesStmts b := by
  cases b with
  | nil => rfl
  | cons s rest =>
      rw [collectStmts, funNamesTop_append, funNamesTop_collectStmt s,
        funNamesTop_collectStmts rest]
      simp only [funNamesStmts]
theorem funNamesTop_collectCases (cs : List (Literal × Block D.Op)) :
    funNamesTop (collectCases cs) = funNamesCases cs := by
  cases cs with
  | nil => rfl
  | cons p rest =>
      obtain ⟨l, b⟩ := p
      rw [collectCases, funNamesTop_append, funNamesTop_collectStmts b,
        funNamesTop_collectCases rest]
      simp only [funNamesCases]
theorem funNamesTop_collectDflt (d : Option (Block D.Op)) :
    funNamesTop (collectDflt d) = funNamesDflt d := by
  cases d with
  | none => rfl
  | some b => rw [collectDflt]; simp only [funNamesDflt]; exact funNamesTop_collectStmts b
end

omit [DecidableEq D.Value] in
theorem lookupFun_singleton (scope : FScope D) (n : Ident) :
    lookupFun [scope] n = (scope.find? (fun p => p.1 = n)).map (fun p => (p.2, [scope])) := by
  simp only [lookupFun]
  cases scope.find? (fun p => p.1 = n) <;> rfl

omit [DecidableEq D.Value] in
theorem mem_hoist_of_mem {L : List (Stmt D.Op)} {n ps rs bd}
    (h : (Stmt.funDef n ps rs bd) ∈ L) :
    (n, ({ params := ps, rets := rs, body := bd } : FDecl D)) ∈ hoist D L := by
  simp only [hoist, List.mem_filterMap]
  exact ⟨.funDef n ps rs bd, h, rfl⟩

/-- The key fact: under unique names, the flat scope resolves a collected
function's name to exactly its (stripped-body) declaration. -/
theorem flatLookup_of_mem {b : Block D.Op} (huniq : UniqueFunNames b)
    {n ps rs bd} (hmem : (Stmt.funDef n ps rs bd) ∈ collectStmts b) :
    flatLookup (flat b) n = some { params := ps, rets := rs, body := bd } := by
  have hkeys : ((flat b).map (·.1)) = funNamesStmts b := by
    rw [flat, hoist_map_fst, funNamesTop_collectStmts]
  have hnd : ((flat b).map (·.1)).Nodup := by rw [hkeys]; exact huniq
  have hfind := find?_nodup_mem hnd (mem_hoist_of_mem (D := D) hmem)
  simp only [flatLookup, lookupFun_singleton, hfind, Option.map_some]

/-! ### Top-level bridges (base = []) -/

omit [DecidableEq D.Value] in
theorem funNamesEnv_singleton (b : Block D.Op) :
    funNamesEnv (D := D) (hoist D b :: []) = funNamesTop b := by
  simp only [funNamesEnv, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
    List.append_nil, hoist_map_fst]

/-- At the top block, the original scope stack is `GoodO` for the flat scope. -/
theorem goodO_top {b : Block D.Op} (huniq : UniqueFunNames b) (hws : WellScoped b) :
    GoodO (D := D) (flat b) (hoist D b :: []) := by
  sorry

/-- At the top block, `b`'s functions are all registered in the flat scope. -/
theorem codeInFlat_top {b : Block D.Op} (huniq : UniqueFunNames b) :
    CodeInFlat (D := D) (flat b) b :=
  fun _ _ _ _ hmem => flatLookup_of_mem huniq hmem

/-! ### The equivalence -/

/-- **Hoisting all function definitions to the top preserves whole-program
semantics**, for programs with globally unique function names that are well
scoped. -/
theorem liftFunDefs_run_equiv {b : Block D.Op}
    (huniq : UniqueFunNames b) (hscoped : WellScoped b)
    {st0 : D.State} {V' st' o} :
    Run D b st0 V' st' o ↔ Run D (liftFunDefs b) st0 V' st' o := by
  have simIff : ∀ {r}, Step D (hoist D b :: []) [] st0 (.stmts b) r ↔
      Step D (flat b :: []) [] st0 (.stmts (stripStmts b)) r := by
    intro r
    have huniqEnv : (funNamesEnv (D := D) (hoist D b :: [])).Nodup := by
      rw [funNamesEnv_singleton]
      exact huniq.sublist (funNamesTop_sublist b)
    have hwsEnv : ScopedCode (funNamesEnv (D := D) (hoist D b :: [])) (.stmts b) := by
      rw [funNamesEnv_singleton]; exact hscoped
    exact step_lift_sim (code := .stmts b) (res := r) huniqEnv (goodO_top huniq hscoped)
      (fun _ => rfl) hwsEnv (codeInFlat_top huniq)
  constructor
  · intro h
    cases h with
    | @block _ _ _ _ Vb stb _ hb =>
        refine Step.block ?_
        rw [hoist_liftFunDefs]
        simp only [liftFunDefs]
        rw [funDefs_noop (collectStmts_allFunDef b)]
        exact simIff.mp hb
  · intro h
    cases h with
    | @block _ _ _ _ Vb stb _ hb =>
        refine Step.block ?_
        rw [hoist_liftFunDefs] at hb
        simp only [liftFunDefs] at hb
        rw [funDefs_noop (collectStmts_allFunDef b)] at hb
        exact simIff.mpr hb

end YulEvmCompiler.Optimizer.Normalization
