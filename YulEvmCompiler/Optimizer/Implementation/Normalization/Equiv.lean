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
      -- init's functions are visible in cond/post/body (they share the loop scope);
      -- post and body are each executed as a block, so hoist their own functions too.
      ScopedStmts (funNamesTop init ++ scope) init ∧
      ScopedExpr (funNamesTop init ++ scope) c ∧
      ScopedStmts (funNamesTop post ++ (funNamesTop init ++ scope)) post ∧
      ScopedStmts (funNamesTop body ++ (funNamesTop init ++ scope)) body
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
def GoodO (flatSc : FScope D) : FunEnv D → Prop
  | [] => True
  | s :: rest =>
      (∀ n d, (n, d) ∈ s →
        flatLookup flatSc n = some (stripDecl d) ∧
        ScopedStmts (funNamesTop d.body ++ funNamesEnv (s :: rest)) d.body ∧
        CodeInFlat flatSc d.body) ∧ GoodO flatSc rest

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
  | .loop c post body =>
      ScopedExpr Γ c ∧ ScopedStmts (funNamesTop post ++ Γ) post ∧
        ScopedStmts (funNamesTop body ++ Γ) body

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
theorem funNamesEnv_append (a c : FunEnv D) :
    funNamesEnv (a ++ c) = funNamesEnv a ++ funNamesEnv c := by
  simp only [funNamesEnv, List.map_append, List.flatten_append]

omit [DecidableEq D.Value] in
theorem lookupFun_cenv_suffix : ∀ (funs : FunEnv D) {f d cenv},
    lookupFun funs f = some (d, cenv) → List.IsSuffix cenv funs
  | [], _, _, _, h => by simp [lookupFun] at h
  | s :: rest, f, d, cenv, h => by
      unfold lookupFun at h
      cases hfind : s.find? (fun p => p.1 = f) with
      | some p =>
          rw [hfind] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl⟩ := h; exact List.suffix_refl _
      | none =>
          rw [hfind] at h
          exact (lookupFun_cenv_suffix rest h).trans (List.suffix_cons _ _)

omit [DecidableEq D.Value] in
theorem goodO_append_right : ∀ (a : FunEnv D) {c : FunEnv D} {flatSc},
    GoodO flatSc (a ++ c) → GoodO flatSc c
  | [], _, _, h => h
  | _ :: a', _, _, h => goodO_append_right a' h.2

omit [DecidableEq D.Value] in
/-- `GoodO` is inherited by any closure environment a lookup returns (a suffix). -/
theorem goodO_cenv {flatSc : FScope D} {funs : FunEnv D} (hg : GoodO flatSc funs)
    {f d cenv} (hlk : lookupFun funs f = some (d, cenv)) : GoodO flatSc cenv := by
  obtain ⟨pre, hpre⟩ := lookupFun_cenv_suffix funs hlk
  rw [← hpre] at hg
  exact goodO_append_right pre hg

omit [DecidableEq D.Value] in
/-- Facts about the function a lookup resolves, with the correct (positional)
body scope, read off structural `GoodO`. -/
theorem goodO_lookup : ∀ {funs : FunEnv D} {flatSc : FScope D},
    GoodO flatSc funs → ∀ {fn d cenv}, lookupFun funs fn = some (d, cenv) →
      flatLookup flatSc fn = some (stripDecl d) ∧
      ScopedStmts (funNamesTop d.body ++ funNamesEnv cenv) d.body ∧
      CodeInFlat flatSc d.body
  | [], _, _, _, _, _, h => by simp [lookupFun] at h
  | s :: rest, flatSc, hg, fn, d, cenv, hlk => by
      unfold lookupFun at hlk
      cases hfind : s.find? (fun p => p.1 = fn) with
      | some p =>
          rw [hfind] at hlk; simp only [Option.some.injEq, Prod.mk.injEq] at hlk
          obtain ⟨hd, hc⟩ := hlk
          have hpmem := List.mem_of_find?_eq_some hfind
          have hpkey : p.1 = fn := by simpa using List.find?_some hfind
          have hmem : (fn, d) ∈ s := by
            have hp : p = (fn, d) := Prod.ext hpkey hd
            rw [← hp]; exact hpmem
          rw [← hc]
          exact hg.1 fn d hmem
      | none => rw [hfind] at hlk; exact goodO_lookup hg.2 hlk

omit [DecidableEq D.Value] in
theorem collectStmt_subset_collectStmts : ∀ {ss : List (Stmt D.Op)} {s},
    s ∈ ss → ∀ x ∈ collectStmt s, x ∈ collectStmts ss
  | [], _, h, _, _ => by simp at h
  | s' :: rest, s, h, x, hx => by
      rw [collectStmts, List.mem_append]
      rcases List.mem_cons.mp h with rfl | h
      · exact Or.inl hx
      · exact Or.inr (collectStmt_subset_collectStmts h x hx)

omit [DecidableEq D.Value] in
theorem mem_collectStmts_of_top {b : List (Stmt D.Op)} {f ps rs body}
    (h : (Stmt.funDef f ps rs body) ∈ b) :
    (Stmt.funDef f ps rs (stripStmts body)) ∈ collectStmts b := by
  refine collectStmt_subset_collectStmts h _ ?_
  rw [collectStmt]; exact List.mem_cons_self

omit [DecidableEq D.Value] in
theorem collectStmts_body_subset {b : List (Stmt D.Op)} {f ps rs body}
    (h : (Stmt.funDef f ps rs body) ∈ b) {x} (hx : x ∈ collectStmts body) :
    x ∈ collectStmts b := by
  refine collectStmt_subset_collectStmts h x ?_
  rw [collectStmt]; exact List.mem_cons_of_mem _ hx

omit [DecidableEq D.Value] in
theorem scopedStmts_funDef_body : ∀ {ss : List (Stmt D.Op)} {Γ},
    ScopedStmts Γ ss → ∀ {f ps rs body}, (Stmt.funDef f ps rs body) ∈ ss →
      ScopedStmts (funNamesTop body ++ Γ) body
  | [], _, _, _, _, _, _, h => by simp at h
  | s' :: rest, Γ, hsc, f, ps, rs, body, h => by
      obtain ⟨h1, h2⟩ := hsc
      rcases List.mem_cons.mp h with rfl | h
      · exact h1
      · exact scopedStmts_funDef_body h2 h

omit [DecidableEq D.Value] in
theorem mem_hoist_inv {b : List (Stmt D.Op)} {f} {d : FDecl D} (h : (f, d) ∈ hoist D b) :
    ∃ ps rs body, d = { params := ps, rets := rs, body := body } ∧
      (Stmt.funDef f ps rs body) ∈ b := by
  simp only [hoist, List.mem_filterMap] at h
  obtain ⟨s, hs, hg⟩ := h
  cases s with
  | funDef n ps rs body =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hg
      obtain ⟨hn, hd⟩ := hg; subst hn; subst hd
      exact ⟨ps, rs, body, rfl, hs⟩
  | _ => simp at hg

omit [DecidableEq D.Value] in
/-- `ResEq flatSc [flatSc]` — the flat scope resolves like itself. -/
theorem resEq_flat (flatSc : FScope D) : ResEq flatSc [flatSc] := fun _ => rfl

omit [DecidableEq D.Value] in
theorem funNamesEnv_hoist_cons (body : List (Stmt D.Op)) (funs : FunEnv D) :
    funNamesEnv (hoist D body :: funs) = funNamesTop body ++ funNamesEnv funs := by
  rw [funNamesEnv_cons, hoist_map_fst]

omit [DecidableEq D.Value] in
/-- Prepending an empty scope to the lifted env is transparent to resolution. -/
theorem resEq_cons_nil {flatSc : FScope D} {funs_h : FunEnv D} (h : ResEq flatSc funs_h) :
    ResEq flatSc ([] :: funs_h) := by
  intro f
  show lookupFun ([] :: funs_h) f = lookupFun [flatSc] f
  unfold lookupFun
  simp only [List.find?_nil]
  exact h f

omit [DecidableEq D.Value] in
/-- Establishing `GoodO` for a pushed block scope, from the block's functions
being in the flat scope and its body well scoped (used for `block`/`forLoop`). -/
theorem goodO_push {flatSc : FScope D} {funs_o : FunEnv D} {body : List (Stmt D.Op)}
    (hO : GoodO flatSc funs_o) (hcfb : CodeInFlat flatSc body)
    (hwsb : ScopedStmts (funNamesTop body ++ funNamesEnv funs_o) body) :
    GoodO flatSc (hoist D body :: funs_o) := by
  refine ⟨?_, hO⟩
  intro n d hmem
  obtain ⟨ps, rs, bdy, hdeq, hfd⟩ := mem_hoist_inv hmem
  refine ⟨?_, ?_, ?_⟩
  · rw [hdeq]
    have hst : stripDecl (D := D) { params := ps, rets := rs, body := bdy }
        = { params := ps, rets := rs, body := stripStmts bdy } := rfl
    rw [hst]
    exact hcfb n ps rs (stripStmts bdy) (mem_collectStmts_of_top hfd)
  · rw [hdeq, funNamesEnv_hoist_cons]
    exact scopedStmts_funDef_body hwsb hfd
  · rw [hdeq]
    intro n' ps' rs' bd' hmem'
    exact hcfb n' ps' rs' bd' (collectStmts_body_subset hfd hmem')

/-! ### `CodeInFlat` / `ScopedStmts` extraction helpers for the simulation cases -/

omit [DecidableEq D.Value] in
/-- `CodeInFlat` transports along a `collectStmts` inclusion. -/
theorem codeInFlat_mono {flatSc : FScope D} {sub code : List (Stmt D.Op)}
    (hsub : ∀ x ∈ collectStmts sub, x ∈ collectStmts code)
    (h : CodeInFlat flatSc code) : CodeInFlat flatSc sub :=
  fun n ps rs bd hm => h n ps rs bd (hsub _ hm)

omit [DecidableEq D.Value] in
theorem collectStmts_singleton (s : Stmt D.Op) : collectStmts [s] = collectStmt s := by
  simp only [collectStmts, List.append_nil]

omit [DecidableEq D.Value] in
theorem cif_block_inv {flatSc : FScope D} {body : List (Stmt D.Op)}
    (h : CodeInFlat flatSc [Stmt.block body]) : CodeInFlat flatSc body :=
  codeInFlat_mono (fun _ hx => by rw [collectStmts_singleton]; exact hx) h

omit [DecidableEq D.Value] in
theorem cif_block_wrap {flatSc : FScope D} {body : List (Stmt D.Op)}
    (h : CodeInFlat flatSc body) : CodeInFlat flatSc [Stmt.block body] :=
  codeInFlat_mono (fun _ hx => by rw [collectStmts_singleton] at hx; exact hx) h

omit [DecidableEq D.Value] in
theorem cif_cond_inv {flatSc : FScope D} {c} {body : List (Stmt D.Op)}
    (h : CodeInFlat flatSc [Stmt.cond c body]) : CodeInFlat flatSc body :=
  codeInFlat_mono (fun _ hx => by rw [collectStmts_singleton]; exact hx) h

omit [DecidableEq D.Value] in
theorem cif_head {flatSc : FScope D} {s} {rest : List (Stmt D.Op)}
    (h : CodeInFlat flatSc (s :: rest)) : CodeInFlat flatSc [s] :=
  codeInFlat_mono (fun x hx => by
    rw [collectStmts_singleton] at hx
    rw [collectStmts, List.mem_append]; exact Or.inl hx) h

omit [DecidableEq D.Value] in
theorem cif_tail {flatSc : FScope D} {s} {rest : List (Stmt D.Op)}
    (h : CodeInFlat flatSc (s :: rest)) : CodeInFlat flatSc rest :=
  codeInFlat_mono (fun x hx => by rw [collectStmts, List.mem_append]; exact Or.inr hx) h

omit [DecidableEq D.Value] in
theorem cif_for_init {flatSc : FScope D} {init c post body}
    (h : CodeInFlat flatSc [Stmt.forLoop init c post body]) : CodeInFlat flatSc init :=
  codeInFlat_mono (fun x hx => by
    rw [collectStmts_singleton, collectStmt, List.mem_append, List.mem_append]
    exact Or.inl (Or.inl hx)) h

omit [DecidableEq D.Value] in
theorem cif_for_post {flatSc : FScope D} {init c post body}
    (h : CodeInFlat flatSc [Stmt.forLoop init c post body]) : CodeInFlat flatSc post :=
  codeInFlat_mono (fun x hx => by
    rw [collectStmts_singleton, collectStmt, List.mem_append, List.mem_append]
    exact Or.inl (Or.inr hx)) h

omit [DecidableEq D.Value] in
theorem cif_for_body {flatSc : FScope D} {init c post body}
    (h : CodeInFlat flatSc [Stmt.forLoop init c post body]) : CodeInFlat flatSc body :=
  codeInFlat_mono (fun x hx => by
    rw [collectStmts_singleton, collectStmt, List.mem_append]
    exact Or.inr hx) h

/-- The block a `switch` selects has its collected functions among the cases'
and default's collected functions. -/
theorem collectStmts_selectSwitch_subset (cv) :
    ∀ {cases : List (Literal × Block D.Op)} {dflt : Option (Block D.Op)} {x},
      x ∈ collectStmts (selectSwitch D cv cases dflt) → x ∈ collectCases cases ++ collectDflt dflt
  | [], dflt, x, hx => by
      unfold selectSwitch at hx
      simp only [List.find?_nil] at hx
      cases dflt with
      | none => simp only [Option.getD_none, collectStmts, List.not_mem_nil] at hx
      | some b => simpa only [Option.getD_some, collectCases, collectDflt, List.nil_append] using hx
  | (l, b) :: rest, dflt, x, hx => by
      unfold selectSwitch at hx
      by_cases hcv : cv = D.litValue l
      · rw [List.find?_cons_of_pos (by simp [hcv])] at hx
        rw [collectCases]
        exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hx)))
      · rw [List.find?_cons_of_neg (by simp [hcv])] at hx
        have h2 := collectStmts_selectSwitch_subset cv (cases := rest) (dflt := dflt) hx
        rw [collectCases]
        rcases List.mem_append.mp h2 with h | h
        · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h)))
        · exact List.mem_append.mpr (Or.inr h)

theorem cif_switch_sel {flatSc : FScope D} {c cv cases dflt}
    (h : CodeInFlat flatSc [Stmt.switch c cases dflt]) :
    CodeInFlat flatSc (selectSwitch D cv cases dflt) :=
  codeInFlat_mono (fun x hx => by
    rw [collectStmts_singleton, collectStmt]
    exact collectStmts_selectSwitch_subset cv hx) h

/-- `stripStmts` commutes with `selectSwitch`: stripping then selecting equals
selecting from the stripped cases/default. -/
theorem selectSwitch_strip (cv) :
    ∀ (cases : List (Literal × Block D.Op)) (dflt : Option (Block D.Op)),
      selectSwitch D cv (stripCases cases) (stripDflt dflt)
        = stripStmts (selectSwitch D cv cases dflt)
  | [], dflt => by
      simp only [stripCases]
      unfold selectSwitch
      simp only [List.find?_nil]
      cases dflt with
      | none => rfl
      | some b => rfl
  | (l, b) :: rest, dflt => by
      rw [stripCases]
      unfold selectSwitch
      by_cases hcv : cv = D.litValue l
      · rw [List.find?_cons_of_pos (by simp [hcv]), List.find?_cons_of_pos (by simp [hcv])]
      · rw [List.find?_cons_of_neg (by simp [hcv]), List.find?_cons_of_neg (by simp [hcv])]
        exact selectSwitch_strip cv rest dflt

/-- The selected `switch` block is well scoped (in the block-hoisted scope) when
the cases and default are. -/
theorem scopedStmts_selectSwitch {Γ} {cv} :
    ∀ {cases : List (Literal × Block D.Op)} {dflt : Option (Block D.Op)},
      ScopedCases Γ cases → ScopedDflt Γ dflt →
      ScopedStmts (funNamesTop (selectSwitch D cv cases dflt) ++ Γ) (selectSwitch D cv cases dflt)
  | [], dflt, _, hd => by
      unfold selectSwitch
      simp only [List.find?_nil]
      cases dflt with
      | none => exact trivial
      | some b => exact hd
  | (l, b) :: rest, dflt, hc, hd => by
      unfold selectSwitch
      by_cases hcv : cv = D.litValue l
      · rw [List.find?_cons_of_pos (by simp [hcv])]; exact hc.1
      · rw [List.find?_cons_of_neg (by simp [hcv])]; exact scopedStmts_selectSwitch hc.2 hd

/-- **Forward simulation.** Under `GoodO`/`ResEq`/well-scopedness/`CodeInFlat`,
an original derivation transports to one over the flat (lifted) environment on
the `stripCode`-ped code. -/
theorem step_lift_fwd {flatSc : FScope D} :
    ∀ {funs_o V st code res}, Step D funs_o V st code res →
    ∀ {funs_h}, (funNamesEnv funs_o).Nodup → GoodO flatSc funs_o → ResEq flatSc funs_h →
      ScopedCode (funNamesEnv funs_o) code → CodeInFlatCode flatSc code →
      Step D funs_h V st (stripCode code) res := by
  sorry

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
  refine ⟨?_, trivial⟩
  intro n d hmem
  obtain ⟨ps, rs, body, hdeq, hfd⟩ := mem_hoist_inv hmem
  refine ⟨?_, ?_, ?_⟩
  · rw [hdeq]
    have : stripDecl (D := D) { params := ps, rets := rs, body := body }
        = { params := ps, rets := rs, body := stripStmts body } := rfl
    rw [this]
    exact flatLookup_of_mem huniq (mem_collectStmts_of_top hfd)
  · rw [hdeq, funNamesEnv_singleton]
    exact scopedStmts_funDef_body hws hfd
  · rw [hdeq]
    intro n' ps' rs' bd' hmem'
    exact flatLookup_of_mem huniq (collectStmts_body_subset hfd hmem')

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
