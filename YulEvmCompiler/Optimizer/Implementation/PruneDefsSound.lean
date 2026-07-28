import YulEvmCompiler.Optimizer.Implementation.PruneDefs
import YulEvmCompiler.Optimizer.Spec.LocalPass
set_option warningAsError true
/-!
# Soundness of unreachable function-definition pruning

The **hoist-shrinking congruence**: executing under a function environment
whose scopes carry extra entries that the executing code never names in call
position is pointwise equivalent to executing without them.

Architecture:

* `Good R` — the code invariant: no call name (at any depth, including nested
  definition bodies) is in the removed set `R`.
* `PFunsRel R` — the environment relation: an *upper* segment of pairwise
  related scopes (target scope = source scope filtered by `R`, or equal; every
  surviving entry's body `Good`) over a *common* tail.  Lookups of `Good`
  names either resolve in the upper segment — to the same declaration with a
  related closure and a `Good` body — or fall through to the common tail,
  where both environments are literally equal and the original sub-derivation
  is reused unchanged.
* `Step.prune_congr` / `Step.prune_congr_bwd` — the two rule inductions.
* The root-sequence lemma: dropped `funDef` statements are execution no-ops.
* `pruneDefsBlock_sound` — assembly: the closure property of `liveDefs`
  discharges the `Good` obligations of the pruned root.
-/

namespace YulEvmCompiler.Optimizer.PruneDefs

open YulSemantics
open YulSemantics.EVM

variable {calls : ExternalCalls} {creates : ExternalCreates}
local notation "D" => evmWithExternal calls creates

/-! ### The code invariant -/

/-- No call name of `e` is in `R`. -/
def GoodE (R : List Ident) (e : Expr Op) : Prop :=
  ∀ n ∈ callNamesExpr e, n ∉ R

def GoodArgs (R : List Ident) (args : List (Expr Op)) : Prop :=
  ∀ n ∈ callNamesArgs args, n ∉ R

def GoodS (R : List Ident) (s : Stmt Op) : Prop :=
  ∀ n ∈ callNamesStmt s, n ∉ R

def GoodSS (R : List Ident) (ss : List (Stmt Op)) : Prop :=
  ∀ n ∈ callNamesStmts ss, n ∉ R

def GoodCases (R : List Ident) (cs : List (Literal × Block Op)) : Prop :=
  ∀ n ∈ callNamesCases cs, n ∉ R

def GoodDflt (R : List Ident) (d : Option (Block Op)) : Prop :=
  ∀ n ∈ callNamesDflt d, n ∉ R

/-- The invariant per code class. -/
def GoodCode (R : List Ident) : Code Op → Prop
  | .expr e => GoodE R e
  | .args args => GoodArgs R args
  | .stmt s => GoodS R s
  | .stmts ss => GoodSS R ss
  | .loop c post body => GoodE R c ∧ GoodSS R post ∧ GoodSS R body

/-! Decomposition lemmas (the callNames functions are `++`-structured). -/

theorem GoodArgs.head {R : List Ident} {e : Expr Op} {rest : List (Expr Op)}
    (h : GoodArgs R (e :: rest)) : GoodE R e :=
  fun n hn => h n (by simp [callNamesArgs, hn])

theorem GoodArgs.tail {R : List Ident} {e : Expr Op} {rest : List (Expr Op)}
    (h : GoodArgs R (e :: rest)) : GoodArgs R rest :=
  fun n hn => h n (by simp [callNamesArgs, hn])

theorem GoodE.builtin {R : List Ident} {op : Op} {args : List (Expr Op)}
    (h : GoodE R (.builtin op args)) : GoodArgs R args :=
  fun n hn => h n (by simp [callNamesExpr, hn])

theorem GoodE.callArgs {R : List Ident} {f : Ident} {args : List (Expr Op)}
    (h : GoodE R (.call f args)) : GoodArgs R args :=
  fun n hn => h n (by simp [callNamesExpr, hn])

theorem GoodE.callName {R : List Ident} {f : Ident} {args : List (Expr Op)}
    (h : GoodE R (.call f args)) : f ∉ R :=
  h f (by simp [callNamesExpr])

theorem GoodSS.head {R : List Ident} {s : Stmt Op} {rest : List (Stmt Op)}
    (h : GoodSS R (s :: rest)) : GoodS R s :=
  fun n hn => h n (by simp [callNamesStmts, hn])

theorem GoodSS.tail {R : List Ident} {s : Stmt Op} {rest : List (Stmt Op)}
    (h : GoodSS R (s :: rest)) : GoodSS R rest :=
  fun n hn => h n (by simp [callNamesStmts, hn])

theorem GoodS.block {R : List Ident} {body : List (Stmt Op)}
    (h : GoodS R (.block body)) : GoodSS R body :=
  fun n hn => h n (by simp [callNamesStmt, hn])

theorem GoodS.letSome {R : List Ident} {xs : List Ident} {e : Expr Op}
    (h : GoodS R (.letDecl xs (some e))) : GoodE R e :=
  fun n hn => h n (by simp [callNamesStmt, hn])

theorem GoodS.assign {R : List Ident} {xs : List Ident} {e : Expr Op}
    (h : GoodS R (.assign xs e)) : GoodE R e :=
  fun n hn => h n (by simp [callNamesStmt, hn])

theorem GoodS.exprStmt {R : List Ident} {e : Expr Op}
    (h : GoodS R (.exprStmt e)) : GoodE R e :=
  fun n hn => h n (by simp [callNamesStmt, hn])

theorem GoodS.condE {R : List Ident} {e : Expr Op} {body : List (Stmt Op)}
    (h : GoodS R (.cond e body)) : GoodE R e :=
  fun n hn => h n (by simp [callNamesStmt, hn])

theorem GoodS.condBody {R : List Ident} {e : Expr Op} {body : List (Stmt Op)}
    (h : GoodS R (.cond e body)) : GoodSS R body :=
  fun n hn => h n (by simp [callNamesStmt, hn])

theorem GoodS.switchE {R : List Ident} {e : Expr Op}
    {cs : List (Literal × Block Op)} {d : Option (Block Op)}
    (h : GoodS R (.switch e cs d)) : GoodE R e :=
  fun n hn => h n (by simp [callNamesStmt, hn])

theorem GoodS.switchCases {R : List Ident} {e : Expr Op}
    {cs : List (Literal × Block Op)} {d : Option (Block Op)}
    (h : GoodS R (.switch e cs d)) : GoodCases R cs :=
  fun n hn => h n (by simp [callNamesStmt, hn])

theorem GoodS.switchDflt {R : List Ident} {e : Expr Op}
    {cs : List (Literal × Block Op)} {d : Option (Block Op)}
    (h : GoodS R (.switch e cs d)) : GoodDflt R d :=
  fun n hn => h n (by simp [callNamesStmt, hn])

theorem GoodS.forInit {R : List Ident} {init : List (Stmt Op)} {e : Expr Op}
    {post body : List (Stmt Op)}
    (h : GoodS R (.forLoop init e post body)) : GoodSS R init :=
  fun n hn => h n (by simp [callNamesStmt, hn])

theorem GoodS.forCond {R : List Ident} {init : List (Stmt Op)} {e : Expr Op}
    {post body : List (Stmt Op)}
    (h : GoodS R (.forLoop init e post body)) : GoodE R e :=
  fun n hn => h n (by simp [callNamesStmt, hn])

theorem GoodS.forPost {R : List Ident} {init : List (Stmt Op)} {e : Expr Op}
    {post body : List (Stmt Op)}
    (h : GoodS R (.forLoop init e post body)) : GoodSS R post :=
  fun n hn => h n (by simp [callNamesStmt, hn])

theorem GoodS.forBody {R : List Ident} {init : List (Stmt Op)} {e : Expr Op}
    {post body : List (Stmt Op)}
    (h : GoodS R (.forLoop init e post body)) : GoodSS R body :=
  fun n hn => h n (by simp [callNamesStmt, hn])

theorem GoodS.funBody {R : List Ident} {n : Ident} {ps rs : List Ident}
    {body : List (Stmt Op)}
    (h : GoodS R (.funDef n ps rs body)) : GoodSS R body :=
  fun m hm => h m (by simp [callNamesStmt, hm])

theorem mem_callNamesCases_of_mem {n : Ident} {p : Literal × Block Op} :
    ∀ {cs : List (Literal × Block Op)}, p ∈ cs → n ∈ callNamesStmts p.2 →
      n ∈ callNamesCases cs
  | [], hp, _ => absurd hp (List.not_mem_nil)
  | q :: rest, hp, hn => by
      rcases List.mem_cons.mp hp with rfl | hp'
      · simp [callNamesCases, hn]
      · simp [callNamesCases, mem_callNamesCases_of_mem hp' hn]

/-- The selected switch block of `Good` cases/default is `Good`. -/
theorem good_selectSwitch {R : List Ident} {cv : U256}
    {cs : List (Literal × Block Op)} {d : Option (Block Op)}
    (hcs : GoodCases R cs) (hd : GoodDflt R d) :
    GoodSS R (selectSwitch D cv cs d) := by
  intro n hn
  unfold selectSwitch at hn
  cases hfind : cs.find? (fun p => decide (cv = Dialect.litValue D p.1)) with
  | none =>
      rw [hfind] at hn
      cases d with
      | none => simp at hn; cases hn
      | some b => exact hd n hn
  | some p =>
      rw [hfind] at hn
      exact hcs n (mem_callNamesCases_of_mem (List.mem_of_find?_eq_some hfind) hn)

/-- Every definition hoisted from a `Good` sequence has a `Good` body. -/
theorem good_hoist {R : List Ident} {ss : List (Stmt Op)} (h : GoodSS R ss) :
    ∀ p ∈ hoist D ss, GoodSS R p.2.body := by
  induction ss with
  | nil => intro p hp; cases hp
  | cons s rest ih =>
      intro p hp
      unfold hoist at hp
      rw [List.filterMap_cons] at hp
      cases s with
      | funDef n ps rs b =>
          rcases List.mem_cons.mp hp with rfl | hp'
          · exact h.head.funBody
          · exact ih h.tail p hp'
      | block body => exact ih h.tail p hp
      | letDecl xs rhs => exact ih h.tail p hp
      | assign xs e => exact ih h.tail p hp
      | exprStmt e => exact ih h.tail p hp
      | cond c body => exact ih h.tail p hp
      | switch c cs d => exact ih h.tail p hp
      | forLoop i c po b => exact ih h.tail p hp
      | «break» => exact ih h.tail p hp
      | «continue» => exact ih h.tail p hp
      | leave => exact ih h.tail p hp

/-! ### The environment relation -/

/-- One related scope pair of the upper segment: the target is the source
filtered by `R` (or the source unchanged), and every source entry whose name
survives has a `Good` body. -/
def PScopeRel (R : List Ident) (s₁ s₂ : FScope D) : Prop :=
  (s₂ = s₁.filter (fun p => !R.contains p.1) ∨ s₂ = s₁) ∧
  ∀ p ∈ s₁, ¬ R.contains p.1 → GoodSS R p.2.body

/-- Related environments: pairwise related upper scopes over an equal tail. -/
def PFunsRel (R : List Ident) (f₁ f₂ : FunEnv D) : Prop :=
  ∃ u₁ u₂ common, f₁ = u₁ ++ common ∧ f₂ = u₂ ++ common ∧
    List.Forall₂ (PScopeRel R) u₁ u₂

theorem PFunsRel.refl (R : List Ident) (f : FunEnv D) : PFunsRel R f f :=
  ⟨[], [], f, rfl, rfl, .nil⟩

/-- Push an equal scope whose entries all have `Good` bodies. -/
theorem PFunsRel.cons_good {R : List Ident} {f₁ f₂ : FunEnv D} (s : FScope D)
    (hgood : ∀ p ∈ s, GoodSS R p.2.body)
    (h : PFunsRel R f₁ f₂) : PFunsRel R (s :: f₁) (s :: f₂) := by
  obtain ⟨u₁, u₂, common, rfl, rfl, hrel⟩ := h
  exact ⟨s :: u₁, s :: u₂, common, rfl, rfl,
    .cons ⟨Or.inr rfl, fun p hp _ => hgood p hp⟩ hrel⟩

/-- `find?` for a name outside `R` agrees across a related scope pair, and a
hit's body is `Good`. -/
theorem pscope_find {R : List Ident} {s₁ s₂ : FScope D}
    (h : PScopeRel R s₁ s₂) {fn : Ident} (hfn : fn ∉ R) :
    (s₁.find? (fun p => p.1 = fn) = none ∧ s₂.find? (fun p => p.1 = fn) = none) ∨
    (∃ p, s₁.find? (fun p => p.1 = fn) = some p ∧
      s₂.find? (fun p => p.1 = fn) = some p ∧ GoodSS R p.2.body) := by
  obtain ⟨hshape, hgood⟩ := h
  rcases hshape with rfl | rfl
  · induction s₁ with
    | nil => left; simp
    | cons q rest ih =>
        by_cases hq : q.1 = fn
        · right
          refine ⟨q, List.find?_cons_of_pos (by simp [hq]), ?_, ?_⟩
          · rw [List.filter_cons_of_pos
              (by simp [hq]; exact fun hc => hfn (by simpa [hq] using hc))]
            exact List.find?_cons_of_pos (by simp [hq])
          · exact hgood q (by simp) (by rw [hq]; simpa using hfn)
        · have ih' := ih (fun p hp hnp => hgood p (by simp [hp]) hnp)
          by_cases hqr : R.contains q.1
          · rw [List.filter_cons_of_neg (by simpa using hqr)]
            rw [List.find?_cons_of_neg (by simp [hq])]
            exact ih'
          · rw [List.filter_cons_of_pos (by simpa using hqr)]
            rw [List.find?_cons_of_neg (by simp [hq]),
              List.find?_cons_of_neg (by simp [hq])]
            exact ih'
  · induction s₂ with
    | nil => left; simp
    | cons q rest ih =>
        by_cases hq : q.1 = fn
        · right
          refine ⟨q, List.find?_cons_of_pos (by simp [hq]),
            List.find?_cons_of_pos (by simp [hq]), ?_⟩
          exact hgood q (by simp) (by rw [hq]; simpa using hfn)
        · rw [List.find?_cons_of_neg (by simp [hq])]
          exact ih (fun p hp hnp => hgood p (by simp [hp]) hnp)

/-- `lookupFun` transport for a name outside `R`: either both environments
resolve to the same declaration — with related closures and a `Good` body —
or the resolution falls into the common tail, where the closures are equal. -/
theorem lookupFun_prel {R : List Ident} {f₁ f₂ : FunEnv D}
    (hR : PFunsRel R f₁ f₂) {fn : Ident} (hfn : fn ∉ R) :
    (lookupFun f₁ fn = none ∧ lookupFun f₂ fn = none) ∨
    (∃ decl cenv₁ cenv₂, lookupFun f₁ fn = some (decl, cenv₁) ∧
      lookupFun f₂ fn = some (decl, cenv₂) ∧
      (cenv₁ = cenv₂ ∨ (PFunsRel R cenv₁ cenv₂ ∧ GoodSS R decl.body))) := by
  obtain ⟨u₁, u₂, common, rfl, rfl, hrel⟩ := hR
  induction hrel with
  | nil =>
      cases hl : lookupFun common fn with
      | none => left; exact ⟨hl, hl⟩
      | some p =>
          right
          exact ⟨p.1, p.2, p.2, by simpa using hl, by simpa using hl, Or.inl rfl⟩
  | @cons s₁ s₂ t₁ t₂ hs _ ih =>
      rcases pscope_find hs hfn with ⟨hn₁, hn₂⟩ | ⟨p, hp₁, hp₂, hgood⟩
      · rw [List.cons_append, List.cons_append, lookupFun, hn₁, lookupFun, hn₂]
        exact ih
      · right
        refine ⟨p.2, s₁ :: (t₁ ++ common), s₂ :: (t₂ ++ common), ?_, ?_, ?_⟩
        · rw [List.cons_append, lookupFun, hp₁]
        · rw [List.cons_append, lookupFun, hp₂]
        · right
          refine ⟨⟨s₁ :: t₁, s₂ :: t₂, common, by simp, by simp, .cons hs ‹_›⟩, hgood⟩

/-- Mirror of `lookupFun_prel`, driven from the target environment. -/
theorem lookupFun_prel_bwd {R : List Ident} {f₁ f₂ : FunEnv D}
    (hR : PFunsRel R f₁ f₂) {fn : Ident} (hfn : fn ∉ R) :
    (lookupFun f₁ fn = none ∧ lookupFun f₂ fn = none) ∨
    (∃ decl cenv₁ cenv₂, lookupFun f₁ fn = some (decl, cenv₁) ∧
      lookupFun f₂ fn = some (decl, cenv₂) ∧
      (cenv₁ = cenv₂ ∨ (PFunsRel R cenv₁ cenv₂ ∧ GoodSS R decl.body))) :=
  lookupFun_prel hR hfn

/-! Bridging decompositions between `GoodSS` and statement-shaped `GoodS`. -/

theorem GoodSS.toBlock {R : List Ident} {body : List (Stmt Op)}
    (h : GoodSS R body) : GoodS R (.block body) :=
  fun n hn => h n (by simpa [callNamesStmt] using hn)

/-! ### The forward rule induction -/

set_option maxHeartbeats 1000000 in
/-- **Hoist-shrinking congruence, forward.** A `Step` of `Good` code
transports from the source environment to the pruned one. -/
theorem Step.prune_congr {R : List Ident} {funs₁ : FunEnv D} {V st code res}
    (h : Step D funs₁ V st code res) :
    ∀ {funs₂}, PFunsRel R funs₁ funs₂ → GoodCode R code →
      Step D funs₂ V st code res := by
  induction h with
  | lit => intro _ _ _; exact Step.lit
  | var hv => intro _ _ _; exact Step.var hv
  | builtinOk _ hb iha => intro _ hR hg; exact Step.builtinOk (iha hR hg.builtin) hb
  | builtinHalt _ hb iha => intro _ hR hg; exact Step.builtinHalt (iha hR hg.builtin) hb
  | builtinArgsHalt _ iha => intro _ hR hg; exact Step.builtinArgsHalt (iha hR hg.builtin)
  | @callOk funs V st fn args argvals st1 decl cenv Vend st2 o ha hl hlen hbody ho iha ihbody =>
      intro funs₂ hR hg
      rcases lookupFun_prel hR hg.callName with ⟨hn₁, _⟩ | ⟨d, c₁, c₂, hl₁, hl₂, hc⟩
      · rw [hl] at hn₁; cases hn₁
      · rw [hl] at hl₁
        injection hl₁ with hd
        injection hd with h1 h2
        subst h1; subst h2
        rcases hc with rfl | ⟨hrel, hgb⟩
        · exact Step.callOk (iha hR hg.callArgs) hl₂ hlen hbody ho
        · exact Step.callOk (iha hR hg.callArgs) hl₂ hlen
            (ihbody hrel hgb.toBlock) ho
  | @callHalt funs V st fn args argvals st1 decl cenv Vend st2 ha hl hlen hbody iha ihbody =>
      intro funs₂ hR hg
      rcases lookupFun_prel hR hg.callName with ⟨hn₁, _⟩ | ⟨d, c₁, c₂, hl₁, hl₂, hc⟩
      · rw [hl] at hn₁; cases hn₁
      · rw [hl] at hl₁
        injection hl₁ with hd
        injection hd with h1 h2
        subst h1; subst h2
        rcases hc with rfl | ⟨hrel, hgb⟩
        · exact Step.callHalt (iha hR hg.callArgs) hl₂ hlen hbody
        · exact Step.callHalt (iha hR hg.callArgs) hl₂ hlen
            (ihbody hrel hgb.toBlock)
  | callArgsHalt _ iha => intro _ hR hg; exact Step.callArgsHalt (iha hR hg.callArgs)
  | argsNil => intro _ _ _; exact Step.argsNil
  | argsCons _ _ iha ihe =>
      intro _ hR hg; exact Step.argsCons (iha hR hg.tail) (ihe hR hg.head)
  | argsRestHalt _ iha => intro _ hR hg; exact Step.argsRestHalt (iha hR hg.tail)
  | argsHeadHalt _ _ iha ihe =>
      intro _ hR hg; exact Step.argsHeadHalt (iha hR hg.tail) (ihe hR hg.head)
  | funDef => intro _ _ _; exact Step.funDef
  | @block funs V st body Vb stb o hbody ihbody =>
      intro funs₂ hR hg
      exact Step.block (ihbody (hR.cons_good _ (good_hoist hg.block)) hg.block)
  | letZero => intro _ _ _; exact Step.letZero
  | letVal _ hlen ihe => intro _ hR hg; exact Step.letVal (ihe hR hg.letSome) hlen
  | letHalt _ ihe => intro _ hR hg; exact Step.letHalt (ihe hR hg.letSome)
  | assignVal _ hlen ihe => intro _ hR hg; exact Step.assignVal (ihe hR hg.assign) hlen
  | assignHalt _ ihe => intro _ hR hg; exact Step.assignHalt (ihe hR hg.assign)
  | exprStmt _ ihe => intro _ hR hg; exact Step.exprStmt (ihe hR hg.exprStmt)
  | exprStmtHalt _ ihe => intro _ hR hg; exact Step.exprStmtHalt (ihe hR hg.exprStmt)
  | ifTrue _ hnz _ ihc ihb =>
      intro _ hR hg
      exact Step.ifTrue (ihc hR hg.condE) hnz (ihb hR hg.condBody.toBlock)
  | ifFalse _ hz ihc => intro _ hR hg; exact Step.ifFalse (ihc hR hg.condE) hz
  | ifHalt _ ihc => intro _ hR hg; exact Step.ifHalt (ihc hR hg.condE)
  | switchExec _ _ ihc ihb =>
      intro _ hR hg
      exact Step.switchExec (ihc hR hg.switchE)
        (ihb hR (good_selectSwitch hg.switchCases hg.switchDflt).toBlock)
  | switchHalt _ ihc => intro _ hR hg; exact Step.switchHalt (ihc hR hg.switchE)
  | @forLoop funs V st init c post body Vinit stinit Vend stend o hinit hloop ihinit ihloop =>
      intro funs₂ hR hg
      exact Step.forLoop
        (ihinit (hR.cons_good _ (good_hoist hg.forInit)) hg.forInit)
        (ihloop (hR.cons_good _ (good_hoist hg.forInit))
          ⟨hg.forCond, hg.forPost, hg.forBody⟩)
  | @forInitHalt funs V st init c post body Vinit stinit hinit ihinit =>
      intro funs₂ hR hg
      exact Step.forInitHalt
        (ihinit (hR.cons_good _ (good_hoist hg.forInit)) hg.forInit)
  | «break» => intro _ _ _; exact Step.break
  | «continue» => intro _ _ _; exact Step.continue
  | leave => intro _ _ _; exact Step.leave
  | seqNil => intro _ _ _; exact Step.seqNil
  | seqCons _ _ ihs ihrest =>
      intro _ hR hg; exact Step.seqCons (ihs hR hg.head) (ihrest hR hg.tail)
  | seqStop _ hne ihs => intro _ hR hg; exact Step.seqStop (ihs hR hg.head) hne
  | loopDone _ hz ihc => intro _ hR hg; exact Step.loopDone (ihc hR hg.1) hz
  | loopCondHalt _ ihc => intro _ hR hg; exact Step.loopCondHalt (ihc hR hg.1)
  | loopStep _ hnz _ hob _ _ ihc ihb ihp ihr =>
      intro _ hR hg
      exact Step.loopStep (ihc hR hg.1) hnz (ihb hR hg.2.2.toBlock) hob
        (ihp hR hg.2.1.toBlock) (ihr hR hg)
  | loopPostHalt _ hnz _ hob _ ihc ihb ihp =>
      intro _ hR hg
      exact Step.loopPostHalt (ihc hR hg.1) hnz (ihb hR hg.2.2.toBlock) hob
        (ihp hR hg.2.1.toBlock)
  | loopBreak _ hnz _ ihc ihb =>
      intro _ hR hg
      exact Step.loopBreak (ihc hR hg.1) hnz (ihb hR hg.2.2.toBlock)
  | loopLeave _ hnz _ ihc ihb =>
      intro _ hR hg
      exact Step.loopLeave (ihc hR hg.1) hnz (ihb hR hg.2.2.toBlock)
  | loopBodyHalt _ hnz _ ihc ihb =>
      intro _ hR hg
      exact Step.loopBodyHalt (ihc hR hg.1) hnz (ihb hR hg.2.2.toBlock)

/-! ### The backward rule induction -/

set_option maxHeartbeats 1000000 in
/-- **Hoist-shrinking congruence, backward.** A `Step` of `Good` code under
the pruned environment transports back to the source environment. -/
theorem Step.prune_congr_bwd {R : List Ident} {funs₂ : FunEnv D} {V st code res}
    (h : Step D funs₂ V st code res) :
    ∀ {funs₁}, PFunsRel R funs₁ funs₂ → GoodCode R code →
      Step D funs₁ V st code res := by
  induction h with
  | lit => intro _ _ _; exact Step.lit
  | var hv => intro _ _ _; exact Step.var hv
  | builtinOk _ hb iha => intro _ hR hg; exact Step.builtinOk (iha hR hg.builtin) hb
  | builtinHalt _ hb iha => intro _ hR hg; exact Step.builtinHalt (iha hR hg.builtin) hb
  | builtinArgsHalt _ iha => intro _ hR hg; exact Step.builtinArgsHalt (iha hR hg.builtin)
  | @callOk funs V st fn args argvals st1 decl cenv Vend st2 o ha hl hlen hbody ho iha ihbody =>
      intro funs₁ hR hg
      rcases lookupFun_prel hR hg.callName with ⟨_, hn₂⟩ | ⟨d, c₁, c₂, hl₁, hl₂, hc⟩
      · rw [hl] at hn₂; cases hn₂
      · rw [hl] at hl₂
        injection hl₂ with hd
        injection hd with h1 h2
        subst h1; subst h2
        rcases hc with rfl | ⟨hrel, hgb⟩
        · exact Step.callOk (iha hR hg.callArgs) hl₁ hlen hbody ho
        · exact Step.callOk (iha hR hg.callArgs) hl₁ hlen
            (ihbody hrel hgb.toBlock) ho
  | @callHalt funs V st fn args argvals st1 decl cenv Vend st2 ha hl hlen hbody iha ihbody =>
      intro funs₁ hR hg
      rcases lookupFun_prel hR hg.callName with ⟨_, hn₂⟩ | ⟨d, c₁, c₂, hl₁, hl₂, hc⟩
      · rw [hl] at hn₂; cases hn₂
      · rw [hl] at hl₂
        injection hl₂ with hd
        injection hd with h1 h2
        subst h1; subst h2
        rcases hc with rfl | ⟨hrel, hgb⟩
        · exact Step.callHalt (iha hR hg.callArgs) hl₁ hlen hbody
        · exact Step.callHalt (iha hR hg.callArgs) hl₁ hlen
            (ihbody hrel hgb.toBlock)
  | callArgsHalt _ iha => intro _ hR hg; exact Step.callArgsHalt (iha hR hg.callArgs)
  | argsNil => intro _ _ _; exact Step.argsNil
  | argsCons _ _ iha ihe =>
      intro _ hR hg; exact Step.argsCons (iha hR hg.tail) (ihe hR hg.head)
  | argsRestHalt _ iha => intro _ hR hg; exact Step.argsRestHalt (iha hR hg.tail)
  | argsHeadHalt _ _ iha ihe =>
      intro _ hR hg; exact Step.argsHeadHalt (iha hR hg.tail) (ihe hR hg.head)
  | funDef => intro _ _ _; exact Step.funDef
  | @block funs V st body Vb stb o hbody ihbody =>
      intro funs₁ hR hg
      exact Step.block (ihbody (hR.cons_good _ (good_hoist hg.block)) hg.block)
  | letZero => intro _ _ _; exact Step.letZero
  | letVal _ hlen ihe => intro _ hR hg; exact Step.letVal (ihe hR hg.letSome) hlen
  | letHalt _ ihe => intro _ hR hg; exact Step.letHalt (ihe hR hg.letSome)
  | assignVal _ hlen ihe => intro _ hR hg; exact Step.assignVal (ihe hR hg.assign) hlen
  | assignHalt _ ihe => intro _ hR hg; exact Step.assignHalt (ihe hR hg.assign)
  | exprStmt _ ihe => intro _ hR hg; exact Step.exprStmt (ihe hR hg.exprStmt)
  | exprStmtHalt _ ihe => intro _ hR hg; exact Step.exprStmtHalt (ihe hR hg.exprStmt)
  | ifTrue _ hnz _ ihc ihb =>
      intro _ hR hg
      exact Step.ifTrue (ihc hR hg.condE) hnz (ihb hR hg.condBody.toBlock)
  | ifFalse _ hz ihc => intro _ hR hg; exact Step.ifFalse (ihc hR hg.condE) hz
  | ifHalt _ ihc => intro _ hR hg; exact Step.ifHalt (ihc hR hg.condE)
  | switchExec _ _ ihc ihb =>
      intro _ hR hg
      exact Step.switchExec (ihc hR hg.switchE)
        (ihb hR (good_selectSwitch hg.switchCases hg.switchDflt).toBlock)
  | switchHalt _ ihc => intro _ hR hg; exact Step.switchHalt (ihc hR hg.switchE)
  | @forLoop funs V st init c post body Vinit stinit Vend stend o hinit hloop ihinit ihloop =>
      intro funs₁ hR hg
      exact Step.forLoop
        (ihinit (hR.cons_good _ (good_hoist hg.forInit)) hg.forInit)
        (ihloop (hR.cons_good _ (good_hoist hg.forInit))
          ⟨hg.forCond, hg.forPost, hg.forBody⟩)
  | @forInitHalt funs V st init c post body Vinit stinit hinit ihinit =>
      intro funs₁ hR hg
      exact Step.forInitHalt
        (ihinit (hR.cons_good _ (good_hoist hg.forInit)) hg.forInit)
  | «break» => intro _ _ _; exact Step.break
  | «continue» => intro _ _ _; exact Step.continue
  | leave => intro _ _ _; exact Step.leave
  | seqNil => intro _ _ _; exact Step.seqNil
  | seqCons _ _ ihs ihrest =>
      intro _ hR hg; exact Step.seqCons (ihs hR hg.head) (ihrest hR hg.tail)
  | seqStop _ hne ihs => intro _ hR hg; exact Step.seqStop (ihs hR hg.head) hne
  | loopDone _ hz ihc => intro _ hR hg; exact Step.loopDone (ihc hR hg.1) hz
  | loopCondHalt _ ihc => intro _ hR hg; exact Step.loopCondHalt (ihc hR hg.1)
  | loopStep _ hnz _ hob _ _ ihc ihb ihp ihr =>
      intro _ hR hg
      exact Step.loopStep (ihc hR hg.1) hnz (ihb hR hg.2.2.toBlock) hob
        (ihp hR hg.2.1.toBlock) (ihr hR hg)
  | loopPostHalt _ hnz _ hob _ ihc ihb ihp =>
      intro _ hR hg
      exact Step.loopPostHalt (ihc hR hg.1) hnz (ihb hR hg.2.2.toBlock) hob
        (ihp hR hg.2.1.toBlock)
  | loopBreak _ hnz _ ihc ihb =>
      intro _ hR hg
      exact Step.loopBreak (ihc hR hg.1) hnz (ihb hR hg.2.2.toBlock)
  | loopLeave _ hnz _ ihc ihb =>
      intro _ hR hg
      exact Step.loopLeave (ihc hR hg.1) hnz (ihb hR hg.2.2.toBlock)
  | loopBodyHalt _ hnz _ ihc ihb =>
      intro _ hR hg
      exact Step.loopBodyHalt (ihc hR hg.1) hnz (ihb hR hg.2.2.toBlock)

/-! ### Dropped `funDef` statements are execution no-ops -/

/-- Forward: a run of the source sequence yields a run of the pruned
sequence, with the same result. -/
theorem pruneRoot_fwd {live : List Ident} :
    ∀ {ss : List (Stmt Op)} {funs : FunEnv D} {V st V₁ st₁ o},
      Step D funs V st (.stmts ss) (.sres V₁ st₁ o) →
      Step D funs V st (.stmts (pruneRoot live ss)) (.sres V₁ st₁ o) := by
  intro ss
  induction ss with
  | nil => intro funs V st V₁ st₁ o h; simpa [pruneRoot] using h
  | cons s rest ih =>
      intro funs V st V₁ st₁ o h
      cases s with
      | funDef n ps rs b =>
          cases h with
          | seqCons hs htail =>
              cases hs
              unfold pruneRoot
              by_cases hn : live.contains n
              · rw [if_pos hn]
                exact Step.seqCons Step.funDef (ih htail)
              · rw [if_neg hn]
                exact ih htail
          | seqStop hs hne =>
              cases hs
              exact absurd rfl hne
      | block body =>
          cases h with
          | seqCons hs htail => exact Step.seqCons hs (ih htail)
          | seqStop hs hne => exact Step.seqStop hs hne
      | letDecl xs rhs =>
          cases h with
          | seqCons hs htail => exact Step.seqCons hs (ih htail)
          | seqStop hs hne => exact Step.seqStop hs hne
      | assign xs e =>
          cases h with
          | seqCons hs htail => exact Step.seqCons hs (ih htail)
          | seqStop hs hne => exact Step.seqStop hs hne
      | exprStmt e =>
          cases h with
          | seqCons hs htail => exact Step.seqCons hs (ih htail)
          | seqStop hs hne => exact Step.seqStop hs hne
      | cond c body =>
          cases h with
          | seqCons hs htail => exact Step.seqCons hs (ih htail)
          | seqStop hs hne => exact Step.seqStop hs hne
      | switch c cs d =>
          cases h with
          | seqCons hs htail => exact Step.seqCons hs (ih htail)
          | seqStop hs hne => exact Step.seqStop hs hne
      | forLoop i c p b =>
          cases h with
          | seqCons hs htail => exact Step.seqCons hs (ih htail)
          | seqStop hs hne => exact Step.seqStop hs hne
      | «break» =>
          cases h with
          | seqCons hs htail => exact Step.seqCons hs (ih htail)
          | seqStop hs hne => exact Step.seqStop hs hne
      | «continue» =>
          cases h with
          | seqCons hs htail => exact Step.seqCons hs (ih htail)
          | seqStop hs hne => exact Step.seqStop hs hne
      | leave =>
          cases h with
          | seqCons hs htail => exact Step.seqCons hs (ih htail)
          | seqStop hs hne => exact Step.seqStop hs hne

/-- Backward: a run of the pruned sequence yields a run of the source
sequence (re-inserting the no-op `funDef` steps). -/
theorem pruneRoot_bwd {live : List Ident} :
    ∀ {ss : List (Stmt Op)} {funs : FunEnv D} {V st V₁ st₁ o},
      Step D funs V st (.stmts (pruneRoot live ss)) (.sres V₁ st₁ o) →
      Step D funs V st (.stmts ss) (.sres V₁ st₁ o) := by
  intro ss
  induction ss with
  | nil => intro funs V st V₁ st₁ o h; simpa [pruneRoot] using h
  | cons s rest ih =>
      intro funs V st V₁ st₁ o h
      cases s with
      | funDef n ps rs b =>
          unfold pruneRoot at h
          by_cases hn : live.contains n
          · rw [if_pos hn] at h
            cases h with
            | seqCons hs htail =>
                cases hs
                exact Step.seqCons Step.funDef (ih htail)
            | seqStop hs hne =>
                cases hs
                exact absurd rfl hne
          · rw [if_neg hn] at h
            exact Step.seqCons Step.funDef (ih h)
      | block body =>
          cases h with
          | seqCons hs htail => exact Step.seqCons hs (ih htail)
          | seqStop hs hne => exact Step.seqStop hs hne
      | letDecl xs rhs =>
          cases h with
          | seqCons hs htail => exact Step.seqCons hs (ih htail)
          | seqStop hs hne => exact Step.seqStop hs hne
      | assign xs e =>
          cases h with
          | seqCons hs htail => exact Step.seqCons hs (ih htail)
          | seqStop hs hne => exact Step.seqStop hs hne
      | exprStmt e =>
          cases h with
          | seqCons hs htail => exact Step.seqCons hs (ih htail)
          | seqStop hs hne => exact Step.seqStop hs hne
      | cond c body =>
          cases h with
          | seqCons hs htail => exact Step.seqCons hs (ih htail)
          | seqStop hs hne => exact Step.seqStop hs hne
      | switch c cs d =>
          cases h with
          | seqCons hs htail => exact Step.seqCons hs (ih htail)
          | seqStop hs hne => exact Step.seqStop hs hne
      | forLoop i c p b =>
          cases h with
          | seqCons hs htail => exact Step.seqCons hs (ih htail)
          | seqStop hs hne => exact Step.seqStop hs hne
      | «break» =>
          cases h with
          | seqCons hs htail => exact Step.seqCons hs (ih htail)
          | seqStop hs hne => exact Step.seqStop hs hne
      | «continue» =>
          cases h with
          | seqCons hs htail => exact Step.seqCons hs (ih htail)
          | seqStop hs hne => exact Step.seqStop hs hne
      | leave =>
          cases h with
          | seqCons hs htail => exact Step.seqCons hs (ih htail)
          | seqStop hs hne => exact Step.seqStop hs hne

/-! ### Closure facts about `liveDefs` -/

/-- Equation lemma: fixpoint reached. -/
theorem reachFuel_succ_nil {defs : List (Ident × List Ident)} {live : List Ident}
    {fuel : Nat} (h : reachNew defs live = []) :
    reachFuel defs (fuel + 1) live = live := by
  rw [reachFuel, h]

/-- Equation lemma: a productive round recurses on the grown set. -/
theorem reachFuel_succ_cons {defs : List (Ident × List Ident)} {live : List Ident}
    {fuel : Nat} {a : Ident} {t : List Ident} (h : reachNew defs live = a :: t) :
    reachFuel defs (fuel + 1) live =
      reachFuel defs fuel (live ++ (a :: t).eraseDups) := by
  rw [reachFuel, h]

/-- The seed survives into the closure. -/
theorem reachFuel_mono (defs : List (Ident × List Ident)) :
    ∀ (fuel : Nat) (seed : List Ident) {n : Ident},
      n ∈ seed → n ∈ reachFuel defs fuel seed
  | 0, seed, n, hn => by simp [reachFuel, hn]
  | fuel + 1, seed, n, hn => by
      cases hnew : reachNew defs seed with
      | nil => rw [reachFuel_succ_nil hnew]; exact hn
      | cons a t =>
          rw [reachFuel_succ_cons hnew]
          exact reachFuel_mono defs fuel _ (by simp [hn])

/-- The closure property: a live definition's defined call names are live. -/
theorem reachFuel_closed (defs : List (Ident × List Ident)) :
    ∀ (fuel : Nat) (seed : List Ident) {n : Ident} {cs : List Ident},
      (n, cs) ∈ defs → (reachFuel defs fuel seed).contains n →
      ∀ m ∈ cs, defs.any (fun d => d.1 = m) →
        (reachFuel defs fuel seed).contains m
  | 0, seed, n, cs, hdef, _, m, hm, hmdef => by
      have hmem : m ∈ defs.map (·.1) := by
        obtain ⟨d, hd, he⟩ := List.any_eq_true.mp hmdef
        exact List.mem_map.mpr ⟨d, hd, by simpa using he⟩
      simp [reachFuel, List.contains_eq_mem, hmem]
  | fuel + 1, seed, n, cs, hdef, hn, m, hm, hmdef => by
      cases hnew : reachNew defs seed with
      | nil =>
          rw [reachFuel_succ_nil hnew] at hn ⊢
          by_cases hms : seed.contains m
          · exact hms
          · exfalso
            have hmem : m ∈ reachNew defs seed := by
              refine List.mem_filter.mpr ⟨?_, ?_⟩
              · exact List.mem_flatMap.mpr ⟨(n, cs), List.mem_filter.mpr ⟨hdef, hn⟩, hm⟩
              · rw [Bool.and_eq_true]
                exact ⟨by simpa using hms, hmdef⟩
            rw [hnew] at hmem
            cases hmem
      | cons a t =>
          rw [reachFuel_succ_cons hnew] at hn ⊢
          exact reachFuel_closed defs fuel _ hdef hn m hm hmdef

/-! ### Transform structure lemmas -/

/-- A hoisted entry's name/call-list pair is a `rootDefs` entry. -/
theorem rootDefs_of_hoist : ∀ {ss : List (Stmt Op)} {p : Ident × FDecl D},
    p ∈ hoist D ss → (p.1, callNamesStmts p.2.body) ∈ rootDefs ss := by
  intro ss
  induction ss with
  | nil => intro p hp; cases hp
  | cons s rest ih =>
      intro p hp
      cases s
      case funDef n ps rs b =>
        rw [show hoist D (Stmt.funDef n ps rs b :: rest) =
          (n, ⟨ps, rs, b⟩) :: hoist D rest from rfl] at hp
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (ih hp')
      all_goals exact ih hp

/-- A hoisted entry's name is a defined name. -/
theorem hoist_name_defined {ss : List (Stmt Op)} {p : Ident × FDecl D}
    (hp : p ∈ hoist D ss) : (rootDefs ss).any (fun d => d.1 = p.1) := by
  have := rootDefs_of_hoist (calls := calls) (creates := creates) hp
  exact List.any_eq_true.mpr ⟨_, this, by simp⟩

/-- Hoisting the pruned root is filtering the hoisted scope by liveness. -/
theorem hoist_pruneRoot (live : List Ident) : ∀ (ss : List (Stmt Op)),
    hoist D (pruneRoot live ss) =
      (hoist D ss).filter (fun p => live.contains p.1) := by
  intro ss
  induction ss with
  | nil => rfl
  | cons s rest ih =>
      cases s
      case funDef n ps rs b =>
        by_cases hn : live.contains n
        · rw [show pruneRoot live (Stmt.funDef n ps rs b :: rest) =
            Stmt.funDef n ps rs b :: pruneRoot live rest from by
              simp only [pruneRoot, if_pos hn]]
          rw [show hoist D (Stmt.funDef n ps rs b :: pruneRoot live rest) =
            (n, ⟨ps, rs, b⟩) :: hoist D (pruneRoot live rest) from rfl]
          rw [show hoist D (Stmt.funDef n ps rs b :: rest) =
            (n, ⟨ps, rs, b⟩) :: hoist D rest from rfl]
          rw [List.filter_cons_of_pos (by simpa using hn)]
          exact congrArg _ ih
        · rw [show pruneRoot live (Stmt.funDef n ps rs b :: rest) =
            pruneRoot live rest from by simp only [pruneRoot, if_neg hn]]
          rw [show hoist D (Stmt.funDef n ps rs b :: rest) =
            (n, ⟨ps, rs, b⟩) :: hoist D rest from rfl]
          rw [List.filter_cons_of_neg (by simpa using hn)]
          exact ih
      all_goals exact ih

/-! ### Assembly -/

/-- The removed set: defined names the closure did not reach. -/
def deadSet (b : Block Op) : List Ident :=
  ((rootDefs b).map (·.1)).filter (fun n => !(liveDefs b).contains n)

theorem deadSet_not_live {b : Block Op} {n : Ident}
    (h : n ∈ deadSet b) : ¬ (liveDefs b).contains n := by
  have := List.mem_filter.mp h
  simpa using this.2

theorem not_deadSet_of_live {b : Block Op} {n : Ident}
    (h : (liveDefs b).contains n) : n ∉ deadSet b := fun hc =>
  deadSet_not_live hc h

theorem not_deadSet_of_undefined {b : Block Op} {n : Ident}
    (h : ¬ ((rootDefs b).map (·.1)).contains n) : n ∉ deadSet b := fun hc =>
  h (by
    have := (List.mem_filter.mp hc).1
    simpa [List.contains_eq_mem] using this)

theorem live_of_not_deadSet {b : Block Op} {n : Ident}
    (hdef : ((rootDefs b).map (·.1)).contains n) (h : n ∉ deadSet b) :
    (liveDefs b).contains n := by
  by_contra hlive
  exact h (List.mem_filter.mpr
    ⟨by simpa [List.contains_eq_mem] using hdef, by simpa using hlive⟩)

/-- A live definition's body is `Good`: its defined call names are live, and
its undefined call names cannot be dead. -/
theorem good_body_of_live {b : Block Op} {n : Ident} {cs : List Ident}
    (hdef : (n, cs) ∈ rootDefs b) (hlive : (liveDefs b).contains n) :
    ∀ m ∈ cs, m ∉ deadSet b := by
  intro m hm
  by_cases hmdef : (rootDefs b).any (fun d => d.1 = m)
  · exact not_deadSet_of_live
      (reachFuel_closed (rootDefs b) _ _ hdef hlive m hm hmdef)
  · refine not_deadSet_of_undefined (fun hc => hmdef ?_)
    have hm' : m ∈ (rootDefs b).map (·.1) := by
      simpa [List.contains_eq_mem] using hc
    obtain ⟨d, hd, he⟩ := List.mem_map.mp hm'
    exact List.any_eq_true.mpr ⟨d, hd, by simp [he]⟩

/-- The seed is live. -/
theorem live_of_rootCalls {b : Block Op} {n : Ident}
    (h : n ∈ rootCalls b) : (liveDefs b).contains n := by
  unfold liveDefs
  have := reachFuel_mono (rootDefs b) ((rootDefs b).length + 1) _
    (List.mem_eraseDups.mpr h)
  simpa [List.contains_eq_mem] using this

/-- Call names of the pruned root come from the entry code or a live body. -/
theorem callNames_pruneRoot {live : List Ident} :
    ∀ {ss : List (Stmt Op)} {n : Ident},
      n ∈ callNamesStmts (pruneRoot live ss) →
      n ∈ rootCalls ss ∨
        ∃ d cs, (d, cs) ∈ rootDefs ss ∧ live.contains d ∧ n ∈ cs := by
  intro ss
  induction ss with
  | nil => intro n hn; cases hn
  | cons s rest ih =>
      intro n hn
      cases s
      case funDef m ps rs bd =>
        by_cases hm : live.contains m
        · rw [show pruneRoot live (Stmt.funDef m ps rs bd :: rest) =
            Stmt.funDef m ps rs bd :: pruneRoot live rest from by
              simp only [pruneRoot, if_pos hm]] at hn
          rcases List.mem_append.mp
            (show n ∈ callNamesStmt (Stmt.funDef m ps rs bd) ++
              callNamesStmts (pruneRoot live rest) from hn) with hh | ht
          · exact Or.inr ⟨m, callNamesStmts bd, List.mem_cons_self .., hm,
              show n ∈ callNamesStmts bd from hh⟩
          · rcases ih ht with hc | ⟨d, cs, hd, hl, hnc⟩
            · exact Or.inl (show n ∈ rootCalls rest from hc)
            · exact Or.inr ⟨d, cs, List.mem_cons_of_mem _ hd, hl, hnc⟩
        · rw [show pruneRoot live (Stmt.funDef m ps rs bd :: rest) =
            pruneRoot live rest from by simp only [pruneRoot, if_neg hm]] at hn
          rcases ih hn with hc | ⟨d, cs, hd, hl, hnc⟩
          · exact Or.inl (show n ∈ rootCalls rest from hc)
          · exact Or.inr ⟨d, cs, List.mem_cons_of_mem _ hd, hl, hnc⟩
      all_goals {
        rcases List.mem_append.mp
          (show n ∈ callNamesStmt _ ++ callNamesStmts (pruneRoot live rest)
            from hn) with hh | ht
        · exact Or.inl (List.mem_append.mpr (Or.inl hh))
        · rcases ih ht with hc | ⟨d, cs, hd, hl, hnc⟩
          · exact Or.inl (List.mem_append.mpr (Or.inr hc))
          · exact Or.inr ⟨d, cs, hd, hl, hnc⟩
      }

/-- The pruned root is `Good` for the dead set. -/
theorem good_pruneRoot (b : Block Op) :
    GoodSS (deadSet b) (pruneRoot (liveDefs b) b) := by
  intro n hn
  rcases callNames_pruneRoot hn with hc | ⟨d, cs, hd, hl, hnc⟩
  · exact not_deadSet_of_live (live_of_rootCalls hc)
  · exact good_body_of_live hd hl n hnc

/-- The hoisted-scope obligations of `PScopeRel` at the root. -/
theorem pscope_root (b : Block Op) :
    PScopeRel (calls := calls) (creates := creates) (deadSet b)
      (hoist D b) (hoist D (pruneRoot (liveDefs b) b)) := by
  constructor
  · left
    rw [hoist_pruneRoot]
    refine (List.filter_congr ?_).symm
    intro p hp
    by_cases hl : (liveDefs b).contains p.1
    · simp only [hl, List.contains_eq_mem]
      simp [not_deadSet_of_live hl]
    · have hdead : p.1 ∈ deadSet b := by
        refine List.mem_filter.mpr ⟨?_, by simpa using hl⟩
        have := hoist_name_defined (calls := calls) (creates := creates) hp
        obtain ⟨d, hd, he⟩ := List.any_eq_true.mp this
        exact List.mem_map.mpr ⟨d, hd, by simpa using he.symm⟩
      simp only [hl, List.contains_eq_mem]
      simp [hdead]
  · intro p hp hnr
    have hdefined := hoist_name_defined (calls := calls) (creates := creates) hp
    have hdef := rootDefs_of_hoist (calls := calls) (creates := creates) hp
    have hlive : (liveDefs b).contains p.1 := by
      refine live_of_not_deadSet ?_ (by simpa [List.contains_eq_mem] using hnr)
      obtain ⟨d, hd, he⟩ := List.any_eq_true.mp hdefined
      simp only [List.contains_eq_mem, decide_eq_true_eq]
      exact List.mem_map.mpr ⟨d, hd, by simpa using he⟩
    exact fun n hn => good_body_of_live hdef hlive n hn

set_option maxHeartbeats 800000 in
/-- **Soundness of unreachable-definition pruning.** -/
theorem pruneDefsBlock_sound (b : Block Op) :
    EquivBlock D b (pruneDefsBlock b) := by
  intro funs V st V' st' o
  have hrel : PFunsRel (calls := calls) (creates := creates) (deadSet b)
      (hoist D b :: funs) (hoist D (pruneRoot (liveDefs b) b) :: funs) :=
    ⟨[hoist D b], [hoist D (pruneRoot (liveDefs b) b)], funs, rfl, rfl,
      .cons (pscope_root b) .nil⟩
  constructor
  · intro h
    cases h with
    | block hb =>
        exact Step.block (Step.prune_congr
          (pruneRoot_fwd (live := liveDefs b) hb) hrel (good_pruneRoot b))
  · intro h
    cases h with
    | block hb =>
        exact Step.block (pruneRoot_bwd
          (Step.prune_congr_bwd hb hrel (good_pruneRoot b)))

end YulEvmCompiler.Optimizer.PruneDefs
