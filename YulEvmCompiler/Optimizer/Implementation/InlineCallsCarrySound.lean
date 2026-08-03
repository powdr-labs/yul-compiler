import YulEvmCompiler.Optimizer.Implementation.InlineCallsCarry
import YulEvmCompiler.Optimizer.Implementation.InlineCallsSound
import YulEvmCompiler.Optimizer.Implementation.FunCongr
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
/-!
# YulEvmCompiler.Optimizer.Implementation.InlineCallsCarrySound

Soundness of the call-carrying inliner (`InlineCallsCarry.lean`). **Partial:**
the `carry_transfer` engine below is proved; the full simulation that discharges
`inlineCallsCarry.sound` is not yet assembled (see the design note).

The architecture mirrors `InlineCallsSound`, with one change concentrated in
the callee-body transfer at an inline site. `InlineCalls` bodies are call-free,
so `scoped_transfer` moves the body's execution to *any* function environment
(it never consults `funs`). Carry bodies bear calls: the transplanted copy runs
its inner calls under the caller's function environment at the site, whereas the
original runs them under the callee's defining scope `cenv`. The move splits in
two:

1. **defining scope → site source** — `carry_transfer` (below), the analog of
   `scoped_transfer` that *permits* calls. It transfers execution to any
   function environment that **agrees** with the original on the code's
   (syntactic) call names, weakening the variable environment by an inert
   suffix. Agreement is exactly what the no-shadowing gate (`carrySurvives`)
   guarantees between the callee's defining scope and the rewrite site. This
   hop is proved and stays within the *source* function environment.

2. **site source → site target** — the transform rewrites the *rest* of the
   program too, so the site's target function environment `funs₂` has
   `cyBlock`-transformed function bodies. This hop is the callee-body's
   share of the whole-pass simulation and must be discharged the same way
   `InlineCallsSound` discharges an ordinary call: through the Δ-indexed
   relation carrying `DeltaCompat Δ cenv` (a *conditional* body equivalence),
   **not** `FunCongr.Step.funs_congr` — its `FunsRel` demands *unconditional*
   `EquivBlock` between a source body and its transform, which is **false**
   (at a `funs` where an inlined callee is undefined the source is stuck while
   `inlineCore` steps). For an *ordinary* call `InlineCallsSound` gets this from
   the `Step` induction hypothesis `ihbody`; at an inline **site** no such
   hypothesis is in scope, so hop 2 needs the simulation applied to the callee
   body via **structural recursion on program size** (`d.ss` is a strict
   subterm of the whole program). That size-recursive assembly — mirroring
   `IcRel`/`IcFunsRel`/`ic_fwd`/`ic_bwd` with the site cases using hop 1 plus
   the size IH — is the remaining work.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM

variable {calls : ExternalCalls} {creates : ExternalCreates}

local notation "D" => evmWithExternal calls creates

/-! ### Carry-scoped per-class checks (calls permitted) -/

/-- Per-class carry check for the transfer induction. -/
def carryArgs (bound : List Ident) : List (Expr Op) → Bool
  | [] => true
  | e :: rest => carryExpr bound e && carryArgs bound rest

/-- Per-class carry check for the transfer induction. -/
def carryCode (bound : List Ident) : Code Op → Bool
  | .expr e => carryExpr bound e
  | .args es => carryArgs bound es
  | .stmt s => (carryStmt bound s).isSome
  | .stmts ss => carryStmts bound ss
  | .loop _ _ _ => false

/-- The binding context the carry checker leaves after one statement. -/
def carryPostBound (bound : List Ident) : Code Op → List Ident
  | .stmt s => (carryStmt bound s).getD bound
  | _ => []

/-! ### Call-name collection per class (for the function-agreement side) -/

/-- The syntactic call names of a code class. -/
def carryCallNames : Code Op → List Ident
  | .expr e => exprCallNames e
  | .args es => argsCallNames es
  | .stmt s => stmtCallNames s
  | .stmts ss => stmtsCallNames ss
  | .loop _ _ _ => []

/-- Two function environments **agree** on a set of names when each resolves
identically under both. -/
def FunsAgree (funs₁ funs₂ : FunEnv D) (names : List Ident) : Prop :=
  ∀ g ∈ names, lookupFun funs₁ g = lookupFun funs₂ g

theorem FunsAgree.mono {funs₁ funs₂ : FunEnv D} {a b : List Ident}
    (h : FunsAgree (calls := calls) (creates := creates) funs₁ funs₂ b)
    (hsub : ∀ x ∈ a, x ∈ b) :
    FunsAgree (calls := calls) (creates := creates) funs₁ funs₂ a :=
  fun g hg => h g (hsub g hg)

/-- Agreement lifts through a common prepended **empty** scope (the only kind a
carry body introduces, since it has no `funDef`s): the empty scope resolves
nothing, so both sides recurse to the agreeing tails. -/
theorem FunsAgree.cons_nil {funs₁ funs₂ : FunEnv D} {names : List Ident}
    (h : FunsAgree (calls := calls) (creates := creates) funs₁ funs₂ names) :
    FunsAgree (calls := calls) (creates := creates) ([] :: funs₁) ([] :: funs₂) names := by
  intro g hg
  have e1 : lookupFun (([] : FScope D) :: funs₁) g = lookupFun funs₁ g := rfl
  have e2 : lookupFun (([] : FScope D) :: funs₂) g = lookupFun funs₂ g := rfl
  rw [e1, e2]; exact h g hg

/-- A carry-checked body has no top-level `funDef`, so it hoists nothing. -/
theorem carryStmts_hoist_nil {bound : List Ident} :
    ∀ {body : List (Stmt Op)}, carryStmts bound body = true → hoist D body = [] := by
  intro body
  induction body generalizing bound with
  | nil => intro _; rfl
  | cons s rest ih =>
      intro h
      unfold carryStmts at h
      cases hs : carryStmt bound s with
      | none => rw [hs] at h; exact absurd h (by simp)
      | some bound' =>
          rw [hs] at h
          cases s with
          | funDef n ps rs b => simp [carryStmt] at hs
          | block b => exact ih h
          | letDecl xs v => exact ih h
          | assign xs e => exact ih h
          | exprStmt e => exact ih h
          | cond c b => exact ih h
          | «switch» c cs d => exact ih h
          | forLoop i c p b => simp [carryStmt] at hs
          | «break» => simp [carryStmt] at hs
          | «continue» => simp [carryStmt] at hs
          | «leave» => simp [carryStmt] at hs

/-! ### Carry-scoped inversions -/

/-- Bound reads make an argument list carry-scoped (no call restriction). -/
theorem carryArgs_of_varsBound {bound : List Ident} {args : List (Expr Op)}
    (hv : (varsList args).all bound.contains = true) : carryArgs bound args = true := by
  induction args with
  | nil => rfl
  | cons e rest ih =>
      rw [show varsList (e :: rest) = exprVars e ++ varsList rest from rfl,
        List.all_append, Bool.and_eq_true] at hv
      unfold carryArgs
      rw [Bool.and_eq_true]
      exact ⟨by unfold carryExpr; exact hv.1, ih hv.2⟩

/-- A carry-scoped builtin's arguments are carry-scoped. -/
theorem carryExpr_builtin_args {bound : List Ident} {op : Op} {args : List (Expr Op)}
    (h : carryExpr bound (.builtin op args) = true) : carryArgs bound args = true := by
  unfold carryExpr at h
  exact carryArgs_of_varsBound (by simpa [exprVars] using h)

/-- A carry-scoped call's arguments are carry-scoped. -/
theorem carryExpr_call_args {bound : List Ident} {f : Ident} {args : List (Expr Op)}
    (h : carryExpr bound (.call f args) = true) : carryArgs bound args = true := by
  unfold carryExpr at h
  exact carryArgs_of_varsBound (by simpa [exprVars] using h)

/-- Split a carry sequence at its head. -/
theorem carryStmts_cons_inv {bound : List Ident} {s : Stmt Op} {rest : List (Stmt Op)}
    (h : carryStmts bound (s :: rest) = true) :
    ∃ bound₁, carryStmt bound s = some bound₁ ∧ carryStmts bound₁ rest = true := by
  unfold carryStmts at h
  split at h
  · next bound₁ heq => exact ⟨bound₁, heq, h⟩
  · cases h

/-- The selected switch block of carry-scoped cases/default is carry-scoped. -/
theorem carry_selectSwitch {bound : List Ident} {cv : U256}
    {cases : List (Literal × Block Op)} {dflt : Option (Block Op)}
    (hc : carryCases bound cases = true) (hd : carryDflt bound dflt = true) :
    carryStmts bound (selectSwitch D cv cases dflt) = true := by
  induction cases with
  | nil =>
      unfold selectSwitch
      simp only [List.find?_nil]
      cases dflt with
      | none => rfl
      | some b => exact hd
  | cons hd' rest ih =>
      rcases hd' with ⟨l, b⟩
      unfold carryCases at hc
      rw [Bool.and_eq_true] at hc
      by_cases hcv : cv = (evmWithExternal calls creates).litValue l
      · rw [selectSwitch, List.find?_cons_of_pos (by simp [hcv])]
        exact hc.1
      · rw [selectSwitch, List.find?_cons_of_neg (by simp [hcv])]
        have := ih hc.2
        rw [selectSwitch] at this
        exact this

/-- Call names of the selected switch block sit inside the cases'/default's. -/
theorem selectSwitch_callNames_sub {cv : U256}
    {cases : List (Literal × Block Op)} {dflt : Option (Block Op)} :
    ∀ g ∈ stmtsCallNames (selectSwitch D cv cases dflt),
      g ∈ casesCallNames cases ++ dfltCallNames dflt := by
  intro g hg
  induction cases with
  | nil =>
      simp only [selectSwitch, List.find?_nil] at hg
      cases dflt with
      | none => simp [stmtsCallNames] at hg
      | some b =>
          refine List.mem_append.mpr (Or.inr ?_)
          simpa [dfltCallNames] using hg
  | cons hd' rest ih =>
      rcases hd' with ⟨l, b⟩
      by_cases hcv : cv = (evmWithExternal calls creates).litValue l
      · rw [selectSwitch, List.find?_cons_of_pos (by simp [hcv])] at hg
        refine List.mem_append.mpr (Or.inl ?_)
        show g ∈ stmtsCallNames b ++ casesCallNames rest
        exact List.mem_append.mpr (Or.inl hg)
      · rw [selectSwitch, List.find?_cons_of_neg (by simp [hcv])] at hg
        have := ih (by rw [selectSwitch]; exact hg)
        rcases List.mem_append.mp this with h | h
        · exact List.mem_append.mpr (Or.inl (by
            show g ∈ stmtsCallNames b ++ casesCallNames rest
            exact List.mem_append.mpr (Or.inr h)))
        · exact List.mem_append.mpr (Or.inr h)

/-! ### The carry-transfer engine -/

/-- **The carry-transfer engine.** Carry code (calls permitted) transfers from
`funs₁, A ++ W` to any `funs₂, A ++ W'` that **agrees** with `funs₁` on the
code's call names, producing only `normal`/`halt` outcomes. Direct calls
resolve identically (agreement) and their bodies run under the shared captured
scope, so they are reused verbatim; the environment extension `W`/`W'` stays
inert below the checked part. -/
theorem carry_transfer {funs₁ : FunEnv D} {V₁ : VEnv D} {st : EvmState}
    {code : Code Op} {res₁ : Res D}
    (h : Step D funs₁ V₁ st code res₁) :
    ∀ {A W : VEnv D} {bound : List Ident} (funs₂ : FunEnv D) (W' : VEnv D),
      V₁ = A ++ W → carryCode bound code = true →
      (∀ x ∈ bound, x ∈ A.map Prod.fst) →
      FunsAgree (calls := calls) (creates := creates) funs₁ funs₂ (carryCallNames code) →
      ∃ res₂, Step D funs₂ (A ++ W') st code res₂ ∧
        TRes (calls := calls) (creates := creates) W W'
          (carryPostBound bound code) res₁ res₂ := by
  induction h with
  | @lit funs V st l =>
      intro A W bound funs₂ W' hV hsc hb hag
      exact ⟨_, Step.lit, .eres _⟩
  | @var funs V st x v hv =>
      intro A W bound funs₂ W' hV hsc hb hag
      subst hV
      have hx : x ∈ bound := by
        unfold carryCode carryExpr at hsc
        have := List.all_eq_true.mp hsc x (by simp [exprVars])
        simpa using this
      have hxA : x ∈ A.map Prod.fst := hb x hx
      have hgv : VEnv.get A x = some v := by
        rw [← VEnv.get_append_mem hxA W]; exact hv
      refine ⟨_, Step.var ?_, .eres _⟩
      rw [VEnv.get_append_mem hxA W']; exact hgv
  | @builtinOk funs V st op args argvals st1 rets st2 ha hbi iha =>
      intro A W bound funs₂ W' hV hsc hb hag
      have hargs : carryArgs bound args = true := carryExpr_builtin_args hsc
      obtain ⟨res₂, hstep, htr⟩ := iha funs₂ W' hV (by simp [carryCode, hargs])
        hb (by simpa [carryCallNames, exprCallNames] using hag)
      cases htr with
      | eres => exact ⟨_, Step.builtinOk hstep hbi, .eres _⟩
  | @builtinHalt funs V st op args argvals st1 st2 ha hbi iha =>
      intro A W bound funs₂ W' hV hsc hb hag
      have hargs : carryArgs bound args = true := carryExpr_builtin_args hsc
      obtain ⟨res₂, hstep, htr⟩ := iha funs₂ W' hV (by simp [carryCode, hargs])
        hb (by simpa [carryCallNames, exprCallNames] using hag)
      cases htr with
      | eres => exact ⟨_, Step.builtinHalt hstep hbi, .eres _⟩
  | @builtinArgsHalt funs V st op args st1 ha iha =>
      intro A W bound funs₂ W' hV hsc hb hag
      have hargs : carryArgs bound args = true := carryExpr_builtin_args hsc
      obtain ⟨res₂, hstep, htr⟩ := iha funs₂ W' hV (by simp [carryCode, hargs])
        hb (by simpa [carryCallNames, exprCallNames] using hag)
      cases htr with
      | eres => exact ⟨_, Step.builtinArgsHalt hstep, .eres _⟩
  | @callOk funs V st fn args argvals st1 decl cenv Vend st2 o ha hlk harity hbody ho iha ihbody =>
      intro A W bound funs₂ W' hV hsc hb hag
      have hargs : carryArgs bound args = true := carryExpr_call_args hsc
      have hagfn : lookupFun funs fn = lookupFun funs₂ fn :=
        hag fn (by simp [carryCallNames, exprCallNames])
      obtain ⟨res₂, hstep, htr⟩ := iha funs₂ W' hV (by simp [carryCode, hargs])
        hb (by
          refine hag.mono ?_
          intro y hy
          show y ∈ carryCallNames (Code.expr (.call fn args))
          simp only [carryCallNames, exprCallNames]
          exact List.mem_cons_of_mem fn (by simpa [carryCallNames] using hy))
      cases htr with
      | eres =>
          refine ⟨_, Step.callOk hstep ?_ harity hbody ho, .eres _⟩
          rw [← hagfn]; exact hlk
  | @callHalt funs V st fn args argvals st1 decl cenv Vend st2 ha hlk harity hbody iha ihbody =>
      intro A W bound funs₂ W' hV hsc hb hag
      have hargs : carryArgs bound args = true := carryExpr_call_args hsc
      have hagfn : lookupFun funs fn = lookupFun funs₂ fn :=
        hag fn (by simp [carryCallNames, exprCallNames])
      obtain ⟨res₂, hstep, htr⟩ := iha funs₂ W' hV (by simp [carryCode, hargs])
        hb (by
          refine hag.mono ?_
          intro y hy
          show y ∈ carryCallNames (Code.expr (.call fn args))
          simp only [carryCallNames, exprCallNames]
          exact List.mem_cons_of_mem fn (by simpa [carryCallNames] using hy))
      cases htr with
      | eres =>
          refine ⟨_, Step.callHalt hstep ?_ harity hbody, .eres _⟩
          rw [← hagfn]; exact hlk
  | @callArgsHalt funs V st fn args st1 ha iha =>
      intro A W bound funs₂ W' hV hsc hb hag
      have hargs : carryArgs bound args = true := carryExpr_call_args hsc
      obtain ⟨res₂, hstep, htr⟩ := iha funs₂ W' hV (by simp [carryCode, hargs])
        hb (by
          refine hag.mono ?_
          intro y hy
          show y ∈ carryCallNames (Code.expr (.call fn args))
          simp only [carryCallNames, exprCallNames]
          exact List.mem_cons_of_mem fn (by simpa [carryCallNames] using hy))
      cases htr with
      | eres => exact ⟨_, Step.callArgsHalt hstep, .eres _⟩
  | @argsNil funs V st =>
      intro A W bound funs₂ W' hV hsc hb hag
      exact ⟨_, Step.argsNil, .eres _⟩
  | @argsCons funs V st e rest restvals st1 v st2 hrest he ihrest ihe =>
      intro A W bound funs₂ W' hV hsc hb hag
      unfold carryCode carryArgs at hsc
      rw [Bool.and_eq_true] at hsc
      have hagE : FunsAgree (calls := calls) (creates := creates) funs funs₂ (exprCallNames e) :=
        hag.mono (fun y hy => by
          show y ∈ argsCallNames (e :: rest)
          exact List.mem_append.mpr (Or.inl hy))
      have hagR : FunsAgree (calls := calls) (creates := creates) funs funs₂ (argsCallNames rest) :=
        hag.mono (fun y hy => by
          show y ∈ argsCallNames (e :: rest)
          exact List.mem_append.mpr (Or.inr hy))
      obtain ⟨res₂, hstep₁, htr₁⟩ := ihrest funs₂ W' hV (by simp [carryCode, hsc.2]) hb hagR
      obtain ⟨res₃, hstep₂, htr₂⟩ := ihe funs₂ W' hV (by simp [carryCode, hsc.1]) hb hagE
      cases htr₁ with
      | eres =>
          cases htr₂ with
          | eres => exact ⟨_, Step.argsCons hstep₁ hstep₂, .eres _⟩
  | @argsRestHalt funs V st e rest st1 hrest ihrest =>
      intro A W bound funs₂ W' hV hsc hb hag
      unfold carryCode carryArgs at hsc
      rw [Bool.and_eq_true] at hsc
      have hagR : FunsAgree (calls := calls) (creates := creates) funs funs₂ (argsCallNames rest) :=
        hag.mono (fun y hy => by
          show y ∈ argsCallNames (e :: rest)
          exact List.mem_append.mpr (Or.inr hy))
      obtain ⟨res₂, hstep₁, htr₁⟩ := ihrest funs₂ W' hV (by simp [carryCode, hsc.2]) hb hagR
      cases htr₁ with
      | eres => exact ⟨_, Step.argsRestHalt hstep₁, .eres _⟩
  | @argsHeadHalt funs V st e rest restvals st1 st2 hrest he ihrest ihe =>
      intro A W bound funs₂ W' hV hsc hb hag
      unfold carryCode carryArgs at hsc
      rw [Bool.and_eq_true] at hsc
      have hagE : FunsAgree (calls := calls) (creates := creates) funs funs₂ (exprCallNames e) :=
        hag.mono (fun y hy => by
          show y ∈ argsCallNames (e :: rest)
          exact List.mem_append.mpr (Or.inl hy))
      have hagR : FunsAgree (calls := calls) (creates := creates) funs funs₂ (argsCallNames rest) :=
        hag.mono (fun y hy => by
          show y ∈ argsCallNames (e :: rest)
          exact List.mem_append.mpr (Or.inr hy))
      obtain ⟨res₂, hstep₁, htr₁⟩ := ihrest funs₂ W' hV (by simp [carryCode, hsc.2]) hb hagR
      obtain ⟨res₃, hstep₂, htr₂⟩ := ihe funs₂ W' hV (by simp [carryCode, hsc.1]) hb hagE
      cases htr₁ with
      | eres =>
          cases htr₂ with
          | eres => exact ⟨_, Step.argsHeadHalt hstep₁ hstep₂, .eres _⟩
  | funDef =>
      intro A W bound funs₂ W' hV hsc hb hag
      simp [carryCode, carryStmt] at hsc
  | @block funs V st body Vb stb o hbody ihbody =>
      intro A W bound funs₂ W' hV hsc hb hag
      subst hV
      have hstmts : carryStmts bound body = true := by
        simp only [carryCode, carryStmt] at hsc
        by_cases hc : carryStmts bound body = true
        · exact hc
        · simp [hc] at hsc
      have hpost : carryPostBound bound (Code.stmt (.block body)) = bound := by
        simp [carryPostBound, carryStmt, hstmts]
      have hhoist : hoist D body = [] := carryStmts_hoist_nil hstmts
      have hagb : FunsAgree (calls := calls) (creates := creates)
          (hoist D body :: funs) (hoist D body :: funs₂) (carryCallNames (.stmts body)) := by
        rw [hhoist]
        exact FunsAgree.cons_nil (by simpa [carryCallNames, stmtCallNames] using hag)
      obtain ⟨res₂, hstep, htr⟩ :=
        ihbody (hoist D body :: funs₂) W' rfl hstmts hb hagb
      have hlenV : (A ++ W).length ≤ Vb.length := venvLen_mono hbody rfl
      have hkeysV := venvKeys_suffix hbody rfl
      cases htr with
      | @norm A' st' hk =>
          have hlen : A.length ≤ A'.length := by
            rw [List.length_append, List.length_append] at hlenV
            omega
          refine ⟨_, Step.block hstep, ?_⟩
          rw [hpost, restore_append hlen, restore_append hlen]
          exact .norm (fun x hx => by
            rw [restore_keys (keys_suffix_cancel hkeysV) hlen]
            exact hb x hx)
      | @halt A' st' =>
          have hlen : A.length ≤ A'.length := by
            rw [List.length_append, List.length_append] at hlenV
            omega
          refine ⟨_, Step.block hstep, ?_⟩
          rw [restore_append hlen, restore_append hlen]
          exact .halt
  | @letZero funs V st vars =>
      intro A W bound funs₂ W' hV hsc hb hag
      subst hV
      refine ⟨_, Step.letZero, ?_⟩
      rw [show bindZeros D vars ++ (A ++ W) = (bindZeros D vars ++ A) ++ W from
            (List.append_assoc _ _ _).symm,
          show bindZeros D vars ++ (A ++ W') = (bindZeros D vars ++ A) ++ W' from
            (List.append_assoc _ _ _).symm]
      refine .norm (fun x hx => ?_)
      have hpost : carryPostBound bound (Code.stmt (.letDecl vars none)) = vars ++ bound := by
        simp [carryPostBound, carryStmt]
      rw [hpost] at hx
      rw [List.map_append, bindZeros_keys]
      rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_append.mpr (Or.inl hx)
      · exact List.mem_append.mpr (Or.inr (hb x hx))
  | @letVal funs V st vars e vals st1 he hlen ihe =>
      intro A W bound funs₂ W' hV hsc hb hag
      subst hV
      have hse : carryExpr bound e = true := by
        simp only [carryCode, carryStmt] at hsc
        by_cases hc : carryExpr bound e = true
        · exact hc
        · simp [hc] at hsc
      obtain ⟨res₂, hstep, htr⟩ := ihe funs₂ W' rfl hse hb
        (by simpa [carryCallNames, stmtCallNames] using hag)
      cases htr with
      | eres =>
          refine ⟨_, Step.letVal hstep hlen, ?_⟩
          rw [show vars.zip vals ++ (A ++ W) = (vars.zip vals ++ A) ++ W from
                (List.append_assoc _ _ _).symm,
              show vars.zip vals ++ (A ++ W') = (vars.zip vals ++ A) ++ W' from
                (List.append_assoc _ _ _).symm]
          refine .norm (fun x hx => ?_)
          have hpost : carryPostBound bound (Code.stmt (.letDecl vars (some e))) =
              vars ++ bound := by
            simp [carryPostBound, carryStmt, hse]
          rw [hpost] at hx
          rw [List.map_append, List.map_fst_zip (by omega)]
          rcases List.mem_append.mp hx with hx | hx
          · exact List.mem_append.mpr (Or.inl hx)
          · exact List.mem_append.mpr (Or.inr (hb x hx))
  | @letHalt funs V st vars e st1 he ihe =>
      intro A W bound funs₂ W' hV hsc hb hag
      subst hV
      have hse : carryExpr bound e = true := by
        simp only [carryCode, carryStmt] at hsc
        by_cases hc : carryExpr bound e = true
        · exact hc
        · simp [hc] at hsc
      obtain ⟨res₂, hstep, htr⟩ := ihe funs₂ W' rfl hse hb
        (by simpa [carryCallNames, stmtCallNames] using hag)
      cases htr with
      | eres => exact ⟨_, Step.letHalt hstep, .halt⟩
  | @assignVal funs V st vars e vals st1 he hlen ihe =>
      intro A W bound funs₂ W' hV hsc hb hag
      subst hV
      have hsc' : vars.all bound.contains = true ∧ carryExpr bound e = true := by
        simp only [carryCode, carryStmt] at hsc
        by_cases hc : (vars.all bound.contains && carryExpr bound e) = true
        · rw [Bool.and_eq_true] at hc
          exact hc
        · simp [hc] at hsc
      have hvars : ∀ x ∈ vars, x ∈ A.map Prod.fst := fun x hx =>
        hb x (all_contains_subset hsc'.1 x hx)
      obtain ⟨res₂, hstep, htr⟩ := ihe funs₂ W' rfl hsc'.2 hb
        (by simpa [carryCallNames, stmtCallNames] using hag)
      cases htr with
      | eres =>
          refine ⟨_, Step.assignVal hstep hlen, ?_⟩
          rw [VEnv.setMany_append_mem hvars, VEnv.setMany_append_mem hvars]
          refine .norm (fun x hx => ?_)
          have hpost : carryPostBound bound (Code.stmt (.assign vars e)) = bound := by
            simp [carryPostBound, carryStmt, hsc'.1, hsc'.2]
          rw [hpost] at hx
          rw [VEnv.setMany_keys («D» := D)]
          exact hb x hx
  | @assignHalt funs V st vars e st1 he ihe =>
      intro A W bound funs₂ W' hV hsc hb hag
      subst hV
      have hse : carryExpr bound e = true := by
        simp only [carryCode, carryStmt] at hsc
        by_cases hc : (vars.all bound.contains && carryExpr bound e) = true
        · rw [Bool.and_eq_true] at hc
          exact hc.2
        · simp [hc] at hsc
      obtain ⟨res₂, hstep, htr⟩ := ihe funs₂ W' rfl hse hb
        (by simpa [carryCallNames, stmtCallNames] using hag)
      cases htr with
      | eres => exact ⟨_, Step.assignHalt hstep, .halt⟩
  | @exprStmt funs V st e st1 he ihe =>
      intro A W bound funs₂ W' hV hsc hb hag
      subst hV
      have hse : carryExpr bound e = true := by
        simp only [carryCode, carryStmt] at hsc
        by_cases hc : carryExpr bound e = true
        · exact hc
        · simp [hc] at hsc
      obtain ⟨res₂, hstep, htr⟩ := ihe funs₂ W' rfl hse hb
        (by simpa [carryCallNames, stmtCallNames] using hag)
      cases htr with
      | eres =>
          refine ⟨_, Step.exprStmt hstep, ?_⟩
          refine .norm (fun x hx => ?_)
          have hpost : carryPostBound bound (Code.stmt (.exprStmt e)) = bound := by
            simp [carryPostBound, carryStmt, hse]
          rw [hpost] at hx
          exact hb x hx
  | @exprStmtHalt funs V st e st1 he ihe =>
      intro A W bound funs₂ W' hV hsc hb hag
      subst hV
      have hse : carryExpr bound e = true := by
        simp only [carryCode, carryStmt] at hsc
        by_cases hc : carryExpr bound e = true
        · exact hc
        · simp [hc] at hsc
      obtain ⟨res₂, hstep, htr⟩ := ihe funs₂ W' rfl hse hb
        (by simpa [carryCallNames, stmtCallNames] using hag)
      cases htr with
      | eres => exact ⟨_, Step.exprStmtHalt hstep, .halt⟩
  | @ifTrue funs V st c body cv st1 V' st2 o hc hcv hbody ihc ihbody =>
      intro A W bound funs₂ W' hV hsc hb hag
      subst hV
      have hsc' : carryExpr bound c = true ∧ carryStmts bound body = true := by
        simp only [carryCode, carryStmt] at hsc
        by_cases hcnd : (carryExpr bound c && carryStmts bound body) = true
        · rw [Bool.and_eq_true] at hcnd
          exact hcnd
        · simp [hcnd] at hsc
      have hagc : FunsAgree (calls := calls) (creates := creates) funs funs₂ (exprCallNames c) :=
        hag.mono (fun y hy => by
          show y ∈ stmtCallNames (.cond c body)
          exact List.mem_append.mpr (Or.inl hy))
      have hagb : FunsAgree (calls := calls) (creates := creates) funs funs₂
          (carryCallNames (.stmt (.block body))) :=
        hag.mono (fun y hy => by
          show y ∈ stmtCallNames (.cond c body)
          exact List.mem_append.mpr (Or.inr (by simpa [carryCallNames, stmtCallNames] using hy)))
      obtain ⟨res₂, hstepc, htrc⟩ := ihc funs₂ W' rfl hsc'.1 hb hagc
      have hscb : carryCode bound (Code.stmt (.block body)) = true := by
        simp [carryCode, carryStmt, hsc'.2]
      obtain ⟨res₃, hstepb, htrb⟩ := ihbody funs₂ W' rfl hscb hb hagb
      cases htrc with
      | eres =>
          have hpostb : carryPostBound bound (Code.stmt (.block body)) = bound := by
            simp [carryPostBound, carryStmt, hsc'.2]
          have hpost : carryPostBound bound (Code.stmt (.cond c body)) = bound := by
            simp [carryPostBound, carryStmt, hsc'.1, hsc'.2]
          rw [hpostb] at htrb
          rw [hpost]
          cases htrb with
          | norm hk => exact ⟨_, Step.ifTrue hstepc hcv hstepb, .norm hk⟩
          | halt => exact ⟨_, Step.ifTrue hstepc hcv hstepb, .halt⟩
  | @ifFalse funs V st c body cv st1 hc hcv ihc =>
      intro A W bound funs₂ W' hV hsc hb hag
      subst hV
      have hcnd : (carryExpr bound c && carryStmts bound body) = true := by
        simp only [carryCode, carryStmt] at hsc
        by_cases hcnd : (carryExpr bound c && carryStmts bound body) = true
        · exact hcnd
        · simp [hcnd] at hsc
      have hsc' : carryExpr bound c = true := by
        rw [Bool.and_eq_true] at hcnd
        exact hcnd.1
      have hagc : FunsAgree (calls := calls) (creates := creates) funs funs₂ (exprCallNames c) :=
        hag.mono (fun y hy => by
          show y ∈ stmtCallNames (.cond c body)
          exact List.mem_append.mpr (Or.inl hy))
      obtain ⟨res₂, hstepc, htrc⟩ := ihc funs₂ W' rfl hsc' hb hagc
      cases htrc with
      | eres =>
          refine ⟨_, Step.ifFalse hstepc hcv, .norm (fun x hx => ?_)⟩
          exact hb x (by
            simpa [carryPostBound, carryStmt, hcnd] using hx)
  | @ifHalt funs V st c body st1 hc ihc =>
      intro A W bound funs₂ W' hV hsc hb hag
      subst hV
      have hsc' : carryExpr bound c = true := by
        simp only [carryCode, carryStmt] at hsc
        by_cases hcnd : (carryExpr bound c && carryStmts bound body) = true
        · rw [Bool.and_eq_true] at hcnd
          exact hcnd.1
        · simp [hcnd] at hsc
      have hagc : FunsAgree (calls := calls) (creates := creates) funs funs₂ (exprCallNames c) :=
        hag.mono (fun y hy => by
          show y ∈ stmtCallNames (.cond c body)
          exact List.mem_append.mpr (Or.inl hy))
      obtain ⟨res₂, hstepc, htrc⟩ := ihc funs₂ W' rfl hsc' hb hagc
      cases htrc with
      | eres => exact ⟨_, Step.ifHalt hstepc, .halt⟩
  | @switchExec funs V st c cases' dflt cv st1 V' st2 o hc hsel ihc ihsel =>
      intro A W bound funs₂ W' hV hsc hb hag
      subst hV
      have hsc' : carryExpr bound c = true ∧ carryCases bound cases' = true ∧
          carryDflt bound dflt = true := by
        simp only [carryCode, carryStmt] at hsc
        by_cases hcnd : (carryExpr bound c && carryCases bound cases' &&
            carryDflt bound dflt) = true
        · rw [Bool.and_eq_true, Bool.and_eq_true] at hcnd
          exact ⟨hcnd.1.1, hcnd.1.2, hcnd.2⟩
        · simp [hcnd] at hsc
      have hagc : FunsAgree (calls := calls) (creates := creates) funs funs₂ (exprCallNames c) :=
        hag.mono (fun y hy => by
          show y ∈ stmtCallNames (.switch c cases' dflt)
          exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hy))))
      have hagsel : FunsAgree (calls := calls) (creates := creates) funs funs₂
          (carryCallNames (.stmt (.block (selectSwitch D cv cases' dflt)))) := by
        refine hag.mono (fun y hy => ?_)
        show y ∈ stmtCallNames (.switch c cases' dflt)
        have hsub := selectSwitch_callNames_sub (calls := calls) (creates := creates)
          (cv := cv) (cases := cases') (dflt := dflt) y
          (by simpa [carryCallNames, stmtCallNames] using hy)
        rcases List.mem_append.mp hsub with hh | hh
        · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hh)))
        · exact List.mem_append.mpr (Or.inr hh)
      obtain ⟨res₂, hstepc, htrc⟩ := ihc funs₂ W' rfl hsc'.1 hb hagc
      have hsels : carryStmts bound (selectSwitch D cv cases' dflt) = true :=
        carry_selectSwitch hsc'.2.1 hsc'.2.2
      have hscb : carryCode bound (Code.stmt (.block (selectSwitch D cv cases' dflt))) =
          true := by
        simp [carryCode, carryStmt, hsels]
      obtain ⟨res₃, hstepb, htrb⟩ := ihsel funs₂ W' rfl hscb hb hagsel
      cases htrc with
      | eres =>
          have hpostb : carryPostBound bound
              (Code.stmt (.block (selectSwitch D cv cases' dflt))) = bound := by
            simp [carryPostBound, carryStmt, hsels]
          have hpost : carryPostBound bound (Code.stmt (.switch c cases' dflt)) = bound := by
            simp [carryPostBound, carryStmt, hsc'.1, hsc'.2.1, hsc'.2.2]
          rw [hpostb] at htrb
          rw [hpost]
          cases htrb with
          | norm hk => exact ⟨_, Step.switchExec hstepc hstepb, .norm hk⟩
          | halt => exact ⟨_, Step.switchExec hstepc hstepb, .halt⟩
  | @switchHalt funs V st c cases' dflt st1 hc ihc =>
      intro A W bound funs₂ W' hV hsc hb hag
      subst hV
      have hsc' : carryExpr bound c = true := by
        simp only [carryCode, carryStmt] at hsc
        by_cases hcnd : (carryExpr bound c && carryCases bound cases' &&
            carryDflt bound dflt) = true
        · rw [Bool.and_eq_true, Bool.and_eq_true] at hcnd
          exact hcnd.1.1
        · simp [hcnd] at hsc
      have hagc : FunsAgree (calls := calls) (creates := creates) funs funs₂ (exprCallNames c) :=
        hag.mono (fun y hy => by
          show y ∈ stmtCallNames (.switch c cases' dflt)
          exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hy))))
      obtain ⟨res₂, hstepc, htrc⟩ := ihc funs₂ W' rfl hsc' hb hagc
      cases htrc with
      | eres => exact ⟨_, Step.switchHalt hstepc, .halt⟩
  | forLoop | forInitHalt =>
      intro A W bound funs₂ W' hV hsc hb hag
      simp [carryCode, carryStmt] at hsc
  | «break» =>
      intro A W bound funs₂ W' hV hsc hb hag
      simp [carryCode, carryStmt] at hsc
  | «continue» =>
      intro A W bound funs₂ W' hV hsc hb hag
      simp [carryCode, carryStmt] at hsc
  | «leave» =>
      intro A W bound funs₂ W' hV hsc hb hag
      simp [carryCode, carryStmt] at hsc
  | @seqNil funs V st =>
      intro A W bound funs₂ W' hV hsc hb hag
      subst hV
      exact ⟨_, Step.seqNil, .norm (fun x hx => by simp [carryPostBound] at hx)⟩
  | @seqCons funs V st s rest V1 st1 V2 st2 o hs hrest ihs ihrest =>
      intro A W bound funs₂ W' hV hsc hb hag
      subst hV
      obtain ⟨bound₁, hstmt, hrest'⟩ := carryStmts_cons_inv hsc
      have hags : FunsAgree (calls := calls) (creates := creates) funs funs₂ (stmtCallNames s) :=
        hag.mono (fun y hy => by
          show y ∈ stmtsCallNames (s :: rest)
          exact List.mem_append.mpr (Or.inl hy))
      have hagr : FunsAgree (calls := calls) (creates := creates) funs funs₂ (stmtsCallNames rest) :=
        hag.mono (fun y hy => by
          show y ∈ stmtsCallNames (s :: rest)
          exact List.mem_append.mpr (Or.inr hy))
      obtain ⟨res₂, hstep₁, htr₁⟩ := ihs funs₂ W' rfl (by simp [carryCode, hstmt])
        hb (by simpa [carryCallNames] using hags)
      have hpost₁ : carryPostBound bound (Code.stmt s) = bound₁ := by
        simp [carryPostBound, hstmt]
      rw [hpost₁] at htr₁
      cases htr₁ with
      | @norm A₁ st₁' hk =>
          obtain ⟨res₃, hstep₂, htr₂⟩ := ihrest funs₂ W' rfl hrest' hk
            (by simpa [carryCallNames] using hagr)
          cases htr₂ with
          | norm hk₂ => exact ⟨_, Step.seqCons hstep₁ hstep₂, .norm hk₂⟩
          | halt => exact ⟨_, Step.seqCons hstep₁ hstep₂, .halt⟩
  | @seqStop funs V st s rest V1 st1 o hs hne ihs =>
      intro A W bound funs₂ W' hV hsc hb hag
      subst hV
      obtain ⟨bound₁, hstmt, hrest'⟩ := carryStmts_cons_inv hsc
      have hags : FunsAgree (calls := calls) (creates := creates) funs funs₂ (stmtCallNames s) :=
        hag.mono (fun y hy => by
          show y ∈ stmtsCallNames (s :: rest)
          exact List.mem_append.mpr (Or.inl hy))
      obtain ⟨res₂, hstep₁, htr₁⟩ := ihs funs₂ W' rfl (by simp [carryCode, hstmt])
        hb (by simpa [carryCallNames] using hags)
      cases htr₁ with
      | norm hk => exact absurd rfl hne
      | halt => exact ⟨_, Step.seqStop hstep₁ (by simp), .halt⟩
  | loopDone | loopCondHalt | loopStep | loopPostHalt | loopBreak | loopLeave
  | loopBodyHalt =>
      intro A W bound funs₂ W' hV hsc hb hag
      simp [carryCode] at hsc

/-! ### Classification inversions (carry) -/

/-- `carryClassifyDecl` unpacked. -/
theorem carryClassifyDecl_inv {f : Ident} {ps rs : List Ident} {body : Block Op}
    {d : IDecl} (h : carryClassifyDecl f ps rs body = some d) :
    d.ps = ps ∧ d.rs = rs ∧ (ps ++ rs).Nodup ∧
    carryStmts (ps ++ rs) d.ss = true ∧
    (body = d.ss ∨ body = d.ss ++ [.leave]) := by
  simp only [carryClassifyDecl] at h
  split at h
  · exact absurd h (by simp)
  · next hplain =>
      split at h
      · next hc =>
          rw [Bool.and_eq_true] at hc
          split at h
          · next hcl =>
              injection h with h
              subst h
              refine ⟨rfl, rfl, by simpa using hc.1, hc.2, ?_⟩
              unfold dropTrailingLeave
              split
              · next hlast =>
                  right
                  have hne : body ≠ [] := by
                    intro he; rw [he] at hlast; cases hlast
                  have hgl : body.getLast hne = .leave := by
                    rw [List.getLast?_eq_some_getLast hne] at hlast
                    injection hlast
                  rw [← hgl]
                  exact (List.dropLast_append_getLast hne).symm
              · left; rfl
          · exact absurd h (by simp)
      · exact absurd h (by simp)

/-- Entries produced by `carryHoistDecls` carry names outside `seen`. -/
theorem carryHoistDecls_not_seen {seen : List Ident} : ∀ {body : List (Stmt Op)}
    {p : Ident × IDecl}, p ∈ carryHoistDecls seen body → p.1 ∉ seen := by
  intro body
  induction body generalizing seen with
  | nil => intro p hp; cases hp
  | cons s rest ih =>
      intro p hp
      cases s with
      | funDef f ps rs fbody =>
          unfold carryHoistDecls at hp
          split at hp
          · exact ih hp
          · next hseen =>
              split at hp
              · rcases List.mem_cons.mp hp with rfl | hp
                · simpa using hseen
                · have := ih hp
                  intro hmem
                  exact this (List.mem_cons_of_mem _ hmem)
              · have := ih hp
                intro hmem
                exact this (List.mem_cons_of_mem _ hmem)
      | block body => exact ih hp
      | letDecl xs v => exact ih hp
      | assign xs e => exact ih hp
      | exprStmt e => exact ih hp
      | cond c body => exact ih hp
      | «switch» c cases dflt => exact ih hp
      | forLoop init c post body => exact ih hp
      | «break» => exact ih hp
      | «continue» => exact ih hp
      | «leave» => exact ih hp

/-- A `carryHoistDecls` entry is found by `find?` on the hoisted scope, at a
declaration it classified. -/
theorem carryHoistDecls_find {seen : List Ident} : ∀ {body : List (Stmt Op)}
    {f : Ident} {d : IDecl}, (f, d) ∈ carryHoistDecls seen body →
    ∃ ps rs fbody, (hoist D body).find? (fun p => p.1 = f) =
        some (f, ⟨ps, rs, fbody⟩) ∧ carryClassifyDecl f ps rs fbody = some d := by
  intro body
  induction body generalizing seen with
  | nil => intro f d hp; cases hp
  | cons s rest ih =>
      intro f d hp
      cases s with
      | funDef g ps rs fbody =>
          rw [show hoist D (.funDef g ps rs fbody :: rest) =
            (g, ⟨ps, rs, fbody⟩) :: hoist D rest from rfl]
          unfold carryHoistDecls at hp
          split at hp
          · next hseen =>
              have hne : f ≠ g := by
                intro he
                have := carryHoistDecls_not_seen hp
                rw [he] at this
                exact this (by simpa using hseen)
              rw [List.find?_cons_of_neg (by simpa using Ne.symm hne)]
              exact ih hp
          · next hseen =>
              split at hp
              · next d' hcl =>
                  rcases List.mem_cons.mp hp with heq | hp
                  · injection heq with h1 h2
                    subst h1
                    rw [List.find?_cons_of_pos (by simp)]
                    exact ⟨ps, rs, fbody, rfl, h2 ▸ hcl⟩
                  · have hne : f ≠ g := by
                      intro he
                      have := carryHoistDecls_not_seen hp
                      rw [he] at this
                      exact this (List.mem_cons_self ..)
                    rw [List.find?_cons_of_neg (by simpa using Ne.symm hne)]
                    exact ih hp
              · have hne : f ≠ g := by
                  intro he
                  have := carryHoistDecls_not_seen hp
                  rw [he] at this
                  exact this (List.mem_cons_self ..)
                rw [List.find?_cons_of_neg (by simpa using Ne.symm hne)]
                exact ih hp
      | block body =>
          rw [show hoist D (.block body :: rest) = hoist D rest from rfl]
          exact ih hp
      | letDecl xs v =>
          rw [show hoist D (.letDecl xs v :: rest) = hoist D rest from rfl]
          exact ih hp
      | assign xs e =>
          rw [show hoist D (.assign xs e :: rest) = hoist D rest from rfl]
          exact ih hp
      | exprStmt e =>
          rw [show hoist D (.exprStmt e :: rest) = hoist D rest from rfl]
          exact ih hp
      | cond c body =>
          rw [show hoist D (.cond c body :: rest) = hoist D rest from rfl]
          exact ih hp
      | «switch» c cases dflt =>
          rw [show hoist D (.switch c cases dflt :: rest) = hoist D rest from rfl]
          exact ih hp
      | forLoop init c post body =>
          rw [show hoist D (.forLoop init c post body :: rest) =
            hoist D rest from rfl]
          exact ih hp
      | «break» =>
          rw [show hoist D (.break :: rest) = hoist D rest from rfl]
          exact ih hp
      | «continue» =>
          rw [show hoist D (.continue :: rest) = hoist D rest from rfl]
          exact ih hp
      | «leave» =>
          rw [show hoist D (.leave :: rest) = hoist D rest from rfl]
          exact ih hp

/-! ### Carry well-formedness of the declaration context -/

/-- Every tracked declaration is carry-classified: distinct parameter/return
names and a carry-scoped body. -/
def CarryWF (Δ : DEnv) : Prop :=
  ∀ p ∈ Δ, (p.2.ps ++ p.2.rs).Nodup ∧
    carryStmts (p.2.ps ++ p.2.rs) p.2.ss = true

/-- `carryHoistDecls` only produces carry-classified declarations. -/
theorem carryHoistDecls_wf {seen : List Ident} : ∀ {body : List (Stmt Op)}
    {p : Ident × IDecl}, p ∈ carryHoistDecls seen body →
    (p.2.ps ++ p.2.rs).Nodup ∧ carryStmts (p.2.ps ++ p.2.rs) p.2.ss = true := by
  intro body
  induction body generalizing seen with
  | nil => intro p hp; cases hp
  | cons s rest ih =>
      intro p hp
      cases s with
      | funDef f ps rs fbody =>
          unfold carryHoistDecls at hp
          split at hp
          · exact ih hp
          · split at hp
            · next d hcl =>
                rcases List.mem_cons.mp hp with rfl | hp
                · obtain ⟨hps, hrs, hnd, hsc, -⟩ := carryClassifyDecl_inv hcl
                  refine ⟨?_, ?_⟩
                  · show (d.ps ++ d.rs).Nodup
                    rw [hps, hrs]; exact hnd
                  · show carryStmts (d.ps ++ d.rs) d.ss = true
                    rw [hps, hrs]; exact hsc
                · exact ih hp
            · exact ih hp
      | block body => exact ih hp
      | letDecl xs v => exact ih hp
      | assign xs e => exact ih hp
      | exprStmt e => exact ih hp
      | cond c body => exact ih hp
      | «switch» c cases dflt => exact ih hp
      | forLoop init c post body => exact ih hp
      | «break» => exact ih hp
      | «continue» => exact ih hp
      | «leave» => exact ih hp

/-- `carryDeltaExtend` preserves carry well-formedness. -/
theorem CarryWF.extend {Δ : DEnv} (h : CarryWF Δ) (body : List (Stmt Op)) :
    CarryWF (carryDeltaExtend Δ body) := by
  intro p hp
  unfold carryDeltaExtend at hp
  rcases List.mem_append.mp hp with hp | hp
  · exact carryHoistDecls_wf hp
  · exact h p (List.mem_filter.mp hp).1

/-- Pruning preserves carry well-formedness. -/
theorem CarryWF.filter {Δ : DEnv} (h : CarryWF Δ) (q : Ident × IDecl → Bool) :
    CarryWF (Δ.filter q) :=
  fun p hp => h p (List.mem_filter.mp hp).1

/-- The empty declaration context is carry well-formed. -/
theorem CarryWF.nil : CarryWF ([] : DEnv) :=
  fun p hp => absurd hp (List.not_mem_nil)

/-! ### Declaration-context compatibility (with the carried-name invariant) -/

/-- Every tracked declaration resolves, via `lookupFun`, to a declaration whose
signature matches and whose body is the tracked one up to a trailing `leave`;
**and** every name the body carries a call to resolves at the *ambient* scope
exactly as at the callee's captured *defining* scope. The last conjunct is the
no-shadowing invariant `carrySurvives` maintains — it is what lets the
transplanted body's inner calls agree between the two scopes. -/
def CarryCompat (Δ : DEnv) (funs : FunEnv D) : Prop :=
  ∀ p ∈ Δ, ∃ body₀ cenv,
    lookupFun funs p.1 = some (⟨p.2.ps, p.2.rs, body₀⟩, cenv) ∧
    (body₀ = p.2.ss ∨ body₀ = p.2.ss ++ [.leave]) ∧
    (∀ g ∈ stmtsCallNames p.2.ss, lookupFun funs g = lookupFun cenv g)

theorem CarryCompat.nil (funs : FunEnv D) :
    CarryCompat (calls := calls) (creates := creates) [] funs :=
  fun p hp => absurd hp (List.not_mem_nil)

/-- Ambient lookup below a block ignores names the block does not define. -/
theorem lookupFun_cons_hoist_not_mem {f : Ident} {body : List (Stmt Op)}
    {funs : FunEnv D} (hnf : f ∉ definedFuns body) :
    lookupFun (hoist D body :: funs) f = lookupFun funs f := by
  have hn : (hoist D body).find? (fun p => p.1 = f) = none :=
    hoist_find_none (by simpa using hnf)
  simp only [lookupFun, hn]

/-- Entering a block preserves carry compatibility: its own carry-classified
declarations resolve in its hoisted scope (with the carried-name invariant
reflexive there), surviving entries resolve below it (their carried names are
unshadowed, so both the declaration and its carried names still agree). -/
theorem CarryCompat.extend {Δ : DEnv} {funs : FunEnv D}
    (h : CarryCompat (calls := calls) (creates := creates) Δ funs)
    (body : List (Stmt Op)) :
    CarryCompat (calls := calls) (creates := creates)
      (carryDeltaExtend Δ body) (hoist D body :: funs) := by
  intro p hp
  unfold carryDeltaExtend at hp
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨py, pd⟩ := p
    obtain ⟨ps, rs, fbody, hfind, hcl⟩ := carryHoistDecls_find hp
    obtain ⟨hps, hrs, -, -, hbody⟩ := carryClassifyDecl_inv hcl
    refine ⟨fbody, hoist D body :: funs, ?_, hbody, ?_⟩
    · show lookupFun (hoist D body :: funs) py = _
      unfold lookupFun
      rw [hfind]
      simp only [hps, hrs]
    · intro g hg; rfl
  · rw [List.mem_filter] at hp
    obtain ⟨hmem, hsurv⟩ := hp
    obtain ⟨body₀, cenv, hlk, hb, hag⟩ := h p hmem
    unfold carrySurvives at hsurv
    rw [Bool.and_eq_true] at hsurv
    have hpnf : p.1 ∉ definedFuns body := by
      have h1 := hsurv.1; simpa using h1
    refine ⟨body₀, cenv, ?_, hb, ?_⟩
    · rw [lookupFun_cons_hoist_not_mem hpnf]; exact hlk
    · intro g hg
      have hgnf : g ∉ definedFuns body := by
        have h1 := List.all_eq_true.mp hsurv.2 g hg; simpa using h1
      rw [lookupFun_cons_hoist_not_mem hgnf]; exact hag g hg

/-- Pruning names surviving a `for` init keeps carry compatibility under the
pushed init scope. -/
theorem CarryCompat.pruneInit {Δ : DEnv} {funs : FunEnv D}
    (h : CarryCompat (calls := calls) (creates := creates) Δ funs)
    (init : List (Stmt Op)) :
    CarryCompat (calls := calls) (creates := creates)
      (Δ.filter (carrySurvives (definedFuns init)))
      (hoist D init :: funs) := by
  intro p hp
  rw [List.mem_filter] at hp
  obtain ⟨hmem, hsurv⟩ := hp
  obtain ⟨body₀, cenv, hlk, hb, hag⟩ := h p hmem
  unfold carrySurvives at hsurv
  rw [Bool.and_eq_true] at hsurv
  have hpnf : p.1 ∉ definedFuns init := by
    have h1 := hsurv.1; simpa using h1
  refine ⟨body₀, cenv, ?_, hb, ?_⟩
  · rw [lookupFun_cons_hoist_not_mem hpnf]; exact hlk
  · intro g hg
    have hgnf : g ∉ definedFuns init := by
      have h1 := List.all_eq_true.mp hsurv.2 g hg; simpa using h1
    rw [lookupFun_cons_hoist_not_mem hgnf]; exact hag g hg

/-! ### The carry-inlining relation

Skip-rule relation over `PCode`, mirroring `IcRel` verbatim except: the block/
body/branch rules extend the context via `carryDeltaExtend` (with the
`carrySurvives` prune), the `for` prunes via `carrySurvives`, and the three
*site* rules carry the *carry* classification (`carryStmts`) and the profit
gate (`carryOK`, discharged where relevant). -/
inductive CyRel : DEnv → PCode Op → PCode Op → Prop
  | expr {Δ : DEnv} {e : Expr Op} : CyRel Δ (.expr e) (.expr e)
  | args {Δ : DEnv} {es : List (Expr Op)} : CyRel Δ (.args es) (.args es)
  | blockS {Δ : DEnv} {body body' : Block Op} :
      CyRel (carryDeltaExtend Δ body) (.stmts body) (.stmts body') →
      CyRel Δ (.stmt (.block body)) (.stmt (.block body'))
  | funDefS {Δ : DEnv} {n : Ident} {ps rs : List Ident} {body body' : Block Op} :
      CyRel (carryDeltaExtend Δ body) (.stmts body) (.stmts body') →
      CyRel Δ (.stmt (.funDef n ps rs body)) (.stmt (.funDef n ps rs body'))
  | letS {Δ : DEnv} {xs : List Ident} {v : Option (Expr Op)} :
      CyRel Δ (.stmt (.letDecl xs v)) (.stmt (.letDecl xs v))
  | assignS {Δ : DEnv} {xs : List Ident} {e : Expr Op} :
      CyRel Δ (.stmt (.assign xs e)) (.stmt (.assign xs e))
  | exprStmtS {Δ : DEnv} {e : Expr Op} :
      CyRel Δ (.stmt (.exprStmt e)) (.stmt (.exprStmt e))
  | condS {Δ : DEnv} {c : Expr Op} {body body' : Block Op} :
      CyRel (carryDeltaExtend Δ body) (.stmts body) (.stmts body') →
      CyRel Δ (.stmt (.cond c body)) (.stmt (.cond c body'))
  | switchS {Δ : DEnv} {c : Expr Op} {cases cases' : List (Literal × Block Op)}
      {dflt dflt' : Option (Block Op)} :
      CyRel Δ (.cases cases) (.cases cases') →
      CyRel Δ (.odflt dflt) (.odflt dflt') →
      CyRel Δ (.stmt (.switch c cases dflt)) (.stmt (.switch c cases' dflt'))
  | forS {Δ : DEnv} {init : Block Op} {c : Expr Op} {post post' body body' : Block Op} :
      CyRel (carryDeltaExtend (Δ.filter (carrySurvives (definedFuns init))) post)
        (.stmts post) (.stmts post') →
      CyRel (carryDeltaExtend (Δ.filter (carrySurvives (definedFuns init))) body)
        (.stmts body) (.stmts body') →
      CyRel Δ (.stmt (.forLoop init c post body))
        (.stmt (.forLoop init c post' body'))
  | breakS {Δ : DEnv} : CyRel Δ (.stmt .break) (.stmt .break)
  | continueS {Δ : DEnv} : CyRel Δ (.stmt .continue) (.stmt .continue)
  | leaveS {Δ : DEnv} : CyRel Δ (.stmt .leave) (.stmt .leave)
  | nilSS {Δ : DEnv} : CyRel Δ (.stmts []) (.stmts [])
  | consSS {Δ : DEnv} {s s' : Stmt Op} {rest rest' : List (Stmt Op)} :
      CyRel Δ (.stmt s) (.stmt s') → CyRel Δ (.stmts rest) (.stmts rest') →
      CyRel Δ (.stmts (s :: rest)) (.stmts (s' :: rest'))
  | siteLet {Δ : DEnv} {f : Ident} {d : IDecl} {xs : List Ident}
      {as : List (Expr Op)} {rest rest' : List (Stmt Op)} :
      lookupDelta Δ f = some d →
      (d.ps ++ d.rs).Nodup →
      carryStmts (d.ps ++ d.rs) d.ss = true →
      siteOK d xs as true = true →
      CyRel Δ (.stmts rest) (.stmts rest') →
      CyRel Δ (.stmts (.letDecl xs (some (.call f as)) :: rest))
        (.stmts (.letDecl xs none :: inlineCore d xs as :: rest'))
  | siteAssign {Δ : DEnv} {f : Ident} {d : IDecl} {xs : List Ident}
      {as : List (Expr Op)} {rest rest' : List (Stmt Op)} :
      lookupDelta Δ f = some d →
      (d.ps ++ d.rs).Nodup →
      carryStmts (d.ps ++ d.rs) d.ss = true →
      siteOK d xs as false = true →
      CyRel Δ (.stmts rest) (.stmts rest') →
      CyRel Δ (.stmts (.assign xs (.call f as) :: rest))
        (.stmts (inlineCore d xs as :: rest'))
  | siteExpr {Δ : DEnv} {f : Ident} {d : IDecl}
      {as : List (Expr Op)} {rest rest' : List (Stmt Op)} :
      lookupDelta Δ f = some d →
      (d.ps ++ d.rs).Nodup →
      carryStmts (d.ps ++ d.rs) d.ss = true →
      siteOK d [] as false = true →
      CyRel Δ (.stmts rest) (.stmts rest') →
      CyRel Δ (.stmts (.exprStmt (.call f as) :: rest))
        (.stmts (inlineCore d [] as :: rest'))
  | loopL {Δ : DEnv} {c : Expr Op} {post post' body body' : Block Op} :
      CyRel (carryDeltaExtend Δ post) (.stmts post) (.stmts post') →
      CyRel (carryDeltaExtend Δ body) (.stmts body) (.stmts body') →
      CyRel Δ (.loop c post body) (.loop c post' body')
  | casesNil {Δ : DEnv} : CyRel Δ (.cases []) (.cases [])
  | casesCons {Δ : DEnv} {l : Literal} {b b' : Block Op}
      {rest rest' : List (Literal × Block Op)} :
      CyRel (carryDeltaExtend Δ b) (.stmts b) (.stmts b') →
      CyRel Δ (.cases rest) (.cases rest') →
      CyRel Δ (.cases ((l, b) :: rest)) (.cases ((l, b') :: rest'))
  | odfltNone {Δ : DEnv} : CyRel Δ (.odflt none) (.odflt none)
  | odfltSome {Δ : DEnv} {b b' : Block Op} :
      CyRel (carryDeltaExtend Δ b) (.stmts b) (.stmts b') →
      CyRel Δ (.odflt (some b)) (.odflt (some b'))

/-! ### The transform inhabits the relation -/

mutual

/-- The statement-list transform inhabits the relation. -/
theorem cyStmts_rel (Δ : DEnv) (hwf : CarryWF Δ) :
    ∀ ss : List (Stmt Op), CyRel Δ (.stmts ss) (.stmts (cyStmts Δ ss))
  | [] => by rw [cyStmts]; exact .nilSS
  | .letDecl xs (some (.call f as)) :: rest => by
      rw [cyStmts, cyStmt]
      split
      · next d hld =>
          obtain ⟨hnd, hsc⟩ := hwf (f, d) (lookupDelta_mem hld)
          by_cases hok : (carryOK d && siteOK d xs as true) = true
          · rw [if_pos hok]
            rw [Bool.and_eq_true] at hok
            exact .siteLet hld hnd hsc hok.2 (cyStmts_rel Δ hwf rest)
          · rw [if_neg hok]
            exact .consSS .letS (cyStmts_rel Δ hwf rest)
      · exact .consSS .letS (cyStmts_rel Δ hwf rest)
  | .assign xs (.call f as) :: rest => by
      rw [cyStmts, cyStmt]
      split
      · next d hld =>
          obtain ⟨hnd, hsc⟩ := hwf (f, d) (lookupDelta_mem hld)
          by_cases hok : (carryOK d && siteOK d xs as false) = true
          · rw [if_pos hok]
            rw [Bool.and_eq_true] at hok
            exact .siteAssign hld hnd hsc hok.2 (cyStmts_rel Δ hwf rest)
          · rw [if_neg hok]
            exact .consSS .assignS (cyStmts_rel Δ hwf rest)
      · exact .consSS .assignS (cyStmts_rel Δ hwf rest)
  | .exprStmt (.call f as) :: rest => by
      rw [cyStmts, cyStmt]
      split
      · next d hld =>
          obtain ⟨hnd, hsc⟩ := hwf (f, d) (lookupDelta_mem hld)
          by_cases hok : (carryOK d && siteOK d [] as false) = true
          · rw [if_pos hok]
            rw [Bool.and_eq_true] at hok
            exact .siteExpr hld hnd hsc hok.2 (cyStmts_rel Δ hwf rest)
          · rw [if_neg hok]
            exact .consSS .exprStmtS (cyStmts_rel Δ hwf rest)
      · exact .consSS .exprStmtS (cyStmts_rel Δ hwf rest)
  | .block body :: rest => by
      rw [cyStmts, cyStmt, cyBlock]
      exact .consSS (.blockS (cyStmts_rel _ (hwf.extend body) body))
        (cyStmts_rel Δ hwf rest)
  | .funDef n ps rs body :: rest => by
      rw [cyStmts, cyStmt, cyBlock]
      exact .consSS (.funDefS (cyStmts_rel _ (hwf.extend body) body))
        (cyStmts_rel Δ hwf rest)
  | .letDecl xs none :: rest => by
      rw [cyStmts]; simp only [cyStmt]
      exact .consSS .letS (cyStmts_rel Δ hwf rest)
  | .letDecl xs (some (.lit l)) :: rest => by
      rw [cyStmts]; simp only [cyStmt]
      exact .consSS .letS (cyStmts_rel Δ hwf rest)
  | .letDecl xs (some (.var y)) :: rest => by
      rw [cyStmts]; simp only [cyStmt]
      exact .consSS .letS (cyStmts_rel Δ hwf rest)
  | .letDecl xs (some (.builtin op es)) :: rest => by
      rw [cyStmts]; simp only [cyStmt]
      exact .consSS .letS (cyStmts_rel Δ hwf rest)
  | .assign xs (.lit l) :: rest => by
      rw [cyStmts]; simp only [cyStmt]
      exact .consSS .assignS (cyStmts_rel Δ hwf rest)
  | .assign xs (.var y) :: rest => by
      rw [cyStmts]; simp only [cyStmt]
      exact .consSS .assignS (cyStmts_rel Δ hwf rest)
  | .assign xs (.builtin op es) :: rest => by
      rw [cyStmts]; simp only [cyStmt]
      exact .consSS .assignS (cyStmts_rel Δ hwf rest)
  | .exprStmt (.lit l) :: rest => by
      rw [cyStmts]; simp only [cyStmt]
      exact .consSS .exprStmtS (cyStmts_rel Δ hwf rest)
  | .exprStmt (.var y) :: rest => by
      rw [cyStmts]; simp only [cyStmt]
      exact .consSS .exprStmtS (cyStmts_rel Δ hwf rest)
  | .exprStmt (.builtin op es) :: rest => by
      rw [cyStmts]; simp only [cyStmt]
      exact .consSS .exprStmtS (cyStmts_rel Δ hwf rest)
  | .cond c body :: rest => by
      rw [cyStmts, cyStmt, cyBlock]
      exact .consSS (.condS (cyStmts_rel _ (hwf.extend body) body))
        (cyStmts_rel Δ hwf rest)
  | .switch c cases dflt :: rest => by
      rw [cyStmts, cyStmt]
      exact .consSS (.switchS (cyCases_rel Δ hwf cases) (cyDflt_rel Δ hwf dflt))
        (cyStmts_rel Δ hwf rest)
  | .forLoop init c post body :: rest => by
      rw [cyStmts, cyStmt]
      simp only [cyBlock]
      exact .consSS (.forS
          (cyStmts_rel _ ((hwf.filter _).extend post) post)
          (cyStmts_rel _ ((hwf.filter _).extend body) body))
        (cyStmts_rel Δ hwf rest)
  | .break :: rest => by
      rw [cyStmts]; simp only [cyStmt]
      exact .consSS .breakS (cyStmts_rel Δ hwf rest)
  | .continue :: rest => by
      rw [cyStmts]; simp only [cyStmt]
      exact .consSS .continueS (cyStmts_rel Δ hwf rest)
  | .leave :: rest => by
      rw [cyStmts]; simp only [cyStmt]
      exact .consSS .leaveS (cyStmts_rel Δ hwf rest)

/-- The case-list transform inhabits the relation. -/
theorem cyCases_rel (Δ : DEnv) (hwf : CarryWF Δ) :
    ∀ cs : List (Literal × Block Op), CyRel Δ (.cases cs) (.cases (cyCases Δ cs))
  | [] => by rw [cyCases]; exact .casesNil
  | (l, b) :: rest => by
      rw [cyCases, cyBlock]
      exact .casesCons (cyStmts_rel _ (hwf.extend b) b) (cyCases_rel Δ hwf rest)

/-- The default transform inhabits the relation. -/
theorem cyDflt_rel (Δ : DEnv) (hwf : CarryWF Δ) :
    ∀ dflt : Option (Block Op), CyRel Δ (.odflt dflt) (.odflt (cyDflt Δ dflt))
  | none => by rw [cyDflt]; exact .odfltNone
  | some b => by
      rw [cyDflt, cyBlock]
      exact .odfltSome (cyStmts_rel _ (hwf.extend b) b)

end

/-! ### Reflexivity (the all-skip derivation) -/

mutual

theorem CyRel.reflStmt (Δ : DEnv) : ∀ s : Stmt Op, CyRel Δ (.stmt s) (.stmt s)
  | .block body => .blockS (CyRel.reflStmts _ body)
  | .funDef n ps rs body => .funDefS (CyRel.reflStmts _ body)
  | .letDecl xs v => .letS
  | .assign xs e => .assignS
  | .exprStmt e => .exprStmtS
  | .cond c body => .condS (CyRel.reflStmts _ body)
  | .switch c cases dflt =>
      .switchS (CyRel.reflCases Δ cases) (CyRel.reflDflt Δ dflt)
  | .forLoop init c post body =>
      .forS (CyRel.reflStmts _ post) (CyRel.reflStmts _ body)
  | .break => .breakS
  | .continue => .continueS
  | .leave => .leaveS

theorem CyRel.reflStmts (Δ : DEnv) : ∀ ss : List (Stmt Op),
    CyRel Δ (.stmts ss) (.stmts ss)
  | [] => .nilSS
  | s :: rest => .consSS (CyRel.reflStmt Δ s) (CyRel.reflStmts Δ rest)

theorem CyRel.reflCases (Δ : DEnv) : ∀ cs : List (Literal × Block Op),
    CyRel Δ (.cases cs) (.cases cs)
  | [] => .casesNil
  | (l, b) :: rest => .casesCons (CyRel.reflStmts _ b) (CyRel.reflCases Δ rest)

theorem CyRel.reflDflt (Δ : DEnv) : ∀ dflt : Option (Block Op),
    CyRel Δ (.odflt dflt) (.odflt dflt)
  | none => .odfltNone
  | some b => .odfltSome (CyRel.reflStmts _ b)

end

/-! ### Function-environment relation -/

/-- Declarations related by the carry transform, relative to the defining
environment. -/
def CyFDeclRel (cenv : FunEnv D) (d₁ d₂ : FDecl D) : Prop :=
  d₁.params = d₂.params ∧ d₁.rets = d₂.rets ∧
    ∃ Δ, CarryCompat (calls := calls) (creates := creates) Δ cenv ∧
      CyRel (carryDeltaExtend Δ d₁.body) (.stmts d₁.body) (.stmts d₂.body)

/-- Scopes related pairwise, relative to the defining environment. -/
def CyScopeRel (cenv : FunEnv D) (s₁ s₂ : FScope D) : Prop :=
  List.Forall₂ (fun p q => p.1 = q.1 ∧
    CyFDeclRel (calls := calls) (creates := creates) cenv p.2 q.2) s₁ s₂

/-- Function environments related scope-by-scope, each scope relative to its
own defining suffix. -/
inductive CyFunsRel : FunEnv D → FunEnv D → Prop
  | nil : CyFunsRel [] []
  | cons {s₁ s₂ : FScope D} {r₁ r₂ : FunEnv D} :
      CyScopeRel (calls := calls) (creates := creates) (s₁ :: r₁) s₁ s₂ →
      CyFunsRel r₁ r₂ →
      CyFunsRel (s₁ :: r₁) (s₂ :: r₂)

/-- A scope lookup transports across `CyScopeRel`. -/
theorem cyScopeRel_find {cenv : FunEnv D} {s₁ s₂ : FScope D}
    (h : CyScopeRel (calls := calls) (creates := creates) cenv s₁ s₂)
    (fn : Ident) :
    (s₁.find? (fun p => p.1 = fn) = none ∧ s₂.find? (fun p => p.1 = fn) = none) ∨
    (∃ p q, s₁.find? (fun p => p.1 = fn) = some p ∧
      s₂.find? (fun p => p.1 = fn) = some q ∧ p.1 = q.1 ∧
      CyFDeclRel (calls := calls) (creates := creates) cenv p.2 q.2) := by
  induction h with
  | nil => left; simp
  | @cons p q u₁ u₂ hpq _ ih =>
      by_cases hp : p.1 = fn
      · right
        refine ⟨p, q, ?_, ?_, hpq.1, hpq.2⟩
        · exact List.find?_cons_of_pos (by simp [hp])
        · exact List.find?_cons_of_pos (by simp [← hpq.1, hp])
      · rw [List.find?_cons_of_neg (by simp [hp]),
            List.find?_cons_of_neg (by simp [← hpq.1, hp])]
        exact ih

/-- `lookupFun` transports forward across `CyFunsRel`. -/
theorem lookupFun_cyFunsRel {f₁ f₂ : FunEnv D}
    (hR : CyFunsRel (calls := calls) (creates := creates) f₁ f₂)
    {fn : Ident} {decl₁ : FDecl D} {cenv₁ : FunEnv D}
    (h : lookupFun f₁ fn = some (decl₁, cenv₁)) :
    ∃ decl₂ cenv₂, lookupFun f₂ fn = some (decl₂, cenv₂) ∧
      CyFDeclRel (calls := calls) (creates := creates) cenv₁ decl₁ decl₂ ∧
      CyFunsRel (calls := calls) (creates := creates) cenv₁ cenv₂ := by
  induction hR with
  | nil => cases h
  | @cons s₁ s₂ r₁ r₂ hscope hrest ih =>
      unfold lookupFun at h ⊢
      rcases cyScopeRel_find hscope fn with ⟨h1, h2⟩ | ⟨p, q, h1, h2, hname, hdecl⟩
      · rw [h1] at h
        rw [h2]
        exact ih h
      · rw [h1] at h
        rw [h2]
        injection h with h
        injection h with hd hc
        subst hd hc
        exact ⟨q.2, s₂ :: r₂, rfl, hdecl, .cons hscope hrest⟩

/-- `lookupFun` transports backward across `CyFunsRel`. -/
theorem lookupFun_cyFunsRel_bwd {f₁ f₂ : FunEnv D}
    (hR : CyFunsRel (calls := calls) (creates := creates) f₁ f₂)
    {fn : Ident} {decl₂ : FDecl D} {cenv₂ : FunEnv D}
    (h : lookupFun f₂ fn = some (decl₂, cenv₂)) :
    ∃ decl₁ cenv₁, lookupFun f₁ fn = some (decl₁, cenv₁) ∧
      CyFDeclRel (calls := calls) (creates := creates) cenv₁ decl₁ decl₂ ∧
      CyFunsRel (calls := calls) (creates := creates) cenv₁ cenv₂ := by
  induction hR with
  | nil => cases h
  | @cons s₁ s₂ r₁ r₂ hscope hrest ih =>
      unfold lookupFun at h ⊢
      rcases cyScopeRel_find hscope fn with ⟨h1, h2⟩ | ⟨p, q, h1, h2, hname, hdecl⟩
      · rw [h2] at h
        rw [h1]
        exact ih h
      · rw [h2] at h
        rw [h1]
        injection h with h
        injection h with hd hc
        subst hd hc
        exact ⟨p.2, s₁ :: r₁, rfl, hdecl, .cons hscope hrest⟩

/-- Extract the hoisted-scope alignment from a related statement sequence. -/
theorem CyRel.hoist_scopeRel {Δ : DEnv} {pc pc' : PCode Op}
    (h : CyRel Δ pc pc') :
    ∀ {ss ss' : List (Stmt Op)}, pc = .stmts ss → pc' = .stmts ss' →
      List.Forall₂ (fun (p q : Ident × FDecl D) => p.1 = q.1 ∧
        p.2.params = q.2.params ∧ p.2.rets = q.2.rets ∧
        CyRel (carryDeltaExtend Δ p.2.body) (.stmts p.2.body) (.stmts q.2.body))
        (hoist D ss) (hoist D ss') := by
  induction h with
  | nilSS =>
      intro ss ss' hss hss'
      injection hss with h1; injection hss' with h2
      subst h1; subst h2
      exact .nil
  | consSS hs _ _ ihrest =>
      intro ss ss' hss hss'
      injection hss with h1; injection hss' with h2
      subst h1; subst h2
      have htail := ihrest rfl rfl
      cases hs with
      | funDefS hbody => exact .cons ⟨rfl, rfl, rfl, hbody⟩ htail
      | blockS _ => simpa [hoist] using htail
      | letS => simpa [hoist] using htail
      | assignS => simpa [hoist] using htail
      | condS _ => simpa [hoist] using htail
      | switchS _ _ => simpa [hoist] using htail
      | forS _ _ => simpa [hoist] using htail
      | exprStmtS => simpa [hoist] using htail
      | breakS => simpa [hoist] using htail
      | continueS => simpa [hoist] using htail
      | leaveS => simpa [hoist] using htail
  | siteLet hld hnd hsc hok _ ihrest =>
      intro ss ss' hss hss'
      injection hss with h1; injection hss' with h2
      subst h1; subst h2
      have htail := ihrest rfl rfl
      show List.Forall₂ _ (hoist D (_ :: _)) (hoist D (_ :: _ :: _))
      simpa [hoist, inlineCore] using htail
  | siteAssign hld hnd hsc hok _ ihrest =>
      intro ss ss' hss hss'
      injection hss with h1; injection hss' with h2
      subst h1; subst h2
      have htail := ihrest rfl rfl
      simpa [hoist, inlineCore] using htail
  | siteExpr hld hnd hsc hok _ ihrest =>
      intro ss ss' hss hss'
      injection hss with h1; injection hss' with h2
      subst h1; subst h2
      have htail := ihrest rfl rfl
      simpa [hoist, inlineCore] using htail
  | expr => exact fun h _ => nomatch h
  | args => exact fun h _ => nomatch h
  | blockS _ _ => exact fun h _ => nomatch h
  | funDefS _ _ => exact fun h _ => nomatch h
  | letS => exact fun h _ => nomatch h
  | assignS => exact fun h _ => nomatch h
  | exprStmtS => exact fun h _ => nomatch h
  | condS _ _ => exact fun h _ => nomatch h
  | switchS _ _ _ _ => exact fun h _ => nomatch h
  | forS _ _ _ _ => exact fun h _ => nomatch h
  | breakS => exact fun h _ => nomatch h
  | continueS => exact fun h _ => nomatch h
  | leaveS => exact fun h _ => nomatch h
  | loopL _ _ _ _ => exact fun h _ => nomatch h
  | casesNil => exact fun h _ => nomatch h
  | casesCons _ _ _ _ => exact fun h _ => nomatch h
  | odfltNone => exact fun h _ => nomatch h
  | odfltSome _ _ => exact fun h _ => nomatch h

/-- The scope-alignment of a related block yields `CyScopeRel`. -/
theorem cyScopeRel_of_block {Δ : DEnv} {funs : FunEnv D}
    {body body' : List (Stmt Op)}
    (hrel : CyRel (carryDeltaExtend Δ body) (.stmts body) (.stmts body'))
    (hcompat : CarryCompat (calls := calls) (creates := creates)
      (carryDeltaExtend Δ body) (hoist D body :: funs)) :
    CyScopeRel (calls := calls) (creates := creates)
      (hoist D body :: funs) (hoist D body) (hoist D body') := by
  have hpairs := CyRel.hoist_scopeRel (calls := calls) (creates := creates)
    hrel rfl rfl
  refine List.Forall₂.imp ?_ hpairs
  intro p q hpq
  exact ⟨hpq.1, hpq.2.1, hpq.2.2.1, carryDeltaExtend Δ body, hcompat, hpq.2.2.2⟩

/-- Reflexive scope relation (for untouched `for`-loop inits). -/
theorem cyScopeRel_refl (cenv : FunEnv D) (s : FScope D) :
    CyScopeRel (calls := calls) (creates := creates) cenv s s := by
  induction s with
  | nil => exact .nil
  | cons p rest ih =>
      refine .cons ⟨rfl, rfl, rfl, [], CarryCompat.nil _, ?_⟩ ih
      exact CyRel.reflStmts _ _

/-- Function environments are self-related. -/
theorem CyFunsRel.refl : ∀ funs : FunEnv D,
    CyFunsRel (calls := calls) (creates := creates) funs funs
  | [] => .nil
  | s :: rest => .cons (cyScopeRel_refl _ s) (CyFunsRel.refl rest)

/-! ### Result correspondence -/

/-- Result correspondence: identical, except a `halt` reached inside an inlined
`let`-form site carries the site's zero-bound targets as an environment prefix
(erased at the nearest enclosing block's `restore`). -/
inductive CyRes : Res D → Res D → Prop
  | refl (r : Res D) : CyRes r r
  | haltIns (Zp V₁ : VEnv D) (st : EvmState) :
      CyRes (.sres V₁ st .halt) (.sres (Zp ++ V₁) st .halt)

/-- The per-class result claim: residue only on the statement-sequence class. -/
def cyResOK : Code Op → Res D → Res D → Prop
  | .stmts _, r₁, r₂ => CyRes (calls := calls) (creates := creates) r₁ r₂
  | _, r₁, r₂ => r₂ = r₁

/-- The switch selection of related case lists/defaults is a related block. -/
theorem CyRel.selectRel {Δ : DEnv} {cases cases' : List (Literal × Block Op)}
    {dflt dflt' : Option (Block Op)}
    (hcs : CyRel Δ (.cases cases) (.cases cases'))
    (hd : CyRel Δ (.odflt dflt) (.odflt dflt')) (cv : U256) :
    CyRel Δ (.stmt (.block (selectSwitch D cv cases dflt)))
      (.stmt (.block (selectSwitch D cv cases' dflt'))) := by
  induction cases generalizing cases' with
  | nil =>
      cases hcs
      cases hd with
      | odfltNone =>
          show CyRel Δ (.stmt (.block (Option.getD none [])))
            (.stmt (.block (Option.getD none [])))
          exact .blockS (CyRel.reflStmts _ _)
      | odfltSome hb =>
          simpa [selectSwitch] using CyRel.blockS hb
  | cons head rest ih =>
      rcases head with ⟨l, b⟩
      cases hcs with
      | casesCons hb hrest =>
          by_cases hcv : cv = (evmWithExternal calls creates).litValue l
          · rw [selectSwitch, List.find?_cons_of_pos (by simp [hcv]),
                selectSwitch, List.find?_cons_of_pos (by simp [hcv])]
            exact .blockS hb
          · rw [selectSwitch, List.find?_cons_of_neg (by simp [hcv]),
                selectSwitch, List.find?_cons_of_neg (by simp [hcv])]
            have := ih hrest
            rw [selectSwitch, selectSwitch] at this
            exact this

