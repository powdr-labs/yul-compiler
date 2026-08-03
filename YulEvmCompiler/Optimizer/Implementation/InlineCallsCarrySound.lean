import YulEvmCompiler.Optimizer.Implementation.InlineCallsCarry
import YulEvmCompiler.Optimizer.Implementation.InlineCallsSound
import YulEvmCompiler.Optimizer.Implementation.FunCongr
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
/-!
# YulEvmCompiler.Optimizer.Implementation.InlineCallsCarrySound

Soundness of the call-carrying inliner (`InlineCallsCarry.lean`).

The architecture mirrors `InlineCallsSound`, with one change concentrated in
the callee-body transfer at an inline site. `InlineCalls` bodies are call-free,
so `scoped_transfer` moves the body's execution to *any* function environment
(it never consults `funs`). Carry bodies bear calls: the transplanted copy runs
its inner calls under the caller's function environment at the site, whereas the
original runs them under the callee's defining scope `cenv`. Two facts bridge
the gap:

* **`carry_transfer`** — the analog of `scoped_transfer` that *permits* calls.
  It transfers execution to any function environment that **agrees** with the
  original on the code's (syntactic) call names, and simultaneously weakens the
  variable environment by an inert suffix. Agreement is exactly what the
  no-shadowing gate (`carrySurvives`) guarantees between the callee's defining
  scope and the rewrite site.
* **`Step.funs_congr`** (`FunCongr.lean`) — the semantic function-environment
  congruence: once the body runs under the *source* site environment, it runs
  under the *transformed* site environment with the same result, because the
  two environments' functions have `EquivBlock`-equivalent bodies.
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
