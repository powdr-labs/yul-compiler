import YulEvmCompiler.Optimizer.Implementation.InlineCalls
import YulEvmCompiler.Optimizer.Implementation.DeadLits
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
/-!
# YulEvmCompiler.Optimizer.Implementation.InlineCallsSound

Soundness of the `InlineCalls` transform (see `InlineCalls.lean` for the
transform and the module notes). Proof architecture:

1. **`scoped_transfer`** — the single semantic engine: code accepted by the
   `scopedStmts` checker executes identically under *any* function
   environment (it contains no calls, so `Step` never consults `funs`) and
   under *any* extension of its environment below the checked part
   (`A ++ W` for arbitrary `W`), producing only `normal`/`halt` outcomes.
   One induction gives funs-irrelevance, scoped weakening in both
   directions, and the outcome restriction at once.

2. **Site lemmas** — conditional on `lookupFun` resolving the callee, the
   call statement and its inlined replacement produce the same results
   (exactly equal on the `assign`/`exprStmt` forms and on every `normal`
   path; the `let` form's halt paths carry the site's zero-bound `xs` as an
   environment prefix until the enclosing block's `restore` erases it).

3. **`IcRel`** — a PropRel-style skip-rule relation indexed by the syntactic
   declaration map `Δ`, with forward/backward `Step` simulations carrying
   `DeltaCompat` (every `Δ` entry resolves via `lookupFun` to its recorded
   declaration) and an `IcFunsRel` function-environment relation.

4. `IcRel.equivBlock` + transform inhabitation discharge `Pass.Sound`.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM

variable {calls : ExternalCalls} {creates : ExternalCreates}

local notation "D" => evmWithExternal calls creates

/-! ### Environment splitting lemmas

Execution of scoped code over `A ++ W` keeps `W` inert: reads and writes of
checked names hit the innermost occurrence, which the checker keeps inside
`A`. -/

/-- A key bound in `A` is found in `A`. -/
theorem VEnv.find?_key_isSome {A : VEnv D} {x : Ident}
    (h : x ∈ A.map Prod.fst) : (A.find? (fun p => p.1 = x)).isSome := by
  rw [List.find?_isSome]
  obtain ⟨p, hp, hpx⟩ := List.mem_map.mp h
  exact ⟨p, hp, by simp [hpx]⟩

/-- Lookup of a key bound in the top part ignores the extension. -/
theorem VEnv.get_append_mem {A : VEnv D} {x : Ident}
    (h : x ∈ A.map Prod.fst) (W : VEnv D) :
    VEnv.get (A ++ W) x = VEnv.get A x := by
  unfold VEnv.get
  rw [List.find?_append]
  obtain ⟨p, hs⟩ := Option.isSome_iff_exists.mp (VEnv.find?_key_isSome h)
  rw [hs]
  rfl

/-- Update of a key bound in the top part ignores the extension. -/
theorem VEnv.set_append_mem {A : VEnv D} {x : Ident}
    (h : x ∈ A.map Prod.fst) (W : VEnv D) (v : U256) :
    VEnv.set (A ++ W) x v = VEnv.set A x v ++ W := by
  induction A with
  | nil => simp at h
  | cons p rest ih =>
      obtain ⟨py, pv⟩ := p
      simp only [List.map_cons, List.mem_cons] at h
      simp only [List.cons_append, VEnv.set]
      by_cases hp : py = x
      · simp [hp]
      · rcases h with h | h
        · exact absurd h.symm hp
        · simp only [hp, if_false, List.cons_append, ih h]

/-- Update of a key not bound in the top part passes through it. -/
theorem VEnv.set_append_not_mem {A : VEnv D} {x : Ident}
    (h : x ∉ A.map Prod.fst) (W : VEnv D) (v : U256) :
    VEnv.set (A ++ W) x v = A ++ VEnv.set W x v := by
  induction A with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨py, pv⟩ := p
      simp only [List.map_cons, List.mem_cons, not_or] at h
      simp only [List.cons_append, VEnv.set]
      rw [if_neg (fun hh => h.1 hh.symm), ih h.2]

/-- Multi-update over keys all bound in the top part ignores the extension. -/
theorem VEnv.setMany_append_mem {A W : VEnv D} {xs : List Ident} {vs : List U256}
    (h : ∀ x ∈ xs, x ∈ A.map Prod.fst) :
    VEnv.setMany (A ++ W) xs vs = VEnv.setMany A xs vs ++ W := by
  unfold VEnv.setMany
  induction xs generalizing vs A with
  | nil => rfl
  | cons x rest ih =>
      cases vs with
      | nil => rfl
      | cons v vrest =>
          simp only [List.zip_cons_cons, List.foldl_cons]
          rw [VEnv.set_append_mem (h x (by simp)) W v]
          exact ih (fun y hy => by
            rw [VEnv.set_keys]
            exact h y (List.mem_cons_of_mem _ hy))

/-- `restore` distributes over a common extension. -/
theorem restore_append {A A' W : VEnv D} (h : A.length ≤ A'.length) :
    restore (A ++ W) (A' ++ W) = restore A A' ++ W := by
  simp only [restore, List.length_append]
  rw [show A'.length + W.length - (A.length + W.length) = A'.length - A.length by omega]
  rw [List.drop_append_of_le_length (by omega)]

/-- Cancelling a common extension of a keys-suffix. -/
theorem keys_suffix_cancel {A A' W : VEnv D}
    (hs : (A ++ W).map Prod.fst <:+ (A' ++ W).map Prod.fst) :
    A.map Prod.fst <:+ A'.map Prod.fst := by
  obtain ⟨t, ht⟩ := hs
  refine ⟨t, ?_⟩
  simp only [List.map_append] at ht
  have := congrArg (fun l => List.take (l.length - W.length) l) ht
  simpa [List.length_append, List.take_append_of_le_length,
    List.take_of_length_le] using
    List.append_cancel_right (by simpa [List.append_assoc] using ht)

/-- Zero-bindings bind exactly their names. -/
theorem bindZeros_keys (xs : List Ident) :
    (bindZeros D xs).map Prod.fst = xs := by
  unfold bindZeros
  induction xs with
  | nil => rfl
  | cons x rest ih => simpa using ih

/-! ### Scoped-code inversions -/

/-- Per-class scoped check for the transfer induction. -/
def scopedArgs (bound : List Ident) : List (Expr Op) → Bool
  | [] => true
  | e :: rest => scopedExpr bound e && scopedArgs bound rest

/-- Per-class scoped check for the transfer induction. -/
def scopedCode (bound : List Ident) : Code Op → Bool
  | .expr e => scopedExpr bound e
  | .args es => scopedArgs bound es
  | .stmt s => (scopedStmt bound s).isSome
  | .stmts ss => scopedStmts bound ss
  | .loop _ _ _ => false

/-- Argument lists with no calls and bound reads are scoped, per argument. -/
theorem scopedArgs_of_parts {bound : List Ident} {args : List (Expr Op)}
    (hnc : argsHaveCall args = false)
    (hv : (varsList args).all bound.contains = true) :
    scopedArgs bound args = true := by
  induction args with
  | nil => rfl
  | cons e rest ih =>
      rw [show argsHaveCall (e :: rest) = (exprHasCall e || argsHaveCall rest) from rfl,
        Bool.or_eq_false_iff] at hnc
      rw [show varsList (e :: rest) = exprVars e ++ varsList rest from rfl,
        List.all_append, Bool.and_eq_true] at hv
      unfold scopedArgs
      rw [Bool.and_eq_true]
      refine ⟨?_, ih hnc.2 hv.2⟩
      unfold scopedExpr
      rw [Bool.and_eq_true, Bool.not_eq_true']
      exact ⟨hnc.1, hv.1⟩

/-- A scoped builtin's arguments are scoped. -/
theorem scopedExpr_builtin_args {bound : List Ident} {op : Op} {args : List (Expr Op)}
    (h : scopedExpr bound (.builtin op args) = true) :
    scopedArgs bound args = true := by
  unfold scopedExpr at h
  rw [Bool.and_eq_true, Bool.not_eq_true'] at h
  exact scopedArgs_of_parts h.1 h.2

/-- The selected switch block of scoped cases/default is scoped. -/
theorem scoped_selectSwitch {bound : List Ident} {cv : U256}
    {cases : List (Literal × Block Op)} {dflt : Option (Block Op)}
    (hc : scopedCases bound cases = true) (hd : scopedDflt bound dflt = true) :
    scopedStmts bound (selectSwitch D cv cases dflt) = true := by
  induction cases with
  | nil =>
      unfold selectSwitch
      simp only [List.find?_nil]
      cases dflt with
      | none => rfl
      | some b => exact hd
  | cons hd' rest ih =>
      rcases hd' with ⟨l, b⟩
      unfold scopedCases at hc
      rw [Bool.and_eq_true] at hc
      by_cases hcv : cv = (evmWithExternal calls creates).litValue l
      · rw [selectSwitch, List.find?_cons_of_pos (by simp [hcv])]
        exact hc.1
      · rw [selectSwitch, List.find?_cons_of_neg (by simp [hcv])]
        have := ih hc.2
        rw [selectSwitch] at this
        exact this

/-! ### The scoped-transfer engine -/

/-- Result correspondence for `scoped_transfer`: expression results transfer
verbatim; statement-class results split as `A' ++ W ↦ A' ++ W'` with only
`normal`/`halt` outcomes, the `normal` case re-establishing the checker's
binding context inside `A'`. -/
inductive TRes (W W' : VEnv D) (post : List Ident) : Res D → Res D → Prop
  | eres (r : EResult D) : TRes W W' post (.eres r) (.eres r)
  | norm {A' : VEnv D} {st' : EvmState}
      (hk : ∀ x ∈ post, x ∈ A'.map Prod.fst) :
      TRes W W' post (.sres (A' ++ W) st' .normal) (.sres (A' ++ W') st' .normal)
  | halt {A' : VEnv D} {st' : EvmState} :
      TRes W W' post (.sres (A' ++ W) st' .halt) (.sres (A' ++ W') st' .halt)

/-- The binding context the checker leaves after one statement (`bound` for
every other class — sequences end at blocks, which restore). -/
def postBound (bound : List Ident) : Code Op → List Ident
  | .stmt s => (scopedStmt bound s).getD bound
  | _ => []

/-- Split a scoped sequence at its head. -/
theorem scopedStmts_cons_inv {bound : List Ident} {s : Stmt Op} {rest : List (Stmt Op)}
    (h : scopedStmts bound (s :: rest) = true) :
    ∃ bound₁, scopedStmt bound s = some bound₁ ∧ scopedStmts bound₁ rest = true := by
  unfold scopedStmts at h
  split at h
  · next bound₁ heq => exact ⟨bound₁, heq, h⟩
  · cases h

/-- Membership form of a positive `List.all contains` test. -/
theorem all_contains_subset {xs bound : List Ident}
    (h : xs.all bound.contains = true) : ∀ x ∈ xs, x ∈ bound := by
  intro x hx
  have := List.all_eq_true.mp h x hx
  simpa using this

/-- **The scoped-transfer engine.** Scoped code never consults the function
environment (it has no calls) and never touches an environment extension
below its checked part — so its execution transfers verbatim from
`funs₁, A ++ W` to *any* `funs₂, A ++ W'`, and it produces only
`normal`/`halt` outcomes. One induction yields funs-irrelevance, scoped
weakening (in both directions, by symmetry of `W`/`W'`), and the outcome
restriction. -/
theorem scoped_transfer {funs₁ : FunEnv D} {V₁ : VEnv D} {st : EvmState}
    {code : Code Op} {res₁ : Res D}
    (h : Step D funs₁ V₁ st code res₁) :
    ∀ {A W : VEnv D} {bound : List Ident} (funs₂ : FunEnv D) (W' : VEnv D),
      V₁ = A ++ W → scopedCode bound code = true →
      (∀ x ∈ bound, x ∈ A.map Prod.fst) →
      ∃ res₂, Step D funs₂ (A ++ W') st code res₂ ∧
        TRes (calls := calls) (creates := creates) W W'
          (postBound bound code) res₁ res₂ := by
  induction h with
  | @lit funs V st l =>
      intro A W bound funs₂ W' hV hsc hb
      exact ⟨_, Step.lit, .eres _⟩
  | @var funs V st x v hv =>
      intro A W bound funs₂ W' hV hsc hb
      subst hV
      have hx : x ∈ bound := by
        unfold scopedCode scopedExpr at hsc
        rw [Bool.and_eq_true] at hsc
        have := List.all_eq_true.mp hsc.2 x (by simp [exprVars])
        simpa using this
      have hxA : x ∈ A.map Prod.fst := hb x hx
      have hgv : VEnv.get A x = some v := by
        rw [← VEnv.get_append_mem hxA W]; exact hv
      refine ⟨_, Step.var ?_, .eres _⟩
      rw [VEnv.get_append_mem hxA W']; exact hgv
  | @builtinOk funs V st op args argvals st1 rets st2 ha hbi iha =>
      intro A W bound funs₂ W' hV hsc hb
      have hargs : scopedArgs bound args = true := scopedExpr_builtin_args hsc
      obtain ⟨res₂, hstep, htr⟩ := iha funs₂ W' hV hargs hb
      cases htr with
      | eres => exact ⟨_, Step.builtinOk hstep hbi, .eres _⟩
  | @builtinHalt funs V st op args argvals st1 st2 ha hbi iha =>
      intro A W bound funs₂ W' hV hsc hb
      have hargs : scopedArgs bound args = true := scopedExpr_builtin_args hsc
      obtain ⟨res₂, hstep, htr⟩ := iha funs₂ W' hV hargs hb
      cases htr with
      | eres => exact ⟨_, Step.builtinHalt hstep hbi, .eres _⟩
  | @builtinArgsHalt funs V st op args st1 ha iha =>
      intro A W bound funs₂ W' hV hsc hb
      have hargs : scopedArgs bound args = true := scopedExpr_builtin_args hsc
      obtain ⟨res₂, hstep, htr⟩ := iha funs₂ W' hV hargs hb
      cases htr with
      | eres => exact ⟨_, Step.builtinArgsHalt hstep, .eres _⟩
  | callOk | callHalt | callArgsHalt =>
      intro A W bound funs₂ W' hV hsc hb
      simp [scopedCode, scopedExpr, exprHasCall] at hsc
  | @argsNil funs V st =>
      intro A W bound funs₂ W' hV hsc hb
      exact ⟨_, Step.argsNil, .eres _⟩
  | @argsCons funs V st e rest restvals st1 v st2 hrest he ihrest ihe =>
      intro A W bound funs₂ W' hV hsc hb
      unfold scopedCode scopedArgs at hsc
      rw [Bool.and_eq_true] at hsc
      obtain ⟨res₂, hstep₁, htr₁⟩ := ihrest funs₂ W' hV hsc.2 hb
      obtain ⟨res₃, hstep₂, htr₂⟩ := ihe funs₂ W' hV hsc.1 hb
      cases htr₁ with
      | eres =>
          cases htr₂ with
          | eres => exact ⟨_, Step.argsCons hstep₁ hstep₂, .eres _⟩
  | @argsRestHalt funs V st e rest st1 hrest ihrest =>
      intro A W bound funs₂ W' hV hsc hb
      unfold scopedCode scopedArgs at hsc
      rw [Bool.and_eq_true] at hsc
      obtain ⟨res₂, hstep₁, htr₁⟩ := ihrest funs₂ W' hV hsc.2 hb
      cases htr₁ with
      | eres => exact ⟨_, Step.argsRestHalt hstep₁, .eres _⟩
  | @argsHeadHalt funs V st e rest restvals st1 st2 hrest he ihrest ihe =>
      intro A W bound funs₂ W' hV hsc hb
      unfold scopedCode scopedArgs at hsc
      rw [Bool.and_eq_true] at hsc
      obtain ⟨res₂, hstep₁, htr₁⟩ := ihrest funs₂ W' hV hsc.2 hb
      obtain ⟨res₃, hstep₂, htr₂⟩ := ihe funs₂ W' hV hsc.1 hb
      cases htr₁ with
      | eres =>
          cases htr₂ with
          | eres => exact ⟨_, Step.argsHeadHalt hstep₁ hstep₂, .eres _⟩
  | funDef =>
      intro A W bound funs₂ W' hV hsc hb
      simp [scopedCode, scopedStmt] at hsc
  | @block funs V st body Vb stb o hbody ihbody =>
      intro A W bound funs₂ W' hV hsc hb
      subst hV
      have hstmts : scopedStmts bound body = true := by
        simp only [scopedCode, scopedStmt] at hsc
        by_cases hc : scopedStmts bound body = true
        · exact hc
        · simp [hc] at hsc
      have hpost : postBound bound (Code.stmt (.block body)) = bound := by
        simp [postBound, scopedStmt, hstmts]
      obtain ⟨res₂, hstep, htr⟩ :=
        ihbody (hoist D body :: funs₂) W' rfl hstmts hb
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
      intro A W bound funs₂ W' hV hsc hb
      subst hV
      refine ⟨_, Step.letZero, ?_⟩
      rw [show bindZeros D vars ++ (A ++ W) = (bindZeros D vars ++ A) ++ W from
            (List.append_assoc _ _ _).symm,
          show bindZeros D vars ++ (A ++ W') = (bindZeros D vars ++ A) ++ W' from
            (List.append_assoc _ _ _).symm]
      refine .norm (fun x hx => ?_)
      have hpost : postBound bound (Code.stmt (.letDecl vars none)) = vars ++ bound := by
        simp [postBound, scopedStmt]
      rw [hpost] at hx
      rw [List.map_append, bindZeros_keys]
      rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_append.mpr (Or.inl hx)
      · exact List.mem_append.mpr (Or.inr (hb x hx))
  | @letVal funs V st vars e vals st1 he hlen ihe =>
      intro A W bound funs₂ W' hV hsc hb
      subst hV
      have hse : scopedExpr bound e = true := by
        simp only [scopedCode, scopedStmt] at hsc
        by_cases hc : scopedExpr bound e = true
        · exact hc
        · simp [hc] at hsc
      obtain ⟨res₂, hstep, htr⟩ := ihe funs₂ W' rfl hse hb
      cases htr with
      | eres =>
          refine ⟨_, Step.letVal hstep hlen, ?_⟩
          rw [show vars.zip vals ++ (A ++ W) = (vars.zip vals ++ A) ++ W from
                (List.append_assoc _ _ _).symm,
              show vars.zip vals ++ (A ++ W') = (vars.zip vals ++ A) ++ W' from
                (List.append_assoc _ _ _).symm]
          refine .norm (fun x hx => ?_)
          have hpost : postBound bound (Code.stmt (.letDecl vars (some e))) =
              vars ++ bound := by
            simp [postBound, scopedStmt, hse]
          rw [hpost] at hx
          rw [List.map_append, List.map_fst_zip (by omega)]
          rcases List.mem_append.mp hx with hx | hx
          · exact List.mem_append.mpr (Or.inl hx)
          · exact List.mem_append.mpr (Or.inr (hb x hx))
  | @letHalt funs V st vars e st1 he ihe =>
      intro A W bound funs₂ W' hV hsc hb
      subst hV
      have hse : scopedExpr bound e = true := by
        simp only [scopedCode, scopedStmt] at hsc
        by_cases hc : scopedExpr bound e = true
        · exact hc
        · simp [hc] at hsc
      obtain ⟨res₂, hstep, htr⟩ := ihe funs₂ W' rfl hse hb
      cases htr with
      | eres => exact ⟨_, Step.letHalt hstep, .halt⟩
  | @assignVal funs V st vars e vals st1 he hlen ihe =>
      intro A W bound funs₂ W' hV hsc hb
      subst hV
      have hsc' : vars.all bound.contains = true ∧ scopedExpr bound e = true := by
        simp only [scopedCode, scopedStmt] at hsc
        by_cases hc : (vars.all bound.contains && scopedExpr bound e) = true
        · rw [Bool.and_eq_true] at hc
          exact hc
        · simp [hc] at hsc
      have hvars : ∀ x ∈ vars, x ∈ A.map Prod.fst := fun x hx =>
        hb x (all_contains_subset hsc'.1 x hx)
      obtain ⟨res₂, hstep, htr⟩ := ihe funs₂ W' rfl hsc'.2 hb
      cases htr with
      | eres =>
          refine ⟨_, Step.assignVal hstep hlen, ?_⟩
          rw [VEnv.setMany_append_mem hvars, VEnv.setMany_append_mem hvars]
          refine .norm (fun x hx => ?_)
          have hpost : postBound bound (Code.stmt (.assign vars e)) = bound := by
            simp [postBound, scopedStmt, hsc'.1, hsc'.2]
          rw [hpost] at hx
          rw [VEnv.setMany_keys]
          exact hb x hx
  | @assignHalt funs V st vars e st1 he ihe =>
      intro A W bound funs₂ W' hV hsc hb
      subst hV
      have hse : scopedExpr bound e = true := by
        simp only [scopedCode, scopedStmt] at hsc
        by_cases hc : (vars.all bound.contains && scopedExpr bound e) = true
        · rw [Bool.and_eq_true] at hc
          exact hc.2
        · simp [hc] at hsc
      obtain ⟨res₂, hstep, htr⟩ := ihe funs₂ W' rfl hse hb
      cases htr with
      | eres => exact ⟨_, Step.assignHalt hstep, .halt⟩
  | @exprStmt funs V st e st1 he ihe =>
      intro A W bound funs₂ W' hV hsc hb
      subst hV
      have hse : scopedExpr bound e = true := by
        simp only [scopedCode, scopedStmt] at hsc
        by_cases hc : scopedExpr bound e = true
        · exact hc
        · simp [hc] at hsc
      obtain ⟨res₂, hstep, htr⟩ := ihe funs₂ W' rfl hse hb
      cases htr with
      | eres =>
          refine ⟨_, Step.exprStmt hstep, ?_⟩
          refine .norm (fun x hx => ?_)
          have hpost : postBound bound (Code.stmt (.exprStmt e)) = bound := by
            simp [postBound, scopedStmt, hse]
          rw [hpost] at hx
          exact hb x hx
  | @exprStmtHalt funs V st e st1 he ihe =>
      intro A W bound funs₂ W' hV hsc hb
      subst hV
      have hse : scopedExpr bound e = true := by
        simp only [scopedCode, scopedStmt] at hsc
        by_cases hc : scopedExpr bound e = true
        · exact hc
        · simp [hc] at hsc
      obtain ⟨res₂, hstep, htr⟩ := ihe funs₂ W' rfl hse hb
      cases htr with
      | eres => exact ⟨_, Step.exprStmtHalt hstep, .halt⟩
  | @ifTrue funs V st c body cv st1 V' st2 o hc hcv hbody ihc ihbody =>
      intro A W bound funs₂ W' hV hsc hb
      subst hV
      have hsc' : scopedExpr bound c = true ∧ scopedStmts bound body = true := by
        simp only [scopedCode, scopedStmt] at hsc
        by_cases hcnd : (scopedExpr bound c && scopedStmts bound body) = true
        · rw [Bool.and_eq_true] at hcnd
          exact hcnd
        · simp [hcnd] at hsc
      obtain ⟨res₂, hstepc, htrc⟩ := ihc funs₂ W' rfl hsc'.1 hb
      have hscb : scopedCode bound (Code.stmt (.block body)) = true := by
        simp [scopedCode, scopedStmt, hsc'.2]
      obtain ⟨res₃, hstepb, htrb⟩ := ihbody funs₂ W' rfl hscb hb
      cases htrc with
      | eres =>
          have hpostb : postBound bound (Code.stmt (.block body)) = bound := by
            simp [postBound, scopedStmt, hsc'.2]
          have hpost : postBound bound (Code.stmt (.cond c body)) = bound := by
            simp [postBound, scopedStmt, hsc'.1, hsc'.2]
          rw [hpostb] at htrb
          rw [hpost]
          cases htrb with
          | norm hk => exact ⟨_, Step.ifTrue hstepc hcv hstepb, .norm hk⟩
          | halt => exact ⟨_, Step.ifTrue hstepc hcv hstepb, .halt⟩
  | @ifFalse funs V st c body cv st1 hc hcv ihc =>
      intro A W bound funs₂ W' hV hsc hb
      subst hV
      have hcnd : (scopedExpr bound c && scopedStmts bound body) = true := by
        simp only [scopedCode, scopedStmt] at hsc
        by_cases hcnd : (scopedExpr bound c && scopedStmts bound body) = true
        · exact hcnd
        · simp [hcnd] at hsc
      have hsc' : scopedExpr bound c = true := by
        rw [Bool.and_eq_true] at hcnd
        exact hcnd.1
      obtain ⟨res₂, hstepc, htrc⟩ := ihc funs₂ W' rfl hsc' hb
      cases htrc with
      | eres =>
          refine ⟨_, Step.ifFalse hstepc hcv, .norm (fun x hx => ?_)⟩
          exact hb x (by
            simpa [postBound, scopedStmt, hcnd] using hx)
  | @ifHalt funs V st c body st1 hc ihc =>
      intro A W bound funs₂ W' hV hsc hb
      subst hV
      have hsc' : scopedExpr bound c = true := by
        simp only [scopedCode, scopedStmt] at hsc
        by_cases hcnd : (scopedExpr bound c && scopedStmts bound body) = true
        · rw [Bool.and_eq_true] at hcnd
          exact hcnd.1
        · simp [hcnd] at hsc
      obtain ⟨res₂, hstepc, htrc⟩ := ihc funs₂ W' rfl hsc' hb
      cases htrc with
      | eres => exact ⟨_, Step.ifHalt hstepc, .halt⟩
  | @switchExec funs V st c cases' dflt cv st1 V' st2 o hc hsel ihc ihsel =>
      intro A W bound funs₂ W' hV hsc hb
      subst hV
      have hsc' : scopedExpr bound c = true ∧ scopedCases bound cases' = true ∧
          scopedDflt bound dflt = true := by
        simp only [scopedCode, scopedStmt] at hsc
        by_cases hcnd : (scopedExpr bound c && scopedCases bound cases' &&
            scopedDflt bound dflt) = true
        · rw [Bool.and_eq_true, Bool.and_eq_true] at hcnd
          exact ⟨hcnd.1.1, hcnd.1.2, hcnd.2⟩
        · simp [hcnd] at hsc
      obtain ⟨res₂, hstepc, htrc⟩ := ihc funs₂ W' rfl hsc'.1 hb
      have hsels : scopedStmts bound (selectSwitch D cv cases' dflt) = true :=
        scoped_selectSwitch hsc'.2.1 hsc'.2.2
      have hscb : scopedCode bound (Code.stmt (.block (selectSwitch D cv cases' dflt))) =
          true := by
        simp [scopedCode, scopedStmt, hsels]
      obtain ⟨res₃, hstepb, htrb⟩ := ihsel funs₂ W' rfl hscb hb
      cases htrc with
      | eres =>
          have hpostb : postBound bound
              (Code.stmt (.block (selectSwitch D cv cases' dflt))) = bound := by
            simp [postBound, scopedStmt, hsels]
          have hpost : postBound bound (Code.stmt (.switch c cases' dflt)) = bound := by
            simp [postBound, scopedStmt, hsc'.1, hsc'.2.1, hsc'.2.2]
          rw [hpostb] at htrb
          rw [hpost]
          cases htrb with
          | norm hk => exact ⟨_, Step.switchExec hstepc hstepb, .norm hk⟩
          | halt => exact ⟨_, Step.switchExec hstepc hstepb, .halt⟩
  | @switchHalt funs V st c cases' dflt st1 hc ihc =>
      intro A W bound funs₂ W' hV hsc hb
      subst hV
      have hsc' : scopedExpr bound c = true := by
        simp only [scopedCode, scopedStmt] at hsc
        by_cases hcnd : (scopedExpr bound c && scopedCases bound cases' &&
            scopedDflt bound dflt) = true
        · rw [Bool.and_eq_true, Bool.and_eq_true] at hcnd
          exact hcnd.1.1
        · simp [hcnd] at hsc
      obtain ⟨res₂, hstepc, htrc⟩ := ihc funs₂ W' rfl hsc' hb
      cases htrc with
      | eres => exact ⟨_, Step.switchHalt hstepc, .halt⟩
  | forLoop | forInitHalt =>
      intro A W bound funs₂ W' hV hsc hb
      simp [scopedCode, scopedStmt] at hsc
  | «break» | «continue» | leave =>
      intro A W bound funs₂ W' hV hsc hb
      simp [scopedCode, scopedStmt] at hsc
  | @seqNil funs V st =>
      intro A W bound funs₂ W' hV hsc hb
      subst hV
      exact ⟨_, Step.seqNil, .norm (fun x hx => by simp [postBound] at hx)⟩
  | @seqCons funs V st s rest V1 st1 V2 st2 o hs hrest ihs ihrest =>
      intro A W bound funs₂ W' hV hsc hb
      subst hV
      obtain ⟨bound₁, hstmt, hrest'⟩ := scopedStmts_cons_inv hsc
      obtain ⟨res₂, hstep₁, htr₁⟩ := ihs funs₂ W' rfl (by simp [scopedCode, hstmt]) hb
      have hpost₁ : postBound bound (Code.stmt s) = bound₁ := by
        simp [postBound, hstmt]
      rw [hpost₁] at htr₁
      cases htr₁ with
      | @norm A₁ st₁' hk =>
          obtain ⟨res₃, hstep₂, htr₂⟩ := ihrest funs₂ W' rfl hrest' hk
          cases htr₂ with
          | norm hk₂ => exact ⟨_, Step.seqCons hstep₁ hstep₂, .norm hk₂⟩
          | halt => exact ⟨_, Step.seqCons hstep₁ hstep₂, .halt⟩
  | @seqStop funs V st s rest V1 st1 o hs hne ihs =>
      intro A W bound funs₂ W' hV hsc hb
      subst hV
      obtain ⟨bound₁, hstmt, hrest'⟩ := scopedStmts_cons_inv hsc
      obtain ⟨res₂, hstep₁, htr₁⟩ := ihs funs₂ W' rfl (by simp [scopedCode, hstmt]) hb
      cases htr₁ with
      | norm hk => exact absurd rfl hne
      | halt => exact ⟨_, Step.seqStop hstep₁ (by simp), .halt⟩
  | loopDone | loopCondHalt | loopStep | loopPostHalt | loopBreak | loopLeave
  | loopBodyHalt =>
      intro A W bound funs₂ W' hV hsc hb
      simp [scopedCode] at hsc

/-! ### Call-free expression transfer

Argument expressions at an inline site are call-free (`siteOK`) but read
arbitrary caller variables, so `scoped_transfer` does not apply; instead their
evaluation transfers to any environment that *agrees on the variables they
read* — and to any function environment. -/

/-- The transfer condition of `exprNoCall_transfer`: call-free code whose
reads the two environments agree on. -/
def NoCallAgrees (V V₂ : VEnv D) : Code Op → Prop
  | .expr e => exprHasCall e = false ∧
      ∀ y ∈ exprVars e, VEnv.get V₂ y = VEnv.get V y
  | .args es => argsHaveCall es = false ∧
      ∀ y ∈ varsList es, VEnv.get V₂ y = VEnv.get V y
  | _ => False

/-- Evaluation of call-free expression/argument code transfers to any function
environment and any read-agreeing variable environment. -/
theorem exprNoCall_transfer {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    {code : Code Op} {res : Res D} (h : Step D funs V st code res) :
    ∀ {V₂ : VEnv D} (funs₂ : FunEnv D),
      NoCallAgrees (calls := calls) (creates := creates) V V₂ code →
      Step D funs₂ V₂ st code res := by
  induction h with
  | lit =>
      intro V₂ funs₂ hc
      exact Step.lit
  | @var funs V st x v hv =>
      intro V₂ funs₂ hc
      obtain ⟨-, hag⟩ := hc
      refine Step.var ?_
      rw [hag x (by simp [exprVars])]
      exact hv
  | @builtinOk funs V st op args argvals st1 rets st2 ha hbi iha =>
      intro V₂ funs₂ hc
      obtain ⟨hnc, hag⟩ := hc
      exact Step.builtinOk (iha funs₂ ⟨hnc, hag⟩) hbi
  | @builtinHalt funs V st op args argvals st1 st2 ha hbi iha =>
      intro V₂ funs₂ hc
      obtain ⟨hnc, hag⟩ := hc
      exact Step.builtinHalt (iha funs₂ ⟨hnc, hag⟩) hbi
  | @builtinArgsHalt funs V st op args st1 ha iha =>
      intro V₂ funs₂ hc
      obtain ⟨hnc, hag⟩ := hc
      exact Step.builtinArgsHalt (iha funs₂ ⟨hnc, hag⟩)
  | callOk | callHalt | callArgsHalt =>
      intro V₂ funs₂ hc
      obtain ⟨hnc, -⟩ := hc
      simp [exprHasCall] at hnc
  | argsNil =>
      intro V₂ funs₂ hc
      exact Step.argsNil
  | @argsCons funs V st e rest restvals st1 v st2 hrest he ihrest ihe =>
      intro V₂ funs₂ hc
      obtain ⟨hnc, hvars⟩ := hc
      rw [show argsHaveCall (e :: rest) = (exprHasCall e || argsHaveCall rest) from rfl,
        Bool.or_eq_false_iff] at hnc
      rw [show varsList (e :: rest) = exprVars e ++ varsList rest from rfl] at hvars
      exact Step.argsCons
        (ihrest funs₂ ⟨hnc.2, fun y hy => hvars y (List.mem_append.mpr (Or.inr hy))⟩)
        (ihe funs₂ ⟨hnc.1, fun y hy => hvars y (List.mem_append.mpr (Or.inl hy))⟩)
  | @argsRestHalt funs V st e rest st1 hrest ihrest =>
      intro V₂ funs₂ hc
      obtain ⟨hnc, hvars⟩ := hc
      rw [show argsHaveCall (e :: rest) = (exprHasCall e || argsHaveCall rest) from rfl,
        Bool.or_eq_false_iff] at hnc
      rw [show varsList (e :: rest) = exprVars e ++ varsList rest from rfl] at hvars
      exact Step.argsRestHalt
        (ihrest funs₂ ⟨hnc.2, fun y hy => hvars y (List.mem_append.mpr (Or.inr hy))⟩)
  | @argsHeadHalt funs V st e rest restvals st1 st2 hrest he ihrest ihe =>
      intro V₂ funs₂ hc
      obtain ⟨hnc, hvars⟩ := hc
      rw [show argsHaveCall (e :: rest) = (exprHasCall e || argsHaveCall rest) from rfl,
        Bool.or_eq_false_iff] at hnc
      rw [show varsList (e :: rest) = exprVars e ++ varsList rest from rfl] at hvars
      exact Step.argsHeadHalt
        (ihrest funs₂ ⟨hnc.2, fun y hy => hvars y (List.mem_append.mpr (Or.inr hy))⟩)
        (ihe funs₂ ⟨hnc.1, fun y hy => hvars y (List.mem_append.mpr (Or.inl hy))⟩)
  | funDef | block | letZero | letVal | letHalt | assignVal | assignHalt
  | exprStmt | exprStmtHalt | ifTrue | ifFalse | ifHalt | switchExec | switchHalt
  | forLoop | forInitHalt | «break» | «continue» | leave | seqNil | seqCons
  | seqStop | loopDone | loopCondHalt | loopStep | loopPostHalt | loopBreak
  | loopLeave | loopBodyHalt =>
      intro V₂ funs₂ hc
      exact absurd hc (by simp [NoCallAgrees])

/-- Argument evaluation produces one value per argument. -/
theorem args_length {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    {as : List (Expr Op)} {vs : List U256} {st1 : EvmState}
    (h : Step D funs V st (.args as) (.eres (.vals vs st1))) :
    vs.length = as.length := by
  induction as generalizing vs st st1 with
  | nil => cases h with | argsNil => rfl
  | cons e rest ih =>
      cases h with
      | argsCons hrest he => simpa using ih hrest

/-! ### Trailing `leave` normalization -/

/-- `hoist` ignores a trailing `leave`. -/
theorem hoist_append_leave (ss : List (Stmt Op)) :
    hoist D (ss ++ [.leave]) = hoist D ss := by
  rw [hoist_append]
  simp [hoist]

/-- Executions of a body with a trailing `leave` are executions of the body
without it: `leave` becomes `normal`, everything else was an early stop. -/
theorem block_trailing_leave_fwd {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    {ss : List (Stmt Op)} {Vr : VEnv D} {st' : EvmState} {o : Outcome}
    (h : Step D funs V st (.stmt (.block (ss ++ [.leave]))) (.sres Vr st' o)) :
    ∃ o', Step D funs V st (.stmt (.block ss)) (.sres Vr st' o') ∧
      ((o = .leave ∧ o' = .normal) ∨ (o = o' ∧ o' ≠ .normal)) := by
  cases h with
  | block hb =>
      rw [hoist_append_leave] at hb
      rcases stmts_append_fwd hb with ⟨V1, st1, hpre, hsuf⟩ | ⟨hne, hpre⟩
      · cases hsuf with
        | seqCons hl _ => cases hl
        | seqStop hl hne =>
            cases hl with
            | leave =>
                exact ⟨.normal, Step.block hpre, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨o, Step.block hpre, Or.inr ⟨rfl, hne⟩⟩

/-- Converse: re-attach the trailing `leave`. -/
theorem block_trailing_leave_bwd {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    {ss : List (Stmt Op)} {Vr : VEnv D} {st' : EvmState} {o' : Outcome}
    (h : Step D funs V st (.stmt (.block ss)) (.sres Vr st' o')) :
    Step D funs V st (.stmt (.block (ss ++ [.leave])))
      (.sres Vr st' (if o' = .normal then .leave else o')) := by
  cases h with
  | block hb =>
      refine Step.block ?_
      rw [hoist_append_leave]
      by_cases ho : o' = .normal
      · subst ho
        exact stmts_append_normal hb (Step.seqStop Step.leave (by simp))
      · rw [if_neg ho]
        exact stmts_append_early hb ho

/-! ### Sequential-assignment characterizations -/

/-- A `setMany` through a head binding it never targets. -/
theorem VEnv.setMany_cons_not_mem {x : Ident} {v : U256} {R : VEnv D}
    {xs : List Ident} (hx : x ∉ xs) (vs : List U256) :
    VEnv.setMany ((x, v) :: R) xs vs = (x, v) :: VEnv.setMany R xs vs := by
  unfold VEnv.setMany
  induction xs generalizing vs R with
  | nil => rfl
  | cons y rest ih =>
      cases vs with
      | nil => rfl
      | cons w wrest =>
          simp only [List.zip_cons_cons, List.foldl_cons]
          have hxy : ¬(x = y) := fun hh => hx (hh ▸ List.mem_cons_self ..)
          rw [show VEnv.set ((x, v) :: R) y w = (x, v) :: VEnv.set R y w by
            simp only [VEnv.set, if_neg hxy]]
          exact ih (fun hh => hx (List.mem_cons_of_mem _ hh)) wrest

/-- Assigning through freshly zero-bound names lands exactly on them. -/
theorem VEnv.setMany_bindZeros {xs : List Ident} (hnd : xs.Nodup)
    {vs : List U256} (hlen : vs.length = xs.length) (V : VEnv D) :
    VEnv.setMany (bindZeros D xs ++ V) xs vs = xs.zip vs ++ V := by
  induction xs generalizing vs with
  | nil => cases vs with | nil => rfl | cons v vs => rfl
  | cons x rest ih =>
      cases vs with
      | nil => simp at hlen
      | cons v vrest =>
          have hx : x ∉ rest := (List.nodup_cons.mp hnd).1
          have hnd' : rest.Nodup := (List.nodup_cons.mp hnd).2
          show VEnv.setMany
              ((x, (evmWithExternal calls creates).zero) :: (bindZeros D rest ++ V))
              (x :: rest) (v :: vrest) = (x, v) :: rest.zip vrest ++ V
          unfold VEnv.setMany
          simp only [List.zip_cons_cons, List.foldl_cons]
          rw [show VEnv.set
              ((x, (evmWithExternal calls creates).zero) :: (bindZeros D rest ++ V)) x v =
            (x, v) :: (bindZeros D rest ++ V) by simp [VEnv.set]]
          have := VEnv.setMany_cons_not_mem (calls := calls) (creates := creates)
            (x := x) (v := v) (R := bindZeros D rest ++ V) hx vrest
          unfold VEnv.setMany at this
          rw [this]
          congr 1
          have := ih hnd' (by simpa using hlen)
          unfold VEnv.setMany at this
          exact this

/-- A block statement restores its entry keys and length. -/
theorem block_stmt_shape {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    {body : Block Op} {Vr : VEnv D} {st' : EvmState} {o : Outcome}
    (h : Step D funs V st (.stmt (.block body)) (.sres Vr st' o)) :
    Vr.map Prod.fst = V.map Prod.fst ∧ Vr.length = V.length := by
  cases h with
  | block hb =>
      exact ⟨restore_keys (venvKeys_suffix hb rfl) (venvLen_mono hb rfl),
        restore_length (venvLen_mono hb rfl)⟩

/-! ### The inlined argument bindings -/

/-- Keys of a zip are its first components (given enough values). -/
theorem zip_keys {ps : List Ident} {vs : List U256} (h : ps.length ≤ vs.length) :
    (ps.zip vs).map Prod.fst = ps :=
  List.map_fst_zip h

/-- `argsShadowOK`'s per-argument return-name component, at the list level. -/
theorem argsShadowOK_rs {rs : List Ident} :
    ∀ {pairs : List (Ident × Expr Op)}, argsShadowOK rs pairs = true →
      ∀ y ∈ varsList (pairs.map Prod.snd), y ∉ rs := by
  intro pairs
  induction pairs with
  | nil => intro _ y hy; simp [varsList] at hy
  | cons pa rest ih =>
      intro h y hy
      unfold argsShadowOK at h
      rw [Bool.and_eq_true] at h
      rw [List.map_cons, show varsList (pa.2 :: rest.map Prod.snd) =
        exprVars pa.2 ++ varsList (rest.map Prod.snd) from rfl] at hy
      rcases List.mem_append.mp hy with hy | hy
      · have := List.all_eq_true.mp h.1 y hy
        rw [Bool.and_eq_true] at this
        simpa using this.2
      · exact ih h.2 y hy

/-- Sequential `let`-bindings reproduce right-to-left argument evaluation:
from `N ++ V` (the freshly bound return/`xs` zone on the caller env), the
reversed parameter `let`s land exactly on the `callOk` parameter frame. -/
theorem argLets_fwd {rs : List Ident} :
    ∀ {ps : List Ident} {as : List (Expr Op)} {argvals : List U256}
      {funs : FunEnv D} {V : VEnv D} {st st1 : EvmState},
      Step D funs V st (.args as) (.eres (.vals argvals st1)) →
      ps.length = as.length →
      argsHaveCall as = false →
      argsShadowOK rs (ps.zip as) = true →
      ∀ {N : VEnv D}, (∀ y ∈ varsList as, y ∉ N.map Prod.fst) →
      ∀ (funs₂ : FunEnv D),
      Step D funs₂ (N ++ V) st
        (.stmts ((ps.zip as).reverse.map (fun pa => .letDecl [pa.1] (some pa.2))))
        (.sres (ps.zip argvals ++ (N ++ V)) st1 .normal) := by
  intro ps as
  induction as generalizing ps with
  | nil =>
      intro argvals funs V st st1 h hlen hnc hsh N hN funs₂
      cases ps with
      | nil =>
          cases h with
          | argsNil => simpa using Step.seqNil
      | cons p ps' => simp at hlen
  | cons a as' ih =>
      intro argvals funs V st st1 h hlen hnc hsh N hN funs₂
      cases ps with
      | nil => simp at hlen
      | cons p ps' =>
          cases h with
          | @argsCons _ _ _ _ _ restvals st1' v _ hrest ha =>
              rw [show argsHaveCall (a :: as') =
                (exprHasCall a || argsHaveCall as') from rfl,
                Bool.or_eq_false_iff] at hnc
              rw [List.zip_cons_cons] at hsh ⊢
              unfold argsShadowOK at hsh
              rw [Bool.and_eq_true] at hsh
              have hNrest : ∀ y ∈ varsList as', y ∉ N.map Prod.fst := fun y hy =>
                hN y (by
                  rw [show varsList (a :: as') = exprVars a ++ varsList as' from rfl]
                  exact List.mem_append.mpr (Or.inr hy))
              have hpre := ih hrest (by simpa using hlen) hnc.2 hsh.2 hNrest funs₂
              have hrestlen : restvals.length = as'.length := args_length hrest
              rw [List.reverse_cons, List.map_append]
              refine stmts_append_normal hpre ?_
              have hagree : ∀ y ∈ exprVars a,
                  VEnv.get (ps'.zip restvals ++ (N ++ V)) y = VEnv.get V y := by
                intro y hy
                have hsha := List.all_eq_true.mp hsh.1 y hy
                rw [Bool.and_eq_true] at hsha
                have hlen' : ps'.length = as'.length := by simpa using hlen
                have hyp : y ∉ (ps'.zip restvals).map Prod.fst := by
                  rw [List.map_fst_zip (by omega : ps'.length ≤ restvals.length)]
                  have h1 := hsha.1
                  rw [List.map_fst_zip (le_of_eq hlen')] at h1
                  simpa using h1
                have hyN : y ∉ N.map Prod.fst := hN y (by
                  rw [show varsList (a :: as') = exprVars a ++ varsList as' from rfl]
                  exact List.mem_append.mpr (Or.inl hy))
                rw [VEnv.get_append_not_mem hyp, VEnv.get_append_not_mem hyN]
              have ha₂ : Step D funs₂ (ps'.zip restvals ++ (N ++ V)) st1'
                  (.expr a) (.eres (.vals [v] st1)) :=
                exprNoCall_transfer ha funs₂ ⟨hnc.1, hagree⟩
              refine Step.seqCons (Step.letVal ha₂ rfl) ?_
              rw [show [p].zip [v] = [(p, v)] from rfl]
              rw [show ([(p, v)] : VEnv D) ++ (ps'.zip restvals ++ (N ++ V)) =
                (p, v) :: ps'.zip restvals ++ (N ++ V) from rfl]
              exact Step.seqNil

/-- Halting argument evaluation halts the `let` sequence, keeping the base
environment as a suffix. -/
theorem argLets_halt_fwd {rs : List Ident} :
    ∀ {ps : List Ident} {as : List (Expr Op)}
      {funs : FunEnv D} {V : VEnv D} {st st1 : EvmState},
      Step D funs V st (.args as) (.eres (.halt st1)) →
      ps.length = as.length →
      argsHaveCall as = false →
      argsShadowOK rs (ps.zip as) = true →
      ∀ {N : VEnv D}, (∀ y ∈ varsList as, y ∉ N.map Prod.fst) →
      ∀ (funs₂ : FunEnv D),
      ∃ P : VEnv D, Step D funs₂ (N ++ V) st
        (.stmts ((ps.zip as).reverse.map (fun pa => .letDecl [pa.1] (some pa.2))))
        (.sres (P ++ (N ++ V)) st1 .halt) := by
  intro ps as
  induction as generalizing ps with
  | nil =>
      intro funs V st st1 h hlen hnc hsh N hN funs₂
      cases h
  | cons a as' ih =>
      intro funs V st st1 h hlen hnc hsh N hN funs₂
      cases ps with
      | nil => simp at hlen
      | cons p ps' =>
          rw [show argsHaveCall (a :: as') =
            (exprHasCall a || argsHaveCall as') from rfl,
            Bool.or_eq_false_iff] at hnc
          rw [List.zip_cons_cons] at hsh ⊢
          unfold argsShadowOK at hsh
          rw [Bool.and_eq_true] at hsh
          have hNrest : ∀ y ∈ varsList as', y ∉ N.map Prod.fst := fun y hy =>
            hN y (by
              rw [show varsList (a :: as') = exprVars a ++ varsList as' from rfl]
              exact List.mem_append.mpr (Or.inr hy))
          rw [List.reverse_cons, List.map_append]
          cases h with
          | @argsRestHalt _ _ _ _ _ _ hrest =>
              obtain ⟨P, hpre⟩ := ih hrest (by simpa using hlen) hnc.2 hsh.2
                hNrest funs₂
              exact ⟨P, stmts_append_early hpre (by simp)⟩
          | @argsHeadHalt _ _ _ _ _ restvals st1' _ hrest ha =>
              have hpre := argLets_fwd (rs := rs) hrest (by simpa using hlen)
                hnc.2 hsh.2 hNrest funs₂
              have hrestlen : restvals.length = as'.length := args_length hrest
              have hagree : ∀ y ∈ exprVars a,
                  VEnv.get (ps'.zip restvals ++ (N ++ V)) y = VEnv.get V y := by
                intro y hy
                have hsha := List.all_eq_true.mp hsh.1 y hy
                rw [Bool.and_eq_true] at hsha
                have hlen' : ps'.length = as'.length := by simpa using hlen
                have hyp : y ∉ (ps'.zip restvals).map Prod.fst := by
                  rw [List.map_fst_zip (by omega : ps'.length ≤ restvals.length)]
                  have h1 := hsha.1
                  rw [List.map_fst_zip (le_of_eq hlen')] at h1
                  simpa using h1
                have hyN : y ∉ N.map Prod.fst := hN y (by
                  rw [show varsList (a :: as') = exprVars a ++ varsList as' from rfl]
                  exact List.mem_append.mpr (Or.inl hy))
                rw [VEnv.get_append_not_mem hyp, VEnv.get_append_not_mem hyN]
              have ha₂ : Step D funs₂ (ps'.zip restvals ++ (N ++ V)) st1'
                  (.expr a) (.eres (.halt st1)) :=
                exprNoCall_transfer ha funs₂ ⟨hnc.1, hagree⟩
              refine ⟨ps'.zip restvals, stmts_append_normal hpre ?_⟩
              exact Step.seqStop (Step.letHalt ha₂) (by simp)

/-! ### The return read-out -/

/-- The trailing `x := r` assignments read the callee frame and write through
it into the caller zone. -/
theorem assigns_fwd {A' : VEnv D} :
    ∀ {xs rs : List Ident},
      (∀ r ∈ rs, r ∈ A'.map Prod.fst) →
      (∀ x ∈ xs, x ∉ A'.map Prod.fst) →
      xs.length = rs.length →
      ∀ (funs : FunEnv D) (Wb : VEnv D) (st : EvmState),
      Step D funs (A' ++ Wb) st
        (.stmts ((xs.zip rs).map (fun xr => .assign [xr.1] (.var xr.2))))
        (.sres (A' ++ VEnv.setMany Wb xs (rs.map
          (fun r => (VEnv.get A' r).getD (evmWithExternal calls creates).zero)))
          st .normal) := by
  intro xs
  induction xs with
  | nil =>
      intro rs hr hx hlen funs Wb st
      cases rs with
      | nil => simpa [VEnv.setMany] using Step.seqNil
      | cons r rs' => simp at hlen
  | cons x xs' ih =>
      intro rs hr hx hlen funs Wb st
      cases rs with
      | nil => simp at hlen
      | cons r rs' =>
          rw [List.zip_cons_cons, List.map_cons]
          have hrA : r ∈ A'.map Prod.fst := hr r (by simp)
          obtain ⟨v, hv⟩ : ∃ v, VEnv.get A' r = some v := by
            have := VEnv.find?_key_isSome (calls := calls) (creates := creates) hrA
            obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp this
            exact ⟨p.2, by unfold VEnv.get; rw [hp]; rfl⟩
          have hgv : VEnv.get (A' ++ Wb) r = some v := by
            rw [VEnv.get_append_mem hrA]; exact hv
          have hset : VEnv.setMany (A' ++ Wb) [x] [v] = A' ++ VEnv.set Wb x v := by
            rw [VEnv.setMany_singleton]
            exact VEnv.set_append_not_mem (hx x (by simp)) Wb v
          have hstep : Step D funs (A' ++ Wb) st
              (.stmt (.assign [x] (.var r)))
              (.sres (VEnv.setMany (A' ++ Wb) [x] [v]) st .normal) :=
            Step.assignVal (Step.var hgv) (by simp)
          rw [hset] at hstep
          have hrest := ih (fun r' hr' => hr r' (List.mem_cons_of_mem _ hr'))
            (fun x' hx' => hx x' (List.mem_cons_of_mem _ hx'))
            (by simpa using hlen) funs (VEnv.set Wb x v) st
          have hmany : VEnv.setMany Wb (x :: xs') ((r :: rs').map
              (fun r => (VEnv.get A' r).getD (evmWithExternal calls creates).zero)) =
              VEnv.setMany (VEnv.set Wb x v) xs' (rs'.map
                (fun r => (VEnv.get A' r).getD (evmWithExternal calls creates).zero)) := by
            rw [List.map_cons, hv]
            rfl
          rw [hmany]
          exact Step.seqCons hstep hrest

/-! ### `TRes` inversions and remaining glue -/

/-- Invert a `normal` transfer result. -/
theorem TRes.norm_inv {W W' : VEnv D} {post : List Ident} {V₁ : VEnv D}
    {st₁ : EvmState} {res₂ : Res D}
    (h : TRes (calls := calls) (creates := creates) W W' post
      (.sres V₁ st₁ .normal) res₂) :
    ∃ A', V₁ = A' ++ W ∧ res₂ = .sres (A' ++ W') st₁ .normal ∧
      (∀ x ∈ post, x ∈ A'.map Prod.fst) := by
  cases h with
  | norm hk => exact ⟨_, rfl, rfl, hk⟩

/-- Invert a `halt` transfer result. -/
theorem TRes.halt_inv {W W' : VEnv D} {post : List Ident} {V₁ : VEnv D}
    {st₁ : EvmState} {res₂ : Res D}
    (h : TRes (calls := calls) (creates := creates) W W' post
      (.sres V₁ st₁ .halt) res₂) :
    ∃ A', V₁ = A' ++ W ∧ res₂ = .sres (A' ++ W') st₁ .halt := by
  cases h with
  | halt => exact ⟨_, rfl, rfl⟩

/-- `restore` to a base of the extension's length peels the top exactly. -/
theorem restore_exact {W Y W' : VEnv D} (h : W'.length = W.length) :
    restore W (Y ++ W') = W' := by
  simp only [restore, List.length_append]
  rw [show Y.length + W'.length - W.length = Y.length by omega]
  exact List.drop_left

/-- Equal-length prefixes of equal appends are equal. -/
theorem append_cancel_of_length {α : Type _} {a b c d : List α}
    (h : a ++ b = c ++ d) (hl : a.length = c.length) : a = c ∧ b = d :=
  List.append_inj h hl

/-- `siteOK` unpacked. -/
theorem siteOK_inv {d : IDecl} {xs : List Ident} {as : List (Expr Op)}
    {isLet : Bool} (h : siteOK d xs as isLet = true) :
    as.length = d.ps.length ∧ xs.length = d.rs.length ∧ xs.Nodup ∧
    argsHaveCall as = false ∧ argsShadowOK d.rs (d.ps.zip as) = true ∧
    (∀ x ∈ xs, x ∉ d.ps ++ d.rs) ∧
    (isLet = true → ∀ y ∈ varsList as, y ∉ xs) := by
  unfold siteOK at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨by simpa using h1, by simpa using h2, by simpa using h3,
    by simpa using h4, h5, ?_, ?_⟩
  · intro x hx
    have := List.all_eq_true.mp h6 x hx
    simpa using this
  · intro hl y hy
    rw [hl] at h7
    have h7' : ∀ x ∈ varsList as, x ∉ xs := by simpa using h7
    exact h7' y hy

/-- `classifyDecl` unpacked. -/
theorem classifyDecl_inv {ps rs : List Ident} {body : Block Op} {d : IDecl}
    (h : classifyDecl ps rs body = some d) :
    d.ps = ps ∧ d.rs = rs ∧ (ps ++ rs).Nodup ∧
    scopedStmts (ps ++ rs) d.ss = true ∧
    (body = d.ss ∨ body = d.ss ++ [.leave]) := by
  unfold classifyDecl at h
  split at h
  · next hc =>
      rw [Bool.and_eq_true] at hc
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
  · cases h

/-! ### The core inline lemmas (forward) -/

/-- Second components of an exact zip. -/
theorem zip_snds : ∀ {ps : List Ident} {as : List (Expr Op)},
    ps.length = as.length → (ps.zip as).map Prod.snd = as := by
  intro ps
  induction ps with
  | nil =>
      intro as h
      cases as with
      | nil => rfl
      | cons a as' => simp at h
  | cons p ps' ih =>
      intro as h
      cases as with
      | nil => simp at h
      | cons a as' =>
          rw [List.zip_cons_cons, List.map_cons, ih (by simpa using h)]

/-- The callee frame's keys are its parameter and return names. -/
theorem calleeFrame_keys {d : IDecl} {argvals : List U256}
    (hlen : d.ps.length ≤ argvals.length) :
    (d.ps.zip argvals ++ bindZeros D d.rs).map Prod.fst = d.ps ++ d.rs := by
  rw [List.map_append, zip_keys hlen, bindZeros_keys]

/-- **Forward, normal path**: from the call's constituents — argument
evaluation, callee body run to `normal` — the inlined core runs to exactly the
sequential-assignment environment. -/
theorem inlineCore_fwd_normal {d : IDecl} {xs : List Ident} {as : List (Expr Op)}
    (hnd : (d.ps ++ d.rs).Nodup)
    (hsc : scopedStmts (d.ps ++ d.rs) d.ss = true)
    (hlen_as : as.length = d.ps.length)
    (hnc : argsHaveCall as = false)
    (hsh : argsShadowOK d.rs (d.ps.zip as) = true)
    (hxout : ∀ x ∈ xs, x ∉ d.ps ++ d.rs)
    (hlen_xs : xs.length = d.rs.length)
    {funs cenv : FunEnv D} {V Z : VEnv D} {st st1 st2 : EvmState}
    {argvals : List U256} {Vend : VEnv D}
    (hargs : Step D funs V st (.args as) (.eres (.vals argvals st1)))
    (hbody : Step D cenv (d.ps.zip argvals ++ bindZeros D d.rs) st1
      (.stmt (.block d.ss)) (.sres Vend st2 .normal))
    (hZ : ∀ y ∈ varsList as, y ∉ Z.map Prod.fst)
    (funs₂ : FunEnv D) :
    Step D funs₂ (Z ++ V) st (.stmt (inlineCore d xs as))
      (.sres (VEnv.setMany (Z ++ V) xs (d.rs.map
        (fun r => (VEnv.get Vend r).getD (evmWithExternal calls creates).zero)))
        st2 .normal) := by
  have hvlen : argvals.length = as.length := args_length hargs
  have hpslen : d.ps.length ≤ argvals.length := by omega
  set A₀ : VEnv D := d.ps.zip argvals ++ bindZeros D d.rs with hA₀
  have hA₀keys : A₀.map Prod.fst = d.ps ++ d.rs := calleeFrame_keys hpslen
  set funs' : FunEnv D := hoist D
    ([Stmt.letDecl d.rs none]
      ++ ((d.ps.zip as).reverse.map (fun pa => Stmt.letDecl [pa.1] (some pa.2)))
      ++ [Stmt.block d.ss]
      ++ (xs.zip d.rs).map (fun xr => Stmt.assign [xr.1] (Expr.var xr.2))) :: funs₂
    with hfuns'
  -- 1. the return zero-inits
  have s1 : Step D funs' (Z ++ V) st (.stmt (.letDecl d.rs none))
      (.sres (bindZeros D d.rs ++ (Z ++ V)) st .normal) := Step.letZero
  -- 2. the argument lets
  have hN : ∀ y ∈ varsList as, y ∉ (bindZeros D d.rs ++ Z).map Prod.fst := by
    intro y hy
    rw [List.map_append, bindZeros_keys]
    intro hmem
    rcases List.mem_append.mp hmem with hm | hm
    · have hrs := argsShadowOK_rs hsh y
      rw [zip_snds hlen_as.symm] at hrs
      exact hrs hy hm
    · exact hZ y hy hm
  have s2 := argLets_fwd (rs := d.rs) hargs hlen_as.symm hnc hsh hN funs'
  -- 3. the body, transferred onto the caller environment
  have hscode : scopedCode (d.ps ++ d.rs) (Code.stmt (.block d.ss)) = true := by
    simp [scopedCode, scopedStmt, hsc]
  have hbound : ∀ x ∈ d.ps ++ d.rs, x ∈ A₀.map Prod.fst := by
    intro x hx; rw [hA₀keys]; exact hx
  obtain ⟨res₂, hstepb, htr⟩ := scoped_transfer hbody
    (A := A₀) (W := ([] : VEnv D)) (bound := d.ps ++ d.rs) funs' (Z ++ V)
    (by simp) hscode hbound
  obtain ⟨A'', hVend, hres₂, hk⟩ := TRes.norm_inv htr
  have hVend' : Vend = A'' := by simpa using hVend
  subst hres₂
  -- the transferred body's frame keeps the callee frame's keys
  have hshape := block_stmt_shape hstepb
  have hkeysA'' : A''.map Prod.fst = d.ps ++ d.rs := by
    have hlA : A''.length = A₀.length := by
      have := hshape.2
      simp only [List.length_append] at this
      omega
    have hkk : A''.map Prod.fst = A₀.map Prod.fst := by
      have := hshape.1
      simp only [List.map_append] at this
      simpa [List.append_assoc] using this
    exact hkk.trans hA₀keys
  have hpost : postBound (d.ps ++ d.rs) (Code.stmt (.block d.ss)) =
      d.ps ++ d.rs := by
    simp [postBound, scopedStmt, hsc]
  rw [hpost] at hk
  -- 4. the read-out assignments
  have s4 := assigns_fwd (A' := A'')
    (fun r hr => by rw [hkeysA'']; exact List.mem_append.mpr (Or.inr hr))
    (fun x hx => by rw [hkeysA'']; exact hxout x hx)
    hlen_xs funs' (Z ++ V) st2
  -- assemble the block
  set argLets : List (Stmt Op) :=
    (d.ps.zip as).reverse.map (fun pa => Stmt.letDecl [pa.1] (some pa.2)) with hargLets
  set assignsL : List (Stmt Op) :=
    (xs.zip d.rs).map (fun xr => Stmt.assign [xr.1] (Expr.var xr.2)) with hassignsL
  have c1 : Step D funs' (Z ++ V) st (.stmts [Stmt.letDecl d.rs none])
      (.sres (bindZeros D d.rs ++ (Z ++ V)) st .normal) :=
    Step.seqCons s1 Step.seqNil
  have s2' : Step D funs' (bindZeros D d.rs ++ (Z ++ V)) st (.stmts argLets)
      (.sres (d.ps.zip argvals ++ (bindZeros D d.rs ++ (Z ++ V))) st1 .normal) := by
    have h := s2
    rw [show (bindZeros D d.rs ++ Z) ++ V = bindZeros D d.rs ++ (Z ++ V) from
      List.append_assoc _ _ _] at h
    exact h
  have c2 : Step D funs' (Z ++ V) st
      (.stmts ([Stmt.letDecl d.rs none] ++ argLets))
      (.sres (d.ps.zip argvals ++ (bindZeros D d.rs ++ (Z ++ V))) st1 .normal) :=
    stmts_append_normal c1 s2'
  have c3b : Step D funs' (d.ps.zip argvals ++ (bindZeros D d.rs ++ (Z ++ V))) st1
      (.stmts [Stmt.block d.ss])
      (.sres (A'' ++ (Z ++ V)) st2 .normal) := by
    have h := Step.seqCons hstepb Step.seqNil
    rw [show A₀ ++ (Z ++ V) = d.ps.zip argvals ++ (bindZeros D d.rs ++ (Z ++ V)) by
      rw [hA₀]; simp [List.append_assoc]] at h
    exact h
  have c3 : Step D funs' (Z ++ V) st
      (.stmts (([Stmt.letDecl d.rs none] ++ argLets) ++ [Stmt.block d.ss]))
      (.sres (A'' ++ (Z ++ V)) st2 .normal) :=
    stmts_append_normal c2 c3b
  have c4 : Step D funs' (Z ++ V) st
      (.stmts ((([Stmt.letDecl d.rs none] ++ argLets) ++ [Stmt.block d.ss]) ++ assignsL))
      (.sres (A'' ++ VEnv.setMany (Z ++ V) xs (d.rs.map
        (fun r => (VEnv.get A'' r).getD (evmWithExternal calls creates).zero)))
        st2 .normal) :=
    stmts_append_normal c3 s4
  have hchain : Step D (hoist D ([Stmt.letDecl d.rs none] ++ argLets
      ++ [Stmt.block d.ss] ++ assignsL) :: funs₂) (Z ++ V) st
      (.stmts ([Stmt.letDecl d.rs none] ++ argLets ++ [Stmt.block d.ss] ++ assignsL))
      (.sres (A'' ++ VEnv.setMany (Z ++ V) xs (d.rs.map
        (fun r => (VEnv.get A'' r).getD (evmWithExternal calls creates).zero)))
        st2 .normal) := by
    rw [hfuns'] at c4
    exact c4
  have hfinal := Step.block (funs := funs₂) hchain
  have hlast : restore (Z ++ V) (A'' ++ VEnv.setMany (Z ++ V) xs (d.rs.map
      (fun r => (VEnv.get A'' r).getD (evmWithExternal calls creates).zero))) =
      VEnv.setMany (Z ++ V) xs (d.rs.map
        (fun r => (VEnv.get A'' r).getD (evmWithExternal calls creates).zero)) :=
    restore_exact (VEnv.setMany_length _ _ _)
  rw [hlast] at hfinal
  rw [hVend']
  show Step D funs₂ (Z ++ V) st (.stmt (.block ([Stmt.letDecl d.rs none] ++ argLets
      ++ [Stmt.block d.ss] ++ assignsL))) _
  exact hfinal

/-- **Forward, body-halt path**: a halting callee body halts the inlined core
with the caller environment restored. -/
theorem inlineCore_fwd_bodyhalt {d : IDecl} {xs : List Ident} {as : List (Expr Op)}
    (hsc : scopedStmts (d.ps ++ d.rs) d.ss = true)
    (hlen_as : as.length = d.ps.length)
    (hnc : argsHaveCall as = false)
    (hsh : argsShadowOK d.rs (d.ps.zip as) = true)
    {funs cenv : FunEnv D} {V Z : VEnv D} {st st1 st2 : EvmState}
    {argvals : List U256} {Vend : VEnv D}
    (hargs : Step D funs V st (.args as) (.eres (.vals argvals st1)))
    (hbody : Step D cenv (d.ps.zip argvals ++ bindZeros D d.rs) st1
      (.stmt (.block d.ss)) (.sres Vend st2 .halt))
    (hZ : ∀ y ∈ varsList as, y ∉ Z.map Prod.fst)
    (funs₂ : FunEnv D) :
    Step D funs₂ (Z ++ V) st (.stmt (inlineCore d xs as))
      (.sres (Z ++ V) st2 .halt) := by
  have hvlen : argvals.length = as.length := args_length hargs
  have hpslen : d.ps.length ≤ argvals.length := by omega
  set A₀ : VEnv D := d.ps.zip argvals ++ bindZeros D d.rs with hA₀
  have hA₀keys : A₀.map Prod.fst = d.ps ++ d.rs := calleeFrame_keys hpslen
  set argLets : List (Stmt Op) :=
    (d.ps.zip as).reverse.map (fun pa => Stmt.letDecl [pa.1] (some pa.2)) with hargLets
  set assignsL : List (Stmt Op) :=
    (xs.zip d.rs).map (fun xr => Stmt.assign [xr.1] (Expr.var xr.2)) with hassignsL
  set funs' : FunEnv D := hoist D
    ([Stmt.letDecl d.rs none] ++ argLets ++ [Stmt.block d.ss] ++ assignsL) :: funs₂
    with hfuns'
  have s1 : Step D funs' (Z ++ V) st (.stmt (.letDecl d.rs none))
      (.sres (bindZeros D d.rs ++ (Z ++ V)) st .normal) := Step.letZero
  have hN : ∀ y ∈ varsList as, y ∉ (bindZeros D d.rs ++ Z).map Prod.fst := by
    intro y hy
    rw [List.map_append, bindZeros_keys]
    intro hmem
    rcases List.mem_append.mp hmem with hm | hm
    · have hrs := argsShadowOK_rs hsh y
      rw [zip_snds hlen_as.symm] at hrs
      exact hrs hy hm
    · exact hZ y hy hm
  have s2 := argLets_fwd (rs := d.rs) hargs hlen_as.symm hnc hsh hN funs'
  have hscode : scopedCode (d.ps ++ d.rs) (Code.stmt (.block d.ss)) = true := by
    simp [scopedCode, scopedStmt, hsc]
  have hbound : ∀ x ∈ d.ps ++ d.rs, x ∈ A₀.map Prod.fst := by
    intro x hx; rw [hA₀keys]; exact hx
  obtain ⟨res₂, hstepb, htr⟩ := scoped_transfer hbody
    (A := A₀) (W := ([] : VEnv D)) (bound := d.ps ++ d.rs) funs' (Z ++ V)
    (by simp) hscode hbound
  obtain ⟨A'', hVend, hres₂⟩ := TRes.halt_inv htr
  subst hres₂
  have c1 : Step D funs' (Z ++ V) st (.stmts [Stmt.letDecl d.rs none])
      (.sres (bindZeros D d.rs ++ (Z ++ V)) st .normal) :=
    Step.seqCons s1 Step.seqNil
  have s2' : Step D funs' (bindZeros D d.rs ++ (Z ++ V)) st (.stmts argLets)
      (.sres (d.ps.zip argvals ++ (bindZeros D d.rs ++ (Z ++ V))) st1 .normal) := by
    have h := s2
    rw [show (bindZeros D d.rs ++ Z) ++ V = bindZeros D d.rs ++ (Z ++ V) from
      List.append_assoc _ _ _] at h
    exact h
  have c2 : Step D funs' (Z ++ V) st
      (.stmts ([Stmt.letDecl d.rs none] ++ argLets))
      (.sres (d.ps.zip argvals ++ (bindZeros D d.rs ++ (Z ++ V))) st1 .normal) :=
    stmts_append_normal c1 s2'
  have c3b : Step D funs' (d.ps.zip argvals ++ (bindZeros D d.rs ++ (Z ++ V))) st1
      (.stmts [Stmt.block d.ss])
      (.sres (A'' ++ (Z ++ V)) st2 .halt) := by
    have h : Step D funs' (A₀ ++ (Z ++ V)) st1 (.stmts [Stmt.block d.ss])
        (.sres (A'' ++ (Z ++ V)) st2 .halt) :=
      Step.seqStop hstepb (by simp)
    rw [show A₀ ++ (Z ++ V) = d.ps.zip argvals ++ (bindZeros D d.rs ++ (Z ++ V)) by
      rw [hA₀]; simp [List.append_assoc]] at h
    exact h
  have c3 : Step D funs' (Z ++ V) st
      (.stmts (([Stmt.letDecl d.rs none] ++ argLets) ++ [Stmt.block d.ss]))
      (.sres (A'' ++ (Z ++ V)) st2 .halt) :=
    stmts_append_normal c2 c3b
  have c4 : Step D funs' (Z ++ V) st
      (.stmts ((([Stmt.letDecl d.rs none] ++ argLets) ++ [Stmt.block d.ss]) ++ assignsL))
      (.sres (A'' ++ (Z ++ V)) st2 .halt) :=
    stmts_append_early c3 (by simp)
  have hchain : Step D (hoist D ([Stmt.letDecl d.rs none] ++ argLets
      ++ [Stmt.block d.ss] ++ assignsL) :: funs₂) (Z ++ V) st
      (.stmts ([Stmt.letDecl d.rs none] ++ argLets ++ [Stmt.block d.ss] ++ assignsL))
      (.sres (A'' ++ (Z ++ V)) st2 .halt) := by
    rw [hfuns'] at c4
    exact c4
  have hfinal := Step.block (funs := funs₂) hchain
  rw [restore_exact rfl] at hfinal
  exact hfinal

/-- **Forward, argument-halt path**: halting argument evaluation halts the
inlined core with the caller environment restored. -/
theorem inlineCore_fwd_argshalt {d : IDecl} {xs : List Ident} {as : List (Expr Op)}
    (hlen_as : as.length = d.ps.length)
    (hnc : argsHaveCall as = false)
    (hsh : argsShadowOK d.rs (d.ps.zip as) = true)
    {funs : FunEnv D} {V Z : VEnv D} {st st1 : EvmState}
    (hargs : Step D funs V st (.args as) (.eres (.halt st1)))
    (hZ : ∀ y ∈ varsList as, y ∉ Z.map Prod.fst)
    (funs₂ : FunEnv D) :
    Step D funs₂ (Z ++ V) st (.stmt (inlineCore d xs as))
      (.sres (Z ++ V) st1 .halt) := by
  set argLets : List (Stmt Op) :=
    (d.ps.zip as).reverse.map (fun pa => Stmt.letDecl [pa.1] (some pa.2)) with hargLets
  set assignsL : List (Stmt Op) :=
    (xs.zip d.rs).map (fun xr => Stmt.assign [xr.1] (Expr.var xr.2)) with hassignsL
  set funs' : FunEnv D := hoist D
    ([Stmt.letDecl d.rs none] ++ argLets ++ [Stmt.block d.ss] ++ assignsL) :: funs₂
    with hfuns'
  have hN : ∀ y ∈ varsList as, y ∉ (bindZeros D d.rs ++ Z).map Prod.fst := by
    intro y hy
    rw [List.map_append, bindZeros_keys]
    intro hmem
    rcases List.mem_append.mp hmem with hm | hm
    · have hrs := argsShadowOK_rs hsh y
      rw [zip_snds hlen_as.symm] at hrs
      exact hrs hy hm
    · exact hZ y hy hm
  obtain ⟨P, s2⟩ := argLets_halt_fwd (rs := d.rs) hargs hlen_as.symm hnc hsh hN funs'
  have c1 : Step D funs' (Z ++ V) st (.stmts [Stmt.letDecl d.rs none])
      (.sres (bindZeros D d.rs ++ (Z ++ V)) st .normal) :=
    Step.seqCons Step.letZero Step.seqNil
  have s2' : Step D funs' (bindZeros D d.rs ++ (Z ++ V)) st (.stmts argLets)
      (.sres ((P ++ bindZeros D d.rs) ++ (Z ++ V)) st1 .halt) := by
    have h := s2
    rw [show P ++ ((bindZeros D d.rs ++ Z) ++ V) =
      (P ++ bindZeros D d.rs) ++ (Z ++ V) by simp [List.append_assoc]] at h
    rw [show (bindZeros D d.rs ++ Z) ++ V = bindZeros D d.rs ++ (Z ++ V) from
      List.append_assoc _ _ _] at h
    exact h
  have c2 : Step D funs' (Z ++ V) st
      (.stmts ([Stmt.letDecl d.rs none] ++ argLets))
      (.sres ((P ++ bindZeros D d.rs) ++ (Z ++ V)) st1 .halt) :=
    stmts_append_normal c1 s2'
  have c3 : Step D funs' (Z ++ V) st
      (.stmts (([Stmt.letDecl d.rs none] ++ argLets) ++ [Stmt.block d.ss]))
      (.sres ((P ++ bindZeros D d.rs) ++ (Z ++ V)) st1 .halt) :=
    stmts_append_early c2 (by simp)
  have c4 : Step D funs' (Z ++ V) st
      (.stmts ((([Stmt.letDecl d.rs none] ++ argLets) ++ [Stmt.block d.ss]) ++ assignsL))
      (.sres ((P ++ bindZeros D d.rs) ++ (Z ++ V)) st1 .halt) :=
    stmts_append_early c3 (by simp)
  have hchain : Step D (hoist D ([Stmt.letDecl d.rs none] ++ argLets
      ++ [Stmt.block d.ss] ++ assignsL) :: funs₂) (Z ++ V) st
      (.stmts ([Stmt.letDecl d.rs none] ++ argLets ++ [Stmt.block d.ss] ++ assignsL))
      (.sres ((P ++ bindZeros D d.rs) ++ (Z ++ V)) st1 .halt) := by
    rw [hfuns'] at c4
    exact c4
  have hfinal := Step.block (funs := funs₂) hchain
  rw [restore_exact rfl] at hfinal
  exact hfinal

/-! ### Backward direction: dissecting the inlined core -/

/-- Dissect the argument `let`s: an execution of the reversed binding sequence
is an evaluation of the argument list under the caller environment. -/
theorem argLets_bwd {rs : List Ident} {funs₁ : FunEnv D} :
    ∀ {ps : List Ident} {as : List (Expr Op)}
      {funs₂ : FunEnv D} {V N : VEnv D} {st : EvmState}
      {Vr : VEnv D} {str : EvmState} {o : Outcome},
      Step D funs₂ (N ++ V) st
        (.stmts ((ps.zip as).reverse.map (fun pa => .letDecl [pa.1] (some pa.2))))
        (.sres Vr str o) →
      ps.length = as.length →
      argsHaveCall as = false →
      argsShadowOK rs (ps.zip as) = true →
      (∀ y ∈ varsList as, y ∉ N.map Prod.fst) →
      (∃ argvals, Vr = ps.zip argvals ++ (N ++ V) ∧ o = .normal ∧
        Step D funs₁ V st (.args as) (.eres (.vals argvals str))) ∨
      (∃ P, Vr = P ++ (N ++ V) ∧ o = .halt ∧
        Step D funs₁ V st (.args as) (.eres (.halt str))) := by
  intro ps as
  induction as generalizing ps with
  | nil =>
      intro funs₂ V N st Vr str o h hlen hnc hsh hN
      cases ps with
      | nil =>
          left
          cases h with
          | seqNil => exact ⟨[], by simp, rfl, Step.argsNil⟩
      | cons p ps' => simp at hlen
  | cons a as' ih =>
      intro funs₂ V N st Vr str o h hlen hnc hsh hN
      cases ps with
      | nil => simp at hlen
      | cons p ps' =>
          rw [show argsHaveCall (a :: as') =
            (exprHasCall a || argsHaveCall as') from rfl,
            Bool.or_eq_false_iff] at hnc
          rw [List.zip_cons_cons] at hsh h
          unfold argsShadowOK at hsh
          rw [Bool.and_eq_true] at hsh
          have hNrest : ∀ y ∈ varsList as', y ∉ N.map Prod.fst := fun y hy =>
            hN y (by
              rw [show varsList (a :: as') = exprVars a ++ varsList as' from rfl]
              exact List.mem_append.mpr (Or.inr hy))
          rw [List.reverse_cons, List.map_append] at h
          rcases stmts_append_fwd h with ⟨V1, st1, hpre, hsuf⟩ | ⟨hne, hpre⟩
          · -- the earlier (rightward) arguments ran to completion
            rcases ih hpre (by simpa using hlen) hnc.2 hsh.2 hNrest
              with ⟨argvals, hV1, -, hargs⟩ | ⟨P, hV1, ho, hargs⟩
            · -- and bound normally; then the head binding ran
              subst hV1
              have hrestlen : argvals.length = as'.length := args_length hargs
              have hagree : ∀ y ∈ exprVars a,
                  VEnv.get (ps'.zip argvals ++ (N ++ V)) y = VEnv.get V y := by
                intro y hy
                have hsha := List.all_eq_true.mp hsh.1 y hy
                rw [Bool.and_eq_true] at hsha
                have hlen' : ps'.length = as'.length := by simpa using hlen
                have hyp : y ∉ (ps'.zip argvals).map Prod.fst := by
                  rw [List.map_fst_zip (by omega : ps'.length ≤ argvals.length)]
                  have h1 := hsha.1
                  rw [List.map_fst_zip (le_of_eq hlen')] at h1
                  simpa using h1
                have hyN : y ∉ N.map Prod.fst := hN y (by
                  rw [show varsList (a :: as') = exprVars a ++ varsList as' from rfl]
                  exact List.mem_append.mpr (Or.inl hy))
                rw [VEnv.get_append_not_mem hyp, VEnv.get_append_not_mem hyN]
              cases hsuf with
              | seqCons hlet htail =>
                  cases hlet with
                  | @letVal _ _ _ _ _ vals stv he hlenv =>
                      cases htail with
                      | seqNil =>
                          left
                          obtain ⟨v, rfl⟩ : ∃ v, vals = [v] := by
                            cases vals with
                            | nil => simp at hlenv
                            | cons v vrest =>
                                cases vrest with
                                | nil => exact ⟨v, rfl⟩
                                | cons _ _ => simp at hlenv
                          refine ⟨v :: argvals, ?_, rfl, ?_⟩
                          · rw [List.zip_cons_cons]
                            rfl
                          · exact Step.argsCons hargs
                              (exprNoCall_transfer he funs₁ ⟨hnc.1,
                                fun y hy => (hagree y hy).symm⟩)
              | seqStop hlet hneq =>
                  cases hlet with
                  | @letVal _ _ _ _ _ vals stv he hlenv => exact absurd rfl hneq
                  | @letHalt _ _ _ _ _ _ he =>
                      right
                      refine ⟨ps'.zip argvals, rfl, rfl, ?_⟩
                      exact Step.argsHeadHalt hargs
                        (exprNoCall_transfer he funs₁ ⟨hnc.1,
                          fun y hy => (hagree y hy).symm⟩)
            · -- an earlier argument halted: the prefix cannot be normal
              exact absurd ho (by simp)
          · -- the let prefix stopped early: only a halt is possible
            rcases ih hpre (by simpa using hlen) hnc.2 hsh.2 hNrest
              with ⟨argvals, hV1, ho, hargs⟩ | ⟨P, hV1, ho, hargs⟩
            · exact absurd ho hne
            · right
              exact ⟨P, hV1, ho, Step.argsRestHalt hargs⟩

/-- Dissect the read-out assignments (given the callee frame's keys, they
always complete normally, computing exactly the sequential update). -/
theorem assigns_bwd {A' : VEnv D} :
    ∀ {xs rs : List Ident} {funs : FunEnv D} {Wb : VEnv D} {st : EvmState}
      {Vr : VEnv D} {str : EvmState} {o : Outcome},
      Step D funs (A' ++ Wb) st
        (.stmts ((xs.zip rs).map (fun xr => .assign [xr.1] (.var xr.2))))
        (.sres Vr str o) →
      (∀ r ∈ rs, r ∈ A'.map Prod.fst) →
      (∀ x ∈ xs, x ∉ A'.map Prod.fst) →
      xs.length = rs.length →
      Vr = A' ++ VEnv.setMany Wb xs (rs.map
        (fun r => (VEnv.get A' r).getD (evmWithExternal calls creates).zero)) ∧
      str = st ∧ o = .normal := by
  intro xs
  induction xs with
  | nil =>
      intro rs funs Wb st Vr str o h hr hx hlen
      cases rs with
      | nil =>
          cases h with
          | seqNil => exact ⟨by simp [VEnv.setMany], rfl, rfl⟩
      | cons r rs' => simp at hlen
  | cons x xs' ih =>
      intro rs funs Wb st Vr str o h hr hx hlen
      cases rs with
      | nil => simp at hlen
      | cons r rs' =>
          rw [List.zip_cons_cons, List.map_cons] at h
          have hrA : r ∈ A'.map Prod.fst := hr r (by simp)
          obtain ⟨v, hv⟩ : ∃ v, VEnv.get A' r = some v := by
            have := VEnv.find?_key_isSome (calls := calls) (creates := creates) hrA
            obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp this
            exact ⟨p.2, by unfold VEnv.get; rw [hp]; rfl⟩
          have hmany : VEnv.setMany Wb (x :: xs') ((r :: rs').map
              (fun r => (VEnv.get A' r).getD (evmWithExternal calls creates).zero)) =
              VEnv.setMany (VEnv.set Wb x v) xs' (rs'.map
                (fun r => (VEnv.get A' r).getD (evmWithExternal calls creates).zero)) := by
            rw [List.map_cons, hv]
            rfl
          cases h with
          | seqCons hs htail =>
              cases hs with
              | @assignVal _ _ _ _ _ vals stv he hlenv =>
                  cases he with
                  | @var _ _ _ _ w hw =>
                      have hwv : w = v := by
                        rw [VEnv.get_append_mem hrA, hv] at hw
                        injection hw with hw
                        exact hw.symm
                      have hsetc : VEnv.setMany (A' ++ Wb) [x] [w] =
                          A' ++ VEnv.set Wb x w := by
                        rw [VEnv.setMany_singleton]
                        exact VEnv.set_append_not_mem (hx x (by simp)) Wb w
                      rw [hsetc] at htail
                      obtain ⟨hVr, hstr, ho⟩ := ih htail
                        (fun r' hr' => hr r' (List.mem_cons_of_mem _ hr'))
                        (fun x' hx' => hx x' (List.mem_cons_of_mem _ hx'))
                        (by simpa using hlen)
                      refine ⟨?_, hstr, ho⟩
                      rw [hmany, ← hwv]
                      exact hVr
          | seqStop hs hneq =>
              cases hs with
              | @assignVal _ _ _ _ _ vals stv he hlenv => exact absurd rfl hneq
              | @assignHalt _ _ _ _ _ _ he => cases he

/-- **Backward**: an execution of the inlined core dissects into the call's
constituents — argument evaluation and callee body run — with the exact
result correspondence of the forward direction. -/
theorem inlineCore_bwd {d : IDecl} {xs : List Ident} {as : List (Expr Op)}
    (hsc : scopedStmts (d.ps ++ d.rs) d.ss = true)
    (hlen_as : as.length = d.ps.length)
    (hnc : argsHaveCall as = false)
    (hsh : argsShadowOK d.rs (d.ps.zip as) = true)
    (hxout : ∀ x ∈ xs, x ∉ d.ps ++ d.rs)
    (hlen_xs : xs.length = d.rs.length)
    {funs₂ : FunEnv D} {V Z : VEnv D} {st : EvmState}
    {Vr : VEnv D} {str : EvmState} {o : Outcome}
    (hcore : Step D funs₂ (Z ++ V) st (.stmt (inlineCore d xs as))
      (.sres Vr str o))
    (hZ : ∀ y ∈ varsList as, y ∉ Z.map Prod.fst)
    (funs₁ cenv : FunEnv D) :
    (∃ argvals st1 Vend,
      Step D funs₁ V st (.args as) (.eres (.vals argvals st1)) ∧
      Step D cenv (d.ps.zip argvals ++ bindZeros D d.rs) st1
        (.stmt (.block d.ss)) (.sres Vend str .normal) ∧
      Vr = VEnv.setMany (Z ++ V) xs (d.rs.map
        (fun r => (VEnv.get Vend r).getD (evmWithExternal calls creates).zero)) ∧
      o = .normal) ∨
    (∃ argvals st1 Vend,
      Step D funs₁ V st (.args as) (.eres (.vals argvals st1)) ∧
      Step D cenv (d.ps.zip argvals ++ bindZeros D d.rs) st1
        (.stmt (.block d.ss)) (.sres Vend str .halt) ∧
      Vr = Z ++ V ∧ o = .halt) ∨
    (Step D funs₁ V st (.args as) (.eres (.halt str)) ∧
      Vr = Z ++ V ∧ o = .halt) := by
  cases hcore with
  | @block _ _ _ _ Vb _ _ hb =>
      cases hb with
      | seqStop hlet hneq =>
          cases hlet with
          | letZero => exact absurd rfl hneq
      | seqCons hlet htail =>
          cases hlet with
          | letZero =>
              -- split the argument lets from the body + read-out
              simp only [List.append_eq, List.nil_append, List.append_assoc] at htail
              rw [show bindZeros D d.rs ++ (Z ++ V) =
                (bindZeros D d.rs ++ Z) ++ V from (List.append_assoc _ _ _).symm]
                at htail
              have htail' := htail
              have hN : ∀ y ∈ varsList as,
                  y ∉ (bindZeros D d.rs ++ Z).map Prod.fst := by
                intro y hy
                rw [List.map_append, bindZeros_keys]
                intro hmem
                rcases List.mem_append.mp hmem with hm | hm
                · have hrs := argsShadowOK_rs hsh y
                  rw [zip_snds hlen_as.symm] at hrs
                  exact hrs hy hm
                · exact hZ y hy hm
              rcases stmts_append_fwd htail' with ⟨V1, st1, hpre, hsuf⟩ | ⟨hne, hpre⟩
              · -- argument lets completed normally
                rcases argLets_bwd (rs := d.rs) (funs₁ := funs₁) hpre hlen_as.symm
                    hnc hsh hN with ⟨argvals, hV1, -, hargs⟩ | ⟨P, hV1, ho, -⟩
                · subst hV1
                  have hvlen : argvals.length = as.length := args_length hargs
                  have hpslen : d.ps.length ≤ argvals.length := by omega
                  have hscode : scopedCode (d.ps ++ d.rs)
                      (Code.stmt (.block d.ss)) = true := by
                    simp [scopedCode, scopedStmt, hsc]
                  have hbound : ∀ x ∈ d.ps ++ d.rs,
                      x ∈ (d.ps.zip argvals ++ bindZeros D d.rs).map Prod.fst := by
                    intro x hx
                    rw [calleeFrame_keys hpslen]
                    exact hx
                  cases hsuf with
                  | @seqCons _ _ _ _ _ V2 st2 _ _ _ hbody htail2 =>
                      rw [show d.ps.zip argvals ++ (bindZeros D d.rs ++ Z ++ V) =
                        (d.ps.zip argvals ++ bindZeros D d.rs) ++ (Z ++ V) by
                          simp [List.append_assoc]] at hbody
                      have hbody' := hbody
                      obtain ⟨res₂, hstepb, htr⟩ := scoped_transfer hbody'
                        (A := d.ps.zip argvals ++ bindZeros D d.rs)
                        (W := Z ++ V) (bound := d.ps ++ d.rs) cenv ([] : VEnv D)
                        rfl hscode hbound
                      obtain ⟨A', hV2, hres₂, hk⟩ := TRes.norm_inv htr
                      subst hres₂ hV2
                      simp only [List.append_nil] at hstepb
                      -- the callee frame's keys survive the body
                      have hshape := block_stmt_shape hbody'
                      have hkeysA' : A'.map Prod.fst = d.ps ++ d.rs := by
                        have hlA : A'.length =
                            (d.ps.zip argvals ++ bindZeros D d.rs).length := by
                          have := hshape.2
                          simp only [List.length_append] at this ⊢
                          omega
                        have hmm : A'.map Prod.fst ++ (Z ++ V).map Prod.fst =
                            (d.ps.zip argvals ++ bindZeros D d.rs).map Prod.fst ++
                              (Z ++ V).map Prod.fst := by
                          rw [← List.map_append, ← List.map_append]
                          exact hshape.1
                        exact (append_cancel_of_length hmm
                          (by simpa using hlA)).1.trans (calleeFrame_keys hpslen)
                      -- dissect the read-out assignments
                      obtain ⟨hVb, hstb, ho⟩ := assigns_bwd htail2
                        (fun r hr => by
                          rw [hkeysA']; exact List.mem_append.mpr (Or.inr hr))
                        (fun x hx => by
                          rw [hkeysA']; exact hxout x hx)
                        hlen_xs
                      subst hVb hstb ho
                      left
                      refine ⟨argvals, st1, A', hargs, hstepb, ?_, rfl⟩
                      exact restore_exact (VEnv.setMany_length _ _ _)
                  | @seqStop _ _ _ _ _ V2 st2 ob hbody hneb =>
                      rw [show d.ps.zip argvals ++ (bindZeros D d.rs ++ Z ++ V) =
                        (d.ps.zip argvals ++ bindZeros D d.rs) ++ (Z ++ V) by
                          simp [List.append_assoc]] at hbody
                      have hbody' := hbody
                      obtain ⟨res₂, hstepb, htr⟩ := scoped_transfer hbody'
                        (A := d.ps.zip argvals ++ bindZeros D d.rs)
                        (W := Z ++ V) (bound := d.ps ++ d.rs) cenv ([] : VEnv D)
                        rfl hscode hbound
                      cases htr with
                      | norm hk => exact absurd rfl hneb
                      | @halt A' st' =>
                          simp only [List.append_nil] at hstepb
                          right; left
                          refine ⟨argvals, st1, A', hargs, hstepb, ?_, rfl⟩
                          exact restore_exact rfl
                · exact absurd ho (by simp)
              · -- the argument lets stopped early: only a halt is possible
                rcases argLets_bwd (rs := d.rs) (funs₁ := funs₁) hpre hlen_as.symm
                    hnc hsh hN with ⟨argvals, hV1, ho, -⟩ | ⟨P, hV1, ho, hargs⟩
                · exact absurd ho hne
                · subst hV1 ho
                  right; right
                  refine ⟨hargs, ?_, rfl⟩
                  rw [show P ++ ((bindZeros D d.rs ++ Z) ++ V) =
                    (P ++ bindZeros D d.rs) ++ (Z ++ V) by simp [List.append_assoc]]
                  exact restore_exact rfl

/-! ### The inlining relation

Skip-rule relation over `PCode` (the transform inhabits it; skip alternatives
make it closed under layout resolution). Expressions are never rewritten —
the expression/argument classes relate identically — and every statement rule
is constructor-preserving except the three *site* rules. `Δ` mirrors the
scope discipline of `hoist`/`lookupFun`: blocks and function bodies extend it
with their own hoisted declarations (`deltaExtend`), a `for` prunes its
`init`-defined names. -/

inductive IcRel : DEnv → PCode Op → PCode Op → Prop
  | expr {Δ : DEnv} {e : Expr Op} : IcRel Δ (.expr e) (.expr e)
  | args {Δ : DEnv} {es : List (Expr Op)} : IcRel Δ (.args es) (.args es)
  | blockS {Δ : DEnv} {body body' : Block Op} :
      IcRel (deltaExtend Δ body) (.stmts body) (.stmts body') →
      IcRel Δ (.stmt (.block body)) (.stmt (.block body'))
  | funDefS {Δ : DEnv} {n : Ident} {ps rs : List Ident} {body body' : Block Op} :
      IcRel (deltaExtend Δ body) (.stmts body) (.stmts body') →
      IcRel Δ (.stmt (.funDef n ps rs body)) (.stmt (.funDef n ps rs body'))
  | letS {Δ : DEnv} {xs : List Ident} {v : Option (Expr Op)} :
      IcRel Δ (.stmt (.letDecl xs v)) (.stmt (.letDecl xs v))
  | assignS {Δ : DEnv} {xs : List Ident} {e : Expr Op} :
      IcRel Δ (.stmt (.assign xs e)) (.stmt (.assign xs e))
  | exprStmtS {Δ : DEnv} {e : Expr Op} :
      IcRel Δ (.stmt (.exprStmt e)) (.stmt (.exprStmt e))
  | condS {Δ : DEnv} {c : Expr Op} {body body' : Block Op} :
      IcRel (deltaExtend Δ body) (.stmts body) (.stmts body') →
      IcRel Δ (.stmt (.cond c body)) (.stmt (.cond c body'))
  | switchS {Δ : DEnv} {c : Expr Op} {cases cases' : List (Literal × Block Op)}
      {dflt dflt' : Option (Block Op)} :
      IcRel Δ (.cases cases) (.cases cases') →
      IcRel Δ (.odflt dflt) (.odflt dflt') →
      IcRel Δ (.stmt (.switch c cases dflt)) (.stmt (.switch c cases' dflt'))
  | forS {Δ : DEnv} {init : Block Op} {c : Expr Op} {post post' body body' : Block Op} :
      IcRel (deltaExtend (Δ.filter
          (fun p => !(definedFuns init).contains p.1)) post)
        (.stmts post) (.stmts post') →
      IcRel (deltaExtend (Δ.filter
          (fun p => !(definedFuns init).contains p.1)) body)
        (.stmts body) (.stmts body') →
      IcRel Δ (.stmt (.forLoop init c post body))
        (.stmt (.forLoop init c post' body'))
  | breakS {Δ : DEnv} : IcRel Δ (.stmt .break) (.stmt .break)
  | continueS {Δ : DEnv} : IcRel Δ (.stmt .continue) (.stmt .continue)
  | leaveS {Δ : DEnv} : IcRel Δ (.stmt .leave) (.stmt .leave)
  | nilSS {Δ : DEnv} : IcRel Δ (.stmts []) (.stmts [])
  | consSS {Δ : DEnv} {s s' : Stmt Op} {rest rest' : List (Stmt Op)} :
      IcRel Δ (.stmt s) (.stmt s') → IcRel Δ (.stmts rest) (.stmts rest') →
      IcRel Δ (.stmts (s :: rest)) (.stmts (s' :: rest'))
  | siteLet {Δ : DEnv} {f : Ident} {d : IDecl} {xs : List Ident}
      {as : List (Expr Op)} {rest rest' : List (Stmt Op)} :
      lookupDelta Δ f = some d →
      (d.ps ++ d.rs).Nodup →
      scopedStmts (d.ps ++ d.rs) d.ss = true →
      siteOK d xs as true = true →
      IcRel Δ (.stmts rest) (.stmts rest') →
      IcRel Δ (.stmts (.letDecl xs (some (.call f as)) :: rest))
        (.stmts (.letDecl xs none :: inlineCore d xs as :: rest'))
  | siteAssign {Δ : DEnv} {f : Ident} {d : IDecl} {xs : List Ident}
      {as : List (Expr Op)} {rest rest' : List (Stmt Op)} :
      lookupDelta Δ f = some d →
      (d.ps ++ d.rs).Nodup →
      scopedStmts (d.ps ++ d.rs) d.ss = true →
      siteOK d xs as false = true →
      IcRel Δ (.stmts rest) (.stmts rest') →
      IcRel Δ (.stmts (.assign xs (.call f as) :: rest))
        (.stmts (inlineCore d xs as :: rest'))
  | siteExpr {Δ : DEnv} {f : Ident} {d : IDecl}
      {as : List (Expr Op)} {rest rest' : List (Stmt Op)} :
      lookupDelta Δ f = some d →
      (d.ps ++ d.rs).Nodup →
      scopedStmts (d.ps ++ d.rs) d.ss = true →
      siteOK d [] as false = true →
      IcRel Δ (.stmts rest) (.stmts rest') →
      IcRel Δ (.stmts (.exprStmt (.call f as) :: rest))
        (.stmts (inlineCore d [] as :: rest'))
  | loopL {Δ : DEnv} {c : Expr Op} {post post' body body' : Block Op} :
      IcRel (deltaExtend Δ post) (.stmts post) (.stmts post') →
      IcRel (deltaExtend Δ body) (.stmts body) (.stmts body') →
      IcRel Δ (.loop c post body) (.loop c post' body')
  | casesNil {Δ : DEnv} : IcRel Δ (.cases []) (.cases [])
  | casesCons {Δ : DEnv} {l : Literal} {b b' : Block Op}
      {rest rest' : List (Literal × Block Op)} :
      IcRel (deltaExtend Δ b) (.stmts b) (.stmts b') →
      IcRel Δ (.cases rest) (.cases rest') →
      IcRel Δ (.cases ((l, b) :: rest)) (.cases ((l, b') :: rest'))
  | odfltNone {Δ : DEnv} : IcRel Δ (.odflt none) (.odflt none)
  | odfltSome {Δ : DEnv} {b b' : Block Op} :
      IcRel (deltaExtend Δ b) (.stmts b) (.stmts b') →
      IcRel Δ (.odflt (some b)) (.odflt (some b'))

/-! ### The transform inhabits the relation -/

/-- Every tracked declaration is classified: distinct parameter/return names
and a scoped body. Maintained by `deltaExtend` (entries come from
`classifyDecl`) and trivially by pruning. -/
def DeltaWF (Δ : DEnv) : Prop :=
  ∀ p ∈ Δ, (p.2.ps ++ p.2.rs).Nodup ∧
    scopedStmts (p.2.ps ++ p.2.rs) p.2.ss = true

/-- `hoistDecls` only produces classified declarations. -/
theorem hoistDecls_wf {seen : List Ident} : ∀ {body : List (Stmt Op)}
    {p : Ident × IDecl}, p ∈ hoistDecls seen body →
    (p.2.ps ++ p.2.rs).Nodup ∧ scopedStmts (p.2.ps ++ p.2.rs) p.2.ss = true := by
  intro body
  induction body generalizing seen with
  | nil => intro p hp; cases hp
  | cons s rest ih =>
      intro p hp
      cases s with
      | funDef f ps rs fbody =>
          unfold hoistDecls at hp
          split at hp
          · exact ih hp
          · split at hp
            · next d hcl =>
                rcases List.mem_cons.mp hp with rfl | hp
                · obtain ⟨hps, hrs, hnd, hsc, -⟩ := classifyDecl_inv hcl
                  refine ⟨?_, ?_⟩
                  · show (d.ps ++ d.rs).Nodup
                    rw [hps, hrs]; exact hnd
                  · show scopedStmts (d.ps ++ d.rs) d.ss = true
                    rw [hps, hrs]
                    exact hsc
                · exact ih hp
            · exact ih hp
      | block body => exact ih hp
      | letDecl xs v => exact ih hp
      | assign xs e => exact ih hp
      | exprStmt e => exact ih hp
      | cond c body => exact ih hp
      | switch c cases dflt => exact ih hp
      | forLoop init c post body => exact ih hp
      | «break» => exact ih hp
      | «continue» => exact ih hp
      | leave => exact ih hp

/-- `deltaExtend` preserves well-formedness. -/
theorem DeltaWF.extend {Δ : DEnv} (h : DeltaWF Δ) (body : List (Stmt Op)) :
    DeltaWF (deltaExtend Δ body) := by
  intro p hp
  unfold deltaExtend at hp
  rcases List.mem_append.mp hp with hp | hp
  · exact hoistDecls_wf hp
  · exact h p (List.mem_filter.mp hp).1

/-- Pruning preserves well-formedness. -/
theorem DeltaWF.filter {Δ : DEnv} (h : DeltaWF Δ) (q : Ident × IDecl → Bool) :
    DeltaWF (Δ.filter q) :=
  fun p hp => h p (List.mem_filter.mp hp).1

/-- A `lookupDelta` hit is a member. -/
theorem lookupDelta_mem {Δ : DEnv} {f : Ident} {d : IDecl}
    (h : lookupDelta Δ f = some d) : (f, d) ∈ Δ := by
  unfold lookupDelta at h
  cases hf : Δ.find? (fun p => p.1 = f) with
  | none => rw [hf] at h; cases h
  | some p =>
      rw [hf] at h
      injection h with h
      have hmem := List.mem_of_find?_eq_some hf
      have hkey : p.1 = f := by
        have := List.find?_some hf
        simpa using this
      have : p = (f, d) := by
        cases p
        simp only at hkey h
        rw [hkey, h]
      rw [← this]
      exact hmem

mutual

/-- The statement-list transform inhabits the relation. -/
theorem icStmts_rel (Δ : DEnv) (hwf : DeltaWF Δ) :
    ∀ ss : List (Stmt Op), IcRel Δ (.stmts ss) (.stmts (icStmts Δ ss))
  | [] => by
      rw [icStmts]
      exact .nilSS
  | .letDecl xs (some (.call f as)) :: rest => by
      rw [icStmts, icStmt]
      split
      · next d hld =>
          obtain ⟨hnd, hsc⟩ := hwf (f, d) (lookupDelta_mem hld)
          by_cases hok : (inlineOK d && siteOK d xs as true) = true
          · rw [if_pos hok]
            rw [Bool.and_eq_true] at hok
            exact .siteLet hld hnd hsc hok.2 (icStmts_rel Δ hwf rest)
          · rw [if_neg hok]
            exact .consSS .letS (icStmts_rel Δ hwf rest)
      · exact .consSS .letS (icStmts_rel Δ hwf rest)
  | .assign xs (.call f as) :: rest => by
      rw [icStmts, icStmt]
      split
      · next d hld =>
          obtain ⟨hnd, hsc⟩ := hwf (f, d) (lookupDelta_mem hld)
          by_cases hok : (inlineOK d && siteOK d xs as false) = true
          · rw [if_pos hok]
            rw [Bool.and_eq_true] at hok
            exact .siteAssign hld hnd hsc hok.2 (icStmts_rel Δ hwf rest)
          · rw [if_neg hok]
            exact .consSS .assignS (icStmts_rel Δ hwf rest)
      · exact .consSS .assignS (icStmts_rel Δ hwf rest)
  | .exprStmt (.call f as) :: rest => by
      rw [icStmts, icStmt]
      split
      · next d hld =>
          obtain ⟨hnd, hsc⟩ := hwf (f, d) (lookupDelta_mem hld)
          by_cases hok : (inlineOK d && siteOK d [] as false) = true
          · rw [if_pos hok]
            rw [Bool.and_eq_true] at hok
            exact .siteExpr hld hnd hsc hok.2 (icStmts_rel Δ hwf rest)
          · rw [if_neg hok]
            exact .consSS .exprStmtS (icStmts_rel Δ hwf rest)
      · exact .consSS .exprStmtS (icStmts_rel Δ hwf rest)
  | .block body :: rest => by
      rw [icStmts, icStmt, icBlock]
      exact .consSS (.blockS (icStmts_rel _ (hwf.extend body) body))
        (icStmts_rel Δ hwf rest)
  | .funDef n ps rs body :: rest => by
      rw [icStmts, icStmt, icBlock]
      exact .consSS (.funDefS (icStmts_rel _ (hwf.extend body) body))
        (icStmts_rel Δ hwf rest)
  | .letDecl xs none :: rest => by
      rw [icStmts]
      simp only [icStmt]
      exact .consSS .letS (icStmts_rel Δ hwf rest)
  | .letDecl xs (some (.lit l)) :: rest => by
      rw [icStmts]
      simp only [icStmt]
      exact .consSS .letS (icStmts_rel Δ hwf rest)
  | .letDecl xs (some (.var y)) :: rest => by
      rw [icStmts]
      simp only [icStmt]
      exact .consSS .letS (icStmts_rel Δ hwf rest)
  | .letDecl xs (some (.builtin op es)) :: rest => by
      rw [icStmts]
      simp only [icStmt]
      exact .consSS .letS (icStmts_rel Δ hwf rest)
  | .assign xs (.lit l) :: rest => by
      rw [icStmts]
      simp only [icStmt]
      exact .consSS .assignS (icStmts_rel Δ hwf rest)
  | .assign xs (.var y) :: rest => by
      rw [icStmts]
      simp only [icStmt]
      exact .consSS .assignS (icStmts_rel Δ hwf rest)
  | .assign xs (.builtin op es) :: rest => by
      rw [icStmts]
      simp only [icStmt]
      exact .consSS .assignS (icStmts_rel Δ hwf rest)
  | .exprStmt (.lit l) :: rest => by
      rw [icStmts]
      simp only [icStmt]
      exact .consSS .exprStmtS (icStmts_rel Δ hwf rest)
  | .exprStmt (.var y) :: rest => by
      rw [icStmts]
      simp only [icStmt]
      exact .consSS .exprStmtS (icStmts_rel Δ hwf rest)
  | .exprStmt (.builtin op es) :: rest => by
      rw [icStmts]
      simp only [icStmt]
      exact .consSS .exprStmtS (icStmts_rel Δ hwf rest)
  | .cond c body :: rest => by
      rw [icStmts, icStmt, icBlock]
      exact .consSS (.condS (icStmts_rel _ (hwf.extend body) body))
        (icStmts_rel Δ hwf rest)
  | .switch c cases dflt :: rest => by
      rw [icStmts, icStmt]
      exact .consSS (.switchS (icCases_rel Δ hwf cases) (icDflt_rel Δ hwf dflt))
        (icStmts_rel Δ hwf rest)
  | .forLoop init c post body :: rest => by
      rw [icStmts, icStmt]
      simp only [icBlock]
      exact .consSS (.forS
          (icStmts_rel _ ((hwf.filter _).extend post) post)
          (icStmts_rel _ ((hwf.filter _).extend body) body))
        (icStmts_rel Δ hwf rest)
  | .break :: rest => by
      rw [icStmts]
      simp only [icStmt]
      exact .consSS .breakS (icStmts_rel Δ hwf rest)
  | .continue :: rest => by
      rw [icStmts]
      simp only [icStmt]
      exact .consSS .continueS (icStmts_rel Δ hwf rest)
  | .leave :: rest => by
      rw [icStmts]
      simp only [icStmt]
      exact .consSS .leaveS (icStmts_rel Δ hwf rest)

/-- The case-list transform inhabits the relation. -/
theorem icCases_rel (Δ : DEnv) (hwf : DeltaWF Δ) :
    ∀ cs : List (Literal × Block Op), IcRel Δ (.cases cs) (.cases (icCases Δ cs))
  | [] => by
      rw [icCases]
      exact .casesNil
  | (l, b) :: rest => by
      rw [icCases, icBlock]
      exact .casesCons (icStmts_rel _ (hwf.extend b) b) (icCases_rel Δ hwf rest)

/-- The default transform inhabits the relation. -/
theorem icDflt_rel (Δ : DEnv) (hwf : DeltaWF Δ) :
    ∀ dflt : Option (Block Op), IcRel Δ (.odflt dflt) (.odflt (icDflt Δ dflt))
  | none => by
      rw [icDflt]
      exact .odfltNone
  | some b => by
      rw [icDflt, icBlock]
      exact .odfltSome (icStmts_rel _ (hwf.extend b) b)

end

/-! ### Reflexivity (the all-skip derivation) -/

mutual

/-- Every statement is `IcRel`-related to itself at any `Δ`. -/
theorem IcRel.reflStmt (Δ : DEnv) : ∀ s : Stmt Op, IcRel Δ (.stmt s) (.stmt s)
  | .block body => .blockS (IcRel.reflStmts _ body)
  | .funDef n ps rs body => .funDefS (IcRel.reflStmts _ body)
  | .letDecl xs v => .letS
  | .assign xs e => .assignS
  | .exprStmt e => .exprStmtS
  | .cond c body => .condS (IcRel.reflStmts _ body)
  | .switch c cases dflt =>
      .switchS (IcRel.reflCases Δ cases) (IcRel.reflDflt Δ dflt)
  | .forLoop init c post body =>
      .forS (IcRel.reflStmts _ post) (IcRel.reflStmts _ body)
  | .break => .breakS
  | .continue => .continueS
  | .leave => .leaveS

/-- Every statement sequence is `IcRel`-related to itself at any `Δ`. -/
theorem IcRel.reflStmts (Δ : DEnv) : ∀ ss : List (Stmt Op),
    IcRel Δ (.stmts ss) (.stmts ss)
  | [] => .nilSS
  | s :: rest => .consSS (IcRel.reflStmt Δ s) (IcRel.reflStmts Δ rest)

/-- Every case list is `IcRel`-related to itself at any `Δ`. -/
theorem IcRel.reflCases (Δ : DEnv) : ∀ cs : List (Literal × Block Op),
    IcRel Δ (.cases cs) (.cases cs)
  | [] => .casesNil
  | (l, b) :: rest => .casesCons (IcRel.reflStmts _ b) (IcRel.reflCases Δ rest)

/-- Every default is `IcRel`-related to itself at any `Δ`. -/
theorem IcRel.reflDflt (Δ : DEnv) : ∀ dflt : Option (Block Op),
    IcRel Δ (.odflt dflt) (.odflt dflt)
  | none => .odfltNone
  | some b => .odfltSome (IcRel.reflStmts _ b)

end

/-! ### Declaration-context compatibility -/

/-- Every tracked declaration resolves, via `lookupFun`, to a declaration
whose signature matches and whose body is the tracked one up to a trailing
`leave`. -/
def DeltaCompat (Δ : DEnv) (funs : FunEnv D) : Prop :=
  ∀ p ∈ Δ, ∃ body₀ cenv,
    lookupFun funs p.1 = some (⟨p.2.ps, p.2.rs, body₀⟩, cenv) ∧
    (body₀ = p.2.ss ∨ body₀ = p.2.ss ++ [.leave])

theorem DeltaCompat.nil (funs : FunEnv D) :
    DeltaCompat (calls := calls) (creates := creates) [] funs :=
  fun p hp => absurd hp (List.not_mem_nil)

/-- Entries produced by `hoistDecls` carry names outside `seen`. -/
theorem hoistDecls_not_seen {seen : List Ident} : ∀ {body : List (Stmt Op)}
    {p : Ident × IDecl}, p ∈ hoistDecls seen body → p.1 ∉ seen := by
  intro body
  induction body generalizing seen with
  | nil => intro p hp; cases hp
  | cons s rest ih =>
      intro p hp
      cases s with
      | funDef f ps rs fbody =>
          unfold hoistDecls at hp
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
      | switch c cases dflt => exact ih hp
      | forLoop init c post body => exact ih hp
      | «break» => exact ih hp
      | «continue» => exact ih hp
      | leave => exact ih hp

/-- A `hoistDecls` entry is found by `find?` on the hoisted scope, at a
declaration it classified. -/
theorem hoistDecls_find {seen : List Ident} : ∀ {body : List (Stmt Op)}
    {f : Ident} {d : IDecl}, (f, d) ∈ hoistDecls seen body →
    ∃ ps rs fbody, (hoist D body).find? (fun p => p.1 = f) =
        some (f, ⟨ps, rs, fbody⟩) ∧ classifyDecl ps rs fbody = some d := by
  intro body
  induction body generalizing seen with
  | nil => intro f d hp; cases hp
  | cons s rest ih =>
      intro f d hp
      cases s with
      | funDef g ps rs fbody =>
          rw [show hoist D (.funDef g ps rs fbody :: rest) =
            (g, ⟨ps, rs, fbody⟩) :: hoist D rest from rfl]
          unfold hoistDecls at hp
          split at hp
          · next hseen =>
              have hne : f ≠ g := by
                intro he
                have := hoistDecls_not_seen hp
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
                      have := hoistDecls_not_seen hp
                      rw [he] at this
                      exact this (List.mem_cons_self ..)
                    rw [List.find?_cons_of_neg (by simpa using Ne.symm hne)]
                    exact ih hp
              · rcases hp' : hp with _
                have hne : f ≠ g := by
                  intro he
                  have := hoistDecls_not_seen hp
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
      | switch c cases dflt =>
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
      | leave =>
          rw [show hoist D (.leave :: rest) = hoist D rest from rfl]
          exact ih hp

/-- Names not defined by a block are absent from its hoisted scope. -/
theorem hoist_find_none {f : Ident} : ∀ {body : List (Stmt Op)},
    f ∉ definedFuns body →
    (hoist D body).find? (fun p => p.1 = f) = none := by
  intro body
  induction body with
  | nil => intro _; rfl
  | cons s rest ih =>
      intro hnf
      cases s with
      | funDef g ps rs fbody =>
          rw [show hoist D (.funDef g ps rs fbody :: rest) =
            (g, ⟨ps, rs, fbody⟩) :: hoist D rest from rfl]
          unfold definedFuns at hnf
          rw [List.mem_cons, not_or] at hnf
          rw [List.find?_cons_of_neg (by simp; exact fun h => hnf.1 h.symm)]
          exact ih hnf.2
      | block body => exact ih (by simpa [definedFuns] using hnf)
      | letDecl xs v => exact ih (by simpa [definedFuns] using hnf)
      | assign xs e => exact ih (by simpa [definedFuns] using hnf)
      | exprStmt e => exact ih (by simpa [definedFuns] using hnf)
      | cond c body => exact ih (by simpa [definedFuns] using hnf)
      | switch c cases dflt => exact ih (by simpa [definedFuns] using hnf)
      | forLoop init c post body => exact ih (by simpa [definedFuns] using hnf)
      | «break» => exact ih (by simpa [definedFuns] using hnf)
      | «continue» => exact ih (by simpa [definedFuns] using hnf)
      | leave => exact ih (by simpa [definedFuns] using hnf)

/-- Entering a block preserves compatibility: its own classified declarations
resolve in its hoisted scope, surviving outer entries resolve below it. -/
theorem DeltaCompat.extend {Δ : DEnv} {funs : FunEnv D}
    (h : DeltaCompat (calls := calls) (creates := creates) Δ funs)
    (body : List (Stmt Op)) :
    DeltaCompat (calls := calls) (creates := creates)
      (deltaExtend Δ body) (hoist D body :: funs) := by
  intro p hp
  unfold deltaExtend at hp
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨py, pd⟩ := p
    obtain ⟨ps, rs, fbody, hfind, hcl⟩ := hoistDecls_find hp
    obtain ⟨hps, hrs, -, -, hbody⟩ := classifyDecl_inv hcl
    refine ⟨fbody, hoist D body :: funs, ?_, hbody⟩
    show lookupFun (hoist D body :: funs) py = _
    unfold lookupFun
    rw [hfind]
    simp only [hps, hrs]
  · rw [List.mem_filter] at hp
    obtain ⟨body₀, cenv, hlk, hb⟩ := h p hp.1
    refine ⟨body₀, cenv, ?_, hb⟩
    show lookupFun (hoist D body :: funs) p.1 = _
    unfold lookupFun
    rw [hoist_find_none (by simpa using hp.2)]
    exact hlk

/-- Pruning names defined by a `for` init keeps compatibility under its
pushed scope. -/
theorem DeltaCompat.pruneInit {Δ : DEnv} {funs : FunEnv D}
    (h : DeltaCompat (calls := calls) (creates := creates) Δ funs)
    (init : List (Stmt Op)) :
    DeltaCompat (calls := calls) (creates := creates)
      (Δ.filter (fun p => !(definedFuns init).contains p.1))
      (hoist D init :: funs) := by
  intro p hp
  rw [List.mem_filter] at hp
  obtain ⟨body₀, cenv, hlk, hb⟩ := h p hp.1
  refine ⟨body₀, cenv, ?_, hb⟩
  show lookupFun (hoist D init :: funs) p.1 = _
  unfold lookupFun
  rw [hoist_find_none (by simpa using hp.2)]
  exact hlk

/-! ### Function-environment relation -/

/-- Declarations related by the inline transform, relative to the defining
environment. -/
def IcFDeclRel (cenv : FunEnv D) (d₁ d₂ : FDecl D) : Prop :=
  d₁.params = d₂.params ∧ d₁.rets = d₂.rets ∧
    ∃ Δ, DeltaCompat (calls := calls) (creates := creates) Δ cenv ∧
      IcRel (deltaExtend Δ d₁.body) (.stmts d₁.body) (.stmts d₂.body)

/-- Scopes related pairwise, relative to the defining environment. -/
def IcScopeRel (cenv : FunEnv D) (s₁ s₂ : FScope D) : Prop :=
  List.Forall₂ (fun p q => p.1 = q.1 ∧
    IcFDeclRel (calls := calls) (creates := creates) cenv p.2 q.2) s₁ s₂

/-- Function environments related scope-by-scope, each scope relative to its
own defining suffix. -/
inductive IcFunsRel : FunEnv D → FunEnv D → Prop
  | nil : IcFunsRel [] []
  | cons {s₁ s₂ : FScope D} {r₁ r₂ : FunEnv D} :
      IcScopeRel (calls := calls) (creates := creates) (s₁ :: r₁) s₁ s₂ →
      IcFunsRel r₁ r₂ →
      IcFunsRel (s₁ :: r₁) (s₂ :: r₂)

/-- A scope lookup transports across `IcScopeRel`. -/
theorem icScopeRel_find {cenv : FunEnv D} {s₁ s₂ : FScope D}
    (h : IcScopeRel (calls := calls) (creates := creates) cenv s₁ s₂)
    (fn : Ident) :
    (s₁.find? (fun p => p.1 = fn) = none ∧ s₂.find? (fun p => p.1 = fn) = none) ∨
    (∃ p q, s₁.find? (fun p => p.1 = fn) = some p ∧
      s₂.find? (fun p => p.1 = fn) = some q ∧ p.1 = q.1 ∧
      IcFDeclRel (calls := calls) (creates := creates) cenv p.2 q.2) := by
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

/-- `lookupFun` transports forward across `IcFunsRel`, returning the
defining-suffix relation. -/
theorem lookupFun_icFunsRel {f₁ f₂ : FunEnv D}
    (hR : IcFunsRel (calls := calls) (creates := creates) f₁ f₂)
    {fn : Ident} {decl₁ : FDecl D} {cenv₁ : FunEnv D}
    (h : lookupFun f₁ fn = some (decl₁, cenv₁)) :
    ∃ decl₂ cenv₂, lookupFun f₂ fn = some (decl₂, cenv₂) ∧
      IcFDeclRel (calls := calls) (creates := creates) cenv₁ decl₁ decl₂ ∧
      IcFunsRel (calls := calls) (creates := creates) cenv₁ cenv₂ := by
  induction hR with
  | nil => cases h
  | @cons s₁ s₂ r₁ r₂ hscope hrest ih =>
      unfold lookupFun at h ⊢
      rcases icScopeRel_find hscope fn with ⟨h1, h2⟩ | ⟨p, q, h1, h2, hname, hdecl⟩
      · rw [h1] at h
        rw [h2]
        exact ih h
      · rw [h1] at h
        rw [h2]
        injection h with h
        injection h with hd hc
        subst hd hc
        exact ⟨q.2, s₂ :: r₂, rfl, hdecl, .cons hscope hrest⟩

/-- `lookupFun` transports backward across `IcFunsRel`. -/
theorem lookupFun_icFunsRel_bwd {f₁ f₂ : FunEnv D}
    (hR : IcFunsRel (calls := calls) (creates := creates) f₁ f₂)
    {fn : Ident} {decl₂ : FDecl D} {cenv₂ : FunEnv D}
    (h : lookupFun f₂ fn = some (decl₂, cenv₂)) :
    ∃ decl₁ cenv₁, lookupFun f₁ fn = some (decl₁, cenv₁) ∧
      IcFDeclRel (calls := calls) (creates := creates) cenv₁ decl₁ decl₂ ∧
      IcFunsRel (calls := calls) (creates := creates) cenv₁ cenv₂ := by
  induction hR with
  | nil => cases h
  | @cons s₁ s₂ r₁ r₂ hscope hrest ih =>
      unfold lookupFun at h ⊢
      rcases icScopeRel_find hscope fn with ⟨h1, h2⟩ | ⟨p, q, h1, h2, hname, hdecl⟩
      · rw [h2] at h
        rw [h1]
        exact ih h
      · rw [h2] at h
        rw [h1]
        injection h with h
        injection h with hd hc
        subst hd hc
        exact ⟨p.2, s₁ :: r₁, rfl, hdecl, .cons hscope hrest⟩

/-- Extract the hoisted-scope alignment from a related statement sequence:
the declarations pair off with bodies related at the sequence's `Δ`
(extended by their own hoists). -/
theorem IcRel.hoist_scopeRel {Δ : DEnv} {pc pc' : PCode Op}
    (h : IcRel Δ pc pc') :
    ∀ {ss ss' : List (Stmt Op)}, pc = .stmts ss → pc' = .stmts ss' →
      List.Forall₂ (fun (p q : Ident × FDecl D) => p.1 = q.1 ∧
        p.2.params = q.2.params ∧ p.2.rets = q.2.rets ∧
        IcRel (deltaExtend Δ p.2.body) (.stmts p.2.body) (.stmts q.2.body))
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

/-- The scope-alignment of a related block yields `IcScopeRel` under the
extended compatibility. -/
theorem icScopeRel_of_block {Δ : DEnv} {funs : FunEnv D}
    {body body' : List (Stmt Op)}
    (hrel : IcRel (deltaExtend Δ body) (.stmts body) (.stmts body'))
    (hcompat : DeltaCompat (calls := calls) (creates := creates)
      (deltaExtend Δ body) (hoist D body :: funs)) :
    IcScopeRel (calls := calls) (creates := creates)
      (hoist D body :: funs) (hoist D body) (hoist D body') := by
  have hpairs := IcRel.hoist_scopeRel (calls := calls) (creates := creates)
    hrel rfl rfl
  refine List.Forall₂.imp ?_ hpairs
  intro p q hpq
  exact ⟨hpq.1, hpq.2.1, hpq.2.2.1, deltaExtend Δ body, hcompat, hpq.2.2.2⟩

/-- Reflexive scope relation (for untouched `for`-loop inits). -/
theorem icScopeRel_refl (cenv : FunEnv D) (s : FScope D) :
    IcScopeRel (calls := calls) (creates := creates) cenv s s := by
  induction s with
  | nil => exact .nil
  | cons p rest ih =>
      refine .cons ⟨rfl, rfl, rfl, [], DeltaCompat.nil _, ?_⟩ ih
      exact IcRel.reflStmts _ _

/-! ### The simulations -/

/-- Result correspondence: identical, except a `halt` reached inside an
inlined `let`-form site carries the site's zero-bound targets as an
environment prefix (erased at the nearest enclosing block's `restore`). -/
inductive IcRes : Res D → Res D → Prop
  | refl (r : Res D) : IcRes r r
  | haltIns (Zp V₁ : VEnv D) (st : EvmState) :
      IcRes (.sres V₁ st .halt) (.sres (Zp ++ V₁) st .halt)

/-- The per-class result claim: residue only on the statement-sequence class. -/
def icResOK : Code Op → Res D → Res D → Prop
  | .stmts _, r₁, r₂ => IcRes (calls := calls) (creates := creates) r₁ r₂
  | _, r₁, r₂ => r₂ = r₁

/-- `restore` past an inserted prefix above the preserved base. -/
theorem restore_prefix_le {base Zp Vb : VEnv D} (h : base.length ≤ Vb.length) :
    restore base (Zp ++ Vb) = restore base Vb := by
  simp only [restore, List.length_append]
  rw [show Zp.length + Vb.length - base.length =
    Zp.length + (Vb.length - base.length) by omega]
  rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append]
  congr 1
  omega

/-- The switch selection of related case lists/defaults is a related block
statement. -/
theorem IcRel.selectRel {Δ : DEnv} {cases cases' : List (Literal × Block Op)}
    {dflt dflt' : Option (Block Op)}
    (hcs : IcRel Δ (.cases cases) (.cases cases'))
    (hd : IcRel Δ (.odflt dflt) (.odflt dflt')) (cv : U256) :
    IcRel Δ (.stmt (.block (selectSwitch D cv cases dflt)))
      (.stmt (.block (selectSwitch D cv cases' dflt'))) := by
  induction cases generalizing cases' with
  | nil =>
      cases hcs
      cases hd with
      | odfltNone =>
          show IcRel Δ (.stmt (.block (Option.getD none [])))
            (.stmt (.block (Option.getD none [])))
          exact .blockS (IcRel.reflStmts _ _)
      | odfltSome hb =>
          simpa [selectSwitch] using IcRel.blockS hb
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

/-- Normalize a callee body to its trailing-`leave`-free form, at a
`normal`/`leave` call outcome; scoped bodies only ever produce `normal`. -/
theorem body_normalize_ok {d : IDecl} {body₀ : List (Stmt Op)}
    (hb : body₀ = d.ss ∨ body₀ = d.ss ++ [.leave])
    (hsc : scopedStmts (d.ps ++ d.rs) d.ss = true)
    {cenv : FunEnv D} {E : VEnv D} {st1 st2 : EvmState} {Vend : VEnv D}
    {o : Outcome}
    (hkeys : ∀ x ∈ d.ps ++ d.rs, x ∈ E.map Prod.fst)
    (hbody : Step D cenv E st1 (.stmt (.block body₀)) (.sres Vend st2 o))
    (ho : o = .normal ∨ o = .leave) :
    Step D cenv E st1 (.stmt (.block d.ss)) (.sres Vend st2 .normal) := by
  have hscode : scopedCode (d.ps ++ d.rs) (Code.stmt (.block d.ss)) = true := by
    simp [scopedCode, scopedStmt, hsc]
  rcases hb with rfl | rfl
  · -- no trailing leave: a scoped body cannot yield `leave`
    rcases ho with rfl | rfl
    · exact hbody
    · obtain ⟨res₂, -, htr⟩ := scoped_transfer hbody
        (A := E) (W := ([] : VEnv D)) (bound := d.ps ++ d.rs) cenv []
        (by simp) hscode hkeys
      cases htr
  · -- trailing leave: `leave` renormalizes, `normal` is impossible
    obtain ⟨o', hbody', hcase⟩ := block_trailing_leave_fwd hbody
    rcases hcase with ⟨-, rfl⟩ | ⟨rfl, hne⟩
    · exact hbody'
    · rcases ho with rfl | rfl
      · exact absurd rfl hne
      · obtain ⟨res₂, -, htr⟩ := scoped_transfer hbody'
          (A := E) (W := ([] : VEnv D)) (bound := d.ps ++ d.rs) cenv []
          (by simp) hscode hkeys
        cases htr

/-- ... and to its halting form. -/
theorem body_normalize_halt {d : IDecl} {body₀ : List (Stmt Op)}
    (hb : body₀ = d.ss ∨ body₀ = d.ss ++ [.leave])
    {cenv : FunEnv D} {E : VEnv D} {st1 st2 : EvmState} {Vend : VEnv D}
    (hbody : Step D cenv E st1 (.stmt (.block body₀)) (.sres Vend st2 .halt)) :
    Step D cenv E st1 (.stmt (.block d.ss)) (.sres Vend st2 .halt) := by
  rcases hb with rfl | rfl
  · exact hbody
  · obtain ⟨o', hbody', hcase⟩ := block_trailing_leave_fwd hbody
    rcases hcase with ⟨h1, -⟩ | ⟨h1, -⟩
    · cases h1
    · rw [← h1] at hbody'
      exact hbody'

/-- **Forward simulation**: a source derivation transports across `IcRel` to
the inlined program, with equal results everywhere except the statement-list
class, where a `let`-form site's halt may carry an inserted prefix. -/
theorem ic_fwd {funs₁ : FunEnv D} {V : VEnv D} {st : EvmState}
    {code : Code Op} {res : Res D} (h : Step D funs₁ V st code res) :
    ∀ {funs₂ : FunEnv D} {Δ : DEnv} {pc' : PCode Op},
      IcFunsRel (calls := calls) (creates := creates) funs₁ funs₂ →
      DeltaCompat (calls := calls) (creates := creates) Δ funs₁ →
      IcRel Δ (toPCode code) pc' →
      ∃ res₂, Step D funs₂ V st (ofPCode pc') res₂ ∧
        icResOK (calls := calls) (creates := creates) code res res₂ := by
  induction h with
  | @lit funs V st l =>
      intro funs₂ Δ pc' hR hΔ hrel
      cases hrel with
      | expr => exact ⟨_, Step.lit, rfl⟩
  | @var funs V st x v hv =>
      intro funs₂ Δ pc' hR hΔ hrel
      cases hrel with
      | expr => exact ⟨_, Step.var hv, rfl⟩
  | @builtinOk funs V st op args argvals st1 rets st2 ha hbi iha =>
      intro funs₂ Δ pc' hR hΔ hrel
      cases hrel with
      | expr =>
          obtain ⟨res₂, hs, heq⟩ := iha hR hΔ IcRel.args
          rw [show res₂ = _ from heq] at hs
          exact ⟨_, Step.builtinOk hs hbi, rfl⟩
  | @builtinHalt funs V st op args argvals st1 st2 ha hbi iha =>
      intro funs₂ Δ pc' hR hΔ hrel
      cases hrel with
      | expr =>
          obtain ⟨res₂, hs, heq⟩ := iha hR hΔ IcRel.args
          rw [show res₂ = _ from heq] at hs
          exact ⟨_, Step.builtinHalt hs hbi, rfl⟩
  | @builtinArgsHalt funs V st op args st1 ha iha =>
      intro funs₂ Δ pc' hR hΔ hrel
      cases hrel with
      | expr =>
          obtain ⟨res₂, hs, heq⟩ := iha hR hΔ IcRel.args
          rw [show res₂ = _ from heq] at hs
          exact ⟨_, Step.builtinArgsHalt hs, rfl⟩
  | @callOk funs V st fn args argvals st1 decl cenv Vend st2 o ha hlk harity hbody ho iha ihbody =>
      intro funs₂ Δ pc' hR hΔ hrel
      cases hrel with
      | expr =>
          obtain ⟨resa, hs, heqa⟩ := iha hR hΔ IcRel.args
          rw [show resa = _ from heqa] at hs
          obtain ⟨decl₂, cenv₂, hlk₂, hdecl, hcenvR⟩ := lookupFun_icFunsRel hR hlk
          obtain ⟨hps, hrs, Δf, hΔf, hbrel⟩ := hdecl
          obtain ⟨resb, hsb, heqb⟩ := ihbody hcenvR hΔf (IcRel.blockS hbrel)
          rw [show resb = _ from heqb] at hsb
          have hsb' : Step D cenv₂ (decl₂.params.zip argvals ++ bindZeros D decl₂.rets)
              st1 (.stmt (.block decl₂.body)) (.sres Vend st2 o) := by
            rw [← hps, ← hrs]
            exact hsb
          have harity' : argvals.length = decl₂.params.length := by
            rw [← hps]; exact harity
          refine ⟨_, Step.callOk hs hlk₂ harity' hsb' ho, ?_⟩
          show Res.eres (.vals (decl₂.rets.map _) st2) =
            Res.eres (.vals (decl.rets.map _) st2)
          rw [← hrs]
  | @callHalt funs V st fn args argvals st1 decl cenv Vend st2 ha hlk harity hbody iha ihbody =>
      intro funs₂ Δ pc' hR hΔ hrel
      cases hrel with
      | expr =>
          obtain ⟨resa, hs, heqa⟩ := iha hR hΔ IcRel.args
          rw [show resa = _ from heqa] at hs
          obtain ⟨decl₂, cenv₂, hlk₂, hdecl, hcenvR⟩ := lookupFun_icFunsRel hR hlk
          obtain ⟨hps, hrs, Δf, hΔf, hbrel⟩ := hdecl
          obtain ⟨resb, hsb, heqb⟩ := ihbody hcenvR hΔf (IcRel.blockS hbrel)
          rw [show resb = _ from heqb] at hsb
          have hsb' : Step D cenv₂ (decl₂.params.zip argvals ++ bindZeros D decl₂.rets)
              st1 (.stmt (.block decl₂.body)) (.sres Vend st2 .halt) := by
            rw [← hps, ← hrs]
            exact hsb
          have harity' : argvals.length = decl₂.params.length := by
            rw [← hps]; exact harity
          exact ⟨_, Step.callHalt hs hlk₂ harity' hsb', rfl⟩
  | @callArgsHalt funs V st fn args st1 ha iha =>
      intro funs₂ Δ pc' hR hΔ hrel
      cases hrel with
      | expr =>
          obtain ⟨resa, hs, heqa⟩ := iha hR hΔ IcRel.args
          rw [show resa = _ from heqa] at hs
          exact ⟨_, Step.callArgsHalt hs, rfl⟩
  | @argsNil funs V st =>
      intro funs₂ Δ pc' hR hΔ hrel
      cases hrel with
      | args => exact ⟨_, Step.argsNil, rfl⟩
  | @argsCons funs V st e rest restvals st1 v st2 hrest he ihrest ihe =>
      intro funs₂ Δ pc' hR hΔ hrel
      cases hrel with
      | args =>
          obtain ⟨res₁, hs₁, heq₁⟩ := ihrest hR hΔ IcRel.args
          rw [show res₁ = _ from heq₁] at hs₁
          obtain ⟨res₂, hs₂, heq₂⟩ := ihe hR hΔ IcRel.expr
          rw [show res₂ = _ from heq₂] at hs₂
          exact ⟨_, Step.argsCons hs₁ hs₂, rfl⟩
  | @argsRestHalt funs V st e rest st1 hrest ihrest =>
      intro funs₂ Δ pc' hR hΔ hrel
      cases hrel with
      | args =>
          obtain ⟨res₁, hs₁, heq₁⟩ := ihrest hR hΔ IcRel.args
          rw [show res₁ = _ from heq₁] at hs₁
          exact ⟨_, Step.argsRestHalt hs₁, rfl⟩
  | @argsHeadHalt funs V st e rest restvals st1 st2 hrest he ihrest ihe =>
      intro funs₂ Δ pc' hR hΔ hrel
      cases hrel with
      | args =>
          obtain ⟨res₁, hs₁, heq₁⟩ := ihrest hR hΔ IcRel.args
          rw [show res₁ = _ from heq₁] at hs₁
          obtain ⟨res₂, hs₂, heq₂⟩ := ihe hR hΔ IcRel.expr
          rw [show res₂ = _ from heq₂] at hs₂
          exact ⟨_, Step.argsHeadHalt hs₁ hs₂, rfl⟩
  | @funDef funs V st n ps rs b =>
      intro funs₂ Δ pc' hR hΔ hrel
      cases hrel with
      | funDefS hbrel => exact ⟨_, Step.funDef, rfl⟩
  | @block funs V st body Vb stb o hb ihb =>
      intro funs₂ Δ pc' hR hΔ hrel
      cases hrel with
      | @blockS _ _ body' hbrel =>
          have hcompat := DeltaCompat.extend (calls := calls) (creates := creates)
            hΔ body
          have hfr : IcFunsRel (calls := calls) (creates := creates)
              (hoist D body :: funs) (hoist D body' :: funs₂) :=
            .cons (icScopeRel_of_block hbrel hcompat) hR
          obtain ⟨res₂, hs, hres⟩ := ihb hfr hcompat hbrel
          cases hres with
          | refl => exact ⟨_, Step.block hs, rfl⟩
          | haltIns Zp =>
              have hb2 := Step.block (funs := funs₂) hs
              rw [restore_prefix_le (venvLen_mono hb rfl)] at hb2
              exact ⟨_, hb2, rfl⟩
  | @letZero funs V st vars =>
      intro funs₂ Δ pc' hR hΔ hrel
      cases hrel with
      | letS => exact ⟨_, Step.letZero, rfl⟩
  | @letVal funs V st vars e vals st1 he hlen ihe =>
      intro funs₂ Δ pc' hR hΔ hrel
      cases hrel with
      | letS =>
          obtain ⟨res₂, hs, heq⟩ := ihe hR hΔ IcRel.expr
          rw [show res₂ = _ from heq] at hs
          exact ⟨_, Step.letVal hs hlen, rfl⟩
  | @letHalt funs V st vars e st1 he ihe =>
      intro funs₂ Δ pc' hR hΔ hrel
      cases hrel with
      | letS =>
          obtain ⟨res₂, hs, heq⟩ := ihe hR hΔ IcRel.expr
          rw [show res₂ = _ from heq] at hs
          exact ⟨_, Step.letHalt hs, rfl⟩
  | @assignVal funs V st vars e vals st1 he hlen ihe =>
      intro funs₂ Δ pc' hR hΔ hrel
      cases hrel with
      | assignS =>
          obtain ⟨res₂, hs, heq⟩ := ihe hR hΔ IcRel.expr
          rw [show res₂ = _ from heq] at hs
          exact ⟨_, Step.assignVal hs hlen, rfl⟩
  | @assignHalt funs V st vars e st1 he ihe =>
      intro funs₂ Δ pc' hR hΔ hrel
      cases hrel with
      | assignS =>
          obtain ⟨res₂, hs, heq⟩ := ihe hR hΔ IcRel.expr
          rw [show res₂ = _ from heq] at hs
          exact ⟨_, Step.assignHalt hs, rfl⟩
  | @exprStmt funs V st e st1 he ihe =>
      intro funs₂ Δ pc' hR hΔ hrel
      cases hrel with
      | exprStmtS =>
          obtain ⟨res₂, hs, heq⟩ := ihe hR hΔ IcRel.expr
          rw [show res₂ = _ from heq] at hs
          exact ⟨_, Step.exprStmt hs, rfl⟩
  | @exprStmtHalt funs V st e st1 he ihe =>
      intro funs₂ Δ pc' hR hΔ hrel
      cases hrel with
      | exprStmtS =>
          obtain ⟨res₂, hs, heq⟩ := ihe hR hΔ IcRel.expr
          rw [show res₂ = _ from heq] at hs
          exact ⟨_, Step.exprStmtHalt hs, rfl⟩
  | @ifTrue funs V st c body cv st1 V' st2 o hc hcv hbody ihc ihbody =>
      intro funs₂ Δ pc' hR hΔ hrel
      cases hrel with
      | @condS _ _ _ body' hbrel =>
          obtain ⟨res₁, hs₁, heq₁⟩ := ihc hR hΔ IcRel.expr
          rw [show res₁ = _ from heq₁] at hs₁
          obtain ⟨res₂, hs₂, heq₂⟩ := ihbody hR hΔ (IcRel.blockS hbrel)
          rw [show res₂ = _ from heq₂] at hs₂
          exact ⟨_, Step.ifTrue hs₁ hcv hs₂, rfl⟩
  | @ifFalse funs V st c body cv st1 hc hcv ihc =>
      intro funs₂ Δ pc' hR hΔ hrel
      cases hrel with
      | condS hbrel =>
          obtain ⟨res₁, hs₁, heq₁⟩ := ihc hR hΔ IcRel.expr
          rw [show res₁ = _ from heq₁] at hs₁
          exact ⟨_, Step.ifFalse hs₁ hcv, rfl⟩
  | @ifHalt funs V st c body st1 hc ihc =>
      intro funs₂ Δ pc' hR hΔ hrel
      cases hrel with
      | condS hbrel =>
          obtain ⟨res₁, hs₁, heq₁⟩ := ihc hR hΔ IcRel.expr
          rw [show res₁ = _ from heq₁] at hs₁
          exact ⟨_, Step.ifHalt hs₁, rfl⟩
  | @switchExec funs V st c cases' dflt cv st1 V' st2 o hc hsel ihc ihsel =>
      intro funs₂ Δ pc' hR hΔ hrel
      cases hrel with
      | switchS hcs hd =>
          obtain ⟨res₁, hs₁, heq₁⟩ := ihc hR hΔ IcRel.expr
          rw [show res₁ = _ from heq₁] at hs₁
          obtain ⟨res₂, hs₂, heq₂⟩ := ihsel hR hΔ (IcRel.selectRel hcs hd cv)
          rw [show res₂ = _ from heq₂] at hs₂
          exact ⟨_, Step.switchExec hs₁ hs₂, rfl⟩
  | @switchHalt funs V st c cases' dflt st1 hc ihc =>
      intro funs₂ Δ pc' hR hΔ hrel
      cases hrel with
      | switchS hcs hd =>
          obtain ⟨res₁, hs₁, heq₁⟩ := ihc hR hΔ IcRel.expr
          rw [show res₁ = _ from heq₁] at hs₁
          exact ⟨_, Step.switchHalt hs₁, rfl⟩
  | @forLoop funs V st init c post body Vinit stinit Vend stend o hinit hloop ihinit ihloop =>
      intro funs₂ Δ pc' hR hΔ hrel
      cases hrel with
      | @forS _ _ _ _ post' _ body' hpost hbody =>
          have hfr : IcFunsRel (calls := calls) (creates := creates)
              (hoist D init :: funs) (hoist D init :: funs₂) :=
            .cons (icScopeRel_refl _ _) hR
          obtain ⟨res₁, hs₁, hres₁⟩ := ihinit hfr (DeltaCompat.nil _)
            (IcRel.reflStmts [] init)
          cases hres₁ with
          | refl =>
              obtain ⟨res₂, hs₂, heq₂⟩ := ihloop hfr
                (DeltaCompat.pruneInit hΔ init)
                (IcRel.loopL hpost hbody)
              rw [show res₂ = _ from heq₂] at hs₂
              exact ⟨_, Step.forLoop hs₁ hs₂, rfl⟩
  | @forInitHalt funs V st init c post body Vinit stinit hinit ihinit =>
      intro funs₂ Δ pc' hR hΔ hrel
      cases hrel with
      | @forS _ _ _ _ post' _ body' hpost hbody =>
          have hfr : IcFunsRel (calls := calls) (creates := creates)
              (hoist D init :: funs) (hoist D init :: funs₂) :=
            .cons (icScopeRel_refl _ _) hR
          obtain ⟨res₁, hs₁, hres₁⟩ := ihinit hfr (DeltaCompat.nil _)
            (IcRel.reflStmts [] init)
          cases hres₁ with
          | refl => exact ⟨_, Step.forInitHalt hs₁, rfl⟩
          | haltIns Zp =>
              have hb2 := Step.forInitHalt (c := c) (post := post') (body := body')
                (funs := funs₂) hs₁
              rw [restore_prefix_le (venvLen_mono hinit rfl)] at hb2
              exact ⟨_, hb2, rfl⟩
  | @«break» funs V st =>
      intro funs₂ Δ pc' hR hΔ hrel
      cases hrel with
      | breakS => exact ⟨_, Step.break, rfl⟩
  | @«continue» funs V st =>
      intro funs₂ Δ pc' hR hΔ hrel
      cases hrel with
      | continueS => exact ⟨_, Step.continue, rfl⟩
  | @leave funs V st =>
      intro funs₂ Δ pc' hR hΔ hrel
      cases hrel with
      | leaveS => exact ⟨_, Step.leave, rfl⟩
  | @seqNil funs V st =>
      intro funs₂ Δ pc' hR hΔ hrel
      cases hrel with
      | nilSS => exact ⟨_, Step.seqNil, .refl _⟩
  | @seqCons funs V st s rest V1 st1 V2 st2 o hs hrest ihs ihrest =>
      intro funs₂ Δ pc' hR hΔ hrel
      cases hrel with
      | consSS hsrel hrestrel =>
          obtain ⟨res₁, hs₁, heq₁⟩ := ihs hR hΔ hsrel
          rw [show res₁ = _ from heq₁] at hs₁
          obtain ⟨res₂, hs₂, hres₂⟩ := ihrest hR hΔ hrestrel
          cases hres₂ with
          | refl => exact ⟨_, Step.seqCons hs₁ hs₂, .refl _⟩
          | haltIns Zp => exact ⟨_, Step.seqCons hs₁ hs₂, .haltIns _ _ _⟩
      | @siteLet _ f d xs as _ rest' hld hnd hsc hok hrestrel =>
          obtain ⟨hlen_as, hlen_xs, hxnd, hnc, hsh, hxout, hxlet⟩ := siteOK_inv hok
          obtain ⟨body₀, cenv₀, hlk₀X, hb₀X⟩ := hΔ (f, d) (lookupDelta_mem hld)
          have hlk₀ : lookupFun funs f =
              some (⟨d.ps, d.rs, body₀⟩, cenv₀) := hlk₀X
          have hb₀ : body₀ = d.ss ∨ body₀ = d.ss ++ [.leave] := hb₀X
          cases hs with
          | @letVal _ _ _ _ _ vals stv he hlenv =>
              cases he with
              | @callOk _ _ _ _ _ argvals st1' decl cenv Vend st2' o' ha hlk harity hbody ho =>
                  rw [hlk₀] at hlk
                  injection hlk with hlk
                  injection hlk with hdecl hcenv
                  subst hdecl hcenv
                  have harity' : argvals.length = d.ps.length := harity
                  have hbody' := body_normalize_ok hb₀ hsc
                    (by
                      intro x hx
                      rw [calleeFrame_keys (by omega)]
                      exact hx) hbody ho
                  have hZvars : ∀ y ∈ varsList as,
                      y ∉ (bindZeros D xs).map Prod.fst := by
                    intro y hy
                    rw [bindZeros_keys]
                    exact hxlet rfl y hy
                  have hcore := inlineCore_fwd_normal hnd hsc hlen_as hnc hsh
                    hxout hlen_xs ha hbody' hZvars funs₂
                  have hsm : VEnv.setMany (bindZeros D xs ++ V) xs
                      (d.rs.map (fun r => (VEnv.get Vend r).getD
                        (evmWithExternal calls creates).zero)) =
                      xs.zip (d.rs.map (fun r => (VEnv.get Vend r).getD
                        (evmWithExternal calls creates).zero)) ++ V :=
                    VEnv.setMany_bindZeros hxnd
                      (by simp only [List.length_map]; omega) V
                  rw [hsm] at hcore
                  obtain ⟨res₂, hs₂, hres₂⟩ := ihrest hR hΔ hrestrel
                  cases hres₂ with
                  | refl =>
                      exact ⟨_, Step.seqCons Step.letZero
                        (Step.seqCons hcore hs₂), .refl _⟩
                  | haltIns Zp =>
                      exact ⟨_, Step.seqCons Step.letZero
                        (Step.seqCons hcore hs₂), .haltIns _ _ _⟩
      | @siteAssign _ f d xs as _ rest' hld hnd hsc hok hrestrel =>
          obtain ⟨hlen_as, hlen_xs, hxnd, hnc, hsh, hxout, -⟩ := siteOK_inv hok
          obtain ⟨body₀, cenv₀, hlk₀X, hb₀X⟩ := hΔ (f, d) (lookupDelta_mem hld)
          have hlk₀ : lookupFun funs f =
              some (⟨d.ps, d.rs, body₀⟩, cenv₀) := hlk₀X
          have hb₀ : body₀ = d.ss ∨ body₀ = d.ss ++ [.leave] := hb₀X
          have hZvars : ∀ y ∈ varsList as,
              y ∉ (([] : VEnv D)).map Prod.fst := by
            intro y hy
            simp
          cases hs with
          | @assignVal _ _ _ _ _ vals stv he hlenv =>
              cases he with
              | @callOk _ _ _ _ _ argvals st1' decl cenv Vend st2' o' ha hlk harity hbody ho =>
                  rw [hlk₀] at hlk
                  injection hlk with hlk
                  injection hlk with hdecl hcenv
                  subst hdecl hcenv
                  have harity' : argvals.length = d.ps.length := harity
                  have hbody' := body_normalize_ok hb₀ hsc
                    (by
                      intro x hx
                      rw [calleeFrame_keys (by omega)]
                      exact hx) hbody ho
                  have hcore := inlineCore_fwd_normal hnd hsc hlen_as hnc hsh
                    hxout hlen_xs (Z := []) ha hbody' hZvars funs₂
                  obtain ⟨res₂, hs₂, hres₂⟩ := ihrest hR hΔ hrestrel
                  cases hres₂ with
                  | refl => exact ⟨_, Step.seqCons hcore hs₂, .refl _⟩
                  | haltIns Zp => exact ⟨_, Step.seqCons hcore hs₂, .haltIns _ _ _⟩
      | @siteExpr _ f d as _ rest' hld hnd hsc hok hrestrel =>
          obtain ⟨hlen_as, hlen_xs, -, hnc, hsh, -, -⟩ := siteOK_inv hok
          obtain ⟨body₀, cenv₀, hlk₀X, hb₀X⟩ := hΔ (f, d) (lookupDelta_mem hld)
          have hlk₀ : lookupFun funs f =
              some (⟨d.ps, d.rs, body₀⟩, cenv₀) := hlk₀X
          have hb₀ : body₀ = d.ss ∨ body₀ = d.ss ++ [.leave] := hb₀X
          have hrs0 : d.rs = [] := by
            cases hrs : d.rs with
            | nil => rfl
            | cons r rs' => rw [hrs] at hlen_xs; simp at hlen_xs
          have hZvars : ∀ y ∈ varsList as,
              y ∉ (([] : VEnv D)).map Prod.fst := by
            intro y hy
            simp
          cases hs with
          | @exprStmt _ _ _ _ stv he =>
              obtain ⟨vs, he', hvs⟩ :
                  ∃ vs, Step D funs V st (.expr (.call f as))
                    (.eres (.vals vs st1)) ∧ vs = [] := ⟨[], he, rfl⟩
              cases he' with
              | @callOk _ _ _ _ _ argvals st1' decl cenv Vend st2' o' ha hlk harity hbody ho =>
                  rw [hlk₀] at hlk
                  injection hlk with hlk
                  injection hlk with hdecl hcenv
                  subst hdecl hcenv
                  have harity' : argvals.length = d.ps.length := harity
                  have hargsl := args_length ha
                  have hbody' := body_normalize_ok hb₀ hsc
                    (by
                      intro x hx
                      rw [calleeFrame_keys (by omega)]
                      exact hx) hbody ho
                  have hcore := inlineCore_fwd_normal hnd hsc hlen_as hnc hsh
                    (fun x hx => by cases hx) hlen_xs (Z := []) ha hbody'
                    hZvars funs₂
                  obtain ⟨res₂, hs₂, hres₂⟩ := ihrest hR hΔ hrestrel
                  have hcore' : Step D funs₂ V st
                      (.stmt (inlineCore d [] as)) (.sres V st1 .normal) := by
                    have hsm : VEnv.setMany (([] : VEnv D) ++ V) []
                        (d.rs.map (fun r => (VEnv.get Vend r).getD
                          (evmWithExternal calls creates).zero)) = V := rfl
                    rw [hsm] at hcore
                    exact hcore
                  cases hres₂ with
                  | refl => exact ⟨_, Step.seqCons hcore' hs₂, .refl _⟩
                  | haltIns Zp => exact ⟨_, Step.seqCons hcore' hs₂, .haltIns _ _ _⟩
  | @seqStop funs V st s rest V1 st1 o hs hne ihs =>
      intro funs₂ Δ pc' hR hΔ hrel
      cases hrel with
      | consSS hsrel hrestrel =>
          obtain ⟨res₁, hs₁, heq₁⟩ := ihs hR hΔ hsrel
          rw [show res₁ = _ from heq₁] at hs₁
          exact ⟨_, Step.seqStop hs₁ hne, .refl _⟩
      | @siteLet _ f d xs as _ rest' hld hnd hsc hok hrestrel =>
          obtain ⟨hlen_as, hlen_xs, hxnd, hnc, hsh, hxout, hxlet⟩ := siteOK_inv hok
          obtain ⟨body₀, cenv₀, hlk₀X, hb₀X⟩ := hΔ (f, d) (lookupDelta_mem hld)
          have hlk₀ : lookupFun funs f =
              some (⟨d.ps, d.rs, body₀⟩, cenv₀) := hlk₀X
          have hb₀ : body₀ = d.ss ∨ body₀ = d.ss ++ [.leave] := hb₀X
          cases hs with
          | @letVal _ _ _ _ _ vals stv he hlenv => exact absurd rfl hne
          | @letHalt _ _ _ _ _ sth he =>
              cases he with
              | @callHalt _ _ _ _ _ argvals st1' decl cenv Vend st2' ha hlk harity hbody =>
                  rw [hlk₀] at hlk
                  injection hlk with hlk
                  injection hlk with hdecl hcenv
                  subst hdecl hcenv
                  have hbody' := body_normalize_halt hb₀ hbody
                  have hZvars : ∀ y ∈ varsList as,
                      y ∉ (bindZeros D xs).map Prod.fst := by
                    intro y hy
                    rw [bindZeros_keys]
                    exact hxlet rfl y hy
                  have hcore := inlineCore_fwd_bodyhalt (xs := xs)
                    (Z := bindZeros D xs) hsc hlen_as hnc hsh
                    ha hbody' hZvars funs₂
                  refine ⟨_, Step.seqCons Step.letZero
                    (Step.seqStop hcore (by simp)), ?_⟩
                  exact .haltIns _ _ _
              | @callArgsHalt _ _ _ _ _ _ ha =>
                  have hZvars : ∀ y ∈ varsList as,
                      y ∉ (bindZeros D xs).map Prod.fst := by
                    intro y hy
                    rw [bindZeros_keys]
                    exact hxlet rfl y hy
                  have hcore := inlineCore_fwd_argshalt (d := d) (xs := xs)
                    (Z := bindZeros D xs) hlen_as hnc hsh
                    ha hZvars funs₂
                  refine ⟨_, Step.seqCons Step.letZero
                    (Step.seqStop hcore (by simp)), ?_⟩
                  exact .haltIns _ _ _
      | @siteAssign _ f d xs as _ rest' hld hnd hsc hok hrestrel =>
          obtain ⟨hlen_as, hlen_xs, hxnd, hnc, hsh, hxout, -⟩ := siteOK_inv hok
          obtain ⟨body₀, cenv₀, hlk₀X, hb₀X⟩ := hΔ (f, d) (lookupDelta_mem hld)
          have hlk₀ : lookupFun funs f =
              some (⟨d.ps, d.rs, body₀⟩, cenv₀) := hlk₀X
          have hb₀ : body₀ = d.ss ∨ body₀ = d.ss ++ [.leave] := hb₀X
          have hZvars : ∀ y ∈ varsList as,
              y ∉ (([] : VEnv D)).map Prod.fst := by
            intro y hy
            simp
          cases hs with
          | @assignVal _ _ _ _ _ vals stv he hlenv => exact absurd rfl hne
          | @assignHalt _ _ _ _ _ sth he =>
              cases he with
              | @callHalt _ _ _ _ _ argvals st1' decl cenv Vend st2' ha hlk harity hbody =>
                  rw [hlk₀] at hlk
                  injection hlk with hlk
                  injection hlk with hdecl hcenv
                  subst hdecl hcenv
                  have hbody' := body_normalize_halt hb₀ hbody
                  have hcore := inlineCore_fwd_bodyhalt (xs := xs)
                    (Z := []) hsc hlen_as hnc hsh ha hbody' hZvars funs₂
                  exact ⟨_, Step.seqStop hcore (by simp), .refl _⟩
              | @callArgsHalt _ _ _ _ _ _ ha =>
                  have hcore := inlineCore_fwd_argshalt (d := d) (xs := xs)
                    (Z := []) hlen_as hnc hsh ha hZvars funs₂
                  exact ⟨_, Step.seqStop hcore (by simp), .refl _⟩
      | @siteExpr _ f d as _ rest' hld hnd hsc hok hrestrel =>
          obtain ⟨hlen_as, hlen_xs, -, hnc, hsh, -, -⟩ := siteOK_inv hok
          obtain ⟨body₀, cenv₀, hlk₀X, hb₀X⟩ := hΔ (f, d) (lookupDelta_mem hld)
          have hlk₀ : lookupFun funs f =
              some (⟨d.ps, d.rs, body₀⟩, cenv₀) := hlk₀X
          have hb₀ : body₀ = d.ss ∨ body₀ = d.ss ++ [.leave] := hb₀X
          have hZvars : ∀ y ∈ varsList as,
              y ∉ (([] : VEnv D)).map Prod.fst := by
            intro y hy
            simp
          cases hs with
          | @exprStmt _ _ _ _ stv he => exact absurd rfl hne
          | @exprStmtHalt _ _ _ _ sth he =>
              cases he with
              | @callHalt _ _ _ _ _ argvals st1' decl cenv Vend st2' ha hlk harity hbody =>
                  rw [hlk₀] at hlk
                  injection hlk with hlk
                  injection hlk with hdecl hcenv
                  subst hdecl hcenv
                  have hbody' := body_normalize_halt hb₀ hbody
                  have hcore := inlineCore_fwd_bodyhalt (xs := ([] : List Ident))
                    (Z := []) hsc hlen_as hnc hsh ha hbody' hZvars funs₂
                  exact ⟨_, Step.seqStop hcore (by simp), .refl _⟩
              | @callArgsHalt _ _ _ _ _ _ ha =>
                  have hcore := inlineCore_fwd_argshalt (d := d) (xs := ([] : List Ident))
                    (Z := []) hlen_as hnc hsh ha hZvars funs₂
                  exact ⟨_, Step.seqStop hcore (by simp), .refl _⟩
  | @loopDone funs V st c post body cv st1 hc hcz ihc =>
      intro funs₂ Δ pc' hR hΔ hrel
      cases hrel with
      | loopL hpost hbody =>
          obtain ⟨res₁, hs₁, heq₁⟩ := ihc hR hΔ IcRel.expr
          rw [show res₁ = _ from heq₁] at hs₁
          exact ⟨_, Step.loopDone hs₁ hcz, rfl⟩
  | @loopCondHalt funs V st c post body st1 hc ihc =>
      intro funs₂ Δ pc' hR hΔ hrel
      cases hrel with
      | loopL hpost hbody =>
          obtain ⟨res₁, hs₁, heq₁⟩ := ihc hR hΔ IcRel.expr
          rw [show res₁ = _ from heq₁] at hs₁
          exact ⟨_, Step.loopCondHalt hs₁, rfl⟩
  | @loopStep funs V st c post body cv st1 Vb stb ob Vp stp Vend stend o hc hcv hbody hob hpost hnext ihc ihbody ihpost ihnext =>
      intro funs₂ Δ pc' hR hΔ hrel
      cases hrel with
      | @loopL _ _ _ post' _ body' hpostrel hbodyrel =>
          obtain ⟨res₁, hs₁, heq₁⟩ := ihc hR hΔ IcRel.expr
          rw [show res₁ = _ from heq₁] at hs₁
          obtain ⟨res₂, hs₂, heq₂⟩ := ihbody hR hΔ (IcRel.blockS hbodyrel)
          rw [show res₂ = _ from heq₂] at hs₂
          obtain ⟨res₃, hs₃, heq₃⟩ := ihpost hR hΔ (IcRel.blockS hpostrel)
          rw [show res₃ = _ from heq₃] at hs₃
          obtain ⟨res₄, hs₄, heq₄⟩ := ihnext hR hΔ (IcRel.loopL hpostrel hbodyrel)
          rw [show res₄ = _ from heq₄] at hs₄
          exact ⟨_, Step.loopStep hs₁ hcv hs₂ hob hs₃ hs₄, rfl⟩
  | @loopPostHalt funs V st c post body cv st1 Vb stb ob Vp stp hc hcv hbody hob hpost ihc ihbody ihpost =>
      intro funs₂ Δ pc' hR hΔ hrel
      cases hrel with
      | loopL hpostrel hbodyrel =>
          obtain ⟨res₁, hs₁, heq₁⟩ := ihc hR hΔ IcRel.expr
          rw [show res₁ = _ from heq₁] at hs₁
          obtain ⟨res₂, hs₂, heq₂⟩ := ihbody hR hΔ (IcRel.blockS hbodyrel)
          rw [show res₂ = _ from heq₂] at hs₂
          obtain ⟨res₃, hs₃, heq₃⟩ := ihpost hR hΔ (IcRel.blockS hpostrel)
          rw [show res₃ = _ from heq₃] at hs₃
          exact ⟨_, Step.loopPostHalt hs₁ hcv hs₂ hob hs₃, rfl⟩
  | @loopBreak funs V st c post body cv st1 Vb stb hc hcv hbody ihc ihbody =>
      intro funs₂ Δ pc' hR hΔ hrel
      cases hrel with
      | loopL hpostrel hbodyrel =>
          obtain ⟨res₁, hs₁, heq₁⟩ := ihc hR hΔ IcRel.expr
          rw [show res₁ = _ from heq₁] at hs₁
          obtain ⟨res₂, hs₂, heq₂⟩ := ihbody hR hΔ (IcRel.blockS hbodyrel)
          rw [show res₂ = _ from heq₂] at hs₂
          exact ⟨_, Step.loopBreak hs₁ hcv hs₂, rfl⟩
  | @loopLeave funs V st c post body cv st1 Vb stb hc hcv hbody ihc ihbody =>
      intro funs₂ Δ pc' hR hΔ hrel
      cases hrel with
      | loopL hpostrel hbodyrel =>
          obtain ⟨res₁, hs₁, heq₁⟩ := ihc hR hΔ IcRel.expr
          rw [show res₁ = _ from heq₁] at hs₁
          obtain ⟨res₂, hs₂, heq₂⟩ := ihbody hR hΔ (IcRel.blockS hbodyrel)
          rw [show res₂ = _ from heq₂] at hs₂
          exact ⟨_, Step.loopLeave hs₁ hcv hs₂, rfl⟩
  | @loopBodyHalt funs V st c post body cv st1 Vb stb hc hcv hbody ihc ihbody =>
      intro funs₂ Δ pc' hR hΔ hrel
      cases hrel with
      | loopL hpostrel hbodyrel =>
          obtain ⟨res₁, hs₁, heq₁⟩ := ihc hR hΔ IcRel.expr
          rw [show res₁ = _ from heq₁] at hs₁
          obtain ⟨res₂, hs₂, heq₂⟩ := ihbody hR hΔ (IcRel.blockS hbodyrel)
          rw [show res₂ = _ from heq₂] at hs₂
          exact ⟨_, Step.loopBodyHalt hs₁ hcv hs₂, rfl⟩

/-- Reconstruct a call-body run from its normalized form (re-attaching the
trailing `leave`), in the shape `callOk` expects. -/
theorem body_denormalize_ok {d : IDecl} {body₀ : List (Stmt Op)}
    (hb : body₀ = d.ss ∨ body₀ = d.ss ++ [.leave])
    {cenv : FunEnv D} {E : VEnv D} {st1 st2 : EvmState} {Vend : VEnv D}
    (hbody : Step D cenv E st1 (.stmt (.block d.ss)) (.sres Vend st2 .normal)) :
    ∃ o, Step D cenv E st1 (.stmt (.block body₀)) (.sres Vend st2 o) ∧
      (o = .normal ∨ o = .leave) := by
  rcases hb with rfl | rfl
  · exact ⟨.normal, hbody, Or.inl rfl⟩
  · have := block_trailing_leave_bwd hbody
    rw [if_pos rfl] at this
    exact ⟨.leave, this, Or.inr rfl⟩

/-- ... and its halting form. -/
theorem body_denormalize_halt {d : IDecl} {body₀ : List (Stmt Op)}
    (hb : body₀ = d.ss ∨ body₀ = d.ss ++ [.leave])
    {cenv : FunEnv D} {E : VEnv D} {st1 st2 : EvmState} {Vend : VEnv D}
    (hbody : Step D cenv E st1 (.stmt (.block d.ss)) (.sres Vend st2 .halt)) :
    Step D cenv E st1 (.stmt (.block body₀)) (.sres Vend st2 .halt) := by
  rcases hb with rfl | rfl
  · exact hbody
  · have := block_trailing_leave_bwd hbody
    rw [if_neg (by simp)] at this
    exact this

/-- A `let`-form site weakens to its assign-form conditions. -/
theorem siteOK_weaken {d : IDecl} {xs : List Ident} {as : List (Expr Op)}
    (h : siteOK d xs as true = true) : siteOK d xs as false = true := by
  unfold siteOK at h ⊢
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true, Bool.and_eq_true] at h ⊢
  exact ⟨h.1, by simp⟩

/-- A call expression with call-free arguments evaluates identically under an
extension whose names its arguments avoid (the callee itself runs in a fresh
environment and resolves in the unchanged function environment). -/
theorem callExpr_extend_bwd {funs : FunEnv D} {N V : VEnv D} {st : EvmState}
    {f : Ident} {as : List (Expr Op)} {r : EResult D}
    (h : Step D funs (N ++ V) st (.expr (.call f as)) (.eres r))
    (hnc : argsHaveCall as = false)
    (hN : ∀ y ∈ varsList as, y ∉ N.map Prod.fst) :
    Step D funs V st (.expr (.call f as)) (.eres r) := by
  have hag : ∀ y ∈ varsList as, VEnv.get V y = VEnv.get (N ++ V) y := by
    intro y hy
    rw [VEnv.get_append_not_mem (hN y hy)]
  cases h with
  | callOk ha hlk harity hbody ho =>
      exact Step.callOk (exprNoCall_transfer ha funs ⟨hnc, hag⟩) hlk harity hbody ho
  | callHalt ha hlk harity hbody =>
      exact Step.callHalt (exprNoCall_transfer ha funs ⟨hnc, hag⟩) hlk harity hbody
  | callArgsHalt ha =>
      exact Step.callArgsHalt (exprNoCall_transfer ha funs ⟨hnc, hag⟩)

/-- **Backward simulation**: a derivation of the inlined program transports
back across `IcRel` to the source. -/
theorem ic_bwd {funs₂ : FunEnv D} {V : VEnv D} {st : EvmState}
    {code₂ : Code Op} {res₂ : Res D} (h : Step D funs₂ V st code₂ res₂) :
    ∀ {funs₁ : FunEnv D} {Δ : DEnv} {pc : PCode Op},
      IcFunsRel (calls := calls) (creates := creates) funs₁ funs₂ →
      DeltaCompat (calls := calls) (creates := creates) Δ funs₁ →
      IcRel Δ pc (toPCode code₂) →
      ∃ res₁, Step D funs₁ V st (ofPCode pc) res₁ ∧
        icResOK (calls := calls) (creates := creates) code₂ res₁ res₂ := by
  induction h with
  | @lit funs V st l =>
      intro funs₁ Δ pc hR hΔ hrel
      cases hrel with
      | expr => exact ⟨_, Step.lit, rfl⟩
  | @var funs V st x v hv =>
      intro funs₁ Δ pc hR hΔ hrel
      cases hrel with
      | expr => exact ⟨_, Step.var hv, rfl⟩
  | @builtinOk funs V st op args argvals st1 rets st2 ha hbi iha =>
      intro funs₁ Δ pc hR hΔ hrel
      cases hrel with
      | expr =>
          obtain ⟨res₁, hs, heq⟩ := iha hR hΔ IcRel.args
          have heqX : _ = res₁ := heq
          rw [← heqX] at hs
          exact ⟨_, Step.builtinOk hs hbi, rfl⟩
  | @builtinHalt funs V st op args argvals st1 st2 ha hbi iha =>
      intro funs₁ Δ pc hR hΔ hrel
      cases hrel with
      | expr =>
          obtain ⟨res₁, hs, heq⟩ := iha hR hΔ IcRel.args
          have heqX : _ = res₁ := heq
          rw [← heqX] at hs
          exact ⟨_, Step.builtinHalt hs hbi, rfl⟩
  | @builtinArgsHalt funs V st op args st1 ha iha =>
      intro funs₁ Δ pc hR hΔ hrel
      cases hrel with
      | expr =>
          obtain ⟨res₁, hs, heq⟩ := iha hR hΔ IcRel.args
          have heqX : _ = res₁ := heq
          rw [← heqX] at hs
          exact ⟨_, Step.builtinArgsHalt hs, rfl⟩
  | @callOk funs V st fn args argvals st1 decl cenv Vend st2 o ha hlk harity hbody ho iha ihbody =>
      intro funs₁ Δ pc hR hΔ hrel
      cases hrel with
      | expr =>
          obtain ⟨resa, hs, heqa⟩ := iha hR hΔ IcRel.args
          have heqaX : _ = resa := heqa
          rw [← heqaX] at hs
          obtain ⟨decl₁, cenv₁, hlk₁, hdecl, hcenvR⟩ := lookupFun_icFunsRel_bwd hR hlk
          obtain ⟨hps, hrs, Δf, hΔf, hbrel⟩ := hdecl
          obtain ⟨resb, hsb, heqb⟩ := ihbody hcenvR hΔf (IcRel.blockS hbrel)
          have heqbX : _ = resb := heqb
          rw [← heqbX] at hsb
          have hsb' : Step D cenv₁ (decl₁.params.zip argvals ++ bindZeros D decl₁.rets)
              st1 (.stmt (.block decl₁.body)) (.sres Vend st2 o) := by
            rw [hps, hrs]
            exact hsb
          have harity' : argvals.length = decl₁.params.length := by
            rw [hps]; exact harity
          refine ⟨_, Step.callOk hs hlk₁ harity' hsb' ho, ?_⟩
          show Res.eres (.vals (decl.rets.map _) st2) =
            Res.eres (.vals (decl₁.rets.map _) st2)
          rw [hrs]
  | @callHalt funs V st fn args argvals st1 decl cenv Vend st2 ha hlk harity hbody iha ihbody =>
      intro funs₁ Δ pc hR hΔ hrel
      cases hrel with
      | expr =>
          obtain ⟨resa, hs, heqa⟩ := iha hR hΔ IcRel.args
          have heqaX : _ = resa := heqa
          rw [← heqaX] at hs
          obtain ⟨decl₁, cenv₁, hlk₁, hdecl, hcenvR⟩ := lookupFun_icFunsRel_bwd hR hlk
          obtain ⟨hps, hrs, Δf, hΔf, hbrel⟩ := hdecl
          obtain ⟨resb, hsb, heqb⟩ := ihbody hcenvR hΔf (IcRel.blockS hbrel)
          have heqbX : _ = resb := heqb
          rw [← heqbX] at hsb
          have hsb' : Step D cenv₁ (decl₁.params.zip argvals ++ bindZeros D decl₁.rets)
              st1 (.stmt (.block decl₁.body)) (.sres Vend st2 .halt) := by
            rw [hps, hrs]
            exact hsb
          have harity' : argvals.length = decl₁.params.length := by
            rw [hps]; exact harity
          exact ⟨_, Step.callHalt hs hlk₁ harity' hsb', rfl⟩
  | @callArgsHalt funs V st fn args st1 ha iha =>
      intro funs₁ Δ pc hR hΔ hrel
      cases hrel with
      | expr =>
          obtain ⟨resa, hs, heqa⟩ := iha hR hΔ IcRel.args
          have heqaX : _ = resa := heqa
          rw [← heqaX] at hs
          exact ⟨_, Step.callArgsHalt hs, rfl⟩
  | @argsNil funs V st =>
      intro funs₁ Δ pc hR hΔ hrel
      cases hrel with
      | args => exact ⟨_, Step.argsNil, rfl⟩
  | @argsCons funs V st e rest restvals st1 v st2 hrest he ihrest ihe =>
      intro funs₁ Δ pc hR hΔ hrel
      cases hrel with
      | args =>
          obtain ⟨res₁, hs₁, heq₁⟩ := ihrest hR hΔ IcRel.args
          have heq₁X : _ = res₁ := heq₁
          rw [← heq₁X] at hs₁
          obtain ⟨res₂', hs₂, heq₂⟩ := ihe hR hΔ IcRel.expr
          have heq₂X : _ = res₂' := heq₂
          rw [← heq₂X] at hs₂
          exact ⟨_, Step.argsCons hs₁ hs₂, rfl⟩
  | @argsRestHalt funs V st e rest st1 hrest ihrest =>
      intro funs₁ Δ pc hR hΔ hrel
      cases hrel with
      | args =>
          obtain ⟨res₁, hs₁, heq₁⟩ := ihrest hR hΔ IcRel.args
          have heq₁X : _ = res₁ := heq₁
          rw [← heq₁X] at hs₁
          exact ⟨_, Step.argsRestHalt hs₁, rfl⟩
  | @argsHeadHalt funs V st e rest restvals st1 st2 hrest he ihrest ihe =>
      intro funs₁ Δ pc hR hΔ hrel
      cases hrel with
      | args =>
          obtain ⟨res₁, hs₁, heq₁⟩ := ihrest hR hΔ IcRel.args
          have heq₁X : _ = res₁ := heq₁
          rw [← heq₁X] at hs₁
          obtain ⟨res₂', hs₂, heq₂⟩ := ihe hR hΔ IcRel.expr
          have heq₂X : _ = res₂' := heq₂
          rw [← heq₂X] at hs₂
          exact ⟨_, Step.argsHeadHalt hs₁ hs₂, rfl⟩
  | @funDef funs V st n ps rs b =>
      intro funs₁ Δ pc hR hΔ hrel
      cases hrel with
      | funDefS hbrel => exact ⟨_, Step.funDef, rfl⟩
  | @block funs V st body' Vb stb o hb ihb =>
      intro funs₁ Δ pc hR hΔ hrel
      cases hrel with
      | @blockS _ body _ hbrel =>
          have hcompat := DeltaCompat.extend (calls := calls) (creates := creates)
            hΔ body
          have hfr : IcFunsRel (calls := calls) (creates := creates)
              (hoist D body :: funs₁) (hoist D body' :: funs) :=
            .cons (icScopeRel_of_block hbrel hcompat) hR
          obtain ⟨res₁, hs, hres⟩ := ihb hfr hcompat hbrel
          cases hres with
          | refl => exact ⟨_, Step.block hs, rfl⟩
          | haltIns Zp V₁ _ =>
              have hb1 := Step.block (funs := funs₁) hs
              refine ⟨_, hb1, ?_⟩
              show Res.sres (restore V (Zp ++ V₁)) stb .halt =
                Res.sres (restore V V₁) stb .halt
              rw [restore_prefix_le (venvLen_mono hs rfl)]
  | @letZero funs V st vars =>
      intro funs₁ Δ pc hR hΔ hrel
      cases hrel with
      | letS => exact ⟨_, Step.letZero, rfl⟩
  | @letVal funs V st vars e vals st1 he hlen ihe =>
      intro funs₁ Δ pc hR hΔ hrel
      cases hrel with
      | letS =>
          obtain ⟨res₁, hs, heq⟩ := ihe hR hΔ IcRel.expr
          have heqX : _ = res₁ := heq
          rw [← heqX] at hs
          exact ⟨_, Step.letVal hs hlen, rfl⟩
  | @letHalt funs V st vars e st1 he ihe =>
      intro funs₁ Δ pc hR hΔ hrel
      cases hrel with
      | letS =>
          obtain ⟨res₁, hs, heq⟩ := ihe hR hΔ IcRel.expr
          have heqX : _ = res₁ := heq
          rw [← heqX] at hs
          exact ⟨_, Step.letHalt hs, rfl⟩
  | @assignVal funs V st vars e vals st1 he hlen ihe =>
      intro funs₁ Δ pc hR hΔ hrel
      cases hrel with
      | assignS =>
          obtain ⟨res₁, hs, heq⟩ := ihe hR hΔ IcRel.expr
          have heqX : _ = res₁ := heq
          rw [← heqX] at hs
          exact ⟨_, Step.assignVal hs hlen, rfl⟩
  | @assignHalt funs V st vars e st1 he ihe =>
      intro funs₁ Δ pc hR hΔ hrel
      cases hrel with
      | assignS =>
          obtain ⟨res₁, hs, heq⟩ := ihe hR hΔ IcRel.expr
          have heqX : _ = res₁ := heq
          rw [← heqX] at hs
          exact ⟨_, Step.assignHalt hs, rfl⟩
  | @exprStmt funs V st e st1 he ihe =>
      intro funs₁ Δ pc hR hΔ hrel
      cases hrel with
      | exprStmtS =>
          obtain ⟨res₁, hs, heq⟩ := ihe hR hΔ IcRel.expr
          have heqX : _ = res₁ := heq
          rw [← heqX] at hs
          exact ⟨_, Step.exprStmt hs, rfl⟩
  | @exprStmtHalt funs V st e st1 he ihe =>
      intro funs₁ Δ pc hR hΔ hrel
      cases hrel with
      | exprStmtS =>
          obtain ⟨res₁, hs, heq⟩ := ihe hR hΔ IcRel.expr
          have heqX : _ = res₁ := heq
          rw [← heqX] at hs
          exact ⟨_, Step.exprStmtHalt hs, rfl⟩
  | @ifTrue funs V st c body' cv st1 V' st2 o hc hcv hbody ihc ihbody =>
      intro funs₁ Δ pc hR hΔ hrel
      cases hrel with
      | @condS _ _ body _ hbrel =>
          obtain ⟨res₁, hs₁, heq₁⟩ := ihc hR hΔ IcRel.expr
          have heq₁X : _ = res₁ := heq₁
          rw [← heq₁X] at hs₁
          obtain ⟨res₂', hs₂, heq₂⟩ := ihbody hR hΔ (IcRel.blockS hbrel)
          have heq₂X : _ = res₂' := heq₂
          rw [← heq₂X] at hs₂
          exact ⟨_, Step.ifTrue hs₁ hcv hs₂, rfl⟩
  | @ifFalse funs V st c body' cv st1 hc hcv ihc =>
      intro funs₁ Δ pc hR hΔ hrel
      cases hrel with
      | condS hbrel =>
          obtain ⟨res₁, hs₁, heq₁⟩ := ihc hR hΔ IcRel.expr
          have heq₁X : _ = res₁ := heq₁
          rw [← heq₁X] at hs₁
          exact ⟨_, Step.ifFalse hs₁ hcv, rfl⟩
  | @ifHalt funs V st c body' st1 hc ihc =>
      intro funs₁ Δ pc hR hΔ hrel
      cases hrel with
      | condS hbrel =>
          obtain ⟨res₁, hs₁, heq₁⟩ := ihc hR hΔ IcRel.expr
          have heq₁X : _ = res₁ := heq₁
          rw [← heq₁X] at hs₁
          exact ⟨_, Step.ifHalt hs₁, rfl⟩
  | @switchExec funs V st c cases₂ dflt₂ cv st1 V' st2 o hc hsel ihc ihsel =>
      intro funs₁ Δ pc hR hΔ hrel
      cases hrel with
      | @switchS _ _ cases₁ _ dflt₁ _ hcs hd =>
          obtain ⟨res₁, hs₁, heq₁⟩ := ihc hR hΔ IcRel.expr
          have heq₁X : _ = res₁ := heq₁
          rw [← heq₁X] at hs₁
          obtain ⟨res₂', hs₂, heq₂⟩ := ihsel hR hΔ (IcRel.selectRel hcs hd cv)
          have heq₂X : _ = res₂' := heq₂
          rw [← heq₂X] at hs₂
          exact ⟨_, Step.switchExec hs₁ hs₂, rfl⟩
  | @switchHalt funs V st c cases₂ dflt₂ st1 hc ihc =>
      intro funs₁ Δ pc hR hΔ hrel
      cases hrel with
      | switchS hcs hd =>
          obtain ⟨res₁, hs₁, heq₁⟩ := ihc hR hΔ IcRel.expr
          have heq₁X : _ = res₁ := heq₁
          rw [← heq₁X] at hs₁
          exact ⟨_, Step.switchHalt hs₁, rfl⟩
  | @forLoop funs V st init c post' body' Vinit stinit Vend stend o hinit hloop ihinit ihloop =>
      intro funs₁ Δ pc hR hΔ hrel
      cases hrel with
      | @forS _ _ _ post _ body _ hpost hbody =>
          have hfr : IcFunsRel (calls := calls) (creates := creates)
              (hoist D init :: funs₁) (hoist D init :: funs) :=
            .cons (icScopeRel_refl _ _) hR
          obtain ⟨res₁, hs₁, hres₁⟩ := ihinit hfr (DeltaCompat.nil _)
            (IcRel.reflStmts [] init)
          cases hres₁ with
          | refl =>
              obtain ⟨res₂', hs₂, heq₂⟩ := ihloop hfr
                (DeltaCompat.pruneInit hΔ init)
                (IcRel.loopL hpost hbody)
              have heq₂X : _ = res₂' := heq₂
              rw [← heq₂X] at hs₂
              exact ⟨_, Step.forLoop hs₁ hs₂, rfl⟩
  | @forInitHalt funs V st init c post' body' Vinit stinit hinit ihinit =>
      intro funs₁ Δ pc hR hΔ hrel
      cases hrel with
      | @forS _ _ _ post _ body _ hpost hbody =>
          have hfr : IcFunsRel (calls := calls) (creates := creates)
              (hoist D init :: funs₁) (hoist D init :: funs) :=
            .cons (icScopeRel_refl _ _) hR
          obtain ⟨res₁, hs₁, hres₁⟩ := ihinit hfr (DeltaCompat.nil _)
            (IcRel.reflStmts [] init)
          cases hres₁ with
          | refl => exact ⟨_, Step.forInitHalt hs₁, rfl⟩
          | haltIns Zp V₁ _ =>
              have hb1 := Step.forInitHalt (c := c) (post := post) (body := body)
                (funs := funs₁) hs₁
              refine ⟨_, hb1, ?_⟩
              show Res.sres (restore V (Zp ++ V₁)) stinit .halt =
                Res.sres (restore V V₁) stinit .halt
              rw [restore_prefix_le (venvLen_mono hs₁ rfl)]
  | @«break» funs V st =>
      intro funs₁ Δ pc hR hΔ hrel
      cases hrel with
      | breakS => exact ⟨_, Step.break, rfl⟩
  | @«continue» funs V st =>
      intro funs₁ Δ pc hR hΔ hrel
      cases hrel with
      | continueS => exact ⟨_, Step.continue, rfl⟩
  | @leave funs V st =>
      intro funs₁ Δ pc hR hΔ hrel
      cases hrel with
      | leaveS => exact ⟨_, Step.leave, rfl⟩
  | @seqNil funs V st =>
      intro funs₁ Δ pc hR hΔ hrel
      cases hrel with
      | nilSS => exact ⟨_, Step.seqNil, .refl _⟩
  | @seqCons funs V st s₂ rest₂ V1 st1 V2 st2 o hs hrest ihs ihrest =>
      intro funs₁ Δ pc hR hΔ hrel
      cases hrel with
      | consSS hsrel hrestrel =>
          obtain ⟨res₁, hs₁, heq₁⟩ := ihs hR hΔ hsrel
          have heq₁X : _ = res₁ := heq₁
          rw [← heq₁X] at hs₁
          obtain ⟨res₂', hs₂, hres₂⟩ := ihrest hR hΔ hrestrel
          cases hres₂ with
          | refl => exact ⟨_, Step.seqCons hs₁ hs₂, .refl _⟩
          | haltIns Zp => exact ⟨_, Step.seqCons hs₁ hs₂, .haltIns _ _ _⟩
      | @siteLet _ f d xs as rest _ hld hnd hsc hok hrestrel =>
          -- after the zero-init the site is exactly its assign form
          obtain ⟨hlen_as, hlen_xs, hxnd, hnc, hsh, hxout, hxlet⟩ := siteOK_inv hok
          cases hs with
          | letZero =>
              obtain ⟨res₁', hs₁', hres'⟩ := ihrest hR hΔ
                (IcRel.siteAssign hld hnd hsc (siteOK_weaken hok) hrestrel)
              have hNx : ∀ y ∈ varsList as, y ∉ (bindZeros D xs).map Prod.fst := by
                intro y hy
                rw [bindZeros_keys]
                exact hxlet rfl y hy
              -- convert the assign-form source run into the let-form one
              rcases res₁' with r | ⟨V₁', st₁', o₁'⟩
              · cases hres'
              · cases hs₁' with
                | @seqCons _ _ _ _ _ Va sta _ _ _ hassign htail₁ =>
                    cases hassign with
                    | @assignVal _ _ _ _ _ vals _ he hlenv =>
                        have hcall := callExpr_extend_bwd he hnc hNx
                        have henv : VEnv.setMany (bindZeros D xs ++ V) xs vals =
                            xs.zip vals ++ V :=
                          VEnv.setMany_bindZeros hxnd (by omega) V
                        have hlet : Step D funs₁ V st
                            (.stmt (.letDecl xs (some (.call f as))))
                            (.sres (xs.zip vals ++ V) sta .normal) :=
                          Step.letVal hcall hlenv
                        rw [henv] at htail₁
                        cases hres' with
                        | refl =>
                            exact ⟨_, Step.seqCons hlet htail₁, .refl _⟩
                        | haltIns Zp =>
                            exact ⟨_, Step.seqCons hlet htail₁, .haltIns _ _ _⟩
                | @seqStop _ _ _ _ _ Va sta oa hassign hnea =>
                    cases hassign with
                    | @assignVal _ _ _ _ _ vals _ he hlenv => exact absurd rfl hnea
                    | @assignHalt _ _ _ _ _ _ he =>
                        have hcall := callExpr_extend_bwd he hnc hNx
                        have hlet : Step D funs₁ V st
                            (.stmt (.letDecl xs (some (.call f as))))
                            (.sres V st₁' .halt) := Step.letHalt hcall
                        cases hres' with
                        | refl =>
                            refine ⟨_, Step.seqStop hlet (by simp), ?_⟩
                            exact .haltIns (bindZeros D xs) _ _
                        | haltIns Zp =>
                            refine ⟨_, Step.seqStop hlet (by simp), ?_⟩
                            have : Zp ++ (bindZeros D xs ++ V) =
                                (Zp ++ bindZeros D xs) ++ V :=
                              (List.append_assoc _ _ _).symm
                            rw [this]
                            exact .haltIns (Zp ++ bindZeros D xs) _ _
      | @siteAssign _ f d xs as rest _ hld hnd hsc hok hrestrel =>
          obtain ⟨hlen_as, hlen_xs, hxnd, hnc, hsh, hxout, -⟩ := siteOK_inv hok
          obtain ⟨body₀, cenv₀, hlk₀X, hb₀X⟩ := hΔ (f, d) (lookupDelta_mem hld)
          have hlk₀ : lookupFun funs₁ f =
              some (⟨d.ps, d.rs, body₀⟩, cenv₀) := hlk₀X
          have hb₀ : body₀ = d.ss ∨ body₀ = d.ss ++ [.leave] := hb₀X
          have hZvars : ∀ y ∈ varsList as,
              y ∉ (([] : VEnv D)).map Prod.fst := by
            intro y hy
            simp
          rcases inlineCore_bwd (Z := []) hsc hlen_as hnc hsh hxout hlen_xs
              hs hZvars funs₁ cenv₀
            with ⟨argvals, st1', Vend, hargs, hbody, hV1, -⟩
              | ⟨argvals, st1', Vend, hargs, hbody, hV1, ho⟩
              | ⟨hargs, hV1, ho⟩
          · obtain ⟨oc, hbody', hoc⟩ := body_denormalize_ok hb₀ hbody
            have hcall : Step D funs₁ V st (.expr (.call f as))
                (.eres (.vals (d.rs.map (fun r => (VEnv.get Vend r).getD
                  (evmWithExternal calls creates).zero)) st1)) := by
              refine Step.callOk hargs hlk₀ ?_ hbody' hoc
              show argvals.length = d.ps.length
              have := args_length hargs
              omega
            have hassign : Step D funs₁ V st
                (.stmt (.assign xs (.call f as)))
                (.sres (VEnv.setMany V xs (d.rs.map (fun r => (VEnv.get Vend r).getD
                  (evmWithExternal calls creates).zero))) st1 .normal) :=
              Step.assignVal hcall (by simp only [List.length_map]; omega)
            have hV1' : V1 = VEnv.setMany V xs (d.rs.map
                (fun r => (VEnv.get Vend r).getD
                  (evmWithExternal calls creates).zero)) := hV1
            obtain ⟨res₂', hs₂, hres₂⟩ := ihrest hR hΔ hrestrel
            rw [hV1'] at hs₂
            cases hres₂ with
            | refl => exact ⟨_, Step.seqCons hassign hs₂, .refl _⟩
            | haltIns Zp => exact ⟨_, Step.seqCons hassign hs₂, .haltIns _ _ _⟩
          · exact absurd ho (by simp)
          · exact absurd ho (by simp)
      | @siteExpr _ f d as rest _ hld hnd hsc hok hrestrel =>
          obtain ⟨hlen_as, hlen_xs, -, hnc, hsh, -, -⟩ := siteOK_inv hok
          obtain ⟨body₀, cenv₀, hlk₀X, hb₀X⟩ := hΔ (f, d) (lookupDelta_mem hld)
          have hlk₀ : lookupFun funs₁ f =
              some (⟨d.ps, d.rs, body₀⟩, cenv₀) := hlk₀X
          have hb₀ : body₀ = d.ss ∨ body₀ = d.ss ++ [.leave] := hb₀X
          have hrs0 : d.rs = [] := by
            cases hrs : d.rs with
            | nil => rfl
            | cons r rs' => rw [hrs] at hlen_xs; simp at hlen_xs
          have hZvars : ∀ y ∈ varsList as,
              y ∉ (([] : VEnv D)).map Prod.fst := by
            intro y hy
            simp
          rcases inlineCore_bwd (Z := []) (xs := []) hsc hlen_as hnc hsh
              (fun x hx => by cases hx) hlen_xs hs hZvars funs₁ cenv₀
            with ⟨argvals, st1', Vend, hargs, hbody, hV1, -⟩
              | ⟨argvals, st1', Vend, hargs, hbody, hV1, ho⟩
              | ⟨hargs, hV1, ho⟩
          · obtain ⟨oc, hbody', hoc⟩ := body_denormalize_ok hb₀ hbody
            have hcall : Step D funs₁ V st (.expr (.call f as))
                (.eres (.vals [] st1)) := by
              have hc := Step.callOk hargs hlk₀ (by
                show argvals.length = d.ps.length
                have := args_length hargs
                omega) hbody' hoc
              rw [show (⟨d.ps, d.rs, body₀⟩ : FDecl D).rets = d.rs from rfl,
                hrs0] at hc
              exact hc
            have hstmt : Step D funs₁ V st
                (.stmt (.exprStmt (.call f as)))
                (.sres V st1 .normal) := Step.exprStmt hcall
            have hV1' : V1 = V := by
              rw [hV1]
              rfl
            obtain ⟨res₂', hs₂, hres₂⟩ := ihrest hR hΔ hrestrel
            rw [hV1'] at hs₂
            cases hres₂ with
            | refl => exact ⟨_, Step.seqCons hstmt hs₂, .refl _⟩
            | haltIns Zp => exact ⟨_, Step.seqCons hstmt hs₂, .haltIns _ _ _⟩
          · exact absurd ho (by simp)
          · exact absurd ho (by simp)
  | @seqStop funs V st s₂ rest₂ V1 st1 o hs hne ihs =>
      intro funs₁ Δ pc hR hΔ hrel
      cases hrel with
      | consSS hsrel hrestrel =>
          obtain ⟨res₁, hs₁, heq₁⟩ := ihs hR hΔ hsrel
          have heq₁X : _ = res₁ := heq₁
          rw [← heq₁X] at hs₁
          exact ⟨_, Step.seqStop hs₁ hne, .refl _⟩
      | @siteLet _ f d xs as rest _ hld hnd hsc hok hrestrel =>
          -- the zero-init never stops early
          cases hs with
          | letZero => exact absurd rfl hne
      | @siteAssign _ f d xs as rest _ hld hnd hsc hok hrestrel =>
          obtain ⟨hlen_as, hlen_xs, hxnd, hnc, hsh, hxout, -⟩ := siteOK_inv hok
          obtain ⟨body₀, cenv₀, hlk₀X, hb₀X⟩ := hΔ (f, d) (lookupDelta_mem hld)
          have hlk₀ : lookupFun funs₁ f =
              some (⟨d.ps, d.rs, body₀⟩, cenv₀) := hlk₀X
          have hb₀ : body₀ = d.ss ∨ body₀ = d.ss ++ [.leave] := hb₀X
          have hZvars : ∀ y ∈ varsList as,
              y ∉ (([] : VEnv D)).map Prod.fst := by
            intro y hy
            simp
          rcases inlineCore_bwd (Z := []) hsc hlen_as hnc hsh hxout hlen_xs
              hs hZvars funs₁ cenv₀
            with ⟨argvals, st1', Vend, hargs, hbody, hV1, ho⟩
              | ⟨argvals, st1', Vend, hargs, hbody, hV1, ho⟩
              | ⟨hargs, hV1, ho⟩
          · exact absurd ho hne
          · have hbody' := body_denormalize_halt hb₀ hbody
            have hcall : Step D funs₁ V st (.expr (.call f as))
                (.eres (.halt st1)) := by
              refine Step.callHalt hargs hlk₀ ?_ hbody'
              show argvals.length = d.ps.length
              have := args_length hargs
              omega
            subst hV1 ho
            exact ⟨_, Step.seqStop (Step.assignHalt hcall) (by simp), .refl _⟩
          · have hcall : Step D funs₁ V st (.expr (.call f as))
                (.eres (.halt st1)) := Step.callArgsHalt hargs
            subst hV1 ho
            exact ⟨_, Step.seqStop (Step.assignHalt hcall) (by simp), .refl _⟩
      | @siteExpr _ f d as rest _ hld hnd hsc hok hrestrel =>
          obtain ⟨hlen_as, hlen_xs, -, hnc, hsh, -, -⟩ := siteOK_inv hok
          obtain ⟨body₀, cenv₀, hlk₀X, hb₀X⟩ := hΔ (f, d) (lookupDelta_mem hld)
          have hlk₀ : lookupFun funs₁ f =
              some (⟨d.ps, d.rs, body₀⟩, cenv₀) := hlk₀X
          have hb₀ : body₀ = d.ss ∨ body₀ = d.ss ++ [.leave] := hb₀X
          have hZvars : ∀ y ∈ varsList as,
              y ∉ (([] : VEnv D)).map Prod.fst := by
            intro y hy
            simp
          rcases inlineCore_bwd (Z := []) (xs := []) hsc hlen_as hnc hsh
              (fun x hx => by cases hx) hlen_xs hs hZvars funs₁ cenv₀
            with ⟨argvals, st1', Vend, hargs, hbody, hV1, ho⟩
              | ⟨argvals, st1', Vend, hargs, hbody, hV1, ho⟩
              | ⟨hargs, hV1, ho⟩
          · exact absurd ho hne
          · have hbody' := body_denormalize_halt hb₀ hbody
            have hcall : Step D funs₁ V st (.expr (.call f as))
                (.eres (.halt st1)) := by
              refine Step.callHalt hargs hlk₀ ?_ hbody'
              show argvals.length = d.ps.length
              have := args_length hargs
              omega
            subst hV1 ho
            exact ⟨_, Step.seqStop (Step.exprStmtHalt hcall) (by simp), .refl _⟩
          · have hcall : Step D funs₁ V st (.expr (.call f as))
                (.eres (.halt st1)) := Step.callArgsHalt hargs
            subst hV1 ho
            exact ⟨_, Step.seqStop (Step.exprStmtHalt hcall) (by simp), .refl _⟩
  | @loopDone funs V st c post' body' cv st1 hc hcz ihc =>
      intro funs₁ Δ pc hR hΔ hrel
      cases hrel with
      | loopL hpost hbody =>
          obtain ⟨res₁, hs₁, heq₁⟩ := ihc hR hΔ IcRel.expr
          have heq₁X : _ = res₁ := heq₁
          rw [← heq₁X] at hs₁
          exact ⟨_, Step.loopDone hs₁ hcz, rfl⟩
  | @loopCondHalt funs V st c post' body' st1 hc ihc =>
      intro funs₁ Δ pc hR hΔ hrel
      cases hrel with
      | loopL hpost hbody =>
          obtain ⟨res₁, hs₁, heq₁⟩ := ihc hR hΔ IcRel.expr
          have heq₁X : _ = res₁ := heq₁
          rw [← heq₁X] at hs₁
          exact ⟨_, Step.loopCondHalt hs₁, rfl⟩
  | @loopStep funs V st c post' body' cv st1 Vb stb ob Vp stp Vend stend o hc hcv hbody hob hpost hnext ihc ihbody ihpost ihnext =>
      intro funs₁ Δ pc hR hΔ hrel
      cases hrel with
      | @loopL _ _ post _ body _ hpostrel hbodyrel =>
          obtain ⟨res₁, hs₁, heq₁⟩ := ihc hR hΔ IcRel.expr
          have heq₁X : _ = res₁ := heq₁
          rw [← heq₁X] at hs₁
          obtain ⟨res₂', hs₂, heq₂⟩ := ihbody hR hΔ (IcRel.blockS hbodyrel)
          have heq₂X : _ = res₂' := heq₂
          rw [← heq₂X] at hs₂
          obtain ⟨res₃, hs₃, heq₃⟩ := ihpost hR hΔ (IcRel.blockS hpostrel)
          have heq₃X : _ = res₃ := heq₃
          rw [← heq₃X] at hs₃
          obtain ⟨res₄, hs₄, heq₄⟩ := ihnext hR hΔ (IcRel.loopL hpostrel hbodyrel)
          have heq₄X : _ = res₄ := heq₄
          rw [← heq₄X] at hs₄
          exact ⟨_, Step.loopStep hs₁ hcv hs₂ hob hs₃ hs₄, rfl⟩
  | @loopPostHalt funs V st c post' body' cv st1 Vb stb ob Vp stp hc hcv hbody hob hpost ihc ihbody ihpost =>
      intro funs₁ Δ pc hR hΔ hrel
      cases hrel with
      | loopL hpostrel hbodyrel =>
          obtain ⟨res₁, hs₁, heq₁⟩ := ihc hR hΔ IcRel.expr
          have heq₁X : _ = res₁ := heq₁
          rw [← heq₁X] at hs₁
          obtain ⟨res₂', hs₂, heq₂⟩ := ihbody hR hΔ (IcRel.blockS hbodyrel)
          have heq₂X : _ = res₂' := heq₂
          rw [← heq₂X] at hs₂
          obtain ⟨res₃, hs₃, heq₃⟩ := ihpost hR hΔ (IcRel.blockS hpostrel)
          have heq₃X : _ = res₃ := heq₃
          rw [← heq₃X] at hs₃
          exact ⟨_, Step.loopPostHalt hs₁ hcv hs₂ hob hs₃, rfl⟩
  | @loopBreak funs V st c post' body' cv st1 Vb stb hc hcv hbody ihc ihbody =>
      intro funs₁ Δ pc hR hΔ hrel
      cases hrel with
      | loopL hpostrel hbodyrel =>
          obtain ⟨res₁, hs₁, heq₁⟩ := ihc hR hΔ IcRel.expr
          have heq₁X : _ = res₁ := heq₁
          rw [← heq₁X] at hs₁
          obtain ⟨res₂', hs₂, heq₂⟩ := ihbody hR hΔ (IcRel.blockS hbodyrel)
          have heq₂X : _ = res₂' := heq₂
          rw [← heq₂X] at hs₂
          exact ⟨_, Step.loopBreak hs₁ hcv hs₂, rfl⟩
  | @loopLeave funs V st c post' body' cv st1 Vb stb hc hcv hbody ihc ihbody =>
      intro funs₁ Δ pc hR hΔ hrel
      cases hrel with
      | loopL hpostrel hbodyrel =>
          obtain ⟨res₁, hs₁, heq₁⟩ := ihc hR hΔ IcRel.expr
          have heq₁X : _ = res₁ := heq₁
          rw [← heq₁X] at hs₁
          obtain ⟨res₂', hs₂, heq₂⟩ := ihbody hR hΔ (IcRel.blockS hbodyrel)
          have heq₂X : _ = res₂' := heq₂
          rw [← heq₂X] at hs₂
          exact ⟨_, Step.loopLeave hs₁ hcv hs₂, rfl⟩
  | @loopBodyHalt funs V st c post' body' cv st1 Vb stb hc hcv hbody ihc ihbody =>
      intro funs₁ Δ pc hR hΔ hrel
      cases hrel with
      | loopL hpostrel hbodyrel =>
          obtain ⟨res₁, hs₁, heq₁⟩ := ihc hR hΔ IcRel.expr
          have heq₁X : _ = res₁ := heq₁
          rw [← heq₁X] at hs₁
          obtain ⟨res₂', hs₂, heq₂⟩ := ihbody hR hΔ (IcRel.blockS hbodyrel)
          have heq₂X : _ = res₂' := heq₂
          rw [← heq₂X] at hs₂
          exact ⟨_, Step.loopBodyHalt hs₁ hcv hs₂, rfl⟩

/-! ### Soundness -/

/-- Function environments are self-related. -/
theorem IcFunsRel.refl : ∀ funs : FunEnv D,
    IcFunsRel (calls := calls) (creates := creates) funs funs
  | [] => .nil
  | s :: rest => .cons (icScopeRel_refl _ s) (IcFunsRel.refl rest)

/-- The empty declaration context is trivially well-formed. -/
theorem DeltaWF.nil : DeltaWF ([] : DEnv) :=
  fun p hp => absurd hp (List.not_mem_nil)

/-- Related blocks are pointwise equivalent. -/
theorem IcRel.equivBlock {b b' : Block Op}
    (h : IcRel (deltaExtend [] b) (.stmts b) (.stmts b')) :
    EquivBlock D b b' := by
  intro funs V st V' st' o
  constructor
  · intro hstep
    obtain ⟨res₂, hs₂, hres⟩ := ic_fwd hstep (IcFunsRel.refl funs)
      (DeltaCompat.nil funs) (IcRel.blockS h)
    rw [show res₂ = _ from hres] at hs₂
    exact hs₂
  · intro hstep
    obtain ⟨res₁, hs₁, hres⟩ := ic_bwd hstep (IcFunsRel.refl funs)
      (DeltaCompat.nil funs) (IcRel.blockS h)
    have hresX : _ = res₁ := hres
    rw [← hresX] at hs₁
    exact hs₁

/-- The **InlineCalls pass**: statement-level inlining of call-free helpers,
bundled with its soundness proof — in the unchanged pointwise spec. -/
def inlineCalls : Pass D where
  run := inlineCallsBlock
  sound := fun b => IcRel.equivBlock
    (by
      rw [show inlineCallsBlock b = icStmts (deltaExtend [] b) b by
        rw [inlineCallsBlock, icBlock]]
      exact icStmts_rel (deltaExtend [] b) (DeltaWF.nil.extend b) b)

@[simp] theorem inlineCalls_run (b : Block Op) :
    (inlineCalls (calls := calls) (creates := creates)).run b =
      inlineCallsBlock b := rfl

end YulEvmCompiler.Optimizer
