import YulEvmCompiler.SsaCfg.Implementation.OfYulSound.FuncTable
import YulEvmCompiler.Optimizer.Core.Equiv
set_option warningAsError true

/-!
# YulEvmCompiler.SsaCfg.Implementation.OfYulSound.ModStmts

The statement motive's outputs and the `modStmts` over-approximation.

`SOut`, `CtxVars`, `LocalsOK`, `ModOut` and the `mod_sim` induction showing
that a source derivation only touches the variables `modStmts` predicts —
the fact the loop and switch reconstructions need.
-/

namespace YulEvmCompiler.SsaCfg
open YulSemantics (Ident Literal Expr Stmt VEnv Outcome Forall₂)
open YulSemantics.EVM (U256 EvmState Op builtinWithExternal evmWithExternal)

section Semantics
variable [model : ExternalModel]
local notation "yulD" => evmWithExternal model.calls model.creates YulSemantics.EVM.ExternalGas.any

/-! ## The simulation motive

Everything above is unconditional. The derivation induction itself is a single
`induction … with` over the source `Step` derivation whose motive is `SOut`
below, mirroring `SimAsm.sim`'s `Motive`. -/

/-- What a statement-class source derivation means on the SSA side, by outcome
— the SSA analogue of `SimAsm.SOut`. `normal` hands back the register file the
fragment ends with (an extension of the one it started with, by single
assignment) together with the environment correspondence; the non-local
outcomes hand back the values their edge carries and consume any continuation
of the target block. -/
def SOut (P : Prog) (f : Func) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) (s₀ s₁ : BState) (R₀ : Regs)
    (renv : Option VMap) (V' : VEnv yulD) (yst yst' : EvmState) (o : Outcome) :
    Prop :=
  match o with
  | .normal => ∃ (env' : VMap) (R₁ : Regs),
      renv = some env' ∧ Regs.Le R₀ R₁
        ∧ Regs.BelowEq s₀.fn.nextVal R₀ R₁ ∧ RegsFresh R₁ s₁.fn
        ∧ EnvOK (model := model) env' V' R₁
        ∧ env'.Unique
        ∧ SimS (model := model) P f s₀.fn R₀ yst s₁.fn R₁ yst'
  | .halt => ExecFrom (model := model) P f s₀.fn R₀ yst (.halt yst')
  | .break => ∃ (lc : LoopCtx) (R₁ : Regs) (vals : List U256),
      lctx = some lc ∧ Regs.Le R₀ R₁
        ∧ Regs.BelowEq s₀.fn.nextVal R₀ R₁ ∧ RegsFresh R₁ s₁.fn
        ∧ Forall₂ (fun x v => YulSemantics.VEnv.get V' x = some v) lc.vars vals
        ∧ ∀ res, JumpTo (model := model) P f lc.brkTgt vals R₁ yst' res
            → ExecFrom (model := model) P f s₀.fn R₀ yst res
  | .continue => ∃ (lc : LoopCtx) (R₁ : Regs) (vals : List U256),
      lctx = some lc ∧ Regs.Le R₀ R₁
        ∧ Regs.BelowEq s₀.fn.nextVal R₀ R₁ ∧ RegsFresh R₁ s₁.fn
        ∧ Forall₂ (fun x v => YulSemantics.VEnv.get V' x = some v) lc.vars vals
        ∧ ∀ res, JumpTo (model := model) P f lc.contTgt vals R₁ yst' res
            → ExecFrom (model := model) P f s₀.fn R₀ yst res
  | .leave => ∃ (rs : List Ident) (vals : List U256),
      rets = some rs
        ∧ Forall₂ (fun x v => YulSemantics.VEnv.get V' x = some v) rs vals
        ∧ ExecFrom (model := model) P f s₀.fn R₀ yst (.ret vals yst')

/-- **The loop/return context is visible.**  The variables a `break`/`continue`
edge carries and the names a `leave` reads are bound in the environment the
fragment runs in.  The construction establishes this exactly where it creates a
context — `forLoop` picks `X = modifiedX envH ...` (a sublist of the visible
names) and `trFunc` starts from `env0 = ps.zip pids ++ rs.zip rids` — and every
inner fragment inherits it, because a scope only ever *extends* the visible name
spine.  It is what lets `SOut.scope` carry a non-local exit's edge values out
through the source's `restore`: those names are outer names, so the scope's own
declarations (which `NoShadow` keeps disjoint from them) never hide them. -/
def CtxVars (lctx : Option LoopCtx) (rets : Option (List Ident)) (env : VMap) :
    Prop :=
  (∀ lc : LoopCtx, lctx = some lc → ∀ x ∈ lc.vars, x ∈ env.map Prod.fst)
    ∧ (∀ rs : List Ident, rets = some rs → ∀ x ∈ rs, x ∈ env.map Prod.fst)

namespace CtxVars

omit model in
theorem mono {lctx : Option LoopCtx} {rets : Option (List Ident)}
    {env env' : VMap} (h : CtxVars lctx rets env)
    (hsub : ∀ x ∈ env.map Prod.fst, x ∈ env'.map Prod.fst) :
    CtxVars lctx rets env' :=
  ⟨fun lc hlc x hx => hsub _ (h.1 lc hlc x hx),
    fun rs hrs x hx => hsub _ (h.2 rs hrs x hx)⟩

omit model in
theorem of_names_eq {lctx : Option LoopCtx} {rets : Option (List Ident)}
    {env env' : VMap} (h : CtxVars lctx rets env)
    (hn : env'.map Prod.fst = env.map Prod.fst) : CtxVars lctx rets env' :=
  h.mono (fun x hx => by rw [hn]; exact hx)

omit model in
theorem setMany {lctx : Option LoopCtx} {rets : Option (List Ident)}
    {env : VMap} (h : CtxVars lctx rets env) (xs : List Ident)
    (is : List ValId) : CtxVars lctx rets (env.setMany xs is) :=
  h.of_names_eq (VMap.names_setMany env xs is)

end CtxVars

/-! ## The `modStmts` over-approximation

A statement list only changes the *outer* bindings its `modStmts` analysis
names. This is exactly what licenses `trStmt`'s `cond`, `switch` and `forLoop`
cases to thread only `modifiedX env bodies` through their join / header / exit
block parameters and to keep the *old* `ValId` for every other variable: SSA
registers persist across blocks, so an unreported variable's existing id still
holds its value. Missing names would be unsound; extra ones are harmless,
because then both incoming edges pass the same value. -/

omit model in
theorem modifiedX_mem_names {env : VMap} {bodies : List (List (Stmt Op))}
    {x : Ident} (h : x ∈ modifiedX env bodies) : x ∈ env.map Prod.fst := by
  simp only [modifiedX] at h
  exact List.mem_eraseDups.mp (List.mem_filter.mp h).1

omit model in
theorem modifiedX_nodup {env : VMap} (h : env.Unique)
    (bodies : List (List (Stmt Op))) : (modifiedX env bodies).Nodup := by
  rw [modifiedX, VMap.eraseDups_names_eq_self h]
  exact h.filter _

omit model in
theorem mem_modifiedX {env : VMap}
    {bodies : List (List (Stmt Op))} {x : Ident}
    (henv : x ∈ env.map Prod.fst) (hmod : x ∈ bodies.flatMap (modStmts [])) :
    x ∈ modifiedX env bodies := by
  simp only [modifiedX, List.mem_filter]
  exact ⟨List.mem_eraseDups.mpr henv, by simpa using hmod⟩

/-- Every name the enclosing statement list has declared so far is bound within
the innermost `locals.length` entries — the invariant `modStmts` threads through
its `letDecl` case, and the reason its `filter` may drop a name without lying:
a `set` to such a name reaches the inner binding, which the enclosing `restore`
drops. Stated as a *set* condition, because a list's declarations reach the
environment in reverse group order. -/
def LocalsOK (locals : List Ident) (V : VEnv yulD) : Prop :=
  ∀ x ∈ locals, x ∈ VEnv.names (V.take locals.length)

@[simp] theorem localsOK_nil (V : VEnv yulD) : LocalsOK [] V := by
  intro x hx; simp at hx

theorem names_take (V : VEnv yulD) (k : Nat) :
    VEnv.names (V.take k) = (VEnv.names V).take k := by
  simp [VEnv.names, List.map_take]

omit model in
theorem drop_append_len {α : Type} (A B : List α) (i : Nat) :
    (A ++ B).drop (A.length + i) = B.drop i := by
  induction A with
  | nil => simp
  | cons a A ih =>
    rw [List.length_cons, List.cons_append,
      show A.length + 1 + i = (A.length + i) + 1 from by omega,
      List.drop_succ_cons]
    exact ih

omit model in
theorem take_append_len {α : Type} (A B : List α) (i : Nat) :
    (A ++ B).take (A.length + i) = A ++ B.take i := by
  induction A with
  | nil => simp
  | cons a A ih =>
    rw [List.length_cons, List.cons_append,
      show A.length + 1 + i = (A.length + i) + 1 from by omega,
      List.take_succ_cons, ih, List.cons_append]

omit model in
theorem mem_take_mono {α : Type} {l : List α} {m k : Nat} (h : m ≤ k) {x : α}
    (hx : x ∈ l.take m) : x ∈ l.take k := by
  have he : l.take m = (l.take k).take m := by
    rw [List.take_take, Nat.min_eq_left h]
  rw [he] at hx
  exact List.mem_of_mem_take hx

/-- What a statement-class execution does to the environment: nothing shrinks,
and at every *outer* depth `n` — outside the `locals` the enclosing list has
declared — the surviving bindings keep their names and either keep their values
or are named by the analysis.

Quantifying over the outer depth is what makes the relation compose through
`seqCons` without any prefix bookkeeping: the tail's guarantee, stated at every
depth, specializes to the depth the head's `let`-bindings left. -/
def ModOut (locals mods : List Ident) (V W : VEnv yulD) : Prop :=
  V.length ≤ W.length
  ∧ ∀ n : Nat, n + locals.length ≤ V.length →
      Forall₂
        (fun (p q : Ident × U256) => p.1 = q.1 ∧ (q.2 = p.2 ∨ q.1 ∈ mods))
        (V.drop (V.length - n)) (W.drop (W.length - n))

/-- The `assign` engine: folding `set` over a list of names changes a position
past `k` only when that name is reported by the analysis — the names that are
*not* reported are exactly the ones bound inside the first `k` entries, which
`set` reaches first. -/
theorem setMany_drop_forall₂ : ∀ {xs : List Ident} {vs : List U256}
    {V : VEnv yulD} {k : Nat} {mods : List Ident},
    (∀ x ∈ xs, x ∈ mods ∨ x ∈ VEnv.names (V.take k)) →
    Forall₂ (fun (p q : Ident × U256) => p.1 = q.1 ∧ (q.2 = p.2 ∨ q.1 ∈ mods))
      (V.drop k) ((YulSemantics.VEnv.setMany V xs vs).drop k) := by
  intro xs
  induction xs with
  | nil => intro vs V k mods _; exact YulSemantics.Forall₂.refl (fun _ => ⟨rfl, Or.inl rfl⟩) _
  | cons x xs ih =>
    intro vs V k mods hall
    cases vs with
    | nil => exact YulSemantics.Forall₂.refl (fun _ => ⟨rfl, Or.inl rfl⟩) _
    | cons v vs =>
      rw [VEnv.setMany_cons]
      have hnames : VEnv.names ((YulSemantics.VEnv.set V x v).take k)
          = VEnv.names (V.take k) := by
        have hns := VEnv.names_set V x v
        rw [VEnv.names, VEnv.names] at hns ⊢
        rw [List.map_take, List.map_take, hns]
      have htail := ih (vs := vs) (V := YulSemantics.VEnv.set V x v) (k := k)
        (mods := mods) (by
          intro y hy
          rcases hall y (List.mem_cons_of_mem _ hy) with hm | hm
          · exact Or.inl hm
          · exact Or.inr (by rw [hnames]; exact hm))
      have hstep : Forall₂
          (fun (p q : Ident × U256) => p.1 = q.1 ∧ (q.2 = p.2 ∨ q.1 ∈ mods))
          (V.drop k) ((YulSemantics.VEnv.set V x v).drop k) := by
        rcases hall x (List.mem_cons_self ..) with hm | hm
        · refine YulSemantics.Forall₂.imp (fun a b hab => ⟨hab.1, hab.2.imp id (fun he => ?_)⟩)
            (YulSemantics.Forall₂.drop k (VEnv.set_positional V x v))
          rw [← hab.1, he]; exact hm
        · rw [VEnv.set_drop_of_mem_take V x v k hm]
          exact YulSemantics.Forall₂.refl (fun _ => ⟨rfl, Or.inl rfl⟩) _
      refine YulSemantics.Forall₂.trans' ?_ hstep htail
      intro a b c hab hbc
      exact ⟨hab.1.trans hbc.1, by
        rcases hbc.2 with h | h
        · rcases hab.2 with h' | h'
          · exact Or.inl (h.trans h')
          · exact Or.inr (by rw [← hbc.1]; exact h')
        · exact Or.inr h⟩

namespace ModOut

theorem rfl' (locals mods : List Ident) (V : VEnv yulD) : ModOut locals mods V V :=
  ⟨Nat.le_refl _, fun _ _ => YulSemantics.Forall₂.refl (fun _ => ⟨rfl, Or.inl rfl⟩) _⟩

theorem mono_mods {locals mods mods' : List Ident} {V W : VEnv yulD}
    (hsub : ∀ x ∈ mods, x ∈ mods') (h : ModOut locals mods V W) :
    ModOut locals mods' V W :=
  ⟨h.1, fun n hn => YulSemantics.Forall₂.imp (fun _ _ hpq =>
    ⟨hpq.1, hpq.2.imp id (fun hm => hsub _ hm)⟩) (h.2 n hn)⟩

/-- Composition. The side condition says the second fragment's guarantee reaches
every depth the first one does — immediate when the head neither declares nor
the tail's `locals` grows, and provided by the `letDecl` length shape otherwise. -/
theorem trans {l₁ l₂ m₁ m₂ : List Ident} {V V₁ V₂ : VEnv yulD}
    (h₁ : ModOut l₁ m₁ V V₁) (h₂ : ModOut l₂ m₂ V₁ V₂)
    (hd : ∀ n : Nat, n + l₁.length ≤ V.length → n + l₂.length ≤ V₁.length) :
    ModOut l₁ (m₁ ++ m₂) V V₂ := by
  refine ⟨Nat.le_trans h₁.1 h₂.1, fun n hn => ?_⟩
  refine YulSemantics.Forall₂.trans' ?_ (h₁.2 n hn) (h₂.2 n (hd n hn))
  intro a b c hab hbc
  refine ⟨hab.1.trans hbc.1, ?_⟩
  rcases hbc.2 with h | h
  · rcases hab.2 with h' | h'
    · exact Or.inl (h.trans h')
    · exact Or.inr (List.mem_append.mpr (Or.inl (by rw [← hbc.1]; exact h')))
  · exact Or.inr (List.mem_append.mpr (Or.inr h))

/-- A scope exit on the right: `restore V W` and `W` agree at every outer
depth. -/
theorem restore_right {locals mods : List Ident} {V W : VEnv yulD}
    (h : ModOut locals mods V W) :
    ModOut locals mods V (YulSemantics.restore V W) := by
  refine ⟨by rw [VEnv.length_restore h.1], fun n hn => ?_⟩
  have h2 := h.2 n hn
  rw [VEnv.length_restore h.1, VEnv.restore_def, List.drop_drop]
  have he : W.length - V.length + (V.length - n) = W.length - n := by
    have := h.1; omega
  rw [he]
  exact h2

end ModOut

/-- Reading back through a `ModOut`: a name the analysis does not report reads
the same in both environments. -/
theorem get_congr_of_forall₂ {mods : List Ident} {x : Ident} (hx : x ∉ mods) :
    ∀ {V W : VEnv yulD},
      Forall₂
        (fun (p q : Ident × U256) => p.1 = q.1 ∧ (q.2 = p.2 ∨ q.1 ∈ mods)) V W →
      YulSemantics.VEnv.get W x = YulSemantics.VEnv.get V x := by
  intro V W h
  induction h with
  | nil => rfl
  | @cons p q V' W' hpq _ ih =>
    rw [VEnv.get_cons, VEnv.get_cons, ← hpq.1]
    by_cases hc : p.1 = x
    · rw [if_pos hc, if_pos hc]
      rcases hpq.2 with heq | hmem
      · rw [heq]
      · exact absurd (by rw [← hc, hpq.1]; exact hmem) hx
    · rw [if_neg hc, if_neg hc]; exact ih

/-- The names a statement declares in the environment it leaves behind. -/
def declsOfStmt : Stmt Op → List Ident
  | .letDecl vars _ => vars
  | _ => []

omit model in
/-- The declarations of a statement list, split at the head. -/
theorem declsOf_cons (s : Stmt Op) (rest : List (Stmt Op)) :
    declsOf (s :: rest) = declsOfStmt s ++ declsOf rest := by
  cases s <;> rfl

/-- The local scope the analysis threads past a statement. -/
def localsAfter (locals : List Ident) : Stmt Op → List Ident
  | .letDecl vars _ => vars ++ locals
  | _ => locals

omit model in
theorem localsAfter_eq (locals : List Ident) (s : Stmt Op) :
    localsAfter locals s = declsOfStmt s ++ locals := by
  cases s <;> rfl

omit model in
theorem modStmts_cons (locals : List Ident) (s : Stmt Op)
    (rest : List (Stmt Op)) :
    modStmts locals (s :: rest)
      = modStmt locals s ++ modStmts (localsAfter locals s) rest := by
  cases s <;> rfl

theorem LocalsOK.ofNames {locals : List Ident} {V W : VEnv yulD}
    (h : VEnv.names W = VEnv.names V) (hl : LocalsOK locals V) : LocalsOK locals W := by
  intro x hx
  rw [names_take, h, ← names_take]
  exact hl x hx

omit model in
/-- Every case body is scanned by `modCases`. -/
theorem mem_modCases {locals : List Ident} :
    ∀ {cases : List (Literal × List (Stmt Op))} {p : Literal × List (Stmt Op)},
      p ∈ cases → ∀ x ∈ modStmts locals p.2, x ∈ modCases locals cases := by
  intro cases
  induction cases with
  | nil => intro p hp; exact absurd hp (by simp)
  | cons q cs ih =>
    intro p hp x hx
    obtain ⟨ql, qb⟩ := q
    rw [modCases]
    rcases List.mem_cons.mp hp with rfl | hm
    · exact List.mem_append_left _ hx
    · exact List.mem_append_right _ (ih hm x hx)

/-- `selectSwitch` picks a scanned case body, or the default. -/
theorem selectSwitch_cases (cv : U256)
    (cases : List (Literal × List (Stmt Op)))
    (dflt : Option (List (Stmt Op))) :
    (∃ p ∈ cases, YulSemantics.selectSwitch yulD cv cases dflt = p.2)
      ∨ YulSemantics.selectSwitch yulD cv cases dflt = dflt.getD [] := by
  unfold YulSemantics.selectSwitch
  cases hf : cases.find? (fun p => decide (cv = YulSemantics.EVM.litValue p.1)) with
  | none => exact Or.inr rfl
  | some p => exact Or.inl ⟨p, List.mem_of_find?_eq_some hf, rfl⟩

/-- The block a `switch` selects is one the analysis scanned. -/
theorem mem_modStmt_switch {locals : List Ident} {cv : U256}
    {cases : List (Literal × List (Stmt Op))} {dflt : Option (List (Stmt Op))}
    {x : Ident}
    (hx : x ∈ modStmts locals (YulSemantics.selectSwitch yulD cv cases dflt)) :
    x ∈ modStmt locals (.switch (.lit (.number 0)) cases dflt) := by
  cases dflt with
  | none =>
    rcases selectSwitch_cases cv cases none with ⟨p, hp, he⟩ | he
    · rw [he] at hx
      exact List.mem_append_left _ (mem_modCases hp x hx)
    · rw [he] at hx
      exact absurd hx (by simp [modStmts])
  | some b =>
    rcases selectSwitch_cases cv cases (some b) with ⟨p, hp, he⟩ | he
    · rw [he] at hx
      exact List.mem_append_left _ (mem_modCases hp x hx)
    · rw [he] at hx
      exact List.mem_append_right _ hx

/-- The induction motive: what a source derivation says about the environment,
by syntactic class. Expression classes say nothing — they do not touch `V`. -/
def ModMotive (V : VEnv yulD) :
    YulSemantics.Code Op → YulSemantics.Res yulD → Prop
  | .stmt s, .sres V' _ o =>
      VEnv.names V'
          = (if o = .normal then declsOfStmt s else []) ++ VEnv.names V
      ∧ ∀ locals, LocalsOK locals V →
          ModOut locals (modStmt locals s) V V'
  | .stmts ss, .sres V' _ o =>
      (∃ W : List Ident, VEnv.names V' = W ++ VEnv.names V
        ∧ (o = .normal → W.length = (declsOf ss).length
            ∧ ∀ x ∈ declsOf ss, x ∈ W))
      ∧ ∀ locals, LocalsOK locals V →
          ModOut locals (modStmts locals ss) V V'
  | .loop _c post body, .sres V' _ _ =>
      (∃ W : List Ident, VEnv.names V' = W ++ VEnv.names V)
      ∧ ∀ locals, LocalsOK locals V →
          ModOut locals (modStmts locals post ++ modStmts locals body) V V'
  | _, _ => True

/-- `ModOut` with a `restore` on the right. -/
theorem ModOut.restoreR {locals mods : List Ident} {V W : VEnv yulD}
    (h : ModOut locals mods V W) :
    ModOut locals mods V (YulSemantics.restore V W) := h.restore_right

/-- Names survive a scope exit. -/
theorem names_restore {V W : VEnv yulD} {Wn : List Ident}
    (hlen : V.length ≤ W.length) (hsh : VEnv.names W = Wn ++ VEnv.names V) :
    VEnv.names (YulSemantics.restore V W) = VEnv.names V := by
  have hWn : Wn.length = W.length - V.length := by
    have := congrArg List.length hsh
    simp [VEnv.length_names] at this
    omega
  rw [VEnv.names, VEnv.restore_def, List.map_drop]
  rw [show List.map Prod.fst W = VEnv.names W from rfl, hsh, ← hWn]
  simp

/--
**The `modStmts` over-approximation is sound** — the analysis obligation, in the
form the induction carries.

The proof is one `induction … with` over the source `Step` derivation with
`ModMotive` above. `ModOut`'s `∀ n` (outer-depth) quantification is what makes
`seqCons` compose without prefix bookkeeping, and `setMany_drop_forall₂` is the
engine of the `assign` case — the one place `LocalsOK` is consumed.
-/
theorem mod_sim {funs : YulSemantics.FunEnv yulD} {V : VEnv yulD}
    {yst : EvmState} {res : YulSemantics.Res yulD}
    {c : YulSemantics.Code Op}
    (h : YulSemantics.Step yulD funs V yst c res) : ModMotive V c res := by
  induction h with
  | lit => trivial
  | var => trivial
  | builtinOk => trivial
  | builtinHalt => trivial
  | builtinArgsHalt => trivial
  | callOk => trivial
  | callHalt => trivial
  | callArgsHalt => trivial
  | argsNil => trivial
  | argsCons => trivial
  | argsRestHalt => trivial
  | argsHeadHalt => trivial
  | funDef => exact ⟨by simp [declsOfStmt], fun locals _ => ModOut.rfl' ..⟩
  | letHalt => exact ⟨by simp, fun locals _ => ModOut.rfl' ..⟩
  | assignHalt => exact ⟨by simp, fun locals _ => ModOut.rfl' ..⟩
  | exprStmt => exact ⟨by simp [declsOfStmt], fun locals _ => ModOut.rfl' ..⟩
  | exprStmtHalt => exact ⟨by simp, fun locals _ => ModOut.rfl' ..⟩
  | ifFalse => exact ⟨by simp [declsOfStmt], fun locals _ => ModOut.rfl' ..⟩
  | ifHalt => exact ⟨by simp, fun locals _ => ModOut.rfl' ..⟩
  | switchHalt => exact ⟨by simp, fun locals _ => ModOut.rfl' ..⟩
  | «break» => exact ⟨by simp, fun locals _ => ModOut.rfl' ..⟩
  | «continue» => exact ⟨by simp, fun locals _ => ModOut.rfl' ..⟩
  | leave => exact ⟨by simp, fun locals _ => ModOut.rfl' ..⟩
  | seqNil => exact ⟨⟨[], rfl, fun _ => ⟨rfl, by simp [declsOf]⟩⟩,
      fun locals _ => ModOut.rfl' ..⟩
  | loopDone => exact ⟨⟨[], rfl⟩, fun locals _ => ModOut.rfl' ..⟩
  | loopCondHalt => exact ⟨⟨[], rfl⟩, fun locals _ => ModOut.rfl' ..⟩
  | @letZero funs V st vars =>
    have hbn : VEnv.names (YulSemantics.bindZeros yulD vars) = vars := by
      simp [VEnv.names, YulSemantics.bindZeros, Function.comp_def]
    have hbl : (YulSemantics.bindZeros yulD vars).length = vars.length := by
      simp [YulSemantics.bindZeros]
    refine ⟨by rw [VEnv.names_append, hbn]; simp [declsOfStmt], fun locals _ => ?_⟩
    refine ⟨by simp [hbl], fun n hn => ?_⟩
    rw [show ((YulSemantics.bindZeros yulD vars ++ V).length - n)
        = (YulSemantics.bindZeros yulD vars).length + (V.length - n) from by
      rw [List.length_append, hbl]; omega, drop_append_len]
    exact YulSemantics.Forall₂.refl (fun _ => ⟨rfl, Or.inl rfl⟩) _
  | @letVal funs V st vars e vals st1 _ hlen _ =>
    have hbn : VEnv.names (vars.zip vals) = vars := by
      rw [VEnv.names, List.map_fst_zip]
      omega
    have hbl : (vars.zip vals).length = vars.length := by
      simp; omega
    refine ⟨by rw [VEnv.names_append, hbn]; simp [declsOfStmt], fun locals _ => ?_⟩
    refine ⟨by simp [hbl], fun n hn => ?_⟩
    rw [show ((vars.zip vals ++ V).length - n)
        = (vars.zip vals).length + (V.length - n) from by
      rw [List.length_append, hbl]; omega, drop_append_len]
    exact YulSemantics.Forall₂.refl (fun _ => ⟨rfl, Or.inl rfl⟩) _
  | @assignVal funs V st vars e vals st1 _ hlen _ =>
    refine ⟨by rw [VEnv.names_setMany]; simp [declsOfStmt], fun locals hloc => ?_⟩
    refine ⟨by rw [VEnv.length_setMany], fun n hn => ?_⟩
    rw [VEnv.length_setMany]
    refine setMany_drop_forall₂ ?_
    intro x hx
    by_cases hxl : x ∈ locals
    · refine Or.inr ?_
      rw [names_take]
      exact mem_take_mono (m := locals.length) (by omega)
        (by rw [← names_take]; exact hloc x hxl)
    · exact Or.inl (List.mem_filter.mpr ⟨hx, by simpa using hxl⟩)
  | @block funs V st body Vb stb o _ ih =>
    have hlen : V.length ≤ Vb.length := (ih.2 [] (localsOK_nil V)).1
    obtain ⟨W, hsh, -⟩ := ih.1
    exact ⟨by rw [names_restore hlen hsh]; simp [declsOfStmt],
      fun locals hloc => (ih.2 locals hloc).restoreR⟩
  | @ifTrue funs V st c body cv st1 V' st2 o _ _ _ _ ih3 =>
    exact ⟨by rw [ih3.1]; rfl, fun locals hloc => ih3.2 locals hloc⟩
  | @switchExec funs V st c cases dflt cv st1 V' st2 o _ _ _ ih2 =>
    refine ⟨by rw [ih2.1]; rfl, fun locals hloc => (ih2.2 locals hloc).mono_mods ?_⟩
    intro x hx
    exact mem_modStmt_switch hx
  | @forLoop funs V st init c post body Vinit stinit Vend stend o _ _ ih1 ih2 =>
    obtain ⟨W1, hn1, hd1⟩ := ih1.1
    obtain ⟨hW1len, hW1mem⟩ := hd1 rfl
    obtain ⟨W2, hn2⟩ := ih2.1
    have hlenV : V.length ≤ Vinit.length := (ih1.2 [] (localsOK_nil V)).1
    have hlenI : Vinit.length ≤ Vend.length := (ih2.2 [] (localsOK_nil Vinit)).1
    have hVi : Vinit.length = (declsOf init).length + V.length := by
      have hh := congrArg List.length hn1
      simp only [VEnv.length_names, List.length_append] at hh
      omega
    refine ⟨by
      rw [names_restore (Nat.le_trans hlenV hlenI)
        (show VEnv.names Vend = (W2 ++ W1) ++ VEnv.names V by
          rw [hn2, hn1, List.append_assoc])]
      simp [declsOfStmt], fun locals hloc => ?_⟩
    have hloc2 : LocalsOK (declsOf init ++ locals) Vinit := by
      intro x hx
      rw [names_take, hn1,
        show (declsOf init ++ locals).length = W1.length + locals.length from by
          rw [List.length_append, hW1len],
        take_append_len]
      rcases List.mem_append.mp hx with h | h
      · exact List.mem_append_left _ (hW1mem x h)
      · exact List.mem_append_right _ (by rw [← names_take]; exact hloc x h)
    refine ((ModOut.trans (ih1.2 locals hloc) (ih2.2 _ hloc2) ?_).mono_mods
      ?_).restoreR
    · intro n hn
      rw [List.length_append, hVi]
      omega
    · intro x hx
      simp only [modStmt]
      rcases List.mem_append.mp hx with h | h
      · exact List.mem_append_left _ (List.mem_append_left _ h)
      · rcases List.mem_append.mp h with h' | h'
        · exact List.mem_append_left _ (List.mem_append_right _ h')
        · exact List.mem_append_right _ h'
  | @forInitHalt funs V st init c post body Vinit stinit _ ih =>
    have hlen : V.length ≤ Vinit.length := (ih.2 [] (localsOK_nil V)).1
    obtain ⟨W, hsh, -⟩ := ih.1
    refine ⟨by rw [names_restore hlen hsh]; simp,
      fun locals hloc => ((ih.2 locals hloc).restoreR).mono_mods ?_⟩
    intro x hx
    simp only [modStmt]
    exact List.mem_append_left _ (List.mem_append_left _ hx)
  | @seqCons funs V st s rest V1 st1 V2 st2 o _ _ ih1 ih2 =>
    have hn1 : VEnv.names V1 = declsOfStmt s ++ VEnv.names V := by
      have hh := ih1.1; simpa using hh
    have hl1 : V1.length = (declsOfStmt s).length + V.length := by
      have hh := congrArg List.length hn1
      simp only [VEnv.length_names, List.length_append] at hh
      omega
    have hlocT : ∀ locals, LocalsOK locals V → LocalsOK (localsAfter locals s) V1 := by
      intro locals hloc x hx
      rw [localsAfter_eq] at hx
      rw [localsAfter_eq, names_take, hn1,
        show (declsOfStmt s ++ locals).length
          = (declsOfStmt s).length + locals.length from by simp,
        take_append_len]
      rcases List.mem_append.mp hx with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (by rw [← names_take]; exact hloc x h)
    obtain ⟨W2, hn2, hd2⟩ := ih2.1
    refine ⟨⟨W2 ++ declsOfStmt s, by rw [hn2, hn1, List.append_assoc], ?_⟩,
      fun locals hloc => ?_⟩
    · intro ho
      obtain ⟨hlen2, hmem2⟩ := hd2 ho
      refine ⟨by rw [declsOf_cons, List.length_append, List.length_append, hlen2]; omega, ?_⟩
      intro x hx
      rw [declsOf_cons] at hx
      rcases List.mem_append.mp hx with h | h
      · exact List.mem_append_right _ h
      · exact List.mem_append_left _ (hmem2 x h)
    · rw [modStmts_cons]
      refine ModOut.trans (ih1.2 locals hloc) (ih2.2 _ (hlocT locals hloc)) ?_
      intro n hn
      rw [localsAfter_eq, List.length_append, hl1]
      omega
  | @seqStop funs V st s rest V1 st1 o _ ho ih =>
    refine ⟨⟨_, ih.1, fun hn => absurd hn ho⟩,
      fun locals hloc => (ih.2 locals hloc).mono_mods ?_⟩
    intro x hx
    simp only [modStmts]
    exact List.mem_append_left _ hx
  | @loopStep funs V st c post body cv st1 Vb stb ob Vp stp Vend stend o
      _h1 _hne _h3 _hob _h5 _h6 _ih1 ih3 ih5 ih6 =>
    have hnb : VEnv.names Vb = VEnv.names V := by
      have hh := ih3.1; simpa [declsOfStmt] using hh
    have hnp : VEnv.names Vp = VEnv.names Vb := by
      have hh := ih5.1; simpa [declsOfStmt] using hh
    obtain ⟨W, hnW⟩ := ih6.1
    refine ⟨⟨W, by rw [hnW, hnp, hnb]⟩, fun locals hloc => ?_⟩
    have hlocB : LocalsOK locals Vb := LocalsOK.ofNames hnb hloc
    have hlocP : LocalsOK locals Vp := LocalsOK.ofNames hnp hlocB
    have hlb : V.length ≤ Vb.length := by
      rw [← VEnv.length_names, ← VEnv.length_names, hnb]
    have hlp : Vb.length ≤ Vp.length := by
      rw [← VEnv.length_names, ← VEnv.length_names, hnp]
    refine ((ModOut.trans (ih3.2 locals hloc)
      (ModOut.trans (ih5.2 locals hlocB) (ih6.2 locals hlocP)
        (fun n hn => by omega)) (fun n hn => by omega)).mono_mods ?_)
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact List.mem_append_right _ h
    · rcases List.mem_append.mp h with h' | h'
      · exact List.mem_append_left _ h'
      · exact h'
  | @loopPostHalt funs V st c post body cv st1 Vb stb ob Vp stp
      _h1 _hne _h3 _hob _h5 _ih1 ih3 ih5 =>
    have hnb : VEnv.names Vb = VEnv.names V := by
      have hh := ih3.1; simpa [declsOfStmt] using hh
    have hnp : VEnv.names Vp = VEnv.names Vb := by
      have hh := ih5.1; simpa using hh
    refine ⟨⟨[], by rw [hnp, hnb]; simp⟩, fun locals hloc => ?_⟩
    have hlocB : LocalsOK locals Vb := LocalsOK.ofNames hnb hloc
    have hlb : V.length ≤ Vb.length := by
      rw [← VEnv.length_names, ← VEnv.length_names, hnb]
    refine ((ModOut.trans (ih3.2 locals hloc) (ih5.2 locals hlocB)
      (fun n hn => by omega)).mono_mods ?_)
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact List.mem_append_right _ h
    · exact List.mem_append_left _ h
  | @loopBreak funs V st c post body cv st1 Vb stb _ _ _ _ ih =>
    exact ⟨⟨_, ih.1⟩, fun locals hloc =>
      (ih.2 locals hloc).mono_mods (fun x hx => List.mem_append_right _ hx)⟩
  | @loopLeave funs V st c post body cv st1 Vb stb _ _ _ _ ih =>
    exact ⟨⟨_, ih.1⟩, fun locals hloc =>
      (ih.2 locals hloc).mono_mods (fun x hx => List.mem_append_right _ hx)⟩
  | @loopBodyHalt funs V st c post body cv st1 Vb stb _ _ _ _ ih =>
    exact ⟨⟨_, ih.1⟩, fun locals hloc =>
      (ih.2 locals hloc).mono_mods (fun x hx => List.mem_append_right _ hx)⟩

/-- The small induction motive used to isolate the name-spine invariant of the
`.loop` code class. -/
def LoopNamesMotive (V : VEnv yulD) :
    YulSemantics.Code Op → YulSemantics.Res yulD → Prop
  | .loop _ _ _, .sres V' _ _ => VEnv.names V' = VEnv.names V
  | _, _ => True

/-- Loop bodies and posts are blocks, so each iteration restores their local
bindings before either repeating or returning.  Consequently an entire loop
keeps the environment's name spine unchanged. -/
theorem loop_names_sim {funs : YulSemantics.FunEnv yulD} {V : VEnv yulD}
    {yst : EvmState} {code : YulSemantics.Code Op}
    {res : YulSemantics.Res yulD}
    (h : YulSemantics.Step yulD funs V yst code res) :
    LoopNamesMotive V code res := by
  induction h <;> simp only [LoopNamesMotive]
  case loopStep funs V st c post body cv st1 Vb stb ob Vp stp Vend stend o
      hc hnz hb hob hp hl ihc ihb ihp ihl =>
    have hnb : VEnv.names Vb = VEnv.names V := by
      simpa [declsOfStmt] using (mod_sim hb).1
    have hnp : VEnv.names Vp = VEnv.names Vb := by
      simpa [declsOfStmt] using (mod_sim hp).1
    exact ihl.trans (hnp.trans hnb)
  case loopPostHalt funs V st c post body cv st1 Vb stb ob Vp stp
      hc hnz hb hob hp ihc ihb ihp =>
    have hnb : VEnv.names Vb = VEnv.names V := by
      simpa [declsOfStmt] using (mod_sim hb).1
    have hnp : VEnv.names Vp = VEnv.names Vb := by
      simpa [declsOfStmt] using (mod_sim hp).1
    exact hnp.trans hnb
  case loopBreak funs V st c post body cv st1 Vb stb hc hnz hb ihc ihb =>
    simpa [declsOfStmt] using (mod_sim hb).1
  case loopLeave funs V st c post body cv st1 Vb stb hc hnz hb ihc ihb =>
    simpa [declsOfStmt] using (mod_sim hb).1
  case loopBodyHalt funs V st c post body cv st1 Vb stb hc hnz hb ihc ihb =>
    simpa [declsOfStmt] using (mod_sim hb).1

theorem loop_names {funs : YulSemantics.FunEnv yulD} {V V' : VEnv yulD}
    {yst yst' : EvmState} {c : Expr Op} {post body : List (Stmt Op)}
    {o : Outcome}
    (h : YulSemantics.Step yulD funs V yst (.loop c post body)
      (.sres V' yst' o)) : VEnv.names V' = VEnv.names V :=
  loop_names_sim h

/-- Reconstruct a join environment from the values carried for every possibly
modified visible name.  Uniqueness is exactly what turns agreement of visible
lookups back into equality of the positional environments. -/
theorem setMany_eq_of_modOut {env : VMap} {R : Regs} {V W : VEnv yulD}
    {mods xs : List Ident} {vals : List U256}
    (henv : EnvOK (model := model) env V R) (huniq : env.Unique)
    (hnames : VEnv.names W = VEnv.names V) (hmod : ModOut [] mods V W)
    (hvals : Forall₂
      (fun x v => YulSemantics.VEnv.get W x = some v) xs vals)
    (_hxs : ∀ x ∈ xs, x ∈ env.map Prod.fst)
    (hcover : ∀ x ∈ env.map Prod.fst, x ∈ mods → x ∈ xs) :
    YulSemantics.VEnv.setMany V xs vals = W := by
  apply VEnv.eq_of_names_get
  · rw [VEnv.names_setMany]
    exact henv.unique_names huniq
  · rw [VEnv.names_setMany, hnames]
  · intro x hx
    rw [VEnv.names_setMany] at hx
    by_cases hxm : x ∈ xs
    · have hWset : YulSemantics.VEnv.setMany W xs vals = W :=
        VEnv.setMany_self hvals
      calc
        YulSemantics.VEnv.get (YulSemantics.VEnv.setMany V xs vals) x =
            YulSemantics.VEnv.get (YulSemantics.VEnv.setMany W xs vals) x :=
          VEnv.get_setMany_congr_of_mem hvals.length_eq hxm hx
            (by rw [hnames]; exact hx)
        _ = YulSemantics.VEnv.get W x := by rw [hWset]
    · rw [VEnv.get_setMany_not_mem hxm]
      have hxenv : x ∈ env.map Prod.fst := by rw [henv.names]; exact hx
      have hxmod : x ∉ mods := fun hm => hxm (hcover x hxenv hm)
      have hf := hmod.2 V.length (by simp)
      have hlen : W.length = V.length := by
        rw [← VEnv.length_names, ← VEnv.length_names, hnames]
      rw [Nat.sub_self, List.drop_zero, hlen, Nat.sub_self, List.drop_zero] at hf
      exact (get_congr_of_forall₂ hxmod hf).symm

omit model in
/-- The loop body inherits the context: its `break`/`continue` variable set is
the loop's `modifiedX`, a sublist of the visible names, and the header rebinding
`setMany` leaves the name spine alone. -/
theorem CtxVars.loopBody {rets : Option (List Ident)} {env : VMap}
    (h : CtxVars none rets env) (brk cont : BlockId)
    (bodies : List (List (Stmt Op))) (hParams : List ValId) :
    CtxVars (some ⟨brk, cont, modifiedX env bodies⟩) rets
      (env.setMany (modifiedX env bodies) hParams) := by
  constructor
  · intro lc hlc x hx
    cases hlc
    rw [VMap.names_setMany]
    exact modifiedX_mem_names hx
  · intro rs hrs x hx
    rw [VMap.names_setMany]
    exact h.2 rs hrs x hx

/-- A statement that completes normally only *extends* the visible name spine,
so the context stays visible in the environment it hands to the tail. -/
theorem CtxVars.step_normal {lctx : Option LoopCtx} {rets : Option (List Ident)}
    {env envA : VMap} {V V1 : VEnv yulD} {R R' : Regs}
    {funs : YulSemantics.FunEnv yulD} {yst yst1 : EvmState} {st : Stmt Op}
    (hctx : CtxVars lctx rets env)
    (henv : EnvOK (model := model) env V R)
    (henvA : EnvOK (model := model) envA V1 R')
    (h1 : YulSemantics.Step yulD funs V yst (.stmt st) (.sres V1 yst1 .normal)) :
    CtxVars lctx rets envA := by
  refine hctx.mono (fun x hx => ?_)
  rw [henv.names] at hx
  rw [henvA.names, (mod_sim h1).1]
  simp only [if_pos]
  exact List.mem_append_right _ hx

end Semantics
end YulEvmCompiler.SsaCfg
