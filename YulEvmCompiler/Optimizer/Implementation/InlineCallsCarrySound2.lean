import YulEvmCompiler.Optimizer.Implementation.InlineCallsCarrySoundFwd
set_option warningAsError true
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM

variable {calls : ExternalCalls} {creates : ExternalCreates}

local notation "D" => evmWithExternal calls creates

/-- Backward mirror of `cyRel_stmts_cons_inv`: invert a `CyRel` whose **target**
is a non-empty statement list, returning the target head/tail shape as
**equations** (keeping the principal derivation's code index a bare variable so
`cy_bwd`'s structural recursion still threads `brecOn`). -/
theorem cyRel_stmts_cons_inv_bwd {Δ : DEnv} {s₂ : Stmt Op} {rest₂ : List (Stmt Op)}
    {pc : PCode Op} (hrel : CyRel Δ pc (.stmts (s₂ :: rest₂))) :
    (∃ s rest, pc = .stmts (s :: rest) ∧
        CyRel Δ (.stmt s) (.stmt s₂) ∧ CyRel Δ (.stmts rest) (.stmts rest₂))
  ∨ (∃ (f : Ident) (d : IDecl) (xs : List Ident) (as : List (Expr Op))
        (rest : List (Stmt Op)),
        pc = .stmts (.letDecl xs (some (.call f as)) :: rest) ∧
        s₂ = .letDecl xs none ∧
        lookupDelta Δ f = some d ∧ (d.ps ++ d.rs).Nodup ∧
        carryStmts (d.ps ++ d.rs) d.ss = true ∧ siteOK d xs as true = true ∧
        CyRel Δ (.stmts (.assign xs (.call f as) :: rest)) (.stmts rest₂))
  ∨ (∃ (f : Ident) (d : IDecl) (xs : List Ident) (as : List (Expr Op))
        (rest : List (Stmt Op)),
        pc = .stmts (.assign xs (.call f as) :: rest) ∧
        s₂ = inlineCore d xs as ∧
        lookupDelta Δ f = some d ∧ (d.ps ++ d.rs).Nodup ∧
        carryStmts (d.ps ++ d.rs) d.ss = true ∧ siteOK d xs as false = true ∧
        CyRel Δ (.stmts rest) (.stmts rest₂))
  ∨ (∃ (f : Ident) (d : IDecl) (as : List (Expr Op)) (rest : List (Stmt Op)),
        pc = .stmts (.exprStmt (.call f as) :: rest) ∧
        s₂ = inlineCore d [] as ∧
        lookupDelta Δ f = some d ∧ (d.ps ++ d.rs).Nodup ∧
        carryStmts (d.ps ++ d.rs) d.ss = true ∧ siteOK d [] as false = true ∧
        CyRel Δ (.stmts rest) (.stmts rest₂)) := by
  cases hrel with
  | consSS hs hrest => exact Or.inl ⟨_, _, rfl, hs, hrest⟩
  | siteLet hld hnd hsc hok hrest =>
      exact Or.inr (Or.inl ⟨_, _, _, _, _, rfl, rfl, hld, hnd, hsc, hok,
        CyRel.siteAssign hld hnd hsc (siteOK_weaken hok) hrest⟩)
  | siteAssign hld hnd hsc hok hrest =>
      exact Or.inr (Or.inr (Or.inl ⟨_, _, _, _, _, rfl, rfl, hld, hnd, hsc, hok, hrest⟩))
  | siteExpr hld hnd hsc hok hrest =>
      exact Or.inr (Or.inr (Or.inr ⟨_, _, _, _, rfl, rfl, hld, hnd, hsc, hok, hrest⟩))

/-- Prepend a list of (unevaluated) arguments to a halting `.args` run. -/
theorem args_prepend_halt {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    {suffix : List (Expr Op)} {st1 : EvmState}
    (h : Step D funs V st (.args suffix) (.eres (.halt st1))) :
    ∀ (pre : List (Expr Op)),
      Step D funs V st (.args (pre ++ suffix)) (.eres (.halt st1)) := by
  intro pre
  induction pre with
  | nil => exact h
  | cons e pre' ih => exact Step.argsRestHalt ih

/-- From a global `argsHaveCall … = false`, an element is call-free. -/
theorem argsHaveCall_split {a : Expr Op} {post : List (Expr Op)} :
    ∀ {pre : List (Expr Op)}, argsHaveCall (pre ++ a :: post) = false →
      exprHasCall a = false := by
  intro pre
  induction pre with
  | nil =>
      intro h
      rw [List.nil_append,
        show argsHaveCall (a :: post) = (exprHasCall a || argsHaveCall post) from rfl,
        Bool.or_eq_false_iff] at h
      exact h.1
  | cons e pre' ih =>
      intro h
      rw [List.cons_append,
        show argsHaveCall (e :: (pre' ++ a :: post)) =
          (exprHasCall e || argsHaveCall (pre' ++ a :: post)) from rfl,
        Bool.or_eq_false_iff] at h
      exact ih h.2

/-- `argsShadowOK` gives that a pair's argument avoids the parameters strictly
after it. -/
theorem argsShadowOK_after {rs : List Ident} {p : Ident} {a : Expr Op}
    {post : List (Ident × Expr Op)} :
    ∀ {pre : List (Ident × Expr Op)},
      argsShadowOK rs (pre ++ (p, a) :: post) = true →
      ∀ y ∈ exprVars a, y ∉ post.map Prod.fst := by
  intro pre
  induction pre with
  | nil =>
      intro h y hy
      rw [List.nil_append,
        show argsShadowOK rs ((p, a) :: post) =
          ((exprVars a).all (fun v => !(post.map Prod.fst).contains v && !rs.contains v) &&
            argsShadowOK rs post) from rfl,
        Bool.and_eq_true] at h
      have hall := List.all_eq_true.mp h.1 y hy
      rw [Bool.and_eq_true] at hall
      simpa using hall.1
  | cons pr pre' ih =>
      intro h y hy
      rcases pr with ⟨q, b⟩
      rw [List.cons_append,
        show argsShadowOK rs ((q, b) :: (pre' ++ (p, a) :: post)) =
          ((exprVars b).all
              (fun v => !((pre' ++ (p, a) :: post).map Prod.fst).contains v && !rs.contains v) &&
            argsShadowOK rs (pre' ++ (p, a) :: post)) from rfl,
        Bool.and_eq_true] at h
      exact ih h.2 y hy

/-- `letZero` result inversion, returning equations (so no sibling index gets
refined by a `cases` in the caller's structural recursion). -/
theorem letZero_inv {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    {xs : List Ident} {res : Res D}
    (h : Step D funs V st (.stmt (.letDecl xs none)) res) :
    res = .sres (bindZeros D xs ++ V) st .normal := by
  cases h with
  | letZero => rfl

theorem varsList_append (a b : List (Expr Op)) :
    varsList (a ++ b) = varsList a ++ varsList b := by
  induction a with
  | nil => rfl
  | cons e rest ih =>
      rw [List.cons_append,
        show varsList (e :: (rest ++ b)) = exprVars e ++ varsList (rest ++ b) from rfl, ih,
        show varsList (e :: rest) = exprVars e ++ varsList rest from rfl, List.append_assoc]

/-- Invert a `halt` `TResL` from the **target** (second) side. -/
theorem TResL.halt_inv' {W W' : VEnv D} {post : List Ident} {res₁ : Res D}
    {V₂ : VEnv D} {st₂ : EvmState}
    (h : TResL (calls := calls) (creates := creates) W W' post res₁
      (.sres V₂ st₂ .halt)) :
    ∃ A', V₂ = A' ++ W' ∧ res₁ = .sres (A' ++ W) st₂ .halt := by
  cases h with
  | halt => exact ⟨_, rfl, rfl⟩

/-- Invert a `normal` `TResL` from the **target** (second) side. -/
theorem TResL.norm_inv' {W W' : VEnv D} {post : List Ident} {res₁ : Res D}
    {V₂ : VEnv D} {st₂ : EvmState}
    (h : TResL (calls := calls) (creates := creates) W W' post res₁
      (.sres V₂ st₂ .normal)) :
    ∃ A', V₂ = A' ++ W' ∧ res₁ = .sres (A' ++ W) st₂ .normal ∧
      (∀ x ∈ post, x ∈ A'.map Prod.fst) := by
  cases h with
  | norm hk => exact ⟨_, rfl, rfl, hk⟩

/-- Invert a `leave` `TResL` from the **target** (second) side. -/
theorem TResL.leave_inv' {W W' : VEnv D} {post : List Ident} {res₁ : Res D}
    {V₂ : VEnv D} {st₂ : EvmState}
    (h : TResL (calls := calls) (creates := creates) W W' post res₁
      (.sres V₂ st₂ .leave)) :
    ∃ A', V₂ = A' ++ W' ∧ res₁ = .sres (A' ++ W) st₂ .leave := by
  cases h with
  | «leave» => exact ⟨_, rfl, rfl⟩

/-- Invert a single-variable `letDecl … (some e)` that ran to `normal`. -/
theorem letSome_norm_inv {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    {x : Ident} {e : Expr Op} {V1 : VEnv D} {st1 : EvmState}
    (h : Step D funs V st (.stmt (.letDecl [x] (some e))) (.sres V1 st1 .normal)) :
    ∃ v, Step D funs V st (.expr e) (.eres (.vals [v] st1)) ∧ V1 = (x, v) :: V := by
  cases h with
  | @letVal _ _ _ _ _ vals stv he hlenv =>
      obtain ⟨v, rfl⟩ : ∃ v, vals = [v] := by
        cases vals with
        | nil => simp at hlenv
        | cons v vrest =>
            cases vrest with
            | nil => exact ⟨v, rfl⟩
            | cons _ _ => simp at hlenv
      exact ⟨v, he, rfl⟩

/-- Invert a single-variable `letDecl … (some e)` that ran to a non-`normal`
outcome: it can only be a `halt`. -/
theorem letSome_stop_inv {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    {x : Ident} {e : Expr Op} {V1 : VEnv D} {st1 : EvmState} {o : Outcome}
    (h : Step D funs V st (.stmt (.letDecl [x] (some e))) (.sres V1 st1 o))
    (hne : o ≠ .normal) :
    Step D funs V st (.expr e) (.eres (.halt st1)) ∧ V1 = V ∧ o = .halt := by
  cases h with
  | @letVal _ _ _ _ _ vals stv he hlenv => exact absurd rfl hne
  | @letHalt _ _ _ _ _ st1' he => exact ⟨he, rfl, rfl⟩

/-- Transfer one argument-`let`'s expression evaluation from the inlined-core
scope (`Sfuns`, `Ecur`) back to the source caller (`funs₁`, `V`): the argument
is call-free and its reads avoid the peeled parameters, the return-zone
`bindZeros`, and the fresh `Z` prefix. -/
theorem argLet_src_transfer {funs₁ Sfuns : FunEnv D} {V Z Ecur : VEnv D}
    {st_cur : EvmState} {d : IDecl} {as : List (Expr Op)}
    {Ppeeled Pfr' : List (Ident × Expr Op)} {valsDone : List U256}
    {pa : Ident × Expr Op}
    (hEcur : Ecur = (Ppeeled.map Prod.fst).zip valsDone ++ (bindZeros D d.rs ++ (Z ++ V)))
    (hvlen : valsDone.length = Ppeeled.length)
    (hlen_as : as.length = d.ps.length)
    (hnc : argsHaveCall as = false)
    (hsh : argsShadowOK d.rs (d.ps.zip as) = true)
    (hZ : ∀ y ∈ varsList as, y ∉ Z.map Prod.fst)
    (hP' : Pfr'.reverse ++ (pa :: Ppeeled) = d.ps.zip as)
    {r : EResult D}
    (he : Step D Sfuns Ecur st_cur (.expr pa.2) (.eres r)) :
    Step D funs₁ V st_cur (.expr pa.2) (.eres r) := by
  obtain ⟨pn, pe⟩ := pa
  have hsh' : argsShadowOK d.rs (Pfr'.reverse ++ (pn, pe) :: Ppeeled) = true := by
    rw [hP']; exact hsh
  have has_eq : as = Pfr'.reverse.map Prod.snd ++ (pe :: Ppeeled.map Prod.snd) := by
    rw [← zip_snds (ps := d.ps) hlen_as.symm, ← hP', List.map_append, List.map_cons]
  have hnc_pa : exprHasCall pe = false :=
    argsHaveCall_split (pre := Pfr'.reverse.map Prod.snd) (post := Ppeeled.map Prod.snd)
      (by rw [← has_eq]; exact hnc)
  have hnPp : ∀ y ∈ exprVars pe, y ∉ Ppeeled.map Prod.fst :=
    argsShadowOK_after (rs := d.rs) (pre := Pfr'.reverse) hsh'
  have hmemas : ∀ y ∈ exprVars pe, y ∈ varsList as := by
    intro y hy
    rw [has_eq, varsList_append]
    refine List.mem_append.mpr (Or.inr ?_)
    rw [show varsList (pe :: Ppeeled.map Prod.snd)
          = exprVars pe ++ varsList (Ppeeled.map Prod.snd) from rfl]
    exact List.mem_append.mpr (Or.inl hy)
  have hnrs : ∀ y ∈ exprVars pe, y ∉ d.rs := by
    intro y hy
    have hh := argsShadowOK_rs (rs := d.rs) hsh y
    rw [zip_snds hlen_as.symm] at hh
    exact hh (hmemas y hy)
  have hagree : ∀ y ∈ exprVars pe, VEnv.get V y = VEnv.get Ecur y := by
    intro y hy
    rw [hEcur]
    have h1 : y ∉ ((Ppeeled.map Prod.fst).zip valsDone).map Prod.fst := by
      rw [List.map_fst_zip (by rw [List.length_map]; omega)]
      exact hnPp y hy
    have h2 : y ∉ (bindZeros D d.rs).map Prod.fst := by
      rw [bindZeros_keys]; exact hnrs y hy
    rw [VEnv.get_append_not_mem h1, VEnv.get_append_not_mem h2,
      VEnv.get_append_not_mem (hZ y (hmemas y hy))]
  exact exprNoCall_transfer he funs₁ ⟨hnc_pa, hagree⟩

/-- The backward dissection produced by `peelArgs`, named so the mutual's
structural-recursion `brecOn` motive stays opaque (a bare `def` application),
keeping the `isDefEq` on recursive calls cheap. -/
def PeelArgsSpec (funs₁ cenv₀ : FunEnv D) (V Z : VEnv D) (st : EvmState)
    (d : IDecl) (xs : List Ident) (as : List (Expr Op))
    (Vinner : VEnv D) (str : EvmState) (o : Outcome) : Prop :=
  (∃ argvals st1 Vend,
    Step D funs₁ V st (.args as) (.eres (.vals argvals st1)) ∧
    Step D cenv₀ (d.ps.zip argvals ++ bindZeros D d.rs) st1
      (.stmt (.block d.ss)) (.sres Vend str .normal) ∧
    Vinner = Vend ++ VEnv.setMany (Z ++ V) xs (d.rs.map
      (fun r => (VEnv.get Vend r).getD (evmWithExternal calls creates).zero)) ∧
    o = .normal) ∨
  (∃ argvals st1 Vend,
    Step D funs₁ V st (.args as) (.eres (.vals argvals st1)) ∧
    Step D cenv₀ (d.ps.zip argvals ++ bindZeros D d.rs) st1
      (.stmt (.block d.ss)) (.sres Vend str .halt) ∧
    Vinner = Vend ++ (Z ++ V) ∧ o = .halt) ∨
  (∃ M : VEnv D, Step D funs₁ V st (.args as) (.eres (.halt str)) ∧
    Vinner = M ++ (Z ++ V) ∧ o = .halt)

/-- Read-out finish for the **normal** callee-body path: the transferred body run
completes normally, then the return-copy assignments reproduce the sequential
read-out. Produces the first (normal) disjunct. -/
theorem nil_seqCons_finish {funs₁ cenv₀ Sfuns : FunEnv D} {V Z : VEnv D}
    {st st_cur : EvmState} {d : IDecl} {xs : List Ident} {as : List (Expr Op)}
    {valsDone : List U256} {A0 : VEnv D} {res₁ : Res D} {Vmid : VEnv D}
    {stmid : EvmState} {Vfin : VEnv D} {stfin : EvmState} {ofin : Outcome}
    {Vinner : VEnv D} {str : EvmState} {o : Outcome}
    (hargs : Step D funs₁ V st (.args as) (.eres (.vals valsDone st_cur)))
    (hA0eq : A0 = d.ps.zip valsDone ++ bindZeros D d.rs)
    (hvd : valsDone.length = d.ps.length)
    (hxout : ∀ x ∈ xs, x ∉ d.ps ++ d.rs) (hlen_xs : xs.length = d.rs.length)
    (hstep : Step D cenv₀ (A0 ++ ([] : VEnv D)) st_cur (.stmt (.block d.ss)) res₁)
    (htr : TResL (calls := calls) (creates := creates) ([] : VEnv D) (Z ++ V)
      (d.ps ++ d.rs) res₁ (.sres Vmid stmid .normal))
    (hrest : Step D Sfuns Vmid stmid
      (.stmts ((xs.zip d.rs).map (fun xr => Stmt.assign [xr.1] (Expr.var xr.2))))
      (.sres Vfin stfin ofin))
    (hres : Res.sres Vfin stfin ofin = .sres Vinner str o) :
    PeelArgsSpec funs₁ cenv₀ V Z st d xs as Vinner str o := by
  unfold PeelArgsSpec
  obtain ⟨A', hVmid, hres₁, hk⟩ := TResL.norm_inv' htr
  rw [hres₁] at hstep
  simp only [List.append_nil] at hstep
  rw [hA0eq] at hstep
  have hA'keys : A'.map Prod.fst = d.ps ++ d.rs := by
    rw [(block_stmt_shape hstep).1,
      calleeFrame_keys (by omega : d.ps.length ≤ valsDone.length)]
  rw [hVmid] at hrest
  obtain ⟨hVfin, hstfin, hofin⟩ := assigns_bwd (A' := A') (Wb := Z ++ V) hrest
    (fun r hr => by rw [hA'keys]; exact List.mem_append.mpr (Or.inr hr))
    (fun x hx => by rw [hA'keys]; exact hxout x hx) hlen_xs
  injection hres with hVf hstf hof
  refine Or.inl ⟨valsDone, st_cur, A', hargs, ?_, ?_, ?_⟩
  · have hss : stmid = str := hstfin.symm.trans hstf
    rw [hss] at hstep; exact hstep
  · exact hVf ▸ hVfin
  · exact hof.symm.trans hofin

/-- Read-out finish for the **non-normal** callee-body path: a strict carry body
cannot `leave`, so the block either `halt`s (second disjunct) or the `leave` case
is refuted through `carry_transfer` (whose `TRes` has no `leave`). -/
theorem nil_seqStop_finish {funs₁ cenv₀ : FunEnv D} {V Z : VEnv D}
    {st st_cur : EvmState} {d : IDecl} {xs : List Ident} {as : List (Expr Op)}
    {valsDone : List U256} {A0 : VEnv D} {res₁ : Res D} {Vfin : VEnv D}
    {stfin : EvmState} {ofin : Outcome}
    {Vinner : VEnv D} {str : EvmState} {o : Outcome}
    (hargs : Step D funs₁ V st (.args as) (.eres (.vals valsDone st_cur)))
    (hA0eq : A0 = d.ps.zip valsDone ++ bindZeros D d.rs)
    (hvd : valsDone.length = d.ps.length)
    (hsc : carryStmts (d.ps ++ d.rs) d.ss = true)
    (hA0keys : A0.map Prod.fst = d.ps ++ d.rs)
    (hstep : Step D cenv₀ (A0 ++ ([] : VEnv D)) st_cur (.stmt (.block d.ss)) res₁)
    (htr : TResL (calls := calls) (creates := creates) ([] : VEnv D) (Z ++ V)
      (d.ps ++ d.rs) res₁ (.sres Vfin stfin ofin))
    (hne : ofin ≠ .normal)
    (hres : Res.sres Vfin stfin ofin = .sres Vinner str o) :
    PeelArgsSpec funs₁ cenv₀ V Z st d xs as Vinner str o := by
  unfold PeelArgsSpec
  cases ofin with
  | normal => exact absurd rfl hne
  | «break» => cases htr
  | «continue» => cases htr
  | halt =>
      obtain ⟨A', hVfin, hres₁⟩ := TResL.halt_inv' htr
      rw [hres₁] at hstep
      simp only [List.append_nil] at hstep
      rw [hA0eq] at hstep
      injection hres with hVf hstf hof
      refine Or.inr (Or.inl ⟨valsDone, st_cur, A', hargs, ?_, ?_, ?_⟩)
      · rw [hstf] at hstep; exact hstep
      · exact hVf ▸ hVfin
      · exact hof.symm
  | «leave» =>
      obtain ⟨A', hVfin, hres₁⟩ := TResL.leave_inv' htr
      rw [hres₁] at hstep
      simp only [List.append_nil] at hstep
      rw [hA0eq] at hstep
      have hcc : carryCode (d.ps ++ d.rs) (Code.stmt (.block d.ss)) = true := by
        simp [carryCode, carryStmt, hsc]
      obtain ⟨res₂, -, htr2⟩ := carry_transfer hstep
        (A := d.ps.zip valsDone ++ bindZeros D d.rs) (W := ([] : VEnv D))
        (bound := d.ps ++ d.rs) cenv₀ ([] : VEnv D)
        (by simp) hcc (fun x hx => by rw [← hA0eq, hA0keys]; exact hx) (FunsAgree.refl _ _)
      cases htr2

/-! ### Folded shapes + bundled context for the argument-let peel

The mutual's packed `brecOn` motive carries every member's telescope; keeping
the shape equations one-application small and the invariant hypotheses in a
single bundle is what keeps the structural-recursion elaboration affordable. -/

/-- The still-to-run tail of the inlined core, folded. -/
def peelTail (d : IDecl) (xs : List Ident) (Pfr : List (Ident × Expr Op)) :
    List (Stmt Op) :=
  Pfr.map (fun pa => Stmt.letDecl [pa.1] (some pa.2)) ++ [Stmt.block d.ss]
    ++ (xs.zip d.rs).map (fun xr => Stmt.assign [xr.1] (Expr.var xr.2))

theorem peelTail_cons (d : IDecl) (xs : List Ident) (pa : Ident × Expr Op)
    (Pfr : List (Ident × Expr Op)) :
    peelTail d xs (pa :: Pfr)
      = Stmt.letDecl [pa.1] (some pa.2) :: peelTail d xs Pfr := by
  simp [peelTail]

theorem peelTail_nil (d : IDecl) (xs : List Ident) :
    peelTail d xs [] = Stmt.block d.ss
      :: (xs.zip d.rs).map (fun xr => Stmt.assign [xr.1] (Expr.var xr.2)) := by
  simp [peelTail]

/-- The inlined-core environment mid-peel, folded. -/
def peelEnvAcc (d : IDecl) (Z V : VEnv D) (Ppeeled : List (Ident × Expr Op))
    (valsDone : List U256) : VEnv D :=
  (Ppeeled.map Prod.fst).zip valsDone ++ (bindZeros D d.rs ++ (Z ++ V))

theorem peelEnvAcc_cons (d : IDecl) (Z V : VEnv D) (pa : Ident × Expr Op)
    (P : List (Ident × Expr Op)) (v : U256) (vs : List U256) :
    peelEnvAcc d Z V (pa :: P) (v :: vs) = (pa.1, v) :: peelEnvAcc d Z V P vs := by
  simp [peelEnvAcc]

/-- Recursion-invariant context of the peel, bundled. -/
structure PeelCtx (d : IDecl) (xs : List Ident) (as : List (Expr Op))
    (cenv₀ funsI Sfuns : FunEnv D) (Z : VEnv D) : Prop where
  hsc : carryStmts (d.ps ++ d.rs) d.ss = true
  hlen_as : as.length = d.ps.length
  hnc : argsHaveCall as = false
  hsh : argsShadowOK d.rs (d.ps.zip as) = true
  hxout : ∀ x ∈ xs, x ∉ d.ps ++ d.rs
  hlen_xs : xs.length = d.rs.length
  hZ : ∀ y ∈ varsList as, y ∉ Z.map Prod.fst
  hRb : CyFunsRel (calls := calls) (creates := creates) funsI Sfuns
  hag_body : ∀ g ∈ stmtsCallNames d.ss, lookupFun cenv₀ g = lookupFun funsI g


mutual

/-- **Backward simulation** across `CyRel`: a target derivation transports back
to the source. -/
theorem cy_bwd {funs₂ : FunEnv D} {V : VEnv D} {st : EvmState}
    {code₂ : Code Op} {res₂ : Res D} (h : Step D funs₂ V st code₂ res₂) :
    ∀ {funs₁ : FunEnv D} {Δ : DEnv} {pc : PCode Op},
      CyFunsRel (calls := calls) (creates := creates) funs₁ funs₂ →
      CarryCompat (calls := calls) (creates := creates) Δ funs₁ →
      CyRel Δ pc (toPCode code₂) →
      ∃ res₁, Step D funs₁ V st (ofPCode pc) res₁ ∧
        cyResOK (calls := calls) (creates := creates) code₂ res₁ res₂ := by
  match h with
  | .lit =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | expr => exact ⟨_, Step.lit, rfl⟩
  | .var hv =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | expr => exact ⟨_, Step.var hv, rfl⟩
  | .builtinOk ha hbi =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | expr =>
          obtain ⟨res₁, hs, heq⟩ := cy_bwd ha hR hΔ CyRel.args
          have heqX : _ = res₁ := heq; rw [← heqX] at hs
          exact ⟨_, Step.builtinOk hs hbi, rfl⟩
  | .builtinHalt ha hbi =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | expr =>
          obtain ⟨res₁, hs, heq⟩ := cy_bwd ha hR hΔ CyRel.args
          have heqX : _ = res₁ := heq; rw [← heqX] at hs
          exact ⟨_, Step.builtinHalt hs hbi, rfl⟩
  | .builtinArgsHalt ha =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | expr =>
          obtain ⟨res₁, hs, heq⟩ := cy_bwd ha hR hΔ CyRel.args
          have heqX : _ = res₁ := heq; rw [← heqX] at hs
          exact ⟨_, Step.builtinArgsHalt hs, rfl⟩
  | @Step.callOk _ _ funs V st fn args argvals st1 decl cenv Vend st2 o ha hlk harity hbody ho =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | expr =>
          obtain ⟨resa, hs, heqa⟩ := cy_bwd ha hR hΔ CyRel.args
          have heqaX : _ = resa := heqa; rw [← heqaX] at hs
          obtain ⟨decl₁, cenv₁, hlk₁, hdecl, hcenvR⟩ := lookupFun_cyFunsRel_bwd hR hlk
          obtain ⟨hps, hrs, Δf, hΔf, hbrel⟩ := hdecl
          obtain ⟨resb, hsb, heqb⟩ := cy_bwd hbody hcenvR hΔf (CyRel.blockS hbrel)
          have heqbX : _ = resb := heqb; rw [← heqbX] at hsb
          have hsb' : Step D cenv₁ (decl₁.params.zip argvals ++ bindZeros D decl₁.rets)
              st1 (.stmt (.block decl₁.body)) (.sres Vend st2 o) := by
            rw [hps, hrs]; exact hsb
          have harity' : argvals.length = decl₁.params.length := by rw [hps]; exact harity
          refine ⟨_, Step.callOk hs hlk₁ harity' hsb' ho, ?_⟩
          show Res.eres (.vals (decl.rets.map _) st2) = Res.eres (.vals (decl₁.rets.map _) st2)
          rw [hrs]
  | @Step.callHalt _ _ funs V st fn args argvals st1 decl cenv Vend st2 ha hlk harity hbody =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | expr =>
          obtain ⟨resa, hs, heqa⟩ := cy_bwd ha hR hΔ CyRel.args
          have heqaX : _ = resa := heqa; rw [← heqaX] at hs
          obtain ⟨decl₁, cenv₁, hlk₁, hdecl, hcenvR⟩ := lookupFun_cyFunsRel_bwd hR hlk
          obtain ⟨hps, hrs, Δf, hΔf, hbrel⟩ := hdecl
          obtain ⟨resb, hsb, heqb⟩ := cy_bwd hbody hcenvR hΔf (CyRel.blockS hbrel)
          have heqbX : _ = resb := heqb; rw [← heqbX] at hsb
          have hsb' : Step D cenv₁ (decl₁.params.zip argvals ++ bindZeros D decl₁.rets)
              st1 (.stmt (.block decl₁.body)) (.sres Vend st2 .halt) := by
            rw [hps, hrs]; exact hsb
          have harity' : argvals.length = decl₁.params.length := by rw [hps]; exact harity
          exact ⟨_, Step.callHalt hs hlk₁ harity' hsb', rfl⟩
  | .callArgsHalt ha =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | expr =>
          obtain ⟨resa, hs, heqa⟩ := cy_bwd ha hR hΔ CyRel.args
          have heqaX : _ = resa := heqa; rw [← heqaX] at hs
          exact ⟨_, Step.callArgsHalt hs, rfl⟩
  | .argsNil =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | args => exact ⟨_, Step.argsNil, rfl⟩
  | .argsCons hrest he =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | args =>
          obtain ⟨res₁, hs₁, heq₁⟩ := cy_bwd hrest hR hΔ CyRel.args
          have heq₁X : _ = res₁ := heq₁; rw [← heq₁X] at hs₁
          obtain ⟨res₂', hs₂, heq₂⟩ := cy_bwd he hR hΔ CyRel.expr
          have heq₂X : _ = res₂' := heq₂; rw [← heq₂X] at hs₂
          exact ⟨_, Step.argsCons hs₁ hs₂, rfl⟩
  | .argsRestHalt hrest =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | args =>
          obtain ⟨res₁, hs₁, heq₁⟩ := cy_bwd hrest hR hΔ CyRel.args
          have heq₁X : _ = res₁ := heq₁; rw [← heq₁X] at hs₁
          exact ⟨_, Step.argsRestHalt hs₁, rfl⟩
  | .argsHeadHalt hrest he =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | args =>
          obtain ⟨res₁, hs₁, heq₁⟩ := cy_bwd hrest hR hΔ CyRel.args
          have heq₁X : _ = res₁ := heq₁; rw [← heq₁X] at hs₁
          obtain ⟨res₂', hs₂, heq₂⟩ := cy_bwd he hR hΔ CyRel.expr
          have heq₂X : _ = res₂' := heq₂; rw [← heq₂X] at hs₂
          exact ⟨_, Step.argsHeadHalt hs₁ hs₂, rfl⟩
  | .funDef =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | funDefS hbrel => exact ⟨_, Step.funDef, rfl⟩
  | @Step.block _ _ funs V st body' Vb stb o hb =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | @blockS _ body _ hbrel =>
          have hcompat := CarryCompat.extend (calls := calls) (creates := creates) hΔ body
          have hfr := CyFunsRel.cons (calls := calls) (creates := creates)
            (cyScopeRel_of_block hbrel hcompat) hR
          obtain ⟨res₁, hs, hres⟩ := cy_bwd hb hfr hcompat hbrel
          cases hres with
          | refl => exact ⟨_, Step.block hs, rfl⟩
          | haltIns Zp V₁ _ =>
              have hb1 := Step.block (funs := funs₁) hs
              refine ⟨_, hb1, ?_⟩
              show Res.sres (restore V (Zp ++ V₁)) stb .halt = Res.sres (restore V V₁) stb .halt
              rw [restore_prefix_le (venvLen_mono hs rfl)]
  | .letZero =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | letS => exact ⟨_, Step.letZero, rfl⟩
  | .letVal he hlen =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | letS =>
          obtain ⟨res₁, hs, heq⟩ := cy_bwd he hR hΔ CyRel.expr
          have heqX : _ = res₁ := heq; rw [← heqX] at hs
          exact ⟨_, Step.letVal hs hlen, rfl⟩
  | .letHalt he =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | letS =>
          obtain ⟨res₁, hs, heq⟩ := cy_bwd he hR hΔ CyRel.expr
          have heqX : _ = res₁ := heq; rw [← heqX] at hs
          exact ⟨_, Step.letHalt hs, rfl⟩
  | .assignVal he hlen =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | assignS =>
          obtain ⟨res₁, hs, heq⟩ := cy_bwd he hR hΔ CyRel.expr
          have heqX : _ = res₁ := heq; rw [← heqX] at hs
          exact ⟨_, Step.assignVal hs hlen, rfl⟩
  | .assignHalt he =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | assignS =>
          obtain ⟨res₁, hs, heq⟩ := cy_bwd he hR hΔ CyRel.expr
          have heqX : _ = res₁ := heq; rw [← heqX] at hs
          exact ⟨_, Step.assignHalt hs, rfl⟩
  | .exprStmt he =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | exprStmtS =>
          obtain ⟨res₁, hs, heq⟩ := cy_bwd he hR hΔ CyRel.expr
          have heqX : _ = res₁ := heq; rw [← heqX] at hs
          exact ⟨_, Step.exprStmt hs, rfl⟩
  | .exprStmtHalt he =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | exprStmtS =>
          obtain ⟨res₁, hs, heq⟩ := cy_bwd he hR hΔ CyRel.expr
          have heqX : _ = res₁ := heq; rw [← heqX] at hs
          exact ⟨_, Step.exprStmtHalt hs, rfl⟩
  | .ifTrue hc hcv hbody =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | @condS _ _ body _ hbrel =>
          obtain ⟨res₁, hs₁, heq₁⟩ := cy_bwd hc hR hΔ CyRel.expr
          have heq₁X : _ = res₁ := heq₁; rw [← heq₁X] at hs₁
          obtain ⟨res₂', hs₂, heq₂⟩ := cy_bwd hbody hR hΔ (CyRel.blockS hbrel)
          have heq₂X : _ = res₂' := heq₂; rw [← heq₂X] at hs₂
          exact ⟨_, Step.ifTrue hs₁ hcv hs₂, rfl⟩
  | .ifFalse hc hcv =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | condS hbrel =>
          obtain ⟨res₁, hs₁, heq₁⟩ := cy_bwd hc hR hΔ CyRel.expr
          have heq₁X : _ = res₁ := heq₁; rw [← heq₁X] at hs₁
          exact ⟨_, Step.ifFalse hs₁ hcv, rfl⟩
  | .ifHalt hc =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | condS hbrel =>
          obtain ⟨res₁, hs₁, heq₁⟩ := cy_bwd hc hR hΔ CyRel.expr
          have heq₁X : _ = res₁ := heq₁; rw [← heq₁X] at hs₁
          exact ⟨_, Step.ifHalt hs₁, rfl⟩
  | .switchExec hc hsel =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | switchS hcs hd =>
          obtain ⟨res₁, hs₁, heq₁⟩ := cy_bwd hc hR hΔ CyRel.expr
          have heq₁X : _ = res₁ := heq₁; rw [← heq₁X] at hs₁
          obtain ⟨res₂', hs₂, heq₂⟩ := cy_bwd hsel hR hΔ (CyRel.selectRel hcs hd _)
          have heq₂X : _ = res₂' := heq₂; rw [← heq₂X] at hs₂
          exact ⟨_, Step.switchExec hs₁ hs₂, rfl⟩
  | .switchHalt hc =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | switchS hcs hd =>
          obtain ⟨res₁, hs₁, heq₁⟩ := cy_bwd hc hR hΔ CyRel.expr
          have heq₁X : _ = res₁ := heq₁; rw [← heq₁X] at hs₁
          exact ⟨_, Step.switchHalt hs₁, rfl⟩
  | @Step.forLoop _ _ funs V st init c post' body' Vinit stinit Vend stend o hinit hloop =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | @forS _ _ _ post _ body _ hpost hbody =>
          have hfr := CyFunsRel.cons (calls := calls) (creates := creates)
            (cyScopeRel_refl (hoist D init :: funs₁) (hoist D init)) hR
          obtain ⟨res₁, hs₁, hres₁⟩ := cy_bwd hinit hfr (CarryCompat.nil _)
            (CyRel.reflStmts [] init)
          cases hres₁ with
          | refl =>
              obtain ⟨res₂', hs₂, heq₂⟩ := cy_bwd hloop hfr (CarryCompat.pruneInit hΔ init)
                (CyRel.loopL hpost hbody)
              have heq₂X : _ = res₂' := heq₂; rw [← heq₂X] at hs₂
              exact ⟨_, Step.forLoop hs₁ hs₂, rfl⟩
  | @Step.forInitHalt _ _ funs V st init c post' body' Vinit stinit hinit =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | @forS _ _ _ post _ body _ hpost hbody =>
          have hfr := CyFunsRel.cons (calls := calls) (creates := creates)
            (cyScopeRel_refl (hoist D init :: funs₁) (hoist D init)) hR
          obtain ⟨res₁, hs₁, hres₁⟩ := cy_bwd hinit hfr (CarryCompat.nil _)
            (CyRel.reflStmts [] init)
          cases hres₁ with
          | refl => exact ⟨_, Step.forInitHalt hs₁, rfl⟩
          | haltIns Zp V₁ _ =>
              have hb1 := Step.forInitHalt (c := c) (post := post) (body := body)
                (funs := funs₁) hs₁
              refine ⟨_, hb1, ?_⟩
              show Res.sres (restore V (Zp ++ V₁)) stinit .halt =
                Res.sres (restore V V₁) stinit .halt
              rw [restore_prefix_le (venvLen_mono hs₁ rfl)]
  | .«break» =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | breakS => exact ⟨_, Step.break, rfl⟩
  | .«continue» =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | continueS => exact ⟨_, Step.continue, rfl⟩
  | .«leave» =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | leaveS => exact ⟨_, Step.leave, rfl⟩
  | .seqNil =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | nilSS => exact ⟨_, Step.seqNil, .refl _⟩
  | @Step.seqCons _ _ _ V st s₂ rest₂ V1 st1 V2 st2 o hs hrest =>
      intro funs₁ Δ pc hR hΔ hrel
      rcases cyRel_stmts_cons_inv_bwd hrel with
        ⟨s, rest, rfl, hsrel, hrestrel⟩
        | ⟨f, d, xs, as, rest, hpc, hs₂eq, hld, hnd, hsc, hok, hsiteA⟩
        | ⟨f, d, xs, as, rest, hpc, hs₂eq, hld, hnd, hsc, hok, hrestrel⟩
        | ⟨f, d, as, rest, hpc, hs₂eq, hld, hnd, hsc, hok, hrestrel⟩
      · obtain ⟨res₁, hs₁, heq₁⟩ := cy_bwd hs hR hΔ hsrel
        have heq₁X : _ = res₁ := heq₁; rw [← heq₁X] at hs₁
        obtain ⟨res₂', hs₂, hres₂⟩ := cy_bwd hrest hR hΔ hrestrel
        cases hres₂ with
        | refl => exact ⟨_, Step.seqCons hs₁ hs₂, .refl _⟩
        | haltIns Zp => exact ⟨_, Step.seqCons hs₁ hs₂, .haltIns _ _ _⟩
      · -- siteLet, seqCons: thin wrapper — after letZero re-relate the tail to
        -- the assign-form site, then convert the source assign run to let form.
        subst hpc
        obtain ⟨hlen_as, hlen_xs, hxnd, hnc, hsh, hxout, hxlet⟩ := siteOK_inv hok
        have hVst : (Res.sres V1 st1 Outcome.normal) =
            .sres (bindZeros D xs ++ V) st .normal := letZero_inv (hs₂eq ▸ hs)
        simp only [Res.sres.injEq] at hVst
        obtain ⟨hV1eq, hst1eq, -⟩ := hVst
        obtain ⟨res₁', hs₁', hres'⟩ := cy_bwd hrest hR hΔ hsiteA
        rw [hV1eq, hst1eq] at hs₁'
        have hNx : ∀ y ∈ varsList as, y ∉ (bindZeros D xs).map Prod.fst := by
          intro y hy; rw [bindZeros_keys]; exact hxlet rfl y hy
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
                  | refl => exact ⟨_, Step.seqCons hlet htail₁, .refl _⟩
                  | haltIns Zp => exact ⟨_, Step.seqCons hlet htail₁, .haltIns _ _ _⟩
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
                      rw [show Zp ++ (bindZeros D xs ++ V) =
                        (Zp ++ bindZeros D xs) ++ V from
                        (List.append_assoc _ _ _).symm]
                      exact .haltIns (Zp ++ bindZeros D xs) _ _
      · -- siteAssign, seqCons
        subst hpc
        obtain ⟨hlen_as, hlen_xs, hxnd, hnc, hsh, hxout, -⟩ := siteOK_inv hok
        obtain ⟨body₀, cenv₀, hlk₀X, hb₀X, hagbody⟩ := hΔ (f, d) (lookupDelta_mem hld)
        have hlk₀ : lookupFun funs₁ f = some (⟨d.ps, d.rs, body₀⟩, cenv₀) := hlk₀X
        have hb₀ : body₀ = d.ss ∨ body₀ = d.ss ++ [.leave] := hb₀X
        have hZv : ∀ y ∈ varsList as, y ∉ (([] : VEnv D)).map Prod.fst := by
          intro y hy; simp
        rcases peelBody hs (List.nil_append V).symm (by rw [hs₂eq]) hsc hlen_as hnc hsh hxout hlen_xs hZv
            funs₁ cenv₀ hagbody hR
          with ⟨argvals, st1', Vend, strp, hargs, hbody, hEq⟩
            | ⟨argvals, st1', Vend, strp, hargs, hbody, hEq⟩
            | ⟨strp, hargs, hEq⟩
        · obtain ⟨oc, hbody', hoc⟩ := body_denormalize_ok hb₀ hbody
          simp only [List.nil_append] at hEq
          injection hEq with hV1 hst1
          have hcall : Step D funs₁ V st (.expr (.call f as))
              (.eres (.vals (d.rs.map (fun r => (VEnv.get Vend r).getD
                (evmWithExternal calls creates).zero)) strp)) := by
            refine Step.callOk hargs hlk₀ ?_ hbody' hoc
            show argvals.length = d.ps.length
            have := args_length hargs; omega
          have hassign : Step D funs₁ V st (.stmt (.assign xs (.call f as)))
              (.sres (VEnv.setMany V xs (d.rs.map (fun r => (VEnv.get Vend r).getD
                (evmWithExternal calls creates).zero))) strp .normal) :=
            Step.assignVal hcall (by simp only [List.length_map]; omega)
          obtain ⟨res₂', hs₂', hres₂⟩ := cy_bwd hrest hR hΔ hrestrel
          rw [hV1, hst1] at hs₂'
          cases hres₂ with
          | refl => exact ⟨_, Step.seqCons hassign hs₂', .refl _⟩
          | haltIns Zp => exact ⟨_, Step.seqCons hassign hs₂', .haltIns _ _ _⟩
        · injection hEq with _ _ ho; exact absurd ho (by simp)
        · injection hEq with _ _ ho; exact absurd ho (by simp)
      · -- siteExpr, seqCons
        subst hpc
        obtain ⟨hlen_as, hlen_xs, -, hnc, hsh, -, -⟩ := siteOK_inv hok
        obtain ⟨body₀, cenv₀, hlk₀X, hb₀X, hagbody⟩ := hΔ (f, d) (lookupDelta_mem hld)
        have hlk₀ : lookupFun funs₁ f = some (⟨d.ps, d.rs, body₀⟩, cenv₀) := hlk₀X
        have hb₀ : body₀ = d.ss ∨ body₀ = d.ss ++ [.leave] := hb₀X
        have hrs0 : d.rs = [] := by
          cases hrs : d.rs with
          | nil => rfl
          | cons r rs' => rw [hrs] at hlen_xs; simp at hlen_xs
        have hZv : ∀ y ∈ varsList as, y ∉ (([] : VEnv D)).map Prod.fst := by
          intro y hy; simp
        rcases peelBody hs (List.nil_append V).symm (by rw [hs₂eq]) hsc hlen_as hnc hsh
            (fun x hx => by cases hx) hlen_xs hZv funs₁ cenv₀ hagbody hR
          with ⟨argvals, st1', Vend, strp, hargs, hbody, hEq⟩
            | ⟨argvals, st1', Vend, strp, hargs, hbody, hEq⟩
            | ⟨strp, hargs, hEq⟩
        · obtain ⟨oc, hbody', hoc⟩ := body_denormalize_ok hb₀ hbody
          injection hEq with hV1 hst1
          have hcall : Step D funs₁ V st (.expr (.call f as)) (.eres (.vals [] strp)) := by
            have hc := Step.callOk hargs hlk₀ (by
              show argvals.length = d.ps.length
              have := args_length hargs; omega) hbody' hoc
            rw [show (⟨d.ps, d.rs, body₀⟩ : FDecl D).rets = d.rs from rfl, hrs0] at hc
            exact hc
          have hstmt : Step D funs₁ V st (.stmt (.exprStmt (.call f as)))
              (.sres V strp .normal) := Step.exprStmt hcall
          have hV1' : V1 = V := by rw [hV1]; rfl
          obtain ⟨res₂', hs₂', hres₂⟩ := cy_bwd hrest hR hΔ hrestrel
          rw [hV1', hst1] at hs₂'
          cases hres₂ with
          | refl => exact ⟨_, Step.seqCons hstmt hs₂', .refl _⟩
          | haltIns Zp => exact ⟨_, Step.seqCons hstmt hs₂', .haltIns _ _ _⟩
        · injection hEq with _ _ ho; exact absurd ho (by simp)
        · injection hEq with _ _ ho; exact absurd ho (by simp)
  | @Step.seqStop _ _ _ V st s₂ rest₂ V1 st1 o hs hne =>
      intro funs₁ Δ pc hR hΔ hrel
      rcases cyRel_stmts_cons_inv_bwd hrel with
        ⟨s, rest, rfl, hsrel, hrestrel⟩
        | ⟨f, d, xs, as, rest, hpc, hs₂eq, hld, hnd, hsc, hok, hsiteA⟩
        | ⟨f, d, xs, as, rest, hpc, hs₂eq, hld, hnd, hsc, hok, hrestrel⟩
        | ⟨f, d, as, rest, hpc, hs₂eq, hld, hnd, hsc, hok, hrestrel⟩
      · obtain ⟨res₁, hs₁, heq₁⟩ := cy_bwd hs hR hΔ hsrel
        have heq₁X : _ = res₁ := heq₁; rw [← heq₁X] at hs₁
        exact ⟨_, Step.seqStop hs₁ hne, .refl _⟩
      · rw [hs₂eq] at hs; cases hs; exact absurd rfl hne
      · -- siteAssign, seqStop
        subst hpc
        obtain ⟨hlen_as, hlen_xs, hxnd, hnc, hsh, hxout, -⟩ := siteOK_inv hok
        obtain ⟨body₀, cenv₀, hlk₀X, hb₀X, hagbody⟩ := hΔ (f, d) (lookupDelta_mem hld)
        have hlk₀ : lookupFun funs₁ f = some (⟨d.ps, d.rs, body₀⟩, cenv₀) := hlk₀X
        have hb₀ : body₀ = d.ss ∨ body₀ = d.ss ++ [.leave] := hb₀X
        have hZv : ∀ y ∈ varsList as, y ∉ (([] : VEnv D)).map Prod.fst := by
          intro y hy; simp
        rcases peelBody hs (List.nil_append V).symm (by rw [hs₂eq]) hsc hlen_as hnc hsh hxout hlen_xs hZv
            funs₁ cenv₀ hagbody hR
          with ⟨argvals, st1', Vend, strp, hargs, hbody, hEq⟩
            | ⟨argvals, st1', Vend, strp, hargs, hbody, hEq⟩
            | ⟨strp, hargs, hEq⟩
        · injection hEq with _ _ ho; exact absurd ho hne
        · have hbody' := body_denormalize_halt hb₀ hbody
          injection hEq with hV1 hst1 ho
          have hcall : Step D funs₁ V st (.expr (.call f as)) (.eres (.halt strp)) := by
            refine Step.callHalt hargs hlk₀ ?_ hbody'
            show argvals.length = d.ps.length
            have := args_length hargs; omega
          subst hV1 hst1 ho
          exact ⟨_, Step.seqStop (Step.assignHalt hcall) (by simp), .refl _⟩
        · injection hEq with hV1 hst1 ho
          have hcall : Step D funs₁ V st (.expr (.call f as)) (.eres (.halt strp)) :=
            Step.callArgsHalt hargs
          subst hV1 hst1 ho
          exact ⟨_, Step.seqStop (Step.assignHalt hcall) (by simp), .refl _⟩
      · -- siteExpr, seqStop
        subst hpc
        obtain ⟨hlen_as, hlen_xs, -, hnc, hsh, -, -⟩ := siteOK_inv hok
        obtain ⟨body₀, cenv₀, hlk₀X, hb₀X, hagbody⟩ := hΔ (f, d) (lookupDelta_mem hld)
        have hlk₀ : lookupFun funs₁ f = some (⟨d.ps, d.rs, body₀⟩, cenv₀) := hlk₀X
        have hb₀ : body₀ = d.ss ∨ body₀ = d.ss ++ [.leave] := hb₀X
        have hZv : ∀ y ∈ varsList as, y ∉ (([] : VEnv D)).map Prod.fst := by
          intro y hy; simp
        rcases peelBody hs (List.nil_append V).symm (by rw [hs₂eq]) hsc hlen_as hnc hsh
            (fun x hx => by cases hx) hlen_xs hZv funs₁ cenv₀ hagbody hR
          with ⟨argvals, st1', Vend, strp, hargs, hbody, hEq⟩
            | ⟨argvals, st1', Vend, strp, hargs, hbody, hEq⟩
            | ⟨strp, hargs, hEq⟩
        · injection hEq with _ _ ho; exact absurd ho hne
        · have hbody' := body_denormalize_halt hb₀ hbody
          injection hEq with hV1 hst1 ho
          have hcall : Step D funs₁ V st (.expr (.call f as)) (.eres (.halt strp)) := by
            refine Step.callHalt hargs hlk₀ ?_ hbody'
            show argvals.length = d.ps.length
            have := args_length hargs; omega
          subst hV1 hst1 ho
          exact ⟨_, Step.seqStop (Step.exprStmtHalt hcall) (by simp), .refl _⟩
        · injection hEq with hV1 hst1 ho
          have hcall : Step D funs₁ V st (.expr (.call f as)) (.eres (.halt strp)) :=
            Step.callArgsHalt hargs
          subst hV1 hst1 ho
          exact ⟨_, Step.seqStop (Step.exprStmtHalt hcall) (by simp), .refl _⟩
  | .loopDone hc hcz =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | loopL hpost hbody =>
          obtain ⟨res₁, hs₁, heq₁⟩ := cy_bwd hc hR hΔ CyRel.expr
          have heq₁X : _ = res₁ := heq₁; rw [← heq₁X] at hs₁
          exact ⟨_, Step.loopDone hs₁ hcz, rfl⟩
  | .loopCondHalt hc =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | loopL hpost hbody =>
          obtain ⟨res₁, hs₁, heq₁⟩ := cy_bwd hc hR hΔ CyRel.expr
          have heq₁X : _ = res₁ := heq₁; rw [← heq₁X] at hs₁
          exact ⟨_, Step.loopCondHalt hs₁, rfl⟩
  | .loopStep hc hcv hbody hob hpost hnext =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | @loopL _ _ post _ body _ hpostrel hbodyrel =>
          obtain ⟨res₁, hs₁, heq₁⟩ := cy_bwd hc hR hΔ CyRel.expr
          have heq₁X : _ = res₁ := heq₁; rw [← heq₁X] at hs₁
          obtain ⟨res₂', hs₂, heq₂⟩ := cy_bwd hbody hR hΔ (CyRel.blockS hbodyrel)
          have heq₂X : _ = res₂' := heq₂; rw [← heq₂X] at hs₂
          obtain ⟨res₃, hs₃, heq₃⟩ := cy_bwd hpost hR hΔ (CyRel.blockS hpostrel)
          have heq₃X : _ = res₃ := heq₃; rw [← heq₃X] at hs₃
          obtain ⟨res₄, hs₄, heq₄⟩ := cy_bwd hnext hR hΔ (CyRel.loopL hpostrel hbodyrel)
          have heq₄X : _ = res₄ := heq₄; rw [← heq₄X] at hs₄
          exact ⟨_, Step.loopStep hs₁ hcv hs₂ hob hs₃ hs₄, rfl⟩
  | .loopPostHalt hc hcv hbody hob hpost =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | loopL hpostrel hbodyrel =>
          obtain ⟨res₁, hs₁, heq₁⟩ := cy_bwd hc hR hΔ CyRel.expr
          have heq₁X : _ = res₁ := heq₁; rw [← heq₁X] at hs₁
          obtain ⟨res₂', hs₂, heq₂⟩ := cy_bwd hbody hR hΔ (CyRel.blockS hbodyrel)
          have heq₂X : _ = res₂' := heq₂; rw [← heq₂X] at hs₂
          obtain ⟨res₃, hs₃, heq₃⟩ := cy_bwd hpost hR hΔ (CyRel.blockS hpostrel)
          have heq₃X : _ = res₃ := heq₃; rw [← heq₃X] at hs₃
          exact ⟨_, Step.loopPostHalt hs₁ hcv hs₂ hob hs₃, rfl⟩
  | .loopBreak hc hcv hbody =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | loopL hpostrel hbodyrel =>
          obtain ⟨res₁, hs₁, heq₁⟩ := cy_bwd hc hR hΔ CyRel.expr
          have heq₁X : _ = res₁ := heq₁; rw [← heq₁X] at hs₁
          obtain ⟨res₂', hs₂, heq₂⟩ := cy_bwd hbody hR hΔ (CyRel.blockS hbodyrel)
          have heq₂X : _ = res₂' := heq₂; rw [← heq₂X] at hs₂
          exact ⟨_, Step.loopBreak hs₁ hcv hs₂, rfl⟩
  | .loopLeave hc hcv hbody =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | loopL hpostrel hbodyrel =>
          obtain ⟨res₁, hs₁, heq₁⟩ := cy_bwd hc hR hΔ CyRel.expr
          have heq₁X : _ = res₁ := heq₁; rw [← heq₁X] at hs₁
          obtain ⟨res₂', hs₂, heq₂⟩ := cy_bwd hbody hR hΔ (CyRel.blockS hbodyrel)
          have heq₂X : _ = res₂' := heq₂; rw [← heq₂X] at hs₂
          exact ⟨_, Step.loopLeave hs₁ hcv hs₂, rfl⟩
  | .loopBodyHalt hc hcv hbody =>
      intro funs₁ Δ pc hR hΔ hrel; cases hrel with
      | loopL hpostrel hbodyrel =>
          obtain ⟨res₁, hs₁, heq₁⟩ := cy_bwd hc hR hΔ CyRel.expr
          have heq₁X : _ = res₁ := heq₁; rw [← heq₁X] at hs₁
          obtain ⟨res₂', hs₂, heq₂⟩ := cy_bwd hbody hR hΔ (CyRel.blockS hbodyrel)
          have heq₂X : _ = res₂' := heq₂; rw [← heq₂X] at hs₂
          exact ⟨_, Step.loopBodyHalt hs₁ hcv hs₂, rfl⟩
  termination_by structural h

/-- Callee-body backward transfer with call simulation. -/
theorem carry_body_bwd {funs₂ : FunEnv D} {V₂ : VEnv D} {st : EvmState}
    {code : Code Op} {res₂ : Res D} (h : Step D funs₂ V₂ st code res₂) :
    ∀ {A W' : VEnv D} {bound : List Ident} (cenv funs₁ : FunEnv D) (W : VEnv D),
      V₂ = A ++ W' → carryBodyCode bound code →
      (∀ x ∈ bound, x ∈ A.map Prod.fst) →
      FunsAgree (calls := calls) (creates := creates) cenv funs₁ (carryCallNames code) →
      CyFunsRel (calls := calls) (creates := creates) funs₁ funs₂ →
      ∃ res₁, Step D cenv (A ++ W) st code res₁ ∧
        TResL (calls := calls) (creates := creates) W W'
          (carryPostBound bound code) res₁ res₂ := by
  match h with
  | .lit =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      exact ⟨_, Step.lit, .eres _⟩
  | @Step.var _ _ _ _ _ x v hv =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      subst hV
      have hx : x ∈ bound := by
        have h2 : carryExpr bound (.var x) = true := hsc
        have := List.all_eq_true.mp h2 x (by simp [exprVars])
        simpa using this
      have hxA : x ∈ A.map Prod.fst := hb x hx
      have hgv : VEnv.get A x = some v := by
        rw [← VEnv.get_append_mem hxA W']; exact hv
      refine ⟨_, Step.var ?_, .eres _⟩
      rw [VEnv.get_append_mem hxA W]; exact hgv
  | @Step.builtinOk _ _ _ _ _ op args argvals st1 rets st2 ha hbi =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      have hargs : carryArgs bound args = true := carryExpr_builtin_args hsc
      obtain ⟨res₁, hstep, htr⟩ := carry_body_bwd ha cenv funs₁ W hV
        (by simpa [carryBodyCode, carryCode] using hargs) hb
        (by simpa [carryCallNames, exprCallNames] using hag) hR
      subst hV
      cases htr with
      | eres => exact ⟨_, Step.builtinOk hstep hbi, .eres _⟩
  | @Step.builtinHalt _ _ _ _ _ op args argvals st1 st2 ha hbi =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      have hargs : carryArgs bound args = true := carryExpr_builtin_args hsc
      obtain ⟨res₁, hstep, htr⟩ := carry_body_bwd ha cenv funs₁ W hV
        (by simpa [carryBodyCode, carryCode] using hargs) hb
        (by simpa [carryCallNames, exprCallNames] using hag) hR
      subst hV
      cases htr with
      | eres => exact ⟨_, Step.builtinHalt hstep hbi, .eres _⟩
  | @Step.builtinArgsHalt _ _ _ _ _ op args st1 ha =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      have hargs : carryArgs bound args = true := carryExpr_builtin_args hsc
      obtain ⟨res₁, hstep, htr⟩ := carry_body_bwd ha cenv funs₁ W hV
        (by simpa [carryBodyCode, carryCode] using hargs) hb
        (by simpa [carryCallNames, exprCallNames] using hag) hR
      subst hV
      cases htr with
      | eres => exact ⟨_, Step.builtinArgsHalt hstep, .eres _⟩
  | @Step.callOk _ _ _ _ _ fn args argvals st1 decl cenv_c Vend st2 o ha hlk harity hbody ho =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      have hargs : carryArgs bound args = true := carryExpr_call_args hsc
      obtain ⟨res₁, hstep, htr⟩ := carry_body_bwd ha cenv funs₁ W hV
        (by simpa [carryBodyCode, carryCode] using hargs) hb
        (by refine hag.mono ?_; intro y hy;
            show y ∈ carryCallNames (Code.expr (.call fn args));
            simp only [carryCallNames, exprCallNames];
            exact List.mem_cons_of_mem fn (by simpa [carryCallNames] using hy)) hR
      subst hV
      cases htr with
      | eres =>
          have hagfn : lookupFun cenv fn = lookupFun funs₁ fn :=
            hag fn (by simp [carryCallNames, exprCallNames])
          obtain ⟨decl₁, cenv₁, hlk₁, hdecl, hcenvR⟩ := lookupFun_cyFunsRel_bwd hR hlk
          rw [← hagfn] at hlk₁
          obtain ⟨hps, hrs, Δf, hΔf, hbrel⟩ := hdecl
          obtain ⟨resb, hsb, heqb⟩ := cy_bwd hbody hcenvR hΔf (CyRel.blockS hbrel)
          have heqbX : _ = resb := heqb; rw [← heqbX] at hsb
          have hsb' : Step D cenv₁ (decl₁.params.zip argvals ++ bindZeros D decl₁.rets)
              st1 (.stmt (.block decl₁.body)) (.sres Vend st2 o) := by
            rw [hps, hrs]; exact hsb
          have harity' : argvals.length = decl₁.params.length := by rw [hps]; exact harity
          refine ⟨_, Step.callOk hstep hlk₁ harity' hsb' ho, ?_⟩
          rw [hrs]; exact .eres _
  | @Step.callHalt _ _ _ _ _ fn args argvals st1 decl cenv_c Vend st2 ha hlk harity hbody =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      have hargs : carryArgs bound args = true := carryExpr_call_args hsc
      obtain ⟨res₁, hstep, htr⟩ := carry_body_bwd ha cenv funs₁ W hV
        (by simpa [carryBodyCode, carryCode] using hargs) hb
        (by refine hag.mono ?_; intro y hy;
            show y ∈ carryCallNames (Code.expr (.call fn args));
            simp only [carryCallNames, exprCallNames];
            exact List.mem_cons_of_mem fn (by simpa [carryCallNames] using hy)) hR
      subst hV
      cases htr with
      | eres =>
          have hagfn : lookupFun cenv fn = lookupFun funs₁ fn :=
            hag fn (by simp [carryCallNames, exprCallNames])
          obtain ⟨decl₁, cenv₁, hlk₁, hdecl, hcenvR⟩ := lookupFun_cyFunsRel_bwd hR hlk
          rw [← hagfn] at hlk₁
          obtain ⟨hps, hrs, Δf, hΔf, hbrel⟩ := hdecl
          obtain ⟨resb, hsb, heqb⟩ := cy_bwd hbody hcenvR hΔf (CyRel.blockS hbrel)
          have heqbX : _ = resb := heqb; rw [← heqbX] at hsb
          have hsb' : Step D cenv₁ (decl₁.params.zip argvals ++ bindZeros D decl₁.rets)
              st1 (.stmt (.block decl₁.body)) (.sres Vend st2 .halt) := by
            rw [hps, hrs]; exact hsb
          have harity' : argvals.length = decl₁.params.length := by rw [hps]; exact harity
          exact ⟨_, Step.callHalt hstep hlk₁ harity' hsb', .eres _⟩
  | @Step.callArgsHalt _ _ _ _ _ fn args st1 ha =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      have hargs : carryArgs bound args = true := carryExpr_call_args hsc
      obtain ⟨res₁, hstep, htr⟩ := carry_body_bwd ha cenv funs₁ W hV
        (by simpa [carryBodyCode, carryCode] using hargs) hb
        (by refine hag.mono ?_; intro y hy;
            show y ∈ carryCallNames (Code.expr (.call fn args));
            simp only [carryCallNames, exprCallNames];
            exact List.mem_cons_of_mem fn (by simpa [carryCallNames] using hy)) hR
      subst hV
      cases htr with
      | eres => exact ⟨_, Step.callArgsHalt hstep, .eres _⟩
  | .argsNil =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      exact ⟨_, Step.argsNil, .eres _⟩
  | @Step.argsCons _ _ _ _ _ e rest restvals st1 v st2 hrest he =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      have hsc2 : (carryExpr bound e && carryArgs bound rest) = true := hsc
      rw [Bool.and_eq_true] at hsc2
      have hagE : FunsAgree (calls := calls) (creates := creates) cenv funs₁ (exprCallNames e) :=
        hag.mono (fun y hy => by
          show y ∈ argsCallNames (e :: rest); exact List.mem_append.mpr (Or.inl hy))
      have hagR : FunsAgree (calls := calls) (creates := creates) cenv funs₁ (argsCallNames rest) :=
        hag.mono (fun y hy => by
          show y ∈ argsCallNames (e :: rest); exact List.mem_append.mpr (Or.inr hy))
      obtain ⟨res₁, hstep₁, htr₁⟩ := carry_body_bwd hrest cenv funs₁ W hV
        (by simpa [carryBodyCode, carryCode] using hsc2.2) hb
        (by simpa [carryCallNames] using hagR) hR
      obtain ⟨res₃, hstep₂, htr₂⟩ := carry_body_bwd he cenv funs₁ W hV
        (by simpa [carryBodyCode, carryCode] using hsc2.1) hb
        (by simpa [carryCallNames] using hagE) hR
      cases htr₁ with
      | eres => cases htr₂ with
        | eres => exact ⟨_, Step.argsCons hstep₁ hstep₂, .eres _⟩
  | @Step.argsRestHalt _ _ _ _ _ e rest st1 hrest =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      have hsc2 : (carryExpr bound e && carryArgs bound rest) = true := hsc
      rw [Bool.and_eq_true] at hsc2
      have hagR : FunsAgree (calls := calls) (creates := creates) cenv funs₁ (argsCallNames rest) :=
        hag.mono (fun y hy => by
          show y ∈ argsCallNames (e :: rest); exact List.mem_append.mpr (Or.inr hy))
      obtain ⟨res₁, hstep₁, htr₁⟩ := carry_body_bwd hrest cenv funs₁ W hV
        (by simpa [carryBodyCode, carryCode] using hsc2.2) hb
        (by simpa [carryCallNames] using hagR) hR
      cases htr₁ with
      | eres => exact ⟨_, Step.argsRestHalt hstep₁, .eres _⟩
  | @Step.argsHeadHalt _ _ _ _ _ e rest restvals st1 st2 hrest he =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      have hsc2 : (carryExpr bound e && carryArgs bound rest) = true := hsc
      rw [Bool.and_eq_true] at hsc2
      have hagE : FunsAgree (calls := calls) (creates := creates) cenv funs₁ (exprCallNames e) :=
        hag.mono (fun y hy => by
          show y ∈ argsCallNames (e :: rest); exact List.mem_append.mpr (Or.inl hy))
      have hagR : FunsAgree (calls := calls) (creates := creates) cenv funs₁ (argsCallNames rest) :=
        hag.mono (fun y hy => by
          show y ∈ argsCallNames (e :: rest); exact List.mem_append.mpr (Or.inr hy))
      obtain ⟨res₁, hstep₁, htr₁⟩ := carry_body_bwd hrest cenv funs₁ W hV
        (by simpa [carryBodyCode, carryCode] using hsc2.2) hb
        (by simpa [carryCallNames] using hagR) hR
      obtain ⟨res₃, hstep₂, htr₂⟩ := carry_body_bwd he cenv funs₁ W hV
        (by simpa [carryBodyCode, carryCode] using hsc2.1) hb
        (by simpa [carryCallNames] using hagE) hR
      cases htr₁ with
      | eres => cases htr₂ with
        | eres => exact ⟨_, Step.argsHeadHalt hstep₁ hstep₂, .eres _⟩
  | .funDef =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      exact absurd hsc (by simp [carryBodyCode, carryCode, carryStmt])
  | @Step.block _ _ _ _ _ body Vb stb o hbody =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      have hstmts : carryLeaveStmts bound body := hsc
      have hpost : carryPostBound bound (Code.stmt (.block body)) = bound :=
        carryPostBound_block bound body
      have hhoist : hoist D body = [] := carryLeaveStmts_hoist_nil hstmts
      have hagb : FunsAgree (calls := calls) (creates := creates)
          (hoist D body :: cenv) (hoist D body :: funs₁) (carryCallNames (.stmts body)) := by
        rw [hhoist]
        exact FunsAgree.cons_nil (by simpa [carryCallNames, stmtCallNames] using hag)
      have hRb : CyFunsRel (calls := calls) (creates := creates)
          (hoist D body :: funs₁) (hoist D body :: funs₂) := by
        rw [hhoist]; exact CyFunsRel.cons_nil hR
      obtain ⟨res₁, hstep, htr⟩ :=
        carry_body_bwd hbody (hoist D body :: cenv) (hoist D body :: funs₁) W hV
          hstmts hb hagb hRb
      have hlenV : V₂.length ≤ Vb.length := venvLen_mono hbody rfl
      have hkeysV := venvKeys_suffix hbody rfl
      subst hV
      cases htr with
      | @norm A' st' hk =>
          have hlen : A.length ≤ A'.length := by
            rw [List.length_append, List.length_append] at hlenV; omega
          refine ⟨_, Step.block hstep, ?_⟩
          rw [hpost, restore_append hlen, restore_append hlen]
          exact .norm (fun x hx => by
            rw [restore_keys (keys_suffix_cancel hkeysV) hlen]; exact hb x hx)
      | @halt A' st' =>
          have hlen : A.length ≤ A'.length := by
            rw [List.length_append, List.length_append] at hlenV; omega
          refine ⟨_, Step.block hstep, ?_⟩
          rw [restore_append hlen, restore_append hlen]; exact .halt
      | @«leave» A' st' =>
          have hlen : A.length ≤ A'.length := by
            rw [List.length_append, List.length_append] at hlenV; omega
          refine ⟨_, Step.block hstep, ?_⟩
          rw [restore_append hlen, restore_append hlen]; exact TResL.leave
  | @Step.letZero _ _ _ _ _ vars =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
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
  | @Step.letVal _ _ _ _ _ vars e vals st1 he hlen =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      have hse : carryExpr bound e = true := by
        have h2 : (carryStmt bound (.letDecl vars (some e))).isSome = true := hsc
        by_cases hc : carryExpr bound e = true
        · exact hc
        · simp [carryStmt, hc] at h2
      obtain ⟨res₁, hstep, htr⟩ := carry_body_bwd he cenv funs₁ W hV
        (by simpa [carryBodyCode, carryCode] using hse) hb
        (by simpa [carryCallNames, stmtCallNames] using hag) hR
      subst hV
      cases htr with
      | eres =>
          refine ⟨_, Step.letVal hstep hlen, ?_⟩
          rw [show vars.zip vals ++ (A ++ W) = (vars.zip vals ++ A) ++ W from
                (List.append_assoc _ _ _).symm,
              show vars.zip vals ++ (A ++ W') = (vars.zip vals ++ A) ++ W' from
                (List.append_assoc _ _ _).symm]
          refine .norm (fun x hx => ?_)
          have hpost : carryPostBound bound (Code.stmt (.letDecl vars (some e))) =
              vars ++ bound := by simp [carryPostBound, carryStmt, hse]
          rw [hpost] at hx
          rw [List.map_append, List.map_fst_zip (by omega)]
          rcases List.mem_append.mp hx with hx | hx
          · exact List.mem_append.mpr (Or.inl hx)
          · exact List.mem_append.mpr (Or.inr (hb x hx))
  | @Step.letHalt _ _ _ _ _ vars e st1 he =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      have hse : carryExpr bound e = true := by
        have h2 : (carryStmt bound (.letDecl vars (some e))).isSome = true := hsc
        by_cases hc : carryExpr bound e = true
        · exact hc
        · simp [carryStmt, hc] at h2
      obtain ⟨res₁, hstep, htr⟩ := carry_body_bwd he cenv funs₁ W hV
        (by simpa [carryBodyCode, carryCode] using hse) hb
        (by simpa [carryCallNames, stmtCallNames] using hag) hR
      subst hV
      cases htr with
      | eres => exact ⟨_, Step.letHalt hstep, .halt⟩
  | @Step.assignVal _ _ _ _ _ vars e vals st1 he hlen =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      have hsc' : vars.all bound.contains = true ∧ carryExpr bound e = true := by
        have h2 : (carryStmt bound (.assign vars e)).isSome = true := hsc
        by_cases hc : (vars.all bound.contains && carryExpr bound e) = true
        · rw [Bool.and_eq_true] at hc; exact hc
        · simp [carryStmt, hc] at h2
      have hvars : ∀ x ∈ vars, x ∈ A.map Prod.fst := fun x hx =>
        hb x (all_contains_subset hsc'.1 x hx)
      obtain ⟨res₁, hstep, htr⟩ := carry_body_bwd he cenv funs₁ W hV
        (by simpa [carryBodyCode, carryCode] using hsc'.2) hb
        (by simpa [carryCallNames, stmtCallNames] using hag) hR
      subst hV
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
  | @Step.assignHalt _ _ _ _ _ vars e st1 he =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      have hse : carryExpr bound e = true := by
        have h2 : (carryStmt bound (.assign vars e)).isSome = true := hsc
        by_cases hc : (vars.all bound.contains && carryExpr bound e) = true
        · rw [Bool.and_eq_true] at hc; exact hc.2
        · simp [carryStmt, hc] at h2
      obtain ⟨res₁, hstep, htr⟩ := carry_body_bwd he cenv funs₁ W hV
        (by simpa [carryBodyCode, carryCode] using hse) hb
        (by simpa [carryCallNames, stmtCallNames] using hag) hR
      subst hV
      cases htr with
      | eres => exact ⟨_, Step.assignHalt hstep, .halt⟩
  | @Step.exprStmt _ _ _ _ _ e st1 he =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      have hse : carryExpr bound e = true := by
        have h2 : (carryStmt bound (.exprStmt e)).isSome = true := hsc
        by_cases hc : carryExpr bound e = true
        · exact hc
        · simp [carryStmt, hc] at h2
      obtain ⟨res₁, hstep, htr⟩ := carry_body_bwd he cenv funs₁ W hV
        (by simpa [carryBodyCode, carryCode] using hse) hb
        (by simpa [carryCallNames, stmtCallNames] using hag) hR
      subst hV
      cases htr with
      | eres =>
          refine ⟨_, Step.exprStmt hstep, ?_⟩
          refine .norm (fun x hx => ?_)
          have hpost : carryPostBound bound (Code.stmt (.exprStmt e)) = bound := by
            simp [carryPostBound, carryStmt, hse]
          rw [hpost] at hx
          exact hb x hx
  | @Step.exprStmtHalt _ _ _ _ _ e st1 he =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      have hse : carryExpr bound e = true := by
        have h2 : (carryStmt bound (.exprStmt e)).isSome = true := hsc
        by_cases hc : carryExpr bound e = true
        · exact hc
        · simp [carryStmt, hc] at h2
      obtain ⟨res₁, hstep, htr⟩ := carry_body_bwd he cenv funs₁ W hV
        (by simpa [carryBodyCode, carryCode] using hse) hb
        (by simpa [carryCallNames, stmtCallNames] using hag) hR
      subst hV
      cases htr with
      | eres => exact ⟨_, Step.exprStmtHalt hstep, .halt⟩
  | @Step.ifTrue _ _ _ _ _ c body cv st1 V' st2 o hc hcv hbody =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      have hsc' : carryExpr bound c = true ∧ carryStmts bound body = true := by
        have h2 : (carryStmt bound (.cond c body)).isSome = true := hsc
        by_cases hcnd : (carryExpr bound c && carryStmts bound body) = true
        · rw [Bool.and_eq_true] at hcnd; exact hcnd
        · simp [carryStmt, hcnd] at h2
      have hagc : FunsAgree (calls := calls) (creates := creates) cenv funs₁ (exprCallNames c) :=
        hag.mono (fun y hy => by
          show y ∈ stmtCallNames (.cond c body); exact List.mem_append.mpr (Or.inl hy))
      have hagb : FunsAgree (calls := calls) (creates := creates) cenv funs₁
          (carryCallNames (.stmt (.block body))) :=
        hag.mono (fun y hy => by
          show y ∈ stmtCallNames (.cond c body)
          exact List.mem_append.mpr (Or.inr (by simpa [carryCallNames, stmtCallNames] using hy)))
      obtain ⟨res₁, hstepc, htrc⟩ := carry_body_bwd hc cenv funs₁ W hV
        (by simpa [carryBodyCode, carryCode] using hsc'.1) hb hagc hR
      have hscb : carryBodyCode bound (Code.stmt (.block body)) := Or.inl hsc'.2
      obtain ⟨res₃, hstepb, htrb⟩ := carry_body_bwd hbody cenv funs₁ W hV hscb hb hagb hR
      subst hV
      cases htrc with
      | eres =>
          have hpostb : carryPostBound bound (Code.stmt (.block body)) = bound :=
            carryPostBound_block bound body
          have hpost : carryPostBound bound (Code.stmt (.cond c body)) = bound := by
            simp [carryPostBound, carryStmt, hsc'.1, hsc'.2]
          rw [hpostb] at htrb
          rw [hpost]
          cases htrb with
          | norm hk => exact ⟨_, Step.ifTrue hstepc hcv hstepb, .norm hk⟩
          | halt => exact ⟨_, Step.ifTrue hstepc hcv hstepb, .halt⟩
          | «leave» => exact ⟨_, Step.ifTrue hstepc hcv hstepb, TResL.leave⟩
  | @Step.ifFalse _ _ _ _ _ c body cv st1 hc hcv =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      have hsc' : carryExpr bound c = true := by
        have h2 : (carryStmt bound (.cond c body)).isSome = true := hsc
        by_cases hcnd : (carryExpr bound c && carryStmts bound body) = true
        · rw [Bool.and_eq_true] at hcnd; exact hcnd.1
        · simp [carryStmt, hcnd] at h2
      have hagc : FunsAgree (calls := calls) (creates := creates) cenv funs₁ (exprCallNames c) :=
        hag.mono (fun y hy => by
          show y ∈ stmtCallNames (.cond c body); exact List.mem_append.mpr (Or.inl hy))
      obtain ⟨res₁, hstepc, htrc⟩ := carry_body_bwd hc cenv funs₁ W hV
        (by simpa [carryBodyCode, carryCode] using hsc') hb hagc hR
      subst hV
      cases htrc with
      | eres =>
          refine ⟨_, Step.ifFalse hstepc hcv, .norm (fun x hx => ?_)⟩
          exact hb x (by
            have : carryPostBound bound (Code.stmt (.cond c body)) = bound := by
              simp only [carryPostBound, carryStmt]; split <;> rfl
            rwa [this] at hx)
  | @Step.ifHalt _ _ _ _ _ c body st1 hc =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      have hsc' : carryExpr bound c = true := by
        have h2 : (carryStmt bound (.cond c body)).isSome = true := hsc
        by_cases hcnd : (carryExpr bound c && carryStmts bound body) = true
        · rw [Bool.and_eq_true] at hcnd; exact hcnd.1
        · simp [carryStmt, hcnd] at h2
      have hagc : FunsAgree (calls := calls) (creates := creates) cenv funs₁ (exprCallNames c) :=
        hag.mono (fun y hy => by
          show y ∈ stmtCallNames (.cond c body); exact List.mem_append.mpr (Or.inl hy))
      obtain ⟨res₁, hstepc, htrc⟩ := carry_body_bwd hc cenv funs₁ W hV
        (by simpa [carryBodyCode, carryCode] using hsc') hb hagc hR
      subst hV
      cases htrc with
      | eres => exact ⟨_, Step.ifHalt hstepc, .halt⟩
  | @Step.switchExec _ _ _ _ _ c cases' dflt cv st1 V' st2 o hc hsel =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      have hsc' : carryExpr bound c = true ∧ carryCases bound cases' = true ∧
          carryDflt bound dflt = true := by
        have h2 : (carryStmt bound (.switch c cases' dflt)).isSome = true := hsc
        by_cases hcnd : (carryExpr bound c && carryCases bound cases' &&
            carryDflt bound dflt) = true
        · rw [Bool.and_eq_true, Bool.and_eq_true] at hcnd; exact ⟨hcnd.1.1, hcnd.1.2, hcnd.2⟩
        · simp [carryStmt, hcnd] at h2
      have hagc : FunsAgree (calls := calls) (creates := creates) cenv funs₁ (exprCallNames c) :=
        hag.mono (fun y hy => by
          show y ∈ stmtCallNames (.switch c cases' dflt)
          exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hy))))
      have hagsel : FunsAgree (calls := calls) (creates := creates) cenv funs₁
          (carryCallNames (.stmt (.block (selectSwitch D cv cases' dflt)))) := by
        refine hag.mono (fun y hy => ?_)
        show y ∈ stmtCallNames (.switch c cases' dflt)
        have hsub := selectSwitch_callNames_sub (calls := calls) (creates := creates)
          (cv := cv) (cases := cases') (dflt := dflt) y
          (by simpa [carryCallNames, stmtCallNames] using hy)
        rcases List.mem_append.mp hsub with hh | hh
        · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hh)))
        · exact List.mem_append.mpr (Or.inr hh)
      obtain ⟨res₁, hstepc, htrc⟩ := carry_body_bwd hc cenv funs₁ W hV
        (by simpa [carryBodyCode, carryCode] using hsc'.1) hb hagc hR
      have hsels : carryStmts bound (selectSwitch D cv cases' dflt) = true :=
        carry_selectSwitch hsc'.2.1 hsc'.2.2
      have hscb : carryBodyCode bound (Code.stmt (.block (selectSwitch D cv cases' dflt))) :=
        Or.inl hsels
      obtain ⟨res₃, hstepb, htrb⟩ := carry_body_bwd hsel cenv funs₁ W hV hscb hb hagsel hR
      subst hV
      cases htrc with
      | eres =>
          have hpostb : carryPostBound bound
              (Code.stmt (.block (selectSwitch D cv cases' dflt))) = bound :=
            carryPostBound_block bound _
          have hpost : carryPostBound bound (Code.stmt (.switch c cases' dflt)) = bound := by
            simp [carryPostBound, carryStmt, hsc'.1, hsc'.2.1, hsc'.2.2]
          rw [hpostb] at htrb
          rw [hpost]
          cases htrb with
          | norm hk => exact ⟨_, Step.switchExec hstepc hstepb, .norm hk⟩
          | halt => exact ⟨_, Step.switchExec hstepc hstepb, .halt⟩
          | «leave» => exact ⟨_, Step.switchExec hstepc hstepb, TResL.leave⟩
  | @Step.switchHalt _ _ _ _ _ c cases' dflt st1 hc =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      have hsc' : carryExpr bound c = true := by
        have h2 : (carryStmt bound (.switch c cases' dflt)).isSome = true := hsc
        by_cases hcnd : (carryExpr bound c && carryCases bound cases' &&
            carryDflt bound dflt) = true
        · rw [Bool.and_eq_true, Bool.and_eq_true] at hcnd; exact hcnd.1.1
        · simp [carryStmt, hcnd] at h2
      have hagc : FunsAgree (calls := calls) (creates := creates) cenv funs₁ (exprCallNames c) :=
        hag.mono (fun y hy => by
          show y ∈ stmtCallNames (.switch c cases' dflt)
          exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hy))))
      obtain ⟨res₁, hstepc, htrc⟩ := carry_body_bwd hc cenv funs₁ W hV
        (by simpa [carryBodyCode, carryCode] using hsc') hb hagc hR
      subst hV
      cases htrc with
      | eres => exact ⟨_, Step.switchHalt hstepc, .halt⟩
  | @Step.forLoop _ _ _ _ _ init c post body Vinit stinit Vend stend o hinit hloop =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      exact absurd hsc (by simp [carryBodyCode, carryCode, carryStmt])
  | @Step.forInitHalt _ _ _ _ _ init c post body Vinit stinit hinit =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      exact absurd hsc (by simp [carryBodyCode, carryCode, carryStmt])
  | .«break» =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      exact absurd hsc (by simp [carryBodyCode, carryCode, carryStmt])
  | .«continue» =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      exact absurd hsc (by simp [carryBodyCode, carryCode, carryStmt])
  | .«leave» =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      exact absurd hsc (by simp [carryBodyCode, carryCode, carryStmt])
  | .seqNil =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      subst hV
      exact ⟨_, Step.seqNil, .norm (fun x hx => by simp [carryPostBound] at hx)⟩
  | @Step.seqCons _ _ _ _ _ s rest V1 st1 V2 st2 o hs hrest =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      have hlv : carryLeaveStmts bound (s :: rest) := hsc
      rcases carryLeaveStmts_cons_inv hlv with ⟨bound₁, hstmt, hrest'⟩ | ⟨rfl, rfl⟩
      · have hags : FunsAgree (calls := calls) (creates := creates) cenv funs₁ (stmtCallNames s) :=
          hag.mono (fun y hy => by
            show y ∈ stmtsCallNames (s :: rest); exact List.mem_append.mpr (Or.inl hy))
        have hagr : FunsAgree (calls := calls) (creates := creates) cenv funs₁
            (stmtsCallNames rest) :=
          hag.mono (fun y hy => by
            show y ∈ stmtsCallNames (s :: rest); exact List.mem_append.mpr (Or.inr hy))
        obtain ⟨res₁, hstep₁, htr₁⟩ := carry_body_bwd hs cenv funs₁ W hV
          (carryBodyCode_of_stmt hstmt) hb
          (by simpa [carryCallNames] using hags) hR
        have hpost₁ : carryPostBound bound (Code.stmt s) = bound₁ := by
          simp [carryPostBound, hstmt]
        rw [hpost₁] at htr₁
        obtain ⟨A₁, hV1, hres₁, hk⟩ := TResL.norm_inv' htr₁
        obtain ⟨res₃, hstep₂, htr₂⟩ := carry_body_bwd hrest cenv funs₁ W hV1
          hrest' hk (by simpa [carryCallNames] using hagr) hR
        subst hres₁
        cases htr₂ with
        | norm hk₂ => exact ⟨_, Step.seqCons hstep₁ hstep₂, .norm hk₂⟩
        | halt => exact ⟨_, Step.seqCons hstep₁ hstep₂, .halt⟩
        | «leave» => exact ⟨_, Step.seqCons hstep₁ hstep₂, TResL.leave⟩
      · cases hs
  | @Step.seqStop _ _ _ _ _ s rest V1 st1 o hs hne =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      have hlv : carryLeaveStmts bound (s :: rest) := hsc
      rcases carryLeaveStmts_cons_inv hlv with ⟨bound₁, hstmt, hrest'⟩ | ⟨rfl, rfl⟩
      · have hags : FunsAgree (calls := calls) (creates := creates) cenv funs₁ (stmtCallNames s) :=
          hag.mono (fun y hy => by
            show y ∈ stmtsCallNames (s :: rest); exact List.mem_append.mpr (Or.inl hy))
        obtain ⟨res₁, hstep₁, htr₁⟩ := carry_body_bwd hs cenv funs₁ W hV
          (carryBodyCode_of_stmt hstmt) hb
          (by simpa [carryCallNames] using hags) hR
        cases htr₁ with
        | norm hk => exact absurd rfl hne
        | halt => exact ⟨_, Step.seqStop hstep₁ (by simp), .halt⟩
        | «leave» => exact ⟨_, Step.seqStop hstep₁ (by simp), TResL.leave⟩
      · cases hs with
        | «leave» => subst hV; exact ⟨_, Step.seqStop Step.leave (by simp), TResL.leave⟩
  | .loopDone hc hcz =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      exact absurd hsc (by simp [carryBodyCode, carryCode])
  | .loopCondHalt hc =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      exact absurd hsc (by simp [carryBodyCode, carryCode])
  | .loopStep hc hcv hbody hob hpost hnext =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      exact absurd hsc (by simp [carryBodyCode, carryCode])
  | .loopPostHalt hc hcv hbody hob hpost =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      exact absurd hsc (by simp [carryBodyCode, carryCode])
  | .loopBreak hc hcv hbody =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      exact absurd hsc (by simp [carryBodyCode, carryCode])
  | .loopLeave hc hcv hbody =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      exact absurd hsc (by simp [carryBodyCode, carryCode])
  | .loopBodyHalt hc hcv hbody =>
      intro A W' bound cenv funs₁ W hV hsc hb hag hR
      exact absurd hsc (by simp [carryBodyCode, carryCode])
  termination_by structural h

/-- Unwrap the inlined core's `block` and delegate to `peelBlock`
(∀-after form; telescope order mirrors the original so `cy_bwd`'s call sites
are unchanged). -/
theorem peelBody {funs₂ : FunEnv D} {E : VEnv D} {st : EvmState}
    {codeP : Code Op} {res : Res D}
    (hs : Step D funs₂ E st codeP res) :
    ∀ {d : IDecl} {xs : List Ident} {as : List (Expr Op)} {V Z : VEnv D},
      E = Z ++ V →
      codeP = .stmt (inlineCore d xs as) →
      carryStmts (d.ps ++ d.rs) d.ss = true →
      as.length = d.ps.length → argsHaveCall as = false →
      argsShadowOK d.rs (d.ps.zip as) = true →
      (∀ x ∈ xs, x ∉ d.ps ++ d.rs) → xs.length = d.rs.length →
      (∀ y ∈ varsList as, y ∉ Z.map Prod.fst) →
      ∀ (funs₁ cenv₀ : FunEnv D),
      (∀ g ∈ stmtsCallNames d.ss, lookupFun funs₁ g = lookupFun cenv₀ g) →
      CyFunsRel (calls := calls) (creates := creates) funs₁ funs₂ →
      ((∃ argvals st1 Vend str,
        Step D funs₁ V st (.args as) (.eres (.vals argvals st1)) ∧
        Step D cenv₀ (d.ps.zip argvals ++ bindZeros D d.rs) st1
          (.stmt (.block d.ss)) (.sres Vend str .normal) ∧
        res = .sres (VEnv.setMany (Z ++ V) xs (d.rs.map
          (fun r => (VEnv.get Vend r).getD (evmWithExternal calls creates).zero))) str .normal) ∨
      (∃ argvals st1 Vend str,
        Step D funs₁ V st (.args as) (.eres (.vals argvals st1)) ∧
        Step D cenv₀ (d.ps.zip argvals ++ bindZeros D d.rs) st1
          (.stmt (.block d.ss)) (.sres Vend str .halt) ∧
        res = .sres (Z ++ V) str .halt) ∨
      (∃ str, Step D funs₁ V st (.args as) (.eres (.halt str)) ∧
        res = .sres (Z ++ V) str .halt)) := by
  match hs with
  | @Step.block _ _ _ _ _ ib Vb stb ob hb =>
      intro d xs as V Z hE hcodeP hsc hlen_as hnc hsh hxout hlen_xs hZ funs₁ cenv₀ hagbody hR
      injection hcodeP with hc1
      injection hc1 with hinner
      have hhoist : hoist D ([Stmt.letDecl d.rs none]
          ++ (d.ps.zip as).reverse.map (fun pa => Stmt.letDecl [pa.1] (some pa.2))
          ++ [Stmt.block d.ss]
          ++ (xs.zip d.rs).map (fun xr => Stmt.assign [xr.1] (Expr.var xr.2))) = [] :=
        inlineStmts_hoist_nil d xs as
      have hRb : CyFunsRel (calls := calls) (creates := creates)
          (hoist D ib :: funs₁) (hoist D ib :: funs₂) := by
        rw [hinner, hhoist]; exact CyFunsRel.cons_nil hR
      have hag_body' : ∀ g ∈ stmtsCallNames d.ss,
          lookupFun cenv₀ g = lookupFun (hoist D ib :: funs₁) g := by
        intro g hg; rw [hinner, hhoist]; exact (hagbody g hg).symm
      have hLrem' : ib = Stmt.letDecl d.rs none :: peelTail d xs ((d.ps.zip as).reverse) := by
        rw [hinner]; simp [peelTail]
      have hpa : PeelArgsSpec funs₁ cenv₀ V Z st d xs as Vb stb ob :=
        peelBlock hb rfl rfl hLrem' hE rfl
          ⟨hsc, hlen_as, hnc, hsh, hxout, hlen_xs, hZ, hRb, hag_body'⟩
      unfold PeelArgsSpec at hpa
      rcases hpa
        with ⟨argvals, st1, Vend, hargs, hbody, hVb, hoeq⟩
          | ⟨argvals, st1, Vend, hargs, hbody, hVb, hoeq⟩
          | ⟨M, hargs, hVb, hoeq⟩
      · refine Or.inl ⟨argvals, st1, Vend, stb, hargs, hbody, ?_⟩
        rw [hoeq, hE, hVb, restore_exact (VEnv.setMany_length _ _ _)]
      · refine Or.inr (Or.inl ⟨argvals, st1, Vend, stb, hargs, hbody, ?_⟩)
        rw [hoeq, hE, hVb, restore_exact rfl]
      · refine Or.inr (Or.inr ⟨stb, hargs, ?_⟩)
        rw [hoeq, hE, hVb, restore_exact rfl]
  | .lit =>
      intro _ _ _ _ _ _ hcodeP
      cases hcodeP
  | .var .. =>
      intro _ _ _ _ _ _ hcodeP
      cases hcodeP
  | .builtinOk .. =>
      intro _ _ _ _ _ _ hcodeP
      cases hcodeP
  | .builtinHalt .. =>
      intro _ _ _ _ _ _ hcodeP
      cases hcodeP
  | .builtinArgsHalt .. =>
      intro _ _ _ _ _ _ hcodeP
      cases hcodeP
  | .callOk .. =>
      intro _ _ _ _ _ _ hcodeP
      cases hcodeP
  | .callHalt .. =>
      intro _ _ _ _ _ _ hcodeP
      cases hcodeP
  | .callArgsHalt .. =>
      intro _ _ _ _ _ _ hcodeP
      cases hcodeP
  | .argsNil =>
      intro _ _ _ _ _ _ hcodeP
      cases hcodeP
  | .argsCons .. =>
      intro _ _ _ _ _ _ hcodeP
      cases hcodeP
  | .argsRestHalt .. =>
      intro _ _ _ _ _ _ hcodeP
      cases hcodeP
  | .argsHeadHalt .. =>
      intro _ _ _ _ _ _ hcodeP
      cases hcodeP
  | .funDef =>
      intro _ _ _ _ _ _ hcodeP
      cases hcodeP
  | .letZero =>
      intro _ _ _ _ _ _ hcodeP
      cases hcodeP
  | .letVal .. =>
      intro _ _ _ _ _ _ hcodeP
      cases hcodeP
  | .letHalt .. =>
      intro _ _ _ _ _ _ hcodeP
      cases hcodeP
  | .assignVal .. =>
      intro _ _ _ _ _ _ hcodeP
      cases hcodeP
  | .assignHalt .. =>
      intro _ _ _ _ _ _ hcodeP
      cases hcodeP
  | .exprStmt .. =>
      intro _ _ _ _ _ _ hcodeP
      cases hcodeP
  | .exprStmtHalt .. =>
      intro _ _ _ _ _ _ hcodeP
      cases hcodeP
  | .ifTrue .. =>
      intro _ _ _ _ _ _ hcodeP
      cases hcodeP
  | .ifFalse .. =>
      intro _ _ _ _ _ _ hcodeP
      cases hcodeP
  | .ifHalt .. =>
      intro _ _ _ _ _ _ hcodeP
      cases hcodeP
  | .switchExec .. =>
      intro _ _ _ _ _ _ hcodeP
      cases hcodeP
  | .switchHalt .. =>
      intro _ _ _ _ _ _ hcodeP
      cases hcodeP
  | .forLoop .. =>
      intro _ _ _ _ _ _ hcodeP
      cases hcodeP
  | .forInitHalt .. =>
      intro _ _ _ _ _ _ hcodeP
      cases hcodeP
  | .«break» =>
      intro _ _ _ _ _ _ hcodeP
      cases hcodeP
  | .«continue» =>
      intro _ _ _ _ _ _ hcodeP
      cases hcodeP
  | .«leave» =>
      intro _ _ _ _ _ _ hcodeP
      cases hcodeP
  | .seqNil =>
      intro _ _ _ _ _ _ hcodeP
      cases hcodeP
  | .seqCons .. =>
      intro _ _ _ _ _ _ hcodeP
      cases hcodeP
  | .seqStop .. =>
      intro _ _ _ _ _ _ hcodeP
      cases hcodeP
  | .loopDone .. =>
      intro _ _ _ _ _ _ hcodeP
      cases hcodeP
  | .loopCondHalt .. =>
      intro _ _ _ _ _ _ hcodeP
      cases hcodeP
  | .loopStep .. =>
      intro _ _ _ _ _ _ hcodeP
      cases hcodeP
  | .loopPostHalt .. =>
      intro _ _ _ _ _ _ hcodeP
      cases hcodeP
  | .loopBreak .. =>
      intro _ _ _ _ _ _ hcodeP
      cases hcodeP
  | .loopLeave .. =>
      intro _ _ _ _ _ _ hcodeP
      cases hcodeP
  | .loopBodyHalt .. =>
      intro _ _ _ _ _ _ hcodeP
      cases hcodeP
  termination_by structural hs

/-- Peel the inlined core's leading `letDecl d.rs none` and delegate to
`peelArgs`; principal-only binders before the match (∀-after form). -/
theorem peelBlock {Sfuns : FunEnv D} {Ecur : VEnv D} {stq : EvmState}
    {codeQ : Code Op} {res : Res D}
    (hseq : Step D Sfuns Ecur stq codeQ res) :
    ∀ {d : IDecl} {xs : List Ident} {as : List (Expr Op)}
      {funs₁ cenv₀ funsI : FunEnv D} {V Z : VEnv D} {st : EvmState}
      {Lrem : List (Stmt Op)} {Vinner : VEnv D} {str : EvmState} {o : Outcome},
      codeQ = .stmts Lrem →
      res = .sres Vinner str o →
      Lrem = Stmt.letDecl d.rs none :: peelTail d xs ((d.ps.zip as).reverse) →
      Ecur = Z ++ V →
      stq = st →
      PeelCtx (calls := calls) (creates := creates) d xs as cenv₀ funsI Sfuns Z →
      PeelArgsSpec funs₁ cenv₀ V Z st d xs as Vinner str o := by
  match hseq with
  | .seqNil =>
      intro d xs as funs₁ cenv₀ funsI V Z st Lrem Vinner str o hcodeQ hres hLrem hEcur hstq ctx
      rw [hLrem] at hcodeQ; simp at hcodeQ
  | @Step.seqCons _ _ _ _ _ s rest Vmid stmid V2 st2 o2 hlet htail =>
      intro d xs as funs₁ cenv₀ funsI V Z st Lrem Vinner str o hcodeQ hres hLrem hEcur hstq ctx
      injection hcodeQ with hLl
      rw [hLrem] at hLl
      injection hLl with hs_eq hrest_eq
      have hzres := letZero_inv (hs_eq ▸ hlet)
      injection hzres with hVmid hstmid
      exact peelArgs htail ((d.ps.zip as).reverse) [] [] rfl hres
        (by simp) hrest_eq
        (by rw [hVmid, hEcur]; simp [peelEnvAcc])
        (by rw [hstmid, hstq]; exact Step.argsNil)
        rfl ctx
  | @Step.seqStop _ _ _ _ _ s rest Vfin stfin ofin hlet hne =>
      intro d xs as funs₁ cenv₀ funsI V Z st Lrem Vinner str o hcodeQ hres hLrem hEcur hstq ctx
      injection hcodeQ with hLl
      rw [hLrem] at hLl
      injection hLl with hs_eq hrest_eq
      have hzres := letZero_inv (hs_eq ▸ hlet)
      injection hzres with hVfin hstfin ho
      exact absurd ho hne
  | .block .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .lit =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .var .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .builtinOk .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .builtinHalt .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .builtinArgsHalt .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .callOk .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .callHalt .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .callArgsHalt .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .argsNil =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .argsCons .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .argsRestHalt .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .argsHeadHalt .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .funDef =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .letZero =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .letVal .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .letHalt .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .assignVal .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .assignHalt .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .exprStmt .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .exprStmtHalt .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .ifTrue .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .ifFalse .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .ifHalt .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .switchExec .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .switchHalt .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .forLoop .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .forInitHalt .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .«break» =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .«continue» =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .«leave» =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .loopDone .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .loopCondHalt .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .loopStep .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .loopPostHalt .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .loopBreak .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .loopLeave .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .loopBodyHalt .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  termination_by structural hseq

theorem peelArgs {Sfuns : FunEnv D} {Ecur : VEnv D} {st_cur : EvmState}
    {codeQ : Code Op} {res : Res D}
    (hseq : Step D Sfuns Ecur st_cur codeQ res) :
    ∀ {d : IDecl} {xs : List Ident} {as : List (Expr Op)}
      {funs₁ cenv₀ funsI : FunEnv D} {V Z : VEnv D} {st : EvmState}
      {Lrem : List (Stmt Op)} {Vinner : VEnv D} {str : EvmState} {o : Outcome}
      (Pfr Ppeeled : List (Ident × Expr Op)) (valsDone : List U256),
      codeQ = .stmts Lrem →
      res = .sres Vinner str o →
      Pfr.reverse ++ Ppeeled = d.ps.zip as →
      Lrem = peelTail d xs Pfr →
      Ecur = peelEnvAcc d Z V Ppeeled valsDone →
      Step D funs₁ V st (.args (Ppeeled.map Prod.snd))
        (.eres (.vals valsDone st_cur)) →
      valsDone.length = Ppeeled.length →
      PeelCtx (calls := calls) (creates := creates) d xs as cenv₀ funsI Sfuns Z →
      PeelArgsSpec funs₁ cenv₀ V Z st d xs as Vinner str o := by
  match hseq with
  | .seqNil =>
      intro d xs as funs₁ cenv₀ funsI V Z st Lrem Vinner str o Pfr Ppeeled valsDone hcodeQ hres hP hLrem hEcur hacc hvlen ctx
      rw [hLrem] at hcodeQ; simp [peelTail] at hcodeQ
  | @Step.seqCons _ _ _ _ _ s rest Vmid stmid Vfin stfin ofin hs hrest =>
      intro d xs as funs₁ cenv₀ funsI V Z st Lrem Vinner str o Pfr Ppeeled valsDone hcodeQ hres hP hLrem hEcur hacc hvlen ctx
      injection hcodeQ with hLl
      rw [hLrem] at hLl
      cases Pfr with
      | cons pa Pfr' =>
          rw [peelTail_cons] at hLl
          injection hLl with hs_eq hrest_eq
          have hEcurU : Ecur = (Ppeeled.map Prod.fst).zip valsDone
              ++ (bindZeros D d.rs ++ (Z ++ V)) := by
            simp only [hEcur, peelEnvAcc]
          obtain ⟨v, he, hV1⟩ := letSome_norm_inv (hs_eq ▸ hs)
          have hP' : Pfr'.reverse ++ (pa :: Ppeeled) = d.ps.zip as := by
            rw [← hP]; simp [List.reverse_cons, List.append_assoc]
          have he' : Step D funs₁ V st_cur (.expr pa.2) (.eres (.vals [v] stmid)) :=
            argLet_src_transfer hEcurU hvlen ctx.hlen_as ctx.hnc ctx.hsh ctx.hZ hP' he
          have hacc' : Step D funs₁ V st (.args ((pa :: Ppeeled).map Prod.snd))
              (.eres (.vals (v :: valsDone) stmid)) := by
            rw [List.map_cons]; exact Step.argsCons hacc he'
          have hEcur' : Vmid = peelEnvAcc d Z V (pa :: Ppeeled) (v :: valsDone) := by
            rw [hV1, hEcur, peelEnvAcc_cons]
          exact peelArgs hrest Pfr' (pa :: Ppeeled) (v :: valsDone) rfl hres hP'
            hrest_eq hEcur' hacc'
            (by rw [List.length_cons, List.length_cons, hvlen]) ctx
      | nil =>
          rw [peelTail_nil] at hLl
          injection hLl with hs_eq hrest_eq
          have hEcurU : Ecur = (Ppeeled.map Prod.fst).zip valsDone
              ++ (bindZeros D d.rs ++ (Z ++ V)) := by
            simp only [hEcur, peelEnvAcc]
          rw [hrest_eq] at hrest
          have hPeq : Ppeeled = d.ps.zip as := by simpa using hP
          have hargs : Step D funs₁ V st (.args as) (.eres (.vals valsDone st_cur)) := by
            have h := hacc; rw [hPeq, zip_snds ctx.hlen_as.symm] at h; exact h
          have hvd : valsDone.length = d.ps.length := by
            rw [hvlen, hPeq, List.length_zip, ctx.hlen_as, Nat.min_self]
          have hV : Ecur = ((Ppeeled.map Prod.fst).zip valsDone ++ bindZeros D d.rs)
              ++ (Z ++ V) := by rw [hEcurU, List.append_assoc]
          have hbc : carryBodyCode (d.ps ++ d.rs) (Code.stmt s) := by
            rw [hs_eq]; exact Or.inl ctx.hsc
          have hA0keys : ((Ppeeled.map Prod.fst).zip valsDone ++ bindZeros D d.rs).map Prod.fst
              = d.ps ++ d.rs := by
            rw [List.map_append, List.map_fst_zip (by rw [List.length_map]; omega),
              bindZeros_keys, hPeq, List.map_fst_zip (le_of_eq ctx.hlen_as.symm)]
          have hA0eq : (Ppeeled.map Prod.fst).zip valsDone ++ bindZeros D d.rs
              = d.ps.zip valsDone ++ bindZeros D d.rs := by
            rw [hPeq, List.map_fst_zip (le_of_eq ctx.hlen_as.symm)]
          obtain ⟨res₁, hstep, htr⟩ := carry_body_bwd hs cenv₀ funsI ([] : VEnv D) hV hbc
            (fun x hx => by rw [hA0keys]; exact hx)
            (by rw [hs_eq]; exact ctx.hag_body) ctx.hRb
          rw [show carryPostBound (d.ps ++ d.rs) (Code.stmt s) = d.ps ++ d.rs from by
            rw [hs_eq]; exact carryPostBound_block _ _] at htr
          rw [hs_eq] at hstep
          exact nil_seqCons_finish hargs hA0eq hvd ctx.hxout ctx.hlen_xs hstep htr hrest hres
  | @Step.seqStop _ _ _ _ _ s rest Vfin stfin ofin hs hne =>
      intro d xs as funs₁ cenv₀ funsI V Z st Lrem Vinner str o Pfr Ppeeled valsDone hcodeQ hres hP hLrem hEcur hacc hvlen ctx
      injection hcodeQ with hLl
      rw [hLrem] at hLl
      cases Pfr with
      | cons pa Pfr' =>
          rw [peelTail_cons] at hLl
          injection hLl with hs_eq hrest_eq
          have hEcurU : Ecur = (Ppeeled.map Prod.fst).zip valsDone
              ++ (bindZeros D d.rs ++ (Z ++ V)) := by
            simp only [hEcur, peelEnvAcc]
          obtain ⟨he, hVfin, hofin⟩ := letSome_stop_inv (hs_eq ▸ hs) hne
          have hP' : Pfr'.reverse ++ (pa :: Ppeeled) = d.ps.zip as := by
            rw [← hP]; simp [List.reverse_cons, List.append_assoc]
          have he' : Step D funs₁ V st_cur (.expr pa.2) (.eres (.halt stfin)) :=
            argLet_src_transfer hEcurU hvlen ctx.hlen_as ctx.hnc ctx.hsh ctx.hZ hP' he
          have has_eq : as = Pfr'.reverse.map Prod.snd ++ (pa.2 :: Ppeeled.map Prod.snd) := by
            rw [← zip_snds (ps := d.ps) ctx.hlen_as.symm, ← hP', List.map_append, List.map_cons]
          have hah : Step D funs₁ V st (.args as) (.eres (.halt stfin)) := by
            rw [has_eq]; exact args_prepend_halt (Step.argsHeadHalt hacc he') _
          injection hres with hVf hstf hof
          unfold PeelArgsSpec
          refine Or.inr (Or.inr
            ⟨(Ppeeled.map Prod.fst).zip valsDone ++ bindZeros D d.rs, ?_, ?_, ?_⟩)
          · rw [← hstf]; exact hah
          · rw [← hVf, hVfin, hEcurU, List.append_assoc]
          · exact hof.symm.trans hofin
      | nil =>
          rw [peelTail_nil] at hLl
          injection hLl with hs_eq hrest_eq
          have hEcurU : Ecur = (Ppeeled.map Prod.fst).zip valsDone
              ++ (bindZeros D d.rs ++ (Z ++ V)) := by
            simp only [hEcur, peelEnvAcc]
          have hPeq : Ppeeled = d.ps.zip as := by simpa using hP
          have hargs : Step D funs₁ V st (.args as) (.eres (.vals valsDone st_cur)) := by
            have h := hacc; rw [hPeq, zip_snds ctx.hlen_as.symm] at h; exact h
          have hvd : valsDone.length = d.ps.length := by
            rw [hvlen, hPeq, List.length_zip, ctx.hlen_as, Nat.min_self]
          have hV : Ecur = ((Ppeeled.map Prod.fst).zip valsDone ++ bindZeros D d.rs)
              ++ (Z ++ V) := by rw [hEcurU, List.append_assoc]
          have hbc : carryBodyCode (d.ps ++ d.rs) (Code.stmt s) := by
            rw [hs_eq]; exact Or.inl ctx.hsc
          have hA0keys : ((Ppeeled.map Prod.fst).zip valsDone ++ bindZeros D d.rs).map Prod.fst
              = d.ps ++ d.rs := by
            rw [List.map_append, List.map_fst_zip (by rw [List.length_map]; omega),
              bindZeros_keys, hPeq, List.map_fst_zip (le_of_eq ctx.hlen_as.symm)]
          have hA0eq : (Ppeeled.map Prod.fst).zip valsDone ++ bindZeros D d.rs
              = d.ps.zip valsDone ++ bindZeros D d.rs := by
            rw [hPeq, List.map_fst_zip (le_of_eq ctx.hlen_as.symm)]
          obtain ⟨res₁, hstep, htr⟩ := carry_body_bwd hs cenv₀ funsI ([] : VEnv D) hV hbc
            (fun x hx => by rw [hA0keys]; exact hx)
            (by rw [hs_eq]; exact ctx.hag_body) ctx.hRb
          rw [show carryPostBound (d.ps ++ d.rs) (Code.stmt s) = d.ps ++ d.rs from by
            rw [hs_eq]; exact carryPostBound_block _ _] at htr
          rw [hs_eq] at hstep
          exact nil_seqStop_finish hargs hA0eq hvd ctx.hsc hA0keys hstep htr hne hres
  | .block .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .lit =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .var .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .builtinOk .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .builtinHalt .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .builtinArgsHalt .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .callOk .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .callHalt .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .callArgsHalt .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .argsNil =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .argsCons .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .argsRestHalt .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .argsHeadHalt .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .funDef =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .letZero =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .letVal .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .letHalt .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .assignVal .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .assignHalt .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .exprStmt .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .exprStmtHalt .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .ifTrue .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .ifFalse .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .ifHalt .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .switchExec .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .switchHalt .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .forLoop .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .forInitHalt .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .«break» =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .«continue» =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .«leave» =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .loopDone .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .loopCondHalt .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .loopStep .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .loopPostHalt .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .loopBreak .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .loopLeave .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  | .loopBodyHalt .. =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcodeQ
      cases hcodeQ
  termination_by structural hseq


end

/-- Related blocks are pointwise equivalent (forward via `cy_fwd`, backward via
`cy_bwd`). -/
theorem CyRel.equivBlock {b b' : Block Op}
    (h : CyRel (carryDeltaExtend [] b) (.stmts b) (.stmts b')) :
    EquivBlock D b b' := by
  intro funs V st V' st' o
  constructor
  · intro hstep
    obtain ⟨res₂, hs₂, hres⟩ := cy_fwd hstep (CyFunsRel.refl funs)
      (CarryCompat.nil funs) (CyRel.blockS h)
    rw [show res₂ = _ from hres] at hs₂
    exact hs₂
  · intro hstep
    obtain ⟨res₁, hs₁, hres⟩ := cy_bwd hstep (CyFunsRel.refl funs)
      (CarryCompat.nil funs) (CyRel.blockS h)
    have hresX : _ = res₁ := hres
    rw [← hresX] at hs₁
    exact hs₁

/-- The **InlineCallsCarry pass**: call-carrying statement inlining, bundled with
its soundness proof. -/
def inlineCallsCarry : LocalPass D where
  run := inlineCallsCarryBlock
  sound := fun b => CyRel.equivBlock
    (by
      rw [show inlineCallsCarryBlock b = cyStmts (carryDeltaExtend [] b) b by
        rw [inlineCallsCarryBlock, cyBlock]]
      exact cyStmts_rel (carryDeltaExtend [] b) (CarryWF.nil.extend b) b)

@[simp] theorem inlineCallsCarry_run (b : Block Op) :
    (inlineCallsCarry (calls := calls) (creates := creates)).run b =
      inlineCallsCarryBlock b := rfl



end YulEvmCompiler.Optimizer
