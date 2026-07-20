import YulEvmCompiler.Optimizer.Implementation.InlineCallsSound
set_option warningAsError true
/-!
# YulEvmCompiler.Optimizer.Implementation.FreshenCalls

**Call-site freshening** — the collision unblocker for `InlineCalls`.

solc's helpers reuse a small vocabulary (`value`, `slot`, `offset`, …) as
*both* caller-side variables and callee parameter/return names, so the
biggest gas-gap fixtures hit `siteOK`'s capture conditions
(`xs ∩ (ps ∪ rs) ≠ ∅`, argument shadowing, call-bearing arguments) and their
helper chains never inline. `InlineCalls` cannot α-rename: its soundness
inserts callee bodies *unchanged* (the `Δ`-matching argument depends on it).

This pass renames the **caller-side results**. An assign-form site
`xs := f(as)` that resolves to an inlinable declaration, fails `siteOK`, but
whose arguments already satisfy the remaining `siteOK` conditions is
rewritten to a self-contained block with globally-fresh return names:

```yul
{ let P_r0, P_r1 := f(as)
  xs[0] := P_r0
  xs[1] := P_r1
}
```

The inner site now has collision-free result names, so
`inlineCalls` (which runs right after this pass in the round) inlines it,
and depth-gated copy propagation plus `DeadPure` consume exactly the copies
introduced here. The fresh names share a prefix `P` chosen so that **no
program identifier starts with it** — freshness needs no counter threading,
per-site reuse of the same names is fine (each site's names are bound only
inside its own block), and the choice depends only on the program's
identifier set, which layout resolution never changes.

Only the assign form is rewritten in v1: the observed blockers are all
assign-form (`value := extract_…(…)`, `slot, offset := storage_array_…(…)`),
and the let form would additionally need the halt-desync bookkeeping of a
zero-init split (`let xs` leaves binders on the env when the site block
halts). Logged as a follow-up.

Soundness (`EquivStmt` per site, pointwise — no function-environment
reasoning is needed because the call remains a call): the call is evaluated
before the fresh bindings are installed; the read-out assignments equal the
original `setMany`; and the enclosing block's `restore` erases the
temporaries on every exit path, including halts.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM

variable {calls : ExternalCalls} {creates : ExternalCreates}

local notation "D" => evmWithExternal calls creates

/-! ### Identifier collection and the fresh prefix -/

mutual

/-- Every identifier occurring in an expression (variables and call names). -/
def exprIdents : Expr Op → List Ident
  | .lit _ => []
  | .var x => [x]
  | .builtin _ args => argsIdents args
  | .call f args => f :: argsIdents args

/-- Identifiers of an argument list. -/
def argsIdents : List (Expr Op) → List Ident
  | [] => []
  | e :: rest => exprIdents e ++ argsIdents rest

end

mutual

/-- Every identifier occurring in a statement: binders, targets, function
names, parameters, returns, and expression identifiers. -/
def stmtIdents : Stmt Op → List Ident
  | .block body => stmtsIdents body
  | .funDef n ps rs body => n :: ps ++ rs ++ stmtsIdents body
  | .letDecl xs none => xs
  | .letDecl xs (some e) => xs ++ exprIdents e
  | .assign xs e => xs ++ exprIdents e
  | .cond c body => exprIdents c ++ stmtsIdents body
  | .switch c cases dflt =>
      exprIdents c ++ casesIdents cases ++ dfltIdents dflt
  | .forLoop init c post body =>
      stmtsIdents init ++ exprIdents c ++ stmtsIdents post ++ stmtsIdents body
  | .exprStmt e => exprIdents e
  | .break => []
  | .continue => []
  | .leave => []

/-- Identifiers of a statement sequence. -/
def stmtsIdents : List (Stmt Op) → List Ident
  | [] => []
  | s :: rest => stmtIdents s ++ stmtsIdents rest

/-- Identifiers of `switch` cases. -/
def casesIdents : List (Literal × Block Op) → List Ident
  | [] => []
  | (_, b) :: rest => stmtsIdents b ++ casesIdents rest

/-- Identifiers of a `switch` default. -/
def dfltIdents : Option (Block Op) → List Ident
  | none => []
  | some b => stmtsIdents b

end

/-- Does any identifier in `used` start with `p`? -/
def prefixUsed (used : List Ident) (p : String) : Bool :=
  used.any (fun x => p.isPrefixOf x)

/-- A prefix no program identifier starts with: the first `fc<k>_` free in
`used`. Termination: there are finitely many identifiers, each with finitely
many prefixes, so some `k ≤ used.length` is free (fuel makes this obvious to
the compiler; on fuel exhaustion — impossible — the pass declines by
returning `none`, keeping the transform total and conservative). -/
def freshPrefixFuel (used : List Ident) : Nat → Nat → Option String
  | 0, _ => none
  | fuel + 1, k =>
      let p := s!"fc{k}_"
      if prefixUsed used p then freshPrefixFuel used fuel (k + 1) else some p

/-- The fresh prefix for a program's identifier set. -/
def freshPrefix (used : List Ident) : Option String :=
  freshPrefixFuel used (used.length + 1) 0

/-! ### The site rewrite -/

/-- The fresh return names for arity `n`: `P_r0 … P_r(n-1)`. -/
def freshRets (P : String) (n : Nat) : List Ident :=
  (List.range n).map (fun i => s!"{P}r{i}")

/-- Should this assign-form site be freshened? It must resolve to an
inlinable declaration that `inlineCalls` *wants* (`inlineOK`) with matching
arities and distinct targets, but be rejected by its capture/shape
conditions (`siteOK`) — the only sites where freshening changes anything. -/
def freshenWanted (d : IDecl) (xs frs : List Ident) (as : List (Expr Op)) : Bool :=
  inlineOK d && as.length = d.ps.length && xs.length = d.rs.length &&
  xs.Nodup && !siteOK d xs as false && siteOK d frs as true &&
  frs.Nodup && xs.all (fun x => !frs.contains x)

/-- The freshened site block (see the module notes). -/
def freshenCore (P : String) (xs : List Ident) (f : Ident)
    (as : List (Expr Op)) : Stmt Op :=
  let frs := freshRets P xs.length
  .block
    ([.letDecl frs (some (.call f as))]
      ++ (xs.zip frs).map (fun xr => .assign [xr.1] (.var xr.2)))

/-! ### Site soundness -/

/-- Reading a no-call argument list is unchanged by the empty function scope
introduced by the site block. -/
private theorem args_emptyScope_fwd {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    {as : List (Expr Op)} {r : EResult D}
    (h : Step D funs V st (.args as) (.eres r)) (hnc : argsHaveCall as = false) :
    Step D ([] :: funs) V st (.args as) (.eres r) :=
  exprNoCall_transfer h ([] :: funs) ⟨hnc, fun _ _ => rfl⟩

private theorem args_emptyScope_bwd {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    {as : List (Expr Op)} {r : EResult D}
    (h : Step D ([] :: funs) V st (.args as) (.eres r)) (hnc : argsHaveCall as = false) :
    Step D funs V st (.args as) (.eres r) :=
  exprNoCall_transfer h funs ⟨hnc, fun _ _ => rfl⟩

/-- A call with call-free arguments is unchanged by an empty innermost
function scope. -/
theorem call_emptyScope_fwd {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    {f : Ident} {as : List (Expr Op)} {r : EResult D}
    (h : Step D funs V st (.expr (.call f as)) (.eres r))
    (hnc : argsHaveCall as = false) :
    Step D ([] :: funs) V st (.expr (.call f as)) (.eres r) := by
  cases h with
  | callOk hargs hlookup hlen hbody ho =>
      exact Step.callOk (args_emptyScope_fwd hargs hnc)
        (by simpa [lookupFun] using hlookup) hlen hbody ho
  | callHalt hargs hlookup hlen hbody =>
      exact Step.callHalt (args_emptyScope_fwd hargs hnc)
        (by simpa [lookupFun] using hlookup) hlen hbody
  | callArgsHalt hargs => exact Step.callArgsHalt (args_emptyScope_fwd hargs hnc)

theorem call_emptyScope_bwd {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    {f : Ident} {as : List (Expr Op)} {r : EResult D}
    (h : Step D ([] :: funs) V st (.expr (.call f as)) (.eres r))
    (hnc : argsHaveCall as = false) :
    Step D funs V st (.expr (.call f as)) (.eres r) := by
  cases h with
  | callOk hargs hlookup hlen hbody ho =>
      exact Step.callOk (args_emptyScope_bwd hargs hnc)
        (by simpa [lookupFun] using hlookup) hlen hbody ho
  | callHalt hargs hlookup hlen hbody =>
      exact Step.callHalt (args_emptyScope_bwd hargs hnc)
        (by simpa [lookupFun] using hlookup) hlen hbody
  | callArgsHalt hargs => exact Step.callArgsHalt (args_emptyScope_bwd hargs hnc)

/-- A `Nodup` zip reads back its values in key order. -/
private theorem zip_gets_eq {xs : List Ident} (hnd : xs.Nodup) :
    ∀ {vs : List U256}, vs.length = xs.length →
      xs.map (fun x => (VEnv.get (xs.zip vs : VEnv D) x).getD
        (evmWithExternal calls creates).zero) = vs := by
  induction xs with
  | nil =>
      intro vs hlen
      cases vs with
      | nil => rfl
      | cons _ _ => simp at hlen
  | cons x rest ih =>
      intro vs hlen
      cases vs with
      | nil => simp at hlen
      | cons v vrest =>
          have hx : x ∉ rest := (List.nodup_cons.mp hnd).1
          have hnd' : rest.Nodup := (List.nodup_cons.mp hnd).2
          have hlen' : vrest.length = rest.length := by simpa using hlen
          simp only [List.zip_cons_cons, List.map_cons]
          rw [show VEnv.get (((x, v) :: rest.zip vrest) : VEnv D) x = some v by
            simp [VEnv.get], Option.getD_some]
          have htail : rest.map
              (fun y => (VEnv.get (((x, v) :: rest.zip vrest) : VEnv D) y).getD
                (evmWithExternal calls creates).zero) =
              rest.map (fun y => (VEnv.get (rest.zip vrest : VEnv D) y).getD
                (evmWithExternal calls creates).zero) := by
            apply List.map_congr_left
            intro y hy
            have hxy : x ≠ y := fun h => hx (h ▸ hy)
            simp [VEnv.get, hxy]
          rw [htail, ih hnd' hlen']

/-- Conditions extracted from the boolean site gate that are needed by the
semantic proof. -/
theorem freshenWanted_inv {d : IDecl} {xs frs : List Ident}
    {as : List (Expr Op)} (h : freshenWanted d xs frs as = true) :
    frs.length = xs.length ∧ frs.Nodup ∧
      (∀ x ∈ xs, x ∉ frs) ∧ argsHaveCall as = false := by
  unfold freshenWanted at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨_, _⟩, hxslen⟩, _⟩, _⟩, hsite⟩, hfrnd⟩, hdisj⟩ := h
  obtain ⟨_, hfrlen, _, hnc, _, _, _⟩ := siteOK_inv hsite
  have hxslen' : xs.length = d.rs.length := by simpa using hxslen
  refine ⟨hfrlen.trans hxslen'.symm, by simpa using hfrnd, ?_, hnc⟩
  intro x hx
  have hx' := List.all_eq_true.mp hdisj x hx
  simpa using hx'

/-- Replacing an assign-form call by a fresh result-binding block preserves
all outcomes, including a halt during the call. -/
theorem freshenCore_equiv_of (P : String) (xs : List Ident) (f : Ident)
    (as : List (Expr Op))
    (hlen : (freshRets P xs.length).length = xs.length)
    (hnd : (freshRets P xs.length).Nodup)
    (hdisj : ∀ x ∈ xs, x ∉ freshRets P xs.length)
    (hnc : argsHaveCall as = false) :
    EquivStmt D (.assign xs (.call f as)) (freshenCore P xs f as) := by
  let frs := freshRets P xs.length
  intro funs V st V' st' o
  constructor
  · intro h
    cases h with
    | @assignVal _ _ _ _ _ vals st1 hcall hvals =>
        have hvals' : vals.length = frs.length := hvals.trans hlen.symm
        have hlet : Step D ([] :: funs) V st
            (.stmt (.letDecl frs (some (.call f as))))
            (.sres (frs.zip vals ++ V) st' .normal) :=
          Step.letVal (call_emptyScope_fwd hcall hnc) hvals'
        have hkeys : (frs.zip vals).map Prod.fst = frs :=
          List.map_fst_zip (le_of_eq hvals'.symm)
        have hassigns := assigns_fwd (A' := (frs.zip vals : VEnv D))
          (xs := xs) (rs := frs)
          (fun r hr => by rw [hkeys]; exact hr)
          (fun x hx => by rw [hkeys]; exact hdisj x hx)
          hlen.symm ([] :: funs) V st'
        rw [zip_gets_eq hnd hvals'] at hassigns
        have hseq := Step.seqCons hlet hassigns
        have hseq' : Step D (hoist D
            (.letDecl frs (some (.call f as)) ::
              (xs.zip frs).map (fun xr => .assign [xr.1] (.var xr.2))) :: funs) V st
            (.stmts (.letDecl frs (some (.call f as)) ::
              (xs.zip frs).map (fun xr => .assign [xr.1] (.var xr.2))))
            (.sres (frs.zip vals ++ VEnv.setMany V xs vals) st' .normal) := by
          simpa [hoist] using hseq
        have hb := Step.block (funs := funs) hseq'
        have hrestore : restore V
            (frs.zip vals ++ VEnv.setMany V xs vals) = VEnv.setMany V xs vals :=
          restore_exact (VEnv.setMany_length _ _ _)
        rw [hrestore] at hb
        simpa [freshenCore, frs, hoist] using hb
    | @assignHalt _ _ _ _ _ st1 hcall =>
        have hlet : Step D ([] :: funs) V st
            (.stmt (.letDecl frs (some (.call f as)))) (.sres V st' .halt) :=
          Step.letHalt (call_emptyScope_fwd hcall hnc)
        have hseq : Step D ([] :: funs) V st
            (.stmts (.letDecl frs (some (.call f as)) ::
              (xs.zip frs).map (fun xr => .assign [xr.1] (.var xr.2))))
            (.sres V st' .halt) := Step.seqStop hlet (by simp)
        have hseq' : Step D (hoist D
            (.letDecl frs (some (.call f as)) ::
              (xs.zip frs).map (fun xr => .assign [xr.1] (.var xr.2))) :: funs) V st
            (.stmts (.letDecl frs (some (.call f as)) ::
              (xs.zip frs).map (fun xr => .assign [xr.1] (.var xr.2))))
            (.sres V st' .halt) := by
          simpa [hoist] using hseq
        have hb := Step.block (funs := funs) hseq'
        simpa [freshenCore, frs, hoist, restore] using hb
  · intro h
    change Step D funs V st (.stmt (.block
      (.letDecl frs (some (.call f as)) ::
        (xs.zip frs).map (fun xr => .assign [xr.1] (.var xr.2))))) _ at h
    cases h with
    | block hb =>
      simp [hoist] at hb
      cases hb with
      | seqCons hlet hassigns =>
          cases hlet with
          | @letVal _ _ _ _ _ vals st1 hcall hvals =>
              have hkeys : (frs.zip vals).map Prod.fst = frs :=
                List.map_fst_zip (le_of_eq hvals.symm)
              obtain ⟨hVr, hst, ho⟩ := assigns_bwd hassigns
                (fun r hr => by rw [hkeys]; exact hr)
                (fun x hx => by rw [hkeys]; exact hdisj x hx) hlen.symm
              subst hst
              subst ho
              rw [zip_gets_eq hnd hvals] at hVr
              have hrestore : restore V (frs.zip vals ++ VEnv.setMany V xs vals) =
                  VEnv.setMany V xs vals := restore_exact (VEnv.setMany_length _ _ _)
              rw [hVr, hrestore]
              exact Step.assignVal (call_emptyScope_bwd hcall hnc)
                (hvals.trans hlen)
      | seqStop hlet hne =>
          cases hlet with
          | letVal hcall hvals => exact absurd rfl hne
          | letHalt hcall =>
              simpa [restore] using Step.assignHalt (call_emptyScope_bwd hcall hnc)

private theorem freshenCore_equiv (P : String) (xs : List Ident) (f : Ident)
    (as : List (Expr Op)) (d : IDecl)
    (hw : freshenWanted d xs (freshRets P xs.length) as = true) :
    EquivStmt D (.assign xs (.call f as)) (freshenCore P xs f as) := by
  obtain ⟨hlen, hnd, hdisj, hnc⟩ := freshenWanted_inv hw
  exact freshenCore_equiv_of P xs f as hlen hnd hdisj hnc

/-! ### The traversal (Δ mirrors `InlineCalls` exactly) -/

mutual

/-- Freshen through one statement. Only the assign-call form rewrites. -/
def fcStmt (P : String) (Δ : DEnv) : Stmt Op → Stmt Op
  | .assign xs (.call f as) =>
      match lookupDelta Δ f with
      | some d =>
          if freshenWanted d xs (freshRets P xs.length) as then freshenCore P xs f as
          else .assign xs (.call f as)
      | none => .assign xs (.call f as)
  | .block body => .block (fcBlock P Δ body)
  | .funDef n ps rs body => .funDef n ps rs (fcBlock P Δ body)
  | .cond c body => .cond c (fcBlock P Δ body)
  | .switch c cases dflt => .switch c (fcCases P Δ cases) (fcDflt P Δ dflt)
  | .forLoop init c post body =>
      let ΔL := Δ.filter (fun p => !(definedFuns init).contains p.1)
      .forLoop init c (fcBlock P ΔL post) (fcBlock P ΔL body)
  | s => s

/-- Freshen through a statement sequence (already under its block's `Δ`). -/
def fcStmts (P : String) (Δ : DEnv) : List (Stmt Op) → List (Stmt Op)
  | [] => []
  | s :: rest => fcStmt P Δ s :: fcStmts P Δ rest

/-- Enter a block: extend `Δ` with its hoisted declarations. -/
def fcBlock (P : String) (Δ : DEnv) (body : List (Stmt Op)) : List (Stmt Op) :=
  fcStmts P (deltaExtend Δ body) body

/-- Freshen through `switch` case bodies. -/
def fcCases (P : String) (Δ : DEnv) :
    List (Literal × Block Op) → List (Literal × Block Op)
  | [] => []
  | (l, b) :: rest => (l, fcBlock P Δ b) :: fcCases P Δ rest

/-- Freshen through a `switch` default. -/
def fcDflt (P : String) (Δ : DEnv) : Option (Block Op) → Option (Block Op)
  | none => none
  | some b => some (fcBlock P Δ b)

end

/-! ### Traversal soundness -/

private theorem fcFunDef_equiv (n : Ident) (ps rs : List Ident)
    (b b' : Block Op) :
    EquivStmt D (.funDef n ps rs b) (.funDef n ps rs b') := by
  intro funs V st V' st' o
  constructor <;> intro h <;> cases h <;> exact Step.funDef

mutual

private theorem fcStmt_equiv (P : String) (Δ : DEnv) :
    ∀ s : Stmt Op, EquivStmt D s (fcStmt P Δ s)
  | .block body =>
      by
        rw [fcStmt]
        change EquivBlock D body (fcBlock P Δ body)
        simpa [fcBlock] using
          (EquivBlock.of_stmts_funs
            (EquivStmts.of_forall₂ (fcStmts_forall2 P (deltaExtend Δ body) body))
            (fcScopeRel P (deltaExtend Δ body) body))
  | .funDef n ps rs body => by
      simpa [fcStmt] using fcFunDef_equiv n ps rs body (fcBlock P Δ body)
  | .letDecl xs v => by simpa [fcStmt] using (EquivStmt.refl (.letDecl xs v) :
      EquivStmt D _ _)
  | .assign xs (.call f as) => by
      simp only [fcStmt]
      split
      · next d hd =>
          split
          · next hw => exact freshenCore_equiv P xs f as d hw
          · exact EquivStmt.refl _
      · exact EquivStmt.refl _
  | .assign xs (.lit l) => by simpa [fcStmt] using
      (EquivStmt.refl (.assign xs (.lit l)) : EquivStmt D _ _)
  | .assign xs (.var x) => by simpa [fcStmt] using
      (EquivStmt.refl (.assign xs (.var x)) : EquivStmt D _ _)
  | .assign xs (.builtin op as) => by simpa [fcStmt] using
      (EquivStmt.refl (.assign xs (.builtin op as)) : EquivStmt D _ _)
  | .cond c body =>
      by
        simpa [fcStmt, fcBlock] using
          (EquivStmt.cond_congr (EquivExpr.refl c)
            (EquivBlock.of_stmts_funs
              (EquivStmts.of_forall₂ (fcStmts_forall2 P (deltaExtend Δ body) body))
              (fcScopeRel P (deltaExtend Δ body) body)))
  | .switch c cases dflt =>
      by
        simpa [fcStmt] using
          (EquivStmt.switch_congr (EquivExpr.refl c)
            (fcCases_forall2 P Δ cases) (fcDflt_equiv P Δ dflt))
  | .forLoop init c post body => by
      let ΔL := Δ.filter (fun p => !(definedFuns init).contains p.1)
      simpa [fcStmt, fcBlock, ΔL] using
        (EquivStmt.forLoop_congr init (EquivExpr.refl c)
          (EquivBlock.of_stmts_funs
            (EquivStmts.of_forall₂ (fcStmts_forall2 P (deltaExtend ΔL post) post))
            (fcScopeRel P (deltaExtend ΔL post) post))
          (EquivBlock.of_stmts_funs
            (EquivStmts.of_forall₂ (fcStmts_forall2 P (deltaExtend ΔL body) body))
            (fcScopeRel P (deltaExtend ΔL body) body)))
  | .exprStmt e => by simpa [fcStmt] using
      (EquivStmt.refl (.exprStmt e) : EquivStmt D _ _)
  | .break => by simpa [fcStmt] using (EquivStmt.refl .break : EquivStmt D _ _)
  | .continue => by simpa [fcStmt] using (EquivStmt.refl .continue : EquivStmt D _ _)
  | .leave => by simpa [fcStmt] using (EquivStmt.refl .leave : EquivStmt D _ _)

private theorem fcStmts_forall2 (P : String) (Δ : DEnv) :
    ∀ ss : List (Stmt Op), List.Forall₂ (EquivStmt D) ss (fcStmts P Δ ss)
  | [] => by rw [fcStmts]; exact .nil
  | s :: rest => by
      simpa [fcStmts] using List.Forall₂.cons
        (fcStmt_equiv P Δ s) (fcStmts_forall2 P Δ rest)

private theorem fcCases_forall2 (P : String) (Δ : DEnv) :
    ∀ cs : List (Literal × Block Op),
      List.Forall₂ (fun p q => p.1 = q.1 ∧ EquivBlock D p.2 q.2)
        cs (fcCases P Δ cs)
  | [] => by rw [fcCases]; exact .nil
  | (l, b) :: rest => by
      rw [fcCases]
      have hb : EquivBlock D b (fcBlock P Δ b) := by
        simpa [fcBlock] using
          (EquivBlock.of_stmts_funs
            (EquivStmts.of_forall₂ (fcStmts_forall2 P (deltaExtend Δ b) b))
            (fcScopeRel P (deltaExtend Δ b) b))
      exact List.Forall₂.cons ⟨rfl, hb⟩ (fcCases_forall2 P Δ rest)

private theorem fcDflt_equiv (P : String) (Δ : DEnv) :
    ∀ dflt : Option (Block Op), EquivBlock D (dflt.getD []) ((fcDflt P Δ dflt).getD [])
  | none => by simpa [fcDflt] using (EquivBlock.refl [] : EquivBlock D _ _)
  | some b => by
      rw [fcDflt]
      simpa [fcBlock] using
        (EquivBlock.of_stmts_funs
          (EquivStmts.of_forall₂ (fcStmts_forall2 P (deltaExtend Δ b) b))
          (fcScopeRel P (deltaExtend Δ b) b))

private theorem fcScopeRel (P : String) (Δ : DEnv) :
    ∀ ss : List (Stmt Op), ScopeRel D (hoist D ss) (hoist D (fcStmts P Δ ss))
  | [] => by simpa [fcStmts, hoist] using (ScopeRel.refl ([] : FScope D))
  | .funDef n ps rs body :: rest => by
      rw [fcStmts, fcStmt]
      simp only [hoist, List.filterMap_cons]
      have hb : EquivBlock D body (fcBlock P Δ body) := by
        simpa [fcBlock] using
          (EquivBlock.of_stmts_funs
            (EquivStmts.of_forall₂ (fcStmts_forall2 P (deltaExtend Δ body) body))
            (fcScopeRel P (deltaExtend Δ body) body))
      exact .cons ⟨rfl, rfl, rfl, hb⟩ (fcScopeRel P Δ rest)
  | .block _ :: rest => by simpa [fcStmts, fcStmt, hoist] using fcScopeRel P Δ rest
  | .letDecl _ _ :: rest => by simpa [fcStmts, fcStmt, hoist] using fcScopeRel P Δ rest
  | .assign xs (.call f as) :: rest => by
      simp only [fcStmts, fcStmt]
      split
      · split <;> simpa [freshenCore, hoist] using fcScopeRel P Δ rest
      · simpa [hoist] using fcScopeRel P Δ rest
  | .assign _ (.lit _) :: rest => by
      simpa [fcStmts, fcStmt, hoist] using fcScopeRel P Δ rest
  | .assign _ (.var _) :: rest => by
      simpa [fcStmts, fcStmt, hoist] using fcScopeRel P Δ rest
  | .assign _ (.builtin _ _) :: rest => by
      simpa [fcStmts, fcStmt, hoist] using fcScopeRel P Δ rest
  | .cond _ _ :: rest => by simpa [fcStmts, fcStmt, hoist] using fcScopeRel P Δ rest
  | .switch _ _ _ :: rest => by simpa [fcStmts, fcStmt, hoist] using fcScopeRel P Δ rest
  | .forLoop _ _ _ _ :: rest => by
      simpa [fcStmts, fcStmt, hoist] using fcScopeRel P Δ rest
  | .exprStmt _ :: rest => by simpa [fcStmts, fcStmt, hoist] using fcScopeRel P Δ rest
  | .break :: rest => by simpa [fcStmts, fcStmt, hoist] using fcScopeRel P Δ rest
  | .continue :: rest => by simpa [fcStmts, fcStmt, hoist] using fcScopeRel P Δ rest
  | .leave :: rest => by simpa [fcStmts, fcStmt, hoist] using fcScopeRel P Δ rest

end

/-- The pass entry point: pick the fresh prefix from the whole block's
identifier set (declining when none is found — impossible, but total). -/
def freshenCallsBlock (b : Block Op) : Block Op :=
  match freshPrefix (stmtsIdents b) with
  | some P => fcBlock P [] b
  | none => b

/-- The **FreshenCalls pass**: collision unblocking for `InlineCalls`
(for assign-form result-name collisions). -/
def freshenCalls : Pass D where
  run := freshenCallsBlock
  sound := fun b => by
    unfold freshenCallsBlock
    split
    · next p hp =>
        simpa [fcBlock] using
          (EquivBlock.of_stmts_funs
            (EquivStmts.of_forall₂ (fcStmts_forall2 p (deltaExtend [] b) b))
            (fcScopeRel p (deltaExtend [] b) b))
    · exact EquivBlock.refl _

@[simp] theorem freshenCalls_run (b : Block Op) :
    (freshenCalls (calls := calls) (creates := creates)).run b =
      freshenCallsBlock b := rfl

end YulEvmCompiler.Optimizer
