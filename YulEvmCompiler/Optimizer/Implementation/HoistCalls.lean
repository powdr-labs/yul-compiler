import YulEvmCompiler.Optimizer.Implementation.FreshenCalls
set_option warningAsError true
/-!
# YulEvmCompiler.Optimizer.Implementation.HoistCalls

Hoist a direct unary nested call out of an assignment-call argument.  This is
the smallest argument normalization needed by Solidity's storage cleanup
chains: `x := f(g(args))` becomes `{ let fresh := g(args); x := f(fresh) }`.
The fresh name and both inlineability gates ensure the following
`FreshenCalls → InlineCalls` stages can consume the temporary and calls.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM

variable {calls : ExternalCalls} {creates : ExternalCreates}
local notation "D" => evmWithExternal calls creates

def hoistedArg (P : String) : Ident := s!"{P}a"

def hoistUnaryWanted (P : String) (outer inner : IDecl)
    (xs : List Ident) (gas : List (Expr Op)) : Bool :=
  let t := hoistedArg P
  inlineOK outer && inlineOK inner && !argsHaveCall gas &&
    siteOK inner [t] gas true &&
    (siteOK outer xs [.var t] false ||
      freshenWanted outer xs (freshRets P xs.length) [.var t]) &&
    !xs.contains t

def hoistUnaryCore (P : String) (xs : List Ident) (f g : Ident)
    (gas : List (Expr Op)) : Stmt Op :=
  let t := hoistedArg P
  .block [.letDecl [t] (some (.call g gas)),
    .assign xs (.call f [.var t])]

theorem hoistUnaryWanted_inv {P : String} {outer inner : IDecl}
    {xs : List Ident} {gas : List (Expr Op)}
    (h : hoistUnaryWanted P outer inner xs gas = true) :
    argsHaveCall gas = false ∧ hoistedArg P ∉ xs := by
  simp only [hoistUnaryWanted, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨_, _⟩, hnc⟩, _⟩, _⟩, htx⟩ := h
  exact ⟨by simpa using hnc, by simpa using htx⟩

theorem hoistUnaryCore_equiv_of (P : String) (xs : List Ident) (f g : Ident)
    (gas : List (Expr Op)) (hnc : argsHaveCall gas = false)
    (htx : hoistedArg P ∉ xs) :
    EquivStmt D (.assign xs (.call f [.call g gas]))
      (hoistUnaryCore P xs f g gas) := by
  let t := hoistedArg P
  intro funs V st V' st' o
  constructor
  · intro h
    cases h with
    | assignVal houter hxs =>
        cases houter with
        | @callOk _ _ _ _ _ _ stArgs decl _ Vend _ _ hargs hl harity hbody hout =>
            cases hargs with
            | @argsCons _ _ _ _ _ _ _ v stInner hnil hinner =>
                cases hnil
                have hinner' := call_emptyScope_fwd hinner hnc
                have hlet : Step D ([] :: funs) V st
                    (.stmt (.letDecl [t] (some (.call g gas))))
                    (.sres ((t, v) :: V) stArgs .normal) := Step.letVal hinner' rfl
                have hargs' : Step D ([] :: funs) ((t, v) :: V) stArgs
                    (.args [.var t]) (.eres (.vals [v] stArgs)) :=
                  Step.argsCons Step.argsNil (Step.var (by simp [VEnv.get]))
                have hcall' := Step.callOk hargs'
                  (by simpa [lookupFun] using hl) harity hbody hout
                have hassign' := Step.assignVal hcall' hxs
                have hseq := Step.seqCons hlet
                  (Step.seqCons hassign' Step.seqNil)
                have hb := Step.block (funs := funs)
                  (body := [.letDecl [t] (some (.call g gas)),
                    .assign xs (.call f [.var t])])
                  (by simpa [hoist] using hseq)
                rw [VEnv.setMany_cons_not_mem htx] at hb
                have hrestore : restore V
                    ((t, v) :: VEnv.setMany V xs
                      (decl.rets.map (fun r => (VEnv.get Vend r).getD
                        (evmWithExternal calls creates).zero))) =
                    VEnv.setMany V xs
                      (decl.rets.map (fun r => (VEnv.get Vend r).getD
                        (evmWithExternal calls creates).zero)) := by
                  simpa using (restore_exact (calls := calls) (creates := creates)
                    (W := V) (Y := [(t, v)])
                    (W' := VEnv.setMany V xs
                      (decl.rets.map (fun r => (VEnv.get Vend r).getD
                        (evmWithExternal calls creates).zero)))
                    (VEnv.setMany_length _ _ _))
                rw [hrestore] at hb
                simpa [hoistUnaryCore, t] using hb
    | assignHalt houter =>
        cases houter with
        | @callHalt _ _ _ _ _ _ stArgs _ _ _ _ hargs hl harity hbody =>
            cases hargs with
            | @argsCons _ _ _ _ _ _ _ v stInner hnil hinner =>
                cases hnil
                have hinner' := call_emptyScope_fwd hinner hnc
                have hlet : Step D ([] :: funs) V st
                    (.stmt (.letDecl [t] (some (.call g gas))))
                    (.sres ((t, v) :: V) stArgs .normal) := Step.letVal hinner' rfl
                have hargs' : Step D ([] :: funs) ((t, v) :: V) stArgs
                    (.args [.var t]) (.eres (.vals [v] stArgs)) :=
                  Step.argsCons Step.argsNil (Step.var (by simp [VEnv.get]))
                have hcall' := Step.callHalt hargs'
                  (by simpa [lookupFun] using hl) harity hbody
                have hassign' := Step.assignHalt (vars := xs) hcall'
                have hseq := Step.seqCons hlet
                  (Step.seqStop (rest := []) hassign' (by decide))
                have hb := Step.block (funs := funs)
                  (body := [.letDecl [t] (some (.call g gas)),
                    .assign xs (.call f [.var t])])
                  (by simpa [hoist] using hseq)
                simpa [hoistUnaryCore, t, restore] using hb
        | callArgsHalt hargs =>
            cases hargs with
            | argsRestHalt hnil => cases hnil
            | argsHeadHalt hnil hinner =>
                cases hnil
                have hlet := Step.letHalt (vars := [t])
                  (call_emptyScope_fwd hinner hnc)
                have hseq := Step.seqStop
                  (rest := [.assign xs (.call f [.var t])]) hlet (by decide)
                have hb := Step.block (funs := funs)
                  (body := [.letDecl [t] (some (.call g gas)),
                    .assign xs (.call f [.var t])])
                  (by simpa [hoist] using hseq)
                simpa [hoistUnaryCore, t, restore] using hb
  · intro h
    change Step D funs V st (.stmt (.block
      [.letDecl [t] (some (.call g gas)),
       .assign xs (.call f [.var t])])) _ at h
    cases h with
    | block hb =>
      simp only [hoist, List.filterMap_cons, List.filterMap_nil] at hb
      cases hb with
      | seqCons hlet hrest =>
          cases hlet with
          | @letVal _ _ _ _ _ vals stInner hinner hlen =>
              have hinner0 := call_emptyScope_bwd hinner hnc
              cases vals with
              | nil => simp at hlen
              | cons v vals =>
                cases vals with
                | cons w vals => simp at hlen
                | nil =>
                  cases hrest with
                  | seqCons hassign hnil =>
                    cases hnil
                    cases hassign with
                    | assignVal houter hxs =>
                      cases houter with
                      | @callOk _ _ _ _ _ _ _ decl _ Vend _ _
                          hargs hl harity hbody hout =>
                        cases hargs with
                        | @argsCons _ _ _ _ _ _ _ vOuter _ hnil hvar =>
                          cases hnil
                          cases hvar with
                          | var hv =>
                          have hvv : v = vOuter := by simpa [VEnv.get] using hv
                          subst vOuter
                          have hargs0 := Step.argsCons Step.argsNil («D» := D) hinner0
                          have hcall0 := Step.callOk hargs0
                            (by simpa [lookupFun] using hl) harity hbody hout
                          have hassign0 := Step.assignVal hcall0 hxs
                          have hrestore : restore V
                              ((t, v) :: VEnv.setMany V xs
                                (List.map (fun r => (VEnv.get Vend r).getD
                                  (evmWithExternal calls creates).zero) decl.rets)) =
                              VEnv.setMany V xs
                                (List.map (fun r => (VEnv.get Vend r).getD
                                  (evmWithExternal calls creates).zero) decl.rets) := by
                            simpa using (restore_exact (calls := calls)
                              (creates := creates) (W := V) (Y := [(t, v)])
                              (W' := VEnv.setMany V xs
                                (decl.rets.map (fun r => (VEnv.get Vend r).getD
                                  (evmWithExternal calls creates).zero)))
                              (VEnv.setMany_length _ _ _))
                          simp only [List.zip, List.zipWith_cons_cons,
                            List.zipWith_nil_left, List.singleton_append]
                          rw [VEnv.setMany_cons_not_mem htx, hrestore]
                          exact hassign0
                  | seqStop hassign hne =>
                    cases hassign with
                    | assignVal _ _ => exact absurd rfl hne
                    | assignHalt houter =>
                      cases houter with
                      | callHalt hargs hl harity hbody =>
                        cases hargs with
                        | @argsCons _ _ _ _ _ _ _ vOuter _ hnil hvar =>
                          cases hnil
                          cases hvar with
                          | var hv =>
                          have hvv : v = vOuter := by simpa [VEnv.get] using hv
                          subst vOuter
                          have hargs0 := Step.argsCons Step.argsNil («D» := D) hinner0
                          have hcall0 := Step.callHalt hargs0
                            (by simpa [lookupFun] using hl) harity hbody
                          simpa [restore] using
                            (Step.assignHalt (vars := xs) hcall0)
                      | callArgsHalt hargs =>
                        cases hargs with
                        | argsRestHalt hnil => cases hnil
                        | argsHeadHalt hnil hvar => cases hnil; cases hvar
      | seqStop hlet hne =>
          cases hlet with
          | letVal _ _ => exact absurd rfl hne
          | letHalt hinner =>
            have hinner0 := call_emptyScope_bwd hinner hnc
            have hnil : Step D funs V st (.args [])
                (.eres (.vals [] st)) := Step.argsNil
            have hargs0 := Step.argsHeadHalt hnil hinner0
            have hcall0 := Step.callArgsHalt (fn := f) hargs0
            simpa [restore] using (Step.assignHalt (vars := xs) hcall0)

/-! ### Hoisting a call out of a builtin write argument

solc's ABI encoders end at a write `op(pos, cleanup_T(value))` — a bare-variable
position and a *nested* helper call as the (last) builtin argument. When the
cleanup body is a single flat built-in (`and(v, mask)`) `InlineHelpers` inlines
it in place; when it is a *nested* built-in (`cleanup_t_bool = iszero(iszero v)`)
`InlineHelpers` cannot ingest it, so the call survives in argument position where
the statement-level `InlineCalls` never reaches it — permanently pinning the whole
encode chain (`abi_encode_t_bool` → `abi_encode_tuple_t_bool` → external) out of
line. Hoisting the nested call to a preceding `let` exposes it to
`FreshenCalls`/`InlineCalls`, collapsing the chain. Yul evaluates arguments
right-to-left, so the trailing argument is the first sub-expression evaluated;
lifting it out of the write therefore preserves evaluation order. -/

/-- Reading a variable through a fresh cons is the same as reading it below. -/
private theorem get_cons_fresh {t p : Ident} (hpt : t ≠ p) (w : U256) (W : VEnv D) :
    VEnv.get ((t, w) :: W) p = VEnv.get W p := by
  simp only [VEnv.get, List.find?_cons]
  by_cases h : ((t, w).fst = p)
  · exact absurd h hpt
  · simp [h]

/-- The hoisted form of a binary builtin write whose last argument is a call:
`op(pos, g(gas))` ⟶ `{ let t := g(gas); op(pos, t) }`. -/
def hoistBuiltinArg (P : String) (op : Op) (p g : Ident) (gas : List (Expr Op)) :
    Stmt Op :=
  let t := hoistedArg P
  .block [.letDecl [t] (some (.call g gas)),
    .exprStmt (.builtin op [.var p, .var t])]

/-- Pure, total, state-independent ops (arithmetic/bitwise/comparison) — the
`pureTotalArity` domain. Used only as a proof-free profitability gate. -/
def hoistPureOp : Op → Bool
  | .add | .sub | .mul | .div | .sdiv | .mod | .smod
  | .signextend | .lt | .gt | .slt | .sgt | .eq
  | .and | .or | .xor | .byte | .shl | .shr | .sar
  | .clz | .iszero | .not | .addmod | .mulmod => true
  | _ => false

mutual
/-- A pure, total, call-free expression tree over `bound`. Matches the
`cleanup_t_*` shape (`iszero(iszero(v))`, `and(v, mask)`) `InlineHelpers` would
inline but for the nested-builtin case. -/
def hoistPureExpr (bound : List Ident) : Expr Op → Bool
  | .lit _ => true
  | .var x => bound.contains x
  | .builtin op args => hoistPureOp op && hoistPureExprs bound args
  | .call _ _ => false
def hoistPureExprs (bound : List Ident) : List (Expr Op) → Bool
  | [] => true
  | e :: rest => hoistPureExpr bound e && hoistPureExprs bound rest
end

/-- The callee body is a single assignment of a pure-total expression over its
parameters/returns — a "cleanup"-style scalar transform. Excludes effectful or
multi-statement helpers (storage readers, struct/array copiers, allocators)
whose inlining grows loop/codec frames (measured: aave `PositionStatusMap`
loops and semantic array/storage codecs blew up when those were hoisted). -/
def hoistInnerPure (d : IDecl) : Bool :=
  match d.ss with
  | [.assign _ e] => hoistPureExpr (d.ps ++ d.rs) e
  | _ => false

/-- Fire the builtin-argument hoist only when the freshly bound call is a
pure-total single-expression cleanup (so `InlineCalls` consumes it next and the
chain collapses without frame blowups), its arguments are call-free, and the
fresh temporary is distinct from the position variable. -/
def hoistBuiltinWanted (P : String) (inner : IDecl) (p : Ident)
    (gas : List (Expr Op)) : Bool :=
  let t := hoistedArg P
  !gas.isEmpty && hoistInnerPure inner &&
  inlineOK inner && !argsHaveCall gas && siteOK inner [t] gas true && !(p == t)

theorem hoistBuiltinWanted_inv {P : String} {inner : IDecl} {p : Ident}
    {gas : List (Expr Op)} (h : hoistBuiltinWanted P inner p gas = true) :
    argsHaveCall gas = false ∧ hoistedArg P ≠ p := by
  simp only [hoistBuiltinWanted, Bool.and_eq_true] at h
  obtain ⟨⟨⟨_, hnc⟩, _⟩, hpt⟩ := h
  refine ⟨by simpa using hnc, ?_⟩
  intro he
  simp [← he] at hpt

/-- Soundness of the builtin-argument hoist: the write and its hoisted form
execute identically from every configuration. -/
theorem hoistBuiltinArg_equiv_of (P : String) (op : Op) (p g : Ident)
    (gas : List (Expr Op)) (hnc : argsHaveCall gas = false)
    (hpt : hoistedArg P ≠ p) :
    EquivStmt D (.exprStmt (.builtin op [.var p, .call g gas]))
      (hoistBuiltinArg P op p g gas) := by
  set t := hoistedArg P with ht
  intro funs V st V' st' o
  have hzip : ∀ w : U256, restore V ([t].zip [w] ++ V) = V := fun w =>
    restore_exact (calls := calls) (creates := creates)
      (W := V) (Y := [t].zip [w]) (W' := V) rfl
  have hcons : ∀ w : U256, restore V ((t, w) :: V) = V := fun w =>
    restore_exact (calls := calls) (creates := creates)
      (W := V) (Y := [(t, w)]) (W' := V) rfl
  constructor
  · intro h
    cases h with
    | @exprStmt _ _ _ _ sout hexpr =>
        cases hexpr with
        | @builtinOk _ _ _ _ _ argvals sA rets sB hargs hb =>
            cases hargs with
            | @argsCons _ _ _ _ _ rvP sMid vP sHead hrestP hheadP =>
                cases hheadP with
                | var hvp =>
                    cases hrestP with
                    | @argsCons _ _ _ _ _ rvC sInC vC sCall hrestC hcall =>
                        cases hrestC with
                        | argsNil =>
                            have hcall' := call_emptyScope_fwd hcall hnc
                            have hlet := Step.letVal (vars := [t]) hcall' rfl
                            have ht_get : VEnv.get ((t, vC) :: V) t = some vC := by
                              simp [VEnv.get]
                            have hp_get : VEnv.get ((t, vC) :: V) p = some vP := by
                              rw [get_cons_fresh hpt]; exact hvp
                            have hexpr' := Step.exprStmt (Step.builtinOk
                              (Step.argsCons
                                (Step.argsCons (Step.argsNil (funs := [] :: funs))
                                  (Step.var ht_get))
                                (Step.var hp_get)) hb)
                            have hseq := Step.seqCons hlet
                              (Step.seqCons hexpr' Step.seqNil)
                            have hblk := Step.block (funs := funs)
                              (body := [.letDecl [t] (some (.call g gas)),
                                .exprStmt (.builtin op [.var p, .var t])])
                              (by simpa [hoist] using hseq)
                            rw [hcons] at hblk
                            simpa [hoistBuiltinArg, ht] using hblk
    | @exprStmtHalt _ _ _ _ sout hexpr =>
        cases hexpr with
        | @builtinHalt _ _ _ _ _ argvals sA sB hargs hb =>
            cases hargs with
            | @argsCons _ _ _ _ _ rvP sMid vP sHead hrestP hheadP =>
                cases hheadP with
                | var hvp =>
                    cases hrestP with
                    | @argsCons _ _ _ _ _ rvC sInC vC sCall hrestC hcall =>
                        cases hrestC with
                        | argsNil =>
                            have hcall' := call_emptyScope_fwd hcall hnc
                            have hlet := Step.letVal (vars := [t]) hcall' rfl
                            have ht_get : VEnv.get ((t, vC) :: V) t = some vC := by
                              simp [VEnv.get]
                            have hp_get : VEnv.get ((t, vC) :: V) p = some vP := by
                              rw [get_cons_fresh hpt]; exact hvp
                            have hexpr' := Step.exprStmtHalt (Step.builtinHalt
                              (Step.argsCons
                                (Step.argsCons (Step.argsNil (funs := [] :: funs))
                                  (Step.var ht_get))
                                (Step.var hp_get)) hb)
                            have hseq := Step.seqCons hlet
                              (Step.seqStop (rest := []) hexpr' (by decide))
                            have hblk := Step.block (funs := funs)
                              (body := [.letDecl [t] (some (.call g gas)),
                                .exprStmt (.builtin op [.var p, .var t])])
                              (by simpa [hoist] using hseq)
                            rw [hcons] at hblk
                            simpa [hoistBuiltinArg, ht] using hblk
        | builtinArgsHalt hargs =>
            cases hargs with
            | argsRestHalt hrest =>
                cases hrest with
                | argsRestHalt hrest2 => cases hrest2
                | argsHeadHalt hrest2 hcall =>
                    cases hrest2 with
                    | argsNil =>
                        have hcall' := call_emptyScope_fwd hcall hnc
                        have hlet := Step.letHalt (vars := [t]) hcall'
                        have hseq := Step.seqStop
                          (rest := [.exprStmt (.builtin op [.var p, .var t])])
                          hlet (by decide)
                        have hblk := Step.block (funs := funs)
                          (body := [.letDecl [t] (some (.call g gas)),
                            .exprStmt (.builtin op [.var p, .var t])])
                          (by simpa [hoist] using hseq)
                        simpa [hoistBuiltinArg, ht, restore] using hblk
            | argsHeadHalt hrest hhead => cases hhead
  · intro h
    change Step D funs V st (.stmt (.block
      [.letDecl [t] (some (.call g gas)),
       .exprStmt (.builtin op [.var p, .var t])])) _ at h
    cases h with
    | block hb =>
        simp only [hoist, List.filterMap_cons, List.filterMap_nil] at hb
        cases hb with
        | seqCons hlet hrest =>
            cases hlet with
            | @letVal _ _ _ _ _ vals st1 hcall hlen =>
                cases vals with
                | nil => simp at hlen
                | cons vg vals =>
                    cases vals with
                    | cons w vals => simp at hlen
                    | nil =>
                        have hcall0 := call_emptyScope_bwd hcall hnc
                        cases hrest with
                        | seqCons hexpr hnil =>
                            cases hnil with
                            | seqNil =>
                                cases hexpr with
                                | @exprStmt _ _ _ _ stb hb2 =>
                                    cases hb2 with
                                    | @builtinOk _ _ _ _ _ argvals sA rets sB hargs2 hbb =>
                                        cases hargs2 with
                                        | @argsCons _ _ _ _ _ rvs2 sM2 vp2 sH2 hrp hhp =>
                                            cases hhp with
                                            | var hvp2 =>
                                                cases hrp with
                                                | @argsCons _ _ _ _ _ rvs3 sM3 vt sH3 hrt hht =>
                                                    cases hrt with
                                                    | argsNil =>
                                                        cases hht with
                                                        | var hvt =>
                                                            have hvtv : vg = vt := by
                                                              simpa [VEnv.get] using hvt
                                                            have hvpV :
                                                                VEnv.get V p = some vp2 := by
                                                              rw [← get_cons_fresh hpt vg V]
                                                              exact hvp2
                                                            have hargs :=
                                                              Step.argsCons
                                                                (Step.argsCons
                                                                  (Step.argsNil (funs := funs)
                                                                    (V := V) (st := st))
                                                                  (hvtv ▸ hcall0))
                                                                (Step.var hvpV)
                                                            have := Step.exprStmt
                                                              (Step.builtinOk hargs hbb)
                                                            rw [hzip]
                                                            exact this
                        | seqStop hexpr hne =>
                            cases hexpr with
                            | exprStmt _ => exact absurd rfl hne
                            | @exprStmtHalt _ _ _ _ stb hb2 =>
                                cases hb2 with
                                | @builtinHalt _ _ _ _ _ argvals sA sB hargs2 hbb =>
                                    cases hargs2 with
                                    | @argsCons _ _ _ _ _ rvs2 sM2 vp2 sH2 hrp hhp =>
                                        cases hhp with
                                        | var hvp2 =>
                                            cases hrp with
                                            | @argsCons _ _ _ _ _ rvs3 sM3 vt sH3 hrt hht =>
                                                cases hrt with
                                                | argsNil =>
                                                    cases hht with
                                                    | var hvt =>
                                                        have hvtv : vg = vt := by
                                                          simpa [VEnv.get] using hvt
                                                        have hvpV :
                                                            VEnv.get V p = some vp2 := by
                                                          rw [← get_cons_fresh hpt vg V]
                                                          exact hvp2
                                                        have hargs :=
                                                          Step.argsCons
                                                            (Step.argsCons
                                                              (Step.argsNil (funs := funs)
                                                                (V := V) (st := st))
                                                              (hvtv ▸ hcall0))
                                                            (Step.var hvpV)
                                                        have := Step.exprStmtHalt
                                                          (Step.builtinHalt hargs hbb)
                                                        rw [hzip]
                                                        exact this
                                | builtinArgsHalt hargs2 =>
                                    cases hargs2 with
                                    | argsRestHalt hrp =>
                                        cases hrp with
                                        | argsRestHalt hrt => cases hrt
                                        | argsHeadHalt hrt hht => cases hht
                                    | argsHeadHalt hrp hhp => cases hhp
        | seqStop hlet hne =>
            cases hlet with
            | letVal _ _ => exact absurd rfl hne
            | @letHalt _ _ _ _ _ st1 hcall =>
                have hcall0 := call_emptyScope_bwd hcall hnc
                have hargs :=
                  Step.argsRestHalt (e := .var p)
                    (Step.argsHeadHalt
                      (Step.argsNil (funs := funs) (V := V) (st := st)) hcall0)
                have hcallhalt := Step.builtinArgsHalt (op := op) hargs
                simpa [restore] using (Step.exprStmtHalt hcallhalt)


/-- Dispatch an expression-statement: hoist a trailing builtin-argument call
when profitable, otherwise leave the statement unchanged. Non-recursive, so
`hcStmt`'s `exprStmt` equation stays unconditional. -/
def hcExprStmt (P : String) (Δ : DEnv) : Expr Op → Stmt Op
  | .builtin op [.var p, .call g gas] =>
      match lookupDelta Δ g with
      | some inner =>
          if hoistBuiltinWanted P inner p gas then hoistBuiltinArg P op p g gas
          else .exprStmt (.builtin op [.var p, .call g gas])
      | none => .exprStmt (.builtin op [.var p, .call g gas])
  | e => .exprStmt e

theorem hcExprStmt_equiv (P : String) (Δ : DEnv) (e : Expr Op) :
    EquivStmt D (.exprStmt e) (hcExprStmt P Δ e) := by
  unfold hcExprStmt
  split
  · next op p g gas =>
      split
      · next inner hlk =>
          split
          · next hw =>
              obtain ⟨hnc, hpt⟩ := hoistBuiltinWanted_inv hw
              exact hoistBuiltinArg_equiv_of P op p g gas hnc hpt
          · exact EquivStmt.refl _
      · exact EquivStmt.refl _
  · exact EquivStmt.refl _

theorem hcExprStmt_shape (P : String) (Δ : DEnv) (e : Expr Op) :
    (∃ b, hcExprStmt P Δ e = .block b) ∨ (∃ e', hcExprStmt P Δ e = .exprStmt e') := by
  unfold hcExprStmt
  split
  · next op p g gas =>
      split
      · next inner hlk =>
          split
          · next hw => exact Or.inl ⟨_, rfl⟩
          · exact Or.inr ⟨_, rfl⟩
      · exact Or.inr ⟨_, rfl⟩
  · exact Or.inr ⟨_, rfl⟩

theorem hoist_cons_hcExprStmt (P : String) (Δ : DEnv) (e : Expr Op)
    (L : List (Stmt Op)) :
    hoist D (hcExprStmt P Δ e :: L) = hoist D L := by
  rcases hcExprStmt_shape P Δ e with
    ⟨b, hb⟩ | ⟨e', hb⟩ <;> rw [hb] <;> simp [hoist]

mutual

def hcStmt (P : String) (Δ : DEnv) : Stmt Op → Stmt Op
  | .assign xs (.call f [.call g gas]) =>
      match lookupDelta Δ f, lookupDelta Δ g with
      | some outer, some inner =>
          if hoistUnaryWanted P outer inner xs gas then
            hoistUnaryCore P xs f g gas
          else .assign xs (.call f [.call g gas])
      | _, _ => .assign xs (.call f [.call g gas])
  | .block body => .block (hcBlock P Δ body)
  | .funDef n ps rs body => .funDef n ps rs (hcBlock P Δ body)
  | .cond c body => .cond c (hcBlock P Δ body)
  | .switch c cases dflt => .switch c (hcCases P Δ cases) (hcDflt P Δ dflt)
  | .forLoop init c post body =>
      let ΔL := Δ.filter (fun p => !(definedFuns init).contains p.1)
      .forLoop init c (hcBlock P ΔL post) (hcBlock P ΔL body)
  | .letDecl xs val => .letDecl xs val
  | .assign xs (.lit l) => .assign xs (.lit l)
  | .assign xs (.var x) => .assign xs (.var x)
  | .assign xs (.builtin op args) => .assign xs (.builtin op args)
  | .assign xs (.call f []) => .assign xs (.call f [])
  | .assign xs (.call f [.lit l]) => .assign xs (.call f [.lit l])
  | .assign xs (.call f [.var x]) => .assign xs (.call f [.var x])
  | .assign xs (.call f [.builtin op args]) => .assign xs (.call f [.builtin op args])
  | .assign xs (.call f (a :: b :: rest)) => .assign xs (.call f (a :: b :: rest))
  | .exprStmt e => hcExprStmt P Δ e
  | .break => .break
  | .continue => .continue
  | .leave => .leave

def hcStmts (P : String) (Δ : DEnv) : List (Stmt Op) → List (Stmt Op)
  | [] => []
  | s :: rest => hcStmt P Δ s :: hcStmts P Δ rest

def hcBlock (P : String) (Δ : DEnv) (body : Block Op) : Block Op :=
  hcStmts P (deltaExtend Δ body) body

def hcCases (P : String) (Δ : DEnv) :
    List (Literal × Block Op) → List (Literal × Block Op)
  | [] => []
  | (l, b) :: rest => (l, hcBlock P Δ b) :: hcCases P Δ rest

def hcDflt (P : String) (Δ : DEnv) : Option (Block Op) → Option (Block Op)
  | none => none
  | some b => some (hcBlock P Δ b)

end

/-! ### Traversal soundness -/

mutual

private theorem hcStmt_equiv (P : String) (Δ : DEnv) :
    ∀ s : Stmt Op, EquivStmt D s (hcStmt P Δ s)
  | .block body => by
      rw [hcStmt]
      change EquivBlock D body (hcBlock P Δ body)
      simpa [hcBlock] using
        (EquivBlock.of_stmts_funs
          (EquivStmts.of_forall₂ (hcStmts_forall2 P (deltaExtend Δ body) body))
          (hcScopeRel P (deltaExtend Δ body) body))
  | .funDef n ps rs body => by
      rw [hcStmt]
      intro funs V st V' st' o
      constructor <;> intro h <;> cases h <;> exact Step.funDef
  | .assign xs (.call f [.call g gas]) => by
      simp only [hcStmt]
      split
      · next outer inner hlookup =>
        split
        · next hw =>
          obtain ⟨hnc, htx⟩ := hoistUnaryWanted_inv hw
          exact hoistUnaryCore_equiv_of P xs f g gas hnc htx
        · exact EquivStmt.refl _
      · exact EquivStmt.refl _
  | .cond c body => by
      simpa [hcStmt, hcBlock] using
        (EquivStmt.cond_congr (EquivExpr.refl («D» := D) c)
          (EquivBlock.of_stmts_funs
            (EquivStmts.of_forall₂ (hcStmts_forall2 P (deltaExtend Δ body) body))
            (hcScopeRel P (deltaExtend Δ body) body)))
  | .switch c cases dflt => by
      simpa [hcStmt] using
        (EquivStmt.switch_congr (EquivExpr.refl («D» := D) c)
          (hcCases_forall2 P Δ cases) (hcDflt_equiv P Δ dflt))
  | .forLoop init c post body => by
      let ΔL := Δ.filter (fun p => !(definedFuns init).contains p.1)
      simpa [hcStmt, hcBlock, ΔL] using
        (EquivStmt.forLoop_congr init (EquivExpr.refl («D» := D) c)
          (EquivBlock.of_stmts_funs
            (EquivStmts.of_forall₂ (hcStmts_forall2 P (deltaExtend ΔL post) post))
            (hcScopeRel P (deltaExtend ΔL post) post))
          (EquivBlock.of_stmts_funs
            (EquivStmts.of_forall₂ (hcStmts_forall2 P (deltaExtend ΔL body) body))
            (hcScopeRel P (deltaExtend ΔL body) body)))
  | .letDecl xs val => by rw [hcStmt]; exact EquivStmt.refl _
  | .assign xs (.lit l) => by rw [hcStmt]; exact EquivStmt.refl _
  | .assign xs (.var x) => by rw [hcStmt]; exact EquivStmt.refl _
  | .assign xs (.builtin op args) => by rw [hcStmt]; exact EquivStmt.refl _
  | .assign xs (.call f []) => by rw [hcStmt]; exact EquivStmt.refl _
  | .assign xs (.call f [.lit l]) => by rw [hcStmt]; exact EquivStmt.refl _
  | .assign xs (.call f [.var x]) => by rw [hcStmt]; exact EquivStmt.refl _
  | .assign xs (.call f [.builtin op args]) => by rw [hcStmt]; exact EquivStmt.refl _
  | .assign xs (.call f (a :: b :: rest)) => by rw [hcStmt]; exact EquivStmt.refl _
  | .exprStmt e => by rw [hcStmt]; exact hcExprStmt_equiv P Δ e
  | .break => by rw [hcStmt]; exact EquivStmt.refl _
  | .continue => by rw [hcStmt]; exact EquivStmt.refl _
  | .leave => by rw [hcStmt]; exact EquivStmt.refl _

private theorem hcStmts_forall2 (P : String) (Δ : DEnv) :
    ∀ ss : List (Stmt Op), List.Forall₂ (EquivStmt D) ss (hcStmts P Δ ss)
  | [] => by rw [hcStmts]; exact .nil
  | s :: rest => by
      simpa [hcStmts] using List.Forall₂.cons
        (hcStmt_equiv P Δ s) (hcStmts_forall2 P Δ rest)

private theorem hcCases_forall2 (P : String) (Δ : DEnv) :
    ∀ cs : List (Literal × Block Op),
      List.Forall₂ (fun p q => p.1 = q.1 ∧ EquivBlock D p.2 q.2)
        cs (hcCases P Δ cs)
  | [] => by rw [hcCases]; exact .nil
  | (l, b) :: rest => by
      rw [hcCases]
      have hb : EquivBlock D b (hcBlock P Δ b) := by
        simpa [hcBlock] using
          (EquivBlock.of_stmts_funs
            (EquivStmts.of_forall₂ (hcStmts_forall2 P (deltaExtend Δ b) b))
            (hcScopeRel P (deltaExtend Δ b) b))
      exact .cons ⟨rfl, hb⟩ (hcCases_forall2 P Δ rest)

private theorem hcDflt_equiv (P : String) (Δ : DEnv) :
    ∀ dflt : Option (Block Op), EquivBlock D (dflt.getD []) ((hcDflt P Δ dflt).getD [])
  | none => by simpa [hcDflt] using (EquivBlock.refl [] : EquivBlock D _ _)
  | some b => by
      rw [hcDflt]
      simpa [hcBlock] using
        (EquivBlock.of_stmts_funs
          (EquivStmts.of_forall₂ (hcStmts_forall2 P (deltaExtend Δ b) b))
          (hcScopeRel P (deltaExtend Δ b) b))

private theorem hcScopeRel (P : String) (Δ : DEnv) :
    ∀ ss : List (Stmt Op), ScopeRel D (hoist D ss) (hoist D (hcStmts P Δ ss))
  | [] => by simpa [hcStmts, hoist] using (ScopeRel.refl ([] : FScope D))
  | .funDef n ps rs body :: rest => by
      rw [hcStmts, hcStmt]
      simp only [hoist, List.filterMap_cons]
      have hb : EquivBlock D body (hcBlock P Δ body) := by
        simpa [hcBlock] using
          (EquivBlock.of_stmts_funs
            (EquivStmts.of_forall₂ (hcStmts_forall2 P (deltaExtend Δ body) body))
            (hcScopeRel P (deltaExtend Δ body) body))
      exact .cons ⟨rfl, rfl, rfl, hb⟩ (hcScopeRel P Δ rest)
  | .block _ :: rest => by simpa [hcStmts, hcStmt, hoist] using hcScopeRel P Δ rest
  | .letDecl _ _ :: rest => by simpa [hcStmts, hcStmt, hoist] using hcScopeRel P Δ rest
  | .assign vars val :: rest => by
      cases val with
      | lit l => simpa [hcStmts, hcStmt, hoist] using hcScopeRel P Δ rest
      | var x => simpa [hcStmts, hcStmt, hoist] using hcScopeRel P Δ rest
      | builtin op args => simpa [hcStmts, hcStmt, hoist] using hcScopeRel P Δ rest
      | call f args =>
        cases args with
        | nil => simpa [hcStmts, hcStmt, hoist] using hcScopeRel P Δ rest
        | cons a tail =>
          cases tail with
          | cons b tail =>
              simpa [hcStmts, hcStmt, hoist] using hcScopeRel P Δ rest
          | nil =>
            cases a with
            | lit l => simpa [hcStmts, hcStmt, hoist] using hcScopeRel P Δ rest
            | var x => simpa [hcStmts, hcStmt, hoist] using hcScopeRel P Δ rest
            | builtin op gas =>
                simpa [hcStmts, hcStmt, hoist] using hcScopeRel P Δ rest
            | call g gas =>
              simp only [hcStmts, hcStmt]
              split
              · split <;>
                  simpa [hoistUnaryCore, hoist] using hcScopeRel P Δ rest
              · simpa [hoist] using hcScopeRel P Δ rest
  | .cond _ _ :: rest => by simpa [hcStmts, hcStmt, hoist] using hcScopeRel P Δ rest
  | .switch _ _ _ :: rest => by simpa [hcStmts, hcStmt, hoist] using hcScopeRel P Δ rest
  | .forLoop _ _ _ _ :: rest => by simpa [hcStmts, hcStmt, hoist] using hcScopeRel P Δ rest
  | .exprStmt e :: rest => by
      rw [hcStmts, hcStmt, hoist_cons_hcExprStmt]
      simpa [hoist] using hcScopeRel P Δ rest
  | .break :: rest => by simpa [hcStmts, hcStmt, hoist] using hcScopeRel P Δ rest
  | .continue :: rest => by simpa [hcStmts, hcStmt, hoist] using hcScopeRel P Δ rest
  | .leave :: rest => by simpa [hcStmts, hcStmt, hoist] using hcScopeRel P Δ rest

end

def hoistCallsBlock (b : Block Op) : Block Op :=
  match freshPrefix (stmtsIdents b) with
  | some P => hcBlock P [] b
  | none => b

def hoistCalls : LocalPass D where
  run := hoistCallsBlock
  sound := fun b => by
    unfold hoistCallsBlock
    split
    · next p hp =>
      simpa [hcBlock] using
        (EquivBlock.of_stmts_funs
          (EquivStmts.of_forall₂ (hcStmts_forall2 p (deltaExtend [] b) b))
          (hcScopeRel p (deltaExtend [] b) b))
    · exact EquivBlock.refl _

end YulEvmCompiler.Optimizer

