import YulEvmCompiler.Optimizer.Implementation.DeadLits
import YulEvmCompiler.Optimizer.Implementation.InlineCallsSound
set_option warningAsError true
/-!
# YulEvmCompiler.Optimizer.Implementation.DeadPure

**Dead pure-binding elimination** — `DeadLits` generalized from literal
right-hand sides to right-hand sides that *provably evaluate in context*:

* literals (subsuming `DeadLits`);
* variables that are **provably bound here** — function parameters/returns
  (the call rule's `callOk` environment binds exactly those) and variables
  let-declared earlier in an enclosing scope of the same frame; and
* total state-preserving builtin trees over those (`pureFn`-domain ops and
  deterministic storage reads at exact arity).  In particular, `sload`
  depends on the input state but returns that state unchanged, so an unused
  read is just as removable as an unused arithmetic result.

Additionally, a **self-assignment** `x := x` with `x` provably bound is
dropped: `VEnv.set V x v = V` when `VEnv.get V x = some v`, so removal
desyncs nothing at all.

This is exactly the shape of the copy scaffolding that `InlineCalls`
materializes and (gated) copy propagation makes dead: `let p := a` parameter
copies, `let r` zero-inits, `let y := x` chain links whose uses were
substituted away.

## Why this cannot reuse `DlRel`'s congruence chaining

`removeLit_equivBlock` needs the removed right-hand side to evaluate on
*every* environment — true for literals only. The dominant removable shape,
a param-sourced copy `let _1 := var_x`, is stuck on environments where
`var_x` is unbound, and `DlRel.sound`'s `funDefS` case demands pointwise
`EquivBlock` of bodies over arbitrary environments, where that stuckness is
observable. Only a `Step` simulation whose `call` case sees the `callOk`
environment can supply the boundness fact. The relation `DcRel bound` below
therefore follows `Propagate`'s architecture: skip rules everywhere, a
semantic invariant (`BoundOK V bound`: every ident in `bound` is bound in
`V`), a syntactic funs relation (`DcFunsRel`), and one bidirectional
simulation — with the env desync ("the unremoved side carries extra dead
bindings until its enclosing block's `restore`") tracked by an insertion
relation generalizing `Frame.InsAt` to interleaved multiple insertions.

The strong `Pass`/`EquivBlock` tier remains reachable because every removed
binding is local to the (implicitly wrapped) top-level block: `restore`
erases the difference at every block exit, exactly as in `DeadLits`.

For-loop `init` blocks are left untouched (their scope spans the whole
loop), mirroring `DeadLits`.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM

variable {calls : ExternalCalls} {creates : ExternalCreates}

local notation "D" => evmWithExternal calls creates

/-! ### The always-evaluating right-hand-side fragment -/

/-- Arity at which `pureFn` is total for an op (`none` for ops outside the
pure fragment). Mirrors `pureFn`'s arms exactly. -/
def pureTotalArity : Op → Option Nat
  | .add | .sub | .mul | .div | .sdiv | .mod | .smod
  | .signextend | .lt | .gt | .slt | .sgt | .eq
  | .and | .or | .xor | .byte | .shl | .shr | .sar => some 2
  | .clz | .iszero | .not => some 1
  | .addmod | .mulmod => some 3
  | _ => none

/-- `pureTotalArity` is the domain of `pureFn`: at the declared arity, the
op is total on values. -/
theorem pureTotalArity_pureFn {op : Op} {n : Nat}
    (h : pureTotalArity op = some n) (vs : List U256) (hlen : vs.length = n) :
    ∃ w, pureFn op vs = some w := by
  unfold pureTotalArity at h
  split at h <;> cases h <;>
    first
      | (match vs, hlen with | [a], _ => exact ⟨_, rfl⟩)
      | (match vs, hlen with | [a, b], _ => exact ⟨_, rfl⟩)
      | (match vs, hlen with | [a, b, c], _ => exact ⟨_, rfl⟩)

/-- Arity of the total, state-preserving expression fragment.  This extends
`pureTotalArity` with storage reads: unlike `mload` and `keccak256`, `sload`
does not expand active memory or otherwise change `EvmState`. -/
def stableTotalArity : Op → Option Nat
  | .sload => some 1
  | op => pureTotalArity op

/-- Every stable-total operation is either a `pureFn` operation or `sload`. -/
theorem stableTotalArity_cases {op : Op} {n : Nat}
    (h : stableTotalArity op = some n) :
    pureTotalArity op = some n ∨ (op = .sload ∧ n = 1) := by
  cases op <;> simp_all [stableTotalArity, pureTotalArity]

mutual

/-- Does the expression evaluate — to exactly one value, without touching
state and without halting — on every environment binding all of `bound`? -/
def alwaysEval (bound : List Ident) : Expr Op → Bool
  | .lit _ => true
  | .var x => bound.contains x
  | .builtin op args =>
      (stableTotalArity op == some args.length) && alwaysEvalArgs bound args
  | .call _ _ => false

/-- `alwaysEval` for each argument. -/
def alwaysEvalArgs (bound : List Ident) : List (Expr Op) → Bool
  | [] => true
  | e :: rest => alwaysEval bound e && alwaysEvalArgs bound rest

end

/-! ### Dead result-region checker -/

/-- Static context for a discardable result region. `bound` may be read;
`owned` contains exactly the region-local bindings that may be assigned. -/
structure DrCtx where
  bound : List Ident
  owned : List Ident

mutual

/-- Check one statement in a total, state-preserving straight-line region. -/
def discardStmt (sink : Ident) (ctx : DrCtx) : Stmt Op → Option DrCtx
  | .block body => do
      let _ ← discardStmts sink ctx body
      pure ctx
  | .letDecl [x] none =>
      if x == sink then none else some ⟨x :: ctx.bound, x :: ctx.owned⟩
  | .letDecl [x] (some rhs) =>
      if x != sink && alwaysEval ctx.bound rhs then
        some ⟨x :: ctx.bound, x :: ctx.owned⟩
      else none
  | .assign [x] rhs =>
      if ctx.owned.contains x && alwaysEval ctx.bound rhs then some ctx else none
  | _ => none

/-- Check a straight-line region, threading declarations through its sequence. -/
def discardStmts (sink : Ident) : DrCtx → List (Stmt Op) → Option DrCtx
  | ctx, [] => some ctx
  | ctx, s :: rest => do
      let ctx' ← discardStmt sink ctx s
      discardStmts sink ctx' rest

end

mutual

/-- Whether executing a statement can consult the Yul function environment. -/
def stmtCallFree : Stmt Op → Bool
  | .block body => stmtsCallFree body
  | .funDef _ _ _ _ => true
  | .letDecl _ none => true
  | .letDecl _ (some e) => !exprHasCall e
  | .assign _ e => !exprHasCall e
  | .cond c body => !exprHasCall c && stmtsCallFree body
  | .switch c cases dflt =>
      !exprHasCall c && casesCallFree cases && dfltCallFree dflt
  | .forLoop init c post body =>
      stmtsCallFree init && !exprHasCall c && stmtsCallFree post && stmtsCallFree body
  | .exprStmt e => !exprHasCall e
  | .break | .continue | .leave => true

def stmtsCallFree : List (Stmt Op) → Bool
  | [] => true
  | s :: rest => stmtCallFree s && stmtsCallFree rest

def casesCallFree : List (Literal × Block Op) → Bool
  | [] => true
  | (_, body) :: rest => stmtsCallFree body && casesCallFree rest

def dfltCallFree : Option (Block Op) → Bool
  | none => true
  | some body => stmtsCallFree body

end

/-- Per-code-class call-freedom predicate. -/
def codeCallFree : Code Op → Bool
  | .expr e => !exprHasCall e
  | .args es => !argsHaveCall es
  | .stmt s => stmtCallFree s
  | .stmts ss => stmtsCallFree ss
  | .loop c post body =>
      !exprHasCall c && stmtsCallFree post && stmtsCallFree body

theorem blockCodeCallFree {body : Block Op} (h : stmtsCallFree body = true) :
    codeCallFree (.stmt (.block body)) = true := h

/-- Is `let sink; { body }` a removable dead result at this point? -/
def removableResult (bound : List Ident) (sink : Ident)
    (body rest : List (Stmt Op)) : Bool :=
  (discardStmts sink ⟨sink :: bound, [sink]⟩ body).isSome &&
    !stmtsMentions sink rest && stmtsCallFree rest

/-- A selected switch arm is call-free when every arm is. -/
theorem selectSwitch_callFree {cv : U256} {cases : List (Literal × Block Op)}
    {dflt : Option (Block Op)} (hc : casesCallFree cases = true)
    (hd : dfltCallFree dflt = true) :
    stmtsCallFree (selectSwitch D cv cases dflt) = true := by
  induction cases with
  | nil =>
      unfold selectSwitch
      simp only [List.find?_nil]
      cases dflt with
      | none => rfl
      | some body => exact hd
  | cons p rest ih =>
      obtain ⟨l, body⟩ := p
      simp only [casesCallFree, Bool.and_eq_true] at hc
      by_cases hcv : cv = (evmWithExternal calls creates).litValue l
      · rw [selectSwitch, List.find?_cons_of_pos (by simp [hcv])]
        exact hc.1
      · rw [selectSwitch, List.find?_cons_of_neg (by simp [hcv])]
        have := ih hc.2
        rwa [selectSwitch] at this

/-- Call-free code is independent of the Yul function environment. -/
theorem Step.callFree_funs {funs₁ : FunEnv D} {V : VEnv D} {st : EvmState}
    {code : Code Op} {res : Res D} (h : Step D funs₁ V st code res) :
    codeCallFree code = true → ∀ funs₂, Step D funs₂ V st code res := by
  induction h with
  | lit => intro _ _; exact Step.lit
  | var hv => intro _ _; exact Step.var hv
  | builtinOk _ hbi ih =>
      intro hcf funs₂
      exact Step.builtinOk (ih (by simpa [codeCallFree, exprHasCall] using hcf) funs₂) hbi
  | builtinHalt _ hbi ih =>
      intro hcf funs₂
      exact Step.builtinHalt (ih (by simpa [codeCallFree, exprHasCall] using hcf) funs₂) hbi
  | builtinArgsHalt _ ih =>
      intro hcf funs₂
      exact Step.builtinArgsHalt (ih (by simpa [codeCallFree, exprHasCall] using hcf) funs₂)
  | callOk | callHalt | callArgsHalt =>
      intro hcf _
      simp [codeCallFree, exprHasCall] at hcf
  | argsNil => intro _ _; exact Step.argsNil
  | argsCons _ _ ihr ihe =>
      intro hcf funs₂
      simp only [codeCallFree, Bool.not_eq_true', argsHaveCall,
        Bool.or_eq_false_iff] at hcf
      exact Step.argsCons
        (ihr (by simp [codeCallFree, hcf.2]) funs₂)
        (ihe (by simp [codeCallFree, hcf.1]) funs₂)
  | argsRestHalt _ ihr =>
      intro hcf funs₂
      simp only [codeCallFree, Bool.not_eq_true', argsHaveCall,
        Bool.or_eq_false_iff] at hcf
      exact Step.argsRestHalt (ihr (by simp [codeCallFree, hcf.2]) funs₂)
  | argsHeadHalt _ _ ihr ihe =>
      intro hcf funs₂
      simp only [codeCallFree, Bool.not_eq_true', argsHaveCall,
        Bool.or_eq_false_iff] at hcf
      exact Step.argsHeadHalt
        (ihr (by simp [codeCallFree, hcf.2]) funs₂)
        (ihe (by simp [codeCallFree, hcf.1]) funs₂)
  | funDef => intro _ _; exact Step.funDef
  | block _ ih =>
      intro hcf funs₂
      exact Step.block (ih (by simpa [codeCallFree, stmtCallFree] using hcf)
        (hoist D _ :: funs₂))
  | letZero => intro _ _; exact Step.letZero
  | letVal _ hlen ih =>
      intro hcf funs₂
      exact Step.letVal (ih (by simpa [codeCallFree, stmtCallFree] using hcf) funs₂) hlen
  | letHalt _ ih =>
      intro hcf funs₂
      exact Step.letHalt (ih (by simpa [codeCallFree, stmtCallFree] using hcf) funs₂)
  | assignVal _ hlen ih =>
      intro hcf funs₂
      exact Step.assignVal (ih (by simpa [codeCallFree, stmtCallFree] using hcf) funs₂) hlen
  | assignHalt _ ih =>
      intro hcf funs₂
      exact Step.assignHalt (ih (by simpa [codeCallFree, stmtCallFree] using hcf) funs₂)
  | exprStmt _ ih =>
      intro hcf funs₂
      exact Step.exprStmt (ih (by simpa [codeCallFree, stmtCallFree] using hcf) funs₂)
  | exprStmtHalt _ ih =>
      intro hcf funs₂
      exact Step.exprStmtHalt (ih (by simpa [codeCallFree, stmtCallFree] using hcf) funs₂)
  | ifTrue _ hnz _ ihc ihb =>
      intro hcf funs₂
      simp only [codeCallFree, stmtCallFree, Bool.and_eq_true] at hcf
      exact Step.ifTrue
        (ihc (by simpa [codeCallFree] using hcf.1) funs₂) hnz
        (ihb (by simpa [codeCallFree, stmtCallFree] using hcf.2) funs₂)
  | ifFalse _ hz ihc =>
      intro hcf funs₂
      simp only [codeCallFree, stmtCallFree, Bool.and_eq_true] at hcf
      exact Step.ifFalse (ihc (by simpa [codeCallFree] using hcf.1) funs₂) hz
  | ifHalt _ ihc =>
      intro hcf funs₂
      simp only [codeCallFree, stmtCallFree, Bool.and_eq_true] at hcf
      exact Step.ifHalt (ihc (by simpa [codeCallFree] using hcf.1) funs₂)
  | switchExec _ _ ihc ihb =>
      intro hcf funs₂
      simp only [codeCallFree, stmtCallFree, Bool.and_eq_true] at hcf
      exact Step.switchExec
        (ihc (by simpa [codeCallFree] using hcf.1.1) funs₂)
        (ihb (blockCodeCallFree (selectSwitch_callFree hcf.1.2 hcf.2)) funs₂)
  | switchHalt _ ihc =>
      intro hcf funs₂
      simp only [codeCallFree, stmtCallFree, Bool.and_eq_true] at hcf
      exact Step.switchHalt (ihc (by simpa [codeCallFree] using hcf.1.1) funs₂)
  | forLoop _ _ ihinit ihloop =>
      intro hcf funs₂
      simp only [codeCallFree, stmtCallFree, Bool.and_eq_true] at hcf
      exact Step.forLoop
        (ihinit (by simpa [codeCallFree] using hcf.1.1.1) (hoist D _ :: funs₂))
        (ihloop (by simp [codeCallFree, hcf.1.1.2, hcf.1.2, hcf.2])
          (hoist D _ :: funs₂))
  | forInitHalt _ ihinit =>
      intro hcf funs₂
      simp only [codeCallFree, stmtCallFree, Bool.and_eq_true] at hcf
      exact Step.forInitHalt
        (ihinit (by simpa [codeCallFree] using hcf.1.1.1) (hoist D _ :: funs₂))
  | «break» => intro _ _; exact Step.break
  | «continue» => intro _ _; exact Step.continue
  | leave => intro _ _; exact Step.leave
  | seqNil => intro _ _; exact Step.seqNil
  | seqCons _ _ ihs ihrest =>
      intro hcf funs₂
      simp only [codeCallFree, stmtsCallFree, Bool.and_eq_true] at hcf
      exact Step.seqCons
        (ihs (by simpa [codeCallFree] using hcf.1) funs₂)
        (ihrest (by simpa [codeCallFree] using hcf.2) funs₂)
  | seqStop _ hne ihs =>
      intro hcf funs₂
      simp only [codeCallFree, stmtsCallFree, Bool.and_eq_true] at hcf
      exact Step.seqStop (ihs (by simpa [codeCallFree] using hcf.1) funs₂) hne
  | loopDone _ hz ihc =>
      intro hcf funs₂
      simp only [codeCallFree, Bool.and_eq_true] at hcf
      exact Step.loopDone (ihc (by simpa [codeCallFree] using hcf.1.1) funs₂) hz
  | loopCondHalt _ ihc =>
      intro hcf funs₂
      simp only [codeCallFree, Bool.and_eq_true] at hcf
      exact Step.loopCondHalt (ihc (by simpa [codeCallFree] using hcf.1.1) funs₂)
  | loopStep _ hnz _ hob _ _ ihc ihb ihp ihr =>
      intro hcf funs₂
      simp only [codeCallFree, Bool.and_eq_true] at hcf
      exact Step.loopStep
        (ihc (by simpa [codeCallFree] using hcf.1.1) funs₂) hnz
        (ihb (blockCodeCallFree hcf.2) funs₂) hob
        (ihp (blockCodeCallFree hcf.1.2) funs₂)
        (ihr (by simp [codeCallFree, hcf.1.1, hcf.1.2, hcf.2]) funs₂)
  | loopPostHalt _ hnz _ hob _ ihc ihb ihp =>
      intro hcf funs₂
      simp only [codeCallFree, Bool.and_eq_true] at hcf
      exact Step.loopPostHalt
        (ihc (by simpa [codeCallFree] using hcf.1.1) funs₂) hnz
        (ihb (blockCodeCallFree hcf.2) funs₂) hob
        (ihp (blockCodeCallFree hcf.1.2) funs₂)
  | loopBreak _ hnz _ ihc ihb =>
      intro hcf funs₂
      simp only [codeCallFree, Bool.and_eq_true] at hcf
      exact Step.loopBreak
        (ihc (by simpa [codeCallFree] using hcf.1.1) funs₂) hnz
        (ihb (blockCodeCallFree hcf.2) funs₂)
  | loopLeave _ hnz _ ihc ihb =>
      intro hcf funs₂
      simp only [codeCallFree, Bool.and_eq_true] at hcf
      exact Step.loopLeave
        (ihc (by simpa [codeCallFree] using hcf.1.1) funs₂) hnz
        (ihb (blockCodeCallFree hcf.2) funs₂)
  | loopBodyHalt _ hnz _ ihc ihb =>
      intro hcf funs₂
      simp only [codeCallFree, Bool.and_eq_true] at hcf
      exact Step.loopBodyHalt
        (ihc (by simpa [codeCallFree] using hcf.1.1) funs₂) hnz
        (ihb (blockCodeCallFree hcf.2) funs₂)

/-! ### The transform -/

/-- Is `s` a removable statement, given the provably-bound set and the rest
of its block? Removable are dead singleton `let`s with always-evaluating
right-hand sides (or zero-init) and self-assignments of bound variables. -/
def removablePure (bound : List Ident) : Stmt Op → List (Stmt Op) → Bool
  | .letDecl [x] none, rest => !stmtsMentions x rest
  | .letDecl [x] (some rhs), rest =>
      alwaysEval bound rhs && !stmtsMentions x rest
  | .assign [x] (.var y), _ => x == y && bound.contains x
  | _, _ => false

mutual

/-- Remove dead pure bindings, recursing into every sub-block (a `for`
loop's `init` is left untouched — its scope spans the whole loop). -/
def dpStmt (bound : List Ident) : Stmt Op → Stmt Op
  | .block body => .block (dpStmts bound body)
  | .funDef n ps rs body => .funDef n ps rs (dpStmts (ps ++ rs) body)
  | .cond c body => .cond c (dpStmts bound body)
  | .switch c cases dflt => .switch c (dpCases bound cases) (dpDflt bound dflt)
  | .forLoop init c post body =>
      .forLoop init c (dpStmts bound post) (dpStmts bound body)
  | s => s

/-- Remove dead pure bindings from a statement sequence, growing the
provably-bound set at each kept declaration. -/
def dpStmts (bound : List Ident) : List (Stmt Op) → List (Stmt Op)
  | [] => []
  | s :: rest =>
      if removablePure bound s rest then dpStmts bound rest
      else
        match s with
        | .letDecl xs val =>
            .letDecl xs val :: dpStmts (xs ++ bound) rest
        | s => dpStmt bound s :: dpStmts bound rest

/-- Remove dead pure bindings from each `switch` case body. -/
def dpCases (bound : List Ident) :
    List (Literal × Block Op) → List (Literal × Block Op)
  | [] => []
  | (l, b) :: rest => (l, dpStmts bound b) :: dpCases bound rest

/-- Remove dead pure bindings from a `switch` default. -/
def dpDflt (bound : List Ident) : Option (Block Op) → Option (Block Op)
  | none => none
  | some b => some (dpStmts bound b)

end

/-! ### Small variable-environment facts -/

/-- A key present in the environment's domain has a value. -/
theorem VEnv.get_isSome_of_key {V : VEnv D} {x : Ident}
    (h : x ∈ V.map Prod.fst) : ∃ v, VEnv.get V x = some v := by
  induction V with
  | nil => simp at h
  | cons p rest ih =>
      rw [VEnv.get_cons]
      by_cases hp : p.1 = x
      · exact ⟨p.2, by rw [if_pos hp]⟩
      · rw [if_neg hp]
        simp only [List.map_cons, List.mem_cons] at h
        rcases h with h | h
        · exact absurd h.symm hp
        · exact ih h

/-- Re-writing a bound variable with its own value is a no-op. -/
theorem VEnv.set_self {V : VEnv D} {x : Ident} {v : U256}
    (h : VEnv.get V x = some v) : VEnv.set V x v = V := by
  induction V with
  | nil => rfl
  | cons p rest ih =>
      rw [VEnv.get_cons] at h
      simp only [VEnv.set]
      by_cases hp : p.1 = x
      · rw [if_pos hp] at h ⊢
        injection h with h
        cases p
        simp_all
      · rw [if_neg hp] at h ⊢
        rw [ih h]

/-! ### The semantic boundness invariant -/

/-- Every listed ident is in the environment's domain. -/
def BoundOK (V : VEnv D) (bound : List Ident) : Prop :=
  ∀ x ∈ bound, x ∈ V.map Prod.fst

theorem BoundOK.nil (V : VEnv D) : BoundOK V [] :=
  fun _ hx => absurd hx (List.not_mem_nil)

/-- Boundness is monotone along execution (domains only grow). -/
theorem BoundOK.mono {V V' : VEnv D} {bound : List Ident} {funs st code st' o}
    (hb : BoundOK V bound) (h : Step D funs V st code (.sres V' st' o)) :
    BoundOK V' bound :=
  fun x hx => dom_mono h (hb x hx)

/-! ### Executing always-evaluating right-hand sides -/

mutual

/-- An always-evaluating expression evaluates: exactly one value, state
unchanged, no halt possible (constructive direction). -/
theorem dcEvalRun {bound : List Ident} {V : VEnv D} (hb : BoundOK V bound)
    (funs : FunEnv D) (st : EvmState) :
    ∀ (e : Expr Op), alwaysEval bound e = true →
      ∃ v, Step D funs V st (.expr e) (.eres (.vals [v] st))
  | .lit _, _ => ⟨_, Step.lit⟩
  | .var x, h => by
      rw [alwaysEval] at h
      have hx : x ∈ bound := by simpa using h
      obtain ⟨v, hv⟩ := VEnv.get_isSome_of_key (hb x hx)
      exact ⟨v, Step.var hv⟩
  | .builtin op args, h => by
      rw [alwaysEval, Bool.and_eq_true] at h
      obtain ⟨vs, hvs, hlen⟩ := dcEvalArgsRun hb funs st args h.2
      have har : stableTotalArity op = some args.length := by simpa using h.1
      rcases stableTotalArity_cases har with hpure | ⟨rfl, harity⟩
      · obtain ⟨w, hw⟩ := pureTotalArity_pureFn hpure vs hlen
        exact ⟨w, Step.builtinOk hvs (pureFn_builtin hw st)⟩
      · match vs, hlen, harity with
        | [k], _, _ =>
            exact ⟨st.storage k, Step.builtinOk hvs (by
              simp [builtinWithExternal, stepOp])⟩
        | [], _, _ => simp_all
        | _ :: _ :: _, _, _ => simp_all
  | .call _ _, h => by rw [alwaysEval] at h; cases h

/-- Always-evaluating argument lists evaluate to one value each, state
unchanged. -/
theorem dcEvalArgsRun {bound : List Ident} {V : VEnv D} (hb : BoundOK V bound)
    (funs : FunEnv D) (st : EvmState) :
    ∀ (es : List (Expr Op)), alwaysEvalArgs bound es = true →
      ∃ vs, Step D funs V st (.args es) (.eres (.vals vs st)) ∧
        vs.length = es.length
  | [], _ => ⟨[], Step.argsNil, rfl⟩
  | e :: rest, h => by
      rw [alwaysEvalArgs, Bool.and_eq_true] at h
      obtain ⟨vs, hvs, hlen⟩ := dcEvalArgsRun hb funs st rest h.2
      obtain ⟨v, hv⟩ := dcEvalRun hb funs st e h.1
      exact ⟨v :: vs, Step.argsCons hvs hv, by simp [hlen]⟩

end

mutual

/-- Inversion: an always-evaluating expression's every evaluation yields
exactly one value with the state unchanged — it can never halt. -/
theorem dcEvalInv {bound : List Ident} :
    ∀ (e : Expr Op), alwaysEval bound e = true →
      ∀ {funs : FunEnv D} {V : VEnv D} {st : EvmState} {r : EResult D},
        Step D funs V st (.expr e) (.eres r) → ∃ v, r = .vals [v] st
  | .lit _, _ => by
      intro hstep
      cases hstep with
      | lit => exact ⟨_, rfl⟩
  | .var _, _ => by
      intro hstep
      cases hstep with
      | var hv => exact ⟨_, rfl⟩
  | .builtin op args, h => by
      intro hstep
      rw [alwaysEval, Bool.and_eq_true] at h
      have har : stableTotalArity op = some args.length := by simpa using h.1
      cases hstep with
      | @builtinOk _ _ _ _ _ argvals st1 rets st2 hargs hbi =>
          obtain ⟨vs, heq, hlen⟩ := dcEvalArgsInv args h.2 hargs
          injection heq with hv hs
          subst hv; subst hs
          rcases stableTotalArity_cases har with hpure | ⟨rfl, harity⟩
          · obtain ⟨w, hw⟩ := pureTotalArity_pureFn hpure argvals hlen
            have hr := pureFn_builtin_inv hw hbi
            injection hr with hr1 hr2
            subst hr1; subst hr2
            exact ⟨w, rfl⟩
          · match argvals, hlen, harity with
            | [k], _, _ =>
                simp [builtinWithExternal, stepOp] at hbi
                obtain ⟨rfl, rfl⟩ := hbi
                exact ⟨st1.storage k, rfl⟩
            | [], _, _ => simp_all
            | _ :: _ :: _, _, _ => simp_all
      | @builtinHalt _ _ _ _ _ argvals st1 st2 hargs hbi =>
          obtain ⟨vs, heq, hlen⟩ := dcEvalArgsInv args h.2 hargs
          injection heq with hv hs
          subst hv; subst hs
          rcases stableTotalArity_cases har with hpure | ⟨rfl, harity⟩
          · obtain ⟨w, hw⟩ := pureTotalArity_pureFn hpure argvals hlen
            exact absurd (pureFn_builtin_inv hw hbi) (by simp)
          · match argvals, hlen, harity with
            | [k], _, _ => simp [builtinWithExternal, stepOp] at hbi
            | [], _, _ => simp_all
            | _ :: _ :: _, _, _ => simp_all
      | builtinArgsHalt hargs =>
          obtain ⟨vs, heq, -⟩ := dcEvalArgsInv args h.2 hargs
          cases heq
  | .call _ _, h => by intro _; rw [alwaysEval] at h; cases h

/-- Inversion for argument lists: one value per argument, state unchanged. -/
theorem dcEvalArgsInv {bound : List Ident} :
    ∀ (es : List (Expr Op)), alwaysEvalArgs bound es = true →
      ∀ {funs : FunEnv D} {V : VEnv D} {st : EvmState} {r : EResult D},
        Step D funs V st (.args es) (.eres r) →
        ∃ vs, r = .vals vs st ∧ vs.length = es.length
  | [], _ => by
      intro hstep
      cases hstep with
      | argsNil => exact ⟨[], rfl, rfl⟩
  | e :: rest, h => by
      intro hstep
      rw [alwaysEvalArgs, Bool.and_eq_true] at h
      cases hstep with
      | @argsCons _ _ _ _ _ restvals st1 v st2 hrest he =>
          obtain ⟨vs, heq, hlen⟩ := dcEvalArgsInv rest h.2 hrest
          injection heq with hv hs
          subst hv; subst hs
          obtain ⟨v', hv'⟩ := dcEvalInv e h.1 he
          injection hv' with _ hs2
          subst hs2
          exact ⟨v :: restvals, rfl, by simp [hlen]⟩
      | argsRestHalt hrest =>
          obtain ⟨vs, heq, -⟩ := dcEvalArgsInv rest h.2 hrest
          cases heq
      | @argsHeadHalt _ _ _ _ _ restvals st1 st2 hrest he =>
          obtain ⟨vs, heq, -⟩ := dcEvalArgsInv rest h.2 hrest
          injection heq with hv hs
          subst hv; subst hs
          obtain ⟨v, hv⟩ := dcEvalInv e h.1 he
          cases hv

end

/-! ### Executing accepted dead result regions -/

/-- The local bindings represented by a discard context form a prefix over
an arbitrary outer environment. Values may change, but the prefix names are
exactly `owned`. -/
def DrFrame (base : VEnv D) (owned : List Ident) (V : VEnv D) : Prop :=
  ∃ A, V = A ++ base ∧ A.map Prod.fst = owned

theorem DrFrame.nil (V : VEnv D) : DrFrame V [] V :=
  ⟨[], by simp⟩

theorem DrFrame.cons {base V : VEnv D} {owned : List Ident}
    (h : DrFrame base owned V) (x : Ident) (v : U256) :
    DrFrame base (x :: owned) ((x, v) :: V) := by
  obtain ⟨A, rfl, hkeys⟩ := h
  exact ⟨(x, v) :: A, by simp [hkeys]⟩

theorem DrFrame.set {base V : VEnv D} {owned : List Ident}
    (h : DrFrame base owned V) {x : Ident} (hx : x ∈ owned) (v : U256) :
    DrFrame base owned (VEnv.set V x v) := by
  obtain ⟨A, rfl, hkeys⟩ := h
  have hxA : x ∈ A.map Prod.fst := by simpa [hkeys] using hx
  refine ⟨VEnv.set A x v, ?_, ?_⟩
  · exact VEnv.set_append_mem hxA base v
  · rw [VEnv.set_keys, hkeys]

mutual

theorem discardStmt_owned_suffix {sink : Ident} {ctx ctx' : DrCtx}
    {s : Stmt Op} (h : discardStmt sink ctx s = some ctx') :
    ∃ pre, ctx'.owned = pre ++ ctx.owned := by
  cases s with
  | block body =>
      cases hb : discardStmts sink ctx body with
      | none => simp [discardStmt, hb] at h
      | some out =>
          simp [discardStmt, hb] at h
          subst ctx'
          exact ⟨[], rfl⟩
  | letDecl xs rhs =>
      cases xs with
      | nil => simp [discardStmt] at h
      | cons x xs =>
          cases xs with
          | nil =>
              cases rhs with
              | none =>
                  by_cases hx : x = sink
                  · simp [discardStmt, hx] at h
                  · simp [discardStmt, hx] at h
                    subst ctx'
                    exact ⟨[x], rfl⟩
              | some rhs =>
                  by_cases hx : x != sink && alwaysEval ctx.bound rhs
                  · simp [discardStmt, hx] at h
                    subst ctx'
                    exact ⟨[x], rfl⟩
                  · simp [discardStmt, hx] at h
          | cons _ _ => simp [discardStmt] at h
  | assign xs rhs =>
      cases xs with
      | nil => simp [discardStmt] at h
      | cons x xs =>
          cases xs with
          | nil =>
              simp [discardStmt] at h
              rcases h with ⟨-, -, rfl⟩
              exact ⟨[], rfl⟩
          | cons _ _ => simp [discardStmt] at h
  | cond _ _ => simp [discardStmt] at h
  | switch _ _ _ => simp [discardStmt] at h
  | forLoop _ _ _ _ => simp [discardStmt] at h
  | funDef _ _ _ _ => simp [discardStmt] at h
  | exprStmt _ => simp [discardStmt] at h
  | «break» => simp [discardStmt] at h
  | «continue» => simp [discardStmt] at h
  | leave => simp [discardStmt] at h

theorem discardStmts_owned_suffix {sink : Ident} {ctx ctx' : DrCtx}
    {ss : List (Stmt Op)} (h : discardStmts sink ctx ss = some ctx') :
    ∃ pre, ctx'.owned = pre ++ ctx.owned := by
  induction ss generalizing ctx with
  | nil =>
      simp only [discardStmts, Option.some.injEq] at h
      subst ctx'
      exact ⟨[], rfl⟩
  | cons s rest ih =>
      cases hs : discardStmt sink ctx s with
      | none => simp [discardStmts, hs] at h
      | some ctx₁ =>
          have htail : discardStmts sink ctx₁ rest = some ctx' := by
            simpa [discardStmts, hs] using h
          obtain ⟨pre₁, hpre₁⟩ := discardStmt_owned_suffix hs
          obtain ⟨pre₂, hpre₂⟩ := ih htail
          exact ⟨pre₂ ++ pre₁, by simp [hpre₂, hpre₁, List.append_assoc]⟩

end


theorem DrFrame.restore {base V V' : VEnv D} {owned owned' : List Ident}
    (hV : DrFrame base owned V) (hV' : DrFrame base owned' V')
    (hsuf : ∃ pre, owned' = pre ++ owned) :
    DrFrame base owned (restore V V') ∧
      (restore V V').map Prod.fst = V.map Prod.fst := by
  obtain ⟨A, rfl, hA⟩ := hV
  obtain ⟨A', rfl, hA'⟩ := hV'
  obtain ⟨pre, rfl⟩ := hsuf
  have hlenA : A.length = owned.length := by
    simpa using congrArg List.length hA
  have hlenA' : A'.length = pre.length + owned.length := by
    simpa using congrArg List.length hA'
  have hdrop : (A' ++ base).drop pre.length = A'.drop pre.length ++ base :=
    List.drop_append_of_le_length (by omega)
  have hkeys : (A'.drop pre.length).map Prod.fst = owned := by
    rw [List.map_drop, hA']
    simp
  have hrestore : YulSemantics.restore (A ++ base) (A' ++ base) =
      A'.drop pre.length ++ base := by
    unfold YulSemantics.restore
    simp only [List.length_append]
    rw [show (A'.length + base.length) - (A.length + base.length) = pre.length by omega]
    exact hdrop
  rw [hrestore]
  constructor
  · exact ⟨A'.drop pre.length, rfl, hkeys⟩
  · simp [hkeys, hA]

mutual

theorem discardStmt_run {sink : Ident} {ctx ctx' : DrCtx} {s : Stmt Op}
    (hcheck : discardStmt sink ctx s = some ctx')
    {base V : VEnv D} (hframe : DrFrame base ctx.owned V)
    (hb : BoundOK V ctx.bound) (funs : FunEnv D) (st : EvmState) :
    ∃ V', Step D funs V st (.stmt s) (.sres V' st .normal) ∧
      DrFrame base ctx'.owned V' ∧ BoundOK V' ctx'.bound := by
  cases s with
  | block body =>
      cases hbody : discardStmts sink ctx body with
      | none => simp [discardStmt, hbody] at hcheck
      | some out =>
          simp [discardStmt, hbody] at hcheck
          subst ctx'
          obtain ⟨Vb, hrun, hframe', -⟩ :=
            discardStmts_run hbody hframe hb (hoist D body :: funs) st
          obtain ⟨hrestFrame, hkeys⟩ :=
            hframe.restore hframe' (discardStmts_owned_suffix hbody)
          refine ⟨restore V Vb, Step.block hrun, hrestFrame, ?_⟩
          intro x hx
          rw [hkeys]
          exact hb x hx
  | letDecl xs rhs =>
      cases xs with
      | nil => simp [discardStmt] at hcheck
      | cons x xs =>
          cases xs with
          | cons _ _ => simp [discardStmt] at hcheck
          | nil =>
              cases rhs with
              | none =>
                  by_cases hx : x = sink
                  · simp [discardStmt, hx] at hcheck
                  · simp [discardStmt, hx] at hcheck
                    subst ctx'
                    refine ⟨(x, 0) :: V, Step.letZero, hframe.cons x 0, ?_⟩
                    intro z hz
                    simp only [List.mem_cons] at hz
                    rcases hz with rfl | hz
                    · simp
                    · simp only [List.map_cons, List.mem_cons]
                      exact Or.inr (hb z hz)
              | some rhs =>
                  simp [discardStmt] at hcheck
                  rcases hcheck with ⟨⟨hx, hae⟩, rfl⟩
                  obtain ⟨v, he⟩ := dcEvalRun hb funs st rhs hae
                  refine ⟨(x, v) :: V, Step.letVal he rfl, hframe.cons x v, ?_⟩
                  intro z hz
                  simp only [List.mem_cons] at hz
                  rcases hz with rfl | hz
                  · simp
                  · simp only [List.map_cons, List.mem_cons]
                    exact Or.inr (hb z hz)
  | assign xs rhs =>
      cases xs with
      | nil => simp [discardStmt] at hcheck
      | cons x xs =>
          cases xs with
          | cons _ _ => simp [discardStmt] at hcheck
          | nil =>
              simp [discardStmt] at hcheck
              rcases hcheck with ⟨⟨hx, hae⟩, rfl⟩
              obtain ⟨v, he⟩ := dcEvalRun hb funs st rhs hae
              refine ⟨VEnv.set V x v, ?_, hframe.set hx v, ?_⟩
              · have h := Step.assignVal (vars := [x]) he rfl
                rwa [VEnv.setMany_singleton] at h
              · intro z hz
                rw [VEnv.set_keys]
                exact hb z hz
  | cond _ _ => simp [discardStmt] at hcheck
  | switch _ _ _ => simp [discardStmt] at hcheck
  | forLoop _ _ _ _ => simp [discardStmt] at hcheck
  | funDef _ _ _ _ => simp [discardStmt] at hcheck
  | exprStmt _ => simp [discardStmt] at hcheck
  | «break» => simp [discardStmt] at hcheck
  | «continue» => simp [discardStmt] at hcheck
  | leave => simp [discardStmt] at hcheck

theorem discardStmts_run {sink : Ident} {ctx ctx' : DrCtx}
    {ss : List (Stmt Op)} (hcheck : discardStmts sink ctx ss = some ctx')
    {base V : VEnv D} (hframe : DrFrame base ctx.owned V)
    (hb : BoundOK V ctx.bound) (funs : FunEnv D) (st : EvmState) :
    ∃ V', Step D funs V st (.stmts ss) (.sres V' st .normal) ∧
      DrFrame base ctx'.owned V' ∧ BoundOK V' ctx'.bound := by
  cases ss with
  | nil =>
      simp only [discardStmts, Option.some.injEq] at hcheck
      subst ctx'
      exact ⟨V, Step.seqNil, hframe, hb⟩
  | cons s rest =>
      cases hs : discardStmt sink ctx s with
      | none => simp [discardStmts, hs] at hcheck
      | some ctx₁ =>
          have htail : discardStmts sink ctx₁ rest = some ctx' := by
            simpa [discardStmts, hs] using hcheck
          obtain ⟨V₁, hsrun, hframe₁, hb₁⟩ :=
            discardStmt_run hs hframe hb funs st
          obtain ⟨V₂, hrest, hframe₂, hb₂⟩ :=
            discardStmts_run htail hframe₁ hb₁ funs st
          exact ⟨V₂, Step.seqCons hsrun hrest, hframe₂, hb₂⟩

end

mutual

/-- Every derivation of an accepted statement has the checked normal,
state-preserving frame shape. -/
theorem discardStmt_inv {sink : Ident} {ctx ctx' : DrCtx} {s : Stmt Op}
    (hcheck : discardStmt sink ctx s = some ctx')
    {base V : VEnv D} (hframe : DrFrame base ctx.owned V)
    (hb : BoundOK V ctx.bound) {funs : FunEnv D} {st V' st' o}
    (hstep : Step D funs V st (.stmt s) (.sres V' st' o)) :
    st' = st ∧ o = .normal ∧ DrFrame base ctx'.owned V' ∧
      BoundOK V' ctx'.bound := by
  cases s with
  | block body =>
      cases hbody : discardStmts sink ctx body with
      | none => simp [discardStmt, hbody] at hcheck
      | some out =>
          simp [discardStmt, hbody] at hcheck
          subst ctx'
          cases hstep with
          | block hrun =>
              obtain ⟨rfl, rfl, hframe', -⟩ :=
                discardStmts_inv hbody hframe hb hrun
              obtain ⟨hrestFrame, hkeys⟩ :=
                hframe.restore hframe' (discardStmts_owned_suffix hbody)
              refine ⟨rfl, rfl, hrestFrame, ?_⟩
              intro x hx
              rw [hkeys]
              exact hb x hx
  | letDecl xs rhs =>
      cases xs with
      | nil => simp [discardStmt] at hcheck
      | cons x xs =>
          cases xs with
          | cons _ _ => simp [discardStmt] at hcheck
          | nil =>
              cases rhs with
              | none =>
                  by_cases hx : x = sink
                  · simp [discardStmt, hx] at hcheck
                  · simp [discardStmt, hx] at hcheck
                    subst ctx'
                    cases hstep with
                    | letZero =>
                        have hframe' : DrFrame base (x :: ctx.owned)
                            ((x, (evmWithExternal calls creates).zero) :: V) :=
                          hframe.cons x (evmWithExternal calls creates).zero
                        have hb' : BoundOK
                            ((x, (evmWithExternal calls creates).zero) :: V)
                            (x :: ctx.bound) := by
                          intro z hz
                          simp only [List.mem_cons] at hz
                          rcases hz with rfl | hz
                          · simp
                          · simp only [List.map_cons, List.mem_cons]
                            exact Or.inr (hb z hz)
                        exact ⟨rfl, rfl, by simpa [bindZeros] using hframe',
                          by simpa [bindZeros] using hb'⟩
              | some rhs =>
                  simp [discardStmt] at hcheck
                  rcases hcheck with ⟨⟨-, hae⟩, rfl⟩
                  cases hstep with
                  | letVal he hlen =>
                      obtain ⟨v, hr⟩ := dcEvalInv rhs hae he
                      injection hr with hvals hst
                      subst hvals; subst hst
                      have hb' : BoundOK ((x, v) :: V) (x :: ctx.bound) := by
                        intro z hz
                        simp only [List.mem_cons] at hz
                        rcases hz with rfl | hz
                        · simp
                        · simp only [List.map_cons, List.mem_cons]
                          exact Or.inr (hb z hz)
                      exact ⟨rfl, rfl, by simpa using hframe.cons x v,
                        by simpa using hb'⟩
                  | letHalt he =>
                      obtain ⟨v, hv⟩ := dcEvalInv rhs hae he
                      cases hv
  | assign xs rhs =>
      cases xs with
      | nil => simp [discardStmt] at hcheck
      | cons x xs =>
          cases xs with
          | cons _ _ => simp [discardStmt] at hcheck
          | nil =>
              simp [discardStmt] at hcheck
              rcases hcheck with ⟨⟨hx, hae⟩, rfl⟩
              cases hstep with
              | assignVal he hlen =>
                  obtain ⟨v, hr⟩ := dcEvalInv rhs hae he
                  injection hr with hvals hst
                  subst hvals; subst hst
                  rw [VEnv.setMany_singleton]
                  refine ⟨rfl, rfl, hframe.set hx v, ?_⟩
                  intro z hz
                  rw [VEnv.set_keys]
                  exact hb z hz
              | assignHalt he =>
                  obtain ⟨v, hv⟩ := dcEvalInv rhs hae he
                  cases hv
  | cond _ _ => simp [discardStmt] at hcheck
  | switch _ _ _ => simp [discardStmt] at hcheck
  | forLoop _ _ _ _ => simp [discardStmt] at hcheck
  | funDef _ _ _ _ => simp [discardStmt] at hcheck
  | exprStmt _ => simp [discardStmt] at hcheck
  | «break» => simp [discardStmt] at hcheck
  | «continue» => simp [discardStmt] at hcheck
  | leave => simp [discardStmt] at hcheck

/-- Inversion for accepted region sequences. -/
theorem discardStmts_inv {sink : Ident} {ctx ctx' : DrCtx}
    {ss : List (Stmt Op)} (hcheck : discardStmts sink ctx ss = some ctx')
    {base V : VEnv D} (hframe : DrFrame base ctx.owned V)
    (hb : BoundOK V ctx.bound) {funs : FunEnv D} {st V' st' o}
    (hstep : Step D funs V st (.stmts ss) (.sres V' st' o)) :
    st' = st ∧ o = .normal ∧ DrFrame base ctx'.owned V' ∧
      BoundOK V' ctx'.bound := by
  cases ss with
  | nil =>
      simp only [discardStmts, Option.some.injEq] at hcheck
      subst ctx'
      cases hstep with
      | seqNil => exact ⟨rfl, rfl, hframe, hb⟩
  | cons s rest =>
      cases hs : discardStmt sink ctx s with
      | none => simp [discardStmts, hs] at hcheck
      | some ctx₁ =>
          have htail : discardStmts sink ctx₁ rest = some ctx' := by
            simpa [discardStmts, hs] using hcheck
          cases hstep with
          | seqCons hstmt hrest =>
              obtain ⟨hst, -, hframe₁, hb₁⟩ :=
                discardStmt_inv hs hframe hb hstmt
              rw [hst] at hrest
              exact discardStmts_inv htail hframe₁ hb₁ hrest
          | seqStop hstmt hne =>
              obtain ⟨-, ho, -, -⟩ := discardStmt_inv hs hframe hb hstmt
              exact absurd ho hne

end

/-- An accepted block, entered immediately after the zero-initialized sink,
has exactly one possible observable shape. -/
theorem discardBlock_run {bound : List Ident} {sink : Ident} {body : Block Op}
    (hcheck : (discardStmts sink ⟨sink :: bound, [sink]⟩ body).isSome = true)
    {V : VEnv D} (hb : BoundOK V bound) (funs : FunEnv D) (st : EvmState) :
    ∃ v, Step D funs ((sink, (evmWithExternal calls creates).zero) :: V) st
      (.stmt (.block body))
      (.sres ((sink, v) :: V) st .normal) := by
  cases hc : discardStmts sink ⟨sink :: bound, [sink]⟩ body with
  | none => simp [hc] at hcheck
  | some out =>
      have hbound : BoundOK ((sink, 0) :: V) (sink :: bound) := by
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · simp
        · simp only [List.map_cons, List.mem_cons]
          exact Or.inr (hb x hx)
      have hstmt : discardStmt sink ⟨sink :: bound, [sink]⟩ (.block body) =
          some ⟨sink :: bound, [sink]⟩ := by simp [discardStmt, hc]
      obtain ⟨V', hrun, hframe, -⟩ :=
        discardStmt_run hstmt (DrFrame.cons (DrFrame.nil V) sink
          (evmWithExternal calls creates).zero)
          hbound funs st
      obtain ⟨A, hV', hkeys⟩ := hframe
      cases A with
      | nil => simp at hkeys
      | cons p rest =>
          cases rest with
          | nil =>
              obtain ⟨rfl, -⟩ := List.cons.inj hkeys
              rw [hV'] at hrun
              exact ⟨p.2, hrun⟩
          | cons q rest => simp at hkeys

theorem discardBlock_inv {bound : List Ident} {sink : Ident} {body : Block Op}
    (hcheck : (discardStmts sink ⟨sink :: bound, [sink]⟩ body).isSome = true)
    {V : VEnv D} (hb : BoundOK V bound) {funs : FunEnv D} {st V' st' o}
    (hstep : Step D funs ((sink, (evmWithExternal calls creates).zero) :: V) st
      (.stmt (.block body))
      (.sres V' st' o)) :
    ∃ v, V' = (sink, v) :: V ∧ st' = st ∧ o = .normal := by
  cases hc : discardStmts sink ⟨sink :: bound, [sink]⟩ body with
  | none => simp [hc] at hcheck
  | some out =>
      have hbound : BoundOK ((sink, 0) :: V) (sink :: bound) := by
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · simp
        · simp only [List.map_cons, List.mem_cons]
          exact Or.inr (hb x hx)
      have hstmt : discardStmt sink ⟨sink :: bound, [sink]⟩ (.block body) =
          some ⟨sink :: bound, [sink]⟩ := by simp [discardStmt, hc]
      obtain ⟨rfl, rfl, hframe, -⟩ :=
        discardStmt_inv hstmt (DrFrame.cons (DrFrame.nil V) sink
          (evmWithExternal calls creates).zero)
          hbound hstep
      obtain ⟨A, hV', hkeys⟩ := hframe
      cases A with
      | nil => simp at hkeys
      | cons p rest =>
          cases rest with
          | nil =>
              obtain ⟨rfl, -⟩ := List.cons.inj hkeys
              exact ⟨p.2, hV', rfl, rfl⟩
          | cons q rest => simp at hkeys

/-! ### The multi-insertion environment relation

`Frame.InsAt` handles one inserted binding; removal interleaves many. `MIns`
is the chain of `InsAt`s, indexed by the (depth, ident) of each insertion —
most recent first. Depths pin the splice points so `restore` alignment
works exactly as for a single insertion, link by link. -/

/-- `MIns ins V₁ V₂`: `V₁` is `V₂` with one extra binding spliced in per
entry of `ins`; the entry `(d, x)` records the insertion's depth (`InsAt`
depth: number of bindings below the splice) and ident. -/
inductive MIns : List (Nat × Ident) → VEnv D → VEnv D → Prop
  | nil (V : VEnv D) : MIns [] V V
  | cons {ins : List (Nat × Ident)} {d : Nat} {x : Ident} {v : U256}
      {V₂ Vm V₁ : VEnv D} :
      MIns ins Vm V₂ → InsAt d x v Vm V₁ → MIns ((d, x) :: ins) V₁ V₂

theorem MIns.nil_eq {V₁ V₂ : VEnv D} (h : MIns [] V₁ V₂) : V₁ = V₂ := by
  cases h; rfl

/-- Reading any ident but the inserted ones is unaffected. -/
theorem MIns.get_ne {ins : List (Nat × Ident)} {V₁ V₂ : VEnv D}
    (h : MIns ins V₁ V₂) {z : Ident} (hz : ∀ p ∈ ins, z ≠ p.2) :
    VEnv.get V₁ z = VEnv.get V₂ z := by
  induction h with
  | nil => rfl
  | @cons ins d x v _ _ _ hm hins ih =>
      rw [hins.get_ne (hz (d, x) (List.mem_cons_self ..))]
      exact ih (fun p hp => hz p (List.mem_cons_of_mem _ hp))

/-- The smaller side's domain is contained in the larger side's. -/
theorem MIns.keys_sub {ins : List (Nat × Ident)} {V₁ V₂ : VEnv D}
    (h : MIns ins V₁ V₂) : ∀ x ∈ V₂.map Prod.fst, x ∈ V₁.map Prod.fst := by
  induction h with
  | nil => exact fun _ hx => hx
  | cons hm hins ih =>
      intro x hx
      obtain ⟨A, B, rfl, rfl, -⟩ := hins
      have := ih x hx
      simp only [List.map_append, List.mem_append, List.map_cons,
        List.mem_cons] at this ⊢
      tauto

/-- Boundness transports from the plain side to the inserted side. -/
theorem BoundOK.of_mins {ins : List (Nat × Ident)} {V₁ V₂ : VEnv D}
    {bound : List Ident} (hb : BoundOK V₂ bound) (h : MIns ins V₁ V₂) :
    BoundOK V₁ bound :=
  fun x hx => h.keys_sub x (hb x hx)

/-- Multi-update over idents disjoint from the insertions preserves the
relation. -/
theorem MIns.setMany {xs : List Ident} (vals : List U256) :
    ∀ {ins : List (Nat × Ident)} {V₁ V₂ : VEnv D}, MIns ins V₁ V₂ →
      (∀ p ∈ ins, p.2 ∉ xs) →
      MIns ins (VEnv.setMany V₁ xs vals) (VEnv.setMany V₂ xs vals) := by
  intro ins V₁ V₂ h
  induction h with
  | nil => intro _; exact .nil _
  | @cons ins d x v _ _ _ hm hins ih =>
      intro hx
      exact .cons (ih (fun p hp => hx p (List.mem_cons_of_mem _ hp)))
        (InsAt.setMany (hx (d, x) (List.mem_cons_self ..)) vals hins)

/-- Prepending the same bindings on both sides preserves the relation. -/
theorem MIns.prepend {ins : List (Nat × Ident)} {V₁ V₂ : VEnv D}
    (h : MIns ins V₁ V₂) (pre : VEnv D) :
    MIns ins (pre ++ V₁) (pre ++ V₂) := by
  induction h with
  | nil => exact .nil _
  | cons hm hins ih => exact .cons ih (hins.prepend pre)

/-- A fresh insertion at the top of the larger side. -/
theorem MIns.insTop {ins : List (Nat × Ident)} {V₁ V₂ : VEnv D}
    (h : MIns ins V₁ V₂) (x : Ident) (v : U256) :
    MIns ((V₁.length, x) :: ins) ((x, v) :: V₁) V₂ :=
  .cons h ⟨[], V₁, rfl, rfl, rfl⟩

/-- The chain splits at any index seam. -/
theorem MIns.split {a b : List (Nat × Ident)} :
    ∀ {V₁ V₂ : VEnv D}, MIns (a ++ b) V₁ V₂ →
      ∃ Vm, MIns a V₁ Vm ∧ MIns b Vm V₂ := by
  induction a with
  | nil => exact fun h => ⟨_, .nil _, h⟩
  | cons p a' ih =>
      obtain ⟨d, x⟩ := p
      intro V₁ V₂ h
      cases h with
      | cons hm hins =>
          obtain ⟨Vm, ha', hb⟩ := ih hm
          exact ⟨Vm, .cons ha' hins, hb⟩

theorem MIns.length {ins : List (Nat × Ident)} {V₁ V₂ : VEnv D}
    (h : MIns ins V₁ V₂) : V₁.length = ins.length + V₂.length := by
  induction h with
  | nil => simp
  | cons hm hins ih =>
      have := hins.length
      simp only [List.length_cons]
      omega

/-- Restoring to a base at or below every insertion erases them all: both
sides restore to the same environment (chains `restore_insAt_le`). -/
theorem restore_mins_le {base : VEnv D} :
    ∀ {insN : List (Nat × Ident)} {V₁ Vm : VEnv D}, MIns insN V₁ Vm →
      (∀ p ∈ insN, base.length ≤ p.1) →
      restore base V₁ = restore base Vm := by
  intro insN V₁ Vm h
  induction h with
  | nil => intro _; rfl
  | @cons ins d x v _ _ _ hm hins ih =>
      intro hd
      rw [← restore_insAt_le hins (hd (d, x) (List.mem_cons_self ..))]
      exact ih (fun p hp => hd p (List.mem_cons_of_mem _ hp))

/-- Value-heterogeneous variant of `InsAt.restore`: the entry insertion's
value plays no role (only its depth), so the entry and body insertions may
carry different values. Proof as in `Frame.InsAt.restore`. -/
theorem insAt_restore_het {d : Nat} {x : Ident} {w v : U256}
    {Ve1 Ve2 Vb1 Vb2 : VEnv D}
    (hentry : InsAt d x w Ve1 Ve2) (hbody : InsAt d x v Vb1 Vb2) :
    InsAt d x v (restore Ve1 Vb1) (restore Ve2 Vb2) := by
  obtain ⟨A, B, hb1, hb2, hBd⟩ := hbody
  obtain ⟨Ae, Be, he1, he2, hBed⟩ := hentry
  have hk1 : Vb1.length - Ve1.length = A.length - Ae.length := by
    rw [hb1, he1]; simp only [List.length_append]; omega
  have hk2 : Vb2.length - Ve2.length = A.length - Ae.length := by
    rw [hb2, he2]; simp only [List.length_append, List.length_cons]; omega
  have hle : A.length - Ae.length ≤ A.length := Nat.sub_le _ _
  change InsAt d x v (Vb1.drop (Vb1.length - Ve1.length))
    (Vb2.drop (Vb2.length - Ve2.length))
  rw [hk1, hk2, hb1, hb2, List.drop_append_of_le_length hle,
    List.drop_append_of_le_length hle]
  exact ⟨A.drop (A.length - Ae.length), B, rfl, rfl, hBd⟩

/-- Same-index chains restore in alignment, link by link. -/
theorem mins_restore_core : ∀ {ins : List (Nat × Ident)} {Ve₁ Ve₂ Vm Vb₂ : VEnv D},
    MIns ins Ve₁ Ve₂ → MIns ins Vm Vb₂ →
    MIns ins (restore Ve₁ Vm) (restore Ve₂ Vb₂) := by
  intro ins
  induction ins with
  | nil =>
      intro Ve₁ Ve₂ Vm Vb₂ he hp
      rw [he.nil_eq, hp.nil_eq]
      exact .nil _
  | cons p ins' ih =>
      obtain ⟨d, x⟩ := p
      intro Ve₁ Ve₂ Vm Vb₂ he hp
      cases he with
      | cons hentry' hlinkE =>
          cases hp with
          | cons hpart' hlinkB =>
              exact .cons (ih hentry' hpart') (insAt_restore_het hlinkE hlinkB)

/-- **Frame + restore, multi-insertion.** Insertions made inside a block
(depths at or above the entry environment) die at the block's `restore`;
the entry insertions survive, link by link. -/
theorem MIns.restore {ins insN : List (Nat × Ident)} {Ve₁ Ve₂ Vb₁ Vb₂ : VEnv D}
    (hentry : MIns ins Ve₁ Ve₂) (hbody : MIns (insN ++ ins) Vb₁ Vb₂)
    (hN : ∀ p ∈ insN, Ve₁.length ≤ p.1) :
    MIns ins (restore Ve₁ Vb₁) (restore Ve₂ Vb₂) := by
  obtain ⟨Vm, hNpart, hpart⟩ := MIns.split hbody
  rw [restore_mins_le hNpart hN]
  exact mins_restore_core hentry hpart

/-- Mention-freeness of every inserted ident in the code still to run. -/
def InsFree (ins : List (Nat × Ident)) (code : Code Op) : Prop :=
  ∀ p ∈ ins, codeMentions p.2 code = false

theorem InsFree.nil (code : Code Op) : InsFree [] code :=
  fun _ hp => absurd hp (List.not_mem_nil)

/-- Mention-freeness is monotone along syntactic containment. -/
theorem InsFree.mono {ins : List (Nat × Ident)} {c₁ c₂ : Code Op}
    (h : InsFree ins c₁)
    (hsub : ∀ x, codeMentions x c₁ = false → codeMentions x c₂ = false) :
    InsFree ins c₂ :=
  fun p hp => hsub _ (h p hp)

/-- Remove every insertion in an `MIns` chain while executing code that
mentions none of their names. -/
theorem MIns.frameRemove {ins : List (Nat × Ident)} {V₁ V₂ : VEnv D}
    (hins : MIns ins V₁ V₂) {funs : FunEnv D} {st : EvmState}
    {code : Code Op} {V₁' : VEnv D} {st' : EvmState} {o : Outcome}
    (hstep : Step D funs V₁ st code (.sres V₁' st' o))
    (hfree : InsFree ins code) :
    ∃ V₂', Step D funs V₂ st code (.sres V₂' st' o) ∧
      MIns ins V₁' V₂' := by
  induction hins generalizing V₁' st' o with
  | nil V => exact ⟨V₁', hstep, .nil _⟩
  | @cons ins d x v V₂ Vm V₁ hm hlink ih =>
      obtain ⟨resm, hstepm, hrelm⟩ :=
        YulEvmCompiler.Optimizer.frameRemove hstep hlink
        (hfree (d, x) (List.mem_cons_self ..))
      obtain ⟨Vm', rfl, hlink'⟩ := hrelm.sres_right
      have hfree' : InsFree ins code :=
        fun p hp => hfree p (List.mem_cons_of_mem _ hp)
      obtain ⟨V₂', hstep₂, hm'⟩ := ih hstepm hfree'
      exact ⟨V₂', hstep₂, .cons hm' hlink'⟩

/-- Add every insertion in an `MIns` chain while executing mention-free
code. -/
theorem MIns.frameAdd {ins : List (Nat × Ident)} {V₁ V₂ : VEnv D}
    (hins : MIns ins V₁ V₂) {funs : FunEnv D} {st : EvmState}
    {code : Code Op} {V₂' : VEnv D} {st' : EvmState} {o : Outcome}
    (hstep : Step D funs V₂ st code (.sres V₂' st' o))
    (hfree : InsFree ins code) :
    ∃ V₁', Step D funs V₁ st code (.sres V₁' st' o) ∧
      MIns ins V₁' V₂' := by
  induction hins generalizing V₂' st' o with
  | nil V => exact ⟨V₂', hstep, .nil _⟩
  | @cons ins d x v V₂ Vm V₁ hm hlink ih =>
      have hfree' : InsFree ins code :=
        fun p hp => hfree p (List.mem_cons_of_mem _ hp)
      obtain ⟨Vm', hstepm, hm'⟩ := ih hstep hfree'
      obtain ⟨res₁, hstep₁, hrel₁⟩ :=
        YulEvmCompiler.Optimizer.frameAdd hstepm hlink
        (hfree (d, x) (List.mem_cons_self ..))
      obtain ⟨V₁', rfl, hlink'⟩ := hrel₁.sres
      exact ⟨V₁', hstep₁, .cons hm' hlink'⟩

/-! ### The removal relation

`DcRel bound bound' pc pc'`: `pc'` is `pc` with a valid subset of dead pure
bindings and self-assignments removed, under provably-bound set `bound`,
leaving `bound'` for what follows. Constructor-preserving on statements;
expressions are never rewritten; the `for` init is fixed. -/

/-- The provably-bound set a kept statement leaves for following statements. -/
def dpOut (bound : List Ident) : Stmt Op → List Ident
  | .letDecl xs _ => xs ++ bound
  | _ => bound

/-- Bound names accumulated by an unchanged statement suffix. -/
def dpOutStmts : List Ident → List (Stmt Op) → List Ident
  | bound, [] => bound
  | bound, s :: rest => dpOutStmts (dpOut bound s) rest

/-- The removal relation (see section header). -/
inductive DcRel : List Ident → List Ident → PCode Op → PCode Op → Prop
  | exprE {bound : List Ident} {e : Expr Op} :
      DcRel bound bound (.expr e) (.expr e)
  | argsE {bound : List Ident} {es : List (Expr Op)} :
      DcRel bound bound (.args es) (.args es)
  | blockS {bound bx : List Ident} {body body' : Block Op} :
      DcRel bound bx (.stmts body) (.stmts body') →
      DcRel bound bound (.stmt (.block body)) (.stmt (.block body'))
  | funDefS {bound bx : List Ident} {n : Ident} {ps rs : List Ident}
      {body body' : Block Op} :
      DcRel (ps ++ rs) bx (.stmts body) (.stmts body') →
      DcRel bound bound (.stmt (.funDef n ps rs body))
        (.stmt (.funDef n ps rs body'))
  | letS {bound : List Ident} {xs : List Ident} {val : Option (Expr Op)} :
      DcRel bound (xs ++ bound) (.stmt (.letDecl xs val))
        (.stmt (.letDecl xs val))
  | assignS {bound : List Ident} {xs : List Ident} {e : Expr Op} :
      DcRel bound bound (.stmt (.assign xs e)) (.stmt (.assign xs e))
  | condS {bound bx : List Ident} {c : Expr Op} {body body' : Block Op} :
      DcRel bound bx (.stmts body) (.stmts body') →
      DcRel bound bound (.stmt (.cond c body)) (.stmt (.cond c body'))
  | switchS {bound : List Ident} {c : Expr Op}
      {cases cases' : List (Literal × Block Op)}
      {dflt dflt' : Option (Block Op)} :
      DcRel bound bound (.cases cases) (.cases cases') →
      DcRel bound bound (.odflt dflt) (.odflt dflt') →
      DcRel bound bound (.stmt (.switch c cases dflt))
        (.stmt (.switch c cases' dflt'))
  | forS {bound bp bb : List Ident} {init : Block Op} {c : Expr Op}
      {post post' body body' : Block Op} :
      DcRel bound bp (.stmts post) (.stmts post') →
      DcRel bound bb (.stmts body) (.stmts body') →
      DcRel bound bound (.stmt (.forLoop init c post body))
        (.stmt (.forLoop init c post' body'))
  | exprStmtS {bound : List Ident} {e : Expr Op} :
      DcRel bound bound (.stmt (.exprStmt e)) (.stmt (.exprStmt e))
  | breakS {bound : List Ident} : DcRel bound bound (.stmt .break) (.stmt .break)
  | continueS {bound : List Ident} :
      DcRel bound bound (.stmt .continue) (.stmt .continue)
  | leaveS {bound : List Ident} : DcRel bound bound (.stmt .leave) (.stmt .leave)
  | nilSS {bound : List Ident} : DcRel bound bound (.stmts []) (.stmts [])
  | consSS {bound b1 b2 : List Ident} {s s' : Stmt Op}
      {rest rest' : List (Stmt Op)} :
      DcRel bound b1 (.stmt s) (.stmt s') →
      DcRel b1 b2 (.stmts rest) (.stmts rest') →
      DcRel bound b2 (.stmts (s :: rest)) (.stmts (s' :: rest'))
  | dropSS {bound b2 : List Ident} {x : Ident} {val : Option (Expr Op)}
      {rest rest' : List (Stmt Op)} :
      (val = none ∨ ∃ rhs, val = some rhs ∧ alwaysEval bound rhs = true) →
      stmtsMentions x rest = false →
      DcRel bound b2 (.stmts rest) (.stmts rest') →
      DcRel bound b2 (.stmts (.letDecl [x] val :: rest)) (.stmts rest')
  | dropSelfSS {bound b2 : List Ident} {x : Ident} {rest rest' : List (Stmt Op)} :
      x ∈ bound →
      DcRel bound b2 (.stmts rest) (.stmts rest') →
      DcRel bound b2 (.stmts (.assign [x] (.var x) :: rest)) (.stmts rest')
  | dropRegionSS {bound : List Ident} {sink : Ident} {body rest : Block Op} :
      (discardStmts sink ⟨sink :: bound, [sink]⟩ body).isSome = true →
      stmtsMentions sink rest = false →
      stmtsCallFree rest = true →
      DcRel bound (dpOutStmts bound rest)
        (.stmts (.letDecl [sink] none :: .block body :: rest)) (.stmts rest)
  | loopL {bound bp bb : List Ident} {c : Expr Op}
      {post post' body body' : Block Op} :
      DcRel bound bp (.stmts post) (.stmts post') →
      DcRel bound bb (.stmts body) (.stmts body') →
      DcRel bound bound (.loop c post body) (.loop c post' body')
  | casesNil {bound : List Ident} : DcRel bound bound (.cases []) (.cases [])
  | casesCons {bound bx : List Ident} {l : Literal} {b b' : Block Op}
      {rest rest' : List (Literal × Block Op)} :
      DcRel bound bx (.stmts b) (.stmts b') →
      DcRel bound bound (.cases rest) (.cases rest') →
      DcRel bound bound (.cases ((l, b) :: rest)) (.cases ((l, b') :: rest'))
  | odfltNone {bound : List Ident} : DcRel bound bound (.odflt none) (.odflt none)
  | odfltSome {bound bx : List Ident} {b b' : Block Op} :
      DcRel bound bx (.stmts b) (.stmts b') →
      DcRel bound bound (.odflt (some b)) (.odflt (some b'))

/-- Removal only shortens statement sequences. -/
theorem DcRel.stmts_len {bound b2 : List Ident} {pc pc' : PCode Op}
    (h : DcRel bound b2 pc pc') :
    ∀ {ss ss' : List (Stmt Op)}, pc = .stmts ss → pc' = .stmts ss' →
      ss'.length ≤ ss.length := by
  induction h with
  | nilSS =>
      intro ss ss' h1 h2
      injection h1 with h1; injection h2 with h2
      subst h1; subst h2
      exact Nat.le_refl _
  | consSS _ _ _ ihrest =>
      intro ss ss' h1 h2
      injection h1 with h1; injection h2 with h2
      subst h1; subst h2
      simpa using Nat.succ_le_succ (ihrest rfl rfl)
  | dropSS _ _ _ ihrest =>
      intro ss ss' h1 h2
      injection h1 with h1; injection h2 with h2
      subst h1; subst h2
      exact Nat.le_trans (ihrest rfl rfl) (by simp)
  | dropSelfSS _ _ ihrest =>
      intro ss ss' h1 h2
      injection h1 with h1; injection h2 with h2
      subst h1; subst h2
      exact Nat.le_trans (ihrest rfl rfl) (by simp)
  | dropRegionSS _ _ =>
      intro ss ss' h1 h2
      injection h1 with h1; injection h2 with h2
      subst h1; subst h2
      simp only [List.length_cons]
      omega
  | exprE => exact fun h _ => nomatch h
  | argsE => exact fun h _ => nomatch h
  | blockS _ _ => exact fun h _ => nomatch h
  | funDefS _ _ => exact fun h _ => nomatch h
  | letS => exact fun h _ => nomatch h
  | assignS => exact fun h _ => nomatch h
  | condS _ _ => exact fun h _ => nomatch h
  | switchS _ _ _ _ => exact fun h _ => nomatch h
  | forS _ _ _ _ => exact fun h _ => nomatch h
  | exprStmtS => exact fun h _ => nomatch h
  | breakS => exact fun h _ => nomatch h
  | continueS => exact fun h _ => nomatch h
  | leaveS => exact fun h _ => nomatch h
  | loopL _ _ _ _ => exact fun h _ => nomatch h
  | casesNil => exact fun h _ => nomatch h
  | casesCons _ _ _ _ => exact fun h _ => nomatch h
  | odfltNone => exact fun h _ => nomatch h
  | odfltSome _ _ => exact fun h _ => nomatch h

/-! ### The transform inhabits the relation -/

/-- Unpack a positive removability test. -/
theorem removablePure_inv {bound : List Ident} {s : Stmt Op}
    {rest : List (Stmt Op)} (h : removablePure bound s rest = true) :
    (∃ x, s = .letDecl [x] none ∧ stmtsMentions x rest = false) ∨
    (∃ x rhs, s = .letDecl [x] (some rhs) ∧ alwaysEval bound rhs = true ∧
      stmtsMentions x rest = false) ∨
    (∃ x, s = .assign [x] (.var x) ∧ x ∈ bound) := by
  unfold removablePure at h
  split at h
  · next x => exact Or.inl ⟨x, rfl, by simpa using h⟩
  · next x rhs =>
      rw [Bool.and_eq_true] at h
      exact Or.inr (Or.inl ⟨x, rhs, rfl, h.1, by simpa using h.2⟩)
  · next x y =>
      rw [Bool.and_eq_true] at h
      have hxy : x = y := by simpa using h.1
      subst hxy
      exact Or.inr (Or.inr ⟨x, rfl, by simpa using h.2⟩)
  · cases h

mutual

/-- The statement transform inhabits the relation. -/
theorem dpStmt_rel (bound : List Ident) : ∀ s : Stmt Op,
    DcRel bound (dpOut bound s) (.stmt s) (.stmt (dpStmt bound s))
  | .block body => by
      obtain ⟨bx, h⟩ := dpStmts_rel bound body
      exact .blockS h
  | .funDef n ps rs body => by
      obtain ⟨bx, h⟩ := dpStmts_rel (ps ++ rs) body
      exact .funDefS h
  | .letDecl _ _ => .letS
  | .assign _ _ => .assignS
  | .cond c body => by
      obtain ⟨bx, h⟩ := dpStmts_rel bound body
      exact .condS h
  | .switch c cases dflt =>
      .switchS (dpCases_rel bound cases) (dpDflt_rel bound dflt)
  | .forLoop init c post body => by
      obtain ⟨bp, hp⟩ := dpStmts_rel bound post
      obtain ⟨bb, hb⟩ := dpStmts_rel bound body
      exact .forS hp hb
  | .exprStmt _ => .exprStmtS
  | .break => .breakS
  | .continue => .continueS
  | .leave => .leaveS

/-- The sequence transform inhabits the relation. -/
theorem dpStmts_rel (bound : List Ident) : ∀ ss : List (Stmt Op),
    ∃ b2, DcRel bound b2 (.stmts ss) (.stmts (dpStmts bound ss))
  | [] => ⟨bound, .nilSS⟩
  | s :: rest => by
      by_cases hrem : removablePure bound s rest = true
      · obtain ⟨b2, htail⟩ := dpStmts_rel bound rest
        rcases removablePure_inv hrem with
          ⟨x, rfl, hm⟩ | ⟨x, rhs, rfl, hae, hm⟩ | ⟨x, rfl, hx⟩
        · rw [dpStmts, if_pos hrem]
          exact ⟨b2, .dropSS (Or.inl rfl) hm htail⟩
        · rw [dpStmts, if_pos hrem]
          exact ⟨b2, .dropSS (Or.inr ⟨rhs, rfl, hae⟩) hm htail⟩
        · rw [dpStmts, if_pos hrem]
          · exact ⟨b2, .dropSelfSS hx htail⟩
          · intro xs val h; cases h
      · cases s with
        | letDecl xs val =>
            rw [dpStmts, if_neg hrem]
            obtain ⟨b2, htail⟩ := dpStmts_rel (xs ++ bound) rest
            exact ⟨b2, .consSS .letS htail⟩
        | block body =>
            rw [dpStmts, if_neg hrem]
            · obtain ⟨b2, htail⟩ := dpStmts_rel bound rest
              exact ⟨b2, .consSS (dpStmt_rel bound (.block body)) htail⟩
            · intro xs val h; cases h
        | funDef n ps rs body =>
            rw [dpStmts, if_neg hrem]
            · obtain ⟨b2, htail⟩ := dpStmts_rel bound rest
              exact ⟨b2, .consSS (dpStmt_rel bound (.funDef n ps rs body)) htail⟩
            · intro xs val h; cases h
        | assign xs e =>
            rw [dpStmts, if_neg hrem]
            · obtain ⟨b2, htail⟩ := dpStmts_rel bound rest
              exact ⟨b2, .consSS (dpStmt_rel bound (.assign xs e)) htail⟩
            · intro xs val h; cases h
        | cond c body =>
            rw [dpStmts, if_neg hrem]
            · obtain ⟨b2, htail⟩ := dpStmts_rel bound rest
              exact ⟨b2, .consSS (dpStmt_rel bound (.cond c body)) htail⟩
            · intro xs val h; cases h
        | «switch» c cases dflt =>
            rw [dpStmts, if_neg hrem]
            · obtain ⟨b2, htail⟩ := dpStmts_rel bound rest
              exact ⟨b2, .consSS (dpStmt_rel bound (.switch c cases dflt)) htail⟩
            · intro xs val h; cases h
        | forLoop init c post body =>
            rw [dpStmts, if_neg hrem]
            · obtain ⟨b2, htail⟩ := dpStmts_rel bound rest
              exact ⟨b2, .consSS (dpStmt_rel bound (.forLoop init c post body)) htail⟩
            · intro xs val h; cases h
        | exprStmt e =>
            rw [dpStmts, if_neg hrem]
            · obtain ⟨b2, htail⟩ := dpStmts_rel bound rest
              exact ⟨b2, .consSS (dpStmt_rel bound (.exprStmt e)) htail⟩
            · intro xs val h; cases h
        | «break» =>
            rw [dpStmts, if_neg hrem]
            · obtain ⟨b2, htail⟩ := dpStmts_rel bound rest
              exact ⟨b2, .consSS (dpStmt_rel bound .break) htail⟩
            · intro xs val h; cases h
        | «continue» =>
            rw [dpStmts, if_neg hrem]
            · obtain ⟨b2, htail⟩ := dpStmts_rel bound rest
              exact ⟨b2, .consSS (dpStmt_rel bound .continue) htail⟩
            · intro xs val h; cases h
        | leave =>
            rw [dpStmts, if_neg hrem]
            · obtain ⟨b2, htail⟩ := dpStmts_rel bound rest
              exact ⟨b2, .consSS (dpStmt_rel bound .leave) htail⟩
            · intro xs val h; cases h

/-- The case-list transform inhabits the relation. -/
theorem dpCases_rel (bound : List Ident) : ∀ cs : List (Literal × Block Op),
    DcRel bound bound (.cases cs) (.cases (dpCases bound cs))
  | [] => .casesNil
  | (l, b) :: rest => by
      obtain ⟨bx, hb⟩ := dpStmts_rel bound b
      exact .casesCons hb (dpCases_rel bound rest)

/-- The default transform inhabits the relation. -/
theorem dpDflt_rel (bound : List Ident) : ∀ d : Option (Block Op),
    DcRel bound bound (.odflt d) (.odflt (dpDflt bound d))
  | none => .odfltNone
  | some b => by
      obtain ⟨bx, hb⟩ := dpStmts_rel bound b
      exact .odfltSome hb

end

/-! ### Reflexivity (any bound) -/

mutual

/-- Every statement is `DcRel`-related to itself at any bound. -/
theorem DcRel.reflStmt (bound : List Ident) : ∀ s : Stmt Op,
    DcRel bound (dpOut bound s) (.stmt s) (.stmt s)
  | .block body => by
      obtain ⟨bx, h⟩ := DcRel.reflStmts bound body
      exact .blockS h
  | .funDef n ps rs body => by
      obtain ⟨bx, h⟩ := DcRel.reflStmts (ps ++ rs) body
      exact .funDefS h
  | .letDecl _ _ => .letS
  | .assign _ _ => .assignS
  | .cond c body => by
      obtain ⟨bx, h⟩ := DcRel.reflStmts bound body
      exact .condS h
  | .switch c cases dflt =>
      .switchS (DcRel.reflCases bound cases) (DcRel.reflDflt bound dflt)
  | .forLoop init c post body => by
      obtain ⟨bp, hp⟩ := DcRel.reflStmts bound post
      obtain ⟨bb, hb⟩ := DcRel.reflStmts bound body
      exact .forS hp hb
  | .exprStmt _ => .exprStmtS
  | .break => .breakS
  | .continue => .continueS
  | .leave => .leaveS

/-- Every sequence is `DcRel`-related to itself at any bound. -/
theorem DcRel.reflStmts (bound : List Ident) : ∀ ss : List (Stmt Op),
    ∃ b2, DcRel bound b2 (.stmts ss) (.stmts ss)
  | [] => ⟨bound, .nilSS⟩
  | s :: rest => by
      obtain ⟨b2, htail⟩ := DcRel.reflStmts (dpOut bound s) rest
      exact ⟨b2, .consSS (DcRel.reflStmt bound s) htail⟩

/-- Every case list is `DcRel`-related to itself at any bound. -/
theorem DcRel.reflCases (bound : List Ident) : ∀ cs : List (Literal × Block Op),
    DcRel bound bound (.cases cs) (.cases cs)
  | [] => .casesNil
  | (l, b) :: rest => by
      obtain ⟨bx, hb⟩ := DcRel.reflStmts bound b
      exact .casesCons hb (DcRel.reflCases bound rest)

/-- Every default is `DcRel`-related to itself at any bound. -/
theorem DcRel.reflDflt (bound : List Ident) : ∀ d : Option (Block Op),
    DcRel bound bound (.odflt d) (.odflt d)
  | none => .odfltNone
  | some b => by
      obtain ⟨bx, hb⟩ := DcRel.reflStmts bound b
      exact .odfltSome hb

end

/-- Deterministic-index form of sequence reflexivity. -/
theorem DcRel.reflStmtsExact (bound : List Ident) : ∀ ss : List (Stmt Op),
    DcRel bound (dpOutStmts bound ss) (.stmts ss) (.stmts ss)
  | [] => .nilSS
  | s :: rest =>
      .consSS (DcRel.reflStmt bound s)
        (DcRel.reflStmtsExact (dpOut bound s) rest)

/-! ### The function-environment relation -/

/-- Declarations with equal signatures and `DcRel (params ++ rets)`-related
bodies. -/
def DcFDeclRel (d₁ d₂ : FDecl D) : Prop :=
  d₁.params = d₂.params ∧ d₁.rets = d₂.rets ∧
    ∃ b2, DcRel (d₁.params ++ d₁.rets) b2 (.stmts d₁.body) (.stmts d₂.body)

/-- Scopes related pairwise: equal names, `DcFDeclRel` declarations. -/
def DcScopeRel (s₁ s₂ : FScope D) : Prop :=
  List.Forall₂ (fun p q => p.1 = q.1 ∧
    DcFDeclRel (calls := calls) (creates := creates) p.2 q.2) s₁ s₂

/-- Function environments related scope-by-scope. -/
def DcFunsRel (f₁ f₂ : FunEnv D) : Prop :=
  List.Forall₂ (DcScopeRel (calls := calls) (creates := creates)) f₁ f₂

theorem DcFDeclRel.refl (d : FDecl D) :
    DcFDeclRel (calls := calls) (creates := creates) d d := by
  obtain ⟨b2, h⟩ := DcRel.reflStmts (d.params ++ d.rets) d.body
  exact ⟨rfl, rfl, b2, h⟩

theorem DcScopeRel.refl (s : FScope D) :
    DcScopeRel (calls := calls) (creates := creates) s s := by
  induction s with
  | nil => exact .nil
  | cons p t ih => exact .cons ⟨rfl, DcFDeclRel.refl _⟩ ih

theorem DcFunsRel.refl (f : FunEnv D) :
    DcFunsRel (calls := calls) (creates := creates) f f := by
  induction f with
  | nil => exact .nil
  | cons s t ih => exact .cons (DcScopeRel.refl _) ih

/-- Related sequences hoist related function scopes. -/
theorem DcRel.hoist_scopeRel {bound b2 : List Ident} {pc pc' : PCode Op}
    (h : DcRel bound b2 pc pc') :
    ∀ {ss ss' : List (Stmt Op)}, pc = .stmts ss → pc' = .stmts ss' →
      DcScopeRel (calls := calls) (creates := creates)
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
      | funDefS hbody => exact .cons ⟨rfl, rfl, rfl, _, hbody⟩ htail
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
  | dropSS _ _ _ ihrest =>
      intro ss ss' hss hss'
      injection hss with h1; injection hss' with h2
      subst h1; subst h2
      simpa [hoist] using ihrest rfl rfl
  | dropSelfSS _ _ ihrest =>
      intro ss ss' hss hss'
      injection hss with h1; injection hss' with h2
      subst h1; subst h2
      simpa [hoist] using ihrest rfl rfl
  | dropRegionSS _ _ =>
      intro ss ss' hss hss'
      injection hss with h1; injection hss' with h2
      subst h1; subst h2
      exact DcScopeRel.refl _
  | exprE => exact fun h _ => nomatch h
  | argsE => exact fun h _ => nomatch h
  | blockS _ _ => exact fun h _ => nomatch h
  | funDefS _ _ => exact fun h _ => nomatch h
  | letS => exact fun h _ => nomatch h
  | assignS => exact fun h _ => nomatch h
  | condS _ _ => exact fun h _ => nomatch h
  | switchS _ _ _ _ => exact fun h _ => nomatch h
  | forS _ _ _ _ => exact fun h _ => nomatch h
  | exprStmtS => exact fun h _ => nomatch h
  | breakS => exact fun h _ => nomatch h
  | continueS => exact fun h _ => nomatch h
  | leaveS => exact fun h _ => nomatch h
  | loopL _ _ _ _ => exact fun h _ => nomatch h
  | casesNil => exact fun h _ => nomatch h
  | casesCons _ _ _ _ => exact fun h _ => nomatch h
  | odfltNone => exact fun h _ => nomatch h
  | odfltSome _ _ => exact fun h _ => nomatch h

/-- A scope lookup transports across `DcScopeRel` (both directions at once). -/
theorem dcScopeRel_find {s₁ s₂ : FScope D}
    (h : DcScopeRel (calls := calls) (creates := creates) s₁ s₂) (fn : Ident) :
    (s₁.find? (fun p => p.1 = fn) = none ∧ s₂.find? (fun p => p.1 = fn) = none) ∨
    (∃ p q, s₁.find? (fun p => p.1 = fn) = some p ∧
      s₂.find? (fun p => p.1 = fn) = some q ∧
      p.1 = q.1 ∧ DcFDeclRel (calls := calls) (creates := creates) p.2 q.2) := by
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

/-- `lookupFun` transports forward across `DcFunsRel`. -/
theorem lookupFun_dcFunsRel {f₁ f₂ : FunEnv D}
    (hR : DcFunsRel (calls := calls) (creates := creates) f₁ f₂) :
    ∀ {fn : Ident} {decl : FDecl D} {cenv : FunEnv D},
      lookupFun f₁ fn = some (decl, cenv) →
      ∃ decl' cenv', lookupFun f₂ fn = some (decl', cenv') ∧
        decl'.params = decl.params ∧ decl'.rets = decl.rets ∧
        (∃ b2, DcRel (decl.params ++ decl.rets) b2
          (.stmts decl.body) (.stmts decl'.body)) ∧
        DcFunsRel (calls := calls) (creates := creates) cenv cenv' := by
  induction hR with
  | nil => intro fn decl cenv h; simp [lookupFun] at h
  | @cons s₁ s₂ t₁ t₂ hs hR' ih =>
      intro fn decl cenv h
      rcases dcScopeRel_find hs fn with ⟨hn₁, hn₂⟩ | ⟨p, q, hp₁, hp₂, hkey, hd⟩
      · rw [lookupFun, hn₁] at h
        obtain ⟨decl', cenv', hl', hpar, hret, hbody, hRc⟩ := ih h
        exact ⟨decl', cenv', by rw [lookupFun, hn₂]; exact hl', hpar, hret,
          hbody, hRc⟩
      · rw [lookupFun, hp₁] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hd_eq, hcenv_eq⟩ := h
        subst hd_eq; subst hcenv_eq
        exact ⟨q.2, s₂ :: t₂, by rw [lookupFun, hp₂], hd.1.symm, hd.2.1.symm,
          hd.2.2, List.Forall₂.cons hs hR'⟩

/-- `lookupFun` transports backward across `DcFunsRel`. -/
theorem lookupFun_dcFunsRel_bwd {f₁ f₂ : FunEnv D}
    (hR : DcFunsRel (calls := calls) (creates := creates) f₁ f₂) :
    ∀ {fn : Ident} {decl' : FDecl D} {cenv' : FunEnv D},
      lookupFun f₂ fn = some (decl', cenv') →
      ∃ decl cenv, lookupFun f₁ fn = some (decl, cenv) ∧
        decl'.params = decl.params ∧ decl'.rets = decl.rets ∧
        (∃ b2, DcRel (decl.params ++ decl.rets) b2
          (.stmts decl.body) (.stmts decl'.body)) ∧
        DcFunsRel (calls := calls) (creates := creates) cenv cenv' := by
  induction hR with
  | nil => intro fn decl' cenv' h; simp [lookupFun] at h
  | @cons s₁ s₂ t₁ t₂ hs hR' ih =>
      intro fn decl' cenv' h
      rcases dcScopeRel_find hs fn with ⟨hn₁, hn₂⟩ | ⟨p, q, hp₁, hp₂, hkey, hd⟩
      · rw [lookupFun, hn₂] at h
        obtain ⟨decl, cenv, hl, hpar, hret, hbody, hRc⟩ := ih h
        exact ⟨decl, cenv, by rw [lookupFun, hn₁]; exact hl, hpar, hret,
          hbody, hRc⟩
      · rw [lookupFun, hp₂] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hd_eq, hcenv_eq⟩ := h
        subst hd_eq; subst hcenv_eq
        exact ⟨p.2, s₁ :: t₁, by rw [lookupFun, hp₁], hd.1.symm, hd.2.1.symm,
          hd.2.2, List.Forall₂.cons hs hR'⟩

/-- The `switch` selection of related case lists/defaults is a related
block. -/
theorem DcRel.selectRel {bound b2 bd : List Ident}
    {cases cases' : List (Literal × Block Op)} {dflt dflt' : Option (Block Op)}
    (hcs : DcRel bound b2 (.cases cases) (.cases cases'))
    (hd : DcRel bound bd (.odflt dflt) (.odflt dflt'))
    (cv : U256) :
    ∃ bsel, DcRel bound bsel
      (.stmts (selectSwitch D cv cases dflt))
      (.stmts (selectSwitch D cv cases' dflt')) := by
  induction cases generalizing cases' with
  | nil =>
      cases hcs
      cases hd with
      | odfltNone =>
          refine ⟨bound, ?_⟩
          show DcRel bound bound (.stmts (Option.getD none []))
            (.stmts (Option.getD none []))
          exact .nilSS
      | odfltSome hb => exact ⟨_, by simpa [selectSwitch] using hb⟩
  | cons head rest ih =>
      rcases head with ⟨l, b⟩
      cases hcs with
      | casesCons hb hrest =>
          by_cases hcv : cv = (evmWithExternal calls creates).litValue l
          · rw [selectSwitch, List.find?_cons_of_pos (by simp [hcv]),
                selectSwitch, List.find?_cons_of_pos (by simp [hcv])]
            exact ⟨_, hb⟩
          · obtain ⟨bsel, hsel⟩ := ih hrest
            refine ⟨bsel, ?_⟩
            rw [selectSwitch, List.find?_cons_of_neg (by simp [hcv]),
                selectSwitch, List.find?_cons_of_neg (by simp [hcv])]
            rw [selectSwitch] at hsel
            exact hsel

/-! ### Dropped-statement execution and inversion -/

/-- A droppable `let` executes deterministically: it binds one value on
top, changes no state, and yields `normal` — and that is its only
behavior. -/
theorem dropLet_inv {bound : List Ident} {x : Ident} {val : Option (Expr Op)}
    (hval : val = none ∨ ∃ rhs, val = some rhs ∧ alwaysEval bound rhs = true)
    {funs : FunEnv D} {V : VEnv D} {st : EvmState} {V' : VEnv D}
    {st' : EvmState} {o : Outcome}
    (h : Step D funs V st (.stmt (.letDecl [x] val)) (.sres V' st' o)) :
    ∃ v, V' = (x, v) :: V ∧ st' = st ∧ o = .normal := by
  rcases hval with rfl | ⟨rhs, rfl, hae⟩
  · cases h with
    | letZero => exact ⟨_, rfl, rfl, rfl⟩
  · cases h with
    | letVal he hlen =>
        obtain ⟨v, hv⟩ := dcEvalInv rhs hae he
        injection hv with hv hs
        subst hv; subst hs
        exact ⟨v, rfl, rfl, rfl⟩
    | letHalt he =>
        obtain ⟨v, hv⟩ := dcEvalInv rhs hae he
        cases hv

/-- ... and it always *can* execute, on any environment binding `bound`. -/
theorem dropLet_run {bound : List Ident} {x : Ident} {val : Option (Expr Op)}
    (hval : val = none ∨ ∃ rhs, val = some rhs ∧ alwaysEval bound rhs = true)
    {V : VEnv D} (hb : BoundOK V bound) (funs : FunEnv D) (st : EvmState) :
    ∃ v, Step D funs V st (.stmt (.letDecl [x] val))
      (.sres ((x, v) :: V) st .normal) := by
  rcases hval with rfl | ⟨rhs, rfl, hae⟩
  · exact ⟨_, Step.letZero⟩
  · obtain ⟨v, hv⟩ := dcEvalRun hb funs st rhs hae
    exact ⟨v, Step.letVal hv rfl⟩

/-- A self-assignment of a bound variable is a strict no-op. -/
theorem dropSelf_inv {x : Ident} {funs : FunEnv D} {V : VEnv D}
    {st : EvmState} {V' : VEnv D} {st' : EvmState} {o : Outcome}
    (h : Step D funs V st (.stmt (.assign [x] (.var x))) (.sres V' st' o)) :
    V' = V ∧ st' = st ∧ o = .normal := by
  cases h with
  | assignVal he hlen =>
      cases he with
      | var hv =>
          refine ⟨?_, rfl, rfl⟩
          show VEnv.setMany V [x] _ = V
          rw [VEnv.setMany_singleton, VEnv.set_self hv]
  | assignHalt he => cases he

/-- ... and it always executes when `x` is bound. -/
theorem dropSelf_run {x : Ident} {V : VEnv D}
    (hb : ∃ v, VEnv.get V x = some v) (funs : FunEnv D) (st : EvmState) :
    Step D funs V st (.stmt (.assign [x] (.var x))) (.sres V st .normal) := by
  obtain ⟨v, hv⟩ := hb
  have h := Step.assignVal (funs := funs) (st := st) (vars := [x])
    (Step.var hv) rfl
  rwa [VEnv.setMany_singleton, VEnv.set_self hv] at h

/-! ### Leading drops (for the backward simulation)

The right derivation of a related sequence pair never sees the dropped
statements, so the backward simulation must construct their left runs
before consuming the right derivation's head. `LeadDrops` names the peeled
prefix; `DcRel.stmts_factor` peels it off a relation; `leadDrops_run`
constructs the left prefix run. -/

/-- `LeadDrops bound ss mid`: `mid` is `ss` minus some leading droppable
statements. -/
inductive LeadDrops (bound : List Ident) :
    List (Stmt Op) → List (Stmt Op) → Prop
  | done (ss : List (Stmt Op)) : LeadDrops bound ss ss
  | dropLet {x : Ident} {val : Option (Expr Op)} {rest mid : List (Stmt Op)} :
      (val = none ∨ ∃ rhs, val = some rhs ∧ alwaysEval bound rhs = true) →
      stmtsMentions x rest = false →
      LeadDrops bound rest mid →
      LeadDrops bound (.letDecl [x] val :: rest) mid
  | dropSelf {x : Ident} {rest mid : List (Stmt Op)} :
      x ∈ bound →
      LeadDrops bound rest mid →
      LeadDrops bound (.assign [x] (.var x) :: rest) mid
  | dropRegion {sink : Ident} {body rest mid : List (Stmt Op)} :
      (discardStmts sink ⟨sink :: bound, [sink]⟩ body).isSome = true →
      stmtsMentions sink rest = false →
      LeadDrops bound rest mid →
      LeadDrops bound (.letDecl [sink] none :: .block body :: rest) mid

theorem LeadDrops.length_le {bound : List Ident} {ss mid : List (Stmt Op)}
    (h : LeadDrops bound ss mid) : mid.length ≤ ss.length := by
  induction h with
  | done _ => exact Nat.le_refl _
  | dropLet _ _ _ ih => exact Nat.le_trans ih (by simp)
  | dropSelf _ _ ih => exact Nat.le_trans ih (by simp)
  | dropRegion _ _ _ ih =>
      simp only [List.length_cons]
      omega

theorem LeadDrops.mentions_le {bound : List Ident} {ss mid : List (Stmt Op)}
    (h : LeadDrops bound ss mid) (z : Ident) :
    stmtsMentions z ss = false → stmtsMentions z mid = false := by
  induction h with
  | done _ => exact fun hm => hm
  | dropLet _ _ _ ih =>
      intro hm
      simp only [stmtsMentions, Bool.or_eq_false_iff] at hm
      exact ih hm.2
  | dropSelf _ _ ih =>
      intro hm
      simp only [stmtsMentions, Bool.or_eq_false_iff] at hm
      exact ih hm.2
  | dropRegion _ _ _ ih =>
      intro hm
      simp only [stmtsMentions, Bool.or_eq_false_iff] at hm
      exact ih hm.2.2

/-- Any sequence relation factors as leading drops followed by a kept head
(or the empty tail). -/
theorem DcRel.stmts_factor {bound b2 : List Ident} {pc pc' : PCode Op}
    (h : DcRel bound b2 pc pc') :
    ∀ {ss ss' : List (Stmt Op)}, pc = .stmts ss → pc' = .stmts ss' →
      (ss' = [] ∧ b2 = bound ∧ LeadDrops bound ss []) ∨
      (∃ s rest s' rest' b1, ss' = s' :: rest' ∧
        LeadDrops bound ss (s :: rest) ∧
        DcRel bound b1 (.stmt s) (.stmt s') ∧
        DcRel b1 b2 (.stmts rest) (.stmts rest')) := by
  induction h with
  | nilSS =>
      intro ss ss' h1 h2
      injection h1 with h1; injection h2 with h2
      subst h1; subst h2
      exact Or.inl ⟨rfl, rfl, .done _⟩
  | consSS hs hrest _ _ =>
      intro ss ss' h1 h2
      injection h1 with h1; injection h2 with h2
      subst h1; subst h2
      exact Or.inr ⟨_, _, _, _, _, rfl, .done _, hs, hrest⟩
  | dropSS hval hm hrest ihrest =>
      intro ss ss' h1 h2
      injection h1 with h1; injection h2 with h2
      subst h1; subst h2
      rcases ihrest rfl rfl with ⟨rfl, hb, hld⟩ |
        ⟨s, rest2, s', rest2', b1, heq, hld, hhead, htail⟩
      · exact Or.inl ⟨rfl, hb, .dropLet hval hm hld⟩
      · exact Or.inr ⟨s, rest2, s', rest2', b1, heq,
          .dropLet hval hm hld, hhead, htail⟩
  | dropSelfSS hx hrest ihrest =>
      intro ss ss' h1 h2
      injection h1 with h1; injection h2 with h2
      subst h1; subst h2
      rcases ihrest rfl rfl with ⟨rfl, hb, hld⟩ |
        ⟨s, rest2, s', rest2', b1, heq, hld, hhead, htail⟩
      · exact Or.inl ⟨rfl, hb, .dropSelf hx hld⟩
      · exact Or.inr ⟨s, rest2, s', rest2', b1, heq,
          .dropSelf hx hld, hhead, htail⟩
  | @dropRegionSS bound sink body rest hcheck hm =>
      intro ss ss' h1 h2
      injection h1 with h1; injection h2 with h2
      subst h1; subst h2
      cases rest with
      | nil => exact Or.inl ⟨rfl, rfl, .dropRegion hcheck hm (.done [])⟩
      | cons s tail =>
          exact Or.inr ⟨s, tail, s, tail, dpOut bound s, rfl,
            .dropRegion hcheck hm (.done _), DcRel.reflStmt bound s,
            DcRel.reflStmtsExact (dpOut bound s) tail⟩
  | exprE => exact fun h _ => nomatch h
  | argsE => exact fun h _ => nomatch h
  | blockS _ _ => exact fun h _ => nomatch h
  | funDefS _ _ => exact fun h _ => nomatch h
  | letS => exact fun h _ => nomatch h
  | assignS => exact fun h _ => nomatch h
  | condS _ _ => exact fun h _ => nomatch h
  | switchS _ _ _ _ => exact fun h _ => nomatch h
  | forS _ _ _ _ => exact fun h _ => nomatch h
  | exprStmtS => exact fun h _ => nomatch h
  | breakS => exact fun h _ => nomatch h
  | continueS => exact fun h _ => nomatch h
  | leaveS => exact fun h _ => nomatch h
  | loopL _ _ _ _ => exact fun h _ => nomatch h
  | casesNil => exact fun h _ => nomatch h
  | casesCons _ _ _ _ => exact fun h _ => nomatch h
  | odfltNone => exact fun h _ => nomatch h
  | odfltSome _ _ => exact fun h _ => nomatch h

/-- Construct the left-side run of a peeled drop prefix: it changes no
state, extends the left environment with fresh insertions, and yields a
chaining function into the remaining sequence. -/
theorem leadDrops_run {bound : List Ident} {ss mid : List (Stmt Op)}
    (h : LeadDrops bound ss mid) :
    ∀ {funs : FunEnv D} {V₁ V₂ : VEnv D} {ins : List (Nat × Ident)}
      (st : EvmState), MIns ins V₁ V₂ → BoundOK V₂ bound →
      ∃ (V₁' : VEnv D) (insN : List (Nat × Ident)),
        MIns (insN ++ ins) V₁' V₂ ∧
        (∀ p ∈ insN, V₁.length ≤ p.1) ∧
        (∀ p ∈ insN, stmtsMentions p.2 mid = false) ∧
        (mid = ss → insN = [] ∧ V₁' = V₁) ∧
        (∀ {V' : VEnv D} {st' : EvmState} {o : Outcome},
          Step D funs V₁' st (.stmts mid) (.sres V' st' o) →
          Step D funs V₁ st (.stmts ss) (.sres V' st' o)) := by
  induction h with
  | done ss =>
      intro funs V₁ V₂ ins st hins hb
      exact ⟨V₁, [], hins, fun p hp => absurd hp (List.not_mem_nil),
        fun p hp => absurd hp (List.not_mem_nil), fun _ => ⟨rfl, rfl⟩,
        fun hstep => hstep⟩
  | @dropLet x val rest mid hval hm hld ih =>
      intro funs V₁ V₂ ins st hins hb
      obtain ⟨v, hstep⟩ := dropLet_run hval (hb.of_mins hins) funs st
      obtain ⟨V₁', insN, hins', hd, hmen, hrefl, hchain⟩ :=
        ih st (hins.insTop x v) hb
      refine ⟨V₁', insN ++ [(V₁.length, x)], ?_, ?_, ?_, ?_, ?_⟩
      · rw [List.append_assoc]
        exact hins'
      · intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · have := hd p hp
          simp only [List.length_cons] at this
          omega
        · rcases List.mem_singleton.mp hp with rfl
          exact Nat.le_refl _
      · intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · exact hmen p hp
        · rcases List.mem_singleton.mp hp with rfl
          exact hld.mentions_le x hm
      · intro hmid
        exfalso
        have h1 := hld.length_le
        have h2 : mid.length = rest.length + 1 := by rw [hmid]; simp
        omega
      · intro V' st' o hrun
        exact Step.seqCons hstep (hchain hrun)
  | @dropSelf x rest mid hx hld ih =>
      intro funs V₁ V₂ ins st hins hb
      have hbx : ∃ v, VEnv.get V₁ x = some v :=
        VEnv.get_isSome_of_key ((hb.of_mins hins) x hx)
      have hstep := dropSelf_run hbx funs st
      obtain ⟨V₁', insN, hins', hd, hmen, hrefl, hchain⟩ := ih st hins hb
      refine ⟨V₁', insN, hins', hd, hmen, ?_, ?_⟩
      · intro hmid
        exfalso
        have h1 := hld.length_le
        have h2 : mid.length = rest.length + 1 := by rw [hmid]; simp
        omega
      · intro V' st' o hrun
        exact Step.seqCons hstep (hchain hrun)
  | @dropRegion sink body rest mid hcheck hm hld ih =>
      intro funs V₁ V₂ ins st hins hb
      obtain ⟨v, hblock⟩ := discardBlock_run hcheck (hb.of_mins hins) funs st
      obtain ⟨V₁', insN, hins', hd, hmen, hrefl, hchain⟩ :=
        ih (funs := funs) st (hins.insTop sink v) hb
      refine ⟨V₁', insN ++ [(V₁.length, sink)], ?_, ?_, ?_, ?_, ?_⟩
      · rw [List.append_assoc]
        exact hins'
      · intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · have := hd p hp
          simp only [List.length_cons] at this
          omega
        · rcases List.mem_singleton.mp hp with rfl
          exact Nat.le_refl _
      · intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · exact hmen p hp
        · rcases List.mem_singleton.mp hp with rfl
          exact hld.mentions_le sink hm
      · intro hmid
        exfalso
        have h1 := hld.length_le
        have h2 : mid.length = rest.length + 2 := by rw [hmid]; simp
        omega
      · intro V' st' o hrun
        have hzero : Step D funs V₁ st (.stmt (.letDecl [sink] none))
            (.sres (bindZeros D [sink] ++ V₁) st .normal) := Step.letZero
        exact Step.seqCons hzero (Step.seqCons hblock (hchain hrun))

/-! ### The forward simulation -/

/-- An unchanged statement establishes the declaration names tracked by
`dpOut` when it finishes normally. -/
theorem BoundOK.afterStmt {bound : List Ident} {V V' : VEnv D}
    {funs : FunEnv D} {st st' : EvmState} {s : Stmt Op}
    (hb : BoundOK V bound)
    (hstep : Step D funs V st (.stmt s) (.sres V' st' .normal)) :
    BoundOK V' (dpOut bound s) := by
  cases s with
  | letDecl xs val =>
      cases hstep with
      | letZero =>
          intro x hx
          simp only [dpOut, List.mem_append] at hx
          rw [List.map_append, bindZeros_keys]
          exact hx.elim (fun h => List.mem_append_left _ h)
            (fun h => List.mem_append_right _ (hb x h))
      | letVal he hlen =>
          intro x hx
          simp only [dpOut, List.mem_append] at hx
          rw [List.map_append, zip_keys (by omega)]
          exact hx.elim (fun h => List.mem_append_left _ h)
            (fun h => List.mem_append_right _ (hb x h))
  | block _ => exact hb.mono hstep
  | funDef _ _ _ _ => exact hb.mono hstep
  | assign _ _ => exact hb.mono hstep
  | cond _ _ => exact hb.mono hstep
  | switch _ _ _ => exact hb.mono hstep
  | forLoop _ _ _ _ => exact hb.mono hstep
  | exprStmt _ => exact hb.mono hstep
  | «break» => exact hb.mono hstep
  | «continue» => exact hb.mono hstep
  | leave => exact hb.mono hstep

/-- Normal execution of an unchanged suffix establishes every declaration
name accumulated by `dpOutStmts`. -/
theorem BoundOK.afterStmts {bound : List Ident} {V V' : VEnv D}
    {funs : FunEnv D} {st st' : EvmState} {ss : List (Stmt Op)}
    (hb : BoundOK V bound)
    (hstep : Step D funs V st (.stmts ss) (.sres V' st' .normal)) :
    BoundOK V' (dpOutStmts bound ss) := by
  induction ss generalizing bound V st with
  | nil =>
      cases hstep with
      | seqNil => exact hb
  | cons s rest ih =>
      cases hstep with
      | seqCons hs hrest =>
          exact ih (hb.afterStmt hs) hrest
      | seqStop _ hne => exact absurd rfl hne

/-- Forward result correspondence, per code class of the source derivation:
expression classes yield identical results; statement classes yield the
same state and outcome with `MIns`-related environments (sequences may add
insertions, at or above the entry depth — none when the relation instance
is reflexive). -/
def DcResF (bound' : List Ident) (ins : List (Nat × Ident)) (len : Nat)
    (isRefl : Prop) : Code Op → Res D → Res D → Prop
  | .expr _, res₁, res₂ => res₂ = res₁
  | .args _, res₁, res₂ => res₂ = res₁
  | .stmt _, .sres V₁' st' o, res₂ =>
      ∃ V₂', res₂ = .sres V₂' st' o ∧ MIns ins V₁' V₂' ∧
        (o = .normal → BoundOK V₂' bound')
  | .stmts _, .sres V₁' st' o, res₂ =>
      ∃ V₂' insN, res₂ = .sres V₂' st' o ∧ MIns (insN ++ ins) V₁' V₂' ∧
        (∀ p ∈ insN, len ≤ p.1) ∧ (isRefl → insN = []) ∧
        (o = .normal → BoundOK V₂' bound')
  | .loop _ _ _, .sres V₁' st' o, res₂ =>
      ∃ V₂', res₂ = .sres V₂' st' o ∧ MIns ins V₁' V₂'
  | .stmt _, .eres _, _ => False
  | .stmts _, .eres _, _ => False
  | .loop _ _ _, .eres _, _ => False

/-- **Forward simulation.** A source derivation, a removal relation on its
code, related function environments, `MIns`-related variable environments
(insertions unmentioned in the code), and boundness of the relation's
`bound` set on the target side yield a target derivation with
`DcResF`-corresponding results. -/
theorem dc_fwd {funs₁ : FunEnv D} {V₁ : VEnv D} {st : EvmState}
    {code : Code Op} {res₁ : Res D} (h : Step D funs₁ V₁ st code res₁) :
    ∀ {funs₂ : FunEnv D} {V₂ : VEnv D} {ins : List (Nat × Ident)}
      {bound bound' : List Ident} {pc' : PCode Op},
      DcFunsRel funs₁ funs₂ →
      DcRel bound bound' (toPCode code) pc' →
      MIns ins V₁ V₂ →
      InsFree ins code →
      BoundOK V₂ bound →
      ∃ res₂, Step D funs₂ V₂ st (ofPCode pc') res₂ ∧
        DcResF bound' ins V₁.length (toPCode code = pc') code res₁ res₂ := by
  induction h with
  | @lit funs V st l =>
      intro funs₂ V₂ ins bound bound' pc' hR hrel hins hfree hb
      cases hrel with
      | exprE => exact ⟨_, Step.lit, rfl⟩
  | @var funs V st x v hv =>
      intro funs₂ V₂ ins bound bound' pc' hR hrel hins hfree hb
      cases hrel with
      | exprE =>
          refine ⟨_, Step.var ?_, rfl⟩
          rw [← hins.get_ne (fun p hp => ?_)]
          · exact hv
          · have := hfree p hp
            simp only [codeMentions, exprMentions,
              decide_eq_false_iff_not] at this
            exact fun hc => this hc.symm
  | @builtinOk funs V st op args argvals st1 rets st2 ha hbi iha =>
      intro funs₂ V₂ ins bound bound' pc' hR hrel hins hfree hb
      cases hrel with
      | exprE =>
          have hfree' : InsFree ins (.args args) := hfree.mono (fun z hz => by
            simpa only [codeMentions, exprMentions] using hz)
          obtain ⟨res₂, hstep, hres⟩ := iha hR DcRel.argsE hins hfree' hb
          rw [show DcResF bound ins V.length _ (.args args) _ res₂ =
            (res₂ = _) from rfl] at hres
          subst hres
          exact ⟨_, Step.builtinOk hstep hbi, rfl⟩
  | @builtinHalt funs V st op args argvals st1 st2 ha hbi iha =>
      intro funs₂ V₂ ins bound bound' pc' hR hrel hins hfree hb
      cases hrel with
      | exprE =>
          have hfree' : InsFree ins (.args args) := hfree.mono (fun z hz => by
            simpa only [codeMentions, exprMentions] using hz)
          obtain ⟨res₂, hstep, hres⟩ := iha hR DcRel.argsE hins hfree' hb
          rw [show DcResF bound ins V.length _ (.args args) _ res₂ =
            (res₂ = _) from rfl] at hres
          subst hres
          exact ⟨_, Step.builtinHalt hstep hbi, rfl⟩
  | @builtinArgsHalt funs V st op args st1 ha iha =>
      intro funs₂ V₂ ins bound bound' pc' hR hrel hins hfree hb
      cases hrel with
      | exprE =>
          have hfree' : InsFree ins (.args args) := hfree.mono (fun z hz => by
            simpa only [codeMentions, exprMentions] using hz)
          obtain ⟨res₂, hstep, hres⟩ := iha hR DcRel.argsE hins hfree' hb
          rw [show DcResF bound ins V.length _ (.args args) _ res₂ =
            (res₂ = _) from rfl] at hres
          subst hres
          exact ⟨_, Step.builtinArgsHalt hstep, rfl⟩
  | @callOk funs V st fn args argvals st1 decl cenv Vend st2 o
      ha hl hlen hbody ho iha ihbody =>
      intro funs₂ V₂ ins bound bound' pc' hR hrel hins hfree hb
      cases hrel with
      | exprE =>
          have hfree' : InsFree ins (.args args) := hfree.mono (fun z hz => by
            simpa only [codeMentions, exprMentions] using hz)
          obtain ⟨res₂, hstep, hres⟩ := iha hR DcRel.argsE hins hfree' hb
          rw [show DcResF bound ins V.length _ (.args args) _ res₂ =
            (res₂ = _) from rfl] at hres
          subst hres
          obtain ⟨decl', cenv', hl', hpar, hret, ⟨b2, hbodyRel⟩, hRc⟩ :=
            lookupFun_dcFunsRel hR hl
          have hbOK : BoundOK (decl.params.zip argvals ++ bindZeros D decl.rets)
              (decl.params ++ decl.rets) := by
            intro y hy
            rw [List.map_append, bindZeros_keys,
              List.map_fst_zip (by omega)]
            exact hy
          obtain ⟨res₂b, hstepb, hresb⟩ := ihbody hRc (DcRel.blockS hbodyRel)
            (MIns.nil _) (InsFree.nil _) hbOK
          obtain ⟨Vend₂, rfl, hminsE, -⟩ := hresb
          obtain rfl := hminsE.nil_eq
          have hstepb' : Step D cenv'
              (decl'.params.zip argvals ++ bindZeros D decl'.rets) st1
              (.stmt (.block decl'.body)) (.sres Vend st2 o) := by
            rw [hpar, hret]; exact hstepb
          have hres := Step.callOk (fn := fn) hstep hl'
            (by rw [hpar]; exact hlen) hstepb' ho
          rw [hret] at hres
          exact ⟨_, hres, rfl⟩
  | @callHalt funs V st fn args argvals st1 decl cenv Vend st2
      ha hl hlen hbody iha ihbody =>
      intro funs₂ V₂ ins bound bound' pc' hR hrel hins hfree hb
      cases hrel with
      | exprE =>
          have hfree' : InsFree ins (.args args) := hfree.mono (fun z hz => by
            simpa only [codeMentions, exprMentions] using hz)
          obtain ⟨res₂, hstep, hres⟩ := iha hR DcRel.argsE hins hfree' hb
          rw [show DcResF bound ins V.length _ (.args args) _ res₂ =
            (res₂ = _) from rfl] at hres
          subst hres
          obtain ⟨decl', cenv', hl', hpar, hret, ⟨b2, hbodyRel⟩, hRc⟩ :=
            lookupFun_dcFunsRel hR hl
          have hbOK : BoundOK (decl.params.zip argvals ++ bindZeros D decl.rets)
              (decl.params ++ decl.rets) := by
            intro y hy
            rw [List.map_append, bindZeros_keys,
              List.map_fst_zip (by omega)]
            exact hy
          obtain ⟨res₂b, hstepb, hresb⟩ := ihbody hRc (DcRel.blockS hbodyRel)
            (MIns.nil _) (InsFree.nil _) hbOK
          obtain ⟨Vend₂, rfl, hminsE, -⟩ := hresb
          obtain rfl := hminsE.nil_eq
          have hstepb' : Step D cenv'
              (decl'.params.zip argvals ++ bindZeros D decl'.rets) st1
              (.stmt (.block decl'.body)) (.sres Vend st2 .halt) := by
            rw [hpar, hret]; exact hstepb
          exact ⟨_, Step.callHalt hstep hl' (by rw [hpar]; exact hlen)
            hstepb', rfl⟩
  | @callArgsHalt funs V st fn args st1 ha iha =>
      intro funs₂ V₂ ins bound bound' pc' hR hrel hins hfree hb
      cases hrel with
      | exprE =>
          have hfree' : InsFree ins (.args args) := hfree.mono (fun z hz => by
            simpa only [codeMentions, exprMentions] using hz)
          obtain ⟨res₂, hstep, hres⟩ := iha hR DcRel.argsE hins hfree' hb
          rw [show DcResF bound ins V.length _ (.args args) _ res₂ =
            (res₂ = _) from rfl] at hres
          subst hres
          exact ⟨_, Step.callArgsHalt hstep, rfl⟩
  | @argsNil funs V st =>
      intro funs₂ V₂ ins bound bound' pc' hR hrel hins hfree hb
      cases hrel with
      | argsE => exact ⟨_, Step.argsNil, rfl⟩
  | @argsCons funs V st e rest restvals st1 v st2 hrest he ihrest ihe =>
      intro funs₂ V₂ ins bound bound' pc' hR hrel hins hfree hb
      cases hrel with
      | argsE =>
          have hfreeR : InsFree ins (.args rest) := hfree.mono (fun z hz => by
            simp only [codeMentions, argsMentions, Bool.or_eq_false_iff] at hz
            simpa only [codeMentions] using hz.2)
          have hfreeE : InsFree ins (.expr e) := hfree.mono (fun z hz => by
            simp only [codeMentions, argsMentions, Bool.or_eq_false_iff] at hz
            simpa only [codeMentions] using hz.1)
          obtain ⟨res₂, hstepr, hresr⟩ := ihrest hR DcRel.argsE hins hfreeR hb
          rw [show DcResF bound ins V.length _ (.args rest) _ res₂ =
            (res₂ = _) from rfl] at hresr
          subst hresr
          obtain ⟨res₃, hstepe, hrese⟩ := ihe hR DcRel.exprE hins hfreeE hb
          rw [show DcResF bound ins V.length _ (.expr e) _ res₃ =
            (res₃ = _) from rfl] at hrese
          subst hrese
          exact ⟨_, Step.argsCons hstepr hstepe, rfl⟩
  | @argsRestHalt funs V st e rest st1 hrest ihrest =>
      intro funs₂ V₂ ins bound bound' pc' hR hrel hins hfree hb
      cases hrel with
      | argsE =>
          have hfreeR : InsFree ins (.args rest) := hfree.mono (fun z hz => by
            simp only [codeMentions, argsMentions, Bool.or_eq_false_iff] at hz
            simpa only [codeMentions] using hz.2)
          obtain ⟨res₂, hstepr, hresr⟩ := ihrest hR DcRel.argsE hins hfreeR hb
          rw [show DcResF bound ins V.length _ (.args rest) _ res₂ =
            (res₂ = _) from rfl] at hresr
          subst hresr
          exact ⟨_, Step.argsRestHalt hstepr, rfl⟩
  | @argsHeadHalt funs V st e rest restvals st1 st2 hrest he ihrest ihe =>
      intro funs₂ V₂ ins bound bound' pc' hR hrel hins hfree hb
      cases hrel with
      | argsE =>
          have hfreeR : InsFree ins (.args rest) := hfree.mono (fun z hz => by
            simp only [codeMentions, argsMentions, Bool.or_eq_false_iff] at hz
            simpa only [codeMentions] using hz.2)
          have hfreeE : InsFree ins (.expr e) := hfree.mono (fun z hz => by
            simp only [codeMentions, argsMentions, Bool.or_eq_false_iff] at hz
            simpa only [codeMentions] using hz.1)
          obtain ⟨res₂, hstepr, hresr⟩ := ihrest hR DcRel.argsE hins hfreeR hb
          rw [show DcResF bound ins V.length _ (.args rest) _ res₂ =
            (res₂ = _) from rfl] at hresr
          subst hresr
          obtain ⟨res₃, hstepe, hrese⟩ := ihe hR DcRel.exprE hins hfreeE hb
          rw [show DcResF bound ins V.length _ (.expr e) _ res₃ =
            (res₃ = _) from rfl] at hrese
          subst hrese
          exact ⟨_, Step.argsHeadHalt hstepr hstepe, rfl⟩
  | @funDef funs V st n ps rs b =>
      intro funs₂ V₂ ins bound bound' pc' hR hrel hins hfree hb
      cases hrel with
      | funDefS hbody =>
          exact ⟨_, Step.funDef, V₂, rfl, hins, fun _ => hb⟩
  | @block funs V st body Vb stb o hbstep ihb =>
      intro funs₂ V₂ ins bound bound' pc' hR hrel hins hfree hb
      cases hrel with
      | @blockS _ bx _ body' hbodyRel =>
          have hfree' : InsFree ins (.stmts body) := hfree.mono (fun z hz => by
            simpa only [codeMentions, stmtMentions] using hz)
          obtain ⟨res₂, hstep, hres⟩ := ihb
            (List.Forall₂.cons (hbodyRel.hoist_scopeRel rfl rfl) hR)
            hbodyRel hins hfree' hb
          obtain ⟨Vb₂, insN, rfl, hminsB, hdepth, -, -⟩ := hres
          refine ⟨_, Step.block hstep, restore V₂ Vb₂, rfl,
            MIns.restore hins hminsB hdepth, fun _ => ?_⟩
          intro y hy
          rw [restore_keys (venvKeys_suffix hstep rfl) (venvLen_mono hstep rfl)]
          exact hb y hy
  | @letZero funs V st vars =>
      intro funs₂ V₂ ins bound bound' pc' hR hrel hins hfree hb
      cases hrel with
      | letS =>
          refine ⟨_, Step.letZero, bindZeros D vars ++ V₂, rfl,
            hins.prepend _, fun _ => ?_⟩
          intro y hy
          rw [List.map_append, bindZeros_keys]
          rcases List.mem_append.mp hy with hy | hy
          · exact List.mem_append.mpr (Or.inl hy)
          · exact List.mem_append.mpr (Or.inr (hb y hy))
  | @letVal funs V st vars e vals st1 he hlen ihe =>
      intro funs₂ V₂ ins bound bound' pc' hR hrel hins hfree hb
      cases hrel with
      | letS =>
          have hfreeE : InsFree ins (.expr e) := hfree.mono (fun z hz => by
            simp only [codeMentions, stmtMentions, optExprMentions,
              Bool.or_eq_false_iff] at hz
            simpa only [codeMentions] using hz.2)
          obtain ⟨res₂, hstepe, hrese⟩ := ihe hR DcRel.exprE hins hfreeE hb
          rw [show DcResF bound ins V.length _ (.expr e) _ res₂ =
            (res₂ = _) from rfl] at hrese
          subst hrese
          refine ⟨_, Step.letVal hstepe hlen, vars.zip vals ++ V₂, rfl,
            hins.prepend _, fun _ => ?_⟩
          intro y hy
          rw [List.map_append, List.map_fst_zip (by omega)]
          rcases List.mem_append.mp hy with hy | hy
          · exact List.mem_append.mpr (Or.inl hy)
          · exact List.mem_append.mpr (Or.inr (hb y hy))
  | @letHalt funs V st vars e st1 he ihe =>
      intro funs₂ V₂ ins bound bound' pc' hR hrel hins hfree hb
      cases hrel with
      | letS =>
          have hfreeE : InsFree ins (.expr e) := hfree.mono (fun z hz => by
            simp only [codeMentions, stmtMentions, optExprMentions,
              Bool.or_eq_false_iff] at hz
            simpa only [codeMentions] using hz.2)
          obtain ⟨res₂, hstepe, hrese⟩ := ihe hR DcRel.exprE hins hfreeE hb
          rw [show DcResF bound ins V.length _ (.expr e) _ res₂ =
            (res₂ = _) from rfl] at hrese
          subst hrese
          exact ⟨_, Step.letHalt hstepe, V₂, rfl, hins, fun h => nomatch h⟩
  | @assignVal funs V st vars e vals st1 he hlen ihe =>
      intro funs₂ V₂ ins bound bound' pc' hR hrel hins hfree hb
      cases hrel with
      | assignS =>
          have hfreeE : InsFree ins (.expr e) := hfree.mono (fun z hz => by
            simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hz
            simpa only [codeMentions] using hz.2)
          have hdisj : ∀ p ∈ ins, p.2 ∉ vars := fun p hp => by
            have := hfree p hp
            simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff,
              decide_eq_false_iff_not] at this
            exact this.1
          obtain ⟨res₂, hstepe, hrese⟩ := ihe hR DcRel.exprE hins hfreeE hb
          rw [show DcResF bound ins V.length _ (.expr e) _ res₂ =
            (res₂ = _) from rfl] at hrese
          subst hrese
          refine ⟨_, Step.assignVal hstepe hlen, VEnv.setMany V₂ vars vals,
            rfl, MIns.setMany vals hins hdisj, fun _ => ?_⟩
          intro y hy
          rw [VEnv.setMany_keys]
          exact hb y hy
  | @assignHalt funs V st vars e st1 he ihe =>
      intro funs₂ V₂ ins bound bound' pc' hR hrel hins hfree hb
      cases hrel with
      | assignS =>
          have hfreeE : InsFree ins (.expr e) := hfree.mono (fun z hz => by
            simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hz
            simpa only [codeMentions] using hz.2)
          obtain ⟨res₂, hstepe, hrese⟩ := ihe hR DcRel.exprE hins hfreeE hb
          rw [show DcResF bound ins V.length _ (.expr e) _ res₂ =
            (res₂ = _) from rfl] at hrese
          subst hrese
          exact ⟨_, Step.assignHalt hstepe, V₂, rfl, hins, fun h => nomatch h⟩
  | @exprStmt funs V st e st1 he ihe =>
      intro funs₂ V₂ ins bound bound' pc' hR hrel hins hfree hb
      cases hrel with
      | exprStmtS =>
          have hfreeE : InsFree ins (.expr e) := hfree.mono (fun z hz => by
            simpa only [codeMentions, stmtMentions] using hz)
          obtain ⟨res₂, hstepe, hrese⟩ := ihe hR DcRel.exprE hins hfreeE hb
          rw [show DcResF bound ins V.length _ (.expr e) _ res₂ =
            (res₂ = _) from rfl] at hrese
          subst hrese
          exact ⟨_, Step.exprStmt hstepe, V₂, rfl, hins, fun _ => hb⟩
  | @exprStmtHalt funs V st e st1 he ihe =>
      intro funs₂ V₂ ins bound bound' pc' hR hrel hins hfree hb
      cases hrel with
      | exprStmtS =>
          have hfreeE : InsFree ins (.expr e) := hfree.mono (fun z hz => by
            simpa only [codeMentions, stmtMentions] using hz)
          obtain ⟨res₂, hstepe, hrese⟩ := ihe hR DcRel.exprE hins hfreeE hb
          rw [show DcResF bound ins V.length _ (.expr e) _ res₂ =
            (res₂ = _) from rfl] at hrese
          subst hrese
          exact ⟨_, Step.exprStmtHalt hstepe, V₂, rfl, hins, fun h => nomatch h⟩
  | @ifTrue funs V st c body cv st1 V' st2 o hc hcv hbstep ihc ihb =>
      intro funs₂ V₂ ins bound bound' pc' hR hrel hins hfree hb
      cases hrel with
      | condS hbodyRel =>
          have hfreeC : InsFree ins (.expr c) := hfree.mono (fun z hz => by
            simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hz
            simpa only [codeMentions] using hz.1)
          have hfreeB : InsFree ins (.stmt (.block body)) :=
            hfree.mono (fun z hz => by
              simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hz
              simpa only [codeMentions, stmtMentions] using hz.2)
          obtain ⟨res₂, hstepc, hresc⟩ := ihc hR DcRel.exprE hins hfreeC hb
          rw [show DcResF bound ins V.length _ (.expr c) _ res₂ =
            (res₂ = _) from rfl] at hresc
          subst hresc
          obtain ⟨res₃, hstepb, hresb⟩ := ihb hR (DcRel.blockS hbodyRel)
            hins hfreeB hb
          obtain ⟨V₂', rfl, hmins, hbAfter⟩ := hresb
          exact ⟨_, Step.ifTrue hstepc hcv hstepb, V₂', rfl, hmins, hbAfter⟩
  | @ifFalse funs V st c body cv st1 hc hcv ihc =>
      intro funs₂ V₂ ins bound bound' pc' hR hrel hins hfree hb
      cases hrel with
      | condS hbodyRel =>
          have hfreeC : InsFree ins (.expr c) := hfree.mono (fun z hz => by
            simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hz
            simpa only [codeMentions] using hz.1)
          obtain ⟨res₂, hstepc, hresc⟩ := ihc hR DcRel.exprE hins hfreeC hb
          rw [show DcResF bound ins V.length _ (.expr c) _ res₂ =
            (res₂ = _) from rfl] at hresc
          subst hresc
          exact ⟨_, Step.ifFalse hstepc hcv, V₂, rfl, hins, fun _ => hb⟩
  | @ifHalt funs V st c body st1 hc ihc =>
      intro funs₂ V₂ ins bound bound' pc' hR hrel hins hfree hb
      cases hrel with
      | condS hbodyRel =>
          have hfreeC : InsFree ins (.expr c) := hfree.mono (fun z hz => by
            simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hz
            simpa only [codeMentions] using hz.1)
          obtain ⟨res₂, hstepc, hresc⟩ := ihc hR DcRel.exprE hins hfreeC hb
          rw [show DcResF bound ins V.length _ (.expr c) _ res₂ =
            (res₂ = _) from rfl] at hresc
          subst hresc
          exact ⟨_, Step.ifHalt hstepc, V₂, rfl, hins, fun h => nomatch h⟩
  | @switchExec funs V st c cases dflt cv st1 V' st2 o hc hsel ihc ihsel =>
      intro funs₂ V₂ ins bound bound' pc' hR hrel hins hfree hb
      cases hrel with
      | switchS hcs hd =>
          have hfreeC : InsFree ins (.expr c) := hfree.mono (fun z hz => by
            simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hz
            simpa only [codeMentions] using hz.1.1)
          obtain ⟨res₂, hstepc, hresc⟩ := ihc hR DcRel.exprE hins hfreeC hb
          rw [show DcResF bound ins V.length _ (.expr c) _ res₂ =
            (res₂ = _) from rfl] at hresc
          subst hresc
          obtain ⟨bsel, hselRel⟩ := DcRel.selectRel hcs hd cv
          have hfreeSel : InsFree ins
              (.stmt (.block (selectSwitch D cv cases dflt))) :=
            hfree.mono (fun z hz => by
              simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hz
              simp only [codeMentions, stmtMentions]
              exact selectSwitch_not_mentions hz.1.2 hz.2)
          obtain ⟨res₃, hstepsel, hressel⟩ := ihsel hR (DcRel.blockS hselRel)
            hins hfreeSel hb
          obtain ⟨V₂', rfl, hmins, hbAfter⟩ := hressel
          exact ⟨_, Step.switchExec hstepc hstepsel, V₂', rfl, hmins, hbAfter⟩
  | @switchHalt funs V st c cases dflt st1 hc ihc =>
      intro funs₂ V₂ ins bound bound' pc' hR hrel hins hfree hb
      cases hrel with
      | switchS hcs hd =>
          have hfreeC : InsFree ins (.expr c) := hfree.mono (fun z hz => by
            simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hz
            simpa only [codeMentions] using hz.1.1)
          obtain ⟨res₂, hstepc, hresc⟩ := ihc hR DcRel.exprE hins hfreeC hb
          rw [show DcResF bound ins V.length _ (.expr c) _ res₂ =
            (res₂ = _) from rfl] at hresc
          subst hresc
          exact ⟨_, Step.switchHalt hstepc, V₂, rfl, hins, fun h => nomatch h⟩
  | @forLoop funs V st init c post body Vinit stinit Vend stend o
      hinitstep hloop ihinit ihloop =>
      intro funs₂ V₂ ins bound bound' pc' hR hrel hins hfree hb
      cases hrel with
      | forS hpostRel hbodyRel =>
          obtain ⟨bi, hinitRel⟩ := DcRel.reflStmts bound init
          have hfreeI : InsFree ins (.stmts init) := hfree.mono (fun z hz => by
            simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hz
            simpa only [codeMentions] using hz.1.1.1)
          have hfreeL : InsFree ins (.loop c post body) :=
            hfree.mono (fun z hz => by
              simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hz
              simp only [codeMentions, Bool.or_eq_false_iff]
              exact ⟨⟨hz.1.1.2, hz.1.2⟩, hz.2⟩)
          obtain ⟨res₂, hstepi, hresi⟩ := ihinit
            (List.Forall₂.cons (DcScopeRel.refl _) hR) hinitRel hins hfreeI hb
          obtain ⟨Vinit₂, insN, rfl, hminsI, hdepthI, hreflI, hbI⟩ := hresi
          obtain rfl := hreflI rfl
          rw [List.nil_append] at hminsI
          obtain ⟨res₃, hstepl, hresl⟩ := ihloop
            (List.Forall₂.cons (DcScopeRel.refl _) hR)
            (DcRel.loopL hpostRel hbodyRel) hminsI hfreeL
            (BoundOK.mono hb hstepi)
          obtain ⟨Vend₂, rfl, hminsE⟩ := hresl
          refine ⟨_, Step.forLoop hstepi hstepl, restore V₂ Vend₂, rfl,
            MIns.restore hins (by simpa using hminsE)
              (fun p hp => absurd hp (List.not_mem_nil)), fun _ => ?_⟩
          intro y hy
          rw [restore_keys ((venvKeys_suffix hstepi rfl).trans
                (venvKeys_suffix hstepl rfl))
              (Nat.le_trans (venvLen_mono hstepi rfl)
                (venvLen_mono hstepl rfl))]
          exact hb y hy
  | @forInitHalt funs V st init c post body Vinit stinit hinitstep ihinit =>
      intro funs₂ V₂ ins bound bound' pc' hR hrel hins hfree hb
      cases hrel with
      | forS hpostRel hbodyRel =>
          obtain ⟨bi, hinitRel⟩ := DcRel.reflStmts bound init
          have hfreeI : InsFree ins (.stmts init) := hfree.mono (fun z hz => by
            simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hz
            simpa only [codeMentions] using hz.1.1.1)
          obtain ⟨res₂, hstepi, hresi⟩ := ihinit
            (List.Forall₂.cons (DcScopeRel.refl _) hR) hinitRel hins hfreeI hb
          obtain ⟨Vinit₂, insN, rfl, hminsI, hdepthI, hreflI, -⟩ := hresi
          obtain rfl := hreflI rfl
          rw [List.nil_append] at hminsI
          exact ⟨_, Step.forInitHalt hstepi, restore V₂ Vinit₂, rfl,
            MIns.restore hins (by simpa using hminsI)
              (fun p hp => absurd hp (List.not_mem_nil)),
            fun h => nomatch h⟩
  | @«break» funs V st =>
      intro funs₂ V₂ ins bound bound' pc' hR hrel hins hfree hb
      cases hrel with
      | breakS => exact ⟨_, Step.break, V₂, rfl, hins, fun h => nomatch h⟩
  | @«continue» funs V st =>
      intro funs₂ V₂ ins bound bound' pc' hR hrel hins hfree hb
      cases hrel with
      | continueS =>
          exact ⟨_, Step.continue, V₂, rfl, hins, fun h => nomatch h⟩
  | @leave funs V st =>
      intro funs₂ V₂ ins bound bound' pc' hR hrel hins hfree hb
      cases hrel with
      | leaveS => exact ⟨_, Step.leave, V₂, rfl, hins, fun h => nomatch h⟩
  | @seqNil funs V st =>
      intro funs₂ V₂ ins bound bound' pc' hR hrel hins hfree hb
      cases hrel with
      | nilSS =>
          exact ⟨_, Step.seqNil, V₂, [], rfl, by simpa using hins,
            fun p hp => absurd hp (List.not_mem_nil), fun _ => rfl,
            fun _ => hb⟩
  | @seqCons funs V st s rest Vm1 stm1 Vm2 stm2 o hs hrest ihs ihrest =>
      intro funs₂ V₂ ins bound bound' pc' hR hrel hins hfree hb
      cases hrel with
      | @consSS _ b1 _ _ s' _ rest' hsRel hrestRel =>
          have hfreeS : InsFree ins (.stmt s) := hfree.mono (fun z hz => by
            simp only [codeMentions, stmtsMentions, Bool.or_eq_false_iff] at hz
            simpa only [codeMentions] using hz.1)
          have hfreeRest : InsFree ins (.stmts rest) :=
            hfree.mono (fun z hz => by
              simp only [codeMentions, stmtsMentions,
                Bool.or_eq_false_iff] at hz
              simpa only [codeMentions] using hz.2)
          obtain ⟨res₂, hstep1, hres1⟩ := ihs hR hsRel hins hfreeS hb
          obtain ⟨V₂1, rfl, hmins1, hbAfter1⟩ := hres1
          obtain ⟨res₃, hstep2, hres2⟩ := ihrest hR hrestRel hmins1 hfreeRest
            (hbAfter1 rfl)
          obtain ⟨V₂2, insN, rfl, hmins2, hdepth2, hrefl2, hbAfter2⟩ := hres2
          refine ⟨_, Step.seqCons hstep1 hstep2, V₂2, insN, rfl, hmins2,
            ?_, ?_, hbAfter2⟩
          · intro p hp
            exact Nat.le_trans (venvLen_mono hs rfl) (hdepth2 p hp)
          · intro heq
            injection heq with heq
            injection heq with heq1 heq2
            subst heq1; subst heq2
            exact hrefl2 rfl
      | @dropSS _ _ x val _ rest' hval hm htailRel =>
          obtain ⟨v, rfl, rfl, -⟩ := dropLet_inv hval hs
          have hfree' : InsFree ((V.length, x) :: ins) (.stmts rest) := by
            intro p hp
            rcases List.mem_cons.mp hp with rfl | hp
            · simpa only [codeMentions] using hm
            · have := hfree p hp
              simp only [codeMentions, stmtsMentions,
                Bool.or_eq_false_iff] at this
              simpa only [codeMentions] using this.2
          obtain ⟨res₂, hstep2, hres2⟩ := ihrest hR htailRel
            (hins.insTop x v) hfree' hb
          obtain ⟨V₂2, insN, rfl, hmins2, hdepth2, hrefl2, hbAfter2⟩ := hres2
          refine ⟨_, hstep2, V₂2, insN ++ [(V.length, x)], rfl, ?_, ?_, ?_,
            hbAfter2⟩
          · rw [List.append_assoc]
            exact hmins2
          · intro p hp
            rcases List.mem_append.mp hp with hp | hp
            · have := hdepth2 p hp
              simp only [List.length_cons] at this
              omega
            · rcases List.mem_singleton.mp hp with rfl
              exact Nat.le_refl _
          · intro heq
            exfalso
            injection heq with heq
            have h1 := DcRel.stmts_len htailRel rfl rfl
            have h2 : rest'.length = rest.length + 1 := by
              rw [← heq]; simp
            omega
      | @dropSelfSS _ _ x _ rest' hx htailRel =>
          obtain ⟨rfl, rfl, -⟩ := dropSelf_inv hs
          have hfreeRest : InsFree ins (.stmts rest) :=
            hfree.mono (fun z hz => by
              simp only [codeMentions, stmtsMentions,
                Bool.or_eq_false_iff] at hz
              simpa only [codeMentions] using hz.2)
          obtain ⟨res₂, hstep2, hres2⟩ := ihrest hR htailRel hins hfreeRest hb
          obtain ⟨V₂2, insN, rfl, hmins2, hdepth2, hrefl2, hbAfter2⟩ := hres2
          refine ⟨_, hstep2, V₂2, insN, rfl, hmins2, hdepth2, ?_, hbAfter2⟩
          intro heq
          exfalso
          injection heq with heq
          have h1 := DcRel.stmts_len htailRel rfl rfl
          have h2 : rest'.length = rest.length + 1 := by
            rw [← heq]; simp
          omega
      | @dropRegionSS _ sink body tail hcheck hm hcf =>
          cases hs with
          | letZero =>
              cases hrest with
              | seqCons hblock htail =>
                  obtain ⟨v, hV, hst, -⟩ :=
                    discardBlock_inv hcheck (hb.of_mins hins) hblock
                  rw [hV, hst] at htail
                  have hld : LeadDrops bound
                      (.letDecl [sink] none :: .block body :: tail) tail :=
                    .dropRegion hcheck hm (.done tail)
                  have hfreeTail : InsFree ((V.length, sink) :: ins) (.stmts tail) := by
                    intro p hp
                    rcases List.mem_cons.mp hp with rfl | hp
                    · simpa only [codeMentions] using hm
                    · exact hld.mentions_le p.2
                        (by simpa only [codeMentions] using hfree p hp)
                  obtain ⟨V₂', htailSame, hmins'⟩ :=
                    (hins.insTop sink v).frameRemove htail hfreeTail
                  have htail₂ := YulEvmCompiler.Optimizer.Step.callFree_funs
                    htailSame (by simpa [codeCallFree] using hcf) funs₂
                  refine ⟨_, htail₂, V₂', [(V.length, sink)], rfl, ?_, ?_, ?_, ?_⟩
                  · simpa using hmins'
                  · intro p hp
                    rcases List.mem_singleton.mp hp with rfl
                    exact Nat.le_refl _
                  · intro heq
                    exfalso
                    injection heq with heq
                    have := congrArg List.length heq
                    simp at this
                    omega
                  · intro ho
                    subst ho
                    exact hb.afterStmts htail₂
              | seqStop hblock hne =>
                  obtain ⟨-, -, -, ho⟩ :=
                    discardBlock_inv hcheck (hb.of_mins hins) hblock
                  exact absurd ho hne
  | @seqStop funs V st s rest Vm1 stm1 o hs hne ihs =>
      intro funs₂ V₂ ins bound bound' pc' hR hrel hins hfree hb
      cases hrel with
      | @consSS _ b1 _ _ s' _ rest' hsRel hrestRel =>
          have hfreeS : InsFree ins (.stmt s) := hfree.mono (fun z hz => by
            simp only [codeMentions, stmtsMentions, Bool.or_eq_false_iff] at hz
            simpa only [codeMentions] using hz.1)
          obtain ⟨res₂, hstep1, hres1⟩ := ihs hR hsRel hins hfreeS hb
          obtain ⟨V₂1, rfl, hmins1, -⟩ := hres1
          refine ⟨_, Step.seqStop hstep1 hne, V₂1, [], rfl,
            by simpa using hmins1,
            fun p hp => absurd hp (List.not_mem_nil), fun _ => rfl,
            fun ho => absurd ho hne⟩
      | dropSS hval hm htailRel =>
          obtain ⟨v, -, -, ho⟩ := dropLet_inv hval hs
          exact absurd ho hne
      | dropSelfSS hx htailRel =>
          obtain ⟨-, -, ho⟩ := dropSelf_inv hs
          exact absurd ho hne
      | dropRegionSS hcheck hm hcf =>
          cases hs with
          | letZero => exact absurd rfl hne
  | @loopDone funs V st c post body cv st1 hc hz ihc =>
      intro funs₂ V₂ ins bound bound' pc' hR hrel hins hfree hb
      cases hrel with
      | loopL hpostRel hbodyRel =>
          have hfreeC : InsFree ins (.expr c) := hfree.mono (fun z hz => by
            simp only [codeMentions, Bool.or_eq_false_iff] at hz
            simpa only [codeMentions] using hz.1.1)
          obtain ⟨res₂, hstepc, hresc⟩ := ihc hR DcRel.exprE hins hfreeC hb
          rw [show DcResF bound ins V.length _ (.expr c) _ res₂ =
            (res₂ = _) from rfl] at hresc
          subst hresc
          exact ⟨_, Step.loopDone hstepc hz, V₂, rfl, hins⟩
  | @loopCondHalt funs V st c post body st1 hc ihc =>
      intro funs₂ V₂ ins bound bound' pc' hR hrel hins hfree hb
      cases hrel with
      | loopL hpostRel hbodyRel =>
          have hfreeC : InsFree ins (.expr c) := hfree.mono (fun z hz => by
            simp only [codeMentions, Bool.or_eq_false_iff] at hz
            simpa only [codeMentions] using hz.1.1)
          obtain ⟨res₂, hstepc, hresc⟩ := ihc hR DcRel.exprE hins hfreeC hb
          rw [show DcResF bound ins V.length _ (.expr c) _ res₂ =
            (res₂ = _) from rfl] at hresc
          subst hresc
          exact ⟨_, Step.loopCondHalt hstepc, V₂, rfl, hins⟩
  | @loopStep funs V st c post body cv st1 Vb stb ob Vp stp Vend stend o
      hc hnz hbstep hob hpost hrec ihc ihb ihp ihrec =>
      intro funs₂ V₂ ins bound bound' pc' hR hrel hins hfree hb
      cases hrel with
      | loopL hpostRel hbodyRel =>
          have hfreeC : InsFree ins (.expr c) := hfree.mono (fun z hz => by
            simp only [codeMentions, Bool.or_eq_false_iff] at hz
            simpa only [codeMentions] using hz.1.1)
          have hfreeB : InsFree ins (.stmt (.block body)) :=
            hfree.mono (fun z hz => by
              simp only [codeMentions, Bool.or_eq_false_iff] at hz
              simpa only [codeMentions, stmtMentions] using hz.2)
          have hfreeP : InsFree ins (.stmt (.block post)) :=
            hfree.mono (fun z hz => by
              simp only [codeMentions, Bool.or_eq_false_iff] at hz
              simpa only [codeMentions, stmtMentions] using hz.1.2)
          obtain ⟨res₂, hstepc, hresc⟩ := ihc hR DcRel.exprE hins hfreeC hb
          rw [show DcResF bound ins V.length _ (.expr c) _ res₂ =
            (res₂ = _) from rfl] at hresc
          subst hresc
          obtain ⟨res₃, hstepb, hresb⟩ := ihb hR (DcRel.blockS hbodyRel)
            hins hfreeB hb
          obtain ⟨Vb₂, rfl, hminsB, -⟩ := hresb
          have hbB : BoundOK Vb₂ bound := BoundOK.mono hb hstepb
          obtain ⟨res₄, hstepp, hresp⟩ := ihp hR (DcRel.blockS hpostRel)
            hminsB hfreeP hbB
          obtain ⟨Vp₂, rfl, hminsP, -⟩ := hresp
          have hbP : BoundOK Vp₂ bound := BoundOK.mono hbB hstepp
          obtain ⟨res₅, hstepr, hresr⟩ := ihrec hR
            (DcRel.loopL hpostRel hbodyRel) hminsP hfree hbP
          obtain ⟨Vend₂, rfl, hminsE⟩ := hresr
          exact ⟨_, Step.loopStep hstepc hnz hstepb hob hstepp hstepr,
            Vend₂, rfl, hminsE⟩
  | @loopPostHalt funs V st c post body cv st1 Vb stb ob Vp stp
      hc hnz hbstep hob hpost ihc ihb ihp =>
      intro funs₂ V₂ ins bound bound' pc' hR hrel hins hfree hb
      cases hrel with
      | loopL hpostRel hbodyRel =>
          have hfreeC : InsFree ins (.expr c) := hfree.mono (fun z hz => by
            simp only [codeMentions, Bool.or_eq_false_iff] at hz
            simpa only [codeMentions] using hz.1.1)
          have hfreeB : InsFree ins (.stmt (.block body)) :=
            hfree.mono (fun z hz => by
              simp only [codeMentions, Bool.or_eq_false_iff] at hz
              simpa only [codeMentions, stmtMentions] using hz.2)
          have hfreeP : InsFree ins (.stmt (.block post)) :=
            hfree.mono (fun z hz => by
              simp only [codeMentions, Bool.or_eq_false_iff] at hz
              simpa only [codeMentions, stmtMentions] using hz.1.2)
          obtain ⟨res₂, hstepc, hresc⟩ := ihc hR DcRel.exprE hins hfreeC hb
          rw [show DcResF bound ins V.length _ (.expr c) _ res₂ =
            (res₂ = _) from rfl] at hresc
          subst hresc
          obtain ⟨res₃, hstepb, hresb⟩ := ihb hR (DcRel.blockS hbodyRel)
            hins hfreeB hb
          obtain ⟨Vb₂, rfl, hminsB, -⟩ := hresb
          have hbB : BoundOK Vb₂ bound := BoundOK.mono hb hstepb
          obtain ⟨res₄, hstepp, hresp⟩ := ihp hR (DcRel.blockS hpostRel)
            hminsB hfreeP hbB
          obtain ⟨Vp₂, rfl, hminsP, -⟩ := hresp
          exact ⟨_, Step.loopPostHalt hstepc hnz hstepb hob hstepp,
            Vp₂, rfl, hminsP⟩
  | @loopBreak funs V st c post body cv st1 Vb stb hc hnz hbstep ihc ihb =>
      intro funs₂ V₂ ins bound bound' pc' hR hrel hins hfree hb
      cases hrel with
      | loopL hpostRel hbodyRel =>
          have hfreeC : InsFree ins (.expr c) := hfree.mono (fun z hz => by
            simp only [codeMentions, Bool.or_eq_false_iff] at hz
            simpa only [codeMentions] using hz.1.1)
          have hfreeB : InsFree ins (.stmt (.block body)) :=
            hfree.mono (fun z hz => by
              simp only [codeMentions, Bool.or_eq_false_iff] at hz
              simpa only [codeMentions, stmtMentions] using hz.2)
          obtain ⟨res₂, hstepc, hresc⟩ := ihc hR DcRel.exprE hins hfreeC hb
          rw [show DcResF bound ins V.length _ (.expr c) _ res₂ =
            (res₂ = _) from rfl] at hresc
          subst hresc
          obtain ⟨res₃, hstepb, hresb⟩ := ihb hR (DcRel.blockS hbodyRel)
            hins hfreeB hb
          obtain ⟨Vb₂, rfl, hminsB, -⟩ := hresb
          exact ⟨_, Step.loopBreak hstepc hnz hstepb, Vb₂, rfl, hminsB⟩
  | @loopLeave funs V st c post body cv st1 Vb stb hc hnz hbstep ihc ihb =>
      intro funs₂ V₂ ins bound bound' pc' hR hrel hins hfree hb
      cases hrel with
      | loopL hpostRel hbodyRel =>
          have hfreeC : InsFree ins (.expr c) := hfree.mono (fun z hz => by
            simp only [codeMentions, Bool.or_eq_false_iff] at hz
            simpa only [codeMentions] using hz.1.1)
          have hfreeB : InsFree ins (.stmt (.block body)) :=
            hfree.mono (fun z hz => by
              simp only [codeMentions, Bool.or_eq_false_iff] at hz
              simpa only [codeMentions, stmtMentions] using hz.2)
          obtain ⟨res₂, hstepc, hresc⟩ := ihc hR DcRel.exprE hins hfreeC hb
          rw [show DcResF bound ins V.length _ (.expr c) _ res₂ =
            (res₂ = _) from rfl] at hresc
          subst hresc
          obtain ⟨res₃, hstepb, hresb⟩ := ihb hR (DcRel.blockS hbodyRel)
            hins hfreeB hb
          obtain ⟨Vb₂, rfl, hminsB, -⟩ := hresb
          exact ⟨_, Step.loopLeave hstepc hnz hstepb, Vb₂, rfl, hminsB⟩
  | @loopBodyHalt funs V st c post body cv st1 Vb stb hc hnz hbstep ihc ihb =>
      intro funs₂ V₂ ins bound bound' pc' hR hrel hins hfree hb
      cases hrel with
      | loopL hpostRel hbodyRel =>
          have hfreeC : InsFree ins (.expr c) := hfree.mono (fun z hz => by
            simp only [codeMentions, Bool.or_eq_false_iff] at hz
            simpa only [codeMentions] using hz.1.1)
          have hfreeB : InsFree ins (.stmt (.block body)) :=
            hfree.mono (fun z hz => by
              simp only [codeMentions, Bool.or_eq_false_iff] at hz
              simpa only [codeMentions, stmtMentions] using hz.2)
          obtain ⟨res₂, hstepc, hresc⟩ := ihc hR DcRel.exprE hins hfreeC hb
          rw [show DcResF bound ins V.length _ (.expr c) _ res₂ =
            (res₂ = _) from rfl] at hresc
          subst hresc
          obtain ⟨res₃, hstepb, hresb⟩ := ihb hR (DcRel.blockS hbodyRel)
            hins hfreeB hb
          obtain ⟨Vb₂, rfl, hminsB, -⟩ := hresb
          exact ⟨_, Step.loopBodyHalt hstepc hnz hstepb, Vb₂, rfl, hminsB⟩

/-! ### The backward simulation -/

/-- A peel of maximal length is no peel at all. -/
theorem LeadDrops.eq_of_length {bound : List Ident} {ss mid : List (Stmt Op)}
    (h : LeadDrops bound ss mid) (hlen : mid.length = ss.length) :
    mid = ss := by
  cases h with
  | done _ => rfl
  | dropLet _ _ hld =>
      have := hld.length_le
      simp only [List.length_cons] at hlen
      omega
  | dropSelf _ hld =>
      have := hld.length_le
      simp only [List.length_cons] at hlen
      omega
  | dropRegion _ _ hld =>
      have := hld.length_le
      simp only [List.length_cons] at hlen
      omega

/-- A relation targeting a sequence has a sequence source. -/
theorem DcRel.src_stmts {bound b2 : List Ident} {pc : PCode Op}
    {ss' : List (Stmt Op)} (h : DcRel bound b2 pc (.stmts ss')) :
    ∃ ss, pc = .stmts ss := by
  cases h <;> exact ⟨_, rfl⟩

/-- Backward result correspondence (mirror of `DcResF`, matched on the
target's result). -/
def DcResB (bound' : List Ident) (ins : List (Nat × Ident)) (len : Nat)
    (isRefl : Prop) : Code Op → Res D → Res D → Prop
  | .expr _, res₁, res₂ => res₁ = res₂
  | .args _, res₁, res₂ => res₁ = res₂
  | .stmt _, res₁, .sres V₂' st' o =>
      ∃ V₁', res₁ = .sres V₁' st' o ∧ MIns ins V₁' V₂' ∧
        (o = .normal → BoundOK V₂' bound')
  | .stmts _, res₁, .sres V₂' st' o =>
      ∃ V₁' insN, res₁ = .sres V₁' st' o ∧ MIns (insN ++ ins) V₁' V₂' ∧
        (∀ p ∈ insN, len ≤ p.1) ∧ (isRefl → insN = []) ∧
        (o = .normal → BoundOK V₂' bound')
  | .loop _ _ _, res₁, .sres V₂' st' o =>
      ∃ V₁', res₁ = .sres V₁' st' o ∧ MIns ins V₁' V₂'
  | .stmt _, _, .eres _ => False
  | .stmts _, _, .eres _ => False
  | .loop _ _ _, _, .eres _ => False

/-- **Backward simulation.** A target derivation transports to a source
derivation with `DcResB`-corresponding results; dropped statements are
re-executed on the source side (`leadDrops_run`). -/
theorem dc_bwd {funs₂ : FunEnv D} {V₂ : VEnv D} {st : EvmState}
    {code : Code Op} {res₂ : Res D} (h : Step D funs₂ V₂ st code res₂) :
    ∀ {funs₁ : FunEnv D} {V₁ : VEnv D} {ins : List (Nat × Ident)}
      {bound bound' : List Ident} {pc : PCode Op},
      DcFunsRel funs₁ funs₂ →
      DcRel bound bound' pc (toPCode code) →
      MIns ins V₁ V₂ →
      InsFree ins (ofPCode pc) →
      BoundOK V₂ bound →
      ∃ res₁, Step D funs₁ V₁ st (ofPCode pc) res₁ ∧
        DcResB bound' ins V₁.length (pc = toPCode code) code res₁ res₂ := by
  induction h with
  | @lit funs V st l =>
      intro funs₁ V₁ ins bound bound' pc hR hrel hins hfree hb
      cases hrel with
      | exprE => exact ⟨_, Step.lit, rfl⟩
  | @var funs V st x v hv =>
      intro funs₁ V₁ ins bound bound' pc hR hrel hins hfree hb
      cases hrel with
      | exprE =>
          refine ⟨_, Step.var ?_, rfl⟩
          rw [hins.get_ne (fun p hp => ?_)]
          · exact hv
          · have := hfree p hp
            simp only [ofPCode, codeMentions, exprMentions,
              decide_eq_false_iff_not] at this
            exact fun hc => this hc.symm
  | @builtinOk funs V st op args argvals st1 rets st2 ha hbi iha =>
      intro funs₁ V₁ ins bound bound' pc hR hrel hins hfree hb
      cases hrel with
      | exprE =>
          have hfree' : InsFree ins (.args args) := hfree.mono (fun z hz => by
            simpa only [ofPCode, codeMentions, exprMentions] using hz)
          obtain ⟨res₁, hstep, hres⟩ := iha hR DcRel.argsE hins hfree' hb
          rw [show DcResB bound ins V₁.length _ (.args args) res₁ _ =
            (res₁ = _) from rfl] at hres
          subst hres
          exact ⟨_, Step.builtinOk hstep hbi, rfl⟩
  | @builtinHalt funs V st op args argvals st1 st2 ha hbi iha =>
      intro funs₁ V₁ ins bound bound' pc hR hrel hins hfree hb
      cases hrel with
      | exprE =>
          have hfree' : InsFree ins (.args args) := hfree.mono (fun z hz => by
            simpa only [ofPCode, codeMentions, exprMentions] using hz)
          obtain ⟨res₁, hstep, hres⟩ := iha hR DcRel.argsE hins hfree' hb
          rw [show DcResB bound ins V₁.length _ (.args args) res₁ _ =
            (res₁ = _) from rfl] at hres
          subst hres
          exact ⟨_, Step.builtinHalt hstep hbi, rfl⟩
  | @builtinArgsHalt funs V st op args st1 ha iha =>
      intro funs₁ V₁ ins bound bound' pc hR hrel hins hfree hb
      cases hrel with
      | exprE =>
          have hfree' : InsFree ins (.args args) := hfree.mono (fun z hz => by
            simpa only [ofPCode, codeMentions, exprMentions] using hz)
          obtain ⟨res₁, hstep, hres⟩ := iha hR DcRel.argsE hins hfree' hb
          rw [show DcResB bound ins V₁.length _ (.args args) res₁ _ =
            (res₁ = _) from rfl] at hres
          subst hres
          exact ⟨_, Step.builtinArgsHalt hstep, rfl⟩
  | @callOk funs V st fn args argvals st1 decl' cenv' Vend st2 o
      ha hl hlen hbody ho iha ihbody =>
      intro funs₁ V₁ ins bound bound' pc hR hrel hins hfree hb
      cases hrel with
      | exprE =>
          have hfree' : InsFree ins (.args args) := hfree.mono (fun z hz => by
            simpa only [ofPCode, codeMentions, exprMentions] using hz)
          obtain ⟨res₁, hstep, hres⟩ := iha hR DcRel.argsE hins hfree' hb
          rw [show DcResB bound ins V₁.length _ (.args args) res₁ _ =
            (res₁ = _) from rfl] at hres
          subst hres
          obtain ⟨decl, cenv, hl₁, hpar, hret, ⟨b2, hbodyRel⟩, hRc⟩ :=
            lookupFun_dcFunsRel_bwd hR hl
          have hbOK : BoundOK
              (decl'.params.zip argvals ++ bindZeros D decl'.rets)
              (decl.params ++ decl.rets) := by
            intro y hy
            rw [List.map_append, bindZeros_keys,
              List.map_fst_zip (by omega), hpar, hret]
            exact hy
          obtain ⟨res₁b, hstepb, hresb⟩ := ihbody hRc (DcRel.blockS hbodyRel)
            (MIns.nil _) (InsFree.nil _) hbOK
          obtain ⟨Vend₁, rfl, hminsE, -⟩ := hresb
          obtain rfl := hminsE.nil_eq
          have hstepb' : Step D cenv
              (decl.params.zip argvals ++ bindZeros D decl.rets) st1
              (.stmt (.block decl.body)) (.sres Vend₁ st2 o) := by
            rw [← hpar, ← hret]; exact hstepb
          have hres := Step.callOk (fn := fn) hstep hl₁
            (by rw [← hpar]; exact hlen) hstepb' ho
          rw [← hret] at hres
          exact ⟨_, hres, rfl⟩
  | @callHalt funs V st fn args argvals st1 decl' cenv' Vend st2
      ha hl hlen hbody iha ihbody =>
      intro funs₁ V₁ ins bound bound' pc hR hrel hins hfree hb
      cases hrel with
      | exprE =>
          have hfree' : InsFree ins (.args args) := hfree.mono (fun z hz => by
            simpa only [ofPCode, codeMentions, exprMentions] using hz)
          obtain ⟨res₁, hstep, hres⟩ := iha hR DcRel.argsE hins hfree' hb
          rw [show DcResB bound ins V₁.length _ (.args args) res₁ _ =
            (res₁ = _) from rfl] at hres
          subst hres
          obtain ⟨decl, cenv, hl₁, hpar, hret, ⟨b2, hbodyRel⟩, hRc⟩ :=
            lookupFun_dcFunsRel_bwd hR hl
          have hbOK : BoundOK
              (decl'.params.zip argvals ++ bindZeros D decl'.rets)
              (decl.params ++ decl.rets) := by
            intro y hy
            rw [List.map_append, bindZeros_keys,
              List.map_fst_zip (by omega), hpar, hret]
            exact hy
          obtain ⟨res₁b, hstepb, hresb⟩ := ihbody hRc (DcRel.blockS hbodyRel)
            (MIns.nil _) (InsFree.nil _) hbOK
          obtain ⟨Vend₁, rfl, hminsE, -⟩ := hresb
          obtain rfl := hminsE.nil_eq
          have hstepb' : Step D cenv
              (decl.params.zip argvals ++ bindZeros D decl.rets) st1
              (.stmt (.block decl.body)) (.sres Vend₁ st2 .halt) := by
            rw [← hpar, ← hret]; exact hstepb
          exact ⟨_, Step.callHalt hstep hl₁ (by rw [← hpar]; exact hlen)
            hstepb', rfl⟩
  | @callArgsHalt funs V st fn args st1 ha iha =>
      intro funs₁ V₁ ins bound bound' pc hR hrel hins hfree hb
      cases hrel with
      | exprE =>
          have hfree' : InsFree ins (.args args) := hfree.mono (fun z hz => by
            simpa only [ofPCode, codeMentions, exprMentions] using hz)
          obtain ⟨res₁, hstep, hres⟩ := iha hR DcRel.argsE hins hfree' hb
          rw [show DcResB bound ins V₁.length _ (.args args) res₁ _ =
            (res₁ = _) from rfl] at hres
          subst hres
          exact ⟨_, Step.callArgsHalt hstep, rfl⟩
  | @argsNil funs V st =>
      intro funs₁ V₁ ins bound bound' pc hR hrel hins hfree hb
      cases hrel with
      | argsE => exact ⟨_, Step.argsNil, rfl⟩
  | @argsCons funs V st e rest restvals st1 v st2 hrest he ihrest ihe =>
      intro funs₁ V₁ ins bound bound' pc hR hrel hins hfree hb
      cases hrel with
      | argsE =>
          have hfreeR : InsFree ins (.args rest) := hfree.mono (fun z hz => by
            simp only [ofPCode, codeMentions, argsMentions,
              Bool.or_eq_false_iff] at hz
            simpa only [codeMentions] using hz.2)
          have hfreeE : InsFree ins (.expr e) := hfree.mono (fun z hz => by
            simp only [ofPCode, codeMentions, argsMentions,
              Bool.or_eq_false_iff] at hz
            simpa only [codeMentions] using hz.1)
          obtain ⟨res₁, hstepr, hresr⟩ := ihrest hR DcRel.argsE hins hfreeR hb
          rw [show DcResB bound ins V₁.length _ (.args rest) res₁ _ =
            (res₁ = _) from rfl] at hresr
          subst hresr
          obtain ⟨res₂, hstepe, hrese⟩ := ihe hR DcRel.exprE hins hfreeE hb
          rw [show DcResB bound ins V₁.length _ (.expr e) res₂ _ =
            (res₂ = _) from rfl] at hrese
          subst hrese
          exact ⟨_, Step.argsCons hstepr hstepe, rfl⟩
  | @argsRestHalt funs V st e rest st1 hrest ihrest =>
      intro funs₁ V₁ ins bound bound' pc hR hrel hins hfree hb
      cases hrel with
      | argsE =>
          have hfreeR : InsFree ins (.args rest) := hfree.mono (fun z hz => by
            simp only [ofPCode, codeMentions, argsMentions,
              Bool.or_eq_false_iff] at hz
            simpa only [codeMentions] using hz.2)
          obtain ⟨res₁, hstepr, hresr⟩ := ihrest hR DcRel.argsE hins hfreeR hb
          rw [show DcResB bound ins V₁.length _ (.args rest) res₁ _ =
            (res₁ = _) from rfl] at hresr
          subst hresr
          exact ⟨_, Step.argsRestHalt hstepr, rfl⟩
  | @argsHeadHalt funs V st e rest restvals st1 st2 hrest he ihrest ihe =>
      intro funs₁ V₁ ins bound bound' pc hR hrel hins hfree hb
      cases hrel with
      | argsE =>
          have hfreeR : InsFree ins (.args rest) := hfree.mono (fun z hz => by
            simp only [ofPCode, codeMentions, argsMentions,
              Bool.or_eq_false_iff] at hz
            simpa only [codeMentions] using hz.2)
          have hfreeE : InsFree ins (.expr e) := hfree.mono (fun z hz => by
            simp only [ofPCode, codeMentions, argsMentions,
              Bool.or_eq_false_iff] at hz
            simpa only [codeMentions] using hz.1)
          obtain ⟨res₁, hstepr, hresr⟩ := ihrest hR DcRel.argsE hins hfreeR hb
          rw [show DcResB bound ins V₁.length _ (.args rest) res₁ _ =
            (res₁ = _) from rfl] at hresr
          subst hresr
          obtain ⟨res₂, hstepe, hrese⟩ := ihe hR DcRel.exprE hins hfreeE hb
          rw [show DcResB bound ins V₁.length _ (.expr e) res₂ _ =
            (res₂ = _) from rfl] at hrese
          subst hrese
          exact ⟨_, Step.argsHeadHalt hstepr hstepe, rfl⟩
  | @funDef funs V st n ps rs b =>
      intro funs₁ V₁ ins bound bound' pc hR hrel hins hfree hb
      cases hrel with
      | funDefS hbody =>
          exact ⟨_, Step.funDef, V₁, rfl, hins, fun _ => hb⟩
  | @block funs V st body' Vb₂ stb o hbstep ihb =>
      intro funs₁ V₁ ins bound bound' pc hR hrel hins hfree hb
      cases hrel with
      | @blockS _ bx body _ hbodyRel =>
          have hfree' : InsFree ins (.stmts body) := hfree.mono (fun z hz => by
            simpa only [ofPCode, codeMentions, stmtMentions] using hz)
          obtain ⟨res₁, hstep, hres⟩ := ihb
            (List.Forall₂.cons (hbodyRel.hoist_scopeRel rfl rfl) hR)
            hbodyRel hins hfree' hb
          obtain ⟨Vb₁, insN, rfl, hminsB, hdepth, -, -⟩ := hres
          refine ⟨_, Step.block hstep, restore V₁ Vb₁, rfl,
            MIns.restore hins hminsB hdepth, fun _ => ?_⟩
          intro y hy
          rw [restore_keys (venvKeys_suffix hbstep rfl)
            (venvLen_mono hbstep rfl)]
          exact hb y hy
  | @letZero funs V st vars =>
      intro funs₁ V₁ ins bound bound' pc hR hrel hins hfree hb
      cases hrel with
      | letS =>
          refine ⟨_, Step.letZero, bindZeros D vars ++ V₁, rfl,
            hins.prepend _, fun _ => ?_⟩
          intro y hy
          rw [List.map_append, bindZeros_keys]
          rcases List.mem_append.mp hy with hy | hy
          · exact List.mem_append.mpr (Or.inl hy)
          · exact List.mem_append.mpr (Or.inr (hb y hy))
  | @letVal funs V st vars e vals st1 he hlen ihe =>
      intro funs₁ V₁ ins bound bound' pc hR hrel hins hfree hb
      cases hrel with
      | letS =>
          have hfreeE : InsFree ins (.expr e) := hfree.mono (fun z hz => by
            simp only [ofPCode, codeMentions, stmtMentions, optExprMentions,
              Bool.or_eq_false_iff] at hz
            simpa only [codeMentions] using hz.2)
          obtain ⟨res₁, hstepe, hrese⟩ := ihe hR DcRel.exprE hins hfreeE hb
          rw [show DcResB bound ins V₁.length _ (.expr e) res₁ _ =
            (res₁ = _) from rfl] at hrese
          subst hrese
          refine ⟨_, Step.letVal hstepe hlen, vars.zip vals ++ V₁, rfl,
            hins.prepend _, fun _ => ?_⟩
          intro y hy
          rw [List.map_append, List.map_fst_zip (by omega)]
          rcases List.mem_append.mp hy with hy | hy
          · exact List.mem_append.mpr (Or.inl hy)
          · exact List.mem_append.mpr (Or.inr (hb y hy))
  | @letHalt funs V st vars e st1 he ihe =>
      intro funs₁ V₁ ins bound bound' pc hR hrel hins hfree hb
      cases hrel with
      | letS =>
          have hfreeE : InsFree ins (.expr e) := hfree.mono (fun z hz => by
            simp only [ofPCode, codeMentions, stmtMentions, optExprMentions,
              Bool.or_eq_false_iff] at hz
            simpa only [codeMentions] using hz.2)
          obtain ⟨res₁, hstepe, hrese⟩ := ihe hR DcRel.exprE hins hfreeE hb
          rw [show DcResB bound ins V₁.length _ (.expr e) res₁ _ =
            (res₁ = _) from rfl] at hrese
          subst hrese
          exact ⟨_, Step.letHalt hstepe, V₁, rfl, hins, fun h => nomatch h⟩
  | @assignVal funs V st vars e vals st1 he hlen ihe =>
      intro funs₁ V₁ ins bound bound' pc hR hrel hins hfree hb
      cases hrel with
      | assignS =>
          have hfreeE : InsFree ins (.expr e) := hfree.mono (fun z hz => by
            simp only [ofPCode, codeMentions, stmtMentions,
              Bool.or_eq_false_iff] at hz
            simpa only [codeMentions] using hz.2)
          have hdisj : ∀ p ∈ ins, p.2 ∉ vars := fun p hp => by
            have := hfree p hp
            simp only [ofPCode, codeMentions, stmtMentions,
              Bool.or_eq_false_iff, decide_eq_false_iff_not] at this
            exact this.1
          obtain ⟨res₁, hstepe, hrese⟩ := ihe hR DcRel.exprE hins hfreeE hb
          rw [show DcResB bound ins V₁.length _ (.expr e) res₁ _ =
            (res₁ = _) from rfl] at hrese
          subst hrese
          refine ⟨_, Step.assignVal hstepe hlen, VEnv.setMany V₁ vars vals,
            rfl, MIns.setMany vals hins hdisj, fun _ => ?_⟩
          intro y hy
          rw [VEnv.setMany_keys]
          exact hb y hy
  | @assignHalt funs V st vars e st1 he ihe =>
      intro funs₁ V₁ ins bound bound' pc hR hrel hins hfree hb
      cases hrel with
      | assignS =>
          have hfreeE : InsFree ins (.expr e) := hfree.mono (fun z hz => by
            simp only [ofPCode, codeMentions, stmtMentions,
              Bool.or_eq_false_iff] at hz
            simpa only [codeMentions] using hz.2)
          obtain ⟨res₁, hstepe, hrese⟩ := ihe hR DcRel.exprE hins hfreeE hb
          rw [show DcResB bound ins V₁.length _ (.expr e) res₁ _ =
            (res₁ = _) from rfl] at hrese
          subst hrese
          exact ⟨_, Step.assignHalt hstepe, V₁, rfl, hins, fun h => nomatch h⟩
  | @exprStmt funs V st e st1 he ihe =>
      intro funs₁ V₁ ins bound bound' pc hR hrel hins hfree hb
      cases hrel with
      | exprStmtS =>
          have hfreeE : InsFree ins (.expr e) := hfree.mono (fun z hz => by
            simpa only [ofPCode, codeMentions, stmtMentions] using hz)
          obtain ⟨res₁, hstepe, hrese⟩ := ihe hR DcRel.exprE hins hfreeE hb
          rw [show DcResB bound ins V₁.length _ (.expr e) res₁ _ =
            (res₁ = _) from rfl] at hrese
          subst hrese
          exact ⟨_, Step.exprStmt hstepe, V₁, rfl, hins, fun _ => hb⟩
  | @exprStmtHalt funs V st e st1 he ihe =>
      intro funs₁ V₁ ins bound bound' pc hR hrel hins hfree hb
      cases hrel with
      | exprStmtS =>
          have hfreeE : InsFree ins (.expr e) := hfree.mono (fun z hz => by
            simpa only [ofPCode, codeMentions, stmtMentions] using hz)
          obtain ⟨res₁, hstepe, hrese⟩ := ihe hR DcRel.exprE hins hfreeE hb
          rw [show DcResB bound ins V₁.length _ (.expr e) res₁ _ =
            (res₁ = _) from rfl] at hrese
          subst hrese
          exact ⟨_, Step.exprStmtHalt hstepe, V₁, rfl, hins, fun h => nomatch h⟩
  | @ifTrue funs V st c body' cv st1 V' st2 o hc hcv hbstep ihc ihb =>
      intro funs₁ V₁ ins bound bound' pc hR hrel hins hfree hb
      cases hrel with
      | @condS _ bx _ body _ hbodyRel =>
          have hfreeC : InsFree ins (.expr c) := hfree.mono (fun z hz => by
            simp only [ofPCode, codeMentions, stmtMentions,
              Bool.or_eq_false_iff] at hz
            simpa only [codeMentions] using hz.1)
          have hfreeB : InsFree ins (.stmt (.block body)) :=
            hfree.mono (fun z hz => by
              simp only [ofPCode, codeMentions, stmtMentions,
                Bool.or_eq_false_iff] at hz
              simpa only [codeMentions, stmtMentions] using hz.2)
          obtain ⟨res₁, hstepc, hresc⟩ := ihc hR DcRel.exprE hins hfreeC hb
          rw [show DcResB bound ins V₁.length _ (.expr c) res₁ _ =
            (res₁ = _) from rfl] at hresc
          subst hresc
          obtain ⟨res₂, hstepb, hresb⟩ := ihb hR (DcRel.blockS hbodyRel)
            hins hfreeB hb
          obtain ⟨V₁', rfl, hmins, hbAfter⟩ := hresb
          exact ⟨_, Step.ifTrue hstepc hcv hstepb, V₁', rfl, hmins, hbAfter⟩
  | @ifFalse funs V st c body' cv st1 hc hcv ihc =>
      intro funs₁ V₁ ins bound bound' pc hR hrel hins hfree hb
      cases hrel with
      | condS hbodyRel =>
          have hfreeC : InsFree ins (.expr c) := hfree.mono (fun z hz => by
            simp only [ofPCode, codeMentions, stmtMentions,
              Bool.or_eq_false_iff] at hz
            simpa only [codeMentions] using hz.1)
          obtain ⟨res₁, hstepc, hresc⟩ := ihc hR DcRel.exprE hins hfreeC hb
          rw [show DcResB bound ins V₁.length _ (.expr c) res₁ _ =
            (res₁ = _) from rfl] at hresc
          subst hresc
          exact ⟨_, Step.ifFalse hstepc hcv, V₁, rfl, hins, fun _ => hb⟩
  | @ifHalt funs V st c body' st1 hc ihc =>
      intro funs₁ V₁ ins bound bound' pc hR hrel hins hfree hb
      cases hrel with
      | condS hbodyRel =>
          have hfreeC : InsFree ins (.expr c) := hfree.mono (fun z hz => by
            simp only [ofPCode, codeMentions, stmtMentions,
              Bool.or_eq_false_iff] at hz
            simpa only [codeMentions] using hz.1)
          obtain ⟨res₁, hstepc, hresc⟩ := ihc hR DcRel.exprE hins hfreeC hb
          rw [show DcResB bound ins V₁.length _ (.expr c) res₁ _ =
            (res₁ = _) from rfl] at hresc
          subst hresc
          exact ⟨_, Step.ifHalt hstepc, V₁, rfl, hins, fun h => nomatch h⟩
  | @switchExec funs V st c cases' dflt' cv st1 V' st2 o hc hsel ihc ihsel =>
      intro funs₁ V₁ ins bound bound' pc hR hrel hins hfree hb
      cases hrel with
      | @switchS _ _ cases _ dflt _ hcs hd =>
          have hfreeC : InsFree ins (.expr c) := hfree.mono (fun z hz => by
            simp only [ofPCode, codeMentions, stmtMentions,
              Bool.or_eq_false_iff] at hz
            simpa only [codeMentions] using hz.1.1)
          obtain ⟨res₁, hstepc, hresc⟩ := ihc hR DcRel.exprE hins hfreeC hb
          rw [show DcResB bound ins V₁.length _ (.expr c) res₁ _ =
            (res₁ = _) from rfl] at hresc
          subst hresc
          obtain ⟨bsel, hselRel⟩ := DcRel.selectRel hcs hd cv
          have hfreeSel : InsFree ins
              (.stmt (.block (selectSwitch D cv cases dflt))) :=
            hfree.mono (fun z hz => by
              simp only [ofPCode, codeMentions, stmtMentions,
                Bool.or_eq_false_iff] at hz
              simp only [codeMentions, stmtMentions]
              exact selectSwitch_not_mentions hz.1.2 hz.2)
          obtain ⟨res₂, hstepsel, hressel⟩ := ihsel hR (DcRel.blockS hselRel)
            hins hfreeSel hb
          obtain ⟨V₁', rfl, hmins, hbAfter⟩ := hressel
          exact ⟨_, Step.switchExec hstepc hstepsel, V₁', rfl, hmins, hbAfter⟩
  | @switchHalt funs V st c cases' dflt' st1 hc ihc =>
      intro funs₁ V₁ ins bound bound' pc hR hrel hins hfree hb
      cases hrel with
      | switchS hcs hd =>
          have hfreeC : InsFree ins (.expr c) := hfree.mono (fun z hz => by
            simp only [ofPCode, codeMentions, stmtMentions,
              Bool.or_eq_false_iff] at hz
            simpa only [codeMentions] using hz.1.1)
          obtain ⟨res₁, hstepc, hresc⟩ := ihc hR DcRel.exprE hins hfreeC hb
          rw [show DcResB bound ins V₁.length _ (.expr c) res₁ _ =
            (res₁ = _) from rfl] at hresc
          subst hresc
          exact ⟨_, Step.switchHalt hstepc, V₁, rfl, hins, fun h => nomatch h⟩
  | @forLoop funs V st init c post' body' Vinit₂ stinit Vend₂ stend o
      hinitstep hloop ihinit ihloop =>
      intro funs₁ V₁ ins bound bound' pc hR hrel hins hfree hb
      cases hrel with
      | @forS _ bp bb _ _ post _ body _ hpostRel hbodyRel =>
          obtain ⟨bi, hinitRel⟩ := DcRel.reflStmts bound init
          have hfreeI : InsFree ins (.stmts init) := hfree.mono (fun z hz => by
            simp only [ofPCode, codeMentions, stmtMentions,
              Bool.or_eq_false_iff] at hz
            simpa only [codeMentions] using hz.1.1.1)
          have hfreeL : InsFree ins (.loop c post body) :=
            hfree.mono (fun z hz => by
              simp only [ofPCode, codeMentions, stmtMentions,
                Bool.or_eq_false_iff] at hz
              simp only [codeMentions, Bool.or_eq_false_iff]
              exact ⟨⟨hz.1.1.2, hz.1.2⟩, hz.2⟩)
          obtain ⟨res₁, hstepi, hresi⟩ := ihinit
            (List.Forall₂.cons (DcScopeRel.refl _) hR) hinitRel hins hfreeI hb
          obtain ⟨Vinit₁, insN, rfl, hminsI, hdepthI, hreflI, -⟩ := hresi
          obtain rfl := hreflI rfl
          rw [List.nil_append] at hminsI
          obtain ⟨res₂, hstepl, hresl⟩ := ihloop
            (List.Forall₂.cons (DcScopeRel.refl _) hR)
            (DcRel.loopL hpostRel hbodyRel) hminsI hfreeL
            (BoundOK.mono hb hinitstep)
          obtain ⟨Vend₁, rfl, hminsE⟩ := hresl
          refine ⟨_, Step.forLoop hstepi hstepl, restore V₁ Vend₁, rfl,
            MIns.restore hins (by simpa using hminsE)
              (fun p hp => absurd hp (List.not_mem_nil)), fun _ => ?_⟩
          intro y hy
          rw [restore_keys ((venvKeys_suffix hinitstep rfl).trans
                (venvKeys_suffix hloop rfl))
              (Nat.le_trans (venvLen_mono hinitstep rfl)
                (venvLen_mono hloop rfl))]
          exact hb y hy
  | @forInitHalt funs V st init c post' body' Vinit₂ stinit hinitstep ihinit =>
      intro funs₁ V₁ ins bound bound' pc hR hrel hins hfree hb
      cases hrel with
      | forS hpostRel hbodyRel =>
          obtain ⟨bi, hinitRel⟩ := DcRel.reflStmts bound init
          have hfreeI : InsFree ins (.stmts init) := hfree.mono (fun z hz => by
            simp only [ofPCode, codeMentions, stmtMentions,
              Bool.or_eq_false_iff] at hz
            simpa only [codeMentions] using hz.1.1.1)
          obtain ⟨res₁, hstepi, hresi⟩ := ihinit
            (List.Forall₂.cons (DcScopeRel.refl _) hR) hinitRel hins hfreeI hb
          obtain ⟨Vinit₁, insN, rfl, hminsI, hdepthI, hreflI, -⟩ := hresi
          obtain rfl := hreflI rfl
          rw [List.nil_append] at hminsI
          exact ⟨_, Step.forInitHalt hstepi, restore V₁ Vinit₁, rfl,
            MIns.restore hins (by simpa using hminsI)
              (fun p hp => absurd hp (List.not_mem_nil)),
            fun h => nomatch h⟩
  | @«break» funs V st =>
      intro funs₁ V₁ ins bound bound' pc hR hrel hins hfree hb
      cases hrel with
      | breakS => exact ⟨_, Step.break, V₁, rfl, hins, fun h => nomatch h⟩
  | @«continue» funs V st =>
      intro funs₁ V₁ ins bound bound' pc hR hrel hins hfree hb
      cases hrel with
      | continueS =>
          exact ⟨_, Step.continue, V₁, rfl, hins, fun h => nomatch h⟩
  | @leave funs V st =>
      intro funs₁ V₁ ins bound bound' pc hR hrel hins hfree hb
      cases hrel with
      | leaveS => exact ⟨_, Step.leave, V₁, rfl, hins, fun h => nomatch h⟩
  | @seqNil funs V st =>
      intro funs₁ V₁ ins bound bound' pc hR hrel hins hfree hb
      obtain ⟨ss, rfl⟩ := hrel.src_stmts
      rcases hrel.stmts_factor rfl rfl with ⟨-, rfl, hld⟩ |
        ⟨s, rest, s'', rest'', b1, heq, -, -, -⟩
      · obtain ⟨V₁', insN, hins', hd, hmen, hrefl, hchain⟩ :=
          leadDrops_run hld st hins hb
        refine ⟨_, hchain Step.seqNil, V₁', insN, rfl, hins', hd, ?_,
          fun _ => hb⟩
        intro heq
        injection heq with heq
        exact (hrefl heq.symm).1
      · cases heq
  | @seqCons funs V st s' rest' Vm1 stm1 Vm2 stm2 o hs' hrest' ihs ihrest =>
      intro funs₁ V₁ ins bound bound' pc hR hrel hins hfree hb
      obtain ⟨ss, rfl⟩ := hrel.src_stmts
      rcases hrel.stmts_factor rfl rfl with ⟨heq, -, -⟩ |
        ⟨s, rest, s'', rest'', b1, heq, hld, hheadRel, htailRel⟩
      · cases heq
      · injection heq with heq1 heq2
        subst heq1; subst heq2
        obtain ⟨V₁', insN₀, hins', hd₀, hmen₀, hrefl₀, hchain⟩ :=
          leadDrops_run hld st hins hb
        have hfreeMid : InsFree (insN₀ ++ ins) (.stmts (s :: rest)) := by
          intro p hp
          rcases List.mem_append.mp hp with hp | hp
          · simpa only [codeMentions] using hmen₀ p hp
          · have := hfree p hp
            simp only [ofPCode, codeMentions] at this ⊢
            exact hld.mentions_le p.2 this
        have hfreeS : InsFree (insN₀ ++ ins) (.stmt s) :=
          hfreeMid.mono (fun z hz => by
            simp only [codeMentions, stmtsMentions, Bool.or_eq_false_iff] at hz
            simpa only [codeMentions] using hz.1)
        have hfreeRest : InsFree (insN₀ ++ ins) (.stmts rest) :=
          hfreeMid.mono (fun z hz => by
            simp only [codeMentions, stmtsMentions, Bool.or_eq_false_iff] at hz
            simpa only [codeMentions] using hz.2)
        obtain ⟨res₁, hstep1, hres1⟩ := ihs hR hheadRel hins' hfreeS hb
        obtain ⟨V₁h, rfl, hmins1, hbAfter1⟩ := hres1
        obtain ⟨res₂, hstep2, hres2⟩ := ihrest hR htailRel hmins1 hfreeRest
          (hbAfter1 rfl)
        obtain ⟨V₁t, insN₁, rfl, hmins2, hdepth2, hrefl2, hbAfter2⟩ := hres2
        refine ⟨_, hchain (Step.seqCons hstep1 hstep2), V₁t,
          insN₁ ++ insN₀, rfl, ?_, ?_, ?_, hbAfter2⟩
        · rw [List.append_assoc]
          exact hmins2
        · intro p hp
          rcases List.mem_append.mp hp with hp | hp
          · have h1 := hdepth2 p hp
            have h2 := venvLen_mono hstep1 rfl
            have h3 := hins'.length
            have h4 := hins.length
            simp only [List.length_append] at h3
            omega
          · exact hd₀ p hp
        · intro heqR
          injection heqR with heqR
          have hlss : (s :: rest).length = ss.length := by
            have l1 := hld.length_le
            have l2 := DcRel.stmts_len htailRel rfl rfl
            have l3 : ss.length = rest'.length + 1 := by rw [heqR]; simp
            simp only [List.length_cons] at l1 ⊢
            omega
          have hmid := hld.eq_of_length hlss
          have hss : s :: rest = s' :: rest' := by rw [hmid, heqR]
          injection hss with hs1 hs2
          subst hs1; subst hs2
          rw [(hrefl₀ hmid).1, hrefl2 rfl]
          rfl
  | @seqStop funs V st s' rest' Vm1 stm1 o hs' hne ihs =>
      intro funs₁ V₁ ins bound bound' pc hR hrel hins hfree hb
      obtain ⟨ss, rfl⟩ := hrel.src_stmts
      rcases hrel.stmts_factor rfl rfl with ⟨heq, -, -⟩ |
        ⟨s, rest, s'', rest'', b1, heq, hld, hheadRel, htailRel⟩
      · cases heq
      · injection heq with heq1 heq2
        subst heq1; subst heq2
        obtain ⟨V₁', insN₀, hins', hd₀, hmen₀, hrefl₀, hchain⟩ :=
          leadDrops_run hld st hins hb
        have hfreeMid : InsFree (insN₀ ++ ins) (.stmts (s :: rest)) := by
          intro p hp
          rcases List.mem_append.mp hp with hp | hp
          · simpa only [codeMentions] using hmen₀ p hp
          · have := hfree p hp
            simp only [ofPCode, codeMentions] at this ⊢
            exact hld.mentions_le p.2 this
        have hfreeS : InsFree (insN₀ ++ ins) (.stmt s) :=
          hfreeMid.mono (fun z hz => by
            simp only [codeMentions, stmtsMentions, Bool.or_eq_false_iff] at hz
            simpa only [codeMentions] using hz.1)
        obtain ⟨res₁, hstep1, hres1⟩ := ihs hR hheadRel hins' hfreeS hb
        obtain ⟨V₁h, rfl, hmins1, -⟩ := hres1
        refine ⟨_, hchain (Step.seqStop hstep1 hne), V₁h, insN₀, rfl,
          hmins1, hd₀, ?_, fun ho => absurd ho hne⟩
        intro heqR
        injection heqR with heqR
        have hlss : (s :: rest).length = ss.length := by
          have l1 := hld.length_le
          have l2 := DcRel.stmts_len htailRel rfl rfl
          have l3 : ss.length = rest'.length + 1 := by rw [heqR]; simp
          simp only [List.length_cons] at l1 ⊢
          omega
        exact (hrefl₀ (hld.eq_of_length hlss)).1
  | @loopDone funs V st c post' body' cv st1 hc hz ihc =>
      intro funs₁ V₁ ins bound bound' pc hR hrel hins hfree hb
      cases hrel with
      | loopL hpostRel hbodyRel =>
          have hfreeC : InsFree ins (.expr c) := hfree.mono (fun z hz => by
            simp only [ofPCode, codeMentions, Bool.or_eq_false_iff] at hz
            simpa only [codeMentions] using hz.1.1)
          obtain ⟨res₁, hstepc, hresc⟩ := ihc hR DcRel.exprE hins hfreeC hb
          rw [show DcResB bound ins V₁.length _ (.expr c) res₁ _ =
            (res₁ = _) from rfl] at hresc
          subst hresc
          exact ⟨_, Step.loopDone hstepc hz, V₁, rfl, hins⟩
  | @loopCondHalt funs V st c post' body' st1 hc ihc =>
      intro funs₁ V₁ ins bound bound' pc hR hrel hins hfree hb
      cases hrel with
      | loopL hpostRel hbodyRel =>
          have hfreeC : InsFree ins (.expr c) := hfree.mono (fun z hz => by
            simp only [ofPCode, codeMentions, Bool.or_eq_false_iff] at hz
            simpa only [codeMentions] using hz.1.1)
          obtain ⟨res₁, hstepc, hresc⟩ := ihc hR DcRel.exprE hins hfreeC hb
          rw [show DcResB bound ins V₁.length _ (.expr c) res₁ _ =
            (res₁ = _) from rfl] at hresc
          subst hresc
          exact ⟨_, Step.loopCondHalt hstepc, V₁, rfl, hins⟩
  | @loopStep funs V st c post' body' cv st1 Vb₂ stb ob Vp₂ stp Vend₂ stend o
      hc hnz hbstep hob hpost hrec ihc ihb ihp ihrec =>
      intro funs₁ V₁ ins bound bound' pc hR hrel hins hfree hb
      cases hrel with
      | @loopL _ bp bb _ post _ body _ hpostRel hbodyRel =>
          have hfreeC : InsFree ins (.expr c) := hfree.mono (fun z hz => by
            simp only [ofPCode, codeMentions, Bool.or_eq_false_iff] at hz
            simpa only [codeMentions] using hz.1.1)
          have hfreeB : InsFree ins (.stmt (.block body)) :=
            hfree.mono (fun z hz => by
              simp only [ofPCode, codeMentions, Bool.or_eq_false_iff] at hz
              simpa only [codeMentions, stmtMentions] using hz.2)
          have hfreeP : InsFree ins (.stmt (.block post)) :=
            hfree.mono (fun z hz => by
              simp only [ofPCode, codeMentions, Bool.or_eq_false_iff] at hz
              simpa only [codeMentions, stmtMentions] using hz.1.2)
          obtain ⟨res₁, hstepc, hresc⟩ := ihc hR DcRel.exprE hins hfreeC hb
          rw [show DcResB bound ins V₁.length _ (.expr c) res₁ _ =
            (res₁ = _) from rfl] at hresc
          subst hresc
          obtain ⟨res₂, hstepb, hresb⟩ := ihb hR (DcRel.blockS hbodyRel)
            hins hfreeB hb
          obtain ⟨Vb₁, rfl, hminsB, -⟩ := hresb
          have hbB : BoundOK Vb₂ bound := BoundOK.mono hb hbstep
          obtain ⟨res₃, hstepp, hresp⟩ := ihp hR (DcRel.blockS hpostRel)
            hminsB hfreeP hbB
          obtain ⟨Vp₁, rfl, hminsP, -⟩ := hresp
          have hbP : BoundOK Vp₂ bound := BoundOK.mono hbB hpost
          obtain ⟨res₄, hstepr, hresr⟩ := ihrec hR
            (DcRel.loopL hpostRel hbodyRel) hminsP hfree hbP
          obtain ⟨Vend₁, rfl, hminsE⟩ := hresr
          exact ⟨_, Step.loopStep hstepc hnz hstepb hob hstepp hstepr,
            Vend₁, rfl, hminsE⟩
  | @loopPostHalt funs V st c post' body' cv st1 Vb₂ stb ob Vp₂ stp
      hc hnz hbstep hob hpost ihc ihb ihp =>
      intro funs₁ V₁ ins bound bound' pc hR hrel hins hfree hb
      cases hrel with
      | @loopL _ bp bb _ post _ body _ hpostRel hbodyRel =>
          have hfreeC : InsFree ins (.expr c) := hfree.mono (fun z hz => by
            simp only [ofPCode, codeMentions, Bool.or_eq_false_iff] at hz
            simpa only [codeMentions] using hz.1.1)
          have hfreeB : InsFree ins (.stmt (.block body)) :=
            hfree.mono (fun z hz => by
              simp only [ofPCode, codeMentions, Bool.or_eq_false_iff] at hz
              simpa only [codeMentions, stmtMentions] using hz.2)
          have hfreeP : InsFree ins (.stmt (.block post)) :=
            hfree.mono (fun z hz => by
              simp only [ofPCode, codeMentions, Bool.or_eq_false_iff] at hz
              simpa only [codeMentions, stmtMentions] using hz.1.2)
          obtain ⟨res₁, hstepc, hresc⟩ := ihc hR DcRel.exprE hins hfreeC hb
          rw [show DcResB bound ins V₁.length _ (.expr c) res₁ _ =
            (res₁ = _) from rfl] at hresc
          subst hresc
          obtain ⟨res₂, hstepb, hresb⟩ := ihb hR (DcRel.blockS hbodyRel)
            hins hfreeB hb
          obtain ⟨Vb₁, rfl, hminsB, -⟩ := hresb
          have hbB : BoundOK Vb₂ bound := BoundOK.mono hb hbstep
          obtain ⟨res₃, hstepp, hresp⟩ := ihp hR (DcRel.blockS hpostRel)
            hminsB hfreeP hbB
          obtain ⟨Vp₁, rfl, hminsP, -⟩ := hresp
          exact ⟨_, Step.loopPostHalt hstepc hnz hstepb hob hstepp,
            Vp₁, rfl, hminsP⟩
  | @loopBreak funs V st c post' body' cv st1 Vb₂ stb hc hnz hbstep ihc ihb =>
      intro funs₁ V₁ ins bound bound' pc hR hrel hins hfree hb
      cases hrel with
      | @loopL _ bp bb _ post _ body _ hpostRel hbodyRel =>
          have hfreeC : InsFree ins (.expr c) := hfree.mono (fun z hz => by
            simp only [ofPCode, codeMentions, Bool.or_eq_false_iff] at hz
            simpa only [codeMentions] using hz.1.1)
          have hfreeB : InsFree ins (.stmt (.block body)) :=
            hfree.mono (fun z hz => by
              simp only [ofPCode, codeMentions, Bool.or_eq_false_iff] at hz
              simpa only [codeMentions, stmtMentions] using hz.2)
          obtain ⟨res₁, hstepc, hresc⟩ := ihc hR DcRel.exprE hins hfreeC hb
          rw [show DcResB bound ins V₁.length _ (.expr c) res₁ _ =
            (res₁ = _) from rfl] at hresc
          subst hresc
          obtain ⟨res₂, hstepb, hresb⟩ := ihb hR (DcRel.blockS hbodyRel)
            hins hfreeB hb
          obtain ⟨Vb₁, rfl, hminsB, -⟩ := hresb
          exact ⟨_, Step.loopBreak hstepc hnz hstepb, Vb₁, rfl, hminsB⟩
  | @loopLeave funs V st c post' body' cv st1 Vb₂ stb hc hnz hbstep ihc ihb =>
      intro funs₁ V₁ ins bound bound' pc hR hrel hins hfree hb
      cases hrel with
      | @loopL _ bp bb _ post _ body _ hpostRel hbodyRel =>
          have hfreeC : InsFree ins (.expr c) := hfree.mono (fun z hz => by
            simp only [ofPCode, codeMentions, Bool.or_eq_false_iff] at hz
            simpa only [codeMentions] using hz.1.1)
          have hfreeB : InsFree ins (.stmt (.block body)) :=
            hfree.mono (fun z hz => by
              simp only [ofPCode, codeMentions, Bool.or_eq_false_iff] at hz
              simpa only [codeMentions, stmtMentions] using hz.2)
          obtain ⟨res₁, hstepc, hresc⟩ := ihc hR DcRel.exprE hins hfreeC hb
          rw [show DcResB bound ins V₁.length _ (.expr c) res₁ _ =
            (res₁ = _) from rfl] at hresc
          subst hresc
          obtain ⟨res₂, hstepb, hresb⟩ := ihb hR (DcRel.blockS hbodyRel)
            hins hfreeB hb
          obtain ⟨Vb₁, rfl, hminsB, -⟩ := hresb
          exact ⟨_, Step.loopLeave hstepc hnz hstepb, Vb₁, rfl, hminsB⟩
  | @loopBodyHalt funs V st c post' body' cv st1 Vb₂ stb hc hnz hbstep
      ihc ihb =>
      intro funs₁ V₁ ins bound bound' pc hR hrel hins hfree hb
      cases hrel with
      | @loopL _ bp bb _ post _ body _ hpostRel hbodyRel =>
          have hfreeC : InsFree ins (.expr c) := hfree.mono (fun z hz => by
            simp only [ofPCode, codeMentions, Bool.or_eq_false_iff] at hz
            simpa only [codeMentions] using hz.1.1)
          have hfreeB : InsFree ins (.stmt (.block body)) :=
            hfree.mono (fun z hz => by
              simp only [ofPCode, codeMentions, Bool.or_eq_false_iff] at hz
              simpa only [codeMentions, stmtMentions] using hz.2)
          obtain ⟨res₁, hstepc, hresc⟩ := ihc hR DcRel.exprE hins hfreeC hb
          rw [show DcResB bound ins V₁.length _ (.expr c) res₁ _ =
            (res₁ = _) from rfl] at hresc
          subst hresc
          obtain ⟨res₂, hstepb, hresb⟩ := ihb hR (DcRel.blockS hbodyRel)
            hins hfreeB hb
          obtain ⟨Vb₁, rfl, hminsB, -⟩ := hresb
          exact ⟨_, Step.loopBodyHalt hstepc hnz hstepb, Vb₁, rfl, hminsB⟩

/-! ### The pass -/

/-- Related blocks are semantically equivalent: the two simulations,
packaged through the hoisted-scope extension of `DcFunsRel`. The top-level
`restore` erases every insertion (all depths lie at or above the entry
environment), so both sides finish in the *same* environment. -/
theorem DcRel.equivBlock {b2 : List Ident} {b b' : Block Op}
    (hrel : DcRel [] b2 (.stmts b) (.stmts b')) :
    EquivBlock D b b' := by
  intro funs V st V' st' o
  constructor
  · intro h
    cases h with
    | block hb =>
        obtain ⟨res₂, hstep, hres⟩ := dc_fwd hb
          (List.Forall₂.cons (hrel.hoist_scopeRel rfl rfl)
            (DcFunsRel.refl funs))
          hrel (MIns.nil V) (InsFree.nil _) (BoundOK.nil V)
        obtain ⟨Vb₂, insN, rfl, hmins, hdepth, -, -⟩ := hres
        rw [(MIns.restore (MIns.nil V) hmins hdepth).nil_eq]
        exact Step.block hstep
  · intro h
    cases h with
    | block hb =>
        obtain ⟨res₁, hstep, hres⟩ := dc_bwd hb
          (List.Forall₂.cons (hrel.hoist_scopeRel rfl rfl)
            (DcFunsRel.refl funs))
          hrel (MIns.nil V) (InsFree.nil _) (BoundOK.nil V)
        obtain ⟨Vb₁, insN, rfl, hmins, hdepth, -, -⟩ := hres
        rw [← (MIns.restore (MIns.nil V) hmins hdepth).nil_eq]
        exact Step.block hstep

/-- The **DeadPure pass**: dead pure-binding and self-assignment
elimination, bundled with its soundness proof — in the unchanged pointwise
spec (bidirectional `Step` simulation with the `BoundOK` invariant and the
`MIns` multi-insertion frame). -/
def deadPure : Pass D where
  run := dpStmts []
  sound := fun b => by
    obtain ⟨b2, hrel⟩ := dpStmts_rel [] b
    exact hrel.equivBlock

@[simp] theorem deadPure_run (b : Block Op) :
    (deadPure (calls := calls) (creates := creates)).run b = dpStmts [] b := rfl


/-! ### Regression examples (checked at build time) -/

-- A dead param-shaped copy dies when its source is provably bound.
example : dpStmts ["p"] [.letDecl ["y"] (some (.var "p")),
    .exprStmt (.builtin .sstore [.lit (.number 0), .lit (.number 1)])]
  = [.exprStmt (.builtin .sstore [.lit (.number 0), .lit (.number 1)])] := rfl
-- ...but stays when the source is not provably bound.
example : dpStmts [] [.letDecl ["y"] (some (.var "p")),
    .exprStmt (.builtin .sstore [.lit (.number 0), .lit (.number 1)])]
  = [.letDecl ["y"] (some (.var "p")),
     .exprStmt (.builtin .sstore [.lit (.number 0), .lit (.number 1)])] := rfl
-- Earlier let-declarations feed the bound set.
example : dpStmts [] [.letDecl ["a"] (some (.lit (.number 1))),
    .letDecl ["y"] (some (.builtin .add [.var "a", .lit (.number 2)])),
    .exprStmt (.builtin .sstore [.lit (.number 0), .var "a"])]
  = [.letDecl ["a"] (some (.lit (.number 1))),
     .exprStmt (.builtin .sstore [.lit (.number 0), .var "a"])] := rfl
-- Self-assignments of bound variables are no-ops and die.
example : dpStmts ["x"] [.assign ["x"] (.var "x"),
    .exprStmt (.builtin .sstore [.lit (.number 0), .var "x"])]
  = [.exprStmt (.builtin .sstore [.lit (.number 0), .var "x"])] := rfl
-- Calls never qualify (they can halt or diverge in effect).
example : dpStmts ["p"] [.letDecl ["y"] (some (.call "f" [.var "p"])),
    .exprStmt (.builtin .sstore [.lit (.number 0), .lit (.number 1)])]
  = [.letDecl ["y"] (some (.call "f" [.var "p"])),
     .exprStmt (.builtin .sstore [.lit (.number 0), .lit (.number 1)])] := rfl
-- Wrong arity is stuck, not total: `add(x)` stays even when `x` is bound.
example : dpStmts ["x"] [.letDecl ["y"] (some (.builtin .add [.var "x"])),
    .exprStmt (.builtin .sstore [.lit (.number 0), .lit (.number 1)])]
  = [.letDecl ["y"] (some (.builtin .add [.var "x"])),
     .exprStmt (.builtin .sstore [.lit (.number 0), .lit (.number 1)])] := rfl
-- funDef bodies reset the bound set to params ++ rets.
example : dpStmts [] [.funDef "f" ["p"] ["r"]
    [.letDecl ["y"] (some (.var "p")), .assign ["r"] (.lit (.number 1))]]
  = [.funDef "f" ["p"] ["r"] [.assign ["r"] (.lit (.number 1))]] := rfl

end YulEvmCompiler.Optimizer
