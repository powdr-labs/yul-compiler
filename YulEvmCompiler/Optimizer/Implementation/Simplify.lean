import YulEvmCompiler.Optimizer.Spec.Pass
import YulEvmCompiler.Optimizer.Implementation.FunCongr
import YulSemantics.Dialect.EVM

/-!
# YulEvmCompiler.Optimizer.Implementation.Simplify

A local **constant-folding + neutral-element** simplifier for the EVM dialect,
the first real `Optimizer.Pass`.  It rewrites, bottom-up:

* a pure built-in applied to all-literal arguments → the folded literal
  (`add(2,3) → 5`), and
* a pure built-in with a neutral literal operand kept alongside a *variable*
  (`add(x,0) → x`, `mul(x,1) → x`, `and(x, 2²⁵⁶−1) → x`, `shl(0,x) → x`, …).

Everything here is dialect-EVM specific (it computes with `stepOp`/`litValue`),
so it lives under `Optimizer/Implementation/`.  Only its type — a `Pass` — is
trusted by the audited surface; the internal proofs below need no separate audit.

## Why these rewrites are sound

The pure EVM ops (`add … sar`) reduce via `stepOp op vs st = some (.ok [f vs] st)`:
the result value is a total function of the argument *values* and the state is
unchanged.  So folding all-literal applications and neutral-operand rewrites are
pointwise `EquivExpr`s (`YulSemantics.Equiv`), lifted through the built-in and
statement congruences to `EquivBlock`, discharging the `Pass` obligation `Sound`.

Two soundness fences (see `IDEAS.md`):

* neutral rewrites keep the **variable on the right-hand side** — `mul(x,0) ≈ 0`
  is *unsound* (its RHS evaluates on environments where `x` is unbound, where the
  LHS is stuck), so absorbing rewrites are deliberately excluded;
* `exp` is **not** folded — its value uses an unbounded `Nat` power, which would
  make the pass diverge on large exponents (soundness is unaffected; feasibility
  is not).
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM

variable {calls : ExternalCalls} {creates : ExternalCreates}

/-- The open-world EVM dialect this pass is a `Pass` over — the dialect the
verified backend theorem (`Pass.optimize_then_compile_correct`) is stated
against. Its `Builtin` reduces to `stepOp` on every non-external op. -/
local notation "D" => evmWithExternal calls creates

/-! ### The pure operation kernel

`pureFn` mirrors the state-independent arms of `stepOp` (arithmetic, comparison,
bitwise/shift), returning the result *value* as a total function of the argument
values, for the correct arity only. `exp` is intentionally omitted. -/

/-- The value computed by a pure EVM op on concrete argument words, or `none`
for a non-pure op or an arity mismatch. Mirrors `EVM.stepOp`'s pure arms. -/
def pureFn : Op → List U256 → Option U256
  | .add,        [a, b]    => some (a + b)
  | .sub,        [a, b]    => some (a - b)
  | .mul,        [a, b]    => some (a * b)
  | .div,        [a, b]    => some (if b = 0 then 0 else a / b)
  | .sdiv,       [a, b]    => some (if b = 0 then 0 else BitVec.sdiv a b)
  | .mod,        [a, b]    => some (if b = 0 then 0 else a % b)
  | .smod,       [a, b]    => some (if b = 0 then 0 else BitVec.srem a b)
  | .addmod,     [a, b, n] => some (if n = 0 then 0 else BitVec.ofNat 256 ((a.toNat + b.toNat) % n.toNat))
  | .mulmod,     [a, b, n] => some (if n = 0 then 0 else BitVec.ofNat 256 ((a.toNat * b.toNat) % n.toNat))
  | .signextend, [a, b]    => some (signExtend a b)
  | .clz,        [a]       => some (clzVal a)
  | .lt,         [a, b]    => some (b2w (a.ult b))
  | .gt,         [a, b]    => some (b2w (b.ult a))
  | .slt,        [a, b]    => some (b2w (a.slt b))
  | .sgt,        [a, b]    => some (b2w (b.slt a))
  | .eq,         [a, b]    => some (b2w (a = b))
  | .iszero,     [a]       => some (b2w (a = 0))
  | .and,        [a, b]    => some (a &&& b)
  | .or,         [a, b]    => some (a ||| b)
  | .xor,        [a, b]    => some (a ^^^ b)
  | .not,        [a]       => some (~~~a)
  | .byte,       [a, b]    => some (if 32 ≤ a.toNat then 0 else (b >>> (248 - 8 * a.toNat)) &&& 0xff)
  | .shl,        [a, b]    => some (b <<< a.toNat)
  | .shr,        [a, b]    => some (b >>> a.toNat)
  | .sar,        [a, b]    => some (BitVec.sshiftRight b a.toNat)
  | _,           _         => none

/-- `pureFn` agrees with `stepOp` at every state: a pure op returns its value
with the state unchanged. -/
theorem pureFn_stepOp {op : Op} {vs : List U256} {w : U256}
    (h : pureFn op vs = some w) (st : EvmState) :
    stepOp op vs st = some (.ok [w] st) := by
  unfold pureFn at h
  split at h <;> simp_all [stepOp, bin, un, ter]

/-- A pure op is a **local** built-in, so its open-world `Builtin` (which handles
only the external `call`/`create`/`gas` family specially) is exactly `stepOp`. -/
theorem pureFn_builtin {op : Op} {vs : List U256} {w : U256}
    (h : pureFn op vs = some w) (st : EvmState) :
    (evmWithExternal calls creates).Builtin op vs st (.ok [w] st) := by
  have hs := pureFn_stepOp h st
  cases op <;> simp_all [builtinWithExternal, pureFn]

/-- Inversion: any `Builtin` result of a pure op on `vs` is its folded value with
the state unchanged. -/
theorem pureFn_builtin_inv {op : Op} {vs : List U256} {w : U256} {st : EvmState}
    {r : BuiltinResult U256 EvmState}
    (h : pureFn op vs = some w) (hb : (evmWithExternal calls creates).Builtin op vs st r) :
    r = .ok [w] st := by
  have hs := pureFn_stepOp h st
  cases op <;> simp_all [builtinWithExternal, pureFn]

/-! ### Evaluating an all-literal argument list

A list of literal expressions always evaluates, right-to-left, to its literal
values with the state unchanged — and that is its *only* result (no halting). -/

/-- Constructing the evaluation of a literal argument list. -/
theorem args_lits_eval (funs : FunEnv D) (V : VEnv D) (st : EvmState) (lits : List Literal) :
    Step D funs V st (.args (lits.map Expr.lit)) (.eres (.vals (lits.map litValue) st)) := by
  induction lits with
  | nil => exact Step.argsNil
  | cons l rest ih => exact Step.argsCons ih Step.lit

/-- Inversion of the evaluation of a literal argument list. -/
theorem args_lits_inv {funs : FunEnv D} {V : VEnv D} {st : EvmState} {lits : List Literal}
    {r : EResult D} (h : Step D funs V st (.args (lits.map Expr.lit)) (.eres r)) :
    r = .vals (lits.map litValue) st := by
  induction lits generalizing r with
  | nil => cases h with | argsNil => rfl
  | cons l rest ih =>
      cases h with
      | argsCons ha he =>
          have hrest := ih ha; injection hrest with hv hs; subst hv; subst hs
          cases he with | lit => rfl
      | argsRestHalt ha => have := ih ha; simp at this
      | argsHeadHalt ha he => cases he

/-! ### Constant folding -/

/-- Fold a pure built-in applied to literals into a single literal. -/
def pureFold (op : Op) (lits : List Literal) : Option Literal :=
  (pureFn op (lits.map litValue)).map (fun w => .number w.toNat)

/-- A number literal denotes exactly the word it was built from. -/
theorem litValue_number_toNat (w : U256) : litValue (.number w.toNat) = w := by
  rw [litValue]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt w.isLt

/-- Evaluate a number literal to a chosen word (its denotation). -/
theorem lit_val_eval {funs : FunEnv D} {V : VEnv D} {st : EvmState} {n : Nat} {v : U256}
    (h : litValue (.number n) = v) :
    Step D funs V st (.expr (.lit (.number n))) (.eres (.vals [v] st)) := by
  have hlit : Step D funs V st (.expr (.lit (.number n)))
      (.eres (.vals [litValue (.number n)] st)) := Step.lit
  rw [h] at hlit; exact hlit

/-- **Constant folding is sound**: a pure built-in applied to all-literal
arguments is semantically equivalent to its folded literal. -/
theorem fold_equiv {op : Op} {lits : List Literal} {l : Literal}
    (h : pureFold op lits = some l) :
    EquivExpr D (.builtin op (lits.map Expr.lit)) (.lit l) := by
  rw [pureFold, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, rfl⟩ := h
  have hlv : (evmWithExternal calls creates).litValue (Literal.number w.toNat) = w :=
    litValue_number_toNat w
  intro funs V st r
  constructor
  · intro hb
    cases hb with
    | builtinOk ha hbb =>
        have hargs := args_lits_inv ha; injection hargs with hv hs; subst hv; subst hs
        have hr := pureFn_builtin_inv hw hbb; injection hr with hrets hst; subst hrets; subst hst
        exact lit_val_eval (litValue_number_toNat w)
    | builtinHalt ha hbb =>
        have hargs := args_lits_inv ha; injection hargs with hv hs; subst hv; subst hs
        have := pureFn_builtin_inv hw hbb; simp at this
    | builtinArgsHalt ha => have := args_lits_inv ha; simp at this
  · intro hl
    cases hl with
    | lit =>
        refine Step.builtinOk (args_lits_eval funs V st lits) ?_
        rw [hlv]; exact pureFn_builtin hw st

/-! ### Neutral-element identities

A binary pure op with a neutral literal operand alongside a *variable* collapses
to the variable.  The variable is kept on the right-hand side, so both sides
require the same variable to be bound — the only sound form (`mul(x,0) ≈ 0` is
excluded).  Each identity is a one-line `pureFn` fact fed to one of the two
position-specific lemmas below. -/

/-- Inversion of `[var x, lit c]` argument evaluation (it cannot halt). -/
theorem var_lit_inv {funs : FunEnv D} {V : VEnv D} {st : EvmState} {x c r}
    (h : Step D funs V st (.args [.var x, .lit c]) (.eres r)) :
    ∃ v, VEnv.get V x = some v ∧ r = .vals [v, litValue c] st := by
  cases h with
  | argsCons ha he =>
      cases he with
      | var hv =>
          cases ha with
          | argsCons hb hc =>
              cases hc with | lit => cases hb with | argsNil => exact ⟨_, hv, rfl⟩
  | argsRestHalt ha => cases ha with
      | argsRestHalt hb => cases hb
      | argsHeadHalt hb hc => cases hc
  | argsHeadHalt ha he => cases he

/-- Inversion of `[lit c, var x]` argument evaluation (it cannot halt). -/
theorem lit_var_inv {funs : FunEnv D} {V : VEnv D} {st : EvmState} {x c r}
    (h : Step D funs V st (.args [.lit c, .var x]) (.eres r)) :
    ∃ v, VEnv.get V x = some v ∧ r = .vals [litValue c, v] st := by
  cases h with
  | argsCons ha he =>
      cases he with
      | lit =>
          cases ha with
          | argsCons hb hc =>
              cases hc with | var hv => cases hb with | argsNil => exact ⟨_, hv, rfl⟩
  | argsRestHalt ha => cases ha with
      | argsRestHalt hb => cases hb
      | argsHeadHalt hb hc => cases hc
  | argsHeadHalt ha he => cases he

/-- **Right-operand neutral**: `op(x, c) ≈ x` when `op` maps `(v, c)` to `v`. -/
theorem builtin_var_lit_equiv {op : Op} {x : Ident} {c : Literal}
    (h : ∀ v : U256, pureFn op [v, litValue c] = some v) :
    EquivExpr D (.builtin op [.var x, .lit c]) (.var x) := by
  intro funs V st r
  constructor
  · intro hb
    cases hb with
    | builtinOk ha hbb =>
        obtain ⟨v, hv, hr⟩ := var_lit_inv ha; injection hr with e1 e2; subst e1; subst e2
        have := pureFn_builtin_inv (h v) hbb; injection this with hrets hst
        subst hrets; subst hst; exact Step.var hv
    | builtinHalt ha hbb =>
        obtain ⟨v, hv, hr⟩ := var_lit_inv ha; injection hr with e1 e2; subst e1; subst e2
        have := pureFn_builtin_inv (h v) hbb; simp at this
    | builtinArgsHalt ha =>
        obtain ⟨v, hv, hr⟩ := var_lit_inv ha; simp at hr
  · intro hx
    cases hx with
    | var hv =>
        exact Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil Step.lit) (Step.var hv))
          (pureFn_builtin (h _) st)

/-- **Left-operand neutral**: `op(c, x) ≈ x` when `op` maps `(c, v)` to `v`. -/
theorem builtin_lit_var_equiv {op : Op} {x : Ident} {c : Literal}
    (h : ∀ v : U256, pureFn op [litValue c, v] = some v) :
    EquivExpr D (.builtin op [.lit c, .var x]) (.var x) := by
  intro funs V st r
  constructor
  · intro hb
    cases hb with
    | builtinOk ha hbb =>
        obtain ⟨v, hv, hr⟩ := lit_var_inv ha; injection hr with e1 e2; subst e1; subst e2
        have := pureFn_builtin_inv (h v) hbb; injection this with hrets hst
        subst hrets; subst hst; exact Step.var hv
    | builtinHalt ha hbb =>
        obtain ⟨v, hv, hr⟩ := lit_var_inv ha; injection hr with e1 e2; subst e1; subst e2
        have := pureFn_builtin_inv (h v) hbb; simp at this
    | builtinArgsHalt ha =>
        obtain ⟨v, hv, hr⟩ := lit_var_inv ha; simp at hr
  · intro hx
    cases hx with
    | var hv =>
        exact Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil (Step.var hv)) Step.lit)
          (pureFn_builtin (h _) st)

/-! ### Recognizing rewritable built-ins

`asLits` succeeds exactly on an all-literal argument list; `neutral` recognizes a
binary op with one variable operand and a neutral literal.  Both feed the
soundness proof back through the equivalences above. -/

/-- The all-ones word `2²⁵⁶−1`, the neutral element of `and`. -/
def allOnes : U256 := BitVec.allOnes 256

/-- Extract the literals of an all-literal argument list. -/
def asLits : List (Expr Op) → Option (List Literal)
  | [] => some []
  | .lit l :: rest => (asLits rest).map (fun ls => l :: ls)
  | _ :: _ => none

/-- If `asLits` succeeds, the arguments were syntactically those literals. -/
theorem asLits_map {args : List (Expr Op)} {lits : List Literal}
    (h : asLits args = some lits) : args = lits.map Expr.lit := by
  induction args generalizing lits with
  | nil => simp [asLits] at h; subst h; rfl
  | cons a rest ih =>
      cases a with
      | lit l =>
          simp only [asLits, Option.map_eq_some_iff] at h
          obtain ⟨ls, hls, rfl⟩ := h
          rw [ih hls]; rfl
      | var _ => simp [asLits] at h
      | builtin _ _ => simp [asLits] at h
      | call _ _ => simp [asLits] at h

/-- Recognize a neutral-element binary op, returning the surviving variable. -/
def neutral : Op → List (Expr Op) → Option (Expr Op)
  | .add, [.var x, .lit c] => if litValue c = 0 then some (.var x) else none
  | .sub, [.var x, .lit c] => if litValue c = 0 then some (.var x) else none
  | .or,  [.var x, .lit c] => if litValue c = 0 then some (.var x) else none
  | .xor, [.var x, .lit c] => if litValue c = 0 then some (.var x) else none
  | .mul, [.var x, .lit c] => if litValue c = 1 then some (.var x) else none
  | .div, [.var x, .lit c] => if litValue c = 1 then some (.var x) else none
  | .and, [.var x, .lit c] => if litValue c = allOnes then some (.var x) else none
  | .add, [.lit c, .var x] => if litValue c = 0 then some (.var x) else none
  | .or,  [.lit c, .var x] => if litValue c = 0 then some (.var x) else none
  | .xor, [.lit c, .var x] => if litValue c = 0 then some (.var x) else none
  | .mul, [.lit c, .var x] => if litValue c = 1 then some (.var x) else none
  | .and, [.lit c, .var x] => if litValue c = allOnes then some (.var x) else none
  | _, _ => none

/-- Every neutral rewrite is a sound equivalence. -/
theorem neutral_equiv {op : Op} {args : List (Expr Op)} {e : Expr Op}
    (h : neutral op args = some e) : EquivExpr D (.builtin op args) e := by
  unfold neutral at h
  split at h <;>
    first
      | contradiction
      | (split_ifs at h with hc <;>
          first
            | contradiction
            | (obtain rfl := Option.some.inj h;
               first
                 | exact builtin_var_lit_equiv (fun v => by
                     rw [hc]; simp only [pureFn, Option.some.injEq]
                     first | simp | (rw [allOnes]; exact BitVec.and_allOnes))
                 | exact builtin_lit_var_equiv (fun v => by
                     rw [hc]; simp only [pureFn, Option.some.injEq]
                     first | simp | (rw [allOnes]; exact BitVec.allOnes_and))))

/-- The local built-in rewrite: constant-fold, else a neutral rewrite, else
rebuild unchanged.  Its arguments are assumed already simplified. -/
def simplifyBuiltin (op : Op) (args : List (Expr Op)) : Expr Op :=
  match (asLits args).bind (pureFold op) with
  | some l => .lit l
  | none => (neutral op args).getD (.builtin op args)

/-- The local built-in rewrite is sound. -/
theorem simplifyBuiltin_equiv (op : Op) (args : List (Expr Op)) :
    EquivExpr D (.builtin op args) (simplifyBuiltin op args) := by
  unfold simplifyBuiltin
  split
  · rename_i l hbind
    rw [Option.bind_eq_some_iff] at hbind
    obtain ⟨lits, hlits, hfold⟩ := hbind
    rw [asLits_map hlits]
    exact fold_equiv hfold
  · cases hn : neutral op args with
    | none => exact EquivExpr.refl _
    | some e => exact neutral_equiv hn

/-! ### The recursive pass

`simplifyExpr`/`simplifyStmt` rewrite bottom-up through the whole program,
**including `funDef` bodies** (soundness there uses the function-environment
congruence `EquivBlock.of_stmts_funs` from `FunCongr`).  The only position left
untouched is a `for`-loop's `init` block, which is both executed *and* hoisted
into the loop's scope — changing it needs a `for`-specific congruence beyond the
upstream `forLoop_congr` (which fixes `init`); that is a logged follow-up. -/

mutual

/-- Simplify an expression bottom-up. -/
def simplifyExpr : Expr Op → Expr Op
  | .lit l => .lit l
  | .var x => .var x
  | .builtin op args => simplifyBuiltin op (simplifyArgs args)
  | .call f args => .call f (simplifyArgs args)

/-- Simplify each expression of an argument list. -/
def simplifyArgs : List (Expr Op) → List (Expr Op)
  | [] => []
  | e :: rest => simplifyExpr e :: simplifyArgs rest

end

mutual

/-- Simplify a statement, recursing into every sub-block (including `funDef`
bodies) except a `for`-loop's `init`. -/
def simplifyStmt : Stmt Op → Stmt Op
  | .block body => .block (simplifyStmts body)
  | .funDef n ps rs body => .funDef n ps rs (simplifyStmts body)
  | .letDecl xs (some e) => .letDecl xs (some (simplifyExpr e))
  | .letDecl xs none => .letDecl xs none
  | .assign xs e => .assign xs (simplifyExpr e)
  | .cond c body => .cond (simplifyExpr c) (simplifyStmts body)
  | .switch c cases dflt => .switch (simplifyExpr c) (simplifyCases cases) (simplifyDflt dflt)
  | .forLoop init c post body =>
      .forLoop init (simplifyExpr c) (simplifyStmts post) (simplifyStmts body)
  | .exprStmt e => .exprStmt (simplifyExpr e)
  | .break => .break
  | .continue => .continue
  | .leave => .leave

/-- Simplify each statement of a sequence. -/
def simplifyStmts : List (Stmt Op) → List (Stmt Op)
  | [] => []
  | s :: rest => simplifyStmt s :: simplifyStmts rest

/-- Simplify each `switch` case body, preserving the labels. -/
def simplifyCases : List (Literal × Block Op) → List (Literal × Block Op)
  | [] => []
  | (l, b) :: rest => (l, simplifyStmts b) :: simplifyCases rest

/-- Simplify a `switch`'s optional default block. -/
def simplifyDflt : Option (Block Op) → Option (Block Op)
  | none => none
  | some b => some (simplifyStmts b)

end

/-! ### Soundness of the pass -/

/-- A `funDef` statement is a no-op — its body runs only when the function is
*called* — so changing the body leaves the statement's own behavior unchanged.
The body's equivalence matters at the block level, through the hoisted scope
(`scopeRel_hoistSimplify` + `EquivBlock.of_stmts_funs`). -/
theorem funDef_equiv (n : Ident) (ps rs : List Ident) (b₁ b₂ : Block Op) :
    EquivStmt D (.funDef n ps rs b₁) (.funDef n ps rs b₂) := by
  intro funs V st V' st' o
  constructor <;> (intro h; cases h; exact Step.funDef)

mutual

/-- Every expression is equivalent to its simplification. -/
theorem simplifyExpr_equiv : ∀ e : Expr Op, EquivExpr D e (simplifyExpr e)
  | .lit _ => EquivExpr.refl _
  | .var _ => EquivExpr.refl _
  | .builtin op args =>
      (EquivExpr.builtin_congr op (EquivArgs.of_forall₂ (simplifyArgs_forall2 args))).trans
        (simplifyBuiltin_equiv op (simplifyArgs args))
  | .call f args =>
      EquivExpr.call_congr f (EquivArgs.of_forall₂ (simplifyArgs_forall2 args))

/-- Each argument is equivalent to its simplification, pairwise. -/
theorem simplifyArgs_forall2 : ∀ args : List (Expr Op),
    List.Forall₂ (EquivExpr D) args (simplifyArgs args)
  | [] => .nil
  | e :: rest => .cons (simplifyExpr_equiv e) (simplifyArgs_forall2 rest)

end

mutual

/-- Every statement is equivalent to its simplification. -/
theorem simplifyStmt_equiv : ∀ s : Stmt Op, EquivStmt D s (simplifyStmt s)
  | .block body =>
      EquivBlock.of_stmts_funs (EquivStmts.of_forall₂ (simplifyStmts_forall2 body))
        (scopeRel_hoistSimplify body)
  | .funDef n ps rs body => funDef_equiv n ps rs body (simplifyStmts body)
  | .letDecl _ (some e) => EquivStmt.letDecl_congr _ (simplifyExpr_equiv e)
  | .letDecl _ none => EquivStmt.refl _
  | .assign _ e => EquivStmt.assign_congr _ (simplifyExpr_equiv e)
  | .cond c body =>
      EquivStmt.cond_congr (simplifyExpr_equiv c)
        (EquivBlock.of_stmts_funs (EquivStmts.of_forall₂ (simplifyStmts_forall2 body))
          (scopeRel_hoistSimplify body))
  | .switch c cases dflt => by
      refine EquivStmt.switch_congr (simplifyExpr_equiv c) (simplifyCases_forall2 cases) ?_
      cases dflt with
      | none => exact EquivBlock.refl _
      | some b =>
          exact EquivBlock.of_stmts_funs (EquivStmts.of_forall₂ (simplifyStmts_forall2 b))
            (scopeRel_hoistSimplify b)
  | .forLoop init c post body =>
      EquivStmt.forLoop_congr init (simplifyExpr_equiv c)
        (EquivBlock.of_stmts_funs (EquivStmts.of_forall₂ (simplifyStmts_forall2 post))
          (scopeRel_hoistSimplify post))
        (EquivBlock.of_stmts_funs (EquivStmts.of_forall₂ (simplifyStmts_forall2 body))
          (scopeRel_hoistSimplify body))
  | .exprStmt e => EquivStmt.exprStmt_congr (simplifyExpr_equiv e)
  | .break => EquivStmt.refl _
  | .continue => EquivStmt.refl _
  | .leave => EquivStmt.refl _

/-- Each statement of a sequence is equivalent to its simplification, pairwise. -/
theorem simplifyStmts_forall2 : ∀ ss : List (Stmt Op),
    List.Forall₂ (EquivStmt D) ss (simplifyStmts ss)
  | [] => .nil
  | s :: rest => .cons (simplifyStmt_equiv s) (simplifyStmts_forall2 rest)

/-- Each `switch` case is label-equal and body-equivalent to its simplification. -/
theorem simplifyCases_forall2 : ∀ cs : List (Literal × Block Op),
    List.Forall₂ (fun p q => p.1 = q.1 ∧ EquivBlock D p.2 q.2) cs (simplifyCases cs)
  | [] => .nil
  | (_, b) :: rest =>
      .cons ⟨rfl, EquivBlock.of_stmts_funs (EquivStmts.of_forall₂ (simplifyStmts_forall2 b))
        (scopeRel_hoistSimplify b)⟩ (simplifyCases_forall2 rest)

/-- The pass changes only `funDef` *bodies* (to `EquivBlock`-equivalent ones with
identical signatures), so a block's hoisted scope maps to a `ScopeRel`-related
one — the side condition of `EquivBlock.of_stmts_funs`. -/
theorem scopeRel_hoistSimplify : ∀ ss : List (Stmt Op),
    ScopeRel D (hoist D ss) (hoist D (simplifyStmts ss))
  | [] => .nil
  | .funDef _ _ _ body :: rest =>
      .cons ⟨rfl, rfl, rfl,
        EquivBlock.of_stmts_funs (EquivStmts.of_forall₂ (simplifyStmts_forall2 body))
          (scopeRel_hoistSimplify body)⟩ (scopeRel_hoistSimplify rest)
  | .block _ :: rest => scopeRel_hoistSimplify rest
  | .letDecl _ (some _) :: rest => scopeRel_hoistSimplify rest
  | .letDecl _ none :: rest => scopeRel_hoistSimplify rest
  | .assign _ _ :: rest => scopeRel_hoistSimplify rest
  | .cond _ _ :: rest => scopeRel_hoistSimplify rest
  | .switch _ _ _ :: rest => scopeRel_hoistSimplify rest
  | .forLoop _ _ _ _ :: rest => scopeRel_hoistSimplify rest
  | .exprStmt _ :: rest => scopeRel_hoistSimplify rest
  | .break :: rest => scopeRel_hoistSimplify rest
  | .continue :: rest => scopeRel_hoistSimplify rest
  | .leave :: rest => scopeRel_hoistSimplify rest

end

/-- A block is equivalent to its simplification (statement congruence lifted
through the function-environment congruence). -/
theorem blockEquiv (b : List (Stmt Op)) : EquivBlock D b (simplifyStmts b) :=
  EquivBlock.of_stmts_funs (EquivStmts.of_forall₂ (simplifyStmts_forall2 b))
    (scopeRel_hoistSimplify b)

/-! ### The pass preserves well-scopedness

`simplify` never introduces a variable read (folding/neutralizing only shrink the
read-set) and preserves the declaration structure exactly (it leaves `let`/assign
variable lists and a `for`'s `init` untouched), so it maps well-scoped programs to
well-scoped programs — the `Pass.scoped` obligation. -/

/-- A scoped argument list scopes each of its members. -/
theorem ScopedArgs_of_mem {Γ : List Ident} : ∀ {es : List (Expr Op)} {e : Expr Op},
    ScopedArgs Γ es → e ∈ es → ScopedExpr Γ e := by
  intro es
  induction es with
  | nil => intro e h hmem; simp at hmem
  | cons a rest ih =>
      intro e h hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact h.1
      · exact ih h.2 hmem

/-- A neutral rewrite returns one of its (variable) arguments. -/
theorem neutral_mem {op : Op} {args : List (Expr Op)} {e : Expr Op}
    (hn : neutral op args = some e) : e ∈ args := by
  unfold neutral at hn
  split at hn <;>
    first
      | contradiction
      | (split_ifs at hn <;>
          first | contradiction | (obtain rfl := Option.some.inj hn; simp))

/-- The local built-in rewrite preserves scoping (its output reads only what its
already-scoped arguments read). -/
theorem simplifyBuiltin_scoped {Γ : List Ident} (op : Op) (args : List (Expr Op))
    (h : ScopedArgs Γ args) : ScopedExpr Γ (simplifyBuiltin op args) := by
  unfold simplifyBuiltin
  split
  · exact True.intro
  · cases hn : neutral op args with
    | none => exact h
    | some e => exact ScopedArgs_of_mem h (neutral_mem hn)

mutual
/-- Simplifying an expression preserves scoping. -/
theorem simplifyExpr_scoped {Γ : List Ident} : ∀ (e : Expr Op),
    ScopedExpr Γ e → ScopedExpr Γ (simplifyExpr e)
  | .lit _, h => h
  | .var _, h => h
  | .builtin op args, h => simplifyBuiltin_scoped op _ (simplifyArgs_scoped args h)
  | .call _ args, h => simplifyArgs_scoped args h
/-- Simplifying an argument list preserves scoping. -/
theorem simplifyArgs_scoped {Γ : List Ident} : ∀ (es : List (Expr Op)),
    ScopedArgs Γ es → ScopedArgs Γ (simplifyArgs es)
  | [], h => h
  | e :: rest, h => ⟨simplifyExpr_scoped e h.1, simplifyArgs_scoped rest h.2⟩
end

/-- `simplify` leaves the declared-variable list of every statement unchanged, so
scope-threading through a sequence is preserved. -/
theorem simplifyStmt_declVars : ∀ (s : Stmt Op), declVars (simplifyStmt s) = declVars s
  | .letDecl _ (some _) => rfl
  | .letDecl _ none => rfl
  | .block _ => rfl
  | .funDef _ _ _ _ => rfl
  | .assign _ _ => rfl
  | .cond _ _ => rfl
  | .switch _ _ _ => rfl
  | .forLoop _ _ _ _ => rfl
  | .exprStmt _ => rfl
  | .break => rfl
  | .continue => rfl
  | .leave => rfl

mutual
/-- Simplifying a statement preserves scoping. -/
theorem simplifyStmt_scoped {Γ : List Ident} : ∀ (s : Stmt Op),
    ScopedStmt Γ s → ScopedStmt Γ (simplifyStmt s)
  | .block body, h => simplifyStmts_scoped body h
  | .funDef _ _ _ body, h => simplifyStmts_scoped body h
  | .letDecl _ (some e), h => simplifyExpr_scoped e h
  | .letDecl _ none, h => h
  | .assign _ e, h => ⟨h.1, simplifyExpr_scoped e h.2⟩
  | .cond c body, h => ⟨simplifyExpr_scoped c h.1, simplifyStmts_scoped body h.2⟩
  | .switch c cases dflt, h =>
      ⟨simplifyExpr_scoped c h.1, simplifyCases_scoped cases h.2.1, simplifyDflt_scoped dflt h.2.2⟩
  | .forLoop init c post body, h =>
      ⟨h.1, simplifyExpr_scoped c h.2.1, simplifyStmts_scoped post h.2.2.1,
        simplifyStmts_scoped body h.2.2.2⟩
  | .exprStmt e, h => simplifyExpr_scoped e h
  | .break, h => h
  | .continue, h => h
  | .leave, h => h
/-- Simplifying a statement sequence preserves scoping. -/
theorem simplifyStmts_scoped {Γ : List Ident} : ∀ (ss : List (Stmt Op)),
    ScopedStmts Γ ss → ScopedStmts Γ (simplifyStmts ss)
  | [], h => h
  | s :: rest, h =>
      ⟨simplifyStmt_scoped s h.1, by
        rw [simplifyStmt_declVars]; exact simplifyStmts_scoped rest h.2⟩
/-- Simplifying `switch` cases preserves scoping. -/
theorem simplifyCases_scoped {Γ : List Ident} : ∀ (cs : List (Literal × Block Op)),
    ScopedCases Γ cs → ScopedCases Γ (simplifyCases cs)
  | [], h => h
  | (_, b) :: rest, h => ⟨simplifyStmts_scoped b h.1, simplifyCases_scoped rest h.2⟩
/-- Simplifying a `switch` default preserves scoping. -/
theorem simplifyDflt_scoped {Γ : List Ident} : ∀ (dflt : Option (Block Op)),
    ScopedOptBlock Γ dflt → ScopedOptBlock Γ (simplifyDflt dflt)
  | none, h => h
  | some b, h => simplifyStmts_scoped b h
end

/-- The **Simplify pass**: constant folding + neutral-element identities over the
whole program (including function bodies; only a `for`-loop's `init` is left
untouched), bundled with its soundness and scope-preservation proofs. -/
def simplify : Pass D where
  run := simplifyStmts
  sound := fun b _ => blockEquiv b
  preservesScoped := fun b hb => simplifyStmts_scoped b hb

/-! ### Optimizing a whole object tree

`simplifyObject` runs the pass on **every** code block of an object tree — the
top (deploy) object and every nested sub-object (e.g. the `*_deployed` runtime of
a Solidity artifact) — leaving names and data segments intact. Each code block is
`EquivBlock`-equivalent to the original (`simplifyObject_codeBlock` +
`blockEquiv`), and the emitted bytecode is the verified compilation of the
result (`compileObject_correct`); the object-tree correctness statement is
`Pass.optimizeObject_compileObject_correct` in `ObjectPass`. -/

mutual

/-- Run the pass on every code block of an object and its sub-objects. -/
def simplifyObject : Object Op → Object Op
  | .mk n code subs segs => .mk n (simplifyStmts code) (simplifyObjects subs) segs

/-- Run `simplifyObject` on each object of a list. -/
def simplifyObjects : List (Object Op) → List (Object Op)
  | [] => []
  | o :: rest => simplifyObject o :: simplifyObjects rest

end

@[simp] theorem simplifyObject_codeBlock (o : Object Op) :
    (simplifyObject o).codeBlock = simplifyStmts o.codeBlock := by
  cases o; rw [simplifyObject]; rfl

/-! ### Regression examples (checked at build time) -/

/-- Constant folding of a pure built-in on literals. -/
example : simplifyExpr (.builtin .add [.lit (.number 2), .lit (.number 3)]) = .lit (.number 5) := rfl
/-- Nested folding: `mul(add(1,2), 1) = 3`. -/
example : simplifyExpr (.builtin .mul [.builtin .add [.lit (.number 1), .lit (.number 2)],
    .lit (.number 1)]) = .lit (.number 3) := rfl
/-- Right neutral: `add(x, 0) = x`. -/
example : simplifyExpr (.builtin .add [.var "x", .lit (.number 0)]) = .var "x" := rfl
/-- Left neutral: `mul(1, x) = x`. -/
example : simplifyExpr (.builtin .mul [.lit (.number 1), .var "x"]) = .var "x" := rfl
/-- Mask by all-ones is the identity: `and(x, 2²⁵⁶−1) = x`. -/
example : simplifyExpr (.builtin .and [.var "x", .lit (.number (2 ^ 256 - 1))]) = .var "x" := rfl
/-- Non-pure built-ins are left untouched. -/
example : simplifyExpr (.builtin .sload [.lit (.number 0)]) =
    .builtin .sload [.lit (.number 0)] := rfl
/-- User-function calls are not folded (only their arguments are simplified). -/
example : simplifyExpr (.call "f" [.builtin .add [.lit (.number 2), .lit (.number 3)]]) =
    .call "f" [.lit (.number 5)] := rfl
/-- Folding fires under a statement, through the congruences. -/
example : simplifyStmts [.exprStmt (.builtin .sstore [.lit (.number 0),
    .builtin .add [.lit (.number 2), .lit (.number 3)]])]
  = [.exprStmt (.builtin .sstore [.lit (.number 0), .lit (.number 5)])] := rfl

end YulEvmCompiler.Optimizer
