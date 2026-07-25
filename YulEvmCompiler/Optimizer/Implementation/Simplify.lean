import YulEvmCompiler.Optimizer.Spec.LocalPass
import YulEvmCompiler.Optimizer.Core.Rule
import YulEvmCompiler.Optimizer.Implementation.FunCongr
import YulSemantics.Dialect.EVM
set_option warningAsError true
/-!
# YulEvmCompiler.Optimizer.Implementation.Simplify

A local **expression + constant-control-flow** simplifier for the EVM dialect,
the first real `Optimizer.LocalPass`. It rewrites, bottom-up:

* a pure built-in applied to all-literal arguments → the folded literal
  (`add(2,3) → 5`);
* a pure built-in with a neutral literal operand kept alongside a *variable*
  (`add(x,0) → x`, `mul(x,1) → x`, `and(x, 2²⁵⁶−1) → x`, `shl(0,x) → x`, …);
* an `if` whose simplified condition is literal → its body or an empty block;
* an `if iszero(eq(x,x)) { body }` validator residue → evaluation and discard
  of the condition (preserving unbound-variable stuckness); and
* a `switch` whose simplified condition is literal → its selected case/default
  block.

Everything here is dialect-EVM specific (it computes with `stepOp`/`litValue`),
so it lives under `Optimizer/Implementation/`.  Only its type — a `LocalPass` — is
trusted by the audited surface; the internal proofs below need no separate audit.

## Why these rewrites are sound

The pure EVM ops (`add … sar`) reduce via `stepOp op vs st = some (.ok [f vs] st)`:
the result value is a total function of the argument *values* and the state is
unchanged.  So folding all-literal applications and neutral-operand rewrites are
pointwise `EquivExpr`s (`YulSemantics.Equiv`), lifted through the built-in and
statement congruences to `EquivBlock`, discharging the `LocalPass` obligation `Sound`.

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

/-- The open-world EVM dialect this pass is a `LocalPass` over — the dialect the
verified backend theorem (`LocalPass.optimize_then_compile_correct`) is stated
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

/-- Every successful constant fold produces a number literal. -/
theorem pureFold_isNumber {op : Op} {lits : List Literal} {literal : Literal}
    (h : pureFold op lits = some literal) : ∃ n, literal = .number n := by
  rw [pureFold, Option.map_eq_some_iff] at h
  obtain ⟨word, _, rfl⟩ := h
  exact ⟨word.toNat, rfl⟩

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
      | (split_ifs at h with hc;
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

/-- Every successful neutral rewrite returns a variable. -/
theorem neutral_result_var {op : Op} {args : List (Expr Op)} {e : Expr Op}
    (h : neutral op args = some e) : ∃ name, e = .var name := by
  unfold neutral at h
  split at h <;>
    first
      | contradiction
      | (split_ifs at h;
          first
            | contradiction
            | (obtain rfl := Option.some.inj h; exact ⟨_, rfl⟩))

/-! ### Core-backed, proof-carrying rewrite rules

Flat pure applications now cross the Core boundary.  The Core type certifies
that every argument is an ANF value, the operation is state-independent, its
input arity is correct, and every variable belongs to the expression context.
Each rule below carries its own `EquivExpr` proof; the generic engine in
`Optimizer/Core/Rule.lean` composes the ordered policy without inspecting the
rules.  Unsupported syntax is left unchanged by the Core boundary. -/

namespace Core

/-- Constant-fold one typed, all-literal Core application. -/
def foldRewrite {Γ : Ctx} : Term Γ 1 → Option (Term Γ 1)
  | .atom _ => none
  | .builtin op args => do
      let lits ← asLits args.emit
      let literal ← pureFold op.toOp lits
      return .atom (.lit literal)

/-- The Core constant-folding rule is sound. -/
theorem foldRewrite_sound {Γ : Ctx} {input output : Term Γ 1}
    (h : foldRewrite input = some output) :
    EquivExpr D input.emit output.emit := by
  cases input with
  | atom value => simp [foldRewrite] at h
  | builtin op args =>
      cases hlits : asLits args.emit with
      | none => simp [foldRewrite, hlits] at h
      | some lits =>
          cases hfold : pureFold op.toOp lits with
          | none => simp [foldRewrite, hlits, hfold] at h
          | some literal =>
              simp [foldRewrite, hlits, hfold] at h
              subst output
              simp only [Term.emit, Value.emit]
              rw [asLits_map hlits]
              exact fold_equiv hfold

/-- Apply a neutral-element rule to a typed Core application.  Re-ingestion of
the survivor retains its original variable-membership proof. -/
def neutralRewrite {Γ : Ctx} : Term Γ 1 → Option (Term Γ 1)
  | .atom _ => none
  | .builtin op args => do
      let survivor ← neutral op.toOp args.emit
      let value ← ingestValue Γ survivor
      return .atom value

/-- The Core neutral-element rule is sound. -/
theorem neutralRewrite_sound {Γ : Ctx} {input output : Term Γ 1}
    (h : neutralRewrite input = some output) :
    EquivExpr D input.emit output.emit := by
  cases input with
  | atom value => simp [neutralRewrite] at h
  | builtin op args =>
      cases hneutral : neutral op.toOp args.emit with
      | none => simp [neutralRewrite, hneutral] at h
      | some survivor =>
          cases hvalue : ingestValue Γ survivor with
          | none => simp [neutralRewrite, hneutral, hvalue] at h
          | some value =>
              simp [neutralRewrite, hneutral, hvalue] at h
              subst output
              simp only [Term.emit]
              rw [ingestValue_emit hvalue]
              exact neutral_equiv hneutral

/-- Constant-folding packaged as a first-class proved rule. -/
def foldRule : Rule where
  rewrite := foldRewrite
  sound := foldRewrite_sound

/-- Neutral identities packaged as a first-class proved rule. -/
def neutralRule : Rule where
  rewrite := neutralRewrite
  sound := neutralRewrite_sound

/-- The current Core simplification policy: constant folding has priority over
neutral-element rewriting, matching the established pass. -/
def simplifyRules : List Rule := [foldRule, neutralRule]

/-- Simplify a typed Core term with the generic proof-carrying rule engine. -/
def simplifyTerm (term : Term Γ 1) : Term Γ 1 := run simplifyRules term

/-- Core simplification preserves the exact upstream expression semantics. -/
theorem simplifyTerm_sound (term : Term Γ 1) :
    EquivExpr D term.emit (simplifyTerm term).emit :=
  run_sound simplifyRules term

/-- A successful fold rule produces a number atom. -/
theorem foldRewrite_shape {input output : Term Γ 1}
    (h : foldRewrite input = some output) :
    ∃ n, output = .atom (.lit (.number n)) := by
  cases input with
  | atom value => simp [foldRewrite] at h
  | builtin op args =>
      cases hlits : asLits args.emit with
      | none => simp [foldRewrite, hlits] at h
      | some lits =>
          cases hfold : pureFold op.toOp lits with
          | none => simp [foldRewrite, hlits, hfold] at h
          | some literal =>
              simp [foldRewrite, hlits, hfold] at h
              subst output
              obtain ⟨n, rfl⟩ := pureFold_isNumber hfold
              exact ⟨n, rfl⟩

/-- A successful neutral rule produces a variable atom. -/
theorem neutralRewrite_shape {input output : Term Γ 1}
    (h : neutralRewrite input = some output) :
    ∃ ref, output = .atom (.var ref) := by
  cases input with
  | atom value => simp [neutralRewrite] at h
  | builtin op args =>
      cases hneutral : neutral op.toOp args.emit with
      | none => simp [neutralRewrite, hneutral] at h
      | some survivor =>
          obtain ⟨name, hs⟩ := neutral_result_var hneutral
          subst survivor
          cases hvalue : ingestValue Γ (.var name) with
          | none => simp [neutralRewrite, hneutral, hvalue] at h
          | some value =>
              simp [neutralRewrite, hneutral, hvalue] at h
              subst output
              cases value with
              | lit literal =>
                  have hemit := ingestValue_emit hvalue
                  simp [Value.emit] at hemit
              | var ref => exact ⟨ref, rfl⟩

/-- The Core simplifier either leaves its input alone, folds to a number, or
returns a variable.  In particular, it never manufactures a string literal. -/
theorem simplifyTerm_shape (input : Term Γ 1) :
    simplifyTerm input = input ∨
      (∃ n, simplifyTerm input = .atom (.lit (.number n))) ∨
      (∃ ref, simplifyTerm input = .atom (.var ref)) := by
  cases hfold : foldRewrite input with
  | some folded =>
      obtain ⟨n, rfl⟩ := foldRewrite_shape hfold
      exact Or.inr (Or.inl ⟨n, by
        simp [simplifyTerm, run, first, simplifyRules, foldRule, hfold]⟩)
  | none =>
      cases hneutral : neutralRewrite input with
      | some rewritten =>
          obtain ⟨ref, rfl⟩ := neutralRewrite_shape hneutral
          exact Or.inr (Or.inr ⟨ref, by
            simp [simplifyTerm, run, first, simplifyRules, foldRule, neutralRule,
              hfold, hneutral]⟩)
      | none =>
          exact Or.inl (by
            simp [simplifyTerm, run, first, simplifyRules, foldRule, neutralRule,
              hfold, hneutral])

end Core

/-- The local built-in rewrite.  Supported flat pure syntax is ingested into
Core and simplified by proof-carrying rules; all other syntax is unchanged.
Arguments are assumed already simplified by the traversal. -/
def simplifyBuiltin (op : Op) (args : List (Expr Op)) : Expr Op :=
  let source : Expr Op := .builtin op args
  match Core.ingestSelf source with
  | some core => (Core.simplifyTerm core).emit
  | none => source

/-- The Core-backed local rewrite is sound. -/
theorem simplifyBuiltin_equiv (op : Op) (args : List (Expr Op)) :
    EquivExpr D (.builtin op args) (simplifyBuiltin op args) := by
  simp only [simplifyBuiltin]
  cases hcore : Core.ingestSelf (Expr.builtin op args) with
  | some core =>
    have herase := Core.ingestSelf_emit hcore
    simpa only [herase] using
      (Core.simplifyTerm_sound (calls := calls) (creates := creates) core)
  | none => exact EquivExpr.refl _

/-! ### Open-operand neutral identities

`neutral` fires only on one-variable-one-literal operand pairs, because it runs
through the Core boundary whose arguments are atoms. The dumps after
`InlineCalls` are dominated by redexes with one *arbitrary* operand — the
`InlineHelpers` identity fence `add(f(…), 0)`, and residue like
`or(0, eq(…))` — which never ingest.

`openNeutral` recognizes those: one operand is the op's neutral literal, the
other survives **unchanged, whatever it is** (calls included). The rewrite is
*not* a pointwise `EquivExpr` for arbitrary survivors — `add(e, 0)` is stuck
when `e` yields zero or several values, while bare `e` is not (that asymmetry
is exactly why the inliner's fence exists). It agrees with the redex on
single-value results and halts (`EquivExpr1` below), so it is applied only at
positions whose semantics already demand exactly one value: argument elements
(`argsCons` binds a single head value) and singleton `let`/`assign`
right-hand sides (`letVal`/`assignVal` check `vals.length = vars.length`).
Multi-binder right-hand sides, `exprStmt` (demands zero values), and
condition positions are left alone. -/

/-- A survivor a rewrite may return: anything but a bare string literal.
Returning a string literal could put one in `dataoffset`/`datasize` argument
position, where layout resolution treats it specially — the resolution
congruence needs rewrites to never manufacture that shape (the same fence as
`simplifyBuiltin_not_stringlit`). -/
def survivorOK : Expr Op → Bool
  | .lit (.string _) => false
  | _ => true

/-- Recognize a neutral-element binary op with one arbitrary surviving
operand. The surviving operand is returned as-is. -/
def openNeutral : Op → List (Expr Op) → Option (Expr Op)
  | .add, [e, .lit c] => if litValue c = 0 ∧ survivorOK e then some e else none
  | .sub, [e, .lit c] => if litValue c = 0 ∧ survivorOK e then some e else none
  | .or,  [e, .lit c] => if litValue c = 0 ∧ survivorOK e then some e else none
  | .xor, [e, .lit c] => if litValue c = 0 ∧ survivorOK e then some e else none
  | .mul, [e, .lit c] => if litValue c = 1 ∧ survivorOK e then some e else none
  | .div, [e, .lit c] => if litValue c = 1 ∧ survivorOK e then some e else none
  | .and, [e, .lit c] => if litValue c = allOnes ∧ survivorOK e then some e else none
  | .add, [.lit c, e] => if litValue c = 0 ∧ survivorOK e then some e else none
  | .or,  [.lit c, e] => if litValue c = 0 ∧ survivorOK e then some e else none
  | .xor, [.lit c, e] => if litValue c = 0 ∧ survivorOK e then some e else none
  | .mul, [.lit c, e] => if litValue c = 1 ∧ survivorOK e then some e else none
  | .and, [.lit c, e] => if litValue c = allOnes ∧ survivorOK e then some e else none
  | .shl, [.lit c, e] => if litValue c = 0 ∧ survivorOK e then some e else none
  | .shr, [.lit c, e] => if litValue c = 0 ∧ survivorOK e then some e else none
  | .sar, [.lit c, e] => if litValue c = 0 ∧ survivorOK e then some e else none
  | _, _ => none

/-- Rewrite a top-level open-operand redex; leave everything else unchanged.
Applied only at single-value positions (see the section notes). -/
def openTop : Expr Op → Expr Op
  | .builtin op args => (openNeutral op args).getD (.builtin op args)
  | e => e

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

/-- Simplify each expression of an argument list. Argument positions demand a
single value per element, so open-operand redexes are rewritten here. -/
def simplifyArgs : List (Expr Op) → List (Expr Op)
  | [] => []
  | e :: rest => openTop (simplifyExpr e) :: simplifyArgs rest

end

/-! ### Constant control-flow selection

Keep the selected body wrapped in `.block`: this preserves the source branch's
variable restoration and function scope, as well as every non-local outcome.
The smart constructors use the closed EVM dialect because they are syntax
transformations independent of the open-world call/create relations. -/

/-- Recognize `iszero(eq(x,x))`, which is false whenever `x` evaluates. -/
def selfEqVar? : Expr Op → Option Ident
  | .builtin .iszero [.builtin .eq [.var x, .var y]] =>
      if x = y then some x else none
  | _ => none

/-- Fold an `if` with a literal condition to the block it deterministically
executes. A self-equality validator residue retains evaluation of its false
condition under `pop`, preserving stuckness while deleting branch dispatch.
Other conditions are rebuilt unchanged. -/
def simplifyCond (c : Expr Op) (body : Block Op) : Stmt Op :=
  match c with
  | .lit l => if litValue l = 0 then .block [] else .block body
  | _ =>
      match selfEqVar? c with
      | some _ => .exprStmt (.builtin .pop [c])
      | none => .cond c body

/-- Fold a `switch` with a literal condition to the case/default block selected
by the source semantics.  A non-literal condition is rebuilt unchanged. -/
def simplifySwitch (c : Expr Op) (cases : List (Literal × Block Op))
    (dflt : Option (Block Op)) : Stmt Op :=
  match c with
  | .lit l => .block (selectSwitch evm (litValue l) cases dflt)
  | _ => .switch c cases dflt

mutual

/-- Simplify a statement, recursing into every sub-block (including `funDef`
bodies) except a `for`-loop's `init`. -/
def simplifyStmt : Stmt Op → Stmt Op
  | .block body => .block (simplifyStmts body)
  | .funDef n ps rs body => .funDef n ps rs (simplifyStmts body)
  | .letDecl [x] (some e) => .letDecl [x] (some (openTop (simplifyExpr e)))
  | .letDecl xs (some e) => .letDecl xs (some (simplifyExpr e))
  | .letDecl xs none => .letDecl xs none
  | .assign [x] e => .assign [x] (openTop (simplifyExpr e))
  | .assign xs e => .assign xs (simplifyExpr e)
  | .cond c body => simplifyCond (simplifyExpr c) (simplifyStmts body)
  | .switch c cases dflt =>
      simplifySwitch (simplifyExpr c) (simplifyCases cases) (simplifyDflt dflt)
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

/-- Successful recognition exposes the exact self-equality condition. -/
theorem selfEqVar?_some {c : Expr Op} {x : Ident} (h : selfEqVar? c = some x) :
    c = .builtin .iszero [.builtin .eq [.var x, .var x]] := by
  unfold selfEqVar? at h
  split at h
  · next a b =>
      split at h
      · next hab =>
          cases h
          subst b
          rfl
      · contradiction
  · contradiction

/-- A normally evaluated `iszero(eq(x,x))` produces exactly zero and leaves
state unchanged. Repeated evaluation of `x` is retained, so the statement is
still stuck when `x` is unbound. -/
theorem selfEq_zero_inv {funs : FunEnv D} {V : VEnv D} {st st' : EvmState}
    {x : Ident} {cv : U256}
    (h : Step D funs V st
      (.expr (.builtin .iszero [.builtin .eq [.var x, .var x]]))
      (.eres (.vals [cv] st'))) : cv = 0 ∧ st' = st := by
  cases h with
  | builtinOk houter hbzero =>
      cases houter with
      | argsCons hnil heq =>
          cases hnil
          cases heq with
          | builtinOk heqargs hbeq =>
              cases heqargs with
              | argsCons hrest hx1 =>
                  cases hx1 with
                  | var hv1 =>
                      cases hrest with
                      | argsCons hnil hx2 =>
                          cases hx2 with
                          | var hv2 =>
                              cases hnil
                              rw [hv1] at hv2
                              injection hv2 with hv
                              subst hv
                              have heqv := pureFn_builtin_inv
                                (calls := calls) (creates := creates)
                                (w := 1) (by simp [pureFn, b2w]) hbeq
                              injection heqv with hvals hst
                              injection hvals with hv
                              subst hv
                              subst hst
                              have hzero := pureFn_builtin_inv
                                (calls := calls) (creates := creates)
                                (w := 0) (by simp [pureFn, b2w]) hbzero
                              injection hzero with hvals hst
                              exact ⟨by simpa using hvals, hst⟩

/-- A self-equality validator branch is unreachable, but its condition must
still be evaluated to preserve unbound-variable stuckness. `pop(condition)`
does exactly that while deleting the branch and body. -/
theorem cond_selfEq_equiv (x : Ident) (body : Block Op) :
    EquivStmt D
      (.cond (.builtin .iszero [.builtin .eq [.var x, .var x]]) body)
      (.exprStmt (.builtin .pop
        [.builtin .iszero [.builtin .eq [.var x, .var x]]])) := by
  intro funs V st V' st' o
  constructor
  · intro h
    cases h with
    | ifTrue hc hnz _ =>
        obtain ⟨rfl, -⟩ := selfEq_zero_inv hc
        exact absurd rfl hnz
    | ifFalse hc _ =>
        obtain ⟨rfl, rfl⟩ := selfEq_zero_inv hc
        exact Step.exprStmt (Step.builtinOk
          (Step.argsCons Step.argsNil hc) (by rfl))
    | ifHalt hc =>
        exact Step.exprStmtHalt
          (Step.builtinArgsHalt (Step.argsHeadHalt Step.argsNil hc))
  · intro h
    cases h with
    | exprStmt hpop =>
        cases hpop with
        | builtinOk hargs hb =>
            cases hargs with
            | argsCons hnil hc =>
                cases hnil
                simp [evmWithExternal, builtinWithExternal, stepOp] at hb
                subst_vars
                obtain ⟨rfl, rfl⟩ := selfEq_zero_inv hc
                exact Step.ifFalse hc rfl
    | exprStmtHalt hpop =>
        cases hpop with
        | @builtinHalt _ _ _ _ _ argvals _ _ _ hb =>
            simp [evmWithExternal, builtinWithExternal] at hb
            cases argvals with
            | nil => simp [stepOp] at hb
            | cons _ rest =>
                cases rest with
                | nil => simp [stepOp] at hb
                | cons _ _ => simp [stepOp] at hb
        | builtinArgsHalt hargs =>
            cases hargs with
            | argsRestHalt hnil => cases hnil
            | argsHeadHalt hnil hc =>
                cases hnil
                exact Step.ifHalt hc

/-- A false literal `if` is exactly an empty block. -/
theorem cond_lit_zero_equiv (l : Literal) (body : Block Op)
    (hz : (evmWithExternal calls creates).litValue l =
      (evmWithExternal calls creates).zero) :
    EquivStmt D (.cond (.lit l) body) (.block []) := by
  intro funs V st V' st' o
  constructor
  · intro h
    cases h with
    | ifTrue hc hnz _ => cases hc; exact absurd hz hnz
    | ifFalse hc _ =>
        cases hc
        simpa [restore] using
          (Step.block (funs := funs) (V := V) (st := st) Step.seqNil)
    | ifHalt hc => cases hc
  · intro h
    cases h with
    | block hb =>
        cases hb
        simpa [restore] using (Step.ifFalse (body := body) Step.lit hz)

/-- A true literal `if` is exactly its body block. -/
theorem cond_lit_nonzero_equiv (l : Literal) (body : Block Op)
    (hnz : (evmWithExternal calls creates).litValue l ≠
      (evmWithExternal calls creates).zero) :
    EquivStmt D (.cond (.lit l) body) (.block body) := by
  intro funs V st V' st' o
  constructor
  · intro h
    cases h with
    | ifTrue hc _ hb => cases hc; exact hb
    | ifFalse hc hz => cases hc; exact absurd hz hnz
    | ifHalt hc => cases hc
  · intro h
    exact Step.ifTrue Step.lit hnz h

/-- A literal `switch` is exactly the case/default block selected by the source
semantics (including first-match behavior). -/
theorem selectSwitch_open_eq (value : U256) (cases : List (Literal × Block Op))
    (dflt : Option (Block Op)) :
    selectSwitch (evmWithExternal calls creates) value cases dflt =
      selectSwitch evm value cases dflt := by
  induction cases with
  | nil => simp [selectSwitch]
  | cons head rest ih =>
      rcases head with ⟨l, body⟩
      by_cases h : value = litValue l
      · simp [selectSwitch, h, evmWithExternal, evm]
      · simpa [selectSwitch, h, evmWithExternal, evm] using ih

theorem switch_lit_equiv (l : Literal) (cases : List (Literal × Block Op))
    (dflt : Option (Block Op)) :
    EquivStmt D (.switch (.lit l) cases dflt)
      (.block (selectSwitch evm (litValue l) cases dflt)) := by
  intro funs V st V' st' o
  constructor
  · intro h
    cases h with
    | switchExec hc hb =>
        cases hc
        rw [selectSwitch_open_eq] at hb
        exact hb
    | switchHalt hc => cases hc
  · intro h
    rw [← selectSwitch_open_eq] at h
    exact Step.switchExec Step.lit h

/-- The `if` smart constructor is semantics-preserving. -/
theorem simplifyCond_equiv (c : Expr Op) (body : Block Op) :
    EquivStmt D (.cond c body) (simplifyCond c body) := by
  cases c with
  | lit l =>
      rw [simplifyCond]
      split
      · next h => exact cond_lit_zero_equiv l body h
      · next h => exact cond_lit_nonzero_equiv l body h
  | var _ => exact EquivStmt.refl _
  | builtin op args =>
      cases hself : selfEqVar? (.builtin op args) with
      | none =>
          have hrefl : EquivStmt D (.cond (.builtin op args) body)
              (.cond (.builtin op args) body) := fun _ _ _ _ _ _ => Iff.rfl
          simpa [simplifyCond, hself] using hrefl
      | some x =>
          have hshape := selfEqVar?_some hself
          rw [hshape]
          simpa [simplifyCond, selfEqVar?] using
            (cond_selfEq_equiv (calls := calls) (creates := creates) x body)
  | call _ _ => exact EquivStmt.refl _

/-- The `switch` smart constructor is semantics-preserving. -/
theorem simplifySwitch_equiv (c : Expr Op) (cases : List (Literal × Block Op))
    (dflt : Option (Block Op)) :
    EquivStmt D (.switch c cases dflt) (simplifySwitch c cases dflt) := by
  cases c with
  | lit l => exact switch_lit_equiv l cases dflt
  | var _ => exact EquivStmt.refl _
  | builtin _ _ => exact EquivStmt.refl _
  | call _ _ => exact EquivStmt.refl _

/-- A folded `if` never contributes a function declaration to its enclosing
hoisted scope. -/
theorem hoist_simplifyCond_cons (c : Expr Op) (body rest : Block Op) :
    hoist D (simplifyCond c body :: rest) = hoist D rest := by
  cases c with
  | lit l => rw [simplifyCond]; split <;> rfl
  | var _ => rfl
  | builtin op args =>
      cases hself : selfEqVar? (.builtin op args) <;>
        simp [simplifyCond, hself, hoist]
  | call _ _ => rfl

/-- A folded `switch` never contributes a function declaration to its enclosing
hoisted scope. -/
theorem hoist_simplifySwitch_cons (c : Expr Op) (cases : List (Literal × Block Op))
    (dflt : Option (Block Op)) (rest : Block Op) :
    hoist D (simplifySwitch c cases dflt :: rest) = hoist D rest := by
  cases c <;> simp [simplifySwitch, hoist]

/-! ### Value-restricted equivalence, and soundness of the open-operand rewrites

`EquivExpr1` is agreement on *single-value results and halts* — everything a
single-value position can observe. It is strictly weaker than `EquivExpr`
(no agreement on zero/multi-value results), and it is exactly the contract
the `openNeutral` rewrites satisfy for arbitrary survivors: `add(e, 0)`
and `e` diverge only on results the consuming positions rule out anyway
(`argsCons` pins argument heads to singletons; `letVal`/`assignVal` pin
right-hand sides to the binder arity). -/

/-- Agreement on single-value results and halts. -/
def EquivExpr1 (e₁ e₂ : Expr Op) : Prop :=
  ∀ funs (V : VEnv D) (st : EvmState),
    (∀ v st', Step D funs V st (.expr e₁) (.eres (.vals [v] st')) ↔
        Step D funs V st (.expr e₂) (.eres (.vals [v] st'))) ∧
    (∀ st', Step D funs V st (.expr e₁) (.eres (.halt st')) ↔
        Step D funs V st (.expr e₂) (.eres (.halt st')))

theorem EquivExpr1.refl (e : Expr Op) :
    EquivExpr1 (calls := calls) (creates := creates) e e :=
  fun _ _ _ => ⟨fun _ _ => Iff.rfl, fun _ => Iff.rfl⟩

theorem EquivExpr1.trans {e₁ e₂ e₃ : Expr Op}
    (h₁ : EquivExpr1 (calls := calls) (creates := creates) e₁ e₂)
    (h₂ : EquivExpr1 (calls := calls) (creates := creates) e₂ e₃) :
    EquivExpr1 (calls := calls) (creates := creates) e₁ e₃ :=
  fun funs V st =>
    ⟨fun v st' => ((h₁ funs V st).1 v st').trans ((h₂ funs V st).1 v st'),
     fun st' => ((h₁ funs V st).2 st').trans ((h₂ funs V st).2 st')⟩

/-- Full pointwise equivalence restricts to the value-restricted one. -/
theorem EquivExpr.toEquivExpr1 {e₁ e₂ : Expr Op}
    (h : EquivExpr D e₁ e₂) :
    EquivExpr1 (calls := calls) (creates := creates) e₁ e₂ :=
  fun funs V st => ⟨fun _ _ => h funs V st _, fun _ => h funs V st _⟩

/-- Inversion of `[e, lit]` argument evaluation to a value list. -/
theorem args_expr_lit_value_inv {funs : FunEnv D} {V st e c vals st'}
    (h : Step D funs V st (.args [e, .lit c]) (.eres (.vals vals st'))) :
    ∃ v, vals = [v, litValue c] ∧
      Step D funs V st (.expr e) (.eres (.vals [v] st')) := by
  cases h with
  | argsCons hrest he =>
      cases hrest with
      | argsCons hnil hc => cases hnil; cases hc; exact ⟨_, rfl, he⟩

/-- Inversion of `[e, lit]` argument evaluation to a halt. -/
theorem args_expr_lit_halt_inv {funs : FunEnv D} {V st e c st'}
    (h : Step D funs V st (.args [e, .lit c]) (.eres (.halt st'))) :
    Step D funs V st (.expr e) (.eres (.halt st')) := by
  cases h with
  | argsRestHalt hrest =>
      cases hrest with
      | argsRestHalt hnil => cases hnil
      | argsHeadHalt hnil hc => cases hnil; cases hc
  | argsHeadHalt hrest he =>
      cases hrest with
      | argsCons hnil hc => cases hnil; cases hc; exact he

/-- Inversion of `[lit, e]` argument evaluation to a value list. -/
theorem args_lit_expr_value_inv {funs : FunEnv D} {V st e c vals st'}
    (h : Step D funs V st (.args [.lit c, e]) (.eres (.vals vals st'))) :
    ∃ v, vals = [litValue c, v] ∧
      Step D funs V st (.expr e) (.eres (.vals [v] st')) := by
  cases h with
  | argsCons hrest he =>
      cases he with
      | lit =>
          cases hrest with
          | argsCons hnil hv => cases hnil; exact ⟨_, rfl, hv⟩

/-- Inversion of `[lit, e]` argument evaluation to a halt. -/
theorem args_lit_expr_halt_inv {funs : FunEnv D} {V st e c st'}
    (h : Step D funs V st (.args [.lit c, e]) (.eres (.halt st'))) :
    Step D funs V st (.expr e) (.eres (.halt st')) := by
  cases h with
  | argsRestHalt hrest =>
      cases hrest with
      | argsRestHalt hnil => cases hnil
      | argsHeadHalt hnil he => cases hnil; exact he
  | argsHeadHalt hrest he => cases he

/-- **Right-operand open neutral**: `op(e, c) ≈₁ e` when `op` maps `(v, c)`
to `v` — for an arbitrary surviving operand. -/
theorem open_right_equiv1 {op : Op} {e : Expr Op} {c : Literal}
    (h : ∀ v : U256, pureFn op [v, litValue c] = some v) :
    EquivExpr1 (calls := calls) (creates := creates) (.builtin op [e, .lit c]) e := by
  intro funs V st
  constructor
  · intro v st'
    constructor
    · intro hb
      cases hb with
      | builtinOk ha hop =>
          obtain ⟨w, rfl, he⟩ := args_expr_lit_value_inv ha
          have := pureFn_builtin_inv (h w) hop
          injection this with hrets hst
          injection hrets with hv _
          subst hv; subst hst
          exact he
    · intro he
      exact Step.builtinOk
        (Step.argsCons (Step.argsCons Step.argsNil Step.lit) he)
        (pureFn_builtin (h v) st')
  · intro st'
    constructor
    · intro hb
      cases hb with
      | builtinHalt ha hop =>
          obtain ⟨w, rfl, he⟩ := args_expr_lit_value_inv ha
          have := pureFn_builtin_inv (h w) hop
          simp at this
      | builtinArgsHalt ha => exact args_expr_lit_halt_inv ha
    · intro he
      exact Step.builtinArgsHalt
        (Step.argsHeadHalt (Step.argsCons Step.argsNil Step.lit) he)

/-- **Left-operand open neutral**: `op(c, e) ≈₁ e` when `op` maps `(c, v)`
to `v` — for an arbitrary surviving operand. -/
theorem open_left_equiv1 {op : Op} {e : Expr Op} {c : Literal}
    (h : ∀ v : U256, pureFn op [litValue c, v] = some v) :
    EquivExpr1 (calls := calls) (creates := creates) (.builtin op [.lit c, e]) e := by
  intro funs V st
  constructor
  · intro v st'
    constructor
    · intro hb
      cases hb with
      | builtinOk ha hop =>
          obtain ⟨w, rfl, he⟩ := args_lit_expr_value_inv ha
          have := pureFn_builtin_inv (h w) hop
          injection this with hrets hst
          injection hrets with hv _
          subst hv; subst hst
          exact he
    · intro he
      exact Step.builtinOk
        (Step.argsCons (Step.argsCons Step.argsNil he) Step.lit)
        (pureFn_builtin (h v) st')
  · intro st'
    constructor
    · intro hb
      cases hb with
      | builtinHalt ha hop =>
          obtain ⟨w, rfl, he⟩ := args_lit_expr_value_inv ha
          have := pureFn_builtin_inv (h w) hop
          simp at this
      | builtinArgsHalt ha => exact args_lit_expr_halt_inv ha
    · intro he
      exact Step.builtinArgsHalt (Step.argsRestHalt
        (Step.argsHeadHalt Step.argsNil he))

/-- Every open-operand rewrite is value-restricted-sound. -/
theorem openNeutral_equiv1 {op : Op} {args : List (Expr Op)} {e : Expr Op}
    (h : openNeutral op args = some e) :
    EquivExpr1 (calls := calls) (creates := creates) (.builtin op args) e := by
  unfold openNeutral at h
  split at h <;>
    first
      | contradiction
      | (split_ifs at h with hc
         · obtain rfl := Option.some.inj h
           first
             | exact open_right_equiv1 (fun v => by
                 rw [hc.1]; simp only [pureFn, Option.some.injEq]
                 first | simp | (rw [allOnes]; exact BitVec.and_allOnes))
             | exact open_left_equiv1 (fun v => by
                 rw [hc.1]; simp only [pureFn, Option.some.injEq]
                 first | simp | (rw [allOnes]; exact BitVec.allOnes_and)))

/-- The top-level open-operand rewrite is value-restricted-sound. -/
theorem openTop_equiv1 : ∀ e : Expr Op,
    EquivExpr1 (calls := calls) (creates := creates) e (openTop e)
  | .lit _ => EquivExpr1.refl _
  | .var _ => EquivExpr1.refl _
  | .call _ _ => EquivExpr1.refl _
  | .builtin op args => by
      rw [openTop]
      cases hn : openNeutral op args with
      | none => exact EquivExpr1.refl _
      | some e => simpa using openNeutral_equiv1 hn

/-! #### Lifting the value-restricted equivalence at single-value positions -/

/-- Argument-element lift: the `.args` context itself pins each head to a
singleton value or a halt, so a value-restricted head rewrite yields **full**
argument-list equivalence. -/
theorem EquivArgs.cons1 {e e' : Expr Op} {rest rest' : List (Expr Op)}
    (hh : EquivExpr1 (calls := calls) (creates := creates) e e')
    (ht : EquivArgs D rest rest') :
    EquivArgs D (e :: rest) (e' :: rest') := by
  intro funs V st r
  constructor
  · intro h
    cases h with
    | argsCons hrest he =>
        exact Step.argsCons ((ht funs V st _).mp hrest) (((hh funs _ _).1 _ _).mp he)
    | argsRestHalt hrest =>
        exact Step.argsRestHalt ((ht funs V st _).mp hrest)
    | argsHeadHalt hrest he =>
        exact Step.argsHeadHalt ((ht funs V st _).mp hrest) (((hh funs _ _).2 _).mp he)
  · intro h
    cases h with
    | argsCons hrest he =>
        exact Step.argsCons ((ht funs V st _).mpr hrest) (((hh funs _ _).1 _ _).mpr he)
    | argsRestHalt hrest =>
        exact Step.argsRestHalt ((ht funs V st _).mpr hrest)
    | argsHeadHalt hrest he =>
        exact Step.argsHeadHalt ((ht funs V st _).mpr hrest) (((hh funs _ _).2 _).mpr he)

/-- Singleton-`let` lift: `letVal` pins the right-hand side to exactly one
value, `letHalt` to a halt. -/
theorem EquivStmt.letDecl1_congr {x : Ident} {e e' : Expr Op}
    (h : EquivExpr1 (calls := calls) (creates := creates) e e') :
    EquivStmt D (.letDecl [x] (some e)) (.letDecl [x] (some e')) := by
  intro funs V st V' st' o
  constructor
  · intro hs
    cases hs with
    | letVal he hlen =>
        rename_i vals
        obtain ⟨v, rfl⟩ : ∃ v, vals = [v] := by
          cases vals with
          | nil => simp at hlen
          | cons a rest =>
              cases rest with
              | nil => exact ⟨a, rfl⟩
              | cons b r => simp at hlen
        exact Step.letVal (((h funs _ _).1 _ _).mp he) hlen
    | letHalt he => exact Step.letHalt (((h funs _ _).2 _).mp he)
  · intro hs
    cases hs with
    | letVal he hlen =>
        rename_i vals
        obtain ⟨v, rfl⟩ : ∃ v, vals = [v] := by
          cases vals with
          | nil => simp at hlen
          | cons a rest =>
              cases rest with
              | nil => exact ⟨a, rfl⟩
              | cons b r => simp at hlen
        exact Step.letVal (((h funs _ _).1 _ _).mpr he) hlen
    | letHalt he => exact Step.letHalt (((h funs _ _).2 _).mpr he)

/-- Singleton-`assign` lift. -/
theorem EquivStmt.assign1_congr {x : Ident} {e e' : Expr Op}
    (h : EquivExpr1 (calls := calls) (creates := creates) e e') :
    EquivStmt D (.assign [x] e) (.assign [x] e') := by
  intro funs V st V' st' o
  constructor
  · intro hs
    cases hs with
    | assignVal he hlen =>
        rename_i vals
        obtain ⟨v, rfl⟩ : ∃ v, vals = [v] := by
          cases vals with
          | nil => simp at hlen
          | cons a rest =>
              cases rest with
              | nil => exact ⟨a, rfl⟩
              | cons b r => simp at hlen
        exact Step.assignVal (((h funs _ _).1 _ _).mp he) hlen
    | assignHalt he => exact Step.assignHalt (((h funs _ _).2 _).mp he)
  · intro hs
    cases hs with
    | assignVal he hlen =>
        rename_i vals
        obtain ⟨v, rfl⟩ : ∃ v, vals = [v] := by
          cases vals with
          | nil => simp at hlen
          | cons a rest =>
              cases rest with
              | nil => exact ⟨a, rfl⟩
              | cons b r => simp at hlen
        exact Step.assignVal (((h funs _ _).1 _ _).mpr he) hlen
    | assignHalt he => exact Step.assignHalt (((h funs _ _).2 _).mpr he)

mutual

/-- Every expression is equivalent to its simplification. -/
theorem simplifyExpr_equiv : ∀ e : Expr Op, EquivExpr D e (simplifyExpr e)
  | .lit _ => EquivExpr.refl _
  | .var _ => EquivExpr.refl _
  | .builtin op args =>
      (EquivExpr.builtin_congr op (simplifyArgs_equivArgs args)).trans
        (simplifyBuiltin_equiv op (simplifyArgs args))
  | .call f args =>
      EquivExpr.call_congr f (simplifyArgs_equivArgs args)

/-- The argument list is equivalent to its simplification. Elements are
related only up to `EquivExpr1` (the open-operand rewrite), which the
argument context lifts to full list equivalence (`EquivArgs.cons1`). -/
theorem simplifyArgs_equivArgs : ∀ args : List (Expr Op),
    EquivArgs D args (simplifyArgs args)
  | [] => EquivArgs.refl _
  | e :: rest =>
      EquivArgs.cons1
        (EquivExpr1.trans (EquivExpr.toEquivExpr1 (simplifyExpr_equiv e)) (openTop_equiv1 _))
        (simplifyArgs_equivArgs rest)

end

mutual

/-- Every statement is equivalent to its simplification. -/
theorem simplifyStmt_equiv : ∀ s : Stmt Op, EquivStmt D s (simplifyStmt s)
  | .block body =>
      EquivBlock.of_stmts_funs (EquivStmts.of_forall₂ (simplifyStmts_forall2 body))
        (scopeRel_hoistSimplify body)
  | .funDef n ps rs body => funDef_equiv n ps rs body (simplifyStmts body)
  | .letDecl [x] (some e) =>
      (EquivStmt.letDecl_congr _ (simplifyExpr_equiv e)).trans
        (EquivStmt.letDecl1_congr (openTop_equiv1 _))
  | .letDecl [] (some e) => EquivStmt.letDecl_congr _ (simplifyExpr_equiv e)
  | .letDecl (_ :: _ :: _) (some e) => EquivStmt.letDecl_congr _ (simplifyExpr_equiv e)
  | .letDecl [_] none => EquivStmt.refl _
  | .letDecl [] none => EquivStmt.refl _
  | .letDecl (_ :: _ :: _) none => EquivStmt.refl _
  | .assign [x] e =>
      (EquivStmt.assign_congr _ (simplifyExpr_equiv e)).trans
        (EquivStmt.assign1_congr (openTop_equiv1 _))
  | .assign [] e => EquivStmt.assign_congr _ (simplifyExpr_equiv e)
  | .assign (_ :: _ :: _) e => EquivStmt.assign_congr _ (simplifyExpr_equiv e)
  | .cond c body =>
      (EquivStmt.cond_congr (simplifyExpr_equiv c)
        (EquivBlock.of_stmts_funs (EquivStmts.of_forall₂ (simplifyStmts_forall2 body))
          (scopeRel_hoistSimplify body))).trans
        (simplifyCond_equiv (simplifyExpr c) (simplifyStmts body))
  | .switch c cases dflt => by
      have hswitch : EquivStmt D (.switch c cases dflt)
          (.switch (simplifyExpr c) (simplifyCases cases) (simplifyDflt dflt)) := by
        apply EquivStmt.switch_congr (simplifyExpr_equiv c) (simplifyCases_forall2 cases)
        cases dflt with
        | none => exact EquivBlock.refl _
        | some b =>
            exact (EquivBlock.of_stmts_funs
              (EquivStmts.of_forall₂ (simplifyStmts_forall2 b))
              (scopeRel_hoistSimplify b))
      simpa only [simplifyStmt] using hswitch.trans
        (simplifySwitch_equiv (simplifyExpr c) (simplifyCases cases) (simplifyDflt dflt))
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
  | .letDecl [_] (some _) :: rest => scopeRel_hoistSimplify rest
  | .letDecl [] (some _) :: rest => scopeRel_hoistSimplify rest
  | .letDecl (_ :: _ :: _) (some _) :: rest => scopeRel_hoistSimplify rest
  | .letDecl [_] none :: rest => scopeRel_hoistSimplify rest
  | .letDecl [] none :: rest => scopeRel_hoistSimplify rest
  | .letDecl (_ :: _ :: _) none :: rest => scopeRel_hoistSimplify rest
  | .assign [_] _ :: rest => scopeRel_hoistSimplify rest
  | .assign [] _ :: rest => scopeRel_hoistSimplify rest
  | .assign (_ :: _ :: _) _ :: rest => scopeRel_hoistSimplify rest
  | .cond c body :: rest => by
      change ScopeRel D (hoist D rest)
        (hoist D (simplifyCond (simplifyExpr c) (simplifyStmts body) :: simplifyStmts rest))
      rw [hoist_simplifyCond_cons]
      exact scopeRel_hoistSimplify rest
  | .switch c cases dflt :: rest => by
      change ScopeRel D (hoist D rest)
        (hoist D (simplifySwitch (simplifyExpr c) (simplifyCases cases) (simplifyDflt dflt) ::
          simplifyStmts rest))
      rw [hoist_simplifySwitch_cons]
      exact scopeRel_hoistSimplify rest
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

/-- The **Simplify pass**: constant folding, neutral-element identities,
literal control-flow selection, and self-equality validator pruning over the
whole program (including function bodies; only a `for`-loop's `init` is left
untouched), bundled with its soundness proof. -/
def simplify : LocalPass D where
  run := simplifyStmts
  sound := blockEquiv

/-! ### Optimizing a whole object tree

`simplifyObject` runs the pass on **every** code block of an object tree — the
top (deploy) object and every nested sub-object (e.g. the `*_deployed` runtime of
a Solidity artifact) — leaving names and data segments intact. Each code block is
`EquivBlock`-equivalent to the original (`simplifyObject_codeBlock` +
`blockEquiv`), and the emitted bytecode is the verified compilation of the
result (`compileObject_correct`); the object-tree correctness statement is
`LocalPass.optimizeObject_compileObject_correct` in `ObjectPass`. -/

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
/-- The Core rule engine rewrites a typed right-neutral application. -/
example (x : Core.Var ["x"]) :
    Core.simplifyTerm (.builtin .add
      (⟨[.var x, .lit (.number 0)], rfl⟩ : Core.Args ["x"] 2)) = .atom (.var x) := by
  rcases x with ⟨name, hname⟩
  simp only [List.mem_singleton] at hname
  subst name
  simp [Core.simplifyTerm, Core.run, Core.first, Core.simplifyRules, Core.foldRule,
    Core.foldRewrite, Core.neutralRule, Core.neutralRewrite, Core.PureOp.toOp,
    Core.Args.emit, Core.Value.emit, Core.Var.emit, Core.ingestValue, asLits, pureFold,
    pureFn, neutral, litValue]
-- The production wrapper successfully composes ingestion with the Core rule.
#guard match simplifyExpr (.builtin .add [.var "x", .lit (.number 0)]) with
  | .var "x" => true
  | _ => false
-- Left neutral: `mul(1, x) = x`.
#guard match simplifyExpr (.builtin .mul [.lit (.number 1), .var "x"]) with
  | .var "x" => true
  | _ => false
-- Mask by all-ones is the identity: `and(x, 2²⁵⁶−1) = x`.
#guard match simplifyExpr
    (.builtin .and [.var "x", .lit (.number (2 ^ 256 - 1))]) with
  | .var "x" => true
  | _ => false
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
/-- A false literal branch is removed. -/
example : simplifyStmt (.cond (.lit (.number 0)) [.exprStmt (.builtin .stop [])]) =
    .block [] := rfl
/-- A condition that folds to true selects its body. -/
example : simplifyStmt (.cond (.builtin .add [.lit (.number 1), .lit (.number 2)])
    [.exprStmt (.builtin .stop [])]) = .block [.exprStmt (.builtin .stop [])] := rfl
-- A self-equality validator keeps condition evaluation but drops its branch.
#guard match simplifyStmt (.cond
    (.builtin .iszero [.builtin .eq [.var "x", .var "x"]])
    [.exprStmt (.builtin .revert [.lit (.number 0), .lit (.number 0)])]) with
  | .exprStmt (.builtin .pop
      [.builtin .iszero [.builtin .eq [.var "x", .var "x"]]]) => true
  | _ => false
-- Equality of different variables is not assumed.
#guard match simplifyStmt (.cond
    (.builtin .iszero [.builtin .eq [.var "x", .var "y"]]) [.break]) with
  | .cond (.builtin .iszero [.builtin .eq [.var "x", .var "y"]]) [.break] => true
  | _ => false
/-- A literal switch keeps only its selected case. -/
example : simplifyStmt (.switch (.lit (.number 2))
    [(.number 1, [.break]), (.number 2, [.leave])] (some [.continue])) =
    .block [.leave] := rfl
/-- A literal switch with no matching case selects its default. -/
example : simplifyStmt (.switch (.lit (.number 3))
    [(.number 1, [.break]), (.number 2, [.leave])] (some [.continue])) =
    .block [.continue] := rfl

end YulEvmCompiler.Optimizer
