import YulEvmCompiler.Optimizer.Spec.LocalPass
import YulEvmCompiler.Optimizer.Implementation.Frame
import YulEvmCompiler.Optimizer.Implementation.FunCongr
import YulEvmCompiler.Optimizer.Implementation.StorageForwardResolve
import YulEvmCompiler.Optimizer.Implementation.CoalesceCopies
import YulSemantics.Dialect.EVM
set_option warningAsError true
/-!
# YulEvmCompiler.Optimizer.Implementation.RejoinPairs

**Adjacent single-use expression rejoining** — the "expression rejoining" half
of issue #65's recommendation 3. After inlining and copy coalescing, the hot
loops bind an intermediate `x` to a producer `e` and then consume `x` exactly
once, in the very next statement, and never again. This pass folds `e` into
that single leaf position, deleting the binder and its live operand-stack
slot. Three **consumer forms** are handled:

* **adjacent binder** — `let x := e; let y := f(x)` → `let y := f[x:=e]`;
* **assignment right-hand side** — `let x := e; y := f(x)` → `y := f[x:=e]`
  (guarded by `x ≠ y`: for `y = x` the rewrite would assign to a variable
  whose declaration was just deleted);
* **if condition** — `let x := e; if c(x) { body }` → `if c[x:=e] { body }`.

```yul
let x := and(w, 1)
let y := iszero(eq(x, 0))
-- ⇒ let y := iszero(eq(and(w, 1), 0))
```

The two non-binder forms matter because solc's unoptimized IR binds *every*
if-condition and *every* assigned value to its own temp; joining them removes
a live stack slot per site. Measured on TickMath's 100-iteration sweep
benchmarks: ~30k gas from the if-condition consumer and ~8k from the
assignment consumer, with the double-`ISZERO` that the condition join exposes
cancelled by the existing `AsmPeephole` rule.

The producer must be call-free: nesting a call back under an expression would
undo `HoistCalls`/`FreshenCalls` and hide the site from `InlineCalls`
(measured: the `fls` fixtures regressed when calls rejoined). Each merged
binder costs a live operand-stack slot and a `DUP`, and the accumulated slots
hold helper bodies above the `liveMax` inlining gates.

For the two non-binder forms (assignment and if-condition), the producer must
additionally be storage-read-free: nesting an `sload`/`tload` inside the
consumer hides it from `ReuseValues`, whose fact recorder sees only binder-form
`let x := sload(k)`, costing a redundant warm SLOAD per execution (measured:
+17% on array-storage push loops).

Guards: the consumer position (`f` or the condition `c`) is a **pure-total
tree** (builtins with `pureTotalArity`, leaves that are literals or bound
variables) with exactly one occurrence of `x`; `x` is dead afterwards (and,
for the if form, unmentioned in `body`); the producer `e` is arbitrary (it may
read or write state or even halt). Moving `e` from its own statement into
`x`'s leaf position only commutes it past pure, total, state-independent
leaf/op evaluations, so the evaluation is unchanged; the depth story matches
`CoalesceCopies` (a live slot is removed, and `e`'s reads happen at the same
depth one statement later with nothing declared between).

The layout-free guards on `e` and the consumer keep the transform the
identity on unresolved `dataoffset`/`datasize` regions, which makes it
commute syntactically with object-layout resolution.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM

variable {calls : ExternalCalls} {creates : ExternalCreates}

local notation "D" => evmWithExternal calls creates

/-! ### The consumer-tree classifier -/

mutual

/-- Count occurrences of `x` in a pure-total consumer tree whose other leaves
are literals or `bound` variables; `none` marks an unusable tree. -/
def rjTree (bound : List Ident) (x : Ident) : Expr Op → Option Nat
  | .lit _ => some 0
  | .var z =>
      if z = x then some 1
      else if bound.contains z then some 0 else none
  | .builtin op args =>
      if pureTotalArity op == some args.length then rjTreeArgs bound x args
      else none
  | .call _ _ => none

def rjTreeArgs (bound : List Ident) (x : Ident) : List (Expr Op) → Option Nat
  | [] => some 0
  | a :: rest => do
      let n ← rjTree bound x a
      let m ← rjTreeArgs bound x rest
      pure (n + m)

end

mutual

/-- Substitute `e` for the `.var x` leaves (the guard ensures there is
exactly one). -/
def rjSubst (x : Ident) (e : Expr Op) : Expr Op → Expr Op
  | .var z => if z = x then e else .var z
  | .builtin op args => .builtin op (rjSubstArgs x e args)
  | t => t

def rjSubstArgs (x : Ident) (e : Expr Op) : List (Expr Op) → List (Expr Op)
  | [] => []
  | a :: rest => rjSubst x e a :: rjSubstArgs x e rest

end

mutual

/-- Operand-stack pressure of evaluating an expression: the maximum number of
pending values while it evaluates (arguments right-to-left). Rejoining must
keep this bounded — a deep merged tree makes every local read from inside it
a deeper `DUP`, which pushed `PoolLiquidity` past the stack-layout rescue when
unbounded (measured). -/
def rjDepth : Expr Op → Nat
  | .lit _ => 1
  | .var _ => 1
  | .builtin _ args => max 1 (rjDepthArgs args)
  | .call _ args => max 1 (rjDepthArgs args)

/-- Arguments evaluate right-to-left, so while argument `a` evaluates, the
arguments after it in source order are already on the stack. -/
def rjDepthArgs : List (Expr Op) → Nat
  | [] => 0
  | a :: rest => max (rest.length + rjDepth a) (rjDepthArgs rest)

end

/-- The rejoin depth budget (measured: unbounded rejoining broke
`PoolLiquidity`'s stack-layout rescue). -/
def rjDepthLimit : Nat := 8

mutual

/-- Storage-read ops anywhere in the tree: joining such a producer nests the
read where ReuseValues' binder-form fact recorder cannot see it, costing a
redundant warm SLOAD per execution (measured: array-storage push loops). -/
def exprReadsStorage : Expr Op → Bool
  | .lit _ => false
  | .var _ => false
  | .builtin .sload _ => true
  | .builtin .tload _ => true
  | .builtin _ args => argsReadStorage args
  | .call _ args => argsReadStorage args

/-- Does a storage-read op occur anywhere in the argument list? -/
def argsReadStorage : List (Expr Op) → Bool
  | [] => false
  | e :: rest => exprReadsStorage e || argsReadStorage rest
end

/-- The pair guard. -/
def rjPair (bound : List Ident) (x y : Ident) (e f : Expr Op)
    (rest : List (Stmt Op)) : Prop :=
  x ≠ y ∧ rjTree bound x f = some 1 ∧ stmtsMentions x rest = false ∧
    exprHasCall e = false ∧ rjDepth (rjSubst x e f) ≤ rjDepthLimit

instance (bound : List Ident) (x y : Ident) (e f : Expr Op)
    (rest : List (Stmt Op)) : Decidable (rjPair bound x y e f rest) := by
  unfold rjPair; infer_instance

/-- The assign-consumer pair guard: `let x := e; y := f(x)` merges into
`y := f[x:=e]`. `x ≠ y` is essential — for `y = x` the rewrite would assign to
a variable whose declaration was just deleted. -/
def rjAssignPair (bound : List Ident) (x y : Ident) (e f : Expr Op)
    (rest : List (Stmt Op)) : Prop :=
  x ≠ y ∧ rjTree bound x f = some 1 ∧ stmtsMentions x rest = false ∧
    exprHasCall e = false ∧ exprReadsStorage e = false ∧
    rjDepth (rjSubst x e f) ≤ rjDepthLimit

instance (bound : List Ident) (x y : Ident) (e f : Expr Op)
    (rest : List (Stmt Op)) : Decidable (rjAssignPair bound x y e f rest) := by
  unfold rjAssignPair; infer_instance

/-- The if-condition-consumer pair guard: `let x := e; if c(x) { body }` merges
into `if c[x:=e] { body }`. -/
def rjCondPair (bound : List Ident) (x : Ident) (e c : Expr Op)
    (body rest : List (Stmt Op)) : Prop :=
  rjTree bound x c = some 1 ∧ stmtsMentions x body = false ∧
    stmtsMentions x rest = false ∧ exprHasCall e = false ∧
    exprReadsStorage e = false ∧ rjDepth (rjSubst x e c) ≤ rjDepthLimit

instance (bound : List Ident) (x : Ident) (e c : Expr Op)
    (body rest : List (Stmt Op)) : Decidable (rjCondPair bound x e c body rest) := by
  unfold rjCondPair; infer_instance

/-! ### The transform -/

/-- One-level left-to-right rejoining; the merged binder is re-examined
against the next statement, so producer chains fold into one tree. -/
def rjPairs (bound : List Ident) : List (Stmt Op) → List (Stmt Op)
  | .letDecl [x] (some e) :: .letDecl [y] (some f) :: rest =>
      if rjPair bound x y e f rest then
        rjPairs bound (.letDecl [y] (some (rjSubst x e f)) :: rest)
      else
        .letDecl [x] (some e) ::
          rjPairs (x :: bound) (.letDecl [y] (some f) :: rest)
  | .letDecl [x] (some e) :: .assign [y] f :: rest =>
      if rjAssignPair bound x y e f rest then
        rjPairs bound (.assign [y] (rjSubst x e f) :: rest)
      else
        .letDecl [x] (some e) ::
          rjPairs (x :: bound) (.assign [y] f :: rest)
  | .letDecl [x] (some e) :: .cond c body :: rest =>
      if rjCondPair bound x e c body rest then
        rjPairs bound (.cond (rjSubst x e c) body :: rest)
      else
        .letDecl [x] (some e) ::
          rjPairs (x :: bound) (.cond c body :: rest)
  | .letDecl xs v :: rest => .letDecl xs v :: rjPairs (xs ++ bound) rest
  | s :: rest => s :: rjPairs bound rest
  | [] => []
  termination_by ss => ss.length
  decreasing_by all_goals simp +arith

mutual

/-- Recurse into every sub-block, rejoining at each sequence level. Each
sequence starts from an **empty** bound set — only variables declared by
earlier `let`s of the same sequence count as safe sibling leaves, because
those are bound in every execution that reaches the pair, no matter how
ill-scoped the ambient environment is (the pointwise spec quantifies over
arbitrary environments). A `for` loop's `init` is left untouched. -/
def rjStmt : Stmt Op → Stmt Op
  | .block body => .block (rjPairs [] (rjStmts body))
  | .funDef n ps rs body => .funDef n ps rs (rjPairs [] (rjStmts body))
  | .cond c body => .cond c (rjPairs [] (rjStmts body))
  | .switch c cases dflt => .switch c (rjCases cases) (rjDflt dflt)
  | .forLoop init c post body =>
      .forLoop init c (rjPairs [] (rjStmts post)) (rjPairs [] (rjStmts body))
  | s => s

def rjStmts : List (Stmt Op) → List (Stmt Op)
  | [] => []
  | s :: rest => rjStmt s :: rjStmts rest

def rjCases : List (Literal × Block Op) → List (Literal × Block Op)
  | [] => []
  | (l, b) :: rest => (l, rjPairs [] (rjStmts b)) :: rjCases rest

def rjDflt : Option (Block Op) → Option (Block Op)
  | none => none
  | some b => some (rjPairs [] (rjStmts b))

end

/-- Rejoin adjacent single-use pure pairs in a top-level block. The whole
block must be free of unresolved `dataoffset`/`datasize`: layout resolution
is then the identity on both the input and the output, which is what makes
the pass an object-path stage (the `StorageForward` recipe). -/
def rejoinPairsBlock (b : Block Op) : Block Op :=
  if storageLayoutFreeStmts b then rjPairs [] (rjStmts b) else b

/-! ### Guard facts -/

theorem pure_stable {op : Op} {n : Nat} (h : pureTotalArity op = some n) :
    stableTotalArity op = some n := by
  cases op <;> simp_all [pureTotalArity, stableTotalArity]

theorem rjTreeArgs_cons_inv {bound : List Ident} {x : Ident} {a : Expr Op}
    {rest : List (Expr Op)} {k : Nat}
    (h : rjTreeArgs bound x (a :: rest) = some k) :
    ∃ n m, rjTree bound x a = some n ∧ rjTreeArgs bound x rest = some m ∧
      n + m = k := by
  unfold rjTreeArgs at h
  cases ha : rjTree bound x a with
  | none => rw [ha] at h; cases h
  | some n =>
      rw [ha] at h
      cases hr : rjTreeArgs bound x rest with
      | none => rw [hr] at h; cases h
      | some m =>
          rw [hr] at h
          injection h with h
          exact ⟨n, m, rfl, rfl, h⟩

mutual

theorem rjTree_zero_mentions {bound : List Ident} {x : Ident} :
    ∀ t : Expr Op, rjTree bound x t = some 0 → exprMentions x t = false
  | .lit _, _ => rfl
  | .var z, h => by
      unfold rjTree at h
      by_cases hz : z = x
      · rw [if_pos hz] at h; cases h
      · simp only [exprMentions]
        exact decide_eq_false fun hxz => hz hxz.symm
  | .builtin op args, h => by
      unfold rjTree at h
      split at h
      · exact rjTreeArgs_zero_mentions args h
      · cases h
  | .call _ _, h => by unfold rjTree at h; cases h

theorem rjTreeArgs_zero_mentions {bound : List Ident} {x : Ident} :
    ∀ args : List (Expr Op), rjTreeArgs bound x args = some 0 →
      argsMentions x args = false
  | [], _ => rfl
  | a :: rest, h => by
      obtain ⟨n, m, ha, hr, hnm⟩ := rjTreeArgs_cons_inv h
      obtain ⟨rfl, rfl⟩ : n = 0 ∧ m = 0 := by omega
      simp [argsMentions, rjTree_zero_mentions a ha,
        rjTreeArgs_zero_mentions rest hr]

end

mutual

theorem rjTree_zero_alwaysEval {bound : List Ident} {x : Ident} :
    ∀ t : Expr Op, rjTree bound x t = some 0 → alwaysEval bound t = true
  | .lit _, _ => rfl
  | .var z, h => by
      unfold rjTree at h
      by_cases hz : z = x
      · rw [if_pos hz] at h; cases h
      · rw [if_neg hz] at h
        by_cases hc : bound.contains z
        · simpa [alwaysEval] using hc
        · rw [if_neg hc] at h; cases h
  | .builtin op args, h => by
      unfold rjTree at h
      split at h
      · next har =>
          have har' : pureTotalArity op = some args.length := by simpa using har
          simp only [alwaysEval, Bool.and_eq_true]
          exact ⟨by simp [pure_stable har'],
            rjTreeArgs_zero_alwaysEval args h⟩
      · cases h
  | .call _ _, h => by unfold rjTree at h; cases h

theorem rjTreeArgs_zero_alwaysEval {bound : List Ident} {x : Ident} :
    ∀ args : List (Expr Op), rjTreeArgs bound x args = some 0 →
      alwaysEvalArgs bound args = true
  | [], _ => rfl
  | a :: rest, h => by
      obtain ⟨n, m, ha, hr, hnm⟩ := rjTreeArgs_cons_inv h
      obtain ⟨rfl, rfl⟩ : n = 0 ∧ m = 0 := by omega
      simp only [alwaysEvalArgs, Bool.and_eq_true]
      exact ⟨rjTree_zero_alwaysEval a ha, rjTreeArgs_zero_alwaysEval rest hr⟩

end

mutual

theorem rjSubst_not_mentions {x : Ident} {e : Expr Op} :
    ∀ t : Expr Op, exprMentions x t = false → rjSubst x e t = t
  | .lit _, _ => rfl
  | .var z, h => by
      unfold rjSubst
      rw [if_neg]
      intro hz
      rw [exprMentions] at h
      simp [hz] at h
  | .builtin op args, h => by
      unfold rjSubst
      rw [rjSubstArgs_not_mentions args (by simpa [exprMentions] using h)]
  | .call _ _, _ => rfl

theorem rjSubstArgs_not_mentions {x : Ident} {e : Expr Op} :
    ∀ args : List (Expr Op), argsMentions x args = false →
      rjSubstArgs x e args = args
  | [], _ => rfl
  | a :: rest, h => by
      rw [argsMentions, Bool.or_eq_false_iff] at h
      unfold rjSubstArgs
      rw [rjSubst_not_mentions a h.1, rjSubstArgs_not_mentions rest h.2]

end

/-! ### Count-0 pieces: inversion and transport

A count-0 subtree is a pure-total expression over literals and non-`x`
variables: every evaluation yields exactly one value with the state
unchanged, and the same value is obtained under any environment agreeing on
its mentioned variables, at any state. -/

mutual

theorem rjT0_vals {bound : List Ident} {x : Ident} :
    ∀ t : Expr Op, rjTree bound x t = some 0 →
    ∀ {funs : FunEnv D} {W : VEnv D} {stA st1 : EvmState} {vs : List U256},
      Step D funs W stA (.expr t) (.eres (.vals vs st1)) →
      ∃ w, vs = [w] ∧ st1 = stA ∧
        ∀ (W' : VEnv D) (stB : EvmState),
          (∀ z, exprMentions z t = true → VEnv.get W' z = VEnv.get W z) →
          Step D funs W' stB (.expr t) (.eres (.vals [w] stB))
  | .lit l, _ => by
      intro hstep
      cases hstep with
      | lit => exact ⟨_, rfl, rfl, fun W' stB _ => Step.lit⟩
  | .var z, h => by
      intro hstep
      cases hstep with
      | var hv =>
          refine ⟨_, rfl, rfl, fun W' stB hag => ?_⟩
          exact Step.var (by rw [hag z (by simp [exprMentions])]; exact hv)
  | .builtin op args, h => by
      intro hstep
      have har : pureTotalArity op = some args.length := by
        unfold rjTree at h
        split at h
        · next har => simpa using har
        · cases h
      have hargs0 : rjTreeArgs bound x args = some 0 := by
        unfold rjTree at h
        split at h
        · exact h
        · cases h
      cases hstep with
      | builtinOk hargs hop =>
          obtain ⟨hst, hlen, htr⟩ := rjT0_args_vals args hargs0 hargs
          subst hst
          obtain ⟨w, hw⟩ := pureTotalArity_pureFn har _ hlen
          have hr := pureFn_builtin_inv hw hop
          injection hr with h1 h2
          subst h1; subst h2
          refine ⟨w, rfl, rfl, fun W' stB hag => ?_⟩
          refine Step.builtinOk (htr W' stB ?_) (pureFn_builtin hw stB)
          intro z hz
          exact hag z (by simpa [exprMentions] using hz)
  | .call _ _, h => by unfold rjTree at h; cases h

theorem rjT0_nohalt {bound : List Ident} {x : Ident} :
    ∀ t : Expr Op, rjTree bound x t = some 0 →
    ∀ {funs : FunEnv D} {W : VEnv D} {stA sth : EvmState},
      ¬ Step D funs W stA (.expr t) (.eres (.halt sth))
  | .lit _, _ => by intro hstep; cases hstep
  | .var _, _ => by intro hstep; cases hstep
  | .builtin op args, h => by
      intro hstep
      have har : pureTotalArity op = some args.length := by
        unfold rjTree at h
        split at h
        · next har => simpa using har
        · cases h
      have hargs0 : rjTreeArgs bound x args = some 0 := by
        unfold rjTree at h
        split at h
        · exact h
        · cases h
      cases hstep with
      | builtinHalt hargs hop =>
          obtain ⟨hst, hlen, -⟩ := rjT0_args_vals args hargs0 hargs
          obtain ⟨w, hw⟩ := pureTotalArity_pureFn har _ hlen
          exact absurd (pureFn_builtin_inv hw hop) (by simp)
      | builtinArgsHalt hargs =>
          exact absurd hargs (rjT0_args_nohalt args hargs0)
  | .call _ _, h => by unfold rjTree at h; cases h

theorem rjT0_args_vals {bound : List Ident} {x : Ident} :
    ∀ args : List (Expr Op), rjTreeArgs bound x args = some 0 →
    ∀ {funs : FunEnv D} {W : VEnv D} {stA st1 : EvmState} {vs : List U256},
      Step D funs W stA (.args args) (.eres (.vals vs st1)) →
      st1 = stA ∧ vs.length = args.length ∧
        ∀ (W' : VEnv D) (stB : EvmState),
          (∀ z, argsMentions z args = true → VEnv.get W' z = VEnv.get W z) →
          Step D funs W' stB (.args args) (.eres (.vals vs stB))
  | [], _ => by
      intro hstep
      cases hstep with
      | argsNil => exact ⟨rfl, rfl, fun _ _ _ => Step.argsNil⟩
  | a :: rest, h => by
      intro hstep
      obtain ⟨n, m, ha, hr, hnm⟩ := rjTreeArgs_cons_inv h
      obtain ⟨rfl, rfl⟩ : n = 0 ∧ m = 0 := by omega
      cases hstep with
      | argsCons hrest hhead =>
          obtain ⟨hst1, hlen, htr⟩ := rjT0_args_vals rest hr hrest
          subst hst1
          obtain ⟨w, hvs, hst2, hwtr⟩ := rjT0_vals a ha hhead
          subst hst2
          obtain rfl : _ = w := by injection hvs
          refine ⟨rfl, by simp [hlen], fun W' stB hag => ?_⟩
          refine Step.argsCons (htr W' stB ?_) (hwtr W' stB ?_)
          · intro z hz
            exact hag z (by simp [argsMentions, hz])
          · intro z hz
            exact hag z (by simp [argsMentions, hz])

theorem rjT0_args_nohalt {bound : List Ident} {x : Ident} :
    ∀ args : List (Expr Op), rjTreeArgs bound x args = some 0 →
    ∀ {funs : FunEnv D} {W : VEnv D} {stA sth : EvmState},
      ¬ Step D funs W stA (.args args) (.eres (.halt sth))
  | [], _ => by intro hstep; cases hstep
  | a :: rest, h => by
      intro hstep
      obtain ⟨n, m, ha, hr, hnm⟩ := rjTreeArgs_cons_inv h
      obtain ⟨rfl, rfl⟩ : n = 0 ∧ m = 0 := by omega
      cases hstep with
      | argsRestHalt hrest =>
          exact absurd hrest (rjT0_args_nohalt rest hr)
      | argsHeadHalt hrest hhead =>
          exact absurd hhead (rjT0_nohalt a ha)

end

/-! ### The carrier: forward substitution -/

/-- Reads of non-`x` variables ignore the inserted `(x, v)`. -/
theorem get_skip {z x : Ident} (hz : z ≠ x) (v : U256) (V : VEnv D) :
    VEnv.get ((x, v) :: V) z = VEnv.get V z := by
  unfold VEnv.get
  rw [List.find?_cons_of_neg]
  simp only [decide_eq_true_eq]
  exact fun hc => hz hc.symm

mutual

/-- Forward: a run of the consumer tree over the bound copy transplants to a
run of the substituted tree, evaluating `e` exactly once in the copy's leaf
position. -/
theorem rjT1_fwd {bound : List Ident} {x : Ident} {e : Expr Op}
    {funs : FunEnv D} {V : VEnv D} {st st1 : EvmState} {v : U256} :
    ∀ t : Expr Op, rjTree bound x t = some 1 →
    ∀ {st2 : EvmState} {vs : List U256},
      Step D funs V st (.expr e) (.eres (.vals [v] st1)) →
      Step D funs ((x, v) :: V) st1 (.expr t) (.eres (.vals vs st2)) →
      ∃ w, vs = [w] ∧ st2 = st1 ∧
        Step D funs V st (.expr (rjSubst x e t)) (.eres (.vals [w] st1))
  | .lit _, h => by unfold rjTree at h; cases h
  | .var z, h => by
      intro he hstep
      have hz : z = x := by
        unfold rjTree at h
        by_cases hz : z = x
        · exact hz
        · rw [if_neg hz] at h
          by_cases hc : bound.contains z
          · rw [if_pos hc] at h; cases h
          · rw [if_neg hc] at h; cases h
      subst hz
      cases hstep with
      | var hv =>
          have hg : VEnv.get ((z, v) :: V) z = some v := by simp [VEnv.get]
          rw [hg] at hv
          injection hv with hv
          subst hv
          refine ⟨v, rfl, rfl, ?_⟩
          unfold rjSubst
          rw [if_pos rfl]
          exact he
  | .builtin op args, h => by
      intro he hstep
      have har : pureTotalArity op = some args.length := by
        unfold rjTree at h
        split at h
        · next har => simpa using har
        · cases h
      have hargs1 : rjTreeArgs bound x args = some 1 := by
        unfold rjTree at h
        split at h
        · exact h
        · cases h
      cases hstep with
      | builtinOk hargs hop =>
          obtain ⟨hst, hlen, htgt⟩ := rjA1_fwd args hargs1 he hargs
          subst hst
          obtain ⟨w, hw⟩ := pureTotalArity_pureFn har _ hlen
          have hr := pureFn_builtin_inv hw hop
          injection hr with h1 h2
          subst h1; subst h2
          refine ⟨w, rfl, rfl, ?_⟩
          unfold rjSubst
          exact Step.builtinOk htgt (pureFn_builtin hw _)
  | .call _ _, h => by unfold rjTree at h; cases h

theorem rjA1_fwd {bound : List Ident} {x : Ident} {e : Expr Op}
    {funs : FunEnv D} {V : VEnv D} {st st1 : EvmState} {v : U256} :
    ∀ args : List (Expr Op), rjTreeArgs bound x args = some 1 →
    ∀ {st2 : EvmState} {vs : List U256},
      Step D funs V st (.expr e) (.eres (.vals [v] st1)) →
      Step D funs ((x, v) :: V) st1 (.args args) (.eres (.vals vs st2)) →
      st2 = st1 ∧ vs.length = args.length ∧
        Step D funs V st (.args (rjSubstArgs x e args)) (.eres (.vals vs st1))
  | [], h => by intro hstep; cases h
  | a :: rest, h => by
      intro he hstep
      obtain ⟨n, m, ha, hr, hnm⟩ := rjTreeArgs_cons_inv h
      rcases n with _ | n
      · -- head count 0: the carrier is in the tail (evaluated first)
        have hm1 : m = 1 := by omega
        subst hm1
        cases hstep with
        | argsCons hrest hhead =>
            obtain ⟨hst, hlen, htgt⟩ := rjA1_fwd rest hr he hrest
            subst hst
            obtain ⟨w, hvs, hst2, hwtr⟩ := rjT0_vals a ha hhead
            subst hst2
            obtain rfl : _ = w := by injection hvs
            refine ⟨rfl, by simp [hlen], ?_⟩
            unfold rjSubstArgs
            rw [rjSubst_not_mentions a (rjTree_zero_mentions a ha)]
            refine Step.argsCons htgt (hwtr V _ ?_)
            intro z hz
            refine (get_skip ?_ v V).symm
            intro hzx
            subst hzx
            rw [rjTree_zero_mentions a ha] at hz
            cases hz
      · -- head count ≥ 1: with sum 1 the head carries the single `x`
        have hn0 : n = 0 := by omega
        subst hn0
        have hm0 : m = 0 := by omega
        subst hm0
        cases hstep with
        | argsCons hrest hhead =>
            obtain ⟨hst, hlen, htr⟩ := rjT0_args_vals rest hr hrest
            subst hst
            obtain ⟨w, hvs, hst2, htgt⟩ := rjT1_fwd a ha he hhead
            subst hst2
            obtain rfl : _ = w := by injection hvs
            refine ⟨rfl, by simp [hlen], ?_⟩
            unfold rjSubstArgs
            rw [rjSubstArgs_not_mentions rest (rjTreeArgs_zero_mentions rest hr)]
            refine Step.argsCons (htr V st ?_) htgt
            intro z hz
            refine (get_skip ?_ v V).symm
            intro hzx
            subst hzx
            rw [rjTreeArgs_zero_mentions rest hr] at hz
            cases hz


end

mutual

/-- The carrier tree cannot halt once `e` has evaluated. -/
theorem rjT1_fwd_nohalt {bound : List Ident} {x : Ident} {e : Expr Op}
    {funs : FunEnv D} {V : VEnv D} {st st1 : EvmState} {v : U256} :
    ∀ t : Expr Op, rjTree bound x t = some 1 →
    ∀ {sth : EvmState},
      Step D funs V st (.expr e) (.eres (.vals [v] st1)) →
      ¬ Step D funs ((x, v) :: V) st1 (.expr t) (.eres (.halt sth))
  | .lit _, h => by unfold rjTree at h; cases h
  | .var z, h => by intro _ hstep; cases hstep
  | .builtin op args, h => by
      intro he hstep
      have har : pureTotalArity op = some args.length := by
        unfold rjTree at h
        split at h
        · next har => simpa using har
        · cases h
      have hargs1 : rjTreeArgs bound x args = some 1 := by
        unfold rjTree at h
        split at h
        · exact h
        · cases h
      cases hstep with
      | builtinHalt hargs hop =>
          obtain ⟨hst, hlen, -⟩ := rjA1_fwd args hargs1 he hargs
          obtain ⟨w, hw⟩ := pureTotalArity_pureFn har _ hlen
          exact absurd (pureFn_builtin_inv hw hop) (by simp)
      | builtinArgsHalt hargs =>
          exact absurd hargs (fun hh => rjA1_fwd_nohalt args hargs1 he hh)
  | .call _ _, h => by unfold rjTree at h; cases h

theorem rjA1_fwd_nohalt {bound : List Ident} {x : Ident} {e : Expr Op}
    {funs : FunEnv D} {V : VEnv D} {st st1 : EvmState} {v : U256} :
    ∀ args : List (Expr Op), rjTreeArgs bound x args = some 1 →
    ∀ {sth : EvmState},
      Step D funs V st (.expr e) (.eres (.vals [v] st1)) →
      ¬ Step D funs ((x, v) :: V) st1 (.args args) (.eres (.halt sth))
  | [], h => by intro hstep; cases h
  | a :: rest, h => by
      intro he hstep
      obtain ⟨n, m, ha, hr, hnm⟩ := rjTreeArgs_cons_inv h
      rcases n with _ | n
      · have hm1 : m = 1 := by omega
        subst hm1
        cases hstep with
        | argsRestHalt hrest =>
            exact absurd hrest (fun hh => rjA1_fwd_nohalt rest hr he hh)
        | argsHeadHalt hrest hhead =>
            exact absurd hhead (rjT0_nohalt a ha)
      · have hn0 : n = 0 := by omega
        subst hn0
        have hm0 : m = 0 := by omega
        subst hm0
        cases hstep with
        | argsRestHalt hrest =>
            exact absurd hrest (rjT0_args_nohalt rest hr)
        | argsHeadHalt hrest hhead =>
            obtain ⟨hst, -, -⟩ := rjT0_args_vals rest hr hrest
            subst hst
            exact absurd hhead (fun hh => rjT1_fwd_nohalt a ha he hh)


end


/-! ### The carrier: halting producer, and the backward direction -/

mutual

/-- If `e` halts, the substituted tree halts identically: the pieces to the
right of the leaf are total and state-preserving, then `e`'s halt
propagates. -/
theorem rjT1_halt {bound : List Ident} {x : Ident} {e : Expr Op}
    {funs : FunEnv D} {V : VEnv D} {st sth : EvmState}
    (hb : BoundOK V bound)
    (heh : Step D funs V st (.expr e) (.eres (.halt sth))) :
    ∀ t : Expr Op, rjTree bound x t = some 1 →
      Step D funs V st (.expr (rjSubst x e t)) (.eres (.halt sth))
  | .lit _, h => by unfold rjTree at h; cases h
  | .var z, h => by
      have hz : z = x := by
        unfold rjTree at h
        by_cases hz : z = x
        · exact hz
        · rw [if_neg hz] at h
          by_cases hc : bound.contains z
          · rw [if_pos hc] at h; cases h
          · rw [if_neg hc] at h; cases h
      subst hz
      unfold rjSubst
      rw [if_pos rfl]
      exact heh
  | .builtin op args, h => by
      have hargs1 : rjTreeArgs bound x args = some 1 := by
        unfold rjTree at h
        split at h
        · exact h
        · cases h
      unfold rjSubst
      exact Step.builtinArgsHalt (rjA1_halt hb heh args hargs1)
  | .call _ _, h => by unfold rjTree at h; cases h

theorem rjA1_halt {bound : List Ident} {x : Ident} {e : Expr Op}
    {funs : FunEnv D} {V : VEnv D} {st sth : EvmState}
    (hb : BoundOK V bound)
    (heh : Step D funs V st (.expr e) (.eres (.halt sth))) :
    ∀ args : List (Expr Op), rjTreeArgs bound x args = some 1 →
      Step D funs V st (.args (rjSubstArgs x e args)) (.eres (.halt sth))
  | [], h => by cases h
  | a :: rest, h => by
      obtain ⟨n, m, ha, hr, hnm⟩ := rjTreeArgs_cons_inv h
      rcases n with _ | n
      · -- carrier in the tail, which evaluates first and halts
        have hm1 : m = 1 := by omega
        subst hm1
        unfold rjSubstArgs
        rw [rjSubst_not_mentions a (rjTree_zero_mentions a ha)]
        exact Step.argsRestHalt (rjA1_halt hb heh rest hr)
      · -- carrier is the head: the pure tail evaluates, then the head halts
        have hn0 : n = 0 := by omega
        subst hn0
        have hm0 : m = 0 := by omega
        subst hm0
        obtain ⟨vs, hvs, -⟩ := dcEvalArgsRun hb funs st rest
          (rjTreeArgs_zero_alwaysEval rest hr)
        unfold rjSubstArgs
        rw [rjSubstArgs_not_mentions rest (rjTreeArgs_zero_mentions rest hr)]
        exact Step.argsHeadHalt hvs (rjT1_halt hb heh a ha)

end

mutual

/-- Backward: a successful run of the substituted tree splits into `e`'s run
and the original tree's run over the bound copy. -/
theorem rjT1_bwd {bound : List Ident} {x : Ident} {e : Expr Op}
    {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    (hb : BoundOK V bound) :
    ∀ t : Expr Op, rjTree bound x t = some 1 →
    ∀ {stw : EvmState} {ws : List U256}, ws.length = 1 →
      Step D funs V st (.expr (rjSubst x e t)) (.eres (.vals ws stw)) →
      ∃ w v st1, ws = [w] ∧ stw = st1 ∧
        Step D funs V st (.expr e) (.eres (.vals [v] st1)) ∧
        Step D funs ((x, v) :: V) st1 (.expr t) (.eres (.vals [w] st1))
  | .lit _, h => by unfold rjTree at h; cases h
  | .var z, h => by
      intro hws hstep
      rename_i stw ws
      have hz : z = x := by
        unfold rjTree at h
        by_cases hz : z = x
        · exact hz
        · rw [if_neg hz] at h
          by_cases hc : bound.contains z
          · rw [if_pos hc] at h; cases h
          · rw [if_neg hc] at h; cases h
      subst hz
      rw [rjSubst, if_pos rfl] at hstep
      obtain ⟨w, rfl⟩ : ∃ w, ws = [w] := by
        cases ws with
        | nil => simp at hws
        | cons a t =>
            cases t with
            | nil => exact ⟨a, rfl⟩
            | cons b t2 => simp at hws
      exact ⟨w, w, stw, rfl, rfl, hstep,
        Step.var (by simp [VEnv.get])⟩
  | .builtin op args, h => by
      intro hws hstep
      have har : pureTotalArity op = some args.length := by
        unfold rjTree at h
        split at h
        · next har => simpa using har
        · cases h
      have hargs1 : rjTreeArgs bound x args = some 1 := by
        unfold rjTree at h
        split at h
        · exact h
        · cases h
      simp only [rjSubst] at hstep
      cases hstep with
      | builtinOk hargs hop =>
          obtain ⟨v, st1, rfl, hlen, he, hsrc⟩ := rjA1_bwd hb args hargs1 hargs
          obtain ⟨w, hw⟩ := pureTotalArity_pureFn har _ hlen
          have hr := pureFn_builtin_inv hw hop
          injection hr with h1 h2
          subst h1; subst h2
          exact ⟨w, v, _, rfl, rfl, he, Step.builtinOk hsrc (pureFn_builtin hw _)⟩
  | .call _ _, h => by unfold rjTree at h; cases h

theorem rjA1_bwd {bound : List Ident} {x : Ident} {e : Expr Op}
    {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    (hb : BoundOK V bound) :
    ∀ args : List (Expr Op), rjTreeArgs bound x args = some 1 →
    ∀ {stw : EvmState} {ws : List U256},
      Step D funs V st (.args (rjSubstArgs x e args)) (.eres (.vals ws stw)) →
      ∃ v st1, stw = st1 ∧ ws.length = args.length ∧
        Step D funs V st (.expr e) (.eres (.vals [v] st1)) ∧
        Step D funs ((x, v) :: V) st1 (.args args) (.eres (.vals ws st1))
  | [], h => by intro _; cases h
  | a :: rest, h => by
      intro hstep
      obtain ⟨n, m, ha, hr, hnm⟩ := rjTreeArgs_cons_inv h
      simp only [rjSubstArgs] at hstep
      rcases n with _ | n
      · -- carrier in the tail
        have hm1 : m = 1 := by omega
        subst hm1
        rw [rjSubst_not_mentions a (rjTree_zero_mentions a ha)] at hstep
        cases hstep with
        | argsCons hrest hhead =>
            obtain ⟨v, st1, rfl, hlen, he, hsrc⟩ := rjA1_bwd hb rest hr hrest
            obtain ⟨hv, hvs, hst2, htr⟩ := rjT0_vals a ha hhead
            subst hst2
            injection hvs with hveq
            subst hveq
            refine ⟨v, _, rfl, by simp [hlen], he,
              Step.argsCons hsrc (htr ((x, v) :: V) _ ?_)⟩
            intro z hz
            refine (get_skip ?_ v V)
            intro hzx
            subst hzx
            rw [rjTree_zero_mentions a ha] at hz
            cases hz
      · -- carrier is the head
        have hn0 : n = 0 := by omega
        subst hn0
        have hm0 : m = 0 := by omega
        subst hm0
        rw [rjSubstArgs_not_mentions rest (rjTreeArgs_zero_mentions rest hr)]
          at hstep
        cases hstep with
        | argsCons hrest hhead =>
            obtain ⟨hst, hlen0, htr⟩ := rjT0_args_vals rest hr hrest
            subst hst
            obtain ⟨w, v, st1, hws, hsth, he, hsrc⟩ :=
              rjT1_bwd hb a ha rfl hhead
            subst hsth
            injection hws with hweq
            subst hweq
            refine ⟨v, _, rfl, by simp [hlen0], he,
              Step.argsCons (htr ((x, v) :: V) _ ?_) hsrc⟩
            intro z hz
            refine (get_skip ?_ v V)
            intro hzx
            subst hzx
            rw [rjTreeArgs_zero_mentions rest hr] at hz
            cases hz

end

mutual

/-- Backward: a halting run of the substituted tree is `e`'s halt. -/
theorem rjT1_bwd_halt {bound : List Ident} {x : Ident} {e : Expr Op}
    {funs : FunEnv D} {V : VEnv D} {st sth : EvmState}
    (hb : BoundOK V bound) :
    ∀ t : Expr Op, rjTree bound x t = some 1 →
      Step D funs V st (.expr (rjSubst x e t)) (.eres (.halt sth)) →
      Step D funs V st (.expr e) (.eres (.halt sth))
  | .lit _, h => by unfold rjTree at h; cases h
  | .var z, h => by
      intro hstep
      have hz : z = x := by
        unfold rjTree at h
        by_cases hz : z = x
        · exact hz
        · rw [if_neg hz] at h
          by_cases hc : bound.contains z
          · rw [if_pos hc] at h; cases h
          · rw [if_neg hc] at h; cases h
      subst hz
      rw [rjSubst, if_pos rfl] at hstep
      exact hstep
  | .builtin op args, h => by
      intro hstep
      have har : pureTotalArity op = some args.length := by
        unfold rjTree at h
        split at h
        · next har => simpa using har
        · cases h
      have hargs1 : rjTreeArgs bound x args = some 1 := by
        unfold rjTree at h
        split at h
        · exact h
        · cases h
      simp only [rjSubst] at hstep
      cases hstep with
      | builtinHalt hargs hop =>
          obtain ⟨v, st1, rfl, hlen, -, -⟩ := rjA1_bwd hb args hargs1 hargs
          obtain ⟨w, hw⟩ := pureTotalArity_pureFn har _ hlen
          exact absurd (pureFn_builtin_inv hw hop) (by simp)
      | builtinArgsHalt hargs =>
          exact rjA1_bwd_halt hb args hargs1 hargs
  | .call _ _, h => by unfold rjTree at h; cases h

theorem rjA1_bwd_halt {bound : List Ident} {x : Ident} {e : Expr Op}
    {funs : FunEnv D} {V : VEnv D} {st sth : EvmState}
    (hb : BoundOK V bound) :
    ∀ args : List (Expr Op), rjTreeArgs bound x args = some 1 →
      Step D funs V st (.args (rjSubstArgs x e args)) (.eres (.halt sth)) →
      Step D funs V st (.expr e) (.eres (.halt sth))
  | [], h => by intro hstep; cases h
  | a :: rest, h => by
      intro hstep
      obtain ⟨n, m, ha, hr, hnm⟩ := rjTreeArgs_cons_inv h
      simp only [rjSubstArgs] at hstep
      rcases n with _ | n
      · have hm1 : m = 1 := by omega
        subst hm1
        rw [rjSubst_not_mentions a (rjTree_zero_mentions a ha)] at hstep
        cases hstep with
        | argsRestHalt hrest =>
            exact rjA1_bwd_halt hb rest hr hrest
        | argsHeadHalt hrest hhead =>
            exact absurd hhead (rjT0_nohalt a ha)
      · have hn0 : n = 0 := by omega
        subst hn0
        have hm0 : m = 0 := by omega
        subst hm0
        rw [rjSubstArgs_not_mentions rest (rjTreeArgs_zero_mentions rest hr)]
          at hstep
        cases hstep with
        | argsRestHalt hrest =>
            exact absurd hrest (rjT0_args_nohalt rest hr)
        | argsHeadHalt hrest hhead =>
            obtain ⟨hst, -, -⟩ := rjT0_args_vals rest hr hrest
            subst hst
            exact rjT1_bwd_halt hb a ha hhead

end

/-! ### Statement-level simulation -/

private theorem rjLetInv {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    {x : Ident} {rhs : Option (Expr Op)} {V' : VEnv D} {st' : EvmState} {o : Outcome}
    (h : Step D funs V st (.stmt (.letDecl [x] rhs)) (.sres V' st' o)) :
    (∃ v, V' = (x, v) :: V ∧ o = .normal ∧
      ((rhs = none ∧ v = (evmWithExternal calls creates).zero ∧ st' = st) ∨
       (∃ e, rhs = some e ∧
         Step D funs V st (.expr e) (.eres (.vals [v] st'))))) ∨
    (∃ e, rhs = some e ∧ V' = V ∧ o = .halt ∧
      Step D funs V st (.expr e) (.eres (.halt st'))) := by
  cases h with
  | letZero =>
      exact Or.inl ⟨_, rfl, rfl, Or.inl ⟨rfl, rfl, rfl⟩⟩
  | @letVal _ _ _ _ _ vals _ he hlen =>
      obtain ⟨v, rfl⟩ : ∃ v, vals = [v] := by
        cases vals with
        | nil => simp at hlen
        | cons a t =>
            cases t with
            | nil => exact ⟨a, rfl⟩
            | cons b t2 => simp at hlen
      exact Or.inl ⟨v, by simp, rfl, Or.inr ⟨_, rfl, he⟩⟩
  | letHalt he => exact Or.inr ⟨_, rfl, rfl, rfl, he⟩

private theorem boundOK_cons {V : VEnv D} {bound : List Ident} {x : Ident}
    {v : U256} (hb : BoundOK V bound) :
    BoundOK ((x, v) :: V) (x :: bound) := by
  intro z hz
  rcases List.mem_cons.mp hz with rfl | hz
  · simp
  · simp [hb z hz]

private theorem boundOK_after_let {funs : FunEnv D} {V V1 : VEnv D}
    {st st1 : EvmState} {xs : List Ident} {val : Option (Expr Op)}
    {bound : List Ident} (hb : BoundOK V bound)
    (hs : Step D funs V st (.stmt (.letDecl xs val)) (.sres V1 st1 .normal)) :
    BoundOK V1 (xs ++ bound) := by
  cases hs with
  | letZero =>
      intro z hz
      rw [List.map_append, bindZeros_keys]
      rcases List.mem_append.mp hz with hzz | hzz
      · exact List.mem_append_left _ hzz
      · exact List.mem_append_right _ (hb z hzz)
  | letVal he hlen =>
      intro z hz
      rw [List.map_append, zip_keys (by omega)]
      rcases List.mem_append.mp hz with hzz | hzz
      · exact List.mem_append_left _ hzz
      · exact List.mem_append_right _ (hb z hzz)

/-- A single-target `setMany` is a `set`. -/
private theorem setMany_single (V : VEnv D) (y : Ident) (w : U256) :
    VEnv.setMany V [y] [w] = VEnv.set V y w := rfl

/-- `set` of a variable other than the freshly-inserted `x` commutes past the
insertion (`set` updates the topmost matching key, and the inserted `(x,·)`
never matches). -/
private theorem set_cons_ne {V : VEnv D} {x y : Ident} (hxy : x ≠ y)
    (v w : U256) :
    VEnv.set ((x, v) :: V) y w = (x, v) :: VEnv.set V y w := by
  simp only [VEnv.set, if_neg hxy]

/-- Forward: a run of the source sequence yields a run of the rejoined
sequence, the final environments related by dead insertions above the entry
frame (one per merged pair). -/
theorem rjPairs_fwd : ∀ (bound : List Ident) (ss : List (Stmt Op))
    {funs : FunEnv D} {V : VEnv D} {st : EvmState} {V₁ : VEnv D}
    {st₁ : EvmState} {o : Outcome},
    BoundOK V bound →
    Step D funs V st (.stmts ss) (.sres V₁ st₁ o) →
    ∃ V₂, Step D funs V st (.stmts (rjPairs bound ss)) (.sres V₂ st₁ o) ∧
      InsChain (calls := calls) (creates := creates) V.length V₂ V₁ := by
  intro bound ss
  induction bound, ss using rjPairs.induct with
  | case1 bound x e y f rest hg ih =>
      intro funs V st V₁ st₁ o hb h
      rw [rjPairs.eq_1, if_pos hg]
      obtain ⟨hxy, htree, hm, hcall, hdepth⟩ := hg
      cases h with
      | seqCons hlet1 htail =>
          rcases rjLetInv hlet1 with ⟨v, rfl, -, hemat⟩ | ⟨e', -, -, hno, -⟩
          · rcases hemat with ⟨heq, -, -⟩ | ⟨e', heq, he⟩
            · cases heq
            · injection heq with heq
              subst heq
              cases htail with
              | seqCons hlet2 hrest =>
                  rcases rjLetInv hlet2 with ⟨w', rfl, -, hfmat⟩ |
                    ⟨f', -, -, hno2, -⟩
                  · rcases hfmat with ⟨heqf, -, -⟩ | ⟨f', heqf, hf⟩
                    · cases heqf
                    · injection heqf with heqf
                      subst heqf
                      obtain ⟨w, hvs, hst2, htgt⟩ := rjT1_fwd f htree he hf
                      injection hvs with hveq
                      subst hveq
                      subst hst2
                      have hins : InsAt V.length x v ((y, w') :: V)
                          ((y, w') :: (x, v) :: V) :=
                        ⟨[(y, w')], V, rfl, rfl, rfl⟩
                      obtain ⟨res₁, hstep₁, hrel⟩ := frameRemove hrest hins
                        (by simpa only [codeMentions] using hm)
                      obtain ⟨V₁', rfl, hins'⟩ := ResRelAt.sres_right hrel
                      obtain ⟨V₂, htgt2, hchain⟩ := ih hb
                        (Step.seqCons (Step.letVal (vars := [y]) htgt rfl) hstep₁)
                      exact ⟨V₂, htgt2, .snoc hchain hins' (Nat.le_refl _)⟩
                  · exact absurd hno2.symm (by simp)
              | seqStop hlet2 hne =>
                  rcases rjLetInv hlet2 with ⟨w', -, hnorm, -⟩ |
                    ⟨f', heqf, -, -, hfh⟩
                  · exact absurd hnorm hne
                  · injection heqf with heqf
                    subst heqf
                    exact absurd hfh (rjT1_fwd_nohalt f htree he)
          · exact absurd hno.symm (by simp)
      | seqStop hlet1 hne =>
          rcases rjLetInv hlet1 with ⟨v, -, hnorm, -⟩ | ⟨e', heq, rfl, rfl, heh⟩
          · exact absurd hnorm hne
          · injection heq with heq
            subst heq
            obtain ⟨V₂, htgt2, hchain⟩ := ih hb
              (Step.seqStop (Step.letHalt (vars := [y])
                (rjT1_halt hb heh f htree)) (by intro hc; cases hc))
            exact ⟨V₂, htgt2, hchain⟩
  | case2 bound x e y f rest hng ih =>
      intro funs V st V₁ st₁ o hb h
      rw [rjPairs.eq_1, if_neg hng]
      cases h with
      | seqCons hs htail =>
          rcases rjLetInv hs with ⟨v, rfl, -, -⟩ | ⟨e', -, -, hno, -⟩
          · obtain ⟨V₂, htgt, hchain⟩ := ih (boundOK_cons hb) htail
            exact ⟨V₂, Step.seqCons hs htgt, hchain.mono (by simp)⟩
          · exact absurd hno.symm (by simp)
      | seqStop hs hne =>
          exact ⟨V₁, Step.seqStop hs hne, .refl _⟩
  | case3 bound x e y f rest hg ih =>
      intro funs V st V₁ st₁ o hb h
      rw [rjPairs.eq_2, if_pos hg]
      obtain ⟨hxy, htree, hm, hcall, -, hdepth⟩ := hg
      cases h with
      | seqCons hlet1 htail =>
          rcases rjLetInv hlet1 with ⟨v, rfl, -, hemat⟩ | ⟨e', -, -, hno, -⟩
          · rcases hemat with ⟨heq, -, -⟩ | ⟨e', heq, he⟩
            · cases heq
            · injection heq with heq
              subst heq
              cases htail with
              | seqCons hassign hrest =>
                  cases hassign with
                  | assignVal hf _hlen =>
                      obtain ⟨w, hvs, hst2, htgt⟩ := rjT1_fwd f htree he hf
                      subst hst2
                      subst hvs
                      rw [setMany_single, set_cons_ne hxy] at hrest
                      have hins : InsAt V.length x v (VEnv.set V y w)
                          ((x, v) :: VEnv.set V y w) :=
                        ⟨[], VEnv.set V y w, rfl, rfl, VEnv.set_length V y w⟩
                      obtain ⟨res₁, hstep₁, hrel⟩ := frameRemove hrest hins
                        (by simpa only [codeMentions] using hm)
                      obtain ⟨V₁', rfl, hins'⟩ := ResRelAt.sres_right hrel
                      have hassignstep := Step.assignVal (funs := funs)
                        (vars := [y]) htgt (rfl : [w].length = [y].length)
                      rw [setMany_single] at hassignstep
                      obtain ⟨V₂, htgt2, hchain⟩ := ih hb
                        (Step.seqCons hassignstep hstep₁)
                      exact ⟨V₂, htgt2, .snoc hchain hins' (Nat.le_refl _)⟩
              | seqStop hassign hne =>
                  cases hassign with
                  | assignVal _hf _hlen => exact absurd rfl hne
                  | assignHalt hfh =>
                      exact absurd hfh (rjT1_fwd_nohalt f htree he)
          · exact absurd hno.symm (by simp)
      | seqStop hlet1 hne =>
          rcases rjLetInv hlet1 with ⟨v, -, hnorm, -⟩ | ⟨e', heq, rfl, rfl, heh⟩
          · exact absurd hnorm hne
          · injection heq with heq
            subst heq
            obtain ⟨V₂, htgt2, hchain⟩ := ih hb
              (Step.seqStop (Step.assignHalt (vars := [y])
                (rjT1_halt hb heh f htree)) (by intro hc; cases hc))
            exact ⟨V₂, htgt2, hchain⟩
  | case4 bound x e y f rest hng ih =>
      intro funs V st V₁ st₁ o hb h
      rw [rjPairs.eq_2, if_neg hng]
      cases h with
      | seqCons hs htail =>
          rcases rjLetInv hs with ⟨v, rfl, -, -⟩ | ⟨e', -, -, hno, -⟩
          · obtain ⟨V₂, htgt, hchain⟩ := ih (boundOK_cons hb) htail
            exact ⟨V₂, Step.seqCons hs htgt, hchain.mono (by simp)⟩
          · exact absurd hno.symm (by simp)
      | seqStop hs hne =>
          exact ⟨V₁, Step.seqStop hs hne, .refl _⟩
  | case5 bound x e c body rest hg ih =>
      intro funs V st V₁ st₁ o hb h
      rw [rjPairs.eq_3, if_pos hg]
      obtain ⟨htree, hmbody, hmrest, hcall, -, hdepth⟩ := hg
      cases h with
      | seqCons hlet1 htail =>
          rcases rjLetInv hlet1 with ⟨v, rfl, -, hemat⟩ | ⟨e', -, -, hno, -⟩
          · rcases hemat with ⟨heq, -, -⟩ | ⟨e', heq, he⟩
            · cases heq
            · injection heq with heq
              subst heq
              cases htail with
              | seqCons hcond hrest =>
                  cases hcond with
                  | ifTrue hc hnz hbody =>
                      obtain ⟨cw, hcvs, hcst, htgtc⟩ := rjT1_fwd c htree he hc
                      injection hcvs with hcveq; subst hcveq
                      subst hcst
                      have hins_blk : InsAt V.length x v V ((x, v) :: V) :=
                        ⟨[], V, rfl, rfl, rfl⟩
                      obtain ⟨resb, hstepb, hrelb⟩ := frameRemove hbody hins_blk
                        (by simpa only [codeMentions, stmtMentions] using hmbody)
                      obtain ⟨V1_body, rfl, hins_body⟩ := ResRelAt.sres_right hrelb
                      obtain ⟨resr, hstepr, hrelr⟩ := frameRemove hrest hins_body
                        (by simpa only [codeMentions] using hmrest)
                      obtain ⟨V₁', rfl, hins'⟩ := ResRelAt.sres_right hrelr
                      obtain ⟨V₂, htgt2, hchain⟩ := ih hb
                        (Step.seqCons (Step.ifTrue htgtc hnz hstepb) hstepr)
                      exact ⟨V₂, htgt2, .snoc hchain hins' (Nat.le_refl _)⟩
                  | ifFalse hc hz =>
                      obtain ⟨cw, hcvs, hcst, htgtc⟩ := rjT1_fwd c htree he hc
                      injection hcvs with hcveq; subst hcveq
                      subst hcst
                      have hins : InsAt V.length x v V ((x, v) :: V) :=
                        ⟨[], V, rfl, rfl, rfl⟩
                      obtain ⟨resr, hstepr, hrelr⟩ := frameRemove hrest hins
                        (by simpa only [codeMentions] using hmrest)
                      obtain ⟨V₁', rfl, hins'⟩ := ResRelAt.sres_right hrelr
                      obtain ⟨V₂, htgt2, hchain⟩ := ih hb
                        (Step.seqCons (Step.ifFalse htgtc hz) hstepr)
                      exact ⟨V₂, htgt2, .snoc hchain hins' (Nat.le_refl _)⟩
              | seqStop hcond hne =>
                  cases hcond with
                  | ifTrue hc hnz hbody =>
                      obtain ⟨cw, hcvs, hcst, htgtc⟩ := rjT1_fwd c htree he hc
                      injection hcvs with hcveq; subst hcveq
                      subst hcst
                      have hins_blk : InsAt V.length x v V ((x, v) :: V) :=
                        ⟨[], V, rfl, rfl, rfl⟩
                      obtain ⟨resb, hstepb, hrelb⟩ := frameRemove hbody hins_blk
                        (by simpa only [codeMentions, stmtMentions] using hmbody)
                      obtain ⟨V1_body, rfl, hins_body⟩ := ResRelAt.sres_right hrelb
                      obtain ⟨V₂, htgt2, hchain⟩ := ih hb
                        (Step.seqStop (Step.ifTrue htgtc hnz hstepb) hne)
                      exact ⟨V₂, htgt2, .snoc hchain hins_body (Nat.le_refl _)⟩
                  | ifFalse _hc _hz => exact absurd rfl hne
                  | ifHalt hch =>
                      exact absurd hch (rjT1_fwd_nohalt c htree he)
          · exact absurd hno.symm (by simp)
      | seqStop hlet1 hne =>
          rcases rjLetInv hlet1 with ⟨v, -, hnorm, -⟩ | ⟨e', heq, rfl, rfl, heh⟩
          · exact absurd hnorm hne
          · injection heq with heq
            subst heq
            obtain ⟨V₂, htgt2, hchain⟩ := ih hb
              (Step.seqStop (Step.ifHalt (rjT1_halt hb heh c htree))
                (by intro hc; cases hc))
            exact ⟨V₂, htgt2, hchain⟩
  | case6 bound x e c body rest hng ih =>
      intro funs V st V₁ st₁ o hb h
      rw [rjPairs.eq_3, if_neg hng]
      cases h with
      | seqCons hs htail =>
          rcases rjLetInv hs with ⟨v, rfl, -, -⟩ | ⟨e', -, -, hno, -⟩
          · obtain ⟨V₂, htgt, hchain⟩ := ih (boundOK_cons hb) htail
            exact ⟨V₂, Step.seqCons hs htgt, hchain.mono (by simp)⟩
          · exact absurd hno.symm (by simp)
      | seqStop hs hne =>
          exact ⟨V₁, Step.seqStop hs hne, .refl _⟩
  | case7 bound xs v rest hno1 hno2 hno3 ih =>
      intro funs V st V₁ st₁ o hb h
      rw [rjPairs.eq_4 bound xs v rest hno1 hno2 hno3]
      cases h with
      | seqCons hs htail =>
          obtain ⟨V₂, htgt, hchain⟩ := ih (boundOK_after_let hb hs) htail
          exact ⟨V₂, Step.seqCons hs htgt,
            hchain.mono (venvLen_mono hs rfl)⟩
      | seqStop hs hne =>
          exact ⟨V₁, Step.seqStop hs hne, .refl _⟩
  | case8 bound s rest hno1 hno2 hno3 hno4 ih =>
      intro funs V st V₁ st₁ o hb h
      rw [rjPairs.eq_5 bound s rest hno1 hno2 hno3 hno4]
      cases h with
      | seqCons hs htail =>
          obtain ⟨V₂, htgt, hchain⟩ := ih (hb.mono hs) htail
          exact ⟨V₂, Step.seqCons hs htgt,
            hchain.mono (venvLen_mono hs rfl)⟩
      | seqStop hs hne =>
          exact ⟨V₁, Step.seqStop hs hne, .refl _⟩
  | case9 bound =>
      intro funs V st V₁ st₁ o hb h
      rw [rjPairs.eq_6]
      cases h
      exact ⟨_, Step.seqNil, .refl _⟩

/-- Backward direction, via `frameAdd` and the backward carrier lemmas. -/
theorem rjPairs_bwd : ∀ (bound : List Ident) (ss : List (Stmt Op))
    {funs : FunEnv D} {V : VEnv D} {st : EvmState} {V₂ : VEnv D}
    {st₁ : EvmState} {o : Outcome},
    BoundOK V bound →
    Step D funs V st (.stmts (rjPairs bound ss)) (.sres V₂ st₁ o) →
    ∃ V₁, Step D funs V st (.stmts ss) (.sres V₁ st₁ o) ∧
      InsChain (calls := calls) (creates := creates) V.length V₂ V₁ := by
  intro bound ss
  induction bound, ss using rjPairs.induct with
  | case1 bound x e y f rest hg ih =>
      intro funs V st V₂ st₁ o hb h
      rw [rjPairs.eq_1, if_pos hg] at h
      obtain ⟨hxy, htree, hm, hcall, hdepth⟩ := hg
      obtain ⟨V₁', hsrc', hchain⟩ := ih hb h
      cases hsrc' with
      | seqCons hlet_y htail =>
          rcases rjLetInv hlet_y with ⟨w', rfl, -, hgmat⟩ | ⟨g', -, -, hno, -⟩
          · rcases hgmat with ⟨heq, -, -⟩ | ⟨g', heq, hg'⟩
            · cases heq
            · injection heq with heq
              subst heq
              obtain ⟨w, v, st1, hws, hst1, he, hsrc⟩ :=
                rjT1_bwd hb f htree rfl hg'
              injection hws with hweq
              subst hweq
              subst hst1
              have hins : InsAt V.length x v ((y, w') :: V)
                  ((y, w') :: (x, v) :: V) :=
                ⟨[(y, w')], V, rfl, rfl, rfl⟩
              obtain ⟨res₂, hstep₂, hrel⟩ := frameAdd htail hins
                (by simpa only [codeMentions] using hm)
              obtain ⟨V₁, rfl, hins'⟩ := ResRelAt.sres hrel
              refine ⟨V₁, Step.seqCons (Step.letVal (vars := [x]) he rfl)
                (Step.seqCons (Step.letVal (vars := [y]) hsrc rfl) hstep₂),
                .snoc hchain hins' (Nat.le_refl _)⟩
          · exact absurd hno.symm (by simp)
      | seqStop hlet_y hne =>
          rcases rjLetInv hlet_y with ⟨w', -, hnorm, -⟩ |
            ⟨g', heq, rfl, rfl, hgh⟩
          · exact absurd hnorm hne
          · injection heq with heq
            subst heq
            exact ⟨V₁', Step.seqStop (Step.letHalt (vars := [x])
              (rjT1_bwd_halt hb f htree hgh)) hne, hchain⟩
  | case2 bound x e y f rest hng ih =>
      intro funs V st V₂ st₁ o hb h
      rw [rjPairs.eq_1, if_neg hng] at h
      cases h with
      | seqCons hs htail =>
          rcases rjLetInv hs with ⟨v, rfl, -, -⟩ | ⟨e', -, -, hno, -⟩
          · obtain ⟨V₁, hsrc, hchain⟩ := ih (boundOK_cons hb) htail
            exact ⟨V₁, Step.seqCons hs hsrc, hchain.mono (by simp)⟩
          · exact absurd hno.symm (by simp)
      | seqStop hs hne =>
          exact ⟨V₂, Step.seqStop hs hne, .refl _⟩
  | case3 bound x e y f rest hg ih =>
      intro funs V st V₂ st₁ o hb h
      rw [rjPairs.eq_2, if_pos hg] at h
      obtain ⟨hxy, htree, hm, hcall, -, hdepth⟩ := hg
      obtain ⟨V₁', hsrc', hchain⟩ := ih hb h
      cases hsrc' with
      | seqCons hassign htail =>
          cases hassign with
          | assignVal hsubf hlen =>
              obtain ⟨w, v, sc, hws, hcst, he, hsrc⟩ :=
                rjT1_bwd hb f htree hlen hsubf
              subst hws
              subst hcst
              rw [setMany_single] at htail
              have hins : InsAt V.length x v (VEnv.set V y w)
                  ((x, v) :: VEnv.set V y w) :=
                ⟨[], VEnv.set V y w, rfl, rfl, VEnv.set_length V y w⟩
              obtain ⟨res₂, hstep₂, hrel⟩ := frameAdd htail hins
                (by simpa only [codeMentions] using hm)
              obtain ⟨V₁, rfl, hins'⟩ := ResRelAt.sres hrel
              have hassign_src := Step.assignVal (funs := funs) (vars := [y])
                hsrc (rfl : [w].length = [y].length)
              rw [setMany_single, set_cons_ne hxy] at hassign_src
              refine ⟨V₁, Step.seqCons (Step.letVal (vars := [x]) he rfl)
                (Step.seqCons hassign_src hstep₂),
                .snoc hchain hins' (Nat.le_refl _)⟩
      | seqStop hassign hne =>
          cases hassign with
          | assignVal _hsub _hlen => exact absurd rfl hne
          | assignHalt hsubfh =>
              exact ⟨_, Step.seqStop (Step.letHalt (vars := [x])
                (rjT1_bwd_halt hb f htree hsubfh)) hne, hchain⟩
  | case4 bound x e y f rest hng ih =>
      intro funs V st V₂ st₁ o hb h
      rw [rjPairs.eq_2, if_neg hng] at h
      cases h with
      | seqCons hs htail =>
          rcases rjLetInv hs with ⟨v, rfl, -, -⟩ | ⟨e', -, -, hno, -⟩
          · obtain ⟨V₁, hsrc, hchain⟩ := ih (boundOK_cons hb) htail
            exact ⟨V₁, Step.seqCons hs hsrc, hchain.mono (by simp)⟩
          · exact absurd hno.symm (by simp)
      | seqStop hs hne =>
          exact ⟨V₂, Step.seqStop hs hne, .refl _⟩
  | case5 bound x e c body rest hg ih =>
      intro funs V st V₂ st₁ o hb h
      rw [rjPairs.eq_3, if_pos hg] at h
      obtain ⟨htree, hmbody, hmrest, hcall, -, hdepth⟩ := hg
      obtain ⟨V₁', hsrc', hchain⟩ := ih hb h
      cases hsrc' with
      | seqCons hcond htail =>
          cases hcond with
          | ifTrue hsubc hnz hbody =>
              obtain ⟨cw, v, sc, hcws, hcst, he, hsrcc⟩ :=
                rjT1_bwd hb c htree rfl hsubc
              injection hcws with hcweq; subst hcweq
              subst hcst
              have hins_blk : InsAt V.length x v V ((x, v) :: V) :=
                ⟨[], V, rfl, rfl, rfl⟩
              obtain ⟨resb, hstepb, hrelb⟩ := frameAdd hbody hins_blk
                (by simpa only [codeMentions, stmtMentions] using hmbody)
              obtain ⟨Vc', rfl, hins_body⟩ := ResRelAt.sres hrelb
              obtain ⟨resr, hstepr, hrelr⟩ := frameAdd htail hins_body
                (by simpa only [codeMentions] using hmrest)
              obtain ⟨V₁, rfl, hins'⟩ := ResRelAt.sres hrelr
              refine ⟨V₁, Step.seqCons (Step.letVal (vars := [x]) he rfl)
                (Step.seqCons (Step.ifTrue hsrcc hnz hstepb) hstepr),
                .snoc hchain hins' (Nat.le_refl _)⟩
          | ifFalse hsubc hz =>
              obtain ⟨cw, v, sc, hcws, hcst, he, hsrcc⟩ :=
                rjT1_bwd hb c htree rfl hsubc
              injection hcws with hcweq; subst hcweq
              subst hcst
              have hins : InsAt V.length x v V ((x, v) :: V) :=
                ⟨[], V, rfl, rfl, rfl⟩
              obtain ⟨resr, hstepr, hrelr⟩ := frameAdd htail hins
                (by simpa only [codeMentions] using hmrest)
              obtain ⟨V₁, rfl, hins'⟩ := ResRelAt.sres hrelr
              refine ⟨V₁, Step.seqCons (Step.letVal (vars := [x]) he rfl)
                (Step.seqCons (Step.ifFalse hsrcc hz) hstepr),
                .snoc hchain hins' (Nat.le_refl _)⟩
      | seqStop hcond hne =>
          cases hcond with
          | ifTrue hsubc hnz hbody =>
              obtain ⟨cw, v, sc, hcws, hcst, he, hsrcc⟩ :=
                rjT1_bwd hb c htree rfl hsubc
              injection hcws with hcweq; subst hcweq
              subst hcst
              have hins_blk : InsAt V.length x v V ((x, v) :: V) :=
                ⟨[], V, rfl, rfl, rfl⟩
              obtain ⟨resb, hstepb, hrelb⟩ := frameAdd hbody hins_blk
                (by simpa only [codeMentions, stmtMentions] using hmbody)
              obtain ⟨Vc', rfl, hins_body⟩ := ResRelAt.sres hrelb
              refine ⟨Vc', Step.seqCons (Step.letVal (vars := [x]) he rfl)
                (Step.seqStop (Step.ifTrue hsrcc hnz hstepb) hne),
                .snoc hchain hins_body (Nat.le_refl _)⟩
          | ifFalse _hsubc _hz => exact absurd rfl hne
          | ifHalt hsubch =>
              exact ⟨_, Step.seqStop (Step.letHalt (vars := [x])
                (rjT1_bwd_halt hb c htree hsubch)) hne, hchain⟩
  | case6 bound x e c body rest hng ih =>
      intro funs V st V₂ st₁ o hb h
      rw [rjPairs.eq_3, if_neg hng] at h
      cases h with
      | seqCons hs htail =>
          rcases rjLetInv hs with ⟨v, rfl, -, -⟩ | ⟨e', -, -, hno, -⟩
          · obtain ⟨V₁, hsrc, hchain⟩ := ih (boundOK_cons hb) htail
            exact ⟨V₁, Step.seqCons hs hsrc, hchain.mono (by simp)⟩
          · exact absurd hno.symm (by simp)
      | seqStop hs hne =>
          exact ⟨V₂, Step.seqStop hs hne, .refl _⟩
  | case7 bound xs v rest hno1 hno2 hno3 ih =>
      intro funs V st V₂ st₁ o hb h
      rw [rjPairs.eq_4 bound xs v rest hno1 hno2 hno3] at h
      cases h with
      | seqCons hs htail =>
          obtain ⟨V₁, hsrc, hchain⟩ := ih (boundOK_after_let hb hs) htail
          exact ⟨V₁, Step.seqCons hs hsrc,
            hchain.mono (venvLen_mono hs rfl)⟩
      | seqStop hs hne =>
          exact ⟨V₂, Step.seqStop hs hne, .refl _⟩
  | case8 bound s rest hno1 hno2 hno3 hno4 ih =>
      intro funs V st V₂ st₁ o hb h
      rw [rjPairs.eq_5 bound s rest hno1 hno2 hno3 hno4] at h
      cases h with
      | seqCons hs htail =>
          obtain ⟨V₁, hsrc, hchain⟩ := ih (hb.mono hs) htail
          exact ⟨V₁, Step.seqCons hs hsrc,
            hchain.mono (venvLen_mono hs rfl)⟩
      | seqStop hs hne =>
          exact ⟨V₂, Step.seqStop hs hne, .refl _⟩
  | case9 bound =>
      intro funs V st V₂ st₁ o hb h
      rw [rjPairs.eq_6] at h
      cases h
      exact ⟨_, Step.seqNil, .refl _⟩

/-! ### Rejoining preserves the hoisted scope -/

theorem rjPairs_hoist : ∀ (bound : List Ident) (ss : List (Stmt Op)),
    hoist D (rjPairs bound ss) = hoist D ss := by
  intro bound ss
  induction bound, ss using rjPairs.induct with
  | case1 bound x e y f rest hg ih =>
      rw [rjPairs.eq_1, if_pos hg]
      simpa [hoist] using ih
  | case2 bound x e y f rest hng ih =>
      rw [rjPairs.eq_1, if_neg hng]
      simpa [hoist] using ih
  | case3 bound x e y f rest hg ih =>
      rw [rjPairs.eq_2, if_pos hg]
      simpa [hoist] using ih
  | case4 bound x e y f rest hng ih =>
      rw [rjPairs.eq_2, if_neg hng]
      simpa [hoist] using ih
  | case5 bound x e c body rest hg ih =>
      rw [rjPairs.eq_3, if_pos hg]
      simpa [hoist] using ih
  | case6 bound x e c body rest hng ih =>
      rw [rjPairs.eq_3, if_neg hng]
      simpa [hoist] using ih
  | case7 bound xs v rest hno1 hno2 hno3 ih =>
      rw [rjPairs.eq_4 bound xs v rest hno1 hno2 hno3]
      simp only [hoist, List.filterMap_cons] at ih ⊢
      rw [ih]
  | case8 bound s rest hno1 hno2 hno3 hno4 ih =>
      rw [rjPairs.eq_5 bound s rest hno1 hno2 hno3 hno4]
      simp only [hoist, List.filterMap_cons] at ih ⊢
      rw [ih]
  | case9 bound => rw [rjPairs.eq_6]

/-- Pair rejoining alone is a sound block rewrite: both sides hoist the same
scope, and the dead insertions vanish under the block's `restore`. The
sequence-local bound set starts empty, so `BoundOK` holds vacuously. -/
theorem rjPairs_blockEquiv (zz : Block Op) :
    EquivBlock D zz (rjPairs [] zz) := by
  intro funs V st V' st' o
  constructor
  · intro h
    cases h with
    | block hb =>
        obtain ⟨V₂, hstep, hchain⟩ := rjPairs_fwd [] zz (BoundOK.nil V) hb
        rw [hchain.restore_eq]
        exact Step.block (by rw [rjPairs_hoist]; exact hstep)
  · intro h
    cases h with
    | block hb =>
        rw [rjPairs_hoist] at hb
        obtain ⟨V₁, hstep, hchain⟩ := rjPairs_bwd [] zz (BoundOK.nil V) hb
        rw [← hchain.restore_eq]
        exact Step.block hstep

/-! ### Lifting through the syntax -/

mutual

theorem rjStmt_equiv : ∀ s : Stmt Op, EquivStmt D s (rjStmt s)
  | .block body => by
      unfold rjStmt
      show EquivBlock D body (rjPairs [] (rjStmts body))
      exact (EquivBlock.of_stmts_funs
        (EquivStmts.of_forall₂ (rjStmts_forall2 body))
        (rjScopeRel body)).trans
        (rjPairs_blockEquiv (rjStmts body))
  | .funDef n ps rs body => by
      unfold rjStmt
      intro funs V st V' st' o
      constructor
      · intro h; cases h; exact Step.funDef
      · intro h; cases h; exact Step.funDef
  | .cond c body => by
      unfold rjStmt
      refine EquivStmt.cond_congr
        (@EquivExpr.refl (evmWithExternal calls creates) _ c) ?_
      exact (EquivBlock.of_stmts_funs
        (EquivStmts.of_forall₂ (rjStmts_forall2 body))
        (rjScopeRel body)).trans
        (rjPairs_blockEquiv (rjStmts body))
  | .switch c cases dflt => by
      unfold rjStmt
      refine EquivStmt.switch_congr
        (@EquivExpr.refl (evmWithExternal calls creates) _ c)
        (rjCases_forall2 cases) ?_
      cases dflt with
      | none => exact EquivBlock.refl _
      | some b =>
          unfold rjDflt
          exact (EquivBlock.of_stmts_funs
            (EquivStmts.of_forall₂ (rjStmts_forall2 b))
            (rjScopeRel b)).trans
            (rjPairs_blockEquiv (rjStmts b))
  | .forLoop init c post body => by
      unfold rjStmt
      refine EquivStmt.forLoop_congr init
        (@EquivExpr.refl (evmWithExternal calls creates) _ c) ?_ ?_
      · exact (EquivBlock.of_stmts_funs
          (EquivStmts.of_forall₂ (rjStmts_forall2 post))
          (rjScopeRel post)).trans
          (rjPairs_blockEquiv (rjStmts post))
      · exact (EquivBlock.of_stmts_funs
          (EquivStmts.of_forall₂ (rjStmts_forall2 body))
          (rjScopeRel body)).trans
          (rjPairs_blockEquiv (rjStmts body))
  | .letDecl xs v => by unfold rjStmt; exact EquivStmt.refl _
  | .assign xs e => by unfold rjStmt; exact EquivStmt.refl _
  | .exprStmt e => by unfold rjStmt; exact EquivStmt.refl _
  | .break => by unfold rjStmt; exact EquivStmt.refl _
  | .continue => by unfold rjStmt; exact EquivStmt.refl _
  | .leave => by unfold rjStmt; exact EquivStmt.refl _

theorem rjStmts_forall2 : ∀ ss : List (Stmt Op),
    List.Forall₂ (EquivStmt D) ss (rjStmts ss)
  | [] => .nil
  | s :: rest => .cons (rjStmt_equiv s) (rjStmts_forall2 rest)

theorem rjCases_forall2 : ∀ cs : List (Literal × Block Op),
    List.Forall₂ (fun p q => p.1 = q.1 ∧ EquivBlock D p.2 q.2) cs (rjCases cs)
  | [] => .nil
  | (_l, b) :: rest =>
      .cons ⟨rfl, (EquivBlock.of_stmts_funs
          (EquivStmts.of_forall₂ (rjStmts_forall2 b))
          (rjScopeRel b)).trans
          (rjPairs_blockEquiv (rjStmts b))⟩
        (rjCases_forall2 rest)

theorem rjScopeRel : ∀ ss : List (Stmt Op),
    ScopeRel D (hoist D ss) (hoist D (rjStmts ss))
  | [] => .nil
  | .funDef n ps rs body :: rest => by
      unfold rjStmts rjStmt
      refine List.Forall₂.cons ⟨rfl, rfl, rfl, ?_⟩ (rjScopeRel rest)
      exact (EquivBlock.of_stmts_funs
        (EquivStmts.of_forall₂ (rjStmts_forall2 body))
        (rjScopeRel body)).trans
        (rjPairs_blockEquiv (rjStmts body))
  | .block body :: rest => by
      simpa [hoist, rjStmts, rjStmt] using rjScopeRel rest
  | .letDecl xs v :: rest => by
      simpa [hoist, rjStmts, rjStmt] using rjScopeRel rest
  | .assign xs e :: rest => by
      simpa [hoist, rjStmts, rjStmt] using rjScopeRel rest
  | .cond c body :: rest => by
      simpa [hoist, rjStmts, rjStmt] using rjScopeRel rest
  | .«switch» c cs dflt :: rest => by
      simpa [hoist, rjStmts, rjStmt] using rjScopeRel rest
  | .forLoop init c post body :: rest => by
      simpa [hoist, rjStmts, rjStmt] using rjScopeRel rest
  | .exprStmt e :: rest => by
      simpa [hoist, rjStmts, rjStmt] using rjScopeRel rest
  | .«break» :: rest => by
      simpa [hoist, rjStmts, rjStmt] using rjScopeRel rest
  | .«continue» :: rest => by
      simpa [hoist, rjStmts, rjStmt] using rjScopeRel rest
  | .«leave» :: rest => by
      simpa [hoist, rjStmts, rjStmt] using rjScopeRel rest

end

theorem rejoinPairsBlock_sound (b : Block Op) :
    EquivBlock D b (rejoinPairsBlock b) := by
  unfold rejoinPairsBlock
  by_cases hlf : storageLayoutFreeStmts b
  · rw [if_pos hlf]
    exact (EquivBlock.of_stmts_funs
      (EquivStmts.of_forall₂ (rjStmts_forall2 b))
      (rjScopeRel b)).trans
      (rjPairs_blockEquiv (rjStmts b))
  · rw [if_neg hlf]
    exact @EquivBlock.refl (evmWithExternal calls creates) _ b

/-! ### Object-path congruence

The processed block is guaranteed free of unresolved `dataoffset`/`datasize`
by the transform's own guard, and the rewrite only rearranges subterms of
that block — so layout resolution is the identity on both the input and the
output, and the RPass obligation reduces to the pass's own soundness. -/

mutual

theorem rjSubst_layoutFree {x : Ident} {e : Expr Op}
    (helf : storageLayoutFreeExpr e = true) :
    ∀ t : Expr Op, storageLayoutFreeExpr t = true →
      storageLayoutFreeExpr (rjSubst x e t) = true
  | .lit _, _ => rfl
  | .var z, _ => by
      unfold rjSubst
      by_cases hz : z = x
      · rw [if_pos hz]; exact helf
      · rw [if_neg hz]; rfl
  | .builtin op args, h => by
      unfold rjSubst
      simp only [storageLayoutFreeExpr, Bool.and_eq_true] at h ⊢
      exact ⟨⟨h.1.1, h.1.2⟩, rjSubstArgs_layoutFree helf args h.2⟩
  | .call f args, h => by unfold rjSubst; exact h

theorem rjSubstArgs_layoutFree {x : Ident} {e : Expr Op}
    (helf : storageLayoutFreeExpr e = true) :
    ∀ args : List (Expr Op), storageLayoutFreeArgs args = true →
      storageLayoutFreeArgs (rjSubstArgs x e args) = true
  | [], _ => rfl
  | a :: rest, h => by
      simp only [rjSubstArgs, storageLayoutFreeArgs, Bool.and_eq_true] at h ⊢
      exact ⟨rjSubst_layoutFree helf a h.1, rjSubstArgs_layoutFree helf rest h.2⟩

end

private theorem slf_cons {s : Stmt Op} {rest : List (Stmt Op)} :
    storageLayoutFreeStmts (s :: rest) =
      (storageLayoutFreeStmt s && storageLayoutFreeStmts rest) := rfl

private theorem slf_let {xs : List Ident} {v : Option (Expr Op)} :
    storageLayoutFreeStmt (.letDecl xs v) = v.all storageLayoutFreeExpr := rfl

private theorem slf_assign {xs : List Ident} {e : Expr Op} :
    storageLayoutFreeStmt (.assign xs e) = storageLayoutFreeExpr e := rfl

private theorem slf_cond {c : Expr Op} {body : List (Stmt Op)} :
    storageLayoutFreeStmt (.cond c body) =
      (storageLayoutFreeExpr c && storageLayoutFreeStmts body) := rfl

theorem rjPairs_layoutFree : ∀ (bound : List Ident) (ss : List (Stmt Op)),
    storageLayoutFreeStmts ss = true →
    storageLayoutFreeStmts (rjPairs bound ss) = true := by
  intro bound ss
  induction bound, ss using rjPairs.induct with
  | case1 bound x e y f rest hg ih =>
      intro h
      rw [rjPairs.eq_1, if_pos hg]
      rw [slf_cons, slf_cons, Bool.and_eq_true, Bool.and_eq_true,
        slf_let, slf_let] at h
      refine ih ?_
      rw [slf_cons, Bool.and_eq_true, slf_let]
      refine ⟨?_, h.2.2⟩
      show storageLayoutFreeExpr (rjSubst x e f) = true
      exact rjSubst_layoutFree (by simpa [Option.all] using h.1) f
        (by simpa [Option.all] using h.2.1)
  | case2 bound x e y f rest hng ih =>
      intro h
      rw [rjPairs.eq_1, if_neg hng]
      rw [slf_cons, Bool.and_eq_true] at h
      rw [slf_cons, Bool.and_eq_true]
      exact ⟨h.1, ih h.2⟩
  | case3 bound x e y f rest hg ih =>
      intro h
      rw [rjPairs.eq_2, if_pos hg]
      rw [slf_cons, slf_cons, Bool.and_eq_true, Bool.and_eq_true,
        slf_let, slf_assign] at h
      refine ih ?_
      rw [slf_cons, Bool.and_eq_true, slf_assign]
      refine ⟨?_, h.2.2⟩
      show storageLayoutFreeExpr (rjSubst x e f) = true
      exact rjSubst_layoutFree (by simpa [Option.all] using h.1) f h.2.1
  | case4 bound x e y f rest hng ih =>
      intro h
      rw [rjPairs.eq_2, if_neg hng]
      rw [slf_cons, Bool.and_eq_true] at h
      rw [slf_cons, Bool.and_eq_true]
      exact ⟨h.1, ih h.2⟩
  | case5 bound x e c body rest hg ih =>
      intro h
      rw [rjPairs.eq_3, if_pos hg]
      rw [slf_cons, slf_cons, Bool.and_eq_true, Bool.and_eq_true,
        slf_let, slf_cond, Bool.and_eq_true] at h
      refine ih ?_
      rw [slf_cons, Bool.and_eq_true, slf_cond, Bool.and_eq_true]
      refine ⟨⟨?_, h.2.1.2⟩, h.2.2⟩
      show storageLayoutFreeExpr (rjSubst x e c) = true
      exact rjSubst_layoutFree (by simpa [Option.all] using h.1) c h.2.1.1
  | case6 bound x e c body rest hng ih =>
      intro h
      rw [rjPairs.eq_3, if_neg hng]
      rw [slf_cons, Bool.and_eq_true] at h
      rw [slf_cons, Bool.and_eq_true]
      exact ⟨h.1, ih h.2⟩
  | case7 bound xs v rest hno1 hno2 hno3 ih =>
      intro h
      rw [rjPairs.eq_4 bound xs v rest hno1 hno2 hno3]
      rw [slf_cons, Bool.and_eq_true] at h
      rw [slf_cons, Bool.and_eq_true]
      exact ⟨h.1, ih h.2⟩
  | case8 bound s rest hno1 hno2 hno3 hno4 ih =>
      intro h
      rw [rjPairs.eq_5 bound s rest hno1 hno2 hno3 hno4]
      rw [slf_cons, Bool.and_eq_true] at h
      rw [slf_cons, Bool.and_eq_true]
      exact ⟨h.1, ih h.2⟩
  | case9 bound => intro h; rw [rjPairs.eq_6]; exact h

mutual

theorem rjStmt_layoutFree : ∀ s : Stmt Op,
    storageLayoutFreeStmt s = true →
    storageLayoutFreeStmt (rjStmt s) = true
  | .block body => fun h => by
      unfold rjStmt
      exact rjPairs_layoutFree [] _ (rjStmts_layoutFree body h)
  | .funDef n ps rs body => fun h => by
      unfold rjStmt
      exact rjPairs_layoutFree [] _ (rjStmts_layoutFree body h)
  | .cond c body => fun h => by
      unfold rjStmt
      simp only [storageLayoutFreeStmt, Bool.and_eq_true] at h ⊢
      exact ⟨h.1, rjPairs_layoutFree [] _ (rjStmts_layoutFree body h.2)⟩
  | .switch c cases dflt => fun h => by
      unfold rjStmt
      simp only [storageLayoutFreeStmt, Bool.and_eq_true] at h ⊢
      exact ⟨⟨h.1.1, rjCases_layoutFree cases h.1.2⟩,
        rjDflt_layoutFree dflt h.2⟩
  | .forLoop init c post body => fun h => by
      unfold rjStmt
      simp only [storageLayoutFreeStmt, Bool.and_eq_true] at h ⊢
      exact ⟨⟨⟨h.1.1.1, h.1.1.2⟩,
        rjPairs_layoutFree [] _ (rjStmts_layoutFree post h.1.2)⟩,
        rjPairs_layoutFree [] _ (rjStmts_layoutFree body h.2)⟩
  | .letDecl xs v => fun h => by unfold rjStmt; exact h
  | .assign xs e => fun h => by unfold rjStmt; exact h
  | .exprStmt e => fun h => by unfold rjStmt; exact h
  | .break => fun h => by unfold rjStmt; exact h
  | .continue => fun h => by unfold rjStmt; exact h
  | .leave => fun h => by unfold rjStmt; exact h

theorem rjStmts_layoutFree : ∀ ss : List (Stmt Op),
    storageLayoutFreeStmts ss = true →
    storageLayoutFreeStmts (rjStmts ss) = true
  | [] => fun h => h
  | s :: rest => fun h => by
      unfold rjStmts
      simp only [storageLayoutFreeStmts, Bool.and_eq_true] at h ⊢
      exact ⟨rjStmt_layoutFree s h.1, rjStmts_layoutFree rest h.2⟩

theorem rjCases_layoutFree : ∀ cs : List (Literal × Block Op),
    storageLayoutFreeCases cs = true →
    storageLayoutFreeCases (rjCases cs) = true
  | [] => fun h => h
  | (l, b) :: rest => fun h => by
      unfold rjCases
      simp only [storageLayoutFreeCases, Bool.and_eq_true] at h ⊢
      exact ⟨rjPairs_layoutFree [] _ (rjStmts_layoutFree b h.1),
        rjCases_layoutFree rest h.2⟩

theorem rjDflt_layoutFree : ∀ d : Option (Block Op),
    storageLayoutFreeDflt d = true →
    storageLayoutFreeDflt (rjDflt d) = true
  | none => fun h => h
  | some b => fun h => by
      unfold rjDflt
      exact rjPairs_layoutFree [] _ (rjStmts_layoutFree b h)

end

/-- **Object-path congruence**: running the pass before layout resolution is
pointwise equivalent to not running it, on the resolved code. -/
theorem resolveRejoinPairsBlock_equiv (L : Layout) (b : Block Op) :
    EquivBlock D (resolveForLayoutStmts L b)
      (resolveForLayoutStmts L (rejoinPairsBlock b)) := by
  unfold rejoinPairsBlock
  by_cases hlf : storageLayoutFreeStmts b
  · rw [if_pos hlf, resolve_storageLayoutFreeStmts L b hlf,
      resolve_storageLayoutFreeStmts L _
        (rjPairs_layoutFree [] _ (rjStmts_layoutFree b hlf))]
    exact (EquivBlock.of_stmts_funs
      (EquivStmts.of_forall₂ (rjStmts_forall2 b))
      (rjScopeRel b)).trans
      (rjPairs_blockEquiv (rjStmts b))
  · rw [if_neg hlf]
    exact @EquivBlock.refl (evmWithExternal calls creates) _ _

/-- **Adjacent single-use expression rejoining** — the verified pass. -/
def rejoinPairs : LocalPass D where
  run := rejoinPairsBlock
  sound := fun b => rejoinPairsBlock_sound b

@[simp] theorem rejoinPairs_run (b : Block Op) :
    (rejoinPairs (calls := calls) (creates := creates)).run b =
      rejoinPairsBlock b := rfl

end YulEvmCompiler.Optimizer
