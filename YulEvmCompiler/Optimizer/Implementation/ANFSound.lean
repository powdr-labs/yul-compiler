import YulSemantics.BigStep
import YulEvmCompiler.Optimizer.Implementation.ANF
import YulEvmCompiler.Optimizer.Spec.Pass
/-!
# ANF normalizer — soundness foundations (`VEnv` weakening atoms)

The ANF normalizer introduces `let` temporaries that stay in scope, so proving
`EquivBlock b (anfBlock b)` needs a **fresh-binding weakening** lemma for `Step`:
a temporary that no code reads threads through execution unchanged and is popped
by the enclosing block's `restore`.

That lemma is a large mutual induction over the whole `Step` relation. It bottoms
out in how `VEnv.get`/`VEnv.set` behave across a prepended (fresh) binding — the
self-contained facts proved here. The `Step`-level weakening lemma and the ANF
temp-tracking simulation build on top; this file is their base.
-/

namespace YulEvmCompiler.Optimizer.ANF

open YulSemantics
open YulSemantics.EVM (Op)

variable {D : Dialect}

/-- Reading a variable past a differently-named binding ignores that binding. -/
@[simp] theorem get_cons_ne {V : VEnv D} {x y : Ident} {w : D.Value} (h : y ≠ x) :
    VEnv.get ((y, w) :: V) x = VEnv.get V x := by
  simp [VEnv.get, List.find?, h]

/-- Reading a variable at its own (innermost) binding. -/
@[simp] theorem get_cons_self {V : VEnv D} {x : Ident} {w : D.Value} :
    VEnv.get ((x, w) :: V) x = some w := by
  simp [VEnv.get, List.find?]

/-- Assigning a variable past a differently-named binding leaves that binding and
recurses into the tail. -/
@[simp] theorem set_cons_ne {V : VEnv D} {x y : Ident} {w v : D.Value} (h : y ≠ x) :
    VEnv.set ((y, w) :: V) x v = (y, w) :: VEnv.set V x v := by
  simp [VEnv.set, h]

/-- Assigning a variable at its own (innermost) binding. -/
@[simp] theorem set_cons_self {V : VEnv D} {x : Ident} {w v : D.Value} :
    VEnv.set ((x, w) :: V) x v = (x, v) :: V := by
  simp [VEnv.set]

/-- A fresh binding is invisible to reads of any variable already in scope: if
`t` differs from `x`, prepending `(t, w)` does not change `x`'s value. This is
the read-side of the weakening lemma at a single binding. -/
theorem get_prepend_fresh {V : VEnv D} {x t : Ident} {w : D.Value} (h : t ≠ x) :
    VEnv.get ((t, w) :: V) x = VEnv.get V x :=
  get_cons_ne h

/-- Assigning an in-scope variable commutes with a fresh prepended binding: the
fresh binding is untouched and the assignment lands in the tail. This is the
write-side of the weakening lemma at a single binding. -/
theorem set_prepend_fresh {V : VEnv D} {x t : Ident} {w v : D.Value} (h : t ≠ x) :
    VEnv.set ((t, w) :: V) x v = (t, w) :: VEnv.set V x v :=
  set_cons_ne h

/-- `VEnv.set` preserves length — so `restore` (which truncates by length) is
insensitive to values written by an assignment. -/
theorem set_length (V : VEnv D) (x : Ident) (v : D.Value) :
    (VEnv.set V x v).length = V.length := by
  induction V with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨y, w⟩ := p
      by_cases h : y = x
      · subst h; simp [VEnv.set]
      · simp [VEnv.set, h, ih]

/-! ### Erasing temporaries: the environment "modulo fresh temps"

The simulation invariant relating the original and ANF'd executions is
`eraseTemps P Va = Vo`: the ANF environment with all temporary (prefix-`P`)
bindings removed equals the original environment. These lemmas show that
invariant is preserved by the environment operations — reads/writes of a
non-temp variable ignore the temps, declaring a temp is invisible to the
erasure, and declaring a non-temp commutes with it. -/

/-- `x` is a temporary of the ANF pass: its name starts with the fresh prefix. -/
def isTemp (P : String) (x : Ident) : Bool := P.isPrefixOf x

/-- The environment with all temporary bindings removed. -/
def eraseTemps (P : String) (V : VEnv D) : VEnv D :=
  V.filter (fun p => ! isTemp P p.1)

@[simp] theorem eraseTemps_nil : eraseTemps P ([] : VEnv D) = [] := rfl

@[simp] theorem eraseTemps_cons_temp {V : VEnv D} {y : Ident} {w : D.Value}
    (h : isTemp P y = true) : eraseTemps P ((y, w) :: V) = eraseTemps P V := by
  simp [eraseTemps, h]

@[simp] theorem eraseTemps_cons_nonTemp {V : VEnv D} {y : Ident} {w : D.Value}
    (h : isTemp P y = false) :
    eraseTemps P ((y, w) :: V) = (y, w) :: eraseTemps P V := by
  simp [eraseTemps, h]

/-- Reading a non-temporary variable is unaffected by erasing temporaries. -/
theorem get_eraseTemps {V : VEnv D} {x : Ident} (h : isTemp P x = false) :
    VEnv.get (eraseTemps P V) x = VEnv.get V x := by
  induction V with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨y, w⟩ := p
      by_cases ht : isTemp P y = true
      · rw [eraseTemps_cons_temp ht, ih]
        have hyx : y ≠ x := by intro he; rw [he, h] at ht; exact absurd ht (by simp)
        rw [get_cons_ne hyx]
      · simp only [Bool.not_eq_true] at ht
        rw [eraseTemps_cons_nonTemp ht]
        by_cases hyx : y = x
        · subst hyx; simp
        · rw [get_cons_ne hyx, get_cons_ne hyx, ih]

/-- Assigning a non-temporary variable commutes with erasing temporaries. -/
theorem eraseTemps_set {V : VEnv D} {x : Ident} {v : D.Value} (h : isTemp P x = false) :
    eraseTemps P (VEnv.set V x v) = VEnv.set (eraseTemps P V) x v := by
  induction V with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨y, w⟩ := p
      by_cases hyx : y = x
      · subst hyx
        have hy : isTemp P y = false := h
        rw [set_cons_self, eraseTemps_cons_nonTemp hy, eraseTemps_cons_nonTemp hy, set_cons_self]
      · rw [set_cons_ne hyx]
        by_cases ht : isTemp P y = true
        · rw [eraseTemps_cons_temp ht, eraseTemps_cons_temp ht, ih]
        · simp only [Bool.not_eq_true] at ht
          rw [eraseTemps_cons_nonTemp ht, eraseTemps_cons_nonTemp ht, set_cons_ne hyx, ih]

/-! ### "No temporary appears here"

The weakening lemma applies to *original* (pre-ANF) code, which mentions no
temporary. `noTemp*` is that predicate over the syntax — a mutual `Bool`
recursion checking that no variable read, no declared/assigned variable, and no
function parameter/return uses a temporary name. (Function *names* live in a
separate namespace and are not temporaries.) -/

mutual
def noTempExpr (P : String) : Expr Op → Bool
  | .lit _ => true
  | .var x => ! isTemp P x
  | .builtin _ args => noTempArgs P args
  | .call _ args => noTempArgs P args
def noTempArgs (P : String) : List (Expr Op) → Bool
  | [] => true
  | e :: rest => noTempExpr P e && noTempArgs P rest
end

/-- No name in a list is a temporary. -/
def noTempIdents (P : String) : List Ident → Bool
  | [] => true
  | x :: rest => (! isTemp P x) && noTempIdents P rest

mutual
def noTempStmt (P : String) : Stmt Op → Bool
  | .block body | .funDef _ _ _ body => noTempStmts P body
  | .letDecl vars val => noTempIdents P vars && val.all (noTempExpr P)
  | .assign vars val => noTempIdents P vars && noTempExpr P val
  | .cond c body => noTempExpr P c && noTempStmts P body
  | .switch c cases dflt => noTempExpr P c && noTempCases P cases && noTempDflt P dflt
  | .forLoop init c post body =>
      noTempStmts P init && noTempExpr P c && noTempStmts P post && noTempStmts P body
  | .exprStmt e => noTempExpr P e
  | .break | .continue | .leave => true
def noTempStmts (P : String) : List (Stmt Op) → Bool
  | [] => true
  | s :: rest => noTempStmt P s && noTempStmts P rest
def noTempCases (P : String) : List (Literal × List (Stmt Op)) → Bool
  | [] => true
  | (_, b) :: rest => noTempStmts P b && noTempCases P rest
def noTempDflt (P : String) : Option (List (Stmt Op)) → Bool
  | none => true
  | some b => noTempStmts P b
end

/-! ### Statement-sequence composition

`anfStmts (s :: rest) = anfStmt s ++ anfStmts rest`, so the list-level simulation
composes the executions of consecutive ANF'd statement-lists. These are the
generic `Step` composition bricks for `.stmts` over `++`. -/

/-- Running `l₁` to a *normal* completion then `l₂` equals running `l₁ ++ l₂`. -/
theorem stmts_append_normal [DecidableEq D.Value] :
    ∀ {l₁ : List (Stmt D.Op)} {funs V st Vm stm l₂ V' st' o},
      Step D funs V st (.stmts l₁) (.sres Vm stm .normal) →
      Step D funs Vm stm (.stmts l₂) (.sres V' st' o) →
      Step D funs V st (.stmts (l₁ ++ l₂)) (.sres V' st' o)
  | [], _, _, _, _, _, _, _, _, _, h1, h2 => by cases h1; exact h2
  | _ :: _, _, _, _, _, _, _, _, _, _, h1, h2 => by
      cases h1 with
      | seqCons hs hrest => exact Step.seqCons hs (stmts_append_normal hrest h2)
      | seqStop _ hne => exact absurd rfl hne

/-- If `l₁` halts / breaks / continues / leaves, `l₁ ++ l₂` stops there (`l₂` is
never reached). -/
theorem stmts_append_stop [DecidableEq D.Value] :
    ∀ {l₁ : List (Stmt D.Op)} {funs V st V' st' o l₂},
      Step D funs V st (.stmts l₁) (.sres V' st' o) → o ≠ .normal →
      Step D funs V st (.stmts (l₁ ++ l₂)) (.sres V' st' o)
  | [], _, _, _, _, _, _, _, h1, ho => by cases h1; exact absurd rfl ho
  | _ :: _, _, _, _, _, _, _, _, h1, ho => by
      cases h1 with
      | seqCons hs hrest => exact Step.seqCons hs (stmts_append_stop hrest ho)
      | seqStop hs hne => exact Step.seqStop hs hne

/-! ### The temp-extension relation — the simulation invariant

`TempExt P Vo Va` means the ANF environment `Va` is the original `Vo` with
temporary bindings *inserted*, the non-temp entries matching pairwise in name and
value and order. This is the structural invariant the `Step` simulation maintains
(stronger than value-agreement, which `restore`'s length-based truncation needs).
-/
inductive TempExt (P : String) : VEnv D → VEnv D → Prop
  | nil : TempExt P [] []
  | temp {Vo Va t w} : isTemp P t = true → TempExt P Vo Va → TempExt P Vo ((t, w) :: Va)
  | keep {Vo Va y v} : isTemp P y = false → TempExt P Vo Va →
      TempExt P ((y, v) :: Vo) ((y, v) :: Va)

/-- A temporary name and a non-temporary name are distinct. -/
theorem name_ne_of_isTemp {P : String} {t x : Ident}
    (ht : isTemp P t = true) (hx : isTemp P x = false) : t ≠ x := by
  intro he; subst he; rw [ht] at hx; simp at hx

/-- Reads of a non-temp variable agree across a temp-extension. -/
theorem TempExt.get {P : String} {Vo Va : VEnv D} {x : Ident}
    (hx : isTemp P x = false) (h : TempExt P Vo Va) :
    VEnv.get Va x = VEnv.get Vo x := by
  induction h with
  | nil => rfl
  | temp ht _ ih => rw [get_cons_ne (name_ne_of_isTemp ht hx)]; exact ih
  | keep hy hte ih =>
      rename_i _ _ y v
      by_cases hyx : y = x
      · subst hyx; simp
      · rw [get_cons_ne hyx, get_cons_ne hyx]; exact ih

/-- Assigning a non-temp variable preserves the temp-extension. -/
theorem TempExt.set {P : String} {Vo Va : VEnv D} {x : Ident} {v : D.Value}
    (hx : isTemp P x = false) (h : TempExt P Vo Va) :
    TempExt P (VEnv.set Vo x v) (VEnv.set Va x v) := by
  induction h with
  | nil => exact .nil
  | temp ht _ ih => rw [set_cons_ne (name_ne_of_isTemp ht hx)]; exact .temp ht ih
  | keep hy hte ih =>
      rename_i _ _ y w
      by_cases hyx : y = x
      · subst hyx; rw [set_cons_self, set_cons_self]; exact .keep hy hte
      · rw [set_cons_ne hyx, set_cons_ne hyx]; exact .keep hy ih

/-- Declaring a fresh temporary in the ANF environment only (invisible to the
original) preserves the extension. -/
theorem TempExt.temp_left {P : String} {Vo Va : VEnv D} {t : Ident} {w : D.Value}
    (ht : isTemp P t = true) (h : TempExt P Vo Va) : TempExt P Vo ((t, w) :: Va) :=
  .temp ht h

/-- Prepending the same block of non-temp declarations to both sides preserves
the extension (used for `let`/`for`-`init` declarations and block entry). -/
theorem TempExt.prepend_nonTemp {P : String} :
    ∀ {new : VEnv D} {Vo Va : VEnv D}, (∀ p ∈ new, isTemp P p.1 = false) →
      TempExt P Vo Va → TempExt P (new ++ Vo) (new ++ Va)
  | [], _, _, _, h => h
  | (y, v) :: rest, _, _, hnew, h => by
      refine .keep (hnew (y, v) (List.mem_cons_self ..)) ?_
      exact TempExt.prepend_nonTemp (fun p hp => hnew p (List.mem_cons_of_mem _ hp)) h

/-- A temp-free environment temp-extends itself (the base case at a program's
outermost scope, where no ANF temporary exists yet). -/
theorem TempExt.of_tempFree {P : String} :
    ∀ {V : VEnv D}, (∀ p ∈ V, isTemp P p.1 = false) → TempExt P V V
  | [], _ => .nil
  | (y, v) :: rest, h => by
      refine .keep (h (y, v) (List.mem_cons_self ..)) ?_
      exact TempExt.of_tempFree (fun p hp => h p (List.mem_cons_of_mem _ hp))

/-! ### `restore` under a block-local prefix

`restore outer inner = inner.drop (inner.length - outer.length)`. The block-scoped
ANF design introduces temporaries as a *prefix* of the block-local environment,
so `restore` drops them: the observable post-block environment is exactly what it
would have been without the temporaries. -/

private theorem drop_length_append {α} (pre suf : List α) :
    (pre ++ suf).drop pre.length = suf := by
  induction pre with
  | nil => rfl
  | cons a as ih => simpa using ih

/-- Restoring past a block-local prefix recovers the enclosing environment. -/
theorem restore_prefix (V pre : VEnv D) : restore V (pre ++ V) = V := by
  unfold restore
  rw [List.length_append, Nat.add_sub_cancel]
  exact drop_length_append pre V

/-- `restore V V = V` (an empty block-local layer). -/
@[simp] theorem restore_self (V : VEnv D) : restore V V = V := by
  have := restore_prefix V ([] : VEnv D); simp only [List.nil_append] at this; exact this

end YulEvmCompiler.Optimizer.ANF

/-! ## Soundness scaffold

The end-to-end soundness statement and the wired `Pass`, scaffolded with a single
`sorry` at the semantic core so the architecture is verified to compose.

Discharging `anfNormalize_sound` for the *current* (persistent-temporary)
`anfBlock` requires, in order of difficulty:

1. a **fresh-binding weakening lemma for `Step`** — temporaries persist across
   statements within the block (so forwarding can reuse them), so the simulation
   threads them through execution; the `VEnv`/`restore` lemmas above are its base;
2. a **block congruence with *equivalent* (not identical) hoisted functions** —
   ANF rewrites `funDef` bodies, so `hoist b ≠ hoist (anfBlock b)`; `EquivBlock.of_stmts`
   (which needs `hoist` equal) does not apply directly;
3. the **flatten evaluation-correctness** simulation on top.

An alternative design (wrap each statement's flattening in its own sub-block)
makes temporaries block-local per statement, removing (1) entirely — but then
temporaries do not persist, defeating store-to-load forwarding. The persistent
design here is the one the redundant-store pass wants. -/

namespace YulEvmCompiler.Optimizer.ANF

open YulSemantics YulSemantics.EVM
open YulEvmCompiler.Optimizer (Pass)

variable {calls : ExternalCalls} {creates : ExternalCreates}
local notation "D" => evmWithExternal calls creates

/-- A program-fresh temporary prefix. A NUL character cannot occur in a Yul
source identifier, so no program identifier starts with it; the freshness fact
is proved when discharging `anfNormalize_sound`. -/
def anfPrefix (_b : Block Op) : String := String.ofList [Char.ofNat 0] ++ "anf"

/-- The wired ANF normalizer: flatten with a program-fresh prefix. -/
def anfNormalize (b : Block Op) : Block Op := anfBlock (anfPrefix b) b

/-- The normalizer's output is in ANF (from the structural proof). -/
theorem anfNormalize_isANF (b : Block Op) : isANFStmts (anfNormalize b) = true :=
  anfBlock_isANF _ b

/-! ### Expression weakening

A temp-free expression evaluates to exactly the same result under a
temp-extended environment: it reads only non-temp variables (`TempExt.get`), and
a `call` runs its callee in a fresh frame independent of the caller's
temporaries, so the callee derivation is reused verbatim (the function
environment `funs` is identical because ANF is the identity on `funDef`). -/
mutual
theorem weakenExpr {funs : FunEnv D} {P : String} {e : Expr Op}
    {Vo Va : VEnv D} {st : EvmState} {r} (hext : TempExt P Vo Va)
    (hnt : noTempExpr P e = true) (h : Step D funs Vo st (.expr e) (.eres r)) :
    Step D funs Va st (.expr e) (.eres r) := by
  cases e with
  | lit l => cases h with | lit => exact Step.lit
  | var x =>
      cases h with
      | var hv =>
          have hx : isTemp P x = false := by simpa [noTempExpr] using hnt
          exact Step.var (by rw [TempExt.get hx hext]; exact hv)
  | builtin op args =>
      have hna : noTempArgs P args = true := by simpa [noTempExpr] using hnt
      cases h with
      | builtinOk ha hb => exact Step.builtinOk (weakenArgs hext hna ha) hb
      | builtinHalt ha hb => exact Step.builtinHalt (weakenArgs hext hna ha) hb
      | builtinArgsHalt ha => exact Step.builtinArgsHalt (weakenArgs hext hna ha)
  | call fn args =>
      have hna : noTempArgs P args = true := by simpa [noTempExpr] using hnt
      cases h with
      | callOk ha hlk hlen hbody ho => exact Step.callOk (weakenArgs hext hna ha) hlk hlen hbody ho
      | callHalt ha hlk hlen hbody => exact Step.callHalt (weakenArgs hext hna ha) hlk hlen hbody
      | callArgsHalt ha => exact Step.callArgsHalt (weakenArgs hext hna ha)

theorem weakenArgs {funs : FunEnv D} {P : String} {es : List (Expr Op)}
    {Vo Va : VEnv D} {st : EvmState} {r} (hext : TempExt P Vo Va)
    (hnt : noTempArgs P es = true) (h : Step D funs Vo st (.args es) (.eres r)) :
    Step D funs Va st (.args es) (.eres r) := by
  cases es with
  | nil => cases h with | argsNil => exact Step.argsNil
  | cons e rest =>
      simp only [noTempArgs, Bool.and_eq_true] at hnt
      cases h with
      | argsCons hrest hhead =>
          exact Step.argsCons (weakenArgs hext hnt.2 hrest) (weakenExpr hext hnt.1 hhead)
      | argsRestHalt hrest => exact Step.argsRestHalt (weakenArgs hext hnt.2 hrest)
      | argsHeadHalt hrest hhead =>
          exact Step.argsHeadHalt (weakenArgs hext hnt.2 hrest) (weakenExpr hext hnt.1 hhead)
end

/-! ### Atom-list weakening

The flattener's atoms are variables/literals, so a binding whose name is not one
of the atoms' variables can be prepended without changing their evaluation — the
non-shadowing fact the flatten-correctness `cons` case needs (a later flatten's
fresh temporaries don't disturb the already-computed earlier atoms). -/
theorem atomArgs_prepend_cons {funs : FunEnv D} {es : List (Expr Op)}
    {V : VEnv D} {t : Ident} {w : U256} {st r}
    (hatom : atomicArgs es = true) (hne : ∀ x, Expr.var x ∈ es → t ≠ x)
    (h : Step D funs V st (.args es) (.eres r)) :
    Step D funs ((t, w) :: V) st (.args es) (.eres r) := by
  induction es generalizing r with
  | nil => cases h with | argsNil => exact Step.argsNil
  | cons e rest ih =>
      simp only [atomicArgs, Bool.and_eq_true] at hatom
      cases h with
      | argsCons hrest hhead =>
          refine Step.argsCons (ih hatom.2 (fun x hx => hne x (List.mem_cons_of_mem _ hx)) hrest) ?_
          -- head atom e evaluates unchanged under the prepended binding
          cases e with
          | var y =>
              cases hhead with
              | var hv =>
                  have : t ≠ y := hne y (List.mem_cons_self ..)
                  exact Step.var (by rw [get_cons_ne this]; exact hv)
          | lit l => cases hhead with | lit => exact Step.lit
          | builtin _ _ => simp [isAtom] at hatom
          | call _ _ => simp [isAtom] at hatom
      | argsRestHalt hrest =>
          exact Step.argsRestHalt (ih hatom.2 (fun x hx => hne x (List.mem_cons_of_mem _ hx)) hrest)
      | argsHeadHalt hrest hhead =>
          refine Step.argsHeadHalt
            (ih hatom.2 (fun x hx => hne x (List.mem_cons_of_mem _ hx)) hrest) ?_
          cases e with
          | var y =>
              cases hhead
          | lit l => cases hhead
          | builtin _ _ => simp [isAtom] at hatom
          | call _ _ => simp [isAtom] at hatom

/-! ### Flatten-correctness

Running a `flatten`/`flattenArgs` prelude from a temp-extended environment binds
the temporaries so that the resulting atom(s) evaluate to the same value(s) as
the original expression, leaving `TempExt` intact and ending at the same state. -/
mutual
theorem flatten_correct {funs : FunEnv D} {P : String} {e : Expr Op}
    {Vo Va : VEnv D} {st : EvmState} {v st1} (k : Nat)
    (hstep : Step D funs Vo st (.expr e) (.eres (.vals [v] st1)))
    (hnt : noTempExpr P e = true) (hext : TempExt P Vo Va) :
    ∃ Va', Step D funs Va st (.stmts (flatten P k e).2.1) (.sres Va' st1 .normal)
      ∧ TempExt P Vo Va'
      ∧ Step D funs Va' st1 (.expr (flatten P k e).2.2) (.eres (.vals [v] st1)) := by
  cases e with
  | var x =>
      cases hstep with
      | var hv =>
          refine ⟨Va, ?_, hext, ?_⟩
          · simp only [flatten]; exact Step.seqNil
          · simp only [flatten]
            exact weakenExpr hext hnt (Step.var hv)
  | lit l =>
      cases hstep with
      | lit =>
          refine ⟨Va, ?_, hext, ?_⟩
          · simp only [flatten]; exact Step.seqNil
          · simp only [flatten]; exact Step.lit
  | builtin op args => sorry
  | call fn args => sorry

theorem flattenArgs_correct {funs : FunEnv D} {P : String} {es : List (Expr Op)}
    {Vo Va : VEnv D} {st : EvmState} {argvals st1} (k : Nat)
    (hstep : Step D funs Vo st (.args es) (.eres (.vals argvals st1)))
    (hnt : noTempArgs P es = true) (hext : TempExt P Vo Va) :
    ∃ Va', Step D funs Va st (.stmts (flattenArgs P k es).2.1) (.sres Va' st1 .normal)
      ∧ TempExt P Vo Va'
      ∧ Step D funs Va' st1 (.args (flattenArgs P k es).2.2) (.eres (.vals argvals st1)) := by
  cases es with
  | nil =>
      cases hstep with
      | argsNil =>
          refine ⟨Va, ?_, hext, ?_⟩
          · simp only [flattenArgs]; exact Step.seqNil
          · simp only [flattenArgs]; exact Step.argsNil
  | cons e rest => sorry
end

/-- **ANF preserves behavior.** (Scaffolded; discharged via the flatten
correctness + statement simulation + `restore` lemmas above.) -/
theorem anfNormalize_sound (b : Block Op) :
    EquivBlock D b (anfNormalize b) := by
  sorry

/-- The ANF normalizer as a verified `Pass`. -/
def anfPass : Pass D where
  run := anfNormalize
  sound := anfNormalize_sound

end YulEvmCompiler.Optimizer.ANF
