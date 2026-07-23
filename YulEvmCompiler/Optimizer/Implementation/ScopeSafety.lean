import YulSemantics.BigStep
import YulEvmCompiler.Optimizer.Implementation.ANF
/-!
# YulEvmCompiler.Optimizer.Implementation.ScopeSafety

Reusable scope-safety meta-theory for the big-step semantics: **free variables**
of expressions, the fact that an **atom list never gets stuck** when its
variables are bound, and the **shape of a `let`-prelude's** resulting
environment (a prefix extension). These are the ingredients a source-to-source
pass needs when it hoists/reorders operands and must argue that a well-scoped
program's atoms remain evaluable.

They are dialect-generic and independent of any particular pass; the ANF
soundness (`ANFSound`) is the first consumer, but the redundant-store pass and
others will reuse the same facts.
-/

namespace YulEvmCompiler.Optimizer.ANF

open YulSemantics
open YulSemantics.EVM (Op)

/-! ### Free variables -/

mutual
/-- The variables read by an expression. -/
def freeVarsExpr : Expr Op → List Ident
  | .var x => [x]
  | .lit _ => []
  | .builtin _ args => freeVarsArgs args
  | .call _ args => freeVarsArgs args
/-- The variables read by an argument list. -/
def freeVarsArgs : List (Expr Op) → List Ident
  | [] => []
  | e :: rest => freeVarsExpr e ++ freeVarsArgs rest
end

@[simp] theorem freeVarsArgs_cons (e : Expr Op) (rest : List (Expr Op)) :
    freeVarsArgs (e :: rest) = freeVarsExpr e ++ freeVarsArgs rest := rfl

/-- A variable-atom of a list is one of its free variables. -/
theorem mem_freeVars_of_mem_var {es : List (Expr Op)} {x : Ident}
    (h : Expr.var x ∈ es) : x ∈ freeVarsArgs es := by
  induction es with
  | nil => simp at h
  | cons e rest ih =>
      rcases List.mem_cons.mp h with rfl | hrest
      · simp [freeVarsExpr]
      · exact List.mem_append.mpr (Or.inr (ih hrest))

open YulSemantics.EVM

variable {calls : ExternalCalls} {creates : ExternalCreates}
local notation "D" => evmWithExternal calls creates

/-! ### Atoms never get stuck when bound

An atom (variable/literal) reads no state and makes no call, so as long as every
variable-atom is bound, the list evaluates — to some values, at the same state.
This is the "progress for atoms" fact the reordering argument needs. -/

theorem atomArgs_eval_of_bound {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    {es : List (Expr Op)} (hatom : atomicArgs es = true)
    (hb : ∀ x, Expr.var x ∈ es → (VEnv.get V x).isSome = true) :
    ∃ vs, Step D funs V st (.args es) (.eres (.vals vs st)) := by
  induction es with
  | nil => exact ⟨[], Step.argsNil⟩
  | cons e rest ih =>
      simp only [atomicArgs, Bool.and_eq_true] at hatom
      obtain ⟨rvs, hrest⟩ := ih hatom.2 (fun x hx => hb x (List.mem_cons_of_mem _ hx))
      cases e with
      | var y =>
          obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hb y (List.mem_cons_self ..))
          exact ⟨v :: rvs, Step.argsCons hrest (Step.var hv)⟩
      | lit l => exact ⟨_, Step.argsCons hrest Step.lit⟩
      | builtin _ _ => simp [isAtom] at hatom
      | call _ _ => simp [isAtom] at hatom

/-- Prepending bindings never unbinds a variable: boundedness is preserved. -/
theorem get_append_isSome {V : VEnv D} {x : Ident} (ext : VEnv D)
    (h : (VEnv.get V x).isSome = true) : (VEnv.get (ext ++ V) x).isSome = true := by
  induction ext with
  | nil => simpa using h
  | cons p rest ih =>
      obtain ⟨y, w⟩ := p
      by_cases hyx : y = x
      · subst hyx; simp [VEnv.get]
      · rw [List.cons_append]
        simpa [VEnv.get, List.find?, hyx] using ih

/-! ### The shape of a `let`-prelude's environment

Executing a list of single-variable `let`s only ever prepends bindings, so the
resulting environment is a prefix extension of the starting one — whatever the
outcome (a halting `let` prepends nothing). This is what lets the enclosing
block's length-based `restore` discharge exactly the introduced temporaries. -/

theorem letPrelude_prefix {funs : FunEnv D} :
    ∀ (pre : List (Stmt Op)) {V V' : VEnv D} {st st' o},
      (∀ s ∈ pre, ∃ t rhs, s = .letDecl [t] (some rhs)) →
      Step D funs V st (.stmts pre) (.sres V' st' o) →
      ∃ ext, V' = ext ++ V
  | [], _, _, _, _, _, _, h => by cases h with | seqNil => exact ⟨[], rfl⟩
  | s :: rest, _, _, _, _, _, hOK, h => by
      obtain ⟨t, rhs, rfl⟩ := hOK s (List.mem_cons_self ..)
      cases h with
      | seqCons hs hrest =>
          cases hs with
          | letVal hval hlen =>
              rename_i vals
              obtain ⟨v, rfl⟩ : ∃ v, vals = [v] := by
                cases vals with
                | nil => simp at hlen
                | cons b tl => cases tl with
                  | nil => exact ⟨b, rfl⟩
                  | cons _ _ => simp at hlen
              obtain ⟨ext, rfl⟩ := letPrelude_prefix rest
                (fun s' hs' => hOK s' (List.mem_cons_of_mem _ hs')) hrest
              exact ⟨ext ++ [(t, v)], by simp⟩
      | seqStop hs hne =>
          cases hs with
          | letVal _ _ => exact absurd rfl hne
          | letHalt _ => exact ⟨[], rfl⟩

/-- A prelude of single-variable `let`s produces `normal` or `halt` — never a
loop control outcome (`break`/`continue`/`leave`). -/
theorem letPrelude_outcome {funs : FunEnv D} :
    ∀ (pre : List (Stmt Op)) {V V' : VEnv D} {st st' o},
      (∀ s ∈ pre, ∃ t rhs, s = .letDecl [t] (some rhs)) →
      Step D funs V st (.stmts pre) (.sres V' st' o) → o = .normal ∨ o = .halt
  | [], _, _, _, _, _, _, h => by cases h with | seqNil => exact Or.inl rfl
  | s :: rest, _, _, _, _, _, hOK, h => by
      obtain ⟨t, rhs, rfl⟩ := hOK s (List.mem_cons_self ..)
      cases h with
      | seqCons _ hrest =>
          exact letPrelude_outcome rest (fun s' hs' => hOK s' (List.mem_cons_of_mem _ hs')) hrest
      | seqStop hs hne =>
          cases hs with
          | letVal _ _ => exact absurd rfl hne
          | letHalt _ => exact Or.inr rfl

end YulEvmCompiler.Optimizer.ANF
