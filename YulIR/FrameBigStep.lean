import YulIR.FrameSem

set_option warningAsError true
/-!
# YulIR.FrameBigStep — relational big-step semantics for the frame IR

The executable `YulIR.FrameSem` interpreter is `partial`, so it carries no equations and is useless
in proofs. This module gives the **relational** big-step judgment that pass-soundness proofs are
stated against.

Following `yul-semantics`, it is a **single indexed inductive** `Step` over a sum `Code` of the
syntactic classes and a sum `Res` of result shapes — *not* a mutual family — precisely so that
derivation `induction` works (Lean's `induction` tactic does not support mutual inductives). The
five conceptual relations are recovered as abbreviations (`ExecRhs`/`ExecStmt`/`ExecBlock`/
`ExecLoop`).

Built-ins go through the dialect's relational `evm.Builtin`. The intrinsic frame keeps it clean: the
store `Fin n → U256` is total, and a call runs the callee body in a fresh `Store m`.
-/

namespace YulIR.FinFrame.Sem

open YulSemantics (Outcome BuiltinResult Literal)
open YulSemantics.EVM (evm litValue)

/-- The block a `switch` runs: the first case whose label matches, else the default (or empty). -/
def selectCase (cv : U256) (cases : List (Literal × Block n)) (dflt : Option (Block n)) : Block n :=
  match cases.find? (fun p => litValue p.1 == cv) with
  | some p => p.2
  | none   => dflt.getD []

/-- The syntactic classes the judgment ranges over (indexed by the frame size). -/
inductive Code (n : Nat)
  | rhs   (r : Rhs n)
  | stmt  (s : Stmt n)
  | stmts (b : Block n)
  | loop  (post body : Block n)

/-- Result shapes: an rhs result (a built-in result), or a statement/block result
(final store, state, control outcome). -/
inductive Res (n : Nat)
  | eres (r : BuiltinResult U256 State)
  | sres (σ : Store n) (st : State) (o : Outcome)

/-- The big-step judgment, as one indexed inductive so rule induction works. -/
inductive Step (funs : Funs) : {n : Nat} → Store n → State → Code n → Res n → Prop
  /- expressions -/
  | atom {n} {σ : Store n} {st a} :
      Step funs σ st (.rhs (.atom a)) (.eres (.ok [evalAtom σ a] st))
  | builtin {n} {σ : Store n} {st op args r} :
      evm.Builtin op (args.map (evalAtom σ)) st r →
      Step funs σ st (.rhs (.builtin op args)) (.eres r)
  | callNorm {n} {σ : Store n} {st fn args} {fdecl : Function}
      {σ' : Store fdecl.nslots} {st' o} :
      funs[fn]? = some fdecl →
      Step funs (seed fdecl.nslots fdecl.params (args.map (evalAtom σ))) st (.stmts fdecl.body)
        (.sres σ' st' o) →
      (o = .normal ∨ o = .leave) →
      Step funs σ st (.rhs (.call fn args)) (.eres (.ok (fdecl.rets.map σ') st'))
  | callHalt {n} {σ : Store n} {st fn args} {fdecl : Function}
      {σ' : Store fdecl.nslots} {st'} :
      funs[fn]? = some fdecl →
      Step funs (seed fdecl.nslots fdecl.params (args.map (evalAtom σ))) st (.stmts fdecl.body)
        (.sres σ' st' .halt) →
      Step funs σ st (.rhs (.call fn args)) (.eres (.halt st'))
  /- statements -/
  | writeOk {n} {σ : Store n} {st d rhs v vs st'} :
      Step funs σ st (.rhs rhs) (.eres (.ok (v :: vs) st')) →
      Step funs σ st (.stmt (.write d rhs)) (.sres (upd σ d v) st' .normal)
  | writeHalt {n} {σ : Store n} {st d rhs st'} :
      Step funs σ st (.rhs rhs) (.eres (.halt st')) →
      Step funs σ st (.stmt (.write d rhs)) (.sres σ st' .halt)
  | writeMany {n} {σ : Store n} {st ds rhs vs st'} :
      Step funs σ st (.rhs rhs) (.eres (.ok vs st')) →
      Step funs σ st (.stmt (.writeMany ds rhs)) (.sres (updMany σ ds vs) st' .normal)
  | writeManyHalt {n} {σ : Store n} {st ds rhs st'} :
      Step funs σ st (.rhs rhs) (.eres (.halt st')) →
      Step funs σ st (.stmt (.writeMany ds rhs)) (.sres σ st' .halt)
  | effectOk {n} {σ : Store n} {st rhs vs st'} :
      Step funs σ st (.rhs rhs) (.eres (.ok vs st')) →
      Step funs σ st (.stmt (.effect rhs)) (.sres σ st' .normal)
  | effectHalt {n} {σ : Store n} {st rhs st'} :
      Step funs σ st (.rhs rhs) (.eres (.halt st')) →
      Step funs σ st (.stmt (.effect rhs)) (.sres σ st' .halt)
  | condFalse {n} {σ : Store n} {st c body} :
      evalAtom σ c = 0 → Step funs σ st (.stmt (.cond c body)) (.sres σ st .normal)
  | condTrue {n} {σ : Store n} {st c body σ' st' o} :
      evalAtom σ c ≠ 0 → Step funs σ st (.stmts body) (.sres σ' st' o) →
      Step funs σ st (.stmt (.cond c body)) (.sres σ' st' o)
  | switch {n} {σ : Store n} {st c cases dflt σ' st' o} :
      Step funs σ st (.stmts (selectCase (evalAtom σ c) cases dflt)) (.sres σ' st' o) →
      Step funs σ st (.stmt (.switch c cases dflt)) (.sres σ' st' o)
  | loopS {n} {σ : Store n} {st post body σ' st' o} :
      Step funs σ st (.loop post body) (.sres σ' st' o) →
      Step funs σ st (.stmt (.loop post body)) (.sres σ' st' o)
  | brk {n} {σ : Store n} {st} :
      Step funs σ st (.stmt .«break») (.sres σ st .«break»)
  | cont {n} {σ : Store n} {st} :
      Step funs σ st (.stmt .«continue») (.sres σ st .«continue»)
  | lv {n} {σ : Store n} {st} :
      Step funs σ st (.stmt .leave) (.sres σ st .leave)
  /- blocks -/
  | nil {n} {σ : Store n} {st} :
      Step funs σ st (.stmts []) (.sres σ st .normal)
  | consNormal {n} {σ σ₁ σ₂ : Store n} {st st₁ st₂ s rest o} :
      Step funs σ st (.stmt s) (.sres σ₁ st₁ .normal) →
      Step funs σ₁ st₁ (.stmts rest) (.sres σ₂ st₂ o) →
      Step funs σ st (.stmts (s :: rest)) (.sres σ₂ st₂ o)
  | consStop {n} {σ σ₁ : Store n} {st st₁ s rest o} :
      Step funs σ st (.stmt s) (.sres σ₁ st₁ o) → o ≠ .normal →
      Step funs σ st (.stmts (s :: rest)) (.sres σ₁ st₁ o)
  /- loops -/
  | loopBrk {n} {σ σ' : Store n} {st st' post body} :
      Step funs σ st (.stmts body) (.sres σ' st' .«break») →
      Step funs σ st (.loop post body) (.sres σ' st' .normal)
  | loopLeave {n} {σ σ' : Store n} {st st' post body} :
      Step funs σ st (.stmts body) (.sres σ' st' .leave) →
      Step funs σ st (.loop post body) (.sres σ' st' .leave)
  | loopHalt {n} {σ σ' : Store n} {st st' post body} :
      Step funs σ st (.stmts body) (.sres σ' st' .halt) →
      Step funs σ st (.loop post body) (.sres σ' st' .halt)
  | loopStep {n} {σ σ₁ σ₂ σ₃ : Store n} {st st₁ st₂ st₃ post body ob o} :
      Step funs σ st (.stmts body) (.sres σ₁ st₁ ob) → (ob = .normal ∨ ob = .«continue») →
      Step funs σ₁ st₁ (.stmts post) (.sres σ₂ st₂ .normal) →
      Step funs σ₂ st₂ (.loop post body) (.sres σ₃ st₃ o) →
      Step funs σ st (.loop post body) (.sres σ₃ st₃ o)
  | loopPostStop {n} {σ σ₁ σ₂ : Store n} {st st₁ st₂ post body ob o} :
      Step funs σ st (.stmts body) (.sres σ₁ st₁ ob) → (ob = .normal ∨ ob = .«continue») →
      Step funs σ₁ st₁ (.stmts post) (.sres σ₂ st₂ o) → o ≠ .normal →
      Step funs σ st (.loop post body) (.sres σ₂ st₂ o)

/-! ### The conceptual relations -/

/-- Evaluate an rhs to a built-in result. -/
abbrev ExecRhs (funs : Funs) {n} (σ : Store n) (st : State) (r : Rhs n)
    (res : BuiltinResult U256 State) : Prop := Step funs σ st (.rhs r) (.eres res)
/-- Execute a statement. -/
abbrev ExecStmt (funs : Funs) {n} (σ : Store n) (st : State) (s : Stmt n)
    (σ' : Store n) (st' : State) (o : Outcome) : Prop := Step funs σ st (.stmt s) (.sres σ' st' o)
/-- Execute a block. -/
abbrev ExecBlock (funs : Funs) {n} (σ : Store n) (st : State) (b : Block n)
    (σ' : Store n) (st' : State) (o : Outcome) : Prop := Step funs σ st (.stmts b) (.sres σ' st' o)

/-! ### Equivalence (at a fixed function table) -/

/-- Pointwise statement equivalence: same results from every store and state. -/
def EquivStmt (funs : Funs) {n} (s₁ s₂ : Stmt n) : Prop :=
  ∀ σ st σ' st' o, ExecStmt funs σ st s₁ σ' st' o ↔ ExecStmt funs σ st s₂ σ' st' o

/-- Pointwise block equivalence. -/
def EquivBlock (funs : Funs) {n} (b₁ b₂ : Block n) : Prop :=
  ∀ σ st σ' st' o, ExecBlock funs σ st b₁ σ' st' o ↔ ExecBlock funs σ st b₂ σ' st' o

theorem EquivStmt.refl (funs : Funs) (s : Stmt n) : EquivStmt funs s s := fun _ _ _ _ _ => Iff.rfl
theorem EquivBlock.refl (funs : Funs) (b : Block n) : EquivBlock funs b b := fun _ _ _ _ _ => Iff.rfl

theorem EquivStmt.symm {funs : Funs} {s₁ s₂ : Stmt n} (h : EquivStmt funs s₁ s₂) :
    EquivStmt funs s₂ s₁ := fun σ st σ' st' o => (h σ st σ' st' o).symm
theorem EquivBlock.symm {funs : Funs} {b₁ b₂ : Block n} (h : EquivBlock funs b₁ b₂) :
    EquivBlock funs b₂ b₁ := fun σ st σ' st' o => (h σ st σ' st' o).symm
theorem EquivBlock.trans {funs : Funs} {b₁ b₂ b₃ : Block n}
    (h₁ : EquivBlock funs b₁ b₂) (h₂ : EquivBlock funs b₂ b₃) : EquivBlock funs b₁ b₃ :=
  fun σ st σ' st' o => (h₁ σ st σ' st' o).trans (h₂ σ st σ' st' o)

/-- Cons-congruence. -/
theorem EquivBlock.consStmt {funs : Funs} {s₁ s₂ : Stmt n} {r₁ r₂ : Block n}
    (hs : EquivStmt funs s₁ s₂) (hr : EquivBlock funs r₁ r₂) :
    EquivBlock funs (s₁ :: r₁) (s₂ :: r₂) := by
  intro σ st σ' st' o
  constructor
  · intro h
    cases h with
    | consNormal h1 h2 => exact .consNormal ((hs _ _ _ _ _).mp h1) ((hr _ _ _ _ _).mp h2)
    | consStop h1 hne  => exact .consStop ((hs _ _ _ _ _).mp h1) hne
  · intro h
    cases h with
    | consNormal h1 h2 => exact .consNormal ((hs _ _ _ _ _).mpr h1) ((hr _ _ _ _ _).mpr h2)
    | consStop h1 hne  => exact .consStop ((hs _ _ _ _ _).mpr h1) hne

/-! ### Whole-program runs -/

/-- Run a program: execute `main` from a zero-initialised frame; observe the final state and
outcome (the local store is discarded). -/
def Run (p : Program) (st : State) (st' : State) (o : Outcome) : Prop :=
  ∃ σ', ExecBlock p.functions (fun _ => 0) st p.main σ' st' o

/-- Equivalent `main` blocks (same function table) give identical runs. -/
theorem Run.of_equivMain {funs : Funs} {main₁ main₂ : Block m}
    (h : EquivBlock funs main₁ main₂) {st st' o} :
    Run ⟨funs, m, main₁⟩ st st' o ↔ Run ⟨funs, m, main₂⟩ st st' o := by
  simp only [Run]
  constructor
  · rintro ⟨σ', hexec⟩; exact ⟨σ', (h _ _ _ _ _).mp hexec⟩
  · rintro ⟨σ', hexec⟩; exact ⟨σ', (h _ _ _ _ _).mpr hexec⟩

end YulIR.FinFrame.Sem
