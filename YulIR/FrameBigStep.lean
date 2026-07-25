import YulIR.FrameSem

set_option warningAsError true
/-!
# YulIR.FrameBigStep — relational big-step semantics for the frame IR

The executable `YulIR.FrameSem` interpreter is `partial`, so it carries no equations and is useless
in proofs. This module gives the **relational** big-step judgment — a `Prop`-valued inductive — that
pass-soundness proofs are stated against (`YulIR.FrameSound`). Built-ins go through the dialect's
relational `evm.Builtin` (not the executable `stepOp`), so the semantics stays proof-friendly and
non-deterministic-ready.

The intrinsic frame keeps it clean: the store `Fin n → U256` is total (reads never fail), there is
no scoping, and a call simply runs the callee body in a fresh `Store m`.

Provides the judgment (`ExecRhs`/`ExecStmt`/`ExecBlock`/`ExecLoop`), pointwise **equivalence**
(`EquivStmt`/`EquivBlock`, at a fixed function table), reflexivity, the cons-congruence, and a
whole-program `Run` with its equivalence corollary for the `main` block.
-/

namespace YulIR.FinFrame.Sem

open YulSemantics (Outcome BuiltinResult Literal)
open YulSemantics.EVM (evm litValue)

/-- The block a `switch` runs: the first case whose label matches the scrutinee, else the default
(or the empty block). Pure, shared by the relation. -/
def selectCase (cv : U256) (cases : List (Literal × Block n)) (dflt : Option (Block n)) : Block n :=
  match cases.find? (fun p => litValue p.1 == cv) with
  | some p => p.2
  | none   => dflt.getD []

mutual
/-- Evaluate an rhs relationally to a built-in result. -/
inductive ExecRhs (funs : Funs) : {n : Nat} → Store n → State → Rhs n → BuiltinResult U256 State → Prop
  | atom {n} {σ : Store n} {st a} :
      ExecRhs funs σ st (.atom a) (.ok [evalAtom σ a] st)
  | builtin {n} {σ : Store n} {st op args r} :
      evm.Builtin op (args.map (evalAtom σ)) st r →
      ExecRhs funs σ st (.builtin op args) r
  | callNorm {n} {σ : Store n} {st fn args} {fdecl : Function}
      {σ' : Store fdecl.nslots} {st' o} :
      funs[fn]? = some fdecl →
      ExecBlock funs (seed fdecl.nslots fdecl.params (args.map (evalAtom σ))) st fdecl.body σ' st' o →
      (o = .normal ∨ o = .leave) →
      ExecRhs funs σ st (.call fn args) (.ok (fdecl.rets.map σ') st')
  | callHalt {n} {σ : Store n} {st fn args} {fdecl : Function}
      {σ' : Store fdecl.nslots} {st'} :
      funs[fn]? = some fdecl →
      ExecBlock funs (seed fdecl.nslots fdecl.params (args.map (evalAtom σ))) st fdecl.body σ' st' .halt →
      ExecRhs funs σ st (.call fn args) (.halt st')

/-- Execute a statement: initial store/state, statement, final store/state, control outcome. -/
inductive ExecStmt (funs : Funs) : {n : Nat} → Store n → State → Stmt n → Store n → State → Outcome → Prop
  | writeOk {n} {σ : Store n} {st d rhs v vs st'} :
      ExecRhs funs σ st rhs (.ok (v :: vs) st') →
      ExecStmt funs σ st (.write d rhs) (upd σ d v) st' .normal
  | writeHalt {n} {σ : Store n} {st d rhs st'} :
      ExecRhs funs σ st rhs (.halt st') →
      ExecStmt funs σ st (.write d rhs) σ st' .halt
  | writeMany {n} {σ : Store n} {st ds rhs vs st'} :
      ExecRhs funs σ st rhs (.ok vs st') →
      ExecStmt funs σ st (.writeMany ds rhs) (updMany σ ds vs) st' .normal
  | writeManyHalt {n} {σ : Store n} {st ds rhs st'} :
      ExecRhs funs σ st rhs (.halt st') →
      ExecStmt funs σ st (.writeMany ds rhs) σ st' .halt
  | effectOk {n} {σ : Store n} {st rhs vs st'} :
      ExecRhs funs σ st rhs (.ok vs st') →
      ExecStmt funs σ st (.effect rhs) σ st' .normal
  | effectHalt {n} {σ : Store n} {st rhs st'} :
      ExecRhs funs σ st rhs (.halt st') →
      ExecStmt funs σ st (.effect rhs) σ st' .halt
  | condFalse {n} {σ : Store n} {st c body} :
      evalAtom σ c = 0 → ExecStmt funs σ st (.cond c body) σ st .normal
  | condTrue {n} {σ : Store n} {st c body σ' st' o} :
      evalAtom σ c ≠ 0 → ExecBlock funs σ st body σ' st' o →
      ExecStmt funs σ st (.cond c body) σ' st' o
  | switch {n} {σ : Store n} {st c cases dflt σ' st' o} :
      ExecBlock funs σ st (selectCase (evalAtom σ c) cases dflt) σ' st' o →
      ExecStmt funs σ st (.switch c cases dflt) σ' st' o
  | loop {n} {σ : Store n} {st post body σ' st' o} :
      ExecLoop funs σ st post body σ' st' o →
      ExecStmt funs σ st (.loop post body) σ' st' o
  | brk {n} {σ : Store n} {st} :
      ExecStmt funs σ st .«break» σ st .«break»
  | cont {n} {σ : Store n} {st} :
      ExecStmt funs σ st .«continue» σ st .«continue»
  | lv {n} {σ : Store n} {st} :
      ExecStmt funs σ st .leave σ st .leave

/-- Execute a block, short-circuiting on a non-`normal` outcome. -/
inductive ExecBlock (funs : Funs) : {n : Nat} → Store n → State → Block n → Store n → State → Outcome → Prop
  | nil {n} {σ : Store n} {st} :
      ExecBlock funs σ st [] σ st .normal
  | consNormal {n} {σ σ₁ σ₂ : Store n} {st st₁ st₂ s rest o} :
      ExecStmt funs σ st s σ₁ st₁ .normal →
      ExecBlock funs σ₁ st₁ rest σ₂ st₂ o →
      ExecBlock funs σ st (s :: rest) σ₂ st₂ o
  | consStop {n} {σ σ₁ : Store n} {st st₁ s rest o} :
      ExecStmt funs σ st s σ₁ st₁ o → o ≠ .normal →
      ExecBlock funs σ st (s :: rest) σ₁ st₁ o

/-- Execute a loop `for {} 1 { post } { body }`. -/
inductive ExecLoop (funs : Funs) : {n : Nat} → Store n → State → Block n → Block n → Store n → State → Outcome → Prop
  | brk {n} {σ σ' : Store n} {st st' post body} :
      ExecBlock funs σ st body σ' st' .«break» →
      ExecLoop funs σ st post body σ' st' .normal
  | leaveB {n} {σ σ' : Store n} {st st' post body} :
      ExecBlock funs σ st body σ' st' .leave →
      ExecLoop funs σ st post body σ' st' .leave
  | haltB {n} {σ σ' : Store n} {st st' post body} :
      ExecBlock funs σ st body σ' st' .halt →
      ExecLoop funs σ st post body σ' st' .halt
  | step {n} {σ σ₁ σ₂ σ₃ : Store n} {st st₁ st₂ st₃ post body ob o} :
      ExecBlock funs σ st body σ₁ st₁ ob → (ob = .normal ∨ ob = .«continue») →
      ExecBlock funs σ₁ st₁ post σ₂ st₂ .normal →
      ExecLoop funs σ₂ st₂ post body σ₃ st₃ o →
      ExecLoop funs σ st post body σ₃ st₃ o
  | postStop {n} {σ σ₁ σ₂ : Store n} {st st₁ st₂ post body ob o} :
      ExecBlock funs σ st body σ₁ st₁ ob → (ob = .normal ∨ ob = .«continue») →
      ExecBlock funs σ₁ st₁ post σ₂ st₂ o → o ≠ .normal →
      ExecLoop funs σ st post body σ₂ st₂ o
end

/-! ### Equivalence (at a fixed function table) -/

/-- Pointwise equivalence of statements: same results from every store and state. -/
def EquivStmt (funs : Funs) {n} (s₁ s₂ : Stmt n) : Prop :=
  ∀ σ st σ' st' o, ExecStmt funs σ st s₁ σ' st' o ↔ ExecStmt funs σ st s₂ σ' st' o

/-- Pointwise equivalence of blocks. -/
def EquivBlock (funs : Funs) {n} (b₁ b₂ : Block n) : Prop :=
  ∀ σ st σ' st' o, ExecBlock funs σ st b₁ σ' st' o ↔ ExecBlock funs σ st b₂ σ' st' o

theorem EquivStmt.refl (funs : Funs) (s : Stmt n) : EquivStmt funs s s := fun _ _ _ _ _ => Iff.rfl
theorem EquivBlock.refl (funs : Funs) (b : Block n) : EquivBlock funs b b := fun _ _ _ _ _ => Iff.rfl

/-- Cons-congruence: equivalent heads and tails give equivalent blocks. -/
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
outcome (the frame store is local and discarded). -/
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
