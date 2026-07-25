import YulIR.FrameStructuralSound

set_option warningAsError true
/-!
# YulIR.FrameSimplifySound — soundness of the `simplify` pass

`simplify` rewrites right-hand sides (constant folding via the dialect's own `stepOp`, plus algebraic
identities) and recurses structurally. Its soundness therefore reduces to a single RHS-level lemma,
`simplifyRhs_equiv : EquivRhs funs (simplifyRhs rhs) rhs`, lifted through statement/block
congruences and the pass's functional-induction principle.

* **Constant folding** (`constFold_equiv`) — a pure built-in on literal operands equals the folded
  literal, justified by the dialect's effect soundness (`NonWriting`/`NonHalting`/`NonReading`) plus
  state-independent definedness (`pure_defined`).
* **Algebraic identities** (`simplifyIdentity_equiv`) — each rewrite (`x+0`, `x*1`, `x-x`, `x&0`,
  shifts by/of zero, …) is a `BitVec` fact about the op's concrete `stepOp` evaluator.

Payoff: `simplify_equiv` (every block) and `simplify_program_run` (whole program).
-/

namespace YulIR.FinFrame.Sem

open YulSemantics (Outcome Literal BuiltinResult)
open YulSemantics.EVM (litValue stepOp evm bin effects EvmState)

/-! ### RHS equivalence and its statement congruences -/

/-- Two right-hand sides are equivalent when they evaluate identically from every store/state. -/
def EquivRhs (funs : Funs) {n} (r₁ r₂ : Rhs n) : Prop :=
  ∀ σ st res, ExecRhs funs σ st r₁ res ↔ ExecRhs funs σ st r₂ res

theorem EquivRhs.refl (funs : Funs) (r : Rhs n) : EquivRhs funs r r := fun _ _ _ => Iff.rfl

theorem EquivRhs.assign_congr {funs : Funs} {r₁ r₂ : Rhs n} (h : EquivRhs funs r₁ r₂)
    (ds : List (Fin n)) : EquivStmt funs (.assign ds r₁) (.assign ds r₂) := by
  intro σ st σ' st' o
  constructor
  · intro hs; cases hs with
    | assignOk hr   => exact .assignOk ((h _ _ _).mp hr)
    | assignHalt hr => exact .assignHalt ((h _ _ _).mp hr)
  · intro hs; cases hs with
    | assignOk hr   => exact .assignOk ((h _ _ _).mpr hr)
    | assignHalt hr => exact .assignHalt ((h _ _ _).mpr hr)

/-! ### Small helpers -/

/-- BEq on atoms reflects equality (proved by cases; `Literal`/`Fin` are lawful). -/
theorem atom_eq_of_beq {a b : Atom n} (h : (a == b) = true) : a = b := by
  cases a with
  | lit l1 => cases b with
    | lit l2 => have h2 : (l1 == l2) = true := h; exact congrArg _ (eq_of_beq h2)
    | slot i => exact Bool.noConfusion h
  | slot i1 => cases b with
    | lit l  => exact Bool.noConfusion h
    | slot i2 => have h2 : (i1 == i2) = true := h; exact congrArg _ (eq_of_beq h2)

/-- An atom that is the literal `0` evaluates to `0`. -/
theorem eval_isVal0 {a : Atom n} (σ : Store n) (h : a.isVal 0 = true) : evalAtom σ a = 0 := by
  cases a with
  | lit l  => simp only [Atom.isVal] at h; simpa [evalAtom] using eq_of_beq h
  | slot i => simp [Atom.isVal] at h

/-- An atom that is the literal `1` evaluates to `1`. -/
theorem eval_isVal1 {a : Atom n} (σ : Store n) (h : a.isVal 1 = true) : evalAtom σ a = 1 := by
  cases a with
  | lit l  => simp only [Atom.isVal] at h; simpa [evalAtom] using eq_of_beq h
  | slot i => simp [Atom.isVal] at h

/-- All-literal operands evaluate state-independently to the literals' values. -/
theorem allLits_map {args : List (Atom n)} {lits : List Literal}
    (h : allLits args = some lits) (σ : Store n) : args.map (evalAtom σ) = lits.map litValue := by
  induction args generalizing lits with
  | nil =>
      simp only [allLits, List.mapM_nil, Option.pure_def, Option.some.injEq] at h; subst h; rfl
  | cons a as ih =>
      cases a with
      | slot i => simp [allLits, Atom.litVal?] at h
      | lit l  =>
          simp only [allLits, List.mapM_cons, Atom.litVal?, Option.bind_eq_bind,
            Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
          obtain ⟨ls, rfl, as', hmap, rfl⟩ := h
          simp only [List.map_cons, evalAtom, litValue]
          exact congrArg (litValue l :: ·) (ih hmap)

/-- Purity in terms of the three effect flags. -/
theorem isPure_effects {op} (hp : Op.isPure op = true) :
    (effects op).reads = false ∧ (effects op).writes = false ∧ (effects op).halts = false := by
  simp only [Op.isPure, Bool.and_eq_true, Bool.not_eq_true'] at hp
  exact ⟨hp.1.1, hp.1.2, hp.2⟩

/-- For a pure op, whether `stepOp` is defined depends only on the arguments, not the state. -/
theorem pure_defined {op} (hp : Op.isPure op = true) {vals : List U256} {st st' : State}
    (h : (stepOp op vals st).isSome = true) : (stepOp op vals st').isSome = true := by
  cases op <;> simp_all [Op.isPure, effects, stepOp, bin, YulSemantics.EVM.un, YulSemantics.EVM.ter] <;>
    (revert h; split <;> simp_all)

/-- A pure built-in returns normally (`.ok`) without changing the state. -/
theorem pure_builtin_ok {op} (hp : Op.isPure op = true) {vals st r} (h : evm.Builtin op vals st r) :
    ∃ outs, r = .ok outs st := by
  obtain ⟨_, hw, hh⟩ := isPure_effects hp
  have hstate := YulSemantics.EVM.effects_sound.write op hw vals st r h
  have hhalt := YulSemantics.EVM.effects_sound.halt op hh vals st r h
  cases r with
  | halt st'' => simp [BuiltinResult.isHalt] at hhalt
  | ok outs st'' => exact ⟨outs, by simp_all [BuiltinResult.state]⟩

/-! ### Constant folding -/

/-- Folding a pure built-in on literal operands to its computed literal preserves evaluation. -/
theorem constFold_equiv {funs : Funs} {op} (hp : Op.isPure op = true) {args : List (Atom n)}
    {lits : List Literal} {l : Literal}
    (hlits : allLits args = some lits) (hfold : evalConst op lits = some l) :
    EquivRhs funs (.atom (.lit l)) (.builtin op args) := by
  have ES := YulSemantics.EVM.effects_sound
  obtain ⟨hread, _, _⟩ := isPure_effects hp
  -- extract the folded value: stepOp op vals₀ init = some (.ok [r0] _), l = .number r0.toNat
  simp only [evalConst] at hfold
  split at hfold
  case _ r0 stout heq =>
    simp only [Option.some.injEq] at hfold; subst hfold
    have hinit : evm.Builtin op (lits.map litValue) EvmState.init (.ok [r0] stout) := heq
    intro σ st res
    have hmap : args.map (evalAtom σ) = lits.map litValue := allLits_map hlits σ
    have hlit : litValue (Literal.number r0.toNat) = r0 := by simp [litValue]
    -- every result of the builtin at `st` is `.ok [r0] st`
    have hkey : ∀ res', evm.Builtin op (lits.map litValue) st res' ↔ res' = .ok [r0] st := by
      intro res'
      constructor
      · intro hb
        obtain ⟨outs, rfl⟩ := pure_builtin_ok hp hb
        have hr := ES.read op hread (lits.map litValue) EvmState.init st [r0] stout outs st hinit hb
        rw [hr]
      · intro hb; subst hb
        have hdef : (stepOp op (lits.map litValue) st).isSome = true :=
          pure_defined hp (show (stepOp op (lits.map litValue) EvmState.init).isSome = true by simp [heq])
        obtain ⟨res2, hres2⟩ := Option.isSome_iff_exists.mp hdef
        obtain ⟨outs, rfl⟩ := pure_builtin_ok hp (show evm.Builtin op _ st _ from hres2)
        have hr := ES.read op hread (lits.map litValue) EvmState.init st [r0] stout outs st hinit hres2
        rw [hr]; exact hres2
    constructor
    · intro h; cases h
      refine .builtin ?_
      show evm.Builtin op (args.map (evalAtom σ)) st _
      rw [hmap]; exact (hkey _).mpr (by simp [evalAtom, hlit])
    · intro h; cases h with
      | builtin hb =>
          rw [hmap] at hb
          have hres : res = .ok [litValue (Literal.number r0.toNat)] st := by
            rw [(hkey _).mp hb, hlit]
          rw [hres]; exact Step.atom
  all_goals simp at hfold

/-! ### Algebraic identities -/

/-- A binary op equals a folded atom, given the op's concrete evaluator and the value identity. -/
theorem binOp_equiv_atom {funs : Funs} {op} {f : U256 → U256 → U256}
    (hf : ∀ (vals : List U256) (st : State), stepOp op vals st = bin f vals st)
    {a b x : Atom n} (hval : ∀ σ : Store n, f (evalAtom σ a) (evalAtom σ b) = evalAtom σ x) :
    EquivRhs funs (.atom x) (.builtin op [a, b]) := by
  intro σ st res
  constructor
  · intro h; cases h
    refine .builtin ?_
    show stepOp op ([a, b].map (evalAtom σ)) st = some _
    rw [hf]; simp [bin, hval σ]
  · intro h; cases h with
    | builtin hb =>
        have hb' : stepOp op [evalAtom σ a, evalAtom σ b] st = some res := hb
        rw [hf] at hb'; simp only [bin, Option.some.injEq] at hb'
        rw [← hb', hval σ]
        exact Step.atom

/-- Every algebraic identity `simplify` applies preserves evaluation. -/
theorem simplifyIdentity_equiv (funs : Funs) (op) (args : List (Atom n)) :
    EquivRhs funs (simplifyIdentity op args (.builtin op args)) (.builtin op args) := by
  unfold simplifyIdentity
  repeat' split
  all_goals try exact EquivRhs.refl funs _
  all_goals apply binOp_equiv_atom (fun _ _ => rfl)
  all_goals intro σ
  all_goals rename_i hdec
  all_goals first
    | (rw [Bool.or_eq_true] at hdec
       rcases hdec with h | h <;> rw [eval_isVal0 σ h] <;> simp [evalAtom, litValue])
    | (obtain rfl := atom_eq_of_beq hdec; simp [evalAtom, litValue])
    | (rw [eval_isVal0 σ hdec]; simp [evalAtom, litValue])
    | (rw [eval_isVal1 σ hdec]; simp [evalAtom, litValue])

/-! ### `simplifyRhs` soundness -/

/-- The full RHS rewrite preserves evaluation: fold, identity, or unchanged. -/
theorem simplifyRhs_equiv (funs : Funs) (rhs : Rhs n) : EquivRhs funs (simplifyRhs rhs) rhs := by
  cases rhs with
  | atom a => exact EquivRhs.refl funs _
  | call fn args => exact EquivRhs.refl funs _
  | builtin op args =>
      simp only [simplifyRhs]
      split
      · exact EquivRhs.refl funs _                               -- impure ⇒ unchanged
      · rename_i hnp
        have hp : Op.isPure op = true := by revert hnp; cases Op.isPure op <;> simp
        split
        · rename_i lits hlits
          split
          · rename_i l hfold; exact constFold_equiv hp hlits hfold
          · exact simplifyIdentity_equiv funs op args
        · exact simplifyIdentity_equiv funs op args

/-! ### Whole-pass soundness of `simplify` -/

/-- **Constant folding + algebraic simplification preserves semantics**, for every block. -/
theorem simplifyBlock_equiv (funs : Funs) (b : Block n) :
    EquivBlock funs (simplifyBlock b) b := by
  refine simplifyBlock.induct
    (motive_1 := fun s => EquivStmt funs (simplifyStmt s) s)
    (motive_2 := fun df => EquivBlock funs ((simplifyDflt df).getD []) (df.getD []))
    (motive_3 := fun b => EquivBlock funs (simplifyBlock b) b)
    (motive_4 := fun cs =>
      List.Forall₂ (fun p q => p.1 = q.1 ∧ EquivBlock funs p.2 q.2) (simplifyCases cs) cs)
    ?assign ?cond ?switch ?loop ?stmt ?bnil ?bcons ?cnil ?ccons ?dnone ?dsome b
  case assign =>
    intro ds rhs; rw [simplifyStmt.eq_1]; exact EquivRhs.assign_congr (simplifyRhs_equiv funs rhs) ds
  case cond =>
    intro c body ih; rw [simplifyStmt.eq_2]; exact EquivStmt.cond_congr ih
  case switch =>
    intro c cs df ihcs ihdf; rw [simplifyStmt.eq_3]; exact EquivStmt.switch_congr ihcs ihdf
  case loop =>
    intro post body ihp ihb; rw [simplifyStmt.eq_4]; exact EquivStmt.loop_congr ihp ihb
  case stmt =>
    intro s hna hnc hns hnl; rw [simplifyStmt.eq_5 s hna hnc hns hnl]
    exact EquivStmt.refl funs s
  case bnil => exact EquivBlock.refl funs []
  case bcons =>
    intro s ss ihs ihss; rw [simplifyBlock.eq_2]; exact EquivBlock.consStmt ihs ihss
  case cnil => exact .nil
  case ccons =>
    intro l b rest ihb ihrest; rw [simplifyCases.eq_2]; exact List.Forall₂.cons ⟨rfl, ihb⟩ ihrest
  case dnone => exact EquivBlock.refl funs []
  case dsome => intro b ihb; rw [simplifyDflt.eq_2]; exact ihb

/-- `simplify` of `main` alone preserves the whole-program run. -/
theorem simplify_equiv (funs : Funs) (b : Block n) : EquivBlock funs (simplify b) b :=
  simplifyBlock_equiv funs b

/-- **Whole-program soundness of `simplify`**: applying it to `main` and every function body yields a
program with identical runs. -/
theorem simplify_program_run (p : Program) {st st' o} :
    Run p st st' o ↔ Run ⟨mapBodiesFuns simplify p.functions⟩ st st' o :=
  run_mapBodies simplify (fun F _ b => simplify_equiv F b)

end YulIR.FinFrame.Sem
