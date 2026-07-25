import YulIR.FrameStructuralSound

set_option warningAsError true
/-!
# YulIR.FrameDropSound — soundness of `dropUnreachableBlock`, and full `structural`

`dropUnreachableBlock` truncates a block at its first *terminator* statement (`break`/`continue`/
`leave`, or an `effect` of a halting built-in like `stop`/`return`/`revert`/`invalid`/
`selfdestruct`). Dropping the tail is sound because a terminator always yields a non-`normal`
outcome, so the block's `consStop` rule fires and the tail never runs.

The semantic core is `isTerminator_nonnormal`; the pass-level result is `dropUnreachable_equiv`
(functional induction on `dropUnreachableBlock`). Composing with `structuralBlock_equiv` gives the
soundness of the whole `structural` pass — `structural_equiv` and `structural_program_run'`.
-/

namespace YulIR.FinFrame.Sem

open YulSemantics (Outcome BuiltinResult)
open YulSemantics.EVM (stepOp evm guardStatic)

/-! ### A halting built-in always produces `.halt` -/

/-- Every halting op (`stop`/`return`/`revert`/`invalid`/`selfdestruct`) evaluates via `stepOp` to a
`.halt` result (or `none`), never an `.ok`. -/
theorem haltingBuiltin_isHalt {op : Op} (hop : haltingOp op = true) {args : List U256}
    {st : State} {r : BuiltinResult U256 State} (hb : evm.Builtin op args st r) :
    r.isHalt = true := by
  have hs : stepOp op args st = some r := hb
  cases op <;> (try (exact absurd hop (by decide)))
  clear hb
  all_goals
    simp only [stepOp, guardStatic] at hs
    split at hs <;> (try split at hs) <;>
      simp only [Option.some.injEq, reduceCtorEq] at hs <;>
      subst hs <;> rfl

/-! ### A terminator statement yields a non-`normal` outcome -/

/-- Executing a terminator statement always ends with a non-`normal` outcome. -/
theorem isTerminator_nonnormal {funs : Funs} {s : Stmt n} {σ st σ' st' o}
    (hterm : isTerminator s = true) (h : ExecStmt funs σ st s σ' st' o) : o ≠ .normal := by
  cases s with
  | «break»    => cases h; exact fun hc => by cases hc
  | «continue» => cases h; exact fun hc => by cases hc
  | leave      => cases h; exact fun hc => by cases hc
  | assign ds rhs =>
      cases rhs with
      | atom a       => simp [isTerminator] at hterm
      | call fn as   => simp [isTerminator] at hterm
      | builtin op as =>
          simp only [isTerminator] at hterm
          cases h with
          | assignHalt _ => exact fun hc => by cases hc
          | assignOk hrhs =>
              cases hrhs with
              | builtin hbltin =>
                  have hh := haltingBuiltin_isHalt hterm hbltin
                  simp [BuiltinResult.isHalt] at hh
  | cond c b         => simp [isTerminator] at hterm
  | switch c cs df   => simp [isTerminator] at hterm
  | loop post body   => simp [isTerminator] at hterm

/-! ### Dropping the tail after a terminator -/

/-- A statement that always ends non-`normal` makes its block tail unreachable. -/
theorem terminator_drop {funs : Funs} {s : Stmt n} (ss : Block n)
    (ht : ∀ σ st σ' st' o, ExecStmt funs σ st s σ' st' o → o ≠ .normal) :
    EquivBlock funs [s] (s :: ss) := by
  intro σ st σ' st' o
  constructor
  · intro h
    have hs := block_singleton_inv h
    exact .consStop hs (ht σ st σ' st' o hs)
  · intro h
    cases h with
    | consNormal hs _ => exact absurd rfl (ht _ _ _ _ _ hs)
    | consStop hs _   => exact block_singleton hs

/-! ### Whole-pass soundness of `dropUnreachableBlock` -/

/-- **Dropping unreachable code preserves semantics**, for every block. -/
theorem dropUnreachable_equiv (funs : Funs) (b : Block n) :
    EquivBlock funs (dropUnreachableBlock b) b := by
  refine dropUnreachableBlock.induct
    (motive_1 := fun s => EquivStmt funs (dropUnreachableStmt s) s)
    (motive_2 := fun df => EquivBlock funs ((dropUnreachableDflt df).getD []) (df.getD []))
    (motive_3 := fun b => EquivBlock funs (dropUnreachableBlock b) b)
    (motive_4 := fun cs =>
      List.Forall₂ (fun p q => p.1 = q.1 ∧ EquivBlock funs p.2 q.2) (dropUnreachableCases cs) cs)
    ?cond ?switch ?loop ?stmt ?bnil ?bterm ?bcons ?cnil ?ccons ?dnone ?dsome b
  -- dropUnreachableStmt cond
  case cond =>
    intro c b ihb
    rw [dropUnreachableStmt.eq_1]
    exact EquivStmt.cond_congr ihb
  -- dropUnreachableStmt switch
  case switch =>
    intro c cs df ihcs ihdf
    rw [dropUnreachableStmt.eq_2]
    exact EquivStmt.switch_congr ihcs ihdf
  -- dropUnreachableStmt loop
  case loop =>
    intro post body ihp ihb
    rw [dropUnreachableStmt.eq_3]
    exact EquivStmt.loop_congr ihp ihb
  -- dropUnreachableStmt other = s
  case stmt =>
    intro s hnc hns hnl
    rw [dropUnreachableStmt.eq_4 s hnc hns hnl]
    exact EquivStmt.refl funs s
  -- block nil
  case bnil => exact EquivBlock.refl funs []
  -- block cons, terminator: dropUnreachableBlock = [dropUnreachableStmt s]
  case bterm =>
    intro s ss hterm ihs
    rw [dropUnreachableBlock.eq_2, if_pos hterm]
    have ht : ∀ σ st σ' st' o, ExecStmt funs σ st s σ' st' o → o ≠ .normal :=
      fun σ st σ' st' o hexec => isTerminator_nonnormal hterm ((ihs σ st σ' st' o).mpr hexec)
    exact EquivBlock.trans (EquivStmt.toSingleton ihs) (terminator_drop ss ht)
  -- block cons, non-terminator: dropUnreachableBlock = dropUnreachableStmt s :: dropUnreachableBlock ss
  case bcons =>
    intro s ss hterm ihs ihss
    rw [dropUnreachableBlock.eq_2, if_neg hterm]
    exact EquivBlock.consStmt ihs ihss
  -- cases nil
  case cnil => exact .nil
  -- cases cons
  case ccons =>
    intro l b rest ihb ihrest
    rw [dropUnreachableCases.eq_2]
    exact List.Forall₂.cons ⟨rfl, ihb⟩ ihrest
  -- default none
  case dnone => exact EquivBlock.refl funs []
  -- default some
  case dsome =>
    intro b ihb
    rw [dropUnreachableDflt.eq_2]; exact ihb

/-! ### Full `structural` = `dropUnreachableBlock ∘ structuralBlock` -/

/-- **The whole `structural` pass preserves semantics**, for every block. -/
theorem structural_equiv (funs : Funs) (b : Block n) :
    EquivBlock funs (structural b) b :=
  EquivBlock.trans (dropUnreachable_equiv funs (structuralBlock b)) (structuralBlock_equiv funs b)

/-- **Whole-program soundness of `structural`**: applying `structural` to `main` and every function
body yields a program with identical runs. -/
theorem structural_program_run' (p : Program) {st st' o} :
    Run p st st' o ↔
      Run ⟨mapBodiesFuns structural p.functions, p.mainSlots, structural p.main⟩ st st' o :=
  run_mapBodies structural (fun F _ b => structural_equiv F b)

end YulIR.FinFrame.Sem
