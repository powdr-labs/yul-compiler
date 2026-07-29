import YulEvmCompiler.Optimizer.Spec.LocalPass
import YulEvmCompiler.Optimizer.Implementation.Frame
import YulEvmCompiler.Optimizer.Implementation.FunCongr
import YulSemantics.Dialect.EVM
set_option warningAsError true
/-!
# YulEvmCompiler.Optimizer.Implementation.CoalesceCopies

**Adjacent copy-chain coalescing (binder forwarding).** The statement inliner
leaves long same-level chains of singleton copies —

```yul
let a := p
let b := a
let c := b
```

— one `DUP` and one live operand-stack slot each, in loops that run tens of
thousands of iterations. Worse, the extra live locals push helper bodies over
the shared `liveMax ≤ 12` stack gates, which keeps gated copy propagation
*and* `InlineCalls` shut on exactly the hot Aave/Uniswap helpers (issue #65).

The rewrite: an adjacent pair

```yul
let x := rhs        (or `let x` zero-init)
let y := x
```

where `x` is never mentioned afterwards becomes

```yul
let y := rhs        (resp. `let y`)
```

processed left-to-right so a whole chain collapses in one invocation. Unlike
copy *substitution* (which can deepen a read past `DUP16`), binder forwarding
removes a live slot and never deepens any read, so it needs no depth gate.

## Soundness shape

`rhs` is evaluated in the same environment on both sides (same value, same
halt). The source then binds `x ↦ v` and reads it back into `y` (the read
cannot go wrong: `x` was just bound); the target binds only `y ↦ v`. From
there the source environment is the target environment with one extra dead
binding `(x, v)` inserted below the top — the `InsAt` insertion of
`Frame.lean`, transported through the mention-free suffix by
`frameAdd`/`frameRemove` and erased by the enclosing block's `restore`
(`InsAt.restore`). Every statement sequence in the semantics runs under a
block (`callOk` bodies, `if`/`switch`/loop bodies, the program root), so the
insertion never outlives its sequence.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM

variable {calls : ExternalCalls} {creates : ExternalCreates}

local notation "D" => evmWithExternal calls creates

/-! ### The transform -/

/-- One-level left-to-right pair coalescing: the adjacent pair
`let x := rhs; let y := x` (or the zero-init variant) merges to `let y := rhs`
when `x` is dead in the remainder. A chain collapses in one sweep because the
merged binder is re-examined against the next statement. -/
def ccPairs : List (Stmt Op) → List (Stmt Op)
  | .letDecl [x] rhs :: .letDecl [y] (some (.var x')) :: rest =>
      if x' = x ∧ x ≠ y ∧ stmtsMentions x rest = false then
        ccPairs (.letDecl [y] rhs :: rest)
      else
        .letDecl [x] rhs :: ccPairs (.letDecl [y] (some (.var x')) :: rest)
  | s :: rest => s :: ccPairs rest
  | [] => []
  termination_by ss => ss.length
  decreasing_by all_goals simp +arith

mutual

/-- Recurse into every sub-block, coalescing at each sequence level. A `for`
loop's `init` is left untouched: its declarations scope over the whole loop,
not just the `init` sequence. -/
def ccStmt : Stmt Op → Stmt Op
  | .block body => .block (ccPairs (ccStmts body))
  | .funDef n ps rs body => .funDef n ps rs (ccPairs (ccStmts body))
  | .cond c body => .cond c (ccPairs (ccStmts body))
  | .switch c cases dflt => .switch c (ccCases cases) (ccDflt dflt)
  | .forLoop init c post body =>
      .forLoop init c (ccPairs (ccStmts post)) (ccPairs (ccStmts body))
  | s => s

def ccStmts : List (Stmt Op) → List (Stmt Op)
  | [] => []
  | s :: rest => ccStmt s :: ccStmts rest

def ccCases : List (Literal × Block Op) → List (Literal × Block Op)
  | [] => []
  | (l, b) :: rest => (l, ccPairs (ccStmts b)) :: ccCases rest

def ccDflt : Option (Block Op) → Option (Block Op)
  | none => none
  | some b => some (ccPairs (ccStmts b))

end

/-- Coalesce adjacent copy chains in a top-level block. -/
def coalesceCopiesBlock (b : Block Op) : Block Op := ccPairs (ccStmts b)

/-! ### Insertion chains

The source side of a coalesced sequence carries one extra dead binding per
merged pair, each inserted at a depth at least the entry environment's length.
`restore` to the entry environment drops the whole region above that length,
so both sides restore identically. -/

/-- `InsChain n V₂ V₁`: `V₁` is `V₂` with finitely many extra bindings, each
inserted at depth `≥ n`. -/
inductive InsChain (n : Nat) : VEnv D → VEnv D → Prop
  | refl (V : VEnv D) : InsChain n V V
  | snoc {V₂ V₁ V₀ : VEnv D} {d : Nat} {x : Ident}
      {v : (evmWithExternal calls creates).Value} :
      InsChain n V₂ V₁ → InsAt d x v V₁ V₀ → n ≤ d →
      InsChain n V₂ V₀

theorem InsChain.mono {m n : Nat} {V₂ V₁ : VEnv D} (hmn : m ≤ n)
    (h : InsChain (calls := calls) (creates := creates) n V₂ V₁) : InsChain m V₂ V₁ := by
  induction h with
  | refl => exact .refl _
  | snoc _ hins hd ih => exact .snoc ih hins (Nat.le_trans hmn hd)

/-- One insertion at depth `≥ |V|` is invisible to `restore V`. -/
theorem insertion_restore_high {d : Nat} {x : Ident}
    {v : (evmWithExternal calls creates).Value}
    {V V₁ V₀ : VEnv D} (h : InsAt d x v V₁ V₀) (hd : V.length ≤ d) :
    restore V V₀ = restore V V₁ := by
  obtain ⟨above, below, rfl, rfl, rfl⟩ := h
  have hdrop : ∀ (pre tl : VEnv D) (k : Nat),
      List.drop (pre.length + k) (pre ++ tl) = List.drop k tl := by
    intro pre
    induction pre with
    | nil => intro tl k; simp
    | cons p ps ih =>
        intro tl k
        simp [Nat.succ_add, ih tl k]
  unfold restore
  simp only [List.length_append, List.length_cons]
  have h₀ : above.length + (below.length + 1) - V.length =
      (above ++ [(x, v)]).length + (below.length - V.length) := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have h₁ : above.length + below.length - V.length =
      above.length + (below.length - V.length) := by omega
  rw [h₀, h₁,
    show above ++ (x, v) :: below = (above ++ [(x, v)]) ++ below by simp,
    hdrop, hdrop]

/-- A whole chain of high insertions is invisible to `restore V`. -/
theorem InsChain.restore_eq {V V₂ V₁ : VEnv D}
    (h : InsChain (calls := calls) (creates := creates) V.length V₂ V₁) :
    restore V V₁ = restore V V₂ := by
  induction h with
  | refl => rfl
  | snoc _ hins hd ih => rw [insertion_restore_high hins hd, ih]

/-! ### The core sequence lemmas

Forward: a run of the source sequence yields a run of the coalesced sequence
whose final environment is the source's minus the merged pairs' dead bindings.
Backward: symmetric, via `frameAdd`. -/

private theorem letStep_inv {funs : FunEnv D} {V : VEnv D} {st : EvmState}
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

/-- Reading back a copy of a binding on top of the environment. -/
private theorem copy_read {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    {x : Ident} {v : U256} {V' : VEnv D} {st' : EvmState} {o : Outcome} {y : Ident}
    (h : Step D funs ((x, v) :: V) st (.stmt (.letDecl [y] (some (.var x))))
      (.sres V' st' o)) :
    V' = (y, v) :: (x, v) :: V ∧ st' = st ∧ o = .normal := by
  cases h with
  | letVal he hlen =>
      cases he with
      | var hv =>
          have hg : VEnv.get ((x, v) :: V) x = some v := by
            simp [VEnv.get]
          rw [hg] at hv
          injection hv with hv
          subst hv
          exact ⟨by simp, rfl, rfl⟩
  | letHalt he => nomatch he

/-- Forward direction of the pair coalescing, by the transform's recursion. -/
theorem ccPairs_fwd : ∀ (ss : List (Stmt Op)) {funs : FunEnv D} {V : VEnv D}
    {st : EvmState} {V₁ : VEnv D} {st₁ : EvmState} {o : Outcome},
    Step D funs V st (.stmts ss) (.sres V₁ st₁ o) →
    ∃ V₂, Step D funs V st (.stmts (ccPairs ss)) (.sres V₂ st₁ o) ∧
      InsChain (calls := calls) (creates := creates) V.length V₂ V₁ := by
  intro ss
  induction ss using ccPairs.induct with
  | case1 x rhs y x' rest hg ih =>
      obtain ⟨rfl, hxy, hm⟩ := hg
      intro funs V st V₁ st₁ o h
      rw [ccPairs.eq_1, if_pos ⟨rfl, hxy, hm⟩]
      cases h with
      | seqCons hlet1 htail =>
          rcases letStep_inv hlet1 with
            ⟨v, rfl, -, hshape⟩ | ⟨e, -, -, hno, -⟩
          · cases htail with
            | seqCons hlet2 hrest =>
                obtain ⟨rfl, rfl, -⟩ := copy_read hlet2
                have hins : InsAt V.length x' v ((y, v) :: V)
                    ((y, v) :: (x', v) :: V) :=
                  ⟨[(y, v)], V, rfl, rfl, rfl⟩
                obtain ⟨res₁, hstep₁, hrel⟩ := frameRemove hrest hins
                  (by simpa only [codeMentions] using hm)
                obtain ⟨V₁', rfl, hins'⟩ := ResRelAt.sres_right hrel
                rcases hshape with ⟨rfl, rfl, rfl⟩ | ⟨e, rfl, he⟩
                · obtain ⟨V₂, htgt, hchain⟩ :=
                    ih (Step.seqCons Step.letZero hstep₁)
                  exact ⟨V₂, htgt, .snoc hchain hins' (Nat.le_refl _)⟩
                · obtain ⟨V₂, htgt, hchain⟩ :=
                    ih (Step.seqCons (Step.letVal (vars := [y]) he rfl) hstep₁)
                  exact ⟨V₂, htgt, .snoc hchain hins' (Nat.le_refl _)⟩
            | seqStop hlet2 hne =>
                obtain ⟨-, -, hnorm⟩ := copy_read hlet2
                exact absurd hnorm hne
          · exact absurd hno.symm (by simp)
      | seqStop hlet1 hne =>
          rcases letStep_inv hlet1 with ⟨v, -, hnorm, -⟩ |
            ⟨e, rfl, rfl, rfl, hhalt⟩
          · exact absurd hnorm hne
          · obtain ⟨V₂, htgt, hchain⟩ :=
              ih (Step.seqStop (Step.letHalt (vars := [y]) hhalt)
                (by intro hc; cases hc))
            exact ⟨V₂, htgt, hchain⟩
  | case2 x rhs y x' rest hng ih =>
      intro funs V st V₁ st₁ o h
      rw [ccPairs.eq_1, if_neg hng]
      cases h with
      | seqCons hs htail =>
          obtain ⟨V₂, htgt, hchain⟩ := ih htail
          exact ⟨V₂, Step.seqCons hs htgt,
            hchain.mono (venvLen_mono hs rfl)⟩
      | seqStop hs hne =>
          exact ⟨V₁, Step.seqStop hs hne, .refl _⟩
  | case3 s rest hno ih =>
      intro funs V st V₁ st₁ o h
      rw [ccPairs.eq_2 s rest hno]
      cases h with
      | seqCons hs htail =>
          obtain ⟨V₂, htgt, hchain⟩ := ih htail
          exact ⟨V₂, Step.seqCons hs htgt,
            hchain.mono (venvLen_mono hs rfl)⟩
      | seqStop hs hne =>
          exact ⟨V₁, Step.seqStop hs hne, .refl _⟩
  | case4 =>
      intro funs V st V₁ st₁ o h
      rw [ccPairs.eq_3]
      cases h
      exact ⟨_, Step.seqNil, .refl _⟩

/-- Backward direction, via `frameAdd`. -/
theorem ccPairs_bwd : ∀ (ss : List (Stmt Op)) {funs : FunEnv D} {V : VEnv D}
    {st : EvmState} {V₂ : VEnv D} {st₁ : EvmState} {o : Outcome},
    Step D funs V st (.stmts (ccPairs ss)) (.sres V₂ st₁ o) →
    ∃ V₁, Step D funs V st (.stmts ss) (.sres V₁ st₁ o) ∧
      InsChain (calls := calls) (creates := creates) V.length V₂ V₁ := by
  intro ss
  induction ss using ccPairs.induct with
  | case1 x rhs y x' rest hg ih =>
      obtain ⟨rfl, hxy, hm⟩ := hg
      intro funs V st V₂ st₁ o h
      rw [ccPairs.eq_1, if_pos ⟨rfl, hxy, hm⟩] at h
      obtain ⟨V₁', hsrc', hchain⟩ := ih h
      cases hsrc' with
      | seqCons hlet_y htail =>
          rcases letStep_inv hlet_y with
            ⟨v, rfl, -, hshape⟩ | ⟨e, -, -, hno, -⟩
          · have hins : InsAt V.length x' v ((y, v) :: V)
                ((y, v) :: (x', v) :: V) :=
              ⟨[(y, v)], V, rfl, rfl, rfl⟩
            obtain ⟨res₂, hstep₂, hrel⟩ := frameAdd htail hins
              (by simpa only [codeMentions] using hm)
            obtain ⟨V₁, rfl, hins'⟩ := ResRelAt.sres hrel
            have hlet_y' : ∀ st2 : EvmState, Step D funs ((x', v) :: V) st2
                (.stmt (.letDecl [y] (some (.var x'))))
                (.sres ((y, v) :: (x', v) :: V) st2 .normal) := fun st2 =>
              Step.letVal («D» := D) (vars := [y])
                (Step.var (by simp [VEnv.get])) rfl
            rcases hshape with ⟨rfl, rfl, rfl⟩ | ⟨e, rfl, he⟩
            · exact ⟨V₁, Step.seqCons Step.letZero
                (Step.seqCons (hlet_y' _) hstep₂),
                .snoc hchain hins' (Nat.le_refl _)⟩
            · exact ⟨V₁, Step.seqCons (Step.letVal (vars := [x']) he rfl)
                (Step.seqCons (hlet_y' _) hstep₂),
                .snoc hchain hins' (Nat.le_refl _)⟩
          · exact absurd hno.symm (by simp)
      | seqStop hlet_y hne =>
          rcases letStep_inv hlet_y with ⟨v, -, hnorm, -⟩ |
            ⟨e, rfl, rfl, rfl, hhalt⟩
          · exact absurd hnorm hne
          · exact ⟨V₁', Step.seqStop
              (Step.letHalt (vars := [x']) hhalt) hne, hchain⟩
  | case2 x rhs y x' rest hng ih =>
      intro funs V st V₂ st₁ o h
      rw [ccPairs.eq_1, if_neg hng] at h
      cases h with
      | seqCons hs htail =>
          obtain ⟨V₁, hsrc, hchain⟩ := ih htail
          exact ⟨V₁, Step.seqCons hs hsrc,
            hchain.mono (venvLen_mono hs rfl)⟩
      | seqStop hs hne =>
          exact ⟨V₂, Step.seqStop hs hne, .refl _⟩
  | case3 s rest hno ih =>
      intro funs V st V₂ st₁ o h
      rw [ccPairs.eq_2 s rest hno] at h
      cases h with
      | seqCons hs htail =>
          obtain ⟨V₁, hsrc, hchain⟩ := ih htail
          exact ⟨V₁, Step.seqCons hs hsrc,
            hchain.mono (venvLen_mono hs rfl)⟩
      | seqStop hs hne =>
          exact ⟨V₂, Step.seqStop hs hne, .refl _⟩
  | case4 =>
      intro funs V st V₂ st₁ o h
      rw [ccPairs.eq_3] at h
      cases h
      exact ⟨_, Step.seqNil, .refl _⟩

/-! ### Pair coalescing preserves the hoisted scope -/

theorem ccPairs_hoist : ∀ ss : List (Stmt Op),
    hoist D (ccPairs ss) = hoist D ss := by
  intro ss
  induction ss using ccPairs.induct with
  | case1 x rhs y x' rest hg ih =>
      obtain ⟨rfl, hxy, hm⟩ := hg
      rw [ccPairs.eq_1, if_pos ⟨rfl, hxy, hm⟩]
      simpa [hoist] using ih
  | case2 x rhs y x' rest hng ih =>
      rw [ccPairs.eq_1, if_neg hng]
      simpa [hoist] using ih
  | case3 s rest hno ih =>
      rw [ccPairs.eq_2 s rest hno]
      simp only [hoist, List.filterMap_cons] at ih ⊢
      rw [ih]
  | case4 => rw [ccPairs.eq_3]

/-- Pair coalescing alone is a sound block rewrite: both sides hoist the same
scope, and the dead insertions vanish under the block's `restore`. -/
theorem ccPairs_blockEquiv (zz : Block Op) :
    EquivBlock D zz (ccPairs zz) := by
  intro funs V st V' st' o
  constructor
  · intro h
    cases h with
    | block hb =>
        obtain ⟨V₂, hstep, hchain⟩ := ccPairs_fwd zz hb
        rw [hchain.restore_eq]
        exact Step.block (by rw [ccPairs_hoist]; exact hstep)
  · intro h
    cases h with
    | block hb =>
        rw [ccPairs_hoist] at hb
        obtain ⟨V₁, hstep, hchain⟩ := ccPairs_bwd zz hb
        rw [← hchain.restore_eq]
        exact Step.block hstep

/-! ### Lifting through the syntax (nested blocks and function bodies) -/

mutual

/-- Every statement is equivalent to its coalesced form. -/
theorem ccStmt_equiv : ∀ s : Stmt Op, EquivStmt D s (ccStmt s)
  | .block body => by
      unfold ccStmt
      show EquivBlock D body (ccPairs (ccStmts body))
      exact (EquivBlock.of_stmts_funs
        (EquivStmts.of_forall₂ (ccStmts_forall2 body))
        (ccScopeRel body)).trans
        (ccPairs_blockEquiv (ccStmts body))
  | .funDef n ps rs body => by
      unfold ccStmt
      intro funs V st V' st' o
      constructor
      · intro h; cases h; exact Step.funDef
      · intro h; cases h; exact Step.funDef
  | .cond c body => by
      unfold ccStmt
      refine EquivStmt.cond_congr (@EquivExpr.refl (evmWithExternal calls creates) _ c) ?_
      exact (EquivBlock.of_stmts_funs
        (EquivStmts.of_forall₂ (ccStmts_forall2 body))
        (ccScopeRel body)).trans
        (ccPairs_blockEquiv (ccStmts body))
  | .switch c cases dflt => by
      unfold ccStmt
      refine EquivStmt.switch_congr (@EquivExpr.refl (evmWithExternal calls creates) _ c) (ccCases_forall2 cases) ?_
      cases dflt with
      | none => exact EquivBlock.refl _
      | some b =>
          unfold ccDflt
          exact (EquivBlock.of_stmts_funs
            (EquivStmts.of_forall₂ (ccStmts_forall2 b))
            (ccScopeRel b)).trans
            (ccPairs_blockEquiv (ccStmts b))
  | .forLoop init c post body => by
      unfold ccStmt
      refine EquivStmt.forLoop_congr init (@EquivExpr.refl (evmWithExternal calls creates) _ c) ?_ ?_
      · exact (EquivBlock.of_stmts_funs
          (EquivStmts.of_forall₂ (ccStmts_forall2 post))
          (ccScopeRel post)).trans
          (ccPairs_blockEquiv (ccStmts post))
      · exact (EquivBlock.of_stmts_funs
          (EquivStmts.of_forall₂ (ccStmts_forall2 body))
          (ccScopeRel body)).trans
          (ccPairs_blockEquiv (ccStmts body))
  | .letDecl xs v => by unfold ccStmt; exact EquivStmt.refl _
  | .assign xs e => by unfold ccStmt; exact EquivStmt.refl _
  | .exprStmt e => by unfold ccStmt; exact EquivStmt.refl _
  | .break => by unfold ccStmt; exact EquivStmt.refl _
  | .continue => by unfold ccStmt; exact EquivStmt.refl _
  | .leave => by unfold ccStmt; exact EquivStmt.refl _

/-- Sequence version, pairwise. -/
theorem ccStmts_forall2 : ∀ ss : List (Stmt Op),
    List.Forall₂ (EquivStmt D) ss (ccStmts ss)
  | [] => .nil
  | s :: rest => .cons (ccStmt_equiv s) (ccStmts_forall2 rest)

/-- Case-list version. -/
theorem ccCases_forall2 : ∀ cs : List (Literal × Block Op),
    List.Forall₂ (fun p q => p.1 = q.1 ∧ EquivBlock D p.2 q.2) cs (ccCases cs)
  | [] => .nil
  | (_l, b) :: rest =>
      .cons ⟨rfl, (EquivBlock.of_stmts_funs
          (EquivStmts.of_forall₂ (ccStmts_forall2 b))
          (ccScopeRel b)).trans
          (ccPairs_blockEquiv (ccStmts b))⟩
        (ccCases_forall2 rest)

/-- The hoisted scopes of a sequence and its statement-wise coalesced form are
`ScopeRel`-related (equal names and signatures, equivalent bodies). -/
theorem ccScopeRel : ∀ ss : List (Stmt Op),
    ScopeRel D (hoist D ss) (hoist D (ccStmts ss))
  | [] => .nil
  | .funDef n ps rs body :: rest => by
      unfold ccStmts ccStmt
      refine List.Forall₂.cons ⟨rfl, rfl, rfl, ?_⟩ (ccScopeRel rest)
      exact (EquivBlock.of_stmts_funs
        (EquivStmts.of_forall₂ (ccStmts_forall2 body))
        (ccScopeRel body)).trans
        (ccPairs_blockEquiv (ccStmts body))
  | .block body :: rest => by
      simpa [hoist, ccStmts, ccStmt] using ccScopeRel rest
  | .letDecl xs v :: rest => by
      simpa [hoist, ccStmts, ccStmt] using ccScopeRel rest
  | .assign xs e :: rest => by
      simpa [hoist, ccStmts, ccStmt] using ccScopeRel rest
  | .cond c body :: rest => by
      simpa [hoist, ccStmts, ccStmt] using ccScopeRel rest
  | .switch c cs dflt :: rest => by
      simpa [hoist, ccStmts, ccStmt] using ccScopeRel rest
  | .forLoop init c post body :: rest => by
      simpa [hoist, ccStmts, ccStmt] using ccScopeRel rest
  | .exprStmt e :: rest => by
      simpa [hoist, ccStmts, ccStmt] using ccScopeRel rest
  | .break :: rest => by
      simpa [hoist, ccStmts, ccStmt] using ccScopeRel rest
  | .continue :: rest => by
      simpa [hoist, ccStmts, ccStmt] using ccScopeRel rest
  | .leave :: rest => by
      simpa [hoist, ccStmts, ccStmt] using ccScopeRel rest

end

/-- Whole-block equivalence: statement-wise rewriting (with the function-scope
congruence), then pair coalescing at this level. -/
theorem ccBlock_equiv (body : Block Op) :
    EquivBlock D body (ccPairs (ccStmts body)) :=
  (EquivBlock.of_stmts_funs
    (EquivStmts.of_forall₂ (ccStmts_forall2 body))
    (ccScopeRel body)).trans
    (ccPairs_blockEquiv (ccStmts body))

/-- **Adjacent copy-chain coalescing** — the verified pass. -/
def coalesceCopies : LocalPass D where
  run := coalesceCopiesBlock
  sound := fun b => ccBlock_equiv b

@[simp] theorem coalesceCopies_run (b : Block Op) :
    (coalesceCopies (calls := calls) (creates := creates)).run b =
      ccPairs (ccStmts b) := rfl

end YulEvmCompiler.Optimizer
