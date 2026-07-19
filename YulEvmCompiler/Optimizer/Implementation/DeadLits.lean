import YulEvmCompiler.Optimizer.Implementation.Propagate
set_option warningAsError true
/-!
# YulEvmCompiler.Optimizer.Implementation.DeadLits

**Dead literal-binding elimination** — the removal companion to `Propagate`.
A singleton `let x := <literal>` (or zero-initialized `let x`) whose variable
never occurs afterward in its block is deleted outright.

## Why THIS removal fits the unchanged pointwise spec

General binding removal is unsound under the pointwise `EquivBlock` iff — for
`let x := e` with an arbitrary `e`, the two sides differ in *stuckness* on
environments where `e` cannot evaluate (this killed the `WellScoped` spec
change of PR #52). A **literal** binding has none of that freedom: it always
evaluates, in one step, to a total function of its syntax, changing no state.
So on every environment both programs run in lockstep — the only difference is
one extra binding, which (a) the remaining code never mentions and (b) the
enclosing block's `restore` drops anyway. The salvaged frame toolkit
(`Frame.lean`: `InsAt`, `frameAdd`/`frameRemove`) is exactly the bidirectional
simulation of "run `x`-free code with vs without an extra `(x,v)` binding",
and depth-from-the-bottom indexing makes the insertion stable under the
prepends/updates of subsequent execution, aligning at `restore`.

After `Propagate`, dead bindings are precisely of this shape (their uses were
substituted away, leaving literal right-hand sides), so the pipeline pair
`propagate → … → deadLits` is solc's rematerialize-then-prune, verified.

## Proof shape

Soundness is again proven for a *relation* (`DlRel`) with skip rules and the
deterministic transform inhabiting it — the same architecture as `Propagate`,
because the object path needs it: resolution creates literal bindings from
`dataoffset`/`datasize` lets, so the function removes more on resolved code;
the relation's skip rules absorb the mismatch and `DlRel` is closed under
resolution (`DeadLitsResolve.lean`). The semantic core is the *chain lemma*: a
`DlRel`-related pair is `EquivBlock`-equivalent under any common prefix,
removal steps discharged by `removeLit_equivBlock` (frame simulation +
`restore` alignment) and kept steps by the pointwise congruences.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM

variable {calls : ExternalCalls} {creates : ExternalCreates}

local notation "D" => evmWithExternal calls creates

/-! ### Sequence splitting and joining -/

/-- Split a run of `pre ++ suf` at the seam. -/
theorem stmts_append_fwd {funs : FunEnv D} {pre suf : List (Stmt Op)} {V st Vb st' o}
    (h : Step D funs V st (.stmts (pre ++ suf)) (.sres Vb st' o)) :
    (∃ V1 st1, Step D funs V st (.stmts pre) (.sres V1 st1 .normal) ∧
       Step D funs V1 st1 (.stmts suf) (.sres Vb st' o)) ∨
    (o ≠ .normal ∧ Step D funs V st (.stmts pre) (.sres Vb st' o)) := by
  induction pre generalizing V st with
  | nil => exact Or.inl ⟨V, st, Step.seqNil, h⟩
  | cons s pre' ih =>
      rw [List.cons_append] at h
      cases h with
      | seqCons hs htail =>
          rcases ih htail with ⟨V1, st1, hpre', hsuf⟩ | ⟨hne, hpre'⟩
          · exact Or.inl ⟨V1, st1, Step.seqCons hs hpre', hsuf⟩
          · exact Or.inr ⟨hne, Step.seqCons hs hpre'⟩
      | seqStop hs hne => exact Or.inr ⟨hne, Step.seqStop hs hne⟩

/-- Join: `pre` to `normal`, then `suf`, runs `pre ++ suf`. -/
theorem stmts_append_normal {funs : FunEnv D} {pre suf : List (Stmt Op)} {V st V1 st1 Vb st' o}
    (hpre : Step D funs V st (.stmts pre) (.sres V1 st1 .normal))
    (hsuf : Step D funs V1 st1 (.stmts suf) (.sres Vb st' o)) :
    Step D funs V st (.stmts (pre ++ suf)) (.sres Vb st' o) := by
  induction pre generalizing V st with
  | nil => cases hpre with | seqNil => exact hsuf
  | cons s pre' ih =>
      cases hpre with
      | seqCons hs hpre' => exact Step.seqCons hs (ih hpre')
      | seqStop _ hne => exact absurd rfl hne

/-- Join: a `pre` that stops early ignores the suffix. -/
theorem stmts_append_early {funs : FunEnv D} {pre suf : List (Stmt Op)} {V st Vb st' o}
    (hpre : Step D funs V st (.stmts pre) (.sres Vb st' o)) (hne : o ≠ .normal) :
    Step D funs V st (.stmts (pre ++ suf)) (.sres Vb st' o) := by
  induction pre generalizing V st with
  | nil => cases hpre with | seqNil => exact absurd rfl hne
  | cons s pre' ih =>
      cases hpre with
      | seqCons hs hpre' => exact Step.seqCons hs (ih hpre')
      | seqStop hs hne' => exact Step.seqStop hs hne'

/-! ### `restore` alignment across an insertion -/

/-- Restoring to a base that lies at or below the insertion point erases the
inserted binding: both sides restore to the same environment. -/
theorem restore_insAt_le {d : Nat} {x : Ident} {w : U256} {V1 V2 base : VEnv D}
    (h : InsAt d x w V1 V2) (hb : base.length ≤ d) :
    restore base V1 = restore base V2 := by
  obtain ⟨A, B, rfl, rfl, hBd⟩ := h
  have g1 : restore base (A ++ B) = B.drop (B.length - base.length) := by
    simp only [restore, List.length_append]
    rw [show A.length + B.length - base.length =
      A.length + (B.length - base.length) by omega]
    rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append]
    congr 1
    omega
  have g2 : restore base (A ++ (x, w) :: B) = B.drop (B.length - base.length) := by
    simp only [restore, List.length_append, List.length_cons]
    rw [show A.length + (B.length + 1) - base.length =
      A.length + ((B.length - base.length) + 1) by omega]
    rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append]
    rw [show A.length + ((B.length - base.length) + 1) - A.length =
      (B.length - base.length) + 1 by omega]
    rfl
  rw [g1, g2]

/-! ### The removable shape and its execution -/

/-- Is `s` a removable dead literal binding, given the rest of its block? -/
def removableLit : Stmt Op → List (Stmt Op) → Bool
  | .letDecl [x] none, rest => !stmtsMentions x rest
  | .letDecl [x] (some (.lit _)), rest => !stmtsMentions x rest
  | _, _ => false

/-- A literal `let` always executes: it binds one value, changes no state, and
yields `normal` — and that is its only behavior. -/
theorem let_lit_inv {x : Ident} {val : Option (Expr Op)} {funs : FunEnv D}
    {V : VEnv D} {st : EvmState} {V2 st2 o}
    (hval : val = none ∨ ∃ l, val = some (.lit l))
    (h : Step D funs V st (.stmt (.letDecl [x] val)) (.sres V2 st2 o)) :
    ∃ v, V2 = (x, v) :: V ∧ st2 = st ∧ o = .normal := by
  rcases hval with rfl | ⟨l, rfl⟩
  · cases h with
    | letZero => exact ⟨_, rfl, rfl, rfl⟩
  · cases h with
    | letVal he hlen =>
        cases he with
        | lit => exact ⟨_, rfl, rfl, rfl⟩
    | letHalt he => cases he

/-- ... and it always *can* execute. -/
theorem let_lit_run {x : Ident} {val : Option (Expr Op)} (funs : FunEnv D)
    (V : VEnv D) (st : EvmState)
    (hval : val = none ∨ ∃ l, val = some (.lit l)) :
    ∃ v, Step D funs V st (.stmt (.letDecl [x] val)) (.sres ((x, v) :: V) st .normal) := by
  rcases hval with rfl | ⟨l, rfl⟩
  · exact ⟨_, Step.letZero⟩
  · exact ⟨_, Step.letVal Step.lit rfl⟩

/-- Dropping a `letDecl` never changes the hoisted function scope. -/
theorem hoist_drop_let (pre rest : List (Stmt Op)) (x : Ident) (val : Option (Expr Op)) :
    hoist D (pre ++ .letDecl [x] val :: rest) = hoist D (pre ++ rest) := by
  unfold hoist
  rw [List.filterMap_append, List.filterMap_append, List.filterMap_cons]

/-! ### The core removal lemma -/

/-- **Removing one dead literal binding is invisible at block granularity.**
Both directions: the frame simulation carries the remaining (x-free) code
across the insertion, and `restore` erases the binding at block exit. -/
theorem removeLit_equivBlock {x : Ident} {val : Option (Expr Op)}
    {pre rest : List (Stmt Op)}
    (hval : val = none ∨ ∃ l, val = some (.lit l))
    (hm : stmtsMentions x rest = false) :
    EquivBlock D (pre ++ .letDecl [x] val :: rest) (pre ++ rest) := by
  have hh := hoist_drop_let (calls := calls) (creates := creates) pre rest x val
  intro funs V st V' st' o
  constructor
  · intro h
    cases h with
    | block hb =>
        rw [hh] at hb
        rcases stmts_append_fwd hb with ⟨V1, st1, hpre, hsuf⟩ | ⟨hne, hpre⟩
        · cases hsuf with
          | seqCons hlet htail =>
              obtain ⟨v, rfl, rfl, -⟩ := let_lit_inv hval hlet
              have hins : InsAt V1.length x v V1 ((x, v) :: V1) :=
                ⟨[], V1, rfl, rfl, rfl⟩
              obtain ⟨res1, hrest1, hrel⟩ := frameRemove htail hins
                (by simpa [codeMentions] using hm)
              obtain ⟨V1', rfl, hins'⟩ := hrel.sres_right
              have hjoin := stmts_append_normal hpre hrest1
              have hlen : V.length ≤ V1.length :=
                venvLen_mono hpre (by rfl)
              have hres : restore V V1' = restore V _ :=
                restore_insAt_le hins' hlen
              rw [← hres]
              exact Step.block hjoin
          | seqStop hlet hne =>
              obtain ⟨v, -, -, ho⟩ := let_lit_inv hval hlet
              exact absurd ho hne
        · exact Step.block (stmts_append_early hpre hne)
  · intro h
    cases h with
    | block hb =>
        rcases stmts_append_fwd hb with ⟨V1, st1, hpre, hsuf⟩ | ⟨hne, hpre⟩
        · obtain ⟨v, hlet⟩ := let_lit_run (x := x) (val := val) _ V1 st1 hval
          have hins : InsAt V1.length x v V1 ((x, v) :: V1) :=
            ⟨[], V1, rfl, rfl, rfl⟩
          obtain ⟨res2, hrest2, hrel⟩ := frameAdd hsuf hins
            (by simpa [codeMentions] using hm)
          obtain ⟨V2', rfl, hins'⟩ := hrel.sres
          have hjoin : Step D (hoist D (pre ++ Stmt.letDecl [x] val :: rest) :: funs)
              V st (.stmts (pre ++ Stmt.letDecl [x] val :: rest)) (.sres V2' st' o) := by
            rw [hh]
            exact stmts_append_normal hpre (Step.seqCons hlet hrest2)
          have hlen : V.length ≤ V1.length :=
            venvLen_mono hpre (by rfl)
          have hres : restore V _ = restore V V2' :=
            restore_insAt_le hins' hlen
          rw [hres]
          exact Step.block hjoin
        · refine Step.block ?_
          rw [hh]
          exact stmts_append_early hpre hne

/-! ### The removal relation -/

/-- `DlRel pc pc'`: `pc'` is `pc` with *some* valid subset of dead literal
bindings removed (and sub-blocks likewise related). `sameS` is the statement
skip rule; `dropSS` guards each removal by the literal shape and the
never-mentioned-afterward condition on the *original* rest. -/
inductive DlRel : PCode Op → PCode Op → Prop
  | sameS {s : Stmt Op} : DlRel (.stmt s) (.stmt s)
  | blockS {body body' : Block Op} :
      DlRel (.stmts body) (.stmts body') →
      DlRel (.stmt (.block body)) (.stmt (.block body'))
  | funDefS {n : Ident} {ps rs : List Ident} {body body' : Block Op} :
      DlRel (.stmts body) (.stmts body') →
      DlRel (.stmt (.funDef n ps rs body)) (.stmt (.funDef n ps rs body'))
  | condS {c : Expr Op} {body body' : Block Op} :
      DlRel (.stmts body) (.stmts body') →
      DlRel (.stmt (.cond c body)) (.stmt (.cond c body'))
  | switchS {c : Expr Op} {cases cases' : List (Literal × Block Op)}
      {dflt dflt' : Option (Block Op)} :
      DlRel (.cases cases) (.cases cases') →
      DlRel (.odflt dflt) (.odflt dflt') →
      DlRel (.stmt (.switch c cases dflt)) (.stmt (.switch c cases' dflt'))
  | forS {init : Block Op} {c : Expr Op} {post post' body body' : Block Op} :
      DlRel (.stmts post) (.stmts post') →
      DlRel (.stmts body) (.stmts body') →
      DlRel (.stmt (.forLoop init c post body)) (.stmt (.forLoop init c post' body'))
  | nilSS : DlRel (.stmts []) (.stmts [])
  | consSS {s s' : Stmt Op} {rest rest' : List (Stmt Op)} :
      DlRel (.stmt s) (.stmt s') → DlRel (.stmts rest) (.stmts rest') →
      DlRel (.stmts (s :: rest)) (.stmts (s' :: rest'))
  | dropSS {x : Ident} {val : Option (Expr Op)} {rest rest' : List (Stmt Op)} :
      (val = none ∨ ∃ l, val = some (.lit l)) →
      stmtsMentions x rest = false →
      DlRel (.stmts rest) (.stmts rest') →
      DlRel (.stmts (.letDecl [x] val :: rest)) (.stmts rest')
  | casesNil : DlRel (.cases []) (.cases [])
  | casesCons {l : Literal} {b b' : Block Op} {rest rest' : List (Literal × Block Op)} :
      DlRel (.stmts b) (.stmts b') → DlRel (.cases rest) (.cases rest') →
      DlRel (.cases ((l, b) :: rest)) (.cases ((l, b') :: rest'))
  | odfltNone : DlRel (.odflt none) (.odflt none)
  | odfltSome {b b' : Block Op} :
      DlRel (.stmts b) (.stmts b') →
      DlRel (.odflt (some b)) (.odflt (some b'))

/-! ### The transform, and it inhabits the relation -/

mutual

/-- Remove dead literal bindings, recursing into every sub-block (a `for`
loop's `init` is left untouched — its scope spans the whole loop). -/
def dlStmt : Stmt Op → Stmt Op
  | .block body => .block (dlStmts body)
  | .funDef n ps rs body => .funDef n ps rs (dlStmts body)
  | .cond c body => .cond c (dlStmts body)
  | .switch c cases dflt => .switch c (dlCases cases) (dlDflt dflt)
  | .forLoop init c post body => .forLoop init c (dlStmts post) (dlStmts body)
  | s => s

/-- Remove dead literal bindings from a statement sequence. -/
def dlStmts : List (Stmt Op) → List (Stmt Op)
  | [] => []
  | s :: rest =>
      if removableLit s rest then dlStmts rest
      else dlStmt s :: dlStmts rest

/-- Remove dead literal bindings from each `switch` case body. -/
def dlCases : List (Literal × Block Op) → List (Literal × Block Op)
  | [] => []
  | (l, b) :: rest => (l, dlStmts b) :: dlCases rest

/-- Remove dead literal bindings from a `switch` default. -/
def dlDflt : Option (Block Op) → Option (Block Op)
  | none => none
  | some b => some (dlStmts b)

end

/-- Unpack a positive removability test. -/
theorem removableLit_inv {s : Stmt Op} {rest : List (Stmt Op)}
    (h : removableLit s rest = true) :
    ∃ x val, s = .letDecl [x] val ∧ (val = none ∨ ∃ l, val = some (.lit l)) ∧
      stmtsMentions x rest = false := by
  unfold removableLit at h
  split at h
  · next x => exact ⟨x, none, rfl, Or.inl rfl, by simpa using h⟩
  · next x l => exact ⟨x, some (.lit l), rfl, Or.inr ⟨l, rfl⟩, by simpa using h⟩
  · cases h

mutual

/-- The statement transform inhabits the relation. -/
theorem dlStmt_rel : ∀ s : Stmt Op, DlRel (.stmt s) (.stmt (dlStmt s))
  | .block body => .blockS (dlStmts_rel body)
  | .funDef _ _ _ body => .funDefS (dlStmts_rel body)
  | .cond _ body => .condS (dlStmts_rel body)
  | .switch _ cases dflt => .switchS (dlCases_rel cases) (dlDflt_rel dflt)
  | .forLoop _ _ post body => .forS (dlStmts_rel post) (dlStmts_rel body)
  | .letDecl _ _ => .sameS
  | .assign _ _ => .sameS
  | .exprStmt _ => .sameS
  | .break => .sameS
  | .continue => .sameS
  | .leave => .sameS

/-- The sequence transform inhabits the relation. -/
theorem dlStmts_rel : ∀ ss : List (Stmt Op), DlRel (.stmts ss) (.stmts (dlStmts ss))
  | [] => .nilSS
  | s :: rest => by
      rw [dlStmts]
      by_cases h : removableLit s rest = true
      · obtain ⟨x, val, rfl, hval, hm⟩ := removableLit_inv h
        rw [if_pos h]
        exact .dropSS hval hm (dlStmts_rel rest)
      · rw [if_neg h]
        exact .consSS (dlStmt_rel s) (dlStmts_rel rest)

/-- The case-list transform inhabits the relation. -/
theorem dlCases_rel : ∀ cs : List (Literal × Block Op), DlRel (.cases cs) (.cases (dlCases cs))
  | [] => .casesNil
  | (_, b) :: rest => .casesCons (dlStmts_rel b) (dlCases_rel rest)

/-- The default transform inhabits the relation. -/
theorem dlDflt_rel : ∀ d : Option (Block Op), DlRel (.odflt d) (.odflt (dlDflt d))
  | none => .odfltNone
  | some b => .odfltSome (dlStmts_rel b)

end

/-! ### Soundness -/

/-- The per-class semantic claim of the removal relation. -/
def dlSound : PCode Op → PCode Op → Prop
  | .stmts ss, .stmts ss' =>
      ∀ pre : List (Stmt Op),
        EquivBlock (evmWithExternal calls creates) (pre ++ ss) (pre ++ ss')
  | .stmt s, .stmt s' =>
      EquivStmt (evmWithExternal calls creates) s s' ∧
        ScopeRel (evmWithExternal calls creates)
          (hoist (evmWithExternal calls creates) [s])
          (hoist (evmWithExternal calls creates) [s'])
  | .cases cs, .cases cs' =>
      List.Forall₂ (fun p q => p.1 = q.1 ∧
        EquivBlock (evmWithExternal calls creates) p.2 q.2) cs cs'
  | .odflt d, .odflt d' =>
      EquivBlock (evmWithExternal calls creates) (d.getD []) (d'.getD [])
  | _, _ => True

/-- Pairwise reflexive `Forall₂` for a common list. -/
private theorem forall₂_refl_equivStmt (l : List (Stmt Op)) :
    List.Forall₂ (EquivStmt D) l l := by
  induction l with
  | nil => exact .nil
  | cons s rest ih => exact .cons (fun _ _ _ _ _ _ => Iff.rfl) ih

private theorem scopeRel_append {a b c d : FScope D}
    (h1 : ScopeRel D a b) (h2 : ScopeRel D c d) : ScopeRel D (a ++ c) (b ++ d) := by
  induction h1 with
  | nil => exact h2
  | cons hp _ ih => exact .cons hp ih

private theorem forall₂_append_equivStmt {a b c d : List (Stmt Op)}
    (h1 : List.Forall₂ (EquivStmt D) a b) (h2 : List.Forall₂ (EquivStmt D) c d) :
    List.Forall₂ (EquivStmt D) (a ++ c) (b ++ d) := by
  induction h1 with
  | nil => exact h2
  | cons hp _ ih => exact .cons hp ih

/-- Hoisting distributes over append. -/
theorem hoist_append (a b : List (Stmt Op)) :
    hoist D (a ++ b) = hoist D a ++ hoist D b := by
  unfold hoist
  exact List.filterMap_append

/-- **Soundness of the removal relation**, all classes at once. The sequence
class carries the arbitrary common prefix so removal steps chain through
`removeLit_equivBlock` while kept steps go through the pointwise congruences
(function bodies via `EquivBlock.of_stmts_funs`). -/
theorem DlRel.sound {pc pc' : PCode Op} (h : DlRel pc pc') :
    dlSound (calls := calls) (creates := creates) pc pc' := by
  induction h with
  | @sameS s =>
      show EquivStmt D s s ∧ ScopeRel D (hoist D [s]) (hoist D [s])
      exact ⟨fun _ _ _ _ _ _ => Iff.rfl, ScopeRel.refl _⟩
  | @blockS body body' _ ih =>
      have hb : EquivBlock D body body' := by simpa using ih []
      exact ⟨hb, ScopeRel.refl _⟩
  | @funDefS n ps rs body body' _ ih =>
      have hb : EquivBlock D body body' := by simpa using ih []
      refine ⟨funDef_equiv n ps rs body body', ?_⟩
      show ScopeRel D (hoist D [.funDef n ps rs body]) (hoist D [.funDef n ps rs body'])
      exact .cons ⟨rfl, rfl, rfl, hb⟩ .nil
  | @condS c body body' _ ih =>
      have hb : EquivBlock D body body' := by simpa using ih []
      exact ⟨EquivStmt.cond_congr (fun _ _ _ _ => Iff.rfl) hb, ScopeRel.refl _⟩
  | @switchS c cases cases' dflt dflt' _ _ ihc ihd =>
      refine ⟨EquivStmt.switch_congr (fun _ _ _ _ => Iff.rfl) ihc ?_,
        ScopeRel.refl _⟩
      exact ihd
  | @forS init c post post' body body' _ _ ihp ihb =>
      have hp : EquivBlock D post post' := by simpa using ihp []
      have hb : EquivBlock D body body' := by simpa using ihb []
      exact ⟨EquivStmt.forLoop_congr init (fun _ _ _ _ => Iff.rfl) hp hb,
        ScopeRel.refl _⟩
  | nilSS =>
      intro pre
      exact EquivBlock.refl _
  | @consSS s s' rest rest' _ _ ihs ihrest =>
      intro pre
      obtain ⟨hs, hscope⟩ := (ihs : EquivStmt D s s' ∧ _)
      have step1 : EquivBlock D (pre ++ s :: rest) (pre ++ s' :: rest) := by
        refine EquivBlock.of_stmts_funs
          (EquivStmts.of_forall₂ (forall₂_append_equivStmt
            (forall₂_refl_equivStmt pre)
            (.cons hs (forall₂_refl_equivStmt rest)))) ?_
        show ScopeRel D (hoist D (pre ++ s :: rest)) (hoist D (pre ++ s' :: rest))
        rw [show (s :: rest) = [s] ++ rest from rfl,
            show (s' :: rest) = [s'] ++ rest from rfl,
            hoist_append, hoist_append, hoist_append, hoist_append]
        exact scopeRel_append (ScopeRel.refl _)
          (scopeRel_append hscope (ScopeRel.refl _))
      have step2 : EquivBlock D (pre ++ s' :: rest) (pre ++ s' :: rest') := by
        have := ihrest (pre ++ [s'])
        simpa [List.append_assoc] using this
      exact step1.trans step2
  | @dropSS x val rest rest' hval hm _ ihrest =>
      intro pre
      exact (removeLit_equivBlock hval hm).trans (ihrest pre)
  | casesNil => exact .nil
  | @casesCons l b b' rest rest' _ _ ihb ihrest =>
      exact .cons ⟨rfl, by simpa using ihb []⟩ ihrest
  | odfltNone => exact EquivBlock.refl _
  | @odfltSome b b' _ ih =>
      show EquivBlock D ((some b).getD []) ((some b').getD [])
      simpa using ih []

/-- Related sequences are equivalent blocks. -/
theorem DlRel.equivBlock {b b' : Block Op}
    (h : DlRel (.stmts b) (.stmts b')) :
    EquivBlock D b b' := by
  have := h.sound (calls := calls) (creates := creates)
  simpa using this []

/-- The **DeadLits pass**: dead literal-binding elimination, bundled with its
soundness proof — in the unchanged pointwise spec. -/
def deadLits : Pass D where
  run := dlStmts
  sound := fun b => DlRel.equivBlock (dlStmts_rel b)

@[simp] theorem deadLits_run (b : Block Op) :
    (deadLits (calls := calls) (creates := creates)).run b = dlStmts b := rfl

/-! ### Regression examples (checked at build time) -/

-- Propagate's leftovers die: `let a := 1  sstore(0, 1)` drops the binding.
example : dlStmts [.letDecl ["a"] (some (.lit (.number 1))),
    .exprStmt (.builtin .sstore [.lit (.number 0), .lit (.number 1)])]
  = [.exprStmt (.builtin .sstore [.lit (.number 0), .lit (.number 1)])] := rfl
-- A *used* literal binding stays.
example : dlStmts [.letDecl ["a"] (some (.lit (.number 1))),
    .exprStmt (.builtin .sstore [.lit (.number 0), .var "a"])]
  = [.letDecl ["a"] (some (.lit (.number 1))),
     .exprStmt (.builtin .sstore [.lit (.number 0), .var "a"])] := rfl
-- A later *assignment* to the variable blocks removal (it would retarget).
example : dlStmts [.letDecl ["a"] (some (.lit (.number 1))),
    .assign ["a"] (.builtin .calldataload [.lit (.number 0)])]
  = [.letDecl ["a"] (some (.lit (.number 1))),
     .assign ["a"] (.builtin .calldataload [.lit (.number 0)])] := rfl
-- Unused zero-init singletons die too.
example : dlStmts [.letDecl ["a"] none,
    .exprStmt (.builtin .sstore [.lit (.number 0), .lit (.number 1)])]
  = [.exprStmt (.builtin .sstore [.lit (.number 0), .lit (.number 1)])] := rfl
-- Non-literal right-hand sides are never removed (they can be stuck/effectful).
example : dlStmts [.letDecl ["a"] (some (.builtin .sload [.lit (.number 0)])),
    .exprStmt (.builtin .sstore [.lit (.number 0), .lit (.number 1)])]
  = [.letDecl ["a"] (some (.builtin .sload [.lit (.number 0)])),
     .exprStmt (.builtin .sstore [.lit (.number 0), .lit (.number 1)])] := rfl
-- Removal recurses into nested blocks.
example : dlStmts [.block [.letDecl ["a"] (some (.lit (.number 1))),
    .exprStmt (.builtin .stop [])]]
  = [.block [.exprStmt (.builtin .stop [])]] := rfl

end YulEvmCompiler.Optimizer
