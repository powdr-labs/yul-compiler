import YulEvmCompiler.Optimizer.Implementation.DeadStores
set_option warningAsError true

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM

variable {calls : ExternalCalls} {creates : ExternalCreates}

local notation "D" => evmWithExternal calls creates

/-! ### `dsDead` bookkeeping -/

/-- A kept assignment: its right-hand side never mentions a dead name, and a
dead name the assignment does not write stays dead. -/
theorem dsDead_assign {x : Ident} {ys : List Ident} {e : Expr Op} {rest : List (Stmt Op)}
    (h : dsDead x (.assign ys e :: rest) = true) :
    exprMentions x e = false ∧ (x ∉ ys → dsDead x rest = true) := by
  simp only [dsDead] at h
  split at h
  · exact absurd h (by simp)
  · next hm =>
      refine ⟨by simpa using hm, ?_⟩
      intro hnot
      split at h
      · next hc => exact absurd (by simpa using hc) hnot
      · exact h

/-- A `let` with an initialiser does not shadow or read a dead name. -/
theorem dsDead_letSome {x : Ident} {ys : List Ident} {e : Expr Op} {rest : List (Stmt Op)}
    (h : dsDead x (.letDecl ys (some e) :: rest) = true) :
    exprMentions x e = false ∧ x ∉ ys ∧ dsDead x rest = true := by
  simp only [dsDead] at h
  split at h
  · exact absurd h (by simp)
  · next hm =>
      split at h
      · exact absurd h (by simp)
      · next hc => exact ⟨by simpa using hm, by simpa using hc, h⟩

/-- A bare `let` does not shadow a dead name. -/
theorem dsDead_letNone {x : Ident} {ys : List Ident} {rest : List (Stmt Op)}
    (h : dsDead x (.letDecl ys none :: rest) = true) :
    x ∉ ys ∧ dsDead x rest = true := by
  simp only [dsDead] at h
  split at h
  · exact absurd h (by simp)
  · next hc => exact ⟨by simpa using hc, h⟩

/-- Every other statement shape is passed through: a dead name is unmentioned by
it and stays dead afterwards. -/
theorem dsDead_pass {x : Ident} {s : Stmt Op} {rest : List (Stmt Op)}
    (h : dsDead x (s :: rest) = true)
    (hshape : (∃ b, s = .block b) ∨ (∃ n ps rs b, s = .funDef n ps rs b) ∨
      (∃ c b, s = .cond c b) ∨ (∃ c cs d, s = .switch c cs d) ∨
      (∃ i c p b, s = .forLoop i c p b) ∨ (∃ e, s = .exprStmt e)) :
    stmtMentions x s = false ∧ dsDead x rest = true := by
  rcases hshape with ⟨b, rfl⟩ | ⟨n, ps, rs, b, rfl⟩ | ⟨c, b, rfl⟩ | ⟨c, cs, d, rfl⟩ |
    ⟨i, c, p, b, rfl⟩ | ⟨e, rfl⟩
  · simp only [dsDead] at h
    split at h
    · exact absurd h (by simp)
    · next hm => exact ⟨by simpa [stmtMentions] using hm, h⟩
  · simp only [dsDead] at h
    split at h
    · exact absurd h (by simp)
    · next hm => exact ⟨by simpa [stmtMentions] using hm, h⟩
  · simp only [dsDead] at h
    split at h
    · exact absurd h (by simp)
    · next hm => exact ⟨by simpa [stmtMentions] using hm, h⟩
  · simp only [dsDead] at h
    split at h
    · exact absurd h (by simp)
    · next hm => exact ⟨by simpa [stmtMentions] using hm, h⟩
  · simp only [dsDead] at h
    split at h
    · exact absurd h (by simp)
    · next hm => exact ⟨by simpa [stmtMentions] using hm, h⟩
  · simp only [dsDead] at h
    split at h
    · exact absurd h (by simp)
    · next hm => exact ⟨by simpa [stmtMentions] using hm, h⟩

/-! ### Small execution facts -/

/-- A singleton multi-assignment is a single in-place update. -/
theorem setMany_single (V : VEnv D) (x : Ident) (v : U256) :
    VEnv.setMany V [x] [v] = VEnv.set V x v := rfl

/-- A zero-initialising singleton `let` pushes one binding. -/
theorem bindZeros_single (x : Ident) (V : VEnv D) :
    bindZeros D [x] ++ V = (x, (evmWithExternal calls creates).zero) :: V := rfl

/-- A normally-terminating `let` prepends exactly its declared names. -/
theorem letStep_keys {xs : List Ident} {val : Option (Expr Op)} {funs : FunEnv D}
    {V Vm : VEnv D} {st stm : EvmState}
    (h : Step D funs V st (.stmt (.letDecl xs val)) (.sres Vm stm .normal)) :
    Vm.map Prod.fst = xs ++ V.map Prod.fst := by
  cases h with
  | letZero => rw [List.map_append, bindZeros_fst]
  | letVal he hlen => rw [List.map_append, List.map_fst_zip (by omega)]

end YulEvmCompiler.Optimizer

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM

variable {calls : ExternalCalls} {creates : ExternalCreates}

local notation "D" => evmWithExternal calls creates

/-! ### The sequence sweep: forward simulation -/

/-- The forward simulation's conclusion, as a predicate on the source sequence,
so the per-shape cases factor out of the induction. `k` is the height of the
environment the enclosing block will `restore` to; `owned` names live above it. -/
def SweepFwd (ss : List (Stmt Op)) : Prop :=
  ∀ {bound owned : List Ident} {funs : FunEnv D} {dead : Ident → Prop} {k : Nat}
    {V1 V2 : VEnv D} {st : EvmState} {V1' : VEnv D} {st' : EvmState} {o : Outcome},
    BoundOK V1 bound → (∀ x, x ∈ owned → AboveK k x V1) →
    VChg dead k (fun _ => False) V1 V2 →
    (∀ x, dead x → dsDead x ss = true) →
    Step D funs V1 st (.stmts ss) (.sres V1' st' o) →
    ∃ (V2' : VEnv D) (dead' : Ident → Prop),
      Step D funs V2 st (.stmts (dsSweep bound owned ss)) (.sres V2' st' o) ∧
      VChg dead' k (fun _ => False) V1' V2'

/-- A statement the sweep passes through that changes neither `bound` nor
`owned`: transport it with the value-change frame lemma. -/
theorem sweepKeep_fwd {s : Stmt Op} {rest : List (Stmt Op)}
    (ih : SweepFwd (calls := calls) (creates := creates) rest)
    {bound owned : List Ident} {funs : FunEnv D} {dead : Ident → Prop} {k : Nat}
    {V1 V2 : VEnv D} {st : EvmState} {V1' : VEnv D} {st' : EvmState} {o : Outcome}
    (hsweep : dsSweep bound owned (s :: rest) = s :: dsSweep bound owned rest)
    (hb : BoundOK V1 bound) (how : ∀ x, x ∈ owned → AboveK k x V1)
    (hrel : VChg dead k (fun _ => False) V1 V2)
    (hments : ∀ x, dead x → stmtMentions x s = false)
    (hadv : ∀ {Vm : VEnv D} {stm : EvmState},
      Step D funs V1 st (.stmt s) (.sres Vm stm .normal) → ∀ x, dead x → dsDead x rest = true)
    (hstep : Step D funs V1 st (.stmts (s :: rest)) (.sres V1' st' o)) :
    ∃ (V2' : VEnv D) (dead' : Ident → Prop),
      Step D funs V2 st (.stmts (dsSweep bound owned (s :: rest))) (.sres V2' st' o) ∧
      VChg dead' k (fun _ => False) V1' V2' := by
  rw [hsweep]
  have hfree : DeadFree dead (Code.stmt s) := fun x hx => hments x hx
  cases hstep with
  | seqCons hs hrest =>
      obtain ⟨res2, hs2, hr2⟩ := vchgStep hs hrel hfree
      obtain ⟨Vm2, rfl, hrelm⟩ := hr2.sres
      obtain ⟨V2', dead', hstep2, hrel2⟩ := ih (hb.mono hs)
        (fun x hx => (how x hx).mono_step hs) hrelm (hadv hs) hrest
      exact ⟨V2', dead', Step.seqCons hs2 hstep2, hrel2⟩
  | seqStop hs hne =>
      obtain ⟨res2, hs2, hr2⟩ := vchgStep hs hrel hfree
      obtain ⟨V2', rfl, hrel2⟩ := hr2.sres
      exact ⟨V2', dead, Step.seqStop hs2 hne, hrel2⟩

/-- A `let` the sweep keeps: same as `sweepKeep_fwd`, but the declared names join
`bound` and `owned`. -/
theorem sweepLetKeep_fwd {xs : List Ident} {val : Option (Expr Op)} {rest : List (Stmt Op)}
    (ih : SweepFwd (calls := calls) (creates := creates) rest)
    {bound owned : List Ident} {funs : FunEnv D} {dead : Ident → Prop} {k : Nat}
    {V1 V2 : VEnv D} {st : EvmState} {V1' : VEnv D} {st' : EvmState} {o : Outcome}
    (hsweep : dsSweep bound owned (.letDecl xs val :: rest)
      = .letDecl xs val :: dsSweep (xs ++ bound) (xs ++ owned) rest)
    (hb : BoundOK V1 bound) (how : ∀ x, x ∈ owned → AboveK k x V1)
    (hrel : VChg dead k (fun _ => False) V1 V2)
    (hments : ∀ x, dead x → stmtMentions x (.letDecl xs val) = false)
    (hadv : ∀ x, dead x → dsDead x rest = true)
    (hstep : Step D funs V1 st (.stmts (.letDecl xs val :: rest)) (.sres V1' st' o)) :
    ∃ (V2' : VEnv D) (dead' : Ident → Prop),
      Step D funs V2 st (.stmts (dsSweep bound owned (.letDecl xs val :: rest)))
        (.sres V2' st' o) ∧
      VChg dead' k (fun _ => False) V1' V2' := by
  rw [hsweep]
  have hfree : DeadFree dead (Code.stmt (.letDecl xs val)) := fun x hx => hments x hx
  have hk : k ≤ V1.length := hrel.tail_le
  cases hstep with
  | seqCons hs hrest =>
      obtain ⟨res2, hs2, hr2⟩ := vchgStep hs hrel hfree
      obtain ⟨Vm2, rfl, hrelm⟩ := hr2.sres
      have hkeys := letStep_keys hs
      obtain ⟨V2', dead', hstep2, hrel2⟩ := ih
        (bound := xs ++ bound) (owned := xs ++ owned)
        (fun y hy => by
          rw [hkeys]
          rcases List.mem_append.mp hy with hy | hy
          · exact List.mem_append_left _ hy
          · exact List.mem_append_right _ (hb y hy))
        (fun y hy => by
          rcases List.mem_append.mp hy with hy | hy
          · exact AboveK.of_keys_head hkeys hk hy
          · exact AboveK.of_keys_mono hkeys (how y hy))
        hrelm hadv hrest
      exact ⟨V2', dead', Step.seqCons hs2 hstep2, hrel2⟩
  | seqStop hs hne =>
      obtain ⟨res2, hs2, hr2⟩ := vchgStep hs hrel hfree
      obtain ⟨V2', rfl, hrel2⟩ := hr2.sres
      exact ⟨V2', dead, Step.seqStop hs2 hne, hrel2⟩

/-- An assignment the sweep keeps. Its right-hand side mentions no dead name, so
it evaluates identically on both sides; the write then kills every dead name it
targets. -/
theorem sweepAssignKeep_fwd {ys : List Ident} {e : Expr Op} {rest : List (Stmt Op)}
    (ih : SweepFwd (calls := calls) (creates := creates) rest)
    {bound owned : List Ident} {funs : FunEnv D} {dead : Ident → Prop} {k : Nat}
    {V1 V2 : VEnv D} {st : EvmState} {V1' : VEnv D} {st' : EvmState} {o : Outcome}
    (hsweep : dsSweep bound owned (.assign ys e :: rest)
      = .assign ys e :: dsSweep bound owned rest)
    (hb : BoundOK V1 bound) (how : ∀ x, x ∈ owned → AboveK k x V1)
    (hrel : VChg dead k (fun _ => False) V1 V2)
    (hd : ∀ x, dead x → dsDead x (.assign ys e :: rest) = true)
    (hstep : Step D funs V1 st (.stmts (.assign ys e :: rest)) (.sres V1' st' o)) :
    ∃ (V2' : VEnv D) (dead' : Ident → Prop),
      Step D funs V2 st (.stmts (dsSweep bound owned (.assign ys e :: rest)))
        (.sres V2' st' o) ∧
      VChg dead' k (fun _ => False) V1' V2' := by
  rw [hsweep]
  have hfree : DeadFree dead (Code.expr e) := fun x hx => (dsDead_assign (hd x hx)).1
  cases hstep with
  | seqCons hs hrest =>
      cases hs with
      | @assignVal _ _ _ _ _ vals st1 he hlen =>
          obtain ⟨r2, he2, hr2⟩ := vchgStep he hrel hfree
          obtain rfl := hr2.eres
          have hrelm : VChg (fun y => dsDead y rest = true) k (fun _ => False)
              (VEnv.setMany V1 ys vals) (VEnv.setMany V2 ys vals) :=
            VChg.setMany ys vals hrel hlen.symm
              (fun y hy hn => (dsDead_assign (hd y hy)).2 hn)
          obtain ⟨V2', dead', hstep2, hrel2⟩ := ih
            (fun y hy => by rw [VEnv.setMany_keys V1]; exact hb y hy)
            (fun y hy => AboveK.of_keys_eq (VEnv.setMany_keys V1 _ _) (how y hy))
            hrelm (fun y hy => hy) hrest
          exact ⟨V2', dead', Step.seqCons (Step.assignVal he2 hlen) hstep2, hrel2⟩
  | seqStop hs hne =>
      cases hs with
      | assignVal _ _ => exact absurd rfl hne
      | @assignHalt _ _ _ _ _ st1 he =>
          obtain ⟨r2, he2, hr2⟩ := vchgStep he hrel hfree
          obtain rfl := hr2.eres
          exact ⟨V2, dead, Step.seqStop (Step.assignHalt he2) hne, hrel⟩

/-- **R1.** The dead store is deleted: the source assigns, the target does not.
`alwaysEval` makes the right-hand side total and state-preserving, and `owned`
puts the target above the tail the enclosing block restores to. -/
theorem sweepAssignDrop_fwd {x : Ident} {e : Expr Op} {rest : List (Stmt Op)}
    (ih : SweepFwd (calls := calls) (creates := creates) rest)
    {bound owned : List Ident} {funs : FunEnv D} {dead : Ident → Prop} {k : Nat}
    {V1 V2 : VEnv D} {st : EvmState} {V1' : VEnv D} {st' : EvmState} {o : Outcome}
    (hcond : (owned.contains x && alwaysEval bound e && dsDead x rest) = true)
    (hb : BoundOK V1 bound) (how : ∀ y, y ∈ owned → AboveK k y V1)
    (hrel : VChg dead k (fun _ => False) V1 V2)
    (hd : ∀ y, dead y → dsDead y (.assign [x] e :: rest) = true)
    (hstep : Step D funs V1 st (.stmts (.assign [x] e :: rest)) (.sres V1' st' o)) :
    ∃ (V2' : VEnv D) (dead' : Ident → Prop),
      Step D funs V2 st (.stmts (dsSweep bound owned (.assign [x] e :: rest)))
        (.sres V2' st' o) ∧
      VChg dead' k (fun _ => False) V1' V2' := by
  have hc := hcond
  rw [Bool.and_eq_true, Bool.and_eq_true] at hc
  obtain ⟨⟨hown, hae⟩, hdead⟩ := hc
  have hsweep : dsSweep bound owned (.assign [x] e :: rest) = dsSweep bound owned rest := by
    simp only [dsSweep, hcond, if_true]
  rw [hsweep]
  have hmono : ∀ y, dead y → dsDead y rest = true := by
    intro y hy
    by_cases hyx : y = x
    · subst hyx; exact hdead
    · exact (dsDead_assign (hd y hy)).2 (by simp [hyx])
  have hab : AboveK k x V1 := how x (by simpa using hown)
  cases hstep with
  | seqCons hs hrest =>
      cases hs with
      | @assignVal _ _ _ _ _ vals st1 he hlen =>
          obtain ⟨v, hv⟩ := dcEvalInv e hae he
          injection hv with hvals hst
          subst hvals; subst hst
          have hrelm : VChg (fun y => dsDead y rest = true) k (fun _ => False)
              (VEnv.setMany V1 [x] [v]) V2 :=
            hrel.set_left v hab (fun h => h) hdead hmono
          obtain ⟨V2', dead', hstep2, hrel2⟩ := ih
            (fun y hy => by rw [VEnv.setMany_keys V1]; exact hb y hy)
            (fun y hy => AboveK.of_keys_eq (VEnv.setMany_keys V1 _ _) (how y hy))
            hrelm (fun y hy => hy) hrest
          exact ⟨V2', dead', hstep2, hrel2⟩
  | seqStop hs hne =>
      cases hs with
      | assignVal _ _ => exact absurd rfl hne
      | @assignHalt _ _ _ _ _ st1 he =>
          obtain ⟨v, hv⟩ := dcEvalInv e hae he
          exact absurd hv (by simp)

/-- **R2.** The dead initialiser is dropped, keeping the binder: the source binds
the right-hand side's value, the target binds zero, and the name is unread until
its next write or the sequence's exit. -/
theorem sweepLetDrop_fwd {x : Ident} {e : Expr Op} {rest : List (Stmt Op)}
    (ih : SweepFwd (calls := calls) (creates := creates) rest)
    {bound owned : List Ident} {funs : FunEnv D} {dead : Ident → Prop} {k : Nat}
    {V1 V2 : VEnv D} {st : EvmState} {V1' : VEnv D} {st' : EvmState} {o : Outcome}
    (hcond : (alwaysEval bound e && dsDead x rest) = true)
    (hb : BoundOK V1 bound) (how : ∀ y, y ∈ owned → AboveK k y V1)
    (hrel : VChg dead k (fun _ => False) V1 V2)
    (hd : ∀ y, dead y → dsDead y (.letDecl [x] (some e) :: rest) = true)
    (hstep : Step D funs V1 st (.stmts (.letDecl [x] (some e) :: rest)) (.sres V1' st' o)) :
    ∃ (V2' : VEnv D) (dead' : Ident → Prop),
      Step D funs V2 st (.stmts (dsSweep bound owned (.letDecl [x] (some e) :: rest)))
        (.sres V2' st' o) ∧
      VChg dead' k (fun _ => False) V1' V2' := by
  have hc := hcond
  rw [Bool.and_eq_true] at hc
  obtain ⟨hae, hdead⟩ := hc
  have hsweep : dsSweep bound owned (.letDecl [x] (some e) :: rest)
      = .letDecl [x] none :: dsSweep (x :: bound) (x :: owned) rest := by
    simp only [dsSweep, hcond, if_true]
  rw [hsweep]
  have hk : k ≤ V1.length := hrel.tail_le
  cases hstep with
  | seqCons hs hrest =>
      cases hs with
      | @letVal _ _ _ _ _ vals st1 he hlen =>
          obtain ⟨v, hv⟩ := dcEvalInv e hae he
          injection hv with hvals hst
          subst hvals; subst hst
          have hgrow : VChg dead k (fun y => (fun _ : Ident => False) y ∨ y = x) V1 V2 :=
            hrel.grow_seen (extra := fun y => y = x)
              (fun y hy hc2 => (dsDead_letSome (hd y hy)).2.1 (by simp [hc2]))
          have hnew : VChg (fun y => dsDead y rest = true) k (fun _ => False)
              ((x, v) :: V1) ((x, (evmWithExternal calls creates).zero) :: V2) :=
            VChg.diff hdead (fun h => h)
              (hgrow.mono_seen (fun y _ hy => (dsDead_letSome (hd y hy)).2.2))
          obtain ⟨V2', dead', hstep2, hrel2⟩ := ih
            (bound := x :: bound) (owned := x :: owned)
            (fun y hy => by
              rcases List.mem_cons.mp hy with rfl | hy
              · simp
              · exact List.mem_cons_of_mem _ (hb y hy))
            (fun y hy => by
              rcases List.mem_cons.mp hy with rfl | hy
              · exact AboveK.head hk
              · exact AboveK.prepend (pre := [(x, v)]) (how y hy))
            hnew (fun y hy => hy) hrest
          exact ⟨V2', dead', Step.seqCons Step.letZero hstep2, hrel2⟩
  | seqStop hs hne =>
      cases hs with
      | letVal _ _ => exact absurd rfl hne
      | @letHalt _ _ _ _ _ st1 he =>
          obtain ⟨v, hv⟩ := dcEvalInv e hae he
          exact absurd hv (by simp)

/-- **Forward simulation of one sweep.** Every source derivation of the sequence
has a target derivation of the swept sequence with the same state and outcome,
and environments that still differ only at dead names above the tail. -/
theorem dsSweep_fwd : ∀ ss : List (Stmt Op), SweepFwd (calls := calls) (creates := creates) ss := by
  intro ss
  induction ss with
  | nil =>
      intro bound owned funs dead k V1 V2 st V1' st' o hb how hrel hd hstep
      cases hstep with
      | seqNil => exact ⟨V2, dead, Step.seqNil, hrel⟩
  | cons s rest ih =>
      intro bound owned funs dead k V1 V2 st V1' st' o hb how hrel hd hstep
      cases s with
      | block body =>
          exact sweepKeep_fwd ih (by simp only [dsSweep]) hb how hrel
            (fun x hx => (dsDead_pass (hd x hx) (Or.inl ⟨body, rfl⟩)).1)
            (fun _ x hx => (dsDead_pass (hd x hx) (Or.inl ⟨body, rfl⟩)).2) hstep
      | funDef n ps rs body =>
          exact sweepKeep_fwd ih (by simp only [dsSweep]) hb how hrel
            (fun x hx => (dsDead_pass (hd x hx) (Or.inr (Or.inl ⟨n, ps, rs, body, rfl⟩))).1)
            (fun _ x hx => (dsDead_pass (hd x hx) (Or.inr (Or.inl ⟨n, ps, rs, body, rfl⟩))).2)
            hstep
      | cond c body =>
          exact sweepKeep_fwd ih (by simp only [dsSweep]) hb how hrel
            (fun x hx => (dsDead_pass (hd x hx) (Or.inr (Or.inr (Or.inl ⟨c, body, rfl⟩)))).1)
            (fun _ x hx => (dsDead_pass (hd x hx) (Or.inr (Or.inr (Or.inl ⟨c, body, rfl⟩)))).2)
            hstep
      | «switch» c cs dflt =>
          exact sweepKeep_fwd ih (by simp only [dsSweep]) hb how hrel
            (fun x hx =>
              (dsDead_pass (hd x hx) (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, cs, dflt, rfl⟩))))).1)
            (fun _ x hx =>
              (dsDead_pass (hd x hx) (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, cs, dflt, rfl⟩))))).2)
            hstep
      | forLoop init c post body =>
          exact sweepKeep_fwd ih (by simp only [dsSweep]) hb how hrel
            (fun x hx => (dsDead_pass (hd x hx)
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨init, c, post, body, rfl⟩)))))).1)
            (fun _ x hx => (dsDead_pass (hd x hx)
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨init, c, post, body, rfl⟩)))))).2)
            hstep
      | exprStmt e =>
          exact sweepKeep_fwd ih (by simp only [dsSweep]) hb how hrel
            (fun x hx => (dsDead_pass (hd x hx)
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e, rfl⟩)))))).1)
            (fun _ x hx => (dsDead_pass (hd x hx)
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e, rfl⟩)))))).2)
            hstep
      | «break» =>
          exact sweepKeep_fwd ih (by simp only [dsSweep]) hb how hrel
            (fun _ _ => rfl) (fun h => by cases h) hstep
      | «continue» =>
          exact sweepKeep_fwd ih (by simp only [dsSweep]) hb how hrel
            (fun _ _ => rfl) (fun h => by cases h) hstep
      | «leave» =>
          exact sweepKeep_fwd ih (by simp only [dsSweep]) hb how hrel
            (fun _ _ => rfl) (fun h => by cases h) hstep
      | assign ys e =>
          rcases ys with _ | ⟨x, ys'⟩
          · exact sweepAssignKeep_fwd ih (by simp only [dsSweep]) hb how hrel hd hstep
          · rcases ys' with _ | ⟨y, ys''⟩
            · by_cases hcond : (owned.contains x && alwaysEval bound e && dsDead x rest) = true
              · exact sweepAssignDrop_fwd ih hcond hb how hrel hd hstep
              · rw [Bool.not_eq_true] at hcond
                exact sweepAssignKeep_fwd ih
                  (by simp only [dsSweep, hcond, Bool.false_eq_true, if_false]) hb how hrel hd hstep
            · exact sweepAssignKeep_fwd ih (by simp only [dsSweep]) hb how hrel hd hstep
      | letDecl xs val =>
          cases val with
          | none =>
              exact sweepLetKeep_fwd ih (by simp only [dsSweep]) hb how hrel
                (fun x hx => by
                  have h1 := (dsDead_letNone (hd x hx)).1
                  simp [stmtMentions, optExprMentions, h1])
                (fun x hx => (dsDead_letNone (hd x hx)).2) hstep
          | some e =>
              rcases xs with _ | ⟨x, xs'⟩
              · exact sweepLetKeep_fwd ih (by simp only [dsSweep]) hb how hrel
                  (fun z hz => by
                    have h1 := dsDead_letSome (hd z hz)
                    simp [stmtMentions, optExprMentions, h1.1, h1.2.1])
                  (fun z hz => (dsDead_letSome (hd z hz)).2.2) hstep
              · rcases xs' with _ | ⟨y, xs''⟩
                · by_cases hcond : (alwaysEval bound e && dsDead x rest) = true
                  · exact sweepLetDrop_fwd ih hcond hb how hrel hd hstep
                  · rw [Bool.not_eq_true] at hcond
                    exact sweepLetKeep_fwd ih
                      (by simp only [dsSweep, hcond, Bool.false_eq_true, if_false,
                        List.singleton_append]) hb how hrel
                      (fun z hz => by
                        have h1 := dsDead_letSome (hd z hz)
                        simp [stmtMentions, optExprMentions, h1.1, h1.2.1])
                      (fun z hz => (dsDead_letSome (hd z hz)).2.2) hstep
                · exact sweepLetKeep_fwd ih (by simp only [dsSweep]) hb how hrel
                    (fun z hz => by
                      have h1 := dsDead_letSome (hd z hz)
                      simp [stmtMentions, optExprMentions, h1.1, h1.2.1])
                    (fun z hz => (dsDead_letSome (hd z hz)).2.2) hstep

end YulEvmCompiler.Optimizer

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM

variable {calls : ExternalCalls} {creates : ExternalCreates}

local notation "D" => evmWithExternal calls creates

/-! ### The sequence sweep: backward simulation -/

/-- The backward simulation's conclusion, as a predicate on the source sequence. -/
def SweepBwd (ss : List (Stmt Op)) : Prop :=
  ∀ {bound owned : List Ident} {funs : FunEnv D} {dead : Ident → Prop} {k : Nat}
    {V1 V2 : VEnv D} {st : EvmState} {V2' : VEnv D} {st' : EvmState} {o : Outcome},
    BoundOK V1 bound → (∀ x, x ∈ owned → AboveK k x V1) →
    VChg dead k (fun _ => False) V1 V2 →
    (∀ x, dead x → dsDead x ss = true) →
    Step D funs V2 st (.stmts (dsSweep bound owned ss)) (.sres V2' st' o) →
    ∃ (V1' : VEnv D) (dead' : Ident → Prop),
      Step D funs V1 st (.stmts ss) (.sres V1' st' o) ∧
      VChg dead' k (fun _ => False) V1' V2'

/-- Backward counterpart of `sweepKeep_fwd`. -/
theorem sweepKeep_bwd {s : Stmt Op} {rest : List (Stmt Op)}
    (ih : SweepBwd (calls := calls) (creates := creates) rest)
    {bound owned : List Ident} {funs : FunEnv D} {dead : Ident → Prop} {k : Nat}
    {V1 V2 : VEnv D} {st : EvmState} {V2' : VEnv D} {st' : EvmState} {o : Outcome}
    (hsweep : dsSweep bound owned (s :: rest) = s :: dsSweep bound owned rest)
    (hb : BoundOK V1 bound) (how : ∀ x, x ∈ owned → AboveK k x V1)
    (hrel : VChg dead k (fun _ => False) V1 V2)
    (hments : ∀ x, dead x → stmtMentions x s = false)
    (hadv : ∀ {Vm : VEnv D} {stm : EvmState},
      Step D funs V1 st (.stmt s) (.sres Vm stm .normal) → ∀ x, dead x → dsDead x rest = true)
    (hstep : Step D funs V2 st (.stmts (dsSweep bound owned (s :: rest))) (.sres V2' st' o)) :
    ∃ (V1' : VEnv D) (dead' : Ident → Prop),
      Step D funs V1 st (.stmts (s :: rest)) (.sres V1' st' o) ∧
      VChg dead' k (fun _ => False) V1' V2' := by
  rw [hsweep] at hstep
  have hfree : DeadFree dead (Code.stmt s) := fun x hx => hments x hx
  cases hstep with
  | seqCons hs hrest =>
      obtain ⟨res1, hs1, hr1⟩ := vchgStep hs hrel.symm hfree
      obtain ⟨Vm1, rfl, hrelm⟩ := hr1.sres
      obtain ⟨V1', dead', hstep1, hrel1⟩ := ih (hb.mono hs1)
        (fun x hx => (how x hx).mono_step hs1) hrelm.symm (hadv hs1) hrest
      exact ⟨V1', dead', Step.seqCons hs1 hstep1, hrel1⟩
  | seqStop hs hne =>
      obtain ⟨res1, hs1, hr1⟩ := vchgStep hs hrel.symm hfree
      obtain ⟨V1', rfl, hrel1⟩ := hr1.sres
      exact ⟨V1', dead, Step.seqStop hs1 hne, hrel1.symm⟩

/-- Backward counterpart of `sweepLetKeep_fwd`. -/
theorem sweepLetKeep_bwd {xs : List Ident} {val : Option (Expr Op)} {rest : List (Stmt Op)}
    (ih : SweepBwd (calls := calls) (creates := creates) rest)
    {bound owned : List Ident} {funs : FunEnv D} {dead : Ident → Prop} {k : Nat}
    {V1 V2 : VEnv D} {st : EvmState} {V2' : VEnv D} {st' : EvmState} {o : Outcome}
    (hsweep : dsSweep bound owned (.letDecl xs val :: rest)
      = .letDecl xs val :: dsSweep (xs ++ bound) (xs ++ owned) rest)
    (hb : BoundOK V1 bound) (how : ∀ x, x ∈ owned → AboveK k x V1)
    (hrel : VChg dead k (fun _ => False) V1 V2)
    (hments : ∀ x, dead x → stmtMentions x (.letDecl xs val) = false)
    (hadv : ∀ x, dead x → dsDead x rest = true)
    (hstep : Step D funs V2 st (.stmts (dsSweep bound owned (.letDecl xs val :: rest)))
      (.sres V2' st' o)) :
    ∃ (V1' : VEnv D) (dead' : Ident → Prop),
      Step D funs V1 st (.stmts (.letDecl xs val :: rest)) (.sres V1' st' o) ∧
      VChg dead' k (fun _ => False) V1' V2' := by
  rw [hsweep] at hstep
  have hfree : DeadFree dead (Code.stmt (.letDecl xs val)) := fun x hx => hments x hx
  have hk : k ≤ V1.length := hrel.tail_le
  cases hstep with
  | seqCons hs hrest =>
      obtain ⟨res1, hs1, hr1⟩ := vchgStep hs hrel.symm hfree
      obtain ⟨Vm1, rfl, hrelm⟩ := hr1.sres
      have hkeys := letStep_keys hs1
      obtain ⟨V1', dead', hstep1, hrel1⟩ := ih
        (bound := xs ++ bound) (owned := xs ++ owned)
        (fun y hy => by
          rw [hkeys]
          rcases List.mem_append.mp hy with hy | hy
          · exact List.mem_append_left _ hy
          · exact List.mem_append_right _ (hb y hy))
        (fun y hy => by
          rcases List.mem_append.mp hy with hy | hy
          · exact AboveK.of_keys_head hkeys hk hy
          · exact AboveK.of_keys_mono hkeys (how y hy))
        hrelm.symm hadv hrest
      exact ⟨V1', dead', Step.seqCons hs1 hstep1, hrel1⟩
  | seqStop hs hne =>
      obtain ⟨res1, hs1, hr1⟩ := vchgStep hs hrel.symm hfree
      obtain ⟨V1', rfl, hrel1⟩ := hr1.sres
      exact ⟨V1', dead, Step.seqStop hs1 hne, hrel1.symm⟩

/-- Backward counterpart of `sweepAssignKeep_fwd`. -/
theorem sweepAssignKeep_bwd {ys : List Ident} {e : Expr Op} {rest : List (Stmt Op)}
    (ih : SweepBwd (calls := calls) (creates := creates) rest)
    {bound owned : List Ident} {funs : FunEnv D} {dead : Ident → Prop} {k : Nat}
    {V1 V2 : VEnv D} {st : EvmState} {V2' : VEnv D} {st' : EvmState} {o : Outcome}
    (hsweep : dsSweep bound owned (.assign ys e :: rest)
      = .assign ys e :: dsSweep bound owned rest)
    (hb : BoundOK V1 bound) (how : ∀ x, x ∈ owned → AboveK k x V1)
    (hrel : VChg dead k (fun _ => False) V1 V2)
    (hd : ∀ x, dead x → dsDead x (.assign ys e :: rest) = true)
    (hstep : Step D funs V2 st (.stmts (dsSweep bound owned (.assign ys e :: rest)))
      (.sres V2' st' o)) :
    ∃ (V1' : VEnv D) (dead' : Ident → Prop),
      Step D funs V1 st (.stmts (.assign ys e :: rest)) (.sres V1' st' o) ∧
      VChg dead' k (fun _ => False) V1' V2' := by
  rw [hsweep] at hstep
  have hfree : DeadFree dead (Code.expr e) := fun x hx => (dsDead_assign (hd x hx)).1
  cases hstep with
  | seqCons hs hrest =>
      cases hs with
      | @assignVal _ _ _ _ _ vals st1 he hlen =>
          obtain ⟨r1, he1, hr1⟩ := vchgStep he hrel.symm hfree
          obtain rfl := hr1.eres
          have hrelm : VChg (fun y => dsDead y rest = true) k (fun _ => False)
              (VEnv.setMany V1 ys vals) (VEnv.setMany V2 ys vals) :=
            VChg.setMany ys vals hrel hlen.symm
              (fun y hy hn => (dsDead_assign (hd y hy)).2 hn)
          obtain ⟨V1', dead', hstep1, hrel1⟩ := ih
            (fun y hy => by rw [VEnv.setMany_keys V1]; exact hb y hy)
            (fun y hy => AboveK.of_keys_eq (VEnv.setMany_keys V1 _ _) (how y hy))
            hrelm (fun y hy => hy) hrest
          exact ⟨V1', dead', Step.seqCons (Step.assignVal he1 hlen) hstep1, hrel1⟩
  | seqStop hs hne =>
      cases hs with
      | assignVal _ _ => exact absurd rfl hne
      | @assignHalt _ _ _ _ _ st1 he =>
          obtain ⟨r1, he1, hr1⟩ := vchgStep he hrel.symm hfree
          obtain rfl := hr1.eres
          exact ⟨V1, dead, Step.seqStop (Step.assignHalt he1) hne, hrel⟩

/-- Backward counterpart of `sweepAssignDrop_fwd` (**R1**): the deleted store is
put back, which `alwaysEval` and `BoundOK` make possible. -/
theorem sweepAssignDrop_bwd {x : Ident} {e : Expr Op} {rest : List (Stmt Op)}
    (ih : SweepBwd (calls := calls) (creates := creates) rest)
    {bound owned : List Ident} {funs : FunEnv D} {dead : Ident → Prop} {k : Nat}
    {V1 V2 : VEnv D} {st : EvmState} {V2' : VEnv D} {st' : EvmState} {o : Outcome}
    (hcond : (owned.contains x && alwaysEval bound e && dsDead x rest) = true)
    (hb : BoundOK V1 bound) (how : ∀ y, y ∈ owned → AboveK k y V1)
    (hrel : VChg dead k (fun _ => False) V1 V2)
    (hd : ∀ y, dead y → dsDead y (.assign [x] e :: rest) = true)
    (hstep : Step D funs V2 st (.stmts (dsSweep bound owned (.assign [x] e :: rest)))
      (.sres V2' st' o)) :
    ∃ (V1' : VEnv D) (dead' : Ident → Prop),
      Step D funs V1 st (.stmts (.assign [x] e :: rest)) (.sres V1' st' o) ∧
      VChg dead' k (fun _ => False) V1' V2' := by
  have hc := hcond
  rw [Bool.and_eq_true, Bool.and_eq_true] at hc
  obtain ⟨⟨hown, hae⟩, hdead⟩ := hc
  have hsweep : dsSweep bound owned (.assign [x] e :: rest) = dsSweep bound owned rest := by
    simp only [dsSweep, hcond, if_true]
  rw [hsweep] at hstep
  have hmono : ∀ y, dead y → dsDead y rest = true := by
    intro y hy
    by_cases hyx : y = x
    · subst hyx; exact hdead
    · exact (dsDead_assign (hd y hy)).2 (by simp [hyx])
  have hab : AboveK k x V1 := how x (by simpa using hown)
  obtain ⟨v, hv⟩ := dcEvalRun hb funs st e hae
  have hrelm : VChg (fun y => dsDead y rest = true) k (fun _ => False)
      (VEnv.setMany V1 [x] [v]) V2 :=
    hrel.set_left v hab (fun h => h) hdead hmono
  obtain ⟨V1', dead', hstep1, hrel1⟩ := ih
    (fun y hy => by rw [VEnv.setMany_keys V1]; exact hb y hy)
    (fun y hy => AboveK.of_keys_eq (VEnv.setMany_keys V1 _ _) (how y hy))
    hrelm (fun y hy => hy) hstep
  exact ⟨V1', dead', Step.seqCons (Step.assignVal hv rfl) hstep1, hrel1⟩

/-- Backward counterpart of `sweepLetDrop_fwd` (**R2**): the dropped initialiser
is put back. -/
theorem sweepLetDrop_bwd {x : Ident} {e : Expr Op} {rest : List (Stmt Op)}
    (ih : SweepBwd (calls := calls) (creates := creates) rest)
    {bound owned : List Ident} {funs : FunEnv D} {dead : Ident → Prop} {k : Nat}
    {V1 V2 : VEnv D} {st : EvmState} {V2' : VEnv D} {st' : EvmState} {o : Outcome}
    (hcond : (alwaysEval bound e && dsDead x rest) = true)
    (hb : BoundOK V1 bound) (how : ∀ y, y ∈ owned → AboveK k y V1)
    (hrel : VChg dead k (fun _ => False) V1 V2)
    (hd : ∀ y, dead y → dsDead y (.letDecl [x] (some e) :: rest) = true)
    (hstep : Step D funs V2 st (.stmts (dsSweep bound owned (.letDecl [x] (some e) :: rest)))
      (.sres V2' st' o)) :
    ∃ (V1' : VEnv D) (dead' : Ident → Prop),
      Step D funs V1 st (.stmts (.letDecl [x] (some e) :: rest)) (.sres V1' st' o) ∧
      VChg dead' k (fun _ => False) V1' V2' := by
  have hc := hcond
  rw [Bool.and_eq_true] at hc
  obtain ⟨hae, hdead⟩ := hc
  have hsweep : dsSweep bound owned (.letDecl [x] (some e) :: rest)
      = .letDecl [x] none :: dsSweep (x :: bound) (x :: owned) rest := by
    simp only [dsSweep, hcond, if_true]
  rw [hsweep] at hstep
  have hk : k ≤ V1.length := hrel.tail_le
  obtain ⟨v, hv⟩ := dcEvalRun hb funs st e hae
  have hgrow : VChg dead k (fun y => (fun _ : Ident => False) y ∨ y = x) V1 V2 :=
    hrel.grow_seen (extra := fun y => y = x)
      (fun y hy hc2 => (dsDead_letSome (hd y hy)).2.1 (by simp [hc2]))
  have hnew : VChg (fun y => dsDead y rest = true) k (fun _ => False)
      ((x, v) :: V1) ((x, (evmWithExternal calls creates).zero) :: V2) :=
    VChg.diff hdead (fun h => h)
      (hgrow.mono_seen (fun y _ hy => (dsDead_letSome (hd y hy)).2.2))
  cases hstep with
  | seqCons hs hrest =>
      cases hs with
      | letZero =>
          obtain ⟨V1', dead', hstep1, hrel1⟩ := ih
            (bound := x :: bound) (owned := x :: owned)
            (fun y hy => by
              rcases List.mem_cons.mp hy with rfl | hy
              · simp
              · exact List.mem_cons_of_mem _ (hb y hy))
            (fun y hy => by
              rcases List.mem_cons.mp hy with rfl | hy
              · exact AboveK.head hk
              · exact AboveK.prepend (pre := [(x, v)]) (how y hy))
            hnew (fun y hy => hy) hrest
          exact ⟨V1', dead', Step.seqCons (Step.letVal hv rfl) hstep1, hrel1⟩
  | seqStop hs hne =>
      cases hs with
      | letZero => exact absurd rfl hne

/-- **Backward simulation of one sweep.** -/
theorem dsSweep_bwd : ∀ ss : List (Stmt Op), SweepBwd (calls := calls) (creates := creates) ss := by
  intro ss
  induction ss with
  | nil =>
      intro bound owned funs dead k V1 V2 st V2' st' o hb how hrel hd hstep
      cases hstep with
      | seqNil => exact ⟨V1, dead, Step.seqNil, hrel⟩
  | cons s rest ih =>
      intro bound owned funs dead k V1 V2 st V2' st' o hb how hrel hd hstep
      cases s with
      | block body =>
          exact sweepKeep_bwd ih (by simp only [dsSweep]) hb how hrel
            (fun x hx => (dsDead_pass (hd x hx) (Or.inl ⟨body, rfl⟩)).1)
            (fun _ x hx => (dsDead_pass (hd x hx) (Or.inl ⟨body, rfl⟩)).2) hstep
      | funDef n ps rs body =>
          exact sweepKeep_bwd ih (by simp only [dsSweep]) hb how hrel
            (fun x hx => (dsDead_pass (hd x hx) (Or.inr (Or.inl ⟨n, ps, rs, body, rfl⟩))).1)
            (fun _ x hx => (dsDead_pass (hd x hx) (Or.inr (Or.inl ⟨n, ps, rs, body, rfl⟩))).2)
            hstep
      | cond c body =>
          exact sweepKeep_bwd ih (by simp only [dsSweep]) hb how hrel
            (fun x hx => (dsDead_pass (hd x hx) (Or.inr (Or.inr (Or.inl ⟨c, body, rfl⟩)))).1)
            (fun _ x hx => (dsDead_pass (hd x hx) (Or.inr (Or.inr (Or.inl ⟨c, body, rfl⟩)))).2)
            hstep
      | «switch» c cs dflt =>
          exact sweepKeep_bwd ih (by simp only [dsSweep]) hb how hrel
            (fun x hx =>
              (dsDead_pass (hd x hx) (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, cs, dflt, rfl⟩))))).1)
            (fun _ x hx =>
              (dsDead_pass (hd x hx) (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, cs, dflt, rfl⟩))))).2)
            hstep
      | forLoop init c post body =>
          exact sweepKeep_bwd ih (by simp only [dsSweep]) hb how hrel
            (fun x hx => (dsDead_pass (hd x hx)
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨init, c, post, body, rfl⟩)))))).1)
            (fun _ x hx => (dsDead_pass (hd x hx)
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨init, c, post, body, rfl⟩)))))).2)
            hstep
      | exprStmt e =>
          exact sweepKeep_bwd ih (by simp only [dsSweep]) hb how hrel
            (fun x hx => (dsDead_pass (hd x hx)
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e, rfl⟩)))))).1)
            (fun _ x hx => (dsDead_pass (hd x hx)
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e, rfl⟩)))))).2)
            hstep
      | «break» =>
          exact sweepKeep_bwd ih (by simp only [dsSweep]) hb how hrel
            (fun _ _ => rfl) (fun h => by cases h) hstep
      | «continue» =>
          exact sweepKeep_bwd ih (by simp only [dsSweep]) hb how hrel
            (fun _ _ => rfl) (fun h => by cases h) hstep
      | «leave» =>
          exact sweepKeep_bwd ih (by simp only [dsSweep]) hb how hrel
            (fun _ _ => rfl) (fun h => by cases h) hstep
      | assign ys e =>
          rcases ys with _ | ⟨x, ys'⟩
          · exact sweepAssignKeep_bwd ih (by simp only [dsSweep]) hb how hrel hd hstep
          · rcases ys' with _ | ⟨y, ys''⟩
            · by_cases hcond : (owned.contains x && alwaysEval bound e && dsDead x rest) = true
              · exact sweepAssignDrop_bwd ih hcond hb how hrel hd hstep
              · rw [Bool.not_eq_true] at hcond
                exact sweepAssignKeep_bwd ih
                  (by simp only [dsSweep, hcond, Bool.false_eq_true, if_false]) hb how hrel hd hstep
            · exact sweepAssignKeep_bwd ih (by simp only [dsSweep]) hb how hrel hd hstep
      | letDecl xs val =>
          cases val with
          | none =>
              exact sweepLetKeep_bwd ih (by simp only [dsSweep]) hb how hrel
                (fun x hx => by
                  have h1 := (dsDead_letNone (hd x hx)).1
                  simp [stmtMentions, optExprMentions, h1])
                (fun x hx => (dsDead_letNone (hd x hx)).2) hstep
          | some e =>
              rcases xs with _ | ⟨x, xs'⟩
              · exact sweepLetKeep_bwd ih (by simp only [dsSweep]) hb how hrel
                  (fun z hz => by
                    have h1 := dsDead_letSome (hd z hz)
                    simp [stmtMentions, optExprMentions, h1.1, h1.2.1])
                  (fun z hz => (dsDead_letSome (hd z hz)).2.2) hstep
              · rcases xs' with _ | ⟨y, xs''⟩
                · by_cases hcond : (alwaysEval bound e && dsDead x rest) = true
                  · exact sweepLetDrop_bwd ih hcond hb how hrel hd hstep
                  · rw [Bool.not_eq_true] at hcond
                    exact sweepLetKeep_bwd ih
                      (by simp only [dsSweep, hcond, Bool.false_eq_true, if_false,
                        List.singleton_append]) hb how hrel
                      (fun z hz => by
                        have h1 := dsDead_letSome (hd z hz)
                        simp [stmtMentions, optExprMentions, h1.1, h1.2.1])
                      (fun z hz => (dsDead_letSome (hd z hz)).2.2) hstep
                · exact sweepLetKeep_bwd ih (by simp only [dsSweep]) hb how hrel
                    (fun z hz => by
                      have h1 := dsDead_letSome (hd z hz)
                      simp [stmtMentions, optExprMentions, h1.1, h1.2.1])
                    (fun z hz => (dsDead_letSome (hd z hz)).2.2) hstep

end YulEvmCompiler.Optimizer
