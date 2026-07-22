import YulEvmCompiler.Optimizer.Implementation.StackLayout
import YulEvmCompiler.Optimizer.Implementation.InlineCallsSound
import YulEvmCompiler.Optimizer.Implementation.DeadPure
import YulEvmCompiler.Optimizer.Implementation.BoundFunCongr
import YulEvmCompiler.Optimizer.Spec.Pass
import YulEvmCompiler.ObjectResolve
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
/-!
# Soundness of smart stack layout

The expression scheduler is justified by associativity while preserving Yul's
right-to-left evaluation order, including state changes and halts.  The slot
reuse simulation is indexed by the depths of the removed binding and the
reused slot.  Both depths are measured from the bottom of the variable
environment, so declarations prepend above them and nested-block `restore`
preserves them. The tail-carrier proof uses the same restoration invariant to
show that sinking a dominated region removes only dead locals before copying
its one live-out value to a result slot.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM

variable {calls : ExternalCalls} {creates : ExternalCreates}
local notation "D" => evmWithExternal calls creates

/-! ### Expression-pressure scheduling -/

private theorem args_two_value_inv {funs : FunEnv D} {V st a b vals st'}
    (h : EvalArgs D funs V st [a, b] (.vals vals st')) :
    ∃ vb stb va, EvalExpr D funs V st b (.vals [vb] stb) ∧
      EvalExpr D funs V stb a (.vals [va] st') ∧ vals = [va, vb] := by
  cases h with
  | argsCons hbTail ha =>
      cases hbTail with
      | argsCons hnil hb => cases hnil; exact ⟨_, _, _, hb, ha, rfl⟩

private theorem args_two_halt_inv {funs : FunEnv D} {V st a b st'}
    (h : EvalArgs D funs V st [a, b] (.halt st')) :
    EvalExpr D funs V st b (.halt st') ∨
      ∃ vb stb, EvalExpr D funs V st b (.vals [vb] stb) ∧
        EvalExpr D funs V stb a (.halt st') := by
  cases h with
  | argsRestHalt hbTail =>
      cases hbTail with
      | argsRestHalt hnil => cases hnil
      | argsHeadHalt hnil hb => cases hnil; exact .inl hb
  | argsHeadHalt hbTail ha =>
      cases hbTail with
      | argsCons hnil hb => cases hnil; exact .inr ⟨_, _, hb, ha⟩

private theorem args_two_value {funs : FunEnv D} {V st a b va vb stb st'}
    (hb : EvalExpr D funs V st b (.vals [vb] stb))
    (ha : EvalExpr D funs V stb a (.vals [va] st')) :
    EvalArgs D funs V st [a, b] (.vals [va, vb] st') :=
  Step.argsCons (Step.argsCons Step.argsNil hb) ha

private theorem args_two_halt_right {funs : FunEnv D} {V st a b st'}
    (hb : EvalExpr D funs V st b (.halt st')) :
    EvalArgs D funs V st [a, b] (.halt st') :=
  Step.argsRestHalt (Step.argsHeadHalt Step.argsNil hb)

private theorem args_two_halt_left {funs : FunEnv D} {V st a b vb stb st'}
    (hb : EvalExpr D funs V st b (.vals [vb] stb))
    (ha : EvalExpr D funs V stb a (.halt st')) :
    EvalArgs D funs V st [a, b] (.halt st') :=
  Step.argsHeadHalt (Step.argsCons Step.argsNil hb) ha

private theorem add_value_inv {funs : FunEnv D} {V st a b vals st'}
    (h : EvalExpr D funs V st (.builtin .add [a, b]) (.vals vals st')) :
    ∃ va vb stb, EvalExpr D funs V st b (.vals [vb] stb) ∧
      EvalExpr D funs V stb a (.vals [va] st') ∧ vals = [va + vb] := by
  cases h with
  | builtinOk hargs hop =>
      obtain ⟨vb, stb, va, hb, ha, rfl⟩ := args_two_value_inv hargs
      have hr := pureFn_builtin_inv (w := va + vb) (by simp [pureFn]) hop
      injection hr with hvals hst
      subst hvals; subst hst
      exact ⟨va, vb, stb, hb, ha, rfl⟩

private theorem add_halt_inv {funs : FunEnv D} {V st a b st'}
    (h : EvalExpr D funs V st (.builtin .add [a, b]) (.halt st')) :
    EvalExpr D funs V st b (.halt st') ∨
      ∃ vb stb, EvalExpr D funs V st b (.vals [vb] stb) ∧
        EvalExpr D funs V stb a (.halt st') := by
  cases h with
  | builtinHalt hargs hop =>
      obtain ⟨vb, stb, va, hb, ha, rfl⟩ := args_two_value_inv hargs
      have hr := pureFn_builtin_inv (w := va + vb) (by simp [pureFn]) hop
      contradiction
  | builtinArgsHalt hargs => exact args_two_halt_inv hargs

private theorem add_value {funs : FunEnv D} {V st a b va vb stb st'}
    (hb : EvalExpr D funs V st b (.vals [vb] stb))
    (ha : EvalExpr D funs V stb a (.vals [va] st')) :
    EvalExpr D funs V st (.builtin .add [a, b]) (.vals [va + vb] st') :=
  Step.builtinOk (args_two_value hb ha) (pureFn_builtin (by simp [pureFn]) st')

private theorem add_halt_right {funs : FunEnv D} {V st a b st'}
    (hb : EvalExpr D funs V st b (.halt st')) :
    EvalExpr D funs V st (.builtin .add [a, b]) (.halt st') :=
  Step.builtinArgsHalt (args_two_halt_right hb)

private theorem add_halt_left {funs : FunEnv D} {V st a b vb stb st'}
    (hb : EvalExpr D funs V st b (.vals [vb] stb))
    (ha : EvalExpr D funs V stb a (.halt st')) :
    EvalExpr D funs V st (.builtin .add [a, b]) (.halt st') :=
  Step.builtinArgsHalt (args_two_halt_left hb ha)

private theorem add_assoc_imp {a b c : Expr Op} {funs V st r} :
    EvalExpr D funs V st (.builtin .add [.builtin .add [a, b], c]) r →
    EvalExpr D funs V st (.builtin .add [a, .builtin .add [b, c]]) r := by
  intro h
  cases r with
  | vals vals st' =>
      obtain ⟨vab, vc, stc, hc, hab, rfl⟩ := add_value_inv h
      obtain ⟨va, vb, stb, hb, ha, heq⟩ := add_value_inv hab
      injection heq with heq'; subst vab
      simpa [BitVec.add_assoc] using add_value (add_value hc hb) ha
  | halt st' =>
      rcases add_halt_inv h with hc | ⟨vc, stc, hc, hab⟩
      · exact add_halt_right (add_halt_right hc)
      · rcases add_halt_inv hab with hb | ⟨vb, stb, hb, ha⟩
        · exact add_halt_right (add_halt_left hc hb)
        · exact add_halt_left (add_value hc hb) ha

private theorem add_assoc_rev_imp {a b c : Expr Op} {funs V st r} :
    EvalExpr D funs V st (.builtin .add [a, .builtin .add [b, c]]) r →
    EvalExpr D funs V st (.builtin .add [.builtin .add [a, b], c]) r := by
  intro h
  cases r with
  | vals vals st' =>
      obtain ⟨va, vbc, stbc, hbc, ha, rfl⟩ := add_value_inv h
      obtain ⟨vb, vc, stc, hc, hb, heq⟩ := add_value_inv hbc
      injection heq with heq'; subst vbc
      simpa [BitVec.add_assoc] using add_value hc (add_value hb ha)
  | halt st' =>
      rcases add_halt_inv h with hbc | ⟨vbc, stbc, hbc, ha⟩
      · rcases add_halt_inv hbc with hc | ⟨vc, stc, hc, hb⟩
        · exact add_halt_right hc
        · exact add_halt_left hc (add_halt_right hb)
      · obtain ⟨vb, vc, stc, hc, hb, heq⟩ := add_value_inv hbc
        injection heq with heq'; subst vbc
        exact add_halt_left hc (add_halt_left hb ha)

theorem add_assoc_equiv (a b c : Expr Op) :
    EquivExpr D (.builtin .add [.builtin .add [a, b], c])
      (.builtin .add [a, .builtin .add [b, c]]) :=
  fun _ _ _ _ => ⟨add_assoc_imp, add_assoc_rev_imp⟩

theorem rightAssocAdd_equiv (a c : Expr Op) :
    EquivExpr D (.builtin .add [a, c]) (rightAssocAdd a c) := by
  fun_induction rightAssocAdd a c
  · next a b c ihb iha =>
      exact (add_assoc_equiv a b c).trans
        ((EquivExpr.builtin_congr Op.add (EquivArgs.of_forall₂
          (.cons (EquivExpr.refl a) (.cons ihb .nil)))).trans iha)
  · exact EquivExpr.refl _

theorem scheduleBuiltin_equiv (op : Op) (args : List (Expr Op)) :
    EquivExpr D (.builtin op args) (scheduleBuiltin op args) := by
  unfold scheduleBuiltin
  by_cases hop : op = .add
  · subst op
    simp only [if_pos]
    cases args with
    | nil => exact EquivExpr.refl _
    | cons a rest =>
      cases rest with
      | nil => exact EquivExpr.refl _
      | cons b tail =>
        cases tail with
        | nil => exact rightAssocAdd_equiv a b
        | cons c tail => exact EquivExpr.refl _
  · rw [if_neg hop]
    exact EquivExpr.refl _

mutual
  theorem scheduleExpr_equiv : ∀ e : Expr Op, EquivExpr D e (scheduleExpr e)
    | .lit _ => EquivExpr.refl _
    | .var _ => EquivExpr.refl _
    | .builtin op args =>
        (EquivExpr.builtin_congr op
          (EquivArgs.of_forall₂ (scheduleArgs_forall2 args))).trans
        (scheduleBuiltin_equiv op (scheduleArgs args))
    | .call f args =>
        EquivExpr.call_congr f (EquivArgs.of_forall₂ (scheduleArgs_forall2 args))

  theorem scheduleArgs_forall2 : ∀ args : List (Expr Op),
      List.Forall₂ (EquivExpr D) args (scheduleArgs args)
    | [] => .nil
    | e :: rest => .cons (scheduleExpr_equiv e) (scheduleArgs_forall2 rest)
end

mutual
  theorem scheduleStmt_equiv : ∀ s : Stmt Op, EquivStmt D s (scheduleStmt s)
    | .block body => by
        rw [scheduleStmt]
        exact EquivBlock.of_stmts_funs
          (EquivStmts.of_forall₂ (scheduleStmts_forall2 body))
          (scopeRel_hoistSchedule body)
    | .funDef f ps rs body => by
        simpa only [scheduleStmt] using funDef_equiv f ps rs body (scheduleStmts body)
    | .letDecl xs (some e) => by
        simpa only [scheduleStmt, Option.map] using
          EquivStmt.letDecl_congr xs (scheduleExpr_equiv e)
    | .letDecl xs none => by simp only [scheduleStmt]; exact EquivStmt.refl _
    | .assign xs e => by
        simpa only [scheduleStmt] using EquivStmt.assign_congr xs (scheduleExpr_equiv e)
    | .cond c body => by
        simpa only [scheduleStmt] using EquivStmt.cond_congr (scheduleExpr_equiv c)
          (EquivBlock.of_stmts_funs (EquivStmts.of_forall₂ (scheduleStmts_forall2 body))
            (scopeRel_hoistSchedule body))
    | .switch c cases dflt => by
        cases dflt with
        | none =>
            rw [scheduleStmt]
            exact EquivStmt.switch_congr (scheduleExpr_equiv c)
              (scheduleCases_forall2 cases) (EquivBlock.refl [])
        | some body =>
            rw [scheduleStmt]
            exact EquivStmt.switch_congr (scheduleExpr_equiv c)
              (scheduleCases_forall2 cases)
              (EquivBlock.of_stmts_funs
                (EquivStmts.of_forall₂ (scheduleStmts_forall2 body))
                (scopeRel_hoistSchedule body))
    | .forLoop init c post body => by
        simpa only [scheduleStmt] using EquivStmt.forLoop_congr init (scheduleExpr_equiv c)
          (EquivBlock.of_stmts_funs (EquivStmts.of_forall₂ (scheduleStmts_forall2 post))
            (scopeRel_hoistSchedule post))
          (EquivBlock.of_stmts_funs (EquivStmts.of_forall₂ (scheduleStmts_forall2 body))
            (scopeRel_hoistSchedule body))
    | .exprStmt e => by
        simpa only [scheduleStmt] using EquivStmt.exprStmt_congr (scheduleExpr_equiv e)
    | .break => by simp only [scheduleStmt]; exact EquivStmt.refl _
    | .continue => by simp only [scheduleStmt]; exact EquivStmt.refl _
    | .leave => by simp only [scheduleStmt]; exact EquivStmt.refl _

  theorem scheduleStmts_forall2 : ∀ ss : Block Op,
      List.Forall₂ (EquivStmt D) ss (scheduleStmts ss)
    | [] => by rw [scheduleStmts]; exact .nil
    | s :: rest => by
        rw [scheduleStmts]
        exact .cons (scheduleStmt_equiv s) (scheduleStmts_forall2 rest)

  theorem scheduleCases_forall2 : ∀ cases : List (Literal × Block Op),
      List.Forall₂ (fun p q => p.1 = q.1 ∧ EquivBlock D p.2 q.2)
        cases (scheduleCases cases)
    | [] => by rw [scheduleCases]; exact .nil
    | (l, body) :: rest => by
        rw [scheduleCases]
        exact .cons ⟨rfl, EquivBlock.of_stmts_funs
          (EquivStmts.of_forall₂ (scheduleStmts_forall2 body))
          (scopeRel_hoistSchedule body)⟩ (scheduleCases_forall2 rest)

  theorem scopeRel_hoistSchedule : ∀ ss : Block Op,
      ScopeRel D (hoist D ss) (hoist D (scheduleStmts ss))
    | [] => by rw [scheduleStmts]; exact ScopeRel.refl []
    | .funDef f ps rs body :: rest => by
        simp only [scheduleStmts, scheduleStmt, hoist, List.filterMap_cons]
        exact .cons ⟨rfl, rfl, rfl,
          EquivBlock.of_stmts_funs (EquivStmts.of_forall₂ (scheduleStmts_forall2 body))
            (scopeRel_hoistSchedule body)⟩ (scopeRel_hoistSchedule rest)
    | .block _ :: rest => by
        simpa [scheduleStmts, scheduleStmt, hoist] using scopeRel_hoistSchedule rest
    | .letDecl _ _ :: rest => by
        simpa [scheduleStmts, scheduleStmt, hoist] using scopeRel_hoistSchedule rest
    | .assign _ _ :: rest => by
        simpa [scheduleStmts, scheduleStmt, hoist] using scopeRel_hoistSchedule rest
    | .cond _ _ :: rest => by
        simpa [scheduleStmts, scheduleStmt, hoist] using scopeRel_hoistSchedule rest
    | .switch c cases dflt :: rest => by
        cases dflt <;>
          simpa [scheduleStmts, scheduleStmt, hoist] using scopeRel_hoistSchedule rest
    | .forLoop _ _ _ _ :: rest => by
        simpa [scheduleStmts, scheduleStmt, hoist] using scopeRel_hoistSchedule rest
    | .exprStmt _ :: rest => by
        simpa [scheduleStmts, scheduleStmt, hoist] using scopeRel_hoistSchedule rest
    | .break :: rest => by
        simpa [scheduleStmts, scheduleStmt, hoist] using scopeRel_hoistSchedule rest
    | .continue :: rest => by
        simpa [scheduleStmts, scheduleStmt, hoist] using scopeRel_hoistSchedule rest
    | .leave :: rest => by
        simpa [scheduleStmts, scheduleStmt, hoist] using scopeRel_hoistSchedule rest
end

theorem scheduleBlock_equiv (b : Block Op) : EquivBlock D b (scheduleStmts b) :=
  EquivBlock.of_stmts_funs (EquivStmts.of_forall₂ (scheduleStmts_forall2 b))
    (scopeRel_hoistSchedule b)

/-! ### Adjacent call-result copy-back -/

private def tempIns (base : Nat) : List Ident → List (Nat × Ident)
  | [] => []
  | t :: ts => (base + ts.length, t) :: tempIns base ts

private theorem tempIns_names {base : Nat} : ∀ {ts : List Ident} {p},
    p ∈ tempIns base ts → p.2 ∈ ts := by
  intro ts
  induction ts with
  | nil => simp [tempIns]
  | cons t ts ih =>
      intro p hp
      simp only [tempIns, List.mem_cons] at hp
      rcases hp with rfl | hp
      · simp
      · exact List.mem_cons_of_mem _ (ih hp)

private theorem tempIns_depth {base : Nat} : ∀ {ts : List Ident} {p},
    p ∈ tempIns base ts → base ≤ p.1 := by
  intro ts
  induction ts with
  | nil => simp [tempIns]
  | cons t ts ih =>
      intro p hp
      simp only [tempIns, List.mem_cons] at hp
      rcases hp with rfl | hp
      · omega
      · exact ih hp

private theorem zip_mins (V : VEnv D) : ∀ {ts : List Ident} {vals : List U256},
    vals.length = ts.length →
    MIns (tempIns V.length ts) (ts.zip vals ++ V) V := by
  intro ts
  induction ts with
  | nil =>
      intro vals hlen
      cases vals with
      | nil => exact .nil V
      | cons _ _ => simp at hlen
  | cons t ts ih =>
      intro vals hlen
      cases vals with
      | nil => simp at hlen
      | cons v vals =>
          have hlen' : vals.length = ts.length := by simpa using hlen
          have hm := ih hlen'
          have ht := hm.insTop t v
          simpa [tempIns, List.length_append, hlen', Nat.add_comm] using ht

private theorem takeCopyBack_spec : ∀ {ts : List Ident} {rest ds suffix},
    takeCopyBack ts rest = some (ds, suffix) →
    rest = copyBackStmts ts ds ++ suffix ∧ ds.length = ts.length := by
  intro ts
  induction ts with
  | nil =>
      intro rest ds suffix h
      simp [takeCopyBack] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [copyBackStmts]
  | cons t ts ih =>
      intro rest ds suffix h
      cases rest with
      | nil => simp [takeCopyBack] at h
      | cons s rest =>
          cases s with
          | assign xs e =>
              cases xs with
              | nil => simp [takeCopyBack] at h
              | cons d xs =>
                cases xs with
                | cons _ _ => simp [takeCopyBack] at h
                | nil =>
                  cases e with
                  | var u =>
                    simp only [takeCopyBack] at h
                    split at h
                    · next hne => simp at h
                    · next heq =>
                      have hut : u = t := by simpa using heq
                      subst u
                      obtain ⟨tailDs, htail, hpair⟩ :=
                        Option.bind_eq_some_iff.mp h
                      cases hpair
                      obtain ⟨hrest, hlen⟩ := ih htail
                      subst rest
                      simp [copyBackStmts, hlen]
                  | lit _ | builtin _ _ | call _ _ => simp [takeCopyBack] at h
          | block _ => simp [takeCopyBack] at h
          | funDef _ _ _ _ => simp [takeCopyBack] at h
          | letDecl _ _ => simp [takeCopyBack] at h
          | cond _ _ => simp [takeCopyBack] at h
          | «switch» _ _ _ => simp [takeCopyBack] at h
          | forLoop _ _ _ _ => simp [takeCopyBack] at h
          | exprStmt _ => simp [takeCopyBack] at h
          | «break» => simp [takeCopyBack] at h
          | «continue» => simp [takeCopyBack] at h
          | «leave» => simp [takeCopyBack] at h

private theorem copy_zip_gets {ts : List Ident} (hnd : ts.Nodup) :
    ∀ {vals : List U256}, vals.length = ts.length →
      ts.map (fun t => (VEnv.get (ts.zip vals : VEnv D) t).getD
        (evmWithExternal calls creates).zero) = vals := by
  induction ts with
  | nil =>
      intro vals hlen
      cases vals with
      | nil => rfl
      | cons _ _ => simp at hlen
  | cons t ts ih =>
      intro vals hlen
      cases vals with
      | nil => simp at hlen
      | cons v vals =>
          have ht : t ∉ ts := (List.nodup_cons.mp hnd).1
          have hnd' : ts.Nodup := (List.nodup_cons.mp hnd).2
          have hlen' : vals.length = ts.length := by simpa using hlen
          simp only [List.zip_cons_cons, List.map_cons]
          rw [show VEnv.get (((t, v) :: ts.zip vals) : VEnv D) t = some v by
            simp [VEnv.get]]
          congr 1
          calc
            ts.map (fun u => (VEnv.get ((t, v) :: ts.zip vals) u).getD
                (evmWithExternal calls creates).zero) =
                ts.map (fun u => (VEnv.get (ts.zip vals) u).getD
                  (evmWithExternal calls creates).zero) := by
              apply List.map_congr_left
              intro u hu
              have htu : t ≠ u := fun h => ht (h ▸ hu)
              simp [VEnv.get, htu]
            _ = vals := ih hnd' hlen'

private theorem hoist_copyBackStmts (ts ds : List Ident) :
    hoist D (copyBackStmts ts ds) = [] := by
  unfold copyBackStmts
  induction ds generalizing ts with
  | nil => simp [hoist]
  | cons d ds ih =>
      cases ts with
      | nil => simp [hoist]
      | cons t ts => simp [hoist, ih]

/-- The semantic core of copy-back coalescing.  The temporary result frame is
an `MIns` extension of the direct-assignment frame; mention-freedom lets the
unchanged suffix run with that frame removed, and block restoration erases it
on every outcome. -/
theorem copyBackSite_equivBlock {pre suffix : Block Op} {ts ds : List Ident}
    {call : Expr Op}
    (hlen : ds.length = ts.length) (hnd : ts.Nodup)
    (hdisj : ∀ d ∈ ds, d ∉ ts)
    (hfree : ∀ t ∈ ts, stmtsMentions t suffix = false) :
    EquivBlock D
      (pre ++ ([.letDecl ts (some call)] ++ copyBackStmts ts ds ++ suffix))
      (pre ++ ([.assign ds call] ++ suffix)) := by
  intro funs V st V' st' o
  have hhoist : hoist D
      (pre ++ ([.letDecl ts (some call)] ++ copyBackStmts ts ds ++ suffix)) =
      hoist D (pre ++ ([.assign ds call] ++ suffix)) := by
    simp only [hoist_append]
    rw [hoist_copyBackStmts]
    simp [hoist]
  let F := hoist D (pre ++ ([.assign ds call] ++ suffix)) :: funs
  constructor
  · intro hrun
    cases hrun with
    | block hb =>
      rw [hhoist] at hb
      rcases stmts_append_fwd hb with ⟨Vp, stp, hpre, hsite⟩ | ⟨hne, hpre⟩
      · cases hsite with
        | seqStop hlet hne =>
          cases hlet with
          | letVal _ _ => exact absurd rfl hne
          | letHalt hcall =>
            exact Step.block (stmts_append_normal hpre
              (Step.seqStop (Step.assignHalt hcall) (by simp)))
        | seqCons hlet hrest =>
          cases hlet with
          | @letVal _ _ _ _ _ vals stv hcall hvals =>
            have hvals' : vals.length = ts.length := hvals
            have hkeys : (ts.zip vals).map Prod.fst = ts :=
              List.map_fst_zip (le_of_eq hvals.symm)
            rcases stmts_append_fwd hrest with
              ⟨Vm, stm, hcopies, hsuffix⟩ | ⟨hneCopies, hcopies⟩
            · obtain ⟨hVm, hstm, hoCopies⟩ := assigns_bwd hcopies
                (fun t ht => by rw [hkeys]; exact ht)
                (fun d hd => by rw [hkeys]; exact hdisj d hd) hlen
              subst stm
              rw [copy_zip_gets hnd hvals'] at hVm
              subst Vm
              have hm : MIns (tempIns Vp.length ts)
                  (ts.zip vals ++ VEnv.setMany Vp ds vals)
                  (VEnv.setMany Vp ds vals) := by
                have hm0 := zip_mins (calls := calls) (creates := creates)
                  (VEnv.setMany Vp ds vals) hvals'
                rw [VEnv.setMany_length] at hm0
                exact hm0
              have hifree : InsFree (tempIns Vp.length ts) (.stmts suffix) := by
                intro p hp
                exact hfree p.2 (tempIns_names hp)
              obtain ⟨Vt, htargetSuffix, hm'⟩ := hm.frameRemove hsuffix hifree
              have htargetSite := Step.seqCons
                (Step.assignVal hcall (hvals.trans hlen.symm))
                htargetSuffix
              have htarget := Step.block (stmts_append_normal hpre htargetSite)
              have hbase : V.length ≤ Vp.length := venvLen_mono hpre rfl
              have herase := restore_mins_le (base := V) hm' (fun p hp =>
                hbase.trans (tempIns_depth hp))
              rw [← herase] at htarget
              exact htarget
            · obtain ⟨_, _, hoCopies⟩ := assigns_bwd hcopies
                (fun t ht => by rw [hkeys]; exact ht)
                (fun d hd => by rw [hkeys]; exact hdisj d hd) hlen
              exact absurd hoCopies hneCopies
      · exact Step.block (stmts_append_early hpre hne)

  · intro hrun
    cases hrun with
    | block hb =>
      rw [← hhoist] at hb
      rcases stmts_append_fwd hb with ⟨Vp, stp, hpre, hsite⟩ | ⟨hne, hpre⟩
      · cases hsite with
        | seqStop hassign hne =>
          cases hassign with
          | assignVal _ _ => exact absurd rfl hne
          | assignHalt hcall =>
            exact Step.block (stmts_append_normal hpre
              (Step.seqStop (Step.letHalt hcall) (by simp)))
        | seqCons hassign hsuffix =>
          cases hassign with
          | assignVal hcall hvals =>
            rename_i stv vals
            have hvals' : vals.length = ts.length := hvals.trans hlen
            have hkeys : (ts.zip vals).map Prod.fst = ts :=
              List.map_fst_zip (le_of_eq hvals'.symm)
            have hm : MIns (tempIns Vp.length ts)
                (ts.zip vals ++ VEnv.setMany Vp ds vals)
                (VEnv.setMany Vp ds vals) := by
              have hm0 := zip_mins (calls := calls) (creates := creates)
                (VEnv.setMany Vp ds vals) hvals'
              rw [VEnv.setMany_length] at hm0
              exact hm0
            have hifree : InsFree (tempIns Vp.length ts) (.stmts suffix) := by
              intro p hp
              exact hfree p.2 (tempIns_names hp)
            obtain ⟨Vs, hsourceSuffix, hm'⟩ := hm.frameAdd hsuffix hifree
            have hcopies := assigns_fwd (A' := (ts.zip vals : VEnv D))
              (fun t ht => by rw [hkeys]; exact ht)
              (fun d hd => by rw [hkeys]; exact hdisj d hd)
              hlen (hoist D
                (pre ++ ([.letDecl ts (some call)] ++
                  copyBackStmts ts ds ++ suffix)) :: funs) Vp stv
            rw [copy_zip_gets hnd hvals'] at hcopies
            have hafterLet := stmts_append_normal hcopies hsourceSuffix
            have hsourceSite := Step.seqCons (Step.letVal hcall hvals') hafterLet
            have hsource := Step.block (stmts_append_normal hpre hsourceSite)
            have hbase : V.length ≤ Vp.length := venvLen_mono hpre rfl
            have herase := restore_mins_le (base := V) hm' (fun p hp =>
              hbase.trans (tempIns_depth hp))
            rw [herase] at hsource
            exact hsource
      · exact Step.block (stmts_append_early hpre hne)


theorem copyBackHere_sound {layout : List Ident} {ss ss' : Block Op}
    (h : copyBackHere layout ss = some ss') (pre : Block Op) :
    EquivBlock D (pre ++ ss) (pre ++ ss') := by
  cases ss with
  | nil => simp [copyBackHere] at h
  | cons s rest =>
    cases s with
    | letDecl ts val =>
      cases val with
      | none => simp [copyBackHere] at h
      | some e =>
        cases e with
        | call f args =>
          simp only [copyBackHere] at h
          split at h
          · simp at h
          · next htemps =>
            obtain ⟨pair, htake, hafter⟩ := Option.bind_eq_some_iff.mp h
            obtain ⟨ds, suffix⟩ := pair
            dsimp only at hafter
            split at hafter
            · next hok =>
              cases hafter
              obtain ⟨hrest, hlen⟩ := takeCopyBack_spec htake
              subst rest
              have hnotempty : ts ≠ [] := by
                intro heq
                subst ts
                exact htemps (by simp)
              have hnodup : ts.Nodup := by
                by_contra hn
                exact htemps (by simp [hn])
              simp only [Bool.and_eq_true] at hok
              have hdisjAll := List.all_eq_true.mp hok.2
              have hdisj : ∀ d ∈ ds, d ∉ ts := by
                intro d hd hdt
                have := hdisjAll d hdt
                simp only [Bool.and_eq_true, Bool.not_eq_true] at this
                have hnot : d ∉ ds := by simpa using this.1
                exact hnot hd
              have hfree : ∀ t ∈ ts, stmtsMentions t suffix = false := by
                intro t ht
                have := hdisjAll t ht
                simp only [Bool.and_eq_true, Bool.not_eq_true] at this
                simpa using this.2
              simpa [List.append_assoc] using copyBackSite_equivBlock
                (calls := calls) (creates := creates) (pre := pre)
                (call := .call f args) hlen hnodup hdisj hfree
            · simp at hafter
        | lit _ => simp [copyBackHere] at h
        | var _ => simp [copyBackHere] at h
        | builtin _ _ => simp [copyBackHere] at h
    | block _ => simp [copyBackHere] at h
    | funDef _ _ _ _ => simp [copyBackHere] at h
    | assign _ _ => simp [copyBackHere] at h
    | cond _ _ => simp [copyBackHere] at h
    | «switch» _ _ _ => simp [copyBackHere] at h
    | forLoop _ _ _ _ => simp [copyBackHere] at h
    | exprStmt _ => simp [copyBackHere] at h
    | «break» => simp [copyBackHere] at h
    | «continue» => simp [copyBackHere] at h
    | «leave» => simp [copyBackHere] at h

/-! ### Right-to-left call-argument staging -/

private theorem zip_get_of_mem {names : List Ident} (hnd : names.Nodup) :
    ∀ {vals : List U256}, vals.length = names.length →
      ∀ {x v}, (x, v) ∈ names.zip vals →
        VEnv.get (names.zip vals : VEnv D) x = some v := by
  induction names with
  | nil => simp
  | cons n names ih =>
      intro vals hlen x v hm
      cases vals with
      | nil => simp at hlen
      | cons w vals =>
        simp only [List.zip_cons_cons, List.mem_cons] at hm
        rcases hm with h | hm
        · injection h with hx hv
          subst x
          subst v
          simp [VEnv.get]
        · have hn : n ∉ names := (List.nodup_cons.mp hnd).1
          have hnd' := (List.nodup_cons.mp hnd).2
          have hlen' : vals.length = names.length := by simpa using hlen
          have hxmem : x ∈ names := (List.of_mem_zip hm).1
          have hnx : n ≠ x := fun heq => hn (heq ▸ hxmem)
          change VEnv.get ((n, w) :: names.zip vals : VEnv D) x = some v
          rw [VEnv.get_cons]
          simp only [hnx, if_false]
          exact ih hnd' hlen' hm

private theorem varArgs_eval {names : List Ident} (hnd : names.Nodup) :
    ∀ {vals : List U256}, vals.length = names.length →
      ∀ (funs : FunEnv D) (V : VEnv D) (st : EvmState),
      Step D funs (names.zip vals ++ V) st (.args (names.map Expr.var))
        (.eres (.vals vals st)) := by
  intro vals hlen funs V st
  let W : VEnv D := names.zip vals ++ V
  have hlookup : ∀ {x v}, (x, v) ∈ names.zip vals →
      @VEnv.get D W x = some v := by
    intro x v hm
    have hx : x ∈ (names.zip vals).map Prod.fst :=
      List.mem_map_of_mem hm
    change @VEnv.get D (names.zip vals ++ V) x = some v
    rw [VEnv.get_append_mem hx]
    exact zip_get_of_mem hnd hlen hm
  let rec go : ∀ (ns : List Ident) (vs : List U256),
      ns.length = vs.length →
      (∀ {x v}, (x, v) ∈ ns.zip vs →
        @VEnv.get D W x = some v) →
      Step D funs (names.zip vals ++ V) st (.args (ns.map Expr.var))
        (.eres (.vals vs st))
    | [], [], _, _ => Step.argsNil
    | [], _ :: _, h, _ => by simp at h
    | _ :: _, [], h, _ => by simp at h
    | n :: ns, v :: vs, h, hl => by
        rw [List.map_cons]
        exact Step.argsCons
          (go ns vs (by simpa using h)
            (fun hm => hl (List.mem_cons_of_mem _ hm)))
          (Step.var (hl (List.mem_cons_self ..)))
  exact go names vals hlen.symm hlookup

private theorem varArgs_inv {names : List Ident} (hnd : names.Nodup)
    {vals : List U256} (hlen : vals.length = names.length)
    {funs : FunEnv D} {V : VEnv D} {st : EvmState} {r : EResult D}
    (h : Step D funs (names.zip vals ++ V) st (.args (names.map Expr.var))
      (.eres r)) : r = .vals vals st := by
  let W : VEnv D := names.zip vals ++ V
  have hlookup : ∀ {x v}, (x, v) ∈ names.zip vals →
      @VEnv.get D W x = some v := by
    intro x v hm
    have hx : x ∈ (names.zip vals).map Prod.fst := List.mem_map_of_mem hm
    change @VEnv.get D (names.zip vals ++ V) x = some v
    rw [VEnv.get_append_mem hx]
    exact zip_get_of_mem hnd hlen hm
  let rec go : ∀ (ns : List Ident) (vs : List U256),
      ns.length = vs.length →
      (∀ {x v}, (x, v) ∈ ns.zip vs →
        @VEnv.get D W x = some v) →
      ∀ {r : EResult D},
      Step D funs (names.zip vals ++ V) st (.args (ns.map Expr.var)) (.eres r) →
        r = .vals vs st
    | [], [], _, _, _, h => by cases h; rfl
    | [], _ :: _, hlen, _, _, _ => by simp at hlen
    | _ :: _, [], hlen, _, _, _ => by simp at hlen
    | n :: ns, v :: vs, hlen, hl, r, hstep => by
        rw [List.map_cons] at hstep
        cases hstep with
        | argsCons htail hvar =>
          have htailEq := go ns vs (by simpa using hlen)
            (fun hm => hl (List.mem_cons_of_mem _ hm)) htail
          injection htailEq with hout hstate
          subst hout
          subst hstate
          cases hvar with
          | var hv =>
            have hv' : @VEnv.get D W n = some v :=
              hl (x := n) (v := v) (by simp)
            rw [hv'] at hv
            injection hv with heq
            subst heq
            rfl
        | argsRestHalt htail =>
          have := go ns vs (by simpa using hlen)
            (fun hm => hl (List.mem_cons_of_mem _ hm)) htail
          contradiction
        | argsHeadHalt htail hvar => cases hvar
  exact go names vals hlen.symm hlookup h

private theorem hoist_stageDecls (names : List Ident) (args : List (Expr Op)) :
    hoist D (stageDecls names args) = [] := by
  unfold stageDecls
  induction names generalizing args with
  | nil => simp [hoist]
  | cons n names ih =>
      cases args with
      | nil => simp [hoist]
      | cons a args =>
        rw [List.zip_cons_cons, List.reverse_cons, List.map_append, hoist_append]
        simp [hoist, ih]

theorem stageCore_equiv_of (P : String) (xs : List Ident) (f : Ident)
    (args : List (Expr Op))
    (hnc : argsHaveCall args = false)
    (hshadow : argsShadowOK [] ((callCarriers P args.length).zip args) = true)
    (hnd : (callCarriers P args.length).Nodup)
    (hdisj : ∀ x ∈ xs, x ∉ callCarriers P args.length) :
    EquivStmt D (.assign xs (.call f args)) (stageCore P xs f args) := by
  let names := callCarriers P args.length
  have hnames : names.length = args.length := by
    simp [names, callCarriers]
  intro funs V st V' st' o
  constructor
  · intro h
    cases h with
    | assignVal hcall hxs =>
      cases hcall with
      | callOk hargs hlookup harglen hbody hout =>
        rename_i argvals stArgs decl cenv Vend stBody
        have hvals : argvals.length = names.length :=
          (args_length hargs).trans hnames.symm
        have hlets := argLets_fwd (rs := []) hargs hnames hnc hshadow
          (N := []) (by simp) ([] :: funs)
        have hvargs := varArgs_eval (calls := calls) (creates := creates)
          hnd hvals ([] :: funs) V stArgs
        have hcall' := Step.callOk hvargs
          (by simpa [lookupFun] using hlookup) harglen hbody hout
        have hassign := Step.assignVal hcall' hxs
        have hseq := stmts_append_normal hlets
          (Step.seqCons hassign Step.seqNil)
        have hb : Step D funs V st (.stmt (.block
            (stageDecls names args ++
              [.assign xs (.call f (names.map Expr.var))])))
            (.sres (restore V (VEnv.setMany (names.zip argvals ++ V) xs
              (decl.rets.map fun r => (VEnv.get Vend r).getD
                (evmWithExternal calls creates).zero))) st' .normal) := by
          apply Step.block
          simpa [stageDecls, hoist] using hseq
        have hm0 := zip_mins (calls := calls) (creates := creates) V hvals
        have hmins := MIns.setMany
          (decl.rets.map fun r => (VEnv.get Vend r).getD
            (evmWithExternal calls creates).zero) hm0
          (fun p hp => by
            have hpname := tempIns_names hp
            intro hx
            exact hdisj p.2 hx hpname)
        have herase := restore_mins_le (base := V) hmins
          (fun p hp => tempIns_depth hp)
        have hsmall : restore V (VEnv.setMany V xs
            (decl.rets.map fun r => (VEnv.get Vend r).getD
              (evmWithExternal calls creates).zero)) =
            VEnv.setMany V xs (decl.rets.map fun r => (VEnv.get Vend r).getD
              (evmWithExternal calls creates).zero) :=
          restore_exact (W := V) (Y := [])
            (W' := VEnv.setMany V xs
              (decl.rets.map fun r => (VEnv.get Vend r).getD
                (evmWithExternal calls creates).zero))
            (VEnv.setMany_length _ _ _)
        rw [herase, hsmall] at hb
        simpa [stageCore, names] using hb
    | assignHalt hcall =>
      cases hcall with
      | callHalt hargs hlookup harglen hbody =>
        rename_i argvals stArgs decl cenv Vend
        have hvals : argvals.length = names.length :=
          (args_length hargs).trans hnames.symm
        have hlets := argLets_fwd (rs := []) hargs hnames hnc hshadow
          (N := []) (by simp) ([] :: funs)
        have hvargs := varArgs_eval (calls := calls) (creates := creates)
          hnd hvals ([] :: funs) V stArgs
        have hcall' := Step.callHalt hvargs
          (by simpa [lookupFun] using hlookup) harglen hbody
        have hseq := stmts_append_normal hlets
          (Step.seqStop (rest := [])
            (Step.assignHalt (vars := xs) hcall') (by simp))
        have hb : Step D funs V st (.stmt (.block
            (stageDecls names args ++
              [.assign xs (.call f (names.map Expr.var))])))
            (.sres (restore V (names.zip argvals ++ V)) st' .halt) := by
          apply Step.block
          have hhoist : hoist D (stageDecls names args ++
              [.assign xs (.call f (names.map Expr.var))]) = [] := by
            rw [hoist_append, hoist_stageDecls]
            simp [hoist]
          rw [hhoist]
          simpa [stageDecls] using hseq
        have hm0 := zip_mins (calls := calls) (creates := creates) V hvals
        have herase := restore_mins_le (base := V) hm0
          (fun p hp => tempIns_depth hp)
        have hself : restore V V = V := restore_exact (Y := []) rfl
        rw [herase, hself] at hb
        simpa [stageCore, names] using hb
      | callArgsHalt hargs =>
        obtain ⟨Pfx, hlets⟩ := argLets_halt_fwd (rs := []) hargs
          hnames hnc hshadow (N := []) (by simp) ([] :: funs)
        have hseq := stmts_append_early
          (suf := [.assign xs (.call f (names.map Expr.var))]) hlets (by simp)
        have hb : Step D funs V st (.stmt (.block
            (stageDecls names args ++
              [.assign xs (.call f (names.map Expr.var))])))
            (.sres (restore V (Pfx ++ V)) st' .halt) := by
          apply Step.block
          have hhoist : hoist D (stageDecls names args ++
              [.assign xs (.call f (names.map Expr.var))]) = [] := by
            rw [hoist_append, hoist_stageDecls]
            simp [hoist]
          rw [hhoist]
          simpa [stageDecls] using hseq
        have herase : restore V (Pfx ++ V) = V := restore_exact rfl
        rw [herase] at hb
        simpa [stageCore, names] using hb
  · intro h
    change Step D funs V st (.stmt (.block
      (stageDecls names args ++
        [.assign xs (.call f (names.map Expr.var))]))) _ at h
    cases h with
    | block hb =>
      have hhoist : hoist D (stageDecls names args ++
          [.assign xs (.call f (names.map Expr.var))]) = [] := by
        rw [hoist_append, hoist_stageDecls]
        simp [hoist]
      rw [hhoist] at hb
      rcases stmts_append_fwd hb with
        ⟨Vm, stm, hlets, hlast⟩ | ⟨hne, hlets⟩
      · rcases argLets_bwd (rs := []) (funs₁ := funs) (N := []) hlets
          hnames hnc hshadow (by simp) with
          ⟨argvals, hVm, ho, hargs⟩ | ⟨Pfx, hVm, ho, hargs⟩
        · subst Vm
          cases hlast with
          | seqCons hassign hnil =>
            cases hnil
            cases hassign with
            | assignVal hcall hxs =>
              cases hcall with
              | callOk hvargs hlookup harglen hbody hout =>
                rename_i callVals callSt decl cenv Vend bodyOut
                have hinv := varArgs_inv (calls := calls) (creates := creates)
                  hnd (args_length hargs |>.trans hnames.symm) hvargs
                injection hinv with hvals hstate
                subst hvals
                subst hstate
                have hcall0 := Step.callOk hargs
                  (by simpa [lookupFun] using hlookup) harglen hbody hout
                have hout0 := Step.assignVal hcall0 hxs
                let retvals := decl.rets.map fun r =>
                  (VEnv.get Vend r).getD (evmWithExternal calls creates).zero
                have hm0 := zip_mins (calls := calls) (creates := creates) V
                  (args_length hargs |>.trans hnames.symm)
                have hmins := MIns.setMany retvals hm0 (fun p hp => by
                  intro hx
                  exact hdisj p.2 hx (tempIns_names hp))
                have herase := restore_mins_le (base := V) hmins
                  (fun p hp => tempIns_depth hp)
                have hsmall : restore V (VEnv.setMany V xs retvals) =
                    VEnv.setMany V xs retvals :=
                  restore_exact (W := V) (Y := [])
                    (VEnv.setMany_length _ _ _)
                simp only [List.nil_append]
                rw [herase, hsmall]
                exact hout0
          | seqStop hassign hne =>
            cases hassign with
            | assignVal _ _ => exact absurd rfl hne
            | assignHalt hcall =>
              cases hcall with
              | callHalt hvargs hlookup harglen hbody =>
                have hinv := varArgs_inv (calls := calls) (creates := creates)
                  hnd (args_length hargs |>.trans hnames.symm) hvargs
                injection hinv with hvals hstate
                subst hvals
                subst hstate
                have hcall0 := Step.callHalt hargs
                  (by simpa [lookupFun] using hlookup) harglen hbody
                have hm0 := zip_mins (calls := calls) (creates := creates) V
                  (args_length hargs |>.trans hnames.symm)
                have herase := restore_mins_le (base := V) hm0
                  (fun p hp => tempIns_depth hp)
                have hself : restore V V = V := restore_exact (Y := []) rfl
                simp only [List.nil_append]
                rw [herase, hself]
                exact Step.assignHalt hcall0
              | callArgsHalt hvargs =>
                have hinv := varArgs_inv (calls := calls) (creates := creates)
                  hnd (args_length hargs |>.trans hnames.symm) hvargs
                contradiction
        · exact absurd ho (by simp)
      · rcases argLets_bwd (rs := []) (funs₁ := funs) (N := []) hlets
          hnames hnc hshadow (by simp) with
          ⟨argvals, hVm, ho, hargs⟩ | ⟨Pfx, hVm, ho, hargs⟩
        · exact absurd ho hne
        · rw [hVm]
          rw [ho]
          have herase : restore V (Pfx ++ V) = V := restore_exact rfl
          rw [show Pfx ++ ([] ++ V) = Pfx ++ V by simp, herase]
          exact Step.assignHalt (vars := xs)
            (Step.callArgsHalt (fn := f) hargs)

theorem stageWanted_equiv {P : String} {Phi : FMap} {layout xs : List Ident}
    {f : Ident} {args : List (Expr Op)}
    (h : stageWanted Phi layout xs f args (callCarriers P args.length) = true) :
    EquivStmt D (.assign xs (.call f args)) (stageCore P xs f args) := by
  unfold stageWanted at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hprev, hxs⟩ := h
  rw [Bool.and_eq_true] at hprev
  obtain ⟨hprev, hnd⟩ := hprev
  rw [Bool.and_eq_true] at hprev
  obtain ⟨hprev, hshadow⟩ := hprev
  rw [Bool.and_eq_true] at hprev
  obtain ⟨_, hnc⟩ := hprev
  have hnc' : argsHaveCall args = false := by simpa using hnc
  have hshadow' : argsShadowOK []
      ((callCarriers P args.length).zip args) = true := hshadow
  have hnd' : (callCarriers P args.length).Nodup := by simpa using hnd
  have hdisj : ∀ x ∈ xs, x ∉ callCarriers P args.length := by
    intro x hx
    have hx' := List.all_eq_true.mp hxs x hx
    simpa using hx'
  exact stageCore_equiv_of P xs f args hnc' hshadow' hnd' hdisj
/-- `x` is the first `x` binding in `V`, at depth `d` from the bottom. -/
def LocalAt (d : Nat) (x : Ident) (V : VEnv D) : Prop :=
  ∃ above below value,
    V = above ++ (x, value) :: below ∧
    x ∉ above.map Prod.fst ∧ below.length = d

/-- `source` has one additional `y` binding whose value is held in the reused
`x` slot of `target`.  `d` and `dx` pin both slots across declarations and
scope restoration. -/
def SlotRel (d dx : Nat) (x y : Ident) (source target : VEnv D) : Prop :=
  ∃ above tail value,
    source = above ++ (y, value) :: tail ∧
    target = above ++ VEnv.set tail x value ∧
    x ∉ above.map Prod.fst ∧ y ∉ above.map Prod.fst ∧
    tail.length = d ∧ LocalAt dx x tail

namespace LocalAt

theorem get_isSome {d : Nat} {x : Ident} {V : VEnv D} (h : LocalAt d x V) :
    (VEnv.get V x).isSome := by
  obtain ⟨above, below, value, rfl, hx, -⟩ := h
  rw [VEnv.get_append_not_mem hx]
  simp [VEnv.get]

theorem set_ne {d : Nat} {x z : Ident} {V : VEnv D} (h : LocalAt d x V)
    (hz : z ≠ x) (value : U256) : LocalAt d x (VEnv.set V z value) := by
  obtain ⟨above, below, old, rfl, hx, hd⟩ := h
  by_cases hza : z ∈ above.map Prod.fst
  · rw [VEnv.set_append_mem hza]
    refine ⟨VEnv.set above z value, below, old, ?_, ?_, hd⟩
    · rfl
    · rw [VEnv.set_keys]
      exact hx
  · rw [VEnv.set_append_not_mem hza]
    simp only [VEnv.set, if_neg (Ne.symm hz)]
    refine ⟨above, VEnv.set below z value, old, rfl, hx, ?_⟩
    rw [VEnv.set_length, hd]

end LocalAt

theorem VEnv.set_idem (V : VEnv D) (x : Ident) (v w : U256) :
    VEnv.set (VEnv.set V x v) x w = VEnv.set V x w := by
  induction V with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨z, old⟩ := p
      by_cases h : z = x
      · subst z; simp [VEnv.set]
      · simp_all [VEnv.set]

theorem VEnv.set_comm {x y : Ident} (hxy : x ≠ y) (V : VEnv D) (vx vy : U256) :
    VEnv.set (VEnv.set V x vx) y vy = VEnv.set (VEnv.set V y vy) x vx := by
  induction V with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨z, old⟩ := p
      by_cases hzx : z = x
      · subst z; simp [VEnv.set, hxy]
      · by_cases hzy : z = y
        · subst z; simp [VEnv.set, hzx]
        · simp_all [VEnv.set]

namespace SlotRel

theorem length {d dx : Nat} {x y : Ident} {V₁ V₂ : VEnv D}
    (h : SlotRel d dx x y V₁ V₂) : V₁.length = V₂.length + 1 := by
  obtain ⟨above, tail, value, rfl, rfl, -, -, -, -⟩ := h
  rw [List.length_append, List.length_cons, List.length_append, VEnv.set_length]
  omega

theorem get_y {d dx : Nat} {x y : Ident} {V₁ V₂ : VEnv D}
    (h : SlotRel d dx x y V₁ V₂) : VEnv.get V₁ y = VEnv.get V₂ x := by
  obtain ⟨above, tail, value, rfl, rfl, hx, hy, -, hlocal⟩ := h
  rw [VEnv.get_append_not_mem hy, VEnv.get_append_not_mem hx]
  have hleft : VEnv.get ((y, value) :: tail) y = some value := by
    simp [VEnv.get]
  rw [hleft]
  exact (VEnv.get_set_self hlocal.get_isSome).symm

theorem get_other {d dx : Nat} {x y z : Ident} {V₁ V₂ : VEnv D}
    (h : SlotRel d dx x y V₁ V₂) (hzx : z ≠ x) (hzy : z ≠ y) :
    VEnv.get V₁ z = VEnv.get V₂ z := by
  obtain ⟨above, tail, value, rfl, rfl, hx, hy, -, -⟩ := h
  by_cases hza : z ∈ above.map Prod.fst
  · rw [VEnv.get_append_mem hza, VEnv.get_append_mem hza]
  · rw [VEnv.get_append_not_mem hza, VEnv.get_append_not_mem hza]
    rw [VEnv.get_cons]
    simp only [if_neg (Ne.symm hzy)]
    exact (VEnv.get_set_ne hzx).symm

theorem prepend {d dx : Nat} {x y : Ident} {V₁ V₂ : VEnv D}
    (h : SlotRel d dx x y V₁ V₂) (pre : VEnv D)
    (hx : x ∉ pre.map Prod.fst) (hy : y ∉ pre.map Prod.fst) :
    SlotRel d dx x y (pre ++ V₁) (pre ++ V₂) := by
  obtain ⟨above, tail, value, rfl, rfl, hxa, hya, hd, hlocal⟩ := h
  refine ⟨pre ++ above, tail, value, by simp [List.append_assoc],
    by simp [List.append_assoc], ?_, ?_, hd, hlocal⟩
  · simp [hx, hxa]
  · simp [hy, hya]

theorem set {d dx : Nat} {x y z : Ident} {V₁ V₂ : VEnv D}
    (h : SlotRel d dx x y V₁ V₂) (hzx : z ≠ x) (value : U256) :
    SlotRel d dx x y (VEnv.set V₁ z value)
      (VEnv.set V₂ (renameLookup [(y, x)] z) value) := by
  obtain ⟨above, tail, old, rfl, rfl, hxa, hya, hd, hlocal⟩ := h
  by_cases hzy : z = y
  · subst hzy
    have hsrc : VEnv.set (above ++ (z, old) :: tail) z value =
        above ++ (z, value) :: tail := by
      rw [VEnv.set_append_not_mem hya]
      simp [VEnv.set]
    have hren : renameLookup [(z, x)] z = x := by simp [renameLookup]
    have htgt : VEnv.set (above ++ VEnv.set tail x old)
        (renameLookup [(z, x)] z) value = above ++ VEnv.set tail x value := by
      rw [hren, VEnv.set_append_not_mem hxa, VEnv.set_idem]
    rw [hsrc, htgt]
    exact ⟨above, tail, value, rfl, rfl, hxa, hya, hd, hlocal⟩
  · have hrename : renameLookup [(y, x)] z = z := by
      have hyz : y ≠ z := Ne.symm hzy
      simp [renameLookup, hyz]
    rw [hrename]
    by_cases hza : z ∈ above.map Prod.fst
    · rw [VEnv.set_append_mem hza, VEnv.set_append_mem hza]
      refine ⟨VEnv.set above z value, tail, old, ?_, ?_, ?_, ?_, hd, hlocal⟩
      · rfl
      · rfl
      · rw [VEnv.set_keys]
        exact hxa
      · rw [VEnv.set_keys]
        exact hya
    · rw [VEnv.set_append_not_mem hza, VEnv.set_append_not_mem hza]
      simp only [VEnv.set, if_neg (Ne.symm hzy)]
      have hcomm := VEnv.set_comm hzx tail value old
      rw [← hcomm]
      refine ⟨above, VEnv.set tail z value, old, rfl, rfl, hxa, hya, ?_, ?_⟩
      · rw [VEnv.set_length, hd]
      · exact hlocal.set_ne hzx value

theorem setMany {d dx : Nat} {x y : Ident} {V₁ V₂ : VEnv D}
    (h : SlotRel d dx x y V₁ V₂) :
    ∀ {vars : List Ident}, x ∉ vars → ∀ (values : List U256),
      SlotRel d dx x y (VEnv.setMany V₁ vars values)
        (VEnv.setMany V₂ (vars.map (renameLookup [(y, x)])) values) := by
  intro vars hx
  induction vars generalizing V₁ V₂ with
  | nil => intro values; cases values <;> simpa [VEnv.setMany] using h
  | cons z rest ih =>
      intro values
      simp only [List.mem_cons, not_or] at hx
      cases values with
      | nil => simpa [VEnv.setMany] using h
      | cons value values =>
          simp only [VEnv.setMany, List.zip_cons_cons, List.foldl_cons, List.map_cons]
          exact ih (h.set (Ne.symm hx.1) value) hx.2 values

/-- The assignment lemma in the reverse simulation direction. -/
theorem setRev {d dx : Nat} {x y z : Ident} {V₁ V₂ : VEnv D}
    (h : SlotRel d dx x y V₁ V₂) (hxy : x ≠ y) (hzy : z ≠ y)
    (value : U256) :
    SlotRel d dx x y
      (VEnv.set V₁ (renameLookup [(x, y)] z) value) (VEnv.set V₂ z value) := by
  by_cases hzx : z = x
  · subst z
    have h₁ : renameLookup [(x, y)] x = y := by simp [renameLookup]
    have h₂ : renameLookup [(y, x)] y = x := by simp [renameLookup]
    rw [h₁]
    have hs := h.set (Ne.symm hxy) value
    rw [h₂] at hs
    exact hs
  · have h₁ : renameLookup [(x, y)] z = z := by
      simp [renameLookup, Ne.symm hzx]
    have h₂ : renameLookup [(y, x)] z = z := by
      simp [renameLookup, Ne.symm hzy]
    rw [h₁]
    have hs := h.set hzx value
    rw [h₂] at hs
    exact hs

theorem setManyRev {d dx : Nat} {x y : Ident} {V₁ V₂ : VEnv D}
    (h : SlotRel d dx x y V₁ V₂) (hxy : x ≠ y) :
    ∀ {vars : List Ident}, y ∉ vars → ∀ (values : List U256),
      SlotRel d dx x y
        (VEnv.setMany V₁ (vars.map (renameLookup [(x, y)])) values)
        (VEnv.setMany V₂ vars values) := by
  intro vars hy
  induction vars generalizing V₁ V₂ with
  | nil => intro values; cases values <;> simpa [VEnv.setMany] using h
  | cons z rest ih =>
      intro values
      simp only [List.mem_cons, not_or] at hy
      cases values with
      | nil => simpa [VEnv.setMany] using h
      | cons value values =>
          simp only [VEnv.setMany, List.zip_cons_cons, List.foldl_cons, List.map_cons]
          exact ih (h.setRev hxy (Ne.symm hy.1) value) hy.2 values

theorem prependZeros {d dx : Nat} {x y : Ident} {V₁ V₂ : VEnv D}
    (h : SlotRel d dx x y V₁ V₂) {vars : List Ident}
    (hx : x ∉ vars) (hy : y ∉ vars) :
    SlotRel d dx x y (bindZeros D vars ++ V₁) (bindZeros D vars ++ V₂) := by
  apply h.prepend
  · simpa [bindZeros] using hx
  · simpa [bindZeros] using hy

theorem prependZip {d dx : Nat} {x y : Ident} {V₁ V₂ : VEnv D}
    (h : SlotRel d dx x y V₁ V₂) {vars : List Ident} {values : List U256}
    (hx : x ∉ vars) (hy : y ∉ vars) :
    SlotRel d dx x y ((vars.zip values : VEnv D) ++ V₁)
      ((vars.zip values : VEnv D) ++ V₂) := by
  apply h.prepend
  · intro hm
    obtain ⟨p, hp, hpx⟩ := List.mem_map.mp hm
    exact hx (hpx ▸ (List.of_mem_zip hp).1)
  · intro hm
    obtain ⟨p, hp, hpy⟩ := List.mem_map.mp hm
    exact hy (hpy ▸ (List.of_mem_zip hp).1)

/-- Restore to a common suffix length ignores arbitrary prefixes. -/
private theorem restore_prefixes {base left right suffix : VEnv D}
    (hbase : base.length ≤ suffix.length) :
    restore base (left ++ suffix) = restore base (right ++ suffix) := by
  have hleft : (left ++ suffix).length - base.length =
      left.length + (suffix.length - base.length) := by simp only [List.length_append]; omega
  have hright : (right ++ suffix).length - base.length =
      right.length + (suffix.length - base.length) := by simp only [List.length_append]; omega
  simp only [restore, hleft, hright]
  rw [List.drop_append, List.drop_eq_nil_of_le (Nat.le_add_right _ _), List.nil_append,
    List.drop_append, List.drop_eq_nil_of_le (Nat.le_add_right _ _), List.nil_append]
  congr 1
  omega

/-- Once the common outer frame lies below the reused `x` slot, block exit
erases both the removed `y` binding and the overwrite of `x`. -/
theorem restore_eq {d dx : Nat} {x y : Ident} {V₁ V₂ base : VEnv D}
    (h : SlotRel d dx x y V₁ V₂) (hbase : base.length ≤ dx) :
    restore base V₁ = restore base V₂ := by
  obtain ⟨above, tail, value, rfl, rfl, -, -, -, hlocal⟩ := h
  obtain ⟨middle, below, old, rfl, hxmiddle, hdx⟩ := hlocal
  have hset : VEnv.set (middle ++ (x, old) :: below) x value =
      middle ++ (x, value) :: below := by
    rw [VEnv.set_append_not_mem hxmiddle]
    simp [VEnv.set]
  rw [hset]
  have heq := restore_prefixes (calls := calls) (creates := creates)
    (base := base)
    (left := above ++ [(y, value)] ++ middle ++ [(x, old)])
    (right := above ++ middle ++ [(x, value)])
    (suffix := below) (by omega)
  simpa [List.append_assoc] using heq

/-- Restoring a nested block preserves the slot relation. -/
theorem restore_nested {d dx : Nat} {x y : Ident} {Ve₁ Ve₂ Vb₁ Vb₂ : VEnv D}
    (hentry : SlotRel d dx x y Ve₁ Ve₂)
    (hbody : SlotRel d dx x y Vb₁ Vb₂)
    (hlen : Ve₁.length ≤ Vb₁.length) :
    SlotRel d dx x y (restore Ve₁ Vb₁) (restore Ve₂ Vb₂) := by
  obtain ⟨entryAbove, entryTail, entryValue, he₁, he₂, -, -, hed, -⟩ := hentry
  obtain ⟨bodyAbove, bodyTail, bodyValue, hb₁, hb₂, hbx, hby, hbd, hlocal⟩ := hbody
  have hab : entryAbove.length ≤ bodyAbove.length := by
    rw [he₁, hb₁] at hlen
    simp only [List.length_append, List.length_cons, hed, hbd] at hlen
    omega
  have hk₁ : Vb₁.length - Ve₁.length = bodyAbove.length - entryAbove.length := by
    rw [he₁, hb₁]
    simp only [List.length_append, List.length_cons, hed, hbd]
    omega
  have hk₂ : Vb₂.length - Ve₂.length = bodyAbove.length - entryAbove.length := by
    rw [he₂, hb₂, List.length_append, List.length_append,
      VEnv.set_length, VEnv.set_length, hed, hbd]
    omega
  unfold YulSemantics.restore
  rw [hk₁, hk₂, hb₁, hb₂,
    List.drop_append_of_le_length (Nat.sub_le _ _),
    List.drop_append_of_le_length (Nat.sub_le _ _)]
  refine ⟨bodyAbove.drop (bodyAbove.length - entryAbove.length), bodyTail,
    bodyValue, rfl, rfl, ?_, ?_, hbd, hlocal⟩
  · simpa [List.map_drop] using fun hm => hbx (List.mem_of_mem_drop hm)
  · simpa [List.map_drop] using fun hm => hby (List.mem_of_mem_drop hm)

end SlotRel

/-! ## Renamed code and its syntactic side conditions -/

def renameCode (r : Rename) : Code Op → Code Op
  | .expr e => .expr (renameExpr r e)
  | .args es => .args (renameArgs r es)
  | .stmt s => .stmt (renameStmt r s)
  | .stmts ss => .stmts (renameStmts r ss)
  | .loop c post body =>
      .loop (renameExpr r c) (renameStmts r post) (renameStmts r body)

def codeDeclares (x : Ident) : Code Op → Bool
  | .expr _ | .args _ => false
  | .stmt s => stmtDeclares x s
  | .stmts ss => stmtsDeclare x ss
  | .loop _ post body => stmtsDeclare x post || stmtsDeclare x body

@[simp] theorem renameLookup_self (x y : Ident) :
    renameLookup [(y, x)] y = x := by simp [renameLookup]

@[simp] theorem renameLookup_ne {x y z : Ident} (h : z ≠ y) :
    renameLookup [(y, x)] z = z := by
  have hyz : y ≠ z := Ne.symm h
  simp [renameLookup, hyz]

theorem hoist_renameStmts (r : Rename) (body : Block Op) :
    hoist D (renameStmts r body) = hoist D body := by
  induction body with
  | nil => simp [renameStmts, hoist]
  | cons s rest ih =>
      unfold hoist at ih ⊢
      cases s <;> simp [renameStmts, renameStmt, ih]
      case «switch» dflt => cases dflt <;> simp [renameStmt, ih]

/-! Renaming a fresh name into a dead name is syntactically invertible. -/

theorem renameLookup_inverse {x y z : Ident} (hzx : z ≠ x) :
    renameLookup [(x, y)] (renameLookup [(y, x)] z) = z := by
  by_cases hzy : z = y
  · subst z
    simp [renameLookup]
  · have hyz : y ≠ z := Ne.symm hzy
    have hxz : x ≠ z := Ne.symm hzx
    simp [renameLookup, hyz, hxz]

mutual
  theorem renameExpr_inverse {x y : Ident} (hxy : x ≠ y) :
      ∀ {e : Expr Op}, exprMentions x e = false →
        renameExpr [(x, y)] (renameExpr [(y, x)] e) = e
    | .lit _, _ => rfl
    | .var z, hm => by
        simp only [exprMentions, decide_eq_false_iff_not] at hm
        simpa [renameExpr] using renameLookup_inverse (y := y) (Ne.symm hm)
    | .builtin op args, hm => by
        simp only [exprMentions] at hm
        simp [renameExpr, renameArgs_inverse hxy hm]
    | .call f args, hm => by
        simp only [exprMentions] at hm
        simp [renameExpr, renameArgs_inverse hxy hm]

  theorem renameArgs_inverse {x y : Ident} (hxy : x ≠ y) :
      ∀ {args : List (Expr Op)}, argsMentions x args = false →
        renameArgs [(x, y)] (renameArgs [(y, x)] args) = args
    | [], _ => rfl
    | e :: rest, hm => by
        simp only [argsMentions, Bool.or_eq_false_iff] at hm
        simp [renameArgs, renameExpr_inverse hxy hm.1,
          renameArgs_inverse hxy hm.2]
end

theorem SlotRel.initial {dx : Nat} {x y : Ident} {V : VEnv D} {value : U256}
    (hlocal : LocalAt dx x V) :
    SlotRel V.length dx x y ((y, value) :: V) (VEnv.set V x value) :=
  ⟨[], V, value, rfl, rfl, by simp, by simp, rfl, hlocal⟩

mutual
  theorem renameStmt_inverse {x y : Ident} (hxy : x ≠ y) :
      ∀ {s : Stmt Op}, stmtMentions x s = false →
        renameStmt [(x, y)] (renameStmt [(y, x)] s) = s
    | .block body, hm => by
        simp only [stmtMentions] at hm
        simp [renameStmt, renameStmts_inverse hxy hm]
    | .funDef f ps rs body, _ => by simp [renameStmt]
    | .letDecl vars val, hm => by
        simp only [stmtMentions, Bool.or_eq_false_iff] at hm
        cases val with
        | none => simp [renameStmt]
        | some e =>
            simp only [optExprMentions] at hm
            simp [renameStmt, renameExpr_inverse hxy hm.2]
    | .assign vars e, hm => by
        simp only [stmtMentions, Bool.or_eq_false_iff] at hm
        have hvars : (vars.map (renameLookup [(y, x)])).map
            (renameLookup [(x, y)]) = vars := by
          rw [List.map_map]
          calc
            List.map (renameLookup [(x, y)] ∘ renameLookup [(y, x)]) vars =
                List.map id vars := List.map_congr_left (fun z hz => by
              have hzx : z ≠ x := by
                intro h; subst z
                have hxnot : x ∉ vars := by simpa using hm.1
                exact hxnot hz
              exact renameLookup_inverse (y := y) hzx)
            _ = vars := by simp
        simp [renameStmt, hvars, renameExpr_inverse hxy hm.2]
    | .cond c body, hm => by
        simp only [stmtMentions, Bool.or_eq_false_iff] at hm
        simp [renameStmt, renameExpr_inverse hxy hm.1,
          renameStmts_inverse hxy hm.2]
    | .switch c cases dflt, hm => by
        simp only [stmtMentions, Bool.or_eq_false_iff] at hm
        rcases hm with ⟨⟨hc, hcases⟩, hdflt⟩
        cases dflt with
        | none =>
            simp [renameStmt, renameExpr_inverse hxy hc,
              renameCases_inverse hxy hcases]
        | some body =>
            simp only [optBlockMentions] at hdflt
            simp [renameStmt, renameExpr_inverse hxy hc,
              renameCases_inverse hxy hcases, renameStmts_inverse hxy hdflt]
    | .forLoop init c post body, hm => by
        simp only [stmtMentions, Bool.or_eq_false_iff] at hm
        rcases hm with ⟨⟨⟨hi, hc⟩, hp⟩, hb⟩
        simp [renameStmt, renameStmts_inverse hxy hi,
          renameExpr_inverse hxy hc, renameStmts_inverse hxy hp,
          renameStmts_inverse hxy hb]
    | .exprStmt e, hm => by
        simp only [stmtMentions] at hm
        simp [renameStmt, renameExpr_inverse hxy hm]
    | .break, _ => by simp [renameStmt]
    | .continue, _ => by simp [renameStmt]
    | .leave, _ => by simp [renameStmt]

  theorem renameStmts_inverse {x y : Ident} (hxy : x ≠ y) :
      ∀ {ss : Block Op}, stmtsMentions x ss = false →
        renameStmts [(x, y)] (renameStmts [(y, x)] ss) = ss
    | [], _ => by simp [renameStmts]
    | s :: rest, hm => by
        simp only [stmtsMentions, Bool.or_eq_false_iff] at hm
        simp [renameStmts, renameStmt_inverse hxy hm.1,
          renameStmts_inverse hxy hm.2]

  theorem renameCases_inverse {x y : Ident} (hxy : x ≠ y) :
      ∀ {cases : List (Literal × Block Op)}, casesMentions x cases = false →
        renameCases [(x, y)] (renameCases [(y, x)] cases) = cases
    | [], _ => by simp [renameCases]
    | (l, body) :: rest, hm => by
        simp only [casesMentions, Bool.or_eq_false_iff] at hm
        simp [renameCases, renameStmts_inverse hxy hm.1,
          renameCases_inverse hxy hm.2]
end

/-! The coalesced program has no residual occurrence of the removed name and
does not introduce declarations of the reused name. -/

mutual
  theorem renameExpr_no_target {x y : Ident} (hxy : x ≠ y) :
      ∀ {e : Expr Op}, exprMentions x e = false →
        exprMentions y (renameExpr [(y, x)] e) = false
    | .lit _, _ => rfl
    | .var z, hm => by
        simp only [exprMentions, decide_eq_false_iff_not] at hm
        by_cases hzy : z = y
        · subst z; simp [renameExpr, renameLookup, exprMentions, Ne.symm hxy]
        · have hyz : y ≠ z := Ne.symm hzy
          simp [renameExpr, renameLookup, exprMentions, hyz]
    | .builtin op args, hm => by
        simpa [renameExpr, exprMentions] using renameArgs_no_target hxy hm
    | .call f args, hm => by
        simpa [renameExpr, exprMentions] using renameArgs_no_target hxy hm

  theorem renameArgs_no_target {x y : Ident} (hxy : x ≠ y) :
      ∀ {args : List (Expr Op)}, argsMentions x args = false →
        argsMentions y (renameArgs [(y, x)] args) = false
    | [], _ => rfl
    | e :: rest, hm => by
        simp only [argsMentions, Bool.or_eq_false_iff] at hm
        simp only [renameArgs, argsMentions, Bool.or_eq_false_iff]
        exact ⟨renameExpr_no_target hxy hm.1, renameArgs_no_target hxy hm.2⟩
end

theorem renameLookup_not_target {x y z : Ident} (hxy : x ≠ y) (hzx : z ≠ x) :
    renameLookup [(y, x)] z ≠ y := by
  by_cases hzy : z = y
  · subst z
    simpa [renameLookup] using hxy
  · simp [renameLookup, Ne.symm hzy, hzy]

theorem renameList_no_target {x y : Ident} (hxy : x ≠ y) {vars : List Ident}
    (hx : x ∉ vars) : y ∉ vars.map (renameLookup [(y, x)]) := by
  intro hm
  obtain ⟨z, hz, heq⟩ := List.mem_map.mp hm
  exact renameLookup_not_target hxy (fun h => hx (h ▸ hz)) heq

mutual
  theorem renameStmt_no_target {x y : Ident} (hxy : x ≠ y) :
      ∀ {s : Stmt Op}, stmtMentions x s = false →
        stmtDeclares y s = false → stmtFunMentions y s = false →
        stmtMentions y (renameStmt [(y, x)] s) = false
    | .block body, hmx, hdy, hfy => by
        simpa [renameStmt, stmtMentions, stmtDeclares, stmtFunMentions] using
          renameStmts_no_target hxy hmx hdy hfy
    | s@(.funDef f ps rs body), hmx, hdy, hfy => by
        simpa [renameStmt, stmtFunMentions] using hfy
    | .letDecl vars val, hmx, hdy, hfy => by
        simp only [stmtMentions, Bool.or_eq_false_iff] at hmx
        simp only [stmtDeclares] at hdy
        cases val with
        | none =>
            simp only [renameStmt, stmtMentions, optExprMentions,
              Bool.or_eq_false_iff]
            exact ⟨by simpa using hdy, rfl⟩
        | some e =>
            simp only [optExprMentions] at hmx
            simp only [renameStmt, stmtMentions, optExprMentions,
              Bool.or_eq_false_iff]
            exact ⟨by simpa using hdy, renameExpr_no_target hxy hmx.2⟩
    | .assign vars e, hmx, hdy, hfy => by
        simp only [stmtMentions, Bool.or_eq_false_iff] at hmx
        have hx : x ∉ vars := by simpa using hmx.1
        have hv := renameList_no_target hxy hx
        simp [renameStmt, stmtMentions, hv, renameExpr_no_target hxy hmx.2]
    | .cond c body, hmx, hdy, hfy => by
        simp only [stmtMentions, Bool.or_eq_false_iff] at hmx
        simp [renameStmt, stmtMentions, renameExpr_no_target hxy hmx.1,
          renameStmts_no_target hxy hmx.2 hdy hfy]
    | .switch c cases dflt, hmx, hdy, hfy => by
        simp only [stmtMentions, Bool.or_eq_false_iff] at hmx
        simp only [stmtDeclares, stmtFunMentions, Bool.or_eq_false_iff] at hdy hfy
        rcases hmx with ⟨⟨hc, hmcs⟩, hmd⟩
        cases dflt with
        | none =>
            simp only [renameStmt, stmtMentions, Bool.or_eq_false_iff]
            exact ⟨⟨renameExpr_no_target hxy hc,
              renameCases_no_target hxy hmcs hdy.1 hfy.1⟩, rfl⟩
        | some body =>
            simp only [optBlockMentions, optBlockDeclares, optBlockFunMentions] at hmd hdy hfy
            simp only [renameStmt, stmtMentions, Bool.or_eq_false_iff,
              optBlockMentions]
            exact ⟨⟨renameExpr_no_target hxy hc,
              renameCases_no_target hxy hmcs hdy.1 hfy.1⟩,
              renameStmts_no_target hxy hmd hdy.2 hfy.2⟩
    | .forLoop init c post body, hmx, hdy, hfy => by
        simp only [stmtMentions, stmtDeclares, stmtFunMentions,
          Bool.or_eq_false_iff] at hmx hdy hfy
        rcases hmx with ⟨⟨⟨hmi, hmc⟩, hmp⟩, hmb⟩
        rcases hdy with ⟨⟨hdi, hdp⟩, hdb⟩
        rcases hfy with ⟨⟨hfi, hfp⟩, hfb⟩
        simp [renameStmt, stmtMentions,
          renameStmts_no_target hxy hmi hdi hfi,
          renameExpr_no_target hxy hmc,
          renameStmts_no_target hxy hmp hdp hfp,
          renameStmts_no_target hxy hmb hdb hfb]
    | .exprStmt e, hmx, hdy, hfy => by
        simpa [renameStmt, stmtMentions] using renameExpr_no_target hxy hmx
    | .break, _, _, _ => by simp [renameStmt, stmtMentions]
    | .continue, _, _, _ => by simp [renameStmt, stmtMentions]
    | .leave, _, _, _ => by simp [renameStmt, stmtMentions]

  theorem renameStmts_no_target {x y : Ident} (hxy : x ≠ y) :
      ∀ {ss : Block Op}, stmtsMentions x ss = false →
        stmtsDeclare y ss = false → stmtsFunMention y ss = false →
        stmtsMentions y (renameStmts [(y, x)] ss) = false
    | [], _, _, _ => by simp [renameStmts, stmtsMentions]
    | s :: rest, hmx, hdy, hfy => by
        simp only [stmtsMentions, stmtsDeclare, stmtsFunMention,
          Bool.or_eq_false_iff] at hmx hdy hfy
        simp only [renameStmts, stmtsMentions, Bool.or_eq_false_iff]
        exact ⟨renameStmt_no_target hxy hmx.1 hdy.1 hfy.1,
          renameStmts_no_target hxy hmx.2 hdy.2 hfy.2⟩

  theorem renameCases_no_target {x y : Ident} (hxy : x ≠ y) :
      ∀ {cases : List (Literal × Block Op)}, casesMentions x cases = false →
        casesDeclare y cases = false → casesFunMention y cases = false →
        casesMentions y (renameCases [(y, x)] cases) = false
    | [], _, _, _ => by simp [renameCases, casesMentions]
    | (l, body) :: rest, hmx, hdy, hfy => by
        simp only [casesMentions, casesDeclare, casesFunMention,
          Bool.or_eq_false_iff] at hmx hdy hfy
        simp only [renameCases, casesMentions, Bool.or_eq_false_iff]
        exact ⟨renameStmts_no_target hxy hmx.1 hdy.1 hfy.1,
          renameCases_no_target hxy hmx.2 hdy.2 hfy.2⟩
end

mutual
  theorem stmtDeclares_rename (r : Rename) (x : Ident) :
      ∀ s : Stmt Op, stmtDeclares x (renameStmt r s) = stmtDeclares x s
    | .block body => by simp [renameStmt, stmtDeclares, stmtsDeclare_rename]
    | .funDef _ _ _ _ => by simp [renameStmt, stmtDeclares]
    | .letDecl _ _ => by simp [renameStmt, stmtDeclares]
    | .assign _ _ => by simp [renameStmt, stmtDeclares]
    | .cond _ body => by simp [renameStmt, stmtDeclares, stmtsDeclare_rename]
    | .switch _ cases dflt => by
        cases dflt <;> simp [renameStmt, stmtDeclares, casesDeclare_rename,
          optBlockDeclares, stmtsDeclare_rename]
    | .forLoop init _ post body => by
        simp [renameStmt, stmtDeclares, stmtsDeclare_rename]
    | .exprStmt _ => by simp [renameStmt, stmtDeclares]
    | .break => by simp [renameStmt, stmtDeclares]
    | .continue => by simp [renameStmt, stmtDeclares]
    | .leave => by simp [renameStmt, stmtDeclares]

  theorem stmtsDeclare_rename (r : Rename) (x : Ident) :
      ∀ ss : Block Op, stmtsDeclare x (renameStmts r ss) = stmtsDeclare x ss
    | [] => by simp [renameStmts, stmtsDeclare]
    | s :: rest => by
        simp [renameStmts, stmtsDeclare, stmtDeclares_rename, stmtsDeclare_rename]

  theorem casesDeclare_rename (r : Rename) (x : Ident) :
      ∀ cases : List (Literal × Block Op),
        casesDeclare x (renameCases r cases) = casesDeclare x cases
    | [] => by simp [renameCases, casesDeclare]
    | (_, body) :: rest => by
        simp [renameCases, casesDeclare, stmtsDeclare_rename, casesDeclare_rename]
end

/-! ## Top-level bindings and the runtime ownership invariant -/

def stmtBinds : Stmt Op → List Ident
  | .letDecl vars _ => vars
  | _ => []

/-- Bindings introduced by a sequence, in final environment order. -/
def stmtsBinds : Block Op → List Ident
  | [] => []
  | s :: rest => stmtsBinds rest ++ stmtBinds s

/-- A normally completing statement changes its key stack only by its own
top-level `let` bindings. Nested blocks restore their entry layout. -/
theorem stmt_normal_keys {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    {s : Stmt Op} {V' : VEnv D} {st' : EvmState}
    (h : Step D funs V st (.stmt s) (.sres V' st' .normal)) :
    V'.map Prod.fst = stmtBinds s ++ V.map Prod.fst := by
  cases h with
  | funDef => rfl
  | block hb =>
      simpa [stmtBinds] using (block_stmt_shape (Step.block hb)).1
  | @letZero _ _ _ vars =>
      simpa [stmtBinds] using
        (bindZeros_keys (calls := calls) (creates := creates) vars)
  | letVal hexpr hlen =>
      simp only [stmtBinds, List.map_append]
      rw [zip_keys hlen.symm.le]
  | assignVal _ _ =>
      simp only [stmtBinds, List.nil_append]
      exact @VEnv.setMany_keys (evmWithExternal calls creates) inferInstance _ _ _
  | exprStmt _ => rfl
  | ifTrue _ _ hbody =>
      simpa [stmtBinds] using (block_stmt_shape hbody).1
  | ifFalse _ _ => rfl
  | switchExec _ hbody =>
      simpa [stmtBinds] using (block_stmt_shape hbody).1
  | forLoop hinit hloop =>
      simp only [stmtBinds]
      exact restore_keys ((venvKeys_suffix hinit rfl).trans (venvKeys_suffix hloop rfl))
        (Nat.le_trans (venvLen_mono hinit rfl) (venvLen_mono hloop rfl))

/-- Exact key layout after normal completion of a statement sequence. -/
theorem stmts_normal_keys {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    {ss : Block Op} {V' : VEnv D} {st' : EvmState}
    (h : Step D funs V st (.stmts ss) (.sres V' st' .normal)) :
    V'.map Prod.fst = stmtsBinds ss ++ V.map Prod.fst := by
  induction ss generalizing V st with
  | nil => cases h; rfl
  | cons s rest ih =>
      cases h with
      | seqCons hs hr =>
          simp only [stmtsBinds]
          rw [ih hr, stmt_normal_keys hs, List.append_assoc]
      | seqStop hs hne => exact absurd rfl hne

/-- A name in the first `n` environment keys has a first binding whose
bottom-depth is at least the suffix below that prefix. -/
theorem localAt_of_mem_take {V : VEnv D} {n : Nat} {x : Ident}
    (hm : x ∈ (V.take n).map Prod.fst) :
    ∃ d, LocalAt d x V ∧ V.length - n ≤ d := by
  induction V generalizing n with
  | nil => simp at hm
  | cons p rest ih =>
      obtain ⟨z, value⟩ := p
      cases n with
      | zero => simp at hm
      | succ n =>
          simp only [List.take_succ_cons, List.map_cons, List.mem_cons] at hm
          by_cases hzx : z = x
          · subst z
            refine ⟨rest.length, ⟨[], rest, value, rfl, by simp, rfl⟩, ?_⟩
            simp only [List.length_cons]
            omega
          · have hxm : x ∈ (rest.take n).map Prod.fst := hm.resolve_left (Ne.symm hzx)
            obtain ⟨d, ⟨above, below, old, hrest, hxa, hd⟩, hbound⟩ := ih hxm
            refine ⟨d, ⟨(z, value) :: above, below, old, ?_, ?_, hd⟩, ?_⟩
            · simp [hrest]
            · simp [Ne.symm hzx, hxa]
            · simpa using hbound

/-- Every syntactically introduced top-level local is represented by a stack
slot above the sequence's entry frame after normal execution. -/
theorem localAt_of_stmtsBind {funs : FunEnv D} {base V' : VEnv D}
    {st st' : EvmState} {ss : Block Op} {x : Ident}
    (hstep : Step D funs base st (.stmts ss) (.sres V' st' .normal))
    (hx : x ∈ stmtsBinds ss) :
    ∃ dx, LocalAt dx x V' ∧ base.length ≤ dx := by
  have hkeys := stmts_normal_keys hstep
  have htake : (V'.take (stmtsBinds ss).length).map Prod.fst = stmtsBinds ss := by
    rw [List.map_take, hkeys]
    simp
  have hm : x ∈ (V'.take (stmtsBinds ss).length).map Prod.fst := by
    rw [htake]
    exact hx
  obtain ⟨dx, hlocal, hbound⟩ := localAt_of_mem_take hm
  refine ⟨dx, hlocal, ?_⟩
  have hlen := congrArg List.length hkeys
  simp only [List.length_map, List.length_append] at hlen
  omega

mutual
  theorem stmtDeclares_false_of_mentions (x : Ident) : ∀ s : Stmt Op,
      stmtMentions x s = false → stmtDeclares x s = false
    | .block body, h => stmtsDeclare_false_of_mentions x body h
    | .funDef _ _ _ _, _ => rfl
    | .letDecl vars val, h => by
        simp only [stmtMentions, Bool.or_eq_false_iff] at h
        simpa [stmtDeclares] using h.1
    | .assign _ _, _ => rfl
    | .cond c body, h => by
        simp only [stmtMentions, Bool.or_eq_false_iff] at h
        exact stmtsDeclare_false_of_mentions x body h.2
    | .switch c cases dflt, h => by
        simp only [stmtMentions, Bool.or_eq_false_iff] at h
        simp only [stmtDeclares, Bool.or_eq_false_iff]
        exact ⟨casesDeclare_false_of_mentions x cases h.1.2,
          optDeclares_false_of_mentions x dflt h.2⟩
    | .forLoop init c post body, h => by
        simp only [stmtMentions, Bool.or_eq_false_iff] at h
        simp only [stmtDeclares, Bool.or_eq_false_iff]
        exact ⟨⟨stmtsDeclare_false_of_mentions x init h.1.1.1,
          stmtsDeclare_false_of_mentions x post h.1.2⟩,
          stmtsDeclare_false_of_mentions x body h.2⟩
    | .exprStmt _, _ => rfl
    | .break, _ => rfl
    | .continue, _ => rfl
    | .leave, _ => rfl

  theorem stmtsDeclare_false_of_mentions (x : Ident) : ∀ ss : Block Op,
      stmtsMentions x ss = false → stmtsDeclare x ss = false
    | [], _ => rfl
    | s :: rest, h => by
        simp only [stmtsMentions, Bool.or_eq_false_iff] at h
        simp only [stmtsDeclare, Bool.or_eq_false_iff]
        exact ⟨stmtDeclares_false_of_mentions x s h.1,
          stmtsDeclare_false_of_mentions x rest h.2⟩

  theorem casesDeclare_false_of_mentions (x : Ident) :
      ∀ cases : List (Literal × Block Op), casesMentions x cases = false →
        casesDeclare x cases = false
    | [], _ => rfl
    | (_, body) :: rest, h => by
        simp only [casesMentions, Bool.or_eq_false_iff] at h
        simp only [casesDeclare, Bool.or_eq_false_iff]
        exact ⟨stmtsDeclare_false_of_mentions x body h.1,
          casesDeclare_false_of_mentions x rest h.2⟩

  theorem optDeclares_false_of_mentions (x : Ident) :
      ∀ dflt : Option (Block Op), optBlockMentions x dflt = false →
        optBlockDeclares x dflt = false
    | none, _ => rfl
    | some body, h => stmtsDeclare_false_of_mentions x body h
end

private theorem find?_renameCases (r : Rename) (value : U256) :
    ∀ cases : List (Literal × Block Op),
      (renameCases r cases).find? (fun p => decide (value = litValue p.1)) =
        (cases.find? (fun p => decide (value = litValue p.1))).map
          (fun p => (p.1, renameStmts r p.2))
  | [] => by simp [renameCases]
  | (lit, body) :: rest => by
      simp only [renameCases, List.find?_cons]
      by_cases h : value = litValue lit
      · simp [h]
      · simp [h, find?_renameCases r value rest]

theorem selectSwitch_rename (r : Rename) (value : U256)
    (cases : List (Literal × Block Op)) (dflt : Option (Block Op)) :
    selectSwitch D value (renameCases r cases) (dflt.map (renameStmts r)) =
      renameStmts r (selectSwitch D value cases dflt) := by
  unfold selectSwitch
  rw [find?_renameCases]
  cases h : cases.find? (fun p => decide (value = litValue p.1)) with
  | none => cases dflt <;> simp [renameStmts]
  | some p => simp

theorem casesDeclare_of_mem {y : Ident} :
    ∀ {cases : List (Literal × Block Op)}, casesDeclare y cases = false →
      ∀ {p}, p ∈ cases → stmtsDeclare y p.2 = false := by
  intro cases
  induction cases with
  | nil => intro _ p hp; simp at hp
  | cons q rest ih =>
      obtain ⟨lit, body⟩ := q
      intro h p hp
      simp only [casesDeclare, Bool.or_eq_false_iff] at h
      rcases List.mem_cons.mp hp with rfl | hp
      · exact h.1
      · exact ih h.2 hp

theorem selectSwitch_not_declares {y : Ident} {value : U256}
    {cases : List (Literal × Block Op)} {dflt : Option (Block Op)}
    (hc : casesDeclare y cases = false)
    (hd : optBlockDeclares y dflt = false) :
    stmtsDeclare y (selectSwitch D value cases dflt) = false := by
  unfold selectSwitch
  cases hfind : cases.find? (fun p => decide (value = litValue p.1)) with
  | some p => exact casesDeclare_of_mem hc (List.mem_of_find?_eq_some hfind)
  | none => cases dflt <;> simp_all [optBlockDeclares, stmtsDeclare]

/-! ## Result relation and semantic simulation -/

def SlotResRel (d dx : Nat) (x y : Ident) : Res D → Res D → Prop
  | .eres r₁, .eres r₂ => r₁ = r₂
  | .sres V₁ st₁ o₁, .sres V₂ st₂ o₂ =>
      SlotRel d dx x y V₁ V₂ ∧ st₁ = st₂ ∧ o₁ = o₂
  | _, _ => False

theorem SlotResRel.eres {d dx : Nat} {x y : Ident} {r : EResult D} {res₂ : Res D}
    (h : SlotResRel d dx x y (.eres r) res₂) : res₂ = .eres r := by
  cases res₂ with
  | eres r₂ => simp only [SlotResRel] at h; rw [h]
  | sres => simp only [SlotResRel] at h

theorem SlotResRel.sres {d dx : Nat} {x y : Ident}
    {V₁ : VEnv D} {st : EvmState} {o : Outcome} {res₂ : Res D}
    (h : SlotResRel d dx x y (.sres V₁ st o) res₂) :
    ∃ V₂, res₂ = .sres V₂ st o ∧ SlotRel d dx x y V₁ V₂ := by
  cases res₂ with
  | eres => simp only [SlotResRel] at h
  | sres V₂ st₂ o₂ =>
      simp only [SlotResRel] at h
      obtain ⟨hslot, rfl, rfl⟩ := h
      exact ⟨V₂, rfl, hslot⟩

theorem SlotResRel.eres_right {d dx : Nat} {x y : Ident}
    {res₁ : Res D} {r : EResult D}
    (h : SlotResRel d dx x y res₁ (.eres r)) : res₁ = .eres r := by
  cases res₁ with
  | eres r₁ => simp only [SlotResRel] at h; rw [h]
  | sres => simp only [SlotResRel] at h

theorem SlotResRel.sres_right {d dx : Nat} {x y : Ident}
    {res₁ : Res D} {V₂ : VEnv D} {st : EvmState} {o : Outcome}
    (h : SlotResRel d dx x y res₁ (.sres V₂ st o)) :
    ∃ V₁, res₁ = .sres V₁ st o ∧ SlotRel d dx x y V₁ V₂ := by
  cases res₁ with
  | eres => simp only [SlotResRel] at h
  | sres V₁ st₁ o₁ =>
      simp only [SlotResRel] at h
      obtain ⟨hslot, rfl, rfl⟩ := h
      exact ⟨V₁, rfl, hslot⟩

/-- Forward half of the slot-renaming bisimulation. -/
theorem slot_fwd {funs : FunEnv D} {V₁ : VEnv D} {st : EvmState}
    {code : Code Op} {res₁ : Res D} (h : Step D funs V₁ st code res₁) :
    ∀ {d dx x y V₂}, SlotRel d dx x y V₁ V₂ →
      codeMentions x code = false → codeDeclares y code = false →
      ∃ res₂, Step D funs V₂ st (renameCode [(y, x)] code) res₂ ∧
        SlotResRel d dx x y res₁ res₂ := by
  induction h with
  | lit => intro d dx x y V₂ hslot _ _; exact ⟨_, Step.lit, rfl⟩
  | @var funs V st z value hget =>
      intro d dx x y V₂ hslot hmx _
      simp only [codeMentions, exprMentions, decide_eq_false_iff_not] at hmx
      by_cases hzy : z = y
      · subst z
        refine ⟨.eres (.vals [value] st), ?_, ?_⟩
        · simpa [renameCode, renameExpr] using
            Step.var (by rw [← hslot.get_y]; exact hget)
        · rfl
      · have hzx : z ≠ x := fun hzx => hmx hzx.symm
        refine ⟨.eres (.vals [value] st), ?_, ?_⟩
        · simpa [renameCode, renameExpr, hzy] using
            Step.var (by rw [← hslot.get_other hzx hzy]; exact hget)
        · rfl
  | builtinOk hargs hb ihargs =>
      intro d dx x y V₂ hslot hmx hdy
      obtain ⟨r, hs, hr⟩ := ihargs hslot
        (by simpa only [codeMentions, exprMentions] using hmx) rfl
      obtain rfl := hr.eres
      exact ⟨_, Step.builtinOk hs hb, rfl⟩
  | builtinHalt hargs hb ihargs =>
      intro d dx x y V₂ hslot hmx hdy
      obtain ⟨r, hs, hr⟩ := ihargs hslot
        (by simpa only [codeMentions, exprMentions] using hmx) rfl
      obtain rfl := hr.eres
      exact ⟨_, Step.builtinHalt hs hb, rfl⟩
  | builtinArgsHalt hargs ihargs =>
      intro d dx x y V₂ hslot hmx hdy
      obtain ⟨r, hs, hr⟩ := ihargs hslot
        (by simpa only [codeMentions, exprMentions] using hmx) rfl
      obtain rfl := hr.eres
      exact ⟨_, Step.builtinArgsHalt hs, rfl⟩
  | callOk hargs hlookup hlen hbody hout ihargs ihbody =>
      intro d dx x y V₂ hslot hmx hdy
      obtain ⟨r, hs, hr⟩ := ihargs hslot
        (by simpa only [codeMentions, exprMentions] using hmx) rfl
      obtain rfl := hr.eres
      exact ⟨_, Step.callOk hs hlookup hlen hbody hout, rfl⟩
  | callHalt hargs hlookup hlen hbody ihargs ihbody =>
      intro d dx x y V₂ hslot hmx hdy
      obtain ⟨r, hs, hr⟩ := ihargs hslot
        (by simpa only [codeMentions, exprMentions] using hmx) rfl
      obtain rfl := hr.eres
      exact ⟨_, Step.callHalt hs hlookup hlen hbody, rfl⟩
  | callArgsHalt hargs ihargs =>
      intro d dx x y V₂ hslot hmx hdy
      obtain ⟨r, hs, hr⟩ := ihargs hslot
        (by simpa only [codeMentions, exprMentions] using hmx) rfl
      obtain rfl := hr.eres
      exact ⟨_, Step.callArgsHalt hs, rfl⟩
  | argsNil => intro d dx x y V₂ hslot _ _; exact ⟨_, Step.argsNil, rfl⟩
  | argsCons hrest hexpr ihrest ihexpr =>
      intro d dx x y V₂ hslot hmx hdy
      simp only [codeMentions, argsMentions, Bool.or_eq_false_iff] at hmx
      obtain ⟨rr, hsr, hrr⟩ := ihrest hslot
        (by simp only [codeMentions]; exact hmx.2) rfl
      obtain rfl := hrr.eres
      obtain ⟨re, hse, hre⟩ := ihexpr hslot
        (by simp only [codeMentions]; exact hmx.1) rfl
      obtain rfl := hre.eres
      exact ⟨_, Step.argsCons hsr hse, rfl⟩
  | argsRestHalt hrest ihrest =>
      intro d dx x y V₂ hslot hmx hdy
      simp only [codeMentions, argsMentions, Bool.or_eq_false_iff] at hmx
      obtain ⟨rr, hsr, hrr⟩ := ihrest hslot
        (by simp only [codeMentions]; exact hmx.2) rfl
      obtain rfl := hrr.eres
      exact ⟨_, Step.argsRestHalt hsr, rfl⟩
  | argsHeadHalt hrest hexpr ihrest ihexpr =>
      intro d dx x y V₂ hslot hmx hdy
      simp only [codeMentions, argsMentions, Bool.or_eq_false_iff] at hmx
      obtain ⟨rr, hsr, hrr⟩ := ihrest hslot
        (by simp only [codeMentions]; exact hmx.2) rfl
      obtain rfl := hrr.eres
      obtain ⟨re, hse, hre⟩ := ihexpr hslot
        (by simp only [codeMentions]; exact hmx.1) rfl
      obtain rfl := hre.eres
      exact ⟨_, Step.argsHeadHalt hsr hse, rfl⟩
  | @funDef funs V st n ps rs body =>
      intro d dx x y V₂ hslot _ _
      refine ⟨.sres V₂ st .normal, ?_, ?_⟩
      · simpa [renameCode, renameStmt] using Step.funDef
      · exact ⟨hslot, rfl, rfl⟩
  | @block funs V st body Vb stb o hbody ihbody =>
      intro d dx x y V₂ hslot hmx hdy
      simp only [codeMentions, stmtMentions] at hmx
      simp only [codeDeclares, stmtDeclares] at hdy
      obtain ⟨r, hs, hr⟩ := ihbody hslot
        (by simp only [codeMentions]; exact hmx)
        (by simp only [codeDeclares]; exact hdy)
      obtain ⟨Vb₂, rfl, hslot'⟩ := hr.sres
      have hs' : Step D (hoist D (renameStmts [(y, x)] body) :: funs)
          V₂ st (.stmts (renameStmts [(y, x)] body)) (.sres Vb₂ stb o) := by
        rw [hoist_renameStmts]
        simpa [renameCode] using hs
      refine ⟨.sres (restore V₂ Vb₂) stb o, ?_, ?_⟩
      · simpa [renameCode, renameStmt] using Step.block hs'
      · exact ⟨hslot.restore_nested hslot' (venvLen_mono hbody rfl), rfl, rfl⟩
  | @letZero funs V st vars =>
      intro d dx x y V₂ hslot hmx hdy
      simp only [codeMentions, stmtMentions, optExprMentions, Bool.or_false,
        decide_eq_false_iff_not] at hmx
      simp only [codeDeclares, stmtDeclares] at hdy
      refine ⟨.sres (bindZeros D vars ++ V₂) st .normal, ?_, ?_⟩
      · simpa [renameCode, renameStmt] using Step.letZero
      · exact ⟨hslot.prependZeros hmx (by simpa using hdy), rfl, rfl⟩
  | @letVal _ _ _ vars e values st' hexpr hlen ih =>
      intro d dx x y V₂ hslot hmx hdy
      simp only [codeMentions, stmtMentions, optExprMentions,
        Bool.or_eq_false_iff, decide_eq_false_iff_not] at hmx
      simp only [codeDeclares, stmtDeclares] at hdy
      obtain ⟨r, hs, hr⟩ := ih hslot
        (by simp only [codeMentions]; exact hmx.2) rfl
      obtain rfl := hr.eres
      refine ⟨.sres (vars.zip values ++ V₂) st' .normal, ?_, ?_⟩
      · simpa [renameCode, renameStmt] using Step.letVal hs hlen
      · exact ⟨hslot.prependZip hmx.1 (by simpa using hdy), rfl, rfl⟩
  | @letHalt funs V st vars e st' hexpr ih =>
      intro d dx x y V₂ hslot hmx hdy
      simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hmx
      obtain ⟨r, hs, hr⟩ := ih hslot
        (by simp only [codeMentions]; exact hmx.2) rfl
      obtain rfl := hr.eres
      refine ⟨.sres V₂ st' .halt, ?_, ?_⟩
      · simpa [renameCode, renameStmt] using Step.letHalt hs
      · exact ⟨hslot, rfl, rfl⟩
  | @assignVal _ _ _ vars e values st' hexpr hlen ih =>
      intro d dx x y V₂ hslot hmx hdy
      simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff,
        decide_eq_false_iff_not] at hmx
      obtain ⟨r, hs, hr⟩ := ih hslot
        (by simp only [codeMentions]; exact hmx.2) rfl
      obtain rfl := hr.eres
      refine ⟨.sres (VEnv.setMany V₂ (vars.map (renameLookup [(y, x)])) values)
        st' .normal, ?_, ?_⟩
      · simpa [renameCode, renameStmt] using
          Step.assignVal hs (by simpa using hlen)
      · exact ⟨hslot.setMany hmx.1 values, rfl, rfl⟩
  | @assignHalt funs V st vars e st' hexpr ih =>
      intro d dx x y V₂ hslot hmx hdy
      simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hmx
      obtain ⟨r, hs, hr⟩ := ih hslot
        (by simp only [codeMentions]; exact hmx.2) rfl
      obtain rfl := hr.eres
      refine ⟨.sres V₂ st' .halt, ?_, ?_⟩
      · simpa [renameCode, renameStmt] using Step.assignHalt hs
      · exact ⟨hslot, rfl, rfl⟩
  | @exprStmt funs V st e st' hexpr ih =>
      intro d dx x y V₂ hslot hmx hdy
      obtain ⟨r, hs, hr⟩ := ih hslot
        (by simpa only [codeMentions, stmtMentions] using hmx) rfl
      obtain rfl := hr.eres
      refine ⟨.sres V₂ st' .normal, ?_, ?_⟩
      · simpa [renameCode, renameStmt] using Step.exprStmt hs
      · exact ⟨hslot, rfl, rfl⟩
  | @exprStmtHalt funs V st e st' hexpr ih =>
      intro d dx x y V₂ hslot hmx hdy
      obtain ⟨r, hs, hr⟩ := ih hslot
        (by simpa only [codeMentions, stmtMentions] using hmx) rfl
      obtain rfl := hr.eres
      refine ⟨.sres V₂ st' .halt, ?_, ?_⟩
      · simpa [renameCode, renameStmt] using Step.exprStmtHalt hs
      · exact ⟨hslot, rfl, rfl⟩
  | @ifTrue funs V st c body cv st₁ V' st₂ o hc hnz hbody ihc ihbody =>
      intro d dx x y V₂ hslot hmx hdy
      simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hmx
      simp only [codeDeclares, stmtDeclares] at hdy
      obtain ⟨rc, hsc, hrc⟩ := ihc hslot
        (by simp only [codeMentions]; exact hmx.1) rfl
      obtain rfl := hrc.eres
      obtain ⟨rb, hsb, hrb⟩ := ihbody hslot
        (by simp only [codeMentions, stmtMentions]; exact hmx.2)
        (by simp only [codeDeclares, stmtDeclares]; exact hdy)
      obtain ⟨V₂', rfl, hslot'⟩ := hrb.sres
      have hsb' : Step D funs V₂ st₁
          (.stmt (.block (renameStmts [(y, x)] body))) (.sres V₂' st₂ o) := by
        simpa [renameCode, renameStmt] using hsb
      refine ⟨.sres V₂' st₂ o, ?_, ?_⟩
      · simpa [renameCode, renameStmt] using Step.ifTrue hsc hnz hsb'
      · exact ⟨hslot', rfl, rfl⟩
  | @ifFalse funs V st c body cv st₁ hc hz ihc =>
      intro d dx x y V₂ hslot hmx hdy
      simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hmx
      obtain ⟨rc, hsc, hrc⟩ := ihc hslot
        (by simp only [codeMentions]; exact hmx.1) rfl
      obtain rfl := hrc.eres
      refine ⟨.sres V₂ st₁ .normal, ?_, ?_⟩
      · simpa [renameCode, renameStmt] using Step.ifFalse hsc hz
      · exact ⟨hslot, rfl, rfl⟩
  | @ifHalt funs V st c body st₁ hc ihc =>
      intro d dx x y V₂ hslot hmx hdy
      simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hmx
      obtain ⟨rc, hsc, hrc⟩ := ihc hslot
        (by simp only [codeMentions]; exact hmx.1) rfl
      obtain rfl := hrc.eres
      refine ⟨.sres V₂ st₁ .halt, ?_, ?_⟩
      · simpa [renameCode, renameStmt] using Step.ifHalt hsc
      · exact ⟨hslot, rfl, rfl⟩
  | @switchExec funs V st c cases dflt cv st₁ V' st₂ o hc hbody ihc ihbody =>
      intro d dx x y V₂ hslot hmx hdy
      simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hmx
      simp only [codeDeclares, stmtDeclares, Bool.or_eq_false_iff] at hdy
      obtain ⟨rc, hsc, hrc⟩ := ihc hslot
        (by simp only [codeMentions]; exact hmx.1.1) rfl
      obtain rfl := hrc.eres
      obtain ⟨rb, hsb, hrb⟩ := ihbody hslot (by
        simp only [codeMentions, stmtMentions]
        exact selectSwitch_not_mentions hmx.1.2 hmx.2) (by
        simp only [codeDeclares]
        exact selectSwitch_not_declares hdy.1 hdy.2)
      obtain ⟨V₂', rfl, hslot'⟩ := hrb.sres
      have hsb' : Step D funs V₂ st₁
          (.stmt (.block (renameStmts [(y, x)] (selectSwitch D cv cases dflt))))
          (.sres V₂' st₂ o) := by
        simpa [renameCode, renameStmt] using hsb
      rw [← selectSwitch_rename] at hsb'
      refine ⟨.sres V₂' st₂ o, ?_, ?_⟩
      · cases dflt <;> simpa [renameCode, renameStmt] using Step.switchExec hsc hsb'
      · exact ⟨hslot', rfl, rfl⟩
  | @switchHalt funs V st c cases dflt st₁ hc ihc =>
      intro d dx x y V₂ hslot hmx hdy
      simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hmx
      obtain ⟨rc, hsc, hrc⟩ := ihc hslot
        (by simp only [codeMentions]; exact hmx.1.1) rfl
      obtain rfl := hrc.eres
      refine ⟨.sres V₂ st₁ .halt, ?_, ?_⟩
      · cases dflt <;> simpa [renameCode, renameStmt] using Step.switchHalt hsc
      · exact ⟨hslot, rfl, rfl⟩
  | @forLoop funs V st init c post body Vinit stinit Vend stend o
      hinit hloop ihinit ihloop =>
      intro d dx x y V₂ hslot hmx hdy
      simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hmx
      simp only [codeDeclares, stmtDeclares, Bool.or_eq_false_iff] at hdy
      obtain ⟨⟨⟨hinitX, hcX⟩, hpostX⟩, hbodyX⟩ := hmx
      obtain ⟨⟨hinitY, hpostY⟩, hbodyY⟩ := hdy
      obtain ⟨ri, hsi, hri⟩ := ihinit hslot
        (by simp only [codeMentions]; exact hinitX)
        (by simp only [codeDeclares]; exact hinitY)
      obtain ⟨Vi₂, rfl, hslotI⟩ := hri.sres
      have hsi' : Step D (hoist D (renameStmts [(y, x)] init) :: funs) V₂ st
          (.stmts (renameStmts [(y, x)] init)) (.sres Vi₂ stinit .normal) := by
        rw [hoist_renameStmts]
        simpa [renameCode] using hsi
      obtain ⟨rl, hsl, hrl⟩ := ihloop hslotI (by
        simp only [codeMentions, hcX, hpostX, hbodyX, Bool.or_false]) (by
        simp only [codeDeclares, hpostY, hbodyY, Bool.or_false])
      obtain ⟨Ve₂, rfl, hslotE⟩ := hrl.sres
      have hsl' : Step D (hoist D (renameStmts [(y, x)] init) :: funs) Vi₂ stinit
          (.loop (renameExpr [(y, x)] c) (renameStmts [(y, x)] post)
            (renameStmts [(y, x)] body)) (.sres Ve₂ stend o) := by
        rw [hoist_renameStmts]
        simpa [renameCode] using hsl
      have hmono : V.length ≤ Vend.length :=
        Nat.le_trans (venvLen_mono hinit rfl) (venvLen_mono hloop rfl)
      refine ⟨.sres (restore V₂ Ve₂) stend o, ?_, ?_⟩
      · simpa [renameCode, renameStmt] using Step.forLoop hsi' hsl'
      · exact ⟨hslot.restore_nested hslotE hmono, rfl, rfl⟩
  | @forInitHalt funs V st init c post body Vinit stinit hinit ihinit =>
      intro d dx x y V₂ hslot hmx hdy
      simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hmx
      simp only [codeDeclares, stmtDeclares, Bool.or_eq_false_iff] at hdy
      obtain ⟨⟨⟨hinitX, hcX⟩, hpostX⟩, hbodyX⟩ := hmx
      obtain ⟨⟨hinitY, hpostY⟩, hbodyY⟩ := hdy
      obtain ⟨ri, hsi, hri⟩ := ihinit hslot
        (by simp only [codeMentions]; exact hinitX)
        (by simp only [codeDeclares]; exact hinitY)
      obtain ⟨Vi₂, rfl, hslotI⟩ := hri.sres
      have hsi' : Step D (hoist D (renameStmts [(y, x)] init) :: funs) V₂ st
          (.stmts (renameStmts [(y, x)] init)) (.sres Vi₂ stinit .halt) := by
        rw [hoist_renameStmts]
        simpa [renameCode] using hsi
      refine ⟨.sres (restore V₂ Vi₂) stinit .halt, ?_, ?_⟩
      · simpa [renameCode, renameStmt] using Step.forInitHalt hsi'
      · exact ⟨hslot.restore_nested hslotI (venvLen_mono hinit rfl), rfl, rfl⟩
  | @«break» funs V st =>
      intro d dx x y V₂ hslot _ _
      refine ⟨.sres V₂ st .«break», ?_, ⟨hslot, rfl, rfl⟩⟩
      simpa [renameCode, renameStmt] using Step.break
  | @«continue» funs V st =>
      intro d dx x y V₂ hslot _ _
      refine ⟨.sres V₂ st .«continue», ?_, ⟨hslot, rfl, rfl⟩⟩
      simpa [renameCode, renameStmt] using Step.continue
  | @«leave» funs V st =>
      intro d dx x y V₂ hslot _ _
      refine ⟨.sres V₂ st .leave, ?_, ?_⟩
      · simpa [renameCode, renameStmt] using Step.leave
      · exact ⟨hslot, rfl, rfl⟩
  | @seqNil funs V st =>
      intro d dx x y V₂ hslot _ _
      refine ⟨.sres V₂ st .normal, ?_, ⟨hslot, rfl, rfl⟩⟩
      simpa [renameCode, renameStmts] using Step.seqNil
  | @seqCons funs V st s rest Vs sts Vr str o hstmt hrest ihstmt ihrest =>
      intro d dx x y V₂ hslot hmx hdy
      simp only [codeMentions, stmtsMentions, Bool.or_eq_false_iff] at hmx
      simp only [codeDeclares, stmtsDeclare, Bool.or_eq_false_iff] at hdy
      obtain ⟨rs, hss, hrs⟩ := ihstmt hslot
        (by simp only [codeMentions]; exact hmx.1)
        (by simp only [codeDeclares]; exact hdy.1)
      obtain ⟨Vs₂, rfl, hslotS⟩ := hrs.sres
      obtain ⟨rr, hsr, hrr⟩ := ihrest hslotS
        (by simp only [codeMentions]; exact hmx.2)
        (by simp only [codeDeclares]; exact hdy.2)
      obtain ⟨Vr₂, rfl, hslotR⟩ := hrr.sres
      refine ⟨.sres Vr₂ str o, ?_, ⟨hslotR, rfl, rfl⟩⟩
      simpa [renameCode, renameStmts] using Step.seqCons hss hsr
  | @seqStop funs V st s rest Vs sts o hstmt hne ihstmt =>
      intro d dx x y V₂ hslot hmx hdy
      simp only [codeMentions, stmtsMentions, Bool.or_eq_false_iff] at hmx
      simp only [codeDeclares, stmtsDeclare, Bool.or_eq_false_iff] at hdy
      obtain ⟨rs, hss, hrs⟩ := ihstmt hslot
        (by simp only [codeMentions]; exact hmx.1)
        (by simp only [codeDeclares]; exact hdy.1)
      obtain ⟨Vs₂, rfl, hslotS⟩ := hrs.sres
      refine ⟨.sres Vs₂ sts o, ?_, ⟨hslotS, rfl, rfl⟩⟩
      simpa [renameCode, renameStmts] using Step.seqStop hss hne
  | @loopDone funs V st c post body cv st₁ hc hz ihc =>
      intro d dx x y V₂ hslot hmx hdy
      simp only [codeMentions, Bool.or_eq_false_iff] at hmx
      obtain ⟨rc, hsc, hrc⟩ := ihc hslot
        (by simp only [codeMentions]; exact hmx.1.1) rfl
      obtain rfl := hrc.eres
      refine ⟨.sres V₂ st₁ .normal, ?_, ⟨hslot, rfl, rfl⟩⟩
      simpa [renameCode] using Step.loopDone hsc hz
  | @loopCondHalt funs V st c post body st₁ hc ihc =>
      intro d dx x y V₂ hslot hmx hdy
      simp only [codeMentions, Bool.or_eq_false_iff] at hmx
      obtain ⟨rc, hsc, hrc⟩ := ihc hslot
        (by simp only [codeMentions]; exact hmx.1.1) rfl
      obtain rfl := hrc.eres
      refine ⟨.sres V₂ st₁ .halt, ?_, ⟨hslot, rfl, rfl⟩⟩
      simpa [renameCode] using Step.loopCondHalt hsc
  | @loopStep funs V st c post body cv st₁ Vb stb ob Vp stp Vend stend o
      hc hnz hbody hob hpost hrec ihc ihbody ihpost ihrec =>
      intro d dx x y V₂ hslot hmx hdy
      simp only [codeMentions, Bool.or_eq_false_iff] at hmx
      simp only [codeDeclares, Bool.or_eq_false_iff] at hdy
      obtain ⟨⟨hcX, hpostX⟩, hbodyX⟩ := hmx
      obtain ⟨hpostY, hbodyY⟩ := hdy
      obtain ⟨rc, hsc, hrc⟩ := ihc hslot
        (by simp only [codeMentions]; exact hcX) rfl
      obtain rfl := hrc.eres
      obtain ⟨rb, hsb, hrb⟩ := ihbody hslot
        (by simp only [codeMentions, stmtMentions]; exact hbodyX)
        (by simp only [codeDeclares, stmtDeclares]; exact hbodyY)
      obtain ⟨Vb₂, rfl, hslotB⟩ := hrb.sres
      obtain ⟨rp, hsp, hrp⟩ := ihpost hslotB
        (by simp only [codeMentions, stmtMentions]; exact hpostX)
        (by simp only [codeDeclares, stmtDeclares]; exact hpostY)
      obtain ⟨Vp₂, rfl, hslotP⟩ := hrp.sres
      obtain ⟨rr, hsr, hrr⟩ := ihrec hslotP
        (by simp only [codeMentions, hcX, hpostX, hbodyX, Bool.or_false])
        (by simp only [codeDeclares, hpostY, hbodyY, Bool.or_false])
      obtain ⟨Ve₂, rfl, hslotE⟩ := hrr.sres
      have hsb' : Step D funs V₂ st₁
          (.stmt (.block (renameStmts [(y, x)] body))) (.sres Vb₂ stb ob) := by
        simpa [renameCode, renameStmt] using hsb
      have hsp' : Step D funs Vb₂ stb
          (.stmt (.block (renameStmts [(y, x)] post))) (.sres Vp₂ stp .normal) := by
        simpa [renameCode, renameStmt] using hsp
      refine ⟨.sres Ve₂ stend o, ?_, ⟨hslotE, rfl, rfl⟩⟩
      simpa [renameCode] using Step.loopStep hsc hnz hsb' hob hsp' hsr
  | @loopPostHalt funs V st c post body cv st₁ Vb stb ob Vp stp
      hc hnz hbody hob hpost ihc ihbody ihpost =>
      intro d dx x y V₂ hslot hmx hdy
      simp only [codeMentions, Bool.or_eq_false_iff] at hmx
      simp only [codeDeclares, Bool.or_eq_false_iff] at hdy
      obtain ⟨⟨hcX, hpostX⟩, hbodyX⟩ := hmx
      obtain ⟨hpostY, hbodyY⟩ := hdy
      obtain ⟨rc, hsc, hrc⟩ := ihc hslot
        (by simp only [codeMentions]; exact hcX) rfl
      obtain rfl := hrc.eres
      obtain ⟨rb, hsb, hrb⟩ := ihbody hslot
        (by simp only [codeMentions, stmtMentions]; exact hbodyX)
        (by simp only [codeDeclares, stmtDeclares]; exact hbodyY)
      obtain ⟨Vb₂, rfl, hslotB⟩ := hrb.sres
      obtain ⟨rp, hsp, hrp⟩ := ihpost hslotB
        (by simp only [codeMentions, stmtMentions]; exact hpostX)
        (by simp only [codeDeclares, stmtDeclares]; exact hpostY)
      obtain ⟨Vp₂, rfl, hslotP⟩ := hrp.sres
      have hsb' : Step D funs V₂ st₁
          (.stmt (.block (renameStmts [(y, x)] body))) (.sres Vb₂ stb ob) := by
        simpa [renameCode, renameStmt] using hsb
      have hsp' : Step D funs Vb₂ stb
          (.stmt (.block (renameStmts [(y, x)] post))) (.sres Vp₂ stp .halt) := by
        simpa [renameCode, renameStmt] using hsp
      refine ⟨.sres Vp₂ stp .halt, ?_, ⟨hslotP, rfl, rfl⟩⟩
      simpa [renameCode] using Step.loopPostHalt hsc hnz hsb' hob hsp'
  | @loopBreak funs V st c post body cv st₁ Vb stb hc hnz hbody ihc ihbody =>
      intro d dx x y V₂ hslot hmx hdy
      simp only [codeMentions, Bool.or_eq_false_iff] at hmx
      simp only [codeDeclares, Bool.or_eq_false_iff] at hdy
      obtain ⟨⟨hcX, hpostX⟩, hbodyX⟩ := hmx
      obtain ⟨hpostY, hbodyY⟩ := hdy
      obtain ⟨rc, hsc, hrc⟩ := ihc hslot
        (by simp only [codeMentions]; exact hcX) rfl
      obtain rfl := hrc.eres
      obtain ⟨rb, hsb, hrb⟩ := ihbody hslot
        (by simp only [codeMentions, stmtMentions]; exact hbodyX)
        (by simp only [codeDeclares, stmtDeclares]; exact hbodyY)
      obtain ⟨Vb₂, rfl, hslotB⟩ := hrb.sres
      have hsb' : Step D funs V₂ st₁
          (.stmt (.block (renameStmts [(y, x)] body))) (.sres Vb₂ stb .«break») := by
        simpa [renameCode, renameStmt] using hsb
      refine ⟨.sres Vb₂ stb .normal, ?_, ⟨hslotB, rfl, rfl⟩⟩
      simpa [renameCode] using Step.loopBreak hsc hnz hsb'
  | @loopLeave funs V st c post body cv st₁ Vb stb hc hnz hbody ihc ihbody =>
      intro d dx x y V₂ hslot hmx hdy
      simp only [codeMentions, Bool.or_eq_false_iff] at hmx
      simp only [codeDeclares, Bool.or_eq_false_iff] at hdy
      obtain ⟨⟨hcX, hpostX⟩, hbodyX⟩ := hmx
      obtain ⟨hpostY, hbodyY⟩ := hdy
      obtain ⟨rc, hsc, hrc⟩ := ihc hslot
        (by simp only [codeMentions]; exact hcX) rfl
      obtain rfl := hrc.eres
      obtain ⟨rb, hsb, hrb⟩ := ihbody hslot
        (by simp only [codeMentions, stmtMentions]; exact hbodyX)
        (by simp only [codeDeclares, stmtDeclares]; exact hbodyY)
      obtain ⟨Vb₂, rfl, hslotB⟩ := hrb.sres
      have hsb' : Step D funs V₂ st₁
          (.stmt (.block (renameStmts [(y, x)] body))) (.sres Vb₂ stb .leave) := by
        simpa [renameCode, renameStmt] using hsb
      refine ⟨.sres Vb₂ stb .leave, ?_, ⟨hslotB, rfl, rfl⟩⟩
      simpa [renameCode] using Step.loopLeave hsc hnz hsb'
  | @loopBodyHalt funs V st c post body cv st₁ Vb stb hc hnz hbody ihc ihbody =>
      intro d dx x y V₂ hslot hmx hdy
      simp only [codeMentions, Bool.or_eq_false_iff] at hmx
      simp only [codeDeclares, Bool.or_eq_false_iff] at hdy
      obtain ⟨⟨hcX, hpostX⟩, hbodyX⟩ := hmx
      obtain ⟨hpostY, hbodyY⟩ := hdy
      obtain ⟨rc, hsc, hrc⟩ := ihc hslot
        (by simp only [codeMentions]; exact hcX) rfl
      obtain rfl := hrc.eres
      obtain ⟨rb, hsb, hrb⟩ := ihbody hslot
        (by simp only [codeMentions, stmtMentions]; exact hbodyX)
        (by simp only [codeDeclares, stmtDeclares]; exact hbodyY)
      obtain ⟨Vb₂, rfl, hslotB⟩ := hrb.sres
      have hsb' : Step D funs V₂ st₁
          (.stmt (.block (renameStmts [(y, x)] body))) (.sres Vb₂ stb .halt) := by
        simpa [renameCode, renameStmt] using hsb
      refine ⟨.sres Vb₂ stb .halt, ?_, ⟨hslotB, rfl, rfl⟩⟩
      simpa [renameCode] using Step.loopBodyHalt hsc hnz hsb'

/-- Reverse half of the slot-renaming bisimulation.  Here `code` is the
already-coalesced code; renaming `x` back to `y` reconstructs the source. -/
theorem slot_rev_fwd {funs : FunEnv D} {V₂ : VEnv D} {st : EvmState}
    {code : Code Op} {res₂ : Res D} (h : Step D funs V₂ st code res₂) :
    ∀ {d dx x y V₁}, SlotRel d dx x y V₁ V₂ → x ≠ y →
      codeMentions y code = false → codeDeclares x code = false →
      ∃ res₁, Step D funs V₁ st (renameCode [(x, y)] code) res₁ ∧
        SlotResRel d dx x y res₁ res₂ := by
  induction h with
  | lit => intro d dx x y V₁ hslot _ _ _; exact ⟨_, Step.lit, rfl⟩
  | @var funs V st z value hget =>
      intro d dx x y V₁ hslot hxy hmy _
      simp only [codeMentions, exprMentions, decide_eq_false_iff_not] at hmy
      by_cases hzx : z = x
      · subst z
        refine ⟨.eres (.vals [value] st), ?_, ?_⟩
        · simpa [renameCode, renameExpr] using
            Step.var (by rw [hslot.get_y]; exact hget)
        · rfl
      · have hzy : z ≠ y := fun hzy => hmy hzy.symm
        refine ⟨.eres (.vals [value] st), ?_, ?_⟩
        · simpa [renameCode, renameExpr, hzx] using
            Step.var (by rw [hslot.get_other hzx hzy]; exact hget)
        · rfl
  | builtinOk hargs hb ihargs =>
      intro d dx x y V₁ hslot hxy hmy hdx
      obtain ⟨r, hs, hr⟩ := ihargs hslot hxy
        (by simpa only [codeMentions, exprMentions] using hmy) rfl
      obtain rfl := hr.eres_right
      exact ⟨_, Step.builtinOk hs hb, rfl⟩
  | builtinHalt hargs hb ihargs =>
      intro d dx x y V₁ hslot hxy hmy hdx
      obtain ⟨r, hs, hr⟩ := ihargs hslot hxy
        (by simpa only [codeMentions, exprMentions] using hmy) rfl
      obtain rfl := hr.eres_right
      exact ⟨_, Step.builtinHalt hs hb, rfl⟩
  | builtinArgsHalt hargs ihargs =>
      intro d dx x y V₁ hslot hxy hmy hdx
      obtain ⟨r, hs, hr⟩ := ihargs hslot hxy
        (by simpa only [codeMentions, exprMentions] using hmy) rfl
      obtain rfl := hr.eres_right
      exact ⟨_, Step.builtinArgsHalt hs, rfl⟩
  | callOk hargs hlookup hlen hbody hout ihargs ihbody =>
      intro d dx x y V₁ hslot hxy hmy hdx
      obtain ⟨r, hs, hr⟩ := ihargs hslot hxy
        (by simpa only [codeMentions, exprMentions] using hmy) rfl
      obtain rfl := hr.eres_right
      exact ⟨_, Step.callOk hs hlookup hlen hbody hout, rfl⟩
  | callHalt hargs hlookup hlen hbody ihargs ihbody =>
      intro d dx x y V₁ hslot hxy hmy hdx
      obtain ⟨r, hs, hr⟩ := ihargs hslot hxy
        (by simpa only [codeMentions, exprMentions] using hmy) rfl
      obtain rfl := hr.eres_right
      exact ⟨_, Step.callHalt hs hlookup hlen hbody, rfl⟩
  | callArgsHalt hargs ihargs =>
      intro d dx x y V₁ hslot hxy hmy hdx
      obtain ⟨r, hs, hr⟩ := ihargs hslot hxy
        (by simpa only [codeMentions, exprMentions] using hmy) rfl
      obtain rfl := hr.eres_right
      exact ⟨_, Step.callArgsHalt hs, rfl⟩
  | argsNil => intro d dx x y V₁ hslot _ _ _; exact ⟨_, Step.argsNil, rfl⟩
  | argsCons hrest hexpr ihrest ihexpr =>
      intro d dx x y V₁ hslot hxy hmy hdx
      simp only [codeMentions, argsMentions, Bool.or_eq_false_iff] at hmy
      obtain ⟨rr, hsr, hrr⟩ := ihrest hslot hxy
        (by simp only [codeMentions]; exact hmy.2) rfl
      obtain rfl := hrr.eres_right
      obtain ⟨re, hse, hre⟩ := ihexpr hslot hxy
        (by simp only [codeMentions]; exact hmy.1) rfl
      obtain rfl := hre.eres_right
      exact ⟨_, Step.argsCons hsr hse, rfl⟩
  | argsRestHalt hrest ihrest =>
      intro d dx x y V₁ hslot hxy hmy hdx
      simp only [codeMentions, argsMentions, Bool.or_eq_false_iff] at hmy
      obtain ⟨rr, hsr, hrr⟩ := ihrest hslot hxy
        (by simp only [codeMentions]; exact hmy.2) rfl
      obtain rfl := hrr.eres_right
      exact ⟨_, Step.argsRestHalt hsr, rfl⟩
  | argsHeadHalt hrest hexpr ihrest ihexpr =>
      intro d dx x y V₁ hslot hxy hmy hdx
      simp only [codeMentions, argsMentions, Bool.or_eq_false_iff] at hmy
      obtain ⟨rr, hsr, hrr⟩ := ihrest hslot hxy
        (by simp only [codeMentions]; exact hmy.2) rfl
      obtain rfl := hrr.eres_right
      obtain ⟨re, hse, hre⟩ := ihexpr hslot hxy
        (by simp only [codeMentions]; exact hmy.1) rfl
      obtain rfl := hre.eres_right
      exact ⟨_, Step.argsHeadHalt hsr hse, rfl⟩
  | @funDef funs V st n ps rs body =>
      intro d dx x y V₁ hslot hxy hmy hdx
      refine ⟨.sres V₁ st .normal, ?_, ⟨hslot, rfl, rfl⟩⟩
      simpa [renameCode, renameStmt] using Step.funDef
  | @block funs V st body Vb stb o hbody ihbody =>
      intro d dx x y V₁ hslot hxy hmy hdx
      simp only [codeMentions, stmtMentions] at hmy
      simp only [codeDeclares, stmtDeclares] at hdx
      obtain ⟨r, hs, hr⟩ := ihbody hslot hxy
        (by simp only [codeMentions]; exact hmy)
        (by simp only [codeDeclares]; exact hdx)
      obtain ⟨Vb₁, rfl, hslot'⟩ := hr.sres_right
      have hs' : Step D (hoist D (renameStmts [(x, y)] body) :: funs) V₁ st
          (.stmts (renameStmts [(x, y)] body)) (.sres Vb₁ stb o) := by
        rw [hoist_renameStmts]
        simpa [renameCode] using hs
      refine ⟨.sres (restore V₁ Vb₁) stb o, ?_, ?_⟩
      · simpa [renameCode, renameStmt] using Step.block hs'
      · have hmono₂ : V.length ≤ Vb.length := venvLen_mono hbody rfl
        have hmono₁ : V₁.length ≤ Vb₁.length := by
          rw [hslot.length, hslot'.length]
          omega
        exact ⟨hslot.restore_nested hslot' hmono₁, rfl, rfl⟩
  | @letZero funs V st vars =>
      intro d dx x y V₁ hslot hxy hmy hdx
      simp only [codeMentions, stmtMentions, optExprMentions, Bool.or_false,
        decide_eq_false_iff_not] at hmy
      simp only [codeDeclares, stmtDeclares] at hdx
      refine ⟨.sres (bindZeros D vars ++ V₁) st .normal, ?_, ?_⟩
      · simpa [renameCode, renameStmt] using Step.letZero
      · exact ⟨hslot.prependZeros (by simpa using hdx) (by simpa using hmy), rfl, rfl⟩
  | @letVal funs V st vars e values st' hexpr hlen ih =>
      intro d dx x y V₁ hslot hxy hmy hdx
      simp only [codeMentions, stmtMentions, optExprMentions,
        Bool.or_eq_false_iff, decide_eq_false_iff_not] at hmy
      simp only [codeDeclares, stmtDeclares] at hdx
      obtain ⟨r, hs, hr⟩ := ih hslot hxy
        (by simp only [codeMentions]; exact hmy.2) rfl
      obtain rfl := hr.eres_right
      refine ⟨.sres (vars.zip values ++ V₁) st' .normal, ?_, ?_⟩
      · simpa [renameCode, renameStmt] using Step.letVal hs hlen
      · exact ⟨hslot.prependZip (by simpa using hdx) hmy.1, rfl, rfl⟩
  | @letHalt funs V st vars e st' hexpr ih =>
      intro d dx x y V₁ hslot hxy hmy hdx
      simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hmy
      obtain ⟨r, hs, hr⟩ := ih hslot hxy
        (by simp only [codeMentions]; exact hmy.2) rfl
      obtain rfl := hr.eres_right
      refine ⟨.sres V₁ st' .halt, ?_, ⟨hslot, rfl, rfl⟩⟩
      simpa [renameCode, renameStmt] using Step.letHalt hs
  | @assignVal funs V st vars e values st' hexpr hlen ih =>
      intro d dx x y V₁ hslot hxy hmy hdx
      simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff,
        decide_eq_false_iff_not] at hmy
      obtain ⟨r, hs, hr⟩ := ih hslot hxy
        (by simp only [codeMentions]; exact hmy.2) rfl
      obtain rfl := hr.eres_right
      refine ⟨.sres (VEnv.setMany V₁ (vars.map (renameLookup [(x, y)])) values)
        st' .normal, ?_, ?_⟩
      · simpa [renameCode, renameStmt] using Step.assignVal hs (by simpa using hlen)
      · exact ⟨hslot.setManyRev hxy hmy.1 values, rfl, rfl⟩
  | @assignHalt funs V st vars e st' hexpr ih =>
      intro d dx x y V₁ hslot hxy hmy hdx
      simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hmy
      obtain ⟨r, hs, hr⟩ := ih hslot hxy
        (by simp only [codeMentions]; exact hmy.2) rfl
      obtain rfl := hr.eres_right
      refine ⟨.sres V₁ st' .halt, ?_, ⟨hslot, rfl, rfl⟩⟩
      simpa [renameCode, renameStmt] using Step.assignHalt hs
  | @exprStmt funs V st e st' hexpr ih =>
      intro d dx x y V₁ hslot hxy hmy hdx
      obtain ⟨r, hs, hr⟩ := ih hslot hxy
        (by simpa only [codeMentions, stmtMentions] using hmy) rfl
      obtain rfl := hr.eres_right
      refine ⟨.sres V₁ st' .normal, ?_, ⟨hslot, rfl, rfl⟩⟩
      simpa [renameCode, renameStmt] using Step.exprStmt hs
  | @exprStmtHalt funs V st e st' hexpr ih =>
      intro d dx x y V₁ hslot hxy hmy hdx
      obtain ⟨r, hs, hr⟩ := ih hslot hxy
        (by simpa only [codeMentions, stmtMentions] using hmy) rfl
      obtain rfl := hr.eres_right
      refine ⟨.sres V₁ st' .halt, ?_, ⟨hslot, rfl, rfl⟩⟩
      simpa [renameCode, renameStmt] using Step.exprStmtHalt hs
  | @ifTrue funs V st c body cv st₁ V' st₂ o hc hnz hbody ihc ihbody =>
      intro d dx x y V₁ hslot hxy hmy hdx
      simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hmy
      simp only [codeDeclares, stmtDeclares] at hdx
      obtain ⟨rc, hsc, hrc⟩ := ihc hslot hxy
        (by simp only [codeMentions]; exact hmy.1) rfl
      obtain rfl := hrc.eres_right
      obtain ⟨rb, hsb, hrb⟩ := ihbody hslot hxy
        (by simp only [codeMentions, stmtMentions]; exact hmy.2)
        (by simp only [codeDeclares, stmtDeclares]; exact hdx)
      obtain ⟨V₁', rfl, hslot'⟩ := hrb.sres_right
      have hsb' : Step D funs V₁ st₁
          (.stmt (.block (renameStmts [(x, y)] body))) (.sres V₁' st₂ o) := by
        simpa [renameCode, renameStmt] using hsb
      refine ⟨.sres V₁' st₂ o, ?_, ⟨hslot', rfl, rfl⟩⟩
      simpa [renameCode, renameStmt] using Step.ifTrue hsc hnz hsb'
  | @ifFalse funs V st c body cv st₁ hc hz ihc =>
      intro d dx x y V₁ hslot hxy hmy hdx
      simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hmy
      obtain ⟨rc, hsc, hrc⟩ := ihc hslot hxy
        (by simp only [codeMentions]; exact hmy.1) rfl
      obtain rfl := hrc.eres_right
      refine ⟨.sres V₁ st₁ .normal, ?_, ⟨hslot, rfl, rfl⟩⟩
      simpa [renameCode, renameStmt] using Step.ifFalse hsc hz
  | @ifHalt funs V st c body st₁ hc ihc =>
      intro d dx x y V₁ hslot hxy hmy hdx
      simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hmy
      obtain ⟨rc, hsc, hrc⟩ := ihc hslot hxy
        (by simp only [codeMentions]; exact hmy.1) rfl
      obtain rfl := hrc.eres_right
      refine ⟨.sres V₁ st₁ .halt, ?_, ⟨hslot, rfl, rfl⟩⟩
      simpa [renameCode, renameStmt] using Step.ifHalt hsc
  | @switchExec funs V st c cases dflt cv st₁ V' st₂ o hc hbody ihc ihbody =>
      intro d dx x y V₁ hslot hxy hmy hdx
      simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hmy
      simp only [codeDeclares, stmtDeclares, Bool.or_eq_false_iff] at hdx
      obtain ⟨rc, hsc, hrc⟩ := ihc hslot hxy
        (by simp only [codeMentions]; exact hmy.1.1) rfl
      obtain rfl := hrc.eres_right
      obtain ⟨rb, hsb, hrb⟩ := ihbody hslot hxy (by
        simp only [codeMentions, stmtMentions]
        exact selectSwitch_not_mentions hmy.1.2 hmy.2) (by
        simp only [codeDeclares]
        exact selectSwitch_not_declares hdx.1 hdx.2)
      obtain ⟨V₁', rfl, hslot'⟩ := hrb.sres_right
      have hsb' : Step D funs V₁ st₁
          (.stmt (.block (renameStmts [(x, y)] (selectSwitch D cv cases dflt))))
          (.sres V₁' st₂ o) := by
        simpa [renameCode, renameStmt] using hsb
      rw [← selectSwitch_rename] at hsb'
      refine ⟨.sres V₁' st₂ o, ?_, ⟨hslot', rfl, rfl⟩⟩
      cases dflt <;> simpa [renameCode, renameStmt] using Step.switchExec hsc hsb'
  | @switchHalt funs V st c cases dflt st₁ hc ihc =>
      intro d dx x y V₁ hslot hxy hmy hdx
      simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hmy
      obtain ⟨rc, hsc, hrc⟩ := ihc hslot hxy
        (by simp only [codeMentions]; exact hmy.1.1) rfl
      obtain rfl := hrc.eres_right
      refine ⟨.sres V₁ st₁ .halt, ?_, ⟨hslot, rfl, rfl⟩⟩
      cases dflt <;> simpa [renameCode, renameStmt] using Step.switchHalt hsc
  | @forLoop funs V st init c post body Vinit stinit Vend stend o
      hinit hloop ihinit ihloop =>
      intro d dx x y V₁ hslot hxy hmy hdx
      simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hmy
      simp only [codeDeclares, stmtDeclares, Bool.or_eq_false_iff] at hdx
      obtain ⟨⟨⟨hinitY, hcY⟩, hpostY⟩, hbodyY⟩ := hmy
      obtain ⟨⟨hinitX, hpostX⟩, hbodyX⟩ := hdx
      obtain ⟨ri, hsi, hri⟩ := ihinit hslot hxy
        (by simp only [codeMentions]; exact hinitY)
        (by simp only [codeDeclares]; exact hinitX)
      obtain ⟨Vi₁, rfl, hslotI⟩ := hri.sres_right
      have hsi' : Step D (hoist D (renameStmts [(x, y)] init) :: funs) V₁ st
          (.stmts (renameStmts [(x, y)] init)) (.sres Vi₁ stinit .normal) := by
        rw [hoist_renameStmts]
        simpa [renameCode] using hsi
      obtain ⟨rl, hsl, hrl⟩ := ihloop hslotI hxy (by
        simp only [codeMentions, hcY, hpostY, hbodyY, Bool.or_false]) (by
        simp only [codeDeclares, hpostX, hbodyX, Bool.or_false])
      obtain ⟨Ve₁, rfl, hslotE⟩ := hrl.sres_right
      have hsl' : Step D (hoist D (renameStmts [(x, y)] init) :: funs) Vi₁ stinit
          (.loop (renameExpr [(x, y)] c) (renameStmts [(x, y)] post)
            (renameStmts [(x, y)] body)) (.sres Ve₁ stend o) := by
        rw [hoist_renameStmts]
        simpa [renameCode] using hsl
      have hmono₂ : V.length ≤ Vend.length :=
        Nat.le_trans (venvLen_mono hinit rfl) (venvLen_mono hloop rfl)
      have hmono₁ : V₁.length ≤ Ve₁.length := by
        rw [hslot.length, hslotE.length]
        omega
      refine ⟨.sres (restore V₁ Ve₁) stend o, ?_, ?_⟩
      · simpa [renameCode, renameStmt] using Step.forLoop hsi' hsl'
      · exact ⟨hslot.restore_nested hslotE hmono₁, rfl, rfl⟩
  | @forInitHalt funs V st init c post body Vinit stinit hinit ihinit =>
      intro d dx x y V₁ hslot hxy hmy hdx
      simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hmy
      simp only [codeDeclares, stmtDeclares, Bool.or_eq_false_iff] at hdx
      obtain ⟨⟨⟨hinitY, hcY⟩, hpostY⟩, hbodyY⟩ := hmy
      obtain ⟨⟨hinitX, hpostX⟩, hbodyX⟩ := hdx
      obtain ⟨ri, hsi, hri⟩ := ihinit hslot hxy
        (by simp only [codeMentions]; exact hinitY)
        (by simp only [codeDeclares]; exact hinitX)
      obtain ⟨Vi₁, rfl, hslotI⟩ := hri.sres_right
      have hsi' : Step D (hoist D (renameStmts [(x, y)] init) :: funs) V₁ st
          (.stmts (renameStmts [(x, y)] init)) (.sres Vi₁ stinit .halt) := by
        rw [hoist_renameStmts]
        simpa [renameCode] using hsi
      have hmono₂ : V.length ≤ Vinit.length := venvLen_mono hinit rfl
      have hmono₁ : V₁.length ≤ Vi₁.length := by
        rw [hslot.length, hslotI.length]
        omega
      refine ⟨.sres (restore V₁ Vi₁) stinit .halt, ?_, ?_⟩
      · simpa [renameCode, renameStmt] using Step.forInitHalt hsi'
      · exact ⟨hslot.restore_nested hslotI hmono₁, rfl, rfl⟩
  | @«break» funs V st =>
      intro d dx x y V₁ hslot hxy hmy hdx
      refine ⟨.sres V₁ st .«break», ?_, ⟨hslot, rfl, rfl⟩⟩
      simpa [renameCode, renameStmt] using Step.break
  | @«continue» funs V st =>
      intro d dx x y V₁ hslot hxy hmy hdx
      refine ⟨.sres V₁ st .«continue», ?_, ⟨hslot, rfl, rfl⟩⟩
      simpa [renameCode, renameStmt] using Step.continue
  | @«leave» funs V st =>
      intro d dx x y V₁ hslot hxy hmy hdx
      refine ⟨.sres V₁ st .leave, ?_, ⟨hslot, rfl, rfl⟩⟩
      simpa [renameCode, renameStmt] using Step.leave
  | @seqNil funs V st =>
      intro d dx x y V₁ hslot hxy hmy hdx
      refine ⟨.sres V₁ st .normal, ?_, ⟨hslot, rfl, rfl⟩⟩
      simpa [renameCode, renameStmts] using Step.seqNil
  | @seqCons funs V st s rest Vs sts Vr str o hstmt hrest ihstmt ihrest =>
      intro d dx x y V₁ hslot hxy hmy hdx
      simp only [codeMentions, stmtsMentions, Bool.or_eq_false_iff] at hmy
      simp only [codeDeclares, stmtsDeclare, Bool.or_eq_false_iff] at hdx
      obtain ⟨rs, hss, hrs⟩ := ihstmt hslot hxy
        (by simp only [codeMentions]; exact hmy.1)
        (by simp only [codeDeclares]; exact hdx.1)
      obtain ⟨Vs₁, rfl, hslotS⟩ := hrs.sres_right
      obtain ⟨rr, hsr, hrr⟩ := ihrest hslotS hxy
        (by simp only [codeMentions]; exact hmy.2)
        (by simp only [codeDeclares]; exact hdx.2)
      obtain ⟨Vr₁, rfl, hslotR⟩ := hrr.sres_right
      refine ⟨.sres Vr₁ str o, ?_, ⟨hslotR, rfl, rfl⟩⟩
      simpa [renameCode, renameStmts] using Step.seqCons hss hsr
  | @seqStop funs V st s rest Vs sts o hstmt hne ihstmt =>
      intro d dx x y V₁ hslot hxy hmy hdx
      simp only [codeMentions, stmtsMentions, Bool.or_eq_false_iff] at hmy
      simp only [codeDeclares, stmtsDeclare, Bool.or_eq_false_iff] at hdx
      obtain ⟨rs, hss, hrs⟩ := ihstmt hslot hxy
        (by simp only [codeMentions]; exact hmy.1)
        (by simp only [codeDeclares]; exact hdx.1)
      obtain ⟨Vs₁, rfl, hslotS⟩ := hrs.sres_right
      refine ⟨.sres Vs₁ sts o, ?_, ⟨hslotS, rfl, rfl⟩⟩
      simpa [renameCode, renameStmts] using Step.seqStop hss hne
  | @loopDone funs V st c post body cv st₁ hc hz ihc =>
      intro d dx x y V₁ hslot hxy hmy hdx
      simp only [codeMentions, Bool.or_eq_false_iff] at hmy
      obtain ⟨rc, hsc, hrc⟩ := ihc hslot hxy
        (by simp only [codeMentions]; exact hmy.1.1) rfl
      obtain rfl := hrc.eres_right
      refine ⟨.sres V₁ st₁ .normal, ?_, ⟨hslot, rfl, rfl⟩⟩
      simpa [renameCode] using Step.loopDone hsc hz
  | @loopCondHalt funs V st c post body st₁ hc ihc =>
      intro d dx x y V₁ hslot hxy hmy hdx
      simp only [codeMentions, Bool.or_eq_false_iff] at hmy
      obtain ⟨rc, hsc, hrc⟩ := ihc hslot hxy
        (by simp only [codeMentions]; exact hmy.1.1) rfl
      obtain rfl := hrc.eres_right
      refine ⟨.sres V₁ st₁ .halt, ?_, ⟨hslot, rfl, rfl⟩⟩
      simpa [renameCode] using Step.loopCondHalt hsc
  | @loopStep funs V st c post body cv st₁ Vb stb ob Vp stp Vend stend o
      hc hnz hbody hob hpost hrec ihc ihbody ihpost ihrec =>
      intro d dx x y V₁ hslot hxy hmy hdx
      simp only [codeMentions, Bool.or_eq_false_iff] at hmy
      simp only [codeDeclares, Bool.or_eq_false_iff] at hdx
      obtain ⟨⟨hcY, hpostY⟩, hbodyY⟩ := hmy
      obtain ⟨hpostX, hbodyX⟩ := hdx
      obtain ⟨rc, hsc, hrc⟩ := ihc hslot hxy
        (by simp only [codeMentions]; exact hcY) rfl
      obtain rfl := hrc.eres_right
      obtain ⟨rb, hsb, hrb⟩ := ihbody hslot hxy
        (by simp only [codeMentions, stmtMentions]; exact hbodyY)
        (by simp only [codeDeclares, stmtDeclares]; exact hbodyX)
      obtain ⟨Vb₁, rfl, hslotB⟩ := hrb.sres_right
      obtain ⟨rp, hsp, hrp⟩ := ihpost hslotB hxy
        (by simp only [codeMentions, stmtMentions]; exact hpostY)
        (by simp only [codeDeclares, stmtDeclares]; exact hpostX)
      obtain ⟨Vp₁, rfl, hslotP⟩ := hrp.sres_right
      obtain ⟨rr, hsr, hrr⟩ := ihrec hslotP hxy
        (by simp only [codeMentions, hcY, hpostY, hbodyY, Bool.or_false])
        (by simp only [codeDeclares, hpostX, hbodyX, Bool.or_false])
      obtain ⟨Ve₁, rfl, hslotE⟩ := hrr.sres_right
      have hsb' : Step D funs V₁ st₁
          (.stmt (.block (renameStmts [(x, y)] body))) (.sres Vb₁ stb ob) := by
        simpa [renameCode, renameStmt] using hsb
      have hsp' : Step D funs Vb₁ stb
          (.stmt (.block (renameStmts [(x, y)] post))) (.sres Vp₁ stp .normal) := by
        simpa [renameCode, renameStmt] using hsp
      refine ⟨.sres Ve₁ stend o, ?_, ⟨hslotE, rfl, rfl⟩⟩
      simpa [renameCode] using Step.loopStep hsc hnz hsb' hob hsp' hsr
  | @loopPostHalt funs V st c post body cv st₁ Vb stb ob Vp stp
      hc hnz hbody hob hpost ihc ihbody ihpost =>
      intro d dx x y V₁ hslot hxy hmy hdx
      simp only [codeMentions, Bool.or_eq_false_iff] at hmy
      simp only [codeDeclares, Bool.or_eq_false_iff] at hdx
      obtain ⟨⟨hcY, hpostY⟩, hbodyY⟩ := hmy
      obtain ⟨hpostX, hbodyX⟩ := hdx
      obtain ⟨rc, hsc, hrc⟩ := ihc hslot hxy
        (by simp only [codeMentions]; exact hcY) rfl
      obtain rfl := hrc.eres_right
      obtain ⟨rb, hsb, hrb⟩ := ihbody hslot hxy
        (by simp only [codeMentions, stmtMentions]; exact hbodyY)
        (by simp only [codeDeclares, stmtDeclares]; exact hbodyX)
      obtain ⟨Vb₁, rfl, hslotB⟩ := hrb.sres_right
      obtain ⟨rp, hsp, hrp⟩ := ihpost hslotB hxy
        (by simp only [codeMentions, stmtMentions]; exact hpostY)
        (by simp only [codeDeclares, stmtDeclares]; exact hpostX)
      obtain ⟨Vp₁, rfl, hslotP⟩ := hrp.sres_right
      have hsb' : Step D funs V₁ st₁
          (.stmt (.block (renameStmts [(x, y)] body))) (.sres Vb₁ stb ob) := by
        simpa [renameCode, renameStmt] using hsb
      have hsp' : Step D funs Vb₁ stb
          (.stmt (.block (renameStmts [(x, y)] post))) (.sres Vp₁ stp .halt) := by
        simpa [renameCode, renameStmt] using hsp
      refine ⟨.sres Vp₁ stp .halt, ?_, ⟨hslotP, rfl, rfl⟩⟩
      simpa [renameCode] using Step.loopPostHalt hsc hnz hsb' hob hsp'
  | @loopBreak funs V st c post body cv st₁ Vb stb hc hnz hbody ihc ihbody =>
      intro d dx x y V₁ hslot hxy hmy hdx
      simp only [codeMentions, Bool.or_eq_false_iff] at hmy
      simp only [codeDeclares, Bool.or_eq_false_iff] at hdx
      obtain ⟨⟨hcY, hpostY⟩, hbodyY⟩ := hmy
      obtain ⟨hpostX, hbodyX⟩ := hdx
      obtain ⟨rc, hsc, hrc⟩ := ihc hslot hxy
        (by simp only [codeMentions]; exact hcY) rfl
      obtain rfl := hrc.eres_right
      obtain ⟨rb, hsb, hrb⟩ := ihbody hslot hxy
        (by simp only [codeMentions, stmtMentions]; exact hbodyY)
        (by simp only [codeDeclares, stmtDeclares]; exact hbodyX)
      obtain ⟨Vb₁, rfl, hslotB⟩ := hrb.sres_right
      have hsb' : Step D funs V₁ st₁
          (.stmt (.block (renameStmts [(x, y)] body))) (.sres Vb₁ stb .«break») := by
        simpa [renameCode, renameStmt] using hsb
      refine ⟨.sres Vb₁ stb .normal, ?_, ⟨hslotB, rfl, rfl⟩⟩
      simpa [renameCode] using Step.loopBreak hsc hnz hsb'
  | @loopLeave funs V st c post body cv st₁ Vb stb hc hnz hbody ihc ihbody =>
      intro d dx x y V₁ hslot hxy hmy hdx
      simp only [codeMentions, Bool.or_eq_false_iff] at hmy
      simp only [codeDeclares, Bool.or_eq_false_iff] at hdx
      obtain ⟨⟨hcY, hpostY⟩, hbodyY⟩ := hmy
      obtain ⟨hpostX, hbodyX⟩ := hdx
      obtain ⟨rc, hsc, hrc⟩ := ihc hslot hxy
        (by simp only [codeMentions]; exact hcY) rfl
      obtain rfl := hrc.eres_right
      obtain ⟨rb, hsb, hrb⟩ := ihbody hslot hxy
        (by simp only [codeMentions, stmtMentions]; exact hbodyY)
        (by simp only [codeDeclares, stmtDeclares]; exact hbodyX)
      obtain ⟨Vb₁, rfl, hslotB⟩ := hrb.sres_right
      have hsb' : Step D funs V₁ st₁
          (.stmt (.block (renameStmts [(x, y)] body))) (.sres Vb₁ stb .leave) := by
        simpa [renameCode, renameStmt] using hsb
      refine ⟨.sres Vb₁ stb .leave, ?_, ⟨hslotB, rfl, rfl⟩⟩
      simpa [renameCode] using Step.loopLeave hsc hnz hsb'
  | @loopBodyHalt funs V st c post body cv st₁ Vb stb hc hnz hbody ihc ihbody =>
      intro d dx x y V₁ hslot hxy hmy hdx
      simp only [codeMentions, Bool.or_eq_false_iff] at hmy
      simp only [codeDeclares, Bool.or_eq_false_iff] at hdx
      obtain ⟨⟨hcY, hpostY⟩, hbodyY⟩ := hmy
      obtain ⟨hpostX, hbodyX⟩ := hdx
      obtain ⟨rc, hsc, hrc⟩ := ihc hslot hxy
        (by simp only [codeMentions]; exact hcY) rfl
      obtain rfl := hrc.eres_right
      obtain ⟨rb, hsb, hrb⟩ := ihbody hslot hxy
        (by simp only [codeMentions, stmtMentions]; exact hbodyY)
        (by simp only [codeDeclares, stmtDeclares]; exact hbodyX)
      obtain ⟨Vb₁, rfl, hslotB⟩ := hrb.sres_right
      have hsb' : Step D funs V₁ st₁
          (.stmt (.block (renameStmts [(x, y)] body))) (.sres Vb₁ stb .halt) := by
        simpa [renameCode, renameStmt] using hsb
      refine ⟨.sres Vb₁ stb .halt, ?_, ⟨hslotB, rfl, rfl⟩⟩
      simpa [renameCode] using Step.loopBodyHalt hsc hnz hsb'

/-! ## One coalescing site -/

/-- Replacing one local binding by an assignment into an earlier dead local is
pointwise block-equivalent. The common prefix establishes ownership of the
reused slot; block restoration erases both internal layouts. -/
theorem reuseSlot_equivBlock {pre rest : Block Op} {x y : Ident}
    {val : Option (Expr Op)}
    (howned : x ∈ stmtsBinds pre) (hxy : x ≠ y)
    (hmx : stmtsMentions x rest = false)
    (hdy : stmtsDeclare y rest = false)
    (hfy : stmtsFunMention y rest = false) :
    EquivBlock D (pre ++ .letDecl [y] val :: rest)
      (pre ++ .assign [x] (val.getD (.lit (.number 0))) ::
        renameStmts [(y, x)] rest) := by
  have hh : hoist D (pre ++ .letDecl [y] val :: rest) =
      hoist D (pre ++ .assign [x] (val.getD (.lit (.number 0))) ::
        renameStmts [(y, x)] rest) := by
    simp only [hoist_append]
    have htail : hoist D rest = hoist D (renameStmts [(y, x)] rest) :=
      (hoist_renameStmts (calls := calls) (creates := creates) [(y, x)] rest).symm
    simpa [hoist] using congrArg (fun tail => hoist D pre ++ tail) htail
  intro funs V st V' st' o
  constructor
  · intro hrun
    cases hrun with
    | block hb =>
      rw [hh] at hb
      rcases stmts_append_fwd hb with ⟨Vp, stp, hpre, hsuf⟩ | ⟨hne, hpre⟩
      · obtain ⟨dx, hxlocal, hxbase⟩ := localAt_of_stmtsBind hpre howned
        cases hsuf with
        | seqCons hlet hrest =>
          cases hlet with
          | letZero =>
            have hslot := SlotRel.initial (y := y)
              (value := (evmWithExternal calls creates).zero) hxlocal
            obtain ⟨rt, htarget, hrel⟩ := slot_fwd hrest hslot
              (by simpa [codeMentions] using hmx)
              (by simpa [codeDeclares] using hdy)
            obtain ⟨Vt, rfl, hslot'⟩ := hrel.sres
            have hassign : Step D (hoist D (pre ++
                .assign [x] (.lit (.number 0)) :: renameStmts [(y, x)] rest) :: funs)
                Vp stp (.stmt (.assign [x] (.lit (.number 0))))
                (.sres (VEnv.set Vp x (evmWithExternal calls creates).zero)
                  stp .normal) :=
              Step.assignVal Step.lit rfl
            have hjoin := stmts_append_normal hpre
              (Step.seqCons hassign htarget)
            have hr := hslot'.restore_eq hxbase
            rw [hr]
            exact Step.block hjoin
          | @letVal _ _ _ _ _ values _ hexpr hlen =>
            cases values with
            | nil => simp at hlen
            | cons value values =>
              cases values with
              | nil =>
                have hslot := SlotRel.initial (y := y) (value := value) hxlocal
                obtain ⟨rt, htarget, hrel⟩ := slot_fwd hrest hslot
                  (by simpa [codeMentions] using hmx)
                  (by simpa [codeDeclares] using hdy)
                obtain ⟨Vt, rfl, hslot'⟩ := hrel.sres
                have hassign := Step.assignVal (vars := [x]) hexpr (by simpa using hlen)
                have hjoin := stmts_append_normal hpre
                  (Step.seqCons hassign htarget)
                have hr := hslot'.restore_eq hxbase
                rw [hr]
                exact Step.block hjoin
              | cons value' values => simp at hlen
        | seqStop hlet hne =>
          cases hlet with
          | letZero => exact absurd rfl hne
          | letVal _ _ => exact absurd rfl hne
          | letHalt hexpr =>
            exact Step.block (stmts_append_normal hpre
              (Step.seqStop (Step.assignHalt hexpr) hne))
      · exact Step.block (stmts_append_early hpre hne)
  · intro hrun
    cases hrun with
    | block hb =>
      rw [← hh] at hb
      rcases stmts_append_fwd hb with ⟨Vp, stp, hpre, hsuf⟩ | ⟨hne, hpre⟩
      · obtain ⟨dx, hxlocal, hxbase⟩ := localAt_of_stmtsBind hpre howned
        have htargetMentions : stmtsMentions y (renameStmts [(y, x)] rest) = false :=
          renameStmts_no_target hxy hmx hdy hfy
        have htargetDeclares : stmtsDeclare x (renameStmts [(y, x)] rest) = false := by
          rw [stmtsDeclare_rename]
          exact stmtsDeclare_false_of_mentions x rest hmx
        cases hsuf with
        | seqCons hassign hrest =>
          cases hassign with
          | @assignVal _ _ _ _ _ values _ hexpr hlen =>
            cases values with
            | nil => simp at hlen
            | cons value values =>
              cases values with
              | nil =>
                have hslot := SlotRel.initial (y := y) (value := value) hxlocal
                obtain ⟨rs, hsource, hrel⟩ := slot_rev_fwd hrest hslot hxy
                  (by simpa [codeMentions] using htargetMentions)
                  (by simpa [codeDeclares] using htargetDeclares)
                obtain ⟨Vs, rfl, hslot'⟩ := hrel.sres_right
                simp only [renameCode] at hsource
                rw [renameStmts_inverse hxy hmx] at hsource
                cases val with
                | none =>
                  cases hexpr
                  have hlet : Step D (hoist D (pre ++ .letDecl [y] none :: rest) :: funs)
                      Vp stp (.stmt (.letDecl [y] none))
                      (.sres ((y, (evmWithExternal calls creates).zero) :: Vp)
                        stp .normal) := Step.letZero
                  have hjoin := stmts_append_normal hpre (Step.seqCons hlet hsource)
                  have hr := hslot'.restore_eq hxbase
                  rw [← hr]
                  exact Step.block hjoin
                | some e0 =>
                  have hlet : Step D (hoist D (pre ++ .letDecl [y] (some e0) :: rest) :: funs)
                      Vp stp (.stmt (.letDecl [y] (some e0)))
                      (.sres ((y, value) :: Vp) _ .normal) :=
                    Step.letVal hexpr (by simpa using hlen)
                  have hjoin := stmts_append_normal hpre (Step.seqCons hlet hsource)
                  have hr := hslot'.restore_eq hxbase
                  rw [← hr]
                  exact Step.block hjoin
              | cons value' values => simp at hlen
        | seqStop hassign hne =>
          cases hassign with
          | assignVal _ _ => exact absurd rfl hne
          | assignHalt hexpr =>
            cases val with
            | none => cases hexpr
            | some e =>
              exact Step.block (stmts_append_normal hpre
                (Step.seqStop (Step.letHalt hexpr) hne))
      · exact Step.block (stmts_append_early hpre hne)

/-- Facts certified by a successful liveness/slot-choice query. -/
theorem reusableSlot_inv {layout owned : List Ident} {y x : Ident}
    {e : Expr Op} {rest : Block Op}
    (h : reusableSlot layout owned y e rest = some x) :
    x ∈ owned ∧ x ≠ y ∧ stmtsMentions x rest = false ∧
      stmtsDeclare y rest = false ∧ stmtsFunMention y rest = false := by
  unfold reusableSlot at h
  have hxmem : x ∈ owned := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  split at hp
  · simp only [Bool.and_eq_true] at hp
    rcases hp with ⟨⟨⟨⟨⟨hdepth, hxy⟩, hyLayout⟩, hmx⟩, hdy⟩, hfy⟩
    exact ⟨hxmem, by simpa using hxy, by simpa using hmx,
      by simpa using hdy, by simpa using hfy⟩
  · contradiction

theorem stmtsBinds_append (a b : Block Op) :
    stmtsBinds (a ++ b) = stmtsBinds b ++ stmtsBinds a := by
  induction a with
  | nil => simp [stmtsBinds]
  | cons s rest ih => simp [stmtsBinds, ih, List.append_assoc]

private theorem forall₂_refl_equivStmt (ss : Block Op) :
    List.Forall₂ (EquivStmt D) ss ss := by
  induction ss with
  | nil => exact .nil
  | cons s rest ih => exact .cons (fun _ _ _ _ _ _ => Iff.rfl) ih

private theorem forall₂_refl_cases (cases : List (Literal × Block Op)) :
    List.Forall₂ (fun p q => p.1 = q.1 ∧ EquivBlock D p.2 q.2) cases cases := by
  induction cases with
  | nil => exact .nil
  | cons p rest ih => exact .cons ⟨rfl, EquivBlock.refl _⟩ ih

private theorem scopeRel_append' {a b c d : FScope D}
    (h₁ : ScopeRel D a b) (h₂ : ScopeRel D c d) :
    ScopeRel D (a ++ c) (b ++ d) := by
  induction h₁ with
  | nil => exact h₂
  | cons hp _ ih => exact .cons hp ih

private theorem forall₂_append_equivStmt {a b c d : Block Op}
    (h₁ : List.Forall₂ (EquivStmt D) a b)
    (h₂ : List.Forall₂ (EquivStmt D) c d) :
    List.Forall₂ (EquivStmt D) (a ++ c) (b ++ d) := by
  induction h₁ with
  | nil => exact h₂
  | cons hp _ ih => exact .cons hp ih

theorem replaceStmt_equivBlock {s s' : Stmt Op} {rest : Block Op}
    (hs : EquivStmt D s s')
    (hscope : ScopeRel D (hoist D [s]) (hoist D [s']))
    (pre : Block Op) :
    EquivBlock D (pre ++ s :: rest) (pre ++ s' :: rest) := by
  refine EquivBlock.of_stmts_funs
    (EquivStmts.of_forall₂ (forall₂_append_equivStmt
      (forall₂_refl_equivStmt pre)
      (.cons hs (forall₂_refl_equivStmt rest)))) ?_
  rw [show (s :: rest) = [s] ++ rest from rfl,
      show (s' :: rest) = [s'] ++ rest from rfl,
      hoist_append, hoist_append, hoist_append, hoist_append]
  exact scopeRel_append' (ScopeRel.refl _)
    (scopeRel_append' hscope (ScopeRel.refl _))

mutual
  theorem stageOneStmt_sound : ∀ (P : String) (Phi : FMap)
      (layout : List Ident) (s s' : Stmt Op),
      stageOneStmt P Phi layout s = some s' →
      EquivStmt D s s' ∧ ScopeRel D (hoist D [s]) (hoist D [s'])
    | P, Phi, layout, .assign xs (.call f args), s', h => by
        unfold stageOneStmt at h
        dsimp only at h
        split at h
        · next hw =>
          cases h
          exact ⟨stageWanted_equiv (calls := calls) (creates := creates) hw,
            ScopeRel.refl _⟩
        · simp at h
    | _, _, _, .assign _ (.lit _), _, h => by simp [stageOneStmt] at h
    | _, _, _, .assign _ (.var _), _, h => by simp [stageOneStmt] at h
    | _, _, _, .assign _ (.builtin _ _), _, h => by simp [stageOneStmt] at h
    | P, Phi, layout, .block body, s', h => by
        simp only [stageOneStmt] at h
        obtain ⟨body', hb, hs'⟩ := Option.map_eq_some_iff.mp h
        subst s'
        exact ⟨stageOneStmts_sound P Phi layout body _ hb [], ScopeRel.refl _⟩
    | P, Phi, layout, .funDef f ps rs body, s', h => by
        simp only [stageOneStmt] at h
        obtain ⟨body', hb, hs'⟩ := Option.map_eq_some_iff.mp h
        subst s'
        have heq := stageOneStmts_sound P Phi (ps ++ rs) body _ hb []
        refine ⟨funDef_equiv f ps rs body body', ?_⟩
        exact .cons ⟨rfl, rfl, rfl, heq⟩ .nil
    | P, Phi, layout, .cond c body, s', h => by
        simp only [stageOneStmt] at h
        obtain ⟨body', hb, hs'⟩ := Option.map_eq_some_iff.mp h
        subst s'
        exact ⟨EquivStmt.cond_congr (fun _ _ _ _ => Iff.rfl)
          (stageOneStmts_sound P Phi layout body _ hb []), ScopeRel.refl _⟩
    | P, Phi, layout, .switch c cases dflt, s', h => by
        unfold stageOneStmt at h
        cases hc : stageOneCases P Phi layout cases with
        | some cases' =>
          simp only [hc] at h
          cases h
          exact ⟨EquivStmt.switch_congr (fun _ _ _ _ => Iff.rfl)
            (stageOneCases_sound P Phi layout cases _ hc) (EquivBlock.refl _),
            ScopeRel.refl _⟩
        | none =>
          simp only [hc] at h
          cases dflt with
          | none => simp at h
          | some body =>
            obtain ⟨body', hb, hs'⟩ := Option.map_eq_some_iff.mp h
            subst s'
            exact ⟨EquivStmt.switch_congr (fun _ _ _ _ => Iff.rfl)
              (forall₂_refl_cases cases)
              (stageOneStmts_sound P Phi layout body _ hb []), ScopeRel.refl _⟩
    | P, Phi, layout, .forLoop init c post body, s', h => by
        unfold stageOneStmt at h
        let Phi' : FMap := (hoistInfos 0 init).1 :: Phi
        let loopLayout := layoutAfter layout init
        change (match stageOneStmts P Phi' loopLayout post with
          | some post' => some (.forLoop init c post' body)
          | none => (.forLoop init c post ·) <$>
              stageOneStmts P Phi' loopLayout body) = some s' at h
        cases hp : stageOneStmts P Phi' loopLayout post with
        | some post' =>
          simp only [hp] at h
          cases h
          exact ⟨EquivStmt.forLoop_congr init (fun _ _ _ _ => Iff.rfl)
            (stageOneStmts_sound P Phi' loopLayout post _ hp [])
            (EquivBlock.refl _), ScopeRel.refl _⟩
        | none =>
          simp only [hp] at h
          obtain ⟨body', hb, hs'⟩ := Option.map_eq_some_iff.mp h
          subst s'
          exact ⟨EquivStmt.forLoop_congr init (fun _ _ _ _ => Iff.rfl)
            (EquivBlock.refl _)
            (stageOneStmts_sound P Phi' loopLayout body _ hb []),
            ScopeRel.refl _⟩
    | _, _, _, .letDecl _ _, _, h => by simp [stageOneStmt] at h
    | _, _, _, .exprStmt _, _, h => by simp [stageOneStmt] at h
    | _, _, _, .break, _, h => by simp [stageOneStmt] at h
    | _, _, _, .continue, _, h => by simp [stageOneStmt] at h
    | _, _, _, .leave, _, h => by simp [stageOneStmt] at h
    termination_by P Phi layout s s' _h => 2 * sizeOf s

  theorem stageOneStmts_sound : ∀ (P : String) (Phi : FMap)
      (layout : List Ident) (ss ss' : Block Op),
      stageOneStmts P Phi layout ss = some ss' →
      ∀ pre : Block Op, EquivBlock D (pre ++ ss) (pre ++ ss')
    | _, _, _, [], _, h => by simp [stageOneStmts] at h
    | P, Phi, layout, s :: rest, ss', h => by
        unfold stageOneStmts at h
        cases hs : stageOneStmt P Phi layout s with
        | some s' =>
          simp only [hs] at h
          cases h
          intro pre
          obtain ⟨heq, hscope⟩ := stageOneStmt_sound P Phi layout s s' hs
          exact replaceStmt_equivBlock heq hscope pre
        | none =>
          simp only [hs] at h
          let layout' := match s with
            | .letDecl xs _ => xs ++ layout
            | _ => layout
          obtain ⟨rest', hr, htarget⟩ := Option.map_eq_some_iff.mp h
          subst ss'
          intro pre
          have heq := stageOneStmts_sound P Phi layout' rest rest' hr (pre ++ [s])
          simpa only [List.append_assoc, List.cons_append, List.nil_append]
            using heq
    termination_by P Phi layout ss ss' _h => 2 * sizeOf ss + 1

  theorem stageOneCases_sound : ∀ (P : String) (Phi : FMap)
      (layout : List Ident) (cases cases' : List (Literal × Block Op)),
      stageOneCases P Phi layout cases = some cases' →
      List.Forall₂ (fun p q => p.1 = q.1 ∧ EquivBlock D p.2 q.2) cases cases'
    | _, _, _, [], _, h => by simp [stageOneCases] at h
    | P, Phi, layout, (l, body) :: rest, cases', h => by
        unfold stageOneCases at h
        split at h
        · next body' hb =>
          cases h
          exact .cons ⟨rfl, stageOneStmts_sound P Phi layout body _ hb []⟩
            (forall₂_refl_cases rest)
        · obtain ⟨rest', hr, hs'⟩ := Option.map_eq_some_iff.mp h
          subst cases'
          exact .cons ⟨rfl, EquivBlock.refl _⟩
            (stageOneCases_sound P Phi layout rest _ hr)
    termination_by P Phi layout cases cases' _h => 2 * sizeOf cases + 1
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

theorem stageOneStmts_equiv {P : String} {Phi : FMap} {b b' : Block Op}
    (h : stageOneStmts P Phi [] b = some b') : EquivBlock D b b' := by
  simpa using stageOneStmts_sound P Phi [] b b' h []

theorem iterateStageWith_equiv (n : Nat) (P : String) (Phi : FMap)
    (b : Block Op) : EquivBlock D b (iterateStageWith n P Phi b) := by
  induction n generalizing b with
  | zero => exact EquivBlock.refl _
  | succ n ih =>
      rw [iterateStageWith]
      cases h : stageOneStmts P Phi [] b with
      | none => exact EquivBlock.refl _
      | some b' => exact (stageOneStmts_equiv h).trans (ih b')

theorem iterateStageCalls_equiv (n : Nat) (P : String) (b : Block Op) :
    EquivBlock D b (iterateStageCalls n P b) := by
  unfold iterateStageCalls
  exact iterateStageWith_equiv n P [(hoistInfos 0 b).1] b

theorem stageCallsBlock_equiv (b : Block Op) :
    EquivBlock D b (stageCallsBlock b) := by
  unfold stageCallsBlock
  split
  · exact iterateStageCalls_equiv 16384 _ b
  · exact EquivBlock.refl _

mutual
  theorem copyOneStmt_sound : ∀ (layout : List Ident) (s s' : Stmt Op),
      copyOneStmt layout s = some s' →
      EquivStmt D s s' ∧ ScopeRel D (hoist D [s]) (hoist D [s'])
    | layout, .block body, s', h => by
        simp only [copyOneStmt] at h
        obtain ⟨body', hb, hs'⟩ := Option.map_eq_some_iff.mp h
        subst s'
        exact ⟨copyOneStmts_sound layout body _ hb [], ScopeRel.refl _⟩
    | layout, .funDef f ps rs body, s', h => by
        simp only [copyOneStmt] at h
        obtain ⟨body', hb, hs'⟩ := Option.map_eq_some_iff.mp h
        subst s'
        have heq := copyOneStmts_sound (ps ++ rs) body _ hb []
        refine ⟨funDef_equiv f ps rs body body', ?_⟩
        exact .cons ⟨rfl, rfl, rfl, heq⟩ .nil
    | layout, .cond c body, s', h => by
        simp only [copyOneStmt] at h
        obtain ⟨body', hb, hs'⟩ := Option.map_eq_some_iff.mp h
        subst s'
        exact ⟨EquivStmt.cond_congr (fun _ _ _ _ => Iff.rfl)
          (copyOneStmts_sound layout body _ hb []), ScopeRel.refl _⟩
    | layout, .switch c cases dflt, s', h => by
        unfold copyOneStmt at h
        cases hc : copyOneCases layout cases with
        | some cases' =>
          simp only [hc] at h
          cases h
          exact ⟨EquivStmt.switch_congr (fun _ _ _ _ => Iff.rfl)
            (copyOneCases_sound layout cases _ hc) (EquivBlock.refl _),
            ScopeRel.refl _⟩
        | none =>
          simp only [hc] at h
          cases dflt with
          | none => simp at h
          | some body =>
            obtain ⟨body', hb, hs'⟩ := Option.map_eq_some_iff.mp h
            subst s'
            exact ⟨EquivStmt.switch_congr (fun _ _ _ _ => Iff.rfl)
              (forall₂_refl_cases cases)
              (copyOneStmts_sound layout body _ hb []), ScopeRel.refl _⟩
    | layout, .forLoop init c post body, s', h => by
        unfold copyOneStmt at h
        change (match copyOneStmts (layoutAfter layout init) post with
          | some post' => some (.forLoop init c post' body)
          | none => (.forLoop init c post ·) <$>
              copyOneStmts (layoutAfter layout init) body) = some s' at h
        cases hp : copyOneStmts (layoutAfter layout init) post with
        | some post' =>
          simp only [hp] at h
          cases h
          exact ⟨EquivStmt.forLoop_congr init (fun _ _ _ _ => Iff.rfl)
            (copyOneStmts_sound (layoutAfter layout init) post _ hp [])
            (EquivBlock.refl _),
            ScopeRel.refl _⟩
        | none =>
          simp only [hp] at h
          obtain ⟨body', hb, hs'⟩ := Option.map_eq_some_iff.mp h
          subst s'
          exact ⟨EquivStmt.forLoop_congr init (fun _ _ _ _ => Iff.rfl)
            (EquivBlock.refl _)
            (copyOneStmts_sound (layoutAfter layout init) body _ hb []),
            ScopeRel.refl _⟩
    | _, .letDecl _ _, _, h => by simp [copyOneStmt] at h
    | _, .assign _ _, _, h => by simp [copyOneStmt] at h
    | _, .exprStmt _, _, h => by simp [copyOneStmt] at h
    | _, .break, _, h => by simp [copyOneStmt] at h
    | _, .continue, _, h => by simp [copyOneStmt] at h
    | _, .leave, _, h => by simp [copyOneStmt] at h
    termination_by layout s s' _h => 2 * sizeOf s

  theorem copyOneStmts_sound : ∀ (layout : List Ident) (ss ss' : Block Op),
      copyOneStmts layout ss = some ss' →
      ∀ pre : Block Op, EquivBlock D (pre ++ ss) (pre ++ ss')
    | layout, ss, ss', h => by
        unfold copyOneStmts at h
        cases ht : copyBackHere layout ss with
        | some target =>
          simp only [ht] at h
          cases h
          exact copyBackHere_sound (calls := calls) (creates := creates) ht
        | none =>
          simp only [ht] at h
          cases ss with
          | nil => simp at h
          | cons s rest =>
            cases hs : copyOneStmt layout s with
            | some s' =>
              simp only [hs] at h
              cases h
              intro pre
              obtain ⟨heq, hscope⟩ := copyOneStmt_sound layout s s' hs
              exact replaceStmt_equivBlock heq hscope pre
            | none =>
              simp only [hs] at h
              let layout' := match s with
                | .letDecl xs _ => xs ++ layout
                | _ => layout
              obtain ⟨rest', hr, htarget⟩ := Option.map_eq_some_iff.mp h
              subst ss'
              intro pre
              have heq := copyOneStmts_sound layout' rest rest' hr (pre ++ [s])
              simpa only [List.append_assoc, List.cons_append, List.nil_append]
                using heq
    termination_by layout ss ss' _h => 2 * sizeOf ss + 1

  theorem copyOneCases_sound : ∀ (layout : List Ident)
      (cases cases' : List (Literal × Block Op)),
      copyOneCases layout cases = some cases' →
      List.Forall₂ (fun p q => p.1 = q.1 ∧ EquivBlock D p.2 q.2) cases cases'
    | _, [], _, h => by simp [copyOneCases] at h
    | layout, (l, body) :: rest, cases', h => by
        unfold copyOneCases at h
        split at h
        · next body' hb =>
          cases h
          exact .cons ⟨rfl, copyOneStmts_sound layout body _ hb []⟩
            (forall₂_refl_cases rest)
        · obtain ⟨rest', hr, hs'⟩ := Option.map_eq_some_iff.mp h
          subst cases'
          exact .cons ⟨rfl, EquivBlock.refl _⟩
            (copyOneCases_sound layout rest _ hr)
    termination_by layout cases cases' _h => 2 * sizeOf cases + 1
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

theorem copyOneStmts_equiv {b b' : Block Op}
    (h : copyOneStmts [] b = some b') : EquivBlock D b b' := by
  simpa using copyOneStmts_sound [] b b' h []

theorem iterateCopyBack_equiv (n : Nat) (b : Block Op) :
    EquivBlock D b (iterateCopyBack n b) := by
  induction n generalizing b with
  | zero => exact EquivBlock.refl _
  | succ n ih =>
      rw [iterateCopyBack]
      cases h : copyOneStmts [] b with
      | none => exact EquivBlock.refl _
      | some b' => exact (copyOneStmts_equiv h).trans (ih b')

mutual
  theorem reuseOneStmt_sound : ∀ (layout : List Ident) (s s' : Stmt Op),
      reuseOneStmt layout s = some s' →
      EquivStmt D s s' ∧ ScopeRel D (hoist D [s]) (hoist D [s'])
    | layout, .block body, s', h => by
        simp only [reuseOneStmt] at h
        obtain ⟨body', hb, hs'⟩ := Option.map_eq_some_iff.mp h
        subst s'
        have heq := reuseOneStmts_sound layout [] body _ hb [] (by simp)
        exact ⟨heq, ScopeRel.refl _⟩
    | layout, .funDef f ps rs body, s', h => by
        simp only [reuseOneStmt] at h
        obtain ⟨body', hb, hs'⟩ := Option.map_eq_some_iff.mp h
        subst s'
        have heq := reuseOneStmts_sound (ps ++ rs) [] body _ hb [] (by simp)
        refine ⟨funDef_equiv f ps rs body body', ?_⟩
        exact .cons ⟨rfl, rfl, rfl, heq⟩ .nil
    | layout, .cond c body, s', h => by
        simp only [reuseOneStmt] at h
        obtain ⟨body', hb, hs'⟩ := Option.map_eq_some_iff.mp h
        subst s'
        have heq := reuseOneStmts_sound layout [] body _ hb [] (by simp)
        exact ⟨EquivStmt.cond_congr (fun _ _ _ _ => Iff.rfl) heq,
          ScopeRel.refl _⟩
    | layout, .switch c cases dflt, s', h => by
        unfold reuseOneStmt at h
        cases hcases : reuseOneCases layout cases with
        | some cases' =>
          simp only [hcases] at h
          cases h
          have hc := reuseOneCases_sound layout cases _ hcases
          exact ⟨EquivStmt.switch_congr (fun _ _ _ _ => Iff.rfl) hc
            (EquivBlock.refl _), ScopeRel.refl _⟩
        | none =>
          simp only [hcases] at h
          cases dflt with
          | none => simp at h
          | some body =>
            cases hb : reuseOneStmts layout [] body with
            | some body' =>
              simp only [hb] at h
              cases h
              have heq := reuseOneStmts_sound layout [] body _ hb [] (by simp)
              exact ⟨EquivStmt.switch_congr (fun _ _ _ _ => Iff.rfl)
                (forall₂_refl_cases cases) heq,
                ScopeRel.refl _⟩
            | none => simp [hb] at h
    | layout, .forLoop init c post body, s', h => by
        unfold reuseOneStmt at h
        cases hp : reuseOneStmts layout [] post with
        | some post' =>
          simp only [hp] at h
          cases h
          have heq := reuseOneStmts_sound layout [] post _ hp [] (by simp)
          exact ⟨EquivStmt.forLoop_congr init (fun _ _ _ _ => Iff.rfl) heq
            (EquivBlock.refl _), ScopeRel.refl _⟩
        | none =>
          simp only [hp] at h
          obtain ⟨body', hb, hs'⟩ := Option.map_eq_some_iff.mp h
          subst s'
          have heq := reuseOneStmts_sound layout [] body _ hb [] (by simp)
          exact ⟨EquivStmt.forLoop_congr init (fun _ _ _ _ => Iff.rfl)
            (EquivBlock.refl _) heq, ScopeRel.refl _⟩
    | _, .letDecl _ _, _, h => by simp [reuseOneStmt] at h
    | _, .assign _ _, _, h => by simp [reuseOneStmt] at h
    | _, .exprStmt _, _, h => by simp [reuseOneStmt] at h
    | _, .break, _, h => by simp [reuseOneStmt] at h
    | _, .continue, _, h => by simp [reuseOneStmt] at h
    | _, .leave, _, h => by simp [reuseOneStmt] at h
    termination_by layout s s' h => 2 * sizeOf s

  theorem reuseOneStmts_sound : ∀ (layout owned : List Ident)
      (ss ss' : Block Op), reuseOneStmts layout owned ss = some ss' →
      ∀ pre : Block Op, (∀ x ∈ owned, x ∈ stmtsBinds pre) →
        EquivBlock D (pre ++ ss) (pre ++ ss')
    | layout, owned, [], ss', h => by simp [reuseOneStmts] at h
    | layout, owned, .letDecl [y] val :: rest, ss', h => by
        rw [reuseOneStmts.eq_2] at h
        cases hx : reusableSlot layout owned y (val.getD (.lit (.number 0))) rest with
        | some x =>
          simp only [hx] at h
          cases h
          intro pre howned
          obtain ⟨hxmem, hxy, hmx, hdy, hfy⟩ := reusableSlot_inv hx
          exact reuseSlot_equivBlock (howned x hxmem) hxy hmx hdy hfy
        | none =>
          simp only [hx] at h
          obtain ⟨rest', hr, hs'⟩ := Option.map_eq_some_iff.mp h
          subst ss'
          intro pre howned
          have hown' : ∀ z ∈ y :: owned,
              z ∈ stmtsBinds (pre ++ [.letDecl [y] val]) := by
            intro z hz
            rw [stmtsBinds_append]
            simp only [stmtsBinds, stmtBinds, List.nil_append, List.mem_append,
              List.mem_singleton]
            simp only [List.mem_cons] at hz
            exact Or.elim hz Or.inl (fun hm => Or.inr (howned z hm))
          convert reuseOneStmts_sound (y :: layout) (y :: owned) rest _ hr
            (pre ++ [.letDecl [y] val]) hown' using 1 <;>
            simp only [List.append_assoc, List.cons_append, List.nil_append]
    | layout, owned, .letDecl [] val :: rest, ss', h => by
        rw [reuseOneStmts.eq_def] at h
        obtain ⟨rest', hr, hs'⟩ := Option.map_eq_some_iff.mp h
        subst ss'
        intro pre howned
        have hown' : ∀ z ∈ ([] : List Ident) ++ owned,
            z ∈ stmtsBinds (pre ++ [.letDecl [] val]) := by
          intro z hz
          rw [stmtsBinds_append]
          simp only [stmtsBinds, stmtBinds, List.nil_append]
          exact howned z hz
        convert reuseOneStmts_sound layout owned rest _ hr
          (pre ++ [.letDecl [] val]) hown'
          using 1 <;> simp only [List.append_assoc, List.cons_append, List.nil_append]
    | layout, owned, .letDecl (a :: b :: ys) val :: rest, ss', h => by
        rw [reuseOneStmts.eq_def] at h
        obtain ⟨rest', hr, hs'⟩ := Option.map_eq_some_iff.mp h
        subst ss'
        intro pre howned
        have hown' : ∀ z ∈ (a :: b :: ys) ++ owned,
            z ∈ stmtsBinds (pre ++ [.letDecl (a :: b :: ys) val]) := by
          intro z hz
          rw [stmtsBinds_append]
          simp only [stmtsBinds, stmtBinds, List.nil_append]
          rcases List.mem_append.mp hz with hz | hz
          · exact List.mem_append_left _ hz
          · exact List.mem_append_right _ (howned z hz)
        convert reuseOneStmts_sound ((a :: b :: ys) ++ layout)
          ((a :: b :: ys) ++ owned) rest _ hr
          (pre ++ [.letDecl (a :: b :: ys) val]) hown' using 1 <;>
          simp only [List.append_assoc, List.cons_append, List.nil_append]
    | layout, owned, (.block body) :: rest, ss', h => by
        rw [reuseOneStmts.eq_def] at h
        apply reuseOneCons_sound (owned := owned) layout rfl
        exact h
    | layout, owned, (.funDef f ps rs body) :: rest, ss', h => by
        rw [reuseOneStmts.eq_def] at h
        apply reuseOneCons_sound (owned := owned) layout rfl
        exact h
    | layout, owned, (.assign vars e) :: rest, ss', h => by
        rw [reuseOneStmts.eq_def] at h
        apply reuseOneCons_sound (owned := owned) layout rfl
        exact h
    | layout, owned, (.cond c body) :: rest, ss', h => by
        rw [reuseOneStmts.eq_def] at h
        apply reuseOneCons_sound (owned := owned) layout rfl
        exact h
    | layout, owned, (.switch c cases dflt) :: rest, ss', h => by
        rw [reuseOneStmts.eq_def] at h
        apply reuseOneCons_sound (owned := owned) layout rfl
        exact h
    | layout, owned, (.forLoop init c post body) :: rest, ss', h => by
        rw [reuseOneStmts.eq_def] at h
        apply reuseOneCons_sound (owned := owned) layout rfl
        exact h
    | layout, owned, (.exprStmt e) :: rest, ss', h => by
        rw [reuseOneStmts.eq_def] at h
        apply reuseOneCons_sound (owned := owned) layout rfl
        exact h
    | layout, owned, .break :: rest, ss', h => by
        rw [reuseOneStmts.eq_def] at h
        apply reuseOneCons_sound (owned := owned) layout rfl
        exact h
    | layout, owned, .continue :: rest, ss', h => by
        rw [reuseOneStmts.eq_def] at h
        apply reuseOneCons_sound (owned := owned) layout rfl
        exact h
    | layout, owned, .leave :: rest, ss', h => by
        rw [reuseOneStmts.eq_def] at h
        apply reuseOneCons_sound (owned := owned) layout rfl
        exact h
    termination_by layout owned ss ss' h => 2 * sizeOf ss + 1

  theorem reuseOneCons_sound (layout : List Ident) {owned : List Ident}
      {s : Stmt Op} {rest ss' : Block Op} (hsbind : stmtBinds s = [])
      (h : (match reuseOneStmt layout s with
        | some s' => some (s' :: rest)
        | none => (s :: ·) <$> reuseOneStmts layout owned rest) = some ss') :
      ∀ pre : Block Op, (∀ x ∈ owned, x ∈ stmtsBinds pre) →
        EquivBlock D (pre ++ s :: rest) (pre ++ ss') := by
    split at h
    · next s' hs =>
      cases h
      intro pre howned
      obtain ⟨heq, hscope⟩ := reuseOneStmt_sound layout s _ hs
      exact replaceStmt_equivBlock heq hscope pre
    · obtain ⟨rest', hr, hs'⟩ := Option.map_eq_some_iff.mp h
      subst ss'
      intro pre howned
      have hown' : ∀ z ∈ owned, z ∈ stmtsBinds (pre ++ [s]) := by
        intro z hz
        rw [stmtsBinds_append]
        simp [stmtsBinds, hsbind, howned z hz]
      convert reuseOneStmts_sound layout owned rest _ hr (pre ++ [s]) hown' using 1 <;>
        simp only [List.append_assoc, List.cons_append, List.nil_append]
    termination_by 2 * sizeOf (s :: rest)

  theorem reuseOneCases_sound : ∀ (layout : List Ident)
      (cases cases' : List (Literal × Block Op)),
      reuseOneCases layout cases = some cases' →
      List.Forall₂ (fun p q => p.1 = q.1 ∧ EquivBlock D p.2 q.2) cases cases'
    | _, [], _, h => by simp [reuseOneCases] at h
    | layout, (l, body) :: rest, cases', h => by
        unfold reuseOneCases at h
        split at h
        · next body' hb =>
          cases h
          exact .cons ⟨rfl, reuseOneStmts_sound layout [] body _ hb [] (by simp)⟩
            (forall₂_refl_cases rest)
        · obtain ⟨rest', hr, hs'⟩ := Option.map_eq_some_iff.mp h
          subst cases'
          exact .cons ⟨rfl, EquivBlock.refl _⟩
            (reuseOneCases_sound layout rest _ hr)
    termination_by layout cases cases' h => 2 * sizeOf cases + 1
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

theorem reuseOneStmts_equiv {b b' : Block Op}
    (h : reuseOneStmts [] [] b = some b') : EquivBlock D b b' := by
  simpa using reuseOneStmts_sound [] [] b b' h [] (by simp)

theorem iterateStackLayout_equiv (n : Nat) (b : Block Op) :
    EquivBlock D b (iterateStackLayout n b) := by
  induction n generalizing b with
  | zero => exact EquivBlock.refl _
  | succ n ih =>
      rw [iterateStackLayout]
      cases h : reuseOneStmts [] [] b with
      | none => exact EquivBlock.refl _
      | some b' => exact (reuseOneStmts_equiv h).trans (ih b')

/-! ## Tail-carrier scope sinking -/

theorem restore_set_commute {base inner : VEnv D} {keys : List Ident}
    {x : Ident} (v : U256)
    (hkeys : inner.map Prod.fst = keys ++ base.map Prod.fst)
    (hx : x ∉ keys) :
    restore base (VEnv.set inner x v) =
      VEnv.set (restore base inner) x v := by
  have hlen : inner.length = keys.length + base.length := by
    have h := congrArg List.length hkeys
    simpa using h
  have hdrop : inner.length - base.length = keys.length := by omega
  let A := inner.take keys.length
  let B := inner.drop keys.length
  have hab : inner = A ++ B := by
    exact (List.take_append_drop keys.length inner).symm
  have hAkeys : A.map Prod.fst = keys := by
    dsimp [A]
    rw [List.map_take, hkeys, List.take_append_of_le_length (Nat.le_refl _)]
    simp
  have hxA : x ∉ A.map Prod.fst := hAkeys ▸ hx
  have hAle : keys.length ≤ inner.length := by omega
  have hAlen : A.length = keys.length := by simp [A, List.length_take, hAle]
  have hBlen : B.length = base.length := by
    simp [B, List.length_drop, hlen]
  rw [hab, VEnv.set_append_not_mem hxA]
  simp only [restore]
  have hsetB : (VEnv.set B x v).length = B.length := VEnv.set_length _ _ _
  rw [show (A ++ B).length - base.length = A.length by simp [hBlen]]
  rw [show (A ++ VEnv.set B x v).length - base.length = A.length by
    simp [hsetB, hBlen]]
  rw [List.drop_left, List.drop_left]

theorem restore_restore {outer base inner : VEnv D}
    (hob : outer.length ≤ base.length) (hbi : base.length ≤ inner.length) :
    restore outer (restore base inner) = restore outer inner := by
  simp only [restore, List.length_drop]
  rw [List.drop_drop]
  have h₁ : inner.length - base.length ≤ inner.length := Nat.sub_le _ _
  have h₂ : inner.length - (inner.length - base.length) = base.length := by omega
  rw [show inner.length - (inner.length - base.length) - outer.length =
      base.length - outer.length by omega]
  congr 1
  omega

theorem restore_erase_head_set {outer tail : VEnv D} {c r : Ident}
    (old value result : U256) (houter : outer.length ≤ tail.length)
    (hcr : c ≠ r) :
    restore outer
        (VEnv.set (VEnv.set ((c, old) :: tail) c value) r result) =
      restore outer (VEnv.set ((c, old) :: tail) r result) := by
  have hc : VEnv.set ((c, old) :: tail) c value = (c, value) :: tail := by
    simp [VEnv.set]
  have hr₁ : VEnv.set ((c, value) :: tail) r result =
      (c, value) :: VEnv.set tail r result := by simp [VEnv.set, hcr]
  have hr₂ : VEnv.set ((c, old) :: tail) r result =
      (c, old) :: VEnv.set tail r result := by simp [VEnv.set, hcr]
  rw [hc, hr₁, hr₂]
  simp only [restore, List.length_cons]
  rw [VEnv.set_length]
  rw [show tail.length + 1 - outer.length =
      (tail.length - outer.length) + 1 by omega]
  rfl

theorem get_set_of_mem {V : VEnv D} {x : Ident} (v : U256)
    (hx : x ∈ V.map Prod.fst) : VEnv.get (VEnv.set V x v) x = some v := by
  induction V with
  | nil => simp at hx
  | cons entry rest ih =>
      obtain ⟨y, old⟩ := entry
      by_cases hy : y = x
      · subst y; simp [VEnv.set, VEnv.get]
      · simp only [List.map_cons, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact absurd rfl hy
        · rw [VEnv.set, if_neg hy]
          unfold VEnv.get at ih ⊢
          rw [List.find?_cons_of_neg (by simpa using hy)]
          exact ih hx

theorem binds_not_mem_of_declare_false (x : Ident) : ∀ mid : Block Op,
    stmtsDeclare x mid = false → x ∉ stmtsBinds mid
  | [], _ => by simp [stmtsBinds]
  | s :: rest, h => by
      simp only [stmtsDeclare, Bool.or_eq_false_iff] at h
      rw [stmtsBinds]
      simp only [List.mem_append, not_or]
      refine ⟨binds_not_mem_of_declare_false x rest h.2, ?_⟩
      cases s <;> simp_all [stmtDeclares, stmtBinds]

inductive EmptyScopeRel : FunEnv D → FunEnv D → Prop
  | refl (funs) : EmptyScopeRel funs funs
  | add (funs) : EmptyScopeRel funs ([] :: funs)
  | drop (funs) : EmptyScopeRel ([] :: funs) funs
  | cons (scope) {funs₁ funs₂} : EmptyScopeRel funs₁ funs₂ →
      EmptyScopeRel (scope :: funs₁) (scope :: funs₂)

theorem EmptyScopeRel.lookup {funs₁ funs₂ : FunEnv D}
    (hrel : EmptyScopeRel funs₁ funs₂) :
    ∀ {fn decl cenv₁}, lookupFun funs₁ fn = some (decl, cenv₁) →
      ∃ cenv₂, lookupFun funs₂ fn = some (decl, cenv₂) ∧
        EmptyScopeRel cenv₁ cenv₂ := by
  induction hrel with
  | refl funs =>
      intro fn decl cenv h
      exact ⟨cenv, h, .refl _⟩
  | add funs =>
      intro fn decl cenv h
      exact ⟨cenv, by simpa [lookupFun] using h, .refl _⟩
  | drop funs =>
      intro fn decl cenv h
      exact ⟨cenv, by simpa [lookupFun] using h, .refl _⟩
  | @cons scope funs₁ funs₂ hrel ih =>
      intro fn decl cenv₁ h
      cases hs : scope.find? (fun p => p.1 = fn) with
      | some p =>
          rw [lookupFun, hs] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨scope :: funs₂, by rw [lookupFun, hs], .cons _ hrel⟩
      | none =>
          rw [lookupFun, hs] at h
          obtain ⟨cenv₂, hout, hc⟩ := ih h
          exact ⟨cenv₂, by rw [lookupFun, hs]; exact hout, hc⟩

theorem Step.emptyScope_congr {funs₁ : FunEnv D} {V st code res}
    (h : Step D funs₁ V st code res) :
    ∀ {funs₂}, EmptyScopeRel funs₁ funs₂ → Step D funs₂ V st code res := by
  induction h with
  | lit => intro _ _; exact Step.lit
  | var hv => intro _ _; exact Step.var hv
  | builtinOk _ hb iha => intro _ hr; exact Step.builtinOk (iha hr) hb
  | builtinHalt _ hb iha => intro _ hr; exact Step.builtinHalt (iha hr) hb
  | builtinArgsHalt _ iha => intro _ hr; exact Step.builtinArgsHalt (iha hr)
  | @callOk funs V st fn args argvals st1 decl cenv Vend st2 o ha hl hlen hbody ho iha ihbody =>
      intro funs₂ hr
      obtain ⟨cenv₂, hl₂, hc⟩ := hr.lookup hl
      exact Step.callOk (iha hr) hl₂ hlen (ihbody hc) ho
  | @callHalt funs V st fn args argvals st1 decl cenv Vend st2 ha hl hlen hbody iha ihbody =>
      intro funs₂ hr
      obtain ⟨cenv₂, hl₂, hc⟩ := hr.lookup hl
      exact Step.callHalt (iha hr) hl₂ hlen (ihbody hc)
  | callArgsHalt _ iha => intro _ hr; exact Step.callArgsHalt (iha hr)
  | argsNil => intro _ _; exact Step.argsNil
  | argsCons _ _ iha ihe => intro _ hr; exact Step.argsCons (iha hr) (ihe hr)
  | argsRestHalt _ iha => intro _ hr; exact Step.argsRestHalt (iha hr)
  | argsHeadHalt _ _ iha ihe => intro _ hr; exact Step.argsHeadHalt (iha hr) (ihe hr)
  | funDef => intro _ _; exact Step.funDef
  | @block funs V st body Vb stb o hbody ihbody =>
      intro funs₂ hr; exact Step.block (ihbody (.cons _ hr))
  | letZero => intro _ _; exact Step.letZero
  | letVal _ hlen ihe => intro _ hr; exact Step.letVal (ihe hr) hlen
  | letHalt _ ihe => intro _ hr; exact Step.letHalt (ihe hr)
  | assignVal _ hlen ihe => intro _ hr; exact Step.assignVal (ihe hr) hlen
  | assignHalt _ ihe => intro _ hr; exact Step.assignHalt (ihe hr)
  | exprStmt _ ihe => intro _ hr; exact Step.exprStmt (ihe hr)
  | exprStmtHalt _ ihe => intro _ hr; exact Step.exprStmtHalt (ihe hr)
  | ifTrue _ hnz _ ihc ihb => intro _ hr; exact Step.ifTrue (ihc hr) hnz (ihb hr)
  | ifFalse _ hz ihc => intro _ hr; exact Step.ifFalse (ihc hr) hz
  | ifHalt _ ihc => intro _ hr; exact Step.ifHalt (ihc hr)
  | switchExec _ _ ihc ihb => intro _ hr; exact Step.switchExec (ihc hr) (ihb hr)
  | switchHalt _ ihc => intro _ hr; exact Step.switchHalt (ihc hr)
  | @forLoop funs V st init c post body Vinit stinit Vend stend o hinit hloop ihinit ihloop =>
      intro funs₂ hr
      exact Step.forLoop (ihinit (.cons _ hr)) (ihloop (.cons _ hr))
  | @forInitHalt funs V st init c post body Vinit stinit hinit ihinit =>
      intro funs₂ hr; exact Step.forInitHalt (ihinit (.cons _ hr))
  | «break» => intro _ _; exact Step.break
  | «continue» => intro _ _; exact Step.continue
  | «leave» => intro _ _; exact Step.leave
  | seqNil => intro _ _; exact Step.seqNil
  | seqCons _ _ ihs ihrest => intro _ hr; exact Step.seqCons (ihs hr) (ihrest hr)
  | seqStop _ hne ihs => intro _ hr; exact Step.seqStop (ihs hr) hne
  | loopDone _ hz ihc => intro _ hr; exact Step.loopDone (ihc hr) hz
  | loopCondHalt _ ihc => intro _ hr; exact Step.loopCondHalt (ihc hr)
  | loopStep _ hnz _ hob _ _ ihc ihb ihp ihr =>
      intro _ hr; exact Step.loopStep (ihc hr) hnz (ihb hr) hob (ihp hr) (ihr hr)
  | loopPostHalt _ hnz _ hob _ ihc ihb ihp =>
      intro _ hr; exact Step.loopPostHalt (ihc hr) hnz (ihb hr) hob (ihp hr)
  | loopBreak _ hnz _ ihc ihb => intro _ hr; exact Step.loopBreak (ihc hr) hnz (ihb hr)
  | loopLeave _ hnz _ ihc ihb => intro _ hr; exact Step.loopLeave (ihc hr) hnz (ihb hr)
  | loopBodyHalt _ hnz _ ihc ihb => intro _ hr; exact Step.loopBodyHalt (ihc hr) hnz (ihb hr)

theorem restored_head {base inner : VEnv D} {c : Ident} {old : U256}
    (hsuffix : ((c, old) :: base).map Prod.fst <:+ inner.map Prod.fst)
    (hlen : ((c, old) :: base).length ≤ inner.length) :
    ∃ value tail, restore ((c, old) :: base) inner = (c, value) :: tail ∧
      tail.length = base.length := by
  have hk : (restore ((c, old) :: base) inner).map Prod.fst =
      ((c, old) :: base).map Prod.fst := restore_keys hsuffix hlen
  have hl : (restore ((c, old) :: base) inner).length =
      ((c, old) :: base).length := restore_length hlen
  generalize hb : restore ((c, old) :: base) inner = B at hk hl ⊢
  cases B with
  | nil => simp at hk
  | cons p tail =>
      obtain ⟨z, value⟩ := p
      simp only [List.map_cons] at hk
      have hzc : z = c := by simpa using congrArg List.head? hk
      subst z
      refine ⟨value, tail, rfl, ?_⟩
      simp only [List.length_cons] at hl
      omega

theorem hoist_nil_of_no_direct_fun : ∀ middle : Block Op,
    hasDirectFun middle = false → hoist D middle = []
  | [], _ => rfl
  | .funDef _ _ _ _ :: _, h => by simp [hasDirectFun] at h
  | .block _ :: rest, h
  | .letDecl _ _ :: rest, h
  | .assign _ _ :: rest, h
  | .cond _ _ :: rest, h
  | .switch _ _ _ :: rest, h
  | .forLoop _ _ _ _ :: rest, h
  | .exprStmt _ :: rest, h
  | .break :: rest, h
  | .continue :: rest, h
  | .leave :: rest, h => by
      simpa [hasDirectFun, hoist] using hoist_nil_of_no_direct_fun rest h

theorem scopeTail_equivBlock {pre middle : Block Op} {carrier result : Ident}
    {e : Expr Op}
    (hcr : carrier ≠ result)
    (hcarrier : stmtsDeclare carrier middle = false)
    (hresult : stmtsDeclare result middle = false)
    (hfun : hasDirectFun middle = false) :
    EquivBlock D
      (pre ++ ([.letDecl [carrier] none] ++
        middle ++ [.assign [result] e, .leave]))
      (pre ++ [.letDecl [carrier] none,
        .block (middle ++ [.assign [carrier] e]),
        .assign [result] (.var carrier), .leave]) := by
  have hmhoist : hoist D middle = [] := hoist_nil_of_no_direct_fun middle hfun
  have hh : hoist D (pre ++ ([.letDecl [carrier] none] ++
        middle ++ [.assign [result] e, .leave])) =
      hoist D (pre ++ [.letDecl [carrier] none,
        .block (middle ++ [.assign [carrier] e]),
        .assign [result] (.var carrier), .leave]) := by
    simp only [hoist_append]
    rw [hmhoist]
    rfl
  have hnc : carrier ∉ stmtsBinds middle :=
    binds_not_mem_of_declare_false carrier middle hcarrier
  have hnr : result ∉ stmtsBinds middle :=
    binds_not_mem_of_declare_false result middle hresult
  intro funs V st V' st' o
  constructor
  · intro hrun
    cases hrun with
    | block hb =>
      rw [hh] at hb
      let F : FunEnv D := hoist D
        (pre ++ [.letDecl [carrier] none,
          .block (middle ++ [.assign [carrier] e]),
          .assign [result] (.var carrier), .leave]) :: funs
      rcases stmts_append_fwd hb with ⟨Vp, stp, hpre, hsuf⟩ | ⟨hne, hpre⟩
      · cases hsuf with
        | seqCons hlet htail =>
          cases hlet with
          | letZero =>
            let Vc : VEnv D :=
              (carrier, (evmWithExternal calls creates).zero) :: Vp
            have htail' := htail
            simp only [bindZeros, List.map_cons, List.map_nil,
              List.cons_append, List.nil_append] at htail'
            rcases stmts_append_fwd htail' with
              ⟨Vm, stm, hmid, hlast⟩ | ⟨hneMid, hmid⟩
            · cases hlast with
              | seqCons hass hleave =>
                cases hass with
                | assignVal hexpr hlen =>
                  rename_i values
                  cases values with
                  | nil => simp at hlen
                  | cons value values =>
                    cases values with
                    | cons value' values => simp at hlen
                    | nil =>
                      cases hleave with
                      | seqCons hleave hnil => cases hleave
                      | seqStop hleave hneLeave =>
                        cases hleave
                        have hmid' :=
                          YulEvmCompiler.Optimizer.Step.emptyScope_congr hmid (.add _)
                        have hexpr' :=
                          YulEvmCompiler.Optimizer.Step.emptyScope_congr hexpr (.add _)
                        have hinner : Step D ([] :: F)
                            Vc stp (.stmts (middle ++ [.assign [carrier] e]))
                            (.sres (VEnv.set Vm carrier value) st' .normal) := by
                          apply stmts_append_normal hmid'
                          exact Step.seqCons (Step.assignVal hexpr' (by simp)) Step.seqNil
                        have hblock : Step D F Vc stp
                            (.stmt (.block (middle ++ [.assign [carrier] e])))
                            (.sres (restore Vc (VEnv.set Vm carrier value)) st' .normal) := by
                          apply Step.block
                          have hi : hoist D (middle ++ [.assign [carrier] e]) = [] := by
                            rw [hoist_append, hmhoist]
                            rfl
                          rw [hi]
                          exact hinner
                        have hkeys := stmts_normal_keys hmid
                        have hccomm := restore_set_commute value hkeys hnc
                        have hbaseKeys := venvKeys_suffix hmid rfl
                        have hbaseLen := venvLen_mono hmid rfl
                        obtain ⟨old, tail, hshape, htailLen⟩ :=
                          restored_head hbaseKeys hbaseLen
                        have hcmem : carrier ∈
                            (restore Vc Vm).map Prod.fst := by
                          rw [hshape]
                          simp
                        have hget0 := get_set_of_mem value hcmem
                        have hget : VEnv.get
                            (restore Vc (VEnv.set Vm carrier value)) carrier =
                            some value := by
                          rw [hccomm]
                          exact hget0
                        have hcopy : Step D F
                            (restore Vc (VEnv.set Vm carrier value)) st'
                            (.stmt (.assign [result] (.var carrier)))
                            (.sres (VEnv.set
                              (restore Vc (VEnv.set Vm carrier value)) result value)
                              st' .normal) :=
                          Step.assignVal (Step.var hget) (by simp)
                        have hleaveTarget : Step D F
                            (VEnv.set
                              (restore Vc (VEnv.set Vm carrier value)) result value)
                            st' (.stmts [.leave])
                            (.sres (VEnv.set
                              (restore Vc (VEnv.set Vm carrier value)) result value)
                              st' .leave) :=
                          Step.seqStop Step.leave (by decide)
                        have hcopyTarget : Step D F
                            (restore Vc (VEnv.set Vm carrier value)) st'
                            (.stmts [.assign [result] (.var carrier), .leave])
                            (.sres (VEnv.set
                              (restore Vc (VEnv.set Vm carrier value)) result value)
                              st' .leave) :=
                          Step.seqCons hcopy hleaveTarget
                        have htargetTail : Step D F Vc stp
                            (.stmts [.block (middle ++ [.assign [carrier] e]),
                              .assign [result] (.var carrier), .leave])
                            (.sres (VEnv.set
                              (restore Vc (VEnv.set Vm carrier value)) result value)
                              st' .leave) :=
                          Step.seqCons hblock hcopyTarget
                        have hVpLen : V.length ≤ Vp.length := venvLen_mono hpre rfl
                        have hOuterVc : V.length ≤ Vc.length := by
                          simp [Vc]
                          omega
                        have hVcLen : Vc.length ≤ Vm.length := hbaseLen
                        have hrcomm := restore_set_commute value hkeys hnr
                        have herase : restore V
                            (VEnv.set (VEnv.set (restore Vc Vm) carrier value)
                              result value) =
                            restore V (VEnv.set (restore Vc Vm) result value) := by
                          rw [hshape]
                          apply restore_erase_head_set old value value
                          · rw [htailLen]
                            exact hVpLen
                          · exact hcr
                        have hsourceEq : restore V
                            (VEnv.set (restore Vc Vm) result value) =
                            restore V (VEnv.set Vm result value) := by
                          rw [← hrcomm]
                          apply restore_restore hOuterVc
                          rw [VEnv.set_length]
                          exact hVcLen
                        have henv : restore V
                            (VEnv.set (restore Vc (VEnv.set Vm carrier value))
                              result value) =
                            restore V (VEnv.set Vm result value) := by
                          rw [hccomm, herase, hsourceEq]
                        have hletTarget : Step D F Vp stp
                            (.stmt (.letDecl [carrier] none))
                            (.sres Vc stp .normal) := by
                          have hz : Step D F Vp stp
                              (.stmt (.letDecl [carrier] none))
                              (.sres (bindZeros D [carrier] ++ Vp) stp .normal) :=
                            Step.letZero
                          simpa [Vc, bindZeros] using hz
                        have htargetSuffix : Step D F Vp stp
                            (.stmts [.letDecl [carrier] none,
                              .block (middle ++ [.assign [carrier] e]),
                              .assign [result] (.var carrier), .leave])
                            (.sres (VEnv.set
                              (restore Vc (VEnv.set Vm carrier value)) result value)
                              st' .leave) :=
                          Step.seqCons hletTarget htargetTail
                        have hfinal := Step.block
                          (stmts_append_normal hpre htargetSuffix)
                        rw [henv] at hfinal
                        simpa [VEnv.setMany] using hfinal
              | seqStop hass hne =>
                cases hass with
                | assignVal _ _ => exact absurd rfl hne
                | assignHalt hexpr =>
                  rename_i Vm
                  have hmid' :=
                    YulEvmCompiler.Optimizer.Step.emptyScope_congr hmid (.add _)
                  have hexpr' :=
                    YulEvmCompiler.Optimizer.Step.emptyScope_congr hexpr (.add _)
                  have hassignTail : Step D ([] :: F) Vm stm
                      (.stmts [.assign [carrier] e]) (.sres Vm st' .halt) :=
                    Step.seqStop (Step.assignHalt (vars := [carrier]) hexpr') (by decide)
                  have hinner : Step D ([] :: F) Vc stp
                      (.stmts (middle ++ [.assign [carrier] e]))
                      (.sres Vm st' .halt) :=
                    stmts_append_normal hmid' hassignTail
                  have hblock : Step D F Vc stp
                      (.stmt (.block (middle ++ [.assign [carrier] e])))
                      (.sres (restore Vc Vm) st' .halt) := by
                    apply Step.block
                    have hi : hoist D (middle ++ [.assign [carrier] e]) = [] := by
                      rw [hoist_append, hmhoist]
                      rfl
                    rw [hi]
                    exact hinner
                  have hVpLen : V.length ≤ Vp.length := venvLen_mono hpre rfl
                  have hVcLen : Vc.length ≤ Vm.length := venvLen_mono hmid rfl
                  have hOuterVc : V.length ≤ Vc.length := by simp [Vc]; omega
                  have henv := restore_restore hOuterVc hVcLen
                  have hblockTail : Step D F Vc stp
                      (.stmts [.block (middle ++ [.assign [carrier] e]),
                        .assign [result] (.var carrier), .leave])
                      (.sres (restore Vc Vm) st' .halt) :=
                    Step.seqStop hblock (by decide)
                  have hletTarget : Step D F Vp stp
                      (.stmt (.letDecl [carrier] none)) (.sres Vc stp .normal) := by
                    have hz : Step D F Vp stp (.stmt (.letDecl [carrier] none))
                        (.sres (bindZeros D [carrier] ++ Vp) stp .normal) := Step.letZero
                    simpa [Vc, bindZeros] using hz
                  have htargetSuffix := Step.seqCons hletTarget hblockTail
                  have hfinal := Step.block (stmts_append_normal hpre htargetSuffix)
                  rw [henv] at hfinal
                  exact hfinal
            · rename_i Vmid
              have hmid' :=
                YulEvmCompiler.Optimizer.Step.emptyScope_congr hmid (.add _)
              have hinner : Step D ([] :: F) Vc stp
                  (.stmts (middle ++ [.assign [carrier] e]))
                  (.sres Vmid st' o) :=
                stmts_append_early (suf := [.assign [carrier] e]) hmid' hneMid
              have hblock : Step D F Vc stp
                  (.stmt (.block (middle ++ [.assign [carrier] e])))
                  (.sres (restore Vc Vmid) st' o) := by
                apply Step.block
                have hi : hoist D (middle ++ [.assign [carrier] e]) = [] := by
                  rw [hoist_append, hmhoist]
                  rfl
                rw [hi]
                exact hinner
              have hVpLen : V.length ≤ Vp.length := venvLen_mono hpre rfl
              have hOuterVc : V.length ≤ Vc.length := by simp [Vc]; omega
              have hVcLen : Vc.length ≤ Vmid.length := venvLen_mono hmid rfl
              have henv := restore_restore hOuterVc hVcLen
              have hblockTail : Step D F Vc stp
                  (.stmts [.block (middle ++ [.assign [carrier] e]),
                    .assign [result] (.var carrier), .leave])
                  (.sres (restore Vc Vmid) st' o) :=
                Step.seqStop hblock hneMid
              have hletTarget : Step D F Vp stp
                  (.stmt (.letDecl [carrier] none)) (.sres Vc stp .normal) := by
                have hz : Step D F Vp stp (.stmt (.letDecl [carrier] none))
                    (.sres (bindZeros D [carrier] ++ Vp) stp .normal) := Step.letZero
                simpa [Vc, bindZeros] using hz
              have htargetSuffix := Step.seqCons hletTarget hblockTail
              have hfinal := Step.block (stmts_append_normal hpre htargetSuffix)
              rw [henv] at hfinal
              exact hfinal
        | seqStop hlet hne =>
          cases hlet
          exact absurd rfl hne
      · exact Step.block (stmts_append_early hpre hne)
  · intro hrun
    cases hrun with
    | block hb =>
      rw [← hh] at hb
      let F : FunEnv D := hoist D
        (pre ++ ([.letDecl [carrier] none] ++
          middle ++ [.assign [result] e, .leave])) :: funs
      rcases stmts_append_fwd hb with ⟨Vp, stp, hpre, hsuf⟩ | ⟨hne, hpre⟩
      · cases hsuf with
        | seqCons hlet hrest =>
          cases hlet
          let Vc : VEnv D :=
            (carrier, (evmWithExternal calls creates).zero) :: Vp
          have hrest' := hrest
          simp only [bindZeros, List.map_cons, List.map_nil,
            List.cons_append, List.nil_append] at hrest'
          cases hrest' with
          | seqCons hblock hafter =>
            cases hblock with
            | block hinner =>
              have hi : hoist D (middle ++ [.assign [carrier] e]) = [] := by
                rw [hoist_append, hmhoist]
                rfl
              rw [hi] at hinner
              have hinner' :=
                YulEvmCompiler.Optimizer.Step.emptyScope_congr hinner (.drop F)
              rcases stmts_append_fwd hinner' with
                ⟨Vm, stm, hmid, hassignCarrier⟩ | ⟨hneMid, hmid⟩
              · cases hassignCarrier with
                | seqCons hassign hnil =>
                  cases hnil
                  cases hassign with
                  | assignVal hexpr hlen =>
                    rename_i values
                    cases values with
                    | nil => simp at hlen
                    | cons value values =>
                      cases values with
                      | cons value' values => simp at hlen
                      | nil =>
                        cases hafter with
                        | seqCons hcopy hleave =>
                          cases hcopy with
                          | assignVal hvar hcopyLen =>
                            rename_i copied
                            cases copied with
                            | nil => simp at hcopyLen
                            | cons copied copiedRest =>
                              cases copiedRest with
                              | cons copied' copiedRest => simp at hcopyLen
                              | nil =>
                                cases hvar
                                rename_i hreadRaw
                                cases hleave with
                                | seqCons hleave hnil => cases hleave
                                | seqStop hleave hneLeave =>
                                  cases hleave
                                  have hkeys := stmts_normal_keys hmid
                                  have hccomm := restore_set_commute value hkeys hnc
                                  have hbaseKeys := venvKeys_suffix hmid rfl
                                  have hbaseLen := venvLen_mono hmid rfl
                                  obtain ⟨old, tail, hshape, htailLen⟩ :=
                                    restored_head hbaseKeys hbaseLen
                                  have hcmem : carrier ∈
                                      (restore Vc Vm).map Prod.fst := by
                                    rw [hshape]
                                    simp
                                  have hget0 := get_set_of_mem value hcmem
                                  have hactual : VEnv.get
                                      (restore Vc (VEnv.set Vm carrier value)) carrier =
                                      some value := by
                                    rw [hccomm]
                                    exact hget0
                                  have hread : VEnv.get
                                      (restore Vc (VEnv.set Vm carrier value)) carrier =
                                      some copied := by
                                    simpa [VEnv.setMany] using hreadRaw
                                  have hcv : copied = value := by
                                    exact Option.some.inj (hread.symm.trans hactual)
                                  subst copied
                                  have hassignResult : Step D F Vm stm
                                      (.stmt (.assign [result] e))
                                      (.sres (VEnv.set Vm result value) st' .normal) :=
                                    Step.assignVal hexpr (by simp)
                                  have hleaveSource : Step D F
                                      (VEnv.set Vm result value) st'
                                      (.stmts [.leave])
                                      (.sres (VEnv.set Vm result value) st' .leave) :=
                                    Step.seqStop Step.leave (by decide)
                                  have hlastSource : Step D F Vm stm
                                      (.stmts [.assign [result] e, .leave])
                                      (.sres (VEnv.set Vm result value) st' .leave) :=
                                    Step.seqCons hassignResult hleaveSource
                                  have hafterLet : Step D F Vc stp
                                      (.stmts (middle ++ [.assign [result] e, .leave]))
                                      (.sres (VEnv.set Vm result value) st' .leave) :=
                                    stmts_append_normal hmid hlastSource
                                  have hletSource : Step D F Vp stp
                                      (.stmt (.letDecl [carrier] none))
                                      (.sres Vc stp .normal) := by
                                    have hz : Step D F Vp stp
                                        (.stmt (.letDecl [carrier] none))
                                        (.sres (bindZeros D [carrier] ++ Vp)
                                          stp .normal) := Step.letZero
                                    simpa [Vc, bindZeros] using hz
                                  have hsourceSuffix := Step.seqCons hletSource hafterLet
                                  have hsourceFinal := Step.block
                                    (stmts_append_normal hpre hsourceSuffix)
                                  have hVpLen : V.length ≤ Vp.length :=
                                    venvLen_mono hpre rfl
                                  have hOuterVc : V.length ≤ Vc.length := by
                                    simp [Vc]
                                    omega
                                  have hVcLen : Vc.length ≤ Vm.length := hbaseLen
                                  have hrcomm := restore_set_commute value hkeys hnr
                                  have herase : restore V
                                      (VEnv.set (VEnv.set (restore Vc Vm)
                                        carrier value) result value) =
                                      restore V (VEnv.set (restore Vc Vm)
                                        result value) := by
                                    rw [hshape]
                                    apply restore_erase_head_set old value value
                                    · rw [htailLen]
                                      exact hVpLen
                                    · exact hcr
                                  have hsourceEq : restore V
                                      (VEnv.set (restore Vc Vm) result value) =
                                      restore V (VEnv.set Vm result value) := by
                                    rw [← hrcomm]
                                    apply restore_restore hOuterVc
                                    rw [VEnv.set_length]
                                    exact hVcLen
                                  have henv : restore V
                                      (VEnv.set
                                        (restore Vc (VEnv.set Vm carrier value))
                                        result value) =
                                      restore V (VEnv.set Vm result value) := by
                                    rw [hccomm, herase, hsourceEq]
                                  rw [← henv] at hsourceFinal
                                  simpa [VEnv.setMany] using hsourceFinal
                        | seqStop hcopy hneCopy =>
                          cases hcopy with
                          | assignVal _ _ => exact absurd rfl hneCopy
                          | assignHalt hvar => cases hvar
                | seqStop hassign hneAssign =>
                  cases hassign with
                  | assignVal _ _ => exact absurd rfl hneAssign
              · exact absurd rfl hneMid
          | seqStop hblock hneBlock =>
            cases hblock with
            | block hinner =>
              have hi : hoist D (middle ++ [.assign [carrier] e]) = [] := by
                rw [hoist_append, hmhoist]
                rfl
              rw [hi] at hinner
              have hinner' :=
                YulEvmCompiler.Optimizer.Step.emptyScope_congr hinner (.drop F)
              rcases stmts_append_fwd hinner' with
                ⟨Vm, stm, hmid, hassignCarrier⟩ | ⟨hneMid, hmid⟩
              · cases hassignCarrier with
                | seqCons hassign hnil =>
                  cases hnil
                  cases hassign
                  exact absurd rfl hneBlock
                | seqStop hassign hneAssign =>
                  cases hassign with
                  | assignVal _ _ => exact absurd rfl hneAssign
                  | assignHalt hexpr =>
                    rename_i Vmid
                    have hlastSource : Step D F Vmid stm
                        (.stmts [.assign [result] e, .leave])
                        (.sres Vmid st' .halt) :=
                      Step.seqStop (Step.assignHalt (vars := [result]) hexpr)
                        (by decide)
                    have hafterLet : Step D F Vc stp
                        (.stmts (middle ++ [.assign [result] e, .leave]))
                        (.sres Vmid st' .halt) :=
                      stmts_append_normal hmid hlastSource
                    have hletSource : Step D F Vp stp
                        (.stmt (.letDecl [carrier] none))
                        (.sres Vc stp .normal) := by
                      have hz : Step D F Vp stp
                          (.stmt (.letDecl [carrier] none))
                          (.sres (bindZeros D [carrier] ++ Vp) stp .normal) :=
                        Step.letZero
                      simpa [Vc, bindZeros] using hz
                    have hsourceSuffix := Step.seqCons hletSource hafterLet
                    have hsourceFinal := Step.block
                      (stmts_append_normal hpre hsourceSuffix)
                    have hOuterVc : V.length ≤ Vc.length := by
                      have hp : V.length ≤ Vp.length := venvLen_mono hpre rfl
                      simp [Vc]
                      omega
                    have hVcLen : Vc.length ≤ Vmid.length :=
                      venvLen_mono hmid rfl
                    have henv := restore_restore hOuterVc hVcLen
                    rw [← henv] at hsourceFinal
                    exact hsourceFinal
              · rename_i Vmid
                have hafterLet : Step D F Vc stp
                    (.stmts (middle ++ [.assign [result] e, .leave]))
                    (.sres Vmid st' o) :=
                  stmts_append_early
                    (suf := [.assign [result] e, .leave]) hmid hneMid
                have hletSource : Step D F Vp stp
                    (.stmt (.letDecl [carrier] none))
                    (.sres Vc stp .normal) := by
                  have hz : Step D F Vp stp
                      (.stmt (.letDecl [carrier] none))
                      (.sres (bindZeros D [carrier] ++ Vp) stp .normal) :=
                    Step.letZero
                  simpa [Vc, bindZeros] using hz
                have hsourceSuffix := Step.seqCons hletSource hafterLet
                have hsourceFinal := Step.block
                  (stmts_append_normal hpre hsourceSuffix)
                have hOuterVc : V.length ≤ Vc.length := by
                  have hp : V.length ≤ Vp.length := venvLen_mono hpre rfl
                  simp [Vc]
                  omega
                have hVcLen : Vc.length ≤ Vmid.length := venvLen_mono hmid rfl
                have henv := restore_restore hOuterVc hVcLen
                rw [← henv] at hsourceFinal
                exact hsourceFinal
        | seqStop hlet hne =>
          cases hlet
          exact absurd rfl hne
      · exact Step.block (stmts_append_early hpre hne)

theorem restore_cons_of_le {outer base : VEnv D} {x : Ident} (v : U256)
    (h : outer.length ≤ base.length) :
    restore outer ((x, v) :: base) = restore outer base := by
  simp only [restore, List.length_cons]
  rw [show base.length + 1 - outer.length =
      (base.length - outer.length) + 1 by omega]
  rfl

theorem splitLet_equivBlock {pre rest : Block Op} {x : Ident} {e : Expr Op} :
    exprMentions x e = false →
    EquivBlock D (pre ++ .letDecl [x] (some e) :: rest)
      (pre ++ .letDecl [x] none :: .assign [x] e :: rest) := by
  intro hx
  have hh : hoist D (pre ++ .letDecl [x] (some e) :: rest) =
      hoist D (pre ++ .letDecl [x] none :: .assign [x] e :: rest) := by
    simp [hoist]
  intro funs V st V' st' o
  constructor
  · intro hrun
    cases hrun with
    | block hb =>
      rw [hh] at hb
      rcases stmts_append_fwd hb with ⟨Vp, stp, hpre, hsuf⟩ | ⟨hne, hpre⟩
      · cases hsuf with
        | seqCons hlet hrest =>
          let F : FunEnv D := hoist D
            (pre ++ .letDecl [x] none :: .assign [x] e :: rest) :: funs
          cases hlet with
          | @letVal _ _ _ _ _ values _ hexpr hlen =>
            cases values with
            | nil => simp at hlen
            | cons value values =>
              cases values with
              | cons value' values => simp at hlen
              | nil =>
                have hzero : Step D F Vp stp (.stmt (.letDecl [x] none))
                    (.sres ((x, (evmWithExternal calls creates).zero) :: Vp)
                      stp .normal) := Step.letZero (funs := F)
                have hins : InsAt Vp.length x
                    (evmWithExternal calls creates).zero Vp
                    ((x, (evmWithExternal calls creates).zero) :: Vp) :=
                  ⟨[], Vp, by simp, by simp, rfl⟩
                obtain ⟨_, hexpr', hrel⟩ := frameAdd hexpr hins
                  (by simpa [codeMentions] using hx)
                obtain rfl := hrel.eres
                have hassign := Step.assignVal (vars := [x]) (vals := [value])
                  hexpr' rfl
                simp [VEnv.setMany, VEnv.set] at hassign
                exact Step.block (stmts_append_normal hpre
                  (Step.seqCons hzero (Step.seqCons hassign hrest)))
        | seqStop hlet hne =>
          let Vp0 := Vp
          let stp0 := stp
          let F : FunEnv D := hoist D
            (pre ++ .letDecl [x] none :: .assign [x] e :: rest) :: funs
          cases hlet with
          | letVal _ _ => exact absurd rfl hne
          | letHalt hexpr =>
            let Vx : VEnv D :=
              (x, (evmWithExternal calls creates).zero) :: Vp0
            have hzero : Step D F Vp0 stp0 (.stmt (.letDecl [x] none))
                (.sres Vx stp0 .normal) := by simpa [Vx, Vp0, bindZeros] using
                  (Step.letZero (funs := F) (V := Vp0) (st := stp0)
                    (vars := [x]))
            have hins : InsAt Vp0.length x
                (evmWithExternal calls creates).zero Vp0 Vx := by
              exact ⟨[], Vp0, by simp, by simp [Vx], rfl⟩
            obtain ⟨_, hexpr', hrel⟩ := frameAdd hexpr hins
              (by simpa [codeMentions] using hx)
            obtain rfl := hrel.eres
            have htarget := Step.seqCons hzero
              (Step.seqStop (rest := rest)
                (Step.assignHalt (vars := [x]) hexpr') hne)
            have hfinal := Step.block (stmts_append_normal hpre htarget)
            have hlenVp : V.length ≤ Vp0.length := by
              simpa [Vp0] using venvLen_mono hpre rfl
            rw [restore_cons_of_le (evmWithExternal calls creates).zero hlenVp]
              at hfinal
            exact hfinal
      · exact Step.block (stmts_append_early hpre hne)
  · intro hrun
    cases hrun with
    | block hb =>
      rw [← hh] at hb
      rcases stmts_append_fwd hb with ⟨Vp, stp, hpre, hsuf⟩ | ⟨hne, hpre⟩
      · cases hsuf with
        | seqCons hzero hrest =>
          cases hzero
          have hrest' := hrest
          simp only [bindZeros, List.map_cons, List.map_nil, List.cons_append,
            List.nil_append] at hrest'
          cases hrest' with
          | seqCons hassign htail =>
            cases hassign with
            | @assignVal _ _ _ _ _ values _ hexpr hlen =>
              cases values with
              | nil => simp at hlen
              | cons value values =>
                cases values with
                | cons value' values => simp at hlen
                | nil =>
                  have hins : InsAt Vp.length x
                      (evmWithExternal calls creates).zero Vp
                      ((x, (evmWithExternal calls creates).zero) :: Vp) :=
                    ⟨[], Vp, by simp, by simp, rfl⟩
                  obtain ⟨_, hexpr', hrel⟩ := frameRemove hexpr hins
                    (by simpa [codeMentions] using hx)
                  obtain rfl := hrel.eres_right
                  have hlet := Step.letVal (vars := [x]) (vals := [value])
                    hexpr' rfl
                  have htail' := htail
                  simp [VEnv.setMany, VEnv.set] at htail'
                  have hs := Step.seqCons hlet htail'
                  exact Step.block (stmts_append_normal hpre hs)
          | seqStop hassign hneAssign =>
            cases hassign with
            | assignVal _ _ => exact absurd rfl hneAssign
            | assignHalt hexpr =>
              have hins : InsAt Vp.length x
                  (evmWithExternal calls creates).zero Vp
                  ((x, (evmWithExternal calls creates).zero) :: Vp) :=
                ⟨[], Vp, by simp, by simp, rfl⟩
              obtain ⟨_, hexpr', hrel⟩ := frameRemove hexpr hins
                (by simpa [codeMentions] using hx)
              obtain rfl := hrel.eres_right
              have hsource := Step.seqStop (rest := rest)
                (Step.letHalt (vars := [x]) hexpr') hneAssign
              have hfinal := Step.block (stmts_append_normal hpre hsource)
              have hlenVp : V.length ≤ Vp.length := venvLen_mono hpre rfl
              rw [← restore_cons_of_le
                (evmWithExternal calls creates).zero hlenVp] at hfinal
              exact hfinal
        | seqStop hzero hne =>
          cases hzero
          exact absurd rfl hne
      · exact Step.block (stmts_append_early hpre hne)

theorem scopeTailVal_equivBlock {pre middle : Block Op}
    {carrier result : Ident} {val : Option (Expr Op)} {e : Expr Op}
    (hcr : carrier ≠ result)
    (hinit : carrierInitSafe carrier val = true)
    (hcarrier : stmtsDeclare carrier middle = false)
    (hresult : stmtsDeclare result middle = false)
    (hfun : hasDirectFun middle = false) :
    EquivBlock D
      (pre ++ ([.letDecl [carrier] val] ++ middle ++
        [.assign [result] e, .leave]))
      (pre ++ [.letDecl [carrier] none,
        .block (carrierInit carrier val ++ middle ++ [.assign [carrier] e]),
        .assign [result] (.var carrier), .leave]) := by
  cases val with
  | none =>
      simpa [carrierInit] using scopeTail_equivBlock
        (pre := pre) hcr hcarrier hresult hfun
  | some init =>
      simp only [carrierInitSafe] at hinit
      have hinit' : exprMentions carrier init = false := by simpa using hinit
      have hsplit := splitLet_equivBlock (calls := calls) (creates := creates)
        (pre := pre)
        (rest := middle ++ [.assign [result] e, .leave]) hinit'
      have hscope := scopeTail_equivBlock (calls := calls) (creates := creates)
        (pre := pre) (carrier := carrier) (result := result) (e := e)
        (middle := .assign [carrier] init :: middle) hcr
        (by simpa [stmtsDeclare, stmtDeclares] using hcarrier)
        (by simpa [stmtsDeclare, stmtDeclares, hcr] using hresult)
        (by simpa [hasDirectFun] using hfun)
      simpa [carrierInit, List.append_assoc] using hsplit.trans hscope

theorem splitAssignLeave_inv : ∀ {ss middle : Block Op} {result : Ident}
    {e : Expr Op}, splitAssignLeave ss = some (middle, result, e) →
      ss = middle ++ [.assign [result] e, .leave] := by
  intro ss
  fun_induction splitAssignLeave ss
  · simp_all
  · rename_i s rest hspecial ih
    intro middle result e h
    cases hs : splitAssignLeave rest with
    | none => simp [hs] at h
    | some p =>
      obtain ⟨m, r, ex⟩ := p
      simp only [hs] at h
      cases h
      rw [ih hs]
      simp
  · simp_all

theorem scopeTailHere_sound {layout : List Ident} {ss ss' : Block Op}
    (h : scopeTailHere layout ss = some ss') :
    ∀ pre : Block Op, EquivBlock D (pre ++ ss) (pre ++ ss') := by
  intro pre
  cases ss with
  | nil => simp [scopeTailHere] at h
  | cons s rest =>
    cases s with
    | letDecl vars val =>
      cases vars with
      | nil => simp [scopeTailHere] at h
      | cons carrier varsTail =>
        cases varsTail with
        | cons y ys => simp [scopeTailHere] at h
        | nil =>
          simp only [scopeTailHere] at h
          cases hs : splitAssignLeave rest with
          | none => simp [hs] at h
          | some p =>
            obtain ⟨middle, result, e⟩ := p
            simp only [hs] at h
            cases hd : layout.findIdx? (fun x => x = result) with
            | none => simp [hd] at h
            | some resultDepth =>
              simp [hd] at h
              rcases h with
                ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, hcr⟩, _⟩, hinit⟩, hc⟩, hr⟩, hf⟩, _⟩, rfl⟩
              have hshape := splitAssignLeave_inv hs
              subst rest
              simpa [List.append_assoc] using
                scopeTailVal_equivBlock (calls := calls) (creates := creates)
                  (pre := pre) (middle := middle) (carrier := carrier)
                  (result := result) (val := val) (e := e)
                  hcr hinit hc hr hf
    | block _ => simp [scopeTailHere] at h
    | funDef _ _ _ _ => simp [scopeTailHere] at h
    | assign _ _ => simp [scopeTailHere] at h
    | cond _ _ => simp [scopeTailHere] at h
    | «switch» _ _ _ => simp [scopeTailHere] at h
    | forLoop _ _ _ _ => simp [scopeTailHere] at h
    | exprStmt _ => simp [scopeTailHere] at h
    | «break» => simp [scopeTailHere] at h
    | «continue» => simp [scopeTailHere] at h
    | «leave» => simp [scopeTailHere] at h

private theorem tail_forall₂_refl_cases
    (cases : List (Literal × Block Op)) :
    List.Forall₂ (fun p q => p.1 = q.1 ∧ EquivBlock D p.2 q.2)
      cases cases := by
  induction cases with
  | nil => exact .nil
  | cons p rest ih => exact .cons ⟨rfl, EquivBlock.refl _⟩ ih

mutual
  theorem scopeOneStmt_sound : ∀ (layout : List Ident) (s s' : Stmt Op),
      scopeOneStmt layout s = some s' →
      EquivStmt D s s' ∧ ScopeRel D (hoist D [s]) (hoist D [s'])
    | layout, .block body, s', h => by
        simp only [scopeOneStmt] at h
        obtain ⟨body', hb, hs'⟩ := Option.map_eq_some_iff.mp h
        subst s'
        have heq := scopeOneStmts_sound layout body _ hb []
        exact ⟨heq, ScopeRel.refl _⟩
    | layout, .funDef f ps rs body, s', h => by
        simp only [scopeOneStmt] at h
        obtain ⟨body', hb, hs'⟩ := Option.map_eq_some_iff.mp h
        subst s'
        have heq := scopeOneStmts_sound (ps ++ rs) body _ hb []
        refine ⟨funDef_equiv f ps rs body body', ?_⟩
        exact .cons ⟨rfl, rfl, rfl, heq⟩ .nil
    | layout, .cond c body, s', h => by
        simp only [scopeOneStmt] at h
        obtain ⟨body', hb, hs'⟩ := Option.map_eq_some_iff.mp h
        subst s'
        have heq := scopeOneStmts_sound layout body _ hb []
        exact ⟨EquivStmt.cond_congr (fun _ _ _ _ => Iff.rfl) heq,
          ScopeRel.refl _⟩
    | layout, .switch c cases dflt, s', h => by
        unfold scopeOneStmt at h
        cases hcases : scopeOneCases layout cases with
        | some cases' =>
          simp only [hcases] at h
          cases h
          have hc := scopeOneCases_sound layout cases _ hcases
          exact ⟨EquivStmt.switch_congr (fun _ _ _ _ => Iff.rfl) hc
            (EquivBlock.refl _), ScopeRel.refl _⟩
        | none =>
          simp only [hcases] at h
          cases dflt with
          | some body =>
            cases hb : scopeOneStmts layout body with
            | some body' =>
              simp only [hb] at h
              cases h
              have heq := scopeOneStmts_sound layout body _ hb []
              exact ⟨EquivStmt.switch_congr (fun _ _ _ _ => Iff.rfl)
                (tail_forall₂_refl_cases cases) heq, ScopeRel.refl _⟩
            | none => simp [hb] at h
          | none => simp at h
    | layout, .forLoop init c post body, s', h => by
        unfold scopeOneStmt at h
        cases hp : scopeOneStmts layout post with
        | some post' =>
          simp only [hp] at h
          cases h
          have heq := scopeOneStmts_sound layout post _ hp []
          exact ⟨EquivStmt.forLoop_congr init (fun _ _ _ _ => Iff.rfl) heq
            (EquivBlock.refl _), ScopeRel.refl _⟩
        | none =>
          simp only [hp] at h
          obtain ⟨body', hb, hs'⟩ := Option.map_eq_some_iff.mp h
          subst s'
          have heq := scopeOneStmts_sound layout body _ hb []
          exact ⟨EquivStmt.forLoop_congr init (fun _ _ _ _ => Iff.rfl)
            (EquivBlock.refl _) heq, ScopeRel.refl _⟩
    | _, .letDecl _ _, _, h => by simp [scopeOneStmt] at h
    | _, .assign _ _, _, h => by simp [scopeOneStmt] at h
    | _, .exprStmt _, _, h => by simp [scopeOneStmt] at h
    | _, .break, _, h => by simp [scopeOneStmt] at h
    | _, .continue, _, h => by simp [scopeOneStmt] at h
    | _, .leave, _, h => by simp [scopeOneStmt] at h
    termination_by layout s s' _h => 2 * sizeOf s

  theorem scopeOneStmts_sound : ∀ (layout : List Ident) (ss ss' : Block Op),
      scopeOneStmts layout ss = some ss' →
      ∀ pre : Block Op, EquivBlock D (pre ++ ss) (pre ++ ss')
    | layout, ss, ss', h => by
        unfold scopeOneStmts at h
        cases ht : scopeTailHere layout ss with
        | some target =>
          simp only [ht] at h
          cases h
          exact scopeTailHere_sound (calls := calls) (creates := creates) ht
        | none =>
          simp only [ht] at h
          cases ss with
          | nil => simp at h
          | cons s rest =>
            cases hs : scopeOneStmt layout s with
            | some s' =>
              simp only [hs] at h
              cases h
              intro pre
              obtain ⟨heq, hscope⟩ := scopeOneStmt_sound layout s s' hs
              exact replaceStmt_equivBlock heq hscope pre
            | none =>
              simp only [hs] at h
              let layout' := match s with
                | .letDecl xs _ => xs ++ layout
                | _ => layout
              obtain ⟨rest', hr, htarget⟩ := Option.map_eq_some_iff.mp h
              subst ss'
              intro pre
              have heq := scopeOneStmts_sound layout' rest rest' hr (pre ++ [s])
              simpa only [List.append_assoc, List.cons_append, List.nil_append]
                using heq
    termination_by layout ss ss' _h => 2 * sizeOf ss + 1

  theorem scopeOneCases_sound : ∀ (layout : List Ident)
      (cases cases' : List (Literal × Block Op)),
      scopeOneCases layout cases = some cases' →
      List.Forall₂ (fun p q => p.1 = q.1 ∧ EquivBlock D p.2 q.2) cases cases'
    | _, [], _, h => by simp [scopeOneCases] at h
    | layout, (l, body) :: rest, cases', h => by
        unfold scopeOneCases at h
        split at h
        · next body' hb =>
          cases h
          exact .cons ⟨rfl, scopeOneStmts_sound layout body _ hb []⟩
            (tail_forall₂_refl_cases rest)
        · obtain ⟨rest', hr, hs'⟩ := Option.map_eq_some_iff.mp h
          subst cases'
          exact .cons ⟨rfl, EquivBlock.refl _⟩
            (scopeOneCases_sound layout rest _ hr)
    termination_by layout cases cases' _h => 2 * sizeOf cases + 1
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

theorem scopeOneStmts_equiv {b b' : Block Op}
    (h : scopeOneStmts [] b = some b') : EquivBlock D b b' := by
  simpa using scopeOneStmts_sound [] b b' h []

theorem iterateTailScope_equiv (n : Nat) (b : Block Op) :
    EquivBlock D b (iterateTailScope n b) := by
  induction n generalizing b with
  | zero => exact EquivBlock.refl _
  | succ n ih =>
      rw [iterateTailScope]
      cases h : scopeOneStmts [] b with
      | none => exact EquivBlock.refl _
      | some b' => exact (scopeOneStmts_equiv h).trans (ih b')

namespace StackV2Sound

open BoundFun

private theorem forwardAliasStmt_hoist (source copy : Ident) (s : Stmt Op) :
    hoist D [(StackV2.forwardAliasStmt source copy s).1] = hoist D [s] := by
  cases s <;> simp [StackV2.forwardAliasStmt, hoist]

private theorem forwardAliasStmts_hoist (source copy : Ident) :
    ∀ body : Block Op,
      hoist D (StackV2.forwardAliasStmts source copy body).1 = hoist D body
  | [] => by simp [StackV2.forwardAliasStmts, hoist]
  | s :: rest => by
      rw [StackV2.forwardAliasStmts]
      generalize hr : StackV2.forwardAliasStmt source copy s = r
      obtain ⟨s', keep, changed⟩ := r
      dsimp only
      have hh := forwardAliasStmt_hoist
        (calls := calls) (creates := creates) source copy s
      rw [hr] at hh
      change hoist D [s'] = hoist D [s] at hh
      cases keep with
      | false =>
          simp only [Bool.false_eq_true, if_false]
          rw [show s' :: rest = [s'] ++ rest by rfl,
            show s :: rest = [s] ++ rest by rfl,
            hoist_append, hoist_append, hh]
      | true =>
          simp only [if_true]
          rw [show s' :: (StackV2.forwardAliasStmts source copy rest).1 =
                [s'] ++ (StackV2.forwardAliasStmts source copy rest).1 by rfl,
            show s :: rest = [s] ++ rest by rfl,
            hoist_append, hoist_append, hh, forwardAliasStmts_hoist]

private theorem selectSwitch_size_lt (c : Expr Op)
    (cases : List (Literal × Block Op)) (dflt : Option (Block Op)) (cv : U256) :
    sizeOf (selectSwitch D cv cases dflt) <
      sizeOf c + sizeOf cases + sizeOf dflt := by
  unfold selectSwitch
  cases hfind : cases.find? (fun p =>
      decide (cv = (evmWithExternal calls creates).litValue p.1)) with
  | some p =>
      simp only
      have hm : p ∈ cases := List.mem_of_find?_eq_some hfind
      have hp := List.sizeOf_lt_of_mem hm
      rcases p with ⟨l, body⟩
      change sizeOf body < sizeOf c + sizeOf cases + sizeOf dflt
      have hb : sizeOf body < sizeOf (l, body) := by simp_wf
      have hc : 0 < sizeOf c := by cases c <;> simp
      have hbc := Nat.lt_trans hb hp
      omega
  | none =>
      simp only
      have hc : 0 < sizeOf c := by cases c <;> simp
      cases dflt with
      | none =>
          change 1 < sizeOf c + sizeOf cases + 1
          omega
      | some body =>
          change sizeOf body < sizeOf c + sizeOf cases + (1 + sizeOf body)
          omega

private theorem forwardAliasStmt_keep_inv (source copy : Ident) :
    ∀ s : Stmt Op, (StackV2.forwardAliasStmt source copy s).2.1 = true →
      StackV2.aliasSelfAssign copy s = true ∨
        (source ∉ writeSetStmt s ∧ copy ∉ writeSetStmt s)
  | .block body, h => by
      simp only [StackV2.forwardAliasStmt, Bool.and_eq_true,
        Bool.not_eq_true, decide_eq_false_iff_not, List.contains_eq_mem,
        writeSetStmt] at h
      right
      change source ∉ writeSetStmts body ∧ copy ∉ writeSetStmts body
      exact ⟨by simpa using h.1, by simpa using h.2⟩
  | .funDef _ _ _ _, _ => by simp [StackV2.aliasSelfAssign, writeSetStmt]
  | .letDecl xs val, h => by
      simp only [StackV2.forwardAliasStmt, Bool.and_eq_true,
        Bool.not_eq_true, decide_eq_false_iff_not, List.contains_eq_mem,
        writeSetStmt] at h
      right
      change source ∉ xs ∧ copy ∉ xs
      exact ⟨by simpa using h.1, by simpa using h.2⟩
  | .assign xs e, h => by
      simp only [StackV2.forwardAliasStmt, Bool.or_eq_true,
        Bool.and_eq_true, Bool.not_eq_true, decide_eq_false_iff_not,
        List.contains_eq_mem, writeSetStmt] at h
      rcases h with hself | hfree
      · exact .inl hself
      · right
        change source ∉ xs ∧ copy ∉ xs
        exact ⟨by simpa using hfree.1, by simpa using hfree.2⟩
  | .cond c body, h => by
      simp only [StackV2.forwardAliasStmt, Bool.and_eq_true,
        Bool.not_eq_true, decide_eq_false_iff_not, List.contains_eq_mem,
        writeSetStmt] at h
      right
      change source ∉ writeSetStmts body ∧ copy ∉ writeSetStmts body
      exact ⟨by simpa using h.1, by simpa using h.2⟩
  | .switch _ _ _, h => by simp [StackV2.forwardAliasStmt] at h
  | .forLoop _ _ _ _, h => by simp [StackV2.forwardAliasStmt] at h
  | .exprStmt _, _ => by simp [StackV2.aliasSelfAssign, writeSetStmt]
  | .break, _ => by simp [StackV2.aliasSelfAssign, writeSetStmt]
  | .continue, _ => by simp [StackV2.aliasSelfAssign, writeSetStmt]
  | .leave, _ => by simp [StackV2.aliasSelfAssign, writeSetStmt]

private theorem aliasSelfAssign_inv {copy : Ident} {s : Stmt Op}
    (h : StackV2.aliasSelfAssign copy s = true) :
    s = .assign [copy] (.var copy) := by
  cases s with
  | assign xs e =>
      cases xs with
      | nil => simp [StackV2.aliasSelfAssign] at h
      | cons x xs =>
          cases xs with
          | nil =>
              cases e <;> simp [StackV2.aliasSelfAssign] at h
              case var => rcases h with ⟨rfl, rfl⟩; rfl
          | cons y ys => simp [StackV2.aliasSelfAssign] at h
  | _ => simp [StackV2.aliasSelfAssign] at h

private theorem aliasSelfAssign_preserves {source copy : Ident}
    {funs : FunEnv D} {V V' : VEnv D} {st st' : EvmState}
    (hne : source ≠ copy)
    (heq : VEnv.get V source = VEnv.get V copy)
    (h : ExecStmt D funs V st (.assign [copy] (.var copy)) V' st' .normal) :
    VEnv.get V' source = VEnv.get V' copy := by
  cases h with
  | assignVal he hlen =>
      cases he with
      | var hget =>
          simp only at hlen
          rw [VEnv.setMany_singleton, VEnv.set_self hget]
          exact heq

private theorem forwardAliasStmt_preserves {source copy : Ident}
    {s : Stmt Op} {funs : FunEnv D} {V V' : VEnv D} {st st' : EvmState}
    (hne : source ≠ copy)
    (heq : VEnv.get V source = VEnv.get V copy)
    (hkeep : (StackV2.forwardAliasStmt source copy s).2.1 = true)
    (h : ExecStmt D funs V st s V' st' .normal) :
    VEnv.get V' source = VEnv.get V' copy := by
  rcases forwardAliasStmt_keep_inv source copy s hkeep with hself | hfree
  · have hs := aliasSelfAssign_inv hself
    subst s
    exact aliasSelfAssign_preserves hne heq h
  · have hf := YulEvmCompiler.Optimizer.Step.env_frame h rfl
    have hs := hf.get_eq hfree.1
    have hc := hf.get_eq hfree.2
    simp only [codeWriteSet] at hs hc
    rw [hs, hc]
    exact heq

mutual
  theorem useAliasExpr_equivAt {source copy : Ident} {V : VEnv D}
      (heq : VEnv.get V source = VEnv.get V copy) :
      ∀ e funs st r,
        EvalExpr D funs V st e r ↔
          EvalExpr D funs V st (StackV2.useAliasExpr source copy e) r
    | .lit l, funs, st, r => by
        constructor <;> intro h <;> cases h <;> exact Step.lit
    | .var x, funs, st, r => by
        by_cases hx : x = source
        · subst x
          simp only [StackV2.useAliasExpr, if_pos]
          constructor <;> intro h <;> cases h with
          | var hget => exact Step.var (by simpa [heq] using hget)
        · simp only [StackV2.useAliasExpr, if_neg hx]
    | .builtin op args, funs, st, r => by
        simp only [StackV2.useAliasExpr]
        constructor
        · intro h
          cases h with
          | builtinOk hargs hop =>
              exact Step.builtinOk
                ((useAliasArgs_equivAt heq args funs st _).mp hargs) hop
          | builtinHalt hargs hop =>
              exact Step.builtinHalt
                ((useAliasArgs_equivAt heq args funs st _).mp hargs) hop
          | builtinArgsHalt hargs =>
              exact Step.builtinArgsHalt
                ((useAliasArgs_equivAt heq args funs st _).mp hargs)
        · intro h
          cases h with
          | builtinOk hargs hop =>
              exact Step.builtinOk
                ((useAliasArgs_equivAt heq args funs st _).mpr hargs) hop
          | builtinHalt hargs hop =>
              exact Step.builtinHalt
                ((useAliasArgs_equivAt heq args funs st _).mpr hargs) hop
          | builtinArgsHalt hargs =>
              exact Step.builtinArgsHalt
                ((useAliasArgs_equivAt heq args funs st _).mpr hargs)
    | .call fn args, funs, st, r => by
        simp only [StackV2.useAliasExpr]
        constructor
        · intro h
          cases h with
          | callOk hargs hl hlen hbody ho =>
              exact Step.callOk
                ((useAliasArgs_equivAt heq args funs st _).mp hargs)
                hl hlen hbody ho
          | callHalt hargs hl hlen hbody =>
              exact Step.callHalt
                ((useAliasArgs_equivAt heq args funs st _).mp hargs)
                hl hlen hbody
          | callArgsHalt hargs =>
              exact Step.callArgsHalt
                ((useAliasArgs_equivAt heq args funs st _).mp hargs)
        · intro h
          cases h with
          | callOk hargs hl hlen hbody ho =>
              exact Step.callOk
                ((useAliasArgs_equivAt heq args funs st _).mpr hargs)
                hl hlen hbody ho
          | callHalt hargs hl hlen hbody =>
              exact Step.callHalt
                ((useAliasArgs_equivAt heq args funs st _).mpr hargs)
                hl hlen hbody
          | callArgsHalt hargs =>
              exact Step.callArgsHalt
                ((useAliasArgs_equivAt heq args funs st _).mpr hargs)

  theorem useAliasArgs_equivAt {source copy : Ident} {V : VEnv D}
      (heq : VEnv.get V source = VEnv.get V copy) :
      ∀ args funs st r,
        EvalArgs D funs V st args r ↔
          EvalArgs D funs V st (StackV2.useAliasArgs source copy args) r
    | [], funs, st, r => by
        constructor <;> intro h <;> cases h <;> exact Step.argsNil
    | e :: rest, funs, st, r => by
        simp only [StackV2.useAliasArgs]
        constructor
        · intro h
          cases h with
          | argsCons hrest he =>
              exact Step.argsCons
                ((useAliasArgs_equivAt heq rest funs st _).mp hrest)
                ((useAliasExpr_equivAt heq e funs _ _).mp he)
          | argsRestHalt hrest =>
              exact Step.argsRestHalt
                ((useAliasArgs_equivAt heq rest funs st _).mp hrest)
          | argsHeadHalt hrest he =>
              exact Step.argsHeadHalt
                ((useAliasArgs_equivAt heq rest funs st _).mp hrest)
                ((useAliasExpr_equivAt heq e funs _ _).mp he)
        · intro h
          cases h with
          | argsCons hrest he =>
              exact Step.argsCons
                ((useAliasArgs_equivAt heq rest funs st _).mpr hrest)
                ((useAliasExpr_equivAt heq e funs _ _).mpr he)
          | argsRestHalt hrest =>
              exact Step.argsRestHalt
                ((useAliasArgs_equivAt heq rest funs st _).mpr hrest)
          | argsHeadHalt hrest he =>
              exact Step.argsHeadHalt
                ((useAliasArgs_equivAt heq rest funs st _).mpr hrest)
                ((useAliasExpr_equivAt heq e funs _ _).mpr he)
end

mutual
  private theorem forwardAliasStmt_equivAt {source copy : Ident} {V : VEnv D}
      (hne : source ≠ copy) (heq : VEnv.get V source = VEnv.get V copy) :
      ∀ (s : Stmt Op) funs st V' st' o,
        ExecStmt D funs V st s V' st' o ↔
          ExecStmt D funs V st (StackV2.forwardAliasStmt source copy s).1
            V' st' o
    | .block body, funs, st, V', st', o => by
        simp only [StackV2.forwardAliasStmt]
        have hh := forwardAliasStmts_hoist
          (calls := calls) (creates := creates) source copy body
        constructor
        · intro h
          cases h with
          | block hb =>
              apply Step.block
              rw [hh]
              exact (forwardAliasStmts_equivAt hne heq body _ _ _ _ _).mp hb
        · intro h
          cases h with
          | block hb =>
              apply Step.block
              rw [hh] at hb
              exact (forwardAliasStmts_equivAt hne heq body _ _ _ _ _).mpr hb
    | .funDef f ps rs body, funs, st, V', st', o => by
        simp only [StackV2.forwardAliasStmt]
    | .letDecl xs none, funs, st, V', st', o => by
        simp only [StackV2.forwardAliasStmt, Option.map]
    | .letDecl xs (some e), funs, st, V', st', o => by
        simp only [StackV2.forwardAliasStmt, Option.map]
        constructor
        · intro h
          cases h with
          | letVal he hlen =>
              exact Step.letVal
                ((useAliasExpr_equivAt heq e funs st _).mp he) hlen
          | letHalt he =>
              exact Step.letHalt
                ((useAliasExpr_equivAt heq e funs st _).mp he)
        · intro h
          cases h with
          | letVal he hlen =>
              exact Step.letVal
                ((useAliasExpr_equivAt heq e funs st _).mpr he) hlen
          | letHalt he =>
              exact Step.letHalt
                ((useAliasExpr_equivAt heq e funs st _).mpr he)
    | .assign xs e, funs, st, V', st', o => by
        simp only [StackV2.forwardAliasStmt]
        constructor
        · intro h
          cases h with
          | assignVal he hlen =>
              exact Step.assignVal
                ((useAliasExpr_equivAt heq e funs st _).mp he) hlen
          | assignHalt he =>
              exact Step.assignHalt
                ((useAliasExpr_equivAt heq e funs st _).mp he)
        · intro h
          cases h with
          | assignVal he hlen =>
              exact Step.assignVal
                ((useAliasExpr_equivAt heq e funs st _).mpr he) hlen
          | assignHalt he =>
              exact Step.assignHalt
                ((useAliasExpr_equivAt heq e funs st _).mpr he)
    | .cond c body, funs, st, V', st', o => by
        simp only [StackV2.forwardAliasStmt]
        have hh := forwardAliasStmts_hoist
          (calls := calls) (creates := creates) source copy body
        constructor
        · intro h
          cases h with
          | @ifTrue _ _ _ _ _ _ st1 _ _ _ hc hn hbody =>
              have hbody' : ExecStmt D funs V st1
                  (.block (StackV2.forwardAliasStmts source copy body).1)
                  V' st' o := by
                cases hbody with
                | block hb =>
                    apply Step.block
                    rw [hh]
                    exact (forwardAliasStmts_equivAt hne heq body _ _ _ _ _).mp hb
              exact Step.ifTrue
                ((useAliasExpr_equivAt heq c funs st _).mp hc) hn
                hbody'
          | ifFalse hc hz =>
              exact Step.ifFalse
                ((useAliasExpr_equivAt heq c funs st _).mp hc) hz
          | ifHalt hc =>
              exact Step.ifHalt
                ((useAliasExpr_equivAt heq c funs st _).mp hc)
        · intro h
          cases h with
          | @ifTrue _ _ _ _ _ _ st1 _ _ _ hc hn hbody =>
              have hbody' : ExecStmt D funs V st1 (.block body) V' st' o := by
                cases hbody with
                | block hb =>
                    apply Step.block
                    rw [hh] at hb
                    exact (forwardAliasStmts_equivAt hne heq body _ _ _ _ _).mpr hb
              exact Step.ifTrue
                ((useAliasExpr_equivAt heq c funs st _).mpr hc) hn
                hbody'
          | ifFalse hc hz =>
              exact Step.ifFalse
                ((useAliasExpr_equivAt heq c funs st _).mpr hc) hz
          | ifHalt hc =>
              exact Step.ifHalt
                ((useAliasExpr_equivAt heq c funs st _).mpr hc)
    | .switch c cases dflt, funs, st, V', st', o => by
        simp only [StackV2.forwardAliasStmt]
    | .forLoop init c post body, funs, st, V', st', o => by
        simp only [StackV2.forwardAliasStmt]
    | .exprStmt e, funs, st, V', st', o => by
        simp only [StackV2.forwardAliasStmt]
        constructor
        · intro h
          cases h with
          | exprStmt he =>
              exact Step.exprStmt
                ((useAliasExpr_equivAt heq e funs st _).mp he)
          | exprStmtHalt he =>
              exact Step.exprStmtHalt
                ((useAliasExpr_equivAt heq e funs st _).mp he)
        · intro h
          cases h with
          | exprStmt he =>
              exact Step.exprStmt
                ((useAliasExpr_equivAt heq e funs st _).mpr he)
          | exprStmtHalt he =>
              exact Step.exprStmtHalt
                ((useAliasExpr_equivAt heq e funs st _).mpr he)
    | .break, funs, st, V', st', o => by
        simp only [StackV2.forwardAliasStmt]
    | .continue, funs, st, V', st', o => by
        simp only [StackV2.forwardAliasStmt]
    | .leave, funs, st, V', st', o => by
        simp only [StackV2.forwardAliasStmt]
    termination_by s funs st V' st' o => 2 * sizeOf s

  private theorem forwardAliasStmts_equivAt {source copy : Ident} {V : VEnv D}
      (hne : source ≠ copy) (heq : VEnv.get V source = VEnv.get V copy) :
      ∀ (body : Block Op) funs st V' st' o,
        ExecStmts D funs V st body V' st' o ↔
          ExecStmts D funs V st (StackV2.forwardAliasStmts source copy body).1
            V' st' o
    | [], funs, st, V', st', o => by
        simp only [StackV2.forwardAliasStmts]
    | s :: rest, funs, st, V', st', o => by
        rw [StackV2.forwardAliasStmts]
        generalize hr : StackV2.forwardAliasStmt source copy s = r
        obtain ⟨s', keep, changed⟩ := r
        dsimp only
        have hhead : ∀ V1 st1 o1,
            ExecStmt D funs V st s V1 st1 o1 ↔
              ExecStmt D funs V st s' V1 st1 o1 := by
          intro V1 st1 o1
          have h := forwardAliasStmt_equivAt hne heq s funs st V1 st1 o1
          simpa [hr] using h
        cases keep with
        | false =>
            simp only [Bool.false_eq_true, if_false]
            constructor
            · intro h
              cases h with
              | seqCons hs hrest => exact Step.seqCons ((hhead _ _ _).mp hs) hrest
              | seqStop hs hn => exact Step.seqStop ((hhead _ _ _).mp hs) hn
            · intro h
              cases h with
              | seqCons hs hrest => exact Step.seqCons ((hhead _ _ _).mpr hs) hrest
              | seqStop hs hn => exact Step.seqStop ((hhead _ _ _).mpr hs) hn
        | true =>
            simp only [if_true]
            constructor
            · intro h
              cases h with
              | seqCons hs hrest =>
                  have heq1 := forwardAliasStmt_preserves hne heq
                    (s := s) (by simpa [hr]) hs
                  exact Step.seqCons ((hhead _ _ _).mp hs)
                    ((forwardAliasStmts_equivAt hne heq1 rest _ _ _ _ _).mp hrest)
              | seqStop hs hn => exact Step.seqStop ((hhead _ _ _).mp hs) hn
            · intro h
              cases h with
              | seqCons hs hrest =>
                  have hs' := (hhead _ _ _).mpr hs
                  have heq1 := forwardAliasStmt_preserves hne heq
                    (s := s) (by simpa [hr]) hs'
                  exact Step.seqCons hs'
                    ((forwardAliasStmts_equivAt hne heq1 rest _ _ _ _ _).mpr hrest)
              | seqStop hs hn => exact Step.seqStop ((hhead _ _ _).mpr hs) hn
    termination_by body funs st V' st' o => 2 * sizeOf body + 1
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

def mapFunBodies (f : List Ident → List Ident → Block Op → Block Op) :
    Block Op → Block Op
  | [] => []
  | .funDef n ps rs body :: rest =>
      .funDef n ps rs (f ps rs body) :: mapFunBodies f rest
  | s :: rest => s :: mapFunBodies f rest

private theorem mapFunBodies_stmts
    (f : List Ident → List Ident → Block Op → Block Op) :
    ∀ b, EquivStmts D b (mapFunBodies f b) := by
  intro b
  apply EquivStmts.of_forall₂
  induction b with
  | nil => exact .nil
  | cons s rest ih =>
      cases s with
      | funDef n ps rs body =>
          apply List.Forall₂.cons
          · intro funs V st V' st' o
            constructor <;> intro h <;> cases h <;> exact Step.funDef
          · exact ih
      | _ =>
          exact .cons (fun _ _ _ _ _ _ => Iff.rfl) ih

private theorem mapFunBodies_scope
    (f : List Ident → List Ident → Block Op → Block Op)
    (hf : ∀ ps rs body,
      BoundEquivBlock D (ps ++ rs) body (f ps rs body)) :
    ∀ b, BoundScopeRel D (hoist D b) (hoist D (mapFunBodies f b)) := by
  intro b
  induction b with
  | nil => exact .nil
  | cons s rest ih =>
      cases s with
      | funDef n ps rs body =>
          exact .cons ⟨rfl, rfl, rfl, hf ps rs body⟩ ih
      | _ =>
          simpa [mapFunBodies, hoist] using ih

theorem mapFunBodies_equiv
    (f : List Ident → List Ident → Block Op → Block Op)
    (hf : ∀ ps rs body,
      BoundEquivBlock D (ps ++ rs) body (f ps rs body)) (b : Block Op) :
    EquivBlock D b (mapFunBodies f b) :=
  EquivBlock.of_stmts_bound_funs (mapFunBodies_stmts f b)
    (mapFunBodies_scope f hf b)

theorem identityPEnv_compat {bound : List Ident} {V : VEnv D}
    (hb : BoundOK V bound) : Compat V (StackV2.identityPEnv bound) := by
  intro p hp
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
  obtain ⟨v, hv⟩ := VEnv.get_isSome_of_key (hb x hx)
  exact ⟨v, hv, hv⟩

theorem seededProp_bound (bound : List Ident) (body : Block Op) :
    BoundEquivBlock D bound body
      (propStmts true (StackV2.identityPEnv bound) body).1 := by
  intro funs V st hb
  let σ := StackV2.identityPEnv bound
  let body' := (propStmts true σ body).1
  have hrel : PropRel σ (propStmts true σ body).2
      (.stmts body) (.stmts body') := propStmts_rel true σ body
  have hscope : PScopeRel (calls := calls) (creates := creates)
      (hoist D body) (hoist D body') :=
    PropRel.hoist_scopeRel (calls := calls) (creates := creates) hrel rfl rfl
  have hbmem : YulEvmCompiler.Optimizer.BoundOK V bound := by
    intro x hx
    change V.map Prod.fst = bound at hb
    rw [hb]
    exact hx
  have hc : Compat V σ := identityPEnv_compat hbmem
  have hF : PFunsRel (hoist D body :: funs) (hoist D body' :: funs) :=
    .cons hscope (PFunsRel.refl funs)
  constructor
  · intro V' st' o _
    constructor
    · intro h
      cases h with
      | block hs => exact Step.block (prop_fwd hs hF hrel hc).1
    · intro h
      cases h with
      | block hs => exact Step.block (prop_bwd hs hF hrel hc)
  · intro st'
    constructor
    · rintro ⟨Vh, h⟩
      refine ⟨Vh, ?_⟩
      cases h with
      | block hs => exact Step.block (prop_fwd hs hF hrel hc).1
    · rintro ⟨Vh, h⟩
      refine ⟨Vh, ?_⟩
      cases h with
      | block hs => exact Step.block (prop_bwd hs hF hrel hc)

theorem iterateSeededProp_bound (n : Nat) (bound : List Ident) (body : Block Op) :
    BoundEquivBlock D bound body (StackV2.iterateSeededProp n bound body) := by
  induction n generalizing body with
  | zero => exact BoundEquivBlock.refl _ _
  | succ n ih =>
      rw [StackV2.iterateSeededProp]
      exact (seededProp_bound bound body).trans
        (ih (propStmts true (StackV2.identityPEnv bound) body).1)

theorem exists_mins_append (pre base : VEnv D) :
    ∃ ins, MIns ins (pre ++ base) base ∧
      (∀ p ∈ ins, p.2 ∈ pre.map Prod.fst) ∧
      (∀ p ∈ ins, base.length ≤ p.1) := by
  induction pre with
  | nil => exact ⟨[], .nil _, by simp, by simp⟩
  | cons q rest ih =>
      obtain ⟨x, v⟩ := q
      obtain ⟨ins, hm, hnames, hdepth⟩ := ih
      refine ⟨((rest ++ base).length, x) :: ins, hm.insTop x v, ?_, ?_⟩
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · simp
        · exact List.mem_cons_of_mem _ (hnames p hp)
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · simp
        · exact hdepth p hp

theorem normal_prefix_mins {pre : Block Op} {funs : FunEnv D}
    {V Vp : VEnv D} {st stp : EvmState}
    (hp : Step D funs V st (.stmts pre) (.sres Vp stp .normal)) :
    ∃ ins, MIns ins Vp (restore V Vp) ∧
      (∀ p ∈ ins, p.2 ∈ stmtsBinds pre) ∧
      (∀ p ∈ ins, V.length ≤ p.1) := by
  have hkeys := stmts_normal_keys hp
  let n := (stmtsBinds pre).length
  have hlen : Vp.length - V.length = n := by
    have hklen := congrArg List.length hkeys
    simp only [List.length_map, List.length_append] at hklen
    simp [n]
    omega
  have hsplit : Vp = Vp.take n ++ Vp.drop n :=
    (List.take_append_drop n Vp).symm
  obtain ⟨ins, hm0, hnames0, hdepth0⟩ :=
    exists_mins_append (Vp.take n) (Vp.drop n)
  have htake : (Vp.take n).map Prod.fst = stmtsBinds pre := by
    rw [List.map_take, hkeys]
    simp [n]
  have hm : MIns ins Vp (restore V Vp) := by
    rw [restore, hlen, hsplit]
    simpa using hm0
  refine ⟨ins, hm, ?_, ?_⟩
  · intro p hpins
    rw [← htake]
    exact hnames0 p hpins
  · intro p hpins
    have hd := hdepth0 p hpins
    have hdrop : (Vp.drop n).length = V.length := by
      rw [List.length_drop]
      have hklen := congrArg List.length hkeys
      simp only [List.length_map, List.length_append] at hklen
      simp [n]
      omega
    rwa [hdrop] at hd

theorem scopePrefix_equivBlock {pre rest : Block Op}
    (hfun : hasDirectFun pre = false)
    (hfree : ∀ x ∈ stmtsBinds pre, stmtsMentions x rest = false) :
    EquivBlock D (pre ++ rest) (.block pre :: rest) := by
  have hhoist : hoist D pre = [] := hoist_nil_of_no_direct_fun pre hfun
  have hh : hoist D (pre ++ rest) = hoist D (.block pre :: rest) := by
    rw [hoist_append, hhoist]
    rfl
  intro funs V st V' st' o
  constructor
  · intro hrun
    cases hrun with
    | block hb =>
      rw [hh] at hb
      rcases stmts_append_fwd hb with ⟨Vp, stp, hp, hr⟩ | ⟨hne, hp⟩
      · have hkeys := stmts_normal_keys hp
        let n := (stmtsBinds pre).length
        have hlen : Vp.length - V.length = n := by
          have hklen := congrArg List.length hkeys
          simp only [List.length_map, List.length_append] at hklen
          simp [n]
          omega
        have hsplit : Vp = Vp.take n ++ Vp.drop n :=
          (List.take_append_drop n Vp).symm
        obtain ⟨ins, hm0, hnames0, hdepth0⟩ :=
          exists_mins_append (Vp.take n) (Vp.drop n)
        have htake : (Vp.take n).map Prod.fst = stmtsBinds pre := by
          rw [List.map_take, hkeys]
          simp [n]
        have hm : MIns ins Vp (restore V Vp) := by
          rw [restore, hlen, hsplit]
          simpa using hm0
        have hnames : ∀ p ∈ ins, p.2 ∈ stmtsBinds pre := by
          intro p hpins
          rw [← htake]
          exact hnames0 p hpins
        have hdepth : ∀ p ∈ ins, V.length ≤ p.1 := by
          intro p hpins
          have hd := hdepth0 p hpins
          have hdrop : (Vp.drop n).length = V.length := by
            rw [List.length_drop]
            have hklen := congrArg List.length hkeys
            simp only [List.length_map, List.length_append] at hklen
            simp [n]
            omega
          rwa [hdrop] at hd
        have hifree : InsFree ins (.stmts rest) := by
          intro p hpins
          simpa [codeMentions] using hfree p.2 (hnames p hpins)
        obtain ⟨Vr, hr', hm'⟩ := hm.frameRemove hr hifree
        have hp' := Step.emptyScope_congr hp (.add _)
        have hp'' : Step D (hoist D pre :: hoist D (.block pre :: rest) :: funs)
            V st (.stmts pre) (.sres Vp stp .normal) := by
          simpa [hhoist] using hp'
        have hblock : Step D (hoist D (.block pre :: rest) :: funs) V st
            (.stmt (.block pre)) (.sres (restore V Vp) stp .normal) := by
          exact Step.block hp''
        have htarget := Step.seqCons hblock hr'
        have herase := MIns.restore (MIns.nil V) (by simpa using hm') hdepth
        rw [herase.nil_eq]
        exact Step.block htarget
      · have hp' := Step.emptyScope_congr hp (.add _)
        rw [← hhoist] at hp'
        have hblock := Step.block hp'
        have hseq := @Step.seqStop D inferInstance
          (hoist D (.block pre :: rest) :: funs) V st (.block pre) rest
          _ st' o hblock hne
        have htarget := Step.block hseq
        have hlen := venvLen_mono hp rfl
        rw [restore_restore (Nat.le_refl _) hlen] at htarget
        exact htarget
  · intro hrun
    cases hrun with
    | block hb =>
      rw [← hh] at hb
      cases hb with
      | seqCons hblock hr =>
        cases hblock with
        | block hp =>
          rw [hhoist] at hp
          have hp' := Step.emptyScope_congr hp (.drop _)
          obtain ⟨ins, hm, hnames, hdepth⟩ := normal_prefix_mins hp'
          have hifree : InsFree ins (.stmts rest) := by
            intro p hpins
            simpa [codeMentions] using hfree p.2 (hnames p hpins)
          obtain ⟨Vr, hr', hm'⟩ := hm.frameAdd hr hifree
          have hsource := stmts_append_normal hp' hr'
          have herase := MIns.restore (MIns.nil V) (by simpa using hm') hdepth
          rw [← herase.nil_eq]
          exact Step.block hsource
      | seqStop hblock hne =>
        cases hblock with
        | block hp =>
          rw [hhoist] at hp
          have hp' := Step.emptyScope_congr hp (.drop _)
          have hsource := Step.block (stmts_append_early (suf := rest) hp' hne)
          have hlen := venvLen_mono hp' rfl
          rw [restore_restore (Nat.le_refl _) hlen]
          exact hsource

theorem scopePrefix_after_equivBlock {outer pre rest : Block Op}
    (hfun : hasDirectFun pre = false)
    (hfree : ∀ x ∈ stmtsBinds pre, stmtsMentions x rest = false) :
    EquivBlock D (outer ++ (pre ++ rest))
      (outer ++ (.block pre :: rest)) := by
  have hhoist : hoist D pre = [] := hoist_nil_of_no_direct_fun pre hfun
  have hh : hoist D (outer ++ (pre ++ rest)) =
      hoist D (outer ++ (.block pre :: rest)) := by
    simp only [hoist_append]
    rw [hhoist]
    simp [hoist]
  intro funs V st V' st' o
  constructor
  · intro hrun
    cases hrun with
    | block hb =>
      rw [hh] at hb
      rcases stmts_append_fwd hb with
        ⟨Vo, sto, ho, hsuf⟩ | ⟨hneOuter, ho⟩
      · rcases stmts_append_fwd hsuf with
          ⟨Vp, stp, hp, hr⟩ | ⟨hne, hp⟩
        · obtain ⟨ins, hm, hnames, hdepthVo⟩ := normal_prefix_mins hp
          have hifree : InsFree ins (.stmts rest) := by
            intro p hpins
            simpa [codeMentions] using hfree p.2 (hnames p hpins)
          obtain ⟨Vr, hr', hm'⟩ := hm.frameRemove hr hifree
          have hp' := Step.emptyScope_congr hp (.add _)
          have hp'' : Step D
              (hoist D pre :: hoist D (outer ++ .block pre :: rest) :: funs)
              Vo sto (.stmts pre) (.sres Vp stp .normal) := by
            simpa [hhoist] using hp'
          have hblock : Step D (hoist D (outer ++ .block pre :: rest) :: funs)
              Vo sto (.stmt (.block pre))
              (.sres (restore Vo Vp) stp .normal) := Step.block hp''
          have htarget := Step.block
            (stmts_append_normal ho (Step.seqCons hblock hr'))
          have hVo : V.length ≤ Vo.length := venvLen_mono ho rfl
          have hdepth : ∀ p ∈ ins, V.length ≤ p.1 :=
            fun p hpins => hVo.trans (hdepthVo p hpins)
          have herase := MIns.restore (MIns.nil V) (by simpa using hm') hdepth
          rw [herase.nil_eq]
          exact htarget
        · have hp' := Step.emptyScope_congr hp (.add _)
          rw [← hhoist] at hp'
          have hblock := Step.block hp'
          have hseq := @Step.seqStop D inferInstance
            (hoist D (outer ++ .block pre :: rest) :: funs) Vo sto
            (.block pre) rest _ st' o hblock hne
          have htarget := Step.block (stmts_append_normal ho hseq)
          have hVo : V.length ≤ Vo.length := venvLen_mono ho rfl
          have hVp := venvLen_mono hp rfl
          rw [restore_restore hVo hVp] at htarget
          exact htarget
      · exact Step.block (stmts_append_early (suf := .block pre :: rest) ho hneOuter)
  · intro hrun
    cases hrun with
    | block hb =>
      rw [← hh] at hb
      rcases stmts_append_fwd hb with
        ⟨Vo, sto, ho, hsuf⟩ | ⟨hneOuter, ho⟩
      · cases hsuf with
        | seqCons hblock hr =>
          cases hblock with
          | block hp =>
            rw [hhoist] at hp
            have hp' := Step.emptyScope_congr hp (.drop _)
            obtain ⟨ins, hm, hnames, hdepthVo⟩ := normal_prefix_mins hp'
            have hifree : InsFree ins (.stmts rest) := by
              intro p hpins
              simpa [codeMentions] using hfree p.2 (hnames p hpins)
            obtain ⟨Vr, hr', hm'⟩ := hm.frameAdd hr hifree
            have hsource := Step.block
              (stmts_append_normal ho (stmts_append_normal hp' hr'))
            have hVo : V.length ≤ Vo.length := venvLen_mono ho rfl
            have hdepth : ∀ p ∈ ins, V.length ≤ p.1 :=
              fun p hpins => hVo.trans (hdepthVo p hpins)
            have herase := MIns.restore (MIns.nil V) (by simpa using hm') hdepth
            rw [← herase.nil_eq]
            exact hsource
        | seqStop hblock hne =>
          cases hblock with
          | block hp =>
            rw [hhoist] at hp
            have hp' := Step.emptyScope_congr hp (.drop _)
            have hsource := Step.block
              (stmts_append_normal ho
                (stmts_append_early (suf := rest) hp' hne))
            have hVo : V.length ≤ Vo.length := venvLen_mono ho rfl
            have hVp := venvLen_mono hp' rfl
            rw [restore_restore hVo hVp]
            exact hsource
      · exact Step.block
          (stmts_append_early (suf := pre ++ rest) ho hneOuter)

theorem directDecls_mem_iff (x : Ident) : ∀ body : Block Op,
    x ∈ StackV2.directDecls body ↔ x ∈ stmtsBinds body
  | [] => by simp [StackV2.directDecls, stmtsBinds]
  | s :: rest => by
      cases s with
      | letDecl vars val =>
          simp [StackV2.directDecls, stmtsBinds, stmtBinds,
            directDecls_mem_iff x rest, or_comm]
      | _ =>
          simp [StackV2.directDecls, stmtsBinds, stmtBinds,
            directDecls_mem_iff x rest]

theorem deadPrefixSearch_sound : ∀ outer pre rest out,
    StackV2.deadPrefixSearch pre rest = some out →
      EquivBlock D (outer ++ (pre ++ rest)) (outer ++ out)
  | _, _, [], _, h => by simp [StackV2.deadPrefixSearch] at h
  | outer, pre, s :: rest, out, h => by
      rw [StackV2.deadPrefixSearch] at h
      let pre' := pre ++ [s]
      let names := StackV2.directDecls pre'
      split at h
      · next hcond =>
        cases h
        change ((((!rest.isEmpty && !names.isEmpty) && decide names.Nodup) &&
          names.all (fun x => !stmtsMentions x rest)) &&
          !hasDirectFun pre') = true at hcond
        simp only [Bool.and_eq_true] at hcond
        rcases hcond with ⟨⟨⟨⟨_, _⟩, _⟩, hall⟩, hfun0⟩
        have hfun : hasDirectFun pre' = false := by
          simpa using hfun0
        have hfree : ∀ x ∈ stmtsBinds pre', stmtsMentions x rest = false := by
          intro x hx
          have hx' : x ∈ names := by
            rw [directDecls_mem_iff]
            exact hx
          have hxall := List.all_eq_true.mp hall x hx'
          simpa using hxall
        simpa [pre', List.append_assoc] using
          scopePrefix_after_equivBlock (calls := calls) (creates := creates)
            (outer := outer) hfun hfree
      · next hcond =>
        have ih := deadPrefixSearch_sound outer pre' rest out h
        simpa [pre', List.append_assoc] using ih

theorem scopeDeadPrefixHere_sound {body out : Block Op}
    (h : StackV2.scopeDeadPrefixHere body = some out) :
    EquivBlock D body out := by
  simpa using deadPrefixSearch_sound [] [] body out h

theorem scopeDeadPrefixHere_after_sound {body out : Block Op}
    (h : StackV2.scopeDeadPrefixHere body = some out) (pre : Block Op) :
    EquivBlock D (pre ++ body) (pre ++ out) := by
  simpa using deadPrefixSearch_sound pre [] body out h

theorem iterateDeadPrefixesHere_equiv (n : Nat) (body : Block Op) :
    EquivBlock D body (StackV2.iterateDeadPrefixesHere n body) := by
  induction n generalizing body with
  | zero => exact EquivBlock.refl _
  | succ n ih =>
      rw [StackV2.iterateDeadPrefixesHere]
      cases h : StackV2.scopeDeadPrefixHere body with
      | none => exact EquivBlock.refl _
      | some out => exact (scopeDeadPrefixHere_sound h).trans (ih out)

mutual
  theorem scopeOneDeadPrefixStmt_sound : ∀ (s s' : Stmt Op),
      StackV2.scopeOneDeadPrefixStmt s = some s' →
      EquivStmt D s s' ∧ ScopeRel D (hoist D [s]) (hoist D [s'])
    | .block body, s', h => by
        simp only [StackV2.scopeOneDeadPrefixStmt] at h
        obtain ⟨body', hb, hs'⟩ := Option.map_eq_some_iff.mp h
        subst s'
        exact ⟨scopeOneDeadPrefixStmts_sound body _ hb [], ScopeRel.refl _⟩
    | .funDef f ps rs body, s', h => by
        simp only [StackV2.scopeOneDeadPrefixStmt] at h
        obtain ⟨body', hb, hs'⟩ := Option.map_eq_some_iff.mp h
        subst s'
        have heq := scopeOneDeadPrefixStmts_sound body _ hb []
        refine ⟨funDef_equiv f ps rs body body', ?_⟩
        exact .cons ⟨rfl, rfl, rfl, heq⟩ .nil
    | .cond c body, s', h => by
        simp only [StackV2.scopeOneDeadPrefixStmt] at h
        obtain ⟨body', hb, hs'⟩ := Option.map_eq_some_iff.mp h
        subst s'
        exact ⟨EquivStmt.cond_congr (fun _ _ _ _ => Iff.rfl)
          (scopeOneDeadPrefixStmts_sound body _ hb []), ScopeRel.refl _⟩
    | .switch c cases dflt, s', h => by
        unfold StackV2.scopeOneDeadPrefixStmt at h
        cases hc : StackV2.scopeOneDeadPrefixCases cases with
        | some cases' =>
            simp only [hc] at h
            cases h
            exact ⟨EquivStmt.switch_congr (fun _ _ _ _ => Iff.rfl)
              (scopeOneDeadPrefixCases_sound cases _ hc)
              (EquivBlock.refl _), ScopeRel.refl _⟩
        | none =>
            simp only [hc] at h
            cases dflt with
            | some body =>
                obtain ⟨body', hb, hs'⟩ := Option.map_eq_some_iff.mp h
                subst s'
                exact ⟨EquivStmt.switch_congr (fun _ _ _ _ => Iff.rfl)
                  (tail_forall₂_refl_cases cases)
                  (scopeOneDeadPrefixStmts_sound body _ hb []), ScopeRel.refl _⟩
            | none => simp at h
    | .forLoop init c post body, s', h => by
        unfold StackV2.scopeOneDeadPrefixStmt at h
        cases hp : StackV2.scopeOneDeadPrefixStmts post with
        | some post' =>
            simp only [hp] at h
            cases h
            exact ⟨EquivStmt.forLoop_congr init (fun _ _ _ _ => Iff.rfl)
              (scopeOneDeadPrefixStmts_sound post _ hp [])
              (EquivBlock.refl _), ScopeRel.refl _⟩
        | none =>
            simp only [hp] at h
            obtain ⟨body', hb, hs'⟩ := Option.map_eq_some_iff.mp h
            subst s'
            exact ⟨EquivStmt.forLoop_congr init (fun _ _ _ _ => Iff.rfl)
              (EquivBlock.refl _)
              (scopeOneDeadPrefixStmts_sound body _ hb []), ScopeRel.refl _⟩
    | .letDecl _ _, _, h => by simp [StackV2.scopeOneDeadPrefixStmt] at h
    | .assign _ _, _, h => by simp [StackV2.scopeOneDeadPrefixStmt] at h
    | .exprStmt _, _, h => by simp [StackV2.scopeOneDeadPrefixStmt] at h
    | .break, _, h => by simp [StackV2.scopeOneDeadPrefixStmt] at h
    | .continue, _, h => by simp [StackV2.scopeOneDeadPrefixStmt] at h
    | .leave, _, h => by simp [StackV2.scopeOneDeadPrefixStmt] at h
    termination_by s s' _h => 2 * sizeOf s

  theorem scopeOneDeadPrefixStmts_sound : ∀ (ss ss' : Block Op),
      StackV2.scopeOneDeadPrefixStmts ss = some ss' →
      ∀ pre : Block Op, EquivBlock D (pre ++ ss) (pre ++ ss')
    | [], _, h => by simp [StackV2.scopeOneDeadPrefixStmts] at h
    | s :: rest, ss', h => by
        unfold StackV2.scopeOneDeadPrefixStmts at h
        cases hh : StackV2.scopeDeadPrefixHere (s :: rest) with
        | some target =>
            rw [hh] at h
            cases h
            exact scopeDeadPrefixHere_after_sound hh
        | none =>
            rw [hh] at h
            cases hs : StackV2.scopeOneDeadPrefixStmt s with
            | some s' =>
                simp only [hs] at h
                cases h
                intro pre
                obtain ⟨heq, hscope⟩ := scopeOneDeadPrefixStmt_sound s s' hs
                exact replaceStmt_equivBlock heq hscope pre
            | none =>
                simp only [hs] at h
                obtain ⟨rest', hr, htarget⟩ := Option.map_eq_some_iff.mp h
                subst ss'
                intro pre
                have heq := scopeOneDeadPrefixStmts_sound rest rest' hr (pre ++ [s])
                simpa only [List.append_assoc, List.cons_append, List.nil_append]
                  using heq
    termination_by ss ss' _h => 2 * sizeOf ss + 1

  theorem scopeOneDeadPrefixCases_sound : ∀
      (cases cases' : List (Literal × Block Op)),
      StackV2.scopeOneDeadPrefixCases cases = some cases' →
      List.Forall₂ (fun p q => p.1 = q.1 ∧ EquivBlock D p.2 q.2)
        cases cases'
    | [], _, h => by simp [StackV2.scopeOneDeadPrefixCases] at h
    | (l, body) :: rest, cases', h => by
        unfold StackV2.scopeOneDeadPrefixCases at h
        cases hb : StackV2.scopeOneDeadPrefixStmts body with
        | some body' =>
            simp only [hb] at h
            cases h
            exact .cons ⟨rfl, scopeOneDeadPrefixStmts_sound body _ hb []⟩
              (tail_forall₂_refl_cases rest)
        | none =>
            simp only [hb] at h
            obtain ⟨rest', hr, htarget⟩ := Option.map_eq_some_iff.mp h
            subst cases'
            exact .cons ⟨rfl, EquivBlock.refl _⟩
              (scopeOneDeadPrefixCases_sound rest _ hr)
    termination_by cases cases' _h => 2 * sizeOf cases + 1
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

theorem iterateDeadPrefixes_equiv (n : Nat) (body : Block Op) :
    EquivBlock D body (StackV2.iterateDeadPrefixes n body) := by
  induction n generalizing body with
  | zero => exact EquivBlock.refl _
  | succ n ih =>
      rw [StackV2.iterateDeadPrefixes]
      cases h : StackV2.scopeOneDeadPrefixStmts body with
      | none => exact EquivBlock.refl _
      | some out =>
          exact (scopeOneDeadPrefixStmts_sound body out h []).trans (ih out)

/- The following first-order helpers record the same fuel structure explicitly;
the mutually recursive proof below is the maintained formulation. -/
/-
private theorem scopeDeadCases_of
    (n : Nat)
    (H : ∀ body : Block Op,
      EquivBlock D body (StackV2.scopeDeadPrefixesStmts n body)) :
    ∀ cases : List (Literal × Block Op),
      List.Forall₂ (fun p q => p.1 = q.1 ∧ EquivBlock D p.2 q.2)
        cases (StackV2.scopeDeadPrefixesCases n cases) := by
  intro cases
  cases n with
  | zero => exact tail_forall₂_refl_cases cases
  | succ n =>
      induction cases with
      | nil => exact .nil
      | cons p rest ih =>
          obtain ⟨l, body⟩ := p
          exact .cons ⟨rfl, H body⟩ ih

private theorem scopeDeadDflt_of
    (n : Nat)
    (H : ∀ body : Block Op,
      EquivBlock D body (StackV2.scopeDeadPrefixesStmts n body)) :
    ∀ dflt : Option (Block Op),
      EquivBlock D (dflt.getD [])
        ((StackV2.scopeDeadPrefixesDflt n dflt).getD []) := by
  intro dflt
  cases n <;> cases dflt <;> simp [StackV2.scopeDeadPrefixesDflt]
  exact H _

private theorem scopeDeadStmt_of
    (n : Nat)
    (H : ∀ body : Block Op,
      EquivBlock D body (StackV2.scopeDeadPrefixesStmts n body)) :
    ∀ s : Stmt Op,
      EquivStmt D s (StackV2.scopeDeadPrefixesStmt (n + 1) s) ∧
      ScopeRel D (hoist D [s])
        (hoist D [StackV2.scopeDeadPrefixesStmt (n + 1) s]) := by
  intro s
  cases s with
  | block body => exact ⟨H body, ScopeRel.refl _⟩
  | funDef f ps rs body =>
      exact ⟨funDef_equiv f ps rs body _ (H body),
        .cons ⟨rfl, rfl, rfl, H body⟩ .nil⟩
  | cond c body =>
      exact ⟨EquivStmt.cond_congr (fun _ _ _ _ => Iff.rfl) (H body),
        ScopeRel.refl _⟩
  | switch c cases dflt =>
      exact ⟨EquivStmt.switch_congr (fun _ _ _ _ => Iff.rfl)
        (scopeDeadCases_of n H cases) (scopeDeadDflt_of n H dflt),
        ScopeRel.refl _⟩
  | forLoop init c post body =>
      exact ⟨EquivStmt.forLoop_congr init (fun _ _ _ _ => Iff.rfl)
        (H post) (H body), ScopeRel.refl _⟩
  | letDecl _ _ | assign _ _ | exprStmt _ | «break» | «continue» | «leave» =>
      exact ⟨fun _ _ _ _ _ _ => Iff.rfl, ScopeRel.refl _⟩

private theorem scopeDeadMapStmts_of
    (n : Nat)
    (H : ∀ body : Block Op,
      EquivBlock D body (StackV2.scopeDeadPrefixesStmts n body)) :
    ∀ body : Block Op,
      EquivStmts D body (body.map (StackV2.scopeDeadPrefixesStmt (n + 1))) := by
  intro body
  apply EquivStmts.of_forall₂
  induction body with
  | nil => exact .nil
  | cons s rest ih => exact .cons (scopeDeadStmt_of n H s).1 ih

private theorem scopeDeadMapScope_of
    (n : Nat)
    (H : ∀ body : Block Op,
      EquivBlock D body (StackV2.scopeDeadPrefixesStmts n body)) :
    ∀ body : Block Op,
      ScopeRel D (hoist D body)
        (hoist D (body.map (StackV2.scopeDeadPrefixesStmt (n + 1)))) := by
  intro body
  induction body with
  | nil => exact .nil
  | cons s rest ih =>
      cases s with
      | funDef f ps rs fnBody =>
          exact .cons ⟨rfl, rfl, rfl, H fnBody⟩ ih
      | _ => simpa [hoist, StackV2.scopeDeadPrefixesStmt] using ih

theorem scopeDeadPrefixesStmts_equiv_old (n : Nat) (body : Block Op) :
    EquivBlock D body (StackV2.scopeDeadPrefixesStmts n body) := by
  induction n generalizing body with
  | zero => exact EquivBlock.refl _
  | succ n ih =>
      rw [StackV2.scopeDeadPrefixesStmts]
      let split := StackV2.iterateDeadPrefixesHere 64 body
      have hs := iterateDeadPrefixesHere_equiv (calls := calls) (creates := creates) 64 body
      apply hs.trans
      exact EquivBlock.of_stmts_funs
        (scopeDeadMapStmts_of n ih split)
        (scopeDeadMapScope_of n ih split)
-/

private theorem forall₂_append {α β : Type} {R : α → β → Prop}
    {a b : List α} {c d : List β}
    (h₁ : List.Forall₂ R a c) (h₂ : List.Forall₂ R b d) :
    List.Forall₂ R (a ++ b) (c ++ d) := by
  induction h₁ with
  | nil => exact h₂
  | cons hp _ ih => exact .cons hp ih

mutual
  theorem scopeDeadPrefixesStmt_equiv : ∀ (n : Nat) (s : Stmt Op),
      EquivStmt D s (StackV2.scopeDeadPrefixesStmt n s) ∧
      ScopeRel D (hoist D [s])
        (hoist D [StackV2.scopeDeadPrefixesStmt n s])
    | 0, s => ⟨fun _ _ _ _ _ _ => Iff.rfl, ScopeRel.refl _⟩
    | n + 1, .block body =>
        ⟨scopeDeadPrefixesStmts_equiv n body, ScopeRel.refl _⟩
    | n + 1, .funDef f ps rs body =>
        ⟨funDef_equiv f ps rs body _,
          .cons ⟨rfl, rfl, rfl, scopeDeadPrefixesStmts_equiv n body⟩ .nil⟩
    | n + 1, .cond c body =>
        ⟨EquivStmt.cond_congr (fun _ _ _ _ => Iff.rfl)
          (scopeDeadPrefixesStmts_equiv n body), ScopeRel.refl _⟩
    | n + 1, .switch c cases dflt =>
        ⟨EquivStmt.switch_congr (fun _ _ _ _ => Iff.rfl)
          (scopeDeadPrefixesCases_equiv n cases)
          (scopeDeadPrefixesDflt_equiv n dflt), ScopeRel.refl _⟩
    | n + 1, .forLoop init c post body =>
        ⟨EquivStmt.forLoop_congr init (fun _ _ _ _ => Iff.rfl)
          (scopeDeadPrefixesStmts_equiv n post)
          (scopeDeadPrefixesStmts_equiv n body), ScopeRel.refl _⟩
    | _n + 1, s@(.letDecl _ _) =>
        ⟨fun _ _ _ _ _ _ => Iff.rfl, ScopeRel.refl _⟩
    | _n + 1, s@(.assign _ _) =>
        ⟨fun _ _ _ _ _ _ => Iff.rfl, ScopeRel.refl _⟩
    | _n + 1, s@(.exprStmt _) =>
        ⟨fun _ _ _ _ _ _ => Iff.rfl, ScopeRel.refl _⟩
    | _n + 1, .break =>
        ⟨fun _ _ _ _ _ _ => Iff.rfl, ScopeRel.refl _⟩
    | _n + 1, .continue =>
        ⟨fun _ _ _ _ _ _ => Iff.rfl, ScopeRel.refl _⟩
    | _n + 1, .leave =>
        ⟨fun _ _ _ _ _ _ => Iff.rfl, ScopeRel.refl _⟩

  theorem scopeDeadPrefixesStmts_equiv : ∀ (n : Nat) (body : Block Op),
      EquivBlock D body (StackV2.scopeDeadPrefixesStmts n body)
    | 0, body => EquivBlock.refl _
    | n + 1, body => by
        rw [StackV2.scopeDeadPrefixesStmts]
        let split := StackV2.iterateDeadPrefixes 64 body
        have hs := iterateDeadPrefixes_equiv
          (calls := calls) (creates := creates) 64 body
        apply hs.trans
        change EquivBlock D split
          (split.map (StackV2.scopeDeadPrefixesStmt n))
        have hstmts : EquivStmts D split
            (split.map (StackV2.scopeDeadPrefixesStmt n)) := by
          apply EquivStmts.of_forall₂
          induction split with
          | nil => exact .nil
          | cons s rest ih =>
              exact .cons (scopeDeadPrefixesStmt_equiv n s).1 ih
        have hscope : ScopeRel D (hoist D split)
            (hoist D (split.map (StackV2.scopeDeadPrefixesStmt n))) := by
          induction split with
          | nil => exact .nil
          | cons s rest ih =>
              have hhead := (scopeDeadPrefixesStmt_equiv n s).2
              rw [show s :: rest = [s] ++ rest by rfl, hoist_append]
              change ScopeRel D (hoist D [s] ++ hoist D rest)
                (hoist D ([StackV2.scopeDeadPrefixesStmt n s] ++
                  rest.map (StackV2.scopeDeadPrefixesStmt n)))
              rw [hoist_append]
              exact forall₂_append hhead ih
        exact EquivBlock.of_stmts_funs hstmts hscope

  theorem scopeDeadPrefixesCases_equiv : ∀ (n : Nat)
      (cases : List (Literal × Block Op)),
      List.Forall₂ (fun p q => p.1 = q.1 ∧ EquivBlock D p.2 q.2)
        cases (StackV2.scopeDeadPrefixesCases n cases)
    | 0, cases => tail_forall₂_refl_cases cases
    | _n + 1, [] => .nil
    | n + 1, (l, body) :: rest =>
        .cons ⟨rfl, scopeDeadPrefixesStmts_equiv n body⟩
          (scopeDeadPrefixesCases_equiv n rest)

  theorem scopeDeadPrefixesDflt_equiv : ∀ (n : Nat)
      (dflt : Option (Block Op)),
      EquivBlock D (dflt.getD [])
        ((StackV2.scopeDeadPrefixesDflt n dflt).getD [])
    | 0, none => EquivBlock.refl _
    | 0, some body => EquivBlock.refl _
    | _n + 1, none => EquivBlock.refl _
    | n + 1, some body => scopeDeadPrefixesStmts_equiv n body
end

private theorem propagateFunctionStmts_eq_mapFunBodies : ∀ b : Block Op,
    StackV2.propagateFunctionStmts b = mapFunBodies
      (fun ps rs body => StackV2.iterateSeededProp 64 (ps ++ rs) body) b := by
  intro b
  induction b with
  | nil => rfl
  | cons s rest ih =>
      change List.map StackV2.propagateFunctionStmt rest =
        mapFunBodies (fun ps rs body =>
          StackV2.iterateSeededProp 64 (ps ++ rs) body) rest at ih
      cases s <;> simp [StackV2.propagateFunctionStmts,
        StackV2.propagateFunctionStmt, mapFunBodies, ih]

private theorem scopeDeadFunctionStmts_eq_mapFunBodies : ∀ b : Block Op,
    StackV2.scopeDeadFunctionStmts b =
      mapFunBodies (fun _ _ body => StackV2.scopeDeadPrefixesStmts 64 body) b := by
  intro b
  induction b with
  | nil => rfl
  | cons s rest ih =>
      change List.map StackV2.scopeDeadFunctionStmt rest =
        mapFunBodies (fun _ _ body => StackV2.scopeDeadPrefixesStmts 64 body) rest at ih
      cases s <;> simp [StackV2.scopeDeadFunctionStmts,
        StackV2.scopeDeadFunctionStmt, mapFunBodies, ih]

/- Duplicated earlier so the alias simulation can use it. -/
/-
mutual
  theorem useAliasExpr_equivAt {source copy : Ident} {V : VEnv D}
      (heq : VEnv.get V source = VEnv.get V copy) :
      ∀ e funs st r,
        EvalExpr D funs V st e r ↔
          EvalExpr D funs V st (StackV2.useAliasExpr source copy e) r
    | .lit l, funs, st, r => by
        constructor <;> intro h <;> cases h <;> exact Step.lit
    | .var x, funs, st, r => by
        by_cases hx : x = source
        · subst x
          simp only [StackV2.useAliasExpr, if_pos]
          constructor <;> intro h <;> cases h with
          | var hget => exact Step.var (by simpa [heq] using hget)
        · simp only [StackV2.useAliasExpr, if_neg hx]
    | .builtin op args, funs, st, r => by
        simp only [StackV2.useAliasExpr]
        constructor
        · intro h
          cases h with
          | builtinOk hargs hop =>
              exact Step.builtinOk
                ((useAliasArgs_equivAt heq args funs st _).mp hargs) hop
          | builtinHalt hargs hop =>
              exact Step.builtinHalt
                ((useAliasArgs_equivAt heq args funs st _).mp hargs) hop
          | builtinArgsHalt hargs =>
              exact Step.builtinArgsHalt
                ((useAliasArgs_equivAt heq args funs st _).mp hargs)
        · intro h
          cases h with
          | builtinOk hargs hop =>
              exact Step.builtinOk
                ((useAliasArgs_equivAt heq args funs st _).mpr hargs) hop
          | builtinHalt hargs hop =>
              exact Step.builtinHalt
                ((useAliasArgs_equivAt heq args funs st _).mpr hargs) hop
          | builtinArgsHalt hargs =>
              exact Step.builtinArgsHalt
                ((useAliasArgs_equivAt heq args funs st _).mpr hargs)
    | .call fn args, funs, st, r => by
        simp only [StackV2.useAliasExpr]
        constructor
        · intro h
          cases h with
          | callOk hargs hl hlen hbody ho =>
              exact Step.callOk
                ((useAliasArgs_equivAt heq args funs st _).mp hargs)
                hl hlen hbody ho
          | callHalt hargs hl hlen hbody =>
              exact Step.callHalt
                ((useAliasArgs_equivAt heq args funs st _).mp hargs)
                hl hlen hbody
          | callArgsHalt hargs =>
              exact Step.callArgsHalt
                ((useAliasArgs_equivAt heq args funs st _).mp hargs)
        · intro h
          cases h with
          | callOk hargs hl hlen hbody ho =>
              exact Step.callOk
                ((useAliasArgs_equivAt heq args funs st _).mpr hargs)
                hl hlen hbody ho
          | callHalt hargs hl hlen hbody =>
              exact Step.callHalt
                ((useAliasArgs_equivAt heq args funs st _).mpr hargs)
                hl hlen hbody
          | callArgsHalt hargs =>
              exact Step.callArgsHalt
                ((useAliasArgs_equivAt heq args funs st _).mpr hargs)

  theorem useAliasArgs_equivAt {source copy : Ident} {V : VEnv D}
      (heq : VEnv.get V source = VEnv.get V copy) :
      ∀ args funs st r,
        EvalArgs D funs V st args r ↔
          EvalArgs D funs V st (StackV2.useAliasArgs source copy args) r
    | [], funs, st, r => by
        constructor <;> intro h <;> cases h <;> exact Step.argsNil
    | e :: rest, funs, st, r => by
        simp only [StackV2.useAliasArgs]
        constructor
        · intro h
          cases h with
          | argsCons hrest he =>
              exact Step.argsCons
                ((useAliasArgs_equivAt heq rest funs st _).mp hrest)
                ((useAliasExpr_equivAt heq e funs _ _).mp he)
          | argsRestHalt hrest =>
              exact Step.argsRestHalt
                ((useAliasArgs_equivAt heq rest funs st _).mp hrest)
          | argsHeadHalt hrest he =>
              exact Step.argsHeadHalt
                ((useAliasArgs_equivAt heq rest funs st _).mp hrest)
                ((useAliasExpr_equivAt heq e funs _ _).mp he)
        · intro h
          cases h with
          | argsCons hrest he =>
              exact Step.argsCons
                ((useAliasArgs_equivAt heq rest funs st _).mpr hrest)
                ((useAliasExpr_equivAt heq e funs _ _).mpr he)
          | argsRestHalt hrest =>
              exact Step.argsRestHalt
                ((useAliasArgs_equivAt heq rest funs st _).mpr hrest)
          | argsHeadHalt hrest he =>
              exact Step.argsHeadHalt
                ((useAliasArgs_equivAt heq rest funs st _).mpr hrest)
                ((useAliasExpr_equivAt heq e funs _ _).mpr he)
end
-/

theorem scopeDeadFunctionStmts_equiv (b : Block Op) :
    EquivBlock D b (StackV2.scopeDeadFunctionStmts b) := by
  rw [scopeDeadFunctionStmts_eq_mapFunBodies]
  exact mapFunBodies_equiv _ (fun ps rs body =>
    BoundEquivBlock.of_equiv (scopeDeadPrefixesStmts_equiv 64 body)) b

private def LayoutEquivStmts (calls' : ExternalCalls) (creates' : ExternalCreates)
    (bound : List Ident) (b₁ b₂ : Block Op) : Prop :=
  let D' := evmWithExternal calls' creates'
  ∀ (funs : FunEnv D') (V : VEnv D') (st : EvmState),
    YulEvmCompiler.Optimizer.BoundOK (calls := calls') (creates := creates')
      V bound → ∀ V' st' o,
    ExecStmts D' funs V st b₁ V' st' o ↔
      ExecStmts D' funs V st b₂ V' st' o

private theorem LayoutEquivStmts.refl (bound : List Ident) (b : Block Op) :
    LayoutEquivStmts calls creates bound b b :=
  fun _ _ _ _ _ _ _ => Iff.rfl

private theorem LayoutEquivStmts.cons {bound bound' : List Ident}
    {s : Stmt Op} {rest rest' : Block Op}
    (hbound : ∀ {funs V st V' st'}, YulEvmCompiler.Optimizer.BoundOK V bound →
      ExecStmt D funs V st s V' st' .normal →
        YulEvmCompiler.Optimizer.BoundOK V' bound')
    (hrest : LayoutEquivStmts calls creates bound' rest rest') :
    LayoutEquivStmts calls creates bound (s :: rest) (s :: rest') := by
  intro funs V st hb V' st' o
  constructor
  · intro h
    cases h with
    | seqCons hs hr =>
        exact Step.seqCons hs
          ((hrest funs _ _ (hbound hb hs) _ _ _).mp hr)
    | seqStop hs hn => exact Step.seqStop hs hn
  · intro h
    cases h with
    | seqCons hs hr =>
        exact Step.seqCons hs
          ((hrest funs _ _ (hbound hb hs) _ _ _).mpr hr)
    | seqStop hs hn => exact Step.seqStop hs hn

private theorem letAlias_establishes {source copy : Ident}
    {funs : FunEnv D} {V V' : VEnv D} {st st' : EvmState}
    (hne : copy ≠ source)
    (h : ExecStmt D funs V st (.letDecl [copy] (some (.var source)))
      V' st' .normal) :
    VEnv.get V' source = VEnv.get V' copy := by
  cases h with
  | letVal he hlen =>
      cases he with
      | var hget =>
          rename_i v
          simp only at hlen
          change VEnv.get ((copy, v) :: V) source =
            VEnv.get ((copy, v) :: V) copy
          rw [VEnv.get_cons, if_neg hne, VEnv.get_cons, if_pos rfl, hget]

private theorem assignAlias_establishes {source copy : Ident}
    {layout : List Ident} {funs : FunEnv D}
    {V V' : VEnv D} {st st' : EvmState}
    (hne : copy ≠ source) (hcopy : copy ∈ layout)
    (hb : YulEvmCompiler.Optimizer.BoundOK V layout)
    (h : ExecStmt D funs V st (.assign [copy] (.var source))
      V' st' .normal) :
    VEnv.get V' source = VEnv.get V' copy := by
  cases h with
  | assignVal he hlen =>
      cases he with
      | var hget =>
          simp only at hlen
          obtain ⟨old, hold⟩ := VEnv.get_isSome_of_key (hb copy hcopy)
          have his : (VEnv.get V copy).isSome = true := by simp [hold]
          rw [VEnv.setMany_singleton, VEnv.get_set_ne hne.symm,
            VEnv.get_set_self his]
          exact hget

private theorem aliasLetStmts_equiv {layout : List Ident}
    {source copy : Ident} {rest : Block Op}
    (hne : copy ≠ source) :
    LayoutEquivStmts calls creates layout
      (.letDecl [copy] (some (.var source)) :: rest)
      (.letDecl [copy] (some (.var source)) ::
        (StackV2.forwardAliasStmts source copy rest).1) := by
  intro funs V st hb V' st' o
  constructor
  · intro h
    cases h with
    | seqCons hs hr =>
        have heq := letAlias_establishes hne hs
        exact Step.seqCons hs
          ((forwardAliasStmts_equivAt hne.symm heq rest _ _ _ _ _).mp hr)
    | seqStop hs hn => exact Step.seqStop hs hn
  · intro h
    cases h with
    | seqCons hs hr =>
        have heq := letAlias_establishes hne hs
        exact Step.seqCons hs
          ((forwardAliasStmts_equivAt hne.symm heq rest _ _ _ _ _).mpr hr)
    | seqStop hs hn => exact Step.seqStop hs hn

private theorem aliasAssignStmts_equiv {layout : List Ident}
    {source copy : Ident} {rest : Block Op}
    (hne : copy ≠ source) (hcopy : copy ∈ layout) :
    LayoutEquivStmts calls creates layout
      (.assign [copy] (.var source) :: rest)
      (.assign [copy] (.var source) ::
        (StackV2.forwardAliasStmts source copy rest).1) := by
  intro funs V st hb V' st' o
  constructor
  · intro h
    cases h with
    | seqCons hs hr =>
        have heq := assignAlias_establishes hne hcopy hb hs
        exact Step.seqCons hs
          ((forwardAliasStmts_equivAt hne.symm heq rest _ _ _ _ _).mp hr)
    | seqStop hs hn => exact Step.seqStop hs hn
  · intro h
    cases h with
    | seqCons hs hr =>
        have heq := assignAlias_establishes hne hcopy hb hs
        exact Step.seqCons hs
          ((forwardAliasStmts_equivAt hne.symm heq rest _ _ _ _ _).mpr hr)
    | seqStop hs hn => exact Step.seqStop hs hn

private theorem aliasAssignStmts_equiv_rev {layout : List Ident}
    {source copy : Ident} {rest : Block Op}
    (hne : copy ≠ source) (hcopy : copy ∈ layout) :
    LayoutEquivStmts calls creates layout
      (.assign [copy] (.var source) :: rest)
      (.assign [copy] (.var source) ::
        (StackV2.forwardAliasStmts copy source rest).1) := by
  intro funs V st hb V' st' o
  constructor
  · intro h
    cases h with
    | seqCons hs hr =>
        have heq := assignAlias_establishes hne hcopy hb hs
        exact Step.seqCons hs
          ((forwardAliasStmts_equivAt hne heq.symm rest _ _ _ _ _).mp hr)
    | seqStop hs hn => exact Step.seqStop hs hn
  · intro h
    cases h with
    | seqCons hs hr =>
        have heq := assignAlias_establishes hne hcopy hb hs
        exact Step.seqCons hs
          ((forwardAliasStmts_equivAt hne heq.symm rest _ _ _ _ _).mpr hr)
    | seqStop hs hn => exact Step.seqStop hs hn

private theorem mem_of_findIdx?_eq_some {layout : List Ident} {x : Ident}
    {i : Nat} (h : layout.findIdx? (fun y => y = x) = some i) :
    x ∈ layout := by
  rw [List.findIdx?_eq_some_iff_getElem] at h
  obtain ⟨hi, heq, _⟩ := h
  have hval : layout[i] = x := by simpa using heq
  rw [← hval]
  exact List.getElem_mem hi

private def aliasLayoutAfter (layout : List Ident) : Stmt Op → List Ident
  | .letDecl xs _ => xs ++ layout
  | _ => layout

private theorem aliasBound_after {layout : List Ident} {s : Stmt Op}
    {funs : FunEnv D} {V V' : VEnv D} {st st' : EvmState}
    (hb : YulEvmCompiler.Optimizer.BoundOK V layout)
    (h : ExecStmt D funs V st s V' st' .normal) :
    YulEvmCompiler.Optimizer.BoundOK V' (aliasLayoutAfter layout s) := by
  cases s with
  | letDecl xs val =>
      simpa [aliasLayoutAfter, dpOut] using
        YulEvmCompiler.Optimizer.BoundOK.afterStmt hb h
  | _ => exact YulEvmCompiler.Optimizer.BoundOK.mono hb h

private theorem aliasFallback {layout layout' : List Ident}
    {s : Stmt Op} {rest rest' : Block Op}
    (hrest : LayoutEquivStmts calls creates layout' rest rest')
    (hlayout : layout' = aliasLayoutAfter layout s) :
    LayoutEquivStmts calls creates layout (s :: rest) (s :: rest') := by
  subst layout'
  exact LayoutEquivStmts.cons (fun hb hs => aliasBound_after hb hs) hrest

private theorem aliasOneStmts_sound : ∀ (layout : List Ident)
    (body out : Block Op), StackV2.aliasOneStmts layout body = some out →
    LayoutEquivStmts calls creates layout body out
  | _, [], _, h => by simp [StackV2.aliasOneStmts] at h
  | layout, s :: rest, out, h => by
      cases s with
      | letDecl xs val =>
          cases xs with
          | nil =>
              replace h := Option.map_eq_some_iff.mp (by
                simpa only [StackV2.aliasOneStmts, Option.map_eq_map, Option.map] using h)
              obtain ⟨rest', hr, hout⟩ := h
              subst out
              exact aliasFallback (aliasOneStmts_sound layout rest rest' hr) rfl
          | cons copy tail =>
              cases tail with
              | cons y ys =>
                  replace h := Option.map_eq_some_iff.mp (by
                    simpa only [StackV2.aliasOneStmts, Option.map_eq_map, Option.map] using h)
                  obtain ⟨rest', hr, hout⟩ := h
                  subst out
                  exact aliasFallback
                    (aliasOneStmts_sound (copy :: y :: ys ++ layout)
                      rest rest' hr) rfl
              | nil =>
                  cases val with
                  | none =>
                      replace h := Option.map_eq_some_iff.mp (by
                        simpa only [StackV2.aliasOneStmts, Option.map_eq_map, Option.map] using h)
                      obtain ⟨rest', hr, hout⟩ := h
                      subst out
                      exact aliasFallback
                        (aliasOneStmts_sound (copy :: layout) rest rest' hr) rfl
                  | some e =>
                      cases e with
                      | var source =>
                          simp only [StackV2.aliasOneStmts] at h
                          split at h
                          · next hg =>
                            generalize hf :
                              StackV2.forwardAliasStmts source copy rest = q at h
                            obtain ⟨restF, keep, changed⟩ := q
                            dsimp only at h
                            split at h
                            · cases h
                              have hne : copy ≠ source := by
                                have hg' := hg
                                simp only [Bool.and_eq_true, bne_iff_ne] at hg'
                                exact hg'.1
                              simpa [hf] using
                                (aliasLetStmts_equiv (layout := layout)
                                  (rest := rest) hne)
                            · obtain ⟨rest', hr, hout⟩ :=
                                Option.map_eq_some_iff.mp h
                              subst out
                              exact aliasFallback
                                (aliasOneStmts_sound (copy :: layout)
                                  rest rest' hr) rfl
                          · obtain ⟨rest', hr, hout⟩ :=
                              Option.map_eq_some_iff.mp h
                            subst out
                            exact aliasFallback
                              (aliasOneStmts_sound (copy :: layout)
                                rest rest' hr) rfl
                      | lit l | builtin op args | call f args =>
                          replace h := Option.map_eq_some_iff.mp (by
                            simpa only [StackV2.aliasOneStmts, Option.map_eq_map, Option.map] using h)
                          obtain ⟨rest', hr, hout⟩ := h
                          subst out
                          exact aliasFallback
                            (aliasOneStmts_sound (copy :: layout)
                              rest rest' hr) rfl
      | assign xs e =>
          cases xs with
          | nil =>
              replace h := Option.map_eq_some_iff.mp (by
                simpa only [StackV2.aliasOneStmts, Option.map_eq_map, Option.map] using h)
              obtain ⟨rest', hr, hout⟩ := h
              subst out
              exact aliasFallback (aliasOneStmts_sound layout rest rest' hr) rfl
          | cons copy tail =>
              cases tail with
              | cons y ys =>
                  replace h := Option.map_eq_some_iff.mp (by
                    simpa only [StackV2.aliasOneStmts, Option.map_eq_map, Option.map] using h)
                  obtain ⟨rest', hr, hout⟩ := h
                  subst out
                  exact aliasFallback
                    (aliasOneStmts_sound layout rest rest' hr) rfl
              | nil =>
                  cases e with
                  | var source =>
                      simp only [StackV2.aliasOneStmts] at h
                      cases hc : layout.findIdx? (fun x => x = copy) with
                      | none =>
                          simp only [hc] at h
                          cases hr : StackV2.aliasOneStmts layout rest with
                          | none => simp [hr] at h
                          | some rest' =>
                              simp [hr] at h
                              subst out
                              exact aliasFallback
                                (aliasOneStmts_sound layout rest rest' hr) rfl
                      | some copyDepth =>
                          cases hs : layout.findIdx? (fun x => x = source) with
                          | none =>
                              simp only [hc, hs] at h
                              cases hr : StackV2.aliasOneStmts layout rest with
                              | none => simp [hr] at h
                              | some rest' =>
                                  simp [hr] at h
                                  subst out
                                  exact aliasFallback
                                    (aliasOneStmts_sound layout rest rest' hr) rfl
                          | some sourceDepth =>
                              simp only [hc, hs] at h
                              split at h
                              · next hg =>
                                generalize hf : StackV2.forwardAliasStmts
                                  source copy rest = q at h
                                obtain ⟨restF, keep, changed⟩ := q
                                dsimp only at h
                                split at h
                                · cases h
                                  have hne : copy ≠ source := by
                                    have hg' := hg
                                    simp only [Bool.and_eq_true, bne_iff_ne] at hg'
                                    exact hg'.1
                                  simpa [hf] using
                                    (aliasAssignStmts_equiv (layout := layout)
                                      (rest := rest) hne
                                      (mem_of_findIdx?_eq_some hc))
                                · obtain ⟨rest', hr, hout⟩ :=
                                    Option.map_eq_some_iff.mp h
                                  subst out
                                  exact aliasFallback
                                    (aliasOneStmts_sound layout rest rest' hr) rfl
                              · split at h
                                · next hg =>
                                  generalize hf : StackV2.forwardAliasStmts
                                    copy source rest = q at h
                                  obtain ⟨restF, keep, changed⟩ := q
                                  dsimp only at h
                                  split at h
                                  · cases h
                                    have hne : copy ≠ source := by
                                      have hg' := hg
                                      simp only [Bool.and_eq_true, bne_iff_ne] at hg'
                                      exact hg'.1
                                    simpa [hf] using
                                      (aliasAssignStmts_equiv_rev
                                        (layout := layout) (rest := rest) hne
                                        (mem_of_findIdx?_eq_some hc))
                                  · obtain ⟨rest', hr, hout⟩ :=
                                      Option.map_eq_some_iff.mp h
                                    subst out
                                    exact aliasFallback
                                      (aliasOneStmts_sound layout rest rest' hr) rfl
                                · obtain ⟨rest', hr, hout⟩ :=
                                    Option.map_eq_some_iff.mp h
                                  subst out
                                  exact aliasFallback
                                    (aliasOneStmts_sound layout rest rest' hr) rfl
                  | lit l | builtin op args | call f args =>
                      replace h := Option.map_eq_some_iff.mp (by
                        simpa only [StackV2.aliasOneStmts, Option.map_eq_map, Option.map] using h)
                      obtain ⟨rest', hr, hout⟩ := h
                      subst out
                      exact aliasFallback
                        (aliasOneStmts_sound layout rest rest' hr) rfl
      | block body =>
          replace h := Option.map_eq_some_iff.mp (by
            simpa only [StackV2.aliasOneStmts, Option.map_eq_map, Option.map] using h)
          obtain ⟨rest', hr, hout⟩ := h
          subst out
          exact aliasFallback (aliasOneStmts_sound layout rest rest' hr) rfl
      | funDef f ps rs body =>
          replace h := Option.map_eq_some_iff.mp (by
            simpa only [StackV2.aliasOneStmts, Option.map_eq_map, Option.map] using h)
          obtain ⟨rest', hr, hout⟩ := h
          subst out
          exact aliasFallback (aliasOneStmts_sound layout rest rest' hr) rfl
      | cond c body =>
          replace h := Option.map_eq_some_iff.mp (by
            simpa only [StackV2.aliasOneStmts, Option.map_eq_map, Option.map] using h)
          obtain ⟨rest', hr, hout⟩ := h
          subst out
          exact aliasFallback (aliasOneStmts_sound layout rest rest' hr) rfl
      | «switch» c cases dflt =>
          replace h := Option.map_eq_some_iff.mp (by
            simpa only [StackV2.aliasOneStmts, Option.map_eq_map, Option.map] using h)
          obtain ⟨rest', hr, hout⟩ := h
          subst out
          exact aliasFallback (aliasOneStmts_sound layout rest rest' hr) rfl
      | forLoop init c post body =>
          replace h := Option.map_eq_some_iff.mp (by
            simpa only [StackV2.aliasOneStmts, Option.map_eq_map, Option.map] using h)
          obtain ⟨rest', hr, hout⟩ := h
          subst out
          exact aliasFallback (aliasOneStmts_sound layout rest rest' hr) rfl
      | exprStmt e =>
          replace h := Option.map_eq_some_iff.mp (by
            simpa only [StackV2.aliasOneStmts, Option.map_eq_map, Option.map] using h)
          obtain ⟨rest', hr, hout⟩ := h
          subst out
          exact aliasFallback (aliasOneStmts_sound layout rest rest' hr) rfl
      | «break» =>
          replace h := Option.map_eq_some_iff.mp (by
            simpa only [StackV2.aliasOneStmts, Option.map_eq_map, Option.map] using h)
          obtain ⟨rest', hr, hout⟩ := h
          subst out
          exact aliasFallback (aliasOneStmts_sound layout rest rest' hr) rfl
      | «continue» =>
          replace h := Option.map_eq_some_iff.mp (by
            simpa only [StackV2.aliasOneStmts, Option.map_eq_map, Option.map] using h)
          obtain ⟨rest', hr, hout⟩ := h
          subst out
          exact aliasFallback (aliasOneStmts_sound layout rest rest' hr) rfl
      | «leave» =>
          replace h := Option.map_eq_some_iff.mp (by
            simpa only [StackV2.aliasOneStmts, Option.map_eq_map, Option.map] using h)
          obtain ⟨rest', hr, hout⟩ := h
          subst out
          exact aliasFallback (aliasOneStmts_sound layout rest rest' hr) rfl
  termination_by layout body out _h => 2 * sizeOf body + 1

private theorem hoist_cons_congr (s : Stmt Op) {a b : Block Op}
    (h : hoist D a = hoist D b) :
    hoist D (s :: a) = hoist D (s :: b) := by
  cases s <;> simp_all [hoist]

private theorem hoist_map_cons {s : Stmt Op} {rest out : Block Op}
    {next : Option (Block Op)}
    (ih : ∀ {a}, next = some a → hoist D a = hoist D rest)
    (h : (s :: ·) <$> next = some out) :
    hoist D out = hoist D (s :: rest) := by
  change Option.map _ next = some out at h
  obtain ⟨a, ha, hout⟩ := Option.map_eq_some_iff.mp h
  subst out
  exact hoist_cons_congr _ (ih ha)

private theorem hoist_forward_result {source copy : Ident}
    {body body' : Block Op} {keep changed : Bool}
    (h : StackV2.forwardAliasStmts source copy body =
      (body', keep, changed)) :
    hoist D body' = hoist D body := by
  have hf := forwardAliasStmts_hoist
    (calls := calls) (creates := creates) source copy body
  rw [h] at hf
  exact hf

private theorem hoist_some_forward {s : Stmt Op} {source copy : Ident}
    {body body' out : Block Op} {keep changed : Bool}
    (hout : some (s :: body') = some out)
    (hforward : StackV2.forwardAliasStmts source copy body =
      (body', keep, changed)) :
    hoist D out = hoist D (s :: body) := by
  injection hout with hout'
  subst out
  exact hoist_cons_congr _ (hoist_forward_result hforward)

private theorem aliasOneStmts_hoist {layout : List Ident}
    {body out : Block Op} (h : StackV2.aliasOneStmts layout body = some out) :
    hoist D out = hoist D body := by
  revert out
  fun_induction StackV2.aliasOneStmts layout body
  all_goals intro out h
  all_goals
    first
    | (apply hoist_map_cons (calls := calls) (creates := creates) <;> assumption)
    | (apply hoist_some_forward (calls := calls) (creates := creates) <;>
        assumption)
    | contradiction

private theorem aliasOneStmts_bound {layout : List Ident}
    {body out : Block Op} (h : StackV2.aliasOneStmts layout body = some out) :
    BoundEquivBlock D layout body out := by
  have hs := aliasOneStmts_sound (calls := calls) (creates := creates)
    layout body out h
  have hh := aliasOneStmts_hoist (calls := calls) (creates := creates) h
  intro funs V st hb
  have hbmem : YulEvmCompiler.Optimizer.BoundOK V layout := by
    intro x hx
    change V.map Prod.fst = layout at hb
    rw [hb]
    exact hx
  constructor
  · intro V' st' o _
    constructor
    · intro hrun
      cases hrun with
      | block hbody =>
          exact Step.block (by
            rw [hh]
            exact (hs (hoist D body :: funs) V st hbmem _ _ _).mp hbody)
    · intro hrun
      cases hrun with
      | block hbody =>
          rw [hh] at hbody
          exact Step.block ((hs (hoist D body :: funs) V st hbmem _ _ _).mpr hbody)
  · intro st'
    constructor
    · rintro ⟨_, hrun⟩
      cases hrun with
      | block hbody =>
          have hrunOut := Step.block (by
            rw [hh]
            exact (hs (hoist D body :: funs) V st hbmem _ _ _).mp hbody)
          exact ⟨_, hrunOut⟩
    · rintro ⟨V', hrun⟩
      cases hrun with
      | block hbody =>
          rw [hh] at hbody
          exact ⟨_, Step.block
            ((hs (hoist D body :: funs) V st hbmem _ _ _).mpr hbody)⟩

theorem iterateAliasesFrom_bound (n : Nat) (layout : List Ident)
    (body : Block Op) :
    BoundEquivBlock D layout body
      (StackV2.iterateAliasesFrom n layout body) := by
  induction n generalizing body with
  | zero => exact BoundEquivBlock.refl _ _
  | succ n ih =>
      rw [StackV2.iterateAliasesFrom]
      cases h : StackV2.aliasOneStmts layout body with
      | none => exact BoundEquivBlock.refl _ _
      | some out => exact (aliasOneStmts_bound h).trans (ih out)

private theorem aliasFunctionStmts_eq_mapFunBodies : ∀ b : Block Op,
    StackV2.aliasFunctionStmts b = mapFunBodies
      (fun ps rs body =>
        StackV2.iterateAliasesFrom 4096 (ps ++ rs) body) b := by
  intro b
  induction b with
  | nil => rfl
  | cons s rest ih =>
      change List.map StackV2.aliasFunctionStmt rest =
        mapFunBodies (fun ps rs body =>
          StackV2.iterateAliasesFrom 4096 (ps ++ rs) body) rest at ih
      cases s <;> simp [StackV2.aliasFunctionStmts,
        StackV2.aliasFunctionStmt, mapFunBodies, ih]

private theorem localAt_of_layout {V : VEnv D} {layout : List Ident}
    {x : Ident} (hkeys : V.map Prod.fst = layout) (hx : x ∈ layout) :
    ∃ d, LocalAt d x V := by
  have hm : x ∈ (V.take V.length).map Prod.fst := by
    simpa [hkeys] using hx
  obtain ⟨d, hd, _⟩ := localAt_of_mem_take hm
  exact ⟨d, hd⟩

private theorem SlotRel.copyBack_restore {d dx : Nat} {x y : Ident}
    {V₁ V₂ base : VEnv D} {value : U256}
    (h : SlotRel d dx x y V₁ V₂) (hxy : x ≠ y)
    (hkeys : V₁.map Prod.fst = y :: base.map Prod.fst)
    (hget : VEnv.get V₁ y = some value) :
    restore base (VEnv.set V₁ x value) = V₂ := by
  obtain ⟨above, tail, old, hV₁, hV₂, hxa, hya, hd, hlocal⟩ := h
  subst V₁
  have habove : above = [] := by
    cases above with
    | nil => rfl
    | cons p rest =>
        have hhead := congrArg List.head? hkeys
        simp only [List.map_append, List.map_cons, List.head?_cons] at hhead
        have hp : p.1 = y := by simpa using hhead
        exact False.elim (hya (by simp [hp]))
  rw [habove] at hkeys hget hV₂ hxa hya ⊢
  simp only [List.nil_append] at hkeys hget hV₂ hxa hya ⊢
  have hvalue : old = value := by
    simpa [VEnv.get] using hget
  subst old
  rw [VEnv.set]
  simp only [if_neg hxy.symm]
  rw [restore]
  have hlen : ((y, value) :: VEnv.set tail x value).length - base.length = 1 := by
    have htail := congrArg List.length hkeys
    simp only [List.length_map, List.length_cons] at htail
    have htailBase : tail.length = base.length := by omega
    rw [List.length_cons, VEnv.set_length, htailBase]
    simp
  rw [hlen]
  simp [hV₂]

mutual
  private theorem rename_straight_stmt (r : Rename) : ∀ s : Stmt Op,
      StackV2.shadowStraightStmt s = true →
        StackV2.shadowStraightStmt (renameStmt r s) = true
    | .block body, h | .cond _ body, h => by
        have hb : StackV2.shadowStraightStmts body = true := by
          simpa only [StackV2.shadowStraightStmt] using h
        simpa only [renameStmt, StackV2.shadowStraightStmt] using
          rename_straight r body hb
    | .switch _ cases dflt, h => by
        have hs : StackV2.shadowStraightCases cases = true ∧
            StackV2.shadowStraightDflt dflt = true := by
          simpa only [StackV2.shadowStraightStmt, Bool.and_eq_true] using h
        simp only [renameStmt.eq_def, StackV2.shadowStraightStmt,
          Bool.and_eq_true]
        constructor
        · exact rename_straight_cases r cases hs.1
        · cases dflt with
          | none => simp [StackV2.shadowStraightDflt]
          | some body =>
              simpa only [StackV2.shadowStraightDflt] using
                rename_straight r body (by
                  simpa only [StackV2.shadowStraightDflt] using hs.2)
    | .letDecl _ _, _ | .assign _ _, _ | .exprStmt _, _ => by
        simp [renameStmt, StackV2.shadowStraightStmt]
    | .funDef _ _ _ _, h | .forLoop _ _ _ _, h |
      .break, h | .continue, h | .leave, h => by
        simp [StackV2.shadowStraightStmt] at h

  private theorem rename_straight (r : Rename) : ∀ body : Block Op,
      StackV2.shadowStraightStmts body = true →
        StackV2.shadowStraightStmts (renameStmts r body) = true
    | [], _ => by simp [renameStmts, StackV2.shadowStraightStmts]
    | s :: rest, h => by
        have hs : StackV2.shadowStraightStmt s = true ∧
            StackV2.shadowStraightStmts rest = true := by
          simpa only [StackV2.shadowStraightStmts, Bool.and_eq_true] using h
        simpa only [renameStmts, StackV2.shadowStraightStmts,
          Bool.and_eq_true] using
          And.intro (rename_straight_stmt r s hs.1)
            (rename_straight r rest hs.2)

  private theorem rename_straight_cases (r : Rename) :
      ∀ cases : List (Literal × Block Op),
      StackV2.shadowStraightCases cases = true →
        StackV2.shadowStraightCases (renameCases r cases) = true
    | [], _ => by simp [renameCases, StackV2.shadowStraightCases]
    | (_, body) :: rest, h => by
        have hs : StackV2.shadowStraightStmts body = true ∧
            StackV2.shadowStraightCases rest = true := by
          simpa only [StackV2.shadowStraightCases, Bool.and_eq_true] using h
        simpa only [renameCases, StackV2.shadowStraightCases,
          Bool.and_eq_true] using
          And.intro (rename_straight r body hs.1)
            (rename_straight_cases r rest hs.2)

  private theorem rename_straight_dflt (r : Rename) :
      ∀ dflt : Option (Block Op),
      StackV2.shadowStraightDflt dflt = true →
        StackV2.shadowStraightDflt
          (match dflt with
          | none => none
          | some body => some (renameStmts r body)) = true
    | none, _ => by simp [StackV2.shadowStraightDflt]
    | some body, h => by
        have hb : StackV2.shadowStraightStmts body = true := by
          simpa only [StackV2.shadowStraightDflt] using h
        simpa only [StackV2.shadowStraightDflt] using
          rename_straight r body hb
end

private theorem straight_cases_mem {cases : List (Literal × Block Op)}
    (h : StackV2.shadowStraightCases cases = true) {p} (hp : p ∈ cases) :
    StackV2.shadowStraightStmts p.2 = true := by
  induction cases with
  | nil => simp at hp
  | cons q rest ih =>
      have hs : StackV2.shadowStraightStmts q.2 = true ∧
          StackV2.shadowStraightCases rest = true := by
        rw [StackV2.shadowStraightCases] at h
        simpa only [Bool.and_eq_true] using h
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hs.1
      · exact ih hs.2 hp

private theorem straight_selectSwitch (cv : U256)
    (cases : List (Literal × Block Op)) (dflt : Option (Block Op))
    (hc : StackV2.shadowStraightCases cases = true)
    (hd : StackV2.shadowStraightDflt dflt = true) :
    StackV2.shadowStraightStmts (selectSwitch D cv cases dflt) = true := by
  unfold selectSwitch
  cases hfind : cases.find? (fun p => decide (cv = litValue p.1)) with
  | some p =>
      simp only [hfind]
      exact straight_cases_mem hc (List.mem_of_find?_eq_some hfind)
  | none =>
      simp only [hfind]
      cases dflt <;> simp_all [StackV2.shadowStraightDflt,
        StackV2.shadowStraightStmts]

private theorem selectSwitch_size_lt_stmt (c : Expr Op) (cv : U256)
    (cases : List (Literal × Block Op)) (dflt : Option (Block Op)) :
    2 * sizeOf (selectSwitch D cv cases dflt) + 1 <
      2 * sizeOf (Stmt.switch c cases dflt) := by
  unfold selectSwitch
  cases hfind : cases.find? (fun p => decide (cv = litValue p.1)) with
  | some p =>
      simp only [hfind]
      have hp := List.mem_of_find?_eq_some hfind
      have hsize := List.sizeOf_lt_of_mem hp
      have hpair : sizeOf p.2 < sizeOf p := by
        rcases p with ⟨lit, body⟩
        simp_wf
      have hstmt : sizeOf cases < sizeOf (Stmt.switch c cases dflt) := by
        simp_wf
        omega
      omega
  | none =>
      simp only [hfind]
      cases dflt <;> simp_all <;> omega

set_option maxHeartbeats 800000 in
mutual
  private theorem straight_stmt_outcome {s : Stmt Op} {funs : FunEnv D}
      {V V' : VEnv D} {st st' : EvmState} {o : Outcome}
      (hs : StackV2.shadowStraightStmt s = true)
      (h : ExecStmt D funs V st s V' st' o) :
      o = .normal ∨ o = .halt := by
    cases h with
    | block hbody =>
        exact straight_outcome _ _ _ _ _ _ _ (by
          simpa only [StackV2.shadowStraightStmt] using hs) hbody
    | funDef => simp [StackV2.shadowStraightStmt] at hs
    | letZero | ifFalse => exact .inl rfl
    | «break» | «continue» | «leave» =>
        simp [StackV2.shadowStraightStmt] at hs
    | letVal | assignVal | exprStmt => exact .inl rfl
    | letHalt | assignHalt | exprStmtHalt | ifHalt | switchHalt |
      forInitHalt => exact .inr rfl
    | ifTrue _ _ hbody =>
        cases hbody with
        | block hbody =>
          exact straight_outcome _ _ _ _ _ _ _ (by
            simpa only [StackV2.shadowStraightStmt] using hs) hbody
    | @switchExec funs0 V0 st0 c cases dflt cv st1 Vout st2 o0
        hcond hbody =>
        cases hbody with
        | block hbody =>
          simp only [StackV2.shadowStraightStmt, Bool.and_eq_true] at hs
          have hsize := selectSwitch_size_lt_stmt (calls := calls)
            (creates := creates) c cv cases dflt
          exact straight_outcome (selectSwitch D cv cases dflt) _ _ _ _ _ _
            (straight_selectSwitch _ _ _ hs.1 hs.2) hbody
    | forLoop => simp [StackV2.shadowStraightStmt] at hs
  termination_by 2 * sizeOf s

  private theorem straight_outcome : ∀ (body : Block Op) (funs : FunEnv D)
      (V V' : VEnv D) (st st' : EvmState) (o : Outcome),
      StackV2.shadowStraightStmts body = true →
      ExecStmts D funs V st body V' st' o →
      o = .normal ∨ o = .halt
    | [], _, _, _, _, _, _, _, h => by
        cases h
        exact .inl rfl
    | s :: rest, _, _, _, _, _, _, hs, h => by
        simp only [StackV2.shadowStraightStmts, Bool.and_eq_true] at hs
        cases h with
        | seqCons _ hrest =>
            exact straight_outcome rest _ _ _ _ _ _ hs.2 hrest
        | seqStop hhead hn =>
            have hout := straight_stmt_outcome (s := s) hs.1 hhead
            rcases hout with rfl | rfl
            · exact False.elim (hn rfl)
            · exact .inr rfl
  termination_by body _ _ _ _ _ _ _ _ => 2 * sizeOf body + 1
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

private theorem shadowStraightCore_bound {layout : List Ident}
    {x shadow : Ident} {body : Block Op}
    (hx : x ∈ layout) (hxy : x ≠ shadow)
    (hshadow : stmtsMentions shadow body = false)
    (hdecl : stmtsDeclare x body = false)
    (hfunX : stmtsFunMention x body = false)
    (hsourceHoist : hoist D body = [])
    (hstraight : StackV2.shadowStraightStmts body = true) :
    BoundEquivBlock D layout body
      [.letDecl [shadow] (some (.var x)),
        .block (renameStmts [(x, shadow)] body),
        .assign [x] (.var shadow)] := by
  intro funs V st hkeys
  change V.map Prod.fst = layout at hkeys
  have hxV : x ∈ V.map Prod.fst := by simpa [hkeys] using hx
  obtain ⟨value, hxget⟩ := VEnv.get_isSome_of_key hxV
  obtain ⟨dx, hxlocal⟩ := localAt_of_layout hkeys hx
  have hslot₀ : SlotRel V.length dx x shadow
      ((shadow, value) :: V) V := by
    have h := SlotRel.initial (y := shadow) (value := value) hxlocal
    rwa [VEnv.set_self hxget] at h
  have htargetMentions :
      stmtsMentions x (renameStmts [(x, shadow)] body) = false :=
    renameStmts_no_target hxy.symm hshadow hdecl hfunX
  have htargetDeclares :
      stmtsDeclare shadow (renameStmts [(x, shadow)] body) = false := by
    rw [stmtsDeclare_rename]
    exact stmtsDeclare_false_of_mentions shadow body hshadow
  have htargetHoist : hoist D (renameStmts [(x, shadow)] body) = [] := by
    rw [hoist_renameStmts, hsourceHoist]
  have htargetOuterHoist : hoist D
      [.letDecl [shadow] (some (.var x)),
        .block (renameStmts [(x, shadow)] body),
        .assign [x] (.var shadow)] = [] := by
    simp [hoist, htargetHoist]
  constructor
  · intro V' st' o ho
    constructor
    · intro hrun
      cases hrun with
      | @block _ _ _ _ Vbody _ _ hbody =>
        have hout := straight_outcome _ _ _ _ _ _ _ hstraight hbody
        rcases hout with rfl | rfl
        · obtain ⟨r, hrenamed, hr⟩ := slot_rev_fwd hbody hslot₀ hxy
            (by simpa [codeMentions] using hshadow)
            (by simpa [codeDeclares] using hdecl)
          obtain ⟨Vb, rfl, hslotB⟩ := hr.sres_right
          have hrenamed' : ExecStmts D ([] :: funs) ((shadow, value) :: V) st
              (renameStmts [(x, shadow)] body) Vb st' .normal := by
            simpa [renameCode, hsourceHoist] using hrenamed
          have hrenamed'' := Step.emptyScope_congr hrenamed' (.add _)
          have hinner : ExecStmt D ([] :: funs) ((shadow, value) :: V) st
              (.block (renameStmts [(x, shadow)] body))
              (restore ((shadow, value) :: V) Vb) st' .normal := by
            exact Step.block (by simpa [htargetHoist] using hrenamed'')
          have hslotR := hslot₀.restore_nested hslotB
            (venvLen_mono hrenamed' rfl)
          have hkeysInner := (block_stmt_shape hinner).1
          have hxFinal : x ∈ (restore V Vbody).map Prod.fst := by
            have hshape := (block_stmt_shape (Step.block hbody)).1
            rw [hshape]
            exact hxV
          obtain ⟨newValue, hxFinalGet⟩ := VEnv.get_isSome_of_key hxFinal
          have hshadowGet : VEnv.get (restore ((shadow, value) :: V) Vb)
              shadow = some newValue := by
            rw [hslotR.get_y]
            exact hxFinalGet
          have hcopy : ExecStmt D ([] :: funs)
              (restore ((shadow, value) :: V) Vb) st'
              (.assign [x] (.var shadow))
              (VEnv.set (restore ((shadow, value) :: V) Vb) x newValue)
              st' .normal := by
            exact Step.assignVal (Step.var hshadowGet) rfl
          have hrestore := SlotRel.copyBack_restore hslotR hxy
            hkeysInner hshadowGet
          have hlet : ExecStmt D ([] :: funs) V st
              (.letDecl [shadow] (some (.var x)))
              ((shadow, value) :: V) st .normal :=
            Step.letVal (Step.var hxget) rfl
          have hseq := Step.seqCons hlet
            (Step.seqCons hinner (Step.seqCons hcopy Step.seqNil))
          have htarget : ExecStmt D funs V st
              (.block [.letDecl [shadow] (some (.var x)),
                .block (renameStmts [(x, shadow)] body),
                .assign [x] (.var shadow)])
              (restore V (VEnv.set (restore ((shadow, value) :: V) Vb)
                x newValue)) st' .normal := by
            exact Step.block (by simpa [htargetOuterHoist] using hseq)
          rw [hrestore] at htarget
          exact htarget
        · exact absurd rfl ho
    · intro hrun
      cases hrun with
      | block hseq =>
        cases hseq with
        | seqCons hlet hrest =>
          cases hlet with
          | letVal hread hlen =>
            cases hread with
            | var hread =>
              simp only at hlen
              rw [hxget] at hread
              cases hread
              cases hrest with
              | seqCons hinner htail =>
                cases htail with
                | seqCons hcopy hnil =>
                  cases hcopy with
                  | assignVal hreadCopy hlenCopy =>
                    cases hreadCopy with
                    | var hshadowGet =>
                      cases hnil
                      cases hinner with
                      | @block _ _ _ _ Vrenamed _ _ hrenamedBody =>
                        have hrenamedBody' : ExecStmts D ([] :: [] :: funs)
                            ((shadow, value) :: V) st
                            (renameStmts [(x, shadow)] body) Vrenamed st' .normal := by
                          simpa [htargetOuterHoist, htargetHoist] using hrenamedBody
                        have hrenamed' := Step.emptyScope_congr
                          hrenamedBody' (.drop _)
                        obtain ⟨r, hsource, hr⟩ := slot_fwd hrenamed' hslot₀
                          (by simpa [codeMentions] using htargetMentions)
                          (by simpa [codeDeclares] using htargetDeclares)
                        obtain ⟨Vb, rfl, hslotB⟩ := hr.sres
                        simp only [renameCode] at hsource
                        rw [renameStmts_inverse hxy.symm hshadow] at hsource
                        have hslotR := hslot₀.restore_nested hslotB
                          (venvLen_mono hrenamed' rfl)
                        simp only at hlenCopy
                        have hinner : ExecStmt D ([] :: funs)
                            ((shadow, value) :: V) st
                            (.block (renameStmts [(x, shadow)] body))
                            (restore ((shadow, value) :: V) Vrenamed)
                            st' .normal := by
                          exact Step.block (by simpa [htargetOuterHoist,
                            htargetHoist] using hrenamedBody)
                        have hkeysInner := (block_stmt_shape hinner).1
                        have hrestore := SlotRel.copyBack_restore hslotR hxy
                          hkeysInner hshadowGet
                        have hsourceBlock : ExecStmt D funs V st (.block body)
                            (restore V Vb) st' .normal := by
                          exact Step.block (by simpa [hsourceHoist] using hsource)
                        simp only [List.zip_cons_cons, List.zip_nil_left,
                          List.nil_append, List.singleton_append]
                        rw [VEnv.setMany_singleton, hrestore]
                        exact hsourceBlock
                | seqStop hcopy hn => cases hcopy <;> simp_all
              | seqStop hinner hn =>
                cases hinner with
                | block hrenamedBody =>
                  have hout := straight_outcome _ _ _ _ _ _ _
                    (rename_straight [(x, shadow)] body hstraight)
                    hrenamedBody
                  rcases hout with rfl | rfl <;> simp_all
        | seqStop hlet hn =>
          cases hlet with
          | letVal _ _ => exact False.elim (hn rfl)
          | letHalt hexpr => cases hexpr
  · intro st'
    constructor
    · rintro ⟨V', hrun⟩
      cases hrun with
      | block hbody =>
        obtain ⟨r, hrenamed, hr⟩ := slot_rev_fwd hbody hslot₀ hxy
          (by simpa [codeMentions] using hshadow)
          (by simpa [codeDeclares] using hdecl)
        obtain ⟨Vb, rfl, hslotB⟩ := hr.sres_right
        have hrenamed' : ExecStmts D ([] :: funs) ((shadow, value) :: V) st
            (renameStmts [(x, shadow)] body) Vb st' .halt := by
          simpa [renameCode, hsourceHoist] using hrenamed
        have hrenamed'' := Step.emptyScope_congr hrenamed' (.add _)
        have hinner : ExecStmt D ([] :: funs) ((shadow, value) :: V) st
            (.block (renameStmts [(x, shadow)] body))
            (restore ((shadow, value) :: V) Vb) st' .halt :=
          Step.block (by simpa [htargetHoist] using hrenamed'')
        have hlet : ExecStmt D ([] :: funs) V st
            (.letDecl [shadow] (some (.var x)))
            ((shadow, value) :: V) st .normal :=
          Step.letVal (Step.var hxget) rfl
        refine ⟨_, Step.block (Step.seqCons hlet
          (Step.seqStop hinner (by simp)))⟩
    · rintro ⟨V', hrun⟩
      cases hrun with
      | block hseq =>
        cases hseq with
        | seqCons hlet hrest =>
          cases hlet with
          | letVal hread hlen =>
            cases hread with
            | var hread =>
              simp only at hlen
              rw [hxget] at hread
              cases hread
              cases hrest with
              | seqStop hinner hn =>
                cases hinner with
                | @block _ _ _ _ Vrenamed _ _ hrenamedBody =>
                  have hrenamedBody' : ExecStmts D ([] :: [] :: funs)
                      ((shadow, value) :: V) st
                      (renameStmts [(x, shadow)] body) Vrenamed st' .halt := by
                    simpa [htargetOuterHoist, htargetHoist] using hrenamedBody
                  have hrenamed' := Step.emptyScope_congr
                    hrenamedBody' (.drop _)
                  obtain ⟨r, hsource, hr⟩ := slot_fwd hrenamed' hslot₀
                    (by simpa [codeMentions] using htargetMentions)
                    (by simpa [codeDeclares] using htargetDeclares)
                  obtain ⟨Vb, rfl, hslotB⟩ := hr.sres
                  simp only [renameCode] at hsource
                  rw [renameStmts_inverse hxy.symm hshadow] at hsource
                  exact ⟨_, Step.block (by simpa [hsourceHoist] using hsource)⟩
              | seqCons hinner htail =>
                cases hinner with
                | block hrenamedBody =>
                  cases htail with
                  | seqStop hcopy hn =>
                      cases hcopy with
                      | assignHalt hv => cases hv
                  | seqCons hcopy hnil => cases hnil
        | seqStop hlet hn =>
          cases hlet with
          | letHalt hexpr => cases hexpr

private theorem shadowStableCandidate_bound (P : String) (Phi : FMap)
    (layout : List Ident) (body : Block Op) : ∀ (xs : List Ident)
    {out : Block Op},
    StackV2.shadowStableCandidate P Phi layout body xs = some out →
      BoundEquivBlock D layout body out
  | [], _, h => by simp [StackV2.shadowStableCandidate] at h
  | x :: xs, out, h => by
      rw [StackV2.shadowStableCandidate] at h
      cases hidx : layout.findIdx? (fun y => y = x) with
      | none =>
          simp only [hidx] at h
          exact shadowStableCandidate_bound P Phi layout body xs h
      | some idx =>
          simp only [hidx] at h
          split at h
          · next hguard =>
            split at h
            · cases h
              simp only [Bool.and_eq_true, Bool.not_eq_true] at hguard
              rcases hguard with ⟨hguard, hcontrols⟩
              rcases hguard with ⟨hguard, hstraight⟩
              rcases hguard with ⟨hguard, hfunMentionNeg⟩
              rcases hguard with ⟨hguard, hescape⟩
              rcases hguard with ⟨hguard, hleave⟩
              rcases hguard with ⟨hguard, hfun⟩
              rcases hguard with ⟨hguard, hdeclNeg⟩
              rcases hguard with ⟨hguard, hshadow⟩
              rcases hguard with ⟨hguard, hfresh⟩
              rcases hguard with ⟨hdepth, hbne⟩
              have hxy : x ≠ s!"{P}r" := bne_iff_ne.mp hbne
              have hshadowFalse : stmtsMentions s!"{P}r" body = false := by
                cases hm : stmtsMentions s!"{P}r" body <;> simp_all
              have hdecl : stmtsDeclare x body = false := by
                cases hd : stmtsDeclare x body <;> simp_all
              have hfunMention : stmtsFunMention x body = false := by
                cases hm : stmtsFunMention x body <;> simp_all
              have hsourceHoist : hoist D body = [] :=
                hoist_nil_of_no_direct_fun body (by
                  cases hf : hasDirectFun body <;> simp_all)
              let inner : Block Op :=
                [.letDecl [s!"{P}r"] (some (.var x)),
                  .block (renameStmts [(x, s!"{P}r")] body),
                  .assign [x] (.var s!"{P}r")]
              have hcore : BoundEquivBlock D layout body inner := by
                simpa [inner] using shadowStraightCore_bound
                  (mem_of_findIdx?_eq_some hidx) hxy
                  hshadowFalse hdecl hfunMention hsourceHoist hstraight
              have hwrap : EquivBlock D inner [.block inner] := by
                simpa [inner] using scopePrefix_equivBlock
                  (pre := inner) (rest := [])
                  (by simp [inner, hasDirectFun])
                  (by intro x hx; rfl)
              exact hcore.trans (BoundEquivBlock.of_equiv hwrap)
            · exact shadowStableCandidate_bound P Phi layout body xs h
          · exact shadowStableCandidate_bound P Phi layout body xs h
  termination_by xs out _h => xs.length

private theorem shadowStableHere_bound {P : String} {Phi : FMap}
    {layout : List Ident} {body out : Block Op}
    (h : StackV2.shadowStableHere P Phi layout body = some out) :
    BoundEquivBlock D layout body out := by
  unfold StackV2.shadowStableHere at h
  cases hfirst : StackV2.shadowStableCandidate P Phi layout body
      ((StackV2.deepVarsStmts Phi layout layout body).filter fun x =>
        !StackV2.writesStmts x body) with
  | some first =>
      simp only [hfirst] at h
      cases h
      exact shadowStableCandidate_bound P Phi layout body _ hfirst
  | none =>
      simp only [hfirst] at h
      exact shadowStableCandidate_bound P Phi layout body _ h

private theorem shadowWrittenHere_bound {P : String} {Phi : FMap}
    {layout : List Ident} {body out : Block Op}
    (h : StackV2.shadowWrittenHere P Phi layout body = some out) :
    BoundEquivBlock D layout body out := by
  exact shadowStableCandidate_bound P Phi layout body _
    (by simpa [StackV2.shadowWrittenHere] using h)

private theorem let_single_bound {funs : FunEnv D} {V V' : VEnv D}
    {st st'} {g : Ident} {init : Option (Expr Op)}
    {layout : List Ident} (hb : BoundFun.BoundOK V layout)
    (hlet : ExecStmt D funs V st (.letDecl [g] init) V' st' .normal) :
    BoundFun.BoundOK V' (g :: layout) := by
  cases init with
  | none =>
      cases hlet
      unfold BoundFun.BoundOK
      change [g] ++ V.map Prod.fst = g :: layout
      rw [hb]
      rfl
  | some e =>
      cases hlet with
      | letVal _ hlen =>
          unfold BoundFun.BoundOK
          rw [List.map_append, List.map_fst_zip (by omega), hb]
          simp

private theorem boundBlockTail_nonhalt {bound : List Ident}
    {inner inner' rest : Block Op}
    (hinner : BoundEquivBlock D bound inner inner')
    {funs : FunEnv D} {V : VEnv D} {st}
    (hb : BoundFun.BoundOK V bound) {V' : VEnv D} {st'}
    {o : Outcome} (ho : o ≠ .halt) :
    ExecStmts D funs V st (.block inner :: rest) V' st' o ↔
      ExecStmts D funs V st (.block inner' :: rest) V' st' o := by
  constructor <;> intro h
  · cases h with
    | seqCons hblock hrest =>
        exact Step.seqCons (((hinner funs V st hb).1 _ _ .normal (by simp)).mp hblock)
          hrest
    | seqStop hblock hn =>
        exact Step.seqStop (((hinner funs V st hb).1 _ _ _ ho).mp hblock) hn
  · cases h with
    | seqCons hblock hrest =>
        exact Step.seqCons (((hinner funs V st hb).1 _ _ .normal (by simp)).mpr hblock)
          hrest
    | seqStop hblock hn =>
        exact Step.seqStop (((hinner funs V st hb).1 _ _ _ ho).mpr hblock) hn

private theorem boundBlockTail_halt {bound : List Ident}
    {inner inner' rest : Block Op}
    (hinner : BoundEquivBlock D bound inner inner')
    {funs : FunEnv D} {V : VEnv D} {st}
    (hb : BoundFun.BoundOK V bound) {st'} :
    (∃ V', ExecStmts D funs V st (.block inner :: rest) V' st' .halt) ↔
      ∃ V', ExecStmts D funs V st (.block inner' :: rest) V' st' .halt := by
  constructor
  · rintro ⟨V', h⟩
    cases h with
    | seqCons hblock hrest =>
        refine ⟨V', Step.seqCons ?_ hrest⟩
        exact ((hinner funs V st hb).1 _ _ .normal (by simp)).mp hblock
    | seqStop hblock _ =>
        obtain ⟨V'', hblock'⟩ := ((hinner funs V st hb).2 st').mp ⟨_, hblock⟩
        exact ⟨V'', Step.seqStop hblock' (by simp)⟩
  · rintro ⟨V', h⟩
    cases h with
    | seqCons hblock hrest =>
        refine ⟨V', Step.seqCons ?_ hrest⟩
        exact ((hinner funs V st hb).1 _ _ .normal (by simp)).mpr hblock
    | seqStop hblock _ =>
        obtain ⟨V'', hblock'⟩ := ((hinner funs V st hb).2 st').mpr ⟨_, hblock⟩
        exact ⟨V'', Step.seqStop hblock' (by simp)⟩

private theorem underLetBlockTail_bound {g : Ident} {init : Option (Expr Op)}
    {layout : List Ident} {inner inner' rest : Block Op}
    (hinner : BoundEquivBlock D (g :: layout) inner inner') :
    BoundEquivBlock D layout
      (.letDecl [g] init :: .block inner :: rest)
      (.letDecl [g] init :: .block inner' :: rest) := by
  intro funs V st hb
  have hhoist : hoist D (.letDecl [g] init :: .block inner :: rest) =
      hoist D (.letDecl [g] init :: .block inner' :: rest) := by
    simp [hoist]
  constructor
  · intro V' st' o ho
    constructor
    · intro h
      cases h with
      | block hbody =>
        apply Step.block
        rw [← hhoist]
        cases hbody with
        | seqCons hlet htail =>
            exact Step.seqCons hlet ((boundBlockTail_nonhalt hinner
              (let_single_bound hb hlet) ho).mp htail)
        | seqStop hlet hn => exact Step.seqStop hlet hn
    · intro h
      cases h with
      | block hbody =>
        apply Step.block
        rw [hhoist]
        cases hbody with
        | seqCons hlet htail =>
            exact Step.seqCons hlet ((boundBlockTail_nonhalt hinner
              (let_single_bound hb hlet) ho).mpr htail)
        | seqStop hlet hn => exact Step.seqStop hlet hn
  · intro st'
    constructor
    · rintro ⟨V', h⟩
      cases h with
      | block hbody =>
        rw [hhoist] at hbody
        cases hbody with
        | seqCons hlet htail =>
            obtain ⟨V'', htail'⟩ := (boundBlockTail_halt hinner
              (let_single_bound hb hlet)).mp ⟨_, htail⟩
            exact ⟨_, Step.block (Step.seqCons hlet htail')⟩
        | seqStop hlet hn => exact ⟨_, Step.block (Step.seqStop hlet hn)⟩
    · rintro ⟨V', h⟩
      cases h with
      | block hbody =>
        rw [← hhoist] at hbody
        cases hbody with
        | seqCons hlet htail =>
            obtain ⟨V'', htail'⟩ := (boundBlockTail_halt hinner
              (let_single_bound hb hlet)).mpr ⟨_, htail⟩
            exact ⟨_, Step.block (Step.seqCons hlet htail')⟩
        | seqStop hlet hn => exact ⟨_, Step.block (Step.seqStop hlet hn)⟩

private theorem singletonBlock_bound {layout : List Ident}
    {inner inner' : Block Op}
    (hinner : BoundEquivBlock D layout inner inner') :
    BoundEquivBlock D layout [.block inner] [.block inner'] := by
  intro funs V st hb
  constructor
  · intro V' st' o ho
    constructor
    · intro h
      cases h with
      | block hbody =>
          exact Step.block ((boundBlockTail_nonhalt (rest := []) hinner hb ho).mp hbody)
    · intro h
      cases h with
      | block hbody =>
          exact Step.block ((boundBlockTail_nonhalt (rest := []) hinner hb ho).mpr hbody)
  · intro st'
    constructor
    · rintro ⟨V', h⟩
      cases h with
      | block hbody =>
          obtain ⟨V'', hbody'⟩ := (boundBlockTail_halt (rest := []) hinner hb).mp
            ⟨_, hbody⟩
          exact ⟨_, Step.block hbody'⟩
    · rintro ⟨V', h⟩
      cases h with
      | block hbody =>
          obtain ⟨V'', hbody'⟩ := (boundBlockTail_halt (rest := []) hinner hb).mpr
            ⟨_, hbody⟩
          exact ⟨_, Step.block hbody'⟩

private theorem shadowInsideExisting_bound (P : String) (Phi : FMap)
    (layout : List Ident) {body out : Block Op}
    (h : StackV2.shadowInsideExisting P Phi layout body = some out) :
    BoundEquivBlock D layout body out := by
  revert out
  fun_induction StackV2.shadowInsideExisting P Phi layout body
  case case1 inner ih =>
    intro out h
    obtain ⟨inner', hinner, rfl⟩ := Option.map_eq_some_iff.mp h
    exact singletonBlock_bound (ih hinner)
  case case2 g init inner rest hgen inner' hinner ih =>
    intro out h
    cases h
    exact underLetBlockTail_bound (ih hinner)
  case case3 g init inner rest hgen hnone ih =>
    intro out h
    contradiction
  case case4 g init inner rest hgen =>
    intro out h
    exact shadowStableHere_bound h
  case case5 body hsingle hchain =>
    intro out h
    exact shadowStableHere_bound h

private theorem shadowInsideExistingWritten_bound (P : String) (Phi : FMap)
    (layout : List Ident) {body out : Block Op}
    (h : StackV2.shadowInsideExistingWritten P Phi layout body = some out) :
    BoundEquivBlock D layout body out := by
  revert out
  fun_induction StackV2.shadowInsideExistingWritten P Phi layout body
  case case1 inner ih =>
    intro out h
    obtain ⟨inner', hinner, rfl⟩ := Option.map_eq_some_iff.mp h
    exact singletonBlock_bound (ih hinner)
  case case2 g init inner rest hgen inner' hinner ih =>
    intro out h
    cases h
    exact underLetBlockTail_bound (ih hinner)
  case case3 g init inner rest hgen hnone ih =>
    intro out h
    contradiction
  case case4 g init inner rest hgen =>
    intro out h
    exact shadowWrittenHere_bound h
  case case5 body hsingle hchain =>
    intro out h
    exact shadowWrittenHere_bound h

private theorem shadowOneRegionStmts_bound {P : String} {Phi : FMap}
    {layout : List Ident} {body out : Block Op}
    (h : StackV2.shadowOneRegionStmts P Phi layout body = some out) :
    BoundEquivBlock D layout body out := by
  exact shadowStableHere_bound (by simpa [StackV2.shadowOneRegionStmts] using h)

theorem iterateRegionRangesFrom_bound (n : Nat) (Phi : FMap)
    (layout : List Ident) (body : Block Op) :
    BoundEquivBlock D layout body
      (StackV2.iterateRegionRangesFrom n Phi layout body) := by
  induction n generalizing body with
  | zero => exact BoundEquivBlock.refl _ _
  | succ n ih =>
      rw [StackV2.iterateRegionRangesFrom]
      cases hp : freshPrefix (stmtsIdents body) with
      | none => exact BoundEquivBlock.refl _ _
      | some P =>
          simp only [hp]
          cases h : StackV2.shadowOneRegionStmts P Phi layout body with
          | none => exact BoundEquivBlock.refl _ _
          | some out => exact (shadowOneRegionStmts_bound h).trans (ih out)

private theorem rangeFunctionStmts_eq_mapFunBodies (n : Nat) : ∀ b : Block Op,
    StackV2.rangeFunctionStmts n b = mapFunBodies
      (fun ps rs body =>
        let (scope, _) := hoistInfos 0 b
        StackV2.iterateRegionRangesFrom n [scope] (ps ++ rs) body) b := by
  intro b
  simp only [StackV2.rangeFunctionStmts]
  generalize hs : (hoistInfos 0 b).1 = scope
  clear hs
  induction b with
  | nil => rfl
  | cons s rest ih =>
      cases s <;> simp [mapFunBodies, ih]
theorem rangeFunctionStmts_equiv (n : Nat) (b : Block Op) :
    EquivBlock D b (StackV2.rangeFunctionStmts n b) := by
  rw [rangeFunctionStmts_eq_mapFunBodies]
  exact mapFunBodies_equiv _ (fun ps rs body => by
    dsimp only
    exact iterateRegionRangesFrom_bound n _ (ps ++ rs) body) b

private theorem nestedRangeFunctionStmts_eq_mapFunBodies : ∀ b : Block Op,
    StackV2.nestedRangeFunctionStmts b = mapFunBodies
      (fun ps rs body =>
        let (scope, _) := hoistInfos 0 b
        match freshPrefix (stmtsIdents body) with
        | some P => (StackV2.shadowInsideExisting P [scope] (ps ++ rs) body).getD body
        | none => body) b := by
  intro b
  simp only [StackV2.nestedRangeFunctionStmts]
  generalize hs : (hoistInfos 0 b).1 = scope
  clear hs
  induction b with
  | nil => rfl
  | cons s rest ih =>
      cases s <;> simp [mapFunBodies, ih]
      all_goals split <;> simp_all

theorem nestedRangeFunctionStmts_equiv (b : Block Op) :
    EquivBlock D b (StackV2.nestedRangeFunctionStmts b) := by
  rw [nestedRangeFunctionStmts_eq_mapFunBodies]
  exact mapFunBodies_equiv _ (fun ps rs body => by
    dsimp only
    cases hp : freshPrefix (stmtsIdents body) with
    | none => exact BoundEquivBlock.refl _ _
    | some P =>
        simp only [hp]
        cases h : StackV2.shadowInsideExisting P _ (ps ++ rs) body with
        | none => exact BoundEquivBlock.refl _ _
        | some out =>
            simpa using shadowInsideExisting_bound P _ (ps ++ rs) h) b

private theorem nestedWrittenRangeFunctionStmts_eq_mapFunBodies : ∀ b : Block Op,
    StackV2.nestedWrittenRangeFunctionStmts b = mapFunBodies
      (fun ps rs body =>
        let (scope, _) := hoistInfos 0 b
        match freshPrefix (stmtsIdents body) with
        | some P =>
            (StackV2.shadowInsideExistingWritten P [scope] (ps ++ rs) body).getD body
        | none => body) b := by
  intro b
  simp only [StackV2.nestedWrittenRangeFunctionStmts]
  generalize hs : (hoistInfos 0 b).1 = scope
  clear hs
  induction b with
  | nil => rfl
  | cons s rest ih =>
      cases s <;> simp [mapFunBodies, ih]
      all_goals split <;> simp_all

theorem nestedWrittenRangeFunctionStmts_equiv (b : Block Op) :
    EquivBlock D b (StackV2.nestedWrittenRangeFunctionStmts b) := by
  rw [nestedWrittenRangeFunctionStmts_eq_mapFunBodies]
  exact mapFunBodies_equiv _ (fun ps rs body => by
    dsimp only
    cases hp : freshPrefix (stmtsIdents body) with
    | none => exact BoundEquivBlock.refl _ _
    | some P =>
        simp only [hp]
        cases h : StackV2.shadowInsideExistingWritten P _ (ps ++ rs) body with
        | none => exact BoundEquivBlock.refl _ _
        | some out =>
            simpa using shadowInsideExistingWritten_bound P _ (ps ++ rs) h) b

theorem iterateNestedRangeFunctionStmts_equiv (n : Nat) (b : Block Op) :
    EquivBlock D b (StackV2.iterateNestedRangeFunctionStmts n b) := by
  induction n generalizing b with
  | zero => exact EquivBlock.refl _
  | succ n ih =>
      rw [StackV2.iterateNestedRangeFunctionStmts]
      exact (nestedRangeFunctionStmts_equiv b).trans
        (ih (StackV2.nestedRangeFunctionStmts b))

theorem aliasFunctionStmts_equiv (b : Block Op) :
    EquivBlock D b (StackV2.aliasFunctionStmts b) := by
  rw [aliasFunctionStmts_eq_mapFunBodies]
  exact mapFunBodies_equiv _ (fun ps rs body =>
    iterateAliasesFrom_bound 4096 (ps ++ rs) body) b

end StackV2Sound

/-- The verified expression-scheduling and liveness-guided stack-layout pass. -/
def stackLayout : Pass D where
  run := stackLayoutBlock
  sound := fun b => by
    simp only [stackLayoutBlock]
    apply (scheduleBlock_equiv b).trans
    apply (iterateCopyBack_equiv 1024 (scheduleStmts b)).trans
    apply (StackV2Sound.scopeDeadFunctionStmts_equiv _).trans
    apply (iterateTailScope_equiv 4096 _).trans
    apply (iterateStackLayout_equiv 4096 _).trans
    apply (StackV2Sound.rangeFunctionStmts_equiv 64 _).trans
    apply (iterateStackLayout_equiv 4096 _).trans
    apply (iterateStackLayout_equiv 4096 _).trans
    apply (StackV2Sound.rangeFunctionStmts_equiv 64 _).trans
    apply (StackV2Sound.aliasFunctionStmts_equiv _).trans
    apply (StackV2Sound.rangeFunctionStmts_equiv 64 _).trans
    apply (StackV2Sound.iterateNestedRangeFunctionStmts_equiv 1 _).trans
    apply (StackV2Sound.nestedWrittenRangeFunctionStmts_equiv _).trans
    apply (iterateStackLayout_equiv 4096 _).trans
    apply (StackV2Sound.aliasFunctionStmts_equiv _).trans
    apply (StackV2Sound.scopeDeadFunctionStmts_equiv _).trans
    exact stageCallsBlock_equiv _

@[simp] theorem stackLayout_run (b : Block Op) :
    (stackLayout (calls := calls) (creates := creates)).run b = stackLayoutBlock b := rfl

end YulEvmCompiler.Optimizer
