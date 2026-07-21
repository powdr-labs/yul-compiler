import YulEvmCompiler.Optimizer.Implementation.StackLayout
import YulEvmCompiler.Optimizer.Implementation.InlineCallsSound
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

/-- The verified expression-scheduling and liveness-guided stack-layout pass. -/
def stackLayout : Pass D where
  run := stackLayoutBlock
  sound := fun b => (scheduleBlock_equiv b).trans
    ((iterateStackLayout_equiv 1024 (scheduleStmts b)).trans
      (iterateTailScope_equiv 1024
        (iterateStackLayout 1024 (scheduleStmts b))))

@[simp] theorem stackLayout_run (b : Block Op) :
    (stackLayout (calls := calls) (creates := creates)).run b = stackLayoutBlock b := rfl

end YulEvmCompiler.Optimizer
