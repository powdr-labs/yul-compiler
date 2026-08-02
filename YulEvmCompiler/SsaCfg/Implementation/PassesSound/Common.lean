import YulEvmCompiler.SsaCfg.Implementation.Passes
import YulEvmCompiler.SsaCfg.Spec.Sem
import YulEvmCompiler.SsaCfg.Implementation.ToAsm
import YulSemantics.Dialect.EVM
set_option warningAsError true

/-!
# YulEvmCompiler.SsaCfg.Implementation.PassesSound.Common

Shared plumbing for every pass proof.

The call-depth-indexed execution relation `ExecN` and its bridge to `Exec`,
`Regs` lemmas, the read/def sets and single-assignment facts, the decidable
dominance check unpacked into the backward-liveness fixed point
(§ `ToAsm`), and entry-rooted definition provenance (`EntryPath`).
-/

namespace YulEvmCompiler.SsaCfg
open YulSemantics.EVM (U256 EvmState Op builtinWithExternal stepOp ExternalCalls
  ExternalCreates)
open YulSemantics (Outcome)

/-! ## Call-depth-indexed execution

`ExecN P n f R st rest res` is the ordinary `Exec` judgment equipped with an
upper bound on the dynamic user-call depth.  Instructions and intra-function
control flow preserve the bound.  At a returning call, the callee runs at
bound `n` while the caller continuation (and the complete call) runs at bound
`n + 1`; a halting call only has the callee premise.  Leaf rules are available
at every bound, which makes the judgment monotone.

This separate inductive is needed below because an `Exec` proof lives in
`Prop`, so its call depth cannot be computed by eliminating it into `Nat`.
-/

inductive ExecN (P : Prog) [model : ExternalModel] :
    Nat → Func → Regs → EvmState → Rest → FRes → Prop
  | const {n : Nat} {f : Func} {R : Regs} {st : EvmState} {d : ValId} {v : U256}
      {is : List Instr} {t : Term} {res : FRes} :
      ExecN P n f (R.set d v) st ⟨is, t⟩ res →
      ExecN P n f R st ⟨.const d v :: is, t⟩ res
  | op {n : Nat} {f : Func} {R : Regs} {st st' : EvmState} {ds : List ValId}
      {yop : Op} {as : List ValId} {args rets : List U256} {is : List Instr}
      {t : Term} {res : FRes} :
      R.getMany as = some args →
      builtinWithExternal model.calls model.creates yop args st (.ok rets st') →
      ds.length = rets.length →
      ExecN P n f (R.setMany ds rets) st' ⟨is, t⟩ res →
      ExecN P n f R st ⟨.op ds yop as :: is, t⟩ res
  | opHalt {n : Nat} {f : Func} {R : Regs} {st st' : EvmState}
      {ds : List ValId} {yop : Op} {as : List ValId} {args : List U256}
      {is : List Instr} {t : Term} :
      R.getMany as = some args →
      builtinWithExternal model.calls model.creates yop args st (.halt st') →
      ExecN P n f R st ⟨.op ds yop as :: is, t⟩ (.halt st')
  | call {n : Nat} {f g : Func} {R : Regs} {st st' : EvmState}
      {ds as : List ValId} {fid : FuncId} {args rvals : List U256} {eb : Block}
      {is : List Instr} {t : Term} {res : FRes} :
      P.funcs[fid]? = some g →
      R.getMany as = some args →
      g.params.length = args.length →
      g.blocks[g.entry]? = some eb →
      ExecN P n g (Regs.empty.setMany g.params args) st
        ⟨eb.instrs, eb.term⟩ (.ret rvals st') →
      ds.length = rvals.length →
      ExecN P (n + 1) f (R.setMany ds rvals) st' ⟨is, t⟩ res →
      ExecN P (n + 1) f R st ⟨.call ds fid as :: is, t⟩ res
  | callHalt {n : Nat} {f g : Func} {R : Regs} {st st' : EvmState}
      {ds as : List ValId} {fid : FuncId} {args : List U256} {eb : Block}
      {is : List Instr} {t : Term} :
      P.funcs[fid]? = some g →
      R.getMany as = some args →
      g.params.length = args.length →
      g.blocks[g.entry]? = some eb →
      ExecN P n g (Regs.empty.setMany g.params args) st
        ⟨eb.instrs, eb.term⟩ (.halt st') →
      ExecN P (n + 1) f R st ⟨.call ds fid as :: is, t⟩ (.halt st')
  | jump {n : Nat} {f : Func} {R : Regs} {st : EvmState} {e : Edge}
      {tb : Block} {args : List U256} {res : FRes} :
      f.blocks[e.target]? = some tb →
      R.getMany e.args = some args →
      tb.params.length = args.length →
      ExecN P n f (R.setMany tb.params args) st ⟨tb.instrs, tb.term⟩ res →
      ExecN P n f R st ⟨[], .jump e⟩ res
  | branchTrue {n : Nat} {f : Func} {R : Regs} {st : EvmState}
      {c : ValId} {v : U256} {et ef : Edge} {tb : Block} {args : List U256}
      {res : FRes} :
      R c = some v → v ≠ 0 →
      f.blocks[et.target]? = some tb →
      R.getMany et.args = some args →
      tb.params.length = args.length →
      ExecN P n f (R.setMany tb.params args) st ⟨tb.instrs, tb.term⟩ res →
      ExecN P n f R st ⟨[], .branch c et ef⟩ res
  | branchFalse {n : Nat} {f : Func} {R : Regs} {st : EvmState}
      {c : ValId} {et ef : Edge} {tb : Block} {args : List U256} {res : FRes} :
      R c = some 0 →
      f.blocks[ef.target]? = some tb →
      R.getMany ef.args = some args →
      tb.params.length = args.length →
      ExecN P n f (R.setMany tb.params args) st ⟨tb.instrs, tb.term⟩ res →
      ExecN P n f R st ⟨[], .branch c et ef⟩ res
  | ret {n : Nat} {f : Func} {R : Regs} {st : EvmState} {xs : List ValId}
      {vals : List U256} :
      R.getMany xs = some vals →
      ExecN P n f R st ⟨[], .ret xs⟩ (.ret vals st)
  | halt {n : Nat} {f : Func} {R : Regs} {st st' : EvmState} {yop : Op}
      {as : List ValId} {args : List U256} :
      R.getMany as = some args →
      builtinWithExternal model.calls model.creates yop args st (.halt st') →
      ExecN P n f R st ⟨[], .halt yop as⟩ (.halt st')

/-- A call-depth bound can always be enlarged. -/
theorem ExecN.mono {P : Prog} {n m : Nat} {f : Func} {R : Regs}
    {st : EvmState} {rest : Rest} {res : FRes}
    (h : ExecN (model := model) P n f R st rest res) (hnm : n ≤ m) :
    ExecN (model := model) P m f R st rest res := by
  induction h generalizing m with
  | const htail ih => exact ExecN.const (ih hnm)
  | op hget hop hlen htail ih => exact ExecN.op hget hop hlen (ih hnm)
  | opHalt hget hop => exact ExecN.opHalt hget hop
  | @call n f g R st st' ds as fid args rvals eb is t res
      hfid hget hplen heb hbody hlen htail ihbody ih =>
      have hmpos : 0 < m := lt_of_lt_of_le (Nat.zero_lt_succ n) (by simpa using hnm)
      obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hmpos)
      exact ExecN.call hfid hget hplen heb (ihbody (by omega)) hlen (ih (by omega))
  | @callHalt n f g R st st' ds as fid args eb is t
      hfid hget hplen heb hbody ihbody =>
      have hmpos : 0 < m := lt_of_lt_of_le (Nat.zero_lt_succ n) (by simpa using hnm)
      obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hmpos)
      exact ExecN.callHalt hfid hget hplen heb (ihbody (by omega))
  | jump htb hget hplen htail ih => exact ExecN.jump htb hget hplen (ih hnm)
  | branchTrue hc hv htb hget hplen htail ih =>
      exact ExecN.branchTrue hc hv htb hget hplen (ih hnm)
  | branchFalse hc htb hget hplen htail ih =>
      exact ExecN.branchFalse hc htb hget hplen (ih hnm)
  | ret hget => exact ExecN.ret hget
  | halt hget hop => exact ExecN.halt hget hop

/-- Forgetting the call-depth index recovers the ordinary semantics. -/
theorem ExecN.toExec {P : Prog} {n : Nat} {f : Func} {R : Regs}
    {st : EvmState} {rest : Rest} {res : FRes}
    (h : ExecN (model := model) P n f R st rest res) :
    Exec (model := model) P f R st rest res := by
  induction h with
  | const htail ih => exact Exec.const ih
  | op hget hop hlen htail ih => exact Exec.op hget hop hlen ih
  | opHalt hget hop => exact Exec.opHalt hget hop
  | call hfid hget hplen heb hbody hlen htail ihbody ih =>
      exact Exec.call hfid hget hplen heb ihbody hlen ih
  | callHalt hfid hget hplen heb hbody ihbody =>
      exact Exec.callHalt hfid hget hplen heb ihbody
  | jump htb hget hplen htail ih => exact Exec.jump htb hget hplen ih
  | branchTrue hc hv htb hget hplen htail ih =>
      exact Exec.branchTrue hc hv htb hget hplen ih
  | branchFalse hc htb hget hplen htail ih =>
      exact Exec.branchFalse hc htb hget hplen ih
  | ret hget => exact Exec.ret hget
  | halt hget hop => exact Exec.halt hget hop

/-- Every terminating execution admits a finite call-depth bound. -/
theorem Exec.toExecN {P : Prog} {f : Func} {R : Regs} {st : EvmState}
    {rest : Rest} {res : FRes} (h : Exec (model := model) P f R st rest res) :
    ∃ n, ExecN (model := model) P n f R st rest res := by
  induction h with
  | const htail ih => obtain ⟨n, hn⟩ := ih; exact ⟨n, ExecN.const hn⟩
  | op hget hop hlen htail ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n, ExecN.op hget hop hlen hn⟩
  | opHalt hget hop => exact ⟨0, ExecN.opHalt hget hop⟩
  | call hfid hget hplen heb hbody hlen htail ihbody ih =>
      obtain ⟨nb, hnb⟩ := ihbody
      obtain ⟨nt, hnt⟩ := ih
      refine ⟨nb + nt + 1, ExecN.call hfid hget hplen heb
        (hnb.mono (by omega)) hlen ?_⟩
      exact hnt.mono (by omega)
  | callHalt hfid hget hplen heb hbody ihbody =>
      obtain ⟨n, hn⟩ := ihbody
      exact ⟨n + 1, ExecN.callHalt hfid hget hplen heb hn⟩
  | jump htb hget hplen htail ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n, ExecN.jump htb hget hplen hn⟩
  | branchTrue hc hv htb hget hplen htail ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n, ExecN.branchTrue hc hv htb hget hplen hn⟩
  | branchFalse hc htb hget hplen htail ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n, ExecN.branchFalse hc htb hget hplen hn⟩
  | ret hget => exact ⟨0, ExecN.ret hget⟩
  | halt hget hop => exact ⟨0, ExecN.halt hget hop⟩

/-! ## `Regs` plumbing -/

namespace Regs

theorem setMany_nil_left (R : Regs) (vs : List U256) : R.setMany [] vs = R := rfl

theorem setMany_nil_right (R : Regs) (xs : List ValId) : R.setMany xs [] = R := by
  cases xs <;> rfl

theorem setMany_cons (R : Regs) (x : ValId) (xs : List ValId) (v : U256) (vs : List U256) :
    R.setMany (x :: xs) (v :: vs) = (R.set x v).setMany xs vs := rfl

/-- Parallel binding leaves an id outside the destination list untouched. -/
theorem setMany_of_not_mem (R : Regs) {d : ValId} (xs : List ValId) (vs : List U256)
    (hd : d ∉ xs) : (R.setMany xs vs) d = R d := by
  induction xs generalizing R vs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mem_cons, not_or] at hd
    cases vs with
    | nil => rw [setMany_nil_right]
    | cons v vs =>
      rw [setMany_cons, ih (R := R.set x v) (vs := vs) hd.2]
      exact set_other R v hd.1

/-- Reading a list of ids only depends on the register file at those ids. -/
theorem getMany_congr {R1 R2 : Regs} {xs : List ValId} (h : ∀ x ∈ xs, R1 x = R2 x) :
    R1.getMany xs = R2.getMany xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [getMany_cons, getMany_cons, h x (by simp), ih (fun y hy => h y (by simp [hy]))]

/-- Agreement on a set of ids survives one binding (the same one on both sides). -/
theorem set_congr {S : ValId → Prop} {R1 R2 : Regs} (h : ∀ x, S x → R1 x = R2 x)
    (d : ValId) (v : U256) : ∀ x, S x → (R1.set d v) x = (R2.set d v) x := by
  intro x hx
  by_cases hxd : x = d
  · simp [set, hxd]
  · simp [set, hxd, h x hx]

/-- Agreement on a set of ids survives a parallel binding. -/
theorem setMany_congr {S : ValId → Prop} {R1 R2 : Regs} (h : ∀ x, S x → R1 x = R2 x)
    (xs : List ValId) (vs : List U256) :
    ∀ x, S x → (R1.setMany xs vs) x = (R2.setMany xs vs) x := by
  induction xs generalizing R1 R2 vs with
  | nil => simpa [setMany_nil_left] using h
  | cons y ys ih =>
    cases vs with
    | nil => simpa [setMany_nil_right] using h
    | cons v vs => simpa [setMany_cons] using ih (set_congr h y v) (vs := vs)

/-- Read a use list after substitution when the two register files agree on
the original uses modulo that substitution. -/
theorem getMany_substVs {σ : Passes.Subst} {R R' : Regs}
    {xs : List ValId} {vs : List U256}
    (hagree : ∀ x ∈ xs, R x = R' (Passes.substV σ x))
    (hget : R.getMany xs = some vs) :
    R'.getMany (Passes.substVs σ xs) = some vs := by
  induction xs generalizing vs with
  | nil => simpa [Passes.substVs] using hget
  | cons x xs ih =>
      rw [getMany_cons] at hget
      cases hx : R x with
      | none => simp [hx] at hget
      | some v =>
          cases htail : R.getMany xs with
          | none => simp [hx, htail] at hget
          | some vals =>
              simp only [hx, htail, Option.bind_some, Option.map_some,
                Option.some.injEq] at hget
              subst vs
              have hx' : R' (Passes.substV σ x) = some v := by
                rw [← hagree x (by simp), hx]
              have ht' := ih (fun y hy => hagree y (by simp [hy])) htail
              simpa [Passes.substVs, getMany_cons, hx'] using ht'

end Regs

/-! ## Read sets -/

/-- Every value read anywhere in a function (all blocks, instructions and
terminators). A jump can transfer control to any block of `f`, so this is the
read set a register-agreement frame has to fix. -/
def Func.allUses (f : Func) : List ValId :=
  f.blocks.toList.flatMap fun b => b.instrs.flatMap Instr.uses ++ b.term.uses

/-! ## Single assignment

`wfCheck` gives `Func.allDefs.Nodup`; these lemmas turn that into the form the
value-level passes need — a value has exactly one definition site, so any
binding of it in any execution comes from *that* instruction. The argument is by
counting occurrences in `allDefs`, which avoids index arithmetic through the
nested `flatMap`. -/

theorem one_le_count_flatMap {α β : Type} [DecidableEq β] {l : List α} {g : α → List β}
    {x : α} {d : β} (hx : x ∈ l) (hd : d ∈ g x) : 1 ≤ (l.flatMap g).count d :=
  List.count_pos_iff.mpr (List.mem_flatMap.mpr ⟨x, hx, hd⟩)

theorem count_le_count_flatMap {α β : Type} [DecidableEq β] {l : List α} {g : α → List β}
    {x : α} {d : β} (hx : x ∈ l) : (g x).count d ≤ (l.flatMap g).count d := by
  induction l with
  | nil => simp at hx
  | cons a rest ih =>
    rw [List.flatMap_cons, List.count_append]
    rcases List.mem_cons.mp hx with rfl | hx'
    · omega
    · have := ih hx'; omega

theorem two_le_count_flatMap {α β : Type} [DecidableEq β] {l : List α} {g : α → List β}
    {x y : α} {d : β} (hx : x ∈ l) (hy : y ∈ l) (hne : x ≠ y)
    (hdx : d ∈ g x) (hdy : d ∈ g y) : 2 ≤ (l.flatMap g).count d := by
  induction l with
  | nil => simp at hx
  | cons a rest ih =>
    rw [List.flatMap_cons, List.count_append]
    rcases List.mem_cons.mp hx with rfl | hx'
    · have hy' : y ∈ rest := by
        rcases List.mem_cons.mp hy with rfl | h
        · exact absurd rfl hne
        · exact h
      have h1 : 1 ≤ (g x).count d := List.count_pos_iff.mpr hdx
      have h2 : 1 ≤ (rest.flatMap g).count d := one_le_count_flatMap hy' hdy
      omega
    · rcases List.mem_cons.mp hy with rfl | hy'
      · have h1 : 1 ≤ (g y).count d := List.count_pos_iff.mpr hdy
        have h2 : 1 ≤ (rest.flatMap g).count d := one_le_count_flatMap hx' hdx
        omega
      · have := ih hx' hy'
        omega

/-! ### Single assignment: one definition site per value -/

/-- The per-block contribution to `Func.allDefs`. -/
abbrev blockAllDefs (b : Block) : List ValId := b.params ++ b.instrs.flatMap Instr.defs

theorem allDefs_eq (f : Func) :
    f.allDefs = f.params ++ f.blocks.toList.flatMap blockAllDefs := rfl

theorem two_le_count_allDefs {f : Func} {d : ValId}
    (h2 : 2 ≤ (f.blocks.toList.flatMap blockAllDefs).count d) : ¬ f.allDefs.Nodup := by
  intro hnd
  have hle := List.nodup_iff_count_le_one.mp hnd d
  rw [allDefs_eq, List.count_append] at hle
  omega

/-- **Single assignment, instruction form**: two instructions of a well-formed
function that define the same value are the same instruction. -/
theorem instr_def_unique {f : Func} (h : f.allDefs.Nodup)
    {b1 b2 : Block} (hb1 : b1 ∈ f.blocks.toList) (hb2 : b2 ∈ f.blocks.toList)
    {x1 x2 : Instr} (hx1 : x1 ∈ b1.instrs) (hx2 : x2 ∈ b2.instrs)
    {d : ValId} (hd1 : d ∈ x1.defs) (hd2 : d ∈ x2.defs) : x1 = x2 := by
  by_contra hne
  refine two_le_count_allDefs (f := f) (d := d) ?_ h
  by_cases hb : b1 = b2
  · subst hb
    have h2 : 2 ≤ (b1.instrs.flatMap Instr.defs).count d :=
      two_le_count_flatMap hx1 hx2 hne hd1 hd2
    have hle : (blockAllDefs b1).count d ≤ (f.blocks.toList.flatMap blockAllDefs).count d :=
      count_le_count_flatMap hb1
    rw [show blockAllDefs b1 = b1.params ++ b1.instrs.flatMap Instr.defs from rfl,
      List.count_append] at hle
    omega
  · refine two_le_count_flatMap hb1 hb2 hb ?_ ?_ <;>
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, by assumption, by assumption⟩)

/-- **Single assignment, parameter form**: a block parameter is never also an
instruction destination. -/
theorem param_not_instr_def {f : Func} (h : f.allDefs.Nodup)
    {b1 b2 : Block} (hb1 : b1 ∈ f.blocks.toList) (hb2 : b2 ∈ f.blocks.toList)
    {x : Instr} (hx : x ∈ b2.instrs) {d : ValId} (hp : d ∈ b1.params) (hd : d ∈ x.defs) :
    False := by
  refine two_le_count_allDefs (f := f) (d := d) ?_ h
  by_cases hb : b1 = b2
  · subst hb
    have h1 : 1 ≤ b1.params.count d := List.count_pos_iff.mpr hp
    have h2 : 1 ≤ (b1.instrs.flatMap Instr.defs).count d := one_le_count_flatMap hx hd
    have hle : (blockAllDefs b1).count d ≤ (f.blocks.toList.flatMap blockAllDefs).count d :=
      count_le_count_flatMap hb1
    rw [show blockAllDefs b1 = b1.params ++ b1.instrs.flatMap Instr.defs from rfl,
      List.count_append] at hle
    omega
  · exact two_le_count_flatMap hb1 hb2 hb (List.mem_append_left _ hp)
      (List.mem_append_right _ (List.mem_flatMap.mpr ⟨x, hx, hd⟩))

/-- **Single assignment, function-parameter form**. -/
theorem funcParam_not_instr_def {f : Func} (h : f.allDefs.Nodup)
    {b : Block} (hb : b ∈ f.blocks.toList) {x : Instr} (hx : x ∈ b.instrs)
    {d : ValId} (hp : d ∈ f.params) (hd : d ∈ x.defs) : False := by
  have hle := List.nodup_iff_count_le_one.mp h d
  rw [allDefs_eq, List.count_append] at hle
  have h1 : 1 ≤ f.params.count d := List.count_pos_iff.mpr hp
  have h2 : 1 ≤ (f.blocks.toList.flatMap blockAllDefs).count d :=
    one_le_count_flatMap hb (List.mem_append_right _ (List.mem_flatMap.mpr ⟨x, hx, hd⟩))
  omega

/-! ## Dominance: the backward-liveness fixed point

`ToAsm.Func.domCheck` decides SSA dominance as "nothing but the function's
parameters is live into the entry block" (backward liveness, `ToAsm.liveInSets`).
This section unpacks that check into the three facts a pass proof needs:

* `ToAsm.liveIn_of_uses` — a value a block reads and does not define is live
  into it;
* `ToAsm.liveIn_of_succ` — liveness propagates backwards along edges;
* `ToAsm.domCheck_entry` — under the check, `liveIn(entry) ⊆ f.params`.

Chaining the first two along a definition-free path and hitting the third is
exactly the argument "a non-dominated use is impossible". -/

namespace ToAsm

/-! ### Sorted-set membership -/

theorem mem_insertSorted {x v : ValId} {l : List ValId} :
    x ∈ insertSorted v l ↔ x = v ∨ x ∈ l := by
  induction l with
  | nil => simp [insertSorted]
  | cons w rest ih =>
    by_cases h1 : v < w
    · simp [insertSorted, h1]
    · by_cases h2 : v = w
      · subst h2; simp [insertSorted]
      · simp only [insertSorted, h1, h2, if_false, List.mem_cons, ih]
        constructor
        · rintro (rfl | rfl | h) <;> simp_all
        · rintro (rfl | rfl | h) <;> simp_all

theorem mem_unionS {x : ValId} {xs ys : List ValId} :
    x ∈ unionS xs ys ↔ x ∈ xs ∨ x ∈ ys := by
  unfold unionS
  induction xs generalizing ys with
  | nil => simp
  | cons a as ih =>
    simp only [List.foldl_cons, ih, mem_insertSorted, List.mem_cons]
    tauto

theorem mem_diffS {x : ValId} {xs ys : List ValId} :
    x ∈ diffS xs ys ↔ x ∈ xs ∧ x ∉ ys := by
  simp [diffS, List.mem_filter]

theorem mem_blockUses {x : ValId} {b : Block} :
    x ∈ blockUses b ↔ x ∈ b.instrs.flatMap Instr.uses ∨ x ∈ b.term.uses := by
  simp [blockUses, mem_unionS]

theorem mem_blockDefs {x : ValId} {b : Block} :
    x ∈ blockDefs b ↔ x ∈ b.params ∨ x ∈ b.instrs.flatMap Instr.defs := by
  simp [blockDefs, mem_unionS, List.mem_append]

/-! ### The liveness fixed point -/

theorem liveInSets_go_fix {f : Func} {fuel : Nat} {cur li : Array (List ValId)}
    (h : liveInSets.go f fuel cur = some li) : liveStep f li = li := by
  induction fuel generalizing cur with
  | zero => simp [liveInSets.go] at h
  | succ n ih =>
    rw [liveInSets.go] at h
    split at h
    · rename_i heq
      obtain rfl := Option.some.inj h
      exact (beq_iff_eq).mp heq
    · exact ih h

/-- `liveInSets` returns a genuine fixed point of the backward liveness step. -/
theorem liveInSets_fix {f : Func} {li : Array (List ValId)} (h : liveInSets f = some li) :
    liveStep f li = li := liveInSets_go_fix (by unfold liveInSets at h; exact h)

theorem liveStep_size {f : Func} {li : Array (List ValId)} :
    (liveStep f li).size = f.blocks.size := by simp [liveStep]

/-- One liveness step read off at one block. -/
theorem liveStep_get_eq {f : Func} {A : Array (List ValId)} {i : Nat} {b : Block}
    (hb : f.blocks[i]? = some b) :
    (liveStep f A)[i]?.getD [] =
      diffS (unionS (blockUses b)
        (b.term.edges.foldl (init := []) fun acc (e : Edge) => unionS (A[e.target]?.getD []) acc))
        (blockDefs b) := by
  have hlt : i < f.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  have hsz : i < (liveStep f A).size := by rw [liveStep_size]; exact hlt
  rw [Array.getElem?_eq_getElem hsz]
  simp only [Option.getD_some, liveStep, Array.getElem_ofFn]
  simp [hb]

theorem liveStep_get_none {f : Func} {A : Array (List ValId)} {i : Nat}
    (hb : f.blocks[i]? = none) : (liveStep f A)[i]?.getD [] = [] := by
  rcases h : (liveStep f A)[i]? with _ | l
  · simp
  · have hlt : i < (liveStep f A).size := (Array.getElem?_eq_some_iff.mp h).1
    have hlt' : i < f.blocks.size := by rw [liveStep_size] at hlt; exact hlt
    exact absurd hb (by simp [Array.getElem?_eq_getElem hlt'])

/-- The fixed-point equation, at one block. -/
theorem liveIn_eq {f : Func} {li : Array (List ValId)} (h : liveInSets f = some li)
    {i : BlockId} {b : Block} (hb : f.blocks[i]? = some b) :
    li[i]?.getD [] =
      diffS (unionS (blockUses b)
        (b.term.edges.foldl (init := []) fun acc (e : Edge) => unionS (li[e.target]?.getD []) acc))
        (blockDefs b) := by
  conv_lhs => rw [← liveInSets_fix h]
  exact liveStep_get_eq hb

/-- Membership in the `liveOut` union over a block's outgoing edges. -/
theorem mem_lout {li : Array (List ValId)} {x : ValId} {edges : List Edge}
    {acc0 : List ValId} :
    x ∈ edges.foldl (fun acc (e : Edge) => unionS (li[e.target]?.getD []) acc) acc0 ↔
      (∃ e ∈ edges, x ∈ li[e.target]?.getD []) ∨ x ∈ acc0 := by
  induction edges generalizing acc0 with
  | nil => simp
  | cons e es ih =>
    simp only [List.foldl_cons, ih, mem_unionS, List.mem_cons]
    constructor
    · rintro (⟨e', he', hx'⟩ | hx | hacc)
      · exact Or.inl ⟨e', Or.inr he', hx'⟩
      · exact Or.inl ⟨e, Or.inl rfl, hx⟩
      · exact Or.inr hacc
    · rintro (⟨e', (rfl | he'), hx'⟩ | hacc)
      · exact Or.inr (Or.inl hx')
      · exact Or.inl ⟨e', he', hx'⟩
      · exact Or.inr (Or.inr hacc)

/-- A value a block reads but does not define is live into that block. -/
theorem liveIn_of_uses {f : Func} {li : Array (List ValId)} (h : liveInSets f = some li)
    {i : BlockId} {b : Block} (hb : f.blocks[i]? = some b) {x : ValId}
    (hu : x ∈ blockUses b) (hd : x ∉ blockDefs b) : x ∈ li[i]?.getD [] := by
  rw [liveIn_eq h hb, mem_diffS]
  exact ⟨mem_unionS.mpr (Or.inl hu), hd⟩

/-- A value live into a successor and not defined by the block is live into the block. -/
theorem liveIn_of_succ {f : Func} {li : Array (List ValId)} (h : liveInSets f = some li)
    {i : BlockId} {b : Block} (hb : f.blocks[i]? = some b) {e : Edge} {x : ValId}
    (he : e ∈ b.term.edges) (hx : x ∈ li[e.target]?.getD []) (hd : x ∉ blockDefs b) :
    x ∈ li[i]?.getD [] := by
  rw [liveIn_eq h hb, mem_diffS]
  exact ⟨mem_unionS.mpr (Or.inr (mem_lout.mpr (Or.inl ⟨e, he, hx⟩))), hd⟩

/-- **The content of the dominance check**: nothing but the function's own
parameters is live into the entry block. Together with `liveIn_of_uses` and
`liveIn_of_succ` this is the whole of "every use is dominated by its
definition": a use whose definition does not dominate it induces a
definition-free path back to the entry, along which backward liveness carries
the value into `liveIn(entry)`. -/
theorem domCheck_entry {f : Func} {li : Array (List ValId)} (hli : liveInSets f = some li)
    (hdom : Func.domCheck f = true) {x : ValId} (hx : x ∈ li[f.entry]?.getD []) :
    x ∈ f.params := by
  unfold Func.domCheck at hdom
  rw [hli] at hdom
  simp only [decide_eq_true_eq] at hdom
  by_contra hp
  have : x ∈ diffS (li[f.entry]?.getD []) f.params := mem_diffS.mpr ⟨hx, hp⟩
  rw [hdom] at this
  exact absurd this (by simp)

theorem Prog.domCheck_main {P : Prog} (h : Prog.domCheck P = true) :
    Func.domCheck P.main = true := ((Bool.and_eq_true _ _).mp h).1

theorem Prog.domCheck_funcs {P : Prog} (h : Prog.domCheck P = true) {g : Func}
    (hg : g ∈ P.funcs) : Func.domCheck g = true := by
  have hall := ((Bool.and_eq_true _ _).mp h).2
  rw [Array.all_eq_true] at hall
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hg
  exact hall i hi

/-! ### Least fixed point (for dominance *preservation*) -/

/-- Pointwise inclusion of liveness maps (total: an out-of-range read is `[]`). -/
def Sub (A B : Array (List ValId)) : Prop :=
  ∀ (i : Nat) (x : ValId), x ∈ A[i]?.getD [] → x ∈ B[i]?.getD []

theorem sub_replicate {n : Nat} {B : Array (List ValId)} :
    Sub (Array.replicate n []) B := by
  intro i x hx
  rcases h : (Array.replicate n ([] : List ValId))[i]? with _ | l
  · rw [h] at hx; simp at hx
  · rw [h] at hx
    have hl : l = [] := by
      obtain ⟨hlt, hget⟩ := Array.getElem?_eq_some_iff.mp h
      simpa using hget.symm
    rw [hl] at hx; simp at hx

/-- The backward liveness step is monotone. -/
theorem liveStep_mono {f : Func} {A B : Array (List ValId)} (h : Sub A B) :
    Sub (liveStep f A) (liveStep f B) := by
  intro i x hx
  rcases hb : f.blocks[i]? with _ | b
  · rw [liveStep_get_none hb] at hx; simp at hx
  · rw [liveStep_get_eq hb] at hx ⊢
    rw [mem_diffS] at hx ⊢
    refine ⟨?_, hx.2⟩
    rcases mem_unionS.mp hx.1 with hu | hl
    · exact mem_unionS.mpr (Or.inl hu)
    · rcases mem_lout.mp hl with ⟨e, he, hxe⟩ | hnil
      · exact mem_unionS.mpr (Or.inr (mem_lout.mpr (Or.inl ⟨e, he, h _ _ hxe⟩)))
      · simp at hnil

/-- **`liveInSets` is the least fixed point**: it is bounded by every pre-fixed
point of the liveness step. This is the engine for dominance *preservation* — to
show a rewritten function still passes `domCheck` it suffices to exhibit a
pre-fixed point built from the original's live sets. -/
theorem liveInSets_least {f : Func} {li ub : Array (List ValId)}
    (h : liveInSets f = some li) (hub : Sub (liveStep f ub) ub) : Sub li ub := by
  have key : ∀ (fuel : Nat) (cur : Array (List ValId)), Sub cur ub →
      ∀ {out}, liveInSets.go f fuel cur = some out → Sub out ub := by
    intro fuel
    induction fuel with
    | zero => intro cur _ out hgo; simp [liveInSets.go] at hgo
    | succ n ih =>
      intro cur hcur out hgo
      rw [liveInSets.go] at hgo
      split at hgo
      · obtain rfl := Option.some.inj hgo; exact hcur
      · exact ih _ (fun i x hx => hub i x (liveStep_mono hcur i x hx)) hgo
  unfold liveInSets at h
  exact key _ _ sub_replicate h

/-! ### Convergence of the liveness fixed point

`Func.domCheck` is `false` *by definition* when `liveInSets` runs out of fuel, so
every statement about dominance preservation first needs to know that it never
does. `liveInSets_isSome` below closes that gap: the iterates increase (Kleene,
from `liveStep_mono`), each is contained in the finite universe of ids the
function mentions, and the sum of their sizes strictly increases at every
non-exiting round — so the fuel `blocks.size * (total + 1) + 2` always
suffices. -/

/-! ### Sortedness of the helper sets -/

theorem nodup_of_pairwise_lt {l : List ValId} (h : l.Pairwise (· < ·)) : l.Nodup :=
  h.imp (fun hlt => Nat.ne_of_lt hlt)

theorem insertSorted_pairwise {v : ValId} {l : List ValId} (h : l.Pairwise (· < ·)) :
    (insertSorted v l).Pairwise (· < ·) := by
  induction l with
  | nil => simp [insertSorted]
  | cons w rest ih =>
    rw [List.pairwise_cons] at h
    by_cases h1 : v < w
    · simp only [insertSorted, h1, if_true]
      refine List.pairwise_cons.mpr ⟨?_, List.pairwise_cons.mpr ⟨h.1, h.2⟩⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact h1
      · exact Nat.lt_trans h1 (h.1 y hy)
    · by_cases h2 : v = w
      · subst h2
        simp only [insertSorted, h1, if_false]
        exact List.pairwise_cons.mpr ⟨h.1, h.2⟩
      · simp only [insertSorted, h1, h2, if_false]
        refine List.pairwise_cons.mpr ⟨?_, ih h.2⟩
        intro y hy
        rcases mem_insertSorted.mp hy with rfl | hy
        · exact Nat.lt_of_le_of_ne (Nat.not_lt.mp h1) (fun heq => h2 heq.symm)
        · exact h.1 y hy

theorem unionS_pairwise {xs ys : List ValId} (h : ys.Pairwise (· < ·)) :
    (unionS xs ys).Pairwise (· < ·) := by
  unfold unionS
  induction xs generalizing ys with
  | nil => exact h
  | cons a as ih => exact ih (insertSorted_pairwise h)

theorem diffS_pairwise {xs ys : List ValId} (h : xs.Pairwise (· < ·)) :
    (diffS xs ys).Pairwise (· < ·) :=
  h.sublist List.filter_sublist

/-! ### Extensionality: a sorted list is determined by its elements -/

theorem pairwise_lt_ext : ∀ {l1 l2 : List ValId}, l1.Pairwise (· < ·) → l2.Pairwise (· < ·) →
    (∀ x, x ∈ l1 ↔ x ∈ l2) → l1 = l2 := by
  intro l1
  induction l1 with
  | nil =>
    intro l2 _ _ hmem
    cases l2 with
    | nil => rfl
    | cons b t2 => exact absurd ((hmem b).mpr (by simp)) (by simp)
  | cons a t ih =>
    intro l2 h1 h2 hmem
    cases l2 with
    | nil => exact absurd ((hmem a).mp (by simp)) (by simp)
    | cons b t2 =>
      rw [List.pairwise_cons] at h1 h2
      have hab : a = b := by
        by_contra hne
        have ha : a ∈ b :: t2 := (hmem a).mp (by simp)
        have hb : b ∈ a :: t := (hmem b).mpr (by simp)
        rcases List.mem_cons.mp ha with rfl | ha'
        · exact hne rfl
        rcases List.mem_cons.mp hb with rfl | hb'
        · exact hne rfl
        exact absurd (Nat.lt_trans (h1.1 b hb') (h2.1 a ha')) (Nat.lt_irrefl _)
      subst hab
      refine congrArg (a :: ·) (ih h1.2 h2.2 ?_)
      intro x
      constructor
      · intro hx
        rcases List.mem_cons.mp ((hmem x).mp (by simp [hx])) with rfl | hx'
        · exact absurd (h1.1 x hx) (Nat.lt_irrefl _)
        · exact hx'
      · intro hx
        rcases List.mem_cons.mp ((hmem x).mpr (by simp [hx])) with rfl | hx'
        · exact absurd (h2.1 x hx) (Nat.lt_irrefl _)
        · exact hx'

/-! ### Iterate invariants -/

/-- Every id any liveness iterate can contain. -/
def liveUniverse (f : Func) : List ValId := f.blocks.toList.flatMap blockUses

theorem mem_liveUniverse {f : Func} {i : BlockId} {b : Block} {x : ValId}
    (hb : f.blocks[i]? = some b) (hx : x ∈ blockUses b) : x ∈ liveUniverse f := by
  have hmem : b ∈ f.blocks.toList := by
    obtain ⟨hlt, hget⟩ := Array.getElem?_eq_some_iff.mp hb
    exact List.mem_iff_getElem.mpr ⟨i, by simpa using hlt, by simpa using hget⟩
  simp only [liveUniverse, List.mem_flatMap]
  exact ⟨b, hmem, hx⟩

theorem lout_pairwise {li : Array (List ValId)} (edges : List Edge) {acc : List ValId}
    (h : acc.Pairwise (· < ·)) :
    (edges.foldl (fun acc (e : Edge) => unionS (li[e.target]?.getD []) acc) acc).Pairwise
      (· < ·) := by
  induction edges generalizing acc with
  | nil => exact h
  | cons e es ih => exact ih (unionS_pairwise h)

theorem liveStep_pairwise {f : Func} {A : Array (List ValId)} (i : Nat) :
    ((liveStep f A)[i]?.getD []).Pairwise (· < ·) := by
  rcases hb : f.blocks[i]? with _ | b
  · rw [liveStep_get_none hb]; exact List.Pairwise.nil
  · rw [liveStep_get_eq hb]
    exact diffS_pairwise (unionS_pairwise (lout_pairwise _ List.Pairwise.nil))

theorem liveStep_liveUniverse {f : Func} {A : Array (List ValId)}
    (hA : ∀ (i : Nat) (x : ValId), x ∈ A[i]?.getD [] → x ∈ liveUniverse f) :
    ∀ (i : Nat) (x : ValId), x ∈ (liveStep f A)[i]?.getD [] → x ∈ liveUniverse f := by
  intro i x hx
  rcases hb : f.blocks[i]? with _ | b
  · rw [liveStep_get_none hb] at hx; simp at hx
  · rw [liveStep_get_eq hb, mem_diffS] at hx
    rcases mem_unionS.mp hx.1 with hu | hl
    · exact mem_liveUniverse hb hu
    · rcases mem_lout.mp hl with ⟨e, -, hxe⟩ | hnil
      · exact hA _ _ hxe
      · simp at hnil

/-! ### The measure -/

/-- Sum of the live-set sizes over the first `n` blocks. -/
def liveMeasure (n : Nat) (A : Array (List ValId)) : Nat :=
  ((List.range n).map fun i => (A[i]?.getD []).length).sum

theorem sum_le_sum {l : List Nat} {F G : Nat → Nat} (h : ∀ i ∈ l, F i ≤ G i) :
    ((l.map F).sum) ≤ ((l.map G).sum) := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h a (by simp)) (ih fun i hi => h i (by simp [hi]))

theorem sum_lt_sum {l : List Nat} {F G : Nat → Nat} (hle : ∀ i ∈ l, F i ≤ G i)
    {j : Nat} (hj : j ∈ l) (hlt : F j < G j) : ((l.map F).sum) < ((l.map G).sum) := by
  induction l with
  | nil => simp at hj
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hj with rfl | hj'
    · exact Nat.add_lt_add_of_lt_of_le hlt (sum_le_sum fun i hi => hle i (by simp [hi]))
    · exact Nat.add_lt_add_of_le_of_lt (hle a (by simp))
        (ih (fun i hi => hle i (by simp [hi])) hj')

theorem sum_le_const {l : List Nat} {F : Nat → Nat} {c : Nat} (h : ∀ i ∈ l, F i ≤ c) :
    ((l.map F).sum) ≤ l.length * c := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := ih fun i hi => h i (by simp [hi])
    have ha := h a (by simp)
    calc F a + (as.map F).sum ≤ c + as.length * c := Nat.add_le_add ha this
      _ = (as.length + 1) * c := by ring


theorem length_le_liveUniverse {f : Func} {l : List ValId} (hp : l.Pairwise (· < ·))
    (hs : ∀ x ∈ l, x ∈ liveUniverse f) : l.length ≤ (liveUniverse f).length :=
  (List.subperm_of_subset (nodup_of_pairwise_lt hp) hs).length_le

theorem measure_le {f : Func} {n : Nat} {A : Array (List ValId)}
    (hp : ∀ (i : Nat), (A[i]?.getD []).Pairwise (· < ·))
    (hu : ∀ (i : Nat) (x : ValId), x ∈ A[i]?.getD [] → x ∈ liveUniverse f) :
    liveMeasure n A ≤ n * (liveUniverse f).length := by
  have h := sum_le_const (l := List.range n) (F := fun i => (A[i]?.getD []).length)
    (c := (liveUniverse f).length) (fun i _ => length_le_liveUniverse (hp i) (fun x hx => hu i x hx))
  simpa [liveMeasure] using h

theorem measure_lt {n : Nat} {A B : Array (List ValId)}
    (hsub : Sub A B) (hpA : ∀ (i : Nat), (A[i]?.getD []).Pairwise (· < ·))
    (hpB : ∀ (i : Nat), (B[i]?.getD []).Pairwise (· < ·))
    (hsA : A.size = n) (hsB : B.size = n) (hne : A ≠ B) :
    liveMeasure n A < liveMeasure n B := by
  have hle : ∀ (i : Nat), (A[i]?.getD []).length ≤ (B[i]?.getD []).length := fun i =>
    (List.subperm_of_subset (nodup_of_pairwise_lt (hpA i)) (fun x hx => hsub i x hx)).length_le
  have hex : ∃ (i : Nat), A[i]? ≠ B[i]? := by
    by_contra hc
    exact hne (Array.ext_getElem? fun i => by by_contra h; exact hc ⟨i, h⟩)
  obtain ⟨i, hi⟩ := hex
  have hin : i < n := by
    by_contra hge
    have hge' : n ≤ i := Nat.not_lt.mp hge
    have h1 : A[i]? = none := by rw [Array.getElem?_eq_none_iff]; omega
    have h2 : B[i]? = none := by rw [Array.getElem?_eq_none_iff]; omega
    exact hi (h1.trans h2.symm)
  have hAi : A[i]? = some (A[i]?.getD []) := by
    rw [Array.getElem?_eq_getElem (by omega)]; simp
  have hBi : B[i]? = some (B[i]?.getD []) := by
    rw [Array.getElem?_eq_getElem (by omega)]; simp
  have hne' : A[i]?.getD [] ≠ B[i]?.getD [] := by
    intro heq; exact hi (hAi.trans (heq ▸ hBi.symm))
  -- a member of B[i] outside A[i]
  have hmem : ∃ (x : ValId), x ∈ B[i]?.getD [] ∧ x ∉ A[i]?.getD [] := by
    by_contra hc
    refine hne' (pairwise_lt_ext (hpA i) (hpB i) (fun x => ⟨fun hx => hsub i x hx, fun hx => ?_⟩))
    by_contra hxA
    exact hc ⟨x, hx, hxA⟩
  obtain ⟨x, hxB, hxA⟩ := hmem
  have hlt : (A[i]?.getD []).length < (B[i]?.getD []).length := by
    have hsub' : A[i]?.getD [] ⊆ (B[i]?.getD []).erase x := by
      intro y hy
      refine (List.mem_erase_of_ne (fun h => hxA ?_)).mpr (hsub i y hy)
      rw [← h]; exact hy
    have h1 := (List.subperm_of_subset (nodup_of_pairwise_lt (hpA i)) hsub').length_le
    rw [List.length_erase_of_mem hxB] at h1
    have h2 : 0 < (B[i]?.getD []).length := List.length_pos_of_mem hxB
    omega
  exact sum_lt_sum (l := List.range n) (fun j _ => hle j) (List.mem_range.mpr hin) hlt


theorem replicate_getD (n i : Nat) :
    ((Array.replicate n ([] : List ValId))[i]?.getD []) = [] := by
  rcases h : (Array.replicate n ([] : List ValId))[i]? with _ | l
  · simp
  · obtain ⟨hlt, hget⟩ := Array.getElem?_eq_some_iff.mp h
    simp only [Option.getD_some]
    simpa using hget.symm

theorem liveUniverse_length_le (f : Func) :
    (liveUniverse f).length ≤
      f.blocks.foldl (init := 0)
        (fun acc b => acc + (blockDefs b).length + (blockUses b).length) := by
  have key : ∀ (l : List Block) (acc : Nat),
      acc + ((l.map fun b => (blockUses b).length).sum) ≤
        l.foldl (fun acc b => acc + (blockDefs b).length + (blockUses b).length) acc := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons b bs ih =>
      intro acc
      simp only [List.map_cons, List.sum_cons, List.foldl_cons]
      have h := ih (acc + (blockDefs b).length + (blockUses b).length)
      omega
  rw [← Array.foldl_toList]
  simp only [liveUniverse, List.length_flatMap]
  simpa using key f.blocks.toList 0

theorem go_isSome {f : Func} :
    ∀ (fuel : Nat) (cur : Array (List ValId)),
      cur.size = f.blocks.size →
      (∀ (i : Nat), (cur[i]?.getD []).Pairwise (· < ·)) →
      (∀ (i : Nat) (x : ValId), x ∈ cur[i]?.getD [] → x ∈ liveUniverse f) →
      Sub cur (liveStep f cur) →
      f.blocks.size * (liveUniverse f).length < liveMeasure f.blocks.size cur + fuel →
      ∃ li, liveInSets.go f fuel cur = some li := by
  intro fuel
  induction fuel with
  | zero =>
    intro cur hsz hp hu hsub hfuel
    have := measure_le (f := f) (n := f.blocks.size) hp hu
    omega
  | succ k ih =>
    intro cur hsz hp hu hsub hfuel
    rw [liveInSets.go]
    split
    · exact ⟨cur, rfl⟩
    · rename_i hbeq
      have hne : liveStep f cur ≠ cur := fun h => hbeq (by simp [h])
      have hlt : liveMeasure f.blocks.size cur < liveMeasure f.blocks.size (liveStep f cur) :=
        measure_lt hsub hp (fun i => liveStep_pairwise i) hsz liveStep_size (Ne.symm hne)
      exact ih (liveStep f cur) liveStep_size (fun i => liveStep_pairwise i)
        (liveStep_liveUniverse hu) (liveStep_mono hsub) (by omega)

/-- **`liveInSets` always converges.** The fuel `blocks.size * (total + 1) + 2`
always suffices: the iterates increase (Kleene, via `liveStep_mono`), each is
contained in the finite universe of mentioned ids, so the sum of their sizes —
which strictly increases at every non-exiting round — is bounded by
`blocks.size * total`. -/
theorem liveInSets_isSome (f : Func) : ∃ li, liveInSets f = some li := by
  refine go_isSome _ _ (by simp) (fun i => by rw [replicate_getD]; exact List.Pairwise.nil)
    (fun i x hx => by rw [replicate_getD] at hx; simp at hx) sub_replicate ?_
  have h0 : liveMeasure f.blocks.size (Array.replicate f.blocks.size []) = 0 := by
    simp [liveMeasure, replicate_getD]
  have hU := liveUniverse_length_le f
  rw [h0]
  have : f.blocks.size * (liveUniverse f).length
      ≤ f.blocks.size * (f.blocks.foldl (init := 0)
          fun acc b => acc + (blockDefs b).length + (blockUses b).length) :=
    Nat.mul_le_mul_left _ hU
  have hexp : f.blocks.size * ((f.blocks.foldl (init := 0)
      fun acc b => acc + (blockDefs b).length + (blockUses b).length) + 1)
      = f.blocks.size * (f.blocks.foldl (init := 0)
          fun acc b => acc + (blockDefs b).length + (blockUses b).length) + f.blocks.size := by
    ring
  omega


/-! ### A reusable dominance-preservation criterion -/

/-- **Dominance preservation criterion.** A rewrite that keeps the function's
parameters and entry, only ever *shrinks* what a block reads, only ever *keeps*
what a block defines, and only ever drops outgoing edges, preserves
`Func.domCheck`. -/
theorem domCheck_of_shrinking {f g : Func}
    (hdom : Func.domCheck f = true)
    (hparams : g.params = f.params) (hentry : g.entry = f.entry)
    (hrel : ∀ (i : BlockId) (b' : Block), g.blocks[i]? = some b' →
      ∃ b, f.blocks[i]? = some b
        ∧ (∀ x ∈ blockUses b', x ∈ blockUses b)
        ∧ (∀ x ∈ blockDefs b, x ∈ blockDefs b')
        ∧ (∀ e ∈ b'.term.edges, ∃ e0 ∈ b.term.edges, e0.target = e.target)) :
    Func.domCheck g = true := by
  obtain ⟨li, hli⟩ := liveInSets_isSome f
  obtain ⟨li', hli'⟩ := liveInSets_isSome g
  -- the original's live sets are a pre-fixed point for the rewritten function
  have hub : Sub (liveStep g li) li := by
    intro i x hx
    rcases hb' : g.blocks[i]? with _ | b'
    · rw [liveStep_get_none hb'] at hx; simp at hx
    · rw [liveStep_get_eq hb', mem_diffS] at hx
      obtain ⟨b, hb, huses, hdefs, hedges⟩ := hrel i b' hb'
      rw [liveIn_eq hli hb, mem_diffS]
      refine ⟨?_, fun hmem => hx.2 (hdefs x hmem)⟩
      rcases mem_unionS.mp hx.1 with hu | hl
      · exact mem_unionS.mpr (Or.inl (huses x hu))
      · rcases mem_lout.mp hl with ⟨e, he, hxe⟩ | hnil
        · obtain ⟨e0, he0, hteq⟩ := hedges e he
          exact mem_unionS.mpr (Or.inr (mem_lout.mpr (Or.inl ⟨e0, he0, by rw [hteq]; exact hxe⟩)))
        · simp at hnil
  have hsub : Sub li' li := liveInSets_least hli' hub
  -- hence nothing beyond the parameters is live into the rewritten entry
  unfold Func.domCheck
  rw [hli']
  simp only [decide_eq_true_eq]
  rw [List.eq_nil_iff_forall_not_mem]
  intro x hx
  rw [mem_diffS] at hx
  refine hx.2 ?_
  rw [hparams]
  refine domCheck_entry hli hdom ?_
  rw [← hentry]
  exact hsub _ _ hx.1

/-- **Dominance preservation under use substitution.**  In addition to the
image of the old live-in set, `avail i` contains representatives made available
by a dominating CSE table on entry to block `i`.  A replaced definition either
has its representative defined earlier in the same output block, or finds it in
that entry table.  Entry availability is empty, and availability inherited by a
successor either was already available to its predecessor or is defined there.

This is the substitution-aware counterpart of `domCheck_of_shrinking`.  Its
pre-fixed point is `σ '' liveIn(f) ∪ avail`; `liveInSets_least` then does the
fixed-point work. -/
theorem domCheck_of_substitution {f g : Func} (σ : ValId → ValId)
    (avail : BlockId → List ValId)
    (hdom : Func.domCheck f = true)
    (hparams : g.params = f.params) (hentry : g.entry = f.entry)
    (hσparams : ∀ x ∈ f.params, σ x = x)
    (havailEntry : avail g.entry = [])
    (hrel : ∀ (i : BlockId) (b' : Block), g.blocks[i]? = some b' →
      ∃ b, f.blocks[i]? = some b
        ∧ (∀ x ∈ blockUses b', ∃ y ∈ blockUses b, σ y = x)
        ∧ (∀ y ∈ blockDefs b, σ y ∈ blockDefs b' ∨ σ y ∈ avail i)
        ∧ (∀ e ∈ b'.term.edges, ∃ e0 ∈ b.term.edges, e0.target = e.target)
        ∧ (∀ e ∈ b'.term.edges, ∀ x ∈ avail e.target,
            x ∈ blockDefs b' ∨ x ∈ avail i)) :
    Func.domCheck g = true := by
  obtain ⟨li, hli⟩ := liveInSets_isSome f
  obtain ⟨li', hli'⟩ := liveInSets_isSome g
  let ub : Array (List ValId) := Array.ofFn fun i : Fin g.blocks.size =>
    unionS ((li[i.1]?.getD []).map σ) (avail i.1)
  have mem_ub (i : Nat) (x : ValId) :
      x ∈ ub[i]?.getD [] ↔
        i < g.blocks.size ∧ ((∃ y ∈ li[i]?.getD [], σ y = x) ∨ x ∈ avail i) := by
    by_cases hi : i < g.blocks.size
    · have hiub : i < ub.size := by simpa [ub] using hi
      rw [Array.getElem?_eq_getElem hiub]
      simp only [Option.getD_some, ub, Array.getElem_ofFn, mem_unionS, List.mem_map]
      constructor
      · rintro (⟨y, hy, rfl⟩ | hx)
        · exact ⟨hi, Or.inl ⟨y, hy, rfl⟩⟩
        · exact ⟨hi, Or.inr hx⟩
      · rintro ⟨-, ⟨y, hy, rfl⟩ | hx⟩
        · exact Or.inl ⟨y, hy, rfl⟩
        · exact Or.inr hx
    · have hgeub : ub.size ≤ i := by simpa [ub] using Nat.not_lt.mp hi
      rw [Array.getElem?_eq_none_iff.mpr hgeub]
      simp [hi]
  have hub : Sub (liveStep g ub) ub := by
    intro i x hx
    rcases hb' : g.blocks[i]? with _ | b'
    · rw [liveStep_get_none hb'] at hx; simp at hx
    · have hi : i < g.blocks.size := (Array.getElem?_eq_some_iff.mp hb').1
      rw [liveStep_get_eq hb', mem_diffS] at hx
      obtain ⟨b, hb, huses, hdefs, hedges, havail⟩ := hrel i b' hb'
      rw [mem_ub]
      refine ⟨hi, ?_⟩
      rcases mem_unionS.mp hx.1 with hu | hl
      · obtain ⟨y, hy, hσ⟩ := huses x hu
        by_cases hyd : y ∈ blockDefs b
        · rcases hdefs y hyd with hd | ha
          · exact absurd (hσ ▸ hd) hx.2
          · exact Or.inr (hσ ▸ ha)
        · exact Or.inl ⟨y, liveIn_of_uses hli hb hy hyd, hσ⟩
      · rcases mem_lout.mp hl with ⟨e, he, hxe⟩ | hnil
        · rw [mem_ub] at hxe
          rcases hxe.2 with ⟨y, hy, hσ⟩ | ha
          · obtain ⟨e0, he0, htarget⟩ := hedges e he
            by_cases hyd : y ∈ blockDefs b
            · rcases hdefs y hyd with hd | hav
              · exact absurd (hσ ▸ hd) hx.2
              · exact Or.inr (hσ ▸ hav)
            · exact Or.inl ⟨y, liveIn_of_succ hli hb he0
                (by rw [htarget]; exact hy) hyd, hσ⟩
          · rcases havail e he x ha with hd | hav
            · exact absurd hd hx.2
            · exact Or.inr hav
        · simp at hnil
  have hsub : Sub li' ub := liveInSets_least hli' hub
  unfold Func.domCheck
  rw [hli']
  simp only [decide_eq_true_eq]
  rw [List.eq_nil_iff_forall_not_mem]
  intro x hx
  rw [mem_diffS] at hx
  have hxub := hsub _ _ hx.1
  rw [mem_ub] at hxub
  rcases hxub.2 with ⟨y, hy, hσ⟩ | ha
  · have hyp : y ∈ f.params := domCheck_entry hli hdom (by rw [← hentry]; exact hy)
    exact hx.2 (by rw [hparams, ← hσ, hσparams y hyp]; exact hyp)
  · rw [havailEntry] at ha
    simp at ha


end ToAsm

/-! ### Entry-rooted definition provenance

The two substitution passes need the history fact behind their block-local
register invariants: a live value at a reached block did not appear in the
persistent register file by accident; its unique definition has occurred on the
path from the function entry (unless it is a function parameter).  Keeping the
path explicit retains repeated block visits, which is essential for
loop-carried block parameters and CSE values.

The statement below is the common, pass-independent part of that provenance
argument.  It uses only the CFG and the liveness fixed point, so both trivial
parameter elimination and CSE can instantiate it. -/

/-- A finite CFG path rooted at the function entry.  `path` contains the
visited predecessor blocks, in execution order; `i` is the currently reached
block. -/
inductive EntryPath (f : Func) : List BlockId → BlockId → Prop
  | entry : EntryPath f [] f.entry
  | edge {path : List BlockId} {i : BlockId} {b : Block} {e : Edge} :
      EntryPath f path i →
      f.blocks[i]? = some b →
      e ∈ b.term.edges →
      EntryPath f (path ++ [i]) e.target

/-- A value has crossed a defining block on an entry-rooted path. -/
def DefinedOnPath (f : Func) (path : List BlockId) (x : ValId) : Prop :=
  ∃ i ∈ path, ∃ b, f.blocks[i]? = some b ∧ x ∈ ToAsm.blockDefs b

theorem DefinedOnPath.snoc {f : Func} {path : List BlockId} {i : BlockId}
    {b : Block} {x : ValId} (hb : f.blocks[i]? = some b)
    (hx : x ∈ ToAsm.blockDefs b) : DefinedOnPath f (path ++ [i]) x := by
  exact ⟨i, by simp, b, hb, hx⟩

theorem DefinedOnPath.mono_snoc {f : Func} {path : List BlockId}
    {i : BlockId} {x : ValId} (h : DefinedOnPath f path x) :
    DefinedOnPath f (path ++ [i]) x := by
  obtain ⟨j, hj, b, hb, hx⟩ := h
  exact ⟨j, List.mem_append_left _ hj, b, hb, hx⟩

/-- **Entry-rooted provenance invariant.**  Under `domCheck`, every value live
at a block reached from entry is either an entry parameter or its definition
has occurred in one of the predecessor blocks on the concrete path.  The proof
is the forward/path form of the usual backwards-liveness dominance argument:
crossing an edge either crosses the unique definition or propagates liveness to
the predecessor. -/
theorem EntryPath.live_origin {f : Func} {li : Array (List ValId)}
    (hli : ToAsm.liveInSets f = some li)
    (hdom : ToAsm.Func.domCheck f = true)
    {path : List BlockId} {i : BlockId} (hp : EntryPath f path i)
    {x : ValId} (hx : x ∈ li[i]?.getD []) :
    x ∈ f.params ∨ DefinedOnPath f path x := by
  induction hp with
  | entry =>
      exact Or.inl (ToAsm.domCheck_entry hli hdom hx)
  | @edge path i b e hp hb he ih =>
      by_cases hd : x ∈ ToAsm.blockDefs b
      · exact Or.inr (DefinedOnPath.snoc hb hd)
      · rcases ih (ToAsm.liveIn_of_succ hli hb he hx hd) with hparam | hpath
        · exact Or.inl hparam
        · exact Or.inr hpath.mono_snoc

theorem Regs.eq_some_setMany {R : Regs} {xs : List ValId} {vs : List U256}
    {x : ValId} {v : U256} (h : (R.setMany xs vs) x = some v) :
    R x = some v ∨ x ∈ xs := by
  by_cases hx : x ∈ xs
  · exact Or.inr hx
  · left
    rw [Regs.setMany_of_not_mem R xs vs hx] at h
    exact h

theorem Regs.eq_some_of_getMany {R : Regs} {xs : List ValId} {vals : List U256}
    (hget : R.getMany xs = some vals) {x : ValId} (hx : x ∈ xs) :
    ∃ v, R x = some v := by
  induction xs generalizing vals with
  | nil => simp at hx
  | cons y ys ih =>
      rw [Regs.getMany_cons] at hget
      cases hy : R y with
      | none => simp [hy] at hget
      | some w =>
          cases hys : R.getMany ys with
          | none => simp [hy, hys] at hget
          | some ws =>
              rcases List.mem_cons.mp hx with rfl | hx
              · exact ⟨w, hy⟩
              · exact ih hys hx

end YulEvmCompiler.SsaCfg
