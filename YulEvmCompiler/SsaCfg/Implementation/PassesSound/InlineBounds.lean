import YulEvmCompiler.SsaCfg.Implementation.PassesSound.CseCert
set_option warningAsError true

/-!
# YulEvmCompiler.SsaCfg.Implementation.PassesSound.InlineBounds

Pass 0 (program-level inlining): fresh-value bounds and register agreement.

`maxVal`/`inlineOffset` bounds on the renamed callee body, the
`inlineRho` renaming and its injectivity, the partitioned register
agreement (`RenamedAgree`, `CallerFrame`), and the callee-body replay
`inlineReplay_execN`.
-/

namespace YulEvmCompiler.SsaCfg
open YulSemantics.EVM (U256 EvmState Op builtinWithExternal stepOp ExternalCalls
  ExternalCreates)
open YulSemantics (Outcome)

/-! ## Pass 0: program-level inlining

`Passes.inlineProg` runs *before* the per-function pipeline: `inlineFunc`
splices eligible call sites (`inlineOnce`, budgeted fixed point), then
`pruneFuncs` drops functions no longer reachable from `main` and remaps the
surviving ids. It needs **no dominance hypothesis** — it only ever splices a
callee body along the unique edge that reaches it — but it does need `wfCheck`
(`inlineOnce` additionally re-checks the arity conditions
`g.params.length == as.length`, `g.nrets == ds.length`, `g.entry == 0` at the
site, so those come for free from the guard rather than from `wfCheck`).

The splice avoids the stale-read hazard the counterexample exhibits: the
spliced blocks are reachable only through the call
block, `contBlock` is reachable only through the spliced `ret` edges, and the
callee's non-parameter ids are renamed by `+ off` with
`off > max (maxVal f) (maxVal g)`, so they cannot capture a caller id. Duplicate
actual arguments (`g(x, x)`) map two callee parameters onto one caller id, which
is harmless because both were bound to the same word at the call. The inlining
simulation and its whole-program composition below prove these facts.

There is one additional precondition that a provisional statement of one-step
inlining soundness easily misses. The renaming table is `g.params.zip as` followed by
`List.find?`, so it sends a duplicated callee parameter to its *first* actual
argument. `Regs.setMany`, on the other hand, binds left-to-right and therefore
leaves the *last* actual argument in that register. Caller well-formedness alone
is therefore insufficient: a malformed callee with duplicate parameters is a
direct counterexample. The production entry point already has `P.wfCheck =
true`, which supplies `g.allDefs.Nodup`; the one-step and fixed-point statements
below carry that whole-program hypothesis explicitly. -/

/-- Whole-program well-formedness supplies the per-callee fact needed by the
inliner. Unlike caller well-formedness, this rules out duplicate callee
parameters and collisions between parameters and local definitions. -/
theorem progWf_func {P : Prog} (hwf : P.wfCheck = true) {fid : FuncId} {g : Func}
    (hg : P.funcs[fid]? = some g) : g.wfCheck P.funcs.size = true := by
  simp only [Prog.wfCheck, Bool.and_eq_true] at hwf
  have hi : fid < P.funcs.size := (Array.getElem?_eq_some_iff.mp hg).1
  rw [Array.getElem?_eq_getElem hi] at hg
  obtain rfl := Option.some.inj hg
  rw [Array.all_eq_true] at hwf
  exact hwf.2 fid hi

/-- Lookup in `params.zip actuals` returns the unique pair carrying a given
parameter. This is the list-level fact that reconciles `inlineOnce`'s `find?`
renaming with call semantics' positional `setMany`. -/
theorem findParam_zip_of_mem {ps as : List ValId} (hnd : ps.Nodup)
    {p a : ValId} (hm : (p, a) ∈ ps.zip as) :
    (ps.zip as).find? (fun pa => pa.1 == p) = some (p, a) := by
  induction ps generalizing as with
  | nil => simp at hm
  | cons q qs ih =>
      cases as with
      | nil => simp at hm
      | cons b bs =>
          rw [List.nodup_cons] at hnd
          rcases List.mem_cons.mp hm with hhead | htail
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hhead
            simp
          · have hpqs : p ∈ qs := by
              exact (List.of_mem_zip htail).1
            have hqp : q ≠ p := fun heq => hnd.1 (heq ▸ hpqs)
            simpa [hqp] using ih hnd.2 htail

/-- Binding formal parameters to the values read from actual parameters agrees
at corresponding positions. The arbitrary base register file makes the lemma
stable under the caller-register frame used by an inlined body. -/
theorem Regs.setMany_getMany_of_mem_zip {R S : Regs} {ps as : List ValId}
    {vals : List U256} (hnd : ps.Nodup) (hlen : ps.length = as.length)
    (hget : R.getMany as = some vals) {p a : ValId} (hm : (p, a) ∈ ps.zip as) :
    (S.setMany ps vals) p = R a := by
  induction ps generalizing S as vals with
  | nil => simp at hm
  | cons q qs ih =>
      cases as with
      | nil => simp at hlen
      | cons b bs =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          rw [Regs.getMany_cons] at hget
          cases hb : R b with
          | none => simp [hb] at hget
          | some v =>
              cases ht : R.getMany bs with
              | none => simp [hb, ht] at hget
              | some vs =>
                  simp only [hb, ht, Option.bind_some, Option.map_some,
                    Option.some.injEq] at hget
                  subst vals
                  rw [List.nodup_cons] at hnd
                  rcases List.mem_cons.mp hm with hhead | htail
                  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hhead
                    rw [Regs.setMany_cons,
                      Regs.setMany_of_not_mem (S.set p v) qs vs hnd.1,
                      Regs.set_same, hb]
                  · exact ih hnd.2 hlen ht htail (S := S.set q v)

/-- The concrete value-renaming function used by `inlineOnce` sends a callee
parameter to its corresponding caller actual. -/
theorem inlineRho_param {ps as : List ValId} (hnd : ps.Nodup) {p a : ValId}
    (hm : (p, a) ∈ ps.zip as) (off : Nat) :
    (match (ps.zip as).find? (fun pa => pa.1 == p) with
      | some pa => pa.2
      | none => p + off) = a := by
  rw [findParam_zip_of_mem hnd hm]

/-- Entry-register agreement for a renamed inlined callee parameter. This is
the base case of the eventual callee-body renaming simulation. -/
theorem inlineParam_regs_agree {R S : Regs} {ps as : List ValId} {vals : List U256}
    (hnd : ps.Nodup) (hlen : ps.length = as.length)
    (hget : R.getMany as = some vals) {p a : ValId} (hm : (p, a) ∈ ps.zip as)
    (off : Nat) :
    (S.setMany ps vals) p =
      R (match (ps.zip as).find? (fun pa => pa.1 == p) with
        | some pa => pa.2
        | none => p + off) := by
  rw [inlineRho_param hnd hm off]
  exact Regs.setMany_getMany_of_mem_zip hnd hlen hget hm

/-- Generic read transport through a value-id renaming. -/
theorem Regs.getMany_map_of_agree {R R' : Regs} {ρ : ValId → ValId}
    {xs : List ValId} {vals : List U256}
    (hagree : ∀ x ∈ xs, R x = R' (ρ x)) (hget : R.getMany xs = some vals) :
    R'.getMany (xs.map ρ) = some vals := by
  induction xs generalizing vals with
  | nil => simpa using hget
  | cons x xs ih =>
      rw [Regs.getMany_cons] at hget
      cases hx : R x with
      | none => simp [hx] at hget
      | some v =>
          cases ht : R.getMany xs with
          | none => simp [hx, ht] at hget
          | some vs =>
              simp only [hx, ht, Option.bind_some, Option.map_some,
                Option.some.injEq] at hget
              subst vals
              have hx' : R' (ρ x) = some v := by
                rw [← hagree x (by simp), hx]
              have ht' := ih (fun y hy => hagree y (by simp [hy])) ht
              simpa [Regs.getMany_cons, hx'] using ht'

@[simp] theorem Passes.renameInstr_defs (ρ : ValId → ValId) (i : Instr) :
    (renameInstr ρ i).defs = i.defs.map ρ := by
  cases i <;> simp [renameInstr, Instr.defs]

@[simp] theorem Passes.renameInstr_uses (ρ : ValId → ValId) (i : Instr) :
    (renameInstr ρ i).uses = i.uses.map ρ := by
  cases i <;> simp [renameInstr, Instr.uses]

@[simp] theorem Passes.renameEdge_args (ρ : ValId → ValId)
    (β : BlockId → BlockId) (e : Edge) :
    (renameEdge ρ β e).args = e.args.map ρ := rfl

@[simp] theorem Passes.renameEdge_target (ρ : ValId → ValId)
    (β : BlockId → BlockId) (e : Edge) :
    (renameEdge ρ β e).target = β e.target := rfl

@[simp] theorem Passes.renameTerm_uses (ρ : ValId → ValId)
    (β : BlockId → BlockId) (t : Term) :
    (renameTerm ρ β t).uses = t.uses.map ρ := by
  cases t <;> simp [renameTerm, Term.uses, renameEdge, List.map_append]

/-! ### Fresh-value bounds used by inlining -/

/-- Folding `Nat.max` over a list never decreases its accumulator. -/
theorem foldl_max_start_le (xs : List Nat) (n : Nat) :
    n ≤ xs.foldl Nat.max n := by
  induction xs generalizing n with
  | nil => exact Nat.le_refl n
  | cons x xs ih =>
      exact le_trans (Nat.le_max_left n x) (ih (Nat.max n x))

/-- Every member is bounded by a `Nat.max` fold, independently of the initial
accumulator. -/
theorem foldl_max_mem_le {xs : List Nat} {x n : Nat} (hx : x ∈ xs) :
    x ≤ xs.foldl Nat.max n := by
  induction xs generalizing n with
  | nil => simp at hx
  | cons y ys ih =>
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hx with rfl | hx
      · exact le_trans (Nat.le_max_right n x) (foldl_max_start_le ys (Nat.max n x))
      · exact ih hx

/-- One block's contribution to `maxVal`, with an explicit initial bound. -/
def Passes.maxBlockVal (acc : ValId) (b : Block) : ValId :=
  let m := fun a (vs : List ValId) => vs.foldl Nat.max a
  m (m (b.instrs.foldl (fun a i => m (m a i.defs) i.uses) acc) b.params)
    b.term.uses

theorem Passes.instrFold_start_le (is : List Instr) (n : ValId) :
    n ≤ is.foldl
      (fun a i => i.uses.foldl Nat.max (i.defs.foldl Nat.max a)) n := by
  induction is generalizing n with
  | nil => exact Nat.le_refl n
  | cons i is ih =>
      rw [List.foldl_cons]
      exact le_trans
        (le_trans (foldl_max_start_le i.defs n)
          (foldl_max_start_le i.uses (i.defs.foldl Nat.max n)))
        (ih _)

theorem Passes.maxBlockVal_start_le (b : Block) (n : ValId) :
    n ≤ maxBlockVal n b := by
  exact le_trans (instrFold_start_le b.instrs n)
    (le_trans (foldl_max_start_le b.params _) (foldl_max_start_le b.term.uses _))

theorem Passes.maxBlockVal_param_le {b : Block} {x : ValId} (hx : x ∈ b.params)
    (n : ValId) : x ≤ maxBlockVal n b := by
  exact le_trans (foldl_max_mem_le (n := b.instrs.foldl
    (fun a i => i.uses.foldl Nat.max (i.defs.foldl Nat.max a)) n) hx)
    (foldl_max_start_le b.term.uses _)

theorem Passes.maxBlockVal_termUse_le {b : Block} {x : ValId} (hx : x ∈ b.term.uses)
    (n : ValId) : x ≤ maxBlockVal n b :=
  foldl_max_mem_le hx

theorem Passes.instrFold_def_le {is : List Instr} {i : Instr} (hi : i ∈ is)
    {x : ValId} (hx : x ∈ i.defs) (n : ValId) :
    x ≤ is.foldl
      (fun a j => j.uses.foldl Nat.max (j.defs.foldl Nat.max a)) n := by
  induction is generalizing n with
  | nil => simp at hi
  | cons j js ih =>
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hi with rfl | hi
      · exact le_trans
          (le_trans (foldl_max_mem_le (n := n) hx)
            (foldl_max_start_le i.uses _))
          (instrFold_start_le js _)
      · exact ih hi _

theorem Passes.instrFold_use_le {is : List Instr} {i : Instr} (hi : i ∈ is)
    {x : ValId} (hx : x ∈ i.uses) (n : ValId) :
    x ≤ is.foldl
      (fun a j => j.uses.foldl Nat.max (j.defs.foldl Nat.max a)) n := by
  induction is generalizing n with
  | nil => simp at hi
  | cons j js ih =>
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hi with rfl | hi
      · exact le_trans (foldl_max_mem_le (n := i.defs.foldl Nat.max n) hx)
          (instrFold_start_le js _)
      · exact ih hi _

theorem Passes.maxBlockVal_instrDef_le {b : Block} {i : Instr} (hi : i ∈ b.instrs)
    {x : ValId} (hx : x ∈ i.defs) (n : ValId) : x ≤ maxBlockVal n b := by
  exact le_trans (instrFold_def_le hi hx n)
    (le_trans (foldl_max_start_le b.params _) (foldl_max_start_le b.term.uses _))

theorem Passes.maxBlockVal_instrUse_le {b : Block} {i : Instr} (hi : i ∈ b.instrs)
    {x : ValId} (hx : x ∈ i.uses) (n : ValId) : x ≤ maxBlockVal n b := by
  exact le_trans (instrFold_use_le hi hx n)
    (le_trans (foldl_max_start_le b.params _) (foldl_max_start_le b.term.uses _))

theorem Passes.blocksFold_start_le (bs : List Block) (n : ValId) :
    n ≤ bs.foldl maxBlockVal n := by
  induction bs generalizing n with
  | nil => exact Nat.le_refl n
  | cons b bs ih =>
      rw [List.foldl_cons]
      exact le_trans (maxBlockVal_start_le b n) (ih _)

theorem Passes.blocksFold_block_le {bs : List Block} {b : Block} (hb : b ∈ bs)
    {x : ValId} (hx : ∀ n, x ≤ maxBlockVal n b) (n : ValId) :
    x ≤ bs.foldl maxBlockVal n := by
  induction bs generalizing n with
  | nil => simp at hb
  | cons c cs ih =>
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hb with rfl | hb
      · exact le_trans (hx n) (blocksFold_start_le cs _)
      · exact ih hb _

theorem Passes.maxVal_eq (f : Func) :
    maxVal f = f.blocks.toList.foldl maxBlockVal
      ([].foldl Nat.max (f.params.foldl Nat.max 0)) := by
  unfold maxVal maxBlockVal
  rw [Array.foldl_toList]

/-- Every function parameter is at most the function's `maxVal`. -/
theorem Passes.param_le_maxVal {f : Func} {x : ValId} (hx : x ∈ f.params) :
    x ≤ maxVal f := by
  rw [maxVal_eq]
  exact le_trans (foldl_max_mem_le (n := 0) hx)
    (blocksFold_start_le f.blocks.toList _)

/-- Every block parameter is at most the enclosing function's `maxVal`. -/
theorem Passes.blockParam_le_maxVal {f : Func} {b : Block}
    (hb : b ∈ f.blocks.toList) {x : ValId} (hx : x ∈ b.params) : x ≤ maxVal f := by
  rw [maxVal_eq]
  exact blocksFold_block_le hb (fun n => maxBlockVal_param_le hx n) _

/-- Every instruction destination is at most the enclosing function's
`maxVal`. -/
theorem Passes.instrDef_le_maxVal {f : Func} {b : Block}
    (hb : b ∈ f.blocks.toList) {i : Instr} (hi : i ∈ b.instrs)
    {x : ValId} (hx : x ∈ i.defs) : x ≤ maxVal f := by
  rw [maxVal_eq]
  exact blocksFold_block_le hb (fun n => maxBlockVal_instrDef_le hi hx n) _

/-- Every instruction operand is at most the enclosing function's `maxVal`. -/
theorem Passes.instrUse_le_maxVal {f : Func} {b : Block}
    (hb : b ∈ f.blocks.toList) {i : Instr} (hi : i ∈ b.instrs)
    {x : ValId} (hx : x ∈ i.uses) : x ≤ maxVal f := by
  rw [maxVal_eq]
  exact blocksFold_block_le hb (fun n => maxBlockVal_instrUse_le hi hx n) _

/-- Every terminator operand is at most the enclosing function's `maxVal`. -/
theorem Passes.termUse_le_maxVal {f : Func} {b : Block}
    (hb : b ∈ f.blocks.toList) {x : ValId} (hx : x ∈ b.term.uses) : x ≤ maxVal f := by
  rw [maxVal_eq]
  exact blocksFold_block_le hb (fun n => maxBlockVal_termUse_le hx n) _

/-- The splice offset is strictly above every value id mentioned by either the
caller or the callee. -/
theorem Passes.maxVal_lt_inlineOffset_left (f g : Func) :
    maxVal f < Nat.max (maxVal f) (maxVal g) + 1 :=
  Nat.lt_succ_of_le (Nat.le_max_left _ _)

theorem Passes.maxVal_lt_inlineOffset_right (f g : Func) :
    maxVal g < Nat.max (maxVal f) (maxVal g) + 1 :=
  Nat.lt_succ_of_le (Nat.le_max_right _ _)

/-! ### Partitioned register agreement -/

/-- The value renaming used by an inline splice, named so its two partitions
can be stated without repeating the `find?` expression. -/
def Passes.inlineRho (ps as : List ValId) (off : Nat) (v : ValId) : ValId :=
  match (ps.zip as).find? (fun pa => pa.1 == v) with
  | some pa => pa.2
  | none => v + off

theorem Passes.inlineRho_of_not_param {ps as : List ValId} {off v : Nat}
    (hv : v ∉ ps) : inlineRho ps as off v = v + off := by
  unfold inlineRho
  have hnone : (ps.zip as).find? (fun pa => pa.1 == v) = none := by
    apply List.find?_eq_none.mpr
    intro pa hpa
    have hp : pa.1 ∈ ps := (List.of_mem_zip hpa).1
    simpa [beq_iff_eq, hv] using (show pa.1 ≠ v from fun h => hv (h ▸ hp))
  rw [hnone]

theorem mem_zip_left_of_length_eq {ps as : List Nat} (hlen : ps.length = as.length)
    {p : Nat} (hp : p ∈ ps) : ∃ a, (p, a) ∈ ps.zip as := by
  induction ps generalizing as with
  | nil => simp at hp
  | cons q qs ih =>
      cases as with
      | nil => simp at hlen
      | cons a as =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          rcases List.mem_cons.mp hp with rfl | hp
          · exact ⟨a, by simp⟩
          · obtain ⟨b, hb⟩ := ih hlen hp
            exact ⟨b, by simp [hb]⟩

theorem Passes.inlineRho_lt_of_param_nodup {ps as : List ValId} {off p : Nat}
    (hnd : ps.Nodup) (hlen : ps.length = as.length)
    (has : ∀ a ∈ as, a < off) (hp : p ∈ ps) : inlineRho ps as off p < off := by
  obtain ⟨a, hpa⟩ := mem_zip_left_of_length_eq hlen hp
  rw [show inlineRho ps as off p = a by
    exact inlineRho_param hnd hpa off]
  exact has a (List.of_mem_zip hpa).2

theorem Passes.inlineRho_ge_of_not_param {ps as : List ValId} {off v : Nat}
    (hv : v ∉ ps) : off ≤ inlineRho ps as off v := by
  rw [inlineRho_of_not_param hv]
  omega

/-- The shifted partition is injective against every callee id when the
destination is not a formal parameter. -/
theorem Passes.inlineRho_eq_of_not_param {ps as : List ValId} {off x d : Nat}
    (hnd : ps.Nodup) (hlen : ps.length = as.length)
    (has : ∀ a ∈ as, a < off) (hd : d ∉ ps)
    (heq : inlineRho ps as off x = inlineRho ps as off d) : x = d := by
  by_cases hx : x ∈ ps
  · have hxl := inlineRho_lt_of_param_nodup hnd hlen has hx
    have hdr := inlineRho_ge_of_not_param (as := as) (off := off) hd
    rw [heq] at hxl
    exact (Nat.not_le_of_lt hxl hdr).elim
  · rw [inlineRho_of_not_param hx, inlineRho_of_not_param hd] at heq
    exact Nat.add_right_cancel heq

/-- One-way agreement is sufficient for replay: every successful callee read
has the same value in the renamed high partition. -/
def Passes.RenamedAgree (ps as : List ValId) (off : Nat)
    (Rc Ri : Regs) : Prop :=
  ∀ x v, Rc x = some v → Ri (inlineRho ps as off x) = some v

/-- The low partition is the caller frame and must remain unchanged while the
spliced callee executes. -/
def Passes.CallerFrame (off : Nat) (Rcaller Ri : Regs) : Prop :=
  ∀ x, x < off → Ri x = Rcaller x

/-- Corresponding parallel bindings preserve one-way renamed agreement when
no destination image aliases another source id's image. -/
theorem Regs.setMany_rename_some {R R' : Regs} {ρ : ValId → ValId}
    (hagree : ∀ x v, R x = some v → R' (ρ x) = some v)
    (xs : List ValId) (vals : List U256)
    (hsep : ∀ x d, d ∈ xs → ρ x = ρ d → x = d) :
    ∀ x v, (R.setMany xs vals) x = some v →
      (R'.setMany (xs.map ρ) vals) (ρ x) = some v := by
  induction xs generalizing R R' vals with
  | nil =>
      simpa [Regs.setMany_nil_left] using hagree
  | cons d ds ih =>
      cases vals with
      | nil => simpa [Regs.setMany_nil_right] using hagree
      | cons w ws =>
          rw [Regs.setMany_cons, List.map_cons, Regs.setMany_cons]
          apply ih (vals := ws)
          · intro x v hx
            by_cases hxd : x = d
            · subst x
              simpa using hx
            · have hrho : ρ x ≠ ρ d := fun h => hxd (hsep x d (by simp) h)
              rw [Regs.set_other _ _ hxd] at hx
              rw [Regs.set_other _ _ hrho]
              exact hagree x v hx
          · intro x q hq heq
            exact hsep x q (by simp [hq]) heq

/-- High-partition writes preserve every caller register below the offset. -/
theorem Regs.setMany_below {R : Regs} {ρ : ValId → ValId} {off : Nat}
    (xs : List ValId) (vals : List U256)
    (hhigh : ∀ d ∈ xs, off ≤ ρ d) :
    ∀ x, x < off → (R.setMany (xs.map ρ) vals) x = R x := by
  intro x hx
  apply Regs.setMany_of_not_mem
  intro hm
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hm
  exact (Nat.not_le_of_lt hx) (hhigh d hd)

/-- Function parameters and block parameters are disjoint under the inliner's
single-assignment hypothesis. -/
theorem funcParam_not_blockParam {f : Func} (hnd : f.allDefs.Nodup)
    {b : Block} (hb : b ∈ f.blocks.toList) {d : ValId}
    (hf : d ∈ f.params) (hbparam : d ∈ b.params) : False := by
  have hall := List.nodup_iff_count_le_one.mp hnd d
  rw [allDefs_eq, List.count_append] at hall
  have h1 : 1 ≤ f.params.count d := List.count_pos_iff.mpr hf
  have h2 : 1 ≤ (f.blocks.toList.flatMap blockAllDefs).count d :=
    one_le_count_flatMap hb (List.mem_append_left _ hbparam)
  omega

theorem params_nodup_of_allDefs {f : Func} {ps : List ValId}
    (hnd : f.allDefs.Nodup) (hps : ps = f.params) : ps.Nodup := by
  subst ps
  rw [allDefs_eq] at hnd
  exact (List.nodup_append.mp hnd).1

theorem Passes.renamedAgree_entry {R : Regs} {ps as : List ValId}
    {vals : List U256} {off : Nat} (hnd : ps.Nodup)
    (hlen : ps.length = as.length) (hget : R.getMany as = some vals) :
    RenamedAgree ps as off (Regs.empty.setMany ps vals) R := by
  intro x v hx
  rcases Regs.eq_some_setMany hx with hempty | hp
  · simp [Regs.empty] at hempty
  · obtain ⟨a, hpa⟩ := mem_zip_left_of_length_eq hlen hp
    have heq := inlineParam_regs_agree (S := Regs.empty) hnd hlen hget hpa off
    exact heq.symm.trans hx

theorem Passes.renamedAgree_getMany {Rc Ri : Regs} {ps as : List ValId}
    {off : Nat} (hagree : RenamedAgree ps as off Rc Ri)
    {xs : List ValId} {vals : List U256} (hget : Rc.getMany xs = some vals) :
    Ri.getMany (xs.map (inlineRho ps as off)) = some vals := by
  apply Regs.getMany_map_of_agree (hget := hget)
  intro x hx
  obtain ⟨v, hv⟩ := Regs.eq_some_of_getMany hget hx
  rw [hv, hagree x v hv]

theorem Passes.renamedAgree_setMany {Rc Ri : Regs} {ps as : List ValId}
    {off : Nat} (hnd : ps.Nodup) (hlen : ps.length = as.length)
    (has : ∀ a ∈ as, a < off) {ds : List ValId}
    (hds : ∀ d ∈ ds, d ∉ ps) (vals : List U256)
    (hagree : RenamedAgree ps as off Rc Ri) :
    RenamedAgree ps as off (Rc.setMany ds vals)
      (Ri.setMany (ds.map (inlineRho ps as off)) vals) := by
  exact Regs.setMany_rename_some hagree ds vals fun x d hd heq =>
    inlineRho_eq_of_not_param hnd hlen has (hds d hd) heq

theorem Passes.callerFrame_setMany {Rcaller Ri : Regs} {ps as : List ValId}
    {off : Nat} {ds : List ValId} (hds : ∀ d ∈ ds, d ∉ ps)
    (hframe : CallerFrame off Rcaller Ri) (vals : List U256) :
    CallerFrame off Rcaller
      (Ri.setMany (ds.map (inlineRho ps as off)) vals) := by
  intro x hx
  rw [Regs.setMany_below ds vals (fun d hd => inlineRho_ge_of_not_param
    (as := as) (off := off) (hds d hd)) x hx]
  exact hframe x hx

def Passes.inlineReplayTerm (ρ : ValId → ValId) (β : BlockId → BlockId)
    (contId : BlockId) : Term → Term
  | .ret vs => .jump ⟨contId, vs.map ρ⟩
  | t => renameTerm ρ β t

def Passes.inlineReplayBlock (ρ : ValId → ValId) (β : BlockId → BlockId)
    (contId : BlockId) (b : Block) : Block :=
  { params := b.params.map ρ
    instrs := b.instrs.map (renameInstr ρ)
    term := inlineReplayTerm ρ β contId b.term }

/-- The current rest really is a suffix of one block of the callee. -/
def Rest.IsSuffixOf (r : Rest) (b : Block) : Prop :=
  ∃ pre, b.instrs = pre ++ r.instrs ∧ b.term = r.term

theorem Rest.IsSuffixOf.tail {r : Rest} {b : Block} {i : Instr}
    (h : (Rest.mk (i :: r.instrs) r.term).IsSuffixOf b) : r.IsSuffixOf b := by
  obtain ⟨pre, his, ht⟩ := h
  refine ⟨pre ++ [i], ?_, ht⟩
  simpa [List.append_assoc] using his

theorem Rest.IsSuffixOf.head_mem {r : Rest} {b : Block} {i : Instr}
    (h : (Rest.mk (i :: r.instrs) r.term).IsSuffixOf b) : i ∈ b.instrs := by
  obtain ⟨pre, his, -⟩ := h
  rw [his]
  simp

theorem Regs.getMany_length {R : Regs} {xs : List ValId} {vs : List U256}
    (h : R.getMany xs = some vs) : xs.length = vs.length := by
  induction xs generalizing vs with
  | nil =>
      have : vs = [] := by simpa using h.symm
      subst vs
      rfl
  | cons x xs ih =>
      rw [Regs.getMany_cons] at h
      cases hx : R x with
      | none => simp [hx] at h
      | some v =>
          cases hxs : R.getMany xs with
          | none => simp [hx, hxs] at h
          | some ws =>
              have hvs : vs = v :: ws := by simpa [hx, hxs] using h.symm
              subst vs
              simp [ih hxs]

theorem Passes.inlineReplayBlock_get {f' g : Func} {preBlocks : Array Block}
    {ρ : ValId → ValId} {β : BlockId → BlockId} {contId i : BlockId}
    {gb : Block} {cont : Block}
    (hblocks : f'.blocks = preBlocks ++ g.blocks.map (inlineReplayBlock ρ β contId) ++ #[cont])
    (hg : g.blocks[i]? = some gb) :
    f'.blocks[preBlocks.size + i]? = some (inlineReplayBlock ρ β contId gb) := by
  rw [hblocks, Array.getElem?_append_left (by
    have hi := (Array.getElem?_eq_some_iff.mp hg).1
    simp
    omega)]
  rw [Array.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  simpa using congrArg (Option.map (inlineReplayBlock ρ β contId)) hg

theorem Passes.inlineContBlock_get {f' g : Func} {preBlocks : Array Block}
    {ρ : ValId → ValId} {β : BlockId → BlockId} {contId : BlockId}
    {cont : Block}
    (hblocks : f'.blocks = preBlocks ++ g.blocks.map (inlineReplayBlock ρ β contId) ++ #[cont]) :
    f'.blocks[preBlocks.size + g.blocks.size]? = some cont := by
  rw [hblocks, Array.getElem?_append_right (by simp)]
  simp only [Array.size_append, Array.size_map]
  simp

theorem block_mem_of_getElem? {f : Func} {i : BlockId} {b : Block}
    (h : f.blocks[i]? = some b) : b ∈ f.blocks.toList :=
  List.mem_of_getElem? (Array.getElem?_toList.trans h)

/-- The indexed replay raises the callee bound once to accommodate the CPS continuation. -/
theorem Passes.inlineReplay_execN [model : ExternalModel]
    {P : Prog} {n : Nat} {g f' : Func} {preBlocks : Array Block} {cont : Block}
    {ps as ds : List ValId} {off contId : Nat}
    {ρ : ValId → ValId} {β : BlockId → BlockId}
    {Rc Ri Rcaller : Regs} {st : EvmState} {rest : Rest} {cres final : FRes}
    (hρ : ρ = inlineRho ps as off)
    (hβ : ∀ i, β i = preBlocks.size + i)
    (hcontId : contId = preBlocks.size + g.blocks.size)
    (hblocks : f'.blocks = preBlocks ++ g.blocks.map (inlineReplayBlock ρ β contId) ++ #[cont])
    (hcontParams : cont.params = ds)
    (hnd : g.allDefs.Nodup) (hps : ps = g.params)
    (hlen : ps.length = as.length) (has : ∀ a ∈ as, a < off)
    (hret : ∀ {b : Block}, b ∈ g.blocks.toList → ∀ {xs}, b.term = .ret xs →
      xs.length = ds.length)
    (hexec : ExecN (model := model) P n g Rc st rest cres)
    {b : Block} (hb : b ∈ g.blocks.toList) (horigin : rest.IsSuffixOf b)
    (hagree : RenamedAgree ps as off Rc Ri)
    (hframe : CallerFrame off Rcaller Ri)
    (hfinal : ∀ st', cres = .halt st' → final = .halt st')
    (hk : ∀ (Rout : Regs) (vals : List U256) (st' : EvmState),
      cres = .ret vals st' → CallerFrame off Rcaller Rout →
      ExecN (model := model) P (n + 1) f' (Rout.setMany ds vals) st'
        ⟨cont.instrs, cont.term⟩ final) :
    ExecN (model := model) P (n + 1) f' Ri st
      ⟨rest.instrs.map (renameInstr ρ), inlineReplayTerm ρ β contId rest.term⟩ final := by
  subst ρ
  induction hexec generalizing Ri b with
  | @const n fcur R st d v is t res htail ih =>
      have hi : Instr.const d v ∈ b.instrs :=
        Rest.IsSuffixOf.head_mem (r := ⟨is, t⟩) horigin
      have hd : d ∉ ps := by
        rw [hps]
        exact fun hp => funcParam_not_instr_def hnd hb hi hp (by simp [Instr.defs])
      refine ExecN.const (ih hcontId hnd hps hret hb
        (Rest.IsSuffixOf.tail (r := ⟨is, t⟩) horigin)
        (renamedAgree_setMany (params_nodup_of_allDefs hnd hps) hlen has
          (ds := [d]) (by simpa using hd) [v] hagree)
        (callerFrame_setMany (as := as) (ds := [d]) (by simpa using hd) hframe [v])
        hfinal hk hblocks)
  | @op n fcur R st st' ods yop oas oargs rets is t res hget hop hlenRet htail ih =>
      have hi : Instr.op ods yop oas ∈ b.instrs :=
        Rest.IsSuffixOf.head_mem (r := ⟨is, t⟩) horigin
      have hds : ∀ d ∈ ods, d ∉ ps := by
        intro d hd hp
        rw [hps] at hp
        exact funcParam_not_instr_def hnd hb hi hp (by simpa [Instr.defs] using hd)
      refine ExecN.op (args := oargs) (rets := rets)
        (renamedAgree_getMany hagree hget) hop (by simpa using hlenRet)
        (ih hcontId hnd hps hret hb
          (Rest.IsSuffixOf.tail (r := ⟨is, t⟩) horigin)
          (renamedAgree_setMany (params_nodup_of_allDefs hnd hps) hlen has
            hds rets hagree)
          (callerFrame_setMany (as := as) hds hframe rets) hfinal hk hblocks)
  | @opHalt n fcur R st st' ods yop oas oargs is t hget hop =>
      have hf := hfinal st' rfl
      subst final
      simpa [renameInstr, inlineReplayTerm, renameTerm] using
        (ExecN.opHalt (f := f') (ds := ods.map (inlineRho ps as off))
          (args := oargs) (renamedAgree_getMany hagree hget) hop)
  | @call n _ callee R st st' ods oas fid oargs rvals eb is t res
      hfid hget hplen heb hbody hlenRet htail ihbody ih =>
      have hi : Instr.call ods fid oas ∈ b.instrs :=
        Rest.IsSuffixOf.head_mem (r := ⟨is, t⟩) horigin
      have hds : ∀ d ∈ ods, d ∉ ps := by
        intro d hd hp
        rw [hps] at hp
        exact funcParam_not_instr_def hnd hb hi hp (by simpa [Instr.defs] using hd)
      refine ExecN.call (args := oargs) (rvals := rvals) (g := callee) (eb := eb)
        hfid (renamedAgree_getMany hagree hget) hplen heb (hbody.mono (by omega))
        (by simpa using hlenRet)
        (ih hcontId hnd hps hret hb
          (Rest.IsSuffixOf.tail (r := ⟨is, t⟩) horigin)
          (renamedAgree_setMany (params_nodup_of_allDefs hnd hps) hlen has
            hds rvals hagree)
          (callerFrame_setMany (as := as) hds hframe rvals) hfinal hk hblocks)
  | @callHalt n _ callee R st st' ods oas fid oargs eb is t
      hfid hget hplen heb hbody ihbody =>
      have hf := hfinal st' rfl
      subst final
      simpa [renameInstr, inlineReplayTerm, renameTerm] using
        (ExecN.callHalt (f := f') (ds := ods.map (inlineRho ps as off))
          (args := oargs) (g := callee) (eb := eb) hfid
          (renamedAgree_getMany hagree hget) hplen heb (hbody.mono (by omega)))
  | @jump n _ R st e tb vals res htb hget hplen htail ih =>
      have htbmem := block_mem_of_getElem? htb
      have hparams : ∀ d ∈ tb.params, d ∉ ps := by
        intro d hd hp
        rw [hps] at hp
        exact funcParam_not_blockParam hnd htbmem hp hd
      refine ExecN.jump (args := vals) (tb := inlineReplayBlock
          (inlineRho ps as off) β contId tb) ?_
        (renamedAgree_getMany hagree hget) (by simpa [inlineReplayBlock] using hplen)
        (ih hcontId hnd hps hret htbmem ⟨[], rfl, rfl⟩
          (renamedAgree_setMany (params_nodup_of_allDefs hnd hps) hlen has
            hparams vals hagree)
          (callerFrame_setMany (as := as) hparams hframe vals) hfinal hk hblocks)
      change f'.blocks[β e.target]? = some _
      rw [hβ e.target]
      exact inlineReplayBlock_get hblocks htb
  | @branchTrue n _ R st c v et ef tb vals res hc hv htb hget hplen htail ih =>
      have htbmem := block_mem_of_getElem? htb
      have hparams : ∀ d ∈ tb.params, d ∉ ps := by
        intro d hd hp
        rw [hps] at hp
        exact funcParam_not_blockParam hnd htbmem hp hd
      refine ExecN.branchTrue (v := v) (args := vals)
        (tb := inlineReplayBlock (inlineRho ps as off) β contId tb)
        (hagree c v hc) hv ?_ (renamedAgree_getMany hagree hget)
        (by simpa [inlineReplayBlock] using hplen)
        (ih hcontId hnd hps hret htbmem ⟨[], rfl, rfl⟩
          (renamedAgree_setMany (params_nodup_of_allDefs hnd hps) hlen has
            hparams vals hagree)
          (callerFrame_setMany (as := as) hparams hframe vals) hfinal hk hblocks)
      change f'.blocks[β et.target]? = some _
      rw [hβ et.target]
      exact inlineReplayBlock_get hblocks htb
  | @branchFalse n _ R st c et ef tb vals res hc htb hget hplen htail ih =>
      have htbmem := block_mem_of_getElem? htb
      have hparams : ∀ d ∈ tb.params, d ∉ ps := by
        intro d hd hp
        rw [hps] at hp
        exact funcParam_not_blockParam hnd htbmem hp hd
      refine ExecN.branchFalse (args := vals)
        (tb := inlineReplayBlock (inlineRho ps as off) β contId tb)
        (hagree c 0 hc) ?_
        (renamedAgree_getMany hagree hget)
        (by simpa [inlineReplayBlock] using hplen)
        (ih hcontId hnd hps hret htbmem ⟨[], rfl, rfl⟩
          (renamedAgree_setMany (params_nodup_of_allDefs hnd hps) hlen has
            hparams vals hagree)
          (callerFrame_setMany (as := as) hparams hframe vals) hfinal hk hblocks)
      change f'.blocks[β ef.target]? = some _
      rw [hβ ef.target]
      exact inlineReplayBlock_get hblocks htb
  | @ret n _ R st xs vals hget =>
      have ht : b.term = .ret xs := horigin.choose_spec.2
      have hlenVals : ds.length = vals.length := by
        rw [← Regs.getMany_length hget, hret hb ht]
      have hk' := hk Ri vals st rfl hframe
      rw [← hcontParams] at hk'
      refine ExecN.jump (args := vals) (tb := cont) ?_
        (renamedAgree_getMany hagree hget) (by simpa [hcontParams] using hlenVals)
        hk'
      rw [hcontId]
      exact inlineContBlock_get hblocks
  | @halt n _ R st st' yop oas oargs hget hop =>
      have hf := hfinal st' rfl
      subst final
      simpa [inlineReplayTerm, renameTerm] using
        (ExecN.halt (f := f') (args := oargs) (renamedAgree_getMany hagree hget) hop)

end YulEvmCompiler.SsaCfg
