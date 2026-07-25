import YulIR.FrameStructuralSound
import YulIR.FrameSimplifySound

set_option warningAsError true
/-!
# YulIR.FrameDceSound — soundness of the `deadCode` pass (store-agreement simulation)

Unlike `structural`/`simplify`, `deadCode` **changes the local store** — it drops writes to slots
that are read nowhere in the body (and are not protected return slots). So it cannot preserve
`EquivBlock` (which compares the full final store). Its soundness is *observational*: at the `Run`
level the local store is discarded (existential `σ'`), and the only surviving observations are the
`EvmState`, the outcome, and a function's return slots (which `prot` protects). We prove it via a
store-agreement simulation: two stores agreeing on the *live* slots (`reads ++ prot`) stay agreeing,
and produce the same `EvmState`/outcome.

This file builds the **forward** direction (every source behaviour is preserved),
`deadCode_run_fwd : Run p → Run (deadCode-of-main p)`, which needs no well-formedness hypothesis
(the removed statements already ran in the source, so they are simply dropped, never reconstructed).
The reverse direction (which must *reinsert* removed statements, hence needs a `WellFormed`
hypothesis ruling out stuck ill-typed terms) is layered on top.
-/

namespace YulIR.FinFrame.Sem

open YulSemantics (Outcome BuiltinResult Literal)
open YulSemantics.EVM (evm litValue)

/-! ### Store agreement on a set of slots -/

/-- Two stores agree on the slot set `S`. -/
def AgreeOn (S : List (Fin n)) (σ₁ σ₂ : Store n) : Prop := ∀ i, i ∈ S → σ₁ i = σ₂ i

theorem AgreeOn.symm {S : List (Fin n)} {σ₁ σ₂} (h : AgreeOn S σ₁ σ₂) : AgreeOn S σ₂ σ₁ :=
  fun i hi => (h i hi).symm

theorem AgreeOn.trans {S : List (Fin n)} {σ₁ σ₂ σ₃} (h₁ : AgreeOn S σ₁ σ₂) (h₂ : AgreeOn S σ₂ σ₃) :
    AgreeOn S σ₁ σ₃ := fun i hi => (h₁ i hi).trans (h₂ i hi)

/-- `dceBlock` commutes with constant-`switch` case selection (labels are preserved, bodies dce'd). -/
theorem dce_selectCase (reads prot : List (Fin n)) (cv : U256) :
    ∀ (cs : List (Literal × Block n)) (df : Option (Block n)),
      selectCase cv (dceCases reads prot cs) (dceDflt reads prot df)
        = dceBlock reads prot (selectCase cv cs df)
  | [], none => rfl
  | [], some b => rfl
  | (l, b) :: rest, df => by
      simp only [dceCases, selectCase, List.find?_cons]
      by_cases hlab : (litValue l == cv) = true
      · simp [hlab]
      · simp only [hlab]
        exact dce_selectCase reads prot cv rest df

/-- The reads of the block a `switch` selects are covered by the switch's case/default reads. -/
theorem blockReads_selectCase_subset (cv : U256) :
    ∀ (cs : List (Literal × Block n)) (df : Option (Block n)),
      blockReads (selectCase cv cs df) ⊆ readsCases cs ++ readsDflt df
  | [], none => by simp [selectCase, readsCases, readsDflt, blockReads]
  | [], some b => by simp [selectCase, readsCases, readsDflt]
  | (l, b) :: rest, df => by
      unfold selectCase
      by_cases hlab : (litValue l == cv) = true
      · rw [List.find?_cons_of_pos (by simpa using hlab)]
        simp only [readsCases]
        intro i hi; exact List.mem_append_left _ (List.mem_append_left _ hi)
      · rw [List.find?_cons_of_neg (by simpa using hlab)]
        simp only [readsCases]
        intro i hi
        rcases List.mem_append.mp (blockReads_selectCase_subset cv rest df hi) with h | h
        · exact List.mem_append_left _ (List.mem_append_right _ h)
        · exact List.mem_append_right _ h

/-- Updating a slot outside `S` preserves agreement. -/
theorem AgreeOn.upd_out {S : List (Fin n)} {σ₁ σ₂} (h : AgreeOn S σ₁ σ₂) {d : Fin n}
    (hd : d ∉ S) (v : U256) : AgreeOn S (upd σ₁ d v) σ₂ := by
  intro i hi
  have : i ≠ d := fun he => hd (he ▸ hi)
  simp only [upd]
  rw [if_neg (by simpa using this)]
  exact h i hi

/-- Updating a slot on both sides to the same value preserves agreement. -/
theorem AgreeOn.upd_both {S : List (Fin n)} {σ₁ σ₂} (h : AgreeOn S σ₁ σ₂) (d : Fin n) (v : U256) :
    AgreeOn S (upd σ₁ d v) (upd σ₂ d v) := by
  intro i hi
  simp only [upd]
  by_cases he : i = d <;> simp [he, h i hi]

/-- Multi-update with the same slots/values on both sides preserves agreement. -/
theorem AgreeOn.updMany_both {S : List (Fin n)} {σ₁ σ₂} (h : AgreeOn S σ₁ σ₂)
    (ds : List (Fin n)) (vs : List U256) : AgreeOn S (updMany σ₁ ds vs) (updMany σ₂ ds vs) := by
  simp only [updMany]
  induction ds.zip vs generalizing σ₁ σ₂ with
  | nil => exact h
  | cons p rest ih => exact ih (h.upd_both p.1 p.2)

/-- Folding `upd` over pairs whose keys are all outside `S` preserves agreement with the start. -/
theorem agree_foldl_upd {S : List (Fin n)} (ps : List (Fin n × U256))
    (hp : ∀ p ∈ ps, p.1 ∉ S) : ∀ σ : Store n, AgreeOn S σ (ps.foldl (fun s p => upd s p.1 p.2) σ) := by
  induction ps with
  | nil => intro σ; exact fun i _ => rfl
  | cons p ps ih =>
      intro σ
      simp only [List.foldl_cons]
      exact AgreeOn.trans (AgreeOn.upd_out (fun _ _ => rfl) (hp p (List.mem_cons_self ..)) p.2).symm
        (ih (fun q hq => hp q (List.mem_cons_of_mem p hq)) (upd σ p.1 p.2))

/-- Multi-updating slots all outside `S` preserves agreement with the original store. -/
theorem AgreeOn.updMany_out {S : List (Fin n)} {σ : Store n} {ds : List (Fin n)}
    (hd : ∀ d ∈ ds, d ∉ S) (vs : List U256) : AgreeOn S σ (updMany σ ds vs) := by
  simp only [updMany]
  exact agree_foldl_upd _ (fun p hp => hd p.1 (List.of_mem_zip hp).1) σ

/-! ### Reads determine evaluation -/

/-- An atom whose slot (if any) is live evaluates identically under agreeing stores. -/
theorem evalAtom_agree {S : List (Fin n)} {σ₁ σ₂} (h : AgreeOn S σ₁ σ₂) {a : Atom n}
    (hin : ∀ i, atomSlot? a = some i → i ∈ S) : evalAtom σ₁ a = evalAtom σ₂ a := by
  cases a with
  | lit l  => rfl
  | slot i => exact h i (hin i rfl)

/-- A list of operands whose live slots agree evaluates identically. -/
theorem map_evalAtom_agree {S : List (Fin n)} {σ₁ σ₂} (h : AgreeOn S σ₁ σ₂) {args : List (Atom n)}
    (hin : ∀ i ∈ args.filterMap atomSlot?, i ∈ S) :
    args.map (evalAtom σ₁) = args.map (evalAtom σ₂) := by
  induction args with
  | nil => rfl
  | cons a as ih =>
      have hhead : evalAtom σ₁ a = evalAtom σ₂ a := by
        apply evalAtom_agree h
        intro i hia
        exact hin i (List.mem_filterMap.mpr ⟨a, List.mem_cons_self .., hia⟩)
      have htail : ∀ i ∈ as.filterMap atomSlot?, i ∈ S := by
        intro i hi
        obtain ⟨a', ha', hia'⟩ := List.mem_filterMap.mp hi
        exact hin i (List.mem_filterMap.mpr ⟨a', List.mem_cons_of_mem a ha', hia'⟩)
      simp only [List.map_cons, hhead, ih htail]

/-- An rhs whose read slots are live evaluates to the same result under agreeing stores (built-ins by
equal operand lists; calls reuse the callee derivation since the seed is argument-determined). -/
theorem execRhs_agree {funs : Funs} {S : List (Fin n)} {σ₁ σ₂} (h : AgreeOn S σ₁ σ₂) {rhs : Rhs n}
    (hin : ∀ i ∈ rhsReads rhs, i ∈ S) {st res} :
    ExecRhs funs σ₁ st rhs res ↔ ExecRhs funs σ₂ st rhs res := by
  have key : ∀ {τ₁ τ₂ : Store n}, AgreeOn S τ₁ τ₂ → (∀ i ∈ rhsReads rhs, i ∈ S) →
      ExecRhs funs τ₁ st rhs res → ExecRhs funs τ₂ st rhs res := by
    intro τ₁ τ₂ hτ hin' hstep
    cases rhs with
    | atom a =>
        cases hstep
        have : evalAtom τ₁ a = evalAtom τ₂ a :=
          evalAtom_agree hτ (by intro i hi; apply hin'; simp [rhsReads, hi])
        rw [this]; exact Step.atom
    | builtin op args =>
        cases hstep with
        | builtin hb =>
            have : args.map (evalAtom τ₁) = args.map (evalAtom τ₂) :=
              map_evalAtom_agree hτ (by intro i hi; exact hin' i (by simpa [rhsReads] using hi))
            exact Step.builtin (this ▸ hb)
    | call fn args =>
        have hmap : args.map (evalAtom τ₁) = args.map (evalAtom τ₂) :=
          map_evalAtom_agree hτ (by intro i hi; exact hin' i (by simpa [rhsReads] using hi))
        cases hstep with
        | callNorm hfn hbody ho => exact Step.callNorm hfn (hmap ▸ hbody) ho
        | callHalt hfn hbody    => exact Step.callHalt hfn (hmap ▸ hbody)
  exact ⟨key h hin, key h.symm (by intro i hi; exact hin i hi)⟩

/-! ### Dead statements are observationally inert -/

/-- A pure rhs evaluates (if at all) to `.ok` with the state unchanged — never halts. -/
theorem pure_rhs_ok {funs : Funs} {rhs : Rhs n} (hp : rhsPure rhs = true) {σ st res}
    (hstep : ExecRhs funs σ st rhs res) : ∃ vs, res = .ok vs st := by
  cases rhs with
  | atom a          => cases hstep; exact ⟨_, rfl⟩
  | builtin op args => cases hstep with
      | builtin hb => exact pure_builtin_ok (by simpa [rhsPure] using hp) hb
  | call fn args    => simp [rhsPure] at hp

/-- A statement `deadCode` deletes leaves the `EvmState` and outcome untouched and only perturbs the
store on a slot outside `reads ++ prot` — so it is invisible to any downstream read or return. -/
theorem dead_step {reads prot : List (Fin n)} {s : Stmt n} (hd : isDead reads prot s = true)
    {funs σ st σ' st' o} (hstep : Step funs σ st (.stmt s) (.sres σ' st' o)) :
    st' = st ∧ o = .normal ∧ AgreeOn (reads ++ prot) σ σ' := by
  cases s with
  | assign ds rhs =>
      simp only [isDead, Bool.and_eq_true] at hd
      obtain ⟨hp, hdall⟩ := hd
      have hdnotin : ∀ d ∈ ds, d ∉ reads ++ prot := by
        intro d hdmem
        have hdd := (List.all_eq_true.mp hdall) d hdmem
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hdd
        simp only [List.mem_append, not_or]
        refine ⟨fun hc => ?_, fun hc => ?_⟩
        · simp [List.contains_eq_mem, hc] at hdd
        · simp [List.contains_eq_mem, hc] at hdd
      cases hstep with
      | assignOk hr =>
          obtain ⟨vs, hres⟩ := pure_rhs_ok hp hr
          simp only [BuiltinResult.ok.injEq] at hres
          exact ⟨hres.2, rfl, AgreeOn.updMany_out hdnotin _⟩
      | assignHalt hr => obtain ⟨vs, hc⟩ := pure_rhs_ok hp hr; simp at hc
  | cond c b         => simp [isDead] at hd
  | switch c cs df   => simp [isDead] at hd
  | loop post body   => simp [isDead] at hd
  | «break»          => simp [isDead] at hd
  | «continue»       => simp [isDead] at hd
  | leave            => simp [isDead] at hd

/-- A dead `assign`'s rhs is pure and all its destinations are outside `reads ++ prot`. -/
theorem dead_dsts_notin {reads prot : List (Fin n)} {ds : List (Fin n)} {rhs : Rhs n}
    (hd : isDead reads prot (.assign ds rhs) = true) :
    rhsPure rhs = true ∧ ∀ d ∈ ds, d ∉ reads ++ prot := by
  simp only [isDead, Bool.and_eq_true] at hd
  obtain ⟨hp, hdall⟩ := hd
  refine ⟨hp, fun d hdmem => ?_⟩
  have hdd := (List.all_eq_true.mp hdall) d hdmem
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hdd
  simp only [List.mem_append, not_or]
  exact ⟨fun hc => by simp [List.contains_eq_mem, hc] at hdd,
         fun hc => by simp [List.contains_eq_mem, hc] at hdd⟩

/-! ### Well-formedness (for the reverse direction) -/

/-! Well-formedness: every pure `assign` rhs evaluates to an `.ok` result from any store. This rules
out exactly the stuck ill-typed terms (arity mismatch, assign-from-void) that would otherwise let
`deadCode` delete a *stuck* statement and thereby invent behaviour. `ofYul` on type-checked Yul
establishes it; here it is an explicit hypothesis. -/
mutual
def WFStmt (funs : Funs) : Stmt n → Prop
  | .assign _ rhs   => rhsPure rhs = true → ∀ (σ : Store n) st, ∃ vs, ExecRhs funs σ st rhs (.ok vs st)
  | .cond _ b       => WFBlock funs b
  | .switch _ cs df => WFCases funs cs ∧ WFDflt funs df
  | .loop p b       => WFBlock funs p ∧ WFBlock funs b
  | _               => True
def WFBlock (funs : Funs) : Block n → Prop
  | []      => True
  | s :: ss => WFStmt funs s ∧ WFBlock funs ss
def WFCases (funs : Funs) : List (Literal × Block n) → Prop
  | []             => True
  | (_, b) :: rest => WFBlock funs b ∧ WFCases funs rest
def WFDflt (funs : Funs) : Option (Block n) → Prop
  | none   => True
  | some b => WFBlock funs b
end

/-- **The `WellFormed` payoff**: a dead statement can be *reinserted* — it has an inert execution
(normal outcome, `EvmState` unchanged, store perturbed only outside `reads ++ prot`). This is what
the reverse simulation uses to reconstruct the statements `deadCode` deleted. -/
theorem dead_inert {reads prot : List (Fin n)} {s : Stmt n} {funs} (hd : isDead reads prot s = true)
    (hwf : WFStmt funs s) (σ : Store n) (st : State) :
    ∃ σ', Step funs σ st (.stmt s) (.sres σ' st .normal) ∧ AgreeOn (reads ++ prot) σ σ' := by
  cases s with
  | assign ds rhs =>
      obtain ⟨hp, hdnotin⟩ := dead_dsts_notin hd
      simp only [WFStmt] at hwf
      obtain ⟨vs, hrhs⟩ := hwf hp σ st
      exact ⟨updMany σ ds vs, Step.assignOk hrhs, AgreeOn.updMany_out hdnotin _⟩
  | cond c b         => simp [isDead] at hd
  | switch c cs df   => simp [isDead] at hd
  | loop post body   => simp [isDead] at hd
  | «break»          => simp [isDead] at hd
  | «continue»       => simp [isDead] at hd
  | leave            => simp [isDead] at hd

/-! ### Forward simulation -/

/-- **Forward store-agreement simulation.** Any source execution can be replayed by the dead-code-
eliminated program from any store agreeing on the live slots (`reads ++ prot`), reaching the same
`EvmState`/outcome and a final store that still agrees on the live slots. Proved by induction on the
derivation with a code-shape motive; `rhs` premises reuse `execRhs_agree` (calls included, since the
seed is argument-determined — the callee table is unchanged here). -/
theorem dce_fwd {funs : Funs} {n} {σ : Store n} {st} {code : Code n} {res}
    (h : Step funs σ st code res) :
    (match code, res with
     | .rhs r, res => ∀ (S : List (Fin n)) σ₂, AgreeOn S σ σ₂ → (∀ i ∈ rhsReads r, i ∈ S) →
         Step funs σ₂ st (.rhs r) res
     | .stmt s, .sres σ' st' o => ∀ (reads prot : List (Fin n)) σ₂, AgreeOn (reads ++ prot) σ σ₂ →
         (∀ i ∈ stmtReads s, i ∈ reads ++ prot) →
         ∃ σ₂', Step funs σ₂ st (.stmt (dceStmt reads prot s)) (.sres σ₂' st' o)
           ∧ AgreeOn (reads ++ prot) σ' σ₂'
     | .stmts b, .sres σ' st' o => ∀ (reads prot : List (Fin n)) σ₂, AgreeOn (reads ++ prot) σ σ₂ →
         (∀ i ∈ blockReads b, i ∈ reads ++ prot) →
         ∃ σ₂', Step funs σ₂ st (.stmts (dceBlock reads prot b)) (.sres σ₂' st' o)
           ∧ AgreeOn (reads ++ prot) σ' σ₂'
     | .loop post body, .sres σ' st' o => ∀ (reads prot : List (Fin n)) σ₂,
         AgreeOn (reads ++ prot) σ σ₂ → (∀ i ∈ blockReads post ++ blockReads body, i ∈ reads ++ prot) →
         ∃ σ₂', Step funs σ₂ st (.loop (dceBlock reads prot post) (dceBlock reads prot body))
           (.sres σ₂' st' o) ∧ AgreeOn (reads ++ prot) σ' σ₂'
     | _, _ => True) := by
  induction h with
  | atom => intro S σ₂ hag hin; exact (execRhs_agree hag hin).mp Step.atom
  | builtin hb => intro S σ₂ hag hin; exact (execRhs_agree hag hin).mp (Step.builtin hb)
  | callNorm hfn hbody ho => intro S σ₂ hag hin; exact (execRhs_agree hag hin).mp (Step.callNorm hfn hbody ho)
  | callHalt hfn hbody => intro S σ₂ hag hin; exact (execRhs_agree hag hin).mp (Step.callHalt hfn hbody)
  | @assignOk _ _ _ ds rhs vs _ _ ihr =>
      intro reads prot σ₂ hag hin
      exact ⟨updMany σ₂ ds vs, Step.assignOk (ihr _ σ₂ hag (by simpa [stmtReads] using hin)),
        AgreeOn.updMany_both hag ds vs⟩
  | assignHalt hr ihr =>
      intro reads prot σ₂ hag hin
      exact ⟨σ₂, Step.assignHalt (ihr _ σ₂ hag (by simpa [stmtReads] using hin)), hag⟩
  | @condFalse _ _ _ c body hc =>
      intro reads prot σ₂ hag hin
      have hcin : ∀ i, atomSlot? c = some i → i ∈ reads ++ prot := fun i hi => hin i
        (by simp only [stmtReads]; exact List.mem_append_left _ (by rw [hi]; exact List.mem_cons_self ..))
      exact ⟨σ₂, Step.condFalse ((evalAtom_agree hag hcin).symm.trans hc), hag⟩
  | @condTrue _ _ _ c body _ _ _ hc hbody ihbody =>
      intro reads prot σ₂ hag hin
      have hcin : ∀ i, atomSlot? c = some i → i ∈ reads ++ prot := fun i hi => hin i
        (by simp only [stmtReads]; exact List.mem_append_left _ (by rw [hi]; exact List.mem_cons_self ..))
      obtain ⟨σ₂', hstep, hag'⟩ := ihbody reads prot σ₂ hag
        (fun i hi => hin i (by simp only [stmtReads]; exact List.mem_append_right _ hi))
      exact ⟨σ₂', Step.condTrue (fun h0 => hc ((evalAtom_agree hag hcin).trans h0)) hstep, hag'⟩
  | @switch _ σ0 _ c cases dflt _ _ _ hsel ihsel =>
      intro reads prot σ₂ hag hin
      have hc : evalAtom σ₂ c = evalAtom σ0 c :=
        (evalAtom_agree hag (fun i hi => hin i
          (by simp only [stmtReads]
              exact List.mem_append_left _ (List.mem_append_left _
                (by rw [hi]; exact List.mem_cons_self ..))))).symm
      have hselin : ∀ i ∈ blockReads (selectCase (evalAtom σ0 c) cases dflt), i ∈ reads ++ prot := by
        intro i hi
        apply hin
        simp only [stmtReads]
        rcases List.mem_append.mp (blockReads_selectCase_subset (evalAtom σ0 c) cases dflt hi) with h | h
        · exact List.mem_append_left _ (List.mem_append_right _ h)
        · exact List.mem_append_right _ h
      obtain ⟨σ₂', hstep, hag'⟩ := ihsel reads prot σ₂ hag hselin
      refine ⟨σ₂', Step.switch ?_, hag'⟩
      rw [hc, dce_selectCase]; exact hstep
  | loopS hl ihloop =>
      intro reads prot σ₂ hag hin
      obtain ⟨σ₂', hstep, hag'⟩ := ihloop reads prot σ₂ hag (by simpa [stmtReads] using hin)
      exact ⟨σ₂', Step.loopS hstep, hag'⟩
  | brk => intro reads prot σ₂ hag hin; exact ⟨σ₂, Step.brk, hag⟩
  | cont => intro reads prot σ₂ hag hin; exact ⟨σ₂, Step.cont, hag⟩
  | lv => intro reads prot σ₂ hag hin; exact ⟨σ₂, Step.lv, hag⟩
  | nil => intro reads prot σ₂ hag hin; exact ⟨σ₂, Step.nil, hag⟩
  | @consNormal _ _ _ _ _ _ _ s rest o hs hrest ihs ihrest =>
      intro reads prot σ₂ hag hin
      by_cases hd : isDead reads prot s = true
      · obtain ⟨hst, _, hσσ₁⟩ := dead_step hd hs
        subst hst
        obtain ⟨σ₂'', hstep, hag''⟩ := ihrest reads prot σ₂ (hσσ₁.symm.trans hag)
          (fun i hi => hin i (by simp only [blockReads]; exact List.mem_append_right _ hi))
        rw [dceBlock, if_pos hd]; exact ⟨σ₂'', hstep, hag''⟩
      · obtain ⟨σ₂m, hs2, hagm⟩ := ihs reads prot σ₂ hag
          (fun i hi => hin i (by simp only [blockReads]; exact List.mem_append_left _ hi))
        obtain ⟨σ₂'', hr2, hag''⟩ := ihrest reads prot σ₂m hagm
          (fun i hi => hin i (by simp only [blockReads]; exact List.mem_append_right _ hi))
        rw [dceBlock, if_neg hd]; exact ⟨σ₂'', Step.consNormal hs2 hr2, hag''⟩
  | @consStop _ _ _ _ _ s rest o hs hne ihs =>
      intro reads prot σ₂ hag hin
      by_cases hd : isDead reads prot s = true
      · exact absurd (dead_step hd hs).2.1 hne
      · obtain ⟨σ₂', hs2, hag'⟩ := ihs reads prot σ₂ hag
          (fun i hi => hin i (by simp only [blockReads]; exact List.mem_append_left _ hi))
        rw [dceBlock, if_neg hd]; exact ⟨σ₂', Step.consStop hs2 hne, hag'⟩
  | loopBrk hbody ihbody =>
      intro reads prot σ₂ hag hin
      obtain ⟨σ₂', hb2, hag'⟩ := ihbody reads prot σ₂ hag
        (fun i hi => hin i (List.mem_append_right _ hi))
      exact ⟨σ₂', Step.loopBrk hb2, hag'⟩
  | loopLeave hbody ihbody =>
      intro reads prot σ₂ hag hin
      obtain ⟨σ₂', hb2, hag'⟩ := ihbody reads prot σ₂ hag
        (fun i hi => hin i (List.mem_append_right _ hi))
      exact ⟨σ₂', Step.loopLeave hb2, hag'⟩
  | loopHalt hbody ihbody =>
      intro reads prot σ₂ hag hin
      obtain ⟨σ₂', hb2, hag'⟩ := ihbody reads prot σ₂ hag
        (fun i hi => hin i (List.mem_append_right _ hi))
      exact ⟨σ₂', Step.loopHalt hb2, hag'⟩
  | loopStep hbody hob hpost hloop ihbody ihpost ihloop =>
      intro reads prot σ₂ hag hin
      obtain ⟨σ₂b, hb2, hagb⟩ := ihbody reads prot σ₂ hag
        (fun i hi => hin i (List.mem_append_right _ hi))
      obtain ⟨σ₂p, hp2, hagp⟩ := ihpost reads prot σ₂b hagb
        (fun i hi => hin i (List.mem_append_left _ hi))
      obtain ⟨σ₂', hl2, hag'⟩ := ihloop reads prot σ₂p hagp hin
      exact ⟨σ₂', Step.loopStep hb2 hob hp2 hl2, hag'⟩
  | loopPostStop hbody hob hpost hne ihbody ihpost =>
      intro reads prot σ₂ hag hin
      obtain ⟨σ₂b, hb2, hagb⟩ := ihbody reads prot σ₂ hag
        (fun i hi => hin i (List.mem_append_right _ hi))
      obtain ⟨σ₂p, hp2, hagp⟩ := ihpost reads prot σ₂b hagb
        (fun i hi => hin i (List.mem_append_left _ hi))
      exact ⟨σ₂p, Step.loopPostStop hb2 hob hp2 hne, hagp⟩

/-! ### Forward soundness of a `main`-style entry body -/

/-- One dead-code pass over an entry body (run from a zero-initialised frame, `prot = []`) is
forward-simulated: the local store `fun _ => 0` agrees with itself everywhere, so `dce_fwd` applies
with the trivial agreement. Stated at the `ExecBlock` level (the store `σ''` is discarded, exactly
the observation `Run` keeps). -/
theorem dceBlock_exec_fwd {funs : Funs} {m} {b : Block m} {σ' st st' o}
    (hexec : ExecBlock funs (fun _ => 0) st b σ' st' o) :
    ∃ σ'', ExecBlock funs (fun _ => 0) st (dceBlock (blockReads b) [] b) σ'' st' o := by
  obtain ⟨σ₂', hstep, _⟩ := dce_fwd hexec (blockReads b) [] (fun _ => 0) (fun _ _ => rfl)
    (by intro i hi; rw [List.append_nil]; exact hi)
  exact ⟨σ₂', hstep⟩

/-- The bounded fixpoint `deadCode [] fuel` over an entry body is forward-simulated. This is the
`deadCode` soundness content for a `main`-style body; lifting it to a whole-program `Run ↔` over the
unified function table additionally needs the call-graph store-agreement coupling (future work). -/
theorem deadCode_exec_fwd {funs : Funs} {m} (fuel : Nat) : ∀ {b : Block m} {σ' st st' o},
    ExecBlock funs (fun _ => 0) st b σ' st' o →
      ∃ σ'', ExecBlock funs (fun _ => 0) st (deadCode [] fuel b) σ'' st' o := by
  induction fuel with
  | zero => intro b σ' st st' o h; exact ⟨σ', by simpa [deadCode] using h⟩
  | succ fuel ih =>
      intro b σ' st st' o h
      rw [deadCode]
      by_cases hfix : (blockCount (dceBlock (blockReads b) [] b) == blockCount b) = true
      · rw [if_pos hfix]; exact dceBlock_exec_fwd h
      · rw [if_neg hfix]
        obtain ⟨σ'', h''⟩ := dceBlock_exec_fwd h
        exact ih h''

/-! ### Reverse simulation -/

/-- Reverse block simulation: a run of the dce'd block lifts back to a run of the original (from any
agreeing store), with the same `EvmState`/outcome and agreeing final store. -/
abbrev RevSimB (funs : Funs) (reads prot : List (Fin n)) (b : Block n) : Prop :=
  ∀ {σ₂ : Store n} {st σ₂' st' o},
    Step funs σ₂ st (.stmts (dceBlock reads prot b)) (.sres σ₂' st' o) →
    ∀ σ₁, AgreeOn (reads ++ prot) σ₁ σ₂ →
      ∃ σ₁', Step funs σ₁ st (.stmts b) (.sres σ₁' st' o) ∧ AgreeOn (reads ++ prot) σ₁' σ₂'

/-- Reverse loop simulation, given reverse sims for `post`/`body`. Induction on the dce'd loop's
derivation (generalize the code, discharge the non-loop constructors with `nofun`). -/
theorem dce_bwd_loop {funs : Funs} {reads prot : List (Fin n)} {post body : Block n}
    (revPost : RevSimB funs reads prot post) (revBody : RevSimB funs reads prot body)
    {σ₂ : Store n} {st code res} (h : Step funs σ₂ st code res) :
    ∀ {σ₂' st' o}, code = .loop (dceBlock reads prot post) (dceBlock reads prot body) →
      res = .sres σ₂' st' o → ∀ σ₁, AgreeOn (reads ++ prot) σ₁ σ₂ →
        ∃ σ₁', Step funs σ₁ st (.loop post body) (.sres σ₁' st' o)
          ∧ AgreeOn (reads ++ prot) σ₁' σ₂' := by
  induction h with
  | loopBrk hb _ =>
      intro σ₂' st' o hcode hres σ₁ hag
      injection hcode with hp hbdy; subst hp; subst hbdy; injection hres with h1 h2 h3
      subst h1; subst h2; subst h3
      obtain ⟨σ₁', hb', hag'⟩ := revBody hb σ₁ hag
      exact ⟨σ₁', Step.loopBrk hb', hag'⟩
  | loopLeave hb _ =>
      intro σ₂' st' o hcode hres σ₁ hag
      injection hcode with hp hbdy; subst hp; subst hbdy; injection hres with h1 h2 h3
      subst h1; subst h2; subst h3
      obtain ⟨σ₁', hb', hag'⟩ := revBody hb σ₁ hag
      exact ⟨σ₁', Step.loopLeave hb', hag'⟩
  | loopHalt hb _ =>
      intro σ₂' st' o hcode hres σ₁ hag
      injection hcode with hp hbdy; subst hp; subst hbdy; injection hres with h1 h2 h3
      subst h1; subst h2; subst h3
      obtain ⟨σ₁', hb', hag'⟩ := revBody hb σ₁ hag
      exact ⟨σ₁', Step.loopHalt hb', hag'⟩
  | loopStep hb hob hp _ _ _ ihl =>
      intro σ₂' st' o hcode hres σ₁ hag
      injection hcode with hpost hbody; subst hpost; subst hbody; injection hres with h1 h2 h3
      subst h1; subst h2; subst h3
      obtain ⟨σ₁b, hb', hagb⟩ := revBody hb σ₁ hag
      obtain ⟨σ₁p, hp', hagp⟩ := revPost hp σ₁b hagb
      obtain ⟨σ₁', hl', hag'⟩ := ihl revPost revBody rfl rfl σ₁p hagp
      exact ⟨σ₁', Step.loopStep hb' hob hp' hl', hag'⟩
  | loopPostStop hb hob hp hne _ _ =>
      intro σ₂' st' o hcode hres σ₁ hag
      injection hcode with hpost hbody; subst hpost; subst hbody; injection hres with h1 h2 h3
      subst h1; subst h2; subst h3
      obtain ⟨σ₁b, hb', hagb⟩ := revBody hb σ₁ hag
      obtain ⟨σ₁p, hp', hagp⟩ := revPost hp σ₁b hagb
      exact ⟨σ₁p, Step.loopPostStop hb' hob hp' hne, hagp⟩
  | _ => intro _ _ _ hcode; nomatch hcode

end YulIR.FinFrame.Sem
