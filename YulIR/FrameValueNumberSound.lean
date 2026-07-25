import YulIR.FramePasses
import YulIR.FrameDceSound

set_option warningAsError true
/-!
# YulIR.FrameValueNumberSound — soundness of `valueNumber`

`valueNumber` is constant/copy propagation + common-subexpression elimination. Unlike the other
passes it carries an *environment* (`env : slot ↦ atom`, `avail : expr ↦ slot`), so its correctness
is a **store-relative** invariant threaded through the block simulation: the maps are only valid
against a particular store, and stay valid because the pass only ever records *immutable*
(written-at-most-once) slots whose defining write has already happened (read-after-write) — the
discipline the decidable checker `vnSafe` (`YulIR.FramePasses`) enforces.

The structure:

* **Invariant** (`VNInv`): `EnvValid`/`AvailValid` (the maps are true of the current store) plus
  `RefsOK` (every referenced slot is immutable and in the checker's written-set `W`) plus `W ⊆ imm`.
  The checker guarantees no remaining statement writes a `W`-slot, so the invariant transports
  along execution (`VNInv.transport` over `AgreeOn W`).
* **Record step** (`recordWrite_sim`): a recording assign's emitted rhs executes exactly like the
  original — the CSE hit needs no well-formedness hypothesis because the avail entry itself
  witnesses evaluability — and the extended maps re-establish the invariant.
* **Simulation** (`vn_sim`): by functional induction on the pass; loops via `loop_imp_sim` (a
  conditional loop simulation re-establishing the invariant each iteration).
* **Capstones**: `valueNumber_equiv` (checker-accepted body ⟹ `EquivBlock`),
  `valueNumberChecked_equiv` (the guarded pass, *unconditionally* sound), and
  `valueNumber_program_run` (whole-program, via the per-function `run_mapBodies`).
-/

namespace YulIR.FinFrame.Sem

open YulSemantics (Outcome BuiltinResult Literal Ident)
open YulSemantics.EVM (evm litValue stepOp EvmState)

/-! ### BEq facts -/

instance : LawfulBEq (Atom n) where
  eq_of_beq := atom_eq_of_beq
  rfl := by
    intro a
    cases a with
    | lit l => exact beq_self_eq_true l
    | slot i => exact beq_self_eq_true i

/-- BEq on rhs reflects equality (components are lawful). -/
theorem rhs_eq_of_beq {r₁ r₂ : Rhs n} (h : (r₁ == r₂) = true) : r₁ = r₂ := by
  cases r₁ with
  | atom a₁ => cases r₂ with
    | atom a₂ => exact congrArg _ (atom_eq_of_beq h)
    | builtin op args => exact Bool.noConfusion h
    | call fn args => exact Bool.noConfusion h
  | builtin op₁ as₁ => cases r₂ with
    | atom a => exact Bool.noConfusion h
    | builtin op₂ as₂ =>
        have h2 : (op₁ == op₂ && as₁ == as₂) = true := h
        obtain ⟨ho, ha⟩ := Bool.and_eq_true_iff.mp h2
        rw [eq_of_beq ho, eq_of_beq ha]
    | call fn args => exact Bool.noConfusion h
  | call f₁ as₁ => cases r₂ with
    | atom a => exact Bool.noConfusion h
    | builtin op args => exact Bool.noConfusion h
    | call f₂ as₂ =>
        have h2 : (f₁ == f₂ && as₁ == as₂) = true := h
        obtain ⟨hf, ha⟩ := Bool.and_eq_true_iff.mp h2
        rw [eq_of_beq hf, eq_of_beq ha]

/-! ### Pure built-in facts -/

theorem bin_ok_len {f : U256 → U256 → U256} {args : List U256} {st : State} {vs st'}
    (h : YulSemantics.EVM.bin f args st = some (.ok vs st')) : vs.length = 1 := by
  unfold YulSemantics.EVM.bin at h
  split at h <;> simp only [Option.some.injEq, YulSemantics.BuiltinResult.ok.injEq,
    reduceCtorEq] at h
  rw [← h.1]
  rfl

theorem un_ok_len {f : U256 → U256} {args : List U256} {st : State} {vs st'}
    (h : YulSemantics.EVM.un f args st = some (.ok vs st')) : vs.length = 1 := by
  unfold YulSemantics.EVM.un at h
  split at h <;> simp only [Option.some.injEq, YulSemantics.BuiltinResult.ok.injEq,
    reduceCtorEq] at h
  rw [← h.1]
  rfl

theorem ter_ok_len {f : U256 → U256 → U256 → U256} {args : List U256} {st : State} {vs st'}
    (h : YulSemantics.EVM.ter f args st = some (.ok vs st')) : vs.length = 1 := by
  unfold YulSemantics.EVM.ter at h
  split at h <;> simp only [Option.some.injEq, YulSemantics.BuiltinResult.ok.injEq,
    reduceCtorEq] at h
  rw [← h.1]
  rfl

/-- For a pure op the number of returned values is a function of the op alone. -/
theorem pure_ok_len {op} (hp : Op.isPure op = true) {v₁ v₂ : List U256} {s₁ s₂ : State}
    {vs₁ vs₂ st₁ st₂}
    (h₁ : stepOp op v₁ s₁ = some (.ok vs₁ st₁)) (h₂ : stepOp op v₂ s₂ = some (.ok vs₂ st₂)) :
    vs₁.length = vs₂.length := by
  cases op <;> first
    | exact absurd hp (by decide)
    | (simp only [stepOp] at h₁ h₂;
       first
         | exact (bin_ok_len h₁).trans (bin_ok_len h₂).symm
         | exact (un_ok_len h₁).trans (un_ok_len h₂).symm
         | exact (ter_ok_len h₁).trans (ter_ok_len h₂).symm
         | (split at h₁ <;> split at h₂ <;> simp_all))

/-- A pure op that probes to a single output at the call's arity returns a singleton. -/
theorem pure_ok_single {op} (hp : Op.isPure op = true) {args : List U256} {st : State} {vs st'}
    (hpr : probe1 op args.length = true) (h : stepOp op args st = some (.ok vs st')) :
    ∃ v, vs = [v] := by
  unfold probe1 at hpr
  split at hpr
  · next x st0 heq =>
      have hlen : vs.length = 1 := pure_ok_len hp h heq
      rcases vs with _ | ⟨v, _ | _⟩ <;> simp_all
  · exact Bool.noConfusion hpr

/-- A pure built-in's `.ok` result is state-independent: it evaluates identically from any state. -/
theorem pure_st_indep {op} (hp : Op.isPure op = true) {args : List U256} {st : State} {vs}
    (h : evm.Builtin op args st (.ok vs st)) (st'' : State) :
    evm.Builtin op args st'' (.ok vs st'') := by
  have hs : stepOp op args st = some (.ok vs st) := h
  have hdef : (stepOp op args st'').isSome = true := pure_defined hp (by rw [hs]; rfl)
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hdef
  obtain ⟨outs, rfl⟩ := pure_builtin_ok hp (show evm.Builtin op args st'' r from hr)
  have hout : outs = vs :=
    YulSemantics.EVM.effects_sound.read op (isPure_effects hp).1 args st'' st outs st'' vs st hr
      (show evm.Builtin op args st (.ok vs st) from hs)
  rwa [hout] at hr

/-- Built-in evaluation is deterministic (`Builtin` is a function graph). -/
theorem builtin_det {op} {args : List U256} {st : State} {r₁ r₂}
    (h₁ : evm.Builtin op args st r₁) (h₂ : evm.Builtin op args st r₂) : r₁ = r₂ := by
  have hs₁ : stepOp op args st = some r₁ := h₁
  have hs₂ : stepOp op args st = some r₂ := h₂
  rw [hs₁] at hs₂
  exact Option.some.inj hs₂

theorem updMany_single (σ : Store n) (d : Fin n) (v : U256) :
    updMany σ [d] [v] = upd σ d v := rfl

/-! ### Environment validity -/

/-- The copy/constant environment is *valid* at a store when every mapping `i ↦ a` holds: the slot
`i` currently has the value the atom `a` denotes. -/
def EnvValid (σ : Store n) (env : List (Fin n × Atom n)) : Prop :=
  ∀ p ∈ env, σ p.1 = evalAtom σ p.2

/-- Resolving an atom through a valid environment preserves its value. -/
theorem resolveAtom_sound {σ : Store n} {env} (h : EnvValid σ env) (a : Atom n) :
    evalAtom σ (resolveAtom env a) = evalAtom σ a := by
  cases a with
  | lit l => rfl
  | slot i =>
      simp only [resolveAtom]
      cases hf : env.find? (fun p => p.1 == i) with
      | none => rfl
      | some p =>
          have hmem : p ∈ env := List.mem_of_find?_eq_some hf
          have hp := List.find?_some hf
          have hpi : p.1 = i := by simpa using hp
          show evalAtom σ p.2 = evalAtom σ (Atom.slot i)
          have : evalAtom σ (Atom.slot i) = σ i := rfl
          rw [this, ← hpi]; exact (h p hmem).symm

/-- Resolving all operands of a list preserves the evaluated value list. -/
theorem map_resolveAtom {σ : Store n} {env} (h : EnvValid σ env) (args : List (Atom n)) :
    (args.map (resolveAtom env)).map (evalAtom σ) = args.map (evalAtom σ) := by
  rw [List.map_map]
  exact List.map_congr_left (fun a _ => resolveAtom_sound h a)

/-- Resolving an rhs through a valid environment preserves its evaluation: it executes to exactly
the same results. -/
theorem resolveRhs_exec {funs : Funs} {σ : Store n} {env} (h : EnvValid σ env) {rhs : Rhs n}
    {st r} : ExecRhs funs σ st (resolveRhs env rhs) r ↔ ExecRhs funs σ st rhs r := by
  cases rhs with
  | atom a =>
      simp only [resolveRhs]
      constructor
      · intro hh; cases hh; rw [resolveAtom_sound h]; exact .atom
      · intro hh; cases hh; rw [← resolveAtom_sound h]; exact .atom
  | builtin op args =>
      simp only [resolveRhs]
      constructor
      · intro hh; cases hh with
        | builtin hb => rw [map_resolveAtom h] at hb; exact .builtin hb
      · intro hh; cases hh with
        | builtin hb => rw [← map_resolveAtom h] at hb; exact .builtin hb
  | call fn args =>
      simp only [resolveRhs]
      constructor
      · intro hh; cases hh with
        | callNorm hl hbody ho => rw [map_resolveAtom h] at hbody; exact .callNorm hl hbody ho
        | callHalt hl hbody => rw [map_resolveAtom h] at hbody; exact .callHalt hl hbody
      · intro hh; cases hh with
        | callNorm hl hbody ho => rw [← map_resolveAtom h] at hbody; exact .callNorm hl hbody ho
        | callHalt hl hbody => rw [← map_resolveAtom h] at hbody; exact .callHalt hl hbody

/-! ### The full value-numbering invariant

Beyond store-validity (`EnvValid`/`AvailValid`), the simulation needs the maps to be structurally
anchored in the checker's written-set `W`: every referenced slot is immutable and already written,
and `W` itself contains only immutable slots. Immutable slots in `W` are never written by any
remaining checked code, which is exactly what keeps the maps valid as execution proceeds. -/

/-- Validity of the available-expression table at a store: every entry `(e, w)` re-evaluates, from
any machine state, to exactly the value currently in slot `w`. -/
def AvailValid (funs : Funs) (σ : Store n) (avail : List (Rhs n × Fin n)) : Prop :=
  ∀ p ∈ avail, ∀ st, ExecRhs funs σ st p.1 (.ok [σ p.2] st)

/-- An atom whose slot references are immutable and already written. -/
def AtomRefs (imm : Fin n → Bool) (W : List (Fin n)) (a : Atom n) : Prop :=
  isImmAtom imm a = true ∧ ∀ s, atomSlot? a = some s → s ∈ W

/-- Structural anchoring of the maps in the written-set `W`. -/
def RefsOK (imm : Fin n → Bool) (W : List (Fin n)) (env : List (Fin n × Atom n))
    (avail : List (Rhs n × Fin n)) : Prop :=
  (∀ p ∈ env, imm p.1 = true ∧ p.1 ∈ W ∧ AtomRefs imm W p.2) ∧
  (∀ q ∈ avail, imm q.2 = true ∧ q.2 ∈ W ∧
    ∃ op args, q.1 = Rhs.builtin op args ∧ Op.isPure op = true ∧ ∀ a ∈ args, AtomRefs imm W a)

/-- The bundled value-numbering invariant at a store. -/
structure VNInv (funs : Funs) (imm : Fin n → Bool) (W : List (Fin n))
    (env : List (Fin n × Atom n)) (avail : List (Rhs n × Fin n)) (σ : Store n) : Prop where
  wImm : ∀ w ∈ W, imm w = true
  refs : RefsOK imm W env avail
  env_valid : EnvValid σ env
  avail_valid : AvailValid funs σ avail

/-- Slot list of an atom list. -/
theorem atomRefs_slots {imm : Fin n → Bool} {W : List (Fin n)} {args : List (Atom n)}
    (h : ∀ a ∈ args, AtomRefs imm W a) : ∀ i ∈ args.filterMap atomSlot?, i ∈ W := by
  intro i hi
  obtain ⟨a, ha, hsl⟩ := List.mem_filterMap.mp hi
  exact (h a ha).2 i hsl

/-- The invariant transports along a store change that agrees on `W` and a `W`-extension. -/
theorem VNInv.transport {funs : Funs} {imm : Fin n → Bool} {W W' : List (Fin n)}
    {env avail} {σ σ' : Store n} (h : VNInv funs imm W env avail σ)
    (hag : AgreeOn W σ σ') (hsub : ∀ w ∈ W, w ∈ W') (hwImm' : ∀ w ∈ W', imm w = true) :
    VNInv funs imm W' env avail σ' := by
  refine ⟨hwImm', ⟨fun p hp => ?_, fun q hq => ?_⟩, fun p hp => ?_, fun p hp st => ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := h.refs.1 p hp
    exact ⟨h1, hsub _ h2, h3, fun s hs => hsub _ (h4 s hs)⟩
  · obtain ⟨h1, h2, op, args, heq, hpure, hargs⟩ := h.refs.2 q hq
    exact ⟨h1, hsub _ h2, op, args, heq, hpure,
      fun a ha => ⟨(hargs a ha).1, fun s hs => hsub _ ((hargs a ha).2 s hs)⟩⟩
  · obtain ⟨-, hW, -, hsl⟩ := h.refs.1 p hp
    have hkey : σ' p.1 = σ p.1 := (hag _ hW).symm
    have hval : evalAtom σ' p.2 = evalAtom σ p.2 := by
      cases hpa : p.2 with
      | lit l => rfl
      | slot s => exact (hag s (hsl s (by rw [hpa]; rfl))).symm
    rw [hkey, hval]
    exact h.env_valid p hp
  · obtain ⟨-, hW, op, args, heq, -, hargs⟩ := h.refs.2 p hp
    have hv := h.avail_valid p hp st
    rw [heq] at hv ⊢
    cases hv with
    | builtin hb =>
        rw [map_evalAtom_agree hag (atomRefs_slots hargs), hag _ hW] at hb
        exact .builtin hb

/-! ### Checker facts: the written-set only grows, and stays immutable -/

/-- What the checker guarantees about its output set: it extends the input, and (given an immutable
input) contains only immutable slots. -/
def WGrows (imm : Fin n → Bool) (W W' : List (Fin n)) : Prop :=
  (∀ w ∈ W, w ∈ W') ∧ ((∀ w ∈ W, imm w = true) → ∀ w ∈ W', imm w = true)

theorem WGrows.rfl {imm : Fin n → Bool} {W : List (Fin n)} : WGrows imm W W :=
  ⟨fun _ h => h, fun h => h⟩

theorem WGrows.trans {imm : Fin n → Bool} {W₁ W₂ W₃ : List (Fin n)}
    (h₁ : WGrows imm W₁ W₂) (h₂ : WGrows imm W₂ W₃) : WGrows imm W₁ W₃ :=
  ⟨fun w hw => h₂.1 w (h₁.1 w hw), fun h => h₂.2 (h₁.2 h)⟩

theorem WGrows.append_filter {imm : Fin n → Bool} {W : List (Fin n)} (ds : List (Fin n)) :
    WGrows imm W (ds.filter imm ++ W) := by
  constructor
  · exact fun w hw => List.mem_append_right _ hw
  · intro h w hw
    rcases List.mem_append.mp hw with h1 | h2
    · exact List.of_mem_filter h1
    · exact h w h2

/-- The checker's written-set only grows (and stays immutable), across the whole mutual group. -/
theorem vnSafe_grows {imm : Fin n → Bool} (W : List (Fin n)) (b : Block n) :
    ∀ W', vnSafeBlock imm W b = some W' → WGrows imm W W' := by
  refine vnSafeBlock.induct imm
    (motive_1 := fun W s => ∀ W', vnSafeStmt imm W s = some W' → WGrows imm W W')
    (motive_2 := fun W df => ∀ W', vnSafeDflt imm W df = some W' → WGrows imm W W')
    (motive_3 := fun W b => ∀ W', vnSafeBlock imm W b = some W' → WGrows imm W W')
    (motive_4 := fun W cs => ∀ W', vnSafeCases imm W cs = some W' → WGrows imm W W')
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ W b
  case _ =>  -- assign, condition true
    intro W ds rhs hcond W' hsome
    rw [vnSafeStmt, if_pos hcond] at hsome
    exact Option.some.inj hsome ▸ WGrows.append_filter ds
  case _ =>  -- assign, condition false
    intro W ds rhs hcond W' hsome
    rw [vnSafeStmt, if_neg hcond] at hsome
    simp at hsome
  case _ =>  -- cond
    intro W c b ih W' hsome
    exact ih W' hsome
  case _ =>  -- switch, cases succeed
    intro W c cs df W₁ hcs ihcs ihdf W' hsome
    simp only [vnSafeStmt, hcs] at hsome
    exact WGrows.trans (ihcs W₁ hcs) (ihdf W' hsome)
  case _ =>  -- switch, cases fail
    intro W c cs df hcs ihcs W' hsome
    simp [vnSafeStmt, hcs] at hsome
  case _ =>  -- loop, body succeeds
    intro W post body W₁ hbody ihb ihp W' hsome
    simp only [vnSafeStmt, hbody] at hsome
    exact WGrows.trans (ihb W₁ hbody) (ihp W' hsome)
  case _ =>  -- loop, body fails
    intro W post body hbody ihb W' hsome
    simp [vnSafeStmt, hbody] at hsome
  case _ =>  -- other statements
    intro t W hna hnc hns hnl W' hsome
    cases t with
    | assign ds rhs => exact absurd rfl (hna ds rhs)
    | cond c b => exact absurd rfl (hnc c b)
    | switch c cs df => exact absurd rfl (hns c cs df)
    | loop post body => exact absurd rfl (hnl post body)
    | _ =>
        simp only [vnSafeStmt, Option.some.injEq] at hsome
        exact hsome ▸ WGrows.rfl
  case _ =>  -- block nil
    intro W W' hsome
    simp only [vnSafeBlock, Option.some.injEq] at hsome
    exact hsome ▸ WGrows.rfl
  case _ =>  -- block cons, stmt succeeds
    intro W s rest W₁ hs ihs ihrest W' hsome
    simp only [vnSafeBlock, hs] at hsome
    exact WGrows.trans (ihs W₁ hs) (ihrest W' hsome)
  case _ =>  -- block cons, stmt fails
    intro W s rest hs ihs W' hsome
    simp [vnSafeBlock, hs] at hsome
  case _ =>  -- cases nil
    intro W W' hsome
    simp only [vnSafeCases, Option.some.injEq] at hsome
    exact hsome ▸ WGrows.rfl
  case _ =>  -- cases cons, block succeeds
    intro W l b rest W₁ hb ihb ihrest W' hsome
    simp only [vnSafeCases, hb] at hsome
    exact WGrows.trans (ihb W₁ hb) (ihrest W' hsome)
  case _ =>  -- cases cons, block fails
    intro W l b rest hb ihb W' hsome
    simp [vnSafeCases, hb] at hsome
  case _ =>  -- dflt none
    intro W W' hsome
    simp only [vnSafeDflt, Option.some.injEq] at hsome
    exact hsome ▸ WGrows.rfl
  case _ =>  -- dflt some
    intro W b ih W' hsome
    exact ih W' hsome

/-! ### Resolution and the record conditions -/

/-- With immutable env keys, resolving preserves the immutability of an atom. -/
theorem resolve_imm_eq {imm : Fin n → Bool} {W} {env : List (Fin n × Atom n)} {avail}
    (href : RefsOK imm W env avail) (a : Atom n) :
    isImmAtom imm (resolveAtom env a) = isImmAtom imm a := by
  cases a with
  | lit l => rfl
  | slot s =>
      simp only [resolveAtom]
      cases hf : env.find? (fun p => p.1 == s) with
      | none => rfl
      | some p =>
          have hmem : p ∈ env := List.mem_of_find?_eq_some hf
          have hps : p.1 = s := by simpa using List.find?_some hf
          obtain ⟨h1, -, h3, -⟩ := href.1 p hmem
          show isImmAtom imm p.2 = isImmAtom imm (.slot s)
          rw [h3]
          simp [isImmAtom, ← hps, h1]

/-- Resolving an atom that is safe to record (a literal, or an immutable slot already in `W`)
yields an atom with anchored references. -/
theorem resolveAtom_refs {imm : Fin n → Bool} {W} {env : List (Fin n × Atom n)} {avail}
    (href : RefsOK imm W env avail) {a : Atom n}
    (ha : ∀ s, a = .slot s → imm s = true ∧ s ∈ W) : AtomRefs imm W (resolveAtom env a) := by
  cases a with
  | lit l => exact ⟨rfl, fun s hs => by simp [resolveAtom, atomSlot?] at hs⟩
  | slot s =>
      simp only [resolveAtom]
      cases hf : env.find? (fun p => p.1 == s) with
      | none =>
          obtain ⟨h1, h2⟩ := ha s rfl
          exact ⟨by simpa [isImmAtom] using h1, fun i hi => by
            simp only [atomSlot?, Option.some.injEq] at hi
            exact hi ▸ h2⟩
      | some p =>
          obtain ⟨-, -, h3, h4⟩ := href.1 p (List.mem_of_find?_eq_some hf)
          exact ⟨h3, h4⟩

/-- A resolved atom that `recordWrite` accepts (`isImmAtom` on the *resolved* form) has anchored
references, given the original passed the checker's rhs condition. -/
theorem resolveAtom_refs' {imm : Fin n → Bool} {W} {env : List (Fin n × Atom n)} {avail}
    (href : RefsOK imm W env avail) {a : Atom n}
    (himm : isImmAtom imm (resolveAtom env a) = true)
    (ha : ∀ s, a = .slot s → imm s = true → s ∈ W) : AtomRefs imm W (resolveAtom env a) := by
  cases a with
  | lit l => exact ⟨rfl, fun s hs => by simp [resolveAtom, atomSlot?] at hs⟩
  | slot s =>
      simp only [resolveAtom] at himm ⊢
      cases hf : env.find? (fun p => p.1 == s) with
      | none =>
          rw [hf] at himm
          exact ⟨himm, fun i hi => by
            simp only [atomSlot?, Option.some.injEq] at hi
            exact hi ▸ ha s rfl (by simpa [isImmAtom] using himm)⟩
      | some p =>
          obtain ⟨-, -, h3, h4⟩ := href.1 p (List.mem_of_find?_eq_some hf)
          exact ⟨h3, h4⟩

/-! ### Extending the invariant with a fresh entry -/

/-- Prepend a valid, anchored copy/constant entry. -/
theorem VNInv.consEnv {funs : Funs} {imm : Fin n → Bool} {W : List (Fin n)} {env avail}
    {σ : Store n} (h : VNInv funs imm W env avail σ) {d : Fin n} {a : Atom n}
    (himm : imm d = true) (hdW : d ∈ W) (har : AtomRefs imm W a)
    (hval : σ d = evalAtom σ a) : VNInv funs imm W ((d, a) :: env) avail σ := by
  refine ⟨h.wImm, ⟨fun p hp => ?_, h.refs.2⟩, fun p hp => ?_, h.avail_valid⟩
  · rcases List.mem_cons.mp hp with rfl | hmem
    · exact ⟨himm, hdW, har⟩
    · exact h.refs.1 p hmem
  · rcases List.mem_cons.mp hp with rfl | hmem
    · exact hval
    · exact h.env_valid p hmem

/-- Prepend a valid, anchored available-expression entry. -/
theorem VNInv.consAvail {funs : Funs} {imm : Fin n → Bool} {W : List (Fin n)} {env avail}
    {σ : Store n} (h : VNInv funs imm W env avail σ) {op} {args : List (Atom n)} {w : Fin n}
    (himm : imm w = true) (hwW : w ∈ W) (hpure : Op.isPure op = true)
    (hargs : ∀ a ∈ args, AtomRefs imm W a)
    (hval : ∀ st, ExecRhs funs σ st (.builtin op args) (.ok [σ w] st)) :
    VNInv funs imm W env ((Rhs.builtin op args, w) :: avail) σ := by
  refine ⟨h.wImm, ⟨h.refs.1, fun q hq => ?_⟩, h.env_valid, fun q hq st => ?_⟩
  · rcases List.mem_cons.mp hq with rfl | hmem
    · exact ⟨himm, hwW, op, args, rfl, hpure, hargs⟩
    · exact h.refs.2 q hmem
  · rcases List.mem_cons.mp hq with rfl | hmem
    · exact hval st
    · exact h.avail_valid q hmem st

/-! ### Conditional loop simulation -/

/-- One-directional conditional loop simulation: if body and post forward-simulate under the
invariant `P` (with `AgreeOn W` re-establishing it via `hP`), so does the whole loop. -/
theorem loop_imp_sim {funs : Funs} {P : Store n → Prop} {W : List (Fin n)}
    {postA postB bodyA bodyB : Block n}
    (hP : ∀ {σ σ' : Store n}, AgreeOn W σ σ' → P σ → P σ')
    (hbody : ∀ σ st σ' st' o, P σ → ExecBlock funs σ st bodyA σ' st' o →
        ExecBlock funs σ st bodyB σ' st' o ∧ AgreeOn W σ σ')
    (hpost : ∀ σ st σ' st' o, P σ → ExecBlock funs σ st postA σ' st' o →
        ExecBlock funs σ st postB σ' st' o ∧ AgreeOn W σ σ') :
    ∀ {σ : Store n} {st code res}, Step funs σ st code res → code = .loop postA bodyA → P σ →
      ∀ {σ' st' o}, res = .sres σ' st' o →
        Step funs σ st (.loop postB bodyB) (.sres σ' st' o) ∧ AgreeOn W σ σ' := by
  intro σ st code res h
  induction h with
  | loopBrk hb =>
      rintro hcode hp σ' st' o hres
      injection hcode with h1 h2; subst h1; subst h2
      injection hres with h3 h4 h5; subst h3; subst h4; subst h5
      obtain ⟨hb', hag⟩ := hbody _ _ _ _ _ hp hb
      exact ⟨.loopBrk hb', hag⟩
  | loopLeave hb =>
      rintro hcode hp σ' st' o hres
      injection hcode with h1 h2; subst h1; subst h2
      injection hres with h3 h4 h5; subst h3; subst h4; subst h5
      obtain ⟨hb', hag⟩ := hbody _ _ _ _ _ hp hb
      exact ⟨.loopLeave hb', hag⟩
  | loopHalt hb =>
      rintro hcode hp σ' st' o hres
      injection hcode with h1 h2; subst h1; subst h2
      injection hres with h3 h4 h5; subst h3; subst h4; subst h5
      obtain ⟨hb', hag⟩ := hbody _ _ _ _ _ hp hb
      exact ⟨.loopHalt hb', hag⟩
  | loopStep hb hob hp hl ihb ihp ihl =>
      rintro hcode hpσ σ' st' o hres
      injection hcode with h1 h2; subst h1; subst h2
      injection hres with h3 h4 h5; subst h3; subst h4; subst h5
      obtain ⟨hb', hag₁⟩ := hbody _ _ _ _ _ hpσ hb
      have hp₁ := hP hag₁ hpσ
      obtain ⟨hp', hag₂⟩ := hpost _ _ _ _ _ hp₁ hp
      have hp₂ := hP hag₂ hp₁
      obtain ⟨hl', hag₃⟩ := ihl @hP hbody hpost rfl hp₂ rfl
      exact ⟨.loopStep hb' hob hp' hl', (hag₁.trans hag₂).trans hag₃⟩
  | loopPostStop hb hob hp hne ihb ihp =>
      rintro hcode hpσ σ' st' o hres
      injection hcode with h1 h2; subst h1; subst h2
      injection hres with h3 h4 h5; subst h3; subst h4; subst h5
      obtain ⟨hb', hag₁⟩ := hbody _ _ _ _ _ hpσ hb
      have hp₁ := hP hag₁ hpσ
      obtain ⟨hp', hag₂⟩ := hpost _ _ _ _ _ hp₁ hp
      exact ⟨.loopPostStop hb' hob hp' hne, hag₁.trans hag₂⟩
  | _ => exact fun hcode => nomatch hcode


/-! ### The record step -/

/-- Extension of an atom's anchoring to a larger written-set. -/
theorem AtomRefs.mono {imm : Fin n → Bool} {W W' : List (Fin n)} (hsub : ∀ w ∈ W, w ∈ W')
    {a : Atom n} (h : AtomRefs imm W a) : AtomRefs imm W' a :=
  ⟨h.1, fun s hs => hsub s (h.2 s hs)⟩

/-- Reading the just-written slot. -/
theorem updMany_single_self (σ : Store n) (d : Fin n) (v : U256) :
    updMany σ [d] [v] d = v := by
  show upd σ d v d = v
  simp [upd]

/-- **What a single `recordWrite` does, semantically**: the emitted rhs executes exactly like the
original statement's rhs, and on normal completion the extended maps satisfy the invariant at the
updated store, with `d` joined into the written-set. -/
theorem recordWrite_sim {funs : Funs} {imm : Fin n → Bool} {W : List (Fin n)}
    {env avail} {σ : Store n} (hinv : VNInv funs imm W env avail σ)
    {d : Fin n} (himm : imm d = true) (hdW : d ∉ W)
    {rhs : Rhs n} (hsafe : vnSafeRhs imm W rhs = true)
    {env' avail' out}
    (hrec : recordWrite imm env avail d (resolveRhs env rhs) = (env', avail', out)) :
    (∀ st r, ExecRhs funs σ st out r ↔ ExecRhs funs σ st rhs r) ∧
    (∀ st vs st₁, ExecRhs funs σ st rhs (.ok vs st₁) →
      VNInv funs imm (d :: W) env' avail' (updMany σ [d] vs)) := by
  have hsub : ∀ w ∈ W, w ∈ (d :: W) := fun w hw => List.mem_cons_of_mem d hw
  have hwImm' : ∀ w ∈ (d :: W), imm w = true := by
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hmem
    · exact himm
    · exact hinv.wImm w hmem
  have hagAny : ∀ vs, AgreeOn W σ (updMany σ [d] vs) := by
    intro vs
    refine AgreeOn.updMany_out ?_ vs
    intro x hx
    rw [List.mem_singleton] at hx
    exact hx ▸ hdW
  have htrans : ∀ vs, VNInv funs imm (d :: W) env avail (updMany σ [d] vs) :=
    fun vs => hinv.transport (hagAny vs) hsub hwImm'
  unfold recordWrite at hrec
  rw [himm] at hrec
  simp only [Bool.not_true, Bool.false_eq_true, if_false] at hrec
  cases rhs with
  | atom a₀ =>
      simp only [resolveRhs] at hrec
      split at hrec
      · -- recorded copy/constant: env grows by (d, resolveAtom env a₀)
        next himm_a =>
        cases hrec
        constructor
        · intro st r; exact resolveRhs_exec (rhs := .atom a₀) hinv.env_valid
        · intro st vs st₁ hex
          have hex' : ExecRhs funs σ st (.atom (resolveAtom env a₀)) (.ok vs st₁) :=
            (resolveRhs_exec (rhs := .atom a₀) hinv.env_valid).mpr hex
          cases hex'
          have hsl : ∀ s, a₀ = .slot s → imm s = true → s ∈ W := by
            intro s hs himms
            subst hs
            simp only [vnSafeRhs, himms, Bool.not_true, Bool.false_or] at hsafe
            rwa [List.contains_eq_mem, decide_eq_true_eq] at hsafe
          have harW := resolveAtom_refs' hinv.refs himm_a hsl
          refine (htrans _).consEnv himm (List.mem_cons_self ..) (harW.mono hsub) ?_
          rw [updMany_single_self]
          exact evalAtom_agree (hagAny _) (fun i hi => harW.2 i hi)
      · -- unrecorded atom: maps unchanged
        cases hrec
        exact ⟨fun st r => resolveRhs_exec (rhs := .atom a₀) hinv.env_valid,
          fun st vs st₁ _ => htrans vs⟩
  | builtin op args₀ =>
      simp only [resolveRhs] at hrec
      split at hrec
      · next hcond =>
        obtain ⟨hpure, hallres⟩ := Bool.and_eq_true_iff.mp hcond
        have hallorig : ∀ a ∈ args₀, isImmAtom imm a = true := by
          intro a ha
          have := List.all_eq_true.mp (by simpa only [List.all_map] using hallres) a ha
          rwa [Function.comp, resolve_imm_eq hinv.refs] at this
        have hcondorig : (Op.isPure op && args₀.all (isImmAtom imm)) = true :=
          Bool.and_eq_true_iff.mpr ⟨hpure, List.all_eq_true.mpr hallorig⟩
        rw [vnSafeRhs, hcondorig, Bool.not_true, Bool.false_or] at hsafe
        obtain ⟨hsafeW, hprobe⟩ := Bool.and_eq_true_iff.mp hsafe
        have hargrefs : ∀ a ∈ args₀.map (resolveAtom env), AtomRefs imm W a := by
          intro a ha
          obtain ⟨a₀', ha₀, rfl⟩ := List.mem_map.mp ha
          refine resolveAtom_refs hinv.refs ?_
          intro s hs
          subst hs
          refine ⟨by simpa [isImmAtom] using hallorig _ ha₀, ?_⟩
          have hc := List.all_eq_true.mp hsafeW _ ha₀
          simp only at hc
          rwa [List.contains_eq_mem, decide_eq_true_eq] at hc
        split at hrec
        · -- CSE hit: copy the earlier result
          next e w hfind =>
          cases hrec
          have hmem := List.mem_of_find?_eq_some hfind
          have hkey : e = Rhs.builtin op (args₀.map (resolveAtom env)) :=
            rhs_eq_of_beq (by simpa using List.find?_some hfind)
          obtain ⟨himmw, hwW, -⟩ := hinv.refs.2 (e, w) hmem
          have hav : ∀ st, ExecRhs funs σ st
              (.builtin op (args₀.map (resolveAtom env))) (.ok [σ w] st) :=
            fun st => hkey ▸ hinv.avail_valid (e, w) hmem st
          constructor
          · intro st r
            constructor
            · intro hout
              cases hout
              exact (resolveRhs_exec (rhs := .builtin op args₀) hinv.env_valid).mp (hav st)
            · intro horig
              have h' := (resolveRhs_exec (rhs := .builtin op args₀) hinv.env_valid).mpr horig
              cases h' with
              | builtin hb =>
                  cases hav st with
                  | builtin hb₀ =>
                      rw [builtin_det hb hb₀]
                      exact Step.atom
          · intro st vs st₁ hex
            have h' := (resolveRhs_exec (rhs := .builtin op args₀) hinv.env_valid).mpr hex
            cases h' with
            | builtin hb =>
                cases hav st with
                | builtin hb₀ =>
                    have heq := builtin_det hb hb₀
                    injection heq with h1 h2
                    subst h1
                    subst h2
                    refine (htrans _).consEnv himm (List.mem_cons_self ..) ⟨?_, ?_⟩ ?_
                    · simpa [isImmAtom] using himmw
                    · intro s hs
                      simp only [atomSlot?, Option.some.injEq] at hs
                      exact hs ▸ hsub w hwW
                    · rw [updMany_single_self]
                      exact hagAny _ w hwW
        · -- CSE miss: memoise into avail
          next hfind =>
          cases hrec
          constructor
          · intro st r; exact resolveRhs_exec (rhs := .builtin op args₀) hinv.env_valid
          · intro st vs st₁ hex
            have h' := (resolveRhs_exec (rhs := .builtin op args₀) hinv.env_valid).mpr hex
            cases h' with
            | builtin hb =>
                obtain ⟨outs, houts⟩ := pure_builtin_ok hpure hb
                injection houts with h1 h2
                subst h2
                obtain ⟨v, rfl⟩ := pure_ok_single (st := st₁) hpure
                  (by simpa only [List.length_map] using hprobe) hb
                refine (htrans _).consAvail himm (List.mem_cons_self ..) hpure
                  (fun a ha => (hargrefs a ha).mono hsub) ?_
                intro st''
                have hmapeq : (args₀.map (resolveAtom env)).map (evalAtom (updMany σ [d] [v]))
                    = (args₀.map (resolveAtom env)).map (evalAtom σ) :=
                  (map_evalAtom_agree (hagAny _) (atomRefs_slots hargrefs)).symm
                refine Step.builtin ?_
                rw [hmapeq, updMany_single_self]
                exact pure_st_indep hpure hb st''
      · -- unrecorded builtin
        cases hrec
        exact ⟨fun st r => resolveRhs_exec (rhs := .builtin op args₀) hinv.env_valid,
          fun st vs st₁ _ => htrans vs⟩
  | call fn args₀ =>
      simp only [resolveRhs] at hrec
      cases hrec
      exact ⟨fun st r => resolveRhs_exec (rhs := .call fn args₀) hinv.env_valid,
        fun st vs st₁ _ => htrans vs⟩

/-! ### The main simulation -/

/-- Conditional block simulation at a written-set: from any invariant store the transformed and
original blocks execute identically (same store, state, outcome), and execution of the original
establishes agreement on `W`. -/
def SimAt (funs : Funs) (imm : Fin n → Bool) (env : List (Fin n × Atom n))
    (avail : List (Rhs n × Fin n)) (W : List (Fin n)) (b' b : Block n) : Prop :=
  ∀ σ : Store n, VNInv funs imm W env avail σ →
    ∀ st σ' st' o,
      (ExecBlock funs σ st b' σ' st' o ↔ ExecBlock funs σ st b σ' st' o) ∧
      (ExecBlock funs σ st b σ' st' o → AgreeOn W σ σ')

/-- A simulation at a larger written-set restricts to a smaller one. -/
theorem SimAt.anti {funs : Funs} {imm : Fin n → Bool} {env avail} {W W₂ : List (Fin n)}
    {b' b : Block n} (hg : WGrows imm W W₂)
    (h : SimAt funs imm env avail W₂ b' b) : SimAt funs imm env avail W b' b := by
  intro σ hinv st σ' st' o
  have hinv₂ : VNInv funs imm W₂ env avail σ :=
    hinv.transport (fun i _ => rfl) hg.1 (hg.2 hinv.wImm)
  obtain ⟨hiff, hag⟩ := h σ hinv₂ st σ' st' o
  exact ⟨hiff, fun hex i hi => hag hex i (hg.1 i hi)⟩

/-- Checker growth for a single statement (wrapper around the block form). -/
theorem vnSafe_grows_stmt {imm : Fin n → Bool} {W W' : List (Fin n)} {s : Stmt n}
    (h : vnSafeStmt imm W s = some W') : WGrows imm W W' :=
  vnSafe_grows W [s] W' (by simp [vnSafeBlock, h])

theorem vnSafe_grows_cases {imm : Fin n → Bool} {W W' : List (Fin n)}
    {cs : List (Literal × Block n)} (h : vnSafeCases imm W cs = some W') : WGrows imm W W' :=
  vnSafe_grows_stmt (s := .switch (.lit (.number 0)) cs none)
    (by simp [vnSafeStmt, h, vnSafeDflt])

theorem vnSafe_grows_dflt {imm : Fin n → Bool} {W W' : List (Fin n)}
    {df : Option (Block n)} (h : vnSafeDflt imm W df = some W') : WGrows imm W W' := by
  cases df with
  | none =>
      obtain rfl : W = W' := by simpa [vnSafeDflt] using h
      exact WGrows.rfl
  | some b => exact vnSafe_grows W b W' h

/-- `selectCase` respects any pointwise relation on the case blocks and default. -/
theorem selectCase_rel {R : Block n → Block n → Prop} {cv : U256}
    {cs₁ cs₂ : List (Literal × Block n)} {df₁ df₂ : Option (Block n)}
    (hcs : List.Forall₂ (fun p q => p.1 = q.1 ∧ R p.2 q.2) cs₁ cs₂)
    (hdf : R (df₁.getD []) (df₂.getD [])) :
    R (selectCase cv cs₁ df₁) (selectCase cv cs₂ df₂) := by
  induction hcs with
  | nil => simpa only [selectCase, List.find?_nil] using hdf
  | @cons p q cs₁' cs₂' hpq _ ih =>
      obtain ⟨hlabel, hblk⟩ := hpq
      unfold selectCase
      by_cases hm : (litValue p.1 == cv) = true
      · have hmq : (litValue q.1 == cv) = true := by rw [← hlabel]; exact hm
        rw [List.find?_cons_of_pos (by simpa using hm), List.find?_cons_of_pos (by simpa using hmq)]
        exact hblk
      · have hmq : ¬ (litValue q.1 == cv) = true := by rw [← hlabel]; exact hm
        rw [List.find?_cons_of_neg (by simpa using hm), List.find?_cons_of_neg (by simpa using hmq)]
        exact ih

/-- **The value-numbering simulation.** On a checker-accepted block, from any invariant store the
transformed block executes exactly like the original — same final store, machine state and outcome —
and execution establishes agreement on the written-set. Proved by functional induction on the pass,
with the statement motive additionally re-establishing the invariant (at the extended maps and
written-set) after every normal step. -/
theorem vn_sim {funs : Funs} {imm : Fin n → Bool} (env : List (Fin n × Atom n))
    (avail : List (Rhs n × Fin n)) (b : Block n) :
    ∀ W W', vnSafeBlock imm W b = some W' →
      SimAt funs imm env avail W (vnBlock imm env avail b) b := by
  refine vnBlock.induct imm
    (motive_1 := fun env avail s => ∀ W W', vnSafeStmt imm W s = some W' →
      ∀ σ : Store n, VNInv funs imm W env avail σ →
        ∀ s' env' avail', vnStmt imm env avail s = (s', env', avail') →
          ∀ st σ' st' o,
            (ExecStmt funs σ st s' σ' st' o ↔ ExecStmt funs σ st s σ' st' o) ∧
            (ExecStmt funs σ st s σ' st' o → AgreeOn W σ σ' ∧
              (o = .normal → VNInv funs imm W' env' avail' σ')))
    (motive_2 := fun env avail df => ∀ W W', vnSafeDflt imm W df = some W' →
      SimAt funs imm env avail W ((vnDflt imm env avail df).getD []) (df.getD []))
    (motive_3 := fun env avail b => ∀ W W', vnSafeBlock imm W b = some W' →
      SimAt funs imm env avail W (vnBlock imm env avail b) b)
    (motive_4 := fun env avail cs => ∀ W W₁, vnSafeCases imm W cs = some W₁ →
      List.Forall₂ (fun p q => p.1 = q.1 ∧ SimAt funs imm env avail W p.2 q.2)
        (vnCases imm env avail cs) cs)
    ?assign1 ?assignN ?cond ?switch ?loop ?stmt ?bnil ?bcons ?cnil ?ccons ?dnone ?dsome env avail b
  case assign1 =>
    intro env avail d rhs env' avail' out hrec W W' hchk σ hinv s'' env'' avail'' hvn
    rw [vnStmt] at hvn
    rw [hrec] at hvn
    cases hvn
    rw [vnSafeStmt] at hchk
    split at hchk
    case isFalse => simp at hchk
    case isTrue hcond =>
    obtain rfl := Option.some.inj hchk
    obtain ⟨hdst, hdsts⟩ := Bool.and_eq_true_iff.mp hcond
    intro st σ' st' o
    by_cases himm : imm d = true
    · -- recording destination
      have hdW : d ∉ W := by
        have hall := List.all_eq_true.mp hdst d (List.mem_singleton_self d)
        simp only [himm, Bool.not_true, Bool.false_or, Bool.not_eq_true'] at hall
        intro hmem
        rw [List.contains_eq_mem, decide_eq_false_iff_not] at hall
        exact hall hmem
      have hsafe : vnSafeRhs imm W rhs = true := by
        simpa only [vnSafeDsts, himm, Bool.not_true, Bool.false_or] using hdsts
      obtain ⟨hexec, hpost⟩ := recordWrite_sim hinv himm hdW hsafe hrec
      refine ⟨?_, ?_⟩
      · constructor
        · intro h
          cases h with
          | assignOk hr => exact .assignOk ((hexec _ _).mp hr)
          | assignHalt hr => exact .assignHalt ((hexec _ _).mp hr)
        · intro h
          cases h with
          | assignOk hr => exact .assignOk ((hexec _ _).mpr hr)
          | assignHalt hr => exact .assignHalt ((hexec _ _).mpr hr)
      · intro h
        cases h with
        | assignOk hr =>
            refine ⟨?_, fun _ => ?_⟩
            · refine AgreeOn.updMany_out ?_ _
              intro x hx
              rw [List.mem_singleton] at hx
              exact hx ▸ hdW
            · simpa [List.filter, himm] using hpost _ _ _ hr
        | assignHalt hr => exact ⟨fun i _ => rfl, fun hno => nomatch hno⟩
    · -- non-recording destination: maps unchanged
      have himmF : imm d = false := Bool.not_eq_true _ ▸ (by simpa using himm)
      have hrec' : env' = env ∧ avail' = avail ∧ out = resolveRhs env rhs := by
        unfold recordWrite at hrec
        rw [himmF] at hrec
        simp only [Bool.not_false, if_true] at hrec
        exact ⟨(Prod.mk.injEq ..).mp hrec |>.1.symm,
          ((Prod.mk.injEq ..).mp ((Prod.mk.injEq ..).mp hrec).2).1.symm,
          ((Prod.mk.injEq ..).mp ((Prod.mk.injEq ..).mp hrec).2).2.symm⟩
      obtain ⟨rfl, rfl, rfl⟩ := hrec'
      have hdW : d ∉ W := fun hmem => himm (hinv.wImm d hmem)
      refine ⟨?_, ?_⟩
      · constructor
        · intro h
          cases h with
          | assignOk hr => exact .assignOk ((resolveRhs_exec (rhs := rhs) hinv.env_valid).mp hr)
          | assignHalt hr =>
              exact .assignHalt ((resolveRhs_exec (rhs := rhs) hinv.env_valid).mp hr)
        · intro h
          cases h with
          | assignOk hr => exact .assignOk ((resolveRhs_exec (rhs := rhs) hinv.env_valid).mpr hr)
          | assignHalt hr =>
              exact .assignHalt ((resolveRhs_exec (rhs := rhs) hinv.env_valid).mpr hr)
      · intro h
        cases h with
        | @assignOk _ _ _ _ _ vs st₁ hr =>
            have hag : AgreeOn W σ (updMany σ [d] vs) := by
              refine AgreeOn.updMany_out ?_ _
              intro x hx
              rw [List.mem_singleton] at hx
              exact hx ▸ hdW
            refine ⟨hag, fun _ => ?_⟩
            have : List.filter imm [d] ++ W = W := by simp [List.filter, himmF]
            rw [this]
            exact hinv.transport hag (fun _ h => h) hinv.wImm
        | assignHalt hr => exact ⟨fun i _ => rfl, fun hno => nomatch hno⟩
  case assignN =>
    intro env avail ds rhs hne W W' hchk σ hinv s'' env'' avail'' hvn
    rw [vnStmt.eq_2 imm env avail ds rhs hne] at hvn
    cases hvn
    rw [vnSafeStmt] at hchk
    split at hchk
    case isFalse => simp at hchk
    case isTrue hcond =>
    obtain rfl := Option.some.inj hchk
    obtain ⟨hdst, -⟩ := Bool.and_eq_true_iff.mp hcond
    intro st σ' st' o
    have hds : ∀ d₀ ∈ ds, d₀ ∉ W := by
      intro d₀ hd₀ hmem
      have hall := List.all_eq_true.mp hdst d₀ hd₀
      have himmw := hinv.wImm d₀ hmem
      simp only [himmw, Bool.not_true, Bool.false_or, Bool.not_eq_true'] at hall
      rw [List.contains_eq_mem, decide_eq_false_iff_not] at hall
      exact hall hmem
    refine ⟨?_, ?_⟩
    · constructor
      · intro h
        cases h with
        | assignOk hr => exact .assignOk ((resolveRhs_exec (rhs := rhs) hinv.env_valid).mp hr)
        | assignHalt hr =>
            exact .assignHalt ((resolveRhs_exec (rhs := rhs) hinv.env_valid).mp hr)
      · intro h
        cases h with
        | assignOk hr => exact .assignOk ((resolveRhs_exec (rhs := rhs) hinv.env_valid).mpr hr)
        | assignHalt hr =>
            exact .assignHalt ((resolveRhs_exec (rhs := rhs) hinv.env_valid).mpr hr)
    · intro h
      cases h with
      | @assignOk _ _ _ _ _ vs st₁ hr =>
          have hag : AgreeOn W σ (updMany σ ds vs) := AgreeOn.updMany_out hds _
          exact ⟨hag, fun _ => hinv.transport hag (WGrows.append_filter ds).1
            ((WGrows.append_filter ds).2 hinv.wImm)⟩
      | assignHalt hr => exact ⟨fun i _ => rfl, fun hno => nomatch hno⟩
  case cond =>
    intro env avail c b ihb W W' hchk σ hinv s'' env'' avail'' hvn
    rw [vnStmt] at hvn
    cases hvn
    rw [vnSafeStmt] at hchk
    have hg := vnSafe_grows W b W' hchk
    have hsim := ihb W W' hchk σ hinv
    intro st σ' st' o
    refine ⟨?_, ?_⟩
    · constructor
      · intro h
        cases h with
        | condFalse hc =>
            refine .condFalse ?_
            rwa [resolveAtom_sound hinv.env_valid] at hc
        | condTrue hc hb =>
            refine .condTrue ?_ ((hsim st σ' st' o).1.mp hb)
            rwa [resolveAtom_sound hinv.env_valid] at hc
      · intro h
        cases h with
        | condFalse hc =>
            refine .condFalse ?_
            rwa [resolveAtom_sound hinv.env_valid]
        | condTrue hc hb =>
            refine .condTrue ?_ ((hsim st σ' st' o).1.mpr hb)
            rwa [resolveAtom_sound hinv.env_valid]
    · intro h
      cases h with
      | condFalse hc =>
          exact ⟨fun i _ => rfl, fun _ =>
            hinv.transport (fun i _ => rfl) hg.1 (hg.2 hinv.wImm)⟩
      | condTrue hc hb =>
          have hag := (hsim st σ' st' o).2 hb
          exact ⟨hag, fun _ => hinv.transport hag hg.1 (hg.2 hinv.wImm)⟩
  case switch =>
    intro env avail c cs df ihcs ihdf W W' hchk σ hinv s'' env'' avail'' hvn
    rw [vnStmt] at hvn
    cases hvn
    rw [vnSafeStmt] at hchk
    split at hchk
    case h_2 => simp at hchk
    case h_1 W₁ hcs =>
    have hg₁ := vnSafe_grows_cases hcs
    have hg₂ := vnSafe_grows_dflt hchk
    have hsel : SimAt funs imm env avail W
        (selectCase (evalAtom σ c) (vnCases imm env avail cs) (vnDflt imm env avail df))
        (selectCase (evalAtom σ c) cs df) :=
      selectCase_rel (ihcs W W₁ hcs) ((ihdf W₁ W' hchk).anti hg₁)
    intro st σ' st' o
    refine ⟨?_, ?_⟩
    · constructor
      · intro h
        cases h with
        | switch hs =>
            refine .switch ?_
            rw [resolveAtom_sound hinv.env_valid] at hs
            exact (hsel σ hinv st σ' st' o).1.mp hs
      · intro h
        cases h with
        | switch hs =>
            refine .switch ?_
            rw [resolveAtom_sound hinv.env_valid]
            exact (hsel σ hinv st σ' st' o).1.mpr hs
    · intro h
      cases h with
      | switch hs =>
          have hag := (hsel σ hinv st σ' st' o).2 hs
          exact ⟨hag, fun _ => hinv.transport hag (hg₁.trans hg₂).1
            ((hg₁.trans hg₂).2 hinv.wImm)⟩
  case loop =>
    intro env avail post body ihp ihb W W' hchk σ hinv s'' env'' avail'' hvn
    rw [vnStmt] at hvn
    cases hvn
    rw [vnSafeStmt] at hchk
    split at hchk
    case h_2 => simp at hchk
    case h_1 W₁ hbody =>
    have hgb := vnSafe_grows W body W₁ hbody
    have hgp := vnSafe_grows W₁ post W' hchk
    have hbodySim := ihb W W₁ hbody
    have hpostSim := (ihp W₁ W' hchk).anti hgb
    have hP : ∀ {σ₁ σ₂ : Store n}, AgreeOn W σ₁ σ₂ →
        VNInv funs imm W env avail σ₁ → VNInv funs imm W env avail σ₂ :=
      fun hag hi => hi.transport hag (fun _ h => h) hi.wImm
    have hbodyF : ∀ σ₁ st₁ σ₂ st₂ o₁, VNInv funs imm W env avail σ₁ →
        ExecBlock funs σ₁ st₁ body σ₂ st₂ o₁ →
        ExecBlock funs σ₁ st₁ (vnBlock imm env avail body) σ₂ st₂ o₁ ∧ AgreeOn W σ₁ σ₂ :=
      fun σ₁ st₁ σ₂ st₂ o₁ hi hex =>
        ⟨(hbodySim σ₁ hi st₁ σ₂ st₂ o₁).1.mpr hex, (hbodySim σ₁ hi st₁ σ₂ st₂ o₁).2 hex⟩
    have hpostF : ∀ σ₁ st₁ σ₂ st₂ o₁, VNInv funs imm W env avail σ₁ →
        ExecBlock funs σ₁ st₁ post σ₂ st₂ o₁ →
        ExecBlock funs σ₁ st₁ (vnBlock imm env avail post) σ₂ st₂ o₁ ∧ AgreeOn W σ₁ σ₂ :=
      fun σ₁ st₁ σ₂ st₂ o₁ hi hex =>
        ⟨(hpostSim σ₁ hi st₁ σ₂ st₂ o₁).1.mpr hex, (hpostSim σ₁ hi st₁ σ₂ st₂ o₁).2 hex⟩
    have hbodyR : ∀ σ₁ st₁ σ₂ st₂ o₁, VNInv funs imm W env avail σ₁ →
        ExecBlock funs σ₁ st₁ (vnBlock imm env avail body) σ₂ st₂ o₁ →
        ExecBlock funs σ₁ st₁ body σ₂ st₂ o₁ ∧ AgreeOn W σ₁ σ₂ :=
      fun σ₁ st₁ σ₂ st₂ o₁ hi hex =>
        have horig := (hbodySim σ₁ hi st₁ σ₂ st₂ o₁).1.mp hex
        ⟨horig, (hbodySim σ₁ hi st₁ σ₂ st₂ o₁).2 horig⟩
    have hpostR : ∀ σ₁ st₁ σ₂ st₂ o₁, VNInv funs imm W env avail σ₁ →
        ExecBlock funs σ₁ st₁ (vnBlock imm env avail post) σ₂ st₂ o₁ →
        ExecBlock funs σ₁ st₁ post σ₂ st₂ o₁ ∧ AgreeOn W σ₁ σ₂ :=
      fun σ₁ st₁ σ₂ st₂ o₁ hi hex =>
        have horig := (hpostSim σ₁ hi st₁ σ₂ st₂ o₁).1.mp hex
        ⟨horig, (hpostSim σ₁ hi st₁ σ₂ st₂ o₁).2 horig⟩
    intro st σ' st' o
    refine ⟨?_, ?_⟩
    · constructor
      · intro h
        cases h with
        | loopS hl => exact .loopS (loop_imp_sim @hP hbodyR hpostR hl rfl hinv rfl).1
      · intro h
        cases h with
        | loopS hl => exact .loopS (loop_imp_sim @hP hbodyF hpostF hl rfl hinv rfl).1
    · intro h
      cases h with
      | loopS hl =>
          have hag := (loop_imp_sim @hP hbodyF hpostF hl rfl hinv rfl).2
          exact ⟨hag, fun _ => hinv.transport hag (hgb.trans hgp).1
            ((hgb.trans hgp).2 hinv.wImm)⟩
  case stmt =>
    intro env avail s hna1 hna2 hnc hns hnl W W' hchk σ hinv s'' env'' avail'' hvn
    cases s with
    | assign ds rhs => exact absurd rfl (hna2 ds rhs)
    | cond c b => exact absurd rfl (hnc c b)
    | switch c cs df => exact absurd rfl (hns c cs df)
    | loop post body => exact absurd rfl (hnl post body)
    | «break» =>
        rw [show vnStmt imm env avail .«break» = (.«break», env, avail) from rfl] at hvn
        cases hvn
        obtain rfl := Option.some.inj
          (show some W = some W' from by rw [← hchk]; rfl)
        intro st σ' st' o
        refine ⟨Iff.rfl, ?_⟩
        intro h
        cases h
        exact ⟨fun i _ => rfl, fun hno => nomatch hno⟩
    | «continue» =>
        rw [show vnStmt imm env avail .«continue» = (.«continue», env, avail) from rfl] at hvn
        cases hvn
        obtain rfl := Option.some.inj
          (show some W = some W' from by rw [← hchk]; rfl)
        intro st σ' st' o
        refine ⟨Iff.rfl, ?_⟩
        intro h
        cases h
        exact ⟨fun i _ => rfl, fun hno => nomatch hno⟩
    | leave =>
        rw [show vnStmt imm env avail .leave = (.leave, env, avail) from rfl] at hvn
        cases hvn
        obtain rfl := Option.some.inj
          (show some W = some W' from by rw [← hchk]; rfl)
        intro st σ' st' o
        refine ⟨Iff.rfl, ?_⟩
        intro h
        cases h
        exact ⟨fun i _ => rfl, fun hno => nomatch hno⟩
  case bnil =>
    intro env avail W W' hchk σ hinv st σ' st' o
    refine ⟨Iff.rfl, ?_⟩
    intro h
    cases h
    exact fun i _ => rfl
  case bcons =>
    intro env avail s rest s' env' avail' hvnstmt ih1 ih3 W W' hchk σ hinv st σ' st' o
    rw [vnSafeBlock] at hchk
    split at hchk
    case h_2 => simp at hchk
    case h_1 W₂ hs =>
    have hstmt := ih1 W W₂ hs σ hinv s' env' avail' hvnstmt
    have hgs := vnSafe_grows_stmt hs
    have hblock : vnBlock imm env avail (s :: rest) = s' :: vnBlock imm env' avail' rest := by
      rw [vnBlock, hvnstmt]
    rw [hblock]
    refine ⟨?_, ?_⟩
    · constructor
      · intro h
        cases h with
        | consNormal h1 h2 =>
            have ho := (hstmt _ _ _ _).1.mp h1
            have hinv₂ := ((hstmt _ _ _ _).2 ho).2 rfl
            exact .consNormal ho ((ih3 W₂ W' hchk _ hinv₂ _ _ _ _).1.mp h2)
        | consStop h1 hne => exact .consStop ((hstmt _ _ _ _).1.mp h1) hne
      · intro h
        cases h with
        | consNormal h1 h2 =>
            have hinv₂ := ((hstmt _ _ _ _).2 h1).2 rfl
            exact .consNormal ((hstmt _ _ _ _).1.mpr h1)
              ((ih3 W₂ W' hchk _ hinv₂ _ _ _ _).1.mpr h2)
        | consStop h1 hne => exact .consStop ((hstmt _ _ _ _).1.mpr h1) hne
    · intro h
      cases h with
      | consNormal h1 h2 =>
          obtain ⟨hag₁, hpi⟩ := (hstmt _ _ _ _).2 h1
          have hinv₂ := hpi rfl
          have hag₂ := (ih3 W₂ W' hchk _ hinv₂ _ _ _ _).2 h2
          exact hag₁.trans (fun i hi => hag₂ i (hgs.1 i hi))
      | consStop h1 hne => exact ((hstmt _ _ _ _).2 h1).1
  case cnil =>
    intro env avail W W₁ hchk
    exact List.Forall₂.nil
  case ccons =>
    intro env avail l b rest ihb ihrest W W₁ hchk
    rw [vnSafeCases] at hchk
    split at hchk
    case h_2 => simp at hchk
    case h_1 W₂ hb =>
    have hg := vnSafe_grows W b W₂ hb
    refine List.Forall₂.cons ⟨rfl, ihb W W₂ hb⟩ ?_
    exact (ihrest W₂ W₁ hchk).imp (fun {p q} hpq => ⟨hpq.1, hpq.2.anti hg⟩)
  case dnone =>
    intro env avail W W' hchk σ hinv st σ' st' o
    refine ⟨Iff.rfl, ?_⟩
    intro h
    cases h
    exact fun i _ => rfl
  case dsome =>
    intro env avail b ih W W' hchk σ hinv st σ' st' o
    exact ih W W' hchk σ hinv st σ' st' o

/-! ### Capstones -/

/-- The initial invariant: empty maps are valid at every store, under any immutable seed set. -/
theorem VNInv.init (funs : Funs) (imm : Fin n → Bool) (W₀ : List (Fin n))
    (hW : ∀ w ∈ W₀, imm w = true) (σ : Store n) : VNInv funs imm W₀ [] [] σ where
  wImm := hW
  refs := ⟨List.forall_mem_nil _, List.forall_mem_nil _⟩
  env_valid := List.forall_mem_nil _
  avail_valid := List.forall_mem_nil _

/-- **Checked value numbering is sound**: on a checker-accepted body, `valueNumber` (constant/copy
propagation + CSE) preserves the big-step semantics exactly. -/
theorem valueNumber_equiv {funs : Funs} {frozen : List (Fin n)} {b : Block n}
    (h : vnSafe frozen b = true) : EquivBlock funs (valueNumber frozen b) b := by
  unfold vnSafe at h
  obtain ⟨W', hW'⟩ := Option.isSome_iff_exists.mp h
  intro σ st σ' st' o
  exact (vn_sim [] [] b _ W' hW'
    σ (VNInv.init funs _ _ (fun w hw => List.of_mem_filter hw) σ) st σ' st' o).1

/-- **The guarded pass is unconditionally sound**: `valueNumberChecked` runs the pass only when the
checker accepts, so it preserves semantics on every block. -/
theorem valueNumberChecked_equiv (funs : Funs) (frozen : List (Fin n)) (b : Block n) :
    EquivBlock funs (valueNumberChecked frozen b) b := by
  unfold valueNumberChecked
  split
  · exact valueNumber_equiv (by assumption)
  · exact EquivBlock.refl funs b

/-- **Whole-program soundness of checked value numbering**: applying it (with each function's
params+returns frozen) to every body of the table yields a program with identical runs. -/
theorem valueNumber_program_run (p : Program) {st st' o} :
    Run p st st' o ↔
      Run ⟨mapBodiesFuns (fun fd b => valueNumberChecked (fd.params ++ fd.rets) b) p.functions⟩
        st st' o :=
  run_mapBodies _ (fun F fd => valueNumberChecked_equiv F (fd.params ++ fd.rets) fd.body)
