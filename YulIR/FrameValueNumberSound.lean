import YulIR.FramePasses
import YulIR.FrameDceSound

set_option warningAsError true
/-!
# YulIR.FrameValueNumberSound — soundness of `valueNumber`

`valueNumber` is constant/copy propagation + common-subexpression elimination. Unlike the other
passes it carries an *environment* (`env : slot ↦ atom`, `avail : expr ↦ slot`), so its correctness
is a **store-relative** invariant threaded through the block simulation: the maps are only valid
against a particular store, and stay valid because the pass only ever records *immutable*
(written-at-most-once) slots whose defining write has already happened (read-after-write).

This file builds the groundwork — the environment-validity invariant and the fact that resolving
an rhs through a valid environment preserves its evaluation.
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

