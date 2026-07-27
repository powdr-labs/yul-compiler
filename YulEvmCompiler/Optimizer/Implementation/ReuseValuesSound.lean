import YulEvmCompiler.Optimizer.Implementation.ReuseValues
import YulEvmCompiler.Optimizer.Implementation.StorageForwardSound
import YulEvmCompiler.Optimizer.Implementation.MemorySpillStateSound
set_option warningAsError true
/-!
# Soundness of scoped available-value reuse

The simulation carries `RvOk`: every cached fact's denotation holds in the
current environment and machine state.

* pure and alias facts speak only about `V` (via the functional evaluator
  `evalPure` over the canonical pure fragment);
* cell facts additionally claim the 32-byte word at their literal address
  and that the word is already inside active memory (so replaying the load
  is state-preserving);
* keccak facts are content-keyed: they claim the hash *of the recorded
  content signature's values* — independent of current memory — plus range
  activity;
* storage-read facts claim the current storage word at their canonical key.

Rewritten right-hand sides evaluate to identical results in identical
states, so the transported derivation has the *same* result as the source
(no result relation is needed) — the induction mirrors
`StorageForwardSound` with the richer invariant.
-/

namespace YulEvmCompiler.Optimizer.ReuseValues

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler.Optimizer (pureTotalArity pureFn pureFn_builtin
  pureFn_builtin_inv pureTotalArity_pureFn storageLayoutFreeStmts
  blockDecls stmtsNoNormal)

variable {calls : ExternalCalls} {creates : ExternalCreates}
local notation "D" => evmWithExternal calls creates

/-! ### A functional evaluator for the canonical pure fragment -/

mutual
/-- Evaluate a canonical pure expression against an environment: literal
numbers, variables, and total pure builtins only. State-independent. -/
def evalPure (V : VEnv D) : Expr Op → Option U256
  | .lit (.number n) => some (Dialect.litValue D (.number n))
  | .lit _ => none
  | .var x => VEnv.get V x
  | .builtin op args =>
      if pureTotalArity op = some args.length then
        (evalPureArgs V args).bind (pureFn op)
      else none
  | .call _ _ => none

def evalPureArgs (V : VEnv D) : List (Expr Op) → Option (List U256)
  | [] => some []
  | e :: rest => do pure ((← evalPure V e) :: (← evalPureArgs V rest))
end

mutual
/-- Evaluation only reads the expression's variables. -/
theorem evalPure_agree {V V' : VEnv D} : ∀ {e : Expr Op},
    (∀ z ∈ exprVarsRv e, VEnv.get V' z = VEnv.get V z) →
    evalPure V' e = evalPure V e
  | .lit l, _ => by cases l <;> rfl
  | .var x, h => by
      simpa [evalPure] using h x (by simp [exprVarsRv])
  | .builtin op args, h => by
      simp only [evalPure]
      rw [evalPureArgs_agree (fun z hz => h z (by simpa [exprVarsRv] using hz))]
  | .call f args, _ => rfl

theorem evalPureArgs_agree {V V' : VEnv D} : ∀ {es : List (Expr Op)},
    (∀ z ∈ argsVarsRv es, VEnv.get V' z = VEnv.get V z) →
    evalPureArgs V' es = evalPureArgs V es
  | [], _ => rfl
  | e :: rest, h => by
      simp only [evalPureArgs]
      rw [evalPure_agree (fun z hz =>
          h z (by simp only [argsVarsRv, List.mem_append]; exact Or.inl hz)),
        evalPureArgs_agree (fun z hz =>
          h z (by simp only [argsVarsRv, List.mem_append]; exact Or.inr hz))]
end

theorem evalPureArgs_length {V : VEnv D} : ∀ {es : List (Expr Op)}
    {ws : List U256}, evalPureArgs V es = some ws → ws.length = es.length
  | [], ws, h => by
      simp only [evalPureArgs, Option.some.injEq] at h
      subst h
      rfl
  | e :: rest, ws, h => by
      simp only [evalPureArgs, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨v, hv, h⟩ := h
      obtain ⟨vs, hvs, h⟩ := h
      simp only [Option.pure_def, Option.some.injEq] at h
      subst h
      simp [evalPureArgs_length hvs]

/-! ### The Step bridge: canonical pure evaluation is total, deterministic,
and state-preserving -/

mutual
/-- Construction: a defined evaluation yields a derivation, at any state. -/
theorem evalPure_step {V : VEnv D} : ∀ {e : Expr Op} {w : U256},
    evalPure V e = some w →
    ∀ (funs : FunEnv D) (st : EvmState),
      Step D funs V st (.expr e) (.eres (.vals [w] st))
  | .lit l, w, h => by
      cases l with
      | number n =>
          simp only [evalPure, Option.some.injEq] at h
          subst h
          exact fun funs st => Step.lit
      | string s => simp [evalPure] at h
      | bool b => simp [evalPure] at h
  | .var x, w, h => fun funs st => Step.var (by simpa [evalPure] using h)
  | .builtin op args, w, h => by
      simp only [evalPure] at h
      split at h
      · next har =>
          cases hargs : evalPureArgs V args with
          | none => rw [hargs] at h; cases h
          | some ws =>
              rw [hargs] at h
              simp only [Option.bind_some] at h
              intro funs st
              exact Step.builtinOk (evalPureArgs_step hargs funs st)
                (pureFn_builtin h st)
      · cases h

theorem evalPureArgs_step {V : VEnv D} : ∀ {es : List (Expr Op)}
    {ws : List U256}, evalPureArgs V es = some ws →
    ∀ (funs : FunEnv D) (st : EvmState),
      Step D funs V st (.args es) (.eres (.vals ws st))
  | [], ws, h => by
      simp only [evalPureArgs, Option.some.injEq] at h
      subst h
      exact fun funs st => Step.argsNil
  | e :: rest, ws, h => by
      simp only [evalPureArgs, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨v, hv, h⟩ := h
      obtain ⟨vs, hvs, h⟩ := h
      simp only [Option.pure_def, Option.some.injEq] at h
      subst h
      intro funs st
      exact Step.argsCons (evalPureArgs_step hvs funs st)
        (evalPure_step hv funs st)
end

mutual
/-- Determinism within the fragment: any derivation of a defined canonical
pure expression returns its evaluation with the state unchanged. -/
theorem evalPure_step_inv {V : VEnv D} : ∀ {e : Expr Op} {w : U256},
    evalPure V e = some w →
    ∀ (funs : FunEnv D) (st : EvmState) (res : Res D),
      Step D funs V st (.expr e) res → res = .eres (.vals [w] st)
  | .lit l, w, h => by
      cases l with
      | number n =>
          simp only [evalPure, Option.some.injEq] at h
          subst h
          intro funs st res hstep
          cases hstep
          rfl
      | string s => simp [evalPure] at h
      | bool b => simp [evalPure] at h
  | .var x, w, h => by
      intro funs st res hstep
      cases hstep with
      | var hv =>
          simp only [evalPure] at h
          rw [h] at hv
          injection hv with hv
          rw [hv]
  | .builtin op args, w, h => by
      simp only [evalPure] at h
      split at h
      · next har =>
          cases hargs : evalPureArgs V args with
          | none => rw [hargs] at h; cases h
          | some ws =>
              rw [hargs] at h
              simp only [Option.bind_some] at h
              intro funs st res hstep
              cases hstep with
              | builtinOk ha hop =>
                  have hres := evalPureArgs_step_inv hargs _ _ _ ha
                  injection hres with hres
                  injection hres with h1 h2
                  subst h1; subst h2
                  have hok := pureFn_builtin_inv h hop
                  injection hok with h3 h4
                  subst h3; subst h4
                  rfl
              | builtinHalt ha hop =>
                  have hres := evalPureArgs_step_inv hargs _ _ _ ha
                  injection hres with hres
                  injection hres with h1 h2
                  subst h1; subst h2
                  have := pureFn_builtin_inv h hop
                  cases this
              | builtinArgsHalt ha =>
                  have := evalPureArgs_step_inv hargs _ _ _ ha
                  cases this
      · cases h

theorem evalPureArgs_step_inv {V : VEnv D} : ∀ {es : List (Expr Op)}
    {ws : List U256}, evalPureArgs V es = some ws →
    ∀ (funs : FunEnv D) (st : EvmState) (res : Res D),
      Step D funs V st (.args es) res → res = .eres (.vals ws st)
  | [], ws, h => by
      simp only [evalPureArgs, Option.some.injEq] at h
      subst h
      intro funs st res hstep
      cases hstep
      rfl
  | e :: rest, ws, h => by
      simp only [evalPureArgs, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨v, hv, h⟩ := h
      obtain ⟨vs, hvs, h⟩ := h
      simp only [Option.pure_def, Option.some.injEq] at h
      subst h
      intro funs st res hstep
      cases hstep with
      | argsCons hr he =>
          have hr' := evalPureArgs_step_inv hvs _ _ _ hr
          injection hr' with hr'
          injection hr' with h1 h2
          subst h1; subst h2
          have he' := evalPure_step_inv hv _ _ _ he
          injection he' with he'
          injection he' with h3 h4
          subst h4
          injection h3 with h5 _
          subst h5
          rfl
      | argsRestHalt hr =>
          have := evalPureArgs_step_inv hvs _ _ _ hr
          cases this
      | argsHeadHalt hr he =>
          have hr' := evalPureArgs_step_inv hvs _ _ _ hr
          injection hr' with hr'
          injection hr' with h1 h2
          subst h1; subst h2
          have := evalPure_step_inv hv _ _ _ he
          cases this
end

/-! ### Range activity -/

/-- The byte range `[off, off+size)` lies inside active memory, so touching
it leaves the state unchanged. -/
def RangeActive (st : EvmState) (off size : Nat) : Prop :=
  activeWordsAfter st.activeWords.toNat off size = st.activeWords.toNat

theorem RangeActive.touch_eq {st : EvmState} {off size : Nat}
    (h : RangeActive st off size) : touchMemory st off size = st := by
  unfold touchMemory
  rw [h, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem RangeActive.mono {st st' : EvmState} {off size : Nat}
    (h : RangeActive st off size)
    (hle : st.activeWords.toNat ≤ st'.activeWords.toNat) :
    RangeActive st' off size := by
  unfold RangeActive activeWordsAfter at h ⊢
  split at h
  · next hz => rw [if_pos hz]
  · next hz =>
      rw [if_neg hz]
      have hX : (off + size - 1) / 32 + 1 ≤ st.activeWords.toNat :=
        max_eq_left_iff.mp h
      exact max_eq_left_iff.mpr (Nat.le_trans hX hle)

private theorem activeWordsAfter_lt (st : EvmState) {off size : Nat}
    (hoff : off ≤ 2 ^ 256) (hsz : size ≤ 2 ^ 256) :
    activeWordsAfter st.activeWords.toNat off size < 2 ^ 256 := by
  unfold activeWordsAfter
  have ha := st.activeWords.isLt
  split
  · exact ha
  · have hX : (off + size - 1) / 32 + 1 < 2 ^ 256 := by omega
    exact Nat.max_lt.mpr ⟨ha, hX⟩

/-- Touching only grows active memory. -/
theorem activeWords_le_touch (st : EvmState) {off size : Nat}
    (hoff : off ≤ 2 ^ 256) (hsz : size ≤ 2 ^ 256) :
    st.activeWords.toNat ≤ (touchMemory st off size).activeWords.toNat := by
  show st.activeWords.toNat ≤
    (BitVec.ofNat 256 (activeWordsAfter st.activeWords.toNat off size)).toNat
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (activeWordsAfter_lt st hoff hsz)]
  unfold activeWordsAfter
  split
  · exact Nat.le_refl _
  · exact Nat.le_max_left _ _

/-- Touching covers the touched range. -/
theorem touch_covers (st : EvmState) {off size : Nat} (hnz : size ≠ 0)
    (hb : off + size ≤ 2 ^ 256) :
    RangeActive (touchMemory st off size) off size := by
  unfold RangeActive
  have hval : (touchMemory st off size).activeWords.toNat =
      activeWordsAfter st.activeWords.toNat off size := by
    show (BitVec.ofNat 256 _).toNat = _
    rw [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (activeWordsAfter_lt st (by omega) (by omega))]
  rw [hval]
  unfold activeWordsAfter
  rw [if_neg hnz, if_neg hnz]
  exact max_eq_left_iff.mpr (Nat.le_max_right _ _)

/-! ### Fact denotations -/

def AliasHolds (V : VEnv D) (p : Ident × Ident) : Prop :=
  ∃ v, VEnv.get V p.1 = some v ∧ VEnv.get V p.2 = some v

def CellHolds (V : VEnv D) (st : EvmState) (p : Nat × Expr Op) : Prop :=
  evalPure V p.2 = some (loadWord st.memory p.1) ∧
    RangeActive st p.1 32 ∧ p.1 + 32 ≤ 2 ^ 256

def PureHolds (V : VEnv D) (p : Expr Op × Ident) : Prop :=
  ∃ w, evalPure V p.1 = some w ∧ VEnv.get V p.2 = some w

/-- Big-endian bytes of one 32-byte word. -/
def wordBytes (w : U256) : List UInt8 :=
  (List.range 32).map (fun i => byteAt w (31 - i))

def wordsBytes : List U256 → List UInt8
  | [] => []
  | w :: ws => wordBytes w ++ wordsBytes ws

/-- The signature's canonical expressions denote the given words. -/
def SigDen (V : VEnv D) : CellSig → List U256 → Prop
  | [], [] => True
  | (_, e) :: rest, w :: ws => evalPure V e = some w ∧ SigDen V rest ws
  | _, _ => False

def KecHolds (V : VEnv D) (st : EvmState)
    (p : (Nat × Nat × CellSig) × Ident) : Prop :=
  ∃ ws, SigDen V p.1.2.2 ws ∧
    VEnv.get V p.2 = some (st.env.keccakOf (wordsBytes ws)) ∧
    RangeActive st p.1.1 p.1.2.1

def SldHolds (V : VEnv D) (st : EvmState) (p : Expr Op × Ident) : Prop :=
  ∃ k, evalPure V p.1 = some k ∧ VEnv.get V p.2 = some (st.storage k)

/-- Cache validity: every fact's denotation holds now. -/
structure RvOk (V : VEnv D) (st : EvmState) (C : RvCache) : Prop where
  aliases : ∀ p ∈ C.aliases, AliasHolds V p
  cells : ∀ p ∈ C.cells, CellHolds V st p
  pures : ∀ p ∈ C.pures, PureHolds V p
  kecs : ∀ p ∈ C.kecs, KecHolds V st p
  slds : ∀ p ∈ C.slds, SldHolds V st p

theorem RvOk.empty (V : VEnv D) (st : EvmState) :
    RvOk V st RvCache.empty := by
  constructor <;> (intro p hp; simp [RvCache.empty] at hp)

/-! ### Environment-change preservation (kill) -/

private theorem not_any_vars {xs vars : List Ident}
    (h : xs.any (vars.contains ·) = false) : ∀ z ∈ vars, z ∉ xs := by
  intro z hz hmem
  have := List.any_eq_false.mp h z hmem
  simp [List.contains_eq_mem, hz] at this

theorem SigDen.agree {V V' : VEnv D} : ∀ {sig : CellSig} {ws : List U256},
    SigDen V sig ws →
    (∀ q ∈ sig, ∀ z ∈ exprVarsRv q.2, VEnv.get V' z = VEnv.get V z) →
    SigDen V' sig ws
  | [], [], _, _ => trivial
  | (i, e) :: rest, w :: ws, h, hag => by
      obtain ⟨h1, h2⟩ := h
      exact ⟨by rw [evalPure_agree (hag (i, e) (by simp))]; exact h1,
        SigDen.agree h2 (fun q hq => hag q (List.mem_cons_of_mem _ hq))⟩
  | [], _ :: _, h, _ => h.elim
  | _ :: _, [], h, _ => h.elim

/-- Facts surviving `kill xs` remain valid in any environment that agrees
with the current one outside `xs`. -/
theorem RvOk.kill {V V' : VEnv D} {st : EvmState} {C : RvCache}
    (hc : RvOk V st C) (xs : List Ident)
    (hag : ∀ z, z ∉ xs → VEnv.get V' z = VEnv.get V z) :
    RvOk V' st (C.kill xs) := by
  constructor
  · intro p hp
    simp only [RvCache.kill, List.mem_filter, Bool.and_eq_true,
      Bool.not_eq_true'] at hp
    obtain ⟨hp, hk1, hk2⟩ := hp
    obtain ⟨v, h1, h2⟩ := hc.aliases p hp
    refine ⟨v, ?_, ?_⟩
    · rw [hag p.1 (by simpa [List.contains_eq_mem] using hk1)]; exact h1
    · rw [hag p.2 (by simpa [List.contains_eq_mem] using hk2)]; exact h2
  · intro p hp
    simp only [RvCache.kill, List.mem_filter, Bool.not_eq_true'] at hp
    obtain ⟨hp, hk⟩ := hp
    obtain ⟨h1, h2, h3⟩ := hc.cells p hp
    refine ⟨?_, h2, h3⟩
    rw [evalPure_agree (fun z hz => hag z (not_any_vars hk z hz))]
    exact h1
  · intro p hp
    simp only [RvCache.kill, List.mem_filter, Bool.and_eq_true,
      Bool.not_eq_true'] at hp
    obtain ⟨hp, hk1, hk2⟩ := hp
    obtain ⟨w, h1, h2⟩ := hc.pures p hp
    refine ⟨w, ?_, ?_⟩
    · rw [evalPure_agree (fun z hz => hag z (not_any_vars hk2 z hz))]
      exact h1
    · rw [hag p.2 (by simpa [List.contains_eq_mem] using hk1)]; exact h2
  · intro p hp
    simp only [RvCache.kill, List.mem_filter, Bool.and_eq_true,
      Bool.not_eq_true'] at hp
    obtain ⟨hp, hk1, hk2⟩ := hp
    obtain ⟨ws, h1, h2, h3⟩ := hc.kecs p hp
    refine ⟨ws, ?_, ?_, h3⟩
    · refine SigDen.agree h1 (fun q hq z hz => hag z ?_)
      intro hzx
      have hnm : (p.1.2.2.any fun q => (exprVarsRv q.2).contains z) = false := by
        have := List.any_eq_false.mp hk2 z hzx
        simpa [sigMentions] using this
      have := List.any_eq_false.mp hnm q hq
      simp [List.contains_eq_mem, hz] at this
    · rw [hag p.2 (by simpa [List.contains_eq_mem] using hk1)]; exact h2
  · intro p hp
    simp only [RvCache.kill, List.mem_filter, Bool.and_eq_true,
      Bool.not_eq_true'] at hp
    obtain ⟨hp, hk1, hk2⟩ := hp
    obtain ⟨k, h1, h2⟩ := hc.slds p hp
    refine ⟨k, ?_, ?_⟩
    · rw [evalPure_agree (fun z hz => hag z (not_any_vars hk2 z hz))]
      exact h1
    · rw [hag p.2 (by simpa [List.contains_eq_mem] using hk1)]; exact h2

/-! ### State-change preservation -/

/-- Machine-state changes that facts cannot observe. -/
structure MemNeutral (st st' : EvmState) : Prop where
  memory : st'.memory = st.memory
  storage : st'.storage = st.storage
  keccak : st'.env.keccakOf = st.env.keccakOf
  active : st.activeWords.toNat ≤ st'.activeWords.toNat

theorem MemNeutral.refl (st : EvmState) : MemNeutral st st :=
  ⟨rfl, rfl, rfl, Nat.le_refl _⟩

theorem MemNeutral.trans {st₁ st₂ st₃ : EvmState}
    (h1 : MemNeutral st₁ st₂) (h2 : MemNeutral st₂ st₃) :
    MemNeutral st₁ st₃ :=
  ⟨h2.memory.trans h1.memory, h2.storage.trans h1.storage,
    h2.keccak.trans h1.keccak, Nat.le_trans h1.active h2.active⟩

theorem MemNeutral.touch (st : EvmState) {off size : Nat}
    (hoff : off ≤ 2 ^ 256) (hsz : size ≤ 2 ^ 256) :
    MemNeutral st (touchMemory st off size) :=
  ⟨rfl, rfl, rfl, activeWords_le_touch st hoff hsz⟩

theorem RvOk.memNeutral {V : VEnv D} {st st' : EvmState} {C : RvCache}
    (hc : RvOk V st C) (h : MemNeutral st st') : RvOk V st' C := by
  constructor
  · exact hc.aliases
  · intro p hp
    obtain ⟨h1, h2, h3⟩ := hc.cells p hp
    exact ⟨by rw [h.memory]; exact h1, h2.mono h.active, h3⟩
  · exact hc.pures
  · intro p hp
    obtain ⟨ws, h1, h2, h3⟩ := hc.kecs p hp
    exact ⟨ws, h1, by rw [h.keccak]; exact h2, h3.mono h.active⟩
  · intro p hp
    obtain ⟨k, h1, h2⟩ := hc.slds p hp
    exact ⟨k, h1, by rw [h.storage]; exact h2⟩

/-- `sstore` invalidates only the storage-read facts. -/
theorem RvOk.sstoreKill {V : VEnv D} {st st' : EvmState} {C : RvCache}
    (hc : RvOk V st C) (hmem : st'.memory = st.memory)
    (hkec : st'.env.keccakOf = st.env.keccakOf)
    (hact : st'.activeWords = st.activeWords) :
    RvOk V st' C.killSlds := by
  have hle : st.activeWords.toNat ≤ st'.activeWords.toNat := by
    rw [hact]
  constructor
  · exact hc.aliases
  · intro p hp
    obtain ⟨h1, h2, h3⟩ := hc.cells p hp
    exact ⟨by rw [hmem]; exact h1, h2.mono hle, h3⟩
  · exact hc.pures
  · intro p hp
    obtain ⟨ws, h1, h2, h3⟩ := hc.kecs p hp
    exact ⟨ws, h1, by rw [hkec]; exact h2, h3.mono hle⟩
  · intro p hp
    simp [RvCache.killSlds] at hp

/-- `mstore` at a checked literal address: overlapping cells are gone, the
rest of the invariant survives. -/
theorem RvOk.mstore {V : VEnv D} {st : EvmState} {C : RvCache}
    (hc : RvOk V st C) {k : Nat} (hkb : k + 32 ≤ 2 ^ 256) {v : U256} :
    RvOk V ({ touchMemory st k 32 with
      memory := storeWord st.memory k v }) (C.putCell k none) := by
  have hactle : st.activeWords.toNat ≤
      ({ touchMemory st k 32 with
        memory := storeWord st.memory k v }).activeWords.toNat :=
    activeWords_le_touch st (by omega) (by omega)
  constructor
  · exact hc.aliases
  · intro p hp
    simp only [RvCache.putCell, List.mem_filter, Bool.not_eq_true'] at hp
    obtain ⟨hp, hno⟩ := hp
    obtain ⟨h1, h2, h3⟩ := hc.cells p hp
    refine ⟨?_, h2.mono hactle, h3⟩
    show evalPure V p.2 = some (loadWord (storeWord st.memory k v) p.1)
    rw [YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other st.memory k p.1 v ?_]
    · exact h1
    · simp only [cellsOverlap, Bool.and_eq_false_iff,
        decide_eq_false_iff_not, Nat.not_lt] at hno
      omega
  · exact hc.pures
  · intro p hp
    obtain ⟨ws, h1, h2, h3⟩ := hc.kecs p hp
    exact ⟨ws, h1, h2, h3.mono hactle⟩
  · intro p hp
    obtain ⟨kk, h1, h2⟩ := hc.slds p hp
    exact ⟨kk, h1, h2⟩

/-! ### Syntactic equality is equality

`exprBeq` reduces definitionally on constructor pairs (its generated match
equations are avoided on purpose). -/

mutual
theorem exprBeq_eq : ∀ (e₁ e₂ : Expr Op), exprBeq e₁ e₂ = true → e₁ = e₂
  | .lit l₁, e₂, h => by
      cases e₂
      case lit l₂ =>
        cases l₁ <;> cases l₂ <;>
          first
          | exact absurd h Bool.false_ne_true
          | exact congrArg Expr.lit (congrArg Literal.number (eq_of_beq h))
          | exact congrArg Expr.lit (congrArg Literal.string (eq_of_beq h))
      all_goals (cases l₁ <;> exact absurd h Bool.false_ne_true)
  | .var x, e₂, h => by
      cases e₂
      case var y => exact congrArg Expr.var (eq_of_beq h)
      all_goals exact absurd h Bool.false_ne_true
  | .builtin o1 a1, e₂, h => by
      cases e₂
      case builtin o2 a2 =>
          have h2 : (o1 == o2 && argsBeq a1 a2) = true := h
          simp only [Bool.and_eq_true, beq_iff_eq] at h2
          rw [h2.1, argsBeq_eq a1 a2 h2.2]
      all_goals exact absurd h Bool.false_ne_true
  | .call f1 a1, e₂, h => by
      cases e₂
      case call f2 a2 =>
          have h2 : (f1 == f2 && argsBeq a1 a2) = true := h
          simp only [Bool.and_eq_true, beq_iff_eq] at h2
          rw [h2.1, argsBeq_eq a1 a2 h2.2]
      all_goals exact absurd h Bool.false_ne_true

theorem argsBeq_eq : ∀ (es₁ es₂ : List (Expr Op)),
    argsBeq es₁ es₂ = true → es₁ = es₂
  | [], es₂, h => by
      cases es₂
      · rfl
      · exact absurd h Bool.false_ne_true
  | e :: rest, es₂, h => by
      cases es₂ with
      | nil => exact absurd h Bool.false_ne_true
      | cons e₂ rest₂ =>
          have h2 : (exprBeq e e₂ && argsBeq rest rest₂) = true := h
          simp only [Bool.and_eq_true] at h2
          rw [exprBeq_eq e e₂ h2.1, argsBeq_eq rest rest₂ h2.2]
end

theorem sigBeq_eq : ∀ (s₁ s₂ : CellSig), sigBeq s₁ s₂ = true → s₁ = s₂
  | [], s₂, h => by
      cases s₂ with
      | nil => rfl
      | cons q r => exact absurd h Bool.false_ne_true
  | (i₁, e₁) :: r₁, s₂, h => by
      cases s₂ with
      | nil => exact absurd h Bool.false_ne_true
      | cons q r₂ =>
          rcases q with ⟨i₂, e₂⟩
          have h2 : (i₁ == i₂ && exprBeq e₁ e₂ && sigBeq r₁ r₂) = true := h
          simp only [Bool.and_eq_true, beq_iff_eq] at h2
          rw [h2.1.1, exprBeq_eq e₁ e₂ h2.1.2, sigBeq_eq r₁ r₂ h2.2]

/-! ### Canonicalization preserves evaluation -/

theorem canonVar_get {C : RvCache} {V : VEnv D} {st : EvmState}
    (hc : RvOk V st C) (y : Ident) :
    VEnv.get V (canonVar C y) = VEnv.get V y := by
  unfold canonVar
  cases hf : C.aliases.find? (fun p => p.1 = y) with
  | none => rfl
  | some p =>
      simp only [Option.map_some, Option.getD_some]
      obtain ⟨v, h1, h2⟩ := hc.aliases p (List.mem_of_find?_eq_some hf)
      have hkey : p.1 = y := by
        have := List.find?_some hf
        simpa using this
      rw [h2, ← hkey, h1]

theorem canonPureArgs_length {C : RvCache} : ∀ {es ces : List (Expr Op)},
    canonPureArgs C es = some ces → ces.length = es.length
  | [], ces, h => by
      simp only [canonPureArgs, Option.some.injEq] at h
      subst h
      rfl
  | e :: rest, ces, h => by
      simp only [canonPureArgs, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at h
      obtain ⟨ce, hce, h⟩ := h
      obtain ⟨crest, hcrest, h⟩ := h
      simp only [Option.pure_def, Option.some.injEq] at h
      subst h
      simp [canonPureArgs_length hcrest]

mutual
theorem canonPureGo_eval {C : RvCache} {V : VEnv D} {st : EvmState}
    (hc : RvOk V st C) : ∀ {e ce : Expr Op}, canonPureGo C e = some ce →
    evalPure V ce = evalPure V e
  | .lit l, ce, h => by
      cases l with
      | number n =>
          simp only [canonPureGo, Option.some.injEq] at h
          subst h
          rfl
      | string s => simp [canonPureGo] at h
      | bool b => simp [canonPureGo] at h
  | .var x, ce, h => by
      simp only [canonPureGo, Option.some.injEq] at h
      subst h
      show evalPure V (.var (canonVar C x)) = evalPure V (.var x)
      simp only [evalPure]
      exact canonVar_get hc x
  | .builtin op args, ce, h => by
      simp only [canonPureGo] at h
      split at h
      · next har =>
          cases hargs : canonPureArgs C args with
          | none => rw [hargs] at h; cases h
          | some cargs =>
              rw [hargs] at h
              simp only [Option.map_some, Option.some.injEq] at h
              subst h
              have hlen : cargs.length = args.length :=
                canonPureArgs_length hargs
              simp only [evalPure, hlen]
              rw [canonPureArgs_eval hc hargs]
      · cases h
  | .call _ _, ce, h => by simp [canonPureGo] at h

theorem canonPureArgs_eval {C : RvCache} {V : VEnv D} {st : EvmState}
    (hc : RvOk V st C) : ∀ {es ces : List (Expr Op)},
    canonPureArgs C es = some ces →
    evalPureArgs V ces = evalPureArgs V es
  | [], ces, h => by
      simp only [canonPureArgs, Option.some.injEq] at h
      subst h
      rfl
  | e :: rest, ces, h => by
      simp only [canonPureArgs, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at h
      obtain ⟨ce, hce, h⟩ := h
      obtain ⟨crest, hcrest, h⟩ := h
      simp only [Option.pure_def, Option.some.injEq] at h
      subst h
      simp only [evalPureArgs]
      rw [canonPureGo_eval hc hce, canonPureArgs_eval hc hcrest]
end

theorem canonPure_eval {C : RvCache} {V : VEnv D} {st : EvmState}
    (hc : RvOk V st C) {e ce : Expr Op} (h : canonPure C e = some ce) :
    evalPure V ce = evalPure V e := by
  unfold canonPure at h
  split at h
  · cases h
  · exact canonPureGo_eval hc h

/-! ### Determinism over the canonical domain -/

mutual
/-- Any derivation of an expression in `canonPureGo`'s domain evaluates it
functionally, with the state unchanged. -/
theorem canonDom_step_inv {C : RvCache} : ∀ {e ce : Expr Op},
    canonPureGo C e = some ce →
    ∀ (funs : FunEnv D) (V : VEnv D) (st : EvmState) (res : Res D),
      Step D funs V st (.expr e) res →
      ∃ w, evalPure V e = some w ∧ res = .eres (.vals [w] st)
  | .lit l, ce, h => by
      cases l with
      | number n =>
          intro funs V st res hstep
          cases hstep
          exact ⟨_, rfl, rfl⟩
      | string s => simp [canonPureGo] at h
      | bool b => simp [canonPureGo] at h
  | .var x, ce, h => by
      intro funs V st res hstep
      cases hstep with
      | var hv => exact ⟨_, hv, rfl⟩
  | .builtin op args, ce, h => by
      simp only [canonPureGo] at h
      split at h
      · next har =>
          have har' : pureTotalArity op = some args.length := by
            simpa using har
          cases hargs : canonPureArgs C args with
          | none => rw [hargs] at h; cases h
          | some cargs =>
              intro funs V st res hstep
              cases hstep with
              | builtinOk ha hop =>
                  obtain ⟨ws, hws, hres⟩ := canonDomArgs_step_inv hargs _ _ _ _ ha
                  injection hres with hres
                  injection hres with h1 h2
                  rw [h1] at hop
                  have hlen : ws.length = args.length :=
                    evalPureArgs_length hws
                  obtain ⟨w, hw⟩ := pureTotalArity_pureFn har' ws (by omega)
                  have hok := pureFn_builtin_inv hw hop
                  injection hok with h3 h4
                  refine ⟨w, ?_, ?_⟩
                  · simp only [evalPure, if_pos har', hws, Option.bind_some, hw]
                  · rw [h3, h4, h2]
              | builtinHalt ha hop =>
                  obtain ⟨ws, hws, hres⟩ := canonDomArgs_step_inv hargs _ _ _ _ ha
                  injection hres with hres
                  injection hres with h1 h2
                  rw [h1] at hop
                  have hlen : ws.length = args.length :=
                    evalPureArgs_length hws
                  obtain ⟨w, hw⟩ := pureTotalArity_pureFn har' ws (by omega)
                  have := pureFn_builtin_inv hw hop
                  cases this
              | builtinArgsHalt ha =>
                  obtain ⟨ws, hws, hres⟩ := canonDomArgs_step_inv hargs _ _ _ _ ha
                  cases hres
      · cases h
  | .call _ _, ce, h => by simp [canonPureGo] at h

theorem canonDomArgs_step_inv {C : RvCache} : ∀ {es ces : List (Expr Op)},
    canonPureArgs C es = some ces →
    ∀ (funs : FunEnv D) (V : VEnv D) (st : EvmState) (res : Res D),
      Step D funs V st (.args es) res →
      ∃ ws, evalPureArgs V es = some ws ∧ res = .eres (.vals ws st)
  | [], ces, h => by
      intro funs V st res hstep
      cases hstep
      exact ⟨[], rfl, rfl⟩
  | e :: rest, ces, h => by
      simp only [canonPureArgs, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at h
      obtain ⟨ce, hce, h⟩ := h
      obtain ⟨crest, hcrest, h⟩ := h
      intro funs V st res hstep
      cases hstep with
      | argsCons hr he =>
          obtain ⟨ws, hws, hres⟩ := canonDomArgs_step_inv hcrest _ _ _ _ hr
          injection hres with hres
          injection hres with h1 h2
          subst h2
          obtain ⟨w, hw, hres'⟩ := canonDom_step_inv hce _ _ _ _ he
          injection hres' with hres'
          injection hres' with h3 h4
          injection h3 with h5 _
          refine ⟨w :: ws, ?_, ?_⟩
          · simp [evalPureArgs, hw, hws]
          · rw [h5, h1, h4]
      | argsRestHalt hr =>
          obtain ⟨ws, hws, hres⟩ := canonDomArgs_step_inv hcrest _ _ _ _ hr
          cases hres
      | argsHeadHalt hr he =>
          obtain ⟨ws, hws, hres⟩ := canonDomArgs_step_inv hcrest _ _ _ _ hr
          injection hres with hres
          injection hres with h1 h2
          subst h2
          obtain ⟨w, hw, hres'⟩ := canonDom_step_inv hce _ _ _ _ he
          cases hres'
end

/-! ### State-neutral expressions only extend active memory -/

theorem rvNeutralExpr_args {op : Op} {args : List (Expr Op)}
    (h : rvNeutralExpr (.builtin op args) = true) :
    rvNeutralArgs args = true := by
  cases op <;>
    first
    | exact absurd h Bool.false_ne_true
    | (have h' : (_ && rvNeutralArgs args) = true := h
       simp only [Bool.and_eq_true] at h'
       exact h'.2)

set_option maxHeartbeats 1600000 in
/-- A neutral builtin's result: values, and a `MemNeutral` state change. -/
theorem rvNeutral_builtin_result {op : Op} {args : List (Expr Op)}
    (hn : rvNeutralExpr (.builtin op args) = true)
    {argvals : List U256} (hlen : argvals.length = args.length)
    {st : EvmState} {r : BuiltinResult U256 EvmState}
    (hop : (evmWithExternal calls creates).Builtin op argvals st r) :
    ∃ rets st', r = .ok rets st' ∧ MemNeutral st st' := by
  cases op
  case sload =>
      have h' : (args.length == 1 && rvNeutralArgs args) = true := hn
      simp only [Bool.and_eq_true, beq_iff_eq] at h'
      obtain ⟨k, rfl⟩ := List.length_eq_one_iff.mp (by omega : argvals.length = 1)
      simp only [builtinWithExternal, stepOp, Option.some.injEq] at hop
      exact ⟨_, _, hop.symm, MemNeutral.refl st⟩
  case mload =>
      have h' : (args.length == 1 && rvNeutralArgs args) = true := hn
      simp only [Bool.and_eq_true, beq_iff_eq] at h'
      obtain ⟨k, rfl⟩ := List.length_eq_one_iff.mp (by omega : argvals.length = 1)
      simp only [builtinWithExternal, stepOp, Option.some.injEq] at hop
      exact ⟨_, _, hop.symm,
        MemNeutral.touch st (Nat.le_of_lt k.isLt) (by omega)⟩
  case keccak256 =>
      have h' : (args.length == 2 && rvNeutralArgs args) = true := hn
      simp only [Bool.and_eq_true, beq_iff_eq] at h'
      match argvals, (by omega : argvals.length = 2) with
      | [p, n], _ =>
          simp only [builtinWithExternal, stepOp, Option.some.injEq] at hop
          exact ⟨_, _, hop.symm,
            MemNeutral.touch st (Nat.le_of_lt p.isLt) (Nat.le_of_lt n.isLt)⟩
  all_goals
    first
    | exact absurd hn Bool.false_ne_true
    | (have h' : ((pureTotalArity _ == some args.length) &&
          rvNeutralArgs args) = true := hn
       simp only [Bool.and_eq_true, beq_iff_eq] at h'
       obtain ⟨w, hw⟩ := pureTotalArity_pureFn h'.1 argvals (by omega)
       exact ⟨[w], st, pureFn_builtin_inv hw hop, MemNeutral.refl st⟩)

mutual
theorem rvNeutral_step : ∀ {e : Expr Op}, rvNeutralExpr e = true →
    ∀ (funs : FunEnv D) (V : VEnv D) (st : EvmState) (res : Res D),
      Step D funs V st (.expr e) res →
      ∃ vs st', res = .eres (.vals vs st') ∧ MemNeutral st st'
  | .lit l, hn => by
      intro funs V st res hstep
      cases hstep
      exact ⟨_, _, rfl, MemNeutral.refl st⟩
  | .var x, hn => by
      intro funs V st res hstep
      cases hstep with
      | var hv => exact ⟨_, _, rfl, MemNeutral.refl st⟩
  | .builtin op args, hn => by
      intro funs V st res hstep
      have hargs := rvNeutralExpr_args hn
      cases hstep with
      | builtinOk ha hop =>
          obtain ⟨vs, st₁, hres, hmn, hlen⟩ :=
            rvNeutralArgs_step hargs _ _ _ _ ha
          injection hres with hres
          injection hres with h1 h2
          rw [← h1] at hlen
          rw [← h2] at hmn
          obtain ⟨rets, st₂, hr, hmn₂⟩ :=
            rvNeutral_builtin_result hn hlen hop
          injection hr with h3 h4
          exact ⟨rets, st₂, by rw [h3, h4], hmn.trans hmn₂⟩
      | builtinHalt ha hop =>
          obtain ⟨vs, st₁, hres, hmn, hlen⟩ :=
            rvNeutralArgs_step hargs _ _ _ _ ha
          injection hres with hres
          injection hres with h1 h2
          rw [← h1] at hlen
          obtain ⟨rets, st₂, hr, hmn₂⟩ :=
            rvNeutral_builtin_result hn hlen hop
          cases hr
      | builtinArgsHalt ha =>
          obtain ⟨vs, st₁, hres, hmn, hlen⟩ :=
            rvNeutralArgs_step hargs _ _ _ _ ha
          cases hres
  | .call f args, hn => absurd hn Bool.false_ne_true

theorem rvNeutralArgs_step : ∀ {es : List (Expr Op)},
    rvNeutralArgs es = true →
    ∀ (funs : FunEnv D) (V : VEnv D) (st : EvmState) (res : Res D),
      Step D funs V st (.args es) res →
      ∃ vs st', res = .eres (.vals vs st') ∧ MemNeutral st st' ∧
        vs.length = es.length
  | [], _ => by
      intro funs V st res hstep
      cases hstep
      exact ⟨[], st, rfl, MemNeutral.refl st, rfl⟩
  | e :: rest, hn => by
      have hn' : (rvNeutralExpr e && rvNeutralArgs rest) = true := hn
      simp only [Bool.and_eq_true] at hn'
      intro funs V st res hstep
      cases hstep with
      | argsCons hr he =>
          obtain ⟨vs, st₁, hres, hmn, hlen⟩ :=
            rvNeutralArgs_step hn'.2 _ _ _ _ hr
          injection hres with hres
          injection hres with h1 h2
          obtain ⟨vs', st₂, hres', hmn'⟩ :=
            rvNeutral_step hn'.1 _ _ _ _ he
          injection hres' with hres'
          injection hres' with h3 h4
          refine ⟨_, _, rfl, ?_, by simp [h1, hlen]⟩
          rw [h4]
          exact (h2 ▸ hmn).trans hmn'
      | argsRestHalt hr =>
          obtain ⟨vs, st₁, hres, -, -⟩ :=
            rvNeutralArgs_step hn'.2 _ _ _ _ hr
          cases hres
      | argsHeadHalt hr he =>
          obtain ⟨vs', st₂, hres', -⟩ := rvNeutral_step hn'.1 _ _ _ _ he
          cases hres'
end

end YulEvmCompiler.Optimizer.ReuseValues
