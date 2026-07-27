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
  blockDecls stmtsNoNormal BoundOK ScopeFrame bindZeros_keys
  scopeFrame_stmts_normal stmtsNoNormal_sound stmtNoNormal_sound)

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

/-! ### Shape inversions for the forwarded right-hand sides -/

/-- `keccak256(a, b)` with literal, in-range operands: the unique result. -/
theorem keccak_lit_inv {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    {funs : FunEnv D} {V : VEnv D} {st : EvmState} {res : Res D}
    (h : Step D funs V st
      (.expr (.builtin .keccak256 [.lit (.number a), .lit (.number b)])) res) :
    res = .eres (.vals [st.env.keccakOf (readBytes st.memory a b)]
      (touchMemory st a b)) := by
  have hta : (Dialect.litValue D (.number a)).toNat = a := by
    show (BitVec.ofNat 256 a).toNat = a
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
  have htb : (Dialect.litValue D (.number b)).toNat = b := by
    show (BitVec.ofNat 256 b).toNat = b
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
  cases h with
  | builtinOk hargs hop =>
      cases hargs with
      | argsCons hrest hlit =>
          cases hrest with
          | argsCons hnil hlit2 =>
              cases hnil
              cases hlit2
              cases hlit
              simp [builtinWithExternal, stepOp] at hop
              obtain ⟨rfl, rfl⟩ := hop
              rw [hta, htb]
  | builtinHalt hargs hop =>
      cases hargs with
      | argsCons hrest hlit =>
          cases hrest with
          | argsCons hnil hlit2 =>
              cases hnil
              cases hlit2
              cases hlit
              simp [builtinWithExternal, stepOp] at hop
  | builtinArgsHalt hargs =>
      cases hargs with
      | argsRestHalt hrest =>
          cases hrest with
          | argsRestHalt hnil => cases hnil
          | argsHeadHalt hnil hlit => cases hlit
      | argsHeadHalt hrest hlit =>
          cases hlit

/-- `mload(k)` with a literal, in-range operand: the unique result. -/
theorem mload_lit_inv {k : Nat} (hk : k < 2 ^ 256)
    {funs : FunEnv D} {V : VEnv D} {st : EvmState} {res : Res D}
    (h : Step D funs V st
      (.expr (.builtin .mload [.lit (.number k)])) res) :
    res = .eres (.vals [loadWord st.memory k] (touchMemory st k 32)) := by
  have htk : (Dialect.litValue D (.number k)).toNat = k := by
    show (BitVec.ofNat 256 k).toNat = k
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
  cases h with
  | builtinOk hargs hop =>
      cases hargs with
      | argsCons hnil hlit =>
          cases hnil
          cases hlit
          simp [builtinWithExternal, stepOp] at hop
          obtain ⟨rfl, rfl⟩ := hop
          rw [htk]
  | builtinHalt hargs hop =>
      cases hargs with
      | argsCons hnil hlit =>
          cases hnil
          cases hlit
          simp [builtinWithExternal, stepOp] at hop
  | builtinArgsHalt hargs =>
      cases hargs with
      | argsRestHalt hnil => cases hnil
      | argsHeadHalt hnil hlit => cases hlit

/-- `sload(k)` with a canonical-domain key: the unique result. -/
theorem sload_canon_inv {C : RvCache} {k ck : Expr Op}
    (hck : canonPureGo C k = some ck)
    {funs : FunEnv D} {V : VEnv D} {st : EvmState} {res : Res D}
    (h : Step D funs V st (.expr (.builtin .sload [k])) res) :
    ∃ kv, evalPure V k = some kv ∧
      res = .eres (.vals [st.storage kv] st) := by
  cases h with
  | builtinOk hargs hop =>
      cases hargs with
      | argsCons hnil hke =>
          cases hnil
          obtain ⟨kv, hkv, hres⟩ := canonDom_step_inv hck _ _ _ _ hke
          injection hres with hres
          injection hres with h1 h2
          injection h1 with h3 _
          rw [h3] at hop
          rw [h2] at hop
          simp [builtinWithExternal, stepOp] at hop
          obtain ⟨rfl, rfl⟩ := hop
          exact ⟨kv, hkv, rfl⟩
  | builtinHalt hargs hop =>
      cases hargs with
      | argsCons hnil hke =>
          cases hnil
          obtain ⟨kv, hkv, hres⟩ := canonDom_step_inv hck _ _ _ _ hke
          injection hres with hres
          injection hres with h1 h2
          injection h1 with h3 _
          rw [h3] at hop
          rw [h2] at hop
          simp [builtinWithExternal, stepOp] at hop
  | builtinArgsHalt hargs =>
      cases hargs with
      | argsRestHalt hnil => cases hnil
      | argsHeadHalt hnil hke =>
          obtain ⟨kv, hkv, hres⟩ := canonDom_step_inv hck _ _ _ _ hke
          cases hres

/-- `mstore(k, v)`: either `v` evaluates and the store happens, or `v`
halts. -/
theorem mstore_lit_inv {k : Nat} (hk : k < 2 ^ 256) {v : Expr Op}
    {funs : FunEnv D} {V : VEnv D} {st : EvmState} {res : Res D}
    (h : Step D funs V st
      (.expr (.builtin .mstore [.lit (.number k), v])) res) :
    (∃ vv st₁, Step D funs V st (.expr v) (.eres (.vals [vv] st₁)) ∧
       res = .eres (.vals [] ({ touchMemory st₁ k 32 with
         memory := storeWord st₁.memory k vv }))) ∨
    (∃ st₁, Step D funs V st (.expr v) (.eres (.halt st₁)) ∧
       res = .eres (.halt st₁)) := by
  have htk : (Dialect.litValue D (.number k)).toNat = k := by
    show (BitVec.ofNat 256 k).toNat = k
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
  cases h with
  | builtinOk hargs hop =>
      cases hargs with
      | argsCons hrest hlit =>
          cases hrest with
          | argsCons hnil hv =>
              cases hnil
              cases hlit
              simp [builtinWithExternal, stepOp] at hop
              obtain ⟨rfl, rfl⟩ := hop
              refine Or.inl ⟨_, _, hv, ?_⟩
              rw [htk]
  | builtinHalt hargs hop =>
      cases hargs with
      | argsCons hrest hlit =>
          cases hrest with
          | argsCons hnil hv =>
              cases hnil
              cases hlit
              simp [builtinWithExternal, stepOp] at hop
  | builtinArgsHalt hargs =>
      cases hargs with
      | argsRestHalt hrest =>
          cases hrest with
          | argsRestHalt hnil => cases hnil
          | argsHeadHalt hnil hv =>
              cases hnil
              exact Or.inr ⟨_, hv, rfl⟩
      | argsHeadHalt hrest hlit =>
          cases hlit

/-- `sstore(k, v)` with neutral operands: only storage (and the storage
mirror in the environment) changes, after a `MemNeutral` argument
evaluation — or a halt. -/
theorem sstore_neutral_inv {args : List (Expr Op)}
    (hn : rvNeutralArgs args = true)
    {funs : FunEnv D} {V : VEnv D} {st : EvmState} {res : Res D}
    (h : Step D funs V st (.expr (.builtin .sstore args)) res) :
    (∃ st₁ st₂, MemNeutral st st₁ ∧ res = .eres (.vals [] st₂) ∧
       st₂.memory = st₁.memory ∧ st₂.env.keccakOf = st₁.env.keccakOf ∧
       st₂.activeWords = st₁.activeWords) ∨
    (∃ st', res = .eres (.halt st')) := by
  cases h with
  | @builtinOk _ _ _ _ _ argvals st1 rets st2 hargs hop =>
      obtain ⟨vs, st₁, hres, hmn, -⟩ :=
        rvNeutralArgs_step hn _ _ _ _ hargs
      injection hres with hres
      injection hres with h1 h2
      rw [← h2] at hmn
      cases argvals with
      | nil => simp [builtinWithExternal, stepOp] at hop
      | cons kv rest =>
        cases rest with
        | nil => simp [builtinWithExternal, stepOp] at hop
        | cons vv rest2 =>
          cases rest2 with
          | cons a b => simp [builtinWithExternal, stepOp] at hop
          | nil =>
              simp only [builtinWithExternal, stepOp, guardStatic,
                Option.some.injEq] at hop
              split at hop
              · cases hop
              · injection hop with hr hs
                refine Or.inl ⟨st1, st2, hmn, ?_, ?_, ?_, ?_⟩
                · rw [← hr]
                · rw [← hs]
                · rw [← hs]
                · rw [← hs]
  | builtinHalt hargs hop => exact Or.inr ⟨_, rfl⟩
  | builtinArgsHalt hargs => exact Or.inr ⟨_, rfl⟩

/-! ### Word/byte decomposition — the keccak content keystone

Equal covering words force equal byte ranges, so a hash keyed by cell
content replays exactly. The BitVec fold lemmas mirror (private) proofs in
`MemorySpillStateSound`. -/

private theorem bitvec_fold_eq (l : List UInt8) :
    ∀ acc : BitVec 256, l.length ≤ 32 → acc.toNat < 256 ^ (32 - l.length) →
      (l.foldl (fun (acc : BitVec 256) b =>
          (acc <<< (8 : Nat)) ||| BitVec.ofNat 256 b.toNat) acc).toNat
        = l.foldl (fun (acc : Nat) b => acc * 256 + b.toNat) acc.toNat := by
  induction l with
  | nil => intro acc _ _; rfl
  | cons b l ih =>
    intro acc hlen hacc
    simp only [List.length_cons] at hlen hacc
    have hb : b.toNat < 256 := b.toNat_lt
    have hpowle : 256 ^ (32 - (l.length + 1)) * 256 ≤ 256 ^ (32 - l.length) := by
      rw [← Nat.pow_succ]
      exact Nat.pow_le_pow_right (by omega) (by omega)
    have hmul_lt : acc.toNat * 256 + b.toNat < 2 ^ 256 := by
      have h1 : acc.toNat * 256 + b.toNat < (acc.toNat + 1) * 256 := by omega
      have h2 : (acc.toNat + 1) * 256 ≤ 256 ^ (32 - (l.length + 1)) * 256 :=
        Nat.mul_le_mul_right 256 hacc
      have hpow : (256 : Nat) ^ (32 - l.length) ≤ 256 ^ 32 :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have h32 : (256 : Nat) ^ 32 = 2 ^ 256 := by
        calc (256 : Nat) ^ 32 = (2 ^ 8) ^ 32 := by norm_num
          _ = 2 ^ (8 * 32) := (Nat.pow_mul 2 8 32).symm
          _ = 2 ^ 256 := by norm_num
      omega
    have hstep : ((acc <<< (8 : Nat)) ||| BitVec.ofNat 256 b.toNat).toNat
        = acc.toNat * 256 + b.toNat := by
      have h256 : acc.toNat * 2 ^ 8 = acc.toNat * 256 := by norm_num
      rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
      rw [Nat.shiftLeft_eq]
      rw [Nat.mod_eq_of_lt (show b.toNat < 2 ^ 256 from by omega)]
      rw [Nat.mod_eq_of_lt (show acc.toNat * 2 ^ 8 < 2 ^ 256 from by
        rw [h256]
        exact lt_of_le_of_lt (Nat.le_add_right _ _) hmul_lt)]
      rw [h256, Nat.mul_comm acc.toNat 256]
      show 2 ^ 8 * acc.toNat ||| b.toNat = 2 ^ 8 * acc.toNat + b.toNat
      exact (Nat.two_pow_add_eq_or_of_lt (show b.toNat < 2 ^ 8 from by omega)
        acc.toNat).symm
    show (l.foldl _ ((acc <<< (8 : Nat)) ||| BitVec.ofNat 256 b.toNat)).toNat = _
    rw [ih _ (by omega) (by
      rw [hstep]
      have h1 : acc.toNat * 256 + b.toNat < (acc.toNat + 1) * 256 := by omega
      have h2 : (acc.toNat + 1) * 256 ≤ 256 ^ (32 - (l.length + 1)) * 256 :=
        Nat.mul_le_mul_right 256 hacc
      omega)]
    rw [hstep, List.foldl_cons]

private theorem byteAt_eq' (value : U256) (i : Nat) :
    byteAt value i = UInt8.ofNat (value.toNat / 256 ^ i % 256) := by
  unfold byteAt
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    show (2 : Nat) ^ (8 * i) = 256 ^ i from by rw [pow_mul]; norm_num,
    UInt8.ofNat_mod_size']

private theorem decode_prefix' (value : U256) : ∀ n, n ≤ 32 →
    ((List.range n).map (fun i => byteAt value (31 - i))).foldl
        (fun acc b => acc * 256 + b.toNat) 0 =
      value.toNat / 256 ^ (32 - n) := by
  intro n hn
  induction n with
  | zero =>
    simp
    symm
    apply Nat.div_eq_of_lt
    simpa [show (256 : Nat) = 2 ^ 8 by norm_num, ← Nat.pow_mul] using value.isLt
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.foldl_append]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    rw [ih (by omega), byteAt_eq']
    rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (Nat.mod_lt _ (by norm_num))]
    have hsub : 31 - n = 32 - (n + 1) := by omega
    rw [hsub]
    have hpow : 256 ^ (32 - n) = 256 ^ (32 - (n + 1)) * 256 := by
      rw [← Nat.pow_succ]
      congr 1
      omega
    rw [hpow, ← Nat.div_div_eq_div_mul]
    have hdiv := Nat.mod_add_div
      (value.toNat / 256 ^ (32 - (n + 1))) 256
    omega

/-- The Nat byte fold, from an arbitrary accumulator. -/
private theorem natFold_from (bs : List UInt8) : ∀ acc : Nat,
    bs.foldl (fun acc b => acc * 256 + b.toNat) acc =
      acc * 256 ^ bs.length +
        bs.foldl (fun acc b => acc * 256 + b.toNat) 0 := by
  induction bs with
  | nil => intro acc; simp
  | cons b bs ih =>
      intro acc
      simp only [List.foldl_cons, List.length_cons, Nat.zero_mul,
        Nat.zero_add]
      rw [ih (acc * 256 + b.toNat), ih b.toNat]
      ring

private theorem natFold_lt (bs : List UInt8) :
    bs.foldl (fun acc b => acc * 256 + b.toNat) 0 < 256 ^ bs.length := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
      simp only [List.foldl_cons, List.length_cons, Nat.zero_mul, Nat.zero_add]
      rw [natFold_from]
      have hb : b.toNat ≤ 255 := by
        have := b.toNat_lt
        omega
      calc b.toNat * 256 ^ bs.length +
            bs.foldl (fun acc b => acc * 256 + b.toNat) 0
          ≤ 255 * 256 ^ bs.length +
            bs.foldl (fun acc b => acc * 256 + b.toNat) 0 :=
            Nat.add_le_add_right (Nat.mul_le_mul_right _ hb) _
        _ < 255 * 256 ^ bs.length + 256 ^ bs.length :=
            Nat.add_lt_add_left ih _
        _ = 256 ^ (bs.length + 1) := by
            rw [Nat.pow_succ]
            ring

private theorem natFold_inj : ∀ (bs₁ bs₂ : List UInt8),
    bs₁.length = bs₂.length →
    bs₁.foldl (fun acc b => acc * 256 + b.toNat) 0 =
      bs₂.foldl (fun acc b => acc * 256 + b.toNat) 0 →
    bs₁ = bs₂
  | [], [], _, _ => rfl
  | [], b :: bs, hlen, _ => by simp at hlen
  | b :: bs, [], hlen, _ => by simp at hlen
  | b₁ :: t₁, b₂ :: t₂, hlen, heq => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [List.foldl_cons, Nat.zero_mul, Nat.zero_add] at heq
      rw [natFold_from t₁, natFold_from t₂, hlen] at heq
      have h₁ := natFold_lt t₁
      have h₂ := natFold_lt t₂
      rw [hlen] at h₁
      have hpos : 0 < (256 : Nat) ^ t₂.length :=
        Nat.pow_pos (by omega)
      have hb : b₁.toNat = b₂.toNat := by
        have e₁ : (b₁.toNat * 256 ^ t₂.length +
            t₁.foldl (fun acc b => acc * 256 + b.toNat) 0) / 256 ^ t₂.length
            = b₁.toNat := by
          rw [Nat.mul_comm, Nat.mul_add_div hpos, Nat.div_eq_of_lt h₁,
            Nat.add_zero]
        have e₂ : (b₂.toNat * 256 ^ t₂.length +
            t₂.foldl (fun acc b => acc * 256 + b.toNat) 0) / 256 ^ t₂.length
            = b₂.toNat := by
          rw [Nat.mul_comm, Nat.mul_add_div hpos, Nat.div_eq_of_lt h₂,
            Nat.add_zero]
        rw [← e₁, ← e₂, heq]
      have hteq : t₁.foldl (fun acc b => acc * 256 + b.toNat) 0 =
          t₂.foldl (fun acc b => acc * 256 + b.toNat) 0 := by
        rw [hb] at heq
        omega
      rw [UInt8.toNat_inj.mp hb, natFold_inj t₁ t₂ hlen hteq]

/-- **The keystone**: the big-endian bytes of a loaded word are exactly the
memory's bytes. -/
theorem wordBytes_loadWord (mem : Nat → UInt8) (p : Nat) :
    wordBytes (loadWord mem p) = readBytes mem p 32 := by
  have hform : loadWord mem p = (readBytes mem p 32).foldl
      (fun (acc : U256) b =>
        (acc <<< (8 : Nat)) ||| BitVec.ofNat 256 b.toNat) 0 := by
    unfold loadWord readBytes
    rw [List.foldl_map]
  have hlenr : (readBytes mem p 32).length = 32 := by
    simp [readBytes]
  have hA : (readBytes mem p 32).foldl
      (fun acc b => acc * 256 + b.toNat) 0 = (loadWord mem p).toNat := by
    rw [hform,
      show ((readBytes mem p 32).foldl
        (fun (acc : U256) b =>
          (acc <<< (8 : Nat)) ||| BitVec.ofNat 256 b.toNat) 0).toNat =
      (readBytes mem p 32).foldl
        (fun acc b => acc * 256 + b.toNat) (BitVec.toNat (0 : U256)) from
        bitvec_fold_eq _ 0 (by rw [hlenr]) (by simp [hlenr])]
    rfl
  have hB : (wordBytes (loadWord mem p)).foldl
      (fun acc b => acc * 256 + b.toNat) 0 = (loadWord mem p).toNat := by
    show ((List.range 32).map
        (fun i => byteAt (loadWord mem p) (31 - i))).foldl _ 0 = _
    rw [decode_prefix' (loadWord mem p) 32 (by omega)]
    simp
  refine natFold_inj _ _ ?_ (by rw [hA, hB])
  rw [hlenr]
  simp [wordBytes]

/-- Bytes of `n` covered words. -/
theorem readBytes_wordsBytes {mem : Nat → UInt8} : ∀ {ws : List U256} {a : Nat},
    (∀ i (_ : i < ws.length), loadWord mem (a + 32 * i) = ws[i]!) →
    readBytes mem a (32 * ws.length) = wordsBytes ws
  | [], a, _ => by simp [readBytes, wordsBytes]
  | w :: ws, a, h => by
      have hsplit : readBytes mem a (32 * (ws.length + 1)) =
          readBytes mem a 32 ++ readBytes mem (a + 32) (32 * ws.length) := by
        unfold readBytes
        rw [show 32 * (ws.length + 1) = 32 + 32 * ws.length from by ring,
          List.range_add, List.map_append, List.map_map]
        congr 1
        apply List.map_congr_left
        intro i _
        show mem (a + (32 + i)) = mem (a + 32 + i)
        congr 1
        omega
      show readBytes mem a (32 * (ws.length + 1)) = wordBytes w ++ wordsBytes ws
      rw [hsplit]
      congr 1
      · rw [← wordBytes_loadWord mem a,
          show loadWord mem a = w from by simpa using h 0 (Nat.succ_pos _)]
      · exact readBytes_wordsBytes (fun i hi => by
          have := h (i + 1) (by simpa using Nat.succ_lt_succ hi)
          simpa [show a + 32 * (i + 1) = a + 32 + 32 * i from by ring]
            using this)

/-! ### Coverage signatures denote the current covering words -/

theorem SigDen.unique {V : VEnv D} : ∀ {sig : CellSig} {ws₁ ws₂ : List U256},
    SigDen V sig ws₁ → SigDen V sig ws₂ → ws₁ = ws₂
  | [], [], [], _, _ => rfl
  | [], [], _ :: _, _, h => h.elim
  | [], _ :: _, _, h, _ => h.elim
  | (i, e) :: rest, w₁ :: t₁, w₂ :: t₂, h₁, h₂ => by
      obtain ⟨he₁, ht₁⟩ := h₁
      obtain ⟨he₂, ht₂⟩ := h₂
      rw [he₁] at he₂
      injection he₂ with hw
      rw [hw, SigDen.unique ht₁ ht₂]
  | (i, e) :: rest, [], _, h, _ => h.elim
  | (i, e) :: rest, _ :: _, [], _, h => h.elim

theorem SigDen.length {V : VEnv D} : ∀ {sig : CellSig} {ws : List U256},
    SigDen V sig ws → ws.length = sig.length
  | [], [], _ => rfl
  | [], _ :: _, h => h.elim
  | (i, e) :: rest, [], h => h.elim
  | (i, e) :: rest, w :: t, h => by
      simp [SigDen.length h.2]

theorem coverageSig_go_den {C : RvCache} {V : VEnv D} {st : EvmState}
    (hc : RvOk V st C) {base : Nat} : ∀ (n i : Nat) {sig : CellSig},
    coverageSig.go C base n i = some sig →
    sig.length = n ∧ ∃ ws, SigDen V sig ws ∧
      ∀ j (_ : j < n), loadWord st.memory (base + 32 * (i + j)) = ws[j]!
  | 0, i, sig, h => by
      simp only [coverageSig.go, Option.some.injEq] at h
      subst h
      exact ⟨rfl, [], trivial, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | n + 1, i, sig, h => by
      simp only [coverageSig.go, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at h
      obtain ⟨v, hv, h⟩ := h
      obtain ⟨rest, hrest, h⟩ := h
      simp only [Option.pure_def, Option.some.injEq] at h
      subst h
      simp only [Option.map_eq_some_iff] at hv
      obtain ⟨q, hq, hv⟩ := hv
      have hqmem := List.mem_of_find?_eq_some hq
      have hqkey : q.1 = base + 32 * i := by
        have := List.find?_some hq
        simpa using this
      obtain ⟨hcell, -, -⟩ := hc.cells q hqmem
      obtain ⟨hlen, ws, hws, hload⟩ := coverageSig_go_den hc n (i + 1) hrest
      refine ⟨by simp [hlen], loadWord st.memory (base + 32 * i) :: ws,
        ⟨?_, hws⟩, ?_⟩
      · rw [hv, hqkey] at hcell
        exact hcell
      · intro j hj
        cases j with
        | zero => simp
        | succ j =>
            have := hload j (by omega)
            simpa [show i + (j + 1) = i + 1 + j from by omega] using this

/-- A successful coverage: the signature denotes the current covering
words. -/
theorem coverageSig_den {C : RvCache} {V : VEnv D} {st : EvmState}
    (hc : RvOk V st C) {base size : Nat} {sig : CellSig}
    (h : coverageSig C base size = some sig) :
    size = 32 * sig.length ∧ size ≠ 0 ∧ ∃ ws, SigDen V sig ws ∧
      ∀ j (_ : j < sig.length), loadWord st.memory (base + 32 * j) = ws[j]! := by
  unfold coverageSig at h
  split at h
  · cases h
  · next hsz =>
      have hsz' : ¬(size == 0 || size % 32 != 0) = true := hsz
      simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, not_or,
        not_not] at hsz'
      obtain ⟨hlen, ws, hws, hload⟩ := coverageSig_go_den hc _ 0 h
      refine ⟨by omega, hsz'.1, ws, hws, ?_⟩
      intro j hj
      have := hload j (by omega)
      simpa using this

/-! ### Facts free of the binding target -/

/-- No fact of `C` mentions `x`. -/
structure XFree (x : Ident) (C : RvCache) : Prop where
  aliases : ∀ p ∈ C.aliases, p.1 ≠ x ∧ p.2 ≠ x
  cells : ∀ p ∈ C.cells, x ∉ exprVarsRv p.2
  pures : ∀ p ∈ C.pures, p.2 ≠ x ∧ x ∉ exprVarsRv p.1
  kecs : ∀ p ∈ C.kecs, p.2 ≠ x ∧ sigMentions x p.1.2.2 = false
  slds : ∀ p ∈ C.slds, p.2 ≠ x ∧ x ∉ exprVarsRv p.1

theorem XFree.kill (C : RvCache) (x : Ident) : XFree x (C.kill [x]) := by
  constructor
  · intro p hp
    simp only [RvCache.kill, List.mem_filter, Bool.and_eq_true,
      Bool.not_eq_true'] at hp
    obtain ⟨-, h1, h2⟩ := hp
    constructor
    · intro hx; rw [hx] at h1; simp at h1
    · intro hx; rw [hx] at h2; simp at h2
  · intro p hp
    simp only [RvCache.kill, List.mem_filter, Bool.not_eq_true'] at hp
    exact fun hx => (not_any_vars hp.2 x hx) (by simp)
  · intro p hp
    simp only [RvCache.kill, List.mem_filter, Bool.and_eq_true,
      Bool.not_eq_true'] at hp
    obtain ⟨-, h1, h2⟩ := hp
    refine ⟨?_, fun hx => (not_any_vars h2 x hx) (by simp)⟩
    intro hx; rw [hx] at h1; simp at h1
  · intro p hp
    simp only [RvCache.kill, List.mem_filter, Bool.and_eq_true,
      Bool.not_eq_true'] at hp
    obtain ⟨-, h1, h2⟩ := hp
    refine ⟨?_, ?_⟩
    · intro hx; rw [hx] at h1; simp at h1
    · have := List.any_eq_false.mp h2 x (by simp)
      simpa using this
  · intro p hp
    simp only [RvCache.kill, List.mem_filter, Bool.and_eq_true,
      Bool.not_eq_true'] at hp
    obtain ⟨-, h1, h2⟩ := hp
    refine ⟨?_, fun hx => (not_any_vars h2 x hx) (by simp)⟩
    intro hx; rw [hx] at h1; simp at h1

private theorem not_any_vars_kill {xs : List Ident} {vars : List Ident}
    (h : ∀ z ∈ vars, z ∉ xs) : xs.any (vars.contains ·) = false := by
  rw [List.any_eq_false]
  intro z hz
  simp only [List.contains_eq_mem, decide_eq_true_eq]
  intro hmem
  exact h z hmem hz

/-- An `x`-free cache stays valid when only `x`'s binding changes. -/
theorem RvOk.update_xfree {x : Ident} {C : RvCache} {V V' : VEnv D}
    {st : EvmState} (hc : RvOk V st C) (hxf : XFree x C)
    (hag : ∀ z, z ≠ x → VEnv.get V' z = VEnv.get V z) :
    RvOk V' st C := by
  constructor
  · intro p hp
    obtain ⟨v, h1, h2⟩ := hc.aliases p hp
    obtain ⟨hx1, hx2⟩ := hxf.aliases p hp
    exact ⟨v, by rw [hag p.1 hx1]; exact h1, by rw [hag p.2 hx2]; exact h2⟩
  · intro p hp
    obtain ⟨h1, h2, h3⟩ := hc.cells p hp
    refine ⟨?_, h2, h3⟩
    rw [evalPure_agree (fun z hz =>
      hag z (fun hzx => hxf.cells p hp (hzx ▸ hz)))]
    exact h1
  · intro p hp
    obtain ⟨w, h1, h2⟩ := hc.pures p hp
    obtain ⟨hx1, hx2⟩ := hxf.pures p hp
    refine ⟨w, ?_, by rw [hag p.2 hx1]; exact h2⟩
    rw [evalPure_agree (fun z hz => hag z (fun hzx => hx2 (hzx ▸ hz)))]
    exact h1
  · intro p hp
    obtain ⟨ws, h1, h2, h3⟩ := hc.kecs p hp
    obtain ⟨hx1, hx2⟩ := hxf.kecs p hp
    refine ⟨ws, ?_, by rw [hag p.2 hx1]; exact h2, h3⟩
    refine SigDen.agree h1 (fun q hq z hz => hag z ?_)
    intro hzx
    subst hzx
    simp only [sigMentions, List.any_eq_false] at hx2
    have := hx2 q hq
    simp [List.contains_eq_mem, hz] at this
  · intro p hp
    obtain ⟨k, h1, h2⟩ := hc.slds p hp
    obtain ⟨hx1, hx2⟩ := hxf.slds p hp
    refine ⟨k, ?_, by rw [hag p.2 hx1]; exact h2⟩
    rw [evalPure_agree (fun z hz => hag z (fun hzx => hx2 (hzx ▸ hz)))]
    exact h1

/-- `get` after prepending one binding. -/
theorem get_cons_ne {V : VEnv D} {x z : Ident}
    {v : (evmWithExternal calls creates).Value} (h : z ≠ x) :
    VEnv.get ((x, v) :: V) z = VEnv.get V z := by
  unfold VEnv.get
  rw [List.find?_cons_of_neg
    (by simpa using fun hc : x = z => h hc.symm)]

theorem get_cons_self {V : VEnv D} {x : Ident}
    {v : (evmWithExternal calls creates).Value} :
    VEnv.get ((x, v) :: V) x = some v := by
  unfold VEnv.get
  rw [List.find?_cons_of_pos (by simp)]
  rfl

theorem coverageSig_go_cells {C : RvCache} {base : Nat} :
    ∀ (n i : Nat) {sig : CellSig},
    coverageSig.go C base n i = some sig →
    ∀ q ∈ sig, ∃ p ∈ C.cells, q.2 = p.2
  | 0, i, sig, h => by
      simp only [coverageSig.go, Option.some.injEq] at h
      subst h
      intro q hq
      simp at hq
  | n + 1, i, sig, h => by
      simp only [coverageSig.go, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at h
      obtain ⟨v, hv, h⟩ := h
      obtain ⟨rest, hrest, h⟩ := h
      simp only [Option.pure_def, Option.some.injEq] at h
      subst h
      simp only [Option.map_eq_some_iff] at hv
      obtain ⟨q₀, hq₀, hv⟩ := hv
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq'
      · exact ⟨q₀, List.mem_of_find?_eq_some hq₀, hv.symm⟩
      · exact coverageSig_go_cells n (i + 1) hrest q hq'

/-- A coverage signature of an `x`-free cache never mentions `x`. -/
theorem coverageSig_xfree {x : Ident} {C : RvCache} (hxf : XFree x C)
    {base size : Nat} {sig : CellSig}
    (h : coverageSig C base size = some sig) :
    sigMentions x sig = false := by
  unfold coverageSig at h
  split at h
  · cases h
  · simp only [sigMentions, List.any_eq_false]
    intro q hq
    obtain ⟨p, hp, hqe⟩ := coverageSig_go_cells _ 0 h q hq
    simp only [List.contains_eq_mem, decide_eq_true_eq]
    rw [hqe]
    exact fun hmem => hxf.cells p hp hmem

theorem canonVar_ne {x : Ident} {C : RvCache} (hxf : XFree x C)
    {y : Ident} (hy : y ≠ x) : canonVar C y ≠ x := by
  unfold canonVar
  cases hf : C.aliases.find? (fun p => p.1 = y) with
  | none => simpa using hy
  | some p =>
      simp only [Option.map_some, Option.getD_some]
      exact (hxf.aliases p (List.mem_of_find?_eq_some hf)).2

/-! ### Classifier inversions -/

theorem keccakLits_inv {e : Expr Op} {a b : Nat}
    (h : keccakLits e = some (a, b)) :
    e = .builtin .keccak256 [.lit (.number a), .lit (.number b)] ∧
      a + b ≤ 2 ^ 256 ∧ b < 2 ^ 256 := by
  unfold keccakLits at h
  split at h
  · next a' b' =>
      split at h
      · next hb =>
          injection h with h
          injection h with h1 h2
          subst h1; subst h2
          exact ⟨rfl, hb.1, hb.2⟩
      · cases h
  · cases h

theorem sloadArg_inv {e : Expr Op} {k : Expr Op}
    (h : sloadArg e = some k) : e = .builtin .sload [k] := by
  unfold sloadArg at h
  split at h
  · injection h with h
    rw [h]
  · cases h

theorem mloadLit_inv {e : Expr Op} {k : Nat} (h : mloadLit e = some k) :
    e = .builtin .mload [.lit (.number k)] ∧ k + 32 ≤ 2 ^ 256 := by
  unfold mloadLit at h
  split at h
  · next k' =>
      split at h
      · next hb =>
          injection h with h
          subst h
          exact ⟨rfl, hb⟩
      · cases h
  · cases h

theorem mstoreLit_inv {e : Expr Op} {k : Nat} {v : Expr Op}
    (h : mstoreLit e = some (k, v)) :
    e = .builtin .mstore [.lit (.number k), v] ∧ k + 32 ≤ 2 ^ 256 := by
  unfold mstoreLit at h
  split at h
  · next k' v' =>
      split at h
      · next hb =>
          injection h with h
          injection h with h1 h2
          subst h1; subst h2
          exact ⟨rfl, hb⟩
      · cases h
  · cases h

theorem canonPure_go {C : RvCache} {e ce : Expr Op}
    (h : canonPure C e = some ce) : canonPureGo C e = some ce := by
  unfold canonPure at h
  split at h
  · cases h
  · exact h

/-- Construction: `keccak256` over in-range literals always evaluates. -/
theorem keccak_lit_eval {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (funs : FunEnv D) (V : VEnv D) (st : EvmState) :
    Step D funs V st
      (.expr (.builtin .keccak256 [.lit (.number a), .lit (.number b)]))
      (.eres (.vals [st.env.keccakOf (readBytes st.memory a b)]
        (touchMemory st a b))) := by
  have hta : (Dialect.litValue D (.number a)).toNat = a := by
    show (BitVec.ofNat 256 a).toNat = a
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
  have htb : (Dialect.litValue D (.number b)).toNat = b := by
    show (BitVec.ofNat 256 b).toNat = b
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
  refine Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil Step.lit)
    Step.lit) ?_
  show stepOp _ _ _ = _
  simp only [stepOp]
  rw [hta, htb]

/-- Construction: `mload` over an in-range literal always evaluates. -/
theorem mload_lit_eval {k : Nat} (hk : k < 2 ^ 256)
    (funs : FunEnv D) (V : VEnv D) (st : EvmState) :
    Step D funs V st (.expr (.builtin .mload [.lit (.number k)]))
      (.eres (.vals [loadWord st.memory k] (touchMemory st k 32))) := by
  have htk : (Dialect.litValue D (.number k)).toNat = k := by
    show (BitVec.ofNat 256 k).toNat = k
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
  refine Step.builtinOk (Step.argsCons Step.argsNil Step.lit) ?_
  show stepOp _ _ _ = _
  simp only [stepOp]
  rw [htk]

/-- Construction: `sload` over an evaluating key. -/
theorem sload_eval {k : Expr Op} {kv : U256} {V : VEnv D}
    (hkv : evalPure V k = some kv)
    (funs : FunEnv D) (st : EvmState) :
    Step D funs V st (.expr (.builtin .sload [k]))
      (.eres (.vals [st.storage kv] st)) := by
  refine Step.builtinOk (Step.argsCons Step.argsNil
    (evalPure_step hkv funs st)) ?_
  show stepOp _ _ _ = _
  simp only [stepOp]

/-! ### The forwarded right-hand side: rewrite transport -/

set_option maxHeartbeats 1600000 in
/-- Forward: a source evaluation of the original rhs is an evaluation of
the rewritten rhs, with the *same* result. -/
theorem rvRhs_fwd_step {C : RvCache} {x : Ident} {e e' : Expr Op}
    {C' : RvCache} (hp : rvRhs C x e = (e', C'))
    {V : VEnv D} {st : EvmState} (hc : RvOk V st C)
    {funs : FunEnv D} {res : Res D}
    (h : Step D funs V st (.expr e) res) :
    Step D funs V st (.expr e') res := by
  unfold rvRhs at hp
  split at hp
  · -- alias: the rhs is untouched
    injection hp with h1 _
    subst h1
    exact h
  · split at hp
    · -- keccak256 over literals
      next a b hke =>
        obtain ⟨rfl, hab, hblt⟩ := keccakLits_inv hke
        split at hp
        · next sig hcov =>
            obtain ⟨hsz, hnz, ws, hws, hload⟩ := coverageSig_den hc hcov
            have ha : a < 2 ^ 256 := by omega
            split at hp
            · -- hit: rewrite to the cached variable
              next key hvar hfind =>
                injection hp with h1 _
                subst h1
                have hqmem := List.mem_of_find?_eq_some hfind
                have hqpred := List.find?_some hfind
                simp only [Bool.and_eq_true, beq_iff_eq] at hqpred
                obtain ⟨⟨hka, hkb⟩, hksig⟩ := hqpred
                obtain ⟨ws₀, hws₀, hgh, hact⟩ := hc.kecs _ hqmem
                rw [sigBeq_eq _ _ hksig] at hws₀
                rw [SigDen.unique hws₀ hws] at hgh
                rw [keccak_lit_inv ha hblt h]
                rw [hka, hkb] at hact
                have hwslen : ws.length = sig.length := SigDen.length hws
                have hbytes : readBytes st.memory a b = wordsBytes ws := by
                  rw [hsz, ← hwslen]
                  exact readBytes_wordsBytes (fun i hi => by
                    have := hload i (by omega)
                    simpa using this)
                rw [(hact.touch_eq : touchMemory st a b = st)]
                refine Step.var ?_
                rw [hgh, ← hbytes]
        -- record and no-coverage arms keep the rhs
            · injection hp with h1 _
              subst h1
              exact h
        · injection hp with h1 _
          subst h1
          exact h
    · split at hp
      · -- sload
        next k hsl =>
          obtain rfl := sloadArg_inv hsl
          split at hp
          · next ck hck =>
              split at hp
              · -- hit
                next key w hfind =>
                  injection hp with h1 _
                  subst h1
                  have hqmem := List.mem_of_find?_eq_some hfind
                  have hqpred := List.find?_some hfind
                  have hkey : key = ck := exprBeq_eq _ _ hqpred
                  obtain ⟨kv₀, hkv₀, hgw⟩ := hc.slds _ hqmem
                  simp only at hkv₀ hgw
                  rw [hkey] at hkv₀
                  obtain ⟨kv, hkv, hres⟩ :=
                    sload_canon_inv (canonPure_go hck) h
                  rw [hres]
                  have hkveq : kv₀ = kv := by
                    rw [canonPure_eval hc hck, hkv] at hkv₀
                    injection hkv₀ with hv
                    exact hv.symm
                  refine Step.var ?_
                  rw [hgw, hkveq]
              · split at hp <;>
                  (injection hp with h1 _; subst h1; exact h)
          · split at hp <;> (injection hp with h1 _; subst h1; exact h)
      · split at hp
        · -- mload
          next k hml =>
            obtain ⟨rfl, hkb⟩ := mloadLit_inv hml
            have hk : k < 2 ^ 256 := by omega
            split at hp
            · next q v hfind =>
                injection hp with h1 _
                subst h1
                have hqmem := List.mem_of_find?_eq_some hfind
                have hkey : q = k := by
                  have := List.find?_some hfind
                  simpa using this
                obtain ⟨hcell, hact, -⟩ := hc.cells _ hqmem
                rw [mload_lit_inv hk h]
                rw [hkey] at hcell hact
                rw [(hact.touch_eq : touchMemory st k 32 = st)]
                refine Step.var ?_
                simpa [evalPure] using hcell
            · next q l hfind =>
                injection hp with h1 _
                subst h1
                have hqmem := List.mem_of_find?_eq_some hfind
                have hkey : q = k := by
                  have := List.find?_some hfind
                  simpa using this
                obtain ⟨hcell, hact, -⟩ := hc.cells _ hqmem
                rw [mload_lit_inv hk h]
                rw [hkey] at hcell hact
                rw [(hact.touch_eq : touchMemory st k 32 = st)]
                cases l with
                | number n =>
                    have : loadWord st.memory k =
                        Dialect.litValue D (.number n) := by
                      simpa [evalPure] using hcell.symm
                    rw [this]
                    exact Step.lit
                | string s => simp [evalPure] at hcell
                | bool b => simp [evalPure] at hcell
            · injection hp with h1 _
              subst h1
              exact h
        · split at hp
          · -- canonical pure
            next ce hce =>
              split at hp
              · injection hp with h1 _
                subst h1
                exact h
              · split at hp
                · -- hit
                  next key w hfind =>
                    injection hp with h1 _
                    subst h1
                    have hqmem := List.mem_of_find?_eq_some hfind
                    have hqpred := List.find?_some hfind
                    have hkey : key = ce := exprBeq_eq _ _ hqpred
                    obtain ⟨w₀, hw₀, hgw⟩ := hc.pures _ hqmem
                    simp only at hw₀ hgw
                    rw [hkey, canonPure_eval hc hce] at hw₀
                    obtain ⟨wv, hwv, hres⟩ :=
                      canonDom_step_inv (canonPure_go hce) _ _ _ _ h
                    rw [hres]
                    have hweq : w₀ = wv := by
                      rw [hwv] at hw₀
                      injection hw₀ with hv
                      exact hv.symm
                    refine Step.var ?_
                    rw [hgw, hweq]
                · split at hp <;> (injection hp with h1 _; subst h1; exact h)
          · split at hp <;> (injection hp with h1 _; subst h1; exact h)

set_option maxHeartbeats 1600000 in
/-- Backward: an evaluation of the rewritten rhs is an evaluation of the
original rhs, with the *same* result. -/
theorem rvRhs_bwd_step {C : RvCache} {x : Ident} {e e' : Expr Op}
    {C' : RvCache} (hp : rvRhs C x e = (e', C'))
    {V : VEnv D} {st : EvmState} (hc : RvOk V st C)
    {funs : FunEnv D} {res : Res D}
    (h : Step D funs V st (.expr e') res) :
    Step D funs V st (.expr e) res := by
  unfold rvRhs at hp
  split at hp
  · injection hp with h1 _
    subst h1
    exact h
  · split at hp
    · next a b hke =>
        obtain ⟨rfl, hab, hblt⟩ := keccakLits_inv hke
        split at hp
        · next sig hcov =>
            obtain ⟨hsz, hnz, ws, hws, hload⟩ := coverageSig_den hc hcov
            have ha : a < 2 ^ 256 := by omega
            split at hp
            · next key hvar hfind =>
                injection hp with h1 _
                subst h1
                have hqmem := List.mem_of_find?_eq_some hfind
                have hqpred := List.find?_some hfind
                simp only [Bool.and_eq_true, beq_iff_eq] at hqpred
                obtain ⟨⟨hka, hkb⟩, hksig⟩ := hqpred
                obtain ⟨ws₀, hws₀, hgh, hact⟩ := hc.kecs _ hqmem
                rw [sigBeq_eq _ _ hksig] at hws₀
                rw [SigDen.unique hws₀ hws] at hgh
                rw [hka, hkb] at hact
                have hwslen : ws.length = sig.length := SigDen.length hws
                have hbytes : readBytes st.memory a b = wordsBytes ws := by
                  rw [hsz, ← hwslen]
                  exact readBytes_wordsBytes (fun i hi => by
                    have := hload i (by omega)
                    simpa using this)
                cases h with
                | var hv =>
                    rw [hgh] at hv
                    injection hv with hv
                    have hev := keccak_lit_eval (calls := calls)
                      (creates := creates) ha hblt funs V st
                    rw [(hact.touch_eq : touchMemory st a b = st),
                      hbytes, hv] at hev
                    exact hev
            · injection hp with h1 _
              subst h1
              exact h
        · injection hp with h1 _
          subst h1
          exact h
    · split at hp
      · next k hsl =>
          obtain rfl := sloadArg_inv hsl
          split at hp
          · next ck hck =>
              split at hp
              · next key w hfind =>
                  injection hp with h1 _
                  subst h1
                  have hqmem := List.mem_of_find?_eq_some hfind
                  have hqpred := List.find?_some hfind
                  have hkey : key = ck := exprBeq_eq _ _ hqpred
                  obtain ⟨kv₀, hkv₀, hgw⟩ := hc.slds _ hqmem
                  simp only at hkv₀ hgw
                  rw [hkey, canonPure_eval hc hck] at hkv₀
                  cases h with
                  | var hv =>
                      rw [hgw] at hv
                      injection hv with hv
                      have hev := sload_eval (calls := calls)
                        (creates := creates) hkv₀ funs st
                      rw [hv] at hev
                      exact hev
              · split at hp <;>
                  (injection hp with h1 _; subst h1; exact h)
          · split at hp <;> (injection hp with h1 _; subst h1; exact h)
      · split at hp
        · next k hml =>
            obtain ⟨rfl, hkb⟩ := mloadLit_inv hml
            have hk : k < 2 ^ 256 := by omega
            split at hp
            · next q v hfind =>
                injection hp with h1 _
                subst h1
                have hqmem := List.mem_of_find?_eq_some hfind
                have hkey : q = k := by
                  have := List.find?_some hfind
                  simpa using this
                obtain ⟨hcell, hact, -⟩ := hc.cells _ hqmem
                rw [hkey] at hcell hact
                cases h with
                | var hv =>
                    have hev := mload_lit_eval (calls := calls)
                      (creates := creates) hk funs V st
                    rw [(hact.touch_eq : touchMemory st k 32 = st)] at hev
                    have hvv : VEnv.get V v =
                        some (loadWord st.memory k) := by
                      simpa [evalPure] using hcell
                    rw [hvv] at hv
                    injection hv with hv
                    rw [hv] at hev
                    exact hev
            · next q l hfind =>
                injection hp with h1 _
                subst h1
                have hqmem := List.mem_of_find?_eq_some hfind
                have hkey : q = k := by
                  have := List.find?_some hfind
                  simpa using this
                obtain ⟨hcell, hact, -⟩ := hc.cells _ hqmem
                rw [hkey] at hcell hact
                cases l with
                | number n =>
                    cases h with
                    | lit =>
                        have hev := mload_lit_eval (calls := calls)
                          (creates := creates) hk funs V st
                        rw [(hact.touch_eq : touchMemory st k 32 = st)] at hev
                        have : loadWord st.memory k =
                            Dialect.litValue D (.number n) := by
                          simpa [evalPure] using hcell.symm
                        rw [this] at hev
                        exact hev
                | string s => simp [evalPure] at hcell
                | bool b => simp [evalPure] at hcell
            · injection hp with h1 _
              subst h1
              exact h
        · split at hp
          · next ce hce =>
              split at hp
              · injection hp with h1 _
                subst h1
                exact h
              · split at hp
                · next key w hfind =>
                    injection hp with h1 _
                    subst h1
                    have hqmem := List.mem_of_find?_eq_some hfind
                    have hqpred := List.find?_some hfind
                    have hkey : key = ce := exprBeq_eq _ _ hqpred
                    obtain ⟨w₀, hw₀, hgw⟩ := hc.pures _ hqmem
                    simp only at hw₀ hgw
                    rw [hkey, canonPure_eval hc hce] at hw₀
                    cases h with
                    | var hv =>
                        rw [hgw] at hv
                        injection hv with hv
                        have hev := evalPure_step hw₀ funs st
                        rw [hv] at hev
                        exact hev
                · split at hp <;>
                    (injection hp with h1 _; subst h1; exact h)
          · split at hp <;> (injection hp with h1 _; subst h1; exact h)

/-- Alias facts recorded at a binding hold: the canonical representative
carries the bound value. -/
private theorem alias_holds_of_var {C : RvCache} {x y : Ident} {v : U256}
    {V V' : VEnv D} {st : EvmState} (hc : RvOk V st C) (hxf : XFree x C)
    (hgx : VEnv.get V' x = some v)
    (hag : ∀ z, z ≠ x → VEnv.get V' z = VEnv.get V z)
    (hy : VEnv.get V y = some v) :
    AliasHolds V' (x, canonVar C y) := by
  by_cases hyx : y = x
  · subst hyx
    have : canonVar C y = y := by
      unfold canonVar
      cases hf : C.aliases.find? (fun p => p.1 = y) with
      | none => rfl
      | some p =>
          have := (hxf.aliases p (List.mem_of_find?_eq_some hf)).1
          have hkey : p.1 = y := by simpa using List.find?_some hf
          exact absurd hkey this
    rw [this]
    exact ⟨v, hgx, hgx⟩
  · refine ⟨v, hgx, ?_⟩
    rw [hag _ (canonVar_ne hxf hyx), canonVar_get hc]
    exact hy

set_option maxHeartbeats 3200000 in
/-- After the binding executes, the extended cache is valid. -/
theorem rvRhs_ok {C : RvCache} {x : Ident} {e e' : Expr Op}
    {C' : RvCache} (hp : rvRhs C x e = (e', C'))
    {V V' : VEnv D} {st st₁ : EvmState} {v : U256}
    (hc : RvOk V st C) (hxf : XFree x C)
    (hgx : VEnv.get V' x = some v)
    (hag : ∀ z, z ≠ x → VEnv.get V' z = VEnv.get V z)
    {funs : FunEnv D}
    (hstep : Step D funs V st (.expr e) (.eres (.vals [v] st₁))) :
    RvOk V' st₁ C' := by
  unfold rvRhs at hp
  split at hp
  · -- alias record
    next y =>
      injection hp with h1 h2
      cases hstep with
      | var hv =>
          subst h2
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · intro p hp'
            rcases List.mem_cons.mp hp' with rfl | hp'
            · exact alias_holds_of_var hc hxf hgx hag hv
            · exact (hc.update_xfree hxf hag).aliases p hp'
          · exact (hc.update_xfree hxf hag).cells
          · exact (hc.update_xfree hxf hag).pures
          · exact (hc.update_xfree hxf hag).kecs
          · exact (hc.update_xfree hxf hag).slds
  · split at hp
    · next a b hke =>
        obtain ⟨rfl, hab, hblt⟩ := keccakLits_inv hke
        split at hp
        · next sig hcov =>
            obtain ⟨hsz, hnz, ws, hws, hload⟩ := coverageSig_den hc hcov
            have ha : a < 2 ^ 256 := by omega
            have hres := keccak_lit_inv ha hblt hstep
            injection hres with hres
            injection hres with hv1 hst1
            injection hv1 with hv1
            have hmn : MemNeutral st st₁ := by
              rw [hst1]
              exact MemNeutral.touch st (by omega) (by omega)
            have hbase := (hc.update_xfree hxf hag).memNeutral hmn
            split at hp
            · -- hit: alias record
              next key hvar hfind =>
                injection hp with h1 h2
                subst h2
                have hqmem := List.mem_of_find?_eq_some hfind
                have hqpred := List.find?_some hfind
                simp only [Bool.and_eq_true, beq_iff_eq] at hqpred
                obtain ⟨⟨hka, hkb⟩, hksig⟩ := hqpred
                obtain ⟨ws₀, hws₀, hgh, hact⟩ := hc.kecs _ hqmem
                rw [sigBeq_eq _ _ hksig] at hws₀
                rw [SigDen.unique hws₀ hws] at hgh
                rw [hka, hkb] at hact
                have hwslen : ws.length = sig.length := SigDen.length hws
                have hbytes : readBytes st.memory a b = wordsBytes ws := by
                  rw [hsz, ← hwslen]
                  exact readBytes_wordsBytes (fun i hi => by
                    have := hload i (by omega)
                    simpa using this)
                refine ⟨?_, hbase.cells, hbase.pures, hbase.kecs, hbase.slds⟩
                intro p hp'
                rcases List.mem_cons.mp hp' with rfl | hp'
                · exact alias_holds_of_var hc hxf hgx hag
                    (by rw [hgh, ← hbytes, ← hv1])
                · exact hbase.aliases p hp'
            · -- record a new keccak fact
              injection hp with h1 h2
              subst h2
              have hsigx : sigMentions x sig = false :=
                coverageSig_xfree hxf hcov
              refine ⟨hbase.aliases, hbase.cells, hbase.pures, ?_,
                hbase.slds⟩
              intro p hp'
              rcases List.mem_cons.mp hp' with rfl | hp'
              · refine ⟨ws, ?_, ?_, ?_⟩
                · refine SigDen.agree hws (fun q hq z hz => hag z ?_)
                  intro hzx
                  subst hzx
                  simp only [sigMentions, List.any_eq_false] at hsigx
                  have := hsigx q hq
                  simp [List.contains_eq_mem, hz] at this
                · show VEnv.get V' x = _
                  have hwslen : ws.length = sig.length := SigDen.length hws
                  have hbytes : readBytes st.memory a b = wordsBytes ws := by
                    rw [hsz, ← hwslen]
                    exact readBytes_wordsBytes (fun i hi => by
                      have := hload i (by omega)
                      simpa using this)
                  rw [hgx, hv1, hbytes, hmn.keccak]
                · show RangeActive st₁ _ _
                  rw [hst1]
                  exact touch_covers st hnz (by omega)
              · exact hbase.kecs p hp'
        · -- no coverage: cache carried across the touch
          injection hp with h1 h2
          subst h2
          obtain ⟨vs, st', hres, hmn⟩ := rvNeutral_step
            (show rvNeutralExpr (.builtin .keccak256
              [.lit (.number a), .lit (.number b)]) = true from rfl)
            _ _ _ _ hstep
          injection hres with hres
          injection hres with hv1 hst1
          rw [hst1]
          exact (hc.update_xfree hxf hag).memNeutral hmn
    · split at hp
      · next k hsl =>
          obtain rfl := sloadArg_inv hsl
          split at hp
          · next ck hck =>
              obtain ⟨kv, hkv, hres⟩ :=
                sload_canon_inv (canonPure_go hck) hstep
              injection hres with hres
              injection hres with hv1 hst1
              injection hv1 with hv1
              have hbase : RvOk V' st₁ C := by
                rw [hst1]
                exact hc.update_xfree hxf hag
              split at hp
              · -- hit: alias record
                next key w hfind =>
                  injection hp with h1 h2
                  subst h2
                  have hqmem := List.mem_of_find?_eq_some hfind
                  have hqpred := List.find?_some hfind
                  have hkey : key = ck := exprBeq_eq _ _ hqpred
                  obtain ⟨kv₀, hkv₀, hgw⟩ := hc.slds _ hqmem
                  simp only at hkv₀ hgw
                  rw [hkey, canonPure_eval hc hck, hkv] at hkv₀
                  injection hkv₀ with hkv₀
                  refine ⟨?_, hbase.cells, hbase.pures, hbase.kecs,
                    hbase.slds⟩
                  intro p hp'
                  rcases List.mem_cons.mp hp' with rfl | hp'
                  · exact alias_holds_of_var hc hxf hgx hag
                      (by rw [hgw, ← hkv₀, ← hv1])
                  · exact hbase.aliases p hp'
              · split at hp
                · -- self-referential: no record
                  injection hp with h1 h2
                  subst h2
                  exact hbase
                · -- record a new storage-read fact
                  next hxg =>
                    injection hp with h1 h2
                    subst h2
                    refine ⟨hbase.aliases, hbase.cells, hbase.pures,
                      hbase.kecs, ?_⟩
                    intro p hp'
                    rcases List.mem_cons.mp hp' with rfl | hp'
                    · refine ⟨kv, ?_, ?_⟩
                      · show evalPure V' ck = some kv
                        rw [evalPure_agree (V := V) (fun z hz => hag z ?_),
                          canonPure_eval hc hck]
                        · exact hkv
                        · intro hzx
                          subst hzx
                          simp [List.contains_eq_mem, hz] at hxg
                      · show VEnv.get V' x = some (st₁.storage kv)
                        rw [hgx, hst1, hv1]
                    · exact hbase.slds p hp'
          · -- non-canonical key: neutrality check
            split at hp
            · next hne =>
                injection hp with h1 h2
                subst h2
                obtain ⟨vs, st', hres, hmn⟩ :=
                  rvNeutral_step hne _ _ _ _ hstep
                injection hres with hres
                injection hres with hv1 hst1
                rw [hst1]
                exact (hc.update_xfree hxf hag).memNeutral hmn
            · injection hp with h1 h2
              subst h2
              exact RvOk.empty _ _
      · split at hp
        · next k hml =>
            obtain ⟨rfl, hkb⟩ := mloadLit_inv hml
            have hk : k < 2 ^ 256 := by omega
            have hres := mload_lit_inv hk hstep
            injection hres with hres
            injection hres with hv1 hst1
            injection hv1 with hv1
            have hmn : MemNeutral st st₁ := by
              rw [hst1]
              exact MemNeutral.touch st (by omega) (by omega)
            have hbase := (hc.update_xfree hxf hag).memNeutral hmn
            split at hp
            · next q vv hfind =>
                injection hp with h1 h2
                subst h2
                have hqmem := List.mem_of_find?_eq_some hfind
                have hkey : q = k := by
                  have := List.find?_some hfind
                  simpa using this
                obtain ⟨hcell, hact, -⟩ := hc.cells _ hqmem
                rw [hkey] at hcell
                refine ⟨?_, hbase.cells, hbase.pures, hbase.kecs,
                  hbase.slds⟩
                intro p hp'
                rcases List.mem_cons.mp hp' with rfl | hp'
                · refine alias_holds_of_var hc hxf hgx hag ?_
                  have : VEnv.get V vv = some (loadWord st.memory k) := by
                    simpa [evalPure] using hcell
                  rw [this, ← hv1]
                · exact hbase.aliases p hp'
            · injection hp with h1 h2
              subst h2
              exact hbase
            · injection hp with h1 h2
              subst h2
              exact hbase
        · split at hp
          · next ce hce =>
              obtain ⟨wv, hwv, hres⟩ :=
                canonDom_step_inv (canonPure_go hce) _ _ _ _ hstep
              injection hres with hres
              injection hres with hv1 hst1
              injection hv1 with hv1
              have hbase : RvOk V' st₁ C := by
                rw [hst1]
                exact hc.update_xfree hxf hag
              split at hp
              · injection hp with h1 h2
                subst h2
                exact hbase
              · split at hp
                · -- hit: alias record
                  next key w hfind =>
                    injection hp with h1 h2
                    subst h2
                    have hqmem := List.mem_of_find?_eq_some hfind
                    have hqpred := List.find?_some hfind
                    have hkey : key = ce := exprBeq_eq _ _ hqpred
                    obtain ⟨w₀, hw₀, hgw⟩ := hc.pures _ hqmem
                    simp only at hw₀ hgw
                    rw [hkey, canonPure_eval hc hce, hwv] at hw₀
                    injection hw₀ with hw₀
                    refine ⟨?_, hbase.cells, hbase.pures, hbase.kecs,
                      hbase.slds⟩
                    intro p hp'
                    rcases List.mem_cons.mp hp' with rfl | hp'
                    · exact alias_holds_of_var hc hxf hgx hag
                        (by rw [hgw, ← hw₀, ← hv1])
                    · exact hbase.aliases p hp'
                · split at hp
                  · injection hp with h1 h2
                    subst h2
                    exact hbase
                  · -- record a new pure fact
                    next hxg =>
                      injection hp with h1 h2
                      subst h2
                      refine ⟨hbase.aliases, hbase.cells, ?_, hbase.kecs,
                        hbase.slds⟩
                      intro p hp'
                      rcases List.mem_cons.mp hp' with rfl | hp'
                      · refine ⟨v, ?_, hgx⟩
                        show evalPure V' ce = some v
                        rw [evalPure_agree (V := V) (fun z hz => hag z ?_),
                          canonPure_eval hc hce, hwv, hv1]
                        intro hzx
                        subst hzx
                        simp [List.contains_eq_mem, hz] at hxg
                      · exact hbase.pures p hp'
          · split at hp
            · next hne =>
                injection hp with h1 h2
                subst h2
                obtain ⟨vs, st', hres, hmn⟩ :=
                  rvNeutral_step hne _ _ _ _ hstep
                injection hres with hres
                injection hres with hv1 hst1
                rw [hst1]
                exact (hc.update_xfree hxf hag).memNeutral hmn
            · injection hp with h1 h2
              subst h2
              exact RvOk.empty _ _

/-! ### Kill across the environment transitions of the semantics -/

theorem RvOk.kill_prepend {V : VEnv D} {st : EvmState} {C : RvCache}
    (hc : RvOk V st C) (xs : List Ident) (vs : List U256) :
    RvOk ((xs.zip vs : VEnv D) ++ V) st (C.kill xs) := by
  refine RvOk.kill (V' := (xs.zip vs : VEnv D) ++ V) hc xs (fun z hz => ?_)
  refine YulEvmCompiler.Optimizer.VEnv.get_append_not_mem ?_
  intro hmem
  obtain ⟨q, hq, hqz⟩ := List.mem_map.mp hmem
  exact hz (hqz ▸ (List.of_mem_zip hq).1)

theorem RvOk.kill_bindZeros {V : VEnv D} {st : EvmState} {C : RvCache}
    (hc : RvOk V st C) (xs : List Ident) :
    RvOk (bindZeros D xs ++ V) st (C.kill xs) := by
  refine RvOk.kill (V' := bindZeros D xs ++ V) hc xs (fun z hz => ?_)
  refine YulEvmCompiler.Optimizer.VEnv.get_append_not_mem ?_
  rw [bindZeros_keys]
  exact hz

theorem RvOk.kill_setMany {V : VEnv D} {st : EvmState} {C : RvCache}
    (hc : RvOk V st C) (xs : List Ident) (vs : List U256) :
    RvOk (VEnv.setMany V xs vs) st (C.kill xs) := by
  refine RvOk.kill (V' := VEnv.setMany V xs vs) hc xs (fun z hz => ?_)
  exact YulEvmCompiler.Optimizer.VEnv.get_setMany_not_mem hz

theorem RvOk.kill_restore {ds : List Ident} {V V' : VEnv D}
    {st : EvmState} {C : RvCache} (hc : RvOk V' st C)
    (hf : ScopeFrame ds V V') :
    RvOk (restore V V') st (C.kill ds) := by
  refine RvOk.kill (V' := restore V V') hc ds (fun z hz => ?_)
  exact hf.restore_get_eq hz

/-! ### Statement-level rewrites -/

theorem rvLet_some (C : RvCache) (xs : List Ident) (e : Expr Op) :
    ∃ e' C', rvLet C xs (some e) = (some e', C') := by
  unfold rvLet
  match xs with
  | [x] => exact ⟨_, _, rfl⟩
  | [] =>
      dsimp only
      split
      · exact ⟨_, _, rfl⟩
      · exact ⟨_, _, rfl⟩
  | _ :: _ :: _ =>
      dsimp only
      split
      · exact ⟨_, _, rfl⟩
      · exact ⟨_, _, rfl⟩

theorem rvLet_none (C : RvCache) (xs : List Ident) :
    rvLet C xs none = (none, C.kill xs) := by
  unfold rvLet
  match xs with
  | [] => rfl
  | [x] => rfl
  | _ :: _ :: _ => rfl

set_option maxHeartbeats 800000 in
theorem rvLet_expr_fwd {C : RvCache} {xs : List Ident} {e e' : Expr Op}
    {C' : RvCache} (hp : rvLet C xs (some e) = (some e', C'))
    {V : VEnv D} {st : EvmState} (hc : RvOk V st C)
    {funs : FunEnv D} {res : Res D}
    (h : Step D funs V st (.expr e) res) :
    Step D funs V st (.expr e') res ∧
      (∀ vals st₁, res = .eres (.vals vals st₁) → vals.length = xs.length →
        RvOk (xs.zip vals ++ V) st₁ C') := by
  have hcatch : (if rvNeutralExpr e = true then (some e, C.kill xs)
        else ((some e : Option (Expr Op)), RvCache.empty)) = (some e', C') →
      Step D funs V st (.expr e') res ∧
      (∀ vals st₁, res = .eres (.vals vals st₁) → vals.length = xs.length →
        RvOk (xs.zip vals ++ V) st₁ C') := by
    intro hp'
    split at hp'
    · next hne =>
        injection hp' with h1 h2
        injection h1 with h1
        subst h1
        refine ⟨h, ?_⟩
        intro vals st₁ hres hlen
        subst hres
        obtain ⟨vs', st', hres', hmn⟩ := rvNeutral_step hne _ _ _ _ h
        injection hres' with hres'
        injection hres' with hv1 hst1
        rw [← h2, hst1]
        exact (hc.kill_prepend _ _).memNeutral hmn
    · injection hp' with h1 h2
      injection h1 with h1
      subst h1
      refine ⟨h, ?_⟩
      intro vals st₁ hres hlen
      rw [← h2]
      exact RvOk.empty _ _
  rcases xs with _ | ⟨x, _ | ⟨y, rest⟩⟩
  · exact hcatch hp
  · unfold rvLet at hp
    injection hp with h1 h2
    injection h1 with h1
    have hkill : RvOk V st (C.kill [x]) := hc.kill [x] (fun _ _ => rfl)
    have hrv : rvRhs (C.kill [x]) x e = (e', C') := by
      rcases hq : rvRhs (C.kill [x]) x e with ⟨a, b⟩
      rw [hq] at h1 h2
      simp only at h1 h2
      rw [h1, h2]
    constructor
    · exact rvRhs_fwd_step hrv hkill h
    · intro vals st₁ hres hlen
      obtain ⟨v, rfl⟩ := List.length_eq_one_iff.mp hlen
      subst hres
      show RvOk ((x, v) :: V) st₁ _
      exact rvRhs_ok hrv hkill (XFree.kill C x)
        get_cons_self (fun z hz => get_cons_ne hz) h
  · exact hcatch hp

theorem rvLet_expr_bwd {C : RvCache} {xs : List Ident} {e e' : Expr Op}
    {C' : RvCache} (hp : rvLet C xs (some e) = (some e', C'))
    {V : VEnv D} {st : EvmState} (hc : RvOk V st C)
    {funs : FunEnv D} {res : Res D}
    (h : Step D funs V st (.expr e') res) :
    Step D funs V st (.expr e) res := by
  have hcatch : (if rvNeutralExpr e = true then (some e, C.kill xs)
        else ((some e : Option (Expr Op)), RvCache.empty)) = (some e', C') →
      Step D funs V st (.expr e) res := by
    intro hp'
    split at hp' <;>
      (injection hp' with h1 h2; injection h1 with h1; subst h1; exact h)
  rcases xs with _ | ⟨x, _ | ⟨y, rest⟩⟩
  · exact hcatch hp
  · unfold rvLet at hp
    injection hp with h1 h2
    injection h1 with h1
    have hkill : RvOk V st (C.kill [x]) := hc.kill [x] (fun _ _ => rfl)
    have hrv : rvRhs (C.kill [x]) x e = (e', C') := by
      rcases hq : rvRhs (C.kill [x]) x e with ⟨a, b⟩
      rw [hq] at h1 h2
      simp only at h1 h2
      rw [h1, h2]
    exact rvRhs_bwd_step hrv hkill h
  · exact hcatch hp

set_option maxHeartbeats 800000 in
theorem rvAssign_expr_fwd {bound : List Ident} {C : RvCache}
    {xs : List Ident} {e e' : Expr Op} {C' : RvCache}
    (hp : rvAssign bound C xs e = (e', C'))
    {V : VEnv D} {st : EvmState} (hc : RvOk V st C) (hb : BoundOK V bound)
    {funs : FunEnv D} {res : Res D}
    (h : Step D funs V st (.expr e) res) :
    Step D funs V st (.expr e') res ∧
      (∀ vals st₁, res = .eres (.vals vals st₁) → vals.length = xs.length →
        RvOk (VEnv.setMany V xs vals) st₁ C') := by
  have hcatch : (if rvNeutralExpr e = true then (e, C.kill xs)
        else (e, RvCache.empty)) = (e', C') →
      Step D funs V st (.expr e') res ∧
      (∀ vals st₁, res = .eres (.vals vals st₁) → vals.length = xs.length →
        RvOk (VEnv.setMany V xs vals) st₁ C') := by
    intro hp'
    split at hp'
    · next hne =>
        injection hp' with h1 h2
        subst h1
        refine ⟨h, ?_⟩
        intro vals st₁ hres hlen
        subst hres
        obtain ⟨vs', st', hres', hmn⟩ := rvNeutral_step hne _ _ _ _ h
        injection hres' with hres'
        injection hres' with hv1 hst1
        rw [← h2, hst1]
        exact (hc.kill_setMany _ _).memNeutral hmn
    · injection hp' with h1 h2
      subst h1
      refine ⟨h, ?_⟩
      intro vals st₁ hres hlen
      rw [← h2]
      exact RvOk.empty _ _
  rcases xs with _ | ⟨x, _ | ⟨y, rest⟩⟩
  · exact hcatch hp
  · unfold rvAssign at hp
    dsimp only at hp
    split at hp
    · next hbx =>
        have hkill : RvOk V st (C.kill [x]) := hc.kill [x] (fun _ _ => rfl)
        have hrv : rvRhs (C.kill [x]) x e = (e', C') := hp
        constructor
        · exact rvRhs_fwd_step hrv hkill h
        · intro vals st₁ hres hlen
          obtain ⟨v, rfl⟩ := List.length_eq_one_iff.mp hlen
          subst hres
          rw [YulEvmCompiler.Optimizer.VEnv.setMany_singleton]
          have hxsome : (VEnv.get V x).isSome :=
            YulEvmCompiler.Optimizer.BoundOK.get_isSome hb hbx
          exact rvRhs_ok hrv hkill (XFree.kill C x)
            (YulEvmCompiler.Optimizer.VEnv.get_set_self hxsome)
            (fun z hz => YulEvmCompiler.Optimizer.VEnv.get_set_ne hz) h
    · exact hcatch hp
  · exact hcatch hp

theorem rvAssign_expr_bwd {bound : List Ident} {C : RvCache}
    {xs : List Ident} {e e' : Expr Op} {C' : RvCache}
    (hp : rvAssign bound C xs e = (e', C'))
    {V : VEnv D} {st : EvmState} (hc : RvOk V st C)
    {funs : FunEnv D} {res : Res D}
    (h : Step D funs V st (.expr e') res) :
    Step D funs V st (.expr e) res := by
  have hcatch : (if rvNeutralExpr e = true then (e, C.kill xs)
        else (e, RvCache.empty)) = (e', C') →
      Step D funs V st (.expr e) res := by
    intro hp'
    split at hp' <;> (injection hp' with h1 h2; subst h1; exact h)
  rcases xs with _ | ⟨x, _ | ⟨y, rest⟩⟩
  · exact hcatch hp
  · unfold rvAssign at hp
    dsimp only at hp
    split at hp
    · next hbx =>
        have hkill : RvOk V st (C.kill [x]) := hc.kill [x] (fun _ _ => rfl)
        exact rvRhs_bwd_step hp hkill h
    · exact hcatch hp
  · exact hcatch hp

theorem rvExprStmt_fst (C : RvCache) (e : Expr Op) :
    (rvExprStmt C e).1 = e := by
  unfold rvExprStmt
  split
  · split <;> rfl
  · split
    · split <;> rfl
    · split <;> rfl
    · split <;> rfl

set_option maxHeartbeats 800000 in
/-- The expression-statement sweep: the expression is unchanged, and the
updated cache is valid after a completed evaluation. -/
theorem rvExprStmt_ok {C : RvCache} {e e' : Expr Op} {C' : RvCache}
    (hp : rvExprStmt C e = (e', C'))
    {V : VEnv D} {st : EvmState} (hc : RvOk V st C)
    {funs : FunEnv D} {res : Res D}
    (h : Step D funs V st (.expr e) res) :
    e' = e ∧ (∀ st₁, res = .eres (.vals [] st₁) → RvOk V st₁ C') := by
  have hfst := rvExprStmt_fst C e
  rw [hp] at hfst
  simp only at hfst
  subst hfst
  refine ⟨rfl, ?_⟩
  intro st₁ hres
  unfold rvExprStmt at hp
  split at hp
  · -- mstore at a checked literal
    next k v hml =>
      obtain ⟨rfl, hkb⟩ := mstoreLit_inv hml
      have hk : k < 2 ^ 256 := by omega
      split at hp
      · next hnv =>
          injection hp with h1 h2
          rcases mstore_lit_inv hk h with
            ⟨vv, stv, hv, hres'⟩ | ⟨stv, hv, hres'⟩
          · rw [hres] at hres'
            injection hres' with hres'
            injection hres' with hv1 hst1
            obtain ⟨vs', st', hresn, hmn⟩ := rvNeutral_step hnv _ _ _ _ hv
            injection hresn with hresn
            injection hresn with hnv1 hnst1
            have hcv : RvOk V stv C := by
              rw [hnst1]
              exact hc.memNeutral hmn
            have hbase := hcv.mstore (v := vv) hkb
            rw [← h2]
            cases hcp : canonPure C v with
            | none =>
                show RvOk V st₁ (C.putCell k none)
                rw [hst1]
                exact hbase
            | some cv =>
                -- a pure store: the evaluation kept the state, and the
                -- stored word now denotes the canonical value
                obtain ⟨wv, hwv, hresp⟩ :=
                  canonDom_step_inv (canonPure_go hcp) _ _ _ _ hv
                injection hresp with hresp
                injection hresp with hpv1 hpst1
                injection hpv1 with hpv1
                show RvOk V st₁ (C.putCell k (some cv))
                rw [hst1]
                constructor
                · exact hbase.aliases
                · intro p hp'
                  simp only [RvCache.putCell, List.mem_cons] at hp'
                  rcases hp' with rfl | hp'
                  · refine ⟨?_, ?_, hkb⟩
                    · show evalPure V cv = _
                      rw [canonPure_eval hcv hcp, hwv]
                      congr 1
                      rw [hpv1,
                        YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord]
                    · exact touch_covers stv (by omega) (by omega)
                  · exact hbase.cells p (by
                      simpa [RvCache.putCell] using hp')
                · exact hbase.pures
                · exact hbase.kecs
                · exact hbase.slds
          · rw [hres] at hres'
            cases hres'
      · injection hp with h1 h2
        rw [← h2]
        exact RvOk.empty _ _
  · split at hp
    · -- sstore with neutral operands
      next args hlen' =>
        split at hp
        · next hn =>
            simp only [Bool.and_eq_true, beq_iff_eq] at hn
            injection hp with h1 h2
            rcases sstore_neutral_inv hn.2 h with
              ⟨stm, st₂, hmn, hres', hmem, hkec, hact⟩ | ⟨st', hres'⟩
            · rw [hres] at hres'
              injection hres' with hres'
              injection hres' with hv1 hst1
              rw [← h2, hst1]
              exact ((hc.memNeutral hmn).sstoreKill hmem hkec hact)
            · rw [hres] at hres'
              cases hres'
        · injection hp with h1 h2
          rw [← h2]
          exact RvOk.empty _ _
    · -- an unchecked mstore is never neutral
      next args =>
        split at hp
        · next hn => exact absurd hn Bool.false_ne_true
        · injection hp with h1 h2
          rw [← h2]
          exact RvOk.empty _ _
    · split at hp
      · next hn =>
          injection hp with h1 h2
          obtain ⟨vs', st', hres', hmn⟩ := rvNeutral_step hn _ _ _ _ h
          rw [hres] at hres'
          injection hres' with hres'
          injection hres' with hv1 hst1
          rw [← h2, hst1]
          exact hc.memNeutral hmn
      · injection hp with h1 h2
        rw [← h2]
        exact RvOk.empty _ _

/-! ### The code-indexed transform relation (the `StorageForward` shape) -/

def rvBoundStmts : List Ident → List (Stmt Op) → List Ident
  | bound, [] => bound
  | bound, s :: rest => rvBoundStmts (rvNextBound bound s) rest

def rvCode (bound : List Ident) (C : RvCache) : Code Op → Code Op × RvCache
  | .expr e => (.expr e, RvCache.empty)
  | .args es => (.args es, RvCache.empty)
  | .stmt s => let p := rvStmt bound C s; (.stmt p.1, p.2)
  | .stmts ss => let p := rvStmts bound C ss; (.stmts p.1, p.2)
  | .loop c post body => (.loop c post body, RvCache.empty)

def rvBound (bound : List Ident) : Code Op → List Ident
  | .stmt s => rvNextBound bound s
  | .stmts ss => rvBoundStmts bound ss
  | _ => bound

def RvRel (bound : List Ident) (C C' : RvCache) (code code' : Code Op) :
    Prop :=
  rvCode bound C code = (code', C')

theorem RvRel.expr_eq {bound : List Ident} {C C' : RvCache} {code : Code Op}
    {e : Expr Op} (h : RvRel bound C C' code (.expr e)) : code = .expr e := by
  cases code <;> simp_all [RvRel, rvCode]

theorem RvRel.args_eq {bound : List Ident} {C C' : RvCache} {code : Code Op}
    {es : List (Expr Op)} (h : RvRel bound C C' code (.args es)) :
    code = .args es := by
  cases code <;> simp_all [RvRel, rvCode]

theorem RvRel.loop_eq {bound : List Ident} {C C' : RvCache} {code : Code Op}
    {c : Expr Op} {post body : Block Op}
    (h : RvRel bound C C' code (.loop c post body)) :
    code = .loop c post body := by
  cases code <;> simp_all [RvRel, rvCode]

set_option linter.unusedSimpArgs false in
theorem RvRel.let_inv {bound : List Ident} {C C' : RvCache} {code : Code Op}
    {xs : List Ident} {rhs' : Option (Expr Op)}
    (h : RvRel bound C C' code (.stmt (.letDecl xs rhs'))) :
    ∃ rhs, code = .stmt (.letDecl xs rhs) ∧ rvLet C xs rhs = (rhs', C') := by
  cases code with
  | stmt s =>
      cases s with
      | letDecl vars val =>
          simp only [RvRel, rvCode, rvStmt, Prod.mk.injEq, Code.stmt.injEq,
            Stmt.letDecl.injEq] at h
          obtain ⟨⟨hvars, hfst⟩, hsnd⟩ := h
          subst vars
          exact ⟨val, rfl, Prod.ext hfst hsnd⟩
      | block body => simp [RvRel, rvCode, rvStmt] at h
      | funDef n ps rs body => simp [RvRel, rvCode, rvStmt] at h
      | assign vars val => simp [RvRel, rvCode, rvStmt] at h
      | cond c body => simp [RvRel, rvCode, rvStmt] at h
      | switch c cases dflt => simp [RvRel, rvCode, rvStmt] at h
      | forLoop init c post body => simp [RvRel, rvCode, rvStmt] at h
      | exprStmt e => simp [RvRel, rvCode, rvStmt, rvExprStmt_fst] at h
      | «break» => simp [RvRel, rvCode, rvStmt] at h
      | «continue» => simp [RvRel, rvCode, rvStmt] at h
      | leave => simp [RvRel, rvCode, rvStmt] at h
  | expr e => simp [RvRel, rvCode] at h
  | args es => simp [RvRel, rvCode] at h
  | stmts ss => simp [RvRel, rvCode] at h
  | loop c post body => simp [RvRel, rvCode] at h

set_option linter.unusedSimpArgs false in
theorem RvRel.assign_inv {bound : List Ident} {C C' : RvCache}
    {code : Code Op} {xs : List Ident} {rhs' : Expr Op}
    (h : RvRel bound C C' code (.stmt (.assign xs rhs'))) :
    ∃ rhs, code = .stmt (.assign xs rhs) ∧
      rvAssign bound C xs rhs = (rhs', C') := by
  cases code with
  | stmt s =>
      cases s with
      | assign vars val =>
          simp only [RvRel, rvCode, rvStmt, Prod.mk.injEq, Code.stmt.injEq,
            Stmt.assign.injEq] at h
          obtain ⟨⟨hvars, hfst⟩, hsnd⟩ := h
          subst vars
          exact ⟨val, rfl, Prod.ext hfst hsnd⟩
      | block body => simp [RvRel, rvCode, rvStmt] at h
      | funDef n ps rs body => simp [RvRel, rvCode, rvStmt] at h
      | letDecl vars val => simp [RvRel, rvCode, rvStmt] at h
      | cond c body => simp [RvRel, rvCode, rvStmt] at h
      | switch c cases dflt => simp [RvRel, rvCode, rvStmt] at h
      | forLoop init c post body => simp [RvRel, rvCode, rvStmt] at h
      | exprStmt e => simp [RvRel, rvCode, rvStmt, rvExprStmt_fst] at h
      | «break» => simp [RvRel, rvCode, rvStmt] at h
      | «continue» => simp [RvRel, rvCode, rvStmt] at h
      | leave => simp [RvRel, rvCode, rvStmt] at h
  | expr e => simp [RvRel, rvCode] at h
  | args es => simp [RvRel, rvCode] at h
  | stmts ss => simp [RvRel, rvCode] at h
  | loop c post body => simp [RvRel, rvCode] at h

set_option linter.unusedSimpArgs false in
theorem RvRel.exprStmt_inv {bound : List Ident} {C C' : RvCache}
    {code : Code Op} {e' : Expr Op}
    (h : RvRel bound C C' code (.stmt (.exprStmt e'))) :
    code = .stmt (.exprStmt e') ∧ (rvExprStmt C e').2 = C' := by
  cases code with
  | stmt s =>
      cases s with
      | exprStmt e =>
          have hfst := rvExprStmt_fst C e
          simp only [RvRel, rvCode, rvStmt, Prod.mk.injEq,
            Code.stmt.injEq, Stmt.exprStmt.injEq] at h
          obtain ⟨h1, h2⟩ := h
          rw [hfst] at h1
          subst h1
          exact ⟨rfl, h2⟩
      | block body => simp [RvRel, rvCode, rvStmt] at h
      | funDef n ps rs body => simp [RvRel, rvCode, rvStmt] at h
      | letDecl vars val => simp [RvRel, rvCode, rvStmt] at h
      | assign vars val => simp [RvRel, rvCode, rvStmt] at h
      | cond c body => simp [RvRel, rvCode, rvStmt] at h
      | switch c cases dflt => simp [RvRel, rvCode, rvStmt] at h
      | forLoop init c post body => simp [RvRel, rvCode, rvStmt] at h
      | «break» => simp [RvRel, rvCode, rvStmt] at h
      | «continue» => simp [RvRel, rvCode, rvStmt] at h
      | leave => simp [RvRel, rvCode, rvStmt] at h
  | expr e => simp [RvRel, rvCode] at h
  | args es => simp [RvRel, rvCode] at h
  | stmts ss => simp [RvRel, rvCode] at h
  | loop c post body => simp [RvRel, rvCode] at h

set_option linter.unusedSimpArgs false in
theorem RvRel.cond_inv {bound : List Ident} {C C' : RvCache}
    {code : Code Op} {c : Expr Op} {body' : Block Op}
    (h : RvRel bound C C' code (.stmt (.cond c body'))) :
    ∃ body, code = .stmt (.cond c body) ∧
      body' = (rvStmts bound RvCache.empty body).1 ∧
      C' = if rvNeutralExpr c && stmtsNoNormal body then C
           else RvCache.empty := by
  cases code with
  | stmt s =>
      cases s <;> simp_all [RvRel, rvCode, rvStmt]
      simpa [h.1.1] using h.2.symm
  | expr e => simp [RvRel, rvCode] at h
  | args es => simp [RvRel, rvCode] at h
  | stmts ss => simp [RvRel, rvCode] at h
  | loop c post body => simp [RvRel, rvCode] at h

set_option linter.unusedSimpArgs false in
theorem RvRel.stmts_nil_inv {bound : List Ident} {C C' : RvCache}
    {code : Code Op} (h : RvRel bound C C' code (.stmts [])) :
    code = .stmts [] := by
  cases code with
  | stmts ss => cases ss <;> simp_all [RvRel, rvCode, rvStmts]
  | expr e => simp [RvRel, rvCode] at h
  | args es => simp [RvRel, rvCode] at h
  | stmt s => simp [RvRel, rvCode] at h
  | loop c post body => simp [RvRel, rvCode] at h

set_option linter.unusedSimpArgs false in
theorem RvRel.stmts_cons_inv {bound : List Ident} {C C' : RvCache}
    {code : Code Op} {s' : Stmt Op} {rest' : List (Stmt Op)}
    (h : RvRel bound C C' code (.stmts (s' :: rest'))) :
    ∃ s rest C1, code = .stmts (s :: rest) ∧ rvStmt bound C s = (s', C1) ∧
      rvStmts (rvNextBound bound s) C1 rest = (rest', C') := by
  cases code with
  | stmts ss =>
      cases ss with
      | nil => simp [RvRel, rvCode, rvStmts] at h
      | cons s rest =>
          generalize hs : rvStmt bound C s = p
          rcases p with ⟨st', C1⟩
          simp only [RvRel, rvCode, rvStmts, hs, Prod.mk.injEq,
            Code.stmts.injEq, List.cons.injEq] at h
          obtain ⟨⟨hst, hrest⟩, hcache⟩ := h
          subst hst
          exact ⟨s, rest, C1, rfl, hs, Prod.ext hrest hcache⟩
  | expr e => simp [RvRel, rvCode] at h
  | args es => simp [RvRel, rvCode] at h
  | stmt s => simp [RvRel, rvCode] at h
  | loop c post body => simp [RvRel, rvCode] at h

set_option linter.unusedSimpArgs false in
theorem RvRel.switch_eq {bound : List Ident} {C C' : RvCache}
    {code : Code Op} {c : Expr Op} {cases' : List (Literal × Block Op)}
    {dflt : Option (Block Op)}
    (h : RvRel bound C C' code (.stmt (.switch c cases' dflt))) :
    code = .stmt (.switch c cases' dflt) ∧ C' = RvCache.empty := by
  cases code with
  | stmt s =>
      cases s <;> simp_all [RvRel, rvCode, rvStmt]
  | expr e => simp [RvRel, rvCode] at h
  | args es => simp [RvRel, rvCode] at h
  | stmts ss => simp [RvRel, rvCode] at h
  | loop c post body => simp [RvRel, rvCode] at h

set_option linter.unusedSimpArgs false in
theorem RvRel.forLoop_eq {bound : List Ident} {C C' : RvCache}
    {code : Code Op} {init : Block Op} {c : Expr Op} {post body : Block Op}
    (h : RvRel bound C C' code (.stmt (.forLoop init c post body))) :
    code = .stmt (.forLoop init c post body) ∧ C' = RvCache.empty := by
  cases code with
  | stmt s =>
      cases s <;> simp_all [RvRel, rvCode, rvStmt]
  | expr e => simp [RvRel, rvCode] at h
  | args es => simp [RvRel, rvCode] at h
  | stmts ss => simp [RvRel, rvCode] at h
  | loop c post body => simp [RvRel, rvCode] at h

set_option linter.unusedSimpArgs false in
theorem RvRel.control_eq {bound : List Ident} {C C' : RvCache}
    {code : Code Op} {s : Stmt Op}
    (hs : s = .«break» ∨ s = .«continue» ∨ s = .leave)
    (h : RvRel bound C C' code (.stmt s)) : code = .stmt s := by
  rcases hs with rfl | rfl | rfl <;>
    cases code with
    | stmt t => cases t <;> simp_all [RvRel, rvCode, rvStmt]
    | expr e => simp [RvRel, rvCode] at h
    | args es => simp [RvRel, rvCode] at h
    | stmts ss => simp [RvRel, rvCode] at h
    | loop c post body => simp [RvRel, rvCode] at h

/-- The sweep never changes the hoisted scope. -/
theorem hoist_rvStmts (bound : List Ident) (C : RvCache) :
    ∀ body : Block Op, hoist D (rvStmts bound C body).1 = hoist D body := by
  intro body
  induction body generalizing bound C with
  | nil => rfl
  | cons s rest ih =>
      cases s with
      | block body =>
          simpa [rvStmts, rvStmt, rvNextBound, hoist] using
            ih bound ((rvStmts bound C body).2.kill (blockDecls body))
      | funDef n ps rs body =>
          simpa [rvStmts, rvStmt, rvNextBound, hoist] using ih bound C
      | letDecl xs rhs =>
          simpa [rvStmts, rvStmt, rvNextBound, hoist] using
            ih (xs ++ bound) (rvLet C xs rhs).2
      | assign xs rhs =>
          simpa [rvStmts, rvStmt, rvNextBound, hoist] using
            ih bound (rvAssign bound C xs rhs).2
      | cond c body =>
          simpa [rvStmts, rvStmt, rvNextBound, hoist] using ih bound
            (if rvNeutralExpr c && stmtsNoNormal body then C
             else RvCache.empty)
      | switch c cases dflt =>
          simpa [rvStmts, rvStmt, rvNextBound, hoist] using
            ih bound RvCache.empty
      | forLoop init c post body =>
          simpa [rvStmts, rvStmt, rvNextBound, hoist] using
            ih bound RvCache.empty
      | exprStmt e =>
          simpa [rvStmts, rvStmt, rvNextBound, hoist] using
            ih bound (rvExprStmt C e).2
      | «break» => simpa [rvStmts, rvStmt, rvNextBound, hoist] using ih bound C
      | «continue» =>
          simpa [rvStmts, rvStmt, rvNextBound, hoist] using ih bound C
      | leave => simpa [rvStmts, rvStmt, rvNextBound, hoist] using ih bound C

set_option maxHeartbeats 3200000 in
theorem rv_fwd {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    {code code' : Code Op} {res : Res D} {bound : List Ident}
    {C C' : RvCache} (h : Step D funs V st code res)
    (hr : RvRel bound C C' code code') (hb : BoundOK V bound)
    (hc : RvOk V st C) :
    Step D funs V st code' res ∧
      (∀ V' st' o, res = .sres V' st' o → o = .normal →
        BoundOK V' (rvBound bound code) ∧ RvOk V' st' C') := by
  induction h generalizing bound C C' code' with
  | lit =>
      simp only [RvRel, rvCode, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.lit, by intros; contradiction⟩
  | var hv =>
      simp only [RvRel, rvCode, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.var hv, by intros; contradiction⟩
  | builtinOk ha hop iha =>
      simp only [RvRel, rvCode, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.builtinOk ha hop, by intros; contradiction⟩
  | builtinHalt ha hop iha =>
      simp only [RvRel, rvCode, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.builtinHalt ha hop, by intros; contradiction⟩
  | builtinArgsHalt ha iha =>
      simp only [RvRel, rvCode, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.builtinArgsHalt ha, by intros; contradiction⟩
  | callOk ha hl hlen hbody ho iha ihbody =>
      simp only [RvRel, rvCode, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.callOk ha hl hlen hbody ho, by intros; contradiction⟩
  | callHalt ha hl hlen hbody iha ihbody =>
      simp only [RvRel, rvCode, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.callHalt ha hl hlen hbody, by intros; contradiction⟩
  | callArgsHalt ha iha =>
      simp only [RvRel, rvCode, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.callArgsHalt ha, by intros; contradiction⟩
  | argsNil =>
      simp only [RvRel, rvCode, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.argsNil, by intros; contradiction⟩
  | argsCons hrest he ihrest ihe =>
      simp only [RvRel, rvCode, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.argsCons hrest he, by intros; contradiction⟩
  | argsRestHalt hrest ihrest =>
      simp only [RvRel, rvCode, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.argsRestHalt hrest, by intros; contradiction⟩
  | argsHeadHalt hrest he ihrest ihe =>
      simp only [RvRel, rvCode, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.argsHeadHalt hrest he, by intros; contradiction⟩
  | funDef =>
      simp only [RvRel, rvCode, rvStmt, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.funDef, by
        intro V' st' o heq ho
        injection heq with hV hs hout
        subst hV; subst hs; subst hout
        exact ⟨hb, hc⟩⟩
  | @block funs V st body Vb stb o hbody ihbody =>
      simp only [RvRel, rvCode, rvStmt, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      obtain ⟨hbody', hcbody⟩ := ihbody (bound := bound) (C := C)
        (C' := (rvStmts bound C body).2)
        (code' := .stmts (rvStmts bound C body).1) rfl hb hc
      rw [← hoist_rvStmts bound C body] at hbody'
      refine ⟨Step.block hbody', ?_⟩
      intro V' st' o' hres ho
      subst o'
      injection hres with hV hs hout
      subst hV; subst hs; subst hout
      have hcbody' := hcbody Vb stb .normal rfl rfl
      exact ⟨hb.mono (Step.block hbody),
        hcbody'.2.kill_restore (scopeFrame_stmts_normal hbody)⟩
  | letZero =>
      simp only [RvRel, rvCode, rvStmt, rvLet_none, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.letZero, by
        intro V' st' o heq ho
        injection heq with hV hs hout
        subst hV; subst hs; subst hout
        constructor
        · intro x hx
          simp only [rvBound, rvNextBound, List.mem_append] at hx
          rw [List.map_append, bindZeros_keys]
          exact hx.elim (fun h => List.mem_append_left _ h)
            (fun h => List.mem_append_right _ (hb x h))
        · exact hc.kill_bindZeros _⟩
  | @letVal funs V st vars e vals st1 he hlen ihe =>
      obtain ⟨e', C'', hp⟩ := rvLet_some C vars e
      simp only [RvRel, rvCode, rvStmt, hp, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      obtain ⟨he', hc'⟩ := rvLet_expr_fwd hp hc he
      refine ⟨Step.letVal he' hlen, ?_⟩
      intro V' st' o hres ho
      injection hres with hV hs hout
      subst hV; subst hs; subst hout
      constructor
      · intro x hx
        simp only [rvBound, rvNextBound, List.mem_append] at hx
        rw [List.map_append, List.map_fst_zip (by omega)]
        exact hx.elim (fun h => List.mem_append_left _ h)
          (fun h => List.mem_append_right _ (hb x h))
      · exact hc' vals st1 rfl (by omega)
  | @letHalt funs V st vars e st1 he ihe =>
      obtain ⟨e', C'', hp⟩ := rvLet_some C vars e
      simp only [RvRel, rvCode, rvStmt, hp, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      obtain ⟨he', -⟩ := rvLet_expr_fwd hp hc he
      exact ⟨Step.letHalt he', by intros; simp_all⟩
  | @assignVal funs V st vars e vals st1 he hlen ihe =>
      generalize hp : rvAssign bound C vars e = p at hr
      rcases p with ⟨e', C''⟩
      simp only [RvRel, rvCode, rvStmt, hp, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      obtain ⟨he', hc'⟩ := rvAssign_expr_fwd hp hc hb he
      refine ⟨Step.assignVal he' hlen, ?_⟩
      intro V' st' o hres ho
      injection hres with hV hs hout
      subst hV; subst hs; subst hout
      exact ⟨hb.afterStmt (Step.assignVal he hlen),
        hc' vals st1 rfl (by omega)⟩
  | @assignHalt funs V st vars e st1 he ihe =>
      generalize hp : rvAssign bound C vars e = p at hr
      rcases p with ⟨e', C''⟩
      simp only [RvRel, rvCode, rvStmt, hp, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      obtain ⟨he', -⟩ := rvAssign_expr_fwd hp hc hb he
      exact ⟨Step.assignHalt he', by intros; simp_all⟩
  | @exprStmt funs V st e st1 he ihe =>
      generalize hp : rvExprStmt C e = p at hr
      rcases p with ⟨e', C''⟩
      simp only [RvRel, rvCode, rvStmt, hp, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      obtain ⟨rfl, hc'⟩ := rvExprStmt_ok hp hc he
      exact ⟨Step.exprStmt he, by
        intro V' st' o hres ho
        injection hres with hV hs hout
        subst hV; subst hs; subst hout
        exact ⟨hb, hc' st1 rfl⟩⟩
  | @exprStmtHalt funs V st e st1 he ihe =>
      generalize hp : rvExprStmt C e = p at hr
      rcases p with ⟨e', C''⟩
      have hfst := rvExprStmt_fst C e
      rw [hp] at hfst
      simp only at hfst
      subst hfst
      simp only [RvRel, rvCode, rvStmt, hp, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.exprStmtHalt he, by intros; simp_all⟩
  | @ifTrue funs V st c body cv st1 V' st2 o hcond hnz hbody ihc ihbody =>
      generalize hkeep : (rvNeutralExpr c && stmtsNoNormal body) = keep at hr
      cases keep with
      | false =>
          simp only [RvRel, rvCode, rvStmt, hkeep, Bool.false_eq_true,
            if_false, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          obtain ⟨hbody', -⟩ := ihbody (bound := bound) (C := RvCache.empty)
            (C' := (rvStmts bound RvCache.empty body).2.kill
              (blockDecls body))
            (code' := .stmt (.block (rvStmts bound RvCache.empty body).1))
            rfl hb (RvOk.empty _ _)
          exact ⟨Step.ifTrue hcond hnz hbody', by
            intro W st' o' hres ho
            injection hres with hV hs hout
            subst hV; subst hs; subst hout
            exact ⟨hb.mono (Step.ifTrue hcond hnz hbody), RvOk.empty _ _⟩⟩
      | true =>
          simp only [RvRel, rvCode, rvStmt, hkeep, if_true,
            Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          obtain ⟨hbody', -⟩ := ihbody (bound := bound) (C := RvCache.empty)
            (C' := (rvStmts bound RvCache.empty body).2.kill
              (blockDecls body))
            (code' := .stmt (.block (rvStmts bound RvCache.empty body).1))
            rfl hb (RvOk.empty _ _)
          refine ⟨Step.ifTrue hcond hnz hbody', ?_⟩
          intro W st' o' hres ho
          have hk : rvNeutralExpr c = true ∧ stmtsNoNormal body = true := by
            simpa using hkeep
          exact False.elim ((stmtNoNormal_sound (s := .block body)
            (by simpa [YulEvmCompiler.Optimizer.stmtNoNormal] using hk.2)
            hbody) (by simp_all))
  | @ifFalse funs V st c body cv st1 hcond hz ihc =>
      generalize hkeep : (rvNeutralExpr c && stmtsNoNormal body) = keep at hr
      cases keep with
      | false =>
          simp only [RvRel, rvCode, rvStmt, hkeep, Bool.false_eq_true,
            if_false, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          exact ⟨Step.ifFalse hcond hz, by
            intro W st' o hres ho
            injection hres with hV hs hout
            subst hV; subst hs; subst hout
            exact ⟨hb, RvOk.empty _ _⟩⟩
      | true =>
          simp only [RvRel, rvCode, rvStmt, hkeep, if_true,
            Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          refine ⟨Step.ifFalse hcond hz, ?_⟩
          intro W st' o hres ho
          injection hres with hV hs hout
          subst hV; subst hs; subst hout
          have hk : rvNeutralExpr c = true ∧ stmtsNoNormal body = true := by
            simpa using hkeep
          obtain ⟨vs', stc, hres', hmn⟩ := rvNeutral_step hk.1 _ _ _ _ hcond
          injection hres' with hres'
          injection hres' with hv1 hst1
          rw [hst1]
          exact ⟨hb, hc.memNeutral hmn⟩
  | @ifHalt funs V st c body st1 hcond ihc =>
      generalize hkeep : (rvNeutralExpr c && stmtsNoNormal body) = keep at hr
      cases keep <;>
        simp only [RvRel, rvCode, rvStmt, hkeep, Bool.false_eq_true,
          if_false, if_true, Prod.mk.injEq] at hr <;>
        obtain ⟨rfl, rfl⟩ := hr <;>
        exact ⟨Step.ifHalt hcond, by intros; simp_all⟩
  | switchExec hcond hsel ihc ihsel =>
      simp only [RvRel, rvCode, rvStmt, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      refine ⟨Step.switchExec hcond hsel, ?_⟩
      intro W st' o hres ho
      injection hres with hV hs hout
      subst hV; subst hs; subst hout
      exact ⟨hb.mono (Step.switchExec hcond hsel), RvOk.empty _ _⟩
  | switchHalt hcond ihc =>
      simp only [RvRel, rvCode, rvStmt, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.switchHalt hcond, by intros; simp_all⟩
  | forLoop hinit hloop ihinit ihloop =>
      simp only [RvRel, rvCode, rvStmt, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      refine ⟨Step.forLoop hinit hloop, ?_⟩
      intro W st' o hres ho
      injection hres with hV hs hout
      subst hV; subst hs; subst hout
      exact ⟨hb.mono (Step.forLoop hinit hloop), RvOk.empty _ _⟩
  | forInitHalt hinit ihinit =>
      simp only [RvRel, rvCode, rvStmt, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.forInitHalt hinit, by intros; simp_all⟩
  | «break» =>
      simp only [RvRel, rvCode, rvStmt, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.break, by intros; simp_all⟩
  | «continue» =>
      simp only [RvRel, rvCode, rvStmt, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.continue, by intros; simp_all⟩
  | leave =>
      simp only [RvRel, rvCode, rvStmt, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.leave, by intros; simp_all⟩
  | seqNil =>
      simp only [RvRel, rvCode, rvStmts, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.seqNil, by
        intro V' st' o heq ho
        injection heq with hV hs hout
        subst hV; subst hs; subst hout
        exact ⟨hb, hc⟩⟩
  | @seqCons funs V st s rest V1 st1 V2 st2 o hs hrest ihs ihrest =>
      generalize hsfp : rvStmt bound C s = p at hr
      rcases p with ⟨s', C1⟩
      simp only [RvRel, rvCode, rvStmts, hsfp, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      obtain ⟨hs', hsok⟩ := ihs (bound := bound) (C := C) (C' := C1)
        (code' := .stmt s') (by simp [RvRel, rvCode, hsfp]) hb hc
      obtain ⟨hb1, hc1⟩ := hsok V1 st1 .normal rfl rfl
      have hbound : rvBound bound (.stmt s) = rvNextBound bound s := by
        cases s <;> rfl
      rw [hbound] at hb1
      obtain ⟨hrest', hrok⟩ := ihrest
        (bound := rvNextBound bound s) (C := C1)
        (C' := (rvStmts (rvNextBound bound s) C1 rest).2)
        (code' := .stmts (rvStmts (rvNextBound bound s) C1 rest).1)
        rfl hb1 hc1
      exact ⟨Step.seqCons hs' hrest', by
        intro V' st' o' hres ho
        have hout := hrok V' st' o' hres ho
        have hbounds : rvBound bound (.stmts (s :: rest)) =
            rvBound (rvNextBound bound s) (.stmts rest) := by
          cases s <;> rfl
        rwa [hbounds]⟩
  | @seqStop funs V st s rest V1 st1 o hs hne ihs =>
      generalize hsfp : rvStmt bound C s = p at hr
      rcases p with ⟨s', C1⟩
      simp only [RvRel, rvCode, rvStmts, hsfp, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      obtain ⟨hs', -⟩ := ihs (bound := bound) (C := C) (C' := C1)
        (code' := .stmt s') (by simp [RvRel, rvCode, hsfp]) hb hc
      exact ⟨Step.seqStop hs' hne, by intros; simp_all⟩
  | loopDone hcond hz ihc =>
      simp only [RvRel, rvCode, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.loopDone hcond hz, by
        intro W st' o hres ho
        injection hres with hV hs hout
        subst hV; subst hs; subst hout
        exact ⟨hb, RvOk.empty _ _⟩⟩
  | loopCondHalt hcond ihc =>
      simp only [RvRel, rvCode, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.loopCondHalt hcond, by intros; simp_all⟩
  | loopStep hcond hnz hbody hob hp hrest ihc ihb ihp ihr =>
      simp only [RvRel, rvCode, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      refine ⟨Step.loopStep hcond hnz hbody hob hp hrest, ?_⟩
      intro W st' o' hres ho
      injection hres with hV hs hout
      subst hV; subst hs; subst hout
      exact ⟨hb.mono (Step.loopStep hcond hnz hbody hob hp hrest),
        RvOk.empty _ _⟩
  | loopPostHalt hcond hnz hbody hob hp ihc ihb ihp =>
      simp only [RvRel, rvCode, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.loopPostHalt hcond hnz hbody hob hp, by
        intro W st' o hres ho
        injection hres with _ _ hout
        subst hout
        simp at ho⟩
  | loopBreak hcond hnz hbody ihc ihb =>
      simp only [RvRel, rvCode, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.loopBreak hcond hnz hbody, by
        intro W st' o hres ho
        injection hres with hV hs hout
        subst hV; subst hs; subst hout
        exact ⟨hb.mono hbody, RvOk.empty _ _⟩⟩
  | loopLeave hcond hnz hbody ihc ihb =>
      simp only [RvRel, rvCode, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.loopLeave hcond hnz hbody, by
        intro W st' o hres ho
        injection hres with _ _ hout
        subst hout
        simp at ho⟩
  | loopBodyHalt hcond hnz hbody ihc ihb =>
      simp only [RvRel, rvCode, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.loopBodyHalt hcond hnz hbody, by
        intro W st' o hres ho
        injection hres with _ _ hout
        subst hout
        simp at ho⟩

set_option maxHeartbeats 3200000 in
theorem rv_bwd {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    {code code' : Code Op} {res : Res D} {bound : List Ident}
    {C C' : RvCache} (h : Step D funs V st code' res)
    (hr : RvRel bound C C' code code') (hb : BoundOK V bound)
    (hc : RvOk V st C) :
    Step D funs V st code res := by
  induction h generalizing code bound C C' with
  | lit =>
      rw [hr.expr_eq]
      exact Step.lit
  | var hv =>
      rw [hr.expr_eq]
      exact Step.var hv
  | builtinOk ha hop iha =>
      rw [hr.expr_eq]
      exact Step.builtinOk ha hop
  | builtinHalt ha hop iha =>
      rw [hr.expr_eq]
      exact Step.builtinHalt ha hop
  | builtinArgsHalt ha iha =>
      rw [hr.expr_eq]
      exact Step.builtinArgsHalt ha
  | callOk ha hl hlen hbody ho iha ihbody =>
      rw [hr.expr_eq]
      exact Step.callOk ha hl hlen hbody ho
  | callHalt ha hl hlen hbody iha ihbody =>
      rw [hr.expr_eq]
      exact Step.callHalt ha hl hlen hbody
  | callArgsHalt ha iha =>
      rw [hr.expr_eq]
      exact Step.callArgsHalt ha
  | argsNil =>
      rw [hr.args_eq]
      exact Step.argsNil
  | argsCons hrest he ihrest ihe =>
      rw [hr.args_eq]
      exact Step.argsCons hrest he
  | argsRestHalt hrest ihrest =>
      rw [hr.args_eq]
      exact Step.argsRestHalt hrest
  | argsHeadHalt hrest he ihrest ihe =>
      rw [hr.args_eq]
      exact Step.argsHeadHalt hrest he
  | funDef =>
      cases code with
      | stmt s =>
          cases s <;> simp_all [RvRel, rvCode, rvStmt]
          exact Step.funDef
      | expr e => simp [RvRel, rvCode] at hr
      | args es => simp [RvRel, rvCode] at hr
      | stmts ss => simp [RvRel, rvCode] at hr
      | loop c post body => simp [RvRel, rvCode] at hr
  | block hbody ihbody =>
      cases code with
      | stmt s =>
          cases s with
          | block body =>
              simp only [RvRel, rvCode, rvStmt, Prod.mk.injEq] at hr
              obtain ⟨hcode, hcache⟩ := hr
              injection hcode with hbodyeq
              cases hbodyeq; cases hcache
              have hbody' := ihbody (code := .stmts body) (bound := bound)
                (C := C) (C' := (rvStmts bound C body).2) rfl hb hc
              rw [hoist_rvStmts bound C body] at hbody'
              exact Step.block hbody'
          | funDef n ps rs body => simp [RvRel, rvCode, rvStmt] at hr
          | letDecl xs rhs => simp [RvRel, rvCode, rvStmt] at hr
          | assign xs rhs => simp [RvRel, rvCode, rvStmt] at hr
          | cond c body => simp [RvRel, rvCode, rvStmt] at hr
          | switch c cases dflt => simp [RvRel, rvCode, rvStmt] at hr
          | forLoop init c post body => simp [RvRel, rvCode, rvStmt] at hr
          | exprStmt e => simp [RvRel, rvCode, rvStmt, rvExprStmt_fst] at hr
          | «break» => simp [RvRel, rvCode, rvStmt] at hr
          | «continue» => simp [RvRel, rvCode, rvStmt] at hr
          | leave => simp [RvRel, rvCode, rvStmt] at hr
      | expr e => simp [RvRel, rvCode] at hr
      | args es => simp [RvRel, rvCode] at hr
      | stmts ss => simp [RvRel, rvCode] at hr
      | loop c post body => simp [RvRel, rvCode] at hr
  | letZero =>
      obtain ⟨rhs, rfl, heq⟩ := hr.let_inv
      cases rhs with
      | none => exact Step.letZero
      | some e =>
          obtain ⟨e', C'', hp⟩ := rvLet_some C _ e
          rw [hp] at heq
          cases heq
  | letVal he hlen ihe =>
      obtain ⟨rhs, rfl, heq⟩ := hr.let_inv
      cases rhs with
      | none =>
          rw [rvLet_none] at heq
          cases heq
      | some e =>
          exact Step.letVal (rvLet_expr_bwd heq hc he) hlen
  | letHalt he ihe =>
      obtain ⟨rhs, rfl, heq⟩ := hr.let_inv
      cases rhs with
      | none =>
          rw [rvLet_none] at heq
          cases heq
      | some e => exact Step.letHalt (rvLet_expr_bwd heq hc he)
  | assignVal he hlen ihe =>
      obtain ⟨rhs, rfl, heq⟩ := hr.assign_inv
      exact Step.assignVal (rvAssign_expr_bwd heq hc he) hlen
  | assignHalt he ihe =>
      obtain ⟨rhs, rfl, heq⟩ := hr.assign_inv
      exact Step.assignHalt (rvAssign_expr_bwd heq hc he)
  | exprStmt he ihe =>
      rw [hr.exprStmt_inv.1]
      exact Step.exprStmt he
  | exprStmtHalt he ihe =>
      rw [hr.exprStmt_inv.1]
      exact Step.exprStmtHalt he
  | ifTrue hcond hnz hbody ihc ihbody =>
      obtain ⟨body, rfl, hbodyeq, hcache⟩ := hr.cond_inv
      cases hbodyeq
      have hbody' := ihbody (code := .stmt (.block body)) (bound := bound)
        (C := RvCache.empty)
        (C' := (rvStmts bound RvCache.empty body).2.kill (blockDecls body))
        rfl hb (RvOk.empty _ _)
      exact Step.ifTrue hcond hnz hbody'
  | ifFalse hcond hz ihc =>
      obtain ⟨body, rfl, hbodyeq, hcache⟩ := hr.cond_inv
      exact Step.ifFalse hcond hz
  | ifHalt hcond ihc =>
      obtain ⟨body, rfl, hbodyeq, hcache⟩ := hr.cond_inv
      exact Step.ifHalt hcond
  | switchExec hcond hsel ihc ihsel =>
      rw [hr.switch_eq.1]
      exact Step.switchExec hcond hsel
  | switchHalt hcond ihc =>
      rw [hr.switch_eq.1]
      exact Step.switchHalt hcond
  | forLoop hinit hloop ihinit ihloop =>
      rw [hr.forLoop_eq.1]
      exact Step.forLoop hinit hloop
  | forInitHalt hinit ihinit =>
      rw [hr.forLoop_eq.1]
      exact Step.forInitHalt hinit
  | «break» =>
      rw [hr.control_eq (Or.inl rfl)]
      exact Step.break
  | «continue» =>
      rw [hr.control_eq (Or.inr (Or.inl rfl))]
      exact Step.continue
  | leave =>
      rw [hr.control_eq (Or.inr (Or.inr rfl))]
      exact Step.leave
  | seqNil =>
      rw [hr.stmts_nil_inv]
      exact Step.seqNil
  | @seqCons funs V st s' rest' V1 st1 V2 st2 o hs hrest ihs ihrest =>
      obtain ⟨s, rest, C1, rfl, hsrel, hrestrel⟩ := hr.stmts_cons_inv
      have hhead : RvRel bound C C1 (.stmt s) (.stmt s') := by
        unfold RvRel
        simp only [rvCode]
        rw [hsrel]
      have hs0 := ihs (code := .stmt s) (bound := bound) (C := C) (C' := C1)
        hhead hb hc
      obtain ⟨-, hsok⟩ := rv_fwd hs0 hhead hb hc
      obtain ⟨hb1, hc1⟩ := hsok V1 st1 .normal rfl rfl
      have hbound : rvBound bound (.stmt s) = rvNextBound bound s := by
        cases s <;> rfl
      rw [hbound] at hb1
      have htail : RvRel (rvNextBound bound s) C1 C' (.stmts rest)
          (.stmts rest') := by
        unfold RvRel
        simp only [rvCode]
        rw [hrestrel]
      have hrest0 := ihrest (code := .stmts rest)
        (bound := rvNextBound bound s) (C := C1) (C' := C') htail hb1 hc1
      exact Step.seqCons hs0 hrest0
  | @seqStop funs V st s' rest' V1 st1 o hs hne ihs =>
      obtain ⟨s, rest, C1, rfl, hsrel, hrestrel⟩ := hr.stmts_cons_inv
      have hhead : RvRel bound C C1 (.stmt s) (.stmt s') := by
        unfold RvRel
        simp only [rvCode]
        rw [hsrel]
      have hs0 := ihs (code := .stmt s) (bound := bound) (C := C) (C' := C1)
        hhead hb hc
      exact Step.seqStop hs0 hne
  | loopDone hcond hz ihc =>
      rw [hr.loop_eq]
      exact Step.loopDone hcond hz
  | loopCondHalt hcond ihc =>
      rw [hr.loop_eq]
      exact Step.loopCondHalt hcond
  | loopStep hcond hnz hbody hob hp hrest ihc ihb ihp ihr =>
      rw [hr.loop_eq]
      exact Step.loopStep hcond hnz hbody hob hp hrest
  | loopPostHalt hcond hnz hbody hob hp ihc ihb ihp =>
      rw [hr.loop_eq]
      exact Step.loopPostHalt hcond hnz hbody hob hp
  | loopBreak hcond hnz hbody ihc ihb =>
      rw [hr.loop_eq]
      exact Step.loopBreak hcond hnz hbody
  | loopLeave hcond hnz hbody ihc ihb =>
      rw [hr.loop_eq]
      exact Step.loopLeave hcond hnz hbody
  | loopBodyHalt hcond hnz hbody ihc ihb =>
      rw [hr.loop_eq]
      exact Step.loopBodyHalt hcond hnz hbody

end YulEvmCompiler.Optimizer.ReuseValues
