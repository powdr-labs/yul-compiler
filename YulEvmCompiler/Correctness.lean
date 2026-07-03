import YulEvmCompiler.OpStep

/-!
# YulEvmCompiler.Correctness

The compiler-correctness theorem for straight-line Yul **with variables and
nested blocks**.

The proof is a forward simulation. The runtime operand stack is split into
three regions: expression temporaries `τ` on top, then the **variable
region** — the image of the semantics' `VEnv` under `conv`, in the same
order (the compile-time layout is literally `V.map Prod.fst`) — then an
arbitrary rest `σ`.

* `SimOk`/`SimHalt` (region-agnostic, from milestone 1) describe single-
  instruction fragments that consume/produce stack values;
* `SimE`/`SimEHalt` describe compiled *expressions*: the variable region is
  fixed, `off` counts the temporaries above it (this is what bounds `DUP`
  depth);
* `SimS`/`SimSHalt` describe compiled *statements*: the variable region
  evolves (`let` grows it, `:=` updates it in place, block exit pops it).

The induction over the Yul `Step` judgment (`sim`) composes these along the
source derivation, with `pushStep`/`opStep`/`dupStep`/`swapStep`/`popStep`
as the leaves, and `compile_correct`/`compile_correct_eval` package the top
level (including the implicit `STOP` when the program falls off the end of
the code).
-/

namespace YulEvmCompiler

open EvmSemantics
open EvmSemantics.EVM
open YulSemantics.EVM (U256 EvmState Op stepOp)
open YulSemantics (Outcome Ident VEnv)

/-! ### The variable region -/

/-- The stack image of a variable environment: the values, converted, in
`VEnv` order (innermost binding = top of the region). -/
def vimg (V : VEnv yul) : List UInt256 := V.map (fun p => conv p.2)

/-- The compile-time layout a variable environment realizes: its names. -/
def names (V : VEnv yul) : List Ident := V.map Prod.fst

@[simp] theorem vimg_nil : vimg ([] : VEnv yul) = [] := rfl
@[simp] theorem vimg_cons (p : Ident × U256) (V : VEnv yul) :
    vimg (p :: V) = conv p.2 :: vimg V := rfl
@[simp] theorem names_nil : names ([] : VEnv yul) = [] := rfl
@[simp] theorem names_cons (p : Ident × U256) (V : VEnv yul) :
    names (p :: V) = p.1 :: names V := rfl
@[simp] theorem vimg_length (V : VEnv yul) : (vimg V).length = V.length := by
  simp [vimg]
@[simp] theorem names_length (V : VEnv yul) : (names V).length = V.length := by
  simp [names]

theorem vimg_append (V W : VEnv yul) : vimg (V ++ W) = vimg V ++ vimg W := by
  simp [vimg]

theorem names_append (V W : VEnv yul) : names (V ++ W) = names V ++ names W := by
  simp [names]

private theorem findIdx?_lt {α : Type} (p : α → Bool) :
    ∀ {l : List α} {idx : Nat}, l.findIdx? p = some idx → idx < l.length := by
  intro l
  induction l with
  | nil => intro idx h; simp at h
  | cons a l ih =>
    intro idx h
    rw [List.findIdx?_cons] at h
    by_cases hp : p a
    · rw [if_pos hp] at h
      simp at h
      simp
      omega
    · rw [if_neg hp] at h
      obtain ⟨idx', hidx', rfl⟩ := Option.map_eq_some_iff.mp h
      have := ih hidx'
      simp
      omega

/-- The value the semantics reads for `x` sits at the index the compiler
computed, in the stack image. -/
theorem vimg_get {V : VEnv yul} {x : Ident} {v : U256} {idx : Nat}
    (hget : VEnv.get V x = some v)
    (hidx : (names V).findIdx? (fun y => y = x) = some idx) :
    (vimg V)[idx]? = some (conv v) := by
  induction V generalizing idx with
  | nil => simp [VEnv.get] at hget
  | cons p V ih =>
    obtain ⟨y, w⟩ := p
    rw [show names ((y, w) :: V) = y :: names V from rfl,
      List.findIdx?_cons] at hidx
    by_cases hxy : y = x
    · rw [if_pos (by simpa using hxy)] at hidx
      have hidx0 : idx = 0 := by simpa using hidx.symm
      subst hidx0
      have hv : w = v := by
        unfold VEnv.get at hget
        rw [List.find?_cons_of_pos (by simpa using hxy)] at hget
        simpa using hget
      subst hv
      rfl
    · rw [if_neg (by simpa using hxy)] at hidx
      obtain ⟨idx', hidx', rfl⟩ := Option.map_eq_some_iff.mp hidx
      have hget' : VEnv.get V x = some v := by
        unfold VEnv.get at hget ⊢
        rwa [List.find?_cons_of_neg (by simpa using hxy)] at hget
      exact ih hget' hidx'

/-- `VEnv.set` keeps the layout. -/
theorem names_set (V : VEnv yul) (x : Ident) (v : U256) :
    names (VEnv.set V x v) = names V := by
  induction V with
  | nil => rfl
  | cons p V ih =>
    obtain ⟨y, w⟩ := p
    unfold VEnv.set
    by_cases hxy : y = x
    · rw [if_pos hxy]
      subst hxy
      rfl
    · rw [if_neg hxy]
      show y :: names (VEnv.set V x v) = y :: names V
      rw [ih]

/-- `VEnv.set` updates the stack image at the compiled index. -/
theorem vimg_set {V : VEnv yul} {x : Ident} (v : U256) {idx : Nat}
    (hidx : (names V).findIdx? (fun y => y = x) = some idx) :
    vimg (VEnv.set V x v) = (vimg V).set idx (conv v) := by
  induction V generalizing idx with
  | nil => rfl
  | cons p V ih =>
    obtain ⟨y, w⟩ := p
    rw [show names ((y, w) :: V) = y :: names V from rfl,
      List.findIdx?_cons] at hidx
    unfold VEnv.set
    by_cases hxy : y = x
    · rw [if_pos hxy]
      rw [if_pos (by simpa using hxy)] at hidx
      have hidx0 : idx = 0 := by simpa using hidx.symm
      subst hidx0
      rfl
    · rw [if_neg hxy]
      rw [if_neg (by simpa using hxy)] at hidx
      obtain ⟨idx', hidx', rfl⟩ := Option.map_eq_some_iff.mp hidx
      show conv w :: vimg (VEnv.set V x v) = (conv w :: vimg V).set (idx' + 1) (conv v)
      rw [ih hidx']
      rfl

/-! ### Target-side meaning of a source evaluation -/

/-- A single-instruction-consuming fragment (unchanged from milestone 1):
region-agnostic, consumes `ins`, produces `out` over an arbitrary rest. -/
def SimOk (yst : EvmState) (is : List Instr) (ins out : List U256)
    (yst' : EvmState) : Prop :=
  ∃ b : Nat, ∀ (code : ByteArray) (pre post : List UInt8) (σ : List UInt256)
    (s : State),
    code = mkCode (pre ++ assembleBytes is ++ post) →
    FrameOK code s → StateMatch yst s →
    s.pc = UInt256.ofNat pre.length →
    s.stack = ins.map conv ++ σ →
    b ≤ s.gasAvailable →
    ∃ s', Steps s s' ∧ FrameOK code s' ∧ StateMatch yst' s'
      ∧ s'.pc = UInt256.ofNat (pre.length + (assembleBytes is).length)
      ∧ s'.stack = out.map conv ++ σ
      ∧ s.gasAvailable - b ≤ s'.gasAvailable

/-- Like `SimOk`, but the fragment halts. -/
def SimHalt (yst : EvmState) (is : List Instr) (ins : List U256)
    (yst' : EvmState) : Prop :=
  ∃ b : Nat, ∀ (code : ByteArray) (pre post : List UInt8) (σ : List UInt256)
    (s : State),
    code = mkCode (pre ++ assembleBytes is ++ post) →
    FrameOK code s → StateMatch yst s →
    s.pc = UInt256.ofNat pre.length →
    s.stack = ins.map conv ++ σ →
    b ≤ s.gasAvailable →
    ∃ s', Steps s s' ∧ StateMatch yst' s' ∧ s'.callStack = []
      ∧ HaltedMatch yst' s'

/-- A compiled *expression* fragment: the variable region `vimg V` is fixed,
`τ` are the temporaries above it (`τ.length = off` is what the compiler's
depth bookkeeping tracks), and the fragment pushes `out` on top. -/
def SimE (yst : EvmState) (V : VEnv yul) (off : Nat) (is : List Instr)
    (out : List U256) (yst' : EvmState) : Prop :=
  ∃ b : Nat, ∀ (code : ByteArray) (pre post : List UInt8)
    (τ σ : List UInt256) (s : State),
    code = mkCode (pre ++ assembleBytes is ++ post) →
    FrameOK code s → StateMatch yst s →
    s.pc = UInt256.ofNat pre.length →
    s.stack = τ ++ vimg V ++ σ →
    τ.length = off →
    b ≤ s.gasAvailable →
    ∃ s', Steps s s' ∧ FrameOK code s' ∧ StateMatch yst' s'
      ∧ s'.pc = UInt256.ofNat (pre.length + (assembleBytes is).length)
      ∧ s'.stack = out.map conv ++ τ ++ vimg V ++ σ
      ∧ s.gasAvailable - b ≤ s'.gasAvailable

/-- Like `SimE`, but the expression halts. -/
def SimEHalt (yst : EvmState) (V : VEnv yul) (off : Nat) (is : List Instr)
    (yst' : EvmState) : Prop :=
  ∃ b : Nat, ∀ (code : ByteArray) (pre post : List UInt8)
    (τ σ : List UInt256) (s : State),
    code = mkCode (pre ++ assembleBytes is ++ post) →
    FrameOK code s → StateMatch yst s →
    s.pc = UInt256.ofNat pre.length →
    s.stack = τ ++ vimg V ++ σ →
    τ.length = off →
    b ≤ s.gasAvailable →
    ∃ s', Steps s s' ∧ StateMatch yst' s' ∧ s'.callStack = []
      ∧ HaltedMatch yst' s'

/-- A compiled *statement* fragment: takes the variable region from `V` to
`V'`. -/
def SimS (yst : EvmState) (V : VEnv yul) (is : List Instr)
    (yst' : EvmState) (V' : VEnv yul) : Prop :=
  ∃ b : Nat, ∀ (code : ByteArray) (pre post : List UInt8) (σ : List UInt256)
    (s : State),
    code = mkCode (pre ++ assembleBytes is ++ post) →
    FrameOK code s → StateMatch yst s →
    s.pc = UInt256.ofNat pre.length →
    s.stack = vimg V ++ σ →
    b ≤ s.gasAvailable →
    ∃ s', Steps s s' ∧ FrameOK code s' ∧ StateMatch yst' s'
      ∧ s'.pc = UInt256.ofNat (pre.length + (assembleBytes is).length)
      ∧ s'.stack = vimg V' ++ σ
      ∧ s.gasAvailable - b ≤ s'.gasAvailable

/-- Like `SimS`, but the statement halts. -/
def SimSHalt (yst : EvmState) (V : VEnv yul) (is : List Instr)
    (yst' : EvmState) : Prop :=
  ∃ b : Nat, ∀ (code : ByteArray) (pre post : List UInt8) (σ : List UInt256)
    (s : State),
    code = mkCode (pre ++ assembleBytes is ++ post) →
    FrameOK code s → StateMatch yst s →
    s.pc = UInt256.ofNat pre.length →
    s.stack = vimg V ++ σ →
    b ≤ s.gasAvailable →
    ∃ s', Steps s s' ∧ StateMatch yst' s' ∧ s'.callStack = []
      ∧ HaltedMatch yst' s'

/-! ### Structural rules -/

theorem SimOk.frame {yst : EvmState} {is : List Instr} {ins out : List U256}
    {yst' : EvmState} (h : SimOk yst is ins out yst') (extra : List U256) :
    SimOk yst is (ins ++ extra) (out ++ extra) yst' := by
  obtain ⟨b, H⟩ := h
  refine ⟨b, ?_⟩
  intro code pre post σ s hcode hf hm hpc hstk hgas
  obtain ⟨s', hsteps, hf', hm', hpc', hstk', hg'⟩ :=
    H code pre post (extra.map conv ++ σ) s hcode hf hm hpc
      (by simpa [List.append_assoc] using hstk) hgas
  exact ⟨s', hsteps, hf', hm', hpc',
    by simpa [List.append_assoc] using hstk', hg'⟩

/-- Lift a region-agnostic fragment that consumes nothing to `SimE`. -/
theorem SimOk.toSimE {yst : EvmState} {is : List Instr} {out : List U256}
    {yst' : EvmState} (h : SimOk yst is [] out yst') (V : VEnv yul) (off : Nat) :
    SimE yst V off is out yst' := by
  obtain ⟨b, H⟩ := h
  refine ⟨b, ?_⟩
  intro code pre post τ σ s hcode hf hm hpc hstk hτ hgas
  obtain ⟨s', hsteps, hf', hm', hpc', hstk', hg'⟩ :=
    H code pre post (τ ++ vimg V ++ σ) s hcode hf hm hpc (by simpa using hstk)
      hgas
  exact ⟨s', hsteps, hf', hm', hpc', by simpa using hstk', hg'⟩

/-- Sequence an expression fragment with a consuming fragment (the compiled
built-in's opcode). -/
theorem SimE.compOk {yst : EvmState} {V : VEnv yul} {off : Nat}
    {is1 is2 : List Instr} {out1 out2 : List U256} {yst1 yst2 : EvmState}
    (h1 : SimE yst V off is1 out1 yst1) (h2 : SimOk yst1 is2 out1 out2 yst2) :
    SimE yst V off (is1 ++ is2) out2 yst2 := by
  obtain ⟨b1, H1⟩ := h1
  obtain ⟨b2, H2⟩ := h2
  refine ⟨b1 + b2, ?_⟩
  intro code pre post τ σ s hcode hf hm hpc hstk hτ hgas
  obtain ⟨s1, st1, hf1, hm1, hpc1, hstk1, hg1⟩ :=
    H1 code pre (assembleBytes is2 ++ post) τ σ s
      (by rw [hcode]; congr 1; simp [assembleBytes_append]) hf hm hpc hstk hτ
      (by omega)
  obtain ⟨s2, st2, hf2, hm2, hpc2, hstk2, hg2⟩ :=
    H2 code (pre ++ assembleBytes is1) post (τ ++ vimg V ++ σ) s1
      (by rw [hcode]; congr 1; simp [assembleBytes_append]) hf1 hm1
      (by rw [hpc1]; congr 1; simp) (by simpa using hstk1) (by omega)
  refine ⟨s2, st1.append st2, hf2, hm2, ?_, by simpa using hstk2, by omega⟩
  rw [hpc2]
  congr 1
  simp [assembleBytes_append]
  omega

/-- Sequence an expression fragment with a consuming fragment that halts. -/
theorem SimE.compHaltOk {yst : EvmState} {V : VEnv yul} {off : Nat}
    {is1 is2 : List Instr} {out1 : List U256} {yst1 yst2 : EvmState}
    (h1 : SimE yst V off is1 out1 yst1) (h2 : SimHalt yst1 is2 out1 yst2) :
    SimEHalt yst V off (is1 ++ is2) yst2 := by
  obtain ⟨b1, H1⟩ := h1
  obtain ⟨b2, H2⟩ := h2
  refine ⟨b1 + b2, ?_⟩
  intro code pre post τ σ s hcode hf hm hpc hstk hτ hgas
  obtain ⟨s1, st1, hf1, hm1, hpc1, hstk1, hg1⟩ :=
    H1 code pre (assembleBytes is2 ++ post) τ σ s
      (by rw [hcode]; congr 1; simp [assembleBytes_append]) hf hm hpc hstk hτ
      (by omega)
  obtain ⟨s2, st2, hm2, hcs2, hhm2⟩ :=
    H2 code (pre ++ assembleBytes is1) post (τ ++ vimg V ++ σ) s1
      (by rw [hcode]; congr 1; simp [assembleBytes_append]) hf1 hm1
      (by rw [hpc1]; congr 1; simp) (by simpa using hstk1) (by omega)
  exact ⟨s2, st1.append st2, hm2, hcs2, hhm2⟩

/-- Sequence two expression fragments as in an argument list: the second runs
with the first's outputs as extra temporaries and contributes one value. -/
theorem SimE.compArgs {yst : EvmState} {V : VEnv yul} {off k : Nat}
    {is1 is2 : List Instr} {out1 : List U256} {v : U256}
    {yst1 yst2 : EvmState} (hlen : out1.length = k)
    (h1 : SimE yst V off is1 out1 yst1)
    (h2 : SimE yst1 V (off + k) is2 [v] yst2) :
    SimE yst V off (is1 ++ is2) (v :: out1) yst2 := by
  obtain ⟨b1, H1⟩ := h1
  obtain ⟨b2, H2⟩ := h2
  refine ⟨b1 + b2, ?_⟩
  intro code pre post τ σ s hcode hf hm hpc hstk hτ hgas
  obtain ⟨s1, st1, hf1, hm1, hpc1, hstk1, hg1⟩ :=
    H1 code pre (assembleBytes is2 ++ post) τ σ s
      (by rw [hcode]; congr 1; simp [assembleBytes_append]) hf hm hpc hstk hτ
      (by omega)
  obtain ⟨s2, st2, hf2, hm2, hpc2, hstk2, hg2⟩ :=
    H2 code (pre ++ assembleBytes is1) post (out1.map conv ++ τ) σ s1
      (by rw [hcode]; congr 1; simp [assembleBytes_append]) hf1 hm1
      (by rw [hpc1]; congr 1; simp) (by simpa [List.append_assoc] using hstk1)
      (by simp [hlen, hτ, Nat.add_comm]) (by omega)
  refine ⟨s2, st1.append st2, hf2, hm2, ?_,
    by simpa [List.append_assoc] using hstk2, by omega⟩
  rw [hpc2]
  congr 1
  simp [assembleBytes_append]
  omega

/-- An expression fragment followed by a halting one (later argument
evaluated fine, earlier argument halts). -/
theorem SimE.compArgsHalt {yst : EvmState} {V : VEnv yul} {off k : Nat}
    {is1 is2 : List Instr} {out1 : List U256}
    {yst1 yst2 : EvmState} (hlen : out1.length = k)
    (h1 : SimE yst V off is1 out1 yst1)
    (h2 : SimEHalt yst1 V (off + k) is2 yst2) :
    SimEHalt yst V off (is1 ++ is2) yst2 := by
  obtain ⟨b1, H1⟩ := h1
  obtain ⟨b2, H2⟩ := h2
  refine ⟨b1 + b2, ?_⟩
  intro code pre post τ σ s hcode hf hm hpc hstk hτ hgas
  obtain ⟨s1, st1, hf1, hm1, hpc1, hstk1, hg1⟩ :=
    H1 code pre (assembleBytes is2 ++ post) τ σ s
      (by rw [hcode]; congr 1; simp [assembleBytes_append]) hf hm hpc hstk hτ
      (by omega)
  obtain ⟨s2, st2, hm2, hcs2, hhm2⟩ :=
    H2 code (pre ++ assembleBytes is1) post (out1.map conv ++ τ) σ s1
      (by rw [hcode]; congr 1; simp [assembleBytes_append]) hf1 hm1
      (by rw [hpc1]; congr 1; simp) (by simpa [List.append_assoc] using hstk1)
      (by simp [hlen, hτ, Nat.add_comm]) (by omega)
  exact ⟨s2, st1.append st2, hm2, hcs2, hhm2⟩

/-- A halting expression fragment ignores anything compiled after it. -/
theorem SimEHalt.extend {yst : EvmState} {V : VEnv yul} {off : Nat}
    {is1 : List Instr} {yst' : EvmState}
    (h : SimEHalt yst V off is1 yst') (is2 : List Instr) :
    SimEHalt yst V off (is1 ++ is2) yst' := by
  obtain ⟨b, H⟩ := h
  refine ⟨b, ?_⟩
  intro code pre post τ σ s hcode hf hm hpc hstk hτ hgas
  exact H code pre (assembleBytes is2 ++ post) τ σ s
    (by rw [hcode]; congr 1; simp [assembleBytes_append]) hf hm hpc hstk hτ hgas

theorem SimS.nil {yst : EvmState} {V : VEnv yul} : SimS yst V [] yst V := by
  refine ⟨0, ?_⟩
  intro code pre post σ s hcode hf hm hpc hstk hgas
  exact ⟨s, .refl s, hf, hm, by simpa using hpc, hstk, by omega⟩

theorem SimS.comp {yst : EvmState} {V V1 V2 : VEnv yul}
    {is1 is2 : List Instr} {yst1 yst2 : EvmState}
    (h1 : SimS yst V is1 yst1 V1) (h2 : SimS yst1 V1 is2 yst2 V2) :
    SimS yst V (is1 ++ is2) yst2 V2 := by
  obtain ⟨b1, H1⟩ := h1
  obtain ⟨b2, H2⟩ := h2
  refine ⟨b1 + b2, ?_⟩
  intro code pre post σ s hcode hf hm hpc hstk hgas
  obtain ⟨s1, st1, hf1, hm1, hpc1, hstk1, hg1⟩ :=
    H1 code pre (assembleBytes is2 ++ post) σ s
      (by rw [hcode]; congr 1; simp [assembleBytes_append]) hf hm hpc hstk
      (by omega)
  obtain ⟨s2, st2, hf2, hm2, hpc2, hstk2, hg2⟩ :=
    H2 code (pre ++ assembleBytes is1) post σ s1
      (by rw [hcode]; congr 1; simp [assembleBytes_append]) hf1 hm1
      (by rw [hpc1]; congr 1; simp) hstk1 (by omega)
  refine ⟨s2, st1.append st2, hf2, hm2, ?_, hstk2, by omega⟩
  rw [hpc2]
  congr 1
  simp [assembleBytes_append]
  omega

theorem SimS.compHalt {yst : EvmState} {V V1 : VEnv yul}
    {is1 is2 : List Instr} {yst1 yst2 : EvmState}
    (h1 : SimS yst V is1 yst1 V1) (h2 : SimSHalt yst1 V1 is2 yst2) :
    SimSHalt yst V (is1 ++ is2) yst2 := by
  obtain ⟨b1, H1⟩ := h1
  obtain ⟨b2, H2⟩ := h2
  refine ⟨b1 + b2, ?_⟩
  intro code pre post σ s hcode hf hm hpc hstk hgas
  obtain ⟨s1, st1, hf1, hm1, hpc1, hstk1, hg1⟩ :=
    H1 code pre (assembleBytes is2 ++ post) σ s
      (by rw [hcode]; congr 1; simp [assembleBytes_append]) hf hm hpc hstk
      (by omega)
  obtain ⟨s2, st2, hm2, hcs2, hhm2⟩ :=
    H2 code (pre ++ assembleBytes is1) post σ s1
      (by rw [hcode]; congr 1; simp [assembleBytes_append]) hf1 hm1
      (by rw [hpc1]; congr 1; simp) hstk1 (by omega)
  exact ⟨s2, st1.append st2, hm2, hcs2, hhm2⟩

theorem SimSHalt.extend {yst : EvmState} {V : VEnv yul} {is1 : List Instr}
    {yst' : EvmState} (h : SimSHalt yst V is1 yst') (is2 : List Instr) :
    SimSHalt yst V (is1 ++ is2) yst' := by
  obtain ⟨b, H⟩ := h
  refine ⟨b, ?_⟩
  intro code pre post σ s hcode hf hm hpc hstk hgas
  exact H code pre (assembleBytes is2 ++ post) σ s
    (by rw [hcode]; congr 1; simp [assembleBytes_append]) hf hm hpc hstk hgas

/-- An expression fragment in statement position (`off = 0`, no outputs). -/
theorem SimE.toSimS {yst : EvmState} {V : VEnv yul} {is : List Instr}
    {yst' : EvmState} (h : SimE yst V 0 is [] yst') : SimS yst V is yst' V := by
  obtain ⟨b, H⟩ := h
  refine ⟨b, ?_⟩
  intro code pre post σ s hcode hf hm hpc hstk hgas
  obtain ⟨s', hsteps, hf', hm', hpc', hstk', hg'⟩ :=
    H code pre post [] σ s hcode hf hm hpc (by simpa using hstk) rfl hgas
  exact ⟨s', hsteps, hf', hm', hpc', by simpa using hstk', hg'⟩

/-- `let x := e`: the produced value becomes the new innermost variable. -/
theorem SimE.toSimSLet {yst : EvmState} {V : VEnv yul} {is : List Instr}
    {x : Ident} {v : U256} {yst' : EvmState}
    (h : SimE yst V 0 is [v] yst') : SimS yst V is yst' ((x, v) :: V) := by
  obtain ⟨b, H⟩ := h
  refine ⟨b, ?_⟩
  intro code pre post σ s hcode hf hm hpc hstk hgas
  obtain ⟨s', hsteps, hf', hm', hpc', hstk', hg'⟩ :=
    H code pre post [] σ s hcode hf hm hpc (by simpa using hstk) rfl hgas
  exact ⟨s', hsteps, hf', hm', hpc', hstk', hg'⟩

/-- A halting expression fragment in statement position. -/
theorem SimEHalt.toSimSHalt {yst : EvmState} {V : VEnv yul} {is : List Instr}
    {yst' : EvmState} (h : SimEHalt yst V 0 is yst') : SimSHalt yst V is yst' := by
  obtain ⟨b, H⟩ := h
  refine ⟨b, ?_⟩
  intro code pre post σ s hcode hf hm hpc hstk hgas
  exact H code pre post [] σ s hcode hf hm hpc (by simpa using hstk) rfl hgas

/-! ### Leaves -/

private theorem set_append_left {α : Type} (l₁ l₂ : List α) (i : Nat) (a : α)
    (h : i < l₁.length) : (l₁ ++ l₂).set i a = l₁.set i a ++ l₂ := by
  induction l₁ generalizing i with
  | nil => simp at h
  | cons x l ih =>
    cases i with
    | zero => rfl
    | succ i =>
      show x :: (l ++ l₂).set i a = _
      rw [ih _ (by simpa using h)]
      rfl

theorem SimOk.nil {yst : EvmState} {ins : List U256} :
    SimOk yst [] ins ins yst := by
  refine ⟨0, ?_⟩
  intro code pre post σ s hcode hf hm hpc hstk hgas
  exact ⟨s, .refl s, hf, hm, by simpa using hpc, hstk, by omega⟩

theorem SimOk.comp {yst : EvmState} {is1 is2 : List Instr}
    {ins out1 out2 : List U256} {yst1 yst2 : EvmState}
    (h1 : SimOk yst is1 ins out1 yst1) (h2 : SimOk yst1 is2 out1 out2 yst2) :
    SimOk yst (is1 ++ is2) ins out2 yst2 := by
  obtain ⟨b1, H1⟩ := h1
  obtain ⟨b2, H2⟩ := h2
  refine ⟨b1 + b2, ?_⟩
  intro code pre post σ s hcode hf hm hpc hstk hgas
  obtain ⟨s1, st1, hf1, hm1, hpc1, hstk1, hg1⟩ :=
    H1 code pre (assembleBytes is2 ++ post) σ s
      (by rw [hcode]; congr 1; simp [assembleBytes_append]) hf hm hpc hstk
      (by omega)
  obtain ⟨s2, st2, hf2, hm2, hpc2, hstk2, hg2⟩ :=
    H2 code (pre ++ assembleBytes is1) post σ s1
      (by rw [hcode]; congr 1; simp [assembleBytes_append]) hf1 hm1
      (by rw [hpc1]; congr 1; simp) hstk1 (by omega)
  refine ⟨s2, st1.append st2, hf2, hm2, ?_, hstk2, by omega⟩
  rw [hpc2]
  congr 1
  simp [assembleBytes_append]
  omega

theorem simOk_push {yst : EvmState} (u : U256) :
    SimOk yst [.push (conv u)] [] [u] yst := by
  refine ⟨40000, ?_⟩
  intro code pre post σ s hcode hf hm hpc hstk hgas
  have hbytes : assembleBytes [Instr.push (conv u)] = (Instr.push (conv u)).bytes := by
    simp
  have hlen : (assembleBytes [Instr.push (conv u)]).length = 33 := by
    rw [hbytes]
    exact Instr.size_push (conv u)
  have hcode' : code = mkCode (pre ++ (Instr.push (conv u)).bytes ++ post) := by
    rw [hcode, hbytes]
  obtain ⟨s', hstep, hf', hm', hpc', hstk', hg'⟩ :=
    pushStep hcode' hf hm hpc (by simpa using hstk) hgas
  refine ⟨s', .trans hstep (.refl _), hf', hm', ?_, hstk', hg'⟩
  rw [hpc', hlen]

theorem simOk_op {yop : Op} {o : Operation} (hop : opTable yop = some o)
    {args rets : List U256} {yst yst' : EvmState}
    (hyul : stepOp yop args yst = some (.ok rets yst')) :
    SimOk yst [.op o] args rets yst' := by
  refine ⟨opBound yop args, ?_⟩
  intro code pre post σ s hcode hf hm hpc hstk hgas
  have hbytes : assembleBytes [Instr.op o] = (Instr.op o).bytes := by
    simp
  have hlen : (assembleBytes [Instr.op o]).length = 1 := by
    rw [hbytes]
    exact Instr.size_op o
  have hcode' : code = mkCode (pre ++ (Instr.op o).bytes ++ post) := by
    rw [hcode, hbytes]
  obtain ⟨s', hstep, hf', hm', hpc', hstk', hg'⟩ :=
    opStep hop hyul hcode' hf hm hpc hstk hgas
  refine ⟨s', .trans hstep (.refl _), hf', hm', ?_, hstk', hg'⟩
  rw [hpc', hlen]

theorem simHalt_op {yop : Op} {o : Operation} (hop : opTable yop = some o)
    {args : List U256} {yst yst' : EvmState}
    (hyul : stepOp yop args yst = some (.halt yst')) :
    SimHalt yst [.op o] args yst' := by
  refine ⟨opBound yop args, ?_⟩
  intro code pre post σ s hcode hf hm hpc hstk hgas
  have hbytes : assembleBytes [Instr.op o] = (Instr.op o).bytes := by
    simp
  have hcode' : code = mkCode (pre ++ (Instr.op o).bytes ++ post) := by
    rw [hcode, hbytes]
  obtain ⟨s', hstep, hm', hcs', hhm'⟩ :=
    opStep hop hyul hcode' hf hm hpc hstk hgas
  exact ⟨s', .trans hstep (.refl _), hm', hcs', hhm'⟩

/-- Reading a variable: `DUP(off + idx + 1)` fetches its image. -/
theorem simE_var {yst : EvmState} {V : VEnv yul} {x : Ident} {v : U256}
    {off idx : Nat} (h16 : off + idx < 16)
    (hget : VEnv.get V x = some v)
    (hidx : (names V).findIdx? (fun y => y = x) = some idx) :
    SimE yst V off [.op (.Dup ⟨⟨off + idx, h16⟩⟩)] [v] yst := by
  refine ⟨40000, ?_⟩
  intro code pre post τ σ s hcode hf hm hpc hstk hτ hgas
  have hbytes : assembleBytes [Instr.op (.Dup ⟨⟨off + idx, h16⟩⟩)]
      = (Instr.op (.Dup ⟨⟨off + idx, h16⟩⟩)).bytes := by simp
  have hlen : (assembleBytes [Instr.op (.Dup ⟨⟨off + idx, h16⟩⟩)]).length = 1 := by
    rw [hbytes]
    exact Instr.size_op _
  have hidxlt : idx < V.length := by
    have := findIdx?_lt _ hidx
    simpa using this
  have hgetstack : s.stack[(⟨off + idx, h16⟩ : Fin 16).val]? = some (conv v) := by
    have h1 : ((τ ++ vimg V) ++ σ)[off + idx]? = some (conv v) := by
      rw [List.getElem?_append_left (by simp; omega),
        List.getElem?_append_right (by omega),
        show off + idx - τ.length = idx from by omega]
      exact vimg_get hget hidx
    rw [hstk]
    exact h1
  obtain ⟨s', hstep, hf', hm', hpc', hstk', hg'⟩ :=
    dupStep (n := ⟨off + idx, h16⟩) (by rw [hcode, hbytes]) hf hm hpc
      hgetstack hgas
  refine ⟨s', .trans hstep (.refl _), hf', hm', ?_, ?_, hg'⟩
  · rw [hlen]
    exact hpc'
  · rw [hstk', hstk]
    rfl

set_option maxRecDepth 100000 in
/-- Assigning a variable: the compiled expression's value gets swapped into
the slot and the old value popped. -/
theorem simS_assign {yst yst' : EvmState} {V : VEnv yul} {x : Ident} {v : U256}
    {is : List Instr} {idx : Nat} (h16 : idx < 16)
    (hidx : (names V).findIdx? (fun y => y = x) = some idx)
    (he : SimE yst V 0 is [v] yst') :
    SimS yst V (is ++ [.op (.Swap ⟨⟨idx, h16⟩⟩), .op .POP]) yst'
      (VEnv.set V x v) := by
  obtain ⟨b, H⟩ := he
  refine ⟨b + 40000 + 40000, ?_⟩
  intro code pre post σ s hcode hf hm hpc hstk hgas
  have hidxlt : idx < V.length := by
    have := findIdx?_lt _ hidx
    simpa using this
  obtain ⟨s1, st1, hf1, hm1, hpc1, hstk1, hg1⟩ :=
    H code pre
      (assembleBytes [Instr.op (.Swap ⟨⟨idx, h16⟩⟩), Instr.op .POP] ++ post)
      [] σ s
      (by rw [hcode]; congr 1; simp [assembleBytes_append]) hf hm hpc
      (by simpa using hstk) rfl (by omega)
  have hstk1' : s1.stack = conv v :: (vimg V ++ σ) := by simpa using hstk1
  have hwit : (vimg V ++ σ)[idx]?
      = some ((vimg V ++ σ)[idx]'(by simp; omega)) :=
    List.getElem?_eq_getElem _
  have hswap : s1.stack.exchange 0 (idx + 1)
      = some ((vimg V ++ σ)[idx]'(by simp; omega)
          :: (vimg V ++ σ).set idx (conv v)) := by
    rw [hstk1']
    unfold List.exchange
    rw [show (conv v :: (vimg V ++ σ))[idx + 1]? = (vimg V ++ σ)[idx]? from rfl]
    rw [hwit]
    rfl
  have hcode2 : code = mkCode ((pre ++ assembleBytes is)
      ++ (Instr.op (.Swap ⟨⟨idx, h16⟩⟩)).bytes
      ++ ((Instr.op .POP).bytes ++ post)) := by
    rw [hcode]
    congr 1
    simp [assembleBytes_append]
  have hpc1' : s1.pc = UInt256.ofNat ((pre ++ assembleBytes is).length) := by
    rw [hpc1]
    congr 1
    simp
  obtain ⟨s2, st2, hf2, hm2, hpc2, hstk2, hg2⟩ :=
    swapStep (pre := pre ++ assembleBytes is)
      (post := (Instr.op .POP).bytes ++ post) (n := ⟨idx, h16⟩)
      hcode2 hf1 hm1 hpc1' hswap (by omega)
  have hcode3 : code = mkCode ((pre ++ assembleBytes is
      ++ (Instr.op (.Swap ⟨⟨idx, h16⟩⟩)).bytes)
      ++ (Instr.op .POP).bytes ++ post) := by
    rw [hcode]
    congr 1
    simp [assembleBytes_append]
  have hpc2' : s2.pc = UInt256.ofNat ((pre ++ assembleBytes is
      ++ (Instr.op (.Swap ⟨⟨idx, h16⟩⟩)).bytes).length) := by
    rw [hpc2]
    congr 1
    simp
    omega
  have hgas3 : 40000 ≤ s2.gasAvailable := by omega
  obtain ⟨s3, st3, hf3, hm3, hpc3, hstk3, hg3⟩ :=
    popStep (pre := pre ++ assembleBytes is
        ++ (Instr.op (.Swap ⟨⟨idx, h16⟩⟩)).bytes) (post := post)
      hcode3 hf2 hm2 hpc2' hstk2 hgas3
  have hgfin : s.gasAvailable - (b + 40000 + 40000) ≤ s3.gasAvailable := by omega
  refine ⟨s3, (st1.snoc st2).snoc st3, hf3, hm3, ?_, ?_, hgfin⟩
  · rw [hpc3]
    congr 1
    simp [assembleBytes_append]
    omega
  · rw [hstk3, set_append_left _ _ _ _ (by simp; omega), vimg_set v hidx]

/-! ### Zero-initialized declarations and block-exit pops -/

private theorem simOk_zeros {yst : EvmState} (n : Nat) :
    SimOk yst (List.replicate n (.push (conv 0))) []
      (List.replicate n (0 : U256)) yst := by
  induction n with
  | zero => exact SimOk.nil
  | succ n ih =>
    have h := SimOk.comp (simOk_push (yst := yst) 0) (ih.frame [0])
    rw [show [Instr.push (conv 0)] ++ List.replicate n (.push (conv 0))
        = List.replicate (n + 1) (.push (conv 0)) from by
      rw [List.replicate_succ]; rfl] at h
    rw [show List.replicate n (0 : U256) ++ [(0 : U256)]
        = List.replicate (n + 1) (0 : U256) from by
      rw [show ([(0 : U256)] : List U256) = List.replicate 1 0 from rfl,
        ← List.replicate_add]] at h
    exact h

private theorem vimg_bindZeros (xs : List Ident) :
    vimg (YulSemantics.bindZeros yul xs) = List.replicate xs.length (conv 0) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    show conv (YulSemantics.Dialect.zero yul)
        :: vimg (YulSemantics.bindZeros yul xs)
      = conv 0 :: List.replicate xs.length (conv 0)
    rw [ih]
    rfl

/-- `let x₁, …, xₙ` — push a zero per name. -/
theorem simS_letZero {yst : EvmState} {V : VEnv yul} (xs : List Ident) :
    SimS yst V (List.replicate xs.length (.push (conv 0))) yst
      (YulSemantics.bindZeros yul xs ++ V) := by
  obtain ⟨b, H⟩ := simOk_zeros (yst := yst) xs.length
  refine ⟨b, ?_⟩
  intro code pre post σ s hcode hf hm hpc hstk hgas
  obtain ⟨s', hsteps, hf', hm', hpc', hstk', hg'⟩ :=
    H code pre post (vimg V ++ σ) s hcode hf hm hpc (by simpa using hstk) hgas
  refine ⟨s', hsteps, hf', hm', hpc', ?_, hg'⟩
  rw [hstk', vimg_append, vimg_bindZeros]
  simp

/-- Popping the block-local part of the variable region on block exit. -/
theorem simS_dropPops {yst : EvmState} :
    ∀ (k : Nat) (Vb : VEnv yul), k ≤ Vb.length →
      SimS yst Vb (List.replicate k (.op .POP)) yst (Vb.drop k) := by
  intro k
  induction k with
  | zero =>
    intro Vb hk
    simpa using SimS.nil (yst := yst) (V := Vb)
  | succ k ih =>
    intro Vb hk
    rcases Vb with _ | ⟨p, Vb⟩
    · simp at hk
    · have hpop : SimS yst (p :: Vb) [.op .POP] yst Vb := by
        refine ⟨40000, ?_⟩
        intro code pre post σ s hcode hf hm hpc hstk hgas
        have hbytes : assembleBytes [Instr.op .POP] = (Instr.op .POP).bytes := by
          simp
        obtain ⟨s', hstep, hf', hm', hpc', hstk', hg'⟩ :=
          popStep (by rw [hcode, hbytes]) hf hm hpc
            (show s.stack = conv p.2 :: (vimg Vb ++ σ) from by rw [hstk]; rfl) hgas
        refine ⟨s', .trans hstep (.refl _), hf', hm', ?_, hstk', hg'⟩
        rw [show (assembleBytes [Instr.op .POP]).length = 1 from by
          rw [hbytes]; exact Instr.size_op _]
        exact hpc'
      have h := SimS.comp hpop (ih Vb (by simpa using hk))
      rw [show [Instr.op .POP] ++ List.replicate k (.op .POP)
          = List.replicate (k + 1) (.op .POP) from by
        rw [List.replicate_succ]; rfl] at h
      exact h

/-! ### Compiler inversion -/

private theorem compileExpr_var_inv {Γ : List Ident} {off : Nat} {x : Ident}
    {is : List Instr} (h : compileExpr Γ off (.var x) = some is) :
    ∃ idx, ∃ h16 : off + idx < 16,
      Γ.findIdx? (fun y => y = x) = some idx ∧
      is = [.op (.Dup ⟨⟨off + idx, h16⟩⟩)] := by
  simp only [compileExpr] at h
  cases hidx : Γ.findIdx? (fun y => y = x) with
  | none => rw [hidx] at h; simp at h
  | some idx =>
    rw [hidx] at h
    simp only [Option.bind_eq_bind, Option.bind_some] at h
    by_cases h16 : off + idx < 16
    · rw [dif_pos h16] at h
      simp only [Option.pure_def, Option.some.injEq] at h
      exact ⟨idx, h16, rfl, h.symm⟩
    · rw [dif_neg h16] at h
      simp at h

private theorem compileExpr_builtin_inv {Γ : List Ident} {off : Nat} {op : Op}
    {args : List (YulSemantics.Expr Op)} {is : List Instr}
    (h : compileExpr Γ off (.builtin op args) = some is) :
    ∃ argCode o, compileArgs Γ off args = some argCode ∧ opTable op = some o ∧
      is = argCode ++ [.op o] := by
  simp only [compileExpr] at h
  cases ha : compileArgs Γ off args with
  | none => rw [ha] at h; simp at h
  | some argCode =>
    rw [ha] at h
    cases ho : opTable op with
    | none => rw [ho] at h; simp at h
    | some o =>
      rw [ho] at h
      simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq] at h
      exact ⟨argCode, o, rfl, rfl, h.symm⟩

private theorem compileArgs_cons_inv {Γ : List Ident} {off : Nat}
    {e : YulSemantics.Expr Op} {rest : List (YulSemantics.Expr Op)}
    {is : List Instr} (h : compileArgs Γ off (e :: rest) = some is) :
    ∃ restCode eCode, compileArgs Γ off rest = some restCode ∧
      compileExpr Γ (off + rest.length) e = some eCode ∧
      is = restCode ++ eCode := by
  simp only [compileArgs] at h
  cases hr : compileArgs Γ off rest with
  | none => rw [hr] at h; simp at h
  | some restCode =>
    rw [hr] at h
    cases he : compileExpr Γ (off + rest.length) e with
    | none => rw [he] at h; simp at h
    | some eCode =>
      rw [he] at h
      simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq] at h
      exact ⟨restCode, eCode, rfl, rfl, h.symm⟩

private theorem compileStmt_exprStmt_inv {pc : Nat} {Γ : List Ident}
    {e : YulSemantics.Expr Op} {is : List Instr} {Γ' : List Ident}
    (h : compileStmt pc Γ (.exprStmt e) = some (is, Γ')) :
    compileExpr Γ 0 e = some is ∧ Γ' = Γ := by
  simp only [compileStmt] at h
  cases he : compileExpr Γ 0 e with
  | none => rw [he] at h; simp at h
  | some c =>
    rw [he] at h
    simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
      Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨by rw [h.1], h.2.symm⟩

private theorem compileStmt_letNone_inv {pc : Nat} {Γ : List Ident} {xs : List Ident}
    {is : List Instr} {Γ' : List Ident}
    (h : compileStmt pc Γ (.letDecl xs none) = some (is, Γ')) :
    is = List.replicate xs.length (.push (conv 0)) ∧ Γ' = xs ++ Γ := by
  simp only [compileStmt, Option.pure_def, Option.some.injEq,
    Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

private theorem compileStmt_letSome_inv {pc : Nat} {Γ : List Ident} {vars : List Ident}
    {e : YulSemantics.Expr Op} {is : List Instr} {Γ' : List Ident}
    (h : compileStmt pc Γ (.letDecl vars (some e)) = some (is, Γ')) :
    ∃ x, vars = [x] ∧ compileExpr Γ 0 e = some is ∧ Γ' = x :: Γ := by
  rcases vars with _ | ⟨x, _ | ⟨y, t⟩⟩ <;> simp only [compileStmt] at h
  · simp at h
  · cases he : compileExpr Γ 0 e with
    | none => rw [he] at h; simp at h
    | some c =>
      rw [he] at h
      simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨x, rfl, by rw [h.1], h.2.symm⟩
  · simp at h

private theorem compileStmt_assign_inv {pc : Nat} {Γ : List Ident} {vars : List Ident}
    {e : YulSemantics.Expr Op} {is : List Instr} {Γ' : List Ident}
    (h : compileStmt pc Γ (.assign vars e) = some (is, Γ')) :
    ∃ x eCode idx, ∃ h16 : idx < 16, vars = [x] ∧
      compileExpr Γ 0 e = some eCode ∧
      Γ.findIdx? (fun y => y = x) = some idx ∧
      is = eCode ++ [.op (.Swap ⟨⟨idx, h16⟩⟩), .op .POP] ∧ Γ' = Γ := by
  rcases vars with _ | ⟨x, _ | ⟨y, t⟩⟩ <;> simp only [compileStmt] at h
  · simp at h
  · cases he : compileExpr Γ 0 e with
    | none => rw [he] at h; simp at h
    | some c =>
      rw [he] at h
      cases hidx : Γ.findIdx? (fun y => y = x) with
      | none => rw [hidx] at h; simp at h
      | some idx =>
        rw [hidx] at h
        simp only [Option.bind_eq_bind, Option.bind_some] at h
        by_cases h16 : idx < 16
        · rw [dif_pos h16] at h
          simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
          exact ⟨x, c, idx, h16, rfl, rfl, hidx, h.1.symm, h.2.symm⟩
        · rw [dif_neg h16] at h
          simp at h
  · simp at h

private theorem compileStmt_block_inv {pc : Nat} {Γ : List Ident}
    {body : List (YulSemantics.Stmt Op)} {is : List Instr} {Γ' : List Ident}
    (h : compileStmt pc Γ (.block body) = some (is, Γ')) :
    ∃ isb Γb, compileStmts pc Γ body = some (isb, Γb) ∧
      is = isb ++ List.replicate (Γb.length - Γ.length) (.op .POP) ∧
      Γ' = Γ := by
  simp only [compileStmt] at h
  cases hb : compileStmts pc Γ body with
  | none => rw [hb] at h; simp at h
  | some p =>
    obtain ⟨isb, Γb⟩ := p
    rw [hb] at h
    simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
      Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨isb, Γb, rfl, h.1.symm, h.2.symm⟩

private theorem compileStmts_cons_inv {pc : Nat} {Γ : List Ident}
    {st : YulSemantics.Stmt Op} {rest : List (YulSemantics.Stmt Op)}
    {is : List Instr} {Γ' : List Ident}
    (h : compileStmts pc Γ (st :: rest) = some (is, Γ')) :
    ∃ is1 Γ1 is2, compileStmt pc Γ st = some (is1, Γ1) ∧
      compileStmts (pc + (assembleBytes is1).length) Γ1 rest = some (is2, Γ') ∧
      is = is1 ++ is2 := by
  simp only [compileStmts] at h
  cases hs : compileStmt pc Γ st with
  | none => rw [hs] at h; simp at h
  | some p =>
    obtain ⟨is1, Γ1⟩ := p
    rw [hs] at h
    simp only [Option.bind_eq_bind, Option.bind_some] at h
    cases hr : compileStmts (pc + (assembleBytes is1).length) Γ1 rest with
    | none => rw [hr] at h; simp at h
    | some q =>
      obtain ⟨is2, Γ2⟩ := q
      rw [hr] at h
      simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨is1, Γ1, is2, rfl, by rw [← h.2]; exact hr, h.1.symm⟩

private theorem compileStmt_cond_inv {pc : Nat} {Γ : List Ident}
    {c : YulSemantics.Expr Op} {body : List (YulSemantics.Stmt Op)}
    {is : List Instr} {Γ' : List Ident}
    (h : compileStmt pc Γ (.cond c body) = some (is, Γ')) :
    ∃ cCode bodyCode Γb,
      compileExpr Γ 0 c = some cCode ∧
      compileStmts (pc + (assembleBytes cCode).length + 35) Γ body
        = some (bodyCode, Γb) ∧
      is = cCode
        ++ [.op .ISZERO,
            .push (UInt256.ofNat (pc + (assembleBytes cCode).length + 35
              + (assembleBytes bodyCode).length + (Γb.length - Γ.length))),
            .op .JUMPI]
        ++ bodyCode ++ List.replicate (Γb.length - Γ.length) (.op .POP)
        ++ [.op .JUMPDEST] ∧
      Γ' = Γ := by
  simp only [compileStmt] at h
  cases hcc : compileExpr Γ 0 c with
  | none => rw [hcc] at h; simp at h
  | some cCode =>
    rw [hcc] at h
    simp only [Option.bind_eq_bind, Option.bind_some] at h
    cases hbc : compileStmts (pc + (assembleBytes cCode).length + 35) Γ body with
    | none => rw [hbc] at h; simp at h
    | some p =>
      obtain ⟨bodyCode, Γb⟩ := p
      rw [hbc] at h
      simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨cCode, bodyCode, Γb, rfl, hbc, h.1.symm, h.2.symm⟩

/-- The layout only ever grows by prepending. -/
private theorem compileStmt_suffix {pc : Nat} {Γ : List Ident} {s : YulSemantics.Stmt Op}
    {is : List Instr} {Γ' : List Ident}
    (h : compileStmt pc Γ s = some (is, Γ')) : ∃ Δ, Γ' = Δ ++ Γ := by
  cases s with
  | exprStmt e =>
    obtain ⟨-, rfl⟩ := compileStmt_exprStmt_inv h
    exact ⟨[], rfl⟩
  | letDecl xs val =>
    cases val with
    | none =>
      obtain ⟨-, rfl⟩ := compileStmt_letNone_inv h
      exact ⟨xs, rfl⟩
    | some e =>
      obtain ⟨x, -, -, rfl⟩ := compileStmt_letSome_inv h
      exact ⟨[x], rfl⟩
  | assign vars e =>
    obtain ⟨x, c, idx, h16, -, -, -, -, rfl⟩ := compileStmt_assign_inv h
    exact ⟨[], rfl⟩
  | block body =>
    obtain ⟨isb, Γb, -, -, rfl⟩ := compileStmt_block_inv h
    exact ⟨[], rfl⟩
  | funDef n ps rs b => simp [compileStmt] at h
  | cond c b =>
    obtain ⟨cc, bc, Γb, hcc, hbc, rfl, rfl⟩ := compileStmt_cond_inv h
    exact ⟨[], rfl⟩
  | switch c cs d => simp [compileStmt] at h
  | forLoop i c p b => simp [compileStmt] at h
  | «break» => simp [compileStmt] at h
  | «continue» => simp [compileStmt] at h
  | leave => simp [compileStmt] at h

private theorem compileStmts_suffix {ss : List (YulSemantics.Stmt Op)} :
    ∀ {pc Γ is Γ'}, compileStmts pc Γ ss = some (is, Γ') → ∃ Δ, Γ' = Δ ++ Γ := by
  induction ss with
  | nil =>
    intro pc Γ is Γ' h
    simp only [compileStmts, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨[], h.2.symm⟩
  | cons st rest ih =>
    intro pc Γ is Γ' h
    obtain ⟨is1, Γ1, is2, hs, hr, rfl⟩ := compileStmts_cons_inv h
    obtain ⟨Δ1, rfl⟩ := compileStmt_suffix hs
    obtain ⟨Δ2, rfl⟩ := ih hr
    exact ⟨Δ2 ++ Δ1, by simp⟩

private theorem names_bindZeros (xs : List Ident) :
    names (YulSemantics.bindZeros yul xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    show x :: names (YulSemantics.bindZeros yul xs) = x :: xs
    rw [ih]

/-! ### Positioned statement simulation

Statements containing jumps produce position-dependent code: the `if`
fragment embeds the absolute address of its closing `JUMPDEST`. `SimSP`
refines `SimS` with (i) the fragment's compile-time position `pcc` and (ii)
an instruction-aligned prefix, which is what the jumpdest analysis needs to
accept our targets. Position-independent fragments lift via `SimS.toSimSP`.
-/

theorem conv_ofNat (n : Nat) :
    conv (BitVec.ofNat 256 n) = UInt256.ofNat n := by
  apply u256ext
  rw [conv_toNat, toNat_u256_ofNat]
  simp

@[simp] theorem length_assembleBytes_replicate_op (n : Nat) (o : Operation) :
    (assembleBytes (List.replicate n (Instr.op o))).length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [List.replicate_succ, ih]
    omega

def SimSP (pcc : Nat) (yst : EvmState) (V : VEnv yul) (is : List Instr)
    (yst' : EvmState) (V' : VEnv yul) : Prop :=
  ∃ b : Nat, ∀ (code : ByteArray) (preIs : List Instr) (post : List UInt8)
    (σ : List UInt256) (s : State),
    code = mkCode (assembleBytes preIs ++ assembleBytes is ++ post) →
    (assembleBytes preIs).length = pcc →
    FrameOK code s → StateMatch yst s →
    s.pc = UInt256.ofNat pcc →
    s.stack = vimg V ++ σ →
    b ≤ s.gasAvailable →
    ∃ s', Steps s s' ∧ FrameOK code s' ∧ StateMatch yst' s'
      ∧ s'.pc = UInt256.ofNat (pcc + (assembleBytes is).length)
      ∧ s'.stack = vimg V' ++ σ
      ∧ s.gasAvailable - b ≤ s'.gasAvailable

def SimSHaltP (pcc : Nat) (yst : EvmState) (V : VEnv yul) (is : List Instr)
    (yst' : EvmState) : Prop :=
  ∃ b : Nat, ∀ (code : ByteArray) (preIs : List Instr) (post : List UInt8)
    (σ : List UInt256) (s : State),
    code = mkCode (assembleBytes preIs ++ assembleBytes is ++ post) →
    (assembleBytes preIs).length = pcc →
    FrameOK code s → StateMatch yst s →
    s.pc = UInt256.ofNat pcc →
    s.stack = vimg V ++ σ →
    b ≤ s.gasAvailable →
    ∃ s', Steps s s' ∧ StateMatch yst' s' ∧ s'.callStack = []
      ∧ HaltedMatch yst' s'

theorem SimS.toSimSP {yst : EvmState} {V : VEnv yul} {is : List Instr}
    {yst' : EvmState} {V' : VEnv yul} (h : SimS yst V is yst' V') (pcc : Nat) :
    SimSP pcc yst V is yst' V' := by
  obtain ⟨b, H⟩ := h
  refine ⟨b, ?_⟩
  intro code preIs post σ s hcode hpre hf hm hpc hstk hgas
  obtain ⟨s', hsteps, hf', hm', hpc', hstk', hg'⟩ :=
    H code (assembleBytes preIs) post σ s hcode hf hm (by rw [hpc, hpre]) hstk
      hgas
  exact ⟨s', hsteps, hf', hm', by rw [hpc', hpre], hstk', hg'⟩

theorem SimSHalt.toSimSHaltP {yst : EvmState} {V : VEnv yul} {is : List Instr}
    {yst' : EvmState} (h : SimSHalt yst V is yst') (pcc : Nat) :
    SimSHaltP pcc yst V is yst' := by
  obtain ⟨b, H⟩ := h
  refine ⟨b, ?_⟩
  intro code preIs post σ s hcode hpre hf hm hpc hstk hgas
  exact H code (assembleBytes preIs) post σ s hcode hf hm (by rw [hpc, hpre])
    hstk hgas

theorem SimSP.comp {pcc : Nat} {yst : EvmState} {V V1 V2 : VEnv yul}
    {is1 is2 : List Instr} {yst1 yst2 : EvmState}
    (h1 : SimSP pcc yst V is1 yst1 V1)
    (h2 : SimSP (pcc + (assembleBytes is1).length) yst1 V1 is2 yst2 V2) :
    SimSP pcc yst V (is1 ++ is2) yst2 V2 := by
  obtain ⟨b1, H1⟩ := h1
  obtain ⟨b2, H2⟩ := h2
  refine ⟨b1 + b2, ?_⟩
  intro code preIs post σ s hcode hpre hf hm hpc hstk hgas
  obtain ⟨s1, st1, hf1, hm1, hpc1, hstk1, hg1⟩ :=
    H1 code preIs (assembleBytes is2 ++ post) σ s
      (by rw [hcode]; congr 1; simp [assembleBytes_append]) hpre hf hm hpc hstk
      (by omega)
  obtain ⟨s2, st2, hf2, hm2, hpc2, hstk2, hg2⟩ :=
    H2 code (preIs ++ is1) post σ s1
      (by rw [hcode]; congr 1; simp [assembleBytes_append])
      (by simp [assembleBytes_append, hpre]) hf1 hm1
      (by rw [hpc1]) hstk1 (by omega)
  refine ⟨s2, st1.append st2, hf2, hm2, ?_, hstk2, by omega⟩
  rw [hpc2]
  congr 1
  simp [assembleBytes_append]
  omega

theorem SimSP.compHalt {pcc : Nat} {yst : EvmState} {V V1 : VEnv yul}
    {is1 is2 : List Instr} {yst1 yst2 : EvmState}
    (h1 : SimSP pcc yst V is1 yst1 V1)
    (h2 : SimSHaltP (pcc + (assembleBytes is1).length) yst1 V1 is2 yst2) :
    SimSHaltP pcc yst V (is1 ++ is2) yst2 := by
  obtain ⟨b1, H1⟩ := h1
  obtain ⟨b2, H2⟩ := h2
  refine ⟨b1 + b2, ?_⟩
  intro code preIs post σ s hcode hpre hf hm hpc hstk hgas
  obtain ⟨s1, st1, hf1, hm1, hpc1, hstk1, hg1⟩ :=
    H1 code preIs (assembleBytes is2 ++ post) σ s
      (by rw [hcode]; congr 1; simp [assembleBytes_append]) hpre hf hm hpc hstk
      (by omega)
  obtain ⟨s2, st2, hm2, hcs2, hhm2⟩ :=
    H2 code (preIs ++ is1) post σ s1
      (by rw [hcode]; congr 1; simp [assembleBytes_append])
      (by simp [assembleBytes_append, hpre]) hf1 hm1
      (by rw [hpc1]) hstk1 (by omega)
  exact ⟨s2, st1.append st2, hm2, hcs2, hhm2⟩

theorem SimSHaltP.extend {pcc : Nat} {yst : EvmState} {V : VEnv yul}
    {is1 : List Instr} {yst' : EvmState}
    (h : SimSHaltP pcc yst V is1 yst') (is2 : List Instr) :
    SimSHaltP pcc yst V (is1 ++ is2) yst' := by
  obtain ⟨b, H⟩ := h
  refine ⟨b, ?_⟩
  intro code preIs post σ s hcode hpre hf hm hpc hstk hgas
  exact H code preIs (assembleBytes is2 ++ post) σ s
    (by rw [hcode]; congr 1; simp [assembleBytes_append]) hpre hf hm hpc hstk
    hgas

/-! ### The simulation induction -/

/-- The induction motive: what a source derivation for each syntactic class
means on the target, conditional on the compiler accepting the syntax against
the layout the runtime environment realizes (`names V`). -/
def Motive (V : VEnv yul) (yst : EvmState) :
    YulSemantics.Code Op → YulSemantics.Res yul → Prop
  | .expr e, .eres (.vals vs yst') =>
      ∀ off is, compileExpr (names V) off e = some is → SimE yst V off is vs yst'
  | .expr e, .eres (.halt yst') =>
      ∀ off is, compileExpr (names V) off e = some is → SimEHalt yst V off is yst'
  | .args es, .eres (.vals vs yst') =>
      ∀ off is, compileArgs (names V) off es = some is →
        vs.length = es.length ∧ SimE yst V off is vs yst'
  | .args es, .eres (.halt yst') =>
      ∀ off is, compileArgs (names V) off es = some is → SimEHalt yst V off is yst'
  | .stmt st, .sres V' yst' o =>
      ∀ pc is Γ', compileStmt pc (names V) st = some (is, Γ') →
        (o = .normal ∧ Γ' = names V' ∧ SimSP pc yst V is yst' V') ∨
        (o = .halt ∧ SimSHaltP pc yst V is yst')
  | .stmts ss, .sres V' yst' o =>
      ∀ pc is Γ', compileStmts pc (names V) ss = some (is, Γ') →
        (o = .normal ∧ Γ' = names V' ∧ SimSP pc yst V is yst' V') ∨
        (o = .halt ∧ SimSHaltP pc yst V is yst')
  | _, _ => True

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
/-- Every source derivation over compiled syntax is simulated by the target. -/
theorem sim {funs : YulSemantics.FunEnv yul} {V : VEnv yul}
    {yst : EvmState} {c : YulSemantics.Code Op} {res : YulSemantics.Res yul}
    (h : YulSemantics.Step yul funs V yst c res) : Motive V yst c res := by
  induction h with
  | lit =>
    intro off is hc
    simp only [compileExpr, Option.some.injEq] at hc
    subst hc
    exact (simOk_push _).toSimE _ _
  | var hget =>
    intro off is hc
    obtain ⟨idx, h16, hidx, rfl⟩ := compileExpr_var_inv hc
    exact simE_var h16 hget hidx
  | builtinOk hargs hb ihargs =>
    intro off is hc
    obtain ⟨argCode, o, harg, hopt, rfl⟩ := compileExpr_builtin_inv hc
    exact ((ihargs off argCode harg).2).compOk (simOk_op hopt hb)
  | builtinHalt hargs hb ihargs =>
    intro off is hc
    obtain ⟨argCode, o, harg, hopt, rfl⟩ := compileExpr_builtin_inv hc
    exact ((ihargs off argCode harg).2).compHaltOk (simHalt_op hopt hb)
  | builtinArgsHalt hargs ihargs =>
    intro off is hc
    obtain ⟨argCode, o, harg, hopt, rfl⟩ := compileExpr_builtin_inv hc
    exact (ihargs off argCode harg).extend [.op o]
  | callOk _ _ _ _ _ _ _ =>
    intro off is hc
    simp [compileExpr] at hc
  | callHalt _ _ _ _ _ _ =>
    intro off is hc
    simp [compileExpr] at hc
  | callArgsHalt _ _ =>
    intro off is hc
    simp [compileExpr] at hc
  | argsNil =>
    intro off is hc
    simp only [compileArgs, Option.some.injEq] at hc
    subst hc
    exact ⟨rfl, (SimOk.nil).toSimE _ _⟩
  | argsCons hrest hhead ihrest ihhead =>
    intro off is hc
    obtain ⟨restCode, eCode, hr, he, rfl⟩ := compileArgs_cons_inv hc
    obtain ⟨hlen, hR⟩ := ihrest off restCode hr
    have hH := ihhead (off + _) eCode he
    exact ⟨by simpa using hlen, hR.compArgs hlen hH⟩
  | argsRestHalt hrest ihrest =>
    intro off is hc
    obtain ⟨restCode, eCode, hr, he, rfl⟩ := compileArgs_cons_inv hc
    exact (ihrest off restCode hr).extend eCode
  | argsHeadHalt hrest hhead ihrest ihhead =>
    intro off is hc
    obtain ⟨restCode, eCode, hr, he, rfl⟩ := compileArgs_cons_inv hc
    obtain ⟨hlen, hR⟩ := ihrest off restCode hr
    exact hR.compArgsHalt hlen (ihhead (off + _) eCode he)
  | funDef =>
    intro pc is Γ' hc
    simp [compileStmt] at hc
  | @block funs V yst body Vb stb o hbody ihbody =>
    intro pc is Γ' hc
    obtain ⟨isb, Γb, hbs, rfl, rfl⟩ := compileStmt_block_inv hc
    rcases ihbody pc isb Γb hbs with ⟨ho, hΓb, hS⟩ | ⟨ho, hH⟩
    · subst ho
      obtain ⟨Δ, hΔ⟩ := compileStmts_suffix hbs
      have hVbΓ : Vb.length = Γb.length := by
        rw [hΓb]; simp
      have hΔlen : Γb.length = Δ.length + V.length := by
        rw [hΔ]; simp
      refine Or.inl ⟨rfl, ?_, ?_⟩
      · refine Eq.symm ?_
        show names (Vb.drop (Vb.length - V.length)) = _
        have hmapdrop : names (Vb.drop (Vb.length - V.length))
            = (names Vb).drop (Vb.length - V.length) := by
          simp [names, List.map_drop]
        rw [hmapdrop, ← hΓb, hΔ]
        rw [List.drop_left' (show Δ.length = Vb.length - V.length from by omega)]
      · rw [show Γb.length - (names V).length = Vb.length - V.length from by
          simp; omega]
        show SimSP pc yst V _ stb (Vb.drop (Vb.length - V.length))
        exact SimSP.comp hS
          (((simS_dropPops _ Vb (by omega))).toSimSP _)
    · exact Or.inr ⟨ho, hH.extend _⟩
  | letZero =>
    intro pc is Γ' hc
    obtain ⟨rfl, rfl⟩ := compileStmt_letNone_inv hc
    exact Or.inl ⟨rfl, by rw [names_append, names_bindZeros],
      (simS_letZero _).toSimSP pc⟩
  | letVal hexp hlen ihexp =>
    intro pc is Γ' hc
    obtain ⟨x, hv, hce, rfl⟩ := compileStmt_letSome_inv hc
    subst hv
    rename_i vals _
    rcases vals with _ | ⟨v0, _ | ⟨v1, t⟩⟩ <;> simp at hlen
    exact Or.inl ⟨rfl, rfl, ((ihexp 0 is hce).toSimSLet).toSimSP pc⟩
  | letHalt hexp ihexp =>
    intro pc is Γ' hc
    obtain ⟨x, hv, hce, rfl⟩ := compileStmt_letSome_inv hc
    exact Or.inr ⟨rfl, ((ihexp 0 is hce).toSimSHalt).toSimSHaltP pc⟩
  | assignVal hexp hlen ihexp =>
    intro pc is Γ' hc
    obtain ⟨x, c, idx, h16, hv, hce, hidx, rfl, rfl⟩ := compileStmt_assign_inv hc
    subst hv
    rename_i vals _
    rcases vals with _ | ⟨v0, _ | ⟨v1, t⟩⟩ <;> simp at hlen
    have hsm : VEnv.setMany ‹VEnv yul› [x] [v0] = VEnv.set ‹VEnv yul› x v0 := rfl
    rw [hsm]
    exact Or.inl ⟨rfl, (names_set _ _ _).symm,
      (simS_assign h16 hidx (ihexp 0 c hce)).toSimSP pc⟩
  | assignHalt hexp ihexp =>
    intro pc is Γ' hc
    obtain ⟨x, c, idx, h16, hv, hce, hidx, rfl, rfl⟩ := compileStmt_assign_inv hc
    exact Or.inr ⟨rfl, (((ihexp 0 c hce).toSimSHalt).extend _).toSimSHaltP pc⟩
  | exprStmt hexp ihexp =>
    intro pc is Γ' hc
    obtain ⟨hce, rfl⟩ := compileStmt_exprStmt_inv hc
    exact Or.inl ⟨rfl, rfl, ((ihexp 0 is hce).toSimS).toSimSP pc⟩
  | exprStmtHalt hexp ihexp =>
    intro pc is Γ' hc
    obtain ⟨hce, rfl⟩ := compileStmt_exprStmt_inv hc
    exact Or.inr ⟨rfl, ((ihexp 0 is hce).toSimSHalt).toSimSHaltP pc⟩
  | @ifTrue funs V yst c body cv yst1 V2 yst2 o hcstep hcv hblock ihc ihblock =>
    intro pc is Γ' hcomp
    obtain ⟨cCode, bodyCode, Γb, hcc, hbc, rfl, rfl⟩ := compileStmt_cond_inv hcomp
    have hpfx : SimE yst V 0
        (cCode ++ [.op .ISZERO] ++ [.push (UInt256.ofNat (pc
          + (assembleBytes cCode).length + 35 + (assembleBytes bodyCode).length
          + (Γb.length - (names V).length)))])
        [BitVec.ofNat 256 (pc + (assembleBytes cCode).length + 35
          + (assembleBytes bodyCode).length + (Γb.length - (names V).length)),
         YulSemantics.EVM.b2w (cv = 0)] yst1 := by
      refine SimE.compArgs (k := 1) rfl
        ((ihc 0 cCode hcc).compOk (simOk_op (yop := .iszero) rfl rfl)) ?_
      rw [← conv_ofNat]
      exact (simOk_push _).toSimE V 1
    have hcondz : (conv (YulSemantics.EVM.b2w (cv = 0))).toNat = 0 := by
      rw [show YulSemantics.EVM.b2w (cv = 0) = (0 : U256) from by
        unfold YulSemantics.EVM.b2w
        rw [if_neg (show ¬(decide (cv = (0 : U256)) = true) from
          fun hd => hcv (of_decide_eq_true hd))]]
      rfl
    have hblockc : compileStmt (pc + (assembleBytes cCode).length + 35) (names V)
        (.block body) = some (bodyCode
          ++ List.replicate (Γb.length - (names V).length) (.op .POP), names V) := by
      simp only [compileStmt]
      rw [hbc]
      rfl
    rcases ihblock (pc + (assembleBytes cCode).length + 35) _ _ hblockc
        with ⟨ho, hΓ, hSP⟩ | ⟨ho, hHP⟩
    · subst ho
      refine Or.inl ⟨rfl, hΓ, ?_⟩
      obtain ⟨bP, HP⟩ := hpfx
      obtain ⟨bB, HB⟩ := hSP
      refine ⟨bP + 40000 + bB + 40000, ?_⟩
      intro code preIs post σ s hcode hpre hf hm hpc hstk hgas
      obtain ⟨s1, st1, hf1, hm1, hpc1, hstk1, hg1⟩ :=
        HP code (assembleBytes preIs)
          (assembleBytes ([.op .JUMPI] ++ bodyCode
            ++ List.replicate (Γb.length - (names V).length) (.op .POP)
            ++ [.op .JUMPDEST]) ++ post) [] σ s
          (by rw [hcode]; congr 1; simp [assembleBytes_append]) hf hm
          (by rw [hpc, hpre]) (by rw [hstk]; rfl) rfl (by omega)
      obtain ⟨s2, st2, hf2, hm2, hpc2, hstk2, hg2⟩ :=
        jumpiNotTakenStep
          (pre := assembleBytes preIs ++ assembleBytes (cCode ++ [.op .ISZERO]
            ++ [.push (UInt256.ofNat (pc + (assembleBytes cCode).length + 35
              + (assembleBytes bodyCode).length
              + (Γb.length - (names V).length)))]))
          (post := assembleBytes (bodyCode
            ++ List.replicate (Γb.length - (names V).length) (.op .POP)
            ++ [.op .JUMPDEST]) ++ post)
          (by rw [hcode]; congr 1; simp [assembleBytes_append]) hf1 hm1
          (by rw [hpc1]; congr 1; simp [assembleBytes_append])
          (by rw [hstk1]; rfl) hcondz (by omega)
      obtain ⟨s3, st3, hf3, hm3, hpc3, hstk3, hg3⟩ :=
        HB code (preIs ++ (cCode ++ [.op .ISZERO]
            ++ [.push (UInt256.ofNat (pc + (assembleBytes cCode).length + 35
              + (assembleBytes bodyCode).length
              + (Γb.length - (names V).length)))] ++ [.op .JUMPI]))
          (assembleBytes [Instr.op .JUMPDEST] ++ post) σ s2
          (by rw [hcode]; congr 1; simp [assembleBytes_append])
          (by simp [assembleBytes_append, hpre]; omega) hf2 hm2
          (by rw [hpc2]; congr 1; simp [assembleBytes_append]; omega)
          hstk2 (by omega)
      obtain ⟨s4, st4, hf4, hm4, hpc4, hstk4, hg4⟩ :=
        jumpdestStep
          (pre := assembleBytes preIs ++ assembleBytes (cCode ++ [.op .ISZERO]
            ++ [.push (UInt256.ofNat (pc + (assembleBytes cCode).length + 35
              + (assembleBytes bodyCode).length
              + (Γb.length - (names V).length)))] ++ [.op .JUMPI] ++ bodyCode
            ++ List.replicate (Γb.length - (names V).length) (.op .POP)))
          (post := post)
          (by rw [hcode]; congr 1; simp [assembleBytes_append]) hf3 hm3
          (by rw [hpc3]; congr 1; simp [assembleBytes_append]; omega)
          (by omega)
      refine ⟨s4, ((st1.snoc st2).append st3).snoc st4, hf4, hm4, ?_,
        by rw [hstk4, hstk3], by omega⟩
      rw [hpc4]
      congr 1
      simp [assembleBytes_append]
      omega
    · refine Or.inr ⟨ho, ?_⟩
      obtain ⟨bP, HP⟩ := hpfx
      obtain ⟨bB, HB⟩ := hHP
      refine ⟨bP + 40000 + bB, ?_⟩
      intro code preIs post σ s hcode hpre hf hm hpc hstk hgas
      obtain ⟨s1, st1, hf1, hm1, hpc1, hstk1, hg1⟩ :=
        HP code (assembleBytes preIs)
          (assembleBytes ([.op .JUMPI] ++ bodyCode
            ++ List.replicate (Γb.length - (names V).length) (.op .POP)
            ++ [.op .JUMPDEST]) ++ post) [] σ s
          (by rw [hcode]; congr 1; simp [assembleBytes_append]) hf hm
          (by rw [hpc, hpre]) (by rw [hstk]; rfl) rfl (by omega)
      obtain ⟨s2, st2, hf2, hm2, hpc2, hstk2, hg2⟩ :=
        jumpiNotTakenStep
          (pre := assembleBytes preIs ++ assembleBytes (cCode ++ [.op .ISZERO]
            ++ [.push (UInt256.ofNat (pc + (assembleBytes cCode).length + 35
              + (assembleBytes bodyCode).length
              + (Γb.length - (names V).length)))]))
          (post := assembleBytes (bodyCode
            ++ List.replicate (Γb.length - (names V).length) (.op .POP)
            ++ [.op .JUMPDEST]) ++ post)
          (by rw [hcode]; congr 1; simp [assembleBytes_append]) hf1 hm1
          (by rw [hpc1]; congr 1; simp [assembleBytes_append])
          (by rw [hstk1]; rfl) hcondz (by omega)
      obtain ⟨s3, st3, hm3, hcs3, hhm3⟩ :=
        HB code (preIs ++ (cCode ++ [.op .ISZERO]
            ++ [.push (UInt256.ofNat (pc + (assembleBytes cCode).length + 35
              + (assembleBytes bodyCode).length
              + (Γb.length - (names V).length)))] ++ [.op .JUMPI]))
          (assembleBytes [Instr.op .JUMPDEST] ++ post) σ s2
          (by rw [hcode]; congr 1; simp [assembleBytes_append])
          (by simp [assembleBytes_append, hpre]; omega) hf2 hm2
          (by rw [hpc2]; congr 1; simp [assembleBytes_append]; omega)
          hstk2 (by omega)
      exact ⟨s3, (st1.snoc st2).append st3, hm3, hcs3, hhm3⟩
  | @ifFalse funs V yst c body cv yst1 hcstep hcv ihc =>
    intro pc is Γ' hcomp
    obtain ⟨cCode, bodyCode, Γb, hcc, hbc, rfl, rfl⟩ := compileStmt_cond_inv hcomp
    have hpfx : SimE yst V 0
        (cCode ++ [.op .ISZERO] ++ [.push (UInt256.ofNat (pc
          + (assembleBytes cCode).length + 35 + (assembleBytes bodyCode).length
          + (Γb.length - (names V).length)))])
        [BitVec.ofNat 256 (pc + (assembleBytes cCode).length + 35
          + (assembleBytes bodyCode).length + (Γb.length - (names V).length)),
         YulSemantics.EVM.b2w (cv = 0)] yst1 := by
      refine SimE.compArgs (k := 1) rfl
        ((ihc 0 cCode hcc).compOk (simOk_op (yop := .iszero) rfl rfl)) ?_
      rw [← conv_ofNat]
      exact (simOk_push _).toSimE V 1
    have hcond1 : (conv (YulSemantics.EVM.b2w (cv = 0))).toNat ≠ 0 := by
      rw [show YulSemantics.EVM.b2w (cv = 0) = (1 : U256) from by
        unfold YulSemantics.EVM.b2w
        rw [if_pos (decide_eq_true (show cv = (0 : U256) from hcv))]]
      decide
    refine Or.inl ⟨rfl, rfl, ?_⟩
    obtain ⟨bP, HP⟩ := hpfx
    refine ⟨bP + 40000 + 40000, ?_⟩
    intro code preIs post σ s hcode hpre hf hm hpc hstk hgas
    obtain ⟨s1, st1, hf1, hm1, hpc1, hstk1, hg1⟩ :=
      HP code (assembleBytes preIs)
        (assembleBytes ([.op .JUMPI] ++ bodyCode
          ++ List.replicate (Γb.length - (names V).length) (.op .POP)
          ++ [.op .JUMPDEST]) ++ post) [] σ s
        (by rw [hcode]; congr 1; simp [assembleBytes_append]) hf hm
        (by rw [hpc, hpre]) (by rw [hstk]; rfl) rfl (by omega)
    have hdlt : pc + (assembleBytes cCode).length + 35
        + (assembleBytes bodyCode).length + (Γb.length - (names V).length)
        < 2 ^ 256 := by
      have hsz := hf.codeSmall
      rw [hcode] at hsz
      simp [assembleBytes_append, hpre] at hsz
      simp
      omega
    have hvalid : Decode.isValidJumpDest code
        (UInt256.ofNat (pc + (assembleBytes cCode).length + 35
          + (assembleBytes bodyCode).length
          + (Γb.length - (names V).length))).toNat = true := by
      rw [toNat_ofNat_of_lt hdlt]
      have hb := isValidJumpDest_boundary
        (preIs ++ (cCode ++ [.op .ISZERO]
          ++ [.push (UInt256.ofNat (pc + (assembleBytes cCode).length + 35
            + (assembleBytes bodyCode).length
            + (Γb.length - (names V).length)))] ++ [.op .JUMPI] ++ bodyCode
          ++ List.replicate (Γb.length - (names V).length) (.op .POP))) post
      rw [show (assembleBytes (preIs ++ (cCode ++ [.op .ISZERO]
            ++ [.push (UInt256.ofNat (pc + (assembleBytes cCode).length + 35
              + (assembleBytes bodyCode).length
              + (Γb.length - (names V).length)))] ++ [.op .JUMPI] ++ bodyCode
            ++ List.replicate (Γb.length - (names V).length) (.op .POP)))).length
          = pc + (assembleBytes cCode).length + 35
          + (assembleBytes bodyCode).length + (Γb.length - (names V).length)
          from by simp [assembleBytes_append, hpre]; omega] at hb
      rw [show mkCode (assembleBytes (preIs ++ (cCode ++ [.op .ISZERO]
          ++ [.push (UInt256.ofNat (pc + (assembleBytes cCode).length + 35
            + (assembleBytes bodyCode).length
            + (Γb.length - (names V).length)))] ++ [.op .JUMPI] ++ bodyCode
          ++ List.replicate (Γb.length - (names V).length) (.op .POP)))
          ++ (Instr.op .JUMPDEST).bytes ++ post) = code from by
        rw [hcode]; congr 1; simp [assembleBytes_append]] at hb
      exact hb
    obtain ⟨s2, st2, hf2, hm2, hpc2, hstk2, hg2⟩ :=
      jumpiTakenStep
        (pre := assembleBytes preIs ++ assembleBytes (cCode ++ [.op .ISZERO]
          ++ [.push (UInt256.ofNat (pc + (assembleBytes cCode).length + 35
            + (assembleBytes bodyCode).length
            + (Γb.length - (names V).length)))]))
        (post := assembleBytes (bodyCode
          ++ List.replicate (Γb.length - (names V).length) (.op .POP)
          ++ [.op .JUMPDEST]) ++ post)
        (by rw [hcode]; congr 1; simp [assembleBytes_append]) hf1 hm1
        (by rw [hpc1]; congr 1; simp [assembleBytes_append])
        (by rw [hstk1]; rfl) hcond1 hvalid (by omega)
    obtain ⟨s3, st3, hf3, hm3, hpc3, hstk3, hg3⟩ :=
      jumpdestStep
        (pre := assembleBytes preIs ++ assembleBytes (cCode ++ [.op .ISZERO]
          ++ [.push (UInt256.ofNat (pc + (assembleBytes cCode).length + 35
            + (assembleBytes bodyCode).length
            + (Γb.length - (names V).length)))] ++ [.op .JUMPI] ++ bodyCode
          ++ List.replicate (Γb.length - (names V).length) (.op .POP)))
        (post := post)
        (by rw [hcode]; congr 1; simp [assembleBytes_append]) hf2 hm2
        (by rw [hpc2]; congr 1; simp [assembleBytes_append, hpre]; omega)
        (by omega)
    refine ⟨s3, (st1.snoc st2).snoc st3, hf3, hm3, ?_, by rw [hstk3, hstk2]; simp, by omega⟩
    rw [hpc3]
    congr 1
    simp [assembleBytes_append, hpre]
    omega
  | @ifHalt funs V yst c body yst1 hcstep ihc =>
    intro pc is Γ' hcomp
    obtain ⟨cCode, bodyCode, Γb, hcc, hbc, rfl, rfl⟩ := compileStmt_cond_inv hcomp
    have h := (ihc 0 cCode hcc).extend ([.op .ISZERO,
      .push (UInt256.ofNat (pc + (assembleBytes cCode).length + 35
        + (assembleBytes bodyCode).length + (Γb.length - (names V).length))),
      .op .JUMPI] ++ bodyCode
      ++ List.replicate (Γb.length - (names V).length) (.op .POP)
      ++ [.op .JUMPDEST])
    refine Or.inr ⟨rfl, ?_⟩
    have h2 := (h.toSimSHalt).toSimSHaltP pc
    refine ⟨h2.choose, ?_⟩
    intro code preIs post σ s hcode hpre hf hm hpc hstk hgas
    exact h2.choose_spec code preIs post σ s
      (by rw [hcode]; congr 1; simp [assembleBytes_append]) hpre hf hm hpc hstk
      hgas
  | switchExec _ _ _ _ =>
    intro pc is Γ' hc
    simp [compileStmt] at hc
  | switchHalt _ _ =>
    intro pc is Γ' hc
    simp [compileStmt] at hc
  | forLoop _ _ _ _ =>
    intro pc is Γ' hc
    simp [compileStmt] at hc
  | forInitHalt _ _ =>
    intro pc is Γ' hc
    simp [compileStmt] at hc
  | «break» =>
    intro pc is Γ' hc
    simp [compileStmt] at hc
  | «continue» =>
    intro pc is Γ' hc
    simp [compileStmt] at hc
  | leave =>
    intro pc is Γ' hc
    simp [compileStmt] at hc
  | seqNil =>
    intro pc is Γ' hc
    simp only [compileStmts, Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    exact Or.inl ⟨rfl, rfl, (SimS.nil).toSimSP pc⟩
  | seqCons hs hrest ihs ihrest =>
    intro pc is Γ' hc
    obtain ⟨is1, Γ1, is2, h1, h2, rfl⟩ := compileStmts_cons_inv hc
    rcases ihs pc is1 Γ1 h1 with ⟨_, hΓ1, hok1⟩ | ⟨hcontra, _⟩
    · rw [hΓ1] at h2
      rcases ihrest (pc + (assembleBytes is1).length) is2 Γ' h2
          with ⟨ho, hΓ2, hok2⟩ | ⟨ho, hh2⟩
      · exact Or.inl ⟨ho, hΓ2, hok1.comp hok2⟩
      · exact Or.inr ⟨ho, hok1.compHalt hh2⟩
    · exact absurd hcontra (by simp)
  | seqStop hs hne ihs =>
    intro pc is Γ' hc
    obtain ⟨is1, Γ1, is2, h1, h2, rfl⟩ := compileStmts_cons_inv hc
    rcases ihs pc is1 Γ1 h1 with ⟨ho, _⟩ | ⟨ho, hh⟩
    · exact absurd ho hne
    · exact Or.inr ⟨ho, hh.extend is2⟩
  | loopDone _ _ => trivial
  | loopCondHalt _ => trivial
  | loopStep _ _ _ _ _ _ _ _ _ _ => trivial
  | loopPostHalt _ _ _ _ _ _ _ _ => trivial
  | loopBreak _ _ _ _ _ => trivial
  | loopLeave _ _ _ _ _ => trivial
  | loopBodyHalt _ _ _ _ _ => trivial

/-! ### The main theorem -/

/-- **Compiler correctness** (straight-line fragment with variables and
nested blocks). If the compiler accepts `prog` and the Yul big-step semantics
runs `prog` from `st₀` to `st'` with outcome `o`, then there is a gas bound
`b` such that from *every* initial EVM state that matches `st₀`, executes the
assembled bytecode, and holds at least `b` gas, the EVM semantics reaches a
matching final state:

* `o = .normal` — the code runs off its end (implicit `STOP`) and halts with
  `.Success`, in a state whose memory/storage/transient storage match `st'`;
* `o = .halt` — the code halts exactly as `st'.halted` records
  (`stop ↦ Success`, `return ↦ Returned` + payload, `revert ↦ Reverted` +
  payload, `invalid ↦ InvalidInstruction`), again with matching state. -/
theorem compile_correct {prog : YulSemantics.Block Op} {is : List Instr}
    (hcomp : compileProgram prog = some is)
    {yst0 : EvmState} {V' : VEnv yul} {yst' : EvmState}
    {o : Outcome}
    (hrun : YulSemantics.Run yul prog yst0 V' yst' o) :
    ∃ b : Nat, ∀ s0 : State,
      FrameOK (assemble is) s0 → StateMatch yst0 s0 →
      s0.pc = UInt256.ofNat 0 → s0.stack = [] → b ≤ s0.gasAvailable →
      ∃ s', Steps s0 s' ∧ s'.callStack = [] ∧ StateMatch yst' s' ∧
        ((o = .normal ∧ s'.halt = .Success ∧ s'.hReturn = .empty) ∨
         (o = .halt ∧ HaltedMatch yst' s')) := by
  obtain ⟨⟨is0, Γ'⟩, hstmts, hfst⟩ := Option.map_eq_some_iff.mp hcomp
  simp only at hfst
  subst hfst
  cases hrun with
  | block hbody =>
    have hsim := sim hbody 0 is0 Γ' hstmts
    have hassemble : assemble is0
        = mkCode (assembleBytes ([] : List Instr) ++ assembleBytes is0 ++ []) := by
      show ByteArray.mk _ = ByteArray.mk _
      congr 1
      simp
    rcases hsim with ⟨ho, _, hok⟩ | ⟨ho, hh⟩
    · subst ho
      obtain ⟨b, H⟩ := hok
      refine ⟨b, ?_⟩
      intro s0 hf hm hpc hstk hgas
      obtain ⟨s1, hsteps, hf1, hm1, hpc1, hstk1, hg1⟩ :=
        H (assemble is0) [] [] [] s0 hassemble rfl hf hm (by simpa using hpc)
          (by rw [hstk]; rfl) hgas
      obtain ⟨s2, hstep2, hm2, hcs2, hhalt2, hret2⟩ :=
        stopStep (is := is0) hf1 hm1 rfl (by simpa using hpc1)
      exact ⟨s2, hsteps.snoc hstep2, hcs2, hm2, Or.inl ⟨rfl, hhalt2, hret2⟩⟩
    · subst ho
      obtain ⟨b, H⟩ := hh
      refine ⟨b, ?_⟩
      intro s0 hf hm hpc hstk hgas
      obtain ⟨s', hsteps, hm', hcs', hhm⟩ :=
        H (assemble is0) [] [] [] s0 hassemble rfl hf hm (by simpa using hpc)
          (by rw [hstk]; rfl) hgas
      exact ⟨s', hsteps, hcs', hm', Or.inr ⟨rfl, hhm⟩⟩

/-- Result-level corollary: the compiled bytecode `Eval`s to the
`ExecutionResult` the Yul outcome corresponds to (`.success` for a program
that falls through; `resultOf` of the recorded halt otherwise). -/
theorem compile_correct_eval {prog : YulSemantics.Block Op} {is : List Instr}
    (hcomp : compileProgram prog = some is)
    {yst0 : EvmState} {V' : VEnv yul} {yst' : EvmState}
    {o : Outcome}
    (hrun : YulSemantics.Run yul prog yst0 V' yst' o) :
    ∃ b : Nat, ∀ s0 : State,
      FrameOK (assemble is) s0 → StateMatch yst0 s0 →
      s0.pc = UInt256.ofNat 0 → s0.stack = [] → b ≤ s0.gasAvailable →
      (o = .normal → Eval s0 .success) ∧
      (o = .halt → ∃ hk, yst'.halted = some hk ∧ Eval s0 (resultOf hk)) := by
  obtain ⟨b, H⟩ := compile_correct hcomp hrun
  refine ⟨b, ?_⟩
  intro s0 hf hm hpc hstk hgas
  obtain ⟨s', hsteps, hcs', hm', hres⟩ := H s0 hf hm hpc hstk hgas
  constructor
  · intro ho
    subst ho
    rcases hres with ⟨_, hhalt, _⟩ | ⟨hcontra, _⟩
    · have hr : s'.toResult = .success := State.toResult_success s' hhalt
      rw [← hr]
      exact Eval.iff_steps_halted.mpr ⟨s', hsteps, by rw [hhalt]; simp, hcs', rfl⟩
    · exact absurd hcontra (by simp)
  · intro ho
    subst ho
    rcases hres with ⟨hcontra, _⟩ | ⟨_, hhm⟩
    · exact absurd hcontra (by simp)
    · obtain ⟨hk, hyst, hhmatch⟩ := hhm
      refine ⟨hk, hyst, ?_⟩
      have hdone : s'.halt ≠ .Running ∧ s'.toResult = resultOf hk := by
        rcases hk with ⟨kind, payload⟩
        cases kind with
        | stop =>
          have hhalt : s'.halt = .Success := hhmatch
          exact ⟨by rw [hhalt]; simp, by
            rw [State.toResult_success s' hhalt]; rfl⟩
        | ret =>
          obtain ⟨hhalt, hpl⟩ := hhmatch
          have hpl' : s'.hReturn.toList = payload := hpl
          refine ⟨by rw [hhalt]; simp, ?_⟩
          rw [State.toResult_returned s' hhalt]
          show ExecutionResult.returned s'.hReturn = .returned (mkCode payload)
          rw [← hpl', mkCode_toList]
        | revert =>
          obtain ⟨hhalt, hpl⟩ := hhmatch
          have hpl' : s'.hReturn.toList = payload := hpl
          refine ⟨by rw [hhalt]; simp, ?_⟩
          rw [State.toResult_reverted s' hhalt]
          show ExecutionResult.reverted s'.hReturn = .reverted (mkCode payload)
          rw [← hpl', mkCode_toList]
        | invalid =>
          have hhalt : s'.halt = .Exception .InvalidInstruction := hhmatch
          exact ⟨by rw [hhalt]; simp, by
            rw [State.toResult_exception s' _ hhalt]; rfl⟩
      rw [← hdone.2]
      exact Eval.iff_steps_halted.mpr ⟨s', hsteps, hdone.1, hcs', rfl⟩

end YulEvmCompiler
