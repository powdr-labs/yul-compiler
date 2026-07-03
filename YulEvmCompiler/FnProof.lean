import YulEvmCompiler.Correctness
import YulEvmCompiler.Functions

/-!
# YulEvmCompiler.FnProof

Correctness lemmas for the function calling convention (see `FUNCTIONS_PLAN.md`).
This file is the verified counterpart of the codegen in
`YulEvmCompiler.Functions`; it is being built up in stages.

## Phase 1.2 — the return-value reshuffle

`retSwaps m = SWAP1; …; SWAPm` is the epilogue rotation that brings the return
address (sitting just below the `m` return values) back to the top while
preserving the return order. `retSwapsSteps` proves it: executed from a state
whose stack is `rvals ++ ret :: σ` (with `|rvals| = m ≤ 16`), it reaches a
state with stack `ret :: rvals ++ σ`, advancing the pc by `m` and leaving the
matched machine state untouched.
-/

namespace YulEvmCompiler

open EvmSemantics EvmSemantics.EVM
open YulSemantics.EVM (EvmState)
open YulSemantics (Expr Stmt Block Ident)
open YulSemantics.EVM (Op litValue)

/-- Chain two gas-consumption bounds (proved in a tiny context, so no `omega`
recursion over large ambient hypotheses). -/
private theorem gsub2 {a b c k₁ k₂ : Nat}
    (h₁ : a - k₁ ≤ b) (h₂ : b - k₂ ≤ c) : a - (k₁ + k₂) ≤ c := by omega

/-- The second step's gas need is met after the first step. -/
private theorem genough {a s₁ k₁ k₂ : Nat}
    (hb : k₁ + k₂ ≤ a) (h₁ : a - k₁ ≤ s₁) : k₂ ≤ s₁ := by omega

/-- Strip a summand from an upper bound. -/
private theorem gstrip {x y z : Nat} (h : x + y ≤ z) : x ≤ z := by omega

/-- `retSwaps m` assembles to exactly `m` (single-byte) instructions. -/
theorem length_assembleBytes_retSwaps (m : Nat) :
    (assembleBytes (retSwaps m)).length = m := by
  induction m with
  | zero => rfl
  | succ k ih =>
    rw [retSwaps, assembleBytes_append]
    simp [ih]

/-- Swapping stack index `0` with index `|rvinit|+1` in `x :: rvinit ++ ret :: σ`
yields `ret :: rvinit ++ x :: σ` — the single-step fact behind the rotation. -/
private theorem exchange_rot {α} (x ret : α) (rvinit σ : List α) :
    (x :: (rvinit ++ ret :: σ)).exchange 0 (rvinit.length + 1)
      = some (ret :: (rvinit ++ x :: σ)) := by
  unfold List.exchange
  have hj : (x :: (rvinit ++ ret :: σ))[rvinit.length + 1]? = some ret := by
    rw [List.getElem?_cons_succ, List.getElem?_append_right (by omega)]
    simp
  rw [List.getElem?_cons_zero, hj]
  show some (((x :: (rvinit ++ ret :: σ)).set 0 ret).set (rvinit.length + 1) x) = _
  rw [List.set_cons_zero, List.set_cons_succ, List.set_append_right _ _ (by omega)]
  simp

/-- **The return-value reshuffle is correct.** From a matching state whose stack
is `rvals ++ ret :: σ` (with `rvals.length = m ≤ 16`), executing the embedded
`retSwaps m` reaches a matching state with stack `ret :: rvals ++ σ`, pc
advanced by `m`, consuming at most `40000·m` gas. -/
theorem retSwapsSteps : ∀ (m : Nat), m ≤ 16 →
    ∀ (code : ByteArray) (pre post : List UInt8) (rvals : List UInt256)
      (ret : UInt256) (σ : List UInt256) (yst : EvmState) (s : State),
      rvals.length = m →
      code = mkCode (pre ++ assembleBytes (retSwaps m) ++ post) →
      FrameOK code s → StateMatch yst s →
      s.pc = UInt256.ofNat pre.length →
      s.stack = rvals ++ ret :: σ →
      40000 * m ≤ s.gasAvailable →
      ∃ s', Steps s s' ∧ FrameOK code s' ∧ StateMatch yst s'
        ∧ s'.pc = UInt256.ofNat (pre.length + m)
        ∧ s'.stack = ret :: rvals ++ σ
        ∧ s.gasAvailable - 40000 * m ≤ s'.gasAvailable := by
  intro m
  induction m with
  | zero =>
    intro _ code pre post rvals ret σ yst s hlen hcode hf hm hpc hstk hgas
    rw [List.length_eq_zero_iff] at hlen
    subst hlen
    exact ⟨s, .refl s, hf, hm, by simpa using hpc, by simpa using hstk, by omega⟩
  | succ k ih =>
    intro hm code pre post rvals ret σ yst s hlen hcode hf hm' hpc hstk hgas
    -- peel the last return value: rvals = rvinit ++ [x]
    have hne : rvals ≠ [] := by intro h; rw [h] at hlen; simp at hlen
    obtain ⟨x, rvinit, hsplit⟩ :
        ∃ x rvinit, rvals = rvinit ++ [x] := by
      refine ⟨rvals.getLast hne, rvals.dropLast, ?_⟩
      exact (List.dropLast_append_getLast hne).symm
    have hinit : rvinit.length = k := by
      have := hlen; rw [hsplit] at this; simpa using this
    have hk16 : k < 16 := by omega
    -- code splits as pre ++ retSwaps k ++ (SWAP k byte ++ post)
    have hcode1 : code = mkCode (pre ++ assembleBytes (retSwaps k)
        ++ ((Instr.op (.Swap ⟨k % 16, Nat.mod_lt _ (by decide)⟩)).bytes ++ post)) := by
      rw [hcode, retSwaps, assembleBytes_append]
      congr 1
      simp [List.append_assoc]
    have hgas' : 40000 * k + 40000 ≤ s.gasAvailable := by rw [← Nat.mul_succ]; exact hgas
    -- IH: run retSwaps k, treating x as the element below the k values
    obtain ⟨s1, st1, hf1, hm1, hpc1, hstk1, hg1⟩ :=
      ih (by omega) code pre
        ((Instr.op (.Swap ⟨k % 16, Nat.mod_lt _ (by decide)⟩)).bytes ++ post)
        rvinit x (ret :: σ) yst s hinit hcode1 hf hm' hpc
        (by rw [hstk, hsplit]; simp) (gstrip hgas')
    -- now SWAP(k+1): exchange 0 (k+1) on  x :: rvinit ++ ret :: σ
    have hkmod : k % 16 = k := Nat.mod_eq_of_lt hk16
    have hswap : s1.stack.exchange 0
        ((⟨k % 16, Nat.mod_lt _ (by decide)⟩ : Fin 16).val + 1)
        = some (ret :: (rvinit ++ x :: σ)) := by
      rw [hstk1]
      simp only [hkmod]
      rw [← hinit]
      exact exchange_rot x ret rvinit σ
    have hcode2 : code = mkCode ((pre ++ assembleBytes (retSwaps k))
        ++ (Instr.op (.Swap ⟨k % 16, Nat.mod_lt _ (by decide)⟩)).bytes ++ post) := by
      rw [hcode1]; congr 1; simp [List.append_assoc]
    have hpc1' : s1.pc = UInt256.ofNat (pre ++ assembleBytes (retSwaps k)).length := by
      rw [hpc1]; congr 1; simp [length_assembleBytes_retSwaps]
    obtain ⟨s2, hstep2, hf2, hm2, hpc2, hstk2, hg2⟩ :=
      swapStep (n := ⟨k % 16, Nat.mod_lt _ (by decide)⟩) hcode2 hf1 hm1 hpc1' hswap
        (genough hgas' hg1)
    refine ⟨s2, st1.snoc hstep2, hf2, hm2, ?_, ?_, ?_⟩
    · rw [hpc2]; congr 1; simp [length_assembleBytes_retSwaps, Nat.add_assoc]
    · rw [hstk2, hsplit]; simp
    · rw [Nat.mul_succ]; exact gsub2 hg1 hg2

/-- `POP×k` assembles to exactly `k` (single-byte) instructions. -/
theorem length_assembleBytes_replicate_pop (k : Nat) :
    (assembleBytes (List.replicate k (Instr.op .POP))).length = k := by
  induction k with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, assembleBytes_cons, List.length_append, Instr.length_bytes_op, ih]
    omega

/-- **`POP` repeated `k` times drops the top `k` stack elements.** From a matching
state whose stack is `drop ++ σ` (with `drop.length = k`), executing the embedded
`POP×k` reaches a matching state with stack `σ`, pc advanced by `k`. Used for the
callee epilogue that discards the `n` parameters before the return reshuffle. -/
theorem popsSteps : ∀ (k : Nat) (code : ByteArray) (pre post : List UInt8)
    (drop σ : List UInt256) (yst : EvmState) (s : State),
    drop.length = k →
    code = mkCode (pre ++ assembleBytes (List.replicate k (.op .POP)) ++ post) →
    FrameOK code s → StateMatch yst s →
    s.pc = UInt256.ofNat pre.length →
    s.stack = drop ++ σ →
    40000 * k ≤ s.gasAvailable →
    ∃ s', Steps s s' ∧ FrameOK code s' ∧ StateMatch yst s'
      ∧ s'.pc = UInt256.ofNat (pre.length + k)
      ∧ s'.stack = σ
      ∧ s.gasAvailable - 40000 * k ≤ s'.gasAvailable := by
  intro k
  induction k with
  | zero =>
    intro code pre post drop σ yst s hlen hcode hf hm hpc hstk hgas
    rw [List.length_eq_zero_iff] at hlen; subst hlen
    exact ⟨s, .refl s, hf, hm, by simpa using hpc, by simpa using hstk, by omega⟩
  | succ k ih =>
    intro code pre post drop σ yst s hlen hcode hf hm hpc hstk hgas
    -- peel the last (deepest) element popped: drop = dinit ++ [x]
    have hne : drop ≠ [] := by intro h; rw [h] at hlen; simp at hlen
    obtain ⟨x, dinit, hsplit⟩ : ∃ x dinit, drop = dinit ++ [x] :=
      ⟨drop.getLast hne, drop.dropLast, (List.dropLast_append_getLast hne).symm⟩
    have hinit : dinit.length = k := by have := hlen; rw [hsplit] at this; simpa using this
    have hgas' : 40000 * k + 40000 ≤ s.gasAvailable := by rw [← Nat.mul_succ]; exact hgas
    have hcode1 : code = mkCode (pre ++ assembleBytes (List.replicate k (.op .POP))
        ++ ((Instr.op .POP).bytes ++ post)) := by
      rw [hcode, List.replicate_succ', assembleBytes_append]
      congr 1; simp [List.append_assoc]
    obtain ⟨s1, st1, hf1, hm1, hpc1, hstk1, hg1⟩ :=
      ih code pre ((Instr.op .POP).bytes ++ post) dinit (x :: σ) yst s hinit hcode1 hf hm hpc
        (by rw [hstk, hsplit]; simp) (gstrip hgas')
    have hcode2 : code = mkCode ((pre ++ assembleBytes (List.replicate k (.op .POP)))
        ++ (Instr.op .POP).bytes ++ post) := by
      rw [hcode1]; simp [List.append_assoc]
    have hpc1' : s1.pc = UInt256.ofNat (pre ++ assembleBytes (List.replicate k (.op .POP))).length := by
      rw [hpc1]; congr 1; simp [length_assembleBytes_replicate_pop]
    obtain ⟨s2, hstep2, hf2, hm2, hpc2, hstk2, hg2⟩ :=
      popStep hcode2 hf1 hm1 hpc1' (by rw [hstk1]) (genough hgas' hg1)
    refine ⟨s2, st1.snoc hstep2, hf2, hm2, ?_, ?_, ?_⟩
    · rw [hpc2]; congr 1; simp [length_assembleBytes_replicate_pop, Nat.add_assoc]
    · rw [hstk2]
    · rw [Nat.mul_succ]; exact gsub2 hg1 hg2

/-- **The callee return sequence is correct.** From a matching state whose stack
is `paramvals ++ rvals ++ retaddr :: σ` (|paramvals| = n, |rvals| = m ≤ 16),
executing the embedded epilogue `POP×n ; SWAP1..SWAPm ; JUMP` drops the `n`
parameters, rotates `retaddr` to the top, and jumps to it — reaching pc =
`retaddr` with the `m` return values `rvals` on top. Assumes `retaddr` is a
valid `JUMPDEST` (the landing pad the caller scaffold placed). -/
theorem calleeEpilogueSteps (code : ByteArray) (pre post : List UInt8)
    (n m : Nat) (hm : m ≤ 16) (paramvals rvals σ : List UInt256) (retaddr : UInt256)
    (yst : EvmState) (s : State)
    (hplen : paramvals.length = n) (hrlen : rvals.length = m)
    (hcode : code = mkCode (pre ++ assembleBytes (List.replicate n (.op .POP)
        ++ retSwaps m ++ [.op .JUMP]) ++ post))
    (hf : FrameOK code s) (hmatch : StateMatch yst s)
    (hpc : s.pc = UInt256.ofNat pre.length)
    (hstk : s.stack = paramvals ++ rvals ++ retaddr :: σ)
    (hvalid : Decode.isValidJumpDest code retaddr.toNat = true)
    (hgas : 40000 * n + (40000 * m + 40000) ≤ s.gasAvailable) :
    ∃ s', Steps s s' ∧ FrameOK code s' ∧ StateMatch yst s'
      ∧ s'.pc = retaddr ∧ s'.stack = rvals ++ σ
      ∧ s.gasAvailable - (40000 * n + (40000 * m + 40000)) ≤ s'.gasAvailable := by
  have hAB : assembleBytes (List.replicate n (.op .POP) ++ retSwaps m ++ [.op .JUMP])
      = assembleBytes (List.replicate n (.op .POP)) ++ assembleBytes (retSwaps m)
        ++ (Instr.op .JUMP).bytes := by
    simp only [assembleBytes_append, assembleBytes_cons, assembleBytes_nil, List.append_nil]
  -- POP×n : drop the parameters
  have hcode1 : code = mkCode (pre ++ assembleBytes (List.replicate n (.op .POP))
      ++ (assembleBytes (retSwaps m) ++ (Instr.op .JUMP).bytes ++ post)) := by
    rw [hcode, hAB]; simp [List.append_assoc]
  obtain ⟨s1, st1, hf1, hm1, hpc1, hstk1, hg1⟩ :=
    popsSteps n code pre (assembleBytes (retSwaps m) ++ (Instr.op .JUMP).bytes ++ post)
      paramvals (rvals ++ retaddr :: σ) yst s hplen hcode1 hf hmatch hpc
      (by rw [hstk]; simp [List.append_assoc]) (gstrip hgas)
  -- SWAP1..SWAPm : rotate retaddr to the top
  have hcode2 : code = mkCode ((pre ++ assembleBytes (List.replicate n (.op .POP)))
      ++ assembleBytes (retSwaps m) ++ ((Instr.op .JUMP).bytes ++ post)) := by
    rw [hcode, hAB]; simp [List.append_assoc]
  have hpc1' : s1.pc = UInt256.ofNat (pre ++ assembleBytes (List.replicate n (.op .POP))).length := by
    rw [hpc1, List.length_append, length_assembleBytes_replicate_pop]
  obtain ⟨s2, st2, hf2, hm2, hpc2, hstk2, hg2⟩ :=
    retSwapsSteps m hm code (pre ++ assembleBytes (List.replicate n (.op .POP)))
      ((Instr.op .JUMP).bytes ++ post) rvals retaddr σ yst s1 hrlen hcode2 hf1 hm1 hpc1'
      hstk1 (gstrip (genough hgas hg1))
  -- JUMP : return to the caller's landing pad
  have hcode3 : code = mkCode ((pre ++ assembleBytes (List.replicate n (.op .POP))
      ++ assembleBytes (retSwaps m)) ++ (Instr.op .JUMP).bytes ++ post) := by
    rw [hcode, hAB]; simp [List.append_assoc]
  have hpc2' : s2.pc = UInt256.ofNat (pre ++ assembleBytes (List.replicate n (.op .POP))
      ++ assembleBytes (retSwaps m)).length := by
    rw [hpc2]; congr 1
    simp only [List.length_append, length_assembleBytes_retSwaps]
  obtain ⟨s3, jstep, hf3, hm3, hpc3, hstk3, hg3⟩ :=
    jumpStep hcode3 hf2 hm2 hpc2' hstk2 hvalid (genough (genough hgas hg1) hg2)
  exact ⟨s3, (st1.append st2).snoc jstep, hf3, hm3, hpc3, hstk3, gsub2 hg1 (gsub2 hg2 hg3)⟩

/-! ## Phase 1.3 — layout arithmetic (position/entry length-independence) -/

/-- `m` stacked identical pushes assemble to `33·m` bytes. -/
theorem length_assembleBytes_replicate_push (m : Nat) (v : EvmSemantics.UInt256) :
    (assembleBytes (List.replicate m (Instr.push v))).length = 33 * m := by
  induction m with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, assembleBytes_cons, List.length_append, Instr.length_bytes_push, ih]
    omega

/-- A call scaffold's byte length is `scaffoldLen`, independent of the pushed
return address and entry point. -/
theorem length_assembleBytes_callScaffold (retaddr entry m : Nat) (argCode : List Instr) :
    (assembleBytes (callScaffold retaddr entry m argCode)).length
      = scaffoldLen m (assembleBytes argCode).length := by
  unfold callScaffold scaffoldLen
  simp only [assembleBytes_cons, assembleBytes_append, List.length_append,
    Instr.length_bytes_push, length_assembleBytes_replicate_push, Instr.length_bytes_op,
    assembleBytes_nil, List.length_nil]

/-- Two function tables are *signature-equivalent* when every name resolves to
infos of the same param/return arity. Compiled **lengths** depend on the table
only through these arities (entry positions flow solely into fixed-width
`PUSH32`s), so signature-equivalent tables yield equal-length code. -/
def FnTable.SigEq (ft₁ ft₂ : FnTable) : Prop :=
  ∀ n, (ft₁.get? n).map (fun i => (i.params.length, i.rets.length))
     = (ft₂.get? n).map (fun i => (i.params.length, i.rets.length))

/-- **Expression codegen length is position- and entry-independent.** Under
signature-equivalent tables and *any* two byte positions, a successful
`compileExprF` on the left yields a successful one on the right of exactly the
same assembled length. -/
theorem compileExprF_lenSig (ft₁ ft₂ : FnTable) (Γ : List Ident)
    (h : FnTable.SigEq ft₁ ft₂) (pc off : Nat) (e : Expr Op) (pc' : Nat)
    (is₁ : List Instr) (he : compileExprF ft₁ pc Γ off e = some is₁) :
    ∃ is₂, compileExprF ft₂ pc' Γ off e = some is₂ ∧
           (assembleBytes is₂).length = (assembleBytes is₁).length := by
  refine compileExprF.induct
    (motive_1 := fun pc off e => ∀ (pc' : Nat) (is₁ : List Instr),
      compileExprF ft₁ pc Γ off e = some is₁ →
      ∃ is₂, compileExprF ft₂ pc' Γ off e = some is₂ ∧
             (assembleBytes is₂).length = (assembleBytes is₁).length)
    (motive_2 := fun pc off args => ∀ (pc' : Nat) (is₁ : List Instr),
      compileArgsF ft₁ pc Γ off args = some is₁ →
      ∃ is₂, compileArgsF ft₂ pc' Γ off args = some is₂ ∧
             (assembleBytes is₂).length = (assembleBytes is₁).length)
    ?lit ?var ?builtin ?call ?argsNil ?argsCons pc off e pc' is₁ he
  case lit =>
      intro pc off l pc' is₁ he
      exact ⟨is₁, by simpa only [compileExprF] using he, rfl⟩
  case var =>
      intro pc off x pc' is₁ he
      refine ⟨is₁, ?_, rfl⟩
      simp only [compileExprF] at he ⊢; exact he
  case builtin =>
      intro pc off op args ihargs pc' is₁ he
      simp only [compileExprF, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at he
      obtain ⟨argCode₁, hargs₁, o, ho, his₁⟩ := he
      obtain ⟨argCode₂, hac₂, hlen⟩ := ihargs pc' argCode₁ hargs₁
      refine ⟨argCode₂ ++ [.op o], ?_, ?_⟩
      · simp only [compileExprF, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def]
        exact ⟨argCode₂, hac₂, o, ho, rfl⟩
      · subst his₁
        simp only [assembleBytes_append, List.length_append, hlen]
  case call =>
      intro pc off f args ihargs pc' is₁ he
      simp only [compileExprF, Option.bind_eq_bind, Option.bind_eq_some_iff] at he
      obtain ⟨info₁, hg1, he⟩ := he
      split at he
      · rename_i hcond
        simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at he
        obtain ⟨argCode₁, hargs₁, his₁⟩ := he
        obtain ⟨argCode₂, hac₂, hlen⟩ := ihargs (pc' + 33 + 33 * 1) argCode₁ hargs₁
        have hf := h f
        rw [hg1] at hf
        cases hg2 : ft₂.get? f with
        | none => rw [hg2] at hf; simp at hf
        | some info₂ =>
            rw [hg2] at hf
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hf
            refine ⟨callScaffold (pc' + 33 + 33 * 1 + (assembleBytes argCode₂).length + 33 + 1)
              info₂.entry 1 argCode₂, ?_, ?_⟩
            · simp only [compileExprF, Option.bind_eq_bind, Option.bind_eq_some_iff]
              refine ⟨info₂, hg2, ?_⟩
              rw [if_pos (by rw [← hf.1, ← hf.2]; exact hcond), Option.bind_eq_some_iff]
              exact ⟨argCode₂, hac₂, rfl⟩
            · subst his₁
              rw [length_assembleBytes_callScaffold, length_assembleBytes_callScaffold, hlen]
      · exact absurd he (by simp)
  case argsNil =>
      intro pc off pc' is₁ he
      exact ⟨is₁, by simpa only [compileArgsF] using he, rfl⟩
  case argsCons =>
      intro pc off e rest ihrest ihe pc' is₁ he
      simp only [compileArgsF, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at he
      obtain ⟨restCode₁, hrest₁, eCode₁, he₁, his₁⟩ := he
      obtain ⟨restCode₂, hrc₂, hrlen⟩ := ihrest pc' restCode₁ hrest₁
      obtain ⟨eCode₂, hec₂, helen⟩ :=
        ihe restCode₁ (pc' + (assembleBytes restCode₂).length) eCode₁ he₁
      refine ⟨restCode₂ ++ eCode₂, ?_, ?_⟩
      · simp only [compileArgsF, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def]
        exact ⟨restCode₂, hrc₂, eCode₂, hec₂, rfl⟩
      · subst his₁
        simp only [assembleBytes_append, List.length_append, hrlen, helen]

/-- **Argument-list codegen length is position- and entry-independent** (list
induction over `compileExprF_lenSig`). -/
theorem compileArgsF_lenSig (ft₁ ft₂ : FnTable) (Γ : List Ident)
    (h : FnTable.SigEq ft₁ ft₂) (pc off : Nat) (args : List (Expr Op)) (pc' : Nat)
    (is₁ : List Instr) :
    compileArgsF ft₁ pc Γ off args = some is₁ →
    ∃ is₂, compileArgsF ft₂ pc' Γ off args = some is₂ ∧
           (assembleBytes is₂).length = (assembleBytes is₁).length := by
  induction args generalizing pc off pc' is₁ with
  | nil => intro he; exact ⟨is₁, by simpa only [compileArgsF] using he, rfl⟩
  | cons e rest ihrest =>
      intro he
      simp only [compileArgsF, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at he
      obtain ⟨restCode₁, hrest₁, eCode₁, he₁, his₁⟩ := he
      obtain ⟨restCode₂, hrc₂, hrlen⟩ := ihrest pc off pc' restCode₁ hrest₁
      obtain ⟨eCode₂, hec₂, helen⟩ :=
        compileExprF_lenSig ft₁ ft₂ Γ h _ _ e (pc' + (assembleBytes restCode₂).length) eCode₁ he₁
      refine ⟨restCode₂ ++ eCode₂, ?_, ?_⟩
      · simp only [compileArgsF, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def]
        exact ⟨restCode₂, hrc₂, eCode₂, hec₂, rfl⟩
      · subst his₁
        simp only [assembleBytes_append, List.length_append, hrlen, helen]

/-- **Call-statement codegen length is position- and entry-independent**; the
return-arity `m` is also preserved (it is read from the callee's signature). -/
theorem compileCallStmt_lenSig (ft₁ ft₂ : FnTable) (Γ : List Ident)
    (h : FnTable.SigEq ft₁ ft₂) (pc off : Nat) (f : Ident) (args : List (Expr Op))
    (pc' : Nat) (is₁ : List Instr) (m₁ : Nat)
    (he : compileCallStmt ft₁ pc Γ off f args = some (is₁, m₁)) :
    ∃ is₂, compileCallStmt ft₂ pc' Γ off f args = some (is₂, m₁) ∧
           (assembleBytes is₂).length = (assembleBytes is₁).length := by
  simp only [compileCallStmt, Option.bind_eq_bind, Option.bind_eq_some_iff] at he
  obtain ⟨info₁, hg1, he⟩ := he
  split at he
  · rename_i hcond
    simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨argCode₁, hargs₁, hcs, hm⟩ := he
    have hf := h f
    rw [hg1] at hf
    cases hg2 : ft₂.get? f with
    | none => rw [hg2] at hf; simp at hf
    | some info₂ =>
        rw [hg2] at hf
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hf
        obtain ⟨argCode₂, hac₂, hlen⟩ :=
          compileArgsF_lenSig ft₁ ft₂ Γ h (pc + 33 + 33 * info₂.rets.length)
            (off + 1 + info₂.rets.length) args
            (pc' + 33 + 33 * info₂.rets.length) argCode₁ (by rw [← hf.2]; exact hargs₁)
        refine ⟨callScaffold (pc' + 33 + 33 * info₂.rets.length +
          (assembleBytes argCode₂).length + 33 + 1) info₂.entry info₂.rets.length argCode₂, ?_, ?_⟩
        · simp only [compileCallStmt, Option.bind_eq_bind, Option.bind_eq_some_iff]
          refine ⟨info₂, hg2, ?_⟩
          rw [if_pos (by rw [← hf.1, ← hf.2]; exact hcond), Option.bind_eq_some_iff]
          refine ⟨argCode₂, hac₂, ?_⟩
          rw [Option.pure_def, Option.some.injEq, Prod.mk.injEq]
          exact ⟨rfl, by rw [← hf.2]; exact hm⟩
        · subst hcs
          rw [length_assembleBytes_callScaffold, length_assembleBytes_callScaffold, hlen, hf.2]
  · exact absurd he (by simp)

set_option maxHeartbeats 1000000 in

/-- **Statement/statement-sequence codegen length is position- and
entry-independent**, and the resulting layout `Γ'` is identical. -/
theorem compileStmtF_lenSig (ft₁ ft₂ : FnTable) (h : FnTable.SigEq ft₁ ft₂)
    (pc : Nat) (Γ : List Ident) (s : Stmt Op) (pc' : Nat) (is₁ : List Instr)
    (Γ' : List Ident) (he : compileStmtF ft₁ pc Γ s = some (is₁, Γ')) :
    ∃ is₂, compileStmtF ft₂ pc' Γ s = some (is₂, Γ') ∧
           (assembleBytes is₂).length = (assembleBytes is₁).length := by
  refine compileStmtF.induct
    (motive_1 := fun pc Γ s => ∀ (pc' : Nat) (is₁ : List Instr) (Γ' : List Ident),
      compileStmtF ft₁ pc Γ s = some (is₁, Γ') →
      ∃ is₂, compileStmtF ft₂ pc' Γ s = some (is₂, Γ') ∧
             (assembleBytes is₂).length = (assembleBytes is₁).length)
    (motive_2 := fun pc Γ ss => ∀ (pc' : Nat) (is₁ : List Instr) (Γ' : List Ident),
      compileStmtsF ft₁ pc Γ ss = some (is₁, Γ') →
      ∃ is₂, compileStmtsF ft₂ pc' Γ ss = some (is₂, Γ') ∧
             (assembleBytes is₂).length = (assembleBytes is₁).length)
    ?funDef ?exprCall ?exprOther ?letNone ?letCall ?letSingle ?letOther
    ?assignSingle ?assignOther ?block ?cond ?catchAll ?stmtsNil ?stmtsCons
    pc Γ s pc' is₁ Γ' he
  case funDef =>
      intro pc Γ name params rets body pc' is₁ Γ' he
      simp only [compileStmtF, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨hcode, hΓ⟩ := he
      subst hcode; subst hΓ
      exact ⟨[], by simp only [compileStmtF], rfl⟩
  case exprCall =>
      intro pc Γ f args pc' is₁ Γ' he
      simp only [compileStmtF, Option.bind_eq_bind, Option.bind_eq_some_iff] at he
      obtain ⟨⟨code, m⟩, hcall, he⟩ := he
      split at he
      · rename_i hm0
        simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at he
        obtain ⟨hcode, hΓ⟩ := he
        subst hcode; subst hΓ
        obtain ⟨code₂, hcall₂, hlen⟩ :=
          compileCallStmt_lenSig ft₁ ft₂ Γ h pc 0 f args pc' code m hcall
        refine ⟨code₂, ?_, hlen⟩
        simp only [compileStmtF, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def]
        refine ⟨(code₂, m), hcall₂, ?_⟩
        show (if m = 0 then some (code₂, Γ) else none) = some (code₂, Γ)
        rw [if_pos hm0]
      · exact absurd he (by simp)
  case exprOther =>
      intro pc Γ e hne pc' is₁ Γ' he
      cases e
      case call f args => exact absurd rfl (hne f args)
      all_goals
        simp only [compileStmtF, Option.bind_eq_bind, Option.bind_eq_some_iff] at he
        obtain ⟨is, his, heq⟩ := he
        simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at heq
        obtain ⟨hcode, hΓ⟩ := heq
        subst hcode; subst hΓ
        obtain ⟨is₂, hce₂, hlen⟩ := compileExprF_lenSig ft₁ ft₂ Γ h pc 0 _ pc' is his
        refine ⟨is₂, ?_, hlen⟩
        simp only [compileStmtF, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def]
        exact ⟨is₂, hce₂, rfl⟩
  case letNone =>
      intro pc Γ xs pc' is₁ Γ' he
      simp only [compileStmtF, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨hcode, hΓ⟩ := he
      subst hcode; subst hΓ
      exact ⟨List.replicate xs.length (.push (conv 0)),
        by simp only [compileStmtF, Option.pure_def], rfl⟩
  case letCall =>
      intro pc Γ xs f args pc' is₁ Γ' he
      simp only [compileStmtF, Option.bind_eq_bind, Option.bind_eq_some_iff] at he
      obtain ⟨⟨code, m⟩, hcall, he⟩ := he
      split at he
      · rename_i hmx
        simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at he
        obtain ⟨hcode, hΓ⟩ := he
        subst hcode; subst hΓ
        obtain ⟨code₂, hcall₂, hlen⟩ :=
          compileCallStmt_lenSig ft₁ ft₂ Γ h pc 0 f args pc' code m hcall
        refine ⟨code₂, ?_, hlen⟩
        simp only [compileStmtF, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def]
        refine ⟨(code₂, m), hcall₂, ?_⟩
        show (if m = xs.length then some (code₂, xs ++ Γ) else none) = some (code₂, xs ++ Γ)
        rw [if_pos hmx]
      · exact absurd he (by simp)
  case letSingle =>
      intro pc Γ x e hne pc' is₁ Γ' he
      cases e
      case call f args => exact absurd rfl (hne f args)
      all_goals
        simp only [compileStmtF, Option.bind_eq_bind, Option.bind_eq_some_iff] at he
        obtain ⟨is, his, heq⟩ := he
        simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at heq
        obtain ⟨hcode, hΓ⟩ := heq
        subst hcode; subst hΓ
        obtain ⟨is₂, hce₂, hlen⟩ := compileExprF_lenSig ft₁ ft₂ Γ h pc 0 _ pc' is his
        refine ⟨is₂, ?_, hlen⟩
        simp only [compileStmtF, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def]
        exact ⟨is₂, hce₂, rfl⟩
  case letOther =>
      intro pc Γ vars val hnecall hnesingle pc' is₁ Γ' he
      cases val
      case call f args => exact absurd rfl (hnecall f args)
      all_goals
        cases vars with
        | nil => exact absurd he (by simp [compileStmtF])
        | cons x xs =>
            cases xs with
            | nil => exact absurd rfl (hnesingle x)
            | cons y ys => exact absurd he (by simp [compileStmtF])
  case assignSingle =>
      intro pc Γ x e pc' is₁ Γ' he
      simp only [compileStmtF, Option.bind_eq_bind, Option.bind_eq_some_iff] at he
      obtain ⟨is, his, idx, hidx, he⟩ := he
      split at he
      · rename_i hlt
        simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at he
        obtain ⟨hcode, hΓ⟩ := he
        subst hΓ
        obtain ⟨is₂, hce₂, hlen⟩ := compileExprF_lenSig ft₁ ft₂ Γ h pc 0 e pc' is his
        refine ⟨is₂ ++ [.op (.Swap ⟨idx, hlt⟩), .op .POP], ?_, ?_⟩
        · simp only [compileStmtF, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def]
          refine ⟨is₂, hce₂, idx, hidx, ?_⟩
          rw [dif_pos hlt]
        · subst hcode
          simp only [assembleBytes_append, List.length_append, hlen]
      · exact absurd he (by simp)
  case assignOther =>
      intro pc Γ vars val hnesingle pc' is₁ Γ' he
      cases vars with
      | nil => exact absurd he (by simp [compileStmtF])
      | cons x xs =>
          cases xs with
          | nil => exact absurd rfl (hnesingle x)
          | cons y ys => exact absurd he (by simp [compileStmtF])
  case block =>
      intro pc Γ body hbody pc' is₁ Γ' he
      simp only [compileStmtF, Option.bind_eq_bind, Option.bind_eq_some_iff] at he
      obtain ⟨⟨isb, Γb⟩, hbc, he⟩ := he
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨hcode, hΓ⟩ := he
      subst hΓ
      obtain ⟨is₂b, hbc₂, hlen⟩ := hbody (pc' + 0) isb Γb hbc
      refine ⟨is₂b ++ List.replicate (Γb.length - Γ.length) (.op .POP), ?_, ?_⟩
      · simp only [compileStmtF, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def]
        exact ⟨(is₂b, Γb), hbc₂, rfl⟩
      · subst hcode
        simp only [assembleBytes_append, List.length_append, hlen]
  case cond =>
      intro pc Γ c body hbody pc' is₁ Γ' he
      simp only [compileStmtF, Option.bind_eq_bind, Option.bind_eq_some_iff] at he
      obtain ⟨cCode, hc, ⟨bodyCode, Γb⟩, hbc, he⟩ := he
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨hcode, hΓ⟩ := he
      subst hΓ
      obtain ⟨cCode₂, hc₂, hclen⟩ := compileExprF_lenSig ft₁ ft₂ Γ h pc 0 c pc' cCode hc
      obtain ⟨bodyCode₂, hbc₂, hblen⟩ :=
        hbody cCode (pc' + (assembleBytes cCode₂).length + 35) bodyCode Γb hbc
      refine ⟨cCode₂ ++ [.op .ISZERO, .push (EvmSemantics.UInt256.ofNat
          (pc' + (assembleBytes cCode₂).length + 35 + (assembleBytes bodyCode₂).length
            + (Γb.length - Γ.length))), .op .JUMPI] ++ bodyCode₂
          ++ List.replicate (Γb.length - Γ.length) (.op .POP) ++ [.op .JUMPDEST], ?_, ?_⟩
      · simp only [compileStmtF, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def]
        exact ⟨cCode₂, hc₂, (bodyCode₂, Γb), hbc₂, rfl⟩
      · subst hcode
        simp only [assembleBytes_append, assembleBytes_cons, List.length_append,
          List.length_cons, List.length_nil, Instr.length_bytes_push, Instr.length_bytes_op,
          length_assembleBytes_replicate_push, hclen, hblen]
  case catchAll =>
      intro t pc Γ hg1 _ hg3 hg4 _ _ hg7 _ hg9 hg10 hg11 pc' is₁ Γ' he
      cases t with
      | funDef n p r b => exact absurd rfl (hg1 n p r b)
      | exprStmt e => exact absurd rfl (hg3 e)
      | letDecl xs v =>
          cases v with
          | none => exact absurd rfl (hg4 xs)
          | some val => exact absurd rfl (hg7 xs val)
      | assign vars val => exact absurd rfl (hg9 vars val)
      | block body => exact absurd rfl (hg10 body)
      | cond c body => exact absurd rfl (hg11 c body)
      | switch c cs d => exact absurd he (by simp [compileStmtF])
      | forLoop i c p b => exact absurd he (by simp [compileStmtF])
      | «break» => exact absurd he (by simp [compileStmtF])
      | «continue» => exact absurd he (by simp [compileStmtF])
      | leave => exact absurd he (by simp [compileStmtF])
  case stmtsNil =>
      intro pc Γ pc' is₁ Γ' he
      simp only [compileStmtsF, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨hcode, hΓ⟩ := he
      subst hcode; subst hΓ
      exact ⟨[], by simp only [compileStmtsF], rfl⟩
  case stmtsCons =>
      intro pc Γ s rest hs hrest pc' is₁ Γ' he
      simp only [compileStmtsF, Option.bind_eq_bind, Option.bind_eq_some_iff] at he
      obtain ⟨⟨is1, Γ1⟩, hs1, ⟨is2, Γ2⟩, hs2, he⟩ := he
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨hcode, hΓ⟩ := he
      subst hΓ
      obtain ⟨is1', hs1', hlen1⟩ := hs pc' is1 Γ1 hs1
      obtain ⟨is2', hs2', hlen2⟩ :=
        hrest is1 Γ1 (pc' + (assembleBytes is1').length) is2 Γ2 hs2
      refine ⟨is1' ++ is2', ?_, ?_⟩
      · simp only [compileStmtsF, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def]
        exact ⟨(is1', Γ1), hs1', (is2', Γ2), hs2', rfl⟩
      · subst hcode
        simp only [assembleBytes_append, List.length_append, hlen1, hlen2]

/-- **Statement-sequence codegen length is position- and entry-independent**
(list induction over `compileStmtF_lenSig`). -/
theorem compileStmtsF_lenSig (ft₁ ft₂ : FnTable) (h : FnTable.SigEq ft₁ ft₂)
    (pc : Nat) (Γ : List Ident) (ss : List (Stmt Op)) (pc' : Nat) (is₁ : List Instr)
    (Γ' : List Ident) :
    compileStmtsF ft₁ pc Γ ss = some (is₁, Γ') →
    ∃ is₂, compileStmtsF ft₂ pc' Γ ss = some (is₂, Γ') ∧
           (assembleBytes is₂).length = (assembleBytes is₁).length := by
  induction ss generalizing pc Γ pc' is₁ Γ' with
  | nil =>
      intro he
      simp only [compileStmtsF, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨hcode, hΓ⟩ := he
      subst hcode; subst hΓ
      exact ⟨[], by simp only [compileStmtsF], rfl⟩
  | cons s rest ih =>
      intro he
      simp only [compileStmtsF, Option.bind_eq_bind, Option.bind_eq_some_iff] at he
      obtain ⟨⟨is1, Γ1⟩, hs1, ⟨is2, Γ2⟩, hs2, he⟩ := he
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨hcode, hΓ⟩ := he
      subst hΓ
      obtain ⟨is1', hs1', hlen1⟩ := compileStmtF_lenSig ft₁ ft₂ h pc Γ s pc' is1 Γ1 hs1
      obtain ⟨is2', hs2', hlen2⟩ :=
        ih (pc + (assembleBytes is1).length) Γ1 (pc' + (assembleBytes is1').length) is2 Γ2 hs2
      refine ⟨is1' ++ is2', ?_, ?_⟩
      · simp only [compileStmtsF, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def]
        exact ⟨(is1', Γ1), hs1', (is2', Γ2), hs2', rfl⟩
      · subst hcode
        simp only [assembleBytes_append, List.length_append, hlen1, hlen2]

/-- **A compiled function body has a position- and entry-independent length.**
The entry byte-position `e` flows only into the body's PUSH32s, so `compileFn`
at two entries yields equal-length code (with the same success/failure). -/
theorem compileFn_lenSig (ft₁ ft₂ : FnTable) (h : FnTable.SigEq ft₁ ft₂)
    (e₁ e₂ : Nat) (ps rs : List Ident) (b : Block Op) (is₁ : List Instr)
    (he : compileFn ft₁ e₁ ps rs b = some is₁) :
    ∃ is₂, compileFn ft₂ e₂ ps rs b = some is₂ ∧
           (assembleBytes is₂).length = (assembleBytes is₁).length := by
  simp only [compileFn, Option.bind_eq_bind, Option.bind_eq_some_iff] at he
  obtain ⟨⟨bodyCode, Γb⟩, hbc, he⟩ := he
  split at he
  · rename_i hrs
    simp only [Option.pure_def, Option.some.injEq] at he
    obtain ⟨bodyCode₂, hbc₂, hlen⟩ :=
      compileStmtF_lenSig ft₁ ft₂ h (e₁ + 1) (ps ++ rs) (.block b) (e₂ + 1) bodyCode Γb hbc
    refine ⟨[.op .JUMPDEST] ++ bodyCode₂ ++ List.replicate ps.length (.op .POP)
      ++ retSwaps rs.length ++ [.op .JUMP], ?_, ?_⟩
    · simp only [compileFn, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def]
      exact ⟨(bodyCode₂, Γb), hbc₂, by rw [if_pos hrs]⟩
    · subst he
      simp only [assembleBytes_append, List.length_append, hlen]
  · exact absurd he (by simp)


end YulEvmCompiler
