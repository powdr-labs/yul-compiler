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

end YulEvmCompiler
