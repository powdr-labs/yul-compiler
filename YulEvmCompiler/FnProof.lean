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
      simp [assembleBytes_append, List.append_assoc]
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

end YulEvmCompiler
