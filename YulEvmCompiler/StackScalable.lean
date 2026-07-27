import YulEvmCompiler.StackBound

set_option warningAsError false  -- WIP
/-!
# YulEvmCompiler.StackScalable — scalable (frame-relative) stack-overflow analysis  [WIP]

Frame-relative, context-insensitive layout analysis. Key ingredients that make it both linear and
sound for multiply-called functions:

* `FSlot = word | ret` — a **target-less** return-address slot. A callee's frame holds the caller's
  return address, whose *target* is context-dependent; `ret` matches any `.code l` without pinning
  it, so a callee's frame layout is context-insensitive (single value per position ⇒ linear).
  The actual return target is read from the runtime value at `dynJump`.
* `Cert.rl` — the **return layout** of the function containing each position, propagated
  intra-function (context-insensitive). `GoodStack.call` carries `rl c = some Sret`; at `dynJump`,
  `frameStep` ties `rl` to the exit frame's tail, giving the return-count consistency for free.
* a **resume witness** in `GoodStack.call`, and `fbMax ≥ 1` at `dynJump` (rules out `root`+`dynJump`).
-/

namespace YulEvmCompiler

open EvmSemantics EvmSemantics.EVM
open YulSemantics.EVM (U256 EvmState Op)

/-! ### Frame slots and the runtime↔layout match -/

/-- A frame-relative slot: a plain word, or a (target-less) return address. -/
inductive FSlot
  | word
  | ret
  deriving DecidableEq

abbrev FLayout := List FSlot

/-- Runtime stack ↔ frame layout: words match `word`; *any* return address matches `ret`. -/
inductive FMatch : List AVal → FLayout → Prop
  | nil : FMatch [] []
  | word {v : U256} {σ : List AVal} {S : FLayout} : FMatch σ S → FMatch (.word v :: σ) (.word :: S)
  | ret {l : Label} {σ : List AVal} {S : FLayout} : FMatch σ S → FMatch (.code l :: σ) (.ret :: S)

theorem FMatch.length_eq {σ : List AVal} {S : FLayout} (h : FMatch σ S) : σ.length = S.length := by
  induction h with
  | nil => rfl
  | word _ ih => simp [ih]
  | ret _ ih => simp [ih]

theorem FMatch.append {σ₁ σ₂ : List AVal} {S₁ S₂ : FLayout}
    (h₁ : FMatch σ₁ S₁) (h₂ : FMatch σ₂ S₂) : FMatch (σ₁ ++ σ₂) (S₁ ++ S₂) := by
  induction h₁ with
  | nil => exact h₂
  | word _ ih => exact .word ih
  | ret _ ih => exact .ret ih

theorem FMatch.append_inv {σ₁ σ₂ : List AVal} {S : FLayout} (h : FMatch (σ₁ ++ σ₂) S) :
    ∃ S₁ S₂, S = S₁ ++ S₂ ∧ FMatch σ₁ S₁ ∧ FMatch σ₂ S₂ := by
  induction σ₁ generalizing S with
  | nil => exact ⟨[], S, rfl, .nil, h⟩
  | cons v σ₁ ih =>
      rw [List.cons_append] at h
      cases h with
      | word htl => obtain ⟨S₁, S₂, rfl, h1, h2⟩ := ih htl; exact ⟨.word :: S₁, S₂, rfl, .word h1, h2⟩
      | ret htl => obtain ⟨S₁, S₂, rfl, h1, h2⟩ := ih htl; exact ⟨.ret :: S₁, S₂, rfl, .ret h1, h2⟩

/-- Head inversion exposing the runtime cons shape. -/
theorem FMatch.cons_inv' {σ : List AVal} {s : FSlot} {S : FLayout} (h : FMatch σ (s :: S)) :
    ∃ a σ', σ = a :: σ' ∧ FMatch [a] [s] ∧ FMatch σ' S := by
  cases h with
  | word htl => exact ⟨_, _, rfl, .word .nil, htl⟩
  | ret htl => exact ⟨_, _, rfl, .ret .nil, htl⟩

/-- Head composition. -/
theorem FMatch.consMatch {a : AVal} {σ : List AVal} {s : FSlot} {S : FLayout}
    (h1 : FMatch [a] [s]) (h2 : FMatch σ S) : FMatch (a :: σ) (s :: S) := by
  cases h1 with
  | word _ => exact .word h2
  | ret _ => exact .ret h2

/-- Split a `FMatch` by a **layout** prefix. -/
theorem FMatch.append_inv_layout {σ : List AVal} {S1 S2 : FLayout} (h : FMatch σ (S1 ++ S2)) :
    ∃ σ1 σ2, σ = σ1 ++ σ2 ∧ FMatch σ1 S1 ∧ FMatch σ2 S2 := by
  induction S1 generalizing σ with
  | nil => exact ⟨[], σ, rfl, .nil, h⟩
  | cons s S1 ih =>
      rw [List.cons_append] at h
      obtain ⟨a, σ', rfl, hsm, htl⟩ := h.cons_inv'
      obtain ⟨σ1, σ2, rfl, h1, h2⟩ := ih htl
      exact ⟨a :: σ1, σ2, rfl, hsm.consMatch h1, h2⟩

/-- `words vs` matches the all-`word` layout. -/
theorem FMatch.replicate_word (vs : List U256) : FMatch (words vs) (List.replicate vs.length .word) := by
  induction vs with
  | nil => exact .nil
  | cons v vs ih => rw [words_cons]; simp only [List.length_cons, List.replicate_succ]; exact .word ih

theorem FMatch.eq_replicate {vs : List U256} {S : FLayout} (h : FMatch (words vs) S) :
    S = List.replicate vs.length .word := by
  induction vs generalizing S with
  | nil => cases h; rfl
  | cons v vs ih => rw [words_cons] at h; cases h with
      | word htl => rw [List.length_cons, List.replicate_succ, ih htl]

/-- The cell at depth `i` matches the slot at depth `i`. -/
theorem FMatch.at_idx {σ : List AVal} {S : FLayout} (h : FMatch σ S) :
    ∀ {i : Nat} {x : AVal} {s : FSlot}, σ[i]? = some x → S[i]? = some s → FMatch [x] [s] := by
  induction h with
  | nil => intro i x s hx _; simp at hx
  | @word w σ' S' _ ih => intro i x s hx hs; cases i with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hs; subst hx; subst hs; exact .word .nil
      | succ k => simp only [List.getElem?_cons_succ] at hx hs; exact ih hx hs
  | @ret l σ' S' _ ih => intro i x s hx hs; cases i with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hs; subst hx; subst hs; exact .ret .nil
      | succ k => simp only [List.getElem?_cons_succ] at hx hs; exact ih hx hs

/-- An all-`word` layout matches an all-word runtime stack. -/
theorem FMatch.allWord {σ : List AVal} {S : FLayout} (h : FMatch σ S) (hw : ∀ s ∈ S, s = FSlot.word) :
    ∀ x ∈ σ, ∃ v, x = .word v := by
  induction h with
  | nil => intro x hx; simp at hx
  | @word w σ' S' _ ih =>
      intro x hx; cases List.mem_cons.mp hx with
      | inl he => exact ⟨w, he⟩
      | inr he => exact ih (fun s hs => hw s (List.mem_cons_of_mem _ hs)) x he
  | @ret l σ' S' _ _ =>
      exact absurd (hw .ret (by simp)) (by simp)

/-! ### The certificate -/

/-- Frame-relative certificate: per position, the frame layout `fl`, max frame base `fbMax`, and the
**return layout** `rl` of the function containing it (propagated intra-function). -/
structure Cert where
  fl : List Asm → Option FLayout
  fbMax : List Asm → Option Nat
  rl : List Asm → Option FLayout

def Cert.Bounded (C : Cert) : Prop :=
  ∀ c S F, C.fl c = some S → C.fbMax c = some F → S.length + F ≤ 1023

/-- Per-instruction step constraint, given current `fl = some S`, `fbMax = some F`, `rl = some R`. -/
def frameStep (prog : List Asm) (C : Cert) : Asm → List Asm → FLayout → Nat → FLayout → Prop
  | .push _,      c, S, F, R => C.fl c = some (.word :: S) ∧ C.fbMax c = some F ∧ C.rl c = some R
  | .dup n,       c, S, F, R => ∃ sl, S[n.val]? = some sl ∧ C.fl c = some (sl :: S)
      ∧ C.fbMax c = some F ∧ C.rl c = some R
  | .pushLabel _, c, S, F, R => C.fl c = some (.ret :: S) ∧ C.fbMax c = some F ∧ C.rl c = some R
  | .pop,         c, S, F, R => ∃ S', S = .word :: S' ∧ C.fl c = some S' ∧ C.fbMax c = some F
      ∧ C.rl c = some R
  | .swap n,      c, S, F, R => ∃ sx mid sy rst, S = sx :: (mid ++ sy :: rst) ∧ mid.length = n.val
      ∧ C.fl c = some (sy :: (mid ++ sx :: rst)) ∧ C.fbMax c = some F ∧ C.rl c = some R
  | .label _,     c, S, F, R => C.fl c = some S ∧ C.fbMax c = some F ∧ C.rl c = some R
  | .op yop,      c, S, F, R => ∃ o, opTable yop = some o ∧ Operation.popArity o ≤ S.length ∧
      C.fl c = some (List.replicate (Operation.pushArity o) FSlot.word ++ S.drop (Operation.popArity o))
      ∧ C.fbMax c = some F ∧ C.rl c = some R
  | .jump l,      _, S, F, R =>
      (∃ t, findLabel l prog = some t ∧ C.fl t = some S ∧ C.fbMax t = some F ∧ C.rl t = some R)
      ∨ True  -- WIP: the call case
  | .jumpi l,     c, S, F, R => ∃ S', S = .word :: S' ∧
      (∃ t, findLabel l prog = some t ∧ C.fl t = some S' ∧ C.fbMax t = some F ∧ C.rl t = some R) ∧
      C.fl c = some S' ∧ C.fbMax c = some F ∧ C.rl c = some R
  | .dynJump,     _, S, F, R => 1 ≤ F ∧ ∃ S', S = .ret :: S' ∧ R = S' ∧ (∀ s ∈ S', s = FSlot.word)

def Cert.Valid (prog : List Asm) (C : Cert) : Prop :=
  ∀ i c S F R, C.fl (i :: c) = some S → C.fbMax (i :: c) = some F → C.rl (i :: c) = some R →
    frameStep prog C i c S F R

/-! ### The invariant -/

inductive GoodStack (prog : List Asm) (C : Cert) : List AVal → List Asm → Prop
  | root {σ : List AVal} {c : List Asm} {S R : FLayout} :
      C.fl c = some S → C.fbMax c = some 0 → C.rl c = some R → FMatch σ S →
      GoodStack prog C σ c
  | call {stk frame rest : List AVal} {c cRet : List Asm} {S Sret : FLayout} {F : Nat} {lRet : Label} :
      C.fl c = some S → C.fbMax c = some F → C.rl c = some Sret →
      FMatch frame S → (.code lRet) ∈ frame → findLabel lRet prog = some cRet → rest.length ≤ F →
      (∀ ws : List AVal, FMatch ws Sret → GoodStack prog C (ws ++ rest) cRet) →
      stk = frame ++ rest →
      GoodStack prog C stk c

theorem GoodStack.certAt {prog C} {σ : List AVal} {c : List Asm} (h : GoodStack prog C σ c) :
    ∃ S F R, C.fl c = some S ∧ C.fbMax c = some F ∧ C.rl c = some R := by
  cases h with
  | root hfl hfb hrl _ => exact ⟨_, _, _, hfl, hfb, hrl⟩
  | call hfl hfb hrl _ _ _ _ _ _ => exact ⟨_, _, _, hfl, hfb, hrl⟩

theorem GoodStack.bound {prog C} (hb : C.Bounded) {σ : List AVal} {c : List Asm}
    (h : GoodStack prog C σ c) : σ.length ≤ 1023 := by
  cases h with
  | @root σ c S R hfl hfb hrl hm => have := hb c S 0 hfl hfb; have := hm.length_eq; omega
  | @call stk frame rest c cRet S Sret F lRet hfl hfb hrl hm hmem hfind hle _ heq =>
      have hbnd := hb c S F hfl hfb; have := hm.length_eq; subst heq; rw [List.length_append]; omega

theorem GoodStack.entry {prog C} {R : FLayout} (h0fl : C.fl prog = some []) (h0fb : C.fbMax prog = some 0)
    (h0rl : C.rl prog = some R) : GoodStack prog C [] prog :=
  .root h0fl h0fb h0rl .nil

/-! ### Frame grow / shrink / same -/

theorem GoodStack.growWord {prog C} {σ : List AVal} {c₀ c₁ : List Asm} {S₀ : FLayout} {v : U256}
    (h : GoodStack prog C σ c₀) (h0 : C.fl c₀ = some S₀) (h1 : C.fl c₁ = some (.word :: S₀))
    (hfb : C.fbMax c₁ = C.fbMax c₀) (hrl : C.rl c₁ = C.rl c₀) :
    GoodStack prog C (.word v :: σ) c₁ := by
  cases h with
  | @root σ c S R hfl hfb0 hrl0 hm =>
      obtain rfl := Option.some.inj (h0 ▸ hfl)
      exact .root h1 (by rw [hfb, hfb0]) (by rw [hrl, hrl0]) (.word hm)
  | @call stk frame rest c cRet S Sret F lRet hfl hfb0 hrl0 hm hmem hfind hle hres heq =>
      obtain rfl := Option.some.inj (h0 ▸ hfl)
      refine .call (lRet := lRet) h1 (by rw [hfb, hfb0]) (by rw [hrl, hrl0]) (FMatch.word (v := v) hm)
        (List.mem_cons_of_mem _ hmem) hfind hle hres ?_
      rw [heq, List.cons_append]

theorem GoodStack.growRet {prog C} {σ : List AVal} {c₀ c₁ : List Asm} {S₀ : FLayout} {l : Label}
    (h : GoodStack prog C σ c₀) (h0 : C.fl c₀ = some S₀) (h1 : C.fl c₁ = some (.ret :: S₀))
    (hfb : C.fbMax c₁ = C.fbMax c₀) (hrl : C.rl c₁ = C.rl c₀) :
    GoodStack prog C (.code l :: σ) c₁ := by
  cases h with
  | @root σ c S R hfl hfb0 hrl0 hm =>
      obtain rfl := Option.some.inj (h0 ▸ hfl)
      exact .root h1 (by rw [hfb, hfb0]) (by rw [hrl, hrl0]) (.ret hm)
  | @call stk frame rest c cRet S Sret F lRet hfl hfb0 hrl0 hm hmem hfind hle hres heq =>
      obtain rfl := Option.some.inj (h0 ▸ hfl)
      refine .call (lRet := lRet) h1 (by rw [hfb, hfb0]) (by rw [hrl, hrl0]) (FMatch.ret (l := l) hm)
        (List.mem_cons_of_mem _ hmem) hfind hle hres ?_
      rw [heq, List.cons_append]

theorem GoodStack.same {prog C} {σ : List AVal} {c₀ c₁ : List Asm}
    (h : GoodStack prog C σ c₀) (hfl : C.fl c₁ = C.fl c₀) (hfb : C.fbMax c₁ = C.fbMax c₀)
    (hrl : C.rl c₁ = C.rl c₀) : GoodStack prog C σ c₁ := by
  cases h with
  | @root σ c S R hfl0 hfb0 hrl0 hm =>
      exact .root (by rw [hfl, hfl0]) (by rw [hfb, hfb0]) (by rw [hrl, hrl0]) hm
  | @call stk frame rest c cRet S Sret F lRet hfl0 hfb0 hrl0 hm hmem hfind hle hres heq =>
      exact .call (by rw [hfl, hfl0]) (by rw [hfb, hfb0]) (by rw [hrl, hrl0]) hm hmem hfind hle hres heq

theorem GoodStack.shrinkWord {prog C} {σ : List AVal} {c₀ c₁ : List Asm} {S' : FLayout} {v : AVal}
    (h : GoodStack prog C (v :: σ) c₀) (h0 : C.fl c₀ = some (.word :: S'))
    (h1 : C.fl c₁ = some S') (hfb : C.fbMax c₁ = C.fbMax c₀) (hrl : C.rl c₁ = C.rl c₀) :
    GoodStack prog C σ c₁ := by
  cases h with
  | @root vσ c S R hfl hfb0 hrl0 hm =>
      obtain rfl := Option.some.inj (h0 ▸ hfl)
      cases hm with
      | word hm' => exact .root h1 (by rw [hfb, hfb0]) (by rw [hrl, hrl0]) hm'
  | @call stk frame rest c cRet S Sret F lRet hfl hfb0 hrl0 hm hmem hfind hle hres heq =>
      obtain rfl := Option.some.inj (h0 ▸ hfl)
      cases hm with
      | @word w frame' S'' hm' =>
          rw [List.cons_append] at heq
          obtain ⟨rfl, rfl⟩ := List.cons.inj heq
          refine .call (lRet := lRet) h1 (by rw [hfb, hfb0]) (by rw [hrl, hrl0]) hm' ?_ hfind hle hres rfl
          cases List.mem_cons.mp hmem with
          | inl he => exact absurd he (by simp)
          | inr hm2 => exact hm2

/-- `op`: replace the top `p` word-args by `q` word-results. -/
theorem GoodStack.opFrame {prog C} {args rets : List U256} {σ : List AVal} {c₀ c₁ : List Asm}
    {S : FLayout} {p q : Nat}
    (h : GoodStack prog C (words args ++ σ) c₀) (h0 : C.fl c₀ = some S)
    (hp : p ≤ S.length) (hargs : args.length = p) (hrets : rets.length = q)
    (h1 : C.fl c₁ = some (List.replicate q FSlot.word ++ S.drop p))
    (hfb : C.fbMax c₁ = C.fbMax c₀) (hrl : C.rl c₁ = C.rl c₀) :
    GoodStack prog C (words rets ++ σ) c₁ := by
  cases h with
  | @root vσ c S' R hfl hfb0 hrl0 hm =>
      obtain rfl := Option.some.inj (h0 ▸ hfl)
      obtain ⟨Sargs, Sσ, rfl, hMargs, hMσ⟩ := hm.append_inv
      have hSalen : Sargs.length = p := by rw [← hMargs.length_eq, words_length, hargs]
      have hdrop : (Sargs ++ Sσ).drop p = Sσ := by rw [← hSalen, List.drop_left]
      refine .root h1 (by rw [hfb, hfb0]) (by rw [hrl, hrl0]) ?_
      rw [hdrop, ← hrets]; exact (FMatch.replicate_word rets).append hMσ
  | @call stk frame rest c cRet S' Sret F lRet hfl hfb0 hrl0 hm hmem hfind hle hres heq =>
      obtain rfl := Option.some.inj (h0 ▸ hfl)
      have hfrlen : frame.length = S.length := hm.length_eq
      have hple : args.length ≤ frame.length := by rw [hfrlen, hargs]; exact hp
      have hwa : words args = frame.take args.length := by
        have := congrArg (List.take args.length) heq
        rwa [List.take_left' (by rw [words_length]), List.take_append_of_le_length hple] at this
      have hσ : σ = frame.drop args.length ++ rest := by
        have := congrArg (List.drop args.length) heq
        rwa [List.drop_left' (by rw [words_length]), List.drop_append_of_le_length hple] at this
      have hframe : frame = words args ++ frame.drop args.length := by
        rw [hwa]; exact (List.take_append_drop args.length frame).symm
      rw [hframe] at hm
      obtain ⟨Sa, Sf, hSeq, hMa, hMf⟩ := hm.append_inv
      have hSalen : Sa.length = p := by rw [← hMa.length_eq, words_length, hargs]
      have hSdrop : S.drop p = Sf := by rw [hSeq, ← hSalen, List.drop_left]
      refine .call (lRet := lRet) (frame := words rets ++ frame.drop args.length) h1
        (by rw [hfb, hfb0]) (by rw [hrl, hrl0]) ?_ ?_ hfind hle hres ?_
      · rw [hSdrop, ← hrets]; exact (FMatch.replicate_word rets).append hMf
      · rw [hframe] at hmem
        cases (List.mem_append.mp hmem) with
        | inl hin => exact absurd hin (by simp [words])
        | inr hin => exact List.mem_append.mpr (Or.inr hin)
      · rw [hσ, ← List.append_assoc]

/-- The runtime cell at depth `i` matches the frame slot at depth `i`. -/
theorem GoodStack.slotAt {prog C} {σ : List AVal} {c : List Asm} {S : FLayout} {i : Nat} {x : AVal}
    {s : FSlot} (h : GoodStack prog C σ c) (hfl : C.fl c = some S) (hx : σ[i]? = some x)
    (hs : S[i]? = some s) : FMatch [x] [s] := by
  cases h with
  | @root σ' c' S' R hfl' hfb' hrl' hm =>
      obtain rfl : S = S' := Option.some.inj (hfl.symm.trans hfl')
      exact hm.at_idx hx hs
  | @call stk frame rest c' cRet S' Sret F lRet hfl' hfb' hrl' hm hmem hfind hle hres heq =>
      obtain rfl : S = S' := Option.some.inj (hfl.symm.trans hfl')
      have hilt : i < frame.length := by
        have hiS : i < S.length := by
          by_contra hc; rw [List.getElem?_eq_none (Nat.le_of_not_lt hc)] at hs; exact absurd hs (by simp)
        rw [hm.length_eq]; exact hiS
      have hxf : frame[i]? = some x := by rw [heq, List.getElem?_append_left hilt] at hx; exact hx
      exact hm.at_idx hxf hs

/-- `swap`: build the swapped frame match. -/
theorem FMatch.swap_build {x y : AVal} {τ ρf : List AVal} {sx sy : FSlot} {Sτ Sρ : FLayout}
    (hm : FMatch (x :: (τ ++ y :: ρf)) (sx :: (Sτ ++ sy :: Sρ))) (hτlen : Sτ.length = τ.length) :
    FMatch (y :: (τ ++ x :: ρf)) (sy :: (Sτ ++ sx :: Sρ)) := by
  obtain ⟨a, σ', ha, hx, hm1⟩ := hm.cons_inv'
  obtain ⟨rfl, rfl⟩ := List.cons.inj ha
  obtain ⟨σ1, σ2, hsplit, hMτ, hM2⟩ := hm1.append_inv_layout
  obtain ⟨rfl, rfl⟩ := List.append_inj hsplit (by rw [hMτ.length_eq, hτlen])
  obtain ⟨b, ρ', hb, hy, hMρ⟩ := hM2.cons_inv'
  obtain ⟨rfl, rfl⟩ := List.cons.inj hb
  exact hy.consMatch (hMτ.append (hx.consMatch hMρ))

theorem swap_mem {α} [DecidableEq α] {x y z : α} {τ ρf : List α}
    (h : z ∈ x :: (τ ++ y :: ρf)) : z ∈ y :: (τ ++ x :: ρf) := by
  simp only [List.mem_cons, List.mem_append] at h ⊢; tauto

theorem GoodStack.swapFrame {prog C} {x y : AVal} {τ ρ : List AVal} {c₀ c₁ : List Asm}
    {sx sy : FSlot} {Sτ Sρ : FLayout}
    (h : GoodStack prog C (x :: (τ ++ y :: ρ)) c₀) (h0 : C.fl c₀ = some (sx :: (Sτ ++ sy :: Sρ)))
    (hτlen : Sτ.length = τ.length) (h1 : C.fl c₁ = some (sy :: (Sτ ++ sx :: Sρ)))
    (hfb : C.fbMax c₁ = C.fbMax c₀) (hrl : C.rl c₁ = C.rl c₀) :
    GoodStack prog C (y :: (τ ++ x :: ρ)) c₁ := by
  cases h with
  | @root σ' c' S' R hfl hfb0 hrl0 hm =>
      obtain rfl := Option.some.inj (h0 ▸ hfl)
      exact .root h1 (by rw [hfb, hfb0]) (by rw [hrl, hrl0]) (hm.swap_build hτlen)
  | @call stk frame rest c' cRet S' Sret F lRet hfl hfb0 hrl0 hm hmem hfind hle hres heq =>
      obtain rfl := Option.some.inj (h0 ▸ hfl)
      obtain ⟨fx, frame1, rfl, hSMfx, hm1⟩ := hm.cons_inv'
      obtain ⟨fτ, frame2, rfl, hMfτ, hM2⟩ := hm1.append_inv_layout
      obtain ⟨fy, fρ, rfl, hSMfy, hMfρ⟩ := hM2.cons_inv'
      rw [List.cons_append, List.append_assoc, List.cons_append] at heq
      obtain ⟨rfl, hrest⟩ := List.cons.inj heq
      obtain ⟨rfl, rfl, rfl⟩ := list_split_uniq hrest (by rw [hMfτ.length_eq, hτlen])
      refine .call (lRet := lRet) (frame := y :: (τ ++ x :: fρ)) h1 (by rw [hfb, hfb0])
        (by rw [hrl, hrl0]) ?_ ?_ hfind hle hres ?_
      · exact hSMfy.consMatch (hMfτ.append (hSMfx.consMatch hMfρ))
      · exact swap_mem hmem
      · rw [List.cons_append, List.append_assoc, List.cons_append]

variable [model : ExternalModel]

set_option warningAsError false in
/-- **Preservation.** All cases proven except `call` (`jump` to a function entry), which is stubbed. -/
theorem GoodStack.step {prog : List Asm} {C : Cert} (hV : C.Valid prog)
    {a b : AConf} (hstep : AStep (model := model) prog a b) (hsuf : a.code <:+ prog)
    (hinv : GoodStack prog C a.stk a.code) :
    GoodStack prog C b.stk b.code := by
  cases hstep with
  | @push v c σ yst =>
      obtain ⟨S, F, R, hfl, hfb, hrl⟩ := hinv.certAt
      obtain ⟨hflc, hfbc, hrlc⟩ := hV _ c S F R hfl hfb hrl
      exact hinv.growWord hfl hflc (by rw [hfbc, hfb]) (by rw [hrlc, hrl])
  | @pushLabel l c σ yst hdef =>
      obtain ⟨S, F, R, hfl, hfb, hrl⟩ := hinv.certAt
      obtain ⟨hflc, hfbc, hrlc⟩ := hV _ c S F R hfl hfb hrl
      exact hinv.growRet hfl hflc (by rw [hfbc, hfb]) (by rw [hrlc, hrl])
  | @pop v σ c yst =>
      obtain ⟨S, F, R, hfl, hfb, hrl⟩ := hinv.certAt
      obtain ⟨S', hSeq, hflc, hfbc, hrlc⟩ := hV _ c S F R hfl hfb hrl
      subst hSeq
      exact hinv.shrinkWord hfl hflc (by rw [hfbc, hfb]) (by rw [hrlc, hrl])
  | @label l c σ yst =>
      obtain ⟨S, F, R, hfl, hfb, hrl⟩ := hinv.certAt
      obtain ⟨hflc, hfbc, hrlc⟩ := hV _ c S F R hfl hfb hrl
      exact hinv.same (by rw [hflc, hfl]) (by rw [hfbc, hfb]) (by rw [hrlc, hrl])
  | @jump l c c' σ yst hfind =>
      obtain ⟨S, F, R, hfl, hfb, hrl⟩ := hinv.certAt
      cases hV _ c S F R hfl hfb hrl with
      | inl hlocal =>
          obtain ⟨t, hfind', hflt, hfbt, hrlt⟩ := hlocal
          rw [hfind] at hfind'; obtain rfl := Option.some.inj hfind'
          exact hinv.same (by rw [hflt, hfl]) (by rw [hfbt, hfb]) (by rw [hrlt, hrl])
      | inr _ => sorry  -- WIP: the call case (jump to a function entry: frame push)
  | @jumpiTaken l v c c' σ yst hv hfind =>
      obtain ⟨S, F, R, hfl, hfb, hrl⟩ := hinv.certAt
      obtain ⟨S', hSeq, ⟨t, hfind', hflt, hfbt, hrlt⟩, _, _, _⟩ := hV _ c S F R hfl hfb hrl
      subst hSeq
      rw [hfind] at hfind'; obtain rfl := Option.some.inj hfind'
      exact hinv.shrinkWord hfl hflt (by rw [hfbt, hfb]) (by rw [hrlt, hrl])
  | @jumpiFall l v c σ yst hv =>
      obtain ⟨S, F, R, hfl, hfb, hrl⟩ := hinv.certAt
      obtain ⟨S', hSeq, _, hflc, hfbc, hrlc⟩ := hV _ c S F R hfl hfb hrl
      subst hSeq
      exact hinv.shrinkWord hfl hflc (by rw [hfbc, hfb]) (by rw [hrlc, hrl])
  | @op yop args rets c σ yst yst' hstepOp =>
      obtain ⟨S, F, R, hfl, hfb, hrl⟩ := hinv.certAt
      obtain ⟨o, hop, hple, hflc, hfbc, hrlc⟩ := hV _ c S F R hfl hfb hrl
      obtain ⟨hargs, hrets⟩ := builtin_arity hop hstepOp
      exact hinv.opFrame hfl hple hargs hrets hflc (by rw [hfbc, hfb]) (by rw [hrlc, hrl])
  | @dup n v τ ρ c yst hτ =>
      obtain ⟨S, F, R, hfl, hfb, hrl⟩ := hinv.certAt
      obtain ⟨sl, hidx, hflc, hfbc, hrlc⟩ := hV _ c S F R hfl hfb hrl
      have hvidx : (τ ++ v :: ρ)[n.val]? = some v := by
        rw [← hτ, List.getElem?_append_right (Nat.le_refl _)]; simp
      have hsm : FMatch [v] [sl] := hinv.slotAt hfl hvidx hidx
      cases hsm with
      | word _ => exact hinv.growWord hfl hflc (by rw [hfbc, hfb]) (by rw [hrlc, hrl])
      | ret _ => exact hinv.growRet hfl hflc (by rw [hfbc, hfb]) (by rw [hrlc, hrl])
  | @swap n x y τ ρ c yst hτ =>
      obtain ⟨S, F, R, hfl, hfb, hrl⟩ := hinv.certAt
      obtain ⟨sx, mid, sy, rst, hSeq, hmidlen, hflc, hfbc, hrlc⟩ := hV _ c S F R hfl hfb hrl
      subst hSeq
      have hτlen : mid.length = τ.length := by rw [hmidlen, hτ]
      exact hinv.swapFrame hfl hτlen hflc (by rw [hfbc, hfb]) (by rw [hrlc, hrl])
  | @dynJump l c c' σ yst hfind =>
      obtain ⟨S, F, R, hfl, hfb, hrl⟩ := hinv.certAt
      obtain ⟨hF1, S', hSeq, hRS', hwords⟩ := hV _ c S F R hfl hfb hrl
      cases hinv with
      | @root σ0 c0 S0 R0 hfl0 hfb0 hrl0 hm =>
          obtain rfl : (0 : Nat) = F := Option.some.inj (hfb0.symm.trans hfb)
          omega
      | @call stk frame rest c0 cRet S0 Sret F0 lRet hfl0 hfb0 hrl0 hm hmem hfind0 hle hres heq =>
          obtain rfl : S = S0 := Option.some.inj (hfl.symm.trans hfl0)
          have hSretS' : Sret = S' := by
            have h1 : Sret = R := Option.some.inj (hrl0.symm.trans hrl); rw [h1, hRS']
          rw [hSretS'] at hres
          rw [hSeq] at hm
          obtain ⟨a, frame', rfl, hxa, hMf⟩ := hm.cons_inv'
          cases hxa with
          | @ret lf =>
              rw [List.cons_append] at heq
              obtain ⟨hcq, rfl⟩ := List.cons.inj heq
              obtain rfl := AVal.code.inj hcq
              have hallw := hMf.allWord hwords
              have hlreq : lRet = l := by
                rcases List.mem_cons.mp hmem with he | hin
                · exact by simpa using he
                · obtain ⟨w, hw⟩ := hallw _ hin; exact absurd hw (by simp)
              subst hlreq
              rw [hfind] at hfind0; obtain rfl := Option.some.inj hfind0
              exact hres frame' hMf

/-- The invariant holds at every reachable configuration. -/
theorem GoodStack.reach {prog : List Asm} {C : Cert} (hV : C.Valid prog)
    {a b : AConf} (hsteps : ASteps (model := model) prog a b) (hsuf : a.code <:+ prog)
    (hinv : GoodStack prog C a.stk a.code) : GoodStack prog C b.stk b.code := by
  induction hsteps with
  | refl => exact hinv
  | head hstep _ ih => exact ih (hstep.suffix hsuf) (GoodStack.step hV hstep hsuf hinv)

/-- The run stack-bound. -/
theorem run_stack_bound2 {prog : List Asm} {C : Cert} (hV : C.Valid prog) (hb : C.Bounded)
    {R : FLayout} (h0fl : C.fl prog = some []) (h0fb : C.fbMax prog = some 0)
    (h0rl : C.rl prog = some R) (yst : EvmState) :
    ∀ mid, ASteps (model := model) prog ⟨prog, [], yst⟩ mid → mid.stk.length ≤ 1023 :=
  fun _ hsteps =>
    (GoodStack.reach hV hsteps (List.suffix_refl _) (GoodStack.entry h0fl h0fb h0rl)).bound hb

end YulEvmCompiler
