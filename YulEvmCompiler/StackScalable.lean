import YulEvmCompiler.StackBound

set_option warningAsError true
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

/-- A frame-relative slot: a plain word; a **target-less** return address `ret` (a function's own
incoming return address, whose target is context-dependent); or a **tagged** return address
`retTo l` for a caller's pending-call setup (the target label `l` is static per caller position). -/
inductive FSlot
  | word
  | ret
  | retTo (l : Label)
  deriving DecidableEq

abbrev FLayout := List FSlot

/-- Runtime stack ↔ frame layout: words match `word`; *any* return address matches `ret`; a
`retTo l` matches exactly the return address `.code l`. -/
inductive FMatch : List AVal → FLayout → Prop
  | nil : FMatch [] []
  | word {v : U256} {σ : List AVal} {S : FLayout} : FMatch σ S → FMatch (.word v :: σ) (.word :: S)
  | ret {l : Label} {σ : List AVal} {S : FLayout} : FMatch σ S → FMatch (.code l :: σ) (.ret :: S)
  | retTo {l : Label} {σ : List AVal} {S : FLayout} : FMatch σ S →
      FMatch (.code l :: σ) (.retTo l :: S)

theorem FMatch.length_eq {σ : List AVal} {S : FLayout} (h : FMatch σ S) : σ.length = S.length := by
  induction h with
  | nil => rfl
  | word _ ih => simp [ih]
  | ret _ ih => simp [ih]
  | retTo _ ih => simp [ih]

theorem FMatch.append {σ₁ σ₂ : List AVal} {S₁ S₂ : FLayout}
    (h₁ : FMatch σ₁ S₁) (h₂ : FMatch σ₂ S₂) : FMatch (σ₁ ++ σ₂) (S₁ ++ S₂) := by
  induction h₁ with
  | nil => exact h₂
  | word _ ih => exact .word ih
  | ret _ ih => exact .ret ih
  | retTo _ ih => exact .retTo ih

theorem FMatch.append_inv {σ₁ σ₂ : List AVal} {S : FLayout} (h : FMatch (σ₁ ++ σ₂) S) :
    ∃ S₁ S₂, S = S₁ ++ S₂ ∧ FMatch σ₁ S₁ ∧ FMatch σ₂ S₂ := by
  induction σ₁ generalizing S with
  | nil => exact ⟨[], S, rfl, .nil, h⟩
  | cons v σ₁ ih =>
      rw [List.cons_append] at h
      cases h with
      | word htl => obtain ⟨S₁, S₂, rfl, h1, h2⟩ := ih htl; exact ⟨.word :: S₁, S₂, rfl, .word h1, h2⟩
      | ret htl => obtain ⟨S₁, S₂, rfl, h1, h2⟩ := ih htl; exact ⟨.ret :: S₁, S₂, rfl, .ret h1, h2⟩
      | @retTo l _ _ htl => obtain ⟨S₁, S₂, rfl, h1, h2⟩ := ih htl
                            exact ⟨.retTo l :: S₁, S₂, rfl, .retTo h1, h2⟩

/-- Head inversion exposing the runtime cons shape. -/
theorem FMatch.cons_inv' {σ : List AVal} {s : FSlot} {S : FLayout} (h : FMatch σ (s :: S)) :
    ∃ a σ', σ = a :: σ' ∧ FMatch [a] [s] ∧ FMatch σ' S := by
  cases h with
  | word htl => exact ⟨_, _, rfl, .word .nil, htl⟩
  | ret htl => exact ⟨_, _, rfl, .ret .nil, htl⟩
  | retTo htl => exact ⟨_, _, rfl, .retTo .nil, htl⟩

/-- Head composition. -/
theorem FMatch.consMatch {a : AVal} {σ : List AVal} {s : FSlot} {S : FLayout}
    (h1 : FMatch [a] [s]) (h2 : FMatch σ S) : FMatch (a :: σ) (s :: S) := by
  cases h1 with
  | word _ => exact .word h2
  | ret _ => exact .ret h2
  | retTo _ => exact .retTo h2

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
  | @retTo l σ' S' _ ih => intro i x s hx hs; cases i with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hs; subst hx; subst hs; exact .retTo .nil
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
  | @retTo l σ' S' _ _ =>
      exact absurd (hw (.retTo l) (by simp)) (by simp)

/-! ### `NoRet`: a layout with no bare `ret` slot (main's frame; propagated) -/

/-- No plain (target-less) `ret` slot — a property of `main`'s frame (it has no incoming return
address, only words and its own pending `retTo` setups). -/
def NoRet (S : FLayout) : Prop := ∀ s ∈ S, s ≠ FSlot.ret

theorem NoRet.word {S} (h : NoRet S) : NoRet (FSlot.word :: S) := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs
  · decide
  · exact h s hs
theorem NoRet.retTo {S l} (h : NoRet S) : NoRet (FSlot.retTo l :: S) := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs
  · simp
  · exact h s hs
theorem NoRet.tail {S s0} (h : NoRet (s0 :: S)) : NoRet S :=
  fun s hs => h s (List.mem_cons_of_mem _ hs)
theorem NoRet.drop {S} (n : Nat) (h : NoRet S) : NoRet (S.drop n) :=
  fun s hs => h s (List.mem_of_mem_drop hs)
theorem NoRet.replicate_word_append {q S} (h : NoRet S) :
    NoRet (List.replicate q FSlot.word ++ S) := by
  intro s hs
  rcases List.mem_append.mp hs with h1 | h2
  · rw [List.eq_of_mem_replicate h1]; decide
  · exact h s h2
theorem NoRet.swap {sx sy : FSlot} {Sτ Sρ : FLayout} (h : NoRet (sx :: (Sτ ++ sy :: Sρ))) :
    NoRet (sy :: (Sτ ++ sx :: Sρ)) := by
  intro s hs; apply h s; simp only [List.mem_cons, List.mem_append] at hs ⊢; tauto
theorem NoRet.append {S1 S2} (h1 : NoRet S1) (h2 : NoRet S2) : NoRet (S1 ++ S2) := by
  intro s hs; rcases List.mem_append.mp hs with h | h
  · exact h1 s h
  · exact h2 s h

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
  -- Same frame effect as `push`; only the lowered width differs.
  | .pushImmutable _ _, c, S, F, R =>
      C.fl c = some (.word :: S) ∧ C.fbMax c = some F ∧ C.rl c = some R
  | .dup n,       c, S, F, R => S[n.val]? = some FSlot.word ∧ C.fl c = some (.word :: S)
      ∧ C.fbMax c = some F ∧ C.rl c = some R
  | .pushLabel l, c, S, F, R => C.fl c = some (.retTo l :: S) ∧ C.fbMax c = some F ∧ C.rl c = some R
  | .pop,         c, S, F, R => ∃ S', S = .word :: S' ∧ C.fl c = some S' ∧ C.fbMax c = some F
      ∧ C.rl c = some R
  | .swap n,      c, S, F, R => ∃ sx mid sy rst, S = sx :: (mid ++ sy :: rst) ∧ mid.length = n.val
      ∧ sx = FSlot.word ∧ (∀ s ∈ mid, s = FSlot.word)
      ∧ C.fl c = some (sy :: (mid ++ sx :: rst)) ∧ C.fbMax c = some F ∧ C.rl c = some R
  | .label _,     c, S, F, R => C.fl c = some S ∧ C.fbMax c = some F ∧ C.rl c = some R
  | .op yop,      c, S, F, R => ∃ o, opTable yop = some o ∧ Operation.popArity o ≤ S.length ∧
      C.fl c = some (List.replicate (Operation.pushArity o) FSlot.word ++ S.drop (Operation.popArity o))
      ∧ C.fbMax c = some F ∧ C.rl c = some R
  | .jump l,      c, S, F, R =>
      (∃ t, findLabel l prog = some t ∧ C.fl t = some S ∧ C.fbMax t = some F ∧ C.rl t = some R)
      ∨ (∃ Sw Smid Lret c' t Sret,
          findLabel l prog = some t ∧
          c = .label Lret :: c' ∧
          S = (Sw ++ [FSlot.retTo Lret]) ++ Smid ∧
          (∀ s ∈ Sw, s = FSlot.word) ∧
          C.fl t = some (Sw ++ [FSlot.ret]) ∧ (∃ Ft, C.fbMax t = some Ft ∧ F + Smid.length ≤ Ft) ∧
          C.rl t = some Sret ∧ (∀ s ∈ Sret, s = FSlot.word) ∧
          findLabel Lret prog = some c' ∧
          C.fl c' = some (Sret ++ Smid) ∧ C.fbMax c' = some F ∧ C.rl c' = some R)
  | .jumpi l,     c, S, F, R => ∃ S', S = .word :: S' ∧
      (∃ t, findLabel l prog = some t ∧ C.fl t = some S' ∧ C.fbMax t = some F ∧ C.rl t = some R) ∧
      C.fl c = some S' ∧ C.fbMax c = some F ∧ C.rl c = some R
  | .dynJump,     _, S, _F, R => ∃ S', S = .ret :: S' ∧ R = S' ∧ (∀ s ∈ S', s = FSlot.word)

def Cert.Valid (prog : List Asm) (C : Cert) : Prop :=
  ∀ i c S F R, C.fl (i :: c) = some S → C.fbMax (i :: c) = some F → C.rl (i :: c) = some R →
    frameStep prog C i c S F R

/-! ### The invariant -/

/-- All-word runtime list. -/
def IsWords (l : List AVal) : Prop := ∀ x ∈ l, ∃ v : U256, x = .word v

/-- The active return address is the **deepest** code cell of the frame: `frame = above ++ .code
lRet :: below` with `below` all words. This locates it unambiguously (pending-call setups live in
`above`; `retRot` moves the address up through words). -/
inductive GoodStack (prog : List Asm) (C : Cert) : List AVal → List Asm → Prop
  | root {σ : List AVal} {c : List Asm} {S R : FLayout} :
      C.fl c = some S → C.fbMax c = some 0 → C.rl c = some R → (∀ s ∈ S, s ≠ FSlot.ret) →
      FMatch σ S → GoodStack prog C σ c
  | call {stk above below rest : List AVal} {c cRet : List Asm} {S Sret : FLayout} {F : Nat}
      {lRet : Label} :
      C.fl c = some S → C.fbMax c = some F → C.rl c = some Sret →
      FMatch (above ++ .code lRet :: below) S → S[above.length]? = some FSlot.ret → IsWords below →
      findLabel lRet prog = some cRet → rest.length ≤ F →
      (∀ ws : List AVal, FMatch ws Sret → GoodStack prog C (ws ++ rest) cRet) →
      stk = (above ++ .code lRet :: below) ++ rest →
      GoodStack prog C stk c

theorem GoodStack.certAt {prog C} {σ : List AVal} {c : List Asm} (h : GoodStack prog C σ c) :
    ∃ S F R, C.fl c = some S ∧ C.fbMax c = some F ∧ C.rl c = some R := by
  cases h with
  | root hfl hfb hrl _ => exact ⟨_, _, _, hfl, hfb, hrl⟩
  | call hfl hfb hrl _ _ _ _ _ _ => exact ⟨_, _, _, hfl, hfb, hrl⟩

theorem GoodStack.bound {prog C} (hb : C.Bounded) {σ : List AVal} {c : List Asm}
    (h : GoodStack prog C σ c) : σ.length ≤ 1023 := by
  cases h with
  | @root σ c S R hfl hfb hrl hnoret hm => have := hb c S 0 hfl hfb; have := hm.length_eq; omega
  | @call stk above below rest c cRet S Sret F lRet hfl hfb hrl hm hact hbw hfind hle _ heq =>
      have hbnd := hb c S F hfl hfb; have hlen := hm.length_eq; subst heq
      rw [List.length_append]; omega

theorem GoodStack.entry {prog C} {R : FLayout} (h0fl : C.fl prog = some []) (h0fb : C.fbMax prog = some 0)
    (h0rl : C.rl prog = some R) : GoodStack prog C [] prog :=
  .root h0fl h0fb h0rl (by simp) .nil

/-! ### Frame grow / shrink / same -/

theorem GoodStack.growWord {prog C} {σ : List AVal} {c₀ c₁ : List Asm} {S₀ : FLayout} {v : U256}
    (h : GoodStack prog C σ c₀) (h0 : C.fl c₀ = some S₀) (h1 : C.fl c₁ = some (.word :: S₀))
    (hfb : C.fbMax c₁ = C.fbMax c₀) (hrl : C.rl c₁ = C.rl c₀) :
    GoodStack prog C (.word v :: σ) c₁ := by
  cases h with
  | @root σ c S R hfl hfb0 hrl0 hnoret hm =>
      obtain rfl := Option.some.inj (h0 ▸ hfl)
      exact .root h1 (by rw [hfb, hfb0]) (by rw [hrl, hrl0]) (NoRet.word hnoret) (.word hm)
  | @call stk above below rest c cRet S Sret F lRet hfl hfb0 hrl0 hm hact hbw hfind hle hres heq =>
      obtain rfl := Option.some.inj (h0 ▸ hfl)
      refine .call (above := .word v :: above) (below := below) (lRet := lRet) h1
        (by rw [hfb, hfb0]) (by rw [hrl, hrl0]) (FMatch.word (v := v) hm) (by simp only [List.length_cons, List.getElem?_cons_succ]; exact hact) hbw hfind hle hres ?_
      rw [heq]; rfl

theorem GoodStack.growRetTo {prog C} {σ : List AVal} {c₀ c₁ : List Asm} {S₀ : FLayout} {l : Label}
    (h : GoodStack prog C σ c₀) (h0 : C.fl c₀ = some S₀) (h1 : C.fl c₁ = some (.retTo l :: S₀))
    (hfb : C.fbMax c₁ = C.fbMax c₀) (hrl : C.rl c₁ = C.rl c₀) :
    GoodStack prog C (.code l :: σ) c₁ := by
  cases h with
  | @root σ c S R hfl hfb0 hrl0 hnoret hm =>
      obtain rfl := Option.some.inj (h0 ▸ hfl)
      exact .root h1 (by rw [hfb, hfb0]) (by rw [hrl, hrl0]) (NoRet.retTo hnoret) (.retTo hm)
  | @call stk above below rest c cRet S Sret F lRet hfl hfb0 hrl0 hm hact hbw hfind hle hres heq =>
      obtain rfl := Option.some.inj (h0 ▸ hfl)
      refine .call (above := .code l :: above) (below := below) (lRet := lRet) h1
        (by rw [hfb, hfb0]) (by rw [hrl, hrl0]) (FMatch.retTo (l := l) hm) (by simp only [List.length_cons, List.getElem?_cons_succ]; exact hact) hbw hfind hle hres ?_
      rw [heq]; rfl

theorem GoodStack.same {prog C} {σ : List AVal} {c₀ c₁ : List Asm}
    (h : GoodStack prog C σ c₀) (hfl : C.fl c₁ = C.fl c₀) (hfb : C.fbMax c₁ = C.fbMax c₀)
    (hrl : C.rl c₁ = C.rl c₀) : GoodStack prog C σ c₁ := by
  cases h with
  | @root σ c S R hfl0 hfb0 hrl0 hnoret hm =>
      exact .root (by rw [hfl, hfl0]) (by rw [hfb, hfb0]) (by rw [hrl, hrl0]) hnoret hm
  | @call stk above below rest c cRet S Sret F lRet hfl0 hfb0 hrl0 hm hact hbw hfind hle hres heq =>
      exact .call (by rw [hfl, hfl0]) (by rw [hfb, hfb0]) (by rw [hrl, hrl0]) hm hact hbw hfind hle hres heq

theorem GoodStack.shrinkWord {prog C} {σ : List AVal} {c₀ c₁ : List Asm} {S' : FLayout} {v : AVal}
    (h : GoodStack prog C (v :: σ) c₀) (h0 : C.fl c₀ = some (.word :: S'))
    (h1 : C.fl c₁ = some S') (hfb : C.fbMax c₁ = C.fbMax c₀) (hrl : C.rl c₁ = C.rl c₀) :
    GoodStack prog C σ c₁ := by
  cases h with
  | @root vσ c S R hfl hfb0 hrl0 hnoret hm =>
      obtain rfl := Option.some.inj (h0 ▸ hfl)
      cases hm with
      | word hm' => exact .root h1 (by rw [hfb, hfb0]) (by rw [hrl, hrl0]) (NoRet.tail hnoret) hm'
  | @call stk above below rest c cRet S Sret F lRet hfl hfb0 hrl0 hm hact hbw hfind hle hres heq =>
      obtain rfl := Option.some.inj (h0 ▸ hfl)
      cases above with
      | nil => rw [List.nil_append] at hm; nomatch hm
      | cons a above' =>
          rw [List.cons_append] at hm heq
          cases hm with
          | @word w σ'' S'' hm' =>
              obtain ⟨rfl, rfl⟩ := List.cons.inj heq
              exact .call (above := above') (below := below) (lRet := lRet) h1
                (by rw [hfb, hfb0]) (by rw [hrl, hrl0]) hm' (by simp only [List.length_cons, List.getElem?_cons_succ] at hact; exact hact) hbw hfind hle hres rfl

/-- `op`: replace the top `p` word-args by `q` word-results. -/
theorem GoodStack.opFrame {prog C} {args rets : List U256} {σ : List AVal} {c₀ c₁ : List Asm}
    {S : FLayout} {p q : Nat}
    (h : GoodStack prog C (words args ++ σ) c₀) (h0 : C.fl c₀ = some S)
    (hp : p ≤ S.length) (hargs : args.length = p) (hrets : rets.length = q)
    (h1 : C.fl c₁ = some (List.replicate q FSlot.word ++ S.drop p))
    (hfb : C.fbMax c₁ = C.fbMax c₀) (hrl : C.rl c₁ = C.rl c₀) :
    GoodStack prog C (words rets ++ σ) c₁ := by
  cases h with
  | @root vσ c S' R hfl hfb0 hrl0 hnoret hm =>
      obtain rfl := Option.some.inj (h0 ▸ hfl)
      obtain ⟨Sargs, Sσ, rfl, hMargs, hMσ⟩ := hm.append_inv
      have hSalen : Sargs.length = p := by rw [← hMargs.length_eq, words_length, hargs]
      have hdrop : (Sargs ++ Sσ).drop p = Sσ := by rw [← hSalen, List.drop_left]
      refine .root h1 (by rw [hfb, hfb0]) (by rw [hrl, hrl0])
        (NoRet.replicate_word_append (NoRet.drop p hnoret)) ?_
      rw [hdrop, ← hrets]; exact (FMatch.replicate_word rets).append hMσ
  | @call stk above below rest c cRet S' Sret F lRet hfl hfb0 hrl0 hm hact hbw hfind hle hres heq =>
      obtain rfl := Option.some.inj (h0 ▸ hfl)
      have hple : args.length ≤ (above ++ AVal.code lRet :: below).length := by
        rw [hm.length_eq, hargs]; exact hp
      have hwa : words args = (above ++ AVal.code lRet :: below).take args.length := by
        have := congrArg (List.take args.length) heq
        rwa [List.take_left' (by rw [words_length]), List.take_append_of_le_length hple] at this
      have hσ : σ = (above ++ AVal.code lRet :: below).drop args.length ++ rest := by
        have := congrArg (List.drop args.length) heq
        rwa [List.drop_left' (by rw [words_length]), List.drop_append_of_le_length hple] at this
      have hpabove : args.length ≤ above.length := by
        by_contra hlt
        rw [Nat.not_le] at hlt
        have hidx : (above ++ AVal.code lRet :: below)[above.length]? = some (AVal.code lRet) := by
          rw [List.getElem?_append_right (le_refl _), Nat.sub_self]; rfl
        have hidx2 : (words args)[above.length]? = some (AVal.code lRet) := by
          rw [hwa, List.getElem?_take, if_pos hlt]; exact hidx
        rw [words, List.getElem?_map] at hidx2
        rcases hh : args[above.length]? with _ | a
        · rw [hh] at hidx2; simp at hidx2
        · rw [hh] at hidx2; simp at hidx2
      have hdropfr : (above ++ AVal.code lRet :: below).drop args.length
          = above.drop args.length ++ AVal.code lRet :: below :=
        List.drop_append_of_le_length hpabove
      have hfreq : above ++ AVal.code lRet :: below
          = words args ++ (above ++ AVal.code lRet :: below).drop args.length := by
        conv_lhs => rw [← List.take_append_drop args.length (above ++ AVal.code lRet :: below)]
        rw [hwa]
      rw [hfreq] at hm
      obtain ⟨Sa, Sf, hSeq, hMa, hMf⟩ := hm.append_inv
      have hSalen : Sa.length = args.length := by rw [← hMa.length_eq, words_length]
      have hSdrop : S.drop p = Sf := by rw [hSeq, ← hargs, ← hSalen, List.drop_left]
      refine .call (above := words rets ++ above.drop args.length) (below := below) (lRet := lRet) h1
        (by rw [hfb, hfb0]) (by rw [hrl, hrl0]) ?_ ?_ hbw hfind hle hres ?_
      · rw [hSdrop, ← hrets]
        have hfr2 : (words rets ++ above.drop args.length) ++ AVal.code lRet :: below
            = words rets ++ (above ++ AVal.code lRet :: below).drop args.length := by
          rw [hdropfr, List.append_assoc]
        rw [hfr2]
        exact (FMatch.replicate_word rets).append hMf
      · rw [List.length_append, List.length_drop, words_length, hrets,
            List.getElem?_append_right (by rw [List.length_replicate]; omega),
            List.length_replicate, List.getElem?_drop, ← hargs,
            show args.length + (q + (above.length - args.length) - q) = above.length from by omega]
        exact hact
      · rw [hσ, hdropfr]; simp only [List.append_assoc]

/-- The runtime cell at depth `i` matches the frame slot at depth `i`. -/
theorem GoodStack.slotAt {prog C} {σ : List AVal} {c : List Asm} {S : FLayout} {i : Nat} {x : AVal}
    {s : FSlot} (h : GoodStack prog C σ c) (hfl : C.fl c = some S) (hx : σ[i]? = some x)
    (hs : S[i]? = some s) : FMatch [x] [s] := by
  cases h with
  | @root σ' c' S' R hfl' hfb' hrl' hnoret hm =>
      obtain rfl : S = S' := Option.some.inj (hfl.symm.trans hfl')
      exact hm.at_idx hx hs
  | @call stk above below rest c' cRet S' Sret F lRet hfl' hfb' hrl' hm hact hbw hfind hle hres heq =>
      obtain rfl : S = S' := Option.some.inj (hfl.symm.trans hfl')
      have hilt : i < (above ++ .code lRet :: below).length := by
        have hiS : i < S.length := by
          by_contra hc; rw [List.getElem?_eq_none (Nat.le_of_not_lt hc)] at hs; exact absurd hs (by simp)
        rw [hm.length_eq]; exact hiS
      have hxf : (above ++ .code lRet :: below)[i]? = some x := by
        rw [heq, List.getElem?_append_left hilt] at hx; exact hx
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
    (hsxw : sx = FSlot.word) (hmidw : ∀ s ∈ Sτ, s = FSlot.word)
    (hτlen : Sτ.length = τ.length) (h1 : C.fl c₁ = some (sy :: (Sτ ++ sx :: Sρ)))
    (hfb : C.fbMax c₁ = C.fbMax c₀) (hrl : C.rl c₁ = C.rl c₀) :
    GoodStack prog C (y :: (τ ++ x :: ρ)) c₁ := by
  subst hsxw
  cases h with
  | @root σ' c' S' R hfl hfb0 hrl0 hnoret hm =>
      obtain rfl := Option.some.inj (h0 ▸ hfl)
      exact .root h1 (by rw [hfb, hfb0]) (by rw [hrl, hrl0]) (NoRet.swap hnoret) (hm.swap_build hτlen)
  | @call stk above below rest c' cRet S' Sret F lRet hfl hfb0 hrl0 hm hact hbw hfind hle hres heq =>
      obtain rfl := Option.some.inj (h0 ▸ hfl)
      -- Peel the layout: frame = .word wv :: (τ ++ y :: fσ2'), with τ all words.
      obtain ⟨w, fr', hfreq, hmw, hmfr'⟩ := hm.cons_inv'
      cases hmw with
      | @word wv =>
        obtain ⟨fσ1, fσ2, hfr'eq, hMσ1, hMσ2⟩ := hmfr'.append_inv_layout
        obtain ⟨fa, fσ2', hfσ2eq, hMa, hMσ2'⟩ := hMσ2.cons_inv'
        subst hfr'eq; subst hfσ2eq
        rw [hfreq, List.cons_append] at heq
        obtain ⟨rfl, htail⟩ := List.cons.inj heq
        rw [List.append_assoc, List.cons_append] at htail
        have hσ1len : τ.length = fσ1.length := by rw [hMσ1.length_eq, hτlen]
        obtain ⟨rfl, rfl, rfl⟩ := list_split_uniq htail hσ1len
        have hτw : IsWords τ := hMσ1.allWord hmidw
        have hMnew : FMatch (y :: (τ ++ AVal.word wv :: fσ2')) (sy :: (Sτ ++ .word :: Sρ)) :=
          hMa.consMatch (hMσ1.append ((FMatch.word (v := wv) FMatch.nil).consMatch hMσ2'))
        have hstk : y :: (τ ++ AVal.word wv :: (fσ2' ++ rest))
            = (y :: (τ ++ AVal.word wv :: fσ2')) ++ rest := by simp
        have hfreq2 : above ++ AVal.code lRet :: below = (AVal.word wv :: τ) ++ (y :: fσ2') := by
          rw [hfreq]; rfl
        -- the leaf where `y` itself is the (deepest) return address
        have leafNil : sy = FSlot.ret → y = AVal.code lRet → below = fσ2' →
            GoodStack prog C ((y :: (τ ++ AVal.word wv :: fσ2')) ++ rest) c₁ := by
          rintro hsy rfl rfl
          refine .call (above := []) (below := τ ++ AVal.word wv :: below) (lRet := lRet) h1
            (by rw [hfb, hfb0]) (by rw [hrl, hrl0]) (by rw [List.nil_append]; exact hMnew)
            (by simp [hsy]) ?_ hfind hle hres (by rw [List.nil_append])
          intro z hz
          rcases List.mem_append.mp hz with hz | hz
          · exact hτw _ hz
          · rcases List.mem_cons.mp hz with rfl | hz
            · exact ⟨wv, rfl⟩
            · exact hbw _ hz
        -- `sy = .ret`: the active return slot lies at depth `|Sτ|` in the old layout.
        have hsyret : above = AVal.word wv :: τ → sy = FSlot.ret := by
          intro habove
          have h := hact
          rw [habove] at h
          simp only [List.length_cons, List.getElem?_cons_succ] at h
          rw [← hτlen, List.getElem?_append_right (le_refl _), Nat.sub_self,
              List.getElem?_cons_zero] at h
          exact Option.some.inj h
        rw [hstk]
        rcases List.append_eq_append_iff.mp hfreq2 with ⟨t, ht1, ht2⟩ | ⟨t, ht1, ht2⟩
        · cases t with
          | cons t0 t' =>
              exfalso
              obtain ⟨rfl, -⟩ := List.cons.inj ht2
              have hmem : (AVal.code lRet) ∈ AVal.word wv :: τ := by
                rw [ht1]; exact List.mem_append_right _ (by simp)
              rcases List.mem_cons.mp hmem with hh | hh
              · exact absurd hh (by simp)
              · obtain ⟨v, hv⟩ := hτw _ hh; exact absurd hv (by simp)
          | nil =>
              rw [List.append_nil] at ht1
              rw [List.nil_append] at ht2
              obtain ⟨hy, hbe⟩ := List.cons.inj ht2
              exact leafNil (hsyret ht1.symm) hy.symm hbe
        · cases t with
          | nil =>
              rw [List.append_nil] at ht1
              rw [List.nil_append] at ht2
              obtain ⟨hy, hbe⟩ := List.cons.inj ht2
              exact leafNil (hsyret ht1) hy hbe.symm
          | cons t0 t' =>
              rw [List.cons_append] at ht2
              obtain ⟨rfl, rfl⟩ := List.cons.inj ht2
              refine .call (above := y :: (τ ++ AVal.word wv :: t')) (below := below) (lRet := lRet)
                h1 (by rw [hfb, hfb0]) (by rw [hrl, hrl0]) ?_ ?_ hbw hfind hle hres (by simp)
              · have he : (y :: (τ ++ AVal.word wv :: t')) ++ AVal.code lRet :: below
                    = y :: (τ ++ AVal.word wv :: (t' ++ AVal.code lRet :: below)) := by simp
                rw [he]; exact hMnew
              · have hkey : Sρ[t'.length]? = some FSlot.ret := by
                  have h := hact
                  rw [ht1, show ((AVal.word wv :: τ) ++ (y :: t')).length
                        = Sτ.length + 1 + t'.length + 1 from by
                          simp only [List.length_append, List.length_cons]; omega,
                      List.getElem?_cons_succ, List.getElem?_append_right (by omega),
                      show Sτ.length + 1 + t'.length - Sτ.length = t'.length + 1 from by omega,
                      List.getElem?_cons_succ] at h
                  exact h
                rw [show (y :: (τ ++ AVal.word wv :: t')).length = Sτ.length + 1 + t'.length + 1
                      from by simp only [List.length_append, List.length_cons]; omega,
                    List.getElem?_cons_succ, List.getElem?_append_right (by omega),
                    show Sτ.length + 1 + t'.length - Sτ.length = t'.length + 1 from by omega,
                    List.getElem?_cons_succ]
                exact hkey

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
  | @pushImmutable key v c σ yst _ =>
      obtain ⟨S, F, R, hfl, hfb, hrl⟩ := hinv.certAt
      obtain ⟨hflc, hfbc, hrlc⟩ := hV _ c S F R hfl hfb hrl
      exact hinv.growWord hfl hflc (by rw [hfbc, hfb]) (by rw [hrlc, hrl])
  | @pushLabel l c σ yst hdef =>
      obtain ⟨S, F, R, hfl, hfb, hrl⟩ := hinv.certAt
      obtain ⟨hflc, hfbc, hrlc⟩ := hV _ c S F R hfl hfb hrl
      exact hinv.growRetTo hfl hflc (by rw [hfbc, hfb]) (by rw [hrlc, hrl])
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
      | inr hcall =>
          obtain ⟨Sw, Smid, Lret, cc, t, Sret, hfindt, hc, hSeq, hSwords, hflt, hfbt, hrlt,
            hSretw, hfindLret, hflcc, hfbcc, hrlcc⟩ := hcall
          obtain ⟨Ft, hfbtEq, hFtGe⟩ := hfbt
          obtain rfl : t = c' := Option.some.inj (hfindt.symm.trans hfind)
          cases hinv with
          | @root σr cr Sr Rr hflr hfbr hrlr hnoretr hmr =>
              obtain rfl : Sr = S := Option.some.inj (hflr.symm.trans hfl)
              obtain rfl : (0 : Nat) = F := Option.some.inj (hfbr.symm.trans hfb)
              rw [hSeq] at hmr
              obtain ⟨fp, midframe, hσeq, hMfp, hMmid⟩ := hmr.append_inv_layout
              obtain ⟨setupW, setupR, rfl, hMsw, hMsr⟩ := hMfp.append_inv_layout
              obtain ⟨lc, e, rfl, hMlc, hMe⟩ := hMsr.cons_inv'
              cases hMe
              cases hMlc with
              | retTo _ =>
                  refine GoodStack.call (above := setupW) (below := []) (lRet := Lret)
                    (rest := midframe) (cRet := cc) hflt hfbtEq hrlt (hMsw.append (FMatch.ret FMatch.nil))
                    (by rw [hMsw.length_eq, List.getElem?_append_right (le_refl _), Nat.sub_self]; rfl)
                    (by intro x hx; simp at hx) hfindLret
                    (by rw [hMmid.length_eq]; omega) ?_ ?_
                  · intro ws hws
                    have hnSret : NoRet Sret := fun s hs => by rw [hSretw s hs]; simp
                    have hnSmid : NoRet Smid := fun s hs =>
                      hnoretr s (by rw [hSeq]; exact List.mem_append_right _ hs)
                    exact GoodStack.root hflcc hfbcc hrlcc (NoRet.append hnSret hnSmid) (hws.append hMmid)
                  · exact hσeq
          | @call stk0 above0 below0 rest0 c0 cRet0 S0 Sret0 F0 lRet0 hfl0 hfb0 hrl0 hm0 hact0 hbw0
              hfind0 hle0 hres0 heq0 =>
              obtain rfl : S0 = S := Option.some.inj (hfl0.symm.trans hfl)
              obtain rfl : F0 = F := Option.some.inj (hfb0.symm.trans hfb)
              obtain rfl : Sret0 = R := Option.some.inj (hrl0.symm.trans hrl)
              -- split the caller frame by the setup layout
              rw [hSeq] at hm0
              obtain ⟨fp, midframe, hfeq, hMfp, hMmid⟩ := hm0.append_inv_layout
              obtain ⟨setupW, setupR, rfl, hMsw, hMsr⟩ := hMfp.append_inv_layout
              obtain ⟨lc, e, rfl, hMlc, hMe⟩ := hMsr.cons_inv'
              cases hMe
              cases hMlc with
              | retTo _ =>
                  have hsetlen : setupW.length = Sw.length := hMsw.length_eq
                  -- `hact0` puts the caller's own return `.ret` strictly below the setup slot.
                  have hSflat : (Sw ++ [FSlot.retTo Lret]) ++ Smid = Sw ++ (FSlot.retTo Lret :: Smid) := by
                    simp
                  have hge : setupW.length + 1 ≤ above0.length := by
                    by_contra hlt
                    rw [Nat.not_le, hsetlen] at hlt
                    have h := hact0
                    rw [hSeq, hSflat] at h
                    rcases Nat.lt_or_ge above0.length Sw.length with hlt2 | hge2
                    · rw [List.getElem?_append_left hlt2, List.getElem?_eq_getElem hlt2,
                          hSwords _ (List.getElem_mem hlt2)] at h
                      exact absurd h (by simp)
                    · have heq2 : above0.length = Sw.length := by omega
                      rw [heq2, List.getElem?_append_right (le_refl _), Nat.sub_self,
                          List.getElem?_cons_zero] at h
                      exact absurd h (by simp)
                  obtain ⟨midAbove, hmidA⟩ :
                      ∃ midAbove, midframe = midAbove ++ AVal.code lRet0 :: below0 := by
                    rcases List.append_eq_append_iff.mp hfeq with ⟨e, he1, he2⟩ | ⟨e, he1, he2⟩
                    · have hlen : setupW.length + 1 = above0.length + e.length := by
                        have := congrArg List.length he1; simpa using this
                      have he0 : e = [] := List.eq_nil_of_length_eq_zero (by omega)
                      subst he0; rw [List.nil_append] at he2
                      exact ⟨[], by rw [List.nil_append, he2]⟩
                    · exact ⟨e, he2⟩
                  have hlen0 : above0.length = setupW.length + 1 + midAbove.length := by
                    have e1 := congrArg List.length hfeq
                    rw [hmidA] at e1
                    simp only [List.length_append, List.length_cons, List.length_nil] at e1
                    omega
                  have habove0 : above0 = (setupW ++ [AVal.code Lret]) ++ midAbove := by
                    have hh := hfeq; rw [hmidA, ← List.append_assoc] at hh
                    refine (List.append_inj hh ?_).1
                    simp only [List.length_append, List.length_cons, List.length_nil]; omega
                  refine GoodStack.call (above := setupW) (below := []) (lRet := Lret)
                    (rest := midframe ++ rest0) (cRet := cc) hflt hfbtEq hrlt
                    (hMsw.append (FMatch.ret FMatch.nil))
                    (by rw [hMsw.length_eq, List.getElem?_append_right (le_refl _), Nat.sub_self]; rfl)
                    (by intro x hx; simp at hx) hfindLret
                    (by rw [List.length_append, hMmid.length_eq]; omega) ?_ ?_ -- hle: |midframe|+|rest0| ≤ Ft
                  · intro ws hws
                    refine GoodStack.call (above := ws ++ midAbove) (below := below0) (lRet := lRet0)
                      (rest := rest0) (cRet := cRet0) hflcc hfbcc hrlcc ?_ ?_ hbw0 hfind0 hle0 hres0 ?_
                    · have hfe : (ws ++ midAbove) ++ AVal.code lRet0 :: below0 = ws ++ midframe := by
                        rw [hmidA]; simp [List.append_assoc]
                      rw [hfe]; exact hws.append hMmid
                    · rw [List.length_append, hws.length_eq, List.getElem?_append_right (by omega),
                          show Sret.length + midAbove.length - Sret.length = midAbove.length from by omega]
                      have h := hact0
                      rw [hSeq, hSflat, show above0.length = Sw.length + 1 + midAbove.length from by
                            rw [hlen0, hsetlen],
                          List.getElem?_append_right (by omega),
                          show Sw.length + 1 + midAbove.length - Sw.length = midAbove.length + 1
                            from by omega, List.getElem?_cons_succ] at h
                      exact h
                    · rw [hmidA]; simp [List.append_assoc]
                  · rw [heq0, hfeq]; simp [List.append_assoc]
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
      obtain ⟨hidx, hflc, hfbc, hrlc⟩ := hV _ c S F R hfl hfb hrl
      have hvidx : (τ ++ v :: ρ)[n.val]? = some v := by
        rw [← hτ, List.getElem?_append_right (Nat.le_refl _)]; simp
      have hsm : FMatch [v] [FSlot.word] := hinv.slotAt hfl hvidx hidx
      cases hsm with
      | word _ => exact hinv.growWord hfl hflc (by rw [hfbc, hfb]) (by rw [hrlc, hrl])
  | @swap n x y τ ρ c yst hτ =>
      obtain ⟨S, F, R, hfl, hfb, hrl⟩ := hinv.certAt
      obtain ⟨sx, mid, sy, rst, hSeq, hmidlen, hsxw, hmidw, hflc, hfbc, hrlc⟩ :=
        hV _ c S F R hfl hfb hrl
      subst hSeq
      have hτlen : mid.length = τ.length := by rw [hmidlen, hτ]
      exact hinv.swapFrame hfl hsxw hmidw hτlen hflc (by rw [hfbc, hfb]) (by rw [hrlc, hrl])
  | @dynJump l c c' σ yst hfind =>
      obtain ⟨S, F, R, hfl, hfb, hrl⟩ := hinv.certAt
      obtain ⟨S', hSeq, hRS', hwords⟩ := hV _ c S F R hfl hfb hrl
      cases hinv with
      | @root σ0 c0 S0 R0 hfl0 hfb0 hrl0 hnoret hm =>
          obtain rfl : S0 = S := Option.some.inj (hfl0.symm.trans hfl)
          rw [hSeq] at hnoret
          exact absurd rfl (hnoret FSlot.ret (by simp))
      | @call stk above below rest c0 cRet S0 Sret F0 lRet hfl0 hfb0 hrl0 hm hact hbw hfind0 hle hres heq =>
          obtain rfl : S = S0 := Option.some.inj (hfl.symm.trans hfl0)
          have hSretS' : Sret = S' := by
            have h1 : Sret = R := Option.some.inj (hrl0.symm.trans hrl); rw [h1, hRS']
          rw [hSretS'] at hres
          rw [hSeq] at hm
          -- The frame's deepest code cell is `lRet`; at dynJump the layout is `.ret :: words`, so
          -- `above` must be empty (any code in `above` would need a word slot below the ret).
          cases above with
          | cons a above' =>
              rw [List.cons_append] at hm
              cases hm with
              | @ret la σ'' _ hm' =>
                  obtain ⟨w, hw⟩ := hm'.allWord hwords (.code lRet)
                    (List.mem_append_right _ (by simp))
                  exact absurd hw (by simp)
          | nil =>
              rw [List.nil_append, List.cons_append] at heq
              rw [List.nil_append] at hm
              cases hm with
              | @ret la σ'' _ hm' =>
                  obtain ⟨hcq, rfl⟩ := List.cons.inj heq
                  obtain rfl := AVal.code.inj hcq
                  rw [hfind] at hfind0; obtain rfl := Option.some.inj hfind0
                  exact hres below hm'

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

/-! ### A decidable, linear verifier for `Cert.Valid` and `Cert.Bounded`

The certificate (`fl`/`fbMax`/`rl`) is proposed by an *untrusted* solver; soundness rests only on the
verifier below, so a wrong proposal is simply rejected. Every position carries a **single** layout,
so the check is one pass over the certificate's finite domain — linear. -/

/-- Split `S` at the first `retTo Lret`, returning the (words) prefix and the suffix. -/
def splitSetup (Lret : Label) : FLayout → Option (FLayout × FLayout)
  | [] => none
  | s :: rest =>
      if s = FSlot.retTo Lret then some ([], rest)
      else match splitSetup Lret rest with
           | some (Sw, Smid) => some (s :: Sw, Smid)
           | none => none

omit model in
theorem splitSetup_sound {Lret : Label} : ∀ {S Sw Smid : FLayout},
    splitSetup Lret S = some (Sw, Smid) → S = Sw ++ FSlot.retTo Lret :: Smid := by
  intro S
  induction S with
  | nil => intro Sw Smid h; simp [splitSetup] at h
  | cons s rest ih =>
      intro Sw Smid h
      simp only [splitSetup] at h
      split at h
      · next hs => rw [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rw [hs]; rfl
      · next hs =>
          revert h; split
          · next Sw' Smid' hsp =>
              intro h; rw [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
              rw [List.cons_append]; congr 1; exact ih hsp
          · intro h; simp at h

/-- Decidable mirror of `frameStep` (each branch is a single `decide` of the right-nested
conjunction, so soundness is a projection). -/
def frameStepB (prog : List Asm) (C : Cert) : Asm → List Asm → FLayout → Nat → FLayout → Bool
  | .push _,      c, S, F, R =>
      decide (C.fl c = some (.word :: S) ∧ C.fbMax c = some F ∧ C.rl c = some R)
  | .pushImmutable _ _, c, S, F, R =>
      decide (C.fl c = some (.word :: S) ∧ C.fbMax c = some F ∧ C.rl c = some R)
  | .dup n,       c, S, F, R => match S[n.val]? with
      | some FSlot.word => decide (C.fl c = some (.word :: S) ∧ C.fbMax c = some F ∧ C.rl c = some R)
      | _ => false
  | .pushLabel l, c, S, F, R =>
      decide (C.fl c = some (.retTo l :: S) ∧ C.fbMax c = some F ∧ C.rl c = some R)
  | .pop,         c, S, F, R => match S with
      | .word :: S' => decide (C.fl c = some S' ∧ C.fbMax c = some F ∧ C.rl c = some R)
      | _ => false
  | .swap n,      c, S, F, R => match S with
      | sx :: rest => match rest.drop n.val with
          | sy :: rst => decide (sx = FSlot.word ∧ (∀ s ∈ rest.take n.val, s = FSlot.word) ∧
              C.fl c = some (sy :: (rest.take n.val ++ sx :: rst)) ∧ C.fbMax c = some F ∧ C.rl c = some R)
          | [] => false
      | [] => false
  | .label _,     c, S, F, R => decide (C.fl c = some S ∧ C.fbMax c = some F ∧ C.rl c = some R)
  | .op yop,      c, S, F, R => match opTable yop with
      | some o => decide (Operation.popArity o ≤ S.length ∧
          C.fl c = some (List.replicate (Operation.pushArity o) FSlot.word ++ S.drop (Operation.popArity o))
          ∧ C.fbMax c = some F ∧ C.rl c = some R)
      | none => false
  | .jump l,      c, S, F, R =>
      (match findLabel l prog with
       | some t => decide (C.fl t = some S ∧ C.fbMax t = some F ∧ C.rl t = some R)
       | none => false)
      || (match c with
          | .label Lret :: c' =>
              (match findLabel l prog with
               | some t =>
                   (match splitSetup Lret S with
                    | some (Sw, Smid) =>
                        (match C.fbMax t, C.rl t with
                         | some Ft, some Sret =>
                             decide (findLabel Lret prog = some c' ∧ (∀ s ∈ Sw, s = FSlot.word) ∧
                               C.fl t = some (Sw ++ [FSlot.ret]) ∧ F + Smid.length ≤ Ft ∧
                               (∀ s ∈ Sret, s = FSlot.word) ∧ C.fl c' = some (Sret ++ Smid) ∧
                               C.fbMax c' = some F ∧ C.rl c' = some R)
                         | _, _ => false)
                    | none => false)
               | none => false)
          | _ => false)
  | .jumpi l,     c, S, F, R => match S with
      | .word :: S' =>
          (match findLabel l prog with
           | some t => decide (C.fl t = some S' ∧ C.fbMax t = some F ∧ C.rl t = some R)
           | none => false)
          && decide (C.fl c = some S' ∧ C.fbMax c = some F ∧ C.rl c = some R)
      | _ => false
  | .dynJump,     _, S, _F, R => match S with
      | .ret :: S' => decide (R = S' ∧ (∀ s ∈ S', s = FSlot.word))
      | _ => false

omit model in
set_option linter.unusedTactic false in
/-- `frameStepB` soundly implies `frameStep`. -/
theorem frameStepB_sound {prog : List Asm} {C : Cert} {i : Asm} {c : List Asm} {S : FLayout}
    {F : Nat} {R : FLayout} (h : frameStepB prog C i c S F R = true) : frameStep prog C i c S F R := by
  cases i with
  | push v => simp only [frameStepB, decide_eq_true_eq] at h; exact h
  | pushImmutable key v => simp only [frameStepB, decide_eq_true_eq] at h; exact h
  | dup n =>
      revert h; simp only [frameStepB]; split
      · next he => intro h; simp only [decide_eq_true_eq] at h; exact ⟨he, h⟩
      · intro h; exact absurd h (by simp)
  | pushLabel l => simp only [frameStepB, decide_eq_true_eq] at h; exact h
  | pop =>
      revert h; simp only [frameStepB]; split
      · next S' => intro h; simp only [decide_eq_true_eq] at h; exact ⟨S', rfl, h⟩
      · intro h; simp at h
  | swap n =>
      revert h; simp only [frameStepB]; split
      · next sx rest =>
          split
          · next sy rst hd =>
              intro h; simp only [decide_eq_true_eq] at h
              refine ⟨sx, rest.take n.val, sy, rst, ?_, ?_, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
              · rw [← hd, List.take_append_drop]
              · have hh : (rest.drop n.val).length = rest.length - n.val := by simp
                rw [hd] at hh; simp only [List.length_cons] at hh
                simp only [List.length_take]; omega
          · intro h; simp at h
      · intro h; simp at h
  | label l => simp only [frameStepB, decide_eq_true_eq] at h; exact h
  | op yop =>
      revert h; simp only [frameStepB]; split
      · next o he => intro h; simp only [decide_eq_true_eq] at h; exact ⟨o, he, h.1, h.2.1, h.2.2.1, h.2.2.2⟩
      · intro h; simp at h
  | jump l =>
      revert h; simp only [frameStepB]; intro h; rw [Bool.or_eq_true] at h
      cases h with
      | inl h =>
          left; revert h; split
          · next t he => intro h; simp only [decide_eq_true_eq] at h; exact ⟨t, he, h⟩
          · intro h; simp at h
      | inr h =>
          right; revert h; split
          · next Lret c' =>
              split
              · next t he =>
                  split
                  · next Sw Smid hsp =>
                      split
                      · next Ft Sret hfbtM hrltM =>
                          intro h; simp only [decide_eq_true_eq] at h
                          obtain ⟨hFL, hSw, hflt, hle, hSret, hflc, hfbc, hrlc⟩ := h
                          exact ⟨Sw, Smid, Lret, c', t, Sret, he, rfl,
                            (by rw [List.append_assoc]; exact splitSetup_sound hsp), hSw,
                            hflt, ⟨Ft, hfbtM, hle⟩, hrltM, hSret, hFL, hflc, hfbc, hrlc⟩
                      · intro h; simp at h
                  · intro h; simp at h
              · intro h; simp at h
          · intro h; simp at h
  | jumpi l =>
      revert h; simp only [frameStepB]; split
      · next S' =>
          intro h; rw [Bool.and_eq_true] at h; obtain ⟨h1, h2⟩ := h
          simp only [decide_eq_true_eq] at h2
          refine ⟨S', rfl, ?_, h2.1, h2.2.1, h2.2.2⟩
          revert h1; split
          · next t he => intro h1; simp only [decide_eq_true_eq] at h1; exact ⟨t, he, h1⟩
          · intro h1; simp at h1
      · intro h; simp at h
  | dynJump =>
      revert h; simp only [frameStepB]; split
      · next S' => intro h; simp only [decide_eq_true_eq] at h; exact ⟨S', rfl, h.1, h.2⟩
      · intro h; simp at h

/-- Equality of two certificate positions, with a pointer-equality fast path.

`withPtrEq a b k h` is *definitionally* `k ()` — the fast path exists only in
the compiled code, and `h` is the obligation that it agrees. So this is
`decide (a = b)` by `rfl`, with no new axiom and no `implemented_by` of our own
(`withPtrEq` is Lean core's).

It matters because the positions a certificate stores are the very suffixes of
`prog` that produced them, so they are *physically shared* with the position
being looked up: the pointer check succeeds immediately where the structural
comparison would walk the whole suffix. Structural `List Asm` equality was 37%
of all instructions in a profile of a mid-sized fixture. -/
def posEq (a b : List Asm) : Bool :=
  withPtrEq a b (fun _ => decide (a = b)) (fun h => by simp [h])

omit model in
@[simp] theorem posEq_eq_decide (a b : List Asm) :
    posEq a b = decide (a = b) := rfl

/-- `Option`-lifted `posEq`. The pointer check has to happen on the *lists*: the
`some c'` wrapper the verifier compares against is freshly allocated, so a
pointer test on the `Option` itself would always miss. -/
def posEqOpt (a b : Option (List Asm)) : Bool :=
  match a, b with
  | some x, some y => posEq x y
  | none, none => true
  | _, _ => false

omit model in
@[simp] theorem posEqOpt_eq_decide (a b : Option (List Asm)) :
    posEqOpt a b = decide (a = b) := by
  cases a <;> cases b <;> simp [posEqOpt]

/-- All certificate facts for one program position, returned together. -/
abbrev CertValue := FLayout × Nat × FLayout

/-- Bundled executable certificate lookup. -/
abbrev CertLookup := List Asm → Option CertValue

/-- The entry type stored in the key-indexed table. -/
abbrev CertEntry := Nat × List Asm × FLayout × Nat × FLayout

/-- Certificate lookup against an already-built table.

`CertLookup` is a function type, so a definition of the form
`let t := …; fun c => … t …` is eta-expanded by the compiler to arity 2 and the
`let` is floated *inside* the lambda: the table would then be reallocated and
refolded on **every** lookup, making the verifier quadratic in the program
length with an O(program) array allocation per lookup. Taking the table as a
parameter is what keeps it shared; `checkCertFast` binds it once. -/
def lookupIn (t : Array (Option CertEntry)) : CertLookup :=
  fun c => match t[c.length]? with
    | some (some e) =>
        if e.2.1 = c then some (e.2.2.1, e.2.2.2.1, e.2.2.2.2) else none
    | _ => none

/-- `lookupIn` with the pointer-equality fast path on the position comparison,
installed into compiled code by `@[csimp]` below. -/
def lookupInFast (t : Array (Option CertEntry)) : CertLookup :=
  fun c => match t[c.length]? with
    | some (some e) =>
        if posEq e.2.1 c then some (e.2.2.1, e.2.2.2.1, e.2.2.2.2) else none
    | _ => none

omit model in
@[csimp] theorem lookupIn_eq_lookupInFast : @lookupIn = @lookupInFast := by
  funext t c
  simp only [lookupIn, lookupInFast, posEq_eq_decide, decide_eq_true_eq]

/-! ### Looking up by index instead of by length

`lookupIn t c` uses `c.length` as the table index, and `c` is a suffix of the
program, so every lookup walks it: `List.length` was 18.7% of a compile on a
mid-sized fixture and 34.9% on the largest. The verifier performs one to three
lookups per entry and there is roughly one entry per instruction, so this is the
last quadratic in the gate.

The lengths are all *derivable* without walking — a fall-through successor is one
shorter than the position it came from, and a jump target's length can be
tabulated with the target itself. What is missing is the length of the position an
entry *stores*, which a hostile table need not report honestly in `e.1`.

`suffixArr` supplies it: cell `k` holds the length-`k` suffix of the program, so
`posEq (suffixArr prog)[e.1]! e.2.1` — O(1) by pointer for a certificate our own
solver produced — *proves* `e.2.1.length = e.1`. When it fails, the entry falls
back to the length-computing path, so acceptance is unchanged either way. -/

/-- Certificate lookup at an explicit index. Equal to `lookupIn t c` exactly when
`k` is `c`'s length (`lookupAt_length`). -/
def lookupAt (t : Array (Option CertEntry)) (k : Nat) (c : List Asm) :
    Option CertValue :=
  match t[k]? with
  | some (some e) =>
      if posEq e.2.1 c then some (e.2.2.1, e.2.2.2.1, e.2.2.2.2) else none
  | _ => none

omit model in
theorem lookupAt_length (t : Array (Option CertEntry)) (c : List Asm) :
    lookupAt t c.length c = lookupIn t c := by
  simp only [lookupAt, lookupIn, posEq_eq_decide, decide_eq_true_eq]

/-- Every suffix of `p`, longest first, appended to `acc`. Pointers are shared
with `p` — nothing is rebuilt — which is what makes the `posEq` check below O(1).
-/
def suffixesGo : List Asm → Array (List Asm) → Array (List Asm)
  | [], acc => acc.push []
  | p@(_ :: rest), acc => suffixesGo rest (acc.push p)

/-- Suffixes of `prog`, longest first: cell `i` is `prog.drop i`, so the suffix of
length `k` sits at index `prog.length - k`. -/
def suffixes (prog : List Asm) : Array (List Asm) := suffixesGo prog #[]

omit model in
private theorem suffixesGo_getElem? (p : List Asm) :
    ∀ (acc : Array (List Asm)) (i : Nat),
      (suffixesGo p acc)[i]? =
        if i < acc.size then acc[i]?
        else if i ≤ acc.size + p.length then some (p.drop (i - acc.size)) else none := by
  induction p with
  | nil =>
      intro acc i
      rw [suffixesGo, Array.getElem?_push]
      rcases Nat.lt_trichotomy i acc.size with h | h | h
      · simp [show i ≠ acc.size by omega, h]
      · subst h; simp
      · simp [show i ≠ acc.size by omega, show ¬ i < acc.size by omega,
          show ¬ i ≤ acc.size by omega]
  | cons i₀ rest ih =>
      intro acc i
      rw [suffixesGo, ih]
      simp only [Array.size_push, List.length_cons]
      rcases Nat.lt_trichotomy i acc.size with h | h | h
      · rw [if_pos (show i < acc.size + 1 by omega), if_pos h,
          Array.getElem?_push_lt h, Array.getElem?_eq_getElem h]
      · subst h
        simp
      · have hdrop : (i₀ :: rest).drop (i - acc.size) = rest.drop (i - (acc.size + 1)) := by
          have h1 : i - acc.size = (i - (acc.size + 1)) + 1 := by omega
          rw [h1, List.drop_succ_cons]
        by_cases hle : i ≤ acc.size + 1 + rest.length
        · simp [show ¬ i < acc.size + 1 by omega, show ¬ i < acc.size by omega,
            hle, show i ≤ acc.size + (rest.length + 1) by omega, hdrop]
        · simp [show ¬ i < acc.size + 1 by omega, show ¬ i < acc.size by omega,
            hle, show ¬ i ≤ acc.size + (rest.length + 1) by omega]

omit model in
/-- Cell `i` of `suffixes prog` is `prog.drop i`. -/
theorem suffixes_getElem? (prog : List Asm) (i : Nat) (h : i ≤ prog.length) :
    (suffixes prog)[i]? = some (prog.drop i) := by
  rw [suffixes, suffixesGo_getElem?]
  simp [Nat.not_lt.mpr (Nat.zero_le i), h]

omit model in
/-- …hence it has length `prog.length - i`. This is the fact that turns a
successful `posEq` into a proof about a stored position's length. -/
theorem suffixes_length (prog : List Asm) (i : Nat) (h : i ≤ prog.length)
    (c : List Asm) (hc : (suffixes prog)[i]? = some c) :
    c.length = prog.length - i := by
  rw [suffixes_getElem? prog i h] at hc
  rw [← Option.some.inj hc]
  simp

/-- `frameStepB` with a bundled certificate API. Each successor position is
looked up once instead of independently through `fl`, `fbMax`, and `rl`. -/
def frameStepLookupB (prog : List Asm) (lookup : CertLookup) :
    Asm → List Asm → FLayout → Nat → FLayout → Bool
  | .push _,      c, S, F, R => decide (lookup c = some (.word :: S, F, R))
  | .pushImmutable _ _, c, S, F, R => decide (lookup c = some (.word :: S, F, R))
  | .dup n,       c, S, F, R => match S[n.val]? with
      | some FSlot.word => decide (lookup c = some (.word :: S, F, R))
      | _ => false
  | .pushLabel l, c, S, F, R => decide (lookup c = some (.retTo l :: S, F, R))
  | .pop,         c, S, F, R => match S with
      | .word :: S' => decide (lookup c = some (S', F, R))
      | _ => false
  | .swap n,      c, S, F, R => match S with
      | sx :: rest => match rest.drop n.val with
          | sy :: rst => decide (sx = FSlot.word ∧
              (∀ s ∈ rest.take n.val, s = FSlot.word) ∧
              lookup c = some (sy :: (rest.take n.val ++ sx :: rst), F, R))
          | [] => false
      | [] => false
  | .label _,     c, S, F, R => decide (lookup c = some (S, F, R))
  | .op yop,      c, S, F, R => match opTable yop with
      | some o => decide (Operation.popArity o ≤ S.length ∧
          lookup c = some
            (List.replicate (Operation.pushArity o) FSlot.word ++
              S.drop (Operation.popArity o), F, R))
      | none => false
  | .jump l,      c, S, F, R =>
      (match findLabel l prog with
       | some t => decide (lookup t = some (S, F, R))
       | none => false)
      || (match c with
          | .label Lret :: c' =>
              (match findLabel l prog with
               | some t =>
                   (match splitSetup Lret S with
                    | some (Sw, Smid) =>
                        (match lookup t with
                         | some (St, Ft, Sret) =>
                             decide (findLabel Lret prog = some c' ∧
                               (∀ s ∈ Sw, s = FSlot.word) ∧
                               St = Sw ++ [FSlot.ret] ∧ F + Smid.length ≤ Ft ∧
                               (∀ s ∈ Sret, s = FSlot.word) ∧
                               lookup c' = some (Sret ++ Smid, F, R))
                         | none => false)
                    | none => false)
               | none => false)
          | _ => false)
  | .jumpi l,     c, S, F, R => match S with
      | .word :: S' =>
          (match findLabel l prog with
           | some t => decide (lookup t = some (S', F, R))
           | none => false)
          && decide (lookup c = some (S', F, R))
      | _ => false
  | .dynJump,     _, S, _F, R => match S with
      | .ret :: S' => decide (R = S' ∧ (∀ s ∈ S', s = FSlot.word))
      | _ => false

/-- Intermediate step relation, proved equal to `frameStepLookupB` by
`frameStepLookupFastB_eq_frameStepLookupB`. Nothing calls this at run time any
more — `frameStepLookupIdxB` is what `checkCertWith` runs — but keeping it splits
the equality proof along the two independent changes it represents.

Two changes, both of them the same idea — stop walking the program for something
that is already known:

* jump targets come from a precomputed table rather than a `findLabel l prog`
  scan per jump;
* the return-continuation conjunct compares the table's entry for the return
  label against the actual continuation with `posEqOpt`. Those two are
  physically-shared suffixes of the program, so the structural comparison walked
  the whole suffix once per call site — 22% of all instructions on the largest
  fixture. -/
def frameStepLookupFastB (tgts : Std.HashMap Label (List Asm))
    (lookup : CertLookup) :
    Asm → List Asm → FLayout → Nat → FLayout → Bool
  | .push _,      c, S, F, R => decide (lookup c = some (.word :: S, F, R))
  | .pushImmutable _ _, c, S, F, R => decide (lookup c = some (.word :: S, F, R))
  | .dup n,       c, S, F, R => match S[n.val]? with
      | some FSlot.word => decide (lookup c = some (.word :: S, F, R))
      | _ => false
  | .pushLabel l, c, S, F, R => decide (lookup c = some (.retTo l :: S, F, R))
  | .pop,         c, S, F, R => match S with
      | .word :: S' => decide (lookup c = some (S', F, R))
      | _ => false
  | .swap n,      c, S, F, R => match S with
      | sx :: rest => match rest.drop n.val with
          | sy :: rst => decide (sx = FSlot.word ∧
              (∀ s ∈ rest.take n.val, s = FSlot.word) ∧
              lookup c = some (sy :: (rest.take n.val ++ sx :: rst), F, R))
          | [] => false
      | [] => false
  | .label _,     c, S, F, R => decide (lookup c = some (S, F, R))
  | .op yop,      c, S, F, R => match opTable yop with
      | some o => decide (Operation.popArity o ≤ S.length ∧
          lookup c = some
            (List.replicate (Operation.pushArity o) FSlot.word ++
              S.drop (Operation.popArity o), F, R))
      | none => false
  | .jump l,      c, S, F, R =>
      (match tgts[l]? with
       | some t => decide (lookup t = some (S, F, R))
       | none => false)
      || (match c with
          | .label Lret :: c' =>
              (match tgts[l]? with
               | some t =>
                   (match splitSetup Lret S with
                    | some (Sw, Smid) =>
                        (match lookup t with
                         | some (St, Ft, Sret) =>
                             posEqOpt tgts[Lret]? (some c') &&
                             decide ((∀ s ∈ Sw, s = FSlot.word) ∧
                               St = Sw ++ [FSlot.ret] ∧ F + Smid.length ≤ Ft ∧
                               (∀ s ∈ Sret, s = FSlot.word) ∧
                               lookup c' = some (Sret ++ Smid, F, R))
                         | none => false)
                    | none => false)
               | none => false)
          | _ => false)
  | .jumpi l,     c, S, F, R => match S with
      | .word :: S' =>
          (match tgts[l]? with
           | some t => decide (lookup t = some (S', F, R))
           | none => false)
          && decide (lookup c = some (S', F, R))
      | _ => false
  | .dynJump,     _, S, _F, R => match S with
      | .ret :: S' => decide (R = S' ∧ (∀ s ∈ S', s = FSlot.word))
      | _ => false




/-- `frameStepLookupFastB` with the fall-through successor looked up by **index**
instead of by length.

`kc` must be `c`'s length, which the caller knows without walking: `checkCertWith`
establishes it for the position an entry stores, and the continuation after a
return label is one shorter. Jump *targets* still resolve by length — they are a
small minority of instructions, and tabulating their lengths would need a second
map and its own accumulator proof. -/
def frameStepLookupIdxB (tgts : Std.HashMap Label (List Asm))
    (lookup : CertLookup) (tbl : Array (Option CertEntry)) (kc : Nat) :
    Asm → List Asm → FLayout → Nat → FLayout → Bool
  | .push _,      c, S, F, R => decide (lookupAt tbl kc c = some (.word :: S, F, R))
  | .pushImmutable _ _, c, S, F, R =>
      decide (lookupAt tbl kc c = some (.word :: S, F, R))
  | .dup n,       c, S, F, R => match S[n.val]? with
      | some FSlot.word => decide (lookupAt tbl kc c = some (.word :: S, F, R))
      | _ => false
  | .pushLabel l, c, S, F, R => decide (lookupAt tbl kc c = some (.retTo l :: S, F, R))
  | .pop,         c, S, F, R => match S with
      | .word :: S' => decide (lookupAt tbl kc c = some (S', F, R))
      | _ => false
  | .swap n,      c, S, F, R => match S with
      | sx :: rest => match rest.drop n.val with
          | sy :: rst => decide (sx = FSlot.word ∧
              (∀ s ∈ rest.take n.val, s = FSlot.word) ∧
              lookupAt tbl kc c = some (sy :: (rest.take n.val ++ sx :: rst), F, R))
          | [] => false
      | [] => false
  | .label _,     c, S, F, R => decide (lookupAt tbl kc c = some (S, F, R))
  | .op yop,      c, S, F, R => match opTable yop with
      | some o => decide (Operation.popArity o ≤ S.length ∧
          lookupAt tbl kc c = some
            (List.replicate (Operation.pushArity o) FSlot.word ++
              S.drop (Operation.popArity o), F, R))
      | none => false
  | .jump l,      c, S, F, R =>
      (match tgts[l]? with
       | some t => decide (lookup t = some (S, F, R))
       | none => false)
      || (match c with
          | .label Lret :: c' =>
              (match tgts[l]? with
               | some t =>
                   (match splitSetup Lret S with
                    | some (Sw, Smid) =>
                        (match lookup t with
                         | some (St, Ft, Sret) =>
                             posEqOpt tgts[Lret]? (some c') &&
                             decide ((∀ s ∈ Sw, s = FSlot.word) ∧
                               St = Sw ++ [FSlot.ret] ∧ F + Smid.length ≤ Ft ∧
                               (∀ s ∈ Sret, s = FSlot.word) ∧
                               lookupAt tbl (kc - 1) c' = some (Sret ++ Smid, F, R))
                         | none => false)
                    | none => false)
               | none => false)
          | _ => false)
  | .jumpi l,     c, S, F, R => match S with
      | .word :: S' =>
          (match tgts[l]? with
           | some t => decide (lookup t = some (S', F, R))
           | none => false)
          && decide (lookupAt tbl kc c = some (S', F, R))
      | _ => false
  | .dynJump,     _, S, _F, R => match S with
      | .ret :: S' => decide (R = S' ∧ (∀ s ∈ S', s = FSlot.word))
      | _ => false





omit model in
/-- Supplying the fall-through successor's index changes nothing, provided the
index really is its length. -/
theorem frameStepLookupIdxB_eq_frameStepLookupFastB
    (tgts : Std.HashMap Label (List Asm)) (tbl : Array (Option CertEntry))
    (kc : Nat) (i : Asm) (c : List Asm) (S : FLayout) (F : Nat) (R : FLayout)
    (hk : kc = c.length) :
    frameStepLookupIdxB tgts (lookupIn tbl) tbl kc i c S F R =
      frameStepLookupFastB tgts (lookupIn tbl) i c S F R := by
  subst hk
  cases i with
  | jump l =>
      -- The only case with a second, one-shorter successor: the continuation
      -- after the return label.
      cases c with
      | nil =>
          simp only [frameStepLookupIdxB, frameStepLookupFastB]
      | cons hd c' =>
          cases hd <;>
            simp only [frameStepLookupIdxB, frameStepLookupFastB, lookupAt_length,
              List.length_cons, Nat.add_sub_cancel]
  | _ =>
      simp only [frameStepLookupIdxB, frameStepLookupFastB, lookupAt_length]

omit model in
/-- Resolving jump targets through `findLabelMap` and comparing the return
continuation with `posEqOpt` computes exactly what scanning with `findLabel` and
a structural comparison does. -/
theorem frameStepLookupFastB_eq_frameStepLookupB (prog : List Asm)
    (lookup : CertLookup) (i : Asm) (c : List Asm) (S : FLayout) (F : Nat)
    (R : FLayout) :
    frameStepLookupFastB (findLabelMap prog) lookup i c S F R =
      frameStepLookupB prog lookup i c S F R := by
  cases i <;>
    simp only [frameStepLookupFastB, frameStepLookupB, findLabelMap_getElem?,
      posEqOpt_eq_decide, Bool.decide_and]

/-! ### The finite certificate and the top-level check -/

/-- The untrusted solver's output: one `(positionLength, position, layout, frameBase, returnLayout)`
per reachable position. The leading length is a precomputed lookup key: reachable positions are
suffixes of the program, so equal length ⟹ equal position, and an O(1) array lookup on the key
replaces any scan — one O(length) list comparison against the stored position confirms the hit. -/
structure CertData where
  entries : List (Nat × List Asm × FLayout × Nat × FLayout)

/-- Largest lookup key claimed by the table. -/
def CertData.maxKey (d : CertData) : Nat :=
  d.entries.foldl (fun m e => max m e.1) 0

/-- Key-indexed lookup table: cell `k` holds the *first* entry with key `k` (`foldr`, so earlier
entries overwrite later ones). Out-of-range keys are dropped — such entries are unreachable
through `toCert` and therefore harmless. -/
def CertData.tbl (d : CertData) (size : Nat) :
    Array (Option (Nat × List Asm × FLayout × Nat × FLayout)) :=
  d.entries.foldr (fun e a => if h : e.1 < a.size then a.set e.1 (some e) h else a)
    (Array.replicate size none)

/-- The key-indexed table at its natural size. Named so it can be **bound once**
and passed as a value: see `lookupIn`. -/
def CertData.table (d : CertData) : Array (Option CertEntry) :=
  d.tbl (d.maxKey + 1)

/-- Build one shared lookup table whose successful lookup returns all three
certificate components. -/
def CertData.toLookup (d : CertData) : CertLookup :=
  let t := d.tbl (d.maxKey + 1)
  fun c => match t[c.length]? with
    | some (some e) =>
        if e.2.1 = c then some (e.2.2.1, e.2.2.2.1, e.2.2.2.2) else none
    | _ => none

omit model in
/-- The shared-table lookup *is* `toLookup`, by `let`-unfolding. -/
theorem CertData.toLookup_eq_lookupIn (d : CertData) :
    d.toLookup = lookupIn d.table := rfl

omit model in
theorem CertData.tbl_size (d : CertData) (size : Nat) : (d.tbl size).size = size := by
  unfold CertData.tbl
  induction d.entries with
  | nil => simp
  | cons e es ih => simp only [List.foldr_cons]; split <;> simp [ih]

omit model in
private theorem tbl_mem_aux {α : Type} [DecidableEq α]
    {es : List (Nat × α)} {size k : Nat} {e : Nat × α}
    (h : (es.foldr (fun e a => if h : e.1 < a.size then a.set e.1 (some e) h else a)
          (Array.replicate size none))[k]? = some (some e)) : e ∈ es := by
  induction es with
  | nil =>
      exfalso
      rw [List.foldr_nil] at h
      rcases Nat.lt_or_ge k size with hk | hk
      · rw [Array.getElem?_eq_getElem (by simpa using hk)] at h
        simp at h
      · rw [Array.getElem?_eq_none (by simpa using hk)] at h
        simp at h
  | cons e₀ es ih =>
      rw [List.foldr_cons] at h
      split at h
      · next hlt =>
          rw [Array.getElem?_set] at h
          split at h
          · exact (Option.some.inj (Option.some.inj h)) ▸ List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (ih h)
      · exact List.mem_cons_of_mem _ (ih h)

omit model in
/-- Every populated table cell holds a genuine entry. -/
theorem CertData.tbl_mem {d : CertData} {size k : Nat}
    {e : Nat × List Asm × FLayout × Nat × FLayout}
    (h : (d.tbl size)[k]? = some (some e)) : e ∈ d.entries :=
  tbl_mem_aux (by simpa [CertData.tbl] using h)

/-- Project the stable proof-facing certificate API from a bundled executable
lookup. -/
def CertLookup.toCert (lookup : CertLookup) : Cert :=
  { fl := fun c => (lookup c).map (fun v => v.1)
    fbMax := fun c => (lookup c).map (fun v => v.2.1)
    rl := fun c => (lookup c).map (fun v => v.2.2) }

/-- The `Cert` induced by a `CertData`. -/
def CertData.toCert (d : CertData) : Cert := d.toLookup.toCert

omit model in
theorem CertLookup.eq_some_iff_fields (lookup : CertLookup) (c : List Asm)
    (S : FLayout) (F : Nat) (R : FLayout) :
    lookup c = some (S, F, R) ↔
      (lookup.toCert.fl c = some S ∧ lookup.toCert.fbMax c = some F ∧
        lookup.toCert.rl c = some R) := by
  cases h : lookup c with
  | none => simp [CertLookup.toCert, h]
  | some value =>
      rcases value with ⟨S', F', R'⟩
      simp [CertLookup.toCert, h]

omit model in
@[simp] theorem CertLookup.decide_eq_some_fields (lookup : CertLookup)
    (c : List Asm) (S : FLayout) (F : Nat) (R : FLayout) :
    decide (lookup c = some (S, F, R)) =
      decide (lookup.toCert.fl c = some S ∧ lookup.toCert.fbMax c = some F ∧
        lookup.toCert.rl c = some R) := by
  cases h : lookup c with
  | none => simp [CertLookup.toCert, h]
  | some value =>
      rcases value with ⟨S', F', R'⟩
      simp [CertLookup.toCert, h]

omit model in
theorem frameStepLookupB_eq_frameStepB (prog : List Asm) (lookup : CertLookup)
    (i : Asm) (c : List Asm) (S : FLayout) (F : Nat) (R : FLayout) :
    frameStepLookupB prog lookup i c S F R =
      frameStepB prog lookup.toCert i c S F R := by
  cases i with
  | push => exact lookup.decide_eq_some_fields c (.word :: S) F R
  | pushImmutable key v => exact lookup.decide_eq_some_fields c (.word :: S) F R
  | pushLabel l => exact lookup.decide_eq_some_fields c (.retTo l :: S) F R
  | label => exact lookup.decide_eq_some_fields c S F R
  | jump l =>
      simp only [frameStepLookupB, frameStepB]
      cases htgt : findLabel l prog with
      | none => simp
      | some t =>
          cases ht : lookup t with
          | none => simp [CertLookup.toCert, ht]
          | some target =>
              rcases target with ⟨St, Ft, Rt⟩
              cases c with
              | nil => simp [CertLookup.toCert, ht]
              | cons head c' =>
                  cases head <;> simp [CertLookup.toCert, ht]
  | dup | pop | swap | op | jumpi | dynJump =>
      simp only [frameStepLookupB, frameStepB]
      repeat' split <;> simp_all

/-- Does an entry's stored position really *are* the program suffix at its claimed
key? `n` is the program length, so the length-`key` suffix sits at index
`n - key` of `sa`. The `key ≤ n` test is what stops `Nat` truncation from making
a wild key look honest.

A `true` answer proves `pos.length = key` (`keyHonest_length`), which is how the
verifier learns a position's length without walking it. For a certificate our own
solver produced the `posEq` is a pointer hit, so this costs O(1) per entry. -/
def keyHonest (sa : Array (List Asm)) (n key : Nat) (pos : List Asm) : Bool :=
  decide (key ≤ n) &&
    (match sa[n - key]? with
     | some c => posEq c pos
     | none => false)

omit model in
/-- Below this many instructions the length walks the suffix index removes are
cheaper than building the index: a program of `n` instructions costs one
`n + 1`-element array and `n` pushes either way, which only pays off once the
quadratic term is the larger one. Small Yul fixtures measurably regressed without
this gate (`objectCompiler`, ~4 ms per fixture). -/
def suffixIndexThreshold : Nat := 512

/-- The suffix index, or nothing for programs too small to benefit. Passing `#[]`
makes `keyHonest` fail for every entry, so they all take the length-computing
path — the same one the honesty test already falls back to. -/
def suffixesFor (prog : List Asm) (n : Nat) : Array (List Asm) :=
  if n < suffixIndexThreshold then #[] else suffixes prog

omit model in
theorem suffixesFor_eq (prog : List Asm) (n : Nat) :
    suffixesFor prog n = suffixes prog ∨ suffixesFor prog n = #[] := by
  unfold suffixesFor
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

omit model in
theorem keyHonest_length {prog : List Asm} {key : Nat} {pos : List Asm}
    (h : keyHonest (suffixes prog) prog.length key pos = true) : pos.length = key := by
  rw [keyHonest, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hle, hmatch⟩ := h
  have hidx : prog.length - key ≤ prog.length := by omega
  rw [suffixes_getElem? prog _ hidx] at hmatch
  simp only [posEq_eq_decide, decide_eq_true_eq] at hmatch
  rw [← hmatch]
  simp only [List.length_drop]
  omega

omit model in
/-- `keyHonest_length` for either array `suffixesFor` can hand out: an empty index
never reports an honest key, so the fact holds vacuously there. -/
theorem keyHonest_length_of {prog : List Asm} {sa : Array (List Asm)}
    (hsa : sa = suffixes prog ∨ sa = #[]) {key : Nat} {pos : List Asm}
    (h : keyHonest sa prog.length key pos = true) : pos.length = key := by
  rcases hsa with rfl | rfl
  · exact keyHonest_length h
  · simp [keyHonest] at h

/-- The verifier: bounded at every entry, and `frameStep` at every instruction entry, plus the
program-entry conditions. Each entry carries its own `(fl, fbMax, rl)`, so the current-position
checks read them directly; `frameStepB` resolves *successor* positions through `C`'s O(1) table.
Keys are bounded by `prog.length` up front, so a hostile table cannot force a huge allocation. -/
def checkCert (prog : List Asm) (d : CertData) : Bool :=
  d.entries.all (fun e => decide (e.1 ≤ prog.length)) &&
  (let C := d.toCert
   (C.fl prog == some []) && (C.fbMax prog == some 0) && (C.rl prog).isSome &&
   d.entries.all (fun e =>
     decide (e.2.2.1.length + e.2.2.2.1 ≤ 1023)
     && (match e.2.1 with
         | i :: c' => frameStepB prog C i c' e.2.2.1 e.2.2.2.1 e.2.2.2.2
         | [] => true)))

/-- Bundled-lookup implementation of `checkCert`, with the key-indexed table and
the program length taken as parameters.

Both are loop-invariant, and both must be *parameters* rather than `let`s to stay
that way: a `let` whose only uses are inside the per-entry closure gets floated
into it, so `prog.length` was recomputed — an O(program) walk — once per entry,
and the table was rebuilt once per lookup (see `lookupIn`). With ~one entry per
reachable instruction that made the verifier quadratic. -/
def checkCertWith (prog : List Asm) (d : CertData) (n : Nat)
    (t : Array (Option CertEntry)) (tgts : Std.HashMap Label (List Asm))
    (sa : Array (List Asm)) : Bool :=
  d.entries.all (fun e => decide (e.1 ≤ n)) &&
  (let lookup := lookupIn t
   (match lookup prog with
    | some ([], 0, _) => true
    | _ => false) &&
   d.entries.all (fun e =>
     decide (e.2.2.1.length + e.2.2.2.1 ≤ 1023)
     && (match e.2.1 with
         | i :: c' =>
             -- When the entry's key is honest its position's length is known, so
             -- the fall-through successor is looked up by index; otherwise fall
             -- back to computing the length, which cannot change the answer.
             frameStepLookupIdxB tgts lookup t
               (if keyHonest sa n e.1 (i :: c') then e.1 - 1 else c'.length)
               i c' e.2.2.1 e.2.2.2.1 e.2.2.2.2
         | [] => true)))

/-- Bundled-lookup implementation of `checkCert`. -/
def checkCertFast (prog : List Asm) (d : CertData) : Bool :=
  checkCertWith prog d prog.length d.table (findLabelMap prog)
    (suffixesFor prog prog.length)

omit model in
theorem checkCertFast_eq_checkCert (prog : List Asm) (d : CertData) :
    checkCertFast prog d = checkCert prog d := by
  let lookup := d.toLookup
  let fastEntry := fun e : Nat × List Asm × FLayout × Nat × FLayout =>
    decide (e.2.2.1.length + e.2.2.2.1 ≤ 1023) &&
      match e.2.1 with
      | i :: c =>
          frameStepLookupIdxB (findLabelMap prog) lookup d.table
            (if keyHonest (suffixesFor prog prog.length) prog.length e.1 (i :: c)
             then e.1 - 1 else c.length)
            i c e.2.2.1 e.2.2.2.1 e.2.2.2.2
      | [] => true
  let slowEntry := fun e : Nat × List Asm × FLayout × Nat × FLayout =>
    decide (e.2.2.1.length + e.2.2.2.1 ≤ 1023) &&
      match e.2.1 with
      | i :: c => frameStepB prog lookup.toCert i c e.2.2.1 e.2.2.2.1 e.2.2.2.2
      | [] => true
  have hentry (e) : fastEntry e = slowEntry e := by
    unfold fastEntry slowEntry
    cases hpos : e.2.1 with
    | nil => rfl
    | cons i c =>
        simp only
        -- Either index is `c`'s length: the honest-key one because `keyHonest`
        -- pins the stored position's length, the other by construction.
        have hk : (if keyHonest (suffixesFor prog prog.length) prog.length e.1
              (i :: c) then e.1 - 1 else c.length) = c.length := by
          by_cases hh : keyHonest (suffixesFor prog prog.length) prog.length e.1
              (i :: c) = true
          · rw [if_pos hh]
            have hlen : (i :: c).length = e.1 :=
              keyHonest_length_of (suffixesFor_eq prog prog.length) hh
            simp only [List.length_cons] at hlen
            omega
          · rw [if_neg (by simpa using hh)]
        have hlk : lookup = lookupIn d.table := rfl
        rw [hlk, hk,
          frameStepLookupIdxB_eq_frameStepLookupFastB _ _ _ _ _ _ _ _ rfl,
          frameStepLookupFastB_eq_frameStepLookupB,
          frameStepLookupB_eq_frameStepB]
  have hall : d.entries.all fastEntry = d.entries.all slowEntry := by
    congr 1
    funext e
    exact hentry e
  unfold checkCertFast checkCertWith checkCert
  simp only [CertData.toCert]
  change (_ && ((match lookup prog with | some ([], 0, _) => true | _ => false) &&
      d.entries.all fastEntry)) =
    (_ && (lookup.toCert.fl prog == some [] && lookup.toCert.fbMax prog == some 0 &&
      (lookup.toCert.rl prog).isSome && d.entries.all slowEntry))
  rw [hall]
  cases h : lookup prog with
  | none => simp [CertLookup.toCert, h]
  | some value =>
      rcases value with ⟨S, F, R⟩
      cases S <;> cases F <;> simp [CertLookup.toCert, h]

omit model in
/-- A defined position comes from a table entry carrying that exact `(position, fl, fbMax, rl)`. -/
theorem CertData.lookup_fl {d : CertData} {c : List Asm} {S : FLayout}
    (hfl : d.toCert.fl c = some S) :
    ∃ e ∈ d.entries, e.2.1 = c ∧ e.2.2.1 = S ∧
      d.toCert.fbMax c = some e.2.2.2.1 ∧ d.toCert.rl c = some e.2.2.2.2 := by
  simp only [CertData.toCert, CertLookup.toCert, CertData.toLookup] at hfl ⊢
  rcases hget : (d.tbl (d.maxKey + 1))[c.length]? with _ | eo
  · simp only [hget] at hfl
    exact absurd hfl (by simp)
  · rcases eo with _ | e
    · simp only [hget] at hfl
      exact absurd hfl (by simp)
    · simp only [hget] at hfl
      by_cases hpe : e.2.1 = c
      · rw [if_pos hpe] at hfl
        exact ⟨e, CertData.tbl_mem hget, hpe, Option.some.inj hfl,
          by simp [hpe], by simp [hpe]⟩
      · rw [if_neg hpe] at hfl
        exact absurd hfl (by simp)

omit model in
/-- **Verifier soundness.** -/
theorem checkCert_sound {prog : List Asm} {d : CertData} (h : checkCert prog d = true) :
    d.toCert.Valid prog ∧ d.toCert.Bounded ∧ d.toCert.fl prog = some [] ∧
      d.toCert.fbMax prog = some 0 ∧ ∃ R, d.toCert.rl prog = some R := by
  simp only [checkCert, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨-, ⟨⟨hentfl, hentfb⟩, hentrl⟩, hall⟩ := h
  refine ⟨?_, ?_, hentfl, hentfb, ?_⟩
  · -- Valid
    intro i c S F R hfl hfb hrl
    obtain ⟨e, hmem, hpe, hS, hfbe, hrle⟩ := d.lookup_fl hfl
    have hF : e.2.2.2.1 = F := by rw [hfbe] at hfb; exact Option.some.inj hfb
    have hR : e.2.2.2.2 = R := by rw [hrle] at hrl; exact Option.some.inj hrl
    have hchk := hall e hmem
    have hstep := hchk.2
    rw [hpe] at hstep
    have hfs := frameStepB_sound hstep
    rwa [hS, hF, hR] at hfs
  · -- Bounded
    intro c S F hfl hfb
    obtain ⟨e, hmem, _, hS, hfbe, _⟩ := d.lookup_fl hfl
    have hF : e.2.2.2.1 = F := by rw [hfbe] at hfb; exact Option.some.inj hfb
    have hchk := hall e hmem
    have hb := hchk.1
    rw [decide_eq_true_eq] at hb
    rw [hS, hF] at hb
    exact hb
  · exact Option.isSome_iff_exists.mp hentrl

/-- **The scalable overflow gate is sound.** A passing `checkCert` guarantees no reachable
configuration overflows the 1024-word stack. -/
theorem checkCert_run_bound {prog : List Asm} {d : CertData} (h : checkCert prog d = true)
    (yst : EvmState) :
    ∀ mid, ASteps (model := model) prog ⟨prog, [], yst⟩ mid → mid.stk.length ≤ 1023 := by
  obtain ⟨hV, hb, h0fl, h0fb, R, h0rl⟩ := checkCert_sound h
  exact run_stack_bound2 hV hb h0fl h0fb h0rl yst

/-! ### The untrusted frame-relative solver

Produces a `CertData` for `checkCert` to verify. Being untrusted, its only job is to make
`checkCert` pass for overflow-free programs; a wrong output is simply rejected by the verifier.

It is **linear** in two phases. Frame layouts (`fl`/`rl`) are context-insensitive, so every reachable
position is explored exactly once — a call explores the callee body *and* the caller's own
continuation directly (no call stack). Reachable positions are suffixes of `prog`, hence uniquely
keyed by their length, so a `position.length`-indexed array gives O(1) dedup. Each call records a
call-graph edge `(caller-frame, callee-frame, |midframe|)`; a second pass (`computeBase`) solves the
per-function base as the fixpoint `base(callee) = max over calls (base(caller) + |midframe|)`. A base
that fails to converge (a call-graph cycle = recursion) or exceeds 1023 is rejected. -/

/-- Labels used as `pushLabel` targets — the return addresses. -/
def pushLabelled (prog : List Asm) : List Label :=
  prog.filterMap (fun x => match x with | .pushLabel l => some l | _ => none)

/-- Count the `retRot` swaps immediately preceding a function's `dynJump` = its return-value count. -/
def retCount : List Asm → Nat → Nat
  | [], run => run
  | .dynJump :: _, run => run
  | .swap _ :: rest, run => retCount rest (run + 1)
  | _ :: rest, _ => retCount rest 0

/-- Every label's `findLabel` answer together with the target suffix's length,
computed in one pass. `k` is the length of the list being walked. -/
def labelTargetsGo : List Asm → Nat →
    Std.HashMap Label (List Asm × Nat) → Std.HashMap Label (List Asm × Nat)
  | [], _, m => m
  | i :: rest, k, m =>
      labelTargetsGo rest (k - 1)
        (match i with
         | .label l => if m.contains l then m else m.insert l (rest, k - 1)
         | _ => m)

/-- Jump-target table: `label ↦ (code after its first definition, that code's
length)`.

The analyzer used to call `findLabel l prog` per jump — a scan of the whole
program each time — and then `t.length`, another one. Both are O(program) and
there is one per jump, so resolving targets was quadratic. This resolves every
label once. -/
def labelTargets (prog : List Asm) : Std.HashMap Label (List Asm × Nat) :=
  labelTargetsGo prog prog.length ∅

/-- Analyzer state: `(positionLength, position, fl, rl, functionEntryLength)`.
The frame base is *not* carried here; it is solved per function in `computeBase`
and grafted on afterwards.

The position's length is **threaded** rather than recomputed. It is the `vis`
dedup key and it ends up in the certificate, and `List.length` on a suffix is
O(program): computing it once per explored position made phase 1 quadratic
(`List.length` was 31% of all instructions in a profile). Every successor's
length is known without walking — the fall-through is one shorter, and a jump
target's comes from `labelTargets`. -/
abbrev AState := Nat × List Asm × FLayout × FLayout × Nat

/-- A call-graph edge `(callerFrameLen, calleeFrameLen, midframeLen)`, keyed by function-entry length. -/
abbrev CallEdge := Nat × Nat × Nat

/-- Forward successors of one abstract state (mirrors `frameStep` forward), plus
any call edge. `k` is the length of `i :: c`, so the fall-through `c` has length
`k - 1`; jump targets take their length from `tgts`. -/
def stepSuccs (tgts : Std.HashMap Label (List Asm × Nat)) (pls : Std.HashSet Label)
    (ar : Std.HashMap Nat Nat)
    (k : Nat) : List Asm → FLayout → FLayout → Nat →
    Option (List AState × List CallEdge × List (Nat × Nat) × List (Nat × Nat))
  | [], _, _, _ => some ([], [], [], [])
  | i :: c, fl, rl, fe =>
    let kc := k - 1
    match i with
    | .push _ => some ([(kc, c, .word :: fl, rl, fe)], [], [], [])
    | .pushImmutable _ _ => some ([(kc, c, .word :: fl, rl, fe)], [], [], [])
    | .dup n => match fl[n.val]? with
        | some FSlot.word => some ([(kc, c, .word :: fl, rl, fe)], [], [], []) | _ => none
    | .pop => match fl with | .word :: fl' => some ([(kc, c, fl', rl, fe)], [], [], []) | _ => none
    | .swap n => match fl with
        | sx :: rest => match rest.drop n.val with
            | sy :: rst => some ([(kc, c, sy :: (rest.take n.val ++ sx :: rst), rl, fe)], [], [], [])
            | [] => none
        | [] => none
    | .label _ => some ([(kc, c, fl, rl, fe)], [], [], [])
    | .pushLabel l => some ([(kc, c, .retTo l :: fl, rl, fe)], [], [], [])
    | .op yop =>
        match opTable yop with
        | some o =>
            some ([(kc, c, List.replicate o.pushArity .word ++ fl.drop o.popArity, rl, fe)], [], [], [])
        | none => none
    | .jumpi l => match tgts[l]? with
        | some (t, kt) => match fl with
            | .word :: fl' => some ([(kt, t, fl', rl, fe), (kc, c, fl', rl, fe)], [], [], [])
            | _ => none
        | none => none
    | .jump l => match tgts[l]? with
        | some (t, kt) => match c with
            | .label Lret :: c' =>
                if pls.contains Lret then
                  match splitSetup Lret fl with
                  | some (Sw, Smid) =>
                      -- the callee's return arity: a previous round's `dynJump`
                      -- observation when available, else the classic-epilogue
                      -- swap-run heuristic (a wrong guess is corrected by the
                      -- next `analyze` round, never trusted — `checkCert`
                      -- verifies the final certificate)
                      let r := (ar[kt]?).getD (retCount t 0)
                      -- callee enters its own frame `t`; the continuation stays in the caller frame.
                      some ([(kt, t, Sw ++ [.ret], List.replicate r .word, kt),
                             (kc - 1, c', List.replicate r .word ++ Smid, rl, fe)],
                            [(fe, kt, Smid.length)], [(kt, r)], [])
                  | none => none
                else some ([(kt, t, fl, rl, fe)], [], [], [])
            | _ => some ([(kt, t, fl, rl, fe)], [], [], [])
        | none => none
    | .dynJump =>
        -- record the actually observed return arity of the enclosing frame
        match fl with
        | .ret :: S' => some ([], [], [], [(fe, S'.length)])
        | _ => some ([], [], [], [])

/-- Phase 1: explore every reachable position once, deduping by `position.length` in `vis`; collect
call edges. Returns `none` on an unrepresentable instruction (rejected downstream). -/
partial def analyzeGo (tgts : Std.HashMap Label (List Asm × Nat)) (pls : Std.HashSet Label)
    (ar : Std.HashMap Nat Nat) :
    List AState → Array (Option AState) → List CallEdge →
    List (Nat × Nat) → List (Nat × Nat) → Bool →
    Array (Option AState) × List CallEdge × List (Nat × Nat) × List (Nat × Nat) × Bool
  | [], vis, edges, assumed, obs, dead => (vis, edges, assumed, obs, dead)
  | (k, pos, fl, rl, fe) :: wl, vis, edges, assumed, obs, dead =>
    if k ≥ vis.size then (vis, edges, assumed, obs, true) else
    match vis[k]! with
    | some _ => analyzeGo tgts pls ar wl vis edges assumed obs dead
    | none =>
      match stepSuccs tgts pls ar k pos fl rl fe with
      | some (succs, es, asms, os) =>
          analyzeGo tgts pls ar (succs ++ wl) (vis.set! k (some (k, pos, fl, rl, fe)))
            (es ++ edges) (asms ++ assumed) (os ++ obs) dead
      | none =>
          -- Unrepresentable here — possibly only because a wrong return-arity
          -- assumption corrupted this path's frame. Record the position (a
          -- surviving bad entry makes `checkCert` reject, so this is never a
          -- soundness leak) and keep walking, so the `dynJump` observations
          -- that correct the arity for the next round are still collected.
          analyzeGo tgts pls ar wl (vis.set! k (some (k, pos, fl, rl, fe)))
            edges assumed obs true

/-- Phase 2: solve the per-function frame base as a fixpoint over the call edges (`size` bounds the
frame-entry key space). Rejects a non-converging graph (recursion) or a base exceeding 1023. -/
def computeBase (size : Nat) (edges : List CallEdge) : Option (Array Nat) := Id.run do
  let mut base : Array Nat := Array.replicate size 0
  -- A DAG converges within `edges.length` relaxation rounds; one extra round detects a cycle.
  -- Stop as soon as a round relaxes nothing: the iteration is monotone, so a
  -- round that changes nothing leaves every later round unchanged too — same
  -- fixpoint, but `|E|` rounds over `|E|` edges is quadratic and real call
  -- graphs settle in a handful.
  for _ in [0:edges.length + 1] do
    let mut changed := false
    for e in edges do
      let nb := base[e.1]! + e.2.2
      if base[e.2.1]! < nb then
        if nb > 1023 then return none
        base := base.set! e.2.1 nb
        changed := true
    if !changed then break
  for e in edges do
    if base[e.2.1]! < base[e.1]! + e.2.2 then return none  -- did not converge ⇒ recursion
  return some base

/-- The solver: explore from the entry (empty frame, `main`'s return layout `[]`, frame = whole
program), solve the bases, then graft `fbMax = base(function)` onto every position. -/
def analyze (prog : List Asm) : CertData :=
  -- Iterate the exploration until the assumed callee return arities agree
  -- with the arities actually observed at each `dynJump` (the swap-run
  -- heuristic seeds round 1 and is exact for the classic backend; the SSA
  -- backend's shuffled epilogues need the observation round). A handful of
  -- rounds always suffices — arities are fixed per function — and a wrong
  -- certificate is merely rejected by `checkCert`, never trusted.
  go 4 {}
where
  n := prog.length
  size := n + 1
  tgts := labelTargets prog
  pls := Std.HashSet.ofList (pushLabelled prog)
  go : Nat → Std.HashMap Nat Nat → CertData
    | 0, _ => ⟨[]⟩
    | fuel + 1, ar =>
      let (vis, edges, assumed, obs, _dead) :=
        analyzeGo tgts pls ar [(n, prog, [], [], n)]
          (Array.replicate size none) [] [] [] false
      -- every arity assumed at a call site must agree with the arity
      -- observed at the callee's own `dynJump`s; otherwise re-run seeded
      -- with the observations (dead ends may be assumption artifacts and
      -- clear up on the re-run; a genuine one survives to the final round,
      -- where its recorded entry fails `checkCert`)
      let obsMap := obs.foldl (fun m (fe, a) => m.insert fe a)
        (∅ : Std.HashMap Nat Nat)
      let consistent := assumed.all fun (kt, r) =>
        match obsMap[kt]? with
        | some a => a = r
        | none => true
      if !consistent then
        go fuel (obs.foldl (fun m (fe, a) => m.insert fe a) ar)
      else
        match computeBase size edges with
        | none => ⟨[]⟩
        | some base =>
          -- The position length is already carried, so the certificate's lookup key
          -- costs nothing here either.
          ⟨vis.toList.filterMap (fun o =>
            o.map (fun s => (s.1, s.2.1, s.2.2.1, base[s.2.2.2.2]!, s.2.2.2.1)))⟩

/-- The `compile`-facing gate: analyse then verify. -/
def stackOK2 (prog : List Asm) : Bool := checkCertFast prog (analyze prog)

/-- **`stackOK2` is sound**: passing it guarantees no stack overflow. -/
theorem stackOK2_run_bound {prog : List Asm} (h : stackOK2 prog = true) (yst : EvmState) :
    ∀ mid, ASteps (model := model) prog ⟨prog, [], yst⟩ mid → mid.stk.length ≤ 1023 :=
  by
    rw [stackOK2, checkCertFast_eq_checkCert] at h
    exact checkCert_run_bound h yst

end YulEvmCompiler
