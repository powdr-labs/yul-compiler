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
          C.fl t = some (Sw ++ [FSlot.ret]) ∧ C.fbMax t = some (F + Smid.length) ∧
          C.rl t = some Sret ∧ (∀ s ∈ Sret, s = FSlot.word) ∧
          findLabel Lret prog = some c' ∧
          C.fl c' = some (Sret ++ Smid) ∧ C.fbMax c' = some F ∧ C.rl c' = some R)
  | .jumpi l,     c, S, F, R => ∃ S', S = .word :: S' ∧
      (∃ t, findLabel l prog = some t ∧ C.fl t = some S' ∧ C.fbMax t = some F ∧ C.rl t = some R) ∧
      C.fl c = some S' ∧ C.fbMax c = some F ∧ C.rl c = some R
  | .dynJump,     _, S, F, R => 1 ≤ F ∧ ∃ S', S = .ret :: S' ∧ R = S' ∧ (∀ s ∈ S', s = FSlot.word)

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
      C.fl c = some S → C.fbMax c = some 0 → C.rl c = some R → FMatch σ S →
      GoodStack prog C σ c
  | call {stk above below rest : List AVal} {c cRet : List Asm} {S Sret : FLayout} {F : Nat}
      {lRet : Label} :
      C.fl c = some S → C.fbMax c = some F → C.rl c = some Sret →
      FMatch (above ++ .code lRet :: below) S → IsWords below →
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
  | @root σ c S R hfl hfb hrl hm => have := hb c S 0 hfl hfb; have := hm.length_eq; omega
  | @call stk above below rest c cRet S Sret F lRet hfl hfb hrl hm hbw hfind hle _ heq =>
      have hbnd := hb c S F hfl hfb; have hlen := hm.length_eq; subst heq
      rw [List.length_append]; omega

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
  | @call stk above below rest c cRet S Sret F lRet hfl hfb0 hrl0 hm hbw hfind hle hres heq =>
      obtain rfl := Option.some.inj (h0 ▸ hfl)
      refine .call (above := .word v :: above) (below := below) (lRet := lRet) h1
        (by rw [hfb, hfb0]) (by rw [hrl, hrl0]) (FMatch.word (v := v) hm) hbw hfind hle hres ?_
      rw [heq]; rfl

theorem GoodStack.growRet {prog C} {σ : List AVal} {c₀ c₁ : List Asm} {S₀ : FLayout} {l : Label}
    (h : GoodStack prog C σ c₀) (h0 : C.fl c₀ = some S₀) (h1 : C.fl c₁ = some (.ret :: S₀))
    (hfb : C.fbMax c₁ = C.fbMax c₀) (hrl : C.rl c₁ = C.rl c₀) :
    GoodStack prog C (.code l :: σ) c₁ := by
  cases h with
  | @root σ c S R hfl hfb0 hrl0 hm =>
      obtain rfl := Option.some.inj (h0 ▸ hfl)
      exact .root h1 (by rw [hfb, hfb0]) (by rw [hrl, hrl0]) (.ret hm)
  | @call stk above below rest c cRet S Sret F lRet hfl hfb0 hrl0 hm hbw hfind hle hres heq =>
      obtain rfl := Option.some.inj (h0 ▸ hfl)
      refine .call (above := .code l :: above) (below := below) (lRet := lRet) h1
        (by rw [hfb, hfb0]) (by rw [hrl, hrl0]) (FMatch.ret (l := l) hm) hbw hfind hle hres ?_
      rw [heq]; rfl

theorem GoodStack.growRetTo {prog C} {σ : List AVal} {c₀ c₁ : List Asm} {S₀ : FLayout} {l : Label}
    (h : GoodStack prog C σ c₀) (h0 : C.fl c₀ = some S₀) (h1 : C.fl c₁ = some (.retTo l :: S₀))
    (hfb : C.fbMax c₁ = C.fbMax c₀) (hrl : C.rl c₁ = C.rl c₀) :
    GoodStack prog C (.code l :: σ) c₁ := by
  cases h with
  | @root σ c S R hfl hfb0 hrl0 hm =>
      obtain rfl := Option.some.inj (h0 ▸ hfl)
      exact .root h1 (by rw [hfb, hfb0]) (by rw [hrl, hrl0]) (.retTo hm)
  | @call stk above below rest c cRet S Sret F lRet hfl hfb0 hrl0 hm hbw hfind hle hres heq =>
      obtain rfl := Option.some.inj (h0 ▸ hfl)
      refine .call (above := .code l :: above) (below := below) (lRet := lRet) h1
        (by rw [hfb, hfb0]) (by rw [hrl, hrl0]) (FMatch.retTo (l := l) hm) hbw hfind hle hres ?_
      rw [heq]; rfl

theorem GoodStack.same {prog C} {σ : List AVal} {c₀ c₁ : List Asm}
    (h : GoodStack prog C σ c₀) (hfl : C.fl c₁ = C.fl c₀) (hfb : C.fbMax c₁ = C.fbMax c₀)
    (hrl : C.rl c₁ = C.rl c₀) : GoodStack prog C σ c₁ := by
  cases h with
  | @root σ c S R hfl0 hfb0 hrl0 hm =>
      exact .root (by rw [hfl, hfl0]) (by rw [hfb, hfb0]) (by rw [hrl, hrl0]) hm
  | @call stk above below rest c cRet S Sret F lRet hfl0 hfb0 hrl0 hm hbw hfind hle hres heq =>
      exact .call (by rw [hfl, hfl0]) (by rw [hfb, hfb0]) (by rw [hrl, hrl0]) hm hbw hfind hle hres heq

theorem GoodStack.shrinkWord {prog C} {σ : List AVal} {c₀ c₁ : List Asm} {S' : FLayout} {v : AVal}
    (h : GoodStack prog C (v :: σ) c₀) (h0 : C.fl c₀ = some (.word :: S'))
    (h1 : C.fl c₁ = some S') (hfb : C.fbMax c₁ = C.fbMax c₀) (hrl : C.rl c₁ = C.rl c₀) :
    GoodStack prog C σ c₁ := by
  cases h with
  | @root vσ c S R hfl hfb0 hrl0 hm =>
      obtain rfl := Option.some.inj (h0 ▸ hfl)
      cases hm with
      | word hm' => exact .root h1 (by rw [hfb, hfb0]) (by rw [hrl, hrl0]) hm'
  | @call stk above below rest c cRet S Sret F lRet hfl hfb0 hrl0 hm hbw hfind hle hres heq =>
      obtain rfl := Option.some.inj (h0 ▸ hfl)
      cases above with
      | nil => rw [List.nil_append] at hm; nomatch hm
      | cons a above' =>
          rw [List.cons_append] at hm heq
          cases hm with
          | @word w σ'' S'' hm' =>
              obtain ⟨rfl, rfl⟩ := List.cons.inj heq
              exact .call (above := above') (below := below) (lRet := lRet) h1
                (by rw [hfb, hfb0]) (by rw [hrl, hrl0]) hm' hbw hfind hle hres rfl

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
  | @call stk above below rest c cRet S' Sret F lRet hfl hfb0 hrl0 hm hbw hfind hle hres heq =>
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
        (by rw [hfb, hfb0]) (by rw [hrl, hrl0]) ?_ hbw hfind hle hres ?_
      · rw [hSdrop, ← hrets]
        have hfr2 : (words rets ++ above.drop args.length) ++ AVal.code lRet :: below
            = words rets ++ (above ++ AVal.code lRet :: below).drop args.length := by
          rw [hdropfr, List.append_assoc]
        rw [hfr2]
        exact (FMatch.replicate_word rets).append hMf
      · rw [hσ, hdropfr]; simp only [List.append_assoc]

/-- The runtime cell at depth `i` matches the frame slot at depth `i`. -/
theorem GoodStack.slotAt {prog C} {σ : List AVal} {c : List Asm} {S : FLayout} {i : Nat} {x : AVal}
    {s : FSlot} (h : GoodStack prog C σ c) (hfl : C.fl c = some S) (hx : σ[i]? = some x)
    (hs : S[i]? = some s) : FMatch [x] [s] := by
  cases h with
  | @root σ' c' S' R hfl' hfb' hrl' hm =>
      obtain rfl : S = S' := Option.some.inj (hfl.symm.trans hfl')
      exact hm.at_idx hx hs
  | @call stk above below rest c' cRet S' Sret F lRet hfl' hfb' hrl' hm hbw hfind hle hres heq =>
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
  | @root σ' c' S' R hfl hfb0 hrl0 hm =>
      obtain rfl := Option.some.inj (h0 ▸ hfl)
      exact .root h1 (by rw [hfb, hfb0]) (by rw [hrl, hrl0]) (hm.swap_build hτlen)
  | @call stk above below rest c' cRet S' Sret F lRet hfl hfb0 hrl0 hm hbw hfind hle hres heq =>
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
        have leafNil : y = AVal.code lRet → below = fσ2' →
            GoodStack prog C ((y :: (τ ++ AVal.word wv :: fσ2')) ++ rest) c₁ := by
          rintro rfl rfl
          refine .call (above := []) (below := τ ++ AVal.word wv :: below) (lRet := lRet) h1
            (by rw [hfb, hfb0]) (by rw [hrl, hrl0]) (by rw [List.nil_append]; exact hMnew) ?_
            hfind hle hres (by rw [List.nil_append])
          intro z hz
          rcases List.mem_append.mp hz with hz | hz
          · exact hτw _ hz
          · rcases List.mem_cons.mp hz with rfl | hz
            · exact ⟨wv, rfl⟩
            · exact hbw _ hz
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
              rw [List.nil_append] at ht2
              obtain ⟨hy, hbe⟩ := List.cons.inj ht2
              exact leafNil hy.symm hbe
        · cases t with
          | nil =>
              rw [List.nil_append] at ht2
              obtain ⟨hy, hbe⟩ := List.cons.inj ht2
              exact leafNil hy hbe.symm
          | cons t0 t' =>
              rw [List.cons_append] at ht2
              obtain ⟨rfl, rfl⟩ := List.cons.inj ht2
              refine .call (above := y :: (τ ++ AVal.word wv :: t')) (below := below) (lRet := lRet)
                h1 (by rw [hfb, hfb0]) (by rw [hrl, hrl0]) ?_ hbw hfind hle hres (by simp)
              have he : (y :: (τ ++ AVal.word wv :: t')) ++ AVal.code lRet :: below
                  = y :: (τ ++ AVal.word wv :: (t' ++ AVal.code lRet :: below)) := by simp
              rw [he]; exact hMnew

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
          obtain rfl : t = c' := Option.some.inj (hfindt.symm.trans hfind)
          cases hinv with
          | @root σr cr Sr Rr hflr hfbr hrlr hmr =>
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
                    (rest := midframe) (cRet := cc) hflt hfbt hrlt (hMsw.append (FMatch.ret FMatch.nil))
                    (by intro x hx; simp at hx) hfindLret (by rw [hMmid.length_eq]; omega) ?_ ?_
                  · intro ws hws
                    exact GoodStack.root hflcc hfbcc hrlcc (hws.append hMmid)
                  · exact hσeq
          | @call stk0 above0 below0 rest0 c0 cRet0 S0 Sret0 F0 lRet0 hfl0 hfb0 hrl0 hm0 hbw0
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
                  -- lRet0 (caller's own return) lives in `midframe` (below the setup)
                  sorry
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
      | retTo _ => exact hinv.growRetTo hfl hflc (by rw [hfbc, hfb]) (by rw [hrlc, hrl])
  | @swap n x y τ ρ c yst hτ =>
      obtain ⟨S, F, R, hfl, hfb, hrl⟩ := hinv.certAt
      obtain ⟨sx, mid, sy, rst, hSeq, hmidlen, hsxw, hmidw, hflc, hfbc, hrlc⟩ :=
        hV _ c S F R hfl hfb hrl
      subst hSeq
      have hτlen : mid.length = τ.length := by rw [hmidlen, hτ]
      exact hinv.swapFrame hfl hsxw hmidw hτlen hflc (by rw [hfbc, hfb]) (by rw [hrlc, hrl])
  | @dynJump l c c' σ yst hfind =>
      obtain ⟨S, F, R, hfl, hfb, hrl⟩ := hinv.certAt
      obtain ⟨hF1, S', hSeq, hRS', hwords⟩ := hV _ c S F R hfl hfb hrl
      cases hinv with
      | @root σ0 c0 S0 R0 hfl0 hfb0 hrl0 hm =>
          obtain rfl : (0 : Nat) = F := Option.some.inj (hfb0.symm.trans hfb)
          omega
      | @call stk above below rest c0 cRet S0 Sret F0 lRet hfl0 hfb0 hrl0 hm hbw hfind0 hle hres heq =>
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

end YulEvmCompiler
