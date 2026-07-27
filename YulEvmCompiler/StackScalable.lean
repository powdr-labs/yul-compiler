import YulEvmCompiler.StackBound

set_option warningAsError false  -- WIP: carries `sorry` placeholders (call/dynJump/dup/swap/op/jumpi)
/-!
# YulEvmCompiler.StackScalable — a **scalable** (frame-relative) stack-overflow analysis  [WIP]

`StackBound` proves the abstract Asm machine never overflows the 1024-word EVM operand stack, but
its checker's layout map is **context-sensitive** (one absolute layout per caller context) and so is
*exponential* in call-nesting depth — it explodes on real Solidity via-IR output.

This module replaces it with a **frame-relative** analysis. A function's frame *layout* is
context-*insensitive*: it excludes the caller context, so each code position gets a **single** frame
layout `fl c` — the checker stays linear. The bound is recovered from a per-function max frame base
`fbMax` (an acyclic-call-graph DP). We reuse `StackBound`'s proven `StkMatch` for the current frame,
and `GoodStack` layers frames into the call chain.

Status: structural lemmas + frame grow/shrink/same + the intra-frame `step` cases
(push/pushLabel/pop/label/local-jump) are proven; `dup`/`swap`/`op`/`jumpi` and the frame-changing
`call`/`dynJump` cases are the remaining work (marked `sorry`). Untrusted solver: memory
`stackbound-retrot-blocker`.
-/

namespace YulEvmCompiler

open EvmSemantics EvmSemantics.EVM
open YulSemantics.EVM (U256 EvmState Op)

/-- Dummy layout map — `StkMatch` ignores its `H` argument, so any value works; we fix one. -/
def dH : LayoutMap := fun _ => []

/-- A runtime value matches a slot: word↔word, or a return address whose label resolves to the
slot's tagged target. -/
def SlotMatchP (prog : List Asm) : AVal → Slot → Prop
  | .word _, .word => True
  | .code l, .code t => findLabel l prog = some t
  | _, _ => False

/-- Head inversion for `StkMatch`. -/
theorem StkMatch.cons_inv {prog H} {a : AVal} {σ : List AVal} {s : Slot} {S : StkLayout}
    (h : StkMatch prog H (a :: σ) (s :: S)) : SlotMatchP prog a s ∧ StkMatch prog H σ S := by
  cases h with
  | word htl => exact ⟨trivial, htl⟩
  | code hf htl => exact ⟨hf, htl⟩

/-- Head inversion exposing the runtime cons shape. -/
theorem StkMatch.cons_inv' {prog H} {σ : List AVal} {s : Slot} {S : StkLayout}
    (h : StkMatch prog H σ (s :: S)) :
    ∃ a σ', σ = a :: σ' ∧ SlotMatchP prog a s ∧ StkMatch prog H σ' S := by
  cases h with
  | word htl => exact ⟨_, _, rfl, trivial, htl⟩
  | code hf htl => exact ⟨_, _, rfl, hf, htl⟩

/-- Head composition for `StkMatch`. -/
theorem StkMatch.consMatch {prog H} {a : AVal} {σ : List AVal} {s : Slot} {S : StkLayout}
    (hm : SlotMatchP prog a s) (h : StkMatch prog H σ S) : StkMatch prog H (a :: σ) (s :: S) := by
  cases a with
  | word w => cases s with
      | word => exact .word h
      | code t => exact absurd hm (by simp [SlotMatchP])
  | code l => cases s with
      | word => exact absurd hm (by simp [SlotMatchP])
      | code t => exact .code hm h

/-- Split a `StkMatch` by a **layout** prefix (dual of `append_inv`, which splits by the stack). -/
theorem StkMatch.append_inv_layout {prog H} {σ : List AVal} {S1 S2 : StkLayout}
    (h : StkMatch prog H σ (S1 ++ S2)) :
    ∃ σ1 σ2, σ = σ1 ++ σ2 ∧ StkMatch prog H σ1 S1 ∧ StkMatch prog H σ2 S2 := by
  induction S1 generalizing σ with
  | nil => exact ⟨[], σ, rfl, .nil, h⟩
  | cons s S1 ih =>
      rw [List.cons_append] at h
      obtain ⟨a, σ', rfl, hsm, htl⟩ := h.cons_inv'
      obtain ⟨σ1, σ2, rfl, h1, h2⟩ := ih htl
      exact ⟨a :: σ1, σ2, rfl, StkMatch.consMatch hsm h1, h2⟩

/-- Matched stacks match cell-by-cell. -/
theorem StkMatch.slotMatch_at {prog H} {σ : List AVal} {S : StkLayout} (h : StkMatch prog H σ S) :
    ∀ {i : Nat} {x : AVal} {s : Slot}, σ[i]? = some x → S[i]? = some s → SlotMatchP prog x s := by
  induction h with
  | nil => intro i x s hx _; simp at hx
  | @word w σ' S' _ ih =>
      intro i x s hx hs
      cases i with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hs
                subst hx; subst hs; trivial
      | succ k => simp only [List.getElem?_cons_succ] at hx hs; exact ih hx hs
  | @code l t σ' S' hf _ ih =>
      intro i x s hx hs
      cases i with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hs
                subst hx; subst hs; exact hf
      | succ k => simp only [List.getElem?_cons_succ] at hx hs; exact ih hx hs

/-! ### The certificate -/

/-- A frame-relative certificate: each code position's **frame layout** `fl` (context-insensitive)
and its function's **max frame base** `fbMax`. -/
structure Cert where
  fl : List Asm → Option StkLayout
  fbMax : List Asm → Option Nat

/-- The certificate keeps every position's absolute height (`|frame| + base`) within the limit. -/
def Cert.Bounded (C : Cert) : Prop :=
  ∀ c S F, C.fl c = some S → C.fbMax c = some F → S.length + F ≤ 1023

/-- Per-instruction frame-relative step constraint (the checker's core), given the current
position's frame layout `S` and base `F`. Intra-frame instructions transform `S`, preserve `F`;
`jump` is local *or* a call (call = WIP `True`); `dynJump` is WIP. -/
def frameStep (prog : List Asm) (C : Cert) : Asm → List Asm → StkLayout → Nat → Prop
  | .push _,      c, S, F => C.fl c = some (.word :: S) ∧ C.fbMax c = some F
  | .dup n,       c, S, F => ∃ sl, S[n.val]? = some sl ∧ C.fl c = some (sl :: S) ∧ C.fbMax c = some F
  | .pushLabel l, c, S, F => ∃ t, findLabel l prog = some t ∧ C.fl c = some (.code t :: S)
      ∧ C.fbMax c = some F
  | .pop,         c, S, F => ∃ S', S = .word :: S' ∧ C.fl c = some S' ∧ C.fbMax c = some F
  | .swap n,      c, S, F => ∃ sx mid sy rest, S = sx :: (mid ++ sy :: rest) ∧ mid.length = n.val
      ∧ C.fl c = some (sy :: (mid ++ sx :: rest)) ∧ C.fbMax c = some F
  | .label _,     c, S, F => C.fl c = some S ∧ C.fbMax c = some F
  | .op yop,      c, S, F => ∃ o, opTable yop = some o ∧ Operation.popArity o ≤ S.length ∧
      C.fl c = some (List.replicate (Operation.pushArity o) Slot.word ++ S.drop (Operation.popArity o))
      ∧ C.fbMax c = some F
  | .jump l,      _, S, F => (∃ t, findLabel l prog = some t ∧ C.fl t = some S ∧ C.fbMax t = some F)
      ∨ True  -- WIP: the call case
  | .jumpi l,     c, S, F => ∃ S', S = .word :: S' ∧
      (∃ t, findLabel l prog = some t ∧ C.fl t = some S' ∧ C.fbMax t = some F) ∧
      C.fl c = some S' ∧ C.fbMax c = some F
  | .dynJump,     _, _, _ => True  -- WIP

/-- A certificate is valid when every analysed position satisfies its frame-step constraint. -/
def Cert.Valid (prog : List Asm) (C : Cert) : Prop :=
  ∀ i c S F, C.fl (i :: c) = some S → C.fbMax (i :: c) = some F → frameStep prog C i c S F

/-! ### The invariant

`call` uses a free stack index `stk` with an equation `stk = frame ++ rest`, so that `cases` on a
cons-shaped stack does not hit dependent-elimination failure on the append. -/

inductive GoodStack (prog : List Asm) (C : Cert) : List AVal → List Asm → Prop
  | root {σ : List AVal} {c : List Asm} {S : StkLayout} :
      C.fl c = some S → C.fbMax c = some 0 → StkMatch prog dH σ S →
      GoodStack prog C σ c
  | call {stk frame rest : List AVal} {c cRet : List Asm} {S Sret : StkLayout} {F : Nat}
      {lRet : Label} :
      C.fl c = some S → C.fbMax c = some F → StkMatch prog dH frame S →
      (.code lRet) ∈ frame → findLabel lRet prog = some cRet → rest.length ≤ F →
      (∀ ws : List AVal, StkMatch prog dH ws Sret → GoodStack prog C (ws ++ rest) cRet) →
      stk = frame ++ rest →
      GoodStack prog C stk c

/-- Extract the current position's certificate entries (no casing of the stack shape). -/
theorem GoodStack.certAt {prog C} {σ : List AVal} {c : List Asm}
    (h : GoodStack prog C σ c) : ∃ S F, C.fl c = some S ∧ C.fbMax c = some F := by
  cases h with
  | root hfl hfb _ => exact ⟨_, _, hfl, hfb⟩
  | call hfl hfb _ _ _ _ _ _ => exact ⟨_, _, hfl, hfb⟩

/-- The runtime cell at depth `i` matches the frame layout slot at depth `i`. -/
theorem GoodStack.slotMatchAt {prog C} {σ : List AVal} {c : List Asm} {S : StkLayout}
    {i : Nat} {x : AVal} {s : Slot}
    (h : GoodStack prog C σ c) (hfl : C.fl c = some S) (hx : σ[i]? = some x) (hs : S[i]? = some s) :
    SlotMatchP prog x s := by
  cases h with
  | @root σ' c' S' hfl' hfb' hm =>
      obtain rfl : S = S' := Option.some.inj (hfl.symm.trans hfl')
      exact hm.slotMatch_at hx hs
  | @call stk frame rest c' cRet S' Sret F lRet hfl' hfb' hm hmem hfindR hle hres heq =>
      obtain rfl : S = S' := Option.some.inj (hfl.symm.trans hfl')
      have hilt : i < frame.length := by
        have hiS : i < S.length := by
          by_contra hc
          rw [List.getElem?_eq_none (Nat.le_of_not_lt hc)] at hs; exact absurd hs (by simp)
        rw [hm.length_eq]; exact hiS
      have hxf : frame[i]? = some x := by rw [heq, List.getElem?_append_left hilt] at hx; exact hx
      exact hm.slotMatch_at hxf hs

/-- **The bound falls out of the invariant + the certificate.** -/
theorem GoodStack.bound {prog C} (hb : C.Bounded) {σ : List AVal} {c : List Asm}
    (h : GoodStack prog C σ c) : σ.length ≤ 1023 := by
  cases h with
  | @root σ c S hfl hfb hm =>
      have := hb c S 0 hfl hfb
      have hlen := hm.length_eq
      omega
  | @call stk frame rest c cRet S Sret F lRet hfl hfb hm hmem hfindR hle hres heq =>
      have hbnd := hb c S F hfl hfb
      have hlen := hm.length_eq
      subst heq; rw [List.length_append]; omega

/-- The entry configuration is `GoodStack`, given the program is assigned the empty frame at base 0. -/
theorem GoodStack.entry {prog C} (h0fl : C.fl prog = some []) (h0fb : C.fbMax prog = some 0) :
    GoodStack prog C [] prog :=
  .root h0fl h0fb .nil

/-! ### Frame grow / shrink / same — the intra-frame building blocks -/

/-- Pushing a plain word onto the current frame (`push`). -/
theorem GoodStack.growWord {prog C} {σ : List AVal} {c₀ c₁ : List Asm} {S₀ : StkLayout} {v : U256}
    (h : GoodStack prog C σ c₀) (h0 : C.fl c₀ = some S₀) (h1 : C.fl c₁ = some (.word :: S₀))
    (hfb : C.fbMax c₁ = C.fbMax c₀) : GoodStack prog C (.word v :: σ) c₁ := by
  cases h with
  | @root σ c S hfl hfb0 hm =>
      obtain rfl := Option.some.inj (h0 ▸ hfl)
      exact .root h1 (by rw [hfb, hfb0]) (.word hm)
  | @call stk frame rest c cRet S Sret F lRet hfl hfb0 hm hmem hfindR hle hres heq =>
      obtain rfl := Option.some.inj (h0 ▸ hfl)
      refine .call (lRet := lRet) h1 (by rw [hfb, hfb0]) (StkMatch.word (v := v) hm)
        (List.mem_cons_of_mem _ hmem) hfindR hle hres ?_
      rw [heq, List.cons_append]

/-- Pushing a return address onto the current frame (`pushLabel`). -/
theorem GoodStack.growCode {prog C} {σ : List AVal} {c₀ c₁ : List Asm} {S₀ : StkLayout}
    {l : Label} {t : List Asm}
    (h : GoodStack prog C σ c₀) (h0 : C.fl c₀ = some S₀) (h1 : C.fl c₁ = some (.code t :: S₀))
    (hfind : findLabel l prog = some t) (hfb : C.fbMax c₁ = C.fbMax c₀) :
    GoodStack prog C (.code l :: σ) c₁ := by
  cases h with
  | @root σ c S hfl hfb0 hm =>
      obtain rfl := Option.some.inj (h0 ▸ hfl)
      exact .root h1 (by rw [hfb, hfb0]) (.code hfind hm)
  | @call stk frame rest c cRet S Sret F lRet hfl hfb0 hm hmem hfindR hle hres heq =>
      obtain rfl := Option.some.inj (h0 ▸ hfl)
      refine .call (lRet := lRet) h1 (by rw [hfb, hfb0]) (StkMatch.code (l := l) hfind hm)
        (List.mem_cons_of_mem _ hmem) hfindR hle hres ?_
      rw [heq, List.cons_append]

/-- Moving to a position with the same frame layout and base (`label`, local `jump`). -/
theorem GoodStack.same {prog C} {σ : List AVal} {c₀ c₁ : List Asm}
    (h : GoodStack prog C σ c₀) (hfl : C.fl c₁ = C.fl c₀) (hfb : C.fbMax c₁ = C.fbMax c₀) :
    GoodStack prog C σ c₁ := by
  cases h with
  | @root σ c S hfl0 hfb0 hm =>
      exact .root (by rw [hfl, hfl0]) (by rw [hfb, hfb0]) hm
  | @call stk frame rest c cRet S Sret F lRet hfl0 hfb0 hm hmem hfindR hle hres heq =>
      exact .call (by rw [hfl, hfl0]) (by rw [hfb, hfb0]) hm hmem hfindR hle hres heq

/-- Popping a plain word off the current frame (`pop`). -/
theorem GoodStack.shrinkWord {prog C} {σ : List AVal} {c₀ c₁ : List Asm} {S' : StkLayout} {v : AVal}
    (h : GoodStack prog C (v :: σ) c₀) (h0 : C.fl c₀ = some (.word :: S'))
    (h1 : C.fl c₁ = some S') (hfb : C.fbMax c₁ = C.fbMax c₀) : GoodStack prog C σ c₁ := by
  cases h with
  | @root vσ c S hfl hfb0 hm =>
      obtain rfl := Option.some.inj (h0 ▸ hfl)
      cases hm with
      | word hm' => exact .root h1 (by rw [hfb, hfb0]) hm'
  | @call stk frame rest c cRet S Sret F lRet hfl hfb0 hm hmem hfindR hle hres heq =>
      obtain rfl := Option.some.inj (h0 ▸ hfl)
      cases hm with
      | @word w frame' S'' hm' =>
          rw [List.cons_append] at heq
          obtain ⟨rfl, rfl⟩ := List.cons.inj heq
          refine .call (lRet := lRet) h1 (by rw [hfb, hfb0]) hm' ?_ hfindR hle hres rfl
          cases List.mem_cons.mp hmem with
          | inl he => exact absurd he (by simp)
          | inr hm2 => exact hm2

/-- Replacing the top `p` word-args of the current frame by `q` word-results (`op`). -/
theorem GoodStack.opFrame {prog C} {args rets : List U256} {σ : List AVal} {c₀ c₁ : List Asm}
    {S : StkLayout} {p q : Nat}
    (h : GoodStack prog C (words args ++ σ) c₀) (h0 : C.fl c₀ = some S)
    (hp : p ≤ S.length) (hargs : args.length = p) (hrets : rets.length = q)
    (h1 : C.fl c₁ = some (List.replicate q Slot.word ++ S.drop p))
    (hfb : C.fbMax c₁ = C.fbMax c₀) : GoodStack prog C (words rets ++ σ) c₁ := by
  cases h with
  | @root vσ c S' hfl hfb0 hm =>
      obtain rfl := Option.some.inj (h0 ▸ hfl)
      obtain ⟨Sargs, Sσ, rfl, hMargs, hMσ⟩ := hm.append_inv
      have hSalen : Sargs.length = p := by rw [← hMargs.length_eq, words_length, hargs]
      have hdrop : (Sargs ++ Sσ).drop p = Sσ := by
        rw [← hSalen, List.drop_left]
      refine .root h1 (by rw [hfb, hfb0]) ?_
      rw [hdrop, ← hrets]
      exact (StkMatch.replicate_word rets).append hMσ
  | @call stk frame rest c cRet S' Sret F lRet hfl hfb0 hm hmem hfindR hle hres heq =>
      obtain rfl := Option.some.inj (h0 ▸ hfl)
      have hfrlen : frame.length = S.length := hm.length_eq
      have hple : args.length ≤ frame.length := by rw [hfrlen, hargs]; exact hp
      -- split the frame at the args
      have hwa : words args = frame.take args.length := by
        have := congrArg (List.take args.length) heq
        rwa [List.take_left' (by rw [words_length]), List.take_append_of_le_length hple] at this
      have hσ : σ = frame.drop args.length ++ rest := by
        have := congrArg (List.drop args.length) heq
        rwa [List.drop_left' (by rw [words_length]), List.drop_append_of_le_length hple] at this
      -- frame = words args ++ frame.drop args.length
      have hframe : frame = words args ++ frame.drop args.length := by
        rw [hwa]; exact (List.take_append_drop args.length frame).symm
      rw [hframe] at hm
      obtain ⟨Sa, Sf, hSeq, hMa, hMf⟩ := hm.append_inv
      have hSalen : Sa.length = p := by rw [← hMa.length_eq, words_length, hargs]
      have hSdrop : S.drop p = Sf := by rw [hSeq, ← hSalen, List.drop_left]
      refine .call (lRet := lRet) (frame := words rets ++ frame.drop args.length) h1
        (by rw [hfb, hfb0]) ?_ ?_ hfindR hle hres ?_
      · rw [hSdrop, ← hrets]; exact (StkMatch.replicate_word rets).append hMf
      · -- return address ∈ words rets ++ frame.drop args.length
        rw [hframe] at hmem
        cases (List.mem_append.mp hmem) with
        | inl hin => exact absurd hin (by simp [words])
        | inr hin => exact List.mem_append.mpr (Or.inr hin)
      · rw [hσ, ← List.append_assoc]

/-- The swapped StkMatch for a frame `x :: (τ ++ y :: ρf)` matching `sx :: (Sτ ++ sy :: Sρ)`
(`swap`, within-frame). -/
theorem StkMatch.swap_build {prog H} {x y : AVal} {τ ρf : List AVal} {sx sy : Slot}
    {Sτ Sρ : StkLayout} (hm : StkMatch prog H (x :: (τ ++ y :: ρf)) (sx :: (Sτ ++ sy :: Sρ)))
    (hτlen : Sτ.length = τ.length) :
    StkMatch prog H (y :: (τ ++ x :: ρf)) (sy :: (Sτ ++ sx :: Sρ)) := by
  obtain ⟨hx, hm1⟩ := hm.cons_inv
  obtain ⟨S1, S2, hSsplit, hMτ, hM2⟩ := hm1.append_inv
  have hlen : Sτ.length = S1.length := by rw [hτlen, hMτ.length_eq]
  obtain ⟨rfl, rfl⟩ := List.append_inj hSsplit hlen
  obtain ⟨hy, hMρ⟩ := hM2.cons_inv
  exact StkMatch.consMatch hy (hMτ.append (StkMatch.consMatch hx hMρ))

/-- Membership survives the frame swap. -/
theorem swap_mem {α} [DecidableEq α] {x y z : α} {τ ρf : List α}
    (h : z ∈ x :: (τ ++ y :: ρf)) : z ∈ y :: (τ ++ x :: ρf) := by
  simp only [List.mem_cons, List.mem_append] at h ⊢; tauto

/-- Swapping the top with a within-frame cell (`swap`). -/
theorem GoodStack.swapFrame {prog C} {x y : AVal} {τ ρ : List AVal} {c₀ c₁ : List Asm}
    {sx sy : Slot} {Sτ Sρ : StkLayout}
    (h : GoodStack prog C (x :: (τ ++ y :: ρ)) c₀)
    (h0 : C.fl c₀ = some (sx :: (Sτ ++ sy :: Sρ))) (hτlen : Sτ.length = τ.length)
    (h1 : C.fl c₁ = some (sy :: (Sτ ++ sx :: Sρ))) (hfb : C.fbMax c₁ = C.fbMax c₀) :
    GoodStack prog C (y :: (τ ++ x :: ρ)) c₁ := by
  cases h with
  | @root σ' c' S' hfl hfb0 hm =>
      obtain rfl : sx :: (Sτ ++ sy :: Sρ) = S' := Option.some.inj (h0.symm.trans hfl)
      exact .root h1 (by rw [hfb, hfb0]) (hm.swap_build hτlen)
  | @call stk frame rest c' cRet S' Sret F lRet hfl hfb0 hm hmem hfindR hle hres heq =>
      obtain rfl : sx :: (Sτ ++ sy :: Sρ) = S' := Option.some.inj (h0.symm.trans hfl)
      -- frame = fx :: (fτ ++ fy :: fρ) via head + layout-append + head inversions
      obtain ⟨fx, frame1, rfl, hSMfx, hm1⟩ := hm.cons_inv'
      obtain ⟨fτ, frame2, rfl, hMfτ, hM2⟩ := hm1.append_inv_layout
      obtain ⟨fy, fρ, rfl, hSMfy, hMfρ⟩ := hM2.cons_inv'
      -- reconcile with x :: (τ ++ y :: ρ) = frame ++ rest
      rw [List.cons_append, List.append_assoc, List.cons_append] at heq
      obtain ⟨rfl, hrest⟩ := List.cons.inj heq
      obtain ⟨rfl, rfl, rfl⟩ :=
        list_split_uniq hrest (by rw [hMfτ.length_eq, hτlen])
      refine .call (lRet := lRet) (frame := y :: (τ ++ x :: fρ)) h1 (by rw [hfb, hfb0]) ?_ ?_
        hfindR hle hres ?_
      · exact StkMatch.consMatch hSMfy (hMfτ.append (StkMatch.consMatch hSMfx hMfρ))
      · exact swap_mem hmem
      · rw [List.cons_append, List.append_assoc, List.cons_append]

variable [model : ExternalModel]

set_option warningAsError false in
/-- **Preservation** (WIP). Intra-frame + `op` + `dup` + `swap` proven; `call`/`dynJump` remain. -/
theorem GoodStack.step {prog : List Asm} {C : Cert} (hV : C.Valid prog)
    {a b : AConf} (hstep : AStep (model := model) prog a b) (hsuf : a.code <:+ prog)
    (hinv : GoodStack prog C a.stk a.code) :
    GoodStack prog C b.stk b.code := by
  cases hstep with
  | @push v c σ yst =>
      obtain ⟨S, F, hfl, hfb⟩ := hinv.certAt
      obtain ⟨hflc, hfbc⟩ := hV _ c S F hfl hfb
      exact hinv.growWord hfl hflc (by rw [hfbc, hfb])
  | @pushLabel l c σ yst hdef =>
      obtain ⟨S, F, hfl, hfb⟩ := hinv.certAt
      obtain ⟨t, hfind, hflc, hfbc⟩ := hV _ c S F hfl hfb
      exact hinv.growCode hfl hflc hfind (by rw [hfbc, hfb])
  | @pop v σ c yst =>
      obtain ⟨S, F, hfl, hfb⟩ := hinv.certAt
      obtain ⟨S', hSeq, hflc, hfbc⟩ := hV _ c S F hfl hfb
      subst hSeq
      exact hinv.shrinkWord hfl hflc (by rw [hfbc, hfb])
  | @label l c σ yst =>
      obtain ⟨S, F, hfl, hfb⟩ := hinv.certAt
      obtain ⟨hflc, hfbc⟩ := hV _ c S F hfl hfb
      exact hinv.same (by rw [hflc, hfl]) (by rw [hfbc, hfb])
  | @jump l c c' σ yst hfind =>
      obtain ⟨S, F, hfl, hfb⟩ := hinv.certAt
      have hstep := hV _ c S F hfl hfb
      cases hstep with
      | inl hlocal =>
          obtain ⟨t, hfind', hflc, hfbc⟩ := hlocal
          rw [hfind] at hfind'; obtain rfl := Option.some.inj hfind'
          exact hinv.same (by rw [hflc, hfl]) (by rw [hfbc, hfb])
      | inr _ => sorry  -- WIP: the call case
  | @dup n v τ ρ c yst hτ =>
      obtain ⟨S, F, hfl, hfb⟩ := hinv.certAt
      obtain ⟨sl, hidx, hflc, hfbc⟩ := hV _ c S F hfl hfb
      have hvidx : (τ ++ v :: ρ)[n.val]? = some v := by
        rw [← hτ, List.getElem?_append_right (Nat.le_refl _)]; simp
      have hsm : SlotMatchP prog v sl := hinv.slotMatchAt hfl hvidx hidx
      cases sl with
      | word =>
          cases v with
          | word w => exact hinv.growWord hfl hflc (by rw [hfbc, hfb])
          | code l => exact absurd hsm (by simp [SlotMatchP])
      | code t =>
          cases v with
          | word w => exact absurd hsm (by simp [SlotMatchP])
          | code l => exact hinv.growCode hfl hflc hsm (by rw [hfbc, hfb])
  | @swap n x y τ ρ c yst hτ =>
      obtain ⟨S, F, hfl, hfb⟩ := hinv.certAt
      obtain ⟨sx, mid, sy, restL, hSeq, hmidlen, hflc, hfbc⟩ := hV _ c S F hfl hfb
      subst hSeq
      -- mid.length = n.val = τ.length
      have hτlen : mid.length = τ.length := by rw [hmidlen, hτ]
      exact hinv.swapFrame hfl hτlen hflc (by rw [hfbc, hfb])
  | @jumpiTaken l v c c' σ yst hv hfind =>
      obtain ⟨S, F, hfl, hfb⟩ := hinv.certAt
      obtain ⟨S', hSeq, ⟨t, hfind', hflt, hfbt⟩, _, _⟩ := hV _ c S F hfl hfb
      subst hSeq
      rw [hfind] at hfind'; obtain rfl := Option.some.inj hfind'
      exact hinv.shrinkWord hfl hflt (by rw [hfbt, hfb])
  | @jumpiFall l v c σ yst hv =>
      obtain ⟨S, F, hfl, hfb⟩ := hinv.certAt
      obtain ⟨S', hSeq, _, hflc, hfbc⟩ := hV _ c S F hfl hfb
      subst hSeq
      exact hinv.shrinkWord hfl hflc (by rw [hfbc, hfb])
  | @op yop args rets c σ yst yst' hstepOp =>
      obtain ⟨S, F, hfl, hfb⟩ := hinv.certAt
      obtain ⟨o, hop, hple, hflc, hfbc⟩ := hV _ c S F hfl hfb
      obtain ⟨hargs, hrets⟩ := builtin_arity hop hstepOp
      exact hinv.opFrame hfl hple hargs hrets hflc (by rw [hfbc, hfb])
  | @dynJump l c c' σ yst hfind => sorry

/-- **The invariant holds at every reachable configuration.** -/
theorem GoodStack.reach {prog : List Asm} {C : Cert} (hV : C.Valid prog)
    {a b : AConf} (hsteps : ASteps (model := model) prog a b) (hsuf : a.code <:+ prog)
    (hinv : GoodStack prog C a.stk a.code) :
    GoodStack prog C b.stk b.code := by
  induction hsteps with
  | refl => exact hinv
  | head hstep _ ih => exact ih (hstep.suffix hsuf) (GoodStack.step hV hstep hsuf hinv)

/-- **The run stack-bound**, in the shape the Phase-B lemmas consume. -/
theorem run_stack_bound2 {prog : List Asm} {C : Cert} (hV : C.Valid prog) (hb : C.Bounded)
    (h0fl : C.fl prog = some []) (h0fb : C.fbMax prog = some 0) (yst : EvmState) :
    ∀ mid, ASteps (model := model) prog ⟨prog, [], yst⟩ mid → mid.stk.length ≤ 1023 :=
  fun _ hsteps =>
    (GoodStack.reach hV hsteps (List.suffix_refl _) (GoodStack.entry h0fl h0fb)).bound hb

end YulEvmCompiler
