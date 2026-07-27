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
  | .swap _,      c, S, F => C.fl c = some S ∧ C.fbMax c = some F  -- WIP
  | .label _,     c, S, F => C.fl c = some S ∧ C.fbMax c = some F
  | .op _,        c, S, F => C.fl c = some S ∧ C.fbMax c = some F  -- WIP
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
  | call {stk frame rest : List AVal} {c cPre : List Asm} {S : StkLayout} {F : Nat} {lRet : Label} :
      C.fl c = some S → C.fbMax c = some F → StkMatch prog dH frame S →
      (.code lRet) ∈ frame → rest.length ≤ F → GoodStack prog C rest cPre →
      stk = frame ++ rest →
      GoodStack prog C stk c

/-- Extract the current position's certificate entries (no casing of the stack shape). -/
theorem GoodStack.certAt {prog C} {σ : List AVal} {c : List Asm}
    (h : GoodStack prog C σ c) : ∃ S F, C.fl c = some S ∧ C.fbMax c = some F := by
  cases h with
  | root hfl hfb _ => exact ⟨_, _, hfl, hfb⟩
  | call hfl hfb _ _ _ _ _ => exact ⟨_, _, hfl, hfb⟩

/-- **The bound falls out of the invariant + the certificate.** -/
theorem GoodStack.bound {prog C} (hb : C.Bounded) {σ : List AVal} {c : List Asm}
    (h : GoodStack prog C σ c) : σ.length ≤ 1023 := by
  cases h with
  | @root σ c S hfl hfb hm =>
      have := hb c S 0 hfl hfb
      have hlen := hm.length_eq
      omega
  | @call stk frame rest c cPre S F lRet hfl hfb hm hmem hle _ heq =>
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
  | @call stk frame rest c cPre S F lRet hfl hfb0 hm hmem hle hcaller heq =>
      obtain rfl := Option.some.inj (h0 ▸ hfl)
      refine .call (lRet := lRet) h1 (by rw [hfb, hfb0]) (StkMatch.word (v := v) hm)
        (List.mem_cons_of_mem _ hmem) hle hcaller ?_
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
  | @call stk frame rest c cPre S F lRet hfl hfb0 hm hmem hle hcaller heq =>
      obtain rfl := Option.some.inj (h0 ▸ hfl)
      refine .call (lRet := lRet) h1 (by rw [hfb, hfb0]) (StkMatch.code (l := l) hfind hm)
        (List.mem_cons_of_mem _ hmem) hle hcaller ?_
      rw [heq, List.cons_append]

/-- Moving to a position with the same frame layout and base (`label`, local `jump`). -/
theorem GoodStack.same {prog C} {σ : List AVal} {c₀ c₁ : List Asm}
    (h : GoodStack prog C σ c₀) (hfl : C.fl c₁ = C.fl c₀) (hfb : C.fbMax c₁ = C.fbMax c₀) :
    GoodStack prog C σ c₁ := by
  cases h with
  | @root σ c S hfl0 hfb0 hm =>
      exact .root (by rw [hfl, hfl0]) (by rw [hfb, hfb0]) hm
  | @call stk frame rest c cPre S F lRet hfl0 hfb0 hm hmem hle hcaller heq =>
      exact .call (by rw [hfl, hfl0]) (by rw [hfb, hfb0]) hm hmem hle hcaller heq

/-- Popping a plain word off the current frame (`pop`). -/
theorem GoodStack.shrinkWord {prog C} {σ : List AVal} {c₀ c₁ : List Asm} {S' : StkLayout} {v : AVal}
    (h : GoodStack prog C (v :: σ) c₀) (h0 : C.fl c₀ = some (.word :: S'))
    (h1 : C.fl c₁ = some S') (hfb : C.fbMax c₁ = C.fbMax c₀) : GoodStack prog C σ c₁ := by
  cases h with
  | @root vσ c S hfl hfb0 hm =>
      obtain rfl := Option.some.inj (h0 ▸ hfl)
      cases hm with
      | word hm' => exact .root h1 (by rw [hfb, hfb0]) hm'
  | @call stk frame rest c cPre S F lRet hfl hfb0 hm hmem hle hcaller heq =>
      obtain rfl := Option.some.inj (h0 ▸ hfl)
      cases hm with
      | @word w frame' S'' hm' =>
          rw [List.cons_append] at heq
          obtain ⟨rfl, rfl⟩ := List.cons.inj heq
          refine .call (lRet := lRet) h1 (by rw [hfb, hfb0]) hm' ?_ hle hcaller rfl
          cases List.mem_cons.mp hmem with
          | inl he => exact absurd he (by simp)
          | inr hm2 => exact hm2

variable [model : ExternalModel]

set_option warningAsError false in
/-- **Preservation** (WIP). Intra-frame cases proven; `dup`/`swap`/`op`/`jumpi`/`call`/`dynJump`
remain (`sorry`). -/
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
  | @dup n v τ ρ c yst hτ => sorry
  | @swap n x y τ ρ c yst hτ => sorry
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
  | @op yop args rets c σ yst yst' hstepOp => sorry
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
