import YulEvmCompiler.AsmSem

set_option warningAsError false  -- WIP: this module carries `sorry` placeholders (not wired in / not audited)
/-!
# YulEvmCompiler.StackScalable — a **scalable** (frame-relative) stack-overflow analysis  [WIP]

`YulEvmCompiler.StackBound` proves the abstract Asm machine never overflows the 1024-word EVM
operand stack, discharged by a checker whose layout map is **context-sensitive** (one absolute
layout per caller context). That checker is *exponential* in call-nesting depth, so it explodes on
real Solidity via-IR output (deeply-nested ABI helpers) — mass rejections and CI timeouts.

This module replaces it with a **frame-relative, context-insensitive** analysis that scales
linearly: each function body is analysed *once*, relative to its own frame, and the total stack
bound is recovered from an acyclic-call-graph base bound. The untrusted solver (`analyze` below,
already validated: `chain 40` fast where the layout solver timed out on `chain 12`; accepts
multiply-called helpers; rejects recursion) proposes a certificate `(rh, fbMax)`; a decidable
checker verifies it; and the invariant `GoodStack` below turns a verified certificate into the
run-time bound.

Status: the untrusted solver + certificate shape + the structural soundness lemmas (`bound`,
`entry`, `reach`) are done; `GoodStack.step` (per-`AStep` preservation) and the decidable checker
are the remaining work (marked `sorry`). See memory `stackbound-retrot-blocker`.
-/

namespace YulEvmCompiler

open EvmSemantics EvmSemantics.EVM
open YulSemantics.EVM (U256 EvmState Op)

/-! ### The untrusted solver (frame-relative; validated fast)

Not part of the trusted base — it only *proposes* a certificate that the checker verifies. Included
here so the certificate it emits is the one the proof consumes. -/

/-- Labels used as a `pushLabel` target = return addresses. -/
def pushLabelled (prog : List Asm) : List Label :=
  prog.filterMap (fun i => match i with | .pushLabel l => some l | _ => none)

/-- Halting ops have no fall-through successor. -/
def isHaltingOp : Op → Bool
  | .stop | .ret | .revert | .invalid | .selfdestruct => true
  | _ => false

/-- Forward frame-relative abstract interpreter. State `(pos, absHeight, callStack)` where each
`callStack` entry is `(frameBase, returnPos, calleeEntry)`. Memo dedups by `(pos, relHeight)` with
`relHeight = absHeight − frameBase` (context-insensitive ⇒ each body explored once ⇒ linear).
Calls are `.jump lentry :: .label lret :: _` with `lret` a return address; recursion (callee already
on the stack) is rejected. Returns the max absolute height, or `none` on reject / overflow. -/
partial def analyzeGo (prog : List Asm) (pls : List Label) :
    Nat → List (List Asm × Nat × List (Nat × List Asm × List Asm)) → List (Nat × List Int) → Nat →
      Option Nat
  | 0, _, _, _ => none
  | _ + 1, [], _, mx => some mx
  | fuel + 1, (pos, absH, cs) :: wl, memo, mx =>
    if absH > 1023 then none else
    let base := (cs.head?.map (·.1)).getD 0
    let rel : Int := (absH : Int) - (base : Int)
    let seen := (memo.find? (fun p => p.1 == pos.length)).map (·.2) |>.getD []
    if seen.contains rel then analyzeGo prog pls fuel wl memo (max mx absH)
    else
      let memo' := if (memo.find? (fun p => p.1 == pos.length)).isSome
                   then memo.map (fun p => if p.1 == pos.length then (p.1, rel :: p.2) else p)
                   else (pos.length, [rel]) :: memo
      let mx' := max mx absH
      let cont (succs) := analyzeGo prog pls fuel (succs ++ wl) memo' mx'
      match pos with
      | [] => cont []
      | i :: c =>
        match i with
        | .push _ => cont [(c, absH + 1, cs)]
        | .dup _ => cont [(c, absH + 1, cs)]
        | .pop => cont [(c, absH - 1, cs)]
        | .swap _ => cont [(c, absH, cs)]
        | .label _ => cont [(c, absH, cs)]
        | .pushLabel _ => cont [(c, absH + 1, cs)]
        | .op yop => if isHaltingOp yop then cont [] else
            match opTable yop with
            | some o => cont [(c, absH - o.popArity + o.pushArity, cs)]
            | none => none
        | .jumpi l => match findLabel l prog with
            | some t => cont [(t, absH - 1, cs), (c, absH - 1, cs)]
            | none => none
        | .jump l => match findLabel l prog with
            | some t =>
                match c with
                | .label lret :: _ =>
                    if pls.contains lret then
                      (if cs.any (fun e => e.2.2 == t) then none
                       else cont [(t, absH, (absH, c, t) :: cs)])
                    else cont [(t, absH, cs)]
                | _ => cont [(t, absH, cs)]
            | none => none
        | .dynJump => match cs with
            | (_, ret, _) :: cs' => cont [(ret, absH - 1, cs')]
            | [] => none

/-- Max reachable absolute operand height, or `none` if the analysis rejects. -/
def analyze (prog : List Asm) : Option Nat :=
  analyzeGo prog (pushLabelled prog) 2000000 [(prog, 0, [])] [] 0

/-! ### The certificate and the invariant

A certificate assigns each position a **relative frame height** `rh` and a **max frame base**
`fbMax` (per-function, from the acyclic-call-graph DP). `CertBounded` is the single fact the bound
needs: the absolute height `fbMax + rh` never exceeds the limit. -/

/-- Certificate: relative height and max-frame-base per code position. -/
structure Cert where
  rh : List Asm → Option Nat
  fbMax : List Asm → Option Nat

/-- The certificate keeps every position's absolute height within the EVM limit. -/
def Cert.Bounded (C : Cert) : Prop :=
  ∀ c n F, C.rh c = some n → C.fbMax c = some F → n + F ≤ 1023

variable [model : ExternalModel]

/-- **The reachable-configuration invariant.** The stack decomposes into the current frame (top
`rh(code)` cells) stacked on the caller chain; each frame's actual base stays within its `fbMax`.
`root` is the bottom (main) frame at base 0; `call` layers a callee frame on a caller that is itself
`GoodStack` at its suspended (pre-call) position. The return address `.code lRet` lives somewhere in
the current frame (it moves during the `retRot` epilogue) and resolves to the caller's resume point.
-/
inductive GoodStack (prog : List Asm) (C : Cert) : List AVal → List Asm → Prop
  | root {σ : List AVal} {c : List Asm} {n : Nat} :
      C.rh c = some n → C.fbMax c = some 0 → σ.length = n →
      GoodStack prog C σ c
  | call {frame rest : List AVal} {c cPre cRet : List Asm} {n F : Nat} {lRet : Label} :
      C.rh c = some n → C.fbMax c = some F → frame.length = n →
      (.code lRet) ∈ frame → findLabel lRet prog = some cRet →
      rest.length ≤ F →
      GoodStack prog C rest cPre →
      GoodStack prog C (frame ++ rest) c

omit model in
/-- **The bound falls out of the invariant + the certificate.** -/
theorem GoodStack.bound {prog C} (hb : C.Bounded) {σ : List AVal} {c : List Asm}
    (h : GoodStack prog C σ c) : σ.length ≤ 1023 := by
  cases h with
  | @root σ c n hrh hfb hlen =>
      have := hb c n 0 hrh hfb; omega
  | @call frame rest c cPre cRet n F lRet hrh hfb hfl _ _ hle _ =>
      have hbnd := hb c n F hrh hfb
      have : (frame ++ rest).length = n + rest.length := by rw [List.length_append, hfl]
      omega

omit model in
/-- The entry configuration is `GoodStack`, provided the certificate assigns the whole program the
root frame (relative height 0, base 0). -/
theorem GoodStack.entry {prog C} (h0rh : C.rh prog = some 0) (h0fb : C.fbMax prog = some 0) :
    GoodStack prog C [] prog :=
  .root h0rh h0fb rfl

set_option warningAsError false in
/-- **Preservation** (WIP). `GoodStack` is preserved by every `AStep`, given a valid certificate.
The certificate-validity hypothesis and the per-`AStep` case analysis are the remaining work. -/
theorem GoodStack.step {prog : List Asm} {C : Cert}
    {a b : AConf} (hstep : AStep (model := model) prog a b) (hsuf : a.code <:+ prog)
    (hinv : GoodStack prog C a.stk a.code) :
    GoodStack prog C b.stk b.code := by
  sorry

/-- **The invariant holds at every reachable configuration.** -/
theorem GoodStack.reach {prog : List Asm} {C : Cert}
    {a b : AConf} (hsteps : ASteps (model := model) prog a b) (hsuf : a.code <:+ prog)
    (hinv : GoodStack prog C a.stk a.code) :
    GoodStack prog C b.stk b.code := by
  induction hsteps with
  | refl => exact hinv
  | head hstep _ ih => exact ih (hstep.suffix hsuf) (GoodStack.step hstep hsuf hinv)

/-- **The run stack-bound**, in the shape the Phase-B lemmas consume. -/
theorem run_stack_bound2 {prog : List Asm} {C : Cert} (hb : C.Bounded)
    (h0rh : C.rh prog = some 0) (h0fb : C.fbMax prog = some 0) (yst : EvmState) :
    ∀ mid, ASteps (model := model) prog ⟨prog, [], yst⟩ mid → mid.stk.length ≤ 1023 :=
  fun _ hsteps =>
    (GoodStack.reach hsteps (List.suffix_refl _) (GoodStack.entry h0rh h0fb)).bound hb

end YulEvmCompiler
