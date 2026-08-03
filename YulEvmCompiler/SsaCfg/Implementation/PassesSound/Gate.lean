import YulEvmCompiler.SsaCfg.Implementation.PassesSound.Common
set_option warningAsError true

/-!
# YulEvmCompiler.SsaCfg.Implementation.PassesSound.Gate

Purity leaves and the pipeline gate.

What `Passes.pureOp` buys at runtime (`evalPure_stepOp`,
`evalPure_transport`), and the two branches of the defensive
`optimizeProg` gate, including the location-indexed caller replay the
inliner's soundness proof is stated against.
-/

namespace YulEvmCompiler.SsaCfg
open YulSemantics.EVM (U256 EvmState Op builtinWithExternal stepOp ExternalCalls
  ExternalCreates)
open YulSemantics (Outcome)

/-! ## Purity leaves

Everything the value-level passes need about built-ins comes from the pinned
dialect's own `effects_sound_withExternal`: a `pure` op (per the dialect's
`effects` table, which is what `Passes.pureOp` reads) is deterministic,
non-reading, non-writing and non-halting. -/

namespace Passes

def removedBlock (bi i j : Nat) (b : Block) : Block :=
  let b0 := if j = bi then { b with params := b.params.eraseIdx i } else b
  { b0 with term := mapEdges (fun e =>
    if e.target = bi then { e with args := e.args.eraseIdx i } else e) b0.term }

theorem pureOp_flags {yop : Op} (h : pureOp yop = true) :
    (YulSemantics.EVM.effects yop).deterministic = true
    ∧ (YulSemantics.EVM.effects yop).reads = false
    ∧ (YulSemantics.EVM.effects yop).writes = false
    ∧ (YulSemantics.EVM.effects yop).halts = false := by
  simp only [pureOp, YulSemantics.Effects.pure, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- A pure built-in is never one of the open-world operations (`call`-family,
`create`-family, `gas`), so its combined local/external relation is exactly the
executable `stepOp` graph — which is what `evalPure` folds with. -/
theorem builtin_of_pure {calls : ExternalCalls} {creates : ExternalCreates} {yop : Op}
    (h : pureOp yop = true) {args : List U256} {st : EvmState}
    {r : YulSemantics.BuiltinResult U256 EvmState} :
    builtinWithExternal calls creates yop args st r ↔ stepOp yop args st = some r := by
  cases yop <;> first
    | exact Iff.rfl
    | (exfalso; revert h; decide)

/-- A pure built-in leaves the machine state untouched. -/
theorem pure_state_eq {calls : ExternalCalls} {creates : ExternalCreates} {yop : Op}
    (hp : pureOp yop = true) {args : List U256} {st st' : EvmState} {rets : List U256}
    (hb : builtinWithExternal calls creates yop args st (.ok rets st')) : st' = st :=
  (YulSemantics.EVM.effects_sound_withExternal calls creates).write yop
    (pureOp_flags hp).2.2.1 args st (.ok rets st') hb

/-- **CSE leaf**: a pure built-in's results are a function of its arguments
alone, so two evaluations of the same `(op, args)` — in *any* two states, hence
at any two program points — return the same values. -/
theorem pure_rets_eq {calls : ExternalCalls} {creates : ExternalCreates} {yop : Op}
    (hp : pureOp yop = true) {args : List U256} {st1 st2 st1' st2' : EvmState}
    {rets1 rets2 : List U256}
    (h1 : builtinWithExternal calls creates yop args st1 (.ok rets1 st1'))
    (h2 : builtinWithExternal calls creates yop args st2 (.ok rets2 st2')) : rets1 = rets2 :=
  (YulSemantics.EVM.effects_sound_withExternal calls creates).read yop
    (pureOp_flags hp).2.1 args st1 st2 rets1 st1' rets2 st2' h1 h2

/-- Invert a successful `evalPure`: the folder saw a clean single-value return
from the dialect's own step function on the initial state. -/
theorem evalPure_stepOp {yop : Op} {args : List U256} {v : U256}
    (h : evalPure yop args = some v) :
    ∃ st', stepOp yop args YulSemantics.EVM.EvmState.init = some (.ok [v] st') := by
  unfold evalPure at h
  rw [ite_eq_iff] at h
  rcases h with ⟨-, h⟩ | ⟨-, h⟩
  · exact absurd h (by simp)
  · rcases hs : stepOp yop args YulSemantics.EVM.EvmState.init with _ | r <;> rw [hs] at h
    · exact absurd h (by simp)
    · rcases r with ⟨rets, st'⟩ | st'
      · rcases rets with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> simp at h
        exact ⟨st', by rw [h]⟩
      · exact absurd h (by simp)

/-- **Constant-folding leaf**: whatever the folder computed on `EvmState.init` is
what the built-in returns in *any* state, and the state is untouched. This is the
transport that lets `constFold` replace `.op [d] yop args` by `.const d v`. -/
theorem evalPure_transport {calls : ExternalCalls} {creates : ExternalCreates} {yop : Op}
    (hp : pureOp yop = true) {args : List U256} {v : U256}
    (he : evalPure yop args = some v) {st st' : EvmState} {rets : List U256}
    (hb : builtinWithExternal calls creates yop args st (.ok rets st')) :
    rets = [v] ∧ st' = st := by
  obtain ⟨s0, hstep⟩ := evalPure_stepOp he
  have hb0 : builtinWithExternal calls creates yop args YulSemantics.EVM.EvmState.init
      (.ok [v] s0) := (builtin_of_pure hp).mpr hstep
  exact ⟨pure_rets_eq hp hb hb0, pure_state_eq hp hb⟩

end Passes


/-! ## The pipeline gate

`optimizeProg` tentatively runs `inlineProg` (program-level function inlining),
uses the result only if an intermediate `wfCheck && domCheck` gate accepts it,
then runs the per-function four-pass pipeline and applies the final defensive
gate. Naming the gated input and candidate keeps the lemmas below (and the
top-level proof) independent of the exact pipeline shape. -/

/-- The input to the per-function pipeline, after the intermediate defensive
gate around inlining. -/
def optimizeInput (P : Prog) : Prog :=
  let P0 := Passes.inlineProg P
  if P0.wfCheck && ToAsm.Prog.domCheck P0 then P0 else P

/-- The pipeline's output *before* the defensive gate. -/
def optimizeCandidate (P : Prog) : Prog :=
  let P0 := Passes.inlineProg P
  let P0 := if P0.wfCheck && ToAsm.Prog.domCheck P0 then P0 else P
  { main := optimizeFunc P0.main, funcs := P0.funcs.map optimizeFunc }

/-- `optimizeProg`, refactored through `optimizeCandidate`. Definitional: this
is the single place that tracks the pipeline's shape. -/
theorem optimizeProg_candidate (P : Prog) :
    optimizeProg P =
      if (optimizeCandidate P).wfCheck && ToAsm.Prog.domCheck (optimizeCandidate P)
      then optimizeCandidate P else P := rfl

/-- Gate rejected ⇒ the optimizer is the identity. -/
theorem optimizeProg_of_gate_false {P : Prog}
    (h : ((optimizeCandidate P).wfCheck && ToAsm.Prog.domCheck (optimizeCandidate P)) = false) :
    optimizeProg P = P := by
  rw [optimizeProg_candidate, h]; simp

/-- Gate accepted ⇒ the optimizer is the candidate. -/
theorem optimizeProg_of_gate_true {P : Prog}
    (h : ((optimizeCandidate P).wfCheck && ToAsm.Prog.domCheck (optimizeCandidate P)) = true) :
    optimizeProg P = optimizeCandidate P := by
  rw [optimizeProg_candidate, h]; simp

section
variable [model : ExternalModel]

/-! ### Location-indexed caller replay

The source caller location is a block id together with the number of
instructions already consumed in that block.  This is deliberately positional:
the instruction at the selected site need not be syntactically unique. -/

/-- The rest corresponding to source location `(j,k)` after splicing the call
at `(bi,ci)`.  Locations before (or at) the call run the remaining prefix and
then jump into the copied callee; locations after it are continuations and all
other locations are unchanged. -/
def Passes.inlineCallerRest (bi ci calleeEntry j k : Nat) (site : Block)
    (r : Rest) : Rest :=
  if j = bi ∧ k ≤ ci then
    ⟨(site.instrs.take ci).drop k, .jump ⟨calleeEntry, []⟩⟩
  else r

omit model in
theorem Passes.inlineCallerBlock_get_site {f f' : Func} {bi : Nat}
    {callBlock : Block} {tail : Array Block}
    (hbi : bi < f.blocks.size)
    (hblocks : f'.blocks = (f.blocks.set! bi callBlock) ++ tail) :
    f'.blocks[bi]? = some callBlock := by
  rw [hblocks, Array.getElem?_append_left (by simp [hbi])]
  simp [Array.set!, hbi]

omit model in
theorem Passes.inlineCallerBlock_get_other {f f' : Func} {bi j : Nat}
    {callBlock b : Block} {tail : Array Block}
    (hj : f.blocks[j]? = some b) (hne : j ≠ bi)
    (hblocks : f'.blocks = (f.blocks.set! bi callBlock) ++ tail) :
    f'.blocks[j]? = some b := by
  have hjlt : j < f.blocks.size := (Array.getElem?_eq_some_iff.mp hj).1
  rw [hblocks, Array.getElem?_append_left (by simp [hjlt])]
  simpa [Array.set!, Array.getElem?_setIfInBounds_ne (Ne.symm hne)] using hj

omit model in
theorem Passes.inlineCallerBlock_get_site₂ {f f' : Func} {bi : Nat}
    {callBlock : Block} {mid tail : Array Block}
    (hbi : bi < f.blocks.size)
    (hblocks : f'.blocks = (f.blocks.set! bi callBlock) ++ mid ++ tail) :
    f'.blocks[bi]? = some callBlock := by
  rw [hblocks, Array.getElem?_append_left (by simp; omega),
    Array.getElem?_append_left (by simp [hbi])]
  simp [Array.set!, hbi]

omit model in
theorem Passes.inlineCallerBlock_get_other₂ {f f' : Func} {bi j : Nat}
    {callBlock b : Block} {mid tail : Array Block}
    (hj : f.blocks[j]? = some b) (hne : j ≠ bi)
    (hblocks : f'.blocks = (f.blocks.set! bi callBlock) ++ mid ++ tail) :
    f'.blocks[j]? = some b := by
  have hjlt : j < f.blocks.size := (Array.getElem?_eq_some_iff.mp hj).1
  rw [hblocks, Array.getElem?_append_left (by simp; omega),
    Array.getElem?_append_left (by simp [hjlt])]
  simpa [Array.set!, Array.getElem?_setIfInBounds_ne (Ne.symm hne)] using hj

omit model in
theorem Passes.wfCheck_entry_params_nil {f : Func} {n : Nat}
    (hwf : f.wfCheck n = true) {b : Block}
    (hb : f.blocks[f.entry]? = some b) : b.params = [] := by
  unfold Func.wfCheck at hwf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hwf
  simpa [hb] using hwf.1.2

omit model in
theorem Passes.wfCheck_ret_arity {f : Func} {n : Nat}
    (hwf : f.wfCheck n = true) {b : Block} (hb : b ∈ f.blocks.toList)
    {xs : List ValId} (ht : b.term = .ret xs) : xs.length = f.nrets := by
  unfold Func.wfCheck at hwf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hwf
  have hblock := Array.all_eq_true_iff_forall_mem.mp hwf.2 b (by simpa using hb)
  simp only [Bool.and_eq_true] at hblock
  simpa [ht] using hblock.1.1

/-- The fallback branch of pass soundness, fully proved. -/
theorem optimizeProg_sound_of_fallback {P : Prog} {yst0 yst' : EvmState} {o : Outcome}
    (h : ((optimizeCandidate P).wfCheck && ToAsm.Prog.domCheck (optimizeCandidate P)) = false)
    (hrun : Run (model := model) P yst0 yst' o) :
    Run (model := model) (optimizeProg P) yst0 yst' o := by
  rw [optimizeProg_of_gate_false h]; exact hrun

end

end YulEvmCompiler.SsaCfg
