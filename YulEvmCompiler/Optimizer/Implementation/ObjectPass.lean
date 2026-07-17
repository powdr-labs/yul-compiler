import YulEvmCompiler.Optimizer.Spec.Pass
import YulEvmCompiler.Optimizer.Implementation.Simplify
import YulEvmCompiler.Optimizer.Implementation.ResolveCongr
import YulEvmCompiler.ObjectCompile

/-!
# YulEvmCompiler.Optimizer.Implementation.ObjectPass

Running a verified `Optimizer.Pass` on an **object's** top code block, and the
correctness theorem for doing so — the object analogue of
`Pass.optimize_then_compile_correct`.

## The layout-coupling caveat

Unlike the block path, an object compiler couples the *compiled length* of a code
block to the byte **offsets** of the object's sub-objects and data segments
(`planObject` derives every offset from the top block's `codeSize`), and
`resolveForLayoutStmts` bakes those offsets into the code as `PUSH32` literals.
So optimizing code that any `dataoffset`/`datasize`/`datacopy` observes shifts the
layout, and there is no `EquivBlock`-congruence for resolution to bridge the two
layouts.

The clean, provable statement is therefore restricted to the fragment where
resolution is the *identity* on the (optimized) top code block — i.e. the top
block makes no layout references (`hres₀`/`hres₁` below), which holds for leaf
objects and for runtime code that neither `datacopy`s a sub-object nor reads a
`dataoffset`/`datasize`. Extending it to the constructor→runtime nesting of real
Solidity output requires a genuine cross-layout object equivalence (relating the
offsets an optimization shifts); that is logged in `IDEAS.md` as the object-path
frontier. See that log for the full analysis.
-/

namespace YulEvmCompiler.Optimizer

open EvmSemantics EvmSemantics.EVM
open YulSemantics (VEnv Run Outcome Block Object)
open YulSemantics.EVM (EvmState evmWithExternal Op Layout)

variable [model : ExternalModel]
local notation "yulD" => evmWithExternal model.calls model.creates

/-- Apply a pass to an object's **top** code block, leaving sub-objects and data
segments byte-identical (so their compiled lengths — and hence every layout
offset derived from them — are unchanged). -/
def Pass.optimizeTopCode (P : Pass yulD) : Object Op → Object Op
  | .mk n code subs segs => .mk n (P.run code) subs segs

@[simp] theorem Pass.optimizeTopCode_codeBlock (P : Pass yulD) (o : Object Op) :
    (P.optimizeTopCode o).codeBlock = P.run o.codeBlock := by
  cases o; rfl

/-- **A verified pass is safe on an object's top code block** — provided
resolution is the identity on the top block (no layout references), so the pass
does not perturb any baked-in offset. Then compiling the optimized object
correctly simulates the *original* object's resolved execution.

This is `compileObject_correct` precomposed with the pass's semantics
preservation (`Pass.run_optimized`), exactly as
`Pass.optimize_then_compile_correct` does for the block path. -/
theorem Pass.optimizeTop_compileObject_correct
    (P : Pass yulD) (hexternal : ExternalsRealized model)
    {o : Object Op} {L : Layout}
    (hcomp : compileObject (P.optimizeTopCode o) = some L)
    (hres₀ : resolveForLayoutStmts L o.codeBlock = o.codeBlock)
    (hres₁ : resolveForLayoutStmts L (P.run o.codeBlock) = P.run o.codeBlock)
    {V : VEnv yulD} {yst : EvmState} {out : Outcome}
    (hrun : RunResolvedObject o L V yst out) :
    ∃ b : Nat, ∀ s0 : State,
      FrameOK (mkCode L.code) s0 → StateMatch L.initState s0 →
      s0.pc = UInt256.ofNat 0 → s0.stack = [] → b ≤ s0.gasAvailable →
      ∃ s', Steps s0 s' ∧ s'.callStack = [] ∧ StateMatch yst s' ∧
        ((out = .normal ∧ s'.halt = .Success ∧ s'.hReturn = .empty) ∨
         (out = .halt ∧ HaltedMatch yst s')) := by
  -- Transport the original run onto the raw top block, then across the pass.
  have h0 : Run yulD o.codeBlock L.initState V yst out := by
    have h := hrun
    change Run yulD (resolveForLayoutStmts L o.codeBlock) L.initState V yst out at h
    rw [hres₀] at h; exact h
  have h1 : Run yulD (P.run o.codeBlock) L.initState V yst out := P.run_optimized h0
  have hrr : RunResolvedObject (P.optimizeTopCode o) L V yst out := by
    change Run yulD (resolveForLayoutStmts L (P.optimizeTopCode o).codeBlock) L.initState V yst out
    rw [P.optimizeTopCode_codeBlock, hres₁]; exact h1
  exact compileObject_correct hexternal hcomp hrr

/-! ### Whole-tree optimization (`simplifyObject`), wired into `compileSource`

`simplifyObject` (in `Simplify`) runs the pass on **every** code block of an
object tree — the deploy object *and* every nested sub-object (the `*_deployed`
runtime of a Solidity artifact). The soundness this delivers is exactly the
object analogue of the block path:

* **the artifact is a verified compilation** of the optimized tree
  (`simplifyObject_compileObject_correct`, below — `compileObject_correct` on
  `simplifyObject o`); and
* **every code block is semantics-preserved** — each object's top code block is
  `EquivBlock`-equivalent to the original (`simplifyObject_topEquiv`, from
  `blockEquiv`), and this holds at every level of the tree because
  `compileObject` compiles sub-objects with the same pass applied.

So the emitted bytecode faithfully runs a program each of whose code blocks is
provably equivalent to the source. (A single end-to-end "bytecode simulates the
*original* object" theorem would additionally need a resolution congruence
`EquivBlock (resolveForLayoutStmts L b) (resolveForLayoutStmts L (P.run b))`,
which the layout-coupling above blocks in general — see `IDEAS.md`.) -/

/-- **The artifact from `simplifyObject` is verified.** Compiling the whole-tree
optimized object correctly simulates its resolved execution — `compileObject_correct`
applied to `simplifyObject o`. -/
theorem simplifyObject_compileObject_correct (hexternal : ExternalsRealized model)
    {o : Object Op} {L : Layout}
    (hcomp : compileObject (simplifyObject o) = some L)
    {V : VEnv yulD} {yst : EvmState} {out : Outcome}
    (hrun : RunResolvedObject (simplifyObject o) L V yst out) :
    ∃ b : Nat, ∀ s0 : State,
      FrameOK (mkCode L.code) s0 → StateMatch L.initState s0 →
      s0.pc = UInt256.ofNat 0 → s0.stack = [] → b ≤ s0.gasAvailable →
      ∃ s', Steps s0 s' ∧ s'.callStack = [] ∧ StateMatch yst s' ∧
        ((out = .normal ∧ s'.halt = .Success ∧ s'.hReturn = .empty) ∨
         (out = .halt ∧ HaltedMatch yst s')) :=
  compileObject_correct hexternal hcomp hrun

/-- **Each object's top code block is semantics-preserved** by `simplifyObject`:
it is `EquivBlock`-equivalent to the original. (`RunObject`/`RunResolvedObject`
depend only on an object's top code block, so this is the operative guarantee at
every level of the tree.) -/
theorem simplifyObject_topEquiv (o : Object Op) :
    YulSemantics.EquivBlock yulD o.codeBlock (simplifyObject o).codeBlock := by
  rw [simplifyObject_codeBlock]; exact blockEquiv o.codeBlock

/-- **End-to-end object optimization is correct.** Compiling `simplifyObject o`
(the whole tree optimized — deploy and runtime) yields bytecode that correctly
simulates the **original** object `o`'s resolved execution under the compiler's
layout. This is the object analogue of `Pass.optimize_then_compile_correct`, now
with no caveat: the resolution congruence (`resolveSimplifyBlock_equiv`) bridges
the optimized artifact's resolved run back to the original's. -/
theorem simplifyObject_correct (hexternal : ExternalsRealized model)
    {o : Object Op} {L : Layout}
    (hcomp : compileObject (simplifyObject o) = some L)
    {V : VEnv yulD} {yst : EvmState} {out : Outcome}
    (hrun : RunResolvedObject o L V yst out) :
    ∃ b : Nat, ∀ s0 : State,
      FrameOK (mkCode L.code) s0 → StateMatch L.initState s0 →
      s0.pc = UInt256.ofNat 0 → s0.stack = [] → b ≤ s0.gasAvailable →
      ∃ s', Steps s0 s' ∧ s'.callStack = [] ∧ StateMatch yst s' ∧
        ((out = .normal ∧ s'.halt = .Success ∧ s'.hReturn = .empty) ∨
         (out = .halt ∧ HaltedMatch yst s')) := by
  have hb := resolveSimplifyBlock_equiv (calls := model.calls) (creates := model.creates)
    L o.codeBlock
  have hrun' : RunResolvedObject (simplifyObject o) L V yst out := by
    show Run yulD (resolveForLayoutStmts L (simplifyObject o).codeBlock) L.initState V yst out
    rw [simplifyObject_codeBlock]
    exact hb.run_iff.mp hrun
  exact compileObject_correct hexternal hcomp hrun'

end YulEvmCompiler.Optimizer
