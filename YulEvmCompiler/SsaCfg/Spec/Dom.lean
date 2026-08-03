import YulEvmCompiler.SsaCfg.Spec.Ir
set_option warningAsError true
/-!
# YulEvmCompiler.SsaCfg.Spec.Dom

**Liveness and the dominance check** — spec-tier because `Prog.domCheck`
appears in the phase-obligation statements (`Spec/Backend.lean`): the SSA
optimization passes are sound only on dominance-respecting programs, and
this file defines what that means, decidably. The definitions keep the
`ToAsm` namespace they were born in (the code generator is their other
consumer); their physical home is the spec tier because an auditor of the
pass obligations must read them.
-/

namespace YulEvmCompiler.SsaCfg

namespace ToAsm

/-! ## Small sorted-set helpers (`List ValId`, ascending, nodup) -/

def insertSorted (v : ValId) : List ValId → List ValId
  | [] => [v]
  | w :: rest =>
    if v < w then v :: w :: rest
    else if v = w then w :: rest
    else w :: insertSorted v rest

def unionS (xs ys : List ValId) : List ValId :=
  xs.foldl (fun acc v => insertSorted v acc) ys

def diffS (xs ys : List ValId) : List ValId :=
  xs.filter (fun v => !ys.contains v)

/-! ## Liveness -/

/-- Values used by a block (instructions + terminator), as a sorted set. -/
def blockUses (b : Block) : List ValId :=
  unionS (b.instrs.flatMap Instr.uses) (unionS b.term.uses [])

/-- Values defined by a block (params + instruction defs), sorted. -/
def blockDefs (b : Block) : List ValId :=
  unionS (b.params ++ b.instrs.flatMap Instr.defs) []

/-- One backward liveness iteration: `liveIn(b) = uses(b) ∪ (liveOut(b) ∖
defs(b))`, `liveOut(b) = ⋃ liveIn(succ)`. -/
def liveStep (f : Func) (liveIn : Array (List ValId)) : Array (List ValId) :=
  Array.ofFn (n := f.blocks.size) fun i =>
    match f.blocks[i.val]? with
    | none => []
    | some b =>
      let lout := b.term.edges.foldl (init := []) fun acc e =>
        unionS (liveIn[e.target]?.getD []) acc
      -- SSA definitions dominate uses, so a value defined in the block is
      -- never live into it, even when used by the block itself
      diffS (unionS (blockUses b) lout) (blockDefs b)

/-- Iterate liveness to a fixed point (fuel-bounded; rejects on
non-convergence, which cannot happen — the sets grow monotonically inside a
finite universe — but the check keeps this total and honest). -/
def liveInSets (f : Func) : Option (Array (List ValId)) :=
  let total := f.blocks.foldl (init := 0) fun acc b =>
    acc + (blockDefs b).length + (blockUses b).length
  let fuel := f.blocks.size * (total + 1) + 2
  go fuel (Array.replicate f.blocks.size [])
where
  go : Nat → Array (List ValId) → Option (Array (List ValId))
    | 0, _ => none
    | fuel + 1, cur =>
      let next := liveStep f cur
      if next == cur then some cur else go fuel next

/-- **The dominance check** (decidable): under single assignment, every use
is dominated by its definition **iff** no value is live into the entry block
beyond the function's parameters — a non-dominated use induces a
definition-free path from entry, which backward liveness propagates all the
way up. This matters because registers persist across blocks and block
parameters are re-bound on every visit: a non-dominated use is *not* stuck,
it reads a stale binding — so the SSA optimization passes (trivial-parameter
elimination, CSE) are only sound on programs passing this check
(`SsaCfg/PassesSound.lean` has the kernel-checked counterexample without
it). -/
def Func.domCheck (f : Func) : Bool :=
  match liveInSets f with
  | some li => diffS (li[f.entry]?.getD []) f.params = []
  | none => false

/-- `Func.domCheck` over the whole program. -/
def Prog.domCheck (P : Prog) : Bool :=
  Func.domCheck P.main && P.funcs.all Func.domCheck


end ToAsm

end YulEvmCompiler.SsaCfg
