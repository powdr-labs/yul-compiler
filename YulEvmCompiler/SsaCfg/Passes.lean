import YulEvmCompiler.SsaCfg.Ir
import Std.Data.HashMap
import Std.Data.HashSet
set_option warningAsError true
/-!
# YulEvmCompiler.SsaCfg.Passes

**Optimization passes** over the `yul-ssa-cfg` dialect, run between the
construction (`SsaCfg/OfYul.lean`) and the code generator
(`SsaCfg/ToAsm.lean`). Pure code transforms — the soundness proofs come
later, following the repo's checked-not-proved bring-up discipline: the
pipeline re-runs `Prog.wfCheck` on its output and falls back to the
*unoptimized* program when the check fails, so a pass bug degrades to a
missed optimization, never a miscompilation.

Four per-function passes, iterated as a pipeline (`pipelineRounds` rounds —
one pass's cleanup exposes the next's opportunities):

1. **Trivial block-parameter elimination** — the block-argument form of
   Braun et al.'s trivial-φ rule. A parameter `p` whose in-edges all pass
   the same value `v` (ignoring self-references `p`) is trivial: every use
   of `p` is replaced by `v`, the parameter is dropped, and the matching
   argument position is dropped from every in-edge. The construction's
   conservative modified-variable analysis makes these common (a join
   parameter both of whose edges pass the same value). Iterated to a fixed
   point — removing one parameter can make another trivial.

2. **Constant folding** — a forward walk with a `ValId → U256` map fed by
   `const` definitions. A *pure* built-in (dialect `effects` table:
   deterministic, no reads, no writes, no halts) applied to known constants
   is evaluated with the dialect's own executable step function (`stepOp`;
   pure ops ignore the state, so `EvmState.init` serves) and replaced by a
   `const`. A `branch` on a known constant becomes a `jump` along the taken
   edge.

3. **Local CSE** — a forward walk with a `(op, args) → dst` table for pure
   ops (and a `value → dst` table for `const`s). A repeated computation is
   dropped and its `dst` mapped to the earlier one. A block inherits the
   end-of-block table of its **unique, already-processed** predecessor —
   the sole in-edge source dominates the block, so every table entry's
   definition dominates every rewritten use; joins and loop headers start
   empty. The substitution accumulates globally (SSA ids are unique
   function-wide) and is applied to the whole function at the end, so uses
   in any block see it.

4. **Dead value elimination** — a liveness fixed point seeded by the
   arguments of effectful instructions (non-pure ops, all `call`s — callee
   effects are unknown) and terminator uses, where an edge argument counts
   as a use *only when the target parameter is live*; the arguments of a
   live pure op/`const` become live transitively. Dead `const`s and dead
   pure ops are deleted; dead block parameters are dropped together with
   the matching argument position of every in-edge. Effectful instructions
   always stay, in order, dead destinations and all.

Invariants preserved by every pass: edge arguments stay aligned with the
target's parameters; non-pure ops and `call`s are never removed or
reordered; the entry block's parameters and the function's
`params`/`nrets` are untouched; substitutions only *remove* definitions,
never duplicate them.
-/

namespace YulEvmCompiler.SsaCfg

open YulSemantics.EVM (U256 Op)

namespace Passes

/-- Purity per the dialect's own effect table — never a hand-rolled list. -/
def pureOp (yop : Op) : Bool :=
  (YulSemantics.EVM.evm.effects yop).pure

/-! ## Use substitution

A substitution maps *removed* definitions to their replacements. It is
applied to uses only — definitions are never renamed, so single assignment
is preserved (the domain's definitions are gone by the time it is applied).
-/

/-- A use substitution. -/
abbrev Subst := Std.HashMap ValId ValId

def substV (σ : Subst) (v : ValId) : ValId := σ.getD v v

def substVs (σ : Subst) (vs : List ValId) : List ValId := vs.map (substV σ)

def substInstr (σ : Subst) : Instr → Instr
  | .const d v => .const d v
  | .op ds yop args => .op ds yop (substVs σ args)
  | .call ds f args => .call ds f (substVs σ args)

def substEdge (σ : Subst) (e : Edge) : Edge :=
  { e with args := substVs σ e.args }

def substTerm (σ : Subst) : Term → Term
  | .jump e => .jump (substEdge σ e)
  | .branch c t f => .branch (substV σ c) (substEdge σ t) (substEdge σ f)
  | .ret vs => .ret (substVs σ vs)
  | .halt yop as => .halt yop (substVs σ as)

def substBlock (σ : Subst) (b : Block) : Block :=
  { b with instrs := b.instrs.map (substInstr σ), term := substTerm σ b.term }

def substFunc (σ : Subst) (f : Func) : Func :=
  { f with blocks := f.blocks.map (substBlock σ) }

/-- Map a function over a terminator's outgoing edges. -/
def mapEdges (g : Edge → Edge) : Term → Term
  | .jump e => .jump (g e)
  | .branch c t f => .branch c (g t) (g f)
  | t => t

/-- The in-edge argument lists per target block (one entry per edge — a
`branch` contributes two edges, both counted even when they coincide). -/
def inEdgeArgs (f : Func) : Array (List (List ValId)) := Id.run do
  let mut acc : Array (List (List ValId)) := Array.replicate f.blocks.size []
  for b in f.blocks do
    for e in b.term.edges do
      acc := acc.setIfInBounds e.target (e.args :: acc[e.target]!)
  return acc

/-- The in-edge source blocks per target block (one entry per edge). -/
def inEdgeSources (f : Func) : Array (List BlockId) := Id.run do
  let mut acc : Array (List BlockId) := Array.replicate f.blocks.size []
  for bi in [0:f.blocks.size] do
    for e in f.blocks[bi]!.term.edges do
      acc := acc.setIfInBounds e.target (bi :: acc[e.target]!)
  return acc

/-! ## Pass 1: trivial block-parameter elimination -/

/-- Find one trivial block parameter: `(block, position, param,
replacement)`. A parameter is trivial when the multiset of matching in-edge
arguments, minus self-references, is a single value. The entry block and
blocks with no in-edges are left alone. -/
def findTrivialParam (f : Func) : Option (BlockId × Nat × ValId × ValId) := Id.run do
  let ins := inEdgeArgs f
  for bi in [0:f.blocks.size] do
    if bi != f.entry then
      let b := f.blocks[bi]!
      let argLists := ins[bi]!
      if !argLists.isEmpty then
        for i in [0:b.params.length] do
          let p := b.params[i]!
          let ith := argLists.filterMap (·[i]?)
          -- every in-edge must actually carry position `i` (wf guarantees)
          if ith.length == argLists.length then
            let others := (ith.filter (· != p)).eraseDups
            if let [v] := others then
              return some (bi, i, p, v)
  return none

/-- Drop parameter position `i` of block `bi`, and position `i` of every
in-edge's arguments into `bi`. -/
def removeParam (f : Func) (bi : BlockId) (i : Nat) : Func :=
  let dropArg := fun (e : Edge) =>
    if e.target == bi then { e with args := e.args.eraseIdx i } else e
  { f with
    blocks := f.blocks.mapIdx fun j b =>
      let b := if j == bi then { b with params := b.params.eraseIdx i } else b
      { b with term := mapEdges dropArg b.term } }

/-- Eliminate trivial block parameters to a fixed point. Each removal can
expose another, so the loop is bounded by the total parameter count. -/
def elimTrivialParams (f0 : Func) : Func := Id.run do
  let total := f0.blocks.foldl (fun n b => n + b.params.length) 0
  let mut f := f0
  for _ in [0:total + 1] do
    match findTrivialParam f with
    | none => return f
    | some (bi, i, p, v) =>
      f := substFunc ((∅ : Subst).insert p v) (removeParam f bi i)
  return f

/-! ## Pass 2: constant folding -/

/-- Evaluate a pure built-in on constant arguments with the dialect's
executable step function. Pure ops ignore the state, so the initial state
serves; anything but a clean single-value return declines. -/
def evalPure (yop : Op) (args : List U256) : Option U256 :=
  match YulSemantics.EVM.stepOp yop args YulSemantics.EVM.EvmState.init with
  | some (.ok [v] _) => some v
  | _ => none

/-- Constant folding: forward walk feeding a `ValId → U256` map (sound
function-wide — SSA ids are defined once), rewriting pure ops on known
constants into `const`s and constant `branch`es into `jump`s. -/
def constFold (f : Func) : Func := Id.run do
  let mut consts : Std.HashMap ValId U256 := ∅
  let mut blocks : Array Block := #[]
  for b in f.blocks do
    let mut instrs : List Instr := []
    for ins in b.instrs do
      match ins with
      | .const d v =>
        consts := consts.insert d v
        instrs := ins :: instrs
      | .op [d] yop args =>
        let folded :=
          if pureOp yop then
            match args.mapM (consts[·]?) with
            | some vs => evalPure yop vs
            | none => none
          else none
        match folded with
        | some v =>
          consts := consts.insert d v
          instrs := .const d v :: instrs
        | none =>
          instrs := ins :: instrs
      | _ =>
        instrs := ins :: instrs
    let term := match b.term with
      | .branch c t e =>
        match consts[c]? with
        | some v => .jump (if v == 0 then e else t)
        | none => b.term
      | t => t
    blocks := blocks.push { b with instrs := instrs.reverse, term := term }
  return { f with blocks := blocks }

/-! ## Pass 3: local CSE -/

/-- The CSE table: available pure computations and constants, each mapping
to the `ValId` that already holds the result. -/
structure CseTab where
  ops : List ((Op × List ValId) × ValId) := []
  consts : List (U256 × ValId) := []
  deriving Inhabited

/-- Local common-subexpression elimination. Blocks are processed in index
order; a block whose *sole* in-edge comes from an already-processed
predecessor inherits that predecessor's end-of-block table (the unique
predecessor dominates the block, so every entry's definition dominates
every use the rewrite creates); joins, loop headers, and the entry start
empty. The dropped-def substitution is global and applied at the end. -/
def cse (f : Func) : Func := Id.run do
  let ins := inEdgeSources f
  let mut tables : Array CseTab := Array.replicate f.blocks.size {}
  let mut σ : Subst := ∅
  let mut blocks : Array Block := #[]
  for bi in [0:f.blocks.size] do
    let b := f.blocks[bi]!
    let mut tab : CseTab :=
      if bi == f.entry then {}
      else match ins[bi]! with
        | [p] => if p < bi then tables[p]! else {}
        | _ => {}
    let mut instrs : List Instr := []
    for ins0 in b.instrs do
      match substInstr σ ins0 with
      | .const d v =>
        match tab.consts.find? (·.1 == v) with
        | some (_, d0) => σ := σ.insert d d0
        | none =>
          tab := { tab with consts := (v, d) :: tab.consts }
          instrs := .const d v :: instrs
      | .op [d] yop args =>
        if pureOp yop then
          match tab.ops.find? (·.1 == (yop, args)) with
          | some (_, d0) => σ := σ.insert d d0
          | none =>
            tab := { tab with ops := ((yop, args), d) :: tab.ops }
            instrs := .op [d] yop args :: instrs
        else
          instrs := .op [d] yop args :: instrs
      | ins => instrs := ins :: instrs
    tables := tables.setIfInBounds bi tab
    blocks := blocks.push { b with instrs := instrs.reverse }
  -- apply the accumulated substitution everywhere (idempotent: its range —
  -- kept defs — is disjoint from its domain — dropped defs)
  return substFunc σ { f with blocks := blocks }

/-! ## Pass 4: dead value elimination -/

/-- One liveness round. Seeds: arguments of non-pure ops and of every
`call`, `branch` conditions, `ret`/`halt` operands. Edge arguments count
only toward live target parameters; a live pure op's arguments become live
transitively. Monotone in `live`. -/
def liveStep (f : Func) (live0 : Std.HashSet ValId) : Std.HashSet ValId := Id.run do
  let mut live := live0
  for b in f.blocks do
    for ins in b.instrs do
      match ins with
      | .const _ _ => pure ()
      | .op ds yop args =>
        if !pureOp yop || ds.any live.contains then
          live := args.foldl (fun s a => s.insert a) live
      | .call _ _ args =>
        live := args.foldl (fun s a => s.insert a) live
    match b.term with
    | .jump _ => pure ()
    | .branch c _ _ => live := live.insert c
    | .ret vs => live := vs.foldl (fun s a => s.insert a) live
    | .halt _ as => live := as.foldl (fun s a => s.insert a) live
    for e in b.term.edges do
      if let some tb := f.blocks[e.target]? then
        for pa in tb.params.zip e.args do
          if live.contains pa.1 then
            live := live.insert pa.2
  return live

/-- Live values of a function, by fixed point. The set only ever grows and
lives inside the finite universe of mentioned ids, so the fuel — one round
per possible insertion, plus slack — always reaches the fixed point. -/
def liveSet (f : Func) : Std.HashSet ValId := Id.run do
  let fuel := f.blocks.foldl (init := f.allDefs.length + 2) fun n b =>
    n + b.instrs.foldl (fun m i => m + i.uses.length) b.term.uses.length
  let mut live : Std.HashSet ValId := ∅
  for _ in [0:fuel] do
    let next := liveStep f live
    if next.size == live.size then
      return live
    live := next
  return live

/-- Dead value elimination: drop dead `const`s and dead pure ops (all
destinations dead — vacuously for destination-less pure ops), keep every
effectful instruction in order, and drop dead block parameters together
with the matching in-edge argument positions (parameter masks come from
the pre-pass blocks, so edges stay aligned). The entry block's parameters
are never touched. -/
def dve (f : Func) : Func :=
  let live := liveSet f
  let keepParam : BlockId → Nat → Bool := fun bi i =>
    match f.blocks[bi]? with
    | some b =>
      match b.params[i]? with
      | some p => live.contains p
      | none => true
    | none => true
  let filterEdge := fun (e : Edge) =>
    { e with
      args := (e.args.zipIdx.filter fun ai => keepParam e.target ai.2).map (·.1) }
  { f with
    blocks := f.blocks.mapIdx fun bi b =>
      { params := if bi == f.entry then b.params else b.params.filter live.contains
        instrs := b.instrs.filter fun i =>
          match i with
          | .const d _ => live.contains d
          | .op ds yop _ => !pureOp yop || ds.any live.contains
          | .call .. => true
        term := mapEdges filterEdge b.term } }

/-! ## The pipeline -/

/-- One full pipeline round over a function. -/
def runOnce (f : Func) : Func :=
  dve (cse (constFold (elimTrivialParams f)))

/-- Pipeline rounds: constant-folding a branch exposes trivial parameters,
parameter elimination exposes CSE, and so on — three rounds settle every
program seen so far. -/
def pipelineRounds : Nat := 3

end Passes

/-- Optimize one SSA function: the four-pass pipeline, iterated. -/
def optimizeFunc (f : Func) : Func := Id.run do
  let mut f := f
  for _ in [0:Passes.pipelineRounds] do
    f := Passes.runOnce f
  return f

/-- Optimize a whole program, defensively: if the optimized program fails
`Prog.wfCheck`, return the original — a pass bug is a missed optimization,
never a miscompilation. -/
def optimizeProg (P : Prog) : Prog :=
  let P' : Prog := { main := optimizeFunc P.main, funcs := P.funcs.map optimizeFunc }
  if P'.wfCheck then P' else P

end YulEvmCompiler.SsaCfg
