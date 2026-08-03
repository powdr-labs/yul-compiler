import YulEvmCompiler.Asm
set_option warningAsError true
/-!
# YulEvmCompiler.CostModel

An **abstract cost model for a compiled code block**, defined on the labeled
assembly layer (`Asm`).  It has one job: when the compiler holds several
independently verified artifacts for the same code block, decide which to keep.
Nothing here is on the trust path — every candidate has already passed its own
backend's correctness theorem and its own overflow certificate — so a wrong
answer costs gas, never soundness.

## What it replaces, and why that mattered

The previous selectors (`SsaCfg.byteCodeCost`, `SsaCfg.instrCost`) weigh the
*assembled bytes* of a whole artifact.  That is a size measure, and it rejects
any optimization that trades size for speed.  `SsaCfg.Passes.rematConsts` is
exactly such an optimization — it spends a `push` to avoid keeping a constant
live — and under `byteCodeCost` the aave-v4 suite *lost* its entire 215,544-gas
win, because the bigger-but-faster artifact was discarded for the smaller one.

Three things about this model carry that result.

**It reads `Asm`, not bytecode.**  The first version of this file analysed
assembled bytes and recovered jumps by looking for `PUSH` immediates that land
on a `JUMPDEST`.  That does not work: measured on `PositionStatusMap`, it found
**19 edges in a 5,215-instruction program**.  Solidity code is full of small
literals that hit a `JUMPDEST` by accident, and an object blob's jump addresses
are section-relative and do not match blob offsets at all.  On `Asm`,
`jump`/`jumpi`/`pushLabel` name their `label` and `dynJump` is precisely the
dynamic edge, so the control-flow graph is exact and backend-neutral.

**It costs one code block.**  Both backends' block compilers have type
`Block → List Asm`, so the comparison happens where control flow is coherent —
and the choice becomes per code block, letting one object take the SSA backend
for its runtime and the classic one for its constructor.

**It charges opcodes, not bytes.**  A `push` is 3 and a `pop` is 2 and a
`jumpdest` is 1, per the Yellow Paper's fee schedule; a `jump` carries its
`PUSH{labelWidth}` as well.  State-touching operations are charged a flat
`W_verylow` rather than their real fee: two candidates compile the same source
and execute the same state operations, so their cost cancels — but only while
it is *small*.  Charging `sstore` even a compressed 200 drowned a difference of
a few `SWAP`s and picked an artifact 132,512 gas worse on
`loopInvariantCodeMotion/no_move_state.yul`.

## What is deliberately absent: execution frequency

There is no term for how often code runs.  That is a measured result, not an
oversight.  A frequency estimate was built four times — weighting emitted bytes
by an estimated block execution count (tried and reverted before this branch);
loop nesting from back-edge spans; the same with Cooper/Harvey/Kennedy
dominators, after the naive version marked 53% of an SSA artifact loop-resident
against 23% for the same program from the classic backend; and additive
call/branch propagation, which is the shape that should in principle correct
the bias against inlining — and *every* version made the suites worse:

| model | uniswap-v4 | aave-v4 |
|---|---:|---:|
| this file (tiers over live code) | **948,525** | **15,399,528** |
| + loop nesting, `8 ^ depth` | 964,615 | 17,699,784 |
| + loop nesting, `2 ^ depth` | 961,641 | 15,399,528 |
| + call/branch frequency | 966,549 | 16,733,564 |

Two artifacts from different backends differ in block structure, so the
estimator's systematic errors do not cancel, and a multiplier amplifies them
into the deciding term.  What does survive is the opcode schedule and *exact*
reachability — enough that unreachable code is free, so the SSA backend's dead
barriers and the classic backend's dead tails stop being charged for.
-/

namespace YulEvmCompiler.CostModel

open EvmSemantics
open YulSemantics.EVM (Op)

/-- Local default, so the array walkers below can use `[k]!`.  `Asm` has no
reason to carry an `Inhabited` instance for the compiler proper. -/
private instance : Inhabited Asm := ⟨Asm.pop⟩

/-! ## Opcode weights -/

/-- Per-execution weight of one EVM operation: the Yellow Paper's fee schedule,
with everything state-touching flattened to `W_verylow` (see the module
docstring for why the flattening is load-bearing). -/
def opTier : Operation → Nat
  | .STOP | .RETURN | .REVERT | .INVALID | .SELFDESTRUCT => 0
  -- W_verylow
  | .ADD | .SUB | .NOT | .LT | .GT | .SLT | .SGT | .EQ | .ISZERO
  | .AND | .OR | .XOR | .BYTE | .SHL | .SHR | .SAR | .CLZ
  | .CALLDATALOAD | .MLOAD | .MSTORE | .MSTORE8 => 3
  -- W_low
  | .MUL | .DIV | .SDIV | .MOD | .SMOD | .SIGNEXTEND | .SELFBALANCE => 5
  -- W_mid
  | .ADDMOD | .MULMOD | .JUMP => 8
  -- W_high
  | .JUMPI => 10
  | .EXP => 10
  | .JUMPDEST => 1
  | .POP => 2
  | .CALLDATACOPY | .CODECOPY | .RETURNDATACOPY | .MCOPY => 6
  -- state and external interaction: charged flat, they cancel between
  -- candidates and their real magnitude only amplifies noise
  | .KECCAK256 | .BLOCKHASH
  | .SLOAD | .TLOAD | .SSTORE | .TSTORE
  | .BALANCE | .EXTCODESIZE | .EXTCODECOPY | .EXTCODEHASH
  | .CALL | .CALLCODE | .DELEGATECALL | .STATICCALL
  | .CREATE | .CREATE2 | .Log _ => 3
  -- W_base: environment and context reads, and anything unlisted
  | _ => 2

/-- Per-execution weight of one `Asm` instruction.  Label pushes lower to
`PUSH{labelWidth}`, so `jump`/`jumpi` carry the push *and* the transfer. -/
def tier : Asm → Nat
  | .push _ => 3
  | .op yop => match opTable yop with
      | some o => opTier o
      | none => 3
  | .dup _ => 3
  | .swap _ => 3
  | .pop => 2
  | .label _ => 1
  | .jump _ => 3 + 8
  | .jumpi _ => 3 + 10
  | .pushLabel _ => 3
  | .dynJump => 8
  -- lowers to a single `PUSH32` of the patched value, whatever it is
  | .pushImmutable _ => 3

/-- Does this instruction end the frame? -/
def halts : Asm → Bool
  | .op yop => match opTable yop with
      | some .STOP | some .RETURN | some .REVERT | some .INVALID
      | some .SELFDESTRUCT => true
      | _ => false
  | _ => false

/-- Does this instruction end its basic block by transferring control away
unconditionally, so the next instruction is not a fallthrough successor? -/
def endsBlock : Asm → Bool
  | .jump _ => true
  | .dynJump => true
  | i => halts i

/-! ## Reachability

Blocks open at index 0, at every `label`, and after every unconditional
transfer.  Edges are read straight off the syntax: `jump l` and `jumpi l` go to
`l`; `pushLabel l` goes to `l`, because that is a call's *return address* and it
is what carries flow past a call whose return is a `dynJump` and therefore
invisible; and a block that does not end in an unconditional transfer falls
through to the next.  `dynJump` itself contributes no edge, and does not need
to: every address that can reach it was pushed by a `pushLabel` that already
did. -/

/-- The largest label mentioned, so the label table can be a flat array rather
than a hash map — this function runs once per candidate per code block per
planning round, so its own cost is not negligible. -/
def maxLabel (prog : Array Asm) : Nat := Id.run do
  let mut m := 0
  for k in [0:prog.size] do
    let l : Nat := match prog[k]! with
      | .label l => l
      | .jump l => l
      | .jumpi l => l
      | .pushLabel l => l
      | _ => 0
    if l > m then m := l
  return m

/-- The abstract cost of one compiled code block: the Yellow Paper tier sum over
its reachable instructions.

Written as one fused pass rather than a reachability array followed by a sum,
and with a flat label table and no adjacency structure — successors are found by
re-scanning a block's own instructions when the search pops it, which is `O(n)`
overall because each block is popped once. -/
def execCostAsmArray (prog : Array Asm) : Nat := Id.run do
  let n := prog.size
  if n == 0 then return 0
  -- label → the index of its definition (`n` = undefined)
  let mut labelIdx : Array Nat := Array.replicate (maxLabel prog + 1) n
  for k in [0:n] do
    if let .label l := prog[k]! then labelIdx := labelIdx.set! l k
  -- block partition: index 0, every `label`, and after every unconditional
  -- transfer.  `blockOf` maps an instruction to its block's start; `blockEnd`
  -- maps a block's start to one past its last instruction.
  let mut blockOf : Array Nat := Array.replicate n 0
  let mut blockEnd : Array Nat := Array.replicate n 0
  let mut cur := 0
  let mut opensNext := true
  for k in [0:n] do
    if opensNext || (prog[k]! matches Asm.label _) then cur := k
    blockOf := blockOf.set! k cur
    blockEnd := blockEnd.set! cur (k + 1)
    opensNext := endsBlock prog[k]!
  -- reachability: depth-first over blocks, rescanning each popped block for its
  -- successors.  `jump`/`jumpi`/`pushLabel` name their target; a block not
  -- ending in an unconditional transfer falls through to the next.
  let mut seen : Array Bool := Array.replicate n false
  let mut work : Array Nat := #[0]
  seen := seen.set! 0 true
  while work.size > 0 do
    let b := work[work.size - 1]!
    work := work.pop
    let last := blockEnd[b]!
    for k in [b:last] do
      let tgt : Nat := match prog[k]! with
        | .jump l => labelIdx.getD l n
        | .jumpi l => labelIdx.getD l n
        | .pushLabel l => labelIdx.getD l n
        | _ => n
      if tgt < n && !seen[tgt]! then
        seen := seen.set! tgt true
        work := work.push tgt
    if last < n && !endsBlock prog[last - 1]! && !seen[last]! then
      seen := seen.set! last true
      work := work.push last
  let mut acc := 0
  for k in [0:n] do
    if seen[blockOf[k]!]! then acc := acc + tier prog[k]!
  return acc

/-- `execCostAsmArray` on the list form the compiler passes around. -/
def execCostAsm (prog : List Asm) : Nat := execCostAsmArray prog.toArray

end YulEvmCompiler.CostModel
