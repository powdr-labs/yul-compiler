import YulEvmCompiler.Compile
import YulEvmCompiler.SsaCfg.OfYul
import YulEvmCompiler.SsaCfg.Passes
import YulEvmCompiler.SsaCfg.ToAsm
set_option warningAsError true
/-!
# YulEvmCompiler.SsaCfg.Compile

The **SSA backend entry point**: Yul → `yul-ssa-cfg` → labeled `Asm` → EVM
bytecode, through the exact same final gates as the classic `compile` — the
Asm peephole (`optimizeAsm`), the stack-overflow certificate (`stackOK2`),
and label resolution (`lowerProg`) — so everything below the `Asm` layer
(Phase B, the certificate checker, the assembler) is shared, code and proof.

`compileViaSsa` is `Option`-valued like everything else in this repository:
any unsupported shape (construction rejection, shuffler depth overflow,
liveness anomaly, failed well-formedness or overflow check) yields `none`,
and the caller falls back to the classic backend. Rejection is never
miscompilation.

The SSA optimization pipeline (`SsaCfg/Passes.lean`) runs between the
construction and the code generator. Occasionally a *better* SSA program
emits *longer* code — removing a block parameter can change a block's
entry stack layout so that an edge needs an extra shuffle and a fused
conditional jump becomes an inverted branch — so both the optimized and
the unoptimized programs are emitted and the shorter result wins (ties go
to the optimized one).
-/

namespace YulEvmCompiler.SsaCfg

open YulSemantics.EVM (Op)

/-- Emit one SSA program through the shared final gates: `ToAsm`, `Asm`
well-formedness, the peephole, the overflow certificate, label
resolution. -/
def finishProg (P : Prog) : Option (List YulEvmCompiler.Instr) := do
  let asm ← ToAsm.emitProg P
  if !wfCheck asm then none else
  let opt := optimizeAsm asm
  if stackOK2 opt then lowerProg opt else none

/-- Compile a top-level Yul block through the SSA-CFG dialect. -/
def compileViaSsa (prog : YulSemantics.Block Op) :
    Option (List YulEvmCompiler.Instr) := do
  let P ← ofBlock prog
  -- dominance gate: the SSA passes are sound only on programs whose uses
  -- are dominated by their definitions (see `ToAsm.Prog.domCheck`)
  if !(ToAsm.Prog.domCheck P) then none else
  match finishProg (optimizeProg P), finishProg P with
  | some a, some b => if a.length ≤ b.length then some a else some b
  | some a, none => some a
  | none, some b => some b
  | none, none => none

/-! ## Static cost — candidate selection

The SSA scheduler wins where dataflow freedom pays (call-heavy code,
switch dispatch, straight-line reuse) and still loses on long chains of
small branch joins, where its v1 canonical entry layouts churn the stack
(solc's forward layout inheritance is the known cure — a follow-up). Until
the scheduler matures, `compileSource` keeps **both** artifacts and picks by
a static gas proxy: a per-opcode weighted count in which the stack-traffic
opcodes (`DUP`/`SWAP`/`POP`/`PUSH`, jumps) carry their real costs and
everything else a uniform base — both candidates compile the same source,
so state-op costs cancel and the difference concentrates exactly in the
traffic the two layouts disagree on. -/

/-- Static cost of one EVM opcode byte (data bytes are skipped by the
walkers below). -/
def opcodeCost (b : UInt8) : Nat :=
  if b == 0x50 then 2            -- POP
  else if b == 0x56 then 8       -- JUMP
  else if b == 0x57 then 10      -- JUMPI
  else if b == 0x5b then 1       -- JUMPDEST
  else if b == 0x5f then 2       -- PUSH0
  else 3                         -- PUSH/DUP/SWAP/arithmetic base

/-- Whether an opcode byte always halts the frame (`STOP`/`RETURN`/`REVERT`/
`INVALID`/`SELFDESTRUCT`). Everything after one of these up to the next
`JUMPDEST` is unreachable — the SSA backend's dead barriers, the classic
backend's dead tails — and must not count toward the executed-code cost. -/
def haltingByte (b : UInt8) : Bool :=
  b == 0x00 || b == 0xf3 || b == 0xfd || b == 0xfe || b == 0xff

/-- Static cost of assembled bytecode: PUSH immediates skipped via the
`skip` counter, unreachable post-halt code skipped via the `dead` flag
(cleared at the next `JUMPDEST`). -/
def byteCodeCost (code : List UInt8) : Nat :=
  go code 0 false 0
where
  go : List UInt8 → Nat → Bool → Nat → Nat
    | [], _, _, acc => acc
    | b :: rest, skip, dead, acc =>
      if skip > 0 then go rest (skip - 1) dead acc
      else
        let n := b.toNat
        let isPush := 0x60 ≤ n && n ≤ 0x7f
        let skip' := if isPush then n - 0x5f else 0
        if dead then
          if b == 0x5b then go rest 0 false (acc + 1)
          else go rest skip' true acc
        else if haltingByte b then go rest 0 true (acc + opcodeCost b)
        else if isPush then go rest skip' false (acc + 3)
        else go rest 0 false (acc + opcodeCost b)

/-- Static cost of a lowered instruction stream (same dead-code skipping as
`byteCodeCost`). -/
def instrCost (is : List YulEvmCompiler.Instr) : Nat :=
  go is false 0
where
  haltingOp : EvmSemantics.Operation → Bool
    | .STOP | .RETURN | .REVERT | .INVALID | .SELFDESTRUCT => true
    | _ => false
  cost : YulEvmCompiler.Instr → Nat
    | .push _ _ => 3
    | .op o =>
      match o with
      | .POP => 2
      | .JUMP => 8
      | .JUMPI => 10
      | .JUMPDEST => 1
      | _ => 3
  go : List YulEvmCompiler.Instr → Bool → Nat → Nat
    | [], _, acc => acc
    | i :: rest, dead, acc =>
      if dead then
        match i with
        | .op .JUMPDEST => go rest false (acc + 1)
        | _ => go rest true acc
      else
        match i with
        | .op o => if haltingOp o then go rest true (acc + cost i)
                   else go rest false (acc + cost i)
        | _ => go rest false (acc + cost i)

end YulEvmCompiler.SsaCfg
