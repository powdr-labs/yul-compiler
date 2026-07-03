import YulEvmCompiler.Instr
import YulEvmCompiler.Value

/-!
# YulEvmCompiler.Compile

The compiler: straight-line Yul with **variables and nested blocks** (no
user-defined functions, no control flow) to EVM bytecode.

Everything is `Option`-valued: `none` means "outside the (currently) supported
fragment". The supported built-in set is the domain of `opTable`, which is the
single source of truth — an op is added there exactly when its correctness
lemma lands in `YulEvmCompiler.Value` / `OpStep`.

## Variables: classic DUP/SWAP stack scheduling

The compiler threads a compile-time stack layout `Γ : List Ident`, the mirror
image of the runtime variable region of the operand stack (innermost — most
recently declared — variable on top, exactly the shape of the semantics'
`VEnv`). `off` counts the expression temporaries currently sitting above that
region:

* `var x` ⇒ `DUP(off + idx + 1)` where `idx` is `x`'s position in `Γ`;
  **rejected** (`none`) when `off + idx ≥ 16` — `DUP16` is the deepest
  reach without EIP-8024's `DUPN`, which evm-semantics does not activate on
  any fork yet.
* `x := e` ⇒ `code(e); SWAP(idx+1); POP` — swap the new value into `x`'s
  slot, pop the old one; rejected when `idx ≥ 16`.
* `let x := e` ⇒ `code(e)` — the value stays put, the layout grows. Free.
* `let x, y, …` (no initializer) ⇒ one `PUSH32 0` per name.
* `{ … }` ⇒ the compiled body followed by one `POP` per variable the block
  declared (mirroring the semantics' `restore`).

Compilation of calls is unchanged: `builtin op [a₁, …, aₙ]` compiles the
arguments right-to-left (Yul's evaluation order, which puts `a₁` on top —
the EVM operand order) followed by the opcode; each already-evaluated
argument deepens `off` by one for the arguments still to come. A program is
the concatenation of its statements; falling off the end of the bytecode is
the EVM's implicit `STOP`, which matches the Yul `.normal` outcome.
-/

namespace YulEvmCompiler

open YulSemantics (Expr Stmt Block Ident)
open YulSemantics.EVM (Op litValue)
open EvmSemantics (Operation)

/-- The single-opcode translation of each supported Yul built-in. `none` means
the built-in is not (yet) in the verified fragment; see the module docstring.

Deliberately *not* covered so far:
* `sdiv`/`smod`/`signextend`/`sar` — plain proof debt: their two's-complement
  `BitVec` ↔ `UInt256` agreement lemmas (`conv_*` in `Value.lean`) are still
  open; each is enabled by adding its lemma, its row here, and its `opStep`
  case;
* memory/state writers that go through evm-semantics' `partial def writeBytes`
  (`mstore`, `mstore8`, `mcopy`, the copy family) — nothing about them is
  provable until `writeBytes` is totalized upstream;
* `keccak256` — the two repos each declare their own unrelated `opaque` hash;
* `log0`–`log4` — need a log-series correspondence (mechanical, later);
* `msize`, `gas`, calls/creates, `selfdestruct` — unmodeled in yul-semantics
  (`stepOp` returns `none`), so no source derivation exists to preserve. -/
def opTable : Op → Option Operation
  -- arithmetic
  | .add => some .ADD | .sub => some .SUB | .mul => some .MUL | .div => some .DIV
  | .mod => some .MOD
  | .addmod => some .ADDMOD | .mulmod => some .MULMOD | .exp => some .EXP
  | .clz => some .CLZ
  -- comparison
  | .lt => some .LT | .gt => some .GT | .slt => some .SLT | .sgt => some .SGT
  | .eq => some .EQ | .iszero => some .ISZERO
  -- bitwise / shifts
  | .and => some .AND | .or => some .OR | .xor => some .XOR | .not => some .NOT
  | .byte => some .BYTE | .shl => some .SHL | .shr => some .SHR
  -- value discard
  | .pop => some .POP
  -- memory read
  | .mload => some .MLOAD
  -- storage / transient storage
  | .sload => some .SLOAD | .sstore => some .SSTORE
  | .tload => some .TLOAD | .tstore => some .TSTORE
  -- halting
  | .stop => some .STOP | .ret => some .RETURN | .revert => some .REVERT
  | .invalid => some .INVALID
  -- everything else: not yet in the verified fragment
  | _ => none

mutual

/-- Compile an expression against layout `Γ` with `off` temporaries currently
above the variable region. The produced value (if any) ends up on top of the
stack. -/
def compileExpr (Γ : List Ident) (off : Nat) : Expr Op → Option (List Instr)
  | .lit l => some [.push (conv (litValue l))]
  | .var x => do
      let idx ← Γ.findIdx? (fun y => y = x)
      if h : off + idx < 16 then
        return [.op (.Dup ⟨off + idx, h⟩)]
      else
        none                        -- too deep for DUP16 (needs EIP-8024)
  | .builtin op args => do
      let argCode ← compileArgs Γ off args
      let o ← opTable op
      return argCode ++ [.op o]
  | .call _ _ => none               -- milestone 4

/-- Compile an argument list, **last argument first** (Yul's right-to-left
evaluation order); the first argument's value ends on top of the stack. Each
argument still to be compiled sees the values of the later arguments as
additional temporaries. -/
def compileArgs (Γ : List Ident) (off : Nat) : List (Expr Op) → Option (List Instr)
  | [] => some []
  | e :: rest => do
      let restCode ← compileArgs Γ off rest
      let eCode ← compileExpr Γ (off + rest.length) e
      return restCode ++ eCode

end

mutual

/-- Compile a statement against layout `Γ`; returns the code and the layout
after the statement. -/
def compileStmt (Γ : List Ident) : Stmt Op → Option (List Instr × List Ident)
  | .exprStmt e => do
      let is ← compileExpr Γ 0 e
      return (is, Γ)
  | .letDecl xs none =>
      return (List.replicate xs.length (.push (conv 0)), xs ++ Γ)
  | .letDecl xs (some e) =>
      match xs with
      | [x] => do
          let is ← compileExpr Γ 0 e
          return (is, x :: Γ)
      | _ => none                   -- multi-value `let` needs user calls
  | .assign xs e =>
      match xs with
      | [x] => do
          let is ← compileExpr Γ 0 e
          let idx ← Γ.findIdx? (fun y => y = x)
          if h : idx < 16 then
            return (is ++ [.op (.Swap ⟨idx, h⟩), .op .POP], Γ)
          else
            none                    -- too deep for SWAP16 (needs EIP-8024)
      | _ => none
  | .block body => do
      let (isb, Γ') ← compileStmts Γ body
      return (isb ++ List.replicate (Γ'.length - Γ.length) (.op .POP), Γ)
  | _ => none

/-- Compile a statement sequence, threading the layout. -/
def compileStmts (Γ : List Ident) : List (Stmt Op) → Option (List Instr × List Ident)
  | [] => some ([], Γ)
  | s :: rest => do
      let (is1, Γ1) ← compileStmt Γ s
      let (is2, Γ2) ← compileStmts Γ1 rest
      return (is1 ++ is2, Γ2)

end

/-- Compile a whole straight-line program (a top-level block, starting from
the empty layout). -/
def compileProgram (prog : Block Op) : Option (List Instr) :=
  (compileStmts [] prog).map (·.1)

end YulEvmCompiler
