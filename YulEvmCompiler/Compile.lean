import YulEvmCompiler.Instr
import YulEvmCompiler.Value

/-!
# YulEvmCompiler.Compile

The milestone-1 compiler: straight-line Yul (no variables, no user-defined
functions, no control flow) to EVM bytecode.

Everything is `Option`-valued: `none` means "outside the (currently) supported
fragment". The supported built-in set is the domain of `opTable`, which is the
single source of truth — an op is added there exactly when its correctness
lemma lands in `YulEvmCompiler.Value` / `Correctness`.

Compilation scheme:

* `lit l` ⇒ `PUSH32 (litValue l)` — the *interpreted* literal is pushed, so all
  literal forms are supported with no well-formedness side condition.
* `builtin op [a₁, …, aₙ]` ⇒ `code(aₙ) … code(a₁) ; OP` — Yul evaluates
  argument lists right-to-left, so emitting the last argument first matches
  the evaluation order *and* leaves `a₁` on top of the stack, which is the
  EVM operand order.
* `exprStmt e` ⇒ `code(e)` (the big-step semantics guarantees `e` produces no
  values in statement position).
* A program is the concatenation of its statements; falling off the end of the
  bytecode is the EVM's implicit `STOP`, which matches the Yul `.normal`
  outcome.
-/

namespace YulEvmCompiler

open YulSemantics (Expr Stmt Block)
open YulSemantics.EVM (Op litValue)
open EvmSemantics (Operation)

/-- The single-opcode translation of each supported Yul built-in. `none` means
the built-in is not (yet) in the verified fragment; see the module docstring.

Deliberately *not* covered in milestone 1:
* memory/state writers that go through evm-semantics' `partial def writeBytes`
  (`mstore`, `mstore8`, `mcopy`, the copy family) — nothing about them is
  provable until `writeBytes` is totalized upstream;
* `keccak256` — the two repos each declare their own unrelated `opaque` hash;
* `log0`–`log4` — need a log-series correspondence (mechanical, later);
* `msize`, `gas`, calls/creates, `selfdestruct` — unmodeled in yul-semantics
  (`stepOp` returns `none`), so no source derivation exists to preserve. -/
def opTable : Op → Option Operation
  -- arithmetic. NOTE: `sdiv`/`smod`/`signextend` (and `sar` below) are not
  -- yet in the verified set — their BitVec-vs-UInt256 agreement lemmas are
  -- the remaining proof debt (see PLAN.md); each is enabled by adding its
  -- `conv_*` lemma to `Value.lean` and its entry here.
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

/-- Compile an expression. The value it produces (if any) ends up on top of
the EVM stack. -/
def compileExpr : Expr Op → Option (List Instr)
  | .lit l => some [.push (conv (litValue l))]
  | .var _ => none                    -- milestone 2 (needs DUPN)
  | .builtin op args => do
      let argCode ← compileArgs args
      let o ← opTable op
      return argCode ++ [.op o]
  | .call _ _ => none                 -- milestone 4

/-- Compile an argument list, **last argument first** (Yul's right-to-left
evaluation order); the first argument's value ends on top of the stack. -/
def compileArgs : List (Expr Op) → Option (List Instr)
  | [] => some []
  | e :: rest => do
      let restCode ← compileArgs rest
      let eCode ← compileExpr e
      return restCode ++ eCode

end

/-- Compile a statement. Milestone 1 supports only built-in expression
statements. -/
def compileStmt : Stmt Op → Option (List Instr)
  | .exprStmt e => compileExpr e
  | _ => none

/-- Compile a statement sequence (concatenation). -/
def compileStmts : List (Stmt Op) → Option (List Instr)
  | [] => some []
  | s :: rest => do
      let sCode ← compileStmt s
      let restCode ← compileStmts rest
      return sCode ++ restCode

/-- Compile a whole straight-line program (a top-level block). -/
def compileProgram (prog : Block Op) : Option (List Instr) :=
  compileStmts prog

end YulEvmCompiler
