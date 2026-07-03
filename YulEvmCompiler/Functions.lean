import YulEvmCompiler.Compile

/-!
# YulEvmCompiler.Functions

**Executable codegen for user-defined Yul functions** (the calling convention
discussed in the design notes), with the *caller-side return-slot zeroing*
variant. This module is the concrete, `#eval`-tested compiler; the correctness
proof against `YulSemantics`/`EvmSemantics` is layered on separately, in
verified stages, and does **not** yet cover this module — so `compileProgF`
here is not (yet) backed by a theorem the way `compileProgram` is.

## Calling convention (caller-side zeroing)

For a call `x₁,…,xₘ := f(a₁,…,aₙ)` the caller emits
```
PUSH32 retaddr          -- the JUMPDEST right after the call
PUSH32 0  (×m)          -- zero-init the m return slots
<a₁ … aₙ, right-to-left> -- Yul arg order; leaves a₁ on top
PUSH32 entry_f
JUMP
JUMPDEST                -- retaddr; stack is now [results] ++ σ
```
so the entry stack is exactly `[a₁..aₙ, 0..0, retaddr] ++ σ`, matching the
reference semantics' initial `VEnv = params.zip argvals ++ bindZeros rets`
(params on top, then the zeroed rets). The callee is therefore just
```
JUMPDEST                -- entry_f
<body compiled as a block, layout params ++ rets>
POP (×n)                -- drop the n params (on top after the body)
SWAP1; SWAP2; …; SWAPm  -- rotate retaddr to the top, preserving ret order
JUMP                    -- return
```
Every instruction is fixed width (`PUSH32` = 33 bytes, others 1), so function
entry positions are found by a two-pass layout: compile once with placeholder
entries to measure lengths, assign positions, compile again. The whole program
is laid out as `main ; STOP ; f₁ ; f₂ ; …` — `main` falls through to the
explicit `STOP`, and the function bodies are reached only by `JUMP`.

Constraints (rejected with `none` otherwise): top-level functions only,
≤ 16 return values (for `SWAPm`), and the usual ≤ 16 DUP/SWAP depth.
-/

namespace YulEvmCompiler

open YulSemantics (Expr Stmt Block Ident)
open YulSemantics.EVM (Op litValue)
open EvmSemantics (Operation)

/-- Static info for a top-level function: signature, body, and (once laid out)
its entry byte-position. -/
structure FnInfo where
  params : List Ident
  rets   : List Ident
  body   : Block Op
  entry  : Nat
  deriving Repr, Inhabited

/-- The compile-time function table: name ↦ info. -/
abbrev FnTable := List (Ident × FnInfo)

/-- Resolve a function name. -/
def FnTable.get? (ft : FnTable) (n : Ident) : Option FnInfo :=
  (ft.find? (fun p => p.1 = n)).map (·.2)

/-- Collect the top-level function definitions of a block (in order). -/
def collectFns : Block Op → List (Ident × List Ident × List Ident × Block Op)
  | [] => []
  | .funDef n ps rs b :: rest => (n, ps, rs, b) :: collectFns rest
  | _ :: rest => collectFns rest

/-- `retSwaps m = SWAP1; SWAP2; …; SWAPm`, the order-preserving rotation that
turns `[r₁,…,rₘ, retaddr]` into `[retaddr, r₁,…,rₘ]`. Indices are taken mod 16;
callers guarantee `m ≤ 16` so no wraparound occurs. -/
def retSwaps : Nat → List Instr
  | 0 => []
  | k + 1 => retSwaps k ++ [.op (.Swap ⟨k % 16, Nat.mod_lt _ (by decide)⟩)]

/-- The fixed scaffold around a call's argument code: return-address push, `m`
zero return slots, the args, the entry-point push, `JUMP`, and the landing
`JUMPDEST`. -/
def callScaffold (retaddr entry m : Nat) (argCode : List Instr) : List Instr :=
  (.push (EvmSemantics.UInt256.ofNat retaddr)) :: List.replicate m (.push (conv 0))
    ++ argCode ++ [.push (EvmSemantics.UInt256.ofNat entry), .op .JUMP, .op .JUMPDEST]

/-- Byte length of a call's scaffold (independent of the pushed values). -/
def scaffoldLen (m argLen : Nat) : Nat := 33 + 33 * m + argLen + 33 + 1 + 1

mutual

/-- Compile an expression at byte position `pc`, layout `Γ`, with `off`
temporaries above the variable region. A call used as a sub-expression must
return exactly one value. -/
def compileExprF (ft : FnTable) (pc : Nat) (Γ : List Ident) (off : Nat) :
    Expr Op → Option (List Instr)
  | .lit l => some [.push (conv (litValue l))]
  | .var x => do
      let idx ← Γ.findIdx? (fun y => y = x)
      if h : off + idx < 16 then return [.op (.Dup ⟨off + idx, h⟩)] else none
  | .builtin op args => do
      let argCode ← compileArgsF ft pc Γ off args
      let o ← opTable op
      return argCode ++ [.op o]
  | .call f args => do
      let info ← ft.get? f
      if info.rets.length = 1 ∧ info.params.length = args.length then
        let argsPc := pc + 33 + 33 * 1
        let argCode ← compileArgsF ft argsPc Γ (off + 1 + 1) args
        let retaddr := argsPc + (assembleBytes argCode).length + 33 + 1
        return callScaffold retaddr info.entry 1 argCode
      else none

/-- Compile an argument list right-to-left; `aₙ` is emitted first (evaluated
first), `a₁` ends up on top. Each earlier argument sees the later ones as
extra temporaries. -/
def compileArgsF (ft : FnTable) (pc : Nat) (Γ : List Ident) (off : Nat) :
    List (Expr Op) → Option (List Instr)
  | [] => some []
  | e :: rest => do
      let restCode ← compileArgsF ft pc Γ off rest
      let eCode ← compileExprF ft (pc + (assembleBytes restCode).length) Γ
        (off + rest.length) e
      return restCode ++ eCode

end

/-- Compile a call in statement position (`m` results left on the stack),
shared by expression statements (`m = 0`), multi-`let`, and multi-assign. -/
def compileCallStmt (ft : FnTable) (pc : Nat) (Γ : List Ident) (off : Nat)
    (f : Ident) (args : List (Expr Op)) : Option (List Instr × Nat) := do
  let info ← ft.get? f
  let m := info.rets.length
  if info.params.length = args.length ∧ m ≤ 16 then
    let argsPc := pc + 33 + 33 * m
    let argCode ← compileArgsF ft argsPc Γ (off + 1 + m) args
    let retaddr := argsPc + (assembleBytes argCode).length + 33 + 1
    return (callScaffold retaddr info.entry m argCode, m)
  else none

mutual

/-- Compile a statement at position `pc` and layout `Γ`, returning the code and
the layout after it. -/
def compileStmtF (ft : FnTable) (pc : Nat) (Γ : List Ident) :
    Stmt Op → Option (List Instr × List Ident)
  | .funDef _ _ _ _ => some ([], Γ)          -- hoisted; a no-op in the main flow
  | .exprStmt (.call f args) => do
      let (code, m) ← compileCallStmt ft pc Γ 0 f args
      if m = 0 then return (code, Γ) else none
  | .exprStmt e => do
      let is ← compileExprF ft pc Γ 0 e
      return (is, Γ)
  | .letDecl xs none =>
      return (List.replicate xs.length (.push (conv 0)), xs ++ Γ)
  | .letDecl xs (some (.call f args)) => do
      let (code, m) ← compileCallStmt ft pc Γ 0 f args
      if m = xs.length then return (code, xs ++ Γ) else none
  | .letDecl [x] (some e) => do
      let is ← compileExprF ft pc Γ 0 e
      return (is, x :: Γ)
  | .letDecl _ (some _) => none
  | .assign [x] e => do
      let is ← compileExprF ft pc Γ 0 e
      let idx ← Γ.findIdx? (fun y => y = x)
      if h : idx < 16 then
        return (is ++ [.op (.Swap ⟨idx, h⟩), .op .POP], Γ)
      else none
  | .assign _ _ => none
  | .block body => do
      let (isb, Γ') ← compileStmtsF ft (pc + 0) Γ body
      return (isb ++ List.replicate (Γ'.length - Γ.length) (.op .POP), Γ)
  | .cond c body => do
      let cCode ← compileExprF ft pc Γ 0 c
      let pcBody := pc + (assembleBytes cCode).length + 35
      let (bodyCode, Γb) ← compileStmtsF ft pcBody Γ body
      let pops := Γb.length - Γ.length
      let dest := pcBody + (assembleBytes bodyCode).length + pops
      return (cCode ++ [.op .ISZERO, .push (EvmSemantics.UInt256.ofNat dest), .op .JUMPI]
        ++ bodyCode ++ List.replicate pops (.op .POP) ++ [.op .JUMPDEST], Γ)
  | _ => none

/-- Compile a statement sequence, threading position and layout. -/
def compileStmtsF (ft : FnTable) (pc : Nat) (Γ : List Ident) :
    List (Stmt Op) → Option (List Instr × List Ident)
  | [] => some ([], Γ)
  | s :: rest => do
      let (is1, Γ1) ← compileStmtF ft pc Γ s
      let (is2, Γ2) ← compileStmtsF ft (pc + (assembleBytes is1).length) Γ1 rest
      return (is1 ++ is2, Γ2)

end

/-- Compile one function: `JUMPDEST ; body (as a block, layout params++rets) ;
POP×n ; SWAP1..SWAPm ; JUMP`. -/
def compileFn (ft : FnTable) (entry : Nat) (ps rs : List Ident) (b : Block Op) :
    Option (List Instr) := do
  let (bodyCode, _) ← compileStmtF ft (entry + 1) (ps ++ rs) (.block b)
  if rs.length ≤ 16 then
    return [.op .JUMPDEST] ++ bodyCode ++ List.replicate ps.length (.op .POP)
      ++ retSwaps rs.length ++ [.op .JUMP]
  else none

/-- Running byte-position of each function entry, given `main`'s length and the
functions' code lengths: `entryᵢ = mainLen + 1 + Σⱼ<ᵢ lenⱼ` (the `+1` is the
`STOP` after `main`). -/
def entryPositions (mainLen : Nat) (lens : List Nat) : List Nat :=
  (lens.foldl (fun (acc : List Nat × Nat) len =>
      (acc.1 ++ [acc.2], acc.2 + len)) ([], mainLen + 1)).1

/-- Compile a whole program with top-level user-defined functions. Two passes:
measure code sizes with placeholder entry positions, assign real positions,
then recompile. -/
def compileProgF (prog : Block Op) : Option (List Instr) := do
  let fns := collectFns prog
  let dummyFt : FnTable := fns.map (fun p => (p.1, ⟨p.2.1, p.2.2.1, p.2.2.2, 0⟩))
  -- pass 1: lengths
  let (mainCode0, _) ← compileStmtsF dummyFt 0 [] prog
  let mainLen := (assembleBytes mainCode0).length
  let lens ← fns.mapM (fun p => do
    let code ← compileFn dummyFt 0 p.2.1 p.2.2.1 p.2.2.2
    return (assembleBytes code).length)
  let entries := entryPositions mainLen lens
  let realFt : FnTable :=
    (fns.zip entries).map (fun (p, e) => (p.1, ⟨p.2.1, p.2.2.1, p.2.2.2, e⟩))
  -- pass 2: real positions
  let (mainCode, _) ← compileStmtsF realFt 0 [] prog
  let fnCodes ← (fns.zip entries).mapM (fun (p, e) =>
    compileFn realFt e p.2.1 p.2.2.1 p.2.2.2)
  return mainCode ++ [.op .STOP] ++ fnCodes.flatten

end YulEvmCompiler
