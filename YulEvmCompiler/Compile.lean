import YulEvmCompiler.Asm

/-!
# YulEvmCompiler.Compile

The compiler from Yul to the labeled assembly layer, now covering
**`for` loops (with `break`/`continue`) and user-defined functions (with
`leave`)** on top of the milestone-2 fragment.

## What is threaded through compilation

* the stack layout `Γ : List Ident` (mirror of the runtime variable
  region, innermost first) — exactly as in milestone 2;
* a **fresh-label counter** `n : Nat`. No freshness invariant is proved
  about it: the final program is *checked* for label well-formedness
  (`wfCheck`) and rejected on failure, so proofs read uniqueness off the
  successful check;
* a **function-info environment** `Φ : FMap`, a stack of scopes mirroring
  the semantics' `FunEnv` (each block hoists its `funDef`s into a fresh
  scope, so forward references and mutual recursion work);
* the enclosing **function context** `F` (`exit` label + frame depth) for
  `leave`, and **loop context** `L` (`brk`/`cont` labels + scope depth)
  for `break`/`continue`. Non-local exits compile to statically-known
  `pop`s (down to the context's depth) followed by a `jump` — the
  runtime never needs to unwind dynamically.

## Layouts of the new constructs

`for {init} c {post} {body}` at layout `Γ` (init extends it to `Γi`;
everything below runs in init's hoisted function scope):

```
<init>
label Lcond:  <c> ; iszero ; jumpi Lexit
<body>                        -- a block; L := ⟨Lexit, Lpost, |Γi|⟩
label Lpost:  <post>          -- a block; L := none (break/continue illegal)
jump Lcond
label Lexit:  pop × (|Γi| − |Γ|)
```

`function f(p₁…pₙ) -> r { body }` (emitted inline where declared, jumped
over; `rets ≤ 1` for now):

```
jump Lskip
label Lentry:  <body>         -- Γf := params ++ rets; F := ⟨Lexit, n+k⟩
label Lexit:   pop × n ; (swap1 if k = 1) ; dynJump
label Lskip:
```

A call `f(a₁…aₙ)` pushes the frame the callee expects — return address
below `k` zero-initialized return slots below the arguments (first
argument on top), matching the callee `VEnv` `params.zip args ++
bindZeros rets` with the return address in the callee's untouched σ:

```
pushLabel Lret ; push 0 × k ; <args right-to-left> ; jump Lentry
label Lret:                   -- stack: r₁…r_k on top of the caller's
```
-/

namespace YulEvmCompiler

open YulSemantics (Expr Stmt Block Ident)
open YulSemantics.EVM (Op litValue U256)

/-- Compile-time information about a user-defined function. -/
structure FunInfo where
  /-- The label of the function's entry `JUMPDEST`. -/
  entry : Label
  /-- Number of parameters. -/
  arity : Nat
  /-- Number of return values (`≤ 1` in the verified fragment). -/
  rets : Nat
  deriving Repr, DecidableEq

/-- One lexical scope's worth of function infos. -/
abbrev FScopeInfo := List (Ident × FunInfo)

/-- The compile-time function environment: a stack of scopes, innermost
first — the mirror of the semantics' `FunEnv`. -/
abbrev FMap := List FScopeInfo

/-- Resolve a function name to its info and the scopes visible at its
definition site. Mirrors `YulSemantics.lookupFun`. -/
def lookupF : FMap → Ident → Option (FunInfo × FMap)
  | [], _ => none
  | scope :: rest, f =>
    match scope.find? (fun p => p.1 = f) with
    | some p => some (p.2, scope :: rest)
    | none => lookupF rest f

/-- The enclosing loop's control context. -/
structure LoopCtx where
  /-- Where `break` jumps (the loop's exit label, before its pops). -/
  brk : Label
  /-- Where `continue` jumps (the label of the `post` block). -/
  cont : Label
  /-- `|Γ|` at the loop's iteration scope; `break`/`continue` pop down to
  this depth before jumping. -/
  depth : Nat
  deriving Repr

/-- The enclosing function's control context. -/
structure FunCtx where
  /-- Where `leave` (and normal completion) jumps: the epilogue label. -/
  exit : Label
  /-- `|Γ|` of the function frame (params + rets); `leave` pops down to
  this depth before jumping. -/
  depth : Nat
  deriving Repr

/-- Hoist a block's function definitions into a compile-time scope,
assigning one fresh entry label per function. Mirrors
`YulSemantics.hoist` (same names, same order). -/
def hoistInfos (n : Nat) : List (Stmt Op) → FScopeInfo × Nat
  | [] => ([], n)
  | .funDef f ps rs _ :: rest =>
      let (scope, n1) := hoistInfos (n + 1) rest
      ((f, ⟨n, ps.length, rs.length⟩) :: scope, n1)
  | _ :: rest => hoistInfos n rest

mutual

/-- Compile an expression at layout `Γ` with `off` temporaries above the
variable region (temporaries include pending return addresses and return
slots of enclosing calls). -/
def compileExpr (Φ : FMap) (Γ : List Ident) (off : Nat) (n : Nat) :
    Expr Op → Option (List Asm × Nat)
  | .lit l => some ([.push (litValue l)], n)
  | .var x => do
      let idx ← Γ.findIdx? (fun y => y = x)
      if h : off + idx < 16 then
        some ([.dup ⟨off + idx, h⟩], n)
      else
        none                      -- too deep for DUP16 (needs EIP-8024)
  | .builtin op args => do
      let (argCode, n1) ← compileArgs Φ Γ off n args
      some (argCode ++ [.op op], n1)
  | .call f args => do
      let (info, _) ← lookupF Φ f
      let lret := n
      let (argCode, n1) ← compileArgs Φ Γ (off + 1 + info.rets) (n + 1) args
      some (.pushLabel lret :: (List.replicate info.rets (.push 0)
        ++ argCode ++ [.jump info.entry, .label lret]), n1)

/-- Compile an argument list, last argument first (Yul's right-to-left
order); each pending argument value deepens `off` for the ones still to
be compiled. -/
def compileArgs (Φ : FMap) (Γ : List Ident) (off : Nat) (n : Nat) :
    List (Expr Op) → Option (List Asm × Nat)
  | [] => some ([], n)
  | e :: rest => do
      let (restCode, n1) ← compileArgs Φ Γ off n rest
      let (eCode, n2) ← compileExpr Φ Γ (off + rest.length) n1 e
      some (restCode ++ eCode, n2)

end

mutual

/-- Compile a `{ … }` block: hoist its function definitions into a fresh
Φ-scope, compile the body under it, pop the block's locals on exit. The
layout is unchanged across the block (mirroring the semantics'
`restore`). -/
def compileBlock (Φ : FMap) (Γ : List Ident) (F : Option FunCtx)
    (L : Option LoopCtx) (n : Nat) (body : List (Stmt Op)) :
    Option (List Asm × Nat) := do
  let (scope, n1) := hoistInfos n body
  if (scope.map Prod.fst).Nodup then    -- Yul forbids duplicate functions
    let (isb, Γ', n2) ← compileStmts (scope :: Φ) Γ F L n1 body
    some (isb ++ List.replicate (Γ'.length - Γ.length) .pop, n2)
  else
    none
  termination_by 2 * sizeOf body + 1

/-- Compile a statement at layout `Γ` under contexts `F`/`L`; returns the
code and the layout after the statement. -/
def compileStmt (Φ : FMap) (Γ : List Ident) (F : Option FunCtx)
    (L : Option LoopCtx) (n : Nat) :
    Stmt Op → Option (List Asm × List Ident × Nat)
  | .exprStmt e => do
      let (is, n1) ← compileExpr Φ Γ 0 n e
      some (is, Γ, n1)
  | .letDecl xs none =>
      some (List.replicate xs.length (.push 0), xs ++ Γ, n)
  | .letDecl xs (some e) =>
      match xs with
      | [x] => do
          let (is, n1) ← compileExpr Φ Γ 0 n e
          some (is, x :: Γ, n1)
      | _ => none                 -- multi-value `let` still unsupported
  | .assign xs e =>
      match xs with
      | [x] => do
          let (is, n1) ← compileExpr Φ Γ 0 n e
          let idx ← Γ.findIdx? (fun y => y = x)
          if h : idx < 16 then
            some (is ++ [.swap ⟨idx, h⟩, .pop], Γ, n1)
          else
            none                  -- too deep for SWAP16 (needs EIP-8024)
      | _ => none
  | .block body => do
      let (is, n1) ← compileBlock Φ Γ F L n body
      some (is, Γ, n1)
  | .cond c body => do
      let lend := n
      let (cCode, n1) ← compileExpr Φ Γ 0 (n + 1) c
      let (bodyCode, n2) ← compileBlock Φ Γ F L n1 body
      some (cCode ++ [.op .iszero, .jumpi lend] ++ bodyCode
        ++ [.label lend], Γ, n2)
  | .forLoop init c post body => do
      let (scope, n0) := hoistInfos n init
      if !(scope.map Prod.fst).Nodup then none else
      let Φ' := scope :: Φ
      let lcond := n0
      let lpost := n0 + 1
      let lexit := n0 + 2
      let (initCode, Γi, n1) ← compileStmts Φ' Γ F L (n0 + 3) init
      let (cCode, n2) ← compileExpr Φ' Γi 0 n1 c
      let (bodyCode, n3) ←
        compileBlock Φ' Γi F (some ⟨lexit, lpost, Γi.length⟩) n2 body
      let (postCode, n4) ← compileBlock Φ' Γi F none n3 post
      some (initCode
        ++ [.label lcond] ++ cCode ++ [.op .iszero, .jumpi lexit]
        ++ bodyCode
        ++ [.label lpost] ++ postCode ++ [.jump lcond]
        ++ [.label lexit] ++ List.replicate (Γi.length - Γ.length) .pop,
        Γ, n4)
  | .funDef f _ps rs body => do
      let (info, _) ← lookupF Φ f
      -- `Nodup`: params may not shadow rets (or each other) — the epilogue
      -- reads return values off the stack region by *position*, which only
      -- agrees with the semantics' name-based `VEnv.get` without shadowing.
      if rs.length ≤ 1 ∧ (_ps ++ rs).Nodup then
        let lexit := n
        let lskip := n + 1
        let Γf := _ps ++ rs
        let (bodyCode, n1) ←
          compileBlock Φ Γf (some ⟨lexit, Γf.length⟩) none (n + 2) body
        some (.jump lskip :: .label info.entry :: bodyCode
          ++ [.label lexit]
          ++ List.replicate _ps.length .pop
          ++ (if rs.length = 1 then [.swap 0] else [])
          ++ [.dynJump, .label lskip], Γ, n1)
      else
        none                      -- multi-value returns unsupported
  | .break => do
      let l ← L
      some (List.replicate (Γ.length - l.depth) .pop ++ [.jump l.brk], Γ, n)
  | .continue => do
      let l ← L
      some (List.replicate (Γ.length - l.depth) .pop ++ [.jump l.cont], Γ, n)
  | .leave => do
      let f ← F
      some (List.replicate (Γ.length - f.depth) .pop ++ [.jump f.exit], Γ, n)
  | .switch c cases dflt => do
      -- `lend` (fresh, smallest) marks the merge point; evaluate `c` (leaving the scrutinee
      -- on the stack), dispatch through the case comparisons, else run the default block.
      let lend := n
      let (cCode, n1) ← compileExpr Φ Γ 0 (n + 1) c
      let (casesAsm, n2) ← compileSwitchCases Φ Γ F L lend n1 cases
      let (defAsm, n3) ← compileBlock Φ Γ F L n2 (match dflt with | some b => b | none => [])
      some (cCode ++ casesAsm ++ .pop :: defAsm ++ [.label lend], Γ, n3)
  termination_by s => 2 * sizeOf s
  decreasing_by
    all_goals simp_wf
    all_goals (first | omega | (cases dflt <;> simp_all <;> omega))

/-- Compile a statement sequence, threading layout and counter. -/
def compileStmts (Φ : FMap) (Γ : List Ident) (F : Option FunCtx)
    (L : Option LoopCtx) (n : Nat) :
    List (Stmt Op) → Option (List Asm × List Ident × Nat)
  | [] => some ([], Γ, n)
  | s :: rest => do
      let (is1, Γ1, n1) ← compileStmt Φ Γ F L n s
      let (is2, Γ2, n2) ← compileStmts Φ Γ1 F L n1 rest
      some (is1 ++ is2, Γ2, n2)
  termination_by ss => 2 * sizeOf ss

/-- Compile a `switch`'s case-dispatch chain, with the scrutinee value on top of the stack.
Each case compares `dup;push v;eq`; on a match it falls through the `jumpi`, pops the scrutinee,
runs the case body (a block at `Γ`), and jumps to `lend`; on a mismatch it skips to the next case
label. Falling off the end leaves the scrutinee on the stack for the caller's default handling. -/
def compileSwitchCases (Φ : FMap) (Γ : List Ident) (F : Option FunCtx)
    (L : Option LoopCtx) (lend : Label) (n : Nat) :
    List (YulSemantics.Literal × Block Op) → Option (List Asm × Nat)
  | [] => some ([], n)
  | (v, b) :: rest => do
      let lnext := n
      let (bAsm, n1) ← compileBlock Φ Γ F L (n + 1) b
      let (restAsm, n2) ← compileSwitchCases Φ Γ F L lend n1 rest
      some ([.dup 0, .push (litValue v), .op .eq, .op .iszero, .jumpi lnext, .pop]
        ++ bAsm ++ [.jump lend, .label lnext] ++ restAsm, n2)
  termination_by cs => 2 * sizeOf cs + 1

end

/-- Compile a whole program (the top-level block): hoist its functions,
compile from the empty layout with no enclosing contexts, then **check
label well-formedness** and lower to the byte-level IR. The check is what
hands the correctness proof unique/defined labels with zero freshness
bookkeeping. -/
def compileProgram (prog : Block Op) : Option (List Asm) := do
  let (scope, n0) := hoistInfos 0 prog
  if !(scope.map Prod.fst).Nodup then none else
  let (asm, _, _) ← compileStmts [scope] [] none none n0 prog
  if wfCheck asm then some asm else none

/-- The full pipeline: Yul → labeled assembly → byte-level IR. -/
def compile (prog : Block Op) : Option (List Instr) := do
  let asm ← compileProgram prog
  lowerProg asm

end YulEvmCompiler
