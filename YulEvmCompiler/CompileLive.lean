import YulEvmCompiler.Compile
import Std.Data.HashSet.Lemmas
set_option warningAsError true
/-!
# Last-use retirement (prototype, unverified)

An alternative statement-level compiler that **retires dead locals as soon as
they die** instead of holding every `let` until its block exits.

## Why

`YulEvmCompiler.compileStmt`'s `.letDecl` prepends to `Γ` and the only pops are
emitted at block exit (`compileBlock`), so on solc-generated IR a long function
accumulates every temporary it ever declares. Only `DUP1`-`DUP16` and
`SWAP1`-`SWAP16` are active, so such a function becomes uncompilable and
`compileSource` falls through to the memory-spilling fallback. On uniswap-v4
`PoolSwap` the worst function holds 280 slots and needs `DUP280`, while a
backward liveness shows its peak *live* set is 20 — and 414 of its 415 functions
peak at 13 or below.

solc has the same 16-slot reach (`EVMVersion::reachableStackDepth`) and fails on
the same variable when forced onto its legacy code transform; it avoids the
problem by always running a liveness-driven layout with eager popping
(`OptimizedEVMCodeTransform`/`StackLayoutGenerator`), keeping memory spilling as
a last resort.

## What this does

After each statement, any block-local whose name no longer occurs in what
remains — the rest of the block, plus whatever the enclosing constructs may
still read — is removed from the operand stack: `POP` when it is on top,
`SWAP k; POP` when it is `k` deep and within reach. Retirement never touches a
slot belonging to an enclosing block (`limit` counts only the current block's
own slots), so `compileBlockLive`'s exit pops and `break`/`continue`/`leave`'s
unwind counts stay exactly `Γ.length - depth`, and a function's parameter/return
frame is never disturbed.

Keeping a variable whenever its name still *occurs* — read or written — is what
makes this safe for later assignments: a variable that is only assigned further
down is never retired out from under the assignment.

## Status

**Unverified prototype.** `compileLive` has no correctness theorem, and the
verified `compile`/`compileObject` and all their proofs are untouched — this is a
separate entry point, in the same spirit as the Asm→Asm scheduler prototype
(#133), so the mechanism can be measured before its simulation proof is
attempted. The recursion is `partial` here for the same reason; a proved version
needs the same `termination_by` measures `Compile.lean` carries.
-/

namespace YulEvmCompiler

open YulSemantics
open YulSemantics.EVM (Op litValue)

/-! ### Occurrence sets -/

mutual
/-- Identifiers occurring in an expression. -/
def liveExprIdents : Expr Op → Std.HashSet Ident → Std.HashSet Ident
  | .lit _, s => s
  | .var x, s => s.insert x
  | .builtin _ args, s => liveArgsIdents args s
  | .call _ args, s => liveArgsIdents args s

def liveArgsIdents : List (Expr Op) → Std.HashSet Ident → Std.HashSet Ident
  | [], s => s
  | e :: rest, s => liveArgsIdents rest (liveExprIdents e s)
end

mutual
/-- Identifiers occurring anywhere in a statement, including declarations and
assignment targets. -/
def liveStmtIdents : Stmt Op → Std.HashSet Ident → Std.HashSet Ident
  | .exprStmt e, s => liveExprIdents e s
  | .letDecl xs none, s => xs.foldl (fun a x => a.insert x) s
  | .letDecl xs (some e), s => liveExprIdents e (xs.foldl (fun a x => a.insert x) s)
  | .assign xs e, s => liveExprIdents e (xs.foldl (fun a x => a.insert x) s)
  | .block body, s => liveStmtsIdents body s
  | .cond c body, s => liveExprIdents c (liveStmtsIdents body s)
  | .funDef _ ps rs body, s =>
      liveStmtsIdents body (ps.foldl (fun a x => a.insert x)
        (rs.foldl (fun a x => a.insert x) s))
  | .forLoop init c post body, s =>
      liveStmtsIdents init (liveExprIdents c
        (liveStmtsIdents post (liveStmtsIdents body s)))
  | .switch c cases dflt, s =>
      liveExprIdents c (liveCasesIdents cases
        (match dflt with | some b => liveStmtsIdents b s | none => s))
  | .break, s => s
  | .continue, s => s
  | .leave, s => s

def liveStmtsIdents : List (Stmt Op) → Std.HashSet Ident → Std.HashSet Ident
  | [], s => s
  | st :: rest, s => liveStmtIdents st (liveStmtsIdents rest s)

def liveCasesIdents : List (Literal × List (Stmt Op)) →
    Std.HashSet Ident → Std.HashSet Ident
  | [], s => s
  | (_, body) :: rest, s => liveStmtsIdents body (liveCasesIdents rest s)
end

/-- `afterSets tail ss` has one entry per element of `ss`: the identifiers
occurring strictly *after* that statement, unioned with `tail`. One backward
pass, so retirement never rescans a suffix. -/
def afterSets (tail : Std.HashSet Ident) :
    List (Stmt Op) → List (Std.HashSet Ident)
  | [] => []
  | _ :: rest =>
      let below := afterSets tail rest
      (match below with
       | [] => tail
       | t :: _ => liveStmtIdents (rest.headD .break) t) :: below

/-! ### Retirement -/

/-- Index of the shallowest retirable slot: a block-local (index `< limit`) whose
name no longer occurs, reachable by `SWAP`. -/
def deadSlot (live : Std.HashSet Ident) (limit : Nat) : List Ident → Nat → Option Nat
  | [], _ => none
  | x :: xs, i =>
      if i ≥ limit || i ≥ 17 then none
      else if live.contains x then deadSlot live limit xs (i + 1)
      else some i

/-- Remove the slot at index `i` by bringing it to the top and popping; the old
top lands where the removed slot was. -/
def retireAt (i : Nat) : List Ident → Option (List Asm × List Ident)
  | [] => none
  | g0 :: rest =>
      if i = 0 then some ([.pop], rest)
      else if h : i - 1 < 16 then
        some ([.swap ⟨i - 1, h⟩, .pop], rest.set (i - 1) g0)
      else none

/-- Retire every dead block-local within reach, shallowest first. `limit` counts
the leading `Γ` entries owned by the current block and shrinks with `Γ`. -/
def retireDead (live : Std.HashSet Ident) :
    Nat → Nat → List Ident → List Asm × List Ident × Nat
  | 0, limit, Γ => ([], Γ, limit)
  | fuel + 1, limit, Γ =>
      match deadSlot live limit Γ 0 with
      | none => ([], Γ, limit)
      | some i =>
          match retireAt i Γ with
          | none => ([], Γ, limit)
          | some (code, Γ') =>
              let (more, Γ'', limit') := retireDead live fuel (limit - 1) Γ'
              (code ++ more, Γ'', limit')

/-! ### The statement layer

Mirrors `Compile.lean`'s mutual block, reusing its expression layer
(`compileExpr`, `compileArgs`, `compileAssigns`) unchanged. The extra `keep`
argument is what the enclosing constructs may still read; `limit` is how many of
`Γ`'s leading slots this block owns. -/

mutual

partial def compileBlockLive (Φ : FMap) (Γ : List Ident) (F : Option FunCtx)
    (L : Option LoopCtx) (keep : Std.HashSet Ident) (n : Nat)
    (body : List (Stmt Op)) : Option (List Asm × Nat) := do
  let (scope, n1) := hoistInfos n body
  if (scope.map Prod.fst).Nodup then
    let (isb, Γ', n2) ← compileStmtsLive (scope :: Φ) Γ F L keep 0 n1
      body (afterSets keep body)
    some (isb ++ List.replicate (Γ'.length - Γ.length) .pop, n2)
  else
    none

partial def compileStmtsLive (Φ : FMap) (Γ : List Ident) (F : Option FunCtx)
    (L : Option LoopCtx) (keep : Std.HashSet Ident) (limit : Nat) (n : Nat) :
    List (Stmt Op) → List (Std.HashSet Ident) →
    Option (List Asm × List Ident × Nat)
  | [], _ => some ([], Γ, n)
  | s :: rest, afters => do
      let after := match afters with | [] => keep | a :: _ => a
      let (is1, Γ1, n1, limit1) ← compileStmtLive Φ Γ F L after limit n s
      let (rcode, Γ2, limit2) := retireDead after Γ1.length limit1 Γ1
      let (is2, Γ3, n2) ← compileStmtsLive Φ Γ2 F L keep limit2 n1 rest
        (match afters with | [] => [] | _ :: t => t)
      some (is1 ++ rcode ++ is2, Γ3, n2)

/-- As `compileStmt`, plus the updated block-local count. `keep` is what follows
this statement (already including the enclosing keep set). -/
partial def compileStmtLive (Φ : FMap) (Γ : List Ident) (F : Option FunCtx)
    (L : Option LoopCtx) (keep : Std.HashSet Ident) (limit : Nat) (n : Nat) :
    Stmt Op → Option (List Asm × List Ident × Nat × Nat)
  | .exprStmt e => do
      let (is, n1) ← compileExpr Φ Γ 0 n e
      some (is, Γ, n1, limit)
  | .letDecl xs none =>
      some (List.replicate xs.length (.push 0), xs ++ Γ, n, limit + xs.length)
  | .letDecl xs (some e) => do
      let (is, n1) ← compileExpr Φ Γ 0 n e
      some (is, xs ++ Γ, n1, limit + xs.length)
  | .assign xs e => do
      let (is, n1) ← compileExpr Φ Γ 0 n e
      let acode ← compileAssigns Γ xs
      some (is ++ acode, Γ, n1, limit)
  | .block body => do
      let (is, n1) ← compileBlockLive Φ Γ F L keep n body
      some (is, Γ, n1, limit)
  | .cond c body => do
      let lend := n
      let (cCode, n1) ← compileExpr Φ Γ 0 (n + 1) c
      let (bodyCode, n2) ← compileBlockLive Φ Γ F L keep n1 body
      some (cCode ++ [.op .iszero, .jumpi lend] ++ bodyCode ++ [.label lend],
        Γ, n2, limit)
  | .forLoop init c post body => do
      let (scope, n0) := hoistInfos n init
      if !(scope.map Prod.fst).Nodup then none else
      let Φ' := scope :: Φ
      let lcond := n0
      let lpost := n0 + 1
      let lexit := n0 + 2
      -- Everything the loop may re-read on a later iteration has to survive
      -- retirement inside `init`, the body and `post`.
      let loopKeep := liveExprIdents c (liveStmtsIdents post
        (liveStmtsIdents body keep))
      let (initCode, Γi, n1, _) ← compileStmtsLive Φ' Γ F L loopKeep 0 (n0 + 3)
        init (afterSets loopKeep init) |>.map
          (fun (a, b, c) => (a, b, c, 0))
      let (cCode, n2) ← compileExpr Φ' Γi 0 n1 c
      let (bodyCode, n3) ←
        compileBlockLive Φ' Γi F (some ⟨lexit, lpost, Γi.length⟩) loopKeep n2 body
      let (postCode, n4) ← compileBlockLive Φ' Γi F none loopKeep n3 post
      some (initCode
        ++ [.label lcond] ++ cCode ++ [.op .iszero, .jumpi lexit]
        ++ bodyCode
        ++ [.label lpost] ++ postCode ++ [.jump lcond]
        ++ [.label lexit] ++ List.replicate (Γi.length - Γ.length) .pop,
        Γ, n4, limit)
  | .funDef f _ps rs body => do
      let (info, _) ← lookupF Φ f
      if rs.length ≤ 16 ∧ (_ps ++ rs).Nodup then
        let lexit := n
        let lskip := n + 1
        let Γf := _ps ++ rs
        -- The epilogue reads the return slots by position, so they — and the
        -- parameter frame below them — must survive the body.
        let frameKeep := rs.foldl (fun a x => a.insert x)
          (_ps.foldl (fun a x => a.insert x) (∅ : Std.HashSet Ident))
        let (bodyCode, n1) ←
          compileBlockLive Φ Γf (some ⟨lexit, Γf.length⟩) none frameKeep (n + 2) body
        some (.jump lskip :: .label info.entry :: bodyCode
          ++ [.label lexit]
          ++ List.replicate _ps.length .pop
          ++ retRot rs.length
          ++ [.dynJump, .label lskip], Γ, n1, limit)
      else
        none
  | .break => do
      let l ← L
      some (List.replicate (Γ.length - l.depth) .pop ++ [.jump l.brk], Γ, n, limit)
  | .continue => do
      let l ← L
      some (List.replicate (Γ.length - l.depth) .pop ++ [.jump l.cont], Γ, n, limit)
  | .leave => do
      let f ← F
      some (List.replicate (Γ.length - f.depth) .pop ++ [.jump f.exit], Γ, n, limit)
  | .switch c cases dflt => do
      let lend := n
      let (cCode, n1) ← compileExpr Φ Γ 0 (n + 1) c
      let (casesAsm, n2) ← compileSwitchCasesLive Φ Γ F L keep lend n1 cases
      let (defAsm, n3) ← compileBlockLive Φ Γ F L keep n2
        (match dflt with | some b => b | none => [])
      some (cCode ++ casesAsm ++ .pop :: defAsm ++ [.label lend], Γ, n3, limit)

partial def compileSwitchCasesLive (Φ : FMap) (Γ : List Ident) (F : Option FunCtx)
    (L : Option LoopCtx) (keep : Std.HashSet Ident) (lend : Label) (n : Nat) :
    List (Literal × Block Op) → Option (List Asm × Nat)
  | [] => some ([], n)
  | (v, b) :: rest => do
      let lnext := n
      let (bAsm, n1) ← compileBlockLive Φ Γ F L keep (n + 1) b
      let (restAsm, n2) ← compileSwitchCasesLive Φ Γ F L keep lend n1 rest
      some ([.dup 0, .push (litValue v), .op .eq, .op .iszero, .jumpi lnext, .pop]
        ++ bAsm ++ [.jump lend, .label lnext] ++ restAsm, n2)

end

/-- `compileProgram` with last-use retirement. -/
def compileProgramLive (prog : Block Op) : Option (List Asm) := do
  let (scope, n0) := hoistInfos 0 prog
  if !(scope.map Prod.fst).Nodup then none else
  let (asm, _, _) ← compileStmtsLive [scope] [] none none ∅ 0 n0
    prog (afterSets ∅ prog)
  if wfCheck asm then some asm else none

/-- `compile` with last-use retirement. Same Asm peephole, same overflow gate,
same lowering — only the layout discipline differs. -/
def compileLive (prog : Block Op) : Option (List Instr) := do
  let asm ← compileProgramLive prog
  let opt := optimizeAsm asm
  if stackOK2 opt then lowerProg opt else none

end YulEvmCompiler
