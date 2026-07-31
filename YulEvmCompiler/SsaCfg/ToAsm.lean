import YulEvmCompiler.Asm
import YulEvmCompiler.SsaCfg.Ir
set_option warningAsError true
/-!
# YulEvmCompiler.SsaCfg.ToAsm

**Code generation**: `yul-ssa-cfg` → the existing labeled `Asm` IR.

This is the gas payoff of the dialect: values live where their *uses* want
them, not where lexical scope pinned them. The generator tracks a **symbolic
stack** (`SSlot` list, top first) through every block:

* each block has a deterministic **entry layout** — its parameters on top,
  then its non-parameter live-in values (sorted), then (inside a function)
  the opaque return address at the bottom;
* an instruction's operands are brought to the top by a greedy **shuffler**
  (`DUP` for values still needed afterwards, `SWAP` cycles, `POP` for dead
  values — liveness-driven, so the POP/DUP/SWAP traffic the classic
  scope-pinned layout emits by construction simply never appears);
* a control-flow edge realizes its parallel copy (block arguments →
  parameters) as a stack shuffle onto the target's entry layout;
* `branch` shuffles to `cond :: layout(true-edge)`, emits `jumpi`, then
  shuffles the fall-through stack onto the false edge's layout;
* calls keep the classic convention (push return label, arguments on top —
  first argument topmost — `jump` to the entry, `dynJump` back), so
  `AsmSem`'s `AVal.code` discipline is untouched;
* `ret` in a function shuffles to `[retAddr, results…]` and `dynJump`s;
  `ret []` in main pops everything and jumps to the terminal label, so a
  `.normal` fall-through still runs off the end of the bytecode exactly like
  the classic backend.

The shuffler is fuel-bounded and **checked**: it must reproduce the target
layout exactly or the whole compilation rejects (`none`) — following the
repo's checked-not-proved discipline, a shuffling bug is a rejection (and a
fallback to the classic backend), never a miscompilation. Depth limits
(`DUP16`/`SWAP16`) reject the same way.

The output runs through the exact same gates as the classic backend
(`wfCheck` here; `optimizeAsm`, `stackOK2`, `lowerProg` in `compileViaSsa`),
so Phase B, the overflow certificate, and the assembler are reused verbatim.
-/

namespace YulEvmCompiler.SsaCfg

open YulSemantics.EVM (U256 Op)

/-- A symbolic stack slot: an SSA value, a pushed call-return label (known),
or the enclosing function's opaque return address. -/
inductive SSlot
  | val (v : ValId)
  | code (l : Label)
  | retAddr
  deriving Repr, DecidableEq, Inhabited

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

/-! ## The greedy checked shuffler -/

def countOcc (σ : List SSlot) (s : SSlot) : Nat :=
  σ.countP (· == s)

/-- Find the index of `s` in `σ`. -/
def idxOf (σ : List SSlot) (s : SSlot) : Option Nat :=
  σ.findIdx? (· == s)

/-- Apply `SWAP(j)` (exchange positions 0 and `j`, `1 ≤ j ≤ 16`). -/
def swapAt (σ : List SSlot) (j : Nat) : Option (List SSlot) := do
  let a ← σ[0]?
  let b ← σ[j]?
  some ((σ.set 0 b).set j a)

/-- One greedy shuffle step; returns the op, the new stack, or `none` when
finished / stuck (stuck is caught by the caller's final equality check). -/
def shuffleGo (τ : List SSlot) : Nat → List SSlot → List Asm →
    Option (List Asm × List SSlot)
  | 0, _, _ => none
  | fuel + 1, σ, acc =>
    if σ = τ then some (acc.reverse, σ) else
    match σ with
    | [] =>
      -- deficit only: dup/push impossible from empty; fail
      none
    | top :: rest =>
      -- 1. surplus top → POP
      if countOcc σ top > countOcc τ top then
        shuffleGo τ fuel rest (.pop :: acc)
      else
        -- 2. a deficit value → DUP it up
        match τ.find? (fun s => countOcc σ s < countOcc τ s) with
        | some need =>
          match idxOf σ need with
          | some i =>
            if h : i < 16 then
              shuffleGo τ fuel (need :: σ) (.dup ⟨i, h⟩ :: acc)
            else none
          | none => none
        | none =>
          -- multisets agree; only swaps remain
          -- 3. a place where the top belongs (and is wrong now)
          let fix := (List.range (min σ.length 17)).find? fun j =>
            0 < j ∧ σ[j]? ≠ τ[j]? ∧ τ[j]? = some top
          match fix with
          | some j =>
            match swapAt σ j with
            | some σ' =>
              if h : j - 1 < 16 then
                shuffleGo τ fuel σ' (.swap ⟨j - 1, h⟩ :: acc)
              else none
            | none => none
          | none =>
            -- 4. bring the shallowest mismatched value to the top
            let mis := (List.range (min σ.length 17)).find? fun j =>
              0 < j ∧ σ[j]? ≠ τ[j]?
            match mis with
            | some j =>
              match swapAt σ j with
              | some σ' =>
                if h : j - 1 < 16 then
                  shuffleGo τ fuel σ' (.swap ⟨j - 1, h⟩ :: acc)
                else none
              | none => none
            | none => none

/-- Shuffle the symbolic stack `σ` onto the exact layout `τ` with
`DUP`/`SWAP`/`POP`, or reject. The result is *checked* (`shuffleGo` only
returns on `σ = τ`). -/
def shuffle (σ τ : List SSlot) : Option (List Asm) := do
  let fuel := (σ.length + τ.length + 2) * (σ.length + τ.length + 2)
  let (ops, final) ← shuffleGo τ fuel σ []
  if final = τ then some ops else none

/-! ## Layouts -/

/-- Remove one occurrence of each of `xs` from `σ` (used for halting-op
argument targets, where whatever sits below the arguments is irrelevant). -/
def removeOnce (σ : List SSlot) : List SSlot → List SSlot
  | [] => σ
  | x :: rest =>
    match idxOf σ x with
    | some i => removeOnce (σ.eraseIdx i) rest
    | none => removeOnce σ rest

/-- The canonical entry layout of block `b` in function `f`: parameters on
top (in order), then the non-parameter live-in values (ascending), then the
function's return address (functions only; `main` has none). -/
def layoutOf (isFunc : Bool) (liveIn : List ValId) (b : Block) : List SSlot :=
  (b.params.map .val)
    ++ ((diffS liveIn b.params).map .val)
    ++ (if isFunc then [SSlot.retAddr] else [])

/-- Keep-list for continuing execution: the distinct still-needed values of
`σ` in their current relative order, plus the (unique) return address.
Pushed call labels are never kept across an instruction — the only live one
belongs to the call being emitted, which places it explicitly. -/
def keepOf (σ : List SSlot) (needed : List ValId) : List SSlot :=
  go σ []
where
  go : List SSlot → List SSlot → List SSlot
    | [], _ => []
    | .val v :: rest, seen =>
      if needed.contains v && !seen.contains (.val v) then
        .val v :: go rest (.val v :: seen)
      else go rest seen
    | .code _ :: rest, seen => go rest seen
    | .retAddr :: rest, seen =>
      if seen.contains .retAddr then go rest seen
      else .retAddr :: go rest (.retAddr :: seen)

/-! ## Emission -/

/-- Per-instruction needed-after sets: for each position, the values any
later instruction, the terminator, or a live-out successor still needs.
Returns the list aligned with `instrs`. -/
def neededAfter (instrs : List Instr) (base : List ValId) :
    List (List ValId) :=
  (go instrs).1
where
  go : List Instr → List (List ValId) × List ValId
    | [] => ([], base)
    | i :: rest =>
      let (lst, nb) := go rest
      (nb :: lst, unionS (unionS i.uses []) (diffS nb (unionS i.defs [])))

/-- Static label numbering: `main`'s blocks first, then each function's, then
the terminal label; call-site return labels are allocated past `endLabel` by
the emission counter. -/
structure LabelMap where
  funcBase : Array Nat
  endLabel : Nat

def mkLabelMap (P : Prog) : LabelMap :=
  let (bases, total) := P.funcs.foldl (init := (#[], P.main.blocks.size))
    fun (acc : Array Nat × Nat) f => (acc.1.push acc.2, acc.2 + f.blocks.size)
  ⟨bases, total⟩

/-- The label of block `b` of function `fidx` (`none` = main). -/
def blkLabel (L : LabelMap) (fidx : Option Nat) (b : BlockId) : Label :=
  match fidx with
  | none => b
  | some i => (L.funcBase[i]?.getD 0) + b

/-- The emission monad: the call-return-label counter. -/
abbrev E := StateT Nat Option

def freshLabel : E Label := fun n => some (n, n + 1)

def liftE {α} : Option α → E α
  | some a => pure a
  | none => fun _ => none

/-- The layout a control-flow edge must establish, in *source-side* terms:
the target's entry layout with each parameter replaced by the corresponding
edge argument (the parallel copy, as a stack target). -/
def edgeLayout (isFunc : Bool) (f : Func) (liveIn : Array (List ValId))
    (e : Edge) : Option (List SSlot) := do
  let tb ← f.blocks[e.target]?
  if e.args.length ≠ tb.params.length then none else
  let lay := layoutOf isFunc (liveIn[e.target]?.getD []) tb
  let sub := tb.params.zip e.args
  some (lay.map fun s =>
    match s with
    | .val v =>
      match sub.find? (·.1 = v) with
      | some pa => .val pa.2
      | none => .val v
    | s => s)

/-- Emit one instruction from symbolic stack `sym`; `needed` is the
needed-after set. Returns the emitted `Asm` and the new symbolic stack. -/
def emitInstr (P : Prog) (L : LabelMap) (sym : List SSlot)
    (needed : List ValId) : Instr → E (List Asm × List SSlot)
  | .const d v =>
    pure ([.push v], .val d :: sym)
  | .op ds yop as => do
    let keep := keepOf sym needed
    let target := as.map .val ++ keep
    let ops ← liftE (shuffle sym target)
    pure (ops ++ [.op yop], ds.map .val ++ keep)
  | .call ds fid as => do
    let callee ← liftE P.funcs[fid]?
    if callee.params.length ≠ as.length then liftE none else
    if callee.nrets ≠ ds.length then liftE none else
    let retLab ← freshLabel
    let entryLab := blkLabel L (some fid) callee.entry
    -- The stack-certificate discipline (`checkCert`'s swap rule) only moves
    -- *words* around, so the pushed return label must never be swapped:
    -- first shuffle (words only) so every argument is present below, then
    -- push the label, then `DUP` the arguments above it. The stale argument
    -- copies stay in the caller's frame below the call and are popped by a
    -- later shuffle once dead.
    let keep := keepOf sym (as.foldl (fun acc a => insertSorted a acc) needed)
    let ops1 ← liftE (shuffle sym keep)
    let dups ← liftE <| (as.reverse.foldlM (init := ([], 0)) fun (acc, k) a =>
      match idxOf keep (.val a) with
      | some i =>
        -- depth: `k` previous dups + the return label + position in `keep`
        let d := k + 1 + i
        if h : d < 16 then some (Asm.dup ⟨d, h⟩ :: acc, k + 1) else none
      | none => none : Option (List Asm × Nat))
    pure (ops1 ++ [.pushLabel retLab] ++ dups.1.reverse
        ++ [.jump entryLab, .label retLab],
      ds.map .val ++ keep)

/-- Emit a terminator from symbolic stack `sym`. -/
def emitTerm (isFunc : Bool) (f : Func) (L : LabelMap) (fidx : Option Nat)
    (liveIn : Array (List ValId)) (sym : List SSlot) : Term → E (List Asm)
  | .jump e => do
    let τ ← liftE (edgeLayout isFunc f liveIn e)
    let ops ← liftE (shuffle sym τ)
    pure (ops ++ [.jump (blkLabel L fidx e.target)])
  | .branch c et ef => do
    let τt ← liftE (edgeLayout isFunc f liveIn et)
    let τf ← liftE (edgeLayout isFunc f liveIn ef)
    -- direct scheme: land on the true edge's layout, then shuffle the
    -- fall-through onto the false edge's — possible only when the true
    -- layout still carries everything the false edge needs
    match shuffle sym (.val c :: τt), shuffle τt τf with
    | some opst, some opsf =>
      pure (opst ++ [.jumpi (blkLabel L fidx et.target)]
        ++ opsf ++ [.jump (blkLabel L fidx ef.target)])
    | _, _ =>
      -- stub scheme: branch over a stack `U` keeping every value either
      -- edge needs; the taken edge hops through a fresh stub block that
      -- finishes its shuffle
      let needs := (τt ++ τf).foldl (init := []) fun acc s =>
        match s with
        | .val v => insertSorted v acc
        | _ => acc
      let U := keepOf sym needs
      let stub ← freshLabel
      let ops0 ← liftE (shuffle sym (.val c :: U))
      let opsf ← liftE (shuffle U τf)
      let opst ← liftE (shuffle U τt)
      pure (ops0 ++ [.jumpi stub]
        ++ opsf ++ [.jump (blkLabel L fidx ef.target)]
        ++ [.label stub] ++ opst ++ [.jump (blkLabel L fidx et.target)])
  | .ret xs => do
    if isFunc then
      -- words-only shuffle with the return address untouched at the bottom,
      -- then the classic `SWAP1 … SWAPk` rotation lifts it to the top (the
      -- only certificate-legal way a return address moves)
      let τ := xs.map SSlot.val ++ [SSlot.retAddr]
      let ops ← liftE (shuffle sym τ)
      let k := xs.length
      if k ≤ 16 then
        let rots := (List.range k).filterMap fun j =>
          if h : j < 16 then some (Asm.swap ⟨j, h⟩) else none
        pure (ops ++ rots ++ [.dynJump])
      else liftE none
    else
      if xs ≠ [] then liftE none else
      let ops ← liftE (shuffle sym [])
      pure (ops ++ [.jump L.endLabel])
  | .halt yop as => do
    let target := as.map (SSlot.val) ++ removeOnce sym (as.map .val)
    let ops ← liftE (shuffle sym target)
    pure (ops ++ [.op yop])

/-- Emit one block: its label, its instructions (with per-position
needed-after sets), its terminator. -/
def emitBlock (P : Prog) (L : LabelMap) (fidx : Option Nat) (f : Func)
    (liveIn : Array (List ValId)) (bid : BlockId) (b : Block) :
    E (List Asm) := do
  let isFunc := fidx.isSome
  let sym0 :=
    if bid = f.entry then
      f.params.map SSlot.val ++ (if isFunc then [SSlot.retAddr] else [])
    else layoutOf isFunc (liveIn[bid]?.getD []) b
  let lout := b.term.edges.foldl (init := []) fun acc e =>
    unionS (liveIn[e.target]?.getD []) acc
  let base := unionS (unionS b.term.uses []) lout
  let needs := neededAfter b.instrs base
  let (body, symEnd) ← (b.instrs.zip needs).foldlM
    (init := (([] : List Asm), sym0)) fun (acc, sym) (i, need) => do
      let (asm, sym') ← emitInstr P L sym need i
      pure (acc ++ asm, sym')
  let tasm ← emitTerm isFunc f L fidx liveIn symEnd b.term
  pure (.label (blkLabel L fidx bid) :: body ++ tasm)

/-- Emit a whole function (blocks in index order; the entry must be block 0,
which both construction entry points guarantee). -/
def emitFunc (P : Prog) (L : LabelMap) (fidx : Option Nat) (f : Func) :
    E (List Asm) := do
  if f.entry ≠ 0 then liftE none else
  let liveIn ← liftE (liveInSets f)
  -- entry live-ins must be covered by the parameters
  if diffS (liveIn[0]?.getD []) f.params ≠ [] then liftE none else
  let idxBlocks := (List.range f.blocks.size).zip f.blocks.toList
  idxBlocks.foldlM (init := []) fun acc (bid, b) => do
    let asm ← emitBlock P L fidx f liveIn bid b
    pure (acc ++ asm)

/-- Drop `jump l` when `label l` immediately follows (the block-order
fall-through case). -/
def elideJumps : List Asm → List Asm
  | .jump l :: .label l' :: rest =>
    if l = l' then .label l' :: elideJumps rest
    else .jump l :: .label l' :: elideJumps rest
  | a :: rest => a :: elideJumps rest
  | [] => []

/-- Emit the whole program: `main`'s blocks (entry first, at `pc = 0`), then
every function's, then the terminal label — so `main`'s `ret []` runs off
the end of the code (the implicit `STOP`), exactly like the classic
backend's `.normal` fall-through. -/
def emitProg (P : Prog) : Option (List Asm) := do
  if !(P.main.params.isEmpty && P.main.nrets = 0) then none else
  let L := mkLabelMap P
  let build : E (List Asm) := do
    let asmMain ← emitFunc P L none P.main
    let idxFuncs := (List.range P.funcs.size).zip P.funcs.toList
    let asmFns ← idxFuncs.foldlM (init := []) fun acc (i, f) => do
      let a ← emitFunc P L (some i) f
      pure (acc ++ a)
    pure (asmMain ++ asmFns ++ [.label L.endLabel])
  let (asm, _) ← build (L.endLabel + 1)
  some (elideJumps asm)

end ToAsm

end YulEvmCompiler.SsaCfg
