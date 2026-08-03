import YulEvmCompiler.Asm
import YulEvmCompiler.SsaCfg.Spec.Ir
import YulEvmCompiler.SsaCfg.Spec.Dom
import Std.Data.HashMap
set_option warningAsError true
/-!
# YulEvmCompiler.SsaCfg.Implementation.ToAsm

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

/-- Reorder a keep-list by **next use** (Koopman stack scheduling): values
whose next use comes sooner sit nearer the top, so successive operations
find their operands surfacing instead of fishing them up from depth; values
without an upcoming in-block use keep their relative order below, and the
return address stays at the bottom. -/
def orderByFuture (kept : List SSlot) (future : List ValId) : List SSlot :=
  let ranked := future.filterMap fun v =>
    if kept.contains (.val v) then some (SSlot.val v) else none
  let ranked := dedup ranked []
  let rest := kept.filter fun s => !ranked.contains s && s != .retAddr
  ranked ++ rest ++ (if kept.contains .retAddr then [.retAddr] else [])
where
  dedup : List SSlot → List SSlot → List SSlot
    | [], seen => seen.reverse
    | s :: rest, seen =>
      if seen.contains s then dedup rest seen else dedup rest (s :: seen)

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

/-- The emission state: the call-return-label counter and the current
function's **entry-layout table** — the forward-pass inheritance that makes
edge shuffles cheap (see `edgeTargetLayout`). -/
structure EmitSt where
  nextLabel : Nat
  layouts : Std.HashMap BlockId (List SSlot) := {}

/-- The emission monad. -/
abbrev E := StateT EmitSt Option

def freshLabel : E Label := fun s =>
  some (s.nextLabel, { s with nextLabel := s.nextLabel + 1 })

def liftE {α} : Option α → E α
  | some a => pure a
  | none => fun _ => none

def getLayout (b : BlockId) : E (Option (List SSlot)) := fun s =>
  some (s.layouts[b]?, s)

def setLayout (b : BlockId) (lay : List SSlot) : E Unit := fun s =>
  some ((), { s with layouts := s.layouts.insert b lay })

/-- Clear the layout table (block ids are function-local). -/
def resetLayouts : E Unit := fun s => some ((), { s with layouts := {} })

/-- Substitute a target-side layout into source-side terms: each parameter
replaced by the corresponding edge argument (the parallel copy, as a stack
target). -/
def substLayout (lay : List SSlot) (params args : List ValId) : List SSlot :=
  let sub := params.zip args
  lay.map fun s =>
    match s with
    | .val v =>
      match sub.find? (·.1 = v) with
      | some pa => .val pa.2
      | none => .val v
    | s => s

/-- Rename each `(arg, param)` pair's first occurrence in the stack. -/
def renameArgs : List (ValId × ValId) → List SSlot → Option (List SSlot)
  | [], sym => some sym
  | (a, p) :: rest, sym =>
    match idxOf sym (.val a) with
    | some i => renameArgs rest (sym.set i (.val p))
    | none => none

/-- Build an **inherited entry-layout candidate** for target block `tb` from
the predecessor's stack `sym` at edge `e` (solc-style forward layout
inheritance): rename the edge arguments to the target's parameters in place,
drop dead and duplicate slots, and accept only if every parameter and
live-in value is present — otherwise the caller falls back to the canonical
layout. Inheriting the predecessor's order makes the recording edge's
shuffle (near-)empty and keeps chains of small blocks from churning the
stack. -/
def inheritCandidate (liveInT : List ValId) (tb : Block) (e : Edge)
    (sym : List SSlot) : Option (List SSlot) := do
  let renamed ← renameArgs (e.args.zip tb.params) sym
  let keepVals := tb.params ++ liveInT
  let lay := go renamed keepVals []
  if tb.params.all (fun p => lay.contains (.val p))
      && liveInT.all (fun v => lay.contains (.val v))
      && !(lay.any (fun s => match s with | .code _ => true | _ => false))
  then some lay else none
where
  go : List SSlot → List ValId → List SSlot → List SSlot
    | [], _, seen => seen.reverse
    | .val v :: rest, keepVals, seen =>
      if keepVals.contains v && !seen.contains (.val v) then
        go rest keepVals (.val v :: seen)
      else go rest keepVals seen
    | .retAddr :: rest, keepVals, seen =>
      if seen.contains .retAddr then go rest keepVals seen
      else go rest keepVals (.retAddr :: seen)
    | .code l :: rest, keepVals, seen => go rest keepVals (.code l :: seen)

/-- The layout a control-flow edge must establish, in *source-side* terms —
**consulting or recording** the target's entry layout: the first edge to
reach a block donates its (filtered, renamed) stack as the block's inherited
entry layout; later edges and the block's own emission consult the recorded
one. Falls back to the canonical `layoutOf` when inheritance is impossible
(an argument not on the stack, a missing live-in). -/
def edgeTargetLayout (isFunc : Bool) (f : Func) (liveIn : Array (List ValId))
    (e : Edge) (sym : List SSlot) : E (List SSlot) := do
  let tb ← liftE f.blocks[e.target]?
  if e.args.length ≠ tb.params.length then liftE none else
  let lay? ← getLayout e.target
  let lay ← match lay? with
    | some lay => pure lay
    | none =>
      let liveInT := diffS (liveIn[e.target]?.getD []) tb.params
      let cand := (inheritCandidate liveInT tb e sym).getD
        (layoutOf isFunc (liveIn[e.target]?.getD []) tb)
      setLayout e.target cand
      pure cand
  pure (substLayout lay tb.params e.args)

/-- Emit one instruction from symbolic stack `sym`; `needed` is the
needed-after set. Returns the emitted `Asm` and the new symbolic stack. -/
def emitInstr (P : Prog) (L : LabelMap) (useFuture : Bool) (sym : List SSlot)
    (needed : List ValId) (future : List ValId) :
    Instr → E (List Asm × List SSlot)
  | .const d v =>
    pure ([.push v], .val d :: sym)
  | .op ds yop as => do
    let keep := if useFuture then orderByFuture (keepOf sym needed) future
                else keepOf sym needed
    -- commutative operations accept either operand order on the stack (the
    -- EVM computes the same word); try both and keep the cheaper shuffle
    let argOrders :=
      match yop, as with
      | .add, [a, b] | .mul, [a, b] | .and, [a, b]
      | .or, [a, b] | .xor, [a, b] | .eq, [a, b] =>
        if a = b then [[a, b]] else [[a, b], [b, a]]
      | _, _ => [as]
    let best := argOrders.foldl (init := none) fun acc args =>
      match shuffle sym (args.map .val ++ keep) with
      | some ops =>
        match acc with
        | some (prev, _) =>
          if ops.length < (prev : List Asm).length then some (ops, args) else acc
        | none => some (ops, args)
      | none => acc
    match best with
    | some (ops, _) => pure (ops ++ [.op yop], ds.map .val ++ keep)
    | none => liftE none
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
    let keep :=
      if useFuture then orderByFuture
        (keepOf sym (as.foldl (fun acc a => insertSorted a acc) needed)) future
      else keepOf sym (as.foldl (fun acc a => insertSorted a acc) needed)
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
    let τ ← edgeTargetLayout isFunc f liveIn e sym
    let ops ← liftE (shuffle sym τ)
    pure (ops ++ [.jump (blkLabel L fidx e.target)])
  | .branch c et ef => do
    let τt ← edgeTargetLayout isFunc f liveIn et sym
    -- the false edge's candidate is donated by the post-`jumpi` stack `τt`
    let τf ← edgeTargetLayout isFunc f liveIn ef τt
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
    let rest := removeOnce sym (as.map .val)
    let target := as.map (SSlot.val) ++ rest
    let ops ← liftE (shuffle sym target)
    -- Dead barrier (never executed — `yop` always halts): the
    -- stack-certificate analyzer walks code linearly past a halting op, so
    -- without this it would fall through into the next block's label with a
    -- depleted frame and record an inconsistent layout there. Consume the
    -- leftover frame and end on an instruction with no fall-through
    -- successor: in a function, pad the leftover words to exactly `nrets`,
    -- lift the return address with the epilogue rotation, and `dynJump`
    -- (whose recorded frame also feeds the analyzer's return-arity
    -- observations); in `main`, pop everything and jump to the terminal
    -- label, whose recorded frame is empty.
    if isFunc then
      let k := f.nrets
      if k > 16 then liftE none else
      let words := rest.length - 1
      let pad : List Asm :=
        if words < k then List.replicate (k - words) (.push 0)
        else List.replicate (words - k) .pop
      let rots := (List.range k).filterMap fun j =>
        if h : j < 16 then some (Asm.swap ⟨j, h⟩) else none
      pure (ops ++ [.op yop] ++ pad ++ rots ++ [.dynJump])
    else
      pure (ops ++ [.op yop]
        ++ List.replicate rest.length .pop ++ [.jump L.endLabel])

/-- Emit one block: its label, its instructions (with per-position
needed-after sets), its terminator. -/
def emitBlock (P : Prog) (L : LabelMap) (ord : Bool) (fidx : Option Nat)
    (f : Func) (liveIn : Array (List ValId)) (bid : BlockId) (b : Block) :
    E (List Asm) := do
  let isFunc := fidx.isSome
  let sym0 ←
    if bid = f.entry then
      pure (f.params.map SSlot.val ++ (if isFunc then [SSlot.retAddr] else []))
    else do
      let rec? ← getLayout bid
      pure (rec?.getD (layoutOf isFunc (liveIn[bid]?.getD []) b))
  -- pin the chosen layout so later (back-)edges consult exactly it
  setLayout bid sym0
  let lout := b.term.edges.foldl (init := []) fun acc e =>
    unionS (liveIn[e.target]?.getD []) acc
  let base := unionS (unionS b.term.uses []) lout
  let needs := neededAfter b.instrs base
  -- per-position ordered future-use sequences (next-use scheduling); empty
  -- when the mode is off, which makes `orderByFuture` the identity order
  let futures :=
    if ord then
      (b.instrs.foldr (init := ([([] : List ValId)], b.term.uses))
        fun i (acc : List (List ValId) × List ValId) =>
          let (lst, fut) := acc
          (fut :: lst, i.uses ++ fut)).1
    else List.replicate b.instrs.length []
  let (body, symEnd) ← (b.instrs.zip (needs.zip futures)).foldlM
    (init := (([] : List Asm), sym0)) fun (acc, sym) (i, need, future) => do
      let (asm, sym') ← emitInstr P L ord sym need future i
      pure (acc ++ asm, sym')
  let tasm ← emitTerm isFunc f L fidx liveIn symEnd b.term
  pure (.label (blkLabel L fidx bid) :: body ++ tasm)

/-- Emit a whole function (blocks in index order; the entry must be block 0,
which both construction entry points guarantee). -/
def emitFunc (P : Prog) (L : LabelMap) (ord : Bool) (fidx : Option Nat)
    (f : Func) : E (List Asm) := do
  if f.entry ≠ 0 then liftE none else
  resetLayouts
  let liveIn ← liftE (liveInSets f)
  -- entry live-ins must be covered by the parameters
  if diffS (liveIn[0]?.getD []) f.params ≠ [] then liftE none else
  let idxBlocks := (List.range f.blocks.size).zip f.blocks.toList
  idxBlocks.foldlM (init := []) fun acc (bid, b) => do
    let asm ← emitBlock P L ord fidx f liveIn bid b
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
def emitProgOrd (ord : Bool) (P : Prog) : Option (List Asm) := do
  if !(P.main.params.isEmpty && P.main.nrets = 0) then none else
  let L := mkLabelMap P
  let build : E (List Asm) := do
    let asmMain ← emitFunc P L ord none P.main
    let idxFuncs := (List.range P.funcs.size).zip P.funcs.toList
    let asmFns ← idxFuncs.foldlM (init := []) fun acc (i, f) => do
      let a ← emitFunc P L ord (some i) f
      pure (acc ++ a)
    pure (asmMain ++ asmFns ++ [.label L.endLabel])
  let (asm, _) ← build ⟨L.endLabel + 1, {}⟩
  some (elideJumps asm)

/-- The default emission (next-use ordering off); `compileViaSsa` tries both
modes and keeps the statically cheaper artifact. -/
def emitProg (P : Prog) : Option (List Asm) :=
  emitProgOrd false P

end ToAsm

end YulEvmCompiler.SsaCfg
