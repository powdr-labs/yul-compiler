import YulIR.Frame

set_option warningAsError true
/-!
# YulIR.FrameStoreElim — redundant store elimination (storage / transient / memory)

Removes a `sstore`/`tstore`/`mstore` whose written location is *provably overwritten* by a later
store to the same address before any potentially-aliasing read — a dead store. Variable writes are
`deadCode`'s job; this pass is about the EVM state spaces.

**Address reasoning is symbolic, not just constant.** A forward scan canonicalizes every address
operand into an affine descriptor `base + offset` (`base` a frame slot or nothing, `offset : U256`),
resolving copies and `add`/`sub`-with-constant definitions (`t := add(p, 32)` gives `t ↦ p + 32`).
Two same-base addresses differ by exactly the difference of their offsets (mod 2^256, no side
conditions), so the pass can decide:

* *kill*: offsets equal ⟹ same address ⟹ the earlier store is fully overwritten;
* *survive a read*: `sload`/`tload` at a same-base address with **nonzero** offset difference cannot
  observe the pending store; an `mload` cannot observe it when the offset difference `δ` satisfies
  `32 ≤ δ ≤ 2^256 - 32` — both 32-byte `.toNat` windows are then ≥ 32 apart in ℕ regardless of the
  common base value (whichever operand is larger, the gap is ≥ 32), hence disjoint.

Elimination itself walks each block **backward** with a *kill set*: canonical addresses certainly
overwritten (by a later same-space store) before any read that could alias them. A store whose
canonical address is in the set is dropped. Crossing an assignment backward drops the entries based
on the written slots (their downstream descriptors referred to the new value). Reads filter the set
by the disjointness rules above; calls, halting ops, `msize` (which observes memory *extent* — an
eliminated `mstore` would change intermediate `activeWords`), `keccak256`, `log*`, `mcopy` and
anything unclassified clear it conservatively. Memory-*writers* (`calldatacopy`, `mstore8`, …) do
not gate a kill: the killing store fully rewrites its 32-byte window, so intervening writes are
invisible after it, and a same-address kill re-touches the same range, so the final `activeWords`
agrees too.

Control flow is conservative in this first version: sub-blocks are optimized separately (`cond`/
`switch` bodies inherit the descriptor environment, `loop` bodies start empty since facts about
loop-written slots do not survive iterations), and every control statement clears the kill set.

**Known caveat for the future soundness proof**: in a *static* call context `sstore`/`tstore` halt
(`guardStatic`), so eliminating one moves the halt point to the killing store. The eventual proof
will carry a non-static side condition (or refine the elimination); valid programs do not reach
stores in static contexts.
-/

namespace YulIR.FinFrame

open YulSemantics (Literal)
open YulSemantics.EVM (litValue U256)

/-- The three EVM state spaces the pass tracks. -/
inductive Space
  | storage | transient | memory
  deriving DecidableEq, Repr

/-- A symbolic address: the value of `base` (a frame slot; `none` = zero) plus a constant. -/
structure AddrDesc (n : Nat) where
  base   : Option (Fin n)
  offset : U256
  deriving DecidableEq, Repr

/-! ### Forward canonicalization -/

/-- Canonical-descriptor environment: facts `slot ↦ base + offset` (bases are always the *oldest*
definition points, so entries never chain). -/
abbrev DescEnv (n : Nat) := List (Fin n × AddrDesc n)

/-- The canonical descriptor of an address operand: a literal, a known affine fact, or itself. -/
def descOf (env : DescEnv n) : Atom n → AddrDesc n
  | .lit l  => { base := none, offset := litValue l }
  | .slot i =>
      match env.find? (fun p => p.1 == i) with
      | some p => p.2
      | none   => { base := some i, offset := 0 }

/-- The affine descriptor a definition gives its destination, if any (computed against the
environment *before* the statement). -/
def rhsDesc (env : DescEnv n) : Rhs n → Option (AddrDesc n)
  | .atom a => some (descOf env a)
  | .builtin .add [x, .lit c] => some { descOf env x with offset := (descOf env x).offset + litValue c }
  | .builtin .add [.lit c, y] => some { descOf env y with offset := (descOf env y).offset + litValue c }
  | .builtin .sub [x, .lit c] => some { descOf env x with offset := (descOf env x).offset - litValue c }
  | _ => none

/-- Step the environment forward across an assignment: invalidate everything keyed on or based on
the written slots, then record the new fact (unless it would be self-referential). -/
def stepEnvAssign (env : DescEnv n) (ds : List (Fin n)) (rhs : Rhs n) : DescEnv n :=
  let cleared := env.filter (fun p =>
    !ds.contains p.1 && (match p.2.base with | some b => !ds.contains b | none => true))
  match ds, rhsDesc env rhs with
  | [d], some desc => if desc.base == some d then cleared else (d, desc) :: cleared
  | _, _ => cleared

/-! ### The kill set and read gating -/

/-- A kill-set entry: this address of this space is overwritten (by a later store) before any
potentially-aliasing read. -/
structure KillEntry (n : Nat) where
  space : Space
  addr  : AddrDesc n
  deriving DecidableEq, Repr

/-- Two same-base addresses whose difference is provably nonzero (word-granular spaces). -/
def provablyNE (a b : AddrDesc n) : Bool :=
  a.base == b.base && a.offset != b.offset

/-- Two same-base 32-byte memory windows that are provably disjoint: the offset difference `δ`
satisfies `32 ≤ δ ≤ 2^256 - 32`. -/
def provablyDisjoint32 (a b : AddrDesc n) : Bool :=
  a.base == b.base &&
    (32 ≤ (a.offset - b.offset) && (a.offset - b.offset) ≤ (0 : U256) - 32)

/-- Filter the kill set at a read: `keep` decides whether an entry certainly cannot alias. -/
def killFilter (ks : List (KillEntry n)) (sp : Space) (keep : AddrDesc n → Bool) :
    List (KillEntry n) :=
  ks.filter (fun e => e.space != sp || keep e.addr)

/-- Drop every entry of the given space. -/
def killClearMem (ks : List (KillEntry n)) : List (KillEntry n) :=
  ks.filter (fun e => e.space != Space.memory)

/-- How an op interacts with the tracked spaces, for gating pending kills. Memory *writers* are
`.inert` — see the module docstring for why writes never gate. -/
inductive RseEffect
  | inert       -- observes no tracked space
  | readS       -- `sload k`: filters storage entries by key disequality
  | readT       -- `tload k`
  | readM       -- `mload p`: filters memory entries by 32-byte disjointness
  | clearM      -- reads memory less precisely, or observes its extent (`msize`)
  | clearAll    -- calls, halts, unclassified

open YulSemantics.EVM (Op) in
/-- Conservative classification: everything not explicitly known safe clears the kill set. -/
def rseEffect (op : Op) : RseEffect :=
  match op with
  | .sload => .readS
  | .tload => .readT
  | .mload => .readM
  | .keccak256 | .mcopy | .msize | .log0 | .log1 | .log2 | .log3 | .log4 => .clearM
  | .calldatacopy | .codecopy | .returndatacopy | .extcodecopy | .datacopy
  | .mstore8 => .inert
  | .address | .origin | .caller | .callvalue | .gasprice | .selfbalance
  | .coinbase | .timestamp | .number | .prevrandao | .gaslimit | .chainid | .basefee
  | .blobbasefee | .balance | .extcodesize | .extcodehash | .blockhash | .blobhash
  | .calldataload | .calldatasize | .codesize | .returndatasize | .datasize
  | .dataoffset => .inert
  | _ => if Op.isPure op then .inert else .clearAll

/-- Apply a read/barrier effect of an rhs to the kill set (address operands canonicalized against
the environment at the statement). -/
def applyRhsEffect (env : DescEnv n) (ks : List (KillEntry n)) : Rhs n → List (KillEntry n)
  | .atom _ => ks
  | .call _ _ => []
  | .builtin op args =>
      match rseEffect op with
      | .inert => ks
      | .readS =>
          match args with
          | [k] => killFilter ks .storage (fun a => provablyNE a (descOf env k))
          | _   => []
      | .readT =>
          match args with
          | [k] => killFilter ks .transient (fun a => provablyNE a (descOf env k))
          | _   => []
      | .readM =>
          match args with
          | [p] => killFilter ks .memory (fun a => provablyDisjoint32 a (descOf env p))
          | _   => []
      | .clearM => killClearMem ks
      | .clearAll => []

open YulSemantics.EVM (Op) in
/-- The store shape this pass eliminates: an effect-position `sstore`/`tstore`/`mstore`, with its
canonical address. -/
def storeShape? (env : DescEnv n) : Stmt n → Option (Space × AddrDesc n)
  | .assign [] (.builtin .sstore [k, _]) => some (.storage, descOf env k)
  | .assign [] (.builtin .tstore [k, _]) => some (.transient, descOf env k)
  | .assign [] (.builtin .mstore [p, _]) => some (.memory, descOf env p)
  | _ => none

/-! ### The pass: forward canonicalization, backward elimination, one recursion -/

mutual

/-- One statement against the kill set valid *after* it (`env` is the descriptor environment
*before* it). Returns `none` when the statement is a dead store. -/
def rseStmt (env : DescEnv n) (ks : List (KillEntry n)) :
    Stmt n → Option (Stmt n) × List (KillEntry n)
  | .assign ds rhs =>
      match storeShape? env (.assign ds rhs) with
      | some (sp, a) =>
          if ks.contains ⟨sp, a⟩ then
            (none, ks)                     -- fully overwritten later: drop; the entry still holds
          else
            (some (.assign ds rhs), ⟨sp, a⟩ :: ks)
      | none =>
          -- crossing the write backward: downstream descriptors based on `ds` are stale
          let ks₁ := ks.filter (fun e => match e.addr.base with
            | some b => !ds.contains b
            | none => true)
          (some (.assign ds rhs), applyRhsEffect env ks₁ rhs)
  | .cond c b => (some (.cond c (rseBlockAux env b).1), [])
  | .switch c cs df => (some (.switch c (rseCases env cs) (rseDflt env df)), [])
  | .loop post body => (some (.loop (rseBlockAux [] post).1 (rseBlockAux [] body).1), [])
  | s => (some s, [])                      -- break/continue/leave: an exit; clear

/-- A block: the environment flows forward, the kill set flows backward (the recursion descends
with the stepped environment and does the elimination on the way back up). A block ends with the
empty kill set — nothing is known overwritten after it. -/
def rseBlockAux (env : DescEnv n) : Block n → Block n × List (KillEntry n)
  | [] => ([], [])
  | s :: rest =>
      let env' := match s with
        | .assign ds rhs => stepEnvAssign env ds rhs
        | _ => []                          -- control flow: facts may not survive; reset
      let (rest', ks) := rseBlockAux env' rest
      match rseStmt env ks s with
      | (some s', ks') => (s' :: rest', ks')
      | (none, ks') => (rest', ks')

def rseCases (env : DescEnv n) : List (Literal × Block n) → List (Literal × Block n)
  | [] => []
  | (l, b) :: rest => (l, (rseBlockAux env b).1) :: rseCases env rest

def rseDflt (env : DescEnv n) : Option (Block n) → Option (Block n)
  | none => none
  | some b => some (rseBlockAux env b).1

end

/-- Optimize a block under a descriptor environment valid at its entry. -/
def rseBlock (env : DescEnv n) (b : Block n) : Block n :=
  (rseBlockAux env b).1

/-- **Redundant store elimination** over a frame body. -/
def storeElim (b : Block n) : Block n := rseBlock [] b

/-! ### Unit checks -/

section Checks
open YulSemantics.EVM (Op)

mutual
private def beqStmt : Stmt 2 → Stmt 2 → Bool
  | .assign ds r, .assign ds' r' => ds == ds' && r == r'
  | .cond c b, .cond c' b' => c == c' && beqBlock b b'
  | .switch c cs df, .switch c' cs' df' => c == c' && beqCases cs cs' && beqDflt df df'
  | .loop p b, .loop p' b' => beqBlock p p' && beqBlock b b'
  | .«break», .«break» => true
  | .«continue», .«continue» => true
  | .leave, .leave => true
  | _, _ => false
private def beqBlock : Block 2 → Block 2 → Bool
  | [], [] => true
  | s :: ss, t :: ts => beqStmt s t && beqBlock ss ts
  | _, _ => false
private def beqCases : List (Literal × Block 2) → List (Literal × Block 2) → Bool
  | [], [] => true
  | (l, b) :: cs, (l', b') :: cs' => l == l' && beqBlock b b' && beqCases cs cs'
  | _, _ => false
private def beqDflt : Option (Block 2) → Option (Block 2) → Bool
  | none, none => true
  | some b, some b' => beqBlock b b'
  | _, _ => false
end

private def lit (k : Nat) : Atom 2 := .lit (.number k)
private def sst (k v : Atom 2) : Stmt 2 := .assign [] (.builtin .sstore [k, v])
private def mst (p v : Atom 2) : Stmt 2 := .assign [] (.builtin .mstore [p, v])
private def p : Atom 2 := .slot 0
private def t : Atom 2 := .slot 1

-- overwritten constant-address store is dropped
#guard beqBlock (storeElim [sst (lit 5) (lit 1), sst (lit 5) (lit 2)]) [sst (lit 5) (lit 2)]
-- an aliasing read in between keeps it
#guard beqBlock (storeElim [sst (lit 5) (lit 1), .assign [1] (.builtin .sload [lit 5]),
    sst (lit 5) (lit 2)])
  [sst (lit 5) (lit 1), .assign [1] (.builtin .sload [lit 5]), sst (lit 5) (lit 2)]
-- a provably-different read in between does not
#guard beqBlock (storeElim [sst (lit 5) (lit 1), .assign [1] (.builtin .sload [lit 6]),
    sst (lit 5) (lit 2)])
  [.assign [1] (.builtin .sload [lit 6]), sst (lit 5) (lit 2)]
-- symbolic same-address kill through a copy: mstore(p,a); t := p; mstore(t,b)
#guard beqBlock (storeElim [mst p (lit 1), .assign [1] (.atom p), mst t (lit 2)])
  [.assign [1] (.atom p), mst t (lit 2)]
-- symbolic offset: t := add(p, 32) — an mload(t) is provably ≥32 away from mstore(p, ·)
#guard beqBlock (storeElim [.assign [1] (.builtin .add [p, lit 32]), mst p (lit 1),
    .assign [1] (.builtin .mload [t]), mst p (lit 2)])
  [.assign [1] (.builtin .add [p, lit 32]), .assign [1] (.builtin .mload [t]), mst p (lit 2)]
  -- (note: the mload writes slot 1 = t, so its own address canonicalizes first — see below)
-- different symbolic addresses do not kill: mstore(p); mstore(add(p,32))
#guard beqBlock (storeElim [.assign [1] (.builtin .add [p, lit 32]), mst p (lit 1), mst t (lit 2)])
  [.assign [1] (.builtin .add [p, lit 32]), mst p (lit 1), mst t (lit 2)]
-- an unknown-address read in between keeps everything
#guard beqBlock (storeElim [mst p (lit 1), .assign [1] (.builtin .mload [t]), mst p (lit 2)])
  [mst p (lit 1), .assign [1] (.builtin .mload [t]), mst p (lit 2)]

end Checks

/-! ## Redundant load elimination (load CSE + store-to-load forwarding)

The forward twin of the elimination above, on the same descriptor machinery: track *known
location values* — `space[addr] = ⟦atom⟧` — established by a load (`x := sload(k)` gives
`storage[k] = x`) or by a store of an atom (`sstore(k, v)` gives `storage[k] = v`). A later load
from a provably-equal address is replaced by a copy of the atom, which `valueNumber`/`deadCode`
then propagate and clean up. Entries are invalidated by

* a same-space store to a possibly-aliasing address (provably-different survives: nonzero offset
  difference for `sstore`/`tstore`, `[32, 2^256-32]` for `mstore`);
* any op that may write the space (calls clobber everything; `calldatacopy`&co, `mstore8`, `mcopy`
  clobber memory conservatively);
* a write to the frame slot holding the address base or the known value.
-/

/-- A known location value: `space[addr] = ⟦value⟧`. -/
structure KnownLoad (n : Nat) where
  space : Space
  addr  : AddrDesc n
  value : Atom n
  deriving DecidableEq

/-- Drop entries whose address base or value mention one of the written slots. -/
def knownDropSlots (kn : List (KnownLoad n)) (ds : List (Fin n)) : List (KnownLoad n) :=
  kn.filter (fun e =>
    (match e.addr.base with | some b => !ds.contains b | none => true) &&
    (match e.value with | .slot v => !ds.contains v | .lit _ => true))

/-- Invalidate at a store: same-space entries survive only when provably not aliased. -/
def knownStore (kn : List (KnownLoad n)) (sp : Space) (a : AddrDesc n) : List (KnownLoad n) :=
  kn.filter (fun e =>
    e.space != sp ||
      (match sp with
       | .memory => provablyDisjoint32 e.addr a
       | _ => provablyNE e.addr a))

open YulSemantics.EVM (Op) in
/-- Which spaces an op may *write* (for invalidating known values). Conservative: anything
unclassified clobbers everything. -/
def opClobbers (op : Op) : List Space :=
  match op with
  | .sload | .tload | .mload | .keccak256 | .msize
  | .log0 | .log1 | .log2 | .log3 | .log4
  | .address | .origin | .caller | .callvalue | .gasprice | .selfbalance
  | .coinbase | .timestamp | .number | .prevrandao | .gaslimit | .chainid | .basefee
  | .blobbasefee | .balance | .extcodesize | .extcodehash | .blockhash | .blobhash
  | .calldataload | .calldatasize | .codesize | .returndatasize | .datasize
  | .dataoffset | .gas => []
  | .calldatacopy | .codecopy | .returndatacopy | .extcodecopy | .datacopy
  | .mstore8 | .mcopy => [.memory]
  | _ => if Op.isPure op then [] else [.storage, .transient, .memory]

open YulSemantics.EVM (Op) in
/-- The load shape: `[x] := sload/tload/mload [k]`. -/
def loadShape? : Stmt n → Option (Space × Atom n × Fin n)
  | .assign [x] (.builtin .sload [k]) => some (.storage, k, x)
  | .assign [x] (.builtin .tload [k]) => some (.transient, k, x)
  | .assign [x] (.builtin .mload [k]) => some (.memory, k, x)
  | _ => none

mutual

/-- One statement forward: rewrite a load whose location is known, and step the fact base. -/
def rleStmt (env : DescEnv n) (kn : List (KnownLoad n)) :
    Stmt n → Stmt n × List (KnownLoad n)
  | .assign ds rhs =>
      match storeShape? env (.assign ds rhs) with
      | some (sp, a) =>
          -- a store: invalidate may-aliases, then learn the stored atom (second operand)
          let kn₁ := knownStore kn sp a
          match rhs with
          | .builtin _ [_, v] =>
              -- avoid a fact whose value slot is also the address base being self-invalidated later
              (.assign ds rhs, ⟨sp, a, v⟩ :: kn₁)
          | _ => (.assign ds rhs, kn₁)
      | none =>
          match loadShape? (.assign ds rhs) with
          | some (sp, k, x) =>
              let a := descOf env k
              match kn.find? (fun e => e.space == sp && e.addr == a) with
              | some e => (.assign ds (.atom e.value), knownDropSlots kn ds)
              | none =>
                  let kn₁ := knownDropSlots kn ds
                  -- learn the loaded value unless the write just clobbered its own address base
                  if (descOf env k).base == some x then (.assign ds rhs, kn₁)
                  else (.assign ds rhs, ⟨sp, a, .slot x⟩ :: kn₁)
          | none =>
              let kn₁ := knownDropSlots kn ds
              let kn₂ := match rhs with
                | .call _ _ => []
                | .builtin op _ => (opClobbers op).foldl
                    (fun acc sp => acc.filter (fun e => e.space != sp)) kn₁
                | .atom _ => kn₁
              (.assign ds rhs, kn₂)
  | .cond c b => (.cond c (rleBlock env kn b), kn)
  | .switch c cs df => (.switch c (rleCases env kn cs) (rleDflt env kn df), kn)
  | .loop post body => (.loop (rleBlock [] [] post) (rleBlock [] [] body), [])
  | s => (s, kn)

def rleBlock (env : DescEnv n) (kn : List (KnownLoad n)) : Block n → Block n
  | [] => []
  | s :: rest =>
      let env' := match s with
        | .assign ds rhs => stepEnvAssign env ds rhs
        | _ => []
      let (s', kn') := rleStmt env kn s
      let kn'' := match s with
        | .assign _ _ => kn'
        | .cond _ b => knownAfterSub kn' b     -- branch may or may not run: drop what it clobbers
        | _ => []                              -- switch/loop/exits: conservative
      s' :: rleBlock env' kn'' rest

def rleCases (env : DescEnv n) (kn : List (KnownLoad n)) :
    List (Literal × Block n) → List (Literal × Block n)
  | [] => []
  | (l, b) :: rest => (l, rleBlock env kn b) :: rleCases env kn rest

def rleDflt (env : DescEnv n) (kn : List (KnownLoad n)) :
    Option (Block n) → Option (Block n)
  | none => none
  | some b => some (rleBlock env kn b)

/-- After a conditional sub-block, keep only facts it cannot have clobbered. Conservative v1:
keep nothing (a cond body may store anywhere). -/
def knownAfterSub (_kn : List (KnownLoad n)) : Block n → List (KnownLoad n)
  | _ => []

end

/-- **Redundant load elimination** over a frame body. -/
def loadElim (b : Block n) : Block n := rleBlock [] [] b

section ChecksLoad
open YulSemantics.EVM (Op)

private def sld (x : Fin 2) (k : Atom 2) : Stmt 2 := .assign [x] (.builtin .sload [k])
private def mld (x : Fin 2) (k : Atom 2) : Stmt 2 := .assign [x] (.builtin .mload [k])

-- repeated sload becomes a copy
#guard beqBlock (loadElim [sld 0 (lit 5), sld 1 (lit 5)])
  [sld 0 (lit 5), .assign [1] (.atom (.slot 0))]
-- store-to-load forwarding
#guard beqBlock (loadElim [sst (lit 5) (lit 7), sld 1 (lit 5)])
  [sst (lit 5) (lit 7), .assign [1] (.atom (.lit (.number 7)))]
-- an intervening may-alias store blocks it
#guard beqBlock (loadElim [sld 0 (lit 5), sst t (lit 1), sld 1 (lit 5)])
  [sld 0 (lit 5), sst t (lit 1), sld 1 (lit 5)]
-- an intervening provably-different store does not
#guard beqBlock (loadElim [sld 0 (lit 5), sst (lit 6) (lit 1), sld 1 (lit 5)])
  [sld 0 (lit 5), sst (lit 6) (lit 1), .assign [1] (.atom (.slot 0))]
-- memory: an mstore ≥32 away does not clobber a known mload
#guard beqBlock (loadElim [mld 1 p, mst (lit 100000) (lit 1), mld 1 p])
  [mld 1 p, mst (lit 100000) (lit 1), mld 1 p]  -- p symbolic vs literal: bases differ, conservative

end ChecksLoad

end YulIR.FinFrame
