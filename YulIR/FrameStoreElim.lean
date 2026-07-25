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

end YulIR.FinFrame
