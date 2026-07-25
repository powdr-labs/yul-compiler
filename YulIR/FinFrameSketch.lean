import YulIR.Ast
import YulIR.Effects

set_option warningAsError true
/-!
# YulIR.FinFrameSketch — a design sketch of the `Fin n`-frame IR

**Not wired into the pipeline.** This is a self-contained sketch to make the ergonomics of the
"numbered local frame" representation concrete (see the discussion in `DESIGN.md`), so we can weigh
it before committing.

## The idea

Because the IR is now **block-free** (one flat statement sequence per function / `main`), a scope is
just a *frame* of `n` local slots. So represent a variable as a slot index `Fin n`, declare the
count `n` in the function/program header, and **unify declaration and assignment** into a single
`write` (all slots are pre-declared by the header, zero-initialised as in Yul).

## What the types buy (the win)

* **Well-scopedness + uniqueness are a type guarantee.** A `Stmt n` can only mention `Fin n`
  slots, so a reference can neither dangle nor collide — the invariant we currently *maintain* in
  `ofYul` becomes *unrepresentable to violate*. Flatness is what makes this cheap: the nested
  `Var Γ` context collapses to a single `n`. (See the `example`s at the end — `.slot 2` in a
  `Stmt 2` is a type error.)
* **Removal is free.** Dead-code elimination drops writes and *leaves a gap*; `n` is unchanged, so
  every remaining `Fin n` reference stays valid with **no renumbering** — `deadWriteElim : Block n →
  Block n`. This is the property de Bruijn indices/levels lack.
* **Constant analysis is a write-count.** With `let`/`assign` unified, "slot `i` is constant" is
  just "written ≤ once" (`isConstant`) — one scan, no `let`-vs-`assign` bookkeeping.

## What it costs (the honest downside)

* **Adding a slot re-types the body.** Introducing a temporary (CSE) goes `Block n → Block (n+1)`,
  which requires weakening every `Fin n` to `Fin (n+1)` — `weakenBlock` below. That's the
  intrinsic-typing tax; it is exactly the plumbing an extrinsic `Nat`-slot (≈ integer unique names)
  would avoid, at the price of losing the type guarantee.
* **Inlining renumbers** the callee's slots into the caller's frame (same cost as fresh-naming).

## Bridge

Erasure to the existing named IR maps slot `i` to the name `_s<i>`, `write` to `assign`, with a
preamble of zero-init `let`s for the local slots (params/rets come from the signature). Shown by
`eraseBlock` below; a full `eraseFunction` prepends the preamble.
-/

namespace YulIR.FinFrame

open YulSemantics (Ident Literal)

/-! ### Syntax over a frame of `n` slots -/

/-- An operand: a literal or a slot reference (`Fin n` ⇒ always in range). -/
inductive Atom (n : Nat)
  | lit  (l : Literal)
  | slot (i : Fin n)

/-- A right-hand side. -/
inductive Rhs (n : Nat)
  | atom    (a : Atom n)
  | builtin (op : Op) (args : List (Atom n))
  | call    (fn : Ident) (args : List (Atom n))

/-- A statement over an `n`-slot frame. No `block` (flat), no `funDef` (lifted), and **no separate
`let`** — a `write` covers both declaration and assignment. -/
inductive Stmt (n : Nat)
  /-- `slot dst := rhs` (single result; declaration *and* reassignment). -/
  | write     (dst : Fin n) (rhs : Rhs n)
  /-- `slot d₀, d₁, … := call(…)` (multi-result). -/
  | writeMany (dsts : List (Fin n)) (rhs : Rhs n)
  /-- an effectful rhs evaluated for its effect. -/
  | effect    (rhs : Rhs n)
  | cond      (c : Atom n) (body : List (Stmt n))
  | switch    (c : Atom n) (cases : List (Literal × List (Stmt n))) (dflt : Option (List (Stmt n)))
  | loop      (post body : List (Stmt n))
  | «break» | «continue» | leave

/-- A block is a flat statement sequence over the frame. -/
abbrev Block (n : Nat) := List (Stmt n)

instance : Inhabited (Atom n) := ⟨.lit (.number 0)⟩
instance : Inhabited (Rhs n)  := ⟨.atom default⟩
instance : Inhabited (Stmt n) := ⟨.«break»⟩

/-- A function: a frame of `nslots` slots, of which the first `nparams` are parameters and the next
`nrets` are returns (the rest are locals). -/
structure Function where
  nslots  : Nat
  nparams : Nat
  nrets   : Nat
  body    : Block nslots

/-- A program: a table of functions (keyed by name) and a `main` frame. -/
structure Program where
  functions : Std.HashMap Ident Function
  mainSlots : Nat
  main      : Block mainSlots

/-! ### The win #1 — removal keeps `n` (free DCE, no renumbering) -/

/-- Purity of an rhs (reuses the dialect's `Op.isPure`). -/
def rhsPure : Rhs n → Bool
  | .atom _       => true
  | .builtin op _ => Op.isPure op
  | .call _ _     => false

mutual
/-- Drop pure writes to slots that are never read (`used`). Note the type: `Block n → Block n` —
the frame size is untouched, so *no* `Fin n` reference is renumbered. -/
partial def deadWriteElim (used : List (Fin n)) : Block n → Block n
  | []      => []
  | s :: ss =>
    match s with
    | .write d rhs =>
        if rhsPure rhs && ! used.contains d then deadWriteElim used ss
        else .write d rhs :: deadWriteElim used ss
    | .cond c b       => .cond c (deadWriteElim used b) :: deadWriteElim used ss
    | .switch c cs df =>
        .switch c (cs.map (fun p => (p.1, deadWriteElim used p.2))) (df.map (deadWriteElim used))
          :: deadWriteElim used ss
    | .loop post body => .loop (deadWriteElim used post) (deadWriteElim used body) :: deadWriteElim used ss
    | other           => other :: deadWriteElim used ss
end

/-! ### The win #2 — unified writes ⇒ constant = written-once -/

mutual
/-- All slots written anywhere in a block. -/
partial def blockWrites : Block n → List (Fin n)
  | []      => []
  | s :: ss => stmtWrites s ++ blockWrites ss
/-- Slots written by a statement. -/
partial def stmtWrites : Stmt n → List (Fin n)
  | .write d _      => [d]
  | .writeMany ds _ => ds
  | .cond _ b       => blockWrites b
  | .switch _ cs df => cs.flatMap (fun p => blockWrites p.2) ++ (df.map blockWrites).getD []
  | .loop post body => blockWrites post ++ blockWrites body
  | _               => []
end

/-- A slot is constant iff it is written at most once. -/
def isConstant (b : Block n) (i : Fin n) : Bool := (blockWrites b |>.count i) ≤ 1

/-! ### The cost — adding a slot re-types the body (weakening) -/

/-- Weaken an atom into a one-larger frame. -/
def weakenAtom : Atom n → Atom (n + 1)
  | .lit l  => .lit l
  | .slot i => .slot i.castSucc

/-- Weaken an rhs. -/
def weakenRhs : Rhs n → Rhs (n + 1)
  | .atom a       => .atom (weakenAtom a)
  | .builtin op a => .builtin op (a.map weakenAtom)
  | .call fn a    => .call fn (a.map weakenAtom)

mutual
/-- Weaken a statement into a one-larger frame — every `Fin n` slot becomes `Fin (n+1)`. This is
the plumbing an extrinsic integer-slot representation would not need (it is the price of the type
guarantee). -/
partial def weakenStmt : Stmt n → Stmt (n + 1)
  | .write d rhs     => .write d.castSucc (weakenRhs rhs)
  | .writeMany ds rhs => .writeMany (ds.map Fin.castSucc) (weakenRhs rhs)
  | .effect rhs      => .effect (weakenRhs rhs)
  | .cond c b        => .cond (weakenAtom c) (weakenBlock b)
  | .switch c cs df  => .switch (weakenAtom c) (cs.map (fun p => (p.1, weakenBlock p.2))) (df.map weakenBlock)
  | .loop post body  => .loop (weakenBlock post) (weakenBlock body)
  | .«break»         => .«break»
  | .«continue»      => .«continue»
  | .leave           => .leave
partial def weakenBlock : Block n → Block (n + 1)
  | []      => []
  | s :: ss => weakenStmt s :: weakenBlock ss
end

/-- Allocate a fresh slot in a block, returning the enlarged block and the new slot index. This is
what CSE/temp-introduction costs: a `weakenBlock` plus `Fin.last`. -/
def allocSlot (b : Block n) : Block (n + 1) × Fin (n + 1) := (weakenBlock b, Fin.last n)

/-! ### Bridge — erase to the existing named IR -/

/-- The Yul/named-IR name for slot `i`. -/
def slotName (i : Fin n) : Ident := s!"_s{i.val}"

/-- Erase an atom to the named IR. -/
def eraseAtom : Atom n → YulIR.Atom
  | .lit l  => .lit l
  | .slot i => .var (slotName i)

/-- Erase an rhs. -/
def eraseRhs : Rhs n → YulIR.Rhs
  | .atom a       => .atom (eraseAtom a)
  | .builtin op a => .builtin op (a.map eraseAtom)
  | .call fn a    => .call fn (a.map eraseAtom)

mutual
/-- Erase a statement: a `write` becomes an `assign` (slots are pre-declared by the frame preamble;
see `eraseFunction`'s note in the module doc). -/
partial def eraseStmt : Stmt n → YulIR.Stmt
  | .write d rhs      => .assign [slotName d] (eraseRhs rhs)
  | .writeMany ds rhs => .assign (ds.map slotName) (eraseRhs rhs)
  | .effect rhs       => .effect (eraseRhs rhs)
  | .cond c b         => .cond (eraseAtom c) (eraseBlock b)
  | .switch c cs df   => .switch (eraseAtom c) (cs.map (fun p => (p.1, eraseBlock p.2))) (df.map eraseBlock)
  | .loop post body   => .loop (eraseBlock post) (eraseBlock body)
  | .«break»          => .«break»
  | .«continue»       => .«continue»
  | .leave            => .leave
partial def eraseBlock : Block n → YulIR.Block
  | []      => []
  | s :: ss => eraseStmt s :: eraseBlock ss
end

/-! ### Type-guarantee demonstration -/

/-- A well-scoped statement over a 2-slot frame: `slot0 := add(slot1, 3)`. -/
example : Stmt 2 := .write 0 (.builtin .add [.slot 1, .lit (.number 3)])

-- The scoping/uniqueness guarantee at work: the following is a *type error*, because `2` is not a
-- `Fin 2` — an out-of-frame slot reference is unrepresentable.
--   example : Stmt 2 := .write 0 (.atom (.slot 2))

end YulIR.FinFrame
