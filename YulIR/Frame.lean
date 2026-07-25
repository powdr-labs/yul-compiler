import YulIR.Ast
import YulIR.Effects

set_option warningAsError true
/-!
# YulIR.Frame — the `Fin n`-frame IR (proof-oriented)

The intrinsically-scoped IR: variables are slot indices `Fin n` into a per-function *frame* of `n`
slots, so well-scopedness and uniqueness are **type guarantees** and the value environment is total.
`YulIR.FrameTranslate` gives `ofYul`/`toYul` (Yul ↔ frame, via the named IR), `YulIR.FrameSem` a
native executable semantics, and `YulIR.FramePasses` sample passes. Adequacy of `ofYul`/`toYul`
against the Yul semantics is deferred.

## The idea

Since the IR is now **block-free**, a scope is a *frame* of `n` local slots. So a variable is a slot
index `Fin n`, the count `n` is declared in the function/program header, and declaration and
assignment unify into a single `write` (all slots pre-declared, zero-initialised, as in Yul).

## The win

* **Well-scopedness + uniqueness are a type guarantee** — a `Stmt n` can only mention `Fin n` slots
  (an out-of-frame `.slot` is untypeable). Flatness collapses the nested `Var Γ` context to one `n`.
* **Removal is free** — DCE drops writes and leaves gaps; `n` is unchanged, no `Fin n` reference is
  renumbered (`deadWriteElim : Block n → Block n`).
* **Constant = written-once** (`isConstant`), enabled by unified writes.

## The cost

* **Growing the frame re-types the body** — `mapBlock (f : Fin n → Fin m)` reindexes every slot;
  `weakenBlock` (`+1`) and the inliner's frame merge (`+k`) pay this. Passes that only rewrite/remove
  (value numbering, structural, DCE) stay `Block n → Block n` and pay *nothing*; only frame-growing
  passes (inlining, LICM, rematerialisation) pay. That is the honest boundary of the friction.
-/

namespace YulIR.FinFrame

open YulSemantics (Ident Literal)

/-! ### Syntax over a frame of `n` slots -/

/-- An operand: a literal or an always-in-range slot reference. -/
inductive Atom (n : Nat)
  | lit  (l : Literal)
  | slot (i : Fin n)
  deriving DecidableEq, BEq

/-- A right-hand side. -/
inductive Rhs (n : Nat)
  | atom    (a : Atom n)
  | builtin (op : Op) (args : List (Atom n))
  | call    (fn : Ident) (args : List (Atom n))
  deriving DecidableEq, BEq

/-- A statement over an `n`-slot frame. No `block` (flat), no `funDef` (lifted), and **no separate
`let`** — `write` covers declaration and assignment alike. -/
inductive Stmt (n : Nat)
  | write     (dst : Fin n) (rhs : Rhs n)
  | writeMany (dsts : List (Fin n)) (rhs : Rhs n)
  | effect    (rhs : Rhs n)
  | cond      (c : Atom n) (body : List (Stmt n))
  | switch    (c : Atom n) (cases : List (Literal × List (Stmt n))) (dflt : Option (List (Stmt n)))
  | loop      (post body : List (Stmt n))
  | «break» | «continue» | leave

abbrev Block (n : Nat) := List (Stmt n)

instance : Inhabited (Atom n) := ⟨.lit (.number 0)⟩
instance : Inhabited (Rhs n)  := ⟨.atom default⟩
instance : Inhabited (Stmt n) := ⟨.«break»⟩

/-- A function over a frame of `nslots` slots; `params`/`rets` are the slots holding its parameters
and returns (kept as explicit slot lists so callers/inliners need no `Fin` arithmetic). -/
structure Function where
  nslots : Nat
  params : List (Fin nslots)
  rets   : List (Fin nslots)
  body   : Block nslots

/-- A program: a table of functions and a `main` frame. -/
structure Program where
  functions : Std.HashMap Ident Function
  mainSlots : Nat
  main      : Block mainSlots

/-! ### General slot remap (subsumes weakening) -/

/-- Remap an atom's slots through `f`. -/
def mapAtom (f : Fin n → Fin m) : Atom n → Atom m
  | .lit l  => .lit l
  | .slot i => .slot (f i)

/-- Remap an rhs's slots. -/
def mapRhs (f : Fin n → Fin m) : Rhs n → Rhs m
  | .atom a       => .atom (mapAtom f a)
  | .builtin op a => .builtin op (a.map (mapAtom f))
  | .call fn a    => .call fn (a.map (mapAtom f))

mutual
/-- Remap every slot of a statement through `f : Fin n → Fin m`. This is the one primitive behind
weakening (`f = Fin.castSucc`) and the inliner's frame merge (`f = Fin.natAdd`/`Fin.castAdd`). -/
partial def mapStmt (f : Fin n → Fin m) : Stmt n → Stmt m
  | .write d rhs      => .write (f d) (mapRhs f rhs)
  | .writeMany ds rhs => .writeMany (ds.map f) (mapRhs f rhs)
  | .effect rhs       => .effect (mapRhs f rhs)
  | .cond c b         => .cond (mapAtom f c) (mapBlock f b)
  | .switch c cs df   => .switch (mapAtom f c) (cs.map (fun p => (p.1, mapBlock f p.2))) (df.map (mapBlock f))
  | .loop post body   => .loop (mapBlock f post) (mapBlock f body)
  | .«break»          => .«break»
  | .«continue»       => .«continue»
  | .leave            => .leave
partial def mapBlock (f : Fin n → Fin m) : Block n → Block m
  | []      => []
  | s :: ss => mapStmt f s :: mapBlock f ss
end

/-- Weaken a block into a one-larger frame (the CSE/temp-introduction cost). -/
def weakenBlock : Block n → Block (n + 1) := mapBlock Fin.castSucc

/-- Allocate a fresh slot: enlarge the frame by one and return the new (last) slot. -/
def allocSlot (b : Block n) : Block (n + 1) × Fin (n + 1) := (weakenBlock b, Fin.last n)

/-! ### Removal keeps `n` — free DCE -/

/-- Purity of an rhs (reuses the dialect's `Op.isPure`). -/
def rhsPure : Rhs n → Bool
  | .atom _       => true
  | .builtin op _ => Op.isPure op
  | .call _ _     => false

mutual
/-- Drop pure writes to slots never read (`used`). The type `Block n → Block n` says it all: the
frame is untouched, so no slot is renumbered. -/
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

/-! ### Unified writes ⇒ constant = written-once -/

mutual
/-- Slots written anywhere in a block. -/
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

/-- A slot is constant (safe for value tracking) iff written at most once. Same soundness basis as
the named IR's "never reassigned": a once-written slot inside a loop is only *tracked* by value
numbering when its operands are themselves immutable, hence loop-invariant. -/
def isConstant (b : Block n) (i : Fin n) : Bool := (blockWrites b |>.count i) ≤ 1

/-! ### Type-guarantee demonstration -/

/-- Well-scoped by construction: `slot0 := add(slot1, 3)` over a 2-slot frame. -/
example : Stmt 2 := .write 0 (.builtin .add [.slot 1, .lit (.number 3)])

-- A type error (uncomment to see): `2` is not a `Fin 2`, so an out-of-frame slot is unrepresentable.
--   example : Stmt 2 := .write 0 (.atom (.slot 2))

end YulIR.FinFrame
