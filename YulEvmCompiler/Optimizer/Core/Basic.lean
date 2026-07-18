import YulSemantics.Dialect.EVM

set_option warningAsError true

/-!
# Optimizer Core IR: intrinsically scoped ANF expressions

This module is the first boundary of the optimizer Core IR.  It deliberately
starts with the expression fragment used by the local simplifier:

* values are literals or variables carrying membership in an explicit context;
* pure built-ins carry their input arity in the type; and
* built-in arguments are values, so nested/effectful expressions cannot be
  represented accidentally.

`ingest` is partial while the public optimizer pass remains total: the current
simplifier leaves syntax not represented by Core unchanged. `ingest_emit` is
the boundary theorem—successful ingestion erases to exactly the original Yul
expression. Later Core stages can extend this module without changing the
audited `Optimizer.Pass` contract or the backend proof.
-/

namespace YulEvmCompiler.Optimizer.Core

open YulSemantics
open YulSemantics.EVM

/-- Variables visible at a Core expression.  The first entry is innermost, as
in the source semantics' `VEnv`. -/
abbrev Ctx := List Ident

/-- A variable reference that cannot name something outside `Γ`. -/
structure Var (Γ : Ctx) where
  name : Ident
  bound : name ∈ Γ

/-- ANF values.  These are the only terms accepted as Core built-in arguments. -/
inductive Value (Γ : Ctx)
  | lit (literal : Literal)
  | var (ref : Var Γ)

/-- Arguments with their arity certified in the type. -/
structure Args (Γ : Ctx) (arity : Nat) where
  values : List (Value Γ)
  length_eq : values.length = arity

/-- State-independent EVM operations supported by the first Core fragment.
The index is the operation's input arity; every operation returns one word.
`exp` is intentionally absent because evaluating enormous literal exponents is
not a feasible optimizer operation. -/
inductive PureOp : Nat → Type
  | add : PureOp 2
  | sub : PureOp 2
  | mul : PureOp 2
  | div : PureOp 2
  | sdiv : PureOp 2
  | mod : PureOp 2
  | smod : PureOp 2
  | addmod : PureOp 3
  | mulmod : PureOp 3
  | signextend : PureOp 2
  | clz : PureOp 1
  | lt : PureOp 2
  | gt : PureOp 2
  | slt : PureOp 2
  | sgt : PureOp 2
  | eq : PureOp 2
  | iszero : PureOp 1
  | and : PureOp 2
  | or : PureOp 2
  | xor : PureOp 2
  | not : PureOp 1
  | byte : PureOp 2
  | shl : PureOp 2
  | shr : PureOp 2
  | sar : PureOp 2
  deriving Repr

/-- Forget a typed Core operation to the upstream Yul operation. -/
def PureOp.toOp : PureOp arity → Op
  | .add => .add
  | .sub => .sub
  | .mul => .mul
  | .div => .div
  | .sdiv => .sdiv
  | .mod => .mod
  | .smod => .smod
  | .addmod => .addmod
  | .mulmod => .mulmod
  | .signextend => .signextend
  | .clz => .clz
  | .lt => .lt
  | .gt => .gt
  | .slt => .slt
  | .sgt => .sgt
  | .eq => .eq
  | .iszero => .iszero
  | .and => .and
  | .or => .or
  | .xor => .xor
  | .not => .not
  | .byte => .byte
  | .shl => .shl
  | .shr => .shr
  | .sar => .sar

/-- Recognize a supported pure operation together with its arity index. -/
def PureOp.ofOp : Op → Option (Sigma PureOp)
  | .add => some ⟨2, .add⟩
  | .sub => some ⟨2, .sub⟩
  | .mul => some ⟨2, .mul⟩
  | .div => some ⟨2, .div⟩
  | .sdiv => some ⟨2, .sdiv⟩
  | .mod => some ⟨2, .mod⟩
  | .smod => some ⟨2, .smod⟩
  | .addmod => some ⟨3, .addmod⟩
  | .mulmod => some ⟨3, .mulmod⟩
  | .signextend => some ⟨2, .signextend⟩
  | .clz => some ⟨1, .clz⟩
  | .lt => some ⟨2, .lt⟩
  | .gt => some ⟨2, .gt⟩
  | .slt => some ⟨2, .slt⟩
  | .sgt => some ⟨2, .sgt⟩
  | .eq => some ⟨2, .eq⟩
  | .iszero => some ⟨1, .iszero⟩
  | .and => some ⟨2, .and⟩
  | .or => some ⟨2, .or⟩
  | .xor => some ⟨2, .xor⟩
  | .not => some ⟨1, .not⟩
  | .byte => some ⟨2, .byte⟩
  | .shl => some ⟨2, .shl⟩
  | .shr => some ⟨2, .shr⟩
  | .sar => some ⟨2, .sar⟩
  | _ => none

/-- The first Core expression fragment.  The output index is already present so
calls and multi-result expressions can be added without changing consumers. -/
inductive Term (Γ : Ctx) : Nat → Type
  | atom (value : Value Γ) : Term Γ 1
  | builtin {arity : Nat} (op : PureOp arity) (args : Args Γ arity) : Term Γ 1

/-- Erase a Core variable to its source name. -/
def Var.emit (ref : Var Γ) : Ident := ref.name

/-- Erase a Core value to Yul. -/
def Value.emit : Value Γ → YulSemantics.Expr Op
  | .lit literal => .lit literal
  | .var ref => .var ref.emit

/-- Erase certified arguments to their source order. -/
def Args.emit (args : Args Γ arity) : List (YulSemantics.Expr Op) :=
  args.values.map Value.emit

/-- Erase a Core expression to the existing Yul AST. -/
def Term.emit {Γ : Ctx} {outputs : Nat} (term : Term Γ outputs) : YulSemantics.Expr Op :=
  match term with
  | .atom value => value.emit
  | .builtin op args => .builtin op.toOp args.emit

/-- Ingest one ANF value, checking variable membership in `Γ`. -/
def ingestValue (Γ : Ctx) : YulSemantics.Expr Op → Option (Value Γ)
  | .lit literal => some (.lit literal)
  | .var name => if h : name ∈ Γ then some (.var ⟨name, h⟩) else none
  | _ => none

/-- Ingest a list of ANF values. -/
def ingestValues (Γ : Ctx) : List (YulSemantics.Expr Op) → Option (List (Value Γ))
  | [] => some []
  | value :: rest => do
      let value' ← ingestValue Γ value
      let rest' ← ingestValues Γ rest
      return value' :: rest'

/-- Ingest the supported expression fragment.  Calls, effectful operations,
nested arguments, unbound variables, and arity mismatches return `none`. -/
def ingest (Γ : Ctx) : YulSemantics.Expr Op → Option (Term Γ 1)
  | .lit literal => some (.atom (.lit literal))
  | .var name => do
      let value ← ingestValue Γ (.var name)
      return .atom value
  | .builtin op args => do
      let ⟨arity, pureOp⟩ ← PureOp.ofOp op
      let values ← ingestValues Γ args
      if h : values.length = arity then
        return .builtin pureOp ⟨values, h⟩
      else
        none
  | .call _ _ => none

/-- Successful value ingestion erases to the original syntax. -/
theorem ingestValue_emit {Γ : Ctx} {source : YulSemantics.Expr Op} {value : Value Γ}
    (h : ingestValue Γ source = some value) : value.emit = source := by
  cases source with
  | lit literal =>
      simp only [ingestValue, Option.some.injEq] at h
      subst value
      rfl
  | var name =>
      simp only [ingestValue] at h
      split at h
      · injection h with heq
        subst value
        rfl
      · contradiction
  | builtin op args => simp [ingestValue] at h
  | call fn args => simp [ingestValue] at h

/-- Successful argument ingestion erases to the original argument list. -/
theorem ingestValues_emit {Γ : Ctx} {source : List (YulSemantics.Expr Op)}
    {values : List (Value Γ)} (h : ingestValues Γ source = some values) :
    values.map Value.emit = source := by
  induction source generalizing values with
  | nil => simp [ingestValues] at h; subst values; rfl
  | cons value rest ih =>
      cases hvalue : ingestValue Γ value with
      | none => simp [ingestValues, hvalue] at h
      | some value' =>
          cases hrest : ingestValues Γ rest with
          | none => simp [ingestValues, hvalue, hrest] at h
          | some rest' =>
              simp [ingestValues, hvalue, hrest] at h
              subst values
              simp only [List.map_cons, List.cons.injEq]
              exact ⟨ingestValue_emit hvalue, ih hrest⟩

/-- Recognition remembers exactly which upstream operation was classified. -/
theorem PureOp.ofOp_toOp {op : Op} {packed : Sigma PureOp}
    (h : PureOp.ofOp op = some packed) : packed.2.toOp = op := by
  cases op <;> simp [PureOp.ofOp] at h <;> subst packed <;> rfl

/-- **Core boundary theorem.** Successful ingestion is a representation change
only: erasing the Core term gives exactly the input Yul expression. -/
theorem ingest_emit {Γ : Ctx} {source : YulSemantics.Expr Op} {core : Term Γ 1}
    (h : ingest Γ source = some core) : core.emit = source := by
  cases source with
  | lit literal =>
      simp [ingest, Term.emit] at h ⊢
      subst core
      rfl
  | var name =>
      cases hvalue : ingestValue Γ (.var name) with
      | none => simp [ingest, hvalue] at h
      | some value =>
          simp [ingest, hvalue] at h
          subst core
          exact ingestValue_emit hvalue
  | builtin op args =>
      cases hop : PureOp.ofOp op with
      | none => simp [ingest, hop] at h
      | some packed =>
          rcases packed with ⟨arity, pureOp⟩
          cases hvalues : ingestValues Γ args with
          | none => simp [ingest, hop, hvalues] at h
          | some values =>
              simp [ingest, hop, hvalues] at h
              obtain ⟨harity, hcore⟩ := h
              subst core
              simp only [Term.emit, Args.emit]
              rw [PureOp.ofOp_toOp hop, ingestValues_emit hvalues]
  | call fn args => simp [ingest] at h

/-- Collect the source names used by an expression.  `ingestSelf` uses this as
its initial certified context; statement-level Core ingestion will instead pass
the lexical context accumulated from declarations. -/
def sourceVars : YulSemantics.Expr Op → Ctx
  | .lit _ => []
  | .var name => [name]
  | .builtin _ args | .call _ args => args.flatMap sourceVars

/-- Try the first Core boundary without requiring a surrounding statement
context.  This is suitable for local rewrites that preserve every referenced
variable; dataflow passes use `ingest` with their actual lexical context. -/
def ingestSelf (source : YulSemantics.Expr Op) : Option (Term (sourceVars source) 1) :=
  ingest (sourceVars source) source

/-- Self-context ingestion has the same exact-erasure boundary theorem. -/
theorem ingestSelf_emit {source : YulSemantics.Expr Op}
    {core : Term (sourceVars source) 1} (h : ingestSelf source = some core) :
    core.emit = source :=
  ingest_emit h

/-! ### Boundary regression examples -/

/-- Correctly scoped, flat, arity-correct pure syntax enters Core. -/
example : (ingest ["x"] (.builtin .add [.var "x", .lit (.number 0)])).isSome = true := by
  simp [ingest, ingestValues, ingestValue, PureOp.ofOp]

/-- Wrong arity is rejected at ingestion rather than represented in Core. -/
example : ingest [] (.builtin .add [.lit (.number 1)]) = none := rfl

/-- Effectful operations remain outside Core and are left unchanged. -/
example : ingest [] (.builtin .sload [.lit (.number 0)]) = none := rfl

/-- Nested expressions are not ANF values and remain unchanged at this boundary
until the statement-level splitter is introduced. -/
example : ingest [] (.builtin .add
    [.builtin .add [.lit (.number 1), .lit (.number 2)], .lit (.number 3)]) = none := rfl

/-- User calls—including recursive calls—remain outside this first Core slice. -/
example : ingest [] (.call "f" []) = none := rfl

end YulEvmCompiler.Optimizer.Core
