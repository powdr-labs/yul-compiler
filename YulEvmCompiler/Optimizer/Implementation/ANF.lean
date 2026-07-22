import YulSemantics.Dialect.EVM
/-!
# ANF / expression-splitting normalizer — structural core

A shared normalization for the optimizer: rewrite Yul so **every operand is an
atom** (a variable or literal), by binding each nested sub-expression to a fresh
`let`. E.g. `sstore(add(x, 1), mul(y, 2))` becomes

```text
let t0 := add(x, 1)
let t1 := mul(y, 2)
sstore(t0, t1)
```

This is the front-end normal form the `Optimizer.Core` expression IR already
assumes (`Core.ingest` accepts exactly an atom or one operator applied to
atoms), so ANF maximizes the fragment `Simplify`/inlining can act on, and it
turns store/load reasoning into a variable-level analysis for the dataflow
passes.

This file is the **structural** core: the expression flattener `flatten` and a
machine-checked proof that its output really is in ANF — every emitted argument
is an atom, and every prelude statement is a single-variable `let` whose
right-hand side applies one operator to atoms (the `preludeOK` shape). The
statement/block wrapper and the *semantic* (`EquivBlock`)-preservation proof —
which must also get Yul's right-to-left argument evaluation order and fresh-name
non-capture right — are the following steps; `flatten` already fixes the binding
order to match evaluation so that proof is available.

Freshness follows `FreshenCalls`: temporaries share a prefix `P` chosen so no
program identifier starts with it, so distinct indices give distinct,
capture-free names with no counter threaded through the eventual proof.
-/

namespace YulEvmCompiler.Optimizer.ANF

open YulSemantics YulSemantics.EVM

/-! ### The ANF shape predicates -/

/-- An **atom**: a variable or a literal — a leaf operand with no sub-expression
to split. (Forwarding separately restricts to `stringFree` values; ANF only
cares that operands are leaves.) -/
def isAtom : Expr Op → Bool
  | .var _ => true
  | .lit _ => true
  | _ => false

/-- Every element of an argument list is an atom. -/
def atomicArgs : List (Expr Op) → Bool
  | [] => true
  | e :: rest => isAtom e && atomicArgs rest

/-- A right-hand side allowed at the head of an ANF `let`: an atom, or a single
operator/`call` applied to atoms (no further nesting). -/
def isFlatRhs : Expr Op → Bool
  | .builtin _ args => atomicArgs args
  | .call _ args => atomicArgs args
  | e => isAtom e

/-- A well-formed prelude statement: `let t := rhs` binding exactly one variable
to a flat right-hand side. -/
def preludeOK : Stmt Op → Bool
  | .letDecl [_] (some rhs) => isFlatRhs rhs
  | _ => false

/-! ### Fresh temporaries -/

/-- The `k`-th temporary under prefix `P`. Distinct `k` give distinct names, and
none is a program identifier when `P` is prefix-fresh. -/
def tempName (P : String) (k : Nat) : Ident := P ++ "t" ++ toString k

/-! ### The flattener

`flatten P k e = (k', prelude, atom)`: `prelude` is a list of ANF `let`s that
must run before the result, and `atom` is the atom denoting `e`'s value. `k`
is the next-free temporary index, threaded left-to-right through the recursion;
arguments are flattened **right-to-left** (Yul's evaluation order) and their
preludes concatenated in that order, so the eventual semantic proof sees effects
in the original order. -/
mutual
def flatten (P : String) (k : Nat) : Expr Op → Nat × List (Stmt Op) × Expr Op
  | .var x => (k, [], .var x)
  | .lit l => (k, [], .lit l)
  | .builtin op args =>
      let (k1, pre, atoms) := flattenArgs P k args
      let t := tempName P k1
      (k1 + 1, pre ++ [.letDecl [t] (some (.builtin op atoms))], .var t)
  | .call f args =>
      let (k1, pre, atoms) := flattenArgs P k args
      let t := tempName P k1
      (k1 + 1, pre ++ [.letDecl [t] (some (.call f atoms))], .var t)

/-- Flatten an argument list right-to-left, returning the accumulated prelude
(in evaluation order) and the list of atoms in source order. -/
def flattenArgs (P : String) (k : Nat) : List (Expr Op) → Nat × List (Stmt Op) × List (Expr Op)
  | [] => (k, [], [])
  | e :: rest =>
      -- evaluate `rest` (to the right) first, then `e`
      let (k1, preRest, atomsRest) := flattenArgs P k rest
      let (k2, preHead, atomHead) := flatten P k1 e
      (k2, preRest ++ preHead, atomHead :: atomsRest)
end

/-! ### Structural correctness: the output is in ANF -/

mutual
/-- The result of `flatten` is an atom, and its prelude is all well-formed ANF
`let`s. -/
theorem flatten_ok (P : String) (k : Nat) (e : Expr Op) :
    isAtom (flatten P k e).2.2 = true ∧
      ∀ s ∈ (flatten P k e).2.1, preludeOK s = true := by
  match e with
  | .var x => exact ⟨rfl, by intro s hs; simp [flatten] at hs⟩
  | .lit l => exact ⟨rfl, by intro s hs; simp [flatten] at hs⟩
  | .builtin op args =>
      refine ⟨rfl, ?_⟩
      intro st hst
      simp only [flatten] at hst
      rcases List.mem_append.mp hst with hpre | htail
      · exact (flattenArgs_ok P k args).2 st hpre
      · rcases List.mem_singleton.mp htail with rfl
        simp only [preludeOK, isFlatRhs]
        exact (flattenArgs_ok P k args).1
  | .call f args =>
      refine ⟨rfl, ?_⟩
      intro st hst
      simp only [flatten] at hst
      rcases List.mem_append.mp hst with hpre | htail
      · exact (flattenArgs_ok P k args).2 st hpre
      · rcases List.mem_singleton.mp htail with rfl
        simp only [preludeOK, isFlatRhs]
        exact (flattenArgs_ok P k args).1

/-- The result atoms of `flattenArgs` are all atoms, and its prelude is
well-formed. -/
theorem flattenArgs_ok (P : String) (k : Nat) (args : List (Expr Op)) :
    atomicArgs (flattenArgs P k args).2.2 = true ∧
      ∀ s ∈ (flattenArgs P k args).2.1, preludeOK s = true := by
  match args with
  | [] => exact ⟨rfl, by intro s hs; simp [flattenArgs] at hs⟩
  | e :: rest =>
      have hrest := flattenArgs_ok P k rest
      have hhead := flatten_ok P (flattenArgs P k rest).1 e
      refine ⟨?_, ?_⟩
      · simp only [flattenArgs, atomicArgs, Bool.and_eq_true]
        exact ⟨hhead.1, hrest.1⟩
      · intro st hst
        simp only [flattenArgs] at hst
        rcases List.mem_append.mp hst with hpre | hpre
        · exact hrest.2 st hpre
        · exact hhead.2 st hpre
end

end YulEvmCompiler.Optimizer.ANF
