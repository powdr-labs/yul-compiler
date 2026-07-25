import YulIR.FramePasses
import YulIR.FrameSimplifySound

set_option warningAsError true
/-!
# YulIR.FrameValueNumberSound — soundness of `valueNumber`

`valueNumber` is constant/copy propagation + common-subexpression elimination. Unlike the other
passes it carries an *environment* (`env : slot ↦ atom`, `avail : expr ↦ slot`), so its correctness
is a **store-relative** invariant threaded through the block simulation: the maps are only valid
against a particular store, and stay valid because the pass only ever records *immutable*
(written-at-most-once) slots whose defining write has already happened (read-after-write).

This file builds the groundwork — the environment-validity invariant and the fact that resolving
an rhs through a valid environment preserves its evaluation.
-/

namespace YulIR.FinFrame.Sem

open YulSemantics (Outcome BuiltinResult Literal Ident)
open YulSemantics.EVM (evm litValue)

/-! ### Environment validity -/

/-- The copy/constant environment is *valid* at a store when every mapping `i ↦ a` holds: the slot
`i` currently has the value the atom `a` denotes. -/
def EnvValid (σ : Store n) (env : List (Fin n × Atom n)) : Prop :=
  ∀ p ∈ env, σ p.1 = evalAtom σ p.2

/-- Resolving an atom through a valid environment preserves its value. -/
theorem resolveAtom_sound {σ : Store n} {env} (h : EnvValid σ env) (a : Atom n) :
    evalAtom σ (resolveAtom env a) = evalAtom σ a := by
  cases a with
  | lit l => rfl
  | slot i =>
      simp only [resolveAtom]
      cases hf : env.find? (fun p => p.1 == i) with
      | none => rfl
      | some p =>
          have hmem : p ∈ env := List.mem_of_find?_eq_some hf
          have hp := List.find?_some hf
          have hpi : p.1 = i := by simpa using hp
          show evalAtom σ p.2 = evalAtom σ (Atom.slot i)
          have : evalAtom σ (Atom.slot i) = σ i := rfl
          rw [this, ← hpi]; exact (h p hmem).symm

/-- Resolving all operands of a list preserves the evaluated value list. -/
theorem map_resolveAtom {σ : Store n} {env} (h : EnvValid σ env) (args : List (Atom n)) :
    (args.map (resolveAtom env)).map (evalAtom σ) = args.map (evalAtom σ) := by
  rw [List.map_map]
  exact List.map_congr_left (fun a _ => resolveAtom_sound h a)

/-- Resolving an rhs through a valid environment preserves its evaluation: it executes to exactly
the same results. -/
theorem resolveRhs_exec {funs : Funs} {σ : Store n} {env} (h : EnvValid σ env) {rhs : Rhs n}
    {st r} : ExecRhs funs σ st (resolveRhs env rhs) r ↔ ExecRhs funs σ st rhs r := by
  cases rhs with
  | atom a =>
      simp only [resolveRhs]
      constructor
      · intro hh; cases hh; rw [resolveAtom_sound h]; exact .atom
      · intro hh; cases hh; rw [← resolveAtom_sound h]; exact .atom
  | builtin op args =>
      simp only [resolveRhs]
      constructor
      · intro hh; cases hh with
        | builtin hb => rw [map_resolveAtom h] at hb; exact .builtin hb
      · intro hh; cases hh with
        | builtin hb => rw [← map_resolveAtom h] at hb; exact .builtin hb
  | call fn args =>
      simp only [resolveRhs]
      constructor
      · intro hh; cases hh with
        | callNorm hl hbody ho => rw [map_resolveAtom h] at hbody; exact .callNorm hl hbody ho
        | callHalt hl hbody => rw [map_resolveAtom h] at hbody; exact .callHalt hl hbody
      · intro hh; cases hh with
        | callNorm hl hbody ho => rw [← map_resolveAtom h] at hbody; exact .callNorm hl hbody ho
        | callHalt hl hbody => rw [← map_resolveAtom h] at hbody; exact .callHalt hl hbody

end YulIR.FinFrame.Sem
