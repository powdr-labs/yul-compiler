import YulEvmCompiler.Optimizer.Implementation.RedundantStore.Domain
/-!
# Redundant-store elimination — M2 (core): load-forwarding to a variable/literal

The reusable heart of the forwarding transfer: replacing a load `sload(k)` by a
value the abstract store already knows is in slot `k`.

## Why the forwarded value is a variable/literal (see `RedundantStores.md` §IR)

On an ANF-normalized program every operand is a variable or literal, so the
value stored at a slot is *already materialized in a variable*. Forwarding
`sload(k) ⟶ let y := x` is then a variable reference: (1) trivially pure — no
re-evaluation, nothing to halt or read — so it is sound without any purity
side-proof; and (2) unconditionally profitable — an expensive `SLOAD` becomes a
`DUP`, and we never risk re-emitting an expensive expression (`keccak`, big
`mulmod`) the way "forward the value expression" would. So the abstract store
holds value-shaped atoms, by design, not as a restriction.

Keys here are literal slots; variable-slot forwarding (matched by value-numbering
on the ANF key variables) is the next step and reuses this same lemma shape.
-/

namespace YulEvmCompiler.Optimizer.RedundantStore

open YulSemantics YulSemantics.EVM
open YulEvmCompiler.Optimizer.Core

variable {calls : ExternalCalls} {creates : ExternalCreates}
local notation "D" => evmWithExternal calls creates

/-! ### `sload` on a literal slot: exact evaluation -/

/-- Evaluating a single literal argument. -/
theorem litArg_eval (n : Nat) {funs : FunEnv D} {V : VEnv D} {st : EvmState} :
    Step D funs V st (.args [.lit (.number n)]) (.eres (.vals [litValue (.number n)] st)) :=
  Step.argsCons Step.argsNil Step.lit

/-- Inversion for a single literal argument. -/
theorem litArg_inv (n : Nat) {funs : FunEnv D} {V : VEnv D} {st : EvmState} {r}
    (h : Step D funs V st (.args [.lit (.number n)]) (.eres r)) :
    r = .vals [litValue (.number n)] st := by
  cases h with
  | argsCons hrest hhead => cases hhead with
    | lit => cases hrest with | argsNil => rfl
  | argsRestHalt hrest => cases hrest
  | argsHeadHalt hrest hhead => cases hhead

/-- `stepOp .sload [k]` reads the current slot without changing state. -/
theorem stepOp_sload (k : U256) (st : EvmState) :
    stepOp .sload [k] st = some (.ok [st.storage k] st) := rfl

theorem builtin_sload_iff (k : U256) (st : EvmState) (r) :
    (D).Builtin .sload [k] st r ↔ stepOp .sload [k] st = some r := Iff.rfl

/-- **Exact evaluation of `sload` on a literal slot**: it yields the current
storage word and leaves the state untouched, and nothing else. -/
theorem sload_lit_eval (n : Nat) {funs : FunEnv D} {V : VEnv D} {st : EvmState} {r} :
    Step D funs V st (.expr (.builtin .sload [.lit (.number n)])) (.eres r)
    ↔ r = .vals [st.storage (litValue (.number n))] st := by
  constructor
  · intro h
    cases h with
    | builtinOk hargs hb =>
        have hi := litArg_inv n hargs; injection hi with hvals hst
        rw [hvals, hst, builtin_sload_iff, stepOp_sload] at hb
        simp only [Option.some.injEq, BuiltinResult.ok.injEq] at hb
        obtain ⟨hrets, hst2⟩ := hb; subst hrets; subst hst2; rfl
    | builtinHalt hargs hb =>
        have hi := litArg_inv n hargs; injection hi with hvals hst
        rw [hvals, hst, builtin_sload_iff, stepOp_sload] at hb
        simp at hb
    | builtinArgsHalt hargs => exact absurd (litArg_inv n hargs) (by simp)
  · rintro rfl
    exact Step.builtinOk (litArg_eval n) (by rw [builtin_sload_iff, stepOp_sload])

/-! ### Forwarding a literal-slot load to a value-shaped stored value -/

/-- **Load-forwarding soundness.** If the abstract store records that literal
slot `n` holds the value-shaped atom `a`, then reading the slot and evaluating
`a` are interchangeable expressions — in both directions, with the same result.
This is the equivalence the statement simulation splices in at a forwarded
`let x := sload(n)` ⟶ `let x := a`, deleting the `SLOAD`. -/
theorem forward_atom_sound {Γ : Ctx} {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    {σ : Avail Γ} (h : Valid funs V st storageRead σ)
    {n : Nat} {a : Value Γ} (hmem : (⟨.lit (.number n), .atom a⟩ : Fact Γ) ∈ σ)
    (hsf : a.stringFree = true) {r} :
    Step D funs V st (.expr (.builtin .sload [.lit (.number n)])) (.eres r)
    ↔ Step D funs V st (.expr (Value.emit a)) (.eres r) := by
  obtain ⟨kw, hkey, hvaleval⟩ := h _ hmem
  have hkw : kw = litValue (.number n) := by cases hkey with | lit => rfl
  subst hkw
  have hisv : isValueExpr (Value.emit a) = true := emit_isValue hsf
  -- `Term.emit (.atom a)` is definitionally `Value.emit a`, and `storageRead st`
  -- is `st.storage`; restate the fact's guarantee in that normal form.
  have hv : Step D funs V st (.expr (Value.emit a))
      (.eres (.vals [st.storage (litValue (.number n))] st)) := hvaleval
  rw [valueEval_eval_iff (calls := calls) (creates := creates) hisv] at hv
  obtain ⟨w, hw, hres⟩ := hv
  injection hres with hvals _; injection hvals with hval
  rw [sload_lit_eval, valueEval_eval_iff (calls := calls) (creates := creates) hisv]
  constructor
  · rintro rfl; exact ⟨w, hw, by rw [hval]⟩
  · rintro ⟨w', hw', rfl⟩
    rw [hw] at hw'; injection hw' with hww; rw [hval, hww]

end YulEvmCompiler.Optimizer.RedundantStore
