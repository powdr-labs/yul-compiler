set_option warningAsError true
/-!
# YulEvmCompiler.GasTx

**Monotone, unbounded gas transformers** — the currency of phase B's gas
bookkeeping.

A phase-B simulation statement guarantees two things about gas: a
*sufficiency threshold* (`bnd ≤ s.gasAvailable` — funded runs complete) and
a *residual lower bound* on the gas left afterwards, which is what lets
thresholds of later segments be discharged when segments compose. The
historical shape of the residual was additive, `s.gasAvailable - bnd ≤
s'.gasAvailable`, and `GasOracle.no_additive_bound_under_eip150` shows that
shape cannot express a gas-forwarding call: under EIP-150 the caller keeps
only about a 64th of what it had, a loss proportional to the unknown
starting gas.

This module generalizes the residual to `tx.f s.gasAvailable ≤
s'.gasAvailable` for a *transformer* `tx` that is

* **monotone** — more gas before never means less gas after, and
* **unbounded** — any demanded residual is reachable by starting with
  enough, which is exactly what makes a following segment's threshold
  dischargeable (`exists_threshold`).

The class is closed under composition, contains the additive case
(`GasTx.sub c` — so every existing phase-B arm embeds unchanged), and
contains the EIP-150 call shape (`GasTx.callLoss c`, `g ↦ (g - c) / 64`),
which is the piece a fused gas-forwarding call instruction needs.
-/

namespace YulEvmCompiler

/-- A monotone, unbounded lower-bound transformer on remaining gas: if the
machine holds `g` gas before a code segment, it holds at least `f g` after.
Monotonicity and unboundedness together let a downstream threshold be pushed
back through the segment (`exists_threshold`), which is all that sequential
composition of phase-B simulations consumes. -/
structure GasTx where
  /-- The residual bound: at least `f g` gas remains of a starting `g`. -/
  f : Nat → Nat
  /-- More gas before never means less gas after. -/
  mono : ∀ {g₁ g₂ : Nat}, g₁ ≤ g₂ → f g₁ ≤ f g₂
  /-- Any demanded residual is reachable from a large enough start. -/
  unbounded : ∀ m : Nat, ∃ g : Nat, m ≤ f g

namespace GasTx

/-- The additive transformer: lose at most `c` gas. This is the historical
phase-B shape; every local-op arm instantiates it. -/
def sub (c : Nat) : GasTx where
  f g := g - c
  mono h := Nat.sub_le_sub_right h c
  unbounded m := ⟨m + c, by omega⟩

@[simp] theorem sub_f (c g : Nat) : (sub c).f g = g - c := rfl

/-- The EIP-150 gas-forwarding call transformer: after committing at most `c`
gas to the call itself, the caller retains the reserved 64th of the rest —
the callee may spend everything it was handed. This is the residual a fused
`gas()`-forwarding call instruction produces, and the shape
`GasOracle.no_additive_bound_under_eip150` proves no `sub c` can cover. -/
def callLoss (c : Nat) : GasTx where
  f g := (g - c) / 64
  mono h := Nat.div_le_div_right (Nat.sub_le_sub_right h c)
  unbounded m := ⟨64 * m + c, by omega⟩

@[simp] theorem callLoss_f (c g : Nat) : (callLoss c).f g = (g - c) / 64 := rfl

/-- Composition: run the `t₁` segment first, then `t₂`. -/
def comp (t₂ t₁ : GasTx) : GasTx where
  f g := t₂.f (t₁.f g)
  mono h := t₂.mono (t₁.mono h)
  unbounded m :=
    have ⟨g₂, h₂⟩ := t₂.unbounded m
    have ⟨g₁, h₁⟩ := t₁.unbounded g₂
    ⟨g₁, Nat.le_trans h₂ (t₂.mono h₁)⟩

@[simp] theorem comp_f (t₂ t₁ : GasTx) (g : Nat) :
    (comp t₂ t₁).f g = t₂.f (t₁.f g) := rfl

/-- Push a downstream threshold back through a segment: a run funded with
`b` gas both meets the segment's own threshold `b₁` and leaves at least `b₂`
gas for what follows. This is the whole content of sequential composition in
phase B. -/
theorem exists_threshold (t₁ : GasTx) (b₁ b₂ : Nat) :
    ∃ b : Nat, b₁ ≤ b ∧ ∀ g, b ≤ g → b₂ ≤ t₁.f g := by
  obtain ⟨g₀, hg₀⟩ := t₁.unbounded b₂
  exact ⟨max b₁ g₀, Nat.le_max_left b₁ g₀,
    fun g hg => Nat.le_trans hg₀ (t₁.mono (Nat.le_trans (Nat.le_max_right b₁ g₀) hg))⟩

end GasTx

end YulEvmCompiler
