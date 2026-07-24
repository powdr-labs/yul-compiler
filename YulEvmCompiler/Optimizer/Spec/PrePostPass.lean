import YulEvmCompiler.Optimizer.Spec.GlobalPass

set_option warningAsError true

/-!
# YulEvmCompiler.Optimizer.Spec.PrePostPass

A small **invariant-preservation / soundness-precondition** framework for optimizer
passes, layered on top of the `LocalPass`/`GlobalPass` specifications.

## The "preserve, don't require" philosophy

The core `LocalPass` obligation (`Sound`) is *unconditional*: a pass must be
semantics-preserving on **every** input. That is the right default — most rewrites
are unconditionally sound — but two finer distinctions are worth naming explicitly,
and this module names them as **three orthogonal, composable notions** rather than
bundling them into one structure:

1. **Soundness may need a precondition, not a normal form.** A pass should require
   only what it needs *for soundness* (`SoundUnder pre`), never what it merely needs
   *for efficiency*. For the overwhelmingly common case `pre = fun _ => True` this
   collapses back to the unconditional `Sound` (`soundUnder_true_iff`).

2. **Normal forms are PRESERVED, not REQUIRED.** A structural invariant `I`
   (e.g. unique variable names, a canonical statement order) is modelled as
   something a pass **preserves** (`Preserves I`: `I b → I (run b)`) — *not*
   something it demands as a precondition for correctness. This is the key
   discipline: an ordinary optimizer that happens to keep `I` intact must not be
   allowed to become *unsound* on inputs violating `I`. Preservation is a separate,
   weaker promise than requirement.

3. **A dedicated pass ESTABLISHES the invariant.** The obligation of *reaching* a
   normal form is concentrated in one normalization pass (`Establishes pre I`:
   `pre b → I (run b)`). Downstream, an establisher followed by any number of
   preservers still establishes `I` (`Establishes.comp_preserves`), so a pipeline
   normalizes once and then relies on every later pass to keep the invariant.

The payoff is compositional: `SoundUnder`, `Preserves`, and `Establishes` each carry
`comp`/`ofList` lemmas, and they interlock (a `Preserves`-witness for the
precondition is exactly what lets two `SoundUnder pre` passes compose). The concrete
soundness currency is unchanged — everything reduces to `EquivBlock` (local tier)
and `RunEquivBlock` (global tier).
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics

variable {D : Dialect} [DecidableEq D.Value]

/-! ## Invariant preservation (`Preserves`)

An invariant `I` is a predicate on programs. A transform `Preserves I` when it maps
`I`-programs to `I`-programs — it is *not* required to be sound only on `I`, and it
is *not* required to establish `I`. This is the "preserve, don't require" promise. -/

/-- A transform **preserves** the invariant `I` when it maps every `I`-satisfying
block to an `I`-satisfying block. This is strictly weaker than *requiring* `I` (which
would be a soundness precondition) or *establishing* `I` (`Establishes`): an ordinary
optimizer preserves normal-form invariants without depending on them for
correctness. -/
def Preserves (I : Block D.Op → Prop) (run : Block D.Op → Block D.Op) : Prop :=
  ∀ b, I b → I (run b)

omit [DecidableEq D.Value] in
/-- The do-nothing transform preserves every invariant. -/
theorem Preserves.id {I : Block D.Op → Prop} : Preserves I _root_.id :=
  fun _ hb => hb

omit [DecidableEq D.Value] in
/-- Preservation composes: if `run₁` and `run₂` both preserve `I`, so does
`run₁ ∘ run₂` (which runs `run₂` first, then `run₁` — matching `LocalPass.comp`). -/
theorem Preserves.comp {I : Block D.Op → Prop} {run₁ run₂ : Block D.Op → Block D.Op}
    (h₁ : Preserves I run₁) (h₂ : Preserves I run₂) : Preserves I (run₁ ∘ run₂) :=
  fun b hb => h₁ (run₂ b) (h₂ b hb)

omit [DecidableEq D.Value] in
/-- A whole pipeline preserves `I` when each stage does. The list is folded exactly
as `LocalPass.ofList` folds passes — `rs.foldr (fun r acc => acc ∘ r) id`, so the
head transform runs first — hence this lemma applies to the underlying `run`
functions of a `LocalPass.ofList` pipeline. -/
theorem Preserves.ofList {I : Block D.Op → Prop} {rs : List (Block D.Op → Block D.Op)}
    (h : ∀ r ∈ rs, Preserves I r) :
    Preserves I (rs.foldr (fun r acc => acc ∘ r) _root_.id) := by
  induction rs with
  | nil => exact Preserves.id
  | cons r rs ih =>
      exact (ih fun r' hr' => h r' (List.mem_cons.2 (Or.inr hr'))).comp
        (h r (List.mem_cons.2 (Or.inl rfl)))

/-! ## Conditional soundness (`SoundUnder`)

A pass carries a precondition `pre` capturing *exactly what it needs to be sound*.
`SoundUnder (fun _ => True)` recovers the unconditional `Sound`. -/

/-- A transform is **sound under the precondition `pre`** when its output is
semantically equivalent to its input on every program satisfying `pre`. The
precondition should capture only what soundness genuinely needs; efficiency
prerequisites do not belong here. -/
def SoundUnder (pre : Block D.Op → Prop) (run : Block D.Op → Block D.Op) : Prop :=
  ∀ b, pre b → EquivBlock D b (run b)

/-- **Bridge to unconditional soundness.** Being sound under the trivial
precondition is exactly being `Sound` — so any existing `LocalPass`/`Sound` proof is
a `SoundUnder (fun _ => True)` proof and vice versa. -/
theorem soundUnder_true_iff {run : Block D.Op → Block D.Op} :
    SoundUnder (fun _ => True) run ↔ Sound D run :=
  ⟨fun h b => h b trivial, fun h b _ => h b⟩

/-- **Composition under a preserved precondition.** If `run₂` *preserves* `pre` and
both `run₁` and `run₂` are sound under `pre`, then `run₁ ∘ run₂` is sound under `pre`
(sound by transitivity of `EquivBlock`). The `Preserves pre run₂` hypothesis is
precisely what lets the precondition survive from the input into `run₁`'s domain. -/
theorem SoundUnder.comp {pre : Block D.Op → Prop} {run₁ run₂ : Block D.Op → Block D.Op}
    (hpre : Preserves pre run₂) (h₁ : SoundUnder pre run₁) (h₂ : SoundUnder pre run₂) :
    SoundUnder pre (run₁ ∘ run₂) :=
  fun b hb => (h₂ b hb).trans (h₁ (run₂ b) (hpre b hb))

/-- **Unconditional composition**, the `pre = fun _ => True` specialisation of
`SoundUnder.comp`: the composite of two unconditionally sound transforms is
unconditionally sound (the preserved-precondition side condition is vacuous). -/
theorem Sound.comp {run₁ run₂ : Block D.Op → Block D.Op}
    (h₁ : Sound D run₁) (h₂ : Sound D run₂) : Sound D (run₁ ∘ run₂) :=
  fun b => (h₂ b).trans (h₁ (run₂ b))

/-! ## Establishing an invariant (`Establishes`)

The obligation of *reaching* a normal form is concentrated in a normalization pass. -/

/-- A transform **establishes** the invariant `I` from precondition `pre` when it
turns every `pre`-satisfying program into an `I`-satisfying one. This is where the
work of *reaching* a normal form lives — a dedicated normalization pass — as opposed
to the `Preserves` promise that downstream passes keep `I` intact. -/
def Establishes (pre : Block D.Op → Prop) (I : Block D.Op → Prop)
    (run : Block D.Op → Block D.Op) : Prop :=
  ∀ b, pre b → I (run b)

omit [DecidableEq D.Value] in
/-- **Normalize once, then preserve.** If `estab` establishes `I` from `pre` and
`opt` preserves `I`, then `opt ∘ estab` establishes `I` from `pre`: the normalization
reaches the normal form and the optimizer keeps it. Iterating this lemma pushes an
established invariant through an arbitrarily long tail of preservers. -/
theorem Establishes.comp_preserves {pre I : Block D.Op → Prop}
    {estab opt : Block D.Op → Block D.Op}
    (he : Establishes pre I estab) (hp : Preserves I opt) :
    Establishes pre I (opt ∘ estab) :=
  fun b hb => hp (estab b) (he b hb)

/-! ## Global tier

The same three notions over the whole-program (`Run`) tier of `Spec/GlobalPass.lean`:
`SoundUnderRun` uses `RunEquivBlock` (the object-boundary equivalence), and
`PreservesObj`/`EstablishesObj` range over `Object → Object` transforms and object
invariants. These are the exact analogues of the local-tier definitions above; the
proofs are identical up to swapping `EquivBlock` for `RunEquivBlock` and `Block` for
`Object`. -/

/-- Whole-program analogue of `SoundUnder`: sound under `pre` at the object boundary,
i.e. `RunEquivBlock`-equivalent on every `pre`-satisfying block. -/
def SoundUnderRun (pre : Block D.Op → Prop) (run : Block D.Op → Block D.Op) : Prop :=
  ∀ b, pre b → RunEquivBlock D b (run b)

/-- Bridge: whole-program soundness under the trivial precondition is unconditional
whole-program equivalence. -/
theorem soundUnderRun_true_iff {run : Block D.Op → Block D.Op} :
    SoundUnderRun (fun _ => True) run ↔ ∀ b, RunEquivBlock D b (run b) :=
  ⟨fun h b => h b trivial, fun h b _ => h b⟩

/-- Composition under a preserved precondition, whole-program tier (transitivity of
`RunEquivBlock`). -/
theorem SoundUnderRun.comp {pre : Block D.Op → Prop} {run₁ run₂ : Block D.Op → Block D.Op}
    (hpre : Preserves pre run₂) (h₁ : SoundUnderRun pre run₁) (h₂ : SoundUnderRun pre run₂) :
    SoundUnderRun pre (run₁ ∘ run₂) :=
  fun b hb => (h₂ b hb).trans (h₁ (run₂ b) (hpre b hb))

/-- Object-invariant analogue of `Preserves`: an `Object → Object` transform maps
every `I`-satisfying object tree to an `I`-satisfying one. -/
def PreservesObj (I : Object D.Op → Prop) (run : Object D.Op → Object D.Op) : Prop :=
  ∀ o, I o → I (run o)

omit [DecidableEq D.Value] in
/-- The do-nothing object transform preserves every object invariant. -/
theorem PreservesObj.id {I : Object D.Op → Prop} : PreservesObj I _root_.id :=
  fun _ ho => ho

omit [DecidableEq D.Value] in
/-- Object-invariant preservation composes (matching `GlobalPass.comp`). -/
theorem PreservesObj.comp {I : Object D.Op → Prop} {run₁ run₂ : Object D.Op → Object D.Op}
    (h₁ : PreservesObj I run₁) (h₂ : PreservesObj I run₂) : PreservesObj I (run₁ ∘ run₂) :=
  fun o ho => h₁ (run₂ o) (h₂ o ho)

omit [DecidableEq D.Value] in
/-- A pipeline of object transforms preserves `I` when each stage does; folded as
`GlobalPass.ofList` folds passes. -/
theorem PreservesObj.ofList {I : Object D.Op → Prop} {rs : List (Object D.Op → Object D.Op)}
    (h : ∀ r ∈ rs, PreservesObj I r) :
    PreservesObj I (rs.foldr (fun r acc => acc ∘ r) _root_.id) := by
  induction rs with
  | nil => exact PreservesObj.id
  | cons r rs ih =>
      exact (ih fun r' hr' => h r' (List.mem_cons.2 (Or.inr hr'))).comp
        (h r (List.mem_cons.2 (Or.inl rfl)))

/-- Object-invariant analogue of `Establishes`: a transform reaches object invariant
`I` from precondition `pre`. -/
def EstablishesObj (pre : Object D.Op → Prop) (I : Object D.Op → Prop)
    (run : Object D.Op → Object D.Op) : Prop :=
  ∀ o, pre o → I (run o)

omit [DecidableEq D.Value] in
/-- Normalize once, then preserve — object tier. An establisher followed by a
preserver still establishes `I`. -/
theorem EstablishesObj.comp_preserves {pre I : Object D.Op → Prop}
    {estab opt : Object D.Op → Object D.Op}
    (he : EstablishesObj pre I estab) (hp : PreservesObj I opt) :
    EstablishesObj pre I (opt ∘ estab) :=
  fun o ho => hp (estab o) (he o ho)

end YulEvmCompiler.Optimizer
