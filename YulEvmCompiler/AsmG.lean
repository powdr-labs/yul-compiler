import YulEvmCompiler.AsmSem
set_option warningAsError true
/-!
# YulEvmCompiler.AsmG

The **abstract-stack scheduling layer**: a structure between Yul and `List Asm`
whose only new proof burden is a *layout-refinement simulation against the
existing Asm machine* (`YulEvmCompiler.AsmSem`).

## Why this layer exists

In the current backend, variables live on the operand stack in declaration
order and every access commits *immediately* to a concrete depth: a read is
`dup depth`, an assignment is `swap depth; pop`. Nothing ever chooses a stack
shape. That is the single reason deep programs are rejected (`DUP16`/`SWAP16`
reach) and why the memory-spill fallback exists. Yul→Yul passes cannot fix it —
Yul has no stack — and flat `List Asm` is already committed to the indices.

`AsmG` decouples the two concerns. The *abstract* side names each live value
with a `VId` and tracks a `Layout` (which value sits at each physical stack
position, top first). A *scheduler* then picks the concrete `dup`/`swap`/`pop`
shuffles that realize the accesses a block needs, and is free to choose the
shallowest occurrence, reuse dead slots, and minimize movement.

## The correctness idea: no new semantics

Crucially, the values on an `AsmG` stack *are* ordinary Asm values — a `Layout`
is realized by a concrete `AsmSem` stack under a valuation `val : VId → AVal`:

```
Realizes val L σ  :=  σ = L.map val
```

So a scheduler primitive is correct exactly when the `Asm` it emits drives the
real `AsmSem` machine from one realized layout to the next. There is no second
`Run`/`Step` judgment to define and no funDef/hoisting congruence to re-prove —
the burden that stalls a full IR. Everything below is a simulation *into the
machine that already exists*, discharged with `AStep`/`ASteps`.

## What is proven here (the kernel)

* `copyToTop` / `copyToTop_correct` — read: DUP the shallowest occurrence of a
  value to the top (rejecting, not miscompiling, when it is out of `DUP` reach).
  The fresh top cell carries the *same* `VId`, which is sound precisely because
  values are immutable (SSA-style): both cells realize to the same `AVal`.
* `pop_step` — drop a dead top slot.
* `swap_step` — exchange the top with a deeper slot (the "move" primitive).
* `loadBinArgs` / `loadBinArgs_correct` — a composite showing the primitives
  compose through `ASteps.trans`: load two operands for a binary built-in in
  Yul's right-to-left order, each from its shallowest occurrence. This is the
  layout-aware version of built-in argument setup.

## The full scheduler this kernel is meant to grow into

```
theorem schedule_correct (g : Layout) (t : Layout) (code : List Asm) :
    scheduleTo g t = some code →
    ∀ {val σ yst rest}, Realizes val g σ →
      ASteps prog ⟨code ++ rest, σ, yst⟩ ⟨rest, ???, yst⟩ ∧ Realizes val t ???
```

i.e. a total-when-in-reach shuffle `scheduleTo : Layout → Layout → Option (List
Asm)` that transforms any stack realizing the *current* layout into one
realizing a *target* layout, built by composing the primitives below. Still to
come: the `compileStmts → AsmG` front end that emits access requests instead of
raw `dup`/`swap`, and the layout selector that chooses block-boundary targets
(the analogue of solc's `StackLayoutGenerator`). Both plug in above this kernel
without touching `AsmSem` or `Correctness`.
-/

namespace YulEvmCompiler

open YulSemantics.EVM (EvmState)

/-- An abstract value identifier. Distinct `VId`s denote distinct live values;
a value is immutable once introduced (SSA-style), so copying it (`dup`) simply
places the *same* `VId` in two stack positions. -/
abbrev VId := Nat

/-- A physical stack layout: the `VId` occupying each operand-stack position,
**top first**. Position `n` in the list is at machine depth `n`. -/
abbrev Layout := List VId

/-- The refinement relating an abstract `Layout` to a concrete `AsmSem` stack:
each slot realizes to its value under the valuation `val`. This is the *only*
invariant the scheduler must maintain — there is no separate semantics. -/
abbrev Realizes (val : VId → AVal) (L : Layout) (σ : List AVal) : Prop :=
  σ = L.map val

@[simp] theorem realizes_def (val : VId → AVal) (L : Layout) (σ : List AVal) :
    Realizes val L σ ↔ σ = L.map val := Iff.rfl

/-! ### Locating a value in the layout -/

/-- Split a layout at the **first** occurrence of `x`: `splitAt? x L = some (τ,
ρ)` means `L = τ ++ x :: ρ` with `x ∉ τ`. Returning the first occurrence is
what makes a read pick the *shallowest* copy — the depth is `τ.length`. -/
def splitAt? (x : VId) : Layout → Option (Layout × Layout)
  | [] => none
  | y :: ys =>
      if y = x then some ([], ys)
      else (splitAt? x ys).map (fun p => (y :: p.1, p.2))

/-- A successful split reconstructs the layout. -/
theorem splitAt?_eq {x : VId} : ∀ {L τ ρ : Layout},
    splitAt? x L = some (τ, ρ) → L = τ ++ x :: ρ := by
  intro L
  induction L with
  | nil => intro τ ρ h; simp [splitAt?] at h
  | cons y ys ih =>
    intro τ ρ h
    simp only [splitAt?] at h
    by_cases hy : y = x
    · subst hy
      rw [if_pos rfl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    · rw [if_neg hy] at h
      obtain ⟨p, hp, hpe⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨pa, pb⟩ := p
      simp only [Prod.mk.injEq] at hpe
      obtain ⟨rfl, rfl⟩ := hpe
      rw [List.cons_append, ih hp]

/-! ### Primitive: read (copy a value to the top) -/

/-- Emit the `Asm` that copies the shallowest occurrence of `x` to the top of
the stack, or `none` if that occurrence is out of `DUP` reach (depth ≥ 16).
Rejection here is the layer's honest "cannot yet realize", never a
miscompilation. -/
def copyToTop (L : Layout) (x : VId) : Option Asm :=
  match splitAt? x L with
  | some (τ, _) => if h : τ.length < 16 then some (.dup ⟨τ.length, h⟩) else none
  | none => none

/-- **Correctness of a read.** If `copyToTop` accepts, the emitted instruction
drives the real machine from any stack realizing `L` to one realizing `x :: L`,
placing `val x` on top and leaving the machine state untouched. -/
theorem copyToTop_correct [model : ExternalModel] {prog : List Asm}
    {L : Layout} {x : VId} {i : Asm}
    {val : VId → AVal} {σ : List AVal} {yst : EvmState} {rest : List Asm}
    (hc : copyToTop L x = some i) (hr : Realizes val L σ) :
    ASteps (model := model) prog ⟨i :: rest, σ, yst⟩ ⟨rest, val x :: σ, yst⟩
      ∧ Realizes val (x :: L) (val x :: σ) := by
  rcases hs : splitAt? x L with _ | ⟨τ, ρ⟩
  · simp [copyToTop, hs] at hc
  · simp only [copyToTop, hs] at hc
    by_cases hlen : τ.length < 16
    · rw [dif_pos hlen] at hc
      have hi : i = Asm.dup ⟨τ.length, hlen⟩ := by injection hc with h; exact h.symm
      have hL : L = τ ++ x :: ρ := splitAt?_eq hs
      have hσ : σ = τ.map val ++ val x :: ρ.map val := by
        have he : σ = L.map val := hr
        rw [he, hL]; simp
      refine ⟨?_, ?_⟩
      · rw [hi, hσ]
        refine ASteps.single ?_
        exact AStep.dup (model := model) (n := ⟨τ.length, hlen⟩) (v := val x)
          (τ := τ.map val) (ρ := ρ.map val) (c := rest) (by simp)
      · show val x :: σ = (x :: L).map val
        have he : σ = L.map val := hr
        rw [he]; rfl
    · rw [dif_neg hlen] at hc
      simp at hc

/-! ### Primitive: drop a dead slot -/

/-- **Correctness of a pop.** Discarding the top slot realizes the tail layout,
leaving the machine state untouched. -/
theorem pop_step [model : ExternalModel] {prog : List Asm}
    {x : VId} {L : Layout}
    {val : VId → AVal} {σ : List AVal} {yst : EvmState} {rest : List Asm}
    (hr : Realizes val (x :: L) σ) :
    ASteps (model := model) prog ⟨.pop :: rest, σ, yst⟩ ⟨rest, L.map val, yst⟩
      ∧ Realizes val L (L.map val) := by
  have he : σ = val x :: L.map val := hr
  refine ⟨?_, rfl⟩
  rw [he]
  exact ASteps.single AStep.pop

/-! ### Primitive: swap the top with a deeper slot -/

/-- **Correctness of a swap.** `swap n` exchanges the top slot with the slot at
depth `n + 1`. Stated on the split form of the layout, mirroring `AStep.swap`;
this is the "move" primitive a shuffle uses when a value must change position
without being duplicated. -/
theorem swap_step [model : ExternalModel] {prog : List Asm}
    {n : Fin 16} {a b : VId} {τ ρ : Layout}
    {val : VId → AVal} {σ : List AVal} {yst : EvmState} {rest : List Asm}
    (hlen : τ.length = n.val) (hr : Realizes val (a :: (τ ++ b :: ρ)) σ) :
    ASteps (model := model) prog ⟨.swap n :: rest, σ, yst⟩
        ⟨rest, val b :: (τ.map val ++ val a :: ρ.map val), yst⟩
      ∧ Realizes val (b :: (τ ++ a :: ρ))
          (val b :: (τ.map val ++ val a :: ρ.map val)) := by
  have hr' : σ = val a :: (τ.map val ++ val b :: ρ.map val) := by
    have he : σ = (a :: (τ ++ b :: ρ)).map val := hr
    simpa using he
  refine ⟨?_, ?_⟩
  · rw [hr']
    refine ASteps.single ?_
    exact AStep.swap (model := model) (n := n) (a := val a) (b := val b)
      (τ := τ.map val) (ρ := ρ.map val) (c := rest) (by simpa using hlen)
  · show val b :: (τ.map val ++ val a :: ρ.map val)
        = (b :: (τ ++ a :: ρ)).map val
    simp

/-! ### Composite: layout-aware binary-argument loading -/

/-- Emit code that loads two operands for a binary built-in in Yul's
right-to-left order — `b` first (so it ends up second on the stack), then `a`
on top — each copied from its shallowest occurrence. `none` if either is out of
reach. -/
def loadBinArgs (L : Layout) (a b : VId) : Option (List Asm) :=
  match copyToTop L b, copyToTop (b :: L) a with
  | some ib, some ia => some [ib, ia]
  | _, _ => none

/-- **Correctness of the composite.** The primitives compose through
`ASteps.trans`: the emitted code drives any stack realizing `L` to one realizing
`a :: b :: L`, with `val a` on top of `val b`, machine state untouched. -/
theorem loadBinArgs_correct [model : ExternalModel] {prog : List Asm}
    {L : Layout} {a b : VId} {code : List Asm}
    {val : VId → AVal} {σ : List AVal} {yst : EvmState} {rest : List Asm}
    (hc : loadBinArgs L a b = some code) (hr : Realizes val L σ) :
    ASteps (model := model) prog ⟨code ++ rest, σ, yst⟩
        ⟨rest, val a :: val b :: σ, yst⟩
      ∧ Realizes val (a :: b :: L) (val a :: val b :: σ) := by
  rcases hb : copyToTop L b with _ | ib
  · simp [loadBinArgs, hb] at hc
  · rcases ha : copyToTop (b :: L) a with _ | ia
    · simp [loadBinArgs, hb, ha] at hc
    · have hcode : code = [ib, ia] := by
        have hthis := hc
        simp only [loadBinArgs, hb, ha, Option.some.injEq] at hthis
        exact hthis.symm
      subst hcode
      obtain ⟨hstep1, hr1⟩ := copyToTop_correct (model := model) (prog := prog)
        (rest := ia :: rest) (yst := yst) hb hr
      obtain ⟨hstep2, hr2⟩ := copyToTop_correct (model := model) (prog := prog)
        (rest := rest) (yst := yst) ha hr1
      refine ⟨?_, hr2⟩
      have hcat : ([ib, ia] : List Asm) ++ rest = ib :: ia :: rest := rfl
      rw [hcat]
      exact hstep1.trans hstep2

end YulEvmCompiler
