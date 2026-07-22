import YulEvmCompiler.Optimizer.Implementation.DeadStore.KeyDiff
import YulEvmCompiler.Optimizer.Core.Subst
/-!
# Redundant-store elimination — M1: abstract domain and `Valid`

The word-region abstract store (`avail`) the redundant-store dataflow pass
threads through a block, plus the soundness relation `Valid` that anchors it to
the pinned Yul semantics.

Design (see `YulEvmCompiler/Optimizer/RedundantStores.md`):

* We track only **known** facts, so the abstract value `⊤` ("unknown") is simply
  *absence from the map* — no explicit lattice-top constructor.
* A fact pairs a **pure key expression** (`Expr Op`, compared through the proved
  `KeyDiff` alias oracle) with a **Core value** (`Term Γ 1`, intrinsically scoped
  in the current lexical context `Γ`, so scope-exit / rebind kills are a typing
  obligation rather than a freshness side-condition).
* `Valid` says every recorded fact holds concretely *right now*: the key
  evaluates purely (no state change, no halt) to a word `kw`, and the value term
  evaluates purely to the word currently stored at `kw`.

M1 delivers the domain, its `KeyDiff`-driven operations, and the structural
`Valid` lemmas (`nil`, `filter`/`kill`, `cons`/`store`) that later milestones
consume. The *semantic* bridge "must-alias keys evaluate to equal words" is a
KeyDiff-soundness obligation deferred to M2, where the transfer proof needs it.
-/

namespace YulEvmCompiler.Optimizer.RedundantStore

open YulSemantics YulSemantics.EVM
open YulEvmCompiler.Optimizer.Core
open YulEvmCompiler.Optimizer.DeadStore (mustAliasWord mustNotAliasWord)

variable {calls : ExternalCalls} {creates : ExternalCreates}
local notation "D" => evmWithExternal calls creates

/-! ### The abstract store -/

/-- One tracked slot: a pure key expression and the Core value known to be
stored there, well-scoped in `Γ`. -/
structure Fact (Γ : Ctx) where
  key : Expr Op
  val : Term Γ 1

/-- The `avail` component of the abstract store: alias-canonical known slots for
one word region (storage *or* transient). Absence of a key means "unknown". -/
abbrev Avail (Γ : Ctx) := List (Fact Γ)

/-- Look up the value known for a slot that **must-alias** `k`. (`List.find?` is
named explicitly: dot-notation on `Avail` would resolve to this very function.) -/
def Avail.find? {Γ : Ctx} (σ : Avail Γ) (k : Expr Op) : Option (Term Γ 1) :=
  (List.find? (fun f : Fact Γ => mustAliasWord f.key k) σ).map (·.val)

/-- Invalidate every fact that could alias `k` — keep only the provably-disjoint
ones. Applied when `k` is written or its aliasing becomes uncertain. -/
def Avail.kill {Γ : Ctx} (σ : Avail Γ) (k : Expr Op) : Avail Γ :=
  List.filter (fun f : Fact Γ => mustNotAliasWord f.key k) σ

/-- Record that slot `k` now holds value `v`: drop possible aliases, then add the
fact. (Redundant/dead-store *decisions* driven by this map come in M3.) -/
def Avail.store {Γ : Ctx} (σ : Avail Γ) (k : Expr Op) (v : Term Γ 1) : Avail Γ :=
  ⟨k, v⟩ :: σ.kill k

/-! ### The soundness relation

`read` is the region's slot accessor: `(·.storage)` for persistent storage,
`(·.transient)` for transient storage. Keeping it a parameter lets the same
domain and lemmas serve both word regions. -/

/-- Persistent-storage slot reader. -/
@[inline] def storageRead (st : EvmState) : U256 → U256 := st.storage
/-- Transient-storage slot reader. -/
@[inline] def transientRead (st : EvmState) : U256 → U256 := st.transient

/-- **The M1 invariant.** Every recorded fact holds at `(funs, V, st)`: its key
evaluates purely (state `st` unchanged, no halt) to some word `kw`, and its value
term evaluates purely to the word currently in that slot, `read st kw`. -/
def Valid (funs : FunEnv D) (V : VEnv D) (st : EvmState)
    (read : EvmState → U256 → U256) (σ : Avail Γ) : Prop :=
  ∀ f ∈ σ, ∃ kw : U256,
    EvalExpr D funs V st f.key (.vals [kw] st) ∧
    EvalExpr D funs V st (Term.emit f.val) (.vals [read st kw] st)

-- Each lemma binds `funs`/`V`/`st`/`read`/`σ` explicitly rather than through a
-- shared `variable` block: with `local notation "D"` a shared block mis-includes
-- the dialect (it drops `funs` and leaves the dialect arguments unresolved). This
-- is the same per-theorem-binder idiom `DeadStore` uses. `calls`/`creates` are
-- inferred from `funs : FunEnv D`.

/-- The empty store is valid in every configuration. -/
@[simp] theorem Valid_nil {Γ : Ctx} {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    {read : EvmState → U256 → U256} :
    Valid funs V st read ([] : Avail Γ) := by
  intro f hf; nomatch hf

/-- `Valid` for `f :: σ` splits into the head fact holding and `Valid σ`. -/
theorem Valid_cons {Γ : Ctx} {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    {read : EvmState → U256 → U256} {σ : Avail Γ} {f : Fact Γ} :
    Valid funs V st read (f :: σ) ↔
      (∃ kw : U256, EvalExpr D funs V st f.key (.vals [kw] st) ∧
        EvalExpr D funs V st (Term.emit f.val) (.vals [read st kw] st))
      ∧ Valid funs V st read σ := by
  constructor
  · intro h
    exact ⟨h f (List.mem_cons_self ..), fun g hg => h g (List.mem_cons_of_mem _ hg)⟩
  · rintro ⟨hf, hσ⟩ g hg
    rcases List.mem_cons.mp hg with rfl | hg'
    · exact hf
    · exact hσ g hg'

/-- Validity is preserved by any sub-store obtained through `List.filter` — in
particular by `kill`. -/
theorem Valid.filter {Γ : Ctx} {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    {read : EvmState → U256 → U256} {σ : Avail Γ}
    (h : Valid funs V st read σ) (p : Fact Γ → Bool) :
    Valid funs V st read (σ.filter p) :=
  fun f hf => h f (List.mem_of_mem_filter hf)

/-- `kill` preserves validity (it only drops facts). -/
theorem Valid.kill {Γ : Ctx} {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    {read : EvmState → U256 → U256} {σ : Avail Γ}
    (h : Valid funs V st read σ) (k : Expr Op) :
    Valid funs V st read (σ.kill k) :=
  h.filter _

/-- `store` preserves validity, given that the new fact holds concretely. This is
the shape M3 discharges from a successful `sstore` step. -/
theorem Valid.store {Γ : Ctx} {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    {read : EvmState → U256 → U256} {σ : Avail Γ}
    (h : Valid funs V st read σ) {k : Expr Op} {v : Term Γ 1}
    (hnew : ∃ kw : U256, EvalExpr D funs V st k (.vals [kw] st) ∧
        EvalExpr D funs V st (Term.emit v) (.vals [read st kw] st)) :
    Valid funs V st read (σ.store k v) :=
  Valid_cons.mpr ⟨hnew, h.kill k⟩

/-! ### Lookup soundness (structural half)

`find?` returns the value of an actual member fact whose key must-aliases the
query. Under `Valid`, that fact's own evaluation guarantee is therefore
available. Turning the guarantee on the *stored* key into one on the *queried*
key needs "must-alias ⇒ equal word" — a KeyDiff-soundness lemma proved in M2. -/

/-- `find?` exposes a witnessing member fact. -/
theorem Avail.find?_some {Γ : Ctx} {σ : Avail Γ} {k : Expr Op} {v : Term Γ 1}
    (h : σ.find? k = some v) :
    ∃ f ∈ σ, f.val = v ∧ mustAliasWord f.key k = true := by
  simp only [Avail.find?] at h
  cases hf : List.find? (fun f : Fact Γ => mustAliasWord f.key k) σ with
  | none => rw [hf] at h; simp at h
  | some f =>
      rw [hf] at h; simp only [Option.map_some, Option.some.injEq] at h
      refine ⟨f, List.mem_of_find?_eq_some hf, h, ?_⟩
      have hp := List.find?_some hf
      simpa using hp

/-- Under `Valid`, a successful lookup yields the evaluation guarantee on the
matched fact's key (the M2 alias bridge carries it to the queried key). -/
theorem Valid.find? {Γ : Ctx} {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    {read : EvmState → U256 → U256} {σ : Avail Γ}
    (h : Valid funs V st read σ)
    {k : Expr Op} {v : Term Γ 1} (hfind : σ.find? k = some v) :
    ∃ (fk : Expr Op) (kw : U256), mustAliasWord fk k = true ∧
      EvalExpr D funs V st fk (.vals [kw] st) ∧
      EvalExpr D funs V st (Term.emit v) (.vals [read st kw] st) := by
  obtain ⟨f, hmem, hval, halias⟩ := Avail.find?_some hfind
  obtain ⟨kw, hkey, hvaleval⟩ := h f hmem
  exact ⟨f.key, kw, halias, hkey, hval ▸ hvaleval⟩

end YulEvmCompiler.Optimizer.RedundantStore
