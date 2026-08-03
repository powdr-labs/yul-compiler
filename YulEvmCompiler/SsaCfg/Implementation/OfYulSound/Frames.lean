import YulEvmCompiler.SsaCfg.Implementation.OfYulSound.Basics
set_option warningAsError true

/-!
# YulEvmCompiler.SsaCfg.Implementation.OfYulSound.Frames

Inverting the construction monad, and the freshness/frame algebra.

`M.*` inversion lemmas for every primitive the builder uses, and the
monotonicity relations they generate — `Grows`, `Completes`, `SGrowsAt`,
`FGrows`, `FContents`, `FOwned`, `FPrefix`, `SGrows` — together with the
`allocScope`/`trExpr` frame lemmas that are provable without the statement
recursion.
-/

namespace YulEvmCompiler.SsaCfg
open YulSemantics (Ident Literal Expr Stmt VEnv Outcome)
open YulSemantics.EVM (U256 EvmState Op builtinWithExternal evmWithExternal)

/-! ## Inverting the construction monad

`M = StateT BState Option`; a successful run of a `do` block decomposes into
successful runs of its steps, exactly as `compileProgramAsm_inv` decomposes the
classic backend's `Option` pipeline. Everything in this section is by
definitional unfolding. -/

namespace M

theorem bind_eq {α β} (x : M α) (f : α → M β) (s : BState) :
    (x >>= f) s = (x s).bind (fun p => f p.1 p.2) := rfl

/-- The workhorse: invert one `do`-step. -/
theorem bind_inv {α β} {x : M α} {f : α → M β} {s : BState} {r : β × BState}
    (h : (x >>= f) s = some r) :
    ∃ (a : α) (s₁ : BState), x s = some (a, s₁) ∧ f a s₁ = some r := by
  rw [bind_eq] at h
  cases hx : x s with
  | none => rw [hx] at h; exact absurd h (by simp)
  | some p =>
    rw [hx] at h
    simp only [Option.bind_some] at h
    exact ⟨p.1, p.2, rfl, h⟩

@[simp] theorem pure_apply {α} (a : α) (s : BState) :
    (pure a : M α) s = some (a, s) := rfl

theorem pure_inv {α} {a a' : α} {s s' : BState} (h : (pure a : M α) s = some (a', s')) :
    a' = a ∧ s' = s := by
  rw [pure_apply] at h
  have h' := Option.some.inj h
  exact ⟨(congrArg Prod.fst h').symm, (congrArg Prod.snd h').symm⟩

@[simp] theorem reject_apply {α} (s : BState) : (reject : M α) s = none := rfl

theorem liftO_inv {α} {o : Option α} {s : BState} {a : α} {s' : BState}
    (h : (liftO o : M α) s = some (a, s')) : o = some a ∧ s' = s := by
  cases o with
  | none => exact absurd h (by simp [liftO])
  | some b =>
    have h' : (b, s) = (a, s') := Option.some.inj h
    have h1 : b = a := congrArg Prod.fst h'
    have h2 : s = s' := congrArg Prod.snd h'
    exact ⟨by rw [h1], h2.symm⟩

/-! ### The primitives -/

@[simp] theorem freshVal_apply (s : BState) :
    freshVal s = some (s.fn.nextVal,
      { s with fn := { s.fn with nextVal := s.fn.nextVal + 1 } }) := rfl

@[simp] theorem emit_apply (i : Instr) (s : BState) :
    emit i s = some ((), { s with fn := { s.fn with cur := i :: s.fn.cur } }) := rfl

@[simp] theorem newBlock_apply (params : List ValId) (s : BState) :
    newBlock params s = some (s.fn.blocks.size,
      { s with fn := { s.fn with
          blocks := s.fn.blocks.push ⟨params, [], .ret []⟩ } }) := rfl

@[simp] theorem moveTo_apply (b : BlockId) (s : BState) :
    moveTo b s = some ((), { s with fn := { s.fn with curId := b, cur := [] } }) := rfl

@[simp] theorem getFn_apply (s : BState) : getFn s = some (s.fn, s) := rfl

@[simp] theorem setFn_apply (fn : FnState) (s : BState) :
    setFn fn s = some ((), { s with fn }) := rfl

@[simp] theorem allocFunc_apply (s : BState) :
    allocFunc s = some (s.funcs.size, { s with funcs := s.funcs.push none }) := rfl

theorem sealCur_inv {t : Term} {s s' : BState} {u : Unit}
    (h : sealCur t s = some (u, s')) :
    ∃ b, s.fn.blocks[s.fn.curId]? = some b
      ∧ s' = { s with fn := { s.fn with
          blocks := s.fn.blocks.set! s.fn.curId ⟨b.params, s.fn.cur.reverse, t⟩,
          cur := [] } } := by
  rw [sealCur] at h
  cases hb : s.fn.blocks[s.fn.curId]? with
  | none => rw [hb] at h; exact absurd h (by simp)
  | some b =>
    rw [hb] at h
    exact ⟨b, rfl, (congrArg Prod.snd (Option.some.inj h)).symm⟩

theorem fillFunc_inv {fid : FuncId} {f : Func} {s s' : BState} {u : Unit}
    (h : fillFunc fid f s = some (u, s')) :
    ∃ hlt : fid < s.funcs.size,
      s' = { s with funcs := s.funcs.set fid (some f) hlt } := by
  rw [fillFunc] at h
  by_cases hlt : fid < s.funcs.size
  · rw [dif_pos hlt] at h
    exact ⟨hlt, (congrArg Prod.snd (Option.some.inj h)).symm⟩
  · rw [dif_neg hlt] at h; exact absurd h (by simp)

theorem edgeArgs_inv {env : VMap} {xs : List Ident} {s s' : BState}
    {ids : List ValId} (h : edgeArgs env xs s = some (ids, s')) :
    xs.mapM env.get = some ids ∧ s' = s :=
  liftO_inv h

/-! ### Fresh-value allocation

The construction's parameter/return-value allocation is `mapM freshVal`, which
returns exactly the next `n` ids. This is the freshness engine: the ids are an
interval above the old `nextVal` and below the new one, hence pairwise
distinct and absent from any register file built from earlier ids. -/

theorem mapM_freshVal {α} : ∀ (xs : List α) (s : BState),
    (xs.mapM (fun _ => freshVal)) s
      = some (List.range' s.fn.nextVal xs.length,
          { s with fn := { s.fn with
              nextVal := s.fn.nextVal + xs.length } }) := by
  intro xs
  induction xs with
  | nil => intro s; rfl
  | cons x xs ih =>
    intro s
    have hn : s.fn.nextVal + 1 + xs.length = s.fn.nextVal + (xs.length + 1) :=
      Nat.add_right_comm _ _ _
    rw [List.mapM_cons, bind_eq, freshVal_apply]
    simp only [Option.bind_some]
    rw [bind_eq, ih]
    simp only [Option.bind_some, pure_apply, List.length_cons, List.range'_succ, hn]

theorem mapM_freshVal_length {α} {xs : List α} {s s' : BState} {ids : List ValId}
    (h : (xs.mapM (fun _ => freshVal)) s = some (ids, s')) :
    ids.length = xs.length ∧ ids = List.range' s.fn.nextVal xs.length
      ∧ s' = { s with fn := { s.fn with nextVal := s.fn.nextVal + xs.length } } := by
  rw [mapM_freshVal] at h
  have h' := Option.some.inj h
  obtain ⟨rfl, rfl⟩ : ids = List.range' s.fn.nextVal xs.length
      ∧ s' = { s with fn := { s.fn with nextVal := s.fn.nextVal + xs.length } } :=
    ⟨(congrArg Prod.fst h').symm, (congrArg Prod.snd h').symm⟩
  exact ⟨by simp, rfl, rfl⟩

theorem nodup_range' (k n : Nat) : (List.range' k n).Nodup := List.nodup_range'

theorem mem_range'_bounds {k n i : Nat} (h : i ∈ List.range' k n) : k ≤ i ∧ i < k + n := by
  rw [List.mem_range'_1] at h
  exact h

theorem some_pair_inj {α : Type} {a b : α} {s t : BState}
    (h : (some (a, s) : Option (α × BState)) = some (b, t)) : a = b ∧ s = t :=
  ⟨congrArg Prod.fst (Option.some.inj h), congrArg Prod.snd (Option.some.inj h)⟩

/-- Invert the `if <ok> then k else reject` form (`trExprN`'s arity gate). -/
theorem ite_reject_inv' {α : Type} {c : Prop} [Decidable c] {k : M α}
    {s : BState} {r : α × BState}
    (h : (if c then k else (reject : M α)) s = some r) : c ∧ k s = some r := by
  by_cases hc : c
  · exact ⟨hc, by rw [if_pos hc] at h; exact h⟩
  · rw [if_neg hc] at h; exact absurd h (by simp)

end M

/-! ## Freshness: the builder only allocates

`Grows s s'` records everything an *expression*-level translation step can do to
the builder state: raise `nextVal` and prepend to the current block's pending
instruction list. Nothing already written moves, and every id an expression
defines is at least the incoming `nextVal` — which is what makes `Regs.Le` (and
hence `EnvOK.mono`) available at every step. -/

/-- The builder state grew: `nextVal` rose, instructions were prepended to the
current block, and nothing else changed. -/
structure Grows (s s' : BState) : Prop where
  nextVal : s.fn.nextVal ≤ s'.fn.nextVal
  blocks : s.fn.blocks = s'.fn.blocks
  curId : s.fn.curId = s'.fn.curId
  funcs : s.funcs = s'.funcs
  cur : ∃ Δ, s'.fn.cur = Δ ++ s.fn.cur

namespace Grows

theorem rfl' (s : BState) : Grows s s := ⟨Nat.le_refl _, rfl, rfl, rfl, ⟨[], rfl⟩⟩

theorem trans {s₁ s₂ s₃ : BState} (h₁ : Grows s₁ s₂) (h₂ : Grows s₂ s₃) :
    Grows s₁ s₃ := by
  obtain ⟨Δ₁, e₁⟩ := h₁.cur
  obtain ⟨Δ₂, e₂⟩ := h₂.cur
  exact ⟨Nat.le_trans h₁.nextVal h₂.nextVal, h₁.blocks.trans h₂.blocks,
    h₁.curId.trans h₂.curId, h₁.funcs.trans h₂.funcs,
    ⟨Δ₂ ++ Δ₁, by rw [e₂, e₁, List.append_assoc]⟩⟩

theorem of_freshVal {s s' : BState} {v : ValId}
    (h : SsaCfg.freshVal s = some (v, s')) : Grows s s' := by
  rw [M.freshVal_apply] at h
  obtain ⟨rfl, rfl⟩ := M.some_pair_inj h
  exact ⟨Nat.le_succ _, rfl, rfl, rfl, ⟨[], rfl⟩⟩

theorem of_emit {i : Instr} {s s' : BState} {u : Unit}
    (h : SsaCfg.emit i s = some (u, s')) : Grows s s' := by
  rw [M.emit_apply] at h
  obtain ⟨rfl, rfl⟩ := M.some_pair_inj h
  exact ⟨Nat.le_refl _, rfl, rfl, rfl, ⟨[i], rfl⟩⟩

theorem of_liftO {α : Type} {o : Option α} {a : α} {s s' : BState}
    (h : (SsaCfg.liftO o : M α) s = some (a, s')) : Grows s s' := by
  obtain ⟨-, rfl⟩ := M.liftO_inv h
  exact rfl' _

theorem of_pure {α : Type} {a b : α} {s s' : BState}
    (h : (pure a : M α) s = some (b, s')) : Grows s s' := by
  obtain ⟨-, rfl⟩ := M.pure_inv h
  exact rfl' _

/-- `mapM freshVal` grows. -/
theorem of_mapM_freshVal {α : Type} {xs : List α} {s s' : BState}
    {ids : List ValId}
    (h : (xs.mapM (fun _ => SsaCfg.freshVal)) s = some (ids, s')) :
    Grows s s' := by
  obtain ⟨-, -, rfl⟩ := M.mapM_freshVal_length h
  exact ⟨by simp, rfl, rfl, rfl, ⟨[], rfl⟩⟩

end Grows

/-- The finished function *completes* a builder state — the placement invariant
the induction carries.

* `sealed`: every block the builder has laid down other than the one it is
  currently filling is already final. This holds at every `trStmt`/`trStmts`/
  `trScope` boundary: the construction always seals the block it is leaving
  before `moveTo`, and the only block it reserves without immediately sealing is
  the join/exit block it makes current on the way out.
* `params`: **every** reserved block keeps its parameter list, current or not.
  This is the strengthening the `cond`/`switch`/`forLoop` cases need, where a
  join/exit block is reserved *before* the blocks that jump to it are sealed —
  the edge-argument arity premises of `Exec.jump`/`Exec.branch*` are about the
  finished block, but the construction only ever sees the reserved one.
* `size`: the block array only grows. -/
structure Completes (f : Func) (fn : FnState)
    (joins : List BlockId := []) : Prop where
  sealed : ∀ (i : Nat) (b : Block), i ∉ joins → i ≠ fn.curId → fn.blocks[i]? = some b
      → f.blocks[i]? = some b
  params : ∀ (i : Nat) (b : Block), fn.blocks[i]? = some b
      → ∃ bf, f.blocks[i]? = some bf ∧ bf.params = b.params
  size : fn.blocks.size ≤ f.blocks.size

theorem Completes.protect {f : Func} {fn : FnState} {joins : List BlockId}
    (h : Completes f fn joins) (joinId : BlockId) :
    Completes f fn (joinId :: joins) := by
  refine ⟨?_, h.params, h.size⟩
  intro i b hnot hne hb
  exact h.sealed i b (fun hi => hnot (by simp [hi])) hne hb

/-- Backward completion transfer across the one non-fresh move structured
control performs: returning to a protected enclosing join.  `moveTo` changes
only `curId`/`cur`; if the output-current block is encountered while proving
the input's sealed field, it is the protected target and the non-membership
premise rules that case out. -/
theorem Completes.of_moveTo_protected {f : Func} {s s' : BState}
    {joinId : BlockId} {u : Unit} {joins : List BlockId}
    (hmem : joinId ∈ joins) (hmv : moveTo joinId s = some (u, s'))
    (h : Completes f s'.fn joins) : Completes f s.fn joins := by
  rw [M.moveTo_apply] at hmv
  obtain ⟨-, rfl⟩ := M.some_pair_inj hmv
  refine ⟨?_, h.params, h.size⟩
  intro i b hnot hne hb
  exact h.sealed i b hnot (fun hi => hnot (hi ▸ hmem)) hb

/-- Blocks protected by an enclosing structured construct were all reserved
before the fragment starts, and none is the fragment's current block.  The
first fact makes the property stable when the fragment moves to a fresh block;
the second licenses exact-block uses of `Completes.sealed` for the block the
fragment is currently filling. -/
structure ProtectedAt (joins : List BlockId) (fn : FnState) : Prop where
  below : ∀ i ∈ joins, i < fn.blocks.size
  away : fn.curId ∉ joins

namespace ProtectedAt

theorem nil (fn : FnState) : ProtectedAt [] fn := ⟨by simp, by simp⟩

end ProtectedAt

/-! ### Statement-class monotonicity

Statements do more than expressions: they reserve blocks, seal them, move the
current block, and fill function slots. `SGrowsAt N` is what survives, relative
to a *base* block count `N` (in use, the block count at the start of the
fragment):

* nothing shrinks (`nextVal`, `size`, `funcsSize`);
* **no block's parameter list ever changes** (`params`) — this is what feeds
  the `params` field of `Completes`;
* the only pre-existing block a fragment can disturb is the one it starts on
  (`keep`), because every other block it seals it reserved itself;
* correspondingly the current block either does not move or moves to a block
  reserved at or after `N` (`curId`).

The last two fields are exactly what makes the relation composable: `keep` for
the second half applies because `curId` for the first half puts the moved-to
block out of range. -/
structure SGrowsAt (N : Nat) (s s' : BState) : Prop where
  nextVal : s.fn.nextVal ≤ s'.fn.nextVal
  size : s.fn.blocks.size ≤ s'.fn.blocks.size
  funcsSize : s.funcs.size ≤ s'.funcs.size
  params : ∀ (i : Nat) (b : Block), s.fn.blocks[i]? = some b →
    ∃ b', s'.fn.blocks[i]? = some b' ∧ b'.params = b.params
  keep : ∀ (i : Nat) (b : Block), i < N → i ≠ s.fn.curId →
    s.fn.blocks[i]? = some b → s'.fn.blocks[i]? = some b
  curId : s'.fn.curId = s.fn.curId ∨ N ≤ s'.fn.curId

/-- Function slots are only ever appended and filled; nothing is ever removed.
Weak enough to survive `trFunc`'s `setFn` save/restore, which is why it is
tracked separately. -/
def FGrows (s s' : BState) : Prop := s.funcs.size ≤ s'.funcs.size

/-- Content half of function-table growth.  Reserved `none` slots may be
refined to a function, but an already-filled slot keeps the same function.
This is the pointwise prefix order needed to transport a local `trFunc`
result into the completed top-level table. -/
def FContents (s s' : BState) : Prop :=
  ∀ (i : Nat) (g : Func), s.funcs[i]? = some (some g) →
    s'.funcs[i]? = some (some g)

/-- Exact ownership of the function slots which are still pending in a local
builder state.  `owned` is not a list of function *names*: it is the
duplicate-free list of the concrete array indices whose reservations this
translation still has to discharge.  This index-level formulation is what
prevents two equal hoisted names from silently sharing one reservation.

The filled-prefix clause connects the local table to the one fixed completed
table used by the construction simulation.  Slots not allocated yet are
deliberately unconstrained. -/
structure FOwned (owned : List FuncId) (s done : BState) : Prop where
  nodup : owned.Nodup
  pending : ∀ i : FuncId, i ∈ owned ↔ s.funcs[i]? = some none
  filled : FContents s done

namespace FGrows

theorem rfl' (s : BState) : FGrows s s := Nat.le_refl _

theorem trans {s₁ s₂ s₃ : BState} (h₁ : FGrows s₁ s₂) (h₂ : FGrows s₂ s₃) :
    FGrows s₁ s₃ := Nat.le_trans h₁ h₂

theorem of_fnOnly {s s' : BState} (h : s.funcs = s'.funcs) : FGrows s s' := by
  rw [FGrows, h]

theorem of_getFn {s s' : BState} {fn : FnState} (h : getFn s = some (fn, s')) :
    FGrows s s' := by
  rw [M.getFn_apply] at h
  obtain ⟨rfl, rfl⟩ := M.some_pair_inj h
  exact rfl' _

theorem of_setFn {fn : FnState} {s s' : BState} {u : Unit}
    (h : setFn fn s = some (u, s')) : FGrows s s' := by
  rw [M.setFn_apply] at h
  obtain ⟨rfl, rfl⟩ := M.some_pair_inj h
  exact of_fnOnly rfl

end FGrows

namespace FContents

theorem rfl' (s : BState) : FContents s s := fun _ _ h => h

theorem trans {s₁ s₂ s₃ : BState} (h₁ : FContents s₁ s₂)
    (h₂ : FContents s₂ s₃) : FContents s₁ s₃ :=
  fun i g hi => h₂ i g (h₁ i g hi)

/-- Filling a genuinely reserved slot preserves every function that was
already present.  The `allocScope`/`trStmts` singleton recovery establishes
the `none` premise for the particular slot selected by `FMap.get`. -/
theorem of_fillFunc_empty {fid : FuncId} {g : Func} {s s' : BState}
    {u : Unit} (hempty : s.funcs[fid]? = some none)
    (h : fillFunc fid g s = some (u, s')) : FContents s s' := by
  obtain ⟨hlt, rfl⟩ := M.fillFunc_inv h
  intro i g' hi
  have hne : i ≠ fid := by
    intro heq
    subst i
    have hbad : some g' = none := Option.some.inj (hi.symm.trans hempty)
    cases hbad
  rw [Array.getElem?_set (h := hlt), if_neg (Ne.symm hne)]
  exact hi

end FContents

namespace FOwned

theorem rfl_of_no_pending {s : BState}
    (h : ∀ i : FuncId, s.funcs[i]? ≠ some none) : FOwned [] s s := by
  refine ⟨List.nodup_nil, ?_, FContents.rfl' s⟩
  intro i
  simp only [List.not_mem_nil, false_iff]
  exact h i

/-- Backwards form of allocation: the newly appended owned reservation is
removed when reconstructing the caller state. -/
theorem back_allocFunc {owned : List FuncId} {s s' done : BState}
    {fid : FuncId} (h : allocFunc s = some (fid, s'))
    (ho : FOwned (owned ++ [fid]) s' done) : FOwned owned s done := by
  rw [M.allocFunc_apply] at h
  obtain ⟨rfl, rfl⟩ := M.some_pair_inj h
  have hnd : owned.Nodup := (ho.nodup.of_append_left)
  have hnot : s.funcs.size ∉ owned := by
    have hd := (List.nodup_append'.mp ho.nodup).2.2
    exact fun hm => (List.disjoint_left.mp hd) hm (by simp)
  refine ⟨hnd, ?_, ?_⟩
  · intro i
    by_cases hi : i = s.funcs.size
    · subst i
      simp [hnot]
    · have hp := ho.pending i
      simpa [Array.getElem?_push, hi] using hp
  · intro i g hi
    apply ho.filled i g
    rw [Array.getElem?_push, if_neg]
    · exact hi
    · intro heq
      subst i
      simp at hi

/-- Backwards form of whole-scope allocation: remove precisely the reservation
suffix recorded by the generated scope map. -/
theorem back_allocScope {owned : List FuncId} {ss : List (Stmt Op)}
    {s s' done : BState} {scope : List (Ident × FuncId)}
    (h : allocScope ss s = some (scope, s'))
    (ho : FOwned (owned ++ scope.map Prod.snd) s' done) :
    FOwned owned s done := by
  rw [allocScope] at h
  have fold : ∀ (l : List (Stmt Op)) (acc : List (Ident × FuncId))
      (s₀ s₁ : BState) (out : List (Ident × FuncId)),
      (l.foldlM (init := acc) fun acc (st : Stmt Op) =>
        match st with
        | Stmt.funDef n _ _ _ => do
            let fid ← allocFunc
            pure (acc ++ [(n, fid)])
        | _ => pure acc) s₀ = some (out, s₁) →
      FOwned (owned ++ out.map Prod.snd) s₁ done →
      FOwned (owned ++ acc.map Prod.snd) s₀ done := by
    intro l
    induction l with
    | nil =>
        intro acc s₀ s₁ out hl hown
        obtain ⟨rfl, rfl⟩ := M.pure_inv hl
        exact hown
    | cons st rest ih =>
        intro acc s₀ s₁ out hl hown
        rw [List.foldlM_cons] at hl
        obtain ⟨acc', t, hst, hrest⟩ := M.bind_inv hl
        have hmid := ih acc' t s₁ out hrest hown
        cases st with
        | funDef n ps rs body =>
            obtain ⟨fid, u, ha, hp⟩ := M.bind_inv hst
            obtain ⟨rfl, rfl⟩ := M.pure_inv hp
            have hback := FOwned.back_allocFunc
              (owned := owned ++ acc.map Prod.snd) ha (by
              simpa [List.map_append, List.append_assoc] using hmid)
            simpa using hback
        | block body | letDecl vars val | assign vars e | cond e body
        | forLoop init e post body | «break» | «continue» | leave
        | switch e cases dflt | exprStmt e =>
            have heq := M.pure_inv hst
            simpa [heq.1, heq.2] using hmid
  simpa using fold ss [] s s' scope h ho

/-- Filling an owned empty slot consumes exactly that index.  The theorem is
stated backwards because a completed suffix tells us both that the output slot
contains `g` and that it agrees with `done`; reconstructing the input then
restores `fid` to the pending budget. -/
theorem back_fillFunc {owned : List FuncId} {fid : FuncId} {g : Func}
    {s s' done : BState} {u : Unit}
    (hempty : s.funcs[fid]? = some none)
    (h : fillFunc fid g s = some (u, s'))
    (ho : FOwned owned s' done) : FOwned (fid :: owned) s done := by
  have hfill := h
  obtain ⟨hlt, rfl⟩ := M.fillFunc_inv h
  have hslot : ({ s with funcs := s.funcs.set fid (some g) hlt }).funcs[fid]?
      = some (some g) := by simp
  have hnot : fid ∉ owned := by
    intro hm
    have hp := (ho.pending fid).mp hm
    rw [hslot] at hp
    cases Option.some.inj hp
  refine ⟨List.nodup_cons.mpr ⟨hnot, ho.nodup⟩, ?_, ?_⟩
  · intro i
    by_cases hi : i = fid
    · subst i
      simp [hempty]
    · have hp := ho.pending i
      rw [Array.getElem?_set (h := hlt), if_neg (Ne.symm hi)] at hp
      simpa [hi] using hp
  · exact FContents.trans (FContents.of_fillFunc_empty hempty hfill) ho.filled

end FOwned

/-! ### Function-table prefix frames

`trFunc` may recursively allocate and fill nested functions while an enclosing
scope still has reserved `none` slots.  Size growth alone does not say that
those caller-owned slots survived.  `FPrefix N s s'` records the stronger
frame fact: every slot below the allocation watermark `N` is byte-for-byte
unchanged (including a pending `none`). -/

def FPrefix (N : Nat) (s s' : BState) : Prop :=
  ∀ i : FuncId, i < N → s'.funcs[i]? = s.funcs[i]?

namespace FPrefix

theorem rfl' (N : Nat) (s : BState) : FPrefix N s s := fun _ _ => rfl

theorem trans {N : Nat} {s₀ s₁ s₂ : BState}
    (h₀₁ : FPrefix N s₀ s₁) (h₁₂ : FPrefix N s₁ s₂) :
    FPrefix N s₀ s₂ := by
  intro i hi
  exact (h₁₂ i hi).trans (h₀₁ i hi)

/-- A theorem at a larger watermark implies one at every smaller watermark. -/
theorem mono {N N' : Nat} (hN : N' ≤ N) {s s' : BState}
    (h : FPrefix N s s') : FPrefix N' s s' :=
  fun i hi => h i (Nat.lt_of_lt_of_le hi hN)

theorem size {N : Nat} {s s' : BState} (h : FPrefix N s s')
    (hN : N ≤ s.funcs.size) : N ≤ s'.funcs.size := by
  cases N with
  | zero => exact Nat.zero_le _
  | succ n =>
      by_contra hn
      have hinLt : n < s.funcs.size := Nat.lt_of_succ_le hN
      have houtLe : s'.funcs.size ≤ n :=
        Nat.le_of_lt_succ (Nat.lt_of_not_ge hn)
      have hin := Array.getElem?_eq_getElem (xs := s.funcs) (i := n) hinLt
      have hout := Array.getElem?_eq_none (xs := s'.funcs) (i := n) houtLe
      have heq := h n (Nat.lt_succ_self n)
      rw [hout, hin] at heq
      cases heq

theorem of_funcs_eq {N : Nat} {s s' : BState} (h : s'.funcs = s.funcs) :
    FPrefix N s s' := by
  intro i hi
  rw [h]

theorem of_grows {N : Nat} {s s' : BState} (h : Grows s s') :
    FPrefix N s s' := of_funcs_eq h.funcs.symm

theorem of_allocFunc {N : Nat} {s s' : BState} {fid : FuncId}
    (hN : N ≤ s.funcs.size) (h : allocFunc s = some (fid, s')) :
    FPrefix N s s' := by
  rw [M.allocFunc_apply] at h
  obtain ⟨rfl, rfl⟩ := M.some_pair_inj h
  intro i hi
  rw [Array.getElem?_push, if_neg
    (Nat.ne_of_lt (Nat.lt_of_lt_of_le hi hN))]

theorem of_fillFunc {N : Nat} {s s' : BState} {fid : FuncId} {g : Func}
    {u : Unit} (hfid : N ≤ fid) (h : fillFunc fid g s = some (u, s')) :
    FPrefix N s s' := by
  obtain ⟨hlt, rfl⟩ := M.fillFunc_inv h
  intro i hi
  rw [Array.getElem?_set (h := hlt), if_neg
    (Nat.ne_of_gt (Nat.lt_of_lt_of_le hi hfid))]

theorem of_getFn {N : Nat} {s s' : BState} {fn : FnState}
    (h : getFn s = some (fn, s')) : FPrefix N s s' := by
  rw [M.getFn_apply] at h
  obtain ⟨rfl, rfl⟩ := M.some_pair_inj h
  exact rfl' _ _

theorem of_setFn {N : Nat} {s s' : BState} {fn : FnState} {u : Unit}
    (h : setFn fn s = some (u, s')) : FPrefix N s s' := by
  rw [M.setFn_apply] at h
  obtain ⟨rfl, rfl⟩ := M.some_pair_inj h
  exact rfl' _ _

theorem of_newBlock {N : Nat} {s s' : BState} {ps : List ValId}
    {bid : BlockId} (h : newBlock ps s = some (bid, s')) : FPrefix N s s' := by
  rw [M.newBlock_apply] at h
  obtain ⟨rfl, rfl⟩ := M.some_pair_inj h
  exact rfl' _ _

theorem of_moveTo {N : Nat} {s s' : BState} {bid : BlockId} {u : Unit}
    (h : moveTo bid s = some (u, s')) : FPrefix N s s' := by
  rw [M.moveTo_apply] at h
  obtain ⟨rfl, rfl⟩ := M.some_pair_inj h
  exact rfl' _ _

theorem of_sealCur {N : Nat} {s s' : BState} {t : Term} {u : Unit}
    (h : sealCur t s = some (u, s')) : FPrefix N s s' := by
  obtain ⟨b, hb, rfl⟩ := M.sealCur_inv h
  exact rfl' _ _

theorem of_liftO {N : Nat} {α : Type} {o : Option α} {a : α}
    {s s' : BState} (h : (liftO o : M α) s = some (a, s')) :
    FPrefix N s s' := by
  obtain ⟨-, rfl⟩ := M.liftO_inv h
  exact rfl' _ _

theorem of_pure {N : Nat} {α : Type} {a b : α} {s s' : BState}
    (h : (pure a : M α) s = some (b, s')) : FPrefix N s s' := by
  obtain ⟨-, rfl⟩ := M.pure_inv h
  exact rfl' _ _

theorem of_edgeArgs {N : Nat} {env : VMap} {xs : List Ident}
    {s s' : BState} {ids : List ValId}
    (h : edgeArgs env xs s = some (ids, s')) : FPrefix N s s' :=
  of_liftO h

end FPrefix

namespace FOwned

/-- Ownership budgets are extensional up to permutation; their list order is
only a convenient way to state duplicate-freedom. -/
theorem perm {owned owned' : List FuncId} {s done : BState}
    (hp : owned.Perm owned') (ho : FOwned owned s done) :
    FOwned owned' s done := by
  refine ⟨hp.nodup ho.nodup, ?_, ho.filled⟩
  intro i
  rw [← hp.mem_iff, ho.pending]

/-- Pull ownership backward across a closed nested translation which frames
the caller's whole input table.  The explicit bound says that `owned` really
belongs to the caller rather than to slots freshly allocated by the nested
translation; this is the small side condition the simulation motive must
thread together with `FOwned`. -/
theorem back_fprefix {owned : List FuncId} {s s' done : BState}
    (hp : FPrefix s.funcs.size s s')
    (hbound : ∀ i : FuncId, i ∈ owned → i < s.funcs.size)
    (ho : FOwned owned s' done) : FOwned owned s done := by
  refine ⟨ho.nodup, ?_, ?_⟩
  · intro i
    constructor
    · intro hi
      rw [← hp i (hbound i hi)]
      exact (ho.pending i).mp hi
    · intro hi
      have hlt : i < s.funcs.size := lt_size_of_getElem? hi
      apply (ho.pending i).mpr
      rwa [hp i hlt]
  · intro i g hi
    have hlt : i < s.funcs.size := lt_size_of_getElem? hi
    apply ho.filled i g
    rwa [hp i hlt]

end FOwned

namespace SGrowsAt

/-- A larger base is a stronger statement. -/
theorem mono {N N' : Nat} (hle : N' ≤ N) {s s' : BState} (h : SGrowsAt N s s') :
    SGrowsAt N' s s' :=
  ⟨h.nextVal, h.size, h.funcsSize, h.params,
    fun i b hi hne hb => h.keep i b (Nat.lt_of_lt_of_le hi hle) hne hb,
    h.curId.imp id (fun hh => Nat.le_trans hle hh)⟩

theorem rfl' (N : Nat) (s : BState) : SGrowsAt N s s :=
  ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, fun _ b hb => ⟨b, hb, rfl⟩,
    fun _ _ _ _ hb => hb, Or.inl rfl⟩

theorem trans {N : Nat} {s₁ s₂ s₃ : BState} (h₁ : SGrowsAt N s₁ s₂)
    (h₂ : SGrowsAt N s₂ s₃) : SGrowsAt N s₁ s₃ := by
  refine ⟨Nat.le_trans h₁.nextVal h₂.nextVal, Nat.le_trans h₁.size h₂.size,
    Nat.le_trans h₁.funcsSize h₂.funcsSize, ?_, ?_, ?_⟩
  · intro i b hb
    obtain ⟨b', hb', hp'⟩ := h₁.params i b hb
    obtain ⟨b'', hb'', hp''⟩ := h₂.params i b' hb'
    exact ⟨b'', hb'', hp''.trans hp'⟩
  · intro i b hi hne hb
    have hne2 : i ≠ s₂.fn.curId := by
      rcases h₁.curId with heq | hge
      · rw [heq]; exact hne
      · omega
    exact h₂.keep i b hi hne2 (h₁.keep i b hi hne hb)
  · rcases h₂.curId with heq | hge
    · rw [heq]; exact h₁.curId
    · exact Or.inr hge

/-- From an expression-level step. -/
theorem of_grows {N : Nat} {s s' : BState} (h : Grows s s') : SGrowsAt N s s' :=
  ⟨h.nextVal, by rw [h.blocks], by rw [h.funcs],
    fun i b hb => ⟨b, by rw [← h.blocks]; exact hb, rfl⟩,
    fun _ b _ _ hb => by rw [← h.blocks]; exact hb, Or.inl h.curId.symm⟩

/-- A step that changes nothing but the function table. -/
theorem of_funcsOnly {N : Nat} {s s' : BState} (hfn : s'.fn = s.fn)
    (hf : s.funcs.size ≤ s'.funcs.size) : SGrowsAt N s s' :=
  ⟨by rw [hfn], by rw [hfn], hf,
    fun i b hb => ⟨b, by rw [hfn]; exact hb, rfl⟩,
    fun _ b _ _ hb => by rw [hfn]; exact hb, Or.inl (by rw [hfn])⟩

theorem of_newBlock {N : Nat} {ps : List ValId} {s s' : BState} {bid : BlockId}
    (h : newBlock ps s = some (bid, s')) : SGrowsAt N s s' := by
  rw [M.newBlock_apply] at h
  obtain ⟨rfl, rfl⟩ := M.some_pair_inj h
  refine ⟨Nat.le_refl _, by simp, Nat.le_refl _, ?_, ?_, Or.inl rfl⟩
  · intro i b hb
    have hlt := lt_size_of_getElem? hb
    refine ⟨b, ?_, rfl⟩
    dsimp only
    rw [Array.getElem?_push, if_neg (by omega : ¬ i = s.fn.blocks.size)]
    exact hb
  · intro i b _ _ hb
    have hlt := lt_size_of_getElem? hb
    dsimp only
    rw [Array.getElem?_push, if_neg (by omega : ¬ i = s.fn.blocks.size)]
    exact hb

/-- The reserved block's id is the old block count: every `moveTo` target the
construction produces is at or beyond the fragment's base. -/
theorem newBlock_id {ps : List ValId} {s s' : BState} {bid : BlockId}
    (h : newBlock ps s = some (bid, s')) : bid = s.fn.blocks.size := by
  rw [M.newBlock_apply] at h
  exact (M.some_pair_inj h).1.symm

theorem of_sealCur {N : Nat} {t : Term} {s s' : BState} {u : Unit}
    (h : sealCur t s = some (u, s')) : SGrowsAt N s s' := by
  obtain ⟨b, hb, rfl⟩ := M.sealCur_inv h
  have hlt : s.fn.curId < s.fn.blocks.size := lt_size_of_getElem? hb
  refine ⟨Nat.le_refl _, by simp, Nat.le_refl _, ?_, ?_, Or.inl rfl⟩
  · intro i b' hb'
    by_cases hc : i = s.fn.curId
    · subst hc
      obtain rfl : b' = b := Option.some.inj (hb'.symm.trans hb)
      refine ⟨⟨b'.params, s.fn.cur.reverse, t⟩, ?_, rfl⟩
      dsimp only
      rw [Array.set!_eq_setIfInBounds,
        Array.getElem?_setIfInBounds_self_of_lt hlt]
    · refine ⟨b', ?_, rfl⟩
      dsimp only
      rw [Array.set!_eq_setIfInBounds,
        Array.getElem?_setIfInBounds_ne (Ne.symm hc)]
      exact hb'
  · intro i b' _ hne hb'
    dsimp only
    rw [Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds_ne (Ne.symm hne)]
    exact hb'

theorem of_moveTo {N : Nat} {bid : BlockId} {s s' : BState} {u : Unit}
    (hbid : N ≤ bid ∨ bid = s.fn.curId) (h : moveTo bid s = some (u, s')) :
    SGrowsAt N s s' := by
  rw [M.moveTo_apply] at h
  obtain ⟨rfl, rfl⟩ := M.some_pair_inj h
  exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _,
    fun i b hb => ⟨b, hb, rfl⟩, fun _ _ _ _ hb => hb, hbid.symm⟩

theorem of_allocFunc {N : Nat} {s s' : BState} {fid : FuncId}
    (h : allocFunc s = some (fid, s')) : SGrowsAt N s s' := by
  rw [M.allocFunc_apply] at h
  obtain ⟨rfl, rfl⟩ := M.some_pair_inj h
  exact of_funcsOnly rfl (by simp)

theorem of_fillFunc {N : Nat} {fid : FuncId} {g : Func} {s s' : BState}
    {u : Unit} (h : fillFunc fid g s = some (u, s')) : SGrowsAt N s s' := by
  obtain ⟨hlt, rfl⟩ := M.fillFunc_inv h
  exact of_funcsOnly rfl (by simp)

theorem of_liftO {N : Nat} {α : Type} {o : Option α} {a : α} {s s' : BState}
    (h : (liftO o : M α) s = some (a, s')) : SGrowsAt N s s' := by
  obtain ⟨-, rfl⟩ := M.liftO_inv h
  exact rfl' N _

theorem of_pure {N : Nat} {α : Type} {a b : α} {s s' : BState}
    (h : (pure a : M α) s = some (b, s')) : SGrowsAt N s s' := by
  obtain ⟨-, rfl⟩ := M.pure_inv h
  exact rfl' N _

theorem of_edgeArgs {N : Nat} {env : VMap} {xs : List Ident} {s s' : BState}
    {ids : List ValId} (h : edgeArgs env xs s = some (ids, s')) :
    SGrowsAt N s s' := of_liftO h

/-- **The `Completes` transfer.** The placement invariant travels *backwards*
along a fragment: if the finished function completes the state the fragment ends
in, it completes the state it started in. This is the payoff of `keep`/`curId`
— the block the fragment started on is the only pre-existing one it could have
sealed, and it is exempt from `Completes.sealed` at the input state. -/
theorem completes_of {f : Func} {s s' : BState} {joins : List BlockId}
    (h : SGrowsAt s.fn.blocks.size s s') (hc : Completes f s'.fn joins) :
    Completes f s.fn joins := by
  refine ⟨?_, ?_, Nat.le_trans h.size hc.size⟩
  · intro i b hprot hne hb
    have hlt : i < s.fn.blocks.size := lt_size_of_getElem? hb
    have hne2 : i ≠ s'.fn.curId := by
      rcases h.curId with heq | hge
      · rw [heq]; exact hne
      · omega
    exact hc.sealed i b hprot hne2 (h.keep i b hlt hne hb)
  · intro i b hb
    obtain ⟨b', hb', hp'⟩ := h.params i b hb
    obtain ⟨bf, hbf, hpf⟩ := hc.params i b' hb'
    exact ⟨bf, hbf, hpf.trans hp'⟩

end SGrowsAt

namespace ProtectedAt

theorem forward {joins : List BlockId} {s s' : BState}
    (hp : ProtectedAt joins s.fn)
    (hg : SGrowsAt s.fn.blocks.size s s') : ProtectedAt joins s'.fn := by
  refine ⟨fun i hi => Nat.lt_of_lt_of_le (hp.below i hi) hg.size, ?_⟩
  intro hc
  rcases hg.curId with heq | hge
  · exact hp.away (by simpa only [heq] using hc)
  · exact Nat.not_lt_of_ge hge (hp.below _ hc)

end ProtectedAt

namespace FGrows

theorem of_newBlock {ps : List ValId} {s s' : BState} {bid : BlockId}
    (h : newBlock ps s = some (bid, s')) : FGrows s s' :=
  (SGrowsAt.of_newBlock (N := 0) h).funcsSize

theorem of_moveTo {bid : BlockId} {s s' : BState} {u : Unit}
    (h : moveTo bid s = some (u, s')) : FGrows s s' :=
  (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) h).funcsSize

theorem of_sealCur {t : Term} {s s' : BState} {u : Unit}
    (h : sealCur t s = some (u, s')) : FGrows s s' :=
  (SGrowsAt.of_sealCur (N := 0) h).funcsSize

theorem of_liftO {α : Type} {o : Option α} {a : α} {s s' : BState}
    (h : (liftO o : M α) s = some (a, s')) : FGrows s s' :=
  (SGrowsAt.of_liftO (N := 0) h).funcsSize

theorem of_pure {α : Type} {a b : α} {s s' : BState}
    (h : (pure a : M α) s = some (b, s')) : FGrows s s' :=
  (SGrowsAt.of_pure (N := 0) h).funcsSize

theorem of_grows {s s' : BState} (h : Grows s s') : FGrows s s' :=
  (SGrowsAt.of_grows (N := 0) h).funcsSize

end FGrows

/-- Statement-class monotonicity at its natural base: the block count the
fragment starts with. -/
def SGrows (s s' : BState) : Prop := SGrowsAt s.fn.blocks.size s s'

namespace SGrows

theorem rfl' (s : BState) : SGrows s s := SGrowsAt.rfl' _ s

/-- Own-base monotonicity is transitive: the second fragment's guarantee is
weakened to the first one's base, which is legitimate because the block array
only grew. -/
theorem trans {s₀ s₁ s₂ : BState} (h₁ : SGrows s₀ s₁) (h₂ : SGrows s₁ s₂) :
    SGrows s₀ s₂ :=
  SGrowsAt.trans h₁ (h₂.mono h₁.size)

theorem of_grows {s s' : BState} (h : Grows s s') : SGrows s s' :=
  SGrowsAt.of_grows h

end SGrows

/-- `mapM` over allocating steps allocates. -/
theorem Grows.of_mapM {α : Type} {g : α → M ValId}
    (hg : ∀ (a : α) (s s' : BState) (v : ValId), g a s = some (v, s') → Grows s s') :
    ∀ (l : List α) (s s' : BState) (vs : List ValId),
      (l.mapM g) s = some (vs, s') → Grows s s' := by
  intro l
  induction l with
  | nil => intro s s' vs h; exact Grows.of_pure h
  | cons a l ih =>
    intro s s' vs h
    rw [List.mapM_cons] at h
    obtain ⟨v, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨vs', s₂, h2, h3⟩ := M.bind_inv h
    exact (hg a s s₁ v h1).trans ((ih s₁ s₂ vs' h2).trans (Grows.of_pure h3))

/-- The zero-initialising allocation `trStmt`/`trFunc` use for `let`-without-value
and for return variables. -/
theorem Grows.of_mapM_constZero {α : Type} {l : List α} {s s' : BState}
    {vs : List ValId}
    (h : (l.mapM (fun _ => do let v ← freshVal; emit (.const v 0); pure v)) s
        = some (vs, s')) : Grows s s' := by
  refine Grows.of_mapM ?_ l s s' vs h
  intro a s₀ s₁ v hv
  obtain ⟨w, s₂, h1, hv⟩ := M.bind_inv hv
  obtain ⟨u, s₃, h2, h3⟩ := M.bind_inv hv
  exact (Grows.of_freshVal h1).trans ((Grows.of_emit h2).trans (Grows.of_pure h3))

/-- The zero-initialising allocation, exactly: the ids are the next `|l|`, and
the emitted instruction block is their `const _ 0`s in order. -/
theorem constZero_apply (s : BState) :
    (do let v ← freshVal; emit (.const v 0); pure v) s
      = some (s.fn.nextVal, { s with fn := { s.fn with
          nextVal := s.fn.nextVal + 1,
          cur := Instr.const s.fn.nextVal 0 :: s.fn.cur } }) := rfl

theorem mapM_constZero_spec {α : Type} : ∀ (l : List α) (s : BState),
    (l.mapM (fun _ => do let v ← freshVal; emit (.const v 0); pure v)) s
      = some (List.range' s.fn.nextVal l.length,
          { s with fn := { s.fn with
              nextVal := s.fn.nextVal + l.length,
              cur := ((List.range' s.fn.nextVal l.length).map
                        (fun v => Instr.const v 0)).reverse ++ s.fn.cur } }) := by
  intro l
  induction l with
  | nil => intro s; rfl
  | cons a l ih =>
    intro s
    have hn : s.fn.nextVal + 1 + l.length = s.fn.nextVal + (l.length + 1) :=
      Nat.add_right_comm _ _ _
    rw [List.mapM_cons, M.bind_eq, constZero_apply]
    simp only [Option.bind_some]
    rw [M.bind_eq, ih]
    simp only [Option.bind_some, M.pure_apply, List.length_cons,
      List.range'_succ, List.map_cons, List.reverse_cons, hn]
    simp

/-- **Expression translation only allocates.** -/
theorem trExpr_grows : ∀ (e : Expr Op) (fenv : FMap) (env : VMap) (s s' : BState)
    (i : ValId), trExpr fenv env e s = some (i, s') → Grows s s' := by
  refine trExpr.induct
    (fun e => ∀ (fenv : FMap) (env : VMap) (s s' : BState) (i : ValId),
      trExpr fenv env e s = some (i, s') → Grows s s')
    (fun es => ∀ (fenv : FMap) (env : VMap) (s s' : BState) (ids : List ValId),
      trArgs fenv env es s = some (ids, s') → Grows s s')
    ?_ ?_ ?_ ?_ ?_ ?_
  · intro l fenv env s s' i h
    rw [trExpr] at h
    obtain ⟨v, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨u, s₂, h2, h3⟩ := M.bind_inv h
    exact (Grows.of_freshVal h1).trans ((Grows.of_emit h2).trans (Grows.of_pure h3))
  · intro x fenv env s s' i h
    rw [trExpr] at h
    exact Grows.of_liftO h
  · intro op args ih fenv env s s' i h
    rw [trExpr] at h
    obtain ⟨as, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨d, s₂, h2, h⟩ := M.bind_inv h
    obtain ⟨u, s₃, h3, h4⟩ := M.bind_inv h
    exact (ih fenv env s s₁ as h1).trans
      ((Grows.of_freshVal h2).trans ((Grows.of_emit h3).trans (Grows.of_pure h4)))
  · intro fn args ih fenv env s s' i h
    rw [trExpr] at h
    obtain ⟨as, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨fid, s₂, h2, h⟩ := M.bind_inv h
    obtain ⟨d, s₃, h3, h⟩ := M.bind_inv h
    obtain ⟨u, s₄, h4, h5⟩ := M.bind_inv h
    exact (ih fenv env s s₁ as h1).trans ((Grows.of_liftO h2).trans
      ((Grows.of_freshVal h3).trans ((Grows.of_emit h4).trans (Grows.of_pure h5))))
  · intro fenv env s s' ids h
    rw [trArgs] at h
    exact Grows.of_pure h
  · intro e rest ihrest ihe fenv env s s' ids h
    rw [trArgs] at h
    obtain ⟨restIds, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨i, s₂, h2, h3⟩ := M.bind_inv h
    exact (ihrest fenv env s s₁ restIds h1).trans
      ((ihe fenv env s₁ s₂ i h2).trans (Grows.of_pure h3))

/-- **Argument-list translation only allocates.** -/
theorem trArgs_grows : ∀ (es : List (Expr Op)) (fenv : FMap) (env : VMap)
    (s s' : BState) (ids : List ValId),
    trArgs fenv env es s = some (ids, s') → Grows s s' := by
  refine trArgs.induct
    (fun e => ∀ (fenv : FMap) (env : VMap) (s s' : BState) (i : ValId),
      trExpr fenv env e s = some (i, s') → Grows s s')
    (fun es => ∀ (fenv : FMap) (env : VMap) (s s' : BState) (ids : List ValId),
      trArgs fenv env es s = some (ids, s') → Grows s s')
    (fun l => trExpr_grows (.lit l)) (fun x => trExpr_grows (.var x))
    (fun op args _ => trExpr_grows (.builtin op args))
    (fun fn args _ => trExpr_grows (.call fn args)) ?_ ?_
  · intro fenv env s s' ids h
    rw [trArgs] at h
    exact Grows.of_pure h
  · intro e rest ihrest ihe fenv env s s' ids h
    rw [trArgs] at h
    obtain ⟨restIds, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨i, s₂, h2, h3⟩ := M.bind_inv h
    exact (ihrest fenv env s s₁ restIds h1).trans
      ((ihe fenv env s₁ s₂ i h2).trans (Grows.of_pure h3))

/-- `foldlM` over steps that only append to the function table. -/
theorem foldlM_funcsOnly {α β : Type} {g : β → α → M β}
    (hg : ∀ (b : β) (a : α) (s s' : BState) (b' : β),
      g b a s = some (b', s') → s'.fn = s.fn ∧ s.funcs.size ≤ s'.funcs.size) :
    ∀ (l : List α) (b : β) (s : BState) (b' : β) (s' : BState),
      (l.foldlM g b) s = some (b', s')
        → s'.fn = s.fn ∧ s.funcs.size ≤ s'.funcs.size := by
  intro l
  induction l with
  | nil =>
    intro b s b' s' h
    obtain ⟨-, rfl⟩ := M.pure_inv h
    exact ⟨rfl, Nat.le_refl _⟩
  | cons a l ih =>
    intro b s b' s' h
    rw [List.foldlM_cons] at h
    obtain ⟨c, s₁, h1, h2⟩ := M.bind_inv h
    obtain ⟨hfn1, hf1⟩ := hg b a s s₁ c h1
    obtain ⟨hfn2, hf2⟩ := ih c s₁ b' s' h2
    exact ⟨hfn2.trans hfn1, Nat.le_trans hf1 hf2⟩

/-- Reserving a scope's function slots touches only the function table. -/
theorem allocScope_funcsOnly {ss : List (Stmt Op)} {s s' : BState}
    {sc : List (Ident × FuncId)} (h : allocScope ss s = some (sc, s')) :
    s'.fn = s.fn ∧ s.funcs.size ≤ s'.funcs.size := by
  rw [allocScope] at h
  refine foldlM_funcsOnly ?_ ss [] s sc s' h
  intro b a s₀ s₁ b' hb
  cases a
  case funDef n ps rs body =>
    obtain ⟨fid, s₂, h1, h2⟩ := M.bind_inv hb
    rw [M.allocFunc_apply] at h1
    obtain ⟨rfl, rfl⟩ := M.some_pair_inj h1
    obtain ⟨-, rfl⟩ := M.pure_inv h2
    exact ⟨rfl, by simp⟩
  all_goals (obtain ⟨-, rfl⟩ := M.pure_inv hb; exact ⟨rfl, Nat.le_refl _⟩)

/-- `allocScope` appends reservations and therefore preserves the complete
pre-existing function-table prefix, including pending `none` entries. -/
theorem allocScope_fprefix {ss : List (Stmt Op)} {s s' : BState}
    {sc : List (Ident × FuncId)} (h : allocScope ss s = some (sc, s')) :
    FPrefix s.funcs.size s s' := by
  rw [allocScope] at h
  have step : ∀ (acc : List (Ident × FuncId)) (st : Stmt Op)
      (s₀ s₁ : BState) (acc' : List (Ident × FuncId)),
      (match st with
        | Stmt.funDef n _ _ _ => do
            let fid ← allocFunc
            pure (acc ++ [(n, fid)])
        | _ => pure acc) s₀ = some (acc', s₁) →
        FPrefix s₀.funcs.size s₀ s₁ ∧ FGrows s₀ s₁ := by
    intro acc st s₀ s₁ acc' hs
    cases st with
    | funDef n ps rs body =>
        obtain ⟨fid, t, ha, hp⟩ := M.bind_inv hs
        obtain ⟨-, rfl⟩ := M.pure_inv hp
        exact ⟨FPrefix.of_allocFunc (Nat.le_refl _) ha,
          (SGrowsAt.of_allocFunc (N := 0) ha).funcsSize⟩
    | block body | letDecl vars val | assign vars e | cond e body
    | forLoop init e post body | «break» | «continue» | leave
    | switch e cases dflt | exprStmt e =>
        obtain ⟨-, rfl⟩ := M.pure_inv hs
        exact ⟨FPrefix.rfl' _ _, FGrows.rfl' _⟩
  have fold : ∀ (l : List (Stmt Op)) (init : List (Ident × FuncId))
      (s₀ s₁ : BState) (out : List (Ident × FuncId)),
      (l.foldlM (init := init) fun acc (st : Stmt Op) =>
        match st with
        | Stmt.funDef n _ _ _ => do
            let fid ← allocFunc
            pure (acc ++ [(n, fid)])
        | _ => pure acc) s₀ = some (out, s₁) →
        FPrefix s₀.funcs.size s₀ s₁ := by
    intro l
    induction l with
    | nil =>
        intro init s₀ s₁ out hl
        obtain ⟨-, rfl⟩ := M.pure_inv hl
        exact FPrefix.rfl' _ _
    | cons st rest ih =>
        intro init s₀ s₁ out hl
        rw [List.foldlM_cons] at hl
        obtain ⟨acc, t, hst, hrest⟩ := M.bind_inv hl
        have hs := step init st s₀ t acc hst
        exact hs.1.trans ((ih acc t s₁ out hrest).mono hs.2)
  exact fold ss [] s s' sc h

/-- Every `funDef` translated by a statement walk must resolve to a slot at or
above `N`.  This is the side condition under which that walk frames the prefix
below `N`. -/
def FillAbove (N : Nat) (fenv : FMap) (ss : List (Stmt Op)) : Prop :=
  ∀ (n : Ident) (ps rs : List Ident) (body : List (Stmt Op)),
    Stmt.funDef n ps rs body ∈ ss →
    ∀ fid : FuncId, fenv.get n = some fid → N ≤ fid

/-- The scope allocated for `ss` covers every declaration in `ss`, and every
slot selected through that innermost scope is freshly appended after the
input table.  Duplicate names are harmless here: `FMap.get` may select the
first duplicate, but all duplicates satisfy the same lower bound. -/
theorem allocScope_fillAbove {ss : List (Stmt Op)} {s s' : BState}
    {scope : List (Ident × FuncId)}
    (h : allocScope ss s = some (scope, s')) (outer : FMap) :
    FillAbove s.funcs.size (scope :: outer) ss := by
  rw [allocScope] at h
  have fold : ∀ (l : List (Stmt Op)) (init : List (Ident × FuncId))
      (s₀ s₁ : BState) (out : List (Ident × FuncId)) (N : Nat),
      N ≤ s₀.funcs.size →
      (l.foldlM (init := init) fun acc (st : Stmt Op) =>
        match st with
        | Stmt.funDef n _ _ _ => do
            let fid ← allocFunc
            pure (acc ++ [(n, fid)])
        | _ => pure acc) s₀ = some (out, s₁) →
      (∀ p ∈ out, p ∈ init ∨ N ≤ p.2) ∧
      (∀ p ∈ init, p ∈ out) ∧
      (∀ (n : Ident) (ps rs : List Ident) (body : List (Stmt Op)),
        Stmt.funDef n ps rs body ∈ l → ∃ fid, (n, fid) ∈ out) := by
    intro l
    induction l with
    | nil =>
        intro baseAcc s₀ s₁ out N hN hl
        obtain ⟨rfl, rfl⟩ := M.pure_inv hl
        exact ⟨fun p hp => Or.inl hp, fun p hp => hp, by simp⟩
    | cons st rest ih =>
        intro baseAcc s₀ s₁ out N hN hl
        rw [List.foldlM_cons] at hl
        obtain ⟨acc, t, hst, hrest⟩ := M.bind_inv hl
        have nonfun
            (hnf : ∀ (n : Ident) (ps rs : List Ident) (body : List (Stmt Op)),
              Stmt.funDef n ps rs body ≠ st)
            (hpure : (pure baseAcc : M (List (Ident × FuncId))) s₀ =
              some (acc, t)) :
            (∀ p ∈ out, p ∈ baseAcc ∨ N ≤ p.2) ∧
            (∀ p ∈ baseAcc, p ∈ out) ∧
            (∀ (n : Ident) (ps rs : List Ident) (body : List (Stmt Op)),
              Stmt.funDef n ps rs body ∈ st :: rest →
                ∃ fid, (n, fid) ∈ out) := by
          obtain ⟨rfl, rfl⟩ := M.pure_inv hpure
          obtain ⟨hout, hkeep, hcov⟩ :=
            ih acc t s₁ out N hN hrest
          refine ⟨hout, hkeep, ?_⟩
          intro n ps rs body hm
          simp only [List.mem_cons] at hm
          exact hm.elim (fun heq => absurd heq (hnf n ps rs body))
            (hcov n ps rs body)
        cases st with
        | funDef n ps rs body =>
            obtain ⟨fid, u, ha, hp⟩ := M.bind_inv hst
            rw [M.allocFunc_apply] at ha
            obtain ⟨rfl, rfl⟩ := M.some_pair_inj ha
            obtain ⟨rfl, rfl⟩ := M.pure_inv hp
            have ht : N ≤ ({ s₀ with funcs := s₀.funcs.push none }).funcs.size := by
              simpa using Nat.le_trans hN (by simp : s₀.funcs.size ≤ s₀.funcs.size + 1)
            obtain ⟨hout, hkeep, hcov⟩ :=
              ih (baseAcc ++ [(n, s₀.funcs.size)])
                { s₀ with funcs := s₀.funcs.push none } s₁ out N ht hrest
            refine ⟨?_, ?_, ?_⟩
            · intro p hpout
              rcases hout p hpout with hpacc | hpge
              · rw [List.mem_append] at hpacc
                exact hpacc.elim Or.inl (fun hpone => by
                  obtain rfl := List.mem_singleton.mp hpone
                  right
                  exact hN)
              · exact Or.inr hpge
            · intro p hpinit
              exact hkeep p (List.mem_append_left _ hpinit)
            · intro n' ps' rs' body' hm
              simp only [List.mem_cons] at hm
              rcases hm with heq | hm
              · cases heq
                exact ⟨s₀.funcs.size,
                  hkeep _ (by simp)⟩
              · exact hcov n' ps' rs' body' hm
        | block body => exact nonfun (by intros; simp) hst
        | letDecl vars val => exact nonfun (by intros; simp) hst
        | assign vars e => exact nonfun (by intros; simp) hst
        | cond e body => exact nonfun (by intros; simp) hst
        | switch e cases dflt => exact nonfun (by intros; simp) hst
        | forLoop init e post body => exact nonfun (by intros; simp) hst
        | exprStmt e => exact nonfun (by intros; simp) hst
        | «break» => exact nonfun (by intros; simp) hst
        | «continue» => exact nonfun (by intros; simp) hst
        | leave => exact nonfun (by intros; simp) hst
  obtain ⟨habove, _hkeep, hcover⟩ := fold ss [] s s' scope s.funcs.size
    (Nat.le_refl _) h
  intro n ps rs body hmem fid hget
  obtain ⟨fid₀, hfid₀⟩ := hcover n ps rs body hmem
  unfold FMap.get at hget
  cases hfind : scope.find? (·.1 = n) with
  | none =>
      have hall := List.find?_eq_none.mp hfind (n, fid₀) hfid₀
      exfalso
      apply hall
      simp
  | some p =>
      have hp : p ∈ scope := List.mem_of_find?_eq_some hfind
      have hfid : p.2 = fid := by simpa [hfind] using hget
      rw [← hfid]
      exact (habove p hp).elim (by simp) id

theorem allocScope_sgrows {ss : List (Stmt Op)} {s s' : BState}
    {sc : List (Ident × FuncId)} (h : allocScope ss s = some (sc, s')) :
    SGrows s s' :=
  SGrowsAt.of_funcsOnly (allocScope_funcsOnly h).1 (allocScope_funcsOnly h).2

/-- **Statement-level right-hand sides only allocate** (`trExprN` is `trArgs`
plus one `emit` for a user call, and a single `trExpr` otherwise). -/
theorem trExprN_grows {fenv : FMap} {env : VMap} {n : Nat} {e : Expr Op}
    {s s' : BState} {ids : List ValId}
    (h : trExprN fenv env n e s = some (ids, s')) : Grows s s' := by
  cases e with
  | call fn args =>
    rw [trExprN] at h
    obtain ⟨as, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨fid, s₂, h2, h⟩ := M.bind_inv h
    obtain ⟨ds, s₃, h3, h⟩ := M.bind_inv h
    obtain ⟨u, s₄, h4, h5⟩ := M.bind_inv h
    exact (trArgs_grows args fenv env s s₁ as h1).trans ((Grows.of_liftO h2).trans
      ((Grows.of_mapM_freshVal h3).trans
        ((Grows.of_emit h4).trans (Grows.of_pure h5))))
  | lit l =>
    rw [trExprN] at h
    · obtain ⟨-, h⟩ := M.ite_reject_inv' h
      obtain ⟨v, s₁, h1, h2⟩ := M.bind_inv h
      exact (trExpr_grows (.lit l) fenv env s s₁ v h1).trans (Grows.of_pure h2)
    · intro fn' args' hc
      simp at hc
  | var x =>
    rw [trExprN] at h
    · obtain ⟨-, h⟩ := M.ite_reject_inv' h
      obtain ⟨v, s₁, h1, h2⟩ := M.bind_inv h
      exact (trExpr_grows (.var x) fenv env s s₁ v h1).trans (Grows.of_pure h2)
    · intro fn' args' hc
      simp at hc
  | builtin op args =>
    rw [trExprN] at h
    · obtain ⟨-, h⟩ := M.ite_reject_inv' h
      obtain ⟨v, s₁, h1, h2⟩ := M.bind_inv h
      exact (trExpr_grows (.builtin op args) fenv env s s₁ v h1).trans (Grows.of_pure h2)
    · intro fn' args' hc
      simp at hc

end YulEvmCompiler.SsaCfg
