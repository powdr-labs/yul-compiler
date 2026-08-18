import YulEvmCompiler.SsaCfg.Implementation.PassesSound.DveCert
import YulEvmCompiler.Optimizer.Core.Equiv
set_option warningAsError true

/-!
# YulEvmCompiler.SsaCfg.Implementation.PassesSound.ConstFoldCert

Pass 2's loop as a fold, and its static constant certificates.

`cfInstrStep`/`cfBlockStep` as pure folds, the terminator rewrite one
constructor at a time, the `ConstDef`/`CFMapSound` certificates, and
`constFold_spec`.
-/

namespace YulEvmCompiler.SsaCfg
open YulSemantics.EVM (U256 EvmState Op builtinWithExternal stepOp ExternalCalls
  ExternalCreates)
open YulSemantics (Outcome)

namespace Passes

/-! ### Pass 2's loop, as a fold -/

abbrev CFInner := MProd (Std.HashMap ValId U256) (List Instr)
abbrev CFOuter := MProd (Array Block) (Std.HashMap ValId U256)

/-- The instruction step of `constFold`'s inner loop. -/
def cfInstrStep (ins : Instr) (st : CFInner) : CFInner :=
  match ins with
  | .const d v => ⟨st.1.insert d v, .const d v :: st.2⟩
  | .op [d] yop args =>
    match (if pureOp yop then
            (match args.mapM (st.1[·]?) with
             | some vs => evalPure yop vs
             | none => none)
           else none) with
    | some v => ⟨st.1.insert d v, .const d v :: st.2⟩
    | none => ⟨st.1, .op [d] yop args :: st.2⟩
  | ins => ⟨st.1, ins :: st.2⟩

/-- The block step of `constFold`'s outer loop, with the inner loop already
expressed as a fold. -/
def cfTerm (b : Block) (m : Std.HashMap ValId U256) : Term :=
  match b.term with
  | .branch c t e =>
    match m[c]? with
    | some v => .jump (if v == 0 then e else t)
    | none => b.term
  | t => t

def cfBlockStep (b : Block) (st : CFOuter) : CFOuter :=
  let r := b.instrs.foldl (fun s i => cfInstrStep i s) ⟨st.2, []⟩
  ⟨st.1.push { b with instrs := r.2.reverse, term := cfTerm b r.1 }, r.1⟩

/-- **`constFold`'s loop, as a fold.** The `do`-block's mutable state is an
`MProd`, and both loop bodies are pure-`yield`, so the bridge applies twice:
once under the outer body's binder (for the instruction loop) and once at the
top level. -/
theorem constFold_blocks_eq (f : Func) :
    (constFold f).blocks = (f.blocks.toList.foldl (fun st b => cfBlockStep b st) ⟨#[], ∅⟩).1 := by
  unfold constFold
  dsimp only
  rw [Id.forIn_array_eq_foldl (g := cfBlockStep) (h := by
    intro b st
    dsimp only [cfBlockStep]
    rw [Id.forIn_eq_foldl (g := cfInstrStep) (h := by
      intro i s
      cases i with
      | const d v => rfl
      | op ds yop args =>
        cases ds with
        | nil => rfl
        | cons d rest => cases rest with
          | nil =>
            simp only [cfInstrStep]
            split <;> split <;> grind
          | cons e es => rfl
      | call ds fid args => rfl)]
    rfl)]
  rfl


/-- One instruction step conses a *replacement* with the same definitions and no
new uses. -/
theorem cfInstrStep_cons (i : Instr) (s : CFInner) :
    ∃ i', (cfInstrStep i s).2 = i' :: s.2 ∧ i'.defs = i.defs ∧ (∀ x ∈ i'.uses, x ∈ i.uses) := by
  cases i with
  | const d v => exact ⟨_, rfl, rfl, fun x hx => hx⟩
  | op ds yop args =>
    cases ds with
    | nil => exact ⟨_, rfl, rfl, fun x hx => hx⟩
    | cons d rest =>
      cases rest with
      | nil =>
        simp only [cfInstrStep]
        split
        · exact ⟨_, rfl, rfl, by simp [Instr.uses]⟩
        · exact ⟨_, rfl, rfl, fun x hx => hx⟩
      | cons e es => exact ⟨_, rfl, rfl, fun x hx => hx⟩
  | call ds fid args => exact ⟨_, rfl, rfl, fun x hx => hx⟩

/-- The instruction fold preserves definitions and never invents a use. -/
theorem cfInstr_fold (l : List Instr) (s : CFInner) :
    (∀ x, x ∈ (l.foldl (fun s i => cfInstrStep i s) s).2.flatMap Instr.defs ↔
        x ∈ s.2.flatMap Instr.defs ∨ x ∈ l.flatMap Instr.defs)
    ∧ (∀ x, x ∈ (l.foldl (fun s i => cfInstrStep i s) s).2.flatMap Instr.uses →
        x ∈ s.2.flatMap Instr.uses ∨ x ∈ l.flatMap Instr.uses) := by
  induction l generalizing s with
  | nil => simp
  | cons i is ih =>
    obtain ⟨i', hi', hdefs, huses⟩ := cfInstrStep_cons i s
    have hstep : (List.foldl (fun s i => cfInstrStep i s) s (i :: is))
        = List.foldl (fun s i => cfInstrStep i s) (cfInstrStep i s) is := rfl
    rw [hstep]
    obtain ⟨ihd, ihu⟩ := ih (cfInstrStep i s)
    constructor
    · intro x
      rw [ihd x, hi']
      simp only [List.flatMap_cons, List.mem_append, hdefs]
      tauto
    · intro x hx
      rcases ihu x hx with h | h
      · rw [hi'] at h
        simp only [List.flatMap_cons, List.mem_append] at h ⊢
        rcases h with h | h
        · exact Or.inr (Or.inl (huses x h))
        · exact Or.inl h
      · simp only [List.flatMap_cons, List.mem_append] at h ⊢
        exact Or.inr (Or.inr h)


/-- The relation `constFold` establishes between a source block and its rewrite;
exactly the hypothesis shape of `ToAsm.domCheck_of_shrinking`. -/
def CFRel (b b' : Block) : Prop :=
  (∀ x ∈ ToAsm.blockUses b', x ∈ ToAsm.blockUses b)
  ∧ (∀ x ∈ ToAsm.blockDefs b, x ∈ ToAsm.blockDefs b')
  ∧ (∀ e ∈ b'.term.edges, ∃ e0 ∈ b.term.edges, e0.target = e.target)

theorem mem_flatMap_reverse {α β} [BEq β] {l : List α} {f : α → List β} {x : β} :
    x ∈ l.reverse.flatMap f ↔ x ∈ l.flatMap f := by
  simp only [List.mem_flatMap, List.mem_reverse]

/-! ### The terminator rewrite, one constructor at a time -/

theorem cfTerm_jump (b : Block) (m : Std.HashMap ValId U256) {e : Edge} (hb : b.term = .jump e) :
    cfTerm b m = b.term := by simp only [cfTerm, hb]

theorem cfTerm_ret (b : Block) (m : Std.HashMap ValId U256) {vs : List ValId}
    (hb : b.term = .ret vs) : cfTerm b m = b.term := by simp only [cfTerm, hb]

theorem cfTerm_halt (b : Block) (m : Std.HashMap ValId U256) {yop : Op} {as : List ValId}
    (hb : b.term = .halt yop as) : cfTerm b m = b.term := by simp only [cfTerm, hb]

theorem cfTerm_branch (b : Block) (m : Std.HashMap ValId U256) {c : ValId} {t e : Edge}
    (hb : b.term = .branch c t e) :
    cfTerm b m = b.term ∨ cfTerm b m = .jump t ∨ cfTerm b m = .jump e := by
  simp only [cfTerm, hb]
  split
  · rename_i v _
    by_cases hv : (v == 0) = true
    · exact Or.inr (Or.inr (by rw [if_pos hv]))
    · exact Or.inr (Or.inl (by rw [if_neg hv]))
  · exact Or.inl rfl

/-- Constant folding either leaves a terminator alone or replaces a `branch` by a
`jump` along one of its own edges. -/
theorem cfTerm_cases (b : Block) (m : Std.HashMap ValId U256) :
    cfTerm b m = b.term ∨ ∃ e0 ∈ b.term.edges, cfTerm b m = .jump e0 := by
  rcases hb : b.term with e | ⟨c, t, e⟩ | vs | ⟨yop, as⟩
  · exact Or.inl ((cfTerm_jump b m hb).trans hb)
  · rcases cfTerm_branch b m hb with h | h | h
    · exact Or.inl (h.trans hb)
    · exact Or.inr ⟨t, by simp [Term.edges], h⟩
    · exact Or.inr ⟨e, by simp [Term.edges], h⟩
  · exact Or.inl ((cfTerm_ret b m hb).trans hb)
  · exact Or.inl ((cfTerm_halt b m hb).trans hb)

theorem cfTerm_uses (b : Block) (m : Std.HashMap ValId U256) {x : ValId}
    (hx : x ∈ (cfTerm b m).uses) : x ∈ b.term.uses := by
  rcases cfTerm_cases b m with h | ⟨e0, he0, h⟩
  · rwa [h] at hx
  · rw [h] at hx
    simp only [Term.uses] at hx
    rcases hb : b.term with e | ⟨c, t, e⟩ | vs | ⟨yop, as⟩ <;> rw [hb] at he0 <;>
      simp only [Term.edges, List.mem_cons] at he0 <;>
      simp only [Term.uses, List.mem_cons, List.mem_append] <;> grind

theorem cfTerm_edges (b : Block) (m : Std.HashMap ValId U256) {e : Edge}
    (he : e ∈ (cfTerm b m).edges) : ∃ e0 ∈ b.term.edges, e0.target = e.target := by
  rcases cfTerm_cases b m with h | ⟨e0, he0, h⟩
  · rw [h] at he; exact ⟨e, he, rfl⟩
  · rw [h] at he
    simp only [Term.edges, List.mem_singleton] at he
    exact ⟨e0, he0, by rw [he]⟩


/-! ### Pass 2's step-by-step correspondence -/

/-- The constant map after one folded instruction. -/
def cfInstrMap (i : Instr) (m : Std.HashMap ValId U256) : Std.HashMap ValId U256 :=
  match i with
  | .const d v => m.insert d v
  | .op [d] yop args =>
    match (if pureOp yop then
            (match args.mapM (m[·]?) with
             | some vs => evalPure yop vs
             | none => none)
           else none) with
    | some v => m.insert d v
    | none => m
  | _ => m

/-- The instruction `constFold` emits for one source instruction. -/
def cfInstrOut (i : Instr) (m : Std.HashMap ValId U256) : Instr :=
  match i with
  | .const d v => .const d v
  | .op [d] yop args =>
    match (if pureOp yop then
            (match args.mapM (m[·]?) with
             | some vs => evalPure yop vs
             | none => none)
           else none) with
    | some v => .const d v
    | none => .op [d] yop args
  | i => i

/-- **The step-by-step correspondence**: one fold step updates the map and
conses one rewritten instruction, both determined by the *incoming map alone*. -/
theorem cfInstrStep_eq (i : Instr) (m : Std.HashMap ValId U256) (acc : List Instr) :
    cfInstrStep i ⟨m, acc⟩ = ⟨cfInstrMap i m, cfInstrOut i m :: acc⟩ := by
  cases i with
  | const d v => rfl
  | op ds yop args =>
    cases ds with
    | nil => rfl
    | cons d rest =>
      cases rest with
      | nil =>
        simp only [cfInstrStep, cfInstrMap, cfInstrOut]
        split <;> grind
      | cons e es => rfl
  | call ds fid args => rfl

/-- The accumulator only ever grows at the front, so a fold started from `acc`
is the fold started from `[]`, appended. -/
theorem cfInstr_fold_split (l : List Instr) (m : Std.HashMap ValId U256) (acc : List Instr) :
    (l.foldl (fun s i => cfInstrStep i s) ⟨m, acc⟩).2
      = (l.foldl (fun s i => cfInstrStep i s) ⟨m, []⟩).2 ++ acc := by
  induction l generalizing m acc with
  | nil => rfl
  | cons i is ih =>
    have hstep : ∀ a : List Instr,
        (List.foldl (fun s i => cfInstrStep i s) ⟨m, a⟩ (i :: is))
          = List.foldl (fun s i => cfInstrStep i s) ⟨cfInstrMap i m, cfInstrOut i m :: a⟩ is := by
      intro a; rw [List.foldl_cons, cfInstrStep_eq]
    rw [hstep acc, hstep [], ih (cfInstrMap i m) (cfInstrOut i m :: acc),
      ih (cfInstrMap i m) [cfInstrOut i m]]
    simp

/-- The block's rewritten instruction list, one step at a time: the head is the
rewrite of the head under the incoming map, and the tail is the rewrite of the
tail under the *updated* map. This is the shape a simulation over `Exec`
consumes. -/
theorem cfInstr_fold_cons (i : Instr) (is : List Instr) (m : Std.HashMap ValId U256) :
    ((i :: is).foldl (fun s i => cfInstrStep i s) ⟨m, []⟩).2.reverse
      = cfInstrOut i m ::
        (is.foldl (fun s i => cfInstrStep i s) ⟨cfInstrMap i m, []⟩).2.reverse := by
  rw [List.foldl_cons, cfInstrStep_eq, cfInstr_fold_split]
  simp

/-- The map after a fold, step by step. -/
theorem cfInstr_foldMap_cons (i : Instr) (is : List Instr) (m : Std.HashMap ValId U256) :
    ((i :: is).foldl (fun s i => cfInstrStep i s) ⟨m, []⟩).1
      = (is.foldl (fun s i => cfInstrStep i s) ⟨cfInstrMap i m, []⟩).1 := by
  rw [List.foldl_cons, cfInstrStep_eq]
  have : ∀ (a : List Instr) (m' : Std.HashMap ValId U256),
      (is.foldl (fun s i => cfInstrStep i s) ⟨m', a⟩).1
        = (is.foldl (fun s i => cfInstrStep i s) ⟨m', []⟩).1 := by
    intro a m'
    induction is generalizing m' a with
    | nil => rfl
    | cons j js ih => rw [List.foldl_cons, List.foldl_cons, cfInstrStep_eq, cfInstrStep_eq,
        ih (cfInstrOut j m' :: a) (cfInstrMap j m'), ih [cfInstrOut j m'] (cfInstrMap j m')]
  exact this _ _

/-- Instruction definitions, flattened out of the blocks, form a sublist of
`allDefs`. -/
theorem instrDefs_sublist_allDefs (f : Func) :
    (f.blocks.toList.flatMap fun b => b.instrs.flatMap Instr.defs).Sublist f.allDefs := by
  rw [allDefs_eq]
  apply List.Sublist.trans _ (List.sublist_append_right f.params _)
  induction f.blocks.toList with
  | nil => exact .slnil
  | cons b bs ih =>
    simp only [List.flatMap_cons]
    exact List.Sublist.append (List.sublist_append_right b.params _) ih

/-- The instruction-definition traversal is duplicate-free in an SSA
function. -/
theorem instrDefs_nodup {f : Func} (h : f.allDefs.Nodup) :
    (f.blocks.toList.flatMap fun b => b.instrs.flatMap Instr.defs).Nodup :=
  h.sublist (instrDefs_sublist_allDefs f)

/-- The instruction accumulator does not affect the map component of a fold. -/
theorem cfInstr_foldMap_acc (l : List Instr) (m : Std.HashMap ValId U256)
    (acc : List Instr) :
    (l.foldl (fun s i => cfInstrStep i s) ⟨m, acc⟩).1 =
      (l.foldl (fun s i => cfInstrStep i s) ⟨m, []⟩).1 := by
  induction l generalizing m acc with
  | nil => rfl
  | cons i is ih =>
    rw [List.foldl_cons, List.foldl_cons, cfInstrStep_eq, cfInstrStep_eq,
      ih (cfInstrMap i m) (cfInstrOut i m :: acc),
      ih (cfInstrMap i m) [cfInstrOut i m]]

/-- The exact block and map produced from a given incoming constant map. -/
def cfBlockOut (b : Block) (m : Std.HashMap ValId U256) : Block :=
  let r := b.instrs.foldl (fun s i => cfInstrStep i s) ⟨m, []⟩
  { b with instrs := r.2.reverse, term := cfTerm b r.1 }

def cfBlockMap (b : Block) (m : Std.HashMap ValId U256) : Std.HashMap ValId U256 :=
  (b.instrs.foldl (fun s i => cfInstrStep i s) ⟨m, []⟩).1

theorem cfBlockStep_eq' (b : Block) (st : CFOuter) :
    cfBlockStep b st = ⟨st.1.push (cfBlockOut b st.2), cfBlockMap b st.2⟩ := by
  simp only [cfBlockStep, cfBlockOut, cfBlockMap]

/-- Later block steps preserve every already-emitted block. -/
theorem cfBlock_fold_get_old (l : List Block) (st : CFOuter) {i : Nat} {b : Block}
    (h : st.1[i]? = some b) :
    (l.foldl (fun st b => cfBlockStep b st) st).1[i]? = some b := by
  induction l generalizing st with
  | nil => exact h
  | cons x xs ih =>
    apply ih (st := cfBlockStep x st)
    rw [cfBlockStep_eq', Array.getElem?_push]
    have hi : i < st.1.size := (Array.getElem?_eq_some_iff.mp h).1
    have hne : i ≠ st.1.size := Nat.ne_of_lt hi
    rw [Array.getElem?_eq_getElem hi] at h
    simp only [hne, ↓reduceIte]
    rw [Array.getElem?_eq_getElem hi]
    exact h

/-! ### Static constant certificates -/

/-- A value forced by a definition in `f`.  The recursive `op` constructor is
well-founded in exactly the folder's instruction order: all argument
certificates already occur in the incoming map. -/
inductive ConstDef (f : Func) : ValId → U256 → Prop
  | const {b : Block} {d : ValId} {v : U256} :
      b ∈ f.blocks.toList → .const d v ∈ b.instrs → ConstDef f d v
  | op {b : Block} {d : ValId} {yop : Op} {as : List ValId} {vs : List U256} {v : U256} :
      b ∈ f.blocks.toList → .op [d] yop as ∈ b.instrs → pureOp yop = true →
      YulSemantics.Forall₂ (ConstDef f) as vs → evalPure yop vs = some v → ConstDef f d v

/-- Every certificate names an actual instruction destination. -/
theorem ConstDef.site {f : Func} {d : ValId} {v : U256} (h : ConstDef f d v) :
    ∃ b ∈ f.blocks.toList, ∃ i ∈ b.instrs, d ∈ i.defs := by
  cases h with
  | const hb hi => exact ⟨_, hb, _, hi, by simp [Instr.defs]⟩
  | op hb hi hp hvs he => exact ⟨_, hb, _, hi, by simp [Instr.defs]⟩

/-- A constant map is sound when each successful lookup carries a static
certificate. -/
def CFMapSound (f : Func) (m : Std.HashMap ValId U256) : Prop :=
  ∀ {d v}, m[d]? = some v → ConstDef f d v

theorem cfMapSound_empty (f : Func) : CFMapSound f ∅ := by
  intro d v h
  simp at h

/-- Successful `mapM` lookups in a sound map produce pointwise constant
certificates. -/
theorem cfMapSound_mapM {f : Func} {m : Std.HashMap ValId U256}
    (hm : CFMapSound f m) {as : List ValId} {vs : List U256}
    (h : as.mapM (m[·]?) = some vs) : YulSemantics.Forall₂ (ConstDef f) as vs := by
  induction as generalizing vs with
  | nil => simp at h; subst vs; exact .nil
  | cons a as ih =>
    simp only [List.mapM_cons] at h
    cases ha : m[a]? with
    | none => simp [ha] at h
    | some v =>
      cases ht : as.mapM (m[·]?) with
      | none => simp [ha, ht] at h
      | some ws =>
        simp [ha, ht] at h
        subst vs
        exact .cons (hm ha) (ih ht)

/-- One folder step extends a sound map when its instruction belongs to the
function. -/
theorem cfInstrMap_sound {f : Func} {b : Block} (hb : b ∈ f.blocks.toList)
    {i : Instr} (hi : i ∈ b.instrs) {m : Std.HashMap ValId U256}
    (hm : CFMapSound f m) : CFMapSound f (cfInstrMap i m) := by
  intro d v hd
  cases i with
  | const x w =>
    rw [cfInstrMap, Std.HashMap.getElem?_insert] at hd
    split at hd
    · rename_i hxd
      have : x = d := by simpa using hxd
      subst d
      simp at hd
      subst v
      exact .const hb hi
    · exact hm hd
  | op ds yop as =>
    cases ds with
    | nil => exact hm hd
    | cons x xs =>
      cases xs with
      | cons y ys => exact hm hd
      | nil =>
        simp only [cfInstrMap] at hd
        split at hd
        · rename_i w hfold
          rw [Std.HashMap.getElem?_insert] at hd
          split at hd
          · rename_i hxd
            have : x = d := by simpa using hxd
            subst d
            simp at hd
            subst v
            by_cases hp : pureOp yop = true
            · cases hs : as.mapM (m[·]?) with
              | none => simp [hp, hs] at hfold
              | some vs =>
                simp [hp, hs] at hfold
                exact .op hb hi hp (cfMapSound_mapM hm hs) hfold
            · have hp' : pureOp yop = false := Bool.eq_false_of_not_eq_true hp
              simp [hp'] at hfold
          · exact hm hd
        · exact hm hd
  | call ds fid as => exact hm hd

/-- Folding a list of instructions from a sound map preserves soundness. -/
theorem cfInstr_foldMap_sound {f : Func} {b : Block} (hb : b ∈ f.blocks.toList)
    {l : List Instr} (hl : ∀ i ∈ l, i ∈ b.instrs) {m : Std.HashMap ValId U256}
    (hm : CFMapSound f m) :
    CFMapSound f (l.foldl (fun s i => cfInstrStep i s) ⟨m, []⟩).1 := by
  induction l generalizing m with
  | nil => exact hm
  | cons i is ih =>
    rw [List.foldl_cons, cfInstrStep_eq]
    rw [cfInstr_foldMap_acc]
    apply ih (fun j hj => hl j (by simp [hj]))
    exact cfInstrMap_sound hb (hl i (by simp)) hm

theorem cfBlockMap_sound {f : Func} {b : Block} (hb : b ∈ f.blocks.toList)
    {m : Std.HashMap ValId U256} (hm : CFMapSound f m) :
    CFMapSound f (cfBlockMap b m) := by
  exact cfInstr_foldMap_sound hb (fun i hi => hi) hm

/-- Strengthening of `cfBlock_fold_get_old`: the incoming map at the selected
block is sound. -/
theorem cfBlock_fold_get_sound {f : Func} {l : List Block}
    (hl : ∀ b ∈ l, b ∈ f.blocks.toList) (st : CFOuter)
    (hst : CFMapSound f st.2) {j : Nat} {b : Block} (h : l[j]? = some b) :
    ∃ m, (l.foldl (fun st b => cfBlockStep b st) st).1[st.1.size + j]? =
        some (cfBlockOut b m) ∧ CFMapSound f m := by
  induction l generalizing st j with
  | nil => simp at h
  | cons x xs ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst x
      refine ⟨st.2, ?_, hst⟩
      rw [List.foldl_cons]
      apply cfBlock_fold_get_old
      rw [cfBlockStep_eq', Array.getElem?_push]
      simp
    | succ j =>
      simp only [List.getElem?_cons_succ] at h
      rw [List.foldl_cons]
      have hx : x ∈ f.blocks.toList := hl x (by simp)
      have hsound : CFMapSound f (cfBlockStep x st).2 := by
        rw [cfBlockStep_eq']
        exact cfBlockMap_sound hx hst
      obtain ⟨m, hm, hms⟩ := ih (fun y hy => hl y (by simp [hy]))
        (cfBlockStep x st) hsound h
      refine ⟨m, ?_, hms⟩
      rw [cfBlockStep_eq'] at hm ⊢
      simp only [Array.size_push] at hm
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hm

theorem constFold_block_get_sound {f : Func} {i : BlockId} {b : Block}
    (h : f.blocks[i]? = some b) :
    ∃ m, (constFold f).blocks[i]? = some (cfBlockOut b m) ∧ CFMapSound f m := by
  rw [constFold_blocks_eq]
  have hl : f.blocks.toList[i]? = some b := by simpa using h
  obtain ⟨m, hm, hms⟩ := cfBlock_fold_get_sound
    (f := f) (fun b hb => hb) ⟨#[], ∅⟩ (cfMapSound_empty f) hl
  exact ⟨m, by simpa using hm, hms⟩

/-! ### Pass 2's structural specification -/

/-- One block step pushes a `CFRel`-rewrite of the source block. -/
theorem cfBlockStep_spec (b : Block) (st : CFOuter) :
    ∃ b', (cfBlockStep b st).1 = st.1.push b' ∧ CFRel b b' := by
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · intro x hx
    rw [ToAsm.mem_blockUses] at hx ⊢
    rcases hx with hx | hx
    · refine Or.inl ?_
      have h := (cfInstr_fold b.instrs ⟨st.2, []⟩).2 x (by
        simpa [mem_flatMap_reverse] using hx)
      simpa using h
    · exact Or.inr (cfTerm_uses b _ hx)
  · intro x hx
    rw [ToAsm.mem_blockDefs] at hx ⊢
    rcases hx with hx | hx
    · exact Or.inl hx
    · refine Or.inr ?_
      have h := ((cfInstr_fold b.instrs ⟨st.2, []⟩).1 x).mpr (Or.inr hx)
      simpa [mem_flatMap_reverse] using h
  · intro e he
    exact cfTerm_edges b _ he

/-- The block fold builds the output array index by index. -/
theorem cfBlock_fold (l : List Block) (st : CFOuter) (i : Nat) (b' : Block)
    (h : (l.foldl (fun st b => cfBlockStep b st) st).1[i]? = some b') :
    st.1[i]? = some b' ∨
      ∃ (j : Nat) (b : Block), l[j]? = some b ∧ i = st.1.size + j ∧ CFRel b b' := by
  induction l generalizing st with
  | nil => exact Or.inl h
  | cons b bs ih =>
    obtain ⟨b'', hpush, hrel⟩ := cfBlockStep_spec b st
    have hstep : (List.foldl (fun st b => cfBlockStep b st) st (b :: bs))
        = List.foldl (fun st b => cfBlockStep b st) (cfBlockStep b st) bs := rfl
    rw [hstep] at h
    rcases ih (cfBlockStep b st) h with h1 | ⟨j, b0, hj, hij, hrel0⟩
    · rw [hpush, Array.getElem?_push] at h1
      split at h1
      · rename_i hi
        obtain rfl := Option.some.inj h1
        exact Or.inr ⟨0, b, rfl, by omega, hrel⟩
      · exact Or.inl h1
    · refine Or.inr ⟨j + 1, b0, by simpa using hj, ?_, hrel0⟩
      rw [hpush] at hij
      simp only [Array.size_push] at hij
      omega

/-- **Pass 2's structural specification**: every block of the output is a
`CFRel`-rewrite of the block at the same index of the input. -/
theorem constFold_spec (f : Func) (i : BlockId) (b' : Block)
    (h : (constFold f).blocks[i]? = some b') : ∃ b, f.blocks[i]? = some b ∧ CFRel b b' := by
  rw [constFold_blocks_eq] at h
  rcases cfBlock_fold f.blocks.toList ⟨#[], ∅⟩ i b' h with h1 | ⟨j, b, hj, hij, hrel⟩
  · simp at h1
  · refine ⟨b, ?_, hrel⟩
    have : i = j := by simpa using hij
    subst this
    simpa using hj

end Passes
end YulEvmCompiler.SsaCfg
