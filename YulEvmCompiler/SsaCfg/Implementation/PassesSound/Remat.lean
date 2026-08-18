import YulEvmCompiler.SsaCfg.Implementation.PassesSound.Pipeline
set_option warningAsError true

/-!
# YulEvmCompiler.SsaCfg.Implementation.PassesSound.Remat

Pass 6 soundness: constant rematerialization (`Passes.rematConsts`), and the
program-level `rematProg_sound'` consumed by `SsaCfg.rematProg_sound`.

The pass only ever *inserts* `const` definitions with ids beyond `maxIdOf f`,
immediately in front of the use they feed, and rewrites that one use.  The
simulation invariant is therefore purely local:

* the two register files **agree on every id `≤ maxIdOf f`** — every id the
  original function mentions — and the copies live strictly above that bound,
  so inserting them cannot disturb anything the original reads;
* a copy `const n v` is emitted for a use of `a` only when `a`'s (unique)
  definition site is `const a v`, so `ConstRegs` — pass 2's register
  consistency invariant, reused verbatim — gives `R a = some v`, which is
  exactly the value the copy binds to `n`.

Everything else is the pass's structural specification: the `forIn`-to-`foldl`
bridge, and the recursive model the simulation peels instruction by
instruction.
-/

namespace YulEvmCompiler.SsaCfg
open YulSemantics.EVM (U256 EvmState Op builtinWithExternal stepOp ExternalCalls
  ExternalCreates)
open YulSemantics (Outcome)
variable [model : ExternalModel]

namespace Passes

/-! ### The substitution the pass applies

`rematConsts` writes its substitution out by hand rather than through
`substV`; the two agree, but only propositionally (`Std.HashMap.getD` is not
`(·[·]?).getD` by `rfl`), so the model carries its own copy and
`rematV_eq_substV` bridges to the `Regs` plumbing. -/

def rematV (σ : Subst) (a : ValId) : ValId := (σ[a]?).getD a

def rematVs (σ : Subst) (as : List ValId) : List ValId := as.map (rematV σ)

def rematI (σ : Subst) : Instr → Instr
  | .const d v => .const d v
  | .op ds yop as => .op ds yop (rematVs σ as)
  | .call ds fid as => .call ds fid (rematVs σ as)

def rematT (σ : Subst) : Term → Term
  | .jump e => .jump { e with args := rematVs σ e.args }
  | .branch c t g =>
      .branch (rematV σ c) { t with args := rematVs σ t.args }
        { g with args := rematVs σ g.args }
  | .ret vs => .ret (rematVs σ vs)
  | .halt yop as => .halt yop (rematVs σ as)

omit model in
theorem rematV_eq_substV (σ : Subst) (a : ValId) : rematV σ a = substV σ a := by
  simp [rematV, substV, Std.HashMap.getD_eq_getD_getElem?]

omit model in
theorem rematVs_eq_substVs (σ : Subst) (as : List ValId) :
    rematVs σ as = substVs σ as := by
  simp [rematVs, substVs, rematV_eq_substV]

/-! ### The static maps -/

def rematConstStep (m : Std.HashMap ValId U256) (i : Instr) : Std.HashMap ValId U256 :=
  match i with
  | .const d v => m.insert d v
  | _ => m

/-- Every `const` destination of the function, with its value. -/
def rematConstMap (f : Func) : Std.HashMap ValId U256 :=
  f.blocks.toList.foldl (fun m b => b.instrs.foldl rematConstStep m) ∅

def rematLocalStep (m : Std.HashMap ValId Nat) (x : Instr × Nat) : Std.HashMap ValId Nat :=
  match x.1 with
  | .const d _ => m.insert d x.2
  | _ => m

/-- Where this block's own `const`s sit, for the distance heuristic. -/
def rematLocalAt (b : Block) : Std.HashMap ValId Nat :=
  b.instrs.zipIdx.foldl rematLocalStep ∅

/-! ### The pass's loops, as folds -/

abbrev RUState := MProd ValId (MProd (Array Instr) Subst)

/-- One step of the loop over an instruction's uses. -/
def rematUseStep (rv : ValId → Option U256) (a : ValId) (s : RUState) : RUState :=
  if (!s.2.2.contains a) = true then
    match rv a with
    | some v => ⟨s.1 + 1, s.2.1.push (.const s.1 v), s.2.2.insert a s.1⟩
    | _ => s
  else s

def rematCopiesFold (rv : ValId → Option U256) (as : List ValId) (s : RUState) : RUState :=
  as.foldl (fun s a => rematUseStep rv a s) s

abbrev RIState := MProd Nat (MProd ValId (Array Instr))

/-- One step of the loop over a block's instructions. -/
def rematInstrStep (rv : Nat → ValId → Option U256) (ins : Instr) (s : RIState) : RIState :=
  let r := rematCopiesFold (rv s.1) ins.uses ⟨s.2.1, s.2.2, ∅⟩
  ⟨s.1 + 1, r.1, r.2.1.push (rematI r.2.2 ins)⟩

def rematSeqFold (rv : Nat → ValId → Option U256) (is : List Instr) (s : RIState) : RIState :=
  is.foldl (fun s ins => rematInstrStep rv ins s) s

abbrev RBState := MProd (Array Block) ValId

def rematBlockStepR (rv : Nat → ValId → Option U256) (b : Block) (s : RBState) : RBState :=
  let r := rematSeqFold rv b.instrs ⟨0, s.2, #[]⟩
  let c := rematCopiesFold (rv b.instrs.length) b.term.uses ⟨r.2.1, r.2.2, ∅⟩
  ⟨s.1.push { b with instrs := c.2.1.toList, term := rematT c.2.2 b.term }, c.1⟩

def rematBlockStep (cm : Std.HashMap ValId U256) (b : Block) (s : RBState) : RBState :=
  rematBlockStepR (fun here a => rematValue cm (rematLocalAt b) here a) b s

def rematBlocksFold (cm : Std.HashMap ValId U256) (bs : List Block) (s : RBState) : RBState :=
  bs.foldl (fun s b => rematBlockStep cm b s) s

omit model in
/-- In `Id`, a monadic bind is an application; `dsimp` with this substitutes
the result of an already-converted loop into the rest of the `do` block, which
is what lets the *next* `forIn` be rewritten (`rw` cannot reach an occurrence
that mentions the bound result). -/
theorem Id.bind_apply {α β : Type} (x : Id α) (k : α → Id β) : (x >>= k) = k x := rfl

omit model in
/-- The body of the loop over one instruction's uses, with the `if`/`match`
pulled out of the `ForInStep`. -/
theorem rematUse_body (rv : ValId → Option U256) (a : ValId) (s : RUState) :
    (if (!s.2.2.contains a) = true then
       (match rv a with
        | some v =>
            pure (ForInStep.yield
              ⟨s.1 + 1, s.2.1.push (Instr.const s.1 v), s.2.2.insert a s.1⟩)
        | _ => pure (ForInStep.yield ⟨s.1, s.2.1, s.2.2⟩))
     else pure (ForInStep.yield ⟨s.1, s.2.1, s.2.2⟩) : Id (ForInStep RUState))
      = pure (ForInStep.yield (rematUseStep rv a s)) := by
  unfold rematUseStep
  split
  · split <;> rfl
  · rfl

omit model in
/-- The body of the loop over one instruction's uses, over the do-elaborator's
`Prod` state, with the `if`/`match` pulled out of the `ForInStep`. -/
theorem rematUse_body_prod (rv : ValId → Option U256) (a : ValId)
    (st : ValId × Array Instr × Subst) :
    (if (!st.2.2.contains a) = true then
       (match rv a with
        | some v => pure (ForInStep.yield
            (st.1 + 1, st.2.1.push (Instr.const st.1 v), st.2.2.insert a st.1))
        | _ => pure (ForInStep.yield (st.1, st.2.1, st.2.2)))
     else pure (ForInStep.yield (st.1, st.2.1, st.2.2))
      : Id (ForInStep (ValId × Array Instr × Subst)))
      = pure (ForInStep.yield
          ((rematUseStep rv a ⟨st.1, st.2.1, st.2.2⟩).1,
            (rematUseStep rv a ⟨st.1, st.2.1, st.2.2⟩).2.1,
            (rematUseStep rv a ⟨st.1, st.2.1, st.2.2⟩).2.2)) := by
  simp only [rematUseStep]
  split
  · split <;> rfl
  · rfl

omit model in
/-- The use-list fold over the do-elaborator's `Prod` state agrees with the
`RUState` fold, componentwise. -/
theorem rematUses_fold_prod (rv : ValId → Option U256) (as : List ValId)
    (next : ValId) (out : Array Instr) (sub : Subst) :
    as.foldl (fun (st : ValId × Array Instr × Subst) a =>
        ((rematUseStep rv a ⟨st.1, st.2.1, st.2.2⟩).1,
          (rematUseStep rv a ⟨st.1, st.2.1, st.2.2⟩).2.1,
          (rematUseStep rv a ⟨st.1, st.2.1, st.2.2⟩).2.2)) (next, out, sub) =
      ((rematCopiesFold rv as ⟨next, out, sub⟩).1,
        (rematCopiesFold rv as ⟨next, out, sub⟩).2.1,
        (rematCopiesFold rv as ⟨next, out, sub⟩).2.2) := by
  unfold rematCopiesFold
  induction as generalizing next out sub with
  | nil => rfl
  | cons a as ih =>
    rw [List.foldl_cons, List.foldl_cons]
    exact ih (rematUseStep rv a ⟨next, out, sub⟩).1
      (rematUseStep rv a ⟨next, out, sub⟩).2.1
      (rematUseStep rv a ⟨next, out, sub⟩).2.2

omit model in
/-- The instruction fold over the do-elaborator's (rotated) `Prod` state agrees
with the `RIState` fold, componentwise. -/
theorem rematSeq_fold_prod (rv : Nat → ValId → Option U256) (is : List Instr)
    (next : ValId) (here : Nat) (out : Array Instr) :
    is.foldl (fun (st : ValId × Nat × Array Instr) ins =>
        ((rematInstrStep rv ins ⟨st.2.1, st.1, st.2.2⟩).2.1,
          (rematInstrStep rv ins ⟨st.2.1, st.1, st.2.2⟩).1,
          (rematInstrStep rv ins ⟨st.2.1, st.1, st.2.2⟩).2.2)) (next, here, out) =
      ((rematSeqFold rv is ⟨here, next, out⟩).2.1,
        (rematSeqFold rv is ⟨here, next, out⟩).1,
        (rematSeqFold rv is ⟨here, next, out⟩).2.2) := by
  unfold rematSeqFold
  induction is generalizing next here out with
  | nil => rfl
  | cons i is ih =>
    rw [List.foldl_cons, List.foldl_cons]
    exact ih (rematInstrStep rv i ⟨here, next, out⟩).2.1
      (rematInstrStep rv i ⟨here, next, out⟩).1
      (rematInstrStep rv i ⟨here, next, out⟩).2.2

omit model in
/-- The pass's nested `for` loops, as folds. -/
theorem rematConsts_eq_fold (f : Func) :
    rematConsts f =
      if (rematConstMap f).isEmpty then f
      else { f with
        blocks := (rematBlocksFold (rematConstMap f) f.blocks.toList ⟨#[], maxIdOf f + 1⟩).1 } := by
  unfold rematConsts
  dsimp only
  rw [Id.forIn_array_eq_foldl (g := fun b m => b.instrs.foldl rematConstStep m) (h := by
    intro b m
    rw [Id.forIn_eq_foldl (g := fun i m => rematConstStep m i) (h := by
      intro i m
      cases i <;> rfl)]
    rfl)]
  dsimp only [Id.bind_apply]
  rw [Id.forIn_array_eq_foldl
    (g := fun b (st : ValId × Array Block) =>
      ((rematBlockStep (rematConstMap f) b ⟨st.2, st.1⟩).2,
        (rematBlockStep (rematConstMap f) b ⟨st.2, st.1⟩).1)) (h := by
    intro b s
    rw [Id.forIn_eq_foldl (g := fun x m => rematLocalStep m x) (h := by
      rintro ⟨i, k⟩ m
      cases i <;> rfl)]
    rw [Id.forIn_eq_foldl
      (g := fun ins (st : ValId × Nat × Array Instr) =>
        ((rematInstrStep (fun here a =>
            rematValue (rematConstMap f) (rematLocalAt b) here a) ins
              ⟨st.2.1, st.1, st.2.2⟩).2.1,
          (rematInstrStep (fun here a =>
            rematValue (rematConstMap f) (rematLocalAt b) here a) ins
              ⟨st.2.1, st.1, st.2.2⟩).1,
          (rematInstrStep (fun here a =>
            rematValue (rematConstMap f) (rematLocalAt b) here a) ins
              ⟨st.2.1, st.1, st.2.2⟩).2.2)) (h := by
      intro ins s
      cases ins with
      | const d v => rfl
      | op ds yop as =>
        rw [Id.forIn_eq_foldl
          (g := fun a (st : ValId × Array Instr × Subst) =>
            ((rematUseStep (fun a' =>
                rematValue (rematConstMap f) (rematLocalAt b) s.2.1 a') a
                  ⟨st.1, st.2.1, st.2.2⟩).1,
              (rematUseStep (fun a' =>
                rematValue (rematConstMap f) (rematLocalAt b) s.2.1 a') a
                  ⟨st.1, st.2.1, st.2.2⟩).2.1,
              (rematUseStep (fun a' =>
                rematValue (rematConstMap f) (rematLocalAt b) s.2.1 a') a
                  ⟨st.1, st.2.1, st.2.2⟩).2.2)) (h := by
          intro a st
          exact rematUse_body_prod _ a st)]
        rw [rematUses_fold_prod]
        rfl
      | call ds fid as =>
        rw [Id.forIn_eq_foldl
          (g := fun a (st : ValId × Array Instr × Subst) =>
            ((rematUseStep (fun a' =>
                rematValue (rematConstMap f) (rematLocalAt b) s.2.1 a') a
                  ⟨st.1, st.2.1, st.2.2⟩).1,
              (rematUseStep (fun a' =>
                rematValue (rematConstMap f) (rematLocalAt b) s.2.1 a') a
                  ⟨st.1, st.2.1, st.2.2⟩).2.1,
              (rematUseStep (fun a' =>
                rematValue (rematConstMap f) (rematLocalAt b) s.2.1 a') a
                  ⟨st.1, st.2.1, st.2.2⟩).2.2)) (h := by
          intro a st
          exact rematUse_body_prod _ a st)]
        rw [rematUses_fold_prod]
        rfl)]
    rw [rematSeq_fold_prod]
    rw [Id.forIn_eq_foldl
      (g := fun a (st : ValId × Array Instr × Subst) =>
        ((rematUseStep (fun a' =>
            rematValue (rematConstMap f) (rematLocalAt b) b.instrs.length a') a
              ⟨st.1, st.2.1, st.2.2⟩).1,
          (rematUseStep (fun a' =>
            rematValue (rematConstMap f) (rematLocalAt b) b.instrs.length a') a
              ⟨st.1, st.2.1, st.2.2⟩).2.1,
          (rematUseStep (fun a' =>
            rematValue (rematConstMap f) (rematLocalAt b) b.instrs.length a') a
              ⟨st.1, st.2.1, st.2.2⟩).2.2)) (h := by
      intro a st
      exact rematUse_body_prod _ a st)]
    rw [rematUses_fold_prod]
    rfl)]
  rw [foldl_prodSwap]
  rfl


/-! ### The recursive model

The folds above run left to right over lists, which is the order the execution
simulation peels them in, but they carry their output in an accumulator.  The
recursive presentations below produce the *suffix* each fold appends, which is
exactly the shape `Exec` induction needs. -/

/-- The copies inserted for one use list, the counter left over, and the
substitution to apply. -/
def rematCopies (rv : ValId → Option U256) :
    List ValId → ValId → Subst → List Instr × ValId × Subst
  | [], next, sub => ([], next, sub)
  | a :: as, next, sub =>
    if sub.contains a then rematCopies rv as next sub
    else
      match rv a with
      | some v =>
        let r := rematCopies rv as (next + 1) (sub.insert a next)
        (Instr.const next v :: r.1, r.2)
      | none => rematCopies rv as next sub

omit model in
theorem rematCopiesFold_eq (rv : ValId → Option U256) :
    ∀ (as : List ValId) (next : ValId) (out : Array Instr) (sub : Subst),
      (rematCopiesFold rv as ⟨next, out, sub⟩).1 = (rematCopies rv as next sub).2.1
      ∧ (rematCopiesFold rv as ⟨next, out, sub⟩).2.1.toList
          = out.toList ++ (rematCopies rv as next sub).1
      ∧ (rematCopiesFold rv as ⟨next, out, sub⟩).2.2 = (rematCopies rv as next sub).2.2 := by
  intro as
  induction as with
  | nil => intro next out sub; exact ⟨rfl, by simp [rematCopiesFold, rematCopies], rfl⟩
  | cons a as ih =>
    intro next out sub
    have hstep : rematCopiesFold rv (a :: as) ⟨next, out, sub⟩
        = rematCopiesFold rv as (rematUseStep rv a ⟨next, out, sub⟩) := rfl
    rw [hstep, rematCopies]
    by_cases hc : sub.contains a = true
    · have : rematUseStep rv a ⟨next, out, sub⟩ = ⟨next, out, sub⟩ := by
        simp [rematUseStep, hc]
      rw [this, if_pos hc]
      exact ih next out sub
    · rw [if_neg hc]
      cases hv : rv a with
      | none =>
        have : rematUseStep rv a ⟨next, out, sub⟩ = ⟨next, out, sub⟩ := by
          simp [rematUseStep, hc, hv]
        rw [this]
        exact ih next out sub
      | some v =>
        have hu : rematUseStep rv a ⟨next, out, sub⟩
            = ⟨next + 1, out.push (Instr.const next v), sub.insert a next⟩ := by
          simp [rematUseStep, hc, hv]
        rw [hu]
        obtain ⟨h1, h2, h3⟩ := ih (next + 1) (out.push (Instr.const next v)) (sub.insert a next)
        exact ⟨h1, by rw [h2]; simp, h3⟩

/-- The rewritten instruction list for a suffix of a block, starting at index
`here` with fresh counter `next`. -/
def rematSeq (rv : Nat → ValId → Option U256) :
    List Instr → Nat → ValId → List Instr × ValId
  | [], _, next => ([], next)
  | ins :: is, here, next =>
    let c := rematCopies (rv here) ins.uses next ∅
    let r := rematSeq rv is (here + 1) c.2.1
    (c.1 ++ rematI c.2.2 ins :: r.1, r.2)

omit model in
theorem rematSeqFold_eq (rv : Nat → ValId → Option U256) :
    ∀ (is : List Instr) (here : Nat) (next : ValId) (out : Array Instr),
      (rematSeqFold rv is ⟨here, next, out⟩).2.1 = (rematSeq rv is here next).2
      ∧ (rematSeqFold rv is ⟨here, next, out⟩).2.2.toList
          = out.toList ++ (rematSeq rv is here next).1 := by
  intro is
  induction is with
  | nil => intro here next out; exact ⟨rfl, by simp [rematSeqFold, rematSeq]⟩
  | cons ins is ih =>
    intro here next out
    have hstep : rematSeqFold rv (ins :: is) ⟨here, next, out⟩
        = rematSeqFold rv is (rematInstrStep rv ins ⟨here, next, out⟩) := rfl
    obtain ⟨h1, h2, h3⟩ := rematCopiesFold_eq (rv here) ins.uses next out ∅
    have hu : rematInstrStep rv ins ⟨here, next, out⟩
        = ⟨here + 1, (rematCopies (rv here) ins.uses next ∅).2.1,
            ((rematCopiesFold (rv here) ins.uses ⟨next, out, ∅⟩).2.1).push
              (rematI (rematCopies (rv here) ins.uses next ∅).2.2 ins)⟩ := by
      simp only [rematInstrStep, h1, h3]
    rw [hstep, hu, rematSeq]
    obtain ⟨k1, k2⟩ := ih (here + 1) (rematCopies (rv here) ins.uses next ∅).2.1
      (((rematCopiesFold (rv here) ins.uses ⟨next, out, ∅⟩).2.1).push
        (rematI (rematCopies (rv here) ins.uses next ∅).2.2 ins))
    refine ⟨k1, ?_⟩
    rw [k2]
    simp [h2]

/-- One rewritten block, and the counter left over. -/
def rematBlockOutR (rv : Nat → ValId → Option U256) (b : Block) (next : ValId) :
    Block × ValId :=
  let r := rematSeq rv b.instrs 0 next
  let c := rematCopies (rv b.instrs.length) b.term.uses r.2 ∅
  ({ b with instrs := r.1 ++ c.1, term := rematT c.2.2 b.term }, c.2.1)

def rematBlockOut (cm : Std.HashMap ValId U256) (b : Block) (next : ValId) : Block × ValId :=
  rematBlockOutR (fun here a => rematValue cm (rematLocalAt b) here a) b next

omit model in
theorem rematBlockStepR_eq (rv : Nat → ValId → Option U256) (b : Block)
    (acc : Array Block) (next : ValId) :
    rematBlockStepR rv b ⟨acc, next⟩
      = ⟨acc.push (rematBlockOutR rv b next).1, (rematBlockOutR rv b next).2⟩ := by
  obtain ⟨h1, h2⟩ := rematSeqFold_eq rv b.instrs 0 next #[]
  obtain ⟨k1, k2, k3⟩ := rematCopiesFold_eq (rv b.instrs.length) b.term.uses
    (rematSeqFold rv b.instrs ⟨0, next, #[]⟩).2.1
    (rematSeqFold rv b.instrs ⟨0, next, #[]⟩).2.2 ∅
  rw [h1] at k1 k2 k3
  simp only [rematBlockStepR, rematBlockOutR, h1, k1, k2, k3, h2]
  simp

omit model in
theorem rematBlockStep_eq (cm : Std.HashMap ValId U256) (b : Block)
    (acc : Array Block) (next : ValId) :
    rematBlockStep cm b ⟨acc, next⟩
      = ⟨acc.push (rematBlockOut cm b next).1, (rematBlockOut cm b next).2⟩ :=
  rematBlockStepR_eq _ b acc next

def rematBlocksOut (cm : Std.HashMap ValId U256) :
    List Block → ValId → List Block × ValId
  | [], next => ([], next)
  | b :: bs, next =>
    let r := rematBlockOut cm b next
    let rs := rematBlocksOut cm bs r.2
    (r.1 :: rs.1, rs.2)

omit model in
theorem rematBlocksFold_eq (cm : Std.HashMap ValId U256) :
    ∀ (bs : List Block) (acc : Array Block) (next : ValId),
      (rematBlocksFold cm bs ⟨acc, next⟩).1.toList
          = acc.toList ++ (rematBlocksOut cm bs next).1
      ∧ (rematBlocksFold cm bs ⟨acc, next⟩).2 = (rematBlocksOut cm bs next).2 := by
  intro bs
  induction bs with
  | nil => intro acc next; exact ⟨by simp [rematBlocksFold, rematBlocksOut], rfl⟩
  | cons b bs ih =>
    intro acc next
    have hstep : rematBlocksFold cm (b :: bs) ⟨acc, next⟩
        = rematBlocksFold cm bs (rematBlockStep cm b ⟨acc, next⟩) := rfl
    rw [hstep, rematBlockStep_eq, rematBlocksOut]
    obtain ⟨h1, h2⟩ := ih (acc.push (rematBlockOut cm b next).1) (rematBlockOut cm b next).2
    exact ⟨by rw [h1]; simp, h2⟩

omit model in
/-- `rematConsts`, fully unfolded to its recursive model. -/
theorem rematConsts_eq (f : Func) :
    rematConsts f =
      if (rematConstMap f).isEmpty then f
      else { f with
        blocks := (rematBlocksOut (rematConstMap f) f.blocks.toList (maxIdOf f + 1)).1.toArray } := by
  rw [rematConsts_eq_fold]
  split
  · rfl
  · obtain ⟨h1, -⟩ := rematBlocksFold_eq (rematConstMap f) f.blocks.toList #[] (maxIdOf f + 1)
    simp only [List.nil_append] at h1
    have : (rematBlocksFold (rematConstMap f) f.blocks.toList ⟨#[], maxIdOf f + 1⟩).1
        = (rematBlocksOut (rematConstMap f) f.blocks.toList (maxIdOf f + 1)).1.toArray := by
      apply Array.ext'
      rw [h1]
    rw [this]


/-! ### Freshness: the counter only grows, and starts above every id in `f` -/

omit model in
theorem rematCopies_next_le (rv : ValId → Option U256) :
    ∀ (as : List ValId) (next : ValId) (sub : Subst),
      next ≤ (rematCopies rv as next sub).2.1 := by
  intro as
  induction as with
  | nil => intro next sub; exact Nat.le_refl _
  | cons a as ih =>
    intro next sub
    rw [rematCopies]
    split
    · exact ih next sub
    · split
      · exact Nat.le_trans (Nat.le_succ next) (ih (next + 1) (sub.insert a next))
      · exact ih next sub

omit model in
theorem rematSeq_next_le (rv : Nat → ValId → Option U256) :
    ∀ (is : List Instr) (here : Nat) (next : ValId), next ≤ (rematSeq rv is here next).2 := by
  intro is
  induction is with
  | nil => intro here next; exact Nat.le_refl _
  | cons ins is ih =>
    intro here next
    rw [rematSeq]
    exact Nat.le_trans (rematCopies_next_le _ ins.uses next ∅)
      (ih (here + 1) (rematCopies (rv here) ins.uses next ∅).2.1)

omit model in
theorem rematBlockOutR_next_le (rv : Nat → ValId → Option U256) (b : Block) (next : ValId) :
    next ≤ (rematBlockOutR rv b next).2 :=
  Nat.le_trans (rematSeq_next_le rv b.instrs 0 next)
    (rematCopies_next_le _ b.term.uses (rematSeq rv b.instrs 0 next).2 ∅)

omit model in
theorem rematBlockOut_next_le (cm : Std.HashMap ValId U256) (b : Block) (next : ValId) :
    next ≤ (rematBlockOut cm b next).2 := rematBlockOutR_next_le _ b next

omit model in
theorem rematBlocksOut_length (cm : Std.HashMap ValId U256) :
    ∀ (bs : List Block) (next : ValId), (rematBlocksOut cm bs next).1.length = bs.length := by
  intro bs
  induction bs with
  | nil => intro next; rfl
  | cons b bs ih => intro next; simp [rematBlocksOut, ih]

omit model in
/-- Every rewritten block is the rewrite of the block at the same index, from
*some* counter value at or above the one the whole pass started with. -/
theorem rematBlocksOut_get (cm : Std.HashMap ValId U256) :
    ∀ (bs : List Block) (next : ValId) (j : Nat) (b : Block), bs[j]? = some b →
      ∃ m, next ≤ m ∧ (rematBlocksOut cm bs next).1[j]? = some (rematBlockOut cm b m).1 := by
  intro bs
  induction bs with
  | nil => intro next j b hb; simp at hb
  | cons b0 bs ih =>
    intro next j b hb
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hb
      subst b0
      exact ⟨next, Nat.le_refl _, rfl⟩
    | succ j =>
      simp only [List.getElem?_cons_succ] at hb
      obtain ⟨m, hm, hget⟩ := ih (rematBlockOut cm b0 next).2 j b hb
      exact ⟨m, Nat.le_trans (rematBlockOut_next_le cm b0 next) hm, by
        simpa [rematBlocksOut] using hget⟩

/-! ### `maxIdOf` bounds every id the function mentions -/

omit model in
theorem foldl_max_le (acc : Nat) (vs : List ValId) : acc ≤ vs.foldl Nat.max acc := by
  induction vs generalizing acc with
  | nil => exact Nat.le_refl _
  | cons v vs ih => exact Nat.le_trans (Nat.le_max_left acc v) (ih (Nat.max acc v))

omit model in
theorem foldl_max_mono {a b : Nat} (h : a ≤ b) (vs : List ValId) :
    vs.foldl Nat.max a ≤ vs.foldl Nat.max b := by
  induction vs generalizing a b with
  | nil => exact h
  | cons v vs ih => exact ih (max_le_max h (Nat.le_refl v))

omit model in
theorem le_foldl_max {x acc : Nat} {vs : List ValId} (h : x ∈ vs) :
    x ≤ vs.foldl Nat.max acc := by
  induction vs generalizing acc with
  | nil => simp at h
  | cons v vs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_trans (Nat.le_max_right acc x) (foldl_max_le _ vs)
    · exact ih h

def mxInstr (acc : Nat) (i : Instr) : Nat := i.uses.foldl Nat.max (i.defs.foldl Nat.max acc)

def mxBlock (acc : Nat) (b : Block) : Nat :=
  b.term.uses.foldl Nat.max (b.params.foldl Nat.max (b.instrs.foldl mxInstr acc))

omit model in
theorem mxInstr_le (acc : Nat) (i : Instr) : acc ≤ mxInstr acc i :=
  Nat.le_trans (foldl_max_le acc i.defs) (foldl_max_le _ i.uses)

omit model in
theorem mxInstr_mono {a b : Nat} (h : a ≤ b) (i : Instr) : mxInstr a i ≤ mxInstr b i :=
  foldl_max_mono (foldl_max_mono h i.defs) i.uses

omit model in
theorem foldl_mxInstr_le (acc : Nat) (is : List Instr) : acc ≤ is.foldl mxInstr acc := by
  induction is generalizing acc with
  | nil => exact Nat.le_refl _
  | cons i is ih => exact Nat.le_trans (mxInstr_le acc i) (ih (mxInstr acc i))

omit model in
theorem foldl_mxInstr_mono {a b : Nat} (h : a ≤ b) (is : List Instr) :
    is.foldl mxInstr a ≤ is.foldl mxInstr b := by
  induction is generalizing a b with
  | nil => exact h
  | cons i is ih => exact ih (mxInstr_mono h i)

omit model in
theorem le_foldl_mxInstr {acc : Nat} {i : Instr} {is : List Instr} (h : i ∈ is) :
    mxInstr acc i ≤ is.foldl mxInstr acc := by
  induction is generalizing acc with
  | nil => simp at h
  | cons j is ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact foldl_mxInstr_le _ is
    · exact Nat.le_trans (mxInstr_mono (mxInstr_le acc j) i) (ih h)

omit model in
theorem mxBlock_le (acc : Nat) (b : Block) : acc ≤ mxBlock acc b :=
  Nat.le_trans (foldl_mxInstr_le acc b.instrs)
    (Nat.le_trans (foldl_max_le _ b.params) (foldl_max_le _ b.term.uses))

omit model in
theorem mxBlock_mono {a b : Nat} (h : a ≤ b) (bl : Block) : mxBlock a bl ≤ mxBlock b bl :=
  foldl_max_mono (foldl_max_mono (foldl_mxInstr_mono h bl.instrs) bl.params) bl.term.uses

omit model in
theorem foldl_mxBlock_le (acc : Nat) (bs : List Block) : acc ≤ bs.foldl mxBlock acc := by
  induction bs generalizing acc with
  | nil => exact Nat.le_refl _
  | cons b bs ih => exact Nat.le_trans (mxBlock_le acc b) (ih (mxBlock acc b))

omit model in
theorem le_foldl_mxBlock {acc : Nat} {b : Block} {bs : List Block} (h : b ∈ bs) :
    mxBlock acc b ≤ bs.foldl mxBlock acc := by
  induction bs generalizing acc with
  | nil => simp at h
  | cons c bs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact foldl_mxBlock_le _ bs
    · exact Nat.le_trans (mxBlock_mono (mxBlock_le acc c) b) (ih h)

omit model in
theorem maxIdOf_eq (f : Func) :
    maxIdOf f = f.blocks.toList.foldl mxBlock (f.params.foldl Nat.max 0) := by
  unfold maxIdOf
  rw [← Array.foldl_toList]
  rfl

omit model in
theorem mxBlock_le_maxIdOf {f : Func} {b : Block} (hb : b ∈ f.blocks.toList) :
    mxBlock (f.params.foldl Nat.max 0) b ≤ maxIdOf f := by
  rw [maxIdOf_eq]
  exact le_foldl_mxBlock hb

omit model in
/-- Every value read by an instruction of `f` is at most `maxIdOf f`. -/
theorem le_maxIdOf_instr_use {f : Func} {b : Block} (hb : b ∈ f.blocks.toList)
    {i : Instr} (hi : i ∈ b.instrs) {x : ValId} (hx : x ∈ i.uses) : x ≤ maxIdOf f := by
  refine Nat.le_trans ?_ (mxBlock_le_maxIdOf hb)
  refine Nat.le_trans ?_ (Nat.le_trans (foldl_max_le _ b.params) (foldl_max_le _ b.term.uses))
  exact Nat.le_trans (le_foldl_max hx) (le_foldl_mxInstr hi)

omit model in
/-- Every value read by a terminator of `f` is at most `maxIdOf f`. -/
theorem le_maxIdOf_term_use {f : Func} {b : Block} (hb : b ∈ f.blocks.toList)
    {x : ValId} (hx : x ∈ b.term.uses) : x ≤ maxIdOf f :=
  Nat.le_trans (le_foldl_max hx) (mxBlock_le_maxIdOf hb)

/-! ### The constant map only names real `const` definitions -/

omit model in
theorem rematConstStep_fold_mem {is : List Instr} {m : Std.HashMap ValId U256}
    {a : ValId} {v : U256} (h : (is.foldl rematConstStep m)[a]? = some v) :
    Instr.const a v ∈ is ∨ m[a]? = some v := by
  induction is generalizing m with
  | nil => exact Or.inr h
  | cons i is ih =>
    rcases ih (m := rematConstStep m i) h with hmem | hget
    · exact Or.inl (List.mem_cons_of_mem _ hmem)
    · cases i with
      | const d w =>
        by_cases hd : a = d
        · subst a
          rw [rematConstStep, Std.HashMap.getElem?_insert_self] at hget
          have : v = w := (Option.some.inj hget).symm
          subst v
          exact Or.inl (List.mem_cons_self ..)
        · rw [rematConstStep, Std.HashMap.getElem?_insert,
            if_neg (by simpa using fun h => hd h.symm)] at hget
          exact Or.inr hget
      | op ds yop as => exact Or.inr hget
      | call ds fid as => exact Or.inr hget

omit model in
theorem rematConstMap_sound {f : Func} {a : ValId} {v : U256}
    (h : (rematConstMap f)[a]? = some v) : ConstDef f a v := by
  unfold rematConstMap at h
  have key : ∀ (bs : List Block) (m : Std.HashMap ValId U256),
      ((bs.foldl (fun m b => b.instrs.foldl rematConstStep m) m)[a]? = some v) →
      (∃ b ∈ bs, Instr.const a v ∈ b.instrs) ∨ m[a]? = some v := by
    intro bs
    induction bs with
    | nil => intro m hm; exact Or.inr hm
    | cons b bs ih =>
      intro m hm
      rcases ih (b.instrs.foldl rematConstStep m) hm with ⟨c, hc, hi⟩ | hget
      · exact Or.inl ⟨c, List.mem_cons_of_mem _ hc, hi⟩
      · rcases rematConstStep_fold_mem hget with hi | hget'
        · exact Or.inl ⟨b, List.mem_cons_self .., hi⟩
        · exact Or.inr hget'
  rcases key f.blocks.toList ∅ h with ⟨b, hb, hi⟩ | hempty
  · exact ConstDef.const hb hi
  · simp at hempty


/-! ### The rewritten rest of a block -/

/-- The rewrite of an arbitrary instruction suffix of a block plus its
terminator: the copies for each remaining instruction, then the copies the
terminator needs, then the substituted terminator. -/
def rematRest (rv : Nat → ValId → Option U256) (blen : Nat) (t : Term)
    (here : Nat) (next : ValId) (is : List Instr) : Rest :=
  let r := rematSeq rv is here next
  let c := rematCopies (rv blen) t.uses r.2 ∅
  ⟨r.1 ++ c.1, rematT c.2.2 t⟩

omit model in
theorem rematRest_nil (rv : Nat → ValId → Option U256) (blen : Nat) (t : Term)
    (here : Nat) (next : ValId) :
    rematRest rv blen t here next [] =
      ⟨(rematCopies (rv blen) t.uses next ∅).1,
        rematT (rematCopies (rv blen) t.uses next ∅).2.2 t⟩ := by
  simp [rematRest, rematSeq]

omit model in
theorem rematRest_cons (rv : Nat → ValId → Option U256) (blen : Nat) (t : Term)
    (here : Nat) (next : ValId) (ins : Instr) (is : List Instr) :
    rematRest rv blen t here next (ins :: is) =
      ⟨(rematCopies (rv here) ins.uses next ∅).1 ++
          rematI (rematCopies (rv here) ins.uses next ∅).2.2 ins ::
            (rematRest rv blen t (here + 1)
              (rematCopies (rv here) ins.uses next ∅).2.1 is).instrs,
        (rematRest rv blen t (here + 1)
          (rematCopies (rv here) ins.uses next ∅).2.1 is).term⟩ := by
  simp [rematRest, rematSeq]

omit model in
theorem rematBlockOutR_eq_rest (rv : Nat → ValId → Option U256) (b : Block) (next : ValId) :
    (rematBlockOutR rv b next).1 =
      { b with
        instrs := (rematRest rv b.instrs.length b.term 0 next b.instrs).instrs,
        term := (rematRest rv b.instrs.length b.term 0 next b.instrs).term } := rfl

omit model in
/-- The heuristic only ever proposes a value the constant map really holds. -/
theorem rematValue_const {cm : Std.HashMap ValId U256} {la : Std.HashMap ValId Nat}
    {here : Nat} {a : ValId} {v : U256} (h : rematValue cm la here a = some v) :
    cm[a]? = some v := by
  unfold rematValue at h
  cases hc : cm[a]? with
  | none => simp only [hc] at h; simp at h
  | some w =>
    simp only [hc] at h
    cases hl : la[a]? with
    | none => simp only [hl] at h; exact h
    | some k =>
      simp only [hl] at h
      split at h
      · exact h
      · simp at h

/-! ### Executing the copies

The copies are `const`s with ids strictly above `maxIdOf f`, so running them
leaves the original ids alone; each one binds its id to the value the original
already holds at the id it was copied from. -/

theorem rematCopies_exec {P : Prog} {f g : Func} {cm : Std.HashMap ValId U256}
    {rv : ValId → Option U256} (hrv : ∀ {a v}, rv a = some v → cm[a]? = some v)
    (hcm : ∀ {a v}, cm[a]? = some v → ConstDef f a v)
    {N : Nat} {R : Regs} (hR : ConstRegs f R) :
    ∀ (as : List ValId) (next : ValId) (sub : Subst) (Rc : Regs),
      N < next →
      (∀ a n, sub[a]? = some n → n < next ∧ N < n ∧ ∀ w, R a = some w → Rc n = some w) →
      (∀ x, x ≤ N → R x = Rc x) →
      ∃ Rc' : Regs,
        (∀ x, x ≤ N → R x = Rc' x)
        ∧ (∀ a n, (rematCopies rv as next sub).2.2[a]? = some n →
             N < n ∧ ∀ w, R a = some w → Rc' n = some w)
        ∧ (∀ (st : EvmState) (is : List Instr) (t : Term) (res : FRes),
             Exec (model := model) P g Rc' st ⟨is, t⟩ res →
             Exec (model := model) P g Rc st
               ⟨(rematCopies rv as next sub).1 ++ is, t⟩ res) := by
  intro as
  induction as with
  | nil =>
    intro next sub Rc _ hsub hag
    exact ⟨Rc, hag, fun a n h => ⟨(hsub a n h).2.1, (hsub a n h).2.2⟩,
      fun st is t res hx => hx⟩
  | cons a as ih =>
    intro next sub Rc hnext hsub hag
    rw [rematCopies]
    by_cases hc : sub.contains a = true
    · rw [if_pos hc]
      exact ih next sub Rc hnext hsub hag
    · rw [if_neg hc]
      cases hv : rv a with
      | none => exact ih next sub Rc hnext hsub hag
      | some v =>
        have hCd : ConstDef f a v := hcm (hrv hv)
        refine ?_
        obtain ⟨Rc', hag', hsub', hexec'⟩ :=
          ih (next + 1) (sub.insert a next) (Rc.set next v)
            (Nat.lt_succ_of_lt hnext)
            (by
              intro a' n hn
              rw [Std.HashMap.getElem?_insert] at hn
              by_cases haa : (a == a') = true
              · rw [if_pos haa] at hn
                have hn' : n = next := (Option.some.inj hn).symm
                subst n
                have : a' = a := by simpa [eq_comm] using (by simpa using haa : a = a')
                subst a'
                refine ⟨Nat.lt_succ_self _, hnext, ?_⟩
                intro w hw
                have : w = v := hR hCd hw
                subst w
                simp
              · rw [if_neg (by simpa using haa)] at hn
                obtain ⟨h1, h2, h3⟩ := hsub a' n hn
                refine ⟨Nat.lt_succ_of_lt h1, h2, ?_⟩
                intro w hw
                rw [Regs.set_other _ _ (Nat.ne_of_lt h1)]
                exact h3 w hw)
            (by
              intro x hx
              rw [Regs.set_other _ _ (Nat.ne_of_lt (Nat.lt_of_le_of_lt hx hnext))]
              exact hag x hx)
        refine ⟨Rc', hag', hsub', ?_⟩
        intro st is t res hx
        exact Exec.const (hexec' st is t res hx)

/-- The copy-prefix property at an empty instruction suffix. -/
theorem exec_copies_nil {P : Prog} {g : Func} {Rc Rc' : Regs} {cps : List Instr}
    (hpre : ∀ (st : EvmState) (is : List Instr) (t : Term) (res : FRes),
      Exec (model := model) P g Rc' st ⟨is, t⟩ res →
      Exec (model := model) P g Rc st ⟨cps ++ is, t⟩ res)
    (st : EvmState) (t : Term) (res : FRes)
    (h : Exec (model := model) P g Rc' st ⟨[], t⟩ res) :
    Exec (model := model) P g Rc st ⟨cps, t⟩ res := by
  simpa using hpre st [] t res h

omit model in
theorem getMany_mem_some {R : Regs} {as : List ValId} {vals : List U256}
    (h : R.getMany as = some vals) {x : ValId} (hx : x ∈ as) : ∃ w, R x = some w := by
  induction as generalizing vals with
  | nil => simp at hx
  | cons y ys ih =>
    rw [Regs.getMany_cons] at h
    cases hy : R y with
    | none => rw [hy] at h; simp at h
    | some w =>
      rw [hy] at h
      cases hys : R.getMany ys with
      | none => rw [hys] at h; simp at h
      | some ws =>
        rcases List.mem_cons.mp hx with rfl | hmem
        · exact ⟨w, hy⟩
        · exact ih hys hmem

omit model in
/-- Reading a use list through the substitution the copies installed. -/
theorem rematCopies_getMany {N : Nat} {R Rc : Regs} {sub : Subst}
    (hag : ∀ x, x ≤ N → R x = Rc x)
    (hsub : ∀ a n, sub[a]? = some n → N < n ∧ ∀ w, R a = some w → Rc n = some w)
    {as : List ValId} (hbound : ∀ a ∈ as, a ≤ N)
    {vals : List U256} (hget : R.getMany as = some vals) :
    Rc.getMany (rematVs sub as) = some vals := by
  rw [rematVs_eq_substVs]
  refine Regs.getMany_substVs ?_ hget
  intro x hx
  cases hs : sub[x]? with
  | none =>
    have : substV sub x = x := by
      rw [← rematV_eq_substV]
      simp [rematV, hs]
    rw [this]
    exact hag x (hbound x hx)
  | some n =>
    have hsv : substV sub x = n := by
      rw [← rematV_eq_substV]
      simp [rematV, hs]
    rw [hsv]
    obtain ⟨w, hxv⟩ := getMany_mem_some hget hx
    rw [hxv, (hsub x n hs).2 w hxv]


omit model in
/-- One value read through the substitution the copies installed. -/
theorem rematCopies_get {N : Nat} {R Rc : Regs} {sub : Subst}
    (hag : ∀ x, x ≤ N → R x = Rc x)
    (hsub : ∀ a n, sub[a]? = some n → N < n ∧ ∀ w, R a = some w → Rc n = some w)
    {x : ValId} (hx : x ≤ N) {w : U256} (h : R x = some w) :
    Rc (rematV sub x) = some w := by
  cases hs : sub[x]? with
  | none => rw [show rematV sub x = x by simp [rematV, hs], ← hag x hx]; exact h
  | some m =>
    rw [show rematV sub x = m by simp [rematV, hs]]
    exact (hsub x m hs).2 w h

/-! ### Locating the rewritten blocks -/

def rvOf (f : Func) (b : Block) : Nat → ValId → Option U256 :=
  fun here a => rematValue (rematConstMap f) (rematLocalAt b) here a

omit model in
theorem rematConsts_params (f : Func) : (rematConsts f).params = f.params := by
  rw [rematConsts_eq]; split <;> rfl

omit model in
theorem rematConsts_entry (f : Func) : (rematConsts f).entry = f.entry := by
  rw [rematConsts_eq]; split <;> rfl

omit model in
theorem rematConsts_blocks_get {f : Func} (hne : (rematConstMap f).isEmpty = false)
    {j : BlockId} {b : Block} (hb : f.blocks[j]? = some b) :
    ∃ m, maxIdOf f < m ∧
      (rematConsts f).blocks[j]? = some (rematBlockOutR (rvOf f b) b m).1 := by
  have hb' : f.blocks.toList[j]? = some b := Array.getElem?_toList.trans hb
  obtain ⟨m, hm, hget⟩ :=
    rematBlocksOut_get (rematConstMap f) f.blocks.toList (maxIdOf f + 1) j b hb'
  refine ⟨m, hm, ?_⟩
  have hR : rematBlockOut (rematConstMap f) b m = rematBlockOutR (rvOf f b) b m := rfl
  rw [hR] at hget
  rw [rematConsts_eq, if_neg (by simp [hne])]
  simpa using hget

end Passes

/-! ### The simulation

The invariant is `∀ x ≤ maxIdOf f, R x = Rc x` — the two register files agree
on every id the original function can mention — together with `ConstRegs f R`,
which is what makes a copy's literal the value the original already holds. -/

theorem remat_exec_aux {P : Prog} {f : Func} {n : Nat} (hwf : f.wfCheck n = true)
    (hnd : f.allDefs.Nodup) (hne : (Passes.rematConstMap f).isEmpty = false)
    {R : Regs} {st : EvmState} {rest : Rest} {res : FRes}
    (hexec : Exec (model := model) P f R st rest res) :
    ∀ {bi : BlockId} {b : Block} {Rc : Regs} {here : Nat} {next : ValId},
      f.blocks[bi]? = some b → rest.term = b.term → rest.instrs <:+ b.instrs →
      Passes.maxIdOf f < next → ConstRegs f R →
      (∀ x, x ≤ Passes.maxIdOf f → R x = Rc x) →
      Exec (model := model) P (Passes.rematConsts f) Rc st
        (Passes.rematRest (Passes.rvOf f b) b.instrs.length rest.term here next
          rest.instrs) res := by
  induction hexec with
  | @const f R st d v is t res htail ih =>
    intro bi b Rc here next hb ht hs hnext hR hag
    have hbmem : b ∈ f.blocks.toList := List.mem_of_getElem? (Array.getElem?_toList.trans hb)
    have hi : Instr.const d v ∈ b.instrs := hs.mem (by simp)
    have hs' : is <:+ b.instrs :=
      List.IsSuffix.trans (show is <:+ Instr.const d v :: is from ⟨[Instr.const d v], rfl⟩) hs
    rw [Passes.rematRest_cons]
    exact Exec.const (ih hwf hnd hne hb ht hs' hnext
      (constRegs_const hnd hbmem hi hR) (Regs.set_congr hag d v))
  | @op f R st st' ds yop as args rets is t res hget hbi hlen htail ih =>
    intro bi b Rc here next hb ht hs hnext hR hag
    have hbmem : b ∈ f.blocks.toList := List.mem_of_getElem? (Array.getElem?_toList.trans hb)
    have hi : Instr.op ds yop as ∈ b.instrs := hs.mem (by simp)
    have hs' : is <:+ b.instrs :=
      List.IsSuffix.trans (show is <:+ Instr.op ds yop as :: is from ⟨[Instr.op ds yop as], rfl⟩) hs
    obtain ⟨Rc', hag', hsub', hpre⟩ :=
      Passes.rematCopies_exec (P := P) (g := Passes.rematConsts f)
        (rv := Passes.rvOf f b here) Passes.rematValue_const Passes.rematConstMap_sound hR
        (Instr.op ds yop as).uses next ∅ Rc hnext (by intro a m hm; simp at hm) hag
    have hbound : ∀ a ∈ as, a ≤ Passes.maxIdOf f := fun a ha =>
      Passes.le_maxIdOf_instr_use hbmem hi (by simpa [Instr.uses] using ha)
    have hget' := Passes.rematCopies_getMany hag' hsub' hbound hget
    have hnext' : Passes.maxIdOf f <
        (Passes.rematCopies (Passes.rvOf f b here) (Instr.op ds yop as).uses next ∅).2.1 :=
      Nat.lt_of_lt_of_le hnext (Passes.rematCopies_next_le _ _ next ∅)
    have hbody := ih (here := here + 1) hwf hnd hne hb ht hs' hnext'
      (constRegs_op hwf hnd hbmem hi hR hget hbi hlen) (Regs.setMany_congr hag' ds rets)
    rw [Passes.rematRest_cons]
    exact hpre st _ _ res (Exec.op hget' hbi hlen hbody)
  | @opHalt f R st st' ds yop as args is t hget hbi =>
    intro bi b Rc here next hb ht hs hnext hR hag
    have hbmem : b ∈ f.blocks.toList := List.mem_of_getElem? (Array.getElem?_toList.trans hb)
    have hi : Instr.op ds yop as ∈ b.instrs := hs.mem (by simp)
    obtain ⟨Rc', hag', hsub', hpre⟩ :=
      Passes.rematCopies_exec (P := P) (g := Passes.rematConsts f)
        (rv := Passes.rvOf f b here) Passes.rematValue_const Passes.rematConstMap_sound hR
        (Instr.op ds yop as).uses next ∅ Rc hnext (by intro a m hm; simp at hm) hag
    have hbound : ∀ a ∈ as, a ≤ Passes.maxIdOf f := fun a ha =>
      Passes.le_maxIdOf_instr_use hbmem hi (by simpa [Instr.uses] using ha)
    have hget' := Passes.rematCopies_getMany hag' hsub' hbound hget
    rw [Passes.rematRest_cons]
    exact hpre st _ _ _ (Exec.opHalt hget' hbi)
  | @call f gc R st st' ds as fid args rvals eb is t res hfid hget hplen heb hbody hlen
      htail ihbody ih =>
    intro bi b Rc here next hb ht hs hnext hR hag
    have hbmem : b ∈ f.blocks.toList := List.mem_of_getElem? (Array.getElem?_toList.trans hb)
    have hi : Instr.call ds fid as ∈ b.instrs := hs.mem (by simp)
    have hs' : is <:+ b.instrs :=
      List.IsSuffix.trans (show is <:+ Instr.call ds fid as :: is from ⟨[Instr.call ds fid as], rfl⟩) hs
    obtain ⟨Rc', hag', hsub', hpre⟩ :=
      Passes.rematCopies_exec (P := P) (g := Passes.rematConsts f)
        (rv := Passes.rvOf f b here) Passes.rematValue_const Passes.rematConstMap_sound hR
        (Instr.call ds fid as).uses next ∅ Rc hnext (by intro a m hm; simp at hm) hag
    have hbound : ∀ a ∈ as, a ≤ Passes.maxIdOf f := fun a ha =>
      Passes.le_maxIdOf_instr_use hbmem hi (by simpa [Instr.uses] using ha)
    have hget' := Passes.rematCopies_getMany hag' hsub' hbound hget
    have hnext' : Passes.maxIdOf f <
        (Passes.rematCopies (Passes.rvOf f b here) (Instr.call ds fid as).uses next ∅).2.1 :=
      Nat.lt_of_lt_of_le hnext (Passes.rematCopies_next_le _ _ next ∅)
    have htl := ih (here := here + 1) hwf hnd hne hb ht hs' hnext'
      (constRegs_call hnd hbmem hi hR rvals) (Regs.setMany_congr hag' ds rvals)
    rw [Passes.rematRest_cons]
    exact hpre st _ _ res (Exec.call hfid hget' hplen heb hbody hlen htl)
  | @callHalt f gc R st st' ds as fid args eb is t hfid hget hplen heb hbody ihbody =>
    intro bi b Rc here next hb ht hs hnext hR hag
    have hbmem : b ∈ f.blocks.toList := List.mem_of_getElem? (Array.getElem?_toList.trans hb)
    have hi : Instr.call ds fid as ∈ b.instrs := hs.mem (by simp)
    obtain ⟨Rc', hag', hsub', hpre⟩ :=
      Passes.rematCopies_exec (P := P) (g := Passes.rematConsts f)
        (rv := Passes.rvOf f b here) Passes.rematValue_const Passes.rematConstMap_sound hR
        (Instr.call ds fid as).uses next ∅ Rc hnext (by intro a m hm; simp at hm) hag
    have hbound : ∀ a ∈ as, a ≤ Passes.maxIdOf f := fun a ha =>
      Passes.le_maxIdOf_instr_use hbmem hi (by simpa [Instr.uses] using ha)
    have hget' := Passes.rematCopies_getMany hag' hsub' hbound hget
    rw [Passes.rematRest_cons]
    exact hpre st _ _ _ (Exec.callHalt hfid hget' hplen heb hbody)
  | @jump f R st e tb vals res htb hget hlen htail ih =>
    intro bi b Rc here next hb ht hs hnext hR hag
    have hbmem : b ∈ f.blocks.toList := List.mem_of_getElem? (Array.getElem?_toList.trans hb)
    have htbmem : tb ∈ f.blocks.toList := List.mem_of_getElem? (Array.getElem?_toList.trans htb)
    obtain ⟨Rc', hag', hsub', hpre⟩ :=
      Passes.rematCopies_exec (P := P) (g := Passes.rematConsts f)
        (rv := Passes.rvOf f b b.instrs.length) Passes.rematValue_const
        Passes.rematConstMap_sound hR (Term.jump e).uses next ∅ Rc hnext
        (by intro a m hm; simp at hm) hag
    have hbound : ∀ a ∈ e.args, a ≤ Passes.maxIdOf f := by
      intro a ha
      exact Passes.le_maxIdOf_term_use hbmem (by rw [← ht]; simpa [Term.uses] using ha)
    have hget' := Passes.rematCopies_getMany hag' hsub' hbound hget
    obtain ⟨m, hm, htb'⟩ := Passes.rematConsts_blocks_get hne htb
    have hbody := ih (here := 0) hwf hnd hne htb rfl (List.suffix_refl _) hm
      (constRegs_setMany_params hnd hR htbmem vals) (Regs.setMany_congr hag' tb.params vals)
    rw [Passes.rematRest_nil]
    exact Passes.exec_copies_nil hpre st _ res (Exec.jump htb' hget' hlen hbody)
  | @branchTrue f R st c v et ef tb vals res hc hv htb hget hlen htail ih =>
    intro bi b Rc here next hb ht hs hnext hR hag
    have hbmem : b ∈ f.blocks.toList := List.mem_of_getElem? (Array.getElem?_toList.trans hb)
    have htbmem : tb ∈ f.blocks.toList := List.mem_of_getElem? (Array.getElem?_toList.trans htb)
    obtain ⟨Rc', hag', hsub', hpre⟩ :=
      Passes.rematCopies_exec (P := P) (g := Passes.rematConsts f)
        (rv := Passes.rvOf f b b.instrs.length) Passes.rematValue_const
        Passes.rematConstMap_sound hR (Term.branch c et ef).uses next ∅ Rc hnext
        (by intro a m hm; simp at hm) hag
    have hcbound : c ≤ Passes.maxIdOf f :=
      Passes.le_maxIdOf_term_use hbmem (by rw [← ht]; simp [Term.uses])
    have hbound : ∀ a ∈ et.args, a ≤ Passes.maxIdOf f := by
      intro a ha
      exact Passes.le_maxIdOf_term_use hbmem (by rw [← ht]; simp [Term.uses, ha])
    have hget' := Passes.rematCopies_getMany hag' hsub' hbound hget
    have hc' := Passes.rematCopies_get hag' hsub' hcbound hc
    obtain ⟨m, hm, htb'⟩ := Passes.rematConsts_blocks_get hne htb
    have hbody := ih (here := 0) hwf hnd hne htb rfl (List.suffix_refl _) hm
      (constRegs_setMany_params hnd hR htbmem vals) (Regs.setMany_congr hag' tb.params vals)
    rw [Passes.rematRest_nil]
    exact Passes.exec_copies_nil hpre st _ res
      (Exec.branchTrue hc' hv htb' hget' hlen hbody)
  | @branchFalse f R st c et ef tb vals res hc htb hget hlen htail ih =>
    intro bi b Rc here next hb ht hs hnext hR hag
    have hbmem : b ∈ f.blocks.toList := List.mem_of_getElem? (Array.getElem?_toList.trans hb)
    have htbmem : tb ∈ f.blocks.toList := List.mem_of_getElem? (Array.getElem?_toList.trans htb)
    obtain ⟨Rc', hag', hsub', hpre⟩ :=
      Passes.rematCopies_exec (P := P) (g := Passes.rematConsts f)
        (rv := Passes.rvOf f b b.instrs.length) Passes.rematValue_const
        Passes.rematConstMap_sound hR (Term.branch c et ef).uses next ∅ Rc hnext
        (by intro a m hm; simp at hm) hag
    have hcbound : c ≤ Passes.maxIdOf f :=
      Passes.le_maxIdOf_term_use hbmem (by rw [← ht]; simp [Term.uses])
    have hbound : ∀ a ∈ ef.args, a ≤ Passes.maxIdOf f := by
      intro a ha
      exact Passes.le_maxIdOf_term_use hbmem (by rw [← ht]; simp [Term.uses, ha])
    have hget' := Passes.rematCopies_getMany hag' hsub' hbound hget
    have hc' := Passes.rematCopies_get hag' hsub' hcbound hc
    obtain ⟨m, hm, htb'⟩ := Passes.rematConsts_blocks_get hne htb
    have hbody := ih (here := 0) hwf hnd hne htb rfl (List.suffix_refl _) hm
      (constRegs_setMany_params hnd hR htbmem vals) (Regs.setMany_congr hag' tb.params vals)
    rw [Passes.rematRest_nil]
    exact Passes.exec_copies_nil hpre st _ res
      (Exec.branchFalse hc' htb' hget' hlen hbody)
  | @ret f R st xs vals hget =>
    intro bi b Rc here next hb ht hs hnext hR hag
    have hbmem : b ∈ f.blocks.toList := List.mem_of_getElem? (Array.getElem?_toList.trans hb)
    obtain ⟨Rc', hag', hsub', hpre⟩ :=
      Passes.rematCopies_exec (P := P) (g := Passes.rematConsts f)
        (rv := Passes.rvOf f b b.instrs.length) Passes.rematValue_const
        Passes.rematConstMap_sound hR (Term.ret xs).uses next ∅ Rc hnext
        (by intro a m hm; simp at hm) hag
    have hbound : ∀ a ∈ xs, a ≤ Passes.maxIdOf f := by
      intro a ha
      exact Passes.le_maxIdOf_term_use hbmem (by rw [← ht]; simpa [Term.uses] using ha)
    have hget' := Passes.rematCopies_getMany hag' hsub' hbound hget
    rw [Passes.rematRest_nil]
    exact Passes.exec_copies_nil hpre st _ _ (Exec.ret hget')
  | @halt f R st st' yop as args hget hbi =>
    intro bi b Rc here next hb ht hs hnext hR hag
    have hbmem : b ∈ f.blocks.toList := List.mem_of_getElem? (Array.getElem?_toList.trans hb)
    obtain ⟨Rc', hag', hsub', hpre⟩ :=
      Passes.rematCopies_exec (P := P) (g := Passes.rematConsts f)
        (rv := Passes.rvOf f b b.instrs.length) Passes.rematValue_const
        Passes.rematConstMap_sound hR (Term.halt yop as).uses next ∅ Rc hnext
        (by intro a m hm; simp at hm) hag
    have hbound : ∀ a ∈ as, a ≤ Passes.maxIdOf f := by
      intro a ha
      exact Passes.le_maxIdOf_term_use hbmem (by rw [← ht]; simpa [Term.uses] using ha)
    have hget' := Passes.rematCopies_getMany hag' hsub' hbound hget
    rw [Passes.rematRest_nil]
    exact Passes.exec_copies_nil hpre st _ _ (Exec.halt hget' hbi)


/-- **Pass 6 (constant rematerialization) soundness.**  No dominance
hypothesis: the pass never reroutes an existing use to an existing value, it
only introduces a fresh definition of a constant in front of the use. -/
theorem rematConsts_sound {P : Prog} {f : Func} {n : Nat} {args : List U256}
    {st : EvmState} {res : FRes} {eb eb' : Block} (hwf : f.wfCheck n = true)
    (heb : f.blocks[f.entry]? = some eb)
    (heb' : (Passes.rematConsts f).blocks[(Passes.rematConsts f).entry]? = some eb')
    (hexec : Exec (model := model) P f (Regs.empty.setMany f.params args) st
      ⟨eb.instrs, eb.term⟩ res) :
    Exec (model := model) P (Passes.rematConsts f) (Regs.empty.setMany f.params args) st
      ⟨eb'.instrs, eb'.term⟩ res := by
  rw [Passes.rematConsts_entry] at heb'
  by_cases hne : (Passes.rematConstMap f).isEmpty = true
  · have hid : Passes.rematConsts f = f := by
      rw [Passes.rematConsts_eq]; simp [hne]
    rw [hid] at heb' ⊢
    have hebeq : eb' = eb := Option.some.inj (heb'.symm.trans heb)
    subst eb'
    exact hexec
  · have hne' : (Passes.rematConstMap f).isEmpty = false := by simpa using hne
    obtain ⟨m, hm, hget⟩ := Passes.rematConsts_blocks_get hne' heb
    have hebeq : eb' = (Passes.rematBlockOutR (Passes.rvOf f eb) eb m).1 :=
      Option.some.inj (heb'.symm.trans hget)
    subst eb'
    have hnd := wfCheck_defs_nodup hwf
    have hsim := remat_exec_aux (here := 0) hwf hnd hne' hexec heb rfl
      (List.suffix_refl _) hm (constRegs_entry hnd args) (fun _ _ => rfl)
    rw [Passes.rematBlockOutR_eq_rest]
    exact hsim

omit model in
theorem Passes.rematStep_params (n : Nat) (f : Func) : (rematStep n f).params = f.params := by
  simp only [rematStep]
  split
  · rw [dve_params, rematConsts_params]
  · rfl

omit model in
theorem Passes.rematStep_wf {f : Func} {n : Nat} (hwf : f.wfCheck n = true) :
    (rematStep n f).wfCheck n = true := by
  simp only [rematStep]
  split
  · next h => exact dve_wf h
  · exact hwf

/-- The two halves of `rematStep`, composed. -/
theorem rematStep_sound {P : Prog} {f : Func} {args : List U256}
    {st : EvmState} {res : FRes} {eb eb' : Block}
    (hwf : f.wfCheck P.funcs.size = true)
    (heb : f.blocks[f.entry]? = some eb)
    (heb' : (Passes.rematStep P.funcs.size f).blocks[
      (Passes.rematStep P.funcs.size f).entry]? = some eb')
    (hexec : Exec (model := model) P f (Regs.empty.setMany f.params args) st
      ⟨eb.instrs, eb.term⟩ res) :
    Exec (model := model) P (Passes.rematStep P.funcs.size f)
      (Regs.empty.setMany (Passes.rematStep P.funcs.size f).params args) st
      ⟨eb'.instrs, eb'.term⟩ res := by
  rw [Passes.rematStep_params]
  simp only [Passes.rematStep] at heb' ⊢
  split at heb'
  · next hgate =>
    rw [if_pos hgate]
    obtain ⟨-, -, ⟨eb1, heb1, -⟩, -⟩ := Passes.func_wfCheck_iff.mp hgate
    have h1 := rematConsts_sound hwf heb heb1 hexec
    have h1' : Exec (model := model) P (Passes.rematConsts f)
        (Regs.empty.setMany (Passes.rematConsts f).params args) st
        ⟨eb1.instrs, eb1.term⟩ res := by
      rw [Passes.rematConsts_params]; exact h1
    have heb2 : (Passes.dve (Passes.rematConsts f)).blocks[(Passes.rematConsts f).entry]?
        = some eb' := by
      simpa [Passes.dve_entry] using heb'
    have h2 := dve_sound (P := P) hgate heb1 heb2 h1'
    rw [Passes.rematConsts_params] at h2
    exact h2
  · next hgate =>
    rw [if_neg hgate]
    have hebeq : eb' = eb := Option.some.inj (heb'.symm.trans heb)
    subst eb'
    exact hexec

omit model in
theorem rematCandidate_lookup {P : Prog} {fid : FuncId} {g : Func}
    (h : P.funcs[fid]? = some g) :
    (rematCandidate P).funcs[fid]? = some (Passes.rematStep P.funcs.size g) := by
  simp [rematCandidate, h]

/-- Change the ambient program to its rematerialized map while leaving the
current function text fixed. -/
theorem rematCandidate_exec {P : Prog} (hPwf : P.wfCheck = true) {f : Func} {R : Regs}
    {st : EvmState} {rest : Rest} {res : FRes}
    (hexec : Exec (model := model) P f R st rest res) :
    Exec (model := model) (rematCandidate P) f R st rest res := by
  induction hexec with
  | const htail ih => exact Exec.const ih
  | op hget hop hlen htail ih => exact Exec.op hget hop hlen ih
  | opHalt hget hop => exact Exec.opHalt hget hop
  | @call f g R st st' ds as fid args rvals eb is t res
      hfid hget hplen heb hbody hlen htail ihbody ih =>
      have hsize : (rematCandidate P).funcs.size = P.funcs.size := by simp [rematCandidate]
      have hgwf : g.wfCheck (rematCandidate P).funcs.size = true := by
        rw [hsize]; exact progWf_func hPwf hfid
      obtain ⟨-, -, ⟨eb', heb', -⟩, -⟩ :=
        Passes.func_wfCheck_iff.mp (Passes.rematStep_wf hgwf)
      have hbody' := rematStep_sound (P := rematCandidate P) hgwf heb heb' ihbody
      rw [hsize] at heb' hbody'
      refine Exec.call (g := Passes.rematStep P.funcs.size g) (eb := eb')
        (rematCandidate_lookup hfid) hget ?_ heb' hbody' hlen ih
      simpa [Passes.rematStep_params] using hplen
  | @callHalt f g R st st' ds as fid args eb is t hfid hget hplen heb hbody ihbody =>
      have hsize : (rematCandidate P).funcs.size = P.funcs.size := by simp [rematCandidate]
      have hgwf : g.wfCheck (rematCandidate P).funcs.size = true := by
        rw [hsize]; exact progWf_func hPwf hfid
      obtain ⟨-, -, ⟨eb', heb', -⟩, -⟩ :=
        Passes.func_wfCheck_iff.mp (Passes.rematStep_wf hgwf)
      have hbody' := rematStep_sound (P := rematCandidate P) hgwf heb heb' ihbody
      rw [hsize] at heb' hbody'
      refine Exec.callHalt (g := Passes.rematStep P.funcs.size g) (eb := eb')
        (rematCandidate_lookup hfid) hget ?_ heb' hbody'
      simpa [Passes.rematStep_params] using hplen
  | jump htb hget hplen htail ih => exact Exec.jump htb hget hplen ih
  | branchTrue hc hv htb hget hplen htail ih => exact Exec.branchTrue hc hv htb hget hplen ih
  | branchFalse hc htb hget hplen htail ih => exact Exec.branchFalse hc htb hget hplen ih
  | ret hget => exact Exec.ret hget
  | halt hget hop => exact Exec.halt hget hop

theorem rematCandidate_sound {P : Prog} {yst0 yst' : EvmState} {o : Outcome}
    (hwf : P.wfCheck = true) (hrun : Run (model := model) P yst0 yst' o) :
    Run (model := model) (rematCandidate P) yst0 yst' o := by
  have hparts := hwf
  simp only [Prog.wfCheck, Bool.and_eq_true] at hparts
  have hmainWf : P.main.wfCheck (rematCandidate P).funcs.size = true := by
    simpa [rematCandidate] using hparts.1.2
  have hmainParams : P.main.params = [] := List.isEmpty_iff.mp hparts.1.1.1
  cases hrun with
  | normal heb hexec =>
      obtain ⟨-, -, ⟨eb', heb', -⟩, -⟩ :=
        Passes.func_wfCheck_iff.mp (Passes.rematStep_wf hmainWf)
      have hamb := rematCandidate_exec hwf hexec
      have hlocal := rematStep_sound (P := rematCandidate P) (args := []) hmainWf heb heb'
        (by simpa [hmainParams, Regs.setMany_nil_left] using hamb)
      exact Run.normal (by simpa [rematCandidate] using heb')
        (by simpa [rematCandidate, Passes.rematStep_params, hmainParams,
          Regs.setMany_nil_left] using hlocal)
  | halt heb hexec =>
      obtain ⟨-, -, ⟨eb', heb', -⟩, -⟩ :=
        Passes.func_wfCheck_iff.mp (Passes.rematStep_wf hmainWf)
      have hamb := rematCandidate_exec hwf hexec
      have hlocal := rematStep_sound (P := rematCandidate P) (args := []) hmainWf heb heb'
        (by simpa [hmainParams, Regs.setMany_nil_left] using hamb)
      exact Run.halt (by simpa [rematCandidate] using heb')
        (by simpa [rematCandidate, Passes.rematStep_params, hmainParams,
          Regs.setMany_nil_left] using hlocal)

/-- **`SsaCfg.rematProg_sound`, reproduced verbatim.**  The defensive gate
either returns the rematerialized program — the case the simulation above
covers — or the original, where soundness is the hypothesis. -/
theorem rematProg_sound' {P : Prog} {yst0 yst' : EvmState} {o : Outcome}
    (hwf : P.wfCheck = true) (hrun : Run (model := model) P yst0 yst' o) :
    Run (model := model) (rematProg P) yst0 yst' o := by
  rw [rematProg_candidate]
  split
  · exact rematCandidate_sound hwf hrun
  · exact hrun

#print axioms rematProg_sound'

end YulEvmCompiler.SsaCfg
