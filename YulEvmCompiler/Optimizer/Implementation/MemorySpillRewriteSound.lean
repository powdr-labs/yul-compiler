import YulEvmCompiler.Optimizer.Implementation.MemorySpillOriginSound
import YulEvmCompiler.Optimizer.Implementation.MemorySpillStateSound
import YulEvmCompiler.Optimizer.Spec.MemoryGuardSound
set_option warningAsError true
/-!
# Environment relation for the memory-spill rewrite

Selected local bindings disappear from the target variable environment;
selected function parameters/results remain as calling-convention cells but
their values may be stale while memory is authoritative.  Unselected bindings
remain pointwise equal.  `VRel` states exactly that shape, while `SlotsLoaded`
relates every currently bound selected source value to its compiler-owned
memory word.

The full syntax-directed simulation is built above these reusable relations.
-/

namespace YulEvmCompiler.Optimizer.MemorySpillRewriteSound

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler.Optimizer
open MemorySpillSelect
open MemorySpillStateSound

variable {base reserved : Nat}
variable {calls : ExternalCalls} {creates : ExternalCreates}

local notation "G" => guardedEvm calls creates base reserved
local notation "D" => evmWithExternal calls creates

abbrev WordEnv := List (Ident × U256)

/-! ## Rewritten function environments

Function declarations are hoisted before execution.  The target environment
therefore contains the rewritten declaration at the same lexical position as
its guarded source declaration.  Making this mapping explicit lets the call
case change owners while retaining ordinary `lookupFun` resolution. -/

def spillDecl (slots : SlotMap) (name : Ident) (decl : FDecl G) : FDecl D :=
  let owner := some name
  let copies := copyBackReturns slots owner decl.rets
  { params := decl.params
    rets := decl.rets
    body := initParams slots owner decl.params ++
      initReturns slots owner decl.rets ++
      [.block (rewriteStmts slots owner copies decl.body)] ++ copies }

def spillScope (slots : SlotMap) (scope : FScope G) : FScope D :=
  scope.map fun item => (item.1, spillDecl slots item.1 item.2)

def spillFuns (slots : SlotMap) (funs : FunEnv G) : FunEnv D :=
  funs.map (spillScope slots)

private theorem hoist_append (left right : Block Op) :
    hoist D (left ++ right) = hoist D left ++ hoist D right := by
  simp [hoist]

private theorem hoist_rewriteStmt (slots : SlotMap) (owner : Owner)
    (exitCopies : Block Op) (stmt : Stmt Op) :
    hoist D (rewriteStmt slots owner exitCopies stmt) =
      spillScope slots (hoist G [stmt]) := by
  cases stmt <;> unfold rewriteStmt
  all_goals
    unfold hoist spillScope spillDecl
    repeat first | split
    all_goals simp_all
    all_goals try simp_all [MemorySpill.store]
    all_goals aesop

@[simp] theorem spillScope_hoist (slots : SlotMap) (owner : Owner)
    (exitCopies : Block Op) (body : Block Op) :
    spillScope slots (hoist G body) =
      hoist D (rewriteStmts slots owner exitCopies body) := by
  induction body with
  | nil => simp [hoist, spillScope, rewriteStmts]
  | cons stmt rest ih =>
      rw [rewriteStmts, hoist_append, hoist_rewriteStmt]
      unfold spillScope at ih ⊢
      rw [show hoist G (stmt :: rest) = hoist G [stmt] ++ hoist G rest by
        cases stmt <;> rfl]
      rw [List.map_append, ih]

private theorem spillScope_find (slots : SlotMap) (scope : FScope G)
    (fn : Ident) :
    (spillScope slots scope).find? (fun item => item.1 = fn) =
      (scope.find? fun item => item.1 = fn).map
        (fun item => (item.1, spillDecl slots item.1 item.2)) := by
  unfold spillScope
  rw [List.find?_map]
  rfl

@[simp] theorem spillFuns_lookup (slots : SlotMap) (funs : FunEnv G)
    (fn : Ident) :
    lookupFun (spillFuns slots funs) fn =
      (lookupFun funs fn).map fun result =>
        (spillDecl slots fn result.1, spillFuns slots result.2) := by
  induction funs with
  | nil => rfl
  | cons scope rest ih =>
      simp only [spillFuns, List.map_cons, lookupFun]
      rw [spillScope_find]
      cases hfind : scope.find? (fun item => item.1 = fn) with
      | none =>
          simp only [Option.map_none]
          exact ih
      | some item =>
          obtain ⟨name, decl⟩ := item
          have hname : name = fn := by
            simpa using List.find?_some hfind
          subst name
          simp only [Option.map_some]
          rfl

theorem spillFuns_lookup_some (slots : SlotMap) {funs : FunEnv G}
    {fn : Ident} {decl : FDecl G} {closure : FunEnv G}
    (hlookup : lookupFun funs fn = some (decl, closure)) :
    lookupFun (spillFuns slots funs) fn =
      some (spillDecl slots fn decl, spillFuns slots closure) := by
  rw [spillFuns_lookup, hlookup]
  rfl

theorem targetSlots_some_of_all_selected {selected : SpillSet}
    {layout : MemorySpillSelect.Layout}
    (hcheck : layoutCheck base reserved selected layout = true)
    (owner : Owner) : ∀ xs : List Ident,
    (∀ name ∈ xs, { owner, name } ∈ selected) →
      ∃ addresses, targetSlots? layout.slots owner xs = some addresses
  | [], _ => ⟨[], rfl⟩
  | name :: rest, hall => by
      obtain ⟨address, haddress⟩ :=
        layoutCheck_selected_slot hcheck (hall name (by simp))
      obtain ⟨addresses, hrest⟩ :=
        targetSlots_some_of_all_selected hcheck owner rest (by
          intro item hmem
          exact hall item (by simp [hmem]))
      exact ⟨address :: addresses, by simp [targetSlots?, haddress, hrest]⟩

theorem targetSlots_none_of_all_unselected {selected : SpillSet}
    {layout : MemorySpillSelect.Layout}
    (hcheck : layoutCheck base reserved selected layout = true)
    (owner : Owner) {name : Ident} (rest : List Ident)
    (hall : ∀ item ∈ name :: rest, { owner, name := item } ∉ selected) :
    targetSlots? layout.slots owner (name :: rest) = none := by
  have hnone : slotFor? layout.slots owner name = none := by
    cases hslot : slotFor? layout.slots owner name with
    | none => rfl
    | some address =>
        exact False.elim (hall name (by simp)
          (layoutCheck_slot_selected hcheck hslot))
  simp [targetSlots?, hnone]

def envGet (vars : WordEnv) (name : Ident) : Option U256 :=
  (vars.find? fun item => item.1 = name).map Prod.snd

def envSet : WordEnv → Ident → U256 → WordEnv
  | [], _, _ => []
  | (head, old) :: rest, name, value =>
      if head = name then (name, value) :: rest
      else (head, old) :: envSet rest name value

def retainedBinding (slots : SlotMap) (owner : Owner)
    (signature : List Ident) (name : Ident) : Bool :=
  match slotFor? slots owner name with
  | none => true
  | some _ => signature.contains name

theorem envGet_cons (item : Ident × U256) (vars : WordEnv) (name : Ident) :
    envGet (item :: vars) name =
      if item.1 = name then some item.2 else envGet vars name := by
  unfold envGet
  rw [List.find?_cons]
  by_cases h : item.1 = name <;> simp [h]

theorem envGet_envSet_self {vars : WordEnv} {name : Ident} {value found : U256}
    (hget : envGet (envSet vars name value) name = some found) :
    found = value := by
  induction vars with
  | nil => simp [envSet, envGet] at hget
  | cons item rest ih =>
      obtain ⟨head, old⟩ := item
      by_cases hhead : head = name
      · subst head
        simp [envSet, envGet_cons] at hget
        exact hget.symm
      · simp [envSet, envGet_cons, hhead] at hget
        exact ih hget

theorem envGet_envSet_self_eq {vars : WordEnv} {name : Ident}
    {old value : U256} (hget : envGet vars name = some old) :
    envGet (envSet vars name value) name = some value := by
  induction vars with
  | nil => simp [envGet] at hget
  | cons item rest ih =>
      obtain ⟨head, found⟩ := item
      rw [envGet_cons] at hget
      by_cases hhead : head = name
      · subst head
        simp [envSet, envGet_cons]
      · simp only [if_neg hhead] at hget
        simp [envSet, envGet_cons, hhead, ih hget]

theorem envGet_envSet_other {vars : WordEnv} {name other : Ident}
    (hne : other ≠ name) (value : U256) :
    envGet (envSet vars name value) other = envGet vars other := by
  induction vars with
  | nil => rfl
  | cons item rest ih =>
      obtain ⟨head, old⟩ := item
      by_cases hhead : head = name
      · subst head
        have hno : name ≠ other := Ne.symm hne
        simp [envSet, envGet_cons, hno]
      · by_cases hother : head = other
        · subst head
          simp [envSet, envGet_cons, hhead]
        · simp [envSet, envGet_cons, hhead, hother, ih]

theorem envSet_eq {calls : ExternalCalls} {creates : ExternalCreates}
    {base reserved : Nat} (vars : WordEnv) (name : Ident) (value : U256) :
    envSet vars name value =
      @VEnv.set (guardedEvm calls creates base reserved) vars name value := by
  induction vars with
  | nil => rfl
  | cons item rest ih =>
      obtain ⟨head, old⟩ := item
      by_cases hhead : head = name <;> simp [envSet, VEnv.set, hhead, ih]

theorem envSet_eq_ordinary {calls : ExternalCalls} {creates : ExternalCreates}
    (vars : WordEnv) (name : Ident) (value : U256) :
    envSet vars name value =
      @VEnv.set (evmWithExternal calls creates) vars name value := by
  induction vars with
  | nil => rfl
  | cons item rest ih =>
      obtain ⟨head, old⟩ := item
      by_cases hhead : head = name <;> simp [envSet, VEnv.set, hhead, ih]

/-- Variable-environment correspondence inside one root/function frame.

* no slot: the binding is retained with the same value;
* selected signature cell: retained structurally, but its stack value is stale;
* selected local: absent from the target environment. -/
inductive VRel (slots : SlotMap) (owner : Owner) (signature : List Ident) :
    WordEnv → WordEnv → Prop
  | nil : VRel slots owner signature [] []
  | unselected {name : Ident} {value : U256} {source target : WordEnv}
      (hslot : slotFor? slots owner name = none)
      (tail : VRel slots owner signature source target) :
      VRel slots owner signature ((name, value) :: source) ((name, value) :: target)
  | selectedSignature {name : Ident} {sourceValue targetValue : U256}
      {source target : WordEnv} {slot : Nat}
      (hslot : slotFor? slots owner name = some slot)
      (hsignature : name ∈ signature)
      (tail : VRel slots owner signature source target) :
      VRel slots owner signature ((name, sourceValue) :: source)
        ((name, targetValue) :: target)
  | selectedLocal {name : Ident} {value : U256}
      {source target : WordEnv} {slot : Nat}
      (hslot : slotFor? slots owner name = some slot)
      (hsignature : name ∉ signature)
      (tail : VRel slots owner signature source target) :
      VRel slots owner signature ((name, value) :: source) target

/-- Every currently bound selected source value is materialized in its slot.
Names not yet declared (or already restored out of scope) impose no condition. -/
def SlotsLoaded (slots : SlotMap) (owner : Owner) (source : WordEnv)
    (targetState : EvmState) : Prop :=
  ∀ name slot value,
    slotFor? slots owner name = some slot →
    envGet source name = some value →
    loadWord targetState.memory slot = value

/-- A slot is fresh with respect to the selected bindings that are live in the
current source environment.  Historical bindings from sibling lexical scopes
are deliberately ignored: the allocator is allowed to reuse their words once
`restore` removes them from the environment. -/
def SlotFreshForEnv (slots : SlotMap) (owner : Owner) (source : WordEnv)
    (writtenName : Ident) (writtenSlot : Nat) : Prop :=
  ∀ otherName otherSlot otherValue,
    otherName ≠ writtenName →
    slotFor? slots owner otherName = some otherSlot →
    envGet source otherName = some otherValue →
    writtenSlot + 32 ≤ otherSlot ∨ otherSlot + 32 ≤ writtenSlot

/-- Every selected binding currently present in the source environment belongs
to the static lexical-live set carried by the syntax-directed simulation. -/
def BoundSelectedIn (slots : SlotMap) (owner : Owner) (source : WordEnv)
    (live : SpillSet) : Prop :=
  ∀ name, name ∈ source.map Prod.fst →
    ∀ slot, slotFor? slots owner name = some slot →
      { owner, name } ∈ live

structure LiveCertified (selected : SpillSet) (frame : Frame)
    (live : SpillSet) : Prop where
  covered : ∃ maxLive ∈ (frameLives selected frame).sets,
    ∀ key ∈ live, key ∈ maxLive

def frameInitialLive (selected : SpillSet) (frame : Frame) : SpillSet :=
  selectedKeys selected frame.owner (frame.params ++ frame.returns)

theorem liveCertified_initial (selected : SpillSet) (frame : Frame) :
    LiveCertified selected frame (frameInitialLive selected frame) := by
  obtain ⟨maxLive, hmax, hsubset⟩ :=
    liveStmts_entry_covered selected frame.owner frame.body
      (frameInitialLive selected frame)
  exact ⟨⟨maxLive, by simpa [frameLives, frameInitialLive] using hmax, hsubset⟩⟩

/-- The current statement sequence's lexical trace is a subtrace of the
owning frame certificate retained in the checked layout. -/
def TraceCovered (selected : SpillSet) (frame : Frame) (live : SpillSet)
    (body : Block Op) : Prop :=
  ∀ liveSet ∈ (liveStmts selected frame.owner live body).1,
    liveSet ∈ (frameLives selected frame).sets

theorem traceCovered_frame (selected : SpillSet) (frame : Frame) :
    TraceCovered selected frame (frameInitialLive selected frame) frame.body := by
  intro liveSet hmem
  simpa [frameLives, frameInitialLive] using hmem

theorem TraceCovered.liveCertified {selected : SpillSet} {frame : Frame}
    {live : SpillSet} {body : Block Op}
    (htrace : TraceCovered selected frame live body) :
    LiveCertified selected frame live := by
  obtain ⟨maxLive, hmax, hsubset⟩ :=
    liveStmts_entry_covered selected frame.owner body live
  exact ⟨⟨maxLive, htrace maxLive hmax, hsubset⟩⟩

theorem TraceCovered.head {selected : SpillSet} {frame : Frame}
    {live : SpillSet} {stmt : Stmt Op} {rest : Block Op}
    (htrace : TraceCovered selected frame live (stmt :: rest)) :
    ∀ liveSet ∈ (liveStmt selected frame.owner live stmt).1,
      liveSet ∈ (frameLives selected frame).sets := by
  intro liveSet hmem
  apply htrace liveSet
  simp only [liveStmts]
  exact List.mem_append_left _ hmem

theorem TraceCovered.tail {selected : SpillSet} {frame : Frame}
    {live : SpillSet} {stmt : Stmt Op} {rest : Block Op}
    (htrace : TraceCovered selected frame live (stmt :: rest)) :
    TraceCovered selected frame (liveStmt selected frame.owner live stmt).2 rest := by
  intro liveSet hmem
  apply htrace liveSet
  simp only [liveStmts]
  exact List.mem_append_right _ hmem

theorem traceCovered_block {selected : SpillSet} {frame : Frame}
    {live : SpillSet} {body : Block Op}
    (hsets : ∀ liveSet ∈
      (liveStmt selected frame.owner live (.block body)).1,
      liveSet ∈ (frameLives selected frame).sets) :
    TraceCovered selected frame live body := by
  intro liveSet hmem
  apply hsets liveSet
  simpa [liveStmt, liveScope] using hmem

theorem traceCovered_cond {selected : SpillSet} {frame : Frame}
    {live : SpillSet} {condition : Expr Op} {body : Block Op}
    (hsets : ∀ liveSet ∈
      (liveStmt selected frame.owner live (.cond condition body)).1,
      liveSet ∈ (frameLives selected frame).sets) :
    TraceCovered selected frame live body := by
  intro liveSet hmem
  apply hsets liveSet
  simpa [liveStmt, liveScope] using hmem

theorem traceCovered_forInit {selected : SpillSet} {frame : Frame}
    {live : SpillSet} {init post body : Block Op} {condition : Expr Op}
    (hsets : ∀ liveSet ∈
      (liveStmt selected frame.owner live (.forLoop init condition post body)).1,
      liveSet ∈ (frameLives selected frame).sets) :
    TraceCovered selected frame live init := by
  intro liveSet hmem
  apply hsets liveSet
  simp only [liveStmt]
  exact List.mem_append_left _ (List.mem_append_left _ hmem)

theorem traceCovered_forBody {selected : SpillSet} {frame : Frame}
    {live : SpillSet} {init post body : Block Op} {condition : Expr Op}
    (hsets : ∀ liveSet ∈
      (liveStmt selected frame.owner live (.forLoop init condition post body)).1,
      liveSet ∈ (frameLives selected frame).sets) :
    TraceCovered selected frame (liveStmts selected frame.owner live init).2 body := by
  intro liveSet hmem
  apply hsets liveSet
  simp only [liveStmt, liveScope]
  exact List.mem_append_left _
    (List.mem_append_right (liveStmts selected frame.owner live init).1 hmem)

theorem traceCovered_forPost {selected : SpillSet} {frame : Frame}
    {live : SpillSet} {init post body : Block Op} {condition : Expr Op}
    (hsets : ∀ liveSet ∈
      (liveStmt selected frame.owner live (.forLoop init condition post body)).1,
      liveSet ∈ (frameLives selected frame).sets) :
    TraceCovered selected frame (liveStmts selected frame.owner live init).2 post := by
  intro liveSet hmem
  apply hsets liveSet
  simp only [liveStmt, liveScope]
  exact List.mem_append_right
    ((liveStmts selected frame.owner live init).1 ++
      (liveStmts selected frame.owner
        (liveStmts selected frame.owner live init).2 body).1) hmem

theorem envGet_name_mem {source : WordEnv} {name : Ident} {value : U256}
    (hget : envGet source name = some value) :
    name ∈ source.map Prod.fst := by
  induction source with
  | nil => simp [envGet] at hget
  | cons item rest ih =>
      obtain ⟨head, old⟩ := item
      rw [envGet_cons] at hget
      by_cases heq : head = name
      · simp [heq]
      · simp only [if_neg heq] at hget
        exact List.mem_cons_of_mem head (ih hget)

theorem envSet_keys (source : WordEnv) (name : Ident) (value : U256) :
    (envSet source name value).map Prod.fst = source.map Prod.fst := by
  induction source with
  | nil => rfl
  | cons item rest ih =>
      obtain ⟨head, old⟩ := item
      by_cases heq : head = name
      · simp [envSet, heq]
      · simp [envSet, heq, ih]

namespace BoundSelectedIn

theorem empty (slots : SlotMap) (owner : Owner) (live : SpillSet) :
    BoundSelectedIn slots owner [] live := by
  intro name hmem
  simp at hmem

theorem set {slots : SlotMap} {owner : Owner} {source : WordEnv}
    {live : SpillSet} (hbound : BoundSelectedIn slots owner source live)
    (name : Ident) (value : U256) :
    BoundSelectedIn slots owner (envSet source name value) live := by
  intro other hmem slot hslot
  rw [envSet_keys] at hmem
  exact hbound other hmem slot hslot

theorem prepend {slots : SlotMap} {owner : Owner} {source front : WordEnv}
    {live nextLive : SpillSet}
    (hbound : BoundSelectedIn slots owner source live)
    (hprefix : ∀ name, name ∈ front.map Prod.fst →
      ∀ slot, slotFor? slots owner name = some slot →
        { owner, name } ∈ nextLive)
    (htail : ∀ key ∈ live, key ∈ nextLive) :
    BoundSelectedIn slots owner (front ++ source) nextLive := by
  intro name hmem slot hslot
  simp only [List.map_append, List.mem_append] at hmem
  rcases hmem with hprefixMem | hsourceMem
  · exact hprefix name hprefixMem slot hslot
  · exact htail _ (hbound name hsourceMem slot hslot)

theorem of_keys_eq {slots : SlotMap} {owner : Owner} {left right : WordEnv}
    {live : SpillSet} (hbound : BoundSelectedIn slots owner left live)
    (hkeys : right.map Prod.fst = left.map Prod.fst) :
    BoundSelectedIn slots owner right live := by
  intro name hmem slot hslot
  rw [hkeys] at hmem
  exact hbound name hmem slot hslot

end BoundSelectedIn

/-- The checked lexical trace turns membership in the current live set into
the exact non-aliasing premise needed for a store. -/
theorem slotFreshForEnv_of_live {selected : SpillSet} {raw : Block Op}
    {layout : MemorySpillSelect.Layout}
    (hbuild : buildLayout base selected raw = some layout)
    (hcheck : layoutCheck base reserved selected layout = true)
    {frame : Frame} (hframe : frame ∈ frames raw)
    {maxLive live : SpillSet}
    (hmax : maxLive ∈ (frameLives selected frame).sets)
    (hlive : ∀ key ∈ live, key ∈ maxLive)
    {owner : Owner}
    {source : WordEnv} (hbound : BoundSelectedIn layout.slots owner source live)
    {name : Ident} {slot : Nat}
    (hname : { owner, name } ∈ maxLive)
    (hslot : slotFor? layout.slots owner name = some slot) :
    SlotFreshForEnv layout.slots owner source name slot := by
  intro otherName otherSlot otherValue hne hotherSlot hget
  have hotherLive : { owner, name := otherName } ∈ live :=
    hbound otherName (envGet_name_mem hget) otherSlot hotherSlot
  have hotherMax : { owner, name := otherName } ∈ maxLive :=
    hlive _ hotherLive
  have hkeysNe : ({ owner, name } : SpillKey) ≠ { owner, name := otherName } := by
    intro heq
    exact hne (congrArg SpillKey.name heq).symm
  have hslotsNe : slot ≠ otherSlot :=
    buildLayout_live_slots_ne hbuild hcheck hframe hmax hname hotherMax
      hkeysNe hslot hotherSlot
  exact layoutCheck_distinct_slots_disjoint hcheck
    (slotFor_mem_of_eq_some hslot) (slotFor_mem_of_eq_some hotherSlot) hslotsNe

theorem loadWord_eq_of_reservedUnchanged {base reserved slot : Nat}
    {before after : EvmState}
    (hrel : ReservedUnchanged base reserved before after)
    (hslot : base ≤ slot ∧ slot + 32 ≤ reserved) :
    loadWord after.memory slot = loadWord before.memory slot := by
  have hread : readBytes after.memory slot 32 =
      readBytes before.memory slot 32 := by
    unfold readBytes
    apply List.map_congr_left
    intro index hindex
    have hi : index < 32 := by simpa using hindex
    exact hrel (slot + index) (by omega) (by omega)
  have hform (memory : Nat → UInt8) :
      loadWord memory slot = (readBytes memory slot 32).foldl
        (fun (acc : U256) byte =>
          (acc <<< (8 : Nat)) ||| BitVec.ofNat 256 byte.toNat) 0 := by
    unfold loadWord readBytes
    rw [List.foldl_map]
  rw [hform after.memory, hform before.memory, hread]

namespace SlotsLoaded

theorem touchMemory {slots : SlotMap} {owner : Owner}
    {source : WordEnv} {state : EvmState} (hloaded : SlotsLoaded slots owner source state)
    (offset size : Nat) :
    SlotsLoaded slots owner source (YulSemantics.EVM.touchMemory state offset size) := by
  intro name slot value hslot hget
  simpa [YulSemantics.EVM.touchMemory] using hloaded name slot value hslot hget

theorem preserve_reserved {slots : SlotMap} {owner : Owner}
    {source : WordEnv} {before after : EvmState}
    (hloaded : SlotsLoaded slots owner source before)
    (hbounds : ∀ name slot, slotFor? slots owner name = some slot →
      base ≤ slot ∧ slot + 32 ≤ reserved)
    (hrel : ReservedUnchanged base reserved before after) :
    SlotsLoaded slots owner source after := by
  intro name slot value hslot hget
  rw [loadWord_eq_of_reservedUnchanged hrel (hbounds name slot hslot)]
  exact hloaded name slot value hslot hget

theorem setNoSlot {slots : SlotMap} {owner : Owner}
    {source : WordEnv} {state : EvmState}
    (hloaded : SlotsLoaded slots owner source state)
    {name : Ident} (hslot : slotFor? slots owner name = none) (value : U256) :
    SlotsLoaded slots owner (envSet source name value) state := by
  intro other otherSlot found hotherSlot hget
  have hne : other ≠ name := by
    intro heq
    subst other
    rw [hslot] at hotherSlot
    contradiction
  rw [envGet_envSet_other hne value] at hget
  exact hloaded other otherSlot found hotherSlot hget

theorem prependNoSlot {slots : SlotMap} {owner : Owner}
    {source : WordEnv} {state : EvmState}
    (hloaded : SlotsLoaded slots owner source state)
    {name : Ident} (hslot : slotFor? slots owner name = none) (value : U256) :
    SlotsLoaded slots owner ((name, value) :: source) state := by
  intro other otherSlot found hotherSlot hget
  rw [envGet_cons] at hget
  have hne : name ≠ other := by
    intro heq
    subst other
    rw [hslot] at hotherSlot
    contradiction
  simp only [if_neg hne] at hget
  exact hloaded other otherSlot found hotherSlot hget

theorem slotState_other {slots : SlotMap} {owner : Owner}
    {source : WordEnv} {before : EvmState}
    (hloaded : SlotsLoaded slots owner source before)
    {writtenName : Ident} {writtenSlot : Nat} {writtenValue : U256}
    (hdisjoint : SlotFreshForEnv slots owner source writtenName writtenSlot) :
    ∀ otherName otherSlot value,
      otherName ≠ writtenName →
      slotFor? slots owner otherName = some otherSlot →
      envGet source otherName = some value →
      loadWord (MemorySpillStateSound.slotState before writtenSlot writtenValue).memory
        otherSlot = value := by
  intro otherName otherSlot value hne hslot hget
  simp only [MemorySpillStateSound.slotState]
  rw [loadWord_storeWord_other before.memory writtenSlot otherSlot writtenValue
    (hdisjoint otherName otherSlot value hne hslot hget)]
  exact hloaded otherName otherSlot value hslot hget

theorem setSelected_store {slots : SlotMap} {owner : Owner}
    {source : WordEnv} {before : EvmState}
    (hloaded : SlotsLoaded slots owner source before)
    {name : Ident} {slot : Nat} (hslot : slotFor? slots owner name = some slot)
    (value : U256)
    (hdisjoint : SlotFreshForEnv slots owner source name slot) :
    SlotsLoaded slots owner (envSet source name value)
      (MemorySpillStateSound.slotState before slot value) := by
  intro otherName otherSlot found hotherSlot hget
  by_cases heq : otherName = name
  · subst otherName
    rw [hslot] at hotherSlot
    cases hotherSlot
    have hvalue := envGet_envSet_self hget
    subst found
    exact slotState_load before slot value
  · apply slotState_other hloaded hdisjoint otherName otherSlot found heq
      hotherSlot
    rwa [envGet_envSet_other heq value] at hget

theorem prependSelected_store {slots : SlotMap} {owner : Owner}
    {source : WordEnv} {before : EvmState}
    (hloaded : SlotsLoaded slots owner source before)
    {name : Ident} {slot : Nat} (hslot : slotFor? slots owner name = some slot)
    (value : U256)
    (hdisjoint : SlotFreshForEnv slots owner source name slot) :
    SlotsLoaded slots owner ((name, value) :: source)
      (MemorySpillStateSound.slotState before slot value) := by
  intro otherName otherSlot found hotherSlot hget
  rw [envGet_cons] at hget
  by_cases heq : name = otherName
  · subst otherName
    simp at hget
    cases hget
    rw [hslot] at hotherSlot
    cases hotherSlot
    exact slotState_load before slot value
  · simp only [if_neg heq] at hget
    exact slotState_other hloaded hdisjoint otherName otherSlot found (Ne.symm heq)
      hotherSlot hget

end SlotsLoaded

theorem scratchRel_touchMemory_right {left right : EvmState}
    (hrel : ScratchRel base reserved left right) (offset size : Nat) :
    ScratchRel base reserved left (YulSemantics.EVM.touchMemory right offset size) := by
  constructor
  · simpa [YulSemantics.EVM.touchMemory, observables] using hrel.observables_eq
  · intro address houtside
    simpa [YulSemantics.EVM.touchMemory] using hrel.memory_eq address houtside

/-- Complete per-frame simulation relation. -/
structure FrameRel (slots : SlotMap) (owner : Owner) (signature : List Ident)
    (source : WordEnv) (sourceState : EvmState)
    (target : WordEnv) (targetState : EvmState) : Prop where
  vars : VRel slots owner signature source target
  loaded : SlotsLoaded slots owner source targetState
  scratch : ScratchRel base reserved sourceState targetState

namespace VRel

theorem empty (slots : SlotMap) (owner : Owner) (signature : List Ident) :
    VRel slots owner signature [] [] := .nil

theorem keys {slots : SlotMap} {owner : Owner} {signature : List Ident}
    {source target : WordEnv}
    (hrel : VRel slots owner signature source target) :
    target.map Prod.fst =
      (source.map Prod.fst).filter
        (retainedBinding slots owner signature) := by
  induction hrel with
  | nil => rfl
  | unselected hslot tail ih =>
      simp [retainedBinding, hslot, ih]
  | selectedSignature hslot hsignature tail ih =>
      simp [retainedBinding, hslot, List.contains_eq_mem, hsignature, ih]
  | selectedLocal hslot hsignature tail ih =>
      simp [retainedBinding, hslot, List.contains_eq_mem, hsignature, ih]

theorem length_eq_filter {slots : SlotMap} {owner : Owner}
    {signature : List Ident} {source target : WordEnv}
    (hrel : VRel slots owner signature source target) :
    target.length =
      ((source.map Prod.fst).filter
        (retainedBinding slots owner signature)).length := by
  simpa using congrArg List.length hrel.keys

/-- Lookup of an unselected binding agrees exactly. -/
theorem get_of_no_slot {slots : SlotMap} {owner : Owner} {signature : List Ident}
    {source target : WordEnv}
    (hrel : VRel slots owner signature source target) {name : Ident}
    (hslot : slotFor? slots owner name = none) :
    envGet source name = envGet target name := by
  induction hrel with
  | nil => rfl
  | @unselected head value source target hhead tail ih =>
      rw [envGet_cons, envGet_cons]
      by_cases heq : head = name
      · simp [heq]
      · simp [heq, ih]
  | @selectedSignature head sourceValue targetValue source target slot
      hhead hsignature tail ih =>
      have hne : head ≠ name := by
        intro heq
        subst head
        rw [hslot] at hhead
        contradiction
      rw [envGet_cons, envGet_cons]
      simp [hne, ih]
  | @selectedLocal head value source target slot hhead hsignature tail ih =>
      have hne : head ≠ name := by
        intro heq
        subst head
        rw [hslot] at hhead
        contradiction
      rw [envGet_cons]
      simp [hne, ih]

/-- A selected signature binding remains structurally present in the target,
even though its target value may be stale until copyback. -/
theorem targetGet_of_selectedSignature {slots : SlotMap} {owner : Owner}
    {signature : List Ident} {source target : WordEnv}
    (hrel : VRel slots owner signature source target)
    {name : Ident} {slot : Nat} (hslot : slotFor? slots owner name = some slot)
    (hsignature : name ∈ signature) {sourceValue : U256}
    (hget : envGet source name = some sourceValue) :
    ∃ targetValue, envGet target name = some targetValue := by
  induction hrel with
  | nil => simp [envGet] at hget
  | @unselected head value source target hhead tail ih =>
      have hne : head ≠ name := by
        intro heq
        subst head
        rw [hslot] at hhead
        contradiction
      rw [envGet_cons] at hget
      simp only [if_neg hne] at hget
      obtain ⟨targetValue, htarget⟩ := ih hget
      exact ⟨targetValue, by rw [envGet_cons]; simp [hne, htarget]⟩
  | @selectedSignature head sourceHead targetHead source target found
      hhead hheadSignature tail ih =>
      rw [envGet_cons] at hget
      by_cases heq : head = name
      · subst head
        exact ⟨targetHead, by simp [envGet_cons]⟩
      · simp only [if_neg heq] at hget
        obtain ⟨targetValue, htarget⟩ := ih hget
        exact ⟨targetValue, by rw [envGet_cons]; simp [heq, htarget]⟩
  | @selectedLocal head value source target found hhead hheadNotSignature tail ih =>
      rw [envGet_cons] at hget
      have hne : head ≠ name := by
        intro heq
        subst head
        exact hheadNotSignature hsignature
      simp only [if_neg hne] at hget
      exact ih hget

/-- A function-call entry environment is related to itself before selected
signature cells are initialized in memory. -/
theorem signatureSelf (slots : SlotMap) (owner : Owner) (signature : List Ident) :
    ∀ vars : WordEnv, (∀ item ∈ vars, item.1 ∈ signature) →
      VRel slots owner signature vars vars
  | [], _ => .nil
  | (name, value) :: rest, hall => by
      have hname : name ∈ signature := hall (name, value) (by simp)
      have hrest : ∀ item ∈ rest, item.1 ∈ signature := by
        intro item hmem
        exact hall item (by simp [hmem])
      cases hslot : slotFor? slots owner name with
      | none => exact .unselected hslot (signatureSelf slots owner signature rest hrest)
      | some slot =>
          exact .selectedSignature hslot hname
            (signatureSelf slots owner signature rest hrest)

theorem setNoSlot {slots : SlotMap} {owner : Owner} {signature : List Ident}
    {source target : WordEnv} (hrel : VRel slots owner signature source target)
    {name : Ident} (hslot : slotFor? slots owner name = none) (value : U256) :
    VRel slots owner signature (envSet source name value)
      (envSet target name value) := by
  induction hrel with
  | nil => exact .nil
  | @unselected head old source target hhead tail ih =>
      by_cases heq : head = name
      · subst head
        simp only [envSet]
        exact .unselected hhead tail
      · simp only [envSet, if_neg heq]
        exact .unselected hhead ih
  | @selectedSignature head sourceValue targetValue source target slot
      hhead hsignature tail ih =>
      have hne : head ≠ name := by
        intro heq
        subst head
        rw [hslot] at hhead
        contradiction
      simp only [envSet, if_neg hne]
      exact .selectedSignature hhead hsignature ih
  | @selectedLocal head old source target slot hhead hsignature tail ih =>
      have hne : head ≠ name := by
        intro heq
        subst head
        rw [hslot] at hhead
        contradiction
      simp only [envSet, if_neg hne]
      exact .selectedLocal hhead hsignature ih

theorem setSelected {slots : SlotMap} {owner : Owner} {signature : List Ident}
    {source target : WordEnv} (hrel : VRel slots owner signature source target)
    {name : Ident} {slot : Nat} (hslot : slotFor? slots owner name = some slot)
    (value : U256) :
    VRel slots owner signature (envSet source name value) target := by
  induction hrel with
  | nil => exact .nil
  | @unselected head old source target hhead tail ih =>
      have hne : head ≠ name := by
        intro heq
        subst head
        rw [hslot] at hhead
        contradiction
      simp only [envSet, if_neg hne]
      exact .unselected hhead ih
  | @selectedSignature head sourceValue targetValue source target found
      hhead hsignature tail ih =>
      by_cases heq : head = name
      · subst head
        simp only [envSet]
        exact .selectedSignature hhead hsignature tail
      · simp only [envSet, if_neg heq]
        exact .selectedSignature hhead hsignature ih
  | @selectedLocal head old source target found hhead hsignature tail ih =>
      by_cases heq : head = name
      · subst head
        simp only [envSet]
        exact .selectedLocal hhead hsignature tail
      · simp only [envSet, if_neg heq]
        exact .selectedLocal hhead hsignature ih

/-- A selected signature cell is retained in the target environment.  Its
stack value is intentionally unconstrained while memory is authoritative, so
copyback may update that target cell without changing the source relation. -/
theorem setTargetSelectedSignature {slots : SlotMap} {owner : Owner}
    {signature : List Ident} {source target : WordEnv}
    (hrel : VRel slots owner signature source target)
    {name : Ident} {slot : Nat} (hslot : slotFor? slots owner name = some slot)
    (hsignature : name ∈ signature) (value : U256) :
    VRel slots owner signature source (envSet target name value) := by
  induction hrel with
  | nil => exact .nil
  | @unselected head old source target hhead tail ih =>
      have hne : head ≠ name := by
        intro heq
        subst head
        rw [hslot] at hhead
        contradiction
      simp only [envSet, if_neg hne]
      exact .unselected hhead ih
  | @selectedSignature head sourceValue targetValue source target found
      hhead hheadSignature tail ih =>
      by_cases heq : head = name
      · subst head
        simp only [envSet]
        exact .selectedSignature hhead hheadSignature tail
      · simp only [envSet, if_neg heq]
        exact .selectedSignature hhead hheadSignature ih
  | @selectedLocal head old source target found hhead hheadNotSignature tail ih =>
      have hne : head ≠ name := by
        intro heq
        subst head
        exact hheadNotSignature hsignature
      exact .selectedLocal hhead hheadNotSignature ih

end VRel

/-! ## Lexical cut stack

Source scopes retain selected locals in `VEnv`, while target scopes omit them.
Consequently the two `restore` calls drop different numeric prefixes.  A cut
records both lengths at the same `VRel` constructor boundary.  Cuts nest
recursively over the suffix selected by the preceding cut; popping a scope is
therefore a structural operation, not an arithmetic alignment assumption. -/

structure CutMark where
  sourceLen : Nat
  targetLen : Nat
  deriving Repr, DecidableEq

def suffixAt (vars : WordEnv) (length : Nat) : WordEnv :=
  vars.drop (vars.length - length)

theorem suffixAt_append_of_le (pre vars : WordEnv) {length : Nat}
    (hle : length ≤ vars.length) :
    suffixAt (pre ++ vars) length = suffixAt vars length := by
  unfold suffixAt
  have hsub : (pre ++ vars).length - length =
      pre.length + (vars.length - length) := by
    simp only [List.length_append]
    omega
  rw [hsub, ← List.drop_drop]
  simp

theorem suffixAt_keys_of_keys_eq {left right : WordEnv}
    (hkeys : right.map Prod.fst = left.map Prod.fst) (length : Nat) :
    (suffixAt right length).map Prod.fst =
      (suffixAt left length).map Prod.fst := by
  have hlength : right.length = left.length := by
    simpa using congrArg List.length hkeys
  unfold suffixAt
  rw [hlength, List.map_drop, List.map_drop, hkeys]

namespace VRel

/-- A `VRel` may be cut at any source suffix boundary.  The corresponding
target suffix contains exactly the retained bindings in that source suffix. -/
theorem suffixSource {slots : SlotMap} {owner : Owner}
    {signature : List Ident} {source target : WordEnv}
    (hrel : VRel slots owner signature source target) :
    ∀ sourceLen, sourceLen ≤ source.length →
      VRel slots owner signature (suffixAt source sourceLen)
        (suffixAt target
          (((suffixAt source sourceLen).map Prod.fst).filter
            (retainedBinding slots owner signature)).length) := by
  intro sourceLen hsourceLen
  induction hrel generalizing sourceLen with
  | nil =>
      have : sourceLen = 0 := by simpa using hsourceLen
      subst sourceLen
      exact .nil
  | @unselected name value source target hslot tail ih =>
      by_cases hfull : sourceLen = ((name, value) :: source).length
      · subst sourceLen
        have hcurrent : VRel slots owner signature
            ((name, value) :: source) ((name, value) :: target) :=
          .unselected hslot tail
        simpa [suffixAt, hcurrent.length_eq_filter] using hcurrent
      · have htailLen : sourceLen ≤ source.length := by
          simp only [List.length_cons] at hsourceLen hfull
          omega
        have hsource : suffixAt ((name, value) :: source) sourceLen =
            suffixAt source sourceLen :=
          suffixAt_append_of_le [(name, value)] source htailLen
        have htail := ih sourceLen htailLen
        let targetLen :=
          (((suffixAt source sourceLen).map Prod.fst).filter
            (retainedBinding slots owner signature)).length
        have htargetLen : targetLen ≤ target.length := by
          have hlength := htail.length_eq_filter
          have heq : (suffixAt target targetLen).length = targetLen := by
            simpa [targetLen] using hlength
          simp only [suffixAt, List.length_drop] at heq
          omega
        have htarget : suffixAt ((name, value) :: target) targetLen =
            suffixAt target targetLen :=
          suffixAt_append_of_le [(name, value)] target htargetLen
        simpa [hsource, htarget, targetLen] using htail
  | @selectedSignature name sourceValue targetValue source target slot
      hslot hsignature tail ih =>
      by_cases hfull : sourceLen = ((name, sourceValue) :: source).length
      · subst sourceLen
        have hcurrent : VRel slots owner signature
            ((name, sourceValue) :: source) ((name, targetValue) :: target) :=
          .selectedSignature hslot hsignature tail
        simpa [suffixAt, hcurrent.length_eq_filter] using hcurrent
      · have htailLen : sourceLen ≤ source.length := by
          simp only [List.length_cons] at hsourceLen hfull
          omega
        have hsource : suffixAt ((name, sourceValue) :: source) sourceLen =
            suffixAt source sourceLen :=
          suffixAt_append_of_le [(name, sourceValue)] source htailLen
        have htail := ih sourceLen htailLen
        let targetLen :=
          (((suffixAt source sourceLen).map Prod.fst).filter
            (retainedBinding slots owner signature)).length
        have htargetLen : targetLen ≤ target.length := by
          have hlength := htail.length_eq_filter
          have heq : (suffixAt target targetLen).length = targetLen := by
            simpa [targetLen] using hlength
          simp only [suffixAt, List.length_drop] at heq
          omega
        have htarget : suffixAt ((name, targetValue) :: target) targetLen =
            suffixAt target targetLen :=
          suffixAt_append_of_le [(name, targetValue)] target htargetLen
        simpa [hsource, htarget, targetLen] using htail
  | @selectedLocal name value source target slot hslot hsignature tail ih =>
      by_cases hfull : sourceLen = ((name, value) :: source).length
      · subst sourceLen
        have hcurrent : VRel slots owner signature
            ((name, value) :: source) target :=
          .selectedLocal hslot hsignature tail
        simpa [suffixAt, hcurrent.length_eq_filter] using hcurrent
      · have htailLen : sourceLen ≤ source.length := by
          simp only [List.length_cons] at hsourceLen hfull
          omega
        have hsource : suffixAt ((name, value) :: source) sourceLen =
            suffixAt source sourceLen :=
          suffixAt_append_of_le [(name, value)] source htailLen
        have htail := ih sourceLen htailLen
        simpa [hsource] using htail

theorem suffix {slots : SlotMap} {owner : Owner}
    {signature : List Ident} {source target : WordEnv}
    (hrel : VRel slots owner signature source target)
    {sourceLen targetLen : Nat}
    (hsourceLen : sourceLen ≤ source.length)
    (_htargetLen : targetLen ≤ target.length)
    (hcount : targetLen =
      (((suffixAt source sourceLen).map Prod.fst).filter
        (retainedBinding slots owner signature)).length) :
    VRel slots owner signature (suffixAt source sourceLen)
      (suffixAt target targetLen) := by
  subst targetLen
  exact hrel.suffixSource sourceLen hsourceLen

end VRel

structure CutRel (slots : SlotMap) (owner : Owner) (signature : List Ident)
    (source target : WordEnv) (mark : CutMark) : Prop where
  source_le : mark.sourceLen ≤ source.length
  target_le : mark.targetLen ≤ target.length
  retained_count : mark.targetLen =
    (((suffixAt source mark.sourceLen).map Prod.fst).filter
      (retainedBinding slots owner signature)).length

inductive CutStackRel (slots : SlotMap) (owner : Owner)
    (signature : List Ident) :
    WordEnv → WordEnv → List CutMark → Prop
  | nil (source target) : CutStackRel slots owner signature source target []
  | cons {source target mark rest}
      (head : CutRel slots owner signature source target mark)
      (tail : CutStackRel slots owner signature
        (suffixAt source mark.sourceLen) (suffixAt target mark.targetLen) rest) :
      CutStackRel slots owner signature source target (mark :: rest)

namespace CutRel

theorem of_keys_eq {slots : SlotMap} {owner : Owner} {signature : List Ident}
    {source target source' target' : WordEnv} {mark : CutMark}
    (hrel : CutRel slots owner signature source target mark)
    (hsource : source'.map Prod.fst = source.map Prod.fst)
    (htarget : target'.map Prod.fst = target.map Prod.fst) :
    CutRel slots owner signature source' target' mark := by
  have hsourceLength : source'.length = source.length := by
    simpa using congrArg List.length hsource
  have htargetLength : target'.length = target.length := by
    simpa using congrArg List.length htarget
  refine ⟨by simpa [hsourceLength] using hrel.source_le,
    by simpa [htargetLength] using hrel.target_le, ?_⟩
  rw [suffixAt_keys_of_keys_eq hsource]
  exact hrel.retained_count

end CutRel

namespace CutStackRel

theorem of_keys_eq {slots : SlotMap} {owner : Owner} {signature : List Ident}
    {source target source' target' : WordEnv} {cuts : List CutMark}
    (hrel : CutStackRel slots owner signature source target cuts)
    (hsource : source'.map Prod.fst = source.map Prod.fst)
    (htarget : target'.map Prod.fst = target.map Prod.fst) :
    CutStackRel slots owner signature source' target' cuts := by
  induction hrel generalizing source' target' with
  | nil => exact .nil _ _
  | @cons source target mark rest head tail ih =>
      apply CutStackRel.cons (head.of_keys_eq hsource htarget)
      apply ih
      · exact suffixAt_keys_of_keys_eq hsource mark.sourceLen
      · exact suffixAt_keys_of_keys_eq htarget mark.targetLen

end CutStackRel

structure EnvRel (slots : SlotMap) (owner : Owner) (signature : List Ident)
    (source target : WordEnv) (cuts : List CutMark) : Prop where
  vars : VRel slots owner signature source target
  cuts : CutStackRel slots owner signature source target cuts

namespace EnvRel

theorem empty (slots : SlotMap) (owner : Owner) (signature : List Ident) :
    EnvRel slots owner signature [] [] [] := ⟨.nil, .nil [] []⟩

theorem push {slots : SlotMap} {owner : Owner} {signature : List Ident}
    {source target : WordEnv} {cuts : List CutMark}
    (hrel : EnvRel slots owner signature source target cuts) :
    EnvRel slots owner signature source target
      ({ sourceLen := source.length, targetLen := target.length } :: cuts) := by
  refine ⟨hrel.vars, .cons ?_ ?_⟩
  · refine ⟨Nat.le_refl _, Nat.le_refl _, ?_⟩
    simpa [suffixAt] using hrel.vars.length_eq_filter
  · simpa [suffixAt] using hrel.cuts

theorem prepend {slots : SlotMap} {owner : Owner} {signature : List Ident}
    {source target : WordEnv} {cuts : List CutMark}
    (sourcePrefix targetPrefix : WordEnv)
    (hrel : EnvRel slots owner signature source target cuts)
    (hvars : VRel slots owner signature
      (sourcePrefix ++ source) (targetPrefix ++ target)) :
    EnvRel slots owner signature
      (sourcePrefix ++ source) (targetPrefix ++ target) cuts := by
  refine ⟨hvars, ?_⟩
  cases hrel.cuts with
  | nil => exact .nil _ _
  | cons head tail =>
      have hsource := suffixAt_append_of_le sourcePrefix source head.source_le
      have htarget := suffixAt_append_of_le targetPrefix target head.target_le
      apply CutStackRel.cons
      · exact {
          source_le := le_trans head.source_le (by simp)
          target_le := le_trans head.target_le (by simp)
          retained_count := by simpa [hsource] using head.retained_count }
      · simpa [hsource, htarget] using tail

theorem setNoSlot {slots : SlotMap} {owner : Owner} {signature : List Ident}
    {source target : WordEnv} {cuts : List CutMark}
    (hrel : EnvRel slots owner signature source target cuts)
    {name : Ident} (hslot : slotFor? slots owner name = none) (value : U256) :
    EnvRel slots owner signature (envSet source name value)
      (envSet target name value) cuts := by
  refine ⟨hrel.vars.setNoSlot hslot value, hrel.cuts.of_keys_eq ?_ ?_⟩
  · exact envSet_keys source name value
  · exact envSet_keys target name value

theorem setSelected {slots : SlotMap} {owner : Owner}
    {signature : List Ident} {source target : WordEnv} {cuts : List CutMark}
    (hrel : EnvRel slots owner signature source target cuts)
    {name : Ident} {slot : Nat} (hslot : slotFor? slots owner name = some slot)
    (value : U256) :
    EnvRel slots owner signature (envSet source name value) target cuts := by
  refine ⟨hrel.vars.setSelected hslot value, hrel.cuts.of_keys_eq ?_ rfl⟩
  exact envSet_keys source name value

theorem setTargetSelectedSignature {slots : SlotMap} {owner : Owner}
    {signature : List Ident} {source target : WordEnv} {cuts : List CutMark}
    (hrel : EnvRel slots owner signature source target cuts)
    {name : Ident} {slot : Nat} (hslot : slotFor? slots owner name = some slot)
    (hsignature : name ∈ signature) (value : U256) :
    EnvRel slots owner signature source (envSet target name value) cuts := by
  refine ⟨hrel.vars.setTargetSelectedSignature hslot hsignature value,
    hrel.cuts.of_keys_eq rfl ?_⟩
  exact envSet_keys target name value

theorem pop {slots : SlotMap} {owner : Owner} {signature : List Ident}
    {outerSource outerTarget source target : WordEnv}
    {mark : CutMark} {cuts : List CutMark}
    (hsource : mark.sourceLen = outerSource.length)
    (htarget : mark.targetLen = outerTarget.length)
    (hrel : EnvRel slots owner signature source target (mark :: cuts)) :
    EnvRel slots owner signature (@restore G outerSource source)
      (@restore D outerTarget target) cuts := by
  cases hrel.cuts with
  | cons head tail =>
      have hsourceRestore :
          @restore G outerSource source = suffixAt source mark.sourceLen := by
        simp [restore, suffixAt, hsource]
      have htargetRestore :
          @restore D outerTarget target = suffixAt target mark.targetLen := by
        simp [restore, suffixAt, htarget]
      rw [hsourceRestore, htargetRestore]
      exact ⟨hrel.vars.suffix head.source_le head.target_le
        head.retained_count, tail⟩

end EnvRel

def AboveUnchanged (cutoff reserved : Nat) (before after : EvmState) : Prop :=
  ∀ address, cutoff ≤ address → address < reserved →
    after.memory address = before.memory address

def ReturnsSynced (returns : List Ident) (source target : WordEnv) : Prop :=
  ∀ name, name ∈ returns → envGet source name = envGet target name

def EnvAgreesOutside (names : List Ident) (before after : WordEnv) : Prop :=
  ∀ name, name ∉ names → envGet after name = envGet before name

namespace EnvAgreesOutside

theorem refl (names : List Ident) (vars : WordEnv) :
    EnvAgreesOutside names vars vars := by
  intro name hname
  rfl

theorem set (vars : WordEnv) (name : Ident) (value : U256) :
    EnvAgreesOutside [name] vars (envSet vars name value) := by
  intro other hother
  rw [envGet_envSet_other (by simpa using hother) value]

end EnvAgreesOutside

namespace AboveUnchanged

theorem refl (cutoff reserved : Nat) (state : EvmState) :
    AboveUnchanged cutoff reserved state state := by
  intro _ _ _
  rfl

theorem trans {cutoff reserved : Nat} {first second third : EvmState}
    (hleft : AboveUnchanged cutoff reserved first second)
    (hright : AboveUnchanged cutoff reserved second third) :
    AboveUnchanged cutoff reserved first third := by
  intro address hcutoff hreserved
  rw [hright address hcutoff hreserved, hleft address hcutoff hreserved]

theorem mono {low high reserved : Nat} {before after : EvmState}
    (hrel : AboveUnchanged low reserved before after) (hle : low ≤ high) :
    AboveUnchanged high reserved before after := by
  intro address hhigh hreserved
  exact hrel address (le_trans hle hhigh) hreserved

theorem of_reserved {base cutoff reserved : Nat} {before after : EvmState}
    (hbase : base ≤ cutoff)
    (hrel : ReservedUnchanged base reserved before after) :
    AboveUnchanged cutoff reserved before after := by
  intro address hcutoff hreserved
  exact hrel address (le_trans hbase hcutoff) hreserved

theorem slotState {cutoff reserved slot : Nat} {value : U256}
    (hslot : slot + 32 ≤ cutoff) (state : EvmState) :
    AboveUnchanged cutoff reserved state
      (MemorySpillStateSound.slotState state slot value) := by
  intro address hcutoff hreserved
  exact storeWord_reserved state.memory (Or.inl hslot)
    address hcutoff hreserved

end AboveUnchanged

def ResultSlotsLoaded (slots : SlotMap) (owner : Owner) (source : WordEnv) :
    BuiltinResult U256 EvmState → Prop
  | .ok _ state | .halt state => SlotsLoaded slots owner source state

def ResultAboveUnchanged (cutoff reserved : Nat) (before : EvmState) :
    BuiltinResult U256 EvmState → Prop
  | .ok _ after | .halt after => AboveUnchanged cutoff reserved before after

theorem guardedBuiltin_sim {slots : SlotMap} {owner : Owner}
    {source : WordEnv} {left right : EvmState}
    {op : Op} {args : List U256}
    {leftResult : BuiltinResult U256 EvmState}
    (hexternals : GuardedExternals calls creates base reserved)
    (hscratch : ScratchRel base reserved left right)
    (hbuiltin : (guardedEvm calls creates base reserved).Builtin
      op args left leftResult)
    (hloaded : SlotsLoaded slots owner source right)
    (hbounds : ∀ name slot, slotFor? slots owner name = some slot →
      base ≤ slot ∧ slot + 32 ≤ reserved)
    {cutoff : Nat} (hcutoff : base ≤ cutoff) :
    ∃ rightResult,
      (evmWithExternal calls creates).Builtin op args right rightResult ∧
      ResultRel base reserved leftResult rightResult ∧
      ResultSlotsLoaded slots owner source rightResult ∧
      ResultAboveUnchanged cutoff reserved right rightResult := by
  obtain ⟨rightResult, hright, hresult⟩ :=
    guarded_builtin_transport hexternals hscratch hbuiltin
  have hreserved := guarded_builtin_reserved hright
  refine ⟨rightResult, hright.1, hresult, ?_, ?_⟩
  · cases rightResult <;>
      exact SlotsLoaded.preserve_reserved hloaded hbounds hreserved
  · cases rightResult <;>
      exact AboveUnchanged.of_reserved hcutoff hreserved

structure ScopedFrameRel (slots : SlotMap) (owner : Owner)
    (signature : List Ident) (cuts : List CutMark)
    (source : WordEnv) (sourceState : EvmState)
    (target : WordEnv) (targetState : EvmState) : Prop where
  env : EnvRel slots owner signature source target cuts
  loaded : SlotsLoaded slots owner source targetState
  scratch : ScratchRel base reserved sourceState targetState

/-- Function-call entry before the inserted parameter/return prologue has
materialized selected signature cells in memory. -/
structure EntryFrameRel (slots : SlotMap) (owner : Owner)
    (signature : List Ident) (source : WordEnv) (sourceState : EvmState)
    (target : WordEnv) (targetState : EvmState) : Prop where
  env : EnvRel slots owner signature source target []
  scratch : ScratchRel base reserved sourceState targetState

namespace EntryFrameRel

theorem exactSignature (slots : SlotMap) (owner : Owner)
    (signature : List Ident) (vars : WordEnv)
    (hall : ∀ item ∈ vars, item.1 ∈ signature)
    (sourceState targetState : EvmState)
    (hscratch : ScratchRel base reserved sourceState targetState) :
    EntryFrameRel (base := base) (reserved := reserved)
      slots owner signature vars sourceState vars targetState := by
  exact {
    env := ⟨VRel.signatureSelf slots owner signature vars hall,
      .nil vars vars⟩
    scratch := hscratch }

end EntryFrameRel

/-- Dynamic frame state paired with the static lexical-live certificate used
to justify intentional slot reuse. -/
structure LiveFrameRel (selected : SpillSet) (layout : MemorySpillSelect.Layout)
    (frame : Frame)
    (signature : List Ident) (cuts : List CutMark) (live : SpillSet)
    (source : WordEnv) (sourceState : EvmState)
    (target : WordEnv) (targetState : EvmState) : Prop where
  frameRel : ScopedFrameRel (base := base) (reserved := reserved)
    layout.slots frame.owner signature cuts source sourceState target targetState
  bound : BoundSelectedIn layout.slots frame.owner source live
  certified : LiveCertified selected frame live

theorem LiveFrameRel.slotFresh {selected : SpillSet} {raw : Block Op}
    {layout : MemorySpillSelect.Layout} {frame : Frame} {signature : List Ident}
    {cuts : List CutMark} {live : SpillSet}
    {source target : WordEnv} {sourceState targetState : EvmState}
    (hrel : LiveFrameRel (base := base) (reserved := reserved)
      selected layout frame signature cuts live source sourceState target targetState)
    (hbuild : buildLayout base selected raw = some layout)
    (hcheck : layoutCheck base reserved selected layout = true)
    (hframe : frame ∈ frames raw)
    {name : Ident} {slot : Nat}
    (hname : { owner := frame.owner, name } ∈ live)
    (hslot : slotFor? layout.slots frame.owner name = some slot) :
    SlotFreshForEnv layout.slots frame.owner source name slot := by
  obtain ⟨maxLive, hmax, hsubset⟩ := hrel.certified.covered
  exact slotFreshForEnv_of_live hbuild hcheck hframe hmax hsubset hrel.bound
    (hsubset _ hname) hslot

/-! ## Syntax-indexed simulation interface -/

def rewriteCode (slots : SlotMap) (owner : Owner) (exitCopies : Block Op) :
    Code Op → Code Op
  | .expr expression => .expr (rewriteExpr slots owner expression)
  | .args args => .args (rewriteArgs slots owner args)
  | .stmt statement => .stmts (rewriteStmt slots owner exitCopies statement)
  | .stmts statements => .stmts (rewriteStmts slots owner exitCopies statements)
  | .loop condition post body =>
      .loop (rewriteExpr slots owner condition)
        (rewriteStmts slots owner exitCopies post)
        (rewriteStmts slots owner exitCopies body)

def liveAfterCode (selected : SpillSet) (owner : Owner) (live : SpillSet) :
    Code Op → SpillSet
  | .expr _ | .args _ | .loop _ _ _ => live
  | .stmt statement => (liveStmt selected owner live statement).2
  | .stmts statements => (liveStmts selected owner live statements).2

def CodeTraceCovered (selected : SpillSet) (frame : Frame) (live : SpillSet) :
    Code Op → Prop
  | .expr _ | .args _ => True
  | .stmt statement =>
      ∀ liveSet ∈ (liveStmt selected frame.owner live statement).1,
        liveSet ∈ (frameLives selected frame).sets
  | .stmts statements => TraceCovered selected frame live statements
  | .loop _ post body =>
      TraceCovered selected frame live post ∧
        TraceCovered selected frame live body

def ResultLiveFrameRel (selected : SpillSet) (layout : MemorySpillSelect.Layout)
    (frame : Frame)
    (signature : List Ident) (cuts : List CutMark) (live : SpillSet)
    (sourceEnv targetEnv : WordEnv) (code : Code Op) : Res G → Res D → Prop
  | .eres (.vals values sourceState), .eres (.vals targetValues targetState) =>
      targetValues = values ∧
        LiveFrameRel (base := base) (reserved := reserved)
          selected layout frame signature cuts live
          sourceEnv sourceState targetEnv targetState
  | .eres (.halt sourceState), .eres (.halt targetState) =>
      LiveFrameRel (base := base) (reserved := reserved)
        selected layout frame signature cuts live
        sourceEnv sourceState targetEnv targetState
  | .sres source sourceState outcome,
      .sres target targetState targetOutcome =>
      targetOutcome = outcome ∧
        LiveFrameRel (base := base) (reserved := reserved)
          selected layout frame signature cuts
          (liveAfterCode selected frame.owner live code)
          source sourceState target targetState
  | _, _ => False

def ResAboveUnchanged (cutoff reserved : Nat) (before : EvmState) :
    Res D → Prop
  | .eres (.vals _ after) | .eres (.halt after)
  | .sres _ after _ => AboveUnchanged cutoff reserved before after

namespace ScopedFrameRel

theorem rootInitial (slots : SlotMap) (sourceState : EvmState) :
    ScopedFrameRel (base := base) (reserved := reserved)
      slots none [] [] [] sourceState [] sourceState := by
  refine ⟨EnvRel.empty slots none [], ?_, ScratchRel.refl base reserved sourceState⟩
  intro name slot value _ hget
  simp [envGet] at hget

theorem observable_eq {slots : SlotMap} {owner : Owner}
    {signature : List Ident} {cuts : List CutMark}
    {source target : WordEnv} {sourceState targetState : EvmState}
    (hrel : ScopedFrameRel (base := base) (reserved := reserved)
      slots owner signature cuts source sourceState target targetState) :
    observables sourceState = observables targetState :=
  hrel.scratch.observables_eq

end ScopedFrameRel

namespace LiveFrameRel

theorem rootInitial {raw : Block Op} {result : Result} {guards : List Nat}
    (_hfacts : SpillFacts raw result guards) (sourceState : EvmState) :
    let guarded := resolveMemoryGuardStmts result.base result.reserved raw
    let frame : Frame := { owner := none, params := [], returns := [], body := guarded }
    LiveFrameRel (base := result.base) (reserved := result.reserved)
      result.selection result.layout frame [] []
      (frameInitialLive result.selection frame)
      [] sourceState [] sourceState := by
  dsimp only
  let guarded := resolveMemoryGuardStmts result.base result.reserved raw
  let frame : Frame := { owner := none, params := [], returns := [], body := guarded }
  have hscoped : ScopedFrameRel (base := result.base) (reserved := result.reserved)
      result.layout.slots none [] [] [] sourceState [] sourceState :=
    ScopedFrameRel.rootInitial result.layout.slots sourceState
  refine {
    frameRel := hscoped
    bound := BoundSelectedIn.empty result.layout.slots none
      (frameInitialLive result.selection frame)
    certified := liveCertified_initial result.selection frame }

end LiveFrameRel

namespace FrameRel

theorem rootInitial (slots : SlotMap) (sourceState : EvmState) :
    FrameRel (base := base) (reserved := reserved)
      slots none [] [] sourceState [] sourceState := by
  refine ⟨.nil, ?_, ScratchRel.refl base reserved sourceState⟩
  intro name slot value _ hget
  simp [envGet] at hget

theorem observable_eq {slots : SlotMap} {owner : Owner} {signature : List Ident}
    {source target : WordEnv} {sourceState targetState : EvmState}
    (hrel : FrameRel (base := base) (reserved := reserved)
      slots owner signature source sourceState target targetState) :
    observables sourceState = observables targetState :=
  hrel.scratch.observables_eq

end FrameRel

/-! ## Ordinary execution of compiler-inserted slot operations -/

theorem evalLoadSlot {funs : FunEnv D} {vars : WordEnv} {state : EvmState}
    {slot : Nat} (hslot : slot < 2 ^ 256) :
    EvalExpr D funs vars state (MemorySpill.load slot)
      (.vals [loadWord state.memory slot] (touchMemory state slot 32)) := by
  apply Step.builtinOk
  · exact Step.argsCons Step.argsNil Step.lit
  · norm_num at hslot
    simp [builtinWithExternal, stepOp, litValue, Nat.mod_eq_of_lt hslot]

/-- A source variable read is either retained as an ordinary variable read or
materialized by the inserted `mload`.  In the latter case only the ignored
active-memory high-water mark changes. -/
theorem evalRewriteVar {slots : SlotMap} {owner : Owner}
    {sourceFuns : FunEnv G}
    {signature : List Ident} {cuts : List CutMark}
    {source target : WordEnv} {sourceState targetState : EvmState}
    (hrel : ScopedFrameRel (base := base) (reserved := reserved)
      slots owner signature cuts source sourceState target targetState)
    (hbounds : ∀ name slot, slotFor? slots owner name = some slot →
      base ≤ slot ∧ slot + 32 ≤ reserved)
    (hreserved : reserved < 2 ^ 256)
    {name : Ident} {value : U256} (hget : envGet source name = some value) :
    ∃ targetState',
      EvalExpr D (spillFuns slots sourceFuns) target targetState
        (rewriteExpr slots owner (.var name)) (.vals [value] targetState') ∧
      ScopedFrameRel (base := base) (reserved := reserved)
        slots owner signature cuts source sourceState target targetState' ∧
      ∀ cutoff, AboveUnchanged cutoff reserved targetState targetState' := by
  cases hslot : slotFor? slots owner name with
  | none =>
      refine ⟨targetState, ?_, hrel, fun cutoff => AboveUnchanged.refl cutoff reserved targetState⟩
      simp only [rewriteExpr, hslot]
      apply Step.var
      have htargetGet : envGet target name = some value := by
        rw [← hrel.env.vars.get_of_no_slot hslot]
        exact hget
      exact htargetGet
  | some slot =>
      have hslotBounds := hbounds name slot hslot
      have hslotLt : slot < 2 ^ 256 := by omega
      let targetState' := YulSemantics.EVM.touchMemory targetState slot 32
      have hload : loadWord targetState.memory slot = value :=
        hrel.loaded name slot value hslot hget
      refine ⟨targetState', ?_, ?_, ?_⟩
      · simpa only [rewriteExpr, hslot, hload] using
          (evalLoadSlot (funs := spillFuns slots sourceFuns)
            (vars := target) (state := targetState) hslotLt)
      · exact {
          env := hrel.env
          loaded := hrel.loaded.touchMemory slot 32
          scratch := scratchRel_touchMemory_right hrel.scratch slot 32 }
      · intro cutoff address hcut hreservedAddress
        simp [targetState', YulSemantics.EVM.touchMemory]

theorem simulateLit {selected : SpillSet} {layout : MemorySpillSelect.Layout}
    {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
    {source target : WordEnv} {sourceState targetState : EvmState}
    {sourceFuns : FunEnv G} (exitCopies : Block Op) (literal : Literal) (cutoff : Nat)
    (hrel : LiveFrameRel (base := base) (reserved := reserved)
      selected layout frame signature cuts live
      source sourceState target targetState) :
    ∃ targetResult,
      Step D (spillFuns layout.slots sourceFuns) target targetState
        (rewriteCode layout.slots frame.owner exitCopies (.expr (.lit literal))) targetResult ∧
      ResultLiveFrameRel (base := base) (reserved := reserved)
        selected layout frame signature cuts live source target
        (.expr (.lit literal))
        (.eres (.vals [Dialect.litValue G literal] sourceState)) targetResult ∧
      ResAboveUnchanged cutoff reserved targetState targetResult := by
  refine ⟨.eres (.vals [Dialect.litValue D literal] targetState), Step.lit, ?_, ?_⟩
  · exact ⟨rfl, hrel⟩
  · exact AboveUnchanged.refl cutoff reserved targetState

theorem simulateVar {selected : SpillSet} {layout : MemorySpillSelect.Layout}
    {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
    {source target : WordEnv} {sourceState targetState : EvmState}
    {sourceFuns : FunEnv G} {name : Ident} {value : U256}
    (hrel : LiveFrameRel (base := base) (reserved := reserved)
      selected layout frame signature cuts live
      source sourceState target targetState)
    (hbounds : ∀ name slot, slotFor? layout.slots frame.owner name = some slot →
      base ≤ slot ∧ slot + 32 ≤ reserved)
    (hreserved : reserved < 2 ^ 256) (hget : envGet source name = some value)
    (exitCopies : Block Op) (cutoff : Nat) :
    ∃ targetResult,
      Step D (spillFuns layout.slots sourceFuns) target targetState
        (rewriteCode layout.slots frame.owner exitCopies (.expr (.var name))) targetResult ∧
      ResultLiveFrameRel (base := base) (reserved := reserved)
        selected layout frame signature cuts live source target
        (.expr (.var name)) (.eres (.vals [value] sourceState)) targetResult ∧
      ResAboveUnchanged cutoff reserved targetState targetResult := by
  obtain ⟨targetState', hstep, hframeRel, habove⟩ :=
    evalRewriteVar hrel.frameRel hbounds hreserved hget
  let hrel' : LiveFrameRel (base := base) (reserved := reserved)
      selected layout frame signature cuts live
      source sourceState target targetState' := {
    frameRel := hframeRel
    bound := hrel.bound
    certified := hrel.certified }
  refine ⟨.eres (.vals [value] targetState'), ?_, ⟨rfl, hrel'⟩, habove cutoff⟩
  simpa [rewriteCode] using hstep

/-! ### Expression and argument derivations

This is the call-free layer of the syntax-directed simulation.  User-function
calls deliberately have no `SpillExpr` constructor: their proof changes frame
owners and consumes the separate origin/call-graph certificates. -/

mutual
  inductive SpillExpr : Expr Op → Prop
    | lit (literal : Literal) : SpillExpr (.lit literal)
    | var (name : Ident) : SpillExpr (.var name)
    | builtin (op : Op) {args : List (Expr Op)} :
        SpillArgs args → SpillExpr (.builtin op args)

  inductive SpillArgs : List (Expr Op) → Prop
    | nil : SpillArgs []
    | cons {expression : Expr Op} {rest : List (Expr Op)} :
        SpillExpr expression → SpillArgs rest →
          SpillArgs (expression :: rest)
end

/-- A valid compiler-resolved memory guard enters the expression simulation as
an ordinary literal. -/
theorem SpillExpr.resolvedMemoryGuard (base reserved : Nat) :
    SpillExpr
      (resolveMemoryGuardExpr base reserved
        (.call "memoryguard" [.lit (.number base)])) := by
  simp [resolveMemoryGuardExpr]
  exact .lit _

mutual
  theorem simulateExprStep {selected : SpillSet}
      {layout : MemorySpillSelect.Layout} {frame : Frame}
      {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
      {source target : WordEnv} {sourceState targetState : EvmState}
      {sourceFuns : FunEnv G} {expression : Expr Op} {sourceResult : EResult G}
      (hsource : EvalExpr G sourceFuns source sourceState expression sourceResult)
      (hsyntax : SpillExpr expression)
      (hrel : LiveFrameRel (base := base) (reserved := reserved)
        selected layout frame signature cuts live
        source sourceState target targetState)
      (hexternals : GuardedExternals calls creates base reserved)
      (hbounds : ∀ name slot,
        slotFor? layout.slots frame.owner name = some slot →
          base ≤ slot ∧ slot + 32 ≤ reserved)
      (hreserved : reserved < 2 ^ 256) (exitCopies : Block Op)
      (cutoff : Nat) (hcutoff : base ≤ cutoff) :
      ∃ targetResult : EResult D,
        EvalExpr D (spillFuns layout.slots sourceFuns) target targetState
          (rewriteExpr layout.slots frame.owner expression) targetResult ∧
        ResultLiveFrameRel (base := base) (reserved := reserved)
          selected layout frame signature cuts live source target
          (.expr expression) (.eres sourceResult) (.eres targetResult) ∧
        ResAboveUnchanged cutoff reserved targetState (.eres targetResult) := by
    cases hsource with
    | lit =>
        cases hsyntax
        exact ⟨.vals [_] targetState, Step.lit, ⟨rfl, hrel⟩,
          AboveUnchanged.refl cutoff reserved targetState⟩
    | var hget =>
        cases hsyntax
        obtain ⟨targetState', heval, hframe, habove⟩ :=
          evalRewriteVar hrel.frameRel hbounds hreserved hget
        let hrel' : LiveFrameRel (base := base) (reserved := reserved)
            selected layout frame signature cuts live
            source sourceState target targetState' := {
          frameRel := hframe
          bound := hrel.bound
          certified := hrel.certified }
        exact ⟨.vals [_] targetState', heval, ⟨rfl, hrel'⟩, habove cutoff⟩
    | builtinOk hargs hbuiltin =>
        cases hsyntax with
        | builtin _ hargSyntax =>
            obtain ⟨targetArgsResult, htargetArgs, hargsRel, haboveArgs⟩ :=
              simulateArgsStep hargs hargSyntax hrel hexternals hbounds
                hreserved exitCopies cutoff hcutoff
            cases targetArgsResult with
            | halt targetArgsState => simp [ResultLiveFrameRel] at hargsRel
            | vals targetArgs targetArgsState =>
                rcases hargsRel with ⟨hvalues, hframeArgs⟩
                subst targetArgs
                obtain ⟨rightResult, hright, hresult, hloaded, haboveBuiltin⟩ :=
                  guardedBuiltin_sim hexternals hframeArgs.frameRel.scratch hbuiltin
                    hframeArgs.frameRel.loaded hbounds hcutoff
                cases rightResult with
                | halt rightState => simp [ResultRel] at hresult
                | ok rightValues rightState =>
                    rcases hresult with ⟨hvalues, hscratch⟩
                    refine ⟨.vals rightValues rightState,
                      Step.builtinOk htargetArgs hright, ?_, ?_⟩
                    · exact ⟨hvalues.symm,
                        { frameRel := {
                            env := hframeArgs.frameRel.env
                            loaded := hloaded
                            scratch := hscratch }
                          bound := hframeArgs.bound
                          certified := hframeArgs.certified }⟩
                    · exact haboveArgs.trans haboveBuiltin
    | builtinHalt hargs hbuiltin =>
        cases hsyntax with
        | builtin _ hargSyntax =>
            obtain ⟨targetArgsResult, htargetArgs, hargsRel, haboveArgs⟩ :=
              simulateArgsStep hargs hargSyntax hrel hexternals hbounds
                hreserved exitCopies cutoff hcutoff
            cases targetArgsResult with
            | halt targetArgsState => simp [ResultLiveFrameRel] at hargsRel
            | vals targetArgs targetArgsState =>
                rcases hargsRel with ⟨hvalues, hframeArgs⟩
                subst targetArgs
                obtain ⟨rightResult, hright, hresult, hloaded, haboveBuiltin⟩ :=
                  guardedBuiltin_sim hexternals hframeArgs.frameRel.scratch hbuiltin
                    hframeArgs.frameRel.loaded hbounds hcutoff
                cases rightResult with
                | ok rightValues rightState => simp [ResultRel] at hresult
                | halt rightState =>
                    refine ⟨.halt rightState, Step.builtinHalt htargetArgs hright,
                      ?_, haboveArgs.trans haboveBuiltin⟩
                    exact {
                      frameRel := {
                        env := hframeArgs.frameRel.env
                        loaded := hloaded
                        scratch := hresult }
                      bound := hframeArgs.bound
                      certified := hframeArgs.certified }
    | builtinArgsHalt hargs =>
        cases hsyntax with
        | builtin _ hargSyntax =>
            obtain ⟨targetArgsResult, htargetArgs, hargsRel, haboveArgs⟩ :=
              simulateArgsStep hargs hargSyntax hrel hexternals hbounds
                hreserved exitCopies cutoff hcutoff
            cases targetArgsResult with
            | vals values state => simp [ResultLiveFrameRel] at hargsRel
            | halt state =>
                exact ⟨.halt state, Step.builtinArgsHalt htargetArgs,
                  hargsRel, haboveArgs⟩
    | callOk hargs hlookup hlength hbody houtcome => cases hsyntax
    | callHalt hargs hlookup hlength hbody => cases hsyntax
    | callArgsHalt hargs => cases hsyntax

  theorem simulateArgsStep {selected : SpillSet}
      {layout : MemorySpillSelect.Layout} {frame : Frame}
      {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
      {source target : WordEnv} {sourceState targetState : EvmState}
      {sourceFuns : FunEnv G} {args : List (Expr Op)} {sourceResult : EResult G}
      (hsource : EvalArgs G sourceFuns source sourceState args sourceResult)
      (hsyntax : SpillArgs args)
      (hrel : LiveFrameRel (base := base) (reserved := reserved)
        selected layout frame signature cuts live
        source sourceState target targetState)
      (hexternals : GuardedExternals calls creates base reserved)
      (hbounds : ∀ name slot,
        slotFor? layout.slots frame.owner name = some slot →
          base ≤ slot ∧ slot + 32 ≤ reserved)
      (hreserved : reserved < 2 ^ 256) (exitCopies : Block Op)
      (cutoff : Nat) (hcutoff : base ≤ cutoff) :
      ∃ targetResult : EResult D,
        EvalArgs D (spillFuns layout.slots sourceFuns) target targetState
          (rewriteArgs layout.slots frame.owner args) targetResult ∧
        ResultLiveFrameRel (base := base) (reserved := reserved)
          selected layout frame signature cuts live source target
          (.args args) (.eres sourceResult) (.eres targetResult) ∧
        ResAboveUnchanged cutoff reserved targetState (.eres targetResult) := by
    cases hsource with
    | argsNil =>
        exact ⟨.vals [] targetState, Step.argsNil, ⟨rfl, hrel⟩,
          AboveUnchanged.refl cutoff reserved targetState⟩
    | argsCons hrest hhead =>
        cases hsyntax with
        | cons hheadSyntax hrestSyntax =>
            obtain ⟨targetRestResult, htargetRest, hrestRel, haboveRest⟩ :=
              simulateArgsStep hrest hrestSyntax hrel hexternals hbounds
                hreserved exitCopies cutoff hcutoff
            cases targetRestResult with
            | halt state => simp [ResultLiveFrameRel] at hrestRel
            | vals targetRestValues restState =>
                rcases hrestRel with ⟨hrestValues, hrestFrame⟩
                subst targetRestValues
                obtain ⟨targetHeadResult, htargetHead, hheadRel, haboveHead⟩ :=
                  simulateExprStep hhead hheadSyntax hrestFrame hexternals hbounds
                    hreserved exitCopies cutoff hcutoff
                cases targetHeadResult with
                | halt state => simp [ResultLiveFrameRel] at hheadRel
                | vals targetHeadValues headState =>
                    rcases hheadRel with ⟨hheadValues, hheadFrame⟩
                    have hone : targetHeadValues = [_] := hheadValues
                    subst targetHeadValues
                    exact ⟨.vals (_ :: _) headState,
                      Step.argsCons htargetRest htargetHead,
                      ⟨rfl, hheadFrame⟩, haboveRest.trans haboveHead⟩
    | argsRestHalt hrest =>
        cases hsyntax with
        | cons hheadSyntax hrestSyntax =>
            obtain ⟨targetRestResult, htargetRest, hrestRel, haboveRest⟩ :=
              simulateArgsStep hrest hrestSyntax hrel hexternals hbounds
                hreserved exitCopies cutoff hcutoff
            cases targetRestResult with
            | vals values state => simp [ResultLiveFrameRel] at hrestRel
            | halt state =>
                exact ⟨.halt state, Step.argsRestHalt htargetRest,
                  hrestRel, haboveRest⟩
    | argsHeadHalt hrest hhead =>
        cases hsyntax with
        | cons hheadSyntax hrestSyntax =>
            obtain ⟨targetRestResult, htargetRest, hrestRel, haboveRest⟩ :=
              simulateArgsStep hrest hrestSyntax hrel hexternals hbounds
                hreserved exitCopies cutoff hcutoff
            cases targetRestResult with
            | halt state => simp [ResultLiveFrameRel] at hrestRel
            | vals targetRestValues restState =>
                rcases hrestRel with ⟨hrestValues, hrestFrame⟩
                subst targetRestValues
                obtain ⟨targetHeadResult, htargetHead, hheadRel, haboveHead⟩ :=
                  simulateExprStep hhead hheadSyntax hrestFrame hexternals hbounds
                    hreserved exitCopies cutoff hcutoff
                cases targetHeadResult with
                | vals values state => simp [ResultLiveFrameRel] at hheadRel
                | halt state =>
                    exact ⟨.halt state, Step.argsHeadHalt htargetRest htargetHead,
                      hheadRel, haboveRest.trans haboveHead⟩
end

theorem execStoreSlot {funs : FunEnv D} {vars : WordEnv}
    {state state' : EvmState} {expression : Expr Op}
    {slot : Nat} {value : U256} (hslot : slot < 2 ^ 256)
    (heval : EvalExpr D funs vars state expression (.vals [value] state')) :
    ExecStmt D funs vars state (MemorySpill.store slot expression) vars
      (MemorySpillStateSound.slotState state' slot value) .normal := by
  apply Step.exprStmt
  apply Step.builtinOk
  · exact Step.argsCons (Step.argsCons Step.argsNil heval) Step.lit
  · norm_num at hslot
    simp [builtinWithExternal, stepOp, MemorySpillStateSound.slotState,
      litValue, Nat.mod_eq_of_lt hslot]

theorem execStoreSlot_halt {funs : FunEnv D} {vars : WordEnv}
    {state state' : EvmState} {expression : Expr Op} {slot : Nat}
    (heval : EvalExpr D funs vars state expression (.halt state')) :
    ExecStmt D funs vars state (MemorySpill.store slot expression) vars
      state' .halt := by
  apply Step.exprStmtHalt
  apply Step.builtinArgsHalt
  exact Step.argsRestHalt (Step.argsHeadHalt Step.argsNil heval)

/-! ### Selected signature copyback -/

theorem execCopyBackOne {slots : SlotMap} {owner : Owner}
    {signature : List Ident} {cuts : List CutMark}
    {source target : WordEnv} {sourceState targetState : EvmState}
    {sourceFuns : FunEnv G} {name : Ident} {slot : Nat} {value : U256}
    (hrel : ScopedFrameRel (base := base) (reserved := reserved)
      slots owner signature cuts source sourceState target targetState)
    (hslot : slotFor? slots owner name = some slot)
    (hsignature : name ∈ signature)
    (hget : envGet source name = some value)
    (hslotBound : slot + 32 ≤ reserved)
    (hreserved : reserved < 2 ^ 256) :
    let finalState := YulSemantics.EVM.touchMemory targetState slot 32
    ExecStmt D (spillFuns slots sourceFuns) target targetState
      (.assign [name] (MemorySpill.load slot))
      (envSet target name value) finalState .normal ∧
    ScopedFrameRel (base := base) (reserved := reserved)
      slots owner signature cuts source sourceState
      (envSet target name value) finalState ∧
    ∀ cutoff, AboveUnchanged cutoff reserved targetState finalState := by
  dsimp only
  have hloadedValue := hrel.loaded name slot value hslot hget
  have hslotLt : slot < 2 ^ 256 := by omega
  have heval := evalLoadSlot
    (funs := spillFuns slots sourceFuns) (vars := target)
    (state := targetState) hslotLt
  rw [hloadedValue] at heval
  have hstatement : ExecStmt D (spillFuns slots sourceFuns) target targetState
      (.assign [name] (MemorySpill.load slot))
      (envSet target name value)
      (YulSemantics.EVM.touchMemory targetState slot 32) .normal := by
    rw [envSet_eq_ordinary]
    exact Step.assignVal heval (by simp)
  refine ⟨hstatement, {
    env := hrel.env.setTargetSelectedSignature hslot hsignature value
    loaded := hrel.loaded.touchMemory slot 32
    scratch := scratchRel_touchMemory_right hrel.scratch slot 32 }, ?_⟩
  intro cutoff address hcut haddress
  simp [YulSemantics.EVM.touchMemory]

theorem execCopyBackReturns {slots : SlotMap} {owner : Owner}
    {signature returns : List Ident} {cuts : List CutMark}
    {source target : WordEnv} {sourceState targetState : EvmState}
    {sourceFuns : FunEnv G}
    (hrel : ScopedFrameRel (base := base) (reserved := reserved)
      slots owner signature cuts source sourceState target targetState)
    (hnodup : returns.Nodup)
    (hsignature : ∀ name ∈ returns, name ∈ signature)
    (hbound : ∀ name ∈ returns, ∃ value, envGet source name = some value)
    (hbounds : ∀ name slot, slotFor? slots owner name = some slot →
      slot + 32 ≤ reserved)
    (hreserved : reserved < 2 ^ 256) :
    ∃ target' targetState',
      ExecStmts D (spillFuns slots sourceFuns) target targetState
        (copyBackReturns slots owner returns) target' targetState' .normal ∧
      ScopedFrameRel (base := base) (reserved := reserved)
        slots owner signature cuts source sourceState target' targetState' ∧
      ReturnsSynced returns source target' ∧
      EnvAgreesOutside returns target target' ∧
      ∀ cutoff, AboveUnchanged cutoff reserved targetState targetState' := by
  induction returns generalizing target targetState with
  | nil =>
      exact ⟨target, targetState, by
          simpa [copyBackReturns] using
            (Step.seqNil : ExecStmts D (spillFuns slots sourceFuns)
              target targetState [] target targetState .normal), hrel,
        by intro name hmem; simp at hmem,
        EnvAgreesOutside.refl [] target,
        fun cutoff => AboveUnchanged.refl cutoff reserved targetState⟩
  | cons name rest ih =>
      have hparts := List.nodup_cons.mp hnodup
      have hnameSignature := hsignature name (by simp)
      obtain ⟨value, hget⟩ := hbound name (by simp)
      have hrestSignature : ∀ other ∈ rest, other ∈ signature := by
        intro other hmem
        exact hsignature other (by simp [hmem])
      have hrestBound : ∀ other ∈ rest,
          ∃ found, envGet source other = some found := by
        intro other hmem
        exact hbound other (by simp [hmem])
      cases hslot : slotFor? slots owner name with
      | none =>
          obtain ⟨target', state', hexec, hfinal, hsync, houtside, habove⟩ :=
            ih hrel hparts.2 hrestSignature hrestBound
          refine ⟨target', state', ?_, hfinal, ?_, ?_, habove⟩
          · simpa [copyBackReturns, hslot] using hexec
          · intro other hmem
            rcases List.mem_cons.mp hmem with rfl | hrest
            · exact hfinal.env.vars.get_of_no_slot hslot
            · exact hsync other hrest
          · intro other hmem
            exact houtside other (by simp at hmem; exact hmem.2)
      | some slot =>
          obtain ⟨old, hold⟩ :=
            hrel.env.vars.targetGet_of_selectedSignature hslot hnameSignature hget
          obtain ⟨hstmt, hnext, haboveHead⟩ := execCopyBackOne hrel hslot
            hnameSignature hget (hbounds name slot hslot) hreserved
          obtain ⟨target', state', hexec, hfinal, hsync, houtside, haboveTail⟩ :=
            ih hnext hparts.2 hrestSignature hrestBound
          refine ⟨target', state', ?_, hfinal, ?_, ?_, ?_⟩
          · simpa [copyBackReturns, hslot] using Step.seqCons hstmt hexec
          · intro other hmem
            rcases List.mem_cons.mp hmem with rfl | hrest
            · have hafterHead : envGet (envSet target other value) other = some value :=
                envGet_envSet_self_eq hold
              rw [hget, ← hafterHead]
              exact (houtside other hparts.1).symm
            · exact hsync other hrest
          · intro other hmem
            have hnot : other ≠ name ∧ other ∉ rest := by simpa using hmem
            rw [houtside other hnot.2]
            exact EnvAgreesOutside.set target name value other (by simpa using hnot.1)
          · intro cutoff
            exact (haboveHead cutoff).trans (haboveTail cutoff)

/-! ### Selected singleton declaration -/

theorem execSelectedLet {selected : SpillSet} {policyBody : Block Op}
    {layout : MemorySpillSelect.Layout} {frame : Frame} {signature : List Ident}
    {cuts : List CutMark} {live : SpillSet}
    {source target : WordEnv} {sourceState targetInitial targetState : EvmState}
    {sourceFuns : FunEnv G} {name : Ident} {slot : Nat} {value : U256}
    {expression : Expr Op}
    (hbuild : buildLayout base selected policyBody = some layout)
    (hcheck : layoutCheck base reserved selected layout = true)
    (hreserved : reserved < 2 ^ 256)
    (hframe : frame ∈ frames policyBody)
    (hslot : slotFor? layout.slots frame.owner name = some slot)
    (hnotSignature : name ∉ signature)
    (hnextCertified : LiveCertified selected frame
      ({ owner := frame.owner, name } :: live))
    (hrel : LiveFrameRel (base := base) (reserved := reserved)
      selected layout frame signature cuts live
      source sourceState target targetState)
    (heval : EvalExpr D (spillFuns layout.slots sourceFuns) target targetInitial
      expression (.vals [value] targetState))
    {cutoff : Nat}
    (haboveExpr : AboveUnchanged cutoff reserved targetInitial targetState)
    (hslotEnd : slot + 32 ≤ cutoff) :
    let finalState := MemorySpillStateSound.slotState targetState slot value
    ExecStmts D (spillFuns layout.slots sourceFuns) target targetInitial
      [MemorySpill.store slot expression] target finalState .normal ∧
    LiveFrameRel (base := base) (reserved := reserved)
      selected layout frame signature cuts
      ({ owner := frame.owner, name } :: live)
      ((name, value) :: source) sourceState target finalState ∧
    AboveUnchanged cutoff reserved targetInitial finalState := by
  dsimp only
  have hslotBounds := layoutCheck_slotFor_bounds hcheck hslot
  have hslotLt : slot < 2 ^ 256 := by omega
  have hstatement := execStoreSlot hslotLt heval
  have hexec : ExecStmts D (spillFuns layout.slots sourceFuns) target targetInitial
      [MemorySpill.store slot expression] target
      (MemorySpillStateSound.slotState targetState slot value) .normal :=
    Step.seqCons hstatement Step.seqNil
  obtain ⟨maxLive, hmax, hsubset⟩ := hnextCertified.covered
  have hfresh : SlotFreshForEnv layout.slots frame.owner source name slot :=
    slotFreshForEnv_of_live hbuild hcheck hframe hmax
      (by
        intro key hkey
        exact hsubset key (by simp [hkey]))
      hrel.bound (hsubset _ (by simp)) hslot
  have hvars : VRel layout.slots frame.owner signature
      ((name, value) :: source) target :=
    .selectedLocal hslot hnotSignature hrel.frameRel.env.vars
  have henv : EnvRel layout.slots frame.owner signature
      ((name, value) :: source) target cuts :=
    EnvRel.prepend [(name, value)] [] hrel.frameRel.env (by simpa using hvars)
  have hloaded := SlotsLoaded.prependSelected_store hrel.frameRel.loaded
    hslot value hfresh
  have hscratch : ScratchRel base reserved sourceState
      (MemorySpillStateSound.slotState targetState slot value) :=
    hrel.frameRel.scratch.trans (slotState_scratch_rel hslotBounds targetState)
  have hbound : BoundSelectedIn layout.slots frame.owner
      ((name, value) :: source) ({ owner := frame.owner, name } :: live) := by
    apply BoundSelectedIn.prepend (front := [(name, value)])
      (nextLive := ({ owner := frame.owner, name } :: live)) hrel.bound
    · intro other hmem otherSlot hotherSlot
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hmem
      subst other
      simp
    · intro key hmem
      exact List.mem_cons_of_mem _ hmem
  refine ⟨hexec, {
    frameRel := ⟨henv, hloaded, hscratch⟩
    bound := hbound
    certified := hnextCertified }, ?_⟩
  exact haboveExpr.trans
    (AboveUnchanged.slotState (reserved := reserved) hslotEnd targetState)

/-! ### Selected singleton assignment -/

theorem execSelectedAssign {selected : SpillSet} {policyBody : Block Op}
    {layout : MemorySpillSelect.Layout} {frame : Frame} {signature : List Ident}
    {cuts : List CutMark} {live : SpillSet}
    {source target : WordEnv} {sourceState targetInitial targetState : EvmState}
    {sourceFuns : FunEnv G} {name : Ident} {slot : Nat} {value : U256}
    {expression : Expr Op}
    (hbuild : buildLayout base selected policyBody = some layout)
    (hcheck : layoutCheck base reserved selected layout = true)
    (hreserved : reserved < 2 ^ 256)
    (hframe : frame ∈ frames policyBody)
    (hslot : slotFor? layout.slots frame.owner name = some slot)
    (hname : { owner := frame.owner, name } ∈ live)
    (hrel : LiveFrameRel (base := base) (reserved := reserved)
      selected layout frame signature cuts live
      source sourceState target targetState)
    (heval : EvalExpr D (spillFuns layout.slots sourceFuns) target targetInitial
      expression (.vals [value] targetState))
    {cutoff : Nat}
    (haboveExpr : AboveUnchanged cutoff reserved targetInitial targetState)
    (hslotEnd : slot + 32 ≤ cutoff) :
    let finalState := MemorySpillStateSound.slotState targetState slot value
    ExecStmts D (spillFuns layout.slots sourceFuns) target targetInitial
      [MemorySpill.store slot expression] target finalState .normal ∧
    LiveFrameRel (base := base) (reserved := reserved)
      selected layout frame signature cuts live
      (envSet source name value) sourceState target finalState ∧
    AboveUnchanged cutoff reserved targetInitial finalState := by
  dsimp only
  have hslotBounds := layoutCheck_slotFor_bounds hcheck hslot
  have hslotLt : slot < 2 ^ 256 := by omega
  have hstatement := execStoreSlot hslotLt heval
  have hexec : ExecStmts D (spillFuns layout.slots sourceFuns) target targetInitial
      [MemorySpill.store slot expression] target
      (MemorySpillStateSound.slotState targetState slot value) .normal :=
    Step.seqCons hstatement Step.seqNil
  have hfresh := hrel.slotFresh hbuild hcheck hframe hname hslot
  have henv := hrel.frameRel.env.setSelected hslot value
  have hloaded := SlotsLoaded.setSelected_store hrel.frameRel.loaded
    hslot value hfresh
  have hscratch : ScratchRel base reserved sourceState
      (MemorySpillStateSound.slotState targetState slot value) :=
    hrel.frameRel.scratch.trans (slotState_scratch_rel hslotBounds targetState)
  have hbound := hrel.bound.set name value
  refine ⟨hexec, {
    frameRel := ⟨henv, hloaded, hscratch⟩
    bound := hbound
    certified := hrel.certified }, ?_⟩
  exact haboveExpr.trans
    (AboveUnchanged.slotState (reserved := reserved) hslotEnd targetState)

/-! ### Unselected singleton assignment -/

theorem execUnselectedAssign {selected : SpillSet}
    {layout : MemorySpillSelect.Layout}
    {frame : Frame} {signature : List Ident} {cuts : List CutMark}
    {live : SpillSet} {source target : WordEnv}
    {sourceState targetInitial targetState : EvmState}
    {sourceFuns : FunEnv G} {name : Ident} {value : U256}
    {expression : Expr Op}
    (hslot : slotFor? layout.slots frame.owner name = none)
    (hrel : LiveFrameRel (base := base) (reserved := reserved)
      selected layout frame signature cuts live
      source sourceState target targetState)
    (heval : EvalExpr D (spillFuns layout.slots sourceFuns) target targetInitial
      expression (.vals [value] targetState))
    {cutoff : Nat}
    (haboveExpr : AboveUnchanged cutoff reserved targetInitial targetState) :
    ExecStmts D (spillFuns layout.slots sourceFuns) target targetInitial
      [.assign [name] expression] (envSet target name value) targetState .normal ∧
    LiveFrameRel (base := base) (reserved := reserved)
      selected layout frame signature cuts live
      (envSet source name value) sourceState
      (envSet target name value) targetState ∧
    AboveUnchanged cutoff reserved targetInitial targetState := by
  have hstatement : ExecStmt D (spillFuns layout.slots sourceFuns)
      target targetInitial (.assign [name] expression)
      (envSet target name value) targetState .normal := by
    rw [envSet_eq_ordinary]
    exact Step.assignVal heval (by simp)
  have hexec : ExecStmts D (spillFuns layout.slots sourceFuns)
      target targetInitial [.assign [name] expression]
      (envSet target name value) targetState .normal :=
    Step.seqCons hstatement Step.seqNil
  refine ⟨hexec, {
    frameRel := {
      env := hrel.frameRel.env.setNoSlot hslot value
      loaded := hrel.frameRel.loaded.setNoSlot hslot value
      scratch := hrel.frameRel.scratch }
    bound := hrel.bound.set name value
    certified := hrel.certified }, haboveExpr⟩

/-! ### Unselected singleton declaration -/

theorem execUnselectedLet {selected : SpillSet}
    {layout : MemorySpillSelect.Layout}
    {frame : Frame} {signature : List Ident} {cuts : List CutMark}
    {live nextLive : SpillSet} {source target : WordEnv}
    {sourceState targetInitial targetState : EvmState}
    {sourceFuns : FunEnv G} {name : Ident} {value : U256}
    {expression : Expr Op}
    (hslot : slotFor? layout.slots frame.owner name = none)
    (hnextCertified : LiveCertified selected frame nextLive)
    (hlive : ∀ key ∈ live, key ∈ nextLive)
    (hrel : LiveFrameRel (base := base) (reserved := reserved)
      selected layout frame signature cuts live
      source sourceState target targetState)
    (heval : EvalExpr D (spillFuns layout.slots sourceFuns) target targetInitial
      expression (.vals [value] targetState))
    {cutoff : Nat}
    (haboveExpr : AboveUnchanged cutoff reserved targetInitial targetState) :
    ExecStmts D (spillFuns layout.slots sourceFuns) target targetInitial
      [.letDecl [name] (some expression)]
      ((name, value) :: target) targetState .normal ∧
    LiveFrameRel (base := base) (reserved := reserved)
      selected layout frame signature cuts nextLive
      ((name, value) :: source) sourceState
      ((name, value) :: target) targetState ∧
    AboveUnchanged cutoff reserved targetInitial targetState := by
  have hstatement : ExecStmt D (spillFuns layout.slots sourceFuns)
      target targetInitial (.letDecl [name] (some expression))
      ((name, value) :: target) targetState .normal := by
    have hstep := Step.letVal (vars := [name]) heval (by simp)
    have hzip : [name].zip [value] = [(name, value)] := by rfl
    rw [hzip] at hstep
    simpa using hstep
  have hexec : ExecStmts D (spillFuns layout.slots sourceFuns)
      target targetInitial [.letDecl [name] (some expression)]
      ((name, value) :: target) targetState .normal :=
    Step.seqCons hstatement Step.seqNil
  have hvars : VRel layout.slots frame.owner signature
      ((name, value) :: source) ((name, value) :: target) :=
    .unselected hslot hrel.frameRel.env.vars
  have henv := EnvRel.prepend [(name, value)] [(name, value)]
    hrel.frameRel.env (by simpa using hvars)
  have hbound : BoundSelectedIn layout.slots frame.owner
      ((name, value) :: source) nextLive := by
    apply BoundSelectedIn.prepend (front := [(name, value)])
      (nextLive := nextLive) hrel.bound
    · intro other hmem otherSlot hotherSlot
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hmem
      subst other
      rw [hslot] at hotherSlot
      contradiction
    · exact hlive
  refine ⟨hexec, {
    frameRel := {
      env := henv
      loaded := hrel.frameRel.loaded.prependNoSlot hslot value
      scratch := hrel.frameRel.scratch }
    bound := hbound
    certified := hnextCertified }, haboveExpr⟩

end YulEvmCompiler.Optimizer.MemorySpillRewriteSound
