import YulEvmCompiler.Compile
import YulSemantics.ObjectRun

/-!
# YulEvmCompiler.ObjectCompile

The **object layer**: assembling a Yul `Object` into a deployed-bytecode
`Layout` (the artifact `YulSemantics.ObjectRun` is parameterized over), and
the key correctness content — that the produced layout is **consistent** with
the object, i.e. every `data` segment is faithfully placed in the deployed
bytecode at the recorded offset with the recorded size.

`compileObject` plans and compiles the complete tree recursively. It resolves
`dataoffset`/`datasize` to fixed-width constants, emits each object's code,
adds a `STOP` seam, and appends child-object bytecode followed by direct data.
Its maps include self, child, nested, and data references under the same
string-literal keys the Yul built-ins consume. Key collisions and layouts that
do not fit a word are rejected.

`compileObject_consistent` discharges `Layout.Consistent`, which — composed
with the semantics' already-proven `constructorCode_returns_of_consistent` —
gives an end-to-end statement: under the compiler's layout, the canonical
constructor for any data segment returns exactly that segment's bytes
(`compiled_constructor_returns`).

The executable layout and direct-data consistency proof are complete. The
remaining proof debt is the stronger `RunObject`-to-EVM simulation theorem:
the block compiler's backend theorem still needs to admit the object payload
as a trailing code suffix, and the reference-resolution pass needs a semantic
preservation theorem against the selected layout.
-/

namespace YulEvmCompiler

open YulSemantics (Object Data Ident)
open YulSemantics.EVM (Op litValue U256 Layout byteFrom readBytes)

/-- The concatenated bytes of a data-segment list, in order. -/
def dataRegion (segs : List (String × Data)) : List UInt8 :=
  segs.flatMap (fun p => p.2.bytes)

/-! ### Recursive, resolved object layout -/

/-- One named byte range visible from an object's code. Offsets are relative
to the start of that object's bytecode. -/
structure ObjectEntry where
  name : String
  offset : Nat
  size : Nat
  deriving Repr, DecidableEq

/-- A planned object layout. `codeSize` is obtained by compiling the code with
zero placeholders for layout references. Since this compiler always emits
fixed-width `PUSH32`, replacing those placeholders with real offsets and sizes
does not change any instruction or label position. -/
structure ObjectPlan where
  name : String
  codeBlock : List (YulSemantics.Stmt Op)
  codeSize : Nat
  size : Nat
  subObjects : List ObjectPlan
  dataSegs : List (String × Data)
  entries : List ObjectEntry
  bytecode : List UInt8
  deriving Repr

private abbrev RefResolver := String → Option (Nat × Nat)

mutual
  /-- Replace `dataoffset`/`datasize` recursively with constants supplied by a
  concrete object layout. -/
  private def resolveObjectExpr (resolve : RefResolver) :
      YulSemantics.Expr Op → Option (YulSemantics.Expr Op)
    | .lit literal => some (.lit literal)
    | .var name => some (.var name)
    | .builtin op args => do
        let args ← resolveObjectExprs resolve args
        match op, args with
        | .dataoffset, [.lit (.string name)] =>
            let entry ← resolve name
            some (.lit (.number entry.1))
        | .datasize, [.lit (.string name)] =>
            let entry ← resolve name
            some (.lit (.number entry.2))
        | _, _ => some (.builtin op args)
    | .call name args => return .call name (← resolveObjectExprs resolve args)

  private def resolveObjectExprs (resolve : RefResolver) :
      List (YulSemantics.Expr Op) → Option (List (YulSemantics.Expr Op))
    | [] => some []
    | expression :: expressions => do
        return (← resolveObjectExpr resolve expression) ::
          (← resolveObjectExprs resolve expressions)
end

mutual
  private def resolveObjectStmt (resolve : RefResolver) :
      YulSemantics.Stmt Op → Option (YulSemantics.Stmt Op)
    | .block body => return .block (← resolveObjectStmts resolve body)
    | .funDef name params returns body =>
        return .funDef name params returns (← resolveObjectStmts resolve body)
    | .letDecl names value =>
        match value with
        | none => some (.letDecl names none)
        | some expression =>
            return .letDecl names (some (← resolveObjectExpr resolve expression))
    | .assign names value => return .assign names (← resolveObjectExpr resolve value)
    | .cond condition body =>
        return .cond (← resolveObjectExpr resolve condition) (← resolveObjectStmts resolve body)
    | .switch condition cases fallback => do
        let condition ← resolveObjectExpr resolve condition
        let cases ← resolveObjectCases resolve cases
        let fallback ← match fallback with
          | none => some none
          | some body => (resolveObjectStmts resolve body).map some
        return .switch condition cases fallback
    | .forLoop init condition post body =>
        return .forLoop (← resolveObjectStmts resolve init)
          (← resolveObjectExpr resolve condition) (← resolveObjectStmts resolve post)
          (← resolveObjectStmts resolve body)
    | .exprStmt expression => return .exprStmt (← resolveObjectExpr resolve expression)
    | .«break» => some .«break»
    | .«continue» => some .«continue»
    | .leave => some .leave

  private def resolveObjectStmts (resolve : RefResolver) :
      List (YulSemantics.Stmt Op) → Option (List (YulSemantics.Stmt Op))
    | [] => some []
    | statement :: statements => do
        return (← resolveObjectStmt resolve statement) ::
          (← resolveObjectStmts resolve statements)

  private def resolveObjectCases (resolve : RefResolver) :
      List (YulSemantics.Literal × List (YulSemantics.Stmt Op)) →
        Option (List (YulSemantics.Literal × List (YulSemantics.Stmt Op)))
    | [] => some []
    | (literal, body) :: cases => do
        return (literal, ← resolveObjectStmts resolve body) ::
          (← resolveObjectCases resolve cases)
end

private def placeholderResolver : RefResolver := fun _ => some (0, 0)

private def shiftChildEntries (base : Nat) (child : ObjectPlan) : List ObjectEntry :=
  child.entries.map fun entry =>
    if entry.name == child.name then
      { entry with offset := base + entry.offset, size := child.bytecode.length }
    else
      { name := child.name ++ "." ++ entry.name
        offset := base + entry.offset
        size := entry.size }

private def childEntries : Nat → List ObjectPlan → List ObjectEntry
  | _, [] => []
  | base, child :: children =>
      shiftChildEntries base child ++ childEntries (base + child.bytecode.length) children

private def dataEntries : Nat → List (String × Data) → List ObjectEntry
  | _, [] => []
  | base, (name, value) :: values =>
      { name, offset := base, size := value.size } :: dataEntries (base + value.size) values

private def canonicalRef (plan : ObjectPlan) (name : String) : String :=
  let ownPrefix := plan.name ++ "."
  if name.startsWith ownPrefix then (name.drop ownPrefix.length).copy else name

private def findEntry (plan : ObjectPlan) (name : String) : Option ObjectEntry :=
  let name := canonicalRef plan name
  plan.entries.find? (fun entry => entry.name == name)

private def planResolver (plan : ObjectPlan) : RefResolver := fun name => do
  let entry ← findEntry plan name
  some (entry.offset, entry.size)

mutual
  /-- Plan all object sizes and named byte ranges. Every object contains one
  explicit `STOP` seam between executable code and embedded child/data bytes,
  so ordinary Yul fall-through cannot execute payload bytes. -/
  def planObject (o : Object Op) : Option ObjectPlan :=
    match o with
    | .mk name code subObjects dataSegs => do
        let subPlans ← planObjects subObjects
        let placeholderCode ← resolveObjectStmts placeholderResolver code
        let instructions ← compile placeholderCode
        let codeSize := (assembleBytes instructions).length
        let childrenSize := (subPlans.map (·.bytecode.length)).sum
        let dataSize := (dataSegs.map (fun entry => entry.2.size)).sum
        let size := codeSize + 1 + childrenSize + dataSize
        if size < 2 ^ 256 then
          let children := childEntries (codeSize + 1) subPlans
          let dataLayout := dataEntries (codeSize + 1 + childrenSize) dataSegs
          let plan : ObjectPlan := {
            name, codeBlock := code, codeSize, size, subObjects := subPlans, dataSegs
            entries := { name, offset := 0, size } :: children ++ dataLayout
            bytecode := []
          }
          let resolvedCode ← resolveObjectStmts (planResolver plan) code
          let resolvedInstructions ← compile resolvedCode
          let executable := assembleBytes resolvedInstructions
          if executable.length != codeSize then none else
          let childBytecode := (subPlans.map (·.bytecode)).flatten
          let bytecode := executable ++ [0] ++ childBytecode ++ dataRegion dataSegs
          if bytecode.length == size then some { plan with bytecode } else none
        else
          none
    termination_by 2 * sizeOf o + 1

  def planObjects (os : List (Object Op)) : Option (List ObjectPlan) :=
    match os with
    | [] => some []
    | o :: objects => do
        return (← planObject o) :: (← planObjects objects)
    termination_by 2 * sizeOf os
end

private def entryKey (entry : ObjectEntry) : U256 :=
  litValue (.string entry.name)

private def entryMap (project : ObjectEntry → Nat) : List ObjectEntry → U256 → U256
  | [], _ => 0
  | entry :: entries, key =>
      if key = entryKey entry then BitVec.ofNat 256 (project entry)
      else entryMap project entries key

/-- Compile a complete object tree to executable EVM bytecode plus real
object-layout maps. References are actual offsets/sizes in the emitted bytes,
not Solidity's synthetic AST-interpreter values. -/
def compileResolvedObject (o : Object Op) : Option Layout := do
  let plan ← planObject o
  if !(plan.entries.map entryKey).Nodup then none else
  some {
    code := plan.bytecode
    dataOffset := entryMap (·.offset) plan.entries
    dataSize := entryMap (·.size) plan.entries
  }

/-! ### Consistency -/

/-- Reading `s.length` bytes at the seam offset `A.length` of `A ++ s ++ B`
returns exactly `s`. -/
theorem readBytes_middle (A s B : List UInt8) :
    readBytes (byteFrom (A ++ s ++ B)) A.length s.length = s := by
  simp only [readBytes, byteFrom]
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hi : i < s.length := by simpa using h1
    simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by simp; omega),
      List.getElem?_append_right (by omega),
      show A.length + i - A.length = i from by omega,
      List.getElem?_eq_getElem hi]
    rfl

/-- Every direct data segment has a matching `dataEntries` record and occupies
that record's byte range after an arbitrary prefix. -/
private theorem dataEntries_correct : ∀ (segs : List (String × Data)) (pre : List UInt8),
    ∀ p ∈ segs,
      ∃ entry ∈ dataEntries pre.length segs,
        entry.name = p.1 ∧ entry.size = p.2.size ∧
        entry.offset ≤ (pre ++ dataRegion segs).length ∧
        readBytes (byteFrom (pre ++ dataRegion segs)) entry.offset p.2.size = p.2.bytes := by
  intro segs
  induction segs with
  | nil => intro pre p hp; simp at hp
  | cons hd rest ih =>
      intro pre p hp
      obtain ⟨name, value⟩ := hd
      rcases List.mem_cons.mp hp with hp | hp
      · subst hp
        refine ⟨{ name, offset := pre.length, size := value.size }, by simp [dataEntries],
          rfl, rfl, by simp [dataRegion], ?_⟩
        rw [show dataRegion ((name, value) :: rest) = value.bytes ++ dataRegion rest by
          simp [dataRegion], ← List.append_assoc]
        exact readBytes_middle pre value.bytes (dataRegion rest)
      · obtain ⟨entry, hentry, hname, hsize, hoffset, hbytes⟩ :=
          ih (pre ++ value.bytes) p hp
        refine ⟨entry, ?_, hname, hsize, ?_, ?_⟩
        · simpa [dataEntries, List.length_append, YulSemantics.Data.size] using
            List.mem_cons_of_mem ({ name, offset := pre.length, size := value.size }) hentry
        · simpa [dataRegion, List.append_assoc] using hoffset
        · simpa [dataRegion, List.append_assoc] using hbytes

/-- A distinct-key entry list's generated map returns the selected projection
for every member. -/
private theorem entryMap_of_mem (project : ObjectEntry → Nat) :
    ∀ (entries : List ObjectEntry), (entries.map entryKey).Nodup →
      ∀ entry ∈ entries,
        entryMap project entries (entryKey entry) = BitVec.ofNat 256 (project entry) := by
  intro entries
  induction entries with
  | nil => intro _ entry h; simp at h
  | cons head rest ih =>
      intro hnodup entry hmem
      simp only [List.map_cons, List.nodup_cons] at hnodup
      rcases List.mem_cons.mp hmem with h | h
      · subst h
        simp [entryMap]
      · have hne : entryKey entry ≠ entryKey head := by
          intro heq
          exact hnodup.1 (heq ▸ List.mem_map_of_mem h)
        simp only [entryMap, if_neg hne]
        exact ih hnodup.2 entry h

/-- Successful planning places every direct data segment in the recorded
bytecode and records a matching entry for it. -/
private theorem planObject_directData {o : Object Op} {plan : ObjectPlan}
    (h : planObject o = some plan) :
    plan.dataSegs = o.dataSegs ∧ plan.bytecode.length < 2 ^ 256 ∧
      ∀ p ∈ o.dataSegs,
        ∃ entry ∈ plan.entries,
          entry.name = p.1 ∧ entry.size = p.2.size ∧ entry.offset < 2 ^ 256 ∧
          readBytes (byteFrom plan.bytecode) entry.offset p.2.size = p.2.bytes := by
  cases o with
  | mk name code subObjects dataSegs =>
      simp only [planObject, Option.bind_eq_bind] at h
      obtain ⟨subPlans, -, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨placeholderCode, -, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨instructions, -, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · rename_i hsmall
        obtain ⟨resolvedCode, -, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨resolvedInstructions, -, h⟩ := Option.bind_eq_some_iff.mp h
        split at h
        · cases h
        · rename_i hexecutable
          split at h
          · rename_i hlength
            simp only [Option.some.injEq] at h
            subst plan
            let executable := assembleBytes resolvedInstructions
            let childBytecode := (subPlans.map (·.bytecode)).flatten
            let pre := executable ++ [0] ++ childBytecode
            have hexecutable' : executable.length = (assembleBytes instructions).length := by
              simpa [executable] using hexecutable
            have hpre : pre.length =
                (assembleBytes instructions).length + 1 +
                  (subPlans.map (·.bytecode.length)).sum := by
              have hmap : subPlans.map (List.length ∘ fun x => x.bytecode) =
                  subPlans.map (fun x => x.bytecode.length) := by
                apply List.map_congr_left
                intro x hx
                rfl
              simp [pre, childBytecode, hexecutable']
              rw [hmap]
              omega
            have hbytecode :
                (executable ++ [0] ++ childBytecode ++ dataRegion dataSegs) =
                  pre ++ dataRegion dataSegs := by
              simp [pre, List.append_assoc]
            have hlength' :
                (executable ++ [0] ++ childBytecode ++ dataRegion dataSegs).length =
                  (assembleBytes instructions).length + 1 +
                    (subPlans.map (·.bytecode.length)).sum +
                      (dataSegs.map (fun entry => entry.2.size)).sum := by
              simpa [executable, childBytecode, YulSemantics.Data.size,
                dataRegion, hexecutable'] using hlength
            have hcodeSmall :
                (executable ++ [0] ++ childBytecode ++ dataRegion dataSegs).length <
                  2 ^ 256 := by
              rw [hlength']
              exact hsmall
            refine ⟨rfl, hcodeSmall, ?_⟩
            intro p hp
            obtain ⟨entry, hentry, hname, hsize, hoffset, hbytes⟩ :=
              dataEntries_correct dataSegs pre p hp
            refine ⟨entry, ?_, hname, hsize, ?_, ?_⟩
            · right
              apply List.mem_append_right
              simpa [hpre] using hentry
            · have hoffset' : entry.offset ≤
                  (executable ++ [0] ++ childBytecode ++ dataRegion dataSegs).length := by
                rw [hbytecode]
                exact hoffset
              omega
            · rw [hbytecode]
              exact hbytes
          · cases h
      · cases h

/-- The recursive resolved compiler faithfully places every direct data
segment in the bytecode range recorded by its public layout maps. -/
theorem compileResolvedObject_consistent {o : Object Op} {L : Layout}
    (h : compileResolvedObject o = some L) : L.Consistent o := by
  simp only [compileResolvedObject, Option.bind_eq_bind] at h
  obtain ⟨plan, hplan, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · cases h
  · rename_i hkeys
    simp only [Option.some.injEq] at h
    subst L
    have hnodup : (plan.entries.map entryKey).Nodup := by
      simpa using hkeys
    obtain ⟨-, -, hcorrect⟩ := planObject_directData hplan
    intro p hp
    obtain ⟨entry, hentry, hname, hsize, hoffset, hbytes⟩ := hcorrect p hp
    have hoff := entryMap_of_mem (·.offset) plan.entries hnodup entry hentry
    have hsz := entryMap_of_mem (·.size) plan.entries hnodup entry hentry
    constructor
    · simpa [entryKey, hname, hsize] using hsz
    · have hkey : litValue (.string p.1) = entryKey entry := by
        simp [entryKey, hname]
      change readBytes (byteFrom plan.bytecode)
        ((entryMap (·.offset) plan.entries (litValue (.string p.1))).toNat)
          p.2.size = p.2.bytes
      rw [hkey, hoff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoffset]
      exact hbytes

/-- Public object compiler: recursively resolved object bytecode and its
layout maps. -/
def compileObject := compileResolvedObject

/-- Public data-placement theorem for `compileObject`. -/
theorem compileObject_consistent {o : Object Op} {L : Layout}
    (h : compileObject o = some L) : L.Consistent o :=
  compileResolvedObject_consistent h

/-! ### End-to-end capstone

Composing consistency with the semantics' `constructorCode_returns_of_consistent`:
under the compiler-produced layout, the canonical constructor for any data
segment of the object halts, returning exactly that segment's bytes. -/

open YulSemantics (VEnv Run)
open YulSemantics.EVM (EvmState evm constructorCode constructorCode_returns_of_consistent)

/-- Under the layout `compileObject` produces, the canonical deploy-code for
any data segment `n` (of the object) returns exactly its bytes. -/
theorem compiled_constructor_returns {o : Object Op} {L : Layout}
    (h : compileObject o = some L) {n : Ident} {d : Data}
    (hmem : (n, d) ∈ o.dataSegs) (hlt : d.size < 2 ^ 256) :
    ∃ V st, Run evm (constructorCode n) L.initState V st .halt ∧
      st.halted = some (.ret, d.bytes) :=
  constructorCode_returns_of_consistent L o (compileObject_consistent h) hmem hlt

/-! ### Demonstration

A tiny object with a data segment: `compileObject` assembles a layout, and it
is consistent with the object — so (via `compiled_constructor_returns`) the
canonical constructor for `"blob"` returns `deadbeef`. -/

/-- `object "C" { code {} data "blob" hex"deadbeef" }`. -/
def demoObject : Object Op :=
  yulObject% object "C" {
    code { }
    data "blob" hex"deadbeef"
  }

/-- A constructor that copies and returns a recursively compiled child. -/
def demoNestedObject : Object Op :=
  yulObject% object "main" {
    code {
      datacopy(0, dataoffset("sub"), datasize("sub"))
      return(0, datasize("sub"))
    }
    object "sub" { code { stop() } }
  }

/-- The real object compiler emits a `STOP` seam before the data and records
the segment's actual offset and size. -/
example : (compileObject demoObject).map (·.code) = some [0, 0xde, 0xad, 0xbe, 0xef] := by
  native_decide

example : (compileObject demoObject).map (fun (layout : Layout) =>
    ((layout.dataOffset (litValue (.string "blob"))).toNat,
      (layout.dataSize (litValue (.string "blob"))).toNat)) = some (1, 4) := by
  native_decide

/-- The parent code is 167 bytes, followed by its seam; the two-byte child
(`STOP` plus its own seam) therefore begins at byte 168. -/
example : (compileObject demoNestedObject).map (fun (layout : Layout) =>
    ((layout.dataOffset (litValue (.string "sub"))).toNat,
      (layout.dataSize (litValue (.string "sub"))).toNat,
      layout.code.length)) = some (168, 2, 170) := by
  native_decide

/-- The produced layout is consistent with the object (`compileObject_consistent`
in action on a concrete instance). -/
example (L : Layout) (h : compileObject demoObject = some L) : L.Consistent demoObject :=
  compileObject_consistent h

end YulEvmCompiler
