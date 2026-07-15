import YulEvmCompiler.Correctness
import YulEvmCompiler.ObjectResolve

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

`compileObject_correct` is the full execution theorem: a `RunObject` derivation
under the produced layout is simulated by the emitted EVM bytecode, including
ordinary fall-through at the `STOP` seam and exact source-level halts. Its proof
composes semantic preservation of layout-reference resolution with a backend
simulation that admits embedded children and data as a trailing payload.

`compileObject_consistent` separately discharges `Layout.Consistent`, which —
composed with the semantics' already-proven
`constructorCode_returns_of_consistent` — shows that the canonical constructor
for any direct data segment returns exactly that segment's bytes
(`compiled_constructor_returns`).
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
    | .builtin op args =>
        match op, args with
        | .dataoffset, [.lit (.string name)] =>
            (resolve name).map fun entry => .lit (.number entry.1)
        | .datasize, [.lit (.string name)] =>
            (resolve name).map fun entry => .lit (.number entry.2)
        | _, _ => (resolveObjectExprs resolve args).map (.builtin op)
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
    | .switch condition cases none => do
        let condition ← resolveObjectExpr resolve condition
        let cases ← resolveObjectCases resolve cases
        return .switch condition cases none
    | .switch condition cases (some body) => do
        let condition ← resolveObjectExpr resolve condition
        let cases ← resolveObjectCases resolve cases
        let body ← resolveObjectStmts resolve body
        return .switch condition cases (some body)
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

/-- A partial planning resolver agrees with the total maps exposed by a
compiled layout whenever the partial resolver accepts a name. -/
private def ResolverAgrees (resolve : RefResolver) (L : Layout) : Prop :=
  ∀ name entry, resolve name = some entry →
    (L.dataOffset (litValue (.string name))).toNat = entry.1 ∧
    (L.dataSize (litValue (.string name))).toNat = entry.2

mutual
  /-- Successful partial expression resolution is exactly the total
  layout-based transformation when their reference maps agree. -/
  private theorem resolveObjectExpr_eq_layout {resolve : RefResolver} {L : Layout}
      (hagree : ResolverAgrees resolve L) :
      ∀ expression resolved,
        resolveObjectExpr resolve expression = some resolved →
          resolved = resolveForLayoutExpr L expression := by
    intro expression resolved h
    cases expression with
    | lit literal =>
        simp [resolveObjectExpr] at h
        subst resolved
        rfl
    | var name =>
        simp [resolveObjectExpr] at h
        subst resolved
        rfl
    | call name args =>
        simp only [resolveObjectExpr] at h
        cases hargs : resolveObjectExprs resolve args with
        | none => simp [hargs] at h
        | some args' =>
            simp [hargs] at h
            subst resolved
            rw [resolveForLayoutExpr]
            congr 1
            exact resolveObjectExprs_eq_layout hagree args args' hargs
    | builtin op args =>
        simp only [resolveObjectExpr] at h
        split at h
        · rename_i name
          obtain ⟨entry, href, rfl⟩ := Option.map_eq_some_iff.mp h
          have ha := hagree name entry href
          rw [resolveForLayoutExpr]
          congr 2
          exact ha.1.symm
        · rename_i name
          obtain ⟨entry, href, rfl⟩ := Option.map_eq_some_iff.mp h
          have ha := hagree name entry href
          rw [resolveForLayoutExpr]
          congr 2
          exact ha.2.symm
        · cases hargs : resolveObjectExprs resolve args with
          | none => simp [hargs] at h
          | some args' =>
              have hresolved := resolveObjectExprs_eq_layout hagree args args' hargs
              simp_all [resolveForLayoutExpr]

  private theorem resolveObjectExprs_eq_layout {resolve : RefResolver} {L : Layout}
      (hagree : ResolverAgrees resolve L) :
      ∀ expressions resolved,
        resolveObjectExprs resolve expressions = some resolved →
          resolved = resolveForLayoutExprs L expressions := by
    intro expressions resolved h
    cases expressions with
    | nil => simp [resolveObjectExprs] at h; subst resolved; rfl
    | cons expression expressions =>
        simp only [resolveObjectExprs] at h
        cases hhead : resolveObjectExpr resolve expression with
        | none => simp [hhead] at h
        | some head =>
            cases htail : resolveObjectExprs resolve expressions with
            | none => simp [hhead, htail] at h
            | some tail =>
                simp [hhead, htail] at h
                subst resolved
                rw [resolveForLayoutExprs]
                congr
                · exact resolveObjectExpr_eq_layout hagree expression head hhead
                · exact resolveObjectExprs_eq_layout hagree expressions tail htail
end

mutual
  private theorem resolveObjectStmt_eq_layout {resolve : RefResolver} {L : Layout}
      (hagree : ResolverAgrees resolve L) :
      ∀ statement resolved,
        resolveObjectStmt resolve statement = some resolved →
          resolved = resolveForLayoutStmt L statement := by
    intro statement resolved h
    cases statement with
    | block body =>
        cases hb : resolveObjectStmts resolve body with
        | none => simp [resolveObjectStmt, hb] at h
        | some body' =>
            simp [resolveObjectStmt, hb] at h
            subst resolved
            rw [resolveForLayoutStmt_block]
            congr 1
            exact resolveObjectStmts_eq_layout hagree body body' hb
    | funDef name params returns body =>
        cases hb : resolveObjectStmts resolve body with
        | none => simp [resolveObjectStmt, hb] at h
        | some body' =>
            simp [resolveObjectStmt, hb] at h
            subst resolved
            rw [resolveForLayoutStmt_funDef]
            congr 1
            exact resolveObjectStmts_eq_layout hagree body body' hb
    | letDecl names value =>
        cases value with
        | none => simp [resolveObjectStmt] at h; subst resolved; simp
        | some expression =>
            cases he : resolveObjectExpr resolve expression with
            | none => simp [resolveObjectStmt, he] at h
            | some expression' =>
                simp [resolveObjectStmt, he] at h
                subst resolved
                rw [resolveForLayoutStmt_letDecl]
                congr 2
                exact resolveObjectExpr_eq_layout hagree expression expression' he
    | assign names value =>
        cases he : resolveObjectExpr resolve value with
        | none => simp [resolveObjectStmt, he] at h
        | some value' =>
            simp [resolveObjectStmt, he] at h
            subst resolved
            rw [resolveForLayoutStmt_assign]
            congr 1
            exact resolveObjectExpr_eq_layout hagree value value' he
    | cond condition body =>
        cases hc : resolveObjectExpr resolve condition with
        | none => simp [resolveObjectStmt, hc] at h
        | some condition' =>
            cases hb : resolveObjectStmts resolve body with
            | none => simp [resolveObjectStmt, hc, hb] at h
            | some body' =>
                simp [resolveObjectStmt, hc, hb] at h
                subst resolved
                rw [resolveForLayoutStmt_cond]
                congr
                · exact resolveObjectExpr_eq_layout hagree condition condition' hc
                · exact resolveObjectStmts_eq_layout hagree body body' hb
    | «switch» condition cases fallback =>
        cases fallback with
        | none =>
            cases hc : resolveObjectExpr resolve condition with
            | none => simp [resolveObjectStmt, hc] at h
            | some condition' =>
                cases hcases : resolveObjectCases resolve cases with
                | none => simp [resolveObjectStmt, hc, hcases] at h
                | some cases' =>
                    simp [resolveObjectStmt, hc, hcases] at h
                    subst resolved
                    rw [resolveForLayoutStmt_switch]
                    congr
                    · exact resolveObjectExpr_eq_layout hagree condition condition' hc
                    · exact resolveObjectCases_eq_layout hagree cases cases' hcases
        | some fallback =>
            cases hc : resolveObjectExpr resolve condition with
            | none => simp [resolveObjectStmt, hc] at h
            | some condition' =>
                cases hcases : resolveObjectCases resolve cases with
                | none => simp [resolveObjectStmt, hc, hcases] at h
                | some cases' =>
                    cases hf : resolveObjectStmts resolve fallback with
                    | none => simp [resolveObjectStmt, hc, hcases, hf] at h
                    | some fallback' =>
                        simp [resolveObjectStmt, hc, hcases, hf] at h
                        subst resolved
                        rw [resolveForLayoutStmt_switch]
                        congr
                        · exact resolveObjectExpr_eq_layout hagree condition condition' hc
                        · exact resolveObjectCases_eq_layout hagree cases cases' hcases
                        · exact resolveObjectStmts_eq_layout hagree fallback fallback' hf
    | forLoop init condition post body =>
        cases hi : resolveObjectStmts resolve init with
        | none => simp [resolveObjectStmt, hi] at h
        | some init' =>
            cases hc : resolveObjectExpr resolve condition with
            | none => simp [resolveObjectStmt, hi, hc] at h
            | some condition' =>
                cases hp : resolveObjectStmts resolve post with
                | none => simp [resolveObjectStmt, hi, hc, hp] at h
                | some post' =>
                    cases hb : resolveObjectStmts resolve body with
                    | none => simp [resolveObjectStmt, hi, hc, hp, hb] at h
                    | some body' =>
                        simp [resolveObjectStmt, hi, hc, hp, hb] at h
                        subst resolved
                        rw [resolveForLayoutStmt_forLoop]
                        congr
                        · exact resolveObjectStmts_eq_layout hagree init init' hi
                        · exact resolveObjectExpr_eq_layout hagree condition condition' hc
                        · exact resolveObjectStmts_eq_layout hagree post post' hp
                        · exact resolveObjectStmts_eq_layout hagree body body' hb
    | exprStmt expression =>
        cases he : resolveObjectExpr resolve expression with
        | none => simp [resolveObjectStmt, he] at h
        | some expression' =>
            simp [resolveObjectStmt, he] at h
            subst resolved
            rw [resolveForLayoutStmt_exprStmt]
            congr 1
            exact resolveObjectExpr_eq_layout hagree expression expression' he
    | «break» => simp [resolveObjectStmt] at h; subst resolved; simp
    | «continue» => simp [resolveObjectStmt] at h; subst resolved; simp
    | «leave» => simp [resolveObjectStmt] at h; subst resolved; simp

  private theorem resolveObjectStmts_eq_layout {resolve : RefResolver} {L : Layout}
      (hagree : ResolverAgrees resolve L) :
      ∀ statements resolved,
        resolveObjectStmts resolve statements = some resolved →
          resolved = resolveForLayoutStmts L statements := by
    intro statements resolved h
    cases statements with
    | nil => simp [resolveObjectStmts] at h; subst resolved; rw [resolveForLayoutStmts_nil]
    | cons statement statements =>
        cases hhead : resolveObjectStmt resolve statement with
        | none => simp [resolveObjectStmts, hhead] at h
        | some head =>
            cases htail : resolveObjectStmts resolve statements with
            | none => simp [resolveObjectStmts, hhead, htail] at h
            | some tail =>
                simp [resolveObjectStmts, hhead, htail] at h
                subst resolved
                rw [resolveForLayoutStmts_cons]
                congr
                · exact resolveObjectStmt_eq_layout hagree statement head hhead
                · exact resolveObjectStmts_eq_layout hagree statements tail htail

  private theorem resolveObjectCases_eq_layout {resolve : RefResolver} {L : Layout}
      (hagree : ResolverAgrees resolve L) :
      ∀ cases resolved,
        resolveObjectCases resolve cases = some resolved →
          resolved = resolveForLayoutCases L cases := by
    intro cases resolved h
    cases cases with
    | nil => simp [resolveObjectCases] at h; subst resolved; rw [resolveForLayoutCases]
    | cons head cases =>
        rcases head with ⟨literal, body⟩
        cases hb : resolveObjectStmts resolve body with
        | none => simp [resolveObjectCases, hb] at h
        | some body' =>
            cases ht : resolveObjectCases resolve cases with
            | none => simp [resolveObjectCases, hb, ht] at h
            | some tail =>
                simp [resolveObjectCases, hb, ht] at h
                subst resolved
                rw [resolveForLayoutCases]
                congr
                · exact resolveObjectStmts_eq_layout hagree body body' hb
                · exact resolveObjectCases_eq_layout hagree cases tail ht
end

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

private def findEntry (plan : ObjectPlan) (name : String) : Option ObjectEntry :=
  plan.entries.find? (fun entry => entry.name == name)

private def planResolver (plan : ObjectPlan) : RefResolver := fun name => do
  let entry ← findEntry plan name
  some ((BitVec.ofNat 256 entry.offset).toNat,
    (BitVec.ofNat 256 entry.size).toNat)

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

private def layoutOfPlan (plan : ObjectPlan) : Layout := {
  code := plan.bytecode
  dataOffset := entryMap (·.offset) plan.entries
  dataSize := entryMap (·.size) plan.entries
}

/-- Compile a complete object tree to executable EVM bytecode plus real
object-layout maps. References are actual offsets/sizes in the emitted bytes,
not Solidity's synthetic AST-interpreter values. -/
def compileResolvedObject (o : Object Op) : Option Layout := do
  let plan ← planObject o
  if !(plan.entries.map entryKey).Nodup then none else
  some (layoutOfPlan plan)

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

/-- The resolver used to compile a plan returns exactly the values exposed by
that plan's public layout maps. This is the semantic link between the partial
reference-resolution pass and `dataoffset`/`datasize` in `RunObject`. -/
private theorem planResolver_agrees (plan : ObjectPlan)
    (hnodup : (plan.entries.map entryKey).Nodup) :
    ResolverAgrees (planResolver plan) (layoutOfPlan plan) := by
  intro name value href
  simp only [planResolver, Option.bind_eq_bind] at href
  obtain ⟨entry, hfind, hvalue⟩ := Option.bind_eq_some_iff.mp href
  simp only [Option.some.injEq] at hvalue
  subst value
  have hmem : entry ∈ plan.entries := List.mem_of_find?_eq_some hfind
  have hname : entry.name = name := by
    have hselected := List.find?_some hfind
    simpa [findEntry] using hselected
  have hoff := entryMap_of_mem (·.offset) plan.entries hnodup entry hmem
  have hsize := entryMap_of_mem (·.size) plan.entries hnodup entry hmem
  constructor
  · simpa [layoutOfPlan, entryKey, hname] using congrArg BitVec.toNat hoff
  · simpa [layoutOfPlan, entryKey, hname] using congrArg BitVec.toNat hsize

/-- A successful plan retains the resolved source and instruction stream that
produced its executable prefix. Everything after the explicit zero byte is an
opaque payload to the block compiler's simulation theorem. -/
private theorem planObject_compileWitness {o : Object Op} {plan : ObjectPlan}
    (h : planObject o = some plan) :
    ∃ resolved instructions payload,
      resolveObjectStmts (planResolver plan) o.codeBlock = some resolved ∧
      compile resolved = some instructions ∧
      plan.bytecode = assembleBytes instructions ++ 0 :: payload := by
  cases o with
  | mk name code subObjects dataSegs =>
      simp only [planObject, Option.bind_eq_bind] at h
      obtain ⟨subPlans, -, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨placeholderCode, -, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨placeholderInstructions, -, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · obtain ⟨resolved, hresolved, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨instructions, hinstructions, h⟩ := Option.bind_eq_some_iff.mp h
        split at h
        · cases h
        · split at h
          · simp only [Option.some.injEq] at h
            subst plan
            refine ⟨resolved, instructions,
              (subPlans.map (·.bytecode)).flatten ++ dataRegion dataSegs, ?_,
              hinstructions, ?_⟩
            · change resolveObjectStmts (planResolver _) code = some resolved
              exact hresolved
            · simp [List.append_assoc]
          · cases h
      · cases h

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
    · simpa [layoutOfPlan, entryKey, hname, hsize] using hsz
    · have hkey : litValue (.string p.1) = entryKey entry := by
        simp [entryKey, hname]
      change readBytes (byteFrom plan.bytecode)
        ((entryMap (·.offset) plan.entries (litValue (.string p.1))).toNat)
          p.2.size = p.2.bytes
      rw [hkey, hoff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoffset]
      exact hbytes

/-- Successful object compilation exposes an instruction stream for the total
layout-resolved source, followed by the explicit `STOP` seam and an arbitrary
embedded payload. -/
private theorem compileResolvedObject_compileWitness {o : Object Op} {L : Layout}
    (h : compileResolvedObject o = some L) :
    ∃ resolved instructions payload,
      resolved = resolveForLayoutStmts L o.codeBlock ∧
      compile resolved = some instructions ∧
      L.code = assembleBytes instructions ++ 0 :: payload := by
  simp only [compileResolvedObject, Option.bind_eq_bind] at h
  obtain ⟨plan, hplan, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · cases h
  · rename_i hkeys
    simp only [Option.some.injEq] at h
    subst L
    have hnodup : (plan.entries.map entryKey).Nodup := by
      simpa using hkeys
    obtain ⟨resolved, instructions, payload, hresolved, hinstructions, hcode⟩ :=
      planObject_compileWitness hplan
    have hresolved' :=
      resolveObjectStmts_eq_layout (planResolver_agrees plan hnodup)
        o.codeBlock resolved hresolved
    exact ⟨resolved, instructions, payload, hresolved', hinstructions, hcode⟩

/-- Public object compiler: recursively resolved object bytecode and its
layout maps. -/
def compileObject := compileResolvedObject

/-- Public data-placement theorem for `compileObject`. -/
theorem compileObject_consistent {o : Object Op} {L : Layout}
    (h : compileObject o = some L) : L.Consistent o :=
  compileResolvedObject_consistent h

/-! ### End-to-end capstones -/

open EvmSemantics
open EvmSemantics.EVM
open YulSemantics (VEnv Run Outcome)
open YulSemantics.EVM
  (EvmState evm evmWithCalls constructorCode constructorCode_returns_of_consistent)

variable [model : ExternalModel]
local notation "yulD" => evmWithCalls model.calls
set_option linter.unusedSectionVars false

/-- Object execution after layout references have been resolved, using an
open-world external-call relation. -/
def RunResolvedObject (o : Object Op) (L : Layout)
    (V : VEnv yulD) (st : EvmState) (out : Outcome) : Prop :=
  Run yulD (resolveForLayoutStmts L o.codeBlock) L.initState V st out

/-- **Object compiler correctness.** If the layout-resolved object executes
under the open-world dialect, then the emitted EVM bytecode simulates the same
execution. The theorem covers both ordinary fall-through through the
compiler-inserted `STOP` seam and source-level halts; recursively compiled
children and data are present in the frame as an inert trailing payload. -/
theorem compileObject_correct (hcalls : CallsRealized model.calls)
    {o : Object Op} {L : Layout}
    (hcomp : compileObject o = some L)
    {V : VEnv yulD} {yst : EvmState} {out : Outcome}
    (hrun : RunResolvedObject o L V yst out) :
    ∃ b : Nat, ∀ s0 : State,
      FrameOK (mkCode L.code) s0 → StateMatch L.initState s0 →
      s0.pc = UInt256.ofNat 0 → s0.stack = [] → b ≤ s0.gasAvailable →
      ∃ s', Steps s0 s' ∧ s'.callStack = [] ∧ StateMatch yst s' ∧
        ((out = .normal ∧ s'.halt = .Success ∧ s'.hReturn = .empty) ∨
         (out = .halt ∧ HaltedMatch yst s')) := by
  obtain ⟨resolved, instructions, payload, hresolved, hinstructions, hcode⟩ :=
    compileResolvedObject_compileWitness hcomp
  have hrun' : Run yulD resolved L.initState V yst out := by
    rw [hresolved]
    exact hrun
  obtain ⟨bound, hsim⟩ :=
    compile_correct_withPayload hcalls (payload := payload) hinstructions hrun'
  refine ⟨bound, ?_⟩
  intro s0 hframe hmatch hpc hstack hgas
  apply hsim s0
  · simpa [assembleWithPayload, hcode] using hframe
  · exact hmatch
  · exact hpc
  · exact hstack
  · exact hgas

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
