import YulEvmCompiler.Correctness
import YulEvmCompiler.ObjectResolve
set_option warningAsError true
/-!
# YulEvmCompiler.ObjectCompile

The **object layer**: assembling a Yul `Object` into a deployed-bytecode
`Layout` (the artifact `YulSemantics.ObjectRun` is parameterized over), and
the key correctness content — that the produced layout is **consistent** with
the object, i.e. every `data` segment is faithfully placed in the deployed
bytecode at the recorded offset with the recorded size.

`compileObject` plans and compiles the complete tree recursively. It resolves
`dataoffset`/`datasize` to constants (emitted with minimal-width pushes, so a
fuel-bounded layout fixpoint re-derives sizes until stable), emits each
object's code, adds a `STOP` seam, and appends child-object bytecode followed
by direct data.
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

/-- A planned object layout. `codeSize` is obtained by re-compiling the code
under a fuel-bounded fixpoint (`planLoop`): because constant pushes now take
the minimal `PUSHk` width, replacing the zero placeholders with real offsets
and sizes can change push widths (hence positions), so the layout is iterated
until the recompiled length is stable. -/
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

/-- Layout entries are keyed by `litValue (.string ·)`, which keeps only the
first **32 UTF-8 bytes** of the name. Two entries whose names share a 32-byte
prefix therefore get the *same* key, and `compileResolvedObject`'s `Nodup` guard
rejects the *whole object tree* when that happens — even if nothing references
either name.

Ordinary input reaches it: solc emits a `.metadata` segment in every object, so
a grandchild contributes both `"parent.child"` and `"parent.child..metadata"`,
and those share a 32-byte prefix as soon as the two generated names total more
than 32 bytes (`"C_1234.C_1234_deployed"` already does at modest name lengths).

The second of that pair is the one to drop, and *not* because of its length: a
qualified name is unreferenceable exactly when `Validate.objectNameAllowed`
refuses it, i.e. when it starts with `"."` or contains `".."`. Joining a
`.`-prefixed data-segment name onto its parent always produces `".."`, so this
rule removes precisely the propagated `.metadata`-style entries and nothing
else. Dropping them removes only entries no program could ever name.

Length is deliberately *not* the criterion. Layout references are checked by
`objectNameAllowed`, not `literalWordWF`, so a name over 32 bytes is perfectly
legal — Solidity's own `long_object_name.yul` resolves the 33-byte
`"object2.object3.object4.datablock"`, and resolution matches entry names
exactly (`findEntry`), so it works regardless of key truncation. Filtering by
length would break it.

Direct data segments are built by `dataEntries` and are untouched, so
`Layout.Consistent` — which quantifies over an object's *direct* segments — is
unaffected. -/
private def shiftChildEntries (base : Nat) (child : ObjectPlan) : List ObjectEntry :=
  child.entries.filterMap fun entry =>
    if entry.name == child.name then
      some { entry with offset := base + entry.offset, size := child.bytecode.length }
    else
      let qualified := child.name ++ "." ++ entry.name
      if qualified.startsWith "." || qualified.contains ".." then
        none
      else
        some { name := qualified, offset := base + entry.offset, size := entry.size }

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

/-- One iteration of the object-layout fixpoint on the assumed code size `c`.
Given already-planned `subPlans`, build the candidate layout that assumes the
executable code occupies `c` bytes, resolve `dataoffset`/`datasize` against it,
recompile, and measure the true executable length `c'`.

- `some (.inl plan)` — the assumed size is a fixpoint (`c' = c`) and the fully
  assembled bytecode has the expected length: `plan` is finished.
- `some (.inr c')` — the assumption was wrong; retry with `c'`.
- `none` — a hard failure (layout does not fit a word, resolution/compilation
  failed, or the assembled length disagrees with the recorded size).

This calls only `compile`/`resolveObjectStmts`/entry builders on the given
`subPlans`; it never recurses on objects, so it lives outside the
`planObject`/`planObjects` mutual block. Because minimal-width pushes make the
recompiled length depend on the resolved constants, `planLoop` iterates
`planAttempt` (starting from the placeholder compile's length) until the length
stabilises; each accepted `ObjectPlan` still passes the same decidable
`length == size`/`length == codeSize` checks the downstream lemmas consume. -/
private def planAttempt (name : String) (code : List (YulSemantics.Stmt Op))
    (subPlans : List ObjectPlan) (dataSegs : List (String × Data)) (c : Nat) :
    Option (ObjectPlan ⊕ Nat) := do
  let childrenSize := (subPlans.map (·.bytecode.length)).sum
  let dataSize := (dataSegs.map (fun entry => entry.2.size)).sum
  let size := c + 1 + childrenSize + dataSize
  if size < 2 ^ 256 then
    let children := childEntries (c + 1) subPlans
    let dataLayout := dataEntries (c + 1 + childrenSize) dataSegs
    let plan : ObjectPlan := {
      name, codeBlock := code, codeSize := c, size, subObjects := subPlans, dataSegs
      entries := { name, offset := 0, size } :: children ++ dataLayout
      bytecode := []
    }
    let resolvedCode ← resolveObjectStmts (planResolver plan) code
    let resolvedInstructions ← compile resolvedCode
    let executable := assembleBytes resolvedInstructions
    let c' := executable.length
    if c' == c then
      let childBytecode := (subPlans.map (·.bytecode)).flatten
      let bytecode := executable ++ [0] ++ childBytecode ++ dataRegion dataSegs
      if bytecode.length == size then some (.inl { plan with bytecode }) else none
    else
      some (.inr c')
  else
    none

/-- Fuel-bounded iteration of `planAttempt`: keep retrying with each freshly
measured code size until a fixpoint is reached (`.inl`), a hard failure occurs
(`none`), or the fuel runs out (`none`). With minimal-width pushes the
placeholder-compile length can differ from the resolved length, so the loop
genuinely iterates; it converges in a couple of rounds (values and hence widths
are monotone in the assumed code size). -/
private def planLoop (name : String) (code : List (YulSemantics.Stmt Op))
    (subPlans : List ObjectPlan) (dataSegs : List (String × Data)) :
    Nat → Nat → Option ObjectPlan
  | 0, _ => none
  | fuel + 1, c =>
    match planAttempt name code subPlans dataSegs c with
    | none => none
    | some (.inl plan) => some plan
    | some (.inr c') => planLoop name code subPlans dataSegs fuel c'

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
        -- Iterate the layout fixpoint starting from the placeholder-compile
        -- length. With minimal-width pushes, resolving the (0,0) placeholders
        -- to real offsets/sizes can change push widths and hence byte
        -- positions, so `planLoop` re-derives the layout until the recompiled
        -- length is stable; the accepted plan still satisfies the same
        -- decidable length checks.
        planLoop name code subPlans dataSegs 34 codeSize
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

/-- Full specification of an accepted `planAttempt` iteration: it exposes the
resolved source and instruction stream behind the executable prefix, records
the assumed code size `c` as a genuine fixpoint (`executable.length = c`), and
fixes every field of the returned plan (name, code, children, data, entry
layout, size, and the exact `executable ++ [STOP] ++ children ++ data`
bytecode). These are precisely the facts the object-correctness lemmas
consume. -/
private theorem planAttempt_spec
    {name : String} {code : List (YulSemantics.Stmt Op)}
    {subPlans : List ObjectPlan} {dataSegs : List (String × Data)}
    {c : Nat} {plan : ObjectPlan}
    (h : planAttempt name code subPlans dataSegs c = some (.inl plan)) :
    ∃ resolved instructions,
      resolveObjectStmts (planResolver plan) code = some resolved ∧
      compile resolved = some instructions ∧
      (assembleBytes instructions).length = c ∧
      plan.name = name ∧
      plan.codeBlock = code ∧
      plan.subObjects = subPlans ∧
      plan.dataSegs = dataSegs ∧
      plan.codeSize = c ∧
      plan.size = c + 1 + (subPlans.map (·.bytecode.length)).sum
                    + (dataSegs.map (fun entry => entry.2.size)).sum ∧
      plan.size < 2 ^ 256 ∧
      plan.entries =
        { name, offset := 0, size := plan.size }
          :: childEntries (c + 1) subPlans
             ++ dataEntries (c + 1 + (subPlans.map (·.bytecode.length)).sum) dataSegs ∧
      plan.bytecode =
        assembleBytes instructions ++ [0]
          ++ (subPlans.map (·.bytecode)).flatten ++ dataRegion dataSegs ∧
      plan.bytecode.length = plan.size := by
  simp only [planAttempt, Option.bind_eq_bind] at h
  split at h
  · rename_i hsmall
    obtain ⟨resolvedCode, hresolvedCode, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨resolvedInstructions, hresolvedInstr, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · rename_i hcc
      split at h
      · rename_i hbc
        simp only [Option.some.injEq, Sum.inl.injEq] at h
        subst plan
        refine ⟨resolvedCode, resolvedInstructions, hresolvedCode, hresolvedInstr,
          ?_, rfl, rfl, rfl, rfl, rfl, ?_, hsmall, rfl, rfl, ?_⟩
        · simpa using hcc
        · rfl
        · simpa using hbc
      · simp at h
    · simp at h
  · simp at h

/-- If the fuel-bounded fixpoint loop returns a plan, that plan was produced by
some accepted `planAttempt` iteration. Lifts `planAttempt_spec` through the
loop by induction on the fuel. -/
private theorem planLoop_spec
    {name : String} {code : List (YulSemantics.Stmt Op)}
    {subPlans : List ObjectPlan} {dataSegs : List (String × Data)} :
    ∀ (fuel c : Nat) {plan : ObjectPlan},
      planLoop name code subPlans dataSegs fuel c = some plan →
        ∃ c', planAttempt name code subPlans dataSegs c' = some (.inl plan) := by
  intro fuel
  induction fuel with
  | zero => intro c plan h; simp [planLoop] at h
  | succ fuel ih =>
      intro c plan h
      unfold planLoop at h
      split at h
      · simp at h
      · rename_i plan' heq
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨c, heq⟩
      · rename_i c' heq
        exact ih c' h

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
      obtain ⟨c', hatt⟩ := planLoop_spec 34 _ h
      obtain ⟨resolved, instructions, hresolved, hinstructions, -, -, -, -, -, -, -, -,
        -, hbytecode, -⟩ := planAttempt_spec hatt
      refine ⟨resolved, instructions,
        (subPlans.map (·.bytecode)).flatten ++ dataRegion dataSegs, hresolved,
        hinstructions, ?_⟩
      rw [hbytecode]
      simp [List.append_assoc]

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
      obtain ⟨placeholderInstructions, -, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨c', hatt⟩ := planLoop_spec 34 _ h
      obtain ⟨resolved, instructions, -, -, hlen, -, -, -, hdata, -, -, hsmall,
        hentries, hbytecode, hbclen⟩ := planAttempt_spec hatt
      set executable := assembleBytes instructions with hexe
      set childBytecode := (subPlans.map (·.bytecode)).flatten with hcbc
      set pre := executable ++ [0] ++ childBytecode with hpreDef
      have hchild : childBytecode.length = (subPlans.map (·.bytecode.length)).sum := by
        have hmap : subPlans.map (List.length ∘ fun x => x.bytecode) =
            subPlans.map (fun x => x.bytecode.length) := by
          apply List.map_congr_left
          intro x _
          rfl
        simp only [hcbc, List.length_flatten, List.map_map]
        rw [hmap]
      have hpre : pre.length = c' + 1 + (subPlans.map (·.bytecode.length)).sum := by
        simp only [hpreDef, List.length_append, List.length_cons, List.length_nil, hlen,
          hchild]
      refine ⟨hdata, ?_, ?_⟩
      · rw [hbclen]; exact hsmall
      · intro p hp
        obtain ⟨entry, hentry, hname, hsize, hoffset, hbytes⟩ :=
          dataEntries_correct dataSegs pre p hp
        refine ⟨entry, ?_, hname, hsize, ?_, ?_⟩
        · rw [hentries]
          right
          apply List.mem_append_right
          simpa [hpre] using hentry
        · have hoffset' : entry.offset ≤ plan.bytecode.length := by
            rw [hbytecode]
            exact hoffset
          omega
        · rw [hbytecode]
          exact hbytes

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

/-! ### Backend-parameterized object planning

The same planning pipeline as `planObject`/`compileResolvedObject`, but with
the per-code-block compiler taken as a parameter, so an alternative verified
backend (the SSA-CFG backend, `YulEvmCompiler.SsaCfg.compileViaSsa`) can
drive the identical layout fixpoint. These are deliberately *parallel*
definitions — the proved `planObject` chain above is untouched — and they
live in this file only to reach the private resolver/entry helpers. The SSA
object-execution theorem will relate `compileResolvedObjectWith` to
`RunResolvedObject` the same way `compileObject_correct` does for the
classic chain. -/

/-- `planAttempt` with the block compiler as a parameter. -/
def planAttemptWith (compileFn : YulSemantics.Block Op → Option (List Instr))
    (name : String) (code : List (YulSemantics.Stmt Op))
    (subPlans : List ObjectPlan) (dataSegs : List (String × Data)) (c : Nat) :
    Option (ObjectPlan ⊕ Nat) := do
  let childrenSize := (subPlans.map (·.bytecode.length)).sum
  let dataSize := (dataSegs.map (fun entry => entry.2.size)).sum
  let size := c + 1 + childrenSize + dataSize
  if size < 2 ^ 256 then
    let children := childEntries (c + 1) subPlans
    let dataLayout := dataEntries (c + 1 + childrenSize) dataSegs
    let plan : ObjectPlan := {
      name, codeBlock := code, codeSize := c, size, subObjects := subPlans, dataSegs
      entries := { name, offset := 0, size } :: children ++ dataLayout
      bytecode := []
    }
    let resolvedCode ← resolveObjectStmts (planResolver plan) code
    let resolvedInstructions ← compileFn resolvedCode
    let executable := assembleBytes resolvedInstructions
    let c' := executable.length
    if c' == c then
      let childBytecode := (subPlans.map (·.bytecode)).flatten
      let bytecode := executable ++ [0] ++ childBytecode ++ dataRegion dataSegs
      if bytecode.length == size then some (.inl { plan with bytecode }) else none
    else
      some (.inr c')
  else
    none

/-- `planLoop` with the block compiler as a parameter. -/
def planLoopWith (compileFn : YulSemantics.Block Op → Option (List Instr))
    (name : String) (code : List (YulSemantics.Stmt Op))
    (subPlans : List ObjectPlan) (dataSegs : List (String × Data)) :
    Nat → Nat → Option ObjectPlan
  | 0, _ => none
  | fuel + 1, c =>
    match planAttemptWith compileFn name code subPlans dataSegs c with
    | none => none
    | some (.inl plan) => some plan
    | some (.inr c') => planLoopWith compileFn name code subPlans dataSegs fuel c'

mutual
  /-- `planObject` with the block compiler as a parameter. -/
  def planObjectWith (compileFn : YulSemantics.Block Op → Option (List Instr))
      (o : Object Op) : Option ObjectPlan :=
    match o with
    | .mk name code subObjects dataSegs => do
        let subPlans ← planObjectsWith compileFn subObjects
        let placeholderCode ← resolveObjectStmts placeholderResolver code
        let instructions ← compileFn placeholderCode
        let codeSize := (assembleBytes instructions).length
        planLoopWith compileFn name code subPlans dataSegs 34 codeSize
    termination_by 2 * sizeOf o + 1

  def planObjectsWith (compileFn : YulSemantics.Block Op → Option (List Instr))
      (os : List (Object Op)) : Option (List ObjectPlan) :=
    match os with
    | [] => some []
    | o :: objects => do
        return (← planObjectWith compileFn o) :: (← planObjectsWith compileFn objects)
    termination_by 2 * sizeOf os
end

/-- `compileResolvedObject` with the block compiler as a parameter. -/
def compileResolvedObjectWith
    (compileFn : YulSemantics.Block Op → Option (List Instr))
    (o : Object Op) : Option Layout := do
  let plan ← planObjectWith compileFn o
  if !(plan.entries.map entryKey).Nodup then none else
  some (layoutOfPlan plan)

/-- **PROTOTYPE, UNPROVEN.** Object compiler using the Asm window scheduler:
the backend-parameterized planning chain instantiated with `compileScheduled`
(the verified pipeline plus `Schedule.scheduleAsm`). A soundness proof for the
scheduler (translation validation, see `AsmScheduleSound`) collapses this into
`compileObject`. -/
def compileObjectScheduled (o : Object Op) : Option Layout :=
  compileResolvedObjectWith compileScheduled o


/-- Public data-placement theorem for `compileObject`. -/
theorem compileObject_consistent {o : Object Op} {L : Layout}
    (h : compileObject o = some L) : L.Consistent o :=
  compileResolvedObject_consistent h

/-! ### End-to-end capstones -/

open EvmSemantics
open EvmSemantics.EVM
open YulSemantics (VEnv Run Outcome)
open YulSemantics.EVM
  (EvmState evm evmWithExternal constructorCode constructorCode_returns_of_consistent)

variable [model : ExternalModel]
local notation "yulD" => evmWithExternal model.calls model.creates
set_option linter.unusedSectionVars false

/-- Object execution after layout references have been resolved, using
open-world external call/create relations. -/
def RunResolvedObject (o : Object Op) (L : Layout)
    (V : VEnv yulD) (st : EvmState) (out : Outcome) : Prop :=
  Run yulD (resolveForLayoutStmts L o.codeBlock) L.initState V st out

/-- **Object compiler correctness.** If the layout-resolved object executes
under the open-world dialect, then the emitted EVM bytecode simulates the same
execution. The theorem covers both ordinary fall-through through the
compiler-inserted `STOP` seam and source-level halts; recursively compiled
children and data are present in the frame as an inert trailing payload. -/
theorem compileObject_correct (hexternal : ExternalsRealized model)
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
    compile_correct_withPayload hexternal (payload := payload) hinstructions hrun'
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

/-- With minimal-width constant pushes and `labelWidth`-byte label pushes the
parent code is 10 bytes, followed by its seam; the two-byte child (`STOP` plus
its own seam) therefore begins at byte 11. -/
example : (compileObject demoNestedObject).map (fun (layout : Layout) =>
    ((layout.dataOffset (litValue (.string "sub"))).toNat,
      (layout.dataSize (litValue (.string "sub"))).toNat,
      layout.code.length)) = some (11, 2, 13) := by
  native_decide

/-- The produced layout is consistent with the object (`compileObject_consistent`
in action on a concrete instance). -/
example (L : Layout) (h : compileObject demoObject = some L) : L.Consistent demoObject :=
  compileObject_consistent h

end YulEvmCompiler
