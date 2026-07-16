import YulEvmCompiler.Correctness
import YulEvmCompiler.ObjectCompile
import YulParser
import YulParser.SoundC

/-!
# SpecClosure — the audited specification boundary, extracted mechanically

This file computes the **specification closure** of the project's headline
guarantees: the set of declarations a human must read and agree with in order
to trust that the correctness theorems *say what they should*. It is the dual
of `Checks.lean`. Where `Checks.lean` walks each theorem's **proof term** to pin
the trusted axiom base, this file walks each theorem's **statement (type)** to
pin the trusted *specification* — the match relations, frame conditions,
outcome correspondences, AST/target data types, and external-semantics entry
points the guarantee is phrased in terms of.

The central invariant that makes the extraction meaningful: **we never traverse
theorem bodies.** Every one of the project's ~400 preservation lemmas lives in a
proof term, so they all vanish automatically; what survives the type-closure is
exactly the specification vocabulary.

## What the closure records

Starting from `roots` (the headline theorems), we transitively collect every
constant reachable through **types** — and, for `def`s whose result is a
`Prop`/sort (the *relations*) and for other spec-level `def`s, through their
**values** too (a relation's body *is* its specification). We stop recursing at
the boundary of the two pinned external semantics (`YulSemantics.*`,
`EvmSemantics.*`): those are trusted ground truth, recorded as boundary nodes
but not unfolded. Lean/Mathlib/`Init`/`Std` core is dropped entirely.

Each surviving declaration is bucketed:

* **this-repo audited surface** — the ~project-local declarations that define
  the correctness criterion. These are hashed by *type and value* (so any
  change to their meaning is detected), except:
* **artifact** declarations (`artifactDefs`) — the compiler/parser *code* being
  verified (`compile`, `compileObject`, `parseBlock`, `parseObject`). Only their
  **type signatures** are pinned; their bodies may change freely under
  autoresearch. This is the whole point: AI may rewrite the algorithm and its
  proofs, but touching anything in the audited surface trips this check.
* **external boundary** — the yul-semantics / evm-semantics entry points the
  guarantee is stated against, summarised by a single combined hash.

## The two CI gates

1. `lake env lean SpecClosure.lean` elaborates the `#guard_msgs` block below,
   which pins the compact closure signature. If a new declaration enters the
   audited surface, or an audited declaration's meaning changes, the printed
   message changes and elaboration fails — a human must re-audit and re-pin.
2. The same command regenerates `SPEC.md` (the human-readable manifest + graph);
   CI then runs `git diff --exit-code SPEC.md` so the doc cannot drift from the
   code.

Neither gate fires when the compiler algorithm or any proof changes — only when
the *specification* does.

## Re-pinning after a legitimate spec change

Run `scripts/update-spec.sh` (which sets `SPEC_REPIN=1`): it regenerates
`SPEC.md` and rewrites this file's own pinned block in place, then verifies it.
Review the resulting diff — it is the audit artifact. This file is
human-approval-only (`.github/CODEOWNERS`, `AGENTS.md`): automated agents must
not re-pin, or a spec change could approve itself.
-/

open Lean

set_option linter.unusedVariables false

namespace SpecClosure

/-! ## Human-audited inputs

These two lists are the only manual classification. Everything else is derived.
If a data-valued definition ever enters the closure that is not listed in
`artifactDefs`, it is conservatively treated as **audited** (its body is hashed),
so the failure mode is always "a human must look at this", never silent drift. -/

/-- The headline guarantees whose *statements* constitute the specification. -/
def roots : List Name :=
  [ ``YulEvmCompiler.compile_correct
  , ``YulEvmCompiler.compile_correct_eval
  , ``YulEvmCompiler.compile_correct_withPayload
  , ``YulEvmCompiler.compileObject_correct
  , ``YulEvmCompiler.compileObject_consistent
  , ``YulEvmCompiler.compiled_constructor_returns
  , ``YulParser.parse_canon_block
  , ``YulParser.parse_canon_obj ]

/-- Repo-local, data-valued definitions that are the **artifact** (the code
being verified), not the specification. Only their type signatures are pinned;
their implementations may change freely. We never recurse into their bodies, so
the compiler/parser internals never enter the audited surface. -/
def artifactDefs : List Name :=
  [ ``YulEvmCompiler.compile
  , ``YulEvmCompiler.compileProgram
  , ``YulEvmCompiler.compileObject
  , ``YulParser.parseBlock
  , ``YulParser.parseObject ]

/-! ## Package bucketing -/

inductive Pkg | this | yul | evm | core
  deriving DecidableEq, Repr, Inhabited

def Pkg.tag : Pkg → String
  | .this => "this" | .yul => "yul-sem" | .evm => "evm-sem" | .core => "core"

/-- Top (leftmost) component of a name, as a string. -/
def topComponent (n : Name) : String :=
  match n.components with
  | c :: _ => c.toString
  | []     => ""

def pkgOfModule (m : Name) : Pkg :=
  match topComponent m with
  | "YulEvmCompiler" | "YulParser" => .this
  | "YulSemantics" => .yul
  | "EvmSemantics" => .evm
  | _ => .core

def pkgOfConst (env : Environment) (n : Name) : Pkg :=
  match env.getModuleIdxFor? n with
  | some idx => pkgOfModule env.allImportedModuleNames[idx]!
  | none => .core

/-! ## Classification of an audited (this-repo) declaration -/

inductive Kind
  | statement   -- a headline theorem's signature
  | relation    -- a `Prop`/sort-valued definition (a match relation / predicate)
  | struct      -- a structure or inductive (its fields are the spec)
  | datadef     -- a data-valued spec definition (audited body: e.g. `resultOf`, `canon`)
  | artifact    -- verified code; only its signature is pinned
  | other       -- theorems/recursors reached through a type; signature only
  deriving DecidableEq, Repr, Inhabited

def Kind.tag : Kind → String
  | .statement => "statement" | .relation => "relation" | .struct => "struct"
  | .datadef => "datadef" | .artifact => "artifact" | .other => "other"

/-- Does the type's ultimate codomain land in a sort (`Prop`/`Type _`)? Such a
`def` is a relation/predicate whose body is part of the specification. -/
partial def resultIsSort : Expr → Bool
  | .forallE _ _ b _ => resultIsSort b
  | .mdata _ e       => resultIsSort e
  | .sort _          => true
  | _                => false

/-- Cheap deterministic hash combiner (FNV-style over the structural
`Expr.hash`, which is stable within a pinned toolchain). -/
def mix (a b : UInt64) : UInt64 := (a ^^^ b) * 1099511628211

def valueHash (ci : ConstantInfo) : UInt64 :=
  match ci.value? (allowOpaque := true) with
  | some v => v.hash
  | none   => 0

def lastStr : Name → String
  | .str _ s => s
  | _        => ""

/-- Last-component prefixes that mark a compiler-generated auxiliary
declaration (recursors, `casesOn`, `below`/`brecOn`, `ctorIdx`, derived
instances, …) not caught by `isInternalDetail`. -/
def genPrefixes : List String :=
  [ "casesOn", "recOn", "rec", "brecOn", "binductionOn", "below", "ibelow"
  , "noConfusion", "injEq", "sizeOf", "repr", "toCtorIdx", "ctorIdx"
  , "ndrec", "fold", "elim", "inst" ]

/-- Is `n` a compiler-generated auxiliary (to be folded into its real parent)? -/
def isAux (env : Environment) (n : Name) : Bool :=
  n.isInternalDetail
    || env.isProjectionFn n
    || (match env.find? n with | some (.ctorInfo _) => true | _ => false)
    || (let s := lastStr n; genPrefixes.any (fun p => s.startsWith p))

/-- Strip auxiliary suffixes until reaching a candidate real declaration. -/
partial def stripToReal (env : Environment) (n : Name) : Name :=
  if isAux env n then
    let p := n.getPrefix
    if p.isAnonymous then n else stripToReal env p
  else n

/-- Classify a *real* this-repo declaration: its `Kind` and whether its value
should be traversed (and hashed). -/
def classify (env : Environment) (n : Name) (ci : ConstantInfo) : Kind × Bool :=
  if n ∈ roots then (.statement, false)
  else match ci with
    | .thmInfo _ | .recInfo _ | .quotInfo _ | .axiomInfo _ => (.other, false)
    | .inductInfo _ | .ctorInfo _ => (.struct, false)
    | .defnInfo _ | .opaqueInfo _ =>
        if n ∈ artifactDefs then (.artifact, false)
        else if resultIsSort ci.type then (.relation, true)
        else (.datadef, true)

structure Node where
  name : Name
  pkg  : Pkg
  kind : Kind
  hash : UInt64
  deriving Inhabited

/-- Compute the specification closure from `roots`. Auxiliary declarations fold
their content hash into their real parent (via XOR, so the result is independent
of visitation order). Returns audited this-repo nodes and external boundary
nodes. -/
partial def closure (env : Environment) :
    Std.HashMap Name Node × Std.HashMap Name Node := Id.run do
  let mut thisNodes : Std.HashMap Name Node := {}
  let mut extNodes  : Std.HashMap Name Node := {}
  let mut visited   : Std.HashSet Name := {}
  let mut stack     : List Name := roots
  while !stack.isEmpty do
    let n := stack.head!
    stack := stack.tail!
    if visited.contains n then continue
    visited := visited.insert n
    match env.find? n with
    | none => continue
    | some ci =>
      match pkgOfConst env n with
      | .core => pure ()                               -- trusted; drop
      | .yul | .evm =>                                 -- boundary: record, don't recurse
        let pkg := pkgOfConst env n
        if !(isAux env n) then
          extNodes := extNodes.insert n ⟨n, pkg, .other, ci.type.hash⟩
      | .this =>
        -- The real declaration this (possibly auxiliary) name belongs to.
        let parent := stripToReal env n
        let parentReal :=
          !(isAux env parent) && (env.find? parent).isSome && pkgOfConst env parent == .this
        -- Whether to fold this decl's *value* into the hash / traverse it.
        let parentArtifact := parent ∈ artifactDefs
        let includeValue := !parentArtifact &&
          (match ci with
            | .thmInfo _ | .recInfo _ | .quotInfo _ | .axiomInfo _ => false
            | _ => true)
        -- This decl's content contribution.
        let contrib := mix (mix n.hash ci.type.hash) (if includeValue then valueHash ci else 0)
        if parentReal then
          -- Ensure the parent is itself processed (classified) …
          if !visited.contains parent then stack := parent :: stack
          -- … and fold this contribution into the parent node.
          match env.find? parent with
          | some pci =>
            let (kind, _) := classify env parent pci
            let prev := (thisNodes[parent]?).map (·.hash) |>.getD 0
            thisNodes := thisNodes.insert parent ⟨parent, .this, kind, prev ^^^ contrib⟩
          | none => pure ()
        -- Recurse into dependencies. Types are always followed (to discover the
        -- data-type vocabulary); values only for non-artifact declarations.
        for d in ci.type.getUsedConstants do
          if !visited.contains d then stack := d :: stack
        if !parentArtifact then
          if includeValue then
            match ci.value? (allowOpaque := true) with
            | some v =>
              for d in v.getUsedConstants do
                if !visited.contains d then stack := d :: stack
            | none => pure ()
          -- Structures: enqueue constructors so their field types are folded in.
          match ci with
          | .inductInfo iv =>
            for c in iv.ctors do
              if !visited.contains c then stack := c :: stack
          | _ => pure ()
  return (thisNodes, extNodes)

/-! ## Rendering -/

def hex (u : UInt64) : String :=
  let digits := "0123456789abcdef".toList.toArray
  let rec go (fuel : Nat) (v : UInt64) (acc : String) : String :=
    match fuel with
    | 0 => acc
    | fuel+1 =>
      if v == 0 && acc.length > 0 then acc
      else go fuel (v / 16) (String.ofList [digits[(v % 16).toNat]!] ++ acc)
  let s := go 16 u ""
  if s.isEmpty then "0" else s

def sortedNodes (m : Std.HashMap Name Node) : Array Node :=
  let arr := m.toArray.map (·.2)
  arr.qsort (fun a b => a.name.toString < b.name.toString)

/-- Combined hash over the external boundary (order-independent via sort). -/
def boundaryHash (ext : Std.HashMap Name Node) : UInt64 :=
  (sortedNodes ext).foldl (fun acc nd => mix acc (mix nd.name.hash nd.hash)) 1469598103934665603

/-- The compact, machine-pinned signature (the frozen contract). -/
def signature (env : Environment) : String := Id.run do
  let (thisNodes, extNodes) := closure env
  let audited := sortedNodes thisNodes
  let mut lines : Array String := #[]
  lines := lines.push s!"SPEC CLOSURE — audited this-repo surface ({audited.size} decls)"
  for nd in audited do
    lines := lines.push s!"  {nd.kind.tag} {nd.name} {hex nd.hash}"
  lines := lines.push
    s!"external boundary: {extNodes.size} decls, combined hash {hex (boundaryHash extNodes)}"
  return String.intercalate "\n" lines.toList

/-! ## Human-readable manifest (`SPEC.md`) -/

def countKind (nodes : Array Node) (k : Kind) : Nat :=
  (nodes.filter (·.kind == k)).size

instance : BEq Kind := ⟨fun a b => a.tag == b.tag⟩

def report (env : Environment) : String := Id.run do
  let (thisNodes, extNodes) := closure env
  let audited := sortedNodes thisNodes
  let ext := sortedNodes extNodes
  let mut o : Array String := #[]
  o := o.push "# The audited specification boundary"
  o := o.push ""
  o := o.push "> **Generated by `SpecClosure.lean` — do not edit by hand.**"
  o := o.push "> Regenerate with `lake env lean SpecClosure.lean`."
  o := o.push ""
  o := o.push "This is the *minimal stable spec*: the declarations a human must read and"
  o := o.push "agree with to trust that the correctness theorems say what they should. It is"
  o := o.push "computed by walking each headline theorem's **statement** (never its proof),"
  o := o.push "so the hundreds of preservation lemmas are excluded automatically — what"
  o := o.push "remains is exactly the specification vocabulary."
  o := o.push ""
  o := o.push s!"**Audited surface: {audited.size} declarations** \\"
  o := o.push s!"relations: {countKind audited .relation} · structures: {countKind audited .struct} · data defs: {countKind audited .datadef} · statements: {countKind audited .statement} · artifact signatures: {countKind audited .artifact} \\"
  o := o.push s!"**External boundary: {ext.size} declarations** across the two pinned semantics."
  o := o.push ""
  o := o.push "Axioms are pinned separately in `Checks.lean` (only `propext`,"
  o := o.push "`Classical.choice`, `Quot.sound`). Anti-vacuity (that the accepted-program"
  o := o.push "coverage never shrinks) is enforced by the differential corpora in CI; see"
  o := o.push "`DESIGN.md`."
  o := o.push ""
  -- Tiered boundary diagram.
  let yulN := (ext.filter (fun nd => nd.pkg.tag == "yul-sem")).size
  let evmN := (ext.filter (fun nd => nd.pkg.tag == "evm-sem")).size
  o := o.push "## The boundary at a glance"
  o := o.push ""
  o := o.push "```mermaid"
  o := o.push "flowchart TD"
  o := o.push "  subgraph audited [\"audited this-repo surface — a human signs off on these\"]"
  o := o.push s!"    S[\"Headline theorem statements ({countKind audited .statement})\"]"
  o := o.push s!"    R[\"Match relations & predicates ({countKind audited .relation})\"]"
  o := o.push s!"    T[\"Structures & data types ({countKind audited .struct})\"]"
  o := o.push s!"    D[\"Data definitions ({countKind audited .datadef})\"]"
  o := o.push s!"    A[\"Artifact signatures ({countKind audited .artifact}) — type only, bodies free\"]"
  o := o.push "  end"
  o := o.push "  subgraph external [\"trusted ground truth — pinned dependency semantics\"]"
  o := o.push s!"    YUL[\"yul-semantics entry points ({yulN})\"]"
  o := o.push s!"    EVM[\"evm-semantics entry points ({evmN})\"]"
  o := o.push "  end"
  o := o.push "  AX[\"Axiom base: propext, Classical.choice, Quot.sound (Checks.lean)\"]"
  o := o.push "  S --> R & T & D & A"
  o := o.push "  R --> T & YUL & EVM"
  o := o.push "  D --> T"
  o := o.push "  T --> YUL & EVM"
  o := o.push "  S -.->|proof term, trusted| AX"
  o := o.push "```"
  o := o.push ""
  -- audited surface, grouped
  let group (k : Kind) (title : String) (desc : String) : Array String := Id.run do
    let ns := audited.filter (·.kind == k)
    if ns.isEmpty then return #[]
    let mut g : Array String := #[]
    g := g.push s!"### {title}"
    g := g.push ""
    g := g.push desc
    g := g.push ""
    g := g.push "| declaration | hash |"
    g := g.push "|---|---|"
    for nd in ns do
      g := g.push s!"| `{nd.name}` | `{hex nd.hash}` |"
    g := g.push ""
    return g
  o := o.push "## Audited this-repo surface"
  o := o.push ""
  o := o ++ group .statement "Theorem statements"
    "The shape of each guarantee. Read these first: the honest scoping lives here."
  o := o ++ group .relation "Match relations & predicates (bodies audited)"
    "How a source state/outcome corresponds to a target state/outcome. The heart of the spec."
  o := o ++ group .struct "Structures & data types (fields audited)"
    "The vocabulary the guarantee is phrased in."
  o := o ++ group .datadef "Data definitions (bodies audited)"
    "Concrete spec-level functions (outcome maps, canonicalisation, byte assembly)."
  o := o ++ group .artifact "Artifact signatures (type only — bodies may change freely)"
    "The code being verified. Only the signatures are frozen; implementations are free."
  o := o ++ group .other "Other (signatures only)"
    "Recursors/auxiliary constants reached through a type."
  -- external boundary
  o := o.push s!"## External-semantics boundary ({ext.size} decls, combined hash `{hex (boundaryHash extNodes)}`)"
  o := o.push ""
  o := o.push "The entry points of the two pinned semantics the guarantee is stated against."
  o := o.push "These are trusted ground truth (auditing them = believing they model real Yul"
  o := o.push "and real EVM); they are recorded but not unfolded."
  o := o.push ""
  for pkg in [Pkg.yul, Pkg.evm] do
    let ns := ext.filter (fun nd => nd.pkg.tag == pkg.tag)
    if !ns.isEmpty then
      o := o.push s!"### {pkg.tag} ({ns.size})"
      o := o.push ""
      let names := ns.map (fun nd => s!"`{nd.name}`")
      o := o.push (String.intercalate ", " names.toList)
      o := o.push ""
  return String.intercalate "\n" o.toList

/-! ## Self-updating the pinned block

`SpecClosure.lean` carries its own frozen `#guard_msgs` block, delimited by the
sentinels below. `pinnedBlock` regenerates that region from the current
environment; `splicePin` replaces it in a source string. The doc-write command
uses these to re-pin the file in place when run with `SPEC_REPIN=1` (see
`scripts/update-spec.sh`). CI never sets that variable, so it only ever checks. -/

-- The marker text is split across `++` so these definitions do not themselves
-- contain the contiguous sentinel string — otherwise `splicePin` would match
-- here instead of the real comment lines it is meant to replace.
def beginSentinel : String :=
  "-- " ++ "BEGIN SPEC CLOSURE PIN (generated by scripts/update-spec.sh — do not edit by hand)"
def endSentinel : String :=
  "-- " ++ "END SPEC CLOSURE PIN"

/-- The full sentinel-delimited pinned region, regenerated from `env`. -/
def pinnedBlock (env : Environment) : String :=
  beginSentinel ++ "\n"
    ++ "/-- info:\n" ++ signature env ++ "\n-/\n"
    ++ "#guard_msgs in\n"
    ++ "open SpecClosure in\n"
    ++ "run_cmd do Lean.logInfo (signature (← getEnv))\n"
    ++ endSentinel

/-- Text of `s` before the first occurrence of `marker`. -/
def beforeFirst (s marker : String) : String := (s.splitOn marker).headD s

/-- Text of `s` after the first occurrence of `marker`, if present. -/
def afterFirst (s marker : String) : Option String :=
  match s.splitOn marker with
  | _ :: rest@(_ :: _) => some (String.intercalate marker rest)
  | _ => none

/-- Replace the sentinel-delimited region of `src` with `pin`. Returns `src`
unchanged if the sentinels are not both found (fail-safe). -/
def splicePin (src pin : String) : String :=
  match afterFirst src beginSentinel with
  | none => src
  | some afterBegin =>
    match afterFirst afterBegin endSentinel with
    | none => src
    | some afterEnd => beforeFirst src beginSentinel ++ pin ++ afterEnd

end SpecClosure

/-! ## CI gate 2 — regenerate the human-readable manifest (and, on demand, re-pin).

Always regenerates `SPEC.md` (CI runs `git diff --exit-code SPEC.md` so the
manifest cannot drift). When `SPEC_REPIN=1` is set — only by
`scripts/update-spec.sh`, never in CI — it also rewrites this file's own pinned
block in place, so a legitimate spec change is re-pinned by one command. -/

open SpecClosure in
run_cmd do
  let env ← getEnv
  IO.FS.writeFile "SPEC.md" (report env)
  if (← IO.getEnv "SPEC_REPIN").isSome then
    let path := "SpecClosure.lean"
    let src ← IO.FS.readFile path
    IO.FS.writeFile path (splicePin src (pinnedBlock env))

/-! ## CI gate 1 — the pinned closure signature.

If this `#guard_msgs` block fails, the audited specification surface changed:
a declaration entered or left it, or an audited declaration's meaning changed.
Re-read the new/changed declarations; if the change is intended, regenerate and
re-pin by copying the printed message here (and update `SPEC.md`). The content
hashes are structural (`Expr.hash`) and reproducible under the pinned
toolchain. -/

-- BEGIN SPEC CLOSURE PIN (generated by scripts/update-spec.sh — do not edit by hand)
/-- info:
SPEC CLOSURE — audited this-repo surface (86 decls)
  struct YulEvmCompiler.CallsRealized 64c9e18484d6ee24
  struct YulEvmCompiler.CreatesRealized c1cd779310c8070e
  struct YulEvmCompiler.EnvMatch 9cea97fa8ae94f99
  struct YulEvmCompiler.ExternalCodeMatch 2d46717e52ff1871
  struct YulEvmCompiler.ExternalModel 75bd1eadd7f209e2
  struct YulEvmCompiler.ExternalsRealized 7fd85ee803561fa8
  struct YulEvmCompiler.FrameOK 97dc148ae9bebed5
  relation YulEvmCompiler.HaltMatch 6557b5faae906a61
  relation YulEvmCompiler.HaltedMatch bd6cde934ed46ce6
  struct YulEvmCompiler.Instr b8989862a6923efc
  datadef YulEvmCompiler.Instr.bytes cb67215ba3c17cde
  datadef YulEvmCompiler.Instr.opByte 1063189e226fb3ef
  relation YulEvmCompiler.IsCallOp 93349e44f6cba900
  relation YulEvmCompiler.IsCreateOp 188d5668d6c00b2b
  relation YulEvmCompiler.LogEntryMatch 44220474a51dc6b6
  relation YulEvmCompiler.LogsMatch 6d1d2dd35bc25e39
  relation YulEvmCompiler.MemMatch e48211ef54b0d862
  relation YulEvmCompiler.RunResolvedObject 22471129a83f65e3
  relation YulEvmCompiler.SelfdestructEntryMatch 3b1f6c17c9cc3b3f
  relation YulEvmCompiler.SelfdestructsMatch 8fb6a9b19498848
  struct YulEvmCompiler.StateMatch 79c6c401a5fb18ee
  datadef YulEvmCompiler.assemble c1c9c0c9a1ad80c8
  datadef YulEvmCompiler.assembleBytes 29d8e692638cce98
  datadef YulEvmCompiler.assembleWithPayload 55ba5256c2c91c08
  artifact YulEvmCompiler.compile 49a8d9e93773bc82
  artifact YulEvmCompiler.compileObject 45cacb379f48e375
  statement YulEvmCompiler.compileObject_consistent 6772c506631c72d
  statement YulEvmCompiler.compileObject_correct 6c28d636cabfed71
  statement YulEvmCompiler.compile_correct ec51f1c553a52f8a
  statement YulEvmCompiler.compile_correct_eval 999e96fc09d553b6
  statement YulEvmCompiler.compile_correct_withPayload 50e2c3107c79f9ea
  statement YulEvmCompiler.compiled_constructor_returns 9a99d76f5d037853
  datadef YulEvmCompiler.conv 25e701af8a9ce7bb
  datadef YulEvmCompiler.mkCode edacb826e56f9571
  datadef YulEvmCompiler.natToBE d47a19daef761803
  datadef YulEvmCompiler.opTable e1b0c299397baebd
  datadef YulEvmCompiler.resolveForLayoutCases a635c809600d2d8a
  datadef YulEvmCompiler.resolveForLayoutExpr 15bc9ca915a17f5a
  datadef YulEvmCompiler.resolveForLayoutExprs deee862dd8d61de4
  datadef YulEvmCompiler.resolveForLayoutStmt ef48ed8902b73d01
  datadef YulEvmCompiler.resolveForLayoutStmts e61eedc003fbb530
  datadef YulEvmCompiler.resultOf 9a4fae748007bd7b
  struct YulParser.CTok f0018424d20ab2ce
  relation YulParser.Parser c3c38aa9630539e
  struct YulParser.QuotedScan fda150592f3cfc21
  datadef YulParser.afterBlockComment 5deac78dd9073c67
  datadef YulParser.canon b2d8eb356dc83a9c
  datadef YulParser.decDigitVal aa9b35f8e24246bf
  datadef YulParser.decDigits 93681863713f8772
  datadef YulParser.digitChar bcde7b79f84349d3
  datadef YulParser.evalDec 2589fcab0b0b1f30
  datadef YulParser.evalHex ac0c5eeed7026dc3
  datadef YulParser.hexDigitVal c4e40fb8db1bdaa8
  datadef YulParser.isDigitC 2e23993f4305ca29
  datadef YulParser.isHexDigitC 98897dc36c763b56
  datadef YulParser.isIdCont 99e813f13d1ba0b5
  datadef YulParser.isIdStart 88b65d8694f2e093
  datadef YulParser.isNumCont b0cd4e6da5b47fc
  datadef YulParser.isWs 1ad606963d724ee0
  datadef YulParser.numVal 36fa963744b7f765
  datadef YulParser.pQuotedChars 12116502d0932a55
  other YulParser.pQuotedChars_rest_lt bf5ffe92f6739f95
  artifact YulParser.parseBlock 548f44114c0c0376
  artifact YulParser.parseObject 7de98252fdadddab
  statement YulParser.parse_canon_block 565944a3acfe55d3
  statement YulParser.parse_canon_obj f40759b3ea852432
  datadef YulParser.printArgsC fb7f406415221f23
  datadef YulParser.printArgsTailC e3f69b37a503a89e
  datadef YulParser.printBlockC 95b7a427f26cf532
  datadef YulParser.printCS 3287ad224aefbc8d
  datadef YulParser.printCS1 2d9a080387cd904f
  datadef YulParser.printCasesC 625001fdca03af40
  datadef YulParser.printDataC a9434095c401bde
  datadef YulParser.printDatasC 8fbdb53b7d48df2b
  datadef YulParser.printExprC a56c648c2737a8d3
  datadef YulParser.printId ad633beed9cc9c7c
  datadef YulParser.printLitC b9cec7d002c6808a
  datadef YulParser.printManyC e5456a769d4dc16d
  datadef YulParser.printNameC b0caa18fdf398b08
  datadef YulParser.printObjC e2186fbe4e35780a
  datadef YulParser.printStmtC 3de2e9120bc6a272
  datadef YulParser.printStmtsC edd2b2fc3c962c96
  datadef YulParser.printStringC ae7fc4513c9611b4
  datadef YulParser.printSubsC 88f936b77e898d85
  datadef YulParser.quotedBody 5e9244808f044035
  datadef YulParser.scanQuoted ad86fca43b5d2cb6
external boundary: 151 decls, combined hash d1238cc2a8e2b0b8
-/
#guard_msgs in
open SpecClosure in
run_cmd do Lean.logInfo (signature (← getEnv))
-- END SPEC CLOSURE PIN
