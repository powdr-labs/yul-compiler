import YulEvmCompiler.Compile
import YulSemantics.ObjectRun

/-!
# YulEvmCompiler.ObjectCompile

The **object layer**: assembling a Yul `Object` into a deployed-bytecode
`Layout` (the artifact `YulSemantics.ObjectRun` is parameterized over), and
the key correctness content — that the produced layout is **consistent** with
the object, i.e. every `data` segment is faithfully placed in the deployed
bytecode at the recorded offset with the recorded size.

`compileObject` compiles the object's `code` block with the ordinary
pipeline (`compileProgram`/`lowerProg`/`assembleBytes`) and appends the data
segments after it, keying the `dataOffset`/`dataSize` maps by each name's
string-literal encoding `litValue (.string name)` exactly as the built-ins
`dataoffset`/`datasize` read them. It rejects objects whose data-segment keys
collide (so the maps are well-defined per segment) or whose deployed size does
not fit a word.

`compileObject_consistent` discharges `Layout.Consistent`, which — composed
with the semantics' already-proven `constructorCode_returns_of_consistent` —
gives an end-to-end statement: under the compiler's layout, the canonical
constructor for any data segment returns exactly that segment's bytes
(`compiled_constructor_returns`).

**Deferred (documented):** resolving `dataoffset`/`datasize` to push-constants
*inside* the compiled code and simulating `RunObject` at the bytecode level
(that needs `compile_correct` generalized to a trailing code suffix); and
laying out nested sub-objects' bytecode (their offsets/sizes are
layout-abstract and unconstrained by `Consistent`).
-/

namespace YulEvmCompiler

open YulSemantics (Object Data Ident)
open YulSemantics.EVM (Op litValue U256 Layout byteFrom readBytes)

/-- The concatenated bytes of a data-segment list, in order. -/
def dataRegion (segs : List (String × Data)) : List UInt8 :=
  segs.flatMap (fun p => p.2.bytes)

/-- Build the `dataOffset`/`dataSize` maps for a data-segment list whose bytes
start at absolute offset `base` in the deployed code. Each name resolves
(under its string-literal key) to its offset and size; earlier segments shadow
later ones, which is why `compileObject` requires the keys to be distinct. -/
def buildMaps (base : Nat) : List (String × Data) → (U256 → U256) × (U256 → U256)
  | [] => (fun _ => 0, fun _ => 0)
  | (nm, d) :: rest =>
      let (offR, szR) := buildMaps (base + d.size) rest
      let key := litValue (.string nm)
      (fun k => if k = key then BitVec.ofNat 256 base else offR k,
       fun k => if k = key then BitVec.ofNat 256 d.size else szR k)

/-- Assemble an object into a deployed-bytecode layout: its compiled `code`
followed by its data segments, with offset/size maps keyed by
`litValue (.string name)`. Rejected when the code does not compile, the
segment keys collide, or the deployed bytecode would not fit a word. -/
def compileObject (o : Object Op) : Option Layout := do
  let asm ← compileProgram o.codeBlock
  let is ← lowerProg asm
  let codeBytes := assembleBytes is
  let code := codeBytes ++ dataRegion o.dataSegs
  if (o.dataSegs.map (fun p => litValue (.string p.1))).Nodup ∧ code.length < 2 ^ 256 then
    let (offMap, szMap) := buildMaps codeBytes.length o.dataSegs
    some { code := code, dataOffset := offMap, dataSize := szMap }
  else
    none

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

/-- `buildMaps` records each segment's size (under its key), given distinct
keys. -/
theorem buildMaps_size : ∀ (segs : List (String × Data)) (base : Nat),
    (segs.map (fun p => litValue (.string p.1))).Nodup →
    ∀ p ∈ segs,
      (buildMaps base segs).2 (litValue (.string p.1)) = BitVec.ofNat 256 p.2.size := by
  intro segs
  induction segs with
  | nil => intro base _ p hp; simp at hp
  | cons hd rest ih =>
    intro base hnodup p hp
    obtain ⟨nm, d⟩ := hd
    simp only [List.map_cons, List.nodup_cons] at hnodup
    rcases List.mem_cons.mp hp with hp | hp
    · subst hp
      simp [buildMaps]
    · have hne : litValue (.string p.1) ≠ litValue (.string nm) := by
        intro h
        exact hnodup.1 (h ▸ List.mem_map_of_mem hp)
      simp only [buildMaps, if_neg hne]
      exact ih (base + d.size) hnodup.2 p hp

/-- `buildMaps` records each segment's offset (under its key), and the deployed
code carries the segment's bytes there — the placement half of consistency. -/
theorem buildMaps_offset : ∀ (segs : List (String × Data)) (pre : List UInt8),
    (segs.map (fun p => litValue (.string p.1))).Nodup →
    pre.length + (dataRegion segs).length < 2 ^ 256 →
    ∀ p ∈ segs,
      readBytes (byteFrom (pre ++ dataRegion segs))
        ((buildMaps pre.length segs).1 (litValue (.string p.1))).toNat p.2.size = p.2.bytes := by
  intro segs
  induction segs with
  | nil => intro pre _ _ p hp; simp at hp
  | cons hd rest ih =>
    intro pre hnodup hlt p hp
    obtain ⟨nm, d⟩ := hd
    simp only [List.map_cons, List.nodup_cons] at hnodup
    have hregion : dataRegion ((nm, d) :: rest) = d.bytes ++ dataRegion rest := by
      simp [dataRegion]
    have hlen_lt : pre.length < 2 ^ 256 := by
      rw [hregion] at hlt; simp only [List.length_append] at hlt; omega
    rcases List.mem_cons.mp hp with hp | hp
    · subst hp
      have hoff : (buildMaps pre.length ((nm, d) :: rest)).1 (litValue (.string nm))
          = BitVec.ofNat 256 pre.length := by simp [buildMaps]
      rw [hoff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen_lt, hregion, ← List.append_assoc]
      exact readBytes_middle pre d.bytes (dataRegion rest)
    · have hne : litValue (.string p.1) ≠ litValue (.string nm) := by
        intro h
        exact hnodup.1 (h ▸ List.mem_map_of_mem hp)
      simp only [buildMaps, if_neg hne]
      have hih := ih (pre ++ d.bytes) hnodup.2 (by
        rw [hregion] at hlt
        simp only [List.length_append] at hlt ⊢
        omega) p hp
      rw [hregion]
      simpa [List.append_assoc, List.length_append, YulSemantics.Data.size] using hih

/-- **Main theorem**: the layout `compileObject` produces is consistent with
the object — every data segment sits at its recorded offset in the deployed
bytecode with its recorded size. -/
theorem compileObject_consistent {o : Object Op} {L : Layout}
    (h : compileObject o = some L) : L.Consistent o := by
  simp only [compileObject, Option.bind_eq_bind] at h
  obtain ⟨asm, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨is, -, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · rename_i hcond
    simp only [Option.some.injEq] at h
    subst h
    intro p hp
    obtain ⟨hnodup, hsmall⟩ := hcond
    refine ⟨buildMaps_size o.dataSegs _ hnodup p hp, ?_⟩
    have hlt : (assembleBytes is).length + (dataRegion o.dataSegs).length < 2 ^ 256 := by
      simpa [List.length_append] using hsmall
    exact buildMaps_offset o.dataSegs _ hnodup hlt p hp
  · simp at h

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

/-- Compilation succeeds and lays the data segment into the deployed bytecode. -/
example : (compileObject demoObject).map (·.code) = some [0xde, 0xad, 0xbe, 0xef] := by
  native_decide

/-- The produced layout is consistent with the object (`compileObject_consistent`
in action on a concrete instance). -/
example (L : Layout) (h : compileObject demoObject = some L) : L.Consistent demoObject :=
  compileObject_consistent h

end YulEvmCompiler
