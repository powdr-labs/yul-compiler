import Challenge.Sha256.Reduction
import YulParser.Compile
set_option warningAsError true
/-!
# The reference submission

`reference.yul` is the challenge's reference implementation: SHA-256 in the
verified Yul fragment, reading the message from calldata and returning the
32-byte digest. It is the incumbent on the leaderboard — deliberately written
for provability rather than gas, so beating it is easy and *proving* you beat
it is the challenge.

The artifact chain has no unverified step of its own:

```text
reference.yul  --parseSource-->  referenceBlock  --compileSource-->  bytecode
               (parse_canon_block:                (compile_correct_eval:
                the AST prints back                the bytecode simulates
                to this source)                    the Yul run)
```

so a reader who audits `reference.yul` has audited the artifact — the two
arrows are theorems, not trust. What is *not* yet a theorem is that the Yul
program computes SHA-256 (`ComputesDigest`); that is the open obligation,
and everything in this file exists to state precisely how it lands on
`Correct`.

Run `lake exe sha256challenge` for the executable check (every FIPS and
padding-boundary vector, against `EvmSemantics.Crypto.Sha256.hash`).
-/

namespace Challenge.Sha256

open EvmSemantics
open YulSemantics (Block)
open YulSemantics.EVM (Op)
open YulEvmCompiler

/-- The reference implementation, verbatim. -/
def referenceSource : String := include_str "reference.yul"

/-- The reference AST: what the verified parser makes of `referenceSource`.
By `YulParser.parse_canon_block` this AST prints back to the source it came
from, so auditing the `.yul` text audits this. -/
def referenceBlock? : Option (Block Op) :=
  match YulParser.parseSource referenceSource with
  | some (.block statements) => some statements
  | _ => none

/-- The reference bytecode: what `yulc` emits for `referenceSource`. -/
def referenceBytecode? : Option ByteArray :=
  YulParser.compileSource referenceSource

/-- **Obligation Y, for the reference.** The reference Yul program computes
the digest of its calldata. -/
def ReferenceComputesDigest : Prop :=
  ∀ block, referenceBlock? = some block → ComputesDigest block

/-- **Obligation A**, uniformly in the code: the canonical EVM frame is
matched by a yul-semantics state. Pure plumbing (build the source state from
the target one); independent of SHA-256 and reusable by every future
challenge. -/
def FramesAbstracted : Prop := ∀ code : ByteArray, AbstractsFrame code

/-- **Obligation C.** `compileSource` is `parse`, then desugaring and
normalization, then the verified Yul→Yul optimizer pipeline, then `compile` —
each step already sound in isolation, but not yet composed into one theorem
about `compileSource`. This says exactly what the composition must give: the
shipped bytecode is `assemble` of an accepted program that still computes the
digest whenever the parsed source does.

Discharging it is mechanical, benefits every user of the compiler (a
`compileSource_correct` capstone), and is the natural next PR. -/
def PipelineComposes : Prop :=
  ∀ code : ByteArray, referenceBytecode? = some code →
    ∃ (prog : Block Op) (is : List Instr),
      compile prog = some is ∧ assemble is = code ∧
      (ReferenceComputesDigest → ComputesDigest prog)

/-- **The reference's end-to-end theorem, modulo its three obligations.**
The shipped bytecode satisfies the challenge statement.

`hsize` is the code-size side condition of `FrameOK`; it holds for any real
artifact (the reference is ~1.5 KB) and is a hypothesis only because
`ByteArray.size` has no a-priori bound. -/
theorem reference_correct
    (hpipeline : PipelineComposes)
    (habs : FramesAbstracted)
    (hyul : ReferenceComputesDigest)
    {code : ByteArray} (hcode : referenceBytecode? = some code)
    (hsize : code.size < 2 ^ 256) :
    Correct code := by
  obtain ⟨prog, is, hcomp, hassemble, himp⟩ := hpipeline code hcode
  subst hassemble
  exact correct_of_computesDigest hcomp hsize (habs _) (himp hyul)

end Challenge.Sha256
