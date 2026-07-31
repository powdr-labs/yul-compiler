# The SHA-256 EVMification challenge

**Write EVM bytecode that computes SHA-256, and prove it.**

[EIP-8200](https://eips.ethereum.org/EIPS/eip-8200) ("EVMification") proposes
retiring precompiles by deploying EVM bytecode at their addresses: after
activation, a call to the address runs ordinary bytecode at ordinary EVM gas
costs instead of a native implementation. The EIP's own security section asks
only that the bytecode "must be thoroughly tested and audited". This challenge
asks for the stronger thing: a **machine-checked proof** that a candidate
bytecode computes exactly what the precompile computed, so that "audited"
becomes "verified", and so that anyone can compete on gas without anyone
having to trust their code.

SHA-256 (`0x02`) is the pilot. It is not in EIP-8200's list (which covers
RIPEMD-160, MODEXP, and BLAKE2f) — it is the same problem in its simplest
form, it is the one the [eth-act/evmification](https://github.com/eth-act/evmification/tree/main/src/sha256)
prototypes start from, and, decisively, our pinned EVM semantics already
contains a SHA-256 model that the `0x02` precompile itself executes. That
makes the specification side of the equivalence *not ours to get wrong*.

---

## 1. What "equivalent" means here

The chain of trust, top to bottom:

```text
FIPS 180-4                                      published standard
    │  human review + §B.1–B.3 published vectors (evm-semantics tests/Sha256Test.lean)
    ▼
EvmSemantics.Crypto.Sha256.hash : ByteArray → ByteArray     ← the canonical spec
    │  Precompile.runSha256 input _ = .success (Crypto.Sha256.hash input) cost
    ▼
what a call to 0x02 does today, in the pinned semantics
```

`Crypto.Sha256.hash` lives in [evm-semantics](https://github.com/powdr-labs/evm-semantics),
pinned by commit in `lakefile.toml`, and is *literally* the function the
precompile dispatch calls. So a proof that a candidate bytecode returns
`Crypto.Sha256.hash calldata` is a proof of equivalence **to the precompile as
modeled by the reference EVM semantics** — we do not introduce a second
SHA-256 of our own and hope the two agree.

The challenge statement is one `Prop`, in
[`Sha256/Statement.lean`](Sha256/Statement.lean):

```lean
def Correct (code : ByteArray) : Prop :=
  ∀ calldata : ByteArray, ∃ g₀ : Nat, ∀ g : Nat, g₀ ≤ g →
    Eval (frame code calldata g) (.returned (spec calldata))
```

Read it as: *for any message, given enough gas, a frame running `code` halts
by returning exactly the 32 digest bytes.* Points worth noticing:

* **It never mentions our implementation.** Not our Yul, not our bytecode, not
  our memory layout, not our gas. Two submissions that both satisfy `Correct`
  are interchangeable at the interface a caller can observe. That is why the
  spec is a *function*, not the incumbent's code: bytecode-to-bytecode
  equivalence would leak one implementation's accidents into the standard.
* **Gas appears, because it must.** Below some level every implementation runs
  out of gas, and no single constant works for all message lengths. The
  `∃ g₀, ∀ g ≥ g₀` shape ("given enough gas") is honest and non-vacuous: the
  conclusion must hold at *every* larger budget, so no candidate passes by
  succeeding at one lucky gas value.
* **`Returned`, not `Success`.** A candidate that reverts, throws, or returns
  the wrong number of bytes fails the statement.

The efficiency-carrying strengthening is

```lean
def CorrectWithSchedule (code : ByteArray) (schedule : Nat → Nat) : Prop :=
  ∀ (calldata : ByteArray) (g : Nat), schedule calldata.size ≤ g →
    Eval (frame code calldata g) (.returned (spec calldata))
```

— a *proven* gas bound as a function of input size, which is what an EIP
needs in order to publish a gas schedule. `correct_of_schedule` shows it
implies `Correct`.

### Scope, stated up front

* `frame` is the canonical precompile-call frame: fresh memory, empty storage
  and transient storage, zero balance, zero call value, depth 0, Osaka. That
  is the situation that actually arises for a call into a freshly deployed,
  storage-free account — but a candidate that reads `SLOAD`/`CALLVALUE`/
  `CALLER` is only pinned at those values. `CorrectInAnyFrame` states the
  frame-generalized version; closing the gap is **Obligation W** below. The
  Tier-1 scorer already runs every vector a second time in a *dirty* frame
  (seeded storage, transient storage, nonzero call value) to catch this
  empirically.
* The candidate is deployed at a non-precompile address, not at `0x02`. In the
  pinned Osaka semantics `0x02` *is* a precompile, so a frame there never
  executes bytecode at all — flipping exactly that bit is what EIP-8200
  activation does. When the semantics grows a post-8200 fork, `deployAddress`
  becomes `0x02` and nothing else changes.

---

## 2. How the reference submission gets there

The reference implementation is
[`Sha256/reference.yul`](Sha256/reference.yul): SHA-256 in the verified Yul
fragment, message from calldata, digest in returndata, 1524 bytes of compiled
bytecode. It is written **for provability, not for gas** — the hash state and
message schedule live in memory so that every loop body is a short memory
transformer with at most a handful of live variables.

Because the compiler between Yul and bytecode is verified, the reference's
proof obligation is a statement about *Yul*, and the bytecode level is
discharged by a theorem that already exists:

```text
ComputesDigest referenceBlock            ← Obligation Y (the real work)
  ∘ compile_correct_eval                   ✔ proved in this repo
  ∘ optimizer / normalizer soundness       ✔ proved in this repo (needs composing: Obligation C)
  ∘ parse_canon_block                      ✔ proved in this repo
  ∘ StateMatch for the canonical frame       Obligation A (plumbing)
  ⟹ Correct referenceBytecode
```

[`Sha256/Reduction.lean`](Sha256/Reduction.lean) proves the reduction —
`correct_of_computesDigest` — today, `sorry`-free, with the same axiom
footprint as the rest of the repository (`propext`, `Classical.choice`,
`Quot.sound`). Its two hypotheses are ordinary `Prop`s; the challenge is to
inhabit them, and no step of the reduction mentions an opcode.
[`Sha256/Reference.lean`](Sha256/Reference.lean) instantiates it for the
shipped artifact (`reference_correct`).

### The open obligations

| # | Name | What it says | Size |
|---|------|--------------|------|
| **Y** | `ComputesDigest` | The Yul program returns `Crypto.Sha256.hash calldata`. | large; decomposed below |
| **A** | `AbstractsFrame` | Each canonical EVM frame is matched by a yul-semantics state with the same calldata and empty memory. | plumbing, ~a day |
| **C** | `PipelineComposes` | `compileSource` = parse ∘ desugar ∘ normalize ∘ optimize ∘ compile, composed into one theorem. Each piece is already sound. | mechanical; wanted repo-wide as `compileSource_correct` |
| **S** | *(optional)* | A declarative, list-based SHA-256 in Lean plus `spec_eq_hash`, so proofs need not fight `Id.run do` loops over `ByteArray`. | small, unblocks Y |
| **W** | `CorrectInAnyFrame` | Generalize from the canonical frame to any fresh frame (arbitrary world/caller/value). Noninterference for a program that executes no state-reading op. | medium |
| **G** | `CorrectWithSchedule` | A proven gas schedule (Tier 3). | medium |

**Obligation Y decomposes** along the structure of `reference.yul`; each part
is independently provable and independently useful:

| | Lemma | Statement |
|---|---|---|
| Y1 | round functions | `rotr`, `ssig0/1`, `bsig0/1`, `ch`, `maj` implement their FIPS 32-bit counterparts, for any 32-bit argument. Pure, no memory: the easiest starting point. |
| Y2 | `initK` | after `initK()`, `kAt j = K[j]` for `j < 64` — one packed-word read lemma, 8 times. |
| Y3 | `pad` | after `pad()`, memory at `0xb20 ..+paddedLen` is the FIPS-padded message and `paddedLen = 64·⌈(n+9)/64⌉`. The padding-boundary case analysis lives here. |
| Y4 | `schedule` | after `schedule(off)`, `W[j]` is the FIPS message schedule of the block at `off`. |
| Y5 | `compress` | one call maps `H` to `compressBlock H block`. |
| Y6 | block loop | the loop folds `compress` over the blocks, giving `H^(N)`. |
| Y7 | output | the final word is the eight state words big-endian, and `return(0, 32)` exposes them. |
| Y8 | framing | the memory regions (`K`, `H`, `H_prev`, `W`, message) are disjoint, and each helper touches only its own. Feeds every lemma above. |

Y1–Y2 are leaf lemmas that can start immediately; Y8 is the framework the
rest lean on. The [Aristotle](https://github.com/powdr-labs/yul-compiler#readme)
workflow used elsewhere in this repo applies directly: each row is a
self-contained Lean goal.

---

## 3. Submitting

### Tier 1 — falsification by execution (required, automatic)

```sh
lake exe sha256challenge --hex=my_impl.hex     # raw bytecode
lake exe sha256challenge --yul=my_impl.yul     # Yul, compiled by yulc
lake exe sha256challenge                        # the reference
```

The scorer runs your candidate in the *pinned executable EVM semantics* over
19 vectors — FIPS 180-4 §B.1/§B.2, the empty message, and every padding
boundary (55, 56, 63, 64, 65, 119, 120, 127, 128, 256, 1000 bytes) — each in
a clean frame and again in a dirty one, comparing returndata with
`Crypto.Sha256.hash` and reporting gas. Passing is **necessary and not
sufficient**: it is falsification, not proof.

The scorer takes ~5 s, so it belongs in CI as the gate that keeps the
reference honest. `.github/workflows/` is a human-approval-only trust boundary
in this repository, so the step is *proposed*, not added — a maintainer can
drop this after the `YulIR round-trip` step:

```yaml
      - name: SHA-256 challenge (reference implementation, Tier 1)
        run: |
          f=ci-summary/sha256-challenge.txt; : > "$f"
          lake build sha256challenge
          if lake exe sha256challenge | tee /tmp/sha256-challenge.txt; then
            echo "sha256_reference=pass" >> "$f"
            grep '^total gas' /tmp/sha256-challenge.txt >> "$f" || true
          else
            echo "::error::the SHA-256 reference implementation no longer matches the spec"
            echo "sha256_reference=fail" >> "$f"; exit 1
          fi
```

and add `Challenge` to the directory list in the `sorry` scan of the
"Verify soundness" step.

### Tier 2 — proved correct

A Lean proof of `Challenge.Sha256.Correct yourBytecode`, on the pinned
toolchain, with no `sorry`, no new `axiom`, no `native_decide`, and the same
axiom footprint the repository already checks (`Checks.lean`). Three routes,
easiest first:

* **Route Y (Yul).** Submit Yul in the verified fragment; `yulc` gives you
  bytecode and `correct_of_computesDigest` gives you `Correct` from a
  Yul-level proof. Cheaper still: prove your Yul *equivalent to the
  reference* — `YulSemantics.EquivBlock` is exactly this relation — and
  inherit the reference's obligation instead of redoing it.
* **Route O (a new optimizer pass).** If your improvement is a general
  transformation rather than a hand-written program, land it as a verified
  Yul→Yul pass (`Optimizer.Sound`, see `YulEvmCompiler/Optimizer/`). Then
  every program the compiler compiles gets faster, not just this one — the
  most valuable kind of submission.
* **Route B (raw bytecode).** Prove directly over `EvmSemantics.EVM.Step`.
  This needs infrastructure we do not have yet: a verified disassembler with
  a round-trip theorem (`assemble ∘ disassemble = id`) so that reasoning can
  happen at the byte-free `Asm` layer, plus a symbolic-execution/Hoare kit
  for loops. Contributions to *that* are as welcome as a submission.

### Tier 3 — proved fast

`CorrectWithSchedule yourBytecode schedule` with a concrete `schedule`. This
is the tier an EIP could actually cite, since it yields a gas formula rather
than a measurement.

### Ranking

Leaderboard rows are `(verified tier, measured gas, bytecode size)`, gas
measured by the scorer on the fixed vector set. A Tier-2 submission always
outranks a faster Tier-1 one: the point of the exercise is bytecode you do
not have to trust.

---

## 4. Where the reference stands

Measured by `lake exe sha256challenge` (gas in the pinned semantics, Osaka):

| input | gas | blocks |
|---|---|---|
| empty | 158,035 | 1 |
| `abc` | 158,038 | 1 |
| 55 bytes | 158,041 | 1 |
| 56 bytes | 314,044 | 2 |
| 64 bytes | 314,044 | 2 |
| 1000 bytes | 2,498,174 | 16 |

That is ≈156,000 gas per 64-byte block, against the precompile's schedule of
`60 + 12·⌈len/32⌉` (84 gas for a 64-byte message). The gap is the whole
point: the reference trades roughly three orders of magnitude of gas for a
proof structure a person can finish, and a hand-optimized implementation
should be able to take one to two of those orders back. **That headroom is
the challenge.**

---

## 5. Roadmap

* **Stage 0 — done, this branch.** Reference Yul compiling through the
  verified compiler; the Tier-1 scorer; the challenge statement; the
  reduction theorem; the obligations named.
* **Stage 1.** Obligations A and C — after which `Correct referenceBytecode`
  rests on the Yul-level obligation *alone*.
* **Stage 2.** Obligation S, then Y1/Y2/Y8: the leaf lemmas and the memory
  framing framework.
* **Stage 3.** Y3–Y7: padding, schedule, compression, block loop, output.
  Reference is Tier 2.
* **Stage 4.** Obligation W (any frame) and G (gas schedule). Route B
  infrastructure: disassembler + round-trip theorem, so raw-bytecode
  submissions become possible.
* **Stage 5.** Open the leaderboard. Then repeat for the precompiles
  EIP-8200 actually names — RIPEMD-160 is the same shape, MODEXP and BLAKE2f
  are where it gets interesting.

## Files

| path | what |
|---|---|
| `Challenge/Sha256/reference.yul` | the reference implementation |
| `Challenge/Sha256/Statement.lean` | `Correct`, `CorrectWithSchedule`, the frame, frame facts |
| `Challenge/Sha256/Reduction.lean` | `correct_of_computesDigest`: Yul obligation ⟹ challenge statement |
| `Challenge/Sha256/Reference.lean` | the artifact, its obligations, `reference_correct` |
| `scripts/Sha256Challenge.lean` | the Tier-1 scorer (`lake exe sha256challenge`) |
