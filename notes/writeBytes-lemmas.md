# Upstream lemmas needed for verified `mstore`

To make the non-storage-based Fibonacci example (`YulSemantics.FibExample.fibContract`)
compile to *verified* bytecode, the compiler needs to prove that an EVM `MSTORE`
preserves the memory-match relation. That reduces to a read-after-write fact about
`MachineState.writeBytes`, which currently has **no** supporting lemmas in
evm-semantics.

## Where it goes

`EvmSemantics/Machine/MachineState.lean` (evm-semantics), in the `MachineState`
namespace, next to the `writeBytes` definition.

## The definition being reasoned about

```lean
-- EvmSemantics/Machine/MachineState.lean
def writeBytes (bs bytes : ByteArray) (start : Nat) : ByteArray :=
  if bytes.size = 0 then bs else
  let needed := start + bytes.size
  let padded :=
    if bs.size < needed then bs ++ ByteArray.mk (Array.replicate (needed - bs.size) 0) else bs
  Id.run do
    let mut acc := padded
    for i in [0:bytes.size] do
      acc := acc.set! (start + i) bytes[i]!
    return acc
```

It is a total `def` (kernel-transparent), so these lemmas are provable.

## Lemma 1 — read-after-write (the one the compiler consumes directly)

Stated with `[a]?.getD 0` so it folds in the zero-padding on both the growth side
(`start + bytes.size > bs.size`) and the out-of-range side. This matches the
compiler's `MemMatch ymem m ↔ ∀ a, ymem a = m[a]?.getD 0` shape.

```lean
namespace MachineState

/-- Read-after-write for `writeBytes`, as a zero-padded pointwise read.
The byte at index `a` is the written byte when `a` lands in the write
window `[start, start + bytes.size)`, and otherwise the original byte;
the `[a]?.getD 0` framing absorbs the zero padding on both the growth
side (`start + bytes.size > bs.size`) and the out-of-range side. -/
theorem writeBytes_getElem?_getD (bs bytes : ByteArray) (start a : Nat) :
    (writeBytes bs bytes start)[a]?.getD 0
      = if start ≤ a ∧ a < start + bytes.size then bytes[a - start]?.getD 0
        else bs[a]?.getD 0 := by
  sorry

end MachineState
```

Correctness of the statement across edge cases:
- `bytes.size = 0`: window empty ⇒ both branches read `bs[a]?.getD 0`. ✓
- padding gap `bs.size ≤ a < start`: out-of-window ⇒ `bs[a]?.getD 0 = 0`, matching
  the zero-fill. ✓
- in-window `a` past the old `bs.size`: `some` (the array was grown). ✓

## Lemma 2 — size (companion; useful, pairs naturally with per-region reads)

```lean
namespace MachineState

/-- `writeBytes` grows the array to cover the write window (and never shrinks). -/
theorem writeBytes_size (bs bytes : ByteArray) (start : Nat) :
    (writeBytes bs bytes start).size
      = if bytes.size = 0 then bs.size else max bs.size (start + bytes.size) := by
  sorry

end MachineState
```

## Proof sketch

Both are about the `Id.run do … acc.set! (start + i) bytes[i]! …` loop:
induct over the range `[0:bytes.size]`; `ByteArray.set!` preserves `.size` and sets
exactly its one index, leaving all others unchanged. The initial `padded` array has
size `max bs.size (start + bytes.size)` when `bytes.size ≠ 0`.

## Not in MachineState (companion, for reference)

Finishing `mstore` in the compiler also needs to index the encoder that MSTORE writes,
`Data.Bytes.natToBytesPadded` (in `EvmSemantics/Data/Bytes.lean`), e.g.

```lean
-- EvmSemantics/Data/Bytes.lean
theorem natToBytesPadded_getElem?_getD (n width k : Nat) (h : k < width) :
    (natToBytesPadded n width)[k]?.getD 0
      = UInt8.ofNat (n / 256 ^ (width - 1 - k) % 256) := by
  sorry
```

This one lives in `Data/Bytes.lean`, not `MachineState`. With Lemma 1 plus this
encoder lemma, the `storeWord`(Yul) ↔ `writeBytes`(EVM) agreement — and hence a
verified `MSTORE` — closes inside the compiler repo, with no further upstream
changes.
