import Challenge.Sha256.Statement
import Challenge.Sha256.Reduction
import Challenge.Sha256.Reference
set_option warningAsError true
/-!
# `Challenge` — verified replacements for precompiles

The EIP-8200 / EIP-7666 "EVMification" challenge: replace a precompile with
EVM bytecode and *prove* the bytecode computes what the precompile computed.

* `Challenge.Sha256.Statement` — the challenge statement every submission
  must satisfy, and the frame it is judged in.
* `Challenge.Sha256.Reduction` — the reduction that discharges it for
  bytecode this repository's verified compiler produced, leaving a
  Yul-level obligation as the only open goal.
* `Challenge.Sha256.Reference` — the reference submission (`reference.yul`)
  and its end-to-end theorem modulo the three named obligations.

`Challenge/README.md` is the challenge document: the tiers, the open
obligations, and how to submit. `Challenge/Sha256/reference.yul` is the
reference implementation; `lake exe sha256challenge` scores candidates.
-/
