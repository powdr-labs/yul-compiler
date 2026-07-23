import YulSemantics.Dialect.EVM
/-!
# Redundant-store elimination — M0 semantics probes

Machine-checked pins of the pinned `yul-semantics` EVM-dialect facts the verified
redundant-store pass will rely on. If an upstream semantics bump breaks one of
these, the design assumption it encodes must be revisited *before* the proof.

See `YulEvmCompiler/Optimizer/RedundantStores.md` (§ "M0 — semantics findings").
-/

namespace YulEvmCompiler.Optimizer.RedundantStore.M0

open YulSemantics YulSemantics.EVM

variable (st st0 : EvmState) (k v v₁ v₂ p : U256)

/-! ### Static-context write protection (the DSE linchpin) -/

/-- **P1.** In a static frame, `sstore` halts with `.staticViolation` and makes
**no** storage change. So deleting a store is only sound if the transformed
program reaches an identical static-violation (or the frame is provably
non-static). -/
theorem sstore_static (h : st.env.static = true) :
    stepOp .sstore [k, v] st = some (.halt { st with halted := some (.staticViolation, []) }) := by
  simp [stepOp, guardStatic, h]

/-- The static-violation result changes nothing but the halt marker. -/
theorem sstore_static_storage (h : st.env.static = true) :
    (BuiltinResult.state <$> stepOp .sstore [k, v] st).map (·.storage) = some st.storage := by
  simp [stepOp, guardStatic, h, BuiltinResult.state]

/-- **P2.** In a non-static frame, `sstore` succeeds (never halts) and writes the
value into the storage map — the foundation of forwarding and dead-store removal. -/
theorem sstore_nonstatic_ok (h : st.env.static = false) :
    (stepOp .sstore [k, v] st).map (·.isHalt) = some false := by
  simp [stepOp, guardStatic, h, BuiltinResult.isHalt]

theorem sstore_nonstatic_storage (h : st.env.static = false) :
    (stepOp .sstore [k, v] st).map (·.state.storage) = some (upd st.storage k v) := by
  simp [stepOp, guardStatic, h, BuiltinResult.state]

/-- **P3.** `.staticViolation` is non-committing: the frame rolls back to `st0`,
carrying only the halt marker and return data. Combined with P1 this is why a
covering static-violation makes deleting a leading dead store observationally
safe (both roll back to `st0`). -/
theorem staticViolation_rolls_back {d} (h : st.halted = some (.staticViolation, d)) :
    committedState st0 st = { st0 with halted := st.halted, returndata := st.returndata } :=
  committedState_rollback h rfl

/-! ### Word-map algebra: the store rewrites, at the state level -/

/-- **P4 (absorb).** Overwriting a slot discards the earlier write — redundant /
dead store elimination for a must-alias pair. -/
theorem upd_absorb (f : U256 → U256) : upd (upd f k v₁) k v₂ = upd f k v₂ := by
  funext x; simp only [upd]; split <;> rfl

/-- **P5 (commute).** Writes to provably-distinct slots commute — lets the scan
step a dead store past a disjoint store (`mustNotAliasWord`). -/
theorem upd_comm (f : U256 → U256) (hk : k ≠ p) :
    upd (upd f k v₁) p v₂ = upd (upd f p v₂) k v₁ := by
  funext x; simp only [upd]; split <;> split <;> first | rfl | (subst_vars; exact absurd rfl hk)

/-! ### Loads and the region distinction -/

/-- **P6.** `sload` returns the current map value and does not change state — the
forwarding target (`sload k ↦ v` needs `st.storage k = eval v`). -/
theorem sload_reads : stepOp .sload [k] st = some (.ok [st.storage k] st) := by
  simp [stepOp]

/-- **P7.** `mstore` is **not** guarded by static context: memory writes succeed
in a static frame. So the memory region has no static-violation barrier — but
`msize`/`touchMemory` observe every write, so removing an `mstore` is only sound
when the write's extent is provably unobserved (a separate obligation). -/
theorem mstore_permitted_in_static :
    stepOp .mstore [p, v] st = some (.ok []
      { touchMemory st p.toNat 32 with memory := storeWord st.memory p.toNat v }) := by
  simp [stepOp]

/-- The memory write leaves storage untouched (it only touches memory + `msize`). -/
theorem mstore_preserves_storage :
    (touchMemory st p.toNat 32).storage = st.storage := by simp [touchMemory]

end YulEvmCompiler.Optimizer.RedundantStore.M0
