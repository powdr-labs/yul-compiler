import YulEvmCompiler.Optimizer.Spec.Observe
set_option warningAsError true
/-!
# Memory-guard contract for observational optimizations

Solidity's `memoryguard(size)` lets an optimizer choose a returned pointer
`ptr`: the source promises to access memory only in `[0, size)` or
`[ptr, ∞)`, while the optimizer owns `[size, ptr)`.  This module states the
representation relation and the dynamic footprint/oracle premises needed to
use that promise honestly.

The relation deliberately ignores `activeWords` and bytes in the reserved
interval, but keeps every caller/transaction observable equal.  It is not an
unconditional weakening of `ObsPass`: source operations still have to satisfy
`OpMemorySafe`, and open-world call/create relations must be insensitive to the
reserved bytes.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM

/-! ## Compiler-chosen guard resolution

The pinned core dialect intentionally has no `memoryguard` operation.  Raw
object Yul carries it as a parser-level pseudo-call; a guarded compiler chooses
the returned pointer and resolves the call to a literal before invoking the
core semantics.  This avoids the false claim that raising the pointer is
equivalent to the identity interpretation.
-/

def resolveMemoryGuardExpr (base reserved : Nat) : Expr Op → Expr Op
  | .call "memoryguard" [.lit (.number k)] =>
      if k = base then .lit (.number reserved)
      else .call "memoryguard" [.lit (.number k)]
  | .call f args => .call f (args.map (resolveMemoryGuardExpr base reserved))
  | .builtin op args => .builtin op (args.map (resolveMemoryGuardExpr base reserved))
  | e => e

mutual
  def resolveMemoryGuardStmt (base reserved : Nat) : Stmt Op → Stmt Op
    | .block body => .block (resolveMemoryGuardStmts base reserved body)
    | .funDef f ps rs body =>
        .funDef f ps rs (resolveMemoryGuardStmts base reserved body)
    | .letDecl xs val =>
        .letDecl xs (val.map (resolveMemoryGuardExpr base reserved))
    | .assign xs e => .assign xs (resolveMemoryGuardExpr base reserved e)
    | .cond c body =>
        .cond (resolveMemoryGuardExpr base reserved c)
          (resolveMemoryGuardStmts base reserved body)
    | .switch c cases dflt =>
        .switch (resolveMemoryGuardExpr base reserved c)
          (resolveMemoryGuardCases base reserved cases)
          (match dflt with
          | some body => some (resolveMemoryGuardStmts base reserved body)
          | none => none)
    | .forLoop init c post body =>
        .forLoop (resolveMemoryGuardStmts base reserved init)
          (resolveMemoryGuardExpr base reserved c)
          (resolveMemoryGuardStmts base reserved post)
          (resolveMemoryGuardStmts base reserved body)
    | .exprStmt e => .exprStmt (resolveMemoryGuardExpr base reserved e)
    | .break => .break
    | .continue => .continue
    | .leave => .leave
    termination_by s => 2 * sizeOf s

  def resolveMemoryGuardStmts (base reserved : Nat) : Block Op → Block Op
    | [] => []
    | s :: rest =>
        resolveMemoryGuardStmt base reserved s :: resolveMemoryGuardStmts base reserved rest
    termination_by ss => 2 * sizeOf ss + 1

  def resolveMemoryGuardCases (base reserved : Nat) :
      List (Literal × Block Op) → List (Literal × Block Op)
    | [] => []
    | (l, body) :: rest =>
        (l, resolveMemoryGuardStmts base reserved body) ::
          resolveMemoryGuardCases base reserved rest
    termination_by cases => 2 * sizeOf cases + 1
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

/-- A half-open memory range `[p, p+n)` stays wholly outside the optimizer's
reserved interval `[base, reserved)`. -/
def RangeOutside (base reserved p n : Nat) : Prop :=
  p + n ≤ base ∨ reserved ≤ p

/-- Two Yul EVM states may differ only in optimizer-owned scratch bytes and in
the active-memory high-water mark. -/
structure ScratchRel (base reserved : Nat) (left right : EvmState) : Prop where
  observables_eq : observables left = observables right
  memory_eq : ∀ i, i < base ∨ reserved ≤ i → left.memory i = right.memory i

namespace ScratchRel

theorem refl (base reserved : Nat) (st : EvmState) : ScratchRel base reserved st st :=
  ⟨rfl, fun _ _ => rfl⟩

theorem symm {base reserved : Nat} {a b : EvmState}
    (h : ScratchRel base reserved a b) : ScratchRel base reserved b a :=
  ⟨h.observables_eq.symm, fun i hi => (h.memory_eq i hi).symm⟩

theorem trans {base reserved : Nat} {a b c : EvmState}
    (hab : ScratchRel base reserved a b) (hbc : ScratchRel base reserved b c) :
    ScratchRel base reserved a c :=
  ⟨hab.observables_eq.trans hbc.observables_eq,
   fun i hi => (hab.memory_eq i hi).trans (hbc.memory_eq i hi)⟩

theorem runObservables_eq {base reserved : Nat} {st0 a b : EvmState}
    (h : ScratchRel base reserved a b) :
    runObservables st0 a = runObservables st0 b := by
  have hr := congrArg Obs.returndata h.observables_eq
  have hh := congrArg Obs.halted h.observables_eq
  change a.returndata = b.returndata at hr
  change a.halted = b.halted at hh
  cases ha : a.halted with
  | none =>
      have hb : b.halted = none := hh.symm.trans ha
      simpa [runObservables, committedState, ha, hb] using h.observables_eq
  | some pair =>
      obtain ⟨kind, data⟩ := pair
      have hb : b.halted = some (kind, data) := hh.symm.trans ha
      cases hc : kind.commits with
      | false =>
          simp only [runObservables, committedState, ha, hb, hc,
            Bool.false_eq_true, ↓reduceIte]
          rw [hr]
      | true =>
          simpa [runObservables, committedState, ha, hb, hc] using h.observables_eq

end ScratchRel

/-- Open-world calls may depend on the world and on their explicit input, but
not on optimizer-owned caller-memory bytes or on `msize`.  The biconditional is
needed for observational equivalence rather than one-way refinement. -/
def CallsScratchInsensitive (calls : ExternalCalls) (base reserved : Nat) : Prop :=
  ∀ req left right response, ScratchRel base reserved left right →
    (calls.Call req left response ↔ calls.Call req right response)

/-- Creation analogue of `CallsScratchInsensitive`; the copied init code is
already part of `req`. -/
def CreatesScratchInsensitive (creates : ExternalCreates) (base reserved : Nat) : Prop :=
  ∀ req left right response, ScratchRel base reserved left right →
    (creates.Create req left response ↔ creates.Create req right response)

/-- Dynamic memory-footprint side condition for one source built-in.  Malformed
arities need no condition because they have no successful semantic step.
`msize` is always forbidden: it directly observes the ignored high-water mark.
-/
def OpMemorySafe (base reserved : Nat) : Op → List U256 → Prop
  | .keccak256, [p, n] | .log0, [p, n] | .ret, [p, n] | .revert, [p, n] =>
      RangeOutside base reserved p.toNat n.toNat
  | .mload, [p] | .mstore, [p, _] => RangeOutside base reserved p.toNat 32
  | .mstore8, [p, _] => RangeOutside base reserved p.toNat 1
  | .mcopy, [dst, src, n] =>
      RangeOutside base reserved dst.toNat n.toNat ∧
        RangeOutside base reserved src.toNat n.toNat
  | .calldatacopy, [dst, _, n] | .codecopy, [dst, _, n]
  | .returndatacopy, [dst, _, n] | .datacopy, [dst, _, n] =>
      RangeOutside base reserved dst.toNat n.toNat
  | .extcodecopy, [_, dst, _, n] => RangeOutside base reserved dst.toNat n.toNat
  | .log1, [p, n, _] | .log2, [p, n, _, _] | .log3, [p, n, _, _, _]
  | .log4, [p, n, _, _, _, _] => RangeOutside base reserved p.toNat n.toNat
  | .call, [_, _, _, input, inputSize, output, outputSize]
  | .callcode, [_, _, _, input, inputSize, output, outputSize] =>
      RangeOutside base reserved input.toNat inputSize.toNat ∧
        RangeOutside base reserved output.toNat outputSize.toNat
  | .delegatecall, [_, _, input, inputSize, output, outputSize]
  | .staticcall, [_, _, input, inputSize, output, outputSize] =>
      RangeOutside base reserved input.toNat inputSize.toNat ∧
        RangeOutside base reserved output.toNat outputSize.toNat
  | .create, [_, p, n] | .create2, [_, p, n, _] =>
      RangeOutside base reserved p.toNat n.toNat
  | .msize, _ => False
  | _, _ => True

/-- The ordinary open-world EVM dialect instrumented with the operational
memoryguard promise.  A derivation exists only when every executed built-in's
dynamic footprint avoids the optimizer-owned interval.  Reusing the standard
big-step judgment avoids a second, manually mirrored semantics. -/
@[reducible] def guardedEvm (calls : ExternalCalls) (creates : ExternalCreates)
    (base reserved : Nat) : Dialect where
  Op := Op
  Value := U256
  State := EvmState
  litValue := litValue
  litWF := litWF
  Builtin := fun op args st result =>
    builtinWithExternal calls creates op args st result ∧
      OpMemorySafe base reserved op args
  effects := effects

/-- A safe run of raw guarded Yul after the compiler has chosen the marker
result.  This is the source-side contract consumed by the spilling theorem. -/
def GuardedRun (calls : ExternalCalls) (creates : ExternalCreates)
    (raw : Block Op) (base reserved : Nat) (st0 : EvmState)
    (V' : VEnv (guardedEvm calls creates base reserved)) (st' : EvmState)
    (o : Outcome) : Prop :=
  Run (guardedEvm calls creates base reserved)
    (resolveMemoryGuardStmts base reserved raw) st0 V' st' o

/-- The complete external part of a concrete reservation contract. -/
structure GuardedExternals (calls : ExternalCalls) (creates : ExternalCreates)
    (base reserved : Nat) : Prop where
  calls_insensitive : CallsScratchInsensitive calls base reserved
  creates_insensitive : CreatesScratchInsensitive creates base reserved

end YulEvmCompiler.Optimizer
