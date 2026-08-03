import YulEvmCompiler.SsaCfg.Implementation.Compile
import YulEvmCompiler.Examples
set_option warningAsError true
/-!
# YulEvmCompiler.SsaCfg.Implementation.Examples

Build-time checks for the SSA backend, mirroring `YulEvmCompiler.Examples`:

* **acceptance** — `compileViaSsa` accepts every example program the classic
  backend accepts (plus `stackPressure`, which the classic scope-pinned
  layout rejects and the liveness-scheduled SSA layout compiles);
* **differential** — the compiled-via-SSA bytecode is executed with
  evm-semantics' `stepF` and its final storage/returndata compared against
  the Yul interpreter (`agreeSsa`), exactly like `agreeOn` does for the
  classic backend.

These `#guard`s run on every `lake build`, so an SSA construction, pass, or
scheduling bug that changes behavior fails the build long before the
simulation proofs cover it.
-/

namespace YulEvmCompiler.SsaCfg.Examples

open YulSemantics
open YulEvmCompiler
open YulEvmCompiler.Examples (evmInit runEvm)

/-- Differential check: run `prog` through the Yul interpreter and its
SSA-compiled bytecode through `stepF`, then compare success, returndata, and
the given storage keys. -/
def agreeSsa (prog : YulSemantics.Block YulSemantics.EVM.Op) (keys : List Nat) : Bool :=
  let yst0 : YulSemantics.EVM.EvmState :=
    { YulSemantics.EVM.EvmState.init with
      env := { YulSemantics.EVM.EvmState.init.env with
        keccakOf := YulEvmCompiler.targetKeccakOracle } }
  match compileViaSsa zeroImmutables prog, Interp.run YulSemantics.EVM.exec 100000 prog yst0 with
  | some is, .ok (_, yst, _) =>
      let s0 := evmInit (assemble is)
      let s := runEvm 100000 s0
      s.isDone
        && (s.halt matches .Success)
        && yst.returndata == s.returnData.toList
        && keys.all (fun k =>
          (yst.storage (BitVec.ofNat 256 k)).toNat
            == ((s.accountMap s.executionEnv.address).storage.get
                  (EvmSemantics.UInt256.ofNat k)).toNat)
  | _, _ => false

open YulEvmCompiler.Examples

#guard agreeSsa sumLoop [0]
#guard agreeSsa breakContinue [0]
#guard agreeSsa switchMatch [0]
#guard agreeSsa switchDefault [0]
#guard agreeSsa multiRet [0, 1]
#guard agreeSsa multiAssign [0, 1]
#guard agreeSsa wrapperHelpers [0, 1]
#guard agreeSsa multiRet3 [0, 1, 2]
#guard agreeSsa funCall [0]
#guard agreeSsa identityHelpers [0, 1]
#guard agreeSsa leaveEarly [0, 1]
#guard agreeSsa nested [0]
#guard agreeSsa breakNested [0]
#guard agreeSsa fibStorage [0]
-- the classic layout rejects this one; the SSA scheduler compiles it
#guard (YulEvmCompiler.compile YulEvmCompiler.zeroImmutables stackPressure).isNone
#guard agreeSsa stackPressure [0]
-- recursion: the classic backend rejects (the stack certificate excludes
-- unbounded frames); the SSA backend's bounded inlining + constant folding
-- fully unrolls fact(5) into a constant, so it compiles — and must agree
#guard (YulEvmCompiler.compile YulEvmCompiler.zeroImmutables factorial).isNone
#guard agreeSsa factorial [0]

end YulEvmCompiler.SsaCfg.Examples
