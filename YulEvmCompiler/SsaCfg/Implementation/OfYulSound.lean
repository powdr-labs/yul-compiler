import YulEvmCompiler.SsaCfg.Implementation.OfYulSound.Basics
import YulEvmCompiler.SsaCfg.Implementation.OfYulSound.Frames
import YulEvmCompiler.SsaCfg.Implementation.OfYulSound.Monotonicity
import YulEvmCompiler.SsaCfg.Implementation.OfYulSound.Leaves
import YulEvmCompiler.SsaCfg.Implementation.OfYulSound.FuncTable
import YulEvmCompiler.SsaCfg.Implementation.OfYulSound.ModStmts
import YulEvmCompiler.SsaCfg.Implementation.OfYulSound.CurBlock
import YulEvmCompiler.SsaCfg.Implementation.OfYulSound.CurInduction
import YulEvmCompiler.SsaCfg.Implementation.OfYulSound.NoShadow
import YulEvmCompiler.SsaCfg.Implementation.OfYulSound.Loop
import YulEvmCompiler.SsaCfg.Implementation.OfYulSound.LoopSim
import YulEvmCompiler.SsaCfg.Implementation.OfYulSound.LoopStepSim
import YulEvmCompiler.SsaCfg.Implementation.OfYulSound.Switch
import YulEvmCompiler.SsaCfg.Implementation.OfYulSound.CallSim
import YulEvmCompiler.SsaCfg.Implementation.OfYulSound.CondSim
import YulEvmCompiler.SsaCfg.Implementation.OfYulSound.BlockSim
import YulEvmCompiler.SsaCfg.Implementation.OfYulSound.Sim
set_option warningAsError true
/-!
# YulEvmCompiler.SsaCfg.Implementation.OfYulSound

**Construction soundness** for the `yul-ssa-cfg` dialect: every terminating
source derivation over a program the construction accepts is matched by an
SSA-CFG execution (`ofBlock_sound'`).

This file is the bottom-up half of that proof: the reusable infrastructure,
the statement-class simulation induction, and the top-level plumbing are all
proved outright.
-/
