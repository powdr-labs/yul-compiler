import YulEvmCompiler.Optimizer.Implementation.Normalization.Disambiguate.Basic
import YulEvmCompiler.Optimizer.Implementation.Normalization.Disambiguate.Alpha
import YulEvmCompiler.Optimizer.Implementation.Normalization.Disambiguate.Instance
import YulEvmCompiler.Optimizer.Implementation.Normalization.Disambiguate.Ren
import YulEvmCompiler.Optimizer.Implementation.Normalization.Disambiguate.Sound
import YulEvmCompiler.Optimizer.Implementation.Normalization.Disambiguate.SoundBwd
import YulEvmCompiler.Optimizer.Implementation.Normalization.Disambiguate.Run
import YulEvmCompiler.Optimizer.Implementation.Normalization.Disambiguate.NormalForm
import YulEvmCompiler.Optimizer.Implementation.Normalization.Disambiguate.Pass
/-!
# Name disambiguation (umbrella)

The disambiguation normalizer and its verification, one module per concern:

* `Basic` — the pass (`disambiguate`) and its syntactic postcondition
  (`Disambiguated`, established by `disambiguate_disambiguated`);
* `Alpha` — the range-indexed α-relation between source and renamed programs;
* `Instance` — the pass's output is α-related to its input (`alpha_disambiguate`);
* `Ren` — the renaming configurations (`RenCfg`/`RenFCfg`) and their lemmas;
* `Sound` / `SoundBwd` — the forward and backward step simulations;
* `Run` — the assembled whole-program soundness (`disambiguate_runEquivBlock`);
* `NormalForm` — bridge to the shared spec (`disambiguate_uniqueNames`);
* `Pass` — the whole-tree transform (`disambiguateObject`) `compileSource` runs
  first, with its conditional soundness (`SourceValid` assumed, not decided —
  see that module's docstring for the limitation).
-/
