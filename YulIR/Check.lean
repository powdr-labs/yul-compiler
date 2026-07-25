import YulIR
import YulEvmCompiler.Compile
import YulEvmCompiler.Optimizer.Implementation.Pipeline
import YulEvmCompiler.Optimizer.Implementation.StackLayout
import YulEvmCompilerTests.SolcDifferential
import YulSemantics.Interp

set_option warningAsError true
/-!
# YulIR.Check — reusable baseline computation

Shared logic behind the `YulIR` baseline (`UpdateBaseline` / `CheckBaseline`):

* **semantic round-trip** — run a program and its `toYul ∘ ofYul` through the
  `yul-semantics` interpreter from several initial states and compare an observable
  fingerprint of the final state + outcome (the `VEnv` differs by `_ir_*` temps, so it
  is excluded; function-typed state fields are sampled at probe keys);
* **backend metrics** — compile the program raw / via the current optimizer / via the IR
  round-trip, and report code size and execution gas (IR vs current) using the existing
  differential harness (`SolcDifferential.measureGas` / `compareBytecode`).

`reportLine` renders one canonical, deterministic baseline row per program; `fullReport`
joins them. The row is a plain-text snapshot so the baseline file is human-readable and
diffs cleanly in review.
-/

namespace YulIR.Check

open YulSemantics EVM
open YulEvmCompilerTests.SolcDifferential (measureGas compareBytecode)

/-! ### Semantic round-trip (interpreter level) -/

/-- Storage/transient keys sampled by the fingerprint. -/
def probeKeys : List U256 := (List.range 32).map (fun i => BitVec.ofNat 256 i)

/-- Number of memory bytes sampled by the fingerprint. -/
def probeMemBytes : Nat := 256

/-- Fuel for the interpreter round-trip. -/
def interpFuel : Nat := 200000

/-- Observable fingerprint of a final machine state + control outcome. -/
structure FingerPrint where
  outcome       : Outcome
  halted        : Option (HaltKind × List UInt8)
  returndata    : List UInt8
  logs          : List LogEntry
  selfdestructs : List (U256 × Bool)
  activeWords   : U256
  storage       : List U256
  transient     : List U256
  memory        : List UInt8
  deriving DecidableEq

/-- Project a final `(state, outcome)` onto its fingerprint. -/
def fingerprint (st : EvmState) (o : Outcome) : FingerPrint :=
  { outcome := o, halted := st.halted, returndata := st.returndata, logs := st.logs
    selfdestructs := st.selfdestructs, activeWords := st.activeWords
    storage := probeKeys.map st.storage, transient := probeKeys.map st.transient
    memory := (List.range probeMemBytes).map st.memory }

/-- Run a Yul program to a fingerprint (or a stuck/out-of-fuel status). -/
def runFP (prog : YulSemantics.Block EVM.Op) (st0 : EvmState) : Result FingerPrint :=
  (Interp.run EVM.exec interpFuel prog st0).map (fun r => fingerprint r.2.1 r.2.2)

/-- An initial state whose calldata is a byte list. -/
def withCalldata (bytes : List UInt8) : EvmState :=
  { EvmState.init with env := { EvmState.init.env with calldata := bytes } }

/-- Initial-state scenarios for the interpreter round-trip. -/
def scenarios : List (String × EvmState) :=
  [ ("init", EvmState.init)
  , ("cd=0..63", withCalldata ((List.range 64).map (fun i => UInt8.ofNat i)))
  , ("cd=42*", withCalldata (List.replicate 64 (UInt8.ofNat 42)))
  , ("cd=one", withCalldata (List.replicate 31 0 ++ [1])) ]

/-- The IR round-trip of a program, **without** IR optimizations. -/
def irRoundTrip (b : YulSemantics.Block EVM.Op) : YulSemantics.Block EVM.Op :=
  YulIR.toYul (YulIR.ofYul b)

/-- The IR round-trip **with** the IR optimization pipeline applied. As passes land in
`YulIR.optimize`, this diverges from `irRoundTrip`. -/
def irOptimized (b : YulSemantics.Block EVM.Op) : YulSemantics.Block EVM.Op :=
  YulIR.toYul (YulIR.optimize (YulIR.ofYul b))

/-- Does the program agree with its IR round-trip under the interpreter, on every
scenario (same status and, when `ok`, identical fingerprint)? -/
def roundTripPasses (prog : YulSemantics.Block EVM.Op) : Bool :=
  scenarios.all (fun (_, st0) => runFP prog st0 == runFP (irRoundTrip prog) st0)

/-- Interpreter status of the source program on the `init` scenario. -/
def sourceStatus (prog : YulSemantics.Block EVM.Op) : String :=
  match Interp.run EVM.exec interpFuel prog EvmState.init with
  | .ok _ => "ok" | .stuck => "stuck" | .outOfFuel => "oof"

/-! ### Backend metrics -/

/-- Today's production optimizer applied to a top-level block. -/
def currentOpt (b : YulSemantics.Block EVM.Op) : YulSemantics.Block EVM.Op :=
  (YulEvmCompiler.Optimizer.optimizerPipeline
    (calls := YulSemantics.EVM.ExternalCalls.none)
    (creates := YulSemantics.EVM.ExternalCreates.none)).run b

/-- Backend: block → bytecode, with the same stack-layout fallback `compileSource` uses. -/
def blockBytecode (b : YulSemantics.Block EVM.Op) : Option ByteArray :=
  (YulEvmCompiler.compile b
    <|> YulEvmCompiler.compile (YulEvmCompiler.Optimizer.stackLayoutBlock b)).map
      YulEvmCompiler.assemble

/-- Compiled code size in bytes, or `none` if the backend failed. -/
def codeSizeOf (b : YulSemantics.Block EVM.Op) : Option Nat := (blockBytecode b).map (·.size)

/-- Sum IR and current execution gas over gas-comparable scenarios; returns the
comparable-scenario count and the two totals. -/
def gasSummary (irB curB : ByteArray) : Nat × Nat × Nat :=
  (measureGas irB curB).foldl (init := (0, 0, 0)) fun (c, gi, gc) (_, r) =>
    match r with
    | some (a, b) => (c + 1, gi + a, gc + b)
    | none => (c, gi, gc)

/-- Right-pad a string to width `n`. -/
def padTo (n : Nat) (s : String) : String :=
  s ++ String.ofList (List.replicate (n - s.length) ' ')

/-- Size of an optional bytecode as a string. -/
def szStr : Option ByteArray → String
  | some ba => toString ba.size
  | none => "FAIL"

/-- One canonical baseline row for a program. -/
def reportLine (name : String) (prog : YulSemantics.Block EVM.Op) : String :=
  let cur := blockBytecode (currentOpt prog)
  let ir  := blockBytecode (irRoundTrip prog)
  let rt  := if roundTripPasses prog then "PASS" else "FAIL"
  let st  := sourceStatus prog
  let head := s!"{padTo 24 name} | st={padTo 5 st} rt={rt}"
  match ir, cur with
  | some irB, some curB =>
      let beh := match compareBytecode irB curB with | .ok _ => "eq" | .error _ => "NE"
      let (c, gi, gc) := gasSummary irB curB
      s!"{head} beh={beh} | size cur={padTo 4 (toString curB.size)} ir={padTo 4 (toString irB.size)}" ++
        s!" | gas[{c}] ir={padTo 7 (toString gi)} cur={gc}"
  | _, _ =>
      s!"{head} | size cur={szStr cur} ir={szStr ir} | gas=n/a"

/-- Render the full baseline over a corpus (deterministic, one row per program). -/
def fullReport (corpus : List (String × YulSemantics.Block EVM.Op)) : String :=
  String.intercalate "\n" (corpus.map (fun (np) => reportLine np.1 np.2)) ++ "\n"

/-- The names of programs whose interpreter round-trip fails (a hard error). -/
def roundTripFailures (corpus : List (String × YulSemantics.Block EVM.Op)) : List String :=
  (corpus.filter (fun np => !roundTripPasses np.2)).map (·.1)

end YulIR.Check
