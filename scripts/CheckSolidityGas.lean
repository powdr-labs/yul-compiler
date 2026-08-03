import YulParser.Compile
import YulEvmCompilerTests.Solc
import YulEvmCompilerTests.SolcDifferential
import YulEvmCompilerTests.CorpusGas
import YulEvmCompilerTests.SolidityCorpus
import YulEvmCompilerTests.InterpreterFixture
import YulEvmCompilerTests.SolTest
import YulEvmCompilerTests.Parallel
import YulEvmCompilerTests.Timing
import YulEvmCompilerTests.SolcDifferentialRunner
set_option warningAsError true

/-!
Compile and gas-check Solidity's `libsolidity/gasTests` fixtures.

Each fixture is a full Solidity contract. This compiler only accepts Yul, so we
route through solc's `--via-ir` lowering — but with the Yul optimizer OFF: solc
lowers the contract to *fully unoptimized* Yul (`--ir`), and this compiler
compiles that. So the pipeline uses only solc's Solidity→Yul front-end and none
of solc's Yul optimizer. Compiling it is the *correctness* check.

For *gas*, both this compiler's and solc's *fully optimized* creation bytecode
(`--bin --optimize --via-ir`) are deployed in the executable EVM (running the
constructor), and the contract's calls are replayed on each. semanticTests
fixtures specify their own calls in the `// ----` section (`f(uint256): 42 ->
42`); those exact calls — arguments already in flattened ABI form — are used, so
real work is exercised, state persists across the sequence, and outputs are
cross-checked. Final frame memory is intentionally excluded because it is not
observable after a contract call returns; returned data and every committed
world effect remain compared. A strict fixture with declared calls must measure
all of them. gasTests have no call spec, so each external function is called
once with synthetic argument words. Over the calls that reach identical
observable behavior, the gas each spends is summed and this compiler's total is
checked against a pinned baseline (fail if it rises while solc's is unchanged —
solc's total fingerprints the fixture; see CorpusGas).
-/

open System YulParser
open EvmSemantics
open YulEvmCompilerTests.Solc
open YulEvmCompilerTests.CorpusGas
open YulEvmCompilerTests.SolidityCorpus
open YulEvmCompilerTests.InterpreterFixture
open YulEvmCompilerTests.SolcDifferential (observe gasUsed)
open YulEvmCompilerTests.SolTest (Call Spec natToWord parseSpec)
open YulEvmCompilerTests.Parallel (detectJobs parMap weightedShard)
open YulEvmCompilerTests.Timing (since timedIO toMs)

/-- Optional deterministic source-size-weighted sharding, so the large
semanticTests corpus can be split across CI jobs without concentrating its
largest contracts in one hash bucket. -/
private structure Shard where
  index : Nat
  count : Nat

/-- Eight nonzero argument words appended after a selector, used only for the
gasTests corpus (which specifies gas per function but no call arguments). It
decodes as value-typed arguments so real work is charged; functions taking
dynamic-typed arguments revert on both sides, which stays gas-comparable. -/
private def argWords : String :=
  String.join (List.replicate 8 "0000000000000000000000000000000000000000000000000000000000000123")

/-- STOP and an empty RETURN are the same successful outcome, but our compiler
emits RETURN where solc's optimizer emits STOP for void functions. Normalize the
two so such calls stay gas-comparable; the returned bytes are still compared
(via the output field), so a real difference is not hidden. -/
private def normHalt : HaltKind → HaltKind
  | .Success => .Returned
  | h => h

/-- Behavioral equality for a completed contract call. The caller can observe
the halt/output, returndata, persistent world, logs, self-destructs, and refund,
but the callee frame's final memory disappears when the call returns. Excluding
that transient memory is also essential for guarded memory spilling: scratch
writes may remain in the halted frame without changing any committed effect. -/
private def sameOutcome (a b : EVM.State) : Bool :=
  normHalt a.halt == normHalt b.halt &&
    { observe a with halt := .Returned, memory := #[] } ==
      { observe b with halt := .Returned, memory := #[] }

private def sameOutcomeIgnoresTransientMemory : Bool :=
  let state := initialState (ByteArray.mk #[])
  sameOutcome state { state with memory := ByteArray.mk #[1] }

private def sameOutcomeStillChecksOutput : Bool :=
  let state := initialState (ByteArray.mk #[])
  !sameOutcome state { state with hReturn := ByteArray.mk #[1] }

private def parseSpecCountsUnsupportedDeclaredCalls : Bool :=
  let spec := parseSpec "// ----\n// f() -> 1\n// g(uint256): unsupported -> 0"
  spec.declaredCalls == 2 && spec.calls.size == 1

private def parseSpecDoesNotCountEnvironmentDirectives : Bool :=
  let spec := parseSpec
    "// ----\n// account: 1 -> 0x12\n// balance: 0x12 -> 10\n// f() -> 1"
  spec.declaredCalls == 1 && spec.calls.size == 1

private def parseSpecEncodesAlignedValues : Bool :=
  let spec := parseSpec
    "// ----\n// f(bytes2,bool): left(0x0022), right(true) ->"
  match spec.calls.toList with
  | [call] =>
      spec.declaredCalls == 1 &&
        call.calldata.extract 4 36 == natToWord (0x22 <<< (8 * 30)) &&
        call.calldata.extract 36 68 == natToWord 1
  | _ => false

private def parseSpecAcceptsOddNibbleHex : Bool :=
  let spec := parseSpec "// ----\n// f(bytes): hex\"123\" ->"
  match spec.calls.toList with
  | [call] =>
      spec.declaredCalls == 1 &&
        call.calldata.extract 4 36 ==
          ByteArray.mk (#[0x01, 0x23] ++ Array.replicate 30 0)
  | _ => false

private def parseSpecSkipsExplicitOutOfGasCalls : Bool :=
  let spec := parseSpec
    "// ----\n// f(uint256): 1 -> 1\n// f(uint256): 0xffff -> FAILURE # Out-of-gas #"
  spec.declaredCalls == 1 && spec.calls.size == 1

#guard sameOutcomeIgnoresTransientMemory
#guard sameOutcomeStillChecksOutput
#guard parseSpecCountsUnsupportedDeclaredCalls
#guard parseSpecDoesNotCountEnvironmentDirectives
#guard parseSpecEncodesAlignedValues
#guard parseSpecAcceptsOddNibbleHex
#guard parseSpecSkipsExplicitOutOfGasCalls

private structure Deployment where
  state : Option EVM.State
  halt : String
  returnSize : Nat

/-- Execute creation bytecode (with constructor arguments appended) and return
a state ready for calls: the returned top-level runtime is installed directly,
and the constructor's complete final account world is retained. The direct
installation deliberately omits a transaction-level EIP-170 check; CREATEs
executed by the constructor still enforce the normal target semantics. -/
private def deployForCalls (creation ctorArgs : ByteArray) (ctorValue : Nat) : Deployment :=
  let base := initialState (creation ++ ctorArgs)
  let start := { base with
    executionEnv := { base.executionEnv with weiValue := UInt256.ofNat ctorValue } }
  let fin := runEvm 3000000 start
  if !fin.isDone || fin.hReturn.size == 0 then {
    state := none
    halt := reprStr fin.halt
    returnSize := fin.hReturn.size
  }
  else
    let rtBase := initialState fin.hReturn
    let addr := rtBase.executionEnv.address
    -- Top-level creation is executed directly, outside a transaction deploy
    -- step, so install its returned runtime explicitly. Keep the rest of the
    -- constructor's final world: integration fixtures create managers,
    -- routers, and tokens whose code and state must survive into the calls.
    let deployed := { (fin.accountMap addr) with
      code := (rtBase.accountMap addr).code }
    let accounts := fin.accountMap.set addr deployed
    {
      state := some { rtBase with
        accountMap := accounts
        substate := { rtBase.substate with originalAccountMap := accounts } }
      halt := reprStr fin.halt
      returnSize := fin.hReturn.size
    }

private def withCall (state : EVM.State) (call : Call) : EVM.State :=
  { state with
    executionEnv := { state.executionEnv with
      calldata := call.calldata, weiValue := UInt256.ofNat call.value }
    substate := { state.substate with originalAccountMap := state.accountMap } }

/-- Replay a call sequence on both deployments, summing per-call gas over the
leading run of behaviorally-identical calls. State persists across calls (as in
a real test), so a divergence or non-halt ends the sequence — the two worlds
would part after it. The result is empty if no call was comparable. -/
private structure CallGas where
  sig : String
  ours : Nat
  solc : Nat

private def replayCalls (ourBase solcBase : EVM.State) (calls : Array Call)
    (fuel : Nat := 3000000) : Array CallGas × Option String := Id.run do
  let mut ourState := ourBase
  let mut solcState := solcBase
  let mut measured : Array CallGas := #[]
  let mut failure : Option String := none
  for call in calls do
    let os := withCall ourState call
    let ss := withCall solcState call
    let ourFinal := runEvm fuel os
    let solcFinal := runEvm fuel ss
    if !(ourFinal.isDone && solcFinal.isDone && sameOutcome ourFinal solcFinal) then
      let ours := { observe ourFinal with halt := .Returned, memory := #[] }
      let solc := { observe solcFinal with halt := .Returned, memory := #[] }
      failure := some (s!"at {call.sig}: " ++
        s!"done={ourFinal.isDone}/{solcFinal.isDone}, " ++
        s!"halt={normHalt ourFinal.halt == normHalt solcFinal.halt}, " ++
        s!"output={ours.output == solc.output}" ++
          s!"(size {ours.output.size}/{solc.output.size}), " ++
        s!"returndata={ours.returnData == solc.returnData}, " ++
        s!"accounts={ours.accounts == solc.accounts}, logs={ours.logs == solc.logs}, " ++
        s!"selfdestructs={ours.selfDestructs == solc.selfDestructs}, refund={ours.refund == solc.refund}")
      break
    measured := measured.push {
      sig := call.sig
      ours := gasUsed os ourFinal
      solc := gasUsed ss solcFinal
    }
    ourState := { ourState with accountMap := ourFinal.accountMap }
    solcState := { solcState with accountMap := solcFinal.accountMap }
  return (measured, failure)

/-! ## Optional solc-side execution cache (`--solc-cache=<dir>`)

The solc half of a gas re-pin — `solcCreationBytecode`, its `deployForCalls`,
and its share of `replayCalls` — is fully deterministic given the fixture
source, the pinned solc version, and the call sequence. When `--solc-cache` is
set, that half is recorded per fixture on the populating run and replayed from a
small text file on later runs, comparing our side against the cached solc
observation fingerprints instead of re-executing solc. The flag never changes
behavior when absent: the live path below is left untouched. -/

/-- Bump when the cache line format or the observation normalization below
changes, so caches written by an older harness are treated as stale. -/
private def solcCacheFormatVersion : Nat := 1

/-- The single observation normalization used for BOTH sides of the gas
comparison. It hashes exactly what `sameOutcome` compares — the observation with
`normHalt` applied to the halt kind and the transient callee memory dropped — so
`obsFingerprint a == obsFingerprint b` iff `sameOutcome a b` (modulo hash
collision; this is a test cache). Memory is excluded (matching `memory := #[]`),
and `normHalt` is folded in (matching the separate halt check plus the
`halt := .Returned` normalization in `sameOutcome`). -/
private def obsFingerprint (s : EVM.State) : UInt64 :=
  let o := observe s
  let logs := String.intercalate ";" (o.logs.toList.map fun log =>
    s!"{log.address.val}:{reprStr (log.topics.map (·.toNat))}:{Hex.bytesToHex log.payload}")
  let canonical := String.intercalate "|" [
    reprStr (normHalt o.halt),
    Hex.bytesToHex o.output,
    Hex.bytesToHex o.returnData,
    reprStr o.accounts,
    logs,
    reprStr (o.selfDestructs.map (·.val)),
    toString o.refund.toNat
  ]
  hash canonical

/-- One replayed solc call, as stored in the cache. `fingerprint` is the decimal
form of `obsFingerprint`, kept as a string so the read path compares it without
re-parsing a `UInt64`. `sig` is written for human readability only; the read
path drives the sequence from the live call list, not from the cached sig. -/
private structure SolcCallRecord where
  sig : String
  isDone : Bool
  fingerprint : String
  gas : Nat

/-- The cached (or freshly measured) solc side of one fixture: whether solc's
deployment produced a runtime, a repr of its deployment halt (`(cached)` when
read back), the deployment's returndata size, and the ordered per-call records.
`records` is meaningful only when `deployed` is true. -/
private structure SolcSide where
  deployed : Bool
  deployHalt : String
  deployReturnSize : Nat
  records : Array SolcCallRecord

/-- Run solc's deployed runtime over the whole call sequence independently of
our side, recording one fingerprint/gas record per call. State persists across
calls exactly as in `replayCalls`; recording stops at the first non-halting
call, which the read path then reproduces as a live mismatch there. Running the
full sequence (not just the leading run our side happens to match) keeps the
cache valid even if our codegen later matches a different number of calls. -/
private def runSolcCalls (solcBase : EVM.State) (calls : Array Call)
    (fuel : Nat := 3000000) : Array SolcCallRecord := Id.run do
  let mut solcState := solcBase
  let mut records : Array SolcCallRecord := #[]
  for call in calls do
    let ss := withCall solcState call
    let solcFinal := runEvm fuel ss
    records := records.push {
      sig := call.sig
      isDone := solcFinal.isDone
      fingerprint := toString (obsFingerprint solcFinal)
      gas := gasUsed ss solcFinal
    }
    if !solcFinal.isDone then break
    solcState := { solcState with accountMap := solcFinal.accountMap }
  return records

/-- The cached analogue of `replayCalls`: our side runs live and is compared
against the cached solc fingerprints in sequence order, stopping at the first
mismatch (or missing cached record) exactly as a live divergence would. The
cached gas is used as solc's gas. -/
private def replayCallsCached (ourBase : EVM.State) (calls : Array Call)
    (records : Array SolcCallRecord) (fuel : Nat := 3000000)
    : Array CallGas × Option String := Id.run do
  let mut ourState := ourBase
  let mut measured : Array CallGas := #[]
  let mut failure : Option String := none
  let mut index := 0
  for call in calls do
    let os := withCall ourState call
    let ourFinal := runEvm fuel os
    match records[index]? with
    | some rec =>
        if !(ourFinal.isDone && rec.isDone &&
            toString (obsFingerprint ourFinal) == rec.fingerprint) then
          failure := some (s!"at {call.sig}: differs from cached solc observation " ++
            s!"(done={ourFinal.isDone}/{rec.isDone})")
          break
        measured := measured.push {
          sig := call.sig
          ours := gasUsed os ourFinal
          solc := rec.gas
        }
        ourState := { ourState with accountMap := ourFinal.accountMap }
    | none =>
        failure := some s!"at {call.sig}: no cached solc observation for this call"
        break
    index := index + 1
  return (measured, failure)

/-- Cache key over the fixture source: the format version, source length (cheap
extra collision safety), the pinned solc version, and the source text. -/
private def sourceCacheHash (source solcVersion : String) : UInt64 :=
  hash s!"{solcCacheFormatVersion}|{source.length}|{solcVersion}|{source}"

/-- Cache key over the call spec (constructor args/value and every call
descriptor) so a changed spec — including synthetic gasTests selectors —
invalidates the cache even when the source text is unchanged. -/
private def callsCacheHash (ctorArgs : ByteArray) (ctorValue : Nat)
    (calls : Array Call) : UInt64 :=
  let descriptors := calls.toList.map fun c =>
    s!"{c.sig}#{c.value}#{Hex.bytesToHex c.calldata}"
  hash s!"{Hex.bytesToHex ctorArgs}#{ctorValue}#{String.intercalate "," descriptors}"

/-- Fixture relative paths contain `/`; map anything that is not a filename-safe
character to `_` so the cache file name is a single flat path component. -/
private def sanitizeCacheName (name : String) : String :=
  String.ofList (name.toList.map fun c =>
    if c.isAlphanum || c == '.' || c == '-' then c else '_')

private def parseCallLine (line : String) : Option SolcCallRecord :=
  match line.splitOn " " with
  | "call" :: isDone :: fp :: gasStr :: _ =>
      match gasStr.toNat? with
      | some gas => some { sig := "", isDone := isDone == "1", fingerprint := fp, gas }
      | none => none
  | _ => none

/-- Parse a cache file, returning the solc side only if the header matches the
current format version, source hash, solc version, and call-spec hash. Any
staleness or malformation yields `none`, which the caller treats as a miss. -/
private def parseSolcCache (contents : String) (sourceHash callsHash : UInt64)
    (solcVersion : String) : Option SolcSide :=
  match (contents.splitOn "\n").filter (fun l => !l.isEmpty) with
  | header :: deployLine :: callLines =>
      if header != s!"v{solcCacheFormatVersion} {sourceHash} {solcVersion} {callsHash}" then none
      else match deployLine.splitOn " " with
        | ["deploy", ok, _haltHash, rs] =>
            match rs.toNat?, callLines.mapM parseCallLine with
            | some returnSize, some records =>
                some { deployed := ok == "ok", deployHalt := "(cached)",
                       deployReturnSize := returnSize, records := records.toArray }
            | _, _ => none
        | _ => none
  | _ => none

/-- Read and validate a fixture's cache file; `none` on absence, staleness, or
malformation. -/
private def loadSolcCache (file : System.FilePath) (sourceHash callsHash : UInt64)
    (solcVersion : String) : IO (Option SolcSide) := do
  if ← file.pathExists then
    return parseSolcCache (← IO.FS.readFile file) sourceHash callsHash solcVersion
  else
    return none

/-- Write a fixture's solc-side cache. The deployment-halt repr is stored only
as a hash, so the read path's deployment-failure message is less specific than
the live one — acceptable because that message is diagnostic (stderr) only. -/
private def writeSolcCache (file : System.FilePath) (sourceHash callsHash : UInt64)
    (solcVersion : String) (side : SolcSide) : IO Unit := do
  let header := s!"v{solcCacheFormatVersion} {sourceHash} {solcVersion} {callsHash}"
  let deployLine :=
    s!"deploy {if side.deployed then "ok" else "fail"} {hash side.deployHalt} {side.deployReturnSize}"
  let callLines := side.records.toList.map fun rec =>
    s!"call {if rec.isDone then "1" else "0"} {rec.fingerprint} {rec.gas} {rec.sig}"
  let text := String.intercalate "\n" (header :: deployLine :: callLines) ++ "\n"
  if let some parent := file.parent then IO.FS.createDirAll parent
  IO.FS.writeFile file text

/-- Pin one row per external function. Repeated calls to the same signature
are summed so existing multi-vector library fixtures still have stable keys. -/
private def perScenarioRows (name : String) (calls : Array CallGas) : Array GasRow :=
  calls.foldl (init := #[]) fun rows call =>
    let key := s!"{name}:{call.sig}"
    match rows.findIdx? (fun row => row.fixture == key) with
    | none => rows.push { fixture := key, ours := call.ours, solc := call.solc }
    | some index => rows.modify index fun row =>
        { row with ours := row.ours + call.ours, solc := row.solc + call.solc }

private def totalRow (name : String) (calls : Array CallGas) : GasRow :=
  calls.foldl (init := { fixture := name, ours := 0, solc := 0 }) fun row call =>
    { row with ours := row.ours + call.ours, solc := row.solc + call.solc }

/-- The per-contract verdict, accumulated exactly as the old sequential loop did
but computed independently so contracts can be gas-checked concurrently. -/
private structure GasOutcome where
  compileFailure : Option (String × String) := none
  measurementFailure : Option (String × String) := none
  skipped : Bool := false
  measured : Array GasRow := #[]

/-- How long one contract took, split by which compiler did the work.

Kept out of `GasOutcome` and threaded through a per-contract `IO.Ref` so the
dozen existing early returns stay untouched: whatever a contract's verdict turns
out to be, the clock readings taken along the way are still reported.

Both backend figures measure the *same* job on the *same* input — unoptimized
Yul → EVM bytecode. solc's Solidity→Yul front-end is charged to neither: it runs
once, before either backend, and its output is what both then compile. -/
private structure Timing where
  /-- solc's `--ir` lowering of the Solidity fixture — the front-end that
  produces the Yul *both* backends compile, and so is charged to neither. -/
  frontendNs : Nat := 0
  /-- This compiler, unoptimized Yul → bytecode, on fixtures it accepted. -/
  oursNs : Nat := 0
  /-- This compiler's time on fixtures it *rejected*, kept apart so the two
  backend columns cover one identical fixture set. Reported separately rather
  than dropped: rejecting a large contract can cost minutes. -/
  rejectedNs : Nat := 0
  /-- This compiler's time on fixtures it compiled but solc would not — the
  other way a fixture fails to form a comparable pair. Neither side is counted,
  since a one-sided figure would compare the backends on different work. -/
  unpairedNs : Nat := 0
  /-- solc `--strict-assembly`, the same unoptimized Yul → bytecode. Deliberately
  *not* solc's `--optimize --via-ir` compile zeroImmutables (which the gas comparison also runs):
  that starts from Solidity and includes both the front-end and the Yul
  optimizer, so it would not be the same job as `oursNs`. -/
  solcNs : Nat := 0
  /-- Whether both compilers finished the job, i.e. `oursNs` and `solcNs` are a
  comparable pair. This is the only case either column counts. -/
  compiled : Bool := false
  /-- Whether this compiler rejected it, i.e. `rejectedNs` is a measurement. -/
  rejected : Bool := false
  /-- Whether solc rejected it, i.e. `unpairedNs` is a measurement. -/
  unpaired : Bool := false

/-- Deploy our bytecode and measure the fixture against an already-resolved solc
side (cached or freshly measured), through the shared `obsFingerprint` replay.
Because `obsFingerprint`-equality coincides with `sameOutcome`, the measured rows
match the live path exactly — the reason a populating (`--solc-cache`) run
produces the same summary as a flagless run. -/
private def measureWithSolcSide (name : String) (perScenario : Bool)
    (creation : ByteArray) (spec : Spec) (calls : Array Call)
    (replayFuel : Nat) (side : SolcSide) : GasOutcome :=
  let ourDeployment := deployForCalls creation spec.ctorArgs spec.ctorValue
  match ourDeployment.state, side.deployed with
  | some ourBase, true =>
      let (callGas, replayFailure) := replayCallsCached ourBase calls side.records replayFuel
      if spec.declaredCalls != 0 && callGas.size != calls.size then
        { measurementFailure := some (name,
            s!"only {callGas.size}/{calls.size} declared calls reached matching observable behavior" ++
              (replayFailure.map fun detail => s!"; {detail}").getD "") }
      else if callGas.isEmpty then {}
      else if perScenario then { measured := perScenarioRows name callGas }
      else { measured := #[totalRow name callGas] }
  | _, _ =>
      if spec.declaredCalls == 0 then {}
      else
        { measurementFailure := some (name,
            s!"deployment did not produce runtime for declared calls " ++
              s!"(ours={ourDeployment.halt}/{ourDeployment.returnSize}, " ++
              s!"solc={side.deployHalt}/{side.deployReturnSize})") }

/-- Time solc doing exactly this compiler's job — assembling the same unoptimized
Yul to bytecode, no optimizer — and charge the two sides only as a pair.

This is a measurement-only invocation: the gas comparison needs solc's *optimized*
bytecode and compiles that separately, and this is the only way to get a runtime
figure for the same job on the same input.

If solc will not assemble the Yul this compiler just compiled, there is no
comparable pair, so *neither* side is counted — charging one and not the other
would compare the backends on different work, and a fast error would deflate
solc's total. This compiler's time still goes to `unpairedNs` so it stays
visible rather than silently vanishing. -/
private def chargeCompilePair (clock : IO.Ref Timing) (solcPath ir : String)
    (oursNs : Nat) : IO Unit := do
  let (result, solcNs) ← timedIO (compileWithSolc solcPath ir)
  if result matches .ok _ then
    clock.modify fun t => { t with oursNs, solcNs, compiled := true }
  else
    clock.modify fun t => { t with unpairedNs := oursNs, unpaired := true }

/-- Compile one contract through solc's unoptimized `--via-ir` Yul, deploy both
this compiler's and solc's optimized bytecode, replay the fixture's calls, and
measure gas — the body of the old loop, extracted as an independent unit of
work with no shared mutable state. Timings go to `clock`. -/
private def processContractIn (clock : IO.Ref Timing) (dir : FilePath) (solcPath : String)
    (perScenario : Bool) (solcCache : Option FilePath) (solcVersion : String)
    (path : FilePath) : IO GasOutcome := do
  let name := relativeName dir path
  let contents ← IO.FS.readFile path
  match runsOnLatestFork contents with
  | .error message => return { compileFailure := some (name, s!"metadata: {message}") }
  | .ok false => return { skipped := true }
  | .ok true =>
      let source := fixtureSource contents
      let (irResult, frontendNs) ← timedIO (solcUnoptimizedIR solcPath source)
      clock.modify ({ · with frontendNs })
      match irResult with
      | .error message => return { compileFailure := some (name, message) }
      | .ok ir =>
          -- Read the stop clock inside each branch, not after a `let creation? :=
          -- compileSource ir`. Lean's compiler sinks a pure binding to where it
          -- is scrutinised, so timing around the binding measures nothing (it
          -- reported 0 ms for a 3-minute compile); the `match` is what forces it.
          let compileStart ← IO.monoNanosNow
          match compileSource ir with
          | none =>
              clock.modify ({ · with rejectedNs := ← since compileStart, rejected := true })
              return { compileFailure := some (name, "this compiler rejected solc's unoptimized IR") }
          | some creation =>
            -- Charge solc for the identical job on the identical input, and only
            -- as a pair, so both columns always cover one identical fixture set.
            chargeCompilePair clock solcPath ir (← since compileStart)
            match solcCache with
            | none =>
              match ← solcCreationBytecode solcPath source with
              | .error message => return { compileFailure := some (name, message) }
              | .ok solcCreation =>
                  -- Replay the fixture's own specified calls (semanticTests).
                  -- With no call spec (gasTests) fall back to one synthetic
                  -- call per external function selector.
                  let spec := parseSpec contents
                  if spec.calls.size != spec.declaredCalls then
                    return { measurementFailure := some (name,
                      s!"only {spec.calls.size}/{spec.declaredCalls} declared calls could be parsed") }
                  let calls ← do
                    if spec.declaredCalls == 0 then
                      match ← solcFunctionSelectors solcPath source with
                      | .error _ => pure #[]
                      | .ok sels => pure (sels.toArray.map fun s =>
                          ({ sig := s, value := 0,
                             calldata := Hex.hexToBytes (s ++ argWords) } : Call))
                    else pure spec.calls
                  let ourDeployment :=
                    deployForCalls creation spec.ctorArgs spec.ctorValue
                  let solcDeployment :=
                    deployForCalls solcCreation spec.ctorArgs spec.ctorValue
                  match ourDeployment.state, solcDeployment.state with
                  | some ourBase, some solcBase =>
                      -- Aave's upstream PositionStatusMap stress tests traverse
                      -- up to 10,000 reserve IDs. They stay below the EVM gas
                      -- limit but require more small-step fuel than ordinary
                      -- corpus calls under this compiler's unoptimized output.
                      let replayFuel :=
                        if dir.fileName == some "aave-v4" then 30000000 else 3000000
                      let (callGas, replayFailure) :=
                        replayCalls ourBase solcBase calls replayFuel
                      if spec.declaredCalls != 0 && callGas.size != calls.size then
                        return { measurementFailure := some (name,
                          s!"only {callGas.size}/{calls.size} declared calls reached matching observable behavior" ++
                            (replayFailure.map fun detail => s!"; {detail}").getD "") }
                      else if callGas.isEmpty then return {}
                      else if perScenario then
                        return { measured := perScenarioRows name callGas }
                      else
                        return { measured := #[totalRow name callGas] }
                  | _, _ =>
                      if spec.declaredCalls == 0 then return {}
                      else
                        let failure :=
                          (name, s!"deployment did not produce runtime for declared calls " ++
                            s!"(ours={ourDeployment.halt}/{ourDeployment.returnSize}, " ++
                            s!"solc={solcDeployment.halt}/{solcDeployment.returnSize})")
                        return { measurementFailure := some failure }
            | some cacheDir =>
              -- The call list (needed for our side and the cache key) is derived
              -- as in the live path; only solc's creation bytecode, deployment,
              -- and per-call execution are cached.
              let spec := parseSpec contents
              if spec.calls.size != spec.declaredCalls then
                return { measurementFailure := some (name,
                  s!"only {spec.calls.size}/{spec.declaredCalls} declared calls could be parsed") }
              let calls ← do
                if spec.declaredCalls == 0 then
                  match ← solcFunctionSelectors solcPath source with
                  | .error _ => pure #[]
                  | .ok sels => pure (sels.toArray.map fun s =>
                      ({ sig := s, value := 0,
                         calldata := Hex.hexToBytes (s ++ argWords) } : Call))
                else pure spec.calls
              let replayFuel := if dir.fileName == some "aave-v4" then 30000000 else 3000000
              let sourceHash := sourceCacheHash source solcVersion
              let callsHash := callsCacheHash spec.ctorArgs spec.ctorValue calls
              let cacheFile := cacheDir / (sanitizeCacheName name ++ ".solccache")
              match ← loadSolcCache cacheFile sourceHash callsHash solcVersion with
              | some side =>
                  return measureWithSolcSide name perScenario creation spec calls replayFuel side
              | none =>
                  -- Cache miss/stale: run solc live (creation + deploy + full
                  -- call sequence), write the cache, then measure through the
                  -- same fingerprint tail the read path uses.
                  match ← solcCreationBytecode solcPath source with
                  | .error message => return { compileFailure := some (name, message) }
                  | .ok solcCreation =>
                      let solcDeployment :=
                        deployForCalls solcCreation spec.ctorArgs spec.ctorValue
                      let side : SolcSide := match solcDeployment.state with
                        | some solcBase =>
                            { deployed := true, deployHalt := solcDeployment.halt,
                              deployReturnSize := solcDeployment.returnSize,
                              records := runSolcCalls solcBase calls replayFuel }
                        | none =>
                            { deployed := false, deployHalt := solcDeployment.halt,
                              deployReturnSize := solcDeployment.returnSize, records := #[] }
                      writeSolcCache cacheFile sourceHash callsHash solcVersion side
                      return measureWithSolcSide name perScenario creation spec calls replayFuel side

/-- `processContractIn` plus the clock it writes to, so a worker returns both the
contract's verdict and how the time on it was spent. -/
private def processContract (dir : FilePath) (solcPath : String) (perScenario : Bool)
    (solcCache : Option FilePath) (solcVersion : String)
    (path : FilePath) : IO (GasOutcome × Timing) := do
  let clock ← IO.mkRef ({} : Timing)
  let outcome ← processContractIn clock dir solcPath perScenario solcCache solcVersion path
  return (outcome, ← clock.get)

private def usage : String :=
  "usage: CheckSolidityGas <contracts-dir> <gas-baseline.txt> " ++
    "<solc-path> <expected-solc-version> [--lenient] [--update] " ++
    "[--per-scenario] [--known=<known-compile-failures.txt>] [--solc-cache=<dir>]"

/-- `lenient`: treat contracts this compiler cannot handle as skips rather than
failures. Off for the curated gasTests (every contract must compile); on for the
broad semanticTests corpus, where many contracts use unsupported features and
only the gas of the compilable, behaviorally comparable subset is pinned.

`known`: a checked-in list of fixtures this compiler is expected to reject
(same convention as the compile-corpus known-failure lists). Strict otherwise:
an unlisted compile zeroImmutables failure fails the run, and so does a stale entry that now
compiles — the list must always match reality. Used for the curated Uniswap
v4-core and Aave v4 suites, whose heaviest fixtures sit beyond the current
compiler's supported fragment on purpose, to record the frontier.

`perScenario`: pin one row per external function signature instead of one total
per fixture. Repeated calls to the same signature are summed. The in-repo
`uniswap-v4` and `aave-v4` directories always enable this mode. -/
private def run (dir baselineFile : FilePath)
    (solcPath expectedSolcVersion : String) (lenient update : Bool)
    (perScenario : Bool) (known : Option (Array String)) (shard : Option Shard)
    (solcCache : Option FilePath) : IO UInt32 := do
  match ← checkSolcVersion solcPath expectedSolcVersion with
  | .error message => IO.eprintln message; return 1
  | .ok () => pure ()
  let paths ← dir.walkDir
  let allFiles := paths.filter (fun p => p.extension == some "sol")
    |>.qsort (fun a b => relativeName dir a < relativeName dir b)
  let files ← match shard with
    | none => pure allFiles
    | some shard => weightedShard shard.index shard.count allFiles fun path => do
        return (← path.metadata).byteSize.toNat
  let selectedNames := files.map (relativeName dir)
  -- Scenario baselines append `:<signature>` to the Solidity fixture path.
  -- Retain those rows when selecting a whole fixture (including shard runs),
  -- while preserving exact path matching for contract-total baselines.
  let perScenario := perScenario ||
    dir.fileName == some "uniswap-v4" || dir.fileName == some "aave-v4"
  let selected (fixture : String) : Bool := selectedNames.any fun name =>
    fixture == name || (perScenario && fixture.startsWith (name ++ ":"))
  if files.isEmpty then
    IO.eprintln s!"{dir}: found no .sol fixtures"
    return 1
  let mut measured : Array GasRow := #[]
  let mut compileFailures : Array (String × String) := #[]
  let mut measurementFailures : Array (String × String) := #[]
  let mut skipped := 0
  let jobs ← detectJobs
  -- The checked-in protocol suites always use scenario rows; keeping this
  -- directory convention automatic avoids duplicating policy in their runner
  -- invocations. The flag remains available for other local suites.
  let mut oursNs := 0
  let mut solcNs := 0
  let mut frontendNs := 0
  let mut rejectedNs := 0
  let mut unpairedNs := 0
  let mut compiledCount := 0
  let mut rejectedCount := 0
  let mut unpairedCount := 0
  let outcomes : Array (GasOutcome × Timing) ← parMap jobs files
    (processContract dir solcPath perScenario solcCache expectedSolcVersion)
  for (outcome, timing) in outcomes do
    if let some entry := outcome.compileFailure then compileFailures := compileFailures.push entry
    if let some entry := outcome.measurementFailure then
      measurementFailures := measurementFailures.push entry
    if outcome.skipped then skipped := skipped + 1
    measured := measured ++ outcome.measured
    oursNs := oursNs + timing.oursNs
    solcNs := solcNs + timing.solcNs
    frontendNs := frontendNs + timing.frontendNs
    rejectedNs := rejectedNs + timing.rejectedNs
    unpairedNs := unpairedNs + timing.unpairedNs
    if timing.compiled then compiledCount := compiledCount + 1
    if timing.rejected then rejectedCount := rejectedCount + 1
    if timing.unpaired then unpairedCount := unpairedCount + 1
  let compiled := files.size - skipped - compileFailures.size
  let failureNames := compileFailures.map (·.1)
  let unexpectedFailures := match known with
    | some allowed =>
        compileFailures.filter (fun (f : String × String) => !allowed.contains f.1)
    | none => compileFailures
  let staleKnown := match known with
    | some allowed =>
        allowed.filter (fun n => selected n && !failureNames.contains n)
    | none => #[]

  if update then
    unless lenient || unexpectedFailures.isEmpty do
      IO.eprintln "Contracts that failed to compile zeroImmutables (fix before pinning):"
      for (name, message) in unexpectedFailures do IO.eprintln s!"  {name}: {message}"
      return 1
    unless lenient || measurementFailures.isEmpty do
      IO.eprintln "Contracts with declared calls that could not be measured:"
      for (name, message) in measurementFailures do IO.eprintln s!"  {name}: {message}"
      return 1
    if !staleKnown.isEmpty then
      printNames "Stale known-compile-failure entries (remove after review):" staleKnown
      return 1
    let baselineKind :=
      if perScenario then "solidity-gas per external function"
      else "solidity-gas"
    IO.FS.writeFile baselineFile (render baselineKind expectedSolcVersion measured)
    IO.println s!"Compiled {compiled} contracts; re-pinned {measured.size} gas rows in {baselineFile}."
    return 0

  let baseline ← match ← readBaseline baselineFile with
    | .ok rows => pure (rows.filter (fun r => selected r.fixture))
    | .error message => IO.eprintln s!"{baselineFile}: {message}"; return 1
  let mut gasRegressions : Array String := #[]
  let mut gasImproved : Array String := #[]
  let mut gasChanged : Array String := #[]
  let mut gasUnpinned : Array String := #[]
  for row in measured do
    match find baseline row.fixture with
    | none => gasUnpinned := gasUnpinned.push row.fixture
    | some pinned =>
        let detail := s!"{row.fixture}: ours {row.ours} vs pinned {pinned.ours} (solc {row.solc})"
        match classify row pinned with
        | .regression => gasRegressions := gasRegressions.push detail
        | .improved => gasImproved := gasImproved.push detail
        | .changed => gasChanged := gasChanged.push s!"{row.fixture}: solc {row.solc} vs pinned {pinned.solc}"
        | .ok => pure ()
  let measuredNames := measured.map (·.fixture)
  let gasStale := (baseline.filter (fun r => !measuredNames.contains r.fixture)).map (·.fixture)

  let unsupported := if lenient || known.isSome then compileFailures.size else 0
  IO.println s!"Compiled {compiled}/{files.size - skipped} latest-fork contracts via solc {expectedSolcVersion} --via-ir (skipped {skipped}, unsupported {unsupported})."
  IO.println s!"Gas: {measured.size} comparable, {gasRegressions.size} regressions, {gasImproved.size} improved, {gasChanged.size} changed, {gasUnpinned.size} unpinned, {gasStale.size} stale."
  -- Machine-readable aggregate for the PR summary comment. `mode=vs_solc_optimized`:
  -- this compiler compiles solc's *unoptimized* IR while solc is fully optimized
  -- (`--optimize --via-ir`), so `ours/solc > 1` is expected until this compiler
  -- gains its own optimizer.
  let suite := dir.fileName.getD "gas"
  IO.println s!"Gas totals: suite={suite} mode=vs_solc_optimized ours={measured.foldl (fun a r => a + r.ours) 0} solc={measured.foldl (fun a r => a + r.solc) 0} comparable={measured.size}"
  -- Machine-readable compiler runtime for the PR summary comment: the summed
  -- per-fixture spans of each compiler on this suite (shard), so the summary can
  -- add shards up and diff head against main.
  --
  -- `ours_ms` and `solc_ms` are the same job on the same input — unoptimized Yul
  -- → bytecode — over the same `fixtures` contracts: only those *both* compilers
  -- finished are counted, on either side. Neither includes solc's Solidity→Yul
  -- front-end: that runs once, before both, and is reported apart as
  -- `frontend_ms`. `solc_ms` is therefore NOT the `--optimize --via-ir` compile
  -- the gas comparison runs, which would start from Solidity and add the Yul
  -- optimizer. The two uncounted buckets hold this compiler's time on contracts
  -- that never formed a pair: `rejected` ones it could not compile zeroImmutables itself, and
  -- `unpaired` ones it compiled but solc would not.
  IO.println s!"Compile time: suite={suite} mode=vs_solc_optimized ours_ms={toMs oursNs} solc_ms={toMs solcNs} frontend_ms={toMs frontendNs} fixtures={compiledCount} rejected_ms={toMs rejectedNs} rejected={rejectedCount} unpaired_ms={toMs unpairedNs} unpaired={unpairedCount}"
  -- Per-fixture rows let the PR summary compare a head run with a main run on
  -- their exact shared fixture set. Tabs are intentional: fixture paths may
  -- contain spaces, but Solidity corpus paths cannot contain tabs.
  for row in measured do
    IO.println s!"Gas row:\t{suite}\tvs_solc_optimized\t{row.fixture}\t{row.ours}\t{row.solc}"
  unless lenient || unexpectedFailures.isEmpty do
    IO.eprintln "Contracts this compiler failed to compile:"
    for (name, message) in unexpectedFailures do IO.eprintln s!"  {name}: {message}"
  unless lenient || measurementFailures.isEmpty do
    IO.eprintln "Contracts with declared calls that could not be measured:"
    for (name, message) in measurementFailures do IO.eprintln s!"  {name}: {message}"
  printNames "Stale known-compile-failure entries (remove after review):" staleKnown
  printNames "Gas improved — re-pin with scripts/update-gas.sh to tighten:" gasImproved
  printNames "Fixtures changed upstream/solc — re-pin with scripts/update-gas.sh:" gasChanged
  printNames "Gas-unpinned fixtures — re-pin with scripts/update-gas.sh:" gasUnpinned
  printNames "Stale gas entries — re-pin with scripts/update-gas.sh:" gasStale
  unless gasRegressions.isEmpty do
    IO.eprintln "GAS REGRESSIONS (this compiler now spends more gas):"
    for detail in gasRegressions do IO.eprintln s!"  {detail}"
  return if (lenient || (unexpectedFailures.isEmpty && measurementFailures.isEmpty)) &&
    staleKnown.isEmpty && gasRegressions.isEmpty && gasChanged.isEmpty &&
    gasUnpinned.isEmpty && gasStale.isEmpty then 0 else 1

def main (args : List String) : IO UInt32 := do
  match args with
  | "--yul-differential" :: rest => solcDifferentialMain rest
  | dir :: baselineFile :: solcPath :: expectedSolcVersion :: rest =>
      let flags := rest.filter (·.startsWith "--")
      let nums := rest.filter (fun s => !s.startsWith "--")
      let knownFiles := flags.filterMap (fun f =>
        if f.startsWith "--known=" then some ((f.drop "--known=".length).copy) else none)
      let cacheDirs := flags.filterMap (fun f =>
        if f.startsWith "--solc-cache=" then some ((f.drop "--solc-cache=".length).copy) else none)
      if !flags.all (fun f =>
          f == "--update" || f == "--lenient" || f == "--per-scenario" ||
            f.startsWith "--known=" || f.startsWith "--solc-cache=") then
        IO.eprintln usage; return 64
      else
        let known ← match knownFiles with
          | [] => pure none
          | [file] => some <$> readKnownFailures (FilePath.mk file)
          | _ => IO.eprintln usage; return 64
        let solcCache : Option FilePath := match cacheDirs with
          | [] => none
          | dir :: _ => some (FilePath.mk dir)
        let shard ← match nums with
          | [] => pure none
          | [rawIndex, rawCount] =>
              match rawIndex.toNat?, rawCount.toNat? with
              | some index, some count =>
                  if count == 0 || index >= count then
                    IO.eprintln "invalid shard"; return 64
                  else pure (some { index, count })
              | _, _ => IO.eprintln usage; return 64
          | _ => IO.eprintln usage; return 64
        run dir baselineFile solcPath expectedSolcVersion
          (flags.contains "--lenient") (flags.contains "--update")
          (flags.contains "--per-scenario") known shard solcCache
  | _ => IO.eprintln usage; return 64
