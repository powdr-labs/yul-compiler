set_option warningAsError true
/-! Bounded, deterministic parallelism for the corpus test runners.

The Solidity corpus runners spend nearly all their wall-clock in per-fixture
work that is independent across fixtures — compiling with this compiler, shelling
out to `solc`, and executing the resulting bytecode. Running them one at a time
leaves every core but one idle. `parMap` fans the work out across worker threads
while keeping the result order (and therefore the run's verdict and logs)
identical to a sequential pass, so parallelism never changes which tests run or
what they report.
-/

namespace YulEvmCompilerTests.Parallel

/-- Degree of parallelism to use: `TEST_JOBS` if set, otherwise the machine's
core count (`nproc`), falling back to 4 if that cannot be determined. The runners
are CPU-bound per fixture, so one worker per core is the right ceiling. -/
def detectJobs : IO Nat := do
  match ← IO.getEnv "TEST_JOBS" with
  | some raw => return max 1 (raw.trimAscii.toString.toNat?.getD 4)
  | none =>
      try
        let out ← IO.Process.output { cmd := "nproc" }
        return max 1 (out.stdout.trimAscii.toString.toNat?.getD 4)
      catch _ => return 4

/-- Map `f` over `items` with up to `jobs` concurrent dedicated-thread workers,
returning the results in the original input order.

Workers take the next unclaimed item from an atomic counter. This dynamic queue
keeps short workers busy when another worker receives an unusually expensive
fixture. Each result carries its original index and the whole thing is re-sorted
at the end, so the output is deterministic and identical to `items.mapM f` no
matter how many workers run. Workers get dedicated threads because each one
blocks on a `solc` subprocess and must not tie up Lean's shared task-pool
threads. A worker error is re-raised on the caller. -/
def parMap {α β : Type} (jobs : Nat) (items : Array α) (f : α → IO β) : IO (Array β) := do
  if jobs ≤ 1 || items.size ≤ 1 then
    return ← items.mapM f
  let next ← IO.mkRef 0
  let workerCount := min jobs items.size
  let tasks ← (Array.range workerCount).mapM fun _ =>
    IO.asTask (prio := Task.Priority.dedicated) <| do
      let mut rows : Array (Nat × β) := #[]
      let mut done := false
      while !done do
        let idx ← next.modifyGet fun idx => (idx, idx + 1)
        if h : idx < items.size then
          rows := rows.push (idx, ← f items[idx])
        else
          done := true
      return rows
  let mut indexed : Array (Nat × β) := #[]
  for task in tasks do
    match ← IO.wait task with
    | .ok rows => indexed := indexed ++ rows
    | .error err => throw err
  return (indexed.qsort (fun a b => a.1 < b.1)).map (·.2)

private structure WeightedItem (α : Type) where
  index : Nat
  weight : Nat

/-- Deterministically divide `items` into `shardCount` shards by greedily
assigning the heaviest remaining item to the currently lightest shard.

The returned shard retains the input order. CI uses source byte size as a cheap,
stable approximation of fixture cost; this avoids the severe stragglers caused
by hashing a few very large fixtures into the same shard. -/
def weightedShard {α : Type} (shardIndex shardCount : Nat) (items : Array α)
    (weight : α → IO Nat) : IO (Array α) := do
  if shardCount == 0 || shardIndex >= shardCount then
    throw <| IO.userError "invalid weighted shard"
  let mut weighted : Array (WeightedItem α) := #[]
  for h : i in [:items.size] do
    weighted := weighted.push { index := i, weight := max 1 (← weight items[i]) }
  weighted := weighted.qsort fun a b =>
    a.weight > b.weight || (a.weight == b.weight && a.index < b.index)
  let mut loads := Array.replicate shardCount 0
  let mut owners := Array.replicate items.size 0
  for entry in weighted do
    let mut owner := 0
    for h : i in [1:shardCount] do
      if loads[i]! < loads[owner]! then owner := i
    loads := loads.modify owner (· + entry.weight)
    owners := owners.set! entry.index owner
  let mut selected : Array α := #[]
  for h : i in [:items.size] do
    if owners[i]! == shardIndex then selected := selected.push items[i]
  return selected

end YulEvmCompilerTests.Parallel
