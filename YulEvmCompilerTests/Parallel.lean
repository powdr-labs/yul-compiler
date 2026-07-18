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

Items are dealt round-robin across `jobs` workers so cost spreads regardless of
where the expensive items sit. Each result carries its original index and the
whole thing is re-sorted at the end, so the output is deterministic and identical
to `items.mapM f` no matter how many workers run. Workers get dedicated threads
because each one blocks on a `solc` subprocess and must not tie up Lean's shared
task-pool threads. A worker error is re-raised on the caller. -/
def parMap {α β : Type} (jobs : Nat) (items : Array α) (f : α → IO β) : IO (Array β) := do
  if jobs ≤ 1 || items.size ≤ 1 then
    return ← items.mapM f
  let mut chunks : Array (Array (Nat × α)) := Array.replicate jobs #[]
  let mut i := 0
  for item in items do
    let worker := i % jobs
    chunks := chunks.set! worker (chunks[worker]!.push (i, item))
    i := i + 1
  let tasks ← chunks.mapM fun chunk =>
    IO.asTask (prio := Task.Priority.dedicated) <| chunk.mapM fun (idx, item) => do
      return (idx, ← f item)
  let mut indexed : Array (Nat × β) := #[]
  for task in tasks do
    match ← IO.wait task with
    | .ok rows => indexed := indexed ++ rows
    | .error err => throw err
  return (indexed.qsort (fun a b => a.1 < b.1)).map (·.2)

end YulEvmCompilerTests.Parallel
