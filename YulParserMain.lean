import YulParser.Compile
import YulEvmCompiler.CompileLive

set_option warningAsError true
/-!
# yulc

A minimal command-line entry point for parser/compiler differential testing.
In parse-only mode it accepts both brace-delimited programs and object-rooted
files. Compilation accepts either form and prints the assembled EVM bytecode
as lowercase hex.
-/

open YulParser YulEvmCompiler

private def outputHexDigits : Array Char :=
  #['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f']

private def byteHex (b : UInt8) : String :=
  let n := b.toNat
  String.ofList [outputHexDigits[n / 16]!, outputHexDigits[n % 16]!]

private def codeHex (code : ByteArray) : String :=
  String.join (code.data.toList.map byteHex)

private def usage : String :=
  "usage: yulc [--parse-only] [--libraries=NAME=ADDR[,NAME=ADDR…]] <file.yul>"

private def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (10 + c.toNat - 'a'.toNat)
  else if 'A' ≤ c && c ≤ 'F' then some (10 + c.toNat - 'A'.toNat)
  else none

private def parseAddress? (text : String) : Option Nat :=
  let digits := (if text.startsWith "0x" || text.startsWith "0X" then
    (text.drop 2).copy else text).toList
  if digits.isEmpty then none
  else digits.foldl (fun acc c => do
    let acc ← acc
    let d ← hexDigit? c
    some (16 * acc + d)) (some 0)

/-- Parse solc's `--libraries` spelling: `file.sol:Lib=0xADDR` entries, comma
separated. A library name may itself contain `:`, so split on the *last* `=`. -/
private def parseLibraries? (spec : String) : Option LinkEnv :=
  if spec.isEmpty then some [] else
  (spec.splitOn ",").foldr (fun entry acc => do
    let acc ← acc
    let parts := entry.splitOn "="
    match parts.reverse with
    | address :: rest@(_ :: _) =>
        let name := String.intercalate "=" rest.reverse
        if name.isEmpty then none else
        return (name.trimAscii.copy, ← parseAddress? address.trimAscii.copy) :: acc
    | _ => none) (some [])

-- TEMPORARY Phase-0 diagnostic (not for commit): peak simultaneously-live
-- locals per function, i.e. the stack pressure an eager-retirement backend
-- would need, versus what the current declaration-order layout holds.
section LiveDiag
open YulSemantics YulSemantics.EVM

private def ins (x : Ident) (xs : List Ident) : List Ident :=
  if xs.contains x then xs else x :: xs

private def uni : List Ident → List Ident → List Ident
  | [], ys => ys
  | x :: xs, ys => uni xs (ins x ys)

private def del : List Ident → List Ident → List Ident
  | [], ys => ys
  | x :: xs, ys => del xs (ys.filter (· != x))

private partial def eVars : Expr Op → List Ident
  | .lit _ => []
  | .var x => [x]
  | .builtin _ args => args.foldl (fun acc e => uni (eVars e) acc) []
  | .call _ args => args.foldl (fun acc e => uni (eVars e) acc) []

mutual
/-- Backward liveness over a statement list. Returns `(peak, liveIn)` where
`peak` is the largest live set seen at any statement boundary inside. -/
private partial def lvStmts : List (Stmt Op) → List Ident → Nat × List Ident
  | [], out => (out.length, out)
  | s :: rest, out =>
      let (pr, mid) := lvStmts rest out
      let (ps, lin) := lvStmt s mid
      (max pr (max ps (max mid.length lin.length)), lin)

private partial def lvStmt : Stmt Op → List Ident → Nat × List Ident
  | .block body, out => lvStmts body out
  -- A nested function definition has its own frame; it does not contribute
  -- pressure to the enclosing one.
  | .funDef _ _ _ _, out => (out.length, out)
  | .letDecl xs val, out =>
      let after := del xs out
      (out.length, match val with | some e => uni (eVars e) after | none => after)
  | .assign xs val, out => (out.length, uni (eVars val) (del xs out))
  | .exprStmt e, out => (out.length, uni (eVars e) out)
  | .cond c body, out =>
      let (pb, lb) := lvStmts body out
      (max pb out.length, uni (eVars c) (uni lb out))
  | .switch c cases dflt, out =>
      let (pc, lc) := cases.foldl
        (fun (acc : Nat × List Ident) cb =>
          let (p, l) := lvStmts cb.2 out
          (max acc.1 p, uni l acc.2)) (out.length, out)
      let (pd, ld) := match dflt with
        | some b => lvStmts b out
        | none => (out.length, out)
      (max pc pd, uni (eVars c) (uni lc ld))
  -- One extra round approximates the loop fixpoint: anything read anywhere in
  -- the loop is treated as live throughout it.
  | .forLoop init c post body, out =>
      let (pb, lb) := lvStmts body out
      let (pp, lp) := lvStmts post (uni lb out)
      let cond := uni (eVars c) (uni lp (uni lb out))
      let (pb2, lb2) := lvStmts body cond
      let (pp2, lp2) := lvStmts post (uni lb2 cond)
      let (pi, li) := lvStmts init (uni (eVars c) (uni lp2 (uni lb2 cond)))
      (max pi (max (max pb pp) (max pb2 pp2)), li)
  | .break, out => (out.length, out)
  | .continue, out => (out.length, out)
  | .leave, out => (out.length, out)
end

/-- Peak live locals for one function body, counting its return variables as
live throughout (the epilogue reads them). -/
private def funPeak (ps rs : List Ident) (body : List (Stmt Op)) : Nat :=
  let (p, _) := lvStmts body rs
  max p (ps.length + rs.length)

private partial def collectFuns : List (Stmt Op) → List (Ident × Nat × Nat × Nat)
  | [] => []
  | .funDef f ps rs body :: rest =>
      (f, ps.length, rs.length, funPeak ps rs body) :: collectFuns rest
  | _ :: rest => collectFuns rest

private partial def flatObjs (o : YulSemantics.Object Op) (tag : String) :
    List (String × YulSemantics.Object Op) :=
  (tag, o) :: (o.subObjects.flatMap (fun s => flatObjs s (tag ++ ".")))

end LiveDiag

open YulEvmCompiler YulEvmCompiler.Optimizer in
private def liveDiag (path : String) : IO UInt32 := do
  let source ← IO.FS.readFile path
  let calls := YulSemantics.EVM.ExternalCalls.none
  let creates := YulSemantics.EVM.ExternalCreates.none
  let some src := parseSource source | do IO.println "parse failed"; return 1
  let o0 ← match src with
    | .object o => pure o
    | .block b => pure (YulSemantics.Object.mk "block" b [] [])
  let raw := pruneLinkerObjectTree (decodeValueObject o0)
  let o := Normalize.normalizeObject
    (D := YulSemantics.EVM.evmWithExternal calls creates) (desugarObject raw)
  for (tag, obj) in flatObjs o "obj" do
    let funs := collectFuns obj.codeBlock
    let worst := (funs.map (fun f => f.2.2.2)).foldl max 0
    let over := funs.filter (fun f => f.2.2.2 + 2 ≥ 16)
    IO.println s!"--- {tag} \"{obj.name}\": {funs.length} functions"
    IO.println s!"    peak live locals, worst function : {worst}"
    IO.println s!"    functions whose peak+2 reaches 16: {over.length}"
    for f in (over.toArray.qsort (fun a b => a.2.2.2 > b.2.2.2)).toList.take 8 do
      IO.println s!"      peak={f.2.2.2} p={f.2.1} r={f.2.2.1}  {f.1}"
  return 0


-- TEMPORARY: per-code-block feasibility of last-use retirement vs the current
-- layout. `dataoffset`/`datasize` are stubbed to 0, mirroring ObjectCompile's
-- private `placeholderResolver`, so blocks are comparable to what `planObject`
-- actually hands the backend.
section LiveCompile
open YulSemantics YulSemantics.EVM

mutual
private partial def stubE : Expr Op → Expr Op
  | .lit l => .lit l
  | .var x => .var x
  | .builtin op args =>
      if op == Op.datasize || op == Op.dataoffset then .lit (.number 0)
      else .builtin op (stubA args)
  | .call f args => .call f (stubA args)
private partial def stubA : List (Expr Op) → List (Expr Op)
  | [] => []
  | e :: r => stubE e :: stubA r
end

mutual
private partial def stubS : Stmt Op → Stmt Op
  | .exprStmt e => .exprStmt (stubE e)
  | .letDecl xs v => .letDecl xs (v.map stubE)
  | .assign xs e => .assign xs (stubE e)
  | .block b => .block (stubSs b)
  | .cond c b => .cond (stubE c) (stubSs b)
  | .funDef f p r b => .funDef f p r (stubSs b)
  | .forLoop i c po b => .forLoop (stubSs i) (stubE c) (stubSs po) (stubSs b)
  | .switch c cs d =>
      .switch (stubE c) (cs.map (fun cb => (cb.1, stubSs cb.2)))
        (d.map stubSs)
  | .break => .break
  | .continue => .continue
  | .leave => .leave
private partial def stubSs : List (Stmt Op) → List (Stmt Op)
  | [] => []
  | s :: r => stubS s :: stubSs r
end

end LiveCompile

open YulEvmCompiler YulEvmCompiler.Optimizer in
private def liveCompile (path : String) : IO UInt32 := do
  let source ← IO.FS.readFile path
  let calls := YulSemantics.EVM.ExternalCalls.none
  let creates := YulSemantics.EVM.ExternalCreates.none
  let some src := parseSource source | do IO.println "parse failed"; return 1
  let o0 ← match src with
    | .object o => pure o
    | .block b => pure (YulSemantics.Object.mk "block" b [] [])
  let raw := pruneLinkerObjectTree (decodeValueObject o0)
  let o := Normalize.normalizeObject
    (D := YulSemantics.EVM.evmWithExternal calls creates) (desugarObject raw)
  let opt := optimizerPipelineObject (calls := calls) (creates := creates) o
  for (tag, obj) in flatObjs o "raw" do
    let blk := stubSs obj.codeBlock
    let t0 ← IO.monoNanosNow
    let base := (compile blk).isSome
    let t1 ← IO.monoNanosNow
    let live := (compileLive blk).isSome
    let t2 ← IO.monoNanosNow
    IO.println s!"{tag} \"{obj.name}\"  compile={base} ({(t1-t0)/1000000} ms)  compileLive={live} ({(t2-t1)/1000000} ms)"
  IO.println "--- combinations on the optimizer-pipeline output ---"
  let sl := stackLayoutObject opt
  let cl := cleanupAfterLayoutObject (calls := calls) (creates := creates) sl
  for (tag, obj) in flatObjs opt "opt" do
    let blk := stubSs obj.codeBlock
    let t0 ← IO.monoNanosNow
    let live := (compileLive blk).isSome
    let t1 ← IO.monoNanosNow
    IO.println s!"{tag} \"{obj.name}\"  compile={(compile blk).isSome}  compileLive={live} ({(t1-t0)/1000000} ms)"
  for (tag, obj) in flatObjs sl "layout" do
    let blk := stubSs obj.codeBlock
    let t0 ← IO.monoNanosNow
    let live := (compileLive blk).isSome
    let t1 ← IO.monoNanosNow
    IO.println s!"{tag} \"{obj.name}\"  compile={(compile blk).isSome}  compileLive={live} ({(t1-t0)/1000000} ms)"
  for (tag, obj) in flatObjs cl "layout+cleanup" do
    let blk := stubSs obj.codeBlock
    let t0 ← IO.monoNanosNow
    let live := (compileLive blk).isSome
    let t1 ← IO.monoNanosNow
    IO.println s!"{tag} \"{obj.name}\"  compile={(compile blk).isSome}  compileLive={live} ({(t1-t0)/1000000} ms)"
  return 0

private def runFile (path : String) (parseOnly : Bool)
    (libraries : LinkEnv := []) : IO UInt32 := do
  let source ← IO.FS.readFile path
  if parseOnly then
    if (parseSource source).isSome then
      return 0
    else
      IO.eprintln s!"{path}: parse failed"
      return 1
  match compileSource source libraries with
  | none =>
      match parseSource source with
      | none =>
          IO.eprintln s!"{path}: parse failed"
          return 1
      | some _ =>
          IO.eprintln s!"{path}: parsed, but uses unsupported compiler features"
          return 2
  | some code =>
      IO.println (codeHex code)
      return 0

def main (args : List String) : IO UInt32 := do
  let parseOnly := args.contains "--parse-only"
  let libSpecs := args.filterMap fun arg =>
    if arg.startsWith "--libraries=" then
      some (arg.drop "--libraries=".length).copy
    else none
  let positional := args.filter fun arg => !arg.startsWith "--"
  match positional, libSpecs.mapM parseLibraries? with
  | [path], some libraries =>
      if args.contains "--livec" then liveCompile path
      else if args.contains "--live" then liveDiag path
      else runFile path parseOnly libraries.flatten
  | _, none => do
      IO.eprintln "yulc: malformed --libraries (expected NAME=0xADDR[,…])"
      return 64
  | _, _ => do
      IO.eprintln usage
      return 64
