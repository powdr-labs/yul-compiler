import YulParser.Compile
import YulSemantics.PrettyPrint
/-!
Inliner gate diagnosis (scratch, untracked). For a solc --ir object file:
dump the post-pipeline Yul, then for every surviving function report why the
inliner passes decline it: classifyDecl / inlineOK components, and for every
call site the siteOK conjunct that fails (or that the site shape is
unreachable, e.g. nested in an expression).
-/

open YulSemantics YulSemantics.EVM YulParser
open YulEvmCompiler.Optimizer

abbrev St := Stmt EVM.Op
abbrev Ex := Expr EVM.Op

/-- All funDefs in a statement tree (name, ps, rs, body), recursively. -/
partial def allFunDefs : List St → List (Ident × List Ident × List Ident × List St)
  | [] => []
  | .funDef f ps rs body :: rest =>
      (f, ps, rs, body) :: allFunDefs body ++ allFunDefs rest
  | .block b :: rest => allFunDefs b ++ allFunDefs rest
  | .cond _ b :: rest => allFunDefs b ++ allFunDefs rest
  | .switch _ cs d :: rest =>
      (cs.flatMap (allFunDefs ·.2)) ++ (d.map allFunDefs).getD [] ++ allFunDefs rest
  | .forLoop i _ p b :: rest =>
      allFunDefs i ++ allFunDefs p ++ allFunDefs b ++ allFunDefs rest
  | _ :: rest => allFunDefs rest

/-- Call sites: (callee, xs, args, shape) where shape describes reachability
for InlineCalls. Nested-in-expression calls are collected as "nested". -/
partial def exprCalls : Ex → List (Ident × List Ex)
  | .call f as => (f, as) :: as.flatMap exprCalls
  | .builtin _ as => as.flatMap exprCalls
  | _ => []

partial def callSites : List St → List (Ident × List Ident × List Ex × String)
  | [] => []
  | .letDecl xs (some (.call f as)) :: rest =>
      (f, xs, as, "let") :: (as.flatMap exprCalls).map (fun (g, gs) => (g, [], gs, "nested"))
        ++ callSites rest
  | .letDecl _ (some e) :: rest =>
      (exprCalls e).map (fun (g, gs) => (g, [], gs, "nested")) ++ callSites rest
  | .letDecl _ none :: rest => callSites rest
  | .assign xs (.call f as) :: rest =>
      (f, xs, as, "assign") :: (as.flatMap exprCalls).map (fun (g, gs) => (g, [], gs, "nested"))
        ++ callSites rest
  | .assign _ e :: rest =>
      (exprCalls e).map (fun (g, gs) => (g, [], gs, "nested")) ++ callSites rest
  | .exprStmt (.call f as) :: rest =>
      (f, [], as, "stmt") :: (as.flatMap exprCalls).map (fun (g, gs) => (g, [], gs, "nested"))
        ++ callSites rest
  | .exprStmt e :: rest =>
      (exprCalls e).map (fun (g, gs) => (g, [], gs, "nested")) ++ callSites rest
  | .funDef _ _ _ body :: rest => callSites body ++ callSites rest
  | .block b :: rest => callSites b ++ callSites rest
  | .cond c b :: rest =>
      (exprCalls c).map (fun (g, gs) => (g, [], gs, "cond-expr")) ++ callSites b ++ callSites rest
  | .switch c cs d :: rest =>
      (exprCalls c).map (fun (g, gs) => (g, [], gs, "switch-expr"))
        ++ cs.flatMap (fun cb => callSites cb.2) ++ (d.map callSites).getD []
        ++ callSites rest
  | .forLoop i c p b :: rest =>
      callSites i ++ (exprCalls c).map (fun (g, gs) => (g, [], gs, "for-cond"))
        ++ callSites p ++ callSites b ++ callSites rest
  | _ :: rest => callSites rest

/-- Why does classifyDecl reject / what are inlineOK components? -/
def declReport (f : Ident) (ps rs : List Ident) (body : List St) : String :=
  let dropped := dropTrailingLeave body
  let nodup := decide (ps ++ rs).Nodup
  let scopedOK := scopedStmts (ps ++ rs) dropped
  match classifyDecl ps rs body with
  | none =>
      s!"{f}: NOT-CLASSIFIED nodup={nodup} scoped={scopedOK} (ps={ps.length} rs={rs.length} stmts={body.length})"
  | some d =>
      let lm := liveMaxStmts (d.ps.length + d.rs.length) d.ss
      let ok := inlineOK d
      s!"{f}: classified rets={d.rs.length} liveMax={lm} inlineOK={ok}"

def siteReport (Δ : DEnv) (f : Ident) (xs : List Ident) (as : List Ex) (shape : String) : String :=
  match lookupDelta Δ f with
  | none => s!"  site {f} [{shape}]: callee not in DEnv"
  | some d =>
      if shape == "nested" || shape == "cond-expr" || shape == "switch-expr" || shape == "for-cond" then
        s!"  site {f} [{shape}]: UNREACHABLE-SHAPE for InlineCalls"
      else
        let isLet := shape == "let"
        let c1 := as.length == d.ps.length && xs.length == d.rs.length && decide xs.Nodup
        let c2 := !argsHaveCall as
        let c3 := argsShadowOK d.rs (d.ps.zip as)
        let c4 := xs.all (fun v => !(d.ps ++ d.rs).contains v)
        let c5 := (!isLet || (varsList as).all (fun v => !xs.contains v))
        let ok := inlineOK d
        s!"  site {f} [{shape}]: inlineOK={ok} arity/nodup={c1} argsNoCall={c2} shadowOK={c3} xsFresh={c4} letNoRead={c5}"

def main (args : List String) : IO Unit := do
  let [path] := args | IO.eprintln "usage: diag <object.yul>" *> return
  let source ← IO.FS.readFile path
  match debugPipelineObject source with
  | none => IO.eprintln "parse/preprocess failed"
  | some (_pre, post) =>
      -- dump optimized Yul
      IO.FS.writeFile (path ++ ".opt") (YulSemantics.ppObject EVM.opName 0 post)
      let rec collect : Object EVM.Op → List (String × List St)
        | .mk n code subs _ => (n, code) :: subs.flatMap collect
      for (objName, code) in collect post do
        let funs := allFunDefs code
        IO.println s!"### object {objName}: {funs.length} surviving functions after pipeline"
        for (f, ps, rs, body) in funs do
          IO.println (declReport f ps rs body)
        IO.println ""
        IO.println "--- call sites of surviving functions ---"
        let Δ := deltaExtend [] code
        let sites := callSites code
        let survivorNames := funs.map (·.1)
        for (f, xs, as, shape) in sites do
          if survivorNames.contains f then
            IO.println (siteReport Δ f xs as shape)
        IO.println ""
