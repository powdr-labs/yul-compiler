import YulEvmCompiler.Optimizer.Implementation.Normalization.Disambiguate.Basic
import YulEvmCompiler.Optimizer.Implementation.Normalization.NormalForm
set_option warningAsError true
/-!
# A collision-only, Solidity-style disambiguator (`RenameNumeric`)

The verified `Disambiguate.disambiguate` renames **every** declared name to a
reserved `dsName k = "\0v…v"` (leading `NUL`). That has two downsides the
`NUL`-namespace trick is paying for: the names are **non-printable** (not valid
Yul), and it renames names that never actually collide.

This module is an alternative **executable** disambiguator that mirrors
Solidity's `--via-ir` scheme instead:

* **collision-only** — a declared name is kept as-is unless it is already taken
  in the output; only then is it renamed;
* **printable numeric suffix** — a renamed `x` becomes `x_1`, `x_2`, … (the
  smallest suffix not already present anywhere in the program), never a `NUL`
  name;
* **program-fresh** — fresh names avoid *all* identifiers occurring in the
  source (`allIdents`), so a generated `x_7` never captures a real `x_7`.

Like the verified pass it produces globally unique declared names
(`NormalForm.UniqueNames`), so it is a drop-in *algorithm* for the same job. It
is provided as a runnable transform (see the `#guard`/`#eval` demos at the end);
**semantic soundness (`RunEquivBlock`) is not yet proved for it** — that is the
remaining work to make it a verified `GlobalPass` (the α-simulation would be
re-derived over program-fresh names, per `Disambiguate/Pass.lean`'s "generalize"
note). Until then the verified `disambiguate` remains the pipeline default.
-/

namespace YulEvmCompiler.Optimizer.RenameNumeric

open YulSemantics
open YulEvmCompiler.Optimizer.Normalize (substOf funNames)

variable {Op : Type}

/-! ### Fresh names -/

/-- Search for the smallest `base_k` (k ≥ 1) not in `avoid`. `fuel` bounds the
search; with `fuel = avoid.length + 1` a free name always exists. -/
def freshAux (base : Ident) (avoid : List Ident) : Nat → Nat → Ident
  | 0, k => base ++ "_" ++ toString k
  | fuel + 1, k =>
      let c := base ++ "_" ++ toString k
      if c ∈ avoid then freshAux base avoid fuel (k + 1) else c

/-- The smallest printable `base_k` suffix not occurring in `avoid`. -/
def freshName (avoid : List Ident) (base : Ident) : Ident :=
  freshAux base avoid (avoid.length + 1) 1

/-- Assign an output name to one declared name: keep it if free, else pick a
fresh numeric suffix. Returns the chosen name, the substitution entry to add
(empty when kept), and the extended `taken` set. -/
def assignName (orig taken : List Ident) (x : Ident) :
    Ident × List (Ident × Ident) × List Ident :=
  if x ∈ taken then
    let x' := freshName (taken ++ orig) x
    (x', [(x, x')], x' :: taken)
  else
    (x, [], x :: taken)

/-- Assign output names to a list of declared names, threading `taken`. -/
def assignNames (orig : List Ident) :
    List Ident → List Ident → List Ident × List (Ident × Ident) × List Ident
  | [], taken => ([], [], taken)
  | x :: xs, taken =>
      let (x', sub, taken1) := assignName orig taken x
      let (xs', subs, taken2) := assignNames orig xs taken1
      (x' :: xs', sub ++ subs, taken2)

/-! ### Collecting all identifiers (the avoidance set) -/

mutual
def identsE : Expr Op → List Ident
  | .lit _ => []
  | .var x => [x]
  | .builtin _ args => identsA args
  | .call fn args => fn :: identsA args
def identsA : List (Expr Op) → List Ident
  | [] => []
  | e :: rest => identsE e ++ identsA rest
end

mutual
def identsS : Stmt Op → List Ident
  | .letDecl vars val => vars ++ (val.map identsE).getD []
  | .assign vars val => vars ++ identsE val
  | .exprStmt e => identsE e
  | .block body => identsSs body
  | .cond c body => identsE c ++ identsSs body
  | .switch c cases dflt =>
      identsE c ++ identsCs cases ++ (match dflt with | none => [] | some b => identsSs b)
  | .funDef fn ps rs body => fn :: (ps ++ rs ++ identsSs body)
  | .forLoop init c post body => identsSs init ++ identsE c ++ identsSs post ++ identsSs body
  | _ => []
def identsSs : List (Stmt Op) → List Ident
  | [] => []
  | s :: rest => identsS s ++ identsSs rest
def identsCs : List (Literal × List (Stmt Op)) → List Ident
  | [] => []
  | (_, body) :: rest => identsSs body ++ identsCs rest
end

/-- Every identifier occurring anywhere in the program (declared or referenced),
so fresh names can avoid all of them. -/
def allIdents (b : Block Op) : List Ident := identsSs b

/-! ### The renaming traversal

Threaded state: variable and function substitutions (`σv`, `σf`, innermost
first) plus the monotone global `taken` set. `orig` is fixed. Blocks discard
their local substitutions on exit (only `taken` leaks); a `for`-init's scope
leaks into its condition/post/body, exactly like the verified pass. -/

structure St where
  σv : List (Ident × Ident)
  σf : List (Ident × Ident)

mutual
def renExpr (st : St) : Expr Op → Expr Op
  | .lit l => .lit l
  | .var x => .var (substOf st.σv x)
  | .builtin op args => .builtin op (renArgs st args)
  | .call fn args => .call (substOf st.σf fn) (renArgs st args)
def renArgs (st : St) : List (Expr Op) → List (Expr Op)
  | [] => []
  | e :: rest => renExpr st e :: renArgs st rest
end

mutual
def renStmt (orig : List Ident) (st : St) (taken : List Ident) :
    Stmt Op → St × List Ident × Stmt Op
  | .letDecl vars val =>
      let (vars', vsub, taken1) := assignNames orig vars taken
      ({ st with σv := vsub ++ st.σv }, taken1, .letDecl vars' (val.map (renExpr st)))
  | .assign vars val =>
      (st, taken, .assign (vars.map (substOf st.σv)) (renExpr st val))
  | .exprStmt e => (st, taken, .exprStmt (renExpr st e))
  | .block body =>
      let r := renScope orig st taken body
      (st, r.2.1, .block r.2.2)
  | .cond c body =>
      let r := renScope orig st taken body
      (st, r.2.1, .cond (renExpr st c) r.2.2)
  | .switch c cases dflt =>
      let rc := renCases orig st taken cases
      let rd := renDflt orig st rc.1 dflt
      (st, rd.1, .switch (renExpr st c) rc.2 rd.2)
  | .funDef fname params rets body =>
      let (params', psub, takenP) := assignNames orig params taken
      let (rets', rsub, takenR) := assignNames orig rets takenP
      let stBody : St := { st with σv := rsub ++ psub ++ st.σv }
      let r := renScope orig stBody takenR body
      (st, r.2.1, .funDef (substOf st.σf fname) params' rets' r.2.2)
  | .forLoop init c post body =>
      let ri := renScope orig st taken init
      let rb := renScope orig ri.1 ri.2.1 body
      let rp := renScope orig ri.1 rb.2.1 post
      (st, rp.2.1, .forLoop ri.2.2 (renExpr ri.1 c) rp.2.2 rb.2.2)
  | .«break» => (st, taken, .«break»)
  | .«continue» => (st, taken, .«continue»)
  | .leave => (st, taken, .leave)
def renStmts (orig : List Ident) (st : St) (taken : List Ident) :
    List (Stmt Op) → St × List Ident × List (Stmt Op)
  | [] => (st, taken, [])
  | s :: rest =>
      let r := renStmt orig st taken s
      let rs := renStmts orig r.1 r.2.1 rest
      (rs.1, rs.2.1, r.2.2 :: rs.2.2)
/-- A lexical scope: prescan and assign its top-level function names (so forward
references resolve), then rename its statements. -/
def renScope (orig : List Ident) (st : St) (taken : List Ident) (body : List (Stmt Op)) :
    St × List Ident × List (Stmt Op) :=
  let (_, fsub, taken1) := assignNames orig (funNames body) taken
  renStmts orig { st with σf := fsub ++ st.σf } taken1 body
def renCases (orig : List Ident) (st : St) (taken : List Ident) :
    List (Literal × List (Stmt Op)) → List Ident × List (Literal × List (Stmt Op))
  | [] => (taken, [])
  | (l, body) :: rest =>
      let r := renScope orig st taken body
      let rs := renCases orig st r.2.1 rest
      (rs.1, (l, r.2.2) :: rs.2)
def renDflt (orig : List Ident) (st : St) (taken : List Ident) :
    Option (List (Stmt Op)) → List Ident × Option (List (Stmt Op))
  | none => (taken, none)
  | some body =>
      let r := renScope orig st taken body
      (r.2.1, some r.2.2)
end

/-- **Collision-only numeric disambiguation.** Rename declared names to printable
`x_k` suffixes only where they collide; keep everything else unchanged. -/
def rename (b : Block Op) : Block Op :=
  (renScope (allIdents b) { σv := [], σf := [] } [] b).2.2

/-! ### Runner / demos

Build-time checks that the transform behaves as advertised on sample programs
(this section is the runnable "runner"; `#eval` prints before/after). -/

section Demo
open YulSemantics
open YulEvmCompiler.Optimizer.NormalForm (UniqueNames declaredNamesStmts)

-- Demos use `Unit` as the (irrelevant) built-in op type; the renamer is dialect-generic.

/-- No collisions: two distinct locals — should be returned **unchanged**. -/
def exNoCollision : Block Unit :=
  [ .letDecl ["x"] (some (.lit (.number 1))),
    .letDecl ["y"] (some (.var "x")) ]

/-- Shadowing: an inner `x` shadows an outer `x`. -/
def exShadow : Block Unit :=
  [ .letDecl ["x"] (some (.lit (.number 1))),
    .block
      [ .letDecl ["x"] (some (.lit (.number 2))),
        .assign ["x"] (.var "x") ] ]

/-- Two sibling scopes each reusing the name `x` (valid Yul — distinct scopes). -/
def exSiblings : Block Unit :=
  [ .block [ .letDecl ["x"] (some (.lit (.number 1))) ],
    .block [ .letDecl ["x"] (some (.lit (.number 2))) ] ]

-- Collision-only: with no collision, no declared name changes.
#guard declaredNamesStmts (rename exNoCollision) = declaredNamesStmts exNoCollision

-- Output is globally uniquely-declared (the `UniqueNames` goal), in every case.
#guard (declaredNamesStmts (rename exNoCollision)).Nodup
#guard (declaredNamesStmts (rename exShadow)).Nodup
#guard (declaredNamesStmts (rename exSiblings)).Nodup

-- Output identifiers are printable (no `NUL`), unlike the verified pass.
#guard (allIdents (rename exShadow)).all (fun s => !s.toList.contains (Char.ofNat 0))
#guard (allIdents (rename exSiblings)).all (fun s => !s.toList.contains (Char.ofNat 0))

-- The shadowed inner `x` became `x_1`; the outer `x` is kept.
#guard "x" ∈ allIdents (rename exShadow)
#guard "x_1" ∈ allIdents (rename exShadow)

-- Visual before/after.
#eval IO.println (repr (rename exShadow))
#eval IO.println (repr (rename exSiblings))

end Demo

end YulEvmCompiler.Optimizer.RenameNumeric
