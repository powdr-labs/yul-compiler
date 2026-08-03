import YulEvmCompiler.Optimizer.Implementation.InlineCalls
import YulEvmCompiler.Optimizer.Implementation.ObjectPass
set_option warningAsError false
/-!
# InlineCallsCarry — call-carrying statement inliner (PROTOTYPE, unproven)

`InlineCalls` requires callee bodies to be *call-free* (`scopedExpr` rejects
any user call), so the leaf-first collapse stalls the moment one function in a
chain legitimately survives (a big math body over the `liveMax` bound, or a
multi-return decoder): every ancestor wrapper in the call chain is then pinned
out of line, paying full call protocol at each level. Diagnosed on
`FullMath.sol`: `fun_mulDiv` is a four-statement forwarding wrapper
(`r := 0; let t := impl(a,b,c); r := t; leave`) kept out of line only because
its body *contains a call*.

This pass inlines small call-**bearing** bodies and simply carries their inner
calls to the transplant site (solc FullInliner semantics). Function references
stay valid: Yul functions are visible throughout their defining block chain,
and the callee is a sibling of (or in an enclosing scope of) every call site
the pass rewrites.

Duplication and pressure gates: body ≤ `carryMaxStmts` statements, at most
`carryMaxCalls` carried calls, no self-recursion, and the shared `liveMax`
stack bound. Bodies the plain (call-free) classifier already accepts are left
to `InlineCalls`.

**Soundness is deliberately `sorry`ed** (`set_option warningAsError false`):
this is a measurement prototype. If it pays, the proof follows the
`InlineCallsSound` skeleton with a function-environment agreement argument for
the carried calls.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM

variable {calls : ExternalCalls} {creates : ExternalCreates}

local notation "D" => evmWithExternal calls creates

/-! ### Carry-scoped well-formedness: `scopedStmt` minus the call-free rule -/

/-- Like `scopedExpr` without `!exprHasCall`: every variable read must be
bound, calls are allowed (their arguments are checked recursively via
`exprVars`). -/
def carryExpr (bound : List Ident) (e : Expr Op) : Bool :=
  (exprVars e).all bound.contains

mutual

def carryStmt (bound : List Ident) : Stmt Op → Option (List Ident)
  | .letDecl xs none => some (xs ++ bound)
  | .letDecl xs (some e) =>
      if carryExpr bound e then some (xs ++ bound) else none
  | .assign xs e =>
      if xs.all bound.contains && carryExpr bound e then some bound else none
  | .exprStmt e => if carryExpr bound e then some bound else none
  | .block body => if carryStmts bound body then some bound else none
  | .cond c body =>
      if carryExpr bound c && carryStmts bound body then some bound else none
  | .switch c cases dflt =>
      if carryExpr bound c && carryCases bound cases && carryDflt bound dflt
      then some bound else none
  | .funDef _ _ _ _ => none
  | .forLoop _ _ _ _ => none
  | .break => none
  | .continue => none
  | .leave => none

def carryStmts (bound : List Ident) : List (Stmt Op) → Bool
  | [] => true
  | s :: rest =>
      match carryStmt bound s with
      | some bound' => carryStmts bound' rest
      | none => false

def carryCases (bound : List Ident) : List (Literal × Block Op) → Bool
  | [] => true
  | (_, b) :: rest => carryStmts bound b && carryCases bound rest

def carryDflt (bound : List Ident) : Option (Block Op) → Bool
  | none => true
  | some b => carryStmts bound b

end

/-! ### Duplication gates -/

/-- User calls contained in an expression. -/
partial def exprCallNames : Expr Op → List Ident
  | .call f as => f :: (as.flatMap exprCallNames)
  | .builtin _ as => as.flatMap exprCallNames
  | _ => []

/-- User calls contained in a statement list (function bodies excluded: a
carry-classified body contains no `funDef`). -/
partial def stmtsCallNames : List (Stmt Op) → List Ident
  | [] => []
  | .letDecl _ (some e) :: rest => exprCallNames e ++ stmtsCallNames rest
  | .letDecl _ none :: rest => stmtsCallNames rest
  | .assign _ e :: rest => exprCallNames e ++ stmtsCallNames rest
  | .exprStmt e :: rest => exprCallNames e ++ stmtsCallNames rest
  | .block b :: rest => stmtsCallNames b ++ stmtsCallNames rest
  | .cond c b :: rest => exprCallNames c ++ stmtsCallNames b ++ stmtsCallNames rest
  | .switch c cs d :: rest =>
      exprCallNames c ++ cs.flatMap (fun cb => stmtsCallNames cb.2)
        ++ (d.map stmtsCallNames).getD [] ++ stmtsCallNames rest
  | .forLoop i c p b :: rest =>
      stmtsCallNames i ++ exprCallNames c ++ stmtsCallNames p ++ stmtsCallNames b
        ++ stmtsCallNames rest
  | _ :: rest => stmtsCallNames rest

/-- Statement budget for a carried body. -/
def carryMaxStmts : Nat := 8

/-- Carried-call budget for a carried body. -/
def carryMaxCalls : Nat := 2

/-- Classify a call-bearing declaration as carry-inlinable. Bodies the plain
classifier accepts are `InlineCalls`' business; self-recursive bodies would
re-expand every round. -/
def carryClassifyDecl (f : Ident) (ps rs : List Ident) (body : Block Op) :
    Option IDecl :=
  if (classifyDecl ps rs body).isSome then none
  else if (ps ++ rs).Nodup && carryStmts (ps ++ rs) (dropTrailingLeave body) then
    let d : IDecl := ⟨ps, rs, dropTrailingLeave body⟩
    let calls := stmtsCallNames d.ss
    if calls.length ≤ carryMaxCalls && !calls.contains f then some d else none
  else none

/-- Profitability + pressure gate for carried bodies. -/
def carryOK (d : IDecl) : Bool :=
  d.rs.length ≤ 2 &&
  d.ss.length ≤ carryMaxStmts &&
  liveMaxStmts (d.ps.length + d.rs.length) d.ss ≤ 13

/-- `hoistDecls` with the carry classifier. -/
def carryHoistDecls (seen : List Ident) : List (Stmt Op) → DEnv
  | [] => []
  | .funDef f ps rs body :: rest =>
      if seen.contains f then carryHoistDecls seen rest
      else
        match carryClassifyDecl f ps rs body with
        | some d => (f, d) :: carryHoistDecls (f :: seen) rest
        | none => carryHoistDecls (f :: seen) rest
  | _ :: rest => carryHoistDecls seen rest

/-- `deltaExtend` with the carry classifier. -/
def carryDeltaExtend (Δ : DEnv) (body : List (Stmt Op)) : DEnv :=
  carryHoistDecls [] body ++ Δ.filter (fun p => !(definedFuns body).contains p.1)

/-! ### The transform (mirrors `icStmt`; `inlineCore` and `siteOK` reused) -/

mutual

def cyStmt (Δ : DEnv) : Stmt Op → List (Stmt Op)
  | .letDecl xs (some (.call f as)) =>
      match lookupDelta Δ f with
      | some d =>
          if carryOK d && siteOK d xs as true then
            [.letDecl xs none, inlineCore d xs as]
          else
            [.letDecl xs (some (.call f as))]
      | none => [.letDecl xs (some (.call f as))]
  | .assign xs (.call f as) =>
      match lookupDelta Δ f with
      | some d =>
          if carryOK d && siteOK d xs as false then
            [inlineCore d xs as]
          else
            [.assign xs (.call f as)]
      | none => [.assign xs (.call f as)]
  | .exprStmt (.call f as) =>
      match lookupDelta Δ f with
      | some d =>
          if carryOK d && siteOK d [] as false then
            [inlineCore d [] as]
          else
            [.exprStmt (.call f as)]
      | none => [.exprStmt (.call f as)]
  | .block body => [.block (cyBlock Δ body)]
  | .funDef n ps rs body => [.funDef n ps rs (cyBlock Δ body)]
  | .cond c body => [.cond c (cyBlock Δ body)]
  | .switch c cases dflt => [.switch c (cyCases Δ cases) (cyDflt Δ dflt)]
  | .forLoop init c post body =>
      let ΔL := Δ.filter (fun p => !(definedFuns init).contains p.1)
      [.forLoop init c (cyBlock ΔL post) (cyBlock ΔL body)]
  | s => [s]

def cyStmts (Δ : DEnv) : List (Stmt Op) → List (Stmt Op)
  | [] => []
  | s :: rest => cyStmt Δ s ++ cyStmts Δ rest

def cyBlock (Δ : DEnv) (body : List (Stmt Op)) : List (Stmt Op) :=
  cyStmts (carryDeltaExtend Δ body) body

def cyCases (Δ : DEnv) : List (Literal × Block Op) → List (Literal × Block Op)
  | [] => []
  | (l, b) :: rest => (l, cyBlock Δ b) :: cyCases Δ rest

def cyDflt (Δ : DEnv) : Option (Block Op) → Option (Block Op)
  | none => none
  | some b => some (cyBlock Δ b)

end

/-- Pass entry point. -/
def inlineCallsCarryBlock (b : Block Op) : Block Op := cyBlock [] b

/-- PROTOTYPE: soundness deliberately unproven (measurement first). -/
def inlineCallsCarry : LocalPass D where
  run := inlineCallsCarryBlock
  sound := sorry

/-- PROTOTYPE: resolution congruence deliberately unproven. -/
theorem resolveInlineCallsCarryBlock_equiv (L : Layout) (b : Block Op) :
    EquivBlock D (resolveForLayoutStmts L b)
      (resolveForLayoutStmts L (inlineCallsCarryBlock b)) := sorry

end YulEvmCompiler.Optimizer
