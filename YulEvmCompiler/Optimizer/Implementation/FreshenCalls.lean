import YulEvmCompiler.Optimizer.Implementation.InlineCalls
set_option warningAsError true
/-!
# YulEvmCompiler.Optimizer.Implementation.FreshenCalls

**Call-site freshening** — the collision unblocker for `InlineCalls`.

solc's helpers reuse a small vocabulary (`value`, `slot`, `offset`, …) as
*both* caller-side variables and callee parameter/return names, so the
biggest gas-gap fixtures hit `siteOK`'s capture conditions
(`xs ∩ (ps ∪ rs) ≠ ∅`, argument shadowing, call-bearing arguments) and their
helper chains never inline. `InlineCalls` cannot α-rename: its soundness
inserts callee bodies *unchanged* (the `Δ`-matching argument depends on it).

This pass renames the **caller side** instead. An assign-form site
`xs := f(as)` that resolves to an inlinable declaration but fails `siteOK`
is rewritten to a self-contained block with globally-fresh names:

```yul
{
  let P_a<n> := as[n]        // ... right-to-left, matching argument order
  ...
  let P_a0 := as[0]
  let P_r0, P_r1 := f(P_a0, …, P_a<n>)
  xs[0] := P_r0
  xs[1] := P_r1
}
```

The inner site now has collision-free, call-free, variable arguments, so
`inlineCalls` (which runs right after this pass in the round) inlines it,
and depth-gated copy propagation plus `DeadPure` consume exactly the copies
introduced here. The fresh names share a prefix `P` chosen so that **no
program identifier starts with it** — freshness needs no counter threading,
per-site reuse of the same names is fine (each site's names are bound only
inside its own block), and the choice depends only on the program's
identifier set, which layout resolution never changes.

Only the assign form is rewritten in v1: the observed blockers are all
assign-form (`value := extract_…(…)`, `slot, offset := storage_array_…(…)`),
and the let form would additionally need the halt-desync bookkeeping of a
zero-init split (`let xs` leaves binders on the env when the site block
halts). Logged as a follow-up.

Soundness (`EquivStmt` per site, pointwise — no function-environment
reasoning is needed because the call remains a call): argument hoists
evaluate the same expressions in the same order (right-to-left) with the
same halt/stuckness behavior; the call reads the hoisted values back in
order; the read-out assignments equal the original `setMany`; and the
enclosing block's `restore` erases the temporaries on every exit path,
including halts.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM

variable {calls : ExternalCalls} {creates : ExternalCreates}

local notation "D" => evmWithExternal calls creates

/-! ### Identifier collection and the fresh prefix -/

mutual

/-- Every identifier occurring in an expression (variables and call names). -/
def exprIdents : Expr Op → List Ident
  | .lit _ => []
  | .var x => [x]
  | .builtin _ args => argsIdents args
  | .call f args => f :: argsIdents args

/-- Identifiers of an argument list. -/
def argsIdents : List (Expr Op) → List Ident
  | [] => []
  | e :: rest => exprIdents e ++ argsIdents rest

end

mutual

/-- Every identifier occurring in a statement: binders, targets, function
names, parameters, returns, and expression identifiers. -/
def stmtIdents : Stmt Op → List Ident
  | .block body => stmtsIdents body
  | .funDef n ps rs body => n :: ps ++ rs ++ stmtsIdents body
  | .letDecl xs none => xs
  | .letDecl xs (some e) => xs ++ exprIdents e
  | .assign xs e => xs ++ exprIdents e
  | .cond c body => exprIdents c ++ stmtsIdents body
  | .switch c cases dflt =>
      exprIdents c ++ casesIdents cases ++ dfltIdents dflt
  | .forLoop init c post body =>
      stmtsIdents init ++ exprIdents c ++ stmtsIdents post ++ stmtsIdents body
  | .exprStmt e => exprIdents e
  | .break => []
  | .continue => []
  | .leave => []

/-- Identifiers of a statement sequence. -/
def stmtsIdents : List (Stmt Op) → List Ident
  | [] => []
  | s :: rest => stmtIdents s ++ stmtsIdents rest

/-- Identifiers of `switch` cases. -/
def casesIdents : List (Literal × Block Op) → List Ident
  | [] => []
  | (_, b) :: rest => stmtsIdents b ++ casesIdents rest

/-- Identifiers of a `switch` default. -/
def dfltIdents : Option (Block Op) → List Ident
  | none => []
  | some b => stmtsIdents b

end

/-- Does any identifier in `used` start with `p`? -/
def prefixUsed (used : List Ident) (p : String) : Bool :=
  used.any (fun x => p.isPrefixOf x)

/-- A prefix no program identifier starts with: the first `fc<k>_` free in
`used`. Termination: there are finitely many identifiers, each with finitely
many prefixes, so some `k ≤ used.length` is free (fuel makes this obvious to
the compiler; on fuel exhaustion — impossible — the pass declines by
returning `none`, keeping the transform total and conservative). -/
def freshPrefixFuel (used : List Ident) : Nat → Nat → Option String
  | 0, _ => none
  | fuel + 1, k =>
      let p := s!"fc{k}_"
      if prefixUsed used p then freshPrefixFuel used fuel (k + 1) else some p

/-- The fresh prefix for a program's identifier set. -/
def freshPrefix (used : List Ident) : Option String :=
  freshPrefixFuel used (used.length + 1) 0

/-! ### The site rewrite -/

/-- The fresh argument names for arity `n`: `P_a0 … P_a(n-1)`. -/
def freshArgs (P : String) (n : Nat) : List Ident :=
  (List.range n).map (fun i => s!"{P}a{i}")

/-- The fresh return names for arity `n`: `P_r0 … P_r(n-1)`. -/
def freshRets (P : String) (n : Nat) : List Ident :=
  (List.range n).map (fun i => s!"{P}r{i}")

/-- Should this assign-form site be freshened? It must resolve to an
inlinable declaration that `inlineCalls` *wants* (`inlineOK`) with matching
arities and distinct targets, but be rejected by its capture/shape
conditions (`siteOK`) — the only sites where freshening changes anything. -/
def freshenWanted (d : IDecl) (xs : List Ident) (as : List (Expr Op)) : Bool :=
  inlineOK d && as.length = d.ps.length && xs.length = d.rs.length &&
  xs.Nodup && !siteOK d xs as false

/-- The freshened site block (see the module notes). -/
def freshenCore (P : String) (xs : List Ident) (f : Ident)
    (as : List (Expr Op)) : Stmt Op :=
  let fas := freshArgs P as.length
  let frs := freshRets P xs.length
  .block
    (((fas.zip as).reverse.map (fun pa => .letDecl [pa.1] (some pa.2)))
      ++ [.letDecl frs (some (.call f (fas.map .var)))]
      ++ (xs.zip frs).map (fun xr => .assign [xr.1] (.var xr.2)))

/-! ### The traversal (Δ mirrors `InlineCalls` exactly) -/

mutual

/-- Freshen through one statement. Only the assign-call form rewrites. -/
def fcStmt (P : String) (Δ : DEnv) : Stmt Op → Stmt Op
  | .assign xs (.call f as) =>
      match lookupDelta Δ f with
      | some d =>
          if freshenWanted d xs as then freshenCore P xs f as
          else .assign xs (.call f as)
      | none => .assign xs (.call f as)
  | .block body => .block (fcBlock P Δ body)
  | .funDef n ps rs body => .funDef n ps rs (fcBlock P Δ body)
  | .cond c body => .cond c (fcBlock P Δ body)
  | .switch c cases dflt => .switch c (fcCases P Δ cases) (fcDflt P Δ dflt)
  | .forLoop init c post body =>
      let ΔL := Δ.filter (fun p => !(definedFuns init).contains p.1)
      .forLoop init c (fcBlock P ΔL post) (fcBlock P ΔL body)
  | s => s

/-- Freshen through a statement sequence (already under its block's `Δ`). -/
def fcStmts (P : String) (Δ : DEnv) : List (Stmt Op) → List (Stmt Op)
  | [] => []
  | s :: rest => fcStmt P Δ s :: fcStmts P Δ rest

/-- Enter a block: extend `Δ` with its hoisted declarations. -/
def fcBlock (P : String) (Δ : DEnv) (body : List (Stmt Op)) : List (Stmt Op) :=
  fcStmts P (deltaExtend Δ body) body

/-- Freshen through `switch` case bodies. -/
def fcCases (P : String) (Δ : DEnv) :
    List (Literal × Block Op) → List (Literal × Block Op)
  | [] => []
  | (l, b) :: rest => (l, fcBlock P Δ b) :: fcCases P Δ rest

/-- Freshen through a `switch` default. -/
def fcDflt (P : String) (Δ : DEnv) : Option (Block Op) → Option (Block Op)
  | none => none
  | some b => some (fcBlock P Δ b)

end

/-- The pass entry point: pick the fresh prefix from the whole block's
identifier set (declining when none is found — impossible, but total). -/
def freshenCallsBlock (b : Block Op) : Block Op :=
  match freshPrefix (stmtsIdents b) with
  | some P => fcBlock P [] b
  | none => b

set_option warningAsError false in
/-- The **FreshenCalls pass**: collision unblocking for `InlineCalls`
(soundness in progress — per-site `EquivStmt`, see module notes). -/
def freshenCalls : Pass D where
  run := freshenCallsBlock
  sound := sorry

@[simp] theorem freshenCalls_run (b : Block Op) :
    (freshenCalls (calls := calls) (creates := creates)).run b =
      freshenCallsBlock b := rfl

end YulEvmCompiler.Optimizer
