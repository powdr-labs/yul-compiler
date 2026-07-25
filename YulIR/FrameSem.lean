import YulIR.Frame
import YulSemantics.Dialect.EVM

set_option warningAsError true
/-!
# YulIR.FrameSem — a native executable semantics for the frame IR

A fuel-indexed interpreter over the `Fin n`-frame IR, specialised to the EVM dialect (built-ins go
through the dialect's own `stepOp`, so the semantics never re-implements EVM behaviour). This is the
*native* semantics against which frame-IR pass soundness will be stated — it never erases to Yul, so
it does not depend on the (deferred) `ofYul`/`toYul` adequacy.

The key ergonomic payoff of the intrinsic frame shows up immediately: the variable environment is a
**total** function `Store n := Fin n → U256` — slot reads never fail, there is no `Option`/unbound
case, and no scoping side-conditions. A function call runs the callee's body in a fresh `Store m`
(its own frame), params seeded from the arguments and all other slots zero.

Fuel bounds loops and calls so the interpreter is executable (`#eval`); the definitions are
`partial`. A relational big-step version (for cleaner induction in proofs) can be layered on later —
this executable form already pins the intended meaning and can be cross-checked against `toYul`.
-/

namespace YulIR.FinFrame.Sem

open YulSemantics (Outcome)
open YulSemantics.EVM (litValue stepOp)

/-- The value type and machine state come from the EVM dialect. -/
abbrev U256 := YulSemantics.EVM.U256
abbrev State := YulSemantics.EVM.EvmState

/-- A frame store: a total map from the `n` slots to values. -/
abbrev Store (n : Nat) := Fin n → U256

/-- The function table an execution runs against. -/
abbrev Funs := Std.HashMap (Option YulSemantics.Ident) Function

/-- Evaluate an atom (total — a slot read cannot fail). -/
def evalAtom (σ : Store n) : Atom n → U256
  | .lit l  => litValue l
  | .slot i => σ i

/-- Update one slot. -/
def upd (σ : Store n) (i : Fin n) (v : U256) : Store n := fun j => if j == i then v else σ j

/-- Update several slots in order (multi-result writes). -/
def updMany (σ : Store n) (is : List (Fin n)) (vs : List U256) : Store n :=
  (is.zip vs).foldl (fun s p => upd s p.1 p.2) σ

/-- Seed a callee frame of `m` slots: parameter slots get the argument values, all others zero. -/
def seed (m : Nat) (params : List (Fin m)) (args : List U256) : Store m := fun j =>
  match (params.zip args).find? (fun p => p.1 == j) with
  | some p => p.2
  | none   => 0

mutual
/-- Evaluate an rhs to a built-in result (`.ok vals st'` or `.halt st'`); `none` on stuck / out of
fuel (arity mismatch, unmodeled built-in, missing function). -/
partial def evalRhs (funs : Funs) (fuel : Nat) (σ : Store n) (st : State) :
    Rhs n → Option (YulSemantics.BuiltinResult U256 State)
  | .atom a          => some (.ok [evalAtom σ a] st)
  | .builtin op args => stepOp op (args.map (evalAtom σ)) st
  | .call fn args    =>
      match fuel with
      | 0        => none
      | fuel + 1 =>
        match funs[some fn]? with
        | none       => none
        | some fdecl =>
            let argvals := args.map (evalAtom σ)
            match execBlock funs fuel (seed fdecl.nslots fdecl.params argvals) st fdecl.body with
            | some (_, st', .halt) => some (.halt st')
            | some (σ', st', _)    => some (.ok (fdecl.rets.map σ') st')   -- normal/leave: read returns
            | none                 => none

/-- Execute a statement: returns the updated store, state, and control outcome. -/
partial def execStmt (funs : Funs) (fuel : Nat) (σ : Store n) (st : State) :
    Stmt n → Option (Store n × State × Outcome)
  | .assign ds rhs =>
      match evalRhs funs fuel σ st rhs with
      | some (.ok vs st') => some (updMany σ ds vs, st', .normal)
      | some (.halt st')  => some (σ, st', .halt)
      | none              => none
  | .cond c body =>
      if evalAtom σ c == 0 then some (σ, st, .normal) else execBlock funs fuel σ st body
  | .switch c cases dflt =>
      let cv := evalAtom σ c
      match cases.find? (fun p => litValue p.1 == cv) with
      | some p => execBlock funs fuel σ st p.2
      | none   => match dflt with
                  | some b => execBlock funs fuel σ st b
                  | none   => some (σ, st, .normal)
  | .loop post body => execLoop funs fuel σ st post body
  | .«break»    => some (σ, st, .«break»)
  | .«continue» => some (σ, st, .«continue»)
  | .leave      => some (σ, st, .leave)

/-- Execute a block, short-circuiting on any non-`normal` outcome. -/
partial def execBlock (funs : Funs) (fuel : Nat) (σ : Store n) (st : State) :
    Block n → Option (Store n × State × Outcome)
  | []      => some (σ, st, .normal)
  | s :: rest =>
      match execStmt funs fuel σ st s with
      | some (σ', st', .normal) => execBlock funs fuel σ' st' rest
      | some res                => some res
      | none                    => none

/-- Execute a loop `for {} 1 { post } { body }`: run `body`; `break` ends it normally, `leave`/`halt`
propagate, `normal`/`continue` run `post` and repeat. -/
partial def execLoop (funs : Funs) (fuel : Nat) (σ : Store n) (st : State) (post body : Block n) :
    Option (Store n × State × Outcome) :=
  match fuel with
  | 0        => none
  | fuel + 1 =>
    match execBlock funs fuel σ st body with
    | some (σ', st', .«break») => some (σ', st', .normal)
    | some (σ', st', .leave)   => some (σ', st', .leave)
    | some (σ', st', .halt)    => some (σ', st', .halt)
    | some (σ', st', _)        =>            -- normal or continue: run post, then loop
        match execBlock funs fuel σ' st' post with
        | some (σ'', st'', .normal) => execLoop funs fuel σ'' st'' post body
        | some res                  => some res
        | none                      => none
    | none => none
end

/-- Run a whole program: execute the entry point (`functions[none]`) in a zero-initialised frame. -/
def run (p : Program) (st : State) (fuel : Nat := 100000) : Option (State × Outcome) :=
  match p.main? with
  | some fd => (execBlock p.functions fuel (fun _ => 0) st fd.body).map (fun r => (r.2.1, r.2.2))
  | none    => none

end YulIR.FinFrame.Sem
