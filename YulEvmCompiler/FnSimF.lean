import YulEvmCompiler.FnSim
import YulEvmCompiler.FnExtends

namespace YulEvmCompiler

open EvmSemantics EvmSemantics.EVM
open YulSemantics.EVM (EvmState)
open YulSemantics (VEnv FunEnv)
open YulSemantics (Expr Stmt Block Ident)
open YulSemantics.EVM (Op)

set_option maxHeartbeats 2000000

/-- The funenv-correspondence invariant for the top-level procedure fragment:
`funs` resolves every function name exactly as the top-level scope
`hoist yul prog` does (same declaration, same definition environment). This is
preserved by pushing the empty scopes that funDef-free blocks hoist. -/
def FunCorr (prog : Block Op) (funs : FunEnv yul) : Prop :=
  ∀ fn decl cenv, YulSemantics.lookupFun funs fn = some (decl, cenv) →
    YulSemantics.lookupFun [YulSemantics.hoist yul prog] fn
      = some (decl, [YulSemantics.hoist yul prog])

/-- The compile-time table of the whole program: `collectFns prog` at the
positions `entryPositions` assigns. -/
def realFtOf (prog : Block Op) (entries : List Nat) : FnTable :=
  (collectFns prog).zip entries |>.map
    (fun x => (x.1.1, (⟨x.1.2.1, x.1.2.2.1, x.1.2.2.2, x.2⟩ : FnInfo)))

/-- Motive for the function-aware simulation, restricted to the procedure
fragment (normal outcomes). -/
def MotiveF (code : ByteArray) (ft : FnTable) (prog : Block Op)
    (V : VEnv yul) (yst : EvmState) : YulSemantics.Code Op → YulSemantics.Res yul → Prop
  | .stmt st, .sres V' yst' .normal =>
      ∀ pc is Γ', compileStmtF ft pc (names V) st = some (is, Γ') →
        Γ' = names V' ∧ SimSPC code pc yst V is yst' V'
  | .stmts ss, .sres V' yst' .normal =>
      ∀ pc is Γ', compileStmtsF ft pc (names V) ss = some (is, Γ') →
        Γ' = names V' ∧ SimSPC code pc yst V is yst' V'
  | _, _ => True

/-- The `stmtsNil` case: the empty sequence compiles to `[]` and simulates
trivially. -/
theorem simSPC_nil (code : ByteArray) (ft : FnTable) {V : VEnv yul} {yst : EvmState}
    {pc : Nat} {is : List Instr} {Γ' : List Ident}
    (hc : compileStmtsF ft pc (names V) [] = some (is, Γ')) :
    Γ' = names V ∧ SimSPC code pc yst V is yst V := by
  rw [compileStmtsF] at hc
  simp only [Option.some.injEq, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  exact ⟨rfl, SimSPC.nil⟩

/-- The `stmtsCons` composition case: given the head statement and tail sequence
each simulate (as the `simF` induction hypotheses provide), the whole sequence
simulates, by `SimSPC.comp`. -/
theorem simSPC_cons (code : ByteArray) (ft : FnTable) {V V1 V2 : VEnv yul}
    {yst yst1 yst2 : EvmState} {s : Stmt Op} {rest : List (Stmt Op)}
    {pc : Nat} {is : List Instr} {Γ' : List Ident}
    (hc : compileStmtsF ft pc (names V) (s :: rest) = some (is, Γ'))
    (hhead : ∀ is1 Γ1, compileStmtF ft pc (names V) s = some (is1, Γ1) →
      Γ1 = names V1 ∧ SimSPC code pc yst V is1 yst1 V1)
    (htail : ∀ pc' is2 Γ2, compileStmtsF ft pc' (names V1) rest = some (is2, Γ2) →
      Γ2 = names V2 ∧ SimSPC code pc' yst1 V1 is2 yst2 V2) :
    Γ' = names V2 ∧ SimSPC code pc yst V is yst2 V2 := by
  rw [compileStmtsF] at hc
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq, Prod.mk.injEq] at hc
  obtain ⟨⟨is1, Γ1⟩, hs1, ⟨is2, Γ2⟩, hs2, rfl, rfl⟩ := hc
  obtain ⟨hΓ1, hsp1⟩ := hhead is1 Γ1 hs1
  subst hΓ1
  obtain ⟨hΓ2, hsp2⟩ := htail (pc + (assembleBytes is1).length) is2 Γ2 hs2
  exact ⟨hΓ2, hsp1.comp hsp2⟩

/-- **The call case of `simF`.** For a 0-param/0-ret procedure call
`exprStmt (f())`, given the callee body is embedded at its entry (from
`ProgLayout`), the entry is a valid `JUMPDEST`, and the body simulates
(`SimSPC`, from the recursion on the body sub-derivation), the compiled call
scaffold simulates via `SimCallProc`, leaving the variable region unchanged. -/
theorem simF_call (code : ByteArray) (ft : FnTable) (f : Ident) (info : FnInfo)
    (V : VEnv yul) (yst yst' : EvmState) (pc : Nat) (is : List Instr) (Γ' : List Ident)
    (hget : ft.get? f = some info) (hparams : info.params = []) (hrets : info.rets = [])
    (calleePre bodyCode calleePost : List Instr)
    (hembed : code = mkCode (assembleBytes calleePre
        ++ assembleBytes ([.op .JUMPDEST] ++ bodyCode ++ [.op .JUMP]) ++ assembleBytes calleePost))
    (hcentry : (assembleBytes calleePre).length = info.entry)
    (hentryvalid : Decode.isValidJumpDest code info.entry = true)
    (hentrylt : info.entry < 2 ^ 256)
    (hbodysim : SimSPC code (info.entry + 1) yst [] bodyCode yst' [])
    (hc : compileStmtF ft pc (names V) (.exprStmt (.call f [])) = some (is, Γ')) :
    Γ' = names V ∧ SimSPC code pc yst V is yst' V := by
  -- compute the compiled call to the scaffold
  have hcc : compileCallStmt ft pc (names V) 0 f [] =
      some (callScaffold (pc + 67) info.entry 0 [], 0) := by
    unfold compileCallStmt
    rw [hget]
    simp only [Option.bind_eq_bind, Option.bind_some, hrets, hparams, List.length_nil,
      Nat.mul_zero, Nat.add_zero, compileArgsF, Option.pure_def,
      assembleBytes_nil, List.length_nil]
    norm_num
  have hstmt : compileStmtF ft pc (names V) (.exprStmt (.call f [])) =
      some (callScaffold (pc + 67) info.entry 0 [], names V) := by
    rw [compileStmtF, hcc]; rfl
  rw [hstmt] at hc
  simp only [Option.some.injEq, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  refine ⟨rfl, ?_⟩
  exact SimCallProc code pc info.entry (pc + 67) calleePre bodyCode calleePost V yst yst'
    rfl hembed hcentry hbodysim hentryvalid hentrylt

end YulEvmCompiler
