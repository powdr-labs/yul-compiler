import YulEvmCompiler.FnSimF

/-!
# YulEvmCompiler.FnSimInduction

The function-aware simulation induction `simF` (Phase 4 of `FUNCTIONS_PLAN.md`):
a single induction over the source `Step` producing the code-fixed `SimSPC`
(and, for a procedure call, the call-scaffold simulation) for `compileStmtF`.

Every case is discharged by a previously-proven combinator:

* call-free leaves (`letZero`, `letVal`/`assignVal`/`exprStmt` on non-calls) reuse
  `Correctness.sim` via `stmtF_reuse` + the reverse-extends `compileExprF_rev`;
* `funDef` is a no-op (`SimSPC.nil`);
* `block` uses `SimSPC_block` (pushing an empty funenv scope via `hcons`);
* `cond` uses `SimSPC_ifTrue` / `simSP_ifFalse` through `compileStmtF_cond_inv`;
* sequences use `simSPC_nil` / `simSPC_cons`;
* a procedure `callOk` uses `simF_call` — the callee body simulation comes from
  the body sub-derivation's induction hypothesis (this discharges recursion),
  the embedding from the `ProgLayout` hypothesis `ht`, and the funenv match from
  `FunAgree` + `lookupFun_realFt_corr`; `compileStmtF_step_outcome` rules out the
  `leave` outcome for a compiled body.

`switch`/`for`/`break`/`continue`/`leave` compile to `none`, so their motive is
vacuous. The `hcons` hypothesis is the sound-fragment restriction: entering any
block preserves funenv agreement, which holds when no block hoists functions
(no nested/shadowing function definitions).
-/

namespace YulEvmCompiler

open EvmSemantics EvmSemantics.EVM
open YulSemantics.EVM (EvmState U256)
open YulSemantics (VEnv FunEnv)
open YulSemantics (Expr Stmt Block Ident)
open YulSemantics.EVM (Op)

set_option maxHeartbeats 4000000

/-- Convenience: procedures have no single-return functions, so `compileExprF`
agrees with the free `compileExpr` (reverse-extends). -/
private theorem hft_ne_one {ft : FnTable}
    (hft : ∀ n info, ft.get? n = some info → info.params = [] ∧ info.rets = [])
    (n : Ident) (info : FnInfo) (h : ft.get? n = some info) : info.rets.length ≠ 1 := by
  rw [(hft n info h).2]; simp

/-- A statement that the function-aware compiler always rejects satisfies the
motive vacuously (or trivially for non-normal outcomes). -/
private theorem motiveF_none {code : ByteArray} {ft : FnTable} {prog : Block Op}
    {funs : FunEnv yul} {V : VEnv yul} {yst : EvmState} {st : Stmt Op} {res : YulSemantics.Res yul}
    (hnone : ∀ pc is Γ', compileStmtF ft pc (names V) st ≠ some (is, Γ')) :
    MotiveF code ft prog funs V yst (.stmt st) res := by
  cases res with
  | eres => trivial
  | sres V' yst' o =>
      cases o <;>
        first
        | trivial
        | (intro _ pc is Γ' hc; exact absurd hc (hnone pc is Γ'))

theorem simF (code : ByteArray) (prog : Block Op) (entries : List Nat) (fullIs : List Instr)
    (ht : ∀ fn info, FnTable.get? (realFtOf prog entries) fn = some info →
      ∃ c, compileFn (realFtOf prog entries) info.entry info.params info.rets info.body = some c ∧
        ∃ preIs postIs, fullIs = preIs ++ c ++ postIs ∧ (assembleBytes preIs).length = info.entry)
    (hcode : code = assemble fullIs)
    (hlen : entries.length = (collectFns prog).length)
    (hproc : ∀ n info, FnTable.get? (realFtOf prog entries) n = some info →
      info.params = [] ∧ info.rets = [])
    (hsize : ∀ n info, FnTable.get? (realFtOf prog entries) n = some info → info.entry < 2 ^ 256)
    (hcons : ∀ (b : Block Op) (fs : FunEnv yul), FunAgree prog fs →
      FunAgree prog (YulSemantics.hoist yul b :: fs))
    {funs : FunEnv yul} {V : VEnv yul} {yst : EvmState}
    {c : YulSemantics.Code Op} {res : YulSemantics.Res yul}
    (h : YulSemantics.Step yul funs V yst c res) :
    MotiveF code (realFtOf prog entries) prog funs V yst c res := by
  set ft := realFtOf prog entries with hft
  induction h with
  | lit => trivial
  | var => trivial
  | builtinOk => trivial
  | builtinHalt => trivial
  | builtinArgsHalt => trivial
  | @callOk funs V yst fn args argvals st1 decl cenv Vend st2 o hargs hlook hplen hbody hor
      ihargs ihbody =>
      intro hcorr pc is Γ' hc
      -- resolve fn against the top-level table
      have hlook' : YulSemantics.lookupFun [YulSemantics.hoist yul prog] fn = some (decl, cenv) := by
        rw [← hcorr fn]; exact hlook
      obtain ⟨info, hget, hp', hr', hb'⟩ := lookupFun_realFt_corr prog entries hlen fn decl cenv hlook'
      obtain ⟨hpar, hret⟩ := hproc fn info hget
      have hdp : decl.params = [] := by rw [← hp', hpar]
      have hdr : decl.rets = [] := by rw [← hr', hret]
      -- cenv is the top-level scope
      have hcenv : cenv = [YulSemantics.hoist yul prog] := by
        rw [lookupFun_single] at hlook'
        rcases hfd : (YulSemantics.hoist yul prog).find? (fun p => p.1 = fn) with _ | p
        · rw [hfd] at hlook'; simp at hlook'
        · rw [hfd] at hlook'; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hlook'
          exact hlook'.2.symm
      -- no args: the argument list evaluated to [], leaving the state unchanged
      have hav : argvals = [] := by rw [hdp] at hplen; simpa using hplen
      subst hav
      cases hargs
      -- now st1 = yst, args = []; bindings collapse to []
      have hbind : decl.params.zip [] ++ YulSemantics.bindZeros yul decl.rets
          = ([] : VEnv yul) := by rw [hdp, hdr]; simp [YulSemantics.bindZeros]
      rw [hbind] at hbody ihbody
      -- embedding of the callee body
      obtain ⟨cd, hcompileFn, preIs, postIs, hfull, hpre⟩ := ht fn info hget
      have hcf := hcompileFn
      rw [hpar, hret] at hcf
      simp only [compileFn, List.append_nil, List.length_nil, Nat.zero_le, List.replicate,
        retSwaps, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq, if_true] at hcf
      obtain ⟨⟨bodyCode, Γbody⟩, hbodyc, hcd⟩ := hcf
      have hbodyc' : compileStmtF ft (info.entry + 1) (names ([] : VEnv yul)) (.block decl.body)
          = some (bodyCode, Γbody) := by rw [← hb']; exact hbodyc
      -- outcome is normal (a compiled body cannot `leave`)
      have hout := compileStmtF_step_outcome ft hbody hbodyc'
      have hnorm : o = .normal := by rcases hor with h | h <;> rcases hout with h' | h' <;> simp_all
      subst hnorm
      obtain ⟨hΓe, hbodysim⟩ := ihbody (hcenv ▸ FunAgree.top prog) (info.entry + 1) bodyCode Γbody
        hbodyc'
      -- Γbody = [] (a block restores its outer, empty, layout), hence Vend = []
      have hΓbody : Γbody = [] := by
        rw [compileStmtF] at hbodyc
        simp only [Nat.add_zero, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
          Option.some.injEq, Prod.mk.injEq] at hbodyc
        obtain ⟨_, _, _, h2⟩ := hbodyc; exact h2.symm
      have hnv : Vend.map Prod.fst = [] := by
        show names Vend = []; rw [← hΓe, hΓbody]
      have hVe : Vend = ([] : VEnv yul) := List.map_eq_nil_iff.mp hnv
      subst hVe
      -- assemble the embedding and finish via simF_call
      have hembed : code = mkCode (assembleBytes preIs
          ++ assembleBytes ([.op .JUMPDEST] ++ bodyCode ++ [.op .JUMP])
          ++ assembleBytes postIs) := by
        rw [hcode, hfull, hcd]; simp [assemble, mkCode, assembleBytes_append]
      have hentryvalid : Decode.isValidJumpDest code info.entry = true := by
        rw [hcode, ← hpre]; exact entry_isValidJumpDest hcompileFn hfull
      exact simF_call code ft fn info V yst st2 pc is Γ' hget hpar hret preIs bodyCode postIs
        hembed hpre hentryvalid (hsize fn info hget) hbodysim hc
  | callHalt => trivial
  | callArgsHalt => trivial
  | argsNil => trivial
  | argsCons => trivial
  | argsRestHalt => trivial
  | argsHeadHalt => trivial
  | funDef =>
      intro hcorr pc is Γ' hc
      rw [compileStmtF] at hc
      simp only [Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      exact ⟨rfl, SimSPC.nil⟩
  | @block funs V yst body Vb stb o hbody ihbody =>
      cases o with
      | normal =>
          intro hcorr pc is Γ' hc
          refine SimSPC_block code ft ?_ hc
          intro isb Γb hbs
          exact ihbody (hcons body funs hcorr) pc isb Γb hbs
      | «break» => trivial
      | «continue» => trivial
      | leave => trivial
      | halt => trivial
  | @letZero funs V yst vars =>
      intro hcorr pc is Γ' hc
      refine stmtF_reuse code (funs := funs) YulSemantics.Step.letZero ?_
      rw [compileStmt]; rw [compileStmtF] at hc; exact hc
  | @letVal funs V yst vars e vals st1 hexp hlen ihexp =>
      cases e with
      | lit l =>
          intro hcorr pc is Γ' hc
          match vars with
          | [x] =>
              refine stmtF_reuse code (funs := funs) (YulSemantics.Step.letVal hexp hlen) ?_
              rw [compileStmt]
              simp only [compileStmtF, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
                Option.some.injEq, Prod.mk.injEq] at hc ⊢
              obtain ⟨is', hce, rfl, rfl⟩ := hc
              exact ⟨is', compileExprF_rev ft (hft_ne_one hproc) (names V) pc 0 _ is' hce, rfl, rfl⟩
          | [] => simp [compileStmtF] at hc
          | x :: y :: t => simp [compileStmtF] at hc
      | var z =>
          intro hcorr pc is Γ' hc
          match vars with
          | [x] =>
              refine stmtF_reuse code (funs := funs) (YulSemantics.Step.letVal hexp hlen) ?_
              rw [compileStmt]
              simp only [compileStmtF, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
                Option.some.injEq, Prod.mk.injEq] at hc ⊢
              obtain ⟨is', hce, rfl, rfl⟩ := hc
              exact ⟨is', compileExprF_rev ft (hft_ne_one hproc) (names V) pc 0 _ is' hce, rfl, rfl⟩
          | [] => simp [compileStmtF] at hc
          | x :: y :: t => simp [compileStmtF] at hc
      | builtin op cargs =>
          intro hcorr pc is Γ' hc
          match vars with
          | [x] =>
              refine stmtF_reuse code (funs := funs) (YulSemantics.Step.letVal hexp hlen) ?_
              rw [compileStmt]
              simp only [compileStmtF, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
                Option.some.injEq, Prod.mk.injEq] at hc ⊢
              obtain ⟨is', hce, rfl, rfl⟩ := hc
              exact ⟨is', compileExprF_rev ft (hft_ne_one hproc) (names V) pc 0 _ is' hce, rfl, rfl⟩
          | [] => simp [compileStmtF] at hc
          | x :: y :: t => simp [compileStmtF] at hc
      | call f cargs =>
          intro hcorr pc is Γ' hc
          -- the compiled call binds `m = vars.length` results; here `m = 0`, so `vars = []`
          have hvars : vars = [] := by
            rw [compileStmtF] at hc
            simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hc
            obtain ⟨⟨code, m⟩, hcall, hb⟩ := hc
            rw [compileCallStmt] at hcall
            simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hcall
            obtain ⟨info, hgeti, hcall2⟩ := hcall
            rw [(hproc f info hgeti).2] at hcall2
            split at hcall2
            · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
                Option.some.injEq, Prod.mk.injEq] at hcall2
              obtain ⟨_, _, _, hm⟩ := hcall2
              split at hb
              · rename_i hcond
                simp only [Option.some.injEq, Prod.mk.injEq] at hb
                rw [← hm] at hcond; exact (List.length_eq_zero_iff).mp hcond.symm
              · exact absurd hb (by simp)
            · exact absurd hcall2 (by simp)
          subst hvars
          have hvals : vals = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
          subst hvals
          -- letDecl [] and exprStmt compile the call identically (defeq)
          have hexpr : compileStmtF ft pc (names V) (.exprStmt (.call f cargs)) = some (is, Γ') := hc
          simpa using ihexp hcorr pc is Γ' hexpr
  | letHalt => trivial
  | @assignVal funs V yst vars e vals st1 hexp hlen ihexp =>
      intro hcorr pc is Γ' hc
      refine stmtF_reuse code (funs := funs) (YulSemantics.Step.assignVal hexp hlen) ?_
      match vars with
      | [x] =>
          rw [compileStmt]
          simp only [compileStmtF, Option.bind_eq_bind, Option.bind_eq_some_iff] at hc ⊢
          obtain ⟨is', hce, idx, hidx, hb⟩ := hc
          exact ⟨is', compileExprF_rev ft (hft_ne_one hproc) (names V) pc 0 _ is' hce, idx, hidx, hb⟩
      | [] => simp [compileStmtF] at hc
      | x :: y :: t => simp [compileStmtF] at hc
  | assignHalt => trivial
  | @exprStmt funs V yst e st1 hexp ihexp =>
      cases e with
      | call f args => intro hcorr pc is Γ' hc; exact ihexp hcorr pc is Γ' hc
      | lit l => cases hexp
      | var x => cases hexp
      | builtin op args =>
          intro hcorr pc is Γ' hc
          refine stmtF_reuse code (funs := funs) (YulSemantics.Step.exprStmt hexp) ?_
          rw [compileStmt]
          simp only [compileStmtF, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
            Option.some.injEq, Prod.mk.injEq] at hc ⊢
          obtain ⟨is', hce, rfl, rfl⟩ := hc
          exact ⟨is', compileExprF_rev ft (hft_ne_one hproc) (names V) pc 0 _ is' hce, rfl, rfl⟩
  | exprStmtHalt => trivial
  | @ifTrue funs V yst c body cv st1 V' st2 o hcstep hcv hblock ihc ihblock =>
      cases o with
      | normal =>
          intro hcorr pc is Γ' hc
          obtain ⟨cCode, bodyCode, Γb, hcc, hbc, rfl, rfl⟩ := compileStmtF_cond_inv ft hc
          have hblockc : compileStmtF ft (pc + (assembleBytes cCode).length + 35) (names V)
              (.block body)
              = some (bodyCode ++ List.replicate (Γb.length - (names V).length) (.op .POP),
                names V) := by
            rw [compileStmtF]
            simp only [Nat.add_zero, Option.bind_eq_bind, hbc, Option.bind_some, Option.pure_def]
          obtain ⟨hΓblock, hbodysim⟩ :=
            ihblock hcorr (pc + (assembleBytes cCode).length + 35) _ _ hblockc
          have hSE : SimE yst V 0 cCode [cv] st1 :=
            sim hcstep 0 cCode (compileExprF_rev ft (hft_ne_one hproc) (names V) pc 0 c cCode hcc)
          have hcondz : (conv (YulSemantics.EVM.b2w (cv = 0))).toNat = 0 :=
            b2w_toNat_eq_zero (fun hd => hcv (of_decide_eq_true hd))
          exact ⟨hΓblock, SimSPC_ifTrue code (ifPrologueSimE hSE) hcondz hbodysim⟩
      | «break» => trivial
      | «continue» => trivial
      | leave => trivial
      | halt => trivial
  | @ifFalse funs V yst c body cv st1 hcstep hcv ihc =>
      intro hcorr pc is Γ' hc
      obtain ⟨cCode, bodyCode, Γb, hcc, hbc, rfl, rfl⟩ := compileStmtF_cond_inv ft hc
      refine ⟨rfl, ?_⟩
      have hSE : SimE yst V 0 cCode [cv] st1 :=
        sim hcstep 0 cCode (compileExprF_rev ft (hft_ne_one hproc) (names V) pc 0 c cCode hcc)
      have hcond1 : (conv (YulSemantics.EVM.b2w (cv = 0))).toNat ≠ 0 :=
        b2w_toNat_ne_zero (decide_eq_true (show cv = (0 : U256) from hcv))
      have hdest : pc + (assembleBytes cCode).length + 35 + (assembleBytes bodyCode).length
            + (Γb.length - (names V).length)
          = pc + (assembleBytes cCode).length + 35
            + (assembleBytes (bodyCode
                ++ List.replicate (Γb.length - (names V).length) (.op .POP))).length := by
        simp [assembleBytes_append]; omega
      exact (simSP_ifFalse (ifPrologueSimE hSE) hcond1 hdest).toSimSPC code
  | ifHalt => trivial
  | switchExec _ _ _ _ => exact motiveF_none (fun pc is Γ' => by simp [compileStmtF])
  | switchHalt => trivial
  | forLoop _ _ _ _ => exact motiveF_none (fun pc is Γ' => by simp [compileStmtF])
  | forInitHalt => trivial
  | «break» => trivial
  | «continue» => trivial
  | leave => trivial
  | seqNil =>
      intro hcorr pc is Γ' hc
      exact simSPC_nil code ft hc
  | @seqCons funs V yst s rest V1 st1 V2 st2 o hs hrest ihs ihrest =>
      cases o with
      | normal =>
          intro hcorr pc is Γ' hc
          exact simSPC_cons code ft hc (fun is1 Γ1 h1 => ihs hcorr pc is1 Γ1 h1)
            (fun pc' is2 Γ2 h2 => ihrest hcorr pc' is2 Γ2 h2)
      | «break» => trivial
      | «continue» => trivial
      | leave => trivial
      | halt => trivial
  | @seqStop funs V yst s rest V1 st1 o hs hne ihs =>
      cases o with
      | normal => exact absurd rfl hne
      | «break» => trivial
      | «continue» => trivial
      | leave => trivial
      | halt => trivial
  | loopDone _ _ => trivial
  | loopCondHalt _ => trivial
  | loopStep _ _ _ _ _ _ _ _ _ _ => trivial
  | loopPostHalt _ _ _ _ _ _ _ _ => trivial
  | loopBreak _ _ _ _ _ => trivial
  | loopLeave _ _ _ _ _ => trivial
  | loopBodyHalt _ _ _ _ _ => trivial

end YulEvmCompiler
