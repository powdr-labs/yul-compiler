import YulEvmCompiler.Optimizer.Implementation.Normalization.Disambiguate.Decide
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# Completeness of the `SourceValid` decider

The dual of `Disambiguate/Decide.lean`: `sourceValidB` not only *implies*
`SourceValid` (soundness, there) but is *implied by* it (completeness, here).
Together they give `sourceValidB b = true ↔ SourceValid b`, so the guard the
normalization pass runs on **fires on exactly** the valid source programs — the
missing ingredient that turns the guarded pass into a clean
`SourceValid → NormalForm` pre/postcondition pass, and (with the parser boundary
`validateBlockSource ⟹ SourceValid`) shows the guard is active on every
parser-accepted program, not a silent identity.

Only the `SourceValid → sourceValidB = true` direction is proved here.
-/

namespace YulEvmCompiler.Optimizer.Normalize

open YulSemantics
open YulEvmCompiler.Optimizer.NormalForm
  (WellScoped ScopedExpr ScopedArgs ScopedStmt ScopedStmts ScopedCases ScopedDflt
   funDefNames declTopVars declTopVarsL)

variable {Op : Type}

/-! ### The fresh-name atom -/

/-- Reverse of `isDsNameL_dsName`: anything the recogniser accepts really is a
`dsName`. -/
theorem isDsNameL_toList_imp {x : Ident} (h : isDsNameL x.toList = true) :
    ∃ k, x = dsName k := by
  cases hL : x.toList with
  | nil => rw [hL] at h; simp [isDsNameL, and_assoc] at h
  | cons c rest =>
      rw [hL] at h
      simp only [isDsNameL, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨hc, hne⟩, hall⟩ := h
      have hmem : ∀ y ∈ rest, y = 'v' := by
        intro y hy
        have := List.all_eq_true.mp hall y hy
        simpa using this
      have hrep : rest = List.replicate rest.length 'v' := List.eq_replicate_of_mem hmem
      have hlen : rest.length ≠ 0 := by
        simp only [ne_eq, List.length_eq_zero_iff]
        intro h0; subst h0; simp at hne
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hlen
      refine ⟨m, ?_⟩
      have hrest : rest = List.replicate (m + 1) 'v' := hrep.trans (by rw [hm])
      have hx : x.toList = Char.ofNat 0 :: List.replicate (m + 1) 'v' := by
        rw [hL, hc, hrest]
      calc x = String.ofList x.toList := String.ofList_toList.symm
        _ = String.ofList (Char.ofNat 0 :: List.replicate (m + 1) 'v') := by rw [hx]
        _ = dsName m := rfl

/-- **Completeness of the fresh-name check.** -/
theorem notFreshB_complete {x : Ident} (h : NotFresh x) : notFreshB x = true := by
  rw [NotFresh] at h
  rw [notFreshB]
  cases hval : isDsNameL x.toList with
  | false => rfl
  | true => obtain ⟨k, hk⟩ := isDsNameL_toList_imp hval; exact absurd hk (h k)

/-- `∀ x ∈ xs, NotFresh x` gives the Bool list check. -/
theorem all_notFreshB_complete {xs : List Ident} (h : ∀ x ∈ xs, NotFresh x) :
    xs.all notFreshB = true :=
  List.all_eq_true.mpr (fun x hx => notFreshB_complete (h x hx))

theorem all_memB_complete {vs xs : List Ident} (h : ∀ x ∈ xs, x ∈ vs) :
    xs.all (fun x => decide (x ∈ vs)) = true :=
  List.all_eq_true.mpr (fun x hx => decide_eq_true_eq.mpr (h x hx))

theorem all_notMemB_complete {dom xs : List Ident} (h : ∀ x ∈ xs, x ∉ dom) :
    xs.all (fun x => decide (x ∉ dom)) = true :=
  List.all_eq_true.mpr (fun x hx => decide_eq_true_eq.mpr (h x hx))

/-! ### `SVStmts` -/

mutual
theorem svExprB_complete : ∀ (e : Expr Op), SVExpr e → svExprB e = true
  | .lit _, _ => rfl
  | .var _, h => by simp only [SVExpr] at h; simp only [svExprB]; exact notFreshB_complete h
  | .builtin _ args, h => by
      simp only [SVExpr] at h; simp only [svExprB]; exact svArgsB_complete args h
  | .call _ args, h => by
      simp only [SVExpr] at h; simp only [svExprB, Bool.and_eq_true]
      exact ⟨notFreshB_complete h.1, svArgsB_complete args h.2⟩
theorem svArgsB_complete : ∀ (es : List (Expr Op)), SVArgs es → svArgsB es = true
  | [], _ => rfl
  | e :: rest, h => by
      simp only [SVArgs] at h; simp only [svArgsB, Bool.and_eq_true]
      exact ⟨svExprB_complete e h.1, svArgsB_complete rest h.2⟩
end

theorem svOptExprB_complete {eo : Option (Expr Op)} (h : ∀ e, eo = some e → SVExpr e) :
    svOptExprB eo = true := by
  cases eo with
  | none => rfl
  | some e => exact svExprB_complete e (h e rfl)

mutual
theorem svStmtB_complete : ∀ (s : Stmt Op), SVStmt s → svStmtB s = true
  | .letDecl vars eo, h => by
      simp only [SVStmt, and_assoc] at h
      simp only [svStmtB, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
      exact ⟨h.1, all_notFreshB_complete h.2.1, svOptExprB_complete h.2.2⟩
  | .assign vars e, h => by
      simp only [SVStmt] at h; simp only [svStmtB, Bool.and_eq_true]
      exact ⟨all_notFreshB_complete h.1, svExprB_complete e h.2⟩
  | .exprStmt e, h => by simp only [SVStmt] at h; exact svExprB_complete e h
  | .funDef fn ps rs body, h => by
      simp only [SVStmt, and_assoc] at h
      simp only [svStmtB, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
      exact ⟨notFreshB_complete h.1, h.2.1, all_notFreshB_complete h.2.2.1,
        svStmtsB_complete body h.2.2.2⟩
  | .block body, h => by simp only [SVStmt] at h; exact svStmtsB_complete body h
  | .cond c body, h => by
      simp only [SVStmt] at h; simp only [svStmtB, Bool.and_eq_true]
      exact ⟨svExprB_complete c h.1, svStmtsB_complete body h.2⟩
  | .switch c cases dflt, h => by
      simp only [SVStmt, and_assoc] at h
      simp only [svStmtB, Bool.and_eq_true, and_assoc]
      exact ⟨svExprB_complete c h.1, svCasesB_complete cases h.2.1, svDfltB_complete dflt h.2.2⟩
  | .forLoop init c post body, h => by
      simp only [SVStmt, and_assoc] at h
      simp only [svStmtB, Bool.and_eq_true, and_assoc]
      exact ⟨svStmtsB_complete init h.1, svExprB_complete c h.2.1,
        svStmtsB_complete post h.2.2.1, svStmtsB_complete body h.2.2.2⟩
  | .break, _ => rfl
  | .continue, _ => rfl
  | .leave, _ => rfl
theorem svStmtsB_complete : ∀ (ss : List (Stmt Op)), SVStmts ss → svStmtsB ss = true
  | [], _ => rfl
  | s :: rest, h => by
      simp only [SVStmts] at h; simp only [svStmtsB, Bool.and_eq_true]
      exact ⟨svStmtB_complete s h.1, svStmtsB_complete rest h.2⟩
theorem svCasesB_complete : ∀ (cs : List (Literal × List (Stmt Op))), SVCases cs → svCasesB cs = true
  | [], _ => rfl
  | (_, body) :: rest, h => by
      simp only [SVCases] at h; simp only [svCasesB, Bool.and_eq_true]
      exact ⟨svStmtsB_complete body h.1, svCasesB_complete rest h.2⟩
theorem svDfltB_complete : ∀ (d : Option (List (Stmt Op))), SVDflt d → svDfltB d = true
  | none, _ => rfl
  | some body, h => by simp only [SVDflt] at h; exact svStmtsB_complete body h
end

/-! ### `WellFormed` -/

mutual
theorem wfInnerB_complete : ∀ (ss : List (Stmt Op)), WFInner ss → wfInnerB ss = true
  | [], _ => rfl
  | s :: rest, h => by
      simp only [WFInner] at h; simp only [wfInnerB, Bool.and_eq_true]
      exact ⟨wfInnerSB_complete s h.1, wfInnerB_complete rest h.2⟩
theorem wfInnerSB_complete : ∀ (s : Stmt Op), WFInnerS s → wfInnerSB s = true
  | .funDef _ _ _ body, h => by
      simp only [WFInnerS] at h; simp only [wfInnerSB, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨h.1, wfInnerB_complete body h.2⟩
  | .block body, h => by
      simp only [WFInnerS] at h; simp only [wfInnerSB, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨h.1, wfInnerB_complete body h.2⟩
  | .cond _ body, h => by
      simp only [WFInnerS] at h; simp only [wfInnerSB, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨h.1, wfInnerB_complete body h.2⟩
  | .switch _ cases dflt, h => by
      simp only [WFInnerS, and_assoc] at h
      simp only [wfInnerSB, Bool.and_eq_true, and_assoc]
      exact ⟨wfCasesB_complete cases h.1, wfDfltB_complete dflt h.2⟩
  | .forLoop init _ post body, h => by
      simp only [WFInnerS, and_assoc] at h
      simp only [wfInnerSB, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
      exact ⟨h.1, wfInnerB_complete init h.2.1, h.2.2.1, wfInnerB_complete body h.2.2.2.1,
        h.2.2.2.2.1, wfInnerB_complete post h.2.2.2.2.2⟩
  | .letDecl _ _, _ => rfl
  | .assign _ _, _ => rfl
  | .exprStmt _, _ => rfl
  | .break, _ => rfl
  | .continue, _ => rfl
  | .leave, _ => rfl
theorem wfCasesB_complete : ∀ (cs : List (Literal × List (Stmt Op))), WFCases cs → wfCasesB cs = true
  | [], _ => rfl
  | (_, body) :: rest, h => by
      simp only [WFCases, and_assoc] at h
      simp only [wfCasesB, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
      exact ⟨h.1, wfInnerB_complete body h.2.1, wfCasesB_complete rest h.2.2⟩
theorem wfDfltB_complete : ∀ (d : Option (List (Stmt Op))), WFDflt d → wfDfltB d = true
  | none, _ => rfl
  | some body, h => by
      simp only [WFDflt] at h; simp only [wfDfltB, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨h.1, wfInnerB_complete body h.2⟩
end

theorem wellFormedB_complete {b : Block Op} (h : WellFormed b) : wellFormedB b = true := by
  simp only [WellFormed, and_assoc] at h
  simp only [wellFormedB, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  exact ⟨h.1, wfInnerB_complete b h.2⟩

/-! ### `NormalForm.WellScoped` -/

mutual
theorem nfScopedExprB_complete : ∀ {vs fs : List Ident} (e : Expr Op),
    ScopedExpr vs fs e → nfScopedExprB vs fs e = true
  | _, _, .lit _, _ => rfl
  | _, _, .var _, h => by
      simp only [ScopedExpr] at h; simp only [nfScopedExprB, decide_eq_true_eq]; exact h
  | _, _, .builtin _ args, h => by
      simp only [ScopedExpr] at h; simp only [nfScopedExprB]; exact nfScopedArgsB_complete args h
  | _, _, .call _ args, h => by
      simp only [ScopedExpr] at h; simp only [nfScopedExprB, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨h.1, nfScopedArgsB_complete args h.2⟩
theorem nfScopedArgsB_complete : ∀ {vs fs : List Ident} (es : List (Expr Op)),
    ScopedArgs vs fs es → nfScopedArgsB vs fs es = true
  | _, _, [], _ => rfl
  | _, _, e :: rest, h => by
      simp only [ScopedArgs] at h; simp only [nfScopedArgsB, Bool.and_eq_true]
      exact ⟨nfScopedExprB_complete e h.1, nfScopedArgsB_complete rest h.2⟩
end

mutual
theorem nfScopedStmtB_complete : ∀ {vs fs : List Ident} (s : Stmt Op),
    ScopedStmt vs fs s → nfScopedStmtB vs fs s = true
  | _, _, .block body, h => by
      simp only [ScopedStmt] at h; simp only [nfScopedStmtB]; exact nfScopedStmtsB_complete body h
  | _, _, .funDef _ _ _ body, h => by
      simp only [ScopedStmt] at h; simp only [nfScopedStmtB]; exact nfScopedStmtsB_complete body h
  | _, _, .letDecl _ (some e), h => by
      simp only [ScopedStmt] at h; simp only [nfScopedStmtB]; exact nfScopedExprB_complete e h
  | _, _, .letDecl _ none, _ => rfl
  | _, _, .assign vars e, h => by
      simp only [ScopedStmt] at h; simp only [nfScopedStmtB, Bool.and_eq_true]
      exact ⟨all_memB_complete h.1, nfScopedExprB_complete e h.2⟩
  | _, _, .cond c body, h => by
      simp only [ScopedStmt] at h; simp only [nfScopedStmtB, Bool.and_eq_true]
      exact ⟨nfScopedExprB_complete c h.1, nfScopedStmtsB_complete body h.2⟩
  | _, _, .switch c cases dflt, h => by
      simp only [ScopedStmt, and_assoc] at h
      simp only [nfScopedStmtB, Bool.and_eq_true, and_assoc]
      exact ⟨nfScopedExprB_complete c h.1, nfScopedCasesB_complete cases h.2.1,
        nfScopedDfltB_complete dflt h.2.2⟩
  | _, _, .forLoop init c post body, h => by
      simp only [ScopedStmt, and_assoc] at h
      simp only [nfScopedStmtB, Bool.and_eq_true, and_assoc]
      exact ⟨nfScopedStmtsB_complete init h.1, nfScopedExprB_complete c h.2.1,
        nfScopedStmtsB_complete post h.2.2.1, nfScopedStmtsB_complete body h.2.2.2⟩
  | _, _, .exprStmt e, h => by
      simp only [ScopedStmt] at h; simp only [nfScopedStmtB]; exact nfScopedExprB_complete e h
  | _, _, .break, _ => rfl
  | _, _, .continue, _ => rfl
  | _, _, .leave, _ => rfl
theorem nfScopedStmtsB_complete : ∀ {vs fs : List Ident} (ss : List (Stmt Op)),
    ScopedStmts vs fs ss → nfScopedStmtsB vs fs ss = true
  | _, _, [], _ => rfl
  | _, _, s :: rest, h => by
      simp only [ScopedStmts] at h; simp only [nfScopedStmtsB, Bool.and_eq_true]
      exact ⟨nfScopedStmtB_complete s h.1, nfScopedStmtsB_complete rest h.2⟩
theorem nfScopedCasesB_complete : ∀ {vs fs : List Ident} (cs : List (Literal × List (Stmt Op))),
    ScopedCases vs fs cs → nfScopedCasesB vs fs cs = true
  | _, _, [], _ => rfl
  | _, _, (_, b) :: cs, h => by
      simp only [ScopedCases] at h; simp only [nfScopedCasesB, Bool.and_eq_true]
      exact ⟨nfScopedStmtsB_complete b h.1, nfScopedCasesB_complete cs h.2⟩
theorem nfScopedDfltB_complete : ∀ {vs fs : List Ident} (d : Option (List (Stmt Op))),
    ScopedDflt vs fs d → nfScopedDfltB vs fs d = true
  | _, _, none, _ => rfl
  | _, _, some b, h => by
      simp only [ScopedDflt] at h; simp only [nfScopedDfltB]; exact nfScopedStmtsB_complete b h
end

theorem nfWellScopedB_complete {b : Block Op} (h : WellScoped b) : nfWellScopedB b = true :=
  nfScopedStmtsB_complete b h

/-! ### `WScopedStmts` -/

mutual
theorem wScopedStmtB_complete : ∀ {dom : List Ident} (s : Stmt Op),
    WScopedStmt dom s → wScopedStmtB dom s = true
  | _, .letDecl vars _, h => by
      simp only [WScopedStmt] at h; simp only [wScopedStmtB]; exact all_notMemB_complete h
  | _, .block body, h => by
      simp only [WScopedStmt] at h; simp only [wScopedStmtB]; exact wScopedStmtsB_complete body h
  | _, .cond _ body, h => by
      simp only [WScopedStmt] at h; simp only [wScopedStmtB]; exact wScopedStmtsB_complete body h
  | _, .switch _ cases dflt, h => by
      simp only [WScopedStmt] at h; simp only [wScopedStmtB, Bool.and_eq_true]
      exact ⟨wScopedCasesB_complete cases h.1, wScopedDfltB_complete dflt h.2⟩
  | _, .funDef _ ps rs body, h => by
      simp only [WScopedStmt] at h; simp only [wScopedStmtB, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨h.1, wScopedStmtsB_complete body h.2⟩
  | _, .forLoop init _ post body, h => by
      simp only [WScopedStmt, and_assoc] at h
      simp only [wScopedStmtB, Bool.and_eq_true, and_assoc]
      exact ⟨wScopedStmtsB_complete init h.1, wScopedStmtsB_complete body h.2.1,
        wScopedStmtsB_complete post h.2.2⟩
  | _, .assign _ _, _ => rfl
  | _, .exprStmt _, _ => rfl
  | _, .break, _ => rfl
  | _, .continue, _ => rfl
  | _, .leave, _ => rfl
theorem wScopedStmtsB_complete : ∀ {dom : List Ident} (ss : List (Stmt Op)),
    WScopedStmts dom ss → wScopedStmtsB dom ss = true
  | _, [], _ => rfl
  | _, s :: rest, h => by
      simp only [WScopedStmts] at h; simp only [wScopedStmtsB, Bool.and_eq_true]
      exact ⟨wScopedStmtB_complete s h.1, wScopedStmtsB_complete rest h.2⟩
theorem wScopedCasesB_complete : ∀ {dom : List Ident} (cs : List (Literal × List (Stmt Op))),
    WScopedCases dom cs → wScopedCasesB dom cs = true
  | _, [], _ => rfl
  | _, (_, body) :: rest, h => by
      simp only [WScopedCases] at h; simp only [wScopedCasesB, Bool.and_eq_true]
      exact ⟨wScopedStmtsB_complete body h.1, wScopedCasesB_complete rest h.2⟩
theorem wScopedDfltB_complete : ∀ {dom : List Ident} (d : Option (List (Stmt Op))),
    WScopedDflt dom d → wScopedDfltB dom d = true
  | _, none, _ => rfl
  | _, some body, h => by
      simp only [WScopedDflt] at h; simp only [wScopedDfltB]; exact wScopedStmtsB_complete body h
end

/-! ### `FScopedStmts` -/

mutual
theorem fScopedStmtB_complete : ∀ {fdom : List Ident} (s : Stmt Op),
    FScopedStmt fdom s → fScopedStmtB fdom s = true
  | _, .block body, h => by
      simp only [FScopedStmt] at h; simp only [fScopedStmtB, Bool.and_eq_true]
      exact ⟨all_notMemB_complete h.1, fScopedStmtsB_complete body h.2⟩
  | _, .cond _ body, h => by
      simp only [FScopedStmt] at h; simp only [fScopedStmtB, Bool.and_eq_true]
      exact ⟨all_notMemB_complete h.1, fScopedStmtsB_complete body h.2⟩
  | _, .funDef _ _ _ body, h => by
      simp only [FScopedStmt] at h; simp only [fScopedStmtB, Bool.and_eq_true]
      exact ⟨all_notMemB_complete h.1, fScopedStmtsB_complete body h.2⟩
  | _, .switch _ cases dflt, h => by
      simp only [FScopedStmt] at h; simp only [fScopedStmtB, Bool.and_eq_true]
      exact ⟨fScopedCasesB_complete cases h.1, fScopedDfltB_complete dflt h.2⟩
  | _, .forLoop init _ post body, h => by
      simp only [FScopedStmt, and_assoc] at h
      simp only [fScopedStmtB, Bool.and_eq_true, and_assoc]
      exact ⟨all_notMemB_complete h.1, fScopedStmtsB_complete init h.2.1,
        all_notMemB_complete h.2.2.1, fScopedStmtsB_complete body h.2.2.2.1,
        all_notMemB_complete h.2.2.2.2.1, fScopedStmtsB_complete post h.2.2.2.2.2⟩
  | _, .letDecl _ _, _ => rfl
  | _, .assign _ _, _ => rfl
  | _, .exprStmt _, _ => rfl
  | _, .break, _ => rfl
  | _, .continue, _ => rfl
  | _, .leave, _ => rfl
theorem fScopedStmtsB_complete : ∀ {fdom : List Ident} (ss : List (Stmt Op)),
    FScopedStmts fdom ss → fScopedStmtsB fdom ss = true
  | _, [], _ => rfl
  | _, s :: rest, h => by
      simp only [FScopedStmts] at h; simp only [fScopedStmtsB, Bool.and_eq_true]
      exact ⟨fScopedStmtB_complete s h.1, fScopedStmtsB_complete rest h.2⟩
theorem fScopedCasesB_complete : ∀ {fdom : List Ident} (cs : List (Literal × List (Stmt Op))),
    FScopedCases fdom cs → fScopedCasesB fdom cs = true
  | _, [], _ => rfl
  | _, (_, body) :: rest, h => by
      simp only [FScopedCases, and_assoc] at h
      simp only [fScopedCasesB, Bool.and_eq_true, and_assoc]
      exact ⟨all_notMemB_complete h.1, fScopedStmtsB_complete body h.2.1,
        fScopedCasesB_complete rest h.2.2⟩
theorem fScopedDfltB_complete : ∀ {fdom : List Ident} (d : Option (List (Stmt Op))),
    FScopedDflt fdom d → fScopedDfltB fdom d = true
  | _, none, _ => rfl
  | _, some body, h => by
      simp only [FScopedDflt] at h; simp only [fScopedDfltB, Bool.and_eq_true]
      exact ⟨all_notMemB_complete h.1, fScopedStmtsB_complete body h.2⟩
end

/-! ### The bundle -/

/-- **Completeness of the `SourceValid` decider**: every valid source block is
accepted by `sourceValidB`. With `sourceValidB_sound` this gives
`sourceValidB b = true ↔ SourceValid b`. -/
theorem sourceValidB_complete {b : Block Op} (h : SourceValid b) : sourceValidB b = true := by
  simp only [SourceValid, and_assoc] at h
  simp only [sourceValidB, Bool.and_eq_true, and_assoc]
  exact ⟨svStmtsB_complete b h.1, wellFormedB_complete h.2.1,
    nfWellScopedB_complete h.2.2.1, wScopedStmtsB_complete b h.2.2.2.1,
    fScopedStmtsB_complete b h.2.2.2.2⟩

end YulEvmCompiler.Optimizer.Normalize
