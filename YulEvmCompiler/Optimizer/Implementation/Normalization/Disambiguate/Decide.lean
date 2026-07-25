import YulEvmCompiler.Optimizer.Implementation.Normalization.Disambiguate.Pass
import YulEvmCompiler.Optimizer.Implementation.Normalization.NormalForm
set_option warningAsError true
/-!
# Decidable mirror of `SourceValid`

`disambiguate`'s soundness is conditional on `SourceValid` (see
`Disambiguate/Pass.lean`): a bundle of five standing validity facts about a
source program. `SourceValid` is a `Prop` built by structural recursion over the
AST, so it is not usable as a runtime guard directly.

This module provides a `Bool` mirror `sourceValidB` with a soundness theorem
`sourceValidB_eq_true → SourceValid`, following the `wellScopedB` /
`wellScopedB_sound` precedent in `HoistFunDefsPass.lean`. It is what lets
`Normalize.normalize` become an **unconditionally** sound `GlobalPass` via
`GlobalPass.ofGuardedBlock` (the hoister's pattern): apply the rename where the
guard fires, be the identity elsewhere.

Only the `= true → Prop` (soundness) direction is proved — that is all the guard
needs. Completeness (`SourceValid → sourceValidB = true`, i.e. that the guard
*fires* on every parser-accepted program) is a separate, front-end concern.
-/

namespace YulEvmCompiler.Optimizer.Normalize

open YulSemantics
open YulEvmCompiler.Optimizer.NormalForm
  (WellScoped ScopedExpr ScopedArgs ScopedStmt ScopedStmts ScopedCases ScopedDflt
   funDefNames declTopVars declTopVarsL)

variable {Op : Type}

/-! ### The fresh-name atom `NotFresh`

`NotFresh x := ∀ k, x ≠ dsName k`, and `dsName k` is the string `NUL v^(k+1)`.
So `x` is a fresh name iff its characters are a `NUL` followed by one-or-more
`'v'`s; `notFreshB` decides the negation. For soundness we only need that every
`dsName k` is recognised (`isDsNameL_dsName`), so the guard never mistakes a
fresh name for a source one. -/

/-- Recognise the character list of a `dsName`: a leading `NUL` then a nonempty
run of `'v'`s. -/
def isDsNameL : List Char → Bool
  | c :: rest => (c == Char.ofNat 0) && !rest.isEmpty && rest.all (· == 'v')
  | [] => false

/-- Decidable mirror of `NotFresh`. -/
def notFreshB (x : Ident) : Bool := !isDsNameL x.toList

private theorem all_replicate_v (n : Nat) : (List.replicate n 'v').all (· == 'v') = true := by
  simp only [List.all_eq_true]
  intro x hx
  simp [List.eq_of_mem_replicate hx]

theorem isDsNameL_dsName (k : Nat) : isDsNameL (dsName k).toList = true := by
  have hlist : (dsName k).toList = Char.ofNat 0 :: List.replicate (k + 1) 'v' := by
    rw [dsName, String.toList_ofList]
  rw [hlist, List.replicate_succ, isDsNameL, List.isEmpty_cons]
  rw [← List.replicate_succ]
  simp only [beq_self_eq_true, Bool.not_false, Bool.true_and, Bool.and_true]
  exact all_replicate_v (k + 1)

theorem notFreshB_sound {x : Ident} (h : notFreshB x = true) : NotFresh x := by
  intro k hk
  have hd : isDsNameL x.toList = true := by rw [hk]; exact isDsNameL_dsName k
  rw [notFreshB, hd] at h
  simp at h

/-- `∀ x ∈ xs, NotFresh x` from the Bool list check. -/
theorem all_notFreshB_sound {xs : List Ident} (h : xs.all notFreshB = true) :
    ∀ x ∈ xs, NotFresh x := by
  intro x hx
  exact notFreshB_sound (List.all_eq_true.mp h x hx)

/-! ### `SVStmts` — source validity -/

mutual
def svExprB : Expr Op → Bool
  | .lit _ => true
  | .var x => notFreshB x
  | .builtin _ args => svArgsB args
  | .call fn args => notFreshB fn && svArgsB args
def svArgsB : List (Expr Op) → Bool
  | [] => true
  | e :: rest => svExprB e && svArgsB rest
end

/-- Optional right-hand side of a `letDecl`. -/
def svOptExprB : Option (Expr Op) → Bool
  | none => true
  | some e => svExprB e

mutual
def svStmtB : Stmt Op → Bool
  | .letDecl vars eo => decide vars.Nodup && vars.all notFreshB && svOptExprB eo
  | .assign vars e => vars.all notFreshB && svExprB e
  | .exprStmt e => svExprB e
  | .funDef fn ps rs body =>
      notFreshB fn && decide (ps ++ rs).Nodup && (ps ++ rs).all notFreshB && svStmtsB body
  | .block body => svStmtsB body
  | .cond c body => svExprB c && svStmtsB body
  | .switch c cases dflt => svExprB c && svCasesB cases && svDfltB dflt
  | .forLoop init c post body => svStmtsB init && svExprB c && svStmtsB post && svStmtsB body
  | _ => true
def svStmtsB : List (Stmt Op) → Bool
  | [] => true
  | s :: rest => svStmtB s && svStmtsB rest
def svCasesB : List (Literal × List (Stmt Op)) → Bool
  | [] => true
  | (_, body) :: rest => svStmtsB body && svCasesB rest
def svDfltB : Option (List (Stmt Op)) → Bool
  | none => true
  | some body => svStmtsB body
end

mutual
theorem svExprB_sound : ∀ (e : Expr Op), svExprB e = true → SVExpr e
  | .lit _, _ => by simp only [SVExpr]
  | .var _, h => by
      simp only [svExprB] at h; simp only [SVExpr]; exact notFreshB_sound h
  | .builtin _ args, h => by
      simp only [svExprB] at h; simp only [SVExpr]; exact svArgsB_sound args h
  | .call _ args, h => by
      simp only [svExprB, Bool.and_eq_true] at h
      simp only [SVExpr]; exact ⟨notFreshB_sound h.1, svArgsB_sound args h.2⟩
theorem svArgsB_sound : ∀ (es : List (Expr Op)), svArgsB es = true → SVArgs es
  | [], _ => by simp only [SVArgs]
  | e :: rest, h => by
      simp only [svArgsB, Bool.and_eq_true] at h
      simp only [SVArgs]; exact ⟨svExprB_sound e h.1, svArgsB_sound rest h.2⟩
end

theorem svOptExprB_sound {eo : Option (Expr Op)} (h : svOptExprB eo = true) :
    ∀ e, eo = some e → SVExpr e := by
  intro e he; subst he; exact svExprB_sound e (by simpa [svOptExprB] using h)

mutual
theorem svStmtB_sound : ∀ (s : Stmt Op), svStmtB s = true → SVStmt s
  | .letDecl vars eo, h => by
      simp only [svStmtB, Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [SVStmt]
      exact ⟨h.1.1, all_notFreshB_sound h.1.2, svOptExprB_sound h.2⟩
  | .assign vars e, h => by
      simp only [svStmtB, Bool.and_eq_true] at h
      simp only [SVStmt]; exact ⟨all_notFreshB_sound h.1, svExprB_sound e h.2⟩
  | .exprStmt e, h => by
      simp only [svStmtB] at h; simp only [SVStmt]; exact svExprB_sound e h
  | .funDef fn ps rs body, h => by
      simp only [svStmtB, Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [SVStmt]
      exact ⟨notFreshB_sound h.1.1.1, h.1.1.2, all_notFreshB_sound h.1.2,
        svStmtsB_sound body h.2⟩
  | .block body, h => by
      simp only [svStmtB] at h; simp only [SVStmt]; exact svStmtsB_sound body h
  | .cond c body, h => by
      simp only [svStmtB, Bool.and_eq_true] at h
      simp only [SVStmt]; exact ⟨svExprB_sound c h.1, svStmtsB_sound body h.2⟩
  | .switch c cases dflt, h => by
      simp only [svStmtB, Bool.and_eq_true] at h
      simp only [SVStmt]
      exact ⟨svExprB_sound c h.1.1, svCasesB_sound cases h.1.2, svDfltB_sound dflt h.2⟩
  | .forLoop init c post body, h => by
      simp only [svStmtB, Bool.and_eq_true] at h
      simp only [SVStmt]
      exact ⟨svStmtsB_sound init h.1.1.1, svExprB_sound c h.1.1.2,
        svStmtsB_sound post h.1.2, svStmtsB_sound body h.2⟩
  | .break, _ => by simp only [SVStmt]
  | .continue, _ => by simp only [SVStmt]
  | .leave, _ => by simp only [SVStmt]
theorem svStmtsB_sound : ∀ (ss : List (Stmt Op)), svStmtsB ss = true → SVStmts ss
  | [], _ => by simp only [SVStmts]
  | s :: rest, h => by
      simp only [svStmtsB, Bool.and_eq_true] at h
      simp only [SVStmts]; exact ⟨svStmtB_sound s h.1, svStmtsB_sound rest h.2⟩
theorem svCasesB_sound : ∀ (cs : List (Literal × List (Stmt Op))), svCasesB cs = true → SVCases cs
  | [], _ => by simp only [SVCases]
  | (_, body) :: rest, h => by
      simp only [svCasesB, Bool.and_eq_true] at h
      simp only [SVCases]; exact ⟨svStmtsB_sound body h.1, svCasesB_sound rest h.2⟩
theorem svDfltB_sound : ∀ (d : Option (List (Stmt Op))), svDfltB d = true → SVDflt d
  | none, _ => by simp only [SVDflt]
  | some body, h => by simp only [svDfltB] at h; simp only [SVDflt]; exact svStmtsB_sound body h
end

/-! ### `WellFormed` — per-block distinct function names -/

mutual
def wfInnerB : List (Stmt Op) → Bool
  | [] => true
  | s :: rest => wfInnerSB s && wfInnerB rest
def wfInnerSB : Stmt Op → Bool
  | .funDef _ _ _ body => decide (funNames body).Nodup && wfInnerB body
  | .block body => decide (funNames body).Nodup && wfInnerB body
  | .cond _ body => decide (funNames body).Nodup && wfInnerB body
  | .switch _ cases dflt => wfCasesB cases && wfDfltB dflt
  | .forLoop init _ post body =>
      (decide (funNames init).Nodup && wfInnerB init) &&
      (decide (funNames body).Nodup && wfInnerB body) &&
      (decide (funNames post).Nodup && wfInnerB post)
  | _ => true
def wfCasesB : List (Literal × List (Stmt Op)) → Bool
  | [] => true
  | (_, body) :: rest => (decide (funNames body).Nodup && wfInnerB body) && wfCasesB rest
def wfDfltB : Option (List (Stmt Op)) → Bool
  | none => true
  | some body => decide (funNames body).Nodup && wfInnerB body
end

/-- Decidable mirror of `WellFormed`. -/
def wellFormedB (b : Block Op) : Bool := decide (funNames b).Nodup && wfInnerB b

mutual
theorem wfInnerB_sound : ∀ (ss : List (Stmt Op)), wfInnerB ss = true → WFInner ss
  | [], _ => by simp only [WFInner]
  | s :: rest, h => by
      simp only [wfInnerB, Bool.and_eq_true] at h
      simp only [WFInner]; exact ⟨wfInnerSB_sound s h.1, wfInnerB_sound rest h.2⟩
theorem wfInnerSB_sound : ∀ (s : Stmt Op), wfInnerSB s = true → WFInnerS s
  | .funDef _ _ _ body, h => by
      simp only [wfInnerSB, Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [WFInnerS]; exact ⟨h.1, wfInnerB_sound body h.2⟩
  | .block body, h => by
      simp only [wfInnerSB, Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [WFInnerS]; exact ⟨h.1, wfInnerB_sound body h.2⟩
  | .cond _ body, h => by
      simp only [wfInnerSB, Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [WFInnerS]; exact ⟨h.1, wfInnerB_sound body h.2⟩
  | .switch _ cases dflt, h => by
      simp only [wfInnerSB, Bool.and_eq_true] at h
      simp only [WFInnerS]; exact ⟨wfCasesB_sound cases h.1, wfDfltB_sound dflt h.2⟩
  | .forLoop init _ post body, h => by
      simp only [wfInnerSB, Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [WFInnerS]
      exact ⟨⟨h.1.1.1, wfInnerB_sound init h.1.1.2⟩, ⟨h.1.2.1, wfInnerB_sound body h.1.2.2⟩,
        ⟨h.2.1, wfInnerB_sound post h.2.2⟩⟩
  | .letDecl _ _, _ => by simp only [WFInnerS]
  | .assign _ _, _ => by simp only [WFInnerS]
  | .exprStmt _, _ => by simp only [WFInnerS]
  | .break, _ => by simp only [WFInnerS]
  | .continue, _ => by simp only [WFInnerS]
  | .leave, _ => by simp only [WFInnerS]
theorem wfCasesB_sound : ∀ (cs : List (Literal × List (Stmt Op))), wfCasesB cs = true → WFCases cs
  | [], _ => by simp only [WFCases]
  | (_, body) :: rest, h => by
      simp only [wfCasesB, Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [WFCases]; exact ⟨⟨h.1.1, wfInnerB_sound body h.1.2⟩, wfCasesB_sound rest h.2⟩
theorem wfDfltB_sound : ∀ (d : Option (List (Stmt Op))), wfDfltB d = true → WFDflt d
  | none, _ => by simp only [WFDflt]
  | some body, h => by
      simp only [wfDfltB, Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [WFDflt]; exact ⟨h.1, wfInnerB_sound body h.2⟩
end

theorem wellFormedB_sound {b : Block Op} (h : wellFormedB b = true) : WellFormed b := by
  simp only [wellFormedB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, wfInnerB_sound b h.2⟩

/-! ### `NormalForm.WellScoped` — every referenced name resolves (two-scope) -/

private theorem all_memB_sound {vs xs : List Ident}
    (h : xs.all (fun x => decide (x ∈ vs)) = true) : ∀ x ∈ xs, x ∈ vs :=
  fun x hx => of_decide_eq_true (List.all_eq_true.mp h x hx)

mutual
def nfScopedExprB (vs fs : List Ident) : Expr Op → Bool
  | .lit _ => true
  | .var x => decide (x ∈ vs)
  | .builtin _ args => nfScopedArgsB vs fs args
  | .call fn args => decide (fn ∈ fs) && nfScopedArgsB vs fs args
def nfScopedArgsB (vs fs : List Ident) : List (Expr Op) → Bool
  | [] => true
  | e :: rest => nfScopedExprB vs fs e && nfScopedArgsB vs fs rest
end

mutual
def nfScopedStmtB (vs fs : List Ident) : Stmt Op → Bool
  | .block body => nfScopedStmtsB vs (fs ++ funDefNames body) body
  | .funDef _ params rets body => nfScopedStmtsB (params ++ rets) (fs ++ funDefNames body) body
  | .letDecl _ (some e) => nfScopedExprB vs fs e
  | .letDecl _ none => true
  | .assign vars e => vars.all (fun x => decide (x ∈ vs)) && nfScopedExprB vs fs e
  | .cond c body => nfScopedExprB vs fs c && nfScopedStmtsB vs (fs ++ funDefNames body) body
  | .switch c cases dflt =>
      nfScopedExprB vs fs c && nfScopedCasesB vs fs cases && nfScopedDfltB vs fs dflt
  | .forLoop init c post body =>
      nfScopedStmtsB vs (fs ++ funDefNames init) init &&
      nfScopedExprB (vs ++ declTopVarsL init) (fs ++ funDefNames init) c &&
      nfScopedStmtsB (vs ++ declTopVarsL init) ((fs ++ funDefNames init) ++ funDefNames post) post &&
      nfScopedStmtsB (vs ++ declTopVarsL init) ((fs ++ funDefNames init) ++ funDefNames body) body
  | .exprStmt e => nfScopedExprB vs fs e
  | _ => true
def nfScopedStmtsB (vs fs : List Ident) : List (Stmt Op) → Bool
  | [] => true
  | s :: rest => nfScopedStmtB vs fs s && nfScopedStmtsB (vs ++ declTopVars s) fs rest
def nfScopedCasesB (vs fs : List Ident) : List (Literal × List (Stmt Op)) → Bool
  | [] => true
  | (_, b) :: cs => nfScopedStmtsB vs (fs ++ funDefNames b) b && nfScopedCasesB vs fs cs
def nfScopedDfltB (vs fs : List Ident) : Option (List (Stmt Op)) → Bool
  | none => true
  | some b => nfScopedStmtsB vs (fs ++ funDefNames b) b
end

/-- Decidable mirror of `NormalForm.WellScoped`. -/
def nfWellScopedB (b : Block Op) : Bool := nfScopedStmtsB [] (funDefNames b) b

mutual
theorem nfScopedExprB_sound : ∀ {vs fs : List Ident} (e : Expr Op),
    nfScopedExprB vs fs e = true → ScopedExpr vs fs e
  | _, _, .lit _, _ => by simp only [ScopedExpr]
  | _, _, .var _, h => by
      simp only [nfScopedExprB, decide_eq_true_eq] at h; simpa only [ScopedExpr]
  | _, _, .builtin _ args, h => by
      simp only [nfScopedExprB] at h; simp only [ScopedExpr]; exact nfScopedArgsB_sound args h
  | _, _, .call _ args, h => by
      simp only [nfScopedExprB, Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [ScopedExpr]; exact ⟨h.1, nfScopedArgsB_sound args h.2⟩
theorem nfScopedArgsB_sound : ∀ {vs fs : List Ident} (es : List (Expr Op)),
    nfScopedArgsB vs fs es = true → ScopedArgs vs fs es
  | _, _, [], _ => by simp only [ScopedArgs]
  | _, _, e :: rest, h => by
      simp only [nfScopedArgsB, Bool.and_eq_true] at h
      simp only [ScopedArgs]; exact ⟨nfScopedExprB_sound e h.1, nfScopedArgsB_sound rest h.2⟩
end

mutual
theorem nfScopedStmtB_sound : ∀ {vs fs : List Ident} (s : Stmt Op),
    nfScopedStmtB vs fs s = true → ScopedStmt vs fs s
  | _, _, .block body, h => by
      simp only [nfScopedStmtB] at h; simp only [ScopedStmt]; exact nfScopedStmtsB_sound body h
  | _, _, .funDef _ _ _ body, h => by
      simp only [nfScopedStmtB] at h; simp only [ScopedStmt]; exact nfScopedStmtsB_sound body h
  | _, _, .letDecl _ (some e), h => by
      simp only [nfScopedStmtB] at h; simp only [ScopedStmt]; exact nfScopedExprB_sound e h
  | _, _, .letDecl _ none, _ => by simp only [ScopedStmt]
  | _, _, .assign vars e, h => by
      simp only [nfScopedStmtB, Bool.and_eq_true] at h
      simp only [ScopedStmt]; exact ⟨all_memB_sound h.1, nfScopedExprB_sound e h.2⟩
  | _, _, .cond c body, h => by
      simp only [nfScopedStmtB, Bool.and_eq_true] at h
      simp only [ScopedStmt]; exact ⟨nfScopedExprB_sound c h.1, nfScopedStmtsB_sound body h.2⟩
  | _, _, .switch c cases dflt, h => by
      simp only [nfScopedStmtB, Bool.and_eq_true] at h
      simp only [ScopedStmt]
      exact ⟨nfScopedExprB_sound c h.1.1, nfScopedCasesB_sound cases h.1.2,
        nfScopedDfltB_sound dflt h.2⟩
  | _, _, .forLoop init c post body, h => by
      simp only [nfScopedStmtB, Bool.and_eq_true] at h
      simp only [ScopedStmt]
      exact ⟨nfScopedStmtsB_sound init h.1.1.1, nfScopedExprB_sound c h.1.1.2,
        nfScopedStmtsB_sound post h.1.2, nfScopedStmtsB_sound body h.2⟩
  | _, _, .exprStmt e, h => by
      simp only [nfScopedStmtB] at h; simp only [ScopedStmt]; exact nfScopedExprB_sound e h
  | _, _, .break, _ => by simp only [ScopedStmt]
  | _, _, .continue, _ => by simp only [ScopedStmt]
  | _, _, .leave, _ => by simp only [ScopedStmt]
theorem nfScopedStmtsB_sound : ∀ {vs fs : List Ident} (ss : List (Stmt Op)),
    nfScopedStmtsB vs fs ss = true → ScopedStmts vs fs ss
  | _, _, [], _ => by simp only [ScopedStmts]
  | _, _, s :: rest, h => by
      simp only [nfScopedStmtsB, Bool.and_eq_true] at h
      simp only [ScopedStmts]; exact ⟨nfScopedStmtB_sound s h.1, nfScopedStmtsB_sound rest h.2⟩
theorem nfScopedCasesB_sound : ∀ {vs fs : List Ident} (cs : List (Literal × List (Stmt Op))),
    nfScopedCasesB vs fs cs = true → ScopedCases vs fs cs
  | _, _, [], _ => by simp only [ScopedCases]
  | _, _, (_, b) :: cs, h => by
      simp only [nfScopedCasesB, Bool.and_eq_true] at h
      simp only [ScopedCases]; exact ⟨nfScopedStmtsB_sound b h.1, nfScopedCasesB_sound cs h.2⟩
theorem nfScopedDfltB_sound : ∀ {vs fs : List Ident} (d : Option (List (Stmt Op))),
    nfScopedDfltB vs fs d = true → ScopedDflt vs fs d
  | _, _, none, _ => by simp only [ScopedDflt]
  | _, _, some b, h => by
      simp only [nfScopedDfltB] at h; simp only [ScopedDflt]; exact nfScopedStmtsB_sound b h
end

theorem nfWellScopedB_sound {b : Block Op} (h : nfWellScopedB b = true) : WellScoped b :=
  nfScopedStmtsB_sound b h

/-! ### `WScopedStmts` — no variable shadows a visible one -/

private theorem all_notMemB_sound {dom xs : List Ident}
    (h : xs.all (fun x => decide (x ∉ dom)) = true) : ∀ x ∈ xs, x ∉ dom :=
  fun x hx => of_decide_eq_true (List.all_eq_true.mp h x hx)

mutual
def wScopedStmtB (dom : List Ident) : Stmt Op → Bool
  | .letDecl vars _ => vars.all (fun x => decide (x ∉ dom))
  | .block body => wScopedStmtsB dom body
  | .cond _ body => wScopedStmtsB dom body
  | .switch _ cases dflt => wScopedCasesB dom cases && wScopedDfltB dom dflt
  | .funDef _ ps rs body => decide (ps ++ rs).Nodup && wScopedStmtsB (ps ++ rs) body
  | .forLoop init _ post body =>
      wScopedStmtsB dom init && wScopedStmtsB (declVarsSeq init ++ dom) body &&
      wScopedStmtsB (declVarsSeq init ++ dom) post
  | _ => true
def wScopedStmtsB (dom : List Ident) : List (Stmt Op) → Bool
  | [] => true
  | s :: rest => wScopedStmtB dom s && wScopedStmtsB (declVars s ++ dom) rest
def wScopedCasesB (dom : List Ident) : List (Literal × List (Stmt Op)) → Bool
  | [] => true
  | (_, body) :: rest => wScopedStmtsB dom body && wScopedCasesB dom rest
def wScopedDfltB (dom : List Ident) : Option (List (Stmt Op)) → Bool
  | none => true
  | some body => wScopedStmtsB dom body
end

mutual
theorem wScopedStmtB_sound : ∀ {dom : List Ident} (s : Stmt Op),
    wScopedStmtB dom s = true → WScopedStmt dom s
  | _, .letDecl vars _, h => by
      simp only [wScopedStmtB] at h; simp only [WScopedStmt]; exact all_notMemB_sound h
  | _, .block body, h => by
      simp only [wScopedStmtB] at h; simp only [WScopedStmt]; exact wScopedStmtsB_sound body h
  | _, .cond _ body, h => by
      simp only [wScopedStmtB] at h; simp only [WScopedStmt]; exact wScopedStmtsB_sound body h
  | _, .switch _ cases dflt, h => by
      simp only [wScopedStmtB, Bool.and_eq_true] at h
      simp only [WScopedStmt]; exact ⟨wScopedCasesB_sound cases h.1, wScopedDfltB_sound dflt h.2⟩
  | _, .funDef _ ps rs body, h => by
      simp only [wScopedStmtB, Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [WScopedStmt]; exact ⟨h.1, wScopedStmtsB_sound body h.2⟩
  | _, .forLoop init _ post body, h => by
      simp only [wScopedStmtB, Bool.and_eq_true] at h
      simp only [WScopedStmt]
      exact ⟨wScopedStmtsB_sound init h.1.1, wScopedStmtsB_sound body h.1.2,
        wScopedStmtsB_sound post h.2⟩
  | _, .assign _ _, _ => by simp only [WScopedStmt]
  | _, .exprStmt _, _ => by simp only [WScopedStmt]
  | _, .break, _ => by simp only [WScopedStmt]
  | _, .continue, _ => by simp only [WScopedStmt]
  | _, .leave, _ => by simp only [WScopedStmt]
theorem wScopedStmtsB_sound : ∀ {dom : List Ident} (ss : List (Stmt Op)),
    wScopedStmtsB dom ss = true → WScopedStmts dom ss
  | _, [], _ => by simp only [WScopedStmts]
  | _, s :: rest, h => by
      simp only [wScopedStmtsB, Bool.and_eq_true] at h
      simp only [WScopedStmts]; exact ⟨wScopedStmtB_sound s h.1, wScopedStmtsB_sound rest h.2⟩
theorem wScopedCasesB_sound : ∀ {dom : List Ident} (cs : List (Literal × List (Stmt Op))),
    wScopedCasesB dom cs = true → WScopedCases dom cs
  | _, [], _ => by simp only [WScopedCases]
  | _, (_, body) :: rest, h => by
      simp only [wScopedCasesB, Bool.and_eq_true] at h
      simp only [WScopedCases]; exact ⟨wScopedStmtsB_sound body h.1, wScopedCasesB_sound rest h.2⟩
theorem wScopedDfltB_sound : ∀ {dom : List Ident} (d : Option (List (Stmt Op))),
    wScopedDfltB dom d = true → WScopedDflt dom d
  | _, none, _ => by simp only [WScopedDflt]
  | _, some body, h => by
      simp only [wScopedDfltB] at h; simp only [WScopedDflt]; exact wScopedStmtsB_sound body h
end

/-! ### `FScopedStmts` — no function shadows a visible one -/

mutual
def fScopedStmtB (fdom : List Ident) : Stmt Op → Bool
  | .block body =>
      (funNames body).all (fun fn => decide (fn ∉ fdom)) && fScopedStmtsB (funNames body ++ fdom) body
  | .cond _ body =>
      (funNames body).all (fun fn => decide (fn ∉ fdom)) && fScopedStmtsB (funNames body ++ fdom) body
  | .funDef _ _ _ body =>
      (funNames body).all (fun fn => decide (fn ∉ fdom)) && fScopedStmtsB (funNames body ++ fdom) body
  | .switch _ cases dflt => fScopedCasesB fdom cases && fScopedDfltB fdom dflt
  | .forLoop init _ post body =>
      (funNames init).all (fun fn => decide (fn ∉ fdom)) &&
      fScopedStmtsB (funNames init ++ fdom) init &&
      ((funNames body).all (fun fn => decide (fn ∉ funNames init ++ fdom)) &&
        fScopedStmtsB (funNames body ++ funNames init ++ fdom) body) &&
      ((funNames post).all (fun fn => decide (fn ∉ funNames init ++ fdom)) &&
        fScopedStmtsB (funNames post ++ funNames init ++ fdom) post)
  | _ => true
def fScopedStmtsB (fdom : List Ident) : List (Stmt Op) → Bool
  | [] => true
  | s :: rest => fScopedStmtB fdom s && fScopedStmtsB fdom rest
def fScopedCasesB (fdom : List Ident) : List (Literal × List (Stmt Op)) → Bool
  | [] => true
  | (_, body) :: rest =>
      ((funNames body).all (fun fn => decide (fn ∉ fdom)) &&
        fScopedStmtsB (funNames body ++ fdom) body) && fScopedCasesB fdom rest
def fScopedDfltB (fdom : List Ident) : Option (List (Stmt Op)) → Bool
  | none => true
  | some body =>
      (funNames body).all (fun fn => decide (fn ∉ fdom)) && fScopedStmtsB (funNames body ++ fdom) body
end

mutual
theorem fScopedStmtB_sound : ∀ {fdom : List Ident} (s : Stmt Op),
    fScopedStmtB fdom s = true → FScopedStmt fdom s
  | _, .block body, h => by
      simp only [fScopedStmtB, Bool.and_eq_true] at h
      simp only [FScopedStmt]; exact ⟨all_notMemB_sound h.1, fScopedStmtsB_sound body h.2⟩
  | _, .cond _ body, h => by
      simp only [fScopedStmtB, Bool.and_eq_true] at h
      simp only [FScopedStmt]; exact ⟨all_notMemB_sound h.1, fScopedStmtsB_sound body h.2⟩
  | _, .funDef _ _ _ body, h => by
      simp only [fScopedStmtB, Bool.and_eq_true] at h
      simp only [FScopedStmt]; exact ⟨all_notMemB_sound h.1, fScopedStmtsB_sound body h.2⟩
  | _, .switch _ cases dflt, h => by
      simp only [fScopedStmtB, Bool.and_eq_true] at h
      simp only [FScopedStmt]; exact ⟨fScopedCasesB_sound cases h.1, fScopedDfltB_sound dflt h.2⟩
  | _, .forLoop init _ post body, h => by
      simp only [fScopedStmtB, Bool.and_eq_true] at h
      simp only [FScopedStmt]
      exact ⟨all_notMemB_sound h.1.1.1, fScopedStmtsB_sound init h.1.1.2,
        ⟨all_notMemB_sound h.1.2.1, fScopedStmtsB_sound body h.1.2.2⟩,
        ⟨all_notMemB_sound h.2.1, fScopedStmtsB_sound post h.2.2⟩⟩
  | _, .letDecl _ _, _ => by simp only [FScopedStmt]
  | _, .assign _ _, _ => by simp only [FScopedStmt]
  | _, .exprStmt _, _ => by simp only [FScopedStmt]
  | _, .break, _ => by simp only [FScopedStmt]
  | _, .continue, _ => by simp only [FScopedStmt]
  | _, .leave, _ => by simp only [FScopedStmt]
theorem fScopedStmtsB_sound : ∀ {fdom : List Ident} (ss : List (Stmt Op)),
    fScopedStmtsB fdom ss = true → FScopedStmts fdom ss
  | _, [], _ => by simp only [FScopedStmts]
  | _, s :: rest, h => by
      simp only [fScopedStmtsB, Bool.and_eq_true] at h
      simp only [FScopedStmts]; exact ⟨fScopedStmtB_sound s h.1, fScopedStmtsB_sound rest h.2⟩
theorem fScopedCasesB_sound : ∀ {fdom : List Ident} (cs : List (Literal × List (Stmt Op))),
    fScopedCasesB fdom cs = true → FScopedCases fdom cs
  | _, [], _ => by simp only [FScopedCases]
  | _, (_, body) :: rest, h => by
      simp only [fScopedCasesB, Bool.and_eq_true] at h
      simp only [FScopedCases]
      exact ⟨⟨all_notMemB_sound h.1.1, fScopedStmtsB_sound body h.1.2⟩, fScopedCasesB_sound rest h.2⟩
theorem fScopedDfltB_sound : ∀ {fdom : List Ident} (d : Option (List (Stmt Op))),
    fScopedDfltB fdom d = true → FScopedDflt fdom d
  | _, none, _ => by simp only [FScopedDflt]
  | _, some body, h => by
      simp only [fScopedDfltB, Bool.and_eq_true] at h
      simp only [FScopedDflt]; exact ⟨all_notMemB_sound h.1, fScopedStmtsB_sound body h.2⟩
end

/-! ### The bundle -/

/-- Decidable mirror of `SourceValid`. -/
def sourceValidB (b : Block Op) : Bool :=
  svStmtsB b && wellFormedB b && nfWellScopedB b &&
    wScopedStmtsB [] b && fScopedStmtsB (funNames b) b

/-- **Soundness of the decidable guard**: whatever `sourceValidB` accepts really
is `SourceValid`, so a pass guarded on `sourceValidB` runs `disambiguate` only
where its conditional soundness theorem applies. -/
theorem sourceValidB_sound {b : Block Op} (h : sourceValidB b = true) : SourceValid b := by
  simp only [sourceValidB, Bool.and_eq_true] at h
  exact ⟨svStmtsB_sound b h.1.1.1.1, wellFormedB_sound h.1.1.1.2,
    nfWellScopedB_sound h.1.1.2, wScopedStmtsB_sound b h.1.2, fScopedStmtsB_sound b h.2⟩

end YulEvmCompiler.Optimizer.Normalize
