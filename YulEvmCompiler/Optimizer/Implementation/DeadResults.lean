import YulEvmCompiler.Optimizer.Implementation.DeadPure
set_option warningAsError true
/-!
# YulEvmCompiler.Optimizer.Implementation.DeadResults

Eliminate an unused zero-initialized result together with its adjacent nested
computation region when the region is statically total and state-preserving.
This is the shape left by statement-level call inlining when the caller ignores
a helper result.

At most one region is removed from each statement sequence per invocation.
The optimizer's fixed-point rounds expose and remove later regions without
forcing the simulation to combine a removal with an independently transformed
suffix.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM

variable {calls : ExternalCalls} {creates : ExternalCreates}

local notation "D" => evmWithExternal calls creates

mutual

def drStmt (bound : List Ident) : Stmt Op → Stmt Op
  | .block body => .block (drStmts bound body)
  | .funDef n ps rs body => .funDef n ps rs (drStmts (ps ++ rs) body)
  | .cond c body => .cond c (drStmts bound body)
  | .switch c cases dflt => .switch c (drCases bound cases) (drDflt bound dflt)
  | .forLoop init c post body =>
      .forLoop init c (drStmts bound post) (drStmts bound body)
  | s => s

def drStmts (bound : List Ident) : List (Stmt Op) → List (Stmt Op)
  | [] => []
  | .letDecl [sink] none :: .block body :: rest =>
      if removableResult bound sink body rest then rest
      else .letDecl [sink] none :: drStmts (sink :: bound) (.block body :: rest)
  | .letDecl xs val :: rest =>
      .letDecl xs val :: drStmts (xs ++ bound) rest
  | s :: rest => drStmt bound s :: drStmts bound rest

def drCases (bound : List Ident) : List (Literal × Block Op) → List (Literal × Block Op)
  | [] => []
  | (l, b) :: rest => (l, drStmts bound b) :: drCases bound rest

def drDflt (bound : List Ident) : Option (Block Op) → Option (Block Op)
  | none => none
  | some b => some (drStmts bound b)

end


theorem removableResult_inv {bound : List Ident} {sink : Ident}
    {body rest : Block Op} (h : removableResult bound sink body rest = true) :
    (discardStmts sink ⟨sink :: bound, [sink]⟩ body).isSome = true ∧
      stmtsMentions sink rest = false ∧ stmtsCallFree rest = true := by
  have hh := h
  simp only [removableResult, Bool.and_eq_true, Bool.not_eq_true'] at hh
  exact ⟨hh.1.1, hh.1.2, hh.2⟩

mutual

theorem drStmt_rel (bound : List Ident) : ∀ s : Stmt Op,
    DcRel bound (dpOut bound s) (.stmt s) (.stmt (drStmt bound s))
  | .block body => by
      obtain ⟨bx, h⟩ := drStmts_rel bound body
      exact .blockS h
  | .funDef n ps rs body => by
      obtain ⟨bx, h⟩ := drStmts_rel (ps ++ rs) body
      exact .funDefS h
  | .letDecl _ _ => .letS
  | .assign _ _ => .assignS
  | .cond c body => by
      obtain ⟨bx, h⟩ := drStmts_rel bound body
      exact .condS h
  | .switch c cases dflt =>
      .switchS (drCases_rel bound cases) (drDflt_rel bound dflt)
  | .forLoop init c post body => by
      obtain ⟨bp, hp⟩ := drStmts_rel bound post
      obtain ⟨bb, hb⟩ := drStmts_rel bound body
      exact .forS hp hb
  | .exprStmt _ => .exprStmtS
  | .break => .breakS
  | .continue => .continueS
  | .leave => .leaveS

theorem drStmts_rel (bound : List Ident) : ∀ ss : List (Stmt Op),
    ∃ b2, DcRel bound b2 (.stmts ss) (.stmts (drStmts bound ss))
  | [] => ⟨bound, .nilSS⟩
  | s :: rest => by
      cases s with
      | letDecl xs val =>
          cases xs with
          | nil =>
              simp only [drStmts]
              obtain ⟨b2, htail⟩ := drStmts_rel bound rest
              exact ⟨b2, .consSS .letS htail⟩
          | cons x xs =>
              cases xs with
              | cons y ys =>
                  simp only [drStmts]
                  obtain ⟨b2, htail⟩ := drStmts_rel ((x :: y :: ys) ++ bound) rest
                  exact ⟨b2, .consSS .letS htail⟩
              | nil =>
                  cases val with
                  | some e =>
                      simp only [drStmts]
                      obtain ⟨b2, htail⟩ := drStmts_rel (x :: bound) rest
                      exact ⟨b2, .consSS .letS htail⟩
                  | none =>
                      cases rest with
                      | nil =>
                          simp only [drStmts]
                          exact ⟨x :: bound, .consSS .letS .nilSS⟩
                      | cons next tail =>
                          cases next with
                          | block body =>
                              by_cases hrem : removableResult bound x body tail = true
                              · rw [drStmts, if_pos hrem]
                                obtain ⟨hcheck, hm, hcf⟩ := removableResult_inv hrem
                                exact ⟨dpOutStmts bound tail, .dropRegionSS hcheck hm hcf⟩
                              · rw [drStmts, if_neg hrem]
                                obtain ⟨b2, htail⟩ :=
                                  drStmts_rel (x :: bound) (.block body :: tail)
                                exact ⟨b2, .consSS .letS htail⟩
                          | funDef n ps rs body =>
                              simp only [drStmts]
                              obtain ⟨b2, htail⟩ :=
                                drStmts_rel (x :: bound) (.funDef n ps rs body :: tail)
                              exact ⟨b2, .consSS .letS htail⟩
                          | letDecl ys rhs =>
                              simp only [drStmts]
                              obtain ⟨b2, htail⟩ :=
                                drStmts_rel (x :: bound) (.letDecl ys rhs :: tail)
                              exact ⟨b2, .consSS .letS htail⟩
                          | assign ys rhs =>
                              simp only [drStmts]
                              obtain ⟨b2, htail⟩ :=
                                drStmts_rel (x :: bound) (.assign ys rhs :: tail)
                              exact ⟨b2, .consSS .letS htail⟩
                          | cond c body =>
                              simp only [drStmts]
                              obtain ⟨b2, htail⟩ :=
                                drStmts_rel (x :: bound) (.cond c body :: tail)
                              exact ⟨b2, .consSS .letS htail⟩
                          | switch c cases dflt =>
                              simp only [drStmts]
                              obtain ⟨b2, htail⟩ :=
                                drStmts_rel (x :: bound) (.switch c cases dflt :: tail)
                              exact ⟨b2, .consSS .letS htail⟩
                          | forLoop init c post body =>
                              simp only [drStmts]
                              obtain ⟨b2, htail⟩ := drStmts_rel (x :: bound)
                                (.forLoop init c post body :: tail)
                              exact ⟨b2, .consSS .letS htail⟩
                          | exprStmt e =>
                              simp only [drStmts]
                              obtain ⟨b2, htail⟩ :=
                                drStmts_rel (x :: bound) (.exprStmt e :: tail)
                              exact ⟨b2, .consSS .letS htail⟩
                          | «break» =>
                              simp only [drStmts]
                              obtain ⟨b2, htail⟩ := drStmts_rel (x :: bound) (.break :: tail)
                              exact ⟨b2, .consSS .letS htail⟩
                          | «continue» =>
                              simp only [drStmts]
                              obtain ⟨b2, htail⟩ :=
                                drStmts_rel (x :: bound) (.continue :: tail)
                              exact ⟨b2, .consSS .letS htail⟩
                          | leave =>
                              simp only [drStmts]
                              obtain ⟨b2, htail⟩ := drStmts_rel (x :: bound) (.leave :: tail)
                              exact ⟨b2, .consSS .letS htail⟩
      | block body =>
          simp only [drStmts]
          obtain ⟨b2, htail⟩ := drStmts_rel bound rest
          exact ⟨b2, .consSS (drStmt_rel bound (.block body)) htail⟩
      | funDef n ps rs body =>
          simp only [drStmts]
          obtain ⟨b2, htail⟩ := drStmts_rel bound rest
          exact ⟨b2, .consSS (drStmt_rel bound (.funDef n ps rs body)) htail⟩
      | assign xs e =>
          simp only [drStmts]
          obtain ⟨b2, htail⟩ := drStmts_rel bound rest
          exact ⟨b2, .consSS .assignS htail⟩
      | cond c body =>
          simp only [drStmts]
          obtain ⟨b2, htail⟩ := drStmts_rel bound rest
          exact ⟨b2, .consSS (drStmt_rel bound (.cond c body)) htail⟩
      | switch c cases dflt =>
          simp only [drStmts]
          obtain ⟨b2, htail⟩ := drStmts_rel bound rest
          exact ⟨b2, .consSS (drStmt_rel bound (.switch c cases dflt)) htail⟩
      | forLoop init c post body =>
          simp only [drStmts]
          obtain ⟨b2, htail⟩ := drStmts_rel bound rest
          exact ⟨b2, .consSS (drStmt_rel bound (.forLoop init c post body)) htail⟩
      | exprStmt e =>
          simp only [drStmts]
          obtain ⟨b2, htail⟩ := drStmts_rel bound rest
          exact ⟨b2, .consSS .exprStmtS htail⟩
      | «break» =>
          simp only [drStmts]
          obtain ⟨b2, htail⟩ := drStmts_rel bound rest
          exact ⟨b2, .consSS .breakS htail⟩
      | «continue» =>
          simp only [drStmts]
          obtain ⟨b2, htail⟩ := drStmts_rel bound rest
          exact ⟨b2, .consSS .continueS htail⟩
      | leave =>
          simp only [drStmts]
          obtain ⟨b2, htail⟩ := drStmts_rel bound rest
          exact ⟨b2, .consSS .leaveS htail⟩

theorem drCases_rel (bound : List Ident) : ∀ cs : List (Literal × Block Op),
    DcRel bound bound (.cases cs) (.cases (drCases bound cs))
  | [] => .casesNil
  | (l, b) :: rest => by
      obtain ⟨bx, hb⟩ := drStmts_rel bound b
      exact .casesCons hb (drCases_rel bound rest)

theorem drDflt_rel (bound : List Ident) : ∀ d : Option (Block Op),
    DcRel bound bound (.odflt d) (.odflt (drDflt bound d))
  | none => .odfltNone
  | some b => by
      obtain ⟨bx, hb⟩ := drStmts_rel bound b
      exact .odfltSome hb

end

/-- Dead read-only result-region elimination. -/
def deadResults : LocalPass D where
  run := drStmts []
  sound := fun b => by
    obtain ⟨b2, hrel⟩ := drStmts_rel [] b
    exact hrel.equivBlock

@[simp] theorem deadResults_run (b : Block Op) :
    (deadResults (calls := calls) (creates := creates)).run b = drStmts [] b := rfl

example : drStmts ["slot"]
    [.letDecl ["ignored"] none,
     .block
       [.letDecl ["word"] (some (.builtin .sload [.var "slot"])),
        .block
          [.letDecl ["value"] (some (.builtin .shr
            [.lit (.number 0), .var "word"])),
           .assign ["ignored"] (.var "value")]],
     .exprStmt (.builtin .sstore [.lit (.number 0), .lit (.number 1)])]
  = [.exprStmt (.builtin .sstore [.lit (.number 0), .lit (.number 1)])] := rfl

-- State-changing regions stay intact.
example : drStmts []
    [.letDecl ["ignored"] none,
     .block [.exprStmt (.builtin .sstore [.lit (.number 0), .lit (.number 1)])],
     .exprStmt (.builtin .stop [])]
  = [.letDecl ["ignored"] none,
     .block [.exprStmt (.builtin .sstore [.lit (.number 0), .lit (.number 1)])],
     .exprStmt (.builtin .stop [])] := rfl

end YulEvmCompiler.Optimizer
