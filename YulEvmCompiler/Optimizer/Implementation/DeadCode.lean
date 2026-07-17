import YulEvmCompiler.Optimizer.Spec.Pass
import YulEvmCompiler.Optimizer.Spec.Scoped
import YulEvmCompiler.Optimizer.Implementation.Frame
import YulSemantics.Dialect.EVM

/-!
# YulEvmCompiler.Optimizer.Implementation.DeadCode

**Dead-`let` elimination.** Drops a `let x := e` whose bound variable `x` is
never used again and whose initialiser `e` is *side-effect-free* (it neither
writes state nor halts). Under the `WellScoped` precondition (`Spec/Scoped.lean`)
this is sound in both directions of the pointwise `EquivBlock`: well-scopedness
guarantees `e` still evaluates from every reachable environment, so removing the
`let` cannot turn a stuck program into a running one (the pathology that makes
binding-removal unsound in general — see `Spec/Scoped.lean`).

The soundness is carried by the **frame lemma** (`Implementation/Frame.lean`):
the dropped binding is invisible to the (unmentioning) rest of the block, and the
block's `restore` drops it on exit, so both programs reach the same result.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM

variable {calls : ExternalCalls} {creates : ExternalCreates}

local notation "D" => evmWithExternal calls creates

/-! ### Side-effect-free initialisers

The fragment of expressions safe to drop: those that always evaluate to a single
value with the state unchanged and never halt. Variables and literals qualify;
richer pure fragments (total non-halting built-ins over side-effect-free
arguments) can be added later — this covers the copy/const temporaries that
dominate `solc`'s `--via-ir` output. -/

/-- Side-effect-free (droppable) initialisers: variables and literals. -/
def SideEffectFree : Expr Op → Bool
  | .var _ => true
  | .lit _ => true
  | _ => false

/-! ### Evaluation adequacy under scoping -/

/-- A variable present in an environment's domain reads to some value. -/
theorem get_some_of_mem_dom {V : VEnv D} {y : Ident} (h : y ∈ V.map Prod.fst) :
    ∃ w, V.get y = some w := by
  induction V with
  | nil => simp at h
  | cons p rest ih =>
      simp only [List.map_cons, List.mem_cons] at h
      unfold VEnv.get
      by_cases hp : p.1 = y
      · rw [List.find?_cons_of_pos (by simp [hp])]; exact ⟨p.2, rfl⟩
      · rw [List.find?_cons_of_neg (by simp [hp])]
        rcases h with h | h
        · exact absurd h.symm hp
        · exact ih h

/-- **Evaluation adequacy.** A side-effect-free expression that is well-scoped in
`Γ`, run from an environment whose domain covers `Γ`, evaluates to a single value
with the state unchanged (and never halts). This is what makes dropping a dead
`let x := e` sound in the *backward* direction: the removed `e` still runs. -/
theorem sef_eval {Γ : List Ident} {e : Expr Op} {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    (hsef : SideEffectFree e = true) (hsc : ScopedExpr Γ e)
    (hdom : ∀ y ∈ Γ, y ∈ V.map Prod.fst) :
    ∃ w, Step D funs V st (.expr e) (.eres (.vals [w] st)) := by
  cases e with
  | lit l => exact ⟨litValue l, Step.lit⟩
  | var y =>
      obtain ⟨w, hw⟩ := get_some_of_mem_dom (hdom y hsc)
      exact ⟨w, Step.var hw⟩
  | builtin op args => simp [SideEffectFree] at hsef
  | call f args => simp [SideEffectFree] at hsef

/-! ### Statement-sequence append decomposition -/

/-- Executing `pre ++ suf` either runs `pre` to a `normal` outcome and then `suf`,
or `pre` short-circuits (a non-`normal` outcome) and `suf` never runs. -/
theorem stmts_append_fwd {funs : FunEnv D} {pre suf : List (Stmt Op)} {V st Vb st' o}
    (h : Step D funs V st (.stmts (pre ++ suf)) (.sres Vb st' o)) :
    (∃ V1 st1, Step D funs V st (.stmts pre) (.sres V1 st1 .normal) ∧
       Step D funs V1 st1 (.stmts suf) (.sres Vb st' o)) ∨
    (o ≠ .normal ∧ Step D funs V st (.stmts pre) (.sres Vb st' o)) := by
  induction pre generalizing V st with
  | nil => exact Or.inl ⟨V, st, Step.seqNil, h⟩
  | cons s pre' ih =>
      rw [List.cons_append] at h
      cases h with
      | seqCons hs htail =>
          rcases ih htail with ⟨V1, st1, hpre', hsuf⟩ | ⟨hne, hpre'⟩
          · exact Or.inl ⟨V1, st1, Step.seqCons hs hpre', hsuf⟩
          · exact Or.inr ⟨hne, Step.seqCons hs hpre'⟩
      | seqStop hs hne => exact Or.inr ⟨hne, Step.seqStop hs hne⟩

/-- Reassembling: `pre` to `normal` then `suf` runs `pre ++ suf`. -/
theorem stmts_append_normal {funs : FunEnv D} {pre suf : List (Stmt Op)} {V st V1 st1 Vb st' o}
    (hpre : Step D funs V st (.stmts pre) (.sres V1 st1 .normal))
    (hsuf : Step D funs V1 st1 (.stmts suf) (.sres Vb st' o)) :
    Step D funs V st (.stmts (pre ++ suf)) (.sres Vb st' o) := by
  induction pre generalizing V st with
  | nil => cases hpre with | seqNil => exact hsuf
  | cons s pre' ih =>
      cases hpre with
      | seqCons hs hpre' => exact Step.seqCons hs (ih hpre')
      | seqStop _ hne => exact absurd rfl hne

/-! ### Declared variables end up in the domain -/

theorem map_fst_zip_eq {α β} {vars : List α} {vals : List β} (h : vars.length = vals.length) :
    (vars.zip vals).map Prod.fst = vars := by
  induction vars generalizing vals with
  | nil => rfl
  | cons a t ih =>
      cases vals with
      | nil => simp at h
      | cons b s => simp only [List.zip_cons_cons, List.map_cons, ih (by simpa using h)]

/-- A single statement adds every variable it declares to the environment domain. -/
theorem stmt_declVars_dom {funs : FunEnv D} {V st s V1 st1}
    (h : Step D funs V st (.stmt s) (.sres V1 st1 .normal)) {y : Ident}
    (hy : y ∈ declVars s) : y ∈ V1.map Prod.fst := by
  cases h with
  | letZero =>
      simp only [declVars] at hy
      rw [List.map_append]
      refine List.mem_append_left _ ?_
      simp only [bindZeros, List.map_map, List.mem_map, Function.comp]
      exact ⟨y, hy, rfl⟩
  | letVal hv hlen =>
      simp only [declVars] at hy
      rw [List.map_append]
      exact List.mem_append_left _ (by rw [map_fst_zip_eq hlen.symm]; exact hy)
  | _ => simp [declVars] at hy

/-- After a normally-completing sequence, every top-level declared variable is in
the domain. -/
theorem stmts_declVars_dom {funs : FunEnv D} : ∀ {ss : List (Stmt Op)} {V st Vb st1},
    Step D funs V st (.stmts ss) (.sres Vb st1 .normal) → ∀ {y}, y ∈ declVarsList ss →
      y ∈ Vb.map Prod.fst := by
  intro ss
  induction ss with
  | nil => intro V st Vb st1 _ y hy; simp [declVarsList] at hy
  | cons s rest ih =>
      intro V st Vb st1 h y hy
      cases h with
      | seqCons hs htail =>
          simp only [declVarsList, List.flatMap_cons, List.mem_append] at hy
          rcases hy with hy | hy
          · exact dom_mono htail (stmt_declVars_dom hs hy)
          · exact ih htail hy
      | seqStop _ hne => exact absurd rfl hne

/-! ### The dead-`let` transformation

`dceStmts` drops a `let x := e` whose `x` is unused in the rest of its block and
whose `e` is side-effect-free, recursing into every nested block /
loop (function bodies are left for a follow-up: they need a function-environment
relation) so dead temporaries inside functions are removed too. It leaves all other
structure — including declared-variable lists and `for`-loop `init` — intact. -/

/-- Is `s` a removable dead `let` at the head of `rest`: a single-variable,
side-effect-free initialiser whose variable is unused in `rest`? -/
def removable : Stmt Op → List (Stmt Op) → Bool
  | .letDecl [x] (some e), rest => SideEffectFree e && !stmtsMentions x rest
  | _, _ => false

mutual
/-- Remove dead `let`s inside a single statement's sub-blocks. Recurses into
`block`/`cond`/`for` bodies (whose bodies run as their own scopes); `switch` and
`funDef` bodies are left unchanged (follow-ups: `switch` needs `selectSwitch` to
be handled by well-founded recursion, `funDef` needs a function-env relation). -/
def dceStmt : Stmt Op → Stmt Op
  | .block body => .block (dceStmts body)
  | .cond c body => .cond c (dceStmts body)
  | .forLoop init c post body => .forLoop init c post body
  | .funDef n ps rs body => .funDef n ps rs body
  | .switch c cases dflt => .switch c cases dflt
  | .letDecl xs val => .letDecl xs val
  | .assign xs val => .assign xs val
  | .exprStmt e => .exprStmt e
  | .«break» => .«break»
  | .«continue» => .«continue»
  | .leave => .leave
/-- Remove dead `let`s from a statement sequence (dropping a removable head,
otherwise recursing into the statement and the tail). -/
def dceStmts : List (Stmt Op) → List (Stmt Op)
  | [] => []
  | s :: rest => if removable s rest then dceStmts rest else dceStmt s :: dceStmts rest
end

/-! ### `dce` never introduces a mention

The transformation only deletes statements and recurses, so a variable unmentioned
by `ss` stays unmentioned by `dceStmts ss`. -/

mutual
theorem dceStmt_mentions {x : Ident} : ∀ {s : Stmt Op}, stmtMentions x s = false →
    stmtMentions x (dceStmt s) = false
  | .block _, h => by simpa only [dceStmt, stmtMentions] using dceStmts_mentions (by simpa only [stmtMentions] using h)
  | .funDef _ _ _ _, h => h
  | .cond _ _, h => by
      simp only [dceStmt, stmtMentions, Bool.or_eq_false_iff] at h ⊢
      exact ⟨h.1, dceStmts_mentions h.2⟩
  | .switch _ _ _, h => h
  | .forLoop _ _ _ _, h => h
  | .letDecl _ _, h => h
  | .assign _ _, h => h
  | .exprStmt _, h => h
  | .«break», h => h
  | .«continue», h => h
  | .leave, h => h
theorem dceStmts_mentions {x : Ident} : ∀ {ss : List (Stmt Op)}, stmtsMentions x ss = false →
    stmtsMentions x (dceStmts ss) = false
  | [], h => h
  | s :: rest, h => by
      have hs : stmtMentions x s = false ∧ stmtsMentions x rest = false := by
        simpa only [stmtsMentions, Bool.or_eq_false_iff] using h
      simp only [dceStmts]
      split
      · exact dceStmts_mentions hs.2
      · simp only [stmtsMentions, Bool.or_eq_false_iff]
        exact ⟨dceStmt_mentions hs.1, dceStmts_mentions hs.2⟩
end

/-! ### The pass preserves well-scopedness

Removing a dead `let x := e` drops `x` from the scope of the rest of its block —
but the rest never reads `x` (it is dead), so scoping is preserved. The engine is
a "drop an unmentioned variable from the middle of the context" lemma. -/

theorem mem_of_ne_mid {α} {y x : α} {Γ₁ Γ₂ : List α} (h : y ∈ Γ₁ ++ x :: Γ₂) (hne : y ≠ x) :
    y ∈ Γ₁ ++ Γ₂ := by
  rw [List.mem_append] at h ⊢
  rcases h with h | h
  · exact Or.inl h
  · rw [List.mem_cons] at h
    rcases h with h | h
    · exact absurd h hne
    · exact Or.inr h

theorem not_mem_declVars {x : Ident} {s : Stmt Op} (h : stmtMentions x s = false) :
    x ∉ declVars s := by
  cases s with
  | letDecl vars val =>
      simp only [stmtMentions, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
      simpa only [declVars] using h.1
  | _ => simp [declVars]

theorem not_mem_declVarsList {x : Ident} {ss : List (Stmt Op)} (h : stmtsMentions x ss = false) :
    x ∉ declVarsList ss := by
  induction ss with
  | nil => simp [declVarsList]
  | cons s rest ih =>
      simp only [stmtsMentions, Bool.or_eq_false_iff] at h
      simp only [declVarsList, List.flatMap_cons, List.mem_append, not_or]
      exact ⟨not_mem_declVars h.1, by simpa only [declVarsList] using ih h.2⟩

mutual
theorem ScopedExpr_erase {x Γ₁ Γ₂} : ∀ {e : Expr Op}, exprMentions x e = false →
    ScopedExpr (Γ₁ ++ x :: Γ₂) e → ScopedExpr (Γ₁ ++ Γ₂) e
  | .lit _, _, h => h
  | .var y, hm, h => by
      simp only [exprMentions, decide_eq_false_iff_not] at hm
      exact mem_of_ne_mid h (fun hy => hm hy.symm)
  | .builtin _ _, hm, h => ScopedArgs_erase (by simpa only [exprMentions] using hm) h
  | .call _ _, hm, h => ScopedArgs_erase (by simpa only [exprMentions] using hm) h
theorem ScopedArgs_erase {x Γ₁ Γ₂} : ∀ {es : List (Expr Op)}, argsMentions x es = false →
    ScopedArgs (Γ₁ ++ x :: Γ₂) es → ScopedArgs (Γ₁ ++ Γ₂) es
  | [], _, h => h
  | _ :: _, hm, h => by
      simp only [argsMentions, Bool.or_eq_false_iff] at hm
      exact ⟨ScopedExpr_erase hm.1 h.1, ScopedArgs_erase hm.2 h.2⟩
end

mutual
theorem ScopedStmt_erase {x Γ₁ Γ₂} : ∀ {s : Stmt Op}, stmtMentions x s = false →
    ScopedStmt (Γ₁ ++ x :: Γ₂) s → ScopedStmt (Γ₁ ++ Γ₂) s
  | .block _, hm, h => ScopedStmts_erase (by simpa only [stmtMentions] using hm) h
  | .funDef _ _ _ _, _, h => h
  | .letDecl _ _, hm, h => by
      simp only [stmtMentions, Bool.or_eq_false_iff] at hm
      exact ScopedOptExpr_erase hm.2 h
  | .assign vars _, hm, h => by
      simp only [stmtMentions, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hm
      refine ⟨fun z hz => mem_of_ne_mid (h.1 z hz) (fun hzx => hm.1 (hzx ▸ hz)), ?_⟩
      exact ScopedExpr_erase hm.2 h.2
  | .cond _ _, hm, h => by
      simp only [stmtMentions, Bool.or_eq_false_iff] at hm
      exact ⟨ScopedExpr_erase hm.1 h.1, ScopedStmts_erase hm.2 h.2⟩
  | .switch _ _ _, hm, h => by
      simp only [stmtMentions, Bool.or_eq_false_iff] at hm
      exact ⟨ScopedExpr_erase hm.1.1 h.1, ScopedCases_erase hm.1.2 h.2.1,
        ScopedOptBlock_erase hm.2 h.2.2⟩
  | .forLoop init _ _ _, hm, h => by
      simp only [stmtMentions, Bool.or_eq_false_iff] at hm
      have hxi : x ∉ declVarsList init := not_mem_declVarsList hm.1.1.1
      refine ⟨ScopedStmts_erase hm.1.1.1 h.1, ?_, ?_, ?_⟩
      · rw [← List.append_assoc]
        exact ScopedExpr_erase hm.1.1.2 (by rw [List.append_assoc]; exact h.2.1)
      · rw [← List.append_assoc]
        exact ScopedStmts_erase hm.1.2 (by rw [List.append_assoc]; exact h.2.2.1)
      · rw [← List.append_assoc]
        exact ScopedStmts_erase hm.2 (by rw [List.append_assoc]; exact h.2.2.2)
  | .exprStmt _, hm, h => ScopedExpr_erase (by simpa only [stmtMentions] using hm) h
  | .«break», _, h => h
  | .«continue», _, h => h
  | .leave, _, h => h
theorem ScopedStmts_erase {x Γ₁ Γ₂} : ∀ {ss : List (Stmt Op)}, stmtsMentions x ss = false →
    ScopedStmts (Γ₁ ++ x :: Γ₂) ss → ScopedStmts (Γ₁ ++ Γ₂) ss
  | [], _, h => h
  | s :: rest, hm, h => by
      simp only [stmtsMentions, Bool.or_eq_false_iff] at hm
      refine ⟨ScopedStmt_erase hm.1 h.1, ?_⟩
      have hxs : x ∉ declVars s := not_mem_declVars hm.1
      rw [← List.append_assoc]
      exact ScopedStmts_erase hm.2 (by rw [List.append_assoc]; exact h.2)
theorem ScopedCases_erase {x Γ₁ Γ₂} : ∀ {cs : List (Literal × List (Stmt Op))},
    casesMentions x cs = false → ScopedCases (Γ₁ ++ x :: Γ₂) cs → ScopedCases (Γ₁ ++ Γ₂) cs
  | [], _, h => h
  | (_, _) :: _, hm, h => by
      simp only [casesMentions, Bool.or_eq_false_iff] at hm
      exact ⟨ScopedStmts_erase hm.1 h.1, ScopedCases_erase hm.2 h.2⟩
theorem ScopedOptExpr_erase {x Γ₁ Γ₂} : ∀ {val : Option (Expr Op)}, optExprMentions x val = false →
    ScopedOptExpr (Γ₁ ++ x :: Γ₂) val → ScopedOptExpr (Γ₁ ++ Γ₂) val
  | none, _, h => h
  | some _, hm, h => ScopedExpr_erase (by simpa only [optExprMentions] using hm) h
theorem ScopedOptBlock_erase {x Γ₁ Γ₂} : ∀ {dflt : Option (List (Stmt Op))},
    optBlockMentions x dflt = false → ScopedOptBlock (Γ₁ ++ x :: Γ₂) dflt →
      ScopedOptBlock (Γ₁ ++ Γ₂) dflt
  | none, _, h => h
  | some _, hm, h => ScopedStmts_erase (by simpa only [optBlockMentions] using hm) h
end

theorem dceStmt_declVars : ∀ (s : Stmt Op), declVars (dceStmt s) = declVars s := by
  intro s; cases s <;> rfl

mutual
/-- `dceStmt` preserves scoping. -/
theorem dceStmt_scoped {Γ} : ∀ {s : Stmt Op}, ScopedStmt Γ s → ScopedStmt Γ (dceStmt s)
  | .block _, h => dceStmts_scoped h
  | .funDef _ _ _ _, h => h
  | .cond _ _, h => ⟨h.1, dceStmts_scoped h.2⟩
  | .switch _ _ _, h => h
  | .forLoop _ _ _ _, h => h
  | .letDecl _ _, h => h
  | .assign _ _, h => h
  | .exprStmt _, h => h
  | .«break», h => h
  | .«continue», h => h
  | .leave, h => h
/-- `dceStmts` preserves scoping: removing a dead `let` drops its (unmentioned)
variable from the scope of the rest, which the rest never needed. -/
theorem dceStmts_scoped {Γ} : ∀ {ss : List (Stmt Op)}, ScopedStmts Γ ss →
    ScopedStmts Γ (dceStmts ss)
  | [], h => h
  | s :: rest, h => by
      simp only [dceStmts]
      by_cases hr : removable s rest
      · -- s is a removable dead `let [x] (some e)`; drop it
        simp only [hr, if_true]
        obtain ⟨x, e, rfl, hx⟩ : ∃ x e, s = .letDecl [x] (some e) ∧
            (SideEffectFree e && !stmtsMentions x rest) = true := by
          cases s with
          | letDecl vars val =>
              cases vars with
              | nil => simp [removable] at hr
              | cons a as =>
                  cases as with
                  | cons _ _ => simp [removable] at hr
                  | nil => cases val with
                    | none => simp [removable] at hr
                    | some e => exact ⟨a, e, rfl, hr⟩
          | _ => simp [removable] at hr
        -- rest is scoped in [x] ++ Γ; x unmentioned in rest ⇒ scoped in Γ
        have hxrest : stmtsMentions x rest = false := by
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hx; exact hx.2
        have hrest : ScopedStmts ([x] ++ Γ) rest := h.2
        exact dceStmts_scoped (ScopedStmts_erase (Γ₁ := []) hxrest hrest)
      · simp only [hr, if_false]
        refine ⟨dceStmt_scoped h.1, ?_⟩
        rw [dceStmt_declVars]; exact dceStmts_scoped h.2
end

/-! ### `restore` arithmetic for the simulation -/

theorem drop_append_len {α} : ∀ (l₁ l₂ : List α), (l₁ ++ l₂).drop l₁.length = l₂
  | [], l₂ => rfl
  | _ :: t, l₂ => by simpa using drop_append_len t l₂

/-- Restoring to `V` after restoring to a larger `V1` is just restoring to `V`. -/
theorem restore_restore {V V1 W : VEnv D} (h1 : V.length ≤ V1.length) (h2 : V1.length ≤ W.length) :
    restore V (restore V1 W) = restore V W := by
  simp only [restore, List.length_drop, List.drop_drop]
  congr 1
  omega

/-- Restoring past an inserted binding (at depth = base length) drops it: the two
sides of a dead-`let` removal restore equally. -/
theorem restore_insAt_eq {d x w} {V1 V2 : VEnv D} (h : InsAt d x w V1 V2) {base : VEnv D}
    (hb : base.length = d) : restore base V1 = restore base V2 := by
  obtain ⟨A, B, rfl, rfl, hBd⟩ := h
  have g1 : restore base (A ++ B) = B := by
    simp only [restore, List.length_append]
    rw [show A.length + B.length - base.length = A.length by omega, drop_append_len]
  have g2 : restore base (A ++ (x, w) :: B) = B := by
    have heq : A ++ (x, w) :: B = (A ++ [(x, w)]) ++ B := by simp
    rw [heq]
    simp only [restore]
    rw [show ((A ++ [(x, w)]) ++ B).length - base.length = (A ++ [(x, w)]).length by
      simp only [List.length_append, List.length_cons, List.length_nil]; omega]
    exact drop_append_len (A ++ [(x, w)]) B
  rw [g1, g2]

/-! ### Simulation helpers -/

/-- A side-effect-free expression leaves the state unchanged. -/
theorem sef_eval_inv {e : Expr Op} {funs : FunEnv D} {V st vals st1}
    (hsef : SideEffectFree e = true)
    (h : Step D funs V st (.expr e) (.eres (.vals vals st1))) : st1 = st := by
  cases e with
  | lit l => cases h; rfl
  | var y => cases h; rfl
  | builtin op args => simp [SideEffectFree] at hsef
  | call f args => simp [SideEffectFree] at hsef

/-- `dce` leaves function definitions (hence the hoisted function scope) unchanged. -/
theorem hoist_dceStmts : ∀ (ss : List (Stmt Op)), hoist D (dceStmts ss) = hoist D ss
  | [] => rfl
  | s :: rest => by
      have ih := hoist_dceStmts rest
      simp only [hoist] at ih ⊢
      simp only [dceStmts]
      by_cases hr : removable s rest <;> simp only [hr, if_true, if_false]
      · cases s with
        | letDecl vars val => simp only [List.filterMap_cons, ih]
        | _ => simp [removable] at hr
      · cases s <;> simp [dceStmt, List.filterMap_cons, ih]

/-! ### The soundness simulation (forward)

Running the dce'd program mirrors the original, up to the dead bindings the block
`restore` drops. Threaded with the scope→domain invariant so a removed
initialiser still evaluates. `dceStmt_fwd` gives the *identical* result for a
single statement (its sub-blocks restore to the same env); `dceStmts_fwd` gives a
`restore`-equal result for a sequence. -/

mutual
theorem dceStmt_fwd (s : Stmt Op) {funs : FunEnv D} {Γ V st V1 st1 o}
    (hsc : ScopedStmt Γ s) (hdom : ∀ y ∈ Γ, y ∈ V.map Prod.fst)
    (h : Step D funs V st (.stmt s) (.sres V1 st1 o)) :
    Step D funs V st (.stmt (dceStmt s)) (.sres V1 st1 o) := by
  cases s with
  | block body =>
      cases h with
      | block hbody =>
          obtain ⟨Vb', hstep', hres⟩ := dceStmts_fwd body hsc hdom hbody
          rw [← hoist_dceStmts body] at hstep'
          simp only [dceStmt]; rw [hres]; exact Step.block hstep'
  | cond c body =>
      simp only [dceStmt]
      cases h with
      | ifTrue hc hcv hbody =>
          cases hbody with
          | block hb =>
              obtain ⟨Vb', hstep', hres⟩ := dceStmts_fwd body hsc.2 hdom hb
              rw [← hoist_dceStmts body] at hstep'
              rw [hres]; exact Step.ifTrue hc hcv (Step.block hstep')
      | ifFalse hc hcv => exact Step.ifFalse hc hcv
      | ifHalt hc => exact Step.ifHalt hc
  | forLoop init c post body => simpa only [dceStmt] using h
  | funDef n ps rs body => simpa only [dceStmt] using h
  | switch c cs df => simpa only [dceStmt] using h
  | letDecl vars val => simpa only [dceStmt] using h
  | assign vars val => simpa only [dceStmt] using h
  | exprStmt e => simpa only [dceStmt] using h
  | «break» => simpa only [dceStmt] using h
  | «continue» => simpa only [dceStmt] using h
  | leave => simpa only [dceStmt] using h
theorem dceStmts_fwd (ss : List (Stmt Op)) {funs : FunEnv D} {Γ V st Vb st' o}
    (hsc : ScopedStmts Γ ss) (hdom : ∀ y ∈ Γ, y ∈ V.map Prod.fst)
    (h : Step D funs V st (.stmts ss) (.sres Vb st' o)) :
    ∃ Vb', Step D funs V st (.stmts (dceStmts ss)) (.sres Vb' st' o) ∧
      restore V Vb = restore V Vb' := by
  cases ss with
  | nil => cases h with | seqNil => exact ⟨V, Step.seqNil, rfl⟩
  | cons s rest =>
      by_cases hr : removable s rest
      · obtain ⟨x, e, rfl, hxr⟩ : ∃ x e, s = .letDecl [x] (some e) ∧
            (SideEffectFree e && !stmtsMentions x rest) = true := by
          cases s with
          | letDecl vars val =>
              cases vars with
              | nil => simp [removable] at hr
              | cons a as => cases as with
                | cons _ _ => simp [removable] at hr
                | nil => cases val with
                  | none => simp [removable] at hr
                  | some e => exact ⟨a, e, rfl, hr⟩
          | _ => simp [removable] at hr
        have hsef : SideEffectFree e = true := by
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hxr; exact hxr.1
        have hxrest : stmtsMentions x rest = false := by
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hxr; exact hxr.2
        simp only [dceStmts, hr, if_true]
        cases h with
        | seqCons hlet htail =>
            cases hlet with
            | @letVal _ _ _ _ _ vals st1 hexpr hlen =>
                obtain ⟨w, rfl⟩ : ∃ w, vals = [w] := by
                  cases vals with
                  | nil => simp at hlen
                  | cons w t => cases t with
                    | nil => exact ⟨w, rfl⟩
                    | cons _ _ => simp at hlen
                obtain rfl := sef_eval_inv hsef hexpr
                have hins : InsAt V.length x w V ((x, w) :: V) := ⟨[], V, rfl, rfl, rfl⟩
                rw [show ([x].zip [w] ++ V) = (x, w) :: V from by simp] at htail
                obtain ⟨r1, hstepV, hrel⟩ :=
                  frameRemove htail hins (by simpa only [codeMentions] using hxrest)
                obtain ⟨Vr, rfl, hinsr⟩ := hrel.sres_right
                have hscr : ScopedStmts Γ rest := ScopedStmts_erase (Γ₁ := []) hxrest hsc.2
                obtain ⟨Vb', htail', hres'⟩ := dceStmts_fwd rest hscr hdom hstepV
                exact ⟨Vb', htail', (restore_insAt_eq hinsr (base := V) rfl).symm.trans hres'⟩
        | seqStop hlet hne =>
            cases hlet with
            | letVal _ _ => exact absurd rfl hne
            | letHalt hexpr =>
                cases e with
                | lit _ => cases hexpr
                | var _ => cases hexpr
                | builtin _ _ => simp [SideEffectFree] at hsef
                | call _ _ => simp [SideEffectFree] at hsef
      · simp only [dceStmts, hr, if_false]
        cases h with
        | @seqCons _ _ _ _ _ V1 st1 _ _ _ hs htail =>
            have hs' := dceStmt_fwd s hsc.1 hdom hs
            have hdom1 : ∀ y ∈ declVars s ++ Γ, y ∈ V1.map Prod.fst := by
              intro y hy
              rcases List.mem_append.1 hy with h' | h'
              · exact stmt_declVars_dom hs h'
              · exact dom_mono hs (hdom y h')
            obtain ⟨Vb', htail', hres⟩ := dceStmts_fwd rest hsc.2 hdom1 htail
            refine ⟨Vb', Step.seqCons hs' htail', ?_⟩
            have hV1 : V.length ≤ V1.length := venvLen_mono hs rfl
            have hVb : V1.length ≤ Vb.length := venvLen_mono htail rfl
            have hVb' : V1.length ≤ Vb'.length := venvLen_mono htail' rfl
            rw [← restore_restore hV1 hVb, ← restore_restore hV1 hVb', hres]
        | seqStop hs hne =>
            exact ⟨_, Step.seqStop (dceStmt_fwd s hsc.1 hdom hs) hne, rfl⟩
end

/-! ### The soundness simulation (backward)

The mirror of the forward direction: a run of the dce'd program is realised by the
original, reconstructing each removed `let` (its side-effect-free initialiser still
evaluates, by `sef_eval`) via `frameAdd`. -/

mutual
theorem dceStmt_bwd (s : Stmt Op) {funs : FunEnv D} {Γ V st V1 st1 o}
    (hsc : ScopedStmt Γ s) (hdom : ∀ y ∈ Γ, y ∈ V.map Prod.fst)
    (h : Step D funs V st (.stmt (dceStmt s)) (.sres V1 st1 o)) :
    Step D funs V st (.stmt s) (.sres V1 st1 o) := by
  cases s with
  | block body =>
      simp only [dceStmt] at h
      cases h with
      | block hbody =>
          obtain ⟨Vborig, horig, hres⟩ := dceStmts_bwd body hsc hdom hbody
          rw [hoist_dceStmts body] at horig
          rw [← hres]; exact Step.block horig
  | cond c body =>
      simp only [dceStmt] at h
      cases h with
      | ifTrue hc hcv hbody =>
          cases hbody with
          | block hb =>
              obtain ⟨Vborig, horig, hres⟩ := dceStmts_bwd body hsc.2 hdom hb
              rw [hoist_dceStmts body] at horig
              rw [← hres]; exact Step.ifTrue hc hcv (Step.block horig)
      | ifFalse hc hcv => exact Step.ifFalse hc hcv
      | ifHalt hc => exact Step.ifHalt hc
  | forLoop init c post body => simpa only [dceStmt] using h
  | funDef n ps rs body => simpa only [dceStmt] using h
  | switch c cs df => simpa only [dceStmt] using h
  | letDecl vars val => simpa only [dceStmt] using h
  | assign vars val => simpa only [dceStmt] using h
  | exprStmt e => simpa only [dceStmt] using h
  | «break» => simpa only [dceStmt] using h
  | «continue» => simpa only [dceStmt] using h
  | leave => simpa only [dceStmt] using h
theorem dceStmts_bwd (ss : List (Stmt Op)) {funs : FunEnv D} {Γ V st Vb' st' o}
    (hsc : ScopedStmts Γ ss) (hdom : ∀ y ∈ Γ, y ∈ V.map Prod.fst)
    (h : Step D funs V st (.stmts (dceStmts ss)) (.sres Vb' st' o)) :
    ∃ Vb, Step D funs V st (.stmts ss) (.sres Vb st' o) ∧ restore V Vb = restore V Vb' := by
  cases ss with
  | nil => cases h with | seqNil => exact ⟨V, Step.seqNil, rfl⟩
  | cons s rest =>
      by_cases hr : removable s rest
      · obtain ⟨x, e, rfl, hxr⟩ : ∃ x e, s = .letDecl [x] (some e) ∧
            (SideEffectFree e && !stmtsMentions x rest) = true := by
          cases s with
          | letDecl vars val =>
              cases vars with
              | nil => simp [removable] at hr
              | cons a as => cases as with
                | cons _ _ => simp [removable] at hr
                | nil => cases val with
                  | none => simp [removable] at hr
                  | some e => exact ⟨a, e, rfl, hr⟩
          | _ => simp [removable] at hr
        have hsef : SideEffectFree e = true := by
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hxr; exact hxr.1
        have hxrest : stmtsMentions x rest = false := by
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hxr; exact hxr.2
        simp only [dceStmts, hr, if_true] at h
        have hscr : ScopedStmts Γ rest := ScopedStmts_erase (Γ₁ := []) hxrest hsc.2
        obtain ⟨Vr, horig, hres⟩ := dceStmts_bwd rest hscr hdom h
        obtain ⟨w, he⟩ := sef_eval (Γ := Γ) hsef hsc.1 hdom (st := st)
        have hins : InsAt V.length x w V ((x, w) :: V) := ⟨[], V, rfl, rfl, rfl⟩
        obtain ⟨res2, hstep2, hrel⟩ := frameAdd horig hins (by simpa only [codeMentions] using hxrest)
        obtain ⟨Vb2, rfl, hins2⟩ := hrel.sres
        have hletstep : Step D funs V st (.stmt (.letDecl [x] (some e))) (.sres ((x, w) :: V) st .normal) := by
          have hlv := Step.letVal he (vars := [x]) (by simp)
          rwa [show [x].zip [w] ++ V = (x, w) :: V from by simp] at hlv
        exact ⟨Vb2, Step.seqCons hletstep hstep2, (restore_insAt_eq hins2 (base := V) rfl).symm.trans hres⟩
      · simp only [dceStmts, hr, if_false] at h
        cases h with
        | @seqCons _ _ _ _ _ V1 st1 _ _ _ hs htail =>
            have hsorig := dceStmt_bwd s hsc.1 hdom hs
            have hdom1 : ∀ y ∈ declVars s ++ Γ, y ∈ V1.map Prod.fst := by
              intro y hy
              rcases List.mem_append.1 hy with h' | h'
              · exact stmt_declVars_dom hsorig h'
              · exact dom_mono hsorig (hdom y h')
            obtain ⟨Vr, hrest, hres⟩ := dceStmts_bwd rest hsc.2 hdom1 htail
            refine ⟨Vr, Step.seqCons hsorig hrest, ?_⟩
            have hV1 : V.length ≤ V1.length := venvLen_mono hsorig rfl
            have hVr : V1.length ≤ Vr.length := venvLen_mono hrest rfl
            have hVb' : V1.length ≤ Vb'.length := venvLen_mono htail rfl
            rw [← restore_restore hV1 hVr, ← restore_restore hV1 hVb', hres]
        | seqStop hs hne =>
            exact ⟨_, Step.seqStop (dceStmt_bwd s hsc.1 hdom hs) hne, rfl⟩
end

/-! ### The pass -/

/-- A well-scoped block is `EquivBlock`-equivalent to its dead-`let`-eliminated
form: the block `restore` erases the removed bindings, and the two simulations
give both implications. -/
theorem dceStmts_equivBlock (b : Block Op) (hb : WellScoped b) :
    EquivBlock D b (dceStmts b) := by
  intro funs V st V' st' o
  constructor
  · intro h
    cases h with
    | block hbody =>
        obtain ⟨Vb', hstep', hres⟩ := dceStmts_fwd b hb (by simp) hbody
        rw [← hoist_dceStmts b] at hstep'
        rw [hres]; exact Step.block hstep'
  · intro h
    cases h with
    | block hbody =>
        obtain ⟨Vb, horig, hres⟩ := dceStmts_bwd b hb (by simp) hbody
        rw [hoist_dceStmts b] at horig
        rw [← hres]; exact Step.block horig

/-- Dead-code elimination preserves whole-program behaviour on well-scoped input:
its `Run` results are exactly those of the source program. (Not packaged as a
`Pass`, whose `Sound` is unconditional; DCE's soundness is `WellScoped`-conditioned
— see the design note in `Spec/Scoped.lean`.) -/
theorem dceStmts_preservesRun (b : Block Op) (hb : WellScoped b) {st0 V' st' o} :
    Run D b st0 V' st' o ↔ Run D (dceStmts b) st0 V' st' o :=
  (dceStmts_equivBlock b hb).run_iff

mutual
/-- Run dead-code elimination on every code block of an object tree (top object
and every nested sub-object), leaving names and data segments intact. -/
def dceObject : Object Op → Object Op
  | .mk n code subs segs => .mk n (dceStmts code) (dceObjects subs) segs
/-- Run `dceObject` on each object of a list. -/
def dceObjects : List (Object Op) → List (Object Op)
  | [] => []
  | o :: rest => dceObject o :: dceObjects rest
end

@[simp] theorem dceObject_codeBlock (o : Object Op) :
    (dceObject o).codeBlock = dceStmts o.codeBlock := by
  cases o; rw [dceObject]; rfl

end YulEvmCompiler.Optimizer
