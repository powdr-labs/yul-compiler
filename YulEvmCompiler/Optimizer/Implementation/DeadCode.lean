import YulEvmCompiler.Optimizer.Spec.Pass
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
whose `e` is side-effect-free, recursing into every nested block / function body /
loop so dead temporaries inside functions are removed too. It leaves all other
structure — including declared-variable lists and `for`-loop `init` — intact. -/

/-- Is `s` a removable dead `let` at the head of `rest`: a single-variable,
side-effect-free initialiser whose variable is unused in `rest`? -/
def removable : Stmt Op → List (Stmt Op) → Bool
  | .letDecl [x] (some e), rest => SideEffectFree e && !stmtsMentions x rest
  | _, _ => false

mutual
/-- Remove dead `let`s inside a single statement's sub-blocks. -/
def dceStmt : Stmt Op → Stmt Op
  | .block body => .block (dceStmts body)
  | .funDef n ps rs body => .funDef n ps rs (dceStmts body)
  | .cond c body => .cond c (dceStmts body)
  | .switch c cases dflt => .switch c (dceCases cases) (dceDflt dflt)
  | .forLoop init c post body => .forLoop (dceStmts init) c (dceStmts post) (dceStmts body)
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
/-- Remove dead `let`s from each `switch` case body. -/
def dceCases : List (Literal × List (Stmt Op)) → List (Literal × List (Stmt Op))
  | [] => []
  | (l, b) :: rest => (l, dceStmts b) :: dceCases rest
/-- Remove dead `let`s from a `switch` default block. -/
def dceDflt : Option (List (Stmt Op)) → Option (List (Stmt Op))
  | none => none
  | some b => some (dceStmts b)
end

/-! ### `dce` never introduces a mention

The transformation only deletes statements and recurses, so a variable unmentioned
by `ss` stays unmentioned by `dceStmts ss`. -/

mutual
theorem dceStmt_mentions {x : Ident} : ∀ {s : Stmt Op}, stmtMentions x s = false →
    stmtMentions x (dceStmt s) = false
  | .block _, h => by simpa only [dceStmt, stmtMentions] using dceStmts_mentions (by simpa only [stmtMentions] using h)
  | .funDef _ ps rs _, h => by
      simp only [dceStmt, stmtMentions, Bool.or_eq_false_iff] at h ⊢
      exact ⟨h.1, dceStmts_mentions h.2⟩
  | .cond _ _, h => by
      simp only [dceStmt, stmtMentions, Bool.or_eq_false_iff] at h ⊢
      exact ⟨h.1, dceStmts_mentions h.2⟩
  | .switch _ _ _, h => by
      simp only [dceStmt, stmtMentions, Bool.or_eq_false_iff] at h ⊢
      exact ⟨⟨h.1.1, dceCases_mentions h.1.2⟩, dceDflt_mentions h.2⟩
  | .forLoop _ _ _ _, h => by
      simp only [dceStmt, stmtMentions, Bool.or_eq_false_iff] at h ⊢
      exact ⟨⟨⟨dceStmts_mentions h.1.1.1, h.1.1.2⟩, dceStmts_mentions h.1.2⟩,
        dceStmts_mentions h.2⟩
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
theorem dceCases_mentions {x : Ident} : ∀ {cs : List (Literal × List (Stmt Op))},
    casesMentions x cs = false → casesMentions x (dceCases cs) = false
  | [], h => h
  | (_, _) :: rest, h => by
      simp only [casesMentions, Bool.or_eq_false_iff] at h
      simp only [dceCases, casesMentions, Bool.or_eq_false_iff]
      exact ⟨dceStmts_mentions h.1, dceCases_mentions h.2⟩
theorem dceDflt_mentions {x : Ident} : ∀ {dflt : Option (List (Stmt Op))},
    optBlockMentions x dflt = false → optBlockMentions x (dceDflt dflt) = false
  | none, h => h
  | some _, h => by simpa only [dceDflt, optBlockMentions] using dceStmts_mentions (by simpa only [optBlockMentions] using h)
end

end YulEvmCompiler.Optimizer
