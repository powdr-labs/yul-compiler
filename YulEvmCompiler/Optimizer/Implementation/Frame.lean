import YulSemantics.Equiv

/-!
# YulEvmCompiler.Optimizer.Implementation.Frame

The **VEnv frame lemma**: a variable that a program never mentions can be freely
inserted into (or removed from) the variable environment without changing
execution. This is the foundation for dead-code elimination (drop a `let x := e`
whose `x` is unused and whose `e` is side-effect-free) and, later, copy
propagation.

`mentions x s` is a syntactic over-approximation of "s reads, writes, or declares
`x`". If `mentions x ss = false`, then an environment carrying an extra binding
`(x,v)` runs `ss` exactly as the environment without it — captured by the
insertion relation `VEnv.InsAt` and threaded through the big-step judgment.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics

variable {D : Dialect} [DecidableEq D.Value]

/-! ### Syntactic "mentions" -/

mutual
/-- Does `x` occur (read) in an expression? -/
def exprMentions (x : Ident) : Expr D.Op → Bool
  | .lit _ => false
  | .var y => x = y
  | .builtin _ args => argsMentions x args
  | .call _ args => argsMentions x args
/-- Does `x` occur in any of an argument list? -/
def argsMentions (x : Ident) : List (Expr D.Op) → Bool
  | [] => false
  | e :: rest => exprMentions x e || argsMentions x rest
end

mutual
/-- Does `x` occur (read, written, or declared) in a statement? -/
def stmtMentions (x : Ident) : Stmt D.Op → Bool
  | .block body => stmtsMentions x body
  | .funDef _ ps rs body => (x ∈ ps) || (x ∈ rs) || stmtsMentions x body
  | .letDecl vars val => (x ∈ vars) || (match val with | some e => exprMentions x e | none => false)
  | .assign vars val => (x ∈ vars) || exprMentions x val
  | .cond c body => exprMentions x c || stmtsMentions x body
  | .switch c cases dflt =>
      exprMentions x c || casesMentions x cases ||
        (match dflt with | some b => stmtsMentions x b | none => false)
  | .forLoop init c post body =>
      stmtsMentions x init || exprMentions x c || stmtsMentions x post || stmtsMentions x body
  | .exprStmt e => exprMentions x e
  | .«break» => false
  | .«continue» => false
  | .leave => false
/-- Does `x` occur in a statement sequence? -/
def stmtsMentions (x : Ident) : List (Stmt D.Op) → Bool
  | [] => false
  | s :: rest => stmtMentions x s || stmtsMentions x rest
/-- Does `x` occur in any `switch` case body? -/
def casesMentions (x : Ident) : List (Literal × List (Stmt D.Op)) → Bool
  | [] => false
  | (_, b) :: rest => stmtsMentions x b || casesMentions x rest
end

/-! ### The insertion relation

`Ins x v V1 V2` holds when `V2` is `V1` with one extra binding `(x,v)` spliced in
at some depth, with `x` fresh everywhere in `V1`. Execution only pushes above the
splice and updates entries in place, so the relation is preserved throughout — and
scope restoration drops the same prefix on both sides. -/

/-- `V2` is `V1` with `(x,v)` inserted at some depth (`x` fresh in `V1`). -/
def Ins (x : Ident) (v : D.Value) (V1 V2 : VEnv D) : Prop :=
  ∃ above below : VEnv D,
    V1 = above ++ below ∧ V2 = above ++ (x, v) :: below ∧
    x ∉ above.map Prod.fst ∧ x ∉ below.map Prod.fst

theorem Ins.length {x v} {V1 V2 : VEnv D} (h : Ins x v V1 V2) : V2.length = V1.length + 1 := by
  obtain ⟨a, b, rfl, rfl, _, _⟩ := h; simp only [List.length_append, List.length_cons]; omega

/-- Reading any variable but `x` is unaffected. -/
theorem Ins.get_ne {x v} {V1 V2 : VEnv D} (h : Ins x v V1 V2) {z : Ident} (hz : z ≠ x) :
    V2.get z = V1.get z := by
  obtain ⟨a, b, rfl, rfl, ha, _⟩ := h
  induction a with
  | nil =>
      simp only [List.nil_append, VEnv.get]
      rw [List.find?_cons_of_neg (by simp [Ne.symm hz])]
  | cons p rest ih =>
      simp only [List.map_cons, List.mem_cons, not_or] at ha
      simp only [List.cons_append, VEnv.get]
      by_cases hp : p.1 = z
      · rw [List.find?_cons_of_pos (by simp [hp]), List.find?_cons_of_pos (by simp [hp])]
      · rw [List.find?_cons_of_neg (by simp [hp]), List.find?_cons_of_neg (by simp [hp])]
        exact ih ha.2

/-- `set` updates a value, never a key, so it preserves the key list. -/
theorem VEnv.set_keys (V : VEnv D) (z : Ident) (w : D.Value) :
    (V.set z w).map Prod.fst = V.map Prod.fst := by
  induction V with
  | nil => rfl
  | cons p rest ih =>
      simp only [VEnv.set]
      by_cases hp : p.1 = z
      · simp [hp]
      · simp only [hp, if_false, List.map_cons, ih]

/-- Writing any variable but `x` preserves the relation. -/
theorem Ins.set {x v} {V1 V2 : VEnv D} (h : Ins x v V1 V2) {z : Ident} (hz : z ≠ x) (w : D.Value) :
    Ins x v (V1.set z w) (V2.set z w) := by
  obtain ⟨a, b, rfl, rfl, ha, hb⟩ := h
  induction a with
  | nil =>
      refine ⟨[], b.set z w, by simp [VEnv.set], ?_, by simp, by rw [VEnv.set_keys]; exact hb⟩
      simp only [List.nil_append, VEnv.set, if_neg (Ne.symm hz)]
  | cons p rest ih =>
      simp only [List.map_cons, List.mem_cons, not_or] at ha
      by_cases hp : p.1 = z
      · refine ⟨(z, w) :: rest, b, ?_, ?_, ?_, hb⟩
        · simp only [List.cons_append, VEnv.set, if_pos hp]
        · simp only [List.cons_append, VEnv.set, if_pos hp]
        · simp only [List.map_cons, List.mem_cons, not_or]
          exact ⟨hp ▸ ha.1, ha.2⟩
      · obtain ⟨a', b', h1, h2, ha', hb'⟩ := ih ha.2
        refine ⟨p :: a', b', ?_, ?_, ?_, hb'⟩
        · simp only [List.cons_append, VEnv.set, if_neg hp]; rw [h1]
        · simp only [List.cons_append, VEnv.set, if_neg hp]; rw [h2]
        · simp only [List.map_cons, List.mem_cons, not_or]; exact ⟨ha.1, ha'⟩

/-- Prepending the same bindings (with `x` fresh) preserves the relation. -/
theorem Ins.prepend {x v} {V1 V2 : VEnv D} (h : Ins x v V1 V2) (pre : VEnv D)
    (hpre : x ∉ pre.map Prod.fst) : Ins x v (pre ++ V1) (pre ++ V2) := by
  obtain ⟨a, b, rfl, rfl, ha, hb⟩ := h
  refine ⟨pre ++ a, b, by simp, by simp, ?_, hb⟩
  simp only [List.map_append, List.mem_append, not_or]; exact ⟨hpre, ha⟩

/-! ### VEnv length lemmas and monotonicity

The semantics leaves "execution only prepends and updates in place" implicit
(see `restore`'s docstring). We make the length half of it explicit: a statement
never shrinks the environment, so `restore` keeps exactly the outer frame. -/

theorem VEnv.set_length (V : VEnv D) (z : Ident) (w : D.Value) :
    (V.set z w).length = V.length := by
  induction V with
  | nil => rfl
  | cons p rest ih =>
      simp only [VEnv.set]; by_cases hp : p.1 = z
      · simp [hp]
      · simp only [hp, if_false, List.length_cons, ih]

theorem VEnv.setMany_length (V : VEnv D) (xs : List Ident) (vs : List D.Value) :
    (V.setMany xs vs).length = V.length := by
  unfold VEnv.setMany
  induction xs.zip vs generalizing V with
  | nil => rfl
  | cons p rest ih => simp only [List.foldl_cons]; rw [ih]; exact VEnv.set_length _ _ _

theorem restore_length {outer inner : VEnv D} (h : outer.length ≤ inner.length) :
    (restore outer inner).length = outer.length := by
  simp only [restore, List.length_drop]; omega

/-- **VEnv length monotonicity**: executing a statement (sequence, loop) never
shrinks the environment. -/
theorem venvLen_mono {funs : FunEnv D} {V st code res} (h : Step D funs V st code res) :
    ∀ {V' st' o}, res = .sres V' st' o → V.length ≤ V'.length := by
  induction h with
  | lit | var | builtinOk | builtinHalt | builtinArgsHalt | callOk | callHalt | callArgsHalt
  | argsNil | argsCons | argsRestHalt | argsHeadHalt =>
      intro V' st' o heq; nomatch heq
  | funDef => intro V' st' o heq; injection heq with h1 _ _; subst h1; exact Nat.le_refl _
  | block _ ihb =>
      intro V' st' o heq; injection heq with h1 _ _; subst h1
      have he := restore_length (ihb rfl); omega
  | letZero => intro V' st' o heq; injection heq with h1 _ _; subst h1; simp only [bindZeros, List.length_append, List.length_map]; omega
  | letVal _ _ _ => intro V' st' o heq; injection heq with h1 _ _; subst h1; simp only [List.length_append]; omega
  | letHalt => intro V' st' o heq; injection heq with h1 _ _; subst h1; exact Nat.le_refl _
  | assignVal _ _ _ => intro V' st' o heq; injection heq with h1 _ _; subst h1; simp only [VEnv.setMany_length]; omega
  | assignHalt => intro V' st' o heq; injection heq with h1 _ _; subst h1; exact Nat.le_refl _
  | exprStmt => intro V' st' o heq; injection heq with h1 _ _; subst h1; exact Nat.le_refl _
  | exprStmtHalt => intro V' st' o heq; injection heq with h1 _ _; subst h1; exact Nat.le_refl _
  | ifTrue _ _ _ _ ihb => intro V' st' o heq; injection heq with h1 _ _; subst h1; exact ihb rfl
  | ifFalse => intro V' st' o heq; injection heq with h1 _ _; subst h1; exact Nat.le_refl _
  | ifHalt => intro V' st' o heq; injection heq with h1 _ _; subst h1; exact Nat.le_refl _
  | switchExec _ _ _ ihb => intro V' st' o heq; injection heq with h1 _ _; subst h1; exact ihb rfl
  | switchHalt => intro V' st' o heq; injection heq with h1 _ _; subst h1; exact Nat.le_refl _
  | forLoop _ _ ihinit ihloop =>
      intro V' st' o heq; injection heq with h1 _ _; subst h1
      have he := restore_length (Nat.le_trans (ihinit rfl) (ihloop rfl)); omega
  | forInitHalt _ ihinit => intro V' st' o heq; injection heq with h1 _ _; subst h1; have he := restore_length (ihinit rfl); omega
  | «break» => intro V' st' o heq; injection heq with h1 _ _; subst h1; exact Nat.le_refl _
  | «continue» => intro V' st' o heq; injection heq with h1 _ _; subst h1; exact Nat.le_refl _
  | leave => intro V' st' o heq; injection heq with h1 _ _; subst h1; exact Nat.le_refl _
  | seqNil => intro V' st' o heq; injection heq with h1 _ _; subst h1; exact Nat.le_refl _
  | seqCons _ _ ihs ihrest => intro V' st' o heq; injection heq with h1 _ _; subst h1; exact Nat.le_trans (ihs rfl) (ihrest rfl)
  | seqStop _ _ ihs => intro V' st' o heq; injection heq with h1 _ _; subst h1; exact ihs rfl
  | loopDone => intro V' st' o heq; injection heq with h1 _ _; subst h1; exact Nat.le_refl _
  | loopCondHalt => intro V' st' o heq; injection heq with h1 _ _; subst h1; exact Nat.le_refl _
  | loopStep _ _ _ _ _ _ _ ihb ihp ihr => intro V' st' o heq; injection heq with h1 _ _; subst h1; exact Nat.le_trans (ihb rfl) (Nat.le_trans (ihp rfl) (ihr rfl))
  | loopPostHalt _ _ _ _ _ _ ihb ihp => intro V' st' o heq; injection heq with h1 _ _; subst h1; exact Nat.le_trans (ihb rfl) (ihp rfl)
  | loopBreak _ _ _ _ ihb => intro V' st' o heq; injection heq with h1 _ _; subst h1; exact ihb rfl
  | loopLeave _ _ _ _ ihb => intro V' st' o heq; injection heq with h1 _ _; subst h1; exact ihb rfl
  | loopBodyHalt _ _ _ _ ihb => intro V' st' o heq; injection heq with h1 _ _; subst h1; exact ihb rfl

end YulEvmCompiler.Optimizer
