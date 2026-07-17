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
  | .letDecl vars val => (x ∈ vars) || optExprMentions x val
  | .assign vars val => (x ∈ vars) || exprMentions x val
  | .cond c body => exprMentions x c || stmtsMentions x body
  | .switch c cases dflt =>
      exprMentions x c || casesMentions x cases || optBlockMentions x dflt
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
/-- Does `x` occur in an optional initialiser expression? (Named helper so that
`stmtMentions` contains no inline `match` — inline matches generate auxiliaries
that break kernel-checking of `simp`-rewritten hypotheses.) -/
def optExprMentions (x : Ident) : Option (Expr D.Op) → Bool
  | some e => exprMentions x e
  | none => false
/-- Does `x` occur in an optional block (a `switch` default)? -/
def optBlockMentions (x : Ident) : Option (List (Stmt D.Op)) → Bool
  | some b => stmtsMentions x b
  | none => false
end

/-! ### The insertion relation

`InsAt d x v V1 V2` holds when `V2` is `V1` with one extra binding `(x,v)` spliced
in at a fixed depth (`below.length = d`). Execution only pushes above the splice
and updates entries in place, so the relation is preserved throughout — and
crucially, tracking the depth `d` lets scope restoration drop the same prefix on
both sides (see `InsAt.restore`).

No freshness of `x` in `V1` is required: code that never *mentions* `x` neither
reads, writes, nor declares it, so an inserted `(x,v)` binding is invisible even
when it shadows an existing one. Dropping freshness keeps the tooling usable
without a no-shadowing side condition on the program. -/

/-- `V2` is `V1` with `(x,v)` inserted at depth `d` (i.e. with `d` bindings below
the splice). -/
def InsAt (d : Nat) (x : Ident) (v : D.Value) (V1 V2 : VEnv D) : Prop :=
  ∃ above below : VEnv D,
    V1 = above ++ below ∧ V2 = above ++ (x, v) :: below ∧ below.length = d

theorem InsAt.length {d x v} {V1 V2 : VEnv D} (h : InsAt d x v V1 V2) :
    V2.length = V1.length + 1 := by
  obtain ⟨a, b, rfl, rfl, _⟩ := h; simp only [List.length_append, List.length_cons]; omega

/-- Reading any variable but `x` is unaffected (the inserted `(x,v)` is skipped, and
any pre-existing entry for `z ≠ x` is found at the same position on both sides). -/
theorem InsAt.get_ne {d x v} {V1 V2 : VEnv D} (h : InsAt d x v V1 V2) {z : Ident} (hz : z ≠ x) :
    V2.get z = V1.get z := by
  obtain ⟨a, b, rfl, rfl, _⟩ := h
  induction a with
  | nil =>
      simp only [List.nil_append, VEnv.get]
      rw [List.find?_cons_of_neg (by simp [Ne.symm hz])]
  | cons p rest ih =>
      simp only [List.cons_append, VEnv.get]
      by_cases hp : p.1 = z
      · rw [List.find?_cons_of_pos (by simp [hp]), List.find?_cons_of_pos (by simp [hp])]
      · rw [List.find?_cons_of_neg (by simp [hp]), List.find?_cons_of_neg (by simp [hp])]
        exact ih

/-- `set` updates a value, never a key, so it preserves the length. -/
theorem VEnv.set_length (V : VEnv D) (z : Ident) (w : D.Value) :
    (V.set z w).length = V.length := by
  induction V with
  | nil => rfl
  | cons p rest ih =>
      simp only [VEnv.set]; by_cases hp : p.1 = z
      · simp [hp]
      · simp only [hp, if_false, List.length_cons, ih]

/-- Writing any variable but `x` preserves the relation (and its depth). -/
theorem InsAt.set {d x v} {V1 V2 : VEnv D} (h : InsAt d x v V1 V2) {z : Ident} (hz : z ≠ x)
    (w : D.Value) : InsAt d x v (V1.set z w) (V2.set z w) := by
  obtain ⟨a, b, rfl, rfl, hd⟩ := h
  induction a with
  | nil =>
      refine ⟨[], b.set z w, by simp [VEnv.set], ?_, by rw [VEnv.set_length]; exact hd⟩
      simp only [List.nil_append, VEnv.set, if_neg (Ne.symm hz)]
  | cons p rest ih =>
      by_cases hp : p.1 = z
      · exact ⟨(z, w) :: rest, b, by simp only [List.cons_append, VEnv.set, if_pos hp],
          by simp only [List.cons_append, VEnv.set, if_pos hp], hd⟩
      · obtain ⟨a', b', h1, h2, hd'⟩ := ih
        exact ⟨p :: a', b', by simp only [List.cons_append, VEnv.set, if_neg hp]; rw [h1],
          by simp only [List.cons_append, VEnv.set, if_neg hp]; rw [h2], hd'⟩

/-- Prepending the same bindings preserves the relation and depth. -/
theorem InsAt.prepend {d x v} {V1 V2 : VEnv D} (h : InsAt d x v V1 V2) (pre : VEnv D) :
    InsAt d x v (pre ++ V1) (pre ++ V2) := by
  obtain ⟨a, b, rfl, rfl, hd⟩ := h
  exact ⟨pre ++ a, b, by simp, by simp, hd⟩

/-! ### VEnv length lemmas and monotonicity

The semantics leaves "execution only prepends and updates in place" implicit
(see `restore`'s docstring). We make the length half of it explicit: a statement
never shrinks the environment, so `restore` keeps exactly the outer frame. -/

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

/-! ### The frame lemma

`x` unmentioned by `code` ⇒ executing `code` from `V1` and from `V2` (= `V1` with
`(x,v)` spliced in) stay in lock-step: expression results are identical, statement
results stay `Ins`-related, and `restore` drops the same frame on both sides. -/

/-- `x` does not occur in a `Code`. -/
def codeMentions (x : Ident) : Code D.Op → Bool
  | .expr e => exprMentions x e
  | .args es => argsMentions x es
  | .stmt s => stmtMentions x s
  | .stmts ss => stmtsMentions x ss
  | .loop c post body => exprMentions x c || stmtsMentions x post || stmtsMentions x body

/-! ### More `InsAt` preservation lemmas -/

/-- `setMany` over keys all `≠ x` preserves the relation and its depth. -/
theorem InsAt.setMany {d x v} {vars : List Ident} (hx : x ∉ vars) :
    ∀ (vals : List D.Value) {V1 V2 : VEnv D}, InsAt d x v V1 V2 →
      InsAt d x v (V1.setMany vars vals) (V2.setMany vars vals) := by
  induction vars with
  | nil => intro vals V1 V2 h; simpa [VEnv.setMany] using h
  | cons a rest ih =>
      simp only [List.mem_cons, not_or] at hx
      intro vals V1 V2 h
      cases vals with
      | nil => simpa [VEnv.setMany] using h
      | cons w ws =>
          have := ih hx.2 ws (h.set (Ne.symm hx.1) w)
          simpa only [VEnv.setMany, List.zip_cons_cons, List.foldl_cons] using this

/-- **Frame + restore.** If the entry environments and the body-exit environments
are both `InsAt d`-related (same depth `d`), so are the restored environments — the
depth index guarantees `restore` drops the same prefix on both sides. -/
theorem InsAt.restore {d x v} {Ve1 Ve2 Vb1 Vb2 : VEnv D}
    (hentry : InsAt d x v Ve1 Ve2) (hbody : InsAt d x v Vb1 Vb2) :
    InsAt d x v (restore Ve1 Vb1) (restore Ve2 Vb2) := by
  obtain ⟨A, B, hb1, hb2, hBd⟩ := hbody
  obtain ⟨Ae, Be, he1, he2, hBed⟩ := hentry
  have hk1 : Vb1.length - Ve1.length = A.length - Ae.length := by
    rw [hb1, he1]; simp only [List.length_append]; omega
  have hk2 : Vb2.length - Ve2.length = A.length - Ae.length := by
    rw [hb2, he2]; simp only [List.length_append, List.length_cons]; omega
  have hle : A.length - Ae.length ≤ A.length := Nat.sub_le _ _
  change InsAt d x v (Vb1.drop (Vb1.length - Ve1.length)) (Vb2.drop (Vb2.length - Ve2.length))
  rw [hk1, hk2, hb1, hb2, List.drop_append_of_le_length hle,
    List.drop_append_of_le_length hle]
  exact ⟨A.drop (A.length - Ae.length), B, rfl, rfl, hBd⟩

/-! ### Mentions helpers -/

theorem casesMentions_of_mem {x : Ident} :
    ∀ {cases : List (Literal × Block D.Op)}, casesMentions x cases = false →
      ∀ {p}, p ∈ cases → stmtsMentions x p.2 = false := by
  intro cases
  induction cases with
  | nil => intro _ p hp; simp at hp
  | cons q rest ih =>
      obtain ⟨lit, b⟩ := q
      intro h p hp
      simp only [casesMentions, Bool.or_eq_false_iff] at h
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact h.1
      · exact ih h.2 hp

theorem selectSwitch_not_mentions {x : Ident} {cv : D.Value}
    {cases : List (Literal × Block D.Op)} {dflt : Option (Block D.Op)}
    (hc : casesMentions x cases = false) (hd : optBlockMentions x dflt = false) :
    stmtsMentions x (selectSwitch D cv cases dflt) = false := by
  unfold selectSwitch
  cases hfind : cases.find? (fun p => decide (cv = D.litValue p.1)) with
  | some p => exact casesMentions_of_mem hc (List.mem_of_find?_eq_some hfind)
  | none =>
      cases dflt with
      | some b => simpa [optBlockMentions] using hd
      | none => rfl

/-! ### The result relation -/

/-- Relation on results: expression results equal; statement results `InsAt d`-related
with equal state and outcome. -/
def ResRelAt (d : Nat) (x : Ident) (v : D.Value) : Res D → Res D → Prop
  | .eres r1, .eres r2 => r1 = r2
  | .sres V1 st1 o1, .sres V2 st2 o2 => InsAt d x v V1 V2 ∧ st1 = st2 ∧ o1 = o2
  | _, _ => False

theorem ResRelAt.eres {d x v} {r : EResult D} {res2 : Res D}
    (h : ResRelAt d x v (.eres r) res2) : res2 = .eres r := by
  cases res2 with
  | eres r2 => simp only [ResRelAt] at h; rw [h]
  | sres => simp only [ResRelAt] at h

theorem ResRelAt.sres {d x v} {V1 : VEnv D} {st o} {res2 : Res D}
    (h : ResRelAt d x v (.sres V1 st o) res2) :
    ∃ V2, res2 = .sres V2 st o ∧ InsAt d x v V1 V2 := by
  cases res2 with
  | eres => simp only [ResRelAt] at h
  | sres V2 st2 o2 =>
      simp only [ResRelAt] at h
      obtain ⟨hins, rfl, rfl⟩ := h
      exact ⟨V2, rfl, hins⟩

theorem ResRelAt.eres_right {d x v} {res1 : Res D} {r : EResult D}
    (h : ResRelAt d x v res1 (.eres r)) : res1 = .eres r := by
  cases res1 with
  | eres r1 => simp only [ResRelAt] at h; rw [h]
  | sres => simp only [ResRelAt] at h

theorem ResRelAt.sres_right {d x v} {res1 : Res D} {V2 : VEnv D} {st o}
    (h : ResRelAt d x v res1 (.sres V2 st o)) :
    ∃ V1, res1 = .sres V1 st o ∧ InsAt d x v V1 V2 := by
  cases res1 with
  | eres => simp only [ResRelAt] at h
  | sres V1 st1 o1 =>
      simp only [ResRelAt] at h
      obtain ⟨hins, rfl, rfl⟩ := h
      exact ⟨V1, rfl, hins⟩

/-! ### The frame lemma (add direction)

Running `code` (which does not mention `x`) from `V2` — an environment carrying an
extra `(x,v)` binding at depth `d` — mirrors running it from `V1`: expression
results are identical, and statement results stay `InsAt d`-related. -/

theorem frameAdd {funs : FunEnv D} {V1 st code res1} (h : Step D funs V1 st code res1) :
    ∀ {d x v V2}, InsAt d x v V1 V2 → codeMentions x code = false →
      ∃ res2, Step D funs V2 st code res2 ∧ ResRelAt d x v res1 res2 := by
  induction h with
  | lit => intro d x v Vt hins hm; exact ⟨_, Step.lit, rfl⟩
  | @var _ _ _ y vv hv =>
      intro d x v Vt hins hm
      have hy : y ≠ x := by
        simp only [codeMentions, exprMentions, decide_eq_false_iff_not] at hm
        exact fun hc => hm hc.symm
      exact ⟨_, Step.var (by rw [hins.get_ne hy]; exact hv), rfl⟩
  | builtinOk hargs hb iha =>
      intro d x v Vt hins hm
      obtain ⟨r, hs, hr⟩ := iha hins (by simpa only [codeMentions, exprMentions] using hm)
      obtain rfl := hr.eres
      exact ⟨_, Step.builtinOk hs hb, rfl⟩
  | builtinHalt hargs hb iha =>
      intro d x v Vt hins hm
      obtain ⟨r, hs, hr⟩ := iha hins (by simpa only [codeMentions, exprMentions] using hm)
      obtain rfl := hr.eres
      exact ⟨_, Step.builtinHalt hs hb, rfl⟩
  | builtinArgsHalt hargs iha =>
      intro d x v Vt hins hm
      obtain ⟨r, hs, hr⟩ := iha hins (by simpa only [codeMentions, exprMentions] using hm)
      obtain rfl := hr.eres
      exact ⟨_, Step.builtinArgsHalt hs, rfl⟩
  | callOk hargs hl hlen hbody ho iha ihbody =>
      intro d x v Vt hins hm
      obtain ⟨r, hs, hr⟩ := iha hins (by simpa only [codeMentions, exprMentions] using hm)
      obtain rfl := hr.eres
      exact ⟨_, Step.callOk hs hl hlen hbody ho, rfl⟩
  | callHalt hargs hl hlen hbody iha ihbody =>
      intro d x v Vt hins hm
      obtain ⟨r, hs, hr⟩ := iha hins (by simpa only [codeMentions, exprMentions] using hm)
      obtain rfl := hr.eres
      exact ⟨_, Step.callHalt hs hl hlen hbody, rfl⟩
  | callArgsHalt hargs iha =>
      intro d x v Vt hins hm
      obtain ⟨r, hs, hr⟩ := iha hins (by simpa only [codeMentions, exprMentions] using hm)
      obtain rfl := hr.eres
      exact ⟨_, Step.callArgsHalt hs, rfl⟩
  | argsNil => intro d x v Vt hins hm; exact ⟨_, Step.argsNil, rfl⟩
  | argsCons hrest he ihrest ihe =>
      intro d x v Vt hins hm
      simp only [codeMentions, argsMentions, Bool.or_eq_false_iff] at hm
      obtain ⟨rr, hsr, hrr⟩ := ihrest hins (by simp only [codeMentions]; exact hm.2)
      obtain rfl := hrr.eres
      obtain ⟨re, hse, hre⟩ := ihe hins (by simp only [codeMentions]; exact hm.1)
      obtain rfl := hre.eres
      exact ⟨_, Step.argsCons hsr hse, rfl⟩
  | argsRestHalt hrest ihrest =>
      intro d x v Vt hins hm
      simp only [codeMentions, argsMentions, Bool.or_eq_false_iff] at hm
      obtain ⟨rr, hsr, hrr⟩ := ihrest hins (by simp only [codeMentions]; exact hm.2)
      obtain rfl := hrr.eres
      exact ⟨_, Step.argsRestHalt hsr, rfl⟩
  | argsHeadHalt hrest he ihrest ihe =>
      intro d x v Vt hins hm
      simp only [codeMentions, argsMentions, Bool.or_eq_false_iff] at hm
      obtain ⟨rr, hsr, hrr⟩ := ihrest hins (by simp only [codeMentions]; exact hm.2)
      obtain rfl := hrr.eres
      obtain ⟨re, hse, hre⟩ := ihe hins (by simp only [codeMentions]; exact hm.1)
      obtain rfl := hre.eres
      exact ⟨_, Step.argsHeadHalt hsr hse, rfl⟩
  | funDef => intro d x v Vt hins hm; exact ⟨_, Step.funDef, ⟨hins, rfl, rfl⟩⟩
  | block hbody ihbody =>
      intro d x v Vt hins hm
      simp only [codeMentions, stmtMentions] at hm
      obtain ⟨r, hs, hr⟩ := ihbody hins (by simp only [codeMentions]; exact hm)
      obtain ⟨Vb2, rfl, hins2⟩ := hr.sres
      exact ⟨_, Step.block hs, ⟨InsAt.restore hins hins2, rfl, rfl⟩⟩
  | letZero =>
      intro d x v Vt hins hm
      simp only [codeMentions, stmtMentions, optExprMentions, Bool.or_false,
        decide_eq_false_iff_not] at hm
      exact ⟨_, Step.letZero, ⟨hins.prepend _, rfl, rfl⟩⟩
  | letVal he hlen ihe =>
      intro d x v Vt hins hm
      simp only [codeMentions, stmtMentions, optExprMentions, Bool.or_eq_false_iff,
        decide_eq_false_iff_not] at hm
      obtain ⟨r, hs, hr⟩ := ihe hins (by simp only [codeMentions]; exact hm.2)
      obtain rfl := hr.eres
      exact ⟨_, Step.letVal hs hlen, ⟨hins.prepend _, rfl, rfl⟩⟩
  | letHalt he ihe =>
      intro d x v Vt hins hm
      simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hm
      obtain ⟨r, hs, hr⟩ := ihe hins (by simp only [codeMentions]; exact hm.2)
      obtain rfl := hr.eres
      exact ⟨_, Step.letHalt hs, ⟨hins, rfl, rfl⟩⟩
  | assignVal he hlen ihe =>
      intro d x v Vt hins hm
      simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hm
      obtain ⟨r, hs, hr⟩ := ihe hins (by simp only [codeMentions]; exact hm.2)
      obtain rfl := hr.eres
      exact ⟨_, Step.assignVal hs hlen, ⟨InsAt.setMany hm.1 _ hins, rfl, rfl⟩⟩
  | assignHalt he ihe =>
      intro d x v Vt hins hm
      simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hm
      obtain ⟨r, hs, hr⟩ := ihe hins (by simp only [codeMentions]; exact hm.2)
      obtain rfl := hr.eres
      exact ⟨_, Step.assignHalt hs, ⟨hins, rfl, rfl⟩⟩
  | exprStmt he ihe =>
      intro d x v Vt hins hm
      simp only [codeMentions, stmtMentions] at hm
      obtain ⟨r, hs, hr⟩ := ihe hins (by simp only [codeMentions]; exact hm)
      obtain rfl := hr.eres
      exact ⟨_, Step.exprStmt hs, ⟨hins, rfl, rfl⟩⟩
  | exprStmtHalt he ihe =>
      intro d x v Vt hins hm
      simp only [codeMentions, stmtMentions] at hm
      obtain ⟨r, hs, hr⟩ := ihe hins (by simp only [codeMentions]; exact hm)
      obtain rfl := hr.eres
      exact ⟨_, Step.exprStmtHalt hs, ⟨hins, rfl, rfl⟩⟩
  | ifTrue hc hcv hbody ihc ihbody =>
      intro d x v Vt hins hm
      simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hm
      obtain ⟨rc, hsc, hrc⟩ := ihc hins (by simp only [codeMentions]; exact hm.1)
      obtain rfl := hrc.eres
      obtain ⟨rb, hsb, hrb⟩ := ihbody hins (by simp only [codeMentions, stmtMentions]; exact hm.2)
      obtain ⟨V'2, rfl, hins2⟩ := hrb.sres
      exact ⟨_, Step.ifTrue hsc hcv hsb, ⟨hins2, rfl, rfl⟩⟩
  | ifFalse hc hcv ihc =>
      intro d x v Vt hins hm
      simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hm
      obtain ⟨rc, hsc, hrc⟩ := ihc hins (by simp only [codeMentions]; exact hm.1)
      obtain rfl := hrc.eres
      exact ⟨_, Step.ifFalse hsc hcv, ⟨hins, rfl, rfl⟩⟩
  | ifHalt hc ihc =>
      intro d x v Vt hins hm
      simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hm
      obtain ⟨rc, hsc, hrc⟩ := ihc hins (by simp only [codeMentions]; exact hm.1)
      obtain rfl := hrc.eres
      exact ⟨_, Step.ifHalt hsc, ⟨hins, rfl, rfl⟩⟩
  | switchExec hc hbody ihc ihbody =>
      intro d x v Vt hins hm
      simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hm
      obtain ⟨rc, hsc, hrc⟩ := ihc hins (by simp only [codeMentions]; exact hm.1.1)
      obtain rfl := hrc.eres
      obtain ⟨rb, hsb, hrb⟩ := ihbody hins (by
        simp only [codeMentions, stmtMentions]
        exact selectSwitch_not_mentions hm.1.2 hm.2)
      obtain ⟨V'2, rfl, hins2⟩ := hrb.sres
      exact ⟨_, Step.switchExec hsc hsb, ⟨hins2, rfl, rfl⟩⟩
  | switchHalt hc ihc =>
      intro d x v Vt hins hm
      simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hm
      obtain ⟨rc, hsc, hrc⟩ := ihc hins (by simp only [codeMentions]; exact hm.1.1)
      obtain rfl := hrc.eres
      exact ⟨_, Step.switchHalt hsc, ⟨hins, rfl, rfl⟩⟩
  | forLoop hinit hloop ihinit ihloop =>
      intro d x v Vt hins hm
      simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hm
      obtain ⟨⟨⟨h_si, h_ec⟩, h_sp⟩, h_sb⟩ := hm
      obtain ⟨ri, hsi, hri⟩ := ihinit hins (by simp only [codeMentions]; exact h_si)
      obtain ⟨Vi2, rfl, hinsi⟩ := hri.sres
      obtain ⟨rl, hsl, hrl⟩ := ihloop hinsi (by simp only [codeMentions, h_ec, h_sp, h_sb, Bool.or_false])
      obtain ⟨Ve2, rfl, hinsl⟩ := hrl.sres
      exact ⟨_, Step.forLoop hsi hsl, ⟨InsAt.restore hins hinsl, rfl, rfl⟩⟩
  | forInitHalt hinit ihinit =>
      intro d x v Vt hins hm
      simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hm
      obtain ⟨⟨⟨h_si, h_ec⟩, h_sp⟩, h_sb⟩ := hm
      obtain ⟨ri, hsi, hri⟩ := ihinit hins (by simp only [codeMentions]; exact h_si)
      obtain ⟨Vi2, rfl, hinsi⟩ := hri.sres
      exact ⟨_, Step.forInitHalt hsi, ⟨InsAt.restore hins hinsi, rfl, rfl⟩⟩
  | «break» => intro d x v Vt hins hm; exact ⟨_, Step.break, ⟨hins, rfl, rfl⟩⟩
  | «continue» => intro d x v Vt hins hm; exact ⟨_, Step.continue, ⟨hins, rfl, rfl⟩⟩
  | leave => intro d x v Vt hins hm; exact ⟨_, Step.leave, ⟨hins, rfl, rfl⟩⟩
  | seqNil => intro d x v Vt hins hm; exact ⟨_, Step.seqNil, ⟨hins, rfl, rfl⟩⟩
  | seqCons hs hrest ihs ihrest =>
      intro d x v Vt hins hm
      simp only [codeMentions, stmtsMentions, Bool.or_eq_false_iff] at hm
      obtain ⟨rs, hss, hrs⟩ := ihs hins (by simp only [codeMentions]; exact hm.1)
      obtain ⟨V1', rfl, hins1⟩ := hrs.sres
      obtain ⟨rr, hsr, hrr⟩ := ihrest hins1 (by simp only [codeMentions]; exact hm.2)
      obtain ⟨V2', rfl, hins2⟩ := hrr.sres
      exact ⟨_, Step.seqCons hss hsr, ⟨hins2, rfl, rfl⟩⟩
  | seqStop hs hne ihs =>
      intro d x v Vt hins hm
      simp only [codeMentions, stmtsMentions, Bool.or_eq_false_iff] at hm
      obtain ⟨rs, hss, hrs⟩ := ihs hins (by simp only [codeMentions]; exact hm.1)
      obtain ⟨V1', rfl, hins1⟩ := hrs.sres
      exact ⟨_, Step.seqStop hss hne, ⟨hins1, rfl, rfl⟩⟩
  | loopDone hc hcv ihc =>
      intro d x v Vt hins hm
      simp only [codeMentions, Bool.or_eq_false_iff] at hm
      obtain ⟨rc, hsc, hrc⟩ := ihc hins (by simp only [codeMentions]; exact hm.1.1)
      obtain rfl := hrc.eres
      exact ⟨_, Step.loopDone hsc hcv, ⟨hins, rfl, rfl⟩⟩
  | loopCondHalt hc ihc =>
      intro d x v Vt hins hm
      simp only [codeMentions, Bool.or_eq_false_iff] at hm
      obtain ⟨rc, hsc, hrc⟩ := ihc hins (by simp only [codeMentions]; exact hm.1.1)
      obtain rfl := hrc.eres
      exact ⟨_, Step.loopCondHalt hsc, ⟨hins, rfl, rfl⟩⟩
  | loopStep hc hcv hbody hob hpost hrec ihc ihbody ihpost ihrec =>
      intro d x v Vt hins hm
      simp only [codeMentions, Bool.or_eq_false_iff] at hm
      obtain ⟨⟨h_ec, h_sp⟩, h_sb⟩ := hm
      obtain ⟨rc, hsc, hrc⟩ := ihc hins (by simp only [codeMentions]; exact h_ec)
      obtain rfl := hrc.eres
      obtain ⟨rb, hsb, hrb⟩ := ihbody hins (by simp only [codeMentions, stmtMentions]; exact h_sb)
      obtain ⟨Vb2, rfl, hinsb⟩ := hrb.sres
      obtain ⟨rp, hsp, hrp⟩ := ihpost hinsb (by simp only [codeMentions, stmtMentions]; exact h_sp)
      obtain ⟨Vp2, rfl, hinsp⟩ := hrp.sres
      obtain ⟨rr, hsr, hrr⟩ := ihrec hinsp (by simp only [codeMentions, h_ec, h_sp, h_sb, Bool.or_false])
      obtain ⟨Ve2, rfl, hinsr⟩ := hrr.sres
      exact ⟨_, Step.loopStep hsc hcv hsb hob hsp hsr, ⟨hinsr, rfl, rfl⟩⟩
  | loopPostHalt hc hcv hbody hob hpost ihc ihbody ihpost =>
      intro d x v Vt hins hm
      simp only [codeMentions, Bool.or_eq_false_iff] at hm
      obtain ⟨⟨h_ec, h_sp⟩, h_sb⟩ := hm
      obtain ⟨rc, hsc, hrc⟩ := ihc hins (by simp only [codeMentions]; exact h_ec)
      obtain rfl := hrc.eres
      obtain ⟨rb, hsb, hrb⟩ := ihbody hins (by simp only [codeMentions, stmtMentions]; exact h_sb)
      obtain ⟨Vb2, rfl, hinsb⟩ := hrb.sres
      obtain ⟨rp, hsp, hrp⟩ := ihpost hinsb (by simp only [codeMentions, stmtMentions]; exact h_sp)
      obtain ⟨Vp2, rfl, hinsp⟩ := hrp.sres
      exact ⟨_, Step.loopPostHalt hsc hcv hsb hob hsp, ⟨hinsp, rfl, rfl⟩⟩
  | loopBreak hc hcv hbody ihc ihbody =>
      intro d x v Vt hins hm
      simp only [codeMentions, Bool.or_eq_false_iff] at hm
      obtain ⟨⟨h_ec, h_sp⟩, h_sb⟩ := hm
      obtain ⟨rc, hsc, hrc⟩ := ihc hins (by simp only [codeMentions]; exact h_ec)
      obtain rfl := hrc.eres
      obtain ⟨rb, hsb, hrb⟩ := ihbody hins (by simp only [codeMentions, stmtMentions]; exact h_sb)
      obtain ⟨Vb2, rfl, hinsb⟩ := hrb.sres
      exact ⟨_, Step.loopBreak hsc hcv hsb, ⟨hinsb, rfl, rfl⟩⟩
  | loopLeave hc hcv hbody ihc ihbody =>
      intro d x v Vt hins hm
      simp only [codeMentions, Bool.or_eq_false_iff] at hm
      obtain ⟨⟨h_ec, h_sp⟩, h_sb⟩ := hm
      obtain ⟨rc, hsc, hrc⟩ := ihc hins (by simp only [codeMentions]; exact h_ec)
      obtain rfl := hrc.eres
      obtain ⟨rb, hsb, hrb⟩ := ihbody hins (by simp only [codeMentions, stmtMentions]; exact h_sb)
      obtain ⟨Vb2, rfl, hinsb⟩ := hrb.sres
      exact ⟨_, Step.loopLeave hsc hcv hsb, ⟨hinsb, rfl, rfl⟩⟩
  | loopBodyHalt hc hcv hbody ihc ihbody =>
      intro d x v Vt hins hm
      simp only [codeMentions, Bool.or_eq_false_iff] at hm
      obtain ⟨⟨h_ec, h_sp⟩, h_sb⟩ := hm
      obtain ⟨rc, hsc, hrc⟩ := ihc hins (by simp only [codeMentions]; exact h_ec)
      obtain rfl := hrc.eres
      obtain ⟨rb, hsb, hrb⟩ := ihbody hins (by simp only [codeMentions, stmtMentions]; exact h_sb)
      obtain ⟨Vb2, rfl, hinsb⟩ := hrb.sres
      exact ⟨_, Step.loopBodyHalt hsc hcv hsb, ⟨hinsb, rfl, rfl⟩⟩

/-! ### The frame lemma (remove direction)

The mirror of `frameAdd`: running `code` (which does not mention `x`) from `V2` — an
environment carrying an extra `(x,v)` binding — can equally be run from `V1` (the
same environment without that binding), with `InsAt d`-related results. Together
`frameAdd`/`frameRemove` give the two implications behind `EquivStmts`. -/

theorem frameRemove {funs : FunEnv D} {V2 st code res2} (h : Step D funs V2 st code res2) :
    ∀ {d x v V1}, InsAt d x v V1 V2 → codeMentions x code = false →
      ∃ res1, Step D funs V1 st code res1 ∧ ResRelAt d x v res1 res2 := by
  induction h with
  | lit => intro d x v Vs hins hm; exact ⟨_, Step.lit, rfl⟩
  | @var _ _ _ y vv hv =>
      intro d x v Vs hins hm
      have hy : y ≠ x := by
        simp only [codeMentions, exprMentions, decide_eq_false_iff_not] at hm
        exact fun hc => hm hc.symm
      exact ⟨_, Step.var (hins.get_ne hy ▸ hv), rfl⟩
  | builtinOk hargs hb iha =>
      intro d x v Vs hins hm
      obtain ⟨r, hs, hr⟩ := iha hins (by simpa only [codeMentions, exprMentions] using hm)
      obtain rfl := hr.eres_right
      exact ⟨_, Step.builtinOk hs hb, rfl⟩
  | builtinHalt hargs hb iha =>
      intro d x v Vs hins hm
      obtain ⟨r, hs, hr⟩ := iha hins (by simpa only [codeMentions, exprMentions] using hm)
      obtain rfl := hr.eres_right
      exact ⟨_, Step.builtinHalt hs hb, rfl⟩
  | builtinArgsHalt hargs iha =>
      intro d x v Vs hins hm
      obtain ⟨r, hs, hr⟩ := iha hins (by simpa only [codeMentions, exprMentions] using hm)
      obtain rfl := hr.eres_right
      exact ⟨_, Step.builtinArgsHalt hs, rfl⟩
  | callOk hargs hl hlen hbody ho iha ihbody =>
      intro d x v Vs hins hm
      obtain ⟨r, hs, hr⟩ := iha hins (by simpa only [codeMentions, exprMentions] using hm)
      obtain rfl := hr.eres_right
      exact ⟨_, Step.callOk hs hl hlen hbody ho, rfl⟩
  | callHalt hargs hl hlen hbody iha ihbody =>
      intro d x v Vs hins hm
      obtain ⟨r, hs, hr⟩ := iha hins (by simpa only [codeMentions, exprMentions] using hm)
      obtain rfl := hr.eres_right
      exact ⟨_, Step.callHalt hs hl hlen hbody, rfl⟩
  | callArgsHalt hargs iha =>
      intro d x v Vs hins hm
      obtain ⟨r, hs, hr⟩ := iha hins (by simpa only [codeMentions, exprMentions] using hm)
      obtain rfl := hr.eres_right
      exact ⟨_, Step.callArgsHalt hs, rfl⟩
  | argsNil => intro d x v Vs hins hm; exact ⟨_, Step.argsNil, rfl⟩
  | argsCons hrest he ihrest ihe =>
      intro d x v Vs hins hm
      simp only [codeMentions, argsMentions, Bool.or_eq_false_iff] at hm
      obtain ⟨rr, hsr, hrr⟩ := ihrest hins (by simp only [codeMentions]; exact hm.2)
      obtain rfl := hrr.eres_right
      obtain ⟨re, hse, hre⟩ := ihe hins (by simp only [codeMentions]; exact hm.1)
      obtain rfl := hre.eres_right
      exact ⟨_, Step.argsCons hsr hse, rfl⟩
  | argsRestHalt hrest ihrest =>
      intro d x v Vs hins hm
      simp only [codeMentions, argsMentions, Bool.or_eq_false_iff] at hm
      obtain ⟨rr, hsr, hrr⟩ := ihrest hins (by simp only [codeMentions]; exact hm.2)
      obtain rfl := hrr.eres_right
      exact ⟨_, Step.argsRestHalt hsr, rfl⟩
  | argsHeadHalt hrest he ihrest ihe =>
      intro d x v Vs hins hm
      simp only [codeMentions, argsMentions, Bool.or_eq_false_iff] at hm
      obtain ⟨rr, hsr, hrr⟩ := ihrest hins (by simp only [codeMentions]; exact hm.2)
      obtain rfl := hrr.eres_right
      obtain ⟨re, hse, hre⟩ := ihe hins (by simp only [codeMentions]; exact hm.1)
      obtain rfl := hre.eres_right
      exact ⟨_, Step.argsHeadHalt hsr hse, rfl⟩
  | funDef => intro d x v Vs hins hm; exact ⟨_, Step.funDef, ⟨hins, rfl, rfl⟩⟩
  | block hbody ihbody =>
      intro d x v Vs hins hm
      simp only [codeMentions, stmtMentions] at hm
      obtain ⟨r, hs, hr⟩ := ihbody hins (by simp only [codeMentions]; exact hm)
      obtain ⟨Vb1, rfl, hins1⟩ := hr.sres_right
      exact ⟨_, Step.block hs, ⟨InsAt.restore hins hins1, rfl, rfl⟩⟩
  | letZero =>
      intro d x v Vs hins hm
      simp only [codeMentions, stmtMentions, optExprMentions, Bool.or_false,
        decide_eq_false_iff_not] at hm
      exact ⟨_, Step.letZero, ⟨hins.prepend _, rfl, rfl⟩⟩
  | letVal he hlen ihe =>
      intro d x v Vs hins hm
      simp only [codeMentions, stmtMentions, optExprMentions, Bool.or_eq_false_iff,
        decide_eq_false_iff_not] at hm
      obtain ⟨r, hs, hr⟩ := ihe hins (by simp only [codeMentions]; exact hm.2)
      obtain rfl := hr.eres_right
      exact ⟨_, Step.letVal hs hlen, ⟨hins.prepend _, rfl, rfl⟩⟩
  | letHalt he ihe =>
      intro d x v Vs hins hm
      simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hm
      obtain ⟨r, hs, hr⟩ := ihe hins (by simp only [codeMentions]; exact hm.2)
      obtain rfl := hr.eres_right
      exact ⟨_, Step.letHalt hs, ⟨hins, rfl, rfl⟩⟩
  | assignVal he hlen ihe =>
      intro d x v Vs hins hm
      simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hm
      obtain ⟨r, hs, hr⟩ := ihe hins (by simp only [codeMentions]; exact hm.2)
      obtain rfl := hr.eres_right
      exact ⟨_, Step.assignVal hs hlen, ⟨InsAt.setMany hm.1 _ hins, rfl, rfl⟩⟩
  | assignHalt he ihe =>
      intro d x v Vs hins hm
      simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hm
      obtain ⟨r, hs, hr⟩ := ihe hins (by simp only [codeMentions]; exact hm.2)
      obtain rfl := hr.eres_right
      exact ⟨_, Step.assignHalt hs, ⟨hins, rfl, rfl⟩⟩
  | exprStmt he ihe =>
      intro d x v Vs hins hm
      simp only [codeMentions, stmtMentions] at hm
      obtain ⟨r, hs, hr⟩ := ihe hins (by simp only [codeMentions]; exact hm)
      obtain rfl := hr.eres_right
      exact ⟨_, Step.exprStmt hs, ⟨hins, rfl, rfl⟩⟩
  | exprStmtHalt he ihe =>
      intro d x v Vs hins hm
      simp only [codeMentions, stmtMentions] at hm
      obtain ⟨r, hs, hr⟩ := ihe hins (by simp only [codeMentions]; exact hm)
      obtain rfl := hr.eres_right
      exact ⟨_, Step.exprStmtHalt hs, ⟨hins, rfl, rfl⟩⟩
  | ifTrue hc hcv hbody ihc ihbody =>
      intro d x v Vs hins hm
      simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hm
      obtain ⟨rc, hsc, hrc⟩ := ihc hins (by simp only [codeMentions]; exact hm.1)
      obtain rfl := hrc.eres_right
      obtain ⟨rb, hsb, hrb⟩ := ihbody hins (by simp only [codeMentions, stmtMentions]; exact hm.2)
      obtain ⟨V'1, rfl, hins1⟩ := hrb.sres_right
      exact ⟨_, Step.ifTrue hsc hcv hsb, ⟨hins1, rfl, rfl⟩⟩
  | ifFalse hc hcv ihc =>
      intro d x v Vs hins hm
      simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hm
      obtain ⟨rc, hsc, hrc⟩ := ihc hins (by simp only [codeMentions]; exact hm.1)
      obtain rfl := hrc.eres_right
      exact ⟨_, Step.ifFalse hsc hcv, ⟨hins, rfl, rfl⟩⟩
  | ifHalt hc ihc =>
      intro d x v Vs hins hm
      simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hm
      obtain ⟨rc, hsc, hrc⟩ := ihc hins (by simp only [codeMentions]; exact hm.1)
      obtain rfl := hrc.eres_right
      exact ⟨_, Step.ifHalt hsc, ⟨hins, rfl, rfl⟩⟩
  | switchExec hc hbody ihc ihbody =>
      intro d x v Vs hins hm
      simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hm
      obtain ⟨rc, hsc, hrc⟩ := ihc hins (by simp only [codeMentions]; exact hm.1.1)
      obtain rfl := hrc.eres_right
      obtain ⟨rb, hsb, hrb⟩ := ihbody hins (by
        simp only [codeMentions, stmtMentions]
        exact selectSwitch_not_mentions hm.1.2 hm.2)
      obtain ⟨V'1, rfl, hins1⟩ := hrb.sres_right
      exact ⟨_, Step.switchExec hsc hsb, ⟨hins1, rfl, rfl⟩⟩
  | switchHalt hc ihc =>
      intro d x v Vs hins hm
      simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hm
      obtain ⟨rc, hsc, hrc⟩ := ihc hins (by simp only [codeMentions]; exact hm.1.1)
      obtain rfl := hrc.eres_right
      exact ⟨_, Step.switchHalt hsc, ⟨hins, rfl, rfl⟩⟩
  | forLoop hinit hloop ihinit ihloop =>
      intro d x v Vs hins hm
      simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hm
      obtain ⟨⟨⟨h_si, h_ec⟩, h_sp⟩, h_sb⟩ := hm
      obtain ⟨ri, hsi, hri⟩ := ihinit hins (by simp only [codeMentions]; exact h_si)
      obtain ⟨Vi1, rfl, hinsi⟩ := hri.sres_right
      obtain ⟨rl, hsl, hrl⟩ := ihloop hinsi (by simp only [codeMentions, h_ec, h_sp, h_sb, Bool.or_false])
      obtain ⟨Ve1, rfl, hinsl⟩ := hrl.sres_right
      exact ⟨_, Step.forLoop hsi hsl, ⟨InsAt.restore hins hinsl, rfl, rfl⟩⟩
  | forInitHalt hinit ihinit =>
      intro d x v Vs hins hm
      simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hm
      obtain ⟨⟨⟨h_si, h_ec⟩, h_sp⟩, h_sb⟩ := hm
      obtain ⟨ri, hsi, hri⟩ := ihinit hins (by simp only [codeMentions]; exact h_si)
      obtain ⟨Vi1, rfl, hinsi⟩ := hri.sres_right
      exact ⟨_, Step.forInitHalt hsi, ⟨InsAt.restore hins hinsi, rfl, rfl⟩⟩
  | «break» => intro d x v Vs hins hm; exact ⟨_, Step.break, ⟨hins, rfl, rfl⟩⟩
  | «continue» => intro d x v Vs hins hm; exact ⟨_, Step.continue, ⟨hins, rfl, rfl⟩⟩
  | leave => intro d x v Vs hins hm; exact ⟨_, Step.leave, ⟨hins, rfl, rfl⟩⟩
  | seqNil => intro d x v Vs hins hm; exact ⟨_, Step.seqNil, ⟨hins, rfl, rfl⟩⟩
  | seqCons hs hrest ihs ihrest =>
      intro d x v Vs hins hm
      simp only [codeMentions, stmtsMentions, Bool.or_eq_false_iff] at hm
      obtain ⟨rs, hss, hrs⟩ := ihs hins (by simp only [codeMentions]; exact hm.1)
      obtain ⟨V1', rfl, hins1⟩ := hrs.sres_right
      obtain ⟨rr, hsr, hrr⟩ := ihrest hins1 (by simp only [codeMentions]; exact hm.2)
      obtain ⟨V2', rfl, hins2⟩ := hrr.sres_right
      exact ⟨_, Step.seqCons hss hsr, ⟨hins2, rfl, rfl⟩⟩
  | seqStop hs hne ihs =>
      intro d x v Vs hins hm
      simp only [codeMentions, stmtsMentions, Bool.or_eq_false_iff] at hm
      obtain ⟨rs, hss, hrs⟩ := ihs hins (by simp only [codeMentions]; exact hm.1)
      obtain ⟨V1', rfl, hins1⟩ := hrs.sres_right
      exact ⟨_, Step.seqStop hss hne, ⟨hins1, rfl, rfl⟩⟩
  | loopDone hc hcv ihc =>
      intro d x v Vs hins hm
      simp only [codeMentions, Bool.or_eq_false_iff] at hm
      obtain ⟨rc, hsc, hrc⟩ := ihc hins (by simp only [codeMentions]; exact hm.1.1)
      obtain rfl := hrc.eres_right
      exact ⟨_, Step.loopDone hsc hcv, ⟨hins, rfl, rfl⟩⟩
  | loopCondHalt hc ihc =>
      intro d x v Vs hins hm
      simp only [codeMentions, Bool.or_eq_false_iff] at hm
      obtain ⟨rc, hsc, hrc⟩ := ihc hins (by simp only [codeMentions]; exact hm.1.1)
      obtain rfl := hrc.eres_right
      exact ⟨_, Step.loopCondHalt hsc, ⟨hins, rfl, rfl⟩⟩
  | loopStep hc hcv hbody hob hpost hrec ihc ihbody ihpost ihrec =>
      intro d x v Vs hins hm
      simp only [codeMentions, Bool.or_eq_false_iff] at hm
      obtain ⟨⟨h_ec, h_sp⟩, h_sb⟩ := hm
      obtain ⟨rc, hsc, hrc⟩ := ihc hins (by simp only [codeMentions]; exact h_ec)
      obtain rfl := hrc.eres_right
      obtain ⟨rb, hsb, hrb⟩ := ihbody hins (by simp only [codeMentions, stmtMentions]; exact h_sb)
      obtain ⟨Vb1, rfl, hinsb⟩ := hrb.sres_right
      obtain ⟨rp, hsp, hrp⟩ := ihpost hinsb (by simp only [codeMentions, stmtMentions]; exact h_sp)
      obtain ⟨Vp1, rfl, hinsp⟩ := hrp.sres_right
      obtain ⟨rr, hsr, hrr⟩ := ihrec hinsp (by simp only [codeMentions, h_ec, h_sp, h_sb, Bool.or_false])
      obtain ⟨Ve1, rfl, hinsr⟩ := hrr.sres_right
      exact ⟨_, Step.loopStep hsc hcv hsb hob hsp hsr, ⟨hinsr, rfl, rfl⟩⟩
  | loopPostHalt hc hcv hbody hob hpost ihc ihbody ihpost =>
      intro d x v Vs hins hm
      simp only [codeMentions, Bool.or_eq_false_iff] at hm
      obtain ⟨⟨h_ec, h_sp⟩, h_sb⟩ := hm
      obtain ⟨rc, hsc, hrc⟩ := ihc hins (by simp only [codeMentions]; exact h_ec)
      obtain rfl := hrc.eres_right
      obtain ⟨rb, hsb, hrb⟩ := ihbody hins (by simp only [codeMentions, stmtMentions]; exact h_sb)
      obtain ⟨Vb1, rfl, hinsb⟩ := hrb.sres_right
      obtain ⟨rp, hsp, hrp⟩ := ihpost hinsb (by simp only [codeMentions, stmtMentions]; exact h_sp)
      obtain ⟨Vp1, rfl, hinsp⟩ := hrp.sres_right
      exact ⟨_, Step.loopPostHalt hsc hcv hsb hob hsp, ⟨hinsp, rfl, rfl⟩⟩
  | loopBreak hc hcv hbody ihc ihbody =>
      intro d x v Vs hins hm
      simp only [codeMentions, Bool.or_eq_false_iff] at hm
      obtain ⟨⟨h_ec, h_sp⟩, h_sb⟩ := hm
      obtain ⟨rc, hsc, hrc⟩ := ihc hins (by simp only [codeMentions]; exact h_ec)
      obtain rfl := hrc.eres_right
      obtain ⟨rb, hsb, hrb⟩ := ihbody hins (by simp only [codeMentions, stmtMentions]; exact h_sb)
      obtain ⟨Vb1, rfl, hinsb⟩ := hrb.sres_right
      exact ⟨_, Step.loopBreak hsc hcv hsb, ⟨hinsb, rfl, rfl⟩⟩
  | loopLeave hc hcv hbody ihc ihbody =>
      intro d x v Vs hins hm
      simp only [codeMentions, Bool.or_eq_false_iff] at hm
      obtain ⟨⟨h_ec, h_sp⟩, h_sb⟩ := hm
      obtain ⟨rc, hsc, hrc⟩ := ihc hins (by simp only [codeMentions]; exact h_ec)
      obtain rfl := hrc.eres_right
      obtain ⟨rb, hsb, hrb⟩ := ihbody hins (by simp only [codeMentions, stmtMentions]; exact h_sb)
      obtain ⟨Vb1, rfl, hinsb⟩ := hrb.sres_right
      exact ⟨_, Step.loopLeave hsc hcv hsb, ⟨hinsb, rfl, rfl⟩⟩
  | loopBodyHalt hc hcv hbody ihc ihbody =>
      intro d x v Vs hins hm
      simp only [codeMentions, Bool.or_eq_false_iff] at hm
      obtain ⟨⟨h_ec, h_sp⟩, h_sb⟩ := hm
      obtain ⟨rc, hsc, hrc⟩ := ihc hins (by simp only [codeMentions]; exact h_ec)
      obtain rfl := hrc.eres_right
      obtain ⟨rb, hsb, hrb⟩ := ihbody hins (by simp only [codeMentions, stmtMentions]; exact h_sb)
      obtain ⟨Vb1, rfl, hinsb⟩ := hrb.sres_right
      exact ⟨_, Step.loopBodyHalt hsc hcv hsb, ⟨hinsb, rfl, rfl⟩⟩

end YulEvmCompiler.Optimizer
