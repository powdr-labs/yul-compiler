import YulEvmCompiler.Optimizer.Implementation.FuseDeclAssign
import YulEvmCompiler.Optimizer.Implementation.CoalesceCopies
set_option warningAsError true
/-!
# Soundness of declare-then-assign fusion — the environment-reorder transport

The sink rewrite moves a binding's creation point: after
`let x; mid; x := e  ↝  mid; let x := e`, the suffix executes over

* source: `C ++ A ++ (x, v) :: B` (the binding sits below `mid`'s locals `A`),
* target: `C ++ (x, v) :: A ++ B` (the binding sits on top of them),

with a common newer segment `C` for everything pushed later.  Yul variable
access is name-first (`VEnv.get`/`VEnv.set` find the first occurrence), so as
long as `A` never binds `x`, both environments agree on every read and every
update — the difference is pure stack *placement*, observable only by
`restore`, which either cuts inside `C` (both sides drop the same entries) or
at/below `B` (both sides return the same suffix of `B`).

`MvRel` packages this shape; the `Step` transport (`mv_congr`, below) carries
a derivation across it.
-/

namespace YulEvmCompiler.Optimizer.FuseDeclAssign

open YulSemantics
open YulSemantics.EVM

variable {calls : ExternalCalls} {creates : ExternalCreates}
local notation "D" => evmWithExternal calls creates

/-! ### `VEnv.set` distributes over append by key location -/

theorem set_append_of_found {V W : VEnv D} {y : Ident}
    (h : (V.find? (fun p => p.1 = y)).isSome)
    (w : (evmWithExternal calls creates).Value) :
    VEnv.set (V ++ W) y w = VEnv.set V y w ++ W := by
  induction V with
  | nil => simp at h
  | cons p V' ih =>
      by_cases hp : p.1 = y
      · obtain ⟨p1, p2⟩ := p
        simp only at hp
        subst hp
        simp [VEnv.set]
      · obtain ⟨p1, p2⟩ := p
        simp only at hp
        rw [List.find?_cons_of_neg (by simp [hp])] at h
        simp only [List.cons_append, VEnv.set, if_neg hp]
        rw [ih h]

theorem set_append_of_none {V W : VEnv D} {y : Ident}
    (h : V.find? (fun p => p.1 = y) = none)
    (w : (evmWithExternal calls creates).Value) :
    VEnv.set (V ++ W) y w = V ++ VEnv.set W y w := by
  induction V with
  | nil => simp
  | cons p V' ih =>
      obtain ⟨p1, p2⟩ := p
      by_cases hp : p1 = y
      · rw [List.find?_cons_of_pos (by simp [hp])] at h
        cases h
      · rw [List.find?_cons_of_neg (by simp [hp])] at h
        simp only [List.cons_append, VEnv.set, if_neg hp]
        rw [ih h]

/-- Keys of an environment survive `VEnv.set` (membership form). -/
theorem mem_set_key {V : VEnv D} {y : Ident}
    {w : (evmWithExternal calls creates).Value} {p : Ident × U256}
    (hp : p ∈ VEnv.set V y w) : ∃ q ∈ V, q.1 = p.1 := by
  induction V with
  | nil => cases hp
  | cons q V' ih =>
      obtain ⟨q1, q2⟩ := q
      by_cases hq : q1 = y
      · simp only [VEnv.set, if_pos hq] at hp
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact ⟨(q1, q2), List.mem_cons_self .., by simp [hq]⟩
        · exact ⟨p, List.mem_cons_of_mem _ hp', rfl⟩
      · simp only [VEnv.set, if_neg hq] at hp
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact ⟨(q1, q2), List.mem_cons_self .., rfl⟩
        · obtain ⟨r, hr, hre⟩ := ih hp'
          exact ⟨r, List.mem_cons_of_mem _ hr, hre⟩

/-! ### The reorder relation -/

/-- One binding moved from below `A` to above it, under a common newer
segment `C`. `x` must not be bound by `A` (reads reach the moved binding on
both sides); it may be bound by `C` (an identical shadow on both sides).
The indices pin the region lengths so `restore` compatibility is derivable:
execution below never changes them. -/
inductive MvRel (x : Ident) (dA dB : Nat) : VEnv D → VEnv D → Prop
  | mk (C A B : VEnv D) (v : (evmWithExternal calls creates).Value)
      (hA : ∀ p ∈ A, p.1 ≠ x) (hdA : A.length = dA) (hdB : B.length = dB) :
      MvRel x dA dB (C ++ (A ++ (x, v) :: B)) (C ++ ((x, v) :: (A ++ B)))

theorem MvRel.length {x : Ident} {dA dB : Nat} {V₁ V₂ : VEnv D}
    (h : MvRel x dA dB V₁ V₂) :
    V₁.length = V₂.length := by
  cases h with
  | mk C A B v hA hdA hdB => simp [List.length_append]; omega

/-- Push a common binding on top. -/
theorem MvRel.push {x : Ident} {dA dB : Nat} {V₁ V₂ : VEnv D}
    (h : MvRel x dA dB V₁ V₂)
    (p : Ident × (evmWithExternal calls creates).Value) :
    MvRel x dA dB (p :: V₁) (p :: V₂) := by
  cases h with
  | mk C A B v hA hdA hdB => exact MvRel.mk (p :: C) A B v hA hdA hdB

/-- Push a common list of bindings on top. -/
theorem MvRel.pushMany {x : Ident} {dA dB : Nat} {V₁ V₂ : VEnv D}
    (h : MvRel x dA dB V₁ V₂)
    (ps : VEnv D) : MvRel x dA dB (ps ++ V₁) (ps ++ V₂) := by
  cases h with
  | mk C A B v hA hdA hdB =>
      have := MvRel.mk (calls := calls) (creates := creates)
        (ps ++ C) A B v hA hdA hdB
      simpa [List.append_assoc] using this

/-- Reads agree across the relation. -/
theorem MvRel.get {x : Ident} {dA dB : Nat} {V₁ V₂ : VEnv D}
    (h : MvRel x dA dB V₁ V₂)
    (y : Ident) : VEnv.get V₁ y = VEnv.get V₂ y := by
  cases h with
  | mk C A B v hA hdA hdB =>
      unfold VEnv.get
      simp only [List.find?_append]
      cases hC : C.find? (fun p => p.1 = y) with
      | some p => simp
      | none =>
          simp only [Option.none_or]
          by_cases hxy : y = x
          · subst hxy
            have hAn : A.find? (fun p => p.1 = y) = none := by
              rw [List.find?_eq_none]
              intro p hp
              simp [hA p hp]
            rw [hAn,
              List.find?_cons_of_pos (by simp),
              List.find?_cons_of_pos (by simp)]
            simp
          · rw [List.find?_cons_of_neg (by simp; exact fun hc : x = y => hxy hc.symm),
              List.find?_cons_of_neg (by simp; exact fun hc : x = y => hxy hc.symm),
              List.find?_append]

/-- Updates preserve the relation. -/
theorem MvRel.set {x : Ident} {dA dB : Nat} {V₁ V₂ : VEnv D}
    (h : MvRel x dA dB V₁ V₂)
    (y : Ident) (w : (evmWithExternal calls creates).Value) :
    MvRel x dA dB (VEnv.set V₁ y w) (VEnv.set V₂ y w) := by
  cases h with
  | mk C A B v hA hdA hdB =>
      cases hC : C.find? (fun p => p.1 = y) with
      | some p =>
          rw [set_append_of_found (by simp [hC]) w,
            set_append_of_found (by simp [hC]) w]
          exact MvRel.mk _ A B v hA hdA hdB
      | none =>
          rw [set_append_of_none hC w, set_append_of_none hC w]
          by_cases hxy : y = x
          · subst hxy
            have hAn : A.find? (fun p => p.1 = y) = none := by
              rw [List.find?_eq_none]
              intro p hp
              simp [hA p hp]
            rw [set_append_of_none hAn w]
            have hset1 : VEnv.set ((y, v) :: B) y w = (y, w) :: B := by
              simp [VEnv.set]
            have hset2 : VEnv.set ((y, v) :: (A ++ B)) y w =
                (y, w) :: (A ++ B) := by
              simp [VEnv.set]
            rw [hset1, hset2]
            exact MvRel.mk C A B w hA hdA hdB
          · cases hA' : A.find? (fun p => p.1 = y) with
            | some q =>
                rw [set_append_of_found (by simp [hA']) w,
                  show VEnv.set ((x, v) :: (A ++ B)) y w =
                    (x, v) :: VEnv.set (A ++ B) y w from by
                      simp only [VEnv.set]
                      rw [if_neg (fun hc : x = y => hxy hc.symm)],
                  set_append_of_found (by simp [hA']) w]
                refine MvRel.mk C (VEnv.set A y w) B v ?_
                  (by rw [VEnv.set_length]; exact hdA) hdB
                intro p hp
                obtain ⟨q', hq', hqe⟩ := mem_set_key hp
                rw [← hqe]
                exact hA q' hq'
            | none =>
                rw [set_append_of_none hA' w,
                  show VEnv.set ((x, v) :: (A ++ B)) y w =
                    (x, v) :: VEnv.set (A ++ B) y w from by
                      simp only [VEnv.set]
                      rw [if_neg (fun hc : x = y => hxy hc.symm)],
                  set_append_of_none hA' w,
                  show VEnv.set ((x, v) :: B) y w =
                    (x, v) :: VEnv.set B y w from by
                      simp only [VEnv.set]
                      rw [if_neg (fun hc : x = y => hxy hc.symm)]]
                exact MvRel.mk C A (VEnv.set B y w) v hA hdA
                  (by rw [VEnv.set_length]; exact hdB)

/-- `setMany` preserves the relation. -/
theorem MvRel.setMany {x : Ident} {dA dB : Nat} {V₁ V₂ : VEnv D}
    (h : MvRel x dA dB V₁ V₂)
    (ys : List Ident) (ws : List (evmWithExternal calls creates).Value) :
    MvRel x dA dB (VEnv.setMany V₁ ys ws) (VEnv.setMany V₂ ys ws) := by
  unfold VEnv.setMany
  induction (ys.zip ws) generalizing V₁ V₂ with
  | nil => exact h
  | cons p rest ih => exact ih (h.set p.1 p.2)

/-! ### `restore` across the relation

`restore outer inner` keeps `inner`'s last `outer.length` entries.  A cut at
or above the moved region (both related environments share the newer segment)
yields related results; a cut at or below the fixed base `B` yields *equal*
results. -/

/-- The workable form: exits whose moved region sits below the entry cut.
`dA`/`dB` name the region lengths; the cut keeps at least the region. -/
theorem restore_mvRel {x : Ident} {Ve₁ Ve₂ : VEnv D}
    {C A B : VEnv D} {v : (evmWithExternal calls creates).Value}
    (hA : ∀ p ∈ A, p.1 ≠ x)
    (hentry_len : A.length + 1 + B.length ≤ Ve₁.length)
    (hlen : Ve₁.length = Ve₂.length)
    (hle₁ : Ve₁.length ≤ (C ++ (A ++ (x, v) :: B)).length) :
    MvRel x A.length B.length (restore Ve₁ (C ++ (A ++ (x, v) :: B)))
      (restore Ve₂ (C ++ ((x, v) :: (A ++ B)))) := by
  unfold restore
  have hlen₂ : (C ++ ((x, v) :: (A ++ B))).length =
      (C ++ (A ++ (x, v) :: B)).length := by
    simp [List.length_append]; omega
  rw [hlen₂, ← hlen]
  -- The drop count stays within `C`.
  have hdrop : (C ++ (A ++ (x, v) :: B)).length - Ve₁.length ≤ C.length := by
    simp only [List.length_append, List.length_cons] at hle₁ ⊢
    omega
  set k := (C ++ (A ++ (x, v) :: B)).length - Ve₁.length with hk
  rw [List.drop_append_of_le_length (by omega),
    List.drop_append_of_le_length (by omega)]
  exact MvRel.mk (C.drop k) A B v hA rfl rfl

/-- Dropping down to the last `n` entries ignores everything above the base. -/
theorem drop_to_base (X B : VEnv D) {n : Nat} (h : n ≤ B.length) :
    List.drop ((X ++ B).length - n) (X ++ B) = List.drop (B.length - n) B := by
  have heq : (X ++ B).length - n = X.length + (B.length - n) := by
    simp [List.length_append]; omega
  rw [heq, List.drop_append]
  rw [List.drop_eq_nil_of_le (Nat.le_add_right ..), List.nil_append]
  congr 1
  omega

/-- Restoring to a base at or below `B` yields equal environments. -/
theorem restore_mv_eq {x : Ident} {V₀ : VEnv D}
    {C A B : VEnv D} {v : (evmWithExternal calls creates).Value}
    (hbase : V₀.length ≤ B.length) :
    restore V₀ (C ++ (A ++ (x, v) :: B)) =
      restore V₀ (C ++ ((x, v) :: (A ++ B))) := by
  unfold restore
  rw [show C ++ (A ++ (x, v) :: B) = (C ++ A ++ [(x, v)]) ++ B from by simp,
    show C ++ ((x, v) :: (A ++ B)) = (C ++ [(x, v)] ++ A) ++ B from by simp,
    drop_to_base _ _ hbase, drop_to_base _ _ hbase]

/-- Restore compatibility: exits related at the same region indices restore
(to related entries) to related environments. -/
theorem MvRel.restore_compat {x : Ident} {dA dB : Nat}
    {Ve₁ Ve₂ Vb₁ Vb₂ : VEnv D}
    (hentry : MvRel x dA dB Ve₁ Ve₂) (hexit : MvRel x dA dB Vb₁ Vb₂)
    (hgrow : Ve₁.length ≤ Vb₁.length) :
    MvRel x dA dB (restore Ve₁ Vb₁) (restore Ve₂ Vb₂) := by
  cases hexit with
  | mk C A B v hA hdA hdB =>
      have hentry_len : A.length + 1 + B.length ≤ Ve₁.length := by
        cases hentry with
        | mk C' A' B' v' hA' hdA' hdB' =>
            simp only [List.length_append, List.length_cons]
            omega
      have := restore_mvRel (calls := calls) (creates := creates)
        (Ve₁ := Ve₁) (Ve₂ := Ve₂) (C := C) (A := A) (B := B) (v := v) hA
        (by omega) hentry.length hgrow
      rw [hdA, hdB] at this
      exact this

/-- The result relation for the transport: expression results are literally
equal; statement results carry related environments. -/
inductive MvRes (x : Ident) (dA dB : Nat) : Res D → Res D → Prop
  | eres (r : EResult D) : MvRes x dA dB (.eres r) (.eres r)
  | sres {V₁ V₂ : VEnv D} (st : EvmState) (o : Outcome)
      (h : MvRel x dA dB V₁ V₂) :
      MvRes x dA dB (.sres V₁ st o) (.sres V₂ st o)

theorem MvRes.eres_inv {x : Ident} {dA dB : Nat} {r : EResult D} {res₂ : Res D}
    (h : MvRes x dA dB (.eres r) res₂) : res₂ = .eres r := by
  cases h; rfl

theorem MvRes.sres_inv {x : Ident} {dA dB : Nat} {V₁ : VEnv D} {st o}
    {res₂ : Res D} (h : MvRes x dA dB (.sres V₁ st o) res₂) :
    ∃ V₂, res₂ = .sres V₂ st o ∧ MvRel x dA dB V₁ V₂ := by
  cases h with
  | sres _ _ hrel => exact ⟨_, rfl, hrel⟩

set_option maxHeartbeats 1600000 in
/-- **The environment-reorder transport**: a derivation over `V₁` yields one
over the related `V₂`, with a related result. Function bodies run in fresh
callee environments and are reused unchanged. -/
theorem Step.mv_congr {x : Ident} {dA dB : Nat} {funs : FunEnv D}
    {V₁ : VEnv D} {st : EvmState} {code : Code Op} {res₁ : Res D}
    (h : Step D funs V₁ st code res₁) :
    ∀ {V₂}, MvRel x dA dB V₁ V₂ →
      ∃ res₂, Step D funs V₂ st code res₂ ∧ MvRes x dA dB res₁ res₂ := by
  induction h with
  | lit => intro _ _; exact ⟨_, Step.lit, .eres _⟩
  | @var _ _ _ y v hv =>
      intro V₂ hR
      exact ⟨_, Step.var (by rw [← hR.get y]; exact hv), .eres _⟩
  | builtinOk ha hb iha =>
      intro V₂ hR
      obtain ⟨r₂, h₂, hrel⟩ := iha hR
      rw [hrel.eres_inv] at h₂
      exact ⟨_, Step.builtinOk h₂ hb, .eres _⟩
  | builtinHalt ha hb iha =>
      intro V₂ hR
      obtain ⟨r₂, h₂, hrel⟩ := iha hR
      rw [hrel.eres_inv] at h₂
      exact ⟨_, Step.builtinHalt h₂ hb, .eres _⟩
  | builtinArgsHalt ha iha =>
      intro V₂ hR
      obtain ⟨r₂, h₂, hrel⟩ := iha hR
      rw [hrel.eres_inv] at h₂
      exact ⟨_, Step.builtinArgsHalt h₂, .eres _⟩
  | callOk ha hl hlen hbody ho iha ihbody =>
      intro V₂ hR
      obtain ⟨r₂, h₂, hrel⟩ := iha hR
      rw [hrel.eres_inv] at h₂
      exact ⟨_, Step.callOk h₂ hl hlen hbody ho, .eres _⟩
  | callHalt ha hl hlen hbody iha ihbody =>
      intro V₂ hR
      obtain ⟨r₂, h₂, hrel⟩ := iha hR
      rw [hrel.eres_inv] at h₂
      exact ⟨_, Step.callHalt h₂ hl hlen hbody, .eres _⟩
  | callArgsHalt ha iha =>
      intro V₂ hR
      obtain ⟨r₂, h₂, hrel⟩ := iha hR
      rw [hrel.eres_inv] at h₂
      exact ⟨_, Step.callArgsHalt h₂, .eres _⟩
  | argsNil => intro _ _; exact ⟨_, Step.argsNil, .eres _⟩
  | argsCons ha he iha ihe =>
      intro V₂ hR
      obtain ⟨r₂, h₂, hrel⟩ := iha hR
      rw [hrel.eres_inv] at h₂
      obtain ⟨r₃, h₃, hrel'⟩ := ihe hR
      rw [hrel'.eres_inv] at h₃
      exact ⟨_, Step.argsCons h₂ h₃, .eres _⟩
  | argsRestHalt ha iha =>
      intro V₂ hR
      obtain ⟨r₂, h₂, hrel⟩ := iha hR
      rw [hrel.eres_inv] at h₂
      exact ⟨_, Step.argsRestHalt h₂, .eres _⟩
  | argsHeadHalt ha he iha ihe =>
      intro V₂ hR
      obtain ⟨r₂, h₂, hrel⟩ := iha hR
      rw [hrel.eres_inv] at h₂
      obtain ⟨r₃, h₃, hrel'⟩ := ihe hR
      rw [hrel'.eres_inv] at h₃
      exact ⟨_, Step.argsHeadHalt h₂ h₃, .eres _⟩
  | funDef => intro V₂ hR; exact ⟨_, Step.funDef, .sres _ _ hR⟩
  | @block _ V _ body Vb stb o hbody ihbody =>
      intro V₂ hR
      obtain ⟨r₂, h₂, hrel⟩ := ihbody hR
      obtain ⟨Vb₂, rfl, hrel'⟩ := hrel.sres_inv
      exact ⟨_, Step.block h₂,
        .sres _ _ (hR.restore_compat hrel' (venvLen_mono hbody rfl))⟩
  | letZero =>
      intro V₂ hR
      exact ⟨_, Step.letZero, .sres _ _ (hR.pushMany _)⟩
  | letVal he hlen ihe =>
      intro V₂ hR
      obtain ⟨r₂, h₂, hrel⟩ := ihe hR
      rw [hrel.eres_inv] at h₂
      exact ⟨_, Step.letVal h₂ hlen, .sres _ _ (hR.pushMany _)⟩
  | letHalt he ihe =>
      intro V₂ hR
      obtain ⟨r₂, h₂, hrel⟩ := ihe hR
      rw [hrel.eres_inv] at h₂
      exact ⟨_, Step.letHalt h₂, .sres _ _ hR⟩
  | assignVal he hlen ihe =>
      intro V₂ hR
      obtain ⟨r₂, h₂, hrel⟩ := ihe hR
      rw [hrel.eres_inv] at h₂
      exact ⟨_, Step.assignVal h₂ hlen, .sres _ _ (hR.setMany _ _)⟩
  | assignHalt he ihe =>
      intro V₂ hR
      obtain ⟨r₂, h₂, hrel⟩ := ihe hR
      rw [hrel.eres_inv] at h₂
      exact ⟨_, Step.assignHalt h₂, .sres _ _ hR⟩
  | exprStmt he ihe =>
      intro V₂ hR
      obtain ⟨r₂, h₂, hrel⟩ := ihe hR
      rw [hrel.eres_inv] at h₂
      exact ⟨_, Step.exprStmt h₂, .sres _ _ hR⟩
  | exprStmtHalt he ihe =>
      intro V₂ hR
      obtain ⟨r₂, h₂, hrel⟩ := ihe hR
      rw [hrel.eres_inv] at h₂
      exact ⟨_, Step.exprStmtHalt h₂, .sres _ _ hR⟩
  | ifTrue hc hnz hb ihc ihb =>
      intro V₂ hR
      obtain ⟨r₂, h₂, hrel⟩ := ihc hR
      rw [hrel.eres_inv] at h₂
      obtain ⟨r₃, h₃, hrel'⟩ := ihb hR
      obtain ⟨Vb₂, rfl, hrel''⟩ := hrel'.sres_inv
      exact ⟨_, Step.ifTrue h₂ hnz h₃, .sres _ _ hrel''⟩
  | ifFalse hc hz ihc =>
      intro V₂ hR
      obtain ⟨r₂, h₂, hrel⟩ := ihc hR
      rw [hrel.eres_inv] at h₂
      exact ⟨_, Step.ifFalse h₂ hz, .sres _ _ hR⟩
  | ifHalt hc ihc =>
      intro V₂ hR
      obtain ⟨r₂, h₂, hrel⟩ := ihc hR
      rw [hrel.eres_inv] at h₂
      exact ⟨_, Step.ifHalt h₂, .sres _ _ hR⟩
  | switchExec hc hb ihc ihb =>
      intro V₂ hR
      obtain ⟨r₂, h₂, hrel⟩ := ihc hR
      rw [hrel.eres_inv] at h₂
      obtain ⟨r₃, h₃, hrel'⟩ := ihb hR
      obtain ⟨Vb₂, rfl, hrel''⟩ := hrel'.sres_inv
      exact ⟨_, Step.switchExec h₂ h₃, .sres _ _ hrel''⟩
  | switchHalt hc ihc =>
      intro V₂ hR
      obtain ⟨r₂, h₂, hrel⟩ := ihc hR
      rw [hrel.eres_inv] at h₂
      exact ⟨_, Step.switchHalt h₂, .sres _ _ hR⟩
  | @forLoop _ V _ init c post body Vinit stinit Vend stend o hinit hloop ihinit ihloop =>
      intro V₂ hR
      obtain ⟨r₂, h₂, hrel⟩ := ihinit hR
      obtain ⟨Vi₂, rfl, hrel'⟩ := hrel.sres_inv
      obtain ⟨r₃, h₃, hrel₂⟩ := ihloop hrel'
      obtain ⟨Ve₂, rfl, hrel₃⟩ := hrel₂.sres_inv
      refine ⟨_, Step.forLoop h₂ h₃, .sres _ _ ?_⟩
      exact hR.restore_compat hrel₃
        (Nat.le_trans (venvLen_mono hinit rfl) (venvLen_mono hloop rfl))
  | @forInitHalt _ V _ init c post body Vinit stinit hinit ihinit =>
      intro V₂ hR
      obtain ⟨r₂, h₂, hrel⟩ := ihinit hR
      obtain ⟨Vi₂, rfl, hrel'⟩ := hrel.sres_inv
      exact ⟨_, Step.forInitHalt h₂,
        .sres _ _ (hR.restore_compat hrel' (venvLen_mono hinit rfl))⟩
  | «break» => intro V₂ hR; exact ⟨_, Step.break, .sres _ _ hR⟩
  | «continue» => intro V₂ hR; exact ⟨_, Step.continue, .sres _ _ hR⟩
  | leave => intro V₂ hR; exact ⟨_, Step.leave, .sres _ _ hR⟩
  | seqNil => intro V₂ hR; exact ⟨_, Step.seqNil, .sres _ _ hR⟩
  | seqCons hs hrest ihs ihrest =>
      intro V₂ hR
      obtain ⟨r₂, h₂, hrel⟩ := ihs hR
      obtain ⟨V₂', rfl, hrel'⟩ := hrel.sres_inv
      obtain ⟨r₃, h₃, hrel₂⟩ := ihrest hrel'
      obtain ⟨V₂'', rfl, hrel₃⟩ := hrel₂.sres_inv
      exact ⟨_, Step.seqCons h₂ h₃, .sres _ _ hrel₃⟩
  | seqStop hs hne ihs =>
      intro V₂ hR
      obtain ⟨r₂, h₂, hrel⟩ := ihs hR
      obtain ⟨V₂', rfl, hrel'⟩ := hrel.sres_inv
      exact ⟨_, Step.seqStop h₂ hne, .sres _ _ hrel'⟩
  | loopDone hc hz ihc =>
      intro V₂ hR
      obtain ⟨r₂, h₂, hrel⟩ := ihc hR
      rw [hrel.eres_inv] at h₂
      exact ⟨_, Step.loopDone h₂ hz, .sres _ _ hR⟩
  | loopCondHalt hc ihc =>
      intro V₂ hR
      obtain ⟨r₂, h₂, hrel⟩ := ihc hR
      rw [hrel.eres_inv] at h₂
      exact ⟨_, Step.loopCondHalt h₂, .sres _ _ hR⟩
  | loopStep hc hnz hb hob hp hr ihc ihb ihp ihr =>
      intro V₂ hR
      obtain ⟨r₂, h₂, hrel⟩ := ihc hR
      rw [hrel.eres_inv] at h₂
      obtain ⟨r₃, h₃, hrel'⟩ := ihb hR
      obtain ⟨Vb₂, rfl, hrelB⟩ := hrel'.sres_inv
      obtain ⟨r₄, h₄, hrel₄⟩ := ihp hrelB
      obtain ⟨Vp₂, rfl, hrelP⟩ := hrel₄.sres_inv
      obtain ⟨r₅, h₅, hrel₅⟩ := ihr hrelP
      obtain ⟨Ve₂, rfl, hrelE⟩ := hrel₅.sres_inv
      exact ⟨_, Step.loopStep h₂ hnz h₃ hob h₄ h₅, .sres _ _ hrelE⟩
  | loopPostHalt hc hnz hb hob hp ihc ihb ihp =>
      intro V₂ hR
      obtain ⟨r₂, h₂, hrel⟩ := ihc hR
      rw [hrel.eres_inv] at h₂
      obtain ⟨r₃, h₃, hrel'⟩ := ihb hR
      obtain ⟨Vb₂, rfl, hrelB⟩ := hrel'.sres_inv
      obtain ⟨r₄, h₄, hrel₄⟩ := ihp hrelB
      obtain ⟨Vp₂, rfl, hrelP⟩ := hrel₄.sres_inv
      exact ⟨_, Step.loopPostHalt h₂ hnz h₃ hob h₄, .sres _ _ hrelP⟩
  | loopBreak hc hnz hb ihc ihb =>
      intro V₂ hR
      obtain ⟨r₂, h₂, hrel⟩ := ihc hR
      rw [hrel.eres_inv] at h₂
      obtain ⟨r₃, h₃, hrel'⟩ := ihb hR
      obtain ⟨Vb₂, rfl, hrelB⟩ := hrel'.sres_inv
      exact ⟨_, Step.loopBreak h₂ hnz h₃, .sres _ _ hrelB⟩
  | loopLeave hc hnz hb ihc ihb =>
      intro V₂ hR
      obtain ⟨r₂, h₂, hrel⟩ := ihc hR
      rw [hrel.eres_inv] at h₂
      obtain ⟨r₃, h₃, hrel'⟩ := ihb hR
      obtain ⟨Vb₂, rfl, hrelB⟩ := hrel'.sres_inv
      exact ⟨_, Step.loopLeave h₂ hnz h₃, .sres _ _ hrelB⟩
  | loopBodyHalt hc hnz hb ihc ihb =>
      intro V₂ hR
      obtain ⟨r₂, h₂, hrel⟩ := ihc hR
      rw [hrel.eres_inv] at h₂
      obtain ⟨r₃, h₃, hrel'⟩ := ihb hR
      obtain ⟨Vb₂, rfl, hrelB⟩ := hrel'.sres_inv
      exact ⟨_, Step.loopBodyHalt h₂ hnz h₃, .sres _ _ hrelB⟩

end YulEvmCompiler.Optimizer.FuseDeclAssign
