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


theorem MvRes.eres_inv_right {x : Ident} {dA dB : Nat} {r : EResult D}
    {res₁ : Res D} (h : MvRes x dA dB res₁ (.eres r)) : res₁ = .eres r := by
  cases h; rfl

theorem MvRes.sres_inv_right {x : Ident} {dA dB : Nat} {V₂ : VEnv D} {st o}
    {res₁ : Res D} (h : MvRes x dA dB res₁ (.sres V₂ st o)) :
    ∃ V₁, res₁ = .sres V₁ st o ∧ MvRel x dA dB V₁ V₂ := by
  cases h with
  | sres _ _ hrel => exact ⟨_, rfl, hrel⟩

set_option maxHeartbeats 1600000 in
/-- The mirrored transport: a derivation over the *target* side of the
relation yields one over the source side. -/
theorem Step.mv_congr_bwd {x : Ident} {dA dB : Nat} {funs : FunEnv D}
    {V₂ : VEnv D} {st : EvmState} {code : Code Op} {res₂ : Res D}
    (h : Step D funs V₂ st code res₂) :
    ∀ {V₁}, MvRel x dA dB V₁ V₂ →
      ∃ res₁, Step D funs V₁ st code res₁ ∧ MvRes x dA dB res₁ res₂ := by
  induction h with
  | lit => intro _ _; exact ⟨_, Step.lit, .eres _⟩
  | @var _ _ _ y v hv =>
      intro V₁ hR
      exact ⟨_, Step.var (by rw [hR.get y]; exact hv), .eres _⟩
  | builtinOk ha hb iha =>
      intro V₁ hR
      obtain ⟨r₂, h₂, hrel⟩ := iha hR
      rw [hrel.eres_inv_right] at h₂
      exact ⟨_, Step.builtinOk h₂ hb, .eres _⟩
  | builtinHalt ha hb iha =>
      intro V₁ hR
      obtain ⟨r₂, h₂, hrel⟩ := iha hR
      rw [hrel.eres_inv_right] at h₂
      exact ⟨_, Step.builtinHalt h₂ hb, .eres _⟩
  | builtinArgsHalt ha iha =>
      intro V₁ hR
      obtain ⟨r₂, h₂, hrel⟩ := iha hR
      rw [hrel.eres_inv_right] at h₂
      exact ⟨_, Step.builtinArgsHalt h₂, .eres _⟩
  | callOk ha hl hlen hbody ho iha ihbody =>
      intro V₁ hR
      obtain ⟨r₂, h₂, hrel⟩ := iha hR
      rw [hrel.eres_inv_right] at h₂
      exact ⟨_, Step.callOk h₂ hl hlen hbody ho, .eres _⟩
  | callHalt ha hl hlen hbody iha ihbody =>
      intro V₁ hR
      obtain ⟨r₂, h₂, hrel⟩ := iha hR
      rw [hrel.eres_inv_right] at h₂
      exact ⟨_, Step.callHalt h₂ hl hlen hbody, .eres _⟩
  | callArgsHalt ha iha =>
      intro V₁ hR
      obtain ⟨r₂, h₂, hrel⟩ := iha hR
      rw [hrel.eres_inv_right] at h₂
      exact ⟨_, Step.callArgsHalt h₂, .eres _⟩
  | argsNil => intro _ _; exact ⟨_, Step.argsNil, .eres _⟩
  | argsCons ha he iha ihe =>
      intro V₁ hR
      obtain ⟨r₂, h₂, hrel⟩ := iha hR
      rw [hrel.eres_inv_right] at h₂
      obtain ⟨r₃, h₃, hrel'⟩ := ihe hR
      rw [hrel'.eres_inv_right] at h₃
      exact ⟨_, Step.argsCons h₂ h₃, .eres _⟩
  | argsRestHalt ha iha =>
      intro V₁ hR
      obtain ⟨r₂, h₂, hrel⟩ := iha hR
      rw [hrel.eres_inv_right] at h₂
      exact ⟨_, Step.argsRestHalt h₂, .eres _⟩
  | argsHeadHalt ha he iha ihe =>
      intro V₁ hR
      obtain ⟨r₂, h₂, hrel⟩ := iha hR
      rw [hrel.eres_inv_right] at h₂
      obtain ⟨r₃, h₃, hrel'⟩ := ihe hR
      rw [hrel'.eres_inv_right] at h₃
      exact ⟨_, Step.argsHeadHalt h₂ h₃, .eres _⟩
  | funDef => intro V₁ hR; exact ⟨_, Step.funDef, .sres _ _ hR⟩
  | @block _ V _ body Vb stb o hbody ihbody =>
      intro V₁ hR
      obtain ⟨r₂, h₂, hrel⟩ := ihbody hR
      obtain ⟨Vb₁, rfl, hrel'⟩ := hrel.sres_inv_right
      exact ⟨_, Step.block h₂,
        .sres _ _ (hR.restore_compat hrel'
          (by rw [hR.length, hrel'.length]; exact venvLen_mono hbody rfl))⟩
  | letZero =>
      intro V₁ hR
      exact ⟨_, Step.letZero, .sres _ _ (hR.pushMany _)⟩
  | letVal he hlen ihe =>
      intro V₁ hR
      obtain ⟨r₂, h₂, hrel⟩ := ihe hR
      rw [hrel.eres_inv_right] at h₂
      exact ⟨_, Step.letVal h₂ hlen, .sres _ _ (hR.pushMany _)⟩
  | letHalt he ihe =>
      intro V₁ hR
      obtain ⟨r₂, h₂, hrel⟩ := ihe hR
      rw [hrel.eres_inv_right] at h₂
      exact ⟨_, Step.letHalt h₂, .sres _ _ hR⟩
  | assignVal he hlen ihe =>
      intro V₁ hR
      obtain ⟨r₂, h₂, hrel⟩ := ihe hR
      rw [hrel.eres_inv_right] at h₂
      exact ⟨_, Step.assignVal h₂ hlen, .sres _ _ (hR.setMany _ _)⟩
  | assignHalt he ihe =>
      intro V₁ hR
      obtain ⟨r₂, h₂, hrel⟩ := ihe hR
      rw [hrel.eres_inv_right] at h₂
      exact ⟨_, Step.assignHalt h₂, .sres _ _ hR⟩
  | exprStmt he ihe =>
      intro V₁ hR
      obtain ⟨r₂, h₂, hrel⟩ := ihe hR
      rw [hrel.eres_inv_right] at h₂
      exact ⟨_, Step.exprStmt h₂, .sres _ _ hR⟩
  | exprStmtHalt he ihe =>
      intro V₁ hR
      obtain ⟨r₂, h₂, hrel⟩ := ihe hR
      rw [hrel.eres_inv_right] at h₂
      exact ⟨_, Step.exprStmtHalt h₂, .sres _ _ hR⟩
  | ifTrue hc hnz hb ihc ihb =>
      intro V₁ hR
      obtain ⟨r₂, h₂, hrel⟩ := ihc hR
      rw [hrel.eres_inv_right] at h₂
      obtain ⟨r₃, h₃, hrel'⟩ := ihb hR
      obtain ⟨Vb₂, rfl, hrel''⟩ := hrel'.sres_inv_right
      exact ⟨_, Step.ifTrue h₂ hnz h₃, .sres _ _ hrel''⟩
  | ifFalse hc hz ihc =>
      intro V₁ hR
      obtain ⟨r₂, h₂, hrel⟩ := ihc hR
      rw [hrel.eres_inv_right] at h₂
      exact ⟨_, Step.ifFalse h₂ hz, .sres _ _ hR⟩
  | ifHalt hc ihc =>
      intro V₁ hR
      obtain ⟨r₂, h₂, hrel⟩ := ihc hR
      rw [hrel.eres_inv_right] at h₂
      exact ⟨_, Step.ifHalt h₂, .sres _ _ hR⟩
  | switchExec hc hb ihc ihb =>
      intro V₁ hR
      obtain ⟨r₂, h₂, hrel⟩ := ihc hR
      rw [hrel.eres_inv_right] at h₂
      obtain ⟨r₃, h₃, hrel'⟩ := ihb hR
      obtain ⟨Vb₂, rfl, hrel''⟩ := hrel'.sres_inv_right
      exact ⟨_, Step.switchExec h₂ h₃, .sres _ _ hrel''⟩
  | switchHalt hc ihc =>
      intro V₁ hR
      obtain ⟨r₂, h₂, hrel⟩ := ihc hR
      rw [hrel.eres_inv_right] at h₂
      exact ⟨_, Step.switchHalt h₂, .sres _ _ hR⟩
  | @forLoop _ V _ init c post body Vinit stinit Vend stend o hinit hloop ihinit ihloop =>
      intro V₁ hR
      obtain ⟨r₂, h₂, hrel⟩ := ihinit hR
      obtain ⟨Vi₁, rfl, hrel'⟩ := hrel.sres_inv_right
      obtain ⟨r₃, h₃, hrel₂⟩ := ihloop hrel'
      obtain ⟨Ve₁, rfl, hrel₃⟩ := hrel₂.sres_inv_right
      refine ⟨_, Step.forLoop h₂ h₃, .sres _ _ ?_⟩
      exact hR.restore_compat hrel₃
        (by rw [hR.length, hrel₃.length]
            exact Nat.le_trans (venvLen_mono hinit rfl) (venvLen_mono hloop rfl))
  | @forInitHalt _ V _ init c post body Vinit stinit hinit ihinit =>
      intro V₁ hR
      obtain ⟨r₂, h₂, hrel⟩ := ihinit hR
      obtain ⟨Vi₁, rfl, hrel'⟩ := hrel.sres_inv_right
      exact ⟨_, Step.forInitHalt h₂,
        .sres _ _ (hR.restore_compat hrel'
          (by rw [hR.length, hrel'.length]; exact venvLen_mono hinit rfl))⟩
  | «break» => intro V₁ hR; exact ⟨_, Step.break, .sres _ _ hR⟩
  | «continue» => intro V₁ hR; exact ⟨_, Step.continue, .sres _ _ hR⟩
  | leave => intro V₁ hR; exact ⟨_, Step.leave, .sres _ _ hR⟩
  | seqNil => intro V₁ hR; exact ⟨_, Step.seqNil, .sres _ _ hR⟩
  | seqCons hs hrest ihs ihrest =>
      intro V₁ hR
      obtain ⟨r₂, h₂, hrel⟩ := ihs hR
      obtain ⟨V₁', rfl, hrel'⟩ := hrel.sres_inv_right
      obtain ⟨r₃, h₃, hrel₂⟩ := ihrest hrel'
      obtain ⟨V₁'', rfl, hrel₃⟩ := hrel₂.sres_inv_right
      exact ⟨_, Step.seqCons h₂ h₃, .sres _ _ hrel₃⟩
  | seqStop hs hne ihs =>
      intro V₁ hR
      obtain ⟨r₂, h₂, hrel⟩ := ihs hR
      obtain ⟨V₁', rfl, hrel'⟩ := hrel.sres_inv_right
      exact ⟨_, Step.seqStop h₂ hne, .sres _ _ hrel'⟩
  | loopDone hc hz ihc =>
      intro V₁ hR
      obtain ⟨r₂, h₂, hrel⟩ := ihc hR
      rw [hrel.eres_inv_right] at h₂
      exact ⟨_, Step.loopDone h₂ hz, .sres _ _ hR⟩
  | loopCondHalt hc ihc =>
      intro V₁ hR
      obtain ⟨r₂, h₂, hrel⟩ := ihc hR
      rw [hrel.eres_inv_right] at h₂
      exact ⟨_, Step.loopCondHalt h₂, .sres _ _ hR⟩
  | loopStep hc hnz hb hob hp hr ihc ihb ihp ihr =>
      intro V₁ hR
      obtain ⟨r₂, h₂, hrel⟩ := ihc hR
      rw [hrel.eres_inv_right] at h₂
      obtain ⟨r₃, h₃, hrel'⟩ := ihb hR
      obtain ⟨Vb₁, rfl, hrelB⟩ := hrel'.sres_inv_right
      obtain ⟨r₄, h₄, hrel₄⟩ := ihp hrelB
      obtain ⟨Vp₁, rfl, hrelP⟩ := hrel₄.sres_inv_right
      obtain ⟨r₅, h₅, hrel₅⟩ := ihr hrelP
      obtain ⟨Ve₁, rfl, hrelE⟩ := hrel₅.sres_inv_right
      exact ⟨_, Step.loopStep h₂ hnz h₃ hob h₄ h₅, .sres _ _ hrelE⟩
  | loopPostHalt hc hnz hb hob hp ihc ihb ihp =>
      intro V₁ hR
      obtain ⟨r₂, h₂, hrel⟩ := ihc hR
      rw [hrel.eres_inv_right] at h₂
      obtain ⟨r₃, h₃, hrel'⟩ := ihb hR
      obtain ⟨Vb₁, rfl, hrelB⟩ := hrel'.sres_inv_right
      obtain ⟨r₄, h₄, hrel₄⟩ := ihp hrelB
      obtain ⟨Vp₁, rfl, hrelP⟩ := hrel₄.sres_inv_right
      exact ⟨_, Step.loopPostHalt h₂ hnz h₃ hob h₄, .sres _ _ hrelP⟩
  | loopBreak hc hnz hb ihc ihb =>
      intro V₁ hR
      obtain ⟨r₂, h₂, hrel⟩ := ihc hR
      rw [hrel.eres_inv_right] at h₂
      obtain ⟨r₃, h₃, hrel'⟩ := ihb hR
      obtain ⟨Vb₁, rfl, hrelB⟩ := hrel'.sres_inv_right
      exact ⟨_, Step.loopBreak h₂ hnz h₃, .sres _ _ hrelB⟩
  | loopLeave hc hnz hb ihc ihb =>
      intro V₁ hR
      obtain ⟨r₂, h₂, hrel⟩ := ihc hR
      rw [hrel.eres_inv_right] at h₂
      obtain ⟨r₃, h₃, hrel'⟩ := ihb hR
      obtain ⟨Vb₁, rfl, hrelB⟩ := hrel'.sres_inv_right
      exact ⟨_, Step.loopLeave h₂ hnz h₃, .sres _ _ hrelB⟩
  | loopBodyHalt hc hnz hb ihc ihb =>
      intro V₁ hR
      obtain ⟨r₂, h₂, hrel⟩ := ihc hR
      rw [hrel.eres_inv_right] at h₂
      obtain ⟨r₃, h₃, hrel'⟩ := ihb hR
      obtain ⟨Vb₁, rfl, hrelB⟩ := hrel'.sres_inv_right
      exact ⟨_, Step.loopBodyHalt h₂ hnz h₃, .sres _ _ hrelB⟩

/-! ### Fresh keys: `x`-mention-free code never adds an `x` key

The lemma that licenses crossing the sink's assignment: after the mention-free
`mid` runs over the inserted `(x, 0)` binding, the entries `mid` pushed above
it cannot be keyed `x`, so `VEnv.set … x val` hits the inserted binding. -/

set_option maxHeartbeats 1600000 in
/-- Executing `x`-mention-free code only adds keys different from `x`. -/
theorem step_new_keys_free {x : Ident} {funs : FunEnv D} {V : VEnv D}
    {st : EvmState} {code : Code Op} {res : Res D}
    (h : Step D funs V st code res) :
    ∀ {V' st' o}, res = .sres V' st' o → codeMentions x code = false →
      ∃ NEW, V'.map Prod.fst = NEW ++ V.map Prod.fst ∧ x ∉ NEW := by
  induction h with
  | lit | var | builtinOk | builtinHalt | builtinArgsHalt | callOk | callHalt
  | callArgsHalt | argsNil | argsCons | argsRestHalt | argsHeadHalt =>
      intro V' st' o heq _; nomatch heq
  | funDef =>
      intro V' st' o heq _
      injection heq with h1 _ _; subst h1
      exact ⟨[], rfl, by simp⟩
  | @block _ V _ body Vb stb o hbody _ =>
      intro V' st' o heq _
      injection heq with h1 _ _; subst h1
      refine ⟨[], ?_, by simp⟩
      rw [restore_keys (venvKeys_suffix hbody rfl) (venvLen_mono hbody rfl)]
      rfl
  | @letZero _ V _ vars =>
      intro V' st' o heq hm
      injection heq with h1 _ _; subst h1
      refine ⟨vars, by simp [bindZeros, Function.comp_def], ?_⟩
      simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff,
        decide_eq_false_iff_not] at hm
      exact hm.1
  | @letVal _ V _ vars e vals _ _ hlen =>
      intro V' st' o heq hm
      injection heq with h1 _ _; subst h1
      refine ⟨vars, ?_, ?_⟩
      · simp only [List.map_append]
        congr 1
        exact List.map_fst_zip (l₂ := vals) (by omega)
      · simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff,
          decide_eq_false_iff_not] at hm
        exact hm.1
  | letHalt =>
      intro V' st' o heq _
      injection heq with h1 _ _; subst h1
      exact ⟨[], rfl, by simp⟩
  | assignVal =>
      intro V' st' o heq _
      injection heq with h1 _ _; subst h1
      exact ⟨[], by rw [VEnv.setMany_keys]; rfl, by simp⟩
  | assignHalt =>
      intro V' st' o heq _
      injection heq with h1 _ _; subst h1
      exact ⟨[], rfl, by simp⟩
  | exprStmt =>
      intro V' st' o heq _
      injection heq with h1 _ _; subst h1
      exact ⟨[], rfl, by simp⟩
  | exprStmtHalt =>
      intro V' st' o heq _
      injection heq with h1 _ _; subst h1
      exact ⟨[], rfl, by simp⟩
  | ifTrue _ _ hb _ ihb =>
      intro V' st' o heq hm
      injection heq with h1 _ _; subst h1
      refine ihb rfl ?_
      simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hm ⊢
      exact hm.2
  | ifFalse =>
      intro V' st' o heq _
      injection heq with h1 _ _; subst h1
      exact ⟨[], rfl, by simp⟩
  | ifHalt =>
      intro V' st' o heq _
      injection heq with h1 _ _; subst h1
      exact ⟨[], rfl, by simp⟩
  | @switchExec _ V _ c cases dflt cv _ _ _ o hc hb _ ihb =>
      intro V' st' o' heq hm
      injection heq with h1 _ _; subst h1
      refine ihb rfl ?_
      simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hm
      simp only [codeMentions, stmtMentions]
      exact selectSwitch_not_mentions hm.1.2 hm.2
  | switchHalt =>
      intro V' st' o heq _
      injection heq with h1 _ _; subst h1
      exact ⟨[], rfl, by simp⟩
  | forLoop hinit hloop _ _ =>
      intro V' st' o heq _
      injection heq with h1 _ _; subst h1
      refine ⟨[], ?_, by simp⟩
      rw [restore_keys ((venvKeys_suffix hinit rfl).trans
          (venvKeys_suffix hloop rfl))
        (Nat.le_trans (venvLen_mono hinit rfl) (venvLen_mono hloop rfl))]
      rfl
  | forInitHalt hinit _ =>
      intro V' st' o heq _
      injection heq with h1 _ _; subst h1
      refine ⟨[], ?_, by simp⟩
      rw [restore_keys (venvKeys_suffix hinit rfl) (venvLen_mono hinit rfl)]
      rfl
  | «break» =>
      intro V' st' o heq _
      injection heq with h1 _ _; subst h1
      exact ⟨[], rfl, by simp⟩
  | «continue» =>
      intro V' st' o heq _
      injection heq with h1 _ _; subst h1
      exact ⟨[], rfl, by simp⟩
  | leave =>
      intro V' st' o heq _
      injection heq with h1 _ _; subst h1
      exact ⟨[], rfl, by simp⟩
  | seqNil =>
      intro V' st' o heq _
      injection heq with h1 _ _; subst h1
      exact ⟨[], rfl, by simp⟩
  | seqCons hs hrest ihs ihrest =>
      intro V' st' o heq hm
      injection heq with h1 _ _; subst h1
      simp only [codeMentions, stmtsMentions, Bool.or_eq_false_iff] at hm
      obtain ⟨N1, he1, hx1⟩ := ihs rfl (by simpa [codeMentions] using hm.1)
      obtain ⟨N2, he2, hx2⟩ := ihrest rfl (by simpa [codeMentions] using hm.2)
      exact ⟨N2 ++ N1, by rw [he2, he1, List.append_assoc], by
        simp only [List.mem_append]
        exact fun hc => hc.elim hx2 hx1⟩
  | seqStop hs hne ihs =>
      intro V' st' o heq hm
      injection heq with h1 _ _; subst h1
      simp only [codeMentions, stmtsMentions, Bool.or_eq_false_iff] at hm
      exact ihs rfl (by simpa [codeMentions] using hm.1)
  | loopDone =>
      intro V' st' o heq _
      injection heq with h1 _ _; subst h1
      exact ⟨[], rfl, by simp⟩
  | loopCondHalt =>
      intro V' st' o heq _
      injection heq with h1 _ _; subst h1
      exact ⟨[], rfl, by simp⟩
  | loopStep _ _ hb _ hp hr _ ihb ihp ihr =>
      intro V' st' o heq hm
      injection heq with h1 _ _; subst h1
      simp only [codeMentions, Bool.or_eq_false_iff] at hm
      obtain ⟨N1, he1, hx1⟩ := ihb rfl
        (by simp [codeMentions, stmtMentions, hm.2])
      obtain ⟨N2, he2, hx2⟩ := ihp rfl
        (by simp [codeMentions, stmtMentions, hm.1.2])
      obtain ⟨N3, he3, hx3⟩ := ihr rfl
        (by simp [codeMentions, hm.1.1, hm.1.2, hm.2])
      refine ⟨N3 ++ N2 ++ N1, ?_, ?_⟩
      · rw [he3, he2, he1]; simp [List.append_assoc]
      · simp only [List.mem_append]
        exact fun hc => hc.elim (fun hc' => hc'.elim hx3 hx2) hx1
  | loopPostHalt _ _ hb _ hp _ ihb ihp =>
      intro V' st' o heq hm
      injection heq with h1 _ _; subst h1
      simp only [codeMentions, Bool.or_eq_false_iff] at hm
      obtain ⟨N1, he1, hx1⟩ := ihb rfl
        (by simp [codeMentions, stmtMentions, hm.2])
      obtain ⟨N2, he2, hx2⟩ := ihp rfl
        (by simp [codeMentions, stmtMentions, hm.1.2])
      refine ⟨N2 ++ N1, ?_, ?_⟩
      · rw [he2, he1, List.append_assoc]
      · simp only [List.mem_append]
        exact fun hc => hc.elim hx2 hx1
  | loopBreak _ _ hb _ ihb =>
      intro V' st' o heq hm
      injection heq with h1 _ _; subst h1
      simp only [codeMentions, Bool.or_eq_false_iff] at hm
      exact ihb rfl (by simp [codeMentions, stmtMentions, hm.2])
  | loopLeave _ _ hb _ ihb =>
      intro V' st' o heq hm
      injection heq with h1 _ _; subst h1
      simp only [codeMentions, Bool.or_eq_false_iff] at hm
      exact ihb rfl (by simp [codeMentions, stmtMentions, hm.2])
  | loopBodyHalt _ _ hb _ ihb =>
      intro V' st' o heq hm
      injection heq with h1 _ _; subst h1
      simp only [codeMentions, Bool.or_eq_false_iff] at hm
      exact ihb rfl (by simp [codeMentions, stmtMentions, hm.2])

/-! ### The mentions bridge

The pass's `mentionsStmt` additionally counts `funDef` and call *names*, so it
is strictly stronger than `Frame`'s `stmtMentions`; a `sink`-checked segment
therefore satisfies the frame lemmas' mention-freeness. -/

mutual
theorem mentionsExpr_bridge {x : Ident} : ∀ {e : Expr Op},
    mentionsExpr x e = false → exprMentions x e = false
  | .lit _, _ => rfl
  | .var y, h => by
      simp only [mentionsExpr, decide_eq_false_iff_not] at h
      simp only [exprMentions, decide_eq_false_iff_not]
      exact fun hc => h hc.symm
  | .builtin op args, h => by
      simp only [mentionsExpr] at h
      simp only [exprMentions]
      exact mentionsArgs_bridge h
  | .call f args, h => by
      simp only [mentionsExpr, Bool.or_eq_false_iff] at h
      simp only [exprMentions]
      exact mentionsArgs_bridge h.2

theorem mentionsArgs_bridge {x : Ident} : ∀ {args : List (Expr Op)},
    mentionsArgs x args = false → argsMentions x args = false
  | [], _ => rfl
  | e :: rest, h => by
      simp only [mentionsArgs, Bool.or_eq_false_iff] at h
      simp only [argsMentions, Bool.or_eq_false_iff]
      exact ⟨mentionsExpr_bridge h.1, mentionsArgs_bridge h.2⟩
end

theorem mentionsOptExpr_bridge {x : Ident} : ∀ {rhs : Option (Expr Op)},
    (rhs.map (mentionsExpr x)).getD false = false →
      optExprMentions x rhs = false
  | none, _ => rfl
  | some e, h => mentionsExpr_bridge (by simpa using h)

mutual
theorem mentionsStmt_bridge {x : Ident} : ∀ {s : Stmt Op},
    mentionsStmt x s = false → stmtMentions x s = false
  | .block body, h => by
      simp only [mentionsStmt] at h
      simp only [stmtMentions]
      exact mentionsStmts_bridge h
  | .funDef n ps rs body, h => by
      simp only [mentionsStmt, Bool.or_eq_false_iff] at h
      simp only [stmtMentions, Bool.or_eq_false_iff]
      exact ⟨⟨by simpa using h.1.1.2, by simpa using h.1.2⟩,
        mentionsStmts_bridge h.2⟩
  | .letDecl xs none, h => by
      simp only [mentionsStmt] at h
      simp only [stmtMentions, Bool.or_eq_false_iff]
      exact ⟨by simpa using h, rfl⟩
  | .letDecl xs (some e), h => by
      simp only [mentionsStmt, Bool.or_eq_false_iff] at h
      simp only [stmtMentions, Bool.or_eq_false_iff]
      exact ⟨by simpa using h.1,
        mentionsOptExpr_bridge (by simpa using h.2)⟩
  | .assign xs e, h => by
      simp only [mentionsStmt, Bool.or_eq_false_iff] at h
      simp only [stmtMentions, Bool.or_eq_false_iff]
      exact ⟨by simpa using h.1, mentionsExpr_bridge h.2⟩
  | .exprStmt e, h => by
      simp only [mentionsStmt] at h
      simp only [stmtMentions]
      exact mentionsExpr_bridge h
  | .cond c body, h => by
      simp only [mentionsStmt, Bool.or_eq_false_iff] at h
      simp only [stmtMentions, Bool.or_eq_false_iff]
      exact ⟨mentionsExpr_bridge h.1, mentionsStmts_bridge h.2⟩
  | .switch c cases dflt, h => by
      simp only [mentionsStmt, Bool.or_eq_false_iff] at h
      simp only [stmtMentions, Bool.or_eq_false_iff]
      exact ⟨⟨mentionsExpr_bridge h.1.1, mentionsCases_bridge h.1.2⟩,
        mentionsDflt_bridge h.2⟩
  | .forLoop init c post body, h => by
      simp only [mentionsStmt, Bool.or_eq_false_iff] at h
      simp only [stmtMentions, Bool.or_eq_false_iff]
      exact ⟨⟨⟨mentionsStmts_bridge h.1.1.1, mentionsExpr_bridge h.1.1.2⟩,
        mentionsStmts_bridge h.1.2⟩, mentionsStmts_bridge h.2⟩
  | .break, _ => rfl
  | .continue, _ => rfl
  | .leave, _ => rfl

theorem mentionsStmts_bridge {x : Ident} : ∀ {ss : List (Stmt Op)},
    mentionsStmts x ss = false → stmtsMentions x ss = false
  | [], _ => rfl
  | s :: rest, h => by
      simp only [mentionsStmts, Bool.or_eq_false_iff] at h
      simp only [stmtsMentions, Bool.or_eq_false_iff]
      exact ⟨mentionsStmt_bridge h.1, mentionsStmts_bridge h.2⟩

theorem mentionsCases_bridge {x : Ident} : ∀ {cs : List (Literal × Block Op)},
    mentionsCases x cs = false → casesMentions x cs = false
  | [], _ => rfl
  | (l, b) :: rest, h => by
      simp only [mentionsCases, Bool.or_eq_false_iff] at h
      simp only [casesMentions, Bool.or_eq_false_iff]
      exact ⟨mentionsStmts_bridge h.1, mentionsCases_bridge h.2⟩

theorem mentionsDflt_bridge {x : Ident} : ∀ {d : Option (Block Op)},
    mentionsDflt x d = false → optBlockMentions x d = false
  | none, _ => rfl
  | some b, h => mentionsStmts_bridge (by simpa [mentionsDflt] using h)
end

/-! ### Structure of a successful `sink` -/

/-- A successful `sink` splits the sequence at the first mention of `x`: an
`x`-free prefix, the singleton assignment (whose right-hand side is `x`-free),
and an untouched tail; the result converts that assignment to a `let`. -/
theorem sink_inv {x : Ident} {ss ss' : List (Stmt Op)}
    (h : sink x ss = some ss') :
    ∃ mid e tail,
      ss = mid ++ .assign [x] e :: tail ∧
      ss' = mid ++ .letDecl [x] (some e) :: tail ∧
      (∀ s ∈ mid, mentionsStmt x s = false) ∧
      mentionsExpr x e = false := by
  induction ss using sink.induct x generalizing ss' with
  | case1 => simp [sink] at h
  | case2 e rest hme =>
      rw [sink, if_pos rfl, if_pos hme] at h
      cases h
  | case3 e rest hme =>
      rw [sink, if_pos rfl, if_neg hme] at h
      injection h with h'
      exact ⟨[], e, rest, by simp, by simp [← h'],
        fun s hs => absurd hs (List.not_mem_nil), by simpa using hme⟩
  | case4 y e rest hy hm =>
      rw [sink, if_neg hy, if_pos hm] at h
      cases h
  | case5 y e rest hy hm ih =>
      rw [sink, if_neg hy, if_neg hm] at h
      cases hrec : sink x rest with
      | none => rw [hrec] at h; cases h
      | some rest' =>
          rw [hrec] at h
          injection h with h'
          obtain ⟨mid, e', tail, rfl, hrest', hmid, he'⟩ := ih hrec
          refine ⟨.assign [y] e :: mid, e', tail, by simp, ?_, ?_, he'⟩
          · rw [← h', hrest']; rfl
          · intro s hs
            rcases List.mem_cons.mp hs with rfl | hs'
            · simpa using hm
            · exact hmid s hs'
  | case6 s rest hshape hm =>
      rw [sink.eq_def] at h
      split at h
      · rename_i heq
        cases heq
      · rename_i y e rest2 heq
        injection heq with h1 h2
        exact absurd h1 (fun hc => hshape y e hc)
      · rename_i heq
        injection heq with h1 h2
        subst h1; subst h2
        rw [if_pos hm] at h
        cases h
  | case7 s rest hshape hm ih =>
      rw [sink.eq_def] at h
      split at h
      · rename_i heq
        cases heq
      · rename_i y e rest2 heq
        injection heq with h1 h2
        exact absurd h1 (fun hc => hshape y e hc)
      · rename_i heq
        injection heq with h1 h2
        subst h1; subst h2
        rw [if_neg hm] at h
        cases hrec : sink x rest with
        | none => rw [hrec] at h; cases h
        | some rest' =>
            rw [hrec] at h
            injection h with h'
            obtain ⟨mid, e', tail, rfl, hrest', hmid, he'⟩ := ih hrec
            refine ⟨s :: mid, e', tail, by simp, ?_, ?_, he'⟩
            · rw [← h', hrest']; rfl
            · intro s' hs
              rcases List.mem_cons.mp hs with rfl | hs'
              · simpa using hm
              · exact hmid s' hs'

/-! ### The accumulated result relation of the fuse sweep -/

/-- One primitive difference the sweep introduces, protecting the bottom `n`
entries: an extra dead binding on the source side (a halt inside a rewritten
site), or one moved binding (the normal path through a sink). -/
inductive FuseStep (n : Nat) : VEnv D → VEnv D → Prop
  | ins {d : Nat} {x : Ident} {v : (evmWithExternal calls creates).Value}
      {V₁ V₂ : VEnv D} :
      InsAt d x v V₂ V₁ → n ≤ d → FuseStep n V₁ V₂
  | mv {x : Ident} {dA dB : Nat} {V₁ V₂ : VEnv D} :
      MvRel x dA dB V₁ V₂ → n ≤ dB → FuseStep n V₁ V₂

/-- Finitely many primitives, composed. -/
inductive FuseChain (n : Nat) : VEnv D → VEnv D → Prop
  | refl (V : VEnv D) : FuseChain n V V
  | head {V₁ V₂ V₃ : VEnv D} :
      FuseStep n V₁ V₂ → FuseChain n V₂ V₃ → FuseChain n V₁ V₃

theorem FuseStep.mono {m n : Nat} {V₁ V₂ : VEnv D} (hmn : m ≤ n)
    (h : FuseStep n V₁ V₂) : FuseStep m V₁ V₂ := by
  cases h with
  | ins hins hd => exact .ins hins (Nat.le_trans hmn hd)
  | mv hmv hd => exact .mv hmv (Nat.le_trans hmn hd)

theorem FuseChain.mono {m n : Nat} {V₁ V₂ : VEnv D} (hmn : m ≤ n)
    (h : FuseChain n V₁ V₂) : FuseChain m V₁ V₂ := by
  induction h with
  | refl => exact .refl _
  | head hs _ ih => exact .head (hs.mono hmn) ih

theorem FuseChain.single {n : Nat} {V₁ V₂ : VEnv D}
    (h : FuseStep n V₁ V₂) : FuseChain n V₁ V₂ :=
  .head h (.refl _)

/-- A base at or below the protected suffix restores both sides equally. -/
theorem FuseStep.restore_eq {n : Nat} {V₀ V₁ V₂ : VEnv D}
    (h : FuseStep n V₁ V₂) (hb : V₀.length ≤ n) :
    restore V₀ V₁ = restore V₀ V₂ := by
  cases h with
  | ins hins hd => exact (restore_insAt_le hins (Nat.le_trans hb hd)).symm
  | @mv x dA dB _ _ hmv hd =>
      cases hmv with
      | mk C A B v hA hdA hdB =>
          exact restore_mv_eq (by omega)

theorem FuseChain.restore_eq {n : Nat} {V₀ V₁ V₂ : VEnv D}
    (h : FuseChain n V₁ V₂) (hb : V₀.length ≤ n) :
    restore V₀ V₁ = restore V₀ V₂ := by
  induction h with
  | refl => rfl
  | head hs _ ih => rw [hs.restore_eq hb, ih]

/-! ### The sink site, forward -/

/-- Split the `x ∉ keys A` fact out of the target `mid` run. -/
theorem above_x_free {funs : FunEnv D} {V A B : VEnv D} {st st' : EvmState}
    {mid : List (Stmt Op)} {x : Ident}
    (hrun : Step D funs V st (.stmts mid) (.sres (A ++ B) st' .normal))
    (hm : codeMentions x (.stmts mid) = false)
    (hB : B.length = V.length) :
    ∀ p ∈ A, p.1 ≠ x := by
  obtain ⟨NEW, hkeys, hxNEW⟩ := step_new_keys_free hrun rfl hm
  have hlenN : NEW.length = A.length := by
    have := congrArg List.length hkeys
    simp only [List.length_map, List.length_append] at this
    omega
  have hsplit : A.map Prod.fst = NEW := by
    have : A.map Prod.fst ++ B.map Prod.fst = NEW ++ V.map Prod.fst := by
      simpa [List.map_append] using hkeys
    exact (List.append_inj this (by simp [hlenN])).1
  intro p hp hc
  exact hxNEW (hsplit ▸ List.mem_map.mpr ⟨p, hp, hc⟩)

theorem mentionsStmts_of_forall {x : Ident} : ∀ {ss : List (Stmt Op)},
    (∀ s ∈ ss, mentionsStmt x s = false) → mentionsStmts x ss = false
  | [], _ => rfl
  | s :: rest, h => by
      simp only [mentionsStmts, Bool.or_eq_false_iff]
      exact ⟨h s (List.mem_cons_self ..), mentionsStmts_of_forall
        (fun s' hs' => h s' (List.mem_cons_of_mem _ hs'))⟩

/-- Inversion for a singleton assignment. -/
theorem assign_inv {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    {x : Ident} {e : Expr Op} {V' : VEnv D} {st' : EvmState} {o : Outcome}
    (h : Step D funs V st (.stmt (.assign [x] e)) (.sres V' st' o)) :
    (∃ val, Step D funs V st (.expr e) (.eres (.vals [val] st')) ∧
      V' = VEnv.set V x val ∧ o = .normal) ∨
    (Step D funs V st (.expr e) (.eres (.halt st')) ∧ V' = V ∧ o = .halt) := by
  cases h with
  | @assignVal _ _ _ _ _ vals _ hev hlen =>
      obtain ⟨val, rfl⟩ : ∃ v, vals = [v] := by
        cases vals with
        | nil => simp at hlen
        | cons a t =>
            cases t with
            | nil => exact ⟨a, rfl⟩
            | cons b t2 => simp at hlen
      exact Or.inl ⟨val, hev, rfl, rfl⟩
  | assignHalt hev => exact Or.inr ⟨hev, rfl, rfl⟩

set_option maxHeartbeats 1600000 in
/-- **The sink site, forward**: a run of
`let x; mid; x := e; tail` (with `mid` and `e` `x`-free) yields a run of
`mid; let x := e; tail` whose result differs by one fuse primitive. -/
theorem sink_site_fwd {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    {x : Ident} {mid tail : List (Stmt Op)} {e : Expr Op}
    (hmid : ∀ s ∈ mid, mentionsStmt x s = false)
    (he : mentionsExpr x e = false)
    {V₁ : VEnv D} {st₁ : EvmState} {o : Outcome}
    (h : Step D funs V st
      (.stmts (.letDecl [x] none :: (mid ++ .assign [x] e :: tail)))
      (.sres V₁ st₁ o)) :
    ∃ V₂, Step D funs V st
      (.stmts (mid ++ .letDecl [x] (some e) :: tail)) (.sres V₂ st₁ o) ∧
      FuseChain V.length V₁ V₂ := by
  -- Bridge the mention hypotheses to the frame lemmas' notion.
  have hmidM : codeMentions x (.stmts mid) = false := by
    show stmtsMentions x mid = false
    exact mentionsStmts_bridge (mentionsStmts_of_forall
      (fun s hs => hmid s hs))
  have heM : exprMentions x e = false := mentionsExpr_bridge he
  -- Invert the head `let x`.
  cases h with
  | seqStop hs hne =>
      cases hs
      exact absurd rfl hne
  | seqCons hs htail0 =>
      cases hs
      -- `htail0` runs `mid ++ assign :: tail` over `(x, 0) :: V`.
      have hins0 : InsAt V.length x (evmWithExternal calls creates).zero
          V ((x, (evmWithExternal calls creates).zero) :: V) :=
        ⟨[], V, rfl, rfl, rfl⟩
      rcases stmts_append_fwd (by simpa [bindZeros] using htail0) with
        ⟨Vm₁, stm, hmidrun, hrest⟩ | ⟨hno, hmidrun⟩
      · -- `mid` completed normally.
        obtain ⟨resm, hmid₂, hrelm⟩ := frameRemove hmidrun hins0 hmidM
        obtain ⟨Vm₂, hresm, hinsm⟩ := ResRelAt.sres_right hrelm
        subst hresm
        obtain ⟨A, B, rfl, rfl, hBd⟩ := hinsm
        have hxA : ∀ p ∈ A, p.1 ≠ x :=
          above_x_free hmid₂ hmidM hBd
        have hAfind : A.find? (fun p => p.1 = x) = none := by
          rw [List.find?_eq_none]
          intro p hp
          simp [hxA p hp]
        -- Invert the assignment.
        cases hrest with
        | seqCons ha htail =>
            rcases assign_inv ha with ⟨val, hev, rfl, -⟩ | ⟨-, -, hno⟩
            · -- Evaluate `e` on the target side.
              obtain ⟨rese, hev₂, hrele⟩ := frameRemove hev
                ⟨A, B, rfl, rfl, hBd⟩ (by simpa [codeMentions] using heM)
              have hrese := ResRelAt.eres_right hrele
              subst hrese
              -- The source assignment hits the inserted binding.
              have hsrcset : VEnv.set
                  (A ++ (x, (evmWithExternal calls creates).zero) :: B)
                  x val = A ++ (x, val) :: B := by
                rw [set_append_of_none hAfind]
                congr 1
                simp [VEnv.set]
              rw [hsrcset] at htail
              -- Relate to the target `let x := e` result.
              have hmv : MvRel x A.length V.length
                  ([] ++ (A ++ (x, val) :: B))
                  ([] ++ ((x, val) :: (A ++ B))) :=
                MvRel.mk [] A B val hxA rfl hBd
              simp only [List.nil_append] at hmv
              obtain ⟨rest₂, htail₂, hrelt⟩ := Step.mv_congr htail hmv
              obtain ⟨V₂, rfl, hrelV⟩ := hrelt.sres_inv
              refine ⟨V₂, ?_, ?_⟩
              · refine stmts_append_normal hmid₂ ?_
                exact Step.seqCons
                  (Step.letVal (vars := [x]) hev₂ (by simp)) htail₂
              · exact FuseChain.single (.mv hrelV (by omega))
            · exact absurd hno.symm (by simp)
        | seqStop ha hne =>
            rcases assign_inv ha with ⟨val, hev, rfl, hno⟩ | ⟨hev, rfl, rfl⟩
            · exact absurd hno hne
            · obtain ⟨rese, hev₂, hrele⟩ := frameRemove hev
                ⟨A, B, rfl, rfl, hBd⟩ (by simpa [codeMentions] using heM)
              have hrese := ResRelAt.eres_right hrele
              subst hrese
              refine ⟨A ++ B, ?_, ?_⟩
              · refine stmts_append_normal hmid₂ ?_
                exact Step.seqStop (Step.letHalt (vars := [x]) hev₂)
                  (by intro hc; cases hc)
              · exact FuseChain.single
                  (.ins ⟨A, B, rfl, rfl, hBd⟩ (by omega))
      · -- `mid` stopped early (halt/break/continue/leave).
        obtain ⟨resm, hmid₂, hrelm⟩ := frameRemove hmidrun hins0 hmidM
        obtain ⟨V₂, hresm, hinsm⟩ := ResRelAt.sres_right hrelm
        subst hresm
        exact ⟨V₂, stmts_append_early hmid₂ hno,
          FuseChain.single (.ins hinsm (by
            obtain ⟨A, B, _, _, hBd⟩ := hinsm
            omega))⟩

/-- Inversion for a singleton `let` with initializer. -/
theorem letSome_inv {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    {x : Ident} {e : Expr Op} {V' : VEnv D} {st' : EvmState} {o : Outcome}
    (h : Step D funs V st (.stmt (.letDecl [x] (some e))) (.sres V' st' o)) :
    (∃ val, Step D funs V st (.expr e) (.eres (.vals [val] st')) ∧
      V' = (x, val) :: V ∧ o = .normal) ∨
    (Step D funs V st (.expr e) (.eres (.halt st')) ∧ V' = V ∧ o = .halt) := by
  cases h with
  | @letVal _ _ _ _ _ vals _ hev hlen =>
      obtain ⟨val, rfl⟩ : ∃ v, vals = [v] := by
        cases vals with
        | nil => simp at hlen
        | cons a t =>
            cases t with
            | nil => exact ⟨a, rfl⟩
            | cons b t2 => simp at hlen
      exact Or.inl ⟨val, hev, by simp, rfl⟩
  | letHalt hev => exact Or.inr ⟨hev, rfl, rfl⟩

set_option maxHeartbeats 1600000 in
/-- **The sink site, backward**: a run of the rewritten
`mid; let x := e; tail` yields a run of the original
`let x; mid; x := e; tail`, with the same fuse-primitive difference. -/
theorem sink_site_bwd {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    {x : Ident} {mid tail : List (Stmt Op)} {e : Expr Op}
    (hmid : ∀ s ∈ mid, mentionsStmt x s = false)
    (he : mentionsExpr x e = false)
    {V₂ : VEnv D} {st₁ : EvmState} {o : Outcome}
    (h : Step D funs V st
      (.stmts (mid ++ .letDecl [x] (some e) :: tail)) (.sres V₂ st₁ o)) :
    ∃ V₁, Step D funs V st
      (.stmts (.letDecl [x] none :: (mid ++ .assign [x] e :: tail)))
      (.sres V₁ st₁ o) ∧
      FuseChain V.length V₁ V₂ := by
  have hmidM : codeMentions x (.stmts mid) = false := by
    show stmtsMentions x mid = false
    exact mentionsStmts_bridge (mentionsStmts_of_forall (fun s hs => hmid s hs))
  have heM : exprMentions x e = false := mentionsExpr_bridge he
  have hins0 : InsAt V.length x (evmWithExternal calls creates).zero
      V ((x, (evmWithExternal calls creates).zero) :: V) :=
    ⟨[], V, rfl, rfl, rfl⟩
  rcases stmts_append_fwd h with
    ⟨Vm₂, stm, hmidrun, hrest⟩ | ⟨hno, hmidrun⟩
  · -- `mid` completed normally on the target side.
    obtain ⟨resm, hmid₁, hrelm⟩ := frameAdd hmidrun hins0 hmidM
    obtain ⟨Vm₁, hresm, hinsm⟩ := ResRelAt.sres hrelm
    subst hresm
    obtain ⟨A, B, rfl, rfl, hBd⟩ := hinsm
    have hxA : ∀ p ∈ A, p.1 ≠ x :=
      above_x_free hmidrun hmidM hBd
    have hAfind : A.find? (fun p => p.1 = x) = none := by
      rw [List.find?_eq_none]
      intro p hp
      simp [hxA p hp]
    cases hrest with
    | seqCons ha htail =>
        rcases letSome_inv ha with ⟨val, hev, rfl, -⟩ | ⟨-, -, hno⟩
        · -- Evaluate `e` on the source side (with the inserted binding).
          obtain ⟨rese, hev₁, hrele⟩ := frameAdd hev
            ⟨A, B, rfl, rfl, hBd⟩ (by simpa [codeMentions] using heM)
          have hrese := ResRelAt.eres hrele
          subst hrese
          -- The source assignment hits the inserted binding.
          have hsrcset : VEnv.set
              (A ++ (x, (evmWithExternal calls creates).zero) :: B)
              x val = A ++ (x, val) :: B := by
            rw [set_append_of_none hAfind]
            congr 1
            simp [VEnv.set]
          have hmv : MvRel x A.length V.length
              ([] ++ (A ++ (x, val) :: B))
              ([] ++ ((x, val) :: (A ++ B))) :=
            MvRel.mk [] A B val hxA rfl hBd
          simp only [List.nil_append] at hmv
          obtain ⟨rest₁, htail₁, hrelt⟩ := Step.mv_congr_bwd htail hmv
          obtain ⟨V₁, hres₁, hrelV⟩ := hrelt.sres_inv_right
          subst hres₁
          refine ⟨V₁, ?_, FuseChain.single (.mv hrelV (by omega))⟩
          refine Step.seqCons Step.letZero ?_
          show Step D funs ((x, (evmWithExternal calls creates).zero) :: V)
            st (.stmts (mid ++ .assign [x] e :: tail)) _
          refine stmts_append_normal hmid₁ ?_
          refine Step.seqCons ?_ htail₁
          have := Step.assignVal (vars := [x]) hev₁ (by simp)
          rwa [show VEnv.setMany
            (A ++ (x, (evmWithExternal calls creates).zero) :: B) [x] [val] =
            A ++ (x, val) :: B from hsrcset] at this
        · exact absurd hno.symm (by simp)
    | seqStop ha hne =>
        rcases letSome_inv ha with ⟨val, hev, rfl, hno⟩ | ⟨hev, rfl, rfl⟩
        · exact absurd hno hne
        · obtain ⟨rese, hev₁, hrele⟩ := frameAdd hev
            ⟨A, B, rfl, rfl, hBd⟩ (by simpa [codeMentions] using heM)
          have hrese := ResRelAt.eres hrele
          subst hrese
          refine ⟨A ++ (x, (evmWithExternal calls creates).zero) :: B, ?_,
            FuseChain.single (.ins ⟨A, B, rfl, rfl, hBd⟩ (by omega))⟩
          refine Step.seqCons Step.letZero ?_
          show Step D funs ((x, (evmWithExternal calls creates).zero) :: V)
            st (.stmts (mid ++ .assign [x] e :: tail)) _
          refine stmts_append_normal hmid₁ ?_
          exact Step.seqStop (Step.assignHalt (vars := [x]) hev₁)
            (by intro hc; cases hc)
  · -- `mid` stopped early on the target side.
    obtain ⟨resm, hmid₁, hrelm⟩ := frameAdd hmidrun hins0 hmidM
    obtain ⟨V₁, hresm, hinsm⟩ := ResRelAt.sres hrelm
    subst hresm
    refine ⟨V₁, ?_, FuseChain.single (.ins hinsm (by
      obtain ⟨A, B, _, _, hBd⟩ := hinsm
      omega))⟩
    refine Step.seqCons Step.letZero ?_
    show Step D funs ((x, (evmWithExternal calls creates).zero) :: V)
      st (.stmts (mid ++ .assign [x] e :: tail)) _
    exact stmts_append_early hmid₁ hno

/-! ### The adjacent literal fuse site -/

/-- Forward: a run of `let x := lit; x := e; rest` yields a run of
`let x := e; rest` — identical on the normal path (the literal value is
overwritten before anything reads it), one dead insertion on halt paths. -/
theorem fuse_site_fwd {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    {x : Ident} {l : Literal} {e : Expr Op} {rest : List (Stmt Op)}
    (he : mentionsExpr x e = false)
    {V₁ : VEnv D} {st₁ : EvmState} {o : Outcome}
    (h : Step D funs V st
      (.stmts (.letDecl [x] (some (.lit l)) :: .assign [x] e :: rest))
      (.sres V₁ st₁ o)) :
    ∃ V₂, Step D funs V st (.stmts (.letDecl [x] (some e) :: rest))
      (.sres V₂ st₁ o) ∧ FuseChain V.length V₁ V₂ := by
  have heM : exprMentions x e = false := mentionsExpr_bridge he
  have hins : InsAt V.length x ((evmWithExternal calls creates).litValue l)
      V ((x, (evmWithExternal calls creates).litValue l) :: V) :=
    ⟨[], V, rfl, rfl, rfl⟩
  cases h with
  | seqStop hlet hne =>
      rcases letSome_inv hlet with ⟨val, hev, rfl, hno⟩ | ⟨hev, rfl, rfl⟩
      · exact absurd hno hne
      · nomatch hev
  | seqCons hlet htail0 =>
      rcases letSome_inv hlet with ⟨val, hev, rfl, -⟩ | ⟨-, -, hno⟩
      · -- The literal evaluates to its value without touching state.
        cases hev with
        | lit =>
          -- Invert the assignment over the extended environment.
          cases htail0 with
          | seqCons ha htail =>
              rcases assign_inv ha with ⟨val', hev', hset, -⟩ | ⟨-, -, hno⟩
              · -- `e` evaluates identically without the binding.
                obtain ⟨rese, hev₂, hrele⟩ := frameRemove hev' hins
                  (by simpa [codeMentions] using heM)
                have hrese := ResRelAt.eres_right hrele
                subst hrese
                have hseteq : VEnv.set
                    ((x, (evmWithExternal calls creates).litValue l) :: V)
                    x val' = (x, val') :: V := by
                  simp [VEnv.set]
                rw [hset, hseteq] at htail
                exact ⟨V₁, Step.seqCons
                  (by simpa using Step.letVal (vars := [x]) hev₂ (by simp))
                  htail, .refl _⟩
              · nomatch hno
          | seqStop ha hne =>
              rcases assign_inv ha with ⟨val', hev', hset, hno⟩ | ⟨hev', rfl, rfl⟩
              · exact absurd hno hne
              · obtain ⟨rese, hev₂, hrele⟩ := frameRemove hev' hins
                  (by simpa [codeMentions] using heM)
                have hrese := ResRelAt.eres_right hrele
                subst hrese
                exact ⟨V, Step.seqStop (Step.letHalt (vars := [x]) hev₂)
                  (by intro hc; cases hc),
                  FuseChain.single (.ins hins (Nat.le_refl _))⟩
      · nomatch hno.symm

/-- Backward: a run of the fused `let x := e; rest` yields a run of the
original pair. -/
theorem fuse_site_bwd {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    {x : Ident} {l : Literal} {e : Expr Op} {rest : List (Stmt Op)}
    (he : mentionsExpr x e = false)
    {V₂ : VEnv D} {st₁ : EvmState} {o : Outcome}
    (h : Step D funs V st (.stmts (.letDecl [x] (some e) :: rest))
      (.sres V₂ st₁ o)) :
    ∃ V₁, Step D funs V st
      (.stmts (.letDecl [x] (some (.lit l)) :: .assign [x] e :: rest))
      (.sres V₁ st₁ o) ∧ FuseChain V.length V₁ V₂ := by
  have heM : exprMentions x e = false := mentionsExpr_bridge he
  have hins : InsAt V.length x ((evmWithExternal calls creates).litValue l)
      V ((x, (evmWithExternal calls creates).litValue l) :: V) :=
    ⟨[], V, rfl, rfl, rfl⟩
  have hlet1 : ∀ st2, Step D funs V st2 (.stmt (.letDecl [x] (some (.lit l))))
      (.sres ((x, (evmWithExternal calls creates).litValue l) :: V) st2 .normal) :=
    fun st2 => by simpa using Step.letVal (vars := [x]) Step.lit (by simp)
  cases h with
  | seqStop hlet hne =>
      rcases letSome_inv hlet with ⟨val, hev, rfl, hno⟩ | ⟨hev, rfl, rfl⟩
      · exact absurd hno hne
      · -- `e` halts: source runs the literal `let`, then the assignment halts.
        obtain ⟨rese, hev₁, hrele⟩ := frameAdd hev hins
          (by simpa [codeMentions] using heM)
        have hrese := ResRelAt.eres hrele
        subst hrese
        refine ⟨_, Step.seqCons (hlet1 st) ?_,
          FuseChain.single (.ins hins (Nat.le_refl _))⟩
        exact Step.seqStop (Step.assignHalt (vars := [x]) hev₁)
          (by intro hc; cases hc)
  | seqCons hlet htail =>
      rcases letSome_inv hlet with ⟨val, hev, rfl, -⟩ | ⟨-, -, hno⟩
      · obtain ⟨rese, hev₁, hrele⟩ := frameAdd hev hins
          (by simpa [codeMentions] using heM)
        have hrese := ResRelAt.eres hrele
        subst hrese
        refine ⟨V₂, Step.seqCons (hlet1 st) (Step.seqCons ?_ htail), .refl _⟩
        have hseteq : VEnv.set
            ((x, (evmWithExternal calls creates).litValue l) :: V)
            x val = (x, val) :: V := by
          simp [VEnv.set]
        have := Step.assignVal (vars := [x]) hev₁ (by simp)
        rw [show VEnv.setMany
          ((x, (evmWithExternal calls creates).litValue l) :: V) [x] [val] =
          (x, val) :: V from hseteq] at this
        exact this
      · nomatch hno.symm

theorem FuseChain.trans {n : Nat} {V₁ V₂ V₃ : VEnv D}
    (h₁ : FuseChain n V₁ V₂) (h₂ : FuseChain n V₂ V₃) : FuseChain n V₁ V₃ := by
  induction h₁ with
  | refl => exact h₂
  | head hs _ ih => exact .head hs (ih h₂)

/-! ### The sweep, forward -/

/-- The sweep's generic cons equation, by exhaustive shape analysis. -/
theorem fuseSeqFuel_cons_generic (fuel : Nat) (s : Stmt Op)
    (rest : List (Stmt Op))
    (h1 : ∀ x, s = .letDecl [x] none → False)
    (h2 : ∀ x l y e rest', s = .letDecl [x] (some (.lit l)) →
      rest = .assign [y] e :: rest' → False) :
    fuseSeqFuel (fuel + 1) (s :: rest) = s :: fuseSeqFuel fuel rest := by
  match s, rest with
  | .letDecl [x] none, _ => exact (h1 x rfl).elim
  | .letDecl [x] (some (.lit l)), .assign [y] e :: rest' =>
      exact (h2 x l y e rest' rfl rfl).elim
  | .letDecl [x] (some (.lit l)), [] => rfl
  | .letDecl [x] (some (.lit l)), .assign [] e :: rest' => rfl
  | .letDecl [x] (some (.lit l)), .assign (y :: z :: ys) e :: rest' => rfl
  | .letDecl [x] (some (.lit l)), .letDecl xs rhs :: rest' => rfl
  | .letDecl [x] (some (.lit l)), .block b :: rest' => rfl
  | .letDecl [x] (some (.lit l)), .funDef n ps rs b :: rest' => rfl
  | .letDecl [x] (some (.lit l)), .exprStmt e :: rest' => rfl
  | .letDecl [x] (some (.lit l)), .cond c b :: rest' => rfl
  | .letDecl [x] (some (.lit l)), .switch c cs d :: rest' => rfl
  | .letDecl [x] (some (.lit l)), .forLoop i c p b :: rest' => rfl
  | .letDecl [x] (some (.lit l)), .break :: rest' => rfl
  | .letDecl [x] (some (.lit l)), .continue :: rest' => rfl
  | .letDecl [x] (some (.lit l)), .leave :: rest' => rfl
  | .letDecl [x] (some (.var v)), _ => rfl
  | .letDecl [x] (some (.builtin op args)), _ => rfl
  | .letDecl [x] (some (.call f args)), _ => rfl
  | .letDecl [] rhs, _ => rfl
  | .letDecl (x :: y :: xs) rhs, _ => rfl
  | .block b, _ => rfl
  | .funDef n ps rs b, _ => rfl
  | .assign xs e, _ => rfl
  | .exprStmt e, _ => rfl
  | .cond c b, _ => rfl
  | .switch c cs d, _ => rfl
  | .forLoop i c p b, _ => rfl
  | .break, _ => rfl
  | .continue, _ => rfl
  | .leave, _ => rfl

set_option maxHeartbeats 3200000 in
/-- **The fuse sweep, forward**: a run of a sequence yields a run of its
swept form, with the accumulated primitive differences protected below the
entry environment. -/
theorem fuseSeqFuel_fwd (fuel : Nat) (ss : List (Stmt Op))
    {funs : FunEnv D} {V : VEnv D} {st : EvmState} {V₁ : VEnv D}
    {st₁ : EvmState} {o : Outcome}
    (h : Step D funs V st (.stmts ss) (.sres V₁ st₁ o)) :
    ∃ V₂, Step D funs V st (.stmts (fuseSeqFuel fuel ss)) (.sres V₂ st₁ o) ∧
      FuseChain V.length V₁ V₂ := by
  induction fuel, ss using fuseSeqFuel.induct generalizing funs V st V₁ st₁ o with
  | case1 ss => exact ⟨_, h, .refl _⟩
  | case2 fuel => exact ⟨_, h, .refl _⟩
  | @case3 fuel x rest rest' hs ih =>
      rw [show fuseSeqFuel (fuel + 1) (.letDecl [x] none :: rest) =
        fuseSeqFuel fuel rest' from by rw [fuseSeqFuel, hs]]
      obtain ⟨mid, e, tail, rfl, rfl, hmid, he⟩ := sink_inv hs
      obtain ⟨V₂, h₂, hchain⟩ := sink_site_fwd hmid he h
      obtain ⟨V₃, h₃, hchain₂⟩ := ih h₂
      exact ⟨V₃, h₃, hchain.trans hchain₂⟩
  | @case4 fuel x rest hs ih =>
      rw [show fuseSeqFuel (fuel + 1) (.letDecl [x] none :: rest) =
        .letDecl [x] none :: fuseSeqFuel fuel rest from by
          rw [fuseSeqFuel, hs]]
      cases h with
      | seqCons hlet htail =>
          cases hlet
          obtain ⟨V₂, h₂, hchain⟩ := ih htail
          exact ⟨V₂, Step.seqCons Step.letZero h₂,
            hchain.mono (by simp [bindZeros])⟩
      | seqStop hlet hne =>
          cases hlet
          exact absurd rfl hne
  | @case5 fuel x l y e rest hguard ih =>
      obtain ⟨hxy, hme⟩ := by
        simpa [Bool.and_eq_true, decide_eq_true_eq] using hguard
      subst hxy
      rw [show fuseSeqFuel (fuel + 1)
          (.letDecl [x] (some (.lit l)) :: .assign [x] e :: rest) =
        fuseSeqFuel fuel (.letDecl [x] (some e) :: rest) from by
          rw [fuseSeqFuel, if_pos hguard]]
      obtain ⟨V₂, h₂, hchain⟩ := fuse_site_fwd (by simpa using hme) h
      obtain ⟨V₃, h₃, hchain₂⟩ := ih h₂
      exact ⟨V₃, h₃, hchain.trans hchain₂⟩
  | @case6 fuel x l y e rest hguard ih =>
      rw [show fuseSeqFuel (fuel + 1)
          (.letDecl [x] (some (.lit l)) :: .assign [y] e :: rest) =
        .letDecl [x] (some (.lit l)) ::
          fuseSeqFuel fuel (.assign [y] e :: rest) from by
          rw [fuseSeqFuel, if_neg hguard]]
      cases h with
      | seqCons hlet htail =>
          rcases letSome_inv hlet with ⟨val, hev, rfl, -⟩ | ⟨-, -, hno⟩
          · obtain ⟨V₂, h₂, hchain⟩ := ih htail
            exact ⟨V₂, Step.seqCons
              (Step.letVal (vars := [x]) hev (by simp)) h₂,
              hchain.mono (by simp)⟩
          · nomatch hno.symm
      | seqStop hlet hne =>
          rcases letSome_inv hlet with ⟨val, hev, rfl, hno⟩ | ⟨hev, rfl, rfl⟩
          · exact absurd hno hne
          · nomatch hev
  | @case7 fuel s rest hshape1 hshape2 ih =>
      have hgen : fuseSeqFuel (fuel + 1) (s :: rest) =
          s :: fuseSeqFuel fuel rest :=
        fuseSeqFuel_cons_generic fuel s rest hshape1 hshape2
      rw [hgen]
      cases h with
      | seqCons hs htail =>
          obtain ⟨V₂, h₂, hchain⟩ := ih htail
          exact ⟨V₂, Step.seqCons hs h₂,
            hchain.mono (venvLen_mono hs rfl)⟩
      | seqStop hs hne =>
          exact ⟨V₁, Step.seqStop hs hne, .refl _⟩

/-! ### The sweep, backward -/

set_option maxHeartbeats 3200000 in
/-- **The fuse sweep, backward**: a run of the swept sequence yields a run of
the original, with the same protected primitive differences. -/
theorem fuseSeqFuel_bwd (fuel : Nat) (ss : List (Stmt Op))
    {funs : FunEnv D} {V : VEnv D} {st : EvmState} {V₂ : VEnv D}
    {st₁ : EvmState} {o : Outcome}
    (h : Step D funs V st (.stmts (fuseSeqFuel fuel ss)) (.sres V₂ st₁ o)) :
    ∃ V₁, Step D funs V st (.stmts ss) (.sres V₁ st₁ o) ∧
      FuseChain V.length V₁ V₂ := by
  induction fuel, ss using fuseSeqFuel.induct generalizing funs V st V₂ st₁ o with
  | case1 ss => exact ⟨_, h, .refl _⟩
  | case2 fuel => exact ⟨_, h, .refl _⟩
  | @case3 fuel x rest rest' hs ih =>
      rw [show fuseSeqFuel (fuel + 1) (.letDecl [x] none :: rest) =
        fuseSeqFuel fuel rest' from by rw [fuseSeqFuel, hs]] at h
      obtain ⟨mid, e, tail, hrest, hrest', hmid, he⟩ := sink_inv hs
      obtain ⟨V₁', h₁, hchain⟩ := ih h
      rw [hrest'] at h₁
      obtain ⟨V₁, h₀, hchain₀⟩ := sink_site_bwd hmid he h₁
      rw [← hrest] at h₀
      exact ⟨V₁, h₀, hchain₀.trans hchain⟩
  | @case4 fuel x rest hs ih =>
      rw [show fuseSeqFuel (fuel + 1) (.letDecl [x] none :: rest) =
        .letDecl [x] none :: fuseSeqFuel fuel rest from by
          rw [fuseSeqFuel, hs]] at h
      cases h with
      | seqCons hlet htail =>
          cases hlet
          obtain ⟨V₁, h₁, hchain⟩ := ih htail
          exact ⟨V₁, Step.seqCons Step.letZero h₁,
            hchain.mono (by simp [bindZeros])⟩
      | seqStop hlet hne =>
          cases hlet
          exact absurd rfl hne
  | @case5 fuel x l y e rest hguard ih =>
      obtain ⟨hxy, hme⟩ := by
        simpa [Bool.and_eq_true, decide_eq_true_eq] using hguard
      subst hxy
      rw [show fuseSeqFuel (fuel + 1)
          (.letDecl [x] (some (.lit l)) :: .assign [x] e :: rest) =
        fuseSeqFuel fuel (.letDecl [x] (some e) :: rest) from by
          rw [fuseSeqFuel, if_pos hguard]] at h
      obtain ⟨V₁', h₁, hchain⟩ := ih h
      obtain ⟨V₁, h₀, hchain₀⟩ := fuse_site_bwd (l := l)
        (by simpa using hme) h₁
      exact ⟨V₁, h₀, hchain₀.trans hchain⟩
  | @case6 fuel x l y e rest hguard ih =>
      rw [show fuseSeqFuel (fuel + 1)
          (.letDecl [x] (some (.lit l)) :: .assign [y] e :: rest) =
        .letDecl [x] (some (.lit l)) ::
          fuseSeqFuel fuel (.assign [y] e :: rest) from by
          rw [fuseSeqFuel, if_neg hguard]] at h
      cases h with
      | seqCons hlet htail =>
          rcases letSome_inv hlet with ⟨val, hev, rfl, -⟩ | ⟨-, -, hno⟩
          · obtain ⟨V₁, h₁, hchain⟩ := ih htail
            exact ⟨V₁, Step.seqCons
              (Step.letVal (vars := [x]) hev (by simp)) h₁,
              hchain.mono (by simp)⟩
          · nomatch hno.symm
      | seqStop hlet hne =>
          rcases letSome_inv hlet with ⟨val, hev, rfl, hno⟩ | ⟨hev, rfl, rfl⟩
          · exact absurd hno hne
          · nomatch hev
  | @case7 fuel s rest hshape1 hshape2 ih =>
      rw [fuseSeqFuel_cons_generic fuel s rest hshape1 hshape2] at h
      cases h with
      | seqCons hs htail =>
          obtain ⟨V₁, h₁, hchain⟩ := ih htail
          exact ⟨V₁, Step.seqCons hs h₁,
            hchain.mono (venvLen_mono hs rfl)⟩
      | seqStop hs hne =>
          exact ⟨V₂, Step.seqStop hs hne, .refl _⟩

end YulEvmCompiler.Optimizer.FuseDeclAssign
