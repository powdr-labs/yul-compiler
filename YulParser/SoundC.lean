import YulParser.Canon
import YulParser.Tokens

/-!
# YulParser.SoundC

The `canon`-level soundness invariant and its combinator lemmas, mirroring
`YulParser.Sound` but with `canon` in place of `fws`. Because `canon` is not a
per-character filter, the invariant additionally carries `Closed (pr a)` (the
printed form does not merge with its continuation), which is what makes the
sequencing lemma compose. To keep printed forms `Closed`, every atom prints its
token *followed by a delimiting space*, so combinators just concatenate (no
separators inserted).
-/

namespace YulParser

open YulParser (Parser andThen pmap orElse opt token skipWs many manyP isWs)

/-- Every successful parse re-prints (via `pr`) to the consumed prefix up to
`canon`, and the printed form is `Closed`. -/
def SoundC {α : Type} (p : Parser α) (pr : α → List Char) : Prop :=
  ∀ cs a rest, p cs = some (a, rest) → canon (pr a) ++ canon rest = canon cs ∧ Closed (pr a)


/-! ### Sequencing -/

theorem andThenC {α β : Type} {p : Parser α} {q : Parser β}
    {pr1 : α → List Char} {pr2 : β → List Char}
    (hp : SoundC p pr1) (hq : SoundC q pr2) :
    SoundC (andThen p q) (fun ab => pr1 ab.1 ++ pr2 ab.2) := by
  intro cs ab rest h
  simp only [andThen, Option.bind_eq_some_iff] at h
  obtain ⟨⟨a, r1⟩, hp', ⟨b, r2⟩, hq', heq⟩ := h
  simp only [Option.some.injEq, Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  obtain ⟨e1, c1⟩ := hp cs a r1 hp'
  obtain ⟨e2, c2⟩ := hq r1 b r2 hq'
  refine ⟨?_, closed_append c1 c2⟩
  rw [c1 (pr2 b), List.append_assoc, e2, e1]

/-! ### Map -/

theorem pmapC {α β : Type} {f : α → β} {p : Parser α}
    {pr : α → List Char} {pr' : β → List Char}
    (hp : SoundC p pr)
    (hf : ∀ a, canon (pr' (f a)) = canon (pr a))
    (hcl : ∀ a, Closed (pr a) → Closed (pr' (f a))) :
    SoundC (pmap f p) pr' := by
  intro cs b rest h
  simp only [pmap, Option.bind_eq_some_iff] at h
  obtain ⟨⟨a, r⟩, hp', heq⟩ := h
  simp only [Option.some.injEq, Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  obtain ⟨e, c⟩ := hp cs a r hp'
  exact ⟨by rw [hf a]; exact e, hcl a c⟩

/-- Common special case: the mapped printer produces exactly the same string. -/
theorem pmapC_eq {α β : Type} {f : α → β} {p : Parser α}
    {pr : α → List Char} {pr' : β → List Char}
    (hp : SoundC p pr) (hf : ∀ a, pr' (f a) = pr a) :
    SoundC (pmap f p) pr' :=
  pmapC hp (fun a => by rw [hf a]) (fun a c => by rw [hf a]; exact c)

/-! ### Choice -/

theorem orElseC {α : Type} {p q : Parser α} {pr : α → List Char}
    (hp : SoundC p pr) (hq : SoundC q pr) : SoundC (orElse p q) pr := by
  intro cs a rest h
  simp only [orElse] at h
  split at h
  · rename_i r heq; rw [Option.some.injEq] at h; subst h; exact hp cs a rest heq
  · exact hq cs a rest h

/-! ### Option -/

theorem optC {α : Type} {p : Parser α} {pr : α → List Char} (hp : SoundC p pr) :
    SoundC (opt p) (fun o => match o with | some a => pr a | none => []) := by
  intro cs o rest h
  simp only [opt] at h
  split at h
  · rename_i a r heq
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hp cs a r heq
  · rename_i heq
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by simp, closed_nil⟩

/-! ### Whitespace-skipping token -/

theorem tokenC {α : Type} {p : Parser α} {pr : α → List Char} (hp : SoundC p pr) :
    SoundC (token p) pr := by
  intro cs a rest h
  simp only [token] at h
  obtain ⟨e, c⟩ := hp _ a rest h
  exact ⟨by rw [e, canon_skipTrivia], c⟩

/-! ### Repetition -/

/-- Printer for a repeated parser: concatenate the element prints (each already
delimited). -/
def printManyC {α : Type} (pr : α → List Char) : List α → List Char
  | [] => []
  | a :: as => pr a ++ printManyC pr as

theorem closed_printManyC {α : Type} {pr : α → List Char} {as : List α}
    (h : ∀ a ∈ as, Closed (pr a)) : Closed (printManyC pr as) := by
  induction as with
  | nil => exact closed_nil
  | cons a as ih =>
    exact closed_append (h a (by simp)) (ih (fun x hx => h x (by simp [hx])))

theorem manyC_raw {α : Type} {p : Parser α} {pr : α → List Char} (hp : SoundC p pr)
    (cs : List Char) :
    canon (printManyC pr (many p cs).1) ++ canon (many p cs).2 = canon cs
      ∧ Closed (printManyC pr (many p cs).1) := by
  fun_induction many p cs with
  | case1 cs hpc => simp [printManyC, closed_nil]
  | case2 cs a rest hpc hlt ih =>
    simp only [printManyC]
    obtain ⟨e, c⟩ := hp cs a rest hpc
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨?_, closed_append c ih2⟩
    rw [c (printManyC pr (many p rest).1), List.append_assoc, ih1, e]
  | case3 cs a rest hpc hlt =>
    simp only [printManyC]
    obtain ⟨e, c⟩ := hp cs a rest hpc
    exact ⟨by rw [List.append_nil]; exact e, by rw [List.append_nil]; exact c⟩

theorem manyC {α : Type} {p : Parser α} {pr : α → List Char} (hp : SoundC p pr) :
    SoundC (manyP p) (printManyC pr) := by
  intro cs a rest h
  simp only [manyP, Option.some.injEq] at h
  have ha : a = (many p cs).1 := by rw [h]
  have hr : rest = (many p cs).2 := by rw [h]
  subst ha hr
  exact manyC_raw hp cs

end YulParser
