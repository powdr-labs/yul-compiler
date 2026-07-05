import YulParser.Core

/-!
# YulParser.Combinators

Sequencing, choice, option, and repetition combinators, each with a soundness
lemma phrased against the printer that re-assembles the pieces. Printers glue
sub-prints with whitespace separators; since `fws` deletes whitespace, the
`Sound` invariant chains through `fws_append`.
-/

namespace YulParser

/-- A whitespace separator (a single space). `fws` of it is empty. -/
def sep : List Char := [' ']

@[simp] theorem fws_sep : fws sep = [] := rfl

/-- Whitespace separators vanish under `fws`, so a printed `a ++ ws ++ b` has the
same significant content as `a ++ b`. -/
theorem fws_glue (a b : List Char) : fws (a ++ sep ++ b) = fws a ++ fws b := by
  rw [fws_append, fws_append, fws_sep, List.append_nil]

/-! ### Sequencing -/

/-- Run `p` then `q`, pairing the results. -/
def andThen {α β : Type} (p : Parser α) (q : Parser β) : Parser (α × β) := fun cs =>
  (p cs).bind fun ar => (q ar.2).bind fun br => some ((ar.1, br.1), br.2)

theorem andThen_sound {α β : Type} {p : Parser α} {q : Parser β}
    {pr1 : α → List Char} {pr2 : β → List Char}
    (hp : Sound p pr1) (hq : Sound q pr2) :
    Sound (andThen p q) (fun ab => pr1 ab.1 ++ sep ++ pr2 ab.2) := by
  intro cs ab rest h
  simp only [andThen, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨a, r1⟩, hp', ⟨b, r2⟩, hq', heq⟩ := h
  simp only [Option.some.injEq, Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  have e1 := hp cs a r1 hp'
  have e2 := hq r1 b r2 hq'
  simp only [fws_glue]
  rw [List.append_assoc, e2, e1]

/-! ### Map -/

/-- Transform the result of a parser. -/
def pmap {α β : Type} (f : α → β) (p : Parser α) : Parser β := fun cs =>
  (p cs).bind fun ar => some (f ar.1, ar.2)

theorem pmap_sound {α β : Type} {f : α → β} {p : Parser α}
    {pr : α → List Char} {pr' : β → List Char}
    (hp : Sound p pr) (hf : ∀ a, fws (pr' (f a)) = fws (pr a)) :
    Sound (pmap f p) pr' := by
  intro cs b rest h
  simp only [pmap, Option.bind_eq_some_iff] at h
  obtain ⟨⟨a, r⟩, hp', heq⟩ := h
  simp only [Option.some.injEq, Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  rw [hf a]; exact hp cs a r hp'

/-! ### Choice -/

/-- Try `p`; on failure, try `q`. -/
def orElse {α : Type} (p q : Parser α) : Parser α := fun cs =>
  match p cs with
  | some r => some r
  | none => q cs

theorem orElse_sound {α : Type} {p q : Parser α} {pr : α → List Char}
    (hp : Sound p pr) (hq : Sound q pr) : Sound (orElse p q) pr := by
  intro cs a rest h
  simp only [orElse] at h
  split at h
  · rename_i r heq
    rw [Option.some.injEq] at h; subst h; exact hp cs a rest heq
  · exact hq cs a rest h

/-! ### Option -/

/-- Optionally run `p`. -/
def opt {α : Type} (p : Parser α) : Parser (Option α) := fun cs =>
  match p cs with
  | some (a, r) => some (some a, r)
  | none => some (none, cs)

theorem opt_sound {α : Type} {p : Parser α} {pr : α → List Char}
    (hp : Sound p pr) :
    Sound (opt p) (fun o => match o with | some a => pr a | none => []) := by
  intro cs o rest h
  simp only [opt] at h
  split at h
  · rename_i a r heq
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hp cs a r heq
  · rename_i heq
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; simp

end YulParser
