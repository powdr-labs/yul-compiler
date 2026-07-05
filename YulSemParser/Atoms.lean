import YulSemParser.SoundC

/-!
# YulSemParser.Atoms

Atomic parsers producing `yul-semantics` values (`Literal`, identifiers as
`String`), plus keyword/punctuation tokens and the discarded type annotation.
Each atom prints its token followed by a delimiting space (so the printed form
is `Closed`), and is proven `SoundC`.
-/

namespace YulSemParser

open YulParser (Parser token pWhile1 pstr isWs isIdStart isIdCont isDigitC pchar pWhile0 keyword)

/-! ### Maximal-munch helper -/

/-- The head of a `dropWhile` fails the predicate, so a further `takeWhile` is empty. -/
theorem takeWhile_dropWhile_nil {α} (p : α → Bool) (l : List α) :
    (l.dropWhile p).takeWhile p = [] := by
  induction l with
  | nil => simp
  | cons a as ih =>
    rw [List.dropWhile_cons]
    split
    · exact ih
    · rename_i hpa; simp [List.takeWhile_cons, hpa]

/-! ### Identifiers -/

/-- Raw identifier characters (whitespace-skipping). -/
def pIdentChars : Parser (List Char) := token (pWhile1 isIdStart isIdCont)

theorem pIdentChars_soundC : SoundC pIdentChars (fun d => d ++ [' ']) := by
  intro cs d rest h
  simp only [pIdentChars, token] at h
  set cs' := cs.dropWhile isWs with hcs'
  cases hc : cs' with
  | nil => rw [hc] at h; simp [pWhile1] at h
  | cons c r =>
    rw [hc] at h
    simp only [pWhile1] at h
    split at h
    · rename_i hfirst
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      set ts := r.takeWhile isIdCont with hts
      have htsAll : ∀ x ∈ ts, isIdCont x = true := fun x hx => List.mem_takeWhile_imp hx
      refine ⟨?_, closed_ident hfirst htsAll⟩
      -- canon of the printed token is a single ident
      have tokEq : canon (c :: ts ++ [' ']) = [CTok.ident (c :: ts)] := by
        have e : c :: ts ++ [' '] = c :: (ts ++ ' ' :: ([] : List Char)) := by simp
        rw [e, canon_ident (idStart_not_ws hfirst) (idStart_not_quote hfirst) hfirst,
          takeWhile_append_all htsAll, dropWhile_append_all htsAll]
        simp only [List.takeWhile_cons, List.dropWhile_cons, (by decide : isIdCont ' ' = false),
          Bool.false_eq_true, if_false, List.append_nil]
        rw [canon_ws (by decide : isWs ' ' = true), canon_nil]
      -- canon cs splits as that ident followed by the remainder
      have hcanon_cs : canon cs = CTok.ident (c :: ts) :: canon (r.dropWhile isIdCont) := by
        rw [← canon_dropWhile_ws cs, ← hcs', hc,
          canon_ident (idStart_not_ws hfirst) (idStart_not_quote hfirst) hfirst]
      rw [hcanon_cs, tokEq, List.singleton_append]
    · exact absurd h (by simp)

/-- An identifier as a `String` (the `yul-semantics` `Ident` type). -/
def pIdent : Parser String := YulParser.pmap String.ofList pIdentChars

theorem pIdent_soundC : SoundC pIdent (fun s => s.toList ++ [' ']) := by
  apply pmapC_eq pIdentChars_soundC
  intro d; rw [String.toList_ofList]

end YulSemParser
