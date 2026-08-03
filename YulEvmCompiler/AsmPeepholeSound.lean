import YulEvmCompiler.AsmSem
import YulEvmCompiler.AsmPeephole
set_option warningAsError true
/-!
# YulEvmCompiler.AsmPeepholeSound

Forward simulation for the Asm-level peephole optimizer
(`YulEvmCompiler.AsmPeephole`), against the phase-A step relation
(`YulEvmCompiler.AsmSem`).

`AStep` is parameterized by the *whole* program (jumps resolve labels to
suffixes via `findLabel`), so the soundness statement is a whole-program
forward simulation, not a local equivalence:

* `Match R` — the configuration relation. The rewrites change the
  intermediate code/stack shape mid-window, so `Match` carries three
  "in-flight" constructors besides the synchronized `sync` state: `mid1`/
  `mid2` inside a return-slot window and `brMid` inside an inverted branch
  (source about to take the `jump`; optimized holding the `iszero`d
  condition for its `jumpi`).
* The simulation threads three whole-run invariants: the executing code is a
  suffix of the program (`AStep.suffix`), label definitions are unique
  (`wfCheck`, so a branch-inversion window *knows* `findLabel` lands on its
  own label), and every code address on the stack is a referenced label
  (`StkRefs`, so `dynJump` targets survive dead-label elimination).
* `step_sim` / `steps_sim` / `halt_sim` — every source `AStep`/`AHalt` is
  matched by finitely many optimized steps preserving `Match`. The optimized
  side stutters (on window entry and dropped labels) and catches up within
  the window, so both runs reach the same endpoint.
* `optimizeAsm_asteps` / `optimizeAsm_ahalt` — the packaged bridge lemmas
  consumed by `YulEvmCompiler.Correctness`, which inserts `optimizeAsm`
  between `compileProgram` and `lowerProg`.
-/

namespace YulEvmCompiler.Peephole

open YulSemantics.EVM (U256 EvmState Op b2w)

/-! ### Whole-run invariants -/

/-- Every code address on the stack is a label that may be referenced. This
is what lets `dynJump` survive dead-label elimination: a `.code l` value can
only ever have been pushed by a `pushLabel l` instruction in the program (or
supplied in the initial stack, which the bridges take empty), so `l` is a
referenced label and its definition is never dropped. -/
def StkRefs (R : List Label) (σ : List AVal) : Prop :=
  ∀ l : Label, AVal.code l ∈ σ → l ∈ R

theorem StkRefs.nil {R : List Label} : StkRefs R [] := fun _ h => absurd h (by simp)

/-- Words carry no code addresses. -/
theorem code_not_mem_words {l : Label} {vs : List U256} :
    AVal.code l ∉ words vs := by
  intro h
  simp only [words, List.mem_map] at h
  obtain ⟨v, -, hv⟩ := h
  cases hv

/-- An executed instruction's label reference is a program reference. -/
theorem refs_of_suffix {prog : List Asm} {i : Asm} {c : List Asm}
    (hsuf : (i :: c) <:+ prog) {l : Label} (hi : i.references = some l) :
    l ∈ labelRefs prog := by
  obtain ⟨pre, rfl⟩ := hsuf
  rw [labelRefs_append]
  exact List.mem_append.mpr (Or.inr (mem_labelRefs_cons.mpr (Or.inl hi)))

/-- `AStep` preserves the code-address invariant: ordinary operations move
only words, `dup`/`swap` duplicate/permute existing values, and `pushLabel`
introduces exactly its own (referenced) label. -/
theorem astep_stkRefs [model : ExternalModel] {R : List Label}
    {prog : List Asm} {a b : AConf}
    (hstep : AStep (model := model) prog a b) (hsuf : a.code <:+ prog)
    (hRefs : ∀ l ∈ labelRefs prog, l ∈ R) (hσ : StkRefs R a.stk) :
    StkRefs R b.stk := by
  cases hstep with
  | push =>
      intro l hl
      rcases List.mem_cons.mp hl with h | h
      · cases h
      · exact hσ l h
  | pushImmutable =>
      intro l hl
      rcases List.mem_cons.mp hl with h | h
      · cases h
      · exact hσ l h
  | @op yop args rets c σ yst yst' hb =>
      intro l hl
      rcases List.mem_append.mp hl with h | h
      · exact absurd h code_not_mem_words
      · exact hσ l (List.mem_append.mpr (Or.inr h))
  | @dup n v τ ρ c yst hτ =>
      intro l hl
      rcases List.mem_cons.mp hl with h | h
      · exact hσ l (h ▸ List.mem_append.mpr (Or.inr (List.mem_cons_self)))
      · exact hσ l h
  | @swap n x z τ ρ c yst hτ =>
      intro l hl
      apply hσ
      simp only [List.mem_cons, List.mem_append] at hl ⊢
      tauto
  | pop =>
      intro l hl
      exact hσ l (List.mem_cons_of_mem _ hl)
  | label => exact hσ
  | jump _ => exact hσ
  | jumpiTaken _ _ =>
      intro l hl
      exact hσ l (List.mem_cons_of_mem _ hl)
  | jumpiFall _ =>
      intro l hl
      exact hσ l (List.mem_cons_of_mem _ hl)
  | @pushLabel l0 c σ yst hl0 =>
      intro l hl
      rcases List.mem_cons.mp hl with h | h
      · cases h
        exact hRefs _ (refs_of_suffix hsuf rfl)
      · exact hσ l h
  | dynJump _ =>
      intro l hl
      exact hσ l (List.mem_cons_of_mem _ hl)

/-! ### The configuration relation -/

/-- A configuration correspondence between a source run (in `prog`) and its
optimized run (in `optimizeAsm prog`). `sync` is the aligned state. `mid1`
(source has done the window's `push`, optimized has done nothing) and `mid2`
(source has done `push; swap1`, optimized has done `pop`) capture the two
in-flight states of a return-slot window. `brMid` captures the in-flight
state of an inverted branch: the source is about to take the `jump m` while
the optimized side holds the (nonzero) `iszero`d condition for its
`jumpi m`. -/
inductive Match (R : List Label) : AConf → AConf → Prop
  | sync {sc oc : List Asm} {σ : List AVal} {y : EvmState} :
      CodeRel R sc oc → Match R ⟨sc, σ, y⟩ ⟨oc, σ, y⟩
  | mid1 {v : U256} {n : Fin 16} (hn : n.val = 0) {S : List AVal}
      {sc oc : List Asm} {y : EvmState} :
      CodeRel R sc oc →
      Match R ⟨.swap n :: .pop :: sc, .word v :: S, y⟩
              ⟨.pop :: .push v :: oc, S, y⟩
  | mid2 {v : U256} {x : AVal} {ρ : List AVal} {sc oc : List Asm} {y : EvmState} :
      CodeRel R sc oc →
      Match R ⟨.pop :: sc, x :: .word v :: ρ, y⟩ ⟨.push v :: oc, ρ, y⟩
  | brMid {l m : Label} {w : U256} (hw : w ≠ 0) {σ : List AVal}
      {sc oc : List Asm} {y : EvmState} :
      CodeRel R sc oc →
      Match R ⟨.jump m :: .label l :: sc, σ, y⟩
              ⟨.jumpi m :: .label l :: oc, .word w :: σ, y⟩
  | dz1 {l : Label} {v : U256} {σ : List AVal} {sc oc : List Asm} {y : EvmState} :
      CodeRel R sc oc →
      Match R ⟨.op .iszero :: .jumpi l :: sc, .word (b2w (v = 0)) :: σ, y⟩
              ⟨.jumpi l :: oc, .word v :: σ, y⟩
  | dz2 {l : Label} {v : U256} {σ : List AVal} {sc oc : List Asm} {y : EvmState} :
      CodeRel R sc oc →
      Match R ⟨.jumpi l :: sc, .word (b2w (b2w (v = 0) = 0)) :: σ, y⟩
              ⟨.jumpi l :: oc, .word v :: σ, y⟩

/-- The `iszero` step the optimized side of an inverted branch executes. -/
theorem iszero_step [model : ExternalModel] {prog' c : List Asm}
    {v : U256} {σ : List AVal} {y : EvmState} :
    AStep (model := model) prog' ⟨.op .iszero :: c, .word v :: σ, y⟩
      ⟨c, .word (b2w (v = 0)) :: σ, y⟩ := by
  have h := AStep.op (model := model) (prog := prog') (yop := .iszero)
    (args := [v]) (rets := [b2w (v = 0)]) (c := c) (σ := σ) (yst := y) (yst' := y) rfl
  simpa [words] using h

/-- Invert a successful `iszero` built-in step: one argument, the `b2w`
result, unchanged state. -/
theorem iszero_inv [model : ExternalModel] {args rets : List U256}
    {yst yst' : EvmState}
    (hb : YulSemantics.EVM.builtinWithExternal model.calls model.creates
      .iszero args yst (.ok rets yst')) :
    ∃ v, args = [v] ∧ rets = [b2w (v = 0)] ∧ yst' = yst := by
  match args with
  | [v] =>
      obtain ⟨rfl, rfl⟩ :
          [b2w (v = 0)] = rets ∧ yst = yst' := by
        have h := Option.some.inj hb
        cases h
        exact ⟨rfl, rfl⟩
      exact ⟨v, rfl, rfl, rfl⟩
  | [] => exact absurd hb (by simp [YulSemantics.EVM.builtinWithExternal,
      YulSemantics.EVM.stepOp, YulSemantics.EVM.un])
  | _ :: _ :: _ => exact absurd hb (by simp [YulSemantics.EVM.builtinWithExternal,
      YulSemantics.EVM.stepOp, YulSemantics.EVM.un])

/-- `iszero` never halts. -/
theorem iszero_no_halt [model : ExternalModel] {args : List U256}
    {yst yf : EvmState}
    (hb : YulSemantics.EVM.builtinWithExternal model.calls model.creates
      .iszero args yst (.halt yf)) : False := by
  match args with
  | [] => exact absurd hb (by simp [YulSemantics.EVM.builtinWithExternal,
      YulSemantics.EVM.stepOp, YulSemantics.EVM.un])
  | [v] => exact absurd hb (by simp [YulSemantics.EVM.builtinWithExternal,
      YulSemantics.EVM.stepOp, YulSemantics.EVM.un])
  | _ :: _ :: _ => exact absurd hb (by simp [YulSemantics.EVM.builtinWithExternal,
      YulSemantics.EVM.stepOp, YulSemantics.EVM.un])

/-- Double `iszero` preserves truthiness: the normalized value is zero
exactly when the original is. -/
theorem b2w_dbl_eq_zero_iff {v : U256} : b2w (b2w (v = 0) = 0) = 0 ↔ v = 0 := by
  by_cases hv : v = 0 <;> simp [b2w, hv]

/-- Invert a step from a configuration headed by an operation (the stack need
not be in `words args ++ σ` form syntactically). -/
theorem astep_op_inv [model : ExternalModel] {prog : List Asm} {yop : Op}
    {c : List Asm} {σs : List AVal} {y : EvmState} {b : AConf}
    (h : AStep (model := model) prog ⟨.op yop :: c, σs, y⟩ b) :
    ∃ args rets σ' yst', σs = words args ++ σ'
      ∧ YulSemantics.EVM.builtinWithExternal model.calls model.creates yop args y
          (.ok rets yst')
      ∧ b = ⟨c, words rets ++ σ', yst'⟩ := by
  cases h with
  | op hb => exact ⟨_, _, _, _, rfl, hb, rfl⟩

/-- Invert a halt from a configuration headed by an operation. -/
theorem ahalt_op_inv [model : ExternalModel] {prog : List Asm} {yop : Op}
    {c : List Asm} {σs : List AVal} {y yf : EvmState}
    (h : AHalt (model := model) prog ⟨.op yop :: c, σs, y⟩ yf) :
    ∃ args σ', σs = words args ++ σ'
      ∧ YulSemantics.EVM.builtinWithExternal model.calls model.creates yop args y
          (.halt yf) := by
  cases h with
  | op hb => exact ⟨_, _, rfl, hb⟩

/-! ### The forward simulation -/

/-- Single-step forward simulation: one source `AStep` is simulated by finitely
many optimized steps preserving `Match`. -/
theorem step_sim [model : ExternalModel] {R : List Label} {prog prog' : List Asm}
    (hnodup : (labelDefs prog).Nodup) (hRefs : ∀ l ∈ labelRefs prog, l ∈ R)
    (hpp : CodeRel R prog prog') {a b a' : AConf}
    (hstep : AStep (model := model) prog a b) (hsuf : a.code <:+ prog)
    (hσ : StkRefs R a.stk) (hm : Match R a a') :
    ∃ b', ASteps (model := model) prog' a' b' ∧ Match R b b' := by
  cases hm with
  | @sync sc oc σ y hc =>
    cases hstep with
    | @push v c σ2 yst =>
      cases hc with
      | keep _ hc' => exact ⟨_, .single .push, .sync hc'⟩
      | window hn hc' => exact ⟨_, .refl _, .mid1 hn hc'⟩
    | @pushImmutable key v c σ2 yst =>
      -- No peephole window ever opens on an immutable placeholder, so the pass
      -- can only `keep` it — which is exactly what must happen: folding one
      -- would move the 32 bytes the constructor patches.
      cases hc with
      | keep _ hc' => exact ⟨_, .single .pushImmutable, .sync hc'⟩
    | @op yop args rets c σ2 yst yst' hb =>
      cases hc with
      | keep _ hc' => exact ⟨_, .single (.op hb), .sync hc'⟩
      | dblIszero hc' =>
        -- first `iszero` of a doomed pair: the optimized side stutters
        obtain ⟨v, rfl, rfl, rfl⟩ := iszero_inv hb
        exact ⟨_, .refl _, .dz1 hc'⟩
    | @dup n v τ ρ c yst hτ =>
      cases hc with
      | keep _ hc' => exact ⟨_, .single (.dup hτ), .sync hc'⟩
    | @swap n aa bb τ ρ c yst hτ =>
      cases hc with
      | keep _ hc' => exact ⟨_, .single (.swap hτ), .sync hc'⟩
    | @pop v c σ2 yst =>
      cases hc with
      | keep _ hc' => exact ⟨_, .single .pop, .sync hc'⟩
    | @label l c σ2 yst =>
      cases hc with
      | keep _ hc' => exact ⟨_, .single .label, .sync hc'⟩
      | dropLabel _ hc' => exact ⟨_, .refl _, .sync hc'⟩
    | @jump l c c'0 σ2 yst hf =>
      cases hc with
      | keep _ hc' =>
        have hR : l ∈ R := hRefs l (refs_of_suffix hsuf rfl)
        obtain ⟨otgt, ho, hr⟩ := codeRel_findLabel hpp hR hf
        exact ⟨_, .single (.jump ho), .sync hr⟩
      | @jumpNext _ ctail oc' hc' =>
        -- the jump's own label is next; source lands exactly there
        obtain ⟨pre0, hpre⟩ := hsuf
        have heq : prog = (pre0 ++ [Asm.jump l]) ++ Asm.label l :: ctail := by
          rw [← hpre]; simp
        have hfl : findLabel l prog = some ctail := by
          rw [heq]; exact findLabel_boundary (by rw [← heq]; exact hnodup)
        obtain rfl : c'0 = ctail := by
          rw [hf] at hfl; exact Option.some.inj hfl
        exact ⟨_, .single .label, .sync hc'⟩
    | @jumpiTaken l v c c'0 σ2 yst hv hf =>
      cases hc with
      | keep _ hc' =>
        have hR : l ∈ R := hRefs l (refs_of_suffix hsuf rfl)
        obtain ⟨otgt, ho, hr⟩ := codeRel_findLabel hpp hR hf
        exact ⟨_, .single (.jumpiTaken hv ho), .sync hr⟩
      | @brInv _ m ctail oc' hc' =>
        -- the window's own label is the unique definition of `l`, so the
        -- source lands exactly at the window's continuation
        obtain ⟨pre0, hpre⟩ := hsuf
        have heq : prog = (pre0 ++ [Asm.jumpi l, Asm.jump m]) ++ Asm.label l :: ctail := by
          rw [← hpre]; simp
        have hfl : findLabel l prog = some ctail := by
          rw [heq]; exact findLabel_boundary (by rw [← heq]; exact hnodup)
        obtain rfl : c'0 = ctail := by
          rw [hf] at hfl; exact Option.some.inj hfl
        -- optimized: iszero (→ 0), fall through the jumpi, step the label
        refine ⟨_, ?_, .sync hc'⟩
        refine .head iszero_step (.head (.jumpiFall (by simp [b2w]; exact hv)) ?_)
        exact .single .label
      | @jumpiNext _ ctail oc' hc' =>
        -- the jumpi's own label is next; taken lands exactly there
        obtain ⟨pre0, hpre⟩ := hsuf
        have heq : prog = (pre0 ++ [Asm.jumpi l]) ++ Asm.label l :: ctail := by
          rw [← hpre]; simp
        have hfl : findLabel l prog = some ctail := by
          rw [heq]; exact findLabel_boundary (by rw [← heq]; exact hnodup)
        obtain rfl : c'0 = ctail := by
          rw [hf] at hfl; exact Option.some.inj hfl
        exact ⟨_, .head .pop (.single .label), .sync hc'⟩
    | @jumpiFall l v c σ2 yst hv =>
      cases hc with
      | keep _ hc' => exact ⟨_, .single (.jumpiFall hv), .sync hc'⟩
      | @brInv _ m _ oc' hc' =>
        -- optimized: iszero (→ 1); hold it for the inverted jumpi
        subst hv
        refine ⟨_, .single iszero_step, Match.brMid ?_ hc'⟩
        simp [b2w]
      | @jumpiNext _ ctail oc' hc' =>
        -- not taken: fall into the label; optimized just pops the condition
        exact ⟨_, .single .pop, .sync (CodeRel.keep _ hc')⟩
    | @pushLabel l c σ2 yst hl =>
      cases hc with
      | keep _ hc' =>
        have hR : l ∈ R := hRefs l (refs_of_suffix hsuf rfl)
        exact ⟨_, .single (.pushLabel (codeRel_labelDefs_mem hpp hR hl)), .sync hc'⟩
    | @dynJump l c c'0 σ2 yst hf =>
      cases hc with
      | keep _ hc' =>
        have hR : l ∈ R := hσ l List.mem_cons_self
        obtain ⟨otgt, ho, hr⟩ := codeRel_findLabel hpp hR hf
        exact ⟨_, .single (.dynJump ho), .sync hr⟩
  | @mid1 v n hn S sc oc y hc =>
    cases hstep with
    | @swap n2 aa bb τ ρ c yst hτ =>
      -- code head is `swap n`; τ.length = n.val = 0 ⇒ τ = []
      obtain rfl : τ = [] := List.length_eq_zero_iff.mp (hτ.trans hn)
      -- opt does one `pop`, landing in the `mid2` state
      exact ⟨_, .single .pop, .mid2 hc⟩
  | @mid2 v x ρ sc oc y hc =>
    cases hstep with
    | @pop v2 c σ2 yst =>
      exact ⟨_, .single .push, .sync hc⟩
  | @brMid l m w hw σ sc oc y hc =>
    cases hstep with
    | jump hf =>
      have hR : m ∈ R := hRefs m (refs_of_suffix hsuf rfl)
      obtain ⟨otgt, ho, hr⟩ := codeRel_findLabel hpp hR hf
      exact ⟨_, .single (.jumpiTaken hw ho), .sync hr⟩
  | @dz1 l v σ sc oc y hc =>
    -- second `iszero` of the pair; the optimized side still stutters
    obtain ⟨args, rets, σ', yst', hσeq, hb, rfl⟩ := astep_op_inv hstep
    obtain ⟨u, rfl, rfl, rfl⟩ := iszero_inv hb
    obtain ⟨rfl, rfl⟩ : b2w (v = 0) = u ∧ σ = σ' := by
      simpa [words] using hσeq
    exact ⟨_, .refl _, .dz2 hc⟩
  | @dz2 l v σ sc oc y hc =>
    cases hstep with
    | @jumpiTaken _ _ c c'0 σ2 yst hv hf =>
      have hvne : v ≠ 0 := fun h => hv (b2w_dbl_eq_zero_iff.mpr h)
      have hR : l ∈ R := hRefs l (refs_of_suffix hsuf rfl)
      obtain ⟨otgt, ho, hr⟩ := codeRel_findLabel hpp hR hf
      exact ⟨_, .single (.jumpiTaken hvne ho), .sync hr⟩
    | @jumpiFall _ _ c σ2 yst hv =>
      have hv0 : v = 0 := b2w_dbl_eq_zero_iff.mp hv
      exact ⟨_, .single (.jumpiFall hv0), .sync hc⟩

/-- Multi-step forward simulation (reflexive-transitive closure), threading
the suffix and stack invariants along the source run. -/
theorem steps_sim [model : ExternalModel] {R : List Label} {prog prog' : List Asm}
    (hnodup : (labelDefs prog).Nodup) (hRefs : ∀ l ∈ labelRefs prog, l ∈ R)
    (hpp : CodeRel R prog prog') {a b a' : AConf}
    (hsteps : ASteps (model := model) prog a b) (hsuf : a.code <:+ prog)
    (hσ : StkRefs R a.stk) (hm : Match R a a') :
    ∃ b', ASteps (model := model) prog' a' b' ∧ Match R b b' := by
  induction hsteps generalizing a' with
  | refl a => exact ⟨a', .refl _, hm⟩
  | @head a c b hstep hrest ih =>
    obtain ⟨c', hc', hmc⟩ := step_sim hnodup hRefs hpp hstep hsuf hσ hm
    obtain ⟨b', hb', hmb⟩ :=
      ih (hstep.suffix hsuf) (astep_stkRefs hstep hsuf hRefs hσ) hmc
    exact ⟨b', hc'.trans hb', hmb⟩

/-- Halting-step simulation. -/
theorem halt_sim [model : ExternalModel] {R : List Label} {prog prog' : List Asm}
    {b a' : AConf} {yf : EvmState}
    (hhalt : AHalt (model := model) prog b yf) (hm : Match R b a') :
    AHalt (model := model) prog' a' yf := by
  cases hm with
  | @sync sc oc σ2 y hc =>
    cases hhalt with
    | @op yop args c σ yst yst' hb =>
      cases hc with
      | keep _ hc' => exact .op hb
      | dblIszero _ => exact absurd hb iszero_no_halt
  | dz1 hc =>
    obtain ⟨args, σ', -, hb⟩ := ahalt_op_inv hhalt
    exact absurd hb iszero_no_halt
  | mid1 _ _ => exact absurd hhalt (by intro h; cases h)
  | mid2 _ => exact absurd hhalt (by intro h; cases h)
  | brMid _ _ => exact absurd hhalt (by intro h; cases h)
  | dz2 _ => exact absurd hhalt (by intro h; cases h)

/-! ### Endpoint inversion and the packaged bridge lemmas -/

/-- With empty source code, `Match` forces the optimized configuration to be
identical (same empty code, stack, and state). -/
theorem match_empty_left {R : List Label} {σ : List AVal} {y : EvmState}
    {a' : AConf} (hm : Match R ⟨[], σ, y⟩ a') :
    a' = ⟨[], σ, y⟩ := by
  cases hm with
  | sync hc => rw [codeRel_nil_left hc]

/-- **Round bridge (normal case).** A full source run from the whole program
(with an empty initial stack, unique label definitions) to empty code is
simulated by one optimization round to the same endpoint. -/
theorem optimizeAsmRound_asteps [model : ExternalModel] {asm : List Asm}
    (hnodup : (labelDefs asm).Nodup) {σf : List AVal} {y yf : EvmState}
    (hsteps : ASteps (model := model) asm ⟨asm, [], y⟩ ⟨[], σf, yf⟩) :
    ASteps (model := model) (optimizeAsmRound asm)
      ⟨optimizeAsmRound asm, [], y⟩ ⟨[], σf, yf⟩ := by
  have hcr := codeRel_optimizeRound asm
  obtain ⟨b', hb', hmb⟩ := steps_sim hnodup (fun _ h => h) hcr hsteps
    (List.suffix_refl asm) StkRefs.nil (.sync hcr)
  rw [match_empty_left hmb] at hb'
  exact hb'

/-- **Round bridge (halt case).** -/
theorem optimizeAsmRound_ahalt [model : ExternalModel] {asm : List Asm}
    (hnodup : (labelDefs asm).Nodup) {y : EvmState} {bconf : AConf} {yf : EvmState}
    (hsteps : ASteps (model := model) asm ⟨asm, [], y⟩ bconf)
    (hhalt : AHalt (model := model) asm bconf yf) :
    ∃ b', ASteps (model := model) (optimizeAsmRound asm)
        ⟨optimizeAsmRound asm, [], y⟩ b'
      ∧ AHalt (model := model) (optimizeAsmRound asm) b' yf := by
  have hcr := codeRel_optimizeRound asm
  obtain ⟨b', hb', hmb⟩ := steps_sim hnodup (fun _ h => h) hcr hsteps
    (List.suffix_refl asm) StkRefs.nil (.sync hcr)
  exact ⟨b', hb', halt_sim hhalt hmb⟩

/-- One round keeps label definitions unique, so the next round's bridge
applies. -/
theorem optimizeAsmRound_nodup {asm : List Asm}
    (hnodup : (labelDefs asm).Nodup) :
    (labelDefs (optimizeAsmRound asm)).Nodup :=
  hnodup.sublist (codeRel_labelDefs_sublist (codeRel_optimizeRound asm))

/-- **Bridge (normal case).** Round bridges compose along the bounded
iteration: a full source run is simulated by `optimizeAsm` (any number of
rounds) to the same endpoint. -/
theorem optimizeAsmN_asteps [model : ExternalModel] (k : Nat) {asm : List Asm}
    (hnodup : (labelDefs asm).Nodup) {σf : List AVal} {y yf : EvmState}
    (hsteps : ASteps (model := model) asm ⟨asm, [], y⟩ ⟨[], σf, yf⟩) :
    ASteps (model := model) (optimizeAsmN k asm)
      ⟨optimizeAsmN k asm, [], y⟩ ⟨[], σf, yf⟩ := by
  induction k generalizing asm with
  | zero => exact hsteps
  | succ k ih =>
    rw [optimizeAsmN]
    split
    · exact hsteps
    · exact ih (optimizeAsmRound_nodup hnodup) (optimizeAsmRound_asteps hnodup hsteps)

/-- **Bridge (halt case).** -/
theorem optimizeAsmN_ahalt [model : ExternalModel] (k : Nat) {asm : List Asm}
    (hnodup : (labelDefs asm).Nodup) {y : EvmState} {bconf : AConf} {yf : EvmState}
    (hsteps : ASteps (model := model) asm ⟨asm, [], y⟩ bconf)
    (hhalt : AHalt (model := model) asm bconf yf) :
    ∃ b', ASteps (model := model) (optimizeAsmN k asm)
        ⟨optimizeAsmN k asm, [], y⟩ b'
      ∧ AHalt (model := model) (optimizeAsmN k asm) b' yf := by
  induction k generalizing asm bconf with
  | zero => exact ⟨bconf, hsteps, hhalt⟩
  | succ k ih =>
    rw [optimizeAsmN]
    split
    · exact ⟨bconf, hsteps, hhalt⟩
    · obtain ⟨b1, hb1, hh1⟩ := optimizeAsmRound_ahalt hnodup hsteps hhalt
      exact ih (optimizeAsmRound_nodup hnodup) hb1 hh1

/-- The packaged bridges for `optimizeAsm` (the production four-round pass),
consumed by `YulEvmCompiler.Correctness`. -/
theorem optimizeAsm_asteps [model : ExternalModel] {asm : List Asm}
    (hnodup : (labelDefs asm).Nodup) {σf : List AVal} {y yf : EvmState}
    (hsteps : ASteps (model := model) asm ⟨asm, [], y⟩ ⟨[], σf, yf⟩) :
    ASteps (model := model) (optimizeAsm asm) ⟨optimizeAsm asm, [], y⟩ ⟨[], σf, yf⟩ :=
  optimizeAsmN_asteps 4 hnodup hsteps

theorem optimizeAsm_ahalt [model : ExternalModel] {asm : List Asm}
    (hnodup : (labelDefs asm).Nodup) {y : EvmState} {bconf : AConf} {yf : EvmState}
    (hsteps : ASteps (model := model) asm ⟨asm, [], y⟩ bconf)
    (hhalt : AHalt (model := model) asm bconf yf) :
    ∃ b', ASteps (model := model) (optimizeAsm asm) ⟨optimizeAsm asm, [], y⟩ b'
      ∧ AHalt (model := model) (optimizeAsm asm) b' yf :=
  optimizeAsmN_ahalt 4 hnodup hsteps hhalt

end YulEvmCompiler.Peephole
