import YulEvmCompiler.SsaCfg.Implementation.PassesSound.InlineBounds
set_option warningAsError true

/-!
# YulEvmCompiler.SsaCfg.Implementation.PassesSound.Inline

Inlining: splice inversion, well-formedness, soundness, and pruning.

`inlineOnce` as a pure fold with its inversion lemma and `allDefs`
permutation, the block-level well-formedness predicate `BlockWF` through
`inlineOnce_wf`, the caller-side replay `inlineCaller_execN` through
`inlineOnce_soundN`, the iteration `inlineN`/`inlineFunc`/`inlineMap`, pure
models of the mutable pruning loops with their reachability invariants
(`pruneFuncs_sound`), and finally `inlineProg_sound`.
-/

namespace YulEvmCompiler.SsaCfg
open YulSemantics.EVM (U256 EvmState Op builtinWithExternal stepOp ExternalCalls
  ExternalCreates)
open YulSemantics (Outcome)

/-! ### Inverting one inlining splice

`inlineOnce` is a pair of nested early-return loops.  As with
`findTrivialParam`, exposing a pure `loopWith` model keeps the inversion local:
the successful result must have been produced by one concrete instruction
step, and unfolding that step gives the complete splice equation. -/

namespace Passes

abbrev InlineState := MProd (Option (Option Func)) PUnit

theorem loopWith_inline_done {α : Type} {g : α → InlineState →
    ForInStep InlineState} {xs : List α} {f : Func}
    (hg : ∀ a, g a ⟨none, PUnit.unit⟩ = .yield ⟨none, PUnit.unit⟩ ∨
      ∃ f, g a ⟨none, PUnit.unit⟩ = .done ⟨some (some f), PUnit.unit⟩)
    (h : (loopWith g xs ⟨none, PUnit.unit⟩).1 = some (some f)) :
    ∃ a ∈ xs, g a ⟨none, PUnit.unit⟩ =
      .done ⟨some (some f), PUnit.unit⟩ := by
  induction xs with
  | nil => simp [loopWith] at h
  | cons a as ih =>
      rw [loopWith_cons] at h
      rcases hg a with ha | ⟨f', ha⟩
      · rw [ha] at h
        obtain ⟨b, hb, hdone⟩ := ih h
        exact ⟨b, by simp [hb], hdone⟩
      · rw [ha] at h
        have hf : f' = f := by simpa using h
        subst f'
        exact ⟨a, by simp, ha⟩

theorem loopWith_inline_cases {α : Type} {g : α → InlineState →
    ForInStep InlineState} {xs : List α}
    (hg : ∀ a, g a ⟨none, PUnit.unit⟩ = .yield ⟨none, PUnit.unit⟩ ∨
      ∃ f, g a ⟨none, PUnit.unit⟩ = .done ⟨some (some f), PUnit.unit⟩) :
    (loopWith g xs ⟨none, PUnit.unit⟩).1 = none ∨
      ∃ f, (loopWith g xs ⟨none, PUnit.unit⟩).1 = some (some f) := by
  induction xs with
  | nil => exact Or.inl rfl
  | cons a as ih =>
      rw [loopWith_cons]
      rcases hg a with ha | ⟨f, ha⟩
      · rw [ha]
        exact ih
      · rw [ha]
        exact Or.inr ⟨f, rfl⟩

def inlineInstrStep (counts : Array Nat) (funcs : Array Func) (f : Func)
    (bi ci : Nat) (_ : InlineState) : ForInStep InlineState :=
  let b := f.blocks[bi]!
  match b.instrs[ci]! with
  | .call ds fid as =>
      match funcs[fid]? with
      | some g =>
          if inlinable (counts[fid]?.getD 0) g && g.params.length == as.length
              && g.nrets == ds.length && g.entry == 0 then
            let off := Nat.max (maxVal f) (maxVal g) + 1
            let paramMap := g.params.zip as
            let ρ := fun v =>
              match paramMap.find? (·.1 == v) with
              | some pa => pa.2
              | none => v + off
            let nCaller := f.blocks.size
            let contId := nCaller + g.blocks.size
            let β := fun (b : BlockId) => nCaller + b
            let spliced := g.blocks.map fun gb =>
              { params := gb.params.map ρ
                instrs := gb.instrs.map (renameInstr ρ)
                term :=
                  match gb.term with
                  | .ret vs => .jump ⟨contId, vs.map ρ⟩
                  | t => renameTerm ρ β t }
            let contBlock : Block :=
              { params := ds
                instrs := b.instrs.drop (ci + 1)
                term := b.term }
            let callBlock : Block :=
              { params := b.params
                instrs := b.instrs.take ci
                term := .jump ⟨nCaller + g.entry, []⟩ }
            let blocks := (f.blocks.set! bi callBlock) ++ spliced ++ #[contBlock]
            .done ⟨some (some { f with blocks }), PUnit.unit⟩
          else .yield ⟨none, PUnit.unit⟩
      | none => .yield ⟨none, PUnit.unit⟩
  | _ => .yield ⟨none, PUnit.unit⟩

def inlineBlockStep (counts : Array Nat) (funcs : Array Func) (f : Func)
    (bi : Nat) (_ : InlineState) : ForInStep InlineState :=
  let b := f.blocks[bi]!
  let r := loopWith (inlineInstrStep counts funcs f bi)
    (List.range' 0 b.instrs.length 1) ⟨none, PUnit.unit⟩
  match r.1 with
  | none => .yield ⟨none, PUnit.unit⟩
  | some a => .done ⟨some a, PUnit.unit⟩

theorem inlineOnce_eq_loop (counts : Array Nat) (funcs : Array Func) (f : Func) :
    inlineOnce counts funcs f =
      (loopWith (inlineBlockStep counts funcs f)
        (List.range' 0 f.blocks.size 1) ⟨none, PUnit.unit⟩).1.getD none := by
  unfold inlineOnce
  dsimp only
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rw [Id.forIn_eq_loopWith (g := inlineBlockStep counts funcs f) (h := by
    intro bi r
    unfold inlineBlockStep
    rw [Id.forIn_eq_loopWith (g := inlineInstrStep counts funcs f bi) (h := by
      intro ci s
      simp only [LawfulMonad.pure_bind]
      cases hi : f.blocks[bi]!.instrs[ci]! with
      | const d v => simp [inlineInstrStep, hi]
      | op ds yop as => simp [inlineInstrStep, hi]
      | call ds fid as =>
          cases hg : funcs[fid]? with
          | none => simp [inlineInstrStep, hi, hg]
          | some g =>
              by_cases hc : inlinable (counts[fid]?.getD 0) g &&
                  g.params.length == as.length && g.nrets == ds.length && g.entry == 0
              · simp [inlineInstrStep, hi, hg, hc]
                rfl
              · simp [inlineInstrStep, hi, hg, hc])]
    simp_all [bind, pure]
    split <;> simp_all)]
  simp [Id.run, bind, pure, Option.getD]
  split <;> simp_all

theorem inlineInstrStep_cases (counts : Array Nat) (funcs : Array Func)
    (f : Func) (bi ci : Nat) :
    inlineInstrStep counts funcs f bi ci ⟨none, PUnit.unit⟩ =
        .yield ⟨none, PUnit.unit⟩ ∨
      ∃ f', inlineInstrStep counts funcs f bi ci ⟨none, PUnit.unit⟩ =
        .done ⟨some (some f'), PUnit.unit⟩ := by
  unfold inlineInstrStep
  dsimp only
  split <;> try { exact Or.inl rfl }
  split <;> try { exact Or.inl rfl }
  split
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inl rfl

theorem inlineBlockStep_cases (counts : Array Nat) (funcs : Array Func)
    (f : Func) (bi : Nat) :
    inlineBlockStep counts funcs f bi ⟨none, PUnit.unit⟩ =
        .yield ⟨none, PUnit.unit⟩ ∨
      ∃ f', inlineBlockStep counts funcs f bi ⟨none, PUnit.unit⟩ =
        .done ⟨some (some f'), PUnit.unit⟩ := by
  unfold inlineBlockStep
  dsimp only
  rcases loopWith_inline_cases
      (fun ci => inlineInstrStep_cases counts funcs f bi ci)
      (xs := List.range' 0 f.blocks[bi]!.instrs.length 1) with hr | ⟨f', hr⟩
  · left
    simp [hr]
  · right
    exact ⟨f', by simp [hr]⟩

/-- Successful `inlineOnce` inversion.  The final equality is the five-part
splice definition (renaming, copied blocks, continuation, split call block,
and concatenated block array) in a form callers can unfold selectively. -/
theorem inlineOnce_inv {counts : Array Nat} {funcs : Array Func} {f f' : Func}
    (h : inlineOnce counts funcs f = some f') :
    ∃ bi b ci ds fid as g,
      bi < f.blocks.size ∧ f.blocks[bi]? = some b ∧
      ci < b.instrs.length ∧ b.instrs[ci]? = some (.call ds fid as) ∧
      funcs[fid]? = some g ∧
      inlinable (counts[fid]?.getD 0) g = true ∧
      g.params.length = as.length ∧ g.nrets = ds.length ∧ g.entry = 0 ∧
      f' =
        let off := Nat.max (maxVal f) (maxVal g) + 1
        let paramMap := g.params.zip as
        let ρ := fun v =>
          match paramMap.find? (·.1 == v) with
          | some pa => pa.2
          | none => v + off
        let nCaller := f.blocks.size
        let contId := nCaller + g.blocks.size
        let β := fun (b : BlockId) => nCaller + b
        let spliced := g.blocks.map fun gb =>
          { params := gb.params.map ρ
            instrs := gb.instrs.map (renameInstr ρ)
            term := match gb.term with
              | .ret vs => .jump ⟨contId, vs.map ρ⟩
              | t => renameTerm ρ β t }
        let contBlock : Block :=
          { params := ds, instrs := b.instrs.drop (ci + 1), term := b.term }
        let callBlock : Block :=
          { params := b.params, instrs := b.instrs.take ci,
            term := .jump ⟨nCaller + g.entry, []⟩ }
        { f with blocks := (f.blocks.set! bi callBlock) ++ spliced ++ #[contBlock] } := by
  rw [inlineOnce_eq_loop] at h
  have hout :
      (loopWith (inlineBlockStep counts funcs f)
        (List.range' 0 f.blocks.size 1) ⟨none, PUnit.unit⟩).1 =
        some (some f') := by
    cases hr : (loopWith (inlineBlockStep counts funcs f)
        (List.range' 0 f.blocks.size 1) ⟨none, PUnit.unit⟩).1 with
    | none => simp [hr, Option.getD] at h
    | some r =>
        cases r with
        | none => simp [hr, Option.getD] at h
        | some q =>
            have hq : q = f' := by simpa [hr, Option.getD] using h
            simp [hq]
  obtain ⟨bi, hbimem, hbistep⟩ := loopWith_inline_done
    (fun j => inlineBlockStep_cases counts funcs f j) hout
  unfold inlineBlockStep at hbistep
  dsimp only at hbistep
  split at hbistep
  · cases hbistep
  · rename_i r hr
    have hr' : r = some f' := by simpa using hbistep
    rw [hr'] at hr
    obtain ⟨ci, hcimem, hcistep⟩ := loopWith_inline_done
      (fun j => inlineInstrStep_cases counts funcs f bi j) hr
    unfold inlineInstrStep at hcistep
    dsimp only at hcistep
    split at hcistep <;> try { cases hcistep }
    rename_i ds fid as hcall
    split at hcistep <;> try { cases hcistep }
    rename_i g hg
    split at hcistep <;> try { cases hcistep }
    rename_i hguard
    have hbi : bi < f.blocks.size := by simpa using hbimem
    have hci : ci < f.blocks[bi]!.instrs.length := by simpa using hcimem
    have hbget : f.blocks[bi]? = some f.blocks[bi]! := by
      rw [Array.getElem?_eq_getElem hbi, getElem!_eq_getElem hbi]
    have hparts : inlinable (counts[fid]?.getD 0) g = true ∧
        g.params.length = as.length ∧ g.nrets = ds.length ∧ g.entry = 0 := by
      have hpraw := (by simpa only [Bool.and_eq_true, beq_iff_eq] using hguard)
      exact ⟨hpraw.1.1.1, hpraw.1.1.2, hpraw.1.2, hpraw.2⟩
    refine ⟨bi, f.blocks[bi]!, ci, ds, fid, as, g, hbi, hbget, hci, ?_, hg,
      ?_, ?_, ?_, ?_, ?_⟩
    · apply List.getElem?_eq_some_iff.mpr
      refine ⟨hci, ?_⟩
      rw [getElem!_pos (f.blocks[bi]!.instrs) ci hci] at hcall
      exact hcall
    · exact hparts.1
    · exact hparts.2.1
    · exact hparts.2.2.1
    · exact hparts.2.2.2
    · simpa using hcistep.symm

/-! ### Well-formedness of one inlining splice -/

theorem blockAllDefs_rename (b : Block) (rho : ValId → ValId) (t : Term) :
    blockAllDefs
        { params := b.params.map rho
          instrs := b.instrs.map (renameInstr rho)
          term := t } =
      (blockAllDefs b).map rho := by
  simp only [blockAllDefs, List.map_append, renameInstr_defs,
    List.flatMap_map]
  rw [List.map_flatMap]

theorem flatMap_set_append_perm {alpha beta : Type} (l : List alpha)
    (k : alpha → List beta) {i : Nat} (hi : i < l.length)
    (new : alpha) (extra : List beta)
    (hpart : List.Perm (k new ++ extra) (k l[i])) :
    List.Perm ((l.set i new).flatMap k ++ extra) (l.flatMap k) := by
  rw [List.set_eq_take_append_cons_drop, if_pos hi]
  simp only [List.flatMap_append, List.flatMap_cons]
  have hswap : List.Perm
      ((l.take i).flatMap k ++ k new ++ (l.drop (i + 1)).flatMap k ++ extra)
      ((l.take i).flatMap k ++ (k new ++ extra) ++
        (l.drop (i + 1)).flatMap k) := by
    simpa only [List.append_assoc] using
      ((List.perm_append_comm : List.Perm
          ((l.drop (i + 1)).flatMap k ++ extra)
          (extra ++ (l.drop (i + 1)).flatMap k))).append_left
        ((l.take i).flatMap k ++ k new)
  have hrepl : List.Perm
      ((l.take i).flatMap k ++ (k new ++ extra) ++
        (l.drop (i + 1)).flatMap k)
      ((l.take i).flatMap k ++ k l[i] ++
        (l.drop (i + 1)).flatMap k) := by
    simpa only [List.append_assoc] using
      (hpart.append_right ((l.drop (i + 1)).flatMap k)).append_left
        ((l.take i).flatMap k)
  have hfinal :
      (l.take i).flatMap k ++ k l[i] ++ (l.drop (i + 1)).flatMap k =
        l.flatMap k := by
    have hl : l = l.take i ++ l[i] :: l.drop (i + 1) := by
      calc
        l = l.take (i + 1) ++ l.drop (i + 1) :=
          (List.take_append_drop (i + 1) l).symm
        _ = l.take i ++ l[i] :: l.drop (i + 1) := by
          rw [List.take_succ_eq_append_getElem hi]
          simp
    conv_rhs => rw [hl]
    simp only [List.flatMap_append, List.flatMap_cons, List.append_assoc]
  simpa only [List.append_assoc] using
    hswap.trans (hrepl.trans (List.Perm.of_eq hfinal))

theorem inlineSite_allDefs_perm {f : Func} {bi ci : Nat} {site : Block}
    {ds as : List ValId} (hbi : bi < f.blocks.size)
    (hsite : f.blocks[bi]? = some site) (hci : ci < site.instrs.length)
    (hcall : site.instrs[ci]? = some (.call ds fid as)) :
    let callBlock : Block :=
      { params := site.params, instrs := site.instrs.take ci,
        term := .jump ⟨f.blocks.size + entry, []⟩ }
    let contBlock : Block :=
      { params := ds, instrs := site.instrs.drop (ci + 1), term := site.term }
    List.Perm
      ((f.blocks.set! bi callBlock).toList.flatMap blockAllDefs ++
        blockAllDefs contBlock)
      (f.blocks.toList.flatMap blockAllDefs) := by
  dsimp only
  have hget : site.instrs[ci] = .call ds fid as := by
    rw [List.getElem?_eq_getElem hci] at hcall
    exact Option.some.inj hcall
  have his : site.instrs = site.instrs.take ci ++
      .call ds fid as :: site.instrs.drop (ci + 1) := by
    calc
      site.instrs = site.instrs.take ci ++ site.instrs.drop ci :=
        (List.take_append_drop ci site.instrs).symm
      _ = site.instrs.take ci ++
          .call ds fid as :: site.instrs.drop (ci + 1) := by
        rw [List.drop_eq_getElem_cons hci, hget]
  have hdefs : site.instrs.flatMap Instr.defs =
      (site.instrs.take ci).flatMap Instr.defs ++ ds ++
        (site.instrs.drop (ci + 1)).flatMap Instr.defs := by
    conv_lhs => rw [his]
    simp [Instr.defs, List.append_assoc]
  have hpart : List.Perm
      (blockAllDefs
          { params := site.params, instrs := site.instrs.take ci,
            term := .jump ⟨f.blocks.size + entry, []⟩ } ++
        blockAllDefs
          { params := ds, instrs := site.instrs.drop (ci + 1), term := site.term })
      (blockAllDefs site) := by
    apply List.Perm.of_eq
    unfold blockAllDefs
    rw [hdefs]
    simp only [List.append_assoc]
  have hlistGet : f.blocks.toList[bi] = site := by
    rw [Array.getElem?_eq_getElem hbi] at hsite
    exact Option.some.inj hsite
  have hpart' : List.Perm
      (blockAllDefs
          { params := site.params, instrs := site.instrs.take ci,
            term := .jump ⟨f.blocks.size + entry, []⟩ } ++
        blockAllDefs
          { params := ds, instrs := site.instrs.drop (ci + 1), term := site.term })
      (blockAllDefs f.blocks.toList[bi]) := by
    rw [hlistGet]
    exact hpart
  simpa [Array.set!, Array.toList_setIfInBounds] using
    flatMap_set_append_perm f.blocks.toList blockAllDefs
      (by simpa using hbi)
      { params := site.params, instrs := site.instrs.take ci,
        term := .jump ⟨f.blocks.size + entry, []⟩ }
      (blockAllDefs
        { params := ds, instrs := site.instrs.drop (ci + 1), term := site.term })
      hpart'

theorem mem_allDefs_le_maxVal {f : Func} {x : ValId} (hx : x ∈ f.allDefs) :
    x ≤ maxVal f := by
  rw [allDefs_eq] at hx
  rcases List.mem_append.mp hx with hp | hb
  · exact param_le_maxVal hp
  · obtain ⟨b, hb, hx⟩ := List.mem_flatMap.mp hb
    rcases List.mem_append.mp hx with hp | hi
    · exact blockParam_le_maxVal hb hp
    · obtain ⟨i, hi, hd⟩ := List.mem_flatMap.mp hi
      exact instrDef_le_maxVal hb hi hd

theorem inlineReplayBlock_allDefs (rho : ValId → ValId)
    (beta : BlockId → BlockId) (contId : BlockId) (b : Block) :
    blockAllDefs (inlineReplayBlock rho beta contId b) =
      (blockAllDefs b).map rho := by
  exact blockAllDefs_rename b rho _

theorem inlineReplayBlocks_allDefs (rho : ValId → ValId)
    (beta : BlockId → BlockId) (contId : BlockId) (g : Func) :
    (g.blocks.map (inlineReplayBlock rho beta contId)).toList.flatMap blockAllDefs =
      (g.blocks.toList.flatMap blockAllDefs).map rho := by
  simp only [Array.toList_map, List.flatMap_map, inlineReplayBlock_allDefs]
  rw [List.map_flatMap]

theorem calleeBody_not_param {g : Func} (hnd : g.allDefs.Nodup)
    {x : ValId} (hx : x ∈ g.blocks.toList.flatMap blockAllDefs) : x ∉ g.params := by
  rw [allDefs_eq] at hnd
  exact fun hp => (List.nodup_append.mp hnd).2.2 x hp x hx rfl

theorem inlineBody_map_eq_shift {g : Func} {as : List ValId} {off : Nat}
    (hnd : g.allDefs.Nodup) :
    (g.blocks.toList.flatMap blockAllDefs).map (inlineRho g.params as off) =
      (g.blocks.toList.flatMap blockAllDefs).map (fun x => x + off) := by
  apply List.map_congr_left
  intro x hx
  exact inlineRho_of_not_param (calleeBody_not_param hnd hx)

theorem inlineSplice_allDefs_perm {f g f' : Func} {bi ci : Nat}
    {site : Block} {ds as : List ValId} {off contId : Nat}
    {rho : ValId → ValId} {beta : BlockId → BlockId}
    {callBlock cont : Block}
    (hbi : bi < f.blocks.size) (hsite : f.blocks[bi]? = some site)
    (hci : ci < site.instrs.length)
    (hcall : site.instrs[ci]? = some (.call ds fid as))
    (_hoff : off = Nat.max (maxVal f) (maxVal g) + 1)
    (hrho : rho = inlineRho g.params as off)
    (hcallBlock : callBlock =
      { params := site.params, instrs := site.instrs.take ci,
        term := .jump ⟨f.blocks.size + g.entry, []⟩ })
    (hcont : cont =
      { params := ds, instrs := site.instrs.drop (ci + 1), term := site.term })
    (hblocks : f'.blocks =
      (f.blocks.set! bi callBlock) ++
        g.blocks.map (inlineReplayBlock rho beta contId) ++ #[cont])
    (hparams : f'.params = f.params) (hgnd : g.allDefs.Nodup) :
    List.Perm f'.allDefs
      (f.allDefs ++
        (g.blocks.toList.flatMap blockAllDefs).map (fun x => x + off)) := by
  have hsiteDefs := inlineSite_allDefs_perm (fid := fid) (entry := g.entry)
    hbi hsite hci hcall
  rw [← hcallBlock, ← hcont] at hsiteDefs
  have hspliced :
      (g.blocks.map (inlineReplayBlock rho beta contId)).toList.flatMap blockAllDefs =
        (g.blocks.toList.flatMap blockAllDefs).map (fun x => x + off) := by
    rw [inlineReplayBlocks_allDefs, hrho, inlineBody_map_eq_shift hgnd]
  have hbody : List.Perm
      ((f.blocks.set! bi callBlock).toList.flatMap blockAllDefs ++
        (g.blocks.map (inlineReplayBlock rho beta contId)).toList.flatMap blockAllDefs ++
        blockAllDefs cont)
      (f.blocks.toList.flatMap blockAllDefs ++
        (g.blocks.toList.flatMap blockAllDefs).map (fun x => x + off)) := by
    let A := (f.blocks.set! bi callBlock).toList.flatMap blockAllDefs
    let S := (g.blocks.map (inlineReplayBlock rho beta contId)).toList.flatMap blockAllDefs
    let C := blockAllDefs cont
    have hswap : List.Perm (A ++ S ++ C) (A ++ C ++ S) := by
      simpa only [List.append_assoc] using
        ((List.perm_append_comm : List.Perm (S ++ C) (C ++ S))).append_left A
    have hrepl : List.Perm (A ++ C ++ S)
        (f.blocks.toList.flatMap blockAllDefs ++ S) :=
      hsiteDefs.append_right S
    simpa only [A, S, C, hspliced] using hswap.trans hrepl
  unfold Func.allDefs
  rw [hparams, hblocks, Array.toList_append, Array.toList_append]
  simp only [List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]
  simpa only [List.append_assoc] using hbody.append_left f.params

theorem inlineSplice_allDefs_nodup {f g f' : Func} {bi ci : Nat}
    {site : Block} {ds as : List ValId} {off contId : Nat}
    {rho : ValId → ValId} {beta : BlockId → BlockId}
    {callBlock cont : Block}
    (hbi : bi < f.blocks.size) (hsite : f.blocks[bi]? = some site)
    (hci : ci < site.instrs.length)
    (hcall : site.instrs[ci]? = some (.call ds fid as))
    (hoff : off = Nat.max (maxVal f) (maxVal g) + 1)
    (hrho : rho = inlineRho g.params as off)
    (hcallBlock : callBlock =
      { params := site.params, instrs := site.instrs.take ci,
        term := .jump ⟨f.blocks.size + g.entry, []⟩ })
    (hcont : cont =
      { params := ds, instrs := site.instrs.drop (ci + 1), term := site.term })
    (hblocks : f'.blocks =
      (f.blocks.set! bi callBlock) ++
        g.blocks.map (inlineReplayBlock rho beta contId) ++ #[cont])
    (hparams : f'.params = f.params)
    (hfnd : f.allDefs.Nodup) (hgnd : g.allDefs.Nodup) : f'.allDefs.Nodup := by
  have hp := inlineSplice_allDefs_perm (fid := fid) hbi hsite hci hcall
    hoff hrho hcallBlock hcont hblocks hparams hgnd
  apply hp.nodup_iff.mpr
  apply List.nodup_append.mpr
  refine ⟨hfnd, ?_, ?_⟩
  · have hbody : (g.blocks.toList.flatMap blockAllDefs).Nodup := by
      rw [allDefs_eq] at hgnd
      exact (List.nodup_append.mp hgnd).2.1
    exact hbody.map (fun _ _ h => Nat.add_right_cancel h)
  · intro x hx y hy hxy
    have hxlt : x < off := by
      rw [hoff]
      exact lt_of_le_of_lt (mem_allDefs_le_maxVal hx)
        (maxVal_lt_inlineOffset_left f g)
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
    have hge : off ≤ z + off := by omega
    apply Nat.not_le_of_lt hxlt
    rw [hxy]
    exact hge

def blockCheckB (blocks : Array Block) (nrets nFuncs : Nat) (b : Block) : Bool :=
  (match b.term with
   | .ret vs => vs.length = nrets
   | _ => true)
  && (b.term.edges.all fun e =>
      match blocks[e.target]? with
      | some tb => e.args.length = tb.params.length
      | none => false)
  && b.instrs.all fun i =>
    match i with
    | .op ds _ _ => ds.length ≤ 1
    | .call _ g _ => g < nFuncs
    | _ => true

def BlockWF (blocks : Array Block) (nrets nFuncs : Nat) (b : Block) : Prop :=
  (match b.term with
   | .ret vs => vs.length = nrets
   | _ => True)
  ∧ (∀ e ∈ b.term.edges, ∃ tb, blocks[e.target]? = some tb ∧
      e.args.length = tb.params.length)
  ∧ ∀ i ∈ b.instrs,
    match i with
    | .op ds _ _ => ds.length ≤ 1
    | .call _ g _ => g < nFuncs
    | _ => True

theorem blockCheckB_eq_true {blocks : Array Block} {nrets nFuncs : Nat}
    {b : Block} : blockCheckB blocks nrets nFuncs b = true ↔
      BlockWF blocks nrets nFuncs b := by
  unfold blockCheckB BlockWF
  simp only [Bool.and_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨⟨hret, hedge⟩, hinstr⟩
    refine ⟨?_, ?_, ?_⟩
    · cases ht : b.term <;> simp_all
    · intro e he
      have h := hedge e he
      split at h <;> simp_all
    · intro i hi
      have h := hinstr i hi
      cases i <;> simp_all
  · rintro ⟨hret, hedge, hinstr⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · cases ht : b.term <;> simp_all
    · intro e he
      obtain ⟨tb, htb, hlen⟩ := hedge e he
      rw [htb]
      simpa using hlen
    · intro i hi
      have h := hinstr i hi
      cases i <;> simp_all

theorem func_wfCheck_iff {f : Func} {nFuncs : Nat} :
    f.wfCheck nFuncs = true ↔
      f.allDefs.Nodup ∧ f.entry < f.blocks.size ∧
      (∃ eb, f.blocks[f.entry]? = some eb ∧ eb.params = []) ∧
      ∀ b ∈ f.blocks.toList, BlockWF f.blocks f.nrets nFuncs b := by
  unfold Func.wfCheck
  change (f.allDefs.Nodup && f.entry < f.blocks.size &&
      (match f.blocks[f.entry]? with
       | some b => b.params.isEmpty
       | none => false) &&
      f.blocks.all (blockCheckB f.blocks f.nrets nFuncs)) = true ↔ _
  simp only [Bool.and_eq_true, decide_eq_true_eq, Array.all_eq_true_iff_forall_mem,
    blockCheckB_eq_true]
  constructor
  · rintro ⟨⟨⟨hnd, hentry⟩, hempty⟩, hall⟩
    rcases hget : f.blocks[f.entry]? with _ | eb
    · simp [hget] at hempty
    · refine ⟨hnd, hentry, ⟨eb, rfl, ?_⟩, ?_⟩
      · exact List.isEmpty_iff.mp (by simpa [hget] using hempty)
      · intro b hb
        exact hall b (by simpa using hb)
  · rintro ⟨hnd, hentry, ⟨eb, heb, hempty⟩, hall⟩
    refine ⟨⟨⟨hnd, hentry⟩, ?_⟩, ?_⟩
    · rw [heb]
      simp [hempty]
    · intro i hi
      exact hall i (by simpa using hi)

theorem inlineBlocks_old_lookup {f f' g : Func} {bi : Nat} {site callBlock cont : Block}
    {rho : ValId → ValId} {beta : BlockId → BlockId} {contId : Nat}
    (hbi : bi < f.blocks.size) (hsite : f.blocks[bi]? = some site)
    (hcallParams : callBlock.params = site.params)
    (hblocks : f'.blocks =
      (f.blocks.set! bi callBlock) ++
        g.blocks.map (inlineReplayBlock rho beta contId) ++ #[cont])
    {i : BlockId} {b : Block} (hb : f.blocks[i]? = some b) :
    ∃ b', f'.blocks[i]? = some b' ∧ b'.params = b.params := by
  have hi : i < f.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  have hprefix : f'.blocks[i]? = (f.blocks.set! bi callBlock)[i]? := by
    have hout : i < ((f.blocks.set! bi callBlock) ++
        g.blocks.map (inlineReplayBlock rho beta contId)).size := by
      simpa using lt_of_lt_of_le hi (Nat.le_add_right f.blocks.size g.blocks.size)
    rw [hblocks, Array.getElem?_append_left hout,
      Array.getElem?_append_left (by simpa using hi)]
  by_cases h : i = bi
  · subst i
    refine ⟨callBlock, ?_, ?_⟩
    · rw [hprefix]
      simp [Array.set!, hbi]
    · have hbsite : b = site := Option.some.inj (hb.symm.trans hsite)
      subst b
      exact hcallParams
  · refine ⟨b, ?_, rfl⟩
    rw [hprefix]
    simpa [Array.set!, Array.getElem?_setIfInBounds_ne (Ne.symm h)] using hb

theorem BlockWF.with_new_targets {old new : Array Block} {nrets nFuncs : Nat}
    {b : Block} (h : BlockWF old nrets nFuncs b)
    (htarget : ∀ {e tb}, e ∈ b.term.edges → old[e.target]? = some tb →
      ∃ tb', new[e.target]? = some tb' ∧ tb'.params = tb.params) :
    BlockWF new nrets nFuncs b := by
  refine ⟨h.1, ?_, h.2.2⟩
  intro e he
  obtain ⟨tb, htb, hlen⟩ := h.2.1 e he
  obtain ⟨tb', htb', hp⟩ := htarget he htb
  exact ⟨tb', htb', by simpa [hp] using hlen⟩

theorem inlineCallBlock_wf {f f' g : Func} {bi ci : Nat} {site callBlock cont : Block}
    {rho : ValId → ValId} {beta : BlockId → BlockId} {contId nFuncs : Nat}
    (hsiteWf : BlockWF f.blocks f.nrets nFuncs site)
    (hgentry : g.entry = 0) (hgentryParams : ∃ eb, g.blocks[g.entry]? = some eb ∧ eb.params = [])
    (hcallBlock : callBlock =
      { params := site.params, instrs := site.instrs.take ci,
        term := .jump ⟨f.blocks.size + g.entry, []⟩ })
    (hblocks : f'.blocks =
      (f.blocks.set! bi callBlock) ++
        g.blocks.map (inlineReplayBlock rho beta contId) ++ #[cont])
    (_hnrets : f'.nrets = f.nrets) :
    BlockWF f'.blocks f'.nrets nFuncs callBlock := by
  subst callBlock
  refine ⟨by simp, ?_, ?_⟩
  · intro e he
    simp only [Term.edges, List.mem_singleton] at he
    subst e
    obtain ⟨eb, heb, hp⟩ := hgentryParams
    have hget := inlineReplayBlock_get
      (f' := f') (preBlocks := f.blocks.set! bi
        { params := site.params, instrs := site.instrs.take ci,
          term := .jump ⟨f.blocks.size + g.entry, []⟩ })
      (ρ := rho) (β := beta) (contId := contId) (cont := cont)
      hblocks heb
    rw [hgentry] at hget ⊢
    refine ⟨inlineReplayBlock rho beta contId eb, by simpa using hget, ?_⟩
    simp [inlineReplayBlock, hp]
  · intro i hi
    exact hsiteWf.2.2 i (List.mem_of_mem_take hi)

theorem inlineContBlock_wf {f f' g : Func} {bi ci : Nat} {site callBlock cont : Block}
    {rho : ValId → ValId} {beta : BlockId → BlockId} {contId nFuncs : Nat}
    (hbi : bi < f.blocks.size) (hsite : f.blocks[bi]? = some site)
    (hsiteWf : BlockWF f.blocks f.nrets nFuncs site)
    (hcallParams : callBlock.params = site.params)
    (hcont : cont =
      { params := ds, instrs := site.instrs.drop (ci + 1), term := site.term })
    (hblocks : f'.blocks =
      (f.blocks.set! bi callBlock) ++
        g.blocks.map (inlineReplayBlock rho beta contId) ++ #[cont])
    (hnrets : f'.nrets = f.nrets) :
    BlockWF f'.blocks f'.nrets nFuncs cont := by
  subst cont
  rw [hnrets]
  refine ⟨hsiteWf.1, ?_, ?_⟩
  · intro e he
    obtain ⟨tb, htb, hlen⟩ := hsiteWf.2.1 e he
    obtain ⟨tb', htb', hp⟩ := inlineBlocks_old_lookup hbi hsite hcallParams
      hblocks htb
    exact ⟨tb', htb', by simpa [hp] using hlen⟩
  · intro i hi
    exact hsiteWf.2.2 i (List.mem_of_mem_drop hi)

theorem inlineReplayBlock_wf {f f' g : Func} {bi : Nat} {callBlock cont gb : Block}
    {rho : ValId → ValId} {beta : BlockId → BlockId} {contId nFuncs : Nat}
    (_hgb : gb ∈ g.blocks.toList) (hgbWf : BlockWF g.blocks g.nrets nFuncs gb)
    (hbeta : ∀ i, beta i = f.blocks.size + i)
    (hcontId : contId = f.blocks.size + g.blocks.size)
    (hcontParams : cont.params = ds) (hnrets : g.nrets = ds.length)
    (hblocks : f'.blocks =
      (f.blocks.set! bi callBlock) ++
        g.blocks.map (inlineReplayBlock rho beta contId) ++ #[cont])
    (_hfNrets : f'.nrets = f.nrets) :
    BlockWF f'.blocks f'.nrets nFuncs (inlineReplayBlock rho beta contId gb) := by
  refine ⟨?_, ?_, ?_⟩
  · cases ht : gb.term <;>
      simp [inlineReplayBlock, inlineReplayTerm, renameTerm, ht]
  · intro e he
    cases ht : gb.term with
    | jump old =>
        simp only [inlineReplayBlock, inlineReplayTerm, ht, renameTerm, Term.edges,
          List.mem_singleton] at he
        subst e
        obtain ⟨tb, htb, hlen⟩ := hgbWf.2.1 old (by rw [ht]; simp [Term.edges])
        have hget := inlineReplayBlock_get
          (f' := f') (preBlocks := f.blocks.set! bi callBlock)
          (ρ := rho) (β := beta) (contId := contId) (cont := cont) hblocks htb
        refine ⟨inlineReplayBlock rho beta contId tb, ?_, ?_⟩
        · change f'.blocks[beta old.target]? = _
          rw [hbeta]
          simpa using hget
        · simpa [inlineReplayBlock] using hlen
    | branch c et ef =>
        simp only [inlineReplayBlock, inlineReplayTerm, ht, renameTerm, Term.edges,
          List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl
        · obtain ⟨tb, htb, hlen⟩ := hgbWf.2.1 et (by rw [ht]; simp [Term.edges])
          have hget := inlineReplayBlock_get
            (f' := f') (preBlocks := f.blocks.set! bi callBlock)
            (ρ := rho) (β := beta) (contId := contId) (cont := cont) hblocks htb
          refine ⟨inlineReplayBlock rho beta contId tb, ?_, ?_⟩
          · change f'.blocks[beta et.target]? = _
            rw [hbeta]
            simpa using hget
          · simpa [inlineReplayBlock] using hlen
        · obtain ⟨tb, htb, hlen⟩ := hgbWf.2.1 ef (by rw [ht]; simp [Term.edges])
          have hget := inlineReplayBlock_get
            (f' := f') (preBlocks := f.blocks.set! bi callBlock)
            (ρ := rho) (β := beta) (contId := contId) (cont := cont) hblocks htb
          refine ⟨inlineReplayBlock rho beta contId tb, ?_, ?_⟩
          · change f'.blocks[beta ef.target]? = _
            rw [hbeta]
            simpa using hget
          · simpa [inlineReplayBlock] using hlen
    | ret vals =>
        simp only [inlineReplayBlock, inlineReplayTerm, ht, Term.edges,
          List.mem_singleton] at he
        subst e
        have hget := inlineContBlock_get
          (f' := f') (g := g) (preBlocks := f.blocks.set! bi callBlock)
          (ρ := rho) (β := beta) (contId := contId) (cont := cont) hblocks
        refine ⟨cont, ?_, ?_⟩
        · rw [hcontId]
          simpa using hget
        · have hret := hgbWf.1
          simp only [ht] at hret
          simpa [hcontParams, hnrets] using hret
    | halt yop args =>
        simp [inlineReplayBlock, inlineReplayTerm, renameTerm, ht, Term.edges] at he
  · intro i hi
    simp only [inlineReplayBlock] at hi
    obtain ⟨old, hold, heq⟩ := List.mem_map.mp hi
    subst i
    have hold := hgbWf.2.2 old hold
    cases old <;> simp_all [renameInstr]

theorem inlineOnce_nrets {counts : Array Nat} {funcs : Array Func}
    {f f' : Func} (hio : inlineOnce counts funcs f = some f') :
    f'.nrets = f.nrets := by
  obtain ⟨bi, site, ci, ds, fid, as, g, hbi, hsite, hci, hcall, hfunc,
    hcount, hlen, hnrets, hentry, hf'⟩ := inlineOnce_inv hio
  rw [hf']

theorem inlineReplayBlock_eq (rho : ValId → ValId) (beta : BlockId → BlockId)
    (contId : BlockId) (gb : Block) :
    inlineReplayBlock rho beta contId gb =
      { params := gb.params.map rho
        instrs := gb.instrs.map (renameInstr rho)
        term := match gb.term with
          | .ret vs => .jump ⟨contId, vs.map rho⟩
          | t => renameTerm rho beta t } := by
  rcases gb with ⟨params, instrs, term⟩
  cases term <;> rfl

theorem inlineOnce_wf {counts : Array Nat} {funcs : Array Func}
    {f f' : Func} {nFuncs : Nat}
    (hfuncs : ∀ {fid : FuncId} {g : Func},
      funcs[fid]? = some g → g.wfCheck nFuncs = true)
    (hfwf : f.wfCheck nFuncs = true)
    (hio : inlineOnce counts funcs f = some f') :
    f'.wfCheck nFuncs = true := by
  obtain ⟨bi, site, ci, ds, fid, as, g, hbi, hsite, hci, hcall, hfunc,
    hcount, hlen, hnrets, hentry, hf'⟩ := inlineOnce_inv hio
  let off := Nat.max (maxVal f) (maxVal g) + 1
  let rho := fun v =>
    match (g.params.zip as).find? (fun pa => pa.1 == v) with
    | some pa => pa.2
    | none => v + off
  let beta : BlockId → BlockId := fun i => f.blocks.size + i
  let contId := f.blocks.size + g.blocks.size
  let callBlock : Block :=
    { params := site.params, instrs := site.instrs.take ci,
      term := .jump ⟨f.blocks.size + g.entry, []⟩ }
  let cont : Block :=
    { params := ds, instrs := site.instrs.drop (ci + 1), term := site.term }
  let replay : Block → Block := fun gb =>
    { params := gb.params.map rho
      instrs := gb.instrs.map (renameInstr rho)
      term := match gb.term with
        | .ret vs => .jump ⟨contId, vs.map rho⟩
        | t => renameTerm rho beta t }
  have hfRaw : f' =
      { f with blocks := (f.blocks.set! bi callBlock) ++
          g.blocks.map replay ++ #[cont] } := by
    simpa [off, rho, beta, contId, callBlock, cont, replay, inlineRho] using hf'
  have hreplay : g.blocks.map replay =
      g.blocks.map (inlineReplayBlock rho beta contId) := by
    apply congrArg (fun k : Block → Block => g.blocks.map k)
    funext gb
    exact (inlineReplayBlock_eq rho beta contId gb).symm
  have hfNamed : f' =
      { f with blocks := (f.blocks.set! bi callBlock) ++
          g.blocks.map (inlineReplayBlock rho beta contId) ++ #[cont] } := by
    rw [hfRaw, hreplay]
  have hblocks : f'.blocks =
      (f.blocks.set! bi callBlock) ++
        g.blocks.map (inlineReplayBlock rho beta contId) ++ #[cont] := by
    rw [hfNamed]
  have hparams : f'.params = f.params := by rw [hfNamed]
  have hnrets' : f'.nrets = f.nrets := by rw [hfNamed]
  have hentry' : f'.entry = f.entry := by rw [hfNamed]
  have hcallBlock : callBlock =
      { params := site.params, instrs := site.instrs.take ci,
        term := .jump ⟨f.blocks.size + g.entry, []⟩ } := rfl
  have hcont : cont =
      { params := ds, instrs := site.instrs.drop (ci + 1), term := site.term } := rfl
  have hcallParams : callBlock.params = site.params := rfl
  have hcontParams : cont.params = ds := rfl
  have hgwf := hfuncs hfunc
  obtain ⟨hfnd, hfentry, ⟨feb, hfeb, hfempty⟩, hfblocks⟩ :=
    func_wfCheck_iff.mp hfwf
  obtain ⟨hgnd, hgentryLt, ⟨geb, hgeb, hgempty⟩, hgblocks⟩ :=
    func_wfCheck_iff.mp hgwf
  have hsiteWf : BlockWF f.blocks f.nrets nFuncs site :=
    hfblocks site (block_mem_of_getElem? hsite)
  apply func_wfCheck_iff.mpr
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact inlineSplice_allDefs_nodup (fid := fid) hbi hsite hci hcall rfl rfl
      hcallBlock hcont hblocks hparams hfnd hgnd
  · rw [hentry']
    exact lt_of_lt_of_le hfentry (by rw [hblocks]; simp)
  · obtain ⟨feb', hfeb', hp⟩ := inlineBlocks_old_lookup hbi hsite hcallParams
      hblocks hfeb
    exact ⟨feb', by simpa [hentry'] using hfeb', by simpa [hp] using hfempty⟩
  · intro b hb
    have hbarr : b ∈ f'.blocks := by simpa using hb
    rw [hblocks] at hbarr
    simp only [Array.mem_append, Array.mem_map, Array.mem_singleton] at hbarr
    rcases hbarr with (hbset | ⟨gb, hgb, rfl⟩) | rfl
    · rcases Array.mem_or_eq_of_mem_setIfInBounds hbset with hold | rfl
      · rw [hnrets']
        apply (hfblocks b (by simpa using hold)).with_new_targets
        intro e tb he htb
        exact inlineBlocks_old_lookup hbi hsite hcallParams hblocks htb
      · exact inlineCallBlock_wf hsiteWf hentry ⟨geb, hgeb, hgempty⟩
          hcallBlock hblocks hnrets'
    · exact inlineReplayBlock_wf (by simpa using hgb)
        (hgblocks gb (by simpa using hgb)) (fun _ => rfl) rfl hcontParams hnrets
        hblocks hnrets'
    · exact inlineContBlock_wf hbi hsite hsiteWf hcallParams hcont hblocks hnrets'

end Passes

section
variable [model : ExternalModel]

/- **One splice preserves executions.**

The callee-side part of the interesting `Exec.call` / `Exec.callHalt` node is
now proved by `Passes.inlineReplay_execN`. In the inlined function that node
becomes: `jump` into the
spliced callee entry, the callee's own derivation re-played inside the caller,
and its `Exec.ret` re-played as the `jump ⟨contId, vs.map ρ⟩` that binds `ds` in
`contBlock`. The register-file obligation is register agreement under the
renaming `ρ`: the callee ran from the *fresh* file
`Regs.empty.setMany g.params args`, while the splice runs from the caller's file
extended at `ρ`-images, and the two agree on everything the callee body reads
because (i) `ρ` sends the callee's parameters to the caller ids holding `args`
and (ii) `ρ` sends everything else above `maxVal f`, so no caller binding is
disturbed — `Regs.setMany_congr` is the work-horse. The `.halt` case is the
same derivation truncated.

`Passes.inlineOnce_inv` above supplies the site inversion:
`bi`, `ci`, the selected call/callee, every guard, and the complete splice
equation.  The remaining first proof object is the renamed-callee `Exec` replay.
The non-injective-formal problem is discharged by the partitioned invariants
`Passes.RenamedAgree` and `Passes.CallerFrame`: the former is one-way (only a
successful callee read must be reproduced), while the latter preserves every
caller register below `off`. `Passes.inlineReplay_execN` carries both through
renamed instructions and block edges, proves appended-block lookups, turns
callee `ret` into the continuation jump, and propagates halts.

The caller-side proof below is indexed by execution location.  Its induction
over the enclosing `Exec` derivation distinguishes four locations:
an ordinary caller block, the prefix before `(bi, ci)`, the selected call itself,
and the new continuation containing `drop (ci + 1)`.  On a back-edge to `bi` it
must re-enter the prefix case (and inline the call again); on a return it must
enter the continuation case with the `CallerFrame` produced by
`inlineReplay_execN`.  A plain structural equality test on the current
instruction is insufficient because an equal call instruction may occur in the
prefix at a different position. -/
omit model in
theorem Passes.inlineCallerRest_before {bi ci entry k : Nat} {site : Block}
    {i : Instr} {is : List Instr} {t : Term} (hk : k < ci)
    (hdrop : site.instrs.drop k = i :: is) :
    inlineCallerRest bi ci entry bi k site ⟨i :: is, t⟩ =
      ⟨i :: (site.instrs.take ci).drop (k + 1), .jump ⟨entry, []⟩⟩ := by
  have hki : k < site.instrs.length := by
    have hlen := congrArg List.length hdrop
    simp at hlen
    omega
  have hkt : k < (site.instrs.take ci).length := by simp; omega
  have hi : site.instrs[k] = i := by
    rw [List.drop_eq_getElem_cons hki] at hdrop
    exact (List.cons.inj hdrop).1
  simp only [inlineCallerRest, true_and, le_of_lt hk, if_true]
  congr 1
  rw [List.drop_eq_getElem_cons hkt]
  congr
  simpa using hi

omit model in
theorem Passes.inlineCallerRest_site (bi ci entry : Nat) (site : Block)
    (r : Rest) :
    inlineCallerRest bi ci entry bi ci site r = ⟨[], .jump ⟨entry, []⟩⟩ := by
  simp [inlineCallerRest]

omit model in
theorem Passes.inlineCallerRest_cons_of_not_site
    {bi ci entry j k : Nat} {site cur : Block} {i : Instr}
    {is : List Instr} {t : Term}
    (hcur : j = bi → cur = site) (hne : j ≠ bi ∨ k ≠ ci)
    (hdrop : cur.instrs.drop k = i :: is) :
    inlineCallerRest bi ci entry j k site ⟨i :: is, t⟩ =
      let r := inlineCallerRest bi ci entry j (k + 1) site ⟨is, t⟩
      ⟨i :: r.instrs, r.term⟩ := by
  by_cases hj : j = bi
  · subst j
    have hcur' : cur = site := hcur rfl
    subst cur
    rcases hne with hne | hne
    · exact (hne rfl).elim
    · rcases Nat.lt_or_gt_of_ne hne with hk | hk
      · rw [inlineCallerRest_before hk hdrop]
        simp [inlineCallerRest, Nat.succ_le_iff.mpr hk]
      · simp [inlineCallerRest, Nat.not_le_of_lt hk,
          Nat.not_le_of_lt (lt_trans hk (Nat.lt_succ_self k))]
  · simp [inlineCallerRest, hj]

omit model in
theorem Passes.head_eq_of_drop_eq_cons {xs : List α} {k : Nat} {x y : α}
    {ys : List α} (hx : xs[k]? = some x) (hdrop : xs.drop k = y :: ys) :
    y = x := by
  have hk : k < xs.length := (List.getElem?_eq_some_iff.mp hx).1
  rw [List.drop_eq_getElem_cons hk] at hdrop
  have hy := (List.cons.inj hdrop).1
  rw [List.getElem?_eq_getElem hk] at hx
  exact hy.symm.trans (Option.some.inj hx)

omit model in
theorem Passes.drop_succ_eq_of_drop_eq_cons {xs : List α} {k : Nat}
    {x : α} {ys : List α} (hdrop : xs.drop k = x :: ys) :
    xs.drop (k + 1) = ys := by
  rw [← List.drop_drop, hdrop]
  rfl

omit model in
theorem Passes.mem_of_drop_eq_cons {xs : List α} {k : Nat}
    {x : α} {ys : List α} (hdrop : xs.drop k = x :: ys) : x ∈ xs := by
  rw [← List.take_append_drop k xs, hdrop]
  simp

omit model in
theorem Passes.CallerFrame.getMany {off : Nat} {R R' : Regs}
    (h : CallerFrame off R R') {xs : List ValId}
    (hxs : ∀ x ∈ xs, x < off) : R.getMany xs = R'.getMany xs := by
  exact Regs.getMany_congr fun x hx => (h x (hxs x hx)).symm

omit model in
theorem Passes.CallerFrame.setMany {off : Nat} {R R' : Regs}
    (h : CallerFrame off R R') {xs : List ValId} (vals : List U256) :
    CallerFrame off (R.setMany xs vals) (R'.setMany xs vals) := by
  intro x hx
  exact Regs.setMany_congr (S := fun y => y < off) h xs vals x hx

/-- The positional caller replay preserves the call-depth bound. -/
theorem Passes.inlineCaller_execN
    {P : Prog} {n : Nat} {f f' g : Func} {bi ci : Nat} {site : Block}
    {ds as : List ValId} {fid off contId : Nat}
    {ρ : ValId → ValId} {β : BlockId → BlockId} {cont callBlock : Block}
    {R Ri : Regs} {st : EvmState} {rest : Rest} {res : FRes}
    (hsite : f.blocks[bi]? = some site)
    (hci : ci < site.instrs.length)
    (hcall : site.instrs[ci]? = some (.call ds fid as))
    (hfunc : P.funcs[fid]? = some g)
    (hgwf : g.wfCheck P.funcs.size = true)
    (hoff : off = Nat.max (Passes.maxVal f) (Passes.maxVal g) + 1)
    (hρ : ρ = inlineRho g.params as off)
    (hβ : ∀ i, β i = f.blocks.size + i)
    (hcontId : contId = f.blocks.size + g.blocks.size)
    (hentry : g.entry = 0)
    (hlen : g.params.length = as.length)
    (hnrets : g.nrets = ds.length)
    (hcallBlock : callBlock =
      { params := site.params, instrs := site.instrs.take ci,
        term := .jump ⟨f.blocks.size + g.entry, []⟩ })
    (hcont : cont =
      { params := ds, instrs := site.instrs.drop (ci + 1), term := site.term })
    (hblocks : f'.blocks =
      (f.blocks.set! bi callBlock) ++
        g.blocks.map (inlineReplayBlock ρ β contId) ++ #[cont])
    (hexec : ExecN (model := model) P n f R st rest res)
    {j k : Nat} {cur : Block}
    (hcur : f.blocks[j]? = some cur)
    (hdrop : cur.instrs.drop k = rest.instrs)
    (hterm : cur.term = rest.term)
    (hframe : CallerFrame off R Ri) :
    ExecN (model := model) P n f' Ri st
      (inlineCallerRest bi ci (f.blocks.size + g.entry) j k site rest) res := by
  have hoffCaller : Passes.maxVal f < off := by
    rw [hoff]
    exact maxVal_lt_inlineOffset_left f g
  have hoffCallee : Passes.maxVal g < off := by
    rw [hoff]
    exact maxVal_lt_inlineOffset_right f g
  have hsiteMem := block_mem_of_getElem? hsite
  have hnd : g.allDefs.Nodup := by
    unfold Func.wfCheck at hgwf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hgwf
    exact hgwf.1.1.1
  have hpsnd : g.params.Nodup := by
    exact params_nodup_of_allDefs hnd rfl
  have hret : ∀ {b : Block}, b ∈ g.blocks.toList → ∀ {xs},
      b.term = .ret xs → xs.length = ds.length := by
    intro b hb xs ht
    rw [← hnrets]
    exact wfCheck_ret_arity hgwf hb ht
  induction hexec generalizing j k cur Ri with
  | @const n _ R st d v is t res htail ih =>
      have himem : Instr.const d v ∈ cur.instrs := mem_of_drop_eq_cons hdrop
      have hcurSite : j = bi → cur = site := by
        intro hj
        subst j
        exact Option.some.inj (hcur.symm.trans hsite)
      have hne : j ≠ bi ∨ k ≠ ci := by
        by_contra hn
        simp only [not_or, not_ne_iff] at hn
        obtain ⟨rfl, rfl⟩ := hn
        have hcureq := hcurSite rfl
        subst cur
        have heq := head_eq_of_drop_eq_cons hcall hdrop
        cases heq
      rw [inlineCallerRest_cons_of_not_site hcurSite hne hdrop]
      refine ExecN.const (ih hsite hoff hβ hcontId hcallBlock hblocks hcur
        (drop_succ_eq_of_drop_eq_cons hdrop) hterm ?_ hoffCaller hsiteMem)
      simpa [Regs.setMany_cons, Regs.setMany_nil_left] using
        (hframe.setMany (xs := [d]) [v])
  | @op n _ R st st' ods yop oas oargs rets is t res hget hop hlenRet htail ih =>
      have himem : Instr.op ods yop oas ∈ cur.instrs := mem_of_drop_eq_cons hdrop
      have hcurSite : j = bi → cur = site := by
        intro hj; subst j; exact Option.some.inj (hcur.symm.trans hsite)
      have hne : j ≠ bi ∨ k ≠ ci := by
        by_contra hn
        simp only [not_or, not_ne_iff] at hn
        obtain ⟨rfl, rfl⟩ := hn
        have hcureq := hcurSite rfl
        subst cur
        have heq := head_eq_of_drop_eq_cons hcall hdrop
        cases heq
      have hoas : ∀ x ∈ oas, x < off := by
        intro x hx
        exact lt_of_le_of_lt (instrUse_le_maxVal (block_mem_of_getElem? hcur)
          himem (by simpa [Instr.uses] using hx)) hoffCaller
      rw [inlineCallerRest_cons_of_not_site hcurSite hne hdrop]
      refine ExecN.op (args := oargs) (rets := rets)
        (by rw [← hframe.getMany hoas]; exact hget) hop hlenRet
        (ih hsite hoff hβ hcontId hcallBlock hblocks hcur
          (drop_succ_eq_of_drop_eq_cons hdrop) hterm ?_ hoffCaller hsiteMem)
      exact hframe.setMany rets
  | @opHalt n _ R st st' ods yop oas oargs is t hget hop =>
      have himem : Instr.op ods yop oas ∈ cur.instrs := mem_of_drop_eq_cons hdrop
      have hcurSite : j = bi → cur = site := by
        intro hj; subst j; exact Option.some.inj (hcur.symm.trans hsite)
      have hne : j ≠ bi ∨ k ≠ ci := by
        by_contra hn
        simp only [not_or, not_ne_iff] at hn
        obtain ⟨rfl, rfl⟩ := hn
        have hcureq := hcurSite rfl
        subst cur
        have heq := head_eq_of_drop_eq_cons hcall hdrop
        cases heq
      have hoas : ∀ x ∈ oas, x < off := by
        intro x hx
        exact lt_of_le_of_lt (instrUse_le_maxVal (block_mem_of_getElem? hcur)
          himem (by simpa [Instr.uses] using hx)) hoffCaller
      rw [inlineCallerRest_cons_of_not_site hcurSite hne hdrop]
      exact ExecN.opHalt (args := oargs) (by rw [← hframe.getMany hoas]; exact hget) hop
  | @call n fcur callee R st st' ods oas ofid oargs rvals eb is t res
      hfid hget hplen heb hbody hlenRet htail ihbody ih =>
      have himem : Instr.call ods ofid oas ∈ cur.instrs := mem_of_drop_eq_cons hdrop
      have hcurSite : j = bi → cur = site := by
        intro hj; subst j; exact Option.some.inj (hcur.symm.trans hsite)
      by_cases hat : j = bi ∧ k = ci
      · obtain ⟨rfl, rfl⟩ := hat
        have hcureq := hcurSite rfl
        subst cur
        have heq := head_eq_of_drop_eq_cons hcall hdrop
        cases heq
        have hgEq : callee = g := Option.some.inj (hfid.symm.trans hfunc)
        subst callee
        rw [inlineCallerRest_site]
        have hoas : ∀ x ∈ as, x < off := by
          intro x hx
          exact lt_of_le_of_lt (instrUse_le_maxVal hsiteMem himem
            (by simpa [Instr.uses] using hx)) hoffCaller
        have hgetRi : Ri.getMany as = some oargs := by
          rw [← hframe.getMany hoas]
          exact hget
        have hentryParams : eb.params = [] := wfCheck_entry_params_nil hgwf (by
          simpa [hentry] using heb)
        refine ExecN.jump (args := [])
          (tb := inlineReplayBlock ρ β contId eb) ?_ (by simp)
          (by simp [inlineReplayBlock, hentryParams]) ?_
        · have hbcopy := inlineReplayBlock_get hblocks heb
          simpa using hbcopy
        · have hreplay := inlineReplay_execN (g := g) (f' := f')
            (preBlocks := fcur.blocks.set! j callBlock)
            (cont := cont) (ps := g.params) (as := as) (ds := ds)
            (off := off) (ρ := ρ) (β := β) (contId := contId)
            (Rc := Regs.empty.setMany g.params oargs) (Rcaller := R)
            (cres := .ret rvals st') (final := res) (b := eb)
            hρ (fun i => by simpa using hβ i) (by simpa using hcontId) hblocks
            (by rw [hcont]) hnd rfl hlen hoas
            (fun {_} hb {_} ht => hret hb ht) hbody (block_mem_of_getElem? heb)
            ⟨[], rfl, rfl⟩ (renamedAgree_entry hpsnd hlen hgetRi) hframe
            (fun s hs => by cases hs)
            (fun Rout vals s heq hRout => by
              cases heq
              have htailDrop := drop_succ_eq_of_drop_eq_cons hdrop
              rw [hcont]
              simpa [inlineCallerRest, htailDrop, hterm] using
                (ih hsite hoff hβ hcontId hcallBlock hblocks
                (j := j) (k := k + 1) (cur := site) hsite
                (drop_succ_eq_of_drop_eq_cons hdrop) hterm
                (hRout.setMany rvals) hoffCaller hsiteMem))
          simpa [inlineReplayBlock, hentryParams, Regs.setMany_nil_left] using hreplay
      · have hne : j ≠ bi ∨ k ≠ ci := by omega
        have hoas : ∀ x ∈ oas, x < off := by
          intro x hx
          exact lt_of_le_of_lt (instrUse_le_maxVal (block_mem_of_getElem? hcur)
            himem (by simpa [Instr.uses] using hx)) hoffCaller
        rw [inlineCallerRest_cons_of_not_site hcurSite hne hdrop]
        refine ExecN.call (args := oargs) (rvals := rvals) (g := callee) (eb := eb)
          hfid (by rw [← hframe.getMany hoas]; exact hget) hplen heb hbody hlenRet
          (ih hsite hoff hβ hcontId hcallBlock hblocks hcur
            (drop_succ_eq_of_drop_eq_cons hdrop) hterm
            (hframe.setMany rvals) hoffCaller hsiteMem)
  | @callHalt n fcur callee R st st' ods oas ofid oargs eb is t
      hfid hget hplen heb hbody ihbody =>
      have himem : Instr.call ods ofid oas ∈ cur.instrs := mem_of_drop_eq_cons hdrop
      have hcurSite : j = bi → cur = site := by
        intro hj; subst j; exact Option.some.inj (hcur.symm.trans hsite)
      by_cases hat : j = bi ∧ k = ci
      · obtain ⟨rfl, rfl⟩ := hat
        have hcureq := hcurSite rfl
        subst cur
        have heq := head_eq_of_drop_eq_cons hcall hdrop
        cases heq
        have hgEq : callee = g := Option.some.inj (hfid.symm.trans hfunc)
        subst callee
        rw [inlineCallerRest_site]
        have hoas : ∀ x ∈ as, x < off := by
          intro x hx
          exact lt_of_le_of_lt (instrUse_le_maxVal hsiteMem himem
            (by simpa [Instr.uses] using hx)) hoffCaller
        have hgetRi : Ri.getMany as = some oargs := by
          rw [← hframe.getMany hoas]
          exact hget
        have hentryParams : eb.params = [] := wfCheck_entry_params_nil hgwf (by
          simpa [hentry] using heb)
        refine ExecN.jump (args := [])
          (tb := inlineReplayBlock ρ β contId eb) ?_ (by simp)
          (by simp [inlineReplayBlock, hentryParams]) ?_
        · have hbcopy := inlineReplayBlock_get hblocks heb
          simpa using hbcopy
        · have hreplay := inlineReplay_execN (g := g) (f' := f')
            (preBlocks := fcur.blocks.set! j callBlock)
            (cont := cont) (ps := g.params) (as := as) (ds := ds)
            (off := off) (ρ := ρ) (β := β) (contId := contId)
            (Rc := Regs.empty.setMany g.params oargs) (Rcaller := R)
            (cres := .halt st') (final := .halt st') (b := eb)
            hρ (fun i => by simpa using hβ i) (by simpa using hcontId) hblocks
            (by rw [hcont]) hnd rfl hlen hoas
            (fun {_} hb {_} ht => hret hb ht) hbody (block_mem_of_getElem? heb)
            ⟨[], rfl, rfl⟩ (renamedAgree_entry hpsnd hlen hgetRi) hframe
            (fun _ h => h)
            (fun Rout vals s heq _ => by cases heq)
          simpa [inlineReplayBlock, hentryParams, Regs.setMany_nil_left] using hreplay
      · have hne : j ≠ bi ∨ k ≠ ci := by omega
        have hoas : ∀ x ∈ oas, x < off := by
          intro x hx
          exact lt_of_le_of_lt (instrUse_le_maxVal (block_mem_of_getElem? hcur)
            himem (by simpa [Instr.uses] using hx)) hoffCaller
        rw [inlineCallerRest_cons_of_not_site hcurSite hne hdrop]
        exact ExecN.callHalt (args := oargs) (g := callee) (eb := eb) hfid
          (by rw [← hframe.getMany hoas]; exact hget) hplen heb hbody
  | @jump n fcur R st e tb vals res htb hget hplen htail ih =>
      have hbefore : ¬ (j = bi ∧ k ≤ ci) := by
        rintro ⟨rfl, hk⟩
        have hcureq : cur = site := Option.some.inj (hcur.symm.trans hsite)
        subst cur
        have hlenDrop := congrArg List.length hdrop
        simp at hlenDrop
        omega
      simp only [inlineCallerRest, if_neg hbefore]
      have htmem := block_mem_of_getElem? htb
      have hargs : ∀ x ∈ e.args, x < off := by
        intro x hx
        exact lt_of_le_of_lt (termUse_le_maxVal (block_mem_of_getElem? hcur)
          (by simpa [hterm, Term.uses] using hx)) hoffCaller
      by_cases he : e.target = bi
      · have htbSite : fcur.blocks[bi]? = some tb := by simpa [he] using htb
        have htbeq : tb = site := Option.some.inj (htbSite.symm.trans hsite)
        subst tb
        have htb' : f'.blocks[e.target]? = some callBlock := by
          rw [he]
          exact inlineCallerBlock_get_site₂ (f := fcur) (f' := f')
            (mid := g.blocks.map (inlineReplayBlock ρ β contId)) (tail := #[cont])
            (Array.getElem?_eq_some_iff.mp hsite).1 hblocks
        rw [hcallBlock] at htb'
        refine ExecN.jump (e := e) (args := vals) htb'
          (by rw [← hframe.getMany hargs]; exact hget)
          (by simpa [hcallBlock] using hplen) ?_
        simpa [inlineCallerRest, hcallBlock] using
          (ih hsite hoff hβ hcontId hcallBlock hblocks
          (j := bi) (k := 0) (cur := site) hsite rfl rfl
          (hframe.setMany vals) hoffCaller hsiteMem)
      · have htb' := inlineCallerBlock_get_other₂ (f := fcur) (f' := f')
          (callBlock := callBlock) (mid :=
            g.blocks.map (inlineReplayBlock ρ β contId)) (tail := #[cont]) htb he hblocks
        refine ExecN.jump (e := e) (args := vals) htb'
          (by rw [← hframe.getMany hargs]; exact hget) hplen ?_
        simpa [inlineCallerRest, he] using
          (ih hsite hoff hβ hcontId hcallBlock hblocks
          (j := e.target) (k := 0) (cur := tb) htb rfl rfl
          (hframe.setMany vals) hoffCaller hsiteMem)
  | @branchTrue n fcur R st c v et ef tb vals res hc hv htb hget hplen htail ih =>
      have hbefore : ¬ (j = bi ∧ k ≤ ci) := by
        rintro ⟨rfl, hk⟩
        have hcureq : cur = site := Option.some.inj (hcur.symm.trans hsite)
        subst cur
        have hlenDrop := congrArg List.length hdrop
        simp at hlenDrop
        omega
      simp only [inlineCallerRest, if_neg hbefore]
      have hcLt : c < off := lt_of_le_of_lt
        (termUse_le_maxVal (block_mem_of_getElem? hcur) (by simp [hterm, Term.uses]))
        hoffCaller
      have hargs : ∀ x ∈ et.args, x < off := by
        intro x hx
        exact lt_of_le_of_lt (termUse_le_maxVal (block_mem_of_getElem? hcur)
          (by simp [hterm, Term.uses, hx])) hoffCaller
      by_cases he : et.target = bi
      · have htbSite : fcur.blocks[bi]? = some tb := by simpa [he] using htb
        have htbeq : tb = site := Option.some.inj (htbSite.symm.trans hsite)
        subst tb
        have htb' : f'.blocks[et.target]? = some callBlock := by
          rw [he]
          exact inlineCallerBlock_get_site₂ (f := fcur) (f' := f')
            (mid := g.blocks.map (inlineReplayBlock ρ β contId)) (tail := #[cont])
            (Array.getElem?_eq_some_iff.mp hsite).1 hblocks
        rw [hcallBlock] at htb'
        refine ExecN.branchTrue (et := et) (ef := ef) (v := v) (args := vals)
          (by rw [hframe c hcLt]; exact hc) hv htb'
          (by rw [← hframe.getMany hargs]; exact hget)
          (by simpa [hcallBlock] using hplen) ?_
        simpa [inlineCallerRest, hcallBlock] using
          (ih hsite hoff hβ hcontId hcallBlock hblocks
          (j := bi) (k := 0) (cur := site) hsite rfl rfl
          (hframe.setMany vals) hoffCaller hsiteMem)
      · have htb' := inlineCallerBlock_get_other₂ (f := fcur) (f' := f')
          (callBlock := callBlock) (mid :=
            g.blocks.map (inlineReplayBlock ρ β contId)) (tail := #[cont]) htb he hblocks
        refine ExecN.branchTrue (et := et) (ef := ef) (v := v) (args := vals)
          (by rw [hframe c hcLt]; exact hc) hv htb'
          (by rw [← hframe.getMany hargs]; exact hget) hplen ?_
        simpa [inlineCallerRest, he] using
          (ih hsite hoff hβ hcontId hcallBlock hblocks
          (j := et.target) (k := 0) (cur := tb) htb rfl rfl
          (hframe.setMany vals) hoffCaller hsiteMem)
  | @branchFalse n fcur R st c et ef tb vals res hc htb hget hplen htail ih =>
      have hbefore : ¬ (j = bi ∧ k ≤ ci) := by
        rintro ⟨rfl, hk⟩
        have hcureq : cur = site := Option.some.inj (hcur.symm.trans hsite)
        subst cur
        have hlenDrop := congrArg List.length hdrop
        simp at hlenDrop
        omega
      simp only [inlineCallerRest, if_neg hbefore]
      have hcLt : c < off := lt_of_le_of_lt
        (termUse_le_maxVal (block_mem_of_getElem? hcur) (by simp [hterm, Term.uses]))
        hoffCaller
      have hargs : ∀ x ∈ ef.args, x < off := by
        intro x hx
        exact lt_of_le_of_lt (termUse_le_maxVal (block_mem_of_getElem? hcur)
          (by simp [hterm, Term.uses, hx])) hoffCaller
      by_cases he : ef.target = bi
      · have htbSite : fcur.blocks[bi]? = some tb := by simpa [he] using htb
        have htbeq : tb = site := Option.some.inj (htbSite.symm.trans hsite)
        subst tb
        have htb' : f'.blocks[ef.target]? = some callBlock := by
          rw [he]
          exact inlineCallerBlock_get_site₂ (f := fcur) (f' := f')
            (mid := g.blocks.map (inlineReplayBlock ρ β contId)) (tail := #[cont])
            (Array.getElem?_eq_some_iff.mp hsite).1 hblocks
        rw [hcallBlock] at htb'
        refine ExecN.branchFalse (et := et) (ef := ef) (args := vals)
          (by rw [hframe c hcLt]; exact hc) htb'
          (by rw [← hframe.getMany hargs]; exact hget)
          (by simpa [hcallBlock] using hplen) ?_
        simpa [inlineCallerRest, hcallBlock] using
          (ih hsite hoff hβ hcontId hcallBlock hblocks
          (j := bi) (k := 0) (cur := site) hsite rfl rfl
          (hframe.setMany vals) hoffCaller hsiteMem)
      · have htb' := inlineCallerBlock_get_other₂ (f := fcur) (f' := f')
          (callBlock := callBlock) (mid :=
            g.blocks.map (inlineReplayBlock ρ β contId)) (tail := #[cont]) htb he hblocks
        refine ExecN.branchFalse (et := et) (ef := ef) (args := vals)
          (by rw [hframe c hcLt]; exact hc) htb'
          (by rw [← hframe.getMany hargs]; exact hget) hplen ?_
        simpa [inlineCallerRest, he] using
          (ih hsite hoff hβ hcontId hcallBlock hblocks
          (j := ef.target) (k := 0) (cur := tb) htb rfl rfl
          (hframe.setMany vals) hoffCaller hsiteMem)
  | @ret n fcur R st xs vals hget =>
      have hbefore : ¬ (j = bi ∧ k ≤ ci) := by
        rintro ⟨rfl, hk⟩
        have hcureq : cur = site := Option.some.inj (hcur.symm.trans hsite)
        subst cur
        have hlenDrop := congrArg List.length hdrop
        simp at hlenDrop
        omega
      simp only [inlineCallerRest, if_neg hbefore]
      have hxs : ∀ x ∈ xs, x < off := by
        intro x hx
        exact lt_of_le_of_lt (termUse_le_maxVal (block_mem_of_getElem? hcur)
          (by simpa [hterm, Term.uses] using hx)) hoffCaller
      exact ExecN.ret (by rw [← hframe.getMany hxs]; exact hget)
  | @halt n fcur R st st' yop oas oargs hget hop =>
      have hbefore : ¬ (j = bi ∧ k ≤ ci) := by
        rintro ⟨rfl, hk⟩
        have hcureq : cur = site := Option.some.inj (hcur.symm.trans hsite)
        subst cur
        have hlenDrop := congrArg List.length hdrop
        simp at hlenDrop
        omega
      simp only [inlineCallerRest, if_neg hbefore]
      have hoas : ∀ x ∈ oas, x < off := by
        intro x hx
        exact lt_of_le_of_lt (termUse_le_maxVal (block_mem_of_getElem? hcur)
          (by simpa [hterm, Term.uses] using hx)) hoffCaller
      exact ExecN.halt (args := oargs) (by rw [← hframe.getMany hoas]; exact hget) hop


/-- One splice preserves an existing call-depth bound. -/
theorem inlineOnce_soundN {P : Prog} {n : Nat} {counts : Array Nat} {f f' : Func} {args : List U256}
    {st : EvmState} {res : FRes} {eb eb' : Block}
    (hPwf : P.wfCheck = true)
    (hio : Passes.inlineOnce counts P.funcs f = some f')
    (heb : f.blocks[f.entry]? = some eb)
    (heb' : f'.blocks[f'.entry]? = some eb')
    (hexec : ExecN (model := model) P n f (Regs.empty.setMany f.params args) st
      ⟨eb.instrs, eb.term⟩ res) :
    ExecN (model := model) P n f' (Regs.empty.setMany f'.params args) st
      ⟨eb'.instrs, eb'.term⟩ res := by
  obtain ⟨bi, site, ci, ds, fid, as, g, hbi, hsite, hci, hcall, hfunc,
    -, hlen, hnrets, hentry, hf'⟩ := Passes.inlineOnce_inv hio
  let off := Nat.max (Passes.maxVal f) (Passes.maxVal g) + 1
  let ρ : ValId → ValId := fun v =>
    match (g.params.zip as).find? (fun pa => pa.1 == v) with
    | some pa => pa.2
    | none => v + off
  let β := fun i : BlockId => f.blocks.size + i
  let contId := f.blocks.size + g.blocks.size
  let callBlock : Block :=
    { params := site.params, instrs := site.instrs.take ci,
      term := .jump ⟨f.blocks.size + g.entry, []⟩ }
  let cont : Block :=
    { params := ds, instrs := site.instrs.drop (ci + 1), term := site.term }
  have hreplayFn :
      (fun gb : Block =>
        { params := gb.params.map ρ
          instrs := gb.instrs.map (Passes.renameInstr ρ)
          term := match gb.term with
            | .ret vs => .jump ⟨contId, vs.map ρ⟩
            | t => Passes.renameTerm ρ β t }) =
        Passes.inlineReplayBlock ρ β contId := by
    funext gb
    cases gb with
    | mk params instrs term => cases term <;> rfl
  have hfshapeRaw : f' =
      { f with blocks := (f.blocks.set! bi callBlock) ++
        g.blocks.map (fun gb =>
          { params := gb.params.map ρ
            instrs := gb.instrs.map (Passes.renameInstr ρ)
            term := match gb.term with
              | .ret vs => .jump ⟨contId, vs.map ρ⟩
              | t => Passes.renameTerm ρ β t }) ++ #[cont] } := by
    simpa [off, ρ, β, contId, callBlock, cont] using hf'
  have hfshape : f' =
      { f with blocks := (f.blocks.set! bi callBlock) ++
        g.blocks.map (Passes.inlineReplayBlock ρ β contId) ++ #[cont] } := by
    rw [hfshapeRaw, hreplayFn]
  have hblocks : f'.blocks = (f.blocks.set! bi callBlock) ++
      g.blocks.map (Passes.inlineReplayBlock ρ β contId) ++ #[cont] := by
    rw [hfshape]
  have hparams : f'.params = f.params := by rw [hfshape]
  have hentry' : f'.entry = f.entry := by rw [hfshape]
  have hstart :
      Passes.inlineCallerRest bi ci (f.blocks.size + g.entry) f.entry 0 site
          ⟨eb.instrs, eb.term⟩ = ⟨eb'.instrs, eb'.term⟩ := by
    by_cases he : f.entry = bi
    · have hebsite : eb = site := by
        rw [he] at heb
        exact Option.some.inj (heb.symm.trans hsite)
      subst eb
      have heb'call : eb' = callBlock := by
        have hout : f'.blocks[f'.entry]? = some callBlock := by
          rw [hentry', he]
          exact Passes.inlineCallerBlock_get_site₂ (f := f) (f' := f')
            (mid := g.blocks.map (Passes.inlineReplayBlock ρ β contId))
            (tail := #[cont]) hbi hblocks
        exact Option.some.inj (heb'.symm.trans hout)
      subst eb'
      simp [Passes.inlineCallerRest, he, callBlock]
    · have hout : f'.blocks[f'.entry]? = some eb := by
        rw [hentry']
        exact Passes.inlineCallerBlock_get_other₂ (f := f) (f' := f')
          (callBlock := callBlock)
          (mid := g.blocks.map (Passes.inlineReplayBlock ρ β contId))
          (tail := #[cont]) heb he hblocks
      have hebeq : eb' = eb := Option.some.inj (heb'.symm.trans hout)
      subst eb'
      simp [Passes.inlineCallerRest, he]
  have hgwf := progWf_func hPwf hfunc
  have hsim := Passes.inlineCaller_execN (model := model)
    (f' := f') (bi := bi) (ci := ci) (site := site) (ds := ds) (as := as)
    (fid := fid) (off := off) (contId := contId) (ρ := ρ) (β := β)
    (cont := cont) (callBlock := callBlock)
    hsite hci hcall hfunc hgwf rfl rfl (fun _ => rfl) rfl hentry hlen hnrets
    rfl rfl hblocks hexec (j := f.entry) (k := 0) (cur := eb)
    heb rfl rfl (fun _ _ => rfl)
  rw [hstart] at hsim
  simpa [hparams] using hsim

/-- Pure iteration model for `inlineFunc`.  Repeating an unsuccessful step is
the identity, so it is equivalent to the implementation's early return. -/
def Passes.inlineN (counts : Array Nat) (funcs : Array Func) : Nat → Func → Func
  | 0, f => f
  | n + 1, f =>
      match inlineOnce counts funcs f with
      | some f' => inlineN counts funcs n f'
      | none => f

def Passes.inlineFuncStep (counts : Array Nat) (funcs : Array Func)
    (_ : Nat) (f : Func) : ForInStep Func :=
  match inlineOnce counts funcs f with
  | some f' => .yield f'
  | none => .done f

def Passes.inlineFuncRawStep (counts : Array Nat) (funcs : Array Func)
    (_ : Nat) (s : MProd (Option Func) Func) : ForInStep (MProd (Option Func) Func) :=
  match inlineOnce counts funcs s.2 with
  | some f' => .yield ⟨none, f'⟩
  | none => .done ⟨some s.2, s.2⟩

omit model in
theorem Passes.inlineFuncRaw_loop (counts : Array Nat) (funcs : Array Func)
    (l : List Nat) (f : Func) :
    let r := loopWith (inlineFuncRawStep counts funcs) l ⟨none, f⟩
    r.1.getD r.2 = loopWith (inlineFuncStep counts funcs) l f := by
  induction l generalizing f with
  | nil => rfl
  | cons i is ih =>
      rw [loopWith_cons, loopWith_cons]
      cases hio : inlineOnce counts funcs f with
      | none => simp [inlineFuncRawStep, inlineFuncStep, hio]
      | some f' =>
          simp only [inlineFuncRawStep, inlineFuncStep, hio]
          exact ih f'

omit model in
theorem Passes.inlineFuncStep_loop (counts : Array Nat) (funcs : Array Func)
    (l : List Nat) (f : Func) :
    loopWith (inlineFuncStep counts funcs) l f = inlineN counts funcs l.length f := by
  induction l generalizing f with
  | nil => rfl
  | cons i is ih =>
      rw [loopWith_cons]
      cases hio : inlineOnce counts funcs f with
      | none => simp [inlineFuncStep, inlineN, hio]
      | some f' => simp [inlineFuncStep, inlineN, hio, ih]

omit model in
theorem Passes.inlineFunc_eq_inlineN (counts : Array Nat) (funcs : Array Func) (f : Func) :
    inlineFunc counts funcs f = inlineN counts funcs 8 f := by
  unfold inlineFunc
  dsimp only
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rw [Id.forIn_eq_loopWith (g := inlineFuncRawStep counts funcs) (h := by
    intro i s
    cases hio : inlineOnce counts funcs s.2 <;>
      simp [inlineFuncRawStep, hio])]
  simp only [Id.run, bind, pure]
  let l := List.range' 0 ((8 - 0 + 1 - 1) / 1) 1
  let r := loopWith (inlineFuncRawStep counts funcs) l ⟨none, f⟩
  change (match r.1 with | none => r.2 | some a => a) = _
  have hm : (match r.1 with | none => r.2 | some a => a) = r.1.getD r.2 := by
    cases r.1 <;> rfl
  rw [hm]
  have hr := inlineFuncRaw_loop counts funcs l f
  change r.1.getD r.2 = _ at hr
  rw [hr, inlineFuncStep_loop]
  rfl

omit model in
theorem Passes.inlineN_nrets (counts : Array Nat) (funcs : Array Func)
    (n : Nat) (f : Func) :
    (inlineN counts funcs n f).nrets = f.nrets := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
      cases hio : inlineOnce counts funcs f with
      | none => simp [inlineN, hio]
      | some f' =>
          simpa [inlineN, hio, inlineOnce_nrets hio] using ih f'

omit model in
theorem Passes.inlineN_wf (counts : Array Nat) (funcs : Array Func)
    {nFuncs : Nat}
    (hfuncs : ∀ {fid : FuncId} {g : Func},
      funcs[fid]? = some g → g.wfCheck nFuncs = true) :
    ∀ (n : Nat) (f : Func), f.wfCheck nFuncs = true →
      (inlineN counts funcs n f).wfCheck nFuncs = true := by
  intro n
  induction n with
  | zero => intro f hfwf; exact hfwf
  | succ n ih =>
      intro f hfwf
      cases hio : inlineOnce counts funcs f with
      | none => simpa [inlineN, hio] using hfwf
      | some f' =>
          simpa [inlineN, hio] using ih f' (inlineOnce_wf hfuncs hfwf hio)

omit model in
theorem Passes.inlineFunc_wf (counts : Array Nat) (funcs : Array Func)
    {f : Func} {nFuncs : Nat}
    (hfuncs : ∀ {fid : FuncId} {g : Func},
      funcs[fid]? = some g → g.wfCheck nFuncs = true)
    (hfwf : f.wfCheck nFuncs = true) :
    (inlineFunc counts funcs f).wfCheck nFuncs = true := by
  rw [inlineFunc_eq_inlineN]
  exact inlineN_wf counts funcs hfuncs 8 f hfwf

omit model in
theorem Passes.inlineFunc_nrets (counts : Array Nat) (funcs : Array Func)
    (f : Func) : (inlineFunc counts funcs f).nrets = f.nrets := by
  rw [inlineFunc_eq_inlineN]
  exact inlineN_nrets counts funcs 8 f

omit model in
/-- A successful splice preserves the existence of the caller entry block. -/
theorem Passes.inlineOnce_entry {counts : Array Nat} {funcs : Array Func}
    {f f' : Func} {eb : Block} (hio : inlineOnce counts funcs f = some f')
    (heb : f.blocks[f.entry]? = some eb) :
    ∃ eb', f'.blocks[f'.entry]? = some eb' := by
  obtain ⟨bi, site, ci, ds, fid, as, g, hbi, hsite, hci, hcall, hfunc,
    hcount, hlen, hnrets, hentry, hf'⟩ := inlineOnce_inv hio
  have hlt : f.entry < f.blocks.size := (Array.getElem?_eq_some_iff.mp heb).1
  have hsetSize :
      (f.blocks.set! bi
        { params := site.params, instrs := site.instrs.take ci,
          term := .jump ⟨f.blocks.size + g.entry, []⟩ }).size = f.blocks.size := by
    simp
  have hentryEq : f'.entry = f.entry := by rw [hf']
  have hlt' : f'.entry < f'.blocks.size := by
    rw [hentryEq]
    apply lt_of_lt_of_le hlt
    rw [hf']
    apply le_trans (le_of_eq hsetSize.symm)
    simp
  refine ⟨f'.blocks[f'.entry], ?_⟩
  exact Array.getElem?_eq_getElem hlt'

omit model in
theorem Passes.inlineOnce_params_entry {counts : Array Nat} {funcs : Array Func}
    {f f' : Func} (hio : inlineOnce counts funcs f = some f') :
    f'.params = f.params ∧ f'.entry = f.entry := by
  obtain ⟨bi, site, ci, ds, fid, as, g, hbi, hsite, hci, hcall, hfunc,
    hcount, hlen, hnrets, hentry, hf'⟩ := inlineOnce_inv hio
  rw [hf']
  exact ⟨rfl, rfl⟩

omit model in
theorem Passes.inlineN_params_entry (counts : Array Nat) (funcs : Array Func)
    (n : Nat) (f : Func) :
    (inlineN counts funcs n f).params = f.params ∧
      (inlineN counts funcs n f).entry = f.entry := by
  induction n generalizing f with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
      cases hio : inlineOnce counts funcs f with
      | none => simp [inlineN, hio]
      | some f' =>
          have hs := inlineOnce_params_entry hio
          have hi := ih f'
          simpa [inlineN, hio, hs.1, hs.2] using hi

/-- Iterated local inlining preserves the same call-depth bound. -/
theorem Passes.inlineN_soundN {P : Prog} {depth : Nat} {counts : Array Nat}
    (hPwf : P.wfCheck = true) :
    ∀ (n : Nat) (f : Func) (args : List U256) (st : EvmState) (res : FRes)
      (eb eb' : Block),
      f.blocks[f.entry]? = some eb →
      (inlineN counts P.funcs n f).blocks[(inlineN counts P.funcs n f).entry]? = some eb' →
      ExecN (model := model) P depth f (Regs.empty.setMany f.params args) st
        ⟨eb.instrs, eb.term⟩ res →
      ExecN (model := model) P depth (inlineN counts P.funcs n f)
        (Regs.empty.setMany (inlineN counts P.funcs n f).params args) st
        ⟨eb'.instrs, eb'.term⟩ res := by
  intro n
  induction n with
  | zero =>
      intro f args st res eb eb' heb heb' hexec
      simp only [inlineN] at heb' ⊢
      have heq : eb' = eb := Option.some.inj (heb'.symm.trans heb)
      subst eb'
      exact hexec
  | succ n ih =>
      intro f args st res eb eb' heb heb' hexec
      cases hio : inlineOnce counts P.funcs f with
      | none =>
          simp only [inlineN, hio] at heb' ⊢
          have heq : eb' = eb := Option.some.inj (heb'.symm.trans heb)
          subst eb'
          exact hexec
      | some f' =>
          obtain ⟨e', he'⟩ := inlineOnce_entry hio heb
          have hexec' := inlineOnce_soundN (model := model) hPwf hio heb he' hexec
          have heb'' :
              (inlineN counts P.funcs n f').blocks[
                (inlineN counts P.funcs n f').entry]? = some eb' := by
            simpa only [inlineN, hio, Option.getD_some] using heb'
          simpa only [inlineN, hio] using
            (ih f' args st res e' eb' he' heb'' hexec')

/-- The production local inliner preserves the same call-depth bound. -/
theorem inlineFunc_soundN {P : Prog} {depth : Nat} {counts : Array Nat} {f : Func} {args : List U256}
    {st : EvmState} {res : FRes} {eb eb' : Block}
    (hPwf : P.wfCheck = true) (_hwf : f.wfCheck P.funcs.size = true)
    (heb : f.blocks[f.entry]? = some eb)
    (heb' : (Passes.inlineFunc counts P.funcs f).blocks[f.entry]? = some eb')
    (hexec : ExecN (model := model) P depth f (Regs.empty.setMany f.params args) st
      ⟨eb.instrs, eb.term⟩ res) :
    ExecN (model := model) P depth (Passes.inlineFunc counts P.funcs f)
      (Regs.empty.setMany f.params args) st ⟨eb'.instrs, eb'.term⟩ res := by
  have hpe := Passes.inlineN_params_entry counts P.funcs 8 f
  have heb'' :
      (Passes.inlineN counts P.funcs 8 f).blocks[
        (Passes.inlineN counts P.funcs 8 f).entry]? = some eb' := by
    rw [hpe.2]
    simpa only [Passes.inlineFunc_eq_inlineN] using heb'
  have hs := Passes.inlineN_soundN (model := model) (counts := counts) hPwf
    8 f args st res eb eb' heb heb'' hexec
  simpa only [Passes.inlineFunc_eq_inlineN, hpe.1] using hs

/-- The unpruned program produced by one inlining round. -/
def Passes.inlineMap (counts : Array Nat) (P : Prog) : Prog :=
  { main := inlineFunc counts P.funcs P.main
    funcs := P.funcs.map (inlineFunc counts P.funcs) }

omit model in
theorem Passes.inlineMap_lookup {counts : Array Nat} {P : Prog}
    {fid : FuncId} {g : Func} (h : P.funcs[fid]? = some g) :
    (inlineMap counts P).funcs[fid]? = some (inlineFunc counts P.funcs g) := by
  simp [inlineMap, h]

omit model in
theorem Passes.inlineMap_wf {counts : Array Nat} {P : Prog}
    (hPwf : P.wfCheck = true) : (inlineMap counts P).wfCheck = true := by
  have hparts := hPwf
  simp only [Prog.wfCheck, Bool.and_eq_true] at hparts ⊢
  have hcallees : ∀ {fid : FuncId} {g : Func},
      P.funcs[fid]? = some g → g.wfCheck P.funcs.size = true := by
    intro fid g hget
    exact progWf_func hPwf hget
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · have hp := inlineN_params_entry counts P.funcs 8 P.main
    simpa [inlineMap, inlineFunc_eq_inlineN, hp.1] using hparts.1.1.1
  · simpa [inlineMap, inlineFunc_nrets] using hparts.1.1.2
  · simpa [inlineMap] using
      (inlineFunc_wf counts P.funcs hcallees hparts.1.2)
  · rw [Array.all_eq_true]
    intro i hi
    have hi' : i < P.funcs.size := by simpa [inlineMap] using hi
    have hfi : P.funcs[i].wfCheck P.funcs.size = true := by
      rw [Array.all_eq_true] at hparts
      exact hparts.2 i hi'
    simpa [inlineMap] using inlineFunc_wf counts P.funcs hcallees hfi

omit model in
/-- Iteration preserves existence of a function's entry block. -/
theorem Passes.inlineN_entry {counts : Array Nat} {funcs : Array Func} :
    ∀ (k : Nat) (f : Func) {eb : Block}, f.blocks[f.entry]? = some eb →
      ∃ eb', (inlineN counts funcs k f).blocks[(inlineN counts funcs k f).entry]? =
        some eb' := by
  intro k
  induction k with
  | zero =>
      intro f eb heb
      exact ⟨eb, heb⟩
  | succ k ih =>
      intro f eb heb
      cases hio : inlineOnce counts funcs f with
      | none =>
          exact ⟨eb, by simpa [inlineN, hio] using heb⟩
      | some f' =>
          obtain ⟨eb', heb'⟩ := inlineOnce_entry hio heb
          simpa [inlineN, hio] using ih f' heb'

omit model in
theorem Passes.inlineFunc_entry {counts : Array Nat} {funcs : Array Func}
    {f : Func} {eb : Block} (heb : f.blocks[f.entry]? = some eb) :
    ∃ eb', (inlineFunc counts funcs f).blocks[(inlineFunc counts funcs f).entry]? =
      some eb' := by
  rw [inlineFunc_eq_inlineN]
  exact inlineN_entry 8 f heb

/-- Change the ambient program from `P` to its one-round function map while
leaving the currently executing function text fixed.  At a call, the callee
is first locally inlined under `P`; the outer strong induction then changes
the ambient program for that new callee at the strictly smaller body bound.
The caller continuation is handled by the structural induction hypothesis. -/
theorem Passes.inlineMap_execN {P : Prog} {counts : Array Nat}
    (hPwf : P.wfCheck = true) :
    ∀ (n : Nat) (f : Func) (R : Regs) (st : EvmState) (rest : Rest) (res : FRes),
      ExecN (model := model) P n f R st rest res →
      ExecN (model := model) (inlineMap counts P) n f R st rest res := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n hdepth =>
      intro f R st rest res hexec
      induction hexec with
      | const htail ih => exact ExecN.const (ih hdepth)
      | op hget hop hlen htail ih => exact ExecN.op hget hop hlen (ih hdepth)
      | opHalt hget hop => exact ExecN.opHalt hget hop
      | @call k f g R st st' ds as fid args rvals eb is t res
          hfid hget hplen heb hbody hlen htail ihbody ih =>
          obtain ⟨eb', heb'⟩ := inlineFunc_entry
            (counts := counts) (funcs := P.funcs) heb
          have hpe := inlineN_params_entry counts P.funcs 8 g
          have heb'' : (inlineFunc counts P.funcs g).blocks[g.entry]? = some eb' := by
            simpa only [inlineFunc_eq_inlineN, hpe.2] using heb'
          have hbodyLocal := inlineFunc_soundN (model := model)
            (depth := k) (counts := counts) hPwf (progWf_func hPwf hfid)
            heb heb'' hbody
          have hbodyLocal' : ExecN (model := model) P k
              (inlineFunc counts P.funcs g)
              (Regs.empty.setMany (inlineFunc counts P.funcs g).params args)
              st ⟨eb'.instrs, eb'.term⟩ (.ret rvals st') := by
            simpa only [inlineFunc_eq_inlineN, hpe.1] using hbodyLocal
          have hbodyMap := hdepth k (by omega)
            (inlineFunc counts P.funcs g)
            (Regs.empty.setMany (inlineFunc counts P.funcs g).params args)
            st ⟨eb'.instrs, eb'.term⟩ (.ret rvals st') hbodyLocal'
          refine ExecN.call (g := inlineFunc counts P.funcs g) (eb := eb')
            (inlineMap_lookup hfid) hget ?_ heb' hbodyMap hlen (ih hdepth)
          simpa only [inlineFunc_eq_inlineN, hpe.1] using hplen
      | @callHalt k f g R st st' ds as fid args eb is t
          hfid hget hplen heb hbody ihbody =>
          obtain ⟨eb', heb'⟩ := inlineFunc_entry
            (counts := counts) (funcs := P.funcs) heb
          have hpe := inlineN_params_entry counts P.funcs 8 g
          have heb'' : (inlineFunc counts P.funcs g).blocks[g.entry]? = some eb' := by
            simpa only [inlineFunc_eq_inlineN, hpe.2] using heb'
          have hbodyLocal := inlineFunc_soundN (model := model)
            (depth := k) (counts := counts) hPwf (progWf_func hPwf hfid)
            heb heb'' hbody
          have hbodyLocal' : ExecN (model := model) P k
              (inlineFunc counts P.funcs g)
              (Regs.empty.setMany (inlineFunc counts P.funcs g).params args)
              st ⟨eb'.instrs, eb'.term⟩ (.halt st') := by
            simpa only [inlineFunc_eq_inlineN, hpe.1] using hbodyLocal
          have hbodyMap := hdepth k (by omega)
            (inlineFunc counts P.funcs g)
            (Regs.empty.setMany (inlineFunc counts P.funcs g).params args)
            st ⟨eb'.instrs, eb'.term⟩ (.halt st') hbodyLocal'
          refine ExecN.callHalt (g := inlineFunc counts P.funcs g) (eb := eb')
            (inlineMap_lookup hfid) hget ?_ heb' hbodyMap
          simpa only [inlineFunc_eq_inlineN, hpe.1] using hplen
      | jump htb hget hplen htail ih => exact ExecN.jump htb hget hplen (ih hdepth)
      | branchTrue hc hv htb hget hplen htail ih =>
          exact ExecN.branchTrue hc hv htb hget hplen (ih hdepth)
      | branchFalse hc htb hget hplen htail ih =>
          exact ExecN.branchFalse hc htb hget hplen (ih hdepth)
      | ret hget => exact ExecN.ret hget
      | halt hget hop => exact ExecN.halt hget hop

/-- One unpruned whole-program inlining map preserves a run. -/
theorem Passes.inlineMap_sound {P : Prog} {counts : Array Nat}
    {yst0 yst' : EvmState} {o : Outcome} (hPwf : P.wfCheck = true)
    (hrun : Run (model := model) P yst0 yst' o) :
    Run (model := model) (inlineMap counts P) yst0 yst' o := by
  have hPwf' := hPwf
  simp only [Prog.wfCheck, Bool.and_eq_true] at hPwf'
  have hmainWf : P.main.wfCheck P.funcs.size = true := by
    exact hPwf'.1.2
  have hmainParams : P.main.params = [] := by
    exact List.isEmpty_iff.mp hPwf'.1.1.1
  cases hrun with
  | normal heb hexec =>
      rename_i eb
      obtain ⟨n, hexecN⟩ := hexec.toExecN
      obtain ⟨eb', heb'⟩ := inlineFunc_entry
        (counts := counts) (funcs := P.funcs) heb
      have hpe := inlineN_params_entry counts P.funcs 8 P.main
      have heb'' : (inlineFunc counts P.funcs P.main).blocks[P.main.entry]? =
          some eb' := by
        simpa only [inlineFunc_eq_inlineN, hpe.2] using heb'
      have hlocal := inlineFunc_soundN (model := model) (depth := n)
        (counts := counts) (args := []) hPwf hmainWf heb heb''
        (by simpa [hmainParams, Regs.setMany_nil_left] using hexecN)
      have hlocal' : ExecN (model := model) P n
          (inlineFunc counts P.funcs P.main) Regs.empty yst0
          ⟨eb'.instrs, eb'.term⟩ (.ret [] yst') := by
        simpa only [inlineFunc_eq_inlineN, hpe.1, hmainParams,
          Regs.setMany_nil_left] using hlocal
      have hmapped := inlineMap_execN (model := model) (counts := counts)
        hPwf n (inlineFunc counts P.funcs P.main) Regs.empty yst0
        ⟨eb'.instrs, eb'.term⟩ (.ret [] yst') hlocal'
      exact Run.normal (by simpa [inlineMap] using heb') hmapped.toExec
  | halt heb hexec =>
      rename_i eb
      obtain ⟨n, hexecN⟩ := hexec.toExecN
      obtain ⟨eb', heb'⟩ := inlineFunc_entry
        (counts := counts) (funcs := P.funcs) heb
      have hpe := inlineN_params_entry counts P.funcs 8 P.main
      have heb'' : (inlineFunc counts P.funcs P.main).blocks[P.main.entry]? =
          some eb' := by
        simpa only [inlineFunc_eq_inlineN, hpe.2] using heb'
      have hlocal := inlineFunc_soundN (model := model) (depth := n)
        (counts := counts) (args := []) hPwf hmainWf heb heb''
        (by simpa [hmainParams, Regs.setMany_nil_left] using hexecN)
      have hlocal' : ExecN (model := model) P n
          (inlineFunc counts P.funcs P.main) Regs.empty yst0
          ⟨eb'.instrs, eb'.term⟩ (.halt yst') := by
        simpa only [inlineFunc_eq_inlineN, hpe.1, hmainParams,
          Regs.setMany_nil_left] using hlocal
      have hmapped := inlineMap_execN (model := model) (counts := counts)
        hPwf n (inlineFunc counts P.funcs P.main) Regs.empty yst0
        ⟨eb'.instrs, eb'.term⟩ (.halt yst') hlocal'
      exact Run.halt (by simpa [inlineMap] using heb') hmapped.toExec

/-! ### Function pruning: pure models of the mutable loops -/

def Passes.pruneCallees (f : Func) : List FuncId :=
  f.blocks.toList.flatMap fun b =>
    b.instrs.filterMap fun i => match i with | .call _ fid _ => some fid | _ => none

def Passes.pruneWorkOne (P : Prog) (n : Nat) (fid : FuncId)
    (s : MProd (List FuncId) (Array Bool)) : MProd (List FuncId) (Array Bool) :=
  if _h : fid < n then
    if !s.2[fid]! then
      ⟨s.1 ++ (P.funcs[fid]?.map pruneCallees).getD [], s.2.set! fid true⟩
    else s
  else s

def Passes.pruneRound (P : Prog) (n : Nat) (_ : Nat)
    (s : MProd (Array Bool) (List FuncId)) : ForInStep (MProd (Array Bool) (List FuncId)) :=
  let r := s.2.foldl (fun r fid => pruneWorkOne P n fid r) ⟨[], s.1⟩
  let out := ⟨r.2, r.1⟩
  if r.1.isEmpty then .done out else .yield out

def Passes.pruneState (P : Prog) : MProd (Array Bool) (List FuncId) :=
  loopWith (pruneRound P P.funcs.size)
    (List.range' 0 (P.funcs.size + 1) 1)
    ⟨Array.replicate P.funcs.size false,
      P.main.blocks.toList.flatMap fun b =>
        b.instrs.filterMap fun i =>
          match i with | .call _ fid _ => some fid | _ => none⟩

def Passes.pruneKeepOne (P : Prog) (used : Array Bool) (fid : FuncId)
    (s : MProd (Array Func) (Array (Option FuncId))) :
    MProd (Array Func) (Array (Option FuncId)) :=
  if used[fid]! then
    ⟨s.1.push P.funcs[fid]!, s.2.set! fid (some s.1.size)⟩
  else s

def Passes.pruneKeep (P : Prog) (used : Array Bool) :
    MProd (Array Func) (Array (Option FuncId)) :=
  (List.range' 0 P.funcs.size 1).foldl
    (fun s fid => pruneKeepOne P used fid s)
    ⟨#[], Array.replicate P.funcs.size none⟩

def Passes.pruneInstr (remap : Array (Option FuncId)) : Instr → Instr
  | .call ds fid as => .call ds ((remap[fid]?.join).getD fid) as
  | i => i

def Passes.pruneBlock (remap : Array (Option FuncId)) (b : Block) : Block :=
  { b with instrs := b.instrs.map (pruneInstr remap) }

def Passes.pruneFix (remap : Array (Option FuncId)) (f : Func) : Func :=
  { f with blocks := f.blocks.map (pruneBlock remap) }

def Passes.pruneModel (P : Prog) : Prog :=
  let used := (pruneState P).1
  if used.all id then P
  else
    let kept := (pruneKeep P used).1
    let remap := (pruneKeep P used).2
    { main := pruneFix remap P.main, funcs := kept.map (pruneFix remap) }

omit model in
theorem Passes.pruneFuncs_eq_model (P : Prog) : pruneFuncs P = pruneModel P := by
  unfold pruneFuncs pruneModel pruneState
  dsimp only
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rw [Id.forIn_eq_loopWith (g := pruneRound P P.funcs.size) (h := by
    intro i s
    rw [Id.forIn_eq_foldl (g := pruneWorkOne P P.funcs.size) (h := by
      intro fid r
      simp only [pruneWorkOne]
      split <;> rename_i hlt
      · split <;> rfl
      · rfl)]
    simp only [pruneRound]
    rfl)]
  simp only [Id.run, bind, pure]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [Id.forIn_eq_foldl (g := pruneKeepOne P (pruneState P).1) (h := by
    intro fid r
    simp only [pruneState, pruneKeepOne]
    split <;> rename_i hc
    · change ForInStep.yield _ = ForInStep.yield _
      congr 1
      exact (if_pos hc).symm
    · change ForInStep.yield _ = ForInStep.yield _
      congr 1
      exact (if_neg hc).symm)]
  rfl

omit model in
theorem Passes.mem_pruneCallees {f : Func} {fid : FuncId} :
    fid ∈ pruneCallees f ↔
      ∃ b ∈ f.blocks.toList, ∃ ds as, Instr.call ds fid as ∈ b.instrs := by
  simp only [pruneCallees, List.mem_flatMap, List.mem_filterMap]
  constructor
  · rintro ⟨b, hb, i, hi, hcall⟩
    cases i with
    | const => simp at hcall
    | op => simp at hcall
    | call ds fid' as =>
        simp only at hcall
        obtain rfl := Option.some.inj hcall
        exact ⟨b, hb, ds, as, hi⟩
  · rintro ⟨b, hb, ds, as, hi⟩
    exact ⟨b, hb, .call ds fid as, hi, rfl⟩

omit model in
theorem Passes.wfCheck_callee_lt {f : Func} {n fid : Nat}
    (hwf : f.wfCheck n = true) (hfid : fid ∈ pruneCallees f) : fid < n := by
  obtain ⟨b, hb, ds, as, hi⟩ := mem_pruneCallees.mp hfid
  unfold Func.wfCheck at hwf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hwf
  have hblock := Array.all_eq_true_iff_forall_mem.mp hwf.2 b (by simpa using hb)
  simp only [Bool.and_eq_true] at hblock
  have hins := List.all_eq_true.mp hblock.2 (.call ds fid as) hi
  simpa using hins

def Passes.MarkSub (A B : Array Bool) : Prop :=
  ∀ (i : Nat), A[i]? = some true → B[i]? = some true

def Passes.UsedAt (A : Array Bool) (i : FuncId) : Prop := A[i]? = some true

omit model in
theorem Passes.markSub_refl (A : Array Bool) : MarkSub A A := fun _ h => h

omit model in
theorem Passes.markSub_trans {A B C : Array Bool} (hAB : MarkSub A B)
    (hBC : MarkSub B C) : MarkSub A C := fun i hi => hBC i (hAB i hi)

omit model in
theorem Passes.pruneWorkOne_size (P : Prog) (n fid : Nat)
    (s : MProd (List FuncId) (Array Bool)) :
    (pruneWorkOne P n fid s).2.size = s.2.size := by
  simp only [pruneWorkOne]
  split
  · split <;> simp
  · rfl

omit model in
theorem Passes.pruneWorkOne_mono (P : Prog) (n fid : Nat)
    (s : MProd (List FuncId) (Array Bool)) :
    MarkSub s.2 (pruneWorkOne P n fid s).2 := by
  intro i hi
  simp only [pruneWorkOne]
  split
  · rename_i hfid
    split
    · by_cases h : fid = i
      · subst i
        have hin : fid < s.2.size := (Array.getElem?_eq_some_iff.mp hi).1
        simp [Array.set!, hin]
      · simpa [Array.set!, Array.getElem?_setIfInBounds_ne h] using hi
    · exact hi
  · exact hi

omit model in
theorem Passes.pruneWorkOne_marks (P : Prog) {n fid : Nat}
    (s : MProd (List FuncId) (Array Bool)) (hfid : fid < n)
    (hsz : s.2.size = n) :
    UsedAt (pruneWorkOne P n fid s).2 fid := by
  simp only [UsedAt, pruneWorkOne, hfid, dite_true]
  split
  · simp [Array.set!, hsz, hfid]
  · rename_i hn
    have hu : s.2[fid]! = true := by
      cases h : s.2[fid]! <;> simp_all
    have hin : fid < s.2.size := by omega
    rw [Array.getElem?_eq_getElem hin]
    simpa [Array.getElem!_eq_getD, Array.getD, hin] using hu

omit model in
theorem Passes.pruneWorkOne_new_origin (P : Prog) {n fid j : Nat}
    (s : MProd (List FuncId) (Array Bool))
    (hj : UsedAt (pruneWorkOne P n fid s).2 j) (hnot : ¬ UsedAt s.2 j) :
    j = fid := by
  simp only [UsedAt, pruneWorkOne] at hj
  split at hj
  · rename_i hfid
    split at hj
    · by_contra hne
      apply hnot
      unfold UsedAt
      simpa [Array.set!, Array.getElem?_setIfInBounds_ne (Ne.symm hne)] using hj
    · exact absurd hj (by simpa [UsedAt] using hnot)
  · exact absurd hj (by simpa [UsedAt] using hnot)

omit model in
theorem Passes.pruneWorkOne_emits (P : Prog) {n fid : Nat}
    (s : MProd (List FuncId) (Array Bool)) (hfid : fid < n)
    (hsz : s.2.size = n)
    (hnot : ¬ UsedAt s.2 fid) {g : Func} (hg : P.funcs[fid]? = some g)
    {callee : FuncId} (hc : callee ∈ pruneCallees g) :
    callee ∈ (pruneWorkOne P n fid s).1 := by
  have hfalse : s.2[fid]! = false := by
    by_contra ht
    have ht' : s.2[fid]! = true := Bool.eq_true_of_not_eq_false ht
    apply hnot
    unfold UsedAt
    have hin : fid < s.2.size := by omega
    rw [Array.getElem?_eq_getElem hin]
    simpa [Array.getElem!_eq_getD, Array.getD, hin] using ht'
  simp only [pruneWorkOne, hfid, dite_true, hfalse,
    Bool.not_false, if_true]
  apply List.mem_append_right
  rw [hg]
  simpa using hc

def Passes.pruneWorkFrom (P : Prog) (n : Nat) (work : List FuncId)
    (s : MProd (List FuncId) (Array Bool)) : MProd (List FuncId) (Array Bool) :=
  work.foldl (fun r fid => pruneWorkOne P n fid r) s

def Passes.pruneWork (P : Prog) (n : Nat) (work : List FuncId)
    (used : Array Bool) : MProd (List FuncId) (Array Bool) :=
  pruneWorkFrom P n work ⟨[], used⟩

omit model in
theorem Passes.pruneWorkFrom_size (P : Prog) (n : Nat) (work : List FuncId)
    (s : MProd (List FuncId) (Array Bool)) :
    (pruneWorkFrom P n work s).2.size = s.2.size := by
  induction work generalizing s with
  | nil => rfl
  | cons fid work ih =>
      simp only [pruneWorkFrom, List.foldl_cons]
      change (pruneWorkFrom P n work (pruneWorkOne P n fid s)).2.size = s.2.size
      rw [ih, pruneWorkOne_size]

omit model in
theorem Passes.pruneWorkFrom_mono (P : Prog) (n : Nat) (work : List FuncId)
    (s : MProd (List FuncId) (Array Bool)) :
    MarkSub s.2 (pruneWorkFrom P n work s).2 := by
  induction work generalizing s with
  | nil => exact markSub_refl s.2
  | cons fid work ih =>
      simp only [pruneWorkFrom, List.foldl_cons]
      exact markSub_trans (pruneWorkOne_mono P n fid s)
        (ih (pruneWorkOne P n fid s))

omit model in
theorem Passes.pruneWorkFrom_marks (P : Prog) {n : Nat} {work : List FuncId}
    {s : MProd (List FuncId) (Array Bool)} (hsz : s.2.size = n) {fid : FuncId}
    (hm : fid ∈ work) (hlt : fid < n) :
    UsedAt (pruneWorkFrom P n work s).2 fid := by
  induction work generalizing s with
  | nil => simp at hm
  | cons j work ih =>
      simp only [pruneWorkFrom, List.foldl_cons]
      rcases List.mem_cons.mp hm with rfl | hm
      · exact (pruneWorkFrom_mono P n work (pruneWorkOne P n fid s)) fid
          (pruneWorkOne_marks P s hlt hsz)
      · exact ih (s := pruneWorkOne P n j s)
          (by rw [pruneWorkOne_size, hsz]) hm

omit model in
theorem Passes.pruneWorkOne_next_mono (P : Prog) (n fid : Nat)
    (s : MProd (List FuncId) (Array Bool)) :
    ∀ x ∈ s.1, x ∈ (pruneWorkOne P n fid s).1 := by
  intro x hx
  simp only [pruneWorkOne]
  split
  · split
    · exact List.mem_append_left _ hx
    · exact hx
  · exact hx

omit model in
theorem Passes.pruneWorkFrom_next_mono (P : Prog) (n : Nat) (work : List FuncId)
    (s : MProd (List FuncId) (Array Bool)) :
    ∀ x ∈ s.1, x ∈ (pruneWorkFrom P n work s).1 := by
  induction work generalizing s with
  | nil => exact fun _ h => h
  | cons fid work ih =>
      intro x hx
      exact ih (pruneWorkOne P n fid s) x (pruneWorkOne_next_mono P n fid s x hx)

omit model in
theorem Passes.pruneWorkFrom_new_origin (P : Prog) {n : Nat}
    {work : List FuncId} {s : MProd (List FuncId) (Array Bool)} {j : FuncId}
    (hj : UsedAt (pruneWorkFrom P n work s).2 j) (hnot : ¬ UsedAt s.2 j) :
    j ∈ work := by
  induction work generalizing s with
  | nil => exact absurd hj hnot
  | cons fid work ih =>
      simp only [pruneWorkFrom, List.foldl_cons] at hj
      by_cases hm : UsedAt (pruneWorkOne P n fid s).2 j
      · exact List.mem_cons.mpr (Or.inl (pruneWorkOne_new_origin P s hm hnot))
      · exact List.mem_cons.mpr (Or.inr (ih (s := pruneWorkOne P n fid s) hj hm))

omit model in
theorem Passes.pruneWorkFrom_emits (P : Prog) {n : Nat}
    {work : List FuncId} {s : MProd (List FuncId) (Array Bool)}
    (hsz : s.2.size = n) {fid : FuncId} (hm : fid ∈ work) (hlt : fid < n)
    (hnot : ¬ UsedAt s.2 fid) {g : Func} (hg : P.funcs[fid]? = some g)
    {callee : FuncId} (hc : callee ∈ pruneCallees g) :
    callee ∈ (pruneWorkFrom P n work s).1 := by
  induction work generalizing s with
  | nil => simp at hm
  | cons j work ih =>
      simp only [pruneWorkFrom, List.foldl_cons]
      rcases List.mem_cons.mp hm with rfl | hm
      · exact pruneWorkFrom_next_mono P n work (pruneWorkOne P n fid s) callee
          (pruneWorkOne_emits P s hlt hsz hnot hg hc)
      · by_cases hj : UsedAt (pruneWorkOne P n j s).2 fid
        · have heq : fid = j := pruneWorkOne_new_origin P s hj hnot
          subst j
          exact pruneWorkFrom_next_mono P n work (pruneWorkOne P n fid s) callee
            (pruneWorkOne_emits P s hlt hsz hnot hg hc)
        · exact ih (s := pruneWorkOne P n j s)
            (by rw [pruneWorkOne_size, hsz]) hm hj

inductive Passes.PruneReach (P : Prog) : FuncId → Prop
  | main {fid : FuncId} : fid ∈ pruneCallees P.main → PruneReach P fid
  | step {src fid : FuncId} {f : Func} : PruneReach P src →
      P.funcs[src]? = some f → fid ∈ pruneCallees f → PruneReach P fid

def Passes.PruneOrigin (P : Prog)
    (s : MProd (List FuncId) (Array Bool)) : Prop :=
  (∀ fid, UsedAt s.2 fid → PruneReach P fid) ∧
  ∀ fid ∈ s.1, PruneReach P fid

omit model in
theorem Passes.pruneWorkOne_origin {P : Prog} {n fid : Nat}
    {s : MProd (List FuncId) (Array Bool)}
    (hfid : PruneReach P fid) (hs : PruneOrigin P s) :
    PruneOrigin P (pruneWorkOne P n fid s) := by
  constructor
  · intro j hj
    by_cases hold : UsedAt s.2 j
    · exact hs.1 j hold
    · have : j = fid := pruneWorkOne_new_origin P s hj hold
      simpa [this] using hfid
  · intro j hj
    simp only [pruneWorkOne] at hj
    split at hj
    · split at hj
      · rcases List.mem_append.mp hj with hj | hj
        · exact hs.2 j hj
        · rcases hg : P.funcs[fid]? with _ | g
          · simp [hg] at hj
          · exact PruneReach.step hfid hg (by simpa [hg] using hj)
      · exact hs.2 j hj
    · exact hs.2 j hj

omit model in
theorem Passes.pruneWorkFrom_origin {P : Prog} {n : Nat}
    {work : List FuncId} {s : MProd (List FuncId) (Array Bool)}
    (hwork : ∀ fid ∈ work, PruneReach P fid) (hs : PruneOrigin P s) :
    PruneOrigin P (pruneWorkFrom P n work s) := by
  induction work generalizing s with
  | nil => exact hs
  | cons fid work ih =>
      simp only [pruneWorkFrom, List.foldl_cons]
      apply ih
      · intro j hj
        exact hwork j (by simp [hj])
      · exact pruneWorkOne_origin (hwork fid (by simp)) hs

def Passes.PruneFrontier (P : Prog) (used : Array Bool)
    (work : List FuncId) : Prop :=
  (∀ fid ∈ pruneCallees P.main, UsedAt used fid ∨ fid ∈ work) ∧
  (∀ src f, UsedAt used src → P.funcs[src]? = some f →
    ∀ fid ∈ pruneCallees f, UsedAt used fid ∨ fid ∈ work)

def Passes.WorkValid (n : Nat) (work : List FuncId) : Prop :=
  ∀ fid ∈ work, fid < n

omit model in
theorem Passes.pruneFrontier_init (P : Prog) :
    PruneFrontier P (Array.replicate P.funcs.size false) (pruneCallees P.main) := by
  constructor
  · exact fun fid h => Or.inr h
  · intro src f hs
    unfold UsedAt at hs
    rcases Array.getElem?_eq_some_iff.mp hs with ⟨hlt, hget⟩
    simp at hget

omit model in
theorem Passes.workValid_init {P : Prog} (hwf : P.wfCheck = true) :
    WorkValid P.funcs.size (pruneCallees P.main) := by
  intro fid hfid
  apply wfCheck_callee_lt (f := P.main) (n := P.funcs.size)
  · simp only [Prog.wfCheck, Bool.and_eq_true] at hwf
    exact hwf.1.2
  · exact hfid

omit model in
theorem Passes.pruneWorkFrom_next_valid {P : Prog} (hwf : P.wfCheck = true)
    {n : Nat} (hn : n = P.funcs.size) {work : List FuncId}
    (hwork : WorkValid n work) {s : MProd (List FuncId) (Array Bool)}
    (hnext : WorkValid n s.1) :
    WorkValid n (pruneWorkFrom P n work s).1 := by
  induction work generalizing s with
  | nil => exact hnext
  | cons fid work ih =>
      have hfid : fid < n := hwork fid (by simp)
      apply ih (s := pruneWorkOne P n fid s)
      · exact fun j hj => hwork j (by simp [hj])
      · intro j hj
        by_cases hf : fid < n
        · by_cases hu : (!s.2[fid]!) = true
          · simp only [pruneWorkOne, hf, dite_true, hu, if_true] at hj
            rcases List.mem_append.mp hj with hj | hj
            · exact hnext j hj
            · rcases hget : P.funcs[fid]? with _ | g
              · simp [hget] at hj
              · have hjlt := wfCheck_callee_lt (f := g) (n := P.funcs.size)
                  (progWf_func hwf hget) (by simpa [hget] using hj)
                simpa [hn] using hjlt
          · simp only [pruneWorkOne, hf, dite_true, hu] at hj
            exact hnext j hj
        · simp only [pruneWorkOne, hf, dite_false] at hj
          exact hnext j hj

omit model in
theorem Passes.pruneFrontier_advance {P : Prog} (_hwf : P.wfCheck = true)
    {used : Array Bool} {work : List FuncId} (hsz : used.size = P.funcs.size)
    (hvalid : WorkValid P.funcs.size work) (hfront : PruneFrontier P used work) :
    let r := pruneWork P P.funcs.size work used
    PruneFrontier P r.2 r.1 := by
  let r := pruneWork P P.funcs.size work used
  have hmono : MarkSub used r.2 := by
    exact pruneWorkFrom_mono P P.funcs.size work ⟨[], used⟩
  have hmarks : ∀ fid ∈ work, UsedAt r.2 fid := by
    intro fid hm
    exact pruneWorkFrom_marks P hsz hm (hvalid fid hm)
  constructor
  · intro fid hm
    rcases hfront.1 fid hm with hu | hw
    · exact Or.inl (hmono fid hu)
    · exact Or.inl (hmarks fid hw)
  · intro src f hsrc hg fid hfid
    by_cases hold : UsedAt used src
    · rcases hfront.2 src f hold hg fid hfid with hu | hw
      · exact Or.inl (hmono fid hu)
      · exact Or.inl (hmarks fid hw)
    · have hsrcWork : src ∈ work :=
        pruneWorkFrom_new_origin P hsrc hold
      have hsrcLt := hvalid src hsrcWork
      exact Or.inr (pruneWorkFrom_emits P hsz hsrcWork hsrcLt hold hg hfid)

def Passes.pruneAdvance (P : Prog) (n : Nat)
    (s : MProd (Array Bool) (List FuncId)) : MProd (Array Bool) (List FuncId) :=
  let r := pruneWork P n s.2 s.1
  ⟨r.2, r.1⟩

omit model in
theorem Passes.pruneRound_eq (P : Prog) (n i : Nat)
    (s : MProd (Array Bool) (List FuncId)) :
    pruneRound P n i s =
      if (pruneAdvance P n s).2.isEmpty then .done (pruneAdvance P n s)
      else .yield (pruneAdvance P n s) := by
  rfl

omit model in
theorem Passes.pruneAdvance_size (P : Prog) (n : Nat)
    (s : MProd (Array Bool) (List FuncId)) :
    (pruneAdvance P n s).1.size = s.1.size := by
  exact pruneWorkFrom_size P n s.2 ⟨[], s.1⟩

omit model in
theorem Passes.pruneAdvance_mono (P : Prog) (n : Nat)
    (s : MProd (Array Bool) (List FuncId)) :
    MarkSub s.1 (pruneAdvance P n s).1 := by
  exact pruneWorkFrom_mono P n s.2 ⟨[], s.1⟩

omit model in
theorem Passes.pruneAdvance_empty {P : Prog} {n : Nat}
    {s : MProd (Array Bool) (List FuncId)} (h : s.2.isEmpty = true) :
    pruneAdvance P n s = s := by
  cases s with
  | mk used work =>
      have hw : work = [] := List.isEmpty_iff.mp h
      subst work
      rfl

omit model in
theorem Passes.pruneFold_empty {P : Prog} {n : Nat}
    {s : MProd (Array Bool) (List FuncId)} (h : s.2.isEmpty = true)
    (l : List Nat) : l.foldl (fun s _ => pruneAdvance P n s) s = s := by
  induction l generalizing s with
  | nil => rfl
  | cons i is ih =>
      simp only [List.foldl_cons]
      rw [pruneAdvance_empty h]
      exact ih h

omit model in
theorem Passes.loopWith_pruneRound_eq_fold (P : Prog) (n : Nat)
    (l : List Nat) (s : MProd (Array Bool) (List FuncId)) :
    loopWith (pruneRound P n) l s =
      l.foldl (fun s _ => pruneAdvance P n s) s := by
  induction l generalizing s with
  | nil => rfl
  | cons i is ih =>
      rw [loopWith_cons, pruneRound_eq]
      by_cases h : (pruneAdvance P n s).2.isEmpty = true
      · rw [if_pos h]
        symm
        exact pruneFold_empty h is
      · rw [if_neg h, List.foldl_cons]
        exact ih (pruneAdvance P n s)

def Passes.pruneIter (P : Prog) (n : Nat) :
    Nat → MProd (Array Bool) (List FuncId) → MProd (Array Bool) (List FuncId)
  | 0, s => s
  | k + 1, s => pruneIter P n k (pruneAdvance P n s)

omit model in
theorem Passes.pruneFold_eq_iter (P : Prog) (n : Nat) (l : List Nat)
    (s : MProd (Array Bool) (List FuncId)) :
    l.foldl (fun s _ => pruneAdvance P n s) s = pruneIter P n l.length s := by
  induction l generalizing s with
  | nil => rfl
  | cons i is ih => simpa [pruneIter] using ih (pruneAdvance P n s)

omit model in
theorem Passes.pruneState_eq_iter (P : Prog) :
    pruneState P = pruneIter P P.funcs.size (P.funcs.size + 1)
      ⟨Array.replicate P.funcs.size false, pruneCallees P.main⟩ := by
  unfold pruneState
  rw [loopWith_pruneRound_eq_fold, pruneFold_eq_iter]
  simp [pruneCallees]

def Passes.PruneStateOrigin (P : Prog)
    (s : MProd (Array Bool) (List FuncId)) : Prop :=
  (∀ fid, UsedAt s.1 fid → PruneReach P fid) ∧
  ∀ fid ∈ s.2, PruneReach P fid

omit model in
theorem Passes.pruneAdvance_origin {P : Prog} {n : Nat}
    {s : MProd (Array Bool) (List FuncId)} (hs : PruneStateOrigin P s) :
    PruneStateOrigin P (pruneAdvance P n s) := by
  exact pruneWorkFrom_origin hs.2 ⟨hs.1, by simp⟩

omit model in
theorem Passes.pruneIter_origin {P : Prog} {n : Nat} :
    ∀ (k : Nat) (s : MProd (Array Bool) (List FuncId)),
      PruneStateOrigin P s → PruneStateOrigin P (pruneIter P n k s) := by
  intro k
  induction k with
  | zero => intro s hs; exact hs
  | succ k ih =>
      intro s hs
      exact ih (pruneAdvance P n s) (pruneAdvance_origin hs)

omit model in
theorem Passes.pruneState_used_reach {P : Prog} {fid : FuncId}
    (hused : UsedAt (pruneState P).1 fid) : PruneReach P fid := by
  rw [pruneState_eq_iter] at hused
  have hinit : PruneStateOrigin P
      ⟨Array.replicate P.funcs.size false, pruneCallees P.main⟩ := by
    constructor
    · intro j hj
      unfold UsedAt at hj
      have hjlt : j < P.funcs.size := by
        simpa using (Array.getElem?_eq_some_iff.mp hj).1
      simp [hjlt] at hj
    · intro j hj
      exact PruneReach.main hj
  exact (pruneIter_origin (P := P) (n := P.funcs.size)
    (P.funcs.size + 1) _ hinit).1 fid hused

def Passes.PruneInv (P : Prog) (s : MProd (Array Bool) (List FuncId)) : Prop :=
  s.1.size = P.funcs.size ∧ WorkValid P.funcs.size s.2 ∧
    PruneFrontier P s.1 s.2

omit model in
theorem Passes.pruneInv_init {P : Prog} (hwf : P.wfCheck = true) :
    PruneInv P ⟨Array.replicate P.funcs.size false, pruneCallees P.main⟩ := by
  exact ⟨by simp, workValid_init hwf, pruneFrontier_init P⟩

omit model in
theorem Passes.pruneInv_advance {P : Prog} (hwf : P.wfCheck = true)
    {s : MProd (Array Bool) (List FuncId)} (h : PruneInv P s) :
    PruneInv P (pruneAdvance P P.funcs.size s) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [pruneAdvance_size, h.1]
  · exact pruneWorkFrom_next_valid hwf rfl h.2.1 (fun _ h => by simp at h)
  · exact pruneFrontier_advance hwf h.1 h.2.1 h.2.2

omit model in
theorem Passes.pruneReach_lt {P : Prog} (hwf : P.wfCheck = true)
    {fid : FuncId} (h : PruneReach P fid) : fid < P.funcs.size := by
  induction h with
  | main hcall => exact workValid_init hwf _ hcall
  | @step src fid f _ hg hcall ih =>
      exact wfCheck_callee_lt (progWf_func hwf hg) hcall

omit model in
theorem Passes.PruneFrontier.missing {P : Prog} {used : Array Bool}
    {work : List FuncId} (hfront : PruneFrontier P used work)
    {fid : FuncId} (hr : PruneReach P fid) (hnot : ¬ UsedAt used fid) :
    ∃ j ∈ work, ¬ UsedAt used j := by
  induction hr with
  | main hcall =>
      rcases hfront.1 _ hcall with hu | hw
      · exact absurd hu hnot
      · exact ⟨_, hw, hnot⟩
  | @step src fid f hr hg hcall ih =>
      by_cases hs : UsedAt used src
      · rcases hfront.2 src f hs hg fid hcall with hu | hw
        · exact absurd hu hnot
        · exact ⟨_, hw, hnot⟩
      · exact ih hs

def Passes.pruneMeasure (n : Nat) (used : Array Bool) : Nat :=
  ((List.range n).map fun i => if used[i]? = some true then 1 else 0).sum

omit model in
theorem Passes.pruneMeasure_le (n : Nat) (used : Array Bool) :
    pruneMeasure n used ≤ n := by
  unfold pruneMeasure
  have hle : ((List.range n).map fun i => if used[i]? = some true then 1 else 0).sum ≤
      ((List.range n).map fun _ => 1).sum :=
    List.sum_le_sum (fun i hi => by split <;> omega)
  simpa using hle

omit model in
theorem Passes.pruneMeasure_lt {n : Nat} {A B : Array Bool}
    (hsub : MarkSub A B) {j : Nat} (hj : j < n)
    (hA : ¬ UsedAt A j) (hB : UsedAt B j) :
    pruneMeasure n A < pruneMeasure n B := by
  unfold pruneMeasure
  apply List.sum_lt_sum
  · intro i hi
    by_cases hiA : UsedAt A i
    · have hiB := hsub i hiA
      simp [UsedAt] at hiA hiB ⊢
      simp [hiA, hiB]
    · simp [UsedAt] at hiA ⊢
      simp [hiA]
  · refine ⟨j, List.mem_range.mpr hj, ?_⟩
    simp [UsedAt] at hA hB ⊢
    simp [hA, hB]

omit model in
theorem Passes.pruneIter_mono (P : Prog) (n k : Nat)
    (s : MProd (Array Bool) (List FuncId)) :
    MarkSub s.1 (pruneIter P n k s).1 := by
  induction k generalizing s with
  | zero => exact markSub_refl s.1
  | succ k ih =>
      exact markSub_trans (pruneAdvance_mono P n s)
        (ih (pruneAdvance P n s))

omit model in
theorem Passes.pruneIter_measure_growth {P : Prog} (hwf : P.wfCheck = true) :
    ∀ (k : Nat) (s : MProd (Array Bool) (List FuncId)), PruneInv P s →
      ∀ {fid : FuncId}, PruneReach P fid →
        ¬ UsedAt (pruneIter P P.funcs.size k s).1 fid →
        pruneMeasure P.funcs.size s.1 + k ≤
          pruneMeasure P.funcs.size (pruneIter P P.funcs.size k s).1 := by
  intro k
  induction k with
  | zero => intro s hinv fid hr hnot; simp [pruneIter]
  | succ k ih =>
      intro s hinv fid hr hfinal
      let s' := pruneAdvance P P.funcs.size s
      have hinv' : PruneInv P s' := pruneInv_advance hwf hinv
      have hmonoTail : MarkSub s'.1 (pruneIter P P.funcs.size k s').1 :=
        pruneIter_mono P P.funcs.size k s'
      have hnot' : ¬ UsedAt s'.1 fid := fun h => hfinal (hmonoTail fid h)
      have hmissing := hinv.2.2.missing hr
        (fun h => hnot' (pruneAdvance_mono P P.funcs.size s fid h))
      obtain ⟨j, hjw, hjnot⟩ := hmissing
      have hjlt : j < P.funcs.size := hinv.2.1 j hjw
      have hjmark : UsedAt s'.1 j :=
        pruneWorkFrom_marks P hinv.1 hjw hjlt
      have hstep : pruneMeasure P.funcs.size s.1 < pruneMeasure P.funcs.size s'.1 :=
        pruneMeasure_lt (pruneAdvance_mono P P.funcs.size s) hjlt hjnot hjmark
      have htail := ih s' hinv' hr hfinal
      simp only [pruneIter] at htail ⊢
      dsimp only [s'] at hstep htail
      omega

omit model in
theorem Passes.pruneState_marks {P : Prog} (hwf : P.wfCheck = true)
    {fid : FuncId} (hr : PruneReach P fid) : UsedAt (pruneState P).1 fid := by
  rw [pruneState_eq_iter]
  by_contra hnot
  have hgrow := pruneIter_measure_growth hwf (P.funcs.size + 1)
    ⟨Array.replicate P.funcs.size false, pruneCallees P.main⟩
    (pruneInv_init hwf) hr hnot
  have hzero : pruneMeasure P.funcs.size (Array.replicate P.funcs.size false) = 0 := by
    unfold pruneMeasure
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have hlt := List.mem_range.mp hi
    simp [hlt]
  have hbound := pruneMeasure_le P.funcs.size
    (pruneIter P P.funcs.size (P.funcs.size + 1)
      ⟨Array.replicate P.funcs.size false, pruneCallees P.main⟩).1
  rw [hzero] at hgrow
  omega

omit model in
theorem Passes.usedAt_getElem! {A : Array Bool} {i : Nat}
    (h : UsedAt A i) : A[i]! = true := by
  unfold UsedAt at h
  obtain ⟨hlt, hget⟩ := Array.getElem?_eq_some_iff.mp h
  simpa [Array.getElem!_eq_getD, Array.getD, hlt] using hget

def Passes.pruneKeepN (P : Prog) (used : Array Bool) (m : Nat) :
    MProd (Array Func) (Array (Option FuncId)) :=
  (List.range m).foldl (fun s fid => pruneKeepOne P used fid s)
    ⟨#[], Array.replicate P.funcs.size none⟩

omit model in
theorem Passes.pruneKeep_eq_keepN (P : Prog) (used : Array Bool) :
    pruneKeep P used = pruneKeepN P used P.funcs.size := by
  simp [pruneKeep, pruneKeepN, List.range_eq_range']

omit model in
theorem Passes.pruneKeepN_remap_size (P : Prog) (used : Array Bool) (m : Nat) :
    (pruneKeepN P used m).2.size = P.funcs.size := by
  unfold pruneKeepN
  have key : ∀ (l : List Nat) (s : MProd (Array Func) (Array (Option FuncId))),
      (l.foldl (fun s fid => pruneKeepOne P used fid s) s).2.size = s.2.size := by
    intro l
    induction l with
    | nil => exact fun _ => rfl
    | cons fid l ih =>
        intro s
        simp only [List.foldl_cons]
        rw [ih]
        simp only [pruneKeepOne]
        split <;> simp
  rw [key]
  simp

omit model in
theorem Passes.pruneKeepN_lookup {P : Prog} {used : Array Bool}
    (_husedSize : used.size = P.funcs.size) :
    ∀ (m : Nat), m ≤ P.funcs.size → ∀ {fid : FuncId} {g : Func}, fid < m →
      P.funcs[fid]? = some g → UsedAt used fid →
      ∃ fid', (pruneKeepN P used m).2[fid]? = some (some fid') ∧
        (pruneKeepN P used m).1[fid']? = some g := by
  intro m
  induction m with
  | zero =>
      intro hm fid g hfid hfunc hused
      exact (Nat.not_lt_zero fid hfid).elim
  | succ m ih =>
      intro hm fid g hfid hfunc hused
      have hmle : m ≤ P.funcs.size := by omega
      rw [pruneKeepN, List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      let s := pruneKeepN P used m
      change ∃ fid', (pruneKeepOne P used m s).2[fid]? = some (some fid') ∧
        (pruneKeepOne P used m s).1[fid']? = some g
      have hsRemap : s.2.size = P.funcs.size := pruneKeepN_remap_size P used m
      rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hfid) with heq | hfidm
      · subst fid
        have hmu : used[m]! = true := usedAt_getElem! hused
        have hmf : P.funcs[m]! = g := by
          obtain ⟨hlt, hget⟩ := Array.getElem?_eq_some_iff.mp hfunc
          simpa [Array.getElem!_eq_getD, Array.getD, hlt] using hget
        refine ⟨s.1.size, ?_, ?_⟩
        · simp [pruneKeepOne, hmu, Array.set!, hsRemap, show m < P.funcs.size by omega]
        · simp [pruneKeepOne, hmu, hmf]
      · have heq : fid ≠ m := Nat.ne_of_lt hfidm
        obtain ⟨fid', hremap, hkept⟩ := ih hmle
          (fid := fid) (g := g) hfidm hfunc hused
        by_cases hmu : used[m]! = true
        · refine ⟨fid', ?_, ?_⟩
          · simpa [s, pruneKeepOne, hmu,
              Array.getElem?_setIfInBounds_ne (Ne.symm heq)] using hremap
          · rw [show pruneKeepOne P used m s =
                ⟨s.1.push P.funcs[m]!, s.2.set! m (some s.1.size)⟩ by
                  simp [pruneKeepOne, hmu]]
            simp only
            rw [Array.getElem?_push]
            have hlt : fid' < s.1.size := (Array.getElem?_eq_some_iff.mp hkept).1
            rw [if_neg (Nat.ne_of_lt hlt)]
            exact hkept
        · refine ⟨fid', ?_, ?_⟩
          · simpa [s, pruneKeepOne, hmu] using hremap
          · simpa [s, pruneKeepOne, hmu] using hkept

omit model in
theorem Passes.pruneKeep_lookup {P : Prog} {used : Array Bool}
    (husedSize : used.size = P.funcs.size) {fid : FuncId} {g : Func}
    (hfunc : P.funcs[fid]? = some g) (hused : UsedAt used fid) :
    ∃ fid', (pruneKeep P used).2[fid]? = some (some fid') ∧
      (pruneKeep P used).1[fid']? = some g := by
  rw [pruneKeep_eq_keepN]
  apply pruneKeepN_lookup husedSize P.funcs.size (le_refl _) _ hfunc hused
  exact (Array.getElem?_eq_some_iff.mp hfunc).1

omit model in
theorem Passes.pruneKeepN_mem {P : Prog} {used : Array Bool}
    (husedSize : used.size = P.funcs.size) :
    ∀ (m : Nat), m ≤ P.funcs.size → ∀ {g : Func},
      g ∈ (pruneKeepN P used m).1 →
      ∃ fid, fid < m ∧ P.funcs[fid]? = some g ∧ UsedAt used fid := by
  intro m
  induction m with
  | zero => intro hm g hg; simp [pruneKeepN] at hg
  | succ m ih =>
      intro hm g hg
      have hmle : m ≤ P.funcs.size := by omega
      rw [pruneKeepN, List.range_succ, List.foldl_append] at hg
      simp only [List.foldl_cons, List.foldl_nil] at hg
      let s := pruneKeepN P used m
      change g ∈ (pruneKeepOne P used m s).1 at hg
      by_cases hmu : used[m]! = true
      · rw [show pruneKeepOne P used m s =
            ⟨s.1.push P.funcs[m]!, s.2.set! m (some s.1.size)⟩ by
              simp [pruneKeepOne, hmu]] at hg
        rcases Array.mem_push.mp hg with hold | heq
        · obtain ⟨fid, hfid, hfunc, hu⟩ := ih hmle hold
          exact ⟨fid, by omega, hfunc, hu⟩
        · have hmlt : m < P.funcs.size := by omega
          have hfunc : P.funcs[m]? = some P.funcs[m]! := by
            rw [Array.getElem?_eq_getElem hmlt, getElem!_eq_getElem hmlt]
          have hu : UsedAt used m := by
            unfold UsedAt
            have hult : m < used.size := by omega
            rw [Array.getElem?_eq_getElem hult]
            simpa [Array.getElem!_eq_getD, Array.getD, hult] using hmu
          exact ⟨m, by omega, by simpa [heq] using hfunc, hu⟩
      · have hold : g ∈ s.1 := by
          simpa [pruneKeepOne, hmu] using hg
        obtain ⟨fid, hfid, hfunc, hu⟩ := ih hmle hold
        exact ⟨fid, by omega, hfunc, hu⟩

omit model in
theorem Passes.pruneKeep_mem {P : Prog} {used : Array Bool}
    (husedSize : used.size = P.funcs.size) {g : Func}
    (hg : g ∈ (pruneKeep P used).1) :
    ∃ fid, P.funcs[fid]? = some g ∧ UsedAt used fid := by
  rw [pruneKeep_eq_keepN] at hg
  obtain ⟨fid, hfid, hfunc, hu⟩ :=
    pruneKeepN_mem husedSize P.funcs.size (le_refl _) hg
  exact ⟨fid, hfunc, hu⟩

omit model in
theorem Passes.pruneIter_size (P : Prog) (n k : Nat)
    (s : MProd (Array Bool) (List FuncId)) :
    (pruneIter P n k s).1.size = s.1.size := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
      rw [pruneIter, ih, pruneAdvance_size]

omit model in
theorem Passes.pruneState_used_size (P : Prog) :
    (pruneState P).1.size = P.funcs.size := by
  rw [pruneState_eq_iter, pruneIter_size]
  simp

def Passes.pruneRest (remap : Array (Option FuncId)) (r : Rest) : Rest :=
  ⟨r.instrs.map (pruneInstr remap), r.term⟩

omit model in
theorem Passes.pruneFix_block {remap : Array (Option FuncId)} {f : Func}
    {i : BlockId} {b : Block} (hb : f.blocks[i]? = some b) :
    (pruneFix remap f).blocks[i]? = some (pruneBlock remap b) := by
  simp [pruneFix, hb]

omit model in
theorem Passes.pruneFix_kept_lookup {remap : Array (Option FuncId)}
    {kept : Array Func} {fid : FuncId} {g : Func} (hg : kept[fid]? = some g) :
    (kept.map (pruneFix remap))[fid]? = some (pruneFix remap g) := by
  simp [hg]

omit model in
theorem Passes.pruneRemap_value {remap : Array (Option FuncId)}
    {fid fid' : FuncId} (h : remap[fid]? = some (some fid')) :
    (remap[fid]?.join).getD fid = fid' := by
  rw [h]
  rfl

def Passes.PruneFuncReach (P : Prog) (f : Func) : Prop :=
  f = P.main ∨ ∃ fid, PruneReach P fid ∧ P.funcs[fid]? = some f

def Passes.PruneRestReach (P : Prog) (r : Rest) : Prop :=
  ∀ ds fid as, Instr.call ds fid as ∈ r.instrs → PruneReach P fid

omit model in
theorem Passes.pruneFuncReach_call {P : Prog} {f : Func}
    (hf : PruneFuncReach P f) {b : Block} (hb : b ∈ f.blocks.toList)
    {ds : List ValId} {fid : FuncId} {as : List ValId}
    (hi : Instr.call ds fid as ∈ b.instrs) : PruneReach P fid := by
  rcases hf with rfl | ⟨src, hsrc, hlookup⟩
  · exact PruneReach.main (mem_pruneCallees.mpr ⟨b, hb, ds, as, hi⟩)
  · exact PruneReach.step hsrc hlookup
      (mem_pruneCallees.mpr ⟨b, hb, ds, as, hi⟩)

omit model in
theorem Passes.pruneInstr_defs (remap : Array (Option FuncId)) (i : Instr) :
    (pruneInstr remap i).defs = i.defs := by
  cases i <;> rfl

omit model in
theorem Passes.pruneBlock_allDefs (remap : Array (Option FuncId)) (b : Block) :
    blockAllDefs (pruneBlock remap b) = blockAllDefs b := by
  simp only [blockAllDefs, pruneBlock, List.flatMap_map, pruneInstr_defs]

omit model in
theorem Passes.pruneFix_allDefs (remap : Array (Option FuncId)) (f : Func) :
    (pruneFix remap f).allDefs = f.allDefs := by
  unfold Func.allDefs pruneFix
  simp only [Array.toList_map, List.flatMap_map, pruneBlock_allDefs]

omit model in
theorem Passes.pruneBlock_wf {remap : Array (Option FuncId)} {f : Func}
    {b : Block} {oldN newN : Nat}
    (hbwf : BlockWF f.blocks f.nrets oldN b)
    (hcall : ∀ ds fid as, Instr.call ds fid as ∈ b.instrs →
      (remap[fid]?.join).getD fid < newN) :
    BlockWF (pruneFix remap f).blocks (pruneFix remap f).nrets newN
      (pruneBlock remap b) := by
  refine ⟨hbwf.1, ?_, ?_⟩
  · intro e he
    obtain ⟨tb, htb, hlen⟩ := hbwf.2.1 e (by simpa [pruneBlock] using he)
    exact ⟨pruneBlock remap tb, pruneFix_block htb,
      by simpa [pruneBlock] using hlen⟩
  · intro i hi
    simp only [pruneBlock] at hi
    obtain ⟨old, hold, heq⟩ := List.mem_map.mp hi
    subst i
    cases old with
    | const => trivial
    | op ds yop as => simpa [pruneInstr] using hbwf.2.2 (.op ds yop as) hold
    | call ds fid as => exact hcall ds fid as hold

omit model in
theorem Passes.pruneFix_wf {remap : Array (Option FuncId)} {f : Func}
    {oldN newN : Nat} (hfwf : f.wfCheck oldN = true)
    (hcall : ∀ b ∈ f.blocks.toList, ∀ ds fid as,
      Instr.call ds fid as ∈ b.instrs →
      (remap[fid]?.join).getD fid < newN) :
    (pruneFix remap f).wfCheck newN = true := by
  obtain ⟨hnd, hentry, ⟨eb, heb, hempty⟩, hblocks⟩ :=
    func_wfCheck_iff.mp hfwf
  apply func_wfCheck_iff.mpr
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [pruneFix_allDefs] using hnd
  · simpa [pruneFix] using hentry
  · exact ⟨pruneBlock remap eb, by simpa [pruneFix] using pruneFix_block heb,
      by simpa [pruneBlock] using hempty⟩
  · intro b hb
    have hbarr : b ∈ (pruneFix remap f).blocks := by simpa using hb
    obtain ⟨old, hold, rfl⟩ := Array.mem_map.mp (by simpa [pruneFix] using hbarr)
    exact pruneBlock_wf (hblocks old (by simpa using hold))
      (fun ds fid as hi => hcall old (by simpa using hold) ds fid as hi)

omit model in
theorem Passes.pruneFix_wf_reach {P : Prog} {used : Array Bool}
    (hwf : P.wfCheck = true) (husedSize : used.size = P.funcs.size)
    (hall : ∀ fid, PruneReach P fid → UsedAt used fid)
    {f : Func} (hreach : PruneFuncReach P f)
    (hfwf : f.wfCheck P.funcs.size = true) :
    let kept := (pruneKeep P used).1
    let remap := (pruneKeep P used).2
    (pruneFix remap f).wfCheck kept.size = true := by
  let kept := (pruneKeep P used).1
  let remap := (pruneKeep P used).2
  apply pruneFix_wf hfwf
  intro b hb ds fid as hi
  have hr : PruneReach P fid := pruneFuncReach_call hreach hb hi
  have hu : UsedAt used fid := hall fid hr
  have hlt : fid < P.funcs.size := pruneReach_lt hwf hr
  have hfunc : P.funcs[fid]? = some P.funcs[fid] :=
    Array.getElem?_eq_getElem hlt
  obtain ⟨fid', hremap, hkept⟩ := pruneKeep_lookup husedSize hfunc hu
  rw [pruneRemap_value hremap]
  exact (Array.getElem?_eq_some_iff.mp hkept).1

omit model in
theorem Passes.pruneRestReach_block {P : Prog} {f : Func}
    (hf : PruneFuncReach P f) {b : Block} (hb : b ∈ f.blocks.toList) :
    PruneRestReach P ⟨b.instrs, b.term⟩ := by
  intro ds fid as hi
  exact pruneFuncReach_call hf hb hi

omit model in
theorem Passes.pruneRestReach_tail {P : Prog} {i : Instr} {is : List Instr}
    {t : Term} (h : PruneRestReach P ⟨i :: is, t⟩) :
    PruneRestReach P ⟨is, t⟩ := by
  intro ds fid as hi
  exact h ds fid as (by simp [hi])

omit model in
theorem Passes.pruneRestReach_head {P : Prog} {ds : List ValId}
    {fid : FuncId} {as : List ValId} {is : List Instr} {t : Term}
    (h : PruneRestReach P ⟨Instr.call ds fid as :: is, t⟩) :
    PruneReach P fid := h ds fid as (by simp)

theorem Passes.pruneExec {P : Prog} {used : Array Bool}
    (husedSize : used.size = P.funcs.size)
    (hall : ∀ fid, PruneReach P fid → UsedAt used fid)
    {f : Func} {R : Regs} {st : EvmState} {rest : Rest} {res : FRes}
    (hexec : Exec (model := model) P f R st rest res) :
    ∀ (_hfunc : PruneFuncReach P f) (_hrest : PruneRestReach P rest),
      let kept := (pruneKeep P used).1
      let remap := (pruneKeep P used).2
      let Q : Prog :=
        { main := pruneFix remap P.main
          funcs := kept.map (pruneFix remap) }
      Exec (model := model) Q (pruneFix remap f) R st (pruneRest remap rest) res := by
  induction hexec with
  | @const f R st d v is t res htail ih =>
      intro hfunc hrest
      exact Exec.const (ih hfunc (pruneRestReach_tail hrest))
  | @op f R st st' ds yop as args rets is t res hget hop hlen htail ih =>
      intro hfunc hrest
      exact Exec.op hget hop hlen (ih hfunc (pruneRestReach_tail hrest))
  | @opHalt f R st st' ds yop as args is t hget hop =>
      intro hfunc hrest
      exact Exec.opHalt hget hop
  | @call f g R st st' ds as fid args rvals eb is t res hlookup hget hplen heb
      hbody hlen htail ihbody ih =>
      intro hfunc hrest
      have hreach : PruneReach P fid := pruneRestReach_head hrest
      have hused : UsedAt used fid := hall fid hreach
      obtain ⟨fid', hremap, hkept⟩ := pruneKeep_lookup husedSize hlookup hused
      let kept := (pruneKeep P used).1
      let remap := (pruneKeep P used).2
      have hnewLookup : (kept.map (pruneFix remap))[fid']? =
          some (pruneFix remap g) := pruneFix_kept_lookup hkept
      have hfidValue : (remap[fid]?.join).getD fid = fid' := pruneRemap_value hremap
      have hcalleeReach : PruneFuncReach P g := Or.inr ⟨fid, hreach, hlookup⟩
      have hebMem : eb ∈ g.blocks.toList := by
        simpa using block_mem_of_getElem? heb
      have hbody' := ihbody hcalleeReach (pruneRestReach_block hcalleeReach hebMem)
      have htail' := ih hfunc (pruneRestReach_tail hrest)
      change Exec _ _ _ _
        ⟨Instr.call ds ((remap[fid]?.join).getD fid) as ::
          (pruneRest remap ⟨is, t⟩).instrs, t⟩ res
      rw [hfidValue]
      exact Exec.call hnewLookup hget (by simpa [pruneFix] using hplen)
        (pruneFix_block heb) hbody' hlen htail'
  | @callHalt f g R st st' ds as fid args eb is t hlookup hget hplen heb hbody ihbody =>
      intro hfunc hrest
      have hreach : PruneReach P fid := pruneRestReach_head hrest
      have hused : UsedAt used fid := hall fid hreach
      obtain ⟨fid', hremap, hkept⟩ := pruneKeep_lookup husedSize hlookup hused
      let kept := (pruneKeep P used).1
      let remap := (pruneKeep P used).2
      have hnewLookup : (kept.map (pruneFix remap))[fid']? =
          some (pruneFix remap g) := pruneFix_kept_lookup hkept
      have hfidValue : (remap[fid]?.join).getD fid = fid' := pruneRemap_value hremap
      have hcalleeReach : PruneFuncReach P g := Or.inr ⟨fid, hreach, hlookup⟩
      have hebMem : eb ∈ g.blocks.toList := by
        simpa using block_mem_of_getElem? heb
      have hbody' := ihbody hcalleeReach (pruneRestReach_block hcalleeReach hebMem)
      change Exec _ _ _ _
        ⟨Instr.call ds ((remap[fid]?.join).getD fid) as ::
          (pruneRest remap ⟨is, t⟩).instrs, t⟩ (.halt st')
      rw [hfidValue]
      exact Exec.callHalt hnewLookup hget (by simpa [pruneFix] using hplen)
        (pruneFix_block heb) hbody'
  | @jump f R st e tb args res htb hget hplen htail ih =>
      intro hfunc hrest
      have htbMem : tb ∈ f.blocks.toList := by simpa using block_mem_of_getElem? htb
      exact Exec.jump (pruneFix_block htb) hget (by simpa [pruneBlock] using hplen)
        (ih hfunc (pruneRestReach_block hfunc htbMem))
  | @branchTrue f R st c v et ef tb args res hc hv htb hget hplen htail ih =>
      intro hfunc hrest
      have htbMem : tb ∈ f.blocks.toList := by simpa using block_mem_of_getElem? htb
      exact Exec.branchTrue hc hv (pruneFix_block htb) hget
        (by simpa [pruneBlock] using hplen)
        (ih hfunc (pruneRestReach_block hfunc htbMem))
  | @branchFalse f R st c et ef tb args res hc htb hget hplen htail ih =>
      intro hfunc hrest
      have htbMem : tb ∈ f.blocks.toList := by simpa using block_mem_of_getElem? htb
      exact Exec.branchFalse hc (pruneFix_block htb) hget
        (by simpa [pruneBlock] using hplen)
        (ih hfunc (pruneRestReach_block hfunc htbMem))
  | @ret f R st xs vals hget =>
      intro hfunc hrest
      exact Exec.ret hget
  | @halt f R st st' yop as args hget hop =>
      intro hfunc hrest
      exact Exec.halt hget hop

omit model in
theorem Passes.pruneFuncs_wf {P : Prog} (hwf : P.wfCheck = true) :
    (pruneFuncs P).wfCheck = true := by
  rw [pruneFuncs_eq_model]
  unfold pruneModel
  let used := (pruneState P).1
  by_cases hallUsed : used.all id = true
  · rw [if_pos hallUsed]
    exact hwf
  · rw [if_neg hallUsed]
    let kept := (pruneKeep P used).1
    let remap := (pruneKeep P used).2
    have husedSize : used.size = P.funcs.size := pruneState_used_size P
    have hmarks : ∀ fid, PruneReach P fid → UsedAt used fid := by
      intro fid hr
      exact pruneState_marks hwf hr
    have horigin : ∀ fid, UsedAt used fid → PruneReach P fid := by
      intro fid hu
      exact pruneState_used_reach hu
    have hparts := hwf
    simp only [Prog.wfCheck, Bool.and_eq_true] at hparts ⊢
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · simpa [pruneFix, kept, remap] using hparts.1.1.1
    · simpa [pruneFix, kept, remap] using hparts.1.1.2
    · have hm := pruneFix_wf_reach hwf husedSize hmarks
          (f := P.main) (Or.inl rfl) hparts.1.2
      simpa [kept, remap] using hm
    · rw [Array.all_eq_true_iff_forall_mem]
      intro q hq
      obtain ⟨g, hg, rfl⟩ := Array.mem_map.mp hq
      obtain ⟨fid, hfunc, hu⟩ := pruneKeep_mem husedSize hg
      have hr : PruneReach P fid := horigin fid hu
      have hgwf : g.wfCheck P.funcs.size = true := progWf_func hwf hfunc
      have hnew := pruneFix_wf_reach hwf husedSize hmarks
        (f := g) (Or.inr ⟨fid, hr, hfunc⟩) hgwf
      simpa [kept, remap] using hnew

/-- **Pruning preserves whole-program runs.** The worklist invariant proves
that every function transitively reachable from `main` is marked within the
`n + 1` rounds.  `pruneKeep_lookup` then relates each marked old index to its
new index and original function, and `pruneExec` transports the complete call
tree while rewriting every call instruction through that remap. -/
theorem pruneFuncs_sound {P : Prog} {yst0 yst' : EvmState} {o : Outcome}
    (hwf : P.wfCheck = true) (hrun : Run (model := model) P yst0 yst' o) :
    Run (model := model) (Passes.pruneFuncs P) yst0 yst' o := by
  rw [Passes.pruneFuncs_eq_model]
  unfold Passes.pruneModel
  let used := (Passes.pruneState P).1
  by_cases hallUsed : used.all id = true
  · change Run (model := model) (if used.all id then P else _) yst0 yst' o
    rw [if_pos hallUsed]
    exact hrun
  · change Run (model := model) (if used.all id then P else _) yst0 yst' o
    rw [if_neg hallUsed]
    have husedSize : used.size = P.funcs.size := by
      exact Passes.pruneState_used_size P
    have hmarks : ∀ fid, Passes.PruneReach P fid → Passes.UsedAt used fid := by
      intro fid hr
      exact Passes.pruneState_marks hwf hr
    cases hrun with
    | normal heb hexec =>
        rename_i eb
        refine Run.normal (Passes.pruneFix_block heb) ?_
        have hebMem : eb ∈ P.main.blocks.toList := by
          simpa using block_mem_of_getElem? heb
        exact Passes.pruneExec (model := model) husedSize hmarks hexec
          (Or.inl rfl) (Passes.pruneRestReach_block (Or.inl rfl) hebMem)
    | halt heb hexec =>
        rename_i eb
        refine Run.halt (Passes.pruneFix_block heb) ?_
        have hebMem : eb ∈ P.main.blocks.toList := by
          simpa using block_mem_of_getElem? heb
        exact Passes.pruneExec (model := model) husedSize hmarks hexec
          (Or.inl rfl) (Passes.pruneRestReach_block (Or.inl rfl) hebMem)

def Passes.inlineRound (P : Prog) : Prog :=
  pruneFuncs (inlineMap (siteCounts P) P)

def Passes.inlineSame (P Q : Prog) : Bool :=
  Q.funcs.size == P.funcs.size && siteCounts Q == siteCounts P

omit model in
theorem Passes.inlineRound_wf {P : Prog} (hwf : P.wfCheck = true) :
    (inlineRound P).wfCheck = true := by
  exact pruneFuncs_wf (inlineMap_wf hwf)

theorem inlineRound_sound {P : Prog} {yst0 yst' : EvmState} {o : Outcome}
    (hwf : P.wfCheck = true) (hrun : Run (model := model) P yst0 yst' o) :
    Run (model := model) (Passes.inlineRound P) yst0 yst' o := by
  apply pruneFuncs_sound (Passes.inlineMap_wf hwf)
  exact Passes.inlineMap_sound hwf hrun

def Passes.inlineProgN : Nat → Prog → Prog
  | 0, P => P
  | n + 1, P =>
      let Q := inlineRound P
      if inlineSame P Q then Q else inlineProgN n Q

def Passes.inlineProgStep (_ : Nat) (P : Prog) : ForInStep Prog :=
  let Q := inlineRound P
  if inlineSame P Q then .done Q else .yield Q

def Passes.inlineProgRawStep (_ : Nat)
    (s : MProd (Option Prog) Prog) : ForInStep (MProd (Option Prog) Prog) :=
  let Q := inlineRound s.2
  if inlineSame s.2 Q then .done ⟨some Q, Q⟩ else .yield ⟨none, Q⟩

omit model in
theorem Passes.inlineProgRaw_loop (l : List Nat) (P : Prog) :
    let r := loopWith inlineProgRawStep l ⟨none, P⟩
    r.1.getD r.2 = loopWith inlineProgStep l P := by
  induction l generalizing P with
  | nil => rfl
  | cons i is ih =>
      rw [loopWith_cons, loopWith_cons]
      by_cases hs : inlineSame P (inlineRound P) = true
      · simp [inlineProgRawStep, inlineProgStep, hs]
      · simpa [inlineProgRawStep, inlineProgStep, hs] using ih (inlineRound P)

omit model in
theorem Passes.inlineProgStep_loop (l : List Nat) (P : Prog) :
    loopWith inlineProgStep l P = inlineProgN l.length P := by
  induction l generalizing P with
  | nil => rfl
  | cons i is ih =>
      rw [loopWith_cons]
      by_cases hs : inlineSame P (inlineRound P) = true
      · simp [inlineProgStep, inlineProgN, hs]
      · simpa [inlineProgStep, inlineProgN, hs] using ih (inlineRound P)

omit model in
theorem Passes.inlineProg_eq_inlineProgN (P : Prog) :
    inlineProg P = inlineProgN 3 P := by
  unfold inlineProg
  dsimp only
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rw [Id.forIn_eq_loopWith (g := inlineProgRawStep) (h := by
    intro i s
    simp only [inlineProgRawStep, inlineRound, inlineMap, inlineSame]
    split <;> rfl)]
  simp only [Id.run, bind, pure]
  let l := List.range' 0 ((3 - 0 + 1 - 1) / 1) 1
  let r := loopWith inlineProgRawStep l ⟨none, P⟩
  change (match r.1 with | none => r.2 | some a => a) = _
  have hm : (match r.1 with | none => r.2 | some a => a) = r.1.getD r.2 := by
    cases r.1 <;> rfl
  rw [hm]
  have hr := inlineProgRaw_loop l P
  change r.1.getD r.2 = _ at hr
  rw [hr, inlineProgStep_loop]
  rfl

theorem inlineProgN_sound {P : Prog} {yst0 yst' : EvmState} {o : Outcome} :
    ∀ n, P.wfCheck = true → Run (model := model) P yst0 yst' o →
      Run (model := model) (Passes.inlineProgN n P) yst0 yst' o := by
  intro n
  induction n generalizing P with
  | zero => intro hwf hrun; exact hrun
  | succ n ih =>
      intro hwf hrun
      have hroundWf := Passes.inlineRound_wf hwf
      have hroundRun := inlineRound_sound hwf hrun
      simp only [Passes.inlineProgN]
      split
      · exact hroundRun
      · exact ih hroundWf hroundRun

/-- **Inlining soundness**, the statement the top-level proof consumes.

The indexed replay chain proves one simultaneous `inlineMap` round.  The
syntactic `inlineMap_wf` and `pruneFuncs_wf` lemmas preserve the hypothesis
needed by the next round, while `inlineProg_eq_inlineProgN` exposes the
implementation's three-round early-return loop as a pure recursion. -/
theorem inlineProg_sound {P : Prog} {yst0 yst' : EvmState} {o : Outcome}
    (hwf : P.wfCheck = true) (hrun : Run (model := model) P yst0 yst' o) :
    Run (model := model) (Passes.inlineProg P) yst0 yst' o := by
  rw [Passes.inlineProg_eq_inlineProgN]
  exact inlineProgN_sound 3 hwf hrun

end

end YulEvmCompiler.SsaCfg
