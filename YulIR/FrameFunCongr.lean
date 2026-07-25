import YulIR.FrameBigStep

set_option warningAsError true
/-!
# YulIR.FrameFunCongr — function-table congruence for the frame semantics

The keystone for lifting a body-internal pass to a whole-program guarantee: if a transformation `g`
is a *locally sound* rewrite — `EquivBlock F (g b) b` for **every** block `b` and function table `F`
— then optimizing every function body with `g` (`mapBodiesFuns`) preserves the big-step judgment,
hence whole-program runs (`Run`). This is the frame analogue of the Yul `funDef` congruence
(`YulSemantics.Step.funenv_congr`), and — thanks to the single-inductive `Step` encoding and
`Std.HashMap.getElem?_map` (record-update keeps `nslots` definitionally equal, so no dependent
transport is needed) — it goes through by a single rule induction.

The "for every `F`" hypothesis is exactly what a *local* pass's soundness proof establishes (its
rewrite doesn't inspect the function table — calls are opaque), so `structural`/`simplify`/
`deadCode` will supply it directly.
-/

namespace YulIR.FinFrame.Sem

open YulSemantics (Outcome Ident)

/-- Optimize every function body of a table with `g` (a size-preserving block transform), keeping
each function's `nslots`/`params`/`rets` (so lookups stay defeq). -/
def mapBodiesFuns (g : {n : Nat} → Block n → Block n) (funs : Funs) : Funs :=
  funs.map (fun _ fd => { fd with body := g fd.body })

/-- Lookup after `mapBodiesFuns`: the body is `g`-transformed, the rest unchanged. -/
theorem mapBodiesFuns_get {g : {n : Nat} → Block n → Block n} {funs : Funs} {fn : Ident}
    {fd : Function} (h : funs[fn]? = some fd) :
    (mapBodiesFuns g funs)[fn]? = some ({ fd with body := g fd.body } : Function) := by
  simp [mapBodiesFuns, Std.HashMap.getElem?_map, h]

/-- Reconstruct a normal/leave call under the optimized table (`fdecl` explicit so the shared
implicit elaborates cleanly; the body is swapped to `g fdecl.body` via local soundness). -/
theorem callNorm_map {g : {n : Nat} → Block n → Block n}
    (hg : ∀ (F : Funs) {m} (b : Block m), EquivBlock F (g b) b)
    {funs : Funs} {N} {σ : Store N} {st : State} {fn : Ident} {args} {fdecl : Function}
    {σ' : Store fdecl.nslots} {st' o}
    (hl : funs[fn]? = some fdecl)
    (hbody' : ExecBlock (mapBodiesFuns g funs)
      (seed fdecl.nslots fdecl.params (args.map (evalAtom σ))) st fdecl.body σ' st' o)
    (ho : o = .normal ∨ o = .leave) :
    Step (mapBodiesFuns g funs) σ st (.rhs (.call fn args)) (.eres (.ok (fdecl.rets.map σ') st')) :=
  Step.callNorm (fdecl := { fdecl with body := g fdecl.body }) (mapBodiesFuns_get hl)
    ((hg (mapBodiesFuns g funs) fdecl.body _ _ _ _ _).mpr hbody') ho

/-- Reconstruct a halting call under the optimized table. -/
theorem callHalt_map {g : {n : Nat} → Block n → Block n}
    (hg : ∀ (F : Funs) {m} (b : Block m), EquivBlock F (g b) b)
    {funs : Funs} {N} {σ : Store N} {st : State} {fn : Ident} {args} {fdecl : Function}
    {σ' : Store fdecl.nslots} {st'}
    (hl : funs[fn]? = some fdecl)
    (hbody' : ExecBlock (mapBodiesFuns g funs)
      (seed fdecl.nslots fdecl.params (args.map (evalAtom σ))) st fdecl.body σ' st' .halt) :
    Step (mapBodiesFuns g funs) σ st (.rhs (.call fn args)) (.eres (.halt st')) :=
  Step.callHalt (fdecl := { fdecl with body := g fdecl.body }) (mapBodiesFuns_get hl)
    ((hg (mapBodiesFuns g funs) fdecl.body _ _ _ _ _).mpr hbody')

/-- **Forward**: any run of the original table is a run of the optimized table. -/
theorem step_mapBodies_mp (g : {n : Nat} → Block n → Block n)
    (hg : ∀ (F : Funs) {m} (b : Block m), EquivBlock F (g b) b)
    {funs : Funs} {n} {σ : Store n} {st code res}
    (h : Step funs σ st code res) : Step (mapBodiesFuns g funs) σ st code res := by
  induction h with
  | atom => exact .atom
  | builtin hb => exact .builtin hb
  | callNorm hl _ ho ihbody => exact callNorm_map hg hl ihbody ho
  | callHalt hl _ ihbody => exact callHalt_map hg hl ihbody
  | writeOk _ ihr => exact .writeOk ihr
  | writeHalt _ ihr => exact .writeHalt ihr
  | writeMany _ ihr => exact .writeMany ihr
  | writeManyHalt _ ihr => exact .writeManyHalt ihr
  | effectOk _ ihr => exact .effectOk ihr
  | effectHalt _ ihr => exact .effectHalt ihr
  | condFalse hc => exact .condFalse hc
  | condTrue hc _ ihb => exact .condTrue hc ihb
  | switch _ ihb => exact .switch ihb
  | loopS _ ihl => exact .loopS ihl
  | brk => exact .brk
  | cont => exact .cont
  | lv => exact .lv
  | nil => exact .nil
  | consNormal _ _ ih1 ih2 => exact .consNormal ih1 ih2
  | consStop _ hne ih1 => exact .consStop ih1 hne
  | loopBrk _ ihb => exact .loopBrk ihb
  | loopLeave _ ihb => exact .loopLeave ihb
  | loopHalt _ ihb => exact .loopHalt ihb
  | loopStep _ hob _ _ ihb ihp ihl => exact .loopStep ihb hob ihp ihl
  | loopPostStop _ hob _ hne ihb ihp => exact .loopPostStop ihb hob ihp hne

/-- Inversion of `mapBodiesFuns` lookup: a hit came from an original function whose body was
`g`-transformed. -/
theorem mapBodiesFuns_get_inv {g : {n : Nat} → Block n → Block n} {funs : Funs} {fn : Ident}
    {fdecl' : Function} (h : (mapBodiesFuns g funs)[fn]? = some fdecl') :
    ∃ fd, funs[fn]? = some fd ∧ fdecl' = { fd with body := g fd.body } := by
  simp only [mapBodiesFuns, Std.HashMap.getElem?_map] at h
  obtain ⟨fd, hfd, heq⟩ := Option.map_eq_some_iff.mp h
  exact ⟨fd, hfd, heq.symm⟩

/-- **Backward**: any run of the optimized table is a run of the original table. -/
theorem step_mapBodies_mpr (g : {n : Nat} → Block n → Block n)
    (hg : ∀ (F : Funs) {m} (b : Block m), EquivBlock F (g b) b)
    {funs : Funs} {n} {σ : Store n} {st code res}
    (h : Step (mapBodiesFuns g funs) σ st code res) : Step funs σ st code res := by
  induction h with
  | atom => exact .atom
  | builtin hb => exact .builtin hb
  | callNorm hl' _ ho ihbody =>
      obtain ⟨fd, hfd, heq⟩ := mapBodiesFuns_get_inv hl'
      subst heq
      exact Step.callNorm (fdecl := fd) hfd ((hg funs fd.body _ _ _ _ _).mp ihbody) ho
  | callHalt hl' _ ihbody =>
      obtain ⟨fd, hfd, heq⟩ := mapBodiesFuns_get_inv hl'
      subst heq
      exact Step.callHalt (fdecl := fd) hfd ((hg funs fd.body _ _ _ _ _).mp ihbody)
  | writeOk _ ihr => exact .writeOk ihr
  | writeHalt _ ihr => exact .writeHalt ihr
  | writeMany _ ihr => exact .writeMany ihr
  | writeManyHalt _ ihr => exact .writeManyHalt ihr
  | effectOk _ ihr => exact .effectOk ihr
  | effectHalt _ ihr => exact .effectHalt ihr
  | condFalse hc => exact .condFalse hc
  | condTrue hc _ ihb => exact .condTrue hc ihb
  | switch _ ihb => exact .switch ihb
  | loopS _ ihl => exact .loopS ihl
  | brk => exact .brk
  | cont => exact .cont
  | lv => exact .lv
  | nil => exact .nil
  | consNormal _ _ ih1 ih2 => exact .consNormal ih1 ih2
  | consStop _ hne ih1 => exact .consStop ih1 hne
  | loopBrk _ ihb => exact .loopBrk ihb
  | loopLeave _ ihb => exact .loopLeave ihb
  | loopHalt _ ihb => exact .loopHalt ihb
  | loopStep _ hob _ _ ihb ihp ihl => exact .loopStep ihb hob ihp ihl
  | loopPostStop _ hob _ hne ihb ihp => exact .loopPostStop ihb hob ihp hne

/-- **Function-table congruence.** A locally-sound body transform `g` (`EquivBlock F (g b) b` for
every block and table) preserves the judgment when applied to every function body. -/
theorem step_mapBodies (g : {n : Nat} → Block n → Block n)
    (hg : ∀ (F : Funs) {m} (b : Block m), EquivBlock F (g b) b)
    {funs : Funs} {n} {σ : Store n} {st code res} :
    Step funs σ st code res ↔ Step (mapBodiesFuns g funs) σ st code res :=
  ⟨step_mapBodies_mp g hg, step_mapBodies_mpr g hg⟩

/-- Whole-program payoff: optimizing every function body with a locally-sound `g` preserves runs. -/
theorem run_mapBodies (g : {n : Nat} → Block n → Block n)
    (hg : ∀ (F : Funs) {m} (b : Block m), EquivBlock F (g b) b)
    {p : Program} {st st' o} :
    Run p st st' o ↔ Run ⟨mapBodiesFuns g p.functions, p.mainSlots, g p.main⟩ st st' o := by
  simp only [Run]
  constructor
  · rintro ⟨σ', hexec⟩
    exact ⟨σ', (hg (mapBodiesFuns g p.functions) p.main _ _ _ _ _).mpr (step_mapBodies_mp g hg hexec)⟩
  · rintro ⟨σ', hexec⟩
    exact ⟨σ', step_mapBodies_mpr g hg ((hg (mapBodiesFuns g p.functions) p.main _ _ _ _ _).mp hexec)⟩

end YulIR.FinFrame.Sem
