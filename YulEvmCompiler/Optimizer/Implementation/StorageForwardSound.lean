import YulEvmCompiler.Optimizer.Implementation.StorageForward
import YulEvmCompiler.Optimizer.Implementation.FunCongr
set_option warningAsError true
/-!
# Soundness of literal-slot storage forwarding

The simulation carries two invariants alongside the source big-step:
`BoundOK` tracks the variables available to cached value expressions, while
`StorageCache.OK` states that every cached expression denotes the current
contents of its literal storage slot. Store aliasing, assignment invalidation,
block restoration, halts, and function scopes are handled explicitly in both
directions, yielding the strong `EquivBlock` contract.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM

variable {calls : ExternalCalls} {creates : ExternalCreates}
local notation "D" => evmWithExternal calls creates

def StorageVal.denote (V : VEnv D) : StorageVal → Option U256
  | .lit n => some (litValue (.number n))
  | .var x => VEnv.get V x
  | .add x n => (VEnv.get V x).map (fun v => v + litValue (.number n))

def StorageFact.Holds (V : VEnv D) (st : EvmState) : Nat × StorageVal → Prop
  | (k, v) => v.denote V = some (st.storage (litValue (.number k)))

def StorageCache.OK (V : VEnv D) (st : EvmState) (C : StorageCache) : Prop :=
  ∀ p ∈ C, StorageFact.Holds V st p

theorem StorageCache.OK.nil (V : VEnv D) (st : EvmState) : StorageCache.OK V st [] := by
  intro p hp
  simp at hp

theorem StorageCache.OK.lookup {V : VEnv D} {st : EvmState} {C : StorageCache}
    (hc : StorageCache.OK V st C) {k : Nat} {v : StorageVal}
    (h : cacheLookup k C = some v) :
    v.denote V = some (st.storage (litValue (.number k))) := by
  simp only [cacheLookup, Option.map_eq_some_iff] at h
  obtain ⟨p, hp, rfl⟩ := h
  have hm := List.mem_of_find?_eq_some hp
  have hk := List.find?_some hp
  have hk' : p.1 = k := by simpa using hk
  cases p with
  | mk k' v =>
    simp only at hk'
    subst k'
    exact hc _ hm

theorem StorageVal.denote_setMany_not_dep {V : VEnv D} {xs : List Ident}
    {vs : List U256} {v : StorageVal} (h : ∀ x, v.dep = some x → x ∉ xs) :
    v.denote (calls := calls) (creates := creates) (VEnv.setMany V xs vs) =
      v.denote (calls := calls) (creates := creates) V := by
  cases v with
  | lit n => rfl
  | var x =>
      simp only [StorageVal.dep, Option.some.injEq] at h
      exact VEnv.get_setMany_not_mem (h x rfl)
  | add x n =>
      simp only [StorageVal.dep, Option.some.injEq] at h
      simp only [StorageVal.denote]
      rw [VEnv.get_setMany_not_mem (h x rfl)]

theorem StorageVal.denote_prepend_not_dep {V : VEnv D} {xs : List Ident}
    {vs : List U256} {v : StorageVal} (h : ∀ x, v.dep = some x → x ∉ xs) :
    v.denote (calls := calls) (creates := creates) (xs.zip vs ++ V) =
      v.denote (calls := calls) (creates := creates) V := by
  have hkeys : ∀ x, v.dep = some x → x ∉ (xs.zip vs).map Prod.fst := by
    intro x hx hmem
    obtain ⟨p, hp, heq⟩ := List.mem_map.mp hmem
    rcases p with ⟨y, w⟩
    simp only at heq
    subst y
    exact h x hx (List.of_mem_zip hp).1
  cases v with
  | lit n => rfl
  | var x =>
      simp only [StorageVal.denote]
      rw [VEnv.get_append_not_mem (hkeys x rfl)]
  | add x n =>
      simp only [StorageVal.denote]
      rw [VEnv.get_append_not_mem (hkeys x rfl)]

theorem StorageCache.OK.kill_setMany {V : VEnv D} {st : EvmState}
    {C : StorageCache} (hc : StorageCache.OK V st C) (xs : List Ident) (vs : List U256) :
    StorageCache.OK (VEnv.setMany V xs vs) st (cacheKill xs C) := by
  intro p hp
  simp only [cacheKill, List.mem_filter] at hp
  rw [StorageFact.Holds, StorageVal.denote_setMany_not_dep]
  · exact hc p hp.1
  · intro x hx hmem
    have hk := hp.2
    rw [hx] at hk
    simp [List.contains_eq_mem, hmem] at hk

theorem StorageCache.OK.kill_prepend {V : VEnv D} {st : EvmState}
    {C : StorageCache} (hc : StorageCache.OK V st C) (xs : List Ident) (vs : List U256) :
    StorageCache.OK (calls := calls) (creates := creates)
      (xs.zip vs ++ V) st (cacheKill xs C) := by
  intro p hp
  simp only [cacheKill, List.mem_filter] at hp
  rw [StorageFact.Holds, StorageVal.denote_prepend_not_dep]
  · exact hc p hp.1
  · intro x hx hmem
    have hk := hp.2
    rw [hx] at hk
    simp [List.contains_eq_mem, hmem] at hk

theorem StorageCache.OK.kill_bindZeros {V : VEnv D} {st : EvmState}
    {C : StorageCache} (hc : StorageCache.OK V st C) (xs : List Ident) :
    StorageCache.OK (bindZeros D xs ++ V) st (cacheKill xs C) := by
  intro p hp
  simp only [cacheKill, List.mem_filter] at hp
  rcases p with ⟨k, v⟩
  rw [StorageFact.Holds]
  have hdep : ∀ x, v.dep = some x → x ∉ (bindZeros D xs).map Prod.fst := by
    intro x hx hmem
    rw [bindZeros_keys] at hmem
    have hk := hp.2
    rw [hx] at hk
    simp [List.contains_eq_mem, hmem] at hk
  cases v with
  | lit n => exact hc (k, .lit n) hp.1
  | var x =>
      simp only [StorageVal.denote]
      rw [VEnv.get_append_not_mem (hdep x rfl)]
      exact hc (k, .var x) hp.1
  | add x n =>
      simp only [StorageVal.denote]
      rw [VEnv.get_append_not_mem (hdep x rfl)]
      exact hc (k, .add x n) hp.1

theorem StorageCache.OK.put {V : VEnv D} {st : EvmState} {C : StorageCache}
    (hc : StorageCache.OK V st C) {k : Nat} {v : StorageVal}
    (hv : StorageFact.Holds V st (k, v)) :
    StorageCache.OK V st (cachePut k v C) := by
  intro p hp
  simp only [cachePut, List.mem_cons, List.mem_filter] at hp
  rcases hp with rfl | hp
  · exact hv
  · exact hc p hp.1

theorem StorageVal.eval {V : VEnv D} {st : EvmState} {v : StorageVal} {w : U256}
    (h : v.denote V = some w) (funs : FunEnv D) :
    Step D funs V st (.expr v.toExpr) (.eres (.vals [w] st)) := by
  cases v with
  | lit n =>
      simp only [StorageVal.denote, Option.some.injEq] at h
      subst w
      exact Step.lit
  | var x =>
      exact Step.var h
  | add x n =>
      simp only [StorageVal.denote, Option.map_eq_some_iff] at h
      obtain ⟨a, ha, rfl⟩ := h
      refine Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil Step.lit) (Step.var ha)) ?_
      exact pureFn_builtin rfl st

theorem StorageVal.eval_inv {V : VEnv D} {st : EvmState} {v : StorageVal}
    {r : EResult D} (h : Step D funs V st (.expr v.toExpr) (.eres r)) :
    ∃ w, v.denote V = some w ∧ r = .vals [w] st := by
  cases v with
  | lit n =>
      cases h
      exact ⟨_, rfl, rfl⟩
  | var x =>
      cases h with
      | var hv => exact ⟨_, hv, rfl⟩
  | add x n =>
      cases h with
      | builtinOk ha hop =>
          cases ha with
          | argsCons hrest hx =>
              cases hrest with
              | argsCons hnil hn =>
                  cases hnil
                  cases hn
                  cases hx with
                  | var hv =>
                      simp [builtinWithExternal, stepOp] at hop
                      obtain ⟨rfl, rfl⟩ := hop
                      exact ⟨_, by simp [StorageVal.denote, hv], rfl⟩
      | builtinHalt ha hop =>
          cases ha with
          | argsCons hrest hx =>
              cases hrest with
              | argsCons hnil hn =>
                  cases hnil
                  cases hn
                  cases hx
                  simp [builtinWithExternal, stepOp, bin] at hop
      | builtinArgsHalt ha =>
          cases ha with
          | argsRestHalt hrest =>
              cases hrest with
              | argsRestHalt hnil => cases hnil
              | argsHeadHalt hnil hn => cases hn
          | argsHeadHalt hrest hx => cases hx

theorem sload_lit_eval (k : Nat) (funs : FunEnv D) (V : VEnv D) (st : EvmState) :
    Step D funs V st (.expr (.builtin .sload [.lit (.number k)]))
      (.eres (.vals [st.storage (litValue (.number k))] st)) := by
  refine Step.builtinOk (Step.argsCons Step.argsNil Step.lit) ?_
  simp [builtinWithExternal, stepOp]

theorem sload_lit_inv {k : Nat} {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    {r : EResult D}
    (h : Step D funs V st (.expr (.builtin .sload [.lit (.number k)])) (.eres r)) :
    r = .vals [st.storage (litValue (.number k))] st := by
  cases h with
  | builtinOk ha hop =>
      cases ha with
      | argsCons hnil hlit =>
          cases hnil
          cases hlit
          simp [builtinWithExternal, stepOp] at hop
          obtain ⟨rfl, rfl⟩ := hop
          rfl
  | builtinHalt ha hop =>
      cases ha with
      | argsCons hnil hlit =>
          cases hnil
          cases hlit
          simp [builtinWithExternal, stepOp] at hop
  | builtinArgsHalt ha =>
      cases ha with
      | argsRestHalt hnil => cases hnil
      | argsHeadHalt hnil hlit => cases hlit

theorem cached_sload_iff {k : Nat} {v : StorageVal} {C : StorageCache}
    (hc : StorageCache.OK V st C) (hl : cacheLookup k C = some v)
    (funs : FunEnv D) (r : EResult D) :
    Step D funs V st (.expr (.builtin .sload [.lit (.number k)])) (.eres r) ↔
      Step D funs V st (.expr v.toExpr) (.eres r) := by
  have hv := hc.lookup hl
  have hs := sload_lit_eval (calls := calls) (creates := creates) k funs V st
  have hr := StorageVal.eval (st := st) hv funs
  constructor
  · intro h
    rw [sload_lit_inv h]
    exact hr
  · intro h
    obtain ⟨w, hw, heq⟩ := StorageVal.eval_inv h
    rw [hv] at hw
    injection hw with hw
    subst w
    rw [heq]
    exact hs

set_option linter.unusedSimpArgs false in
theorem literalSloadKey_eq_some {e : Expr Op} {k : Nat}
    (h : literalSloadKey e = some k) :
    e = .builtin .sload [.lit (.number k)] := by
  unfold literalSloadKey at h
  split at h <;> simp_all

set_option linter.unusedSimpArgs false in
theorem classifyStorageVal_eq_some {e : Expr Op} {v : StorageVal}
    (h : classifyStorageVal e = some v) : e = v.toExpr := by
  unfold classifyStorageVal at h
  split at h <;> injection h <;> subst v <;> rfl

set_option linter.unusedSimpArgs false in
theorem literalStore_eq_some {e : Expr Op} {k : Nat} {v : StorageVal}
    (h : literalStore e = some (k, v)) :
    ∃ rhs, e = .builtin .sstore [.lit (.number k), rhs] ∧
      classifyStorageVal rhs = some v := by
  unfold literalStore at h
  split at h <;> simp_all

theorem literalStore_holds {e : Expr Op} {k : Nat} {v : StorageVal}
    (hl : literalStore e = some (k, v))
    (h : Step D funs V st (.expr e) (.eres (.vals [] st'))) :
    StorageFact.Holds V st' (k, v) := by
  obtain ⟨rhs, rfl, hv⟩ := literalStore_eq_some hl
  have hrhs : rhs = v.toExpr := classifyStorageVal_eq_some hv
  cases h with
  | builtinOk ha hop =>
      cases ha with
      | argsCons hrest hkey =>
          cases hkey
          cases hrest with
          | argsCons hnil hvstep =>
              cases hnil
              rw [hrhs] at hvstep
              obtain ⟨w, hw, heq⟩ := StorageVal.eval_inv hvstep
              injection heq with hvals hstate
              cases hvals; cases hstate
              simp [builtinWithExternal, stepOp, guardStatic] at hop
              split at hop
              · contradiction
              · injection hop with _ hst
                cases hst
                simp [StorageFact.Holds, hw, upd]

mutual

theorem storageStableExpr_inv {e : Expr Op} (hs : storageStableExpr e = true)
    {funs : FunEnv D} {V : VEnv D} {st : EvmState} {r : EResult D}
    (h : Step D funs V st (.expr e) (.eres r)) :
    ∃ v, r = .vals [v] st := by
  cases e with
  | lit l => cases h; exact ⟨_, rfl⟩
  | var x => cases h; exact ⟨_, rfl⟩
  | call fn args => simp [storageStableExpr] at hs
  | builtin op args =>
      simp only [storageStableExpr, Bool.and_eq_true] at hs
      cases h with
      | builtinOk ha hop =>
          obtain ⟨vs, heq, hlen⟩ := storageStableArgs_inv hs.2 ha
          injection heq with hvs hst
          cases hvs; cases hst
          have har : pureTotalArity op = some args.length := by simpa using hs.1
          obtain ⟨w, hw⟩ := pureTotalArity_pureFn har _ hlen
          have heq := pureFn_builtin_inv hw hop
          injection heq with hrs hst
          cases hrs; cases hst
          exact ⟨w, rfl⟩
      | builtinHalt ha hop =>
          obtain ⟨vs, heq, hlen⟩ := storageStableArgs_inv hs.2 ha
          injection heq with hvs hst
          cases hvs; cases hst
          have har : pureTotalArity op = some args.length := by simpa using hs.1
          obtain ⟨w, hw⟩ := pureTotalArity_pureFn har _ hlen
          exact absurd (pureFn_builtin_inv hw hop) (by simp)
      | builtinArgsHalt ha =>
          obtain ⟨vs, heq, -⟩ := storageStableArgs_inv hs.2 ha
          cases heq

theorem storageStableArgs_inv {es : List (Expr Op)} (hs : storageStableArgs es = true)
    {funs : FunEnv D} {V : VEnv D} {st : EvmState} {r : EResult D}
    (h : Step D funs V st (.args es) (.eres r)) :
    ∃ vs, r = .vals vs st ∧ vs.length = es.length := by
  cases es with
  | nil => cases h; exact ⟨[], rfl, rfl⟩
  | cons e rest =>
      simp only [storageStableArgs, Bool.and_eq_true] at hs
      cases h with
      | argsCons hr he =>
          obtain ⟨vs, heq, hlen⟩ := storageStableArgs_inv hs.2 hr
          injection heq with hvs hst
          cases hvs; cases hst
          obtain ⟨v, heq⟩ := storageStableExpr_inv hs.1 he
          injection heq with _ hst
          cases hst
          exact ⟨_ :: _, rfl, by simp [hlen]⟩
      | argsRestHalt hr =>
          obtain ⟨vs, heq, -⟩ := storageStableArgs_inv hs.2 hr
          cases heq
      | argsHeadHalt hr he =>
          obtain ⟨vs, heq, -⟩ := storageStableArgs_inv hs.2 hr
          injection heq with _ hst
          subst hst
          obtain ⟨v, heq⟩ := storageStableExpr_inv hs.1 he
          cases heq

end

set_option linter.unusedSimpArgs false in
theorem sfLet_expr_fwd {xs : List Ident} {e e' : Expr Op} {C C' : StorageCache}
    {r : EResult D} (h : Step D funs V st (.expr e) (.eres r))
    (heq : sfLet C xs (some e) = (some e', C'))
    (hc : StorageCache.OK V st C) :
    Step D funs V st (.expr e') (.eres r) ∧
      (∀ vals st', r = .vals vals st' → vals.length = xs.length →
        StorageCache.OK (xs.zip vals ++ V) st' C') := by
  cases xs with
  | nil =>
      simp only [sfLet] at heq
      split at heq
      · next hs =>
          obtain ⟨rfl, rfl⟩ := heq
          refine ⟨h, ?_⟩
          intro vals st' hr _
          obtain ⟨w, hw⟩ := storageStableExpr_inv hs h
          rw [hr] at hw
          injection hw with hvals hst
          cases hvals; cases hst
          exact hc.kill_prepend [] []
      · obtain ⟨rfl, rfl⟩ := heq
        exact ⟨h, by intros; exact StorageCache.OK.nil _ _⟩
  | cons x rest =>
      cases rest with
      | nil =>
          generalize hk : literalSloadKey e = q
          cases q with
          | none =>
              simp only [sfLet, hk] at heq
              split at heq
              · next hs =>
                  obtain ⟨rfl, rfl⟩ := heq
                  refine ⟨h, ?_⟩
                  intro vals st' hr _
                  obtain ⟨w, hw⟩ := storageStableExpr_inv hs h
                  rw [hr] at hw
                  injection hw with hvals hst
                  cases hvals; cases hst
                  exact hc.kill_prepend [x] _
              · obtain ⟨rfl, rfl⟩ := heq
                exact ⟨h, by intros; exact StorageCache.OK.nil _ _⟩
          | some k =>
              simp only [sfLet, hk] at heq
              have he : e = .builtin .sload [.lit (.number k)] :=
                literalSloadKey_eq_some hk
              generalize hl : cacheLookup k C = q
              cases q with
              | none =>
                  simp only [hl, Option.map_none, Option.getD_none] at heq
                  obtain ⟨rfl, rfl⟩ := heq
                  refine ⟨h, ?_⟩
                  intro vals st' hr hlen
                  rw [he] at h
                  have hsload := sload_lit_inv h
                  rw [hr] at hsload
                  injection hsload with hvals hst
                  cases hst
                  cases vals with
                  | nil => simp at hlen
                  | cons w tail =>
                      cases tail with
                      | nil =>
                          cases hvals
                          refine (hc.kill_prepend [x] [_]).put ?_
                          simp only [StorageFact.Holds, StorageVal.denote]
                          change VEnv.get ((x, _) :: V) x = some _
                          rw [VEnv.get_cons]
                          simp
                      | cons w' tail => simp at hlen
              | some v =>
                  simp only [hl, Option.map_some, Option.getD_some] at heq
                  obtain ⟨rfl, rfl⟩ := heq
                  refine ⟨(cached_sload_iff hc hl funs r).mp (he ▸ h), ?_⟩
                  intro vals st' hr hlen
                  have hsload := sload_lit_inv (he ▸ h)
                  rw [hr] at hsload
                  injection hsload with hvals hst
                  cases hst
                  cases vals with
                  | nil => simp at hlen
                  | cons w tail =>
                      cases tail with
                      | nil =>
                          cases hvals
                          refine (hc.kill_prepend [x] [_]).put ?_
                          simp only [StorageFact.Holds, StorageVal.denote]
                          change VEnv.get ((x, _) :: V) x = some _
                          rw [VEnv.get_cons]
                          simp
                      | cons w' tail => simp at hlen
      | cons y tail =>
          simp only [sfLet] at heq
          split at heq
          · next hs =>
              obtain ⟨rfl, rfl⟩ := heq
              refine ⟨h, ?_⟩
              intro vals st' hr _
              obtain ⟨w, hw⟩ := storageStableExpr_inv hs h
              rw [hr] at hw
              injection hw with hvals hst
              cases hvals; cases hst
              exact hc.kill_prepend (x :: y :: tail) [w]
          · obtain ⟨rfl, rfl⟩ := heq
            exact ⟨h, by intros; exact StorageCache.OK.nil _ _⟩

theorem sfLet_some (C : StorageCache) (xs : List Ident) (e : Expr Op) :
    ∃ e' C', sfLet C xs (some e) = (some e', C') := by
  cases xs with
  | nil => simp [sfLet]; split <;> simp
  | cons x rest =>
      cases rest with
      | nil =>
          simp only [sfLet]
          split
          · next k =>
              exact ⟨_, _, rfl⟩
          · split <;> simp
      | cons y tail => simp [sfLet]; split <;> simp

set_option linter.unusedSimpArgs false in
theorem sfAssign_expr_fwd {bound xs : List Ident} {e e' : Expr Op}
    {C C' : StorageCache} {r : EResult D}
    (h : Step D funs V st (.expr e) (.eres r))
    (heq : sfAssign bound C xs e = (e', C'))
    (hc : StorageCache.OK V st C) :
    Step D funs V st (.expr e') (.eres r) ∧
      (∀ vals st', r = .vals vals st' →
        StorageCache.OK (VEnv.setMany V xs vals) st' C') := by
  cases xs with
  | nil =>
      simp only [sfAssign] at heq
      split at heq
      · next hs =>
          obtain ⟨rfl, rfl⟩ := heq
          refine ⟨h, ?_⟩
          intro vals st' hr
          obtain ⟨w, hw⟩ := storageStableExpr_inv hs h
          rw [hr] at hw
          injection hw with hvals hst
          cases hvals; cases hst
          exact hc.kill_setMany [] [w]
      · obtain ⟨rfl, rfl⟩ := heq
        exact ⟨h, by intros; exact StorageCache.OK.nil _ _⟩
  | cons x rest =>
      cases rest with
      | nil =>
          generalize hk : literalSloadKey e = q
          cases q with
          | none =>
              simp only [sfAssign, hk] at heq
              split at heq
              · next hs =>
                  obtain ⟨rfl, rfl⟩ := heq
                  refine ⟨h, ?_⟩
                  intro vals st' hr
                  obtain ⟨w, hw⟩ := storageStableExpr_inv hs h
                  rw [hr] at hw
                  injection hw with hvals hst
                  cases hvals; cases hst
                  exact hc.kill_setMany [x] [w]
              · obtain ⟨rfl, rfl⟩ := heq
                exact ⟨h, by intros; exact StorageCache.OK.nil _ _⟩
          | some k =>
              simp only [sfAssign, hk] at heq
              have he : e = .builtin .sload [.lit (.number k)] :=
                literalSloadKey_eq_some hk
              generalize hl : cacheLookup k C = q
              cases q with
              | none =>
                  simp only [hl, Option.map_none, Option.getD_none] at heq
                  obtain ⟨rfl, rfl⟩ := heq
                  refine ⟨h, ?_⟩
                  intro vals st' hr
                  rw [he] at h
                  have hsload := sload_lit_inv h
                  rw [hr] at hsload
                  injection hsload with hvals hst
                  cases hvals; cases hst
                  exact hc.kill_setMany [x] [_]
              | some v =>
                  simp only [hl, Option.map_some, Option.getD_some] at heq
                  obtain ⟨rfl, rfl⟩ := heq
                  refine ⟨(cached_sload_iff hc hl funs r).mp (he ▸ h), ?_⟩
                  intro vals st' hr
                  have hsload := sload_lit_inv (he ▸ h)
                  rw [hr] at hsload
                  injection hsload with hvals hst
                  cases hvals; cases hst
                  exact hc.kill_setMany [x] [_]
      | cons y tail =>
          simp only [sfAssign] at heq
          split at heq
          · next hs =>
              obtain ⟨rfl, rfl⟩ := heq
              refine ⟨h, ?_⟩
              intro vals st' hr
              obtain ⟨w, hw⟩ := storageStableExpr_inv hs h
              rw [hr] at hw
              injection hw with hvals hst
              cases hvals; cases hst
              exact hc.kill_setMany (x :: y :: tail) [w]
          · obtain ⟨rfl, rfl⟩ := heq
            exact ⟨h, by intros; exact StorageCache.OK.nil _ _⟩

set_option linter.unusedSimpArgs false in
theorem sfExprStmt_ok {e e' : Expr Op} {C C' : StorageCache}
    (h : Step D funs V st (.expr e) (.eres (.vals [] st')))
    (heq : sfExprStmt C e = (e', C')) (_hc : StorageCache.OK V st C) :
    e' = e ∧ StorageCache.OK V st' C' := by
  simp only [sfExprStmt] at heq
  generalize hl : literalStore e = q
  cases q with
  | none =>
      simp only [hl] at heq
      split at heq
      · next hs =>
          obtain ⟨rfl, rfl⟩ := heq
          obtain ⟨w, hw⟩ := storageStableExpr_inv hs h
          cases hw
      · obtain ⟨rfl, rfl⟩ := heq
        exact ⟨rfl, StorageCache.OK.nil _ _⟩
  | some p =>
      rcases p with ⟨k, v⟩
      simp only [hl] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact ⟨rfl, (StorageCache.OK.nil V st').put (literalStore_holds hl h)⟩

theorem sfExprStmt_fst (C : StorageCache) (e : Expr Op) : (sfExprStmt C e).1 = e := by
  simp only [sfExprStmt]
  split <;> first | rfl | (split <;> rfl)

set_option linter.unusedSimpArgs false in
theorem sfLet_expr_bwd {xs : List Ident} {e e' : Expr Op} {C C' : StorageCache}
    {r : EResult D} (h : Step D funs V st (.expr e') (.eres r))
    (heq : sfLet C xs (some e) = (some e', C'))
    (hc : StorageCache.OK V st C) : Step D funs V st (.expr e) (.eres r) := by
  cases xs with
  | nil =>
      simp only [sfLet] at heq
      split at heq <;> obtain ⟨rfl, rfl⟩ := heq <;> exact h
  | cons x rest =>
      cases rest with
      | nil =>
          generalize hk : literalSloadKey e = q
          cases q with
          | none =>
              simp only [sfLet, hk] at heq
              split at heq <;> obtain ⟨rfl, rfl⟩ := heq <;> exact h
          | some k =>
              simp only [sfLet, hk] at heq
              have he := literalSloadKey_eq_some hk
              generalize hl : cacheLookup k C = q
              cases q with
              | none =>
                  simp only [hl, Option.map_none, Option.getD_none] at heq
                  obtain ⟨rfl, rfl⟩ := heq
                  exact h
              | some v =>
                  simp only [hl, Option.map_some, Option.getD_some] at heq
                  obtain ⟨rfl, rfl⟩ := heq
                  rw [he]
                  exact (cached_sload_iff hc hl funs r).mpr h
      | cons y tail =>
          simp only [sfLet] at heq
          split at heq <;> obtain ⟨rfl, rfl⟩ := heq <;> exact h

set_option linter.unusedSimpArgs false in
theorem sfAssign_expr_bwd {bound xs : List Ident} {e e' : Expr Op}
    {C C' : StorageCache} {r : EResult D}
    (h : Step D funs V st (.expr e') (.eres r))
    (heq : sfAssign bound C xs e = (e', C'))
    (hc : StorageCache.OK V st C) : Step D funs V st (.expr e) (.eres r) := by
  cases xs with
  | nil =>
      simp only [sfAssign] at heq
      split at heq <;> obtain ⟨rfl, rfl⟩ := heq <;> exact h
  | cons x rest =>
      cases rest with
      | nil =>
          generalize hk : literalSloadKey e = q
          cases q with
          | none =>
              simp only [sfAssign, hk] at heq
              split at heq <;> obtain ⟨rfl, rfl⟩ := heq <;> exact h
          | some k =>
              simp only [sfAssign, hk] at heq
              have he := literalSloadKey_eq_some hk
              generalize hl : cacheLookup k C = q
              cases q with
              | none =>
                  simp only [hl, Option.map_none, Option.getD_none] at heq
                  obtain ⟨rfl, rfl⟩ := heq
                  exact h
              | some v =>
                  simp only [hl, Option.map_some, Option.getD_some] at heq
                  obtain ⟨rfl, rfl⟩ := heq
                  rw [he]
                  exact (cached_sload_iff hc hl funs r).mpr h
      | cons y tail =>
          simp only [sfAssign] at heq
          split at heq <;> obtain ⟨rfl, rfl⟩ := heq <;> exact h

def sfCode (bound : List Ident) (C : StorageCache) : Code Op → Code Op × StorageCache
  | .expr e => (.expr e, [])
  | .args es => (.args es, [])
  | .stmt s => let p := sfStmt bound C s; (.stmt p.1, p.2)
  | .stmts ss => let p := sfStmts bound C ss; (.stmts p.1, p.2)
  | .loop c post body => (.loop c post body, [])

def sfBound (bound : List Ident) : Code Op → List Ident
  | .stmt s => dpOut bound s
  | .stmts ss => dpOutStmts bound ss
  | _ => bound

def SFRel (bound : List Ident) (C C' : StorageCache) (code code' : Code Op) : Prop :=
  sfCode bound C code = (code', C')

theorem SFRel.expr_eq {bound : List Ident} {C C' : StorageCache} {code : Code Op}
    {e : Expr Op} (h : SFRel bound C C' code (.expr e)) : code = .expr e := by
  cases code <;> simp_all [SFRel, sfCode]

theorem SFRel.args_eq {bound : List Ident} {C C' : StorageCache} {code : Code Op}
    {es : List (Expr Op)} (h : SFRel bound C C' code (.args es)) : code = .args es := by
  cases code <;> simp_all [SFRel, sfCode]

theorem SFRel.loop_eq {bound : List Ident} {C C' : StorageCache} {code : Code Op}
    {c : Expr Op} {post body : Block Op}
    (h : SFRel bound C C' code (.loop c post body)) : code = .loop c post body := by
  cases code <;> simp_all [SFRel, sfCode]

set_option linter.unusedSimpArgs false in
theorem SFRel.let_inv {bound : List Ident} {C C' : StorageCache} {code : Code Op}
    {xs : List Ident} {rhs' : Option (Expr Op)}
    (h : SFRel bound C C' code (.stmt (.letDecl xs rhs'))) :
    ∃ rhs, code = .stmt (.letDecl xs rhs) ∧ sfLet C xs rhs = (rhs', C') := by
  cases code with
  | stmt s =>
      cases s with
      | letDecl vars val =>
          simp only [SFRel, sfCode, sfStmt, Prod.mk.injEq, Code.stmt.injEq,
            Stmt.letDecl.injEq] at h
          obtain ⟨⟨hvars, hfst⟩, hsnd⟩ := h
          subst vars
          exact ⟨val, rfl, Prod.ext hfst hsnd⟩
      | block body => simp [SFRel, sfCode, sfStmt] at h
      | funDef n ps rs body => simp [SFRel, sfCode, sfStmt] at h
      | assign vars val => simp [SFRel, sfCode, sfStmt] at h
      | cond c body => simp [SFRel, sfCode, sfStmt] at h
      | switch c cases dflt => simp [SFRel, sfCode, sfStmt] at h
      | forLoop init c post body => simp [SFRel, sfCode, sfStmt] at h
      | exprStmt e => simp [SFRel, sfCode, sfStmt] at h
      | «break» => simp [SFRel, sfCode, sfStmt] at h
      | «continue» => simp [SFRel, sfCode, sfStmt] at h
      | leave => simp [SFRel, sfCode, sfStmt] at h
  | expr e => simp [SFRel, sfCode] at h
  | args es => simp [SFRel, sfCode] at h
  | stmts ss => simp [SFRel, sfCode] at h
  | loop c post body => simp [SFRel, sfCode] at h

set_option linter.unusedSimpArgs false in
theorem SFRel.assign_inv {bound : List Ident} {C C' : StorageCache} {code : Code Op}
    {xs : List Ident} {rhs' : Expr Op}
    (h : SFRel bound C C' code (.stmt (.assign xs rhs'))) :
    ∃ rhs, code = .stmt (.assign xs rhs) ∧ sfAssign bound C xs rhs = (rhs', C') := by
  cases code with
  | stmt s =>
      cases s with
      | assign vars val =>
          simp only [SFRel, sfCode, sfStmt, Prod.mk.injEq, Code.stmt.injEq,
            Stmt.assign.injEq] at h
          obtain ⟨⟨hvars, hfst⟩, hsnd⟩ := h
          subst vars
          exact ⟨val, rfl, Prod.ext hfst hsnd⟩
      | block body => simp [SFRel, sfCode, sfStmt] at h
      | funDef n ps rs body => simp [SFRel, sfCode, sfStmt] at h
      | letDecl vars val => simp [SFRel, sfCode, sfStmt] at h
      | cond c body => simp [SFRel, sfCode, sfStmt] at h
      | switch c cases dflt => simp [SFRel, sfCode, sfStmt] at h
      | forLoop init c post body => simp [SFRel, sfCode, sfStmt] at h
      | exprStmt e => simp [SFRel, sfCode, sfStmt] at h
      | «break» => simp [SFRel, sfCode, sfStmt] at h
      | «continue» => simp [SFRel, sfCode, sfStmt] at h
      | leave => simp [SFRel, sfCode, sfStmt] at h
  | expr e => simp [SFRel, sfCode] at h
  | args es => simp [SFRel, sfCode] at h
  | stmts ss => simp [SFRel, sfCode] at h
  | loop c post body => simp [SFRel, sfCode] at h

set_option linter.unusedSimpArgs false in
theorem SFRel.exprStmt_inv {bound : List Ident} {C C' : StorageCache} {code : Code Op}
    {e' : Expr Op} (h : SFRel bound C C' code (.stmt (.exprStmt e'))) :
    code = .stmt (.exprStmt e') := by
  cases code with
  | stmt s =>
      cases s <;> simp_all [SFRel, sfCode, sfStmt, sfExprStmt_fst]
  | expr e => simp [SFRel, sfCode] at h
  | args es => simp [SFRel, sfCode] at h
  | stmts ss => simp [SFRel, sfCode] at h
  | loop c post body => simp [SFRel, sfCode] at h

set_option linter.unusedSimpArgs false in
theorem SFRel.cond_inv {bound : List Ident} {C C' : StorageCache} {code : Code Op}
    {c : Expr Op} {body' : Block Op}
    (h : SFRel bound C C' code (.stmt (.cond c body'))) :
    ∃ body, code = .stmt (.cond c body) ∧
      body' = (sfStmts bound [] body).1 ∧
      C' = if storageStableExpr c && stmtsNoNormal body then C else [] := by
  cases code with
  | stmt s =>
      cases s <;> simp_all [SFRel, sfCode, sfStmt]
      simpa [h.1.1] using h.2.symm
  | expr e => simp [SFRel, sfCode] at h
  | args es => simp [SFRel, sfCode] at h
  | stmts ss => simp [SFRel, sfCode] at h
  | loop c post body => simp [SFRel, sfCode] at h

set_option linter.unusedSimpArgs false in
theorem SFRel.stmts_nil_inv {bound : List Ident} {C C' : StorageCache} {code : Code Op}
    (h : SFRel bound C C' code (.stmts [])) : code = .stmts [] := by
  cases code with
  | stmts ss => cases ss <;> simp_all [SFRel, sfCode, sfStmts]
  | expr e => simp [SFRel, sfCode] at h
  | args es => simp [SFRel, sfCode] at h
  | stmt s => simp [SFRel, sfCode] at h
  | loop c post body => simp [SFRel, sfCode] at h

set_option linter.unusedSimpArgs false in
theorem SFRel.stmts_cons_inv {bound : List Ident} {C C' : StorageCache}
    {code : Code Op} {s' : Stmt Op} {rest' : List (Stmt Op)}
    (h : SFRel bound C C' code (.stmts (s' :: rest'))) :
    ∃ s rest C1, code = .stmts (s :: rest) ∧ sfStmt bound C s = (s', C1) ∧
      sfStmts (sfNextBound bound s) C1 rest = (rest', C') := by
  cases code with
  | stmts ss =>
      cases ss with
      | nil => simp [SFRel, sfCode, sfStmts] at h
      | cons s rest =>
          generalize hs : sfStmt bound C s = p
          rcases p with ⟨st, C1⟩
          simp only [SFRel, sfCode, sfStmts, hs, Prod.mk.injEq,
            Code.stmts.injEq, List.cons.injEq] at h
          obtain ⟨⟨hst, hrest⟩, hcache⟩ := h
          subst st
          exact ⟨s, rest, C1, rfl, hs, Prod.ext hrest hcache⟩
  | expr e => simp [SFRel, sfCode] at h
  | args es => simp [SFRel, sfCode] at h
  | stmt s => simp [SFRel, sfCode] at h
  | loop c post body => simp [SFRel, sfCode] at h

set_option linter.unusedSimpArgs false in
theorem SFRel.switch_eq {bound : List Ident} {C C' : StorageCache} {code : Code Op}
    {c : Expr Op} {cases : List (Literal × Block Op)} {dflt : Option (Block Op)}
    (h : SFRel bound C C' code (.stmt (.switch c cases dflt))) :
    code = .stmt (.switch c cases dflt) := by
  cases code with
  | stmt s => cases s <;> simp_all [SFRel, sfCode, sfStmt]
  | expr e => simp [SFRel, sfCode] at h
  | args es => simp [SFRel, sfCode] at h
  | stmts ss => simp [SFRel, sfCode] at h
  | loop c post body => simp [SFRel, sfCode] at h

set_option linter.unusedSimpArgs false in
theorem SFRel.forLoop_eq {bound : List Ident} {C C' : StorageCache} {code : Code Op}
    {init : Block Op} {c : Expr Op} {post body : Block Op}
    (h : SFRel bound C C' code (.stmt (.forLoop init c post body))) :
    code = .stmt (.forLoop init c post body) := by
  cases code with
  | stmt s => cases s <;> simp_all [SFRel, sfCode, sfStmt]
  | expr e => simp [SFRel, sfCode] at h
  | args es => simp [SFRel, sfCode] at h
  | stmts ss => simp [SFRel, sfCode] at h
  | loop c post body => simp [SFRel, sfCode] at h

set_option linter.unusedSimpArgs false in
theorem SFRel.control_eq {bound : List Ident} {C C' : StorageCache} {code : Code Op}
    {s : Stmt Op} (hs : s = .break ∨ s = .continue ∨ s = .leave)
    (h : SFRel bound C C' code (.stmt s)) : code = .stmt s := by
  rcases hs with rfl | rfl | rfl <;>
    cases code with
    | stmt t => cases t <;> simp_all [SFRel, sfCode, sfStmt]
    | expr e => simp [SFRel, sfCode] at h
    | args es => simp [SFRel, sfCode] at h
    | stmts ss => simp [SFRel, sfCode] at h
    | loop c post body => simp [SFRel, sfCode] at h

theorem hoist_sfStmts (bound : List Ident) (C : StorageCache) :
    ∀ body : Block Op, hoist D (sfStmts bound C body).1 = hoist D body := by
  intro body
  induction body generalizing bound C with
  | nil => rfl
  | cons s rest ih =>
      cases s with
      | block body => simpa [sfStmts, sfStmt, sfNextBound, hoist] using ih bound ([] : StorageCache)
      | funDef n ps rs body =>
          simpa [sfStmts, sfStmt, sfNextBound, hoist] using ih bound C
      | letDecl xs rhs =>
          simpa [sfStmts, sfStmt, sfNextBound, hoist] using ih (xs ++ bound) (sfLet C xs rhs).2
      | assign xs rhs =>
          simpa [sfStmts, sfStmt, sfNextBound, hoist] using ih bound (sfAssign bound C xs rhs).2
      | cond c body =>
          simpa [sfStmts, sfStmt, sfNextBound, hoist] using ih bound
            (if storageStableExpr c && stmtsNoNormal body then C else [])
      | switch c cases dflt =>
          simpa [sfStmts, sfStmt, sfNextBound, hoist] using ih bound ([] : StorageCache)
      | forLoop init c post body =>
          simpa [sfStmts, sfStmt, sfNextBound, hoist] using ih bound ([] : StorageCache)
      | exprStmt e =>
          simpa [sfStmts, sfStmt, sfNextBound, hoist] using ih bound (sfExprStmt C e).2
      | «break» => simpa [sfStmts, sfStmt, sfNextBound, hoist] using ih bound C
      | «continue» => simpa [sfStmts, sfStmt, sfNextBound, hoist] using ih bound C
      | leave => simpa [sfStmts, sfStmt, sfNextBound, hoist] using ih bound C

mutual

theorem stmtNoNormal_sound {s : Stmt Op} (hn : stmtNoNormal s = true)
    (h : Step D funs V st (.stmt s) (.sres V' st' o)) : o ≠ .normal := by
  cases s with
  | «break» => cases h; simp
  | «continue» => cases h; simp
  | leave => cases h; simp
  | block body =>
      simp only [stmtNoNormal] at hn
      cases h with
      | block hb => exact stmtsNoNormal_sound hn hb
  | exprStmt e =>
      cases e with
      | builtin op args =>
          simp only [stmtNoNormal] at hn
          have hopEq : op = .revert := of_decide_eq_true hn
          subst op
          cases h with
          | exprStmt he =>
              cases he with
              | builtinOk ha hop =>
                  simp [builtinWithExternal, stepOp] at hop
                  split at hop <;> simp_all
          | exprStmtHalt he => simp
      | lit l => simp [stmtNoNormal] at hn
      | var x => simp [stmtNoNormal] at hn
      | call fn args => simp [stmtNoNormal] at hn
  | funDef n ps rs body => simp [stmtNoNormal] at hn
  | letDecl xs rhs => simp [stmtNoNormal] at hn
  | assign xs rhs => simp [stmtNoNormal] at hn
  | cond c body => simp [stmtNoNormal] at hn
  | switch c cases dflt => simp [stmtNoNormal] at hn
  | forLoop init c post body => simp [stmtNoNormal] at hn

theorem stmtsNoNormal_sound {ss : List (Stmt Op)} (hn : stmtsNoNormal ss = true)
    (h : Step D funs V st (.stmts ss) (.sres V' st' o)) : o ≠ .normal := by
  cases ss with
  | nil => simp [stmtsNoNormal] at hn
  | cons s rest =>
      simp only [stmtsNoNormal, Bool.or_eq_true] at hn
      cases h with
      | seqCons hs hr =>
          rcases hn with hn | hn
          · exact False.elim ((stmtNoNormal_sound hn hs) rfl)
          · exact stmtsNoNormal_sound hn hr
      | seqStop hs hne => exact hne

end

set_option linter.unusedSimpArgs false in
theorem sf_fwd {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    {code code' : Code Op} {res : Res D} {bound : List Ident}
    {C C' : StorageCache} (h : Step D funs V st code res)
    (hr : SFRel bound C C' code code') (hb : BoundOK V bound)
    (hc : StorageCache.OK V st C) :
    Step D funs V st code' res ∧
      (∀ V' st' o, res = .sres V' st' o → o = .normal →
        BoundOK V' (sfBound bound code) ∧ StorageCache.OK V' st' C') := by
  induction h generalizing bound C C' code' with
  | lit =>
      simp only [SFRel, sfCode, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.lit, by intros; contradiction⟩
  | var hv =>
      simp only [SFRel, sfCode, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.var hv, by intros; contradiction⟩
  | builtinOk ha hop iha =>
      simp only [SFRel, sfCode, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.builtinOk ha hop, by intros; contradiction⟩
  | builtinHalt ha hop iha =>
      simp only [SFRel, sfCode, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.builtinHalt ha hop, by intros; contradiction⟩
  | builtinArgsHalt ha iha =>
      simp only [SFRel, sfCode, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.builtinArgsHalt ha, by intros; contradiction⟩
  | callOk ha hl hlen hbody ho iha ihbody =>
      simp only [SFRel, sfCode, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.callOk ha hl hlen hbody ho, by intros; contradiction⟩
  | callHalt ha hl hlen hbody iha ihbody =>
      simp only [SFRel, sfCode, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.callHalt ha hl hlen hbody, by intros; contradiction⟩
  | callArgsHalt ha iha =>
      simp only [SFRel, sfCode, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.callArgsHalt ha, by intros; contradiction⟩
  | argsNil =>
      simp only [SFRel, sfCode, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.argsNil, by intros; contradiction⟩
  | argsCons hrest he ihrest ihe =>
      simp only [SFRel, sfCode, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.argsCons hrest he, by intros; contradiction⟩
  | argsRestHalt hrest ihrest =>
      simp only [SFRel, sfCode, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.argsRestHalt hrest, by intros; contradiction⟩
  | argsHeadHalt hrest he ihrest ihe =>
      simp only [SFRel, sfCode, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.argsHeadHalt hrest he, by intros; contradiction⟩
  | funDef =>
      simp only [SFRel, sfCode, sfStmt, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.funDef, by
        intro V' st' o heq ho
        injection heq with hV hs hout
        subst hV; subst hs; subst hout
        exact ⟨hb, hc⟩⟩
  | @block funs V st body Vb stb o hbody ihbody =>
      simp only [SFRel, sfCode, sfStmt, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      obtain ⟨hbody', -⟩ := ihbody (bound := bound) (C := C)
        (C' := (sfStmts bound C body).2)
        (code' := .stmts (sfStmts bound C body).1) rfl hb hc
      rw [← hoist_sfStmts bound C body] at hbody'
      refine ⟨Step.block hbody', ?_⟩
      intro V' st' o' hres ho
      injection hres with hV hs hout
      subst hV; subst hs; subst hout
      exact ⟨hb.mono (Step.block hbody), StorageCache.OK.nil _ _⟩
  | letZero =>
      simp only [SFRel, sfCode, sfStmt, sfLet, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.letZero, by
        intro V' st' o heq ho
        injection heq with hV hs hout
        subst hV; subst hs; subst hout
        constructor
        · intro x hx
          simp only [sfBound, dpOut, List.mem_append] at hx
          rw [List.map_append, bindZeros_keys]
          exact hx.elim (fun h => List.mem_append_left _ h)
            (fun h => List.mem_append_right _ (hb x h))
        · exact hc.kill_bindZeros _⟩
  | @letVal funs V st vars e vals st1 he hlen ihe =>
      obtain ⟨e', C'', hp⟩ := sfLet_some C vars e
      simp only [SFRel, sfCode, sfStmt, hp, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      obtain ⟨he', hc'⟩ := sfLet_expr_fwd he hp hc
      refine ⟨Step.letVal he' hlen, ?_⟩
      intro V' st' o hres ho
      injection hres with hV hs hout
      subst hV; subst hs; subst hout
      constructor
      · intro x hx
        simp only [sfBound, dpOut, List.mem_append] at hx
        rw [List.map_append, List.map_fst_zip (by omega)]
        exact hx.elim (fun h => List.mem_append_left _ h)
          (fun h => List.mem_append_right _ (hb x h))
      · exact hc' vals st1 rfl hlen
  | @letHalt funs V st vars e st1 he ihe =>
      obtain ⟨e', C'', hp⟩ := sfLet_some C vars e
      simp only [SFRel, sfCode, sfStmt, hp, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      obtain ⟨he', -⟩ := sfLet_expr_fwd he hp hc
      exact ⟨Step.letHalt he', by intros; simp_all⟩
  | @assignVal funs V st vars e vals st1 he hlen ihe =>
      generalize hp : sfAssign bound C vars e = p
      rcases p with ⟨e', C''⟩
      simp only [SFRel, sfCode, sfStmt, hp, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      obtain ⟨he', hc'⟩ := sfAssign_expr_fwd he hp hc
      refine ⟨Step.assignVal he' hlen, ?_⟩
      intro V' st' o hres ho
      injection hres with hV hs hout
      subst hV; subst hs; subst hout
      exact ⟨hb.afterStmt (Step.assignVal he hlen), hc' vals st1 rfl⟩
  | @assignHalt funs V st vars e st1 he ihe =>
      generalize hp : sfAssign bound C vars e = p
      rcases p with ⟨e', C''⟩
      simp only [SFRel, sfCode, sfStmt, hp, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      obtain ⟨he', -⟩ := sfAssign_expr_fwd he hp hc
      exact ⟨Step.assignHalt he', by intros; simp_all⟩
  | @exprStmt funs V st e st1 he ihe =>
      generalize hp : sfExprStmt C e = p
      rcases p with ⟨e', C''⟩
      simp only [SFRel, sfCode, sfStmt, hp, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      obtain ⟨rfl, hc'⟩ := sfExprStmt_ok he hp hc
      exact ⟨Step.exprStmt he, by
        intro V' st' o hres ho
        injection hres with hV hs hout
        subst hV; subst hs; subst hout
        exact ⟨hb, hc'⟩⟩
  | @exprStmtHalt funs V st e st1 he ihe =>
      generalize hp : sfExprStmt C e = p
      rcases p with ⟨e', C''⟩
      have hfst := sfExprStmt_fst C e
      rw [hp] at hfst
      simp only at hfst
      subst e'
      simp only [SFRel, sfCode, sfStmt, hp, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.exprStmtHalt he, by intros; simp_all⟩
  | @ifTrue funs V st c body cv st1 V' st2 o hcond hnz hbody ihc ihbody =>
      generalize hkeep : (storageStableExpr c && stmtsNoNormal body) = keep
      cases keep with
      | false =>
          simp only [SFRel, sfCode, sfStmt, hkeep, Bool.false_eq_true, if_false,
            Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          obtain ⟨hbody', -⟩ := ihbody (bound := bound) (C := []) (C' := [])
            (code' := .stmt (.block (sfStmts bound [] body).1)) rfl hb
            (StorageCache.OK.nil _ _)
          exact ⟨Step.ifTrue hcond hnz hbody', by
            intro W st' o' hres ho
            injection hres with hV hs hout
            subst hV; subst hs; subst hout
            exact ⟨hb.mono (Step.ifTrue hcond hnz hbody), StorageCache.OK.nil _ _⟩⟩
      | true =>
          simp only [SFRel, sfCode, sfStmt, hkeep, if_true, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          obtain ⟨hbody', -⟩ := ihbody (bound := bound) (C := []) (C' := [])
            (code' := .stmt (.block (sfStmts bound [] body).1)) rfl hb
            (StorageCache.OK.nil _ _)
          refine ⟨Step.ifTrue hcond hnz hbody', ?_⟩
          intro W st' o' hres ho
          have hk : storageStableExpr c = true ∧ stmtsNoNormal body = true := by
            simpa using hkeep
          have hn := hk.2
          exact False.elim ((stmtNoNormal_sound (s := .block body)
            (by simpa [stmtNoNormal] using hn) hbody) (by simp_all))
  | @ifFalse funs V st c body cv st1 hcond hz ihc =>
      generalize hkeep : (storageStableExpr c && stmtsNoNormal body) = keep
      cases keep with
      | false =>
          simp only [SFRel, sfCode, sfStmt, hkeep, Bool.false_eq_true, if_false,
            Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          exact ⟨Step.ifFalse hcond hz, by
            intro W st' o hres ho
            injection hres with hV hs hout
            subst hV; subst hs; subst hout
            exact ⟨hb, StorageCache.OK.nil _ _⟩⟩
      | true =>
          simp only [SFRel, sfCode, sfStmt, hkeep, if_true, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          refine ⟨Step.ifFalse hcond hz, ?_⟩
          intro W st' o hres ho
          injection hres with hV hs hout
          subst hV; subst hs; subst hout
          have hk : storageStableExpr c = true ∧ stmtsNoNormal body = true := by
            simpa using hkeep
          obtain ⟨w, hw⟩ := storageStableExpr_inv hk.1 hcond
          injection hw with hvals hst
          cases hvals; cases hst
          exact ⟨hb, hc⟩
  | @ifHalt funs V st c body st1 hcond ihc =>
      generalize hkeep : (storageStableExpr c && stmtsNoNormal body) = keep
      cases keep <;>
        simp only [SFRel, sfCode, sfStmt, hkeep, Bool.false_eq_true, if_false,
          if_true, Prod.mk.injEq] at hr <;>
        obtain ⟨rfl, rfl⟩ := hr <;>
        exact ⟨Step.ifHalt hcond, by intros; simp_all⟩
  | switchExec hcond hsel ihc ihsel =>
      simp only [SFRel, sfCode, sfStmt, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      refine ⟨Step.switchExec hcond hsel, ?_⟩
      intro W st' o hres ho
      injection hres with hV hs hout
      subst hV; subst hs; subst hout
      exact ⟨hb.mono (Step.switchExec hcond hsel), StorageCache.OK.nil _ _⟩
  | switchHalt hcond ihc =>
      simp only [SFRel, sfCode, sfStmt, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.switchHalt hcond, by intros; simp_all⟩
  | forLoop hinit hloop ihinit ihloop =>
      simp only [SFRel, sfCode, sfStmt, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      refine ⟨Step.forLoop hinit hloop, ?_⟩
      intro W st' o hres ho
      injection hres with hV hs hout
      subst hV; subst hs; subst hout
      exact ⟨hb.mono (Step.forLoop hinit hloop), StorageCache.OK.nil _ _⟩
  | forInitHalt hinit ihinit =>
      simp only [SFRel, sfCode, sfStmt, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.forInitHalt hinit, by intros; simp_all⟩
  | «break» =>
      simp only [SFRel, sfCode, sfStmt, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.break, by intros; simp_all⟩
  | «continue» =>
      simp only [SFRel, sfCode, sfStmt, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.continue, by intros; simp_all⟩
  | leave =>
      simp only [SFRel, sfCode, sfStmt, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.leave, by intros; simp_all⟩
  | seqNil =>
      simp only [SFRel, sfCode, sfStmts, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.seqNil, by
        intro V' st' o heq ho
        injection heq with hV hs hout
        subst hV; subst hs; subst hout
        exact ⟨hb, hc⟩⟩
  | @seqCons funs V st s rest V1 st1 V2 st2 o hs hrest ihs ihrest =>
      generalize hsfp : sfStmt bound C s = p
      rcases p with ⟨s', C1⟩
      simp only [SFRel, sfCode, sfStmts, hsfp, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      obtain ⟨hs', hsok⟩ := ihs (bound := bound) (C := C) (C' := C1)
        (code' := .stmt s') (by simp [SFRel, sfCode, hsfp]) hb hc
      obtain ⟨hb1, hc1⟩ := hsok V1 st1 .normal rfl rfl
      have hbound : sfBound bound (.stmt s) =
          sfNextBound bound s := by
        cases s <;> rfl
      rw [hbound] at hb1
      obtain ⟨hrest', hrok⟩ := ihrest
        (bound := sfNextBound bound s)
        (C := C1)
        (C' := (sfStmts
          (sfNextBound bound s) C1 rest).2)
        (code' := .stmts (sfStmts
          (sfNextBound bound s) C1 rest).1)
        rfl hb1 hc1
      exact ⟨Step.seqCons hs' hrest', by
        intro V' st' o' hres ho
        have hout := hrok V' st' o' hres ho
        have hbounds : sfBound bound (.stmts (s :: rest)) =
            sfBound (sfNextBound bound s)
              (.stmts rest) := by cases s <;> rfl
        rwa [hbounds]⟩
  | @seqStop funs V st s rest V1 st1 o hs hne ihs =>
      generalize hsfp : sfStmt bound C s = p
      rcases p with ⟨s', C1⟩
      simp only [SFRel, sfCode, sfStmts, hsfp, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      obtain ⟨hs', -⟩ := ihs (bound := bound) (C := C) (C' := C1)
        (code' := .stmt s') (by simp [SFRel, sfCode, hsfp]) hb hc
      exact ⟨Step.seqStop hs' hne, by intros; simp_all⟩
  | loopDone hcond hz ihc =>
      simp only [SFRel, sfCode, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.loopDone hcond hz, by
        intro W st' o hres ho
        injection hres with hV hs hout
        subst hV; subst hs; subst hout
        exact ⟨hb, StorageCache.OK.nil _ _⟩⟩
  | loopCondHalt hcond ihc =>
      simp only [SFRel, sfCode, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.loopCondHalt hcond, by intros; simp_all⟩
  | loopStep hcond hnz hbody hob hp hrest ihc ihb ihp ihr =>
      simp only [SFRel, sfCode, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      refine ⟨Step.loopStep hcond hnz hbody hob hp hrest, ?_⟩
      intro W st' o' hres ho
      injection hres with hV hs hout
      subst hV; subst hs; subst hout
      exact ⟨hb.mono (Step.loopStep hcond hnz hbody hob hp hrest), StorageCache.OK.nil _ _⟩
  | loopPostHalt hcond hnz hbody hob hp ihc ihb ihp =>
      simp only [SFRel, sfCode, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.loopPostHalt hcond hnz hbody hob hp, by
        intro W st' o hres ho
        injection hres with _ _ hout
        subst hout
        simp at ho⟩
  | loopBreak hcond hnz hbody ihc ihb =>
      simp only [SFRel, sfCode, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.loopBreak hcond hnz hbody, by
        intro W st' o hres ho
        injection hres with hV hs hout
        subst hV; subst hs; subst hout
        exact ⟨hb.mono hbody, StorageCache.OK.nil _ _⟩⟩
  | loopLeave hcond hnz hbody ihc ihb =>
      simp only [SFRel, sfCode, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.loopLeave hcond hnz hbody, by
        intro W st' o hres ho
        injection hres with _ _ hout
        subst hout
        simp at ho⟩
  | loopBodyHalt hcond hnz hbody ihc ihb =>
      simp only [SFRel, sfCode, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨Step.loopBodyHalt hcond hnz hbody, by
        intro W st' o hres ho
        injection hres with _ _ hout
        subst hout
        simp at ho⟩

set_option linter.unusedSimpArgs false in
theorem sf_bwd {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    {code code' : Code Op} {res : Res D} {bound : List Ident}
    {C C' : StorageCache} (h : Step D funs V st code' res)
    (hr : SFRel bound C C' code code') (hb : BoundOK V bound)
    (hc : StorageCache.OK V st C) :
    Step D funs V st code res := by
  induction h generalizing code bound C C' with
  | lit =>
      rw [hr.expr_eq]
      exact Step.lit
  | var hv =>
      rw [hr.expr_eq]
      exact Step.var hv
  | builtinOk ha hop iha =>
      rw [hr.expr_eq]
      exact Step.builtinOk ha hop
  | builtinHalt ha hop iha =>
      rw [hr.expr_eq]
      exact Step.builtinHalt ha hop
  | builtinArgsHalt ha iha =>
      rw [hr.expr_eq]
      exact Step.builtinArgsHalt ha
  | callOk ha hl hlen hbody ho iha ihbody =>
      rw [hr.expr_eq]
      exact Step.callOk ha hl hlen hbody ho
  | callHalt ha hl hlen hbody iha ihbody =>
      rw [hr.expr_eq]
      exact Step.callHalt ha hl hlen hbody
  | callArgsHalt ha iha =>
      rw [hr.expr_eq]
      exact Step.callArgsHalt ha
  | argsNil =>
      rw [hr.args_eq]
      exact Step.argsNil
  | argsCons hrest he ihrest ihe =>
      rw [hr.args_eq]
      exact Step.argsCons hrest he
  | argsRestHalt hrest ihrest =>
      rw [hr.args_eq]
      exact Step.argsRestHalt hrest
  | argsHeadHalt hrest he ihrest ihe =>
      rw [hr.args_eq]
      exact Step.argsHeadHalt hrest he
  | funDef =>
      cases code with
      | stmt s =>
          cases s <;> simp_all [SFRel, sfCode, sfStmt]
          exact Step.funDef
      | expr e => simp [SFRel, sfCode] at hr
      | args es => simp [SFRel, sfCode] at hr
      | stmts ss => simp [SFRel, sfCode] at hr
      | loop c post body => simp [SFRel, sfCode] at hr
  | block hbody ihbody =>
      cases code with
      | stmt s =>
          cases s with
          | block body =>
              simp only [SFRel, sfCode, sfStmt, Prod.mk.injEq] at hr
              obtain ⟨hcode, hcache⟩ := hr
              injection hcode with hbodyeq
              cases hbodyeq; cases hcache
              have hbody' := ihbody (code := .stmts body) (bound := bound)
                (C := C) (C' := (sfStmts bound C body).2) rfl hb hc
              rw [hoist_sfStmts bound C body] at hbody'
              exact Step.block hbody'
          | funDef n ps rs body => simp [SFRel, sfCode, sfStmt] at hr
          | letDecl xs rhs => simp [SFRel, sfCode, sfStmt] at hr
          | assign xs rhs => simp [SFRel, sfCode, sfStmt] at hr
          | cond c body => simp [SFRel, sfCode, sfStmt] at hr
          | switch c cases dflt => simp [SFRel, sfCode, sfStmt] at hr
          | forLoop init c post body => simp [SFRel, sfCode, sfStmt] at hr
          | exprStmt e => simp [SFRel, sfCode, sfStmt] at hr
          | «break» => simp [SFRel, sfCode, sfStmt] at hr
          | «continue» => simp [SFRel, sfCode, sfStmt] at hr
          | leave => simp [SFRel, sfCode, sfStmt] at hr
      | expr e => simp [SFRel, sfCode] at hr
      | args es => simp [SFRel, sfCode] at hr
      | stmts ss => simp [SFRel, sfCode] at hr
      | loop c post body => simp [SFRel, sfCode] at hr
  | letZero =>
      obtain ⟨rhs, rfl, heq⟩ := hr.let_inv
      cases rhs with
      | none => exact Step.letZero
      | some e =>
          obtain ⟨e', C'', hp⟩ := sfLet_some C _ e
          rw [hp] at heq
          cases heq
  | letVal he hlen ihe =>
      obtain ⟨rhs, rfl, heq⟩ := hr.let_inv
      cases rhs with
      | none => simp [sfLet] at heq
      | some e =>
          exact Step.letVal (sfLet_expr_bwd he heq hc) hlen
  | letHalt he ihe =>
      obtain ⟨rhs, rfl, heq⟩ := hr.let_inv
      cases rhs with
      | none => simp [sfLet] at heq
      | some e => exact Step.letHalt (sfLet_expr_bwd he heq hc)
  | assignVal he hlen ihe =>
      obtain ⟨rhs, rfl, heq⟩ := hr.assign_inv
      exact Step.assignVal (sfAssign_expr_bwd he heq hc) hlen
  | assignHalt he ihe =>
      obtain ⟨rhs, rfl, heq⟩ := hr.assign_inv
      exact Step.assignHalt (sfAssign_expr_bwd he heq hc)
  | exprStmt he ihe =>
      rw [hr.exprStmt_inv]
      exact Step.exprStmt he
  | exprStmtHalt he ihe =>
      rw [hr.exprStmt_inv]
      exact Step.exprStmtHalt he
  | ifTrue hcond hnz hbody ihc ihbody =>
      obtain ⟨body, rfl, hbodyeq, hcache⟩ := hr.cond_inv
      cases hbodyeq
      have hbody' := ihbody (code := .stmt (.block body)) (bound := bound)
        (C := []) (C' := []) rfl hb (StorageCache.OK.nil _ _)
      exact Step.ifTrue hcond hnz hbody'
  | ifFalse hcond hz ihc =>
      obtain ⟨body, rfl, hbodyeq, hcache⟩ := hr.cond_inv
      exact Step.ifFalse hcond hz
  | ifHalt hcond ihc =>
      obtain ⟨body, rfl, hbodyeq, hcache⟩ := hr.cond_inv
      exact Step.ifHalt hcond
  | switchExec hcond hsel ihc ihsel =>
      rw [hr.switch_eq]
      exact Step.switchExec hcond hsel
  | switchHalt hcond ihc =>
      rw [hr.switch_eq]
      exact Step.switchHalt hcond
  | forLoop hinit hloop ihinit ihloop =>
      rw [hr.forLoop_eq]
      exact Step.forLoop hinit hloop
  | forInitHalt hinit ihinit =>
      rw [hr.forLoop_eq]
      exact Step.forInitHalt hinit
  | «break» =>
      rw [hr.control_eq (Or.inl rfl)]
      exact Step.break
  | «continue» =>
      rw [hr.control_eq (Or.inr (Or.inl rfl))]
      exact Step.continue
  | leave =>
      rw [hr.control_eq (Or.inr (Or.inr rfl))]
      exact Step.leave
  | seqNil =>
      rw [hr.stmts_nil_inv]
      exact Step.seqNil
  | @seqCons funs V st s' rest' V1 st1 V2 st2 o hs hrest ihs ihrest =>
      obtain ⟨s, rest, C1, rfl, hsrel, hrestrel⟩ := hr.stmts_cons_inv
      have hhead : SFRel bound C C1 (.stmt s) (.stmt s') := by
        unfold SFRel
        simp only [sfCode]
        rw [hsrel]
      have hs0 := ihs (code := .stmt s) (bound := bound) (C := C) (C' := C1)
        hhead hb hc
      obtain ⟨-, hsok⟩ := sf_fwd hs0 hhead hb hc
      obtain ⟨hb1, hc1⟩ := hsok V1 st1 .normal rfl rfl
      have hbound : sfBound bound (.stmt s) = sfNextBound bound s := by
        cases s <;> rfl
      rw [hbound] at hb1
      have htail : SFRel (sfNextBound bound s) C1 C' (.stmts rest)
          (.stmts rest') := by
        unfold SFRel
        simp only [sfCode]
        rw [hrestrel]
      have hrest0 := ihrest (code := .stmts rest) (bound := sfNextBound bound s)
        (C := C1) (C' := C') htail hb1 hc1
      exact Step.seqCons hs0 hrest0
  | @seqStop funs V st s' rest' V1 st1 o hs hne ihs =>
      obtain ⟨s, rest, C1, rfl, hsrel, hrestrel⟩ := hr.stmts_cons_inv
      have hhead : SFRel bound C C1 (.stmt s) (.stmt s') := by
        unfold SFRel
        simp only [sfCode]
        rw [hsrel]
      have hs0 := ihs (code := .stmt s) (bound := bound) (C := C) (C' := C1)
        hhead hb hc
      exact Step.seqStop hs0 hne
  | loopDone hcond hz ihc =>
      rw [hr.loop_eq]
      exact Step.loopDone hcond hz
  | loopCondHalt hcond ihc =>
      rw [hr.loop_eq]
      exact Step.loopCondHalt hcond
  | loopStep hcond hnz hbody hob hp hrest ihc ihb ihp ihr =>
      rw [hr.loop_eq]
      exact Step.loopStep hcond hnz hbody hob hp hrest
  | loopPostHalt hcond hnz hbody hob hp ihc ihb ihp =>
      rw [hr.loop_eq]
      exact Step.loopPostHalt hcond hnz hbody hob hp
  | loopBreak hcond hnz hbody ihc ihb =>
      rw [hr.loop_eq]
      exact Step.loopBreak hcond hnz hbody
  | loopLeave hcond hnz hbody ihc ihb =>
      rw [hr.loop_eq]
      exact Step.loopLeave hcond hnz hbody
  | loopBodyHalt hcond hnz hbody ihc ihb =>
      rw [hr.loop_eq]
      exact Step.loopBodyHalt hcond hnz hbody

theorem storageForwardShallow_sound : Sound D storageForwardShallowBlock := by
  intro b
  by_cases hfree : storageLayoutFreeStmts b = true
  · simp only [storageForwardShallowBlock, hfree, if_true]
    · intro funs V st V' st' o
      constructor
      · intro h
        cases h with
        | block hb =>
            obtain ⟨hb', -⟩ := sf_fwd hb (bound := []) (C := [])
              (C' := (sfStmts [] [] b).2)
              (code' := .stmts (sfStmts [] [] b).1) rfl
              (BoundOK.nil _) (StorageCache.OK.nil _ _)
            rw [← hoist_sfStmts [] [] b] at hb'
            exact Step.block hb'
      · intro h
        cases h with
        | block hb =>
            rw [hoist_sfStmts [] [] b] at hb
            exact Step.block (sf_bwd hb (bound := []) (C := [])
              (C' := (sfStmts [] [] b).2) (code := .stmts b) rfl
              (BoundOK.nil _) (StorageCache.OK.nil _ _))
  · have hfalse : storageLayoutFreeStmts b = false := Bool.eq_false_of_not_eq_true hfree
    simpa [storageForwardShallowBlock, hfalse] using (EquivBlock.refl b : EquivBlock D b b)

def storageForwardShallow : Pass D where
  run := storageForwardShallowBlock
  sound := storageForwardShallow_sound

set_option linter.unusedVariables false in
mutual

theorem sfFunStmt_equiv : ∀ s : Stmt Op, EquivStmt D s (sfFunStmt s)
  | .block body =>
      EquivBlock.of_stmts_funs (EquivStmts.of_forall₂ (sfFunStmts_forall2 body))
        (sfFunScopeRel body)
  | .funDef n ps rs body =>
      funDef_equiv n ps rs body _
  | .cond c body =>
      EquivStmt.cond_congr (EquivExpr.refl _)
        (EquivBlock.of_stmts_funs (EquivStmts.of_forall₂ (sfFunStmts_forall2 body))
          (sfFunScopeRel body))
  | .switch c cases dflt =>
      EquivStmt.switch_congr (EquivExpr.refl _) (sfFunCases_forall2 cases)
        (sfFunDflt_equiv dflt)
  | .forLoop init c post body => by
      simpa [sfFunStmt, storageForwardShallow] using
        (EquivStmt.forLoop_congr init (EquivExpr.refl c)
        ((EquivBlock.of_stmts_funs
          (EquivStmts.of_forall₂ (sfFunStmts_forall2 post))
          (sfFunScopeRel post)).trans
            (storageForwardShallow.sound (sfFunStmts post)))
        ((EquivBlock.of_stmts_funs
          (EquivStmts.of_forall₂ (sfFunStmts_forall2 body))
          (sfFunScopeRel body)).trans
            (storageForwardShallow.sound (sfFunStmts body))))
  | .letDecl xs rhs => EquivStmt.refl _
  | .assign xs rhs => EquivStmt.refl _
  | .exprStmt e => EquivStmt.refl _
  | .break => EquivStmt.refl _
  | .continue => EquivStmt.refl _
  | .leave => EquivStmt.refl _

theorem sfFunStmts_forall2 : ∀ ss : List (Stmt Op),
    List.Forall₂ (EquivStmt D) ss (sfFunStmts ss)
  | [] => .nil
  | s :: rest => .cons (sfFunStmt_equiv s) (sfFunStmts_forall2 rest)

theorem sfFunCases_forall2 : ∀ cs : List (Literal × Block Op),
    List.Forall₂ (fun p q => p.1 = q.1 ∧ EquivBlock D p.2 q.2) cs (sfFunCases cs)
  | [] => .nil
  | (l, body) :: rest =>
      .cons ⟨rfl, EquivBlock.of_stmts_funs
        (EquivStmts.of_forall₂ (sfFunStmts_forall2 body)) (sfFunScopeRel body)⟩
        (sfFunCases_forall2 rest)

theorem sfFunDflt_equiv : ∀ dflt : Option (Block Op),
    EquivBlock D (dflt.getD []) ((sfFunDflt dflt).getD [])
  | none => EquivBlock.refl _
  | some body => by
      simpa [sfFunDflt] using EquivBlock.of_stmts_funs
        (EquivStmts.of_forall₂ (sfFunStmts_forall2 body)) (sfFunScopeRel body)

theorem sfFunScopeRel : ∀ ss : List (Stmt Op),
    ScopeRel D (hoist D ss) (hoist D (sfFunStmts ss))
  | [] => .nil
  | .funDef n ps rs body :: rest =>
      .cons ⟨rfl, rfl, rfl,
        (EquivBlock.of_stmts_funs (EquivStmts.of_forall₂ (sfFunStmts_forall2 body))
          (sfFunScopeRel body)).trans (storageForwardShallow.sound (sfFunStmts body))⟩
        (sfFunScopeRel rest)
  | .block body :: rest => sfFunScopeRel rest
  | .letDecl xs rhs :: rest => sfFunScopeRel rest
  | .assign xs rhs :: rest => sfFunScopeRel rest
  | .cond c body :: rest => sfFunScopeRel rest
  | .switch c cases dflt :: rest => sfFunScopeRel rest
  | .forLoop init c post body :: rest => sfFunScopeRel rest
  | .exprStmt e :: rest => sfFunScopeRel rest
  | .break :: rest => sfFunScopeRel rest
  | .continue :: rest => sfFunScopeRel rest
  | .leave :: rest => sfFunScopeRel rest

end

theorem storageForward_sound : Sound D storageForwardBlock := by
  intro b
  exact (EquivBlock.of_stmts_funs (EquivStmts.of_forall₂ (sfFunStmts_forall2 b))
    (sfFunScopeRel b)).trans (storageForwardShallow.sound (sfFunStmts b))

def storageForward : Pass D where
  run := storageForwardBlock
  sound := storageForward_sound

end YulEvmCompiler.Optimizer
