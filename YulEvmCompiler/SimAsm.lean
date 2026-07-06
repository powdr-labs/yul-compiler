import YulEvmCompiler.AsmSem
import YulEvmCompiler.Compile
import YulSemantics.BigStep

/-!
# YulEvmCompiler.SimAsm

**Phase A**: the simulation from the Yul big-step semantics to the Asm
semantics. Everything here is byte-free and gas-free: fragments are placed
by list appends (`prog = pre ++ asm ++ c`), jumps land at labels via
`findLabel`, and built-ins step by the dialect's own `stepOp`.

The fragment-execution shapes (`ASimE`/`ASimS`/… below) mirror the
milestone-2 `SimE`/`SimS`, with two new ingredients:

* stack values are `AVal`s — expression temporaries `τ` may contain
  function return addresses, so only their *length* is constrained;
* the non-local outcomes (`break`/`continue`/`leave`) get their own shape
  `ASimNL`: pop down to the context's depth, jump to the context's label.

See `PLAN.md` § "Phase A detailed design" for the roadmap.
-/

namespace YulEvmCompiler.SimA

open YulEvmCompiler
open YulSemantics (Expr Stmt Block Ident VEnv Outcome)
open YulSemantics.EVM (U256 EvmState Op stepOp litValue)

/-- The Yul EVM dialect (as in `OpStep.yul`, redeclared to keep phase A
independent of the EVM-side modules). -/
abbrev yulD : YulSemantics.Dialect := YulSemantics.EVM.evm

/-- The Asm-stack image of a variable environment: the values as words,
innermost binding on top. -/
def wimg (V : VEnv yulD) : List AVal := V.map (fun p => .word p.2)

/-- The layout a variable environment realizes: its names. -/
def names (V : VEnv yulD) : List Ident := V.map Prod.fst

/-- Keep the outermost `depth` bindings (the semantics' `restore`, by
target length). -/
def trim (depth : Nat) (V : VEnv yulD) : VEnv yulD :=
  V.drop (V.length - depth)

@[simp] theorem wimg_nil : wimg [] = [] := rfl
@[simp] theorem wimg_cons (p : Ident × U256) (V : VEnv yulD) :
    wimg (p :: V) = .word p.2 :: wimg V := rfl
@[simp] theorem wimg_length (V : VEnv yulD) : (wimg V).length = V.length := by
  simp [wimg]
theorem wimg_append (V W : VEnv yulD) : wimg (V ++ W) = wimg V ++ wimg W := by
  simp [wimg]

@[simp] theorem names_nil : names [] = [] := rfl
@[simp] theorem names_cons (p : Ident × U256) (V : VEnv yulD) :
    names (p :: V) = p.1 :: names V := rfl
@[simp] theorem names_length (V : VEnv yulD) : (names V).length = V.length := by
  simp [names]
theorem names_append (V W : VEnv yulD) : names (V ++ W) = names V ++ names W := by
  simp [names]

theorem wimg_drop (n : Nat) (V : VEnv yulD) :
    wimg (V.drop n) = (wimg V).drop n := by
  simp [wimg, List.map_drop]

theorem names_drop (n : Nat) (V : VEnv yulD) :
    names (V.drop n) = (names V).drop n := by
  simp [names, List.map_drop]

/-! ### Fragment-execution shapes

All are parameterized by the whole program `prog` and quantify over the
fragment's placement `prog = pre ++ asm ++ c`. -/

/-- A compiled *expression* fragment: pushes `vs` (as words) over the
temporaries `τ` (length `off`; may contain return addresses), the variable
region, and an arbitrary rest. -/
def ASimE (prog : List Asm) (yst : EvmState) (V : VEnv yulD) (off : Nat)
    (asm : List Asm) (vs : List U256) (yst' : EvmState) : Prop :=
  ∀ (pre c : List Asm) (τ σ : List AVal),
    prog = pre ++ asm ++ c → τ.length = off →
    ASteps prog ⟨asm ++ c, τ ++ wimg V ++ σ, yst⟩
      ⟨c, words vs ++ (τ ++ wimg V ++ σ), yst'⟩

/-- Like `ASimE`, but evaluation halts. -/
def ASimEHalt (prog : List Asm) (yst : EvmState) (V : VEnv yulD) (off : Nat)
    (asm : List Asm) (yst' : EvmState) : Prop :=
  ∀ (pre c : List Asm) (τ σ : List AVal),
    prog = pre ++ asm ++ c → τ.length = off →
    ∃ conf, ASteps prog ⟨asm ++ c, τ ++ wimg V ++ σ, yst⟩ conf
      ∧ AHalt prog conf yst'

/-- A compiled *statement* fragment with a normal outcome: the variable
region evolves from `V` to `V'`. -/
def ASimS (prog : List Asm) (yst : EvmState) (V : VEnv yulD)
    (asm : List Asm) (yst' : EvmState) (V' : VEnv yulD) : Prop :=
  ∀ (pre c : List Asm) (σ : List AVal),
    prog = pre ++ asm ++ c →
    ASteps prog ⟨asm ++ c, wimg V ++ σ, yst⟩ ⟨c, wimg V' ++ σ, yst'⟩

/-- Like `ASimS`, but execution halts. -/
def ASimSHalt (prog : List Asm) (yst : EvmState) (V : VEnv yulD)
    (asm : List Asm) (yst' : EvmState) : Prop :=
  ∀ (pre c : List Asm) (σ : List AVal),
    prog = pre ++ asm ++ c →
    ∃ conf, ASteps prog ⟨asm ++ c, wimg V ++ σ, yst⟩ conf
      ∧ AHalt prog conf yst'

/-- A *non-local exit* (`break`/`continue`/`leave`): pop the region down
to the context's `depth` and jump to the context's label `l`, arriving at
the suffix after it. The rest `σ` is untouched — it is the same σ the
enclosing loop/function frame started with. -/
def ASimNL (prog : List Asm) (yst : EvmState) (V : VEnv yulD)
    (asm : List Asm) (yst' : EvmState) (V' : VEnv yulD)
    (l : Label) (depth : Nat) : Prop :=
  ∀ (pre c cL : List Asm) (σ : List AVal),
    prog = pre ++ asm ++ c → findLabel l prog = some cL →
    ASteps prog ⟨asm ++ c, wimg V ++ σ, yst⟩
      ⟨cL, wimg (trim depth V') ++ σ, yst'⟩

/-! ### Structural composition -/

theorem ASimS.nil {prog : List Asm} {yst : EvmState} {V : VEnv yulD} :
    ASimS prog yst V [] yst V := by
  intro pre c σ hp
  exact .refl _

/-- Sequence two statement fragments. -/
theorem ASimS.comp {prog : List Asm} {yst yst1 yst2 : EvmState}
    {V V1 V2 : VEnv yulD} {a1 a2 : List Asm}
    (h1 : ASimS prog yst V a1 yst1 V1) (h2 : ASimS prog yst1 V1 a2 yst2 V2) :
    ASimS prog yst V (a1 ++ a2) yst2 V2 := by
  intro pre c σ hp
  rw [List.append_assoc]
  exact (h1 pre (a2 ++ c) σ (by rw [hp]; simp)).trans
    (h2 (pre ++ a1) c σ (by rw [hp]; simp))

/-- A statement fragment followed by a halting one. -/
theorem ASimS.compHalt {prog : List Asm} {yst yst1 yst2 : EvmState}
    {V V1 : VEnv yulD} {a1 a2 : List Asm}
    (h1 : ASimS prog yst V a1 yst1 V1) (h2 : ASimSHalt prog yst1 V1 a2 yst2) :
    ASimSHalt prog yst V (a1 ++ a2) yst2 := by
  intro pre c σ hp
  obtain ⟨conf, hsteps, hhalt⟩ := h2 (pre ++ a1) c σ (by rw [hp]; simp)
  refine ⟨conf, ?_, hhalt⟩
  rw [List.append_assoc]
  exact (h1 pre (a2 ++ c) σ (by rw [hp]; simp)).trans hsteps

/-- A statement fragment followed by a non-local exit. -/
theorem ASimS.compNL {prog : List Asm} {yst yst1 yst2 : EvmState}
    {V V1 V2 : VEnv yulD} {a1 a2 : List Asm} {l : Label} {depth : Nat}
    (h1 : ASimS prog yst V a1 yst1 V1)
    (h2 : ASimNL prog yst1 V1 a2 yst2 V2 l depth) :
    ASimNL prog yst V (a1 ++ a2) yst2 V2 l depth := by
  intro pre c cL σ hp hfind
  rw [List.append_assoc]
  exact (h1 pre (a2 ++ c) σ (by rw [hp]; simp)).trans
    (h2 (pre ++ a1) c cL σ (by rw [hp]; simp) hfind)

/-- A halting fragment ignores anything appended after it. -/
theorem ASimSHalt.extend {prog : List Asm} {yst yst' : EvmState}
    {V : VEnv yulD} {a1 : List Asm}
    (h : ASimSHalt prog yst V a1 yst') (a2 : List Asm) :
    ASimSHalt prog yst V (a1 ++ a2) yst' := by
  intro pre c σ hp
  obtain ⟨conf, hsteps, hhalt⟩ := h pre (a2 ++ c) σ (by rw [hp]; simp)
  refine ⟨conf, ?_, hhalt⟩
  rw [List.append_assoc]
  exact hsteps

/-- A non-local exit ignores anything appended after it. -/
theorem ASimNL.extend {prog : List Asm} {yst yst' : EvmState}
    {V V' : VEnv yulD} {a1 : List Asm} {l : Label} {depth : Nat}
    (h : ASimNL prog yst V a1 yst' V' l depth) (a2 : List Asm) :
    ASimNL prog yst V (a1 ++ a2) yst' V' l depth := by
  intro pre c cL σ hp hfind
  rw [List.append_assoc]
  exact h pre (a2 ++ c) cL σ (by rw [hp]; simp) hfind

/-- An expression fragment in statement position (`off = 0`, no values). -/
theorem ASimE.toASimS {prog : List Asm} {yst yst' : EvmState}
    {V : VEnv yulD} {asm : List Asm}
    (h : ASimE prog yst V 0 asm [] yst') :
    ASimS prog yst V asm yst' V := by
  intro pre c σ hp
  simpa using h pre c [] σ hp rfl

/-- `let x := e`: the produced value becomes the innermost variable. -/
theorem ASimE.toASimSLet {prog : List Asm} {yst yst' : EvmState}
    {V : VEnv yulD} {asm : List Asm} {x : Ident} {v : U256}
    (h : ASimE prog yst V 0 asm [v] yst') :
    ASimS prog yst V asm yst' ((x, v) :: V) := by
  intro pre c σ hp
  show ASteps prog ⟨asm ++ c, wimg V ++ σ, yst⟩
    ⟨c, .word v :: (wimg V ++ σ), yst'⟩
  simpa using h pre c [] σ hp rfl

/-- Zipping names with equally-many values gives the values' stack image. -/
theorem wimg_zip : ∀ (xs : List Ident) (vs : List U256),
    xs.length = vs.length → wimg (xs.zip vs) = words vs := by
  intro xs
  induction xs with
  | nil => intro vs h; cases vs with | nil => rfl | cons => simp at h
  | cons x xs ih =>
    intro vs h
    cases vs with
    | nil => simp at h
    | cons v vs =>
      have hlen : xs.length = vs.length := by simpa using h
      show wimg ((x, v) :: xs.zip vs) = words (v :: vs)
      rw [wimg_cons, ih vs hlen]
      rfl

/-- Zipping names with equally-many values keeps the names as the layout. -/
theorem names_zip : ∀ (xs : List Ident) (vs : List U256),
    xs.length = vs.length → names (xs.zip vs) = xs := by
  intro xs
  induction xs with
  | nil => intro vs _; rfl
  | cons x xs ih =>
    intro vs h
    cases vs with
    | nil => simp at h
    | cons v vs =>
      have hlen : xs.length = vs.length := by simpa using h
      show names ((x, v) :: xs.zip vs) = x :: xs
      rw [names_cons, ih vs hlen]

/-- `let x₁, …, xₖ := e`: the produced values become the innermost
variables, already in layout order. -/
theorem ASimE.toASimSLetMany {prog : List Asm} {yst yst' : EvmState}
    {V : VEnv yulD} {asm : List Asm} {xs : List Ident} {vs : List U256}
    (hlen : xs.length = vs.length)
    (h : ASimE prog yst V 0 asm vs yst') :
    ASimS prog yst V asm yst' (xs.zip vs ++ V) := by
  intro pre c σ hp
  have hsteps := h pre c [] σ hp rfl
  rw [wimg_append, wimg_zip xs vs hlen]
  simpa using hsteps

/-- A halting expression fragment in statement position. -/
theorem ASimEHalt.toASimSHalt {prog : List Asm} {yst yst' : EvmState}
    {V : VEnv yulD} {asm : List Asm}
    (h : ASimEHalt prog yst V 0 asm yst') :
    ASimSHalt prog yst V asm yst' := by
  intro pre c σ hp
  simpa using h pre c [] σ hp rfl

/-! ### Leaf steps -/

/-- Pushing a literal. -/
theorem asimE_push {prog : List Asm} {yst : EvmState} {V : VEnv yulD}
    {off : Nat} (v : U256) :
    ASimE prog yst V off [.push v] [v] yst := by
  intro pre c τ σ hp hτ
  exact .single (.push)

/-- Sequence an expression fragment with a later argument's fragment (the
earlier values become temporaries for the later one). -/
theorem ASimE.compArgs {prog : List Asm} {yst yst1 yst2 : EvmState}
    {V : VEnv yulD} {off k : Nat} {a1 a2 : List Asm}
    {vs : List U256} {v : U256}
    (hlen : vs.length = k)
    (h1 : ASimE prog yst V off a1 vs yst1)
    (h2 : ASimE prog yst1 V (off + k) a2 [v] yst2) :
    ASimE prog yst V off (a1 ++ a2) (v :: vs) yst2 := by
  intro pre c τ σ hp hτ
  rw [List.append_assoc]
  refine (h1 pre (a2 ++ c) τ σ (by rw [hp]; simp) hτ).trans ?_
  have h2' := h2 (pre ++ a1) c (words vs ++ τ) σ (by rw [hp]; simp)
    (by simp [hlen, hτ, Nat.add_comm])
  show ASteps prog ⟨a2 ++ c, words vs ++ (τ ++ wimg V ++ σ), yst1⟩
    ⟨c, .word v :: (words vs ++ (τ ++ wimg V ++ σ)), yst2⟩
  simpa [List.append_assoc] using h2'

/-- An expression fragment followed by a halting one. -/
theorem ASimE.compArgsHalt {prog : List Asm} {yst yst1 yst2 : EvmState}
    {V : VEnv yulD} {off k : Nat} {a1 a2 : List Asm} {vs : List U256}
    (hlen : vs.length = k)
    (h1 : ASimE prog yst V off a1 vs yst1)
    (h2 : ASimEHalt prog yst1 V (off + k) a2 yst2) :
    ASimEHalt prog yst V off (a1 ++ a2) yst2 := by
  intro pre c τ σ hp hτ
  obtain ⟨conf, hsteps, hhalt⟩ := h2 (pre ++ a1) c (words vs ++ τ) σ
    (by rw [hp]; simp) (by simp [hlen, hτ, Nat.add_comm])
  refine ⟨conf, ?_, hhalt⟩
  rw [List.append_assoc]
  refine (h1 pre (a2 ++ c) τ σ (by rw [hp]; simp) hτ).trans ?_
  simpa [List.append_assoc] using hsteps

/-- A halting expression fragment ignores anything appended after it. -/
theorem ASimEHalt.extend {prog : List Asm} {yst yst' : EvmState}
    {V : VEnv yulD} {off : Nat} {a1 : List Asm}
    (h : ASimEHalt prog yst V off a1 yst') (a2 : List Asm) :
    ASimEHalt prog yst V off (a1 ++ a2) yst' := by
  intro pre c τ σ hp hτ
  obtain ⟨conf, hsteps, hhalt⟩ := h pre (a2 ++ c) τ σ (by rw [hp]; simp) hτ
  refine ⟨conf, ?_, hhalt⟩
  rw [List.append_assoc]
  exact hsteps

/-- The built-in step, non-halting: consume the argument words (which sit
as the innermost temporaries), push the results. -/
theorem asimE_op {prog : List Asm} {yst yst1 yst2 : EvmState}
    {V : VEnv yulD} {off : Nat} {asm : List Asm} {yop : Op}
    {args rets : List U256}
    (hargs : ASimE prog yst V off asm args yst1)
    (hstep : stepOp yop args yst1 = some (.ok rets yst2)) :
    ASimE prog yst V off (asm ++ [.op yop]) rets yst2 := by
  intro pre c τ σ hp hτ
  rw [List.append_assoc]
  refine (hargs pre ([.op yop] ++ c) τ σ (by rw [hp]; simp) hτ).trans ?_
  have hstep' : AStep prog
      ⟨.op yop :: c, words args ++ (τ ++ wimg V ++ σ), yst1⟩
      ⟨c, words rets ++ (τ ++ wimg V ++ σ), yst2⟩ := .op hstep
  exact .single hstep'

/-- The built-in step, halting. -/
theorem asimE_opHalt {prog : List Asm} {yst yst1 yst2 : EvmState}
    {V : VEnv yulD} {off : Nat} {asm : List Asm} {yop : Op}
    {args : List U256}
    (hargs : ASimE prog yst V off asm args yst1)
    (hstep : stepOp yop args yst1 = some (.halt yst2)) :
    ASimEHalt prog yst V off (asm ++ [.op yop]) yst2 := by
  intro pre c τ σ hp hτ
  refine ⟨_, ?_, .op (c := c) (σ := τ ++ wimg V ++ σ) hstep⟩
  rw [List.append_assoc]
  exact hargs pre ([.op yop] ++ c) τ σ (by rw [hp]; simp) hτ

/-! ### The variable region: get/set agreement -/

private theorem findIdx?_lt {α : Type} (p : α → Bool) :
    ∀ {l : List α} {idx : Nat}, l.findIdx? p = some idx → idx < l.length := by
  intro l
  induction l with
  | nil => intro idx h; simp at h
  | cons a l ih =>
    intro idx h
    rw [List.findIdx?_cons] at h
    by_cases hp : p a
    · rw [if_pos hp] at h
      simp at h
      simp
      omega
    · rw [if_neg hp] at h
      obtain ⟨idx', hidx', rfl⟩ := Option.map_eq_some_iff.mp h
      have := ih hidx'
      simp
      omega

/-- The value the semantics reads for `x` sits at the compiled index in the
stack image. -/
theorem wimg_get {V : VEnv yulD} {x : Ident} {v : U256} {idx : Nat}
    (hget : YulSemantics.VEnv.get V x = some v)
    (hidx : (names V).findIdx? (fun y => y = x) = some idx) :
    (wimg V)[idx]? = some (.word v) := by
  induction V generalizing idx with
  | nil => simp [YulSemantics.VEnv.get] at hget
  | cons p V ih =>
    obtain ⟨y, w⟩ := p
    rw [show names ((y, w) :: V) = y :: names V from rfl,
      List.findIdx?_cons] at hidx
    by_cases hxy : y = x
    · rw [if_pos (by simpa using hxy)] at hidx
      have hidx0 : idx = 0 := by simpa using hidx.symm
      subst hidx0
      have hv : w = v := by
        unfold YulSemantics.VEnv.get at hget
        rw [List.find?_cons_of_pos (by simpa using hxy)] at hget
        simpa using hget
      subst hv
      rfl
    · rw [if_neg (by simpa using hxy)] at hidx
      obtain ⟨idx', hidx', rfl⟩ := Option.map_eq_some_iff.mp hidx
      have hget' : YulSemantics.VEnv.get V x = some v := by
        unfold YulSemantics.VEnv.get at hget ⊢
        rwa [List.find?_cons_of_neg (by simpa using hxy)] at hget
      exact ih hget' hidx'

/-- `VEnv.set` keeps the layout. -/
theorem names_set (V : VEnv yulD) (x : Ident) (v : U256) :
    names (YulSemantics.VEnv.set V x v) = names V := by
  induction V with
  | nil => rfl
  | cons p V ih =>
    obtain ⟨y, w⟩ := p
    unfold YulSemantics.VEnv.set
    by_cases hxy : y = x
    · rw [if_pos hxy]
      subst hxy
      rfl
    · rw [if_neg hxy]
      show y :: names (YulSemantics.VEnv.set V x v) = y :: names V
      rw [ih]

/-- `VEnv.setMany` keeps the layout (it is a fold of `set`). -/
theorem names_setMany (V : VEnv yulD) (xs : List Ident) (vs : List U256) :
    names (YulSemantics.VEnv.setMany V xs vs) = names V := by
  have h : ∀ (l : List (Ident × U256)) (W : VEnv yulD),
      names (l.foldl (fun acc p => YulSemantics.VEnv.set acc p.1 p.2) W)
        = names W := by
    intro l
    induction l with
    | nil => intro W; rfl
    | cons p l ih => intro W; rw [List.foldl_cons, ih]; exact names_set W p.1 p.2
  exact h (xs.zip vs) V

/-- `VEnv.setMany` keeps the region length. -/
theorem length_setMany (V : VEnv yulD) (xs : List Ident) (vs : List U256) :
    (YulSemantics.VEnv.setMany V xs vs).length = V.length := by
  have := congrArg List.length (names_setMany V xs vs)
  simpa using this

/-- `VEnv.set` updates the stack image at the compiled index. -/
theorem wimg_set {V : VEnv yulD} {x : Ident} (v : U256) {idx : Nat}
    (hidx : (names V).findIdx? (fun y => y = x) = some idx) :
    wimg (YulSemantics.VEnv.set V x v) = (wimg V).set idx (.word v) := by
  induction V generalizing idx with
  | nil => rfl
  | cons p V ih =>
    obtain ⟨y, w⟩ := p
    rw [show names ((y, w) :: V) = y :: names V from rfl,
      List.findIdx?_cons] at hidx
    unfold YulSemantics.VEnv.set
    by_cases hxy : y = x
    · rw [if_pos hxy]
      rw [if_pos (by simpa using hxy)] at hidx
      have hidx0 : idx = 0 := by simpa using hidx.symm
      subst hidx0
      rfl
    · rw [if_neg hxy]
      rw [if_neg (by simpa using hxy)] at hidx
      obtain ⟨idx', hidx', rfl⟩ := Option.map_eq_some_iff.mp hidx
      show .word w :: wimg (YulSemantics.VEnv.set V x v)
        = (.word w :: wimg V).set (idx' + 1) (.word v)
      rw [ih hidx']
      rfl

/-- Split a list at a `getElem?`-hit. -/
private theorem split_at_getElem {α : Type} {l : List α} {idx : Nat} {v : α}
    (h : l[idx]? = some v) :
    l = l.take idx ++ v :: l.drop (idx + 1) ∧ (l.take idx).length = idx := by
  have hlt : idx < l.length := by
    by_contra hge
    rw [List.getElem?_eq_none_iff.mpr (by omega)] at h
    simp at h
  have hv : l[idx]'hlt = v := by
    rw [List.getElem?_eq_getElem hlt] at h
    simpa using h
  constructor
  · conv_lhs => rw [← List.take_append_drop idx l]
    rw [List.drop_eq_getElem_cons hlt, hv]
  · simp
    omega

/-- Setting at the seam of an append replaces the head of the right part. -/
private theorem set_at_append' {α : Type} {τ : List α} {idx : Nat}
    (h : τ.length = idx) (y x : α) (ρ : List α) :
    (τ ++ y :: ρ).set idx x = τ ++ x :: ρ := by
  subst h
  induction τ with
  | nil => rfl
  | cons t τ ih =>
    show t :: (τ ++ y :: ρ).set τ.length x = _
    rw [ih]
    rfl

/-- Reading a variable: `DUP(off + idx + 1)` fetches its image. -/
theorem asimE_var {prog : List Asm} {yst : EvmState} {V : VEnv yulD}
    {x : Ident} {v : U256} {off idx : Nat} (h16 : off + idx < 16)
    (hget : YulSemantics.VEnv.get V x = some v)
    (hidx : (names V).findIdx? (fun y => y = x) = some idx) :
    ASimE prog yst V off [.dup ⟨off + idx, h16⟩] [v] yst := by
  intro pre c τ σ hp hτ
  obtain ⟨hsplit, hlen⟩ := split_at_getElem (wimg_get hget hidx)
  have hstk : τ ++ wimg V ++ σ
      = (τ ++ (wimg V).take idx)
        ++ AVal.word v :: ((wimg V).drop (idx + 1) ++ σ) := by
    conv_lhs => rw [hsplit]
    simp
  have hstep : AStep prog
      ⟨.dup ⟨off + idx, h16⟩ :: c,
        (τ ++ (wimg V).take idx)
          ++ AVal.word v :: ((wimg V).drop (idx + 1) ++ σ), yst⟩
      ⟨c, AVal.word v :: ((τ ++ (wimg V).take idx)
          ++ AVal.word v :: ((wimg V).drop (idx + 1) ++ σ)), yst⟩ :=
    .dup (by simp [hlen, hτ])
  rw [show ([Asm.dup ⟨off + idx, h16⟩] ++ c) = Asm.dup ⟨off + idx, h16⟩ :: c
    from rfl, hstk]
  exact .single (by simpa using hstep)

/-- Assigning a variable: `SWAP(idx+1); POP` writes the computed value into
its slot. -/
theorem asimS_assign {prog : List Asm} {yst yst' : EvmState} {V : VEnv yulD}
    {x : Ident} {v : U256} {asm : List Asm} {idx : Nat} (h16 : idx < 16)
    (hidx : (names V).findIdx? (fun y => y = x) = some idx)
    (he : ASimE prog yst V 0 asm [v] yst') :
    ASimS prog yst V (asm ++ [.swap ⟨idx, h16⟩, .pop]) yst'
      (YulSemantics.VEnv.set V x v) := by
  intro pre c σ hp
  rw [List.append_assoc]
  show ASteps prog ⟨asm ++ (.swap ⟨idx, h16⟩ :: .pop :: c), wimg V ++ σ, yst⟩
    ⟨c, wimg (YulSemantics.VEnv.set V x v) ++ σ, yst'⟩
  have h1 : ASteps prog
      ⟨asm ++ (.swap ⟨idx, h16⟩ :: .pop :: c), wimg V ++ σ, yst⟩
      ⟨.swap ⟨idx, h16⟩ :: .pop :: c, .word v :: (wimg V ++ σ), yst'⟩ := by
    simpa using he pre (.swap ⟨idx, h16⟩ :: .pop :: c) [] σ (by rw [hp]; simp) rfl
  refine h1.trans ?_
  -- decompose the region at idx
  have hgetV : ∃ w, (wimg V)[idx]? = some w := by
    have hlt : idx < V.length := by simpa using findIdx?_lt _ hidx
    exact ⟨(wimg V)[idx]'(by simpa using hlt), List.getElem?_eq_getElem _⟩
  obtain ⟨w, hw⟩ := hgetV
  obtain ⟨hsplit, hlen⟩ := split_at_getElem hw
  have hstk : wimg V ++ σ
      = (wimg V).take idx ++ w :: ((wimg V).drop (idx + 1) ++ σ) := by
    conv_lhs => rw [hsplit]
    simp
  -- SWAP(idx+1)
  have hswap : AStep prog
      ⟨.swap ⟨idx, h16⟩ :: (.pop :: c),
        .word v :: ((wimg V).take idx ++ w :: ((wimg V).drop (idx + 1) ++ σ)),
        yst'⟩
      ⟨.pop :: c,
        w :: ((wimg V).take idx
          ++ .word v :: ((wimg V).drop (idx + 1) ++ σ)), yst'⟩ :=
    .swap (by simp [hlen])
  -- POP
  have hpop : AStep prog
      ⟨.pop :: c,
        w :: ((wimg V).take idx
          ++ .word v :: ((wimg V).drop (idx + 1) ++ σ)), yst'⟩
      ⟨c, (wimg V).take idx ++ .word v :: ((wimg V).drop (idx + 1) ++ σ),
        yst'⟩ := .pop
  have hfinal : (wimg V).take idx ++ .word v :: ((wimg V).drop (idx + 1) ++ σ)
      = wimg (YulSemantics.VEnv.set V x v) ++ σ := by
    rw [wimg_set v hidx]
    conv_rhs => rw [hsplit]
    rw [set_at_append' hlen]
    simp
  rw [hstk]
  exact (ASteps.single hswap).trans ((ASteps.single hpop).trans
    (by rw [hfinal]; exact .refl _))

/-- Executing a multi-assignment's store sequence: with `xs.length` values
`vs` stacked on top of the region (first target's value on top), each
`swap;pop` writes one into its slot, ending at `setMany V xs vs`. -/
theorem assigns_exec {prog : List Asm} {yst : EvmState} :
    ∀ (xs : List Ident) (vs : List U256) (V : VEnv yulD) (acode : List Asm),
      xs.length = vs.length →
      compileAssigns (names V) xs = some acode →
      ∀ (pre c : List Asm) (σ : List AVal),
        prog = pre ++ acode ++ c →
        ASteps prog ⟨acode ++ c, words vs ++ wimg V ++ σ, yst⟩
          ⟨c, wimg (YulSemantics.VEnv.setMany V xs vs) ++ σ, yst⟩ := by
  intro xs
  induction xs with
  | nil =>
    intro vs V acode hlen hac pre c σ hp
    cases vs with
    | cons v vs => simp at hlen
    | nil =>
      simp only [compileAssigns, Option.some.injEq] at hac
      subst hac
      show ASteps prog ⟨[] ++ c, words [] ++ wimg V ++ σ, yst⟩
        ⟨c, wimg (YulSemantics.VEnv.setMany V [] []) ++ σ, yst⟩
      simp only [words, List.map_nil, List.nil_append]
      exact .refl _
  | cons x xs ih =>
    intro vs V acode hlen hac pre c σ hp
    cases vs with
    | nil => simp at hlen
    | cons v vs =>
      have hlen' : xs.length = vs.length := by simpa using hlen
      simp only [compileAssigns, Option.bind_eq_bind] at hac
      obtain ⟨idx, hidx, hac2⟩ := Option.bind_eq_some_iff.mp hac
      by_cases h16 : idx + xs.length < 16
      · rw [dif_pos h16] at hac2
        obtain ⟨rest, hrest, hac3⟩ := Option.bind_eq_some_iff.mp hac2
        simp only [Option.some.injEq] at hac3
        subst hac3
        -- locate `x`'s slot inside the region image
        have hlt : idx < (wimg V).length := by
          have := findIdx?_lt _ hidx; simpa using this
        obtain ⟨w, hw⟩ : ∃ w, (wimg V)[idx]? = some w :=
          ⟨(wimg V)[idx]'hlt, List.getElem?_eq_getElem _⟩
        obtain ⟨hsplitV, hlenV⟩ := split_at_getElem hw
        -- the store index reaches past the `vs` still stacked above
        have hAlen : (words vs ++ (wimg V).take idx).length = idx + xs.length := by
          simp only [List.length_append, hlenV, words, List.length_map]
          omega
        -- decompose the stack: `word v` on top, target slot `w` at depth idx+|vs|
        have hstk : words (v :: vs) ++ wimg V ++ σ
            = .word v :: ((words vs ++ (wimg V).take idx)
                ++ w :: ((wimg V).drop (idx + 1) ++ σ)) := by
          conv_lhs => rw [show words (v :: vs) = .word v :: words vs from rfl, hsplitV]
          simp [List.append_assoc]
        have hswap : AStep prog
            ⟨.swap ⟨idx + xs.length, h16⟩ :: (.pop :: (rest ++ c)),
              .word v :: ((words vs ++ (wimg V).take idx)
                ++ w :: ((wimg V).drop (idx + 1) ++ σ)), yst⟩
            ⟨.pop :: (rest ++ c),
              w :: ((words vs ++ (wimg V).take idx)
                ++ .word v :: ((wimg V).drop (idx + 1) ++ σ)), yst⟩ :=
          .swap (by simp [hAlen])
        have hpop : AStep prog
            ⟨.pop :: (rest ++ c),
              w :: ((words vs ++ (wimg V).take idx)
                ++ .word v :: ((wimg V).drop (idx + 1) ++ σ)), yst⟩
            ⟨rest ++ c,
              (words vs ++ (wimg V).take idx)
                ++ .word v :: ((wimg V).drop (idx + 1) ++ σ), yst⟩ := .pop
        -- the stack after the pop is exactly `words vs ++ wimg (set V x v) ++ σ`
        have hset : wimg (YulSemantics.VEnv.set V x v)
            = (wimg V).take idx ++ .word v :: (wimg V).drop (idx + 1) := by
          rw [wimg_set v hidx]
          conv_lhs => rw [hsplitV]
          rw [set_at_append' hlenV]
        have hmid : (words vs ++ (wimg V).take idx)
              ++ .word v :: ((wimg V).drop (idx + 1) ++ σ)
            = words vs ++ wimg (YulSemantics.VEnv.set V x v) ++ σ := by
          rw [hset]; simp [List.append_assoc]
        have hnames := names_set V x v
        have hih := ih vs (YulSemantics.VEnv.set V x v) rest hlen'
          (by rw [hnames]; exact hrest)
          (pre ++ [.swap ⟨idx + xs.length, h16⟩, .pop]) c σ (by rw [hp]; simp)
        rw [hstk]
        refine .head hswap (.head hpop ?_)
        rw [hmid, show YulSemantics.VEnv.setMany V (x :: xs) (v :: vs)
          = YulSemantics.VEnv.setMany (YulSemantics.VEnv.set V x v) xs vs from rfl]
        exact hih
      · rw [dif_neg h16] at hac2; exact absurd hac2 (by simp)

/-- `x₁, …, xₖ := e`: evaluate `e` (leaving its `k` values on top), then
store each into its variable and pop. -/
theorem asimS_assigns {prog : List Asm} {yst yst' : EvmState} {V : VEnv yulD}
    {xs : List Ident} {vs : List U256} {eCode acode : List Asm}
    (hlen : xs.length = vs.length)
    (hac : compileAssigns (names V) xs = some acode)
    (he : ASimE prog yst V 0 eCode vs yst') :
    ASimS prog yst V (eCode ++ acode) yst' (YulSemantics.VEnv.setMany V xs vs) := by
  intro pre c σ hp
  have h1 := he pre (acode ++ c) [] σ (by rw [hp]; simp [List.append_assoc]) rfl
  have h2 := assigns_exec (prog := prog) (yst := yst') xs vs V acode hlen hac
    (pre ++ eCode) c σ (by rw [hp]; simp [List.append_assoc])
  rw [List.append_assoc]
  refine ASteps.trans ?_ h2
  simpa [List.append_assoc] using h1

/-! ### Statement leaves: declarations, pops, labels, non-local exits -/

/-- The dialect's zero is the `0` word the compiler pushes. -/
theorem yulD_zero : yulD.zero = (0 : U256) := rfl

/-- `let x₁, …, xₙ` — one zero push per name. -/
theorem asimS_letZero {prog : List Asm} {yst : EvmState} {V : VEnv yulD}
    (xs : List Ident) :
    ASimS prog yst V (List.replicate xs.length (.push 0)) yst
      (YulSemantics.bindZeros yulD xs ++ V) := by
  induction xs with
  | nil => exact ASimS.nil
  | cons x xs ih =>
    show ASimS prog yst V (List.replicate (xs.length + 1) (.push 0)) yst _
    rw [List.replicate_succ']
    have hlast : ASimS prog yst (YulSemantics.bindZeros yulD xs ++ V)
        [.push 0] yst
        ((x, yulD.zero) :: (YulSemantics.bindZeros yulD xs ++ V)) := by
      rw [yulD_zero]
      exact (asimE_push 0).toASimSLet
    exact ih.comp hlast

/-- Popping a prefix of the region. -/
theorem asimS_pops {prog : List Asm} {yst : EvmState} :
    ∀ (W V : VEnv yulD),
      ASimS prog yst (W ++ V) (List.replicate W.length .pop) yst V := by
  intro W
  induction W with
  | nil => intro V; exact ASimS.nil
  | cons p W ih =>
    intro V pre c σ hp
    refine .head (.pop (v := .word p.2) (σ := wimg (W ++ V) ++ σ)) ?_
    have := ih V (pre ++ [.pop]) c σ (by rw [hp]; simp [List.replicate_succ])
    simpa using this

/-- Popping down to `trim depth` (saturating: no-op when `depth ≥ |V|`). -/
theorem asimS_trim {prog : List Asm} {yst : EvmState} (depth : Nat)
    (V : VEnv yulD) :
    ASimS prog yst V (List.replicate (V.length - depth) .pop) yst
      (trim depth V) := by
  have h := asimS_pops (prog := prog) (yst := yst)
    (V.take (V.length - depth)) (V.drop (V.length - depth))
  rw [List.take_append_drop] at h
  rw [show (V.take (V.length - depth)).length = V.length - depth from by
    simp] at h
  exact h

/-- Block exit: pop the block's locals, realizing the semantics'
`restore`. -/
theorem asimS_restore {prog : List Asm} {yst : EvmState}
    (V Vb : VEnv yulD) :
    ASimS prog yst Vb (List.replicate (Vb.length - V.length) .pop) yst
      (YulSemantics.restore V Vb) :=
  asimS_trim V.length Vb

/-- A label definition is a no-op. -/
theorem asimS_label {prog : List Asm} {yst : EvmState} {V : VEnv yulD}
    (l : Label) :
    ASimS prog yst V [.label l] yst V :=
  fun _pre _c _σ _hp => .single .label

/-- The compiled `break`/`continue`/`leave`: pop to the context's depth,
jump to its label. -/
theorem asimNL_exit {prog : List Asm} {yst : EvmState} {V : VEnv yulD}
    (l : Label) (depth : Nat) :
    ASimNL prog yst V (List.replicate (V.length - depth) .pop ++ [.jump l])
      yst V l depth := by
  intro pre c cL σ hp hfind
  rw [List.append_assoc]
  refine (asimS_trim (prog := prog) (yst := yst) depth V pre ([.jump l] ++ c) σ
    (by rw [hp]; simp)).trans ?_
  exact .single (.jump hfind)

/-! ### The `if` building blocks -/

theorem stepOp_iszero (v : U256) (st : EvmState) :
    stepOp .iszero [v] st
      = some (.ok [YulSemantics.EVM.b2w (v = 0)] st) := rfl

/-- The compiled condition prologue `cCode ; ISZERO`. -/
theorem asimE_condPrologue {prog : List Asm} {yst yst1 : EvmState}
    {V : VEnv yulD} {cCode : List Asm} {cv : U256}
    (hc : ASimE prog yst V 0 cCode [cv] yst1) :
    ASimE prog yst V 0 (cCode ++ [.op .iszero])
      [YulSemantics.EVM.b2w (cv = 0)] yst1 :=
  asimE_op hc (stepOp_iszero cv yst1)

/-- Truthy `if`, body runs normally: fall through the `jumpi`, run the
body, step over the trailing label. -/
theorem asimS_ifTrue {prog : List Asm} {yst yst1 yst2 : EvmState}
    {V V2 : VEnv yulD} {cCode bodyAsm : List Asm} {cv : U256} {lend : Label}
    (hc : ASimE prog yst V 0 cCode [cv] yst1)
    (hcv : cv ≠ 0)
    (hbody : ASimS prog yst1 V bodyAsm yst2 V2) :
    ASimS prog yst V
      (cCode ++ [.op .iszero, .jumpi lend] ++ bodyAsm ++ [.label lend])
      yst2 V2 := by
  have hzero : YulSemantics.EVM.b2w (cv = 0) = 0 := by
    unfold YulSemantics.EVM.b2w
    rw [if_neg (by simpa using hcv)]
  have hfall : ASimS prog yst V (cCode ++ [.op .iszero, .jumpi lend]) yst1 V := by
    intro pre c σ hp
    have h1 : ASteps prog
        ⟨(cCode ++ [.op .iszero]) ++ (.jumpi lend :: c), wimg V ++ σ, yst⟩
        ⟨.jumpi lend :: c,
          .word (YulSemantics.EVM.b2w (cv = 0)) :: (wimg V ++ σ), yst1⟩ := by
      simpa using (asimE_condPrologue hc) pre (.jumpi lend :: c) [] σ
        (by rw [hp]; simp) rfl
    have h2 : AStep prog
        ⟨.jumpi lend :: c,
          .word (YulSemantics.EVM.b2w (cv = 0)) :: (wimg V ++ σ), yst1⟩
        ⟨c, wimg V ++ σ, yst1⟩ := .jumpiFall hzero
    have hcode : cCode ++ [Asm.op .iszero, Asm.jumpi lend] ++ c
        = (cCode ++ [Asm.op .iszero]) ++ (Asm.jumpi lend :: c) := by simp
    rw [hcode]
    exact h1.snoc h2
  have := (hfall.comp hbody).comp (asimS_label lend)
  simpa using this

/-- Truthy `if` whose body halts. -/
theorem asimS_ifTrueHalt {prog : List Asm} {yst yst1 yst2 : EvmState}
    {V : VEnv yulD} {cCode bodyAsm : List Asm} {cv : U256} {lend : Label}
    (hc : ASimE prog yst V 0 cCode [cv] yst1)
    (hcv : cv ≠ 0)
    (hbody : ASimSHalt prog yst1 V bodyAsm yst2) :
    ASimSHalt prog yst V
      (cCode ++ [.op .iszero, .jumpi lend] ++ bodyAsm ++ [.label lend])
      yst2 := by
  have hzero : YulSemantics.EVM.b2w (cv = 0) = 0 := by
    unfold YulSemantics.EVM.b2w
    rw [if_neg (by simpa using hcv)]
  have hfall : ASimS prog yst V (cCode ++ [.op .iszero, .jumpi lend]) yst1 V := by
    intro pre c σ hp
    have h1 : ASteps prog
        ⟨(cCode ++ [.op .iszero]) ++ (.jumpi lend :: c), wimg V ++ σ, yst⟩
        ⟨.jumpi lend :: c,
          .word (YulSemantics.EVM.b2w (cv = 0)) :: (wimg V ++ σ), yst1⟩ := by
      simpa using (asimE_condPrologue hc) pre (.jumpi lend :: c) [] σ
        (by rw [hp]; simp) rfl
    have hcode : cCode ++ [Asm.op .iszero, Asm.jumpi lend] ++ c
        = (cCode ++ [Asm.op .iszero]) ++ (Asm.jumpi lend :: c) := by simp
    rw [hcode]
    exact h1.snoc (.jumpiFall hzero)
  have := (hfall.compHalt hbody).extend [.label lend]
  simpa using this

/-- Truthy `if` whose body exits non-locally. -/
theorem asimS_ifTrueNL {prog : List Asm} {yst yst1 yst2 : EvmState}
    {V V2 : VEnv yulD} {cCode bodyAsm : List Asm} {cv : U256}
    {lend l : Label} {depth : Nat}
    (hc : ASimE prog yst V 0 cCode [cv] yst1)
    (hcv : cv ≠ 0)
    (hbody : ASimNL prog yst1 V bodyAsm yst2 V2 l depth) :
    ASimNL prog yst V
      (cCode ++ [.op .iszero, .jumpi lend] ++ bodyAsm ++ [.label lend])
      yst2 V2 l depth := by
  have hzero : YulSemantics.EVM.b2w (cv = 0) = 0 := by
    unfold YulSemantics.EVM.b2w
    rw [if_neg (by simpa using hcv)]
  have hfall : ASimS prog yst V (cCode ++ [.op .iszero, .jumpi lend]) yst1 V := by
    intro pre c σ hp
    have h1 : ASteps prog
        ⟨(cCode ++ [.op .iszero]) ++ (.jumpi lend :: c), wimg V ++ σ, yst⟩
        ⟨.jumpi lend :: c,
          .word (YulSemantics.EVM.b2w (cv = 0)) :: (wimg V ++ σ), yst1⟩ := by
      simpa using (asimE_condPrologue hc) pre (.jumpi lend :: c) [] σ
        (by rw [hp]; simp) rfl
    have hcode : cCode ++ [Asm.op .iszero, Asm.jumpi lend] ++ c
        = (cCode ++ [Asm.op .iszero]) ++ (Asm.jumpi lend :: c) := by simp
    rw [hcode]
    exact h1.snoc (.jumpiFall hzero)
  have := (hfall.compNL hbody).extend [.label lend]
  simpa using this

/-- Falsy `if`: the `jumpi` is taken, over the body to the trailing
label. Needs unique labels to know where the jump lands. -/
theorem asimS_ifFalse {prog : List Asm}
    (hnodup : (labelDefs prog).Nodup)
    {yst yst1 : EvmState} {V : VEnv yulD} {cCode bodyAsm : List Asm}
    {cv : U256} {lend : Label}
    (hc : ASimE prog yst V 0 cCode [cv] yst1)
    (hcv : cv = 0) :
    ASimS prog yst V
      (cCode ++ [.op .iszero, .jumpi lend] ++ bodyAsm ++ [.label lend])
      yst1 V := by
  have hone : YulSemantics.EVM.b2w (cv = 0) ≠ 0 := by
    unfold YulSemantics.EVM.b2w
    rw [if_pos (by simpa using hcv)]
    decide
  intro pre c σ hp
  -- the fragment ends with the label; the jump lands right after it
  have hfind : findLabel lend prog = some c := by
    have hsplit : prog = (pre ++ cCode ++ [.op .iszero, .jumpi lend]
        ++ bodyAsm) ++ .label lend :: c := by
      rw [hp]; simp
    rw [hsplit]
    exact findLabel_boundary (by rw [← hsplit]; exact hnodup)
  have h1 : ASteps prog
      ⟨(cCode ++ [.op .iszero]) ++ (.jumpi lend
          :: (bodyAsm ++ .label lend :: c)),
        wimg V ++ σ, yst⟩
      ⟨.jumpi lend :: (bodyAsm ++ .label lend :: c),
        .word (YulSemantics.EVM.b2w (cv = 0)) :: (wimg V ++ σ), yst1⟩ := by
    simpa using (asimE_condPrologue hc) pre
      (.jumpi lend :: (bodyAsm ++ .label lend :: c)) [] σ
      (by rw [hp]; simp) rfl
  have h2 : AStep prog
      ⟨.jumpi lend :: (bodyAsm ++ .label lend :: c),
        .word (YulSemantics.EVM.b2w (cv = 0)) :: (wimg V ++ σ), yst1⟩
      ⟨c, wimg V ++ σ, yst1⟩ := .jumpiTaken hone hfind
  have hcode : cCode ++ [Asm.op .iszero, Asm.jumpi lend] ++ bodyAsm
      ++ [Asm.label lend] ++ c
      = (cCode ++ [Asm.op .iszero])
        ++ (Asm.jumpi lend :: (bodyAsm ++ Asm.label lend :: c)) := by simp
  rw [hcode]
  exact h1.snoc h2

/-- `if` whose condition halts. -/
theorem asimS_ifCondHalt {prog : List Asm} {yst yst1 : EvmState}
    {V : VEnv yulD} {cCode bodyAsm : List Asm} {lend : Label}
    (hc : ASimEHalt prog yst V 0 cCode yst1) :
    ASimSHalt prog yst V
      (cCode ++ [.op .iszero, .jumpi lend] ++ bodyAsm ++ [.label lend])
      yst1 := by
  rw [show cCode ++ [Asm.op .iszero, Asm.jumpi lend] ++ bodyAsm
      ++ [Asm.label lend]
      = cCode ++ ([Asm.op .iszero, Asm.jumpi lend] ++ bodyAsm
        ++ [Asm.label lend]) from by simp]
  exact (hc.extend _).toASimSHalt

/-! ### `switch`: the case-comparison prologue -/

/-- `DUP1` reads the innermost variable (the `switch` scrutinee, modelled as a
let-bound temp). -/
theorem asimE_dup0 {prog : List Asm} {yst : EvmState} {V : VEnv yulD}
    (x : Ident) (v : U256) :
    ASimE prog yst ((x, v) :: V) 0 [.dup 0] [v] yst := by
  intro pre c τ σ hp hτ
  obtain rfl := List.eq_nil_of_length_eq_zero hτ
  have hstep : AStep prog
      ⟨.dup (0 : Fin 16) :: c, .word v :: (wimg V ++ σ), yst⟩
      ⟨c, .word v :: (.word v :: (wimg V ++ σ)), yst⟩ :=
    AStep.dup (n := (0 : Fin 16)) (v := .word v) (τ := []) (ρ := wimg V ++ σ) (by simp)
  exact ASteps.single hstep

/-- The `switch` case comparison `DUP1 ; PUSH w ; EQ ; ISZERO`, reading the
scrutinee `cv` (the innermost temp): it computes the *skip* condition
`b2w (b2w (w = cv) = 0)` (nonzero ⇔ no match), leaving `cv` beneath. -/
theorem asimE_switchCmp {prog : List Asm} {yst : EvmState} {V : VEnv yulD}
    (x : Ident) (w cv : U256) :
    ASimE prog yst ((x, cv) :: V) 0 [.dup 0, .push w, .op .eq, .op .iszero]
      [YulSemantics.EVM.b2w (YulSemantics.EVM.b2w (w = cv) = 0)] yst := by
  have h2 : ASimE prog yst ((x, cv) :: V) 0 [.dup 0, .push w] [w, cv] yst :=
    ASimE.compArgs (k := 1) rfl (asimE_dup0 x cv) (asimE_push w)
  have heq : stepOp .eq [w, cv] yst
      = some (.ok [YulSemantics.EVM.b2w (w = cv)] yst) := rfl
  have h3 := asimE_op h2 heq
  have hiz : stepOp .iszero [YulSemantics.EVM.b2w (w = cv)] yst
      = some (.ok [YulSemantics.EVM.b2w (YulSemantics.EVM.b2w (w = cv) = 0)] yst) := rfl
  have h4 := asimE_op h3 hiz
  simpa using h4

/-- After a fragment `A` (bringing `V` to `V'`), `jump lend` reaches the
fragment's own trailing `label lend`, skipping the intervening `B`. -/
theorem asimS_jumpToEnd {prog : List Asm} {yst yst' : EvmState}
    {V V' : VEnv yulD} {A B : List Asm} {lend : Label}
    (hnodup : (labelDefs prog).Nodup)
    (hA : ASimS prog yst V A yst' V') :
    ASimS prog yst V (A ++ .jump lend :: B ++ [.label lend]) yst' V' := by
  intro pre c σ hp
  have hsplit : prog = (pre ++ A ++ .jump lend :: B) ++ .label lend :: c := by
    rw [hp]; simp
  have hfind : findLabel lend prog = some c := by
    rw [hsplit]; exact findLabel_boundary (by rw [← hsplit]; exact hnodup)
  have hA' := hA pre (.jump lend :: (B ++ [.label lend] ++ c)) σ (by rw [hp]; simp)
  have hstep : AStep prog
      ⟨.jump lend :: (B ++ [.label lend] ++ c), wimg V' ++ σ, yst'⟩
      ⟨c, wimg V' ++ σ, yst'⟩ := .jump hfind
  simpa using hA'.trans (.single hstep)

/-- The case comparison, when the scrutinee matches: it falls through the
`jumpi`, leaving the scrutinee for the following `pop`. -/
theorem asimS_cmpFall {prog : List Asm} {yst : EvmState} {V : VEnv yulD}
    (x : Ident) (w cv : U256) (lnext : Label) (hmatch : cv = w) :
    ASimS prog yst ((x, cv) :: V)
      [.dup 0, .push w, .op .eq, .op .iszero, .jumpi lnext] yst ((x, cv) :: V) := by
  have hz : YulSemantics.EVM.b2w (YulSemantics.EVM.b2w (w = cv) = 0) = 0 := by
    subst hmatch; simp [YulSemantics.EVM.b2w]
  intro pre c σ hp
  have hc := asimE_switchCmp (prog := prog) (yst := yst) (V := V) x w cv
    pre (.jumpi lnext :: c) [] σ (by rw [hp]; simp) rfl
  have hjmp : AStep prog
      ⟨.jumpi lnext :: c,
        .word (YulSemantics.EVM.b2w (YulSemantics.EVM.b2w (w = cv) = 0))
          :: (wimg ((x, cv) :: V) ++ σ), yst⟩
      ⟨c, wimg ((x, cv) :: V) ++ σ, yst⟩ := .jumpiFall hz
  have hcode : ([.dup 0, .push w, .op .eq, .op .iszero, .jumpi lnext] : List Asm) ++ c
      = [.dup 0, .push w, .op .eq, .op .iszero] ++ (.jumpi lnext :: c) := by simp
  rw [hcode]
  refine (?_ : ASteps prog _ _).trans (.single hjmp)
  simpa using hc

/-- Normal-outcome dispatch: the compiled case chain (plus its default tail)
runs `compileBlock (selectSwitch cv cases dflt)` and reaches `lend`, with the
scrutinee consumed. By induction on `cases`. -/
theorem asimS_switchTailNormal {prog : List Asm} (hnodup : (labelDefs prog).Nodup)
    {Φ : FMap} {F : Option FunCtx} {L : Option LoopCtx}
    {yst1 yst2 : EvmState} {V V' : VEnv yulD} {cv : U256} (dummy : Ident)
    {lend : Label} {defAsm : List Asm} {n2 n3 : Nat}
    {dflt : Option (Block Op)}
    (hdef : compileBlock Φ (names V) F L n2 (dflt.getD []) = some (defAsm, n3)) :
    ∀ (cases : List (YulSemantics.Literal × Block Op)) {chainAsm : List Asm} {n1 : Nat},
      compileSwitchCases Φ (names V) F L lend n1 cases = some (chainAsm, n2) →
      (∀ m bAsm m',
        compileBlock Φ (names V) F L m (YulSemantics.selectSwitch yulD cv cases dflt) = some (bAsm, m') →
        ASimS prog yst1 V bAsm yst2 V') →
      ASimS prog yst1 ((dummy, cv) :: V)
        (chainAsm ++ .pop :: defAsm ++ [.label lend]) yst2 V' := by
  intro cases
  induction cases with
  | nil =>
    intro chainAsm n1 hchain hblk
    simp only [compileSwitchCases, Option.some.injEq, Prod.mk.injEq] at hchain
    obtain ⟨rfl, rfl⟩ := hchain
    have hb : ASimS prog yst1 V defAsm yst2 V' := hblk _ defAsm n3 hdef
    have hpop : ASimS prog yst1 ((dummy, cv) :: V) [.pop] yst1 V := by
      simpa using asimS_pops (prog := prog) (yst := yst1) [(dummy, cv)] V
    simpa using (hpop.comp hb).comp (asimS_label lend)
  | cons vb rest ih =>
    intro chainAsm n1 hchain hblk
    obtain ⟨v, b⟩ := vb
    simp only [compileSwitchCases, Option.bind_eq_bind] at hchain
    obtain ⟨⟨bAsm, m1⟩, hb, h2⟩ := Option.bind_eq_some_iff.mp hchain
    obtain ⟨⟨restAsm, m2⟩, hrest, h3⟩ := Option.bind_eq_some_iff.mp h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h3
    obtain ⟨rfl, rfl⟩ := h3
    by_cases hmatch : cv = litValue v
    · -- matched case: run its body, jump to the end
      have hsel : YulSemantics.selectSwitch yulD cv ((v, b) :: rest) dflt = b := by
        simp [YulSemantics.selectSwitch, hmatch]
      have hbody : ASimS prog yst1 V bAsm yst2 V' :=
        hblk (n1 + 1) bAsm m1 (by rw [hsel]; exact hb)
      have hpop : ASimS prog yst1 ((dummy, cv) :: V) [.pop] yst1 V := by
        simpa using asimS_pops (prog := prog) (yst := yst1) [(dummy, cv)] V
      have hA : ASimS prog yst1 ((dummy, cv) :: V)
          ([.dup 0, .push (litValue v), .op .eq, .op .iszero, .jumpi n1] ++ [.pop] ++ bAsm)
          yst2 V' :=
        ((asimS_cmpFall dummy (litValue v) cv n1 hmatch).comp hpop).comp hbody
      have := asimS_jumpToEnd (lend := lend) (B := .label n1 :: restAsm ++ .pop :: defAsm)
        hnodup hA
      simpa using this
    · -- unmatched case: skip to the next case, recurse
      have hsel : YulSemantics.selectSwitch yulD cv ((v, b) :: rest) dflt = YulSemantics.selectSwitch yulD cv rest dflt := by
        simp [YulSemantics.selectSwitch, hmatch]
      have hIH : ASimS prog yst1 ((dummy, cv) :: V)
          (restAsm ++ .pop :: defAsm ++ [.label lend]) yst2 V' :=
        ih hrest (fun m bAsm' m' hc' => hblk m bAsm' m' (by rw [hsel]; exact hc'))
      intro pre c σ hp
      -- find the next-case label
      have hsplit : prog = (pre ++ [.dup 0, .push (litValue v), .op .eq, .op .iszero,
          .jumpi n1, .pop] ++ bAsm ++ [.jump lend]) ++ .label n1 ::
          (restAsm ++ .pop :: defAsm ++ [.label lend] ++ c) := by rw [hp]; simp
      have hfind : findLabel n1 prog
          = some (restAsm ++ .pop :: defAsm ++ [.label lend] ++ c) := by
        rw [hsplit]; exact findLabel_boundary (by rw [← hsplit]; exact hnodup)
      have hnz : YulSemantics.EVM.b2w (YulSemantics.EVM.b2w (litValue v = cv) = 0) ≠ 0 := by
        have h1 : litValue v ≠ cv := fun h => hmatch h.symm
        simp [YulSemantics.EVM.b2w, h1]
      -- prologue produces the (nonzero) skip condition; jumpi is taken
      have hc := asimE_switchCmp (prog := prog) (yst := yst1) (V := V) dummy (litValue v) cv
        pre (.jumpi n1 :: (.pop :: bAsm ++ [.jump lend, .label n1] ++ restAsm
          ++ .pop :: defAsm ++ [.label lend]) ++ c) [] σ (by rw [hp]; simp) rfl
      have hjmp : AStep prog
          ⟨.jumpi n1 :: (.pop :: bAsm ++ [.jump lend, .label n1] ++ restAsm
            ++ .pop :: defAsm ++ [.label lend]) ++ c,
            .word (YulSemantics.EVM.b2w (YulSemantics.EVM.b2w (litValue v = cv) = 0))
              :: (wimg ((dummy, cv) :: V) ++ σ), yst1⟩
          ⟨restAsm ++ .pop :: defAsm ++ [.label lend] ++ c, wimg ((dummy, cv) :: V) ++ σ, yst1⟩ :=
        .jumpiTaken hnz hfind
      have hstep := hIH (pre ++ [.dup 0, .push (litValue v), .op .eq, .op .iszero, .jumpi n1, .pop]
        ++ bAsm ++ [.jump lend, .label n1]) c σ (by rw [hp]; simp)
      have hcode : (([.dup 0, .push (litValue v), .op .eq, .op .iszero, .jumpi n1, .pop] ++ bAsm
            ++ [.jump lend, .label n1] ++ restAsm) ++ .pop :: defAsm ++ [.label lend]) ++ c
          = [.dup 0, .push (litValue v), .op .eq, .op .iszero]
            ++ (.jumpi n1 :: (.pop :: bAsm ++ [.jump lend, .label n1] ++ restAsm
              ++ .pop :: defAsm ++ [.label lend]) ++ c) := by simp
      rw [hcode]
      refine (?_ : ASteps prog _ _).trans (ASteps.head hjmp ?_)
      · exact hc
      · simpa using hstep

/-- Halting-outcome dispatch: the selected block halts; the trailing code is
never reached. -/
theorem asimS_switchTailHalt {prog : List Asm} (hnodup : (labelDefs prog).Nodup)
    {Φ : FMap} {F : Option FunCtx} {L : Option LoopCtx}
    {yst1 yst2 : EvmState} {V : VEnv yulD} {cv : U256} (dummy : Ident)
    {lend : Label} {defAsm : List Asm} {n2 n3 : Nat}
    {dflt : Option (Block Op)}
    (hdef : compileBlock Φ (names V) F L n2 (dflt.getD []) = some (defAsm, n3)) :
    ∀ (cases : List (YulSemantics.Literal × Block Op)) {chainAsm : List Asm} {n1 : Nat},
      compileSwitchCases Φ (names V) F L lend n1 cases = some (chainAsm, n2) →
      (∀ m bAsm m',
        compileBlock Φ (names V) F L m (YulSemantics.selectSwitch yulD cv cases dflt) = some (bAsm, m') →
        ASimSHalt prog yst1 V bAsm yst2) →
      ASimSHalt prog yst1 ((dummy, cv) :: V)
        (chainAsm ++ .pop :: defAsm ++ [.label lend]) yst2 := by
  intro cases
  induction cases with
  | nil =>
    intro chainAsm n1 hchain hblk
    simp only [compileSwitchCases, Option.some.injEq, Prod.mk.injEq] at hchain
    obtain ⟨rfl, rfl⟩ := hchain
    have hb : ASimSHalt prog yst1 V defAsm yst2 := hblk _ defAsm n3 hdef
    have hpop : ASimS prog yst1 ((dummy, cv) :: V) [.pop] yst1 V := by
      simpa using asimS_pops (prog := prog) (yst := yst1) [(dummy, cv)] V
    simpa using (hpop.compHalt hb).extend [.label lend]
  | cons vb rest ih =>
    intro chainAsm n1 hchain hblk
    obtain ⟨v, b⟩ := vb
    simp only [compileSwitchCases, Option.bind_eq_bind] at hchain
    obtain ⟨⟨bAsm, m1⟩, hb, h2⟩ := Option.bind_eq_some_iff.mp hchain
    obtain ⟨⟨restAsm, m2⟩, hrest, h3⟩ := Option.bind_eq_some_iff.mp h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h3
    obtain ⟨rfl, rfl⟩ := h3
    by_cases hmatch : cv = litValue v
    · have hsel : YulSemantics.selectSwitch yulD cv ((v, b) :: rest) dflt = b := by
        simp [YulSemantics.selectSwitch, hmatch]
      have hbody : ASimSHalt prog yst1 V bAsm yst2 := hblk (n1 + 1) bAsm m1 (by rw [hsel]; exact hb)
      have hpop : ASimS prog yst1 ((dummy, cv) :: V) [.pop] yst1 V := by
        simpa using asimS_pops (prog := prog) (yst := yst1) [(dummy, cv)] V
      have hA : ASimSHalt prog yst1 ((dummy, cv) :: V)
          ([.dup 0, .push (litValue v), .op .eq, .op .iszero, .jumpi n1] ++ [.pop] ++ bAsm) yst2 :=
        ((asimS_cmpFall dummy (litValue v) cv n1 hmatch).comp hpop).compHalt hbody
      have heq : ([.dup 0, .push (litValue v), .op .eq, .op .iszero, .jumpi n1, .pop] ++ bAsm
            ++ [.jump lend, .label n1] ++ restAsm) ++ .pop :: defAsm ++ [.label lend]
          = ([.dup 0, .push (litValue v), .op .eq, .op .iszero, .jumpi n1] ++ [.pop] ++ bAsm)
            ++ ([.jump lend, .label n1] ++ restAsm ++ .pop :: defAsm ++ [.label lend]) := by simp
      rw [heq]; exact hA.extend _
    · have hsel : YulSemantics.selectSwitch yulD cv ((v, b) :: rest) dflt
          = YulSemantics.selectSwitch yulD cv rest dflt := by simp [YulSemantics.selectSwitch, hmatch]
      have hIH : ASimSHalt prog yst1 ((dummy, cv) :: V)
          (restAsm ++ .pop :: defAsm ++ [.label lend]) yst2 :=
        ih hrest (fun m bAsm' m' hc' => hblk m bAsm' m' (by rw [hsel]; exact hc'))
      intro pre c σ hp
      have hsplit : prog = (pre ++ [.dup 0, .push (litValue v), .op .eq, .op .iszero,
          .jumpi n1, .pop] ++ bAsm ++ [.jump lend]) ++ .label n1 ::
          (restAsm ++ .pop :: defAsm ++ [.label lend] ++ c) := by rw [hp]; simp
      have hfind : findLabel n1 prog
          = some (restAsm ++ .pop :: defAsm ++ [.label lend] ++ c) := by
        rw [hsplit]; exact findLabel_boundary (by rw [← hsplit]; exact hnodup)
      have hnz : YulSemantics.EVM.b2w (YulSemantics.EVM.b2w (litValue v = cv) = 0) ≠ 0 := by
        have h1 : litValue v ≠ cv := fun h => hmatch h.symm
        simp [YulSemantics.EVM.b2w, h1]
      have hc := asimE_switchCmp (prog := prog) (yst := yst1) (V := V) dummy (litValue v) cv
        pre (.jumpi n1 :: (.pop :: bAsm ++ [.jump lend, .label n1] ++ restAsm
          ++ .pop :: defAsm ++ [.label lend]) ++ c) [] σ (by rw [hp]; simp) rfl
      have hjmp : AStep prog
          ⟨.jumpi n1 :: (.pop :: bAsm ++ [.jump lend, .label n1] ++ restAsm
            ++ .pop :: defAsm ++ [.label lend]) ++ c,
            .word (YulSemantics.EVM.b2w (YulSemantics.EVM.b2w (litValue v = cv) = 0))
              :: (wimg ((dummy, cv) :: V) ++ σ), yst1⟩
          ⟨restAsm ++ .pop :: defAsm ++ [.label lend] ++ c, wimg ((dummy, cv) :: V) ++ σ, yst1⟩ :=
        .jumpiTaken hnz hfind
      obtain ⟨conf, hsteps, hhalt⟩ := hIH (pre ++ [.dup 0, .push (litValue v), .op .eq, .op .iszero,
        .jumpi n1, .pop] ++ bAsm ++ [.jump lend, .label n1]) c σ (by rw [hp]; simp)
      refine ⟨conf, ?_, hhalt⟩
      have hcode : (([.dup 0, .push (litValue v), .op .eq, .op .iszero, .jumpi n1, .pop] ++ bAsm
            ++ [.jump lend, .label n1] ++ restAsm) ++ .pop :: defAsm ++ [.label lend]) ++ c
          = [.dup 0, .push (litValue v), .op .eq, .op .iszero]
            ++ (.jumpi n1 :: (.pop :: bAsm ++ [.jump lend, .label n1] ++ restAsm
              ++ .pop :: defAsm ++ [.label lend]) ++ c) := by simp
      rw [hcode]
      exact hc.trans (ASteps.head hjmp (by simpa using hsteps))

/-- Non-local-exit dispatch (`break`/`continue`/`leave`): the selected block
exits to the context label `l`. -/
theorem asimS_switchTailNL {prog : List Asm} (hnodup : (labelDefs prog).Nodup)
    {Φ : FMap} {F : Option FunCtx} {L : Option LoopCtx}
    {yst1 yst2 : EvmState} {V V' : VEnv yulD} {cv : U256} (dummy : Ident)
    {lend l : Label} {depth : Nat} {defAsm : List Asm} {n2 n3 : Nat}
    {dflt : Option (Block Op)}
    (hdef : compileBlock Φ (names V) F L n2 (dflt.getD []) = some (defAsm, n3)) :
    ∀ (cases : List (YulSemantics.Literal × Block Op)) {chainAsm : List Asm} {n1 : Nat},
      compileSwitchCases Φ (names V) F L lend n1 cases = some (chainAsm, n2) →
      (∀ m bAsm m',
        compileBlock Φ (names V) F L m (YulSemantics.selectSwitch yulD cv cases dflt) = some (bAsm, m') →
        ASimNL prog yst1 V bAsm yst2 V' l depth) →
      ASimNL prog yst1 ((dummy, cv) :: V)
        (chainAsm ++ .pop :: defAsm ++ [.label lend]) yst2 V' l depth := by
  intro cases
  induction cases with
  | nil =>
    intro chainAsm n1 hchain hblk
    simp only [compileSwitchCases, Option.some.injEq, Prod.mk.injEq] at hchain
    obtain ⟨rfl, rfl⟩ := hchain
    have hb : ASimNL prog yst1 V defAsm yst2 V' l depth := hblk _ defAsm n3 hdef
    have hpop : ASimS prog yst1 ((dummy, cv) :: V) [.pop] yst1 V := by
      simpa using asimS_pops (prog := prog) (yst := yst1) [(dummy, cv)] V
    simpa using (hpop.compNL hb).extend [.label lend]
  | cons vb rest ih =>
    intro chainAsm n1 hchain hblk
    obtain ⟨v, b⟩ := vb
    simp only [compileSwitchCases, Option.bind_eq_bind] at hchain
    obtain ⟨⟨bAsm, m1⟩, hb, h2⟩ := Option.bind_eq_some_iff.mp hchain
    obtain ⟨⟨restAsm, m2⟩, hrest, h3⟩ := Option.bind_eq_some_iff.mp h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h3
    obtain ⟨rfl, rfl⟩ := h3
    by_cases hmatch : cv = litValue v
    · have hsel : YulSemantics.selectSwitch yulD cv ((v, b) :: rest) dflt = b := by
        simp [YulSemantics.selectSwitch, hmatch]
      have hbody : ASimNL prog yst1 V bAsm yst2 V' l depth :=
        hblk (n1 + 1) bAsm m1 (by rw [hsel]; exact hb)
      have hpop : ASimS prog yst1 ((dummy, cv) :: V) [.pop] yst1 V := by
        simpa using asimS_pops (prog := prog) (yst := yst1) [(dummy, cv)] V
      have hA : ASimNL prog yst1 ((dummy, cv) :: V)
          ([.dup 0, .push (litValue v), .op .eq, .op .iszero, .jumpi n1] ++ [.pop] ++ bAsm)
          yst2 V' l depth :=
        ((asimS_cmpFall dummy (litValue v) cv n1 hmatch).comp hpop).compNL hbody
      have heq : ([.dup 0, .push (litValue v), .op .eq, .op .iszero, .jumpi n1, .pop] ++ bAsm
            ++ [.jump lend, .label n1] ++ restAsm) ++ .pop :: defAsm ++ [.label lend]
          = ([.dup 0, .push (litValue v), .op .eq, .op .iszero, .jumpi n1] ++ [.pop] ++ bAsm)
            ++ ([.jump lend, .label n1] ++ restAsm ++ .pop :: defAsm ++ [.label lend]) := by simp
      rw [heq]; exact hA.extend _
    · have hsel : YulSemantics.selectSwitch yulD cv ((v, b) :: rest) dflt
          = YulSemantics.selectSwitch yulD cv rest dflt := by simp [YulSemantics.selectSwitch, hmatch]
      have hIH : ASimNL prog yst1 ((dummy, cv) :: V)
          (restAsm ++ .pop :: defAsm ++ [.label lend]) yst2 V' l depth :=
        ih hrest (fun m bAsm' m' hc' => hblk m bAsm' m' (by rw [hsel]; exact hc'))
      intro pre c cL σ hp hfindL
      have hsplit : prog = (pre ++ [.dup 0, .push (litValue v), .op .eq, .op .iszero,
          .jumpi n1, .pop] ++ bAsm ++ [.jump lend]) ++ .label n1 ::
          (restAsm ++ .pop :: defAsm ++ [.label lend] ++ c) := by rw [hp]; simp
      have hfind : findLabel n1 prog
          = some (restAsm ++ .pop :: defAsm ++ [.label lend] ++ c) := by
        rw [hsplit]; exact findLabel_boundary (by rw [← hsplit]; exact hnodup)
      have hnz : YulSemantics.EVM.b2w (YulSemantics.EVM.b2w (litValue v = cv) = 0) ≠ 0 := by
        have h1 : litValue v ≠ cv := fun h => hmatch h.symm
        simp [YulSemantics.EVM.b2w, h1]
      have hc := asimE_switchCmp (prog := prog) (yst := yst1) (V := V) dummy (litValue v) cv
        pre (.jumpi n1 :: (.pop :: bAsm ++ [.jump lend, .label n1] ++ restAsm
          ++ .pop :: defAsm ++ [.label lend]) ++ c) [] σ (by rw [hp]; simp) rfl
      have hjmp : AStep prog
          ⟨.jumpi n1 :: (.pop :: bAsm ++ [.jump lend, .label n1] ++ restAsm
            ++ .pop :: defAsm ++ [.label lend]) ++ c,
            .word (YulSemantics.EVM.b2w (YulSemantics.EVM.b2w (litValue v = cv) = 0))
              :: (wimg ((dummy, cv) :: V) ++ σ), yst1⟩
          ⟨restAsm ++ .pop :: defAsm ++ [.label lend] ++ c, wimg ((dummy, cv) :: V) ++ σ, yst1⟩ :=
        .jumpiTaken hnz hfind
      have hstep := hIH (pre ++ [.dup 0, .push (litValue v), .op .eq, .op .iszero, .jumpi n1, .pop]
        ++ bAsm ++ [.jump lend, .label n1]) c cL σ (by rw [hp]; simp) hfindL
      have hcode : (([.dup 0, .push (litValue v), .op .eq, .op .iszero, .jumpi n1, .pop] ++ bAsm
            ++ [.jump lend, .label n1] ++ restAsm) ++ .pop :: defAsm ++ [.label lend]) ++ c
          = [.dup 0, .push (litValue v), .op .eq, .op .iszero]
            ++ (.jumpi n1 :: (.pop :: bAsm ++ [.jump lend, .label n1] ++ restAsm
              ++ .pop :: defAsm ++ [.label lend]) ++ c) := by simp
      rw [hcode]
      exact hc.trans (ASteps.head hjmp (by simpa using hstep))

/-! ### Functions: the compile-time/semantic environment agreement -/

/-- The epilogue instructions of a compiled function. -/
def epilogue (nps nrs : Nat) : List Asm :=
  List.replicate nps .pop
    ++ (if nrs = 1 then [.swap 0] else [])
    ++ [.dynJump]

/-- What the compiler emitted for one function, somewhere in the program:
entry label, compiled body (against the scopes visible at the definition
site), exit label, epilogue. -/
def FunOK (prog : List Asm) (decl : YulSemantics.FDecl yulD)
    (info : FunInfo) (Φv : FMap) : Prop :=
  info.arity = decl.params.length
    ∧ info.rets = decl.rets.length
    ∧ decl.rets.length ≤ 1
    ∧ (decl.params ++ decl.rets).Nodup
    ∧ ∃ (lexit n₀ n₁ : Nat) (bodyAsm : List Asm),
        compileBlock Φv (decl.params ++ decl.rets)
          (some ⟨lexit, (decl.params ++ decl.rets).length⟩) none n₀ decl.body
          = some (bodyAsm, n₁)
        ∧ (.label info.entry :: bodyAsm
            ++ .label lexit :: epilogue decl.params.length decl.rets.length)
            <:+: prog

/-- Scopewise agreement between the semantic function environment and the
compile-time one. Every function's `Φv` is the scope stack from its own
scope outward — exactly what `lookupFun` returns as `cenv`. -/
inductive FEnvOK (prog : List Asm) : YulSemantics.FunEnv yulD → FMap → Prop
  | nil : FEnvOK prog [] []
  | cons {scope : YulSemantics.FScope yulD} {scopeI : FScopeInfo}
      {rest : YulSemantics.FunEnv yulD} {restI : FMap} :
      List.Forall₂
        (fun (p : Ident × YulSemantics.FDecl yulD) (q : Ident × FunInfo) =>
          p.1 = q.1 ∧ FunOK prog p.2 q.2 (scopeI :: restI))
        scope scopeI →
      FEnvOK prog rest restI →
      FEnvOK prog (scope :: rest) (scopeI :: restI)

/-- The two scope searches agree, entry by entry. -/
private theorem find?_agree {prog : List Asm} {Φv : FMap} {f : Ident} :
    ∀ {scope : YulSemantics.FScope yulD} {scopeI : FScopeInfo},
      List.Forall₂
        (fun (p : Ident × YulSemantics.FDecl yulD) (q : Ident × FunInfo) =>
          p.1 = q.1 ∧ FunOK prog p.2 q.2 Φv) scope scopeI →
      (scope.find? (fun p => p.1 = f) = none
        ∧ scopeI.find? (fun q => q.1 = f) = none)
      ∨ (∃ p q, scope.find? (fun p => p.1 = f) = some p
          ∧ scopeI.find? (fun q => q.1 = f) = some q
          ∧ FunOK prog p.2 q.2 Φv) := by
  intro scope scopeI h
  induction h with
  | nil => exact Or.inl ⟨rfl, rfl⟩
  | @cons p q scope' scopeI' hpq htail ih =>
    obtain ⟨hname, hok⟩ := hpq
    by_cases hf : p.1 = f
    · refine Or.inr ⟨p, q, ?_, ?_, hok⟩
      · rw [List.find?_cons_of_pos (by simpa using hf)]
      · rw [List.find?_cons_of_pos (by simp [← hname, hf])]
    · rw [show scope'.find? (fun p => p.1 = f)
          = (p :: scope').find? (fun p => p.1 = f) from by
        rw [List.find?_cons_of_neg (by simpa using hf)]] at ih
      rw [show scopeI'.find? (fun q => q.1 = f)
          = (q :: scopeI').find? (fun q => q.1 = f) from by
        rw [List.find?_cons_of_neg (by simp [← hname, hf])]] at ih
      exact ih

/-- Successful lookups on corresponding environments correspond. -/
theorem lookupF_ok {prog : List Asm} {funs : YulSemantics.FunEnv yulD}
    {Φ : FMap} (h : FEnvOK prog funs Φ) {f : Ident}
    {decl : YulSemantics.FDecl yulD} {cenv : YulSemantics.FunEnv yulD}
    (hlk : YulSemantics.lookupFun funs f = some (decl, cenv)) :
    ∃ (info : FunInfo) (Φv : FMap),
      lookupF Φ f = some (info, Φv) ∧ FunOK prog decl info Φv
        ∧ FEnvOK prog cenv Φv := by
  induction h with
  | nil => simp [YulSemantics.lookupFun] at hlk
  | @cons scope scopeI rest restI hscope hrest ih =>
    rw [YulSemantics.lookupFun] at hlk
    rw [lookupF]
    rcases find?_agree hscope (f := f) with ⟨hn1, hn2⟩ | ⟨p, q, hs1, hs2, hok⟩
    · rw [hn1] at hlk
      rw [hn2]
      exact ih hlk
    · rw [hs1] at hlk
      rw [hs2]
      obtain ⟨rfl, rfl⟩ : p.2 = decl ∧ scope :: rest = cenv := by
        refine ⟨?_, ?_⟩ <;> · injection hlk with h'; cases h'; rfl
      exact ⟨q.2, scopeI :: restI, rfl, hok, .cons hscope hrest⟩

/-! ### The calling convention: return values off the stack region -/

/-- Lookup skips bindings whose names don't match. -/
private theorem get_append_right {A B : VEnv yulD} {r : Ident}
    (h : r ∉ names A) :
    YulSemantics.VEnv.get (A ++ B) r = YulSemantics.VEnv.get B r := by
  induction A with
  | nil => rfl
  | cons p A ih =>
    have hne : p.1 ≠ r := fun hEq => h (by
      rw [show names (p :: A) = p.1 :: names A from rfl, hEq]
      exact List.mem_cons_self ..)
    unfold YulSemantics.VEnv.get
    rw [List.cons_append, List.find?_cons_of_neg (by simpa using hne)]
    exact ih (fun hmem => h (List.mem_cons_of_mem _ hmem))

/-- On an environment with distinct names, name-based lookup reads the
values in order. -/
private theorem get_self {B : VEnv yulD} (hnodup : (names B).Nodup) :
    (names B).map (fun r => (YulSemantics.VEnv.get B r).getD yulD.zero)
      = B.map Prod.snd := by
  induction B with
  | nil => rfl
  | cons p B ih =>
    obtain ⟨y, w⟩ := p
    rw [show names ((y, w) :: B) = y :: names B from rfl] at hnodup ⊢
    have hy : y ∉ names B := by
      have := List.nodup_cons.mp hnodup
      exact this.1
    rw [List.map_cons, List.map_cons]
    congr 1
    · show (YulSemantics.VEnv.get ((y, w) :: B) y).getD yulD.zero = w
      unfold YulSemantics.VEnv.get
      rw [List.find?_cons_of_pos (by simp)]
      rfl
    · rw [← ih (List.nodup_cons.mp hnodup).2]
      apply List.map_congr_left
      intro r hr
      have hne : y ≠ r := fun hEq => hy (hEq ▸ hr)
      show (YulSemantics.VEnv.get ((y, w) :: B) r).getD _ = _
      unfold YulSemantics.VEnv.get
      rw [List.find?_cons_of_neg (by simpa using hne)]

/-- The stack image of the region below the parameters is exactly the
return values the semantics reads by name — provided names don't shadow. -/
theorem wimg_rets {Vend : VEnv yulD} {ps rs : List Ident}
    (hnames : names Vend = ps ++ rs) (hnodup : (ps ++ rs).Nodup) :
    wimg (Vend.drop ps.length)
      = words (rs.map (fun r =>
          (YulSemantics.VEnv.get Vend r).getD yulD.zero)) := by
  -- split Vend at the parameter/return boundary
  have hlenV : Vend.length = ps.length + rs.length := by
    have := congrArg List.length hnames
    simpa using this
  obtain ⟨A, B, rfl, hA⟩ : ∃ A B, Vend = A ++ B ∧ A.length = ps.length :=
    ⟨Vend.take ps.length, Vend.drop ps.length,
      (List.take_append_drop _ _).symm, by simp; omega⟩
  have hnA : names A = ps := by
    have h1 : names (A ++ B) = names A ++ names B := names_append ..
    rw [h1] at hnames
    exact List.append_inj_left hnames (by simpa using hA)
  have hnB : names B = rs := by
    have h1 : names (A ++ B) = names A ++ names B := names_append ..
    rw [h1] at hnames
    exact List.append_inj_right hnames (by simpa using hA)
  have hdrop : (A ++ B).drop ps.length = B := by
    rw [← hA]
    simp
  rw [hdrop]
  -- name-based lookups skip A entirely (no shadowing) and read B in order
  have hget : ∀ r ∈ rs, YulSemantics.VEnv.get (A ++ B) r
      = YulSemantics.VEnv.get B r := by
    intro r hr
    apply get_append_right
    rw [hnA]
    intro hmem
    exact (List.disjoint_of_nodup_append hnodup) hmem hr
  have : rs.map (fun r => (YulSemantics.VEnv.get (A ++ B) r).getD yulD.zero)
      = rs.map (fun r => (YulSemantics.VEnv.get B r).getD yulD.zero) := by
    apply List.map_congr_left
    intro r hr
    rw [hget r hr]
  rw [this, ← hnB,
    get_self (by rw [hnB]; exact (List.nodup_append.mp hnodup).2.1)]
  simp [wimg, words]

/-- Executing the epilogue from just after the exit label: pop the
parameters, bring the return address to the top, jump back to the call
site with the return values (read off the stack region — which agrees with
the semantics' name-based reads thanks to `Nodup`). -/
theorem asim_epilogue {prog : List Asm} {yst : EvmState}
    {Vend : VEnv yulD} {ps rs : List Ident} {lret : Label} {cRet : List Asm}
    (hnames : names Vend = ps ++ rs) (hnodup : (ps ++ rs).Nodup)
    (hrs1 : rs.length ≤ 1)
    (hfind : findLabel lret prog = some cRet) :
    ∀ (pre c : List Asm) (σc : List AVal),
      prog = pre ++ epilogue ps.length rs.length ++ c →
      ASteps prog ⟨epilogue ps.length rs.length ++ c,
          wimg Vend ++ (.code lret :: σc), yst⟩
        ⟨cRet, words (rs.map (fun r =>
            (YulSemantics.VEnv.get Vend r).getD yulD.zero)) ++ σc, yst⟩ := by
  intro pre c σc hp
  have hlenV : Vend.length = ps.length + rs.length := by
    have := congrArg List.length hnames
    simpa using this
  -- pop the parameters
  have hsplitV : Vend = Vend.take ps.length ++ Vend.drop ps.length :=
    (List.take_append_drop _ _).symm
  have htake : (Vend.take ps.length).length = ps.length := by
    simp
    omega
  have hpops : ASteps prog
      ⟨List.replicate ps.length .pop
          ++ ((if rs.length = 1 then [.swap 0] else [])
            ++ [.dynJump] ++ c),
        wimg Vend ++ (.code lret :: σc), yst⟩
      ⟨(if rs.length = 1 then [.swap 0] else []) ++ [.dynJump] ++ c,
        wimg (Vend.drop ps.length) ++ (.code lret :: σc), yst⟩ := by
    have h := asimS_pops (prog := prog) (yst := yst)
      (Vend.take ps.length) (Vend.drop ps.length)
    rw [htake] at h
    have := h pre ((if rs.length = 1 then [.swap 0] else [])
        ++ [.dynJump] ++ c) (.code lret :: σc)
      (by rw [hp]; simp [epilogue])
    rw [← hsplitV] at this
    exact this
  have hcode : epilogue ps.length rs.length ++ c
      = List.replicate ps.length .pop
        ++ ((if rs.length = 1 then [.swap 0] else []) ++ [.dynJump] ++ c) := by
    simp [epilogue]
  rw [hcode]
  rw [wimg_rets hnames hnodup] at hpops
  -- return-value shuffling depends on the arity (0 or 1)
  rcases rs with _ | ⟨r, rs'⟩
  · -- no return values: straight to the dynJump
    refine hpops.trans ?_
    show ASteps prog ⟨.dynJump :: c, .code lret :: σc, yst⟩ _
    exact .single (.dynJump hfind)
  · rcases rs' with _ | ⟨r2, rs''⟩
    · -- one return value: swap it past the return address
      refine hpops.trans ?_
      show ASteps prog
        ⟨.swap 0 :: (.dynJump :: c),
          .word ((YulSemantics.VEnv.get Vend r).getD yulD.zero)
            :: (.code lret :: σc), yst⟩ _
      have hswap : AStep prog
          ⟨.swap 0 :: (.dynJump :: c),
            .word ((YulSemantics.VEnv.get Vend r).getD yulD.zero)
              :: ([] ++ .code lret :: σc), yst⟩
          ⟨.dynJump :: c,
            .code lret :: ([] ++ .word ((YulSemantics.VEnv.get Vend r).getD
              yulD.zero) :: σc), yst⟩ := .swap rfl
      refine .head (by simpa using hswap) ?_
      exact .single (.dynJump hfind)
    · simp at hrs1

/-! ### Depth guards and the induction motive -/

/-- The loop context's depth is realized by the current region. -/
def LDepthOK : Option LoopCtx → VEnv yulD → Prop
  | some lc, V => lc.depth ≤ V.length
  | none, _ => True

/-- The function context's depth is realized by the current region. -/
def FDepthOK : Option FunCtx → VEnv yulD → Prop
  | some fc, V => fc.depth ≤ V.length
  | none, _ => True

/-- What a statement-class derivation means on the target, by outcome.
The *layout* facts (`Γ'`, lengths, context existence) hold outright; the
*simulation* facts are conditional on the function-environment agreement
`FEnvOK`, which is only establishable once the fragment is placed in the
program (a block's own placement is what puts its functions' bodies in
`prog`). -/
def SOut (prog : List Asm) (funs : YulSemantics.FunEnv yulD) (Φ : FMap)
    (yst : EvmState) (V : VEnv yulD) (asm : List Asm)
    (V' : VEnv yulD) (yst' : EvmState) (o : Outcome)
    (F : Option FunCtx) (L : Option LoopCtx) (Γ' : List Ident) : Prop :=
  match o with
  | .normal => Γ' = names V' ∧ V.length ≤ V'.length
      ∧ (FEnvOK prog funs Φ → ASimS prog yst V asm yst' V')
  | .halt => FEnvOK prog funs Φ → ASimSHalt prog yst V asm yst'
  | .break => ∃ lc, L = some lc ∧ V.length ≤ V'.length
      ∧ names (trim lc.depth V') = (names V).drop (V.length - lc.depth)
      ∧ (FEnvOK prog funs Φ →
          ASimNL prog yst V asm yst' V' lc.brk lc.depth)
  | .continue => ∃ lc, L = some lc ∧ V.length ≤ V'.length
      ∧ names (trim lc.depth V') = (names V).drop (V.length - lc.depth)
      ∧ (FEnvOK prog funs Φ →
          ASimNL prog yst V asm yst' V' lc.cont lc.depth)
  | .leave => ∃ fc, F = some fc ∧ V.length ≤ V'.length
      ∧ names (trim fc.depth V') = (names V).drop (V.length - fc.depth)
      ∧ (FEnvOK prog funs Φ →
          ASimNL prog yst V asm yst' V' fc.exit fc.depth)

/-- The suffix of the program at a compiled loop's condition label. -/
abbrev loopIter (lcond lpost lexit : Label)
    (cCode bodyAsm postAsm cRest : List Asm) : List Asm :=
  cCode ++ [.op .iszero, .jumpi lexit] ++ bodyAsm
    ++ .label lpost :: postAsm ++ .jump lcond :: .label lexit :: cRest

def LOut (prog : List Asm) (funs : YulSemantics.FunEnv yulD) (Φ : FMap)
    (yst : EvmState) (V V' : VEnv yulD)
    (yst' : EvmState) (o : Outcome) (F : Option FunCtx)
    (lcond lpost lexit : Label) (cCode bodyAsm postAsm : List Asm) : Prop :=
  match o with
  | .normal => names V' = names V ∧
      (∀ cRest, findLabel lcond prog
          = some (loopIter lcond lpost lexit cCode bodyAsm postAsm cRest) →
        FEnvOK prog funs Φ → ∀ σ : List AVal,
        ASteps prog
          ⟨loopIter lcond lpost lexit cCode bodyAsm postAsm cRest,
            wimg V ++ σ, yst⟩
          ⟨cRest, wimg V' ++ σ, yst'⟩)
  | .halt => ∀ cRest, findLabel lcond prog
        = some (loopIter lcond lpost lexit cCode bodyAsm postAsm cRest) →
      FEnvOK prog funs Φ → ∀ σ : List AVal,
      ∃ conf, ASteps prog
        ⟨loopIter lcond lpost lexit cCode bodyAsm postAsm cRest,
          wimg V ++ σ, yst⟩ conf
        ∧ AHalt prog conf yst'
  | .leave => ∃ fc, F = some fc ∧ V.length ≤ V'.length
      ∧ names (trim fc.depth V') = (names V).drop (V.length - fc.depth)
      ∧ (∀ cRest, findLabel lcond prog
            = some (loopIter lcond lpost lexit cCode bodyAsm postAsm cRest) →
          FEnvOK prog funs Φ →
          ∀ (σ : List AVal) (cL : List Asm), findLabel fc.exit prog = some cL →
            ASteps prog
              ⟨loopIter lcond lpost lexit cCode bodyAsm postAsm cRest,
                wimg V ++ σ, yst⟩
              ⟨cL, wimg (trim fc.depth V') ++ σ, yst'⟩)
  | _ => True

/-- The induction motive: what a source derivation for each syntactic
class means on the target, conditional on the compiler accepting the
syntax against the layout the runtime environment realizes. -/
def Motive (prog : List Asm) (funs : YulSemantics.FunEnv yulD)
    (V : VEnv yulD) (yst : EvmState) :
    YulSemantics.Code Op → YulSemantics.Res yulD → Prop
  | .expr e, .eres (.vals vs yst') =>
      ∀ Φ off n asm n',
        compileExpr Φ (names V) off n e = some (asm, n') →
        FEnvOK prog funs Φ → ASimE prog yst V off asm vs yst'
  | .expr e, .eres (.halt yst') =>
      ∀ Φ off n asm n',
        compileExpr Φ (names V) off n e = some (asm, n') →
        FEnvOK prog funs Φ → ASimEHalt prog yst V off asm yst'
  | .args es, .eres (.vals vs yst') =>
      ∀ Φ off n asm n',
        compileArgs Φ (names V) off n es = some (asm, n') →
        vs.length = es.length
          ∧ (FEnvOK prog funs Φ → ASimE prog yst V off asm vs yst')
  | .args es, .eres (.halt yst') =>
      ∀ Φ off n asm n',
        compileArgs Φ (names V) off n es = some (asm, n') →
        FEnvOK prog funs Φ → ASimEHalt prog yst V off asm yst'
  | .stmt s, .sres V' yst' o =>
      ∀ Φ F L n asm Γ' n',
        FDepthOK F V → LDepthOK L V →
        compileStmt Φ (names V) F L n s = some (asm, Γ', n') →
        SOut prog funs Φ yst V asm V' yst' o F L Γ'
  | .stmts ss, .sres V' yst' o =>
      ∀ Φ F L n asm Γ' n',
        FDepthOK F V → LDepthOK L V →
        compileStmts Φ (names V) F L n ss = some (asm, Γ', n') →
        SOut prog funs Φ yst V asm V' yst' o F L Γ'
  | .loop c post body, .sres V' yst' o =>
      ∀ Φ F lcond lpost lexit cCode bodyAsm postAsm n₁ n₂ n₃ n₄,
        FDepthOK F V →
        compileExpr Φ (names V) 0 n₁ c = some (cCode, n₂) →
        compileBlock Φ (names V) F (some ⟨lexit, lpost, V.length⟩) n₂ body
          = some (bodyAsm, n₃) →
        compileBlock Φ (names V) F none n₃ post = some (postAsm, n₄) →
        LOut prog funs Φ yst V V' yst' o F lcond lpost lexit
          cCode bodyAsm postAsm
  | _, _ => True

/-! ### Compile-equation inversions -/

private theorem expr_lit_inv {Φ : FMap} {Γ : List Ident} {off n : Nat}
    {l : YulSemantics.Literal} {asm : List Asm} {n' : Nat}
    (h : compileExpr Φ Γ off n (.lit l) = some (asm, n')) :
    asm = [.push (litValue l)] ∧ n' = n := by
  simp only [compileExpr, Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

private theorem expr_var_inv {Φ : FMap} {Γ : List Ident} {off n : Nat}
    {x : Ident} {asm : List Asm} {n' : Nat}
    (h : compileExpr Φ Γ off n (.var x) = some (asm, n')) :
    ∃ (idx : Nat) (h16 : off + idx < 16),
      Γ.findIdx? (fun y => y = x) = some idx
      ∧ asm = [.dup ⟨off + idx, h16⟩] ∧ n' = n := by
  simp only [compileExpr, Option.bind_eq_bind] at h
  obtain ⟨idx, hidx, h2⟩ := Option.bind_eq_some_iff.mp h
  by_cases h16 : off + idx < 16
  · rw [dif_pos h16] at h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h2
    exact ⟨idx, h16, hidx, h2.1.symm, h2.2.symm⟩
  · rw [dif_neg h16] at h2
    exact absurd h2 (by simp)

private theorem expr_builtin_inv {Φ : FMap} {Γ : List Ident} {off n : Nat}
    {op : Op} {args : List (Expr Op)} {asm : List Asm} {n' : Nat}
    (h : compileExpr Φ Γ off n (.builtin op args) = some (asm, n')) :
    ∃ argCode, compileArgs Φ Γ off n args = some (argCode, n')
      ∧ asm = argCode ++ [.op op] := by
  simp only [compileExpr, Option.bind_eq_bind] at h
  obtain ⟨⟨argCode, n1⟩, hargs, h2⟩ := Option.bind_eq_some_iff.mp h
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  exact ⟨argCode, h2.2 ▸ hargs, h2.1.symm⟩

private theorem expr_call_inv {Φ : FMap} {Γ : List Ident} {off n : Nat}
    {f : Ident} {args : List (Expr Op)} {asm : List Asm} {n' : Nat}
    (h : compileExpr Φ Γ off n (.call f args) = some (asm, n')) :
    ∃ (info : FunInfo) (Φv : FMap) (argCode : List Asm),
      lookupF Φ f = some (info, Φv)
      ∧ compileArgs Φ Γ (off + 1 + info.rets) (n + 1) args
          = some (argCode, n')
      ∧ asm = .pushLabel n :: (List.replicate info.rets (.push 0)
          ++ argCode ++ [.jump info.entry, .label n]) := by
  simp only [compileExpr, Option.bind_eq_bind] at h
  obtain ⟨⟨info, Φv⟩, hlk, h2⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨argCode, n1⟩, hargs, h3⟩ := Option.bind_eq_some_iff.mp h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h3
  exact ⟨info, Φv, argCode, hlk, h3.2 ▸ hargs, h3.1.symm⟩

private theorem args_nil_inv {Φ : FMap} {Γ : List Ident} {off n : Nat}
    {asm : List Asm} {n' : Nat}
    (h : compileArgs Φ Γ off n [] = some (asm, n')) :
    asm = [] ∧ n' = n := by
  simp only [compileArgs, Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

private theorem args_cons_inv {Φ : FMap} {Γ : List Ident} {off n : Nat}
    {e : Expr Op} {rest : List (Expr Op)} {asm : List Asm} {n' : Nat}
    (h : compileArgs Φ Γ off n (e :: rest) = some (asm, n')) :
    ∃ (restCode : List Asm) (n1 : Nat) (eCode : List Asm),
      compileArgs Φ Γ off n rest = some (restCode, n1)
      ∧ compileExpr Φ Γ (off + rest.length) n1 e = some (eCode, n')
      ∧ asm = restCode ++ eCode := by
  simp only [compileArgs, Option.bind_eq_bind] at h
  obtain ⟨⟨restCode, n1⟩, hrest, h2⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨eCode, n2⟩, he, h3⟩ := Option.bind_eq_some_iff.mp h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h3
  exact ⟨restCode, n1, eCode, hrest, h3.2 ▸ he, h3.1.symm⟩

private theorem stmt_exprStmt_inv {Φ : FMap} {Γ : List Ident}
    {F : Option FunCtx} {L : Option LoopCtx} {n : Nat} {e : Expr Op}
    {asm : List Asm} {Γ' : List Ident} {n' : Nat}
    (h : compileStmt Φ Γ F L n (.exprStmt e) = some (asm, Γ', n')) :
    compileExpr Φ Γ 0 n e = some (asm, n') ∧ Γ' = Γ := by
  simp only [compileStmt, Option.bind_eq_bind] at h
  obtain ⟨⟨eCode, n1⟩, he, h2⟩ := Option.bind_eq_some_iff.mp h
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  obtain ⟨h3, h4, h5⟩ := h2
  exact ⟨h3 ▸ h5 ▸ he, h4.symm⟩

private theorem stmt_letNone_inv {Φ : FMap} {Γ : List Ident}
    {F : Option FunCtx} {L : Option LoopCtx} {n : Nat} {xs : List Ident}
    {asm : List Asm} {Γ' : List Ident} {n' : Nat}
    (h : compileStmt Φ Γ F L n (.letDecl xs none) = some (asm, Γ', n')) :
    asm = List.replicate xs.length (.push 0) ∧ Γ' = xs ++ Γ ∧ n' = n := by
  simp only [compileStmt, Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

private theorem stmt_letSome_inv {Φ : FMap} {Γ : List Ident}
    {F : Option FunCtx} {L : Option LoopCtx} {n : Nat} {xs : List Ident}
    {e : Expr Op} {asm : List Asm} {Γ' : List Ident} {n' : Nat}
    (h : compileStmt Φ Γ F L n (.letDecl xs (some e)) = some (asm, Γ', n')) :
    compileExpr Φ Γ 0 n e = some (asm, n') ∧ Γ' = xs ++ Γ := by
  simp only [compileStmt, Option.bind_eq_bind] at h
  obtain ⟨⟨eCode, n1⟩, he, h2⟩ := Option.bind_eq_some_iff.mp h
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  exact ⟨h2.1 ▸ h2.2.2 ▸ he, h2.2.1.symm⟩

private theorem stmt_assign_inv {Φ : FMap} {Γ : List Ident}
    {F : Option FunCtx} {L : Option LoopCtx} {n : Nat} {xs : List Ident}
    {e : Expr Op} {asm : List Asm} {Γ' : List Ident} {n' : Nat}
    (h : compileStmt Φ Γ F L n (.assign xs e) = some (asm, Γ', n')) :
    ∃ (eCode acode : List Asm),
      compileExpr Φ Γ 0 n e = some (eCode, n')
      ∧ compileAssigns Γ xs = some acode
      ∧ asm = eCode ++ acode ∧ Γ' = Γ := by
  simp only [compileStmt, Option.bind_eq_bind] at h
  obtain ⟨⟨eCode, n1⟩, he, h2⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨acode, hac, h3⟩ := Option.bind_eq_some_iff.mp h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h3
  exact ⟨eCode, acode, h3.2.2 ▸ he, hac, h3.1.symm, h3.2.1.symm⟩

private theorem stmt_break_inv {Φ : FMap} {Γ : List Ident}
    {F : Option FunCtx} {L : Option LoopCtx} {n : Nat}
    {asm : List Asm} {Γ' : List Ident} {n' : Nat}
    (h : compileStmt Φ Γ F L n .break = some (asm, Γ', n')) :
    ∃ lc, L = some lc
      ∧ asm = List.replicate (Γ.length - lc.depth) .pop ++ [.jump lc.brk]
      ∧ Γ' = Γ ∧ n' = n := by
  simp only [compileStmt, Option.bind_eq_bind] at h
  obtain ⟨lc, hlc, h2⟩ := Option.bind_eq_some_iff.mp h
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  exact ⟨lc, hlc, h2.1.symm, h2.2.1.symm, h2.2.2.symm⟩

private theorem stmt_continue_inv {Φ : FMap} {Γ : List Ident}
    {F : Option FunCtx} {L : Option LoopCtx} {n : Nat}
    {asm : List Asm} {Γ' : List Ident} {n' : Nat}
    (h : compileStmt Φ Γ F L n .continue = some (asm, Γ', n')) :
    ∃ lc, L = some lc
      ∧ asm = List.replicate (Γ.length - lc.depth) .pop ++ [.jump lc.cont]
      ∧ Γ' = Γ ∧ n' = n := by
  simp only [compileStmt, Option.bind_eq_bind] at h
  obtain ⟨lc, hlc, h2⟩ := Option.bind_eq_some_iff.mp h
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  exact ⟨lc, hlc, h2.1.symm, h2.2.1.symm, h2.2.2.symm⟩

private theorem stmt_leave_inv {Φ : FMap} {Γ : List Ident}
    {F : Option FunCtx} {L : Option LoopCtx} {n : Nat}
    {asm : List Asm} {Γ' : List Ident} {n' : Nat}
    (h : compileStmt Φ Γ F L n .leave = some (asm, Γ', n')) :
    ∃ fc, F = some fc
      ∧ asm = List.replicate (Γ.length - fc.depth) .pop ++ [.jump fc.exit]
      ∧ Γ' = Γ ∧ n' = n := by
  simp only [compileStmt, Option.bind_eq_bind] at h
  obtain ⟨fc, hfc, h2⟩ := Option.bind_eq_some_iff.mp h
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  exact ⟨fc, hfc, h2.1.symm, h2.2.1.symm, h2.2.2.symm⟩

private theorem stmts_nil_inv {Φ : FMap} {Γ : List Ident}
    {F : Option FunCtx} {L : Option LoopCtx} {n : Nat}
    {asm : List Asm} {Γ' : List Ident} {n' : Nat}
    (h : compileStmts Φ Γ F L n [] = some (asm, Γ', n')) :
    asm = [] ∧ Γ' = Γ ∧ n' = n := by
  simp only [compileStmts, Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

private theorem stmts_cons_inv {Φ : FMap} {Γ : List Ident}
    {F : Option FunCtx} {L : Option LoopCtx} {n : Nat} {s : Stmt Op}
    {rest : List (Stmt Op)} {asm : List Asm} {Γ' : List Ident} {n' : Nat}
    (h : compileStmts Φ Γ F L n (s :: rest) = some (asm, Γ', n')) :
    ∃ (is1 : List Asm) (Γ1 : List Ident) (n1 : Nat) (is2 : List Asm),
      compileStmt Φ Γ F L n s = some (is1, Γ1, n1)
      ∧ compileStmts Φ Γ1 F L n1 rest = some (is2, Γ', n')
      ∧ asm = is1 ++ is2 := by
  simp only [compileStmts, Option.bind_eq_bind] at h
  obtain ⟨⟨is1, Γ1, n1⟩, h1, h2⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨is2, Γ2, n2⟩, h3, h4⟩ := Option.bind_eq_some_iff.mp h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h4
  exact ⟨is1, Γ1, n1, is2, h1, h4.2.1 ▸ h4.2.2 ▸ h3, h4.1.symm⟩

/-- Monotonicity of the depth guards in the region length. -/
theorem FDepthOK.mono {F : Option FunCtx} {V W : VEnv yulD}
    (h : FDepthOK F V) (hle : V.length ≤ W.length) : FDepthOK F W := by
  cases F with
  | none => trivial
  | some fc => exact Nat.le_trans h hle

theorem LDepthOK.mono {L : Option LoopCtx} {V W : VEnv yulD}
    (h : LDepthOK L V) (hle : V.length ≤ W.length) : LDepthOK L W := by
  cases L with
  | none => trivial
  | some lc => exact Nat.le_trans h hle

/-- `bindZeros` binds exactly the given names. -/
theorem names_bindZeros (xs : List Ident) :
    names (YulSemantics.bindZeros yulD xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    show x :: names (YulSemantics.bindZeros yulD xs) = x :: xs
    rw [ih]

private theorem block_inv {Φ : FMap} {Γ : List Ident} {F : Option FunCtx}
    {L : Option LoopCtx} {n : Nat} {body : List (Stmt Op)}
    {asm : List Asm} {n' : Nat}
    (h : compileBlock Φ Γ F L n body = some (asm, n')) :
    ∃ (scope : FScopeInfo) (n1 : Nat) (stmtsAsm : List Asm)
      (Γb : List Ident) (n2 : Nat),
      hoistInfos n body = (scope, n1)
      ∧ (scope.map Prod.fst).Nodup
      ∧ compileStmts (scope :: Φ) Γ F L n1 body = some (stmtsAsm, Γb, n2)
      ∧ asm = stmtsAsm ++ List.replicate (Γb.length - Γ.length) .pop
      ∧ n' = n2 := by
  rw [compileBlock] at h
  rcases hh : hoistInfos n body with ⟨scope, n1⟩
  rw [hh] at h
  dsimp only at h
  by_cases hnd : (scope.map Prod.fst).Nodup
  · rw [if_pos hnd, Option.bind_eq_bind] at h
    obtain ⟨⟨stmtsAsm, Γb, n2⟩, hs, h2⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.some.injEq, Prod.mk.injEq] at h2
    exact ⟨scope, n1, stmtsAsm, Γb, n2, rfl, hnd, hs, h2.1.symm, h2.2.symm⟩
  · rw [if_neg hnd] at h
    exact absurd h (by simp)

private theorem stmt_block_inv {Φ : FMap} {Γ : List Ident}
    {F : Option FunCtx} {L : Option LoopCtx} {n : Nat}
    {body : List (Stmt Op)} {asm : List Asm} {Γ' : List Ident} {n' : Nat}
    (h : compileStmt Φ Γ F L n (.block body) = some (asm, Γ', n')) :
    compileBlock Φ Γ F L n body = some (asm, n') ∧ Γ' = Γ := by
  simp only [compileStmt, Option.bind_eq_bind] at h
  obtain ⟨⟨is, n1⟩, hb, h2⟩ := Option.bind_eq_some_iff.mp h
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  exact ⟨h2.1 ▸ h2.2.2 ▸ hb, h2.2.1.symm⟩

private theorem stmt_cond_inv {Φ : FMap} {Γ : List Ident}
    {F : Option FunCtx} {L : Option LoopCtx} {n : Nat} {ce : Expr Op}
    {body : List (Stmt Op)} {asm : List Asm} {Γ' : List Ident} {n' : Nat}
    (h : compileStmt Φ Γ F L n (.cond ce body) = some (asm, Γ', n')) :
    ∃ (cCode : List Asm) (n1 : Nat) (bodyCode : List Asm),
      compileExpr Φ Γ 0 (n + 1) ce = some (cCode, n1)
      ∧ compileBlock Φ Γ F L n1 body = some (bodyCode, n')
      ∧ asm = cCode ++ [.op .iszero, .jumpi n] ++ bodyCode ++ [.label n]
      ∧ Γ' = Γ := by
  simp only [compileStmt, Option.bind_eq_bind] at h
  obtain ⟨⟨cCode, n1⟩, hce, h2⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨bodyCode, n2⟩, hb, h3⟩ := Option.bind_eq_some_iff.mp h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h3
  exact ⟨cCode, n1, bodyCode, hce, h3.2.2 ▸ hb, h3.1.symm, h3.2.1.symm⟩

private theorem stmt_switch_inv {Φ : FMap} {Γ : List Ident}
    {F : Option FunCtx} {L : Option LoopCtx} {n : Nat} {c : Expr Op}
    {cases : List (YulSemantics.Literal × Block Op)} {dflt : Option (Block Op)}
    {asm : List Asm} {Γ' : List Ident} {n' : Nat}
    (h : compileStmt Φ Γ F L n (.switch c cases dflt) = some (asm, Γ', n')) :
    ∃ (cCode : List Asm) (n1 : Nat) (casesAsm : List Asm) (n2 : Nat) (defAsm : List Asm),
      compileExpr Φ Γ 0 (n + 1) c = some (cCode, n1)
      ∧ compileSwitchCases Φ Γ F L n n1 cases = some (casesAsm, n2)
      ∧ compileBlock Φ Γ F L n2 (dflt.getD []) = some (defAsm, n')
      ∧ asm = cCode ++ casesAsm ++ .pop :: defAsm ++ [.label n]
      ∧ Γ' = Γ := by
  rw [compileStmt.eq_def] at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨cCode, n1⟩, hce, h2⟩ := h
  obtain ⟨⟨casesAsm, n2⟩, hcs, h3⟩ := h2
  obtain ⟨⟨defAsm, n3⟩, hdef, h4⟩ := h3
  simp only [Option.some.injEq, Prod.mk.injEq] at h4
  refine ⟨cCode, n1, casesAsm, n2, defAsm, hce, hcs, ?_, h4.1.symm, h4.2.1.symm⟩
  rw [← h4.2.2]
  cases dflt <;> exact hdef

/-- The block `selectSwitch` runs is always compiled (as some case body, or the
default). Provides the `compileBlock` witness the switch simulation feeds to the
block's induction hypothesis. -/
private theorem selectSwitch_compiled {Φ : FMap} {Γ : List Ident}
    {F : Option FunCtx} {L : Option LoopCtx} {lend : Label} {cv : U256}
    {defAsm : List Asm} {n2 n3 : Nat} {dflt : Option (Block Op)}
    (hdef : compileBlock Φ Γ F L n2 (dflt.getD []) = some (defAsm, n3)) :
    ∀ (cases : List (YulSemantics.Literal × Block Op)) {casesAsm : List Asm} {n1 : Nat},
      compileSwitchCases Φ Γ F L lend n1 cases = some (casesAsm, n2) →
      ∃ m bAsm m',
        compileBlock Φ Γ F L m (YulSemantics.selectSwitch yulD cv cases dflt) = some (bAsm, m') := by
  intro cases
  induction cases with
  | nil => intro casesAsm n1 hcs; exact ⟨n2, defAsm, n3, hdef⟩
  | cons vb rest ih =>
    intro casesAsm n1 hcs
    obtain ⟨v, b⟩ := vb
    simp only [compileSwitchCases, Option.bind_eq_bind] at hcs
    obtain ⟨⟨bAsm, m1⟩, hb, h2⟩ := Option.bind_eq_some_iff.mp hcs
    obtain ⟨⟨restAsm, m2⟩, hrest, h3⟩ := Option.bind_eq_some_iff.mp h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h3
    obtain ⟨rfl, rfl⟩ := h3
    by_cases hmatch : cv = litValue v
    · exact ⟨n1 + 1, bAsm, m1, by
        rw [show YulSemantics.selectSwitch yulD cv ((v, b) :: rest) dflt = b from by
          simp [YulSemantics.selectSwitch, hmatch]]; exact hb⟩
    · obtain ⟨m, bAsm', m', hbc⟩ := ih hrest
      exact ⟨m, bAsm', m', by
        rw [show YulSemantics.selectSwitch yulD cv ((v, b) :: rest) dflt
          = YulSemantics.selectSwitch yulD cv rest dflt from by
          simp [YulSemantics.selectSwitch, hmatch]]; exact hbc⟩

/-- Turn a `compileBlock` equation into the `compileStmt (.block …)`
form the statement motive consumes. -/
private theorem stmt_of_block {Φ : FMap} {Γ : List Ident}
    {F : Option FunCtx} {L : Option LoopCtx} {n : Nat}
    {body : List (Stmt Op)} {asm : List Asm} {n' : Nat}
    (h : compileBlock Φ Γ F L n body = some (asm, n')) :
    compileStmt Φ Γ F L n (.block body) = some (asm, Γ, n') := by
  simp only [compileStmt, h, Option.bind_eq_bind, Option.bind_some]

/-- The dialect zero, as the truthiness test sees it. -/
private theorem ne_zero_of_ne_dzero {cv : U256} (h : cv ≠ yulD.zero) :
    cv ≠ 0 := h

/-- A label placed anywhere in the program is defined. -/
private theorem mem_labelDefs_of_split {prog pre c' : List Asm} {l : Label}
    (h : prog = pre ++ .label l :: c') : l ∈ labelDefs prog := by
  rw [h, labelDefs_append]
  exact List.mem_append_right _
    (by rw [labelDefs_label]; exact List.mem_cons_self ..)

/-- Pushing `k` zeros (the call-site initialization of the callee's return
slots). -/
private theorem push_zeros {prog : List Asm} {yst : EvmState} (k : Nat)
    (S : List AVal) (rest : List Asm) :
    ASteps prog ⟨List.replicate k (.push (0 : U256)) ++ rest, S, yst⟩
      ⟨rest, words (List.replicate k 0) ++ S, yst⟩ := by
  induction k generalizing S with
  | zero => exact .refl _
  | succ k ih =>
    rw [List.replicate_succ]
    refine .head (.push (v := 0)) ?_
    have h := ih (.word 0 :: S)
    rw [show words (List.replicate (k + 1) (0 : U256)) ++ S
        = words (List.replicate k 0) ++ (.word 0 :: S) from by
      rw [List.replicate_succ']
      simp [words_append]]
    exact h

/-- The callee's initial frame, as names and as a stack image. -/
private theorem callee_frame {ps rs : List Ident} {vs : List U256}
    (hlen : vs.length = ps.length) :
    names (ps.zip vs ++ YulSemantics.bindZeros yulD rs) = ps ++ rs
    ∧ wimg (ps.zip vs ++ YulSemantics.bindZeros yulD rs)
        = words vs ++ words (List.replicate rs.length 0)
    ∧ (ps.zip vs ++ YulSemantics.bindZeros yulD rs).length
        = ps.length + rs.length := by
  have hzipn : names (ps.zip vs) = ps := by
    show (ps.zip vs).map Prod.fst = ps
    exact List.map_fst_zip (Nat.le_of_eq hlen.symm)
  have hzipw : wimg (ps.zip vs) = words vs := by
    show (ps.zip vs).map (fun p => AVal.word p.2) = vs.map .word
    rw [show (fun p : Ident × U256 => AVal.word p.2)
        = AVal.word ∘ Prod.snd from rfl, ← List.map_map]
    rw [List.map_snd_zip (Nat.le_of_eq hlen)]
  have hbzw : wimg (YulSemantics.bindZeros yulD rs)
      = words (List.replicate rs.length 0) := by
    induction rs with
    | nil => rfl
    | cons r rs ih =>
      show AVal.word yulD.zero :: wimg (YulSemantics.bindZeros yulD rs) = _
      rw [ih, yulD_zero]
      rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [names_append, hzipn, names_bindZeros]
  · rw [wimg_append, hzipw, hbzw]
  · have h1 : (ps.zip vs).length = ps.length := by
      rw [List.length_zip, hlen, Nat.min_self]
    have h2 : (YulSemantics.bindZeros yulD rs).length = rs.length := by
      have := congrArg List.length (names_bindZeros rs)
      simpa using this
    rw [List.length_append, h1, h2]

/-- Locate a function's body from its `FunOK` placement. -/
private theorem funOK_entry {prog : List Asm}
    (hnodup : (labelDefs prog).Nodup)
    {decl : YulSemantics.FDecl yulD} {info : FunInfo} {Φv : FMap}
    (hok : FunOK prog decl info Φv) :
    ∃ (lexit n₀ n₁ : Nat) (bodyAsm : List Asm) (s t : List Asm),
      compileBlock Φv (decl.params ++ decl.rets)
        (some ⟨lexit, (decl.params ++ decl.rets).length⟩) none n₀ decl.body
        = some (bodyAsm, n₁)
      ∧ prog = s ++ .label info.entry
          :: (bodyAsm ++ .label lexit
            :: epilogue decl.params.length decl.rets.length ++ t)
      ∧ findLabel info.entry prog
          = some (bodyAsm ++ .label lexit
            :: epilogue decl.params.length decl.rets.length ++ t) := by
  obtain ⟨-, -, -, -, lexit, n₀, n₁, bodyAsm, hbodyC, s, t, hst⟩ := hok
  refine ⟨lexit, n₀, n₁, bodyAsm, s, t, hbodyC, ?_, ?_⟩
  · rw [← hst]
    simp
  · have hsplit : prog = s ++ .label info.entry
        :: (bodyAsm ++ .label lexit
          :: epilogue decl.params.length decl.rets.length ++ t) := by
      rw [← hst]
      simp
    rw [hsplit]
    exact findLabel_boundary (by rw [← hsplit]; exact hnodup)

private theorem stmt_funDef_inv {Φ : FMap} {Γ : List Ident}
    {F : Option FunCtx} {L : Option LoopCtx} {n : Nat} {f : Ident}
    {ps rs : List Ident} {body : List (Stmt Op)}
    {asm : List Asm} {Γ' : List Ident} {n' : Nat}
    (h : compileStmt Φ Γ F L n (.funDef f ps rs body) = some (asm, Γ', n')) :
    ∃ (info : FunInfo) (Φv : FMap) (bodyCode : List Asm),
      lookupF Φ f = some (info, Φv)
      ∧ rs.length ≤ 1 ∧ (ps ++ rs).Nodup
      ∧ compileBlock Φ (ps ++ rs) (some ⟨n, (ps ++ rs).length⟩) none
          (n + 2) body = some (bodyCode, n')
      ∧ asm = .jump (n + 1) :: .label info.entry :: bodyCode
          ++ .label n :: epilogue ps.length rs.length ++ [.label (n + 1)]
      ∧ Γ' = Γ := by
  simp only [compileStmt, Option.bind_eq_bind] at h
  obtain ⟨⟨info, Φv⟩, hlk, h2⟩ := Option.bind_eq_some_iff.mp h
  by_cases hg : rs.length ≤ 1 ∧ (ps ++ rs).Nodup
  · rw [if_pos hg] at h2
    obtain ⟨⟨bodyCode, n1⟩, hb, h3⟩ := Option.bind_eq_some_iff.mp h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h3
    refine ⟨info, Φv, bodyCode, hlk, hg.1, hg.2, h3.2.2 ▸ hb, ?_, h3.2.1.symm⟩
    rw [← h3.1]
    simp [epilogue]
  · rw [if_neg hg] at h2
    exact absurd h2 (by simp)

/-- Layouts only grow across statements. -/
private theorem stmt_suffix {Φ : FMap} {Γ : List Ident} {F : Option FunCtx}
    {L : Option LoopCtx} {n : Nat} {s : Stmt Op} {asm : List Asm}
    {Γ' : List Ident} {n' : Nat}
    (h : compileStmt Φ Γ F L n s = some (asm, Γ', n')) :
    ∃ Δ, Γ' = Δ ++ Γ := by
  cases s with
  | exprStmt e => exact ⟨[], ((stmt_exprStmt_inv h).2).symm ▸ rfl⟩
  | letDecl xs v =>
    cases v with
    | none =>
      obtain ⟨-, rfl, -⟩ := stmt_letNone_inv h
      exact ⟨xs, rfl⟩
    | some e =>
      obtain ⟨-, rfl⟩ := stmt_letSome_inv h
      exact ⟨xs, rfl⟩
  | assign xs e =>
    obtain ⟨-, -, -, -, -, rfl⟩ := stmt_assign_inv h
    exact ⟨[], rfl⟩
  | block body => exact ⟨[], ((stmt_block_inv h).2).symm ▸ rfl⟩
  | cond c body =>
    obtain ⟨-, -, -, -, -, -, rfl⟩ := stmt_cond_inv h
    exact ⟨[], rfl⟩
  | funDef f ps rs body =>
    obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := stmt_funDef_inv h
    exact ⟨[], rfl⟩
  | forLoop init c post body =>
    simp only [compileStmt] at h
    rcases hh : hoistInfos n init with ⟨scope, n0⟩
    rw [hh] at h
    dsimp only at h
    by_cases hnd : (scope.map Prod.fst).Nodup
    · rw [if_neg (by simp [hnd]), Option.bind_eq_bind] at h
      obtain ⟨⟨initCode, Γi, n1⟩, -, h2⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨⟨cCode, n2⟩, -, h3⟩ := Option.bind_eq_some_iff.mp h2
      obtain ⟨⟨bodyCode, n3⟩, -, h4⟩ := Option.bind_eq_some_iff.mp h3
      obtain ⟨⟨postCode, n4⟩, -, h5⟩ := Option.bind_eq_some_iff.mp h4
      simp only [Option.some.injEq, Prod.mk.injEq] at h5
      exact ⟨[], h5.2.1.symm ▸ rfl⟩
    · rw [if_pos (by simp [hnd])] at h
      exact absurd h (by simp)
  | «break» =>
    obtain ⟨-, -, -, rfl, -⟩ := stmt_break_inv h
    exact ⟨[], rfl⟩
  | «continue» =>
    obtain ⟨-, -, -, rfl, -⟩ := stmt_continue_inv h
    exact ⟨[], rfl⟩
  | leave =>
    obtain ⟨-, -, -, rfl, -⟩ := stmt_leave_inv h
    exact ⟨[], rfl⟩
  | switch c cases dflt =>
    obtain ⟨-, -, -, -, -, -, -, -, -, rfl⟩ := stmt_switch_inv h
    exact ⟨[], rfl⟩

private theorem stmts_suffix {Φ : FMap} {F : Option FunCtx}
    {L : Option LoopCtx} :
    ∀ {ss : List (Stmt Op)} {Γ : List Ident} {n : Nat} {asm : List Asm}
      {Γ' : List Ident} {n' : Nat},
      compileStmts Φ Γ F L n ss = some (asm, Γ', n') →
      ∃ Δ, Γ' = Δ ++ Γ := by
  intro ss
  induction ss with
  | nil =>
    intro Γ n asm Γ' n' h
    obtain ⟨-, rfl, -⟩ := stmts_nil_inv h
    exact ⟨[], rfl⟩
  | cons s rest ih =>
    intro Γ n asm Γ' n' h
    obtain ⟨is1, Γ1, n1, is2, h1, h2, rfl⟩ := stmts_cons_inv h
    obtain ⟨Δ1, rfl⟩ := stmt_suffix h1
    obtain ⟨Δ2, rfl⟩ := ih h2
    exact ⟨Δ2 ++ Δ1, by simp⟩

/-- Trimming commutes with `restore` (down to a depth below the restored
region). -/
theorem trim_restore {V Vb : VEnv yulD} {d : Nat} (hd : d ≤ V.length)
    (hlen : V.length ≤ Vb.length) :
    trim d (YulSemantics.restore V Vb) = trim d Vb := by
  unfold trim YulSemantics.restore
  rw [List.drop_drop]
  congr 1
  rw [List.length_drop]
  omega

/-- Dropping past a prepended block. -/
private theorem drop_append_plus {α : Type} (Δ Γ : List α) (k : Nat) :
    (Δ ++ Γ).drop (Δ.length + k) = Γ.drop k := by
  induction Δ with
  | nil => simp
  | cons a Δ ih =>
    show List.drop (Δ.length + 1 + k) (a :: (Δ ++ Γ)) = _
    rw [show Δ.length + 1 + k = (Δ.length + k) + 1 from by omega,
      List.drop_succ_cons]
    exact ih

/-- The bare non-local exits leave the environment unchanged. -/
private theorem names_trim_self (d : Nat) (V : VEnv yulD) :
    names (trim d V) = (names V).drop (V.length - d) := by
  unfold trim
  rw [names_drop]

/-- Retarget a non-local exit at a `trim`-equal environment. -/
theorem ASimNL.retarget {prog : List Asm} {yst yst' : EvmState}
    {V W W' : VEnv yulD} {asm : List Asm} {l : Label} {d : Nat}
    (h : ASimNL prog yst V asm yst' W l d)
    (heq : trim d W' = trim d W) :
    ASimNL prog yst V asm yst' W' l d := by
  intro pre c cL σ hp hfind
  rw [heq]
  exact h pre c cL σ hp hfind

/-- `find?` reaches the first entry named `f` past a prefix that avoids it. -/
private theorem find?_mem_head {pre tl : FScopeInfo} {f : Ident} {x : FunInfo}
    (hf : f ∉ pre.map Prod.fst) :
    (pre ++ (f, x) :: tl).find? (fun q => q.1 = f) = some (f, x) := by
  induction pre with
  | nil => simp
  | cons a pre ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hf
    rw [List.cons_append, List.find?_cons_of_neg (by
      simp only [decide_eq_true_eq]; exact fun h => hf.1 h.symm)]
    exact ih hf.2

/-- On a `Nodup`-named scope, the first entry of any suffix headed by `f` is
what `find?` returns. -/
private theorem find?_suffix_nodup {scope_top : FScopeInfo} {f : Ident}
    {x : FunInfo} {tl : FScopeInfo}
    (hnd : (scope_top.map Prod.fst).Nodup)
    (hsuf : (f, x) :: tl <:+ scope_top) :
    scope_top.find? (fun q => q.1 = f) = some (f, x) := by
  obtain ⟨pre, hpre⟩ := hsuf
  subst hpre
  have hfp : f ∉ pre.map Prod.fst := by
    rw [List.map_append, List.map_cons] at hnd
    exact fun hmem =>
      (List.nodup_append.mp hnd).2.2 f hmem f (by simp) rfl
  exact find?_mem_head hfp

/-- **Walking a block's statements**: the compiled block's inline `funDef`
fragments realize, entry-by-entry, the `FunOK` witnesses for the hoisted
scope. Induction over the statement list; the fixed outer scope
`scope_top` (in `Φfull`) supplies each function's label via `find?`, so the
compiled `.label`/`lookupF` and the hoisted entry always agree. -/
private theorem hoist_forall2 {prog : List Asm} {Φ : FMap}
    {scope_top : FScopeInfo} {F : Option FunCtx} {L : Option LoopCtx}
    (hnd : (scope_top.map Prod.fst).Nodup) :
    ∀ (body : List (Stmt Op)) (Γ : List Ident) (nc : Nat) (asm : List Asm)
      (Γ' : List Ident) (nc' : Nat) (nh : Nat),
      compileStmts (scope_top :: Φ) Γ F L nc body = some (asm, Γ', nc') →
      asm <:+: prog →
      (hoistInfos nh body).1 <:+ scope_top →
      List.Forall₂
        (fun (p : Ident × YulSemantics.FDecl yulD) (q : Ident × FunInfo) =>
          p.1 = q.1 ∧ FunOK prog p.2 q.2 (scope_top :: Φ))
        (YulSemantics.hoist yulD body) (hoistInfos nh body).1 := by
  intro body
  induction body with
  | nil =>
    intro Γ nc asm Γ' nc' nh _ _ _
    exact List.Forall₂.nil
  | cons s rest ih =>
    intro Γ nc asm Γ' nc' nh hcs hplace hsuf
    obtain ⟨is1, Γ1, n1, is2, his1, hcs2, rfl⟩ := stmts_cons_inv hcs
    have his1p : is1 <:+: prog :=
      List.IsInfix.trans List.infix_append_left hplace
    have his2p : is2 <:+: prog :=
      List.IsInfix.trans List.infix_append_right hplace
    cases s
    case funDef f ps rs b =>
      have hsuf' : (f, (⟨nh, ps.length, rs.length⟩ : FunInfo))
          :: (hoistInfos (nh + 1) rest).1 <:+ scope_top := hsuf
      obtain ⟨info', Φv', bodyCode, hlk', hrs1, hndpr, hbodyC', hasm, -⟩ :=
        stmt_funDef_inv his1
      have hlkval : lookupF (scope_top :: Φ) f
          = some (⟨nh, ps.length, rs.length⟩, scope_top :: Φ) := by
        simp only [lookupF, find?_suffix_nodup hnd hsuf']
      have hpair := hlk'.symm.trans hlkval
      simp only [Option.some.injEq, Prod.mk.injEq] at hpair
      obtain ⟨rfl, -⟩ := hpair
      refine List.Forall₂.cons ⟨rfl, ?_⟩ ?_
      · refine ⟨rfl, rfl, hrs1, hndpr, nc, nc + 2, n1, bodyCode, hbodyC', ?_⟩
        refine List.IsInfix.trans
          (⟨[.jump (nc + 1)], [.label (nc + 1)], ?_⟩ : _ <:+: is1) his1p
        rw [hasm]; simp
      · exact ih Γ1 n1 is2 Γ' nc' (nh + 1) hcs2 his2p
          ((List.suffix_cons _ _).trans hsuf')
    all_goals exact ih Γ1 n1 is2 Γ' nc' nh hcs2 his2p hsuf

/-- **Entering a block**: the hoisted compile-time scope agrees with the
semantics' hoisted scope, provided the block's compiled statements sit in
the program (their inline `funDef` fragments are what `FunOK.placed`
points at). -/
theorem hoist_ok {prog : List Asm} {funs : YulSemantics.FunEnv yulD}
    {Φ : FMap} (hΦ : FEnvOK prog funs Φ)
    {body : List (Stmt Op)} {Γ : List Ident} {F : Option FunCtx}
    {L : Option LoopCtx} {n : Nat} {scope : FScopeInfo} {n0 nc : Nat}
    {asm : List Asm} {Γ' : List Ident} {n' : Nat}
    (hh : hoistInfos n body = (scope, n0))
    (hnd : (scope.map Prod.fst).Nodup)
    (hcs : compileStmts (scope :: Φ) Γ F L nc body = some (asm, Γ', n'))
    (hplace : asm <:+: prog) :
    FEnvOK prog (YulSemantics.hoist yulD body :: funs) (scope :: Φ) := by
  have hf2 := hoist_forall2 (Φ := Φ) (scope_top := scope) (F := F) (L := L)
    hnd body Γ nc asm Γ' n' n hcs hplace
    (by simp only [hh]; exact List.suffix_refl _)
  simp only [hh] at hf2
  exact FEnvOK.cons hf2 hΦ

private theorem stmt_forLoop_inv {Φ : FMap} {Γ : List Ident}
    {F : Option FunCtx} {L : Option LoopCtx} {n : Nat} {init : List (Stmt Op)}
    {ce : Expr Op} {post body : List (Stmt Op)}
    {asm : List Asm} {Γ' : List Ident} {n' : Nat}
    (h : compileStmt Φ Γ F L n (.forLoop init ce post body)
      = some (asm, Γ', n')) :
    ∃ (scope : FScopeInfo) (n0 : Nat) (initCode : List Asm) (Γi : List Ident)
      (n1 : Nat) (cCode : List Asm) (n2 : Nat) (bodyCode : List Asm)
      (n3 : Nat) (postCode : List Asm),
      hoistInfos n init = (scope, n0)
      ∧ (scope.map Prod.fst).Nodup
      ∧ compileStmts (scope :: Φ) Γ F L (n0 + 3) init
          = some (initCode, Γi, n1)
      ∧ compileExpr (scope :: Φ) Γi 0 n1 ce = some (cCode, n2)
      ∧ compileBlock (scope :: Φ) Γi F (some ⟨n0 + 2, n0 + 1, Γi.length⟩)
          n2 body = some (bodyCode, n3)
      ∧ compileBlock (scope :: Φ) Γi F none n3 post = some (postCode, n')
      ∧ asm = initCode
          ++ .label n0 :: cCode ++ [.op .iszero, .jumpi (n0 + 2)]
          ++ bodyCode ++ .label (n0 + 1) :: postCode ++ .jump n0
          :: .label (n0 + 2)
          :: List.replicate (Γi.length - Γ.length) .pop
      ∧ Γ' = Γ := by
  simp only [compileStmt] at h
  rcases hh : hoistInfos n init with ⟨scope, n0⟩
  rw [hh] at h
  dsimp only at h
  by_cases hnd : (scope.map Prod.fst).Nodup
  · rw [if_neg (by simp [hnd]), Option.bind_eq_bind] at h
    obtain ⟨⟨initCode, Γi, n1⟩, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨cCode, n2⟩, h3, h4⟩ := Option.bind_eq_some_iff.mp h2
    obtain ⟨⟨bodyCode, n3⟩, h5, h6⟩ := Option.bind_eq_some_iff.mp h4
    obtain ⟨⟨postCode, n4⟩, h7, h8⟩ := Option.bind_eq_some_iff.mp h6
    simp only [Option.some.injEq, Prod.mk.injEq] at h8
    refine ⟨scope, n0, initCode, Γi, n1, cCode, n2, bodyCode, n3, postCode,
      rfl, hnd, h1, h3, h5, h8.2.2 ▸ h7, ?_, h8.2.1.symm⟩
    rw [← h8.1]
    simp
  · rw [if_pos (by simp [hnd])] at h
    exact absurd h (by simp)

/-- A loop-iteration judgment only produces `normal`, `halt`, or `leave`. -/
private theorem loop_outcome {funs : YulSemantics.FunEnv yulD} {V : VEnv yulD}
    {st : EvmState} {ce : Expr Op} {post body : Block Op} {V' : VEnv yulD}
    {st' : EvmState} {o : Outcome}
    (h : YulSemantics.Step yulD funs V st (.loop ce post body)
      (.sres V' st' o)) :
    o = .normal ∨ o = .halt ∨ o = .leave := by
  generalize hcode : (YulSemantics.Code.loop ce post body
    : YulSemantics.Code Op) = code at h
  generalize hres : (YulSemantics.Res.sres V' st' o
    : YulSemantics.Res yulD) = res at h
  induction h generalizing V' st' o <;> try (cases hcode)
  case loopDone =>
    cases hres
    exact .inl rfl
  case loopCondHalt =>
    cases hres
    exact .inr (.inl rfl)
  case loopStep ihc ihbody ihpost ihrest =>
    exact ihrest rfl hres
  case loopPostHalt =>
    cases hres
    exact .inr (.inl rfl)
  case loopBreak =>
    cases hres
    exact .inl rfl
  case loopLeave =>
    cases hres
    exact .inr (.inr rfl)
  case loopBodyHalt =>
    cases hres
    exact .inr (.inl rfl)

/-- A block never lengthens the variable environment: its outcome env is a
`restore` of the input, whatever the outcome. -/
private theorem block_len_le {funs : YulSemantics.FunEnv yulD}
    {V : VEnv yulD} {st : EvmState} {body : Block Op} {Vend : VEnv yulD}
    {st' : EvmState} {o : Outcome}
    (h : YulSemantics.Step yulD funs V st (.stmt (.block body))
      (.sres Vend st' o)) :
    Vend.length ≤ V.length := by
  cases h with
  | block hbody =>
    simp only [YulSemantics.restore, List.length_drop]
    omega

/-! ### The simulation induction -/

set_option maxHeartbeats 1000000 in
/-- **Phase A**: every source derivation over compiled syntax is simulated
by the Asm machine (`Motive` unfolds to the relevant `ASim*` shape for each
code/result class). -/
theorem sim {prog : List Asm} (hnodup : (labelDefs prog).Nodup)
    {funs : YulSemantics.FunEnv yulD} {V : VEnv yulD} {yst : EvmState}
    {c : YulSemantics.Code Op} {res : YulSemantics.Res yulD}
    (h : YulSemantics.Step yulD funs V yst c res) :
    Motive prog funs V yst c res := by
  induction h with
  | lit =>
    intro Φ off n asm n' hc hΦ
    obtain ⟨rfl, rfl⟩ := expr_lit_inv hc
    exact asimE_push _
  | var hget =>
    intro Φ off n asm n' hc hΦ
    obtain ⟨idx, h16, hidx, rfl, rfl⟩ := expr_var_inv hc
    exact asimE_var h16 hget hidx
  | builtinOk hargs hb ihargs =>
    intro Φ off n asm n' hc hΦ
    obtain ⟨argCode, hargs', rfl⟩ := expr_builtin_inv hc
    exact asimE_op ((ihargs Φ off n argCode n' hargs').2 hΦ) hb
  | builtinHalt hargs hb ihargs =>
    intro Φ off n asm n' hc hΦ
    obtain ⟨argCode, hargs', rfl⟩ := expr_builtin_inv hc
    exact asimE_opHalt ((ihargs Φ off n argCode n' hargs').2 hΦ) hb
  | builtinArgsHalt hargs ihargs =>
    intro Φ off n asm n' hc hΦ
    obtain ⟨argCode, hargs', rfl⟩ := expr_builtin_inv hc
    exact (ihargs Φ off n argCode n' hargs' hΦ).extend _
  | callOk hargs hlk harity hbody ho ihargs ihbody =>
    rename_i funs0 V0 st0 fn args0 argvals st1 decl cenv Vend st2 o
    intro Φ off n asm n' hc hΦ
    obtain ⟨info, Φv, argCode, hlkF, hargsC, rfl⟩ := expr_call_inv hc
    obtain ⟨info', Φv', hlkF', hok, hΦv⟩ := lookupF_ok hΦ hlk
    have hpair := hlkF.symm.trans hlkF'
    injection hpair with hpair
    cases hpair
    have hrs : info.rets = decl.rets.length := hok.2.1
    have hrs1 : decl.rets.length ≤ 1 := hok.2.2.1
    have hnodupPR : (decl.params ++ decl.rets).Nodup := hok.2.2.2.1
    obtain ⟨lexit, n₀, n₁, bodyAsm, s, t, hbodyC, hsplitP, hfindEntry⟩ :=
      funOK_entry hnodup hok
    obtain ⟨hnamesV₀, hwimgV₀, hlenV₀⟩ := callee_frame
      (rs := decl.rets) harity
    obtain ⟨hlenA, hsimA⟩ := ihargs Φ (off + 1 + info.rets) (n + 1) argCode
      n' hargsC
    have hbodyStmt : compileStmt Φv
        (names (decl.params.zip argvals
          ++ YulSemantics.bindZeros yulD decl.rets))
        (some ⟨lexit, (decl.params ++ decl.rets).length⟩) none n₀
        (.block decl.body)
        = some (bodyAsm,
            names (decl.params.zip argvals
              ++ YulSemantics.bindZeros yulD decl.rets), n₁) := by
      rw [hnamesV₀]
      exact stmt_of_block hbodyC
    have hFd : FDepthOK (some ⟨lexit, (decl.params ++ decl.rets).length⟩)
        (decl.params.zip argvals ++ YulSemantics.bindZeros yulD decl.rets) := by
      show (decl.params ++ decl.rets).length ≤ _
      rw [hlenV₀]
      simp
    have hsimBody := ihbody Φv
      (some ⟨lexit, (decl.params ++ decl.rets).length⟩) none n₀ bodyAsm
      _ n₁ hFd trivial hbodyStmt
    have hVendLe : Vend.length
        ≤ (decl.params.zip argvals
          ++ YulSemantics.bindZeros yulD decl.rets).length :=
      block_len_le hbody
    intro pre c τ σ hp hτ
    have hfindRet : findLabel n prog = some c := by
      have hsplitR : prog = (pre ++ .pushLabel n
          :: (List.replicate info.rets (.push 0) ++ argCode
            ++ [.jump info.entry])) ++ .label n :: c := by
        rw [hp]; simp
      rw [hsplitR]
      exact findLabel_boundary (by rw [← hsplitR]; exact hnodup)
    have hfindExit : findLabel lexit prog
        = some (epilogue decl.params.length decl.rets.length ++ t) := by
      have hsplitE : prog = (s ++ .label info.entry :: bodyAsm)
          ++ .label lexit
            :: (epilogue decl.params.length decl.rets.length ++ t) := by
        rw [hsplitP]; simp
      rw [hsplitE]
      exact findLabel_boundary (by rw [← hsplitE]; exact hnodup)
    have hdef : n ∈ labelDefs prog :=
      mem_labelDefs_of_split (pre := pre ++ .pushLabel n
          :: (List.replicate info.rets (.push 0) ++ argCode
            ++ [.jump info.entry])) (c' := c)
        (by rw [hp]; simp)
    have h1 : AStep prog
        ⟨.pushLabel n :: (List.replicate info.rets (.push 0)
            ++ (argCode ++ [.jump info.entry, .label n] ++ c)),
          τ ++ wimg V0 ++ σ, st0⟩
        ⟨List.replicate info.rets (.push 0)
            ++ (argCode ++ [.jump info.entry, .label n] ++ c),
          .code n :: (τ ++ wimg V0 ++ σ), st0⟩ := .pushLabel hdef
    have h2 := push_zeros (prog := prog) (yst := st0) info.rets
      (.code n :: (τ ++ wimg V0 ++ σ))
      (argCode ++ [.jump info.entry, .label n] ++ c)
    have h3 : ASteps prog
        ⟨argCode ++ ([.jump info.entry, .label n] ++ c),
          (words (List.replicate info.rets 0) ++ .code n :: τ)
            ++ wimg V0 ++ σ, st0⟩
        ⟨[.jump info.entry, .label n] ++ c,
          words argvals ++ ((words (List.replicate info.rets 0)
            ++ .code n :: τ) ++ wimg V0 ++ σ), st1⟩ :=
      (hsimA hΦ) (pre ++ .pushLabel n :: List.replicate info.rets (.push 0))
        ([.jump info.entry, .label n] ++ c)
        (words (List.replicate info.rets 0) ++ .code n :: τ) σ
        (by rw [hp]; simp) (by simp [hτ]; omega)
    have h4 : AStep prog
        ⟨.jump info.entry :: ([.label n] ++ c),
          words argvals ++ ((words (List.replicate info.rets 0)
            ++ .code n :: τ) ++ wimg V0 ++ σ), st1⟩
        ⟨bodyAsm ++ .label lexit
            :: epilogue decl.params.length decl.rets.length ++ t,
          words argvals ++ ((words (List.replicate info.rets 0)
            ++ .code n :: τ) ++ wimg V0 ++ σ), st1⟩ := .jump hfindEntry
    have hbodyEpi : ASteps prog
        ⟨bodyAsm ++ .label lexit
            :: epilogue decl.params.length decl.rets.length ++ t,
          wimg (decl.params.zip argvals
            ++ YulSemantics.bindZeros yulD decl.rets)
            ++ (.code n :: (τ ++ wimg V0 ++ σ)), st1⟩
        ⟨c, words (decl.rets.map (fun r =>
            (YulSemantics.VEnv.get Vend r).getD yulD.zero))
          ++ (τ ++ wimg V0 ++ σ), st2⟩ := by
      rcases ho with rfl | rfl
      · -- normal completion: run body, step past the exit label, epilogue
        obtain ⟨hΓ', hlenB, hsimN⟩ := hsimBody
        have hnamesVend : names Vend = decl.params ++ decl.rets := by
          rw [← hΓ', hnamesV₀]
        have hepi := asim_epilogue (yst := st2) (Vend := Vend)
          (ps := decl.params) (rs := decl.rets)
          hnamesVend hnodupPR hrs1 hfindRet
          (s ++ .label info.entry :: bodyAsm ++ [.label lexit]) t
          (τ ++ wimg V0 ++ σ)
          (by rw [hsplitP]; simp)
        have hbodySteps := (hsimN hΦv)
          (s ++ [.label info.entry])
          (.label lexit :: epilogue decl.params.length decl.rets.length ++ t)
          (.code n :: (τ ++ wimg V0 ++ σ))
          (by rw [hsplitP]; simp)
        have hlabel : AStep prog
            ⟨.label lexit
                :: (epilogue decl.params.length decl.rets.length ++ t),
              wimg Vend ++ (.code n :: (τ ++ wimg V0 ++ σ)), st2⟩
            ⟨epilogue decl.params.length decl.rets.length ++ t,
              wimg Vend ++ (.code n :: (τ ++ wimg V0 ++ σ)), st2⟩ := .label
        have hcombined := hbodySteps.trans (.head hlabel hepi)
        simpa only [List.append_assoc, List.cons_append] using hcombined
      · -- leave: jump straight to the exit label, then epilogue
        obtain ⟨fc, hfceq, hlenB, hnm, hsimL⟩ := hsimBody
        injection hfceq with hfe
        subst hfe
        have hlenEq : Vend.length = (decl.params ++ decl.rets).length := by
          rw [List.length_append]
          rw [hlenV₀] at hVendLe hlenB
          omega
        have htrim : trim (decl.params ++ decl.rets).length Vend = Vend := by
          unfold trim
          rw [show Vend.length - (decl.params ++ decl.rets).length = 0 by omega]
          simp
        have hzero : (decl.params.zip argvals
            ++ YulSemantics.bindZeros yulD decl.rets).length
            - (decl.params ++ decl.rets).length = 0 := by
          rw [hlenV₀, List.length_append]; omega
        have hnamesVend : names Vend = decl.params ++ decl.rets := by
          rw [htrim] at hnm
          rw [hnm, hzero, List.drop_zero, hnamesV₀]
        have hepi := asim_epilogue (yst := st2) (Vend := Vend)
          (ps := decl.params) (rs := decl.rets)
          hnamesVend hnodupPR hrs1 hfindRet
          (s ++ .label info.entry :: bodyAsm ++ [.label lexit]) t
          (τ ++ wimg V0 ++ σ)
          (by rw [hsplitP]; simp)
        have hbodySteps := (hsimL hΦv)
          (s ++ [.label info.entry])
          (.label lexit :: epilogue decl.params.length decl.rets.length ++ t)
          (epilogue decl.params.length decl.rets.length ++ t)
          (.code n :: (τ ++ wimg V0 ++ σ))
          (by rw [hsplitP]; simp)
          hfindExit
        rw [htrim] at hbodySteps
        have hcombined := hbodySteps.trans hepi
        simpa only [List.append_assoc, List.cons_append] using hcombined
    have hshape : Asm.pushLabel n :: (List.replicate info.rets (.push 0)
          ++ argCode ++ [.jump info.entry, .label n]) ++ c
        = Asm.pushLabel n :: (List.replicate info.rets (.push 0)
          ++ (argCode ++ [.jump info.entry, .label n] ++ c)) := by
      simp
    rw [hshape]
    refine (ASteps.head h1 h2).trans ?_
    refine (by simpa [List.append_assoc] using h3 : ASteps prog _ _).trans ?_
    refine (ASteps.single (by simpa using h4)).trans ?_
    simpa [List.append_assoc, hwimgV₀, hrs] using hbodyEpi
  | callHalt hargs hlk harity hbody ihargs ihbody =>
    rename_i funs0 V0 st0 fn args0 argvals st1 decl cenv Vend st2
    intro Φ off n asm n' hc hΦ
    obtain ⟨info, Φv, argCode, hlkF, hargsC, rfl⟩ := expr_call_inv hc
    obtain ⟨info', Φv', hlkF', hok, hΦv⟩ := lookupF_ok hΦ hlk
    have hpair := hlkF.symm.trans hlkF'
    injection hpair with hpair
    cases hpair
    have hrs : info.rets = decl.rets.length := hok.2.1
    obtain ⟨lexit, n₀, n₁, bodyAsm, s, t, hbodyC, hsplitP, hfindEntry⟩ :=
      funOK_entry hnodup hok
    obtain ⟨hnamesV₀, hwimgV₀, hlenV₀⟩ := callee_frame
      (rs := decl.rets) harity
    obtain ⟨hlenA, hsimA⟩ := ihargs Φ (off + 1 + info.rets) (n + 1) argCode
      n' hargsC
    have hbodyStmt : compileStmt Φv
        (names (decl.params.zip argvals
          ++ YulSemantics.bindZeros yulD decl.rets))
        (some ⟨lexit, (decl.params ++ decl.rets).length⟩) none n₀
        (.block decl.body)
        = some (bodyAsm,
            names (decl.params.zip argvals
              ++ YulSemantics.bindZeros yulD decl.rets), n₁) := by
      rw [hnamesV₀]
      exact stmt_of_block hbodyC
    have hFd : FDepthOK (some ⟨lexit, (decl.params ++ decl.rets).length⟩)
        (decl.params.zip argvals ++ YulSemantics.bindZeros yulD decl.rets) := by
      show (decl.params ++ decl.rets).length ≤ _
      rw [hlenV₀]
      simp
    have hsimBody := ihbody Φv
      (some ⟨lexit, (decl.params ++ decl.rets).length⟩) none n₀ bodyAsm
      _ n₁ hFd trivial hbodyStmt
    intro pre c τ σ hp hτ
    have hdef : n ∈ labelDefs prog :=
      mem_labelDefs_of_split (pre := pre ++ .pushLabel n
          :: (List.replicate info.rets (.push 0) ++ argCode
            ++ [.jump info.entry])) (c' := c)
        (by rw [hp]; simp)
    have h1 : AStep prog
        ⟨.pushLabel n :: (List.replicate info.rets (.push 0)
            ++ (argCode ++ [.jump info.entry, .label n] ++ c)),
          τ ++ wimg V0 ++ σ, st0⟩
        ⟨List.replicate info.rets (.push 0)
            ++ (argCode ++ [.jump info.entry, .label n] ++ c),
          .code n :: (τ ++ wimg V0 ++ σ), st0⟩ := .pushLabel hdef
    have h2 := push_zeros (prog := prog) (yst := st0) info.rets
      (.code n :: (τ ++ wimg V0 ++ σ))
      (argCode ++ [.jump info.entry, .label n] ++ c)
    have h3 : ASteps prog
        ⟨argCode ++ ([.jump info.entry, .label n] ++ c),
          (words (List.replicate info.rets 0) ++ .code n :: τ)
            ++ wimg V0 ++ σ, st0⟩
        ⟨[.jump info.entry, .label n] ++ c,
          words argvals ++ ((words (List.replicate info.rets 0)
            ++ .code n :: τ) ++ wimg V0 ++ σ), st1⟩ :=
      (hsimA hΦ) (pre ++ .pushLabel n :: List.replicate info.rets (.push 0))
        ([.jump info.entry, .label n] ++ c)
        (words (List.replicate info.rets 0) ++ .code n :: τ) σ
        (by rw [hp]; simp) (by simp [hτ]; omega)
    have h4 : AStep prog
        ⟨.jump info.entry :: ([.label n] ++ c),
          words argvals ++ ((words (List.replicate info.rets 0)
            ++ .code n :: τ) ++ wimg V0 ++ σ), st1⟩
        ⟨bodyAsm ++ .label lexit
            :: epilogue decl.params.length decl.rets.length ++ t,
          words argvals ++ ((words (List.replicate info.rets 0)
            ++ .code n :: τ) ++ wimg V0 ++ σ), st1⟩ := .jump hfindEntry
    have hstkV₀ : words argvals ++ ((words (List.replicate info.rets 0)
          ++ .code n :: τ) ++ wimg V0 ++ σ)
        = wimg (decl.params.zip argvals
            ++ YulSemantics.bindZeros yulD decl.rets)
          ++ (.code n :: (τ ++ wimg V0 ++ σ)) := by
      rw [hwimgV₀, hrs]
      simp
    obtain ⟨conf, hsteps, hhalt⟩ := (hsimBody hΦv)
      (s ++ [.label info.entry])
      (.label lexit :: epilogue decl.params.length decl.rets.length ++ t)
      (.code n :: (τ ++ wimg V0 ++ σ))
      (by rw [hsplitP]; simp)
    refine ⟨conf, ?_, hhalt⟩
    have hshape : Asm.pushLabel n :: (List.replicate info.rets (.push 0)
          ++ argCode ++ [.jump info.entry, .label n]) ++ c
        = Asm.pushLabel n :: (List.replicate info.rets (.push 0)
          ++ (argCode ++ [.jump info.entry, .label n] ++ c)) := by
      simp
    rw [hshape]
    refine (ASteps.head h1 h2).trans ?_
    refine (by simpa [List.append_assoc] using h3 : ASteps prog _ _).trans ?_
    refine (ASteps.single (by simpa using h4)).trans ?_
    simpa [List.append_assoc, hwimgV₀, hrs] using hsteps
  | callArgsHalt hargs ihargs =>
    rename_i funs0 V0 st0 f0 args0 st1
    intro Φ off n asm n' hc hΦ
    obtain ⟨info, Φv, argCode, hlk, hargsC, rfl⟩ := expr_call_inv hc
    intro pre c τ σ hp hτ
    have hdef : n ∈ labelDefs prog :=
      mem_labelDefs_of_split (pre := pre ++ .pushLabel n
          :: (List.replicate info.rets (.push 0) ++ argCode
            ++ [.jump info.entry])) (c' := c)
        (by rw [hp]; simp)
    have h1 : AStep prog
        ⟨.pushLabel n :: (List.replicate info.rets (.push 0)
            ++ (argCode ++ [.jump info.entry, .label n] ++ c)),
          τ ++ wimg V0 ++ σ, st0⟩
        ⟨List.replicate info.rets (.push 0)
            ++ (argCode ++ [.jump info.entry, .label n] ++ c),
          .code n :: (τ ++ wimg V0 ++ σ), st0⟩ := .pushLabel hdef
    have h2 := push_zeros (prog := prog) (yst := st0) info.rets
      (.code n :: (τ ++ wimg V0 ++ σ))
      (argCode ++ [.jump info.entry, .label n] ++ c)
    obtain ⟨conf, hsteps, hhalt⟩ :=
      (ihargs Φ (off + 1 + info.rets) (n + 1) argCode n' hargsC hΦ)
        (pre ++ .pushLabel n :: List.replicate info.rets (.push 0))
        ([.jump info.entry, .label n] ++ c)
        (words (List.replicate info.rets 0) ++ .code n :: τ) σ
        (by rw [hp]; simp)
        (by simp [hτ]; omega)
    refine ⟨conf, ?_, hhalt⟩
    have hshape : Asm.pushLabel n :: (List.replicate info.rets (.push 0)
          ++ argCode ++ [.jump info.entry, .label n]) ++ c
        = Asm.pushLabel n :: (List.replicate info.rets (.push 0)
          ++ (argCode ++ [.jump info.entry, .label n] ++ c)) := by
      simp
    rw [hshape]
    refine (ASteps.head h1 h2).trans ?_
    have hstk : words (List.replicate info.rets 0)
        ++ (.code n :: (τ ++ wimg V0 ++ σ))
        = (words (List.replicate info.rets 0) ++ .code n :: τ)
          ++ wimg V0 ++ σ := by
      simp
    rw [hstk]
    simpa [List.append_assoc] using hsteps
  | argsNil =>
    intro Φ off n asm n' hc
    obtain ⟨rfl, rfl⟩ := args_nil_inv hc
    refine ⟨rfl, fun hΦ pre c τ σ hp hτ => ?_⟩
    exact .refl _
  | argsCons hrest hhead ihrest ihhead =>
    intro Φ off n asm n' hc
    obtain ⟨restCode, n1, eCode, hr, he, rfl⟩ := args_cons_inv hc
    obtain ⟨hlen, hR⟩ := ihrest Φ off n restCode n1 hr
    refine ⟨by simpa using hlen, fun hΦ => ?_⟩
    exact ASimE.compArgs hlen (hR hΦ)
      (by simpa [hlen] using ihhead Φ (off + _) n1 eCode n' he hΦ)
  | argsRestHalt hrest ihrest =>
    intro Φ off n asm n' hc hΦ
    obtain ⟨restCode, n1, eCode, hr, he, rfl⟩ := args_cons_inv hc
    exact (ihrest Φ off n restCode n1 hr hΦ).extend _
  | argsHeadHalt hrest hhead ihrest ihhead =>
    intro Φ off n asm n' hc hΦ
    obtain ⟨restCode, n1, eCode, hr, he, rfl⟩ := args_cons_inv hc
    obtain ⟨hlen, hR⟩ := ihrest Φ off n restCode n1 hr
    exact ASimE.compArgsHalt hlen (hR hΦ)
      (by simpa [hlen] using ihhead Φ (off + _) n1 eCode n' he hΦ)
  | funDef =>
    rename_i funs1 V1 st1 f1 ps1 rs1 b1
    intro Φ F L n asm Γ' n' hF hL hc
    obtain ⟨info, Φv, bodyCode, hlk, hrs, hnd, hb, rfl, rfl⟩ :=
      stmt_funDef_inv hc
    refine ⟨rfl, Nat.le_refl _, fun hΦ => ?_⟩
    intro pre c σ hp
    have hfind : findLabel (n + 1) prog = some c := by
      have hsplit : prog = (pre ++ .jump (n + 1) :: .label info.entry
          :: bodyCode ++ .label n :: epilogue ps1.length rs1.length)
          ++ .label (n + 1) :: c := by
        rw [hp]
        simp
      rw [hsplit]
      exact findLabel_boundary (by rw [← hsplit]; exact hnodup)
    exact .single (.jump hfind)
  | block hbody ihbody =>
    rename_i funs0 V0 st0 body0 Vb stb o
    intro Φ F L n asm Γ' n' hF hL hc
    obtain ⟨hblockA, rfl⟩ := stmt_block_inv hc
    obtain ⟨scope, n1, stmtsAsm, Γb, n2, hh, hnd, hcs, rfl, rfl⟩ :=
      block_inv hblockA
    have hout := ihbody (scope :: Φ) F L n1 stmtsAsm Γb n' hF hL hcs
    obtain ⟨Δ, hΔ⟩ := stmts_suffix hcs
    match o, hout with
    | .normal, ⟨hΓb, hlenb, hsimb⟩ =>
      have hΓblen : Γb.length = Vb.length := by
        rw [hΓb]
        simp
      have hnames : names (YulSemantics.restore V0 Vb) = names V0 := by
        show names (Vb.drop (Vb.length - V0.length)) = _
        rw [names_drop, ← hΓb, hΔ]
        rw [show Vb.length - V0.length = Δ.length from by
          have h1 := congrArg List.length hΔ
          simp at h1
          omega]
        simp
      refine ⟨hnames.symm, ?_, fun hΦ => ?_⟩
      · show V0.length ≤ (Vb.drop (Vb.length - V0.length)).length
        simp
        omega
      · intro pre c σ hp
        have hplace : stmtsAsm <:+: prog :=
          ⟨pre, List.replicate (Γb.length - (names V0).length) .pop ++ c,
            by rw [hp]; simp⟩
        have hΦ' := hoist_ok hΦ hh hnd hcs hplace
        have hcomp : ASimS prog st0 V0
            (stmtsAsm ++ List.replicate
              (Γb.length - (names V0).length) .pop)
            stb (YulSemantics.restore V0 Vb) := by
          rw [show Γb.length - (names V0).length
              = Vb.length - V0.length from by rw [hΓblen]; simp]
          exact (hsimb hΦ').comp (asimS_restore _ Vb)
        exact hcomp pre c σ hp
    | .halt, hsimb =>
      intro hΦ pre c σ hp
      have hplace : stmtsAsm <:+: prog :=
        ⟨pre, List.replicate (Γb.length - (names V0).length) .pop ++ c,
          by rw [hp]; simp⟩
      have hΦ' := hoist_ok hΦ hh hnd hcs hplace
      exact ((hsimb hΦ').extend _) pre c σ hp
    | .break, ⟨lc, hlc, hlenb, hnmb, hsimb⟩ =>
      have hd : lc.depth ≤ V0.length := by
        rw [hlc] at hL
        exact hL
      refine ⟨lc, hlc, ?_, ?_, fun hΦ pre c cL σ hp hfind => ?_⟩
      · show V0.length ≤ (Vb.drop (Vb.length - V0.length)).length
        simp
        omega
      · show names (trim lc.depth (YulSemantics.restore V0 Vb)) = _
        rw [trim_restore hd hlenb]
        exact hnmb
      · have hplace : stmtsAsm <:+: prog :=
          ⟨pre, List.replicate (Γb.length - (names V0).length) .pop ++ c,
            by rw [hp]; simp⟩
        have hΦ' := hoist_ok hΦ hh hnd hcs hplace
        exact (((hsimb hΦ').extend _).retarget
          (trim_restore hd hlenb)) pre c cL σ hp hfind
    | .continue, ⟨lc, hlc, hlenb, hnmb, hsimb⟩ =>
      have hd : lc.depth ≤ V0.length := by
        rw [hlc] at hL
        exact hL
      refine ⟨lc, hlc, ?_, ?_, fun hΦ pre c cL σ hp hfind => ?_⟩
      · show V0.length ≤ (Vb.drop (Vb.length - V0.length)).length
        simp
        omega
      · show names (trim lc.depth (YulSemantics.restore V0 Vb)) = _
        rw [trim_restore hd hlenb]
        exact hnmb
      · have hplace : stmtsAsm <:+: prog :=
          ⟨pre, List.replicate (Γb.length - (names V0).length) .pop ++ c,
            by rw [hp]; simp⟩
        have hΦ' := hoist_ok hΦ hh hnd hcs hplace
        exact (((hsimb hΦ').extend _).retarget
          (trim_restore hd hlenb)) pre c cL σ hp hfind
    | .leave, ⟨fc, hfc, hlenb, hnmb, hsimb⟩ =>
      have hd : fc.depth ≤ V0.length := by
        rw [hfc] at hF
        exact hF
      refine ⟨fc, hfc, ?_, ?_, fun hΦ pre c cL σ hp hfind => ?_⟩
      · show V0.length ≤ (Vb.drop (Vb.length - V0.length)).length
        simp
        omega
      · show names (trim fc.depth (YulSemantics.restore V0 Vb)) = _
        rw [trim_restore hd hlenb]
        exact hnmb
      · have hplace : stmtsAsm <:+: prog :=
          ⟨pre, List.replicate (Γb.length - (names V0).length) .pop ++ c,
            by rw [hp]; simp⟩
        have hΦ' := hoist_ok hΦ hh hnd hcs hplace
        exact (((hsimb hΦ').extend _).retarget
          (trim_restore hd hlenb)) pre c cL σ hp hfind
  | letZero =>
    intro Φ F L n asm Γ' n' hF hL hc
    obtain ⟨rfl, rfl, rfl⟩ := stmt_letNone_inv hc
    refine ⟨?_, by simp, fun hΦ => asimS_letZero _⟩
    rw [names_append, names_bindZeros]
  | letVal hexp hlen ihexp =>
    intro Φ F L n asm Γ' n' hF hL hc
    obtain ⟨he, rfl⟩ := stmt_letSome_inv hc
    refine ⟨?_, ?_, fun hΦ => (ihexp Φ 0 n asm n' he hΦ).toASimSLetMany hlen.symm⟩
    · rw [names_append, names_zip _ _ hlen.symm]
    · rw [List.length_append]; omega
  | letHalt hexp ihexp =>
    intro Φ F L n asm Γ' n' hF hL hc
    obtain ⟨he, rfl⟩ := stmt_letSome_inv hc
    exact fun hΦ => (ihexp Φ 0 n asm n' he hΦ).toASimSHalt
  | assignVal hexp hlen ihexp =>
    intro Φ F L n asm Γ' n' hF hL hc
    obtain ⟨eCode, acode, he, hac, rfl, rfl⟩ := stmt_assign_inv hc
    exact ⟨(names_setMany _ _ _).symm, (length_setMany _ _ _).ge,
      fun hΦ => asimS_assigns hlen.symm hac (ihexp Φ 0 n eCode n' he hΦ)⟩
  | assignHalt hexp ihexp =>
    intro Φ F L n asm Γ' n' hF hL hc
    obtain ⟨eCode, acode, he, hac, rfl, rfl⟩ := stmt_assign_inv hc
    exact fun hΦ => ((ihexp Φ 0 n eCode n' he hΦ).toASimSHalt).extend _
  | exprStmt hexp ihexp =>
    intro Φ F L n asm Γ' n' hF hL hc
    obtain ⟨he, rfl⟩ := stmt_exprStmt_inv hc
    exact ⟨rfl, Nat.le_refl _, fun hΦ => (ihexp Φ 0 n asm n' he hΦ).toASimS⟩
  | exprStmtHalt hexp ihexp =>
    intro Φ F L n asm Γ' n' hF hL hc
    obtain ⟨he, rfl⟩ := stmt_exprStmt_inv hc
    exact fun hΦ => (ihexp Φ 0 n asm n' he hΦ).toASimSHalt
  | ifTrue hcstep hcv hblock ihc ihblock =>
    intro Φ F L n asm Γ' n' hF hL hc
    obtain ⟨cCode, n1, bodyCode, hce, hb, rfl, rfl⟩ := stmt_cond_inv hc
    have hcv' := ne_zero_of_ne_dzero hcv
    have hout := ihblock Φ F L n1 bodyCode _ n' hF hL (stmt_of_block hb)
    rename_i o
    match o, hout with
    | .normal, ⟨hΓb, hlenb, hsimb⟩ =>
      exact ⟨hΓb, hlenb, fun hΦ =>
        asimS_ifTrue (ihc Φ 0 (n + 1) cCode n1 hce hΦ) hcv' (hsimb hΦ)⟩
    | .halt, hsimb =>
      exact fun hΦ =>
        asimS_ifTrueHalt (ihc Φ 0 (n + 1) cCode n1 hce hΦ) hcv' (hsimb hΦ)
    | .break, ⟨lc, hlc, hlenb, hnmb, hsimb⟩ =>
      exact ⟨lc, hlc, hlenb, hnmb, fun hΦ =>
        asimS_ifTrueNL (ihc Φ 0 (n + 1) cCode n1 hce hΦ) hcv' (hsimb hΦ)⟩
    | .continue, ⟨lc, hlc, hlenb, hnmb, hsimb⟩ =>
      exact ⟨lc, hlc, hlenb, hnmb, fun hΦ =>
        asimS_ifTrueNL (ihc Φ 0 (n + 1) cCode n1 hce hΦ) hcv' (hsimb hΦ)⟩
    | .leave, ⟨fc, hfc, hlenb, hnmb, hsimb⟩ =>
      exact ⟨fc, hfc, hlenb, hnmb, fun hΦ =>
        asimS_ifTrueNL (ihc Φ 0 (n + 1) cCode n1 hce hΦ) hcv' (hsimb hΦ)⟩
  | ifFalse hcstep hcv ihc =>
    intro Φ F L n asm Γ' n' hF hL hc
    obtain ⟨cCode, n1, bodyCode, hce, hb, rfl, rfl⟩ := stmt_cond_inv hc
    exact ⟨rfl, Nat.le_refl _, fun hΦ =>
      asimS_ifFalse hnodup (ihc Φ 0 (n + 1) cCode n1 hce hΦ) hcv⟩
  | ifHalt hcstep ihc =>
    intro Φ F L n asm Γ' n' hF hL hc
    obtain ⟨cCode, n1, bodyCode, hce, hb, rfl, rfl⟩ := stmt_cond_inv hc
    exact fun hΦ =>
      asimS_ifCondHalt (ihc Φ 0 (n + 1) cCode n1 hce hΦ)
  | switchExec hcstep hblock ihc ihblock =>
    intro Φ F L n asm Γ' n' hF hL hc
    obtain ⟨cCode, n1, casesAsm, n2, defAsm, hce, hcs, hdef, rfl, rfl⟩ := stmt_switch_inv hc
    obtain ⟨m0, bAsm0, m0', hbc0⟩ := selectSwitch_compiled hdef _ hcs
    have hout0 := ihblock Φ F L m0 bAsm0 _ m0' hF hL (stmt_of_block hbc0)
    rename_i o
    match o, hout0 with
    | .normal, ⟨hΓ, hlen, _⟩ =>
      refine ⟨hΓ, hlen, fun hΦ => ?_⟩
      have hd := asimS_switchTailNormal hnodup "" hdef _ hcs
        (fun m bAsm m' hbc =>
          ((ihblock Φ F L m bAsm _ m' hF hL (stmt_of_block hbc)).2.2 hΦ))
      simpa using ((ihc Φ 0 (n + 1) cCode n1 hce hΦ).toASimSLet (x := "")).comp hd
    | .halt, _ =>
      refine fun hΦ => ?_
      have hd := asimS_switchTailHalt hnodup "" hdef _ hcs
        (fun m bAsm m' hbc =>
          ((ihblock Φ F L m bAsm _ m' hF hL (stmt_of_block hbc)) hΦ))
      simpa using ((ihc Φ 0 (n + 1) cCode n1 hce hΦ).toASimSLet (x := "")).compHalt hd
    | .break, ⟨lc, hlc, hlen, hnm, _⟩ =>
      refine ⟨lc, hlc, hlen, hnm, fun hΦ => ?_⟩
      have hd := asimS_switchTailNL (l := lc.brk) (depth := lc.depth) hnodup "" hdef _ hcs
        (fun m bAsm m' hbc => by
          obtain ⟨lc', hlc', _, _, hsim'⟩ := ihblock Φ F L m bAsm _ m' hF hL (stmt_of_block hbc)
          obtain rfl : lc = lc' := Option.some.inj (hlc.symm.trans hlc')
          exact hsim' hΦ)
      simpa using ((ihc Φ 0 (n + 1) cCode n1 hce hΦ).toASimSLet (x := "")).compNL hd
    | .continue, ⟨lc, hlc, hlen, hnm, _⟩ =>
      refine ⟨lc, hlc, hlen, hnm, fun hΦ => ?_⟩
      have hd := asimS_switchTailNL (l := lc.cont) (depth := lc.depth) hnodup "" hdef _ hcs
        (fun m bAsm m' hbc => by
          obtain ⟨lc', hlc', _, _, hsim'⟩ := ihblock Φ F L m bAsm _ m' hF hL (stmt_of_block hbc)
          obtain rfl : lc = lc' := Option.some.inj (hlc.symm.trans hlc')
          exact hsim' hΦ)
      simpa using ((ihc Φ 0 (n + 1) cCode n1 hce hΦ).toASimSLet (x := "")).compNL hd
    | .leave, ⟨fc, hfc, hlen, hnm, _⟩ =>
      refine ⟨fc, hfc, hlen, hnm, fun hΦ => ?_⟩
      have hd := asimS_switchTailNL (l := fc.exit) (depth := fc.depth) hnodup "" hdef _ hcs
        (fun m bAsm m' hbc => by
          obtain ⟨fc', hfc', _, _, hsim'⟩ := ihblock Φ F L m bAsm _ m' hF hL (stmt_of_block hbc)
          obtain rfl : fc = fc' := Option.some.inj (hfc.symm.trans hfc')
          exact hsim' hΦ)
      simpa using ((ihc Φ 0 (n + 1) cCode n1 hce hΦ).toASimSLet (x := "")).compNL hd
  | switchHalt hcstep ihc =>
    intro Φ F L n asm Γ' n' hF hL hc
    obtain ⟨cCode, n1, casesAsm, n2, defAsm, hce, hcs, hdef, rfl, rfl⟩ := stmt_switch_inv hc
    refine fun hΦ => ?_
    have h := ((ihc Φ 0 (n + 1) cCode n1 hce hΦ).toASimSHalt).extend
        (casesAsm ++ .pop :: defAsm ++ [.label n])
    have he : cCode ++ (casesAsm ++ .pop :: defAsm ++ [.label n])
        = cCode ++ casesAsm ++ .pop :: defAsm ++ [.label n] := by
      simp [List.append_assoc]
    rwa [he] at h
  | forLoop hinit hloop ihinit ihloop =>
    rename_i funs0 V0 st0 init0 ce post0 body0 Vinit stinit Vend stend o
    intro Φ F L n asm Γ' n' hF hL hc
    obtain ⟨scope, n0, initCode, Γi, n1, cCode, n2, bodyCode, n3, postCode,
      hh, hnd, hinitC, hce, hbA, hpA, rfl, rfl⟩ := stmt_forLoop_inv hc
    obtain ⟨hΓi, hlenI, hsimI⟩ := ihinit (scope :: Φ) F L (n0 + 3) initCode
      Γi n1 hF hL hinitC
    obtain ⟨Δi, hΔi⟩ := stmts_suffix hinitC
    have hnVinit : names Vinit = Δi ++ names V0 := by rw [← hΓi, hΔi]
    have hlVinit : Vinit.length = Δi.length + V0.length := by
      have := congrArg List.length hnVinit
      simpa using this
    have hlΓi : Γi.length = Vinit.length := by
      rw [hΓi]
      simp
    have hloopOut := ihloop (scope :: Φ) F n0 (n0 + 1) (n0 + 2) cCode
      bodyCode postCode n1 n2 n3 n' (hF.mono hlenI)
      (by rw [← hΓi]; exact hce)
      (by rw [← hΓi, show Vinit.length = Γi.length from hlΓi.symm]; exact hbA)
      (by rw [← hΓi]; exact hpA)
    -- the executable prefix (init, then the condition label), and the
    -- placement facts, all under a given placement of the fragment
    rcases loop_outcome hloop with rfl | rfl | rfl
    · -- normal
      obtain ⟨hnEnd, hsimEnd⟩ := hloopOut
      have hnVend : names Vend = names Vinit := hnEnd
      have hlVend : Vend.length = Vinit.length := by
        have := congrArg List.length hnVend
        simpa using this
      have hnames : names (YulSemantics.restore V0 Vend) = names V0 := by
        show names (Vend.drop (Vend.length - V0.length)) = _
        rw [names_drop, hnVend, hnVinit]
        rw [show Vend.length - V0.length = Δi.length from by omega]
        simp
      refine ⟨hnames.symm, ?_, fun hΦ => ?_⟩
      · show V0.length ≤ (Vend.drop (Vend.length - V0.length)).length
        simp
        omega
      · intro pre c σ hp
        have hΦ' : FEnvOK prog (YulSemantics.hoist yulD init0 :: funs0)
            (scope :: Φ) :=
          hoist_ok hΦ hh hnd hinitC
            ⟨pre, .label n0 :: cCode ++ [.op .iszero, .jumpi (n0 + 2)]
              ++ bodyCode ++ .label (n0 + 1) :: postCode ++ .jump n0
              :: .label (n0 + 2)
              :: List.replicate (Γi.length - (names V0).length) .pop ++ c,
              by rw [hp]; simp⟩
        have h1 := (hsimI hΦ') pre
          (.label n0 :: loopIter n0 (n0 + 1) (n0 + 2) cCode bodyCode postCode
            (List.replicate (Γi.length - (names V0).length) .pop ++ c))
          σ (by rw [hp]; simp)
        have hcond : findLabel n0 prog
            = some (loopIter n0 (n0 + 1) (n0 + 2) cCode bodyCode postCode
              (List.replicate (Γi.length - (names V0).length) .pop ++ c)) := by
          have hsplit : prog = (pre ++ initCode) ++ .label n0
              :: loopIter n0 (n0 + 1) (n0 + 2) cCode bodyCode postCode
                (List.replicate (Γi.length - (names V0).length) .pop ++ c) := by
            rw [hp]
            simp
          rw [hsplit]
          exact findLabel_boundary (by rw [← hsplit]; exact hnodup)
        have h2 := hsimEnd _ hcond hΦ' σ
        have h3 : ASimS prog stend Vend
            (List.replicate (Γi.length - (names V0).length) .pop)
            stend (YulSemantics.restore V0 Vend) := by
          rw [show Γi.length - (names V0).length = Vend.length - V0.length
            from by simp [hlΓi]; omega]
          exact asimS_restore V0 Vend
        have h4 := h3 (pre ++ initCode ++ .label n0
            :: cCode ++ [.op .iszero, .jumpi (n0 + 2)] ++ bodyCode
            ++ .label (n0 + 1) :: postCode ++ [.jump n0, .label (n0 + 2)])
          c σ (by rw [hp]; simp)
        have hfinal : ASteps prog
            ⟨initCode ++ (.label n0 :: loopIter n0 (n0 + 1) (n0 + 2) cCode
                bodyCode postCode
                (List.replicate (Γi.length - (names V0).length) .pop ++ c)),
              wimg V0 ++ σ, st0⟩
            ⟨c, wimg (YulSemantics.restore V0 Vend) ++ σ, stend⟩ := by
          have hlbl : ASteps prog
              ⟨.label n0 :: loopIter n0 (n0 + 1) (n0 + 2) cCode bodyCode
                  postCode
                  (List.replicate (Γi.length - (names V0).length) .pop ++ c),
                wimg Vinit ++ σ, stinit⟩
              ⟨loopIter n0 (n0 + 1) (n0 + 2) cCode bodyCode postCode
                  (List.replicate (Γi.length - (names V0).length) .pop ++ c),
                wimg Vinit ++ σ, stinit⟩ := .single .label
          refine ((h1.trans hlbl).trans h2).trans ?_
          simpa using h4
        have hshape : initCode
            ++ .label n0 :: cCode ++ [.op .iszero, .jumpi (n0 + 2)]
            ++ bodyCode ++ .label (n0 + 1) :: postCode ++ .jump n0
            :: .label (n0 + 2)
            :: List.replicate (Γi.length - (names V0).length) .pop ++ c
            = initCode ++ (.label n0 :: loopIter n0 (n0 + 1) (n0 + 2) cCode
              bodyCode postCode
              (List.replicate (Γi.length - (names V0).length) .pop ++ c)) := by
          simp
        rw [hshape]
        exact hfinal
    · -- halt
      have hsimEnd := hloopOut
      intro hΦ pre c σ hp
      have hΦ' : FEnvOK prog (YulSemantics.hoist yulD init0 :: funs0)
          (scope :: Φ) :=
        hoist_ok hΦ hh hnd hinitC
            ⟨pre, .label n0 :: cCode ++ [.op .iszero, .jumpi (n0 + 2)]
              ++ bodyCode ++ .label (n0 + 1) :: postCode ++ .jump n0
              :: .label (n0 + 2)
              :: List.replicate (Γi.length - (names V0).length) .pop ++ c,
              by rw [hp]; simp⟩
      have h1 := (hsimI hΦ') pre
        (.label n0 :: loopIter n0 (n0 + 1) (n0 + 2) cCode bodyCode postCode
          (List.replicate (Γi.length - (names V0).length) .pop ++ c))
        σ (by rw [hp]; simp)
      have hcond : findLabel n0 prog
          = some (loopIter n0 (n0 + 1) (n0 + 2) cCode bodyCode postCode
            (List.replicate (Γi.length - (names V0).length) .pop ++ c)) := by
        have hsplit : prog = (pre ++ initCode) ++ .label n0
            :: loopIter n0 (n0 + 1) (n0 + 2) cCode bodyCode postCode
              (List.replicate (Γi.length - (names V0).length) .pop ++ c) := by
          rw [hp]
          simp
        rw [hsplit]
        exact findLabel_boundary (by rw [← hsplit]; exact hnodup)
      obtain ⟨conf, hsteps, hhalt⟩ := hsimEnd _ hcond hΦ' σ
      refine ⟨conf, ?_, hhalt⟩
      have hshape : initCode
          ++ .label n0 :: cCode ++ [.op .iszero, .jumpi (n0 + 2)]
          ++ bodyCode ++ .label (n0 + 1) :: postCode ++ .jump n0
          :: .label (n0 + 2)
          :: List.replicate (Γi.length - (names V0).length) .pop ++ c
          = initCode ++ (.label n0 :: loopIter n0 (n0 + 1) (n0 + 2) cCode
            bodyCode postCode
            (List.replicate (Γi.length - (names V0).length) .pop ++ c)) := by
        simp
      rw [hshape]
      exact (h1.trans (.head .label (.refl _))).trans hsteps
    · -- leave
      obtain ⟨fc, hfc, hlenL, hnmL, hsimL⟩ := hloopOut
      have hd : fc.depth ≤ V0.length := by
        rw [hfc] at hF
        exact hF
      have hVle : V0.length ≤ Vend.length := by omega
      refine ⟨fc, hfc, ?_, ?_, fun hΦ pre c cL σ hp hfindEx => ?_⟩
      · show V0.length ≤ (Vend.drop (Vend.length - V0.length)).length
        simp
        omega
      · show names (trim fc.depth (YulSemantics.restore V0 Vend)) = _
        rw [trim_restore hd hVle, hnmL, hnVinit, hlVinit]
        rw [show Δi.length + V0.length - fc.depth
            = Δi.length + (V0.length - fc.depth) from by omega,
          drop_append_plus]
      · have hΦ' : FEnvOK prog (YulSemantics.hoist yulD init0 :: funs0)
            (scope :: Φ) :=
          hoist_ok hΦ hh hnd hinitC
            ⟨pre, .label n0 :: cCode ++ [.op .iszero, .jumpi (n0 + 2)]
              ++ bodyCode ++ .label (n0 + 1) :: postCode ++ .jump n0
              :: .label (n0 + 2)
              :: List.replicate (Γi.length - (names V0).length) .pop ++ c,
              by rw [hp]; simp⟩
        have h1 := (hsimI hΦ') pre
          (.label n0 :: loopIter n0 (n0 + 1) (n0 + 2) cCode bodyCode postCode
            (List.replicate (Γi.length - (names V0).length) .pop ++ c))
          σ (by rw [hp]; simp)
        have hcond : findLabel n0 prog
            = some (loopIter n0 (n0 + 1) (n0 + 2) cCode bodyCode postCode
              (List.replicate (Γi.length - (names V0).length) .pop ++ c)) := by
          have hsplit : prog = (pre ++ initCode) ++ .label n0
              :: loopIter n0 (n0 + 1) (n0 + 2) cCode bodyCode postCode
                (List.replicate (Γi.length - (names V0).length) .pop ++ c) := by
            rw [hp]
            simp
          rw [hsplit]
          exact findLabel_boundary (by rw [← hsplit]; exact hnodup)
        have h2 := hsimL _ hcond hΦ' σ cL hfindEx
        have hshape : initCode
            ++ .label n0 :: cCode ++ [.op .iszero, .jumpi (n0 + 2)]
            ++ bodyCode ++ .label (n0 + 1) :: postCode ++ .jump n0
            :: .label (n0 + 2)
            :: List.replicate (Γi.length - (names V0).length) .pop ++ c
            = initCode ++ (.label n0 :: loopIter n0 (n0 + 1) (n0 + 2) cCode
              bodyCode postCode
              (List.replicate (Γi.length - (names V0).length) .pop ++ c)) := by
          simp
        rw [hshape, show trim fc.depth (YulSemantics.restore V0 Vend)
            = trim fc.depth Vend from trim_restore hd hVle]
        exact (h1.trans (.head .label (.refl _))).trans h2
  | forInitHalt hinit ihinit =>
    rename_i funs0 V0 st0 init0 ce post0 body0 Vinit stinit
    intro Φ F L n asm Γ' n' hF hL hc
    obtain ⟨scope, n0, initCode, Γi, n1, cCode, n2, bodyCode, n3, postCode,
      hh, hnd, hinitC, hce, hbA, hpA, rfl, rfl⟩ := stmt_forLoop_inv hc
    have hsimI := ihinit (scope :: Φ) F L (n0 + 3) initCode Γi n1 hF hL hinitC
    intro hΦ pre c σ hp
    have hΦ' : FEnvOK prog (YulSemantics.hoist yulD init0 :: funs0)
        (scope :: Φ) :=
      hoist_ok hΦ hh hnd hinitC
            ⟨pre, .label n0 :: cCode ++ [.op .iszero, .jumpi (n0 + 2)]
              ++ bodyCode ++ .label (n0 + 1) :: postCode ++ .jump n0
              :: .label (n0 + 2)
              :: List.replicate (Γi.length - (names V0).length) .pop ++ c,
              by rw [hp]; simp⟩
    obtain ⟨conf, hsteps, hhalt⟩ := (hsimI hΦ') pre
      (.label n0 :: loopIter n0 (n0 + 1) (n0 + 2) cCode bodyCode postCode
        (List.replicate (Γi.length - (names V0).length) .pop ++ c))
      σ (by rw [hp]; simp)
    refine ⟨conf, ?_, hhalt⟩
    have hshape : initCode
        ++ .label n0 :: cCode ++ [.op .iszero, .jumpi (n0 + 2)]
        ++ bodyCode ++ .label (n0 + 1) :: postCode ++ .jump n0
        :: .label (n0 + 2)
        :: List.replicate (Γi.length - (names V0).length) .pop ++ c
        = initCode ++ (.label n0 :: loopIter n0 (n0 + 1) (n0 + 2) cCode
          bodyCode postCode
          (List.replicate (Γi.length - (names V0).length) .pop ++ c)) := by
      simp
    rw [hshape]
    exact hsteps
  | «break» =>
    intro Φ F L n asm Γ' n' hF hL hc
    obtain ⟨lc, rfl, rfl, rfl, rfl⟩ := stmt_break_inv hc
    refine ⟨lc, rfl, Nat.le_refl _, names_trim_self _ _, fun hΦ => ?_⟩
    have := asimNL_exit (prog := prog) (yst := ‹EvmState›)
      (V := ‹VEnv yulD›) lc.brk lc.depth
    simpa using this
  | «continue» =>
    intro Φ F L n asm Γ' n' hF hL hc
    obtain ⟨lc, rfl, rfl, rfl, rfl⟩ := stmt_continue_inv hc
    refine ⟨lc, rfl, Nat.le_refl _, names_trim_self _ _, fun hΦ => ?_⟩
    have := asimNL_exit (prog := prog) (yst := ‹EvmState›)
      (V := ‹VEnv yulD›) lc.cont lc.depth
    simpa using this
  | leave =>
    intro Φ F L n asm Γ' n' hF hL hc
    obtain ⟨fc, rfl, rfl, rfl, rfl⟩ := stmt_leave_inv hc
    refine ⟨fc, rfl, Nat.le_refl _, names_trim_self _ _, fun hΦ => ?_⟩
    have := asimNL_exit (prog := prog) (yst := ‹EvmState›)
      (V := ‹VEnv yulD›) fc.exit fc.depth
    simpa using this
  | seqNil =>
    intro Φ F L n asm Γ' n' hF hL hc
    obtain ⟨rfl, rfl, rfl⟩ := stmts_nil_inv hc
    exact ⟨rfl, Nat.le_refl _, fun _ => ASimS.nil⟩
  | seqCons hs hrest ihs ihrest =>
    rename_i V0 st0 s0 rest0 V1 st1 V2 st2 o
    intro Φ F L n asm Γ' n' hF hL hc
    obtain ⟨is1, Γ1, n1, is2, h1, h2, rfl⟩ := stmts_cons_inv hc
    obtain ⟨hΓ1, hlen1, hsim1⟩ := ihs Φ F L n is1 Γ1 n1 hF hL h1
    obtain ⟨Δ, hΔ⟩ := stmt_suffix h1
    have hnV1 : names V1 = Δ ++ names V0 := by rw [← hΓ1, hΔ]
    have hlV1 : V1.length = Δ.length + V0.length := by
      have := congrArg List.length hnV1
      simpa using this
    rw [hΓ1] at h2
    have hnmProp : ∀ (d : Nat) (W : VEnv yulD), d ≤ V0.length →
        names (trim d W) = (names V1).drop (V1.length - d) →
        names (trim d W) = (names V0).drop (V0.length - d) := by
      intro d W hd hW
      rw [hW, hnV1,
        show V1.length - d = Δ.length + (V0.length - d) from by omega,
        drop_append_plus]
    match o with
    | .normal =>
      obtain ⟨hΓ2, hlen2, hsim2⟩ := ihrest Φ F L n1 is2 Γ' n'
        (hF.mono hlen1) (hL.mono hlen1) h2
      exact ⟨hΓ2, Nat.le_trans hlen1 hlen2,
        fun hΦ => (hsim1 hΦ).comp (hsim2 hΦ)⟩
    | .halt =>
      have hsim2 := ihrest Φ F L n1 is2 Γ' n'
        (hF.mono hlen1) (hL.mono hlen1) h2
      exact fun hΦ => (hsim1 hΦ).compHalt (hsim2 hΦ)
    | .break =>
      obtain ⟨lc, hlc, hlen2, hnm2, hsim2⟩ := ihrest Φ F L n1 is2 Γ' n'
        (hF.mono hlen1) (hL.mono hlen1) h2
      exact ⟨lc, hlc, Nat.le_trans hlen1 hlen2,
        hnmProp lc.depth V2 (by rw [hlc] at hL; exact hL) hnm2,
        fun hΦ => (hsim1 hΦ).compNL (hsim2 hΦ)⟩
    | .continue =>
      obtain ⟨lc, hlc, hlen2, hnm2, hsim2⟩ := ihrest Φ F L n1 is2 Γ' n'
        (hF.mono hlen1) (hL.mono hlen1) h2
      exact ⟨lc, hlc, Nat.le_trans hlen1 hlen2,
        hnmProp lc.depth V2 (by rw [hlc] at hL; exact hL) hnm2,
        fun hΦ => (hsim1 hΦ).compNL (hsim2 hΦ)⟩
    | .leave =>
      obtain ⟨fc, hfc, hlen2, hnm2, hsim2⟩ := ihrest Φ F L n1 is2 Γ' n'
        (hF.mono hlen1) (hL.mono hlen1) h2
      exact ⟨fc, hfc, Nat.le_trans hlen1 hlen2,
        hnmProp fc.depth V2 (by rw [hfc] at hF; exact hF) hnm2,
        fun hΦ => (hsim1 hΦ).compNL (hsim2 hΦ)⟩
  | seqStop hs hne ihs =>
    intro Φ F L n asm Γ' n' hF hL hc
    obtain ⟨is1, Γ1, n1, is2, h1, h2, rfl⟩ := stmts_cons_inv hc
    have hout := ihs Φ F L n is1 Γ1 n1 hF hL h1
    rename_i o
    match o, hout with
    | .normal, _ => exact absurd rfl hne
    | .halt, hout => exact fun hΦ => (hout hΦ).extend is2
    | .break, ⟨lc, hlc, hlen, hnm, hsim⟩ =>
      exact ⟨lc, hlc, hlen, hnm, fun hΦ => (hsim hΦ).extend is2⟩
    | .continue, ⟨lc, hlc, hlen, hnm, hsim⟩ =>
      exact ⟨lc, hlc, hlen, hnm, fun hΦ => (hsim hΦ).extend is2⟩
    | .leave, ⟨fc, hfc, hlen, hnm, hsim⟩ =>
      exact ⟨fc, hfc, hlen, hnm, fun hΦ => (hsim hΦ).extend is2⟩
  | loopDone hc hcv ihc =>
    rename_i funs0 V0 st0 ce post0 body0 cv st1
    intro Φ F lcond lpost lexit cCode bodyAsm postAsm n₁ n₂ n₃ n₄
      hF hce hbA hpA
    refine ⟨rfl, fun cRest hcond hΦ σ => ?_⟩
    obtain ⟨preI, hpreI⟩ := findLabel_suffix hcond
    have hfindExit : findLabel lexit prog = some cRest := by
      have hsplit : prog = (preI ++ cCode ++ [.op .iszero, .jumpi lexit]
          ++ bodyAsm ++ .label lpost :: postAsm ++ [.jump lcond])
          ++ .label lexit :: cRest := by
        rw [← hpreI]
        simp
      rw [hsplit]
      exact findLabel_boundary (by rw [← hsplit]; exact hnodup)
    have hcv0 : cv = (0 : U256) := hcv
    have hone : YulSemantics.EVM.b2w (cv = 0) ≠ 0 := by
      unfold YulSemantics.EVM.b2w
      rw [if_pos (decide_eq_true hcv0)]
      decide
    have h1 : ASteps prog
        ⟨(cCode ++ [.op .iszero]) ++ (.jumpi lexit :: (bodyAsm
            ++ .label lpost :: postAsm ++ .jump lcond :: .label lexit :: cRest)),
          wimg V0 ++ σ, st0⟩
        ⟨.jumpi lexit :: (bodyAsm ++ .label lpost :: postAsm
            ++ .jump lcond :: .label lexit :: cRest),
          .word (YulSemantics.EVM.b2w (cv = 0)) :: (wimg V0 ++ σ), st1⟩ :=
      (asimE_condPrologue (ihc Φ 0 n₁ cCode n₂ hce hΦ)) preI
        (.jumpi lexit :: (bodyAsm ++ .label lpost :: postAsm
          ++ .jump lcond :: .label lexit :: cRest)) [] σ
        (by rw [← hpreI]; simp) rfl
    have h2 : AStep prog
        ⟨.jumpi lexit :: (bodyAsm ++ .label lpost :: postAsm
            ++ .jump lcond :: .label lexit :: cRest),
          .word (YulSemantics.EVM.b2w (cv = 0)) :: (wimg V0 ++ σ), st1⟩
        ⟨cRest, wimg V0 ++ σ, st1⟩ := .jumpiTaken hone hfindExit
    have hshape : loopIter lcond lpost lexit cCode bodyAsm postAsm cRest
        = (cCode ++ [Asm.op .iszero]) ++ (.jumpi lexit :: (bodyAsm
            ++ .label lpost :: postAsm ++ .jump lcond
            :: .label lexit :: cRest)) := by
      simp
    rw [hshape]
    exact h1.snoc h2
  | loopCondHalt hc ihc =>
    rename_i funs0 V0 st0 ce post0 body0 st1
    intro Φ F lcond lpost lexit cCode bodyAsm postAsm n₁ n₂ n₃ n₄
      hF hce hbA hpA cRest hcond hΦ σ
    obtain ⟨preI, hpreI⟩ := findLabel_suffix hcond
    obtain ⟨conf, hsteps, hhalt⟩ := (ihc Φ 0 n₁ cCode n₂ hce hΦ) preI
      ([.op .iszero, .jumpi lexit] ++ bodyAsm ++ .label lpost :: postAsm
        ++ .jump lcond :: .label lexit :: cRest) [] σ
      (by rw [← hpreI]; simp) rfl
    refine ⟨conf, ?_, hhalt⟩
    have hshape : loopIter lcond lpost lexit cCode bodyAsm postAsm cRest
        = cCode ++ ([Asm.op .iszero, Asm.jumpi lexit] ++ bodyAsm
            ++ .label lpost :: postAsm ++ .jump lcond
            :: .label lexit :: cRest) := by
      simp
    rw [hshape]
    simpa using hsteps
  | loopStep hc hcv hbody hob hpost hrest ihc ihbody ihpost ihrest =>
    rename_i funs0 V0 st0 ce post0 body0 cv st1 Vb stb ob Vp stp Vend stend o
    intro Φ F lcond lpost lexit cCode bodyAsm postAsm n₁ n₂ n₃ n₄
      hF hce hbA hpA
    have hVble : Vb.length ≤ V0.length := by
      cases hbody with
      | block hin =>
        show (YulSemantics.restore V0 _).length ≤ _
        unfold YulSemantics.restore
        simp
        omega
    have hout := ihbody Φ F (some ⟨lexit, lpost, V0.length⟩) n₂ bodyAsm
      (names V0) n₃ hF (Nat.le_refl _) (stmt_of_block hbA)
    -- layout: the body ends with the loop-scope names
    have hnVb : names Vb = names V0 := by
      rcases hob with rfl | rfl
      · exact hout.1.symm
      · obtain ⟨lc, hlc, hlenB, hnmB, hsimB⟩ := hout
        obtain rfl : (⟨lexit, lpost, V0.length⟩ : LoopCtx) = lc := by
          injection hlc
        have htrim : trim V0.length Vb = Vb := by
          unfold trim
          rw [show Vb.length - V0.length = 0 from by omega]
          exact List.drop_zero
        rw [htrim] at hnmB
        rw [show V0.length - V0.length = 0 from by omega,
          List.drop_zero] at hnmB
        exact hnmB
    have hlVb : Vb.length = V0.length := by
      have := congrArg List.length hnVb
      simpa using this
    have hpA' : compileStmt Φ (names Vb) F none n₃ (.block post0)
        = some (postAsm, names Vb, n₄) := by
      rw [hnVb]
      exact stmt_of_block hpA
    obtain ⟨hΓp, hlenp, hsimp'⟩ := ihpost Φ F none n₃ postAsm (names Vb) n₄
      (hF.mono (Nat.le_of_eq hlVb.symm)) trivial hpA'
    have hnVp : names Vp = names V0 := by rw [← hΓp, hnVb]
    have hlVp : Vp.length = V0.length := by
      have := congrArg List.length hnVp
      simpa using this
    have hrest' := ihrest Φ F lcond lpost lexit cCode bodyAsm postAsm
      n₁ n₂ n₃ n₄ (hF.mono (Nat.le_of_eq hlVp.symm))
      (by rw [hnVp]; exact hce)
      (by rw [hnVp, show Vp.length = V0.length from hlVp]; exact hbA)
      (by rw [hnVp]; exact hpA)
    -- the executable prefix: one full iteration, parameterized by placement
    have hprefix : ∀ cRest, findLabel lcond prog
          = some (loopIter lcond lpost lexit cCode bodyAsm postAsm cRest) →
        FEnvOK prog funs0 Φ → ∀ σ : List AVal,
        ASteps prog
          ⟨loopIter lcond lpost lexit cCode bodyAsm postAsm cRest,
            wimg V0 ++ σ, st0⟩
          ⟨loopIter lcond lpost lexit cCode bodyAsm postAsm cRest,
            wimg Vp ++ σ, stp⟩ := by
      intro cRest hcond hΦ σ
      obtain ⟨preI, hpreI⟩ := findLabel_suffix hcond
      have hfindPost : findLabel lpost prog
          = some (postAsm ++ .jump lcond :: .label lexit :: cRest) := by
        have hsplit : prog = (preI ++ cCode ++ [.op .iszero, .jumpi lexit]
            ++ bodyAsm) ++ .label lpost
            :: (postAsm ++ .jump lcond :: .label lexit :: cRest) := by
          rw [← hpreI]
          simp
        rw [hsplit]
        exact findLabel_boundary (by rw [← hsplit]; exact hnodup)
      have hsimBody : ASteps prog
          ⟨bodyAsm ++ (.label lpost :: postAsm
              ++ .jump lcond :: .label lexit :: cRest),
            wimg V0 ++ σ, st1⟩
          ⟨postAsm ++ .jump lcond :: .label lexit :: cRest,
            wimg Vb ++ σ, stb⟩ := by
        rcases hob with rfl | rfl
        · obtain ⟨hΓb, hlenb, hsimb⟩ := hout
          have h := (hsimb hΦ) (preI ++ cCode ++ [.op .iszero, .jumpi lexit])
            (.label lpost :: postAsm ++ .jump lcond :: .label lexit :: cRest)
            σ (by rw [← hpreI]; simp)
          refine h.snoc ?_
          exact .label
        · obtain ⟨lc, hlc, hlenB, hnmB, hsimB⟩ := hout
          obtain rfl : (⟨lexit, lpost, V0.length⟩ : LoopCtx) = lc := by
            injection hlc
          have htrim : trim V0.length Vb = Vb := by
            unfold trim
            rw [show Vb.length - V0.length = 0 from by omega]
            exact List.drop_zero
          have h := (hsimB hΦ) (preI ++ cCode ++ [.op .iszero, .jumpi lexit])
            (.label lpost :: postAsm ++ .jump lcond :: .label lexit :: cRest)
            (postAsm ++ .jump lcond :: .label lexit :: cRest)
            σ (by rw [← hpreI]; simp) hfindPost
          rw [htrim] at h
          exact h
      have hcv0 : cv ≠ (0 : U256) := hcv
      have hzero : YulSemantics.EVM.b2w (cv = 0) = 0 := by
        unfold YulSemantics.EVM.b2w
        rw [if_neg (by simp only [decide_eq_true_eq]; exact fun h => hcv0 h)]
      have h1 : ASteps prog
          ⟨(cCode ++ [.op .iszero]) ++ (.jumpi lexit :: (bodyAsm
              ++ .label lpost :: postAsm ++ .jump lcond
              :: .label lexit :: cRest)),
            wimg V0 ++ σ, st0⟩
          ⟨.jumpi lexit :: (bodyAsm ++ .label lpost :: postAsm
              ++ .jump lcond :: .label lexit :: cRest),
            .word (YulSemantics.EVM.b2w (cv = 0)) :: (wimg V0 ++ σ), st1⟩ :=
        (asimE_condPrologue (ihc Φ 0 n₁ cCode n₂ hce hΦ)) preI
          (.jumpi lexit :: (bodyAsm ++ .label lpost :: postAsm
            ++ .jump lcond :: .label lexit :: cRest)) [] σ
          (by rw [← hpreI]; simp) rfl
      have h2 : AStep prog
          ⟨.jumpi lexit :: (bodyAsm ++ .label lpost :: postAsm
              ++ .jump lcond :: .label lexit :: cRest),
            .word (YulSemantics.EVM.b2w (cv = 0)) :: (wimg V0 ++ σ), st1⟩
          ⟨bodyAsm ++ (.label lpost :: postAsm
              ++ .jump lcond :: .label lexit :: cRest),
            wimg V0 ++ σ, st1⟩ := by
        have := AStep.jumpiFall (prog := prog) (l := lexit)
          (v := YulSemantics.EVM.b2w (cv = 0))
          (c := bodyAsm ++ .label lpost :: postAsm
            ++ .jump lcond :: .label lexit :: cRest)
          (σ := wimg V0 ++ σ) (yst := st1) hzero
        simpa using this
      have h4 := (hsimp' hΦ) (preI ++ cCode ++ [.op .iszero, .jumpi lexit]
          ++ bodyAsm ++ [.label lpost])
        (.jump lcond :: .label lexit :: cRest) σ (by rw [← hpreI]; simp)
      have h5 : AStep prog
          ⟨.jump lcond :: .label lexit :: cRest, wimg Vp ++ σ, stp⟩
          ⟨loopIter lcond lpost lexit cCode bodyAsm postAsm cRest,
            wimg Vp ++ σ, stp⟩ := .jump hcond
      have hshape : loopIter lcond lpost lexit cCode bodyAsm postAsm cRest
          = (cCode ++ [Asm.op .iszero]) ++ (.jumpi lexit :: (bodyAsm
              ++ .label lpost :: postAsm ++ .jump lcond
              :: .label lexit :: cRest)) := by
        simp
      rw [hshape]
      refine ((h1.snoc h2).trans hsimBody).trans ?_
      rw [← hshape]
      exact h4.snoc h5
    match o, hrest' with
    | .normal, ⟨hnEnd, hsimEnd⟩ =>
      refine ⟨by rw [hnEnd, hnVp], fun cRest hcond hΦ σ => ?_⟩
      exact (hprefix cRest hcond hΦ σ).trans (hsimEnd cRest hcond hΦ σ)
    | .halt, hsimEnd =>
      intro cRest hcond hΦ σ
      obtain ⟨conf, hsteps, hhalt⟩ := hsimEnd cRest hcond hΦ σ
      exact ⟨conf, (hprefix cRest hcond hΦ σ).trans hsteps, hhalt⟩
    | .leave, ⟨fc, hfc, hlenEnd, hnmEnd, hsimEnd⟩ =>
      refine ⟨fc, hfc, by omega, ?_, fun cRest hcond hΦ σ cL hfindEx => ?_⟩
      · rw [hnmEnd, hnVp, hlVp]
      · exact (hprefix cRest hcond hΦ σ).trans
          (hsimEnd cRest hcond hΦ σ cL hfindEx)
    | .break, _ => trivial
    | .continue, _ => trivial
  | loopPostHalt hc hcv hbody hob hpost ihc ihbody ihpost =>
    rename_i funs0 V0 st0 ce post0 body0 cv st1 Vb stb ob Vp stp
    intro Φ F lcond lpost lexit cCode bodyAsm postAsm n₁ n₂ n₃ n₄
      hF hce hbA hpA
    have hVble : Vb.length ≤ V0.length := by
      cases hbody with
      | block hin =>
        show (YulSemantics.restore V0 _).length ≤ _
        unfold YulSemantics.restore
        simp
        omega
    have hout := ihbody Φ F (some ⟨lexit, lpost, V0.length⟩) n₂ bodyAsm
      (names V0) n₃ hF (Nat.le_refl _) (stmt_of_block hbA)
    have hnVb : names Vb = names V0 := by
      rcases hob with rfl | rfl
      · exact hout.1.symm
      · obtain ⟨lc, hlc, hlenB, hnmB, hsimB⟩ := hout
        obtain rfl : (⟨lexit, lpost, V0.length⟩ : LoopCtx) = lc := by
          injection hlc
        have htrim : trim V0.length Vb = Vb := by
          unfold trim
          rw [show Vb.length - V0.length = 0 from by omega]
          exact List.drop_zero
        rw [htrim] at hnmB
        rw [show V0.length - V0.length = 0 from by omega,
          List.drop_zero] at hnmB
        exact hnmB
    have hlVb : Vb.length = V0.length := by
      have := congrArg List.length hnVb
      simpa using this
    have hpA' : compileStmt Φ (names Vb) F none n₃ (.block post0)
        = some (postAsm, names Vb, n₄) := by
      rw [hnVb]
      exact stmt_of_block hpA
    have hsimp' := ihpost Φ F none n₃ postAsm (names Vb) n₄
      (hF.mono (Nat.le_of_eq hlVb.symm)) trivial hpA'
    intro cRest hcond hΦ σ
    obtain ⟨preI, hpreI⟩ := findLabel_suffix hcond
    have hfindPost : findLabel lpost prog
        = some (postAsm ++ .jump lcond :: .label lexit :: cRest) := by
      have hsplit : prog = (preI ++ cCode ++ [.op .iszero, .jumpi lexit]
          ++ bodyAsm) ++ .label lpost
          :: (postAsm ++ .jump lcond :: .label lexit :: cRest) := by
        rw [← hpreI]
        simp
      rw [hsplit]
      exact findLabel_boundary (by rw [← hsplit]; exact hnodup)
    have hsimBody : ASteps prog
        ⟨bodyAsm ++ (.label lpost :: postAsm
            ++ .jump lcond :: .label lexit :: cRest),
          wimg V0 ++ σ, st1⟩
        ⟨postAsm ++ .jump lcond :: .label lexit :: cRest,
          wimg Vb ++ σ, stb⟩ := by
      rcases hob with rfl | rfl
      · obtain ⟨hΓb, hlenb, hsimb⟩ := hout
        have h := (hsimb hΦ) (preI ++ cCode ++ [.op .iszero, .jumpi lexit])
          (.label lpost :: postAsm ++ .jump lcond :: .label lexit :: cRest)
          σ (by rw [← hpreI]; simp)
        refine h.snoc ?_
        exact .label
      · obtain ⟨lc, hlc, hlenB, hnmB, hsimB⟩ := hout
        obtain rfl : (⟨lexit, lpost, V0.length⟩ : LoopCtx) = lc := by
          injection hlc
        have htrim : trim V0.length Vb = Vb := by
          unfold trim
          rw [show Vb.length - V0.length = 0 from by omega]
          exact List.drop_zero
        have h := (hsimB hΦ) (preI ++ cCode ++ [.op .iszero, .jumpi lexit])
          (.label lpost :: postAsm ++ .jump lcond :: .label lexit :: cRest)
          (postAsm ++ .jump lcond :: .label lexit :: cRest)
          σ (by rw [← hpreI]; simp) hfindPost
        rw [htrim] at h
        exact h
    have hcv0 : cv ≠ (0 : U256) := hcv
    have hzero : YulSemantics.EVM.b2w (cv = 0) = 0 := by
      unfold YulSemantics.EVM.b2w
      rw [if_neg (by simp only [decide_eq_true_eq]; exact fun h => hcv0 h)]
    have h1 : ASteps prog
        ⟨(cCode ++ [.op .iszero]) ++ (.jumpi lexit :: (bodyAsm
            ++ .label lpost :: postAsm ++ .jump lcond
            :: .label lexit :: cRest)),
          wimg V0 ++ σ, st0⟩
        ⟨.jumpi lexit :: (bodyAsm ++ .label lpost :: postAsm
            ++ .jump lcond :: .label lexit :: cRest),
          .word (YulSemantics.EVM.b2w (cv = 0)) :: (wimg V0 ++ σ), st1⟩ :=
      (asimE_condPrologue (ihc Φ 0 n₁ cCode n₂ hce hΦ)) preI
        (.jumpi lexit :: (bodyAsm ++ .label lpost :: postAsm
          ++ .jump lcond :: .label lexit :: cRest)) [] σ
        (by rw [← hpreI]; simp) rfl
    have h2 : AStep prog
        ⟨.jumpi lexit :: (bodyAsm ++ .label lpost :: postAsm
            ++ .jump lcond :: .label lexit :: cRest),
          .word (YulSemantics.EVM.b2w (cv = 0)) :: (wimg V0 ++ σ), st1⟩
        ⟨bodyAsm ++ (.label lpost :: postAsm
            ++ .jump lcond :: .label lexit :: cRest),
          wimg V0 ++ σ, st1⟩ := by
      have := AStep.jumpiFall (prog := prog) (l := lexit)
        (v := YulSemantics.EVM.b2w (cv = 0))
        (c := bodyAsm ++ .label lpost :: postAsm
          ++ .jump lcond :: .label lexit :: cRest)
        (σ := wimg V0 ++ σ) (yst := st1) hzero
      simpa using this
    obtain ⟨conf, hsteps, hhalt⟩ := (hsimp' hΦ)
      (preI ++ cCode ++ [.op .iszero, .jumpi lexit] ++ bodyAsm
        ++ [.label lpost])
      (.jump lcond :: .label lexit :: cRest) σ (by rw [← hpreI]; simp)
    refine ⟨conf, ?_, hhalt⟩
    have hshape : loopIter lcond lpost lexit cCode bodyAsm postAsm cRest
        = (cCode ++ [Asm.op .iszero]) ++ (.jumpi lexit :: (bodyAsm
            ++ .label lpost :: postAsm ++ .jump lcond
            :: .label lexit :: cRest)) := by
      simp
    rw [hshape]
    exact ((h1.snoc h2).trans hsimBody).trans hsteps
  | loopBreak hc hcv hbody ihc ihbody =>
    rename_i funs0 V0 st0 ce post0 body0 cv st1 Vb stb
    intro Φ F lcond lpost lexit cCode bodyAsm postAsm n₁ n₂ n₃ n₄
      hF hce hbA hpA
    have hout := ihbody Φ F (some ⟨lexit, lpost, V0.length⟩) n₂ bodyAsm
      (names V0) n₃ hF (Nat.le_refl _) (stmt_of_block hbA)
    obtain ⟨lc, hlc, hlenB, hnmB, hsimB⟩ := hout
    obtain rfl : (⟨lexit, lpost, V0.length⟩ : LoopCtx) = lc := by
      injection hlc
    have hVble : Vb.length ≤ V0.length := by
      cases hbody with
      | block hin =>
        show (YulSemantics.restore V0 _).length ≤ _
        unfold YulSemantics.restore
        simp
        omega
    have htrim : trim V0.length Vb = Vb := by
      unfold trim
      rw [show Vb.length - V0.length = 0 from by omega]
      exact List.drop_zero
    rw [htrim] at hnmB
    rw [show V0.length - V0.length = 0 from by omega, List.drop_zero] at hnmB
    refine ⟨hnmB, fun cRest hcond hΦ σ => ?_⟩
    obtain ⟨preI, hpreI⟩ := findLabel_suffix hcond
    have hfindExit : findLabel lexit prog = some cRest := by
      have hsplit : prog = (preI ++ cCode ++ [.op .iszero, .jumpi lexit]
          ++ bodyAsm ++ .label lpost :: postAsm ++ [.jump lcond])
          ++ .label lexit :: cRest := by
        rw [← hpreI]
        simp
      rw [hsplit]
      exact findLabel_boundary (by rw [← hsplit]; exact hnodup)
    have hcv0 : cv ≠ (0 : U256) := hcv
    have hzero : YulSemantics.EVM.b2w (cv = 0) = 0 := by
      unfold YulSemantics.EVM.b2w
      rw [if_neg (by simp only [decide_eq_true_eq]; exact fun h => hcv0 h)]
    have h1 : ASteps prog
        ⟨(cCode ++ [.op .iszero]) ++ (.jumpi lexit :: (bodyAsm
            ++ .label lpost :: postAsm ++ .jump lcond :: .label lexit :: cRest)),
          wimg V0 ++ σ, st0⟩
        ⟨.jumpi lexit :: (bodyAsm ++ .label lpost :: postAsm
            ++ .jump lcond :: .label lexit :: cRest),
          .word (YulSemantics.EVM.b2w (cv = 0)) :: (wimg V0 ++ σ), st1⟩ :=
      (asimE_condPrologue (ihc Φ 0 n₁ cCode n₂ hce hΦ)) preI
        (.jumpi lexit :: (bodyAsm ++ .label lpost :: postAsm
          ++ .jump lcond :: .label lexit :: cRest)) [] σ
        (by rw [← hpreI]; simp) rfl
    have h2 : AStep prog
        ⟨.jumpi lexit :: (bodyAsm ++ .label lpost :: postAsm
            ++ .jump lcond :: .label lexit :: cRest),
          .word (YulSemantics.EVM.b2w (cv = 0)) :: (wimg V0 ++ σ), st1⟩
        ⟨bodyAsm ++ (.label lpost :: postAsm
            ++ .jump lcond :: .label lexit :: cRest),
          wimg V0 ++ σ, st1⟩ := by
      have := AStep.jumpiFall (prog := prog) (l := lexit)
        (v := YulSemantics.EVM.b2w (cv = 0))
        (c := bodyAsm ++ .label lpost :: postAsm
          ++ .jump lcond :: .label lexit :: cRest)
        (σ := wimg V0 ++ σ) (yst := st1) hzero
      simpa using this
    have h3 : ASteps prog
        ⟨bodyAsm ++ (.label lpost :: postAsm
            ++ .jump lcond :: .label lexit :: cRest),
          wimg V0 ++ σ, st1⟩
        ⟨cRest, wimg (trim V0.length Vb) ++ σ, stb⟩ :=
      (hsimB hΦ) (preI ++ cCode ++ [.op .iszero, .jumpi lexit])
        (.label lpost :: postAsm ++ .jump lcond :: .label lexit :: cRest)
        cRest σ (by rw [← hpreI]; simp) hfindExit
    rw [htrim] at h3
    have hshape : loopIter lcond lpost lexit cCode bodyAsm postAsm cRest
        = (cCode ++ [Asm.op .iszero]) ++ (.jumpi lexit :: (bodyAsm
            ++ .label lpost :: postAsm ++ .jump lcond
            :: .label lexit :: cRest)) := by
      simp
    rw [hshape]
    exact (h1.snoc h2).trans h3
  | loopLeave hc hcv hbody ihc ihbody =>
    rename_i funs0 V0 st0 ce post0 body0 cv st1 Vb stb
    intro Φ F lcond lpost lexit cCode bodyAsm postAsm n₁ n₂ n₃ n₄
      hF hce hbA hpA
    have hout := ihbody Φ F (some ⟨lexit, lpost, V0.length⟩) n₂ bodyAsm
      (names V0) n₃ hF (Nat.le_refl _) (stmt_of_block hbA)
    obtain ⟨fc, hfc, hlenB, hnmB, hsimB⟩ := hout
    refine ⟨fc, hfc, hlenB, hnmB, fun cRest hcond hΦ σ cL hfindEx => ?_⟩
    obtain ⟨preI, hpreI⟩ := findLabel_suffix hcond
    have hcv0 : cv ≠ (0 : U256) := hcv
    have hzero : YulSemantics.EVM.b2w (cv = 0) = 0 := by
      unfold YulSemantics.EVM.b2w
      rw [if_neg (by simp only [decide_eq_true_eq]; exact fun h => hcv0 h)]
    have h1 : ASteps prog
        ⟨(cCode ++ [.op .iszero]) ++ (.jumpi lexit :: (bodyAsm
            ++ .label lpost :: postAsm ++ .jump lcond :: .label lexit :: cRest)),
          wimg V0 ++ σ, st0⟩
        ⟨.jumpi lexit :: (bodyAsm ++ .label lpost :: postAsm
            ++ .jump lcond :: .label lexit :: cRest),
          .word (YulSemantics.EVM.b2w (cv = 0)) :: (wimg V0 ++ σ), st1⟩ :=
      (asimE_condPrologue (ihc Φ 0 n₁ cCode n₂ hce hΦ)) preI
        (.jumpi lexit :: (bodyAsm ++ .label lpost :: postAsm
          ++ .jump lcond :: .label lexit :: cRest)) [] σ
        (by rw [← hpreI]; simp) rfl
    have h2 : AStep prog
        ⟨.jumpi lexit :: (bodyAsm ++ .label lpost :: postAsm
            ++ .jump lcond :: .label lexit :: cRest),
          .word (YulSemantics.EVM.b2w (cv = 0)) :: (wimg V0 ++ σ), st1⟩
        ⟨bodyAsm ++ (.label lpost :: postAsm
            ++ .jump lcond :: .label lexit :: cRest),
          wimg V0 ++ σ, st1⟩ := by
      have := AStep.jumpiFall (prog := prog) (l := lexit)
        (v := YulSemantics.EVM.b2w (cv = 0))
        (c := bodyAsm ++ .label lpost :: postAsm
          ++ .jump lcond :: .label lexit :: cRest)
        (σ := wimg V0 ++ σ) (yst := st1) hzero
      simpa using this
    have h3 : ASteps prog
        ⟨bodyAsm ++ (.label lpost :: postAsm
            ++ .jump lcond :: .label lexit :: cRest),
          wimg V0 ++ σ, st1⟩
        ⟨cL, wimg (trim fc.depth Vb) ++ σ, stb⟩ :=
      (hsimB hΦ) (preI ++ cCode ++ [.op .iszero, .jumpi lexit])
        (.label lpost :: postAsm ++ .jump lcond :: .label lexit :: cRest)
        cL σ (by rw [← hpreI]; simp) hfindEx
    have hshape : loopIter lcond lpost lexit cCode bodyAsm postAsm cRest
        = (cCode ++ [Asm.op .iszero]) ++ (.jumpi lexit :: (bodyAsm
            ++ .label lpost :: postAsm ++ .jump lcond
            :: .label lexit :: cRest)) := by
      simp
    rw [hshape]
    exact (h1.snoc h2).trans h3
  | loopBodyHalt hc hcv hbody ihc ihbody =>
    rename_i funs0 V0 st0 ce post0 body0 cv st1 Vb stb
    intro Φ F lcond lpost lexit cCode bodyAsm postAsm n₁ n₂ n₃ n₄
      hF hce hbA hpA
    have hsimB := ihbody Φ F (some ⟨lexit, lpost, V0.length⟩) n₂ bodyAsm
      (names V0) n₃ hF (Nat.le_refl _) (stmt_of_block hbA)
    intro cRest hcond hΦ σ
    obtain ⟨preI, hpreI⟩ := findLabel_suffix hcond
    have hcv0 : cv ≠ (0 : U256) := hcv
    have hzero : YulSemantics.EVM.b2w (cv = 0) = 0 := by
      unfold YulSemantics.EVM.b2w
      rw [if_neg (by simp only [decide_eq_true_eq]; exact fun h => hcv0 h)]
    have h1 : ASteps prog
        ⟨(cCode ++ [.op .iszero]) ++ (.jumpi lexit :: (bodyAsm
            ++ .label lpost :: postAsm ++ .jump lcond :: .label lexit :: cRest)),
          wimg V0 ++ σ, st0⟩
        ⟨.jumpi lexit :: (bodyAsm ++ .label lpost :: postAsm
            ++ .jump lcond :: .label lexit :: cRest),
          .word (YulSemantics.EVM.b2w (cv = 0)) :: (wimg V0 ++ σ), st1⟩ :=
      (asimE_condPrologue (ihc Φ 0 n₁ cCode n₂ hce hΦ)) preI
        (.jumpi lexit :: (bodyAsm ++ .label lpost :: postAsm
          ++ .jump lcond :: .label lexit :: cRest)) [] σ
        (by rw [← hpreI]; simp) rfl
    have h2 : AStep prog
        ⟨.jumpi lexit :: (bodyAsm ++ .label lpost :: postAsm
            ++ .jump lcond :: .label lexit :: cRest),
          .word (YulSemantics.EVM.b2w (cv = 0)) :: (wimg V0 ++ σ), st1⟩
        ⟨bodyAsm ++ (.label lpost :: postAsm
            ++ .jump lcond :: .label lexit :: cRest),
          wimg V0 ++ σ, st1⟩ := by
      have := AStep.jumpiFall (prog := prog) (l := lexit)
        (v := YulSemantics.EVM.b2w (cv = 0))
        (c := bodyAsm ++ .label lpost :: postAsm
          ++ .jump lcond :: .label lexit :: cRest)
        (σ := wimg V0 ++ σ) (yst := st1) hzero
      simpa using this
    obtain ⟨conf, hsteps, hhalt⟩ := (hsimB hΦ)
      (preI ++ cCode ++ [.op .iszero, .jumpi lexit])
      (.label lpost :: postAsm ++ .jump lcond :: .label lexit :: cRest)
      σ (by rw [← hpreI]; simp)
    refine ⟨conf, ?_, hhalt⟩
    have hshape : loopIter lcond lpost lexit cCode bodyAsm postAsm cRest
        = (cCode ++ [Asm.op .iszero]) ++ (.jumpi lexit :: (bodyAsm
            ++ .label lpost :: postAsm ++ .jump lcond
            :: .label lexit :: cRest)) := by
      simp
    rw [hshape]
    exact (h1.snoc h2).trans hsteps

end YulEvmCompiler.SimA
