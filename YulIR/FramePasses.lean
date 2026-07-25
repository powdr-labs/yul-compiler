import YulIR.Frame

set_option warningAsError true
/-!
# YulIR.FinFrameSketchPasses — two real passes on the `Fin n`-frame IR

To measure the ergonomics concretely, here are two genuine passes over the frame IR of
`YulIR.FinFrameSketch`:

* **`valueNumber`** — constant/copy propagation + common-subexpression elimination. This is the
  meatiest of the current pipeline passes, and the headline finding is its **type**:
  `Block n → Block n`. It rewrites operands and memoises pure expressions into *existing* slots, so
  it **never grows the frame** — no weakening, no `Fin` arithmetic, the analysis just keys its
  environment on `Fin n`. The unified-write model costs nothing here: "immutable" is `isConstant`
  (written-once), exactly the precondition the named pass used ("never reassigned").

* **`inlineTail`** — inline a call, the pass that *does* pay the friction. Merging the callee's
  `k`-slot frame into the caller's `n`-slot frame forces the result into `Block (n + k)`: the caller
  is reindexed with `Fin.castAdd k` and the callee body with `Fin.natAdd n`. That whole-tree slot
  remap on both sides is the intrinsic-typing tax — real, but confined to frame-*growing* passes.

Net: the tax is exactly where the theory predicted — inlining/LICM/rematerialisation pay it,
value-numbering/structural/DCE do not.
-/

namespace YulIR.FinFrame

open YulSemantics (Ident Literal)

/-! ### Value numbering — `Block n → Block n`, no frame growth -/

/-- Immutability of an operand under the "constant slots" predicate `imm`. -/
def isImmAtom (imm : Fin n → Bool) : Atom n → Bool
  | .lit _  => true
  | .slot i => imm i

/-- Resolve a slot through the value environment (constant/copy propagation). -/
def resolveAtom (env : List (Fin n × Atom n)) : Atom n → Atom n
  | .lit l  => .lit l
  | .slot i => match env.find? (fun p => p.1 == i) with
               | some p => p.2
               | none   => .slot i

/-- Resolve an rhs's operands. -/
def resolveRhs (env : List (Fin n × Atom n)) : Rhs n → Rhs n
  | .atom a       => .atom (resolveAtom env a)
  | .builtin op a => .builtin op (a.map (resolveAtom env))
  | .call fn a    => .call fn (a.map (resolveAtom env))

/-- Record a resolved `write dst := rhs'`: update the value environment and available-expression
table, and return the rhs to emit (a copy when `dst` becomes a known constant/slot or a CSE hit).
Only *constant* (`imm`) destinations with all-immutable operands are tracked, so entries never go
stale — the same soundness discipline as the named pass. -/
def recordWrite (imm : Fin n → Bool) (env : List (Fin n × Atom n)) (avail : List (Rhs n × Fin n))
    (dst : Fin n) (rhs' : Rhs n) : List (Fin n × Atom n) × List (Rhs n × Fin n) × Rhs n :=
  if ! imm dst then (env, avail, rhs')
  else match rhs' with
    | .atom a =>
        if isImmAtom imm a then ((dst, a) :: env, avail, .atom a) else (env, avail, .atom a)
    | .builtin op as =>
        if Op.isPure op && as.all (isImmAtom imm) then
          match avail.find? (fun p => p.1 == rhs') with
          | some (_, w) => ((dst, .slot w) :: env, avail, .atom (.slot w))   -- CSE hit: copy earlier result
          | none        => (env, (rhs', dst) :: avail, rhs')                 -- memoise
        else (env, avail, rhs')
    | .call _ _ => (env, avail, rhs')

/-! Value numbering over a block, given the immutability predicate and current maps. The result is
`Block n` — the frame is never touched. -/
mutual
/-- Value-number a single statement: emit the rewritten statement and the updated maps (only an
`assign` to a single slot grows the maps; control-flow statements recurse into their sub-blocks but
do not thread map updates back out). -/
def vnStmt (imm : Fin n → Bool) (env : List (Fin n × Atom n)) (avail : List (Rhs n × Fin n)) :
    Stmt n → Stmt n × List (Fin n × Atom n) × List (Rhs n × Fin n)
  | .assign [d] rhs =>
      let (env', avail', out) := recordWrite imm env avail d (resolveRhs env rhs)
      (.assign [d] out, env', avail')
  | .assign ds rhs => (.assign ds (resolveRhs env rhs), env, avail)
  | .cond c b => (.cond (resolveAtom env c) (vnBlock imm env avail b), env, avail)
  | .switch c cs df =>
      (.switch (resolveAtom env c) (vnCases imm env avail cs) (vnDflt imm env avail df), env, avail)
  | .loop post body => (.loop (vnBlock imm env avail post) (vnBlock imm env avail body), env, avail)
  | s => (s, env, avail)
def vnBlock (imm : Fin n → Bool) (env : List (Fin n × Atom n))
    (avail : List (Rhs n × Fin n)) : Block n → Block n
  | []      => []
  | s :: rest =>
      let (s', env', avail') := vnStmt imm env avail s
      s' :: vnBlock imm env' avail' rest
def vnCases (imm : Fin n → Bool) (env : List (Fin n × Atom n)) (avail : List (Rhs n × Fin n)) :
    List (Literal × Block n) → List (Literal × Block n)
  | []             => []
  | (l, b) :: rest => (l, vnBlock imm env avail b) :: vnCases imm env avail rest
def vnDflt (imm : Fin n → Bool) (env : List (Fin n × Atom n)) (avail : List (Rhs n × Fin n)) :
    Option (Block n) → Option (Block n)
  | none   => none
  | some b => some (vnBlock imm env avail b)
end

/-- Immutability for value tracking. A local slot is immutable iff written at most once (its single
write is its declaration, dominating all reads). Parameters and returns carry an implicit initial
value (arg / zero) with **no** declaration-write, so a *written* param/ret is a reassignment of that
initial value — mutable — and must be excluded (a read before its write, e.g. `x := f(x)` on a
return var, sees the old value). Read-only params/rets (never written) stay immutable. -/
def immSlot (frozen : List (Fin n)) (b : Block n) (d : Fin n) : Bool :=
  let c := (blockWrites b).count d
  if frozen.contains d then c == 0 else c ≤ 1

/-- Value numbering over a frame body, given the params+returns (`frozen`) whose writes are
reassignments of an initial value. -/
def valueNumber (frozen : List (Fin n)) (b : Block n) : Block n :=
  vnBlock (immSlot frozen b) [] [] b

/-! ### The value-numbering safety checker

`vnBlock` is sound only under a *read-after-write* discipline: an entry it records references
"immutable" slots, and stays valid only if those slots are never written afterwards. `immSlot`
guarantees at most one write, but not that the write *precedes* the reads — `d := j; j := 5; use d`
would record `d ≡ j` and then rewrite `use d` into `use j`, wrongly. The checker below walks the
block exactly like `vnBlock`, threading the set `W` of already-written immutable slots, and demands:

* every write to an immutable slot targets a slot not yet in `W` (single write, now used up);
* whenever a statement would *record* (an immutable single destination with a recordable rhs),
  every slot operand is already in `W`;
* a recorded builtin returns exactly one value (probed at the call's arity — excludes zero-output
  pure ops like `pop`, whose CSE would fabricate a write).

The soundness proof takes `imm` as a black box: any `imm` passing the checker is safe, `immSlot` is
just the heuristic that makes real code pass. -/

/-- `op` applied at arity `k` returns exactly one value. For a pure op the output arity depends only
on the input arity, so probing with dummy operands decides it. -/
def probe1 (op : Op) (k : Nat) : Bool :=
  match YulSemantics.EVM.stepOp op (List.replicate k 0) YulSemantics.EVM.EvmState.init with
  | some (.ok [_] _) => true
  | _ => false

/-- An rhs is safe to sit in a *recording* position (an `imm` single destination): if `recordWrite`
would track it, every slot operand must already be written. -/
def vnSafeRhs (imm : Fin n → Bool) (W : List (Fin n)) : Rhs n → Bool
  | .atom (.lit _) => true
  | .atom (.slot s) => !imm s || W.contains s
  | .builtin op args =>
      !(Op.isPure op && args.all (isImmAtom imm)) ||
        (args.all (fun a => match a with | .slot s => W.contains s | .lit _ => true) &&
         probe1 op args.length)
  | .call _ _ => true

/-- The recording condition applies only to single-destination assigns. -/
def vnSafeDsts (imm : Fin n → Bool) (W : List (Fin n)) : List (Fin n) → Rhs n → Bool
  | [d], rhs => !imm d || vnSafeRhs imm W rhs
  | _, _ => true

mutual
def vnSafeStmt (imm : Fin n → Bool) (W : List (Fin n)) : Stmt n → Option (List (Fin n))
  | .assign ds rhs =>
      if ds.all (fun d => !imm d || !W.contains d) && vnSafeDsts imm W ds rhs then
        some (ds.filter imm ++ W)
      else none
  | .cond _ b => vnSafeBlock imm W b
  | .switch _ cs df =>
      match vnSafeCases imm W cs with
      | some W' => vnSafeDflt imm W' df
      | none    => none
  | .loop post body =>
      match vnSafeBlock imm W body with
      | some W' => vnSafeBlock imm W' post
      | none    => none
  | _ => some W
def vnSafeBlock (imm : Fin n → Bool) (W : List (Fin n)) : Block n → Option (List (Fin n))
  | []        => some W
  | s :: rest =>
      match vnSafeStmt imm W s with
      | some W' => vnSafeBlock imm W' rest
      | none    => none
def vnSafeCases (imm : Fin n → Bool) (W : List (Fin n)) :
    List (Literal × Block n) → Option (List (Fin n))
  | []             => some W
  | (_, b) :: rest =>
      match vnSafeBlock imm W b with
      | some W' => vnSafeCases imm W' rest
      | none    => none
def vnSafeDflt (imm : Fin n → Bool) (W : List (Fin n)) :
    Option (Block n) → Option (List (Fin n))
  | none   => some W
  | some b => vnSafeBlock imm W b
end

/-- The whole-body safety check for `valueNumber`: run the checker under `immSlot`, seeding `W` with
the immutable frozen slots (params/returns carry an initial value, so they count as written). -/
def vnSafe (frozen : List (Fin n)) (b : Block n) : Bool :=
  (vnSafeBlock (immSlot frozen b) (frozen.filter (immSlot frozen b)) b).isSome

/-- `valueNumber` guarded by the safety checker: the pass runs only on blocks the checker accepts
(the soundness proof covers exactly the checked case, making this variant unconditionally sound). -/
def valueNumberChecked (frozen : List (Fin n)) (b : Block n) : Block n :=
  if vnSafe frozen b then valueNumber frozen b else b

/-! ### Inlining — the pass that pays the frame-growth tax -/

/-- Inline a call `dsts := callee(args)` that sits at the *tail* of a caller whose earlier
statements are `pre : Block n`. The result lives in the enlarged frame `Block (n + callee.nslots)`:

* the caller prefix and the call's args/dsts are reindexed with `Fin.castAdd` (caller slots occupy
  the low part of the merged frame);
* the callee body is reindexed with `Fin.natAdd n` (callee slots occupy the high part);
* parameters are bound and returns extracted by `write`s across the two slot ranges.

The two full-tree `mapBlock` remaps are exactly the intrinsic-typing friction. (A full inliner folds
this over every inlinable call site, each fold growing the frame — restricted to non-recursive,
`leave`-free callees; `leave`/recursion handling is orthogonal future work.) -/
def inlineTail (pre : Block n) (callee : Function)
    (args : List (Atom n)) (dsts : List (Fin n)) : Block (n + callee.nslots) :=
  let k := callee.nslots
  let cast : Fin n → Fin (n + k) := Fin.castAdd k          -- caller slots ↪ low part
  let off  : Fin k → Fin (n + k) := Fin.natAdd n           -- callee slots ↪ high part
  let preW    := mapBlock cast pre
  let argsW   := args.map (mapAtom cast)
  let dstsW   := dsts.map cast
  let binds   := (callee.params.zip argsW).map (fun p => Stmt.assign [off p.1] (.atom p.2))
  let bodyOff := mapBlock off callee.body
  let extract := (dstsW.zip callee.rets).map (fun p => Stmt.assign [p.1] (.atom (.slot (off p.2))))
  preW ++ binds ++ bodyOff ++ extract

/-! ### Demonstrations -/

/-- Value numbering keeps the frame: `slot0 := add(1,2); slot1 := add(1,2)` (a CSE opportunity) is
optimised within `Block 2`. -/
example : Block 2 :=
  valueNumber [] [ .assign [0] (.builtin .add [.lit (.number 1), .lit (.number 2)])
              , .assign [1] (.builtin .add [.lit (.number 1), .lit (.number 2)]) ]

/-- Inlining a 1-slot identity-ish callee into a 1-slot caller yields a `Block (1 + 1)` — the frame
grew, and both sides were reindexed. -/
example : Block (1 + 1) :=
  inlineTail (n := 1)
    (pre := [])
    (callee := { nslots := 1, params := [0], rets := [0], body := [] })
    (args := [.lit (.number 7)]) (dsts := [0])

end YulIR.FinFrame
