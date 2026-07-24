import YulIR.Analysis

/-!
# YulIR.Uniquify — make every variable declaration unique

α-renames all bound variables so each declaration gets a globally fresh name and every
reference resolves to its binder. This removes shadowing, so the value-tracking passes can
key on names globally without scope confusion. Function names are left unchanged (calls
resolve by name; the value passes treat calls as opaque anyway).

Fresh names are `_u<n>`, chosen to avoid every identifier already in the program, so a
renamed variable can never collide with an existing name or another fresh one. This is a
behaviour-preserving α-renaming (validated by the interpreter round-trip check).
-/

namespace YulIR

open YulSemantics (Ident Literal)

/-- Renaming environment: source name → fresh name, innermost first. -/
abbrev Ren := List (Ident × Ident)

/-- Look up a variable's current fresh name (unchanged if unbound — e.g. a stray global). -/
def Ren.get (σ : Ren) (x : Ident) : Ident :=
  match σ.find? (fun p => p.1 == x) with
  | some p => p.2
  | none   => x

/-- Rename an atom's variable. -/
def renAtom (σ : Ren) : Atom → Atom
  | .lit l => .lit l
  | .var x => .var (σ.get x)

/-- Rename an rhs's operands. -/
def renRhs (σ : Ren) : Rhs → Rhs
  | .atom a       => .atom (renAtom σ a)
  | .builtin op a => .builtin op (a.map (renAtom σ))
  | .call fn a    => .call fn (a.map (renAtom σ))

/-- Allocate a fresh `_u<n>` not present in `ids`. -/
partial def freshName (ids : List Ident) : StateM Nat Ident := do
  let n ← get
  set (n + 1)
  let nm := s!"_u{n}"
  if ids.contains nm then freshName ids else pure nm

/-- Fresh names for a list of binders. -/
def freshNames (ids : List Ident) : List Ident → StateM Nat (List Ident)
  | []      => pure []
  | _ :: xs => do
      let f ← freshName ids
      let rest ← freshNames ids xs
      pure (f :: rest)

mutual
/-- Uniquify a statement; returns the renamed statement and the renaming extended with any
bindings it introduces (for subsequent statements in the *same* scope). -/
partial def uniqStmt (ids : List Ident) (σ : Ren) : Stmt → StateM Nat (Stmt × Ren)
  | .letD vars rhs => do
      let rhs' := renRhs σ rhs               -- rhs is evaluated before the binders exist
      let fresh ← freshNames ids vars
      pure (.letD fresh rhs', (vars.zip fresh) ++ σ)
  | .assign vars rhs =>
      pure (.assign (vars.map σ.get) (renRhs σ rhs), σ)
  | .effect rhs =>
      pure (.effect (renRhs σ rhs), σ)
  | .cond c body => do
      let body' ← uniqBlock ids σ body
      pure (.cond (renAtom σ c) body', σ)
  | .switch c cases dflt => do
      let cases' ← uniqCases ids σ cases
      let dflt' ← uniqOpt ids σ dflt
      pure (.switch (renAtom σ c) cases' dflt', σ)
  | .loop post body => do
      let post' ← uniqBlock ids σ post
      let body' ← uniqBlock ids σ body
      pure (.loop post' body', σ)
  | .block body => do
      let body' ← uniqBlock ids σ body
      pure (.block body', σ)
  | .funDef name ps rs body => do
      let ps' ← freshNames ids ps
      let rs' ← freshNames ids rs
      let σbody := (ps.zip ps') ++ (rs.zip rs')   -- callee sees only its params/rets
      let body' ← uniqBlock ids σbody body
      pure (.funDef name ps' rs' body', σ)
  | s => pure (s, σ)

/-- Uniquify a block, threading the renaming across its statements. -/
partial def uniqBlock (ids : List Ident) (σ : Ren) : Block → StateM Nat Block
  | []      => pure []
  | s :: ss => do
      let (s', σ') ← uniqStmt ids σ s
      let ss' ← uniqBlock ids σ' ss
      pure (s' :: ss')

partial def uniqCases (ids : List Ident) (σ : Ren) :
    List (Literal × Block) → StateM Nat (List (Literal × Block))
  | []           => pure []
  | (l, b) :: rest => do
      let b' ← uniqBlock ids σ b
      let rest' ← uniqCases ids σ rest
      pure ((l, b') :: rest')

partial def uniqOpt (ids : List Ident) (σ : Ren) : Option Block → StateM Nat (Option Block)
  | none   => pure none
  | some b => do
      let b' ← uniqBlock ids σ b
      pure (some b')
end

/-- Rename every variable in a block to a globally unique name. -/
def uniquify (b : Block) : Block := (uniqBlock (allIdents b) [] b).run' 0

end YulIR
