/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Lean.Meta.Constructions
public import Lean.Meta.SizeOf
import Lean.Meta.Constructions.CtorIdx
import Lean.Meta.Constructions.CtorElim
import Lean.Meta.IndPredBelow
import Lean.Meta.Injective
public import Lean.Elab.PreDefinition.Structural
import Lean.Compiler.CSimpAttr
import Lean.Elab.App

public section

/-!
# Lowering a universe-heterogeneous mutual inductive block

Lean requires every member of a mutual inductive block to live in the same
universe.  The restriction is checked three times over: once while the headers
are elaborated, once after the constructors are, and once by the kernel.  So a
block like

```
mutual
inductive A : Prop where
  | fromB : B → A
  | fromC : C → A
inductive B : Type 0 where
  | fromA : Nat → A → B
inductive C : Type 2 where
  | fromA : A → C
  | higherUniv : Nat → Type → C
end
```

is rejected, even though it denotes something perfectly sensible.

This module implements the lowering behind this library's `mutual`, which
accepts such a block by translating it into ordinary declarations.  Everything
it adds to the environment is an ordinary inductive type, definition or
theorem, so no part of it asks anything new of the kernel and the worst it can
do is fail.

## The translation

1. An all-`Prop` **shadow** of the whole block, `X_i._shadow`.  Every block has
   one: the side condition on a constructor field of a `Prop`-valued inductive
   is `imax l' 0 ≤ 0`, which is vacuous, so the fields can be copied verbatim
   with member occurrences redirected to the shadow.

2. The **data** members, declared under the users' own names, against the
   shadow.  They are grouped into strongly connected components of the
   data-only dependency graph and emitted in topological order.  Each SCC is
   necessarily universe-homogeneous -- an edge `i → j` forces `l_j ≤ l_i`, so a
   cycle forces equality -- hence each is an ordinary mutual block.

   Not every member reaches this step.  A copy that only the shadow needs --
   `Mumi.Denest` calls it a *ghost*, and marks it with a `GhostInfo` -- is
   passed over here, and everything from step 3 on writes the type it copies
   where the shadow writes the member.  So a ghost's constructors and `casesOn`
   are the copied type's, and the writer never meets its name.

   Its recursor is the copied type's too where the occurrences it stands for all
   sit in `Prop` members' constructors, which the lowering emits as definitions.
   Where a data member has a field at one, the occurrence goes to the kernel
   written out in full, the kernel denests it as it would have done had no
   `Prop` forced a copy at all, and the ghost's recursor is the `X.rec_k` that
   comes back.

3. The `Prop` members' user-facing names (reducible abbreviations for their
   shadows) and constructors, the squash maps `X._squash : X → X._shadow`, and
   a block-wide recursor `X.mutualRec` for every member.

A data SCC may come back from `addDecl` larger than it went in: a nesting the
kernel can denest is one it *does* denest, giving itself a type for the
occurrence and an extra recursor `X.rec_k` at it.  Those extras are carried
through rather than hidden, so the block's recursors range over them too and
the constructor keeps the type the writer wrote; see the section on what the
kernel denested.

Only the `Prop` members are mangled.  Data members are honest inductive types
under the names the user wrote, so `match`, `induction`, `cases`, `injection`,
`noConfusion`, `deriving`, `sizeOf` and the code generator all work on them as
usual, and the block's computational content stays computable.  A `Prop`
member's constructors have to be re-derived, because their fields have the
wrong types in the shadow: `A.fromB` must take a real `B`, not a `B._shadow`.

## Why the recursors come out right

* A `Prop` member of a block with at least two members is never
  large-eliminating, and the shadow has the same number of members, so it has
  exactly the original's elimination strength.  Squashing the data members
  loses nothing.  (This is also the safety boundary: we derive *universes* per
  member, never *elimination* per member.)
* A `Prop` member's iota rules are equations between proofs, so they hold by
  proof irrelevance.
* All computational content sits in the data recursors, which are the native
  recursors of the honestly-declared data members, so their iota rules hold by
  delta on `mutualRec` followed by native iota.

The one place a choice principle is unavoidable is a `Prop` member with a
constructor field that is a *function into* a data member: the data witnesses
then have to be selected pointwise, which needs `Classical.choice`.  A block
without such a field produces axiom-free recursors.

The recursors are also computable, which takes a little work, as the code
generator compiles no recursor application at all; see the section on
implementations below.
-/

namespace Lean.Elab.MultiuniverseInductive

open Lean Meta

/-- Parent of every trace class this library registers, so that
`set_option trace.Mumi true` turns all of them on at once. -/
initialize registerTraceClass `Mumi

/-! ## Auxiliary names -/

/-- The all-`Prop` shadow of member `n`. -/
def shadowName (n : Name) : Name := n ++ `_shadow

/-- `X._squash : X → X._shadow`, the map that forgets a data member's data. -/
def squashName (n : Name) : Name := n ++ `_squash

/-- Re-root a constructor name `X.c` at `newRoot`, giving `newRoot.c`. -/
def reroot (memberName newRoot ctorName : Name) : Name :=
  ctorName.replacePrefix memberName newRoot

/-- `List.replicate` as an `Array`. -/
private def rep {α : Type _} (n : Nat) (a : α) : Array α := (List.replicate n a).toArray

/-! ## Input -/

/--
What a member that exists only in the *shadow* stands for in the real world.

A nesting under a `Prop` head has to become a member of the block: the shadow
copies every constructor field with the members redirected to their shadows, and
a redirected `List B` would read `List B._shadow`, which is not even well-typed,
so the shadow needs a `Prop` analogue of `List B` of its own.  But that argument
is about the shadow alone.  In the real world the occurrence sits in a `Prop`
member's constructor, which the lowering emits as a *definition* rather than as
a kernel constructor, so nothing there stops it from being stated at `List B`
itself.

So such a member is declared in the shadow and nowhere else, and everything the
real world would have said about it is said about the type it copies instead:
its constructors are that type's, its recursor is built from that type's, and
`List B` is what the writer reads.  `Mumi.Denest` decides which copies can be
treated this way and lists the conditions.

A ghost a *data* member has a field at goes one step further.  There the
occurrence is not in a definition but in a kernel constructor, so `List B` is
written into the block the kernel is handed -- and the kernel denests it, which
is what it would have done had there been no `Prop` member to force a copy in
the first place.  Such a ghost's recursion is the kernel's own `B.rec_1`, and
`nativeRec?` is where `mkNests` records it once the kernel has answered.
-/
structure GhostInfo where
  /-- `fun params => I p₁ … p_k`: the type the member copies, with the block's
  own members still free variables.  The member's indices are `I`'s own, so its
  type at some indices is this applied to the parameters and then to them. -/
  value     : Expr
  /-- `I` itself, whose recursor, `casesOn` and constructors do the work. -/
  head      : Name
  levels    : List Level
  /-- How many parameters `I` takes, so that the indices of a value of this
  member's type can be read off it -- the block's own parameter count says
  nothing about them. -/
  numParams : Nat
  /-- `I`'s constructors, in `I`'s order, which is the order the copy's own
  constructors were made in. -/
  ctors     : Array Name
  /-- The kernel's recursor at this type, for a ghost the kernel denested, and
  `none` for one whose occurrences all sit in definitions.  Filled in by
  `mkNests`, which is the first point at which the kernel has been asked. -/
  nativeRec? : Option Name := none
  deriving Inhabited

/--
The elaborated block, as the elaborator hands it to the lowering.  This
is exactly the information `Lean.Elab.Command.mkInductiveDeclCore` has already
computed, with the members still represented by free variables.
-/
structure Input where
  levelParams : List Name
  /-- Number of leading section `variable`s; `numVars ≤ numParams`.  A member's
  free variable stands for the member *already applied* to these, so
  substituting a constant for it means applying that constant to them, exactly
  as `replaceIndFVarsWithConsts` does. -/
  numVars     : Nat
  numParams   : Nat
  /-- The free variables standing for the members. -/
  memberFVars : Array Expr
  memberNames : Array Name
  /-- `∀ params idxs, Sort l`, with all `numParams` binders. -/
  memberTypes : Array Expr
  ctorNames   : Array (Array Name)
  /-- `∀ params fields, X_owner params idxs`, members as free variables. -/
  ctorTypes   : Array (Array Expr)
  /-- Whether the block declares classes; if so, `SizeOf` instances and
  injectivity theorems are not generated, as for `mutual`. -/
  isClass     : Bool := false
  /-- Set by `denest` when a copy takes a constructor-local as an index of its
  own.  The kernel's denesting refuses that outright -- *nested inductive
  datatypes parameters cannot contain local variables* -- so a block that needed
  it is one Lean could not have elaborated, however homogeneous it came out. -/
  localIndices : Bool := false
  /-- Set by `denest` for a copy that is to exist in the shadow only; `none` at
  every member the writer declared.  Empty when there is nothing to say. -/
  memberGhost : Array (Option GhostInfo) := #[]

/-! ## Block description -/

/-- What a recursive constructor field recurses into. -/
structure RecField where
  /-- Index of the member this field recurses into. -/
  member : Nat
  /-- Number of leading `∀` binders before the member is reached.  Nonzero
  means the field is a *function into* the member; these are the fields that
  force `Classical.choice` when the recursor's target is a `Prop`. -/
  arity  : Nat
  deriving Inhabited, Repr

/-- One constructor of the block. -/
structure CtorInfo where
  name      : Name
  /-- Index of the member it belongs to. -/
  owner     : Nat
  /-- `∀ params fields, X_owner params idxs`, members as free variables. -/
  type      : Expr
  numFields : Nat
  /-- One entry per field; `none` for a non-recursive field. -/
  fields    : Array (Option RecField)
  deriving Inhabited

/-- One member of the block. -/
structure MemberInfo where
  name   : Name
  /-- `∀ params idxs, Sort l`.  Contains no member occurrences. -/
  type   : Expr
  level  : Level
  isProp : Bool
  ctors  : Array CtorInfo
  /-- Set when the member is declared in the shadow and nowhere else; see
  `GhostInfo`. -/
  ghost? : Option GhostInfo := none
  deriving Inhabited

/-- The elaborated block plus the results of the analysis. -/
structure Block where
  levelParams : List Name
  numVars     : Nat
  numParams   : Nat
  memberFVars : Array Expr
  members     : Array MemberInfo
  /-- Every constructor, in block order (member 0's, then member 1's, ...).
  This is the order in which minor premises appear in every recursor. -/
  allCtors    : Array CtorInfo
  /-- Data-only SCCs, in topological order (dependencies first). -/
  sccs        : Array (Array Nat)
  /-- For each member, its SCC index, or `none` if it is a `Prop` member. -/
  sccOf       : Array (Option Nat)
  /-- One fresh universe parameter per data SCC. -/
  sccLevel    : Array Name
  /-- Whether any member is a `Prop`, i.e. whether a shadow is needed. -/
  hasProp     : Bool
  isClass     : Bool
  /-- Each member as the real world names it: the constant it is declared as,
  or, for a ghost, `fun params => I p₁ … p_k` -- the type it stands for, with
  the other members already substituted.  `Block.realTypeAt` reads it. -/
  userTargets : Array Expr
  deriving Inhabited

def Block.size (b : Block) : Nat := b.members.size

/--
The name a member is actually declared under.  Data members keep the users'
own names and are honest inductives; only `Prop` members are mangled.
-/
def Block.realName (b : Block) (i : Nat) : Name :=
  let m := b.members[i]!
  if m.isProp then shadowName m.name else m.name

/-- Does this member exist in the shadow only?  See `GhostInfo`. -/
def Block.isGhost (b : Block) (i : Nat) : Bool := b.members[i]!.ghost?.isSome

/-- Does any member? -/
def Block.hasGhost (b : Block) : Bool := b.members.any (·.ghost?.isSome)

/--
Member `j`'s type as the real world states it, at the block's parameters and
that member's own indices: the member itself, or, for a ghost, the type it
stands for.
-/
def Block.realTypeAt (b : Block) (j : Nat) (params idxs : Array Expr) : Expr :=
  b.userTargets[j]!.beta (params ++ idxs)

/--
The indices in a type of the form `X_j params idxs`.  A ghost's are the copied
type's, which start after *its* parameters and not after the block's.
-/
def Block.memberIdxs (b : Block) (j : Nat) (ty : Expr) : Array Expr :=
  let args := ty.getAppArgs
  match b.members[j]!.ghost? with
  | some g => args.extract g.numParams args.size
  | none   => args.extract b.numParams args.size

/--
The universe of `X_i`'s motive: `Prop` for a `Prop` member, the member's SCC
parameter otherwise.  Members of one SCC must share a parameter, because the
native recursor of an SCC has a single elimination universe -- and they are
universe-homogeneous anyway.
-/
def Block.motiveLevel (b : Block) (i : Nat) : Level :=
  match b.sccOf[i]! with
  | none   => .zero
  | some s => .param b.sccLevel[s]!

def Block.ownLevels (b : Block) : List Level := b.levelParams.map .param

/--
Constructor `c` as the real world writes it, at the block's parameters and the
constructor's own fields.  A ghost's constructors are the copied type's, taken
at that type's parameters -- which is well-typed exactly because the copy's
fields were the original's with nothing but ghosts and members rewritten into
them.
-/
def Block.userCtorApp (b : Block) (c : CtorInfo) (params fields : Array Expr) : Expr :=
  match b.members[c.owner]!.ghost? with
  | none   => mkAppN (mkConst c.name b.ownLevels) (params ++ fields)
  | some g =>
    let q := (b.members[c.owner]!.ctors.findIdx? (·.name == c.name)).getD 0
    let oparams := (b.realTypeAt c.owner params #[]).getAppArgs
    mkAppN (mkConst g.ctors[q]! g.levels) (oparams ++ fields)

/--
The native recursor member `i`'s component eliminates with, the levels it is
instantiated at, and the parameters it takes.  A ghost has none of its own, so
it borrows the copied type's -- which is the whole point of being one.

A ghost the kernel denested borrows nothing: the kernel wrote it a recursor of
its own, over the component it belongs to, and only that one recurses back into
the component's members.  `List.rec` would offer an induction hypothesis for the
tail and none for the head.
-/
def Block.memberRecOf (b : Block) (i : Nat) (params : Array Expr) :
    Name × List Level × Array Expr :=
  match b.members[i]!.ghost? with
  | none   => (b.members[i]!.name ++ `rec, b.ownLevels, params)
  | some { nativeRec? := some r, .. } => (r, b.ownLevels, params)
  | some g => (g.head ++ `rec, g.levels, (b.realTypeAt i params #[]).getAppArgs)

@[inherit_doc Block.memberRecOf]
def Block.memberCasesOf (b : Block) (i : Nat) (params : Array Expr) :
    Name × List Level × Array Expr :=
  match b.members[i]!.ghost? with
  | none   => (b.members[i]!.name ++ `casesOn, b.ownLevels, params)
  | some g => (g.head ++ `casesOn, g.levels, (b.realTypeAt i params #[]).getAppArgs)

/-- Every generated recursor carries one extra universe parameter per data SCC,
ahead of the block's own parameters, as Lean puts elimination universes first. -/
def Block.recLevelParams (b : Block) : List Name := b.sccLevel.toList ++ b.levelParams

def Block.recLevels (b : Block) : List Level := b.recLevelParams.map .param

/--
The block-wide recursor: motives and minor premises for *every* member of the
block.  Data members already have a native `X.rec`, whose motives range over
their own SCC only, so the block-wide one needs a name of its own.  A `Prop`
member has no native recursor under its user-facing name, so it additionally
answers to `X.rec`.

A ghost is not declared at all, so its cannot be named after it.  It takes the
name the recursor over a type the *kernel* denested would have taken -- the
`X.mutualRec_1` that sits beside `X.mutualRec`.  For a ghost the kernel really
did denest, that *is* the name: `X` is its component's first declared member and
the index is the one the kernel gave `X.rec_1`, so the pair reads as it would in
a block with no `Prop` member.  For a ghost of its own, there is no component to
name it after and nothing occupying the name either -- the kernel denested
nothing for that component -- so it hangs off the block's first member.
-/
def Block.recName (b : Block) (i : Nat) : Name :=
  if !b.isGhost i then b.members[i]!.name ++ `mutualRec
  else
    let base? := do
      let s ← b.sccOf[i]!
      let j ← b.sccs[s]!.find? (!b.isGhost ·)
      return (b.members[j]!.name, (b.sccs[s]!.filter b.isGhost).idxOf i)
    let (root, k) := base?.getD
      (b.members[0]!.name,
        (Array.range i).countP fun j => b.isGhost j && (b.sccOf[j]!.all (b.sccs[·]!.all b.isGhost)))
    root ++ `mutualRec |>.appendIndexAfter (k + 1)

/-! ## Moving between the three "worlds"

During elaboration the members are free variables.  Emitting a declaration
means replacing those free variables by constants: by the shadow names, or by
the names the members are declared under (which for a data member is the
user-facing name).  The substitution has to happen underneath the parameter
telescope, because a member free variable stands for the member applied to the
section variables.
-/

def Block.substIn (b : Block) (targets vars : Array Expr) (body : Expr) : MetaM Expr := do
  let mut m : ExprMap Expr := {}
  for h : i in *...b.memberFVars.size do
    m := m.insert b.memberFVars[i] (targets[i]!.beta vars)
  let body := body.replace fun e =>
    if !e.isFVar then none else m[e]?
  -- a ghost's replacement is a lambda, so substituting it leaves the
  -- applications it stood in for as redexes
  if b.hasGhost then Core.betaReduce body else return body

@[inherit_doc Block.substIn]
private def Block.substMembers (b : Block) (targets : Array Expr) (ctorType : Expr) :
    MetaM Expr :=
  forallBoundedTelescope ctorType b.numParams fun params body => do
    mkForallFVars params (← b.substIn targets (params.extract 0 b.numVars) body)

/-- Substitute the shadow names of all members.  A ghost has a shadow like any
other member; it is only the real world it is missing from. -/
def Block.toShadow (b : Block) (e : Expr) : MetaM Expr :=
  b.substMembers (b.members.map fun m => mkConst (shadowName m.name) b.ownLevels) e

/-- Substitute what the real world calls each member: its own name, or, for a
ghost, the type it stands for. -/
def Block.toUser (b : Block) (e : Expr) : MetaM Expr :=
  b.substMembers b.userTargets e

/--
What `toUser` substitutes, worked out once, when the block is analysed.

A ghost's stand-in is stated in the writer's terms and so mentions the block's
members, which have to be substituted into it in turn.  One pass is enough:
being in the writer's terms is also why it never mentions another copy.
-/
private def Block.computeUserTargets (b : Block) : MetaM (Array Expr) := do
  let mut targets : Array Expr := b.members.map fun m => mkConst m.name b.ownLevels
  for h : i in *...b.members.size do
    if let some g := b.members[i].ghost? then
      targets := targets.set! i <| ←
        lambdaBoundedTelescope g.value b.numParams fun ps body => do
          mkLambdaFVars ps (← b.substIn targets (ps.extract 0 b.numVars) body)
  return targets

/-! ## Small helpers -/

/-- Overwrite the binder annotations of the first `bis.size` `∀`-binders. -/
private partial def forceBinderInfos (e : Expr) (bis : Array BinderInfo) (i : Nat := 0) : Expr :=
  if h : i < bis.size then
    match e with
    | .forallE n d b _ => .forallE n d (forceBinderInfos b bis (i + 1)) bis[i]
    | _ => e
  else e

/-- Replace the resulting `Sort _` of an arity by `Prop`. -/
private partial def resultToProp : Expr → Expr
  | .forallE n d b bi => .forallE n d (resultToProp b) bi
  | _ => mkSort .zero

/--
Add a plain safe definition and hand it to the code generator.  `logErrors :=
false` makes the compiler mark a declaration `noncomputable` rather than report
an error.

`compile := false` leaves code generation to someone else, and is how the data
members' recursors are added: their bodies are recursor applications and so are
not compilable as written, and the implementations emitted afterwards supply
their code instead.
-/
def addDef (name : Name) (levelParams : List Name) (type value : Expr)
    (hints : ReducibilityHints := .regular 0) (compile := true) : MetaM Unit := do
  let decl := Declaration.defnDecl { name, levelParams, type, value, hints, safety := .safe }
  addDecl decl
  if compile then
    compileDecl decl (logErrors := false)

/--
Run `act`, and if it throws, wind the environment back and carry on without it.

Several of the constructions this library makes are optional: a recursor over a
whole block, a bridge back to the original nesting types, an extra recursor the
`induction` tactic can drive.  The block is emitted either way -- what a failure
costs is what sits on top of it -- so none of them may take the declaration down
with it.  What a failure must not leave behind is half of itself, since the
plain names are exactly the ones whatever runs instead will want.  So the
environment goes back to where it was and the reason goes to the trace, which
`set_option trace.Mumi true` shows.

`none` says the attempt did not go through.
-/
def attempt? {m : Type → Type} [Monad m] [MonadEnv m] [MonadExcept Exception m]
    [MonadTrace m] [MonadRef m] [AddMessageContext m] [MonadOptions m] {α}
    (cls : Name) (what : MessageData) (act : m α) : m (Option α) := do
  let env ← getEnv
  try
    return some (← act)
  catch e =>
    setEnv env
    Lean.trace cls fun _ => m!"{what}: {e.toMessageData}"
    return none

/--
`attempt?` for a construction whose result is nothing but whether it went
through.
-/
def attempted {m : Type → Type} [Monad m] [MonadEnv m] [MonadExcept Exception m]
    [MonadTrace m] [MonadRef m] [AddMessageContext m] [MonadOptions m]
    (cls : Name) (what : MessageData) (act : m Unit) : m Bool :=
  Option.isSome <$> attempt? cls what act

/--
Can the `induction` tactic supply every argument of `n` by itself?

It builds the motive out of the goal, reads the targets off the term being
inducted on, and turns the explicit remainder into goals.  Anything else
implicit is filled only if solving the motive solves it -- which is how a
parameter like `List.rec`'s `{α}` gets filled, since it appears in the motive's
own type.

The binder that is not filled is a *second* motive, which the recursor over a
whole block has one of per member.  `induction` would leave it as a
metavariable, and the tactic reports that as a stuck instance problem in the
first branch rather than as anything to do with the eliminator, so such a
recursor is left `using`-only -- as Lean leaves the recursor of any mutual or
nested inductive.
-/
def elimIsSelfContained (n : Name) : MetaM Bool := do
  let info ← getElimInfo n
  forallTelescopeReducing info.elimType fun xs _ => do
    let motiveTy ← inferType xs[info.motivePos]!
    for h : i in *...xs.size do
      if i == info.motivePos || info.targetsPos.contains i then continue
      let d ← xs[i].fvarId!.getDecl
      if d.binderInfo.isExplicit || d.binderInfo == .instImplicit then continue
      unless ← dependsOn motiveTy d.fvarId do
        return false
    return true

/--
Tag a recursor `@[elab_as_elim]`, as Lean's own recursors are.  Without it an
application is elaborated left to right and the motive is whatever unification
happens to pin down from the expected type; with it the motive is generalised
from the expected type over the major premises first, so that
`Ctx.rec .. Γ : C Γ` elaborates its minors at the general statement rather than
at the one instance the goal mentions.

Two things have to hold first.  Every argument the conclusion applies the motive
to must be a local, because those are the targets the expected type gets
abstracted over; a predicate motive of an induction-inductive block takes the
*value* the data motive computed, which is not one, and tagging it would turn
applications that elaborate today into "invalid motive".  And
`getElabElimInfo` -- the check the attribute itself runs -- has to accept it.

A recursor that fails either keeps working and merely elaborates left to right,
which is a better outcome than refusing the block; `trace.Mumi` says which.

One that `elimIsSelfContained` accepts is registered as the `induction` tactic's
default eliminator for the member as well.  Without that, `induction` reaches
for the recursor of whatever the member unfolds to and reports the pre-block --
`the induction tactic does not support the type Ctx._pre` -- which names a
declaration the writer never wrote.  `induction := false` registers it for
`cases` instead, which is what a hypothesis-free eliminator is for.
-/
def markElabAsElim (n : Name) (induction := true) : MetaM Unit := do
  let simple ← forallTelescopeReducing (← getConstInfo n).type fun _ concl =>
    pure (concl.getAppFn.isFVar && concl.getAppArgs.all (·.isFVar))
  unless simple do
    trace[Mumi] "`{n}` is not an eliminator: its motive is applied to a computed value"
    return
  try
    discard <| Lean.Elab.Term.getElabElimInfo n
    Lean.Elab.Term.elabAsElim.setTag n
  catch e =>
    trace[Mumi] "`{n}` does not take `@[elab_as_elim]`: {e.toMessageData}"
  try
    if ← elimIsSelfContained n then
      addCustomEliminator n .global (induction := induction)
  catch e =>
    let what := if induction then "induction" else "cases"
    trace[Mumi] "`{n}` does not take `@[{what}_eliminator]`: {e.toMessageData}"

/--
Add an inductive declaration and everything Lean normally builds alongside one.
This mirrors `Lean.Elab.Command.elabInductiveViews`: compile first (`sizeOf`
and friends depend on it), then the per-member constructions, then `brecOn` in
a second pass, then the block-wide ones.  `brecOn` in particular is what
structural recursion and the equation compiler need, so without it a `match`
on a member would not elaborate.
-/
def addInd (levelParams : List Name) (numParams : Nat) (indTypes : Array InductiveType)
    (isClass : Bool := false) : MetaM Unit := do
  let decl := Declaration.inductDecl levelParams numParams indTypes.toList false
  addDecl decl
  let names := indTypes.map (·.name)
  -- a nested occurrence is denested by the kernel, which declares a type for it
  -- and a recursor `X.rec_k` with the major premise there.  The kernel knows
  -- about those, but the environment the elaborator reads does not until it is
  -- told, one by one until there are no more -- the kernel is the only record of
  -- how many there were
  for name in names do
    let mut k := 1
    repeat
      let auxRec := name ++ `rec |>.appendIndexAfter k
      let some info := (← getEnv).toKernelEnv.find? auxRec | break
      let res ← (← getEnv).addConstAsync auxRec .recursor
      res.commitConst res.asyncEnv (info? := info)
      res.commitCheckEnv res.asyncEnv
      setEnv res.mainEnv
      k := k + 1
  Lean.compileDecls names
  let env ← getEnv
  let hasEq   := env.contains ``Eq
  let hasHEq  := env.contains ``HEq
  let hasUnit := env.contains ``PUnit
  let hasProd := env.contains ``Prod
  let hasNat  := env.contains ``Nat
  for n in names do
    -- `mkRecOn` reuses `casesOn` where it can, so build that first
    if hasUnit then mkCasesOn n
    mkRecOn n
    if hasNat then mkCtorIdx n
    if hasNat then mkCtorElim n
    if hasUnit && hasEq && hasHEq then mkNoConfusion n
    if hasUnit && hasProd then mkBelow n
  for n in names do
    if hasUnit && hasProd then mkBRecOn n
  unless isClass do
    -- these are generated for the whole block from its first member
    mkSizeOfInstances names[0]!
    IndPredBelow.mkBelow names[0]!
    for n in names do
      mkInjectiveTheorems n

/-! ## An eliminator with one motive -/

/--
Walk the minors of a recursion whose other motives have been discharged,
keeping the ones that conclude at the motive `kept`, dropping the rest, and
handing the continuation the binders that survived alongside the arguments the
original recursor is to be applied to.

`mots`/`motVals` are the recursion's motives and what each is being replaced
by, and `others` the motives being discharged.  A minor's type can mention both
the motives and the minors before it -- that is what makes a recursion over a
whole block one recursion -- so each is put across under everything before it.

Within a surviving minor, a binder whose type mentions a motive that is going is
an induction hypothesis about a member the caller will learn nothing about, and
goes with it.  `forCases` counts the kept motive among those, which is what
turns the recursion into a case split: a minor concludes at the motive applied
to the constructor, which mentions the fields and never the hypotheses, so
dropping them all leaves every minor saying what it said.
-/
private partial def soloMinors {α} [Inhabited α] (others mots motVals mins : Array Expr)
    (kept : Expr) (forCases : Bool) (q : Nat) (newMins minVals : Array Expr)
    (k : Array Expr → Array Expr → MetaM α) : MetaM α := do
  if h : q < mins.size then
    let orig := mins[q]
    let origTy ← inferType orig
    let isGone (id : FVarId) :=
      others.any (·.fvarId! == id) || (forCases && kept.fvarId! == id)
    -- read off before the substitution: what it leaves at the conclusion's head
    -- is no longer a motive, and a hypothesis at a discharged motive no longer
    -- mentions one
    let atKept ← forallTelescope origTy fun _ c => pure (c.getAppFn == kept)
    let drop ← forallTelescope origTy fun as _ =>
      as.mapM fun a => return (← inferType a).hasAnyFVar isGone
    let keptOf (as : Array Expr) : Array Expr :=
      (as.zip drop).filterMap fun (a, d) => if d then none else some a
    let ty ← Core.betaReduce (origTy.replaceFVars (mots ++ mins.extract 0 q) (motVals ++ minVals))
    if atKept then
      -- the minors of the members that go carry the names the recursion over
      -- the whole block had to disambiguate them into, so each surviving one is
      -- renamed after the constructor it is for: `induction ... with | snoc`
      let ctor? ← forallTelescope origTy fun _ c =>
        pure (c.getAppArgs.back?.bind (·.getAppFn.constName?))
      let name ← match ctor? with
        | some (.str _ s) => pure (Name.mkSimple s)
        | _               => orig.fvarId!.getUserName
      let rTy ← forallTelescope ty fun as c => mkForallFVars (keptOf as) c
      withLocalDeclD name rTy fun nm => do
        let val ← forallTelescope ty fun as _ => mkLambdaFVars as (mkAppN nm (keptOf as))
        soloMinors others mots motVals mins kept forCases (q + 1)
          (newMins.push nm) (minVals.push val) k
    else
      let val ← forallTelescope ty fun as c => do
        mkLambdaFVars as (mkConst ``PUnit.unit [← getLevel c])
      soloMinors others mots motVals mins kept forCases (q + 1) newMins (minVals.push val) k
  else
    k newMins minVals

/--
An eliminator with one motive, for a member whose siblings' motives can be
filled in with nothing.

The recursion over the whole block asks for a motive at every member, which is
what makes it strong -- and what stops `induction` from driving it, since
nothing determines the motives the goal does not mention.  Discharge every
motive but one and what comes out is the shape `induction` expects, at the cost
of the hypotheses at the discharged members.

Those hypotheses are only worth their cost in two arrangements.  A block with
one data member and any number of propositions gives the data member a recursor
into any sort; a block with one proposition gives that one a recursor into
`Prop`.  Both are as strong as a one-motive statement can be: a motive at a
single member cannot mention what the recursion computed at another, so what is
dropped is what it could not have used.

Any other arrangement would discharge a second *data* motive, which does lose
hypotheses a caller could have wanted, so `src` is left as the only recursor
there.  Nothing is emitted then, and nothing is reported: this is an extra, and
a block that cannot have one is not thereby worse off.

`evenIfWeaker` asks for it anyway, whatever the arrangement costs.  What makes
the refusal above safe is that the member is a real inductive, so a caller who
writes `induction` and gets nothing gets mainline's own refusal -- "does not
support the type, because it is mutually inductive" -- and goes looking for the
recursor.  A member of an induction-inductive block is a `def`, and there is no
such refusal to fall back on: `induction` unfolds it to the subtype it is
encoded as and offers a case split on `Subtype.mk`, binding a pre-term and a
proof of its well-formedness.  Weighed against that, a one-motive principle
that has lost a sibling's hypotheses is the better default by some way, and the
recursion over the whole block is a `using` away.

`forCases` asks instead for the eliminator a case split needs, which is the
same one with every minor's hypotheses gone.  A case split uses no hypothesis at
any member, so there is none to weigh and no arrangement to refuse: every other
motive is discharged whatever kind it is, and a block whose recursion already
had one motive still has hypotheses worth dropping out of it.  That leaves
`cases` working where `induction` does not, which is where mainline leaves them
too -- a mutual inductive gets a `casesOn` at one motive and is refused by
`induction` outright.

Emitting one at all is the point.  `cases` on a member of an erased block
reaches for whatever the member unfolds to, and so asks for `Subtype.mk` -- the
encoding's constructor, under a name the writer never wrote and cannot usefully
name the fields of, since what it binds is a pre-term and a proof rather than
the constructor's arguments.  A `Prop` member fares no better for being a real
inductive underneath: splitting one whose data index is a variable makes the
tactic solve `Γ.1 = Ctx._pre.nil`, which is the encoding again and which it
cannot do.  Registering one of these instead leaves the block's own constructors
as the cases, and the unification that would have gone through the subtype does
not arise.

`elimLevels` are the universe parameters `src` carries for its data motives --
one per data SCC on this route, one overall on the induction-inductive one.
-/
def addSoloElim (nParams : Nat) (elimLevels : Array Name) (keepIsProp : Bool)
    (src soloName : Name) (forCases : Bool) (evenIfWeaker := false) : MetaM Unit := do
  let some info := (← getEnv).find? src | return
  let recCst := mkConst src (info.levelParams.map Level.param)
  forallBoundedTelescope info.type nParams fun ps rest =>
  forallTelescope rest fun xs concl => do
    -- the motives lead, and are the binders that take a member to a sort
    let mut nMot := 0
    for x in xs do
      unless ← forallTelescope (← inferType x) fun _ c => pure c.isSort do break
      nMot := nMot + 1
    let mots := xs.extract 0 nMot
    -- a recursion at one motive is nothing to cut down, though it still has
    -- hypotheses a case split wants gone
    if nMot ≤ 1 && !forCases then return
    let some kq := mots.findIdx? (· == concl.getAppFn) | return
    let isProp ← mots.mapM fun m => do
      forallTelescope (← inferType m) fun _ c =>
        pure (match c with | .sort u => u.isZero | _ => false)
    -- every other motive has to be of the other kind, or discharging it would
    -- cost a hypothesis worth having -- which a case split has not got, and
    -- which a block with no refusal to fall back on would rather pay
    unless forCases || evenIfWeaker ||
        (Array.range nMot).all fun q => q == kq || isProp[q]! != keepIsProp do
      return
    -- whether what comes out is itself a proof, which is not the same question as
    -- whether the member is a `Prop`: a subsingleton's recursor eliminates into
    -- any sort, and the eliminator built from it has to go on carrying the
    -- universe it does that in.  Where it *is* a proof, the sorts the data motives
    -- were polymorphic in have nothing left to range over, and are pinned rather
    -- than carried
    let intoProp := keepIsProp && isProp[kq]!
    let pinned := if intoProp then elimLevels.filter (info.levelParams.contains ·) else #[]
    let pin (e : Expr) : Expr :=
      e.instantiateLevelParams pinned.toList (pinned.toList.map fun _ => Level.one)
    let outLvls := info.levelParams.filter (!pinned.contains ·)
    let others := (Array.range nMot).filterMap fun q => if q == kq then none else some mots[q]!
    let isOther (id : FVarId) := others.any (·.fvarId! == id)
    -- a discharged motive is filled in with the one-element type at its own
    -- sort, which is the only thing to fill a *data* motive in with while the
    -- sort it lands in is still a parameter the kept motive needs
    let triv (ty : Expr) : MetaM Expr :=
      forallTelescope ty fun as c => mkLambdaFVars as (mkConst ``PUnit [c.sortLevel!])
    let subst (e : Expr) (vals : Array Expr) : MetaM Expr :=
      Core.betaReduce (e.replaceFVars (mots.extract 0 vals.size) vals)
    -- the discharged motives before the kept one, so that its own type can be
    -- put across before its binders are counted
    let mut motVals : Array Expr := #[]
    for q in *...kq do
      motVals := motVals.push (← triv (← subst (← inferType mots[q]!) motVals))
    let keptTy ← inferType mots[kq]!
    let drop ← forallTelescope keptTy fun as _ =>
      as.mapM fun a => return (← inferType a).hasAnyFVar isOther
    let keptOf (as : Array Expr) : Array Expr :=
      (as.zip drop).filterMap fun (a, d) => if d then none else some a
    let keptTy' ← subst keptTy motVals
    let dTy ← forallTelescope keptTy' fun as c => mkForallFVars (keptOf as) c
    let before := motVals
    withLocalDecl `motive .implicit dTy fun d => do
      let mut motVals := before.push (←
        forallTelescope keptTy' fun as _ => mkLambdaFVars as (mkAppN d (keptOf as)))
      for q in (kq + 1)...nMot do
        motVals := motVals.push (← triv (← subst (← inferType mots[q]!) motVals))
      -- a minor is a binder concluding at a motive; what follows them is the
      -- indices and the major, which pass through untouched
      let rest' := xs.extract nMot xs.size
      let mut nMin := 0
      for x in rest' do
        unless ← forallTelescope (← inferType x) fun _ c => pure (mots.contains c.getAppFn) do
          break
        nMin := nMin + 1
      let mins := rest'.extract 0 nMin
      let tgts := rest'.extract nMin rest'.size
      let (ty, val) ← soloMinors others mots motVals mins mots[kq]! forCases 0 #[] #[]
        fun newMins minVals => do
          let binders := ps ++ #[d] ++ newMins ++ tgts
          let ty ← mkForallFVars binders
            (← Core.betaReduce (concl.replaceFVars (mots ++ mins) (motVals ++ minVals)))
          let val ← mkLambdaFVars binders
            (mkAppN recCst (ps ++ motVals ++ minVals ++ tgts))
          return ((ty : Expr), (val : Expr))
      if intoProp then
        addDecl (.thmDecl
          { name := soloName, levelParams := outLvls, type := pin ty, value := pin val })
      else
        addDef soloName outLvls (pin ty) (pin val)
      markElabAsElim soloName (induction := !forCases)

/--
`Nonempty ((w : α) ×' β w)`: a `Prop` that still remembers a data witness, and
whose eliminator lands in `Prop`, which is all the minor premises of a `Prop`
member's recursor ever need.
-/
private def mkNESig (α β : Expr) : MetaM Expr := do
  mkAppM ``Nonempty #[← mkAppOptM ``PSigma #[some α, some β]]

/--
The levels to instantiate the eliminator `elimName` -- a recursor or a
`casesOn` -- at, given that its motives live at `elim` and the block's own
levels are `own`.  A small-eliminating `Prop` has no separate elimination
universe, so the extra level is only prepended when the eliminator actually has
one.
-/
private def elimLevelsFor (elimName : Name) (elim : Level) (own : List Level) :
    MetaM (List Level) := do
  let info ← getConstInfo elimName
  if info.levelParams.length == own.length then
    return own
  else
    return elim :: own

/-! ## Analysis

Deciding *whether* a block can be lowered, and rejecting the shapes the
lowering cannot express.
-/

/--
Condensation of the data-only dependency graph, in topological order
(dependencies first).  Returns the components and, for each member, its
component index (`none` for a `Prop` member).

A `Prop` member is a sink: the shadow declares every member of the block before
any data member is, and a data member's field at a `Prop` sibling is a field at
that shadow, already a constant.  So a path that leaves the data members is a
path that does not come back, and closing over one would group components that
can perfectly well be declared one after another.

`n` is the number of members of one `mutual` block, so the cubic reachability
closure is not worth optimising.
-/
def computeSCCs (n : Nat) (isData : Array Bool) (edges : Array (Array Bool)) :
    Array (Array Nat) × Array (Option Nat) := Id.run do
  -- transitive closure, relaying through the data members alone
  let mut r := edges
  for k in *...n do
    if !isData[k]! then continue
    for i in *...n do
      if r[i]![k]! then
        for j in *...n do
          if r[k]![j]! && !r[i]![j]! then
            r := r.set! i (r[i]!.set! j true)
  -- raw components: `i ~ j` iff mutually reachable
  let mut compOf : Array (Option Nat) := rep n none
  let mut comps : Array (Array Nat) := #[]
  for i in *...n do
    if isData[i]! && compOf[i]!.isNone then
      let mut c := #[]
      for j in *...n do
        if isData[j]! && compOf[j]!.isNone && (j == i || (r[i]![j]! && r[j]![i]!)) then
          c := c.push j
      for j in c do
        compOf := compOf.set! j (some comps.size)
      comps := comps.push c
  -- topologically order the condensation: a component may be emitted once
  -- every component it depends on has been emitted
  let m := comps.size
  let mut emitted : Array Bool := rep m false
  let mut order : Array Nat := #[]
  for _pass in *...m do
    if order.size == m then
      break
    for a in *...m do
      if !emitted[a]! then
        let mut ok := true
        for i in comps[a]! do
          for j in *...n do
            if r[i]![j]! then
              if let some bc := compOf[j]! then
                if bc != a && !emitted[bc]! then
                  ok := false
        if ok then
          emitted := emitted.set! a true
          order := order.push a
  -- renumber into topological order
  let mut newOf : Array Nat := rep m 0
  for pos in *...order.size do
    newOf := newOf.set! order[pos]! pos
  let sccs := order.map (comps[·]!)
  let sccOf := compOf.map (fun o => o.map (newOf[·]!))
  return (sccs, sccOf)

/-- Pick `n` level parameter names not clashing with `avoid`. -/
def freshLevelNames (avoid : List Name) (n : Nat) : Array Name := Id.run do
  let cands : Array Name := #[`u, `v, `w, `x, `y, `z]
  let mut used := avoid
  let mut out := #[]
  let mut next := 0
  for i in *...n do
    let mut nm := if h : i < cands.size then cands[i] else Name.mkSimple s!"u_{i}"
    while used.contains nm do
      next := next + 1
      nm := Name.mkSimple s!"u_{next}"
    used := nm :: used
    out := out.push nm
  return out

/-- Does `e` mention any of the block's members? -/
private def mentionsMember (fvars : Array Expr) (e : Expr) : Bool :=
  fvars.any fun f => e.containsFVar f.fvarId!

/--
What a constructor field turns out to be.
-/
private inductive FieldKind where
  /-- Recurses into a member, or mentions none at all: `none` for the latter. -/
  | plain (rf : Option RecField)
  /-- Mentions members only from inside another type constructor's parameters,
  as `List B` and `Tree S` do.  `denest` leaves such an occurrence alone and
  hands it to the kernel, which either finds the type closed already -- `B` is
  declared before `A` -- or denests it itself.  Either way there is nothing for
  the lowering to recurse into, but the emission order still has to respect the
  members the occurrence names. -/
  | inert (deps : Array Nat) (why : MessageData)

/--
Classify one constructor field.

Accepts a non-recursive field (no member occurrence at all), a field of the
form `∀ ys, X_j params idxs` where neither the `ys` domains nor the `idxs`
mention any member, or a *nested* occurrence such as `List (X_j ...)`.  The last
of those is only accepted provisionally: `analyze` checks below that the block
is one whose nested occurrences reach the kernel at all.
-/
private def analyzeField (inp : Input) (fieldTy : Expr) (ctor : Name) (k : Nat) :
    MetaM FieldKind := do
  if !mentionsMember inp.memberFVars fieldTy then
    return .plain none
  forallTelescope fieldTy fun ys body => do
    for y in ys do
      if mentionsMember inp.memberFVars (← inferType y) then
        throwError m!"Unsupported constructor field in a multiuniverse block: field \
          {k + 1} of `{ctor}` takes an argument whose type mentions a member of the block"
          ++ .note "This is not a strictly positive occurrence, so the lowering has nothing \
            to translate it to"
    let some j := inp.memberFVars.findIdx? (· == body.getAppFn)
      | let bad := m!"Unsupported constructor field in a multiuniverse block: field \
            {k + 1} of `{ctor}` mentions a member of the block in a nested position, in the \
            type{indentExpr fieldTy}"
        -- a nested occurrence goes one of two ways: left as written, for the
        -- kernel to denest, or copied into a member of the block.  A head that
        -- is not an inductive type is out of reach of both -- there is nothing
        -- for the kernel to denest and no constructors to copy
        let head? := body.getAppFn.constName?.bind (← getEnv).find?
        unless head? matches some (.inductInfo _) do
          throwError bad ++ .note "The head of the occurrence is not an inductive type, so \
            there is nothing to denest and nothing to copy"
        let mut deps : Array Nat := #[]
        for i in *...inp.memberFVars.size do
          if body.containsFVar inp.memberFVars[i]!.fvarId! then
            deps := deps.push i
        return .inert deps (← addMessageContext <| bad
          ++ .note "A block with a `Prop` member is lowered through an all-`Prop` shadow, \
            which copies every constructor field with the members redirected -- and a \
            redirected nested occurrence is not even well-typed.  So the occurrence had to \
            become a member of the block itself, and it could not be")
    for a in body.getAppArgs do
      if mentionsMember inp.memberFVars a then
        throwError m!"Unsupported constructor field in a multiuniverse block: field \
          {k + 1} of `{ctor}` has a type that applies a member of the block to an argument \
          mentioning another one, in the type{indentExpr fieldTy}"
          ++ .note "Nested occurrences are not supported"
    return .plain (some { member := j, arity := ys.size })

/--
Reject a constructor whose *result indices* depend on a field of data-member
type.

The lowering identifies the shadow world and the real world at every index
position: the shadow constructor is applied to shadow fields, the real one to
real fields, and the two must land at the same indices.  Fields that are not
members, and fields of `Prop`-member type, are literally the same variable in
both worlds; a field of data-member type is not.

This is a defensive check.  Reaching it needs a function from a member of the
block into an index type, and there is none to be had: headers are elaborated
before any member is in scope, so no member's indices can mention another
member, and nested occurrences are rejected outright.
-/
private def checkIndices (isProp : Array Bool) (c : CtorInfo)
    (fields : Array Expr) (idxs : Array Expr) : MetaM Unit := do
  let mut bad : Array Expr := #[]
  for k in *...c.numFields do
    if let some rf := c.fields[k]! then
      if !isProp[rf.member]! then
        bad := bad.push fields[k]!
  if bad.isEmpty then return
  for idx in idxs do
    for f in bad do
      if idx.containsFVar f.fvarId! then
        throwError m!"Unsupported constructor in a multiuniverse block: `{c.name}` \
          computes a result index from a field whose type is a non-`Prop` member of the block"
          ++ .note "The lowering cannot keep the shadow block and the real one in step across \
            such an index, since the shadow's data fields carry no data"

/-- Build a `Block` from freshly elaborated inductive data, or throw. -/
def analyze (inp : Input) : MetaM Block := do
  let n := inp.memberTypes.size
  -- 1. the members' universes
  let mut levels : Array Level := #[]
  let mut isProp : Array Bool := #[]
  for i in *...n do
    let l ← forallTelescope inp.memberTypes[i]! fun _ body => do
      let .sort l := (← whnf body)
        | throwError "The type of `{inp.memberNames[i]!}` does not end in a sort:\
            {indentExpr inp.memberTypes[i]!}"
      return l
    levels := levels.push l
    isProp := isProp.push (match l.normalize with | .zero => true | _ => false)
  -- 2. the constructors, and the data-only dependency graph
  let mut members : Array MemberInfo := #[]
  let mut allCtors : Array CtorInfo := #[]
  let mut edges : Array (Array Bool) := rep n (rep n false)
  -- one entry per member an inert field names, to be checked in step 3
  let mut inert : Array (Nat × Nat × MessageData) := #[]
  for i in *...n do
    let mut ctors : Array CtorInfo := #[]
    for j in *...inp.ctorNames[i]!.size do
      let cname := inp.ctorNames[i]![j]!
      let cty := inp.ctorTypes[i]![j]!
      let (c, inerts) ← forallBoundedTelescope cty (some inp.numParams) fun _params inner =>
        forallTelescope inner fun fields result => do
          let mut fs : Array (Option RecField) := #[]
          let mut inerts : Array (Nat × Nat × MessageData) := #[]
          for k in *...fields.size do
            match ← analyzeField inp (← inferType fields[k]!) cname k with
            | .plain rf => fs := fs.push rf
            | .inert deps why =>
              fs := fs.push none
              for d in deps do inerts := inerts.push (i, d, why)
          let c : CtorInfo :=
            { name := cname, owner := i, type := cty, numFields := fields.size, fields := fs }
          let args := result.getAppArgs
          checkIndices isProp c fields (args.extract inp.numParams args.size)
          return (c, inerts)
      inert := inert ++ inerts
      if !isProp[i]! then
        for f? in c.fields do
          if let some rf := f? then
            if !isProp[rf.member]! then
              edges := edges.set! i (edges[i]!.set! rf.member true)
      ctors := ctors.push c
      allCtors := allCtors.push c
    members := members.push
      { name := inp.memberNames[i]!, type := inp.memberTypes[i]!,
        level := levels[i]!, isProp := isProp[i]!, ctors,
        ghost? := inp.memberGhost[i]?.join }
  -- an inert field recurses into nothing, but the member it names still has to
  -- exist by the time this one is declared
  for (i, d, _) in inert do
    if !isProp[i]! && !isProp[d]! then
      edges := edges.set! i (edges[i]!.set! d true)
  -- 3. condensation of the data-only graph
  let isData := isProp.map not
  let (sccs, sccOf) := computeSCCs n isData edges
  -- a ghost goes last in its component.  What the kernel is handed is the
  -- component's other members, with the ghost written out as the type it stands
  -- for, and what comes back has a motive and minor premises for each of those
  -- first and for what it denested after; keeping the block's order the same
  -- lets one list of motives serve both
  let ghostly := fun (i : Nat) => (inp.memberGhost[i]?.join).isSome
  let sccs := sccs.map fun c => c.filter (!ghostly ·) ++ c.filter ghostly
  -- `denest` copies every nested occurrence of a block with a `Prop` member, so
  -- one that survived to here is one it could not copy
  if isProp.any id then
    for (_, _, why) in inert do
      throwError why
  let sccLevel := freshLevelNames inp.levelParams sccs.size
  let b : Block :=
    { levelParams := inp.levelParams, numVars := inp.numVars, numParams := inp.numParams,
      memberFVars := inp.memberFVars, members, allCtors,
      sccs, sccOf, sccLevel, hasProp := isProp.any id, isClass := inp.isClass,
      userTargets := #[] }
  return { b with userTargets := ← b.computeUserTargets }

/-- Is every member at the same universe?  Then the block is an ordinary
`mutual` block and the lowering should not touch it. -/
def Block.isHomogeneous (b : Block) : Bool :=
  b.members.all fun m => m.level.normalize == b.members[0]!.level.normalize

/-! ## The lowering

Emission order; each step only mentions constants emitted by earlier steps.

0. if the block is homogeneous, emit it natively and stop;
1. `X_i._shadow`   -- the all-`Prop` shadow of the whole block;
2. `X_i` for `Prop` members -- reducible abbreviations for their shadows;
3. `X_i` for data members   -- honest inductives, one SCC at a time, in
                              topological order;
4. `X_i._squash`   -- `X_i → X_i._shadow`, one SCC at a time;
5. `X_i.c` for `Prop` members -- the user-facing constructors;
6. `X_i.mutualRec` for `Prop` members -- from the shadow recursor;
7. `X_i.mutualRec` for data members, in SCC order -- from the native recursors.

Step 6 only mentions data *constructors*, never data recursors, so 6 and 7 do
not form a cycle.
-/

/-- Walk `n` `∀`-binders of `ty`, building an argument for each via `mk` and
instantiating as we go, so later domains see the earlier arguments. -/
private def buildArgs (ty : Expr) (n : Nat) (mk : Nat → Expr → MetaM Expr) :
    MetaM (Array Expr) := do
  let mut ty := ty
  let mut args := #[]
  for i in *...n do
    let ty' ← whnf ty
    let .forallE _ d body _ := ty'
      | throwError "(internal) multiuniverse lowering: expected {n} arguments in\
          {indentExpr ty}"
    let a ← mk i d
    args := args.push a
    ty := body.instantiate1 a
  return args

/-- The constructors of SCC `s`, as indices into `b.allCtors`, in the order the
native recursor of that SCC expects its minor premises. -/
private def sccCtorIndices (b : Block) (s : Nat) : Array Nat := Id.run do
  let mut out := #[]
  for j in b.sccs[s]! do
    for q in *...b.allCtors.size do
      if b.allCtors[q]!.owner == j then
        out := out.push q
  return out

/-- `X_i.mutualRec := X_i.rec`, for a block whose native recursor already ranges
over every member.  Keeps the generated API the same on the native path as on
the lowered one. -/
private def aliasNativeRecs (b : Block) : MetaM Unit := do
  for i in *...b.size do
    let rn := b.members[i]!.name ++ `rec
    let info ← getConstInfoRec rn
    addDef (b.recName i) info.levelParams info.type
      (mkConst rn (info.levelParams.map Level.param)) (compile := false)
    markElabAsElim (b.recName i)

/-- A homogeneous block is an ordinary `mutual` block; emit it unchanged, so
that this library's `mutual` is a strict superset of Lean's. -/
private def emitNative (b : Block) : MetaM Unit := do
  let mut indTypes : Array InductiveType := #[]
  for i in *...b.size do
    let m := b.members[i]!
    let ctors ← m.ctors.mapM fun c =>
      return ({ name := c.name, type := ← b.toUser c.type } : Constructor)
    indTypes := indTypes.push { name := m.name, type := m.type, ctors := ctors.toList }
  addInd b.levelParams b.numParams indTypes b.isClass
  aliasNativeRecs b

/-- The all-`Prop` shadow.  Only the resulting sorts change: constructor fields
are copied verbatim, with member occurrences redirected to the shadow, which is
legal because a `Prop`-valued inductive imposes no constraint on its fields. -/
private def emitShadow (b : Block) : MetaM Unit := do
  let mut indTypes : Array InductiveType := #[]
  for i in *...b.size do
    let m := b.members[i]!
    let sn := shadowName m.name
    let ctors ← m.ctors.mapM fun c =>
      return ({ name := reroot m.name sn c.name, type := ← b.toShadow c.type } : Constructor)
    indTypes := indTypes.push { name := sn, type := resultToProp m.type, ctors := ctors.toList }
  addInd b.levelParams b.numParams indTypes

/-- A `Prop` member *is* its shadow -- the shadow only squashes data members --
so its user-facing name is a reducible abbreviation.  These come before the
data members, whose constructors mention them. -/
private def emitPropAliases (b : Block) : MetaM Unit := do
  for i in *...b.size do
    let m := b.members[i]!
    if m.isProp then
      addDef m.name b.levelParams m.type (mkConst (b.realName i) b.ownLevels) .abbrev
      setReducibleAttribute m.name

/--
One SCC of the data-only dependency graph, declared under the users' own names.
Its members are necessarily at the same universe (an edge `i → j` forces
`l_j ≤ l_i`, so a cycle forces equality), hence this is an ordinary,
homogeneous mutual block.  Fields of `Prop`-member type refer to the aliases,
which the kernel unfolds to the shadow; being outside the block, they impose no
positivity obligation.

A ghost is passed over: the real world says nothing about it, and a component
of nothing but ghosts declares nothing at all.
-/
private def emitDataSCC (b : Block) (s : Nat) : MetaM Unit := do
  let mut indTypes : Array InductiveType := #[]
  for i in b.sccs[s]! do
    if b.isGhost i then continue
    let m := b.members[i]!
    let ctors ← m.ctors.mapM fun c =>
      return ({ name := c.name, type := ← b.toUser c.type } : Constructor)
    indTypes := indTypes.push { name := m.name, type := m.type, ctors := ctors.toList }
  if indTypes.isEmpty then return
  addInd b.levelParams b.numParams indTypes b.isClass

/-- `X_j._squash params idxs v`, lifted pointwise through any leading `∀`s of
`v`'s type. -/
private def squashApply (b : Block) (params : Array Expr) (j : Nat) (v : Expr) :
    MetaM Expr := do
  forallTelescope (← inferType v) fun ys body => do
    let sq := mkConst (squashName b.members[j]!.name) b.ownLevels
    mkLambdaFVars ys (mkAppN sq (params ++ b.memberIdxs j body ++ #[mkAppN v ys]))

/-- Minor premise for `X_i._squash`: rebuild the constructor in the shadow. -/
private def mkSquashMinor (b : Block) (s : Nat) (params : Array Expr) (c : CtorInfo)
    (minorTy : Expr) : MetaM Expr := do
  forallTelescope minorTy fun args _ => do
    let fields := args.extract 0 c.numFields
    let ihs := args.extract c.numFields args.size
    let mut gs := #[]
    let mut p := 0
    for k in *...c.numFields do
      match c.fields[k]! with
      | none => gs := gs.push fields[k]!
      | some rf =>
        if b.members[rf.member]!.isProp then
          -- already a shadow inhabitant: `X_j` *is* `X_j._shadow`
          gs := gs.push fields[k]!
        else if b.sccOf[rf.member]! == some s then
          -- the induction hypothesis *is* the shadow image
          gs := gs.push ihs[p]!
          p := p + 1
        else
          -- an earlier SCC: its squash map is already defined
          gs := gs.push (← squashApply b params rf.member fields[k]!)
    let m := b.members[c.owner]!
    let sctor := mkConst (reroot m.name (shadowName m.name) c.name) b.ownLevels
    mkLambdaFVars args (mkAppN sctor (params ++ gs))

private def emitSquashSCC (b : Block) (s : Nat) : MetaM Unit := do
  let ctorIdx := sccCtorIndices b s
  for i in b.sccs[s]! do
    let m := b.members[i]!
    forallBoundedTelescope m.type (some b.numParams) fun params _ => do
      let shadowOf (j : Nat) (jidxs : Array Expr) : Expr :=
        mkAppN (mkConst (shadowName b.members[j]!.name) b.ownLevels) (params ++ jidxs)
      let mut motives := #[]
      for j in b.sccs[s]! do
        let aj ← instantiateForall b.members[j]!.type params
        let mot ← forallTelescope aj fun jidxs _ =>
          withLocalDeclD `t (b.realTypeAt j params jidxs) fun tv =>
            mkLambdaFVars (jidxs ++ #[tv]) (shadowOf j jidxs)
        motives := motives.push mot
      let (recName, base, rparams) := b.memberRecOf i params
      let recFn := mkConst recName (← elimLevelsFor recName .zero base)
      let ty0 ← instantiateForall (← inferType recFn) rparams
      let ty1 ← instantiateForall ty0 motives
      let minors ← buildArgs ty1 ctorIdx.size fun q minorTy =>
        mkSquashMinor b s params b.allCtors[ctorIdx[q]!]! minorTy
      let ai ← instantiateForall m.type params
      forallTelescope ai fun idxs _ =>
        withLocalDeclD `t (b.realTypeAt i params idxs) fun tv => do
          let all := params ++ idxs ++ #[tv]
          let ty ← mkForallFVars all (shadowOf i idxs)
          let val ← mkLambdaFVars all
            (mkAppN recFn (rparams ++ motives ++ minors ++ idxs ++ #[tv]))
          addDef (squashName m.name) b.levelParams ty val

/--
The `Prop` members' constructors.  The data members' constructors are the
native ones and need no help; a `Prop` member's shadow constructor wants shadow
arguments, so each data field is sent through its squash map.
-/
private def emitPropCtors (b : Block) : MetaM Unit := do
  for i in *...b.size do
    let m := b.members[i]!
    if !m.isProp then continue
    for c in m.ctors do
      let cty ← b.toUser c.type
      forallBoundedTelescope cty (some b.numParams) fun params inner =>
        forallTelescope inner fun fields _ => do
          let mut gs := #[]
          for k in *...c.numFields do
            match c.fields[k]! with
            | some rf =>
              if b.members[rf.member]!.isProp then
                gs := gs.push fields[k]!
              else
                gs := gs.push (← squashApply b params rf.member fields[k]!)
            | none => gs := gs.push fields[k]!
          let realCtor := mkConst (reroot m.name (b.realName i) c.name) b.ownLevels
          -- reuse the elaborated type verbatim, so the constructor keeps the
          -- binder annotations it would have got from `mutual`
          addDef c.name b.levelParams cty
            (← mkLambdaFVars (params ++ fields) (mkAppN realCtor (params ++ gs)))

/-! ### What the kernel denested

`Mumi.Denest` leaves a nested occurrence the kernel can take to the kernel, so
`S.t` really is stated at `Tree S`, and the type the kernel invents for `Tree S`
is declared alongside `S`.  What that costs is that the component's native
recursor ranges over more than the component's members: it has a motive for
each invented type and minor premises for its constructors.  Everything the
lowering builds out of that recursor has to offer the same.

They go at the end of their kind -- every member's motive first and then the
invented ones, every constructor of the block first and then theirs -- so a
block with nothing nested reads exactly as it did, and one with a nesting reads
as the recursor Lean writes for a `mutual` block that nests.
-/

/-- One type the kernel denested, and where it lands in the block-wide recursors. -/
structure NestSpec where
  /-- The type constructor itself: `Tree`, not `Tree S`. -/
  head       : Name
  /-- Its motive's position, at or past `b.size`. -/
  motive     : Nat
  /-- Its first minor premise's position, at or past `b.allCtors.size`. -/
  firstMinor : Nat
  /-- How many constructors it has, hence how many minor premises. -/
  numMinors  : Nat
  /-- The kernel's own recursor with the major premise at this type: `S.rec_1`
  where the component's members have `S.rec`. -/
  nativeRec  : Name
  /-- The block-wide recursor at this type, which is to `S.mutualRec` what
  `S.rec_1` is to `S.rec`. -/
  recName    : Name
  deriving Inhabited

/-- What the kernel denested, one entry per data SCC. -/
structure Nests where
  perScc     : Array (Array NestSpec)
  numMotives : Nat
  numMinors  : Nat
  deriving Inhabited

/-- Nothing was denested: every block without a nesting, and the native path. -/
def Nests.empty (n : Nat) : Nests :=
  { perScc := rep n #[], numMotives := 0, numMinors := 0 }

def Nests.forScc (ns : Nests) (s : Nat) : Array NestSpec := ns.perScc[s]?.getD #[]

/-- Which denested type a motive index past the block's own members belongs to. -/
def Nests.spec? (ns : Nests) (e : Nat) : Option NestSpec :=
  ns.perScc.findSome? fun specs => specs.findSome? fun sp =>
    if sp.motive == e then some sp else none

/-- The implementation of a block-wide recursor, and the `@[csimp]` theorem for
it.  Named as a member's are, so that a nesting's recursor and a member's are
told apart only by which of them they belong to. -/
def NestSpec.implName (sp : NestSpec) : Name := sp.recName ++ `impl

@[inherit_doc NestSpec.implName]
def NestSpec.implEqName (sp : NestSpec) : Name := sp.recName ++ `eq_impl

/-- `X_i.rec`, at its own parameters and at motive values of the caller's
choosing, with the type that is left over. -/
private def memberRecAt (b : Block) (i : Nat) (params vals : Array Expr) :
    MetaM (Expr × Expr) := do
  let (recName, base, rparams) := b.memberRecOf i params
  let recFn := mkConst recName (← elimLevelsFor recName (b.motiveLevel i) base)
  let ty ← instantiateForall (← inferType recFn) rparams
  return (recFn, ← instantiateForall ty vals)

/-- The motive values a component's native recursor is applied at, in its own
order: the block's motive for each of the component's members, then the block's
motive for each type the kernel denested for the component.

They are passed as they stand rather than eta-expanded, so that the induction
hypotheses read back off the recursor mention the motive itself.  Whoever reads
them has to recognise which motive an induction hypothesis is about, and a
`(fun t => motive_1 t) a` in a minor premise the writer will read is worse
besides. -/
private def sccMotiveVals (b : Block) (ns : Nests) (s : Nat) (motives : Array Expr) :
    Array Expr :=
  b.sccs[s]!.map (motives[·]!) ++ (ns.forScc s).map fun sp => motives[sp.motive]!

/--
Read off what the kernel denested for each component, by comparing that
component's native recursor with the component the lowering handed it.  A
recursor with more motives than its component has *declared* members has them
for types the kernel invented, and there is no other way for one to arise.

Some of those the block already has a member for: a ghost the kernel denested is
one of the block's own slots, with its own motive, minor premises and recursor,
and all it wants from here is the name of the kernel's recursor at it.  Those are
matched up by the type each stands for and the component reordered to agree with
the kernel, so that one list of motives serves the block's recursors and the
native one alike.  What is left over -- a nesting the writer wrote in a block
with no ghost in it -- becomes a `NestSpec`.

Both cannot happen at once: a ghost exists only in a block with a `Prop` member,
and there the shadow has no way to follow a nesting it has no member for.
-/
private def mkNests (b : Block) : MetaM (Block × Nests) := do
  let mut b := b
  let mut perScc : Array (Array NestSpec) := #[]
  let mut nMot := 0
  let mut nMin := 0
  for s in *...b.sccs.size do
    let i := b.sccs[s]![0]!
    let name := b.members[i]!.name
    -- a component of ghosts was never handed to the kernel, so it has nothing
    -- to report; the type a ghost stands for is one the kernel already knows
    if b.isGhost i then
      perScc := perScc.push #[]
      continue
    let info ← getConstInfoRec (name ++ `rec)
    let ghosts := b.sccs[s]!.filter b.isGhost
    let decl := b.sccs[s]!.size - ghosts.size
    -- each extra motive's major premise, as `∀ idxs, T idxs` under the
    -- component's parameters.  That is exactly how a ghost states the type it
    -- stands for, so which motive is whose is settled by comparing the two and
    -- not by their heads, which two ghosts may well share
    let (heads, ordered) ←
      forallBoundedTelescope b.members[i]!.type (some b.numParams) fun params _ => do
        let (_, ty) ← memberRecAt b i params #[]
        forallBoundedTelescope ty (some info.numMotives) fun ms _ => do
          let extra := ms.extract decl info.numMotives
          let mut heads : Array Name := #[]
          let mut ordered : Array Nat := #[]
          for m in extra do
            let (hd, majTy) ← forallTelescope (← inferType m) fun zs _ => do
              let some t := zs.back?
                | throwError "(internal) multiuniverse lowering: `{name}.rec` has a motive that \
                    takes no major premise"
              let mty ← inferType t
              let some hd := (← whnf mty).getAppFn.constName?
                | throwError "(internal) multiuniverse lowering: `{name}.rec` has a motive over \
                    something that is not a type constructor"
              return (hd, ← mkForallFVars zs.pop mty)
            heads := heads.push hd
            unless extra.size != ghosts.size do
              let mut found := none
              for g in ghosts do
                if found.isNone && !ordered.contains g then
                  let gTy ← forallTelescope (← instantiateForall b.members[g]!.type params)
                    fun idxs _ => mkForallFVars idxs (b.realTypeAt g params idxs)
                  if ← isDefEq gTy majTy then found := some g
              let some q := found
                | throwError "(internal) multiuniverse lowering: `{name}.rec` has a motive over \
                    `{hd}`, which no member of its component stands for"
              ordered := ordered.push q
          return (heads, ordered)
    let mut specs : Array NestSpec := #[]
    if heads.size == ghosts.size then
      for k in *...ordered.size do
        let nativeRec := name ++ `rec |>.appendIndexAfter (k + 1)
        discard <| getConstInfoRec nativeRec
        b := { b with members := b.members.modify ordered[k]! fun m =>
          { m with ghost? := m.ghost?.map ({ · with nativeRec? := nativeRec }) } }
      b := { b with sccs := b.sccs.set! s (b.sccs[s]!.filter (!b.isGhost ·) ++ ordered) }
    else
      if b.hasProp then
        throwError "(internal) multiuniverse lowering: the kernel denested an occurrence in a \
          block with a `Prop` member, which its shadow cannot follow"
      for k in *...heads.size do
        let numMinors := (← getConstInfoInduct heads[k]!).numCtors
        let nativeRec := name ++ `rec |>.appendIndexAfter (k + 1)
        discard <| getConstInfoRec nativeRec
        specs := specs.push
          { head := heads[k]!, motive := b.size + nMot, firstMinor := b.allCtors.size + nMin,
            numMinors, nativeRec, recName := name ++ `mutualRec |>.appendIndexAfter (k + 1) }
        nMot := nMot + 1
        nMin := nMin + numMinors
    unless info.numMinors == (sccCtorIndices b s).size + specs.foldl (· + ·.numMinors) 0 do
      throwError "(internal) multiuniverse lowering: `{name}.rec` asks for {info.numMinors} \
        minor premises, which its component and what the kernel denested for it do not \
        account for"
    perScc := perScc.push specs
  return (b, { perScc, numMotives := nMot, numMinors := nMin })

/-- The motives a component's native recursor asks for beyond its members'. -/
private def nestMotiveTypes (b : Block) (ns : Nests) (s : Nat) (params : Array Expr) :
    MetaM (Array Expr) := do
  let e := (ns.forScc s).size
  if e == 0 then return #[]
  let sz := b.sccs[s]!.size
  let (_, ty) ← memberRecAt b b.sccs[s]![0]! params #[]
  forallBoundedTelescope ty (some (sz + e)) fun xs _ =>
    (xs.extract sz (sz + e)).mapM inferType

/-- The minor premises it asks for beyond its members' constructors, stated at
the block's own motives.  No minor premise's type mentions the ones before it, so
reading them all off one telescope is enough. -/
private def nestMinorTypes (b : Block) (ns : Nests) (s : Nat) (params motives : Array Expr) :
    MetaM (Array Expr) := do
  let specs := ns.forScc s
  if specs.isEmpty then return #[]
  let (_, ty) ← memberRecAt b b.sccs[s]![0]! params (sccMotiveVals b ns s motives)
  let own := (sccCtorIndices b s).size
  let tot := specs.foldl (· + ·.numMinors) 0
  forallBoundedTelescope ty (some (own + tot)) fun xs _ =>
    (xs.extract own (own + tot)).mapM inferType

/--
The induction hypotheses the kernel's own recursor offers for `c` that the
block's field analysis does not: one for each occurrence the kernel denested.

Each comes back as the index of the field it is about, and its type abstracted
over the constructor's fields, for the caller to restate at whichever copies of
them it holds.  Which field a hypothesis is about is not guessed: it is the one
whose variable the hypothesis mentions.
-/
private def nestIHs (b : Block) (ns : Nests) (params motives : Array Expr) (c : CtorInfo) :
    MetaM (Array (Nat × Expr)) := do
  let some s := b.sccOf[c.owner]! | return #[]
  if (ns.forScc s).isEmpty then return #[]
  let (_, ty) ← memberRecAt b b.sccs[s]![0]! params (sccMotiveVals b ns s motives)
  let ctorIdx := sccCtorIndices b s
  let some pos := ctorIdx.findIdx? (b.allCtors[·]!.name == c.name)
    | throwError "(internal) multiuniverse lowering: `{c.name}` is not a constructor of its \
        own component"
  let minorTy ← forallBoundedTelescope ty (some (pos + 1)) fun xs _ => inferType xs[pos]!
  forallBoundedTelescope minorTy (some c.numFields) fun fields rest =>
    forallTelescope rest fun ihs _ => do
      let mut out : Array (Nat × Expr) := #[]
      for ih in ihs do
        let t ← inferType ih
        let mut which : Option Nat := none
        for k in *...c.numFields do
          if which.isNone && t.containsFVar fields[k]!.fvarId! then which := some k
        let some k := which
          | throwError "(internal) multiuniverse lowering: an induction hypothesis of \
              `{c.name}` is about none of its fields"
        if c.fields[k]!.isNone then out := out.push (k, t.abstract fields)
      return out

/-- The one of `nestIHs`' hypotheses that is about field `k`, restated at
`fields`. -/
private def nestIH? (nested : Array (Nat × Expr)) (k : Nat) (fields : Array Expr) :
    Option Expr :=
  nested.findSome? fun (j, t) => if j == k then some (t.instantiateRev fields) else none

/-! ### Recursors

Every generated recursor has the *same* signature apart from its major premise
and result:

```
{params} {motive_1 .. motive_n} (case_1 .. case_K) {idxs} (t : X_i idxs)
  : motive_i idxs t
```

with `motive_j` at `Prop` for a `Prop` member and at that member's SCC universe
otherwise (and named plain `motive` when the block has only one member, which is
`motiveNames` below).  This uniformity is what lets a data recursor plug `X_j.mutualRec`
in as the induction hypothesis for a field it has no native IH for: the
arguments it already has are exactly the ones `X_j.mutualRec` wants.
-/

/-- What to call the motives of a recursor that has `n` of them: `motive` on its
own when there is only one, `motive_1 .. motive_n` otherwise.  Lean names its own
recursors this way, and every recursor we emit follows it, so that a caller who
has to name a motive names it the same whichever member it came from. -/
def motiveNames (n : Nat) : Array Name :=
  if n == 1 then #[`motive]
  else Array.ofFn (n := n) fun j => Name.mkSimple s!"motive_{j.val + 1}"

/-- The type of the minor premise for constructor `c`: all fields, then one
induction hypothesis per recursive field and per field the kernel denested, in
field order -- which is the order the kernel's own recursors use. -/
private def mkMinorType (b : Block) (ns : Nests) (params motives : Array Expr) (c : CtorInfo) :
    MetaM Expr := do
  let nested ← nestIHs b ns params motives c
  let inner ← instantiateForall (← b.toUser c.type) params
  forallTelescope inner fun fields result => do
    let idxs := b.memberIdxs c.owner result
    let ctorApp := b.userCtorApp c params fields
    let mut concl := mkAppN motives[c.owner]! (idxs ++ #[ctorApp])
    let mut ihs : Array (Name × Expr) := #[]
    for k in *...c.numFields do
      if let some rf := c.fields[k]! then
        let ih ← forallTelescope (← inferType fields[k]!) fun ys fbody => do
          let fidxs := b.memberIdxs rf.member fbody
          mkForallFVars ys (mkAppN motives[rf.member]! (fidxs ++ #[mkAppN fields[k]! ys]))
        ihs := ihs.push (Name.mkSimple s!"ih_{k + 1}", ih)
      else if let some ih := nestIH? nested k fields then
        ihs := ihs.push (Name.mkSimple s!"ih_{k + 1}", ih)
    -- no induction hypothesis is ever referred to, so plain `forallE` is safe
    for (nm, t) in ihs.reverse do
      concl := .forallE nm t concl .default
    mkForallFVars fields concl

/-- The binder infos of every recursor in the block: parameters and motives
implicit, minor premises explicit, then the indices implicit and the major
premise explicit. -/
private def recBinderInfos (b : Block) (ns : Nests) (nidxs : Nat) : Array BinderInfo :=
  rep b.numParams BinderInfo.implicit
    ++ rep (b.size + ns.numMotives) BinderInfo.implicit
    ++ rep (b.allCtors.size + ns.numMinors) BinderInfo.default
    ++ rep nidxs BinderInfo.implicit
    ++ #[BinderInfo.default]

/-- Set up the front of the telescope every recursor in the block shares -- one
motive per member and per type the kernel denested, then one minor premise per
constructor of each -- and hand it to `k`. -/
private def withRecFront {α} [Inhabited α] (b : Block) (ns : Nests) (params : Array Expr)
    (k : Array Expr → Array Expr → MetaM α) : MetaM α := do
  let mut motiveTys : Array Expr := #[]
  for j in *...b.size do
    let aj ← instantiateForall b.members[j]!.type params
    motiveTys := motiveTys.push <| ← forallTelescope aj fun jidxs _ =>
      withLocalDeclD `t (b.realTypeAt j params jidxs)
        fun tv => mkForallFVars (jidxs ++ #[tv]) (mkSort (b.motiveLevel j))
  for s in *...b.sccs.size do
    motiveTys := motiveTys ++ (← nestMotiveTypes b ns s params)
  let mnames := motiveNames motiveTys.size
  let mut motiveDecls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) := #[]
  for j in *...motiveTys.size do
    motiveDecls := motiveDecls.push (mnames[j]!, .implicit, fun _ => pure motiveTys[j]!)
  withLocalDecls motiveDecls fun motives => do
    let mut minorTys : Array Expr := #[]
    for q in *...b.allCtors.size do
      minorTys := minorTys.push (← mkMinorType b ns params motives b.allCtors[q]!)
    for s in *...b.sccs.size do
      minorTys := minorTys ++ (← nestMinorTypes b ns s params motives)
    let mut minorDecls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) := #[]
    for q in *...minorTys.size do
      minorDecls := minorDecls.push
        (Name.mkSimple s!"case_{q + 1}", .default, fun _ => pure minorTys[q]!)
    withLocalDecls minorDecls fun minors => k motives minors

/-- Set up the whole telescope of `X_i.mutualRec` and hand the body builder the
pieces. -/
private def withRecTelescope (b : Block) (ns : Nests) (i : Nat)
    (mkBody : Array Expr → Array Expr → Array Expr → Array Expr → Expr → MetaM Expr) :
    MetaM (Expr × Expr) := do
  forallBoundedTelescope b.members[i]!.type (some b.numParams) fun params _ =>
    withRecFront b ns params fun motives minors => do
      let ai ← instantiateForall b.members[i]!.type params
      forallTelescope ai fun idxs _ =>
        withLocalDeclD `t (b.realTypeAt i params idxs) fun major => do
          let body ← mkBody params motives minors idxs major
          let all := params ++ motives ++ minors ++ idxs ++ #[major]
          let ty ← mkForallFVars all (mkAppN motives[i]! (idxs ++ #[major]))
          return (forceBinderInfos ty (recBinderInfos b ns idxs.size), ← mkLambdaFVars all body)

/-- The same, for the recursor whose major premise is a type the kernel denested.
Its indices and major premise are read off its motive, which is the kernel's own. -/
private def withNestRecTelescope (b : Block) (ns : Nests) (s : Nat) (sp : NestSpec)
    (mkBody : Array Expr → Array Expr → Array Expr → Array Expr → Expr → MetaM Expr) :
    MetaM (Expr × Expr) := do
  forallBoundedTelescope b.members[b.sccs[s]![0]!]!.type (some b.numParams) fun params _ =>
    withRecFront b ns params fun motives minors => do
      forallTelescope (← inferType motives[sp.motive]!) fun zs _ => do
        let some t := zs.back?
          | throwError "(internal) multiuniverse lowering: the motive for `{sp.head}` takes no \
              major premise"
        let idxs := zs.pop
        withLocalDeclD `t (← inferType t) fun major => do
          let body ← mkBody params motives minors idxs major
          let all := params ++ motives ++ minors ++ idxs ++ #[major]
          let ty ← mkForallFVars all (mkAppN motives[sp.motive]! (idxs ++ #[major]))
          return (forceBinderInfos ty (recBinderInfos b ns idxs.size), ← mkLambdaFVars all body)

/-- `nameOf j` -- `X_j.mutualRec`, or the implementation of it built below --
applied at the current motives and minors, lifted pointwise through any leading
`∀`s of `v`'s type.  Every recursor in the block takes the same arguments, so
the ones we already have are exactly the ones it wants. -/
private def recCallTo (b : Block) (nameOf : Nat → Name) (levels : List Level)
    (params motives minors : Array Expr) (j : Nat) (v : Expr) : MetaM Expr := do
  forallTelescope (← inferType v) fun ys body => do
    let jidxs := b.memberIdxs j body
    let r := mkConst (nameOf j) levels
    mkLambdaFVars ys (mkAppN r (params ++ motives ++ minors ++ jidxs ++ #[mkAppN v ys]))

/-- `X_j.mutualRec` applied at the current motives and minors. -/
private def recCall (b : Block) (params motives minors : Array Expr) (j : Nat) (v : Expr) :
    MetaM Expr :=
  recCallTo b b.recName b.recLevels params motives minors j v

/--
Build the body of a shadow minor premise, walking the constructor's fields.

The shadow's fields for data members are useless -- they carry no data -- so we
*discard* them and take the real element out of the corresponding induction
hypothesis, whose motive was chosen to be `Nonempty ((w : X_j) ×' motive_j w)`
precisely so that it would still contain one.  This is legal because everything
built here is a `Prop`.
-/
private partial def propMinorBody (b : Block) (params motives minors : Array Expr)
    (c : CtorInfo) (q : Nat) (sf sih : Array Expr) (target : Expr)
    (k ihPos : Nat) (realF realIH : Array Expr) : MetaM Expr := do
  if k ≥ c.numFields then
    let minorApp := mkAppN minors[q]! (realF ++ realIH)
    let m := b.members[c.owner]!
    if m.isProp then
      -- the shadow field and the real field are equal by proof irrelevance
      return minorApp
    else
      -- repackage as `⟨⟨X_m.c realF, case realF realIH⟩⟩`
      let sigTy := target.appArg!
      let sargs := sigTy.getAppArgs
      let ctorApp := b.userCtorApp c params realF
      let mk ← mkAppOptM ``PSigma.mk
        #[some sargs[0]!, some sargs[1]!, some ctorApp, some minorApp]
      mkAppOptM ``Nonempty.intro #[some sigTy, some mk]
  else
    let cont := propMinorBody b params motives minors c q sf sih target
    match c.fields[k]! with
    | none => cont (k + 1) ihPos (realF.push sf[k]!) realIH
    | some rf =>
      let ih := sih[ihPos]!
      if b.members[rf.member]!.isProp then
        -- `X_j` *is* `X_j._shadow`, so the shadow field and IH are already right
        cont (k + 1) (ihPos + 1) (realF.push sf[k]!) (realIH.push ih)
      else if rf.arity == 0 then
        -- destructure the witness; `Nonempty.rec` lands in `Prop`, which the
        -- target is, so no choice principle is needed
        let ihTy ← whnf (← inferType ih)
        let sigTy := ihTy.appArg!
        let lvl ← getLevel sigTy
        withLocalDeclD (Name.mkSimple s!"w_{k + 1}") sigTy fun wv => do
          let bb ← mkAppM ``PSigma.fst #[wv]
          let pp ← mkAppM ``PSigma.snd #[wv]
          let rest ← cont (k + 1) (ihPos + 1) (realF.push bb) (realIH.push pp)
          let f ← mkLambdaFVars #[wv] rest
          let mot := Expr.lam `h ihTy target .default
          return mkAppN (mkConst ``Nonempty.rec [lvl]) #[sigTy, mot, f, ih]
      else
        -- a function *into* a data member: the witnesses have to be selected
        -- pointwise, which is the one place `Classical.choice` is unavoidable
        let ihTy ← inferType ih
        let kf ← forallTelescope ihTy fun ys neBody => do
          let sigTy := (← whnf neBody).appArg!
          let lvl ← getLevel sigTy
          mkLambdaFVars ys (mkAppN (mkConst ``Classical.choice [lvl]) #[sigTy, mkAppN ih ys])
        let bb ← forallTelescope ihTy fun ys _ => do
          mkLambdaFVars ys (← mkAppM ``PSigma.fst #[mkAppN kf ys])
        let pp ← forallTelescope ihTy fun ys _ => do
          mkLambdaFVars ys (← mkAppM ``PSigma.snd #[mkAppN kf ys])
        cont (k + 1) (ihPos + 1) (realF.push bb) (realIH.push pp)

private def mkPropRecBody (b : Block) (i : Nat)
    (params motives minors idxs : Array Expr) (major : Expr) : MetaM Expr := do
  let mut smotives := #[]
  for j in *...b.size do
    let aj ← instantiateForall b.members[j]!.type params
    let mot ← forallTelescope aj fun jidxs _ => do
      let sTy := mkAppN (mkConst (shadowName b.members[j]!.name) b.ownLevels) (params ++ jidxs)
      withLocalDeclD `t sTy fun tv => do
        let body ←
          if b.members[j]!.isProp then
            pure (mkAppN motives[j]! (jidxs ++ #[tv]))
          else
            let dTy := b.realTypeAt j params jidxs
            withLocalDeclD `w dTy fun wv => do
              mkNESig dTy (← mkLambdaFVars #[wv] (mkAppN motives[j]! (jidxs ++ #[wv])))
        mkLambdaFVars (jidxs ++ #[tv]) body
    smotives := smotives.push mot
  let recName := shadowName b.members[i]!.name ++ `rec
  let recFn := mkConst recName (← elimLevelsFor recName .zero b.ownLevels)
  let ty0 ← instantiateForall (← inferType recFn) params
  let ty1 ← instantiateForall ty0 smotives
  let sminors ← buildArgs ty1 b.allCtors.size fun q minorTy => do
    let c := b.allCtors[q]!
    forallTelescope minorTy fun args target => do
      let sf := args.extract 0 c.numFields
      let sih := args.extract c.numFields args.size
      let body ← propMinorBody b params motives minors c q sf sih (← whnf target) 0 0 #[] #[]
      mkLambdaFVars args body
  return mkAppN recFn (params ++ smotives ++ sminors ++ idxs ++ #[major])

/--
The body of a data recursor: one application of the kernel's own recursor for
the component, at the block's motives.

`recName` says which one -- a member's `rec`, or the `rec_k` the kernel gave a
type it denested for the component -- and `base` and `rparams` are the levels
and parameters it takes, which for a ghost's are the copied type's.  All of them
have the same motives and minor premises, so the same body serves for any; only
the major premise differs.

The minor premises for the component's own constructors are the block's,
supplied with an induction hypothesis for every field: the kernel's own where it
has one, and a call to the block-wide recursor where the field points outside the
component.  The ones the kernel added for what it denested are passed through
untouched, since the block asks for them in exactly the form the kernel does.
-/
private def mkSccRecBody (b : Block) (ns : Nests) (s : Nat) (recName : Name)
    (base : List Level) (rparams : Array Expr)
    (params motives minors idxs : Array Expr) (major : Expr) : MetaM Expr := do
  let nmotives := sccMotiveVals b ns s motives
  let lvl := b.motiveLevel b.sccs[s]![0]!
  let recFn := mkConst recName (← elimLevelsFor recName lvl base)
  let ty0 ← instantiateForall (← inferType recFn) rparams
  let ty1 ← instantiateForall ty0 nmotives
  let ctorIdx := sccCtorIndices b s
  let specs := ns.forScc s
  let nminors ← buildArgs ty1 (ctorIdx.size + specs.foldl (· + ·.numMinors) 0) fun q minorTy => do
    if q ≥ ctorIdx.size then
      -- the specs of a component are numbered consecutively, so its extra minor
      -- premises sit in one run of the block's
      return minors[specs[0]!.firstMinor + (q - ctorIdx.size)]!
    let gq := ctorIdx[q]!
    let c := b.allCtors[gq]!
    let nested ← nestIHs b ns params motives c
    forallTelescope minorTy fun args _ => do
      let fields := args.extract 0 c.numFields
      let nih := args.extract c.numFields args.size
      let mut userIH := #[]
      let mut p := 0
      for k in *...c.numFields do
        if let some rf := c.fields[k]! then
          if b.sccOf[rf.member]! == some s then
            -- the native recursor already provides this one
            userIH := userIH.push nih[p]!
            p := p + 1
          else
            -- a `Prop` member, or a data member of an earlier SCC: its
            -- block-wide recursor is already defined and takes exactly our
            -- arguments
            userIH := userIH.push (← recCall b params motives minors rf.member fields[k]!)
        else if (nestIH? nested k fields).isSome then
          -- an occurrence the kernel denested, so the native recursor has it
          userIH := userIH.push nih[p]!
          p := p + 1
      mkLambdaFVars args (mkAppN minors[gq]! (fields ++ userIH))
  return mkAppN recFn (rparams ++ nmotives ++ nminors ++ idxs ++ #[major])

private def emitRec (b : Block) (ns : Nests) (i : Nat) : MetaM Unit := do
  let m := b.members[i]!
  let (ty, val) ← withRecTelescope b ns i fun params motives minors idxs major => do
    if m.isProp then
      mkPropRecBody b i params motives minors idxs major
    else
      let some s := b.sccOf[i]!
        | throwError "(internal) multiuniverse lowering: data member without an SCC"
      let (recName, base, rparams) := b.memberRecOf i params
      mkSccRecBody b ns s recName base rparams params motives minors idxs major
  -- a data member's recursor is left uncompiled: its body is a recursor
  -- application, so compiling it here would fail and mark it `noncomputable`,
  -- and its code comes instead from the implementation emitted afterwards.  A
  -- `Prop` member's is a proof, so it erases and may as well go through now
  addDef (b.recName i) b.recLevelParams ty val (compile := m.isProp)
  markElabAsElim (b.recName i)
  -- a `Prop` member has no native recursor under its user-facing name, so the
  -- block-wide one may as well also answer to `X.rec`
  if m.isProp then
    addDef (m.name ++ `rec) b.recLevelParams ty val
    markElabAsElim (m.name ++ `rec)
    -- neither of those is a shape `induction` can drive: both ask for a motive
    -- at every data member of the block, and the goal determines none of them.
    -- `X.recP` has them discharged at `Unit`, which costs nothing a proof about
    -- a `Prop` member could have used
    discard <| attempt? `Mumi m!"no one-motive recursor for `{m.name}`" <|
      addSoloElim b.numParams b.sccLevel true (b.recName i) (m.name ++ `recP)
        (forCases := false)

/-- The block-wide recursor whose major premise is a type the kernel denested.
Lean declares one of these for every mutual block that nests, so a block lowered
here has them too, under the names a `mutual` block's would have. -/
private def emitNestRec (b : Block) (ns : Nests) (s : Nat) (sp : NestSpec) : MetaM Unit := do
  let (ty, val) ← withNestRecTelescope b ns s sp fun params motives minors idxs major =>
    mkSccRecBody b ns s sp.nativeRec b.ownLevels params params motives minors idxs major
  addDef sp.recName b.recLevelParams ty val (compile := false)
  markElabAsElim sp.recName

/-! ### Making the recursors computable

The code generator compiles no recursor application at all -- `X.rec` exactly
as little as `Nat.rec` -- so a `mutualRec` whose body is one would be
`noncomputable`, and so would everything downstream of it.  That would be a real
loss: the point of keeping the data members as honest inductives is that the
block stays computable, and `mutualRec` is the only way to write a recursion
that genuinely crosses members.

The restriction is about the shape of the term, not about the function: the
same recursion written by cases compiles fine, in a lowered block and in an
ordinary `mutual` one alike.  So each data member's `mutualRec` is paired with
an *implementation*

```
X_i.mutualRec.impl : <the type of X_i.mutualRec, verbatim>
```

which splits on its major premise with `X_i.casesOn` and calls itself and its
siblings directly, and with a theorem

```
X_i.mutualRec.eq_impl : @X_i.mutualRec = @X_i.mutualRec.impl
```

tagged `@[csimp]`, which is what makes the code generator emit the
implementation's code wherever `X_i.mutualRec` is used.

Nothing about this is taken on trust.  The implementation is a `def` like any
other, handed to Lean's own structural recursion (`Structural.structuralRecursion`,
not `addPreDefinitions`, which would quietly fall back to `partial` or `sorry`
on failure), so it is only accepted if that machinery can see it terminates.
The theorem is an ordinary proof, checked by the kernel.  A wrong one is an
error at the point of the block, which is the right place to find out that the
proof generator needs work; the alternative -- an unchecked companion the code
generator believes -- would be a miscompilation instead.

`mutualRec` itself is untouched: the iota rules and `#print axioms` are exactly
what they were, and `eq_impl`'s use of `funext` stays inside `eq_impl`.  A `Prop`
member needs no implementation at all: the result of its recursor is a `Prop`,
hence so is the recursor's whole type, so it is a proof and is erased.

The implementations recurse directly only within their own SCC.  For a field in
an earlier SCC an implementation calls that member's `mutualRec`, whose
`@[csimp]` theorem is registered by then and rewrites the call when the code
generator gets to it; that keeps each proof one congruence deep and means
nothing has to be threaded across components by hand.
-/

/-- The computable implementation of `X_i.mutualRec`. -/
def Block.implName (b : Block) (i : Nat) : Name := b.recName i ++ `impl

/-- The `@[csimp]` theorem `@X_i.mutualRec = @X_i.mutualRec.impl`. -/
def Block.implEqName (b : Block) (i : Nat) : Name := b.recName i ++ `eq_impl

/-! A *slot* is a position among the block's motives: a member below `b.size`,
and a type the kernel denested above it.  The implementations are written over
slots throughout, since a member's recursion into a nesting and back is one
mutual recursion and has to be defined as one. -/

/-- The block-wide recursor for a slot. -/
private def slotRecName (b : Block) (ns : Nests) (e : Nat) : Name :=
  match ns.spec? e with
  | some sp => sp.recName
  | none => b.recName e

/-- Its implementation. -/
private def slotImplName (b : Block) (ns : Nests) (e : Nat) : Name :=
  match ns.spec? e with
  | some sp => sp.implName
  | none => b.implName e

/-- Its `@[csimp]` theorem. -/
private def slotImplEqName (b : Block) (ns : Nests) (e : Nat) : Name :=
  match ns.spec? e with
  | some sp => sp.implEqName
  | none => b.implEqName e

/-- Which slot an induction hypothesis is about, and how many arguments it is
lifted through.  Its conclusion is an application of exactly one of the motives,
so neither has to be guessed from the field it came from. -/
private def ihSlot (motives : Array Expr) (ihTy : Expr) : MetaM (Nat × Nat) :=
  forallTelescope ihTy fun ys body => do
    let some e := motives.findIdx? (· == body.getAppFn)
      | throwError "(internal) multiuniverse lowering: an induction hypothesis is about none \
          of the block's motives:{indentExpr ihTy}"
    return (e, ys.size)

/-- An induction hypothesis of type `ihTy`, built by recursing with `nameOf` on
the slot the hypothesis is about.  Every recursor in the block takes the same
arguments before the indices, so the ones we already hold are the ones it wants,
and the indices and the value it wants are the hypothesis' own. -/
private def implIH (levels : List Level) (nameOf : Nat → Name)
    (params motives minors : Array Expr) (ihTy : Expr) : MetaM Expr :=
  forallTelescope ihTy fun ys body => do
    let (e, _) ← ihSlot motives (← mkForallFVars ys body)
    mkLambdaFVars ys
      (mkAppN (mkConst (nameOf e) levels) (params ++ motives ++ minors ++ body.getAppArgs))

/-- A minor premise of a block-wide recursor, applied to a constructor's fields
and to induction hypotheses built by recursing.  `casesOn` offers no hypotheses
of its own, so which ones are wanted is read off the minor premise's own type. -/
private def applyMinor (levels : List Level) (nameOf : Nat → Name)
    (params motives minors : Array Expr) (minor : Expr) (fields : Array Expr) : MetaM Expr := do
  forallTelescope (← instantiateForall (← inferType minor) fields) fun ihs _ => do
    let vals ← ihs.mapM fun ih => do
      implIH levels nameOf params motives minors (← inferType ih)
    return mkAppN minor (fields ++ vals)

/--
The body of `X_i.mutualRec.impl`: one `X_i.casesOn`, with every induction
hypothesis supplied by a direct call -- to a sibling's implementation inside
`group`, and to `X_j.mutualRec` outside it, where that member's own `@[csimp]`
theorem takes over.  `levels` are the levels the recursors are instantiated at,
which differ between the lowered and the native path.
-/
private def mkImplBody (b : Block) (ns : Nests) (group : Array Nat) (levels : List Level)
    (i : Nat) (params motives minors idxs : Array Expr) (major : Expr) : MetaM Expr := do
  let mot ← forallTelescope (← inferType motives[i]!) fun zs _ =>
    mkLambdaFVars zs (mkAppN motives[i]! zs)
  let (casesName, base, cparams) := b.memberCasesOf i params
  let elim ← getLevel (mkAppN motives[i]! (idxs ++ #[major]))
  let casesFn := mkConst casesName (← elimLevelsFor casesName elim base)
  let ty0 ← instantiateForall (← inferType casesFn) cparams
  let ty1 ← instantiateForall ty0 #[mot]
  let ty2 ← instantiateForall ty1 (idxs ++ #[major])
  -- outside the group -- an earlier SCC, or a `Prop` member, whose recursor is a
  -- proof and needs no implementation -- go through `mutualRec` and let `csimp`
  -- rewrite the call
  let nameOf (e : Nat) : Name :=
    if group.contains e then slotImplName b ns e else slotRecName b ns e
  let mut ctorIdx := #[]
  for q in *...b.allCtors.size do
    if b.allCtors[q]!.owner == i then
      ctorIdx := ctorIdx.push q
  let cminors ← buildArgs ty2 ctorIdx.size fun q minorTy => do
    let gq := ctorIdx[q]!
    -- `casesOn` offers no induction hypotheses, so its minor premise binds the
    -- fields and nothing else
    forallBoundedTelescope minorTy (some b.allCtors[gq]!.numFields) fun fields _ => do
      mkLambdaFVars fields
        (← applyMinor levels nameOf params motives minors minors[gq]! fields)
  return mkAppN casesFn (cparams ++ #[mot] ++ idxs ++ #[major] ++ cminors)

/--
The same, for the implementation of a recursor over a type the kernel denested.
That type is not a member of the block, so the cases are its own and the
parameters they are taken at are the major premise's, not the block's; from
there the induction hypotheses are built exactly as a member's are.
-/
private def mkNestImplBody (b : Block) (ns : Nests) (group : Array Nat) (levels : List Level)
    (sp : NestSpec) (params motives minors idxs : Array Expr) (major : Expr) : MetaM Expr := do
  let dinfo ← getConstInfoInduct sp.head
  let majorTy ← whnf (← inferType major)
  let dparams := majorTy.getAppArgs.extract 0 dinfo.numParams
  let mot ← forallTelescope (← inferType motives[sp.motive]!) fun zs _ =>
    mkLambdaFVars zs (mkAppN motives[sp.motive]! zs)
  let casesName := sp.head ++ `casesOn
  let elim ← getLevel (mkAppN motives[sp.motive]! (idxs ++ #[major]))
  let casesFn := mkConst casesName (← elimLevelsFor casesName elim majorTy.getAppFn.constLevels!)
  let ty0 ← instantiateForall (← inferType casesFn) dparams
  let ty1 ← instantiateForall ty0 #[mot]
  let ty2 ← instantiateForall ty1 (idxs ++ #[major])
  let nameOf (e : Nat) : Name :=
    if group.contains e then slotImplName b ns e else slotRecName b ns e
  let ctors := dinfo.ctors.toArray
  let cminors ← buildArgs ty2 ctors.size fun q minorTy => do
    let numFields := (← getConstInfoCtor ctors[q]!).numFields
    forallBoundedTelescope minorTy (some numFields) fun fields _ => do
      mkLambdaFVars fields
        (← applyMinor levels nameOf params motives minors minors[sp.firstMinor + q]! fields)
  return mkAppN casesFn (dparams ++ #[mot] ++ idxs ++ #[major] ++ cminors)

/--
Open the telescope of `X_i.mutualRec` -- `{params} {motive_1 .. motive_n}
(case_1 .. case_K) {idxs} (t)` -- and hand `k` the whole telescope and each of
its five parts.

Both paths agree on the split.  A lowered block's recursors have this signature
by construction, and a homogeneous block's `mutualRec` is an alias of a native
recursor, whose motives and minor premises range over the whole block; the
caller checks that.
-/
private def withMutualRecTelescope {α} [Inhabited α] (b : Block) (ns : Nests) (i : Nat)
    (k : Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Expr → MetaM α) :
    MetaM α := do
  let info ← getConstInfoDefn (slotRecName b ns i)
  forallTelescope info.type fun xs _ => do
    let nmot := b.numParams + b.size + ns.numMotives
    let nfront := nmot + b.allCtors.size + ns.numMinors
    if xs.size ≤ nfront then
      throwError "(internal) multiuniverse lowering: unexpected signature for \
        `{slotRecName b ns i}`:{indentExpr info.type}"
    k xs (xs.extract 0 b.numParams) (xs.extract b.numParams nmot)
      (xs.extract nmot nfront)
      (xs.extract nfront (xs.size - 1)) xs[xs.size - 1]!

/-- `h : ∀ ys, f ys = g ys` becomes `f = g`, one `funext` per binder. -/
private def mkFunExtN (h : Expr) (n : Nat) : MetaM Expr := do
  if n == 0 then return h
  forallBoundedTelescope (← inferType h) (some n) fun ys _ => do
    let mut p := mkAppN h ys
    for k in *...n do
      p ← mkFunExt (← mkLambdaFVars #[ys[n - 1 - k]!] p)
    return p

/-- The constructors of the slots in `group`, in the order the recursor whose
motives range over exactly `group` expects its minor premises, each as its
position among the block's minor premises, the slot that owns it, and how many
fields it has. -/
private def groupCtorIndices (b : Block) (ns : Nests) (group : Array Nat) :
    MetaM (Array (Nat × Nat × Nat)) := do
  let mut out := #[]
  for j in group do
    match ns.spec? j with
    | some sp =>
      for t in *...sp.numMinors do
        let c ← getConstInfoCtor (← getConstInfoInduct sp.head).ctors.toArray[t]!
        out := out.push (sp.firstMinor + t, j, c.numFields)
    | none =>
      for q in *...b.allCtors.size do
        if b.allCtors[q]!.owner == j then
          out := out.push (q, j, b.allCtors[q]!.numFields)
  return out

/--
A proof of `X_i.mutualRec args idxs major = X_i.mutualRec.impl args idxs major`,
by induction on `major` with `X_i.rec`.

`motiveGroup` is what that recursor's motives range over, `implGroup` the
members being implemented -- the same thing on the lowered path, where the
recursor belongs to the SCC, but not on the native one, where it belongs to the
whole block.  For a member of `motiveGroup` outside `implGroup` the two sides of
the equation are the same term, so its statement is reflexive and its minor
premises are `rfl`.

Everywhere else the two sides differ only at the induction hypotheses: the
recursor's iota rule leaves `X_l.mutualRec .. field` where the implementation
leaves `X_l.mutualRec.impl .. field`, for `l` in `implGroup`, and the same term
otherwise.  So each minor premise is a chain of congruences over the induction
hypotheses -- legal because no minor premise's later argument types depend on
them -- and closes by `rfl` at the head.
-/
private def mkImplEqBody (b : Block) (ns : Nests) (implGroup motiveGroup : Array Nat)
    (levels : List Level) (i : Nat) (params motives minors idxs : Array Expr) (major : Expr) :
    MetaM Expr := do
  let apply (nm : Name) (zs : Array Expr) : Expr :=
    mkAppN (mkConst nm levels) (params ++ motives ++ minors ++ zs)
  let implOf (e : Nat) : Name :=
    if implGroup.contains e then slotImplName b ns e else slotRecName b ns e
  let mut pmotives := #[]
  for j in motiveGroup do
    -- a motive's own type says what its slot ranges over, member or nesting
    pmotives := pmotives.push <| ← forallTelescope (← inferType motives[j]!) fun zs _ => do
      mkLambdaFVars zs (← mkEq (apply (slotRecName b ns j) zs) (apply (implOf j) zs))
  let (recName, base, rparams) := match ns.spec? i with
    | some sp => (sp.nativeRec, b.ownLevels, params)
    | none => b.memberRecOf i params
  let recFn := mkConst recName (← elimLevelsFor recName .zero base)
  let ty0 ← instantiateForall (← inferType recFn) rparams
  let ty1 ← instantiateForall ty0 pmotives
  let ctorIdx ← groupCtorIndices b ns motiveGroup
  let pminors ← buildArgs ty1 ctorIdx.size fun q minorTy => do
    let (gq, owner, numFields) := ctorIdx[q]!
    forallTelescope minorTy fun args target => do
      let some (_, lhs, _) := (← whnf target).eq?
        | throwError "(internal) multiuniverse lowering: the induction motive for slot \
            {owner} is not an equation"
      if !implGroup.contains owner then
        return ← mkLambdaFVars args (← mkEqRefl lhs)
      let fields := args.extract 0 numFields
      let nih := args.extract numFields args.size
      -- the block's minor premise says which induction hypotheses the two sides
      -- differ at; the recursor offers one for each whose slot it has a motive
      -- for, and only those
      let bihs ← forallTelescope (← instantiateForall (← inferType minors[gq]!) fields)
        fun ihs _ => ihs.mapM inferType
      let mut pf ← mkEqRefl (mkAppN minors[gq]! fields)
      let mut p := 0
      for ihTy in bihs do
        let (e, arity) ← ihSlot motives ihTy
        let inMotive := motiveGroup.contains e
        let h ←
          if inMotive && implGroup.contains e then
            mkFunExtN nih[p]! arity
          else
            mkEqRefl (← implIH levels (slotRecName b ns ·) params motives minors ihTy)
        if inMotive then
          p := p + 1
        pf ← mkCongr pf h
      mkLambdaFVars args pf
  return mkAppN recFn (rparams ++ pmotives ++ pminors ++ idxs ++ #[major])

/--
The implementations of one group of members' recursors, and their `@[csimp]`
theorems.

`implGroup` is a strongly connected component of the data-only dependency
graph, so its implementations are exactly the ones that have to be defined by
mutual recursion; `motiveGroup` is what the native recursors used to prove the
theorems range over, which on the native path is the whole block.
-/
private def emitImplGroup (b : Block) (ns : Nests) (implGroup motiveGroup : Array Nat) :
    TermElabM Unit := do
  if implGroup.isEmpty then return
  let docCtx := (← getLCtx, ← getLocalInstances)
  let names := implGroup.map (slotImplName b ns)
  let mut preDefs : Array PreDefinition := #[]
  for i in implGroup do
    let info ← getConstInfoDefn (slotRecName b ns i)
    let levels := info.levelParams.map Level.param
    let value ← withMutualRecTelescope b ns i fun xs params motives minors idxs major => do
      let body ← match ns.spec? i with
        | some sp => mkNestImplBody b ns implGroup levels sp params motives minors idxs major
        | none => mkImplBody b ns implGroup levels i params motives minors idxs major
      mkLambdaFVars xs body
    preDefs := preDefs.push
      { ref := .missing, kind := .def, levelParams := info.levelParams, modifiers := {},
        declName := slotImplName b ns i, binders := .missing, type := info.type, value,
        termination := TerminationHints.none }
  -- `structuralRecursion` throws if it cannot see that the definitions
  -- terminate; `addPreDefinitions` would instead fall back to `partial` or
  -- `sorry`, which is exactly the silent degradation we are avoiding
  if preDefs.any fun p => p.value.getUsedConstants.any (names.contains ·) then
    Structural.structuralRecursion docCtx preDefs
      (preDefs.map fun _ => (none : Option TerminationMeasure))
  else
    for preDef in preDefs do
      addAndCompileNonRec docCtx preDef
  for i in implGroup do
    let info ← getConstInfoDefn (slotRecName b ns i)
    let levels := info.levelParams.map Level.param
    let value ← withMutualRecTelescope b ns i fun xs params motives minors idxs major => do
      let mut pf ←
        mkImplEqBody b ns implGroup motiveGroup levels i params motives minors idxs major
      -- `∀ args, f args = g args` becomes `f = g`, which is `@X_i.mutualRec =
      -- @X_i.mutualRec.impl` up to eta -- the shape `csimp` wants
      for k in *...xs.size do
        pf ← mkFunExt (← mkLambdaFVars #[xs[xs.size - 1 - k]!] pf)
      return pf
    let type ← mkEq (mkConst (slotRecName b ns i) levels) (mkConst (slotImplName b ns i) levels)
    addDecl (.thmDecl
      { name := slotImplEqName b ns i, levelParams := info.levelParams, type, value })
    Compiler.CSimp.add (slotImplEqName b ns i) .global

/--
Implementations for a homogeneous block, whose `mutualRec`s are aliases of the
native recursors and so have the native signature -- one elimination universe
for the whole block rather than one per component, and motives ranging over
every member.
-/
private def emitNativeImpls (b : Block) : TermElabM Unit := do
  -- compile the aliases as they stand: this erases the small-eliminating ones
  -- and leaves anything else `noncomputable`, just as its own `rec` is
  let compileAliases : TermElabM Unit := do
    for i in *...b.size do
      Lean.compileDecl (.defnDecl (← getConstInfoDefn (b.recName i))) (logErrors := false)
  -- an all-`Prop` homogeneous block computes nothing, so it needs no
  -- implementation
  if b.members.all (·.isProp) then
    return ← compileAliases
  let info ← getConstInfoRec (b.members[0]!.name ++ `rec)
  -- the native recursor of a mutual block ranges over every member; if some
  -- future change makes that false, fall back to the aliases as they stand
  unless info.numParams == b.numParams && info.numMotives == b.size
      && info.numMinors == b.allCtors.size do
    return ← compileAliases
  -- a homogeneous block that is not all-`Prop` has no `Prop` member at all, so
  -- every member is in one of the data SCCs
  for s in *...b.sccs.size do
    emitImplGroup b (Nests.empty b.sccs.size) b.sccs[s]! (Array.range b.size)

/--
Lower an elaborated multiuniverse block to ordinary declarations.

A homogeneous block is emitted natively, so this library's `mutual` accepts
everything Lean's does and means the same thing by it.
-/
def lower (inp : Input) : TermElabM Unit := do
  let b ← analyze inp
  if b.isHomogeneous then
    emitNative b
    emitNativeImpls b
    return
  if b.hasProp then
    emitShadow b
    emitPropAliases b
  for s in *...b.sccs.size do
    emitDataSCC b s
  -- what the kernel denested is only knowable once it has been handed the block
  let (b, ns) ← mkNests b
  if b.hasProp then
    for s in *...b.sccs.size do
      emitSquashSCC b s
    emitPropCtors b
    for i in *...b.size do
      if b.members[i]!.isProp then
        emitRec b ns i
  -- one SCC at a time, so that an implementation's calls into an earlier
  -- component are already backed by a `@[csimp]` theorem
  for s in *...b.sccs.size do
    for i in b.sccs[s]! do
      emitRec b ns i
    for sp in ns.forScc s do
      emitNestRec b ns s sp
    -- a member's recursion into a type the kernel denested and back is one
    -- mutual recursion, so their implementations are defined together
    let group := b.sccs[s]! ++ (ns.forScc s).map (·.motive)
    emitImplGroup b ns group group

end Lean.Elab.MultiuniverseInductive
