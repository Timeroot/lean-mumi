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

Lean requires every member of a mutual inductive block to be in the same
universe.  The restriction is checked three times: while the headers are
elaborated, after the constructors are, and by the kernel.  So a block like

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

is rejected, although it denotes a well-defined family.

This module is the lowering behind this library's `mutual`.  It translates such
a block into ordinary declarations.  Every declaration it adds is an ordinary
inductive type, definition or theorem, so it asks nothing new of the kernel.

## The translation

1.  An all-`Prop` **shadow** of the whole block, `X_i._shadow`.  Every block has
   one.  The side condition on a constructor field of a `Prop`-valued inductive
   is `imax l' 0 ≤ 0`, which is vacuous, so the fields can be copied verbatim
   with member occurrences redirected to the shadow.

2.  The **data** members, declared under the users' own names, against the
   shadow.  They are grouped into strongly connected components of the data-only
   dependency graph and emitted in topological order.  Each SCC is
   universe-homogeneous -- an edge `i → j` forces `l_j ≤ l_i`, so a cycle forces
   equality -- hence each is an ordinary mutual block.

   A copy that only the shadow needs -- `Mumi.Denest` calls it a *ghost* and
   marks it with a `GhostInfo` -- is skipped here.  From step 3 on, the type it
   copies is written wherever the shadow writes the member, so its constructors
   and `casesOn` are the copied type's and the writer never sees its name.

   Its recursor is the copied type's when every occurrence it stands for is in a
   `Prop` member's constructor, which the lowering emits as a definition.  When a
   data member has a field at one, the occurrence reaches the kernel written out
   in full, the kernel denests it, and the ghost's recursor is the resulting
   `X.rec_k`.

3.  The `Prop` members' user-facing names (reducible abbreviations for their
   shadows) and constructors, the squash maps `X._squash : X → X._shadow`, and a
   block-wide recursor `X.mutualRec` for every member.

A data SCC may come back from `addDecl` larger than it went in: the kernel
denests what it can, adding a type for the occurrence and an extra recursor
`X.rec_k` at it.  Those extras are kept, so the block's recursors range over them
too and the constructor keeps the type the writer wrote; see the section on what
the kernel denested.

Only the `Prop` members are mangled.  Data members are ordinary inductive types
under the names the user wrote, so `match`, `induction`, `cases`, `injection`,
`noConfusion`, `deriving`, `sizeOf` and the code generator work on them as usual.
A `Prop` member's constructors must be re-derived, because their fields have the
wrong types in the shadow: `A.fromB` must take a real `B`, not a `B._shadow`.

## Why the recursors come out right

* A `Prop` member of a block with at least two members never large-eliminates,
  and the shadow has the same number of members, so it has the original's
  elimination strength.  Squashing the data members loses nothing.  This is the
  safety boundary: universes are derived per member, elimination never is.
* A `Prop` member's iota rules are equations between proofs, so proof
  irrelevance discharges them.
* All computational content is in the data recursors, which are the native
  recursors of the data members, so their iota rules hold by delta on
  `mutualRec` followed by native iota.

Choice is unavoidable in one case: a `Prop` member with a constructor field that
is a *function into* a data member.  The data witnesses must then be selected
pointwise, which needs `Classical.choice`.  A block without such a field produces
axiom-free recursors.

The recursors are also computable.  The code generator compiles no recursor
application, so this takes extra work; see the section on implementations.
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

/-- The last component of a name, for building a readable auxiliary name. -/
def shortName : Name → String
  | .str p s => if s.startsWith "_" then shortName p else s
  | _        => "nested"

/--
Unfold definitions at the head of `e` until an inductive type is exposed, so a
nested occurrence behind an `abbrev` is still seen. -/
def exposeInduct (e : Expr) : MetaM Expr := do
  let mut e := e
  for _ in *...8 do
    let .const n _ := e.getAppFn | return e
    if let some (.inductInfo _) := (← getEnv).find? n then return e
    let some e' ← unfoldDefinition? e | return e
    e := e'
  return e

/-! ## Input -/

/-- What a member that exists only in the *shadow* stands for in the real world. -/
structure GhostInfo where
  /-- `fun params => I p₁ … p_k`: the type the member copies, with the block's
  own members still free variables.  The member's indices are `I`'s own, so its
  type at given indices is this applied to the parameters and then to them. -/
  value     : Expr
  /-- `I` itself, whose recursor, `casesOn` and constructors do the work. -/
  head      : Name
  levels    : List Level
  /-- How many parameters `I` takes, so the indices of a value of this member's
  type can be read off it.  The block's own parameter count does not apply. -/
  numParams : Nat
  /-- `I`'s constructors, in `I`'s order, which is the order the copy's own
  constructors were made in. -/
  ctors     : Array Name
  /-- The kernel's recursor at this type for a ghost the kernel denested; `none`
  for one whose occurrences are all in definitions.  Filled in by `mkNests`, the
  first point at which the kernel has answered. -/
  nativeRec? : Option Name := none
  deriving Inhabited

/--
The elaborated block, as the elaborator hands it to the lowering: the
information `Lean.Elab.Command.mkInductiveDeclCore` has computed, with the
members still represented by free variables. -/
structure Input where
  levelParams : List Name
  /-- Number of leading section `variable`s; `numVars ≤ numParams`. -/
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
  /-- Set by `denest` when a copy takes a constructor-local as an index of its own. -/
  localIndices : Bool := false
  /-- Set by `denest` for a copy that is to exist in the shadow only; `none` at
  every member the writer declared.  Empty when there is nothing to say. -/
  memberGhost : Array (Option GhostInfo) := #[]

/-! ## Block description -/

/-- What a recursive constructor field recurses into. -/
structure RecField where
  /-- Index of the member this field recurses into. -/
  member : Nat
  /-- Number of leading `∀` binders before the member is reached.  Nonzero means
  the field is a *function into* the member; such fields force
  `Classical.choice` when the recursor's target is a `Prop`. -/
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
  /-- Each member as the real world names it: the constant it is declared as, or,
  for a ghost, `fun params => I p₁ … p_k`, the type it stands for with the other
  members substituted.  Read by `Block.realTypeAt`. -/
  userTargets : Array Expr
  deriving Inhabited

def Block.size (b : Block) : Nat := b.members.size

/-- The name a member is declared under. -/
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
stands for. -/
def Block.realTypeAt (b : Block) (j : Nat) (params idxs : Array Expr) : Expr :=
  b.userTargets[j]!.beta (params ++ idxs)

/-- The indices in a type of the form `X_j params idxs`. -/
def Block.memberIdxs (b : Block) (j : Nat) (ty : Expr) : Array Expr :=
  let args := ty.getAppArgs
  match b.members[j]!.ghost? with
  | some g => args.extract g.numParams args.size
  | none   => args.extract b.numParams args.size

/--
The universe of `X_i`'s motive: `Prop` for a `Prop` member, the member's SCC
parameter otherwise. -/
def Block.motiveLevel (b : Block) (i : Nat) : Level :=
  match b.sccOf[i]! with
  | none   => .zero
  | some s => .param b.sccLevel[s]!

def Block.ownLevels (b : Block) : List Level := b.levelParams.map .param

/--
Constructor `c` as the real world writes it, at the block's parameters and the
constructor's own fields. -/
def Block.userCtorApp (b : Block) (c : CtorInfo) (params fields : Array Expr) : Expr :=
  match b.members[c.owner]!.ghost? with
  | none   => mkAppN (mkConst c.name b.ownLevels) (params ++ fields)
  | some g =>
    let q := (b.members[c.owner]!.ctors.findIdx? (·.name == c.name)).getD 0
    let oparams := (b.realTypeAt c.owner params #[]).getAppArgs
    mkAppN (mkConst g.ctors[q]! g.levels) (oparams ++ fields)

/--
The native recursor member `i`'s component eliminates with, the levels it is
instantiated at, and the parameters it takes. -/
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
block. -/
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

During elaboration the members are free variables.  Emitting a declaration means
replacing them by constants: the shadow names, or the names the members are
declared under (for a data member, the user-facing name).  The substitution
happens underneath the parameter telescope, because a member free variable stands
for the member applied to the section variables.
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
other member; only the real world is missing it. -/
def Block.toShadow (b : Block) (e : Expr) : MetaM Expr :=
  b.substMembers (b.members.map fun m => mkConst (shadowName m.name) b.ownLevels) e

/-- Substitute what the real world calls each member: its own name, or, for a
ghost, the type it stands for. -/
def Block.toUser (b : Block) (e : Expr) : MetaM Expr :=
  b.substMembers b.userTargets e

/-- What `toUser` substitutes, computed once when the block is analysed. -/
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

/-- Add a plain safe definition and hand it to the code generator. -/
def addDef (name : Name) (levelParams : List Name) (type value : Expr)
    (hints : ReducibilityHints := .regular 0) (compile := true) : MetaM Unit := do
  let decl := Declaration.defnDecl { name, levelParams, type, value, hints, safety := .safe }
  addDecl decl
  if compile then
    compileDecl decl (logErrors := false)

/-- Run `act`; if it throws, restore the environment and continue without it. -/
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
`attempt?` for a construction whose only result is whether it went through.
-/
def attempted {m : Type → Type} [Monad m] [MonadEnv m] [MonadExcept Exception m]
    [MonadTrace m] [MonadRef m] [AddMessageContext m] [MonadOptions m]
    (cls : Name) (what : MessageData) (act : m Unit) : m Bool :=
  Option.isSome <$> attempt? cls what act

/-- Can the `induction` tactic supply every argument of `n` by itself? -/
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

/-- Tag a recursor `@[elab_as_elim]`, as Lean's own recursors are. -/
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

/-- Add an inductive declaration and everything Lean normally builds alongside one. -/
def addInd (levelParams : List Name) (numParams : Nat) (indTypes : Array InductiveType)
    (isClass : Bool := false) (genSizeOf : Bool := true) (genBRecOn : Bool := true) :
    MetaM Unit := do
  let decl := Declaration.inductDecl levelParams numParams indTypes.toList false
  addDecl decl
  let names := indTypes.map (·.name)
  -- the kernel denests a nested occurrence, declaring a type for it and a
  -- recursor `X.rec_k` with the major premise there
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
    if hasUnit && hasProd && genBRecOn then mkBelow n
  for n in names do
    if hasUnit && hasProd && genBRecOn then mkBRecOn n
  unless isClass do
    -- these are generated for the whole block from its first member
    if genSizeOf then mkSizeOfInstances names[0]!
    IndPredBelow.mkBelow names[0]!
    for n in names do
      mkInjectiveTheorems n

/-! ## An eliminator with one motive -/

/--
Walk the minors of a recursion whose other motives have been discharged, keep
the ones that conclude at the motive `kept`, drop the rest, and hand the
continuation the surviving binders together with the arguments the original
recursor is to be applied to. -/
private partial def soloMinors {α} [Inhabited α] (others mots motVals mins : Array Expr)
    (kept : Expr) (forCases : Bool) (q : Nat) (newMins minVals : Array Expr)
    (k : Array Expr → Array Expr → MetaM α) : MetaM α := do
  if h : q < mins.size then
    let orig := mins[q]
    let origTy ← inferType orig
    let isGone (id : FVarId) :=
      others.any (·.fvarId! == id) || (forCases && kept.fvarId! == id)
    -- read off before the substitution: afterwards the conclusion's head is no
    -- longer a motive, and a hypothesis at a discharged motive no longer
    -- mentions one
    let atKept ← forallTelescope origTy fun _ c => pure (c.getAppFn == kept)
    let drop ← forallTelescope origTy fun as _ =>
      as.mapM fun a => return (← inferType a).hasAnyFVar isGone
    let keptOf (as : Array Expr) : Array Expr :=
      (as.zip drop).filterMap fun (a, d) => if d then none else some a
    let ty ← Core.betaReduce (origTy.replaceFVars (mots ++ mins.extract 0 q) (motVals ++ minVals))
    if atKept then
      -- the block-wide recursion had to disambiguate its minor names, so each
      -- surviving minor is renamed after the constructor it is for, giving
      -- `induction ... with | snoc`
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
discharged. -/
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
    -- every other motive must be of the other kind, or discharging it costs a
    -- hypothesis worth having -- which a case split does not have, and which a
    -- block with no refusal to fall back on would rather pay
    unless forCases || evenIfWeaker ||
        (Array.range nMot).all fun q => q == kq || isProp[q]! != keepIsProp do
      return
    -- whether the result is itself a proof.  This differs from whether the
    -- member is a `Prop`: a subsingleton's recursor eliminates into any sort,
    -- and the eliminator built from it must keep carrying that universe
    let intoProp := keepIsProp && isProp[kq]!
    let pinned := if intoProp then elimLevels.filter (info.levelParams.contains ·) else #[]
    let pin (e : Expr) : Expr :=
      e.instantiateLevelParams pinned.toList (pinned.toList.map fun _ => Level.one)
    let outLvls := info.levelParams.filter (!pinned.contains ·)
    let others := (Array.range nMot).filterMap fun q => if q == kq then none else some mots[q]!
    let isOther (id : FVarId) := others.any (·.fvarId! == id)
    -- a discharged motive is filled with the one-element type at its own sort,
    -- the only choice for a *data* motive while the sort it lands in is still a
    -- parameter the kept motive needs
    let triv (ty : Expr) : MetaM Expr :=
      forallTelescope ty fun as c => mkLambdaFVars as (mkConst ``PUnit [c.sortLevel!])
    let subst (e : Expr) (vals : Array Expr) : MetaM Expr :=
      Core.betaReduce (e.replaceFVars (mots.extract 0 vals.size) vals)
    -- the discharged motives before the kept one, so its type can be substituted
    -- into before its binders are counted
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
      -- a minor is a binder concluding at a motive; what follows is the indices
      -- and the major, which pass through untouched
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
`Nonempty ((w : α) ×' β w)`: a `Prop` that remembers a data witness and whose
eliminator lands in `Prop`, which is all the minor premises of a `Prop` member's
recursor need. -/
private def mkNESig (α β : Expr) : MetaM Expr := do
  mkAppM ``Nonempty #[← mkAppOptM ``PSigma #[some α, some β]]

/--
The levels to instantiate the eliminator `elimName` -- a recursor or a `casesOn`
-- at, given that its motives are at `elim` and the block's own levels are
`own`. -/
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
(dependencies first). -/
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
  let mut compOf : Array (Option Nat) := Array.replicate n none
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
  -- topologically order the condensation: a component may be emitted once every
  -- component it depends on has been
  let m := comps.size
  let mut emitted : Array Bool := Array.replicate m false
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
  let mut newOf : Array Nat := Array.replicate m 0
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

/-- What a constructor field is. -/
private inductive FieldKind where
  /-- Recurses into a member, or mentions none; `none` for the latter. -/
  | plain (rf : Option RecField)
  /--
  Mentions members only inside another type constructor's parameters, as `List
  B` and `Tree S` do. -/
  | inert (deps : Array Nat) (why : MessageData)

/-- Classify one constructor field. -/
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
        -- a nested occurrence goes one of two ways: left as written for the
        -- kernel to denest, or copied into a member of the block
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
type. -/
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
  let mut edges : Array (Array Bool) := Array.replicate n (Array.replicate n false)
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
  -- an inert field recurses into nothing, but the member it names must exist by
  -- the time this one is declared
  for (i, d, _) in inert do
    if !isProp[i]! && !isProp[d]! then
      edges := edges.set! i (edges[i]!.set! d true)
  -- 3. condensation of the data-only graph
  let isData := isProp.map not
  let (sccs, sccOf) := computeSCCs n isData edges
  -- a ghost goes last in its component
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

/-- Is every member at the same universe?  If so the block is an ordinary
`mutual` block and the lowering must not touch it. -/
def Block.isHomogeneous (b : Block) : Bool :=
  b.members.all fun m => m.level.normalize == b.members[0]!.level.normalize

/-! ## The lowering

Emission order; each step only mentions constants emitted by earlier steps.

0. if the block is homogeneous, emit it natively and stop;
1.  `X_i._shadow`   -- the all-`Prop` shadow of the whole block;
2.  `X_i` for `Prop` members -- reducible abbreviations for their shadows;
3.  `X_i` for data members   -- honest inductives, one SCC at a time, in
                              topological order;
4.  `X_i._squash`   -- `X_i → X_i._shadow`, one SCC at a time;
5.  `X_i.c` for `Prop` members -- the user-facing constructors;
6.  `X_i.mutualRec` for `Prop` members -- from the shadow recursor;
7.  `X_i.mutualRec` for data members, in SCC order -- from the native recursors.

Step 6 only mentions data *constructors*, never data recursors, so 6 and 7 do
not form a cycle.
-/

/-- Walk `n` `∀`-binders of `ty`, building an argument for each with `mk` and
instantiating as it goes, so later domains see the earlier arguments. -/
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
over every member.  Keeps the generated API the same on both paths. -/
private def aliasNativeRecs (b : Block) : MetaM Unit := do
  for i in *...b.size do
    let rn := b.members[i]!.name ++ `rec
    let info ← getConstInfoRec rn
    addDef (b.recName i) info.levelParams info.type
      (mkConst rn (info.levelParams.map Level.param)) (compile := false)
    markElabAsElim (b.recName i)

/-- A homogeneous block is an ordinary `mutual` block; emit it unchanged, so this
library's `mutual` is a strict superset of Lean's. -/
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
are copied verbatim with member occurrences redirected to the shadow, which is
legal because a `Prop`-valued inductive constrains none of its fields. -/
private def emitShadow (b : Block) : MetaM Unit := do
  let mut indTypes : Array InductiveType := #[]
  for i in *...b.size do
    let m := b.members[i]!
    let sn := shadowName m.name
    let ctors ← m.ctors.mapM fun c =>
      return ({ name := reroot m.name sn c.name, type := ← b.toShadow c.type } : Constructor)
    indTypes := indTypes.push { name := sn, type := resultToProp m.type, ctors := ctors.toList }
  addInd b.levelParams b.numParams indTypes

/-- A `Prop` member *is* its shadow, since the shadow squashes data members only,
so its user-facing name is a reducible abbreviation.  These come before the data
members, whose constructors mention them. -/
private def emitPropAliases (b : Block) : MetaM Unit := do
  for i in *...b.size do
    let m := b.members[i]!
    if m.isProp then
      addDef m.name b.levelParams m.type (mkConst (b.realName i) b.ownLevels) .abbrev
      setReducibleAttribute m.name

/-- One SCC of the data-only dependency graph, declared under the users' own names. -/
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

/-- The `Prop` members' constructors. -/
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

`Mumi.Denest` passes a nested occurrence the kernel can take to the kernel, so
`S.t` is stated at `Tree S` and the type the kernel invents for `Tree S` is
declared alongside `S`.  The cost is that the component's native recursor ranges
over more than the component's members: it has a motive for each invented type and
minor premises for its constructors.  Everything built from that recursor must
offer the same.

They go at the end of their kind -- every member's motive first, then the invented
ones; every constructor of the block first, then theirs -- so a block with nothing
nested reads unchanged, and one with a nesting reads like the recursor Lean writes
for a `mutual` block that nests.
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
  { perScc := Array.replicate n #[], numMotives := 0, numMinors := 0 }

def Nests.forScc (ns : Nests) (s : Nat) : Array NestSpec := ns.perScc[s]?.getD #[]

/-- Which denested type a motive index past the block's own members belongs to. -/
def Nests.spec? (ns : Nests) (e : Nat) : Option NestSpec :=
  ns.perScc.findSome? fun specs => specs.findSome? fun sp =>
    if sp.motive == e then some sp else none

/-- The implementation of a block-wide recursor, and the `@[csimp]` theorem for
it.  Named as a member's are, so a nesting's recursor and a member's differ only
in what they belong to. -/
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

/--
The motive values a component's native recursor is applied at, in its own order:
the block's motive for each of the component's members, then the block's motive
for each type the kernel denested for the component. -/
private def sccMotiveVals (b : Block) (ns : Nests) (s : Nat) (motives : Array Expr) :
    Array Expr :=
  b.sccs[s]!.map (motives[·]!) ++ (ns.forScc s).map fun sp => motives[sp.motive]!

/--
Read off what the kernel denested for each component, by comparing that
component's native recursor with the component the lowering handed it. -/
private def mkNests (b : Block) : MetaM (Block × Nests) := do
  let mut b := b
  let mut perScc : Array (Array NestSpec) := #[]
  let mut nMot := 0
  let mut nMin := 0
  for s in *...b.sccs.size do
    let i := b.sccs[s]![0]!
    let name := b.members[i]!.name
    -- a component of ghosts never reached the kernel, so it has nothing to
    -- report; the kernel already knows the type a ghost stands for
    if b.isGhost i then
      perScc := perScc.push #[]
      continue
    let info ← getConstInfoRec (name ++ `rec)
    let ghosts := b.sccs[s]!.filter b.isGhost
    let decl := b.sccs[s]!.size - ghosts.size
    -- each extra motive's major premise, as `∀ idxs, T idxs` under the
    -- component's parameters
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

/-- The minor premises it asks for beyond its members' constructors, stated at the
block's own motives.  No minor premise's type mentions the ones before it, so one
telescope reads them all. -/
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
block's field analysis does not: one for each occurrence the kernel denested. -/
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
otherwise (named plain `motive` when the block has one member; see `motiveNames`
below).  This uniformity lets a data recursor plug `X_j.mutualRec` in as the
induction hypothesis for a field it has no native IH for: the arguments it already
has are the ones `X_j.mutualRec` wants.
-/

/--
What to call the motives of a recursor that has `n` of them: `motive` alone when
there is one, `motive_1 .. motive_n` otherwise. -/
def motiveNames (n : Nat) : Array Name :=
  if n == 1 then #[`motive]
  else Array.ofFn (n := n) fun j => Name.mkSimple s!"motive_{j.val + 1}"

/-- The type of the minor premise for constructor `c`: all fields, then one
induction hypothesis per recursive field and per field the kernel denested, in
field order, as the kernel's own recursors do. -/
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
    -- no induction hypothesis is referred to, so plain `forallE` is safe
    for (nm, t) in ihs.reverse do
      concl := .forallE nm t concl .default
    mkForallFVars fields concl

/-- The binder infos of every recursor in the block: parameters and motives
implicit, minor premises explicit, then the indices implicit and the major
premise explicit. -/
private def recBinderInfos (b : Block) (ns : Nests) (nidxs : Nat) : Array BinderInfo :=
  Array.replicate b.numParams BinderInfo.implicit
    ++ Array.replicate (b.size + ns.numMotives) BinderInfo.implicit
    ++ Array.replicate (b.allCtors.size + ns.numMinors) BinderInfo.default
    ++ Array.replicate nidxs BinderInfo.implicit
    ++ #[BinderInfo.default]

/-- Build the front of the telescope every recursor in the block shares -- one
motive per member and per type the kernel denested, then one minor premise per
constructor of each -- and pass it to `k`. -/
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

/-- Build the whole telescope of `X_i.mutualRec` and pass the pieces to the body
builder. -/
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

/-- `nameOf j` -- `X_j.mutualRec`, or its implementation built below -- applied at
the current motives and minors, lifted pointwise through any leading `∀`s of `v`'s
type.  Every recursor in the block takes the same arguments, so the ones in hand
are the ones it wants. -/
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

/-- Build the body of a shadow minor premise, walking the constructor's fields. -/
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
        -- a function *into* a data member: the witnesses must be selected
        -- pointwise, the one place `Classical.choice` is unavoidable
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
the component, at the block's motives. -/
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
            -- a `Prop` member, or a data member of an earlier SCC: its block-wide
            -- recursor is already defined and takes the same arguments
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
  -- application, so compiling it here would fail and mark it `noncomputable`
  addDef (b.recName i) b.recLevelParams ty val (compile := m.isProp)
  markElabAsElim (b.recName i)
  -- a `Prop` member has no native recursor under its user-facing name, so the
  -- block-wide one also answers to `X.rec`
  if m.isProp then
    addDef (m.name ++ `rec) b.recLevelParams ty val
    markElabAsElim (m.name ++ `rec)
    -- neither of those is a shape `induction` can drive: both ask for a motive
    -- at every data member of the block, and the goal determines none of them
    discard <| attempt? `Mumi m!"no one-motive recursor for `{m.name}`" <|
      addSoloElim b.numParams b.sccLevel true (b.recName i) (m.name ++ `recP)
        (forCases := false)

/-- The block-wide recursor whose major premise is a type the kernel denested.
Lean declares one for every mutual block that nests, so a block lowered here has
them too, under the names a `mutual` block's would have. -/
private def emitNestRec (b : Block) (ns : Nests) (s : Nat) (sp : NestSpec) : MetaM Unit := do
  let (ty, val) ← withNestRecTelescope b ns s sp fun params motives minors idxs major =>
    mkSccRecBody b ns s sp.nativeRec b.ownLevels params params motives minors idxs major
  addDef sp.recName b.recLevelParams ty val (compile := false)
  markElabAsElim sp.recName

/-! ### Making the recursors computable

The code generator compiles no recursor application -- `X.rec` no more than
`Nat.rec` -- so a `mutualRec` whose body is one would be `noncomputable`, and so
would everything downstream.  That defeats the purpose: the data members are kept
as ordinary inductives so the block stays computable, and `mutualRec` is the only
way to write a recursion that crosses members.

The restriction is on the shape of the term, not on the function: the same
recursion written by cases compiles, in a lowered block and in an ordinary
`mutual` one alike.  So each data member's `mutualRec` is paired with an
*implementation*

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

Nothing here is taken on trust.  The implementation is an ordinary `def`, handed
to Lean's structural recursion (`Structural.structuralRecursion`, not
`addPreDefinitions`, which falls back to `partial` or `sorry` on failure), so it
is accepted only if that machinery sees it terminates.  The theorem is an ordinary
proof, checked by the kernel.  A wrong one is an error at the point of the block,
which is where to find out that the proof generator needs work; an unchecked
companion the code generator believes would be a miscompilation.

`mutualRec` itself is untouched: the iota rules and `#print axioms` are unchanged,
and `eq_impl`'s use of `funext` stays inside `eq_impl`.  A `Prop` member needs no
implementation: its recursor's result is a `Prop`, so the recursor is a proof and
is erased.

The implementations recurse directly only within their own SCC.  For a field in an
earlier SCC an implementation calls that member's `mutualRec`, whose `@[csimp]`
theorem is registered by then and rewrites the call when the code generator
reaches it.  That keeps each proof one congruence deep and threads nothing across
components by hand.
-/

/-- The computable implementation of `X_i.mutualRec`. -/
def Block.implName (b : Block) (i : Nat) : Name := b.recName i ++ `impl

/-- The `@[csimp]` theorem `@X_i.mutualRec = @X_i.mutualRec.impl`. -/
def Block.implEqName (b : Block) (i : Nat) : Name := b.recName i ++ `eq_impl

/-! A *slot* is a position among the block's motives: a member below `b.size`, a
type the kernel denested above it.  The implementations are written over slots
throughout, since a member's recursion into a nesting and back is one mutual
recursion and must be defined as one. -/

/-- What a slot's own `NestSpec` calls something, or what the block calls it at a
member.  Every name asked of a slot goes through this. -/
private def slotName (ns : Nests) (e : Nat) (ofNest : NestSpec → Name)
    (ofMember : Nat → Name) : Name :=
  match ns.spec? e with
  | some sp => ofNest sp
  | none => ofMember e

/-- The block-wide recursor for a slot. -/
private def slotRecName (b : Block) (ns : Nests) (e : Nat) : Name :=
  slotName ns e (·.recName) b.recName

/-- Its implementation. -/
private def slotImplName (b : Block) (ns : Nests) (e : Nat) : Name :=
  slotName ns e (·.implName) b.implName

/-- Its `@[csimp]` theorem. -/
private def slotImplEqName (b : Block) (ns : Nests) (e : Nat) : Name :=
  slotName ns e (·.implEqName) b.implEqName

/-- Which slot an induction hypothesis is about, and how many arguments it is
lifted through.  Its conclusion applies exactly one motive, so neither is guessed
from the field it came from. -/
private def ihSlot (motives : Array Expr) (ihTy : Expr) : MetaM (Nat × Nat) :=
  forallTelescope ihTy fun ys body => do
    let some e := motives.findIdx? (· == body.getAppFn)
      | throwError "(internal) multiuniverse lowering: an induction hypothesis is about none \
          of the block's motives:{indentExpr ihTy}"
    return (e, ys.size)

/--
An induction hypothesis of type `ihTy`, built by recursing with `nameOf` on the
slot the hypothesis is about. -/
private def implIH (levels : List Level) (nameOf : Nat → Name)
    (params motives minors : Array Expr) (ihTy : Expr) : MetaM Expr :=
  forallTelescope ihTy fun ys body => do
    let (e, _) ← ihSlot motives (← mkForallFVars ys body)
    mkLambdaFVars ys
      (mkAppN (mkConst (nameOf e) levels) (params ++ motives ++ minors ++ body.getAppArgs))

/-- A minor premise of a block-wide recursor, applied to a constructor's fields
and to induction hypotheses built by recursing.  `casesOn` offers no hypotheses,
so which ones are needed is read off the minor premise's own type. -/
private def applyMinor (levels : List Level) (nameOf : Nat → Name)
    (params motives minors : Array Expr) (minor : Expr) (fields : Array Expr) : MetaM Expr := do
  forallTelescope (← instantiateForall (← inferType minor) fields) fun ihs _ => do
    let vals ← ihs.mapM fun ih => do
      implIH levels nameOf params motives minors (← inferType ih)
    return mkAppN minor (fields ++ vals)

/--
One `casesOn` at `motive`, with every induction hypothesis its minor premises
ask for supplied by a direct call. -/
private def mkCasesImplBody (b : Block) (ns : Nests) (group : Array Nat) (levels : List Level)
    (motive : Expr) (casesName : Name) (baseLvls : List Level) (cparams : Array Expr)
    (alts : Array (Nat × Expr)) (params motives minors idxs : Array Expr) (major : Expr) :
    MetaM Expr := do
  let mot ← forallTelescope (← inferType motive) fun zs _ =>
    mkLambdaFVars zs (mkAppN motive zs)
  let elim ← getLevel (mkAppN motive (idxs ++ #[major]))
  let casesFn := mkConst casesName (← elimLevelsFor casesName elim baseLvls)
  let ty0 ← instantiateForall (← inferType casesFn) cparams
  let ty1 ← instantiateForall ty0 #[mot]
  let ty2 ← instantiateForall ty1 (idxs ++ #[major])
  let nameOf (e : Nat) : Name :=
    if group.contains e then slotImplName b ns e else slotRecName b ns e
  let cminors ← buildArgs ty2 alts.size fun q minorTy => do
    let (numFields, minor) := alts[q]!
    -- `casesOn` offers no induction hypotheses, so its minor premise binds the
    -- fields and nothing else
    forallBoundedTelescope minorTy (some numFields) fun fields _ => do
      mkLambdaFVars fields (← applyMinor levels nameOf params motives minors minor fields)
  return mkAppN casesFn (cparams ++ #[mot] ++ idxs ++ #[major] ++ cminors)

/--
The body of `X_i.mutualRec.impl`: one `X_i.casesOn`, with every induction
hypothesis supplied by a direct call -- to a sibling's implementation inside
`group`, to `X_j.mutualRec` outside it, where that member's `@[csimp]` theorem
takes over. -/
private def mkImplBody (b : Block) (ns : Nests) (group : Array Nat) (levels : List Level)
    (i : Nat) (params motives minors idxs : Array Expr) (major : Expr) : MetaM Expr := do
  let (casesName, base, cparams) := b.memberCasesOf i params
  let mut alts : Array (Nat × Expr) := #[]
  for q in *...b.allCtors.size do
    if b.allCtors[q]!.owner == i then
      alts := alts.push (b.allCtors[q]!.numFields, minors[q]!)
  mkCasesImplBody b ns group levels motives[i]! casesName base cparams alts
    params motives minors idxs major

/-- The same, for the implementation of a recursor over a type the kernel denested. -/
private def mkNestImplBody (b : Block) (ns : Nests) (group : Array Nat) (levels : List Level)
    (sp : NestSpec) (params motives minors idxs : Array Expr) (major : Expr) : MetaM Expr := do
  let dinfo ← getConstInfoInduct sp.head
  let majorTy ← whnf (← inferType major)
  let dparams := majorTy.getAppArgs.extract 0 dinfo.numParams
  let alts ← dinfo.ctors.toArray.mapIdxM fun q cn =>
    return ((← getConstInfoCtor cn).numFields, minors[sp.firstMinor + q]!)
  mkCasesImplBody b ns group levels motives[sp.motive]! (sp.head ++ `casesOn)
    majorTy.getAppFn.constLevels! dparams alts params motives minors idxs major

/--
Open the telescope of `X_i.mutualRec` -- `{params} {motive_1 .. motive_n}
(case_1 .. case_K) {idxs} (t)` -- and pass `k` the whole telescope and each of
its five parts. -/
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

/--
The constructors of the slots in `group`, in the order the recursor whose
motives range over exactly `group` expects its minor premises. -/
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
by induction on `major` with `X_i.rec`. -/
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
      -- for, and no others
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
theorems. -/
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
  -- `structuralRecursion` throws if it cannot see that the definitions terminate;
  -- `addPreDefinitions` would fall back to `partial` or `sorry`, the silent
  -- degradation this avoids
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
      -- `∀ args, f args = g args` becomes `f = g`, which up to eta is
      -- `@X_i.mutualRec = @X_i.mutualRec.impl`, the shape `csimp` wants
      for k in *...xs.size do
        pf ← mkFunExt (← mkLambdaFVars #[xs[xs.size - 1 - k]!] pf)
      return pf
    let type ← mkEq (mkConst (slotRecName b ns i) levels) (mkConst (slotImplName b ns i) levels)
    addDecl (.thmDecl
      { name := slotImplEqName b ns i, levelParams := info.levelParams, type, value })
    Compiler.CSimp.add (slotImplEqName b ns i) .global

/--
Implementations for a homogeneous block, whose `mutualRec`s are aliases of the
native recursors and so have the native signature: one elimination universe for
the whole block rather than one per component, and motives ranging over every
member. -/
private def emitNativeImpls (b : Block) : TermElabM Unit := do
  -- compile the aliases as they stand: this erases the small-eliminating ones and
  -- leaves anything else `noncomputable`, as its own `rec` is
  let compileAliases : TermElabM Unit := do
    for i in *...b.size do
      Lean.compileDecl (.defnDecl (← getConstInfoDefn (b.recName i))) (logErrors := false)
  -- an all-`Prop` homogeneous block computes nothing, so it needs no
  -- implementation
  if b.members.all (·.isProp) then
    return ← compileAliases
  let info ← getConstInfoRec (b.members[0]!.name ++ `rec)
  -- the native recursor of a mutual block ranges over every member; if a future
  -- change makes that false, fall back to the aliases as they stand
  unless info.numParams == b.numParams && info.numMotives == b.size
      && info.numMinors == b.allCtors.size do
    return ← compileAliases
  -- a homogeneous block that is not all-`Prop` has no `Prop` member, so every
  -- member is in one of the data SCCs
  for s in *...b.sccs.size do
    emitImplGroup b (Nests.empty b.sccs.size) b.sccs[s]! (Array.range b.size)

/-- Lower an elaborated multiuniverse block to ordinary declarations. -/
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
  -- what the kernel denested is knowable only once it has been handed the block
  let (b, ns) ← mkNests b
  if b.hasProp then
    for s in *...b.sccs.size do
      emitSquashSCC b s
    emitPropCtors b
    for i in *...b.size do
      if b.members[i]!.isProp then
        emitRec b ns i
  -- one SCC at a time, so an implementation's calls into an earlier component are
  -- already backed by a `@[csimp]` theorem
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
