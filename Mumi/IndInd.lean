/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Mumi.Options
public import Mumi.Lowering
public import Mumi.Runtime
public import Mumi.View
public import Mumi.Owned
public import Lean.Elab.MutualInductive
import all Lean.Elab.MutualInductive
import all Lean.Meta.Injective

/-!
# Induction-induction, when the dependency runs only through `Prop`

A block is *induction-inductive* when one member's **arity** mentions another,

```lean
mutual
inductive Ctx : Type where
  | nil  : Ctx
  | snoc : (Γ : Ctx) → (x : String) → Fresh x Γ → Ctx
inductive Fresh : String → Ctx → Prop where
  | nil  : (x : String) → Fresh x .nil
  | snoc : (x y : String) → (Γ : Ctx) → (h : Fresh y Γ) → x ≠ y → Fresh x Γ →
      Fresh x (.snoc Γ y h)
end
```

`Fresh`'s arity mentions `Ctx`.  This obstruction differs from the one
`Mumi.Lowering` lifts: universe heterogeneity is a *check* on an elaborated
block, whereas here the block does not elaborate at all.  Lean elaborates every
member's arity before any member is in scope, so `Ctx` in `Fresh`'s arity is an
unknown identifier.

## Blocks that separate

The erasure is for members that are *simultaneous*.  Many blocks that reach this
module are not: `Fresh`'s arity mentions `Ctx` above, but if `Ctx` held no
`Fresh` then nothing would mention `Fresh`, and the two could be declared one
after the other.  `separationOrder?` builds the block's dependency graph over
both arities and constructor types.  If it is acyclic, the block is a sequence of
ordinary declarations, and each member is handed to Lean on its own in topological
order.

That is a strict improvement wherever it applies.  Each member is a genuine
`inductive`, with `match`, `deriving`, `injection`, `contradiction` and an
index-refining `cases`, all of which the erasure costs.  A nesting that mentions
a sibling is the sibling itself by the time the nesting is read, so no copy is
made and the kernel denests it.  What is given up is the block's *joint*
recursor: three separate declarations have three separate recursors, and a
statement over all of them has to be built in as many steps.  `set_option
mumi.separate false` keeps the block here and keeps that recursor.

Lean may still refuse a member on its own -- a nesting applied to a
constructor-local is the usual reason.  The split is therefore tentative, and a
block Lean will not read falls back to the erasure.

## The narrow class

This module handles **narrow** blocks: every field of a data constructor whose
type mentions a `Prop` member is itself a proof, and so can be *erased*.  A data
member's arity may also mention the block; where it does, the index is *deleted*
(see "What is allowed").  The example needs no deletion, so erasing the proofs
leaves an ordinary block:

```lean
inductive Ctx._pre : Type where
  | nil  : Ctx._pre
  | snoc : Ctx._pre → String → Ctx._pre

inductive Fresh._pre : String → Ctx._pre → Prop where
  | nil  (x : String) : Fresh._pre x .nil
  | snoc (x y : String) (Γ : Ctx._pre) (h : Fresh._pre y Γ) (hne : x ≠ y)
      (hx : Fresh._pre x Γ) : Fresh._pre x (.snoc Γ y)
```

`Ctx._pre` has forgotten which of its elements are real `Ctx`s, so a predicate
puts that back.  It is a *function*, not an inductive:

```lean
def Ctx._wf : Ctx._pre → Prop :=
  Ctx._pre.rec (motive := fun _ => Prop) True (fun Γ x ih => ih ∧ Fresh._pre x Γ)

def Ctx   := { Γ : Ctx._pre // Ctx._wf Γ }
def Fresh (x : String) (Γ : Ctx) : Prop := Fresh._pre x Γ.val
```

Being a function makes the encoding cheap: `Ctx._wf (.snoc Γ x)` is definitionally
`Ctx._wf Γ ∧ Fresh._pre x Γ`, so inversion is `And.left` and `And.right`.  There
is one conjunct per recursive field (the sub-term is well formed) and one per
erased field (the proof it carried).  The constructors are then definitions, and
the recursor is structural recursion on the pre-type with the well-formedness
proof threaded through:

```lean
def Ctx.recAux {C : Ctx → Sort u} (nil : C Ctx.nil)
    (snoc : (Γ : Ctx) → (x : String) → (h : Fresh x Γ) → C Γ → C (Ctx.snoc Γ x h)) :
    (Γ₀ : Ctx._pre) → (w : Ctx._wf Γ₀) → C ⟨Γ₀, w⟩
  | .nil,          _ => nil
  | .snoc Γ₀ x,    w => snoc ⟨Γ₀, w.1⟩ x w.2 (Ctx.recAux nil snoc Γ₀ w.1)

def Ctx.rec {C : Ctx → Sort u} .. (Γ : Ctx) : C Γ :=
  Ctx.recAux nil snoc Γ.val Γ.property
```

Both iota rules hold by `rfl`, and the encoding adds no axioms.  It rests on the
two facts the heterogeneous lowering rests on: definitional proof irrelevance,
which collapses the `_wf` proofs, and definitional eta for structures, which
gives `⟨Γ.val, Γ.property⟩ ≡ Γ`.  `recAux` is structural recursion rather than a
`Ctx._pre.rec` application for the reason given in `Mumi.Lowering`: the code
generator compiles no recursor application.

A `Prop` member's recursor needs none of that, since `Fresh` *is* `Fresh._pre` at
the `.val`s of its indices.  Only the world `Fresh._pre.rec`'s motive and minors
are stated in is wrong, so it is run at the transported motive
`fun Γ₀ h => ∀ w, C ⟨Γ₀, w⟩ h` and applied to the major premise's own indices,
where `⟨Γ.val, Γ.property⟩ ≡ Γ` closes it.  See `addPropRecs`.

## What is allowed

* Any number of data and `Prop` members, in any universes.  The data members
  become one mutual pre-block, emitted through `Mumi.Lowering` so that the
  kernel's same-universe rule is lifted (see `emitPreData`).  The two passes are
  independent: erasure never inspects a universe, and the lowering never sees an
  arity that mentions the block.  Rules underneath the lifted one still apply:
  data members that recurse into *one another* must agree on their universe, and
  a field must fit inside its member.
* Parameters and auto-bound implicits, shared by the whole block.
* Universe parameters, declared or auto-bound, shared by the whole block.  A
  *data* member may not sit at a bare `Sort u`: its wrapper lands in
  `Sort (max 1 u)`, which is `Sort u` only for visibly non-zero `u`.
* A member may omit its resulting type -- `inductive Tree where` -- and it is read
  as `Type`.  A metavariable cannot go into the scratch axiom.  A block the guess
  is too small for is rejected with the type to write.
* Members named under one another -- `TreeNested.WF` beside `TreeNested`.
  Constructors are known by name, so nothing is read off a prefix.
* Indices on any member, a *data* member included -- `Ty : Ctx → Type` beside
  `Ctx`, and `Tm : (Γ : Ctx) → Ty Γ → Type` beside both.  An index of a data member
  that mentions the block is *deleted*: `Ty._pre` carries no index and the
  well-formedness puts a `Ctx._pre` back.  Such an index must be a data member's
  own type applied outright, what remains after deletion must name no other index,
  and an index that *stays* may mention none that goes.  See `checkDropped`.
* A constructor of such a member either takes a deleted index as a field or
  *builds* it from its fields and the block's constructors, in which case the
  well-formedness carries an equation stating what was built.  It may build
  several, build one out of another, and supply one field as several.  See
  `Block.transportBuilt`.
* Recursive fields may be indexed and infinitary -- `(f : (n : Nat) → Vec n)` --
  provided the binders `ys` mention no member of the block.  `(f : Ctx → Ctx)` is
  rejected, not for positivity but because a `Ctx._pre` cannot become a `Ctx`
  without its well-formedness proof, leaving nothing to pass `f`.
* A member that takes no part in the erasure *leaves the block* and is declared as
  the ordinary inductive it already is.  Two kinds qualify, for opposite reasons:
  a proposition nothing else in the block is stated with, and a data member
  nothing else in the block reaches.  See `markPeeled`.

  The second kind needs a fixpoint, a member the block still reaches being
  possibly reached only by another that is itself leaving: `Sub.ext` reads a `Tm`,
  so `Tm` cannot go while `Sub` is there, but can once `Sub` has gone.  Members
  leave until no more can, subject to two conditions: what stays must still be
  induction-inductive, or no recursor of ours is left to widen, and what leaves
  must not be induction-inductive among itself.

  A member that leaves gains `match`, and with it the equation compiler,
  `injection` and `contradiction`.  The block loses nothing:
  `widenWithPeeled` puts the departed motive back into every recursor.  A *data*
  member that leaves is declared as `X._ind`, with the writer's name a definition
  unfolding to it (see `peelIndName`), the kernel writing `X.rec` for whatever it
  is handed as an inductive `X`.  Its constructors keep the writer's names, and
  `X._ind.c` is aliased to `X.c` so dot-notation resolves against either head.

## Nested inductives that denest to this

Lean builds induction-inductive blocks on its own.  A *nested* inductive is
denested by specialising the nesting type constructor to the block, and if that
type is itself a family indexed by another type being specialised, the enlarged
block is induction-inductive.  The smallest such case is a tree that is
well-formed by construction and stores itself:

```lean
inductive Tree (α : Type u) where
  | empty
  | node (key : Nat) (value : α) (l r : Tree α)
inductive Tree.WFWith (α : Type u) : Tree α → List Nat → Prop where ..
inductive Tree.WF (α : Type u) : Tree α → Prop where
  | intro (l : List Nat) (t : Tree α) (h : Tree.WFWith α t l) : Tree.WF α t
inductive WFTree (α : Type u) : Type u where
  | mk (x : Tree α) (h : x.WF)

inductive RecWFTree where
  | mk (x : WFTree RecWFTree)
```

Copying `WFTree` at `RecWFTree` drags in `Tree`, and copying `Tree` drags in
`Tree.WF` and `Tree.WFWith`, whose arities are indexed by the copy of `Tree`, so
Lean must check a five-member block:

```lean
mutual
inductive RecWFTree                             : Type
inductive RecWFTree.nested_WFTree_1             : Type
inductive RecWFTree.nested_Tree_2               : Type
inductive RecWFTree.nested_WF_3     : RecWFTree.nested_Tree_2 → Prop
inductive RecWFTree.nested_WFWith_4 : RecWFTree.nested_Tree_2 → List Nat → Prop
end
```

which is a narrow-class induction-inductive block: only the `Prop` members'
arities mention the block.  `denestRaw` builds it and `prepareCore` lowers it,
and `Mumi.Declaration` reaches this path only after Lean itself and the
heterogeneous retry have both failed.  `Mumi.Denest` does the same job for the
blocks `Mumi.Lowering` takes, but is not reusable here: it rewrites an `Input`
over member *free variables* and only at the head of an application, whereas here
the members are constants and a copied constructor can appear in an *index*.

Two shapes cost the copies more than an extra constructor.  A nesting type that
is part of a `mutual` family is copied with the whole family.  A nesting whose
parameters mention a *field* of the constructor it sits in -- `OkFam LocalsII n`
for a field `n` -- gains `n` as an index of the copy, and every constructor of
the copy takes it as a leading field.  Both survive the erasure: by the time
`prepareCore` sees it the copy is a member like any other.

## What this does not do

* Section `variable`s.
* An erased field's type may not mention a *data* member as a constant.
  `(h : Fresh x Γ)` is fine, `Fresh x Γ` unfolding to `Fresh._pre x Γ.val`, so
  erasing it is definitionally invisible; `(h : Γ = Γ')` is not, since `Γ = Γ'`
  and `Γ.val = Γ'.val` are different propositions and the encoding would have to
  transport between them.
* A data constructor's field mentioning a `Prop` member must be a proof; that is
  the "narrow" in narrow class.
* The constructors of a data member that *stayed* are `def`s, so `match` does not
  work on them.  (A member that left is a real inductive.)  `Mumi.addViews` adds
  `casesOn`, `recOn`, `ctorIdx`, `noConfusionType` and `noConfusion` under the
  expected names, stated about the member, and a `Prop` member gets the two
  eliminators too; `inj` and a `@[simp] injEq` come from
  `addInjEqs`, and a simproc distinguishes two *different* constructors.  What
  reduces the equation before it looks does not benefit: `contradiction` and
  `injection` reach for the `noConfusion` of what the member unfolds to, which is
  the wrapper's.  A bare `induction` or `cases` does work and names the
  constructors that were written.  A recursor with a *single* motive is
  registered as the `induction` tactic's default; a block whose members recurse
  into each other has one motive per member and stays `using`-only, as in vanilla
  Lean, so reason with
  `induction Γ using Ctx.rec with | nil => .. | snoc Γ x h ih => ..`.
* A bare `cases` on a `Prop` member works only where the motive does not depend on
  the indices; otherwise it fails with "dependent elimination failed", reaching for
  `Fresh._pre`'s `casesOn`.  Use
  `induction x, Γ, h using Fresh.rec with | nil .. | snoc ..`, listing the indices
  as targets.
* A `Prop` member that joins the recursion over the whole block eliminates into
  `Prop` only, even where its own recursor would eliminate into any sort: its
  hypothesis rides in a bundle beside a data member's, and a bundle holds its
  `Prop` half in a conjunction.  A subsingleton judgement therefore trades large
  elimination for the other half of the recursion.
* A block that both names a `Prop` member at a deleted index -- `Wf.base :
  (Γ : Ctx) → Ok Γ → Wf Γ (Ty.base Γ)`, where `Ty.base` deleted the `Γ` -- and
  deletes an index built out of a constructor -- `Ty.pi : (Γ : Ctx) → (A : Ty Γ)
  → Ty (Γ.snoc A) → Ty Γ`.  Both turn on what a deleted index arrives under, and
  they need opposite things: the first the whole bundle, to state a hypothesis
  with, the second the motive's value alone, the only half a minor can rebuild.
  Either alone succeeds, and both are tried.
* Two copies that need each other, an original nested inside another original,
  have no order to build the bridge in.  This is reported and the bridge dropped
  as a whole, as whenever any step of it fails.
* A *data* member leaves the block only where the block holds no propositions, a
  bundled `Prop` motive surviving neither the motive order nor a hypothesis at a
  proof field when restated from outside; and only where what stays is still
  induction-inductive.
* A data member that left prints as `X._ind` in the types of its own constructors
  and nowhere else -- `Tm.lam : .. → Tm._ind (Γ.snoc A) B → Tm._ind Γ
  (Ty.pi Γ A B)` -- constructor types being the one place the kernel will not
  accept a definition standing in for the inductive.  The recursors, the
  eliminators `induction` and `cases` reach for, and the goals they leave all
  read `Tm`.
* A recursor over a data member that left is a recursor application, which the
  code generator does not compile, so it is published beside an `unsafe` companion
  written out of `casesOn` and a self-call and wired up with `setImplementedBy`.
  A group of data members that left *together* is genuinely mutual, so the kernel
  recursor has one motive per member; such a group gets no companion.
-/

public section

namespace Mumi.IndInd

open Lean Lean.Meta Lean.Elab Lean.Elab.Command
open Lean.Elab.MultiuniverseInductive
  (addDef addInd reroot motiveNames markElabAsElim addSoloElim attempt?
    attempted freshLevelNames shortName exposeInduct proveBy ctorTypeAt)

/-- Why a block fell back from the recursor it would rather have had. -/
initialize registerTraceClass `Mumi.indind (inherited := true)

/-! ## Names -/

/-- The erased pre-type of member `n`. -/
def preName (n : Name) : Name := n ++ `_pre

/-- `X._wf : ∀ idxs, X._pre idxs → Prop`, well-formedness on the pre-type. -/
def wfName (n : Name) : Name := n ++ `_wf

/--
`X._sub args`, the one-constructor inductive pairing a pre-value with its
well-formedness proof; a data member unfolds to this. -/
def subName (n : Name) : Name := n ++ `_sub

/-- The `_sub` wrapper `ty` is, if it is one: its head, levels and arguments. -/
def subOf? (ty : Expr) : Option (Name × List Level × Array Expr) :=
  match ty.getAppFn with
  | .const n@(.str _ "_sub") us => some (n, us, ty.getAppArgs)
  | _ => none

/--
`X._ind`, the inductive a peeled member is declared as when `X` itself must stay
a definition, `X.rec` being owed to the whole block.  See step 11 of `emit`. -/
def peelIndName (n : Name) : Name := n ++ `_ind

/--
The recursor over *all* of the data pre-block, which `X._wf` recurses with:
`X._pre.rec` for one mutual inductive, `mutualRec` for a lowered one. -/
def preDataRecName (heterogeneous : Bool) (n : Name) : Name :=
  preName n ++ (if heterogeneous then `mutualRec else `rec)

/-! ## The block, as we analyse it -/

/-- What becomes of one field of a constructor under erasure. -/
inductive FieldKind where
  /-- Mentions no member of the block; kept as it stands. -/
  | plain
  /-- `∀ ys, M args` for the member at index `mem`; kept, at the pre-type. -/
  | recur (mem : Nat)
  /-- A proof mentioning a `Prop` member; dropped, and remembered by `_wf`. -/
  | erased
  /--
  A value of the member `mem` that is also the resulting type's index at
  position `pos`; dropped, and given back as an argument of `_wf`. -/
  | deleted (mem : Nat) (pos : Nat)
  deriving Inhabited, DecidableEq, Repr

structure CtorSpec where
  name  : Name
  /-- `∀ params fields, M args`, with the members and their constructors as constants. -/
  type  : Expr
  kinds : Array FieldKind
  deriving Inhabited

structure MemberSpec where
  name   : Name
  /-- `∀ params idxs, Sort l`, with the members as constants. -/
  type   : Expr
  isProp : Bool
  /-- The `l` of the resulting `Sort l`. -/
  level  : Level
  /--
  Which of the member's indices the pre-type drops, counting from the first one
  after the parameters: those whose type mentions the block. -/
  dropped : Array Nat := #[]
  /--
  Which of the deleted indices a recursion is handed a hypothesis about: those at
  a *data* member's type, in the same numbering as `dropped`. -/
  dropIhs : Array Nat := #[]
  ctors  : Array CtorSpec
  deriving Inhabited

structure Block where
  members : Array MemberSpec
  /-- The block's parameters, which lead every member's arity and every field telescope. -/
  numParams : Nat
  /--
  The universe parameters, shared by every declaration the lowering makes.  A
  member that does not mention one still carries it. -/
  us : List Name := []
  /--
  The name a constructor is emitted under; the identity where the block was not
  denested. -/
  rawCtor : Name → Name := id
  /-- The name a member is emitted under; as `Block.rawCtor`, one level up. -/
  rawMember : Name → Name := id
  deriving Inhabited

def Block.size (b : Block) : Nat := b.members.size

/-- An expression with every constructor and member of the block named the way it
is really emitted; see `Block.rawCtor` and `Block.rawMember`. -/
def Block.toRaw (b : Block) (e : Expr) : Expr :=
  e.replace fun
    | .const n us =>
      let r := b.rawMember (b.rawCtor n)
      if r == n then none else some (.const r us)
    | _ => none

/--
The name a constructor was written under, given the one it is emitted as: the
inverse of `Block.rawCtor`, and the identity on anything else. -/
def Block.unRaw (b : Block) (n : Name) : Name := Id.run do
  for m in b.members do
    for c in m.ctors do
      if c.name != n && b.rawCtor c.name == n then return c.name
  return n

/--
A constructor's type at the block's parameters, named the way the block is
emitted. -/
def Block.ctorType (b : Block) (c : CtorSpec) (ps : Array Expr) : MetaM Expr :=
  return b.toRaw (← instantiateForall c.type ps)

/-- The block's universe parameters as levels. -/
def Block.lvls (b : Block) : List Level := b.us.map Level.param

/-- A constant of the block, at the block's own universe parameters. -/
def Block.cst (b : Block) (n : Name) : Expr := mkConst n b.lvls

/--
Member `i` as a constant, named the way it is emitted.  This agrees with the
written name except at a `Prop` member the bridge will restate. -/
def Block.memberCst (b : Block) (i : Nat) : Expr :=
  b.cst (b.rawMember b.members[i]!.name)

/-- Drop the leading parameters from an argument list, leaving the indices. -/
def Block.idxArgs (b : Block) (args : Array Expr) : Array Expr :=
  args.extract b.numParams args.size

/-- Drop the leading parameters from a constructor's field telescope. -/
def Block.fieldKinds (b : Block) (kinds : Array FieldKind) : Array FieldKind :=
  kinds.extract b.numParams kinds.size

/-- The members that are not propositions, in declaration order. -/
def Block.dataIdxs (b : Block) : Array Nat :=
  (Array.range b.size).filter (!b.members[·]!.isProp)

/-- The members that are propositions, in declaration order. -/
def Block.propIdxs (b : Block) : Array Nat :=
  (Array.range b.size).filter (b.members[·]!.isProp)

/-- The index of the member named `n`. -/
def Block.memberIdx? (b : Block) (n : Name) : Option Nat :=
  -- either name will do: a type read out of a raw declaration spells a renamed
  -- member the way it was emitted, and both names answer the same questions
  b.members.findIdx? fun m => m.name == n || b.rawMember m.name == n

/-- The index of the member whose *pre-type* is named `n`. -/
def Block.preIdx? (b : Block) (n : Name) : Option Nat :=
  b.members.findIdx? (preName ·.name == n)

/--
Where the minor premise for the constructor `n` sits in a recursor over the
members `idxs`: their constructors, in order, flattened. -/
def Block.minorIdx (b : Block) (idxs : Array Nat) (n : Name) : Nat := Id.run do
  let n := b.unRaw n
  let mut acc := 0
  for i in idxs do
    for c in b.members[i]!.ctors do
      if c.name == n then return acc
      acc := acc + 1
  return acc

/-- Whether the pre-world drops this field: an erased proof or a deleted index. -/
def FieldKind.isDropped : FieldKind → Bool
  | .erased | .deleted .. => true
  | _ => false

/-- Whether this field is one of the resulting type's indices, and so deleted. -/
def FieldKind.isDeleted : FieldKind → Bool
  | .deleted .. => true
  | _ => false

/-- The positions of the fields a constructor keeps. -/
def keptPositions (kinds : Array FieldKind) : Array Nat := Id.run do
  let mut out := #[]
  for i in *...kinds.size do
    unless kinds[i]!.isDropped do out := out.push i
  return out

/-- The positions of a constructor's recursive fields. -/
def recPositions (kinds : Array FieldKind) : Array Nat := Id.run do
  let mut out := #[]
  for i in *...kinds.size do
    if let .recur _ := kinds[i]! then out := out.push i
  return out

/--
The member a minor premise's induction hypothesis about this field is stated at,
and `none` for a field with no hypothesis. -/
def FieldKind.ihTarget? : FieldKind → Option Nat
  | .recur m | .deleted m _ => some m
  | _ => none

@[inherit_doc FieldKind.ihTarget?]
def FieldKind.hasIh (k : FieldKind) : Bool := k.ihTarget?.isSome

/-- The positions of the fields a minor premise takes an induction hypothesis
about, in the order the telescope binds them.  See `FieldKind.hasIh`. -/
def ihPositions (kinds : Array FieldKind) : Array Nat := Id.run do
  let mut out := #[]
  for i in *...kinds.size do
    if kinds[i]!.hasIh then out := out.push i
  return out

/--
The field the constructor deleted along with the index at position `pos`, if the
index was a field. -/
def deletedField? (kinds : Array FieldKind) (pos : Nat) : Option Nat := Id.run do
  for k in *...kinds.size do
    if let .deleted _ p := kinds[k]! then
      if p == pos then return some k
  return none

/--
`FieldKind.ihTarget?` with the propositions removed; the recursion has no
hypothesis to pass about those.  See `MemberSpec.dropIhs`. -/
def Block.ihTarget? (b : Block) (k : FieldKind) : Option Nat :=
  match k.ihTarget? with
  | some m => if b.members[m]!.isProp then none else some m
  | none   => none

@[inherit_doc Block.ihTarget?]
def Block.hasIh (b : Block) (k : FieldKind) : Bool := (b.ihTarget? k).isSome

/-- `ihPositions` with the propositions taken out; see `Block.ihTarget?`. -/
def Block.ihPositions (b : Block) (kinds : Array FieldKind) : Array Nat := Id.run do
  let mut out := #[]
  for i in *...kinds.size do
    if b.hasIh kinds[i]! then out := out.push i
  return out

/-- Which entries of `Block.dropIdxs` and `Block.dropArgs` carry a hypothesis:
see `MemberSpec.dropIhs`. -/
def Block.ihSlots (b : Block) (i : Nat) : Array Nat := Id.run do
  let m := b.members[i]!
  let mut out : Array Nat := #[]
  for q in *...m.dropped.size do
    if m.dropIhs.contains m.dropped[q]! then out := out.push q
  return out

/-- The deleted indices that carry a hypothesis, out of all of them in arity
order; `dels` is a `Block.dropIdxs` or `Block.dropArgs`. -/
def Block.ihDrops (b : Block) (i : Nat) (dels : Array Expr) : Array Expr :=
  (b.ihSlots i).map (dels[·]!)

/-- Whether the deleted index at arity position `p` of member `i` is one of the
block's propositions, equivalently whether it goes without a hypothesis.  Ask
only of positions that are deleted: any other answers `true`. -/
def Block.dropAtProp (b : Block) (i p : Nat) : Bool :=
  !b.members[i]!.dropIhs.contains p

/-- Whether the pre-type of the member `i` keeps the argument at position `k`. -/
def Block.keepsArg (b : Block) (i k : Nat) : Bool :=
  k < b.numParams || !b.members[i]!.dropped.contains (k - b.numParams)

/-- A member's indices with the ones its pre-type dropped taken out. -/
def Block.keptIdxs (b : Block) (i : Nat) (idxs : Array Expr) : Array Expr :=
  if b.members[i]!.dropped.isEmpty then idxs
  else (Array.range idxs.size).filterMap fun p =>
    if b.members[i]!.dropped.contains p then none else idxs[p]?

/-- Just the indices the pre-type dropped: the member's block-typed ones. -/
def Block.dropIdxs (b : Block) (i : Nat) (idxs : Array Expr) : Array Expr :=
  b.members[i]!.dropped.filterMap (idxs[·]?)

/-- `Block.keptIdxs`, counting from a member application's first argument. -/
def Block.keptArgs (b : Block) (i : Nat) (args : Array Expr) : Array Expr :=
  if b.members[i]!.dropped.isEmpty then args
  else args.take b.numParams ++ b.keptIdxs i (args.extract b.numParams args.size)

/-- `Block.dropIdxs`, counting from a member application's first argument. -/
def Block.dropArgs (b : Block) (i : Nat) (args : Array Expr) : Array Expr :=
  b.dropIdxs i (args.extract b.numParams args.size)

/-- `X ↦ X._pre`, and `X.c ↦ X._pre.c` for a constructor of `X`. -/
def Block.preOf (b : Block) (n : Name) : Name := Id.run do
  let n := b.unRaw n
  for m in b.members do
    if n == m.name then return preName m.name
    for c in m.ctors do
      if n == c.name then return reroot m.name (preName m.name) c.name
  return n

/-- The fields a data constructor keeps, or `none` if `n` is not one. -/
def Block.keptOf (b : Block) (n : Name) : Option (Array Nat) := Id.run do
  let n := b.unRaw n
  for m in b.members do
    unless m.isProp do
      for c in m.ctors do
        if n == c.name then return some (keptPositions c.kinds)
  return none

/--
`e` rewritten to the pre-world: members and their constructors are re-rooted, and
what the pre-world drops goes with them -- a member's deleted indices, a data
constructor's erased and deleted arguments. -/
partial def Block.tr (b : Block) (e : Expr) : Expr :=
  match e with
  | .const n us => .const (b.preOf n) us
  | .app .. =>
    e.withApp fun f args =>
      let args := args.map b.tr
      match f with
      | .const n us =>
        match b.memberIdx? n with
        | some i => mkAppN (.const (b.preOf n) us) (b.keptArgs i args)
        | none =>
          match b.keptOf n with
          | some ks => mkAppN (.const (b.preOf n) us) (ks.filterMap fun i => args[i]?)
          | none    => mkAppN (.const (b.preOf n) us) args
      | _ => mkAppN (b.tr f) args
  | .lam n d v bi     => .lam n (b.tr d) (b.tr v) bi
  | .forallE n d v bi => .forallE n (b.tr d) (b.tr v) bi
  | .letE n t v x nd  => .letE n (b.tr t) (b.tr v) (b.tr x) nd
  | .mdata d x        => .mdata d (b.tr x)
  | .proj s i x       => .proj s i (b.tr x)
  | _ => e

/--
Whether `n` is a member of the block, or a constructor of one, among the members
`keep` selects. -/
def Block.named (b : Block) (keep : MemberSpec → Bool) (n : Name) : Bool :=
  let n := b.unRaw n
  b.members.any fun m => keep m && (n == m.name || m.ctors.any (·.name == n))

/-- Whether `e` mentions any member of the block, or any of their constructors. -/
def Block.mentions (b : Block) (e : Expr) : Bool :=
  e.getUsedConstants.any (b.named (fun _ => true))

/-- Whether `e` mentions any *data* member of the block as a constant. -/
def Block.mentionsData (b : Block) (e : Expr) : Bool :=
  e.getUsedConstants.any (b.named (!·.isProp))

/-- Whether `e` mentions any `Prop` member of the block as a constant. -/
def Block.mentionsProp (b : Block) (e : Expr) : Bool :=
  e.getUsedConstants.any (b.named (·.isProp))

/--
Put the block's own constants at one shared list of levels, disposing of the
unassigned metavariables a scratch axiom's reference carries. -/
def normLevels (names : Array Name) (lvls : List Level) (e : Expr) : Expr :=
  e.replace fun s =>
    match s with
    | .const n _ => if names.contains n then some (.const n lvls) else none
    | _ => none

/-! ## Members applied to their indices

The data member `X` at indices `args` is the subtype of `X._pre args` cut out by
`X._wf args`.  Everything crossing between the two worlds goes through these
five.  `args` are always the pre-world's. -/

/-- The pre-types of the indices member `i` dropped, at parameters `ps`. -/
def Block.dropTys (b : Block) (i : Nat) (ps : Array Expr) : MetaM (Array Expr) := do
  if b.members[i]!.dropped.isEmpty then return #[]
  forallTelescope (← instantiateForall b.members[i]!.type ps) fun idxs _ => do
    let ds := b.dropIdxs i idxs
    ds.mapIdxM fun q x => do
      mkLambdaFVars (b.keptIdxs i idxs ++ ds.extract 0 q) (b.tr (← inferType x))

/-- `Block.dropTys` read at a member's indices, of which only the kept ones are
looked at; each entry is still a function of the dropped indices before it.
`idxs` counts from the member's first index, not its first argument. -/
def Block.dropTysAt (b : Block) (i : Nat) (ps idxs : Array Expr) : MetaM (Array Expr) := do
  return (← b.dropTys i ps).map (·.beta (b.keptIdxs i idxs))

/--
Bind a member's dropped indices one at a time, each at its type read at the ones
before it.  `Block.dropTysAt` leaves that dependency standing. -/
partial def withDropTele {α} [Inhabited α] (dts : Array Expr) (q : Nat) (acc : Array Expr)
    (k : Array Expr → MetaM α) : MetaM α := do
  if h : q < dts.size then
    withLocalDeclD `d (dts[q].beta acc) fun d => withDropTele dts (q + 1) (acc.push d) k
  else
    k acc

/-- `∀ dropped, e`, the dropped indices bound in order; see `withDropTele`. -/
def mkDropForall (dts : Array Expr) (e : Expr) : MetaM Expr :=
  withDropTele dts 0 #[] fun ds => mkForallFVars ds e

/-- `ts[0] → .. → ts[n-1] → e`, with nothing depending on anything. -/
def mkArrows (ts : Array Expr) (e : Expr) : Expr :=
  ts.foldr (fun t acc => .forallE `a t acc .default) e

/--
The sort every motive of the `X._wf` recursion lands in: the `max` of `Type` and
the sorts of the member's deleted indices, a motive ending in those and then
`Prop`. -/
def Block.wfMotiveLevel (b : Block) (ps : Array Expr) : MetaM Level := do
  let mut l := Level.one
  for i in b.dataIdxs do
    -- a level names no binder, so the arity's own are as good as anyone's
    let ls ← forallTelescope (← instantiateForall b.members[i]!.type ps) fun idxs _ => do
      withDropTele (← b.dropTysAt i ps idxs) 0 #[] fun ds =>
        ds.mapM fun d => do getLevel (← inferType d)
    for x in ls do
      l := (mkLevelMax l x).normalize
  return l

/--
The extra argument every motive of the `X._wf` recursion ends in when the motives
would not otherwise share a sort, and the value that fills it; empty when they
agree. -/
def wfPad (l : Level) : Array Expr × Array Expr :=
  if l == Level.one then (#[], #[])
  else (#[mkConst ``PUnit [l]], #[mkConst ``PUnit.unit [l]])

/--
A member's indices with each deleted one rebound at its pre-type; every other
index keeps the arity's own binder. -/
def Block.withValIdxs {α} [Inhabited α] (b : Block) (i : Nat) (ps idxs : Array Expr)
    (k : Array Expr → MetaM α) : MetaM α := do
  let dropped := b.members[i]!.dropped
  if dropped.isEmpty then return ← k idxs
  let dts ← b.dropTysAt i ps idxs
  let mut decls : Array (Name × (Array Expr → MetaM Expr)) := #[]
  for q in *...dropped.size do
    let n ← idxs[dropped[q]!]!.fvarId!.getUserName
    decls := decls.push (n, fun prev => pure (dts[q]!.beta prev))
  withLocalDeclsD decls fun ds => do
    let mut out := idxs
    for q in *...dropped.size do
      out := out.set! dropped[q]! ds[q]!
    k out

/-- `X._pre args`, with the indices the pre-type dropped taken out of `args`. -/
def Block.preApp (b : Block) (i : Nat) (args : Array Expr) : Expr :=
  mkAppN (b.cst (preName b.members[i]!.name)) (b.keptArgs i args)

/--
`X._wf args`, a predicate on `X._pre args`.  `_wf` keeps every index the arity
had, a deleted one being what the pre-term no longer states. -/
def Block.wfApp (b : Block) (i : Nat) (args : Array Expr) : Expr :=
  mkAppN (b.cst (wfName b.members[i]!.name)) args

/-- `X._sub args`, the wrapper that `X args` unfolds to. -/
def Block.subtype (b : Block) (i : Nat) (args : Array Expr) : Expr :=
  mkAppN (b.cst (subName b.members[i]!.name)) args

def Block.sVal (b : Block) (i : Nat) (args : Array Expr) (e : Expr) : Expr :=
  mkAppN (b.cst (subName b.members[i]!.name ++ `val)) (args.push e)

def Block.sProp (b : Block) (i : Nat) (args : Array Expr) (e : Expr) : Expr :=
  mkAppN (b.cst (subName b.members[i]!.name ++ `property)) (args.push e)

def Block.sMk (b : Block) (i : Nat) (args : Array Expr) (v p : Expr) : Expr :=
  mkAppN (b.cst (subName b.members[i]!.name ++ `mk)) (args ++ #[v, p])

/-! ## Recursive fields

A recursive field has type `∀ ys, M args` for a member `M`.  `ys` is empty in the
ordinary case and non-empty for an infinitary field such as
`(f : (n : Nat) → Vec n)`.  The three functions below let one code path handle
both. -/

/--
If `ty` is `∀ ys, M args` for a member `M`, pass `k` the binders, the member's
index and its arguments.  Otherwise return `none`. -/
def Block.withRecTarget? {α} (b : Block) (ty : Expr)
    (k : Array Expr → Nat → Array Expr → MetaM α) : MetaM (Option α) :=
  -- a copy of `Subtype` carries its predicate as a parameter, so its proof field
  -- arrives as `(fun t => P t) val`; a field is its beta-normal form, and the
  -- kernel reads it that way too
  forallTelescope ty.headBeta fun ys concl => do
    let concl := concl.headBeta
    let .const n _ := concl.getAppFn | return none
    let some i := b.memberIdx? n | return none
    return some (← k ys i concl.getAppArgs)

/-- `Block.withRecTarget?`, for a caller with no other reading to fall back on. -/
def Block.withRecTarget {α} (b : Block) (ty : Expr)
    (k : Array Expr → Nat → Array Expr → MetaM α) : MetaM α := do
  let some r ← b.withRecTarget? ty k
    | throwError "Not a recursive field type:{indentExpr ty}"
  return r

/-- As `Block.withRecTarget?`, but reading the pre-world name `M._pre`. -/
def Block.withPreTarget {α} (b : Block) (ty : Expr)
    (k : Array Expr → Nat → Array Expr → MetaM α) : MetaM α :=
  forallTelescope ty.headBeta fun ys concl => do
    let concl := concl.headBeta
    let .const n _ := concl.getAppFn
      | throwError "Not a recursive field type: {ty}"
    let some i := b.preIdx? n
      | throwError "Not a recursive field type: {ty}"
    k ys i concl.getAppArgs

mutual

/-- The pre-world image of `x : ty`. -/
partial def Block.preImage (b : Block) (x ty : Expr) : MetaM Expr := do
  let r? ← b.withRecTarget? ty fun ys i args => do
    if b.members[i]!.isProp then return x
    else mkLambdaFVars ys (b.sVal i (← b.valArgs i args) (mkAppN x ys))
  return r?.getD x

/--
A member's arguments moved from the real world to the pre-world; the only place
that gap is crossed. -/
partial def Block.valArgs (b : Block) (i : Nat) (args : Array Expr) : MetaM (Array Expr) := do
  if b.members[i]!.dropped.isEmpty then return args
  let mut out := #[]
  for k in *...args.size do
    if b.keepsArg i k then out := out.push args[k]!
    else out := out.push (← b.preImage args[k]! (← inferType args[k]!))
  return out

end

/--
A field's type moved to the pre-world, with the surrounding fields replaced by
the pre-world stand-ins `news`. -/
def Block.subTy (b : Block) (olds news : Array Expr) (ty : Expr) : MetaM Expr :=
  forallTelescope ty.headBeta fun ys concl => do
    let concl := concl.headBeta
    let across :=
      match concl.getAppFn with
      | .const n us =>
        if (b.memberIdx? n).isSome then
          mkAppN (.const (b.rawMember n) us) (concl.getAppArgs.map b.tr)
        else b.tr concl
      | _ => b.tr concl
    return (← mkForallFVars ys across).replaceFVars olds news

/-- The type `Block.subTy`'s reading of a field is bound at, with nothing kept back. -/
def Block.preTy (b : Block) (subTy : Expr) : MetaM Expr := do
  let r? ← b.withRecTarget? subTy fun ys i args => mkForallFVars ys (b.preApp i args)
  return r?.getD subTy

/--
`Block.subTy`'s reading of every field of a constructor, at the pre-world terms
`xs` standing for them. -/
def Block.subFieldTys (b : Block) (cc : CtorSpec) (ps xs : Array Expr) :
    MetaM (Array Expr) := do
  forallBoundedTelescope (← instantiateForall (b.toRaw cc.type) ps) xs.size fun rxs _ => do
    let mut out : Array Expr := #[]
    for z in *...rxs.size do
      out := out.push (← b.subTy (rxs.extract 0 z) (xs.extract 0 z) (← inferType rxs[z]!))
    return out

/-- The pre-world images of a whole telescope, each read at its own type. -/
def Block.preImages (b : Block) (xs : Array Expr) : MetaM (Array Expr) :=
  xs.mapM fun x => do b.preImage x (← inferType x)

/-- The well-formedness proof `x` carries: `fun ys => (x ys).property`. -/
def Block.propImage (b : Block) (x ty : Expr) : MetaM Expr :=
  b.withRecTarget ty fun ys i args => do
    mkLambdaFVars ys (b.sProp i (← b.valArgs i args) (mkAppN x ys))

/--
A member's indices in the pre-world, and the well-formedness the data ones
carry, as the two lists a pre-block's recursor takes. -/
def Block.preAndWf (b : Block) (idxs : Array Expr) : MetaM (Array Expr × Array Expr) := do
  let mut pres : Array Expr := #[]
  let mut wfs : Array Expr := #[]
  for y in idxs do
    let ty ← inferType y
    pres := pres.push (← b.preImage y ty)
    let isData ← b.withRecTarget? ty fun _ m _ => pure (!b.members[m]!.isProp)
    if isData == some true then
      wfs := wfs.push (← b.propImage y ty)
  return (pres, wfs)

/--
The `Prop` members behind a pre-block recursor's members, in the recursor's
order. -/
def Block.propsBehind (b : Block) (recInfo : RecursorVal) : MetaM (Array Nat) :=
  recInfo.all.toArray.mapM fun n => do
    let some j := b.propIdxs.find? fun j => preName b.members[j]!.name == n
      | throwError "No `Prop` member of the block behind `{n}`"
    return j

/-- Every constructor of the given members, paired with the member it is of. -/
def Block.ctorsOf (b : Block) (idxs : Array Nat) : Array (Nat × CtorSpec) :=
  idxs.flatMap fun j => b.members[j]!.ctors.map fun cc => (j, cc)

/--
`∀ ys, X._wf args (y ys)`, from a recursive field `y : ∀ ys, X args`, read from
`Block.subTy`'s reading of it, the only one that still names a deleted index. -/
def Block.wfOfSub (b : Block) (y subTy : Expr) : MetaM Expr :=
  b.withRecTarget subTy fun ys i args =>
    mkForallFVars ys (mkApp (b.wfApp i args) (mkAppN y ys))

/--
The earlier erased fields that field `k`'s conjunct still names, in field order,
closed under one naming another. -/
def erasedDeps (kinds : Array FieldKind) (imgs : Array (Option Expr))
    (subTys : Array Expr) (conj : Expr) (k : Nat) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  for q in *...k do
    let j := k - 1 - q
    if kinds[j]! == .erased then
      if let some x := imgs[j]! then
        if x.isFVar && (conj.containsFVar x.fvarId! ||
            out.any (subTys[·]!.containsFVar x.fvarId!)) then
          out := out.push j
  return out.reverse

/-- The binders `Block.erasedConj` puts on, one at a time so each is at the ones before it. -/
partial def Block.closeErased (b : Block) (imgs : Array (Option Expr)) (subTys : Array Expr)
    (deps : Array Nat) (q : Nat) (olds news : Array Expr) (conj : Expr) : MetaM Expr := do
  if h : q < deps.size then
    let x := imgs[deps[q]]!.get!
    let ty := (← b.preTy subTys[deps[q]]!).replaceFVars olds news
    withLocalDeclD (← x.fvarId!.getUserName) ty fun y =>
      b.closeErased imgs subTys deps (q + 1) (olds.push x) (news.push y) conj
  else
    mkForallFVars news (conj.replaceFVars olds news)

/--
What an erased field's conjunct says: the proposition the field carried, closed
over the earlier erased fields it names. -/
def Block.erasedConj (b : Block) (kinds : Array FieldKind) (imgs : Array (Option Expr))
    (subTys : Array Expr) (k : Nat) : MetaM Expr := do
  let conj ← b.preTy subTys[k]!
  b.closeErased imgs subTys (erasedDeps kinds imgs subTys conj k) 0 #[] #[] conj

/--
The conjuncts of a constructor's well-formedness, in the order `_wf` states
them: recursive fields first, then erased fields, then the equations `eqs`, one
per built index. -/
def Block.wfConjs (b : Block) (kinds : Array FieldKind) (imgs : Array (Option Expr))
    (subTys : Array Expr) (eqs : Array Expr := #[]) : MetaM (Array Expr) := do
  let mut conjs : Array Expr := #[]
  for k in recPositions kinds do
    let conj ← b.wfOfSub imgs[k]!.get! subTys[k]!
    conjs := conjs.push <|
      ← b.closeErased imgs subTys (erasedDeps kinds imgs subTys conj k) 0 #[] #[] conj
  for k in *...kinds.size do
    if kinds[k]! == .erased then conjs := conjs.push (← b.erasedConj kinds imgs subTys k)
  return conjs ++ eqs

/--
The equations a constructor's *built* indices impose: one per index the pre-type
deleted that the constructor does not take as a field. -/
def Block.builtEqs (b : Block) (i : Nat) (kinds : Array FieldKind) (concl : Expr)
    (olds news dvals : Array Expr) : MetaM (Array (Nat × Expr)) := do
  let dropped := b.members[i]!.dropped
  let idxArgs := b.idxArgs concl.getAppArgs
  let mut out : Array (Nat × Expr) := #[]
  for q in *...dropped.size do
    if (deletedField? kinds dropped[q]!).isSome || b.dropAtProp i dropped[q]! then continue
    out := out.push (q, ← mkEq ((b.tr idxArgs[dropped[q]!]!).replaceFVars olds news) dvals[q]!)
  return out

/--
The shape of `X._wf`'s hypothesis about a recursive field: what its motive says
at a pre-term of the member the field recurses into. -/
def Block.ihTy (b : Block) (ps pad : Array Expr) (subTy : Expr) : MetaM Expr :=
  b.withRecTarget subTy fun ys mm args => do
    let dts ← b.dropTysAt mm ps (b.idxArgs args)
    mkForallFVars ys (← mkDropForall dts (mkArrows pad (mkSort Level.zero)))

/-- `∀ ys, ih ys dels`, the same conjunct written with a recursor's own hypothesis. -/
def Block.ihConj (b : Block) (ih : Expr) (padVal : Array Expr) (subTy : Expr) : MetaM Expr :=
  b.withRecTarget subTy fun ys mm args =>
    mkForallFVars ys (mkAppN ih (ys ++ b.dropArgs mm args ++ padVal))

/-! ## Conjunctions

`X._wf` at a constructor is a right-associated conjunction: one conjunct per
recursive field, then one per erased field, and `True` when there are none.
These three functions fix that shape.  The constructors build it and the recursor
takes it apart, so both must agree. -/

/-- `cs[i] ∧ (cs[i+1] ∧ ..)`, and `True` when `i` is past the end. -/
partial def foldConj (cs : Array Expr) (i : Nat) : Expr :=
  if h : i < cs.size then
    if i + 1 == cs.size then cs[i] else mkApp2 (mkConst ``And) cs[i] (foldConj cs (i + 1))
  else
    mkConst ``True

/-- A proof of `cs[i]` from a proof `w` of `foldConj cs 0`. -/
def projConj (cs : Array Expr) (w : Expr) (i : Nat) : Expr := Id.run do
  let mut e := w
  for j in *...i do
    e := mkApp3 (mkConst ``And.right) cs[j]! (foldConj cs (j + 1)) e
  if i + 1 < cs.size then
    e := mkApp3 (mkConst ``And.left) cs[i]! (foldConj cs (i + 1)) e
  return e

/-- A proof of `foldConj cs 0` from proofs `ps` of each conjunct. -/
partial def introConj (cs ps : Array Expr) (i : Nat) : Expr :=
  if h : i < cs.size then
    if i + 1 == cs.size then ps[i]!
    else mkApp4 (mkConst ``And.intro) cs[i] (foldConj cs (i + 1)) ps[i]! (introConj cs ps (i + 1))
  else
    mkConst ``True.intro

/-! ## Rebuilding a telescope in the pre-world -/

/--
Walk a constructor's fields, rebuilding the telescope in the pre-world.  `k`
receives the substitution built (originals left, stand-ins right), one image per
original field (`none` for a dropped one), and each field's type. -/
partial def withPreFieldsAux {α} [Inhabited α] (b : Block) (kinds : Array FieldKind)
    (xs : Array Expr) (i : Nat) (olds news : Array Expr) (imgs : Array (Option Expr))
    (subTys : Array Expr)
    (k : Array Expr → Array Expr → Array (Option Expr) → Array Expr → MetaM α) : MetaM α := do
  if h : i < xs.size then
    let x := xs[i]
    let ty ← inferType x
    let sub ← b.subTy olds news ty
    if kinds[i]!.isDropped then
      -- an erased field is its own image: nothing of it survives into the
      -- pre-term, but a later field's type may name it and the well-formedness
      -- must be able to say which field that was
      let img := if kinds[i]! == .erased then some x else none
      withPreFieldsAux b kinds xs (i + 1) olds news (imgs.push img) (subTys.push sub) k
    else
      let pre ← b.preTy sub
      if pre == ty then
        withPreFieldsAux b kinds xs (i + 1) (olds.push x) (news.push x)
          (imgs.push (some x)) (subTys.push sub) k
      else
        withLocalDeclD (← x.fvarId!.getUserName) pre fun y =>
          withPreFieldsAux b kinds xs (i + 1) (olds.push x) (news.push y)
            (imgs.push (some y)) (subTys.push sub) k
  else
    k olds news imgs subTys

@[inherit_doc withPreFieldsAux]
def withPreFields {α} [Inhabited α] (b : Block) (kinds : Array FieldKind) (xs : Array Expr)
    (olds news : Array Expr)
    (k : Array Expr → Array Expr → Array (Option Expr) → Array Expr → MetaM α) : MetaM α :=
  withPreFieldsAux b kinds xs 0 olds news #[] #[] k

/-- The pre-world stand-ins of the fields a constructor keeps, in order. -/
def keptImages (kinds : Array FieldKind) (imgs : Array (Option Expr)) : Array Expr :=
  (keptPositions kinds).map (imgs[·]!.get!)

/--
The real terms an alternative reads a member's deleted indices at, in arity
order. -/
partial def Block.withDelsAux {α} [Inhabited α] (b : Block) (kinds : Array FieldKind)
    (xs : Array Expr) (dropped : Array Nat) (tys : Array (Name × Expr)) (q : Nat)
    (acc : Array Expr) (k : Array Expr → MetaM α) : MetaM α := do
  if h : q < dropped.size then
    match deletedField? kinds dropped[q] with
    | some kf => b.withDelsAux kinds xs dropped tys (q + 1) (acc.push xs[kf]!) k
    | none =>
      withLocalDeclD tys[q]!.1 (tys[q]!.2.beta acc) fun d =>
        b.withDelsAux kinds xs dropped tys (q + 1) (acc.push d) k
  else
    k acc

/--
`Block.withDelsAux`, given the constructor's own conclusion indices `cidxs` to
read the arity at. -/
def Block.withDels {α} [Inhabited α] (b : Block) (i : Nat) (ps xs cidxs : Array Expr)
    (kinds : Array FieldKind) (k : Array Expr → MetaM α) : MetaM α := do
  let dropped := b.members[i]!.dropped
  if dropped.all fun p => (deletedField? kinds p).isSome then
    return ← k (dropped.map fun p => xs[(deletedField? kinds p).get!]!)
  let tys ← forallTelescope (← instantiateForall b.members[i]!.type ps) fun idxs _ => do
    let ds := b.dropIdxs i idxs
    ds.mapIdxM fun q d =>
      return (← d.fvarId!.getUserName,
        ← mkLambdaFVars (b.keptIdxs i idxs ++ ds.extract 0 q) (← inferType d))
  let kept := b.keptIdxs i cidxs
  b.withDelsAux kinds xs dropped (tys.map fun (n, t) => (n, t.beta kept)) 0 #[] k

/--
An index the erasure deleted that the constructor *builds* rather than takes as
a field: `Tm.lam` ends in `Tm Γ (Ty.pi Γ A B)`, whose second index is no field. -/
structure BuiltIdx where
  /-- Which of the member's deleted indices this is, counted in arity order. -/
  slot : Nat
  /-- The member the index is a value of. -/
  mem : Nat
  /-- That member's own arguments, as the pre-world states them. -/
  args : Array Expr
  /-- The binder the alternative reads the index at, one of `AltFields.dels`. -/
  del : Expr
  /-- The pre-world term the constructor gives the index, `Ty._pre.pi a b`. -/
  pre : Expr
  /-- Which conjunct of the well-formedness equates `pre` with the index's value. -/
  conj : Nat
  deriving Inhabited

/--
One constructor of a data member, read in the pre-world: the starting point for
an alternative of either recursor. -/
structure AltFields where
  kinds : Array FieldKind
  xs : Array Expr
  olds : Array Expr
  news : Array Expr
  imgs : Array (Option Expr)
  subTys : Array Expr
  cIdxs : Array Expr
  realIdxs : Array Expr
  head : Expr
  wc : Expr
  conjs : Array Expr
  real : Array Expr
  recPos : Array Nat
  dels : Array Expr
  built : Array BuiltIdx

/--
Read the constructor `c` of member `i` in the pre-world and run `k` on it, under
the binders it introduces: the pre-world fields, the deleted indices and the
well-formedness `wc`. -/
def Block.withAlt {α} [Inhabited α] (b : Block) (i : Nat) (c : CtorSpec) (ps : Array Expr)
    (k : AltFields → MetaM α) : MetaM α := do
  let kinds := b.fieldKinds c.kinds
  forallTelescope (← b.ctorType c ps) fun xs cconcl => do
    let dropped := b.members[i]!.dropped
    b.withDels i ps xs (b.idxArgs cconcl.getAppArgs) kinds fun dels => do
      -- the pre-world sees a deleted index as its value, and that is what the
      -- substitution carries
      let mut fOlds : Array Expr := #[]
      let mut fNews : Array Expr := #[]
      let mut dvals : Array Expr := #[]
      for q in *...dropped.size do
        let val ← b.preImage dels[q]! (← inferType dels[q]!)
        dvals := dvals.push val
        if (deletedField? kinds dropped[q]!).isSome then
          fOlds := fOlds.push dels[q]!
          fNews := fNews.push val
      withPreFields b kinds xs fOlds fNews fun olds news imgs subTys => do
        let mut cIdxs := cconcl.getAppArgs.map (·.replaceFVars olds news)
        for q in *...dropped.size do
          cIdxs := cIdxs.set! (b.numParams + dropped[q]!) dvals[q]!
        let head := mkAppN (b.cst (b.preOf c.name)) (ps ++ keptImages kinds imgs)
        withLocalDeclD `w (mkApp (b.wfApp i cIdxs) head) fun wc => do
          let recPos := recPositions kinds
          let eqs ← b.builtEqs i kinds cconcl olds news dvals
          let conjs ← b.wfConjs kinds imgs subTys (eqs.map (·.2))
          let mut built : Array BuiltIdx := #[]
          for (q, eq) in eqs do
            let some (mem, args) ← b.withRecTarget? (← inferType dels[q]!) fun _ mm margs =>
                return (mm, ← b.valArgs mm margs)
              | throwError "The resulting type of `{c.name}` gives index {dropped[q]! + 1} \
                  as{indentExpr eq.appFn!.appArg!}\nwhich is not a value of a member \
                  of the block"
            built := built.push
              { slot := q, mem, args, del := dels[q]!, pre := eq.appFn!.appArg!,
                conj := conjs.size - eqs.size + built.size }
          let mut real : Array Expr := #[]
          let mut nrec := 0
          let mut nera := 0
          for j in *...xs.size do
            match kinds[j]! with
            | .recur mm =>
              let y := (imgs[j]!).get!
              let pr := projConj conjs wc nrec
              real := real.push <| ← b.withRecTarget subTys[j]! fun ys _ args =>
                mkLambdaFVars ys (b.sMk mm args (mkAppN y ys) (mkAppN pr ys))
              nrec := nrec + 1
            | .plain => real := real.push (imgs[j]!).get!
            | .deleted .. => real := real.push xs[j]!
            | .erased =>
              -- the conjunct was closed over the earlier erased fields it named;
              -- those have just been recovered, so it opens again
              let pr := projConj conjs wc (recPos.size + nera)
              let deps := erasedDeps kinds imgs subTys (← b.preTy subTys[j]!) j
              real := real.push (mkAppN pr (deps.map (real[·]!)))
              nera := nera + 1
          let realIdxs := cconcl.getAppArgs.map (·.replaceFVars xs real)
          k { kinds, xs, olds, news, imgs, subTys, cIdxs, realIdxs, head, wc, conjs, real,
              recPos, dels, built }

/--
An alternative's body carried from the index the constructor built to the index
the recursion was called at. -/
def Block.transportBuilt (b : Block) (i : Nat) (a : AltFields)
    (goal core : Array Expr → Array Expr → Expr → MetaM Expr) : MetaM Expr := do
  if a.built.isEmpty then return ← core (b.idxArgs a.realIdxs) a.cIdxs a.wc
  let qs := a.built.map fun bi => b.members[i]!.dropped[bi.slot]!
  -- what the constructor reads each built index at, and what the alternative
  -- does: the latter is already in `cIdxs`, since a bound index arrives there
  -- as the pre-world value of the binder
  let pres := a.built.map (·.pre)
  let dels := (Array.range qs.size).map fun k => a.cIdxs[b.numParams + qs[k]!]!
  -- a built index may be *stated* at one built before it -- `Tm.var` ends in
  -- `Tm (Γ.snoc A) (Ty.base (Γ.snoc A))` -- so its arguments are read at
  -- whatever that one has been moved to so far, not at where it ends up
  let argsAt (k : Nat) (vs : Array Expr) : Array Expr :=
    a.built[k]!.args.map fun e => e.replace fun s => Id.run do
      for j in *...qs.size do
        if s == dels[j]! then return some vs[j]!
      return none
  -- the conclusion's arguments, and the member's real indices, with every built
  -- index read at the value it is given here instead of at the constructor's
  let cIdxsAt (vs : Array Expr) : Array Expr := Id.run do
    let mut out := a.cIdxs
    for h : k in *...qs.size do
      out := out.set! (b.numParams + qs[k]) vs[k]!
    return out
  let mIdxsAt (vs hs : Array Expr) : Array Expr := Id.run do
    let mut out := b.idxArgs a.realIdxs
    for h : k in *...qs.size do
      out := out.set! qs[k] (b.sMk a.built[k]!.mem (argsAt k vs) vs[k]! hs[k]!)
    return out
  -- run `k` under a well-formedness for each built value and one for the term,
  -- all of them stated at the values handed in
  let withHalves (vs : Array Expr) (k : Array Expr → Expr → MetaM Expr) : MetaM Expr := do
    let decls : Array (Name × (Array Expr → MetaM Expr)) :=
      (Array.range qs.size).map fun z =>
        (`h, fun _ => pure (mkApp (b.wfApp a.built[z]!.mem (argsAt z vs)) vs[z]!))
    withLocalDeclsD decls fun hs =>
      withLocalDeclD `w (mkApp (b.wfApp i (cIdxsAt vs)) a.head) fun w => k hs w
  let mut term ← withHalves pres fun hs w => do
    mkLambdaFVars (hs ++ #[w]) (← core (mIdxsAt pres hs) (cIdxsAt pres) w)
  for k in *...qs.size do
    let bi := a.built[k]!
    let before := dels.extract 0 k ++ pres.extract k pres.size
    let mot ← withLocalDeclD `v (b.preApp bi.mem (argsAt k before)) fun v => do
      let vs := (dels.extract 0 k).push v ++ pres.extract (k + 1) pres.size
      mkLambdaFVars #[v] (← withHalves vs fun hs w => do
        mkForallFVars (hs ++ #[w]) (← goal (mIdxsAt vs hs) (cIdxsAt vs) w))
    term ← mkEqNDRec mot term (projConj a.conjs a.wc bi.conj)
  let proofs := a.built.map fun bi => b.sProp bi.mem bi.args bi.del
  return mkAppN term (proofs ++ #[a.wc])

/-- `withLocalDeclsD`, but the binders come out implicit. -/
def withImplicits {α} [Inhabited α] (decls : Array (Name × (Array Expr → TermElabM Expr)))
    (k : Array Expr → TermElabM α) : TermElabM α :=
  withLocalDecls (decls.map fun (n, ty) => (n, .implicit, ty)) k

/-- What distinguishes one recursor's front from another's. -/
structure Front where
  /-- The members the motives run over, in the order the recursor takes them. -/
  members : Array Nat
  /-- Where a member's motive sits among them. -/
  pos : Nat → Nat
  /-- The sort the motives land in. -/
  lvl : Level
  /-- What the thing a motive is about is called: `t` for a value, `h` for a proof. -/
  major : Name
  /-- The fields a minor premise takes an induction hypothesis about. -/
  ihPos : Array FieldKind → Array Nat

/--
The front of a recursor stated in the raw world, passed to `k` as the motives
and the minors: a motive over the member's own arity, a minor over the raw
constructor's fields concluding at the raw constructor. -/
def Block.withRawFront {α} [Inhabited α] (b : Block) (ps : Array Expr) (f : Front)
    (k : Array Expr → Array Expr → TermElabM α) : TermElabM α := do
  let mnames := motiveNames f.members.size
  let motiveDecls : Array (Name × (Array Expr → TermElabM Expr)) :=
    f.members.mapIdx fun q j => (mnames[q]!, fun _ => do
      forallTelescope (← instantiateForall b.members[j]!.type ps) fun idxs _ =>
        withLocalDeclD f.major (mkAppN (b.memberCst j) (ps ++ idxs)) fun t =>
          mkForallFVars (idxs ++ #[t]) (mkSort f.lvl))
  withImplicits motiveDecls fun motives => do
    let mut minorDecls : Array (Name × (Array Expr → TermElabM Expr)) := #[]
    for j in f.members do
      for cc in b.members[j]!.ctors do
        minorDecls := minorDecls.push (Name.mkSimple cc.name.getString!, fun _ => do
          forallTelescope (← b.ctorType cc ps) fun xs concl => do
            let kinds := b.fieldKinds cc.kinds
            let ihDecls : Array (Name × (Array Expr → TermElabM Expr)) :=
              (f.ihPos kinds).map fun z => (`ih, fun _ => do
                let r? ← b.withRecTarget? (← inferType xs[z]!) fun ys m args =>
                  mkForallFVars ys
                    (mkAppN motives[f.pos m]! (b.idxArgs args ++ #[mkAppN xs[z]! ys]))
                let some e := r? | throwError "Not a recursive field of `{cc.name}`"
                return e)
            withLocalDeclsD ihDecls fun ihs =>
              mkForallFVars (xs ++ ihs) (mkAppN motives[f.pos j]!
                (b.idxArgs concl.getAppArgs ++
                  #[mkAppN (b.cst (b.rawCtor cc.name)) (ps ++ xs)])))
    withLocalDeclsD minorDecls fun minors => k motives minors

/-! ## Elaborating the headers, with the members as scratch axioms

The members' arities must be elaborated with the *other* members in scope, which
`mutual` refuses to do.  Each member is declared as a temporary `axiom` as soon
as its arity is known, inside `withoutModifyingEnv`.  The constructors elaborate
against those.  The data constructors become axioms too, so that `.snoc` in a
`Prop` constructor's type resolves as written.  The environment is then rolled
back and the real declarations made under the same names.

The arities need an order the writer need not supply, so a worklist is used: go
round the members, keep whichever succeed, stop when a round adds nothing.  The
universe parameters are unknown until every constructor is read, so a stub is
declared over every universe name in scope and `restub` moves the batch once the
list is settled. -/

private def stubAxiomAt (levelParams : List Name) (name : Name) (type : Expr) :
    TermElabM Unit := do
  -- A scratch axiom never enters the visible environment, and every real
  -- declaration is kernel-checked on its own.  Skipping is also required: a
  -- stub's type carries level metavariables, and `Elab.async` checks in a task
  -- that `restub`'s rewind cannot cancel
  withOptions (debug.skipKernelTC.set · true) do
    addDecl (.axiomDecl { name, levelParams, type := ← instantiateMVars type, isUnsafe := false })

private def stubAxiom (name : Name) (type : Expr) : TermElabM Unit := do
  -- every universe name in scope, so the stub is well-formed whichever ones its
  -- type turns out to use; `normLevels` puts the references straight afterwards,
  -- and `restub` moves the axioms themselves once the block's own list is known
  stubAxiomAt (← Term.getLevelNames).reverse name type

/--
Add a batch of scratch axioms, each after whatever else in the batch it
mentions, by worklist. -/
private def stubBatch (levelParams : List Name) (todo : Array (Name × Expr))
    (what : String := "scratch axioms") : TermElabM Unit := do
  let batch := todo.map (·.1)
  let mut todo := todo
  while !todo.isEmpty do
    let env ← getEnv
    let mut next : Array (Name × Expr) := #[]
    let mut progress := false
    for (n, t) in todo do
      if t.getUsedConstants.any fun c => batch.contains c && (env.find? c).isNone then
        next := next.push (n, t)
      else
        stubAxiomAt levelParams n t
        progress := true
    unless progress do
      throwError "The {what} `{next.map (·.1)}` depend on one another circularly"
    todo := next

/--
Auto-binding, as Lean's header elaboration does it: universe names such as the
`u` of `Type u` join the level names, and unbound identifiers become implicit
binders. -/
private def withAuto {α} (views : Array InductiveView) (k : TermElabM α) : TermElabM α :=
  Term.withAutoBoundImplicitForbiddenPred (fun n => views.any (·.shortDeclName == n)) <|
    Term.withAutoBoundImplicit k

/-- `∀ params idxs, Sort l`, together with how many of those binders are parameters. -/
private def elabArity (views : Array InductiveView) (view : InductiveView) :
    TermElabM (Expr × Nat) := do
  withRef (view.type?.getD view.ref) <| Term.withoutErrToSorry <| withAuto views do
    Term.elabBinders view.binders.getArgs fun params => do
      let type ← withAuto views do
        match view.type? with
        | none => pure (mkSort (mkLevelSucc Level.zero))
        | some typeStx => do
          let type ← Term.elabType typeStx
          Term.synthesizeSyntheticMVarsNoPostponing
          let idxs ← Term.addAutoBoundImplicits #[] none
          mkForallFVars idxs (← instantiateMVars type)
      let params ← Term.addAutoBoundImplicits params none
      return (← instantiateMVars (← mkForallFVars params type), params.size)

/-- Make the leading `n` binders implicit. -/
partial def implicitPrefix (n : Nat) (e : Expr) : Expr :=
  let keep (bi : BinderInfo) := if bi == .instImplicit then bi else .implicit
  match n, e with
  | 0, _ => e
  | n + 1, .forallE nm d body bi => .forallE nm d (implicitPrefix n body) (keep bi)
  | n + 1, .lam nm d body bi => .lam nm d (implicitPrefix n body) (keep bi)
  | _, _ => e

/-- Make the `n` binders starting at position `lo` implicit. -/
partial def implicitRange (lo n : Nat) (e : Expr) : Expr :=
  match lo, e with
  | 0, _ => implicitPrefix n e
  | lo + 1, .forallE nm d body bi => .forallE nm d (implicitRange lo n body) bi
  | lo + 1, .lam nm d body bi => .lam nm d (implicitRange lo n body) bi
  | _, _ => e

/--
A recursor's binders, as Lean leaves its own: the parameters implicit, the
motives and minors as declared, the indices implicit, the major premise
explicit. -/
def hideRecBinders (numParams numPremises numIdxs : Nat) (e : Expr) : Expr :=
  implicitPrefix numParams <| implicitRange (numParams + numPremises) numIdxs e

/-- `∀ {params} fields, M params args`; the parameters lead here too. -/
private def elabCtorType (views : Array InductiveView) (view : InductiveView) (ctor : CtorView) :
    TermElabM Expr :=
  withRef ctor.ref <| Term.withoutErrToSorry <| withAuto views do
    Term.elabBinders view.binders.getArgs fun params =>
      withAuto views <| Term.elabBinders ctor.binders.getArgs fun fields => do
        let ty ← match ctor.type? with
          | some typeStx => Term.elabType typeStx
          | none =>
            -- the member is in scope only as its scratch axiom, declared over
            -- every universe name around when its arity was read, so an empty
            -- level list is the right length only when there were none
            let ps := (((← getEnv).find? view.declName).map (·.levelParams)).getD []
            pure (mkAppN (mkConst view.declName (← ps.mapM fun _ => mkFreshLevelMVar)) params)
        Term.synthesizeSyntheticMVarsNoPostponing
        -- an auto-bound implicit of a constructor is a field of it, not a
        -- parameter: the parameters are fixed by the member's own arity
        let fields ← Term.addAutoBoundImplicits fields none
        let ty ← instantiateMVars (← mkForallFVars (params ++ fields) ty)
        return implicitPrefix params.size ty

/-- Reject up front everything the lowering below does not know how to do. -/
private def checkSupported (views : Array InductiveView) : TermElabM Unit := do
  for v in views do
    withRef v.ref do
      unless v.levelNames == views[0]!.levelNames do
        throwError "`{views[0]!.declName}` and `{v.declName}` declare different universe \
          parameters; every member of a mutual block must declare the same ones"
      if v.isClass then
        throwError "An induction-inductive block may not declare a class"
      if v.isCoinductive then
        throwError "An induction-inductive block may not be coinductive"
      unless v.computedFields.isEmpty do
        throwError "Computed fields are not supported for an induction-inductive block"

/--
Everything that must be built while the scratch axioms are still in the
environment. -/
structure Plan where
  block : Block
  /-- The data members' pre-types, as one mutual inductive. -/
  preDataInds : Array InductiveType
  /--
  Whether those pre-types disagree about their universe and so must reach the
  kernel through `Mumi.Lowering` rather than as a single `addInd`. -/
  preIsHeterogeneous : Bool := false
  /--
  The `Prop` members' pre-types in the layers `propLayers` computed: one mutual
  inductive per layer, declared in this order, so a proposition indexed by
  another already has the other's pre-type in scope. -/
  prePropInds : Array (Array InductiveType)
  /-- Which members each of those layers holds, in the same order. -/
  propLayers : Array (Array Nat) := #[]
  /-- `X._wf`, per data member: its name, type and `X._pre.rec` body. -/
  wfDecls : Array (Name × Expr × Expr)
  /-- The members denesting added, and the original application each copies. -/
  copies : Array (Name × Expr) := #[]
  /--
  The members that left the block rather than going through the erasure, ready
  to be declared as they stand; see `markPeeled`. -/
  peeled : Array InductiveType := #[]
  /--
  Where each of those sat in the block as written, so that the recursors of the
  members that stayed can put them back.  See `widenWithPeeled`. -/
  peeledIdxs : Array Nat := #[]
  deriving Inhabited

/-- The elaborated block, with no syntax left in it. -/
structure Raw where
  names     : Array Name
  ctorNames : Array (Array Name)
  /-- `∀ params idxs, Sort l`, one per member. -/
  arities   : Array Expr
  /-- `∀ {params} fields, M params args`, one per constructor. -/
  ctorTypes : Array (Array Expr)
  numParams : Nat
  /-- The level names in scope where the block was written. -/
  scopeLevelNames : List Name
  /-- The level names the block itself declares. -/
  declLevelNames  : List Name
  /--
  The members `denestRaw` added, and what each is a copy of: a lambda over the
  block's parameters, and over any constructor field its parameters mentioned,
  giving the original application `I ps'`.  Empty for a hand-written block. -/
  copies : Array (Name × Expr) := #[]
  /--
  The environment as it stood before the first scratch axiom was added, so they
  can be re-declared once the block's universe parameters are known; see
  `restub`. -/
  stubEnv : Option Environment := none
  /-- The section variables in scope where the block was written, in scope order. -/
  vars : Array Expr := #[]
  /--
  The members that leave the block before the erasure sees it, by index; see
  `markPeeled`. -/
  peeled : Array Nat := #[]
  deriving Inhabited

/-- The block's own names: its members and their constructors. -/
def Raw.blockNames (r : Raw) : Array Name :=
  (Array.range r.names.size).flatMap fun i => #[r.names[i]!] ++ r.ctorNames[i]!

/-- Whether each member is a proposition, and the `l` of its resulting `Sort l`. -/
def memberLevels (names : Array Name) (arities : Array Expr) :
    TermElabM (Array Bool × Array Level) := do
  let mut isProp : Array Bool := #[]
  let mut levels : Array Level := #[]
  for i in *...arities.size do
    let (p, l) ← forallTelescopeReducing arities[i]! fun _ res => do
      match ← whnfD res with
      | .sort u => return (u.normalize == Level.zero, u)
      | _ => throwError "The resulting type of `{names[i]!}` is not a sort"
    isProp := isProp.push p
    levels := levels.push l
  return (isProp, levels)

/--
Mark the members that leave the block rather than being erased with it: a
proposition when the erasure has nothing to offer it, a data member when it has
nothing to offer the erasure. -/
def markPeeled (r : Raw) : TermElabM Raw := do
  let (isProp, _) ← memberLevels r.names r.arities
  -- a block of nothing but propositions gives the erasure nothing to keep, but
  -- the peel is not the erasure: the propositions that leave may be all that was
  -- in the way.  So no early return on there being no data
  let dataNames := (Array.range r.names.size).filterMap fun i =>
    if isProp[i]! then none else some r.names[i]!
  let propNames := (Array.range r.names.size).filterMap fun i =>
    if isProp[i]! then some r.names[i]! else none
  -- a constructor field whose type is the block's data, at a position the
  -- conclusion does not bind: the shape the erasure cannot state a minor for
  let wants (i : Nat) : TermElabM Bool := do
    -- or an arity indexed by another of the block's propositions
    if r.arities[i]!.getUsedConstants.any fun c => c != r.names[i]! && propNames.contains c then
      return true
    for c in r.ctorTypes[i]! do
      let hit ← forallTelescope c fun xs concl => do
        for x in xs do
          let ty ← inferType x
          if ← Meta.isProp ty then continue
          if ty.getUsedConstants.any (dataNames.contains ·) then
            unless concl.containsFVar x.fvarId! do return true
        return false
      if hit then return true
    return false
  let mentions (i j : Nat) : Bool :=
    let n := r.names[j]!
    r.arities[i]!.getUsedConstants.contains n ||
      r.ctorTypes[i]!.any (·.getUsedConstants.contains n)
  -- a data member nothing else in the block reaches is peeled too: it gains
  -- `match`, and `widenWithPeeled` puts its motive back in the other recursors
  let peelData := !isProp.any id
  let mut cand : Array Nat := #[]
  for j in *...r.names.size do
    if isProp[j]! then
      if ← wants j then cand := cand.push j
    else if peelData && !(Array.range r.names.size).any fun i => i != j && mentions i j then
      cand := cand.push j
  -- and close downwards: a candidate the block still names is no candidate, and
  -- dropping one may be what puts another back in
  let close (c₀ : Array Nat) : Array Nat := Id.run do
    let mut c := c₀
    repeat
      let next := c.filter fun j =>
        !(Array.range r.names.size).any fun i => i != j && !c.contains i && mentions i j
      if next.size == c.size then break
      c := next
    return c
  cand := close cand
  let kept (c : Array Nat) : Array Nat := (Array.range r.names.size).filter (!c.contains ·)
  -- a data member is peeled to gain it something, not to take the block apart:
  -- if what stays is no longer induction-inductive, the staying members lose the
  -- peeled one's motive and only a recursor of ours can be widened
  let stillIndInd (keep : Array Nat) : Bool := keep.any fun i =>
    r.arities[i]!.getUsedConstants.any fun c => keep.any fun k => k != i && r.names[k]! == c
  if cand.any (!isProp[·]!) && !stillIndInd (kept cand) then
    cand := close (cand.filter (isProp[·]!))
  -- and now grow upwards.  A data member the block still reaches cannot leave,
  -- but the member reaching it may be leaving too: `Sub` reads a `Tm`, so `Tm`
  -- is no candidate until `Sub` is out
  if peelData then
    let mut grew := true
    while grew do
      grew := false
      for j in *...r.names.size do
        if isProp[j]! || cand.contains j then continue
        if (Array.range r.names.size).any fun i => i != j && !cand.contains i && mentions i j then
          continue
        let c := cand.push j
        if !stillIndInd c && stillIndInd (kept c) then
          cand := c
          grew := true
  if cand.isEmpty then return r
  return { r with peeled := cand }

/--
The block's members in the order they can be declared one at a time, if no two
of them depend on each other.  `none` when some pair does, which is the case the
erasure is for. -/
def separationOrder? (r : Raw) : Option (Array Nat) := Id.run do
  let n := r.names.size
  if n ≤ 1 then return none
  -- a member's own occurrences do not have to wait for anything, so `i == j` is
  -- not a dependency
  let uses (i j : Nat) : Bool :=
    i != j &&
      (r.arities[i]!.getUsedConstants.contains r.names[j]! ||
        r.ctorTypes[i]!.any (·.getUsedConstants.contains r.names[j]!))
  let mut order : Array Nat := #[]
  let mut left := Array.range n
  while !left.isEmpty do
    -- whichever member is left that uses nothing still left can go next; if none
    -- can, what is left is a cycle and the block is genuinely simultaneous
    let some k := left.find? fun j => !left.any (uses j ·) | return none
    order := order.push k
    left := left.filter (· != k)
  return some order

/--
The arity check that depends on which members are still in the block, and the
order the propositions' pre-types are declared in. -/
def propLayers (names : Array Name) (arities : Array Expr) (ctorTypes : Array (Array Expr))
    (isProp : Array Bool) : TermElabM (Array (Array Nat)) := owning do
  -- erasure keeps the data and rebuilds it as a subtype of what it kept, so a
  -- block with nothing but propositions gives it nothing to work on
  if isProp.all id then
    throwError "Every member of this induction-inductive block is a proposition; there is \
      nothing for the erasure to keep"
  let propIdxs := (Array.range names.size).filter (isProp[·]!)
  if propIdxs.isEmpty then return #[]
  let propAt (c : Name) : Option Nat := propIdxs.find? (names[·]! == c)
  -- `j` must be strictly later than everything its arity names, and no earlier
  -- than everything its constructors name
  let after : Array (Array Nat) := propIdxs.map fun j =>
    arities[j]!.getUsedConstants.filterMap fun c =>
      if c == names[j]! then none else propAt c
  let notBefore : Array (Array Nat) := propIdxs.map fun j =>
    ctorTypes[j]!.foldl (init := #[]) fun acc t =>
      t.getUsedConstants.foldl (init := acc) fun acc c =>
        match propAt c with
        | some k => if k == j || acc.contains k then acc else acc.push k
        | none   => acc
  let pos (j : Nat) : Nat := (propIdxs.findIdx? (· == j)).getD 0
  let mut layer : Array Nat := Array.replicate propIdxs.size 0
  -- each round can only lift a member above one more of the ones it waits for,
  -- so a chain of `n` settles in `n` rounds and anything still moving is a cycle
  for _ in *...(propIdxs.size + 1) do
    let mut grew := false
    for q in *...propIdxs.size do
      let mut l := layer[q]!
      for k in after[q]! do
        l := max l (layer[pos k]! + 1)
      for k in notBefore[q]! do
        l := max l layer[pos k]!
      if l != layer[q]! then
        layer := layer.set! q l
        grew := true
    unless grew do
      let depth := layer.foldl max 0
      return (Array.range (depth + 1)).map fun d =>
        (Array.range propIdxs.size).filterMap fun q =>
          if layer[q]! == d then some propIdxs[q]! else none
  -- name a member that is still moving, and the one it is waiting for
  let q := ((Array.range propIdxs.size).find? (!after[·]!.isEmpty)).getD 0
  let j := propIdxs[q]!
  let k := after[q]![0]!
  throwError "The arity of `{names[j]!}` mentions `{names[k]!}`, which is another \
    proposition of the block, and `{names[k]!}` cannot be declared first: the two are \
    induction-inductive with each other.  Erasure sends the data members to one mutual \
    inductive and the propositions to a series of them, so a proposition may be indexed \
    by the block's data and by any proposition that can be declared before it -- but the \
    erasure buys one crossing, from the data to the propositions, and not a second \
    from the propositions to themselves"

/-- The checks the arities alone settle. -/
def checkDataArities (names : Array Name) (isProp : Array Bool)
    (levels : Array Level) : TermElabM Bool := owning do
  let dataIdxs := (Array.range names.size).filter (!isProp[·]!)
  -- The data members become one mutual pre-block, so the kernel's same-universe
  -- rule applies.  `Mumi.Lowering` lifts it, so members that disagree are not an
  -- error but a decision: emit the pre-block through the lowering rather than
  -- through `addInd`
  let mut heterogeneous := false
  for i in dataIdxs do
    unless ← isLevelDefEq levels[i]! levels[dataIdxs[0]!]! do
      heterogeneous := true
  -- a data member is encoded as a wrapper, which lands in `Sort (max 1 l)`
  for i in dataIdxs do
    unless ← isLevelDefEq (mkLevelMax Level.one levels[i]!) levels[i]! do
      let s := toString (← ppExpr (mkSort levels[i]!))
      throwError "The data member `{names[i]!}` lives at `{s}`, which could still \
        be `Prop`.  It is encoded as a wrapper around its pre-type, which lands one \
        universe up from \
        `Prop`, so a data member's universe has to be visibly non-zero -- `Type v` rather \
        than `Sort v`"
  return heterogeneous

/--
Which of each member's indices its pre-type must delete: those whose type
mentions the block. -/
def droppedIndices (b : Block) : MetaM (Array (Array Nat × Array Nat)) := do
  let mut out : Array (Array Nat × Array Nat) := #[]
  for m in b.members do
    if m.isProp then
      out := out.push (#[], #[])
    else
      out := out.push <| ← forallBoundedTelescope m.type b.numParams fun _ rest =>
        forallTelescope rest fun idxs _ => do
          let mut ds : Array Nat := #[]
          let mut hs : Array Nat := #[]
          for p in *...idxs.size do
            let ty ← inferType idxs[p]!
            if b.mentions ty then
              ds := ds.push p
              -- the head settles it: only an index at a data member's own type
              -- is something the recursion can say anything about
              let atData ← b.withRecTarget? ty fun _ j _ => pure !b.members[j]!.isProp
              if atData.getD false then hs := hs.push p
          return (ds, hs)
  return out

/--
Whether the deletions `droppedIndices` asks for can be carried out: a deleted
index's type must *be* a member's, only a member having a pre-type to state it
at, and an index that stays must not mention one that goes. -/
def checkDropped (b : Block) : TermElabM Unit := owning do
  for i in b.dataIdxs do
    let m := b.members[i]!
    if m.dropped.isEmpty then continue
    forallBoundedTelescope m.type b.numParams fun _ rest =>
      forallTelescope rest fun idxs _ => do
        let mentionsIdx (e : Expr) (which : Array Expr) : Bool :=
          e.hasAnyFVar fun v => which.any (·.fvarId! == v)
        for p in *...idxs.size do
          let ty ← inferType idxs[p]!
          unless m.dropped.contains p do
            if mentionsIdx ty (b.dropIdxs i idxs) then
              throwError "The index `{idxs[p]!}` of `{m.name}` mentions an index the erasure \
                has to delete, so it cannot be left where it is:{indentExpr ty}"
            continue
          -- a proof is as good an index as any: the proposition has a pre-type
          -- of its own, declared before `X._wf`, so `Tm._wf` can be stated at an
          -- `Ok._pre` like any other deleted index
          let some _ ← b.withRecTarget? ty fun ys j _ => do
              unless ys.isEmpty do
                throwError "The index `{idxs[p]!}` of `{m.name}` binds arguments before \
                  reaching a member of the block, and the erasure has no pre-type to state \
                  it at:{indentExpr ty}"
              return j
            | throwError "The index `{idxs[p]!}` of `{m.name}` mentions the block without \
                being a member's type, so the erasure has no pre-type to state it \
                at:{indentExpr ty}"

/-- The members `which` selects, in an order in which each can be defined. -/
def memberOrder (b : Block) (which : Array Nat) : TermElabM (Array Nat) := owning do
  let needs (i : Nat) : Array Nat :=
    which.filter fun j =>
      j != i && b.members[i]!.type.getUsedConstants.contains b.members[j]!.name
  let mut out : Array Nat := #[]
  let mut left := which
  while !left.isEmpty do
    let ready := left.filter fun i => (needs i).all (out.contains ·)
    if ready.isEmpty then
      let ns := ", ".intercalate (left.toList.map fun i => s!"`{b.members[i]!.name}`")
      throwError "The members {ns} index one another, so there is no order in which the \
        erasure could define them: each one's subtype would mention the next"
    out := out ++ ready
    left := left.filter (!ready.contains ·)
  return out

/-- `memberOrder` over the data members, which is what the constructors are sorted
against: a constructor's indices are built out of the block's own constructors,
and every member is a definition before any constructor is. -/
def dataOrder (b : Block) : TermElabM (Array Nat) := memberOrder b b.dataIdxs

/-- The data constructors in an order in which each can be defined. -/
def ctorOrder (b : Block) (order : Array Nat) : TermElabM (Array (Nat × CtorSpec)) := owning do
  let mut left : Array (Nat × CtorSpec) := #[]
  for i in order do
    for c in b.members[i]!.ctors do
      left := left.push (i, c)
  let mut out : Array (Nat × CtorSpec) := #[]
  while !left.isEmpty do
    let ready := left.filter fun (_, c) =>
      left.all fun (_, d) => d.name == c.name || !c.type.getUsedConstants.contains d.name
    if ready.isEmpty then
      let ns := ", ".intercalate (left.toList.map fun (_, c) => s!"`{c.name}`")
      throwError "The constructors {ns} name one another in their types, so there is no \
        order in which the erasure could define them"
    out := out ++ ready
    left := left.filter fun (_, c) => !ready.any (·.2.name == c.name)
  return out

/--
Whether the recursion can name an induction hypothesis at `e`, a deleted index
of one of `c`'s recursive fields. -/
partial def reachableIh (b : Block) (c : CtorSpec) (kinds : Array FieldKind) (xs : Array Expr)
    (e : Expr) : MetaM Unit := do
  let f := e.getAppFn
  if f.isFVar then
    let some q := (Array.range xs.size).find? (xs[·]! == f)
      | throwError "`{c.name}` recurses under the index{indentExpr e}\nwhich the erasure \
          deletes, and which is not one of its own fields"
    unless kinds[q]!.isDeleted || kinds[q]! matches .recur _ do
      throwError "`{c.name}` recurses under the index{indentExpr e}\nwhich the erasure \
        deletes, and the recursion has no induction hypothesis at that field"
    return
  let some n := f.constName?
    | throwError "`{c.name}` recurses under the index{indentExpr e}\nwhich the erasure \
        deletes, and which is neither a field nor a constructor of the block"
  let some (_, cs) := (b.ctorsOf b.dataIdxs).find? (·.2.name == b.unRaw n)
    | throwError "`{c.name}` recurses under the index{indentExpr e}\nwhich the erasure \
        deletes, and `{n}` is not a constructor of one of the block's data members"
  let ks := b.fieldKinds cs.kinds
  let args := b.idxArgs e.getAppArgs
  unless args.size == ks.size do
    throwError "`{c.name}` recurses under the index{indentExpr e}\nin which `{n}` is not \
      fully applied"
  for z in *...ks.size do
    if let .recur _ := ks[z]! then
      reachableIh b cs ks args (← forallTelescope (← inferType args[z]!) fun ys _ =>
        pure (mkAppN args[z]! ys))

/--
The refusal for a constructor that *builds* an index at one of the block's
propositions rather than taking the proof as a field. -/
def throwBuiltProof {α} (b : Block) (i : Nat) (c : CtorSpec) (p : Nat) (a : Expr) :
    TermElabM α :=
  throwError "The resulting type of `{c.name}` builds the index{indentExpr a}\nwhich is a \
    proof, at index {p + 1} of `{b.members[i]!.name}`.  Erasure deletes an index at one of \
    the block's propositions and hands it back to the well-formedness, where proof \
    irrelevance leaves nothing to say which proof it was, so a constructor has to take \
    that index as a field rather than build it"

/--
An index a constructor builds rather than takes as a field, checked to be a term
the erasure can state. -/
partial def statableIdx (b : Block) (c : CtorSpec) (kinds : Array FieldKind) (xs : Array Expr)
    (top e : Expr) : TermElabM Unit := do
  let bad (why : MessageData) : TermElabM Unit :=
    throwError "The resulting type of `{c.name}` builds the index{indentExpr top}\nwhich the \
      erasure has to delete, and {why}"
  match e.getAppFn with
  | .fvar id =>
    let some q := (Array.range xs.size).find? (xs[·]!.fvarId! == id)
      | bad m!"`{e.getAppFn}` in it is not one of the constructor's fields"
    if kinds[q]! == .erased then
      bad m!"the field `{xs[q]!}` in it is an erased proof, which the pre-world drops"
    else
      e.getAppArgs.forM (statableIdx b c kinds xs top)
  | .const n _ =>
    unless b.named (fun _ => true) n do
      return ← e.getAppArgs.forM (statableIdx b c kinds xs top)
    let some (_, cs) := (b.ctorsOf b.dataIdxs).find? (·.2.name == b.unRaw n)
      | bad m!"`{n}` in it is no data constructor of the block, so the pre-world has \
          nothing to say it with"
    -- read off the type, not off `kinds`: the constructors are classified one
    -- after another, and this one may not have been reached yet
    if e.getAppNumArgs != (← forallTelescope cs.type fun ys _ => pure ys.size) then
      bad m!"`{n}` is not fully applied in it"
    else
      -- the arguments erasure keeps, and only those: `Ctx._pre.snoc` has no
      -- proof to take, so `Ctx.snoc Γ h` is a term the pre-world can say
      -- whatever the proof `h` was made of
      let args := e.getAppArgs
      forallTelescope cs.type fun ys _ =>
        for z in *...args.size do
          let ty := (← inferType ys[z]!).headBeta
          unless b.mentionsProp ty && (← isProp ty) do
            statableIdx b c kinds xs top args[z]!
  | _ => bad m!"it is not built out of the constructor's fields and the block's constructors"

/-- `reachableIh` at every deleted index every data constructor recurses under
that a hypothesis is wanted at; one at a proposition is not, having none to
want -- see `MemberSpec.dropIhs`. -/
def checkIhReachable (b : Block) : TermElabM Unit := owning do
  if b.members.all (·.dropped.isEmpty) then return
  for i in b.dataIdxs do
    for c in b.members[i]!.ctors do
      let kinds := b.fieldKinds c.kinds
      forallBoundedTelescope c.type b.numParams fun _ rest =>
        forallTelescope rest fun xs _ => do
          for k in *...xs.size do
            if let .recur mm := kinds[k]! then
              unless b.members[mm]!.dropped.isEmpty do
                discard <| b.withRecTarget? (← inferType xs[k]!) fun _ _ args =>
                  (b.ihDrops mm (b.dropArgs mm args)).forM (reachableIh b c kinds xs)

/-- Re-declare the scratch axioms at the block's own universe parameters. -/
private def restub (r : Raw) (us : List Name) (arities : Array Expr)
    (ctorTypes : Array (Array Expr)) : TermElabM Unit := do
  let some env0 := r.stubEnv | return
  let env ← getEnv
  let mut todo : Array (Name × Expr) := #[]
  for i in *...r.names.size do
    -- only what really was stubbed: `withRaw` leaves the `Prop` members'
    -- constructors out, since nothing is elaborated against them
    if env.contains r.names[i]! then
      todo := todo.push (r.names[i]!, arities[i]!)
    for j in *...r.ctorNames[i]!.size do
      if env.contains r.ctorNames[i]![j]! then
        todo := todo.push (r.ctorNames[i]![j]!, ctorTypes[i]![j]!)
  setEnv env0
  stubBatch us todo

/--
The pre-types of some of a block's members, as inductive types over the scratch
axioms. -/
private def preInds (b : Block) (us : List Name) (idxs : Array Nat) (stubCtors : Bool) :
    TermElabM (Array InductiveType) := do
  let arity (i : Nat) : TermElabM Expr := do
    if b.members[i]!.dropped.isEmpty then return b.tr b.members[i]!.type
    forallBoundedTelescope b.members[i]!.type b.numParams fun ps rest =>
      forallTelescope rest fun is res => mkForallFVars (ps ++ b.keptIdxs i is) res
  for i in idxs do
    stubAxiomAt us (preName b.members[i]!.name) (← arity i)
  idxs.mapM fun i => do
    let m := b.members[i]!
    let mut cs : Array Constructor := #[]
    for c in m.ctors do
      -- a deleted field needs no stand-in here: every mention of it is an index
      -- of a member that has deleted it too, so `tr` is what takes it away
      let type ← forallTelescope c.type fun xs concl =>
        withPreFields b c.kinds xs #[] #[] fun olds news _ _ =>
          mkForallFVars news (b.tr (concl.replaceFVars olds news))
      if stubCtors then stubAxiomAt us (b.preOf c.name) type
      cs := cs.push { name := b.preOf c.name, type }
    return { name := preName m.name, type := ← arity i, ctors := cs.toList }

/-- The section variables the block uses, folded in as its leading parameters. -/
private def withSectionVars (r : Raw) : TermElabM Raw := do
  if r.vars.isEmpty then return r
  let mut st : CollectFVars.State := {}
  for a in r.arities do st := collectFVars st a
  for ts in r.ctorTypes do
    for t in ts do st := collectFVars st t
  for (_, e) in r.copies do st := collectFVars st e
  let mut keep : Array FVarId := #[]
  let mut grew := true
  while grew do
    grew := false
    for v in r.vars do
      let id := v.fvarId!
      if keep.contains id then continue
      let ty ← id.getType
      let wanted := st.fvarSet.contains id ||
        ((← id.getDecl).binderInfo == .instImplicit && keep.any (ty.containsFVar ·))
      if wanted then
        keep := keep.push id
        st := collectFVars st ty
        grew := true
  let used := r.vars.filter (keep.contains ·.fvarId!)
  if used.isEmpty then return r
  let blockNames := r.blockNames
  let fix (e : Expr) : Expr :=
    e.replace fun s => match s with
      | .const n ls => if blockNames.contains n then some (mkAppN (.const n ls) used) else none
      | _ => none
  let arities ← r.arities.mapM fun a => mkForallFVars used (fix a)
  let ctorTypes ← r.ctorTypes.mapM (·.mapM fun t =>
    return implicitPrefix used.size (← mkForallFVars used (fix t)))
  let copies ← r.copies.mapM fun (n, e) => return (n, ← mkLambdaFVars used (fix e))
  return { r with arities, ctorTypes, copies, numParams := r.numParams + used.size }

/-- Everything between the elaborated block and the `Plan`. -/
def prepareCore (r : Raw) : TermElabM Plan := do
    let r ← withSectionVars r
    let n := r.names.size
    let numParams := r.numParams
    let blockNames := r.blockNames
    let mut arities := r.arities
    let mut ctorTypes := r.ctorTypes
    -- which members are propositions, and at what universe each one lives
    let (isProp, levels) ← memberLevels r.names arities
    let preIsHeterogeneous ← checkDataArities r.names isProp levels
    -- the same-universe rule is what pins a copy's level metavariable, so read
    -- everything it could be in back afterwards: nothing else will assign it, and
    -- a `Sort ?u` reaching the kernel is a declaration with metavariables
    arities ← arities.mapM instantiateMVars
    ctorTypes ← ctorTypes.mapM (·.mapM instantiateMVars)
    let levels ← levels.mapM instantiateLevelMVars
    -- the block's universe parameters: whichever of the declared and auto-bound
    -- ones anything in the block actually uses, in Lean's own order
    let mut cps : CollectLevelParams.State := {}
    for i in *...n do
      cps := collectLevelParams cps arities[i]!
      for t in ctorTypes[i]! do
        cps := collectLevelParams cps t
    let us ← match sortDeclLevelParams r.scopeLevelNames r.declLevelNames cps.params with
      | .ok us => pure us
      | .error msg => throwError msg
    let lvls := us.map Level.param
    arities := arities.map (normLevels blockNames lvls)
    ctorTypes := ctorTypes.map (·.map (normLevels blockNames lvls))
    -- the peeled members leave the block here, taking their types with them
    -- exactly as they were written
    let peeled : Array InductiveType := r.peeled.map fun i =>
      let cs := (Array.range r.ctorNames[i]!.size).map fun j =>
        ({ name := r.ctorNames[i]![j]!, type := ctorTypes[i]![j]! } : Constructor)
      { name := r.names[i]!, type := arities[i]!, ctors := cs.toList }
    let keep := (Array.range n).filter (!r.peeled.contains ·)
    let r := { r with names := keep.map (r.names[·]!)
                      ctorNames := keep.map (r.ctorNames[·]!) }
    let n := keep.size
    arities := keep.map (arities[·]!)
    ctorTypes := keep.map (ctorTypes[·]!)
    let isProp := keep.map (isProp[·]!)
    let levels := keep.map (levels[·]!)
    let dataIdxs := (Array.range n).filter (!isProp[·]!)
    let propIdxs := (Array.range n).filter (isProp[·]!)
    let propLayers ← propLayers r.names arities ctorTypes isProp
    restub r us arities ctorTypes
    -- a skeleton is enough for `Block.mentions`, `Block.preOf` and `Block.memberIdx?`
    let skeleton : Block :=
      { numParams, us
        members := (Array.range n).map fun i =>
          { name := r.names[i]!, type := arities[i]!, isProp := isProp[i]!
            level := levels[i]!
            ctors := (Array.range ctorTypes[i]!.size).map fun j =>
              { name := r.ctorNames[i]![j]!, type := ctorTypes[i]![j]!,
                kinds := #[] } } }
    -- which indices the pre-world has to delete has to be settled before any
    -- constructor is classified, since a deleted index is what a field becomes
    let drops ← droppedIndices skeleton
    let skeleton : Block :=
      { skeleton with
        members := skeleton.members.mapIdx fun i m =>
          { m with dropped := drops[i]!.1, dropIhs := drops[i]!.2 } }
    -- a *data* member's index of that shape is refused rather than denested: the
    -- index is deleted, so it travels as a pre-type and returns as a subtype of
    -- it, and a `List` of them is neither.  This is the last place that can tell
    for j in dataIdxs do
      if r.copies.any (·.1 == r.names[j]!) then continue
      forallTelescope arities[j]! fun idxs _ => do
        for y in idxs do
          let head := (← inferType y).getAppFn.constName?
          if let some (_, orig) := r.copies.find? fun (n, _) => head == some n then
            throwError "The index `{y}` of `{r.names[j]!}` is{indentExpr orig}\nwhich mentions a \
              member of the block without being one, so the erasure has no pre-type to state it \
              at"
    -- a `Prop` member's index is rewritten by taking each argument to the
    -- pre-world, and that is only possible one index at a time: an index whose
    -- type merely *contains* a member, `List Ctx`, has no such image
    for j in propIdxs do
      forallTelescope arities[j]! fun idxs _ => do
        for y in idxs do
          let ty ← inferType y
          unless (← recTargetOf? skeleton ty).isSome do
            if skeleton.mentions ty then
              throwError "The index `{y}` of `{r.names[j]!}` mentions the block \
                without being a member's type, so it has no counterpart on the erased \
                types:{indentExpr ty}"
    -- classify every constructor's fields
    let mut members := skeleton.members
    for i in dataIdxs do
      let mut cs := #[]
      for c in skeleton.members[i]!.ctors do
        cs := cs.push { c with kinds := ← classifyDataCtor skeleton i c }
      members := members.set! i { members[i]! with ctors := cs }
    for i in propIdxs do
      let mut cs := #[]
      for c in skeleton.members[i]!.ctors do
        cs := cs.push { c with kinds := ← classifyPropCtor skeleton c }
      members := members.set! i { members[i]! with ctors := cs }
    let b : Block := { members, numParams, us }
    checkDropped b
    checkIhReachable b
    -- refuse a cycle here rather than at emission, where the pre-block would
    -- already be in the environment
    discard <| ctorOrder b (← dataOrder b)
    -- the pre-world, still against scratch axioms
    let preDataInds ← preInds b us b.dataIdxs (stubCtors := true)
    -- one layer at a time, so that a layer's arities find the pre-types of the
    -- ones before it already stubbed
    let prePropInds ← propLayers.mapM fun layer => preInds b us layer (stubCtors := false)
    -- `X._wf`, one conjunct per recursive field and one per erased proof field
    let wfDecls ← forallBoundedTelescope b.members[b.dataIdxs[0]!]!.type numParams
        fun ps _ => do
      -- a motive ends in the member's deleted indices, because that is where
      -- `_wf` has to take them back: `Ctx0 → Prop` rather than `Prop`, which is
      -- still a `Prop`, since `imax _ 0` is `0`
      let motiveLevel ← b.wfMotiveLevel ps
      let (pad, padVal) := wfPad motiveLevel
      let mut motives : Array Expr := #[]
      for i in b.dataIdxs do
        motives := motives.push <| ←
          forallTelescope (← instantiateForall b.members[i]!.type ps) fun idxs _ => do
            let res ← mkDropForall (← b.dropTysAt i ps idxs) (mkArrows pad (mkSort Level.zero))
            withLocalDeclD `t (b.preApp i (ps ++ idxs)) fun t =>
              mkLambdaFVars (b.keptIdxs i idxs ++ #[t]) res
      let mut wfMinors : Array Expr := #[]
      for i in b.dataIdxs do
        for c in b.members[i]!.ctors do
          let kinds := b.fieldKinds c.kinds
          let minor ← forallTelescope (← b.ctorType c ps) fun xs concl => do
            -- the deleted indices are what the motive ends in, so the minor
            -- takes them last, all of them and at their pre-types
            let dropped := b.members[i]!.dropped
            -- the kept indices a dropped one's pre-type names are read at the
            -- constructor's own values for them, which is where they are the
            -- fields the pre-world left alone rather than the arity's binders
            let dts ← b.dropTysAt i ps (b.idxArgs concl.getAppArgs)
            let mut dDecls : Array (Name × (Array Expr → TermElabM Expr)) := #[]
            for q in *...dropped.size do
              let n ← match deletedField? kinds dropped[q]! with
                | some j => xs[j]!.fvarId!.getUserName
                | none => pure `d
              dDecls := dDecls.push (n, fun prev => pure (dts[q]!.beta prev))
            let padDecls : Array (Name × (Array Expr → TermElabM Expr)) :=
              pad.map fun t => (`_pad, fun _ => pure t)
            withLocalDeclsD dDecls fun dels =>
             withLocalDeclsD padDecls fun pads => do
              let mut fOlds : Array Expr := #[]
              let mut fNews : Array Expr := #[]
              for q in *...dropped.size do
                if let some j := deletedField? kinds dropped[q]! then
                  fOlds := fOlds.push xs[j]!
                  fNews := fNews.push dels[q]!
              withPreFields b kinds xs fOlds fNews fun olds news imgs subTys => do
                let recPos := recPositions kinds
                let ihDecls : Array (Name × (Array Expr → MetaM Expr)) := recPos.map fun k =>
                  (`ih, fun _ => b.ihTy ps pad subTys[k]!)
                withLocalDeclsD ihDecls fun ihs => do
                  let mut conjs : Array Expr := #[]
                  for q in *...recPos.size do
                    -- closed over the erased fields it names, exactly as
                    -- `Block.wfConjs` closes the conjunct this one has to match
                    let conj ← b.ihConj ihs[q]! padVal subTys[recPos[q]!]!
                    conjs := conjs.push <| ← b.closeErased imgs subTys
                      (erasedDeps kinds imgs subTys conj recPos[q]!) 0 #[] #[] conj
                  for k in *...xs.size do
                    if kinds[k]! == .erased then
                      conjs := conjs.push (← b.erasedConj kinds imgs subTys k)
                  for (_, eq) in ← b.builtEqs i kinds concl olds news dels do
                    conjs := conjs.push eq
                  mkLambdaFVars (keptImages kinds imgs ++ ihs) <|
                    ← mkLambdaFVars (dels ++ pads) (foldConj conjs 0)
          wfMinors := wfMinors.push minor
      let mut wfDecls : Array (Name × Expr × Expr) := #[]
      for i in b.dataIdxs do
        let m := b.members[i]!
        -- one motive universe, the one they were all brought to; a lowered
        -- pre-block wants one per component, which `widenPreRecLevels` supplies
        let rec' := mkConst (preDataRecName preIsHeterogeneous m.name) (motiveLevel :: b.lvls)
        let (type, value) ← forallTelescope (← instantiateForall m.type ps) fun is _ =>
          b.withValIdxs i ps is fun vis =>
            withLocalDeclD `t (b.preApp i (ps ++ vis)) fun t => do
              let type ← mkForallFVars (ps ++ vis ++ #[t]) (mkSort Level.zero)
              -- the recursion is over the pre-term, so the deleted indices
              -- cannot travel with the others: they come after the major
              -- premise, out of the motive, in the order the arity had them
              let value ←
                if m.dropped.isEmpty && padVal.isEmpty then
                  mkLambdaFVars ps (mkAppN rec' (ps ++ motives ++ wfMinors))
                else
                  let args := ps ++ motives ++ wfMinors ++ b.keptIdxs i vis ++ #[t] ++
                    b.dropIdxs i vis ++ padVal
                  mkLambdaFVars (ps ++ vis ++ #[t]) (mkAppN rec' args)
              return (type, value)
        wfDecls := wfDecls.push (wfName m.name, type, value)
      return wfDecls
    return { block := b, preDataInds, prePropInds, propLayers, wfDecls, preIsHeterogeneous,
             peeled, peeledIdxs := r.peeled
             copies := r.copies.map fun (n, e) => (n, normLevels blockNames lvls e) }
where
  /-- Every field of a data constructor is `plain`, `recur` or `erased`. -/
  classifyDataCtor (b : Block) (i : Nat) (c : CtorSpec) : TermElabM (Array FieldKind) :=
    forallTelescope c.type fun xs concl => do
      let dName := b.members[i]!.name
      unless concl.getAppFn.constName? == some dName do
        throwError "The resulting type of `{c.name}` must be `{dName}` itself"
      let mut kinds := #[]
      for x in xs do
        -- a bundle written as a `Subtype` reaches us as `(fun t => P t) val`,
        -- whose *binder* mentions a data member though the proposition does
        -- not; classify what the field says, not how it was spelled
        let ty := (← inferType x).headBeta
        if b.mentionsProp ty && (← isProp ty) then
          -- erasing this field must be definitionally invisible, which it is
          -- exactly when no data member appears in its type: then `P args`
          -- unfolds to `P._pre args'` and the two readings agree
          if b.mentionsData ty then
            throwError "The proof field `{x}` of `{c.name}` mentions a \
              data member of the block in its type, so erasing it would not be \
              definitionally invisible:{indentExpr ty}"
          kinds := kinds.push .erased
          continue
        match ← recTargetOf? b ty with
        | some (m, ysClean) =>
          unless ysClean do
            throwError "The field `{x}` of `{c.name}` binds a member of \
              the block before recursing, which erasure cannot follow: a pre-world value \
              cannot be turned back into a real one without its well-formedness \
              proof.{indentExpr ty}"
          if b.members[m]!.isProp then
            throwError "The field `{x}` of `{c.name}` has a `Prop` \
              member's type but is not a proof:{indentExpr ty}"
          kinds := kinds.push (.recur m)
        | none =>
          if b.mentions ty then
            throwError "The field `{x}` of `{c.name}` mentions the block, but is neither a \
              member's type nor a proof of one of the block's propositions, so this lowering \
              cannot erase it:{indentExpr ty}"
          kinds := kinds.push .plain
      -- what the arity deletes, the constructor deletes with it
      let idxArgs := b.idxArgs concl.getAppArgs
      let dropped := b.members[i]!.dropped
      -- which of the member's own indices each of them is stated at, which
      -- decides both what a field given twice may stand for and what may be
      -- built at all
      let statedAt ← if dropped.isEmpty then pure #[] else
        forallBoundedTelescope b.members[i]!.type b.numParams fun _ rest =>
          forallTelescope rest fun aidxs _ =>
            aidxs.mapM fun y => do
              let ty ← inferType y
              return (Array.range aidxs.size).filter fun z => ty.containsFVar aidxs[z]!.fvarId!
      -- the deleted indices each field is given as, in arity order
      let mut given : Array (Nat × Array Nat) := #[]
      for p in dropped do
        let some k := (Array.range xs.size).find? (idxArgs[p]! == xs[·]!) | continue
        match given.findIdx? (·.1 == k) with
        | some z => given := given.modify z fun (k, ps) => (k, ps.push p)
        | none => given := given.push (k, #[p])
      let mut built : Array Nat := #[]
      for p in dropped do
        let a := idxArgs[p]!
        match (Array.range xs.size).find? (a == xs[·]!) with
        | none =>
          if b.dropAtProp i p then throwBuiltProof b i c p a
          statableIdx b c kinds xs a a
          built := built.push p
        | some k =>
          -- a field can stand for only one of the indices it is given as --
          -- `Sub.id : (Γ : Ctx) → Sub Γ Γ` gives its context as both -- and
          -- which one is not free: only the reading the field *is* leaves a
          -- field typed at that index at a term the alternative has
          let ps := (given.find? (·.1 == k)).getD (k, #[p]) |>.2
          let keep := (ps.find? fun p' =>
            dropped.any fun r => !ps.contains r && statedAt[r]!.contains p').getD ps[0]!
          if p != keep then
            if b.dropAtProp i p then throwBuiltProof b i c p a
            statableIdx b c kinds xs a a
            built := built.push p
            continue
          -- a proof field given as an index is deleted like any other
          let m ← match kinds[k]!, ← recTargetOf? b (← inferType xs[k]!).headBeta with
            | .recur m, _ | .erased, some (m, true) => pure m
            | _, _ =>
              throwError "The resulting type of `{c.name}` gives index {p + 1} as the field \
                `{a}`, which is not a value of a member of the block"
          kinds := kinds.set! k (.deleted m p)
      -- an index taken as a field, but stated at one the constructor built,
      -- cannot stay a field: the alternative binds the built index, so the
      -- field would sit at the constructor's reading of something the
      -- alternative only has a binder for
      for p in dropped do
        let some k := deletedField? kinds p | continue
        -- a proof index is not promoted: erasure drops the field whatever else
        -- happens to it, so there is no reading of it for the field to be left
        -- at, and no equation for the two to be said to agree by
        if b.dropAtProp i p then continue
        unless statedAt[p]!.any built.contains do continue
        let .deleted m _ := kinds[k]! | continue
        kinds := kinds.set! k (.recur m)
        built := built.push p
        statableIdx b c kinds xs idxArgs[p]! idxArgs[p]!
      checkIndexArgs b c kinds xs (b.keptArgs i concl.getAppArgs) "the resulting type"
      for k in *...xs.size do
        if kinds[k]! != .plain then
          continue
        if (← inferType xs[k]!).hasAnyFVar fun v =>
            (Array.range xs.size).any fun q => kinds[q]! != .plain && xs[q]!.fvarId! == v then
          throwError "The field `{xs[k]!}` of `{c.name}` depends on a \
            field the erasure has to move or drop"
      return kinds
  /-- A `Prop` constructor erases nothing; every field is `plain` or `recur`. -/
  classifyPropCtor (b : Block) (c : CtorSpec) : TermElabM (Array FieldKind) :=
    forallTelescope c.type fun xs _ => do
      let mut kinds := #[]
      for x in xs do
        let ty ← inferType x
        match ← recTargetOf? b ty with
        | some (m, ysClean) =>
          unless ysClean do
            throwError "The field `{x}` of `{c.name}` binds a member of \
              the block before recursing, which erasure cannot follow:{indentExpr ty}"
          kinds := kinds.push (.recur m)
        | none =>
          if b.mentions ty then
            throwError "The field `{x}` of `{c.name}` mentions the block \
              other than as a member's type, which this lowering cannot rewrite:{indentExpr ty}"
          kinds := kinds.push .plain
      return kinds
  /-- `ty` as `∀ ys, M args`, with whether `ys` avoids the block. -/
  recTargetOf? (b : Block) (ty : Expr) : TermElabM (Option (Nat × Bool)) :=
    b.withRecTarget? ty fun ys m _ => do
      let mut clean := true
      for y in ys do
        if b.mentions (← inferType y) then clean := false
      return (m, clean)
  /-- A data constructor's index arguments have to survive erasure untouched. -/
  checkIndexArgs (b : Block) (c : CtorSpec) (kinds : Array FieldKind) (xs args : Array Expr)
      (what : String) : TermElabM Unit := do
    for a in args do
      if b.mentions a then
        throwError "{what} of `{c.name}` mentions the block in an index:{indentExpr a}"
      for k in *...xs.size do
        if kinds[k]! != .plain && a.containsFVar xs[k]!.fvarId! then
          throwError "{what} of `{c.name}` uses the field \
            `{xs[k]!}` as an index, but erasure has to move or drop \
            it{indentExpr a}"

/-- Elaborate a written block into a `Raw`, and hand it on. -/
def withRaw {α} (views : Array InductiveView) (vars : Array Expr := #[])
    (k : Raw → TermElabM α) : TermElabM α := do
  checkSupported views
  let scopeLevelNames ← Term.getLevelNames
  withoutModifyingEnv <| Term.withLevelNames views[0]!.levelNames do
    -- everything added from here on is a scratch axiom, and `restub` rewinds to
    -- this point to re-declare them at the block's own universe parameters
    let env0 ← getEnv
    let n := views.size
    let names := views.map (·.declName)
    -- the block's own names; inside the scratch environment that is everything
    -- of the block there is to mention
    let blockNames : Array Name :=
      views.flatMap fun v => #[v.declName] ++ v.ctors.map (·.declName)
    -- the arities, by worklist
    let mut arities : Array (Option Expr) := (List.replicate n none).toArray
    let mut paramCounts : Array Nat := (List.replicate n 0).toArray
    let mut lastErr : Option Exception := none
    let mut progress := true
    while progress do
      progress := false
      for i in *...n do
        if arities[i]!.isSome then
          continue
        let s ← Term.saveState
        try
          let (ty, np) ← elabArity views views[i]!
          unless ← isTypeFormerType ty do
            throwError "The resulting type of `{views[i]!.declName}` is not a sort"
          stubAxiom views[i]!.declName ty
          arities := arities.set! i (some ty)
          paramCounts := paramCounts.set! i np
          progress := true
        catch ex =>
          lastErr := some ex
          s.restore
    for i in *...n do
      if arities[i]!.isNone then
        match lastErr with
        | some ex => throw ex
        | none => throwError "Could not elaborate the arity of `{views[i]!.declName}`"
    let arities' := arities.map (·.get!)
    -- `mutual` already demands that the members' parameters agree, but nothing
    -- has checked it yet, and the whole encoding shares one telescope
    let numParams := paramCounts[0]!
    for i in *...n do
      unless paramCounts[i]! == numParams do
        throwError "`{views[0]!.declName}` takes {numParams} parameter(s) and \
          `{views[i]!.declName}` takes {paramCounts[i]!}; every member of a mutual block must \
          take the same ones"
    let paramShape (t : Expr) : MetaM Expr :=
      forallBoundedTelescope t numParams fun ps _ => mkForallFVars ps (mkConst ``Unit)
    for i in *...n do
      unless ← isDefEq (← paramShape arities'[0]!) (← paramShape arities'[i]!) do
        throwError "The parameters of `{views[0]!.declName}` and `{views[i]!.declName}` differ; \
          every member of a mutual block must take the same ones"
    -- the same checks `prepareCore` makes, made here too so that a block
    -- erasure cannot reach is turned away before its constructors are read
    let (isProp, levels) ← memberLevels names arities'
    -- run for its checks and its level unification; which route the pre-block
    -- takes is settled again, on the final arities, in `prepareCore`
    discard <| checkDataArities names isProp levels
    let dataIdxs := (Array.range n).filter (!isProp[·]!)
    let propIdxs := (Array.range n).filter (isProp[·]!)
    -- a constructor of an indexed family has to say what its indices are; Lean
    -- refuses this too, and here the fallback would silently make the resulting
    -- type the unapplied family, which is not even a proposition
    for i in *...n do
      let arityBinders ← forallTelescope arities'[i]! fun xs _ => pure xs.size
      if arityBinders > numParams then
        for c in views[i]!.ctors do
          if c.type?.isNone then
            withRef c.ref <| throwError "Missing resulting type for constructor \
              `{c.declName}`.  It must be given because `{views[i]!.declName}` is an \
              inductive family"
    -- the constructors, a member at a time, each after the members its arity
    -- names.  An index is built out of the indexing member's own constructors:
    -- `Tm : (Γ : Ctx) → Ok Γ → Type` has `Tm.top : Tm .nil .nil`, whose second
    -- `.nil` is `Ok`'s
    let mut ctorTypes : Array (Array Expr) := (List.replicate n (#[] : Array Expr)).toArray
    let mut pending := dataIdxs ++ propIdxs
    while !pending.isEmpty do
      let ready := pending.filter fun i =>
        !arities'[i]!.getUsedConstants.any fun c =>
          pending.any fun j => j != i && names[j]! == c
      let ready := if ready.isEmpty then #[pending[0]!] else ready
      for i in ready do
        let tys ← views[i]!.ctors.mapM (elabCtorType views views[i]! ·)
        ctorTypes := ctorTypes.set! i tys
        for j in *...tys.size do
          stubAxiom views[i]!.ctors[j]!.declName tys[j]!
      pending := pending.filter (!ready.contains ·)
    -- a member whose resulting type was left out was guessed at `Type`
    for i in *...n do
      if views[i]!.type?.isNone then
        for j in *...ctorTypes[i]!.size do
          forallBoundedTelescope ctorTypes[i]![j]! numParams fun _ t =>
            forallTelescope t fun xs _ => do
              for x in xs do
                let ty ← inferType x
                if ty.getUsedConstants.any (blockNames.contains ·) then
                  continue
                let l ← getLevel ty
                unless ← isLevelDefEq (mkLevelMax l levels[i]!) levels[i]! do
                  let at_ := toString (← ppExpr (mkSort l))
                  let want := toString (← ppExpr (mkSort (mkLevelMax l levels[i]!).normalize))
                  throwError "`{views[i]!.declName}` gives no resulting type, so it was read \
                    as `Type`; but the field `{x}` of `{views[i]!.ctors[j]!.declName}` lives \
                    in `{at_}`, which does not fit.  Write the resulting type \
                    out: `inductive {views[i]!.declName} : {want}`"
    k { names, ctorNames := views.map (·.ctors.map (·.declName))
        arities := arities', ctorTypes, numParams, scopeLevelNames
        declLevelNames := views[0]!.levelNames, stubEnv := some env0, vars }

/-! ## Denesting into the block

A *nested* occurrence is a member of the block appearing inside the parameters
of some other inductive type, as `RecWFTree` does in

```lean
inductive RecWFTree where
  | mk (x : WFTree RecWFTree)
```

The kernel handles these by specialising the nesting type constructor to the
block: `WFTree RecWFTree` becomes a new member and the enlarged block is checked
instead.  `Mumi.Denest` does the same at the elaborator.  Neither can do it here:
the specialisation of `Tree.WF` is `Tree.WF RecWFTree : Tree RecWFTree → Prop`,
whose *arity* mentions the copy of `Tree`, so the enlarged block is
induction-inductive.  It is done again here against the `Raw` above, and the
result goes through `prepareCore` like any other.

Two things differ from `Mumi.Denest`.  The members are *constants*, their scratch
axioms, so an occurrence is recognised by name.  And the rewrite is structural
rather than head-only, a copied constructor being able to appear in an index:
`Tree.WFWith.empty` ends in `Tree.WFWith α .empty []`, whose `.empty` must become
the copy's.
-/

/-!
A nesting applied to something that mentions a field of the constructor it sits
in -- `mk (n : Nat) (x : OkFam A n)` -- cannot become a copy with `n` among its
parameters, a member's parameters being fixed before any constructor is
elaborated.  It becomes a copy *indexed* by `n`, with the field abstracted out of
the parameters on the way in.  That abstraction must survive between the two
passes, which see one occurrence as different expressions: `scanExpr` walks under
binders with free variables, `rwExpr` walks the raw expression with de Bruijn
indices.  The parameters are therefore recorded as a *pattern*, an abstracted
field standing as a hole constant, and `matchHoles` reads back each hole.
-/

/-- The marker standing for the `j`-th field a copy's parameters were abstracted over. -/
private def mkHole (j : Nat) : Expr := .const (.num `_mumi.hole j) []

/-- Which hole `e` is, if it is one. -/
private def holeIdx? : Expr → Option Nat
  | .const (.num p j) [] => if p == `_mumi.hole then some j else none
  | _ => none

/-- Fill each hole in `e` with what `vals` gives it. -/
private def fillHoles (vals : Array Expr) (e : Expr) : Expr :=
  if vals.isEmpty then e else e.replace fun s => holeIdx? s >>= (vals[·]?)

/-- Is one of the first `d` loose bound variables in `e`? -/
private def hasLooseBVarBelow (e : Expr) (d : Nat) : Bool := Id.run do
  for i in *...d do
    if e.hasLooseBVar i then return true
  return false

/--
Match the pattern `p`, holes and all, against `e`, recording what each hole
stood for; a hole reached twice has to reach the same thing both times. -/
private partial def matchHoles (p e : Expr) (out : Array (Option Expr)) (depth := 0) :
    Option (Array (Option Expr)) :=
  if let some j := holeIdx? p then
    if hasLooseBVarBelow e depth then none
    else
      let v := if depth == 0 then e else e.lowerLooseBVars depth depth
      match out[j]? with
      | some (some prev) => if prev == v then some out else none
      | some none        => some (out.set! j (some v))
      | none             => none
  else match p, e with
    | .app f a, .app g b => do matchHoles a b (← matchHoles f g out depth) depth
    | .forallE _ d b _, .forallE _ d' b' _
    | .lam _ d b _, .lam _ d' b' _ =>
      do matchHoles b b' (← matchHoles d d' out depth) (depth + 1)
    | .letE _ t v b _, .letE _ t' v' b' _ =>
      do matchHoles b b' (← matchHoles v v' (← matchHoles t t' out depth) depth) (depth + 1)
    | .mdata _ b, e' => matchHoles b e' out depth
    | p', .mdata _ b => matchHoles p' b out depth
    | .proj _ i b, .proj _ i' b' => if i == i' then matchHoles b b' out depth else none
    | p', e' => if p' == e' then some out else none

/-- Open the telescope of fields a copy's parameters were abstracted over. -/
private def withHoles {m : Type → Type} [Monad m] [MonadControlT MetaM m] {α : Type}
    (tys : List (Name × Expr)) (acc : Array Expr) (k : Array Expr → m α) : m α :=
  match tys with
  | []           => k acc
  | (n, ty) :: r => withLocalDeclD n (fillHoles acc ty) fun y => withHoles r (acc.push y) k

/-- One nested application, and the member it is about to become. -/
private structure AuxSpec where
  /--
  `@I p₁ … p_k`: the type constructor applied to its parameters and nothing
  else. -/
  key       : Expr
  name      : Name
  /--
  `I`'s parameters, as they were written -- levels and all, unlike `key` -- with
  a hole wherever a field of the constructor was abstracted out. -/
  params    : Array Expr
  /--
  The fields those holes stand for: their names, for the copy's binders, and
  their types, each of which may mention the holes of the ones before it. -/
  localTys  : List (Name × Expr)
  indName   : Name
  /-- The levels `I` was applied at. -/
  levels    : List Level
  /-- How many of `I`'s arguments were specialised, which is `params.size`.  Not
  always `I`'s own parameter count -- see `specParams`. -/
  numParams : Nat
  ctors     : Array Name
  deriving Inhabited

private abbrev DenestM := StateRefT (Array AuxSpec) MetaM

/-- Does `e` mention any of `names`? -/
private def mentionsNames (names : Array Name) (e : Expr) : Bool :=
  e.getUsedConstants.any (names.contains ·)

/--
Put every constant of `names` at the empty level list, and every other level in
normal form, so that keys compare. -/
private def stripLevels (names : Array Name) (e : Expr) : Expr :=
  e.replace fun s =>
    match s with
    | .const n us =>
      if names.contains n then some (.const n [])
      else
        let us' := us.map (·.normalize)
        if us' == us then none else some (.const n us')
    | .sort u =>
      let u' := u.normalize
      if u' == u then none else some (.sort u')
    | _ => none

/-- How far into an occurrence's arguments the parameters a copy specialises reach. -/
private def specParams (names : Array Name) (info : InductiveVal) (args : Array Expr) : Nat :=
  Id.run do
    if !info.ctors.isEmpty then return info.numParams
    let mut k := 0
    for p in *...info.numParams do
      if mentionsNames names args[p]! then k := p + 1
    return if k == 0 then info.numParams else k

/--
Recognise a nested occurrence: an inductive type applied to parameters that
mention the block. -/
private def nestedApp? (names : Array Name) (e : Expr) :
    MetaM (Option (Expr × InductiveVal × List Level × Array Expr × Array Expr)) := do
  if !mentionsNames names e then return none
  let .const hd _ := e.getAppFn | return none
  if names.contains hd then return none
  let e ← exposeInduct e
  let .const iname lvls := e.getAppFn | return none
  let some (.inductInfo info) := (← getEnv).find? iname | return none
  let args := e.getAppArgs
  if args.size < info.numParams then return none
  let np := specParams names info args
  let params := args.extract 0 np
  if !params.any (mentionsNames names ·) then return none
  return some (mkAppN (.const iname lvls) params, info, lvls, params,
    args.extract np args.size)

mutual

/--
Intern the nested application `e` is, if it is one, and then look through the
copy's own arity and constructors for further nesting. -/
private partial def internNested (names : Array Name) (root : Name) (bound : Array FVarId)
    (e : Expr) : DenestM Unit := do
  let some (_, info, lvls, params, idxArgs) ← nestedApp? names e | return
  -- `Mumi.Denest` turns a nesting parameter that mentions a field of the
  -- constructor it sits in into an extra index of the copy, and so does this
  let mut want : Array FVarId := #[]
  for y in bound.reverse do
    if want.contains y || params.any (·.containsFVar y) then
      unless want.contains y do want := want.push y
      let ty ← y.getType
      for z in bound do
        if ty.containsFVar z then
          unless want.contains z do want := want.push z
  let ys := (bound.filter (want.contains ·)).map Expr.fvar
  let holes := (Array.range ys.size).map mkHole
  let params := params.map (·.replaceFVars ys holes)
  -- the key is what says whether this occurrence has been seen, so it comes
  -- before every complaint: scanning a copy reaches the copy itself again, and
  -- an index of its own is not one it has to be able to specialise
  if (← get).any (·.key == stripLevels names (mkAppN (.const info.name lvls) params)) then return
  for a in idxArgs do
    if mentionsNames names a then
      throwError m!"Cannot denest{indentExpr e}"
        ++ .note m!"`{info.name}` is applied to a member of the block in an index rather \
          than a parameter, and only parameters can be specialised"
  -- a local the copy gains may itself be typed by the block -- `List (Ty Γ)`
  -- makes a copy indexed by the `Γ` it was nested at -- and that is no obstacle
  -- here, only the statement that the copy is induction-inductive too, which is
  -- the thing this file was written to erase
  let mut localPats : Array (Name × Expr) := #[]
  for j in *...ys.size do
    let ty ← inferType ys[j]!
    localPats := localPats.push
      (← ys[j]!.fvarId!.getUserName, ty.replaceFVars (ys.extract 0 j) (holes.extract 0 j))
  let localTys := localPats.toList
  -- nesting into one member of a mutual family specialises the whole family:
  -- the members mention each other, so a copy of one is useless without copies
  -- of the rest
  let fam ← info.all.toArray.mapM getConstInfoInduct
  for fi in fam do
    let name := root ++ Name.mkSimple s!"nested_{shortName fi.name}_{(← get).size + 1}"
    modify (·.push { key := stripLevels names (mkAppN (.const fi.name lvls) params)
                     name, params, localTys, indName := fi.name, levels := lvls,
                     numParams := params.size, ctors := fi.ctors.toArray })
  -- the copies' own arities and constructors are fresh telescopes, so nothing
  -- this scan is under is a binder of theirs -- except the fields the parameters
  -- were abstracted over, which a nesting inside them may mention in turn
  withHoles localTys #[] fun ls => do
    let params := params.map (fillHoles ls)
    let inner := ls.map (·.fvarId!)
    for fi in fam do
      let some ci := (← getEnv).find? fi.name | return
      scanExpr names root inner (← instantiateForall (ci.instantiateTypeLevelParams lvls) params)
      for c in fi.ctors do
        scanExpr names root inner (← ctorTypeAt c lvls params)

/-- Look for nested occurrences everywhere in `e`, indices included. -/
private partial def scanExpr (names : Array Name) (root : Name) (bound : Array FVarId)
    (e : Expr) : DenestM Unit := do
  match e with
  | .app .. =>
    internNested names root bound e
    scanExpr names root bound e.getAppFn
    for a in e.getAppArgs do scanExpr names root bound a
  | .forallE n d b bi | .lam n d b bi =>
    scanExpr names root bound d
    -- go under the binder with a real local rather than into the raw body: a
    -- nesting that cannot be denested is reported with the offending
    -- expression in it, and a loose bvar prints as `#0`
    withLocalDecl n bi d fun x =>
      scanExpr names root (bound.push x.fvarId!) (b.instantiate1 x)
  | .letE n t v b _ =>
    scanExpr names root bound t; scanExpr names root bound v
    withLetDecl n t v fun x =>
      scanExpr names root (bound.push x.fvarId!) (b.instantiate1 x)
  | .mdata _ b | .proj _ _ b => scanExpr names root bound b
  | _ => pure ()

end

/--
The spec `app` is an occurrence of, and what its holes stood for there: a copy
whose parameters mention a field takes that field as a leading index, so those
come back to be passed on in front of the occurrence's own indices. -/
private def specOf? (names : Array Name) (specs : Array AuxSpec) (app : Expr) :
    Option (AuxSpec × Array Expr) := Id.run do
  let a := stripLevels names app
  -- `internNested` keys on the whole application, so a block holding both `List
  -- (Wrap R n)` and `List (Wrap R 0)` gets a member for each
  for s in specs do
    if s.localTys.isEmpty && s.key == a then return some (s, #[])
  for s in specs do
    unless s.localTys.isEmpty do
      if let some out := matchHoles s.key a (Array.replicate s.localTys.length none) then
        if let some ls := out.mapM id then return some (s, ls)
  return none

/-- `e` as an application of a specialised type, or of one of its constructors. -/
private def specHit? (names : Array Name) (specs : Array AuxSpec) (e : Expr) :
    MetaM (Option (Name × Array Expr)) := do
  let .const cn lvls := e.getAppFn | return none
  if names.contains cn then return none
  let args := e.getAppArgs
  -- a constructor carries its type's parameters, so its copy is found the same way
  if let some (.ctorInfo ci) := (← getEnv).find? cn then
    if args.size < ci.numParams then return none
    let some (s, ls) :=
      specOf? names specs (mkAppN (.const ci.induct lvls) (args.extract 0 ci.numParams))
      | return none
    return some (reroot s.indName s.name cn, ls ++ args.extract ci.numParams args.size)
  let some (app, _, _, _, idxArgs) ← nestedApp? names e | return none
  let some (s, ls) := specOf? names specs app | return none
  return some (s.name, ls ++ idxArgs)

/-- Replace every specialised occurrence in `e` by the member it became. -/
private partial def rwExpr (names : Array Name) (specs : Array AuxSpec) (ps : Array Expr)
    (auxLvls : List Level) (e : Expr) : MetaM Expr := do
  let rw := rwExpr names specs ps auxLvls
  Lean.Core.transform e (pre := fun e => do
    match e with
    | .app .. =>
      if mentionsNames names e then
        if let some (aux, rest) ← specHit? names specs e then
          return .done (mkAppN (.const aux auxLvls) (ps ++ (← rest.mapM rw)))
      return .done (mkAppN (← rw e.getAppFn) (← e.getAppArgs.mapM rw))
    | _ => return .continue)

/-- Copy the first `n` binder names and annotations from `model` onto `e`. -/
private def copyLeadingBinders : Nat → Expr → Expr → Expr
  | 0, _, e => e
  | n + 1, .forallE mn _ mb mbi, .forallE _ ty b _ =>
    .forallE mn ty (copyLeadingBinders n mb b) mbi
  | _, _, e => e

/-- Specialise every nested occurrence in `r` into a member of its own. -/
def denestRaw (r : Raw) : TermElabM Raw := do
  let names := r.blockNames
  let root := r.names[0]!
  -- one telescope for the whole pass: a spec's key holds the parameters as they
  -- appear under *these* binders, so a second telescope would not match it
  forallBoundedTelescope r.arities[0]! r.numParams fun ps _ => do
    -- a peeled member is not part of what is being denested: it is declared
    -- afterwards, over the block as the writer reads it, so its own occurrences
    -- of a nesting are the nesting and want no copy made of them
    let scan : DenestM Unit := do
      for i in *...r.arities.size do
        if r.peeled.contains i then continue
        scanExpr names root #[] (← instantiateForall r.arities[i]! ps)
        for ct in r.ctorTypes[i]! do
          scanExpr names root #[] (← instantiateForall ct ps)
    let (_, specs) ← scan.run #[]
    if specs.isEmpty then return r
    -- the copies are referenced exactly as the members are: one metavariable
    -- per universe name in scope, which `normLevels` replaces with the block's
    let auxLvls ← (← Term.getLevelNames).mapM fun _ => mkFreshLevelMVar
    let auxNames := specs.map (·.name)
    let rw (e : Expr) : MetaM Expr := rwExpr names specs ps auxLvls e
    -- rewrite in place, keeping the original expression where nothing changed
    let rwTop (model : Expr) : MetaM Expr := do
      let body ← instantiateForall model ps
      let body' ← rw body
      if body' == body then return model
      return copyLeadingBinders r.numParams model (← mkForallFVars ps body')
    let arities ← r.arities.mapIdxM fun i a =>
      if r.peeled.contains i then pure a else (rwTop a : MetaM Expr)
    let ctorTypes ← r.ctorTypes.mapIdxM fun i cts =>
      if r.peeled.contains i then pure cts else cts.mapM fun c => (rwTop c : MetaM Expr)
    -- the copies themselves
    let mut auxArities : Array Expr := #[]
    let mut auxCtorTypes : Array (Array Expr) := #[]
    for s in specs do
      let ci ← getConstInfo s.indName
      -- a field the parameters were abstracted over becomes a leading index of
      -- the copy, and a leading argument of each of its constructors
      let (arity, cts) ← withHoles s.localTys #[] fun ls => do
        let params := s.params.map (fillHoles ls)
        -- a nesting whose parameter is a lambda -- `Σ _ : Nat, Wrap R n` passes
        -- `fun _ => Wrap R n` -- leaves a redex wherever the original mentions
        -- that parameter, and `Sigma.mk`'s `snd : β fst` becomes `(fun _ =>
        -- Wrap R n) fst`
        let resType ← Core.betaReduce
          (← instantiateForall (ci.instantiateTypeLevelParams s.levels) params)
        let arity := copyLeadingBinders r.numParams r.arities[0]!
          (← mkForallFVars (ps ++ ls) (← rw resType))
        let mut cts : Array Expr := #[]
        for c in s.ctors do
          let cty ← Core.betaReduce (← ctorTypeAt c s.levels params)
          cts := cts.push (implicitPrefix r.numParams (← mkForallFVars (ps ++ ls) (← rw cty)))
        return (arity, cts)
      auxArities := auxArities.push arity
      auxCtorTypes := auxCtorTypes.push cts
    -- stub the copies, arities before constructors and each after whatever it
    -- mentions: a copy's arity may name a copy interned after it
    let scopeLvls := (← Term.getLevelNames).reverse
    let what := "copies this nested inductive denests into"
    stubBatch scopeLvls
      ((Array.range specs.size).map fun k => (auxNames[k]!, auxArities[k]!)) what
    stubBatch scopeLvls ((Array.range specs.size).flatMap fun k =>
      (Array.range auxCtorTypes[k]!.size).map fun j =>
        (reroot specs[k]!.indName specs[k]!.name specs[k]!.ctors[j]!, auxCtorTypes[k]![j]!)) what
    -- what each copy stands for, kept for the bridge back to it
    let mut copies : Array (Name × Expr) := #[]
    for s in specs do
      let ci ← getConstInfoInduct s.indName
      let app ← withHoles s.localTys #[] fun ls => do
        let params := s.params.map (fillHoles ls)
        -- a parameter `specParams` left unspecialised is a leading index of the
        -- copy, and the original still wants it where its own parameters go, so
        -- it is abstracted here alongside the fields -- at the type the
        -- original gives it rather than the copy's, which is the one the bridge
        -- has to start from
        let res ← instantiateForall (ci.instantiateTypeLevelParams s.levels) params
        forallBoundedTelescope res (ci.numParams - s.numParams) fun ds _ => do
          instantiateMVars (← mkLambdaFVars (ps ++ ls ++ ds)
            (mkAppN (.const s.indName s.levels) (params ++ ds)))
      copies := copies.push (s.name, app)
    return { r with
      names := r.names ++ auxNames
      ctorNames := r.ctorNames ++ specs.map fun s => s.ctors.map (reroot s.indName s.name)
      arities := (← arities.mapM instantiateMVars) ++ (← auxArities.mapM instantiateMVars)
      ctorTypes := (← ctorTypes.mapM (·.mapM instantiateMVars)) ++
        (← auxCtorTypes.mapM (·.mapM instantiateMVars))
      copies := r.copies ++ copies }

/-! ## The bridge back to the originals

Denesting replaces `WFTree RecWFTree` with a copy of `WFTree` specialised at the
block, and a copy is not the type it copies: no arrangement of declarations makes
them defeq, the copy having to exist before `RecWFTree` and `WFTree RecWFTree`
not being writable until after.  Lean's own nested inductives have no copy at all
-- the kernel builds the enlarged block internally -- which an elaborator cannot
reproduce.  What can be arranged is that the copy never appears in anything the
writer reads.  The two types are *isomorphic*, and the isomorphism is definable:

* `X.ofOrig` sends the original to the copy, recursing on the original: a data
  copy's is compiled by structural recursion, a `Prop` copy's is a theorem built
  from the original's own `rec`.
* `X.toOrig` sends the copy back.  It recurses on the copy, a member of the
  lowered block, so it goes through the pre-type: `X.toOrigPre` is the structural
  recursion, over a motive taking the well-formedness of the indices *after* the
  term itself, and `X.toOrig` supplies them from the index it was handed.
* `X.ofOrig_toOrig : (X.ofOrig (X.toOrig x)).val = x.val` closes the round trip
  on the side the recursor needs, by recursion on the copy.

With `ofOrig`, the constructor the writer declared can be given the type they
wrote.  The kernel-facing constructor keeps the copy in its type under a hidden
name, `RecWFTree._nested_mk`, and `RecWFTree.mk` is a wrapper over it:

```lean
def RecWFTree.mk (x : WFTree RecWFTree) : RecWFTree := RecWFTree._nested_mk (ofOrig x)
```

The recursor gets the same treatment and needs the whole isomorphism.
`RecWFTree._nested_rec` is the kernel-facing one, with a motive for every member
of the enlarged block.  `X.rec` takes motives over the originals and applies
`_nested_rec` at `fun idxs t => C .. (X.toOrig t)`, which lines a minor stated
over a copy up with one stated over the original.  The exception is a renamed
constructor of the writer's own: the raw minor concludes at the raw constructor
applied to the copy-typed field, the nice one at the nice constructor applied to
`X.toOrig` of it, which unfolds to the raw one at `X.ofOrig (X.toOrig ..)`.  So
the conclusion is transported along `ofOrig_toOrig` one field at a time at the
`.val` level, and the wrapper's `ext` lifts the result back.

Copies whose originals are nested in each other -- `Rose T`, whose field is a
`List (Rose T)`, or the two members of a `mutual` family -- are compiled as one
group.  A group of data copies goes by structural recursion over the outer
original's recursor; a group of `Prop` copies is a mutual induction, each theorem
giving every copy a real motive so a sibling arrives as a hypothesis.  A group
that *mixes* the two has no such shape.

Nothing here is load-bearing: every step is attempted, and if any fails the
environment is rolled back, the plain names are defined as the raw declarations,
and the block is what it was before.
-/

/-- `e` with `n` leading lambdas stripped, and how many there were. -/
private def peelLams : Nat → Expr → Expr
  | 0,     e             => e
  | n + 1, .lam _ _ b _  => peelLams n b
  | _,     e             => e

/-- How many lambdas `e` starts with. -/
private def numHeadLams : Expr → Nat
  | .lam _ _ b _ => numHeadLams b + 1
  | _            => 0

/-- A member denesting added, and the type it is a copy of. -/
structure Copy where
  /-- Where the copy sits among the block's members. -/
  idx     : Nat
  /-- The copy's name. -/
  name    : Name
  /-- The inductive being copied. -/
  indName : Name
  /--
  `fun ls => I ps'`: that inductive applied to its parameters, under the block's
  parameters, abstracted over the constructor fields those parameters mentioned. -/
  app     : Expr
  /-- How many constructor fields `app` is abstracted over.  Usually none. -/
  numLocals : Nat := 0
  deriving Inhabited

/-- The original this copy stands for, at the locals `ls`. -/
def Copy.orig (c : Copy) (ls : Array Expr) : Expr := c.app.beta (ls.extract 0 c.numLocals)

/-- The original at the locals in `args`, applied to whatever else `args` holds. -/
def Copy.origAt (c : Copy) (args : Array Expr) : Expr :=
  c.app.beta args

/-- The original's image in the copy: `X.ofOrig : I ps' idxs → X ps idxs'`. -/
def Copy.ofName (c : Copy) : Name := c.name ++ `ofOrig

/--
The copy's own arguments for `e`, if `e` is this copy's original applied: the
locals the family member is at -- read off the occurrence, they being what says
*which* member of the family it is -- followed by the original's real indices. -/
def Copy.argsOf? (cp : Copy) (e : Expr) : MetaM (Option (Array Expr)) := do
  -- a nesting whose parameter is a lambda -- `Sigma`'s second one -- leaves the
  -- original applied under a redex, and the copy is at the head of its
  -- beta-normal form
  let e := e.headBeta
  let some hd := e.getAppFn.constName? | return none
  unless hd == cp.indName do return none
  let args := e.getAppArgs
  let s ← saveState
  let (ls, _, _) ← forallMetaBoundedTelescope (← inferType cp.app) cp.numLocals
  let app := cp.app.beta ls
  let n := app.getAppNumArgs
  if args.size ≥ n then
    if ← isDefEq (mkAppN e.getAppFn (args.extract 0 n)) app then
      let ls ← ls.mapM instantiateMVars
      unless ls.any (·.hasExprMVar) do
        return some (ls ++ args.extract n args.size)
  s.restore
  return none

/-- The bridge is built under one telescope of the block's parameters. -/
structure BridgeCtx where
  b      : Block
  /-- The block's parameters, as free variables. -/
  ps     : Array Expr
  copies : Array Copy
  /--
  The name the recursion over each copy is restated under.  A copy is named
  after the writer's own type, so this is a name the writer can reach, and the
  only one a statement about the copy's recursion has to name. -/
  copyRecs : Array Name := #[]
  deriving Inhabited

namespace BridgeCtx

/-- Which copy's original `e` is an application of, and the arguments it carries. -/
def copyOf? (c : BridgeCtx) (e : Expr) : MetaM (Option (Nat × Array Expr)) := do
  -- as in `Block.withRecTarget?`: a wrapper's proof field says
  -- `(fun t => P t) val`, and the copy is at the head of its beta-normal form
  let e := e.headBeta
  if e.getAppFn.constName?.isNone then return none
  -- a block may hold both `List (Wrap R n)`, whose copy stands for the family,
  -- and `List (Wrap R 0)`, whose copy stands for that one type
  for narrow in [true, false] do
    for k in *...c.copies.size do
      if (c.copies[k]!.numLocals == 0) != narrow then continue
      if let some args ← c.copies[k]!.argsOf? e then
        return some (k, args)
  return none

/-- The copy-world image of `x : ty`, where `ty` is stated in the original world. -/
def ofImage (c : BridgeCtx) (x ty : Expr) : MetaM Expr :=
  forallTelescope ty.headBeta fun ys concl => do
    let some (k, idxs) ← c.copyOf? concl | return x
    mkLambdaFVars ys <|
      mkAppN (mkConst c.copies[k]!.ofName c.b.lvls) (c.ps ++ idxs ++ #[mkAppN x ys])

/-- The copy-world images of a whole telescope, each read at its own type. -/
def ofImages (c : BridgeCtx) (xs : Array Expr) : MetaM (Array Expr) :=
  xs.mapM fun x => do c.ofImage x (← inferType x)

/-- The original of a copy, or of a copy's constructor, applied to `args`. -/
def unCopyHead? (c : BridgeCtx) (hd : Name) (args : Array Expr) : MetaM (Option Expr) := do
  if args.size < c.ps.size then return none
  let rest := args.extract c.ps.size args.size
  for cp in c.copies do
    -- a copy indexed by a constructor's field carries the field first, both as an
    -- index of its own and as a leading argument of each of its constructors
    if rest.size < cp.numLocals then continue
    let orig := cp.orig rest
    let rest := rest.extract cp.numLocals rest.size
    if hd == cp.name then
      return some (mkAppN orig rest)
    for oc in (← getConstInfoInduct cp.indName).ctors do
      if hd == reroot cp.indName cp.name oc then
        return some (mkAppN (mkConst oc orig.getAppFn.constLevels!) (orig.getAppArgs ++ rest))
  return none

/-- `e` with every copy, and every copy's constructor, put back as the original. -/
partial def unCopy (c : BridgeCtx) (e : Expr) : MetaM Expr :=
  Lean.Core.transform e (pre := fun e => do
    match e with
    | .app .. =>
      -- the head is read before it is rewritten: a copy's constructor is found
      -- under the copy's name, and `unCopyHead?` is what puts the original back
      let args ← e.getAppArgs.mapM c.unCopy
      if let some hd := e.getAppFn.constName? then
        if let some r ← c.unCopyHead? hd args then return .done r
      return .done (mkAppN (← c.unCopy e.getAppFn) args)
    | .const n _ => return .done ((← c.unCopyHead? n #[]).getD e)
    | _ => return .continue)

/-- Member `i`'s arity as the writer stated it, at the block's parameters. -/
def niceArity (c : BridgeCtx) (i : Nat) : MetaM Expr := do
  c.unCopy (← instantiateForall c.b.members[i]!.type c.ps)

/-- Every copy that a subterm of `e` is an application of the original of. -/
private partial def usesCopies (c : BridgeCtx) (e : Expr) (acc : Array Nat) :
    MetaM (Array Nat) := do
  let mut acc := acc
  if let some hd := e.getAppFn.constName? then
    let args := e.getAppArgs
    -- as itself, if it is one of the copied inductives applied to its parameters
    if let some (k, _) ← c.copyOf? e then
      unless acc.contains k do acc := acc.push k
    -- and as its inductive, if it is one of their constructors
    if let .ctorInfo ci ← getConstInfo hd then
      if args.size ≥ ci.numParams then
        let ind := mkAppN (mkConst ci.induct e.getAppFn.constLevels!)
          (args.extract 0 ci.numParams)
        if let some (k, _) ← c.copyOf? ind then
          unless acc.contains k do acc := acc.push k
  -- the body of a binder is entered with a real local rather than as it stands:
  -- `copyOf?` decides by unifying against the copy's parameters, and a copy of a
  -- family is at a *field*, so `Box.Never R b` has to be asked about with a `b`
  -- that unification can be shown
  match e with
  | .app f a          => c.usesCopies a (← c.usesCopies f acc)
  | .forallE n d b bi
  | .lam n d b bi     => do
    let acc' ← c.usesCopies d acc
    withLocalDecl n bi d fun x => c.usesCopies (b.instantiate1 x) acc'
  | .letE n t v b _   => do
    let acc' ← c.usesCopies v (← c.usesCopies t acc)
    withLetDecl n t v fun x => c.usesCopies (b.instantiate1 x) acc'
  | .mdata _ b        => c.usesCopies b acc
  | .proj _ _ b       => c.usesCopies b acc
  | _                 => return acc

/--
The copies, grouped and ordered so that each group comes after every copy the
group's originals mention. -/
def order (c : BridgeCtx) : MetaM (Array (Array Nat)) := do
  let n := c.copies.size
  let mut uses : Array (Array Nat) := #[]
  for cp in c.copies do
    -- a copy standing for a family is looked at with its locals opened, so that
    -- what its members mention is what any one of them mentions
    let ks ← lambdaBoundedTelescope cp.app cp.numLocals fun ls orig => do
      let lvls := orig.getAppFn.constLevels!
      let params := orig.getAppArgs
      let info ← getConstInfoInduct cp.indName
      -- a local's own type counts: the copy is indexed by it, and where that
      -- type is itself copied the index has to cross that copy's bridge before
      -- this one can be stated
      let mut ks : Array Nat := #[]
      for l in ls do ks ← c.usesCopies (← inferType l) ks
      ks ← c.usesCopies
        (← instantiateForall (info.instantiateTypeLevelParams lvls) params) ks
      for cn in info.ctors do
        let ci ← getConstInfoCtor cn
        ks ← c.usesCopies
          (← instantiateForall (ci.type.instantiateLevelParams ci.levelParams lvls) params) ks
      return ks
    uses := uses.push ks
  -- reachability, so that mutual need can be read off both ways at once
  let mut reach := uses
  let mut changed := true
  while changed do
    changed := false
    for k in *...n do
      let mut ks := reach[k]!
      for j in reach[k]! do
        for l in reach[j]! do
          unless ks.contains l do
            ks := ks.push l
            changed := true
      reach := reach.set! k ks
  let mut done : Array Nat := #[]
  let mut out : Array (Array Nat) := #[]
  while done.size < n do
    -- mutual reachability is an equivalence, so every copy in a group has the
    -- same reachable set and asking one of them is asking all of them
    let mut picked : Option (Array Nat) := none
    for k in *...n do
      if done.contains k then continue
      let grp := (Array.range n).filter fun j =>
        j == k || (reach[k]!.contains j && reach[j]!.contains k)
      if reach[k]!.all fun j => done.contains j || grp.contains j then
        picked := some grp
        break
    match picked with
    | some grp => out := out.push grp; done := done ++ grp
    | none     => throwError "The copies of this block cannot be put in any order"
  return out

/-- `X.ofOrig`'s type: the original at its indices, sent to the copy at theirs. -/
def ofType (c : BridgeCtx) (k : Nat) : MetaM Expr := do
  let cp := c.copies[k]!
  forallTelescope (← inferType cp.app) fun jdxs _ => do
    let imgs ← c.ofImages jdxs
    withLocalDeclD `x (cp.origAt jdxs) fun x =>
      return implicitPrefix (c.ps.size + jdxs.size) (←
        mkForallFVars (c.ps ++ jdxs ++ #[x]) (mkAppN (c.b.cst cp.name) (c.ps ++ imgs)))

/--
`X.ofOrig` for a data copy: a `casesOn` on the original, with the fields sent
across one by one. -/
def ofValueData (c : BridgeCtx) (k : Nat) : MetaM Expr := do
  let cp := c.copies[k]!
  let info ← getConstInfoInduct cp.indName
  forallTelescope (← inferType cp.app) fun jdxs _ => do
    -- the locals lead the copy's indices, and are parameters of the original, so
    -- they are what fixes which original this is and not what `casesOn` takes
    let orig := cp.orig jdxs
    let params := orig.getAppArgs
    let lvls := orig.getAppFn.constLevels!
    let idxs := jdxs.extract cp.numLocals jdxs.size
    let resTy := mkAppN (c.b.cst cp.name) (c.ps ++ (← c.ofImages jdxs))
    withLocalDeclD `x (mkAppN orig idxs) fun x => do
      let motive ← mkLambdaFVars (idxs ++ #[x]) resTy
      let elim ← getLevel resTy
      let mut alts : Array Expr := #[]
      for cn in info.ctors do
        let ci ← getConstInfoCtor cn
        let cty ← instantiateForall (ci.type.instantiateLevelParams ci.levelParams lvls) params
        alts := alts.push <| ← forallTelescope cty fun xs _ => do
          let fimgs ← c.ofImages xs
          mkLambdaFVars xs <|
            mkAppN (mkConst (reroot cp.indName cp.name cn) c.b.lvls)
              (c.ps ++ jdxs.extract 0 cp.numLocals ++ fimgs)
      let body := mkAppN (mkConst (mkCasesOnName cp.indName) (elim :: lvls))
        (params ++ #[motive] ++ idxs ++ #[x] ++ alts)
      return implicitPrefix (c.ps.size + jdxs.size) (← mkLambdaFVars (c.ps ++ jdxs ++ #[x]) body)

/-- What one minor premise of a recursor is about. -/
structure MinorPlan where
  /-- The motive the minor concludes at. -/
  motive : Nat
  /-- The constructor it concludes with. -/
  ctor : Name
  /-- How many fields that constructor takes. -/
  numFields : Nat
  /-- For each field, the hypothesis the recursor supplies about it, if there is
  one, as its position among the minor's arguments and the motive it is for. -/
  ihs : Array (Option (Nat × Nat))
  deriving Inhabited

/--
What each minor premise of `recTy`, a recursor's type at its parameters, is
about. -/
def recPlan (recInfo : RecursorVal) (recTy : Expr) : MetaM (Array MinorPlan) :=
  forallBoundedTelescope recTy recInfo.numMotives fun ms rest =>
    forallBoundedTelescope rest recInfo.numMinors fun mins _ => do
      let mut out : Array MinorPlan := #[]
      for mi in mins do
        out := out.push <| ← forallTelescope (← inferType mi) fun args concl => do
          let some cn := concl.getAppArgs.back?.bind (·.getAppFn.constName?)
            | throwError "the recursor's minor premise does not conclude at a constructor"
          let nf := (← getConstInfoCtor cn).numFields
          let fields := args.extract 0 nf
          let ihs := args.extract nf args.size
          let mut fplan : Array (Option (Nat × Nat)) := Array.replicate nf none
          for j in *...ihs.size do
            let hit? ← forallTelescope (← inferType ihs[j]!) fun _ ihConcl => do
              let some mq := ms.findIdx? (· == ihConcl.getAppFn) | return none
              let some major := ihConcl.getAppArgs.back? | return none
              let some z := fields.findIdx? (major.containsFVar ·.fvarId!) | return none
              return some (z, j, mq)
            if let some (z, j, mq) := hit? then fplan := fplan.set! z (some (j, mq))
          return { motive := (ms.findIdx? (· == concl.getAppFn)).getD 0
                   ctor := cn, numFields := nf, ihs := fplan }
      return out

/--
An original's own recursor, set up to prove something of a whole group of copies
at once. -/
structure GroupElim where
  /-- The recursor. -/
  recInfo : RecursorVal
  /-- Its levels: the original's, with the motives' in front where it takes one. -/
  recLvls : List Level
  /-- Its type, at the original's parameters. -/
  recTy : Expr
  /-- What each of its minor premises is about. -/
  plan : Array MinorPlan
  /-- The motives, one per member the recursor eliminates. -/
  motives : Array Expr
  /-- Which copy each motive is for, where it is one the group is proving. -/
  targets : Array (Option Nat)

/--
Set the recursor of `cp`'s original, at `params` and `lvls`, up to eliminate all
of `grp` at once. -/
def groupElim (c : BridgeCtx) (grp : Array Nat) (cp : Copy) (params : Array Expr)
    (lvls : List Level) (motive : Nat → Array Expr → Expr → MetaM Expr) :
    MetaM GroupElim := do
  let recInfo ← getConstInfoRec (mkRecName cp.indName)
  -- every motive here lands in `Prop` -- a copy of a proposition is a
  -- proposition, and an equation is one too -- so where the recursor takes a
  -- level of its own it is given zero
  let recLvls := if recInfo.levelParams.length == (← getConstInfoInduct cp.indName).levelParams.length
    then lvls else .zero :: lvls
  let recTy ← instantiateForall
    (recInfo.type.instantiateLevelParams recInfo.levelParams recLvls) params
  let plan ← recPlan recInfo recTy
  let (motives, targets) ← forallBoundedTelescope recTy recInfo.numMotives fun ms _ => do
    let mut motives : Array Expr := #[]
    let mut targets : Array (Option Nat) := #[]
    for m in ms do
      let (mot, tgt) ← forallTelescope (← inferType m) fun ys _ => do
        let trivial := (← mkLambdaFVars ys (mkConst ``True), none)
        let some major := ys.back? | return trivial
        let some (k', jdxs') ← c.copyOf? (← inferType major) | return trivial
        unless grp.contains k' do return trivial
        return (← mkLambdaFVars ys (← motive k' jdxs' major), some k')
      motives := motives.push mot
      targets := targets.push tgt
    return (motives, targets)
  return { recInfo, recLvls, recTy, plan, motives, targets }

/--
The minor premises: `body` at each one about a copy in the group, `trivial` at
each one that is not. -/
def GroupElim.minors (ge : GroupElim)
    (body : Nat → MinorPlan → Array Expr → Expr → MetaM Expr) : MetaM (Array Expr) := do
  forallBoundedTelescope (← instantiateForall ge.recTy ge.motives) ge.recInfo.numMinors
    fun mins _ => do
      let mut out : Array Expr := #[]
      for q in *...mins.size do
        let mp := ge.plan[q]!
        out := out.push <| ← forallTelescope (← inferType mins[q]!) fun args concl => do
          let some k' := ge.targets[mp.motive]! | mkLambdaFVars args (mkConst ``True.intro)
          mkLambdaFVars args (← body k' mp args concl)
      return out

/-- The recursor applied to everything: `params`, the motives, `minors`, and a major premise. -/
def GroupElim.app (ge : GroupElim) (params minors idxs : Array Expr) (x : Expr) : Expr :=
  mkAppN (mkConst ge.recInfo.name ge.recLvls) (params ++ ge.motives ++ minors ++ idxs ++ #[x])

/-- `X.ofOrig` for a `Prop` copy: one application of the original's own recursor. -/
def ofValueProp (c : BridgeCtx) (grp : Array Nat) (k : Nat) : MetaM Expr := do
  let cp := c.copies[k]!
  -- a copy standing for a family recurses one member at a time, so the whole
  -- recursor application is built under the locals that say which member it is
  forallTelescope (← inferType cp.app) fun jdxs _ => do
  let orig := cp.orig jdxs
  let params := orig.getAppArgs
  let idxs := jdxs.extract cp.numLocals jdxs.size
  let ge ← c.groupElim grp cp params orig.getAppFn.constLevels! fun k' jdxs' _ => do
    return mkAppN (c.b.cst c.copies[k']!.name) (c.ps ++ (← c.ofImages jdxs'))
  let minors ← ge.minors fun k' mp args concl => do
    let cp' := c.copies[k']!
    -- the minor concludes at the motive, which is the copy at its own
    -- arguments, so the locals this constructor is built at are read off it
    let cargs := concl.headBeta.getAppArgs
    unless cargs.size ≥ c.ps.size + cp'.numLocals do
      throwError "the recursor's minor premise does not conclude at the copy"
    let ls := cargs.extract c.ps.size (c.ps.size + cp'.numLocals)
    let ihs := args.extract mp.numFields args.size
    let mut fimgs : Array Expr := #[]
    for z in *...mp.numFields do
      if let some (j, mq') := mp.ihs[z]! then
        if ge.targets[mq']!.isSome then
          fimgs := fimgs.push ihs[j]!
          continue
      fimgs := fimgs.push (← c.ofImage args[z]! (← inferType args[z]!))
    return mkAppN (mkConst (reroot cp'.indName cp'.name mp.ctor) c.b.lvls) (c.ps ++ ls ++ fimgs)
  withLocalDeclD `x (mkAppN orig idxs) fun x => do
    return implicitPrefix (c.ps.size + jdxs.size)
      (← mkLambdaFVars (c.ps ++ jdxs ++ #[x]) (ge.app params minors idxs x))

/-- Add `X.ofOrig` for every copy, each group after the ones its own bodies call. -/
def addOfOrig (c : BridgeCtx) (docCtx : LocalContext × LocalInstances) : TermElabM Unit := do
  for grp in ← c.order do
    let isProp (k : Nat) : Bool := c.b.members[c.copies[k]!.idx]!.isProp
    if grp.all isProp then
      for k in grp do
        let cp := c.copies[k]!
        addDecl (.thmDecl { name := cp.ofName, levelParams := c.b.us
                            type := ← instantiateMVars (← c.ofType k)
                            value := ← instantiateMVars (← c.ofValueProp grp k) })
    else if grp.any isProp then
      throwError "The types denesting copies are nested in one another, and only some \
        of them are propositions"
    else
      let names := grp.map (c.copies[·]!.ofName)
      let preDefs ← grp.mapM fun k => do
        return { ref := .missing, kind := .def, levelParams := c.b.us, modifiers := {},
                 declName := c.copies[k]!.ofName, binders := .missing,
                 type := ← instantiateMVars (← c.ofType k),
                 value := ← instantiateMVars (← c.ofValueData k),
                 termination := TerminationHints.none : PreDefinition }
      -- a group of two is mutually recursive by construction, but a group of one
      -- need not recurse at all -- a copy of a type that nests nothing --  and
      -- `structuralRecursion` has no argument to recurse on then
      if preDefs.any fun d => d.value.getUsedConstants.any names.contains then
        Structural.structuralRecursion docCtx preDefs (Array.replicate grp.size none)
      else
        for d in preDefs do addAndCompileNonRec docCtx d

/-- Give every renamed member the arity it was declared with. -/
def niceMembers (c : BridgeCtx) (rawOf : Name → Name) : TermElabM Unit := do
  for i in *...c.b.size do
    let m := c.b.members[i]!
    let raw := rawOf m.name
    if raw == m.name then continue
    let body ← c.niceArity i
    let type ← mkForallFVars c.ps body
    let value ← forallTelescope body fun xs _ => do
      mkLambdaFVars (c.ps ++ xs) (mkAppN (mkConst raw c.b.lvls) (c.ps ++ (← c.ofImages xs)))
    addDef m.name c.b.us (← instantiateMVars type) (← instantiateMVars value)
      (compile := false)

/-- Give every renamed constructor the type it was declared with. -/
def niceCtors (c : BridgeCtx) (rawOf : Name → Name) : TermElabM Unit := do
  for i in *...c.b.size do
    let m := c.b.members[i]!
    for ctor in m.ctors do
      let raw := rawOf ctor.name
      if raw == ctor.name then continue
      let niceBody ← c.unCopy (← instantiateForall ctor.type c.ps)
      let type := implicitPrefix c.ps.size (← mkForallFVars c.ps niceBody)
      let inner ← forallTelescope niceBody fun xs _ => do
        mkLambdaFVars xs (mkAppN (mkConst raw c.b.lvls) (c.ps ++ (← c.ofImages xs)))
      let value := implicitPrefix c.ps.size (← mkLambdaFVars c.ps inner)
      let type ← instantiateMVars type
      let value ← instantiateMVars value
      if m.isProp then
        addDecl (.thmDecl { name := ctor.name, levelParams := c.b.us, type, value })
      else
        addDef ctor.name c.b.us type value

end BridgeCtx

/-! ### The way back, and the recursor stated over the originals

`ofOrig` gives the constructors their written types, but a recursor travels the
other way: a minor is handed a term of the *copy* and must produce one of the
original for the writer's motive.  So the isomorphism is completed.

* `X.toOrig` sends the copy to the original.  A data copy's is one application of
  the copy's own recursor, with the members it is not eliminating given `PUnit`.
  A `Prop` copy's cannot be, the copy being defined as its pre-form at the
  underlying values, so a proof in hand says nothing about the well-formedness
  the original's statement needs.  It goes through the pre-form's recursor with
  the well-formedness proofs taken last, and `X.toOrig` supplies them from the
  index it was given.

* `X.ofOrig_toOrig` is the round trip at the underlying pre-world value, needed
  where a minor for a constructor the writer declared produces the raw
  constructor at the round-tripped fields and must produce it at the fields
  themselves.  Stating it at the subtype would make that transport ill-typed; at
  the value there are no proof fields, and the wrapper's `ext` lifts it.
-/

/-- The copy's image in the original: `X.toOrig : X ps idxs → I ps' idxs'`. -/
def Copy.toName (c : Copy) : Name := c.name ++ `toOrig

/-- The pre-world stepping stone a `Prop` copy's `toOrig` goes through. -/
def Copy.preToName (c : Copy) : Name := c.name ++ `toOrigPre

/-- `(X.ofOrig (X.toOrig x)).val = x.val`. -/
def Copy.roundName (c : Copy) : Name := c.name ++ `ofOrig_toOrig

/-- `X.toOrig (X.ofOrig x) = x`, the round trip taken the other way. -/
def Copy.backName (c : Copy) : Name := c.name ++ `toOrig_ofOrig

/-- `X.ofOrig a = X.ofOrig b → a = b`. -/
def Copy.ofInjName (c : Copy) : Name := c.name ++ `ofOrig_inj

/-- How many of the original's arguments are parameters. -/
def Copy.numOrigParams (c : Copy) : Nat := (peelLams c.numLocals c.app).getAppNumArgs

/--
The original's constructor that `n`, a constructor of the copy, is a copy of,
applied to `vals`, the copy's constructor's own arguments. -/
def Copy.origCtor (c : Copy) (n : Name) (vals : Array Expr) : Expr :=
  let orig := c.orig vals
  mkAppN (mkConst (reroot c.name c.indName n) orig.getAppFn.constLevels!)
    (orig.getAppArgs ++ vals.extract c.numLocals vals.size)

namespace BridgeCtx

/-- Which copy the block's member `i` is, if it is one. -/
def copyAt? (c : BridgeCtx) (i : Nat) : Option Nat :=
  c.copies.findIdx? (·.idx == i)

/-- Where the data member `i` sits among the motives. -/
def dpos (c : BridgeCtx) (i : Nat) : Nat := (c.b.dataIdxs.findIdx? (· == i)).getD 0

/--
The type of the major premise of member `i`'s recursion, as the writer wrote it.
A copy stands for an original, so the recursion over it is over that original. -/
def majorType (c : BridgeCtx) (i : Nat) (idxs : Array Expr) : Expr :=
  match c.copyAt? i with
  | some k => c.copies[k]!.origAt idxs
  | none   => mkAppN (c.b.cst c.b.members[i]!.name) (c.ps ++ idxs)

/-- The name of anything the denesting made up, if `ty` mentions one. -/
def leaked? (c : BridgeCtx) (ty : Expr) : Option Name :=
  let b := c.b
  ty.getUsedConstants.find? fun n =>
    (!c.copyRecs.contains n && c.copies.any (fun cp => cp.name.isPrefixOf n))
      || b.members.any fun m =>
           (m.name != n && b.rawMember m.name == n)
             || m.ctors.any fun cc => cc.name != n && b.rawCtor cc.name == n

/--
The motive arguments of a member's type: a copy's are the *original's*. `app` is
the member applied, in the original world for a copy. -/
def niceIdxArgs (c : BridgeCtx) (i : Nat) (app : Expr) : MetaM (Array Expr) := do
  match c.copyAt? i with
  | none   => return c.b.idxArgs app.getAppArgs
  | some k =>
    let cp := c.copies[k]!
    let some args ← cp.argsOf? app
      | throwError "`{cp.name}` stands for a family of originals, and{indentExpr app} is not \
          one of them"
    return args

/-- `X._sub.ext` at `ty`, a member of the block applied to its arguments. -/
def subtypeExt (_c : BridgeCtx) (_i : Nat) (ty a a' h : Expr) : MetaM Expr := do
  let sub ← whnfD ty
  let some (n, us, args) := subOf? sub
    | throwError "`{ty}` is not the wrapper the member unfolds to"
  return mkAppN (mkConst (n ++ `ext) us) (args ++ #[a, a', h])

/--
The original-world image of `x : ty`, where `ty` is written in the copy world;
the mirror of `BridgeCtx.ofImage`. -/
partial def toImage (c : BridgeCtx) (x ty : Expr) : MetaM Expr :=
  forallTelescope ty fun ys concl => do
    let some hd := concl.getAppFn.constName? | return x
    if let some k := c.copies.findIdx? (·.name == hd) then
      return ← mkLambdaFVars ys <|
        mkAppN (mkConst c.copies[k]!.toName c.b.lvls)
          (c.ps ++ c.b.idxArgs concl.getAppArgs ++ #[mkAppN x ys])
    -- a proof of a member the bridge restates: what the writer wrote is the raw
    -- member at the round trips of the indices, so the proof is carried onto
    -- them, one index at a time, each read at the ones already moved
    let some m := c.b.members.findIdx? fun mm =>
        mm.name != hd && c.b.rawMember mm.name == hd
      | return x
    let idxs := c.b.idxArgs concl.getAppArgs
    let mut cur := idxs
    let mut proof := mkAppN x ys
    for z in *...idxs.size do
      let ity ← inferType idxs[z]!
      let some ihd := ity.getAppFn.constName? | continue
      let some k := c.copies.findIdx? (·.name == ihd) | continue
      let cp := c.copies[k]!
      let img ← c.toImage idxs[z]! ity
      let rt := (← c.ofImage img (← inferType img)).headBeta
      let eq ← c.subtypeExt cp.idx ity rt idxs[z]! <|
        mkAppN (mkConst cp.roundName c.b.lvls)
          (c.ps ++ c.b.idxArgs ity.getAppArgs ++ #[idxs[z]!])
      let motive ← withLocalDeclD `w ity fun w =>
        mkLambdaFVars #[w] (mkAppN (c.b.memberCst m) (c.ps ++ cur.set! z w))
      proof ← mkEqNDRec motive proof (← mkEqSymm eq)
      cur := cur.set! z rt
    mkLambdaFVars ys proof

/-- The original-world images of a whole telescope, each read at its own type. -/
def toImages (c : BridgeCtx) (xs : Array Expr) : MetaM (Array Expr) :=
  xs.mapM fun x => do c.toImage x (← inferType x)

/-- `X.toOrig`'s type: the copy at its indices, sent to the original at theirs. -/
def toType (c : BridgeCtx) (k : Nat) : MetaM Expr := do
  let cp := c.copies[k]!
  forallTelescope (← instantiateForall c.b.members[cp.idx]!.type c.ps) fun idxs _ => do
    let jdxs ← c.toImages idxs
    withLocalDeclD `x (mkAppN (c.b.cst cp.name) (c.ps ++ idxs)) fun x =>
      return implicitPrefix (c.ps.size + idxs.size) (←
        mkForallFVars (c.ps ++ idxs ++ #[x]) (cp.origAt jdxs))

/--
Build one minor per constructor of every data member, reading the binders off
the raw recursor's own type rather than reconstructing them. -/
def withRawMinors (c : BridgeCtx) (recCst : Expr) (motives : Array Expr)
    (mk : Nat → CtorSpec → Array Expr → Array Expr → Expr → TermElabM Expr) :
    TermElabM (Array Expr) := do
  let b := c.b
  let dIdxs := b.dataIdxs
  let recTy ← instantiateForall (← inferType recCst) (c.ps ++ motives)
  let mut n := 0
  for i in dIdxs do
    n := n + b.members[i]!.ctors.size
  forallBoundedTelescope recTy n fun ms _ => do
    let mut out : Array Expr := #[]
    let mut q := 0
    for i in dIdxs do
      for cc in b.members[i]!.ctors do
        let kinds := b.fieldKinds cc.kinds
        let nf := kinds.size
        out := out.push <| ←
          forallBoundedTelescope (← inferType ms[q]!) (nf + (b.ihPositions kinds).size)
            fun args concl => do
              mkLambdaFVars args
                (← mk i cc (args.extract 0 nf) (args.extract nf args.size) concl)
        q := q + 1
    return out

/-- `X.toOrig` for a data copy: one application of the copy's own recursor. -/
def toValueData (c : BridgeCtx) (grp : Array Nat) (k : Nat) (rawRec : Nat → Name) :
    TermElabM Expr := do
  let b := c.b
  let cp := c.copies[k]!
  -- the copy of member `i`, when there is one and it is one of ours
  let mine? (i : Nat) : Option Nat := do
    let j ← c.copyAt? i
    guard (grp.contains j)
    return j
  forallTelescope (← instantiateForall b.members[cp.idx]!.type c.ps) fun idxs _ => do
    let jdxs ← c.toImages idxs
    let elim ← getLevel (cp.origAt jdxs)
    withLocalDeclD `x (mkAppN (b.cst cp.name) (c.ps ++ idxs)) fun x => do
      let motives ← b.dataIdxs.mapM fun i => do
        forallTelescope (← instantiateForall b.members[i]!.type c.ps) fun ids _ =>
          withLocalDeclD `t (mkAppN (b.cst b.members[i]!.name) (c.ps ++ ids)) fun t => do
            let body ← match mine? i with
              | some j => pure (c.copies[j]!.origAt (← c.toImages ids))
              | none => pure (mkConst ``PUnit [elim])
            mkLambdaFVars (ids ++ #[t]) body
      let recCst := mkConst (rawRec cp.idx) (elim :: b.lvls)
      let minors ← c.withRawMinors recCst motives fun i cc xs ihs _ => do
        let some j := mine? i | return mkConst ``PUnit.unit [elim]
        let kinds := b.fieldKinds cc.kinds
        let mut vals : Array Expr := #[]
        let mut nih := 0
        for z in *...xs.size do
          match kinds[z]! with
          | .recur m =>
            if (mine? m).isSome then vals := vals.push ihs[nih]!
            else vals := vals.push (← c.toImage xs[z]! (← inferType xs[z]!))
          | .plain  => vals := vals.push xs[z]!
          | .erased => vals := vals.push (← c.toImage xs[z]! (← inferType xs[z]!))
          -- a copy carries the constructor-locals its parameters mention as
          -- leading fields, and when one of those is a member of the block the
          -- erasure calls it a deleted index
          | .deleted .. => vals := vals.push xs[z]!
          -- a deleted field arrives with a hypothesis of its own, so the count
          -- has to step over it even though nothing here reads it
          if b.hasIh kinds[z]! then nih := nih + 1
        return c.copies[j]!.origCtor cc.name vals
      return implicitPrefix (c.ps.size + idxs.size) (← mkLambdaFVars (c.ps ++ idxs ++ #[x])
        (mkAppN recCst (c.ps ++ motives ++ minors ++ idxs ++ #[x])))

/--
Walk a `Prop` member's indices in the pre-world, collecting the well-formedness
proofs that turn them back into real ones. -/
partial def withWfIdxsAux {α} [Inhabited α] (c : BridgeCtx) (idxs : Array Expr) (i : Nat)
    (preTy : Expr) (pres ws : Array Expr) (reals : Array (Expr × Expr))
    (k : Array Expr → Array Expr → Array (Expr × Expr) → TermElabM α) : TermElabM α := do
  if h : i < idxs.size then
    forallBoundedTelescope preTy (some 1) fun ys rest => do
      let y := ys[0]!
      -- the copy-world type the index was declared with, kept alongside the
      -- term: a rebuilt index is the wrapper's `.mk`, and what that infers to
      -- names the wrapper rather than the copy, which is what the image is
      -- looked up by
      let raw ← inferType idxs[i]
      let ty := raw.replaceFVars (idxs.extract 0 i) (reals.map (·.1))
      -- and the same type read the way `Block.subTy` reads a field: the
      -- member's real head over pre-world arguments
      let sub ← c.b.subTy (idxs.extract 0 i) pres raw
      let isData ← c.b.withRecTarget? ty fun _ m _ => pure (!c.b.members[m]!.isProp)
      if isData == some true then
        withLocalDeclD `w (← c.b.wfOfSub y sub) fun w => do
          let real ← c.b.withRecTarget sub fun zs mm args =>
            mkLambdaFVars zs (c.b.sMk mm args (mkAppN y zs) (mkAppN w zs))
          c.withWfIdxsAux idxs (i + 1) rest (pres.push y) (ws.push w)
            (reals.push (real, ty)) k
      else
        c.withWfIdxsAux idxs (i + 1) rest (pres.push y) ws (reals.push (y, ty)) k
  else
    k pres ws reals

@[inherit_doc withWfIdxsAux]
def withWfIdxs {α} [Inhabited α] (c : BridgeCtx) (j : Nat)
    (k : Array Expr → Array Expr → Array (Expr × Expr) → TermElabM α) : TermElabM α := do
  let m := c.b.members[j]!
  let preTy ← instantiateForall (← inferType (c.b.cst (preName m.name))) c.ps
  forallTelescope (← instantiateForall m.type c.ps) fun idxs _ =>
    c.withWfIdxsAux idxs 0 preTy #[] #[] #[] k

/--
Every well-formedness fact a proof of a `_wf` conjunction yields, with the proof
of each. -/
partial def wfParts (w : Expr) : MetaM (Array (Expr × Expr)) := do
  let ty ← whnf (← inferType w)
  let mut out := #[(ty, w)]
  if ty.isAppOfArity ``And 2 then
    let l := ty.appFn!.appArg!
    let r := ty.appArg!
    out := out ++ (← wfParts (mkApp3 (mkConst ``And.left) l r w))
    out := out ++ (← wfParts (mkApp3 (mkConst ``And.right) l r w))
  return out

/-- What both restatements of a raw `Prop` minor premise open with, handed to `k`. -/
def withRawPropMinor {α} (b : Block) (cc : CtorSpec) (ps : Array Expr)
    (kinds : Array FieldKind) (args : Array Expr) (concl : Expr)
    (k : Array Expr → Array Expr → Array Expr → Array (Expr × Expr) → Array Expr →
      TermElabM α) : TermElabM α := do
  let xs := args.extract 0 kinds.size
  let ihs := args.extract kinds.size args.size
  let subTys ← b.subFieldTys cc ps xs
  forallTelescope (← whnf concl) fun ws _ => do
    let mut parts : Array (Expr × Expr) := #[]
    for w in ws do
      parts := parts ++ (← wfParts w)
    k xs ihs subTys parts ws

/-- Every wrapper's `property` the statement `want` puts within reach. -/
partial def subProps (e : Expr) (acc : Array Expr) : Array Expr :=
  match e with
  -- the whole spine at once, since `.val` and `.property` take the same
  -- arguments and a walk down `.app` would collect every partial application of
  -- one of them as well as the application that was really there
  | .app .. =>
    let args := e.getAppArgs
    let acc := match e.getAppFn with
      | .const (.str p@(.str _ "_sub") "val") us =>
        acc.push (mkAppN (mkConst (.str p "property") us) args)
      | _ => acc
    args.foldl (fun acc a => subProps a acc) acc
  | .lam _ d b _ | .forallE _ d b _ => subProps b (subProps d acc)
  | .letE _ t v b _ => subProps b (subProps v (subProps t acc))
  | .mdata _ b => subProps b acc
  | .proj _ _ b => subProps b acc
  | _ => acc

/-- The proof among `parts` of the statement `want`, or one assembled out of them. -/
partial def findPart (parts : Array (Expr × Expr)) (want : Expr) : MetaM Expr := do
  let bad : MetaM Expr := throwError "No well-formedness proof to hand for{indentExpr want}"
  for (ty, pf) in parts do
    if ← isDefEq ty want then return pf
  -- what an infinitary field contributes is quantified: at `f : Nat → T` the
  -- conjunct is that *every* `f n` is well formed, and what is wanted is the one
  -- at the `n` in hand
  for (ty, pf) in parts do
    unless ty.isForall do continue
    let (xs, _, body) ← forallMetaTelescope ty
    if ← isDefEqGuarded body want then
      return ← instantiateMVars (mkAppN pf xs)
  -- a real value in the statement carries the fact about itself, which is no
  -- part of anything the caller was handed
  for pf in subProps want #[] do
    if ← isDefEqGuarded (← inferType pf) want then return pf
  -- unfolding strips one pre-constructor off the term the fact is about, so a
  -- descent stops of its own accord; what it stops at is either a fact the
  -- caller holds or one nothing could supply, and the second is reported
  -- against the statement that was asked for rather than the unfolded one
  match ← whnf want with
  | .app (.app (.const ``And _) l) r =>
    try return mkApp4 (mkConst ``And.intro) l r (← findPart parts l) (← findPart parts r)
    catch _ => bad
  | e => if e.isConstOf ``True then return mkConst ``True.intro else bad

/-- A raw induction hypothesis, at the well-formedness proofs in hand. -/
def atParts (parts : Array (Expr × Expr)) (ih fieldTy : Expr) : MetaM Expr := do
  let nzs ← forallTelescope fieldTy fun zs _ => pure zs.size
  forallBoundedTelescope (← inferType ih) nzs fun zs rest => do
    forallTelescope (← whnf rest) fun ws _ => do
      let mut fnd : Array Expr := #[]
      for w in ws do
        fnd := fnd.push (← findPart parts (← inferType w))
      mkLambdaFVars zs (mkAppN ih (zs ++ fnd))

/-- Some element of a field's type, if a constructor can be applied to make one. -/
partial def someElem? (b : Block) (ty : Expr) (fuel : Nat) : MetaM (Option Expr) := do
  if let .some inst ← trySynthInstance (← mkAppM ``Inhabited #[ty]) then
    return some (← mkAppOptM ``Inhabited.default #[ty, inst])
  if fuel == 0 then return none
  forallTelescope ty fun ys concl => do
    let .const n _ := concl.getAppFn | return none
    let some i := b.memberIdx? n | return none
    let args := concl.getAppArgs
    if args.size < b.numParams then return none
    for cc in b.members[i]!.ctors do
      unless (← getEnv).contains cc.name do continue
      -- the parameters are the ones the field's own type is at; only the fields
      -- after them are looked for, and a later one's type may name an earlier
      let mut ty ← instantiateForall cc.type (args.extract 0 b.numParams)
      let mut vals := args.extract 0 b.numParams
      let mut ok := true
      repeat
        let .forallE _ d body _ := ← whnf ty | break
        let some a ← someElem? b d (fuel - 1) | ok := false; break
        vals := vals.push a
        ty := body.instantiate1 a
      -- an indexed family is inhabited at some indices and not others, so what
      -- the constructor happens to conclude at has to be the index in hand
      if ok && (← isDefEq ty concl) then
        return some (← mkLambdaFVars ys (mkAppN (b.cst cc.name) vals))
    return none

/--
Put back a data field of a `Prop` constructor at its subtype, or say why there
is none to put back. -/
def dataFieldPart (b : Block) (cc : CtorSpec) (parts : Array (Expr × Expr))
    (x subTy : Expr) : MetaM Expr := do
  let want ← b.wfOfSub x subTy
  try
    findPart parts want
  catch _ =>
    -- the inversion's fields carry macro scopes; what to name is what the writer did
    let fld := (← x.fvarId!.getUserName).eraseMacroScopes
    throwError "`{cc.name}` has a field `{fld}` whose type is a data member of the \
      block, and its conclusion does not say that `{fld}` is well formed.  A `Prop` \
      constructor carries no well-formedness of its own -- only what its indices \
      bring -- so there is nothing to state the recursor's minor premise with."

/-- A data field of a `Prop` constructor, put back at its subtype. -/
def rebuiltField (b : Block) (cc : CtorSpec) (parts : Array (Expr × Expr))
    (x subTy : Expr) (strayOk := false) : MetaM Expr := do
  let rebuild (pf : Expr) : MetaM Expr :=
    b.withRecTarget subTy fun zs mm args =>
      mkLambdaFVars zs (b.sMk mm args (mkAppN x zs) (mkAppN pf zs))
  if strayOk then
    if let some pf ← observing? (dataFieldPart b cc parts x subTy) then
      return ← rebuild pf
    if let some e ← someElem? b subTy 4 then
      return e
  rebuild (← dataFieldPart b cc parts x subTy)

/-- Which of a `Prop` constructor's fields nothing else in the constructor mentions. -/
def strayFields (b : Block) (i : Nat) (c : CtorSpec) (ps : Array Expr) :
    MetaM (Array Nat) := do
  unless b.members[i]!.isProp do return #[]
  let kinds := b.fieldKinds c.kinds
  forallTelescope (← b.ctorType c ps) fun xs concl => do
    let mut out : Array Nat := #[]
    for z in *...kinds.size do
      let .recur mm := kinds[z]! | continue
      -- a proof field is never put back at a subtype, so it is never in question
      if b.members[mm]!.isProp then continue
      let fv := xs[z]!.fvarId!
      if concl.hasAnyFVar (· == fv) then continue
      if ← xs.anyM fun y => return (← inferType y).hasAnyFVar (· == fv) then continue
      out := out.push z
    return out

/-- `X.toOrigPre` and `X.toOrig` for a `Prop` copy. -/
def addToOrigProp (c : BridgeCtx) (k : Nat) : TermElabM Unit := do
  let b := c.b
  let cp := c.copies[k]!
  let recInfo ← getConstInfoRec (mkRecName (preName cp.name))
  -- the motives and minors of a mutual recursor run over the block in its own
  -- order, every constructor of every member; `rules` holds only the ones for
  -- the type the recursor belongs to, so the order is read off `all` instead
  let pIdxs ← b.propsBehind recInfo
  -- which of the motives came out real, so that the minors agree with them
  let mut realMot : Array Bool := #[]
  let mut motives : Array Expr := #[]
  for j in pIdxs do
    let (mot, real) ← c.withWfIdxs j fun pres ws reals =>
      withLocalDeclD `h (mkAppN (b.cst (preName b.members[j]!.name)) (c.ps ++ pres)) fun h => do
        let some kj := c.copyAt? j
          | return (← mkLambdaFVars (pres ++ #[h]) (mkConst ``True), false)
        let mut js : Array Expr := #[]
        for (r, ty) in reals do
          js := js.push (← c.toImage r ty)
        let body ← mkForallFVars ws (c.copies[kj]!.origAt js)
        -- `toOrig` is added one copy at a time, and a sibling whose own index
        -- has not been sent across yet has nothing to state its real motive
        -- with
        let env ← getEnv
        if body.getUsedConstants.all env.contains then
          return (← mkLambdaFVars (pres ++ #[h]) body, true)
        return (← mkLambdaFVars (pres ++ #[h]) (mkConst ``True), false)
    motives := motives.push mot
    realMot := realMot.push real
  let recLvls := if recInfo.levelParams.length == b.us.length then b.lvls else Level.zero :: b.lvls
  let recTy ← instantiateForall
    (recInfo.type.instantiateLevelParams recInfo.levelParams recLvls) (c.ps ++ motives)
  let minors ← forallBoundedTelescope recTy recInfo.numMinors fun ms _ => do
    let order := b.ctorsOf pIdxs
    let mut out : Array Expr := #[]
    for q in *...ms.size do
      let (j, cc) := order[q]!
      let kinds := b.fieldKinds cc.kinds
      let ihPos := (recPositions kinds).filter fun z =>
        match kinds[z]! with
        | .recur m => b.members[m]!.isProp
        | _        => false
      out := out.push <| ←
        forallBoundedTelescope (← inferType ms[q]!) (kinds.size + ihPos.size) fun args concl => do
          let some kj := c.copyAt? j
            | return ← mkLambdaFVars args (mkConst ``True.intro)
          unless realMot[(pIdxs.findIdx? (· == j)).getD 0]! do
            return ← mkLambdaFVars args (mkConst ``True.intro)
          let cpj := c.copies[kj]!
          withRawPropMinor b cc c.ps kinds args concl fun xs ihs subTys parts ws => do
            let mut vals : Array Expr := #[]
            let mut nih := 0
            for z in *...xs.size do
              let ty ← inferType xs[z]!
              match kinds[z]! with
              | .plain  => vals := vals.push xs[z]!
              | .erased => vals := vals.push xs[z]!
              | .deleted .. => throwError "A `Prop` member deleted an index"
              | .recur m =>
                if !b.members[m]!.isProp then
                  -- a data field, rebuilt at the subtype from the proof in
                  -- hand, and then sent across
                  unless b.members[m]!.dropped.isEmpty do
                    throwError "A deleted index reached the denesting bridge"
                  -- the bridge is a theorem, so a stray field may be stood in for
                  let real ← rebuiltField b cc parts xs[z]! subTys[z]! (strayOk := true)
                  let realTy ← b.withRecTarget subTys[z]! fun zs mm args =>
                    mkForallFVars zs (mkAppN (b.memberCst mm) args)
                  vals := vals.push (← c.toImage real realTy)
                else if (c.copyAt? m).isSome then
                  -- the hypothesis for this field, at its own indices' proofs
                  vals := vals.push (← atParts parts ihs[nih]! ty)
                  nih := nih + 1
                else
                  -- a `Prop` member the writer declared: the proof is the proof
                  nih := nih + 1
                  vals := vals.push xs[z]!
            mkLambdaFVars (args ++ ws) (cpj.origCtor cc.name vals)
    return out
  let preType ← c.withWfIdxs cp.idx fun pres ws reals =>
    withLocalDeclD `h (mkAppN (b.cst (preName cp.name)) (c.ps ++ pres)) fun h => do
      let mut js : Array Expr := #[]
      for (r, ty) in reals do
        js := js.push (← c.toImage r ty)
      return implicitPrefix c.ps.size (←
        mkForallFVars (c.ps ++ pres ++ #[h] ++ ws) (cp.origAt js))
  let preValue ← c.withWfIdxs cp.idx fun pres ws _ =>
    withLocalDeclD `h (mkAppN (b.cst (preName cp.name)) (c.ps ++ pres)) fun h =>
      return implicitPrefix c.ps.size (← mkLambdaFVars (c.ps ++ pres ++ #[h] ++ ws)
        (mkAppN (mkConst recInfo.name recLvls)
          (c.ps ++ motives ++ minors ++ pres ++ #[h] ++ ws)))
  addDecl (.thmDecl { name := cp.preToName, levelParams := b.us
                      type := ← instantiateMVars preType
                      value := ← instantiateMVars preValue })
  let value ← forallTelescope (← instantiateForall b.members[cp.idx]!.type c.ps) fun idxs _ =>
    withLocalDeclD `x (mkAppN (b.cst cp.name) (c.ps ++ idxs)) fun x => do
      let (pres, wps) ← b.preAndWf idxs
      return implicitPrefix (c.ps.size + idxs.size) (← mkLambdaFVars (c.ps ++ idxs ++ #[x])
        (mkAppN (mkConst cp.preToName b.lvls) (c.ps ++ pres ++ #[x] ++ wps)))
  addDecl (.thmDecl { name := cp.toName, levelParams := b.us
                      type := ← instantiateMVars (← c.toType k)
                      value := ← instantiateMVars value })

/-- Add `X.toOrig` for every copy, each after the ones its own body calls. -/
def addToOrig (c : BridgeCtx) (rawRec : Nat → Name) : TermElabM Unit := do
  for grp in ← c.order do
    for k in grp do
      let cp := c.copies[k]!
      if c.b.members[cp.idx]!.isProp then
        c.addToOrigProp k
      else
        addDef cp.toName c.b.us (← instantiateMVars (← c.toType k))
          (← instantiateMVars (← c.toValueData grp k rawRec))

/-- `funext` applied `n` times, to a hypothesis that is pointwise an equation. -/
partial def funExtN (h : Expr) (n : Nat) : MetaM Expr := do
  if n == 0 then return h
  forallBoundedTelescope (← inferType h) (some 1) fun ys _ => do
    let y := ys[0]!
    mkFunExt (← mkLambdaFVars #[y] (← funExtN (mkApp h y) (n - 1)))

/-- `head as = head bs`, one step per argument the two sides differ at. -/
def stepCongr (head : Expr) (n : Nat) (arg : Nat → TermElabM Expr)
    (pf : Nat → TermElabM (Option Expr)) : TermElabM Expr := do
  let eqSides (p : Expr) : TermElabM (Expr × Expr) := do
    let some (_, l, r) := (← whnf (← instantiateMVars (← inferType p))).eq?
      | throwError "Not an equation:{indentExpr p}"
    return (l, r)
  let mut cur : Array Expr := #[]
  let mut steps : Array (Nat × Expr) := #[]
  for z in *...n do
    match ← pf z with
    | some p =>
      steps := steps.push (cur.size, p)
      cur := cur.push (← eqSides p).1
    | none => cur := cur.push (← arg z)
  let mut acc ← mkEqRefl (mkAppN head cur)
  for (pos, p) in steps do
    let motive ← withLocalDeclD `a (← inferType cur[pos]!) fun a =>
      mkLambdaFVars #[a] (mkAppN head (cur.set! pos a))
    acc ← mkEqTrans acc (← mkCongrArg motive p)
    cur := cur.set! pos (← eqSides p).2
  return acc

/--
`X._pre.c (kept images) = X._pre.c (kept fields)`, one step per field the two
sides differ at. -/
def valCongr (c : BridgeCtx) (cc : CtorSpec) (xs : Array Expr)
    (pf : Nat → TermElabM (Option Expr)) : TermElabM Expr := do
  let b := c.b
  let kept := keptPositions (b.fieldKinds cc.kinds)
  stepCongr (mkAppN (b.cst (b.preOf cc.name)) c.ps) kept.size
    (fun q => do b.preImage xs[kept[q]!]! (← inferType xs[kept[q]!]!))
    (fun q => pf kept[q]!)

/--
Move a minor's result from the constructors that were written to the ones the
raw recursor asks about. -/
def acrossFields (c : BridgeCtx) (cc : CtorSpec) (xs : Array Expr)
    (concl body : Expr) : TermElabM Expr := do
  -- the gap may already be closed, and then there is nothing to close it with
  if ← isDefEq (← inferType body) concl then return body
  let b := c.b
  let kinds := b.fieldKinds cc.kinds
  -- the round trip of every field at a copy, and the equation that closes it
  let mut rts := xs
  let mut steps : Array (Nat × Expr) := #[]
  for z in *...xs.size do
    let ty ← inferType xs[z]!
    -- a proof field outside the copies -- erased, or recursive at a proposition
    -- of the block -- proves a member the bridge may have restated, and has
    -- then moved too: `Ok v` at the field `v` is the raw member at the round
    -- trip of `v`, where the nice minor's proof sits
    let carried : Bool := match kinds[z]! with
      | .erased   => true
      | .recur mm => (c.copyAt? mm).isNone && b.members[mm]!.isProp
      | _         => false
    if carried then
      rts := rts.set! z (← c.toImage xs[z]! ty)
      continue
    let .recur mm := kinds[z]! | continue
    let some k := c.copyAt? mm | continue
    let cp := c.copies[k]!
    let img ← c.toImage xs[z]! ty
    let rt := (← c.ofImage img (← inferType img)).headBeta
    -- a field may be a function into the copy, and then the round trip closes at
    -- each argument and `funext` puts it back together
    let nzs ← forallTelescope ty fun zs _ => pure zs.size
    let pointwise ← forallTelescope ty fun zs tgt => do
      let a := (mkAppN rt zs).headBeta
      let a' := mkAppN xs[z]! zs
      -- a copy of a proposition has no round trip to close: the two sides are
      -- proofs of the one proposition, so they are the one proof
      mkLambdaFVars zs <| ←
        if b.members[cp.idx]!.isProp then
          pure (mkApp3 (mkConst ``proof_irrel) tgt a a')
        else
          c.subtypeExt cp.idx tgt a a' <|
            mkAppN (mkConst cp.roundName b.lvls)
              (c.ps ++ b.idxArgs tgt.getAppArgs ++ #[a'])
    steps := steps.push (z, ← funExtN pointwise nzs)
    rts := rts.set! z rt
  let mut body := body
  let mut cur := rts
  for (z, eq) in steps do
    let ty ← inferType xs[z]!
    -- a later field may be a proof *about* this one -- `Ok v` at the field `v`
    -- -- and it was moved onto the round trip along with it, so it has to be
    -- carried back the same way
    let mut carry : Array (Nat × Expr) := #[]
    for k in (z + 1)...xs.size do
      let abst ← kabstract (← Core.betaReduce (← inferType cur[k]!)) rts[z]!
      if abst.hasLooseBVars then carry := carry.push (k, .lam `w ty abst .default)
    let motive ← withLocalDeclD `w ty fun w =>
      do withLocalDeclD `hw (← mkEq rts[z]! w) fun hw => do
        let mut out := cur.set! z w
        for (k, mot) in carry do
          out := out.set! k (← mkEqNDRec mot out[k]! hw)
        mkLambdaFVars #[w, hw] (concl.replaceFVars xs out)
    body ← mkEqRec motive body eq
    -- the carried proofs moved with this step, and a proof about *two* fields
    -- at copies is still standing on the round trip of the one that has not had
    -- its step yet
    for (k, mot) in carry do
      cur := cur.set! k (← mkEqNDRec mot cur[k]! eq)
    cur := cur.set! z xs[z]!
  return body

/-- The raw motive standing behind the writer's, for a member the bridge restated. -/
def rawPropMotive (c : BridgeCtx) (m : Nat) (nice : Expr) : TermElabM Expr := do
  let b := c.b
  forallTelescope (← instantiateForall b.members[m]!.type c.ps) fun idxs _ =>
    withLocalDeclD `h (mkAppN (b.memberCst m) (c.ps ++ idxs)) fun h => do
      mkLambdaFVars (idxs ++ #[h]) (mkAppN nice (← c.toImages (idxs ++ #[h])))

/--
The equation between the constructor at its fields' round trips and the
constructor at the fields themselves, one step per field that is at a copy. -/
def roundTrip (c : BridgeCtx) (cc : CtorSpec) (xs : Array Expr) : TermElabM Expr := do
  let kinds := c.b.fieldKinds cc.kinds
  c.valCongr cc xs fun z => do
    let .recur mm := kinds[z]! | return none
    let some k := c.copyAt? mm | return none
    let cp := c.copies[k]!
    let nzs ← forallTelescope (← inferType xs[z]!) fun zs _ => pure zs.size
    -- at the value, which is where `valCongr` puts its steps; the whole
    -- constructor application is lifted back to the subtype afterwards
    let pointwise ← forallTelescope (← inferType xs[z]!) fun zs tgt =>
      mkLambdaFVars zs (mkAppN (mkConst cp.roundName c.b.lvls)
        (c.ps ++ c.b.idxArgs tgt.getAppArgs ++ #[mkAppN xs[z]! zs]))
    return some (← funExtN pointwise nzs)

/--
The same move as `BridgeCtx.acrossFields`, walked along the conclusion's
arguments instead of the constructor's fields. -/
def acrossIndices (c : BridgeCtx) (concl body : Expr) : TermElabM Expr := do
  let b := c.b
  let head := concl.getAppFn
  let raws := concl.getAppArgs
  let mut args := (← Core.betaReduce (← inferType body)).getAppArgs
  if args.size != raws.size then
    throwError "The minor concludes at {args.size} arguments where the raw one has {raws.size}"
  let mut body := body
  for j in *...raws.size do
    let tgt := raws[j]!
    let src := args[j]!
    if src == tgt then continue
    let ty ← inferType tgt
    -- a proof is carried by proof irrelevance, and an index the block did not
    -- rename is already where it belongs
    if ← isProp ty then continue
    if src.getAppFn == tgt.getAppFn then continue
    let some niceName := src.getAppFn.constName? | continue
    let some (m, cc) := (Array.range b.size).findSome? fun z =>
        (b.members[z]!.ctors.find? (·.name == niceName)).map ((z, ·))
      | continue
    let xs := tgt.getAppArgs.extract c.ps.size tgt.getAppArgs.size
    let eq ← c.subtypeExt m ty src tgt (← c.roundTrip cc xs)
    let motive ← withLocalDeclD `z ty fun z => do
      withLocalDeclD `h (← mkEq src z) fun h => do
      let mut out := args.set! j z
      for k in (j + 1)...args.size do
        let abst ← kabstract (← inferType args[k]!) src
        unless abst.hasLooseBVars do continue
        out := out.set! k (← mkEqNDRec (.lam `z ty abst .default) args[k]! h)
      mkLambdaFVars #[z, h] (mkAppN head out)
    body ← mkEqRec motive body eq
    args := (← Core.betaReduce (← inferType body)).getAppArgs
  return body

/--
`X.toOrig_ofOrig` at `x : ty`, if `ty` is a copy's original: the proof that
sending `x` into the copy and reading it back is `x` again. -/
def backEq? (c : BridgeCtx) (x ty : Expr) : MetaM (Option Expr) := do
  let some (k, idxs) ← c.copyOf? ty.headBeta | return none
  return some (mkAppN (mkConst c.copies[k]!.backName c.b.lvls) (c.ps ++ idxs ++ #[x]))

/--
A value the raw recursor returned, moved from the round trips of the writer's
indices onto the indices themselves; nothing moves in a block with no restated
member. -/
def backAcross (c : BridgeCtx) (raws : Array Expr) (body : Expr) :
    TermElabM Expr := do
  let mut body := body
  for tgt in raws do
    let ty ← inferType tgt
    -- the proof rides on the index it is about, and once that is where the
    -- writer put it the two proofs are the one proof
    if ← isProp ty then continue
    let some eq ← c.backEq? tgt ty | continue
    let some (_, src, _) := (← instantiateMVars (← inferType eq)).eq? | continue
    let stated ← Core.betaReduce (← inferType body)
    let args := stated.getAppArgs
    unless args.any (· == src) do continue
    let motive ← withLocalDeclD `z ty fun z => do
      withLocalDeclD `hz (← mkEq src z) fun hz => do
        let mut out := args
        for q in *...args.size do
          if args[q]! == src then
            out := out.set! q z
            continue
          let abst ← kabstract (← inferType args[q]!) src
          unless abst.hasLooseBVars do continue
          out := out.set! q (← mkEqNDRec (.lam `z ty abst .default) args[q]! hz)
        mkLambdaFVars #[z, hz] (mkAppN stated.getAppFn out)
    body ← mkEqRec motive body eq
  return body

/--
Add a restatement of the raw recursor `recCst`, over the block's parameters, the
nice motives and minors, concluding at `goalMot`. -/
def addRestated (c : BridgeCtx) (i : Nat) (lp niceName : Name)
    (nmots nmins : Array Expr) (goalMot recCst : Expr)
    (rmots rmins : Array Expr) : TermElabM Unit := do
  let b := c.b
  let (type, value) ←
    forallTelescope (← c.niceArity i) fun idxs _ =>
      withLocalDeclD `t (c.majorType i idxs) fun t => do
        let hide := hideRecBinders c.ps.size (nmots.size + nmins.size) idxs.size
        let all := c.ps ++ nmots ++ nmins ++ idxs ++ #[t]
        -- the raw recursor is indexed over the copies, so the major premise's
        -- indices go across; the premise itself does not, the written statement
        -- of a member being by definition the raw one at those very images --
        -- unless the member is itself a copy, whose premise is the original's
        let rIdxs ← c.ofImages idxs
        let rt ← c.ofImage t (c.majorType i idxs)
        let raw := mkAppN recCst (c.ps ++ rmots ++ rmins ++ rIdxs ++ #[rt])
        -- and then what the raw one concludes at is the round trip of the
        -- writer's arguments, which is those arguments up to `X.toOrig_ofOrig`
        let body ← if (c.copyAt? i).isNone then pure raw
                   else c.backAcross (idxs ++ #[t]) raw
        -- `goalMot` is a motive when the conclusion is just that motive at the
        -- indices, and a function of them when the conclusion is more than that
        return (hide (← mkForallFVars all
                  (← Core.betaReduce (mkAppN goalMot (idxs ++ #[t])))),
                hide (← mkLambdaFVars all body))
  let type ← instantiateMVars type
  if let some n := c.leaked? type then
    throwError "`{niceName}` would be stated with `{n}` in it, which is not \
      one of the writer's names"
  addDef niceName (lp :: b.us) type (← instantiateMVars value)
  markElabAsElim niceName

/-- Add `X.ofOrig_toOrig` for each copy in `needed`. -/
def addRoundTrips (c : BridgeCtx) (needed : Array Nat) (rawRec : Nat → Name) :
    TermElabM Unit := do
  let b := c.b
  -- `(X.ofOrig (X.toOrig t)).val`, for `t` a term of the copy at `ids`
  let roundLhs (k : Nat) (ids : Array Expr) (t : Expr) : MetaM Expr := do
    let cp := c.copies[k]!
    let there := mkAppN (mkConst cp.toName b.lvls) (c.ps ++ ids ++ #[t])
    let back := mkAppN (mkConst cp.ofName b.lvls) (c.ps ++ ids ++ #[there])
    return b.sVal cp.idx (← b.valArgs cp.idx (c.ps ++ ids)) back
  let motives ← b.dataIdxs.mapM fun i => do
    forallTelescope (← instantiateForall b.members[i]!.type c.ps) fun ids _ =>
      withLocalDeclD `t (mkAppN (b.cst b.members[i]!.name) (c.ps ++ ids)) fun t => do
        let body ← match c.copyAt? i with
          | some k => mkEq (← roundLhs k ids t) (b.sVal i (← b.valArgs i (c.ps ++ ids)) t)
          | none   => pure (mkConst ``True)
        mkLambdaFVars (ids ++ #[t]) body
  for k in needed do
    let cp := c.copies[k]!
    let recCst := mkConst (rawRec cp.idx) (Level.zero :: b.lvls)
    let minors ← c.withRawMinors recCst motives fun i cc xs ihs _ => do
      if (c.copyAt? i).isNone then
        return mkConst ``True.intro
      let kinds := b.fieldKinds cc.kinds
      let ihPos := b.ihPositions kinds
      c.valCongr cc xs fun z => do
        let .recur m := kinds[z]! | return none
        if (c.copyAt? m).isNone then return none
        let nzs ← forallTelescope (← inferType xs[z]!) fun zs _ => pure zs.size
        return some (← funExtN ihs[(ihPos.findIdx? (· == z)).getD 0]! nzs)
    let (type, value) ←
      forallTelescope (← instantiateForall b.members[cp.idx]!.type c.ps) fun idxs _ =>
        withLocalDeclD `x (mkAppN (b.cst cp.name) (c.ps ++ idxs)) fun x => do
          let ty := implicitPrefix (c.ps.size + idxs.size) (←
            mkForallFVars (c.ps ++ idxs ++ #[x])
              (← mkEq (← roundLhs k idxs x)
                (b.sVal cp.idx (← b.valArgs cp.idx (c.ps ++ idxs)) x)))
          let val := implicitPrefix (c.ps.size + idxs.size) (←
            mkLambdaFVars (c.ps ++ idxs ++ #[x])
              (mkAppN recCst (c.ps ++ motives ++ minors ++ idxs ++ #[x])))
          return (ty, val)
    addDecl (.thmDecl { name := cp.roundName, levelParams := b.us
                        type := ← instantiateMVars type
                        value := ← instantiateMVars value })

/-! ### The round trip taken from the other end

`ofOrig_toOrig` starts at the copy, an induction over a member of this block.
`toOrig_ofOrig` starts at the original, so it is a different induction.

The scheme is `ofOrig`'s for a `Prop` copy.  Every copy in the group gets its
round trip as a motive, everything else goes to `True`, and a field at a group
member takes the hypothesis the recursor supplies.  Each minor is a congruence
between one constructor at two lots of arguments; a field is left alone where the
round trip comes back by eta through a structure, and is otherwise that
hypothesis or the round trip of the copy it is at.  The congruence is
`mkHCongrWithArity`'s and so heterogeneous, which a field indexed by another
needs: what moves under such a field moves its type with it, leaving a `HEq`.  A
data field there is out of reach; a `Prop` one is `proof_irrel_heq`.

This exists for `ofOrig_inj`, and through it the injectivity of a constructor
with a field at a copy: `injection` leaves an equation between the two sides'
`ofOrig`s, for which `ofOrig_toOrig` is the wrong half.
-/

/-- `X.toOrig (X.ofOrig x)`, for `x` the original at `jdxs`. -/
def backLhs (c : BridgeCtx) (k : Nat) (jdxs : Array Expr) (x : Expr) : MetaM Expr := do
  let cp := c.copies[k]!
  let imgs ← c.ofImages jdxs
  return mkAppN (mkConst cp.toName c.b.lvls)
    (c.ps ++ imgs ++ #[mkAppN (mkConst cp.ofName c.b.lvls) (c.ps ++ jdxs ++ #[x])])

/-- `X.toOrig_ofOrig`, by the original's own recursor at the whole group. -/
def backValue (c : BridgeCtx) (grp : Array Nat) (k : Nat) (wanted : IO.Ref (Array Nat)) :
    TermElabM (Expr × Expr) := do
  let cp := c.copies[k]!
  forallTelescope (← inferType cp.app) fun jdxs _ => do
  let orig := cp.orig jdxs
  let params := orig.getAppArgs
  let lvls := orig.getAppFn.constLevels!
  let idxs := jdxs.extract cp.numLocals jdxs.size
  let ge ← c.groupElim grp cp params lvls fun k' jdxs' major => do
    mkEq (← c.backLhs k' jdxs' major) major
  let minors ← ge.minors fun _ mp args _ => do
    let cn := mp.ctor
    let nf := mp.numFields
    let fields := args.extract 0 nf
    let ihs := args.extract nf args.size
    -- what the left side holds at each field, and the equation saying it
    -- comes back to the right side's, where there is one to be had
    let mut lhss : Array Expr := #[]
    let mut steps : Array (Option Expr) := #[]
    for z in *...nf do
      let ty ← inferType fields[z]!
      let nzs ← forallTelescope ty fun zs _ => pure zs.size
      let mut step : Option Expr := none
      let mut lhs := fields[z]!
      if let some (j, mq') := mp.ihs[z]! then
        if ge.targets[mq']!.isSome then
          -- a field that is a function into the group is given a hypothesis for
          -- each of its values, and the equation wanted is of the two functions
          step := some (← funExtN ihs[j]! nzs)
      if step.isNone then
        (lhs, step) ← forallTelescope ty fun zs concl => do
          let some (k', jdxs') ← c.copyOf? concl | return (fields[z]!, none)
          let fz := mkAppN fields[z]! zs
          let side ← c.backLhs k' jdxs' fz
          -- the round trip at a field may come back on its own -- through
          -- a structure it does, by eta, and between two proofs of one
          -- proposition it does too -- and then there is nothing to say
          if ← isDefEq side fz then return (fields[z]!, none)
          if c.b.members[c.copies[k']!.idx]!.isProp then
            -- two proofs of two propositions that differ only in what has
            -- moved underneath them: no equation is wanted or available,
            -- and `proof_irrel_heq` closes the step below
            let cpn := c.copies[k']!.name
            unless nzs == 0 do
              throwError "field {z} of `{cn}` is a family of proofs at `{cpn}`"
            return (side, none)
          -- otherwise it is that copy's own round trip that says so, and if
          -- that has not been proved then saying which one it was is what
          -- gets it proved and this pass run again
          unless (← getEnv).contains c.copies[k']!.backName do
            wanted.modify fun w => if w.contains k' then w else w.push k'
            throwError "no round trip out of `{c.copies[k']!.name}` to use at `{cn}`"
          let e := mkAppN (mkConst c.copies[k']!.backName c.b.lvls)
            (c.ps ++ jdxs' ++ #[fz])
          return (← mkLambdaFVars zs side, some (← funExtN (← mkLambdaFVars zs e) nzs))
      -- the equation's own left side is the one to use, so that what the
      -- steps are taken at is exactly what they are stated about
      if let some e := step then
        let some (_, l, _) := (← whnf (← inferType e)).eq?
          | throwError "field {z} of `{cn}` was given something that is not an equation"
        lhs := l
      lhss := lhss.push lhs
      steps := steps.push step
    -- a field a later field's type mentions cannot be moved on its own, so
    -- the congruence is taken heterogeneously: at such a field the two
    -- sides are of two different types, and only a `Prop` one is reachable
    let ct ← mkHCongrWithArity (mkAppN (mkConst cn lvls) params) nf
    let mut prf := ct.proof
    let mut cty := ct.type
    for z in *...nf do
      let a := lhss[z]!
      let b := fields[z]!
      let rest := (cty.bindingBody!.instantiate1 a).bindingBody!.instantiate1 b
      let e ← match steps[z]!, rest.bindingDomain!.isAppOf ``Eq with
        | some s, true  => pure s
        | some s, false => mkHEqOfEq s
        | none,   true  => mkEqRefl b
        | none,   false =>
          if a == b then mkHEqRefl b else mkAppM ``proof_irrel_heq #[a, b]
      prf := mkApp3 prf a b e
      cty := rest.bindingBody!.instantiate1 e
    mkEqOfHEq prf
  withLocalDeclD `x (mkAppN orig idxs) fun x => do
    let all := c.ps ++ jdxs ++ #[x]
    let n := c.ps.size + jdxs.size
    return (implicitPrefix n (← mkForallFVars all (← mkEq (← c.backLhs k jdxs x) x)),
            implicitPrefix n (← mkLambdaFVars all (ge.app params minors idxs x)))

/-- `X.ofOrig_inj`, which is the round trip read as a left inverse. -/
def ofInjValue (c : BridgeCtx) (k : Nat) : TermElabM (Expr × Expr) := do
  let cp := c.copies[k]!
  forallTelescope (← inferType cp.app) fun jdxs _ => do
    let ofOrig (t : Expr) := mkAppN (mkConst cp.ofName c.b.lvls) (c.ps ++ jdxs ++ #[t])
    let back (t : Expr) := mkAppN (mkConst cp.backName c.b.lvls) (c.ps ++ jdxs ++ #[t])
    withLocalDeclD `a (cp.origAt jdxs) fun a => withLocalDeclD `b (cp.origAt jdxs) fun b => do
      let imgs ← c.ofImages jdxs
      let toFn ← withLocalDeclD `t (← inferType (ofOrig a)) fun t =>
        mkLambdaFVars #[t] (mkAppN (mkConst cp.toName c.b.lvls) (c.ps ++ imgs ++ #[t]))
      withLocalDeclD `h (← mkEq (ofOrig a) (ofOrig b)) fun h => do
        let all := c.ps ++ jdxs ++ #[a, b, h]
        let n := c.ps.size + jdxs.size + 2
        let val ← mkEqTrans (← mkEqSymm (back a)) (← mkEqTrans (← mkCongrArg toFn h) (back b))
        return (implicitPrefix n (← mkForallFVars all (← mkEq a b)),
                implicitPrefix n (← mkLambdaFVars all val))

/--
Add `X.toOrig_ofOrig` and `X.ofOrig_inj` for each data copy in `needed`, and for
each copy those turn out to be proved at. -/
def addBackTrips (c : BridgeCtx) (needed : Array Nat) : TermElabM Unit := do
  let order ← c.order
  let wanted ← IO.mkRef (#[] : Array Nat)
  let prove (grp : Array Nat) (k : Nat) : TermElabM Unit := do
    let cp := c.copies[k]!
    let (type, value) ← c.backValue grp k wanted
    addDecl (.thmDecl { name := cp.backName, levelParams := c.b.us
                        type := ← instantiateMVars type
                        value := ← instantiateMVars value })
    let (type, value) ← c.ofInjValue k
    addDecl (.thmDecl { name := cp.ofInjName, levelParams := c.b.us
                        type := ← instantiateMVars type
                        value := ← instantiateMVars value })
  -- a `Prop` copy needs none: its round trip and itself are the same proof, and
  -- the kernel already knows it
  let todo (k : Nat) : TermElabM Bool := do
    if c.b.members[c.copies[k]!.idx]!.isProp then return false
    return !(← getEnv).contains c.copies[k]!.backName
  let mut want := needed
  let mut growing := true
  while growing do
    growing := false
    for grp in order do
      for k in grp do
        unless want.contains k do continue
        unless ← todo k do continue
        wanted.set #[]
        let env ← getEnv
        try
          prove grp k
        catch _ =>
          setEnv env
          for k' in ← wanted.get do
            unless want.contains k' do
              want := want.push k'
              growing := true
  for grp in order do
    for k in grp do
      unless want.contains k do continue
      unless ← todo k do continue
      discard <| attempt? `Mumi.indind m!"no round trip out of `{c.copies[k]!.name}`" (prove grp k)

/--
The front of a recursor stated the way the writer wrote the block, handed to `k`
as the motives and the minors. -/
def withNiceFront {α} [Inhabited α] (c : BridgeCtx) (f : Front)
    (k : Array Expr → Array Expr → TermElabM α) : TermElabM α := do
  let b := c.b
  let mnames := motiveNames f.members.size
  let motiveDecls : Array (Name × (Array Expr → TermElabM Expr)) :=
    f.members.mapIdx fun q m => (mnames[q]!, fun _ => do
      match c.copyAt? m with
      | some ci =>
        let cp := c.copies[ci]!
        forallTelescope (← inferType cp.app) fun jdxs _ =>
          withLocalDeclD f.major (cp.origAt jdxs) fun t =>
            mkForallFVars (jdxs ++ #[t]) (mkSort f.lvl)
      | none =>
        forallTelescope (← c.niceArity m) fun ids _ =>
          withLocalDeclD f.major (mkAppN (b.cst b.members[m]!.name) (c.ps ++ ids)) fun t =>
            mkForallFVars (ids ++ #[t]) (mkSort f.lvl))
  withImplicits motiveDecls fun nmotives => do
    let mut minorDecls : Array (Name × (Array Expr → TermElabM Expr)) := #[]
    for m in f.members do
      for cc in b.members[m]!.ctors do
        minorDecls := minorDecls.push (Name.mkSimple cc.name.getString!, fun _ => do
          forallTelescope (← c.unCopy (← instantiateForall cc.type c.ps)) fun ys concl => do
            let kinds := b.fieldKinds cc.kinds
            let ihDecls : Array (Name × (Array Expr → TermElabM Expr)) :=
              (f.ihPos kinds).map fun z => (`ih, fun _ => do
                let some mm := kinds[z]!.ihTarget? | throwError "Not a recursive field"
                forallTelescope (← inferType ys[z]!) fun zs tgt => do
                  mkForallFVars zs (mkAppN nmotives[f.pos mm]!
                    ((← c.niceIdxArgs mm tgt) ++ #[mkAppN ys[z]! zs])))
            withLocalDeclsD ihDecls fun ihs => do
              let ctorApp := match c.copyAt? m with
                | some ci => c.copies[ci]!.origCtor cc.name ys
                | none    => mkAppN (b.cst cc.name) (c.ps ++ ys)
              mkForallFVars (ys ++ ihs) (mkAppN nmotives[f.pos m]!
                ((← c.niceIdxArgs m concl) ++ #[ctorApp])))
    withLocalDeclsD minorDecls fun nminors => k nmotives nminors

/-- The recursor for a member the writer declared, with only originals in it. -/
def addNiceRec (c : BridgeCtx) (i : Nat) (lp : Name) (rawRec : Nat → Name)
    (niceName : Name) (rawOf : Name → Name) : TermElabM Unit := do
  let b := c.b
  let lvl := Level.param lp
  let dIdxs := b.dataIdxs
  c.withNiceFront
      { members := dIdxs, pos := c.dpos, lvl, major := `t, ihPos := b.ihPositions }
      fun nmotives nminors => do
    let rmotives ← dIdxs.mapM fun m =>
      match c.copyAt? m with
      | none   => pure nmotives[c.dpos m]!
      | some k => do
        let cp := c.copies[k]!
        forallTelescope (← instantiateForall b.members[m]!.type c.ps) fun ids _ =>
          withLocalDeclD `t (mkAppN (b.memberCst m) (c.ps ++ ids)) fun t => do
            mkLambdaFVars (ids ++ #[t]) (mkAppN nmotives[c.dpos m]!
              ((← c.toImages ids) ++
                #[mkAppN (mkConst cp.toName b.lvls) (c.ps ++ ids ++ #[t])]))
    let recCst := mkConst (rawRec i) (lvl :: b.lvls)
    let rminors ← c.withRawMinors recCst rmotives fun _ cc xs ihs concl => do
      let vals ← c.toImages xs
      let body := mkAppN nminors[b.minorIdx dIdxs cc.name]! (vals ++ ihs)
      if rawOf cc.name == cc.name then return body
      c.acrossFields cc xs concl body
    c.addRestated i lp niceName nmotives nminors nmotives[c.dpos i]! recCst
      rmotives rminors

/-- The recursor over the whole block, with only originals in it. -/
def addNiceGrandRec (c : BridgeCtx) (i : Nat) (lp : Name) (rawGrand : Nat → Name)
    (niceOf : Nat → Name) (rawOf : Name → Name) (free ready : Array Nat) :
    TermElabM Unit := do
  let b := c.b
  let lvl := Level.param lp
  let recCst := mkConst (rawGrand i) (lvl :: b.lvls)
  -- anything of the writer's own reads back under the name that was written: a
  -- constructor whose type mentions a copy, and a proposition indexed by one
  let renames : Array (Name × Name) := Id.run do
    let mut out : Array (Name × Name) := #[]
    for m in b.members do
      if b.rawMember m.name != m.name then out := out.push (b.rawMember m.name, m.name)
      for cc in m.ctors do
        if rawOf cc.name != cc.name then out := out.push (rawOf cc.name, cc.name)
    return out
  let nice (e : Expr) : MetaM Expr := do
    let e ← c.unCopy e
    if renames.isEmpty then return e
    return e.replace fun s => match s with
      | .const n us => (renames.find? (·.1 == n)).map fun (_, nn) => .const nn us
      | _           => none
  -- one motive per member and one minor per constructor -- of the members the
  -- recursion covers, which is all of them but the `Prop` ones `emitGrandRecs`
  -- left out for being indexed by no data member
  let covered := (Array.range b.size).filter (!free.contains ·)
  let nMinors : Nat := Id.run do
    let mut n := 0
    for z in covered do
      n := n + b.members[z]!.ctors.size
    return n
  let recTy ← instantiateForall (← inferType recCst) c.ps
  forallBoundedTelescope recTy covered.size fun rmots rest0 => do
  forallBoundedTelescope rest0 nMinors fun rmins rest1 => do
    -- the major premise's motive, and so the one the restatement concludes at
    let iq ← forallTelescope rest1 fun _ concl => do
      let some q := rmots.findIdx? (· == concl.getAppFn)
        | throwError "`{rawGrand i}` does not conclude at one of its motives"
      pure q
    let mut motDecls : Array (Name × (Array Expr → TermElabM Expr)) := #[]
    for h : q in *...rmots.size do
      let ty ← nice (← inferType rmots[q])
      let pre := rmots.extract 0 q
      motDecls := motDecls.push ((← rmots[q].fvarId!.getUserName),
        fun prev => pure (ty.replaceFVars pre prev))
    withImplicits motDecls fun nmots => do
      let mut minDecls : Array (Name × (Array Expr → TermElabM Expr)) := #[]
      for h : q in *...rmins.size do
        let ty ← nice (← inferType rmins[q])
        let pre := rmots ++ rmins.extract 0 q
        minDecls := minDecls.push ((← rmins[q].fvarId!.getUserName),
          fun prev => pure (ty.replaceFVars pre (nmots ++ prev)))
      withLocalDeclsD minDecls fun nmins => do
        -- a motive's own binders can mention an earlier motive -- that is what
        -- makes this one recursion -- so each is put across under the ones before
        -- it, or the raw binder would be left in the value's binder types
        let mut rmotives : Array Expr := #[]
        for h : q in *...rmots.size do
          let ty ← Core.betaReduce ((← inferType rmots[q]).replaceFVars (rmots.extract 0 q)
            rmotives)
          rmotives := rmotives.push <| ←
            forallTelescope ty fun zs _ => do
              mkLambdaFVars zs (mkAppN nmots[q]! (← c.toImages zs))
        let mut rminors : Array Expr := #[]
        for h : q in *...rmins.size do
          -- which constructor the minor is for, and which motive it concludes
          -- at, read off before the motives go across: what the substitution
          -- leaves at the conclusion's head is no longer one of them
          let (rawName, mq) ← forallTelescope (← inferType rmins[q]) fun _ concl => do
            let some rawName := concl.getAppArgs.back?.bind (·.getAppFn.constName?)
              | throwError "A minor of `{rawGrand i}` does not conclude at a constructor"
            let some mq := rmots.findIdx? (· == concl.getAppFn)
              | throwError "A minor of `{rawGrand i}` does not conclude at a motive"
            pure (rawName, mq)
          -- a `Prop` motive is stated over what the data recursor returns, so a
          -- minor concluding at one mentions the data minors as well as the
          -- motives, and those have to go across too or their raw binders are
          -- left free in the value
          let ty ← Core.betaReduce ((← inferType rmins[q]).replaceFVars
            (rmots ++ rmins.extract 0 q) (rmotives ++ rminors))
          rminors := rminors.push <| ←
            forallTelescope ty fun args concl => do
              let some (mz, cc) := (Array.range b.size).findSome? fun z =>
                  (b.members[z]!.ctors.find? fun cc => rawOf cc.name == rawName).map ((z, ·))
                | throwError "No constructor of the block behind `{rawName}`"
              let kinds := b.fieldKinds cc.kinds
              let xs := args.extract 0 kinds.size
              let ihs := args.extract kinds.size args.size
              let vals ← c.toImages xs
              let body := mkAppN nmins[q]! (vals ++ ihs)
              if rawOf cc.name == cc.name then
                return ← mkLambdaFVars args body
              -- a constructor that *builds* a deleted index has the copy in the
              -- index and in the term at once, and only the field they came
              -- from has an equation, so that one moves on the field axis
              let kinds' := b.fieldKinds cc.kinds
              if b.members[mz]!.dropped.any fun p => (deletedField? kinds' p).isNone then
                mkLambdaFVars args (← c.acrossFields cc xs concl body)
              else
                mkLambdaFVars args (← c.acrossIndices concl body)
        -- the conclusion, read off the raw one and put across binder by binder
        let goal ← forallTelescope rest1 fun zs concl => do
          let across (e : Expr) : TermElabM Expr :=
            Core.betaReduce (e.replaceFVars (rmots ++ rmins) (rmotives ++ rminors))
          let fixed := c.ps.size + rmots.size + rmins.size
          let args ← concl.getAppArgs.mapM fun a => do
            let some n := a.getAppFn.constName? | across a
            let rest ← (a.getAppArgs.extract fixed a.getAppArgs.size).mapM across
            if let some z := ready.find? fun z => rawGrand z == n then
              return mkAppN (mkConst (niceOf z) a.getAppFn.constLevels!)
                (c.ps ++ nmots ++ nmins ++ rest)
            -- a copy is covered by the recursion but is nothing the writer
            -- named, so there is no name to read its recursion under
            if let some k := c.copies.findIdx? fun cp => rawGrand cp.idx == n then
              throwError "the writer has no name for the recursion at \
                `{← ppExpr (c.copies[k]!.orig #[])}`, which is what this \
                proposition is indexed by"
            if covered.any (rawGrand · == n) then
              throwError "`{rawGrand i}` concludes at `{n}`, which is not \
                stated over the originals"
            across a
          mkLambdaFVars zs (mkAppN nmots[iq]! args)
        c.addRestated i lp (niceOf i) nmots nmins goal recCst rmotives rminors

/-- The positions of the fields a `Prop` member's recursor gets a hypothesis for. -/
def propRecPositions (b : Block) (grp : Array Nat) (kinds : Array FieldKind) : Array Nat :=
  (recPositions kinds).filter fun z =>
    match kinds[z]! with
    | .recur m => b.members[m]!.isProp && grp.contains m
    | _        => false

/-- What the two `Prop` recursor builders both read off the pre-block's recursor. -/
structure PropRecs where
  /-- The pre-block's own recursor, which a raw one is one application of. -/
  info : RecursorVal
  /-- Every `Prop` member behind that recursor, in the order it runs over them. -/
  pIdxs : Array Nat
  /-- The ones a recursor is wanted for. -/
  kIdxs : Array Nat
  /-- The motives' universe. -/
  lvl : Level
  /-- The levels the pre-block's recursor is taken at. -/
  recLvls : List Level
  /-- The level parameters a recursor built from it takes. -/
  us : List Name

/--
Read that off one layer of the block's propositions, or `none` if there is
nothing there to build. -/
def propRecs? (b : Block) (lp : Name) (rep : Nat) (keep : Array Nat) :
    MetaM (Option PropRecs) := do
  let info ← getConstInfoRec (mkRecName (preName b.members[rep]!.name))
  let pIdxs ← b.propsBehind info
  let kIdxs := pIdxs.filter (keep.contains ·)
  if kIdxs.isEmpty then return none
  let large := info.levelParams.length != b.us.length
  let lvl := if large then Level.param lp else Level.zero
  return some { info, pIdxs, kIdxs, lvl
                recLvls := if large then lvl :: b.lvls else b.lvls
                us := if large then lp :: b.us else b.us }

/-- `X.rec` for a `Prop` member, stated over the block rather than the pre-types. -/
def addPropRecs (c : BridgeCtx) (s : PropRecs) (recNameOf : Nat → Name) :
    TermElabM Unit := do
  let b := c.b
  let ps := c.ps
  let { info := recInfo, pIdxs, kIdxs, lvl, recLvls, us } := s
  let ppos (m : Nat) : Nat := (kIdxs.findIdx? (· == m)).getD 0
  b.withRawFront ps
      { members := kIdxs, pos := ppos, lvl, major := `h,
        ihPos := propRecPositions b s.pIdxs }
      fun motives minors => do
    -- a member nobody asked for is recursed into all the same, at `PUnit`,
    -- which is a `Sort` at whatever level the raw recursor eliminates into
    let trivMotive := mkConst ``PUnit [lvl]
    let rmotives ← pIdxs.mapM fun j =>
      c.withWfIdxs j fun pres ws reals =>
        withLocalDeclD `h (mkAppN (b.cst (preName b.members[j]!.name)) (ps ++ pres)) fun h => do
          let body ←
            if kIdxs.contains j then
              mkForallFVars ws (mkAppN motives[ppos j]! (reals.map (·.1) ++ #[h]))
            else
              pure trivMotive
          mkLambdaFVars (pres ++ #[h]) body
    let recTy ← instantiateForall
      (recInfo.type.instantiateLevelParams recInfo.levelParams recLvls) (ps ++ rmotives)
    let rminors ← forallBoundedTelescope recTy recInfo.numMinors fun ms _ => do
      let order := b.ctorsOf pIdxs
      -- `minors` runs over the kept members' constructors only, in the same order
      let minorPos : Array (Option Nat) := Id.run do
        let mut out : Array (Option Nat) := #[]
        let mut acc := 0
        for (j, _) in order do
          if kIdxs.contains j then
            out := out.push (some acc); acc := acc + 1
          else
            out := out.push none
        return out
      let mut out : Array Expr := #[]
      for q in *...ms.size do
        let (_, cc) := order[q]!
        let some qm := minorPos[q]!
          | out := out.push <| ← forallTelescope (← inferType ms[q]!) fun args _ =>
              mkLambdaFVars args (mkConst ``PUnit.unit [lvl])
            continue
        let kinds := b.fieldKinds cc.kinds
        let ihPos := propRecPositions b s.pIdxs kinds
        out := out.push <| ←
          forallBoundedTelescope (← inferType ms[q]!) (kinds.size + ihPos.size)
            fun args concl => do
              withRawPropMinor b cc ps kinds args concl fun xs ihs subTys parts ws => do
                let mut vals : Array Expr := #[]
                let mut nihs : Array Expr := #[]
                for z in *...xs.size do
                  let ty ← inferType xs[z]!
                  match kinds[z]! with
                  | .plain | .erased => vals := vals.push xs[z]!
                  | .deleted .. => throwError "A `Prop` member deleted an index"
                  | .recur m =>
                    if !b.members[m]!.isProp then
                      -- a data field, rebuilt at the subtype from the proof in hand
                      -- a minor lands in the motive's universe, and a stray
                      -- field may be stood in for exactly when that is `Prop`
                      vals := vals.push <| ←
                        rebuiltField b cc parts xs[z]! subTys[z]!
                          (strayOk := s.lvl == .zero)
                    else
                      -- the field itself passes through; its hypothesis is the
                      -- raw one at the well-formedness the rebuild used -- and
                      -- there is one only if this recursion runs over that
                      -- member, which an earlier layer's it does not
                      vals := vals.push xs[z]!
                      if s.pIdxs.contains m then
                        nihs := nihs.push (← atParts parts ihs[nihs.size]! ty)
                mkLambdaFVars (args ++ ws) (mkAppN minors[qm]! (vals ++ nihs))
      return out
    for q in *...kIdxs.size do
      let j := kIdxs[q]!
      let m := b.members[j]!
      let (type, value) ←
        forallTelescope (← instantiateForall m.type ps) fun idxs _ =>
          withLocalDeclD `h (mkAppN (b.memberCst j) (ps ++ idxs)) fun h => do
            let hide := hideRecBinders ps.size (motives.size + minors.size) idxs.size
            let ty := hide (←
              mkForallFVars (ps ++ motives ++ minors ++ idxs ++ #[h])
                (mkAppN motives[q]! (idxs ++ #[h])))
            let (pres, wfs) ← b.preAndWf idxs
            let val := hide (←
              mkLambdaFVars (ps ++ motives ++ minors ++ idxs ++ #[h])
                (mkAppN (mkConst (mkRecName (preName m.name)) recLvls)
                  (ps ++ rmotives ++ rminors ++ pres ++ #[h] ++ wfs)))
            return (ty, val)
      addDef (recNameOf j) us (← instantiateMVars type) (← instantiateMVars value)
        (compile := false)
      markElabAsElim (recNameOf j)

/-- `X.rec` for a `Prop` member, with only originals in it. -/
def addNicePropRec (c : BridgeCtx) (s : PropRecs) (j : Nat) (rawRec : Nat → Name)
    (niceName : Name) : TermElabM Unit := do
  let b := c.b
  let ps := c.ps
  let kIdxs := s.kIdxs
  let ppos (m : Nat) : Nat := (kIdxs.findIdx? (· == m)).getD 0
  c.withNiceFront
      { members := kIdxs, pos := ppos, lvl := s.lvl, major := `h,
        ihPos := propRecPositions b s.pIdxs }
      fun nmotives nminors => do
    let rmotives ← kIdxs.mapM fun m =>
      match c.copyAt? m with
      | none   =>
        if b.rawMember b.members[m]!.name == b.members[m]!.name then
          pure nmotives[ppos m]!
        else c.rawPropMotive m nmotives[ppos m]!
      | some k => do
        forallTelescope (← instantiateForall b.members[m]!.type ps) fun idxs _ =>
          withLocalDeclD `h (mkAppN (b.memberCst m) (ps ++ idxs)) fun h => do
            mkLambdaFVars (idxs ++ #[h]) (mkAppN nmotives[ppos m]!
              ((← c.toImages idxs) ++
                #[mkAppN (mkConst c.copies[k]!.toName b.lvls) (ps ++ idxs ++ #[h])]))
    let recCst := mkConst (rawRec j) (s.us.map Level.param)
    let recTy ← instantiateForall (← inferType recCst) (ps ++ rmotives)
    let mut numMinors := 0
    for m in kIdxs do numMinors := numMinors + b.members[m]!.ctors.size
    let rminors ← forallBoundedTelescope recTy numMinors fun ms _ => do
      let mut out : Array Expr := #[]
      let mut q := 0
      for m in kIdxs do
        for cc in b.members[m]!.ctors do
          let kinds := b.fieldKinds cc.kinds
          let nf := kinds.size
          out := out.push <| ←
            forallBoundedTelescope (← inferType ms[q]!)
                (nf + (propRecPositions b s.pIdxs kinds).size) fun args concl => do
              let xs := args.extract 0 nf
              let body := mkAppN nminors[q]!
                ((← c.toImages xs) ++ args.extract nf args.size)
              mkLambdaFVars args (← c.acrossFields cc xs concl body)
          q := q + 1
      return out
    let (type, value) ←
      forallTelescope (← c.niceArity j) fun idxs _ =>
        withLocalDeclD `h (mkAppN (b.cst b.members[j]!.name) (ps ++ idxs)) fun h => do
          let hide := hideRecBinders ps.size (nmotives.size + nminors.size) idxs.size
          let all := ps ++ nmotives ++ nminors ++ idxs ++ #[h]
          let rIdxs ← c.ofImages idxs
          let val ← c.backAcross (idxs ++ #[h])
            (mkAppN recCst (ps ++ rmotives ++ rminors ++ rIdxs ++ #[h]))
          return (hide (← mkForallFVars all (mkAppN nmotives[ppos j]! (idxs ++ #[h]))),
                  hide (← mkLambdaFVars all val))
    addDef niceName s.us (← instantiateMVars type) (← instantiateMVars value)
      (compile := false)
    markElabAsElim niceName

end BridgeCtx

/-! ## The induction-inductive recursor

Steps 8 and 9 build two separate recursors, one over the data members and one
over the `Prop` members.  That computes, but a `Prop` member's motive should be
able to mention the *value* the recursion produced at its data index, and a data
constructor carrying a proof should get an induction hypothesis for it:

```
mutual
inductive Ctx : Type where
  | nil | snoc (Γ : Ctx) (x : String) (h : Fresh x Γ) : Ctx
inductive Fresh : String → Ctx → Prop where
  | nil (x) : Fresh x .nil
  | snoc (x y) (Γ) (h : Fresh y Γ) : x ≠ y → Fresh x Γ → Fresh x (.snoc Γ y h)
end
```

the recursor wanted is

```
Ctx.rec.{u} {motive_1 : Ctx → Sort u}
    {motive_2 : (x : String) → (Γ : Ctx) → motive_1 Γ → Fresh x Γ → Prop}
    (nil : motive_1 .nil)
    (snoc : (Γ : Ctx) → (x : String) → (h : Fresh x Γ) → (Γ_ih : motive_1 Γ) →
      (h_ih : motive_2 x Γ Γ_ih h) → motive_1 (.snoc Γ x h)) → ..
```

and `Fresh.rec` takes the same motives and minors.  The two motives cannot be
merged -- `Fresh` is small-eliminating -- but it must be one recursion: the value
at `Ctx.snoc Γ x h` needs the proof-motive's value at `h`, which needs the
data-motive's value at `Γ`.  So the recursion computes at each pre-term a
**bundle**: the data value paired with the proof-motive's value at *every* proof
of *every* `Prop` member indexed by that pre-term.

```
Bundle p := (w : Ctx._wf p) →
  PSigma fun c : motive_1 ⟨p, w⟩ => ∀ x (h : Fresh._pre x p), motive_2 x ⟨p, w⟩ c h
```

The pairing is a `PSigma` rather than a `Subtype` because the first component is
data, and it stays one even for a data member no `Prop` member is indexed by
(with `fun _ => True` second), so every bundle lands in `Sort (max 1 u)` and the
group can recurse together.

Building the bundle at a data constructor is the work.  The data component is the
minor applied to the rebuilt fields, whose proof-field hypotheses come out of the
bundle's *own* second component.  The proof component is proved by inverting the
`Prop` member's pre-form at the constructor: index unification forces the proof's
fields to be the constructor's own, so the `Prop` minor's data hypotheses are the
sibling bundles' first components and its proof hypotheses their second.  The
inversion is `Lean.Meta.cases`; the recursive calls are named before it runs so
structural recursion sees them at the top of the alternative rather than under
the equations the inversion introduces.
-/

/-- Where a `Prop` member of the block sits in the recursion. -/
structure PropSlot where
  /-- The `Prop` member's index in the block. -/
  j : Nat
  /-- The position, among its own indices, of the data member it rides in. -/
  pos : Nat
  /-- That data member's index in the block. -/
  data : Nat
  /-- For each index of that data member, which of the `Prop` member's it is. -/
  bound : Array Nat
  deriving Inhabited

/-- The slot of the `Prop` member at block index `j`. -/
def slotOf? (slots : Array PropSlot) (j : Nat) : Option PropSlot := slots.find? (·.j == j)

/-- The slots the bundle of the data member at block index `i` carries. -/
def slotsAt (slots : Array PropSlot) (i : Nat) : Array Nat :=
  (Array.range slots.size).filter (slots[·]!.data == i)

/-- Of a `Prop` member's indices, the ones its slot does not already account for. -/
def PropSlot.freeArgs (s : PropSlot) (args : Array Expr) : Array Expr :=
  (Array.range args.size).filterMap fun z =>
    if z == s.pos || s.bound.contains z then none else some args[z]!

/-- The index arguments of the data member a `Prop` member's principal index is at. -/
def dataIdxArgs (b : Block) (who : Name) (d : Expr) : MetaM (Array Expr) := do
  let some args ← b.withRecTarget? (← inferType d) fun _ _ args => pure (b.idxArgs args)
    | throwError "The index `{d}` of `{who}` is not a member's type"
  return args

/-- Read a slot off every `Prop` member of the block. -/
def propSlots? (b : Block) (ps : Array Expr) : TermElabM (Option (Array PropSlot)) := do
  let mut out : Array PropSlot := #[]
  for j in b.propIdxs do
    let r : Option (Option PropSlot) ←
      forallTelescope (← instantiateForall b.members[j]!.type ps) fun idxs _ => do
        let mut found : Option PropSlot := none
        let mut dataPos : Array Nat := #[]
        for k in *...idxs.size do
          let hit ← b.withRecTarget? (← inferType idxs[k]!) fun ys m args =>
            return (ys.isEmpty, m, b.idxArgs args)
          let some (clean, m, margs) := hit | continue
          if b.members[m]!.isProp then continue
          unless clean do return none
          let mut bound : Array Nat := #[]
          for a in margs do
            let some q := (idxs.extract 0 k).findIdx? (· == a) | return none
            bound := bound.push q
          unless dataPos.all (bound.contains ·) do return none
          dataPos := dataPos.push k
          found := some { j, pos := k, data := m, bound }
        return some found
    let some s? := r | return none
    -- no data index at all: free-standing, and the caller leaves it out
    let some s := s? | continue
    out := out.push s
  -- which member has to be settled before which, read off the constructors
  let mut before : Array (Nat × Nat) := #[]
  for s in out do
    for c in b.members[s.j]!.ctors do
      let kinds := b.fieldKinds c.kinds
      let deps ← forallTelescope (← instantiateForall c.type ps) fun xs concl => do
        let idxa := b.idxArgs concl.getAppArgs
        if h : s.pos < idxa.size then
          let principal := idxa[s.pos]
          let mut acc : Array Nat := #[]
          for k in *...xs.size do
            let .recur mm := kinds[k]! | continue
            if mm == s.j then continue
            let some s' := out.find? (·.j == mm) | continue
            let fp ← b.withRecTarget? (← inferType xs[k]!) fun ys _ args =>
              pure (if ys.isEmpty then (b.idxArgs args)[s'.pos]? else none)
            if fp == some (some principal) then acc := acc.push mm
          return acc
        else return #[]
      for m in deps do
        unless before.contains (m, s.j) do before := before.push (m, s.j)
  let mut sorted : Array PropSlot := #[]
  let mut left := out
  while !left.isEmpty do
    let mut nxt : Array PropSlot := #[]
    for s in left do
      if before.all fun (m, j) => j != s.j || sorted.any (·.j == m) then
        sorted := sorted.push s
      else nxt := nxt.push s
    -- two that each want the other at its own term: no order settles them
    if nxt.size == left.size then return none
    left := nxt
  return some sorted

/--
Re-bind a `Prop` member's index telescope with its data index pinned to `target`
(and that index's own indices to `dIdxs`). -/
partial def withSlotIdxs {α} [Inhabited α] (b : Block) (s : PropSlot) (dIdxs : Array Expr)
    (target targetPre ty : Expr) (q : Nat) (free all pres : Array Expr)
    (k : Array Expr → Array Expr → Array Expr → MetaM α) : MetaM α := do
  match ty with
  | .forallE nm d body bi =>
    if q == s.pos then
      withSlotIdxs b s dIdxs target targetPre (body.instantiate1 target) (q + 1)
        free (all.push target) (pres.push targetPre) k
    else if let some r := s.bound.findIdx? (· == q) then
      let a := dIdxs[r]!
      withSlotIdxs b s dIdxs target targetPre (body.instantiate1 a) (q + 1)
        free (all.push a) (pres.push (← b.preImage a d)) k
    else
      withLocalDecl nm bi d fun x => do
        let px ← b.preImage x d
        withSlotIdxs b s dIdxs target targetPre (body.instantiate1 x) (q + 1)
          (free.push x) (all.push x) (pres.push px) k
  | _ => k free all pres

/-- The conjuncts of a right-associated conjunction of `n` of them. -/
def peelConj (n : Nat) (e : Expr) : Array Expr := Id.run do
  let mut out : Array Expr := #[]
  let mut e := e
  for q in *...n do
    if q + 1 == n then out := out.push e
    else
      out := out.push e.appFn!.appArg!
      e := e.appArg!
  return out

/-- A proof of the conjunction of `pfs`, right-associated as `foldConj` folds it. -/
def conjIntro (pfs : Array Expr) : MetaM Expr := do
  if pfs.isEmpty then return mkConst ``True.intro
  let mut e := pfs.back!
  for q in *...(pfs.size - 1) do
    e ← mkAppM ``And.intro #[pfs[pfs.size - 2 - q]!, e]
  return e

/-- Bind a batch of `let`s at once. -/
partial def withLets {α} [Inhabited α] (names : Array Name) (tys vals : Array Expr)
    (k : Array Expr → MetaM α) : MetaM α := go 0 #[]
where
  go (i : Nat) (acc : Array Expr) : MetaM α := do
    if h : i < tys.size then
      withLetDecl names[i]! tys[i] vals[i]! fun x => go (i + 1) (acc.push x)
    else
      k acc

/-- The recursor's own value at a term of a member's type, as the minors see it. -/
partial def ihOfTerm (b : Block) (ctors : Array (Nat × CtorSpec)) (ctorNameOf : Name → Name)
    (hasIh : FieldKind → Bool) (minors : Array Expr) (ihAt : Array (FVarId × Expr))
    (e : Expr) (bundled : Bool := false) : MetaM Expr := do
  let f := e.getAppFn
  if let .fvar id := f then
    let some (_, ih) := ihAt.find? (·.1 == id)
      | throwError "No induction hypothesis for{indentExpr e}"
    return mkAppN ih e.getAppArgs
  if bundled then
    throwError "The propositions at{indentExpr e}\nwould have to be proved outside the recursion"
  let some n := f.constName? | throwError "No induction hypothesis for{indentExpr e}"
  -- the term comes out of a constructor's *type*, where a constructor the bridge
  -- renames appears under its hidden name
  let some q := ctors.findIdx? fun (_, cs) => cs.name == n || ctorNameOf cs.name == n
    | throwError "No induction hypothesis for{indentExpr e}"
  unless q < minors.size do
    throwError "The minor for `{n}` is not in scope where{indentExpr e}\nis needed"
  let kinds := b.fieldKinds ctors[q]!.2.kinds
  let fields := b.idxArgs e.getAppArgs
  unless fields.size == kinds.size do
    throwError "`{n}` is not fully applied in{indentExpr e}"
  let mut ihs : Array Expr := #[]
  for z in *...kinds.size do
    unless hasIh kinds[z]! do continue
    ihs := ihs.push <| ← forallTelescope (← inferType fields[z]!) fun ys _ => do
      mkLambdaFVars ys (← ihOfTerm b ctors ctorNameOf hasIh minors ihAt (mkAppN fields[z]! ys))
  return mkAppN minors[q]! (fields ++ ihs)

/--
The recursion's own value at a real term `v` of a member's type, for a caller
that is not itself inside the recursion. -/
partial def valueIh (b : Block) (recAuxName : Nat → Name) (lvl : Level)
    (ps motives minors : Array Expr) (v : Expr)
    (answer : Nat → Array Expr → Expr → Expr → Expr → MetaM Expr :=
      fun _ _ _ _ e => pure e) : MetaM Expr := do
  let r? ← b.withRecTarget? (← inferType v) fun _ mm args => do
    let dihs ← (b.ihDrops mm (b.dropArgs mm args)).mapM
      (valueIh b recAuxName lvl ps motives minors · answer)
    let vargs ← b.valArgs mm args
    let p := b.sVal mm vargs v
    let wf := b.sProp mm vargs v
    answer mm (b.idxArgs args) p wf <| mkAppN (mkConst (recAuxName mm) (lvl :: b.lvls))
      (ps ++ motives ++ minors ++ b.idxArgs args ++ dihs ++ #[p, wf])
  let some e := r?
    | throwError "Not a value of a member of the block:{indentExpr v}"
  return e

/--
Add definitions that may call each other, splitting them into the groups that
actually recurse. -/
def addRecGroups (docCtx : LocalContext × LocalInstances)
    (preDefs : Array PreDefinition) : TermElabM Unit := do
  if preDefs.isEmpty then return
  let n := preDefs.size
  let names := preDefs.map (·.declName)
  let direct : Array (Array Bool) := preDefs.map fun d =>
    let used := d.value.getUsedConstants
    names.map (used.contains ·)
  let mut reach := direct
  for k in *...n do
    for i in *...n do
      if reach[i]![k]! then
        let rk := reach[k]!
        reach := reach.modify i fun ri => Id.run do
          let mut ri := ri
          for j in *...n do
            if rk[j]! then ri := ri.set! j true
          return ri
  let mut done : Array Bool := Array.replicate n false
  let mut left := n
  while left > 0 do
    -- the condensation is a DAG, so some component has all its callees added
    let mut picked : Array Nat := #[]
    for i in *...n do
      if done[i]! || !picked.isEmpty then continue
      let scc := (Array.range n).filter fun j =>
        j == i || (reach[i]![j]! && reach[j]![i]!)
      if scc.all fun x => (Array.range n).all fun y =>
          !direct[x]![y]! || scc.contains y || done[y]! then
        picked := scc
    if picked.isEmpty then
      throwError "Cannot order the recursion between{
        indentD (MessageData.joinSep (names.toList.map toMessageData) ", ")}"
    let group := picked.map (preDefs[·]!)
    if picked.size == 1 && !direct[picked[0]!]![picked[0]!]! then
      addAndCompileNonRec docCtx group[0]!
    else
      Structural.structuralRecursion docCtx group
        (group.map fun _ => (none : Option TerminationMeasure))
    for i in picked do
      done := done.set! i true
    left := left - picked.size

/-- The auxiliary recursors over the pre-types, added as one group. -/
def addRecAuxs (docCtx : LocalContext × LocalInstances) (levelParams : List Name)
    (auxs : Array (Name × Expr × Expr)) : TermElabM Unit :=
  addRecGroups docCtx <| auxs.map fun (declName, type, value) =>
    { ref := .missing, kind := .def, levelParams, modifiers := {}, declName,
      binders := .missing, type, value, termination := TerminationHints.none }

/--
Check that no `Prop` constructor pins a field of the data constructor it is
about. -/
def checkPrincipals (b : Block) (ps : Array Expr) (slots : Array PropSlot)
    (ctorNameOf : Name → Name) : MetaM Unit := do
  for s in slots do
    for c in b.members[s.j]!.ctors do
      forallTelescope (← instantiateForall c.type ps) fun xs concl => do
        let idxa := b.idxArgs concl.getAppArgs
        let some principal := idxa[s.pos]? | return
        if principal.isFVar then return
        let mut ok := false
        if let some cn := principal.getAppFn.constName? then
          if b.members.any fun m =>
              m.ctors.any fun cc => cc.name == cn || ctorNameOf cc.name == cn then
            ok := true
            let mut seen : Array Expr := #[]
            for a in b.idxArgs principal.getAppArgs do
              unless a.isFVar && xs.contains a && !seen.contains a do ok := false
              seen := seen.push a
        unless ok do
          throwError "`{c.name}` is a constructor of `{b.members[s.j]!.name}` at{
            indentExpr principal}\nwhich pins a field of `{b.members[s.data]!.name}` \
            rather than naming one.  The recursion over the whole block would then have \
            to compute at that term, which is not one it is recursing on."

/--
Check that the members left out of the recursion are disconnected from the ones
that stay. -/
def checkFreeProps (b : Block) (ps : Array Expr) (free : Array Nat) : MetaM Unit := do
  for i in *...b.size do
    let m := b.members[i]!
    for c in m.ctors do
      let kinds := b.fieldKinds c.kinds
      forallTelescope (← instantiateForall c.type ps) fun xs _ => do
        for k in *...xs.size do
          if kinds[k]! == .plain then continue
          if m.isProp && !(kinds[k]! matches .recur _) then continue
          let some mm ← b.withRecTarget? (← inferType xs[k]!) fun _ mm _ => pure mm | continue
          let bad := if free.contains i then !free.contains mm && b.members[mm]!.isProp
                     else free.contains mm
          if bad then
            throwError "`{c.name}` has a field of type `{b.members[mm]!.name}`, and \
              `{b.members[free[0]!]!.name}` is a `Prop` member no data member indexes.  \
              The recursion over the whole block cannot cover both."

/--
Open member `i`'s pre-type: its indices, the values its well-formedness
predicate is stated at, a hypothesis for each index the pre-type deleted, a
pre-term, and a proof that the pre-term is well-formed. -/
def withPreRec {α} [Inhabited α] (b : Block) (i : Nat) (ps : Array Expr)
    (ihTypeAt : Expr → MetaM Expr)
    (k : Array Expr → Array Expr → Array Expr → Expr → Expr → TermElabM α) : TermElabM α := do
  forallTelescope (← instantiateForall b.members[i]!.type ps) fun idxs _ => do
    let vargs ← b.valArgs i (ps ++ idxs)
    let delDecls : Array (Name × (Array Expr → TermElabM Expr)) :=
      (b.ihDrops i (b.dropIdxs i idxs)).map fun d => (`ih, fun _ => ihTypeAt d)
    withLocalDeclsD delDecls fun delIhs =>
      withLocalDeclD `t (b.preApp i (ps ++ idxs)) fun t0 =>
        withLocalDeclD `w (mkApp (b.wfApp i vargs) t0) fun w =>
          k idxs vargs delIhs t0 w

/--
The auxiliary recursion at member `i`, as a type and a value: everything a
`withPreRec` opened, abstracted over `concl`, with the value one `casesOn` on
the pre-term taking `alts` at the constructors. -/
def recAuxOver (b : Block) (i : Nat) (ps motives minors idxs delIhs : Array Expr)
    (t0 w concl : Expr) (alts : Array Expr) : MetaM (Expr × Expr) := do
  let all := ps ++ motives ++ minors ++ idxs ++ delIhs ++ #[t0, w]
  let dropped := b.dropIdxs i idxs ++ delIhs ++ #[w]
  let inner ← mkForallFVars dropped concl
  let casesMotive ← mkLambdaFVars (b.keptIdxs i idxs ++ #[t0]) inner
  let cases := mkAppN (mkConst (preName b.members[i]!.name ++ `casesOn)
      ((← getLevel inner) :: b.lvls))
    (ps ++ #[casesMotive] ++ b.keptIdxs i idxs ++ #[t0] ++ alts)
  return (implicitPrefix ps.size (← mkForallFVars all concl),
          implicitPrefix ps.size (← mkLambdaFVars all (mkAppN cases dropped)))

/--
`X.rec` for every member of an induction-inductive block, over one set of
motives and minors: see the section header for the shape and why it is one
recursion. -/
def emitGrandRecs (b : Block) (docCtx : LocalContext × LocalInstances) (lp : Name)
    (recNameOf recAuxName : Nat → Name) (ctorNameOf : Name → Name) (bundled : Bool) :
    TermElabM (Array Nat) := do
  let dIdxs := b.dataIdxs
  if dIdxs.isEmpty || b.propIdxs.isEmpty then
    throwError "Not an induction-inductive block"
  -- a deleted index at a proposition gets no hypothesis, and everything here
  -- reads the hypotheses off a list as long as the deleted indices are
  for i in dIdxs do
    let m := b.members[i]!
    if m.dropIhs.size != m.dropped.size then
      throwError "`{m.name}` is indexed by a proposition of the block, which the recursion \
        over the whole of it has no hypothesis to offer about"
  let lvl := Level.param lp
  let ihName (n : Name) : Name := if n.hasMacroScopes then `ih else n.appendAfter "_ih"
  -- everything below is stated in the raw world, where the copies are the types
  -- and anything the bridge will rename goes by its hidden name -- a
  -- constructor whose type mentions a copy, and a proposition indexed by one
  let b := { b with members := b.members.map fun m =>
    { m with ctors := m.ctors.map fun c => { c with type := b.toRaw c.type } } }
  let out ← forallBoundedTelescope b.members[0]!.type b.numParams fun ps _ => do
    let some slots ← propSlots? b ps
      | throwError "No one data index of a `Prop` member settles the rest of them"
    checkPrincipals b ps slots ctorNameOf
    let free := b.propIdxs.filter fun j => (slotOf? slots j).isNone
    if slots.isEmpty then
      throwError "No `Prop` member of this block is indexed by a data member"
    checkFreeProps b ps free
    -- motives and minors come out in the order the block was written, save that
    -- a `Prop` member's motive has to follow the data motive it mentions
    let ord : Array Nat := Id.run do
      let mut out : Array Nat := #[]
      let mut left := (Array.range b.size).filter (!free.contains ·)
      while !left.isEmpty do
        let mut nxt : Array Nat := #[]
        for i in left do
          match slotOf? slots i with
          | some s => if out.contains s.data then out := out.push i else nxt := nxt.push i
          | none => out := out.push i
        if nxt.size == left.size then return out
        left := nxt
      return out
    unless ord.size + free.size == b.size do
      throwError "A `Prop` member is indexed by a member that depends on it"
    let mpos (i : Nat) : Nat := (ord.findIdx? (· == i)).getD 0
    let ctors := b.ctorsOf ord
    let minorPos (n : Name) : Nat := (ctors.findIdx? (·.2.name == n)).getD 0
    -- a field a `Prop` constructor's conclusion forgets has no well-formedness
    -- to be put back at its subtype with, so the recursion stands an arbitrary
    -- element of its type in
    let strayList : Array (Array Nat) ← ctors.mapM fun (i, c) => BridgeCtx.strayFields b i c ps
    let strayAt (n : Name) : Array Nat := strayList[minorPos n]!
    -- this is a recursor over the whole block, one motive per member and one
    -- minor per constructor, so it is named the way Lean names its own: two
    -- members can share a constructor's short name, and a repeated binder is
    -- one `induction .. using` cannot address, so repeats are numbered
    let minorNames : Array Name := Id.run do
      let mut out : Array Name := #[]
      for (_, c) in ctors do
        let base := c.name.getString!
        let mut n := Name.mkSimple base
        let mut k := 0
        while out.contains n do
          k := k + 1
          n := Name.mkSimple s!"{base}_{k}"
        out := out.push n
      return out
    let mnames := motiveNames ord.size
    -- which fields of a data constructor its minor premise gives a hypothesis
    -- about: everything the recursion has a value at, which a plain field is
    -- not
    let hasIh : FieldKind → Bool := fun k => k != .plain
    let motiveDecls : Array (Name × (Array Expr → TermElabM Expr)) := ord.mapIdx fun q i =>
      (mnames[q]!, fun acc => do
        let m := b.members[i]!
        forallTelescope (← instantiateForall m.type ps) fun idxs _ => do
          match slotOf? slots i with
          | some s =>
            let d := idxs[s.pos]!
            let dArgs ← dataIdxArgs b m.name d
            withLocalDeclD (ihName (← d.fvarId!.getUserName))
                (mkAppN acc[mpos s.data]! (dArgs ++ #[d])) fun xih =>
              withLocalDeclD `h (mkAppN (b.memberCst i) (ps ++ idxs)) fun h =>
                mkForallFVars (idxs ++ #[xih, h]) (mkSort Level.zero)
          | none =>
            withLocalDeclD `t (mkAppN (b.memberCst i) (ps ++ idxs)) fun t =>
              mkForallFVars (idxs ++ #[t]) (mkSort lvl))
    withImplicits motiveDecls fun motives => do
      let mut minorDecls : Array (Name × (Array Expr → TermElabM Expr)) := #[]
      for h : q in *...ctors.size do
        let (i, c) := ctors[q]
        minorDecls := minorDecls.push (minorNames[q]!, fun acc => do
          forallTelescope (← b.ctorType c ps) fun xs concl => do
            let kinds := b.fieldKinds c.kinds
            -- a data constructor's proof fields get a hypothesis too, which is
            -- the whole point; a `Prop` constructor has none to give one to, and
            -- a field its conclusion forgets gets none either -- see `strayFields`
            let stray := strayAt c.name
            let ihPos := (Array.range kinds.size).filter fun k =>
              !stray.contains k &&
                if b.members[i]!.isProp then kinds[k]! matches .recur _ else hasIh kinds[k]!
            let mut names : Array Name := #[]
            for k in ihPos do
              names := names.push (ihName (← xs[k]!.fvarId!.getUserName))
            let ihDecls : Array (Name × (Array Expr → TermElabM Expr)) :=
              ihPos.mapIdx fun q k => (names[q]!, fun ihAcc => do
                let ihAt : Array (FVarId × Expr) :=
                  (Array.range ihAcc.size).map fun z => (xs[ihPos[z]!]!.fvarId!, ihAcc[z]!)
                let ty ← inferType xs[k]!
                let r? ← b.withRecTarget? ty fun ys mm args => do
                  let idxa := b.idxArgs args
                  match slotOf? slots mm with
                  | some s =>
                    let ih ← ihOfTerm b ctors ctorNameOf hasIh acc ihAt idxa[s.pos]!
                    mkForallFVars ys (mkAppN motives[mpos mm]! (idxa ++ #[ih, mkAppN xs[k]! ys]))
                  | none =>
                    mkForallFVars ys (mkAppN motives[mpos mm]! (idxa ++ #[mkAppN xs[k]! ys]))
                let some r := r?
                  | throwError "The field `{xs[k]!}` of `{c.name}` is not a member's \
                      type:{indentExpr ty}"
                return r)
            withLocalDeclsD ihDecls fun ihs => do
              let ihAt : Array (FVarId × Expr) :=
                (Array.range ihs.size).map fun z => (xs[ihPos[z]!]!.fvarId!, ihs[z]!)
              let idxa := b.idxArgs concl.getAppArgs
              let head := mkAppN (b.cst (ctorNameOf c.name)) (ps ++ xs)
              match slotOf? slots i with
              | some s =>
                let ih ← ihOfTerm b ctors ctorNameOf hasIh acc ihAt idxa[s.pos]!
                mkForallFVars (xs ++ ihs) (mkAppN motives[mpos i]! (idxa ++ #[ih, head]))
              | none =>
                mkForallFVars (xs ++ ihs) (mkAppN motives[mpos i]! (idxa ++ #[head])))
      withLocalDeclsD minorDecls fun minors => do
        -- The binders a slot's component lives under: whichever of the `Prop`
        -- member's own indices the data member does not fix, and a proof of it
        -- at the pre-type
        let withSlotBinders {α} [Inhabited α] (s : PropSlot) (mIdxs : Array Expr)
            (target p : Expr) (k : Array Expr → Array Expr → Expr → MetaM α) : MetaM α := do
          withSlotIdxs b s mIdxs target p (← instantiateForall b.members[s.j]!.type ps)
            0 #[] #[] #[] fun free all pres =>
              withLocalDeclD `h
                (mkAppN (b.cst (preName b.members[s.j]!.name)) (ps ++ pres)) fun h =>
                  k free all h
        -- the bundle: what the recursion computes at a pre-term
        let bundleType (i : Nat) (mIdxs vargs : Array Expr) (p wf : Expr) : MetaM Expr := do
          let target := b.sMk i vargs p wf
          let cTy := mkAppN motives[mpos i]! (mIdxs ++ #[target])
          withLocalDeclD `c cTy fun c => do
            let mut comps : Array Expr := #[]
            for si in slotsAt slots i do
              let s := slots[si]!
              comps := comps.push <| ←
                withSlotBinders s mIdxs target p fun free all h =>
                  mkForallFVars (free ++ #[h]) (mkAppN motives[mpos s.j]! (all ++ #[c, h]))
            let beta ← mkLambdaFVars #[c] (foldConj comps 0)
            return mkApp2 (mkConst ``PSigma [lvl, Level.zero]) cTy beta
        -- a bundle whose type is already on its binder says what it is itself,
        -- and reading it off is shorter than stating it a second time
        let bunTy (bun : Expr) : MetaM Expr := do whnf (← inferType bun)
        -- the two components of a bundle's type
        let bunParts (bTy : Expr) : MetaM (Expr × Expr) := do
          unless bTy.isAppOfArity ``PSigma 2 && bTy.appArg!.isLambda do
            throwError "The recursion over the whole block wanted a bundle here and \
              found{indentExpr bTy}"
          return (bTy.appFn!.appArg!, bTy.appArg!)
        let bunFst (bTy bun : Expr) : MetaM Expr := do
          let (alpha, beta) ← bunParts bTy
          return mkApp3 (mkConst ``PSigma.fst [lvl, Level.zero]) alpha beta bun
        let bunMk (bTy c props : Expr) : MetaM Expr := do
          let (alpha, beta) ← bunParts bTy
          return mkApp4 (mkConst ``PSigma.mk [lvl, Level.zero]) alpha beta c props
        let slotComp (bTy bun : Expr) (si : Nat) : MetaM Expr := do
          let s := slots[si]!
          let group := slotsAt slots s.data
          let q := (group.findIdx? (· == si)).getD 0
          let (alpha, beta) ← bunParts bTy
          let fst := mkApp3 (mkConst ``PSigma.fst [lvl, Level.zero]) alpha beta bun
          let snd := mkApp3 (mkConst ``PSigma.snd [lvl, Level.zero]) alpha beta bun
          return projConj (peelConj group.size (beta.bindingBody!.instantiate1 fst)) snd q
        -- what the recursion promises at a real value of a data member's type.
        -- A deleted index is handed one of these, since the pre-term the
        -- recursion runs on does not have the index in it to recurse at
        let ihTypeAt (v : Expr) : MetaM Expr := do
          let r? ← b.withRecTarget? (← inferType v) fun _ mm args => do
            let mIdxs := b.idxArgs args
            unless bundled do
              return mkAppN motives[mpos mm]! (mIdxs ++ #[v])
            let vargs ← b.valArgs mm (ps ++ mIdxs)
            bundleType mm mIdxs vargs (b.sVal mm vargs v) (b.sProp mm vargs v)
          let some ty := r?
            | throwError "Not a value of a member of the block:{indentExpr v}"
          return ty
        -- a deleted index's hypothesis read as the motive's value, which is what
        -- it is already unless it is carrying the propositions as well
        let ihValOf (ih : Expr) : MetaM Expr := do
          if bundled then return ← bunFst (← bunTy ih) ih else return ih
        -- an index of a `Prop` member, back at the subtypes
        let toRealIdxs (delS : Array (Expr × Expr × Expr)) (jj : Nat) (pidxs : Array Expr)
            (parts : Array (Expr × Expr)) : MetaM (Array Expr) := do
          let mut rty ← instantiateForall b.members[jj]!.type ps
          -- the same telescope walked at the pre-world arguments instead, which
          -- is the *sub* reading: a data index that deleted indices of its own
          -- is the only place they are still named, and `X._wf` wants them
          let mut sty := rty
          let mut out : Array Expr := #[]
          for z in *...pidxs.size do
            let .forallE _ _ rbody _ := rty
              | throwError "`{b.members[jj]!.name}` has too few indices"
            let .forallE _ sd sbody _ := sty
              | throwError "`{b.members[jj]!.name}` has too few indices"
            let isData ← b.withRecTarget? sd fun ys m2 _ =>
              pure (ys.isEmpty && !b.members[m2]!.isProp)
            let v ← if let some (_, dv, _) := delS.find? (·.1 == pidxs[z]!) then
                pure dv
              else if isData == some true then
                let pf ← BridgeCtx.findPart parts (← b.wfOfSub pidxs[z]! sd)
                b.withRecTarget sd fun _ m2 args => pure (b.sMk m2 args pidxs[z]! pf)
              else pure pidxs[z]!
            out := out.push v
            rty := rbody.instantiate1 v
            sty := sbody.instantiate1 pidxs[z]!
          return out
        -- One alternative of the inversion that proves a bundle's proof
        -- component.  A `Prop` constructor's data field need not be a *strict*
        -- subterm of the pre-term recursed at: `WF.intro (l) (t) (h : WFWith t
        -- l)` holds the pre-term itself
        let fillAlt (imgs : Array (Option Expr)) (recPos : Array Nat) (buns : Array Expr)
            (delAt : Array (Expr × Expr × Expr))
            (wc selfPre self : Expr) (selfProps : Array (Option Expr))
            (sg : CasesSubgoal) : MetaM Unit := sg.mvarId.withContext do
          let some ctorName := sg.ctorName | throwError "A sparse alternative in the inversion"
          let some (_, cc) := (Array.range b.size).findSome? fun z =>
              (b.members[z]!.ctors.find? fun cc => b.preOf cc.name == ctorName).map ((z, ·))
            | throwError "No constructor of the block behind `{ctorName}`"
          let kinds := b.fieldKinds cc.kinds
          let fields := sg.fields
          unless fields.size == kinds.size do
            throwError "The inversion gave {fields.size} fields for `{cc.name}`"
          let parts ← BridgeCtx.wfParts (sg.subst.apply wc)
          let strayHere := strayAt cc.name
          let delS := delAt.map fun (pre, d, ih) => (sg.subst.apply pre, d, ih)
          -- the fields line up one for one with the constructor's own, which is
          -- what the count above has just made sure of
          let subTys ← b.subFieldTys cc ps fields
          let bunAt (e : Expr) : Option Nat := Id.run do
            for q in *...recPos.size do
              if e.getAppFn == sg.subst.apply (imgs[recPos[q]!]!).get! then return some q
            return none
          let bunOf (q : Nat) (args : Array Expr) : Expr := mkAppN (sg.subst.apply buns[q]!) args
          let selfPreS := sg.subst.apply selfPre
          let mut vals : Array Expr := #[]
          let mut ihs : Array Expr := #[]
          for z in *...kinds.size do
            let f := fields[z]!
            let fty ← inferType f
            match kinds[z]! with
            | .plain | .erased => vals := vals.push f
            | .deleted .. => throwError "A deleted index reached the grand recursor"
            | .recur mm =>
              if b.members[mm]!.isProp then
                let some si := slots.findIdx? (·.j == mm)
                  | throwError "No slot for `{b.members[mm]!.name}`"
                let s := slots[si]!
                vals := vals.push f
                ihs := ihs.push <| ← b.withPreTarget fty fun zs _ pargs => do
                  let pidxs := b.idxArgs pargs
                  let principal := pidxs[s.pos]!
                  let comp ←
                    if principal == selfPreS then
                      match selfProps[si]! with
                      | some e => pure (sg.subst.apply e)
                      | none =>
                        throwError "`{b.members[s.j]!.name}` is wanted at the very term it is \
                          being proved at, and is not settled yet"
                    else if let some (_, _, dih) := delS.find? (·.1 == principal) then
                      -- the proof is about an index the constructor being
                      -- recursed at deleted, so what stands for a recursive call
                      -- is the hypothesis that index arrived under -- and only
                      -- the bundled reading of that hypothesis has one in it
                      unless bundled do
                        throwError "`{cc.name}` asks for `{b.members[s.j]!.name}` at{
                          indentExpr principal}\nwhich is an index the pre-type dropped, and the \
                          hypothesis handed in about a dropped index carries its value alone"
                      slotComp (← bunTy dih) dih si
                    else do
                      let some q := bunAt principal
                        | throwError "No recursive call for{indentExpr principal}"
                      let bun := bunOf q principal.getAppArgs
                      slotComp (← bunTy bun) bun si
                  let reals ← toRealIdxs delS mm pidxs parts
                  mkLambdaFVars zs (mkAppN comp (s.freeArgs reals ++ #[mkAppN f zs]))
              else if let some (_, d, dih) := delS.find? (·.1 == f) then
                -- the field is the deleted index itself, so it is already real
                -- and already has its hypothesis; there is no call to find it at
                if strayHere.contains z then
                  throwError "`{cc.name}` has a field `{f}` that the minor premise was \
                    stated without a hypothesis for, and that the recursion has one for \
                    after all"
                vals := vals.push d
                ihs := ihs.push (← ihValOf dih)
              else if strayHere.contains z then
                -- the conclusion forgets the field, so there is no putting it back
                -- at its subtype and no hypothesis to offer at it; the minor was
                -- stated without one, and what goes in its place is sound because
                -- the minor is building a proof
                vals := vals.push <| ←
                  BridgeCtx.rebuiltField b cc parts f subTys[z]! (strayOk := true)
              else
                let pf ← BridgeCtx.dataFieldPart b cc parts f subTys[z]!
                -- the *sub* reading, which is the one that still names an index
                -- the pre-type deleted -- and `X._wf` is stated at all of them
                vals := vals.push <| ← b.withRecTarget subTys[z]! fun zs m2 args =>
                  mkLambdaFVars zs (b.sMk m2 args (mkAppN f zs) (mkAppN pf zs))
                ihs := ihs.push <| ← b.withRecTarget subTys[z]! fun zs _ _ => do
                  if f == selfPreS then
                    return ← mkLambdaFVars zs (sg.subst.apply self)
                  let some q := bunAt f | throwError "No recursive call for{indentExpr f}"
                  let bun := bunOf q zs
                  mkLambdaFVars zs (← bunFst (← bunTy bun) bun)
          sg.mvarId.assign (mkAppN (sg.subst.apply minors[minorPos cc.name]!) (vals ++ ihs))
        -- one alternative of the recursion itself
        let altFor (i : Nat) (c : CtorSpec) : MetaM Expr :=
          b.withAlt i c ps fun a => do
                let { kinds, xs, olds, news, imgs, subTys, cIdxs, realIdxs, head, wc, conjs,
                      real, recPos, dels, .. } := a
                -- a deleted index arrives with a hypothesis of its own, which is
                -- what a recursive call standing under it will be handed
                let dDecls : Array (Name × (Array Expr → MetaM Expr)) :=
                  dels.map fun d => (`ih, fun _ => ihTypeAt d)
                withLocalDeclsD dDecls fun dIhs => do
                -- a deleted index in all three readings at once: the pre-image
                -- an inversion's field is substituted to, the real value a minor
                -- premise wants, and the hypothesis about it
                let delAt : Array (Expr × Expr × Expr) ← dels.mapIdxM fun q d => do
                  return ((← b.preImage d (← inferType d)), d, dIhs[q]!)
                -- a recursive field read in both worlds at once
                let withField {α} [Inhabited α] (k : Nat)
                    (f : Array Expr → Nat → Array Expr → Array Expr → MetaM α) : MetaM α := do
                  let r? ← b.withRecTarget? subTys[k]! fun ys mm pargs => do
                    let rConcl ← instantiateForall (← inferType xs[k]!) ys
                    f ys mm pargs rConcl.getAppArgs
                  let some e := r?
                    | throwError "The field `{xs[k]!}` of `{c.name}` is not a member's type"
                  return e
                -- the recursive calls, named before anything else, so that
                -- structural recursion meets them at the top of the alternative
                let mut ihAt : Array (FVarId × Expr) :=
                  dels.mapIdx fun q d => (d.fvarId!, dIhs[q]!)
                let mut bnames : Array Name := #[]
                let mut btys : Array Expr := #[]
                let mut bvals : Array Expr := #[]
                for q in *...recPos.size do
                  let k := recPos[q]!
                  let y := (imgs[k]!).get!
                  let pr := projConj conjs wc q
                  bnames := bnames.push (ihName (← xs[k]!.fvarId!.getUserName))
                  let (bty, bval, ih) ← withField k fun ys mm pargs rargs => do
                    let bTy ← bundleType mm (b.idxArgs rargs) pargs
                      (mkAppN y ys) (mkAppN pr ys)
                    let dihs ← (b.dropArgs mm rargs).mapM
                      (ihOfTerm b ctors ctorNameOf hasIh minors ihAt · bundled)
                    let call := mkAppN (mkConst (recAuxName mm) (lvl :: b.lvls))
                      (ps ++ motives ++ minors ++ b.idxArgs rargs ++ dihs ++
                        #[mkAppN y ys, mkAppN pr ys])
                    -- what a field stands for wherever a deleted index names it,
                    -- which is the same reading its own hypothesis arrives in
                    let ihVal ← if bundled then pure call else bunFst bTy call
                    return (← mkForallFVars ys bTy, ← mkLambdaFVars ys call,
                      ← mkLambdaFVars ys ihVal)
                  btys := btys.push bty
                  bvals := bvals.push bval
                  ihAt := ihAt.push (xs[k]!.fvarId!, ih)
                -- the calls name the real fields, which the alternative does not
                -- bind; a deleted one is its own real self, so it survives
                let atReal (e : Expr) : Expr := e.replaceFVars xs real
                withLets bnames (btys.map atReal) (bvals.map atReal) fun buns => do
                  let mut ihs : Array Expr := #[]
                  for k in *...xs.size do
                    match kinds[k]! with
                    | .plain => pure ()
                    -- the alternative binds the index and not the field, so the
                    -- hypothesis about it is the one the recursion arrived with
                    -- rather than one of the bundles just built
                    | .deleted .. =>
                      let some q := dels.findIdx? (· == xs[k]!)
                        | throwError "The deleted field `{xs[k]!}` of `{c.name}` is not one \
                            of the alternative's indices"
                      ihs := ihs.push (← ihValOf dIhs[q]!)
                    | .recur _ =>
                      let q := (recPos.findIdx? (· == k)).getD 0
                      ihs := ihs.push <| ← b.withRecTarget subTys[k]! fun ys _ _ => do
                        let bun := mkAppN buns[q]! ys
                        mkLambdaFVars ys (← bunFst (← bunTy bun) bun)
                    | .erased =>
                      let ty ← inferType xs[k]!
                      let r? ← b.withRecTarget? ty fun ys jj rargs => do
                        let some si := slots.findIdx? (·.j == jj)
                          | throwError "No slot for `{b.members[jj]!.name}`"
                        let s := slots[si]!
                        let ridxs := b.idxArgs rargs
                        let principal := ridxs[s.pos]!
                        let some k' := (Array.range xs.size).find? fun z =>
                            principal.getAppFn == xs[z]!
                          | throwError "The proof field `{xs[k]!}` of `{c.name}` is not \
                              about a recursive field"
                        let some q := recPos.findIdx? (· == k')
                          | throwError "The proof field `{xs[k]!}` of `{c.name}` is not \
                              about a recursive field"
                        let zs := principal.getAppArgs.map (·.replaceFVars olds news)
                        let bun := mkAppN buns[q]! zs
                        let comp ← slotComp (← bunTy bun) bun si
                        let fargs := s.freeArgs (ridxs.map (·.replaceFVars xs real))
                        mkLambdaFVars ys (mkAppN comp (fargs ++ #[mkAppN real[k]! ys]))
                      let some e := r?
                        | throwError "The proof field `{xs[k]!}` of `{c.name}` is not a \
                            `Prop` member's type:{indentExpr ty}"
                      ihs := ihs.push e
                  let cVal := mkAppN minors[minorPos c.name]! (real ++ ihs)
                  -- the bundle is built at whichever reading of the indices it
                  -- is asked for, because an index the constructor *builds* is
                  -- one the alternative was handed a binder for instead: what
                  -- comes out is the constructor's reading and what is owed is
                  -- the binder's, and the transport carries the whole of it
                  mkLambdaFVars (keptImages kinds imgs ++ dels ++ dIhs ++ #[wc])
                    (← b.transportBuilt i a
                      (fun mIdxs vargs w => bundleType i mIdxs vargs head w)
                      fun mIdxs vargs w => do
                        -- the slots are settled in block order, so a `Prop`
                        -- member that appears in a later one's constructor is
                        -- ready by then
                        let mut props : Array Expr := #[]
                        let mut selfProps : Array (Option Expr) :=
                          (List.replicate slots.size none).toArray
                        for si in slotsAt slots i do
                          let s := slots[si]!
                          let target := b.sMk i vargs head w
                          let sp := selfProps
                          let pr ← withSlotBinders s mIdxs target head
                            fun free all h => do
                              let goal := mkAppN motives[mpos s.j]! (all ++ #[cVal, h])
                              let mv ← mkFreshExprSyntheticOpaqueMVar goal
                              for sg in ← mv.mvarId!.cases h.fvarId! do
                                fillAlt imgs recPos buns delAt wc head cVal sp sg
                              mkLambdaFVars (free ++ #[h]) (← instantiateMVars mv)
                          props := props.push pr
                          selfProps := selfProps.set! si (some pr)
                        let bTy ← bundleType i mIdxs vargs head w
                        mkLetFVars buns (← bunMk bTy cVal (← conjIntro props)))
        -- the recursion, one mutual group over the data pre-types
        let mut auxs : Array (Expr × Expr) := #[]
        for i in dIdxs do
          auxs := auxs.push <| ← withPreRec b i ps ihTypeAt fun idxs vargs delIhs t0 w => do
            let mut alts : Array Expr := #[]
            for c in b.members[i]!.ctors do
              alts := alts.push (← altFor i c)
            recAuxOver b i ps motives minors idxs delIhs t0 w
              (← bundleType i idxs vargs t0 w) alts
        -- both kinds of `X.rec` are stated over the same prefix, and everything
        -- ahead of the target is left implicit for `induction .. using`
        let sig (idxs : Array Expr) (t goal val : Expr) : MetaM (Expr × Expr) := do
          let all := ps ++ motives ++ minors ++ idxs ++ #[t]
          let hide := hideRecBinders ps.size (motives.size + minors.size) idxs.size
          return (hide (← mkForallFVars all goal), hide (← mkLambdaFVars all val))
        -- `X.rec` is not inside the recursion, so the hypothesis at a deleted
        -- index is a recursion of its own, at that index -- and what it returns
        -- is a bundle, of which the motive's value is the first component
        let bunAnswer (mm : Nat) (mIdxs : Array Expr) (p wf e : Expr) : MetaM Expr := do
          if bundled then return e
          bunFst (← bundleType mm mIdxs (← b.valArgs mm (ps ++ mIdxs)) p wf) e
        let delIhsAt (i : Nat) (idxs : Array Expr) : MetaM (Array Expr) :=
          (b.dropIdxs i idxs).mapM
            (valueIh b recAuxName lvl ps motives minors · bunAnswer)
        -- `X.rec` for the data members, then for the `Prop` ones
        let mut recs : Array (Name × Expr × Expr × Bool) := #[]
        for i in dIdxs do
          let m := b.members[i]!
          recs := recs.push <| ← forallTelescope (← instantiateForall m.type ps) fun idxs _ =>
            withLocalDeclD `t (mkAppN (b.memberCst i) (ps ++ idxs)) fun t => do
              let vargs ← b.valArgs i (ps ++ idxs)
              let tv := b.sVal i vargs t
              let tp := b.sProp i vargs t
              let bTy ← bundleType i idxs vargs tv tp
              let bun := mkAppN (mkConst (recAuxName i) (lvl :: b.lvls))
                (ps ++ motives ++ minors ++ idxs ++ (← delIhsAt i idxs) ++ #[tv, tp])
              let (ty, val) ← sig idxs t (mkAppN motives[mpos i]! (idxs ++ #[t]))
                (← bunFst bTy bun)
              return (recNameOf i, ty, val, true)
        for si in *...slots.size do
          let s := slots[si]!
          let m := b.members[s.j]!
          recs := recs.push <| ← forallTelescope (← instantiateForall m.type ps) fun idxs _ =>
            withLocalDeclD `h (mkAppN (b.memberCst s.j) (ps ++ idxs)) fun h => do
              let d := idxs[s.pos]!
              let dArgs ← dataIdxArgs b m.name d
              let vargs ← b.valArgs s.data (ps ++ dArgs)
              let dv := b.sVal s.data vargs d
              let dp := b.sProp s.data vargs d
              let bTy ← bundleType s.data dArgs vargs dv dp
              let bun := mkAppN (mkConst (recAuxName s.data) (lvl :: b.lvls))
                (ps ++ motives ++ minors ++ dArgs ++ (← delIhsAt s.data dArgs) ++ #[dv, dp])
              let xih := mkAppN (mkConst (recNameOf s.data) (lvl :: b.lvls))
                (ps ++ motives ++ minors ++ dArgs ++ #[d])
              let comp ← slotComp bTy bun si
              let (ty, val) ← sig idxs h (mkAppN motives[mpos s.j]! (idxs ++ #[xih, h]))
                (mkAppN comp (s.freeArgs idxs ++ #[h]))
              return (recNameOf s.j, ty, val, false)
        return (auxs, recs, free)
  let (auxs, recs, free) := out
  addRecAuxs docCtx (lp :: b.us) <| auxs.mapIdx fun q (ty, val) =>
    (recAuxName dIdxs[q]!, ty, val)
  for (n, ty, val, compile) in recs do
    addDef n (lp :: b.us) (← instantiateMVars ty) (← instantiateMVars val) (compile := compile)
    markElabAsElim n
  return free

/-- A data member's recursor, in the two forms step 8 builds it in. -/
structure SplitRec where
  /-- The auxiliary recursor's type, over the pre-type. -/
  auxType : Expr
  /-- The auxiliary recursor's value. -/
  auxValue : Expr
  /-- The recursor's type, over the member's own type. -/
  type : Expr
  /-- The recursor's value, an application of the auxiliary. -/
  value : Expr
  deriving Inhabited

/-! ## Emitting the declarations -/

/-- The data members' pre-types, as real declarations. -/
private def emitPreData (p : Plan) : TermElabM Nat := do
  let b := p.block
  unless p.preIsHeterogeneous do
    addInd b.us b.numParams p.preDataInds
    return 1
  let names := p.preDataInds.map (·.name)
  let decls : Array (Name × (Array Expr → TermElabM Expr)) :=
    p.preDataInds.map fun ind => (`x, fun _ => pure ind.type)
  try
    withLocalDeclsD decls fun fvars => do
      -- `Input` carries the members as free variables where an `InductiveType`
      -- carries them as constants that are not in the environment yet
      let toFVar (e : Expr) : Expr :=
        e.replace fun
          | .const n _ => (names.findIdx? (· == n)).map (fvars[·]!)
          | _          => none
      MultiuniverseInductive.lower
        { levelParams := b.us
          numVars     := 0
          numParams   := b.numParams
          memberFVars := fvars
          memberNames := names
          memberTypes := p.preDataInds.map (·.type)
          ctorNames   := p.preDataInds.map fun ind => (ind.ctors.map (·.name)).toArray
          ctorTypes   := p.preDataInds.map fun ind =>
                           (ind.ctors.map fun c => toFVar c.type).toArray }
  catch ex => owning do
    -- name the pair that disagreed before anything else: which two members they
    -- are is the first thing the reader needs, and the inner error is about the
    -- pre-block, whose names nobody wrote the universe a member ends in, read
    -- off its *pre*-type
    let levelOf (q : Nat) : TermElabM Level :=
      forallTelescope p.preDataInds[q]!.type fun _ body => do
        let .sort l := ← whnf body | return .zero
        instantiateLevelMVars l
    let l0 ← levelOf 0
    -- the block is not necessarily induction-inductive: this path is also a
    -- retry on an ordinary heterogeneous block whose denesting brought it here,
    -- so say "block" and let the members do the identifying
    let mut which := m!"The data members of this block live in different universes"
    for q in *...b.dataIdxs.size do
      let l ← levelOf q
      unless l == l0 do
        let s0 := toString (← ppExpr (mkSort l0))
        let s := toString (← ppExpr (mkSort l))
        which := m!"The data members `{b.members[b.dataIdxs[0]!]!.name}` and \
          `{b.members[b.dataIdxs[q]!]!.name}` live in different universes, `{s0}` and `{s}`"
        break
    throwError "{which}.  Lowering the erased pre-block into ordinary inductives is what \
      lifts the kernel's same-universe rule, and here it did not go \
      through:{indentD ex.toMessageData}\n\n\
      Note: What the lowering lifts is the rule that the *members* of a mutual block agree \
      about their universe.  The two rules underneath it stand: members that recurse into \
      one another have to agree anyway -- an edge puts one universe at or below the other, \
      so a cycle makes them equal -- and a field still has to fit inside the member it \
      belongs to.  `X._pre` above is the erased form of `X`"
  let info ← getConstInfo (names[0]! ++ `mutualRec)
  return info.levelParams.length - b.us.length

/--
Repeat the motive universe in `e`'s pre-recursor heads until there are `k` of
them. -/
private def widenPreRecLevels (p : Plan) (k : Nat) (e : Expr) : Expr :=
  if k == 1 then e else
    let heads := p.preDataInds.map (·.name ++ `mutualRec)
    e.replace fun
      | .const n us =>
        if heads.contains n then
          some (.const n (List.replicate k us.head! ++ us.drop 1))
        else none
      | _ => none

/-! ## Injectivity

A data member is a `def` onto a subtype and its constructors are `def`s, so
nothing hands them the `inj`/`injEq` pair a real inductive's constructors get.
The statements are mainline's, built by `mkInjectiveTheoremTypeCore?` off a
`ConstructorVal` assembled from the `def`; only the proofs are ours.  Forwards,
the equation is pushed through the wrapper's `.val`, where reduction takes the
two constructors down to the pre-world's own and `injection` splits them; each
equation that yields is a field's outright or a wrapper's `ext` away from one,
and substituting them in turn makes the later ones homogeneous.  Backwards, the
components are substituted and the two sides are the same term.
-/

/-- The conjuncts of a right-associated `And`, or the whole of `e` if it is not one. -/
private partial def conjuncts (e : Expr) : Array Expr :=
  if e.isAppOfArity ``And 2 then #[e.appFn!.appArg!] ++ conjuncts e.appArg!
  else #[e]

/--
How many equations `injection` yields at `pre`, an application of a pre-world
constructor: one per field, less the proofs, which proof irrelevance settles
without an equation of their own. -/
private def preEqCount (pre : Expr) : MetaM Nat := do
  let some n := pre.getAppFn.constName? | return 0
  let cv ← getConstInfoCtor n
  forallBoundedTelescope cv.type cv.numParams fun _ rest =>
    forallTelescope rest fun fs _ => do
      let mut k := 0
      for f in fs do
        unless ← isProp (← inferType f) do k := k + 1
      return k

/-- `X.c.inj` and `X.c.injEq` for one constructor of a data member. -/
def addInjEqs (b : Block) (ofInjs : Array Name) (i : Nat) (c : CtorSpec) :
    TermElabM Unit := do
  let info ← getConstInfo c.name
  let arity ← forallTelescope info.type fun xs _ => pure xs.size
  let cv : ConstructorVal :=
    { name := c.name, levelParams := info.levelParams, type := info.type,
      induct := b.members[i]!.name, cidx := 0, numParams := b.numParams,
      numFields := arity - b.numParams, isUnsafe := false }
  let some eqTy ← mkInjectiveTheoremTypeCore? cv true | return
  let some injTy ← mkInjectiveTheoremTypeCore? cv false | return
  -- the binders the two statements share: the parameters, the fields, and a
  -- second copy of every field that is not shared
  let nBinders ← forallTelescope eqTy fun xs _ => pure xs.size
  let us := info.levelParams.map Level.param
  let hH := mkIdent `mumiH
  let hV := mkIdent `mumiV
  let hC := mkIdent `mumiC
  let qName (k : Nat) := mkIdent (Name.mkSimple s!"mumiQ{k}")
  let injName := mkInjectiveTheoremNameFor c.name
  let injVal ← forallBoundedTelescope injTy nBinders fun xs body => do
    let lhs := body.bindingDomain!.appFn!.appArg!
    let sub ← whnf (← inferType lhs)
    let some (sn, sus, sargs) := subOf? sub
      | throwError "`{c.name}` does not build a wrapper, so `injection` has nothing to split"
    let pre ← whnf (mkAppN (mkConst (sn ++ `val) sus) (sargs.push lhs))
    let nEq ← preEqCount pre
    if nEq == 0 then throwError "`{c.name}` reduces to no pre-world constructor"
    let qs : TSyntaxArray [`ident, ``Lean.Parser.Term.hole] :=
      (Array.range nEq).map fun k => ⟨(qName k).raw⟩
    -- an equation about a field of the subtype has to be lifted before it can
    -- be substituted, one about a field at a denested copy has to be read back
    -- through that copy, and one about a field a shared one's type mentions is
    -- heterogeneous until the substitutions before it have run
    let mut rest : Array (TSyntax `tactic) := #[]
    for k in *...nEq do
      let q := qName k
      let mut lifted : Array Term := #[]
      for e in #[← `(term| $q:ident), ← `(term| eq_of_heq $q)] do
        for x in b.dataIdxs do
          let ext ← `(term| $(mkIdent (subName b.members[x]!.name ++ `ext)) $e)
          lifted := lifted.push ext
          for n in ofInjs do
            lifted := lifted.push (← `(term| $(mkIdent n) $ext))
      lifted := lifted.push (← `(term| eq_of_heq $q))
      let alts ← lifted.mapM fun e => do
        let s : Array (TSyntax `tactic) :=
          #[← `(tactic| have mumiE := $e), ← `(tactic| subst mumiE)]
        `(Lean.Parser.Tactic.tacticSeq| $[$s]*)
      rest := rest.push (← `(tactic| first | subst $q $[| $alts]* | skip))
    let comps := conjuncts (body.bindingBody!.instantiate1 lhs)
    let terms ← comps.mapM fun t =>
      if t.isAppOf ``HEq then `(term| HEq.rfl) else `(term| rfl)
    rest := rest.push <| ←
      match terms with
      | #[t] => `(tactic| exact $t)
      | _ => `(tactic| exact ⟨$terms,*⟩)
    -- `injection` substitutes what it can as it goes, so on a constructor with
    -- one field to compare it has already answered the question and there is
    -- nothing left to do -- hence `all_goals`, which is a no-op then
    let steps : Array (TSyntax `tactic) := #[
      ← `(tactic| intro $hH:ident),
      ← `(tactic| have $hV:ident := congrArg $(mkIdent (sn ++ `val)) $hH),
      ← `(tactic| injection $hV with $qs*),
      ← `(tactic| all_goals $[$rest]*)]
    mkLambdaFVars xs (← proveBy body (← `(Lean.Parser.Tactic.tacticSeq| $[$steps]*)))
  addDecl (.thmDecl { name := injName, levelParams := info.levelParams,
                      type := ← instantiateMVars injTy, value := ← instantiateMVars injVal })
  let eqName := mkInjectiveEqTheoremNameFor c.name
  let eqVal ← forallTelescope eqTy fun xs goal => do
    let comps := conjuncts goal.appArg!
    -- the conjunction is taken apart by projection rather than by a pattern,
    -- since an `rfl` pattern written here is one this quotation invented and
    -- `rcases` would take it for a name to bind
    let mut bwdSteps : Array (TSyntax `tactic) := #[← `(tactic| intro $hC:ident)]
    for k in *...comps.size do
      let mut t : Term := hC
      for _ in *...k do t ← `($t.2)
      if k + 1 != comps.size then t ← `($t.1)
      bwdSteps := bwdSteps.push (← `(tactic| have $(qName k):ident := $t))
    for k in *...comps.size do
      bwdSteps := bwdSteps.push <| ←
        `(tactic| first | subst $(qName k) | cases $(qName k):term)
    bwdSteps := bwdSteps.push (← `(tactic| rfl))
    let bwd ← proveBy (← mkArrow goal.appArg! goal.appFn!.appArg!)
      (← `(Lean.Parser.Tactic.tacticSeq| $[$bwdSteps]*))
    mkLambdaFVars xs (← mkAppM ``Eq.propIntro #[mkAppN (mkConst injName us) xs, bwd])
  addDecl (.thmDecl { name := eqName, levelParams := info.levelParams,
                      type := ← instantiateMVars eqTy, value := ← instantiateMVars eqVal })
  addSimpTheorem (ext := simpExtension) eqName (post := true) (inv := false)
    AttributeKind.global (prio := eval_prio default)

/-! ## Disjointness

Two different constructors of one data member build different terms, and `simp`
will not find that out by itself: what makes it true is a `noConfusion` in the
pre-world, and core's `reduceCtorEq` never fires on a `def`.  Pairs of
constructors are quadratically many, so this is one simproc for the whole library
rather than a lemma each.  It pushes the equation through the wrapper's `.val`,
where reduction takes the two sides down to two different pre-world constructors,
and hands what comes back to `noConfusion` -- so the pre-world name occurs in the
proof term and in nothing stated.
-/

/--
`(X.c₁ .. = X.c₂ ..) = False`, for two different constructors of a data member
of an induction-inductive block. -/
simproc [simp] ctorNoConfusion (_ = _) := fun e => do
  let some (_, lhs, rhs) := e.eq? | return .continue
  let some c₁ := lhs.getAppFn.constName? | return .continue
  let some c₂ := rhs.getAppFn.constName? | return .continue
  if c₁ == c₂ then return .continue
  let mem := c₁.getPrefix
  if mem != c₂.getPrefix then return .continue
  -- `preName` spelled out, since a simproc is `meta` code and may not call it
  unless (← getEnv).contains (mem ++ `_pre.noConfusion) do return .continue
  -- a member and its constructors are plain `def`s, so nothing below reduces at
  -- the transparency `simp` calls a simproc under
  withDefault do
  try
    let sub ← whnf (← inferType lhs)
    -- `subOf?` spelled out, for the reason `preName` is
    let .const sn@(.str _ "_sub") sus := sub.getAppFn | return .continue
    let val := mkAppN (mkConst (sn ++ `val) sus) sub.getAppArgs
    let prf ← withLocalDeclD `h (← mkEq lhs rhs) fun h => do
      let no ← mkNoConfusion (mkConst ``False) (← mkCongrArg val h)
      unless (← inferType no).isConstOf ``False do
        throwError "`{c₁}` and `{c₂}` are not two constructors apart"
      mkLambdaFVars #[h] no
    return .done { expr := mkConst ``False, proof? := ← mkAppM ``eq_false #[prf] }
  catch _ =>
    return .continue

/--
The minor premise a peeled constructor takes in a widened recursor: its fields,
then one hypothesis per field at a member of the block, then the motive at what
the constructor built. -/
private def peeledMinorType (numParams : Nat) (memberAt : Name → Option Nat)
    (motives : Array Expr) (us : List Level) (ps : Array Expr) (motive : Expr)
    (c : Constructor) : TermElabM Expr := do
  forallTelescope (← instantiateForall c.type ps) fun xs concl => do
    let mut ihs : Array (Name × (Array Expr → TermElabM Expr)) := #[]
    for x in xs do
      -- an infinitary field promises the motive at each of its results, so the
      -- field's own telescope leads the hypothesis
      let ih? ← forallTelescope (← inferType x) fun ys res => do
        let some n := res.getAppFn.constName? | return (none : Option Expr)
        let some o := memberAt n | return none
        let args := res.getAppArgs
        return some <| ← mkForallFVars ys
          (mkAppN motives[o]! (args.extract numParams args.size ++ #[mkAppN x ys]))
      if let some ih := ih? then ihs := ihs.push (`ih, fun _ => pure ih)
    withLocalDeclsD ihs fun ihs => do
      let args := concl.getAppArgs
      mkForallFVars (xs ++ ihs) <| mkAppN motive
        (args.extract numParams args.size ++ #[mkAppN (mkConst c.name us) (ps ++ xs)])

/--
The minor the kernel's recursor over a peeled member wants, out of the one a
recursion over the whole block offers. -/
private def selfMinorValue (numParams : Nat) (memberAt : Name → Option Nat)
    (pubRec : Nat → Name) (elimLvls : List Level) (covered : Array Nat)
    (motives minors : Array Expr) (ps : Array Expr)
    (minor : Expr) (c : Constructor) (selfCall? : Option Expr := none) :
    TermElabM Expr := do
  forallTelescope (← instantiateForall c.type ps) fun xs _ => do
    -- one pass over the fields: a field at the member itself is a hypothesis the
    -- kernel's recursion will hand over, and a field at any other member is one
    -- this recursor works out for itself
    let mut kinds : Array (Option (Expr ⊕ Expr)) := #[]
    for x in xs do
      kinds := kinds.push <| ← forallTelescope (← inferType x) fun ys res => do
        let some n := res.getAppFn.constName? | return (none : Option (Expr ⊕ Expr))
        let some o := memberAt n | return none
        let args := res.getAppArgs
        let idxs := args.extract numParams args.size
        if covered.contains o then
          match selfCall? with
          | some h =>
            return some (.inr (← mkLambdaFVars ys (mkAppN h (idxs ++ #[mkAppN x ys]))))
          | none =>
            return some (.inl (← mkForallFVars ys (mkAppN motives[o]! (idxs ++ #[mkAppN x ys]))))
        else
          return some (.inr (← mkLambdaFVars ys (mkAppN (mkConst (pubRec o) elimLvls)
            (ps ++ motives ++ minors ++ idxs ++ #[mkAppN x ys]))))
    let selfDecls : Array (Name × (Array Expr → TermElabM Expr)) :=
      kinds.filterMap fun
        | some (.inl t) => some (`ih, fun _ => pure t)
        | _ => none
    withLocalDeclsD selfDecls fun selfIHs => do
      let mut ihs : Array Expr := #[]
      let mut taken := 0
      for k in kinds do
        match k with
        | some (.inl _) => ihs := ihs.push selfIHs[taken]!; taken := taken + 1
        | some (.inr v) => ihs := ihs.push v
        | none => pure ()
      mkLambdaFVars (xs ++ selfIHs) (mkAppN minor (xs ++ ihs))

/--
Put the members that left the block back into the recursors of the ones that
stayed. -/
def widenWithPeeled (b : Block) (peeled : Array InductiveType) (peeledAt : Array Nat)
    (pubRec : Nat → Name) (core pub : Name) (coreAt : Array Nat) (self : Nat)
    (compile := true) : TermElabM Unit := do
  let us := b.us.map Level.param
  let info ← getConstInfo core
  let total := b.size + peeled.size
  let keptAt := (Array.range total).filter (!peeledAt.contains ·)
  let mnames := motiveNames total
  -- the name, arity and constructors of whichever member sits at a place in the
  -- block, peeled or not, and all as the writer wrote them
  let memberOf (o : Nat) : Name × Expr × Array Constructor :=
    match peeledAt.idxOf? o with
    | some k => (peeled[k]!.name, peeled[k]!.type, peeled[k]!.ctors.toArray)
    | none =>
      let m := b.members[(keptAt.idxOf? o).get!]!
      (m.name, m.type, m.ctors.map fun c => { name := c.name, type := c.type })
  -- which member of the whole block, if any, a name belongs to
  let memberAt (n : Name) : Option Nat :=
    (Array.range total).find? fun o => (memberOf o).1 == n
  let (selfName, selfType, _) := memberOf self
  forallTelescope info.type fun args concl => do
    let ps := args.extract 0 b.numParams
    -- the motives are the arguments after the parameters whose own types end in
    -- a sort
    let mut nMot := 0
    for a in args.extract b.numParams args.size do
      if ← forallTelescopeReducing (← inferType a) fun _ c => pure c.isSort then
        nMot := nMot + 1
      else break
    unless nMot == coreAt.size do
      throwError "`{core}` has {nMot} motives where the recursion is over {coreAt.size}"
    let oldMot := args.extract b.numParams (b.numParams + nMot)
    -- the universe the recursion returns in is the core's own
    let lvl ← forallTelescopeReducing (← inferType oldMot[0]!) fun _ c =>
      match c with
      | .sort u => pure u
      | _ => throwError "`{core}`'s first motive does not end in a sort"
    let numIdxs ← forallTelescope (← instantiateForall selfType ps) fun is _ => pure is.size
    let oldMin := args.extract (b.numParams + nMot) (args.size - numIdxs - 1)
    let major := args.extract (args.size - numIdxs - 1) args.size
    -- a motive is made afresh wherever the core has none to reuse, and also
    -- where the core's own would name the inductive behind a peeled member
    -- instead of the member: the writer never wrote `Tm._ind`
    let motDecls : Array (Name × (Array Expr → TermElabM Expr)) :=
      (Array.range total).map fun o =>
        (mnames[o]!, fun _ => do
          match (if peeledAt.contains o then none else coreAt.idxOf? o) with
          | some q => inferType oldMot[q]!
          | none =>
            let (n, ty, _) := memberOf o
            forallTelescope (← instantiateForall ty ps) fun idxs _ =>
              withLocalDeclD `t (mkAppN (mkConst n us) (ps ++ idxs)) fun t =>
                mkForallFVars (idxs ++ #[t]) (mkSort lvl))
    withImplicits motDecls fun motives => do
      let coreMotives := coreAt.map (motives[·]!)
      let sub (e : Expr) : Expr := e.replaceFVars oldMot coreMotives
      -- one minor per constructor, in the order the block was written
      let selfPeeled := peeledAt.contains self
      let mut minorDecls : Array (Name × (Array Expr → TermElabM Expr)) := #[]
      let mut owner : Array Nat := #[]
      let mut ctorOf : Array Constructor := #[]
      let mut taken := 0
      for o in *...total do
        let (_, _, cs) := memberOf o
        for c in cs do
          owner := owner.push o
          ctorOf := ctorOf.push c
          if coreAt.contains o && !selfPeeled then
            let old := oldMin[taken]!
            taken := taken + 1
            minorDecls := minorDecls.push (Name.mkSimple c.name.getString!, fun _ =>
              return sub (← inferType old))
          else
            minorDecls := minorDecls.push (Name.mkSimple c.name.getString!, fun _ =>
              peeledMinorType b.numParams memberAt motives us ps motives[o]! c)
      withLocalDeclsD minorDecls fun minors => do
        let mut coreMinors : Array Expr := #[]
        for q in *...minors.size do
          if selfPeeled then
            if coreAt.contains owner[q]! then
              coreMinors := coreMinors.push <| ← selfMinorValue b.numParams memberAt pubRec
                (lvl :: us) coreAt motives minors ps minors[q]! ctorOf[q]!
          else if coreAt.contains owner[q]! then
            coreMinors := coreMinors.push minors[q]!
        let publish (maj : Array Expr) (goal : Expr) : TermElabM Unit := do
          let all := ps ++ motives ++ minors ++ maj
          addDef pub info.levelParams (← mkForallFVars all goal)
            (← mkLambdaFVars all (mkAppN (mkConst core (info.levelParams.map Level.param))
              (ps ++ coreMotives ++ coreMinors ++ maj)))
            (compile := compile)
          markElabAsElim pub
        if selfPeeled then
          -- the core is the kernel's recursor over the inductive behind the
          -- member, so its major is stated at that and not at the name the
          -- writer reads
          let idxDecls ← forallTelescope (← instantiateForall selfType ps) fun idxs _ => do
            let mut ds : Array (Name × (Array Expr → TermElabM Expr)) := #[]
            for q in *...idxs.size do
              let ty ← inferType idxs[q]!
              let before := idxs.extract 0 q
              ds := ds.push ((← idxs[q]!.fvarId!.getUserName), fun prev =>
                pure (ty.replaceFVars before prev))
            return ds
          withImplicits idxDecls fun idxs =>
            withLocalDeclD `t (mkAppN (mkConst selfName us) (ps ++ idxs)) fun t => do
              publish (idxs ++ #[t]) (mkAppN motives[self]! (idxs ++ #[t]))
              -- and a companion that can run
              let csName := core.getPrefix ++ `casesOn
              let all := ps ++ motives ++ minors ++ idxs ++ #[t]
              let ok ← attempt? `Mumi.indind m!"no compiled recursion for `{pub}`" <| do
                unless ((← getEnv).find? csName).isSome do
                  throwError "`{csName}` is not there to take the major apart with"
                unless coreAt.size == 1 do
                  throwError "the recursion is over {coreAt.size} members at once"
                let elimLvls := info.levelParams.map Level.param
                let selfCall := mkAppN (mkConst (pub ++ `impl) elimLvls)
                  (ps ++ motives ++ minors)
                let mut caseVals : Array Expr := #[]
                for q in *...minors.size do
                  if owner[q]! == self then
                    caseVals := caseVals.push <| ← selfMinorValue b.numParams memberAt pubRec
                      (lvl :: us) coreAt motives minors ps minors[q]! ctorOf[q]!
                      (selfCall? := some selfCall)
                let decl := Declaration.defnDecl
                  { name := pub ++ `impl, levelParams := info.levelParams
                    type := ← mkForallFVars all (mkAppN motives[self]! (idxs ++ #[t]))
                    value := ← mkLambdaFVars all (mkAppN (mkConst csName elimLvls)
                      (ps ++ #[motives[self]!] ++ idxs ++ #[t] ++ caseVals))
                    hints := .opaque, safety := .unsafe }
                addDecl decl
                compileDecl decl (logErrors := false)
                if Lean.isNoncomputable (← getEnv) (pub ++ `impl) then
                  throwError "the companion did not compile either"
                Lean.setImplementedBy pub (pub ++ `impl)
              unless compile || ok.isNone do
                compileDecl (.defnDecl (← getConstInfoDefn pub)) (logErrors := false)
        else
          publish major (sub concl)

/-- The wrapper that a data member unfolds to, and the pieces that take it apart. -/
def emitSub (b : Block) (i : Nat) : MetaM Unit := do
  let m := b.members[i]!
  let n := subName m.name
  let nArgs ← forallTelescope m.type fun idxs _ => pure idxs.size
  forallBoundedTelescope (← getConstInfo (wfName m.name)).type nArgs fun ps _ => do
    let sub := mkAppN (mkConst n b.lvls) ps
    let pre := b.preApp i ps
    let wf := b.wfApp i ps
    let ctorType ← withLocalDeclD `val pre fun v =>
      withLocalDeclD `property (mkApp wf v) fun h =>
        return implicitPrefix ps.size (← mkForallFVars (ps ++ #[v, h]) sub)
    addInd b.us ps.size
      #[{ name := n, type := ← mkForallFVars ps (mkSort m.level)
          ctors := [{ name := n ++ `mk, type := ctorType }] }]
      (genBRecOn := false)
    -- the two fields, as `Subtype` states them: the parameters implicit, so that
    -- `congrArg X._sub.val h` is a thing that can be written
    withLocalDeclD `self sub fun t => do
      for (j, name, ty, compile) in
          [(0, n ++ `val, pre, true), (1, n ++ `property, mkApp wf (b.sVal i ps t), false)] do
        addDef name b.us (implicitPrefix ps.size (← mkForallFVars (ps.push t) ty))
          (implicitPrefix ps.size (← mkLambdaFVars (ps.push t) (.proj n j t)))
          (hints := .abbrev) (compile := compile)
        setReducibleAttribute name
        modifyEnv (addProjectionFnInfo · name (n ++ `mk) ps.size j false)
    -- the wrapper is a one-constructor inductive whose two definitions really
    -- are its projections, and saying so is what keeps `Γ.val` printing as
    -- `Γ.val` rather than as the application it is underneath: field notation
    -- is offered for a name the environment holds a *structure* under, and
    -- looks through the member's definition to find it
    let fields := #[`val, `property].map fun f =>
      ({ fieldName := f, projFn := n ++ f, subobject? := none, binderInfo := .default } :
        StructureFieldInfo)
    modifyEnv (registerStructure · { structName := n, fields })
    setStructureParents n #[]
    -- two wrappers with the same value are the same wrapper, the other field
    -- being a proof.  Eta says the rest: `x` is its own `⟨x.val, x.property⟩`
    withLocalDecl `x .implicit sub fun x => withLocalDecl `y .implicit sub fun y => do
      withLocalDeclD `h (← mkEq (b.sVal i ps x) (b.sVal i ps y)) fun h => do
        let motive ← withLocalDeclD `v pre fun v =>
          withLocalDeclD `hp (mkApp wf v) fun hp => do
            mkLambdaFVars #[v] (← mkForallFVars #[hp] (← mkEq x (b.sMk i ps v hp)))
        let base ← withLocalDeclD `hp (mkApp wf (b.sVal i ps x)) fun hp => do
          mkLambdaFVars #[hp] (← mkEqRefl x)
        addDef (n ++ `ext) b.us
          (implicitPrefix ps.size (← mkForallFVars (ps ++ #[x, y, h]) (← mkEq x y)))
          (implicitPrefix ps.size (← mkLambdaFVars (ps ++ #[x, y, h])
            (mkApp (← mkEqNDRec motive base h) (b.sProp i ps y))))
          (compile := false)
    let valFn := mkAppN (b.cst (n ++ `val)) ps
    let extFn := mkAppN (b.cst (n ++ `ext)) ps
    for (cls, args) in
        [(``Repr, #[valFn]), (``Hashable, #[valFn]), (``DecidableEq, #[valFn, extFn])] do
      let how := match cls with
        | ``Repr => ``Mumi.reprOfVal
        | ``Hashable => ``Mumi.hashableOfVal
        | _ => ``Mumi.decEqOfVal
      let name := Name.mkStr n ("inst" ++ cls.getString!)
      discard <| attempt? `Mumi.indind m!"`{name}`" do
        withLocalDecl `inst .instImplicit (← mkAppM cls #[pre]) fun ih => do
          addDef name b.us
            (implicitPrefix ps.size (← mkForallFVars (ps.push ih) (← mkAppM cls #[sub])))
            (implicitPrefix ps.size (← mkLambdaFVars (ps.push ih) (← mkAppM how args)))
          Lean.Meta.registerInstance name .global (eval_prio default)

/--
`e` with every application of an eliminator's motive `mot` replaced by what `f`
makes of the argument it was applied to. -/
private def substMot (mot : Expr) (f : Expr → Expr) (e : Expr) : Expr :=
  e.replace fun sub => if sub.isApp && sub.getAppFn == mot then some (f sub.appArg!) else none

/--
The level a course-of-values table takes its motive into, which the block has no
name for. -/
private def motiveLevelName (us : List Name) : Name := Id.run do
  let mut c := `u
  let mut k := 0
  while us.contains c do
    k := k + 1
    c := Name.mkSimple s!"u_{k}"
  return c

/--
The conjuncts of a well-formedness obligation, each with a proof of it read off
the obligation itself. -/
private partial def wfConjuncts (ty proof : Expr) : MetaM (Array (Expr × Expr)) := do
  let ty ← whnf ty
  unless ty.isAppOfArity ``And 2 do return #[(ty, proof)]
  let l := ty.appFn!.appArg!
  let r := ty.appArg!
  return (← wfConjuncts l (mkApp3 (mkConst ``And.left) l r proof))
    ++ (← wfConjuncts r (mkApp3 (mkConst ``And.right) l r proof))

/-- The levels a course-of-values table over a member is stated at. -/
private structure BRecOnLevels where
  /-- the level parameters, the motive's ahead of the block's -/
  lps : List Name
  /-- the motive's own level -/
  lvl : Level
  /-- the table's level: room for the motive and for the member's own fields,
  which is what Lean's own `below` asks for too -/
  w : Level
  /-- the levels a declaration of the family is applied at -/
  ls : List Level

/-- The levels for a table over a member whose own level is `level`. -/
private def brecOnLevels (b : Block) (level : Level) : BRecOnLevels :=
  let lvlName := motiveLevelName b.us
  let lvl := Level.param lvlName
  { lps := lvlName :: b.us, lvl, w := (mkLevelMax level lvl).normalize, ls := lvl :: b.lvls }

/-! `Lean.Meta.PProdN.pack` and `.mk` fold the same way, but take each entry's
level from `getLevel` instead of from the table's own.  The recursion then stops
reducing, so the two below write `w` at every entry and stay. -/

/-- The type of a row of the table, from the type of each entry. -/
private def mkRowTy (w : Level) (tys : Array Expr) : Expr :=
  if tys.isEmpty then mkConst ``PUnit [w]
  else tys.pop.foldr (mkApp2 (mkConst ``PProd [w, w])) tys.back!

/-- A row of the table, from the type and the value of each entry. -/
private def mkRow (w : Level) (entries : Array (Expr × Expr)) : Expr := Id.run do
  if entries.isEmpty then return mkConst ``PUnit.unit [w]
  let mut ty := entries.back!.1
  let mut val := entries.back!.2
  for k in *...(entries.size - 1) do
    let j := entries.size - 2 - k
    val := mkApp4 (mkConst ``PProd.mk [w, w]) entries[j]!.1 ty entries[j]!.2 val
    ty := mkApp2 (mkConst ``PProd [w, w]) entries[j]!.1 ty
  return val

/--
One of the definitions a course-of-values recursion is made of.  The member's
own arguments are bound implicitly; the result is reducible and protected, and
goes to the equation compiler rather than to the code generator.  `isElim` marks
the two that eliminate, which the tactics must not unfold. -/
private def addBRecOnPart (name : Name) (lps : List Name) (numArgs : Nat) (isElim : Bool)
    (type value : Expr) : MetaM Unit := do
  addDef name lps (implicitPrefix numArgs type) (implicitPrefix numArgs value) (compile := false)
  setReducibleAttribute name
  if isElim then modifyEnv (markAuxRecursor · name)
  modifyEnv (addProtected · name)

/-- The theorem that the recursion is its step applied to its row. -/
private def addBRecOnEq (name : Name) (lps : List Name) (numArgs : Nat)
    (type value : Expr) : MetaM Unit := do
  addDecl (.thmDecl { name, levelParams := lps, type := implicitPrefix numArgs type,
                      value := implicitPrefix numArgs value })
  modifyEnv (addProtected · name)

/--
The caller's data, restated wherever the pre-recursor bound something of its
own. -/
private structure Restated where
  /-- the member's arguments, with a kept index replaced by the bound one -/
  args : Array Expr
  /-- the caller's motive, at those arguments -/
  motive : Expr
  /-- the caller's step, in the two declarations that have one -/
  step? : Option Expr

/--
The same four declarations as `emitBRecOn`, for a member with indices of its
own. -/
private def emitIndexedBRecOn (p : Plan) (preRecUnivs : Nat) (b : Block) (i : Nat) :
    MetaM Unit := do
  let m := b.members[i]!
  let n := subName m.name
  let nArgs ← forallTelescope m.type fun idxs _ => pure idxs.size
  let preRec := preDataRecName p.preIsHeterogeneous m.name
  unless (← getEnv).contains preRec do return
  let recInfo ← getConstInfo preRec
  let { lps, lvl, w, ls } := brecOnLevels b m.level
  forallBoundedTelescope (← getConstInfo (wfName m.name)).type nArgs fun ps _ => do
    let params := ps.extract 0 b.numParams
    let sub := mkAppN (mkConst n b.lvls) ps
    -- the arguments the pre-type kept as indices of its own, which the recursor
    -- binds and which everything downstream is therefore generalised over
    let keptPos := (Array.range (nArgs - b.numParams)).filterMap fun q =>
      if m.dropped.contains q then none else some (b.numParams + q)
    let keptFVars := keptPos.map (ps[·]!.fvarId!)
    -- and the deleted ones whose types mention a kept one, which cannot stay
    -- fixed while it varies and so are bound beside it
    let mut gp : Array Nat := #[]
    let mut gf : Array FVarId := #[]
    for q in m.dropped.qsort (· < ·) do
      let k := b.numParams + q
      if (← inferType ps[k]!).hasAnyFVar fun id => keptFVars.contains id || gf.contains id then
        gp := gp.push k
        gf := gf.push ps[k]!.fvarId!
    let genPos := gp
    -- the other way round there is nothing to do, and nothing to expect: a kept
    -- index is an index of the pre-type, which has no deleted one to speak of
    let dropFVars := m.dropped.map (ps[b.numParams + ·]!.fvarId!)
    for k in keptPos do
      if (← inferType ps[k]!).hasAnyFVar dropFVars.contains then return
    let keptNames ← keptPos.mapM fun k => ps[k]!.fvarId!.getUserName
    let genNames ← genPos.mapM fun k => ps[k]!.fvarId!.getUserName
    -- `ps`, with the bound positions taken from `idxs` and `gs` instead
    let psAt (idxs gs : Array Expr) : Array Expr := Id.run do
      let mut out := ps
      for j in *...keptPos.size do
        out := out.set! keptPos[j]! idxs[j]!
      for j in *...gs.size do
        out := out.set! genPos[j]! gs[j]!
      return out
    let mkS (r : Restated) (v pf : Expr) : Expr := b.sMk i r.args v pf
    let belowOf (args : Array Expr) (mot x : Expr) : Expr :=
      mkAppN (mkConst (n ++ `below) ls) (args ++ #[mot, x])
    let belowAt (r : Restated) (x : Expr) : Expr := belowOf r.args r.motive x
    let stepTy (args : Array Expr) (mot : Expr) : MetaM Expr :=
      withLocalDeclD `t (mkAppN (mkConst n b.lvls) args) fun t => do
        mkForallFVars #[t] (← mkArrow (belowOf args mot t) (mkApp mot t))
    withLocalDecl `motive .implicit (← mkArrow sub (mkSort lvl)) fun motive => do
      -- the pre-block's recursor, with the member's own motive `fun k v => ∀ w,
      -- generalised bodyOf` and every other member's trivial
      let drive (outerStep? : Option Expr) (bodyOf : Restated → Expr → Expr → MetaM Expr)
          (second : Restated → Expr → Expr → Expr → Expr)
          (mk : Restated → Expr → Expr → Array (Expr × Expr) → MetaM Expr) : MetaM Expr := do
        -- the deleted indices that follow a kept one, at the kept ones given
        let withDropped (keptVals : Array Expr) (k : Array Expr → MetaM Expr) : MetaM Expr :=
          withLocalDeclsD ((Array.range genPos.size).map fun j =>
            (genNames[j]!, fun (news : Array Expr) => do
              return (← inferType ps[genPos[j]!]!).replaceFVars
                (keptPos.map (ps[·]!) ++ (genPos.extract 0 j).map (ps[·]!))
                (keptVals ++ news))) k
        -- and the caller's own data, restated at `args`
        let withMotive (args : Array Expr)
            (k : Restated → Array Expr → MetaM Expr) : MetaM Expr := do
          if keptPos.isEmpty then
            k { args, motive, step? := outerStep? } #[]
          else
            let motTy ← mkArrow (mkAppN (mkConst n b.lvls) args) (mkSort lvl)
            withLocalDeclD `motive motTy fun mot => do
              if outerStep?.isSome then
                withLocalDeclD `F (← stepTy args mot) fun f =>
                  k { args, motive := mot, step? := some f } #[mot, f]
              else
                k { args, motive := mot, step? := none } #[mot]
        let memMot ← withLocalDeclsD
            ((Array.range keptPos.size).map fun j =>
              (keptNames[j]!, fun (news : Array Expr) => do
                return (← inferType ps[keptPos[j]!]!).replaceFVars
                  ((keptPos.extract 0 j).map (ps[·]!)) news))
            fun kept => do
          withLocalDeclD `v (b.preApp i (psAt kept #[])) fun v =>
            withDropped kept fun gs => do
              let args := psAt kept gs
              withLocalDeclD `w (mkApp (b.wfApp i args) v) fun wv =>
                withMotive args fun r ms => do
                  mkLambdaFVars (kept.push v)
                    (← mkForallFVars (gs ++ #[wv] ++ ms) (← bodyOf r v wv))
        -- the sort the recursor takes its motives into, which the generalisation
        -- moves and which the motive just built is the only honest account of
        let uR ← forallTelescope (← inferType memMot) fun _ concl =>
          return (← whnf concl).sortLevel!.normalize
        let us := List.replicate preRecUnivs uR ++ b.lvls
        let ty ← instantiateForall (recInfo.instantiateTypeLevelParams us) params
        let unitTy := mkConst ``PUnit [uR]
        let unitVal := mkConst ``PUnit.unit [uR]
        forallTelescope ty fun xs concl => do
          let mot := concl.getAppFn
          -- the kept indices and the major premise trail the minors
          let nTrail := concl.getAppNumArgs
          -- the motives lead, being the arguments whose types end in a sort
          let mut nMot := 0
          for x in xs do
            unless ← forallTelescope (← inferType x) fun _ c => pure c.isSort do break
            nMot := nMot + 1
          let motives := xs.extract 0 nMot
          let mut motVals := #[]
          for mo in motives do
            if mo == mot then
              motVals := motVals.push memMot
            else
              motVals := motVals.push
                (← forallTelescope (← inferType mo) fun ys _ => mkLambdaFVars ys unitTy)
          -- every motive is an `fvar` while a minor is being built, here as much
          -- as in `substMot`; a member's constructor may carry a field of another
          -- member, whose hypothesis is about that other motive
          let subMot (e : Expr) : Expr := e.replace fun s =>
            if s.isApp then
              match motives.findIdx? (· == s.getAppFn) with
              | some k => some (mkAppN motVals[k]! s.getAppArgs).headBeta
              | none => none
            else none
          let mut vals := #[]
          for minor in xs.extract nMot (xs.size - nTrail) do
            let v ← forallTelescope (← inferType minor) fun fields mconcl => do
              unless mconcl.getAppFn == mot do return ← mkLambdaFVars fields unitVal
              let ctorApp := mconcl.appArg!
              let cIdxs := mconcl.getAppArgs.pop
              withDropped cIdxs fun gs => do
                let cArgs := psAt cIdxs gs
                let wfC := b.wfApp i cArgs
                withLocalDeclD `w (mkApp wfC ctorApp) fun wv =>
                  withMotive cArgs fun r ms => do
                    let cs ← wfConjuncts (mkApp wfC ctorApp) wv
                    let mut entries := #[]
                    for f in fields do
                      let e? ← forallTelescope (← inferType f) fun ys body => do
                        unless body.isApp && body.getAppFn == mot do return none
                        -- a hypothesis at another index is about another wrapper,
                        -- so about another motive, and gets no column
                        unless ← isDefEq (b.preApp i (psAt body.getAppArgs.pop #[]))
                            (b.preApp i cArgs) do
                          return none
                        let fv := body.appArg!
                        let want ← mkForallFVars ys (mkApp wfC fv)
                        let mut pf? := none
                        for (cty, cpf) in cs do
                          if pf?.isNone then
                            if ← isDefEq cty want then pf? := some cpf
                        let some cpf := pf? | return none
                        let wpf := mkAppN cpf ys
                        let ih := mkAppN f (ys ++ gs ++ #[wpf] ++ ms)
                        return some (← mkForallFVars ys (mkApp2 (mkConst ``PProd [lvl, w])
                            (mkApp r.motive (mkS r fv wpf)) (second r ih fv wpf)),
                          ← mkLambdaFVars ys ih)
                      if let some e := e? then entries := entries.push e
                    mkLambdaFVars (fields ++ gs ++ #[wv] ++ ms) (← mk r ctorApp wv entries)
            vals := vals.push (subMot v)
          return mkAppN (mkConst preRec us) ((params ++ motVals) ++ vals)
      -- the indices the recursor still wants, then the pre-value and its
      -- obligation, which is what the recursion runs on and what eta says is the
      -- wrapper back again, with everything the motive generalised put back at
      -- what the caller fixed it to
      let opened (dargs : Array Expr) (x : Expr) : Array Expr :=
        keptPos.map (ps[·]!) ++ #[b.sVal i ps x] ++ genPos.map (ps[·]!)
          ++ #[b.sProp i ps x] ++ dargs
      let outerR : Restated := { args := ps, motive, step? := none }
      -- 1. the table
      let belowVal ← drive none (fun _ _ _ => pure (mkSort w))
        (fun _ ih _ _ => ih)
        (fun _ _ _ entries => return mkRowTy w (entries.map (·.1)))
      let belowName := n ++ `below
      let dBelow := if keptPos.isEmpty then #[] else #[motive]
      addBRecOnPart belowName lps ps.size (isElim := true)
        (← mkForallFVars (ps.push motive) (← mkArrow sub (mkSort w)))
        (← mkLambdaFVars (ps.push motive)
          (← withLocalDeclD `t sub fun t =>
            mkLambdaFVars #[t] (mkAppN belowVal (opened dBelow t))))
      let fTy ← stepTy ps motive
      withLocalDeclD `t sub fun t => withLocalDeclD `F fTy fun F => do
        let args := ps ++ #[motive, t, F]
        let outerRF : Restated := { args := ps, motive, step? := some F }
        let dStep := if keptPos.isEmpty then #[] else #[motive, F]
        let pair (r : Restated) (x : Expr) : Expr :=
          mkApp2 (mkConst ``PProd [lvl, w]) (mkApp r.motive x) (belowAt r x)
        -- 2. one pass filling it, answering at the wrapper and handing back the
        -- row it stood on
        let goVal ← drive (some F) (fun r v wv => pure (pair r (mkS r v wv)))
          (fun r _ fv wpf => belowAt r (mkS r fv wpf))
          (fun r ctorApp wv entries => do
            let x := mkS r ctorApp wv
            let row := mkRow w entries
            return mkApp4 (mkConst ``PProd.mk [lvl, w]) (mkApp r.motive x) (belowAt r x)
              (mkApp2 r.step?.get! x row) row)
        let goName := n ++ `brecOn ++ `go
        addBRecOnPart goName lps ps.size (isElim := false)
          (← mkForallFVars args (pair outerR t))
          (← mkLambdaFVars args (mkAppN goVal (opened dStep t)))
        -- 3. the answer alone
        let brecName := n ++ `brecOn
        let goApp (r : Restated) (x : Expr) : Expr :=
          mkAppN (mkConst goName ls) (r.args ++ #[r.motive, x, r.step?.get!])
        addBRecOnPart brecName lps ps.size (isElim := true)
          (← mkForallFVars args (mkApp motive t))
          (← mkLambdaFVars args
            (mkApp3 (mkConst ``PProd.fst [lvl, w]) (mkApp motive t) (belowAt outerR t)
              (goApp outerRF t)))
        -- 4. and that the answer is the step applied to the row
        let brecApp (r : Restated) (x : Expr) : Expr :=
          mkAppN (mkConst brecName ls) (r.args ++ #[r.motive, x, r.step?.get!])
        let eqOf (r : Restated) (x : Expr) : Expr :=
          mkApp3 (mkConst ``Eq [lvl]) (mkApp r.motive x) (brecApp r x) (mkApp2 r.step?.get! x
            (mkApp3 (mkConst ``PProd.snd [lvl, w]) (mkApp r.motive x) (belowAt r x) (goApp r x)))
        let eqVal ← drive (some F) (fun r v wv => pure (eqOf r (mkS r v wv)))
          (fun _ ih _ _ => ih)
          (fun r ctorApp wv _ => do
            let x := mkS r ctorApp wv
            return mkApp2 (mkConst ``Eq.refl [lvl]) (mkApp r.motive x) (brecApp r x))
        addBRecOnEq (brecName ++ `eq) lps ps.size
          (← mkForallFVars args (eqOf outerRF t))
          (← mkLambdaFVars args (mkAppN eqVal (opened dStep t)))

/--
`below`, `brecOn.go`, `brecOn` and `brecOn.eq` for a data member's wrapper,
which is what lets a definition by recursion over the member be structural. -/
def emitBRecOn (p : Plan) (preRecUnivs : Nat) (b : Block) (i : Nat) : MetaM Unit := do
  let m := b.members[i]!
  let n := subName m.name
  let nArgs ← forallTelescope m.type fun idxs _ => pure idxs.size
  unless nArgs == b.numParams do
    emitIndexedBRecOn p preRecUnivs b i
    return
  let recD := m.name ++ `recD
  let casesD := m.name ++ `casesD
  unless (← getEnv).contains recD && (← getEnv).contains casesD do return
  let recInfo ← getConstInfo recD
  let casesInfo ← getConstInfo casesD
  let { lps, lvl, w, ls } := brecOnLevels b m.level
  -- which of an eliminator's levels is its motive's
  let motiveLvl (info : ConstantInfo) : MetaM Name :=
    forallBoundedTelescope info.type (some (b.numParams + 1)) fun xs _ => do
      forallTelescope (← inferType xs.back!) fun _ concl => do
        let .sort (.param p) := concl
          | throwError "`{info.name}` does not take its motive into a level of its own"
        return p
  let recMLvl ← motiveLvl recInfo
  let casesMLvl ← motiveLvl casesInfo
  forallBoundedTelescope (← getConstInfo (wfName m.name)).type nArgs fun ps _ => do
    let sub := mkAppN (mkConst n b.lvls) ps
    withLocalDecl `motive .implicit (← mkArrow sub (mkSort lvl)) fun motive => do
      let belowOf (t : Expr) : Expr := mkAppN (mkConst (n ++ `below) ls) (ps ++ #[motive, t])
      -- `X.recD` or `X.casesD` at motive level `l`, with `motiveOf` for the
      -- motive and `mk` for each minor premise, stopping short of the major
      let build (info : ConstantInfo) (mlvl : Name) (l : Level) (motiveOf : Expr → MetaM Expr)
          (subst : Expr → Expr) (second : Expr → Expr → Array Expr → Expr)
          (mk : Expr → Array Expr → Array Expr → MetaM Expr) : MetaM Expr := do
        let us := info.levelParams.map fun q => if q == mlvl then l else .param q
        let ty ← instantiateForall (info.instantiateTypeLevelParams us) ps
        forallTelescope ty fun xs _ => do
          let mot := xs[0]!
          let motiveVal ← motiveOf (← inferType mot).bindingDomain!
          let mut vals := #[]
          for minor in xs.extract 1 (xs.size - 1) do
            let v ← forallTelescope (← inferType minor) fun fields concl => do
              let mut entries := #[]
              let mut ihs := #[]
              for f in fields do
                let entry? ← forallTelescope (← inferType f) fun ys body => do
                  unless body.isApp && body.getAppFn == mot do return none
                  return some (← mkForallFVars ys (mkApp2 (mkConst ``PProd [lvl, w])
                    (mkApp motive body.appArg!) (second f body.appArg! ys)))
                if let some e := entry? then
                  entries := entries.push e
                  ihs := ihs.push f
              mkLambdaFVars fields (← mk concl.appArg! entries ihs)
            vals := vals.push (substMot mot subst v)
          return mkAppN (mkConst info.name us) ((ps.push motiveVal) ++ vals)
      -- 1. the table: what is known about everything below `t`
      let belowVal ← build recInfo recMLvl (mkLevelSucc w)
        (fun dom => return .lam `t dom (mkSort w) .default)
        (fun _ => mkSort w)
        (fun f _ ys => mkAppN f ys)
        (fun _ entries _ => return mkRowTy w entries)
      let belowName := n ++ `below
      addBRecOnPart belowName lps ps.size (isElim := true)
        (← mkForallFVars (ps.push motive) (← mkArrow sub (mkSort w)))
        (← mkLambdaFVars (ps.push motive) belowVal)
      let fTy ← withLocalDeclD `t sub fun t => do
        mkForallFVars #[t] (← mkArrow (belowOf t) (mkApp motive t))
      withLocalDeclD `t sub fun t => withLocalDeclD `F fTy fun F => do
        let args := ps ++ #[motive, t, F]
        let pair (x : Expr) : Expr :=
          mkApp2 (mkConst ``PProd [lvl, w]) (mkApp motive x) (belowOf x)
        -- 2. one pass filling the table, which answers at `t` and hands back
        -- the row it stood on so that the next constructor up can reuse it
        let goVal ← build recInfo recMLvl w
          (fun dom => withLocalDeclD `x dom fun x => mkLambdaFVars #[x] (pair x))
          pair
          (fun _ arg _ => belowOf arg)
          (fun ctorApp entries ihs => do
            let row := mkRow w (entries.zip ihs)
            return mkApp4 (mkConst ``PProd.mk [lvl, w]) (mkApp motive ctorApp) (belowOf ctorApp)
              (mkApp2 F ctorApp row) row)
        let goName := n ++ `brecOn ++ `go
        addBRecOnPart goName lps ps.size (isElim := false)
          (← mkForallFVars args (pair t))
          (← mkLambdaFVars args (mkApp goVal t))
        -- 3. the answer alone, which is what the equation compiler applies
        let brecName := n ++ `brecOn
        let goApp (x : Expr) : Expr := mkAppN (mkConst goName ls) (ps ++ #[motive, x, F])
        addBRecOnPart brecName lps ps.size (isElim := true)
          (← mkForallFVars args (mkApp motive t))
          (← mkLambdaFVars args
            (mkApp3 (mkConst ``PProd.fst [lvl, w]) (mkApp motive t) (belowOf t) (goApp t)))
        -- 4. and that the answer is the step applied to the row, which holds by
        -- `rfl` at every constructor and is what the equations are unfolded with
        let brecApp (x : Expr) : Expr := mkAppN (mkConst brecName ls) (ps ++ #[motive, x, F])
        let eqOf (x : Expr) : Expr :=
          mkApp3 (mkConst ``Eq [lvl]) (mkApp motive x) (brecApp x) (mkApp2 F x
            (mkApp3 (mkConst ``PProd.snd [lvl, w]) (mkApp motive x) (belowOf x) (goApp x)))
        let eqVal ← build casesInfo casesMLvl .zero
          (fun dom => withLocalDeclD `x dom fun x => mkLambdaFVars #[x] (eqOf x))
          eqOf
          (fun f _ ys => mkAppN f ys)
          (fun ctorApp _ _ => do
            return mkApp2 (mkConst ``Eq.refl [lvl]) (mkApp motive ctorApp) (brecApp ctorApp))
        addBRecOnEq (brecName ++ `eq) lps ps.size
          (← mkForallFVars args (eqOf t))
          (← mkLambdaFVars args (mkApp eqVal t))

/-- Emit the whole encoding for a prepared block. -/
def emit (p : Plan) : TermElabM Unit := do
  let docCtx := (← getLCtx, ← getLocalInstances)
  let dIdxs := p.block.dataIdxs
  let copyNames := p.copies.map (·.1)
  -- a `Prop` member whose arity runs over a copy is emitted under a hidden
  -- name: `Ok : List Ctx → Prop` is not a statement the block can make until
  -- `ofOrig` exists to send a `List Ctx` to the copy the raw member is really
  -- over
  let rawMemberName : Name → Name := fun n => Id.run do
    for j in p.block.propIdxs do
      let m := p.block.members[j]!
      if copyNames.contains m.name then continue
      if m.name == n && m.type.getUsedConstants.any (copyNames.contains ·) then
        return Name.mkStr m.name "_nested"
    return n
  -- and a constructor of a member the writer declared is hidden whenever the raw
  -- world spells its type differently -- because it mentions a copy, or because
  -- the member it belongs to is one of the above
  let rawCtorName : Name → Name := fun n => Id.run do
    for m in p.block.members do
      if copyNames.contains m.name then continue
      for c in m.ctors do
        if c.name == n && c.type.getUsedConstants.any
            (fun u => copyNames.contains u || rawMemberName u != u) then
          return Name.mkStr m.name ("_nested_" ++ n.getString!)
    return n
  -- a raw declaration lives in the world where the copies *are* the types, so a
  -- type mentioning a constructor the bridge will rename must mention the
  -- hidden name instead
  let b := { p.block with rawCtor := rawCtorName, rawMember := rawMemberName }
  let toRaw := b.toRaw
  -- position of a data member among the motives
  let dpos : Array Nat := Id.run do
    let mut out := (List.replicate b.size 0).toArray
    for q in *...dIdxs.size do
      out := out.set! dIdxs[q]! q
    return out

  -- 1. the data members' pre-types
  let preRecUnivs ← emitPreData p

  -- 2. the `Prop` members' pre-types, layer by layer: a proposition indexed by
  -- another is declared after it, since no member of one mutual inductive may
  -- appear in another's arity
  for layer in p.prePropInds do
    unless layer.isEmpty do
      addInd b.us b.numParams layer

  -- 3. the well-formedness predicates
  for (name, type, value) in p.wfDecls do
    addDef name b.us type (widenPreRecLevels p preRecUnivs value) (compile := false)

  -- 4. the members themselves, each after the ones its arity names: `Ty Γ` is a
  -- subtype whose predicate is applied to `Γ.val`, and that names `Ctx`
  for i in ← memberOrder b (b.dataIdxs ++ b.propIdxs) do
    let m := b.members[i]!
    if m.isProp then
      let value ← forallTelescope m.type fun idxs _ => do
        mkLambdaFVars idxs (mkAppN (b.cst (preName m.name)) (← b.preImages idxs))
      addDef (rawMemberName m.name) b.us m.type value (compile := false)
    else
      emitSub b i
      let value ← forallTelescope m.type fun idxs _ =>
        return ← mkLambdaFVars idxs (b.subtype i (← b.valArgs i idxs))
      addDef m.name b.us m.type value (compile := false)

  -- 5. the constructors, each after the ones its own type names
  for (i, c) in ← ctorOrder b (← memberOrder b (b.dataIdxs ++ b.propIdxs)) do
    if b.members[i]!.isProp then
      let cty := toRaw c.type
      let value ← forallTelescope cty fun xs _ => do
        mkLambdaFVars xs (mkAppN (b.cst (b.preOf c.name)) (← b.preImages xs))
      addDecl (.thmDecl
        { name := rawCtorName c.name, levelParams := b.us, type := cty, value })
      continue
    let cty := toRaw c.type
    let value ← forallTelescope cty fun xs concl => do
      let imgs ← b.preImages xs
      let mut subTys : Array Expr := #[]
      for x in xs do
        subTys := subTys.push (← b.subTy xs imgs (← inferType x))
      -- what the pre-world makes of an index the constructor built is exactly
      -- the constructor's own pre-image of it, so the equation the erasure
      -- states about it is one of a term with itself
      let vargs ← b.valArgs i concl.getAppArgs
      let eqs ← b.builtEqs i c.kinds (← b.ctorType c xs) xs imgs
        (b.members[i]!.dropped.map fun p => vargs[b.numParams + p]!)
      -- the conjuncts and, in the same order, what proves each of them
      let conjs ← b.wfConjs c.kinds (imgs.map some) subTys (eqs.map (·.2))
      let mut proofs : Array Expr := #[]
      for k in recPositions c.kinds do
        -- closed over the same erased fields `Block.wfConjs` closed the conjunct
        -- over, and the field's own proof serves at each of them
        let deps := erasedDeps c.kinds (imgs.map some) subTys
          (← b.wfOfSub imgs[k]! subTys[k]!) k
        proofs := proofs.push <| ← mkLambdaFVars (deps.map (xs[·]!))
          (← b.propImage xs[k]! (← inferType xs[k]!))
      for k in *...xs.size do
        if c.kinds[k]! == .erased then
          -- the field proves its conjunct at whatever the closure binds, since
          -- those are proofs of the very propositions the fields it names are
          let deps := erasedDeps c.kinds (imgs.map some) subTys (← b.preTy subTys[k]!) k
          proofs := proofs.push (← mkLambdaFVars (deps.map (xs[·]!)) xs[k]!)
      for (_, eq) in eqs do
        proofs := proofs.push (← mkEqRefl eq.appFn!.appArg!)
      let kept := (keptPositions c.kinds).map (imgs[·]!)
      mkLambdaFVars xs <| b.sMk i vargs
        (mkAppN (b.cst (b.preOf c.name)) kept) (introConj conjs proofs 0)
    addDef (rawCtorName c.name) b.us cty value

  -- 6. the recursors, one mutual group by structural recursion on the pre-types
  -- the motive's universe, under a name the writer cannot have taken
  let lp := (freshLevelNames b.us 1)[0]!
  let lvl := Level.param lp
  let recAuxName (i : Nat) : Name := b.members[i]!.name ++ `recAux
  -- a member of an induction-inductive block is a `def`, so Lean generates no
  -- `X.rec` for it and the name is free -- which is the one users reach for
  let env ← getEnv
  let pubRecName (i : Nat) : Name :=
    let n := b.members[i]!.name ++ `rec
    if (env.find? n).isNone then n else b.members[i]!.name ++ `recursor
  -- when members were peeled off, everything below states the recursion over
  -- what is left under a name of its own, and the writer's name is given the
  -- shape the whole block would have had
  let peeledAllData := p.peeled.all fun t =>
    match t.type.getForallBody with
    | .sort u => u.normalize != Level.zero
    | _ => false
  let widen := !p.peeled.isEmpty && b.propIdxs.isEmpty && peeledAllData
  let recName (i : Nat) : Name :=
    if widen then Name.mkStr b.members[i]!.name "_core_rec" else pubRecName i
  -- the recursor over the whole block states a `Prop` member's motive at the
  -- value the data recursion returned, which the `induction` tactic cannot read.
  -- The split recursor concludes at the motive itself, so it keeps a name of its
  -- own for the tactic to run on
  let inductName (i : Nat) : Name := b.members[i]!.name ++ `induct
  -- a member the writer declared, in a block with copies in it, gets its
  -- recursor twice over: the kernel-facing one, whose motives are over the
  -- copies, under a hidden name, and `X.rec` stated over the originals
  let rawRecName (i : Nat) : Name :=
    if p.copies.isEmpty then recName i else Name.mkStr b.members[i]!.name "_nested_rec"
  -- an induction-inductive block wants one recursor over all of its members at
  -- once, and falls back to the split recursors of steps 8 and 9 when there is
  -- none
  let grandRecName (i : Nat) : Name :=
    if p.copies.isEmpty then recName i else Name.mkStr b.members[i]!.name "_nested_grand"
  let grandAuxName (i : Nat) : Name :=
    if p.copies.isEmpty then b.members[i]!.name ++ `recAux
    else Name.mkStr b.members[i]!.name "_nested_grandAux"
  -- `none` if there is no recursor over the whole block, and otherwise the
  -- `Prop` members it left out -- free-standing ones, which step 9 still owes
  let grand? : Option (Array Nat) ←
    if b.propIdxs.isEmpty then pure none
    else attempt? `Mumi.indind "no recursor over the whole block" <| do
      -- what a deleted index arrives under is a choice, and neither way is the
      -- weaker one: carrying the propositions about it covers a `Prop`
      -- constructor that names one of them, and carrying only the value covers
      -- a deleted index built out of a constructor
      let env ← getEnv
      try
        emitGrandRecs b docCtx lp grandRecName grandAuxName rawCtorName true
      catch _ =>
        setEnv env
        emitGrandRecs b docCtx lp grandRecName grandAuxName rawCtorName false
  let grand := grand?.isSome
  let grandFree := grand?.getD #[]
  -- the split recursors are what step 10 builds the bridge out of, so they are
  -- skipped only when there is no bridge to build
  let grandOnly := grand && p.copies.isEmpty
  -- the parameters are shared by every motive, minor and recursive call, so the
  -- whole group is built under one telescope of them
  let results ←
   if grandOnly then pure (#[] : Array SplitRec) else
    forallBoundedTelescope b.members[dIdxs[0]!]!.type b.numParams fun ps _ => do
    b.withRawFront ps
        { members := dIdxs, pos := (dpos[·]!), lvl, major := `t, ihPos := b.ihPositions }
        fun motives minors => do
      -- what the recursion promises at a real value of a member's type
      let ihTypeAt (v : Expr) : MetaM Expr := do
        let r? ← b.withRecTarget? (← inferType v) fun _ mm args =>
          pure (mkAppN motives[dpos[mm]!]! (b.idxArgs args ++ #[v]))
        let some ty := r?
          | throwError "Not a value of a member of the block:{indentExpr v}"
        return ty
      let dCtors := b.ctorsOf dIdxs
      let mut out : Array SplitRec := #[]
      for i in dIdxs do
        let m := b.members[i]!
        let r ← withPreRec b i ps ihTypeAt fun idxs vargs delIhs t0 w => do
          let mut alts : Array Expr := #[]
          for c in m.ctors do
            let alt ← b.withAlt i c ps fun a => do
              let { kinds, xs, imgs, wc, conjs, real, recPos, dels, .. } := a
              -- a deleted index arrives with its own hypothesis, which
              -- is what a recursive call under it will be handed --
              -- unless it is a proof, and then there is none to arrive
              let ihDels := b.ihDrops i dels
              let dDecls : Array (Name × (Array Expr → MetaM Expr)) :=
                ihDels.map fun d => (`ih, fun _ => ihTypeAt d)
              withLocalDeclsD dDecls fun dIhs => do
                -- everything here is built over the fields as the
                -- constructor bound them and moved to the alternative's
                -- own binders at the end, because an induction
                -- hypothesis is found by the shape of the index term
                let mut ihAt : Array (FVarId × Expr) :=
                  ihDels.mapIdx fun q d => (d.fvarId!, dIhs[q]!)
                let mut ihs : Array Expr := #[]
                for k in b.ihPositions kinds do
                  -- a deleted field is not a field of the pre-term, so there is
                  -- nothing here to recurse at
                  if kinds[k]!.isDeleted then
                    let some q := ihDels.findIdx? (· == xs[k]!)
                      | throwError "The deleted field `{xs[k]!}` of `{c.name}` is \
                          not one of the alternative's indices"
                    ihs := ihs.push dIhs[q]!
                    continue
                  let some q := recPos.findIdx? (· == k)
                    | throwError "Not a recursive field of `{c.name}`"
                  let y := (imgs[k]!).get!
                  let pr := projConj conjs wc q
                  let ih? ← b.withRecTarget? (← inferType xs[k]!) fun ys mm args => do
                    let dihs ← (b.ihDrops mm (b.dropArgs mm args)).mapM
                      (ihOfTerm b dCtors rawCtorName b.hasIh
                        minors ihAt ·)
                    let call := mkAppN (mkConst (recAuxName mm) (lvl :: b.lvls))
                      (ps ++ motives ++ minors ++ b.idxArgs args ++ dihs ++
                        #[mkAppN y ys, mkAppN pr ys])
                    mkLambdaFVars ys call
                  let some ih := ih?
                    | throwError "Not a recursive field of `{c.name}`"
                  ihs := ihs.push ih
                  ihAt := ihAt.push (xs[k]!.fvarId!, ih)
                let core := mkAppN minors[b.minorIdx dIdxs c.name]!
                  (real ++ ihs.map (·.replaceFVars xs real))
                mkLambdaFVars (keptImages kinds imgs ++ dels ++ dIhs ++ #[wc])
                  (← b.transportBuilt i a
                    (fun mIdxs vargs w =>
                      return mkAppN motives[dpos[i]!]!
                        (mIdxs ++ #[b.sMk i vargs a.head w]))
                    (fun _ _ _ => return core))
            alts := alts.push alt
          let (recAuxType, recAuxValue) ← recAuxOver b i ps motives minors idxs delIhs t0 w
            (mkAppN motives[dpos[i]!]! (idxs ++ #[b.sMk i vargs t0 w])) alts
          let (recType, recValue) ←
            withLocalDeclD `t (mkAppN (b.memberCst i) (ps ++ idxs)) fun t => do
              let hide := hideRecBinders ps.size (motives.size + minors.size) idxs.size
              let ty := hide <| ←
                mkForallFVars (ps ++ motives ++ minors ++ idxs ++ #[t])
                  (mkAppN motives[dpos[i]!]! (idxs ++ #[t]))
              -- `X.rec` is not inside the recursion, so the hypothesis at a
              -- deleted index is a recursion of its own, at that index
              let dihs ← (b.ihDrops i (b.dropIdxs i idxs)).mapM
                (valueIh b recAuxName lvl ps motives minors ·)
              let val := hide <| ←
                mkLambdaFVars (ps ++ motives ++ minors ++ idxs ++ #[t])
                  (mkAppN (mkConst (recAuxName i) (lvl :: b.lvls))
                    (ps ++ motives ++ minors ++ idxs ++ dihs ++
                      #[b.sVal i vargs t, b.sProp i vargs t]))
              return (ty, val)
          return { auxType := recAuxType, auxValue := recAuxValue,
                   type := recType, value := recValue }
        out := out.push r
      return out
  unless grandOnly do
    addRecAuxs docCtx (lp :: b.us) <| results.mapIdx fun q r =>
      (recAuxName dIdxs[q]!, r.auxType, r.auxValue)
    for q in *...dIdxs.size do
      addDef (rawRecName dIdxs[q]!) (lp :: b.us) results[q]!.type results[q]!.value
      markElabAsElim (rawRecName dIdxs[q]!)

  -- 7.  `X.rec` for the `Prop` members the writer declared, out of the
  -- pre-block's own recursor.  A copy gets no recursor of its own, but a member
  -- whose recursion runs into one is recursing over the container, so the copy
  -- joins the group with the container's motive; step 10 puts the original back
  let mut propGroups : Array (Array Nat) := #[]
  for j in b.propIdxs do
    unless propGroups.any (·.contains j) do
      propGroups := propGroups.push
        (← b.propsBehind (← getConstInfoRec (mkRecName (preName b.members[j]!.name))))
  let closeUp (grp seed : Array Nat) : Array Nat := Id.run do
    let mut keep := seed
    let mut grew := true
    while grew do
      grew := false
      for j in keep do
        for cc in b.members[j]!.ctors do
          for k in b.fieldKinds cc.kinds do
            if let .recur m := k then
              if b.members[m]!.isProp && grp.contains m && !keep.contains m then
                keep := keep.push m; grew := true
    return keep
  let wanted (j : Nat) : Bool :=
    !copyNames.contains b.members[j]!.name && (!grandOnly || grandFree.contains j)
  -- not every `Prop` member has a derivable recursor: a constructor with a data
  -- field the conclusion's indices do not reach cannot have that field put back
  -- at its subtype
  let buildProps (rep : Nat) (keep : Array Nat) : TermElabM (Option BridgeCtx.PropRecs) := do
    let some s ← BridgeCtx.propRecs? b lp rep keep | return none
    let ok ← attempted `Mumi.indind "no recursor for the `Prop` members" <|
      forallBoundedTelescope b.members[0]!.type b.numParams fun ps _ =>
        BridgeCtx.addPropRecs { b, ps, copies := #[] } s rawRecName
    return if ok then some s else none
  let mut propRecs : Array BridgeCtx.PropRecs := #[]
  for grp in propGroups do
    let gKeep := closeUp grp (grp.filter wanted)
    if gKeep.isEmpty then continue
    match ← buildProps grp[0]! gKeep with
    | some s => propRecs := propRecs.push s
    | none =>
      -- whose fault it was, asked one member at a time and with the environment
      -- put back after each, so that asking costs nothing
      let mut ok : Array Nat := #[]
      for j in gKeep do
        if ok.contains j then continue
        let sub := closeUp grp #[j]
        let env ← getEnv
        let stands := (← buildProps grp[0]! sub).isSome
        setEnv env
        if stands then ok := ok ++ sub.filter (!ok.contains ·)
      unless ok.isEmpty || ok.size == gKeep.size do
        if let some s ← buildProps grp[0]! ok then propRecs := propRecs.push s
  let propBuilt := !propRecs.isEmpty

  -- 8. the bridge back to the originals
  unless p.copies.isEmpty do
    let built ← forallBoundedTelescope b.members[dIdxs[0]!]!.type b.numParams fun ps _ => do
      let copies : Array Copy := p.copies.filterMap fun (n, e) => do
        let idx ← b.memberIdx? n
        -- what is left of the lambda after the block's parameters are supplied is
        -- the fields of the constructor the nesting sat in, if it mentioned any
        let app := e.beta ps
        let numLocals := numHeadLams app
        let indName ← (peelLams numLocals app).getAppFn.constName?
        some { idx, name := n, indName, app, numLocals }
      let c : BridgeCtx := { b, ps, copies, copyRecs := copies.map (recName ·.idx) }
      -- the round trip is wanted exactly where a constructor of the writer's own
      -- has a copy-typed field, which is where the recursor has to transport
      let needed : Array Nat := Id.run do
        let mut out : Array Nat := #[]
        -- a data copy needs its own: the recursion over it is restated at the
        -- original, and reads the raw one at the round trip of the major premise
        for k in *...copies.size do
          unless b.members[copies[k]!.idx]!.isProp do out := out.push k
        for i in *...b.size do
          if (c.copyAt? i).isSome then continue
          -- and where a member the bridge restates is indexed by one: its
          -- recursor's motive travels the same way a field does
          unless rawMemberName b.members[i]!.name == b.members[i]!.name do
            for k in *...copies.size do
              if b.members[i]!.type.getUsedConstants.contains copies[k]!.name then
                unless out.contains k do out := out.push k
          for cc in b.members[i]!.ctors do
            if rawCtorName cc.name == cc.name then continue
            for k in b.fieldKinds cc.kinds do
              if let .recur m := k then
                -- a field at a `Prop` copy needs none: its round trip and itself
                -- are the same proof
                if b.members[m]!.isProp then continue
                if let some k' := c.copyAt? m then
                  unless out.contains k' do out := out.push k'
        return out
      -- the bridge is all or nothing: it adds declarations one by one, and a
      -- half-built one would collide with the plain names the fallback uses
      attempted `Mumi.indind "no bridge back to the originals" do
        -- `filterMap` drops a copy whose head is not a constant, which nothing
        -- denesting builds; a partial bridge would leave the block half-stated
        unless copies.size == p.copies.size do
          throwError "a copy of this block is not an application of an inductive"
        c.addOfOrig docCtx
        c.niceMembers rawMemberName
        c.addToOrig rawRecName
        c.niceCtors rawCtorName
        c.addRoundTrips needed rawRecName
        c.addBackTrips needed
        -- a `Prop` member the recursion over the whole block covers wants to be
        -- restated from *that* one and not from its split recursor, for the
        -- same reason it was covered: read off the grand one its motive takes
        -- the value the data recursion returned, and read off the split one it
        -- does not
        let mut grandDone : Array Nat := #[]
        for i in dIdxs ++ b.propIdxs do
          -- a copy is one of the writer's own types under a name of ours, so the
          -- recursion over it restates like any other member's; it is the one
          -- restatement the block can do without, so it is allowed to decline
          let optional := (c.copyAt? i).isSome
          -- the recursor over the whole block is the better one, and it is not
          -- always restatable over the originals; the split one always is
          let covered := grand && !(b.members[i]!.isProp && grandFree.contains i)
          let big ← if !covered then pure false else
            attempted `Mumi.indind
              "the recursor over the whole block does not restate over the originals" <|
              c.addNiceGrandRec i lp grandRecName recName rawCtorName grandFree grandDone
          if big then
            grandDone := grandDone.push i
          else unless b.members[i]!.isProp do
            let split := c.addNiceRec i lp rawRecName (recName i) rawCtorName
            if optional then
              discard <| attempted `Mumi.indind
                s!"`{recName i}` does not restate over the originals" split
            else
              split
        -- and the same for the `Prop` members, whose recursors name a copy
        -- exactly when their recursion runs into one
        for s in propRecs do
          for j in s.kIdxs do
            if (c.copyAt? j).isSome then continue
            let nm := if grandDone.contains j then inductName j else recName j
            discard <| attempted `Mumi.indind
              s!"`{nm}` does not restate over the originals" <|
              c.addNicePropRec s j rawRecName nm
        -- a copy whose recursion declined keeps the raw one under the plain
        -- name, which is where a reader of this block would look for it
        for i in dIdxs do
          if (c.copyAt? i).isNone then continue
          if rawRecName i == recName i then continue
          if (← getEnv).contains (recName i) then continue
          let info ← getConstInfo (rawRecName i)
          addDef (recName i) info.levelParams info.type
            (mkConst (rawRecName i) (info.levelParams.map Level.param)) (compile := false)
          markElabAsElim (recName i)
    unless built do
      -- a `Prop` recursor that never mentioned a copy is already the one that was
      -- wanted, and only owes the plain name; one that does mention a copy has no
      -- statement over the originals to fall back on, and stays unnamed
      if propBuilt then
        for j in propRecs.flatMap (·.kIdxs) do
          if copyNames.contains b.members[j]!.name then continue
          if rawRecName j == recName j then continue
          let info ← getConstInfo (rawRecName j)
          if info.type.getUsedConstants.any (copyNames.contains ·) then continue
          addDef (recName j) info.levelParams info.type
            (mkConst (rawRecName j) (info.levelParams.map Level.param)) (compile := false)
          markElabAsElim (recName j)
      -- the copies stay visible, and the plain names are the raw declarations --
      -- the members first, a constructor's written type naming them
      for m in b.members do
        let raw := rawMemberName m.name
        unless raw == m.name do
          addDef m.name b.us m.type (b.cst raw) (compile := false)
      for m in b.members do
        for c in m.ctors do
          let raw := rawCtorName c.name
          if raw == c.name then continue
          if m.isProp then
            addDecl (.thmDecl
              { name := c.name, levelParams := b.us, type := c.type, value := b.cst raw })
          else
            addDef c.name b.us c.type (b.cst raw)
      for q in *...dIdxs.size do
        let i := dIdxs[q]!
        if rawRecName i == recName i then continue
        addDef (recName i) (lp :: b.us) results[q]!.type
          (mkConst (rawRecName i) (lvl :: b.lvls))
        markElabAsElim (recName i)

  -- 9. the members that left the block rather than being erased with it, as the
  -- ordinary inductive types they already were.  After the bridge, because what
  -- they are stated over is the block the writer reads
  unless p.peeled.isEmpty do
    if !widen then
      addInd b.us b.numParams p.peeled
    else
      -- the inductive is declared one name over and the writer's name is given
      -- to a definition that unfolds to it, because the kernel writes `X.rec`
      -- for whatever it is handed as an inductive `X` and `X.rec` is wanted for
      -- the recursion over the whole block
      let names := p.peeled.map (·.name)
      let uses := p.peeled.map fun t =>
        let cs := t.ctors.foldl (fun acc c => acc ++ c.type.getUsedConstants) #[]
        (Array.range names.size).filter fun j => cs.contains names[j]!
      let mut groups : Array (Array Nat) := #[]
      let mut done : Array Nat := #[]
      while done.size < p.peeled.size do
        let rest := (Array.range p.peeled.size).filter (!done.contains ·)
        let ready := rest.filter fun a => uses[a]!.all fun c => c == a || done.contains c
        -- nothing is ready only when what is left is a cycle, and a cycle is a
        -- mutual inductive: it goes in whole
        if ready.isEmpty then
          groups := groups.push rest
          done := done ++ rest
        else
          for a in ready do groups := groups.push #[a]
          done := done ++ ready
      for g in groups do
        let toInd (e : Expr) : Expr := e.replace fun
          | .const n us =>
            if g.any (names[·]! == n) then some (.const (peelIndName n) us) else none
          | _ => none
        addInd b.us b.numParams <| g.map fun a =>
          let t := p.peeled[a]!
          { t with name := peelIndName t.name, type := toInd t.type
                   ctors := t.ctors.map fun c => { c with type := toInd c.type } }
        -- and left as a plain definition, not a reducible one, so that the
        -- namespace `.var` is looked up in is still the writer's: what resolves a
        -- dot stops at the head of the expected type, and unfolding it would send
        -- the reader to a constructor of `Tm._ind` that was never declared
        for a in g do
          let t := p.peeled[a]!
          addDef t.name b.us t.type (mkConst (peelIndName t.name) (b.us.map Level.param))
          -- the one place the head is `Tm._ind` regardless is a field of a
          -- constructor, since an inductive's own occurrences in its
          -- constructors are the one thing the kernel will not let a definition
          -- stand in for
          for c in t.ctors do
            modifyEnv (Lean.addAlias · (Name.str (peelIndName t.name) c.name.getString!) c.name)
      let total := b.size + p.peeled.size
      let keptAt := (Array.range total).filter (!p.peeledIdxs.contains ·)
      let pubRec (o : Nat) : Name :=
        match keptAt.idxOf? o with
        | some i => pubRecName i
        | none => p.peeled[(p.peeledIdxs.idxOf? o).getD 0]!.name ++ `rec
      for i in *...b.size do
        let ok ← attempt? `Mumi.indind
            m!"no recursor over the whole block for `{b.members[i]!.name}`" <|
          widenWithPeeled b p.peeled p.peeledIdxs pubRec (recName i) (pubRecName i)
            keptAt keptAt[i]!
        -- the recursion itself is not what failed, so the writer still gets a
        -- recursor under the name they reach for; it is only short of the
        -- motives of the members that left
        if ok.isNone then
          let info ← getConstInfo (recName i)
          addDef (pubRecName i) info.levelParams info.type
            (mkConst (recName i) (info.levelParams.map Level.param))
          markElabAsElim (pubRecName i)
      -- in the order the groups were declared in, so that a member whose fields
      -- reach another peeled one finds that one's widened recursor already there
      for g in groups do
        let coreAt := g.map (p.peeledIdxs[·]!)
        for k in g do
          let n := p.peeled[k]!.name
          discard <| attempt? `Mumi.indind
              m!"no recursor over the whole block for `{n}`" <|
            widenWithPeeled b p.peeled p.peeledIdxs pubRec (peelIndName n ++ `rec) (n ++ `rec)
              coreAt p.peeledIdxs[k]! (compile := false)

  -- 10. one recursor per member with the other members' motives discharged,
  -- which is the shape `induction` can drive, and the same one without its
  -- hypotheses, which is the shape `cases` can drive
  for i in *...b.size do
    let m := b.members[i]!
    if copyNames.contains m.name then continue
    let solo (s : Name) := m.name ++ s.appendAfter (if m.isProp then "P" else "D")
    discard <| attempt? `Mumi.indind m!"no one-motive recursor for `{m.name}`" <|
      addSoloElim b.numParams #[lp] m.isProp (pubRecName i) (solo `rec) (forCases := false)
        (evenIfWeaker := true)
    discard <| attempt? `Mumi.indind m!"no cases eliminator for `{m.name}`" <|
      addSoloElim b.numParams #[lp] m.isProp (pubRecName i) (solo `cases) (forCases := true)
  -- a member that left the block has a real recursion of its own already, but
  -- it is the kernel's, over `Tm._ind`, and every goal `induction` leaves says
  -- so
  if widen then
    for t in p.peeled do
      discard <| attempt? `Mumi.indind m!"no one-motive recursor for `{t.name}`" <|
        addSoloElim b.numParams #[lp] false (t.name ++ `rec) (t.name ++ `recD)
          (forCases := false) (evenIfWeaker := true)
      discard <| attempt? `Mumi.indind m!"no cases eliminator for `{t.name}`" <|
        addSoloElim b.numParams #[lp] false (t.name ++ `rec) (t.name ++ `casesD)
          (forCases := true)

  -- 10b. the course-of-values recursion over each data member, which is what
  -- the equation compiler looks for when it decides whether a definition by
  -- recursion over a member can be structural
  for i in b.dataIdxs do
    if copyNames.contains b.members[i]!.name then continue
    discard <| attempt? `Mumi.indind
        m!"no course-of-values recursion for `{b.members[i]!.name}`" <|
      emitBRecOn p preRecUnivs b i

  -- 11. injectivity of the data constructors, which has to come after the
  -- bridge: what is stated is stated about the type the writer wrote, and until
  -- step 10 has run that is not yet what the constructor's own type says
  let ofInjs ← copyNames.filterM fun n => return (← getEnv).contains (n ++ `ofOrig_inj)
  for (i, c) in b.ctorsOf b.dataIdxs do
    if copyNames.contains b.members[i]!.name then continue
    discard <| attempt? `Mumi.indind m!"no injectivity for `{c.name}`" <|
      addInjEqs b (ofInjs.map (· ++ `ofOrig_inj)) i c

  -- 12. what `match` is driven through, and the eliminators under the names an
  -- `inductive` answers to.  A `Prop` member has no view, so it gets those two
  -- and nothing else
  addViews b.numParams <| b.dataIdxs.filterMap fun i =>
    let m := b.members[i]!
    if copyNames.contains m.name then none else some (m.name, m.ctors.map (·.name))
  for i in b.propIdxs do
    let m := b.members[i]!
    unless copyNames.contains m.name || (← m.ctors[0]?.mapM fun c =>
        return ((← getEnv).find? c.name).any (·.isCtor)).getD true do
      addPropEliminators b.numParams m.name

/-! ## The entry point -/

/--
Whether some member's arity mentions a sibling -- the syntactic signature of
induction-induction, and the reason the block does not elaborate. -/
def viewsAreInductionInductive (views : Array InductiveView) : Bool := Id.run do
  let names := views.map (·.shortDeclName)
  let mentions (stx : Syntax) : Bool :=
    (stx.find? fun s => s.isIdent && names.contains s.getId.eraseMacroScopes).isSome
  for v in views do
    if let some t := v.type? then
      if mentions t then return true
    if mentions v.binders then return true
  return false

/-- Some members of the block, as the command they would have been on their own. -/
private def groupCommand (elems : Array Syntax) (g : Array Nat) : Syntax :=
  let es := g.map (elems[·]!)
  if es.size == 1 then es[0]!
  else mkNode ``Lean.Parser.Command.mutual
    #[mkAtomFrom es[0]! "mutual", mkNullNode es, mkAtomFrom es.back! "end"]

/-- Carry the docstrings the writer put on the block through to what was built. -/
def addViewDocStrings (views : Array InductiveView) : TermElabM Unit := do
  let some view0 := views[0]? | return
  Term.withDeclName view0.declName do
    for view in views do
      withRef view.declId do
        if (← getEnv).contains view.declName then
          addDocString' view.declName view.binders view.docString?
      for ctor in view.ctors do
        withRef ctor.declId do
          if (← getEnv).contains ctor.declName then
            addDocString' ctor.declName ctor.binders ctor.modifiers.docString?

/--
Run `x`, and if it does not go through cleanly leave nothing of it behind --
neither what it added to the environment nor what it complained about. -/
private def tentatively (x : CommandElabM Unit) : CommandElabM Bool := do
  let s ← get
  try
    x
    if (← get).messages.hasErrors then
      set s
      return false
    return true
  catch _ =>
    set s
    return false

/--
As `tentatively`, but handing back what went wrong rather than only that
something did. -/
private def tentatively? (x : CommandElabM Unit) : CommandElabM (Option MessageData) := do
  let s ← get
  let n := s.messages.reportedPlusUnreported.size
  try
    x
    let logged := ((← get).messages.reportedPlusUnreported.toList.drop n).filterMap fun m =>
      if m.severity matches .error then some m.data else none
    if logged.isEmpty then return none
    set s
    return some (MessageData.joinSep logged ", ")
  catch ex =>
    set s
    return some ex.toMessageData

/-- Instance the member from a constructor that can be applied, if one can. -/
def inhabitedFromCtor? (declName : Name) (ctors : Array Name) : MetaM (Option Declaration) := do
  let info ← getConstInfo declName
  let lvls := info.levelParams.map Level.param
  forallTelescopeReducing info.type fun ps concl => do
    -- an indexed family is inhabited at some indices and not others, so there
    -- is no one instance to state; `Inhabited` is for the members without them
    let .sort u := concl | return none
    let hyps ← ps.filterMapM fun p => do
      return if (← inferType p).isSort then some (`inst, BinderInfo.instImplicit,
        fun (_ : Array Expr) => mkAppM ``Inhabited #[p]) else none
    withLocalDecls hyps fun hs => do
      let target := mkAppN (mkConst declName lvls) ps
      for c in ctors do
        -- the fields are filled one at a time rather than all at once: a
        -- constructor may state a later field's type in terms of an earlier
        -- field, and then the value chosen for the earlier one is part of it
        let mut ty ← ctorTypeAt c lvls ps
        let mut args : Array Expr := #[]
        let mut ok := true
        repeat
          let .forallE _ d body _ := ← whnf ty | break
          let .some inst ← trySynthInstance (← mkAppM ``Inhabited #[d]) | ok := false; break
          let a ← mkAppOptM ``Inhabited.default #[d, inst]
          args := args.push a
          ty := body.instantiate1 a
        unless ok && (← isDefEq ty target) do continue
        let value ← mkLambdaFVars (ps ++ hs)
          (mkApp2 (mkConst ``Inhabited.mk [u]) target (mkAppN (mkConst c lvls) (ps ++ args)))
        let type ← mkForallFVars (ps ++ hs) (mkApp (mkConst ``Inhabited [u]) target)
        return some (.defnDecl {
          name := declName ++ `instInhabited, levelParams := info.levelParams
          type := implicitPrefix ps.size type, value := implicitPrefix ps.size value
          hints := .abbrev, safety := .safe })
      return none

/-- `deriving` on an induction-inductive block, asked for twice over. -/
private def applyDeriving (views : Array InductiveView) (requireDeriving : Bool) :
    CommandElabM Unit := do
  let mut processed : NameSet := {}
  for view in views do
    for classView in view.derivingClasses do
      let className ← liftCoreM <| classView.getClassName
      unless processed.contains className do
        processed := processed.insert className
        let env ← getEnv
        let declNames := views.filterMap fun v =>
          if v.derivingClasses.any (·.cls == classView.cls) && env.contains v.declName then
            some v.declName
          else
            none
        if declNames.isEmpty then continue
        -- a peeled member never went through the erasure, so it is an inductive
        -- like any other and its handlers are applied to it directly -- to the
        -- inductive behind it, where the member had to give up its own name so
        -- that the block could keep `X.rec`
        let peelOf (n : Name) : Option Name :=
          match env.find? n with
          | some (.inductInfo _) => some n
          | _ => match env.find? (peelIndName n) with
                 | some (.inductInfo _) => some (peelIndName n)
                 | _ => none
        let (peeled, declNames) := declNames.partition (peelOf · |>.isSome)
        unless peeled.isEmpty do
          withRef classView.ref <| classView.applyHandlers (peeled.filterMap peelOf)
        if declNames.isEmpty then continue
        let pres := declNames.filterMap fun n =>
          if env.contains (preName n) then some (preName n) else none
        -- all of them at once is what a handler wants for a family it can see is
        -- one, but a handler that cannot do one of them takes the rest down with
        -- it, so what it turns down as a group is offered again one at a time
        unless pres.isEmpty do
          unless ← tentatively (classView.applyHandlers pres) do
            for p in pres do
              unless ← tentatively (classView.applyHandlers #[p]) do
                trace[Mumi.indind] "nothing to derive `{className}` for on `{p}`"
        -- a member a constructor can instance is instanced from it, and only
        -- what is left over goes the delta route
        let declNames ← if className != ``Inhabited then pure declNames else
          declNames.filterM fun n => do
            let some view := views.find? (·.declName == n) | return true
            let ctors := view.ctors.map (·.declName)
            let some decl ← runTermElabM fun _ => inhabitedFromCtor? n ctors | return true
            liftCoreM <| addAndCompile decl
            -- `registerInstance`, not `addInstance`: the former also sets the
            -- instance-reducible transparency that the `instance` command sets,
            -- and a plain `def` of a class type is warned about without it
            runTermElabM fun _ =>
              Lean.Meta.registerInstance (n ++ `instInhabited) .global (eval_prio default)
            return false
        if declNames.isEmpty then continue
        let note := m!"A data member of an induction-inductive block unfolds to a wrapper \
          around its pre-type, so `deriving` reaches it only through an instance that wrapper \
          has -- `DecidableEq`, `Repr` and `Hashable` are given one, and a class that is not \
          can be derived for the wrapper itself, which the hint above names"
        -- the delta route reports by logging as readily as by throwing, and a
        -- logged error is how a route declines, so a caller that has said it
        -- would rather have the block runs it where the log can be undone
        let delta (ns : Array Name) : CommandElabM Unit :=
          runTermElabM fun _ => for n in ns do
            Term.processDefDeriving classView (← mkConstWithLevelParams n)
        withRef classView.ref do
          if requireDeriving then
            try delta declNames
            catch ex => logError m!"{ex.toMessageData}\n\nNote: {note}"
          else
            -- one member at a time: putting the state back to swallow the error
            -- would otherwise take back the members that did derive with it
            for n in declNames do
              if let some why ← tentatively? (delta #[n]) then
                logWarning m!"{why}\n\nNote: {note}"

/-- The views of the members of a `mutual` block, with their modifiers elaborated. -/
def elemViews (elems : Array Syntax) : CommandElabM (Array InductiveView) := do
  let inductives ← elems.mapM fun stx => do
    let modifiers ← elabModifiers ⟨stx[0]⟩
    pure (modifiers, stx[1])
  let elabs ← runTermElabM fun _ => inductives.mapM fun (m, s) => mkInductiveView m s
  return elabs.map (·.view)

/-- Elaborate an induction-inductive block by erasing its proof fields. -/
def elabInductionInductive (elems : Array Syntax) (requireIndInd := false)
    (requireDeriving := true) : CommandElabM Unit := do
  let views ← elemViews elems
  if requireIndInd && !viewsAreInductionInductive views then
    throwError "No member's arity names a sibling, so reading this block as an \
      induction-induction would not change what it means"
  -- whether a run peeled anything, so that a failure knows whether there is a
  -- second reading of the block to fall back on
  let peeled ← IO.mkRef false
  -- and, when there is no reason left to be here, the groups to hand back to
  -- Lean instead, in the order it has to read them
  let split ← IO.mkRef (none : Option (Array (Array Nat)))
  let go (peel : Bool) : CommandElabM Unit := do
    runTermElabM fun vars => do
      emit (← withRaw views vars fun r => do
        -- no two members depend on each other, so the block is a sequence of
        -- ordinary declarations: each one is Lean's to read on its own, and
        -- erasing them would only cost them `cases`, `injection` and `deriving`
        if peel && mumi.separate.get (← getOptions) then
          if let some order := separationOrder? r then
            split.set (some (order.map (#[·])))
            throwError "this block is Lean's to read"
        let r ← if peel then markPeeled r else pure r
        peeled.set (!r.peeled.isEmpty)
        -- what stays may no longer be induction-inductive at all: the arity
        -- that named a sibling can have been the peeled member's own
        unless r.peeled.isEmpty do
          let core := (Array.range views.size).filter (!r.peeled.contains ·)
          unless viewsAreInductionInductive (core.map (views[·]!)) do
            split.set (some #[core, r.peeled])
            throwError "this block is Lean's to read"
        let env0 ← getEnv
        let r ← try denestRaw r catch ex => do
          -- the scan throws before anything is stubbed, but a later step might not
          setEnv env0
          trace[Mumi.indind] "lowering this block without denesting it: {ex.toMessageData}"
          pure r
        prepareCore r)
      addViewDocStrings views
    applyDeriving views requireDeriving
  -- peeling is an improvement and not a requirement, so a block it does not
  -- suit is read again without it
  let s ← get
  try
    go true
    if (← get).messages.hasErrors && (← peeled.get) then
      set s
      go false
  catch ex =>
    match ← split.get with
    | some groups =>
      set s
      -- in dependency order, since a later group is stated over an earlier one.
      -- Lean's to accept or not, and if not there is still the erasure to fall
      -- back on
      unless ← tentatively (groups.forM fun g => elabCommand (groupCommand elems g)) do
        set s
        go false
    | none =>
      unless ← peeled.get do throw ex
      set s
      go false

/-- Elaborate a *nested* inductive whose denesting is one the kernel refuses. -/
def elabNestedInductive (elems : Array Syntax) (requireBridge := false)
    (requireDeriving := true) : CommandElabM Unit := do
  let views ← elemViews elems
  -- one `runTermElabM`, as in `elabInductionInductive`: the plan is built with
  -- the members stubbed as scratch axioms, and the info trees that come out of
  -- that world have to be merged in the same pass as the ones `emit` records,
  -- or a hover over a field whose type is a member of the block is left
  -- pointing at a constant that never made it into the environment
  runTermElabM fun vars => do
    let p ← withRaw views vars fun r => do
      let r ← denestRaw r
      if r.names.size == views.size then
        throwError "This inductive has no nested occurrence to denest"
      -- a copy whose lambda goes past the block's parameters stands for a
      -- family, one member per value of a field of the constructor it sat in
      let atLocal := r.copies.any fun (_, e) => numHeadLams e > r.numParams
      unless r.arities.any (mentionsNames r.names ·) || atLocal do
        throwError "Denesting this inductive neither makes it induction-inductive \
          nor needs a constructor's field as an index"
      prepareCore r
    emit p
    -- the bridge is all or nothing, so one copy answers for all of them
    if requireBridge then
      if let some (n, _) := p.copies[0]? then
        unless (← getEnv).contains (n ++ `ofOrig) do
          throwError "This block came out with `{n}` visible rather than the type it \
            copies; `set_option trace.Mumi.indind true` says why"
    addViewDocStrings views
  applyDeriving views requireDeriving

end Mumi.IndInd
