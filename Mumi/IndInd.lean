/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Mumi.Lowering
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

`Fresh`'s arity mentions `Ctx`.  This is a different obstruction from the one
`Mumi.Lowering` lifts.  Universe heterogeneity is a *check* on an elaborated
block; here the block does not elaborate at all, because Lean elaborates every
member's arity before any member is in scope, so `Ctx` in `Fresh`'s arity is an
unknown identifier.  Collapsing the block to one universe does not help.

## The narrow class

We handle the case where the block is **narrow**: every field of a data
constructor whose type mentions a `Prop` member is itself a proof.  Then those
fields can be *erased*.  A data member's arity may mention the block as well, and
where it does the index is *deleted* -- see "What is allowed" below.  The example
above needs no deletion, its induction-induction running only through `Fresh`, so
erasing the proofs leaves an ordinary, non-induction-inductive block:

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

Being a function is what makes the encoding cheap: `Ctx._wf (.snoc Γ x)` *is*
`Ctx._wf Γ ∧ Fresh._pre x Γ`, definitionally, so "inversion" is `And.left` and
`And.right` and no inversion lemmas have to be generated.  One conjunct per
recursive field (the sub-term is well formed) and one per erased field (the
proof it carried).

The constructors are then definitions rather than constructors, and the
recursor is written by structural recursion on the pre-type with the
well-formedness proof threaded through:

```lean
def Ctx.recAux {C : Ctx → Sort u} (nil : C Ctx.nil)
    (snoc : (Γ : Ctx) → (x : String) → (h : Fresh x Γ) → C Γ → C (Ctx.snoc Γ x h)) :
    (Γ₀ : Ctx._pre) → (w : Ctx._wf Γ₀) → C ⟨Γ₀, w⟩
  | .nil,          _ => nil
  | .snoc Γ₀ x,    w => snoc ⟨Γ₀, w.1⟩ x w.2 (Ctx.recAux nil snoc Γ₀ w.1)

def Ctx.rec {C : Ctx → Sort u} .. (Γ : Ctx) : C Γ :=
  Ctx.recAux nil snoc Γ.val Γ.property
```

Both iota rules hold by `rfl`, and the encoding adds no axioms.  That rests on
the same two things the heterogeneous lowering rests on: definitional proof
irrelevance, which collapses the `_wf` proofs, and definitional eta for
structures, which gives `⟨Γ.val, Γ.property⟩ ≡ Γ`.

`recAux` is written by structural recursion rather than as a `Ctx._pre.rec`
application for the reason spelled out in `Mumi.Lowering`: the code generator
compiles no recursor application, so the direct term would be `noncomputable`
and so would everything downstream.  Lean's own `Structural.structuralRecursion`
does the work; if it cannot see that the definition terminates, that is an
error at the point of the block rather than a silent fallback.

A `Prop` member's recursor needs none of that machinery, because `Fresh` *is*
`Fresh._pre` at the `.val`s of its indices.  What is wrong with `Fresh._pre.rec`
is only the world its motive and minors are stated in, so it is run at the
transported motive `fun Γ₀ h => ∀ w, C ⟨Γ₀, w⟩ h` -- a statement about every way
of making `Γ₀` well-formed -- and the result applied to the major premise's own
indices, where `⟨Γ.val, Γ.property⟩ ≡ Γ` again closes it.  A minor that was
handed a data field in the pre-world has to put it back at its subtype, and the
proof for that is read off the conclusion's `_wf`: being a conjunction over the
constructor's recursive and erased fields, it contains the well-formedness of
everything the constructor was built from.  See `addPropRecs`.

## What is allowed

* Any number of data members and any number of `Prop` members, and they need
  not share a universe.  The data members become one mutual pre-block, which the
  kernel's same-universe rule applies to -- so the pre-block is emitted through
  `Mumi.Lowering`, whose whole job is lifting that rule.  The two passes compose
  in that order and are independent: erasure never looks at a universe, and the
  lowering never sees an arity that mentions the block.  See `emitPreData`.

  What the composition cannot buy is the rules underneath the one being lifted.
  Data members that recurse into *one another* still have to agree, since an
  edge puts one universe at or below the other and a cycle makes them equal; and
  a field still has to fit inside the member it is a field of.
* Parameters, shared by the whole block as `mutual` already requires, and
  auto-bound implicits.
* Universe parameters, declared or auto-bound, shared by the whole block as
  Lean's own `mutual` requires.  A *data* member may not sit at a bare `Sort u`,
  though: it is encoded as a subtype, and `Subtype` lands in `Sort (max 1 u)`,
  which is `Sort u` again only when `u` is visibly non-zero.
* A member may leave its resulting type out -- `inductive Tree where` -- and it
  is read as `Type`.  Lean would put a metavariable there and solve it from the
  fields, but a metavariable cannot go into the scratch axiom that puts the
  member in scope for its siblings, and the guess would be baked into their
  fields before it was known (`List Tree` picks up `List.{0}`).  So the guess is
  fixed, and a block it is too small for is rejected with the type to write.
* Members named under one another -- `TreeNested.WF` beside `TreeNested`.  A
  member's constructors are known by name, so nothing has to be read off a
  prefix.
* Indices on any member, a *data* member's included -- `Ty : Ctx → Type` beside
  `Ctx`, and `Tm : (Γ : Ctx) → Ty Γ → Type` beside both.  An index of a data
  member that mentions the block is *deleted*: the pre-world has no `Ctx` to
  state `Ty` at, so `Ty._pre` carries no index and the well-formedness puts a
  `Ctx._pre` back.  To be stateable at all such an index has to be a data
  member's own type applied outright, what is left of it once the deletion has
  run must name no other index, and an index that *stays* may mention none that
  goes.  See `checkDropped`.
* A constructor of such a member either gives a deleted index as a field of its
  own or *builds* it, out of its fields and the block's data constructors, and
  the well-formedness carries an equation saying in the pre-world what was built.
  It may build more than one, build one out of another, and give one field as
  several of them; a field standing at an index that reads one the constructor
  built is kept and its index built out of it, which is the same thing said
  twice.  See `Block.transportBuilt`, which is what carries an alternative from
  the constructor's reading of all this to the recursion's.
* Recursive fields may be indexed and infinitary -- `(f : (n : Nat) → Vec n)` --
  provided the binders `ys` mention no member of the block.  `(f : Ctx → Ctx)`
  is out, and not because of positivity: a pre-world `Ctx._pre` cannot be turned
  back into a `Ctx` without its well-formedness proof, so there is nothing to
  hand `f`.
* A member that takes no part in the erasure *leaves the block* instead of going
  through it, and is declared as the ordinary inductive it already is once the
  members it is stated over are there.  Two kinds qualify, for opposite reasons:
  a proposition nothing else in the block is stated with, which the erasure has
  nothing to offer, and a data member nothing else in the block reaches, which
  has nothing to offer the erasure.  See `markPeeled`.

  The second kind is settled by a fixpoint rather than by one pass, because a
  member the block still reaches may be reached only by another member that is
  itself leaving.  `Sub.ext` reads a `Tm`, so `Tm` cannot go while `Sub` is
  there; `Sub` goes, and then `Tm` can follow.  Members leave until no more can,
  subject to what stays being induction-inductive still -- otherwise there is no
  recursor of ours left to widen -- and to what leaves not being
  induction-inductive among itself, since that is handed to the kernel as it
  stands.

  What a member gains by leaving is everything an inductive has and an encoded
  member does not -- `match` above all, and with it the equation compiler,
  `noConfusion`, `injection` and `contradiction`.  What the block loses is
  nothing: `widenWithPeeled` puts the departed member's motive back into every
  recursor, so `Ctx.rec` over a block one of whose members left is the same
  recursion, motive for motive, as it would have been.  That is what Lean itself
  does for a `mutual` block that is not really mutual, and a member that can be
  lifted out is exactly that case.

  A *data* member that leaves is declared one name over, as `X._ind`, and the
  writer's name is given to a definition unfolding to it -- see `peelIndName` --
  because the kernel writes `X.rec` for whatever it is handed as an inductive
  `X`, and `X.rec` is wanted for the block's recursion.  Its constructors are
  declared under the writer's names all the same, since nothing requires a
  constructor to sit in its own type's namespace, and `X._ind.c` is aliased to
  `X.c` so that dot-notation resolves against either head.

## Nested inductives that denest to this

Nobody writes an induction-inductive block by accident, but Lean will build one
for you.  A *nested* inductive is denested by specialising the nesting type
constructor to the block, and if the type being specialised is itself a family
indexed by another type being specialised, the enlarged block is
induction-inductive.  The smallest interesting case is a tree that is
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
`Tree.WF` and `Tree.WFWith`, whose arities are indexed by the copy of `Tree`.
So the block Lean would have to check is the five-member block

```lean
mutual
inductive RecWFTree                             : Type
inductive RecWFTree.nested_WFTree_1             : Type
inductive RecWFTree.nested_Tree_2               : Type
inductive RecWFTree.nested_WF_3     : RecWFTree.nested_Tree_2 → Prop
inductive RecWFTree.nested_WFWith_4 : RecWFTree.nested_Tree_2 → List Nat → Prop
end
```

and that is exactly a narrow-class induction-inductive block: only the `Prop`
members' arities mention the block.  `denestRaw` builds it, `prepareCore`
lowers it, and `Mumi.Declaration` reaches this path only after Lean itself and
the heterogeneous retry have both failed.

`Mumi.Denest` does the same job for the blocks `Mumi.Lowering` takes, but it
cannot be reused: it rewrites an `Input` over member *free variables*, and only
at the head of an application, whereas here the members are constants and a
copied constructor can turn up in an *index* -- `nested_WFWith_4.empty` has
`nested_Tree_2.empty` as its first index -- so the rewrite has to be
structural.  Both differences are small and both are load-bearing.

Two shapes are worth naming because they cost the copies more than an extra
constructor.  A nesting type that is itself part of a `mutual` family is copied
with the whole family, since a copy of one member alone would still mention the
others.  And a nesting whose parameters mention a *field* of the constructor it
sits in -- `OkFam LocalsII n` for a field `n` -- stands for a whole family of
originals, so its copy gains `n` as an index and every one of the copy's
constructors takes it as a leading field.  Both survive the erasure: the copy is
a member like any other by the time `prepareCore` sees it, and neither its
family nor its extra index is anything the erasure has to know about.

## What this does not do

* Section `variable`s.
* An erased field's type may not mention a *data* member as a constant.
  `(h : Fresh x Γ)` is fine -- `Fresh x Γ` unfolds to `Fresh._pre x Γ.val`, so
  erasing it is definitionally invisible -- but `(h : Γ = Γ')` is not: `Γ = Γ'`
  and `Γ.val = Γ'.val` are different propositions, and the encoding would have
  to transport between them.
* A data constructor's field mentioning a `Prop` member must be a proof; that is
  the "narrow" in narrow class.
* The constructors of a data member that *stayed* in the block are `def`s, so
  `match` on them does not work and there is no `noConfusion` at the name one
  would reach for.  (A member that left is a real inductive and has both; this
  bullet is about the ones the erasure carried.)  What they do
  have is `inj` and a `@[simp] injEq`, stated as the ones a real inductive's
  constructors get -- at a field at a denested copy too, where what the equation
  reduces to is the copy's `ofOrig` of each side and it is that copy's own
  `ofOrig_inj` that reads it back.  Two *different* constructors are told apart
  by a simproc rather than by a theorem, so `simp` settles those too --
  `contradiction` and `injection` do not, since what they reach for is the
  `noConfusion` of whatever the member unfolds to, which is `Subtype`'s.  Reason with
  `induction Γ using Ctx.rec with | nil => .. | snoc Γ x h ih => ..`; a
  bare `induction` or `cases` destructs the subtype and leaks `Ctx._pre` into
  the goal.  A recursor with a *single* motive is registered as the `induction`
  tactic's default for its member, so a bare `induction` does work on those --
  but a block whose members recurse into each other has a motive apiece, and
  those stay `using`-only, as a mutual block's do in vanilla Lean.
* A bare `cases` on a `Prop` member works only where the motive does not depend
  on the indices, and otherwise fails ("dependent elimination failed"), because
  what it reaches for is `Fresh._pre`'s `casesOn`, stated over the pre-type.
  `Fresh.rec` itself is derived and is stated over the originals, so
  `induction x, Γ, h using Fresh.rec with | nil .. | snoc ..` is the way in; its
  indices are listed as targets, as they would be for any indexed family.
* A `Prop` member that joins the recursion over the whole block is eliminated
  into `Prop`, even where its own recursor would have gone into any sort.  Its
  hypothesis rides in a bundle beside a data member's, and what a bundle holds
  its `Prop` half in is a conjunction.  A subsingleton judgement therefore
  trades large elimination for the other half of the recursion -- the one that
  lets a data function be declared with the proposition's motive on it.
* A block that both names a `Prop` member at a deleted index -- `Wf.base :
  (Γ : Ctx) → Ok Γ → Wf Γ (Ty.base Γ)`, where `Ty.base` deleted the `Γ` -- and
  deletes an index built out of a constructor -- `Ty.pi : (Γ : Ctx) → (A : Ty Γ)
  → Ty (Γ.snoc A) → Ty Γ`.  What a deleted index arrives under settles both, and
  the two want opposite things of it: the first wants the whole bundle, so that
  the proposition about that index is there to state a hypothesis with, and the
  second wants the motive's value alone, which is the only half that can be
  rebuilt out of a minor.  Either on its own goes through, and both are tried.
* Two copies that need each other -- an original nested inside another
  original -- have no order to build the bridge in.  That is reported rather
  than worked around, and the bridge is dropped as a whole, as it is whenever
  any step of it fails: the plain names are then the raw declarations,
  `RecWFTree.mk` reads `RecWFTree.nested_WFTree_1 → RecWFTree` again, and the
  block is exactly what it was before the bridge was attempted.
* A *data* member leaves the block only where the block holds no propositions.
  A recursor over a block that has them bundles each `Prop` motive with the value
  the data recursion returned at the index it is stated over, and neither the
  order the motives come in nor a hypothesis at a proof field survives being
  restated from outside, so a data member's leaving would cost the block that
  shape.  It leaves only where what stays is still induction-inductive, too:
  otherwise Lean is handed the remainder as ordinary declarations, and a
  recursor the kernel wrote is not ours to widen.
* A data member that left prints as `X._ind` in the types of its own
  constructors, and there only -- `Tm.lam : .. → Tm._ind (Γ.snoc A) B → Tm._ind Γ
  (Ty.pi Γ A B)`.  An inductive's own occurrences in its constructor types are
  the one thing the kernel will not let a definition stand in for.  The
  recursors, the eliminators `induction` and `cases` reach for, and the goals
  they leave all read `Tm`.
* A recursor over a data member that left is a recursor application, which the
  code generator compiles none of, so it is published beside an `unsafe`
  companion written out of `casesOn` and a self-call and wired up with
  `setImplementedBy`.  Nothing is trusted by this: the definition the kernel
  checked is the one every proof reads, and a companion that does not go through
  leaves it `noncomputable`, which is what it would have been anyway.  A group of
  data members that left *together*, being genuinely mutual with one another,
  gets no companion -- the kernel recursor it would be written out of has a
  motive apiece -- so its recursor is `noncomputable`.
-/

public section

namespace Mumi.IndInd

open Lean Lean.Meta Lean.Elab Lean.Elab.Command
open Lean.Elab.MultiuniverseInductive
  (addDef addInd reroot motiveNames markElabAsElim addSoloElim attempt?
    attempted freshLevelNames shortName exposeInduct)

/-- Why a block fell back from the recursor it would rather have had. -/
initialize registerTraceClass `Mumi.indind (inherited := true)

/-! ## Names -/

/-- The erased pre-type of member `n`. -/
def preName (n : Name) : Name := n ++ `_pre

/-- `X._wf : ∀ idxs, X._pre idxs → Prop`, well-formedness on the pre-type. -/
def wfName (n : Name) : Name := n ++ `_wf

/--
`X._ind`, the inductive a member that left the block is really declared as, in
the case where `X` itself has to stay a definition.

The kernel writes `X.rec` for whatever it is handed as an inductive named `X`,
and that is the one name a member of a `mutual` block cannot give up: what the
writer expects to find there is a recursion over the whole block, motives and
all.  So the type goes one name over and `X` becomes a definition that unfolds
to it.  See step 11 of `emit`.
-/
def peelIndName (n : Name) : Name := n ++ `_ind

/--
The recursor of the data pre-block that ranges over *all* of it, which is what
`X._wf` recurses with.

When the pre-block goes in as one mutual inductive that is the kernel's own
`X._pre.rec`.  When its members disagree about their universe it goes in through
`Mumi.Lowering` instead, which splits it into one ordinary block per component
and offers the whole-block recursor under `mutualRec` -- so that is the name to
reach for.  The two differ in how many motive universes they take, which
`widenPreRecLevels` settles.
-/
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
  A value of the member `mem` that is also the resulting type's index at position
  `pos`; dropped, and given back as an argument of `_wf`.

  Two things are dropped when data is indexed by data, and this is the second of
  them.  The index goes from the *arity*, because the pre-types are one mutual
  inductive and no member of one may appear in another's arity; the field that
  was that index goes with it, because there is nothing left for it to index.
  Both come back from `_wf`, an erased proof out of its conjuncts and a deleted
  index out of its arguments.
  -/
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
  after the parameters: exactly those whose type mentions the block.

  Empty unless the block indexes data by data, which is the one thing that puts
  a member of the erased pre-block into another's arity.  A `Prop` member's
  indices are never dropped -- the propositions become a *second* pre-block,
  declared after the data one, so their arities may name it freely.
  -/
  dropped : Array Nat := #[]
  ctors  : Array CtorSpec
  deriving Inhabited

structure Block where
  members : Array MemberSpec
  /-- The block's parameters, which lead every member's arity and every field telescope. -/
  numParams : Nat
  /--
  The universe parameters, shared by every declaration the lowering makes.  A
  member that does not mention one still carries it, exactly as Lean's own
  mutual inductives do, so that one list of levels serves the whole block.
  -/
  us : List Name := []
  /--
  The name a constructor is really emitted under.

  A constructor whose type mentions a denesting copy comes out under a hidden
  name, and only gets the one that was written when the bridge at the end gives
  it back.  So anything built before then that has to *name* a constructor has
  to ask for the hidden one -- the plain name does not exist yet, and when it
  does it will take the original where this one takes the copy.  The identity is
  the right answer everywhere the block was not denested.
  -/
  rawCtor : Name → Name := id
  /--
  The name a member is really emitted under.

  The same story as `Block.rawCtor`, one level up.  A `Prop` member whose *arity*
  runs over a denesting copy -- `Ok : List Ctx → Prop`, where the block nests at
  `List Ctx` -- cannot be given the writer's name until the bridge is there to
  say what the written arity means, so it too comes out hidden and the bridge
  composes it with `ofOrig` under the plain name.  Only propositions: a data
  member indexed by a copy is a block denesting turns down outright, since the
  index would have to travel out and back and no transport of a nesting is the
  identity.
  -/
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
The name a constructor was written under, given the one it is emitted as.

The inverse of `Block.rawCtor`, and the identity on everything that is not a
renamed constructor.  Every question the block answers about a name -- what its
pre-world counterpart is, which fields it keeps, whether it belongs to the block
at all -- is asked of the written name, so a name that arrives raw comes back
through here first.
-/
def Block.unRaw (b : Block) (n : Name) : Name := Id.run do
  for m in b.members do
    for c in m.ctors do
      if c.name != n && b.rawCtor c.name == n then return c.name
  return n

/--
A constructor's type at the block's parameters, named the way the block is really
emitted.

The written type is what the block was declared with, and a constructor that
*builds* one of its own indices names another constructor there: `U.mk (v : List
T) : U (.node v)` has `T.node` in it.  With a denesting copy in the block that
name is not the one `T.node` is emitted under, and everything the recursors are
built out of is built before the bridge at the end gives it back.  So the type
is read here rather than off the spec, and the recursors name what exists.
-/
def Block.ctorType (b : Block) (c : CtorSpec) (ps : Array Expr) : MetaM Expr :=
  return b.toRaw (← instantiateForall c.type ps)

/-- The block's universe parameters as levels. -/
def Block.lvls (b : Block) : List Level := b.us.map Level.param

/-- A constant of the block, at the block's own universe parameters. -/
def Block.cst (b : Block) (n : Name) : Expr := mkConst n b.lvls

/--
Member `i` as a constant, named the way it is really emitted.

Anything stated in the raw world -- where the copies are the types -- has to
reach a member by this and not by the name the writer wrote, for the same reason
`Block.toRaw` exists.  The two agree except at a `Prop` member the bridge is
going to restate.
-/
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
  -- member the way it was emitted, and everything asked about it -- what its
  -- pre-type is, which arguments it keeps -- is the same question either way
  b.members.findIdx? fun m => m.name == n || b.rawMember m.name == n

/-- The index of the member whose *pre-type* is named `n`. -/
def Block.preIdx? (b : Block) (n : Name) : Option Nat :=
  b.members.findIdx? (preName ·.name == n)

/--
Where the minor premise for the constructor `n` sits in a recursor over the
members `idxs`: their constructors, in order, flattened.  Out of range if `n` is
not a constructor of one of them, which is a caller's mistake and reads better
as a panic at the minor than as a silently wrong one.
-/
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
The member a minor premise's induction hypothesis about this field is stated
at, and `none` for a field there is no hypothesis about.

A recursive field gets one because the recursion has just run at it.  A
*deleted* one gets the very same hypothesis for the opposite reason: it is an
index, so the alternative binds the index and not the field, and the recursion
was handed a hypothesis about it on the way in rather than computing one.  Which
of the two produced it is the recursion's business; the minor sees a hypothesis
about every field whose type is a member of the block either way, and that is
what the eliminator of an inductive-inductive definition is supposed to give.

So this is deliberately not `recPositions`, which stays the narrower question of
which fields the recursion calls itself at.  Anything reading the minor's
telescope wants this one, and the two answers differ exactly on the blocks the
erasure deletes an index of.
-/
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
index was a field at all.

`none` means the constructor *builds* that index -- `Tm.lam` ends in
`Tm Γ (Ty.pi Γ A B)`, whose second index is no field of it -- and then the
erasure has an equation to state rather than a field to drop.
-/
def deletedField? (kinds : Array FieldKind) (pos : Nat) : Option Nat := Id.run do
  for k in *...kinds.size do
    if let .deleted _ p := kinds[k]! then
      if p == pos then return some k
  return none

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
The block's own view of an expression, rewritten to the pre-world: members and
their constructors are re-rooted, and whatever the pre-world drops goes with
them -- a member's deleted indices, and a data constructor's erased and deleted
arguments.
-/
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
Whether `n` is a member of the block, or a constructor of one, among those
members `keep` selects.

The test is by exact name, not by prefix: a member may perfectly well be
declared *under* another member's name -- `TreeNested` beside `TreeNested.WF` --
and then a prefix test would read every mention of the predicate as a mention of
the tree.  Nothing else of the block exists yet to be mentioned, since the whole
of it is in scope only as the scratch axioms this list names.
-/
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
Put the block's own constants at one shared list of levels.

Each member is stubbed as an `axiom` over every universe name in scope, so a
reference to it elaborates to `Ctx.{?u, ?v}` with one metavariable per name and
only those the reference actually constrains are assigned.  But the block is
uniformly polymorphic in its parameters, so the right level list is always the
same one -- which also disposes of the metavariables nothing constrained.

`lvls` being empty is not a reason to skip this.  A block that uses no universe
parameters written under a `universe u v w` the rest of the file needs is still
stubbed over `u`, `v` and `w`, and every reference to a member still comes back
carrying three metavariables that nothing will ever assign.
-/
def normLevels (names : Array Name) (lvls : List Level) (e : Expr) : Expr :=
  e.replace fun s =>
    match s with
    | .const n _ => if names.contains n then some (.const n lvls) else none
    | _ => none

/-! ## Members applied to their indices

The data member `X` at indices `args` is the subtype of `X._pre args` cut out by
`X._wf args`.  Everything that crosses between the two worlds goes through these
five, so they are the only place the shape of the encoding is written down.

`args` are always the pre-world's: `Block.valArgs` is what puts them that way,
and it is called once, where the member is defined.  Below that they only ever
travel, so there is no second place to remember the difference. -/

/--
The pre-types of the indices the member `i` dropped, at the parameters `ps`,
each as a function of the indices the pre-type kept.

`X._wf` takes these back as arguments, and a motive over `X._pre` has to end in
them, so they are read once from the arity and used in both places.  A dropped
index's pre-type may name the kept ones -- a context carrying its own length
makes `Ty : (n : Nat) → Ctx n → Type` delete a `Ctx n`, whose pre-reading is
still `Ctx._pre n` -- and the readers do not agree about what binder `n` is, so
what comes back is abstracted over the kept indices and every reader says which
ones it means.  `Block.dropTysAt` is that, and is what everyone actually calls.

They may name nothing *else*, which is what `checkDropped` is for and why one
lambda over the kept indices is the whole of the dependency: no dropped index
binds for another, so this stays an array and never becomes a telescope.
-/
def Block.dropTys (b : Block) (i : Nat) (ps : Array Expr) : MetaM (Array Expr) := do
  if b.members[i]!.dropped.isEmpty then return #[]
  forallTelescope (← instantiateForall b.members[i]!.type ps) fun idxs _ =>
    (b.dropIdxs i idxs).mapM fun x => do
      mkLambdaFVars (b.keptIdxs i idxs) (b.tr (← inferType x))

/-- `Block.dropTys` read at a member's indices, of which only the kept ones are
looked at.  `idxs` counts from the member's first index, not its first argument. -/
def Block.dropTysAt (b : Block) (i : Nat) (ps idxs : Array Expr) : MetaM (Array Expr) := do
  return (← b.dropTys i ps).map (·.beta (b.keptIdxs i idxs))

/-- `ts[0] → .. → ts[n-1] → e`, with nothing depending on anything. -/
def mkArrows (ts : Array Expr) (e : Expr) : Expr :=
  ts.foldr (fun t acc => .forallE `a t acc .default) e

/--
The sort the motives of the `X._wf` recursion all land in.

A motive ends in the member's deleted indices and then `Prop`, so it lands in the
`max` of their sorts and `Type`, which is `Prop`'s own.  A member that deleted
nothing lands in `Type` flat, and while the deleted indices are at `Type` too --
`Ctx._pre : Type` -- that is one and the same sort for every member of the block,
which is why this is `Type` almost always.
-/
def Block.wfMotiveLevel (b : Block) (ps : Array Expr) : MetaM Level := do
  let mut l := Level.one
  for i in b.dataIdxs do
    -- a level names no binder, so the arity's own are as good as anyone's
    let ls ← forallTelescope (← instantiateForall b.members[i]!.type ps) fun idxs _ => do
      (← b.dropTysAt i ps idxs).mapM getLevel
    for x in ls do
      l := (mkLevelMax l x).normalize
  return l

/--
The one further argument every motive of the `X._wf` recursion ends in when they
would not otherwise agree, and what fills it in.

A block at `Type 1`, or one under a universe parameter, deletes indices from
above `Type`, so a motive that ends in one lands higher than a motive that ends
in nothing.  One recursion has one motive sort, so all of them are brought up to
the highest by ending in an argument nothing ever reads.  Empty in the ordinary
case, where they agree already and the recursion is the shorter for it.
-/
def wfPad (l : Level) : Array Expr × Array Expr :=
  if l == Level.one then (#[], #[])
  else (#[mkConst ``PUnit [l]], #[mkConst ``PUnit.unit [l]])

/--
A member's indices as `X._wf` binds them: a deleted one at its pre-type, and
every other one the arity's own binder, unchanged.

Only the deleted ones are rebound, at the kept ones the arity already gave.  The
rest are left alone so that no substitution is needed: what they might have
mentioned is a deleted index, and `prepareCore` refuses that.
-/
def Block.withValIdxs {α} [Inhabited α] (b : Block) (i : Nat) (ps idxs : Array Expr)
    (k : Array Expr → MetaM α) : MetaM α := do
  let dropped := b.members[i]!.dropped
  if dropped.isEmpty then return ← k idxs
  let dts ← b.dropTysAt i ps idxs
  let mut decls : Array (Name × (Array Expr → MetaM Expr)) := #[]
  for q in *...dropped.size do
    let n ← idxs[dropped[q]!]!.fvarId!.getUserName
    decls := decls.push (n, fun _ => pure dts[q]!)
  withLocalDeclsD decls fun ds => do
    let mut out := idxs
    for q in *...dropped.size do
      out := out.set! dropped[q]! ds[q]!
    k out

/-- `X._pre args`, with the indices the pre-type dropped taken out of `args`. -/
def Block.preApp (b : Block) (i : Nat) (args : Array Expr) : Expr :=
  mkAppN (b.cst (preName b.members[i]!.name)) (b.keptArgs i args)

/--
`X._wf args`, a predicate on `X._pre args`.

`_wf` keeps every index the arity had, because a deleted one is exactly what the
pre-term no longer says and the predicate has to say instead.
-/
def Block.wfApp (b : Block) (i : Nat) (args : Array Expr) : Expr :=
  mkAppN (b.cst (wfName b.members[i]!.name)) args

/-- `{t : X._pre args // X._wf args t}`, which is what `X args` unfolds to. -/
def Block.subtype (b : Block) (i : Nat) (args : Array Expr) : Expr :=
  mkApp2 (mkConst ``Subtype [b.members[i]!.level]) (b.preApp i args) (b.wfApp i args)

def Block.sVal (b : Block) (i : Nat) (args : Array Expr) (e : Expr) : Expr :=
  mkApp3 (mkConst ``Subtype.val [b.members[i]!.level]) (b.preApp i args) (b.wfApp i args) e

def Block.sProp (b : Block) (i : Nat) (args : Array Expr) (e : Expr) : Expr :=
  mkApp3 (mkConst ``Subtype.property [b.members[i]!.level]) (b.preApp i args) (b.wfApp i args) e

def Block.sMk (b : Block) (i : Nat) (args : Array Expr) (v p : Expr) : Expr :=
  mkApp4 (mkConst ``Subtype.mk [b.members[i]!.level]) (b.preApp i args) (b.wfApp i args) v p

/-! ## Recursive fields

A recursive field has type `∀ ys, M args` for a member `M`.  `ys` is empty in
the ordinary case and non-empty for an infinitary one such as
`(f : (n : Nat) → Vec n)`; the three functions below are what make the two
cases the same code. -/

/--
If `ty` is `∀ ys, M args` for some member `M`, hand `k` the binders, the member's
index and its arguments.  Otherwise answer `none`.
-/
def Block.withRecTarget? {α} (b : Block) (ty : Expr)
    (k : Array Expr → Nat → Array Expr → MetaM α) : MetaM (Option α) :=
  -- a copy of `Subtype` carries its predicate as a parameter, so its proof
  -- field arrives as `(fun t => P t) val`; what a field *is* is its beta-normal
  -- form, and the kernel reads it that way too
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

/--
The pre-world image of `x : ty`.  A term of a data member's type loses its
well-formedness proof; everything else, including a term of a `Prop` member's
type, passes through, because `P args` is *defined* as `P._pre args'`.
-/
partial def Block.preImage (b : Block) (x ty : Expr) : MetaM Expr := do
  let r? ← b.withRecTarget? ty fun ys i args => do
    if b.members[i]!.isProp then return x
    else mkLambdaFVars ys (b.sVal i (← b.valArgs i args) (mkAppN x ys))
  return r?.getD x

/--
A member's arguments moved from the real world to the pre-world.

Everything the encoding does with a member's arguments it does with them stated
as the pre-world states them, which for all but a deleted index is no difference
at all: the other arguments never mention the block, so the two worlds spell
them the same way.  A deleted index is a subtype element in one world and its
value in the other, and this is the one place that gap is crossed.  The recursion
is on the arity: a deleted index is itself a member application, whose own
deleted indices have to be crossed before it can be.
-/
partial def Block.valArgs (b : Block) (i : Nat) (args : Array Expr) : MetaM (Array Expr) := do
  if b.members[i]!.dropped.isEmpty then return args
  let mut out := #[]
  for k in *...args.size do
    if b.keepsArg i k then out := out.push args[k]!
    else out := out.push (← b.preImage args[k]! (← inferType args[k]!))
  return out

end

/--
A field's type moved to the pre-world, with the fields around it replaced by the
pre-world stand-ins `news`.

A member application keeps its real head.  What the pre-world does to one is
exactly to drop arguments, and the readers of this are the ones that still need
them all: `Block.withRecTarget?` finds the member there, and the arguments it
hands over are pre-world terms already.  Everywhere else, and under the head,
`Block.tr` has been through.

Real means real in this world, where the copies are the types, so the head is
the name the member is really emitted under -- the reading is only ever wanted
before the bridge exists to give a renamed proposition the plain one.

The order of the two halves is the whole point.  A stand-in can be a term like
`A.val`, whose type argument names the real world -- `Ty._wf ((Γ.snoc A).val)` --
and `Block.tr` reaching *that* would rewrite the `Γ.snoc A` buried in it into a
pre-world constructor applied to real terms, which is not a term at all.  So the
type is translated while it is still purely real, and the stand-ins go in
afterwards, already across.
-/
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
`Block.subTy`'s reading of every field of a constructor the pre-world keeps one
for one, at the pre-world terms `xs` standing for them.

A `Prop` constructor is such a constructor: nothing of a `Prop` member is erased
or deleted, so its two field telescopes line up and each real field type can be
read at the stand-ins for the fields before it.  Worth reading at all for the
usual reason -- `Block.subTy` keeps the member's real head, and so goes on
naming an index the pre-type deleted, which is the only form `X._wf` has to be
stated in.

The type is read in the raw naming, this being a raw-world reading throughout
and the writer's names not all being defined when it is wanted.
-/
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
carry, as the two lists a pre-block's recursor wants.

A motive over a pre-type is built by `withWfIdxs`, which takes the erased
indices first and the proofs about them last, after the major premise -- there
is nothing to say about an index until the recursor has one.  So a call has to
supply them in two pieces with the major premise between, and only the data
indices contribute a proof.  Both ends read the same list, so it is built once.
-/
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
The `Prop` members behind a pre-block recursor's members, in the recursor's own
order.

A mutual recursor's motives and minors run over the whole pre-block in the order
the pre-block was declared in, which is not in general the order the members
were written in, and every constructor of every member gets a minor whether or
not the caller has any use for it.  Reading the order off `all` is the only way
to line the two up.
-/
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
`Block.subTy`'s reading of it -- which is the only one in which a deleted index
is still there to be said.
-/
def Block.wfOfSub (b : Block) (y subTy : Expr) : MetaM Expr :=
  b.withRecTarget subTy fun ys i args =>
    mkForallFVars ys (mkApp (b.wfApp i args) (mkAppN y ys))

/--
The conjuncts of a constructor's well-formedness, in the order `_wf` states
them: the recursive fields first, each saying its sub-term is well formed, then
the erased fields, each being the proposition that field carried, and last the
equations `eqs`, one for each index the constructor builds rather than takes as
a field.  `projConj` reads positions off this order, so it is the same one
`recPositions` and the erased fields come out in.

`imgs` is indexed by field and only has to be filled in at the recursive
positions; that is the shape `withPreFields` hands over.
-/
def Block.wfConjs (b : Block) (kinds : Array FieldKind) (imgs : Array (Option Expr))
    (subTys : Array Expr) (eqs : Array Expr := #[]) : MetaM (Array Expr) := do
  let mut conjs : Array Expr := #[]
  for k in recPositions kinds do
    conjs := conjs.push (← b.wfOfSub imgs[k]!.get! subTys[k]!)
  for k in *...kinds.size do
    if kinds[k]! == .erased then conjs := conjs.push (← b.preTy subTys[k]!)
  return conjs ++ eqs

/--
The equations a constructor's *built* indices impose: one for each index the
pre-type deleted that the constructor does not simply take as a field.

`Tm.lam` ends in `Tm Γ (Ty.pi Γ A B)`, and `Tm._pre.lam` says nothing about
either index -- that is what deleting them means.  `Tm._wf` takes both back as
arguments, and where the first is a field the constructor *is*, so that binding
the argument binds the field, the second is one it *builds*.  Nothing then ties
the argument to the term unless the well-formedness says so itself, and this is
the conjunct that says it: `Ty._pre.pi a b = A`.  The recursor transports along
it to get from the argument the recursion was given back to the term the
constructor wrote, and at a real `Tm.lam` the two are the same term, so the
proof is `rfl` and the transport computes away.

`dvals` are the pre-world readings of the member's deleted indices in arity
order, and `olds`/`news` move the constructor's fields across.  Each answer says
which of those indices it is about.
-/
def Block.builtEqs (b : Block) (i : Nat) (kinds : Array FieldKind) (concl : Expr)
    (olds news dvals : Array Expr) : MetaM (Array (Nat × Expr)) := do
  let dropped := b.members[i]!.dropped
  let idxArgs := b.idxArgs concl.getAppArgs
  let mut out : Array (Nat × Expr) := #[]
  for q in *...dropped.size do
    if (deletedField? kinds dropped[q]!).isSome then continue
    out := out.push (q, ← mkEq ((b.tr idxArgs[dropped[q]!]!).replaceFVars olds news) dvals[q]!)
  return out

/--
The shape of `X._wf`'s hypothesis about a recursive field: what its motive says
at a pre-term of the member the field recurses into.

A member that deleted indices has a motive that ends in them, so the hypothesis
does too: knowing a pre-term is well formed means knowing it at each of the
contexts it could be read in, and nothing here has said which one is meant yet.
-/
def Block.ihTy (b : Block) (ps pad : Array Expr) (subTy : Expr) : MetaM Expr :=
  b.withRecTarget subTy fun ys mm args => do
    let dts ← b.dropTysAt mm ps (b.idxArgs args)
    mkForallFVars ys (mkArrows (dts ++ pad) (mkSort Level.zero))

/-- `∀ ys, ih ys dels`, the same conjunct written with a recursor's own hypothesis. -/
def Block.ihConj (b : Block) (ih : Expr) (padVal : Array Expr) (subTy : Expr) : MetaM Expr :=
  b.withRecTarget subTy fun ys mm args =>
    mkForallFVars ys (mkAppN ih (ys ++ b.dropArgs mm args ++ padVal))

/-! ## Conjunctions

`X._wf` at a constructor is a right-associated conjunction, one conjunct per
recursive field followed by one per erased field, and `True` when there are
none.  These three functions are the only place that shape is fixed; the
constructors build it, the recursor takes it apart, and they have to agree. -/

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
Walk a constructor's fields, rebuilding the telescope in the pre-world: the
dropped fields go and everything else keeps its place with its type moved across
by `Block.subTy`, the earlier fields replaced by their pre-world counterparts.

`k` receives the substitution the walk built -- the original fields on the left
and their pre-world stand-ins on the right, which is what moves an expression
across -- an image per *original* field (`none` for a dropped one), and each
field's type as `Block.subTy` reads it, which is with the member applications
left at their real names.

The pre-world stand-in of a *deleted* field is not bound here; the caller
supplies it, in `olds` and `news`, because the two callers disagree about what
it is.  `X._wf` binds it as a fresh pre-term of the member, while a recursor's
alternative has a real one to hand and takes its value.

A field the pre-world leaves alone -- a `Nat`, a parameter's value, anything the
block does not reach into -- is its own stand-in and gets no new binder.  That
is worth the equality test on its own account, since it is most of the fields of
most constructors, but it is also what lets a deleted index's *type* be written
down before the walk runs: a pre-type that mentions such a field mentions the
very binder the arity gave it, and not one this walk has yet to invent.
-/
partial def withPreFieldsAux {α} [Inhabited α] (b : Block) (kinds : Array FieldKind)
    (xs : Array Expr) (i : Nat) (olds news : Array Expr) (imgs : Array (Option Expr))
    (subTys : Array Expr)
    (k : Array Expr → Array Expr → Array (Option Expr) → Array Expr → MetaM α) : MetaM α := do
  if h : i < xs.size then
    let x := xs[i]
    let ty ← inferType x
    let sub ← b.subTy olds news ty
    if kinds[i]!.isDropped then
      withPreFieldsAux b kinds xs (i + 1) olds news (imgs.push none) (subTys.push sub) k
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
def keptImages (imgs : Array (Option Expr)) : Array Expr := imgs.filterMap id

/--
The real terms an alternative reads a member's deleted indices at, in arity
order.

An index the constructor takes as a field is that field, and wants no binder of
its own.  One it *builds* -- `Tm.lam` ends in `Tm Γ (Ty.pi Γ A B)`, whose second
index is no field of it -- has nothing to be, so the alternative binds it, at
the type the arity gives it.  They are bound in order and each at the ones
before it, because a deleted index's type may well name them: `Tm`'s second
index is a `Ty` of its first.
-/
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
read the arity at.

A deleted index's type may name the indices that stayed as well as the deleted
ones before it -- `Tm`'s second index is a `Ty n Γ`, whose `n` is an index the
erasure keeps -- and the arity states it at the binders the arity gave them,
which are nobody's here.  So the type is abstracted over both and applied to the
constructor's readings: the kept indices come from the conclusion, because that
is where the recursion was called, and the deleted ones from what the
alternative has bound so far.
-/
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
a field: `Tm.lam` ends in `Tm Γ (Ty.pi Γ A B)`, and its second index is no field
of it.

An alternative is handed the index the recursion was called at, while the
constructor has a reading of its own, and all the two have in common is the
equation `Block.builtEqs` puts into the well-formedness.  So the alternative
binds the index -- there being no field for it to be -- and everything it wants
to say at the constructor's reading has to be carried over by that equation.
-/
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
One constructor of a data member, read in the pre-world: what an alternative of
either recursor starts from.

`xs` are the fields at the originals, `imgs` their pre-world stand-ins one per
original field, and `olds`/`news` the substitution that moves an expression
across.  `head` is the pre-world constructor applied to the fields it kept, `wc`
a local proof that `head` is well formed, `conjs` the conjuncts that proof
splits into, and `cIdxs` the conclusion's arguments moved across.

`real` is the constructor's own fields put back: a recursive one paired with
its share of `wc`, an erased one read off `wc`, a plain one passed through, a
deleted index left exactly as it was.  Both recursors hand `real` to the *same*
minor premises, so they have to agree about it down to the order -- which is why
it is built in one place.

`dels` are those deleted indices, which is the one thing here that is a real
term rather than a pre-world one: it is the member the pre-block could not
mention, and a minor premise binds it back.  An index the constructor *builds*
has no field to be, and `built` says which ones those are and what they were
bound at; see `BuiltIdx`.

`realIdxs` is `cIdxs` again, on the other side: the conclusion's arguments with
the fields put back as `real` has them.  A motive is stated in the real world
and nowhere else, so a caller that has to name one at the constructor's own
indices reads them here, and everything that builds a term reads `cIdxs`.
-/
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
Read the constructor `c` of member `i` in the pre-world and run `k` on it,
under the binders it introduces: the pre-world fields, the deleted indices and
the well-formedness `wc`, all of which `k` is expected to abstract over.  An
index the constructor builds contributes two binders of its own, which `k` finds
in `AltFields.built` and has to abstract over instead of the index.
-/
def Block.withAlt {α} [Inhabited α] (b : Block) (i : Nat) (c : CtorSpec) (ps : Array Expr)
    (k : AltFields → MetaM α) : MetaM α := do
  let kinds := b.fieldKinds c.kinds
  forallTelescope (← b.ctorType c ps) fun xs cconcl => do
    let dropped := b.members[i]!.dropped
    b.withDels i ps xs (b.idxArgs cconcl.getAppArgs) kinds fun dels => do
      -- what the pre-world sees of a deleted index is its value, and that is
      -- what the substitution carries.  Only an index that is a field is
      -- substituted *for*: one the alternative just bound stands for nothing
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
        let head := mkAppN (b.cst (b.preOf c.name)) (ps ++ keptImages imgs)
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
              real := real.push (projConj conjs wc (recPos.size + nera))
              nera := nera + 1
          let realIdxs := cconcl.getAppArgs.map (·.replaceFVars xs real)
          k { kinds, xs, olds, news, imgs, subTys, cIdxs, realIdxs, head, wc, conjs, real,
              recPos, dels, built }

/--
An alternative's body carried from the index the constructor built to the one
the recursion was called at.

`core` is what the recursion returns at the constructor, and it returns it at
the constructor's own reading of the index -- `Ty.pi Γ A B`.  The alternative
was handed an index of its own instead, and all the two have in common is the
equation the well-formedness states between them.  So the motive is abstracted
over the index's *value*, `core` proves it at the constructor's reading, and
that equation moves it to the alternative's.  Both well-formedness proofs travel
inside the abstraction -- the index's and the term's -- because the motive's own
arguments are made out of them.

A constructor that builds no index gets `core` back untouched, and even one that
does pays nothing at a real term: there the two readings are the same term, the
equation proves `x = x`, and the kernel takes the transport away again before
the minor premise is reached.

A constructor may build more than one index -- `Sub.ext` of a substitution
between two contexts builds both of them -- and the well-formedness has an
equation for each, so the transports are done one after another.  Every one of
them is stated at the indices the ones before it already moved, which is why the
goal is abstracted over all of the built values at once and then transported a
value at a time rather than each transport being closed off on its own.

`goal` says what the alternative concludes at and `core` produces it, both of
them given the member's real indices, the pre-world reading of the same
arguments, and the term's well-formedness.  The two recursions want different
things there -- a split alternative concludes at a motive and a grand one at a
bundle -- and the transport is the same either way, so it is asked rather than
assumed.

The body is asked for under those three rather than handed in ready-made
because the grand recursion's bundle has the well-formedness *in its type*: the
bundle at the alternative's reading of the index is not the bundle at the
constructor's, and the one to build is the constructor's.  A split alternative
concludes at a motive, which is stated in the real world and has no proof in
it, so it ignores all three and builds the same body either way.
-/
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
  -- `Tm (Γ.snoc A) (Ty.base (Γ.snoc A))`, whose second index is a type in the
  -- context the first one is -- so its own arguments have to be read at
  -- whatever that one has been moved to so far and not at where it ends up.
  -- Its pre-*type* names no index at all, which `checkDropped` saw to, so only
  -- the well-formedness and the subtype element are affected
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
partial def withImplicits {α} [Inhabited α] (decls : Array (Name × (Array Expr → TermElabM Expr)))
    (k : Array Expr → TermElabM α) : TermElabM α :=
  go 0 #[]
where
  go (i : Nat) (acc : Array Expr) : TermElabM α := do
    if h : i < decls.size then
      withLocalDecl decls[i].1 .implicit (← decls[i].2 acc) fun x => go (i + 1) (acc.push x)
    else
      k acc

/-! ## Elaborating the headers, with the members as scratch axioms

The members' arities have to be elaborated with the *other* members in scope,
which is exactly what `mutual` refuses to do.  So each member is declared as a
temporary `axiom` as soon as its own arity is known, inside
`withoutModifyingEnv`; the constructors are elaborated against those, and the
data constructors become axioms too so that `.snoc` in a `Prop` constructor's
type resolves the way the writer meant.  The environment is then rolled back and
the real declarations are made under the very same names, so the expressions we
extracted stay meaningful.

Elaborating the arities needs an order, and the writer is under no obligation to
supply one, so they are elaborated by a worklist: go round the members, keep
whichever succeed, and stop when a round adds nothing.  A genuine circularity --
`A`'s arity mentioning `B` and `B`'s mentioning `A` -- fails every round, and is
reported with the error of the last attempt.

Which universe parameters the block ends up with is not known until every
constructor has been read, so a stub is declared over every universe name in
scope at the time and `restub` moves the whole batch once the real list is
settled. -/

private def stubAxiomAt (levelParams : List Name) (name : Name) (type : Expr) :
    TermElabM Unit := do
  -- A scratch axiom is never part of the environment anybody sees: `withRaw`
  -- elaborates the whole block inside `withoutModifyingEnv`, and every real
  -- declaration made afterwards is kernel-checked on its own.  So the kernel is
  -- told to stand aside here, which is not merely an economy.  A stub is added
  -- as soon as its type is elaborated, before the block's universe parameters
  -- are known, so its type still carries a level metavariable for every
  -- universe name in scope that nothing has constrained -- and `Elab.async`
  -- checks in a background task, which `restub`'s rewind cannot call off, so
  -- the complaint would surface as an error about a name that no longer exists.
  withOptions (debug.skipKernelTC.set · true) do
    addDecl (.axiomDecl { name, levelParams, type := ← instantiateMVars type, isUnsafe := false })

private def stubAxiom (name : Name) (type : Expr) : TermElabM Unit := do
  -- every universe name in scope, so the stub is well-formed whichever ones its
  -- type turns out to use; `normLevels` puts the references straight afterwards,
  -- and `restub` moves the axioms themselves once the block's own list is known
  stubAxiomAt (← Term.getLevelNames).reverse name type

/--
Add a batch of scratch axioms, each after whatever else in the batch it mentions.

The order the names were first stubbed in is not one their types respect: a
copy's arity may name a copy interned after it, and re-stubbing starts from an
environment where none of the batch exists.  So they go in by worklist, as the
arities themselves do.
-/
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
Auto-binding, as Lean's own header elaboration does it: universe names such as
the `u` of `Type u` are collected into the level names, and unbound identifiers
become implicit binders.  A *member's* name is forbidden from auto-binding, or
the worklist below would silently accept a sibling it has not stubbed yet by
turning it into an implicit variable.
-/
private def withAuto {α} (views : Array InductiveView) (k : TermElabM α) : TermElabM α :=
  Term.withAutoBoundImplicitForbiddenPred (fun n => views.any (·.shortDeclName == n)) <|
    Term.withAutoBoundImplicit k

/--
`∀ params idxs, Sort l`, together with how many of those binders are parameters.

A member that gives no resulting type at all -- `inductive Tree where` -- is read
as `Type`.  Lean would put a universe metavariable there and solve it from the
constructors' fields, but a metavariable cannot go into the scratch axiom that
puts this member in scope for its siblings, and a wrong guess there would be
baked into the siblings' fields (`List Tree` picks up `List.{0}`).  So the guess
is fixed, and `checkInferredArity` below rejects a block the guess is too small
for rather than quietly mis-elaborating it.
-/
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

/--
Make the leading `n` binders implicit.  A constructor's parameters are implicit
even where the type's are explicit -- `List.nil : {α : Type u} → List α` -- and
that is what lets `.nil` resolve against an expected type; the recursor's are
implicit for the same reason `List.rec`'s are.
-/
partial def implicitPrefix (n : Nat) (e : Expr) : Expr :=
  let keep (bi : BinderInfo) := if bi == .instImplicit then bi else .implicit
  match n, e with
  | 0, _ => e
  | n + 1, .forallE nm d body bi => .forallE nm d (implicitPrefix n body) (keep bi)
  | n + 1, .lam nm d body bi => .lam nm d (implicitPrefix n body) (keep bi)
  | _, _ => e

/--
Make the `n` binders that start at position `lo` implicit, leaving the ones
before them as they are.

A recursor's indices are implicit in the major premise -- `Nat.le.rec` ends
`{a : Nat} → (t : n.le a) → motive a t`, whatever `Nat.le`'s own index binder
looked like -- and a recursor's indices sit after its motives and minors, not
at the front where `implicitPrefix` reaches.
-/
partial def implicitRange (lo n : Nat) (e : Expr) : Expr :=
  match lo, e with
  | 0, _ => implicitPrefix n e
  | lo + 1, .forallE nm d body bi => .forallE nm d (implicitRange lo n body) bi
  | lo + 1, .lam nm d body bi => .lam nm d (implicitRange lo n body) bi
  | _, _ => e

/--
A recursor's binders, as Lean leaves its own: the parameters implicit, the
motives and minors as they were declared, the indices implicit again, and the
major premise the only thing left to write.
-/
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
            -- the member is in scope only as its scratch axiom, and that is
            -- declared over every universe name that was around when its arity
            -- was read.  An empty level list is the right length only when there
            -- were none; anywhere else it makes a constructor whose type is
            -- ill-formed the moment another member's constructor mentions it,
            -- which is exactly what a `Prop` member indexed by this one does.
            -- Which levels they are is not knowable yet and does not matter,
            -- since `normLevels` moves every reference to the block's own list;
            -- but writing the names in would make the block depend on universes
            -- it does not use, so they go in as metavariables
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
Everything that has to be built while the scratch axioms are still in the
environment.

`Meta.forallTelescope` looks each binder's type up -- `withNewLocalInstances`
asks `isClass?` about it -- so a telescope over a constructor's type only works
where the members are declared.  That is true of the scratch environment and
false of the one the real declarations go into, up until the member being
telescoped over has itself been added.  So the pre-world types, which are
telescoped from the original ones, are all built here, against scratch axioms
for the pre-types as well; everything from `X` itself onwards is built during
emission, by which point the constants it telescopes over are real.
-/
structure Plan where
  block : Block
  /-- The data members' pre-types, as one mutual inductive. -/
  preDataInds : Array InductiveType
  /--
  Whether those pre-types disagree about their universe, and so have to reach
  the kernel through `Mumi.Lowering` rather than as a single `addInd`.

  The whole-block recursor is then `X._pre.mutualRec` rather than `X._pre.rec`,
  and it takes a motive universe per component instead of one; `preDataRec` is
  where that difference is spent.
  -/
  preIsHeterogeneous : Bool := false
  /-- The `Prop` members' pre-types, as one mutual inductive. -/
  prePropInds : Array InductiveType
  /-- `X._wf`, per data member: its name, type and `X._pre.rec` body. -/
  wfDecls : Array (Name × Expr × Expr)
  /-- The members denesting added, and the original application each copies. -/
  copies : Array (Name × Expr) := #[]
  /--
  The members that left the block rather than going through the erasure, ready
  to be declared as they stand.  See `markPeeled` for which ones those are; they
  are stated over the block as the writer reads it, so they go in last of all.

  A data member among them is declared one name over, as `X._ind`, with `X`
  itself a definition unfolding to it, so that `X.rec` is free to be the
  recursion over the whole block.  See `peelIndName` and step 11 of `emit`.
  -/
  peeled : Array InductiveType := #[]
  /--
  Where each of those sat in the block as it was written, so that the recursors
  of the members that stayed can put them back in their places.  See
  `widenWithPeeled`.
  -/
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
  The members `denestRaw` added, and what each one is a copy of: a lambda over
  the block's parameters, and over any field of the constructor its parameters
  mentioned, giving the original application `I ps'` that the copy stands for,
  with the copy's own indices still to come.  Empty for a block somebody wrote.
  -/
  copies : Array (Name × Expr) := #[]
  /--
  The environment as it stood before the first scratch axiom was added, so that
  they can be re-declared once the block's universe parameters are known.  See
  `restub`.
  -/
  stubEnv : Option Environment := none
  /--
  The section variables in scope where the block was written, in scope order.
  Whichever of them the block turns out to use become its leading parameters;
  see `withSectionVars`.  Empty outside a section.
  -/
  vars : Array Expr := #[]
  /--
  The members that leave the block before the erasure sees it, by index.  See
  `markPeeled`: they are the members that take no part in what the erasure is
  for -- propositions nothing else in the block is stated with, and data members
  nothing else in the block reaches -- and they come out as inductives the
  writer would recognise instead.  Their types are left exactly as they were
  written -- denesting skips them, and so does everything after.
  -/
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
Mark the members that should leave the block rather than be erased with it.

Two kinds of member leave, for opposite reasons.  A proposition leaves when the
erasure has nothing to offer it; a data member leaves when it has nothing to
offer the erasure.  The comments through the body say which is which at each
step; the paragraphs here are about the first.

A proposition the rest of the block is never stated with -- no data member's
arity or field mentions it, and neither does any proposition that is itself
staying -- is a *consumer* of the block and not a part of it.  The erasure is
there to break the cycle between the data and the propositions inside it, and a
member outside the cycle gains nothing by going through: it can be declared
afterwards, over the members as the writer sees them, as the ordinary inductive
it already is.

That would be the better answer for every such member, and it is deliberately
not taken for every one.  A proposition the erasure *can* carry comes back with
a recursor over the whole block -- the data recursion and the proof in step
together -- which is worth more than the plain one it would get out here, and
blocks that have it were written for it.  So the peel is kept for the case where
the erasure has nothing to offer: a constructor with a field whose type is a
data member of the block, sitting at a position its own conclusion says nothing
about.  There is no well-formedness in reach for such a field -- see
`dataFieldPart` -- so the recursor cannot be stated at all, and until now the
member simply came out without one.

Nothing here is peeled unless it can be, either.  These types are declared after
the block and read against it, so a member whose type will be rewritten on the
way through -- because it mentions a nesting the block denests -- is left where
it is; what it would be declared over is a copy, which is the one thing the
writer must not be shown.
-/
def markPeeled (r : Raw) : TermElabM Raw := do
  let (isProp, _) ← memberLevels r.names r.arities
  -- a block of nothing but propositions gives the erasure nothing to keep and is
  -- refused for that, but the peel is not the erasure: the propositions that
  -- leave it may be all there was in the way, and then what stays is a block
  -- Lean can read.  So no early return on there being no data here
  let dataNames := (Array.range r.names.size).filterMap fun i =>
    if isProp[i]! then none else some r.names[i]!
  let propNames := (Array.range r.names.size).filterMap fun i =>
    if isProp[i]! then some r.names[i]! else none
  -- a constructor field whose type is the block's data, at a position the
  -- conclusion does not bind: the shape the erasure cannot state a minor for.
  -- A *proof* field of that shape is not one -- it travels erased and whole,
  -- and nothing has to be put back at a subtype for it -- so `h : a = b`
  -- between two members is no reason to peel anything
  let wants (i : Nat) : TermElabM Bool := do
    -- or an arity indexed by another of the block's propositions.  The erasure
    -- buys one crossing, from the data to the propositions, and not a second
    -- from the propositions to themselves -- `checkDataArities` turns such a
    -- member away outright -- whereas outside the block the index is a
    -- proposition like any other and there is nothing to arrange
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
  -- a data member nothing else in the block reaches at all is peeled too, and
  -- for the opposite reason: not that the erasure has nothing to offer it, but
  -- that it has nothing to offer the erasure.  What it gets instead is
  -- everything an inductive gets, `match` above all, and the members that stay
  -- lose nothing -- `widenWithPeeled` puts its motive back in their recursors.
  --
  -- Only in a block with no propositions in it.  A recursor over a block that
  -- has them bundles each `Prop` motive with the value the data recursion
  -- returned at the index it is stated over, and neither the order the motives
  -- come in nor a hypothesis at a proof field survives being restated from
  -- outside; a peeled data member would cost the block that shape
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
  -- a data member is peeled to gain it something, not to take the block apart.
  -- If what stays is no longer induction-inductive then Lean is handed the whole
  -- thing as two ordinary declarations instead, and the members that stay lose
  -- the peeled one's motive with nothing to put it back -- `widenWithPeeled`
  -- restates a recursor of ours, and one the kernel wrote is not ours to
  -- restate.  So then the data candidates go, and the propositions, whose peel
  -- was never about the shape of anybody else's recursor, are asked again
  let stillIndInd (keep : Array Nat) : Bool := keep.any fun i =>
    r.arities[i]!.getUsedConstants.any fun c => keep.any fun k => k != i && r.names[k]! == c
  if cand.any (!isProp[·]!) &&
      !stillIndInd ((Array.range r.names.size).filter (!cand.contains ·)) then
    cand := close (cand.filter (isProp[·]!))
  -- and now grow upwards.  A data member the block still reaches cannot leave,
  -- but the member reaching it may be leaving too, and then there is nothing
  -- holding it in after all: `Sub` reads a `Tm`, so `Tm` is no candidate to
  -- begin with, and once `Sub` is out it is one.  Taking them one at a time and
  -- asking again after each keeps the two things a peel owes.  What stays has to
  -- be induction-inductive still, since widening a recursor is only possible
  -- where the recursor is ours to widen; and what leaves must *not* be
  -- induction-inductive among itself, since `addInd` hands it to the kernel as
  -- it stands and the kernel is what cannot read such a block in the first place
  if peelData then
    let mut grew := true
    while grew do
      grew := false
      for j in *...r.names.size do
        if isProp[j]! || cand.contains j then continue
        if (Array.range r.names.size).any fun i => i != j && !cand.contains i && mentions i j then
          continue
        let c := cand.push j
        if !stillIndInd c &&
            stillIndInd ((Array.range r.names.size).filter (!c.contains ·)) then
          cand := c
          grew := true
  if cand.isEmpty then return r
  return { r with peeled := cand }

/--
The arity checks that depend on which members are still in the block.

Both of them are about the propositions, and both are things the peel can carry
away, so unlike the rest of the arity checks they wait until the constructors
have been read -- whether anything else is stated with a member is a fact about
those.  What is left over by then really is out of reach.

The second one is the interesting one.  The `Prop` members' erased pre-types are
one mutual inductive too, and no member of a mutual inductive may appear in
another's arity, so a `Prop` indexed by a `Prop` runs into the very rule the
block as a whole is here to lift, one level up: the erasure buys one crossing,
from the data to the propositions, and not a second from the propositions to
themselves.
-/
def checkStayingArities (names : Array Name) (arities : Array Expr)
    (isProp : Array Bool) : TermElabM Unit := owning do
  -- erasure keeps the data and rebuilds it as a subtype of what it kept, so a
  -- block with nothing but propositions gives it nothing to work on
  if isProp.all id then
    throwError "Every member of this induction-inductive block is a proposition; there is \
      nothing for the erasure to keep"
  let propIdxs := (Array.range names.size).filter (isProp[·]!)
  for j in propIdxs do
    for c in arities[j]!.getUsedConstants do
      if c != names[j]! then
        if let some k := propIdxs.find? (names[·]! == c) then
          throwError "The arity of `{names[j]!}` mentions `{names[k]!}`, which is another \
            proposition of the block.  Erasure sends the data members to one mutual \
            inductive and the propositions to a second one, and a mutual inductive's \
            members may not appear in one another's arities -- so a proposition may be \
            indexed by the block's data, but not by another of its propositions.  One \
            that nothing else in the block is stated with leaves the block before this \
            rule reaches it; this one is named by something that stays"

/--
The checks the arities alone settle.

They are made before any constructor is elaborated, so that a block erasure
cannot reach at all is turned away before its fields are read against members
that will never exist.

Every one of them says the same kind of thing -- this is an induction-inductive
block, and it is outside the narrow class -- so they are `Mumi.owning` errors:
worth reporting even when this is a retry whose failure would otherwise be
dropped, since the block really was recognised and really is out of scope.
-/
def checkDataArities (names : Array Name) (isProp : Array Bool)
    (levels : Array Level) : TermElabM Bool := owning do
  let dataIdxs := (Array.range names.size).filter (!isProp[·]!)
  -- The data members become one mutual pre-block, so the kernel's own
  -- same-universe rule applies to it.  Lifting that rule is exactly what
  -- `Mumi.Lowering` does, so members that disagree are not an error here but a
  -- decision: the pre-block is emitted through the lowering instead of straight
  -- through `addInd`.  `emitPreData` is the other half.
  --
  -- A copy's level may still be a metavariable: the nesting type was applied at
  -- one, and in a universe-polymorphic block nothing before now had to pin it
  -- down.  Unification is what pins it, so try it on every member before giving
  -- up on agreement -- a level left unassigned reaches the kernel as `Sort ?u`.
  -- Only levels that genuinely cannot be made to agree choose the other route.
  let mut heterogeneous := false
  for i in dataIdxs do
    unless ← isLevelDefEq levels[i]! levels[dataIdxs[0]!]! do
      heterogeneous := true
  -- a data member is encoded as a `Subtype`, which lands in `Sort (max 1 l)`.
  -- For `Type v` that is `Sort l` again; for a bare `Sort u`, which might yet
  -- be `Prop`, it is not, and the definition would not typecheck
  for i in dataIdxs do
    unless ← isLevelDefEq (mkLevelMax Level.one levels[i]!) levels[i]! do
      let s := toString (← ppExpr (mkSort levels[i]!))
      throwError "The data member `{names[i]!}` lives at `{s}`, which could still \
        be `Prop`.  It is encoded as a subtype, and `Subtype` lands one universe up from \
        `Prop`, so a data member's universe has to be visibly non-zero -- `Type v` rather \
        than `Sort v`"
  return heterogeneous

/--
Which of each member's indices its pre-type has to delete: the ones whose type
mentions the block.

That is the whole rule, and it is forced.  The data members become a single
mutual inductive, and no member of a mutual inductive may appear in another's
arity, so `Ty : Ctx → Type` is an arity the pre-block cannot state.  Deleting
the index is what lifts the rule; `X._wf`, which is a definition and under no
such rule, is where it goes.

A `Prop` member never deletes anything.  Its pre-type is declared *after* the
data one and is a separate mutual inductive, so it may name the data pre-types
in its arity as freely as it likes.
-/
def droppedIndices (b : Block) : MetaM (Array (Array Nat)) := do
  let mut out : Array (Array Nat) := #[]
  for m in b.members do
    if m.isProp then
      out := out.push #[]
    else
      out := out.push <| ← forallBoundedTelescope m.type b.numParams fun _ rest =>
        forallTelescope rest fun idxs _ => do
          let mut ds : Array Nat := #[]
          for p in *...idxs.size do
            if b.mentions (← inferType idxs[p]!) then ds := ds.push p
          return ds
  return out

/--
Whether the deletions `droppedIndices` asks for can be carried out.

Three things have to hold, and each of them is the price of a decision made
elsewhere.  A deleted index's type must *be* a data member's, because the
pre-world has to have a type to state it at, and only a member has a pre-type.
What is left of that type after the deletion -- `Ty._pre`, from `Ty Γ` -- may
name the indices that stayed but not the ones that went, because the deleted
indices are handed round as an array rather than as a telescope, and an array
has nowhere for one of its own entries to have been bound.  A `Ctx` carrying its
own length is fine, then: `Ty : (n : Nat) → Ctx n → Type` deletes a `Ctx n`
whose pre-reading `Ctx._pre n` names `n`, and `n` is an index that stayed.  And
an index that stays must not mention one that goes, because the one that stays
is left at the binder the arity gave it, and the one that goes is not.

Like the other arity checks these are `Mumi.owning`: the block really is an
induction-induction and really is outside what the erasure can state.
-/
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
          let some j ← b.withRecTarget? ty fun ys j _ => do
              unless ys.isEmpty do
                throwError "The index `{idxs[p]!}` of `{m.name}` binds arguments before \
                  reaching a member of the block, and the erasure has no pre-type to state \
                  it at:{indentExpr ty}"
              return j
            | throwError "The index `{idxs[p]!}` of `{m.name}` mentions the block without \
                being a member's type, so the erasure has no pre-type to state it \
                at:{indentExpr ty}"
          if b.members[j]!.isProp then
            throwError "The index `{idxs[p]!}` of `{m.name}` is a proof of \
              `{b.members[j]!.name}`, and the erasure keeps a proposition's proofs nowhere: \
              it is the propositions that are erased, so there would be nothing left to \
              index by{indentExpr ty}"
          if mentionsIdx (b.tr ty) (b.dropIdxs i idxs) then
            throwError "The index `{idxs[p]!}` of `{m.name}` still depends on another index \
              the erasure deletes, and the deleted indices are handed round as an array, in \
              which there is nowhere for one of them to have bound another:\
              {indentExpr (b.tr ty)}"

/--
The data members in an order in which each can be defined.

A member indexed by another mentions it by name -- `Ty G` is a subtype whose
predicate is applied to `G.val` -- so it has to be declared second.  Two members
each indexed by the other are a block no order would help, and that is the one
thing refused here.
-/
def dataOrder (b : Block) : TermElabM (Array Nat) := owning do
  let needs (i : Nat) : Array Nat :=
    b.dataIdxs.filter fun j =>
      j != i && b.members[i]!.type.getUsedConstants.contains b.members[j]!.name
  let mut out : Array Nat := #[]
  let mut left := b.dataIdxs
  while !left.isEmpty do
    let ready := left.filter fun i => (needs i).all (out.contains ·)
    if ready.isEmpty then
      let ns := ", ".intercalate (left.toList.map fun i => s!"`{b.members[i]!.name}`")
      throwError "The members {ns} index one another, so there is no order in which the \
        erasure could define them: each one's subtype would mention the next"
    out := out ++ ready
    left := left.filter (!ready.contains ·)
  return out

/--
The data constructors in an order in which each can be defined.

A constructor of an indexed family names its indices, and when the block indexes
data by data those indices are built out of the block's own constructors --
`Ty.pi`'s field `B : Ty (Γ.snoc A)` names `Ctx.snoc`.  Every member is a
definition by then, but a constructor is one too, so it has to be there first.

The sort is stable, so a block whose constructors say nothing about one another
comes out in the order it was written.
-/
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
of one of `c`'s recursive fields.

Recursing into such a field means calling the member's `recAux`, and a `recAux`
whose member deleted an index wants that index's own hypothesis along with it --
`Ty.recAux` at `Ty (Γ.snoc A)` has to be handed the hypothesis at `Γ.snoc A`.
`ihOfTerm` is what will find one, and it knows two things: a field of the
constructor, whose hypothesis the minor was given, and a constructor of the
block, whose hypothesis is its minor applied to the fields' own.  A function of
the fields is neither, so it is turned away here rather than half-emitted.

Below the top call `xs` is not a telescope but a constructor's argument list,
since an index built out of a constructor is checked against that constructor's
own fields, and an argument list holds closed terms as readily as variables --
`Ctx.snoc n Γ true A` gives one.  So the head is looked for by comparing terms
rather than by reading a variable off each entry.
-/
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
An index a constructor builds rather than takes as a field, checked to be a term
the erasure can state.

The well-formedness is going to say that the index the recursion arrives at *is*
this term, and it says so in the pre-world.  So everything the term is made of
has to have a pre-world reading: a field of the constructor's own has one, either
a stand-in or, where the field is itself a deleted index, its value, and so does
a data constructor of the block, fully applied.  An erased proof field has none,
having been dropped, and neither has anything else of the block -- a member's
type, say, or a constructor still waiting for arguments.
-/
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
      e.getAppArgs.forM (statableIdx b c kinds xs top)
  | _ => bad m!"it is not built out of the constructor's fields and the block's constructors"

/-- `reachableIh` at every deleted index every data constructor recurses under. -/
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
                  (b.dropArgs mm args).forM (reachableIh b c kinds xs)

/--
Re-declare the scratch axioms at the block's own universe parameters.

A member is stubbed as soon as its arity is known, and the only level list
available then is every universe name in scope.  That is the wrong list twice
over.  It can be too long -- a `universe u v w` the rest of the file needs is in
scope whether or not the block uses any of it -- and it can be *different* from
one member to the next, since a later member's `Type u` auto-binds `u` after an
earlier member has already been stubbed.  Either way it is not `us`, which is
what `normLevels` has just rewritten every reference to.

So the scratch environment is wound back to before the first stub and the whole
batch is declared again at `us`, from the normalized types.  Nothing else is
lost by the rewind: `withRaw` elaborates the block inside `withoutModifyingEnv`,
so anything else the elaboration happened to add was going to be discarded on
the way out regardless.
-/
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
axioms.

An arity goes through `tr` whichever kind of member it belongs to, and then
loses the indices the pre-type drops.  For a `Prop` member `tr` is the whole of
it: its arity may mention the block's data, and what it says of it is said again
at the pre-types.  For a data member it is the other way round -- `tr` has
nothing to rewrite, because a data index that mentions the block is one the
pre-type is about to delete.

Every pre-type is stubbed before any constructor is built, because a
constructor of one member may mention the pre-type of another.  The
constructors themselves are stubbed only when asked: `X._wf` is defined by
recursion over the data pre-constructors and is elaborated before the pre-block
is really declared, while nothing is ever elaborated against a `Prop`
pre-constructor.
-/
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

/--
The section variables the block uses, folded in as its leading parameters.

An inductive written inside a `variable (α : Type)` means the same as one that
takes `α` by hand, so the work is to find out which variables that is and put
them in front.  Which ones cannot be known before the constructors are read --
`Ty.base : (Γ : Ctx) → α → Ty Γ` names `α` in a field and in no arity at all --
so this runs on the finished `Raw` rather than on the way in.

A variable is kept when the block mentions it, when a kept variable's own type
mentions it, or when it is an instance whose type is about variables already
kept, which is how `[Inhabited α]` comes along with `α`.  The three feed each
other, so the search runs to a fixed point, and the survivors are taken in scope
order, which is dependency order.

They are then bound in front of every arity, every constructor type and every
copy's lambda, and every reference to a member or a constructor of the block is
applied to them -- which is what lets the short spellings the writer used inside
the block go on meaning what they meant.  The constructors' copy of them is made
implicit, since that is what the rest of this file expects a parameter to look
like there.
-/
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

/--
Everything between the elaborated block and the `Plan`.

The block reaching here need not be one anybody wrote: `denest` adds members of
its own, and they go through exactly the same analysis.
-/
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
    -- exactly as they were written.  They are collected after the levels are
    -- settled, because what they are stated over is the block, and the block
    -- spells its own universes only once `us` is known; and before `restub`,
    -- because a name that is going to be declared for real must not still be
    -- standing in the environment as a scratch axiom
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
    checkStayingArities r.names arities isProp
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
        members := skeleton.members.mapIdx fun i m => { m with dropped := drops[i]! } }
    -- a *data* member's index of that shape is refused rather than denested.
    -- Denesting is what makes the proposition above work -- `GOk : GWrap GVec →
    -- Prop` becomes `GOk : GVec.nested_GWrap_1 → Prop`, and since the whole
    -- proposition is erased there is nothing to carry back -- but a data
    -- member's index of the same shape is deleted, which means travelling as a
    -- member's pre-type and coming back as a subtype of it, and a `List` of
    -- them is neither: the transport would be a `List.map`, which is no
    -- identity, and the iota rules would stop holding by `rfl`.  So the index
    -- has to be a member's type as written, and this is the last place that can
    -- tell -- by `checkDropped` the copy is a member and passes, leaving the
    -- writer with a `Ty` indexed by an internal name they never wrote
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
    let prePropInds ← preInds b us b.propIdxs (stubCtors := false)
    -- `X._wf`, one conjunct per recursive field and one per erased proof field.
    -- All the data members share one set of motives and minors, so each `X._wf`
    -- is a different projection of the very same recursion.
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
            let res := mkArrows ((← b.dropTysAt i ps idxs) ++ pad) (mkSort Level.zero)
            withLocalDeclD `t (b.preApp i (ps ++ idxs)) fun t =>
              mkLambdaFVars (b.keptIdxs i idxs ++ #[t]) res
      let mut wfMinors : Array Expr := #[]
      for i in b.dataIdxs do
        for c in b.members[i]!.ctors do
          let kinds := b.fieldKinds c.kinds
          let minor ← forallTelescope (← b.ctorType c ps) fun xs concl => do
            -- the deleted indices are what the motive ends in, so the minor
            -- takes them last, all of them and at their pre-types.  A field the
            -- constructor gave as one of them is then read at the binder that
            -- replaced it; an index it built is read nowhere, and the equations
            -- at the end of the conjunction are what pin that binder down
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
              dDecls := dDecls.push (n, fun _ => pure dts[q]!)
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
                    conjs := conjs.push (← b.ihConj ihs[q]! padVal subTys[recPos[q]!]!)
                  for k in *...xs.size do
                    if kinds[k]! == .erased then
                      conjs := conjs.push (← b.preTy subTys[k]!)
                  for (_, eq) in ← b.builtEqs i kinds concl olds news dels do
                    conjs := conjs.push eq
                  mkLambdaFVars (keptImages imgs ++ ihs) <|
                    ← mkLambdaFVars (dels ++ pads) (foldConj conjs 0)
          wfMinors := wfMinors.push minor
      let mut wfDecls : Array (Name × Expr × Expr) := #[]
      for i in b.dataIdxs do
        let m := b.members[i]!
        -- one motive universe, the one they were all brought to.  A lowered
        -- pre-block wants one per component instead, and `widenPreRecLevels`
        -- repeats this one to suit once the real recursor is there to be counted
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
    return { block := b, preDataInds, prePropInds, wfDecls, preIsHeterogeneous, peeled
             peeledIdxs := r.peeled
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
      -- what the arity deletes, the constructor deletes with it.  A constructor
      -- that gives such an index as a bare field of its own loses the field
      -- along with the index, which is the cheap case and the common one; one
      -- that *builds* the index keeps every field and owes the erasure an
      -- equation instead, saying in the pre-world what it built
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
          statableIdx b c kinds xs a a
          built := built.push p
        | some k =>
          -- a field can stand for only one of the indices it is given as --
          -- `Sub.id : (Γ : Ctx) → Sub Γ Γ` gives its context as both -- and
          -- which one is not free: an index stated at one of those readings has
          -- a field typed there, and only the reading the field *is* leaves
          -- that field at a term the alternative has.  Every other reading is
          -- treated as one the constructor built, out of the field, and the
          -- equation in the well-formedness is what says they agree
          let ps := (given.find? (·.1 == k)).getD (k, #[p]) |>.2
          let keep := (ps.find? fun p' =>
            dropped.any fun r => !ps.contains r && statedAt[r]!.contains p').getD ps[0]!
          if p != keep then
            statableIdx b c kinds xs a a
            built := built.push p
            continue
          let .recur m := kinds[k]!
            | if kinds[k]! == .erased then
                throwError "`{c.name}` gives index {p + 1} as the field `{a}`, which is a \
                  proof.  A member indexed by a proposition of this block is not supported: \
                  the proof is erased, so there is nothing left to index by -- and since \
                  `Prop` is proof-irrelevant, such an index says nothing that dropping it \
                  would not say as well"
              else
                throwError "The resulting type of `{c.name}` gives index {p + 1} as the field \
                  `{a}`, which is not a value of a member of the block"
          kinds := kinds.set! k (.deleted m p)
      -- an index taken as a field, but stated at one the constructor built,
      -- cannot stay a field: the alternative binds the built index, so the field
      -- would be sitting at the constructor's reading of something the
      -- alternative only has a binder for.  What it can do instead is be both --
      -- the field is kept, the index is built out of it, and the equation the
      -- well-formedness carries for a built index is what says the two agree.
      -- The alternative then binds the field where the constructor wrote it and
      -- gets an induction hypothesis for it besides, which the deleted reading
      -- would not have given.  A binder in an arity can only name the ones before
      -- it, so one pass in arity order settles every promotion this sets off
      for p in dropped do
        let some k := deletedField? kinds p | continue
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

/--
Elaborate a written block into a `Raw`, and hand it on.

`k` runs with the scratch axioms still in scope, which is what `prepareCore`
needs; it is a callback rather than a return value for exactly that reason.
-/
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
    -- the constructors: the data members' first, so that their constructors are
    -- in scope for the `Prop` members' -- that is where `.snoc` has to resolve
    let mut ctorTypes : Array (Array Expr) := (List.replicate n (#[] : Array Expr)).toArray
    for i in dataIdxs do
      let tys ← views[i]!.ctors.mapM (elabCtorType views views[i]! ·)
      ctorTypes := ctorTypes.set! i tys
      for j in *...tys.size do
        stubAxiom views[i]!.ctors[j]!.declName tys[j]!
    for i in propIdxs do
      ctorTypes := ctorTypes.set! i (← views[i]!.ctors.mapM (elabCtorType views views[i]! ·))
    -- a member whose resulting type was left out was guessed at `Type`.  Now
    -- that the fields are known, check the guess was big enough: a field the
    -- guess does not fit would have been elaborated against the wrong universe,
    -- so the answer is to ask for the type rather than to widen it here
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
block: `WFTree RecWFTree` becomes a new member of the block, and the enlarged
block is checked instead.  `Mumi.Denest` does the same at the elaborator, and
hands the result to `Mumi.Lowering`.

Neither can do it here.  The specialisation of `Tree.WF` above is
`Tree.WF RecWFTree : Tree RecWFTree → Prop`, whose *arity* mentions the copy of
`Tree` -- the enlarged block is induction-inductive, which is exactly what
`Mumi.Denest` refuses and `Mumi.Lowering` cannot lower.  So the specialisation
is done again here, against the `Raw` above, and the enlarged block goes through
`prepareCore` like any other.

Two things differ from `Mumi.Denest` beyond that, and both follow from where in
the pipeline this sits.  The members are *constants* -- their scratch axioms --
rather than free variables, so an occurrence is recognised by name.  And the
rewrite is structural rather than head-only, because a copied constructor can
appear in an index: `Tree.WFWith.empty`'s resulting type is
`Tree.WFWith α .empty []`, and the `.empty` in it has to become the copy's.
-/

/-!
A nesting applied to something that mentions a field of the constructor it sits
in -- `mk (n : Nat) (x : OkFam A n)` -- cannot become a copy with `n` among its
parameters: a member's parameters are fixed before any constructor is
elaborated.  It becomes a copy *indexed* by `n` instead, and the field is
abstracted out of the parameters on the way in.

That abstraction has to survive between the two passes.  `scanExpr` walks under
binders with free variables of its own, `rwExpr` walks the raw expression with
its de Bruijn indices still in it, and one occurrence is a different expression
in each.  So the parameters are recorded as a *pattern*: an abstracted field
stands as a hole constant, which nothing the block can contain has in it, and
`matchHoles` reads back out of a candidate what each hole stood for.
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
stood for.  A hole reached twice has to reach the same thing both times.

`e` is the raw expression, de Bruijn indices and all, so a hole reached under a
binder of the pattern -- `Sigma Nat fun _ => Wrap R n` puts one under a lambda
-- comes back counted from inside that binder, while it is passed on outside it.
So `depth` says how many of the pattern's binders it was found under, and what
it stood for is lowered past them.  A value that is one of them cannot be lifted
out at all, and the match fails.
-/
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

/--
Open the telescope of fields a copy's parameters were abstracted over.  Each
one's type may mention the holes of the ones before it, so they go in in order.
-/
private def withHoles {m : Type → Type} [Monad m] [MonadControlT MetaM m] {α : Type}
    (tys : List (Name × Expr)) (acc : Array Expr) (k : Array Expr → m α) : m α :=
  match tys with
  | []           => k acc
  | (n, ty) :: r => withLocalDeclD n (fillHoles acc ty) fun y => withHoles r (acc.push y) k

/-- One nested application, and the member it is about to become. -/
private structure AuxSpec where
  /--
  `@I p₁ … p_k`: the type constructor applied to its parameters and nothing
  else.  Two occurrences with the same parameters share one member, so this is
  the key -- with the block's own constants stripped of their levels, because
  each is a scratch axiom over every universe name in scope and two references
  to it carry two different sets of metavariables.  Two occurrences that differ
  only in the fields they are applied to share one member too, which is what the
  holes in it are for.
  -/
  key       : Expr
  name      : Name
  /--
  `I`'s parameters, as they were written -- levels and all, unlike `key` -- with
  a hole wherever a field of the constructor was abstracted out.
  -/
  params    : Array Expr
  /--
  The fields those holes stand for: their names, for the copy's binders, and
  their types, each of which may mention the holes of the ones before it.  Empty
  unless the nesting was applied to something a field reaches.
  -/
  localTys  : List (Name × Expr)
  indName   : Name
  /-- The levels `I` was applied at. -/
  levels    : List Level
  numParams : Nat
  ctors     : Array Name
  deriving Inhabited

private abbrev DenestM := StateRefT (Array AuxSpec) MetaM

/-- Does `e` mention any of `names`? -/
private def mentionsNames (names : Array Name) (e : Expr) : Bool :=
  e.getUsedConstants.any (names.contains ·)

/--
Put every constant of `names` at the empty level list, and every other level in
normal form, so that keys compare.

A member's own levels are dropped because a key stands for the shape of the
nesting and not for how the occurrence spelled the block.  The rest are
normalised because the order `max` writes its arguments in is not fixed:
`List (T α β)` with `T : Type (max u v)` elaborates to `List.{max v u}` in one
member's arity and `List.{max u v}` in another member's constructor, and
structural equality between those two is false.  A key that missed that way
would leave the occurrence standing in the constructor while the arity took the
copy, and the two no longer agree on what the constructor's index is.
-/
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

/--
Recognise a nested occurrence: an inductive type applied to parameters that
mention the block.  A member applied to its own arguments is not one, and
neither is an inductive that mentions the block only outside its parameters.
-/
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
  let params := args.extract 0 info.numParams
  if !params.any (mentionsNames names ·) then return none
  return some (mkAppN (.const iname lvls) params, info, lvls, params,
    args.extract info.numParams args.size)

mutual

/--
Intern the nested application `e` is, if it is one, and then look through the
copy's own arity and constructors for further nesting.
-/
private partial def internNested (names : Array Name) (root : Name) (bound : Array FVarId)
    (e : Expr) : DenestM Unit := do
  let some (_, info, lvls, params, idxArgs) ← nestedApp? names e | return
  -- `Mumi.Denest` turns a nesting parameter that mentions a field of the
  -- constructor it sits in into an extra index of the copy, and so does this.
  -- `bound` is what the scan itself went under, so it is exactly the fields in
  -- scope at the occurrence; the ones the parameters reach are closed under
  -- their own types, so that the telescope the copy gains is well formed, and
  -- taken in scope order, which is dependency order
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
  -- the thing this file was written to erase.  So the type goes across as it
  -- stands and the copy joins the block as an ordinary member
  let mut localPats : Array (Name × Expr) := #[]
  for j in *...ys.size do
    let ty ← inferType ys[j]!
    localPats := localPats.push
      (← ys[j]!.fvarId!.getUserName, ty.replaceFVars (ys.extract 0 j) (holes.extract 0 j))
  let localTys := localPats.toList
  -- nesting into one member of a mutual family specialises the whole family:
  -- the members mention each other, so a copy of one is useless without copies
  -- of the rest.  They share a parameter telescope, so `params` fits all of
  -- them, and they are named in declaration order however the block reached
  -- them.  Every one is interned before any is scanned, so that the members'
  -- references to each other find copies rather than intern them again
  let fam ← info.all.toArray.mapM getConstInfoInduct
  for fi in fam do
    let name := root ++ Name.mkSimple s!"nested_{shortName fi.name}_{(← get).size + 1}"
    modify (·.push { key := stripLevels names (mkAppN (.const fi.name lvls) params)
                     name, params, localTys, indName := fi.name, levels := lvls,
                     numParams := fi.numParams, ctors := fi.ctors.toArray })
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
        let cinfo ← getConstInfoCtor c
        scanExpr names root inner
          (← instantiateForall (cinfo.type.instantiateLevelParams cinfo.levelParams lvls) params)

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
come back to be passed on in front of the occurrence's own indices.
-/
private def specOf? (names : Array Name) (specs : Array AuxSpec) (app : Expr) :
    Option (AuxSpec × Array Expr) := Id.run do
  let a := stripLevels names app
  -- `internNested` keys on the whole application, so a block holding both
  -- `List (Wrap R n)` and `List (Wrap R 0)` gets a member for each.  The second
  -- occurrence matches both -- the family's hole takes `0` -- and the member
  -- that stands for it alone is the one meant: sending it to the family's
  -- instead would give that member's own constructors a conclusion at a
  -- different type
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
  match e with
  | .app .. =>
    if mentionsNames names e then
      if let some (aux, rest) ← specHit? names specs e then
        return mkAppN (.const aux auxLvls) (ps ++ (← rest.mapM rw))
    return mkAppN (← rw e.getAppFn) (← e.getAppArgs.mapM rw)
  | .forallE n d b bi => return .forallE n (← rw d) (← rw b) bi
  | .lam n d b bi => return .lam n (← rw d) (← rw b) bi
  | .letE n t v b nd => return .letE n (← rw t) (← rw v) (← rw b) nd
  | .mdata m b => return .mdata m (← rw b)
  | .proj s i b => return .proj s i (← rw b)
  | _ => return e

/--
Copy the first `n` binder names and annotations from `model` onto `e`.

Rewriting under the block's parameters means taking them apart and putting them
back, and `mkForallFVars` annotates each binder the way its local declaration
is, which for a constructor is not how the constructor had it.
-/
private def copyLeadingBinders : Nat → Expr → Expr → Expr
  | 0, _, e => e
  | n + 1, .forallE mn _ mb mbi, .forallE _ ty b _ =>
    .forallE mn ty (copyLeadingBinders n mb b) mbi
  | _, _, e => e

/--
Specialise every nested occurrence in `r` into a member of its own.

A block with no nested occurrence comes back untouched.  Otherwise the copies
are appended as members, and everything -- the original members included -- is
rewritten to mention them instead.  The copies are stubbed as scratch axioms on
the way out, in dependency order, so that `prepareCore` can telescope over them
like any other member.
-/
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
        -- that parameter, and `Sigma.mk`'s `snd : β fst` becomes
        -- `(fun _ => Wrap R n) fst`.  The copy is a declaration the writer reads,
        -- so it gets the beta-normal form
        let resType ← Core.betaReduce
          (← instantiateForall (ci.instantiateTypeLevelParams s.levels) params)
        let arity := copyLeadingBinders r.numParams r.arities[0]!
          (← mkForallFVars (ps ++ ls) (← rw resType))
        let mut cts : Array Expr := #[]
        for c in s.ctors do
          let cinfo ← getConstInfoCtor c
          let cty ← Core.betaReduce (← instantiateForall
            (cinfo.type.instantiateLevelParams cinfo.levelParams s.levels) params)
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
      let app ← withHoles s.localTys #[] fun ls => do
        instantiateMVars (← mkLambdaFVars (ps ++ ls)
          (mkAppN (.const s.indName s.levels) (s.params.map (fillHoles ls))))
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
block, and a copy is not the type it copies: `RecWFTree.nested_WFTree_1` and
`WFTree RecWFTree` have the same constructors, but no term of one is a term of
the other, and no arrangement of declarations makes them defeq -- the copy has
to exist before `RecWFTree` does, and `WFTree RecWFTree` cannot be written until
`RecWFTree` does.  Lean's own nested inductives have no such copy at all: the
kernel builds the enlarged block internally and states `Rose.rec` over
`List Rose` directly, which is not something an elaborator can reproduce.

What can be arranged is that the copy never appears in anything the writer has
to read.  The two types are *isomorphic*, and the isomorphism is definable:

* `X.ofOrig` sends the original to the copy.  It recurses on the original, an
  ordinary inductive with an ordinary recursor, so this direction is the easy
  one: a data copy's is compiled by structural recursion, a `Prop` copy's is a
  theorem built from the original's own `rec`.
* `X.toOrig` sends the copy back.  It has to recurse on the copy, which is a
  member of the lowered block, so it goes through the pre-type: `X.toOrigPre`
  is the structural recursion, over a motive that takes the well-formedness of
  the indices *after* the term itself, and `X.toOrig` supplies them from the
  index it was handed.
* `X.ofOrig_toOrig : (X.ofOrig (X.toOrig x)).val = x.val` closes the round trip
  on the side the recursor needs, by recursion on the copy the same way.

With `ofOrig`, the constructor the writer declared can be given the type they
wrote.  The kernel-facing constructor keeps the copy in its type under a hidden
name, `RecWFTree._nested_mk`, and `RecWFTree.mk` is a wrapper over it:

```lean
def RecWFTree.mk (x : WFTree RecWFTree) : RecWFTree := RecWFTree._nested_mk (ofOrig x)
```

The recursor gets the same treatment, and needs the whole isomorphism.
`RecWFTree._nested_rec` is the kernel-facing one, with a motive for every member
of the enlarged block -- one of them over `RecWFTree.nested_WFTree_1`.  `X.rec`
takes motives over the originals instead and applies `_nested_rec` at
`fun idxs t => C .. (X.toOrig t)`, which is what makes a minor stated over a
copy line up with one stated over the original: a field of copy type is handed
on as `X.toOrig` of itself, and the induction hypotheses match on the nose.

The one place it does not line up is a constructor of the writer's own that had
to be renamed.  The raw minor concludes at the raw constructor applied to the
copy-typed field, and the nice minor concludes at the nice constructor applied
to `X.toOrig` of it -- which unfolds to the raw one at `X.ofOrig (X.toOrig ..)`.
`ofOrig_toOrig` is exactly the difference, so the conclusion is transported
along it, one field at a time and at the `.val` level, and `Subtype.ext` lifts
the result back.

A copy is not a name anyone reaches for, so a copy keeps only its raw recursor
and `X.rec` is emitted for the members the writer declared.  The plain name is
always free: every member of a lowered block is a `def`, so Lean generates no
`X.rec` of its own to collide with.

Copies whose originals are nested in each other -- `Rose T`, whose own field is
a `List (Rose T)`, so that both are copied and neither can be built first, or
the two members of a `mutual` family, which are copied together because a copy
of one is no use without the other -- are found and compiled as one group.  A
group of data copies is compiled by structural recursion over the outer
original's recursor; a group of `Prop` copies is a mutual induction, each
theorem giving every copy in the group a real motive so that a sibling arrives
as a hypothesis rather than as a call to a theorem that does not exist yet.  A
group that *mixes* the two has no such shape, since a data copy's `ofOrig` is a
compiled function and a `Prop` copy's is a theorem; no block in vanilla Lean is
known to produce one.

Nothing here is load-bearing.  Every step is attempted and, if any of it fails
-- that last case, say -- the environment is rolled back to before the bridge,
the plain names are defined as the raw declarations instead, and the block is
exactly what it was before.
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

/--
A member denesting added, and the type it is a copy of.

A copy whose nesting parameters mentioned a field of the constructor it sat in
stands for a *family* of originals rather than for one: `fun (n : Nat) => OkFam
α n` is copied once, and the field `n` becomes a leading index of the copy.
`app` is that lambda, `numLocals` says how long it is, and everywhere below the
copy's own indices are those locals followed by the original's real indices --
which is exactly the telescope of `app`'s type.
-/
structure Copy where
  /-- Where the copy sits among the block's members. -/
  idx     : Nat
  /-- The copy's name. -/
  name    : Name
  /-- The inductive being copied. -/
  indName : Name
  /--
  `fun ls => I ps'`: that inductive applied to its parameters, under the block's
  parameters, abstracted over the constructor fields those parameters mentioned.
  -/
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
The copy's own arguments for `e`, if `e` is this copy's original applied.

Those are the locals the family member is at -- read off the occurrence, since
they are what says *which* member of the family it is -- followed by the
original's real indices.  A copy of a single original has no locals, and then
this is just the old question of whether the parameters agree.
-/
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
  deriving Inhabited

namespace BridgeCtx

/-- Which copy's original `e` is an application of, and the arguments it carries. -/
def copyOf? (c : BridgeCtx) (e : Expr) : MetaM (Option (Nat × Array Expr)) := do
  -- as in `Block.withRecTarget?`: a `Subtype`'s proof field says
  -- `(fun t => P t) val`, and the copy is at the head of its beta-normal form
  let e := e.headBeta
  if e.getAppFn.constName?.isNone then return none
  -- a block may hold both `List (Wrap R n)`, whose copy stands for the family,
  -- and `List (Wrap R 0)`, whose copy stands for that one type.  Both match the
  -- second occurrence, and the one that copies nothing else is the right answer:
  -- taking the family's would send `nested_List_3.nil` to a conclusion at
  -- `nested_List_1 0`, which is a different type
  for narrow in [true, false] do
    for k in *...c.copies.size do
      if (c.copies[k]!.numLocals == 0) != narrow then continue
      if let some args ← c.copies[k]!.argsOf? e then
        return some (k, args)
  return none

/--
The copy-world image of `x : ty`, where `ty` is stated in the original world.

A field or index whose type has nothing to do with the block comes back as it
is; one that lands in a copied type is sent through that copy's `ofOrig`.  That
`ofOrig` is indexed by the *original's* indices -- it is what sends them across
-- so they are passed on as they stand.
-/
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
partial def unCopy (c : BridgeCtx) (e : Expr) : MetaM Expr := do
  match e with
  | .app .. =>
    let args ← e.getAppArgs.mapM c.unCopy
    if let some hd := e.getAppFn.constName? then
      if let some r ← c.unCopyHead? hd args then return r
    return mkAppN (← c.unCopy e.getAppFn) args
  | .const n _ => return (← c.unCopyHead? n #[]).getD e
  | .forallE n d b bi => return .forallE n (← c.unCopy d) (← c.unCopy b) bi
  | .lam n d b bi => return .lam n (← c.unCopy d) (← c.unCopy b) bi
  | .letE n t v b nd => return .letE n (← c.unCopy t) (← c.unCopy v) (← c.unCopy b) nd
  | .mdata m b => return .mdata m (← c.unCopy b)
  | .proj s i b => return .proj s i (← c.unCopy b)
  | _ => return e

/--
Member `i`'s arity as the writer stated it, at the block's parameters.

A `Prop` member indexed by a nesting was denested along with everything else, so
what the block carries is its arity over the copy; the plain name the bridge
gives it is over the original.  For every other member the two are the same
expression, `unCopy` having nothing to put back.
-/
def niceArity (c : BridgeCtx) (i : Nat) : MetaM Expr := do
  c.unCopy (← instantiateForall c.b.members[i]!.type c.ps)

/--
Every copy that a subterm of `e` is an application of the original of.

The question is which copy, not which inductive: `Tree` nested inside `WFTree`
inside the block is copied twice, once at `R` and once at `WFTree R`, and the
two are different members with different bridges.  `copyOf?` tells them apart by
their parameters, so it is asked about each application rather than about each
head name.  A constructor is asked about as the inductive it belongs to.
-/
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
  match e with
  | .app f a         => c.usesCopies a (← c.usesCopies f acc)
  | .forallE _ d b _ => c.usesCopies b (← c.usesCopies d acc)
  | .lam _ d b _     => c.usesCopies b (← c.usesCopies d acc)
  | .letE _ t v b _  => c.usesCopies b (← c.usesCopies v (← c.usesCopies t acc))
  | .mdata _ b       => c.usesCopies b acc
  | .proj _ _ b      => c.usesCopies b acc
  | _                => return acc

/--
The copies, grouped and ordered so that each group comes after every copy the
group's originals mention.

The originals are looked at *instantiated at their parameters*, which is what
makes a copy of `List` at a copied `Tree` come out after the `Tree`: plain
`List` mentions nothing of the block.  It is also what lets two copies of the
same inductive be ordered against each other, which nesting inside nesting
needs: `Tree (WFTree R)` waits for `WFTree R`, which waits for `Tree R`, which
waits for nothing.  A copy may of course mention *itself*.

Copies that genuinely need each other -- a nesting type that is itself a nested
inductive, so that `Rose T` and `List (Rose T)` are copied together, or a
nesting into one member of a mutual family -- have no order between them, and
come back as one group.  `addOfOrig` compiles such a group as one mutual
recursion; `toOrig` does not need the grouping, because it recurses on the
copies, which are members of a single lowered block already.
-/
def order (c : BridgeCtx) : MetaM (Array (Array Nat)) := do
  let n := c.copies.size
  let mut uses : Array (Array Nat) := #[]
  for cp in c.copies do
    -- a copy standing for a family is looked at with its locals opened, so that
    -- what its members mention is what any one of them mentions
    let ks ← lambdaBoundedTelescope cp.app cp.numLocals fun _ orig => do
      let lvls := orig.getAppFn.constLevels!
      let params := orig.getAppArgs
      let info ← getConstInfoInduct cp.indName
      let mut ks ← c.usesCopies
        (← instantiateForall (info.instantiateTypeLevelParams lvls) params) #[]
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
across one by one.  A field of the original's own type becomes a recursive call,
which is what `Structural.structuralRecursion` is handed afterwards.
-/
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
about.

`recInfo.rules` would answer the constructor and its arity, but only for the
member whose recursor this is, and the minors run over the whole block.
-/
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
at once.

Both `ofValueProp` and `backValue` are one application of it, and they agree on
everything but what a motive says and what a minor premise proves.
-/
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
of `grp` at once.

`motive` says what is being proved of a member of the group, and is given which
copy it is, the arguments that copy is at, and the major premise.  Everything
else the recursor eliminates -- the other members of the original's own block,
and the types that block nests into -- is sent to `True`, whose hypotheses are
worth nothing and whose minor premises `GroupElim.minors` discharges.
-/
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
The minor premises: `body` at each one that is about a copy in the group, and
`trivial` at each one that is not.

`body` is given the copy the minor is about, what the minor is about it, the
minor's own arguments and the conclusion it has to reach; the abstraction over
those arguments is taken here rather than by `body`.
-/
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

/--
`X.ofOrig` for a `Prop` copy: one application of the original's own recursor.

A theorem cannot call itself, so a field of the original's type takes the
hypothesis the recursor supplies for it rather than a recursive call.  The same
goes for a field of any other original in `grp`, the copies that need each other
and so are being defined at once -- `Chain.Even` and `Chain.Odd`, say.  Every
one of them is given its copy as a motive, and everything else the recursor
eliminates is sent to `True`, whose minor premises are `trivial` and whose
hypotheses are worth nothing; a field of a copy *outside* the group is already
bridged and goes across by calling that copy's `ofOrig`.

The original's recursor carries a motive per member of its own mutual block,
and one more per type that block nests into, so which hypothesis belongs to
which field cannot be read off the field alone.  It is read off the recursor
instead: before the motives are instantiated, a hypothesis' type still mentions
both the motive it is for and the field it is about.
-/
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

/--
Add `X.ofOrig` for every copy, each group after the ones its own bodies call.

A group of more than one is a set of copies whose originals are nested in each
other -- `Rose T` and the `List (Rose T)` inside it, or the two members of a
mutual family the block nests into -- and their `ofOrig`s need each other.

`Prop` copies get one theorem each: a `Prop` copy's `ofOrig` recurses through
its original's recursor, and that recursor already has a motive for every other
original in the group, so nothing in the group is a call.  Data copies are
compiled together by structural recursion, over the recursor of the outermost
original, which likewise has a motive for each of them: it is exactly what a
writer gets for `def f : Rose α → β` paired with `def fs : List (Rose α) → γ`.

A group holding both kinds at once would be a mutual family that is itself
induction-inductive, which is not something Lean can be asked for, and it is
refused -- which drops the bridge and leaves the block with its copies visible.
-/
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

/--
Give every renamed member the arity it was declared with.

A `Prop` member the writer indexed by a nesting is emitted over the copy, and
what it means over the original is the raw one at the original's image -- which
is what `ofOrig` is for, and why this waits until `ofOrig` is there.

It has to come before the constructors: `Ok.nil : Ok []` typechecks against the
raw `Ok._nested (K.ofOrig [])` only because `ofOrig` at a constructor of the
original reduces to the copy's, so the plain name has to exist for the plain
statement to be made at all.
-/
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

/--
Give every renamed constructor the type it was declared with.

`rawOf` is the name the constructor was actually emitted under; a constructor
that kept its own name has nothing to do here.
-/
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

`ofOrig` alone gives the constructors their written types, but a recursor has to
travel the other way: a minor is handed a term of the *copy* and has to produce
one of the original for the writer's motive to apply to.  So the isomorphism is
completed.

* `X.toOrig` sends the copy to the original.  A data copy's is one application of
  the copy's own recursor, with the members it is not eliminating given `PUnit`
  as their motive.  A `Prop` copy's cannot be, quite: the copy is *defined* as
  its pre-form at the underlying values, so a proof in hand says nothing about
  the well-formedness of the terms it is indexed by, and the original's statement
  needs those.  It goes through the pre-form's recursor with the well-formedness
  proofs taken last, and `X.toOrig` supplies them from the index it was given.

* `X.ofOrig_toOrig` is the round trip, at the underlying pre-world value.  It is
  needed in exactly one place -- a minor for a constructor the writer declared
  produces the raw constructor at the round-tripped fields, and this is what
  turns that back into the raw constructor at the fields themselves.  Stating it
  at the subtype would make that transport ill-typed, since a constructor with
  an erased proof field has a field whose *type* moves with the transport; at the
  value there are no proof fields left at all, and `Subtype.ext` lifts it.
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
applied to `vals`, the copy's constructor's own arguments.

A copy standing for a family carries its locals as leading fields of every
constructor, and they say which original this constructor belongs to; the rest
of `vals` are the original's own fields.
-/
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
The name of anything the denesting made up, if `ty` mentions one.

Every statement the bridge adds is a statement a writer reads and has to
instantiate, so none of them may name a copy, anything in a copy's namespace, or
the hidden name a renamed member or constructor went in under.  A *value* may
name all of these and mostly does -- it is the raw declaration it is standing in
front of.  The bridge checks the types it adds against this rather than trusting
that they came out clean, since a restatement that reaches for one of these names
is one the block is better off not having: the split recursor it falls back to
says less but says it in the writer's own words.
-/
def leaked? (c : BridgeCtx) (ty : Expr) : Option Name :=
  let b := c.b
  ty.getUsedConstants.find? fun n =>
    c.copies.any (fun cp => cp.name.isPrefixOf n)
      || b.members.any fun m =>
           (m.name != n && b.rawMember m.name == n)
             || m.ctors.any fun cc => cc.name != n && b.rawCtor cc.name == n

/--
The motive arguments of a member's type: a copy's are the *original's*.

`app` is the member applied, in the original world for a copy.  A copy standing
for a family is asked which member of it this is, since the locals that answer
that are among the original's parameters and lead the copy's own indices.
-/
def niceIdxArgs (c : BridgeCtx) (i : Nat) (app : Expr) : MetaM (Array Expr) := do
  match c.copyAt? i with
  | none   => return c.b.idxArgs app.getAppArgs
  | some k =>
    let cp := c.copies[k]!
    let some args ← cp.argsOf? app
      | throwError "`{cp.name}` stands for a family of originals, and{indentExpr app} is not \
          one of them"
    return args

/--
`Subtype.ext` at `ty`, a member of the block applied to its arguments.

Which subtype that is could be spelled out of the member and the arguments, but
not from the arguments as the writer sees them: an index at another member is
kept by the erasure at its pre-world value, and reading it off the type asks the
one question there is to ask and gets both components at once.
-/
def subtypeExt (c : BridgeCtx) (i : Nat) (ty a a' h : Expr) : MetaM Expr := do
  let sub ← whnfD ty
  unless sub.isAppOfArity ``Subtype 2 do
    throwError "`{ty}` is not the subtype the member unfolds to"
  return mkAppN (mkConst ``Subtype.ext [c.b.members[i]!.level])
    #[sub.appFn!.appArg!, sub.appArg!, a, a', h]

/--
The original-world image of `x : ty`, where `ty` is written in the copy world.

The mirror of `BridgeCtx.ofImage`.  A copy's indices are the original's -- a data
copy has the arity it copies, and a `Prop` copy's `toOrig` is stated at the
copy's own -- so here too the indices are passed on as they stand.

A proof of a member the bridge restates is the third thing this meets, and the
only one that moves: the written statement is the raw member at the round trips
of its indices, so the proof is transported onto them.
-/
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
the raw recursor's own type rather than reconstructing them.

`mk` is handed the member, the constructor, the fields and the induction
hypotheses, and returns the minor's body.
-/
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
          forallBoundedTelescope (← inferType ms[q]!) (nf + (ihPositions kinds).size)
            fun args concl => do
              mkLambdaFVars args
                (← mk i cc (args.extract 0 nf) (args.extract nf args.size) concl)
        q := q + 1
    return out

/--
`X.toOrig` for a data copy: one application of the copy's own recursor.

The copy being sent across is one of `grp`, the copies whose originals are
nested in each other and so have no order between them -- `Rose T` and the
`List (Rose T)` inside it.  Every one of them gets its original as a motive, and
every other member of the block is eliminated into `PUnit`.  Only one of the
motives is what the definition returns, so giving the rest of the group
something real looks wasteful, and is what keeps this a single recursor
application: a field whose type is another copy in the group then arrives as an
induction hypothesis already in the original world, rather than as a call to a
`toOrig` that is being defined at the same moment.

A copy *outside* the group is already defined, so its fields go across by
calling its `toOrig`, as they always did.  Handing it a motive too would be
worse than wasteful: an erased field of one of its constructors would drag in a
`Prop` copy's `toOrig`, and that one is stated in terms of this one.
-/
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
          -- erasure calls it a deleted index.  Here it is still a field, and it
          -- is the local `origCtor` reads off the front, so it goes across as
          -- itself
          | .deleted .. => vals := vals.push xs[z]!
          -- a deleted field arrives with a hypothesis of its own, so the count
          -- has to step over it even though nothing here reads it
          if kinds[z]!.hasIh then nih := nih + 1
        return c.copies[j]!.origCtor cc.name vals
      return implicitPrefix (c.ps.size + idxs.size) (← mkLambdaFVars (c.ps ++ idxs ++ #[x])
        (mkAppN recCst (c.ps ++ motives ++ minors ++ idxs ++ #[x])))

/--
Walk a `Prop` member's indices in the pre-world, collecting the well-formedness
proofs that turn them back into real ones.

`k` receives the pre-world binders, one proof binder per index that lands in a
data member, and the real indices rebuilt from the two.
-/
partial def withWfIdxsAux {α} [Inhabited α] (c : BridgeCtx) (idxs : Array Expr) (i : Nat)
    (preTy : Expr) (pres ws : Array Expr) (reals : Array (Expr × Expr))
    (k : Array Expr → Array Expr → Array (Expr × Expr) → TermElabM α) : TermElabM α := do
  if h : i < idxs.size then
    forallBoundedTelescope preTy (some 1) fun ys rest => do
      let y := ys[0]!
      -- the copy-world type the index was declared with, kept alongside the term:
      -- a rebuilt index is a `Subtype.mk`, and what that infers to says `Subtype`
      -- rather than the copy, which is what the image is looked up by.  A later
      -- index's type can mention an earlier one, and what stands for that here is
      -- the rebuilt index, not the binder the member was declared with
      let raw ← inferType idxs[i]
      let ty := raw.replaceFVars (idxs.extract 0 i) (reals.map (·.1))
      -- and the same type read the way `Block.subTy` reads a field: the member's
      -- real head over pre-world arguments.  That reading is the only one that
      -- still names an index the pre-type deleted, and `X._wf` takes every index
      -- the arity had, so it is the only one the proof can be stated from
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
of each.

`X._wf` at a constructor is a conjunction over the recursive fields, so a proof
that a constructor application is well formed *contains* the proof for each of
its arguments.  Which conjunct is which is not worth reconstructing: they are all
collected and the one that is wanted is the one whose statement matches.
-/
partial def wfParts (w : Expr) : MetaM (Array (Expr × Expr)) := do
  let ty ← whnf (← inferType w)
  let mut out := #[(ty, w)]
  if ty.isAppOfArity ``And 2 then
    let l := ty.appFn!.appArg!
    let r := ty.appArg!
    out := out ++ (← wfParts (mkApp3 (mkConst ``And.left) l r w))
    out := out ++ (← wfParts (mkApp3 (mkConst ``And.right) l r w))
  return out

/--
Every `Subtype.property` the statement `want` puts within reach.

A real value is a pre-term paired with its well-formedness, so any `.val` in a
statement brings the proof about that `.val` along with it.  The one the
statement is about need not be the outermost -- `Ty._wf Γ.val A.val` is `A`'s
property, not `Γ`'s -- so every projection in there is collected and the caller
tries them all.
-/
partial def subProps (e : Expr) (acc : Array Expr) : Array Expr :=
  let acc :=
    if e.isAppOfArity ``Subtype.val 3 then
      acc.push (mkAppN (mkConst ``Subtype.property e.getAppFn.constLevels!) e.getAppArgs)
    else acc
  match e with
  | .app f a => subProps a (subProps f acc)
  | .lam _ d b _ | .forallE _ d b _ => subProps b (subProps d acc)
  | .letE _ t v b _ => subProps b (subProps v (subProps t acc))
  | .mdata _ b => subProps b acc
  | .proj _ _ b => subProps b acc
  | _ => acc

/--
The proof among `parts` of the statement `want`, or one assembled out of them.

A fact about a term the constructor *built* -- `Wf.pi` recurses at
`Wf (Γ.snoc A) B`, and no proof about `Γ.snoc A` was handed to it -- is in none
of the parts, but it is not new either.  `X._wf` at a pre-constructor is the
conjunction of the facts about that constructor's own arguments, so unfolding
the statement one step turns it into exactly the facts the caller does hold, and
the proof is those put back together.  A constructor with no recursive arguments
unfolds to `True` and needs nothing at all.
-/
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

/--
A raw induction hypothesis, at the well-formedness proofs in hand.

A motive over a pre-type ends in the proofs about its indices, so the hypothesis
the pre-block's recursor states for a `Prop` field is quantified over them: the
pre-world does not know which proofs the field's indices will turn out to carry.
At a constructor we do know -- they are components of the proof the conclusion
is under, which `wfParts` has already broken apart -- so the hypothesis is
applied to the matching component of each and comes back in the shape the
caller's own minor premise asks for.
-/
def atParts (parts : Array (Expr × Expr)) (ih fieldTy : Expr) : MetaM Expr := do
  let nzs ← forallTelescope fieldTy fun zs _ => pure zs.size
  forallBoundedTelescope (← inferType ih) nzs fun zs rest => do
    forallTelescope (← whnf rest) fun ws _ => do
      let mut fnd : Array Expr := #[]
      for w in ws do
        fnd := fnd.push (← findPart parts (← inferType w))
      mkLambdaFVars zs (mkAppN ih (zs ++ fnd))

/--
Some element of a field's type, if a constructor can be applied to make one.

This is what stands in for a *stray* field -- a data field of a `Prop`
constructor that the conclusion says nothing about, and so has no
well-formedness in reach to put it back at its subtype with.  Standing in for it
is sound because everything built out of such a field is a proof, and two proofs
of one proposition are definitionally equal: the constructor applied to any
element of the field's type *is* the constructor applied to the element that was
meant.  Callers are the ones who know they are building a proof, so they are the
ones who ask for this.

The search is the one `Inhabited` would do -- a constructor whose own fields can
be filled in turn -- with the block's own members included, since their visible
constructors are `def`s into the subtype and are in the environment by the time
any of this runs.  It is bounded by `fuel` rather than by anything cleverer: a
member that needs a deep term to reach is a member the writer is unlikely to
have meant as a throwaway, and answering `none` costs only the recursor that
would have been built.

An infinitary field is a function into the member, and is answered under its own
binders by a constant function.
-/
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
is none to put back.

A data constructor's `_wf` is computed from its fields, so every one of them
comes with its own well-formedness.  A `Prop` constructor has no `_wf` -- a
`Prop` member is a predicate on values that are already well formed -- so the
only well-formedness in reach is whatever its *conclusion's* indices carry.  A
data field the conclusion does not mention, the middle value of a transitivity
rule being the usual one, has none.

Recording it is not an option either: `_wf` is a function defined by recursion
on the erased data, and a data member whose fields include proofs has a `_wf`
that mentions the `Prop` members' erased types.  A `Prop` member carrying `_wf`
of its fields would have to be declared before and after itself.
-/
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

/--
A data field of a `Prop` constructor, put back at its subtype.

The recursion runs in the pre-world, so the field arrives erased; the minor
premise the caller is building is stated over the writer's own types, so the
field has to be paired back up with its well-formedness before it can be passed
on.  An infinitary field is a function into the member, and is rebuilt under its
own binders.

`strayOk` says that what is being built is a proof, and so that a field with no
well-formedness in reach may be answered with `someElem?` instead of the value
the recursion was handed.  Only a caller can know that -- it is the caller that
holds the term's type -- and a caller that does not say so gets the failure and
the reason for it, as before.
-/
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

/--
Which of a `Prop` constructor's fields nothing else in the constructor mentions.

A field like this is one the recursion has to stand an arbitrary element in for:
its well-formedness would have to come from the conclusion, and the conclusion
does not know it exists.  Standing one in costs the minor premise its induction
hypothesis at that field, since the substitute is not the value the recursion was
handed and there is nothing to be said about it.

The positions are worked out here, once, because the minor premise's *type* and
the term that fills it are built far apart and have to agree about them down to
the last one.  Disagreeing is not a type error where the mistake is: it is an
application at the wrong arity, a long way from either half.

Hence the test is what it is.  Asking `dataFieldPart` directly would name more
fields, but it is asked under a substitution on one side and not on the other and
does not always give the same answer twice; occurring in the constructor's own
type is a property of the constructor and of nothing else.  A field the
conclusion mentions in a way `dataFieldPart` still cannot use falls through to
the failure it always had.

A field a *later field's type* mentions is not stray either, even if the
conclusion forgets it: substituting for it would leave that later field's type
talking about a value no longer there.
-/
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

/--
`X.toOrigPre` and `X.toOrig` for a `Prop` copy.

The recursion is on the pre-form, whose motive takes the well-formedness of the
indices *after* the proof itself; `X.toOrig` then supplies them from the index
it was handed.

Every `Prop` copy in the block gets its real motive, not just the one being
defined, so that a copy whose constructor recurses into a *sibling* copy has an
induction hypothesis to hand rather than a `True`.  The minors are then the same
for all of them and only the recursor's head changes, which is why they are
built here and not once per copy.  A `Prop` member the writer declared is not a
copy of anything and is eliminated into `True`.
-/
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
        -- `toOrig` is added one copy at a time, and a sibling whose own index has
        -- not been sent across yet has nothing to state its real motive with.  Two
        -- families denested side by side are like that: each is settled whole
        -- before the other is begun.  `True` is the right motive there, and costs
        -- only an induction hypothesis that nothing in the other family asks for
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
          let xs := args.extract 0 kinds.size
          let ihs := args.extract kinds.size args.size
          let subTys ← b.subFieldTys cc c.ps xs
          forallTelescope (← whnf concl) fun ws _ => do
            let mut parts : Array (Expr × Expr) := #[]
            for w in ws do
              parts := parts ++ (← wfParts w)
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
                  -- a data field, rebuilt at the subtype from the proof in hand, and
                  -- then sent across.  A member that deleted an index is spelt one
                  -- way here and another in the copy world, and nothing in reach
                  -- says which original index the deleted one stands for
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

/--
Add `X.toOrig` for every copy, each after the ones its own body calls.

Unlike `ofOrig`, a group of copies that need each other does not have to be
compiled together: each one is a single application of the lowered block's
recursor, and `toValueData` gives the whole group motives so that the group's
own members never appear as calls.
-/
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

/--
`head as = head bs`, one step per argument the two sides differ at.

`arg z` is the term both sides hold at position `z`, and `pf z` an equation
there instead, for a position where they differ.  The steps are taken one at a
time rather than as a single `congr` so that a head whose later arguments depend
on earlier ones still goes through, which needs the steps to be at arguments no
later one depends on -- the caller's business, and true where this is used.
-/
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
sides differ at.

`pf z` is the equation for field `z`, or `none` when the two sides hold the same
term there -- which is every field but a copy's, and every erased field, since
those are not at this level at all.  A field used as an index has to be one
erasure leaves alone, so the steps never move what a later field depends on.
-/
def valCongr (c : BridgeCtx) (cc : CtorSpec) (xs : Array Expr)
    (pf : Nat → TermElabM (Option Expr)) : TermElabM Expr := do
  let b := c.b
  let kept := keptPositions (b.fieldKinds cc.kinds)
  stepCongr (mkAppN (b.cst (b.preOf cc.name)) c.ps) kept.size
    (fun q => do b.preImage xs[kept[q]!]! (← inferType xs[kept[q]!]!))
    (fun q => pf kept[q]!)

/--
Move a minor's result from the constructors that were written to the ones the raw
recursor asks about.

The nice minor is handed the round trip of each field that is at a copy -- the
copy sent to the original and back -- and every renamed constructor it builds is
by definition the raw one at exactly those round trips.  So the whole of the gap
between what the nice minor concluded and what the raw one owes is one
substitution: the raw conclusion with each such field replaced by its round trip
*is* the nice conclusion, definitionally, and closing the round trip a field at a
time closes all of it at once.

That is worth doing on the field axis rather than the conclusion's, because a
conclusion moves in more places than one and they do not move independently.
`U.mk (v : List T) : U (.node v)` has the copy in its index as well as in the
term, and `Ok.node (n) (v : List (Wrap T n)) : Ok (.node n v)` has it in the
index of a proof; walking the arguments would have to carry each along the ones
before it, and the term at a moved index has no equation of its own to be carried
along.  The field they all came from has one.

`cc` is the constructor, `xs` its fields as the raw minor bound them, `concl`
what the raw minor has to conclude at, and `body` what the nice one produced.
-/
def acrossFields (c : BridgeCtx) (cc : CtorSpec) (xs : Array Expr)
    (concl body : Expr) : TermElabM Expr := do
  -- the gap may already be closed, and then there is nothing to close it with.
  -- A motive the bridge restated is stated at the image of its index, so it
  -- reads a field at a copy through `toOrig` itself and the round trip cancels
  -- against it: the nice minor concluded at exactly what the raw one owes, and
  -- an equation put in anyway would have to be true of the round trip instead
  if ← isDefEq (← inferType body) concl then return body
  let b := c.b
  let kinds := b.fieldKinds cc.kinds
  -- the round trip of every field at a copy, and the equation that closes it
  let mut rts := xs
  let mut steps : Array (Nat × Expr) := #[]
  for z in *...xs.size do
    let ty ← inferType xs[z]!
    -- a proof field standing outside the copies -- an erased one, or a recursive
    -- one at a proposition of the block -- is a proof of a member the bridge may
    -- have restated, and then it has moved as well: `Ok v` at the field `v` is
    -- the raw member at the round trip of `v`, and that is where the nice minor's
    -- proof of it sits.  No step of its own -- what moves `v` back carries it --
    -- but the starting point has to know where it went.  `toImage` leaves any
    -- other proof alone
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
    -- a later field may be a proof *about* this one -- `Ok v` at the field `v` --
    -- and it was moved onto the round trip along with it, so it has to be carried
    -- back the same way.  Binding the equation inside the motive is what lets
    -- that happen; nothing but a proof is ever carried, a data field at another
    -- field of a copy being a shape denesting turns down, and two proofs of the
    -- one proposition are the same proof, so the far end meets `xs` exactly
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
    -- the carried proofs moved with this step, and a proof about *two* fields at
    -- copies is still standing on the round trip of the one that has not had its
    -- step yet.  So `cur` follows the body: the same transport the motive made,
    -- at the equation itself rather than at the one it bound, which is the term
    -- the body now holds in that position and so the one the next step has to
    -- read its statement off
    for (k, mot) in carry do
      cur := cur.set! k (← mkEqNDRec mot cur[k]! eq)
    cur := cur.set! z xs[z]!
  return body

/--
The raw motive standing behind the writer's, for a member the bridge restated.

A `Prop` member indexed by a nesting is written over the original and emitted
over the copy, so a motive the raw recursor takes is bound at the copy's
arguments where the writer's is bound at the original's.  Both the arguments and
the proof go across the same way anything else does, `BridgeCtx.toImage` knowing
what to do with each -- which for the proof is a transport onto the round trips
of its own indices, that being what the written statement unfolds to.
-/
def rawPropMotive (c : BridgeCtx) (m : Nat) (nice : Expr) : TermElabM Expr := do
  let b := c.b
  forallTelescope (← instantiateForall b.members[m]!.type c.ps) fun idxs _ =>
    withLocalDeclD `h (mkAppN (b.memberCst m) (c.ps ++ idxs)) fun h => do
      mkLambdaFVars (idxs ++ #[h]) (mkAppN nice (← c.toImages (idxs ++ #[h])))

/--
The equation between the constructor at its fields' round trips and the
constructor at the fields themselves, one step per field that is at a copy.
-/
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
arguments instead of the constructor's fields.

The recursion over the whole block needs this one.  Its `Prop` motives are
stated over what the data recursion returned, so a `Prop` minor's conclusion
mentions the data minors -- and those have already been moved across themselves,
so the conclusion is no longer a function of the fields alone and substituting a
field into it does not produce what the nice minor concluded.  What is still
true is that each argument of the conclusion moved by a rename of its own head,
so they are moved one at a time, with the equation bound inside the motive so
that every later argument standing on the one being moved is carried along.  The
data minor's own conclusion is then carried by exactly the transport that built
it, and the two sides meet.

A proof is never carried: two proofs of the one proposition are the same proof,
so once its indices line up, so does it.
-/
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
sending `x` into the copy and reading it back is `x` again.

`none` when there is nothing to send, which is every type outside the denesting
and so most of them.
-/
def backEq? (c : BridgeCtx) (x ty : Expr) : MetaM (Option Expr) := do
  let some (k, idxs) ← c.copyOf? ty.headBeta | return none
  return some (mkAppN (mkConst c.copies[k]!.backName c.b.lvls) (c.ps ++ idxs ++ #[x]))

/--
A value the raw recursor returned, moved from the round trips of the writer's
indices onto the indices themselves.

A proposition the bridge restated is emitted over the copies, so its recursor has
to be given the copy-world images of the indices, and what it hands back is the
writer's motive at those images read out again -- `(ofOrig a).toOrig` where the
writer wrote `a`.  The two are equal and not the same term, so the value is
carried across one index at a time, `X.toOrig_ofOrig` closing each and the
equation bound inside the motive so that the proof standing on the index comes
along with it.  Nothing moves at all in a block with no such member, the
recursor's own statement being the writer's already.

`raws` is what the value ought to be stated at -- the writer's indices, and the
major premise with them where the caller has one.  Which argument each of them is
the round trip of is looked for rather than counted off, a motive taking more
arguments than the writer wrote indices as soon as the recursion over the whole
block is the one being restated: there the value the data recursion returned
stands between the index and the proof, and it moves along with the index it is
stated over rather than on any step of its own.  What the value is stated at is
read off its own type, that always being a motive applied.
-/
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
Add a restatement of the raw recursor `recCst`, stated over the block's
parameters, the nice motives and minors, and concluding at `goalMot`.  The raw
motives and minors are what the value passes on, each of them sending its
arguments across.  Everything ahead of the major premise is implicit, as it is
in a recursor Lean generates for itself.
-/
def addRestated (c : BridgeCtx) (i : Nat) (lp niceName : Name)
    (nmots nmins : Array Expr) (goalMot recCst : Expr)
    (rmots rmins : Array Expr) : TermElabM Unit := do
  let b := c.b
  let (type, value) ←
    forallTelescope (← c.niceArity i) fun idxs _ =>
      withLocalDeclD `t (mkAppN (b.cst b.members[i]!.name) (c.ps ++ idxs)) fun t => do
        let hide := hideRecBinders c.ps.size (nmots.size + nmins.size) idxs.size
        let all := c.ps ++ nmots ++ nmins ++ idxs ++ #[t]
        -- the raw recursor is indexed over the copies, so the major premise's
        -- indices go across; the premise itself does not, the written statement
        -- of a member being by definition the raw one at those very images
        let rIdxs ← c.ofImages idxs
        -- `goalMot` is a motive when the conclusion is just that motive at the
        -- indices, and a function of them when the conclusion is more than that
        return (hide (← mkForallFVars all
                  (← Core.betaReduce (mkAppN goalMot (idxs ++ #[t])))),
                hide (← mkLambdaFVars all
                  (mkAppN recCst (c.ps ++ rmots ++ rmins ++ rIdxs ++ #[t]))))
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
  -- `(X.ofOrig (X.toOrig t)).val`, for `t` a term of the copy at `ids`.  The
  -- value and its well-formedness are stated in the pre-world, so a copy that
  -- deleted an index of its own has its arguments crossed over first
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
      let ihPos := ihPositions kinds
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

`ofOrig_toOrig` starts at the copy and comes back to it, and that is an
induction over the copy, which is a member of this block.  `toOrig_ofOrig`
starts at the original, and that is a different induction altogether: over a
type that is no member of anything here, but an ordinary inductive with a
recursor of its own.

The scheme is `ofOrig`'s for a `Prop` copy.  Every copy in the group is given
its round trip as a motive, everything else the original's recursor eliminates
goes to `True`, and a field at a group member contributes the hypothesis the
recursor supplies rather than a call.  Each minor is then a congruence between
one constructor at two lots of arguments, because `toOrig` and `ofOrig` both
reduce at a constructor; a field is left alone where the round trip already
comes back by itself -- through a structure it does, by eta -- and is otherwise
either that hypothesis or the round trip of whichever copy the field is at.

The congruence is `mkHCongrWithArity`'s and so heterogeneous, which is what it
takes for a field the block's own shape indexes by another: what moves under
such a field moves its type with it, and there is no equation to state, only a
`HEq`.  A data field in that position is out of reach, but a `Prop` one is
exactly `proof_irrel_heq` -- and that is the shape a denested ind-ind original
has, a proof carried alongside the thing it is about.

What this is for is `ofOrig_inj`, and through it the injectivity of a
constructor with a field at a copy.  What `injection` leaves at such a field is
an equation between the two sides' `ofOrig`s, and `ofOrig_toOrig` is the wrong
half of the round trip to get anything out of it.
-/

/-- `X.toOrig (X.ofOrig x)`, for `x` the original at `jdxs`. -/
def backLhs (c : BridgeCtx) (k : Nat) (jdxs : Array Expr) (x : Expr) : MetaM Expr := do
  let cp := c.copies[k]!
  let imgs ← c.ofImages jdxs
  return mkAppN (mkConst cp.toName c.b.lvls)
    (c.ps ++ imgs ++ #[mkAppN (mkConst cp.ofName c.b.lvls) (c.ps ++ jdxs ++ #[x])])

/--
`X.toOrig_ofOrig`, by the original's own recursor at the whole group.

A field at another copy is read back by *that* copy's round trip, which may not
have been proved yet -- so `wanted` is where the name of one that was missing is
left, for the caller to prove and come back with.
-/
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
          -- a field that is a function into the group is given a
          -- hypothesis for each of its values, and the equation wanted is
          -- of the two functions
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
each copy those turn out to be proved at.

`needed` is where the writer's own constructors have a field, and a copy's round
trip is proved at *its* constructors, whose fields may be at copies further in
again.  Which of those actually want a round trip of their own is not something
to read off the fields: at a great many of them it comes back by itself, and a
copy asked for on the strength of having a field there would be a pair of
theorems nobody ever names.  So the copy that was missing is the one the proof
says it wanted, and the pass is simply run again for it -- until a go round
learns nothing new, which it must, there being finitely many copies.

Nothing the block emits needs any of this, so a failure costs only the pair it
was proving and goes to the trace rather than taking the bridge down with it.
That is what the last pass is for: the rounds before it fail quietly, since
"the copy further in is not there yet" is a state of affairs and not a fault.
What a real failure costs in the end is the injectivity of whichever
constructors had a field at the copy that failed.
-/
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
The recursor for a member the writer declared, with only originals in it.

The motives are over the originals, the minors are over the originals'
constructors, and the copies are gone from both.  The value is the raw recursor
at motives that send their argument across first; every minor then lines up
definitionally, except for a constructor of the writer's own that had to be
renamed -- there the raw one comes out at the round-tripped fields, and the round
trip is what closes the gap.
-/
def addNiceRec (c : BridgeCtx) (i : Nat) (lp : Name) (rawRec : Nat → Name)
    (niceName : Name) (rawOf : Name → Name) : TermElabM Unit := do
  let b := c.b
  let lvl := Level.param lp
  let dIdxs := b.dataIdxs
  let mnames := motiveNames dIdxs.size
  let motiveDecls : Array (Name × (Array Expr → TermElabM Expr)) :=
    dIdxs.mapIdx fun q m => (mnames[q]!, fun _ => do
      match c.copyAt? m with
      | some k =>
        let cp := c.copies[k]!
        forallTelescope (← inferType cp.app) fun jdxs _ =>
          withLocalDeclD `t (cp.origAt jdxs) fun t =>
            mkForallFVars (jdxs ++ #[t]) (mkSort lvl)
      | none =>
        forallTelescope (← c.niceArity m) fun ids _ =>
          withLocalDeclD `t (mkAppN (b.cst b.members[m]!.name) (c.ps ++ ids)) fun t =>
            mkForallFVars (ids ++ #[t]) (mkSort lvl))
  withImplicits motiveDecls fun nmotives => do
    let mut minorDecls : Array (Name × (Array Expr → TermElabM Expr)) := #[]
    for m in dIdxs do
      for cc in b.members[m]!.ctors do
        minorDecls := minorDecls.push (Name.mkSimple cc.name.getString!, fun _ => do
          forallTelescope (← c.unCopy (← instantiateForall cc.type c.ps)) fun ys concl => do
            let kinds := b.fieldKinds cc.kinds
            let ihDecls : Array (Name × (Array Expr → TermElabM Expr)) :=
              (ihPositions kinds).map fun z => (`ih, fun _ => do
                let some mm := kinds[z]!.ihTarget? | throwError "Not a recursive field"
                forallTelescope (← inferType ys[z]!) fun zs tgt => do
                  mkForallFVars zs (mkAppN nmotives[c.dpos mm]!
                    ((← c.niceIdxArgs mm tgt) ++ #[mkAppN ys[z]! zs])))
            withLocalDeclsD ihDecls fun ihs => do
              let ctorApp := match c.copyAt? m with
                | some k => c.copies[k]!.origCtor cc.name ys
                | none   => mkAppN (b.cst cc.name) (c.ps ++ ys)
              mkForallFVars (ys ++ ihs) (mkAppN nmotives[c.dpos m]!
                ((← c.niceIdxArgs m concl) ++ #[ctorApp])))
    withLocalDeclsD minorDecls fun nminors => do
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

/--
The recursor over the whole block, with only originals in it.

`emitGrandRecs` has already built one over the copies, and its shape is the shape
wanted -- a motive per member, a minor per constructor, a `Prop` motive taking the
value the recursion produced at the data member it is indexed by.  So nothing is
reconstructed from the block here.  Each binder is the raw binder with the copies
put back as originals, the binders before it replaced by the ones already built,
and a constructor of the writer's own that had to be renamed put back under the
name that was written.  The value is the raw recursor at motives that send their
arguments across first, the way `BridgeCtx.addNiceRec` does it, and the round trip
closes the same gap at the same place.

Which member the whole thing recurses at is read off the raw recursor too: the
motive it concludes at is the one the major premise belongs to.

For a `Prop` member the conclusion is more than that motive at the indices: the
motive also takes the value the data recursion returned, and the raw recursor
writes it with the raw recursor over the copies at the raw binders.  The nice
recursor for that member is defined as exactly that, so the application is
rebuilt at the nice binders rather than substituted into -- substituting would
leave an internal name and the transported binders in a type a writer reads.
`ready` says which members already have theirs, since one that fell back to its
split recursor has nothing of the right shape to be rebuilt at.
-/
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
              -- a constructor that *builds* an index the erasure deleted has
              -- the copy in the index and in the term at once, and the term at
              -- a moved index has no equation of its own to be carried along;
              -- the field they both came from has one, so that one moves on the
              -- field axis.  Everything else moves on the argument axis, and
              -- has to: a `Prop` minor's conclusion mentions the data minors,
              -- so a data minor that moved the other way would no longer be the
              -- term the `Prop` minor is carrying
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
            -- a copy is a member of the block and so covered by the recursion,
            -- but it is nothing the writer named and there is no name to read
            -- its recursion under.  The value could be put in as the term it is,
            -- and the statement would then be about the recursion over the
            -- denesting rather than over anything written; the split recursor
            -- says less and says it in the writer's own words, so the block is
            -- better off with that one
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
def propRecPositions (b : Block) (kinds : Array FieldKind) : Array Nat :=
  (recPositions kinds).filter fun z =>
    match kinds[z]! with
    | .recur m => b.members[m]!.isProp
    | _        => false

/--
What the two `Prop` recursor builders both read off the pre-block's recursor.

The raw recursor of `BridgeCtx.addPropRecs` and the restatement of
`BridgeCtx.addNicePropRec` have to agree on the members they run over, the order
they run over them in and the universe they eliminate into, and all three come
from the same place.  Reading them once keeps the two in step.
-/
structure PropRecs where
  /-- The pre-block's own recursor, which a raw one is one application of. -/
  info : RecursorVal
  /-- Every `Prop` member behind that recursor, in the order it runs over them. -/
  pIdxs : Array Nat
  /--
  The ones a recursor is wanted for.  The rest still get a motive and a minor,
  since the pre-block recurses through all of them at once, but nobody has to
  see them: theirs are the trivial ones, and the caller has already made sure
  that nothing kept recurses into one.
  -/
  kIdxs : Array Nat
  /-- The motives' universe. -/
  lvl : Level
  /-- The levels the pre-block's recursor is taken at. -/
  recLvls : List Level
  /-- The level parameters a recursor built from it takes. -/
  us : List Name

/--
Read that off the block, or `none` if there is nothing here to build.

`lp` is a level parameter the writer cannot have taken; the recursor carries one
of its own exactly when the pre-block's does, which is to say when it eliminates
large.
-/
def propRecs? (b : Block) (lp : Name) (keep : Array Nat) : MetaM (Option PropRecs) := do
  if b.propIdxs.isEmpty then return none
  let info ← getConstInfoRec (mkRecName (preName b.members[b.propIdxs[0]!]!.name))
  let pIdxs ← b.propsBehind info
  let kIdxs := pIdxs.filter (keep.contains ·)
  if kIdxs.isEmpty then return none
  let large := info.levelParams.length != b.us.length
  let lvl := if large then Level.param lp else Level.zero
  return some { info, pIdxs, kIdxs, lvl
                recLvls := if large then lvl :: b.lvls else b.lvls
                us := if large then lp :: b.us else b.us }

/--
`X.rec` for a `Prop` member, stated over the block rather than the pre-types.

A `Prop` member is *defined* as its pre-form at the `.val`s of its indices, so
`X._pre.rec` is nearly the recursor already; what it has wrong is the world its
motive and minors are stated in.  The motive is transported the way
`toOrigPre`'s is -- `fun pres h => ∀ ws, C (pres rebuilt with ws) h` -- and the
major premise's own indices supply the `ws` at the very end, where
`⟨t.val, t.property⟩ ≡ t` closes it.

A minor then arrives with its fields in the pre-world, and a field of a *data*
member's type has to be put back at the subtype.  The proof that lets it be is
in the conclusion: `X._wf` at a constructor is the conjunction of the `_wf`s of
its recursive fields, so the well-formedness of the conclusion's indices
contains the well-formedness of everything the constructor was built from.  A
field the conclusion does not reach that way is not rebuildable -- `X._pre` is
then genuinely larger than `X`'s image in it -- and the group is dropped rather
than half-emitted.

A field of a `Prop` member's type needs nothing done to it, since `P args` *is*
`P._pre args'`; only its induction hypothesis does, and that is the raw one at
the same well-formedness proofs the fields were rebuilt with, so the two line up
definitionally.

The motives cover every `Prop` member of the block and the minors every
constructor of one, which is what the pre-block's own recursor does.  The data
members are a separate block with a recursor of their own, so a `Prop`
constructor's data field arrives without a hypothesis -- correctly, since
nothing recurses into it.
-/
def addPropRecs (c : BridgeCtx) (s : PropRecs) (recNameOf : Nat → Name) :
    TermElabM Unit := do
  let b := c.b
  let ps := c.ps
  let { info := recInfo, pIdxs, kIdxs, lvl, recLvls, us } := s
  let ppos (m : Nat) : Nat := (kIdxs.findIdx? (· == m)).getD 0
  let mnames := motiveNames kIdxs.size
  let motiveDecls : Array (Name × (Array Expr → TermElabM Expr)) :=
    kIdxs.mapIdx fun q j => (mnames[q]!, fun _ => do
      forallTelescope (← instantiateForall b.members[j]!.type ps) fun idxs _ =>
        withLocalDeclD `h (mkAppN (b.memberCst j) (ps ++ idxs)) fun h =>
          mkForallFVars (idxs ++ #[h]) (mkSort lvl))
  withImplicits motiveDecls fun motives => do
    let mut minorDecls : Array (Name × (Array Expr → TermElabM Expr)) := #[]
    for j in kIdxs do
      for cc in b.members[j]!.ctors do
        minorDecls := minorDecls.push (Name.mkSimple cc.name.getString!, fun _ => do
          forallTelescope (← instantiateForall (b.toRaw cc.type) ps) fun xs concl => do
            let kinds := b.fieldKinds cc.kinds
            let ihDecls : Array (Name × (Array Expr → TermElabM Expr)) :=
              (propRecPositions b kinds).map fun z => (`ih, fun _ => do
                let r? ← b.withRecTarget? (← inferType xs[z]!) fun ys m args =>
                  mkForallFVars ys
                    (mkAppN motives[ppos m]! (b.idxArgs args ++ #[mkAppN xs[z]! ys]))
                let some e := r? | throwError "Not a recursive field of `{cc.name}`"
                return e)
            withLocalDeclsD ihDecls fun ihs =>
              mkForallFVars (xs ++ ihs) (mkAppN motives[ppos j]!
                (b.idxArgs concl.getAppArgs ++
                  #[mkAppN (b.cst (b.rawCtor cc.name)) (ps ++ xs)])))
    withLocalDeclsD minorDecls fun minors => do
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
          let ihPos := propRecPositions b kinds
          out := out.push <| ←
            forallBoundedTelescope (← inferType ms[q]!) (kinds.size + ihPos.size)
              fun args concl => do
                let xs := args.extract 0 kinds.size
                let ihs := args.extract kinds.size args.size
                let subTys ← b.subFieldTys cc ps xs
                forallTelescope (← whnf concl) fun ws _ => do
                  let mut parts : Array (Expr × Expr) := #[]
                  for w in ws do
                    parts := parts ++ (← wfParts w)
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
                        -- raw one at the well-formedness the rebuild used
                        vals := vals.push xs[z]!
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

/--
`X.rec` for a `Prop` member, with only originals in it.

The `Prop` side of `BridgeCtx.addNiceRec`, and a much shorter one.  A copy the
recursion reaches gets its motive over the original it stands for and its minors
over the original's constructors; the value is the raw recursor at motives that
send their argument across with `toOrig` first, and at minors that do the same
to their fields.

The proof itself needs no transporting back, which is where this is shorter than
the data side.  Every copy a `Prop` member's recursion reaches is a copy of a
*proposition* -- that is what put it in this group -- so a minor's conclusion is
a statement about a proof, and the raw constructor and the one the bridge renamed
are the same proof to the kernel.  On the data side that gap costs a transport;
proof irrelevance closes it here for nothing.

What the proof *carries* is another matter, and that is what
`BridgeCtx.acrossFields` is for -- the same function the data side uses, closing
the same round trips.
-/
def addNicePropRec (c : BridgeCtx) (s : PropRecs) (j : Nat) (rawRec : Nat → Name)
    (niceName : Name) : TermElabM Unit := do
  let b := c.b
  let ps := c.ps
  let kIdxs := s.kIdxs
  let ppos (m : Nat) : Nat := (kIdxs.findIdx? (· == m)).getD 0
  let mnames := motiveNames kIdxs.size
  let motiveDecls : Array (Name × (Array Expr → TermElabM Expr)) :=
    kIdxs.mapIdx fun q m => (mnames[q]!, fun _ => do
      match c.copyAt? m with
      | some k =>
        forallTelescope (← inferType c.copies[k]!.app) fun jdxs _ =>
          withLocalDeclD `h (c.copies[k]!.origAt jdxs) fun h =>
            mkForallFVars (jdxs ++ #[h]) (mkSort s.lvl)
      | none =>
        forallTelescope (← c.niceArity m) fun idxs _ =>
          withLocalDeclD `h (mkAppN (b.cst b.members[m]!.name) (ps ++ idxs)) fun h =>
            mkForallFVars (idxs ++ #[h]) (mkSort s.lvl))
  withImplicits motiveDecls fun nmotives => do
    let mut minorDecls : Array (Name × (Array Expr → TermElabM Expr)) := #[]
    for m in kIdxs do
      for cc in b.members[m]!.ctors do
        minorDecls := minorDecls.push (Name.mkSimple cc.name.getString!, fun _ => do
          forallTelescope (← c.unCopy (← instantiateForall cc.type ps)) fun xs concl => do
            let kinds := b.fieldKinds cc.kinds
            let ihDecls : Array (Name × (Array Expr → TermElabM Expr)) :=
              (propRecPositions b kinds).map fun z => (`ih, fun _ => do
                let .recur mm := kinds[z]! | throwError "Not a recursive field"
                forallTelescope (← inferType xs[z]!) fun zs tgt => do
                  mkForallFVars zs (mkAppN nmotives[ppos mm]!
                    ((← c.niceIdxArgs mm tgt) ++ #[mkAppN xs[z]! zs])))
            withLocalDeclsD ihDecls fun ihs => do
              let ctorApp := match c.copyAt? m with
                | some k => c.copies[k]!.origCtor cc.name xs
                | none   => mkAppN (b.cst cc.name) (ps ++ xs)
              mkForallFVars (xs ++ ihs) (mkAppN nmotives[ppos m]!
                ((← c.niceIdxArgs m concl) ++ #[ctorApp])))
    withLocalDeclsD minorDecls fun nminors => do
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
                  (nf + (propRecPositions b kinds).size) fun args concl => do
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

Steps 8 and 9 below build two separate recursors: one for the data members,
whose motives run over the data members only, and one for the `Prop` members,
whose motives run over those.  That is enough to compute with, but it is not the
eliminator the block deserves: a `Prop` member of an induction-inductive block
is indexed by a data member, so its motive ought to be allowed to mention the
*value* the recursion produced at that index, and a data constructor that
carries a proof ought to get an induction hypothesis for it.  Written out for

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

and `Fresh.rec` takes the very same motives and minors.  The two motives cannot
be merged into one -- `Fresh` is small-eliminating, so nothing may land in
`Sort u` by recursion on it -- but they can be *taken together*, which is
exactly the shape above.

It has to be one recursion, because the two halves are interleaved: the value at
`Ctx.snoc Γ x h` needs the proof-motive's value at `h`, which needs the
data-motive's value at `Γ`.  So the recursion computes, at each pre-term, a
**bundle**: the data value paired with the proof-motive's value at *every* proof
of *every* `Prop` member indexed by that pre-term.

```
Bundle p := (w : Ctx._wf p) →
  PSigma fun c : motive_1 ⟨p, w⟩ => ∀ x (h : Fresh._pre x p), motive_2 x ⟨p, w⟩ c h
```

The pairing is a `PSigma` rather than a `Subtype` because the first component is
data; and it stays a `PSigma` even for a data member no `Prop` member is indexed
by (with `fun _ => True` as the second component), so that every member's bundle
lands in `Sort (max 1 u)` and the group can recurse together.

Building the bundle at a data constructor is where the work is.  The data
component is the minor applied to the rebuilt fields, whose proof-field
hypotheses come out of the bundle's *own* second component at the recursive
field the proof is about.  The proof component is proved by inverting the
`Prop` member's pre-form at the constructor: index unification forces the
proof's fields to be the constructor's own, so the `Prop` minor's data
hypotheses are the sibling bundles' first components and its proof hypotheses
their second.  The inversion is `Lean.Meta.cases`, which discharges the
alternatives that cannot happen; the recursive calls are named before it runs so
that structural recursion sees them at the top of the alternative rather than
buried under the equations the inversion introduces.
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

/--
Of a `Prop` member's indices, the ones its slot does not already account for.

Fixing the data index fixes that member's own indices too, so a proof component
is stated over the rest alone; whoever applies it has to leave out exactly the
same ones.
-/
def PropSlot.freeArgs (s : PropSlot) (args : Array Expr) : Array Expr :=
  (Array.range args.size).filterMap fun z =>
    if z == s.pos || s.bound.contains z then none else some args[z]!

/--
The index arguments of the data member a `Prop` member's principal index is at.
`who` names the member for the error, which is a malformed block rather than
something the caller can recover from.
-/
def dataIdxArgs (b : Block) (who : Name) (d : Expr) : MetaM (Array Expr) := do
  let some args ← b.withRecTarget? (← inferType d) fun _ _ args => pure (b.idxArgs args)
    | throwError "The index `{d}` of `{who}` is not a member's type"
  return args

/--
Read a slot off every `Prop` member of the block.

A grand recursor puts each `Prop` member it covers in the bundle of one data
member, so it needs a single index of that member's to settle all the rest: a
bundle carries the hypotheses about one data value and no more.  The last data
index is the one that stands the best chance, since a later index is stated over
the earlier ones, and it settles them exactly when it names them all -- the
`Ty Γ` of `Wf : (Γ : Ctx) → Ty Γ → Prop` has the `Γ` as its own index, so the
`Ty` bundle already knows which `Ctx` it is over.  Two data indices that fix
each other not at all are two the one bundle cannot hold hypotheses for.

A member indexed by *no* data member is a different matter: there is no bundle
to put it in, but neither is there anything for it to be in one for.  It gets no
slot, and the caller leaves it out of the recursion rather than giving up on the
block; a recursor of its own comes from the split ones.  So an empty result
means every `Prop` member is free-standing, and `none` means one of them is
genuinely in the way.

The slots come back in *settle* order rather than block order.  A bundle's proof
components are built one after another, and `WF.intro (l) (t) (h : WFWith t l)`
asks for `WFWith` at the very term `WF` is being proved at -- where the only
thing that can stand for it is a component already built.  So a `Prop` member
another wants at its own principal term comes first.  Which order that is, is not
something the writer chose: denesting names the copies in the order it meets
them, and the block that comes out can have the two either way round.
-/
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
Re-bind a `Prop` member's index telescope with its data index pinned to
`target` (and that index's own indices to `dIdxs`).  `k` receives the indices
that stayed free, all of them in order, and their pre-world images -- with
`targetPre` standing in for `target`, which is where the pre-term itself goes.
-/
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

/--
The recursor's own value at a term of a member's type, as the minors see it.

A minor's conclusion says what the recursion returns at the constructor it is
for, and a `Prop` member's motive takes the data motive's value at its index --
so a `Prop` minor's conclusion has to name that value.  The index is built out
of the constructor's fields, so the value is built the same way: a field's value
is its induction hypothesis, and a constructor's is the minor for it, applied to
the fields' values in turn.  Anything else is not something the recursion has a
value for, and the block gets the split recursors instead.

Which fields carry a hypothesis is `hasIh`, and it differs between the callers:
the recursion over the whole block has a motive at every member, so a proof
field carries one too, while the recursion over the data members alone has
hypotheses only where it recursed.

`bundled` asks for the whole bundle at the term rather than the motive's value,
which a caller wants when the hypothesis is going to a `recAux` whose deleted
indices carry their propositions with them.  Only a term already under a
hypothesis can answer that: rebuilding one out of a minor gets the value and
nothing else, since the propositional half of a bundle at a constructor is
proved by inverting a proof of it, which is the recursion's own work and not
something to be done a second time out here.
-/
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
that is not itself inside the recursion.

`X.rec` is such a caller: it has a term and no hypothesis about anything, so the
one a member's `recAux` wants at each index it deleted has to be produced here,
by recursing at that index.  Which is finite -- the recursion is on the arity,
and an index of `Tm` is a `Ty` whose index is a `Ctx` whose arity is empty --
and, unlike the hypotheses an alternative builds, under no obligation to
decrease, since `X.rec` does not call itself.

`answer` is what the caller's `recAux` returns read as the motive's value, told
the member, its real indices, the pre-term and its well-formedness -- which is
everything the reading can depend on, and the same four the caller states the
return type from.  The recursion over the data members alone returns the value
already and leaves it alone; the one over the whole block returns a bundle,
whose first component it is.  It is applied at every level, because a hypothesis
built here is handed to a `recAux` that wants the same reading of it.
-/
partial def valueIh (b : Block) (recAuxName : Nat → Name) (lvl : Level)
    (ps motives minors : Array Expr) (v : Expr)
    (answer : Nat → Array Expr → Expr → Expr → Expr → MetaM Expr :=
      fun _ _ _ _ e => pure e) : MetaM Expr := do
  let r? ← b.withRecTarget? (← inferType v) fun _ mm args => do
    let dihs ← (b.dropArgs mm args).mapM
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
actually recurse.

`Structural.structuralRecursion` wants a group that is mutually recursive:
handed one whose members are independent it throws, and handed one where only
some of them recurse it panics inside Lean's fixed-parameter analysis before it
gets as far as throwing.  A block's members are under no obligation to be
mutually recursive -- `A` may nest a family over `B` while `B` never mentions
`A` -- so the call graph is condensed into its strongly connected components
and each one is added on its own, callees first.

A component of one that does not call itself is not a recursion at all and goes
the direct way.  Everything else goes to `structuralRecursion`, which throws if
it cannot see that the definitions terminate; that is what we want, and is why
`addPreDefinitions`, which would quietly fall back to `partial` or `sorry`, is
not used.
-/
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

/--
The auxiliary recursors over the pre-types, added as one group.

Both the split recursors and the grand one are stated over a member's type and
proved by an auxiliary that runs over its pre-type instead, and neither kind can
be added on its own: the auxiliaries call each other exactly as the pre-block's
members do.  So each kind hands its whole array here, and the sorting into
mutually recursive groups happens once, in `addRecGroups`.
-/
def addRecAuxs (docCtx : LocalContext × LocalInstances) (levelParams : List Name)
    (auxs : Array (Name × Expr × Expr)) : TermElabM Unit :=
  addRecGroups docCtx <| auxs.map fun (declName, type, value) =>
    { ref := .missing, kind := .def, levelParams, modifiers := {}, declName,
      binders := .missing, type, value, termination := TerminationHints.none }

/--
Check that no `Prop` constructor pins a field of the data constructor it is
about.

What proves a bundle's proof component is an inversion, which unifies the `Prop`
constructor's principal index against the data constructor the recursion is at.
What that may not do is pin one of *the data constructor's* fields: the
recursion has a call at the field, and once the field has been replaced the call
is at a term that is no longer a subterm of what is being recursed on.  So a
principal index has to be a variable, or a constructor at fields of its own, all
of them different.

One step and no more.  A nesting through two types at once -- `List (Except
String T)` denests to a copy of `List` over a copy of `Except` -- can have a
`Prop` constructor whose index is one copy's constructor at another's, and the
unification does walk into both.  What does not follow it is the recursion: the
alternative being filled in is the outer copy's, so a call is in hand at each of
*its* fields and at nothing inside them.  Admitting the deeper tree on the
grounds that the leaves below the top need no hypothesis was tried, and does not
help either -- what the value then needs is a call at the outer field itself,
inside the inversion that took it apart, and Lean's structural recursion cannot
see that one.  So the shallow rule is the real one, and saying so precisely is
worth more than reaching one step further and failing later with a worse
message.
-/
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
that stay.

A `Prop` member no data member indexes rides in no bundle, so it is left out
entirely.  That is only sound if nothing that stays recurses into it -- a field
of its type would want a hypothesis at a motive that is not there -- and if it
does not recurse into a `Prop` member that stays, since the split recursors it
will be given instead would then have to name one this emits.
-/
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
pre-term, and a proof that the pre-term is well-formed.

That is what both recursions over the block run under, the grand one and the
split ones.  The predicate is stated in the pre-world, so an index the pre-type
deleted reaches it at its value; and since such an index is not in the term the
recursion runs on, there is nothing there to recurse at, so the caller is handed
a hypothesis about it instead, of whatever shape `ihTypeAt` gives it.
-/
def withPreRec {α} [Inhabited α] (b : Block) (i : Nat) (ps : Array Expr)
    (ihTypeAt : Expr → MetaM Expr)
    (k : Array Expr → Array Expr → Array Expr → Expr → Expr → TermElabM α) : TermElabM α := do
  forallTelescope (← instantiateForall b.members[i]!.type ps) fun idxs _ => do
    let vargs ← b.valArgs i (ps ++ idxs)
    let delDecls : Array (Name × (Array Expr → TermElabM Expr)) :=
      (b.dropIdxs i idxs).map fun d => (`ih, fun _ => ihTypeAt d)
    withLocalDeclsD delDecls fun delIhs =>
      withLocalDeclD `t (b.preApp i (ps ++ idxs)) fun t0 =>
        withLocalDeclD `w (mkApp (b.wfApp i vargs) t0) fun w =>
          k idxs vargs delIhs t0 w

/--
The auxiliary recursion at member `i`, as a type and a value: everything a
`withPreRec` opened, abstracted over `concl`, with the value one `casesOn` on
the pre-term taking `alts` at the constructors.

A deleted index is not read off the pre-term, so the `casesOn` stands under
everything the pre-type dropped -- those indices, the hypotheses at them, and
the well-formedness proof -- and is applied to them again afterwards.
-/
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
recursion.  Throws if the block is not one this can be done for, and the caller
falls back to the split recursors.

A `Prop` member no data member indexes is not induction-inductive with anything,
and having one is no reason to give up on the members that are.  Such a member
is left out: it gets no motive, no minor and no recursor here, and the returned
indices tell the caller which ones it still owes a recursor to.

`bundled` says what a deleted index arrives under.  An index the pre-type
dropped is not in the term the recursion runs on, so the caller has to hand a
hypothesis about it in; the plain reading of that hypothesis is the motive's
value, which is all a data member ever asks of it.  A `Prop` constructor can ask
for more -- `Wf.base : (Γ : Ctx) → Ok Γ → Wf Γ (Ty.base Γ)` wants the `Ok` at a
`Γ` that `Ty.base` deleted -- and then the hypothesis has to be the whole bundle.
That costs generality at the other end, since a bundle cannot be rebuilt out of
a minor, so the caller tries this way first and falls back to the plain reading.
-/
def emitGrandRecs (b : Block) (docCtx : LocalContext × LocalInstances) (lp : Name)
    (recNameOf recAuxName : Nat → Name) (ctorNameOf : Name → Name) (bundled : Bool) :
    TermElabM (Array Nat) := do
  let dIdxs := b.dataIdxs
  if dIdxs.isEmpty || b.propIdxs.isEmpty then
    throwError "Not an induction-inductive block"
  let lvl := Level.param lp
  let ihName (n : Name) : Name := if n.hasMacroScopes then `ih else n.appendAfter "_ih"
  -- everything below is stated in the raw world, where the copies are the types
  -- and anything the bridge will rename goes by its hidden name -- a constructor
  -- whose type mentions a copy, and a proposition indexed by one.  A constructor
  -- type reaches that world when a proposition's index pins a data constructor,
  -- or when it names the proposition it belongs to, and neither plain name is
  -- defined until the bridge runs
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
    -- a field a `Prop` constructor's conclusion forgets has no well-formedness to
    -- be put back at its subtype with, so the recursion stands an arbitrary
    -- element of its type in.  That is sound here because every `Prop` member of
    -- this recursor has a slot, and a member with a slot gets a `Prop`-valued
    -- motive, so the minor is building a proof -- and two proofs of one
    -- proposition are definitionally equal, which is exactly what says the
    -- substitute does as well as the value that was meant
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
    -- not.  A deleted index is one of them even though the pre-constructor has
    -- no field for it, because the recursion was handed a hypothesis about it
    -- on the way in -- see `FieldKind.ihTarget?`, which this agrees with once
    -- the erased proof fields a `Prop` member contributes are added
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
        -- at the pre-type.  The component is *stated* in the bundle's type and
        -- *proved* in the bundle's value, so the two have to agree about them
        let withSlotBinders {α} [Inhabited α] (s : PropSlot) (mIdxs : Array Expr)
            (target p : Expr) (k : Array Expr → Array Expr → Expr → MetaM α) : MetaM α := do
          withSlotIdxs b s mIdxs target p (← instantiateForall b.members[s.j]!.type ps)
            0 #[] #[] #[] fun free all pres =>
              withLocalDeclD `h
                (mkAppN (b.cst (preName b.members[s.j]!.name)) (ps ++ pres)) fun h =>
                  k free all h
        -- the bundle: what the recursion computes at a pre-term.  It is indexed
        -- twice over, because its two halves live in different worlds: `mIdxs`
        -- are the member's indices in the real one, which is the only world a
        -- motive is stated in, and `vargs` the same arguments in the pre-world,
        -- where the pre-term and its well-formedness are.  A block that deletes
        -- no index spells the two the same way
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
        -- the two components of a bundle's type.  Whether a term really is a
        -- bundle depends on how the recursion arrived at it, and the ones that
        -- turn out not to be are the block's answer that the joint reading does
        -- not hold together -- so this reports rather than taking the type
        -- apart on faith, which aborts the process instead of the elaboration
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
        -- recursion runs on does not have the index in it to recurse at.
        -- `bundled` is the reading that carries the propositions about the index
        -- too, which a `Prop` constructor naming one of them needs
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
        -- an index of a `Prop` member, back at the subtypes.  An index the
        -- constructor being recursed at deleted is real already, and there is
        -- nothing in the alternative's well-formedness to put it back together
        -- from -- the pre-constructor dropped it rather than carrying a proof
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
        -- subterm of the pre-term being recursed at: `WF.intro (l) (t) (h : WFWith t l)`
        -- has the pre-term itself in it, and asks for the data value there and
        -- for the component of a `Prop` member at the very same place.  So the
        -- bundle under construction stands in for a recursive call, its first
        -- component being `self` and its slot components the ones already built.
        -- `delAt` is the other way a data field can fail to be a subterm: it can
        -- be an index the constructor being recursed at *deleted*, in its
        -- pre-image and its real reading, with the hypothesis it arrived under
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
                -- a recursive field read in both worlds at once.  The pre-world
                -- reading is what the encoding's terms are built out of and the
                -- real one is where the motives are; the two are the same
                -- telescope, so the second is instantiated at the first's binders
                let withField {α} [Inhabited α] (k : Nat)
                    (f : Array Expr → Nat → Array Expr → Array Expr → MetaM α) : MetaM α := do
                  let r? ← b.withRecTarget? subTys[k]! fun ys mm pargs => do
                    let rConcl ← instantiateForall (← inferType xs[k]!) ys
                    f ys mm pargs rConcl.getAppArgs
                  let some e := r?
                    | throwError "The field `{xs[k]!}` of `{c.name}` is not a member's type"
                  return e
                -- the recursive calls, named before anything else, so that
                -- structural recursion meets them at the top of the alternative.
                -- They are built over the constructor's own fields and moved to
                -- the alternative's binders at the end, because the hypothesis a
                -- deleted index wants is found by the shape of the index term
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
                  mkLambdaFVars (keptImages imgs ++ dels ++ dIhs ++ #[wc])
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

/--
A data member's recursor, in the two forms step 8 builds it in.

The auxiliary is the one that does the work: it runs over the pre-type, and
takes the well-formedness proof as an argument of its own, which is what leaves
the recursion structural enough for the equation compiler to see.  The other is
what a writer reaches for, stated over the member's own type, and is nothing
but the auxiliary applied to the subtype's two projections.  They have to travel
together because the first is added by the group and the second one at a time.
-/
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

/--
The data members' pre-types, as real declarations.

They are one mutual inductive whenever they agree about their universe, and the
kernel takes that as it stands.  When they do not agree, the rule being broken
is the kernel's own same-universe rule for a mutual block -- which is precisely
the rule `Mumi.Lowering` exists to lift.  So the pre-block is handed to the
lowering instead: it splits into one ordinary mutual inductive per strongly
connected component, emits them in topological order, and stitches the pieces
back into a recursor ranging over the whole block again.

Erasure and lowering are two different restrictions being lifted, and this is
where they compose.  Erasure removes the dependency of one member's *arity* on
another; what it leaves behind is an ordinary mutual block, which may or may not
also be heterogeneous, and lowering is what answers that second question.
Neither pass has to know anything about the other's problem.

Either way, what comes back out is `X._pre`, its constructors, and one recursor
over all of it, which is all the rest of the encoding asks for.  The return
value is how many motive universes that recursor takes -- one on the direct
path, one per component on the lowered one.
-/
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
    -- pre-block, whose names nobody wrote
    -- the universe a member ends in, read off its *pre*-type rather than off
    -- what the writer wrote.  Erasure leaves the resulting sort alone, and the
    -- pre-types are closed, where a member's own type names its siblings and
    -- not one of them is in the environment yet -- looking at that here is how
    -- the reason this block was turned down gets replaced by an unknown constant
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
them.

`X._wf`'s body was built against a recursor taking one.  A lowered pre-block's
`mutualRec` takes one per component -- and `Block.wfMotiveLevel` already brought
every motive `X._wf` supplies to a single sort, so they are all that universe and
the one already there is it.
-/
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

A data member of an induction-inductive block is a `def` onto a subtype, and its
constructors are `def`s too, so nothing hands them the `inj`/`injEq` pair that a
real inductive's constructors get.  Without those `simp` knows nothing whatever
about a constructor equation -- not even that `Ctx.snoc Γ A = Ctx.snoc Δ B` says
`Γ = Δ` -- and the encoding shows through the first time anyone asks.

The statements are mainline's own, built by `mkInjectiveTheoremTypeCore?` off a
`ConstructorVal` assembled from the `def`, so the rules about which fields get
compared are mainline's too: a field the resulting type pins is shared between
the two sides rather than compared, a proof field is left out, and a field whose
type moved with an earlier one is compared with `HEq`.

Only the proofs are ours, and they are the same few moves every time.  Forwards,
the equation is pushed through `Subtype.val`, where reduction takes the two
constructors down to the pre-world's own and `injection` splits them; each
equation that yields is a field's outright or a `Subtype.ext` away from one, and
substituting them in turn is what makes the later ones homogeneous.  Backwards,
the components are substituted and the two sides are the same term.
-/

/-- The conjuncts of a right-associated `And`, or the whole of `e` if it is not one. -/
private partial def conjuncts (e : Expr) : Array Expr :=
  if e.isAppOfArity ``And 2 then #[e.appFn!.appArg!] ++ conjuncts e.appArg!
  else #[e]

/--
How many equations `injection` yields at `pre`, an application of a pre-world
constructor: one per field, less the proofs, which proof irrelevance settles
without an equation of their own.
-/
private def preEqCount (pre : Expr) : MetaM Nat := do
  let some n := pre.getAppFn.constName? | return 0
  let cv ← getConstInfoCtor n
  forallBoundedTelescope cv.type cv.numParams fun _ rest =>
    forallTelescope rest fun fs _ => do
      let mut k := 0
      for f in fs do
        unless ← isProp (← inferType f) do k := k + 1
      return k

/--
Elaborate `by seq` at `goal`, with whatever is in scope in scope, and raise
rather than report if it does not go through.

A tactic block that fails ordinarily says so by logging and standing in `sorry`
for what it could not prove, which is right for a script the writer wrote and
wrong for one we are trying on their behalf: what should come of that is no
theorem and a trace, not a proof of `False` waiting to be found and an error
about a script they never saw.  So the log is set aside for the attempt and put
back after it, and anything left in it counts as a failure.
-/
private def proveBy (goal : Expr) (seq : TSyntax ``Lean.Parser.Tactic.tacticSeq) :
    TermElabM Expr := do
  let log ← Core.getMessageLog
  Core.setMessageLog {}
  try
    let e ← Term.withoutErrToSorry do
      let e ← Term.elabTerm (← `(by $seq)) (some goal)
      Term.synthesizeSyntheticMVarsNoPostponing
      instantiateMVars e
    if (← Core.getMessageLog).hasErrors || e.hasSorry || e.hasExprMVar then
      throwError "the script left the goal unproved"
    return e
  finally
    Core.setMessageLog log

/--
`X.c.inj` and `X.c.injEq` for one constructor of a data member.

Nothing is added for a constructor with no two applications to tell apart --
one all of whose fields the resulting type pins, or whose only fields are
proofs -- which is where mainline's statement builder answers `none` too.

`ofInjs` are the `X.ofOrig_inj` the bridge managed to prove, and they are what a
field at a denested copy needs: what `injection` leaves there is an equation
between the two sides' images in the copy.  Which copy is not worked out --
there are only ever a few, and the script tries each in turn.
-/
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
  -- second copy of every field that is not shared.  `injEq` ends there, while
  -- `inj` goes on to take the equation itself, which the forward proof wants
  -- to introduce under a name of its own rather than off a telescope
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
    unless sub.isAppOfArity ``Subtype 2 do
      throwError "`{c.name}` does not build a subtype, so `injection` has nothing to split"
    let u := sub.getAppFn.constLevels!.head!
    let pre ← whnf (mkApp3 (mkConst ``Subtype.val [u]) sub.appFn!.appArg! sub.appArg! lhs)
    let nEq ← preEqCount pre
    if nEq == 0 then throwError "`{c.name}` reduces to no pre-world constructor"
    let qs : TSyntaxArray [`ident, ``Lean.Parser.Term.hole] :=
      (Array.range nEq).map fun k => ⟨(qName k).raw⟩
    -- an equation about a field of the subtype has to be lifted before it can
    -- be substituted, one about a field at a denested copy has to be read back
    -- through that copy, and one about a field a shared one's type mentions is
    -- heterogeneous until the substitutions before it have run.  A shared
    -- field's own equation is of a term with itself and there is nothing to do
    let mut rest : Array (TSyntax `tactic) := #[]
    for k in *...nEq do
      let q := qName k
      let mut lifted : Array Term := #[]
      for e in #[← `(term| $q:ident), ← `(term| eq_of_heq $q)] do
        let ext ← `(term| Subtype.ext $e)
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
      ← `(tactic| have $hV:ident := congrArg Subtype.val $hH),
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
will not find that out by itself.  What makes it true is a `noConfusion` in the
pre-world, and the member is a `def`, so there is nothing under the name the
writer would reach for; core's own `reduceCtorEq`, which asks whether either
side is a constructor application, never fires either.

A lemma per pair of constructors would say it, but there are quadratically many
pairs and every one of them would be a declaration nobody wrote.  So it is one
simproc for the whole library instead.  It pushes the equation through
`Subtype.val`, where reduction takes the two sides down to two different
pre-world constructors, and hands what comes back to `noConfusion` -- so the
pre-world name occurs in the proof term and in nothing that is stated.
-/

/--
`(X.c₁ .. = X.c₂ ..) = False`, for two different constructors of a data member
of an induction-inductive block.

A simproc is offered every equation in the file, so the shape is recognised by
name first: two constants that differ, whose shared prefix `X` has a pre-world
`X._pre` carrying a `noConfusion`.  That is two lookups, and it turns away an
equation between unrelated functions before anything is elaborated.

What survives is then built and checked rather than trusted.  Two names can
differ and still reduce to one constructor -- `noConfusion` answers a *weaker*
question there, and its answer is not `False` -- so the term's type is read back
before the rewrite is offered, and anything else is quietly left alone.
-/
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
    unless sub.isAppOfArity ``Subtype 2 do return .continue
    let u := sub.getAppFn.constLevels!.head!
    let val := mkApp2 (mkConst ``Subtype.val [u]) sub.appFn!.appArg! sub.appArg!
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
the constructor built.

Nothing here is in the erased world.  A peeled member is an inductive over the
types the writer wrote, its fields are at those types, and the hypotheses are
the ones any recursor over the block would offer -- which is why this can be
said at all for a member whose erased recursor could not be.
-/
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
recursion over the whole block offers.

The block's minor asks for a hypothesis at every field that is at a member of
the block, and the kernel's recursion has only the ones at the members it
`covered` to give.  Every other one is a recursion in its own right, and all of
them are within reach: the widened recursor of the member a field is at takes
exactly the motives and minors this one was handed, so it can simply be called.
That is the recursion Lean's own grand recursor would have run there.

`selfCall?` is for the companion described in `addPeeledRecImpl`, which takes
itself apart with a `casesOn` and so is handed no hypothesis at all: given the
recursion's own name, a field at the member itself becomes a call to it, and
what comes back is a minor over the constructor's fields alone.
-/
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
stayed.

A peeled member is an inductive in its own right, with a recursor of its own,
and nothing that stayed can reach it -- that is what made the peel legal in the
first place.  So the block's own recursion has no use for its motive.  But what
Lean gives a `mutual` block is one motive per member and one minor per
constructor whether the recursion needs them or not: a block whose members turn
out to be independent still comes out in the shape it was written in.  A reader
of `Ctx.rec` should not be able to tell that `Tm` was declared apart from it, so
the motives and minors come back, in the order the block put them, and the
recursor simply does not look at them.  Sound for the same reason the peel was:
what it discards, nothing it returns could have depended on.

This runs for the members that left as well as for the ones that stayed.  What
the kernel wrote for a peeled member is a recursion over that member alone, and
a reader of `Tm.rec` is owed the same three motives a reader of `Ctx.rec` is.

`core` is the recursion being restated, `coreAt` the places in the block its
motives stand for -- in its own order, which is the block's -- and `self` the
place of the member it concludes at.  `pub` is the name the writer reads.
Everything is stated over the block as the writer reads it, which is the only
world the peeled types exist in, so this runs once they are declared.
-/
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
    -- a sort.  A minor's ends in a motive and an index's in neither, so the run
    -- of them stops where the minors start
    let mut nMot := 0
    for a in args.extract b.numParams args.size do
      if ← forallTelescopeReducing (← inferType a) fun _ c => pure c.isSort then
        nMot := nMot + 1
      else break
    unless nMot == coreAt.size do
      throwError "`{core}` has {nMot} motives where the recursion is over {coreAt.size}"
    let oldMot := args.extract b.numParams (b.numParams + nMot)
    -- the universe the recursion returns in is the core's own.  It is not always
    -- a name this side of the block chose: what a peeled member brings is the
    -- recursor the kernel wrote for it
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
      -- one minor per constructor, in the order the block was written.  A minor
      -- the core states is restated at the new motives, and every other one is
      -- built here -- including the peeled member's own, whose core version is
      -- short of the hypotheses at the members it does not recurse over
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
          -- writer reads.  The two being definitionally equal is exactly what
          -- lets the one below be handed to the one above
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
              -- and a companion that can actually run.  What was just published
              -- is a recursor application, and the code generator compiles none
              -- of those, so the same function is written a second time out of a
              -- `casesOn` -- which it does compile -- and a recursive call, which
              -- an `unsafe` definition may make freely.  Nothing is trusted: the
              -- checked definition is the one the kernel has and every proof
              -- reads, and a companion that does not go through leaves it
              -- `noncomputable`, which is what it would have been anyway
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

/--
Emit the whole encoding for a prepared block.

Everything here telescopes over types that mention the block's members, so the
order matters twice over: the pre-world declarations of steps 1--3 come out of
the `Plan` already built (they could only be built while the scratch axioms were
in scope), and from step 4 on each member is a real constant by the time a later
step looks through its type.
-/
def emit (p : Plan) : TermElabM Unit := do
  let docCtx := (← getLCtx, ← getLocalInstances)
  let dIdxs := p.block.dataIdxs
  let copyNames := p.copies.map (·.1)
  -- a `Prop` member whose arity runs over a copy is emitted under a hidden name:
  -- `Ok : List Ctx → Prop` is not a statement the block can make until `ofOrig`
  -- exists to send a `List Ctx` to the copy the raw member is really over.  The
  -- bridge at the end gives the plain name the arity that was written, and if it
  -- cannot, the plain name is an alias
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
  -- type that mentions a constructor the bridge is going to rename has to
  -- mention the hidden name instead.  It happens when a proposition's index pins
  -- a data constructor -- `Q.mk (x : WFTree R) : Q (.mk x)` -- and the pinned
  -- constructor is one with a copy-typed field, and again when a constructor
  -- builds an index the erasure deletes out of a copy-typed field of its own.
  -- The block carries the renaming so that `Block.withAlt`, which is where the
  -- second of those is read, does not have to be handed it
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

  -- 2. the `Prop` members' pre-types
  unless p.prePropInds.isEmpty do
    addInd b.us b.numParams p.prePropInds

  -- 3. the well-formedness predicates
  for (name, type, value) in p.wfDecls do
    addDef name b.us type (widenPreRecLevels p preRecUnivs value) (compile := false)

  -- 4. the data members themselves, each after the ones it is indexed by: `Ty Γ`
  -- is a subtype whose predicate is applied to `Γ.val`, and that names `Ctx`
  let dOrder ← dataOrder b
  for i in dOrder do
    let m := b.members[i]!
    let value ← forallTelescope m.type fun idxs _ =>
      return ← mkLambdaFVars idxs (b.subtype i (← b.valArgs i idxs))
    addDef m.name b.us m.type value (compile := false)

  -- 5. the `Prop` members, at the subtypes
  for j in b.propIdxs do
    let m := b.members[j]!
    let value ← forallTelescope m.type fun idxs _ => do
      mkLambdaFVars idxs (mkAppN (b.cst (preName m.name)) (← b.preImages idxs))
    addDef (rawMemberName m.name) b.us m.type value (compile := false)

  -- 6. the data constructors, each after the ones its own type names
  for (i, c) in ← ctorOrder b dOrder do
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
        proofs := proofs.push (← b.propImage xs[k]! (← inferType xs[k]!))
      for k in *...xs.size do
        if c.kinds[k]! == .erased then proofs := proofs.push xs[k]!
      for (_, eq) in eqs do
        proofs := proofs.push (← mkEqRefl eq.appFn!.appArg!)
      let kept := (keptPositions c.kinds).map (imgs[·]!)
      mkLambdaFVars xs <| b.sMk i vargs
        (mkAppN (b.cst (b.preOf c.name)) kept) (introConj conjs proofs 0)
    addDef (rawCtorName c.name) b.us cty value

  -- 7. the `Prop` constructors
  for j in b.propIdxs do
    for c in b.members[j]!.ctors do
      let cty := toRaw c.type
      let value ← forallTelescope cty fun xs _ => do
        mkLambdaFVars xs (mkAppN (b.cst (b.preOf c.name)) (← b.preImages xs))
      addDecl (.thmDecl
        { name := rawCtorName c.name, levelParams := b.us, type := cty, value })

  -- 8. the recursors, one mutual group by structural recursion on the pre-types
  -- the motive's universe, under a name the writer cannot have taken
  let lp := (freshLevelNames b.us 1)[0]!
  let lvl := Level.param lp
  let recAuxName (i : Nat) : Name := b.members[i]!.name ++ `recAux
  -- a member of an induction-inductive block is a `def`, so Lean generates no
  -- `X.rec` for it and the name is free -- which is the one users reach for.
  -- It is still checked, in case a member is named under something that has one
  let env ← getEnv
  let pubRecName (i : Nat) : Name :=
    let n := b.members[i]!.name ++ `rec
    if (env.find? n).isNone then n else b.members[i]!.name ++ `recursor
  -- when members were peeled off, everything below states the recursion over
  -- what is left under a name of its own, and the writer's name is given the
  -- shape the whole block would have had.  See `widenWithPeeled`; a peeled
  -- proposition is left out of that, since a `Prop` motive in a recursor over
  -- the whole block is bundled with the data recursion's value at the index it
  -- is stated over, and a member that left has no such value to offer
  let peeledAllData := p.peeled.all fun t =>
    match t.type.getForallBody with
    | .sort u => u.normalize != Level.zero
    | _ => false
  let widen := !p.peeled.isEmpty && b.propIdxs.isEmpty && peeledAllData
  let recName (i : Nat) : Name :=
    if widen then Name.mkStr b.members[i]!.name "_core_rec" else pubRecName i
  -- a member the writer declared, in a block with copies in it, gets its
  -- recursor twice over: the kernel-facing one, whose motives are over the
  -- copies, under a hidden name, and `X.rec` stated over the originals.  A copy
  -- is not a name anyone reaches for, so its recursor is only the raw one
  let rawRecName (i : Nat) : Name :=
    if p.copies.isEmpty || copyNames.contains b.members[i]!.name then recName i
    else Name.mkStr b.members[i]!.name "_nested_rec"
  -- an induction-inductive block wants one recursor over all of its members at
  -- once, so that a `Prop` motive can mention the value the recursion produced
  -- at the data member it is indexed by.  It does not always exist, and the
  -- block falls back to the split recursors of steps 8 and 9 when it does not.
  -- With copies in the block the bridge of step 10 is built out of the split
  -- ones, so both families are emitted and only the grand one is restated over
  -- the originals; the names have to be kept apart for that
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
      -- a deleted index built out of a constructor.  So both are tried, and
      -- only the second one's reason is worth a trace
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
  let mnames := motiveNames dIdxs.size
  -- the parameters are shared by every motive, minor and recursive call, so the
  -- whole group is built under one telescope of them
  let results ←
   if grandOnly then pure (#[] : Array SplitRec) else
    forallBoundedTelescope b.members[dIdxs[0]!]!.type b.numParams fun ps _ => do
    let motiveDecls : Array (Name × (Array Expr → TermElabM Expr)) := dIdxs.mapIdx fun q i =>
      (mnames[q]!, fun _ => do
        forallTelescope (← instantiateForall b.members[i]!.type ps) fun idxs _ =>
          withLocalDeclD `t (mkAppN (b.memberCst i) (ps ++ idxs)) fun t =>
            mkForallFVars (idxs ++ #[t]) (mkSort lvl))
    withImplicits motiveDecls fun motives => do
      -- one minor per constructor of every data member, in block order
      let mut minorDecls : Array (Name × (Array Expr → TermElabM Expr)) := #[]
      for i in dIdxs do
        for c in b.members[i]!.ctors do
          let kinds := b.fieldKinds c.kinds
          minorDecls := minorDecls.push (Name.mkSimple c.name.getString!, fun _ => do
            forallTelescope (← b.ctorType c ps) fun xs concl => do
              let ihDecls : Array (Name × (Array Expr → TermElabM Expr)) :=
                (ihPositions kinds).map fun k =>
                  (`ih, fun _ => do
                    let r? ← b.withRecTarget? (← inferType xs[k]!) fun ys m args =>
                      mkForallFVars ys
                        (mkAppN motives[dpos[m]!]! (b.idxArgs args ++ #[mkAppN xs[k]! ys]))
                    match r? with
                    | some e => pure e
                    | none => throwError "Not a recursive field of `{c.name}`")
              withLocalDeclsD ihDecls fun ihs =>
                mkForallFVars (xs ++ ihs)
                  (mkAppN motives[dpos[i]!]!
                    (b.idxArgs concl.getAppArgs ++
                      #[mkAppN (b.cst (rawCtorName c.name)) (ps ++ xs)])))
      withLocalDeclsD minorDecls fun minors => do
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
                -- is what a recursive call under it will be handed
                let dDecls : Array (Name × (Array Expr → MetaM Expr)) :=
                  dels.map fun d => (`ih, fun _ => ihTypeAt d)
                withLocalDeclsD dDecls fun dIhs => do
                  -- everything here is built over the fields as the
                  -- constructor bound them and moved to the alternative's
                  -- own binders at the end, because an induction
                  -- hypothesis is found by the shape of the index term
                  let mut ihAt : Array (FVarId × Expr) :=
                    dels.mapIdx fun q d => (d.fvarId!, dIhs[q]!)
                  let mut ihs : Array Expr := #[]
                  for k in ihPositions kinds do
                    -- a deleted field is not a field of the pre-term, so
                    -- there is nothing here to recurse at.  It is one of
                    -- the indices instead, and the hypothesis the minor
                    -- wants about it is the one the recursion was handed
                    -- when it was called, already in scope and already
                    -- at this very term
                    if kinds[k]!.isDeleted then
                      let some q := dels.findIdx? (· == xs[k]!)
                        | throwError "The deleted field `{xs[k]!}` of `{c.name}` is \
                            not one of the alternative's indices"
                      ihs := ihs.push dIhs[q]!
                      continue
                    let some q := recPos.findIdx? (· == k)
                      | throwError "Not a recursive field of `{c.name}`"
                    let y := (imgs[k]!).get!
                    let pr := projConj conjs wc q
                    let ih? ← b.withRecTarget? (← inferType xs[k]!) fun ys mm args => do
                      let dihs ← (b.dropArgs mm args).mapM
                        (ihOfTerm b dCtors rawCtorName FieldKind.hasIh
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
                  mkLambdaFVars (keptImages imgs ++ dels ++ dIhs ++ #[wc])
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
                let dihs ← (b.dropIdxs i idxs).mapM
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

  -- 9. `X.rec` for the `Prop` members the writer declared, out of the pre-block's
  -- own recursor.  A copy is not a name anyone reaches for, and the type it
  -- copies has a real recursor of Lean's own already, so a copy gets none of its
  -- own -- but a member whose recursion runs into one is recursing over the
  -- container, so the copy joins the group and its motive is the container's.
  -- The recursor that comes out here names it, and step 10 puts the original
  -- back in its place.
  --
  -- When the grand recursors took the plain names, only the members they left
  -- out are still owed one; `emitGrandRecs` leaves out exactly the free-standing
  -- ones, and has already made sure that none of them recurses into a member it
  -- did cover, so the closure below cannot cross back
  -- a group of `Prop` members has to be closed under recursion into another of
  -- them: the recursion is one recursion, and a member left out of it has only
  -- the trivial motive, which is nothing to state an induction hypothesis with
  let closeUp (seed : Array Nat) : Array Nat := Id.run do
    let mut keep := seed
    let mut grew := true
    while grew do
      grew := false
      for j in keep do
        for cc in b.members[j]!.ctors do
          for k in b.fieldKinds cc.kinds do
            if let .recur m := k then
              if b.members[m]!.isProp && !keep.contains m then
                keep := keep.push m; grew := true
    return keep
  let propKeep : Array Nat := closeUp <| b.propIdxs.filter fun j =>
    !copyNames.contains b.members[j]!.name && (!grandOnly || grandFree.contains j)
  -- not every `Prop` member has a derivable recursor: a constructor with a data
  -- field the conclusion's indices do not reach cannot have that field put back
  -- at its subtype.  The kept members share one erased recursion, so one such
  -- constructor costs the whole group its recursor -- but the group does not
  -- have to be all of them.  The data members are unaffected and the `Prop`
  -- members keep their constructors either way
  let buildProps (keep : Array Nat) : TermElabM (Option BridgeCtx.PropRecs) := do
    let some s ← BridgeCtx.propRecs? b lp keep | return none
    let ok ← attempted `Mumi.indind "no recursor for the `Prop` members" <|
      forallBoundedTelescope b.members[0]!.type b.numParams fun ps _ =>
        BridgeCtx.addPropRecs { b, ps, copies := #[] } s rawRecName
    return if ok then some s else none
  let propRecs? ← match ← buildProps propKeep with
    | some s => pure (some s)
    | none => do
      -- whose fault it was, asked one member at a time and with the environment
      -- put back after each, so that asking costs nothing.  What fails is a
      -- constructor of a kept member and nothing else, so a member that stands
      -- on its own stands in any group it is closed in, and the ones that stand
      -- can simply be unioned back together and built once
      let mut ok : Array Nat := #[]
      for j in propKeep do
        if ok.contains j then continue
        let grp := closeUp #[j]
        let env ← getEnv
        let stands := (← buildProps grp).isSome
        setEnv env
        if stands then ok := ok ++ grp.filter (!ok.contains ·)
      if ok.isEmpty || ok.size == propKeep.size then pure none
      else buildProps ok
  let propBuilt := propRecs?.isSome

  -- 10. the bridge back to the originals
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
      let c : BridgeCtx := { b, ps, copies }
      -- the round trip is wanted exactly where a constructor of the writer's own
      -- has a copy-typed field, which is where the recursor has to transport
      let needed : Array Nat := Id.run do
        let mut out : Array Nat := #[]
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
        -- restated from *that* one and not from its split recursor, for the same
        -- reason it was covered: read off the grand one its motive takes the
        -- value the data recursion returned, and read off the split one it does
        -- not.  So the two families are restated by one loop, and the fallbacks
        -- differ only in which split recursor is the one to fall back to
        let mut grandDone : Array Nat := #[]
        for i in dIdxs ++ b.propIdxs do
          if (c.copyAt? i).isSome then continue
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
            c.addNiceRec i lp rawRecName (recName i) rawCtorName
        -- and the same for the `Prop` members, whose recursors name a copy
        -- exactly when their recursion runs into one.  Each is a leaf: nothing
        -- else is stated in terms of it, so one that will not go across costs
        -- only its own plain name and the block keeps everything else
        if propBuilt then
          if let some s := propRecs? then
            for j in s.kIdxs do
              if (c.copyAt? j).isSome || grandDone.contains j then continue
              discard <| attempted `Mumi.indind
                s!"`{recName j}` does not restate over the originals" <|
                c.addNicePropRec s j rawRecName (recName j)
    unless built do
      -- a `Prop` recursor that never mentioned a copy is already the one that was
      -- wanted, and only owes the plain name; one that does mention a copy has no
      -- statement over the originals to fall back on, and stays unnamed
      if propBuilt then
        for j in (propRecs?.map (·.kIdxs)).getD #[] do
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

  -- 11. the members that left the block rather than being erased with it, as the
  -- ordinary inductive types they already were.  After the bridge, because what
  -- they are stated over is the block the writer reads and step 10 is where that
  -- becomes something the environment holds.  They come out of `addInd` with
  -- everything an inductive gets -- a recursor, `casesOn`, `noConfusion`,
  -- `brecOn`, and so `match` and the equation compiler -- which is the whole
  -- reason for peeling them.  Their motives and minors then go back into the
  -- recursors of the members that stayed, so that a block written as a `mutual`
  -- still reads as one
  unless p.peeled.isEmpty do
    if !widen then
      addInd b.us b.numParams p.peeled
    else
      -- the inductive is declared one name over and the writer's name is given
      -- to a definition that unfolds to it, because the kernel writes `X.rec`
      -- for whatever it is handed as an inductive `X` and `X.rec` is wanted for
      -- the recursion over the whole block.  Everything the match machinery does
      -- begins by reducing a type to its head, so the definition is no obstacle
      -- to it; and the constructors keep the names that were written, since
      -- nothing obliges a constructor to sit inside its own type's namespace.  A
      -- `match`, the goals a `cases` leaves and the `injEq`s all read as the
      -- block does, and only `#print X` gives away where the type really lives
      -- and one at a time where they can be, since only a member that is
      -- genuinely mutual with another has to share a declaration with it.  What
      -- that buys is a kernel recursor at one motive, which is the only shape
      -- the compiled companion in `widenWithPeeled` knows how to write; and it
      -- keeps a peeled member's name, rather than the inductive behind it,
      -- in the fields of every other one that mentions it
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
          -- constructor, since an inductive's own occurrences in its constructors
          -- are the one thing the kernel will not let a definition stand in for.
          -- So `.var` in an argument of `Tm.lam` looks for `Tm._ind.var`, and it
          -- is pointed at the constructor that is really there
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

  -- 12. one recursor per member with the other members' motives discharged,
  -- which is the shape `induction` can drive, and the same one without its
  -- hypotheses, which is the shape `cases` can drive.  Both are asked for
  -- `evenIfWeaker`: a member here is a `def`, so a tactic that finds no
  -- eliminator of its own does not stop but unfolds it, and what it offers a
  -- split on is `Subtype.mk`.  A principle that has lost a sibling's
  -- hypotheses beats one stated in the encoding, and the recursion over the
  -- whole block is still there under `using`.  A failure is traced and dropped
  for i in *...b.size do
    let m := b.members[i]!
    if copyNames.contains m.name then continue
    let solo (s : Name) := m.name ++ s.appendAfter (if m.isProp then "P" else "D")
    discard <| attempt? `Mumi.indind m!"no one-motive recursor for `{m.name}`" <|
      addSoloElim b.numParams #[lp] m.isProp (pubRecName i) (solo `rec) (forCases := false)
        (evenIfWeaker := true)
    discard <| attempt? `Mumi.indind m!"no cases eliminator for `{m.name}`" <|
      addSoloElim b.numParams #[lp] m.isProp (pubRecName i) (solo `cases) (forCases := true)
  -- a member that left the block has a real recursion of its own already, but it
  -- is the kernel's, over `Tm._ind`, and every goal `induction` leaves says so.
  -- The same one cut out of the block's is stated in the writer's names, and it
  -- is no weaker: discharging the other motives only drops the hypotheses at
  -- fields the kernel's recursor never offered one at either
  if widen then
    for t in p.peeled do
      discard <| attempt? `Mumi.indind m!"no one-motive recursor for `{t.name}`" <|
        addSoloElim b.numParams #[lp] false (t.name ++ `rec) (t.name ++ `recD)
          (forCases := false) (evenIfWeaker := true)
      discard <| attempt? `Mumi.indind m!"no cases eliminator for `{t.name}`" <|
        addSoloElim b.numParams #[lp] false (t.name ++ `rec) (t.name ++ `casesD)
          (forCases := true)

  -- 13. injectivity of the data constructors, which has to come after the
  -- bridge: what is stated is stated about the type the writer wrote, and
  -- until step 10 has run that is not yet what the constructor's own type
  -- says.  A `Prop` member's constructors are proofs and there is nothing to
  -- state.  A failure is traced and dropped
  let ofInjs ← copyNames.filterM fun n => return (← getEnv).contains (n ++ `ofOrig_inj)
  for (i, c) in b.ctorsOf b.dataIdxs do
    if copyNames.contains b.members[i]!.name then continue
    discard <| attempt? `Mumi.indind m!"no injectivity for `{c.name}`" <|
      addInjEqs b (ofInjs.map (· ++ `ofOrig_inj)) i c

/-! ## The entry point -/

/--
Whether some member's arity mentions a sibling -- the syntactic signature of
induction-induction, and the reason the block does not elaborate.  Used only
after header elaboration has already failed, so a block that happens to mention
a *global* of the same name is not affected: that one elaborates.
-/
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

/--
Carry the docstrings the writer put on the block through to what was built.

Lean's own inductive elaborator adds these in a pass of its own, after the
declarations exist, so that a docstring may refer to the type and to its
constructors; nothing on this route does that for us, and a member here is a
`def` and a `Prop` constructor a `theorem`, neither of which the writer named.

Each one is guarded on its name being in the environment.  A block can lose a
constructor on the way through -- a `Prop` member's, when its `Prop` is one the
encoding cannot reach -- and there is nothing to attach a docstring to then.
-/
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
neither what it added to the environment nor what it complained about.

A deriving handler reports by logging as often as by throwing, so "did it work"
is two questions, and undoing it is a matter of putting the whole command state
back rather than just the environment.
-/
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
something did.

The reason has to be read out of the log before the state that holds the log is
put back, which is the whole difficulty: a handler that logged its complaint
instead of throwing it says nothing to a caller that only restores.
-/
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

/--
Instance the member from a constructor that can be applied, if one can.

`Inhabited` is not a class the `Subtype` a data member comes back as can lift,
so the delta route below cannot reach it the way `DecidableEq` and `Repr` are
reached.  It does not need to.  A type is inhabited as soon as one of its
constructors can be applied, and a member's visible constructors are ordinary
functions into it, subtype or not -- so the instance the writer would have had
to write by hand can be written here instead, and it is the same one they would
have written.

A field is filled by whatever `Inhabited` says its own type is, so a
constructor with no fields always serves and one whose fields are inhabited
serves too.  A field of the block is not, since the instance being built is the
one that would have answered, so a member whose every constructor needs a value
of the block declines, and the delta route gets it after all and reports the
failure the way it reports any other.  Declining is the right answer rather
than a wrong one: such a member may genuinely be empty.

Parameters that are types get an `Inhabited` hypothesis apiece, which is what
Lean's own handler does for an ordinary inductive, and what makes the instance
useful at a parameter that is not itself inhabited.
-/
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
        let cinfo ← getConstInfo c
        -- the fields are filled one at a time rather than all at once: a
        -- constructor may state a later field's type in terms of an earlier
        -- field, and then the value chosen for the earlier one is part of it
        let mut ty ← instantiateForall
          (cinfo.type.instantiateLevelParams cinfo.levelParams lvls) ps
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

/--
`deriving` on an induction-inductive block, asked for twice over.

A data member `X` of one of these is not an inductive but a `def`: the subtype
of `X._pre` that `X._wf` cuts out.  A handler that wants to see constructors
therefore has nothing to work with, and the one route left open is the one
Lean calls *delta* deriving -- unfold the member and derive for what is under
it.  `Subtype` carries instances of its own, given ones for the type it cuts
down, so what that needs is the class on the pre-type, where the constructors
really are.

Hence: ask on the pre-types first, quietly, and then delta derive the members.
`DecidableEq` and `Repr` come across that way -- `Repr` showing the pre-term,
constructor names and all, since that is the value it is handed.  A class with
no `Subtype` instance to lift does not come across, and says so -- but by then
the block is already in the environment, which is the part worth keeping, so
the complaint is logged rather than thrown.

`Inhabited` used to be the headline member of that unlucky class.  It no longer
is: a member's visible constructors are ordinary functions into it, so
`inhabitedFromCtor?` writes the instance the writer would have written and the
delta route is never asked.

Whether what is left over failing is an error or a warning is the caller's to
say.  A caller with another route to try wants the error, since a logged one is
how a route declines and lets the next one have the block; the caller of last
resort wants the warning, because by then the choice is between a block with a
class missing and no block at all, and the first is plainly better.

The pre-types are asked for as one array first, since a class that recurses
needs to see a whole mutual inductive at once, and singly after that: the data
members' pre-types are one block and the `Prop` members' another, so a block
with `deriving` on both would not go through together.
-/
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
        -- that the block could keep `X.rec`.  Only the members that came back as
        -- subtypes need the two-step treatment below
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
        -- what is left over goes the delta route.  `Inhabited` is the class
        -- this comes up for, and it is the one a constructor answers directly
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
        let note := m!"A data member of an induction-inductive block is the subtype of its \
          pre-type, so `deriving` reaches it only through an instance `Subtype` already has \
          -- `DecidableEq` and `Repr` do, and a class that does not has to be instanced by hand"
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

/--
Elaborate an induction-inductive block by erasing its proof fields.

The block is denested on the way in.  A block somebody wrote by hand may nest
too -- `Ctx.snoc` taking a `List Ty` is the ordinary way to write a context of
several types -- and `denestRaw` returns a block with no nested occurrence
untouched, so this costs the common case nothing.

Denesting is *best effort* here, unlike on the rescue path, where it is the
whole reason we were called.  This block was written as a `mutual`, so it has
its own reasons to be well or ill formed, and they are the ones worth reporting:
a nesting that cannot be specialised gets the block lowered undenested instead,
which either works or fails with a complaint about the field itself.  `set_option
trace.Mumi.indind true` says when that happened and why.

`requireIndInd` is for the caller that reaches here as a *retry*, after Lean has
already turned the block down.  A block whose members shadow globals of the same
name elaborates its arities against those globals -- Lean reads every arity
before any member is in scope -- so it is never routed here, and Lean rejects it
at the constructors instead, where the members *are* in scope and no longer
agree with the arities.  Reading it again with the members in scope throughout
is what it must have meant, but only if some arity names a sibling at all;
otherwise the block failed for its own reasons and they are the ones to report.
-/
def elabInductionInductive (elems : Array Syntax) (requireIndInd := false)
    (requireDeriving := true) : CommandElabM Unit := do
  let views ← elemViews elems
  if requireIndInd && !viewsAreInductionInductive views then
    throwError "No member's arity names a sibling, so reading this block as an \
      induction-induction would not change what it means"
  -- whether a run peeled anything, so that a failure knows whether there is a
  -- second reading of the block to fall back on
  let peeled ← IO.mkRef false
  -- and, when the peel takes the whole reason for being here with it, the two
  -- halves to hand back to Lean instead.  Set from inside the run, because what
  -- peels is only known once the block's types have been elaborated
  let split ← IO.mkRef (none : Option (Array Nat × Array Nat))
  let go (peel : Bool) : CommandElabM Unit := do
    runTermElabM fun vars => do
      emit (← withRaw views vars fun r => do
        let r ← if peel then markPeeled r else pure r
        peeled.set (!r.peeled.isEmpty)
        -- what stays may no longer be induction-inductive at all: the arity that
        -- named a sibling can have been the peeled member's own.  Then there is
        -- nothing here for the block to gain -- the erasure's recursion over
        -- everything at once needs a proposition indexed by a member to have any
        -- content, and a block with no such member has none -- while Lean's own
        -- reading gives real inductives, with `match` and with its denesting
        unless r.peeled.isEmpty do
          let core := (Array.range views.size).filter (!r.peeled.contains ·)
          unless viewsAreInductionInductive (core.map (views[·]!)) do
            split.set (some (core, r.peeled))
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
  -- suit is read again without it.  What it can cost is a member stated over
  -- something the bridge did not manage to restate -- the peeled type is
  -- written against the block as the writer sees it, and if the writer's own
  -- names did not come back then it is over nothing that exists
  let s ← get
  try
    go true
    if (← get).messages.hasErrors && (← peeled.get) then
      set s
      go false
  catch ex =>
    match ← split.get with
    | some (core, rest) =>
      set s
      -- the core first, since what left the block is stated over it.  Lean's to
      -- accept or not, and if not there is still the erasure to fall back on
      unless ← tentatively (do
          elabCommand (groupCommand elems core)
          elabCommand (groupCommand elems rest)) do
        set s
        go false
    | none =>
      unless ← peeled.get do throw ex
      set s
      go false

/--
Elaborate a *nested* inductive whose denesting is one the kernel refuses.

Denesting must add a member, and then either leave some member's arity
mentioning the block, or have needed a field of a constructor as an index of a
copy.  Those are exactly the two the kernel's own denesting will not do -- it
specialises a nesting type only when the copy's arity comes out free of the
block, and only when the parameters it specialises at are closed -- so nothing
that already works reaches here.

The second is also something `Mumi.Lowering` can take, so the two routes have to
be ordered.  Neither wins outright: this one states the block over the original
nesting types where it can bridge, which lowering never does, but when the
bridge does not go through it leaves the copies visible, and lowering's own
`eq_orig` is then the better answer.  So `requireBridge` lets a caller ask for
the good case first, fall back to lowering, and come back here without it.
-/
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
