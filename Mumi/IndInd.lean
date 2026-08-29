/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Mumi.Lowering
public import Lean.Elab.MutualInductive
import all Lean.Elab.MutualInductive

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

We handle the case where the induction-induction runs **only through proofs**:
no *data* member's arity mentions the block, and every field of a data
constructor whose type mentions a `Prop` member is itself a proof.  Then those
fields can be *erased*, and what is left is an ordinary, non-induction-inductive
block.  For the example above:

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

## What is allowed

* Any number of data members and any number of `Prop` members.  The data
  members become one mutual pre-block, so they must share a universe -- the
  kernel's own rule, which `Mumi.Lowering` lifts for blocks it can see, but the
  pre-block is built here and not routed back through it.
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
* Indices on any member.  A *data* member's indices may not mention the block:
  that is data-on-data induction-induction, which erasure cannot reach.
* Recursive fields may be indexed and infinitary -- `(f : (n : Nat) → Vec n)` --
  provided the binders `ys` mention no member of the block.  `(f : Ctx → Ctx)`
  is out, and not because of positivity: a pre-world `Ctx._pre` cannot be turned
  back into a `Ctx` without its well-formedness proof, so there is nothing to
  hand `f`.

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

## What this does not do

* Section `variable`s.
* An erased field's type may not mention a *data* member as a constant.
  `(h : Fresh x Γ)` is fine -- `Fresh x Γ` unfolds to `Fresh._pre x Γ.val`, so
  erasing it is definitionally invisible -- but `(h : Γ = Γ')` is not: `Γ = Γ'`
  and `Γ.val = Γ'.val` are different propositions, and the encoding would have
  to transport between them.
* A data constructor's field mentioning a `Prop` member must be a proof; that is
  the "narrow" in narrow class.
* The data members' constructors are `def`s, so `match` on them does not work
  and there is no `injEq` or `noConfusion`.  Reason with
  `induction Γ using Ctx.rec with | nil => .. | snoc Γ x h ih => ..`; a
  bare `induction` or `cases` destructs the subtype and leaks `Ctx._pre` into
  the goal.
* `cases` on a `Prop` member works only where the motive does not depend on the
  indices, and otherwise fails ("dependent elimination failed"), because its
  recursor is still `Fresh._pre`'s, stated over the pre-type.  Deriving a real
  `Fresh.rec` from it -- motive `fun x Γ₀ h => ∀ w, motive x ⟨Γ₀, w⟩ h` -- is
  the obvious next step and is not done here.
* Two copies that need each other -- an original nested inside another
  original -- have no order to build the bridge in.  That is reported rather
  than worked around, and the bridge is dropped as a whole, as it is whenever
  any step of it fails: the plain names are then the raw declarations,
  `RecWFTree.mk` reads `RecWFTree.nested_WFTree_1 → RecWFTree` again, and the
  block is exactly what it was before the bridge was attempted.
* A nesting whose parameters mention a field of the constructor it appears in
  (`OkFam BadLocals n` for a local `n`).  `Mumi.Denest` turns such locals into
  extra indices of the copy; a copy that is a member of an induction-inductive
  block would need the same, and does not get it.
* A nesting type that is itself part of a mutual family, and a `mutual` block
  one of whose members is nested this way.  Only a standalone `inductive`
  reaches this path.
-/

public section

namespace Mumi.IndInd

open Lean Lean.Meta Lean.Elab Lean.Elab.Command
open Lean.Elab.MultiuniverseInductive (addDef addInd reroot)

/-! ## Names -/

/-- The erased pre-type of member `n`. -/
def preName (n : Name) : Name := n ++ `_pre

/-- `X._wf : ∀ idxs, X._pre idxs → Prop`, well-formedness on the pre-type. -/
def wfName (n : Name) : Name := n ++ `_wf

/-! ## The block, as we analyse it -/

/-- What becomes of one field of a constructor under erasure. -/
inductive FieldKind where
  /-- Mentions no member of the block; kept as it stands. -/
  | plain
  /-- `∀ ys, M args` for the member at index `mem`; kept, at the pre-type. -/
  | recur (mem : Nat)
  /-- A proof mentioning a `Prop` member; dropped, and remembered by `_wf`. -/
  | erased
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
  deriving Inhabited

def Block.size (b : Block) : Nat := b.members.size

/-- The block's universe parameters as levels. -/
def Block.lvls (b : Block) : List Level := b.us.map Level.param

/-- A constant of the block, at the block's own universe parameters. -/
def Block.cst (b : Block) (n : Name) : Expr := mkConst n b.lvls

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
  b.members.findIdx? (·.name == n)

/-- The index of the member whose *pre-type* is named `n`. -/
def Block.preIdx? (b : Block) (n : Name) : Option Nat :=
  b.members.findIdx? (preName ·.name == n)

/-- The positions of the fields a constructor keeps. -/
def keptPositions (kinds : Array FieldKind) : Array Nat := Id.run do
  let mut out := #[]
  for i in *...kinds.size do
    if kinds[i]! != .erased then out := out.push i
  return out

/-- The positions of a constructor's recursive fields. -/
def recPositions (kinds : Array FieldKind) : Array Nat := Id.run do
  let mut out := #[]
  for i in *...kinds.size do
    if let .recur _ := kinds[i]! then out := out.push i
  return out

/-- `X ↦ X._pre`, and `X.c ↦ X._pre.c` for a constructor of `X`. -/
def Block.preOf (b : Block) (n : Name) : Name := Id.run do
  for m in b.members do
    if n == m.name then return preName m.name
    for c in m.ctors do
      if n == c.name then return reroot m.name (preName m.name) c.name
  return n

/-- The fields a data constructor keeps, or `none` if `n` is not one. -/
def Block.keptOf (b : Block) (n : Name) : Option (Array Nat) := Id.run do
  for m in b.members do
    unless m.isProp do
      for c in m.ctors do
        if n == c.name then return some (keptPositions c.kinds)
  return none

/--
The block's own view of an expression, rewritten to the pre-world: members and
their constructors are re-rooted, and a data constructor's erased arguments are
dropped.
-/
partial def Block.tr (b : Block) (e : Expr) : Expr :=
  match e with
  | .const n us => .const (b.preOf n) us
  | .app .. =>
    e.withApp fun f args =>
      let args := args.map b.tr
      match f with
      | .const n us =>
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
-/
def normLevels (names : Array Name) (lvls : List Level) (e : Expr) : Expr :=
  if lvls.isEmpty then e else
    e.replace fun s =>
      match s with
      | .const n _ => if names.contains n then some (.const n lvls) else none
      | _ => none

/-! ## Members applied to their indices

The data member `X` at indices `args` is the subtype of `X._pre args` cut out by
`X._wf args`.  Everything that crosses between the two worlds goes through these
five, so they are the only place the shape of the encoding is written down. -/

/-- `X._pre args`. -/
def Block.preApp (b : Block) (i : Nat) (args : Array Expr) : Expr :=
  mkAppN (b.cst (preName b.members[i]!.name)) args

/-- `X._wf args`, a predicate on `X._pre args`. -/
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
  forallTelescope ty fun ys concl => do
    let .const n _ := concl.getAppFn | return none
    let some i := b.memberIdx? n | return none
    return some (← k ys i concl.getAppArgs)

/-- As `Block.withRecTarget?`, but reading the pre-world name `M._pre`. -/
def Block.withPreTarget {α} (b : Block) (ty : Expr)
    (k : Array Expr → Nat → Array Expr → MetaM α) : MetaM α :=
  forallTelescope ty fun ys concl => do
    let .const n _ := concl.getAppFn
      | throwError "Not a recursive field type: {ty}"
    let some i := b.preIdx? n
      | throwError "Not a recursive field type: {ty}"
    k ys i concl.getAppArgs

/--
The pre-world image of `x : ty`.  A term of a data member's type loses its
well-formedness proof; everything else, including a term of a `Prop` member's
type, passes through, because `P args` is *defined* as `P._pre args'`.
-/
def Block.preImage (b : Block) (x ty : Expr) : MetaM Expr := do
  let r? ← b.withRecTarget? ty fun ys i args => do
    if b.members[i]!.isProp then return x
    else mkLambdaFVars ys (b.sVal i args (mkAppN x ys))
  return r?.getD x

/-- The well-formedness proof `x` carries: `fun ys => (x ys).property`. -/
def Block.propImage (b : Block) (x ty : Expr) : MetaM Expr := do
  let r? ← b.withRecTarget? ty fun ys i args =>
    mkLambdaFVars ys (b.sProp i args (mkAppN x ys))
  match r? with
  | some e => return e
  | none => throwError "Not a recursive field type: {ty}"

/-- `∀ ys, X._wf args (y ys)`, from a pre-world field `y : ∀ ys, X._pre args`. -/
def Block.wfOfPre (b : Block) (y preTy : Expr) : MetaM Expr :=
  b.withPreTarget preTy fun ys i args =>
    mkForallFVars ys (mkApp (b.wfApp i args) (mkAppN y ys))

/-- `∀ ys, ih ys`, the same conjunct written with a recursor's own hypothesis. -/
def ihConj (ih preTy : Expr) : MetaM Expr :=
  forallTelescope preTy fun ys _ => mkForallFVars ys (mkAppN ih ys)

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
Walk a constructor's fields, rebuilding the telescope in the pre-world: erased
fields are dropped and everything else keeps its place with `Block.tr` applied
to its type and the earlier fields replaced by their pre-world counterparts.

`k` receives the original fields that survive, their pre-world counterparts (in
step), an image per *original* field (`none` for an erased one) and the
pre-world type of every original field, in order.
-/
partial def withPreFieldsAux {α} [Inhabited α] (b : Block) (kinds : Array FieldKind)
    (xs : Array Expr) (i : Nat) (olds news : Array Expr) (imgs : Array (Option Expr))
    (preTys : Array Expr)
    (k : Array Expr → Array Expr → Array (Option Expr) → Array Expr → MetaM α) : MetaM α := do
  if h : i < xs.size then
    let x := xs[i]
    let ty := b.tr ((← inferType x).replaceFVars olds news)
    if kinds[i]! == .erased then
      withPreFieldsAux b kinds xs (i + 1) olds news (imgs.push none) (preTys.push ty) k
    else
      withLocalDeclD (← x.fvarId!.getUserName) ty fun y =>
        withPreFieldsAux b kinds xs (i + 1) (olds.push x) (news.push y)
          (imgs.push (some y)) (preTys.push ty) k
  else
    k olds news imgs preTys

@[inherit_doc withPreFieldsAux]
def withPreFields {α} [Inhabited α] (b : Block) (kinds : Array FieldKind) (xs : Array Expr)
    (k : Array Expr → Array Expr → Array (Option Expr) → Array Expr → MetaM α) : MetaM α :=
  withPreFieldsAux b kinds xs 0 #[] #[] #[] #[] k

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
reported with the error of the last attempt. -/

private def stubAxiom (name : Name) (type : Expr) : TermElabM Unit := do
  -- every universe name in scope, so the stub is well-formed whichever ones its
  -- type turns out to use; `normLevels` puts the references straight afterwards
  let levelParams := (← Term.getLevelNames).reverse
  addDecl (.axiomDecl { name, levelParams, type, isUnsafe := false })

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

/-- `∀ {params} fields, M params args`; the parameters lead here too. -/
private def elabCtorType (views : Array InductiveView) (view : InductiveView) (ctor : CtorView) :
    TermElabM Expr :=
  withRef ctor.ref <| Term.withoutErrToSorry <| withAuto views do
    Term.elabBinders view.binders.getArgs fun params =>
      withAuto views <| Term.elabBinders ctor.binders.getArgs fun fields => do
        let ty ← match ctor.type? with
          | some typeStx => Term.elabType typeStx
          | none => pure (mkAppN (mkConst view.declName []) params)
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
      unless v.derivingClasses.isEmpty do
        throwError "`deriving` is not supported for an induction-inductive block"
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
  /-- The `Prop` members' pre-types, as one mutual inductive. -/
  prePropInds : Array InductiveType
  /-- `X._wf`, per data member: its name, type and `X._pre.rec` body. -/
  wfDecls : Array (Name × Expr × Expr)
  /-- The members denesting added, and the original application each copies. -/
  copies : Array (Name × Expr) := #[]
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
  the block's parameters giving the original application `I ps'` that the copy
  stands for, with the copy's own indices still to come.  Empty for a block
  somebody wrote.
  -/
  copies : Array (Name × Expr) := #[]
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
The checks the arities alone settle.

They are made before any constructor is elaborated, so that a block erasure
cannot reach at all is turned away before its fields are read against members
that will never exist.
-/
def checkDataArities (names : Array Name) (arities : Array Expr) (blockNames : Array Name)
    (isProp : Array Bool) (levels : Array Level) : TermElabM Unit := do
  let dataIdxs := (Array.range names.size).filter (!isProp[·]!)
  if dataIdxs.isEmpty then
    throwError "Every member of this induction-inductive block is a proposition; there is \
      nothing for the erasure to keep"
  -- a data member indexed by the block is data-on-data induction-induction,
  -- which erasure cannot reach; say so before elaborating any constructor
  for i in dataIdxs do
    if arities[i]!.getUsedConstants.any (blockNames.contains ·) then
      throwError "The arity of `{names[i]!}` mentions the block.  Erasure can only \
        reach an induction-induction whose dependency runs through `Prop`, and this one \
        indexes data by data"
  -- the data members become one mutual pre-block, so the kernel's own
  -- same-universe rule applies to them
  for i in dataIdxs do
    unless levels[i]!.normalize == levels[dataIdxs[0]!]!.normalize do
      let fst := toString (← ppExpr (mkSort levels[dataIdxs[0]!]!))
      let snd := toString (← ppExpr (mkSort levels[i]!))
      throwError "The data members `{names[dataIdxs[0]!]!}` and \
        `{names[i]!}` of this induction-inductive block live in different \
        universes, `{fst}` and `{snd}`; the erased pre-block is a single mutual \
        inductive, so they must agree"
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

/--
Everything between the elaborated block and the `Plan`.

The block reaching here need not be one anybody wrote: `denest` adds members of
its own, and they go through exactly the same analysis.
-/
def prepareCore (r : Raw) : TermElabM Plan := do
    let n := r.names.size
    let numParams := r.numParams
    let blockNames := r.blockNames
    let mut arities := r.arities
    let mut ctorTypes := r.ctorTypes
    -- which members are propositions, and at what universe each one lives
    let (isProp, levels) ← memberLevels r.names arities
    checkDataArities r.names arities blockNames isProp levels
    let dataIdxs := (Array.range n).filter (!isProp[·]!)
    let propIdxs := (Array.range n).filter (isProp[·]!)
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
    -- a skeleton is enough for `Block.mentions`, `Block.preOf` and `Block.memberIdx?`
    let skeleton : Block :=
      { numParams, us
        members := (Array.range n).map fun i =>
          { name := r.names[i]!, type := arities[i]!, isProp := isProp[i]!
            level := levels[i]!
            ctors := (Array.range ctorTypes[i]!.size).map fun j =>
              { name := r.ctorNames[i]![j]!, type := ctorTypes[i]![j]!,
                kinds := #[] } } }
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
    -- the pre-world, still against scratch axioms
    for i in b.dataIdxs do
      stubAxiom (preName b.members[i]!.name) b.members[i]!.type
    let mut preDataInds : Array InductiveType := #[]
    for i in b.dataIdxs do
      let m := b.members[i]!
      let mut cs : Array Constructor := #[]
      for c in m.ctors do
        let type ← forallTelescope c.type fun xs concl =>
          withPreFields b c.kinds xs fun olds news _ _ =>
            mkForallFVars news (b.tr (concl.replaceFVars olds news))
        stubAxiom (b.preOf c.name) type
        cs := cs.push { name := b.preOf c.name, type }
      preDataInds := preDataInds.push
        { name := preName m.name, type := m.type, ctors := cs.toList }
    for j in b.propIdxs do
      stubAxiom (preName b.members[j]!.name) (b.tr b.members[j]!.type)
    let mut prePropInds : Array InductiveType := #[]
    for j in b.propIdxs do
      let m := b.members[j]!
      let mut cs : Array Constructor := #[]
      for c in m.ctors do
        let type ← forallTelescope c.type fun xs concl =>
          withPreFields b c.kinds xs fun olds news _ _ =>
            mkForallFVars news (b.tr (concl.replaceFVars olds news))
        cs := cs.push { name := b.preOf c.name, type }
      prePropInds := prePropInds.push
        { name := preName m.name, type := b.tr m.type, ctors := cs.toList }
    -- `X._wf`, one conjunct per recursive field and one per erased proof field.
    -- All the data members share one set of motives and minors, so each `X._wf`
    -- is a different projection of the very same recursion.
    let wfDecls ← forallBoundedTelescope b.members[b.dataIdxs[0]!]!.type numParams
        fun ps _ => do
      let mut motives : Array Expr := #[]
      for i in b.dataIdxs do
        motives := motives.push <| ←
          forallTelescope (← instantiateForall b.members[i]!.type ps) fun idxs _ =>
            withLocalDeclD `t (b.preApp i (ps ++ idxs)) fun t =>
              mkLambdaFVars (idxs ++ #[t]) (mkSort Level.zero)
      let mut wfMinors : Array Expr := #[]
      for i in b.dataIdxs do
        for c in b.members[i]!.ctors do
          let kinds := b.fieldKinds c.kinds
          let minor ← forallTelescope (← instantiateForall c.type ps) fun xs _ =>
            withPreFields b kinds xs fun _ news _ preTys => do
              let recPos := recPositions kinds
              let ihDecls : Array (Name × (Array Expr → MetaM Expr)) := recPos.map fun k =>
                (`ih, fun _ => forallTelescope preTys[k]! fun ys _ =>
                  mkForallFVars ys (mkSort Level.zero))
              withLocalDeclsD ihDecls fun ihs => do
                let mut conjs : Array Expr := #[]
                for q in *...recPos.size do
                  conjs := conjs.push (← ihConj ihs[q]! preTys[recPos[q]!]!)
                for k in *...xs.size do
                  if kinds[k]! == .erased then
                    conjs := conjs.push preTys[k]!
                mkLambdaFVars (news ++ ihs) (foldConj conjs 0)
          wfMinors := wfMinors.push minor
      let mut wfDecls : Array (Name × Expr × Expr) := #[]
      for i in b.dataIdxs do
        let m := b.members[i]!
        let type ← forallTelescope m.type fun idxs _ =>
          withLocalDeclD `t (b.preApp i idxs) fun t =>
            mkForallFVars (idxs ++ #[t]) (mkSort Level.zero)
        let value ← mkLambdaFVars ps <|
          mkAppN (mkConst (preName m.name ++ `rec) (Level.one :: b.lvls))
            (ps ++ motives ++ wfMinors)
        wfDecls := wfDecls.push (wfName m.name, type, value)
      return wfDecls
    return { block := b, preDataInds, prePropInds, wfDecls
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
        let ty ← inferType x
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
      checkIndexArgs b c kinds xs concl.getAppArgs "the resulting type"
      for k in *...xs.size do
        if kinds[k]! != .plain then
          continue
        if (← inferType xs[k]!).hasAnyFVar fun v =>
            (recPositions kinds).any (xs[·]!.fvarId! == v) ||
            (Array.range xs.size).any fun q => kinds[q]! == .erased && xs[q]!.fvarId! == v then
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
def withRaw {α} (views : Array InductiveView) (k : Raw → TermElabM α) : TermElabM α := do
  checkSupported views
  let scopeLevelNames ← Term.getLevelNames
  withoutModifyingEnv <| Term.withLevelNames views[0]!.levelNames do
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
    checkDataArities names arities' blockNames isProp levels
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
        declLevelNames := views[0]!.levelNames }

/-- The block, elaborated and checked, ready for `emit`. -/
def prepare (views : Array InductiveView) : TermElabM Plan :=
  withRaw views prepareCore

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

/-- One nested application, and the member it is about to become. -/
private structure AuxSpec where
  /--
  `@I p₁ … p_k`: the type constructor applied to its parameters and nothing
  else.  Two occurrences with the same parameters share one member, so this is
  the key -- with the block's own constants stripped of their levels, because
  each is a scratch axiom over every universe name in scope and two references
  to it carry two different sets of metavariables.
  -/
  key       : Expr
  name      : Name
  /-- `I`'s parameters, as they were written -- levels and all, unlike `key`. -/
  params    : Array Expr
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

/-- Put every constant of `names` at the empty level list, so that keys compare. -/
private def stripLevels (names : Array Name) (e : Expr) : Expr :=
  e.replace fun s =>
    match s with
    | .const n _ => if names.contains n then some (.const n []) else none
    | _ => none

/--
Unfold definitions at the head of `e` until an inductive type constructor is
exposed, so that a nested occurrence behind an `abbrev` is still seen.  Gives up
after a few steps, and on anything that is not a definition.
-/
private def exposeInduct (e : Expr) : MetaM Expr := do
  let mut e := e
  for _ in *...8 do
    let .const n _ := e.getAppFn | return e
    if let some (.inductInfo _) := (← getEnv).find? n then return e
    let some e' ← unfoldDefinition? e | return e
    e := e'
  return e

/-- The last component of a name, for building a readable auxiliary name. -/
private def shortName (n : Name) : String :=
  match n with
  | .str _ s => s
  | _        => "nested"

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
private partial def internNested (names : Array Name) (root : Name) (e : Expr) :
    DenestM Unit := do
  let some (app, info, lvls, params, idxArgs) ← nestedApp? names e | return
  let key := stripLevels names app
  if (← get).any (·.key == key) then return
  for a in idxArgs do
    if mentionsNames names a then
      throwError m!"Cannot denest{indentExpr e}"
        ++ .note m!"`{info.name}` is applied to a member of the block in an index rather \
          than a parameter, and only parameters can be specialised"
  -- `Mumi.Denest` turns such locals into extra indices of the copy; here they
  -- would have to be indices of a member of an induction-inductive block, and
  -- that is not done
  for p in params do
    if p.hasLooseBVars then
      throwError m!"Cannot denest{indentExpr e}"
        ++ .note m!"`{info.name}` is applied to something that depends on a field of the \
          constructor it appears in"
  if info.all.length > 1 then
    throwError m!"Cannot denest{indentExpr e}"
      ++ .note m!"`{info.name}` is itself part of a mutual block, and only one member of it \
        would be specialised"
  let name := root ++ Name.mkSimple s!"nested_{shortName info.name}_{(← get).size + 1}"
  modify (·.push { key, name, params, indName := info.name, levels := lvls,
                   numParams := info.numParams, ctors := info.ctors.toArray })
  let some ci := (← getEnv).find? info.name | return
  scanExpr names root (← instantiateForall (ci.instantiateTypeLevelParams lvls) params)
  for c in info.ctors do
    let cinfo ← getConstInfoCtor c
    scanExpr names root
      (← instantiateForall (cinfo.type.instantiateLevelParams cinfo.levelParams lvls) params)

/-- Look for nested occurrences everywhere in `e`, indices included. -/
private partial def scanExpr (names : Array Name) (root : Name) (e : Expr) : DenestM Unit := do
  match e with
  | .app .. =>
    internNested names root e
    scanExpr names root e.getAppFn
    for a in e.getAppArgs do scanExpr names root a
  | .forallE _ d b _ | .lam _ d b _ =>
    scanExpr names root d; scanExpr names root b
  | .letE _ t v b _ =>
    scanExpr names root t; scanExpr names root v; scanExpr names root b
  | .mdata _ b | .proj _ _ b => scanExpr names root b
  | _ => pure ()

end

/-- `e` as an application of a specialised type, or of one of its constructors. -/
private def specHit? (names : Array Name) (specs : Array AuxSpec) (e : Expr) :
    MetaM (Option (Name × Array Expr)) := do
  let .const cn lvls := e.getAppFn | return none
  if names.contains cn then return none
  let args := e.getAppArgs
  -- a constructor carries its type's parameters, so its copy is found the same way
  if let some (.ctorInfo ci) := (← getEnv).find? cn then
    if args.size < ci.numParams then return none
    let key := stripLevels names (mkAppN (.const ci.induct lvls) (args.extract 0 ci.numParams))
    let some s := specs.find? (·.key == key) | return none
    return some (reroot s.indName s.name cn, args.extract ci.numParams args.size)
  let some (app, _, _, _, idxArgs) ← nestedApp? names e | return none
  let some s := specs.find? (·.key == stripLevels names app) | return none
  return some (s.name, idxArgs)

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
    let scan : DenestM Unit := do
      for a in r.arities do scanExpr names root (← instantiateForall a ps)
      for cts in r.ctorTypes do
        for ct in cts do scanExpr names root (← instantiateForall ct ps)
    let (_, specs) ← scan.run #[]
    if specs.isEmpty then return r
    -- the copies are referenced exactly as the members are: one metavariable
    -- per universe name in scope, which `normLevels` replaces with the block's
    let auxLvls ← (← Term.getLevelNames).mapM fun _ => mkFreshLevelMVar
    let auxNames := specs.map (·.name)
    let allNames := names ++ auxNames ++
      specs.flatMap fun s => s.ctors.map (reroot s.indName s.name)
    let rw (e : Expr) : MetaM Expr := rwExpr names specs ps auxLvls e
    -- rewrite in place, keeping the original expression where nothing changed
    let rwTop (model : Expr) : MetaM Expr := do
      let body ← instantiateForall model ps
      let body' ← rw body
      if body' == body then return model
      return copyLeadingBinders r.numParams model (← mkForallFVars ps body')
    let arities ← r.arities.mapM fun a => (rwTop a : MetaM Expr)
    let ctorTypes ← r.ctorTypes.mapM (·.mapM fun c => (rwTop c : MetaM Expr))
    -- the copies themselves
    let mut auxArities : Array Expr := #[]
    let mut auxCtorTypes : Array (Array Expr) := #[]
    for s in specs do
      let params := s.params
      let ci ← getConstInfo s.indName
      let resType ← instantiateForall (ci.instantiateTypeLevelParams s.levels) params
      auxArities := auxArities.push
        (copyLeadingBinders r.numParams r.arities[0]! (← mkForallFVars ps (← rw resType)))
      let mut cts : Array Expr := #[]
      for c in s.ctors do
        let cinfo ← getConstInfoCtor c
        let cty ← instantiateForall
          (cinfo.type.instantiateLevelParams cinfo.levelParams s.levels) params
        cts := cts.push (implicitPrefix r.numParams (← mkForallFVars ps (← rw cty)))
      auxCtorTypes := auxCtorTypes.push cts
    -- stub the copies, arities before constructors and each after whatever it
    -- mentions: a copy's arity may name a copy interned after it
    let stubInOrder (todo : Array (Name × Expr)) : TermElabM Unit := do
      let mut todo := todo
      while !todo.isEmpty do
        let env ← getEnv
        let mut next : Array (Name × Expr) := #[]
        let mut progress := false
        for (n, t) in todo do
          if t.getUsedConstants.any fun c => allNames.contains c && (env.find? c).isNone then
            next := next.push (n, t)
          else
            stubAxiom n (← instantiateMVars t)
            progress := true
        unless progress do
          throwError "The copies `{next.map (·.1)}` this nested inductive denests into \
            depend on one another circularly"
        todo := next
    stubInOrder ((Array.range specs.size).map fun k => (auxNames[k]!, auxArities[k]!))
    stubInOrder <| (Array.range specs.size).flatMap fun k =>
      (Array.range auxCtorTypes[k]!.size).map fun j =>
        (reroot specs[k]!.indName specs[k]!.name specs[k]!.ctors[j]!, auxCtorTypes[k]![j]!)
    -- what each copy stands for, kept for the bridge back to it
    let mut copies : Array (Name × Expr) := #[]
    for s in specs do
      copies := copies.push
        (s.name, ← instantiateMVars (← mkLambdaFVars ps (mkAppN (.const s.indName s.levels) s.params)))
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

Nothing here is load-bearing.  Every step is attempted and, if any of it fails
-- a copy whose original is nested in another copy needs the two `ofOrig`s in
one mutual group, which is not done -- the environment is rolled back to before
the bridge, the plain names are defined as the raw declarations instead, and the
block is exactly what it was before.
-/

/-- A member denesting added, and the type it is a copy of. -/
structure Copy where
  /-- Where the copy sits among the block's members. -/
  idx     : Nat
  /-- The copy's name. -/
  name    : Name
  /-- The inductive being copied. -/
  indName : Name
  /-- `I ps'`: that inductive applied to its parameters, under the block's parameters. -/
  app     : Expr
  deriving Inhabited

/-- The original's image in the copy: `X.ofOrig : I ps' idxs → X ps idxs'`. -/
def Copy.ofName (c : Copy) : Name := c.name ++ `ofOrig

/-- The bridge is built under one telescope of the block's parameters. -/
structure BridgeCtx where
  b      : Block
  /-- The block's parameters, as free variables. -/
  ps     : Array Expr
  copies : Array Copy
  deriving Inhabited

namespace BridgeCtx

/-- Which copy's original `e` is an application of, and the indices it carries. -/
def copyOf? (c : BridgeCtx) (e : Expr) : MetaM (Option (Nat × Array Expr)) := do
  let some hd := e.getAppFn.constName? | return none
  let args := e.getAppArgs
  for k in *...c.copies.size do
    let app := c.copies[k]!.app
    let n := app.getAppNumArgs
    if app.getAppFn.constName? == some hd && args.size ≥ n then
      if ← isDefEq (mkAppN e.getAppFn (args.extract 0 n)) app then
        return some (k, args.extract n args.size)
  return none

/--
The copy-world image of `x : ty`, where `ty` is stated in the original world.

A field or index whose type has nothing to do with the block comes back as it
is; one that lands in a copied type is sent through that copy's `ofOrig`.  That
`ofOrig` is indexed by the *original's* indices -- it is what sends them across
-- so they are passed on as they stand.
-/
def ofImage (c : BridgeCtx) (x ty : Expr) : MetaM Expr :=
  forallTelescope ty fun ys concl => do
    let some (k, idxs) ← c.copyOf? concl | return x
    mkLambdaFVars ys <|
      mkAppN (mkConst c.copies[k]!.ofName c.b.lvls) (c.ps ++ idxs ++ #[mkAppN x ys])

/-- The original of a copy, or of a copy's constructor, applied to `args`. -/
def unCopyHead? (c : BridgeCtx) (hd : Name) (args : Array Expr) : MetaM (Option Expr) := do
  if args.size < c.ps.size then return none
  let rest := args.extract c.ps.size args.size
  for cp in c.copies do
    if hd == cp.name then
      return some (mkAppN cp.app rest)
    for orig in (← getConstInfoInduct cp.indName).ctors do
      if hd == reroot cp.indName cp.name orig then
        return some (mkAppN (mkConst orig cp.app.getAppFn.constLevels!)
          (cp.app.getAppArgs ++ rest))
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
The copies, ordered so that each comes after every copy its original mentions.

The originals are looked at *instantiated at their parameters*, which is what
makes a copy of `List` at a copied `Tree` come out after the `Tree`: plain
`List` mentions nothing of the block.  Two copies that need each other -- an
original nested inside another original -- have no such order, and that is
reported rather than worked around.
-/
def order (c : BridgeCtx) : MetaM (Array Nat) := do
  let mut uses : Array (Array Name) := #[]
  for cp in c.copies do
    let lvls := cp.app.getAppFn.constLevels!
    let params := cp.app.getAppArgs
    let info ← getConstInfoInduct cp.indName
    let mut ns := (← instantiateForall (info.instantiateTypeLevelParams lvls) params)
      |>.getUsedConstants
    for cn in info.ctors do
      let ci ← getConstInfoCtor cn
      ns := ns ++ (← instantiateForall
        (ci.type.instantiateLevelParams ci.levelParams lvls) params).getUsedConstants
    uses := uses.push ns
  let mut done : Array Nat := #[]
  let mut todo := Array.range c.copies.size
  while !todo.isEmpty do
    let mut next : Array Nat := #[]
    let mut progress := false
    for k in todo do
      let ready := (Array.range c.copies.size).all fun j =>
        c.copies[j]!.indName == c.copies[k]!.indName || done.contains j ||
          !(uses[k]!.contains c.copies[j]!.indName)
      if ready then
        done := done.push k
        progress := true
      else
        next := next.push k
    unless progress do
      throwError "The types denesting copies are nested in one another"
    todo := next
  return done

/-- `X.ofOrig`'s type: the original at its indices, sent to the copy at theirs. -/
def ofType (c : BridgeCtx) (k : Nat) : MetaM Expr := do
  let cp := c.copies[k]!
  forallTelescope (← inferType cp.app) fun jdxs _ => do
    let mut imgs : Array Expr := #[]
    for y in jdxs do
      imgs := imgs.push (← c.ofImage y (← inferType y))
    withLocalDeclD `x (mkAppN cp.app jdxs) fun x =>
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
  let params := cp.app.getAppArgs
  let lvls := cp.app.getAppFn.constLevels!
  forallTelescope (← inferType cp.app) fun jdxs _ => do
    let mut imgs : Array Expr := #[]
    for y in jdxs do
      imgs := imgs.push (← c.ofImage y (← inferType y))
    let resTy := mkAppN (c.b.cst cp.name) (c.ps ++ imgs)
    withLocalDeclD `x (mkAppN cp.app jdxs) fun x => do
      let motive ← mkLambdaFVars (jdxs ++ #[x]) resTy
      let elim ← getLevel resTy
      let mut alts : Array Expr := #[]
      for cn in info.ctors do
        let ci ← getConstInfoCtor cn
        let cty ← instantiateForall (ci.type.instantiateLevelParams ci.levelParams lvls) params
        alts := alts.push <| ← forallTelescope cty fun xs _ => do
          let mut fimgs : Array Expr := #[]
          for y in xs do
            fimgs := fimgs.push (← c.ofImage y (← inferType y))
          mkLambdaFVars xs <|
            mkAppN (mkConst (reroot cp.indName cp.name cn) c.b.lvls) (c.ps ++ fimgs)
      let body := mkAppN (mkConst (mkCasesOnName cp.indName) (elim :: lvls))
        (params ++ #[motive] ++ jdxs ++ #[x] ++ alts)
      return implicitPrefix (c.ps.size + jdxs.size) (← mkLambdaFVars (c.ps ++ jdxs ++ #[x]) body)

/--
`X.ofOrig` for a `Prop` copy: the original's own recursor.  A theorem cannot
call itself, so a field of the original's type takes the hypothesis the
recursor supplies for it rather than a recursive call.
-/
def ofValueProp (c : BridgeCtx) (k : Nat) : MetaM Expr := do
  let cp := c.copies[k]!
  let info ← getConstInfoInduct cp.indName
  let recInfo ← getConstInfoRec (mkRecName cp.indName)
  unless recInfo.numMotives == 1 do
    throwError "`{cp.indName}` is itself a nested inductive"
  let params := cp.app.getAppArgs
  let lvls := cp.app.getAppFn.constLevels!
  forallTelescope (← inferType cp.app) fun jdxs _ => do
    let mut imgs : Array Expr := #[]
    for y in jdxs do
      imgs := imgs.push (← c.ofImage y (← inferType y))
    let resTy := mkAppN (c.b.cst cp.name) (c.ps ++ imgs)
    withLocalDeclD `x (mkAppN cp.app jdxs) fun x => do
      let motive ← mkLambdaFVars (jdxs ++ #[x]) resTy
      let elim ← getLevel resTy
      let recLvls := if recInfo.levelParams.length == info.levelParams.length then lvls
        else elim :: lvls
      let recTy ← instantiateForall
        (recInfo.type.instantiateLevelParams recInfo.levelParams recLvls) (params ++ #[motive])
      let minors ← forallBoundedTelescope recTy recInfo.numMinors fun ms _ => do
        let mut out : Array Expr := #[]
        for q in *...ms.size do
          let rule := recInfo.rules[q]!
          out := out.push <| ← forallTelescope (← inferType ms[q]!) fun args _ => do
            let fields := args.extract 0 rule.nfields
            let ihs := args.extract rule.nfields args.size
            let mut fimgs : Array Expr := #[]
            let mut nih := 0
            for y in fields do
              let ty ← inferType y
              let selfRec ← forallTelescope ty fun _ concl => do
                match ← c.copyOf? concl with
                | some (k', _) => return k' == k
                | none         => return false
              if selfRec && nih < ihs.size then
                fimgs := fimgs.push ihs[nih]!
                nih := nih + 1
              else
                fimgs := fimgs.push (← c.ofImage y ty)
            mkLambdaFVars args <|
              mkAppN (mkConst (reroot cp.indName cp.name rule.ctor) c.b.lvls) (c.ps ++ fimgs)
        return out
      let body := mkAppN (mkConst recInfo.name recLvls)
        (params ++ #[motive] ++ minors ++ jdxs ++ #[x])
      return implicitPrefix (c.ps.size + jdxs.size) (← mkLambdaFVars (c.ps ++ jdxs ++ #[x]) body)

/-- Add `X.ofOrig` for every copy, each after the ones its own body calls. -/
def addOfOrig (c : BridgeCtx) (docCtx : LocalContext × LocalInstances) : TermElabM Unit := do
  for k in ← c.order do
    let cp := c.copies[k]!
    let type ← instantiateMVars (← c.ofType k)
    if c.b.members[cp.idx]!.isProp then
      let value ← instantiateMVars (← c.ofValueProp k)
      addDecl (.thmDecl { name := cp.ofName, levelParams := c.b.us, type, value })
    else
      let value ← instantiateMVars (← c.ofValueData k)
      let preDef : PreDefinition :=
        { ref := .missing, kind := .def, levelParams := c.b.us, modifiers := {},
          declName := cp.ofName, binders := .missing, type, value,
          termination := TerminationHints.none }
      if value.getUsedConstants.contains cp.ofName then
        Structural.structuralRecursion docCtx #[preDef] #[none]
      else
        addAndCompileNonRec docCtx preDef

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
        let mut imgs : Array Expr := #[]
        for x in xs do
          imgs := imgs.push (← c.ofImage x (← inferType x))
        mkLambdaFVars xs (mkAppN (mkConst raw c.b.lvls) (c.ps ++ imgs))
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

/-- How many of the original's arguments are parameters. -/
def Copy.numOrigParams (c : Copy) : Nat := c.app.getAppNumArgs

/-- The original's constructor that `n`, a constructor of the copy, is a copy of. -/
def Copy.origCtor (c : Copy) (n : Name) : Expr :=
  mkAppN (mkConst (reroot c.name c.indName n) c.app.getAppFn.constLevels!) c.app.getAppArgs

namespace BridgeCtx

/-- Which copy the block's member `i` is, if it is one. -/
def copyAt? (c : BridgeCtx) (i : Nat) : Option Nat :=
  c.copies.findIdx? (·.idx == i)

/-- Where the data member `i` sits among the motives. -/
def dpos (c : BridgeCtx) (i : Nat) : Nat := (c.b.dataIdxs.findIdx? (· == i)).getD 0

/-- The motive arguments of a member's type: a copy's are the *original's*. -/
def niceIdxArgs (c : BridgeCtx) (i : Nat) (args : Array Expr) : Array Expr :=
  match c.copyAt? i with
  | some k => args.extract c.copies[k]!.numOrigParams args.size
  | none   => c.b.idxArgs args

/--
The original-world image of `x : ty`, where `ty` is written in the copy world.

The mirror of `BridgeCtx.ofImage`.  A copy's indices are the original's -- a data
copy has the arity it copies, and a `Prop` copy's `toOrig` is stated at the
copy's own -- so here too the indices are passed on as they stand.
-/
def toImage (c : BridgeCtx) (x ty : Expr) : MetaM Expr :=
  forallTelescope ty fun ys concl => do
    let some hd := concl.getAppFn.constName? | return x
    let some k := c.copies.findIdx? (·.name == hd) | return x
    mkLambdaFVars ys <|
      mkAppN (mkConst c.copies[k]!.toName c.b.lvls)
        (c.ps ++ c.b.idxArgs concl.getAppArgs ++ #[mkAppN x ys])

/-- `X.toOrig`'s type: the copy at its indices, sent to the original at theirs. -/
def toType (c : BridgeCtx) (k : Nat) : MetaM Expr := do
  let cp := c.copies[k]!
  forallTelescope (← instantiateForall c.b.members[cp.idx]!.type c.ps) fun idxs _ => do
    let mut jdxs : Array Expr := #[]
    for y in idxs do
      jdxs := jdxs.push (← c.toImage y (← inferType y))
    withLocalDeclD `x (mkAppN (c.b.cst cp.name) (c.ps ++ idxs)) fun x =>
      return implicitPrefix (c.ps.size + idxs.size) (←
        mkForallFVars (c.ps ++ idxs ++ #[x]) (mkAppN cp.app jdxs))

/--
Build one minor per constructor of every data member, reading the binders off
the raw recursor's own type rather than reconstructing them.

`mk` is handed the member, the constructor, the fields and the induction
hypotheses, and returns the minor's body.
-/
def withRawMinors (c : BridgeCtx) (recCst : Expr) (motives : Array Expr)
    (mk : Nat → CtorSpec → Array Expr → Array Expr → TermElabM Expr) :
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
          forallBoundedTelescope (← inferType ms[q]!) (nf + (recPositions kinds).size)
            fun args _ => do
              mkLambdaFVars args (← mk i cc (args.extract 0 nf) (args.extract nf args.size))
        q := q + 1
    return out

/--
`X.toOrig` for a data copy: one application of the copy's own recursor.

Only the copy being sent across has a motive worth anything; the other members
of the block are eliminated into `PUnit`, which is what makes this a single
recursor application rather than a mutual group.
-/
def toValueData (c : BridgeCtx) (k : Nat) (rawRec : Nat → Name) : TermElabM Expr := do
  let b := c.b
  let cp := c.copies[k]!
  forallTelescope (← instantiateForall b.members[cp.idx]!.type c.ps) fun idxs _ => do
    let mut jdxs : Array Expr := #[]
    for y in idxs do
      jdxs := jdxs.push (← c.toImage y (← inferType y))
    let elim ← getLevel (mkAppN cp.app jdxs)
    withLocalDeclD `x (mkAppN (b.cst cp.name) (c.ps ++ idxs)) fun x => do
      let motives ← b.dataIdxs.mapM fun i => do
        forallTelescope (← instantiateForall b.members[i]!.type c.ps) fun ids _ =>
          withLocalDeclD `t (mkAppN (b.cst b.members[i]!.name) (c.ps ++ ids)) fun t => do
            let body ← if i == cp.idx then do
                let mut js : Array Expr := #[]
                for y in ids do
                  js := js.push (← c.toImage y (← inferType y))
                pure (mkAppN cp.app js)
              else
                pure (mkConst ``PUnit [elim])
            mkLambdaFVars (ids ++ #[t]) body
      let recCst := mkConst (rawRec cp.idx) (elim :: b.lvls)
      let minors ← c.withRawMinors recCst motives fun i cc xs ihs => do
        if i != cp.idx then
          return mkConst ``PUnit.unit [elim]
        let kinds := b.fieldKinds cc.kinds
        let mut vals : Array Expr := #[]
        let mut nih := 0
        for z in *...xs.size do
          match kinds[z]! with
          | .recur m =>
            if m == cp.idx then vals := vals.push ihs[nih]!
            else vals := vals.push (← c.toImage xs[z]! (← inferType xs[z]!))
            nih := nih + 1
          | .plain  => vals := vals.push xs[z]!
          | .erased => vals := vals.push (← c.toImage xs[z]! (← inferType xs[z]!))
        return mkAppN (cp.origCtor cc.name) vals
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
      let ty := (← inferType idxs[i]).replaceFVars (idxs.extract 0 i) (reals.map (·.1))
      let isData ← c.b.withRecTarget? ty fun _ m _ => pure (!c.b.members[m]!.isProp)
      if isData == some true then
        withLocalDeclD `w (← c.b.wfOfPre y (← inferType y)) fun w => do
          let real ← c.b.withPreTarget (← inferType y) fun zs mm args =>
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

/-- The proof among `parts` of the statement `want`. -/
def findPart (parts : Array (Expr × Expr)) (want : Expr) : MetaM Expr := do
  for (ty, pf) in parts do
    if ← isDefEq ty want then return pf
  throwError "No well-formedness proof to hand for{indentExpr want}"

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
  let pIdxs ← recInfo.all.toArray.mapM fun n => do
    let some j := b.propIdxs.find? fun j => preName b.members[j]!.name == n
      | throwError "No `Prop` member of the block behind `{n}`"
    return j
  let motives ← pIdxs.mapM fun j =>
    c.withWfIdxs j fun pres ws reals =>
      withLocalDeclD `h (mkAppN (b.cst (preName b.members[j]!.name)) (c.ps ++ pres)) fun h => do
        let body ← match c.copyAt? j with
          | some kj => do
            let mut js : Array Expr := #[]
            for (r, ty) in reals do
              js := js.push (← c.toImage r ty)
            mkForallFVars ws (mkAppN c.copies[kj]!.app js)
          | none => pure (mkConst ``True)
        mkLambdaFVars (pres ++ #[h]) body
  let recLvls := if recInfo.levelParams.length == b.us.length then b.lvls else Level.zero :: b.lvls
  let recTy ← instantiateForall
    (recInfo.type.instantiateLevelParams recInfo.levelParams recLvls) (c.ps ++ motives)
  let minors ← forallBoundedTelescope recTy recInfo.numMinors fun ms _ => do
    let order : Array (Nat × CtorSpec) := pIdxs.flatMap fun j =>
      b.members[j]!.ctors.map fun cc => (j, cc)
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
          let cpj := c.copies[kj]!
          let xs := args.extract 0 kinds.size
          let ihs := args.extract kinds.size args.size
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
              | .recur m =>
                if !b.members[m]!.isProp then
                  -- a data field, rebuilt at the subtype from the proof in hand
                  let pf ← findPart parts (← b.wfOfPre xs[z]! ty)
                  let (real, realTy) ← b.withPreTarget ty fun zs mm args' => do
                    let v ← mkLambdaFVars zs (b.sMk mm args' (mkAppN xs[z]! zs) (mkAppN pf zs))
                    let t ← mkForallFVars zs (mkAppN (b.cst b.members[mm]!.name) args')
                    return (v, t)
                  vals := vals.push (← c.toImage real realTy)
                else if (c.copyAt? m).isSome then
                  -- the hypothesis for this field, at its own indices' proofs
                  let ih := ihs[nih]!
                  let nzs ← forallTelescope ty fun zs _ => pure zs.size
                  nih := nih + 1
                  vals := vals.push <| ←
                    forallBoundedTelescope (← inferType ih) nzs fun zs rest => do
                      forallTelescope (← whnf rest) fun ws' _ => do
                        let mut fnd : Array Expr := #[]
                        for w' in ws' do
                          fnd := fnd.push (← findPart parts (← inferType w'))
                        mkLambdaFVars zs (mkAppN ih (zs ++ fnd))
                else
                  -- a `Prop` member the writer declared: the proof is the proof
                  nih := nih + 1
                  vals := vals.push xs[z]!
            mkLambdaFVars (args ++ ws) (mkAppN (cpj.origCtor cc.name) vals)
    return out
  let preType ← c.withWfIdxs cp.idx fun pres ws reals =>
    withLocalDeclD `h (mkAppN (b.cst (preName cp.name)) (c.ps ++ pres)) fun h => do
      let mut js : Array Expr := #[]
      for (r, ty) in reals do
        js := js.push (← c.toImage r ty)
      return implicitPrefix c.ps.size (←
        mkForallFVars (c.ps ++ pres ++ #[h] ++ ws) (mkAppN cp.app js))
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
      let mut pres : Array Expr := #[]
      let mut wps : Array Expr := #[]
      for y in idxs do
        let ty ← inferType y
        pres := pres.push (← b.preImage y ty)
        let isData ← b.withRecTarget? ty fun _ m _ => pure (!b.members[m]!.isProp)
        if isData == some true then
          wps := wps.push (← b.propImage y ty)
      return implicitPrefix (c.ps.size + idxs.size) (← mkLambdaFVars (c.ps ++ idxs ++ #[x])
        (mkAppN (mkConst cp.preToName b.lvls) (c.ps ++ pres ++ #[x] ++ wps)))
  addDecl (.thmDecl { name := cp.toName, levelParams := b.us
                      type := ← instantiateMVars (← c.toType k)
                      value := ← instantiateMVars value })

/-- Add `X.toOrig` for every copy, each after the ones its own body calls. -/
def addToOrig (c : BridgeCtx) (rawRec : Nat → Name) : TermElabM Unit := do
  for k in ← c.order do
    let cp := c.copies[k]!
    if c.b.members[cp.idx]!.isProp then
      c.addToOrigProp k
    else
      addDef cp.toName c.b.us (← instantiateMVars (← c.toType k))
        (← instantiateMVars (← c.toValueData k rawRec))

/-- `funext` applied `n` times, to a hypothesis that is pointwise an equation. -/
partial def funExtN (h : Expr) (n : Nat) : MetaM Expr := do
  if n == 0 then return h
  forallBoundedTelescope (← inferType h) (some 1) fun ys _ => do
    let y := ys[0]!
    mkFunExt (← mkLambdaFVars #[y] (← funExtN (mkApp h y) (n - 1)))

/--
`X._pre.c (kept images) = X._pre.c (kept fields)`, one step per field the two
sides differ at.

`pf z` is the equation for field `z`, or `none` when the two sides hold the same
term there -- which is every field but a copy's, and every erased field, since
those are not at this level at all.  The steps are taken one at a time rather
than as a single `congr` so that a constructor whose later fields depend on
earlier ones still goes through: what the steps move is never what a later field
depends on, because a field used as an index has to be one erasure leaves alone.
-/
def valCongr (c : BridgeCtx) (cc : CtorSpec) (xs : Array Expr)
    (pf : Nat → TermElabM (Option Expr)) : TermElabM Expr := do
  let b := c.b
  let kinds := b.fieldKinds cc.kinds
  let head := mkAppN (b.cst (b.preOf cc.name)) c.ps
  let eqSides (p : Expr) : TermElabM (Expr × Expr) := do
    let some (_, l, r) := (← whnf (← instantiateMVars (← inferType p))).eq?
      | throwError "Not an equation:{indentExpr p}"
    return (l, r)
  let mut cur : Array Expr := #[]
  let mut steps : Array (Nat × Expr) := #[]
  for z in keptPositions kinds do
    match ← pf z with
    | some p =>
      steps := steps.push (cur.size, p)
      cur := cur.push (← eqSides p).1
    | none => cur := cur.push (← b.preImage xs[z]! (← inferType xs[z]!))
  let mut acc ← mkEqRefl (mkAppN head cur)
  for (pos, p) in steps do
    let motive ← withLocalDeclD `a (← inferType cur[pos]!) fun a =>
      mkLambdaFVars #[a] (mkAppN head (cur.set! pos a))
    acc ← mkEqTrans acc (← mkCongrArg motive p)
    cur := cur.set! pos (← eqSides p).2
  return acc

/-- `Subtype.ext` at the member `i`, whose type is a subtype by definition. -/
def subtypeExt (c : BridgeCtx) (i : Nat) (args : Array Expr) (a a' h : Expr) : Expr :=
  mkAppN (mkConst ``Subtype.ext [c.b.members[i]!.level])
    #[c.b.preApp i args, c.b.wfApp i args, a, a', h]

/-- Add `X.ofOrig_toOrig` for each copy in `needed`. -/
def addRoundTrips (c : BridgeCtx) (needed : Array Nat) (rawRec : Nat → Name) :
    TermElabM Unit := do
  let b := c.b
  -- `(X.ofOrig (X.toOrig t)).val`, for `t` a term of the copy at `ids`
  let roundLhs (k : Nat) (ids : Array Expr) (t : Expr) : Expr :=
    let cp := c.copies[k]!
    let there := mkAppN (mkConst cp.toName b.lvls) (c.ps ++ ids ++ #[t])
    let back := mkAppN (mkConst cp.ofName b.lvls) (c.ps ++ ids ++ #[there])
    b.sVal cp.idx (c.ps ++ ids) back
  let motives ← b.dataIdxs.mapM fun i => do
    forallTelescope (← instantiateForall b.members[i]!.type c.ps) fun ids _ =>
      withLocalDeclD `t (mkAppN (b.cst b.members[i]!.name) (c.ps ++ ids)) fun t => do
        let body ← match c.copyAt? i with
          | some k => mkEq (roundLhs k ids t) (b.sVal i (c.ps ++ ids) t)
          | none   => pure (mkConst ``True)
        mkLambdaFVars (ids ++ #[t]) body
  for k in needed do
    let cp := c.copies[k]!
    let recCst := mkConst (rawRec cp.idx) (Level.zero :: b.lvls)
    let minors ← c.withRawMinors recCst motives fun i cc xs ihs => do
      if (c.copyAt? i).isNone then
        return mkConst ``True.intro
      let kinds := b.fieldKinds cc.kinds
      let recPos := recPositions kinds
      c.valCongr cc xs fun z => do
        let .recur m := kinds[z]! | return none
        if (c.copyAt? m).isNone then return none
        let nzs ← forallTelescope (← inferType xs[z]!) fun zs _ => pure zs.size
        return some (← funExtN ihs[(recPos.findIdx? (· == z)).getD 0]! nzs)
    let (type, value) ←
      forallTelescope (← instantiateForall b.members[cp.idx]!.type c.ps) fun idxs _ =>
        withLocalDeclD `x (mkAppN (b.cst cp.name) (c.ps ++ idxs)) fun x => do
          let ty := implicitPrefix (c.ps.size + idxs.size) (←
            mkForallFVars (c.ps ++ idxs ++ #[x])
              (← mkEq (roundLhs k idxs x) (b.sVal cp.idx (c.ps ++ idxs) x)))
          let val := implicitPrefix (c.ps.size + idxs.size) (←
            mkLambdaFVars (c.ps ++ idxs ++ #[x])
              (mkAppN recCst (c.ps ++ motives ++ minors ++ idxs ++ #[x])))
          return (ty, val)
    addDecl (.thmDecl { name := cp.roundName, levelParams := b.us
                        type := ← instantiateMVars type
                        value := ← instantiateMVars value })

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
  let shortOf (m : Nat) : String :=
    match c.copyAt? m with
    | some k => c.copies[k]!.indName.getString!
    | none   => b.members[m]!.name.getString!
  let mnames : Array Name := Id.run do
    if dIdxs.size == 1 then return #[`C]
    let mut used : Array String := #[]
    let mut out : Array Name := #[]
    for m in dIdxs do
      let mut s := "C_" ++ shortOf m
      let mut j := 1
      while used.contains s do
        j := j + 1
        s := "C_" ++ shortOf m ++ "_" ++ toString j
      used := used.push s
      out := out.push (Name.mkSimple s)
    return out
  let motiveDecls : Array (Name × (Array Expr → TermElabM Expr)) :=
    dIdxs.mapIdx fun q m => (mnames[q]!, fun _ => do
      match c.copyAt? m with
      | some k =>
        let cp := c.copies[k]!
        forallTelescope (← inferType cp.app) fun jdxs _ =>
          withLocalDeclD `t (mkAppN cp.app jdxs) fun t =>
            mkForallFVars (jdxs ++ #[t]) (mkSort lvl)
      | none =>
        forallTelescope (← instantiateForall b.members[m]!.type c.ps) fun ids _ =>
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
              (recPositions kinds).map fun z => (`ih, fun _ => do
                let .recur mm := kinds[z]! | throwError "Not a recursive field"
                forallTelescope (← inferType ys[z]!) fun zs tgt =>
                  mkForallFVars zs (mkAppN nmotives[c.dpos mm]!
                    (c.niceIdxArgs mm tgt.getAppArgs ++ #[mkAppN ys[z]! zs])))
            withLocalDeclsD ihDecls fun ihs => do
              let ctorApp := match c.copyAt? m with
                | some k => mkAppN (c.copies[k]!.origCtor cc.name) ys
                | none   => mkAppN (b.cst cc.name) (c.ps ++ ys)
              mkForallFVars (ys ++ ihs) (mkAppN nmotives[c.dpos m]!
                (c.niceIdxArgs m concl.getAppArgs ++ #[ctorApp])))
    withLocalDeclsD minorDecls fun nminors => do
      let rmotives ← dIdxs.mapM fun m =>
        match c.copyAt? m with
        | none   => pure nmotives[c.dpos m]!
        | some k => do
          let cp := c.copies[k]!
          forallTelescope (← instantiateForall b.members[m]!.type c.ps) fun ids _ =>
            withLocalDeclD `t (mkAppN (b.cst b.members[m]!.name) (c.ps ++ ids)) fun t => do
              let mut js : Array Expr := #[]
              for y in ids do
                js := js.push (← c.toImage y (← inferType y))
              mkLambdaFVars (ids ++ #[t]) (mkAppN nmotives[c.dpos m]!
                (js ++ #[mkAppN (mkConst cp.toName b.lvls) (c.ps ++ ids ++ #[t])]))
      let recCst := mkConst (rawRec i) (lvl :: b.lvls)
      let rminors ← c.withRawMinors recCst rmotives fun m cc xs ihs => do
        let mut vals : Array Expr := #[]
        for x in xs do
          vals := vals.push (← c.toImage x (← inferType x))
        let minorIdx := Id.run do
          let mut acc := 0
          for m' in dIdxs do
            for c' in b.members[m']!.ctors do
              if c'.name == cc.name then return acc
              acc := acc + 1
          return acc
        let body := mkAppN nminors[minorIdx]! (vals ++ ihs)
        let raw := rawOf cc.name
        if raw == cc.name then return body
        -- the nice constructor is the raw one at `ofOrig` of its fields, so what
        -- the minor produced is about the round trip; the equation removes it
        let kinds := b.fieldKinds cc.kinds
        let h ← c.valCongr cc xs fun z => do
          let .recur mm := kinds[z]! | return none
          let some k' := c.copyAt? mm | return none
          let cp := c.copies[k']!
          let nzs ← forallTelescope (← inferType xs[z]!) fun zs _ => pure zs.size
          let pointwise ← forallTelescope (← inferType xs[z]!) fun zs tgt => do
            let ids := b.idxArgs tgt.getAppArgs
            let elt := mkAppN xs[z]! zs
            -- at the value, which is where `valCongr` puts its steps; the whole
            -- constructor application is lifted back to the subtype afterwards
            mkLambdaFVars zs (mkAppN (mkConst cp.roundName b.lvls) (c.ps ++ ids ++ #[elt]))
          return some (← funExtN pointwise nzs)
        let src := mkAppN (b.cst cc.name) (c.ps ++ vals)
        let tgt := mkAppN (b.cst raw) (c.ps ++ xs)
        let tgtTy ← inferType tgt
        let args := c.ps ++ b.idxArgs tgtTy.getAppArgs
        let motive ← withLocalDeclD `z tgtTy fun z =>
          mkLambdaFVars #[z] (mkAppN rmotives[c.dpos m]! (b.idxArgs tgtTy.getAppArgs ++ #[z]))
        mkEqNDRec motive body (c.subtypeExt m args src tgt h)
      let (type, value) ←
        forallTelescope (← instantiateForall b.members[i]!.type c.ps) fun idxs _ =>
          withLocalDeclD `t (mkAppN (b.cst b.members[i]!.name) (c.ps ++ idxs)) fun t => do
            let ty := implicitPrefix c.ps.size (←
              mkForallFVars (c.ps ++ nmotives ++ nminors ++ idxs ++ #[t])
                (mkAppN nmotives[c.dpos i]! (idxs ++ #[t])))
            let val := implicitPrefix c.ps.size (←
              mkLambdaFVars (c.ps ++ nmotives ++ nminors ++ idxs ++ #[t])
                (mkAppN recCst (c.ps ++ rmotives ++ rminors ++ idxs ++ #[t])))
            return (ty, val)
      addDef niceName (lp :: b.us) (← instantiateMVars type) (← instantiateMVars value)

end BridgeCtx

/-! ## Emitting the declarations -/

/--
Emit the whole encoding for a prepared block.

Everything here telescopes over types that mention the block's members, so the
order matters twice over: the pre-world declarations of steps 1--3 come out of
the `Plan` already built (they could only be built while the scratch axioms were
in scope), and from step 4 on each member is a real constant by the time a later
step looks through its type.
-/
def emit (p : Plan) : TermElabM Unit := do
  let b := p.block
  let docCtx := (← getLCtx, ← getLocalInstances)
  let dIdxs := b.dataIdxs
  -- a constructor of a member the writer declared, whose type mentions a copy,
  -- is emitted under a hidden name; the bridge at the end gives the plain name
  -- the type that was written, and if it cannot, the plain name is an alias
  let copyNames := p.copies.map (·.1)
  let rawCtorName : Name → Name := fun n => Id.run do
    for m in b.members do
      if copyNames.contains m.name then continue
      for c in m.ctors do
        if c.name == n && c.type.getUsedConstants.any (copyNames.contains ·) then
          return Name.mkStr m.name ("_nested_" ++ n.getString!)
    return n
  -- position of a data member among the motives
  let dpos : Array Nat := Id.run do
    let mut out := (List.replicate b.size 0).toArray
    for q in *...dIdxs.size do
      out := out.set! dIdxs[q]! q
    return out

  -- 1. the data members' pre-types
  addInd b.us b.numParams p.preDataInds

  -- 2. the `Prop` members' pre-types
  unless p.prePropInds.isEmpty do
    addInd b.us b.numParams p.prePropInds

  -- 3. the well-formedness predicates
  for (name, type, value) in p.wfDecls do
    addDef name b.us type value (compile := false)

  -- 4. the data members themselves
  for i in dIdxs do
    let m := b.members[i]!
    let value ← forallTelescope m.type fun idxs _ => mkLambdaFVars idxs (b.subtype i idxs)
    addDef m.name b.us m.type value (compile := false)

  -- 5. the `Prop` members, at the subtypes
  for j in b.propIdxs do
    let m := b.members[j]!
    let value ← forallTelescope m.type fun idxs _ => do
      let mut args := #[]
      for y in idxs do
        args := args.push (← b.preImage y (← inferType y))
      mkLambdaFVars idxs (mkAppN (b.cst (preName m.name)) args)
    addDef m.name b.us m.type value (compile := false)

  -- 6. the data constructors
  for i in dIdxs do
    for c in b.members[i]!.ctors do
      let value ← forallTelescope c.type fun xs concl => do
        let mut imgs : Array Expr := #[]
        for x in xs do
          imgs := imgs.push (← b.preImage x (← inferType x))
        let mut preTys : Array Expr := #[]
        for x in xs do
          preTys := preTys.push (b.tr ((← inferType x).replaceFVars xs imgs))
        let recPos := recPositions c.kinds
        let mut conjs : Array Expr := #[]
        let mut proofs : Array Expr := #[]
        for k in recPos do
          conjs := conjs.push (← b.wfOfPre imgs[k]! preTys[k]!)
          proofs := proofs.push (← b.propImage xs[k]! (← inferType xs[k]!))
        for k in *...xs.size do
          if c.kinds[k]! == .erased then
            conjs := conjs.push preTys[k]!
            proofs := proofs.push xs[k]!
        let kept := (keptPositions c.kinds).map (imgs[·]!)
        mkLambdaFVars xs <| b.sMk i concl.getAppArgs
          (mkAppN (b.cst (b.preOf c.name)) kept) (introConj conjs proofs 0)
      addDef (rawCtorName c.name) b.us c.type value

  -- 7. the `Prop` constructors
  for j in b.propIdxs do
    for c in b.members[j]!.ctors do
      let value ← forallTelescope c.type fun xs _ => do
        let mut imgs : Array Expr := #[]
        for x in xs do
          imgs := imgs.push (← b.preImage x (← inferType x))
        mkLambdaFVars xs (mkAppN (b.cst (b.preOf c.name)) imgs)
      addDecl (.thmDecl
        { name := rawCtorName c.name, levelParams := b.us, type := c.type, value })

  -- 8. the recursors, one mutual group by structural recursion on the pre-types
  -- the motive's universe, under a name the writer cannot have taken
  let lp := Id.run do
    let mut c := `u
    let mut k := 0
    while b.us.contains c do
      k := k + 1
      c := Name.mkSimple s!"u_{k}"
    return c
  let lvl := Level.param lp
  let recAuxName (i : Nat) : Name := b.members[i]!.name ++ `recAux
  -- a member of an induction-inductive block is a `def`, so Lean generates no
  -- `X.rec` for it and the name is free -- which is the one users reach for.
  -- It is still checked, in case a member is named under something that has one
  let env ← getEnv
  let recName (i : Nat) : Name :=
    let n := b.members[i]!.name ++ `rec
    if (env.find? n).isNone then n else b.members[i]!.name ++ `recursor
  -- a member the writer declared, in a block with copies in it, gets its
  -- recursor twice over: the kernel-facing one, whose motives are over the
  -- copies, under a hidden name, and `X.rec` stated over the originals.  A copy
  -- is not a name anyone reaches for, so its recursor is only the raw one
  let rawRecName (i : Nat) : Name :=
    if p.copies.isEmpty || copyNames.contains b.members[i]!.name then recName i
    else Name.mkStr b.members[i]!.name "_nested_rec"
  -- one motive is `C`; several are `C_Ctx`, `C_Ty`, .. so they can be named
  let motiveName (i : Nat) : Name :=
    if dIdxs.size == 1 then `C else Name.mkSimple ("C_" ++ b.members[i]!.name.getString!)
  -- the parameters are shared by every motive, minor and recursive call, so the
  -- whole group is built under one telescope of them
  let results ← forallBoundedTelescope b.members[dIdxs[0]!]!.type b.numParams fun ps _ => do
    let motiveDecls : Array (Name × (Array Expr → TermElabM Expr)) := dIdxs.map fun i =>
      (motiveName i, fun _ => do
        forallTelescope (← instantiateForall b.members[i]!.type ps) fun idxs _ =>
          withLocalDeclD `t (mkAppN (b.cst b.members[i]!.name) (ps ++ idxs)) fun t =>
            mkForallFVars (idxs ++ #[t]) (mkSort lvl))
    withImplicits motiveDecls fun motives => do
      -- one minor per constructor of every data member, in block order
      let mut minorDecls : Array (Name × (Array Expr → TermElabM Expr)) := #[]
      for i in dIdxs do
        for c in b.members[i]!.ctors do
          let kinds := b.fieldKinds c.kinds
          minorDecls := minorDecls.push (Name.mkSimple c.name.getString!, fun _ => do
            forallTelescope (← instantiateForall c.type ps) fun xs concl => do
              let ihDecls : Array (Name × (Array Expr → TermElabM Expr)) :=
                (recPositions kinds).map fun k =>
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
        let mut out : Array (Expr × Expr × Expr × Expr) := #[]
        for i in dIdxs do
          let m := b.members[i]!
          let r ← forallTelescope (← instantiateForall m.type ps) fun idxs _ =>
            withLocalDeclD `t (b.preApp i (ps ++ idxs)) fun t0 =>
              withLocalDeclD `w (mkApp (b.wfApp i (ps ++ idxs)) t0) fun w => do
                let concl := mkAppN motives[dpos[i]!]! (idxs ++ #[b.sMk i (ps ++ idxs) t0 w])
                let recAuxType := implicitPrefix ps.size <| ←
                  mkForallFVars (ps ++ motives ++ minors ++ idxs ++ #[t0, w]) concl
                -- the motive of the `casesOn`: the well-formedness proof stays under it
                let inner ← mkForallFVars #[w] concl
                let elim ← getLevel inner
                let casesMotive ← mkLambdaFVars (idxs ++ #[t0]) inner
                let mut alts : Array Expr := #[]
                for c in m.ctors do
                  let kinds := b.fieldKinds c.kinds
                  let alt ← forallTelescope (← instantiateForall c.type ps) fun xs cconcl =>
                    withPreFields b kinds xs fun olds news imgs preTys => do
                      let cIdxs := cconcl.getAppArgs.map (·.replaceFVars olds news)
                      let head := mkAppN (b.cst (b.preOf c.name)) (ps ++ news)
                      withLocalDeclD `w (mkApp (b.wfApp i cIdxs) head) fun wc => do
                        let recPos := recPositions kinds
                        let mut conjs : Array Expr := #[]
                        for k in recPos do
                          conjs := conjs.push (← b.wfOfPre (imgs[k]!).get! preTys[k]!)
                        for k in *...xs.size do
                          if kinds[k]! == .erased then
                            conjs := conjs.push preTys[k]!
                        -- the original fields, rebuilt at the subtypes
                        let mut real : Array Expr := #[]
                        let mut nrec := 0
                        let mut nera := 0
                        for k in *...xs.size do
                          match kinds[k]! with
                          | .recur mm =>
                            let y := (imgs[k]!).get!
                            let pr := projConj conjs wc nrec
                            real := real.push <| ← b.withPreTarget preTys[k]! fun ys _ args =>
                              mkLambdaFVars ys
                                (b.sMk mm args (mkAppN y ys) (mkAppN pr ys))
                            nrec := nrec + 1
                          | .plain => real := real.push (imgs[k]!).get!
                          | .erased =>
                            real := real.push (projConj conjs wc (recPos.size + nera))
                            nera := nera + 1
                        let mut ihs : Array Expr := #[]
                        for q in *...recPos.size do
                          let k := recPos[q]!
                          let y := (imgs[k]!).get!
                          let pr := projConj conjs wc q
                          ihs := ihs.push <| ← b.withPreTarget preTys[k]! fun ys mm args =>
                            mkLambdaFVars ys (mkAppN (mkConst (recAuxName mm) (lvl :: b.lvls))
                              (ps ++ motives ++ minors ++ b.idxArgs args ++
                                #[mkAppN y ys, mkAppN pr ys]))
                        let minorIdx := Id.run do
                          let mut acc := 0
                          for i' in dIdxs do
                            for c' in b.members[i']!.ctors do
                              if c'.name == c.name then return acc
                              acc := acc + 1
                          return acc
                        mkLambdaFVars (news ++ #[wc])
                          (mkAppN minors[minorIdx]! (real ++ ihs))
                  alts := alts.push alt
                let body := mkApp (mkAppN (mkConst (preName m.name ++ `casesOn) (elim :: b.lvls))
                  (ps ++ #[casesMotive] ++ idxs ++ #[t0] ++ alts)) w
                let recAuxValue := implicitPrefix ps.size <|
                  ← mkLambdaFVars (ps ++ motives ++ minors ++ idxs ++ #[t0, w]) body
                let (recType, recValue) ←
                  withLocalDeclD `t (mkAppN (b.cst m.name) (ps ++ idxs)) fun t => do
                    let ty := implicitPrefix ps.size <| ←
                      mkForallFVars (ps ++ motives ++ minors ++ idxs ++ #[t])
                        (mkAppN motives[dpos[i]!]! (idxs ++ #[t]))
                    let val := implicitPrefix ps.size <| ←
                      mkLambdaFVars (ps ++ motives ++ minors ++ idxs ++ #[t])
                        (mkAppN (mkConst (recAuxName i) (lvl :: b.lvls))
                          (ps ++ motives ++ minors ++ idxs ++
                            #[b.sVal i (ps ++ idxs) t, b.sProp i (ps ++ idxs) t]))
                    return (ty, val)
                return (recAuxType, recAuxValue, recType, recValue)
          out := out.push r
        return out
  let mut preDefs : Array PreDefinition := #[]
  for q in *...dIdxs.size do
    let (recAuxType, recAuxValue, _, _) := results[q]!
    preDefs := preDefs.push
      { ref := .missing, kind := .def, levelParams := lp :: b.us, modifiers := {},
        declName := recAuxName dIdxs[q]!, binders := .missing, type := recAuxType,
        value := recAuxValue, termination := TerminationHints.none }
  -- `structuralRecursion` throws if it cannot see that the definitions
  -- terminate, which is what we want; but it also throws on a definition that
  -- does not recurse at all, so those go the direct way
  let auxNames := dIdxs.map recAuxName
  if preDefs.any fun d => d.value.getUsedConstants.any (auxNames.contains ·) then
    Structural.structuralRecursion docCtx preDefs
      (preDefs.map fun _ => (none : Option TerminationMeasure))
  else
    for preDef in preDefs do
      addAndCompileNonRec docCtx preDef
  for q in *...dIdxs.size do
    let (_, _, recType, recValue) := results[q]!
    addDef (rawRecName dIdxs[q]!) (lp :: b.us) recType recValue

  -- 9. the bridge back to the originals
  unless p.copies.isEmpty do
    let env ← getEnv
    let built ← forallBoundedTelescope b.members[dIdxs[0]!]!.type b.numParams fun ps _ => do
      let copies : Array Copy := p.copies.filterMap fun (n, e) => do
        let idx ← b.memberIdx? n
        let app := e.beta ps
        let indName ← app.getAppFn.constName?
        some { idx, name := n, indName, app }
      let c : BridgeCtx := { b, ps, copies }
      -- the round trip is wanted exactly where a constructor of the writer's own
      -- has a copy-typed field, which is where the recursor has to transport
      let needed : Array Nat := Id.run do
        let mut out : Array Nat := #[]
        for i in dIdxs do
          if (c.copyAt? i).isSome then continue
          for cc in b.members[i]!.ctors do
            if rawCtorName cc.name == cc.name then continue
            for k in b.fieldKinds cc.kinds do
              if let .recur m := k then
                if let some k' := c.copyAt? m then
                  unless out.contains k' do out := out.push k'
        return out
      try
        c.addOfOrig docCtx
        c.addToOrig rawRecName
        c.niceCtors rawCtorName
        c.addRoundTrips needed rawRecName
        for i in dIdxs do
          if (c.copyAt? i).isNone then
            c.addNiceRec i lp rawRecName (recName i) rawCtorName
        return true
      catch _ =>
        -- the bridge is all or nothing: it adds declarations one by one, and a
        -- half-built one would collide with the plain names the fallback uses
        setEnv env
        return false
    unless built do
      -- the copies stay visible, and the plain names are the raw declarations
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
        let (_, _, recType, _) := results[q]!
        addDef (recName i) (lp :: b.us) recType (mkConst (rawRecName i) (lvl :: b.lvls))

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

/-- Elaborate an induction-inductive block by erasing its proof fields. -/
def elabInductionInductive (elems : Array Syntax) : CommandElabM Unit := do
  let inductives ← elems.mapM fun stx => do
    let modifiers ← elabModifiers ⟨stx[0]⟩
    pure (modifiers, stx[1])
  let elabs ← runTermElabM fun _ => inductives.mapM fun (m, s) => mkInductiveView m s
  let views := elabs.map (·.view)
  runTermElabM fun vars => do
    unless vars.isEmpty do
      throwError "Section variables are not supported for an induction-inductive block"
    emit (← prepare views)

/--
Elaborate a *nested* inductive whose denesting is induction-inductive.

The gate is that denesting must both add a member and leave some member's arity
mentioning the block.  That is exactly the case `Mumi.Denest` refuses -- it can
specialise a nesting type only when the copy's arity comes out free of the
block -- so nothing that already works reaches here.
-/
def elabNestedInductive (elems : Array Syntax) : CommandElabM Unit := do
  let inductives ← elems.mapM fun stx => do
    let modifiers ← elabModifiers ⟨stx[0]⟩
    pure (modifiers, stx[1])
  let elabs ← runTermElabM fun _ => inductives.mapM fun (m, s) => mkInductiveView m s
  let views := elabs.map (·.view)
  let plan ← runTermElabM fun vars => do
    unless vars.isEmpty do
      throwError "Section variables are not supported for an induction-inductive block"
    withRaw views fun r => do
      let r ← denestRaw r
      if r.names.size == views.size then
        throwError "This inductive has no nested occurrence to denest"
      unless r.arities.any (mentionsNames r.names ·) do
        throwError "Denesting this inductive does not make it induction-inductive"
      prepareCore r
  runTermElabM fun _ => emit plan

end Mumi.IndInd
