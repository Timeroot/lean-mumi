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

def Ctx.recursor {C : Ctx → Sort u} .. (Γ : Ctx) : C Γ :=
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
  `induction Γ using Ctx.recursor with | nil => .. | snoc Γ x h ih => ..`; a
  bare `induction` or `cases` destructs the subtype and leaks `Ctx._pre` into
  the goal.
* `cases` on a `Prop` member works only where the motive does not depend on the
  indices, and otherwise fails ("dependent elimination failed"), because its
  recursor is still `Fresh._pre`'s, stated over the pre-type.  Deriving a real
  `Fresh.rec` from it -- motive `fun x Γ₀ h => ∀ w, motive x ⟨Γ₀, w⟩ h` -- is
  the obvious next step and is not done here.
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
  deriving Inhabited

/-- The block, elaborated and checked, ready for `emit`. -/
def prepare (views : Array InductiveView) : TermElabM Plan := do
  checkSupported views
  let scopeLevelNames ← Term.getLevelNames
  withoutModifyingEnv <| Term.withLevelNames views[0]!.levelNames do
    let n := views.size
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
      unless ← isDefEq (← paramShape arities[0]!.get!) (← paramShape arities[i]!.get!) do
        throwError "The parameters of `{views[0]!.declName}` and `{views[i]!.declName}` differ; \
          every member of a mutual block must take the same ones"
    -- which members are propositions, and at what universe each one lives
    let mut isProp : Array Bool := #[]
    let mut levels : Array Level := #[]
    for i in *...n do
      let (p, l) ← forallTelescopeReducing arities[i]!.get! fun _ r => do
        match ← whnfD r with
        | .sort u => return (u.normalize == Level.zero, u)
        | _ => throwError "The resulting type of `{views[i]!.declName}` is not a sort"
      isProp := isProp.push p
      levels := levels.push l
    let dataIdxs := (Array.range n).filter (!isProp[·]!)
    let propIdxs := (Array.range n).filter (isProp[·]!)
    if dataIdxs.isEmpty then
      throwError "Every member of this induction-inductive block is a proposition; there is \
        nothing for the erasure to keep"
    -- a data member indexed by the block is data-on-data induction-induction,
    -- which erasure cannot reach; say so before elaborating any constructor
    for i in dataIdxs do
      if arities[i]!.get!.getUsedConstants.any (blockNames.contains ·) then
        throwError "The arity of `{views[i]!.declName}` mentions the block.  Erasure can only \
          reach an induction-induction whose dependency runs through `Prop`, and this one \
          indexes data by data"
    -- the data members become one mutual pre-block, so the kernel's own
    -- same-universe rule applies to them
    for i in dataIdxs do
      unless levels[i]!.normalize == levels[dataIdxs[0]!]!.normalize do
        let fst := toString (← ppExpr (mkSort levels[dataIdxs[0]!]!))
        let snd := toString (← ppExpr (mkSort levels[i]!))
        throwError "The data members `{views[dataIdxs[0]!]!.declName}` and \
          `{views[i]!.declName}` of this induction-inductive block live in different \
          universes, `{fst}` and `{snd}`; the erased pre-block is a single mutual \
          inductive, so they must agree"
    -- a data member is encoded as a `Subtype`, which lands in `Sort (max 1 l)`.
    -- For `Type v` that is `Sort l` again; for a bare `Sort u`, which might yet
    -- be `Prop`, it is not, and the definition would not typecheck
    for i in dataIdxs do
      unless ← isLevelDefEq (mkLevelMax Level.one levels[i]!) levels[i]! do
        let s := toString (← ppExpr (mkSort levels[i]!))
        throwError "The data member `{views[i]!.declName}` lives at `{s}`, which could still \
          be `Prop`.  It is encoded as a subtype, and `Subtype` lands one universe up from \
          `Prop`, so a data member's universe has to be visibly non-zero -- `Type v` rather \
          than `Sort v`"
    -- a constructor of an indexed family has to say what its indices are; Lean
    -- refuses this too, and here the fallback would silently make the resulting
    -- type the unapplied family, which is not even a proposition
    for i in *...n do
      let arityBinders ← forallTelescope arities[i]!.get! fun xs _ => pure xs.size
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
    -- the block's universe parameters: whichever of the declared and auto-bound
    -- ones anything in the block actually uses, in Lean's own order
    let mut cps : CollectLevelParams.State := {}
    for i in *...n do
      cps := collectLevelParams cps arities[i]!.get!
      for t in ctorTypes[i]! do
        cps := collectLevelParams cps t
    let us ← match sortDeclLevelParams scopeLevelNames views[0]!.levelNames cps.params with
      | .ok us => pure us
      | .error msg => throwError msg
    let lvls := us.map Level.param
    arities := arities.map (·.map (normLevels blockNames lvls))
    ctorTypes := ctorTypes.map (·.map (normLevels blockNames lvls))
    -- a skeleton is enough for `Block.mentions`, `Block.preOf` and `Block.memberIdx?`
    let skeleton : Block :=
      { numParams, us
        members := (Array.range n).map fun i =>
          { name := views[i]!.declName, type := arities[i]!.get!, isProp := isProp[i]!
            level := levels[i]!
            ctors := (Array.range ctorTypes[i]!.size).map fun j =>
              { name := views[i]!.ctors[j]!.declName, type := ctorTypes[i]![j]!,
                kinds := #[] } } }
    -- a `Prop` member's index is rewritten by taking each argument to the
    -- pre-world, and that is only possible one index at a time: an index whose
    -- type merely *contains* a member, `List Ctx`, has no such image
    for j in propIdxs do
      forallTelescope arities[j]!.get! fun idxs _ => do
        for y in idxs do
          let ty ← inferType y
          unless (← recTargetOf? skeleton ty).isSome do
            if skeleton.mentions ty then
              throwError "The index `{y}` of `{views[j]!.declName}` mentions the block \
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
    return { block := b, preDataInds, prePropInds, wfDecls }
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
      addDef c.name b.us c.type value

  -- 7. the `Prop` constructors
  for j in b.propIdxs do
    for c in b.members[j]!.ctors do
      let value ← forallTelescope c.type fun xs _ => do
        let mut imgs : Array Expr := #[]
        for x in xs do
          imgs := imgs.push (← b.preImage x (← inferType x))
        mkLambdaFVars xs (mkAppN (b.cst (b.preOf c.name)) imgs)
      addDecl (.thmDecl { name := c.name, levelParams := b.us, type := c.type, value })

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
  let recName (i : Nat) : Name := b.members[i]!.name ++ `recursor
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
                      #[mkAppN (b.cst c.name) (ps ++ xs)])))
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
    addDef (recName dIdxs[q]!) (lp :: b.us) recType recValue

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

end Mumi.IndInd
