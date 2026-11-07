/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import MumiTests.Spec.Harness

/-!
# Shapes a denesting can take

`MumiTests/GrandRec.lean` varies the *block*: abstract universes, several
predicates over one type, infinitary constructors, two unrelated families at
once.  This file varies the *nesting* -- the path from the writer's constructor
down to the recursive occurrence -- and holds the block fixed.

Most sections below reuse one family, `Lib.Tree` / `Lib.Tree.WF` /
`Lib.WFTree`, so that the only thing differing between them is how the writer
reaches it: through a second copy of the same family, through a `List`, twice
in one constructor, through a function, at an index the constructor supplies.
Two sections near the end are shapes that do *not* come out whole; they are
here so that a change in what the library accepts shows up as a test failure
rather than as a surprise.
-/

namespace MumiTests.Shapes

/-! ## The shared family -/

namespace Lib

mumi_spec
inductive Tree (α : Type u) : Type u where
  | empty
  | node (a : α) (l r : Tree α)

mumi_spec
inductive Tree.WF (α : Type u) : Tree α → Prop where
  | empty : Tree.WF α .empty
  | node (a : α) (l r : Tree α) (hl : Tree.WF α l) (hr : Tree.WF α r) :
      Tree.WF α (.node a l r)

mumi_spec
inductive WFTree (α : Type u) : Type u where
  | mk (x : Tree α) (h : x.WF)

end Lib

open Lib

/-! ## Nesting inside nesting

`WFTree (WFTree R)` copies the whole family twice over, once at `R` and once at
`WFTree R`, and the outer copy's parameters mention the inner copy.  The two
copies of `Tree` are *different types*, so the order the copies get built in has
to be a sort of the copies themselves; sorting the types they were copied from
has `Tree` waiting on `Tree` and the whole block falling back to leaving the
copies visible.
-/

namespace Deep

mumi_spec (simp := [R.rec_mk, R.rec_1_mk, R.rec_2_node, R.rec_4_mk, R.rec_5_node, R.casesOn_mk])
inductive R where
  | mk (x : WFTree (WFTree R))

namespace R

/-- A one-element tree under a proof that it is well formed. -/
def lift (r : R) : WFTree R :=
  .mk (.node r .empty .empty) (.node r .empty .empty .empty .empty)

def wrap (x : WFTree R) : R :=
  .mk (.mk (.node x .empty .empty) (.node x .empty .empty .empty .empty))

def base : R := .mk (.mk .empty .empty)

/-- How many `R`s there are. -/
def size : R → Nat :=
  R.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat) (motive_3 := fun _ => Nat)
    (motive_4 := fun _ _ _ => True) (motive_5 := fun _ => Nat) (motive_6 := fun _ => Nat)
    (motive_7 := fun _ _ _ => True)
    (fun _ ih => 1 + ih)
    (fun _ _ ih _ => ih)
    0 (fun _ _ _ iha ihl ihr => iha + ihl + ihr)
    trivial (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ ih _ => ih)
    0 (fun _ _ _ iha ihl ihr => iha + ihl + ihr)
    trivial (fun _ _ _ _ _ _ _ _ _ _ => trivial)

example : size base = 1 := rfl
example : size (wrap (lift base)) = 2 := rfl

/--
Rebuilding, which is what the two predicate motives are for.

The minor for `WFTree.mk` is handed a proof that the tree it was *given* is well
formed and has to produce one about the tree the recursion *built*; `motive_4`
and `motive_7` are what carry that across, one for each copy of
`Tree.WF`; the motives are numbered as Lean numbers a nested inductive's, every
type a constructor nests before what those nest in turn.
-/
def rebuild : R → R :=
  R.rec (motive_1 := fun _ => R) (motive_2 := fun _ => WFTree (WFTree R))
    (motive_3 := fun _ => Tree (WFTree R))
    (motive_4 := fun _ ih _ => Tree.WF (WFTree R) ih)
    (motive_5 := fun _ => WFTree R) (motive_6 := fun _ => Tree R)
    (motive_7 := fun _ ih _ => Tree.WF R ih)
    (fun _ ih => .mk ih)
    (fun _ _ ih hw => .mk ih hw)
    .empty (fun _ _ _ iha ihl ihr => .node iha ihl ihr)
    .empty (fun _ _ _ _ _ iha ihl ihr hl hr => .node iha ihl ihr hl hr)
    (fun _ _ ih hw => .mk ih hw)
    .empty (fun _ _ _ iha ihl ihr => .node iha ihl ihr)
    .empty (fun _ _ _ _ _ iha ihl ihr hl hr => .node iha ihl ihr hl hr)

example : rebuild base = base := rfl
example : size (rebuild (wrap (lift base))) = 2 := rfl

/-- info: 'MumiTests.Shapes.Deep.R.rebuild' does not depend on any axioms -/
#guard_msgs in
#print axioms rebuild

end R

end Deep

/-! ## A plain container in between

No member of the block occurs in `List`, so `List` is not copied and gets no
well-formedness of its own; the denesting has to see straight through it to the
`WFTree R` inside, and `List`'s own recursion is spliced into the block's.
-/

namespace Between

mumi_spec (simp := [R.rec_mk, R.rec_1_cons, R.rec_2_mk, R.rec_3_node, R.casesOn_mk])
inductive R where
  | mk (xs : List (WFTree R))

namespace R

def leaf : R := .mk []

def wrap (rs : List R) : R :=
  .mk (rs.map fun r => .mk (.node r .empty .empty) (.node r .empty .empty .empty .empty))

def size : R → Nat :=
  R.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat) (motive_3 := fun _ => Nat)
    (motive_4 := fun _ => Nat) (motive_5 := fun _ _ _ => True)
    (fun _ ih => 1 + ih)
    0 (fun _ _ ih iht => ih + iht)
    (fun _ _ ih _ => ih)
    0 (fun _ _ _ iha ihl ihr => iha + ihl + ihr)
    trivial (fun _ _ _ _ _ _ _ _ _ _ => trivial)

example : size leaf = 1 := rfl
example : size (wrap [leaf, leaf, leaf]) = 4 := rfl

end R

end Between

/-! ## An indexed data member, with the predicate indexed alongside it

`Vec` is indexed by its length and `Vec.Up` by that same length *and* the
vector, so the copy of `Vec.Up` has an index of the copy's own type.  The writer
picks one length out of the family and only that one gets copied.
-/

namespace Indexed

mumi_spec
inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons {n : Nat} (a : α) (v : Vec α n) : Vec α (n + 1)

mumi_spec
inductive Vec.Up (α : Type) : (n : Nat) → Vec α n → Prop where
  | nil : Vec.Up α 0 .nil
  | cons {n : Nat} (a : α) (v : Vec α n) (h : Vec.Up α n v) :
      Vec.Up α (n + 1) (.cons a v)

mumi_spec
inductive UVec (α : Type) (n : Nat) where
  | mk (v : Vec α n) (h : Vec.Up α n v)

mumi_spec (simp := [R.rec_mk, R.rec_1_mk, R.rec_2_cons, R.casesOn_mk])
inductive R where
  | tip
  | mk (x : UVec R 2)

namespace R

def pair (x y : R) : R :=
  .mk (.mk (.cons x (.cons y .nil)) (.cons x (.cons y .nil) (.cons y .nil .nil)))

def size : R → Nat :=
  R.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat)
    (motive_3 := fun _ _ => Nat) (motive_4 := fun _ _ _ _ => True)
    1
    (fun _ ih => ih)
    (fun _ _ ih _ => ih)
    0 (fun _ _ iha ihv => iha + ihv)
    trivial (fun _ _ _ _ _ _ => trivial)

example : size .tip = 1 := rfl
example : size (pair .tip (pair .tip .tip)) = 3 := rfl

end R

end Indexed

/-! ## The same nesting twice in one constructor

Two fields at the same nested type have to share one copy, not get one each.
-/

namespace Twice

mumi_spec (simp := [R.rec_mk, R.rec_1_mk, R.rec_2_node, R.casesOn_mk])
inductive R where
  | tip
  | mk (x : WFTree R) (y : WFTree R)

namespace R

def lift (r : R) : WFTree R :=
  .mk (.node r .empty .empty) (.node r .empty .empty .empty .empty)

def pair (x y : R) : R := .mk (lift x) (lift y)

def size : R → Nat :=
  R.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat) (motive_3 := fun _ => Nat)
    (motive_4 := fun _ _ _ => True)
    1
    (fun _ _ ihx ihy => ihx + ihy)
    (fun _ _ ih _ => ih)
    0 (fun _ _ _ iha ihl ihr => iha + ihl + ihr)
    trivial (fun _ _ _ _ _ _ _ _ _ _ => trivial)

example : size .tip = 1 := rfl
example : size (pair .tip (pair .tip .tip)) = 3 := rfl

/-- Rebuilding, which needs the predicate motive. -/
def rebuild : R → R :=
  R.rec (motive_1 := fun _ => R) (motive_2 := fun _ => WFTree R)
    (motive_3 := fun _ => Tree R) (motive_4 := fun _ ih _ => Tree.WF R ih)
    .tip
    (fun _ _ ihx ihy => .mk ihx ihy)
    (fun _ _ ih hw => .mk ih hw)
    .empty (fun _ _ _ iha ihl ihr => .node iha ihl ihr)
    .empty (fun _ _ _ _ _ iha ihl ihr hl hr => .node iha ihl ihr hl hr)

example : rebuild (pair .tip .tip) = pair .tip .tip := rfl

/-- info: 'MumiTests.Shapes.Twice.R.rebuild' does not depend on any axioms -/
#guard_msgs in
#print axioms rebuild

end R

end Twice

/-! ## A writer with its own parameter, at an abstract universe

Every copy has to carry `β` and `u` along, and the block lands where `R` was
declared rather than where the family it nests was.
-/

namespace Param

mumi_spec (simp := [R.rec_mk, R.rec_1_mk, R.rec_2_node, R.casesOn_mk])
inductive R (β : Type u) : Type u where
  | leaf (b : β)
  | mk (x : WFTree (R β))

namespace R

def wrap {β : Type u} (r : R β) : R β :=
  .mk (.mk (.node r .empty .empty) (.node r .empty .empty .empty .empty))

def size {β : Type u} : R β → Nat :=
  R.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat) (motive_3 := fun _ => Nat)
    (motive_4 := fun _ _ _ => True)
    (fun _ => 1)
    (fun _ ih => ih)
    (fun _ _ ih _ => ih)
    0 (fun _ _ _ iha ihl ihr => iha + ihl + ihr)
    trivial (fun _ _ _ _ _ _ _ _ _ _ => trivial)

example : size (wrap (wrap (R.leaf 3))) = 1 := rfl

end R

end Param

/-! ## The writer reached through a function field

`Fn`'s field is a function into `α`, so the copy is infinitary: its minor takes
a function of induction hypotheses rather than one per recursive field, and the
recursion still computes.
-/

namespace Fun

mumi_spec
inductive Fn (α : Type) where
  | mk (f : Bool → α)

mumi_spec
inductive Fn.Tot (α : Type) : Fn α → Prop where
  | mk (f : Bool → α) : Fn.Tot α (.mk f)

mumi_spec
inductive TFn (α : Type) where
  | mk (x : Fn α) (h : x.Tot)

mumi_spec
inductive R where
  | tip
  | mk (x : TFn R)

namespace R

def pair (x y : R) : R := .mk (.mk (.mk (fun b => cond b x y)) (.mk (fun b => cond b x y)))

def size : R → Nat :=
  R.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat) (motive_3 := fun _ => Nat)
    (motive_4 := fun _ _ _ => True)
    1
    (fun _ ih => ih)
    (fun _ _ ih _ => ih)
    (fun _ ih => ih true + ih false)
    (fun _ _ => trivial)

example : size .tip = 1 := rfl
example : size (pair .tip (pair .tip .tip)) = 3 := rfl

end R

end Fun

/-! ## The bundle is a `structure`

Nothing says the type carrying the value and its proof has to be an
`inductive`; a one-constructor `structure` is the ordinary way to write it, and
the minor's conclusion comes out in structure-instance notation.
-/

namespace Struct

structure SWFTree (α : Type u) : Type u where
  x : Tree α
  h : x.WF

mumi_spec (simp := [R.rec_mk, R.rec_1_mk, R.rec_2_node, R.casesOn_mk])
inductive R where
  | tip
  | mk (y : SWFTree R)

namespace R

def wrap (r : R) : R :=
  .mk { x := .node r .empty .empty, h := .node r .empty .empty .empty .empty }

def size : R → Nat :=
  R.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat) (motive_3 := fun _ => Nat)
    (motive_4 := fun _ _ _ => True)
    1
    (fun _ ih => 1 + ih)
    (fun _ _ ih _ => ih)
    0 (fun _ _ _ iha ihl ihr => iha + ihl + ihr)
    trivial (fun _ _ _ _ _ _ _ _ _ _ => trivial)

example : size .tip = 1 := rfl
example : size (wrap (wrap .tip)) = 3 := rfl

end R

end Struct

/-! ## The bundle is a `Subtype`

`{ t : Tree R // t.WF }` is the shortest way to say it, and the one that needs
no new declaration at all.  `Subtype` carries its predicate as a *parameter*, so
the copy's proof field arrives as `(fun t => WF t) val` -- a beta-redex whose
binder mentions a data member though the proposition it states does not.  What a
field is, is its beta-normal form.
-/

namespace Sub

mumi_spec (simp := [R.rec_mk, R.rec_1_mk, R.rec_2_node, R.casesOn_mk])
inductive R where
  | tip
  | mk (y : { t : Tree R // t.WF })

namespace R

def wrap (r : R) : R :=
  .mk ⟨.node r .empty .empty, .node r .empty .empty .empty .empty⟩

def size : R → Nat :=
  R.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat) (motive_3 := fun _ => Nat)
    (motive_4 := fun _ _ _ => True)
    1
    (fun _ ih => 1 + ih)
    (fun _ _ ih _ => ih)
    0 (fun _ _ _ iha ihl ihr => iha + ihl + ihr)
    trivial (fun _ _ _ _ _ _ _ _ _ _ => trivial)

example : size .tip = 1 := rfl
example : size (wrap (wrap .tip)) = 3 := rfl

/-- Rebuilding, which needs the predicate motive. -/
def rebuild : R → R :=
  R.rec (motive_1 := fun _ => R) (motive_2 := fun _ => { t : Tree R // t.WF })
    (motive_3 := fun _ => Tree R) (motive_4 := fun _ ih _ => Tree.WF R ih)
    .tip
    (fun _ ih => .mk ih)
    (fun _ _ ih hw => ⟨ih, hw⟩)
    .empty (fun _ _ _ iha ihl ihr => .node iha ihl ihr)
    .empty (fun _ _ _ _ _ iha ihl ihr hl hr => .node iha ihl ihr hl hr)

example : rebuild (wrap .tip) = wrap .tip := rfl

/-- info: 'MumiTests.Shapes.Sub.R.rebuild' does not depend on any axioms -/
#guard_msgs in
#print axioms rebuild

end R

end Sub

/-! ## An induction-inductive nesting beside an ordinary one

`List R` is nested the way Lean nests things; `WFTree R` is not.  Both end up in
one recursion, with `List`'s minors after the family's.
-/

namespace Mixed

mumi_spec (simp := [R.rec_mk, R.rec_1_mk, R.rec_2_cons, R.rec_3_node, R.casesOn_mk])
inductive R where
  | tip
  | mk (x : WFTree R) (l : List R)

end Mixed

/-! ## A container inside the family's parameter

`WFTree (Option R)`: `Option` sits between the copy's parameter and the writer,
so it is copied too and gets a motive of its own.
-/

namespace InParam

mumi_spec (simp := [R.rec_mk, R.rec_1_mk, R.rec_2_node, R.casesOn_mk])
inductive R where
  | tip
  | mk (x : WFTree (Option R))

end InParam

/-! ## Two writers over one family, and one nested at the other

`Ra` denests the family at itself; `Rb` denests it again at `Ra × Rb`, where
`Ra` is already a type this library built.  The copies must not collide, and
`Ra` -- which `Rb` does not recurse into -- must not acquire a motive.
-/

namespace Twin

mumi_spec (simp := [Ra.rec_mk, Ra.rec_1_mk, Ra.rec_2_node, Ra.casesOn_mk])
inductive Ra where
  | tip
  | mk (x : WFTree Ra)

mumi_spec (simp := [Rb.rec_mk, Rb.rec_1_mk, Rb.rec_2_node, Rb.casesOn_mk])
inductive Rb where
  | tip
  | mk (x : WFTree (Ra × Rb))

end Twin

/-! ## A `Prop` constructor with a data field its conclusion does not reach

`Chain.Pair.cons` has a field `u : Chain α` that the conclusion never mentions.
A `Prop` constructor carries no well-formedness of its own -- only what its
indices bring it -- so there is nothing to put `u` back at its subtype with.

What the field can be put back at instead is any element of its type at all.  A
field the conclusion forgets is exactly what makes the proposition fail to be a
subsingleton, so every motive over it is `Prop`-valued and everything the
recursion has to build for it is a proof; two proofs of one proposition are
definitionally equal, so the element that was meant and the element that was
found are interchangeable.

What the recursion cannot do is say anything *about* the substitute, so the minor
premise binds `u` and offers no induction hypothesis at it -- which is what Lean's
own recursor for such a proposition does too, having no motive to offer one from.
Everything else survives: the `Prop` recursors are stated, the map back to the
originals goes through, and the recursor over the whole block is stated as well.
-/

namespace Stray

mumi_spec
inductive Chain (α : Type) where
  | nil
  | cons (a : α) (t : Chain α)

mumi_spec
inductive Chain.Pair (α : Type) : Chain α → Prop where
  | nil : Chain.Pair α .nil
  | cons (a : α) (t u : Chain α) (h : Chain.Pair α t) : Chain.Pair α (.cons a t)

mumi_spec
inductive PChain (α : Type) where
  | mk (c : Chain α) (h : c.Pair)

-- nothing is held back any more.  What the trace still says is that the
-- course-of-values recursion could not be built: the block is nested, so the
-- recursor computes at a constructor only up to a transport, and the table
-- `below` would have to reduce there for anything to be read out of it
/--
trace: [Mumi.indind] no course-of-values recursion for `MumiTests.Shapes.Stray.R`: (kernel) application type mismatch
      F (R.mk x) PUnit.unit
    argument has type
      PUnit
    but function has type
      @R._sub.below motive (R.mk x) → motive (R.mk x)
-/
#guard_msgs in
set_option trace.Mumi.indind true in
inductive R where
  | tip
  | mk (x : PChain R)

-- the minor for `cons` binds `u` and stops there: there is no `u_ih`

/-! The constructor is the writer's own, and so is what it takes. -/

/--
info: @Chain.Pair.cons : ∀ {α : Type} (a : α) (t u : Chain α), Chain.Pair α t → Chain.Pair α (Chain.cons a t)
-/
#guard_msgs in
#check @Chain.Pair.cons

/-! And the stand-in is invisible, because it is a proof: `cons` at one `u` and
`cons` at another are the same term. -/

example (a : R) (t u v : Chain R) (h : Chain.Pair R t) :
    Chain.Pair.cons a t u h = Chain.Pair.cons a t v h := rfl

end Stray

/-! ## A `Prop` indexed by another `Prop`

`A.Q` is indexed by a proof of `A.P`, and no member of a mutual inductive may
appear in another's arity.  But nothing says the propositions have to be one
mutual inductive: they are erased, and nothing is defined by recursion across
the whole of them, so they are declared as several, one after another, and one
indexed by another comes second and names its pre-type as freely as it names
the data.  The only shape still refused is the genuine cycle, two propositions
each in the other's arity.

The constructor carries both proofs, and the second is about the first, so the
well-formedness has to say something that mentions a field the pre-term does
not keep.  What it says is `P._pre x ∧ ∀ h, Q._pre x h`, which is the
existential the pair really is, written so that proof irrelevance closes both
directions definitionally.
-/

namespace PropIdx

mumi_spec
inductive A (α : Type) where
  | mk (a : α)
  | nil

mumi_spec
inductive A.P (α : Type) : A α → Prop where
  | mk (a : α) : A.P α (.mk a)

mumi_spec
inductive A.Q (α : Type) : (x : A α) → A.P α x → Prop where
  | mk (a : α) : A.Q α (.mk a) (.mk a)

mumi_spec
inductive QA (α : Type) where
  | mk (x : A α) (h : x.P) (q : A.Q α x h)

mumi_spec (simp := [R.casesOn_mk, R.rec_mk])
inductive R where
  | mk (x : QA R)

/-! Both propositions get a motive, and both are stated over the originals: the
copies denesting made of `A`, `A.P` and `A.Q` are gone by the time the recursor
is named. -/

/-! And the `Prop`-typed index says nothing, `Prop` being proof-irrelevant. -/

example (x : A R) (h h' : A.P R x) : A.Q R x h = A.Q R x h' := rfl

end PropIdx

/-! ## A `Prop` member with no constructors

Which of an inductive's binders are parameters is read off its constructors, and
`Box.Never` has none: every binder is fixed across all zero of them, so the index
it was written with arrives promoted to a parameter.  That is what Lean's own
nesting check trips over -- the occurrence `Box.Never R b` then has a parameter
holding `b`, a field of the constructor it sits in, and the kernel takes no
nesting whose parameters are not closed.

Denesting specialises only as far as the block reaches.  `R` is the last
parameter that mentions it, so the promoted index stays an index of the copy,
where it is rewritten along with everything else and comes out at the copy of
`Box`; the bridge then carries it back.  What the writer reads is the same block
they would get if the proposition had a constructor and Lean had left its index
alone.
-/

namespace Empty

mumi_spec
inductive Box (α : Type) where
  | mk (a : α)
  | nil

mumi_spec
inductive Box.Never (α : Type) : Box α → Prop

mumi_spec
inductive NBox (α : Type) where
  | mk (b : Box α) (h : b.Never)

mumi_spec (simp := [R.casesOn_mk, R.rec_mk, R.rec_1_mk])
inductive R where
  | tip
  | mk (x : NBox R)

end Empty

/-! ## The writer is indexed, and passes its index into the nesting

`R n` nests `WFTree (R n)`, so the copy of `WFTree` cannot be parameterised once
and for all: `n` is a *field of the constructor the occurrence sits in*, not a
parameter of the block, and copies are settled before any constructor is.  What
denesting does instead is copy the whole family *indexed by* `n` -- one copy
standing for `WFTree (R 0)`, `WFTree (R 1)` and the rest at once -- and hand each
constructor of the copy the `n` it belongs to as a leading field.

Every motive below is then indexed by `n`, and none of the copies is visible:
the recursor is stated over `WFTree`, `Tree` and `Tree.WF` themselves.
-/

namespace IdxW

mumi_spec (simp := [R.rec_mk, R.rec_1_mk, R.rec_2_node, R.casesOn_mk])
inductive R : Nat → Type where
  | tip (n : Nat) : R n
  | mk (n : Nat) (x : WFTree (R n)) : R n

namespace R

/-- A one-element tree of `R n`s under a proof that it is well formed. -/
def lift (r : R n) : WFTree (R n) :=
  .mk (.node r .empty .empty) (.node r .empty .empty .empty .empty)

def wrap (x : WFTree (R n)) : R n := .mk n x

/-- How many `R`s there are. -/
def size : R n → Nat :=
  R.rec (motive_1 := fun _ _ => Nat) (motive_2 := fun _ _ => Nat)
    (motive_3 := fun _ _ => Nat) (motive_4 := fun _ _ _ _ => True)
    (fun _ => 1) (fun _ _ ih => 1 + ih)
    (fun _ _ _ ih _ => ih)
    (fun _ => 0) (fun _ _ _ _ iha ihl ihr => iha + ihl + ihr)
    (fun _ => trivial) (fun _ _ _ _ _ _ _ _ _ _ _ => trivial)

example : size (.tip 3) = 1 := rfl
example : size (wrap (lift (.tip 3))) = 2 := rfl

/-- info: 3 -/
#guard_msgs in
#eval size (wrap (lift (wrap (lift (.tip 0)))))

/-- info: 'MumiTests.Shapes.IdxW.R.size' does not depend on any axioms -/
#guard_msgs in
#print axioms R.size

end R

end IdxW

/-! ## The nesting's parameter is a variable the constructor binds

Lean's kernel refuses a nested occurrence whose parameters mention a local, so
`Cx H n` is out: `n` is bound by the constructor that reaches it.  Denesting it
by hand has no such trouble -- the copy takes `n` as an index of its own -- and
what comes back is the block as written, with `Cx` itself in the constructor
and `Cx`'s own constructors as the recursor's minor premises.
-/

namespace LocalParam

mumi_spec
inductive Cx (α : Type u) (n : Nat) : Type u where
  | mk : α → Cx α n
  | z : Cx α n

/--
error: (kernel) invalid nested inductive datatype 'MumiTests.Shapes.LocalParam.Cx', nested inductive datatypes parameters cannot contain local variables.
-/
#guard_msgs in
set_option mumi.enabled false in
inductive Stock where
  | tip : Stock
  | mk : (n : Nat) → Cx Stock n → Stock

mumi_spec (simp := [H.rec_mk, H.casesOn_mk])
inductive H where
  | tip : H
  | mk : (n : Nat) → Cx H n → H

/-! Nothing here is pretty-printed back into shape: the constructor really does
take a `Cx H n`. -/

/-- info: H.mk : (n : Nat) → Cx H n → H -/
#guard_msgs in
#check @H.mk

/--
info: @H.rec : {motive_1 : H → Sort u_1} →
  {motive_2 : (n : Nat) → Cx H n → Sort u_1} →
    motive_1 H.tip →
      ((n : Nat) → (a : Cx H n) → motive_2 n a → motive_1 (H.mk n a)) →
        ((n : Nat) → (a : H) → motive_1 a → motive_2 n (Cx.mk a)) → ((n : Nat) → motive_2 n Cx.z) → (t : H) → motive_1 t
-/
#guard_msgs in
#check @H.rec

def H.size : H → Nat :=
  H.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    0 (fun _ _ ih => ih) (fun _ _ ih => 1 + ih) (fun _ => 0)

example : H.size (H.mk 3 (Cx.mk H.tip)) = 1 := rfl

/-- info: 2 -/
#guard_msgs in
#eval H.size (H.mk 3 (Cx.mk (H.mk 0 (Cx.mk H.tip))))

/-- info: 'MumiTests.Shapes.LocalParam.H.size' does not depend on any axioms -/
#guard_msgs in
#print axioms H.size

end LocalParam

end MumiTests.Shapes
