/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import MumiTests.Spec.Harness

/-!
# The recursor over the whole block, on denested blocks

`MumiTests.IndInd` covers the recursor over the whole block on blocks the writer
wrote as a `mutual`.  This is the same recursor on blocks nobody wrote: the ones
`Mumi.IndInd` builds by denesting, where the members are copies of types that
already exist and the recursor has to be restated over the originals before
anyone can use it.

The shape is the same in both places.  One motive per member, `Prop` members
included; one minor per constructor; and a `Prop` motive takes *the value the
recursion produced* at the data member it is indexed by, so that a recursion can
rebuild a value and carry the proofs about it along.  That last part is what
makes the difference between a recursor one can define a map with and one that
gets stuck: with motives only for the data members, the minor for a
`mk (x : T) (h : P x)` is handed a proof about the *original* `x` and asked for
one about whatever the recursion built, and there is nothing to make that step
with.

Each section below is one shape a denesting can come out in.  The ones that do
not get the recursor over the whole block say why, and pin the split recursors
they get instead.
-/

/-! ## Abstract universes, and two parameters

Both parameters of the nesting type get carried into every copy, and the block
lands in the universe the writer's own type was declared in, whatever that is.
-/

namespace Univ

mumi_spec
inductive Lbl (α : Type u) (β : Type v) : Type (max u v) where
  | tip (a : α)
  | bin (b : β) (l r : Lbl α β)

mumi_spec
inductive Lbl.Ord (α : Type u) (β : Type v) : Lbl α β → Prop where
  | tip (a : α) : Lbl.Ord α β (.tip a)
  | bin (b : β) (l r : Lbl α β) (hl : Lbl.Ord α β l) (hr : Lbl.Ord α β r) :
      Lbl.Ord α β (.bin b l r)

mumi_spec
inductive OLbl (α : Type u) (β : Type v) : Type (max u v) where
  | mk (x : Lbl α β) (h : x.Ord)

mumi_spec (unproven := [Nest.casesOn_mk]) (xfail := [rec, recOn, axioms])
inductive Nest (γ : Type w) : Type w where
  | leaf (c : γ)
  | mk (x : OLbl (Nest γ) γ)

-- `γ` stands in for both of `Lbl`'s parameters, and `Lbl.Ord`'s copy is indexed
-- by `Lbl`'s, which is what makes the denesting induction-inductive

namespace Nest

/-- A pair of leaves under a label, and the proof that it is ordered. -/
def pair {γ : Type w} (b : γ) (x y : Nest γ) : Nest γ :=
  .mk (.mk (.bin b (.tip x) (.tip y)) (.bin b (.tip x) (.tip y) (.tip x) (.tip y)))

/-- How many leaves there are. -/
def size {γ : Type w} : Nest γ → Nat :=
  Nest.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat) (motive_3 := fun _ => Nat)
    (motive_4 := fun _ _ _ => True)
    (fun _ => 1) (fun _ ih => ih) (fun _ _ ih _ => ih)
    (fun _ ih => ih) (fun _ _ _ ihl ihr => ihl + ihr)
    (fun _ _ => trivial) (fun _ _ _ _ _ _ _ _ _ => trivial)

def ex : Nest Nat := pair 7 (.leaf 1) (pair 8 (.leaf 2) (.leaf 3))

example : size ex = 3 := rfl

/-- info: 3 -/
#guard_msgs in
#eval size ex

/--
Rebuilding the tree, which needs `motive_4`.

The minor for `OLbl.mk` is handed `h`, a proof that the tree it was given is
ordered, and has to produce one about the tree the recursion built.  `motive_4`
says the rebuilt tree is ordered, and the two `Lbl.Ord` minors maintain it.
-/
def rebuild {γ : Type w} : Nest γ → Nest γ :=
  Nest.rec (motive_1 := fun _ => Nest γ) (motive_2 := fun _ => OLbl (Nest γ) γ)
    (motive_3 := fun _ => Lbl (Nest γ) γ)
    (motive_4 := fun _ ih _ => Lbl.Ord (Nest γ) γ ih)
    (fun c => .leaf c) (fun _ ih => .mk ih) (fun _ _ ih hord => .mk ih hord)
    (fun _ ih => .tip ih) (fun b _ _ ihl ihr => .bin b ihl ihr)
    (fun _ ih => .tip ih) (fun b _ _ _ _ ihl ihr hl hr => .bin b ihl ihr hl hr)

example : size (rebuild ex) = 3 := rfl

/-- info: 'Univ.Nest.rebuild' does not depend on any axioms -/
#guard_msgs in
#print axioms rebuild

end Nest

end Univ

/-! ## Two `Prop` members over one data member

Each of them gets a motive, and the minor for the constructor that carries both
proofs gets a hypothesis for each.  What the recursion computes at a value of
the data member is that value's image paired with *both* facts about it.
-/

namespace TwoProps

mumi_spec
inductive Chain (α : Type) where
  | nil
  | cons (a : α) (t : Chain α)

mumi_spec
inductive Chain.P (α : Type) : Chain α → Prop where
  | nil : Chain.P α .nil
  | cons (a : α) (t : Chain α) (h : Chain.P α t) : Chain.P α (.cons a t)

mumi_spec
inductive Chain.Q (α : Type) : Chain α → Prop where
  | nil : Chain.Q α .nil
  | cons (a : α) (t : Chain α) (h : Chain.Q α t) : Chain.Q α (.cons a t)

mumi_spec
inductive Good (α : Type) where
  | mk (c : Chain α) (h1 : c.P) (h2 : c.Q)

mumi_spec (unproven := [RecGood.casesOn_mk]) (xfail := [rec, recOn, axioms])
inductive RecGood where
  | mk (x : Good RecGood)

-- `motive_4` and `motive_5` are the two of them, and `Good.mk`'s minor asks for
-- one hypothesis apiece, both about the same computed value `c_ih`

namespace RecGood

def bottom : RecGood := .mk (.mk .nil .nil .nil)

def wrap (v : RecGood) : RecGood :=
  .mk (.mk (.cons v .nil) (.cons v .nil .nil) (.cons v .nil .nil))

/-- How many `RecGood`s are nested inside. -/
def depth : RecGood → Nat :=
  RecGood.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat) (motive_3 := fun _ => Nat)
    (motive_4 := fun _ _ _ => True) (motive_5 := fun _ _ _ => True)
    (fun _ ih => ih + 1) (fun _ _ _ ih _ _ => ih)
    0 (fun _ _ iha iht => iha + iht)
    trivial (fun _ _ _ _ _ _ => trivial)
    trivial (fun _ _ _ _ _ _ => trivial)

example : depth bottom = 1 := rfl
example : depth (wrap (wrap bottom)) = 3 := rfl

/-- Rebuilding, carrying both facts. -/
def rebuild : RecGood → RecGood :=
  RecGood.rec (motive_1 := fun _ => RecGood) (motive_2 := fun _ => Good RecGood)
    (motive_3 := fun _ => Chain RecGood)
    (motive_4 := fun _ ih _ => Chain.P RecGood ih)
    (motive_5 := fun _ ih _ => Chain.Q RecGood ih)
    (fun _ ih => .mk ih) (fun _ _ _ ih hp hq => .mk ih hp hq)
    .nil (fun _ _ iha iht => .cons iha iht)
    .nil (fun _ _ _ iha iht hp => .cons iha iht hp)
    .nil (fun _ _ _ iha iht hq => .cons iha iht hq)

example : depth (rebuild (wrap (wrap bottom))) = 3 := rfl

/-- info: 'TwoProps.RecGood.rebuild' does not depend on any axioms -/
#guard_msgs in
#print axioms rebuild

end RecGood

end TwoProps

/-! ## Infinitary fields, in the data member and in the `Prop` member

A constructor field of function type recurses once per argument, and so does the
hypothesis about it.  The `Prop` member's field `h : ∀ n, Fin (f n)` is the
interesting one: what the well-formedness of the erased block records at an
infinitary field is quantified, and the fact wanted at a particular `n` is that
one applied.
-/

namespace Infinitary

mumi_spec
inductive Br (α : Type) where
  | leaf
  | node (f : Nat → Br α) (a : α)

mumi_spec
inductive Br.Fin (α : Type) : Br α → Prop where
  | leaf : Br.Fin α .leaf
  | node (f : Nat → Br α) (a : α) (h : ∀ n, Br.Fin α (f n)) : Br.Fin α (.node f a)

mumi_spec
inductive FBr (α : Type) where
  | mk (b : Br α) (h : b.Fin)

mumi_spec (unproven := [RecBr.casesOn_mk]) (xfail := [rec, recOn, axioms])
inductive RecBr where
  | mk (x : FBr RecBr)

-- `Br.node`'s minor gets `(a : Nat) → motive_3 (f a)`, and `Fin.node`'s gets
-- `∀ n, motive_4 (f n) (f_ih n) ⋯`: the hypothesis about the branch at `n` is
-- about the value the recursion produced at that same `n`

namespace RecBr

def bottom : RecBr := .mk (.mk .leaf .leaf)

def wrap (v : RecBr) : RecBr :=
  .mk (.mk (.node (fun _ => .leaf) v) (.node (fun _ => .leaf) v (fun _ => .leaf)))

/-- How many `RecBr`s are nested inside, down the leftmost branch. -/
def depth : RecBr → Nat :=
  RecBr.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat) (motive_3 := fun _ => Nat)
    (motive_4 := fun _ _ _ => True)
    (fun _ ih => ih + 1) (fun _ _ ih _ => ih)
    0 (fun _ _ ihf iha => ihf 0 + iha)
    trivial (fun _ _ _ _ _ _ => trivial)

example : depth bottom = 1 := rfl
example : depth (wrap (wrap bottom)) = 3 := rfl

/-- Rebuilding, carrying `Br.Fin` through the infinitary field. -/
def rebuild : RecBr → RecBr :=
  RecBr.rec (motive_1 := fun _ => RecBr) (motive_2 := fun _ => FBr RecBr)
    (motive_3 := fun _ => Br RecBr)
    (motive_4 := fun _ ih _ => Br.Fin RecBr ih)
    (fun _ ih => .mk ih) (fun _ _ ih hf => .mk ih hf)
    .leaf (fun _ _ ihf iha => .node ihf iha)
    .leaf (fun _ _ _ ihf iha hf => .node ihf iha hf)

example : depth (rebuild (wrap (wrap bottom))) = 3 := rfl

-- the recursor over the whole block is stated over the *original* types, and
-- what carries a recursion across is the round trip between a copy and its
-- original.  Proving that round trip is the identity at an infinitary
-- constructor means proving `(fun n => toOrig (ofOrig (f n))) = f`, which is
-- `funext`, which is `Quot.sound`.  Nothing else in this file pays it
/-- info: 'Infinitary.RecBr.rebuild' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms rebuild

end RecBr

end Infinitary

/-! ## Two nesting families at once

A constructor may nest more than one family, and the two have nothing to do with
each other.  Each contributes its own data members and its own `Prop` member, so
the block has two data members carrying a proof and the recursor has a motive
for each of the seven members.
-/

namespace TwoFamilies

mumi_spec
inductive Tr (α : Type) where
  | tip
  | bin (l r : Tr α) (a : α)

mumi_spec
inductive Tr.Full (α : Type) : Tr α → Prop where
  | tip : Tr.Full α .tip
  | bin (l r : Tr α) (a : α) (hl : Tr.Full α l) (hr : Tr.Full α r) : Tr.Full α (.bin l r a)

mumi_spec
inductive FTr (α : Type) where
  | mk (t : Tr α) (h : t.Full)

mumi_spec
inductive Seq (α : Type) where
  | nil
  | cons (a : α) (t : Seq α)

mumi_spec
inductive Seq.NonEmpty (α : Type) : Seq α → Prop where
  | cons (a : α) (t : Seq α) : Seq.NonEmpty α (.cons a t)

mumi_spec
inductive NESeq (α : Type) where
  | mk (s : Seq α) (h : s.NonEmpty)

mumi_spec (unproven := [RecTwo.casesOn_mk]) (xfail := [rec, recOn, axioms])
inductive RecTwo where
  | tip
  | mk (x : FTr RecTwo) (y : NESeq RecTwo)

-- one motive per member of both families, `Tr.Full` and `Seq.NonEmpty` each
-- taking the value computed at the data member it indexes, and eleven minors

namespace RecTwo

-- spelled out: `.tip` alone is ambiguous between four of this block's members
def one : RecTwo :=
  RecTwo.mk
    (FTr.mk (Tr.bin Tr.tip Tr.tip RecTwo.tip)
      (Tr.Full.bin Tr.tip Tr.tip RecTwo.tip Tr.Full.tip Tr.Full.tip))
    (NESeq.mk (Seq.cons RecTwo.tip Seq.nil) (Seq.NonEmpty.cons RecTwo.tip Seq.nil))

/-- How many `RecTwo`s are inside. -/
def size : RecTwo → Nat :=
  RecTwo.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat) (motive_3 := fun _ => Nat)
    (motive_4 := fun _ _ _ => True) (motive_5 := fun _ => Nat) (motive_6 := fun _ => Nat)
    (motive_7 := fun _ _ _ => True)
    1 (fun _ _ ihx ihy => ihx + ihy)
    (fun _ _ ih _ => ih)
    0 (fun _ _ _ ihl ihr iha => ihl + ihr + iha)
    trivial (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ ih _ => ih)
    0 (fun _ _ iha iht => iha + iht)
    (fun _ _ _ _ => trivial)

example : size one = 2 := rfl

/-- Rebuilding, carrying both families' proofs. -/
def rebuild : RecTwo → RecTwo :=
  RecTwo.rec (motive_1 := fun _ => RecTwo) (motive_2 := fun _ => FTr RecTwo)
    (motive_3 := fun _ => Tr RecTwo)
    (motive_4 := fun _ ih _ => Tr.Full RecTwo ih)
    (motive_5 := fun _ => NESeq RecTwo) (motive_6 := fun _ => Seq RecTwo)
    (motive_7 := fun _ ih _ => Seq.NonEmpty RecTwo ih)
    RecTwo.tip (fun _ _ ihx ihy => RecTwo.mk ihx ihy)
    (fun _ _ ih hf => FTr.mk ih hf)
    Tr.tip (fun _ _ _ ihl ihr iha => Tr.bin ihl ihr iha)
    Tr.Full.tip (fun _ _ _ _ _ ihl ihr iha hl hr => Tr.Full.bin ihl ihr iha hl hr)
    (fun _ _ ih hn => NESeq.mk ih hn)
    Seq.nil (fun _ _ iha iht => Seq.cons iha iht)
    (fun _ _ iha iht => Seq.NonEmpty.cons iha iht)

example : size (rebuild one) = 2 := rfl

/-- info: 'TwoFamilies.RecTwo.rebuild' does not depend on any axioms -/
#guard_msgs in
#print axioms rebuild

end RecTwo

end TwoFamilies

/-! ## A `Prop` member indexed by two data values

Not one of the ones that gets the recursor over the whole block, and the reason
is the recursion's shape rather than an oversight.  What the recursion computes
at a value of a data member is that value's image paired with the facts about
it, and a relation between two values is not a fact about either one: at the
first of them the second is not being recursed on and its image is not there to
state the relation with.

So the split recursors are what this block gets: a motive for each data member
and nothing for `Rel`, which is still perfectly usable for everything that does
not have to rebuild the relation.
-/

namespace Relation

mumi_spec
inductive Lst (α : Type) where
  | nil
  | cons (a : α) (t : Lst α)

mumi_spec
inductive Rel (α : Type) : Lst α → Lst α → Prop where
  | nil : Rel α .nil .nil
  | cons (a b : α) (s t : Lst α) : Rel α s t → Rel α (.cons a s) (.cons b t)

mumi_spec
inductive RelPair (α : Type) where
  | mk (s t : Lst α) (h : Rel α s t)

mumi_spec (unproven := [RecRel.casesOn_mk]) (xfail := [rec, recOn, axioms])
inductive RecRel where
  | mk (x : RelPair RecRel)

namespace RecRel

def bottom : RecRel := .mk (.mk .nil .nil .nil)

def wrap (v : RecRel) : RecRel := .mk (.mk (.cons v .nil) (.cons v .nil) (.cons v v .nil .nil .nil))

/-- The split recursors still compute. -/
def depth : RecRel → Nat :=
  RecRel.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat) (motive_3 := fun _ => Nat)
    (fun _ ih => ih + 1) (fun _ _ _ ihs iht => ihs + iht)
    0 (fun _ _ iha iht => iha + iht)

example : depth bottom = 1 := rfl
-- both sides of the relation get recursed on, so a wrap doubles the count
example : depth (wrap (wrap bottom)) = 7 := rfl

/-- info: 'Relation.RecRel.depth' does not depend on any axioms -/
#guard_msgs in
#print axioms depth

end RecRel

end Relation

/-! ## A `Prop` constructor that pins a data field

The other shape that does not get the recursor over the whole block.  What
proves the fact a recursion carries about a rebuilt value is an inversion, which
unifies the `Prop` constructor's index against the data constructor the
recursion is at.  `Short.cons`'s index is `.cons a .nil`, so the unification
does not just name the tail, it *pins* it -- and the recursion, which has a call
at the tail, is left with a call at `.nil`, which is not a term it is recursing
on.

An index that is a variable, or a constructor at fields of its own, is fine; it
is the pinning that is not.  `set_option trace.Mumi.indind true` says so.
-/

namespace Pinned

mumi_spec
inductive Chain (α : Type) where
  | nil
  | cons (a : α) (t : Chain α)

mumi_spec
inductive Chain.Short (α : Type) : Chain α → Prop where
  | nil : Chain.Short α .nil
  | cons (a : α) : Chain.Short α (.cons a .nil)

mumi_spec
inductive Good (α : Type) where
  | mk (c : Chain α) (h : c.Short)

/--
trace: [Mumi.indind] no recursor over the whole block: `Pinned.RecShort.nested_Short_3.cons` is a constructor of `Pinned.RecShort.nested_Short_3` at
      RecShort.nested_Chain_2.cons a RecShort.nested_Chain_2.nil
    which pins a field of `Pinned.RecShort.nested_Chain_2` rather than naming one.  The recursion over the whole block would then have to compute at that term, which is not one it is recursing on.
[Mumi.indind] no course-of-values recursion for `Pinned.RecShort`: (kernel) application type mismatch
      F (RecShort.mk x) PUnit.unit
    argument has type
      PUnit
    but function has type
      @RecShort._sub.below motive (RecShort.mk x) → motive (RecShort.mk x)
-/
#guard_msgs(whitespace := lax) in
set_option trace.Mumi.indind true in
inductive RecShort where
  | mk (x : Good RecShort)

/--
info: @RecShort.rec : {motive_1 : RecShort → Sort u_1} →
  {motive_2 : Good RecShort → Sort u_1} →
    {motive_3 : Chain RecShort → Sort u_1} →
      ((x : Good RecShort) → motive_2 x → motive_1 (RecShort.mk x)) →
        ((c : Chain RecShort) → (h : Chain.Short RecShort c) → motive_3 c → motive_2 (Good.mk c h)) →
          motive_3 Chain.nil →
            ((a : RecShort) → (t : Chain RecShort) → motive_1 a → motive_3 t → motive_3 (Chain.cons a t)) →
              (t : RecShort) → motive_1 t
-/
#guard_msgs in
#check @RecShort.rec

namespace RecShort

def bottom : RecShort := .mk (.mk .nil .nil)

def wrap (v : RecShort) : RecShort := .mk (.mk (.cons v .nil) (.cons v))

def depth : RecShort → Nat :=
  RecShort.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat) (motive_3 := fun _ => Nat)
    (fun _ ih => ih + 1) (fun _ _ ih => ih)
    0 (fun _ _ iha iht => iha + iht)

example : depth (wrap (wrap bottom)) = 3 := rfl

/-! Injectivity is a separate question from the recursor, and it does come out
here, through all three copies: `Good`'s own field is at the copy of `Chain`,
and the proof beside it is at the copy of `Short`, whose type moves when the
chain under it does.  That last step is `proof_irrel_heq`, and what the writer
is left with is stated at the originals. -/

/-- info: mk.injEq : ∀ (x x_1 : Good RecShort), (mk x = mk x_1) = (x = x_1) -/
#guard_msgs(whitespace := lax) in
#check @RecShort.mk.injEq

example (x y : Good RecShort) (h : RecShort.mk x = RecShort.mk y) : x = y := by
  simp at h; exact h

/-- info: 'Pinned.RecShort.mk.injEq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms RecShort.mk.injEq

end RecShort

end Pinned

/-! ## A nesting type that is one member of a mutual family

`Chain.Even` and `Chain.Odd` are declared together, so a copy of one is no use
without a copy of the other: denesting specialises the whole family, and the
two copies come back as a single group, each `ofOrig` going through the
family's own recursor rather than calling its sibling.
-/

namespace MutualProp

mumi_spec
inductive Chain (α : Type) where
  | nil
  | cons (a : α) (t : Chain α)

mumi_spec
mutual
inductive Chain.Even (α : Type) : Chain α → Prop where
  | nil : Chain.Even α .nil
  | cons (a : α) (t : Chain α) : Chain.Odd α t → Chain.Even α (.cons a t)
inductive Chain.Odd (α : Type) : Chain α → Prop where
  | cons (a : α) (t : Chain α) : Chain.Even α t → Chain.Odd α (.cons a t)
end

mumi_spec
inductive EChain (α : Type) where
  | mk (c : Chain α) (h : c.Even)

mumi_spec (unproven := [RecEven.casesOn_mk]) (xfail := [rec, recOn, axioms])
inductive RecEven where
  | mk (x : EChain RecEven)

-- `Chain.Odd` is nowhere in the declaration, and it still gets a motive: it is
-- what the hypothesis for the `Even.cons` case is about

-- the sibling's bridge is stated over the sibling's own original
/--
info: @RecEven.nested_Odd_4.ofOrig : ∀ {a : Chain RecEven},
  Chain.Odd RecEven a → RecEven.nested_Odd_4 (RecEven.nested_Chain_2.ofOrig a)
-/
#guard_msgs in
#check @RecEven.nested_Odd_4.ofOrig

namespace RecEven

def bottom : RecEven := .mk (.mk .nil .nil)

-- `Chain.Odd .nil` has no proof, so a chain grows two at a time
def wrap (v : RecEven) : RecEven :=
  .mk (.mk (.cons v (.cons v .nil)) (.cons v (.cons v .nil) (.cons v .nil .nil)))

def depth (t : RecEven) : Nat :=
  RecEven.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat) (motive_3 := fun _ => Nat)
    (motive_4 := fun _ _ _ => True) (motive_5 := fun _ _ _ => True)
    (fun _ ih => ih + 1) (fun _ _ ih _ => ih)
    0 (fun _ _ iha iht => iha + iht)
    trivial (fun _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial) t

example : depth bottom = 1 := rfl

/-- info: 7 -/
#guard_msgs in
#eval depth (wrap (wrap bottom))

-- no index of a `Prop` copy lands in a data member, so nothing needs `propext`
/-- info: 'MutualProp.RecEven.depth' does not depend on any axioms -/
#guard_msgs in
#print axioms depth

end RecEven

end MutualProp

/-! ## What is not rescued

A block that stays Lean's error.  `set_option trace.Mumi.rescue true` says why
each retry did not take; without it the declaration reads exactly as it would
if the library were not imported.

The lowering erases proof fields and keeps data ones; a field that mentions the
block to the left of an arrow is neither, so there is nothing to erase it to.
The block is not one Lean would have taken either, and it stays rejected.
-/

namespace Negative

mumi_spec
inductive NegT (α : Type) where
  | mk : (α → Nat) → NegT α

mumi_spec
inductive NegT.Ok (α : Type) : NegT α → Prop where
  | mk (f : α → Nat) : NegT.Ok α (.mk f)

mumi_spec
inductive OkNeg (α : Type) where
  | mk (x : NegT α) (h : x.Ok)

/-- error: (kernel) unknown constant 'Negative.RecNeg' -/
#guard_msgs in
inductive RecNeg where
  | mk (x : OkNeg RecNeg)

end Negative
