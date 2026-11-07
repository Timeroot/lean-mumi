/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import MumiTests.Spec.Harness

/-!
# A tour of the whole surface

Every block below is a `mutual` (or a nested `inductive`) that Lean on its own
either rejects or gets wrong, written out with what the library gives back for
it: the constructors and their types, the recursors and their types, what
reduces by `rfl` and what `decide` will close, what compiles and runs, and what
`cases` and `match` can and cannot do with it.  Where something is missing it is
here as a pinned error rather than as a sentence, so that the day it starts
working this file says so.

Each section ends its opening paragraph with a verdict, one of five:

* *works* -- the declarations are there and have the types they would have had
  if the kernel had taken the block directly.
* *works, with a caveat* -- the block goes through and computes, but something
  about it reads differently, or costs an axiom, or is missing a lemma.
* *rejected, not yet* -- nothing about Lean's kernel or this lowering rules it
  out; there is simply no case for it.
* *rejected, no known way* -- the obstruction is in the kernel or in the
  encoding, and we do not know how to remove it.
* *rejected, a different theory* -- what is being asked for is not this
  extension of Lean but another one, with its own proof-theoretic strength.

Nothing here is *unsound*, and one section says why the nearest thing to it
would be.

Extra declarations live in these namespaces -- pre-types, wrappers, well-
formedness predicates, views, and the eliminators that `induction`, `cases` and
the equation compiler are driven by.  Their names are not ones Lean would have
chosen, so nothing here pins them or asks a writer to type them.  What is pinned
is that the names a writer *does* reach for are there with the types they should
have, and that the tactics standing on the rest behave.
-/

namespace MumiTests.Demo

/-! ## 1. Two members in different universes

A `Prop` and a `Type` in one `mutual`.  The kernel refuses this outright --
*mutually inductive types must live in the same universe* -- and the library
lowers the block into declarations it does accept.  What comes back reads as
the block written: the data member is a genuine inductive behind its name, so
`match`, `cases` and the code generator work on it as on any other, and every
member's `rec` is the block's, one motive per member, as Lean's own `mutual`
would have it.

*Verdict: works.* -/

namespace Hetero

mumi_spec
mutual
/-- A tree, in `Type`, with one field at the proposition beside it. -/
inductive Tree : Type where
  | leaf (n : Nat) : Tree
  | node (l r : Tree) : Tree
  | wrap (h : Hidden) : Tree
/-- A proposition, in `Prop`, holding a tree. -/
inductive Hidden : Prop where
  | mk (t : Tree) : Hidden
end

/-! Both members print as the inductives they were written as. -/

/--
info: inductive MumiTests.Demo.Hetero.Tree : Type
number of parameters: 0
constructors:
MumiTests.Demo.Hetero.Tree.leaf : Nat → Tree
MumiTests.Demo.Hetero.Tree.node : Tree → Tree → Tree
MumiTests.Demo.Hetero.Tree.wrap : Hidden → Tree
-/
#guard_msgs in
#print Tree

/-! `Tree.rec` is the block's: a motive for the tree and one for the proposition,
and a minor premise for every constructor of either. -/

/-! `match` and `cases` work, because there is nothing in the way of them.  A
`wrap` gives back nothing: its field is a proof and the result is data. -/

def size : Tree → Nat
  | .leaf _ => 1
  | .node l r => size l + size r
  | .wrap _ => 0

example : size (.node (.leaf 1) (.leaf 2)) = 2 := rfl
example (h : Hidden) : size (.wrap h) = 0 := rfl
example : size (.node (.leaf 1) (.leaf 2)) = 2 := by decide

/-- info: 2 -/
#guard_msgs in
#eval size (.node (.leaf 1) (.leaf 2))

/-! `cases` on the proposition, and `induction` on the tree, with the block's own
constructor names as the cases. -/

example (h : Hidden) : True := by cases h; trivial

example (t : Tree) : 0 ≤ size t := by
  induction t with
  | leaf n => simp [size]
  | node l r ihl ihr => simp
  | wrap h => simp [size]

/-- info: 'MumiTests.Demo.Hetero.size' does not depend on any axioms -/
#guard_msgs in
#print axioms size

end Hetero

/-! ## 2. Data members two universes apart

The same lifting, with no `Prop` in sight: `Small` is in `Type` and `Large` in
`Type 2`.  The rule that is lifted is the one about the *members* of a block
agreeing.  The rule underneath it stands, and the second block here is it: two
data members that recurse into *one another* put each universe at or below the
other, so a cycle makes them equal and nothing can lift that.

*Verdict: works, and the cycle is rejected, no known way.* -/

namespace TwoUniverses

mumi_spec
mutual
inductive Small : Type where
  | z : Small
  | s (m : Small) : Small
inductive Large : Type 2 where
  | of (m : Small) : Large
  | ty (α : Type 1) : Large
  | pair (a b : Large) : Large
end

def depth : Large → Nat
  | .of _ => 0
  | .ty _ => 0
  | .pair a b => max (depth a) (depth b) + 1

example : depth (.pair (.of .z) (.ty (ULift Nat))) = 1 := rfl

/-- info: 1 -/
#guard_msgs in
#eval depth (.pair (.of .z) (.ty (ULift Nat)))

/-! `induction` over the member two universes up, and `cases` over the one
below it. -/

example (a : Large) : 0 ≤ depth a := by
  induction a with
  | of m => simp [depth]
  | ty α => simp [depth]
  | pair a b iha ihb => simp

example (m : Small) : m = .z ∨ ∃ k, m = .s k := by
  cases m with
  | z => exact .inl rfl
  | s k => exact .inr ⟨k, rfl⟩

/-! Now the cycle.  `Cyc1` holds a `Cyc2` and `Cyc2` holds a `Cyc1`, so each
universe is at or below the other and they have to agree; the report names the
two members and the rule that did survive. -/

/--
error: Invalid universe level in constructor `MumiTests.Demo.TwoUniverses.Cyc1.mk`: Parameter `b` has type
  Cyc2
at universe level
  2
which is not less than or equal to the inductive type's resulting universe level
  1

Hint: The data members `MumiTests.Demo.TwoUniverses.Cyc1` and `MumiTests.Demo.TwoUniverses.Cyc2` live in different universes, `Type` and `Type 1`.  Lowering the erased pre-block into ordinary inductives is what lifts the kernel's same-universe rule, and here it did not go through:
  (kernel) mutually inductive types must live in the same universe

Note: What the lowering lifts is the rule that the *members* of a mutual block agree about their universe.  The two rules underneath it stand: members that recurse into one another have to agree anyway -- an edge puts one universe at or below the other, so a cycle makes them equal -- and a field still has to fit inside the member it belongs to.  `X._pre` above is the erased form of `X`
-/
#guard_msgs in
mutual
inductive Cyc1 : Type where
  | mk (b : Cyc2) : Cyc1
inductive Cyc2 : Type 1 where
  | mk (a : Cyc1) : Cyc2
  | ty (α : Type) : Cyc2
end

end TwoUniverses

/-! ## 3. Induction-induction

One member's *arity* mentions another: `Ty` is indexed by `Ctx`, and `Ctx`'s
second constructor holds a `Ty`.  Lean cannot even elaborate this, since it
elaborates every arity before any member is in scope.

The encoding erases the block-typed index, so a member is a subtype of an erased
pre-type and its constructors are `def`s rather than kernel constructors.  Most
of what that would cost is bought back: the types read as written, the recursors
are the ones the block should have, `match` goes through a view, recursion is
structural, and the constructors get their injectivity lemmas.  Three things are
genuinely gone, and they are pinned at the end of this section.

*Verdict: works, with a caveat.* -/

namespace IndInd

mumi_spec
mutual
inductive Ctx : Type where
  | nil : Ctx
  | snoc (Γ : Ctx) (A : Ty Γ) : Ctx
inductive Ty : Ctx → Type where
  | base (Γ : Ctx) : Ty Γ
  | arr (Γ : Ctx) (A : Ty Γ) (B : Ty (.snoc Γ A)) : Ty Γ
end

/-! The member is a definition, and so is each constructor -- but the *types*
are the ones written above. -/

/--
info: def MumiTests.Demo.IndInd.Ctx : Type :=
Ctx._sub
-/
#guard_msgs in
#print Ctx

/-! `Ctx.rec` is the whole block's, with a motive per member, which is what an
induction-inductive block has instead of one recursor each.  The tactics are
driven off principles cut out of it, further down. -/

/-! `match` works, through a view the rewrite puts in the way, and the
recursion it produces is structural: no `WellFounded.fix`, so the equations hold
by `rfl` and the kernel will run them. -/

def len : Ctx → Nat
  | .nil => 0
  | .snoc Γ _ => len Γ + 1

/--
info: def MumiTests.Demo.IndInd.len : Ctx → Nat :=
fun x => Ctx._sub.brecOn x len._f
-/
#guard_msgs in
#print len

example : len .nil = 0 := rfl
example (Γ : Ctx) (A : Ty Γ) : len (Γ.snoc A) = len Γ + 1 := rfl
example : len (.snoc .nil (.base .nil)) = 1 := by decide

/-- info: 1 -/
#guard_msgs in
#eval len (.snoc .nil (.base .nil))

/-- info: 'MumiTests.Demo.IndInd.len' does not depend on any axioms -/
#guard_msgs in
#print axioms len

/-! Recursion over the indexed member too, as long as it stays at the index it
was given.  `A` is at `Ty Γ`, the same context the whole term is at, so this one
is structural exactly as `len` was. -/

def dom {Γ : Ctx} : Ty Γ → Nat
  | .base _ => 1
  | .arr _ A _ => dom A + 1

/--
info: def MumiTests.Demo.IndInd.dom : {Γ : Ctx} → Ty Γ → Nat :=
fun {Γ} x => Ty._sub.brecOn x dom._f
-/
#guard_msgs in
#print dom

example (Γ : Ctx) : dom (Ty.base Γ) = 1 := rfl
example (Γ A B) : dom (Ty.arr Γ A B) = dom A + 1 := rfl
example : dom (Ty.arr .nil (.base .nil) (.base _)) = 2 := by decide

/-- info: 2 -/
#guard_msgs in
#eval dom (Ty.arr .nil (.base .nil) (.base _))

/-! `B` is at `Ty (Γ.snoc A)`, a *different* context, and the table a structural
recursion runs on is built with the context held fixed.  So a definition that
descends into `B` is well-founded instead: it elaborates and runs, but its
equations are theorems rather than `rfl`, and it costs the two axioms
well-founded recursion costs.  Section 6 is this obstruction on its own. -/

def tsize {Γ : Ctx} : Ty Γ → Nat
  | .base _ => 1
  | .arr _ A B => tsize A + tsize B + 1

/-- info: 'MumiTests.Demo.IndInd.tsize' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tsize

/--
error: Type mismatch
  rfl
has type
  ?m.6 = ?m.6
but is expected to have type
  tsize (Ty.base Γ) = 1
-/
#guard_msgs in
example (Γ : Ctx) : tsize (Ty.base Γ) = 1 := rfl

example (Γ : Ctx) : tsize (Ty.base Γ) = 1 := by simp [tsize]

/-- info: 3 -/
#guard_msgs in
#eval tsize (Ty.arr .nil (.base .nil) (.base _))

/-! The tactics work on either member, with the block's own constructor names as
the cases and an induction hypothesis at the recursive field. -/

def len' : Ctx → Nat
  | .nil => 0
  | .snoc Γ _ => len' Γ + 1

example (Γ : Ctx) : len Γ = len' Γ := by
  induction Γ with
  | nil => rfl
  | snoc Δ A ih => simp [len, len', ih]

example (Γ : Ctx) (A : Ty Γ) : 1 ≤ dom A := by
  cases A with
  | base _ => simp [dom]
  | arr _ A B => simp [dom]

/-! `Ctx.casesOn` and `Ctx.recOn` are there under the names an `inductive`
answers to, so `using` names the same cases, and a case split written as a term
still compiles. -/

example (Γ : Ctx) : Nat := by
  induction Γ using Ctx.casesOn with
  | nil => exact 0
  | snoc Δ A => exact len Δ + 1

def isNil (Γ : Ctx) : Bool :=
  Ctx.casesOn (motive_1 := fun _ => Bool) Γ true (fun _ _ => false)

/-- info: false -/
#guard_msgs in
#eval isNil (Ctx.snoc .nil (.base .nil))

/-! Injectivity is a theorem and a `@[simp]` lemma, stated the way an ordinary
constructor's is -- the dependent field compared with `HEq`. -/

example (Γ : Ctx) (A : Ty Γ) : Ctx.snoc Γ A ≠ .nil := by simp

/-! `noConfusion` is stated about the member, and says what an ordinary
constructor's does: the same constructor twice compares the fields, two
different ones prove anything. -/

/--
info: @Ctx.noConfusion : {P : Sort u_1} → {t t' : Ctx} → t = t' → Ctx.noConfusionType P t t'
-/
#guard_msgs in
#check @Ctx.noConfusion

example (Γ Δ : Ctx) (A : Ty Γ) (B : Ty Δ) (P : Sort u) :
    Ctx.noConfusionType P (Γ.snoc A) (Δ.snoc B) = ((Γ = Δ → A ≍ B → P) → P) := rfl

example (Γ : Ctx) (A : Ty Γ) (h : Ctx.nil = Ctx.snoc Γ A) : False := Ctx.noConfusion h

/-! `injection` and `contradiction` reduce the type in hand until they reach an inductive,
and what they reach is the wrapper, so `Mumi.CtorTactics` looks first at an equation between
two constructors of a member. -/

example (Γ Δ : Ctx) (A : Ty Γ) (B : Ty Δ) (h : Ctx.snoc Γ A = Ctx.snoc Δ B) : Γ = Δ := by
  injection h

example (Γ Δ : Ctx) (A : Ty Γ) (B : Ty Δ) (h : Ctx.snoc Γ A = Ctx.snoc Δ B) : Γ = Δ :=
  (Ctx.snoc.inj h).1

example (Γ : Ctx) (A : Ty Γ) (h : Ctx.nil = Ctx.snoc Γ A) : False := by contradiction

example (Γ : Ctx) (A : Ty Γ) (h : Ctx.nil = Ctx.snoc Γ A) : False := by simp at h

/-! A view presents one constructor and stops, so a constructor written inside
another pattern is taken apart by a `match` of its own, which the rewrite writes. -/

def twoDeep : Ctx → Nat
  | .snoc (.snoc Δ _) _ => len Δ + 10
  | .snoc .nil _ => 1
  | .nil => 0

/-- info: 10 -/
#guard_msgs in
#eval twoDeep (.snoc (.snoc .nil (.base .nil)) (.base _))

end IndInd

/-! ## 4. A proposition over the block

The shape the encoding was written for: data, and a judgement about the data in
`Prop`.  The proposition gets a place in the block's recursor, where its motive
may mention the value the data recursion produced, and `induction` and `cases`
work on a proof of it.  The motive lands in `Prop`; section 9 is about why.

*Verdict: works.* -/

namespace Judgement

mumi_spec
mutual
inductive Ctx : Type where
  | nil : Ctx
  | snoc (Γ : Ctx) (A : Ty Γ) : Ctx
inductive Ty : Ctx → Type where
  | base (Γ : Ctx) : Ty Γ
inductive Ok : Ctx → Prop where
  | nil : Ok .nil
  | snoc (Γ : Ctx) (A : Ty Γ) (h : Ok Γ) : Ok (.snoc Γ A)
end

/-! `Ok.rec` is the whole block's, and `motive_3` there takes the value the data
recursion produced as well as the proof.  So a proposition here can say
something about what the recursion over `Ctx` returned, which is strictly more
than a recursion over the propositions alone can state.  Section 8 is a block
that loses it. -/

/-! `induction` and `cases` work on a proof, with the constructor names the
block was written with.  A proof can also be had the other way round, by
structural recursion over the *data* member. -/

theorem ok_nil_or_snoc (Γ : Ctx) (h : Ok Γ) : Γ = .nil ∨ ∃ Δ A, Γ = .snoc Δ A := by
  cases h with
  | nil => exact .inl rfl
  | snoc Δ A _ => exact .inr ⟨Δ, A, rfl⟩

theorem ok_of_ok (Γ : Ctx) (h : Ok Γ) : Ok Γ := by
  induction h with
  | nil => exact .nil
  | snoc Δ A _ ih => exact .snoc Δ A ih

/-- Every context in this block happens to be well formed, and the proof is a
structural recursion over the data member. -/
theorem always_ok : ∀ Γ : Ctx, Ok Γ
  | .nil => .nil
  | .snoc Γ A => .snoc Γ A (always_ok Γ)

/-- info: 'MumiTests.Demo.Judgement.always_ok' does not depend on any axioms -/
#guard_msgs in
#print axioms always_ok

end Judgement

/-! ## 5. An index the erasure keeps

`KTy` carries two indices: a `KCtx`, which is block-typed and which the erasure
deletes, and a `Nat`, which is not and which survives into the pre-type.  A
deleted index becomes a parameter of the wrapper and can be held fixed; a kept
one is bound by the recursion, so the table a structural definition needs is
built with its motive generalised over everything downstream of it.  None of
that shows: the definition is structural, its equations hold by `rfl`, and it
brings in no axiom.

*Verdict: works.* -/

namespace KeptIndex

mumi_spec
mutual
inductive KCtx : Type where
  | nil : KCtx
  | snoc (Γ : KCtx) (A : KTy Γ 0) : KCtx
inductive KTy : KCtx → Nat → Type where
  | base (Γ : KCtx) (k : Nat) : KTy Γ k
  | arr (Γ : KCtx) (k : Nat) (A B : KTy Γ k) : KTy Γ k
end

def kDep {Γ : KCtx} {k : Nat} : KTy Γ k → Nat
  | .base _ _ => 0
  | .arr _ _ A B => max (kDep A) (kDep B) + 1

/--
info: def MumiTests.Demo.KeptIndex.kDep : {Γ : KCtx} → {k : Nat} → KTy Γ k → Nat :=
fun {Γ} {k} x => KTy._sub.brecOn x kDep._f
-/
#guard_msgs in
#print kDep

example (Γ k) : kDep (KTy.base Γ k) = 0 := rfl
example (Γ k A B) : kDep (KTy.arr Γ k A B) = max (kDep A) (kDep B) + 1 := rfl
example : kDep (KTy.arr .nil 2 (.base .nil 2) (.base .nil 2)) = 1 := by decide

/-- info: 1 -/
#guard_msgs in
#eval kDep (KTy.arr .nil 2 (.base .nil 2) (.base .nil 2))

/-- info: 'MumiTests.Demo.KeptIndex.kDep' does not depend on any axioms -/
#guard_msgs in
#print axioms kDep

end KeptIndex

/-! ## 6. A constructor that lands at another index

`up` concludes at `n + 1` from an argument at `n`.  The type is fine and the
constructor is fine; what is not fine is a *structural* recursion across it.
The table a structural definition runs on is built at fixed parameters of the
wrapper, and the kept index is one of them, so there is no row for a value at a
different one -- and no way to write the motive of a table that would have one,
because holding the index as an index rather than a parameter costs the wrapper
its structure eta, which is what makes the whole encoding definitional.

So such a definition falls back to well-founded recursion: it elaborates, it
compiles, it runs, `simp` proves its equations -- and `rfl` does not, because
`WellFounded.fix` is `@[irreducible]`, so `decide` cannot see through it either.

*Verdict: works, with a caveat -- and the caveat is no known way.* -/

namespace CrossIndex

mumi_spec
mutual
inductive UCtx : Type where
  | nil : UCtx
  | snoc (Γ : UCtx) (A : UTy 0 Γ) : UCtx
inductive UTy : Nat → UCtx → Type where
  | base (n : Nat) (Γ : UCtx) : UTy n Γ
  | wrap (n : Nat) (Γ : UCtx) (A : UTy n Γ) : UTy n Γ
  | up (n : Nat) (Γ : UCtx) (A : UTy n Γ) : UTy (n + 1) Γ
end

/-! Where the crossing call is the *only* recursion, there is something else to
descend on -- the `Nat` -- and Lean takes it, so this one is structural after
all. -/

def uUp {n : Nat} {Γ : UCtx} : UTy n Γ → Nat
  | .base _ _ => 0
  | .wrap _ _ _ => 0
  | .up _ _ A => uUp A + 1

/--
info: def MumiTests.Demo.CrossIndex.uUp : {n : Nat} → {Γ : UCtx} → UTy n Γ → Nat :=
fun {n} {Γ} x => Nat.brecOn (motive := fun {n} => UTy n Γ → Nat) n (@uUp._f Γ) x
-/
#guard_msgs in
#print uUp

example (n Γ A) : uUp (UTy.up n Γ A) = uUp A + 1 := rfl

/-! Put a same-index recursive call beside it and neither the index nor the
value is descended on by itself, so the definition is well-founded. -/

def uDep {n : Nat} {Γ : UCtx} : UTy n Γ → Nat
  | .base _ _ => 0
  | .wrap _ _ A => uDep A + 1
  | .up _ _ A => uDep A + 1

/-- info: 'MumiTests.Demo.CrossIndex.uDep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms uDep

/--
error: Type mismatch
  rfl
has type
  ?m.16 = ?m.16
but is expected to have type
  uDep (UTy.wrap n Γ A) = uDep A + 1
-/
#guard_msgs in
example (n Γ A) : uDep (UTy.wrap n Γ A) = uDep A + 1 := rfl

example (n Γ A) : uDep (UTy.wrap n Γ A) = uDep A + 1 := by simp [uDep]

/-- info: 2 -/
#guard_msgs in
#eval uDep (UTy.up 0 .nil (.wrap 0 .nil (.base 0 .nil)))

end CrossIndex

/-! ## 7. A proposition over two data members

`C` and `D` do not mention each other and `R` is indexed by both, so no two
members of the block depend on each other in a cycle.  The block separates and
Lean reads the three declarations in turn.  Each is an ordinary `inductive` with
its own recursor.  A `mutual` is still the right way to write it: Lean itself
refuses the block, because `R`'s arity names its siblings.

*Verdict: works.* -/

namespace TwoHosts

mumi_spec
mutual
inductive C : Type where
  | nil : C
  | cons (c : C) : C
inductive D : Type where
  | nil : D
inductive R : C → D → Prop where
  | nil : R .nil .nil
  | cons (c : C) (d : D) (h : R c d) : R c.cons d
end

/-- Its own recursion is the full one, so `induction` on a proof goes through. -/
theorem r_nil (c : C) (d : D) (h : R c d) : d = .nil := by
  induction h with
  | nil => rfl
  | cons _ _ _ ih => exact ih

/-- And so does `cases`. -/
theorem r_shape (c : C) (d : D) (h : R c d) : c = .nil ∨ ∃ k, c = .cons k := by
  cases h with
  | nil => exact .inl rfl
  | cons k _ _ => exact .inr ⟨k, rfl⟩

/-! And `C` is Lean's, with the one motive, so `induction` takes it without
`using`. -/

example (c : C) : c = c := by
  induction c with
  | nil => rfl
  | cons k ih => rfl

end TwoHosts

/-! ## 8. A `Prop` constructor that forgets a field

`Big.node` binds a `hs : List T` that its conclusion `Big (.node cs h)` says
nothing about.  Putting such a field back at its subtype would need a
well-formedness obligation to state it with, and a `Prop` constructor carries
none of its own -- it has only what its indices bring it, and this field is at
no index.

So `Big` stays out of the erasure.  It leaves the block as an ordinary inductive,
which nothing in the block mentions, and that is also why it costs nothing: the
recursion over `T` never needs `Big` to compute, so `T.rec` just takes `Big`'s motive
and minors as well, and `Big.rec` is Lean's recursor over `Big` into a motive at what
`T.rec` computes.  It has a hypothesis at every field, `hs_ih` included.  The control
at the end of the section is the same block with `hs` deleted, whose `Big.rec` has
the same shape.

The caveat is the one `T` brings with it, nesting through `List`: `T.rec`'s rules
hold by `simp` with their lemmas, not by `rfl`.  The types are as written, the data
member is untouched, and `induction` and `cases` work and bind the field, driving
Lean's own recursor, kept as `Big.induct`, which has no hypothesis at a datum.

*Verdict: works, with a caveat.* -/

namespace Forgotten

mumi_spec (simp := [T.casesOn_node, T.rec_node, T.rec_1_cons])
mutual
inductive T : Type where
  | node (cs : List T) (h : Ok cs) : T
  | leaf : T
inductive Ok : List T → Prop where
  | nil : Ok []
  | cons (t : T) (ts : List T) (h : Ok ts) : Ok (t :: ts)
inductive Big : T → Prop where
  | node (cs : List T) (hs : List T) (h : Ok cs) : Big (.node cs h)
  | leaf : Big .leaf
end

/-! `Big.rec` has a motive per target, and `hs` and `hs_ih` in the minor premise for
`Big.node`.  `Ok` did not forget anything and stays in the block. -/

/-! `induction` and `cases` reach for those, so both work on the member with the
forgotten field, and both bind it. -/

theorem Big.elim {t : T} (h : Big t) : t = .leaf ∨ ∃ cs, ∃ hc : Ok cs, t = .node cs hc := by
  induction h with
  | node cs hs hc => exact .inr ⟨cs, hc, rfl⟩
  | leaf => exact .inl rfl

/-! The data member computes as it always did. -/

def count : T → Nat
  | .leaf => 1
  | .node cs _ => cs.length

example : count .leaf = 1 := rfl

/-- info: 1 -/
#guard_msgs in
#eval count (.node [.leaf] (.cons .leaf [] .nil))

/-! The control: the same block with `hs` deleted, where `Big` stays in the block.
Its motive is the same either way: it takes `motive_1 a`, the value the recursion
over `T` produced, alongside the proof. -/

namespace Kept

mumi_spec (simp := [T.casesOn_node, T.rec_node, T.rec_1_cons])
mutual
inductive T : Type where
  | node (cs : List T) (h : Ok cs) : T
  | leaf : T
inductive Ok : List T → Prop where
  | nil : Ok []
  | cons (t : T) (ts : List T) (h : Ok ts) : Ok (t :: ts)
inductive Big : T → Prop where
  | node (cs : List T) (h : Ok cs) : Big (.node cs h)
  | leaf : Big .leaf
end

end Kept

end Forgotten

/-! ## 9. What a `Prop` member may eliminate into

A `Prop` member's recursion is the block's, so a use of it supplies a motive for
every member at once.  The `Prop` member's own motive there lands in `Prop` and
cannot be asked to land anywhere else.

This is the one place where the missing feature would be unsound rather than
merely absent.  Large elimination is granted to a single inductive on a
syntactic check -- one constructor, every field either a proof or an index --
and the check is about *that* inductive.  A joint recursor answers for a whole
block at once, and its data minor premises may consume the value the `Prop`
motive produced, so granting the `Prop` motive a `Type` would let a proof
determine data at every member of the block, subsingleton or not.  Per-member
large elimination on a joint recursor is unsound; it is refused, and this is
what the refusal reads like.

*Verdict: works as far as it is sound to, and further would be unsound.* -/

namespace PropElim

mumi_spec
mutual
inductive A : Prop where
  | mk (b : B) : A
inductive B : Type where
  | leaf (n : Nat) : B
  | fromA (a : A) : B
end

/-! The `Prop` member's motive is `A → Prop`; the data member's is `Sort u`. -/

/--
error: Type mismatch
  Nat
has type
  Type
of sort `Type 1` but is expected to have type
  Prop
of sort `Type`
-/
#guard_msgs in
example (a : A) : Nat :=
  A.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat)
    (fun _ ih => ih) (fun n => n) (fun _ ih => ih) a

/-! Into `Prop` it goes, and computes. -/

theorem a_holds (a : A) : A := A.rec (motive_2 := fun _ => True)
  (fun b _ => .mk b) (fun _ => trivial) (fun _ _ => trivial) a

/-- info: 'MumiTests.Demo.PropElim.a_holds' does not depend on any axioms -/
#guard_msgs in
#print axioms a_holds

/-! The data member's recursion is a genuine large elimination, and it reduces.
`B.rec` is the block's, as Lean's would be for a `mutual` block: a motive at
each member, so the field at the proposition carries a hypothesis too. -/

example : B.rec (motive_1 := fun _ => True) (motive_2 := fun _ => Nat)
    (fun _ _ => trivial) (fun n => n) (fun _ _ => 0) (.leaf 7) = 7 := rfl

/-! Written as the `match` a writer would write, it compiles and runs. -/

def tag : B → Nat
  | .leaf n => n
  | .fromA _ => 0

example : tag (.leaf 7) = 7 := rfl
example : tag (.fromA (.mk (.leaf 7))) = 0 := rfl

/-- info: 7 -/
#guard_msgs in
#eval tag (.leaf 7)

end PropElim

/-! ## 10. A nested inductive the kernel refuses

`Nonempty T` is a `Prop` and `T` is a `Type`, so specialising the nesting to the
block -- which is how the kernel handles a nested inductive at all -- produces
exactly the heterogeneous block of section 1.  The library rescues it, and the
copy of `Nonempty` that has to exist underneath is *equal* to the original by
`propext`, so it never has to be named: a coercion each way crosses between
them and a delaborator shows the original.

*Verdict: works.* -/

namespace NestProp

mumi_spec
inductive T : Type where
  | mk1 : T
  | mkT (h : Nonempty T) : T

/-! The constructor prints as one: the rescue went through the lowering, not
through the erasure, so behind `T` is an inductive. -/
/-- info: constructor MumiTests.Demo.NestProp.T.mkT : Nonempty T → T -/
#guard_msgs in
#print T.mkT

def two : T := T.mkT ⟨T.mk1⟩

/-- info: 'MumiTests.Demo.NestProp.two' does not depend on any axioms -/
#guard_msgs in
#print axioms two

def tag : T → Nat
  | .mk1 => 1
  | .mkT _ => 2

example : tag two = 2 := rfl
example : tag two = 2 := by decide

/-- info: 2 -/
#guard_msgs in
#eval tag two

end NestProp

/-! ## 11. A nested inductive whose copy is data

The same rescue where the nesting is a `Type` rather than a `Prop`.  Two
distinct data types can be isomorphic and no more, so the copy gets `toOrig`,
`ofOrig` and a coercion each way, but it keeps its own name in signatures.  That
name is the whole of the difference: values cross with the coercions, both
directions compile, and nothing costs an axiom.

*Verdict: works, with a caveat.* -/

namespace NestData

mumi_spec
mutual
inductive Box (α : Type u) : Type u where
  | mk (a : α) (p : BoxP α) : Box α
inductive BoxP (α : Type u) : Prop where
  | p : BoxP α
end

mumi_spec
mutual
inductive St : Type 1 where
  | tip : St
  | mk (w : Box St) : St
inductive Other : Type where
  | b : Other
end

/-! The field's type is what was written.  There is a copy of `Box St` behind it, which
is what the kernel was handed, and the recursor has motives for `Box St` and `BoxP St`. -/

/-- info: St.mk : Box St → St -/
#guard_msgs in
#check @St.mk

/-- info: St.nested_Box_1.toOrig : St.nested_Box_1 → Box St -/
#guard_msgs in
#check @St.nested_Box_1.toOrig

/-- info: St.nested_Box_1.ofOrig : Box St → St.nested_Box_1 -/
#guard_msgs in
#check @St.nested_Box_1.ofOrig

/-- The inner `match` is `Box`'s own. -/
def count : St → Nat
  | .tip => 0
  | .mk w => match (w : Box St) with | .mk _ _ => 1

/-- info: 1 -/
#guard_msgs in
#eval count (St.mk (.mk .tip .p))

/-- info: 'MumiTests.Demo.NestData.count' does not depend on any axioms -/
#guard_msgs in
#print axioms count

end NestData

/-! ## 12. `deriving`

A data member of an induction-inductive block *is* a subtype, so a handler that
wants constructors has nothing to look at.  The class is derived for the
pre-type, where the constructors are, and lifted onto the member.
`DecidableEq` and `Repr` come across that way -- which means `decide` works on
an equation between members, and `Repr` prints the pre-term, constructor names
and all.

The clause on the block is what does this.  A later, standalone
`deriving instance C for X` goes the way anything else that reduces a member's
type goes, and finds `Subtype`.

*Verdict: works, with a caveat.* -/

namespace Derive

mumi_spec
mutual
inductive DVec : Type where
  | nil : DVec
  | cons (v : DVec) (h : DOk v) : DVec
  deriving DecidableEq, Repr
inductive DOk : DVec → Prop where
  | nil : DOk .nil
end

/-- info: true -/
#guard_msgs in
#eval decide (DVec.nil = DVec.nil)

/-- info: false -/
#guard_msgs in
#eval decide (DVec.nil = DVec.cons DVec.nil DOk.nil)

example : DVec.nil ≠ DVec.cons DVec.nil DOk.nil := by decide

/-! `Repr` is written against the member, so what is shown is what was written: its
constructors under their names, and a proof field as `_`, as Lean's own has it. -/
/-- info: MumiTests.Demo.Derive.DVec.cons (MumiTests.Demo.Derive.DVec.nil) _ -/
#guard_msgs in
#eval repr (DVec.cons DVec.nil DOk.nil)

/-! A mutual induction-induction, with everything an ordinary inductive derives.  What the
pre-term erases, `Γ` here, is shown all the same. -/

namespace Everything

mutual
inductive Ctx : Type where
  | nil
  | snoc (Γ : Ctx) (A : Ty Γ)
  deriving Repr, BEq, DecidableEq, Inhabited, Hashable, Nonempty, Ord
inductive Ty : Ctx → Type where
  | base (Γ : Ctx) : Ty Γ
  | pi (Γ : Ctx) (A : Ty Γ) : Ty Γ
  deriving Repr, BEq, DecidableEq, Hashable
end

/--
info: MumiTests.Demo.Derive.Everything.Ctx.snoc
  (MumiTests.Demo.Derive.Everything.Ctx.nil)
  (MumiTests.Demo.Derive.Everything.Ty.base (MumiTests.Demo.Derive.Everything.Ctx.nil))
-/
#guard_msgs in
#eval Ctx.snoc .nil (.base .nil)
/-- info: true -/
#guard_msgs in
#eval Ctx.nil == Ctx.nil
/-- info: Ordering.eq -/
#guard_msgs in
#eval compare Ctx.nil Ctx.nil
/-- info: true -/
#guard_msgs in
#eval (default : Ctx) == .nil
example : Ctx.nil = Ctx.nil := by decide
example : Ctx.nil ≠ Ctx.snoc .nil (.base .nil) := by decide
example : Nonempty Ctx := inferInstance
example (Γ) : DecidableEq (Ty Γ) := inferInstance

end Everything

/-! Through a nesting: the copy's pre-type goes with the member's, and what is shown of the
field is the `List` it was written as. -/

namespace Through

mutual
inductive T (α : Type) : Type where
  | leaf (a : α)
  | node (cs : List (T α)) (h : Ok α cs)
  deriving Repr, BEq
inductive Ok (α : Type) : List (T α) → Prop where
  | nil : Ok α []
end

/-- info: MumiTests.Demo.Derive.Through.T.node [] _ -/
#guard_msgs in
#eval (T.node [] .nil : T Nat)
/-- info: true -/
#guard_msgs in
#eval (T.node [] .nil : T Nat) == T.node [] .nil

end Through

/--
error: failed to synthesize instance of type class
  Inhabited DVec._sub

Hint: Adding the command `deriving instance Inhabited for MumiTests.Demo.Derive.DVec._sub` may allow Lean to derive the missing instance.
---
error: Failed to delta derive `Inhabited` instance for `DVec`.

Note: Delta deriving tries the following strategies: (1) inserting the definition into each explicit non-out-param parameter of a class and (2) unfolding definitions further.
-/
#guard_msgs in
deriving instance Inhabited for DVec

end Derive

/-! ## 13. An index that binds before it reaches the block

The erasure deletes a block-typed index by replacing it with its pre-type, so
the index has to *be* a member applied to arguments.  `Nat → Ctx` is not one: it
binds an argument first, and there is no pre-type to state the whole of it at.

The erasure is only needed for a block whose members are genuinely simultaneous.
`Ctx` does not mention `Ty`, so this block separates and Lean reads the two
declarations in turn, which puts the index out of the erasure's reach entirely.

Add the back-edge and the rejection is there again.  Nothing about the kernel
rules it out: the erased index would be `Nat → Ctx._pre` and its well-formedness
the pointwise `∀ n, Ctx._wf (f n)`, both perfectly statable.  There is simply no
case for it in the erasure, and a recursion over such a block would want a table
indexed by a function.

*Verdict: works when the block separates, rejected when it does not.* -/

namespace FunIndex

mumi_spec
mutual
inductive Ctx : Type where
  | nil : Ctx
inductive Ty : (Nat → Ctx) → Type where
  | mk (f : Nat → Ctx) : Ty f
end

example (f : Nat → Ctx) (t : Ty f) : True := by
  cases t with
  | mk => trivial

/--
error: The index `a✝¹` of `MumiTests.Demo.FunIndex.TyC` binds arguments before reaching a member of the block, and the erasure has no pre-type to state it at:
  Nat → CtxC
-/
#guard_msgs in
mutual
inductive CtxC : Type where
  | nil : CtxC
  | snoc (f : Nat → CtxC) (A : TyC f) : CtxC
inductive TyC : (Nat → CtxC) → Type where
  | mk (f : Nat → CtxC) : TyC f
end

end FunIndex

/-! ## 14. Arities in a cycle

`P`'s arity mentions `Q` and `Q`'s mentions `P`.  A block-typed index is erased
to the *pre-type* of the member it mentions, so that member's own arity has to
be settled first, and the arities therefore have to admit an order.

Source order is not what supplies it.  A member's arity may name a member
declared later in the same block, as the first example below does; what a cycle
takes away is any order at all, and the block is rejected at whichever reference
closes it.  A member whose arity mentions *itself* is the same rejection with
one member.

This is the restriction that is left after the others are lifted, and it is not
a small one to want gone: an erasure that needs no order would have to erase
every member's indices at once against pre-types that do not exist yet.  We know
of none.

*Verdict: rejected, no known way.* -/

namespace CyclicArity

/-! Order alone is fine -- `T` is indexed by a `C` declared after it. -/

mumi_spec
mutual
inductive T : C → Type where
  | base (Γ : C) : T Γ
inductive C : Type where
  | nil : C
  | snoc (Γ : C) (A : T Γ) : C
end

/-! A cycle is not. -/

/-- error: Unknown identifier `P` -/
#guard_msgs in
mutual
inductive P : Q → Prop where
  | mk (q : Q) : P q
inductive Q : P → Prop where
  | mk (p : P) : Q p
end

/-! Neither is a member indexed by itself. -/

/-- error: Unknown identifier `S` -/
#guard_msgs in
inductive S : S → Prop where
  | mk (s : S) : S s

end CyclicArity

/-! ## 15. A data member at `Sort u`

A data member is encoded as a wrapper around its erased pre-type, and a wrapper
is a subtype, which lands one universe above `Prop`.  So the encoding needs to
know that the member is not a `Prop`, and `Sort u` does not say: for `u = 0` it
is one.  Lean refuses `inductive X : Sort u` for its own version of the same
reason, and the hint the library adds says which of the two is talking.

`imax` inside a *field* is fine; it is only the member's own universe that has
to be decidably not `Prop`.

*Verdict: rejected, no known way.* -/

namespace SortMember

universe u

/--
error: The data member `MumiTests.Demo.SortMember.C` lives at `Sort u`, which could still be `Prop`.  It is encoded as a wrapper around its pre-type, which lands one universe up from `Prop`, so a data member's universe has to be visibly non-zero -- `Type v` rather than `Sort v`
-/
#guard_msgs in
mutual
inductive C : Sort u where
  | nil : C
inductive T : C → Type where
  | mk (Γ : C) : T Γ
end

end SortMember

/-! ## 16. Induction-recursion

A type and a function *into* types, defined at the same time: `El` is used in
`U`'s own constructor.  This is not induction-induction with the arity written
differently -- it is Dybjer and Setzer's other scheme, and Lean's `mutual`
rejects the mixture of an `inductive` and a `def` before anything here is
consulted.

It is also the one place in this file where a large cardinal is the right thing
to talk about.  The proof-theoretic strength of induction-recursion is that of
`KPM`, Kripke-Platek set theory with a recursively Mahlo ordinal (Dybjer-Setzer,
*Induction-recursion and initial algebras*), where induction-induction is far
weaker and is interpretable in ordinary indexed inductive types.  What that does
*not* mean is that Lean cannot host it: Lean's universe hierarchy is stronger
than a recursively Mahlo ordinal by a wide margin, and a particular
induction-recursive universe can be encoded by hand.  What is missing is a
scheme -- a general erasure with the definitional equalities `El` should have --
and the reason to be careful about wanting one is Setzer's *external* Mahlo
universe, which is the genuinely stronger thing in this neighbourhood.

On this branch that scheme exists, as the experimental frontend in `Mumi/IR`:
Lean rejects the mixture first, and the block is then read as a universe and
its decoder.  The carrier lands one universe above where it was written unless
`mumi.mahlo` is set, and `Mumi/IR/README.md` says what that trades.

*Verdict: accepted, on the induction-recursion frontend.* -/

namespace IndRec

#guard_msgs in
mutual
inductive U : Type where
  | nat : U
  | pi (a : U) (b : El a → U) : U
def El : U → Type
  | .nat => Nat
  | .pi a b => (x : El a) → El (b x)
end

example (a : U) (b : El a → U) : El (U.pi a b) = ((x : El a) → El (b x)) := rfl

end IndRec

/-! ## 17. `Quot` at the head of a nesting

Denesting works by making a copy of the nesting type specialised to the block,
so the head of the nesting has to be an inductive: there has to be something to
specialise.  `Quot` is a primitive, and there is nothing to copy.

*Verdict: rejected, no known way.* -/

namespace QuotNest

/--
error: (kernel) arg #1 of 'MumiTests.Demo.QuotNest.Z.mk' contains a non valid occurrence of the datatypes being declared
-/
#guard_msgs in
inductive Z : Type where
  | mk (q : Quot (fun (_ _ : Z) => True)) : Z

end QuotNest

/-! ## Equations between constructors

Lean's tactics read an equation between constructors off the constructors, and here a
constructor is a definition unfolding to a wrapper's.  `Mumi.CtorTactics` gives
`contradiction`, `injection`, `cases` and `simp` what Lean's own have
(`MumiTests/Spec/SelfTest.lean`, its `Native` section), on each kind of encoded member,
with nothing internal in what they leave. -/

namespace CtorEqs

mutual
inductive Ctx : Type where
  | nil
  | snoc (Γ : Ctx) (A : Ty Γ)
inductive Ty : Ctx → Type where
  | base {Γ} : Ty Γ
  | pi {Γ} (A : Ty Γ) (B : Ty (.snoc Γ A)) : Ty Γ
end

example (Γ A) : Ctx.nil ≠ Ctx.snoc Γ A := by intro h; contradiction
example (Γ A) : Ctx.nil ≠ Ctx.snoc Γ A := by intro h; cases h
example (Γ A) : Ctx.nil ≠ Ctx.snoc Γ A := fun e => Ctx.noConfusion e
example (Γ A) : Ctx.nil ≠ Ctx.snoc Γ A := by simp
example (Γ Γ' A A') (e : Ctx.snoc Γ A = Ctx.snoc Γ' A') : Γ = Γ' := by
  injection e with h1 h2
example (Γ Γ' A A') (e : Ctx.snoc Γ A = Ctx.snoc Γ' A') : A ≍ A' := by
  injection e with h1 h2
example (Γ Γ' A A') (e : Ctx.snoc Γ A = Ctx.snoc Γ' A') : Γ = Γ' := by
  cases e; rfl

-- what `injection` leaves is about the fields
/--
error: unsolved goals
Γ Γ' : Ctx
A : Ty Γ
A' : Ty Γ'
h1 : Γ = Γ'
h2 : A ≍ A'
⊢ True ∧ True
-/
#guard_msgs in
example (Γ Γ' A A') (e : Ctx.snoc Γ A = Ctx.snoc Γ' A') : True ∧ True := by
  injection e with h1 h2

-- one equation deep inside another
example (Γ A B B') (e : Ctx.snoc (Ctx.snoc Γ A) B = Ctx.snoc (Ctx.snoc Γ A) B') : B = B' := by
  cases e; rfl

/-- info: 'MumiTests.Demo.CtorEqs.Ctx.noConfusion' does not depend on any axioms -/
#guard_msgs in
#print axioms Ctx.noConfusion

mutual
inductive T : Type where
  | leaf
  | node (cs : List T) (h : Ok cs)
inductive Ok : List T → Prop where
  | nil : Ok []
end

-- `h` is a proof, so `cs` is the one equation, as Lean has it
example (cs h) : T.leaf ≠ T.node cs h := by intro e; contradiction
example (cs h) : T.leaf ≠ T.node cs h := by intro e; cases e
example (cs h) : T.leaf ≠ T.node cs h := fun e => T.noConfusion e
example (a b h h') (e : T.node a h = T.node b h') : a = b := by
  injection e with h1
example (a b h h') (e : T.node a h = T.node b h') : a = b := by
  cases e; rfl
example (a b h h') (e : T.node a h = T.node b h') : a = b := T.node.inj e

-- induction-recursion, whose `X.ctorIdx` and measure come from the recursion
mutual
inductive U : Type where
  | base : U
  | pi (a : U) (b : El a → U) : U
def El : U → Type
  | .base => Nat
  | .pi a b => (x : El a) → El (b x)
end

example (x b) : U.base ≠ U.pi x b := by intro h; contradiction
example (x b) : U.base ≠ U.pi x b := by intro h; cases h
example (x b) : U.base ≠ U.pi x b := fun h => U.noConfusion h
example (x b) : U.base ≠ U.pi x b := by simp
example (x x' b b') (e : U.pi x b = U.pi x' b') : x = x' := by
  injection e with h1 h2
example (x x' b b') (e : U.pi x b = U.pi x' b') : x = x' := by
  cases e; rfl
example : U.ctorIdx .base = 0 := rfl

/-- info: U.pi.sizeOf_spec : ∀ (a : U) (b : El a → U), sizeOf (a.pi b) = 1 + sizeOf a -/
#guard_msgs in
#check @U.pi.sizeOf_spec

-- at one constructor `U`'s `noConfusion` offers its fields' equations, through its view
example (P : Sort _) (x x' b b') : U.noConfusionType P (U.pi x b) (U.pi x' b') = ((x = x' → b ≍ b' → P) → P) := rfl

/-! ### The other ways into such an equation

Each goes through as it does for Lean's own (`MumiTests/Spec/SelfTest.lean`).  The harness asks
these of every block; what follows is what it has no way of asking, needing a type of its own. -/

section Ways

-- `rfl` patterns against a variable are a substitution, which is Lean's
example (Γ A) (b : Ctx) (e : Ctx.snoc Γ A = b) : Ctx.snoc Γ A = b := by rcases e with rfl; rfl
example (Γ A) (b : Ctx) (e : Ctx.snoc Γ A = b) : Ctx.snoc Γ A = b := by obtain rfl := e; rfl
-- and between two constructors are the case split
example (Γ Δ A B) (e : Ctx.snoc Γ A = Ctx.snoc Δ B) : Γ = Δ := by rcases e with rfl; rfl
example (Γ Δ A B) (e : Ctx.snoc Γ A = Ctx.snoc Δ B) : Γ = Δ := by obtain rfl := e; rfl

-- what `injections` leaves is about the fields, not the wrapper
/--
error: unsolved goals
Γ Δ : Ctx
A : Ty Γ
B : Ty Δ
h1 : Γ = Δ
h2 : A ≍ B
⊢ True ∧ True
-/
#guard_msgs in
example (Γ Δ A B) (e : Ctx.snoc Γ A = Ctx.snoc Δ B) : True ∧ True := by
  injections h1 h2

-- too many names is said as Lean says it
/--
error: Tactic `injections` failed: too many identifiers provided, unused: [h3]

Γ Δ : Ctx
A : Ty Γ
B : Ty Δ
h1 : Γ = Δ
h2 : A ≍ B
⊢ True
-/
#guard_msgs in
example (Γ Δ A B) (e : Ctx.snoc Γ A = Ctx.snoc Δ B) : True := by
  injections h1 h2 h3

-- a mistake in an alternative is reported as that, not as an equation not solved
/--
error: Type mismatch
  1
has type
  Nat
of sort `Type` but is expected to have type
  Γ = Γ
of sort `Prop`
-/
#guard_msgs in
example (Γ Δ A B) (e : Ctx.snoc Γ A = Ctx.snoc Δ B) : Γ = Δ := by
  cases e with | refl => exact (1 : Nat)

-- several goals: the others are not disturbed
example (Γ Δ A B) (e : Ctx.snoc Γ A = Ctx.snoc Δ B) : Γ = Δ ∧ True := by
  constructor
  · cases e with | refl => rfl
  · trivial

/-! `cases` where an index is a constructor of a member, which it has to solve against each
case. -/

inductive CtxAt : Ctx → Type where
  | atNil : CtxAt .nil
  | atSnoc (Γ A) : CtxAt (.snoc Γ A)
inductive CtxPAt : Ctx → Prop where
  | nil : CtxPAt .nil
  | snoc (Γ A) : CtxPAt (.snoc Γ A)
inductive TAt : T → Type where
  | atLeaf : TAt .leaf
  | atNode (cs h) : TAt (.node cs h)
inductive TPAt : T → Prop where
  | leaf : TPAt .leaf
  | node (cs h) : TPAt (.node cs h)
inductive UAt : U → Type 1 where
  | atBase : UAt .base
  | atPi (a b) : UAt (.pi a b)
inductive UPAt : U → Prop where
  | base : UPAt .base
  | pi (a b) : UPAt (.pi a b)

example (a : CtxAt .nil) : a = .atNil := by cases a; rfl
example (h : CtxPAt .nil) : True := by cases h; trivial
example (Γ A) (a : CtxAt (.snoc Γ A)) : a = .atSnoc Γ A := by cases a; rfl
example (Γ A) (a : CtxAt (.snoc Γ A)) : a = .atSnoc Γ A := by cases a with | atSnoc G B => rfl
example (Γ A) (a b : CtxAt (.snoc Γ A)) : a = b := by cases a; cases b; rfl
example (Γ A) (h : CtxPAt (.snoc Γ A)) : True := by cases h; trivial
example (Γ A) (h : CtxPAt (.snoc Γ A)) : True := by cases h with | snoc => trivial
example (Γ A) (h : CtxPAt (.snoc Γ A)) : True := by rcases h with ⟨⟩; trivial
example (Γ A) (h : CtxPAt (.snoc Γ A)) : True := by obtain ⟨⟩ := h; trivial

example (a : TAt .leaf) : a = .atLeaf := by cases a; rfl
example (h : TPAt .leaf) : True := by cases h; trivial
example (cs h) (a : TAt (.node cs h)) : a = .atNode cs h := by cases a; rfl
example (cs h) (a : TAt (.node cs h)) : a = .atNode cs h := by cases a with | atNode c k => rfl
example (cs h) (p : TPAt (.node cs h)) : True := by cases p; trivial
example (cs h) (p : TPAt (.node cs h)) : True := by cases p with | node => trivial
example (cs h) (p : TPAt (.node cs h)) : True := by rcases p with ⟨⟩; trivial

example (a : UAt .base) : a = .atBase := by cases a; rfl
example (x b) (a : UAt (.pi x b)) : a = .atPi x b := by cases a; rfl
example (x b) (a : UAt (.pi x b)) : a = .atPi x b := by cases a with | atPi y c => rfl
example (x b) (p : UPAt (.pi x b)) : True := by cases p; trivial
example (x b) (p : UPAt (.pi x b)) : True := by cases p with | pi => trivial
example (x b) (p : UPAt (.pi x b)) : True := by rcases p with ⟨⟩; trivial

-- two indices, one solved by the other's, and a case ruled out
inductive Two : Ctx → Ctx → Prop where
  | mk (Γ A) : Two (.snoc Γ A) (.snoc Γ A)
example (Γ A Δ B) (h : Two (.snoc Γ A) (.snoc Δ B)) : Γ = Δ := by cases h; rfl
example (Γ A) (h : Two .nil (.snoc Γ A)) : False := by cases h
example (Γ A) (h : Two .nil (.snoc Γ A)) : False := nomatch h
example (x : Ctx) (h : Two x x) : True := by cases h; trivial

-- under another inductive's constructor
inductive Deep : Option T → Prop where
  | mk (cs h) : Deep (some (.node cs h))
example (a h) (p : Deep (some (T.node a h))) : True := by cases p; trivial
example (a b h k) (e : some (T.node a h) = some (T.node b k)) : a = b := by cases e; rfl
example (a b h k) (e : some (T.node a h) = some (T.node b k)) : a = b := by injections

-- naming the fields, by `cases` and by a pattern
inductive CtxV : Ctx → Type where
  | atSnoc (Γ A) (m : Nat) : CtxV (.snoc Γ A)
inductive CtxW : Ctx → Type where
  | l : CtxW .nil
  | n (Γ A) (w : CtxW .nil) : CtxW (.snoc Γ A)
example (Γ A) (v : CtxV (.snoc Γ A)) : Nat := by rcases v with ⟨c, k, m⟩; exact m
example (Γ A) (v : CtxV (.snoc Γ A)) : True := by obtain ⟨c, k, m⟩ := v; trivial
example (Γ A) (v : CtxW (.snoc Γ A)) : True := by cases v with | n c k x => cases x; trivial

-- `simp` at such an equation, and `nomatch`
example (a b A B) (e : Ctx.snoc a A = Ctx.snoc b B) : a = b := by simp at e; exact e.1
example (a n) (e : Ctx.nil = Ctx.snoc a n) : False := nomatch e
example (a b A B) : Ctx.snoc a A = Ctx.snoc b B ↔ a = b ∧ HEq A B := by simp

-- a member itself, at its sibling's constructor, which is the member's own case split
example (Γ A) (t : Ty (.snoc Γ A)) : True := by cases t <;> trivial
example (t : Ty .nil) : True := by cases t <;> trivial
example (Γ A) (t : Ty (.snoc Γ A)) : True := by cases t with | base => trivial | pi => trivial
example (Γ A) : Ty (.snoc Γ A) → Nat
  | .base => 0
  | .pi _ _ => 1

-- what Lean refuses of its own (`SelfTest`), it refuses here
example (Γ A) (t : Ty (.snoc Γ A)) : True := by
  fail_if_success induction t with | base => trivial | pi => trivial
  trivial
example (a b A B) (e : Ctx.snoc a A = Ctx.snoc b B) : a = b := by
  fail_if_success subst e
  cases e; rfl

/-! `match` where an index is a constructor of a member.  Lean's match compiler solves that
index by its own `cases`, so `Mumi.CtorTactics` writes such a `match` as the `cases` above. -/

inductive CtxZ : Ctx → Type where
  | l (k : Nat) : CtxZ .nil
  | n (Γ A) (w : Option Nat) : CtxZ (.snoc Γ A)

example (Γ A) (v : CtxV (.snoc Γ A)) : Nat := match v with | .atSnoc _ _ m => m
example (Γ A) : CtxV (.snoc Γ A) → Nat | .atSnoc _ _ m => m
example (Γ A) (v : CtxW (.snoc Γ A)) : True := by match v with | .n _ _ _ => trivial
example (v : CtxW .nil) : True := by match v with | .l => trivial

-- it reduces, where the case split does
def vval (Γ A) (v : CtxV (.snoc Γ A)) : Nat := match v with | .atSnoc _ _ m => m
example (Γ A) : vval Γ A (.atSnoc Γ A 5) = 5 := rfl
/-- info: 5 -/
#guard_msgs in
#eval vval .nil .base (.atSnoc .nil .base 5)

-- a field has both its names, the pattern's and the context's, and they agree
def vfst (Γ A) (v : CtxV (.snoc Γ A)) : Ctx := match v with | .atSnoc G _ _ => G
example (Γ A) (v : CtxV (.snoc Γ A)) : Ctx := match v with | .atSnoc _ _ _ => Γ
example (Γ A) (v : CtxV (.snoc Γ A)) : vfst Γ A v = Γ := by cases v; rfl
-- a result that depends on it
example (Γ A) (v : CtxV (.snoc Γ A)) : Ty Γ := match v with | .atSnoc _ B _ => B

-- `none` here is the constructor, not a variable that matches everything
def zval (Γ A) (z : CtxZ (.snoc Γ A)) : Nat := match z with
  | .n _ _ none => 0
  | .n _ _ (some k) => k
/-- info: 3 -/
#guard_msgs in
#eval zval .nil .base (.n .nil .base (some 3))
/-- info: 0 -/
#guard_msgs in
#eval zval .nil .base (.n .nil .base none)
/-- info: 'MumiTests.Demo.CtorEqs.zval' does not depend on any axioms -/
#guard_msgs in
#print axioms zval

-- several discriminants, a wildcard, `..`
def zpair (Γ A) (z : CtxZ (.snoc Γ A)) (b : Bool) : Nat := match z, b with
  | .n _ _ none, true => 0
  | .n _ _ none, false => 1
  | .n _ _ (some k), _ => k
/-- info: 1 -/
#guard_msgs in
#eval zpair .nil .base (.n .nil .base none) false
example (Γ A) (z : CtxZ (.snoc Γ A)) : Nat := match z with | _ => 7
example (Γ A) (z : CtxZ (.snoc Γ A)) : Nat := match z with | .n .. => 7

-- what is wrong is said
/--
error: Missing cases:
_, _, (some _)
-/
#guard_msgs in
example (Γ A) (z : CtxZ (.snoc Γ A)) : Nat := match z with | .n _ _ none => 0

/-- error: Redundant alternative: Any expression matching this pattern will match one of the preceding alternatives -/
#guard_msgs in
example (Γ A) (v : CtxV (.snoc Γ A)) : Nat := match v with | .atSnoc _ _ m => m | .atSnoc _ _ k => k

/--
error: Type mismatch
  G
has type
  Ctx
but is expected to have type
  Nat
-/
#guard_msgs in
example (Γ A) (v : CtxV (.snoc Γ A)) : Nat := match v with | .atSnoc G _ _ => G

-- a case left out, where two are possible
inductive CtxR : Ctx → Type where
  | stop (Γ A) : CtxR (.snoc Γ A)
  | go (Γ A) (r : CtxR (.snoc Γ A)) : CtxR (.snoc Γ A)
/--
error: unsolved goals
case go
Γ : Ctx
A : Ty Γ
r✝ : CtxR (Γ.snoc A)
⊢ Nat
-/
#guard_msgs in
example (Γ A) : CtxR (.snoc Γ A) → Nat | .stop _ _ => 0

/-! Recursion through such a `match`.  It is the `cases` above rather than a matcher, so Lean's
generator could only state the unfolding, which `simp` loops on; `Mumi.splitEqns` states one
equation to a constructor, as Lean's own are (`SelfTest`). -/

def rlen (Γ A) : CtxR (.snoc Γ A) → Nat
  | .stop _ _ => 0
  | .go _ _ r => rlen Γ A r + 1
/-- info: 1 -/
#guard_msgs in
#eval rlen .nil .base (.go .nil .base (.stop .nil .base))

/-- info: rlen.eq_1 : ∀ (Γ : Ctx) (A : Ty Γ), rlen Γ A (CtxR.stop Γ A) = 0 -/
#guard_msgs in
#check @rlen.eq_1
/-- info: rlen.eq_2 : ∀ (Γ : Ctx) (A : Ty Γ) (r : CtxR (Γ.snoc A)), rlen Γ A (CtxR.go Γ A r) = rlen Γ A r + 1 -/
#guard_msgs in
#check @rlen.eq_2

example (Γ A) : rlen Γ A (.stop Γ A) = 0 := by simp [rlen]
example (Γ A r) : rlen Γ A (.go Γ A r) = rlen Γ A r + 1 := by simp [rlen]
example (Γ A r) : rlen Γ A (.go Γ A r) = rlen Γ A r + 1 := by simp only [rlen]
example (Γ A r) : rlen Γ A (.go Γ A r) = rlen Γ A r + 1 := by rw [rlen]
-- by induction, as one would
example (Γ A) (r : CtxR (.snoc Γ A)) : rlen Γ A (.go Γ A (.go Γ A r)) = rlen Γ A r + 2 := by
  simp [rlen]

-- rows that take a further `match`
inductive CtxS : Ctx → Type where
  | stop (Γ A) (o : Option Nat) : CtxS (.snoc Γ A)
  | go (Γ A) (r : CtxS (.snoc Γ A)) : CtxS (.snoc Γ A)
def slen (Γ A) : CtxS (.snoc Γ A) → Nat
  | .stop _ _ none => 0
  | .stop _ _ (some k) => k
  | .go _ _ r => slen Γ A r + 1
example (Γ A r) : slen Γ A (.go Γ A r) = slen Γ A r + 1 := by simp [slen]
example (Γ A) : slen Γ A (.stop Γ A none) = 0 := by simp [slen]
example (Γ A k) : slen Γ A (.stop Γ A (some k)) = k := by simp [slen]

-- what the index is made of, named by the patterns: each a `let`
def snamed : (Γ : Ctx) → (A : Ty Γ) → CtxS (.snoc Γ A) → Nat
  | _, _, .stop _ _ _ => 0
  | Γ, A, .go _ _ r => snamed Γ A r + 1
example (Γ A r) : snamed Γ A (.go Γ A r) = snamed Γ A r + 1 := by simp [snamed]

-- a further discriminant after it
def safter (Γ A) : CtxS (.snoc Γ A) → Nat → Nat
  | .stop _ _ _, k => k
  | .go _ _ r, k => safter Γ A r (k + 1)
termination_by x => sizeOf x
example (Γ A r k) : safter Γ A (.go Γ A r) k = safter Γ A r (k + 1) := by simp [safter]

/-! Gap: with an argument that changes along the recursion, Lean's guess at a measure goes
wrong on what `cases` leaves, where Lean's own needs no help (`SelfTest`).  Saying the measure
is all it takes. -/

def sacc (Γ A) (k : Nat) (x : CtxS (.snoc Γ A)) : Nat := match x with
  | .stop _ _ _ => k
  | .go _ _ r => sacc Γ A (k + 1) r
termination_by sizeOf x
example (Γ A k r) : sacc Γ A k (.go Γ A r) = sacc Γ A (k + 1) r := by simp [sacc]

#guard_msgs (drop error) in
def saccGuess (Γ A) (k : Nat) : CtxS (.snoc Γ A) → Nat
  | .stop _ _ _ => k
  | .go _ _ r => saccGuess Γ A (k + 1) r
/-- info: 'MumiTests.Demo.CtorEqs.saccGuess' depends on axioms: [sorryAx] -/
#guard_msgs in
#print axioms saccGuess

/-! `match` on a `Prop` member that is a definition.  Its constructors are theorems, so Lean's
`match` has no patterns to elaborate, and the same rewrite gives it the case split. -/

mutual
inductive PT : Type where
  | leaf
  | node (t : PT) (h : POk t)
inductive POk : PT → Prop where
  | leaf : POk .leaf
  | node (t) (h : POk t) : POk (.node t h)
end

example (t) (h : POk t) : True := match h with | .leaf => trivial | .node _ _ => trivial
example (t) (h : POk t) : True := by match h with | .leaf => trivial | .node _ _ => trivial
example (t) (h : POk t) : True := match h with | POk.leaf .. => trivial | POk.node .. => trivial
example (t) : POk t → True | .leaf => trivial | .node _ _ => trivial
-- the index is the case's, and asking nothing of it is what takes it
theorem pokSelf (t) (h : POk t) : POk t := match t, h with
  | _, .leaf => .leaf
  | _, .node a b => .node a b
/-- info: 'MumiTests.Demo.CtorEqs.pokSelf' does not depend on any axioms -/
#guard_msgs in
#print axioms pokSelf

/-! `match` on a member of an induction-recursion, through its view. -/

def uTag : U → Nat
  | .base => 0
  | .pi _ _ => 1
example : uTag .base = 0 := rfl
example (a b) : uTag (.pi a b) = 1 := rfl
example (a b) : uTag (.pi a b) = 1 := by simp [uTag]
def uSize : U → Nat
  | .base => 1
  | .pi a _ => uSize a + 1
/-- info: 2 -/
#guard_msgs in
#eval uSize (.pi .base fun _ => .base)
example (a b) : uSize (.pi a b) = uSize a + 1 := by simp [uSize]

/-! What is left to Lean's compiler: a `match` with a motive of its own, on a term rather than
a name, or a `h :` on the discriminant, stops at the wrapper as before. -/

example (Γ A) (v : CtxV (.snoc Γ A)) : Nat := by
  fail_if_success exact match h : v with | .atSnoc _ _ m => m
  cases v with | atSnoc _ _ m => exact m

-- nothing internal in any of these proofs' axioms
theorem casesAtIndex (Γ A) (a b : CtxAt (.snoc Γ A)) : a = b := by cases a; cases b; rfl
theorem casesDeep (a b h k) (e : some (T.node a h) = some (T.node b k)) : a = b := by cases e; rfl
/-- info: 'MumiTests.Demo.CtorEqs.casesAtIndex' does not depend on any axioms -/
#guard_msgs in
#print axioms casesAtIndex
/-- info: 'MumiTests.Demo.CtorEqs.casesDeep' does not depend on any axioms -/
#guard_msgs in
#print axioms casesDeep

end Ways

end CtorEqs

/-! ## At the universe written

`X.ctorIdx` is a case split here, kept from Meta's unifier, which can spend for ever in what
it reaches; so `T.noConfusion h` does not reduce its way to its answer, and is told it.  And a
clause of a decoder may leave a field `_`, as any match may. -/

namespace LowerCtorEqs

set_option mumi.mahlo true in
mutual
inductive LCtx : Type where
  | nil : LCtx
  | ext (Γ : LCtx) (A : LTy Γ) : LCtx
inductive LTy : LCtx → Type where
  | base {Γ : LCtx} : LTy Γ
  | pi {Γ : LCtx} (A : LTy Γ) (B : LTy (.ext Γ A)) : LTy Γ
def LEl : LCtx → Type
  | .nil => Unit
  | .ext Γ _ => LEl Γ
def LVal {Γ : LCtx} : LTy Γ → Type
  | .base => Nat
  | .pi _ _ => Nat
end

example (Γ A) : LEl (.ext Γ A) = LEl Γ := rfl
example (Γ A) : LCtx.nil ≠ LCtx.ext Γ A := fun h => LCtx.noConfusion h
example {Γ} (A B) : LTy.base (Γ := Γ) ≠ LTy.pi A B := fun h => LTy.noConfusion h
example {Γ} (A B) : LTy.base (Γ := Γ) ≠ LTy.pi A B := fun h => LTy.noConfusion rfl (heq_of_eq h)
example (Γ A) (P : Sort _) (h : LCtx.nil = LCtx.ext Γ A) : P := LCtx.noConfusion h

-- and one written at the type a higher up
mutual
inductive U : Type where
  | base : U
  | pi (a : U) (b : El a → U) : U
def El : U → Type
  | .base => Nat
  | .pi a _ => El a
end

example (a b) : El (.pi a b) = El a := rfl

end LowerCtorEqs

/-! ## `deriving` on an induction-recursion

No pre-term stands behind these members, so what is derived is written against them by
`match`.  `DecidableEq` wants proofs that does not write, and says so rather than refusing the
block. -/

namespace DerivedIR

mutual
inductive U : Type where
  | base : U
  | pi (a : U) (b : El a → U) : U
  deriving Repr, Inhabited, Nonempty
inductive V : Type where
  | nat (n : Nat) : V
  | up (v : V) : V
  deriving Repr, BEq, Hashable, Inhabited
def El : U → Type
  | .base => Nat
  | .pi a b => (x : El a) → El (b x)
end

/-- info: MumiTests.Demo.DerivedIR.U.base -/
#guard_msgs in
#eval U.base
/-- info: MumiTests.Demo.DerivedIR.U.pi (MumiTests.Demo.DerivedIR.U.base) _ -/
#guard_msgs in
#eval U.pi .base fun _ => .base
/-- info: MumiTests.Demo.DerivedIR.V.up (MumiTests.Demo.DerivedIR.V.nat 1) -/
#guard_msgs in
#eval V.up (.nat 1)
/-- info: true -/
#guard_msgs in
#eval V.nat 1 == .nat 1
/-- info: false -/
#guard_msgs in
#eval V.nat 1 == .nat 2
/-- info: false -/
#guard_msgs in
#eval V.nat 1 == .up (.nat 1)
/-- info: true -/
#guard_msgs in
#eval hash (V.nat 1) != hash (V.nat 2)
/-- info: MumiTests.Demo.DerivedIR.V.nat 0 -/
#guard_msgs in
#eval (default : V)
example : Nonempty U := inferInstance

-- a carrier with no decoder of its own beside one with: `V` above, which used to be refused

/-- error: `deriving DecidableEq` is not available on an induction-recursion's members yet: `Repr`, `BEq`, `Hashable`, `Inhabited` and `Nonempty` are.  An instance may be written by `match`, which works on them. -/
#guard_msgs in
mutual
inductive Code : Type where
  | one : Code
  | pair (a b : Code) : Code
  deriving DecidableEq
def size : Code → Nat
  | .one => 1
  | .pair a b => size a + size b
end

/-- info: 2 -/
#guard_msgs in
#eval size (Code.pair .one .one)

end DerivedIR

/-! ## An index that is only variables, and a case that concludes at a constructor

`At (.id Γ)` has no constructor of `Ctx` in it, but `At.ext` concludes at `Ctx.snoc`, and that
is what `cases` has to compare with `Γ`. -/

namespace RepeatedAt

set_option mumi.separate false in
mutual
inductive Ctx : Type where
  | nil : Ctx
  | snoc : (Γ : Ctx) → Ty Γ → Ctx
inductive Ty : Ctx → Type where
  | base : (Γ : Ctx) → Ty Γ
inductive Sb : Ctx → Ctx → Type where
  | id : (Γ : Ctx) → Sb Γ Γ
  | ext : (Γ Δ : Ctx) → (A : Ty Γ) → (B : Ty Δ) → Sb Γ Δ → Sb (Ctx.snoc Γ A) (Ctx.snoc Δ B)
end

inductive At : {a b : Ctx} → Sb a b → Prop where
  | id (Γ) : At (.id Γ)
  | ext (Γ Δ A B s) : At (.ext Γ Δ A B s)

example (Γ) (h : At (.id Γ)) : True := by cases h; trivial
example (Γ Δ A B s) (h : At (.ext Γ Δ A B s)) : True := by cases h; trivial
example (Γ) (h : At (.id Γ)) : True := match h with | .id _ => trivial

end RepeatedAt

end MumiTests.Demo
