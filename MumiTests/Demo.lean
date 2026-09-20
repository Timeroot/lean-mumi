/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import Mumi

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
lowers the block into declarations it does accept.  What comes back is genuine
inductives, so everything Lean does to an inductive it does to these.

*Verdict: works.* -/

namespace Hetero

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

/-! Both members really are inductives, and so are their constructors. -/

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

/-- info: Tree.wrap : Hidden → Tree -/
#guard_msgs in
#check @Tree.wrap

/-- info: Hidden.mk : ∀ (t : Tree), Hidden -/
#guard_msgs in
#check @Hidden.mk

/-! `Tree.rec` is what it would have been with no proposition beside it: one
motive, one minor premise per constructor. -/

/--
info: @Tree.rec : {motive : Tree → Sort u_1} →
  ((n : Nat) → motive (Tree.leaf n)) →
    ((l r : Tree) → motive l → motive r → motive (l.node r)) →
      ((h : Hidden) → motive (Tree.wrap h)) → (t : Tree) → motive t
-/
#guard_msgs in
#check @Tree.rec

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

mutual
inductive Small : Type where
  | z : Small
  | s (m : Small) : Small
inductive Large : Type 2 where
  | of (m : Small) : Large
  | ty (α : Type 1) : Large
  | pair (a b : Large) : Large
end

/-- info: Large.of : Small → Large -/
#guard_msgs in
#check @Large.of

/--
info: @Large.rec : {motive : Large → Sort u_1} →
  ((m : Small) → motive (Large.of m)) →
    ((α : Type 1) → motive (Large.ty α)) →
      ((a b : Large) → motive a → motive b → motive (a.pair b)) → (t : Large) → motive t
-/
#guard_msgs in
#check @Large.rec

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

/-- info: Ctx.snoc : (Γ : Ctx) → Ty Γ → Ctx -/
#guard_msgs in
#check @Ctx.snoc

/-- info: Ty.arr : (Γ : Ctx) → (A : Ty Γ) → Ty (Γ.snoc A) → Ty Γ -/
#guard_msgs in
#check @Ty.arr

/-! `Ctx.rec` is the whole block's, with a motive per member, which is what an
induction-inductive block has instead of one recursor each.  The tactics are
driven off principles cut out of it, further down. -/

/--
info: @Ctx.rec : {motive_1 : Ctx → Sort u_1} →
  {motive_2 : (a : Ctx) → Ty a → Sort u_1} →
    motive_1 Ctx.nil →
      ((Γ : Ctx) → (A : Ty Γ) → motive_1 Γ → motive_2 Γ A → motive_1 (Γ.snoc A)) →
        ((Γ : Ctx) → motive_1 Γ → motive_2 Γ (Ty.base Γ)) →
          ((Γ : Ctx) →
              (A : Ty Γ) →
                (B : Ty (Γ.snoc A)) → motive_1 Γ → motive_2 Γ A → motive_2 (Γ.snoc A) B → motive_2 Γ (Ty.arr Γ A B)) →
            (t : Ctx) → motive_1 t
-/
#guard_msgs in
#check @Ctx.rec

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
  Ctx.casesOn (motive := fun _ => Bool) Γ true (fun _ _ => false)

/-- info: false -/
#guard_msgs in
#eval isNil (Ctx.snoc .nil (.base .nil))

/-! Injectivity is a theorem and a `@[simp]` lemma, stated the way an ordinary
constructor's is -- the dependent field compared with `HEq`. -/

/--
info: Ctx.snoc.injEq : ∀ (Γ : Ctx) (A : Ty Γ) (Γ_1 : Ctx) (A_1 : Ty Γ_1), (Γ.snoc A = Γ_1.snoc A_1) = (Γ = Γ_1 ∧ A ≍ A_1)
-/
#guard_msgs in
#check @Ctx.snoc.injEq

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

/-! ### What is missing

`injection` and `contradiction` reduce the type in hand until they reach an
inductive, and what they reach is the wrapper.  So `injection` leaves a goal
about pre-terms, and `contradiction` sees the wrapper's one constructor on both
sides and gives up.  `Ctx.noConfusion`, `Ctx.snoc.inj` and `simp` state the same
things about the member. -/

/--
error: unsolved goals
Γ Δ : Ctx
A : Ty Γ
B : Ty Δ
val_eq✝ : Γ.val.snoc A.val = Δ.val.snoc B.val
⊢ Γ = Δ
-/
#guard_msgs in
example (Γ Δ : Ctx) (A : Ty Γ) (B : Ty Δ) (h : Ctx.snoc Γ A = Ctx.snoc Δ B) : Γ = Δ := by
  injection h

example (Γ Δ : Ctx) (A : Ty Γ) (B : Ty Δ) (h : Ctx.snoc Γ A = Ctx.snoc Δ B) : Γ = Δ :=
  (Ctx.snoc.inj h).1

/--
error: Tactic `contradiction` failed

Γ : Ctx
A : Ty Γ
h : Ctx.nil = Γ.snoc A
⊢ False
-/
#guard_msgs in
example (Γ : Ctx) (A : Ty Γ) (h : Ctx.nil = Ctx.snoc Γ A) : False := by contradiction

example (Γ : Ctx) (A : Ty Γ) (h : Ctx.nil = Ctx.snoc Γ A) : False := by simp at h

/-! A view presents one constructor and stops, so a constructor written inside
another pattern needs a `match` of its own.  Saying so is the whole of the fix
we can offer; the split itself is two `match`es. -/

/--
error: A constructor of `MumiTests.Demo.IndInd.Ctx` cannot be written inside another pattern. `MumiTests.Demo.IndInd.Ctx` is matched through a view, which presents one constructor and stops, so this one has to be reached by a `match` of its own.
-/
#guard_msgs in
example (c : Ctx) : Nat :=
  match c with
  | .snoc (.snoc Γ _) _ => len Γ
  | _ => 0

def twoDeep : Ctx → Nat
  | .snoc Γ _ => match Γ with
    | .snoc Δ _ => len Δ + 10
    | .nil => 1
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

/-- info: Ok.snoc : ∀ (Γ : Ctx) (A : Ty Γ), Ok Γ → Ok (Γ.snoc A) -/
#guard_msgs in
#check @Ok.snoc

/-! `Ok.rec` is the whole block's, and `motive_3` there takes the value the data
recursion produced as well as the proof.  So a proposition here can say
something about what the recursion over `Ctx` returned, which is strictly more
than a recursion over the propositions alone can state.  Section 8 is a block
that loses it. -/

/--
info: @Ok.rec : ∀ {motive_1 : Ctx → Sort u_1} {motive_2 : (a : Ctx) → Ty a → Sort u_1}
  {motive_3 : (a : Ctx) → motive_1 a → Ok a → Prop} (nil : motive_1 Ctx.nil)
  (snoc : (Γ : Ctx) → (A : Ty Γ) → motive_1 Γ → motive_2 Γ A → motive_1 (Γ.snoc A))
  (base : (Γ : Ctx) → motive_1 Γ → motive_2 Γ (Ty.base Γ)) (nil_1 : motive_3 Ctx.nil nil Ok.nil)
  (snoc_1 :
    ∀ (Γ : Ctx) (A : Ty Γ) (h : Ok Γ) (Γ_ih : motive_1 Γ) (A_ih : motive_2 Γ A),
      motive_3 Γ Γ_ih h → motive_3 (Γ.snoc A) (snoc Γ A Γ_ih A_ih) ⋯)
  {a : Ctx} (h : Ok a), motive_3 a (Ctx.rec nil snoc base nil_1 snoc_1 a) h
-/
#guard_msgs in
#check @Ok.rec

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

mutual
inductive KCtx : Type where
  | nil : KCtx
  | snoc (Γ : KCtx) (A : KTy Γ 0) : KCtx
inductive KTy : KCtx → Nat → Type where
  | base (Γ : KCtx) (k : Nat) : KTy Γ k
  | arr (Γ : KCtx) (k : Nat) (A B : KTy Γ k) : KTy Γ k
end

/-- info: KTy.arr : (Γ : KCtx) → (k : Nat) → KTy Γ k → KTy Γ k → KTy Γ k -/
#guard_msgs in
#check @KTy.arr

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

mutual
inductive UCtx : Type where
  | nil : UCtx
  | snoc (Γ : UCtx) (A : UTy 0 Γ) : UCtx
inductive UTy : Nat → UCtx → Type where
  | base (n : Nat) (Γ : UCtx) : UTy n Γ
  | wrap (n : Nat) (Γ : UCtx) (A : UTy n Γ) : UTy n Γ
  | up (n : Nat) (Γ : UCtx) (A : UTy n Γ) : UTy (n + 1) Γ
end

/-- info: UTy.up : (n : Nat) → (Γ : UCtx) → UTy n Γ → UTy (n + 1) Γ -/
#guard_msgs in
#check @UTy.up

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

/--
info: @R.rec : ∀ {motive : (a : C) → (a_1 : D) → R a a_1 → Prop},
  motive C.nil D.nil R.nil →
    (∀ (c : C) (d : D) (h : R c d), motive c d h → motive c.cons d ⋯) →
      ∀ {a : C} {a_1 : D} (t : R a a_1), motive a a_1 t
-/
#guard_msgs in
#check @R.rec

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

/--
info: @C.rec : {motive : C → Sort u_1} → motive C.nil → ((c : C) → motive c → motive c.cons) → (t : C) → motive t
-/
#guard_msgs in
#check @C.rec

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

What that costs is the propositions' place in the recursion over the *whole
block*.  Every proposition here is peeled out instead and given a recursion over
the propositions alone; with no joint recursion left to hold the name, that one
*is* `rec`.  The control at the end of the section is the same block with `hs`
deleted, where `Big.rec` carries a motive per member and the proposition's takes
the value the recursion over `T` produced -- the thing section 4 turns on.  The
difference between the two `Big.rec`s is the whole of the cost, and it falls on
every proposition in the block, not only on the one that forgot a field.

Nothing else goes.  The types are as written, the data member is untouched,
`induction` and `cases` work and bind the field, and the surviving recursion is
no worse than the one Lean gives such a proposition standing alone: `hs` bound
in the minor premise for `Big.node`, and no `hs_ih`, because a field the
conclusion never mentions is exactly what stops the proposition from being a
subsingleton.

*Verdict: works, with a caveat -- and the caveat is no known way.* -/

namespace Forgotten

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

/-- info: Big.node : ∀ (cs hs : List T) (h : Ok cs), Big (T.node cs h) -/
#guard_msgs in
#check @Big.node

/-! `Big.rec` is the recursion over the propositions alone: one motive, `hs`
bound in the minor premise for `Big.node`, and no `hs_ih`.  `Ok` did not forget
anything and is peeled out all the same. -/

/--
info: @Big.rec : ∀ {motive : (a : T) → Big a → Prop},
  (∀ (cs hs : List T) (h : Ok cs), motive (T.node cs h) ⋯) → motive T.leaf Big.leaf → ∀ {a : T} (t : Big a), motive a t
-/
#guard_msgs in
#check @Big.rec

/--
info: @Ok.rec : ∀ {motive : (a : List T) → Ok a → Prop},
  motive [] Ok.nil →
    (∀ (t : T) (ts : List T) (h : Ok ts), motive ts h → motive (t :: ts) ⋯) → ∀ {a : List T} (h : Ok a), motive a h
-/
#guard_msgs in
#check @Ok.rec

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

/-! The control: the same block with `hs` deleted.  Now the propositions stay in
the block's recursion, and `motive_2` takes `motive_1 a` -- the value the
recursion over `T` produced -- alongside the proof.  That argument is what the
forgotten field costs. -/

namespace Kept

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

/--
info: @Big.rec : ∀ {motive_1 : T → Sort u_1} {motive_2 : (a : T) → motive_1 a → Big a → Prop} {motive_3 : List T → Sort u_1}
  {motive_4 : (a : List T) → motive_3 a → Ok a → Prop}
  (node : (cs : List T) → (h : Ok cs) → (cs_ih : motive_3 cs) → motive_4 cs cs_ih h → motive_1 (T.node cs h))
  (leaf : motive_1 T.leaf)
  (node_1 :
    ∀ (cs : List T) (h : Ok cs) (cs_ih : motive_3 cs) (h_ih : motive_4 cs cs_ih h),
      motive_2 (T.node cs h) (node cs h cs_ih h_ih) ⋯)
  (leaf_1 : motive_2 T.leaf leaf Big.leaf) (nil : motive_3 [])
  (cons : (head : T) → (tail : List T) → motive_1 head → motive_3 tail → motive_3 (head :: tail))
  (nil_1 : motive_4 [] nil Ok.nil)
  (cons_1 :
    ∀ (t : T) (ts : List T) (h : Ok ts) (t_ih : motive_1 t) (ts_ih : motive_3 ts),
      motive_4 ts ts_ih h → motive_4 (t :: ts) (cons t ts t_ih ts_ih) ⋯)
  {a : T} (t : Big a), motive_2 a (T.rec node leaf node_1 leaf_1 nil cons nil_1 cons_1 a) t
-/
#guard_msgs in
#check @Big.rec

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

mutual
inductive A : Prop where
  | mk (b : B) : A
inductive B : Type where
  | leaf (n : Nat) : B
  | fromA (a : A) : B
end

/-! The `Prop` member's motive is `A → Prop`; the data member's is `Sort u`. -/
/--
info: @A.rec : ∀ {motive_1 : A → Prop} {motive_2 : B → Sort u_1},
  (∀ (b : B) (ih_1 : motive_2 b), motive_1 ⋯) →
    ∀ (case_2 : (n : Nat) → motive_2 (B.leaf n)) (case_3 : (a : A) → motive_1 a → motive_2 (B.fromA a)) (t : A),
      motive_1 t
-/
#guard_msgs in
#check @A.rec

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
`B.rec` is the one-motive one, so the field at the proposition carries no
hypothesis: there is no motive over `A` for it to be at. -/

example : B.rec (motive := fun _ => Nat) (fun n => n) (fun _ => 0) (.leaf 7) = 7 := rfl

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

inductive T : Type where
  | mk1 : T
  | mkT (h : Nonempty T) : T

/-- info: T.mkT : Nonempty T → T -/
#guard_msgs in
#check @T.mkT

/-! The constructor really is a constructor here: the rescue went through the
lowering, not through the erasure, so `T` is an inductive. -/
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

mutual
inductive Box (α : Type u) : Type u where
  | mk (a : α) (p : BoxP α) : Box α
inductive BoxP (α : Type u) : Prop where
  | p : BoxP α
end

mutual
inductive St : Type 1 where
  | tip : St
  | mk (w : Box St) : St
inductive Other : Type where
  | b : Other
end

/-! The field's type is the copy's name, not `Box St`. -/
/-- info: St.mk : St.nested_Box_1 → St -/
#guard_msgs in
#check @St.mk

/-- info: St.nested_Box_1.toOrig : St.nested_Box_1 → Box St -/
#guard_msgs in
#check @St.nested_Box_1.toOrig

/-- info: St.nested_Box_1.ofOrig : Box St → St.nested_Box_1 -/
#guard_msgs in
#check @St.nested_Box_1.ofOrig

/-- A `match` on the field goes through the coercion, and the inner `match` is
`Box`'s own. -/
def count : St → Nat
  | .tip => 0
  | .mk w => match (w : Box St) with | .mk _ _ => 1

/-- info: 1 -/
#guard_msgs in
#eval count (St.mk (St.nested_Box_1.ofOrig (.mk .tip .p)))

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

/-! The pre-term is what `Repr` was handed, so the proof field is gone and the
constructors are the pre-type's. -/
/-- info: MumiTests.Demo.Derive.DVec._pre.cons (MumiTests.Demo.Derive.DVec._pre.nil) -/
#guard_msgs in
#eval repr (DVec.cons DVec.nil DOk.nil)

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

mutual
inductive Ctx : Type where
  | nil : Ctx
inductive Ty : (Nat → Ctx) → Type where
  | mk (f : Nat → Ctx) : Ty f
end

/-- info: Ty.mk : (f : Nat → Ctx) → Ty f -/
#guard_msgs in
#check @Ty.mk

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

mutual
inductive T : C → Type where
  | base (Γ : C) : T Γ
inductive C : Type where
  | nil : C
  | snoc (Γ : C) (A : T Γ) : C
end

/-- info: T.base : (Γ : C) → T Γ -/
#guard_msgs in
#check @T.base

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

*Verdict: rejected, a different theory.* -/

namespace IndRec

/--
error: invalid mutual block: either all elements of the block must be inductive/structure declarations, or they must all be definitions/theorems/abbrevs
-/
#guard_msgs in
mutual
inductive U : Type where
  | nat : U
  | pi (a : U) (b : El a → U) : U
def El : U → Type
  | .nat => Nat
  | .pi a b => (x : El a) → El (b x)
end

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

end MumiTests.Demo
