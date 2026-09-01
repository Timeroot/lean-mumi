/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import Mumi

/-!
# Recursors with one motive

The recursion over a whole induction-inductive block asks for a motive at every
member.  That is what makes it strong, and what stops `induction` from driving
it: the goal mentions one member, and nothing determines the motives of the
others.

So each member also gets a recursor with the other members' motives already
discharged -- `X.recD` for a data member and `X.recP` for a proposition, each
at the one-element type of the discharged motive's own sort -- and a `casesD`
or `casesP` with the hypotheses gone as well, which is the shape `cases` wants.

Discharging a motive of the *other* kind costs nothing: a motive at one member
cannot mention what the recursion computed at another, so what goes is what it
could not have used.  Discharging one of the same kind does cost hypotheses,
and on the induction-inductive route it is done anyway -- a member there is a
`def`, so a tactic that finds no eliminator of its own does not stop the way
mainline stops a `mutual`; it unfolds the member and offers a split on the
subtype it is encoded as.  A weaker principle beats one stated in the encoding,
and the recursion over the whole block is still a `using` away.  The lowered
route keeps its members as inductives, so it keeps the refusal too.
-/

namespace MumiTests.SoloRec

/-! ## The flagship block -/

namespace Flagship

mutual
inductive Ctx : Type where
  | nil
  | snoc (Γ : Ctx) (x : String) (h : Fresh x Γ)
inductive Fresh : String → Ctx → Prop where
  | nil (x : String) : Fresh x .nil
  | snoc (x y : String) (Γ : Ctx) (h : Fresh y Γ) (hne : x ≠ y) (hΓ : Fresh x Γ) :
      Fresh x (.snoc Γ y h)
end

/--
info: @Ctx.recD : {motive : Ctx → Sort u_1} →
  motive Ctx.nil → ((Γ : Ctx) → (x : String) → (h : Fresh x Γ) → motive Γ → motive (Γ.snoc x h)) → (t : Ctx) → motive t
-/
#guard_msgs in
#check @Ctx.recD

/--
info: @Fresh.recP : ∀ {motive : (a : String) → (a_1 : Ctx) → Fresh a a_1 → Prop},
  (∀ (x : String), motive x Ctx.nil ⋯) →
    (∀ (x y : String) (Γ : Ctx) (h : Fresh y Γ) (hne : x ≠ y) (hΓ : Fresh x Γ),
        motive y Γ h → motive x Γ hΓ → motive x (Γ.snoc y h) ⋯) →
      ∀ {a : String} {a_1 : Ctx} (h : Fresh a a_1), motive a a_1 h
-/
#guard_msgs in
#check @Fresh.recP

/-! `Ctx.recD` computes: its iota rule is the block's, which holds by `rfl`. -/

def len : Ctx → Nat := Ctx.recD 0 (fun _ _ _ n => n + 1)

example : len .nil = 0 := rfl
example : len (.snoc .nil "a" (.nil "a")) = 1 := rfl
example : len (.snoc (.snoc .nil "a" (.nil "a")) "b" (.snoc "b" "a" .nil (.nil "a")
    (by simp) (.nil "b"))) = 2 := rfl

/-! Both are the `induction` tactic's default eliminator for their member, so
neither needs `using`. -/

example (Γ : Ctx) : len Γ = len Γ := by
  induction Γ with
  | nil => rfl
  | snoc Γ x h ih => rfl

theorem fresh_lt {x : String} {Γ : Ctx} (h : Fresh x Γ) : 0 ≤ len Γ := by
  induction h with
  | nil x => exact Nat.le_refl 0
  | snoc x y Γ h hne hΓ ih ihΓ => exact Nat.zero_le _

/-- The data motive really is available at any sort, not just at `Prop`. -/
example : Ctx → Type := Ctx.recD (motive := fun _ => Type) Unit (fun _ _ _ α => Option α)

end Flagship

/-! ## One data member and several propositions

Every proposition's motive is discharged at once, so the data member still gets
its recursor.  So does each proposition, at the price of the hypotheses at the
other one -- a price worth paying, since a member of an erased block is a `def`
and a tactic that finds no eliminator unfolds it rather than stopping.
-/

namespace TwoProps

mutual
inductive C : Type where
  | nil
  | snoc (Γ : C) (x : String) (h : P x Γ) (g : Q Γ)
inductive P : String → C → Prop where
  | nil (x) : P x .nil
inductive Q : C → Prop where
  | nil : Q .nil
end

/--
info: @C.recD : {motive : C → Sort u_1} →
  motive C.nil →
    ((Γ : C) → (x : String) → (h : P x Γ) → (g : Q Γ) → motive Γ → motive (Γ.snoc x h g)) → (t : C) → motive t
-/
#guard_msgs in
#check @C.recD

/--
info: @P.recP : ∀ {motive : (a : String) → (a_1 : C) → P a a_1 → Prop},
  (∀ (x : String), motive x C.nil ⋯) → ∀ {a : String} {a_1 : C} (h : P a a_1), motive a a_1 h
-/
#guard_msgs in
#check @P.recP

/--
info: @Q.recP : ∀ {motive : (a : C) → Q a → Prop}, motive C.nil Q.nil → ∀ {a : C} (h : Q a), motive a h
-/
#guard_msgs in
#check @Q.recP

example (Γ : C) : True := by
  induction Γ with
  | nil => trivial
  | snoc Γ x h g ih => trivial

/-! Each proposition drives `induction` on its own, without naming the other. -/

example (x : String) (Γ : C) (h : P x Γ) : True := by
  induction h with
  | nil y => trivial

example (Γ : C) (g : Q Γ) : True := by
  induction g with
  | nil => trivial

end TwoProps

/-! ## Two data members, and what the second one costs

Discharging a data motive costs the induction hypotheses at that member.  The
recursion is written anyway, because the member it is written for is a `def`
and the tactic that would have had it does not stop without one -- it unfolds
the member and splits on the subtype.  A denested block is the usual way to
have two data members: the copies the denesting adds are data members like any
other, and here the whole of `R`'s recursive structure sits inside one, so what
is left after they are discharged is a case split.
-/

namespace TwoData

inductive Tree (α : Type) : Type where
  | leaf | node (l : Tree α) (a : α) (r : Tree α)

inductive Tree.WF {α : Type} : Tree α → Prop where
  | leaf : Tree.WF .leaf
  | node (l a r) : Tree.WF l → Tree.WF r → Tree.WF (.node l a r)

def WFTree (α : Type) : Type := { t : Tree α // t.WF }

inductive R : Type where
  | tip
  | mk (x : WFTree R)

/--
info: @R.recD : {motive : R → Sort u_1} → motive R.tip → ((x : { t // t.WF }) → motive (R.mk x)) → (t : R) → motive t
-/
#guard_msgs in
#check @R.recD

/-! The recursion over the whole block is still there, and still the strong
one: two of its four motives are data, which is exactly what the one-motive
version had to give up. -/

/--
info: @R.rec : {motive_1 : R → Sort u_1} →
  {motive_2 : { t // t.WF } → Sort u_1} →
    {motive_3 : Tree R → Sort u_1} →
      {motive_4 : (a : Tree R) → motive_3 a → a.WF → Prop} →
        motive_1 R.tip →
          ((x : { t // t.WF }) → motive_2 x → motive_1 (R.mk x)) →
            ((val : Tree R) →
                (property : val.WF) →
                  (val_ih : motive_3 val) → motive_4 val val_ih property → motive_2 ⟨val, property⟩) →
              (leaf : motive_3 Tree.leaf) →
                (node :
                    (l : Tree R) →
                      (a : R) → (r : Tree R) → motive_3 l → motive_1 a → motive_3 r → motive_3 (l.node a r)) →
                  motive_4 Tree.leaf leaf ⋯ →
                    (∀ (l : Tree R) (a : R) (r : Tree R) (a_1 : l.WF) (a_2 : r.WF) (l_ih : motive_3 l)
                        (a_ih : motive_1 a) (r_ih : motive_3 r),
                        motive_4 l l_ih a_1 →
                          motive_4 r r_ih a_2 → motive_4 (l.node a r) (node l a r l_ih a_ih r_ih) ⋯) →
                      (t : R) → motive_1 t
-/
#guard_msgs in
#check @R.rec

end TwoData

/-! ## The lowered route

A block that is heterogeneous without being induction-inductive is lowered
rather than encoded, and its `Prop` members were in the same position: the
block-wide `X.mutualRec` -- which also answers to `X.rec` there -- asks for a
motive at every data member, and a goal about the proposition determines none of
them.  They get an `X.recP` by the same rule.

The data members need nothing: a lowered data member keeps its own native `rec`,
and discharging the propositions' motives at `True` is exactly what that already
is.
-/

namespace Lowered

mutual
inductive D : Type where
  | tip
  | mk (h : R)
inductive R : Prop where
  | tip
  | mk (d : D)
end

/--
info: @R.recP : ∀ {motive : R → Prop}, motive R.tip → (∀ (d : D), motive ⋯) → ∀ (t : R), motive t
-/
#guard_msgs in
#check @R.recP

/-! The recursion over the block is untouched, and still the strong one: its
`mk` case does get the induction hypothesis at `D` that `recP`'s cannot. -/

/--
info: @R.mutualRec : ∀ {motive_1 : D → Sort u_1} {motive_2 : R → Prop} (case_1 : motive_1 D.tip)
  (case_2 : (h : R) → motive_2 h → motive_1 (D.mk h)),
  motive_2 R.tip → (∀ (d : D) (ih_1 : motive_1 d), motive_2 ⋯) → ∀ (t : R), motive_2 t
-/
#guard_msgs in
#check @R.mutualRec

example (r : R) : True := by
  induction r with
  | tip => trivial
  | mk d => trivial

/-! A lowered data member keeps Lean's own recursor, and Lean's own `induction`
support with it. -/

/--
info: @D.rec : {motive : D → Sort u_1} → motive D.tip → ((h : R) → motive (D.mk h)) → (t : D) → motive t
-/
#guard_msgs in
#check @D.rec

example (d : D) : True := by
  induction d with
  | tip => trivial
  | mk h => trivial

end Lowered

/-! An indexed proposition keeps its indices as targets. -/

namespace LoweredIndexed

mutual
inductive D : Type 1 where
  | tip
  | mk (α : Type) (h : R α)
inductive R : Type → Prop where
  | tip (α) : R α
  | mk (α) (d : D) : R α
end

/--
info: @R.recP : ∀ {motive : (a : Type) → R a → Prop},
  (∀ (α : Type), motive α ⋯) → (∀ (α : Type) (d : D), motive α ⋯) → ∀ {a : Type} (t : R a), motive a t
-/
#guard_msgs in
#check @R.recP

example (α : Type) (r : R α) : True := by
  induction r with
  | tip β => trivial
  | mk β d => trivial

end LoweredIndexed

/-! Two data members in two universes are two SCCs, so the block-wide recursor
carries two elimination levels; both are pinned, and neither survives into
`recP`. -/

namespace LoweredTwoSCC

mutual
inductive A : Type where
  | tip
  | mk (h : R)
inductive B : Type 1 where
  | tip
  | mk (a : A) (h : R)
inductive R : Prop where
  | tip
  | mk (a : A) (b : B)
end

/--
info: @R.recP : ∀ {motive : R → Prop}, motive R.tip → (∀ (a : A) (b : B), motive ⋯) → ∀ (t : R), motive t
-/
#guard_msgs in
#check @R.recP

/-- info: R.recP has 0 universe parameters, R.mutualRec has 2 -/
#guard_msgs in
open Lean in
run_meta do
  let env ← getEnv
  let n (c : Name) := ((env.find? c).map (·.levelParams.length)).getD 0
  logInfo m!"R.recP has {n `MumiTests.SoloRec.LoweredTwoSCC.R.recP} universe parameters, \
    R.mutualRec has {n `MumiTests.SoloRec.LoweredTwoSCC.R.mutualRec}"

example (r : R) : True := by
  induction r with
  | tip => trivial
  | mk a b => trivial

end LoweredTwoSCC

/-! Two propositions in a lowered block get nothing, for the reason they get
nothing anywhere else: discharging the other's motive drops a hypothesis. -/

namespace LoweredTwoProps

mutual
inductive D : Type where
  | tip
  | mk (h : R)
inductive R : Prop where
  | tip
  | mk (d : D) (q : Q)
inductive Q : Prop where
  | tip
end

/-- info: R.recP: false, Q.recP: false -/
#guard_msgs in
open Lean in
run_meta do
  let env ← getEnv
  logInfo m!"R.recP: {(env.find? `MumiTests.SoloRec.LoweredTwoProps.R.recP).isSome}, \
    Q.recP: {(env.find? `MumiTests.SoloRec.LoweredTwoProps.Q.recP).isSome}"

end LoweredTwoProps

end MumiTests.SoloRec
