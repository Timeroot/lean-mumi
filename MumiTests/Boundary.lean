/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import Mumi

/-!
# Shapes at the edge of what the block elaborators take

The other test files each grow out of one construction and vary it.  This one
is the opposite: a sweep of block shapes written down without reference to how
the library works, kept because they came out whole and so are worth being told
about if they stop doing so.  Several of them are combinations -- a nesting at
a member another member indexes, an ind-ind block across two universes, a
denesting that wants a constructor's field as an index of a copy -- that each
of the other files exercises one half of.

The last section is the one shape in the sweep that does not come out.  It is
here for the same reason `MumiTests.Shapes` keeps its two: so that a change in
what the library accepts is a test failure and not a surprise.
-/

namespace MumiTests.Boundary

/-! ## A member indexed by a list of another

`Sub` is data, and its index is a `List Ctx` -- a nesting of a member, in the
*arity* of a member.  The arity is where a member may not appear, so the index
is deleted and given back by the well-formedness; that the thing deleted is a
container of a member rather than a member is what this pins.
-/

namespace ListIdx

mutual
inductive Ctx : Type where
  | nil
  | snoc (Γ : Ctx) (A : Ty Γ) : Ctx
inductive Ty : Ctx → Type where
  | base (Γ : Ctx) : Ty Γ
inductive Sub : List Ctx → Type where
  | nil : Sub []
  | cons (Γ : Ctx) (Γs : List Ctx) (A : Ty Γ) (s : Sub Γs) : Sub (Γ :: Γs)
end

example : Sub [.nil] := .cons .nil [] (.base .nil) .nil

/--
info: @Sub.rec : {motive_1 : Ctx → Sort u_1} →
  {motive_2 : (a : Ctx) → Ty a → Sort u_1} →
    {motive_3 : (a : List Ctx) → Sub a → Sort u_1} →
      motive_1 Ctx.nil →
        ((Γ : Ctx) → (A : Ty Γ) → motive_1 Γ → motive_2 Γ A → motive_1 (Γ.snoc A)) →
          ((Γ : Ctx) → motive_1 Γ → motive_2 Γ (Ty.base Γ)) →
            motive_3 [] Sub.nil →
              ((Γ : Ctx) →
                  (Γs : List Ctx) →
                    (A : Ty Γ) →
                      (s : Sub Γs) →
                        motive_1 Γ → motive_2 Γ A → motive_3 Γs s → motive_3 (Γ :: Γs) (Sub.cons Γ Γs A s)) →
                {a : List Ctx} → (t : Sub a) → motive_3 a t
-/
#guard_msgs in
#check @Sub.rec

end ListIdx

/-! ## A nesting at a member another member indexes

`Ctx.many` reaches its own block through a `List`, and `Ty` is indexed by
`Ctx`.  The recursion the block gets has a motive for the container as well as
for the two members, which is what a nesting always adds, and the container's
motive is indexed by the context the list is at.
-/

namespace ListNest

mutual
inductive Ctx : Type where
  | nil
  | many (Γ : Ctx) (As : List (Ty Γ)) : Ctx
inductive Ty : Ctx → Type where
  | base (Γ : Ctx) : Ty Γ
  | list (Γ : Ctx) (As : List (Ty Γ)) : Ty Γ
end

example : Ctx := .many .nil [.base .nil, .list .nil []]

/--
info: @Ctx.rec : {motive_1 : Ctx → Sort u_1} →
  {motive_2 : (a : Ctx) → Ty a → Sort u_1} →
    {motive_3 : (Γ : Ctx) → List (Ty Γ) → Sort u_1} →
      motive_1 Ctx.nil →
        ((Γ : Ctx) → (As : List (Ty Γ)) → motive_1 Γ → motive_3 Γ As → motive_1 (Γ.many As)) →
          ((Γ : Ctx) → motive_1 Γ → motive_2 Γ (Ty.base Γ)) →
            ((Γ : Ctx) → (As : List (Ty Γ)) → motive_1 Γ → motive_3 Γ As → motive_2 Γ (Ty.list Γ As)) →
              ((Γ : Ctx) → motive_1 Γ → motive_3 Γ []) →
                ((Γ : Ctx) →
                    (head : Ty Γ) →
                      (tail : List (Ty Γ)) →
                        motive_1 Γ → motive_2 Γ head → motive_3 Γ tail → motive_3 Γ (head :: tail)) →
                  (t : Ctx) → motive_1 t
-/
#guard_msgs in
#check @Ctx.rec

end ListNest

/-! ## The same, through `Prod`, `Option` and `Except`

A container with two fields of the nested type, one with none, and one whose
other summand is unrelated.
-/

namespace OtherNests

mutual
inductive Ctx : Type where
  | nil
  | pair (Γ : Ctx) (p : Ty Γ × Ty Γ) : Ctx
  | maybe (Γ : Ctx) (A : Option (Ty Γ)) : Ctx
  | either (Γ : Ctx) (A : Except Nat (Ty Γ)) : Ctx
inductive Ty : Ctx → Type where
  | base (Γ : Ctx) : Ty Γ
end

example : Ctx := .pair .nil (.base .nil, .base .nil)
example : Ctx := .maybe .nil none
example : Ctx := .either .nil (.error 3)

end OtherNests

/-! ## A nesting whose parameters mention a field of the constructor

`Vec (Ty Γ) n` takes its length from `n`, which `Ctx.snoc` binds.  That is the
denesting the kernel refuses outright -- it specialises a nesting only at
closed parameters -- so the copy is one the library has to make, inside a block
that is induction-inductive besides.
-/

namespace LocalNest

inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons {n} (a : α) (v : Vec α n) : Vec α (n + 1)

mutual
inductive Ctx : Type where
  | nil
  | snoc (n : Nat) (Γ : Ctx) (v : Vec (Ty Γ) n) : Ctx
inductive Ty : Ctx → Type where
  | base (Γ : Ctx) : Ty Γ
end

example : Ctx := .snoc 1 .nil (.cons (.base .nil) .nil)

/--
info: @Ctx.rec : {motive_1 : Ctx → Sort u_1} →
  {motive_2 : (a : Ctx) → Ty a → Sort u_1} →
    {motive_3 : (Γ : Ctx) → (a : Nat) → Vec (Ty Γ) a → Sort u_1} →
      motive_1 Ctx.nil →
        ((n : Nat) → (Γ : Ctx) → (v : Vec (Ty Γ) n) → motive_1 Γ → motive_3 Γ n v → motive_1 (Ctx.snoc n Γ v)) →
          ((Γ : Ctx) → motive_1 Γ → motive_2 Γ (Ty.base Γ)) →
            ((Γ : Ctx) → motive_1 Γ → motive_3 Γ 0 Vec.nil) →
              ((Γ : Ctx) →
                  {n : Nat} →
                    (a : Ty Γ) →
                      (v : Vec (Ty Γ) n) →
                        motive_1 Γ → motive_2 Γ a → motive_3 Γ n v → motive_3 Γ (n + 1) (Vec.cons a v)) →
                (t : Ctx) → motive_1 t
-/
#guard_msgs in
#check @Ctx.rec

end LocalNest

/-! ## An infinitary field at an indexed member

`Ctx.fam` holds a family of types over its own context, so the recursion's
hypothesis about it is a family of hypotheses.
-/

namespace Infinitary

mutual
inductive Ctx : Type where
  | nil
  | fam (Γ : Ctx) (f : Nat → Ty Γ) : Ctx
inductive Ty : Ctx → Type where
  | base (Γ : Ctx) : Ty Γ
end

example : Ctx := .fam .nil fun _ => .base .nil

/--
info: @Ctx.rec : {motive_1 : Ctx → Sort u_1} →
  {motive_2 : (a : Ctx) → Ty a → Sort u_1} →
    motive_1 Ctx.nil →
      ((Γ : Ctx) → (f : Nat → Ty Γ) → motive_1 Γ → ((a : Nat) → motive_2 Γ (f a)) → motive_1 (Γ.fam f)) →
        ((Γ : Ctx) → motive_1 Γ → motive_2 Γ (Ty.base Γ)) → (t : Ctx) → motive_1 t
-/
#guard_msgs in
#check @Ctx.rec

end Infinitary

/-! ## Two universes across an induction-induction

`Ctx` is a `Type 1` and `Ty` a `Type`, so the block is heterogeneous *and*
induction-inductive.  Only one of the two elaborators can have it, and it is
the ind-ind one: the arity is what decides, and the universes then sort
themselves out because the pre-types are the ones that have to agree.
-/

namespace TwoUniverses

mutual
inductive Ctx : Type 1 where
  | nil
  | snoc (Γ : Ctx) (A : Ty Γ) : Ctx
inductive Ty : Ctx → Type where
  | base (Γ : Ctx) : Ty Γ
end

example : Ctx := .snoc .nil (.base .nil)

/--
info: @Ty.rec : {motive_1 : Ctx → Sort u_1} →
  {motive_2 : (a : Ctx) → Ty a → Sort u_1} →
    motive_1 Ctx.nil →
      ((Γ : Ctx) → (A : Ty Γ) → motive_1 Γ → motive_2 Γ A → motive_1 (Γ.snoc A)) →
        ((Γ : Ctx) → motive_1 Γ → motive_2 Γ (Ty.base Γ)) → {a : Ctx} → (t : Ty a) → motive_2 a t
-/
#guard_msgs in
#check @Ty.rec

end TwoUniverses

/-! ## One constructor each

Nothing here is recursive except through the index, so the block is the
smallest induction-induction there is.
-/

namespace SingleCtor

mutual
inductive Ctx : Type where
  | mk (n : Nat) (A : Ty n) : Ctx
inductive Ty : Nat → Type where
  | mk (n : Nat) : Ty n
end

example : Ctx := .mk 2 (.mk 2)

end SingleCtor

/-! ## A section variable the block picks up

`α` is a variable of the section and is used by one member only; both members
take it as a parameter, which is what Lean does for a `mutual` block of its
own.
-/

namespace SectionVar

section
variable (α : Type)

mutual
inductive Ctx : Type where
  | nil
  | snoc (Γ : Ctx) (A : Ty Γ) : Ctx
inductive Ty : Ctx → Type where
  | base (Γ : Ctx) (a : α) : Ty Γ
end

end

example : Ctx Nat := .snoc .nil (.base .nil 3)

end SectionVar

/-! ## A member indexed by two others of the same type

`Sub.id` gives its context as both indices, which is the case where a field
can stand for only one of the positions it is written at and the other is
treated as one the constructor built.
-/

namespace TwoIdx

mutual
inductive Ctx : Type where
  | nil
  | snoc (Γ : Ctx) (A : Ty Γ) : Ctx
inductive Ty : Ctx → Type where
  | base (Γ : Ctx) : Ty Γ
inductive Sub : Ctx → Ctx → Type where
  | id (Γ : Ctx) : Sub Γ Γ
  | wk (Γ : Ctx) (A : Ty Γ) : Sub (.snoc Γ A) Γ
end

example : Sub (.snoc .nil (.base .nil)) .nil := .wk .nil (.base .nil)

/--
info: @Sub.rec : {motive_1 : Ctx → Sort u_1} →
  {motive_2 : (a : Ctx) → Ty a → Sort u_1} →
    {motive_3 : (a a_1 : Ctx) → Sub a a_1 → Sort u_1} →
      motive_1 Ctx.nil →
        ((Γ : Ctx) → (A : Ty Γ) → motive_1 Γ → motive_2 Γ A → motive_1 (Γ.snoc A)) →
          ((Γ : Ctx) → motive_1 Γ → motive_2 Γ (Ty.base Γ)) →
            ((Γ : Ctx) → motive_1 Γ → motive_3 Γ Γ (Sub.id Γ)) →
              ((Γ : Ctx) → (A : Ty Γ) → motive_1 Γ → motive_2 Γ A → motive_3 (Γ.snoc A) Γ (Sub.wk Γ A)) →
                {a a_1 : Ctx} → (t : Sub a a_1) → motive_3 a a_1 t
-/
#guard_msgs in
#check @Sub.rec

end TwoIdx

/-! ## The recursor computes

Both iota rules of an ind-ind block are definitional, and `rfl` is what says
so at a recursor applied by hand rather than through `induction`.
-/

namespace Iota

mutual
inductive Ctx : Type where
  | nil
  | snoc (Γ : Ctx) (A : Ty Γ) : Ctx
inductive Ty : Ctx → Type where
  | base (Γ : Ctx) : Ty Γ
end

def depth : Ctx → Nat :=
  Ctx.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    0 (fun _ _ n _ => n + 1) (fun _ _ => 0)

example : depth .nil = 0 := rfl
example : depth (.snoc .nil (.base .nil)) = 1 := rfl
example : depth (.snoc (.snoc .nil (.base .nil)) (.base _)) = 2 := rfl

end Iota

/-! ## Two propositions over one data member, each naming the other

The recursion is one recursion over all three, so each proposition's motive is
stated over the data member's motive and the two hypotheses are available to
each other.
-/

namespace EvenOdd

mutual
inductive Tm : Type where
  | z
  | s (t : Tm)
inductive Even : Tm → Prop where
  | z : Even .z
  | s (t : Tm) (h : Odd t) : Even (.s t)
inductive Odd : Tm → Prop where
  | s (t : Tm) (h : Even t) : Odd (.s t)
end

example : Even (.s (.s .z)) := .s _ (.s _ .z)

/--
info: @Even.rec : ∀ {motive_1 : Tm → Sort u_1} {motive_2 : (a : Tm) → motive_1 a → Even a → Prop}
  {motive_3 : (a : Tm) → motive_1 a → Odd a → Prop} (z : motive_1 Tm.z) (s : (t : Tm) → motive_1 t → motive_1 t.s)
  (z_1 : motive_2 Tm.z z Even.z)
  (s_1 : ∀ (t : Tm) (h : Odd t) (t_ih : motive_1 t), motive_3 t t_ih h → motive_2 t.s (s t t_ih) ⋯)
  (s_2 : ∀ (t : Tm) (h : Even t) (t_ih : motive_1 t), motive_2 t t_ih h → motive_3 t.s (s t t_ih) ⋯) {a : Tm}
  (h : Even a), motive_2 a (Tm.rec z s z_1 s_1 s_2 a) h
-/
#guard_msgs in
#check @Even.rec

end EvenOdd

end MumiTests.Boundary
