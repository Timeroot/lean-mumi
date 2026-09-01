/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import Mumi

/-!
# A `mutual` block whose members nest into each other

`MumiTests.Nested` and `MumiTests.GrandRec` cover a *single* `inductive` that
nests.  This file is the `mutual` version: a block Lean's own elaborator takes
as far as denesting and then hands to the kernel, which rejects the enlarged
block -- either because the copies land in more than one universe, or because a
copy is indexed by another copy and the enlarged block is induction-inductive.

Such a block is homogeneous as written, so `Mumi.Elab.classifyBlock` routes it
`.stock` and Lean gets it first; the retry in `Mumi.Rescue` picks it up only
after Lean has said no.  What comes back is one recursion over the writer's
members *and* every copy denesting made, spelled in the originals.

The nesting type used throughout is a well-formed binary tree, which is the
smallest thing that makes the enlarged block induction-inductive: copying
`WFTree` at a member drags in `Tree` and `Tree.WF`, and `Tree.WF` is indexed by
the copy of `Tree`.
-/

namespace Lib

inductive Tree (α : Type u) : Type u where
  | empty
  | node (a : α) (l r : Tree α)

inductive Tree.WF (α : Type u) : Tree α → Prop where
  | empty : Tree.WF α .empty
  | node (a : α) (l r : Tree α) (hl : Tree.WF α l) (hr : Tree.WF α r) :
      Tree.WF α (.node a l r)

inductive WFTree (α : Type u) : Type u where
  | mk (x : Tree α) (h : x.WF)

end Lib

open Lib

/-! ## Two members, each nesting the other

The block Lean sees after denesting has eight members: `A`, `B`, and a copy of
`WFTree`, `Tree` and `Tree.WF` at each of them.  So the recursion has eight
motives, and every one of them is spelled in the writer's own names --
`WFTree B`, not `A.nested_WFTree_1`.
-/

namespace Twin

mutual
inductive A : Type where
  | tip
  | mk (x : WFTree B)
inductive B : Type where
  | tip
  | mk (x : WFTree A)
end

/--
info: A.mk : WFTree B → A
-/
#guard_msgs in
#check @A.mk

/--
info: B.mk : WFTree A → B
-/
#guard_msgs in
#check @B.mk

/--
info: @A.rec : {motive_1 : A → Sort u_1} →
  {motive_2 : B → Sort u_1} →
    {motive_3 : WFTree B → Sort u_1} →
      {motive_4 : Tree B → Sort u_1} →
        {motive_5 : (a : Tree B) → motive_4 a → Tree.WF B a → Prop} →
          {motive_6 : WFTree A → Sort u_1} →
            {motive_7 : Tree A → Sort u_1} →
              {motive_8 : (a : Tree A) → motive_7 a → Tree.WF A a → Prop} →
                motive_1 A.tip →
                  ((x : WFTree B) → motive_3 x → motive_1 (A.mk x)) →
                    motive_2 B.tip →
                      ((x : WFTree A) → motive_6 x → motive_2 (B.mk x)) →
                        ((x : Tree B) →
                            (h : Tree.WF B x) → (x_ih : motive_4 x) → motive_5 x x_ih h → motive_3 (WFTree.mk x h)) →
                          (empty : motive_4 Tree.empty) →
                            (node :
                                (a : B) →
                                  (l r : Tree B) → motive_2 a → motive_4 l → motive_4 r → motive_4 (Tree.node a l r)) →
                              motive_5 Tree.empty empty ⋯ →
                                (∀ (a : B) (l r : Tree B) (hl : Tree.WF B l) (hr : Tree.WF B r) (a_ih : motive_2 a)
                                    (l_ih : motive_4 l) (r_ih : motive_4 r),
                                    motive_5 l l_ih hl →
                                      motive_5 r r_ih hr → motive_5 (Tree.node a l r) (node a l r a_ih l_ih r_ih) ⋯) →
                                  ((x : Tree A) →
                                      (h : Tree.WF A x) →
                                        (x_ih : motive_7 x) → motive_8 x x_ih h → motive_6 (WFTree.mk x h)) →
                                    (empty_2 : motive_7 Tree.empty) →
                                      (node_2 :
                                          (a : A) →
                                            (l r : Tree A) →
                                              motive_1 a → motive_7 l → motive_7 r → motive_7 (Tree.node a l r)) →
                                        motive_8 Tree.empty empty_2 ⋯ →
                                          (∀ (a : A) (l r : Tree A) (hl : Tree.WF A l) (hr : Tree.WF A r)
                                              (a_ih : motive_1 a) (l_ih : motive_7 l) (r_ih : motive_7 r),
                                              motive_8 l l_ih hl →
                                                motive_8 r r_ih hr →
                                                  motive_8 (Tree.node a l r) (node_2 a l r a_ih l_ih r_ih) ⋯) →
                                            (t : A) → motive_1 t
-/
#guard_msgs in
#check @A.rec

/-! The two recursors differ only in which motive the major premise concludes at. -/

/--
info: @B.rec : {motive_1 : A → Sort u_1} →
  {motive_2 : B → Sort u_1} →
    {motive_3 : WFTree B → Sort u_1} →
      {motive_4 : Tree B → Sort u_1} →
        {motive_5 : (a : Tree B) → motive_4 a → Tree.WF B a → Prop} →
          {motive_6 : WFTree A → Sort u_1} →
            {motive_7 : Tree A → Sort u_1} →
              {motive_8 : (a : Tree A) → motive_7 a → Tree.WF A a → Prop} →
                motive_1 A.tip →
                  ((x : WFTree B) → motive_3 x → motive_1 (A.mk x)) →
                    motive_2 B.tip →
                      ((x : WFTree A) → motive_6 x → motive_2 (B.mk x)) →
                        ((x : Tree B) →
                            (h : Tree.WF B x) → (x_ih : motive_4 x) → motive_5 x x_ih h → motive_3 (WFTree.mk x h)) →
                          (empty : motive_4 Tree.empty) →
                            (node :
                                (a : B) →
                                  (l r : Tree B) → motive_2 a → motive_4 l → motive_4 r → motive_4 (Tree.node a l r)) →
                              motive_5 Tree.empty empty ⋯ →
                                (∀ (a : B) (l r : Tree B) (hl : Tree.WF B l) (hr : Tree.WF B r) (a_ih : motive_2 a)
                                    (l_ih : motive_4 l) (r_ih : motive_4 r),
                                    motive_5 l l_ih hl →
                                      motive_5 r r_ih hr → motive_5 (Tree.node a l r) (node a l r a_ih l_ih r_ih) ⋯) →
                                  ((x : Tree A) →
                                      (h : Tree.WF A x) →
                                        (x_ih : motive_7 x) → motive_8 x x_ih h → motive_6 (WFTree.mk x h)) →
                                    (empty_2 : motive_7 Tree.empty) →
                                      (node_2 :
                                          (a : A) →
                                            (l r : Tree A) →
                                              motive_1 a → motive_7 l → motive_7 r → motive_7 (Tree.node a l r)) →
                                        motive_8 Tree.empty empty_2 ⋯ →
                                          (∀ (a : A) (l r : Tree A) (hl : Tree.WF A l) (hr : Tree.WF A r)
                                              (a_ih : motive_1 a) (l_ih : motive_7 l) (r_ih : motive_7 r),
                                              motive_8 l l_ih hl →
                                                motive_8 r r_ih hr →
                                                  motive_8 (Tree.node a l r) (node_2 a l r a_ih l_ih r_ih) ⋯) →
                                            (t : B) → motive_2 t
-/
#guard_msgs in
#check @B.rec

/-! The recursion computes, and the members' recursions really do cross. -/

/-- The number of `mk`s on the way down, counting through both members. -/
def size : A → Nat :=
  A.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat)
    (motive_3 := fun _ => Nat) (motive_4 := fun _ => Nat)
    (motive_5 := fun _ _ _ => True) (motive_6 := fun _ => Nat)
    (motive_7 := fun _ => Nat) (motive_8 := fun _ _ _ => True)
    0 (fun _ n => n + 1)
    0 (fun _ n => n + 1)
    (fun _ _ n _ => n) 0 (fun _ _ _ b l r => b + l + r)
    trivial (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ n _ => n) 0 (fun _ _ _ a l r => a + l + r)
    trivial (fun _ _ _ _ _ _ _ _ _ _ => trivial)

theorem leafWF (α : Type) : Tree.WF α .empty := .empty

def leafA : A := .mk (.mk .empty (leafWF _))
def leafB : B := .mk (.mk .empty (leafWF _))

example : size .tip = 0 := rfl
example : size leafA = 1 := rfl

/-- A tree of `A`s inside a `B` inside an `A`: the recursion crosses twice. -/
def deep : A :=
  .mk (.mk (.node (B.mk (.mk (.node A.tip .empty .empty)
      (.node _ _ _ (leafWF _) (leafWF _)))) .empty .empty)
    (.node _ _ _ (leafWF _) (leafWF _)))

example : size deep = 2 := rfl

/--
info: 'Twin.size' does not depend on any axioms
-/
#guard_msgs in
#print axioms size

end Twin

/-! ## One member nests itself, and the other only mentions it

`B` is not part of any copy, so its motive is there once and no copy of the
nesting type is made at it.
-/

namespace Self

mutual
inductive A : Type where
  | tip
  | mk (x : WFTree A)
inductive B : Type where
  | mk (a : A)
end

/--
info: @A.rec : {motive_1 : A → Sort u_1} →
  {motive_2 : B → Sort u_1} →
    {motive_3 : WFTree A → Sort u_1} →
      {motive_4 : Tree A → Sort u_1} →
        {motive_5 : (a : Tree A) → motive_4 a → Tree.WF A a → Prop} →
          motive_1 A.tip →
            ((x : WFTree A) → motive_3 x → motive_1 (A.mk x)) →
              ((a : A) → motive_1 a → motive_2 (B.mk a)) →
                ((x : Tree A) →
                    (h : Tree.WF A x) → (x_ih : motive_4 x) → motive_5 x x_ih h → motive_3 (WFTree.mk x h)) →
                  (empty : motive_4 Tree.empty) →
                    (node :
                        (a : A) → (l r : Tree A) → motive_1 a → motive_4 l → motive_4 r → motive_4 (Tree.node a l r)) →
                      motive_5 Tree.empty empty ⋯ →
                        (∀ (a : A) (l r : Tree A) (hl : Tree.WF A l) (hr : Tree.WF A r) (a_ih : motive_1 a)
                            (l_ih : motive_4 l) (r_ih : motive_4 r),
                            motive_5 l l_ih hl →
                              motive_5 r r_ih hr → motive_5 (Tree.node a l r) (node a l r a_ih l_ih r_ih) ⋯) →
                          (t : A) → motive_1 t
-/
#guard_msgs in
#check @A.rec

end Self

/-! ## Parameters

A parameter of the block becomes a parameter of every copy, so `WFTree (B α)`
stays `WFTree (B α)` and the recursor leads with `{α : Type}`.
-/

namespace Param

mutual
inductive A (α : Type) : Type where
  | tip (a : α)
  | mk (x : WFTree (B α))
inductive B (α : Type) : Type where
  | tip
  | up (a : A α)
end

/--
info: @A.mk : {α : Type} → WFTree (B α) → A α
-/
#guard_msgs in
#check @A.mk

/--
info: @A.rec : {α : Type} →
  {motive_1 : A α → Sort u_1} →
    {motive_2 : B α → Sort u_1} →
      {motive_3 : WFTree (B α) → Sort u_1} →
        {motive_4 : Tree (B α) → Sort u_1} →
          {motive_5 : (a : Tree (B α)) → motive_4 a → Tree.WF (B α) a → Prop} →
            ((a : α) → motive_1 (A.tip a)) →
              ((x : WFTree (B α)) → motive_3 x → motive_1 (A.mk x)) →
                motive_2 B.tip →
                  ((a : A α) → motive_1 a → motive_2 (B.up a)) →
                    ((x : Tree (B α)) →
                        (h : Tree.WF (B α) x) → (x_ih : motive_4 x) → motive_5 x x_ih h → motive_3 (WFTree.mk x h)) →
                      (empty : motive_4 Tree.empty) →
                        (node :
                            (a : B α) →
                              (l r : Tree (B α)) → motive_2 a → motive_4 l → motive_4 r → motive_4 (Tree.node a l r)) →
                          motive_5 Tree.empty empty ⋯ →
                            (∀ (a : B α) (l r : Tree (B α)) (hl : Tree.WF (B α) l) (hr : Tree.WF (B α) r)
                                (a_ih : motive_2 a) (l_ih : motive_4 l) (r_ih : motive_4 r),
                                motive_5 l l_ih hl →
                                  motive_5 r r_ih hr → motive_5 (Tree.node a l r) (node a l r a_ih l_ih r_ih) ⋯) →
                              (t : A α) → motive_1 t
-/
#guard_msgs in
#check @A.rec

end Param

/-! ## Nesting two deep

`WFTree (WFTree B)` copies the whole family twice over, at `B` and at the copy
of `WFTree` at `B`, and both layers show up as motives of their own.
-/

namespace Deep

mutual
inductive A : Type where
  | tip
  | mk (x : WFTree (WFTree B))
inductive B : Type where
  | tip
end

/--
info: @A.rec : {motive_1 : A → Sort u_1} →
  {motive_2 : B → Sort u_1} →
    {motive_3 : WFTree (WFTree B) → Sort u_1} →
      {motive_4 : Tree (WFTree B) → Sort u_1} →
        {motive_5 : WFTree B → Sort u_1} →
          {motive_6 : Tree B → Sort u_1} →
            {motive_7 : (a : Tree B) → motive_6 a → Tree.WF B a → Prop} →
              {motive_8 : (a : Tree (WFTree B)) → motive_4 a → Tree.WF (WFTree B) a → Prop} →
                motive_1 A.tip →
                  ((x : WFTree (WFTree B)) → motive_3 x → motive_1 (A.mk x)) →
                    motive_2 B.tip →
                      ((x : Tree (WFTree B)) →
                          (h : Tree.WF (WFTree B) x) →
                            (x_ih : motive_4 x) → motive_8 x x_ih h → motive_3 (WFTree.mk x h)) →
                        (empty : motive_4 Tree.empty) →
                          (node :
                              (a : WFTree B) →
                                (l r : Tree (WFTree B)) →
                                  motive_5 a → motive_4 l → motive_4 r → motive_4 (Tree.node a l r)) →
                            ((x : Tree B) →
                                (h : Tree.WF B x) →
                                  (x_ih : motive_6 x) → motive_7 x x_ih h → motive_5 (WFTree.mk x h)) →
                              (empty_1 : motive_6 Tree.empty) →
                                (node_1 :
                                    (a : B) →
                                      (l r : Tree B) →
                                        motive_2 a → motive_6 l → motive_6 r → motive_6 (Tree.node a l r)) →
                                  motive_7 Tree.empty empty_1 ⋯ →
                                    (∀ (a : B) (l r : Tree B) (hl : Tree.WF B l) (hr : Tree.WF B r) (a_ih : motive_2 a)
                                        (l_ih : motive_6 l) (r_ih : motive_6 r),
                                        motive_7 l l_ih hl →
                                          motive_7 r r_ih hr →
                                            motive_7 (Tree.node a l r) (node_1 a l r a_ih l_ih r_ih) ⋯) →
                                      motive_8 Tree.empty empty ⋯ →
                                        (∀ (a : WFTree B) (l r : Tree (WFTree B)) (hl : Tree.WF (WFTree B) l)
                                            (hr : Tree.WF (WFTree B) r) (a_ih : motive_5 a) (l_ih : motive_4 l)
                                            (r_ih : motive_4 r),
                                            motive_8 l l_ih hl →
                                              motive_8 r r_ih hr →
                                                motive_8 (Tree.node a l r) (node a l r a_ih l_ih r_ih) ⋯) →
                                          (t : A) → motive_1 t
-/
#guard_msgs in
#check @A.rec

end Deep

/-! ## A nesting Lean can do, wrapped around one it cannot

`List B` is a nesting the kernel handles by itself, and `WFTree B` is not.  Both
appear, and the block still goes through: Lean's denesting is what produces the
enlarged block in the first place, so the copy of `List` is one of its members
like any other.
-/

namespace Mixed

mutual
inductive A : Type where
  | tip
  | mk (x : WFTree B) (l : List B)
inductive B : Type where
  | tip
end

/--
info: A.mk : WFTree B → List B → A
-/
#guard_msgs in
#check @A.mk

/--
info: @A.rec : {motive_1 : A → Sort u_1} →
  {motive_2 : B → Sort u_1} →
    {motive_3 : WFTree B → Sort u_1} →
      {motive_4 : Tree B → Sort u_1} →
        {motive_5 : (a : Tree B) → motive_4 a → Tree.WF B a → Prop} →
          {motive_6 : List B → Sort u_1} →
            motive_1 A.tip →
              ((x : WFTree B) → (l : List B) → motive_3 x → motive_6 l → motive_1 (A.mk x l)) →
                motive_2 B.tip →
                  ((x : Tree B) →
                      (h : Tree.WF B x) → (x_ih : motive_4 x) → motive_5 x x_ih h → motive_3 (WFTree.mk x h)) →
                    (empty : motive_4 Tree.empty) →
                      (node :
                          (a : B) →
                            (l r : Tree B) → motive_2 a → motive_4 l → motive_4 r → motive_4 (Tree.node a l r)) →
                        motive_5 Tree.empty empty ⋯ →
                          (∀ (a : B) (l r : Tree B) (hl : Tree.WF B l) (hr : Tree.WF B r) (a_ih : motive_2 a)
                              (l_ih : motive_4 l) (r_ih : motive_4 r),
                              motive_5 l l_ih hl →
                                motive_5 r r_ih hr → motive_5 (Tree.node a l r) (node a l r a_ih l_ih r_ih) ⋯) →
                            motive_6 [] →
                              ((head : B) → (tail : List B) → motive_2 head → motive_6 tail → motive_6 (head :: tail)) →
                                (t : A) → motive_1 t
-/
#guard_msgs in
#check @A.rec

end Mixed

/-! ## A nesting over both members at once

`Prod A B` is copied once, and its motive is over the pair; the minor gets an
induction hypothesis for each side.
-/

namespace Pair

mutual
inductive A : Type where
  | tip
  | mk (x : WFTree (A × B))
inductive B : Type where
  | tip
end

/--
info: @A.rec : {motive_1 : A → Sort u_1} →
  {motive_2 : B → Sort u_1} →
    {motive_3 : WFTree (A × B) → Sort u_1} →
      {motive_4 : Tree (A × B) → Sort u_1} →
        {motive_5 : A × B → Sort u_1} →
          {motive_6 : (a : Tree (A × B)) → motive_4 a → Tree.WF (A × B) a → Prop} →
            motive_1 A.tip →
              ((x : WFTree (A × B)) → motive_3 x → motive_1 (A.mk x)) →
                motive_2 B.tip →
                  ((x : Tree (A × B)) →
                      (h : Tree.WF (A × B) x) → (x_ih : motive_4 x) → motive_6 x x_ih h → motive_3 (WFTree.mk x h)) →
                    (empty : motive_4 Tree.empty) →
                      (node :
                          (a : A × B) →
                            (l r : Tree (A × B)) → motive_5 a → motive_4 l → motive_4 r → motive_4 (Tree.node a l r)) →
                        ((fst : A) → (snd : B) → motive_1 fst → motive_2 snd → motive_5 (fst, snd)) →
                          motive_6 Tree.empty empty ⋯ →
                            (∀ (a : A × B) (l r : Tree (A × B)) (hl : Tree.WF (A × B) l) (hr : Tree.WF (A × B) r)
                                (a_ih : motive_5 a) (l_ih : motive_4 l) (r_ih : motive_4 r),
                                motive_6 l l_ih hl →
                                  motive_6 r r_ih hr → motive_6 (Tree.node a l r) (node a l r a_ih l_ih r_ih) ⋯) →
                              (t : A) → motive_1 t
-/
#guard_msgs in
#check @A.rec

end Pair

/-! ## An indexed member

The index is carried through the copies, and -- as for any recursor -- is bound
implicitly in the major premise.
-/

namespace Indexed

mutual
inductive A : Nat → Type where
  | tip : A 0
  | mk (n : Nat) (x : WFTree B) : A (n + 1)
inductive B : Type where
  | tip
  | up (n : Nat) (a : A n)
end

/--
info: A.mk : (n : Nat) → WFTree B → A (n + 1)
-/
#guard_msgs in
#check @A.mk

/--
info: B.up : (n : Nat) → A n → B
-/
#guard_msgs in
#check @B.up

/--
info: @A.rec : {motive_1 : (a : Nat) → A a → Sort u_1} →
  {motive_2 : B → Sort u_1} →
    {motive_3 : WFTree B → Sort u_1} →
      {motive_4 : Tree B → Sort u_1} →
        {motive_5 : (a : Tree B) → motive_4 a → Tree.WF B a → Prop} →
          motive_1 0 A.tip →
            ((n : Nat) → (x : WFTree B) → motive_3 x → motive_1 (n + 1) (A.mk n x)) →
              motive_2 B.tip →
                ((n : Nat) → (a : A n) → motive_1 n a → motive_2 (B.up n a)) →
                  ((x : Tree B) →
                      (h : Tree.WF B x) → (x_ih : motive_4 x) → motive_5 x x_ih h → motive_3 (WFTree.mk x h)) →
                    (empty : motive_4 Tree.empty) →
                      (node :
                          (a : B) →
                            (l r : Tree B) → motive_2 a → motive_4 l → motive_4 r → motive_4 (Tree.node a l r)) →
                        motive_5 Tree.empty empty ⋯ →
                          (∀ (a : B) (l r : Tree B) (hl : Tree.WF B l) (hr : Tree.WF B r) (a_ih : motive_2 a)
                              (l_ih : motive_4 l) (r_ih : motive_4 r),
                              motive_5 l l_ih hl →
                                motive_5 r r_ih hr → motive_5 (Tree.node a l r) (node a l r a_ih l_ih r_ih) ⋯) →
                            {a : Nat} → (t : A a) → motive_1 a t
-/
#guard_msgs in
#check @A.rec

end Indexed

/-! ## Modifiers

A docstring and a `private` survive the round trip.  `private` comes for free,
since the members are declared under the names the writer's own views carry;
the docstrings are re-attached afterwards, from those views, exactly as Lean's
inductive elaborator attaches its own.

What does not survive is `inductive` itself: a member of an induction-inductive
block is a `def` for the subtype its pre-type carves out, so `#print` shows the
encoding.  That is the trade the whole library makes, and the recursors above
are what make it one worth taking.
-/

namespace Modifiers

mutual
/-- The one with the nesting. -/
inductive A : Type where
  | tip
  /-- The nesting itself. -/
  | mk (x : WFTree B)
private inductive B : Type where
  | tip
end

/--
info: A: some (The one with the nesting. ), A.mk: some (The nesting itself. )
-/
#guard_msgs in
open Lean in
run_meta logInfo m!"A: {← findDocString? (← getEnv) ``A}, \
  A.mk: {← findDocString? (← getEnv) ``A.mk}"

/--
info: A is private: false, B is private: true
-/
#guard_msgs in
open Lean in
run_meta logInfo m!"A is private: {isPrivateName ``A}, B is private: {isPrivateName ``B}"

/--
info: def Modifiers.A : Type :=
Subtype A._wf
-/
#guard_msgs in
#print A

end Modifiers

/-! ## Heterogeneous only because of a `Prop`

A block with a free-standing `Prop` member is heterogeneous, so `classifyBlock`
routes it away from Lean and to `Mumi.Lowering` -- which does not denest.  The
retry catches that too: lowering fails, and the same induction-inductive path
takes the block whole.

The data members get the recursion over the copies.  The `Prop` member is not
indexed by a data member, so it is not part of that recursion and gets a
recursor of its own -- one motive, exactly Lean's own shape, and registered as
the `induction` tactic's default.
-/

namespace FreeProp

mutual
inductive A : Type where
  | tip
  | mk (x : WFTree B)
inductive B : Type where
  | tip
inductive P : Nat → Prop where
  | z : P 0
  | s (n : Nat) : P n → P (n + 1)
end

/--
info: @A.rec : {motive_1 : A → Sort u_1} →
  {motive_2 : B → Sort u_1} →
    {motive_3 : WFTree B → Sort u_1} →
      {motive_4 : Tree B → Sort u_1} →
        {motive_5 : (a : Tree B) → motive_4 a → Tree.WF B a → Prop} →
          motive_1 A.tip →
            ((x : WFTree B) → motive_3 x → motive_1 (A.mk x)) →
              motive_2 B.tip →
                ((x : Tree B) →
                    (h : Tree.WF B x) → (x_ih : motive_4 x) → motive_5 x x_ih h → motive_3 (WFTree.mk x h)) →
                  (empty : motive_4 Tree.empty) →
                    (node :
                        (a : B) → (l r : Tree B) → motive_2 a → motive_4 l → motive_4 r → motive_4 (Tree.node a l r)) →
                      motive_5 Tree.empty empty ⋯ →
                        (∀ (a : B) (l r : Tree B) (hl : Tree.WF B l) (hr : Tree.WF B r) (a_ih : motive_2 a)
                            (l_ih : motive_4 l) (r_ih : motive_4 r),
                            motive_5 l l_ih hl →
                              motive_5 r r_ih hr → motive_5 (Tree.node a l r) (node a l r a_ih l_ih r_ih) ⋯) →
                          (t : A) → motive_1 t
-/
#guard_msgs in
#check @A.rec

/--
info: @P.rec : ∀ {motive : (a : Nat) → P a → Prop},
  motive 0 P.z → (∀ (n : Nat) (a : P n), motive n a → motive (n + 1) ⋯) → ∀ {a : Nat} (h : P a), motive a h
-/
#guard_msgs in
#check @P.rec

theorem P.pos : ∀ {n}, P n → 0 ≤ n := by
  intro n h
  induction h with
  | z => exact Nat.le_refl 0
  | s m _ ih => exact Nat.zero_le _

/--
info: 'FreeProp.P.pos' does not depend on any axioms
-/
#guard_msgs in
#print axioms P.pos

end FreeProp

/-! Same block, but the `Prop` mentions a data member in a *field* rather than
being indexed by one.  It is still not indexed by one, so nothing changes about
the routing. -/

namespace FreePropField

mutual
inductive A : Type where
  | tip
  | mk (x : WFTree B)
inductive B : Type where
  | tip
inductive P : Nat → Prop where
  | z (a : A) : P 0
end

/--
info: @A.rec : {motive_1 : A → Sort u_1} →
  {motive_2 : B → Sort u_1} →
    {motive_3 : WFTree B → Sort u_1} →
      {motive_4 : Tree B → Sort u_1} →
        {motive_5 : (a : Tree B) → motive_4 a → Tree.WF B a → Prop} →
          motive_1 A.tip →
            ((x : WFTree B) → motive_3 x → motive_1 (A.mk x)) →
              motive_2 B.tip →
                ((x : Tree B) →
                    (h : Tree.WF B x) → (x_ih : motive_4 x) → motive_5 x x_ih h → motive_3 (WFTree.mk x h)) →
                  (empty : motive_4 Tree.empty) →
                    (node :
                        (a : B) → (l r : Tree B) → motive_2 a → motive_4 l → motive_4 r → motive_4 (Tree.node a l r)) →
                      motive_5 Tree.empty empty ⋯ →
                        (∀ (a : B) (l r : Tree B) (hl : Tree.WF B l) (hr : Tree.WF B r) (a_ih : motive_2 a)
                            (l_ih : motive_4 l) (r_ih : motive_4 r),
                            motive_5 l l_ih hl →
                              motive_5 r r_ih hr → motive_5 (Tree.node a l r) (node a l r a_ih l_ih r_ih) ⋯) →
                          (t : A) → motive_1 t
-/
#guard_msgs in
#check @A.rec

/--
info: P.z : ∀ (a : A), P 0
-/
#guard_msgs in
#check @P.z

end FreePropField

/-! ## Both restrictions at once: different universes *and* a denesting

Erasure and lowering lift two different rules of the kernel's, and one block can
break both.  `A` is at `Type 1` and `B` at `Type`, so they cannot be one mutual
inductive; and `A` nests `WFTree B`, whose specialisation carries a `Tree.WF`
proof, so lowering on its own cannot denest it either.

They compose in that order.  Erasure goes first and takes the proof field out,
and what it leaves behind is an ordinary mutual block that merely happens to be
heterogeneous -- which is exactly what `Mumi.Lowering` emits.  Neither pass has
to know anything about the other's problem: erasure never looks at a universe,
and the lowering never sees an arity that mentions the block.

The constructor still reads the way it was written, and the recursor ranges over
the two members the writer declared and the three copies denesting added, all
stated over the originals.
-/

namespace BigSmall

mutual
inductive A : Type 1 where
  | tip
  | mk (x : WFTree B)
inductive B : Type where
  | tip
end

/-- info: A.mk : WFTree B → A -/
#guard_msgs in
#check @A.mk

/--
info: @A.rec : {motive_1 : A → Sort u_1} →
  {motive_2 : B → Sort u_1} →
    {motive_3 : WFTree B → Sort u_1} →
      {motive_4 : Tree B → Sort u_1} →
        {motive_5 : (a : Tree B) → motive_4 a → Tree.WF B a → Prop} →
          motive_1 A.tip →
            ((x : WFTree B) → motive_3 x → motive_1 (A.mk x)) →
              motive_2 B.tip →
                ((x : Tree B) →
                    (h : Tree.WF B x) → (x_ih : motive_4 x) → motive_5 x x_ih h → motive_3 (WFTree.mk x h)) →
                  (empty : motive_4 Tree.empty) →
                    (node :
                        (a : B) → (l r : Tree B) → motive_2 a → motive_4 l → motive_4 r → motive_4 (Tree.node a l r)) →
                      motive_5 Tree.empty empty ⋯ →
                        (∀ (a : B) (l r : Tree B) (hl : Tree.WF B l) (hr : Tree.WF B r) (a_ih : motive_2 a)
                            (l_ih : motive_4 l) (r_ih : motive_4 r),
                            motive_5 l l_ih hl →
                              motive_5 r r_ih hr → motive_5 (Tree.node a l r) (node a l r a_ih l_ih r_ih) ⋯) →
                          (t : A) → motive_1 t
-/
#guard_msgs in
#check @A.rec

end BigSmall

/-! ## A denesting the lowering takes on its own

Every block above nests `WFTree`, which is what makes the enlarged block
induction-inductive and so puts it in `Mumi.IndInd`'s hands.  Nest a plain
`Tree` instead and the enlarged block is heterogeneous and nothing more, so the
induction-inductive retry declines it and `Mumi.Lowering` is what takes it.

The two routes relate a copy to its original differently, and it shows.
`Mumi.IndInd` defines the constructors over the originals outright, so `A.mk`
above reads `WFTree B`.  The lowering leaves the kernel's constructor alone and
registers a coercion each way instead, so `S.t` reads the copy.  That is the
honest thing to print: a data copy is only *isomorphic* to what it copies, not
equal to it, and `Mumi.Bridge` displays a copy as its original only for the
`Prop` copies, where an equality licenses it.

What the coercion buys is that nobody has to build a copy.  A `Tree S` goes
straight into `S.t`, whether it is a value or a variable, and the block computes.
-/

namespace LowerNest

mutual
inductive S : Type where
  | nil
  | t : Tree S → S
inductive Big : Type 1 where
  | of : Type → Big
  | c : S → Big
end

/-- info: S.t : S.nested_Tree_1 → S -/
#guard_msgs in
#check @S.t

/-- info: Big.c : S → Big -/
#guard_msgs in
#check @Big.c

/--
info: @S.mutualRec : {motive_1 : S → Sort u_1} →
  {motive_2 : Big → Sort u_2} →
    {motive_3 : S.nested_Tree_1 → Sort u_1} →
      motive_1 S.nil →
        ((a : S.nested_Tree_1) → motive_3 a → motive_1 (S.t a)) →
          ((a : Type) → motive_2 (Big.of a)) →
            ((a : S) → motive_1 a → motive_2 (Big.c a)) →
              motive_3 S.nested_Tree_1.empty →
                ((a : S) →
                    (l r : S.nested_Tree_1) →
                      motive_1 a → motive_3 l → motive_3 r → motive_3 (S.nested_Tree_1.node a l r)) →
                  (t : S) → motive_1 t
-/
#guard_msgs in
#check @S.mutualRec

-- the field's type is the copy, and what goes into it is a `Tree S`
def tr : Tree S := .node .nil .empty .empty
def s1 : S := S.t tr

-- not only closed values: a variable of the original type goes in too
example (t : Tree S) : S := S.t t

def S.size (x : S) : Nat :=
  S.mutualRec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat)
    (motive_3 := fun _ => Nat)
    0 (fun _ ih => ih + 1) (fun _ => 0) (fun _ ih => ih)
    0 (fun _ _ _ iha ihl ihr => iha + ihl + ihr) x

example : S.nil.size = 0 := rfl
example : s1.size = 1 := rfl

/-- info: 1 -/
#guard_msgs in
#eval s1.size

example : (match s1 with | .nil => 0 | .t _ => 1 : Nat) = 1 := rfl

-- `cases` needs no recursor and works as it would on any other block.
-- (`induction` does not, but that is Lean: it refuses every mutually
-- inductive type, lowered or not.)
example (x : S) : x = .nil ∨ ∃ t, x = .t t := by
  cases x with
  | nil => exact .inl rfl
  | t t => exact .inr ⟨t, rfl⟩

/-
Structural recursion is where the copy stops being only a matter of display.
A function that recurses into the nesting needs a companion at the nested
type, and the companion has to be stated at the copy: `S.t`'s field *is* a
`S.nested_Tree_1`, and the coercion that lets a `Tree S` be passed in is a
function, so a `Tree S` argument is not a subterm of anything and no measure
decreases.  Written at the copy it goes through, and computes.

This is the same gap as the signature above, from the other side.  Displaying
the copy as `Tree S` would not help -- the name would still have to be written
to make the definition typecheck -- so what it would take is `Mumi.IndInd`'s
bridge, which states the block over the originals outright.  The lowering has
no such bridge.
-/
mutual
def sz : S → Nat
  | .nil => 1
  | .t t => 1 + szT t
def szT : S.nested_Tree_1 → Nat
  | .empty => 0
  | .node a l r => sz a + szT l + szT r
end

/-- info: 2 -/
#guard_msgs in
#eval sz s1

end LowerNest

/-! ## Limits

### A nesting the kernel *can* do, in a heterogeneous block

Here lowering succeeds, so the retry never runs, and the copy `List` was
specialised into is a member of the block under its generated name.  That name
is visible in the recursor.  It is a wart, not a soundness question: the block
is the one the kernel would have built for a homogeneous version of the same
declaration.

The ind-ind route would have stated the block over `List B` itself, and since
its pre-block goes through the lowering too it could now take this one -- but it
is a retry, and a retry only runs when the route ahead of it failed.  `BigSmall`
above is the same shape with a nesting lowering *cannot* do, and there the retry
does run and the written form survives.  Which of the two you get is decided by
whether the first route works, not by which reads better.

Nothing can be done about the name in the recursor: the copy is a data member,
only isomorphic to `List B` and not equal to it, so displaying it as `List B`
would be a lie.  What *can* be done is to make the name unnecessary anywhere
else, and that is what the isomorphism and its two coercions are for.
-/

namespace ListBig

mutual
inductive A : Type 1 where
  | tip
  | mk (x : List B)
inductive B : Type where
  | tip
end

/--
info: @A.rec : {motive : A → Sort u_1} → motive A.tip → ((x : A.nested_List_1) → motive (A.mk x)) → (t : A) → motive t
-/
#guard_msgs in
#check @A.rec

/-- info: A.nested_List_1.toOrig : A.nested_List_1 → List B -/
#guard_msgs in
#check @A.nested_List_1.toOrig

/-- info: A.nested_List_1.ofOrig : List B → A.nested_List_1 -/
#guard_msgs in
#check @A.nested_List_1.ofOrig

/-! A `List B` goes into the constructor, and what comes back out of a match is
usable as a `List B`.  Neither writes the copy's name, and both run. -/

def size : A → Nat
  | .tip => 0
  | .mk x => (x : List B).length

/-- info: 2 -/
#guard_msgs in
#eval size (A.mk [B.tip, B.tip])

/-- info: 'ListBig.size' does not depend on any axioms -/
#guard_msgs in
#print axioms size

/-! There is no equation between the two types, and none is claimed. -/

/-- error: Unknown constant `ListBig.A.nested_List_1.eq_orig` -/
#guard_msgs in
#check @A.nested_List_1.eq_orig

end ListBig
