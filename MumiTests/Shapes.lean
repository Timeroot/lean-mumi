/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import Mumi

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

/-! ## Nesting inside nesting

`WFTree (WFTree R)` copies the whole family twice over, once at `R` and once at
`WFTree R`, and the outer copy's parameters mention the inner copy.  The two
copies of `Tree` are *different types*, so the order the copies get built in has
to be a sort of the copies themselves; sorting the types they were copied from
has `Tree` waiting on `Tree` and the whole block falling back to leaving the
copies visible.
-/

namespace Deep

inductive R where
  | mk (x : WFTree (WFTree R))

/--
info: @R.rec : {motive_1 : R → Sort u_1} →
  {motive_2 : WFTree (WFTree R) → Sort u_1} →
    {motive_3 : Tree (WFTree R) → Sort u_1} →
      {motive_4 : WFTree R → Sort u_1} →
        {motive_5 : Tree R → Sort u_1} →
          {motive_6 : (a : Tree R) → motive_5 a → Tree.WF R a → Prop} →
            {motive_7 : (a : Tree (WFTree R)) → motive_3 a → Tree.WF (WFTree R) a → Prop} →
              ((x : WFTree (WFTree R)) → motive_2 x → motive_1 (R.mk x)) →
                ((x : Tree (WFTree R)) →
                    (h : Tree.WF (WFTree R) x) → (x_ih : motive_3 x) → motive_7 x x_ih h → motive_2 (WFTree.mk x h)) →
                  (empty : motive_3 Tree.empty) →
                    (node :
                        (a : WFTree R) →
                          (l r : Tree (WFTree R)) → motive_4 a → motive_3 l → motive_3 r → motive_3 (Tree.node a l r)) →
                      ((x : Tree R) →
                          (h : Tree.WF R x) → (x_ih : motive_5 x) → motive_6 x x_ih h → motive_4 (WFTree.mk x h)) →
                        (empty_1 : motive_5 Tree.empty) →
                          (node_1 :
                              (a : R) →
                                (l r : Tree R) → motive_1 a → motive_5 l → motive_5 r → motive_5 (Tree.node a l r)) →
                            motive_6 Tree.empty empty_1 ⋯ →
                              (∀ (a : R) (l r : Tree R) (hl : Tree.WF R l) (hr : Tree.WF R r) (a_ih : motive_1 a)
                                  (l_ih : motive_5 l) (r_ih : motive_5 r),
                                  motive_6 l l_ih hl →
                                    motive_6 r r_ih hr → motive_6 (Tree.node a l r) (node_1 a l r a_ih l_ih r_ih) ⋯) →
                                motive_7 Tree.empty empty ⋯ →
                                  (∀ (a : WFTree R) (l r : Tree (WFTree R)) (hl : Tree.WF (WFTree R) l)
                                      (hr : Tree.WF (WFTree R) r) (a_ih : motive_4 a) (l_ih : motive_3 l)
                                      (r_ih : motive_3 r),
                                      motive_7 l l_ih hl →
                                        motive_7 r r_ih hr → motive_7 (Tree.node a l r) (node a l r a_ih l_ih r_ih) ⋯) →
                                    (t : R) → motive_1 t
-/
#guard_msgs in
#check @R.rec

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
    (motive_4 := fun _ => Nat) (motive_5 := fun _ => Nat)
    (motive_6 := fun _ _ _ => True) (motive_7 := fun _ _ _ => True)
    (fun _ ih => 1 + ih)
    (fun _ _ ih _ => ih)
    0 (fun _ _ _ iha ihl ihr => iha + ihl + ihr)
    (fun _ _ ih _ => ih)
    0 (fun _ _ _ iha ihl ihr => iha + ihl + ihr)
    trivial (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    trivial (fun _ _ _ _ _ _ _ _ _ _ => trivial)

example : size base = 1 := rfl
example : size (wrap (lift base)) = 2 := rfl

/--
Rebuilding, which is what the two predicate motives are for.

The minor for `WFTree.mk` is handed a proof that the tree it was *given* is well
formed and has to produce one about the tree the recursion *built*; `motive_6`
and `motive_7` are what carry that across, one for each copy of `Tree.WF`.
-/
def rebuild : R → R :=
  R.rec (motive_1 := fun _ => R) (motive_2 := fun _ => WFTree (WFTree R))
    (motive_3 := fun _ => Tree (WFTree R)) (motive_4 := fun _ => WFTree R)
    (motive_5 := fun _ => Tree R)
    (motive_6 := fun _ ih _ => Tree.WF R ih)
    (motive_7 := fun _ ih _ => Tree.WF (WFTree R) ih)
    (fun _ ih => .mk ih)
    (fun _ _ ih hw => .mk ih hw)
    .empty (fun _ _ _ iha ihl ihr => .node iha ihl ihr)
    (fun _ _ ih hw => .mk ih hw)
    .empty (fun _ _ _ iha ihl ihr => .node iha ihl ihr)
    .empty (fun _ _ _ _ _ iha ihl ihr hl hr => .node iha ihl ihr hl hr)
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

inductive R where
  | mk (xs : List (WFTree R))

/--
info: @R.rec : {motive_1 : R → Sort u_1} →
  {motive_2 : List (WFTree R) → Sort u_1} →
    {motive_3 : WFTree R → Sort u_1} →
      {motive_4 : Tree R → Sort u_1} →
        {motive_5 : (a : Tree R) → motive_4 a → Tree.WF R a → Prop} →
          ((xs : List (WFTree R)) → motive_2 xs → motive_1 (R.mk xs)) →
            motive_2 [] →
              ((head : WFTree R) → (tail : List (WFTree R)) → motive_3 head → motive_2 tail → motive_2 (head :: tail)) →
                ((x : Tree R) →
                    (h : Tree.WF R x) → (x_ih : motive_4 x) → motive_5 x x_ih h → motive_3 (WFTree.mk x h)) →
                  (empty : motive_4 Tree.empty) →
                    (node :
                        (a : R) → (l r : Tree R) → motive_1 a → motive_4 l → motive_4 r → motive_4 (Tree.node a l r)) →
                      motive_5 Tree.empty empty ⋯ →
                        (∀ (a : R) (l r : Tree R) (hl : Tree.WF R l) (hr : Tree.WF R r) (a_ih : motive_1 a)
                            (l_ih : motive_4 l) (r_ih : motive_4 r),
                            motive_5 l l_ih hl →
                              motive_5 r r_ih hr → motive_5 (Tree.node a l r) (node a l r a_ih l_ih r_ih) ⋯) →
                          (t : R) → motive_1 t
-/
#guard_msgs in
#check @R.rec

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

inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons {n : Nat} (a : α) (v : Vec α n) : Vec α (n + 1)

inductive Vec.Up (α : Type) : (n : Nat) → Vec α n → Prop where
  | nil : Vec.Up α 0 .nil
  | cons {n : Nat} (a : α) (v : Vec α n) (h : Vec.Up α n v) :
      Vec.Up α (n + 1) (.cons a v)

inductive UVec (α : Type) (n : Nat) where
  | mk (v : Vec α n) (h : Vec.Up α n v)

inductive R where
  | tip
  | mk (x : UVec R 2)

/--
info: @R.rec : {motive_1 : R → Sort u_1} →
  {motive_2 : UVec R 2 → Sort u_1} →
    {motive_3 : (a : Nat) → Vec R a → Sort u_1} →
      {motive_4 : (n : Nat) → (a : Vec R n) → motive_3 n a → Vec.Up R n a → Prop} →
        motive_1 R.tip →
          ((x : UVec R 2) → motive_2 x → motive_1 (R.mk x)) →
            ((v : Vec R 2) →
                (h : Vec.Up R 2 v) → (v_ih : motive_3 2 v) → motive_4 2 v v_ih h → motive_2 (UVec.mk v h)) →
              (nil : motive_3 0 Vec.nil) →
                (cons :
                    {n : Nat} → (a : R) → (v : Vec R n) → motive_1 a → motive_3 n v → motive_3 (n + 1) (Vec.cons a v)) →
                  motive_4 0 Vec.nil nil ⋯ →
                    (∀ {n : Nat} (a : R) (v : Vec R n) (h : Vec.Up R n v) (a_ih : motive_1 a) (v_ih : motive_3 n v),
                        motive_4 n v v_ih h → motive_4 (n + 1) (Vec.cons a v) (cons a v a_ih v_ih) ⋯) →
                      (t : R) → motive_1 t
-/
#guard_msgs in
#check @R.rec

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

inductive R where
  | tip
  | mk (x : WFTree R) (y : WFTree R)

/--
info: @R.rec : {motive_1 : R → Sort u_1} →
  {motive_2 : WFTree R → Sort u_1} →
    {motive_3 : Tree R → Sort u_1} →
      {motive_4 : (a : Tree R) → motive_3 a → Tree.WF R a → Prop} →
        motive_1 R.tip →
          ((x y : WFTree R) → motive_2 x → motive_2 y → motive_1 (R.mk x y)) →
            ((x : Tree R) → (h : Tree.WF R x) → (x_ih : motive_3 x) → motive_4 x x_ih h → motive_2 (WFTree.mk x h)) →
              (empty : motive_3 Tree.empty) →
                (node : (a : R) → (l r : Tree R) → motive_1 a → motive_3 l → motive_3 r → motive_3 (Tree.node a l r)) →
                  motive_4 Tree.empty empty ⋯ →
                    (∀ (a : R) (l r : Tree R) (hl : Tree.WF R l) (hr : Tree.WF R r) (a_ih : motive_1 a)
                        (l_ih : motive_3 l) (r_ih : motive_3 r),
                        motive_4 l l_ih hl →
                          motive_4 r r_ih hr → motive_4 (Tree.node a l r) (node a l r a_ih l_ih r_ih) ⋯) →
                      (t : R) → motive_1 t
-/
#guard_msgs in
#check @R.rec

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

inductive R (β : Type u) : Type u where
  | leaf (b : β)
  | mk (x : WFTree (R β))

/--
info: @R.rec : {β : Type u_2} →
  {motive_1 : R β → Sort u_1} →
    {motive_2 : WFTree (R β) → Sort u_1} →
      {motive_3 : Tree (R β) → Sort u_1} →
        {motive_4 : (a : Tree (R β)) → motive_3 a → Tree.WF (R β) a → Prop} →
          ((b : β) → motive_1 (R.leaf b)) →
            ((x : WFTree (R β)) → motive_2 x → motive_1 (R.mk x)) →
              ((x : Tree (R β)) →
                  (h : Tree.WF (R β) x) → (x_ih : motive_3 x) → motive_4 x x_ih h → motive_2 (WFTree.mk x h)) →
                (empty : motive_3 Tree.empty) →
                  (node :
                      (a : R β) →
                        (l r : Tree (R β)) → motive_1 a → motive_3 l → motive_3 r → motive_3 (Tree.node a l r)) →
                    motive_4 Tree.empty empty ⋯ →
                      (∀ (a : R β) (l r : Tree (R β)) (hl : Tree.WF (R β) l) (hr : Tree.WF (R β) r) (a_ih : motive_1 a)
                          (l_ih : motive_3 l) (r_ih : motive_3 r),
                          motive_4 l l_ih hl →
                            motive_4 r r_ih hr → motive_4 (Tree.node a l r) (node a l r a_ih l_ih r_ih) ⋯) →
                        (t : R β) → motive_1 t
-/
#guard_msgs in
#check @R.rec

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

inductive Fn (α : Type) where
  | mk (f : Bool → α)

inductive Fn.Tot (α : Type) : Fn α → Prop where
  | mk (f : Bool → α) : Fn.Tot α (.mk f)

inductive TFn (α : Type) where
  | mk (x : Fn α) (h : x.Tot)

inductive R where
  | tip
  | mk (x : TFn R)

/--
info: @R.rec : {motive_1 : R → Sort u_1} →
  {motive_2 : TFn R → Sort u_1} →
    {motive_3 : Fn R → Sort u_1} →
      {motive_4 : (a : Fn R) → motive_3 a → Fn.Tot R a → Prop} →
        motive_1 R.tip →
          ((x : TFn R) → motive_2 x → motive_1 (R.mk x)) →
            ((x : Fn R) → (h : Fn.Tot R x) → (x_ih : motive_3 x) → motive_4 x x_ih h → motive_2 (TFn.mk x h)) →
              (mk_2 : (f : Bool → R) → ((a : Bool) → motive_1 (f a)) → motive_3 (Fn.mk f)) →
                (∀ (f : Bool → R) (f_ih : (a : Bool) → motive_1 (f a)), motive_4 (Fn.mk f) (mk_2 f fun a => f_ih a) ⋯) →
                  (t : R) → motive_1 t
-/
#guard_msgs in
#check @R.rec

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

inductive R where
  | tip
  | mk (y : SWFTree R)

/--
info: @R.rec : {motive_1 : R → Sort u_1} →
  {motive_2 : SWFTree R → Sort u_1} →
    {motive_3 : Tree R → Sort u_1} →
      {motive_4 : (a : Tree R) → motive_3 a → Tree.WF R a → Prop} →
        motive_1 R.tip →
          ((y : SWFTree R) → motive_2 y → motive_1 (R.mk y)) →
            ((x : Tree R) → (h : Tree.WF R x) → (x_ih : motive_3 x) → motive_4 x x_ih h → motive_2 { x := x, h := h }) →
              (empty : motive_3 Tree.empty) →
                (node : (a : R) → (l r : Tree R) → motive_1 a → motive_3 l → motive_3 r → motive_3 (Tree.node a l r)) →
                  motive_4 Tree.empty empty ⋯ →
                    (∀ (a : R) (l r : Tree R) (hl : Tree.WF R l) (hr : Tree.WF R r) (a_ih : motive_1 a)
                        (l_ih : motive_3 l) (r_ih : motive_3 r),
                        motive_4 l l_ih hl →
                          motive_4 r r_ih hr → motive_4 (Tree.node a l r) (node a l r a_ih l_ih r_ih) ⋯) →
                      (t : R) → motive_1 t
-/
#guard_msgs in
#check @R.rec

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

inductive R where
  | tip
  | mk (y : { t : Tree R // t.WF })

/--
info: @R.rec : {motive_1 : R → Sort u_1} →
  {motive_2 : { t // Tree.WF R t } → Sort u_1} →
    {motive_3 : Tree R → Sort u_1} →
      {motive_4 : (a : Tree R) → motive_3 a → Tree.WF R a → Prop} →
        motive_1 R.tip →
          ((y : { t // Tree.WF R t }) → motive_2 y → motive_1 (R.mk y)) →
            ((val : Tree R) →
                (property : Tree.WF R val) →
                  (val_ih : motive_3 val) → motive_4 val val_ih property → motive_2 ⟨val, property⟩) →
              (empty : motive_3 Tree.empty) →
                (node : (a : R) → (l r : Tree R) → motive_1 a → motive_3 l → motive_3 r → motive_3 (Tree.node a l r)) →
                  motive_4 Tree.empty empty ⋯ →
                    (∀ (a : R) (l r : Tree R) (hl : Tree.WF R l) (hr : Tree.WF R r) (a_ih : motive_1 a)
                        (l_ih : motive_3 l) (r_ih : motive_3 r),
                        motive_4 l l_ih hl →
                          motive_4 r r_ih hr → motive_4 (Tree.node a l r) (node a l r a_ih l_ih r_ih) ⋯) →
                      (t : R) → motive_1 t
-/
#guard_msgs in
#check @R.rec

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

inductive R where
  | tip
  | mk (x : WFTree R) (l : List R)

/--
info: @R.rec : {motive_1 : R → Sort u_1} →
  {motive_2 : WFTree R → Sort u_1} →
    {motive_3 : Tree R → Sort u_1} →
      {motive_4 : (a : Tree R) → motive_3 a → Tree.WF R a → Prop} →
        {motive_5 : List R → Sort u_1} →
          motive_1 R.tip →
            ((x : WFTree R) → (l : List R) → motive_2 x → motive_5 l → motive_1 (R.mk x l)) →
              ((x : Tree R) → (h : Tree.WF R x) → (x_ih : motive_3 x) → motive_4 x x_ih h → motive_2 (WFTree.mk x h)) →
                (empty : motive_3 Tree.empty) →
                  (node :
                      (a : R) → (l r : Tree R) → motive_1 a → motive_3 l → motive_3 r → motive_3 (Tree.node a l r)) →
                    motive_4 Tree.empty empty ⋯ →
                      (∀ (a : R) (l r : Tree R) (hl : Tree.WF R l) (hr : Tree.WF R r) (a_ih : motive_1 a)
                          (l_ih : motive_3 l) (r_ih : motive_3 r),
                          motive_4 l l_ih hl →
                            motive_4 r r_ih hr → motive_4 (Tree.node a l r) (node a l r a_ih l_ih r_ih) ⋯) →
                        motive_5 [] →
                          ((head : R) → (tail : List R) → motive_1 head → motive_5 tail → motive_5 (head :: tail)) →
                            (t : R) → motive_1 t
-/
#guard_msgs in
#check @R.rec

end Mixed

/-! ## A container inside the family's parameter

`WFTree (Option R)`: `Option` sits between the copy's parameter and the writer,
so it is copied too and gets a motive of its own.
-/

namespace InParam

inductive R where
  | tip
  | mk (x : WFTree (Option R))

/--
info: @R.rec : {motive_1 : R → Sort u_1} →
  {motive_2 : WFTree (Option R) → Sort u_1} →
    {motive_3 : Tree (Option R) → Sort u_1} →
      {motive_4 : Option R → Sort u_1} →
        {motive_5 : (a : Tree (Option R)) → motive_3 a → Tree.WF (Option R) a → Prop} →
          motive_1 R.tip →
            ((x : WFTree (Option R)) → motive_2 x → motive_1 (R.mk x)) →
              ((x : Tree (Option R)) →
                  (h : Tree.WF (Option R) x) → (x_ih : motive_3 x) → motive_5 x x_ih h → motive_2 (WFTree.mk x h)) →
                (empty : motive_3 Tree.empty) →
                  (node :
                      (a : Option R) →
                        (l r : Tree (Option R)) → motive_4 a → motive_3 l → motive_3 r → motive_3 (Tree.node a l r)) →
                    motive_4 none →
                      ((val : R) → motive_1 val → motive_4 (some val)) →
                        motive_5 Tree.empty empty ⋯ →
                          (∀ (a : Option R) (l r : Tree (Option R)) (hl : Tree.WF (Option R) l)
                              (hr : Tree.WF (Option R) r) (a_ih : motive_4 a) (l_ih : motive_3 l) (r_ih : motive_3 r),
                              motive_5 l l_ih hl →
                                motive_5 r r_ih hr → motive_5 (Tree.node a l r) (node a l r a_ih l_ih r_ih) ⋯) →
                            (t : R) → motive_1 t
-/
#guard_msgs in
#check @R.rec

end InParam

/-! ## Two writers over one family, and one nested at the other

`Ra` denests the family at itself; `Rb` denests it again at `Ra × Rb`, where
`Ra` is already a type this library built.  The copies must not collide, and
`Ra` -- which `Rb` does not recurse into -- must not acquire a motive.
-/

namespace Twin

inductive Ra where
  | tip
  | mk (x : WFTree Ra)

inductive Rb where
  | tip
  | mk (x : WFTree (Ra × Rb))

/--
info: @Rb.rec : {motive_1 : Rb → Sort u_1} →
  {motive_2 : WFTree (Ra × Rb) → Sort u_1} →
    {motive_3 : Tree (Ra × Rb) → Sort u_1} →
      {motive_4 : Ra × Rb → Sort u_1} →
        {motive_5 : (a : Tree (Ra × Rb)) → motive_3 a → Tree.WF (Ra × Rb) a → Prop} →
          motive_1 Rb.tip →
            ((x : WFTree (Ra × Rb)) → motive_2 x → motive_1 (Rb.mk x)) →
              ((x : Tree (Ra × Rb)) →
                  (h : Tree.WF (Ra × Rb) x) → (x_ih : motive_3 x) → motive_5 x x_ih h → motive_2 (WFTree.mk x h)) →
                (empty : motive_3 Tree.empty) →
                  (node :
                      (a : Ra × Rb) →
                        (l r : Tree (Ra × Rb)) → motive_4 a → motive_3 l → motive_3 r → motive_3 (Tree.node a l r)) →
                    ((fst : Ra) → (snd : Rb) → motive_1 snd → motive_4 (fst, snd)) →
                      motive_5 Tree.empty empty ⋯ →
                        (∀ (a : Ra × Rb) (l r : Tree (Ra × Rb)) (hl : Tree.WF (Ra × Rb) l) (hr : Tree.WF (Ra × Rb) r)
                            (a_ih : motive_4 a) (l_ih : motive_3 l) (r_ih : motive_3 r),
                            motive_5 l l_ih hl →
                              motive_5 r r_ih hr → motive_5 (Tree.node a l r) (node a l r a_ih l_ih r_ih) ⋯) →
                          (t : Rb) → motive_1 t
-/
#guard_msgs in
#check @Rb.rec

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

inductive Chain (α : Type) where
  | nil
  | cons (a : α) (t : Chain α)

inductive Chain.Pair (α : Type) : Chain α → Prop where
  | nil : Chain.Pair α .nil
  | cons (a : α) (t u : Chain α) (h : Chain.Pair α t) : Chain.Pair α (.cons a t)

inductive PChain (α : Type) where
  | mk (c : Chain α) (h : c.Pair)

-- nothing is held back any more, so the trace has nothing to say
#guard_msgs in
set_option trace.Mumi.indind true in
inductive R where
  | tip
  | mk (x : PChain R)

-- the minor for `cons` binds `u` and stops there: there is no `u_ih`
/--
info: @R.rec : {motive_1 : R → Sort u_1} →
  {motive_2 : PChain R → Sort u_1} →
    {motive_3 : Chain R → Sort u_1} →
      {motive_4 : (a : Chain R) → motive_3 a → Chain.Pair R a → Prop} →
        motive_1 R.tip →
          ((x : PChain R) → motive_2 x → motive_1 (R.mk x)) →
            ((c : Chain R) →
                (h : Chain.Pair R c) → (c_ih : motive_3 c) → motive_4 c c_ih h → motive_2 (PChain.mk c h)) →
              (nil : motive_3 Chain.nil) →
                (cons : (a : R) → (t : Chain R) → motive_1 a → motive_3 t → motive_3 (Chain.cons a t)) →
                  motive_4 Chain.nil nil ⋯ →
                    (∀ (a : R) (t u : Chain R) (h : Chain.Pair R t) (a_ih : motive_1 a) (t_ih : motive_3 t),
                        motive_4 t t_ih h → motive_4 (Chain.cons a t) (cons a t a_ih t_ih) ⋯) →
                      (t : R) → motive_1 t
-/
#guard_msgs in
#check @R.rec

/-! The constructor is the writer's own, and so is what it takes. -/

/-- info: R.mk : PChain R → R -/
#guard_msgs in
#check @R.mk

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

inductive A (α : Type) where
  | mk (a : α)
  | nil

inductive A.P (α : Type) : A α → Prop where
  | mk (a : α) : A.P α (.mk a)

inductive A.Q (α : Type) : (x : A α) → A.P α x → Prop where
  | mk (a : α) : A.Q α (.mk a) (.mk a)

inductive QA (α : Type) where
  | mk (x : A α) (h : x.P) (q : A.Q α x h)

inductive R where
  | mk (x : QA R)

/-! Both propositions get a motive, and both are stated over the originals: the
copies denesting made of `A`, `A.P` and `A.Q` are gone by the time the recursor
is named. -/

/--
info: @R.rec : {motive_1 : R → Sort u_1} →
  {motive_2 : QA R → Sort u_1} →
    {motive_3 : A R → Sort u_1} →
      {motive_4 : (a : A R) → motive_3 a → A.P R a → Prop} →
        {motive_5 : (x : A R) → (a : A.P R x) → motive_3 x → A.Q R x a → Prop} →
          ((x : QA R) → motive_2 x → motive_1 (R.mk x)) →
            ((x : A R) →
                (h : A.P R x) →
                  (q : A.Q R x h) →
                    (x_ih : motive_3 x) → motive_4 x x_ih h → motive_5 x h x_ih q → motive_2 (QA.mk x h q)) →
              (mk_2 : (a : R) → motive_1 a → motive_3 (A.mk a)) →
                motive_3 A.nil →
                  (∀ (a : R) (a_ih : motive_1 a), motive_4 (A.mk a) (mk_2 a a_ih) ⋯) →
                    (∀ (a : R) (a_ih : motive_1 a), motive_5 (A.mk a) ⋯ (mk_2 a a_ih) ⋯) → (t : R) → motive_1 t
-/
#guard_msgs in
#check @R.rec

/-! And the `Prop`-typed index says nothing, `Prop` being proof-irrelevant. -/

example (x : A R) (h h' : A.P R x) : A.Q R x h = A.Q R x h' := rfl

end PropIdx

/-! ## Not rescued: a `Prop` member with no constructors

Lean infers an inductive's parameters from its constructors, and
`Box.Never` has none, so its index counts as a parameter and Lean's own
nesting check rejects the block before any of this gets a look in.

Denesting turns a nesting parameter that mentions a field of the constructor
into an extra index of the copy, which is what the next two sections rest on.
The field's own type may mention the block -- the copy is then indexed by a
member, and the induction-inductive route erases it with the rest.  What it may
not do is mention the block through something that is *not* a member: here
`b : Box R` is the field, and `Box R` has no erased counterpart to index the copy
by, so that route stops one step further along than the plain denesting does.
-/

namespace Empty

inductive Box (α : Type) where
  | mk (a : α)
  | nil

inductive Box.Never (α : Type) : Box α → Prop

inductive NBox (α : Type) where
  | mk (b : Box α) (h : b.Never)

/--
error: (kernel) invalid nested inductive datatype 'MumiTests.Shapes.Empty.Box.Never', nested inductive datatypes parameters cannot contain local variables.
---
trace: [Mumi.rescue] the induction-inductive retry, over the originals did not take: The index `b` of `MumiTests.Shapes.Empty.R.nested_Never_3` mentions the block without being a member's type, so it has no counterpart on the erased types:
      Box R
[Mumi.rescue] lowering the denested block did not take: Cannot denest
      Box.Never R b

    Note: `MumiTests.Shapes.Empty.Box.Never` is applied to something depending on `b`, whose own type mentions a member of the block
[Mumi.rescue] the induction-inductive retry did not take: The index `b` of `MumiTests.Shapes.Empty.R.nested_Never_3` mentions the block without being a member's type, so it has no counterpart on the erased types:
      Box R
-/
#guard_msgs(whitespace := lax) in
set_option trace.Mumi.rescue true in
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

inductive R : Nat → Type where
  | tip (n : Nat) : R n
  | mk (n : Nat) (x : WFTree (R n)) : R n

/-- info: R.mk : (n : Nat) → WFTree (R n) → R n -/
#guard_msgs in
#check @R.mk

/--
info: @R.rec : {motive_1 : (a : Nat) → R a → Sort u_1} →
  {motive_2 : (n : Nat) → WFTree (R n) → Sort u_1} →
    {motive_3 : (n : Nat) → Tree (R n) → Sort u_1} →
      {motive_4 : (n : Nat) → (a : Tree (R n)) → motive_3 n a → Tree.WF (R n) a → Prop} →
        ((n : Nat) → motive_1 n (R.tip n)) →
          ((n : Nat) → (x : WFTree (R n)) → motive_2 n x → motive_1 n (R.mk n x)) →
            ((n : Nat) →
                (x : Tree (R n)) →
                  (h : Tree.WF (R n) x) → (x_ih : motive_3 n x) → motive_4 n x x_ih h → motive_2 n (WFTree.mk x h)) →
              (empty : (n : Nat) → motive_3 n Tree.empty) →
                (node :
                    (n : Nat) →
                      (a : R n) →
                        (l r : Tree (R n)) →
                          motive_1 n a → motive_3 n l → motive_3 n r → motive_3 n (Tree.node a l r)) →
                  (∀ (n : Nat), motive_4 n Tree.empty (empty n) ⋯) →
                    (∀ (n : Nat) (a : R n) (l r : Tree (R n)) (hl : Tree.WF (R n) l) (hr : Tree.WF (R n) r)
                        (a_ih : motive_1 n a) (l_ih : motive_3 n l) (r_ih : motive_3 n r),
                        motive_4 n l l_ih hl →
                          motive_4 n r r_ih hr → motive_4 n (Tree.node a l r) (node n a l r a_ih l_ih r_ih) ⋯) →
                      {a : Nat} → (t : R a) → motive_1 a t
-/
#guard_msgs in
#check @R.rec

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

inductive H where
  | tip : H
  | mk : (n : Nat) → Cx H n → H

/-! Nothing here is pretty-printed back into shape: the constructor really does
take a `Cx H n`. -/

/-- info: H.mk : (n : Nat) → Cx H n → H -/
#guard_msgs in
set_option mumi.pp.nested false in
#check @H.mk

/--
info: @H.rec : {motive_1 : H → Sort u_1} →
  {motive_2 : (n : Nat) → Cx H n → Sort u_1} →
    motive_1 H.tip →
      ((n : Nat) → (a : Cx H n) → motive_2 n a → motive_1 (H.mk n a)) →
        ((n : Nat) → (a : H) → motive_1 a → motive_2 n (Cx.mk a)) → ((n : Nat) → motive_2 n Cx.z) → (t : H) → motive_1 t
-/
#guard_msgs in
set_option mumi.pp.nested false in
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
