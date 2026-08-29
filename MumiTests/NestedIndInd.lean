/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import Mumi

/-!
# Nested inductives whose denesting is induction-inductive

`MumiTests.Nested` covers the nested inductives whose denesting is merely
heterogeneous.  These are the ones whose denesting is *induction-inductive*: a
copy's arity mentions another copy, so `Mumi.Denest` refuses them and
`Mumi.IndInd` takes them instead.
-/

/-! ## A well-formed binary search tree of itself

The motivating case.  `WFTree α` is a tree paired with a proof, and the proof
predicate is indexed by the tree, so specialising all four types at `RecWFTree`
gives a block in which `Tree.WF`'s copy is indexed by `Tree`'s copy.
-/

inductive Tree (α : Type u) where
  | empty
  | node (key : Nat) (value : α) (l r : Tree α)

inductive Tree.WFWith (α : Type u) : Tree α → List Nat → Prop where
  | empty : Tree.WFWith α .empty []
  | node {llist rlist} (key : Nat) (value : α) (l r : Tree α)
      (hl : Tree.WFWith α l llist) (hr : Tree.WFWith α r rlist)
      (hl' : ∀ a ∈ llist, a < key) (hr' : ∀ a ∈ rlist, key < a) :
      Tree.WFWith α (.node key value l r) (llist ++ key :: rlist)

inductive Tree.WF (α : Type u) : Tree α → Prop where
  | intro (l : List Nat) (t : Tree α) (h : Tree.WFWith α t l) : Tree.WF α t

inductive WFTree (α : Type u) : Type u where
  | mk (x : Tree α) (h : x.WF)

inductive RecWFTree where
  | mk (x : WFTree RecWFTree)

/-- info: RecWFTree : Type -/
#guard_msgs in
#check @RecWFTree

-- the constructor has the type it was declared with; the copy is in the
-- kernel-facing one, under a name nobody has to reach for
/-- info: RecWFTree.mk : WFTree RecWFTree → RecWFTree -/
#guard_msgs in
#check @RecWFTree.mk

/-- info: RecWFTree._nested_mk : RecWFTree.nested_WFTree_1 → RecWFTree -/
#guard_msgs in
#check @RecWFTree._nested_mk

/-- info: RecWFTree.nested_WFTree_1.ofOrig : WFTree RecWFTree → RecWFTree.nested_WFTree_1 -/
#guard_msgs in
#check @RecWFTree.nested_WFTree_1.ofOrig

/--
info: @RecWFTree.nested_WF_3.ofOrig : ∀ {a : Tree RecWFTree},
  Tree.WF RecWFTree a → RecWFTree.nested_WF_3 (RecWFTree.nested_Tree_2.ofOrig a)
-/
#guard_msgs in
#check @RecWFTree.nested_WF_3.ofOrig

/-- info: RecWFTree.nested_WFTree_1 : Type -/
#guard_msgs in
#check @RecWFTree.nested_WFTree_1

/--
info: RecWFTree.nested_WFTree_1.mk : (x : RecWFTree.nested_Tree_2) → RecWFTree.nested_WF_3 x → RecWFTree.nested_WFTree_1
-/
#guard_msgs in
#check @RecWFTree.nested_WFTree_1.mk

/-- info: RecWFTree.nested_Tree_2 : Type -/
#guard_msgs in
#check @RecWFTree.nested_Tree_2

/--
info: RecWFTree.nested_Tree_2.node : Nat →
  RecWFTree → RecWFTree.nested_Tree_2 → RecWFTree.nested_Tree_2 → RecWFTree.nested_Tree_2
-/
#guard_msgs in
#check @RecWFTree.nested_Tree_2.node

-- the copy of an arity that mentions another copy: this is the whole point
/-- info: RecWFTree.nested_WF_3 : RecWFTree.nested_Tree_2 → Prop -/
#guard_msgs in
#check @RecWFTree.nested_WF_3

/--
info: RecWFTree.nested_WFWith_4 : RecWFTree.nested_Tree_2 → List Nat → Prop
-/
#guard_msgs in
#check @RecWFTree.nested_WFWith_4

-- a copied constructor in an *index*, which a head-only rewrite cannot reach
/--
info: RecWFTree.nested_WFWith_4.empty : RecWFTree.nested_WFWith_4 RecWFTree.nested_Tree_2.empty []
-/
#guard_msgs in
#check @RecWFTree.nested_WFWith_4.empty

/--
info: @RecWFTree.nested_WFWith_4.node : ∀ {llist rlist : List Nat} (key : Nat) (value : RecWFTree)
  (l r : RecWFTree.nested_Tree_2),
  RecWFTree.nested_WFWith_4 l llist →
    RecWFTree.nested_WFWith_4 r rlist →
      (∀ (a : Nat), a ∈ llist → a < key) →
        (∀ (a : Nat), a ∈ rlist → key < a) →
          RecWFTree.nested_WFWith_4 (RecWFTree.nested_Tree_2.node key value l r) (llist ++ key :: rlist)
-/
#guard_msgs in
#check @RecWFTree.nested_WFWith_4.node

-- one motive per data member, and the erased proof back in its minor.  Nothing
-- in it is a copy: the motives are over the types the block was written with,
-- and so are the constructors the minors conclude at
/--
info: @RecWFTree.rec : {C_RecWFTree : RecWFTree → Sort u_1} →
  {C_WFTree : WFTree RecWFTree → Sort u_1} →
    {C_Tree : Tree RecWFTree → Sort u_1} →
      ((x : WFTree RecWFTree) → C_WFTree x → C_RecWFTree (RecWFTree.mk x)) →
        ((x : Tree RecWFTree) → (h : Tree.WF RecWFTree x) → C_Tree x → C_WFTree (WFTree.mk x h)) →
          C_Tree Tree.empty →
            ((key : Nat) →
                (value : RecWFTree) →
                  (l r : Tree RecWFTree) → C_RecWFTree value → C_Tree l → C_Tree r → C_Tree (Tree.node key value l r)) →
              (t : RecWFTree) → C_RecWFTree t
-/
#guard_msgs in
#check @RecWFTree.rec

-- the kernel-facing one is still there, over the copies, under a hidden name
/--
info: @RecWFTree._nested_rec : {C_RecWFTree : RecWFTree → Sort u_1} →
  {C_nested_WFTree_1 : RecWFTree.nested_WFTree_1 → Sort u_1} →
    {C_nested_Tree_2 : RecWFTree.nested_Tree_2 → Sort u_1} →
      ((x : RecWFTree.nested_WFTree_1) → C_nested_WFTree_1 x → C_RecWFTree (RecWFTree._nested_mk x)) →
        ((x : RecWFTree.nested_Tree_2) →
            (h : RecWFTree.nested_WF_3 x) → C_nested_Tree_2 x → C_nested_WFTree_1 (RecWFTree.nested_WFTree_1.mk x h)) →
          C_nested_Tree_2 RecWFTree.nested_Tree_2.empty →
            ((key : Nat) →
                (value : RecWFTree) →
                  (l r : RecWFTree.nested_Tree_2) →
                    C_RecWFTree value →
                      C_nested_Tree_2 l →
                        C_nested_Tree_2 r → C_nested_Tree_2 (RecWFTree.nested_Tree_2.node key value l r)) →
              (t : RecWFTree) → C_RecWFTree t
-/
#guard_msgs in
#check @RecWFTree._nested_rec

-- the way back, which is what lets the recursor be stated over the originals
/-- info: RecWFTree.nested_WFTree_1.toOrig : RecWFTree.nested_WFTree_1 → WFTree RecWFTree -/
#guard_msgs in
#check @RecWFTree.nested_WFTree_1.toOrig

/--
info: @RecWFTree.nested_WF_3.toOrig : ∀ {a : RecWFTree.nested_Tree_2}, RecWFTree.nested_WF_3 a → Tree.WF RecWFTree a.toOrig
-/
#guard_msgs in
#check @RecWFTree.nested_WF_3.toOrig

namespace RecWFTree

theorem emptyWF : Tree.WF RecWFTree .empty := .intro [] _ .empty

def leaf (v : RecWFTree) : Tree RecWFTree := .node 0 v .empty .empty

theorem leafWF (v : RecWFTree) : (leaf v).WF :=
  .intro _ _ (.node 0 v .empty .empty .empty .empty (by simp) (by simp))

def bottom : RecWFTree := .mk (.mk .empty emptyWF)

def wrap (v : RecWFTree) : RecWFTree := .mk (.mk (leaf v) (leafWF v))

/-- How many `RecWFTree`s are nested inside. -/
def depth (t : RecWFTree) : Nat :=
  RecWFTree.rec (C_RecWFTree := fun _ => Nat) (C_WFTree := fun _ => Nat)
    (C_Tree := fun _ => Nat)
    (fun _ ih => ih + 1) (fun _ _ ih => ih) 0 (fun _ _ _ _ ihv ihl ihr => ihv + ihl + ihr) t

-- iota holds definitionally, all the way through the copies
example : depth bottom = 1 := rfl
example : depth (wrap bottom) = 2 := rfl
example : depth (wrap (wrap bottom)) = 3 := rfl

/-- info: 3 -/
#guard_msgs in
#eval depth (wrap (wrap bottom))

/-- info: 'RecWFTree' does not depend on any axioms -/
#guard_msgs in
#print axioms RecWFTree

/-- info: 'RecWFTree.depth' does not depend on any axioms -/
#guard_msgs in
#print axioms depth

/-- The erased predicate can still be destructed. -/
example (t : nested_Tree_2) (h : nested_WF_3 t) : True := by
  cases h with
  | intro l t hw => trivial

end RecWFTree

/-! ## Parameters, carried into every copy -/

inductive Bag (α : Type) where
  | mk : List α → Bag α

inductive BagOk (α : Type) : Bag α → Prop where
  | mk : (l : List α) → BagOk α (.mk l)

inductive OkBag (α : Type) where
  | mk (b : Bag α) (h : BagOk α b)

inductive Rec2 (β : Type) where
  | leaf (b : β)
  | mk (x : OkBag (Rec2 β))

/-- info: Rec2 : Type → Type -/
#guard_msgs in
#check @Rec2

/-- info: @Rec2.mk : {β : Type} → OkBag (Rec2 β) → Rec2 β -/
#guard_msgs in
#check @Rec2.mk

/-- info: Rec2.nested_BagOk_4 : (β : Type) → Rec2.nested_Bag_2 β → Prop -/
#guard_msgs in
#check @Rec2.nested_BagOk_4

-- the `List` inside `Bag` is a copy in its own right, and recurses two ways
/--
info: @Rec2.nested_List_3.cons : {β : Type} → Rec2 β → Rec2.nested_List_3 β → Rec2.nested_List_3 β
-/
#guard_msgs in
#check @Rec2.nested_List_3.cons

-- and the recursor is over `OkBag`, `Bag` and `List`, the parameter carried through
/--
info: @Rec2.rec : {β : Type} →
  {C_Rec2 : Rec2 β → Sort u_1} →
    {C_OkBag : OkBag (Rec2 β) → Sort u_1} →
      {C_Bag : Bag (Rec2 β) → Sort u_1} →
        {C_List : List (Rec2 β) → Sort u_1} →
          ((b : β) → C_Rec2 (Rec2.leaf b)) →
            ((x : OkBag (Rec2 β)) → C_OkBag x → C_Rec2 (Rec2.mk x)) →
              ((b : Bag (Rec2 β)) → (h : BagOk (Rec2 β) b) → C_Bag b → C_OkBag (OkBag.mk b h)) →
                ((a : List (Rec2 β)) → C_List a → C_Bag (Bag.mk a)) →
                  C_List [] →
                    ((head : Rec2 β) → (tail : List (Rec2 β)) → C_Rec2 head → C_List tail → C_List (head :: tail)) →
                      (t : Rec2 β) → C_Rec2 t
-/
#guard_msgs in
#check @Rec2.rec

/-! ## Indices, on both the data copy and the proof copy -/

inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons : α → {n : Nat} → Vec α n → Vec α (n + 1)

inductive VecOk (α : Type) : {n : Nat} → Vec α n → Prop where
  | nil : VecOk α .nil
  | cons (a : α) {n} (v : Vec α n) : VecOk α v → VecOk α (.cons a v)

inductive OkVec (α : Type) where
  | mk {n : Nat} (v : Vec α n) (h : VecOk α v)

inductive Rec3 where
  | mk (x : OkVec Rec3)

/-- info: Rec3.mk : OkVec Rec3 → Rec3 -/
#guard_msgs in
#check @Rec3.mk

/-- info: Rec3.nested_Vec_2 : Nat → Type -/
#guard_msgs in
#check @Rec3.nested_Vec_2

/-- info: @Rec3.nested_VecOk_3 : {n : Nat} → Rec3.nested_Vec_2 n → Prop -/
#guard_msgs in
#check @Rec3.nested_VecOk_3

-- the index survives the trip out: the motive for the copy of `Vec` is a motive
-- for `Vec`, at the index the copy was carrying
/--
info: @Rec3.rec : {C_Rec3 : Rec3 → Sort u_1} →
  {C_OkVec : OkVec Rec3 → Sort u_1} →
    {C_Vec : (a : Nat) → Vec Rec3 a → Sort u_1} →
      ((x : OkVec Rec3) → C_OkVec x → C_Rec3 (Rec3.mk x)) →
        ({n : Nat} → (v : Vec Rec3 n) → (h : VecOk Rec3 v) → C_Vec n v → C_OkVec (OkVec.mk v h)) →
          C_Vec 0 Vec.nil →
            ((a : Rec3) → {n : Nat} → (a_1 : Vec Rec3 n) → C_Rec3 a → C_Vec n a_1 → C_Vec (n + 1) (Vec.cons a a_1)) →
              (t : Rec3) → C_Rec3 t
-/
#guard_msgs in
#check @Rec3.rec

namespace Rec3

def bottom : Rec3 := .mk (.mk .nil .nil)

def wrap (v : Rec3) : Rec3 := .mk (.mk (.cons v .nil) (.cons v .nil .nil))

/-- How many `Rec3`s are nested inside. -/
def depth (t : Rec3) : Nat :=
  Rec3.rec (C_Rec3 := fun _ => Nat) (C_OkVec := fun _ => Nat) (C_Vec := fun _ _ => Nat)
    (fun _ ih => ih + 1) (fun _ _ ih => ih) 0 (fun _ {_} _ iha ihv => iha + ihv) t

-- iota holds through the indexed copy too
example : depth bottom = 1 := rfl
example : depth (wrap (wrap bottom)) = 3 := rfl

/-- info: 3 -/
#guard_msgs in
#eval depth (wrap (wrap bottom))

/-- info: 'Rec3.depth' does not depend on any axioms -/
#guard_msgs in
#print axioms depth

end Rec3

/-! ## What is not rescued

A nesting whose parameters mention a field of the constructor it appears in.
`Mumi.Denest` turns those locals into extra indices of the copy; here the copy
is a member of an induction-inductive block, and that is not done.  The
declaration keeps Lean's own error, exactly as if the library were not imported.
-/

inductive Fam (α : Type) : Nat → Type where
  | mk : α → Fam α n

inductive FamOk (α : Type) : {n : Nat} → Fam α n → Prop where
  | mk {n : Nat} (a : α) : FamOk α (.mk (n := n) a)

inductive OkFam (α : Type) (n : Nat) where
  | mk (v : Fam α n) (h : FamOk α v)

/--
error: (kernel) invalid nested inductive datatype 'OkFam', nested inductive datatypes parameters
cannot contain local variables.
-/
#guard_msgs in
inductive BadLocals where
  | mk (n : Nat) (x : OkFam BadLocals n)

/-! ## The off switch -/

/-- error: (kernel) unknown constant 'Off2' -/
#guard_msgs in
set_option mumi.enabled false in
inductive Off2 where
  | mk (x : WFTree Off2)
