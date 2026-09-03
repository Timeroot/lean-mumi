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

-- one motive per member of the denested block, `Prop` members included, and one
-- minor per constructor.  Nothing in it is a copy: the motives are over the
-- types the block was written with, and so are the constructors the minors
-- conclude at.  A `Prop` motive takes the value the recursion produced at the
-- data member it is indexed by, which is what lets a recursion rebuild the tree
-- and carry its well-formedness along with it
/--
info: @RecWFTree.rec : {motive_1 : RecWFTree → Sort u_1} →
  {motive_2 : WFTree RecWFTree → Sort u_1} →
    {motive_3 : Tree RecWFTree → Sort u_1} →
      {motive_4 : (a : Tree RecWFTree) → motive_3 a → Tree.WF RecWFTree a → Prop} →
        {motive_5 : (a : Tree RecWFTree) → (a_1 : List Nat) → motive_3 a → Tree.WFWith RecWFTree a a_1 → Prop} →
          ((x : WFTree RecWFTree) → motive_2 x → motive_1 (RecWFTree.mk x)) →
            ((x : Tree RecWFTree) →
                (h : Tree.WF RecWFTree x) → (x_ih : motive_3 x) → motive_4 x x_ih h → motive_2 (WFTree.mk x h)) →
              (empty : motive_3 Tree.empty) →
                (node :
                    (key : Nat) →
                      (value : RecWFTree) →
                        (l r : Tree RecWFTree) →
                          motive_1 value → motive_3 l → motive_3 r → motive_3 (Tree.node key value l r)) →
                  (∀ (l : List Nat) (t : Tree RecWFTree) (h : Tree.WFWith RecWFTree t l) (t_ih : motive_3 t),
                      motive_5 t l t_ih h → motive_4 t t_ih ⋯) →
                    motive_5 Tree.empty [] empty ⋯ →
                      (∀ {llist rlist : List Nat} (key : Nat) (value : RecWFTree) (l r : Tree RecWFTree)
                          (hl : Tree.WFWith RecWFTree l llist) (hr : Tree.WFWith RecWFTree r rlist)
                          (hl' : ∀ (a : Nat), a ∈ llist → a < key) (hr' : ∀ (a : Nat), a ∈ rlist → key < a)
                          (value_ih : motive_1 value) (l_ih : motive_3 l) (r_ih : motive_3 r),
                          motive_5 l llist l_ih hl →
                            motive_5 r rlist r_ih hr →
                              motive_5 (Tree.node key value l r) (llist ++ key :: rlist)
                                (node key value l r value_ih l_ih r_ih) ⋯) →
                        (t : RecWFTree) → motive_1 t
-/
#guard_msgs in
#check @RecWFTree.rec

-- the kernel-facing one is still there, over the copies, under a hidden name
/--
info: @RecWFTree._nested_rec : {motive_1 : RecWFTree → Sort u_1} →
  {motive_2 : RecWFTree.nested_WFTree_1 → Sort u_1} →
    {motive_3 : RecWFTree.nested_Tree_2 → Sort u_1} →
      ((x : RecWFTree.nested_WFTree_1) → motive_2 x → motive_1 (RecWFTree._nested_mk x)) →
        ((x : RecWFTree.nested_Tree_2) →
            (h : RecWFTree.nested_WF_3 x) → motive_3 x → motive_2 (RecWFTree.nested_WFTree_1.mk x h)) →
          motive_3 RecWFTree.nested_Tree_2.empty →
            ((key : Nat) →
                (value : RecWFTree) →
                  (l r : RecWFTree.nested_Tree_2) →
                    motive_1 value → motive_3 l → motive_3 r → motive_3 (RecWFTree.nested_Tree_2.node key value l r)) →
              (t : RecWFTree) → motive_1 t
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
  RecWFTree.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat)
    (motive_3 := fun _ => Nat) (motive_4 := fun _ _ _ => True)
    (motive_5 := fun _ _ _ _ => True)
    (fun _ ih => ih + 1) (fun _ _ ih _ => ih) 0
    (fun _ _ _ _ ihv ihl ihr => ihv + ihl + ihr)
    (fun _ _ _ _ _ => trivial) trivial
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial) t

-- iota holds definitionally, all the way through the copies
example : depth bottom = 1 := rfl
example : depth (wrap bottom) = 2 := rfl
example : depth (wrap (wrap bottom)) = 3 := rfl

/--
Rebuilding the tree, which the split recursors cannot do.

The minor for `WFTree.mk` is handed a proof that the *original* tree is
well-formed and has to produce one about the tree the recursion built.  With a
motive only for the data members there is nothing to make that step with, and
the goal is in fact false.  Here `motive_4` and `motive_5` say what the recursion
maintains about the rebuilt tree, and the `Tree.WF` and `Tree.WFWith` minors
maintain it.
-/
def rebuild : RecWFTree → RecWFTree :=
  RecWFTree.rec
    (motive_1 := fun _ => RecWFTree)
    (motive_2 := fun _ => WFTree RecWFTree)
    (motive_3 := fun _ => Tree RecWFTree)
    (motive_4 := fun _ ih _ => Tree.WF RecWFTree ih)
    (motive_5 := fun _ l ih _ => Tree.WFWith RecWFTree ih l)
    (fun _ ih => .mk ih)
    (fun _ _ ih hwf => .mk ih hwf)
    .empty
    (fun key _ _ _ ihv ihl ihr => .node key ihv ihl ihr)
    (fun l _ _ ih hw => .intro l ih hw)
    .empty
    (fun key _ _ _ _ _ hl' hr' ihv ihl ihr hwl hwr => .node key ihv ihl ihr hwl hwr hl' hr')

example : depth (rebuild (wrap (wrap bottom))) = 3 := rfl

/-- info: 'RecWFTree.rebuild' does not depend on any axioms -/
#guard_msgs in
#print axioms rebuild

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

/-! ### The bridge is an isomorphism

Nothing above needs these -- the recursor is stated over the originals, so a
recursion never meets a copy.  They are here because the bridge is what makes
that restatement legitimate, and an equivalence that is only claimed is worth
less than one that is checked.  `nested_WF_3` and `nested_WFWith_4` have no
`.rec` of their own and do not need one: they are inverted through `Tree.WF.rec`
and the round trip. -/

theorem ofOrig_toOrig (a : nested_Tree_2) : nested_Tree_2.ofOrig a.toOrig = a :=
  nested_Tree_2.rec
    (motive_1 := fun _ => True) (motive_2 := fun _ => True)
    (motive_3 := fun a => nested_Tree_2.ofOrig a.toOrig = a)
    (fun _ _ => trivial) (fun _ _ _ => trivial)
    rfl
    (fun k v l r _ ihl ihr => by
      show nested_Tree_2.ofOrig (Tree.node k v l.toOrig r.toOrig) = _
      show nested_Tree_2.node k v (nested_Tree_2.ofOrig l.toOrig) (nested_Tree_2.ofOrig r.toOrig) = _
      rw [ihl, ihr])
    a

theorem nested_WF_3.inversion {a : nested_Tree_2} (h : nested_WF_3 a) :
    ∃ l, Tree.WFWith RecWFTree a.toOrig l := by
  obtain ⟨l, t, hw⟩ := h.toOrig
  exact ⟨l, hw⟩

theorem nested_WF_3.of {a : nested_Tree_2} (l) (hw : Tree.WFWith RecWFTree a.toOrig l) :
    nested_WF_3 a :=
  ofOrig_toOrig a ▸ nested_WF_3.ofOrig (.intro l a.toOrig hw)

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
  {motive_1 : Rec2 β → Sort u_1} →
    {motive_2 : OkBag (Rec2 β) → Sort u_1} →
      {motive_3 : Bag (Rec2 β) → Sort u_1} →
        {motive_4 : List (Rec2 β) → Sort u_1} →
          {motive_5 : (a : Bag (Rec2 β)) → motive_3 a → BagOk (Rec2 β) a → Prop} →
            ((b : β) → motive_1 (Rec2.leaf b)) →
              ((x : OkBag (Rec2 β)) → motive_2 x → motive_1 (Rec2.mk x)) →
                ((b : Bag (Rec2 β)) →
                    (h : BagOk (Rec2 β) b) → (b_ih : motive_3 b) → motive_5 b b_ih h → motive_2 (OkBag.mk b h)) →
                  (mk_2 : (a : List (Rec2 β)) → motive_4 a → motive_3 (Bag.mk a)) →
                    motive_4 [] →
                      ((head : Rec2 β) →
                          (tail : List (Rec2 β)) → motive_1 head → motive_4 tail → motive_4 (head :: tail)) →
                        (∀ (l : List (Rec2 β)) (l_ih : motive_4 l), motive_5 (Bag.mk l) (mk_2 l l_ih) ⋯) →
                          (t : Rec2 β) → motive_1 t
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
info: @Rec3.rec : {motive_1 : Rec3 → Sort u_1} →
  {motive_2 : OkVec Rec3 → Sort u_1} →
    {motive_3 : (a : Nat) → Vec Rec3 a → Sort u_1} →
      {motive_4 : {n : Nat} → (a : Vec Rec3 n) → motive_3 n a → VecOk Rec3 a → Prop} →
        ((x : OkVec Rec3) → motive_2 x → motive_1 (Rec3.mk x)) →
          ({n : Nat} →
              (v : Vec Rec3 n) →
                (h : VecOk Rec3 v) → (v_ih : motive_3 n v) → motive_4 v v_ih h → motive_2 (OkVec.mk v h)) →
            (nil : motive_3 0 Vec.nil) →
              (cons :
                  (a : Rec3) →
                    {n : Nat} → (a_1 : Vec Rec3 n) → motive_1 a → motive_3 n a_1 → motive_3 (n + 1) (Vec.cons a a_1)) →
                motive_4 Vec.nil nil ⋯ →
                  (∀ (a : Rec3) {n : Nat} (v : Vec Rec3 n) (a_1 : VecOk Rec3 v) (a_ih : motive_1 a)
                      (v_ih : motive_3 n v), motive_4 v v_ih a_1 → motive_4 (Vec.cons a v) (cons a v a_ih v_ih) ⋯) →
                    (t : Rec3) → motive_1 t
-/
#guard_msgs in
#check @Rec3.rec

namespace Rec3

def bottom : Rec3 := .mk (.mk .nil .nil)

def wrap (v : Rec3) : Rec3 := .mk (.mk (.cons v .nil) (.cons v .nil .nil))

/-- How many `Rec3`s are nested inside. -/
def depth (t : Rec3) : Nat :=
  Rec3.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat) (motive_3 := fun _ _ => Nat)
    (motive_4 := fun _ _ _ => True)
    (fun _ ih => ih + 1) (fun _ _ ih _ => ih) 0 (fun _ {_} _ iha ihv => iha + ihv)
    trivial (fun _ _ _ _ _ _ _ => trivial) t

-- iota holds through the indexed copy too
example : depth bottom = 1 := rfl
example : depth (wrap (wrap bottom)) = 3 := rfl

/-- info: 3 -/
#guard_msgs in
#eval depth (wrap (wrap bottom))

-- `VecOk`'s copy is indexed, so the recursor over the whole block carries
-- `propext` and everything built from it does too
/-- info: 'Rec3.depth' depends on axioms: [propext] -/
#guard_msgs in
#print axioms depth

end Rec3

/-! ## A nesting that nests again

`Rose` holds a `List (Rose α)`, so specialising `Rose` at the block calls for
specialising `List (Rose _)` too, and each copy mentions the other.  Neither can
be built first; they come back as one group and are compiled together, as one
structural recursion over the outer original's recursor.
-/

inductive Rose (α : Type) : Type where
  | node (a : α) (cs : List (Rose α))

mutual
inductive RT : Type where
  | tip
  | mk (r : Rose RT) (t : RT) (h : RP t) : RT
inductive RP : RT → Prop where
  | tip : RP .tip
end

/-- info: RT.mk : Rose RT → (t : RT) → RP t → RT -/
#guard_msgs in
#check @RT.mk

-- `List` is nowhere in the block and still gets a motive, because `Rose`'s own
-- field is one
/--
info: @RT.rec : {motive_1 : RT → Sort u_1} →
  {motive_2 : (a : RT) → motive_1 a → RP a → Prop} →
    {motive_3 : Rose RT → Sort u_1} →
      {motive_4 : List (Rose RT) → Sort u_1} →
        (tip : motive_1 RT.tip) →
          ((r : Rose RT) →
              (t : RT) → (h : RP t) → motive_3 r → (t_ih : motive_1 t) → motive_2 t t_ih h → motive_1 (RT.mk r t h)) →
            motive_2 RT.tip tip RP.tip →
              ((a : RT) → (cs : List (Rose RT)) → motive_1 a → motive_4 cs → motive_3 (Rose.node a cs)) →
                motive_4 [] →
                  ((head : Rose RT) →
                      (tail : List (Rose RT)) → motive_3 head → motive_4 tail → motive_4 (head :: tail)) →
                    (t : RT) → motive_1 t
-/
#guard_msgs in
#check @RT.rec

-- both directions, for both copies
/-- info: RT.nested_Rose_1.ofOrig : Rose RT → RT.nested_Rose_1 -/
#guard_msgs in
#check @RT.nested_Rose_1.ofOrig

/-- info: RT.nested_List_2.toOrig : RT.nested_List_2 → List (Rose RT) -/
#guard_msgs in
#check @RT.nested_List_2.toOrig

namespace RT

def size (t : RT) : Nat :=
  RT.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ _ => True)
    (motive_3 := fun _ => Nat) (motive_4 := fun _ => Nat)
    1 (fun _ _ _ ihr iht _ => ihr + iht) trivial
    (fun _ _ iha ihcs => iha + ihcs) 0 (fun _ _ ih iht => ih + iht) t

example : size .tip = 1 := rfl

/-- info: 3 -/
#guard_msgs in
#eval size (.mk (.node .tip [.node .tip []]) .tip .tip)

-- neither copy is indexed, so no `propext` is needed to get back out
/-- info: 'RT.size' does not depend on any axioms -/
#guard_msgs in
#print axioms size

end RT

/-! ## A nesting type from a `mutual` family

`Fo` and `Ba` are declared together and mention each other, so a copy of `Fo`
alone would be useless: the whole family is specialised at the block, and the
two copies are compiled as one group the same way.
-/

mutual
inductive Fo (α : Type) : Type where
  | mk (a : α) (b : Ba α)
inductive Ba (α : Type) : Type where
  | nil
  | cons (f : Fo α) (b : Ba α)
end

mutual
inductive MT : Type where
  | tip
  | mk (x : Fo MT) (t : MT) (h : MP t)
inductive MP : MT → Prop where
  | tip : MP .tip
end

/-- info: MT.mk : Fo MT → (t : MT) → MP t → MT -/
#guard_msgs in
#check @MT.mk

/--
info: @MT.rec : {motive_1 : MT → Sort u_1} →
  {motive_2 : (a : MT) → motive_1 a → MP a → Prop} →
    {motive_3 : Fo MT → Sort u_1} →
      {motive_4 : Ba MT → Sort u_1} →
        (tip : motive_1 MT.tip) →
          ((x : Fo MT) →
              (t : MT) → (h : MP t) → motive_3 x → (t_ih : motive_1 t) → motive_2 t t_ih h → motive_1 (MT.mk x t h)) →
            motive_2 MT.tip tip MP.tip →
              ((a : MT) → (b : Ba MT) → motive_1 a → motive_4 b → motive_3 (Fo.mk a b)) →
                motive_4 Ba.nil →
                  ((f : Fo MT) → (b : Ba MT) → motive_3 f → motive_4 b → motive_4 (Ba.cons f b)) → (t : MT) → motive_1 t
-/
#guard_msgs in
#check @MT.rec

/-- info: MT.nested_Ba_2.ofOrig : Ba MT → MT.nested_Ba_2 -/
#guard_msgs in
#check @MT.nested_Ba_2.ofOrig

/-- info: MT.nested_Fo_1.toOrig : MT.nested_Fo_1 → Fo MT -/
#guard_msgs in
#check @MT.nested_Fo_1.toOrig

namespace MT

def size (t : MT) : Nat :=
  MT.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ _ => True)
    (motive_3 := fun _ => Nat) (motive_4 := fun _ => Nat)
    1 (fun _ _ _ ihx iht _ => ihx + iht) trivial
    (fun _ _ iha ihb => iha + ihb) 0 (fun _ _ ihf ihb => ihf + ihb) t

example : size .tip = 1 := rfl

/-- info: 3 -/
#guard_msgs in
#eval size (.mk (.mk .tip (.cons (.mk .tip .nil) .nil)) .tip .tip)

/-- info: 'MT.size' does not depend on any axioms -/
#guard_msgs in
#print axioms size

end MT

/-! ## A nesting whose parameters mention a field of the constructor

`OkFam BadLocals n` sits inside a constructor that takes `n` as a field, so the
copy of `OkFam` cannot be fixed at one parameter: it stands for the whole family
`OkFam BadLocals 0`, `OkFam BadLocals 1`, and so on.  Denesting copies it indexed
by `n`, and hands each of the copy's constructors the `n` it belongs to as a
leading field.

`OkFam` is itself induction-inductive -- `FamOk` is a predicate on `Fam` -- so
all three come across, and the `n` travels with them.  Notice that only the
copies whose parameters actually mention `n` gain the index: `Fam BadLocals` and
`FamOk BadLocals` are copied at their own arity, and it is the *original's* index
that carries the `n` there.
-/

inductive Fam (α : Type) : Nat → Type where
  | mk : α → Fam α n

inductive FamOk (α : Type) : {n : Nat} → Fam α n → Prop where
  | mk {n : Nat} (a : α) : FamOk α (.mk (n := n) a)

inductive OkFam (α : Type) (n : Nat) where
  | mk (v : Fam α n) (h : FamOk α v)

inductive BadLocals where
  | tip
  | mk (n : Nat) (x : OkFam BadLocals n)

/-- info: BadLocals.mk : (n : Nat) → OkFam BadLocals n → BadLocals -/
#guard_msgs in
#check @BadLocals.mk

/--
info: @BadLocals.rec : {motive_1 : BadLocals → Sort u_1} →
  {motive_2 : (n : Nat) → OkFam BadLocals n → Sort u_1} →
    {motive_3 : (n : Nat) → Fam BadLocals n → Sort u_1} →
      {motive_4 : (n : Nat) → (a : Fam BadLocals n) → motive_3 n a → FamOk BadLocals a → Prop} →
        motive_1 BadLocals.tip →
          ((n : Nat) → (x : OkFam BadLocals n) → motive_2 n x → motive_1 (BadLocals.mk n x)) →
            ((n : Nat) →
                (v : Fam BadLocals n) →
                  (h : FamOk BadLocals v) → (v_ih : motive_3 n v) → motive_4 n v v_ih h → motive_2 n (OkFam.mk v h)) →
              (mk_2 : (n : Nat) → (a : BadLocals) → motive_1 a → motive_3 n (Fam.mk a)) →
                (∀ (n : Nat) (a : BadLocals) (a_ih : motive_1 a), motive_4 n (Fam.mk a) (mk_2 n a a_ih) ⋯) →
                  (t : BadLocals) → motive_1 t
-/
#guard_msgs in
#check @BadLocals.rec

/--
info: @BadLocals.nested_OkFam_1.ofOrig : {n : Nat} → OkFam BadLocals n → BadLocals.nested_OkFam_1 n
-/
#guard_msgs in
#check @BadLocals.nested_OkFam_1.ofOrig

/-- info: @BadLocals.nested_Fam_2.toOrig : {n : Nat} → BadLocals.nested_Fam_2 n → Fam BadLocals n -/
#guard_msgs in
#check @BadLocals.nested_Fam_2.toOrig

namespace BadLocals

def size (t : BadLocals) : Nat :=
  BadLocals.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    (motive_3 := fun _ _ => Nat) (motive_4 := fun _ _ _ _ => True)
    1 (fun _ _ ih => 1 + ih)
    (fun _ _ _ ihv _ => ihv)
    (fun _ _ ih => ih)
    (fun _ _ _ => trivial)
    t

example : size .tip = 1 := rfl

/-- info: 2 -/
#guard_msgs in
#eval size (.mk 7 (.mk (.mk BadLocals.tip) (.mk BadLocals.tip)))

/-- info: 'BadLocals.size' does not depend on any axioms -/
#guard_msgs in
#print axioms size

end BadLocals

/-! ### And the same nesting inside an induction-inductive block

`BadLocals` is a standalone `inductive`, and the extra index is something the
denesting arranges before the block is read.  A block that erases sees the copy
as one of its own members, so the index has to survive that too: `LocalsII.Ok`
is stated over `OkFam LocalsII n`, the copy of `OkFam` is indexed by `n` like
any other, and the erasure carries the `n` through the pre-world without ever
seeing that it began as a field.
-/

mutual
inductive LocalsII : Type where
  | tip
  | mk : (n : Nat) → (x : OkFam LocalsII n) → LocalsII.Ok n x → LocalsII
inductive LocalsII.Ok : (n : Nat) → OkFam LocalsII n → Prop where
  | mk : (n : Nat) → (x : OkFam LocalsII n) → LocalsII.Ok n x
end

/--
info: @LocalsII.rec : {motive_1 : LocalsII → Sort u_1} →
  {motive_2 : (n : Nat) → OkFam LocalsII n → Sort u_1} →
    {motive_3 : (n : Nat) → Fam LocalsII n → Sort u_1} →
      {motive_4 : (n : Nat) → (a : Fam LocalsII n) → motive_3 n a → FamOk LocalsII a → Prop} →
        {motive_5 : (n : Nat) → (a : OkFam LocalsII n) → motive_2 n a → LocalsII.Ok n a → Prop} →
          motive_1 LocalsII.tip →
            ((n : Nat) →
                (x : OkFam LocalsII n) →
                  (a : LocalsII.Ok n x) → (x_ih : motive_2 n x) → motive_5 n x x_ih a → motive_1 (LocalsII.mk n x a)) →
              ((n : Nat) →
                  (v : Fam LocalsII n) →
                    (h : FamOk LocalsII v) → (v_ih : motive_3 n v) → motive_4 n v v_ih h → motive_2 n (OkFam.mk v h)) →
                (mk_2 : (n : Nat) → (a : LocalsII) → motive_1 a → motive_3 n (Fam.mk a)) →
                  (∀ (n : Nat) (a : LocalsII) (a_ih : motive_1 a), motive_4 n (Fam.mk a) (mk_2 n a a_ih) ⋯) →
                    (∀ (n : Nat) (x : OkFam LocalsII n) (x_ih : motive_2 n x), motive_5 n x x_ih ⋯) →
                      (t : LocalsII) → motive_1 t
-/
#guard_msgs in
#check @LocalsII.rec

/--
info: @LocalsII.Ok.rec : ∀ {motive : (n : Nat) → (a : OkFam LocalsII n) → LocalsII.Ok n a → Prop},
  (∀ (n : Nat) (x : OkFam LocalsII n), motive n x ⋯) →
    ∀ {n : Nat} {a : OkFam LocalsII n} (h : LocalsII.Ok n a), motive n a h
-/
#guard_msgs in
#check @LocalsII.Ok.rec

namespace LocalsII

def size (t : LocalsII) : Nat :=
  LocalsII.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    (motive_3 := fun _ _ => Nat) (motive_4 := fun _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ => True)
    1 (fun _ _ _ ih _ => 1 + ih)
    (fun _ _ _ ihv _ => ihv)
    (fun _ _ ih => ih)
    (fun _ _ _ => trivial)
    (fun _ _ _ => trivial)
    t

example : size .tip = 1 := rfl

/-- info: 2 -/
#guard_msgs in
#eval size (.mk 7 (.mk (.mk LocalsII.tip) (.mk LocalsII.tip)) (.mk _ _))

/-- info: 'LocalsII.size' does not depend on any axioms -/
#guard_msgs in
#print axioms size

end LocalsII

/-! ## The off switch -/

/-- error: (kernel) unknown constant 'Off2' -/
#guard_msgs in
set_option mumi.enabled false in
inductive Off2 where
  | mk (x : WFTree Off2)
