import Mumi

/-!
# Induction-induction through `Prop`

`Mumi.IndInd` handles a `mutual` block one of whose members' *arities* mentions
a sibling, provided the dependency runs only through proofs.  Lean rejects every
block in this file outright -- a member's arity names a constant that is not yet
in scope -- so there is nothing here whose behaviour could have changed.

The point of each test is that the *visible* declarations are the ones written,
that both iota rules hold by `rfl`, that the result computes, and that no axiom
is added.
-/

/-! ## The motivating block

A context, and the proposition that a name is fresh for it.  `Fresh`'s arity
mentions `Ctx`, and `Ctx.snoc` carries a `Fresh`.
-/

mutual
inductive Ctx : Type where
  | nil : Ctx
  | snoc : (Γ : Ctx) → (x : String) → Fresh x Γ → Ctx
inductive Fresh : String → Ctx → Prop where
  | nil : (x : String) → Fresh x .nil
  | snoc : (x y : String) → (Γ : Ctx) → (h : Fresh y Γ) → x ≠ y → Fresh x Γ →
    Fresh x (.snoc Γ y h)
end

/-- info: Ctx : Type -/
#guard_msgs in
#check @Ctx

/-- info: Fresh : String → Ctx → Prop -/
#guard_msgs in
#check @Fresh

/-- info: Ctx.nil : Ctx -/
#guard_msgs in
#check @Ctx.nil

/-- info: Ctx.snoc : (Γ : Ctx) → (x : String) → Fresh x Γ → Ctx -/
#guard_msgs in
#check @Ctx.snoc

/-- info: Fresh.nil : ∀ (x : String), Fresh x Ctx.nil -/
#guard_msgs in
#check @Fresh.nil

/--
info: Fresh.snoc : ∀ (x y : String) (Γ : Ctx) (h : Fresh y Γ), x ≠ y → Fresh x Γ → Fresh x (Γ.snoc y h)
-/
#guard_msgs in
#check @Fresh.snoc

/--
info: @Ctx.rec : {C : Ctx → Sort u_1} →
  C Ctx.nil → ((Γ : Ctx) → (x : String) → (a : Fresh x Γ) → C Γ → C (Γ.snoc x a)) → (t : Ctx) → C t
-/
#guard_msgs in
#check @Ctx.rec

/-! ### The recursor computes, and both iota rules are definitional -/

def Ctx.length (Γ : Ctx) : Nat :=
  Ctx.rec (C := fun _ => Nat) 0 (fun _ _ _ ih => ih + 1) Γ

example {C : Ctx → Sort u} (n : C .nil)
    (s : (Γ : Ctx) → (x : String) → (h : Fresh x Γ) → C Γ → C (.snoc Γ x h)) :
    Ctx.rec n s .nil = n := rfl

example {C : Ctx → Sort u} (n : C .nil)
    (s : (Γ : Ctx) → (x : String) → (h : Fresh x Γ) → C Γ → C (.snoc Γ x h))
    (Γ : Ctx) (x : String) (h : Fresh x Γ) :
    Ctx.rec n s (.snoc Γ x h) = s Γ x h (Ctx.rec n s Γ) := rfl

/-- A closed term, built through the `Fresh` obligations. -/
def ex : Ctx :=
  .snoc (.snoc .nil "x" (.nil "x")) "y"
    (.snoc "y" "x" .nil (.nil "x") (by decide) (.nil "y"))

/-- info: 2 -/
#guard_msgs in
#eval ex.length

example : ex.length = 2 := rfl

/-- info: 'Ctx.rec' does not depend on any axioms -/
#guard_msgs in
#print axioms Ctx.rec

/-- info: 'ex' does not depend on any axioms -/
#guard_msgs in
#print axioms ex

/-- info: 'Ctx.length' does not depend on any axioms -/
#guard_msgs in
#print axioms Ctx.length

/-! ### `induction ... using` is the way to reason about it

The constructors are `def`s, so `match` and a bare `cases` do not see them.  The
recursor's minor premises are named after the constructors, so `induction using`
reads the way it would for a real inductive.

A `Prop` member has one too, and it is indexed, so its indices are listed as
targets just as they would be for a stock indexed family.
-/

example (Γ : Ctx) : 0 ≤ Γ.length := by
  induction Γ using Ctx.rec with
  | nil => simp [Ctx.length]
  | snoc Γ x h ih => simp

example (x : String) (Γ : Ctx) (h : Fresh x Γ) : 0 ≤ Γ.length := by
  induction x, Γ, h using Fresh.rec with
  | nil x => simp [Ctx.length]
  | snoc x y Γ h hne h' ih ih' => simp

/-! ## Several `Prop` members

Any number of propositions may hang off one data member.
-/

mutual
inductive Tm : Type where
  | var : Nat → Tm
  | app : (f : Tm) → (a : Tm) → Ok f → Ok a → Tm
  | lam : (b : Tm) → Closed b → Tm
inductive Ok : Tm → Prop where
  | var : (n : Nat) → Ok (.var n)
  | lam : (b : Tm) → (h : Closed b) → Ok (.lam b h)
inductive Closed : Tm → Prop where
  | var : (n : Nat) → Closed (.var n)
  | lam : (b : Tm) → (h : Closed b) → Closed (.lam b h)
end

/-- info: Tm.app : (f a : Tm) → Ok f → Ok a → Tm -/
#guard_msgs in
#check @Tm.app

/-- info: Tm.lam : (b : Tm) → Closed b → Tm -/
#guard_msgs in
#check @Tm.lam

/-- info: Closed.lam : ∀ (b : Tm) (h : Closed b), Closed (b.lam h) -/
#guard_msgs in
#check @Closed.lam

def Tm.size (t : Tm) : Nat :=
  Tm.rec (C := fun _ => Nat) (fun _ => 1) (fun _ _ _ _ i j => i + j + 1)
    (fun _ _ i => i + 1) t

example : Tm.size (.var 3) = 1 := rfl

example (f a : Tm) (hf : Ok f) (ha : Ok a) :
    Tm.size (.app f a hf ha) = Tm.size f + Tm.size a + 1 := rfl

/-- info: 4 -/
#guard_msgs in
#eval Tm.size (.app (.lam (.var 0) (.var 0)) (.var 1) (.lam (.var 0) (.var 0)) (.var 1))

/-- info: 'Tm.size' does not depend on any axioms -/
#guard_msgs in
#print axioms Tm.size

/-! ## The `Prop` member may come first -/

mutual
inductive Ok3 : Vec3 → Prop where
  | nil : Ok3 .nil
inductive Vec3 : Type where
  | nil : Vec3
  | cons : (v : Vec3) → Ok3 v → Vec3
end

/-- info: Vec3.cons : (v : Vec3) → Ok3 v → Vec3 -/
#guard_msgs in
#check @Vec3.cons

def Vec3.size (v : Vec3) : Nat :=
  Vec3.rec (C := fun _ => Nat) 0 (fun _ _ ih => ih + 1) v

/-- info: 1 -/
#guard_msgs in
#eval Vec3.size (.cons .nil .nil)

example : Vec3.size (.cons .nil .nil) = 1 := rfl

/-! ## Indices

Both members are indexed, and the `Prop` member is indexed by the data member at
one of its own indices.
-/

mutual
inductive IVec : Nat → Type where
  | nil : IVec 0
  | cons : (n : Nat) → (v : IVec n) → (x : Nat) → IFresh x n v → IVec (n + 1)
inductive IFresh : Nat → (n : Nat) → IVec n → Prop where
  | nil : (x : Nat) → IFresh x 0 .nil
  | cons : (x y n : Nat) → (v : IVec n) → (h : IFresh y n v) → x ≠ y → IFresh x n v →
      IFresh x (n + 1) (.cons n v y h)
end

/-- info: IVec.cons : (n : Nat) → (v : IVec n) → (x : Nat) → IFresh x n v → IVec (n + 1) -/
#guard_msgs in
#check @IVec.cons

/--
info: IFresh.cons : ∀ (x y n : Nat) (v : IVec n) (h : IFresh y n v),
  x ≠ y → IFresh x n v → IFresh x (n + 1) (IVec.cons n v y h)
-/
#guard_msgs in
#check @IFresh.cons

/--
info: @IVec.rec : {C : (a : Nat) → IVec a → Sort u_1} →
  C 0 IVec.nil →
    ((n : Nat) → (v : IVec n) → (x : Nat) → (a : IFresh x n v) → C n v → C (n + 1) (IVec.cons n v x a)) →
      (a : Nat) → (t : IVec a) → C a t
-/
#guard_msgs in
#check @IVec.rec

def IVec.sum : (n : Nat) → IVec n → Nat :=
  fun n v => IVec.rec (C := fun _ _ => Nat) 0 (fun _ _ x _ ih => ih + x) n v

def exVec : IVec 1 := .cons 0 .nil 5 (.nil 5)

/-- info: 5 -/
#guard_msgs in
#eval exVec.sum

example : IVec.sum 1 exVec = 5 := rfl

example {C : (n : Nat) → IVec n → Sort u} (nil : C 0 .nil)
    (cons : (n : Nat) → (v : IVec n) → (x : Nat) → (h : IFresh x n v) → C n v →
      C (n + 1) (.cons n v x h)) (n : Nat) (v : IVec n) (x : Nat) (h : IFresh x n v) :
    IVec.rec nil cons (n + 1) (.cons n v x h)
      = cons n v x h (IVec.rec nil cons n v) := rfl

/-- info: 'IVec.sum' does not depend on any axioms -/
#guard_msgs in
#print axioms IVec.sum

-- the indices are generalised along with the major premise
example (n : Nat) (v : IVec n) : 0 ≤ IVec.sum n v := by
  induction n, v using IVec.rec with
  | nil => simp [IVec.sum]
  | cons n v x h ih => simp

/-! ## Several data members

The data members become one mutual pre-block, so each of their recursors takes
one motive per data member and one minor premise per constructor of any of them.
-/

mutual
inductive Ctx2 : Type where
  | nil : Ctx2
  | snoc : (Γ : Ctx2) → (t : Ty) → Wf Γ t → Ctx2
inductive Ty : Type where
  | base : Ty
  | arr : (a b : Ty) → Ty
inductive Wf : Ctx2 → Ty → Prop where
  | base : (Γ : Ctx2) → Wf Γ .base
end

/--
info: @Ctx2.rec : {C_Ctx2 : Ctx2 → Sort u_1} →
  {C_Ty : Ty → Sort u_1} →
    C_Ctx2 Ctx2.nil →
      ((Γ : Ctx2) → (t : Ty) → (a : Wf Γ t) → C_Ctx2 Γ → C_Ty t → C_Ctx2 (Γ.snoc t a)) →
        C_Ty Ty.base → ((a b : Ty) → C_Ty a → C_Ty b → C_Ty (a.arr b)) → (t : Ctx2) → C_Ctx2 t
-/
#guard_msgs in
#check @Ctx2.rec

/--
info: @Ty.rec : {C_Ctx2 : Ctx2 → Sort u_1} →
  {C_Ty : Ty → Sort u_1} →
    C_Ctx2 Ctx2.nil →
      ((Γ : Ctx2) → (t : Ty) → (a : Wf Γ t) → C_Ctx2 Γ → C_Ty t → C_Ctx2 (Γ.snoc t a)) →
        C_Ty Ty.base → ((a b : Ty) → C_Ty a → C_Ty b → C_Ty (a.arr b)) → (t : Ty) → C_Ty t
-/
#guard_msgs in
#check @Ty.rec

def Ctx2.length (Γ : Ctx2) : Nat :=
  Ctx2.rec (C_Ctx2 := fun _ => Nat) (C_Ty := fun _ => Nat)
    0 (fun _ _ _ ih _ => ih + 1) 1 (fun _ _ i j => i + j + 1) Γ

def Ty.size (t : Ty) : Nat :=
  Ty.rec (C_Ctx2 := fun _ => Nat) (C_Ty := fun _ => Nat)
    0 (fun _ _ _ ih _ => ih + 1) 1 (fun _ _ i j => i + j + 1) t

def exCtx2 : Ctx2 := .snoc .nil .base (.base .nil)

/-- info: 1 -/
#guard_msgs in
#eval exCtx2.length

/-- info: 3 -/
#guard_msgs in
#eval (Ty.arr .base .base).size

example : exCtx2.length = 1 := rfl

/-- info: 'Ctx2.length' does not depend on any axioms -/
#guard_msgs in
#print axioms Ctx2.length

/-! ## Infinitary recursive fields

`Nat → Tree` recurses under a binder, and the induction hypothesis follows it.
-/

mutual
inductive Tree : Type where
  | leaf : Tree
  | node : (f : Nat → Tree) → Good f → Tree
inductive Good : (Nat → Tree) → Prop where
  | leaf : Good (fun _ => .leaf)
end

/-- info: Tree.node : (f : Nat → Tree) → Good f → Tree -/
#guard_msgs in
#check @Tree.node

/--
info: @Tree.rec : {C : Tree → Sort u_1} →
  C Tree.leaf → ((f : Nat → Tree) → (a : Good f) → ((a : Nat) → C (f a)) → C (Tree.node f a)) → (t : Tree) → C t
-/
#guard_msgs in
#check @Tree.rec

def Tree.depthAt (t : Tree) (k : Nat) : Nat :=
  Tree.rec (C := fun _ => Nat → Nat) (fun _ => 0)
    (fun _ _ ih k => ih k k + 1) t k

/-- info: 1 -/
#guard_msgs in
#eval Tree.depthAt (.node (fun _ => .leaf) .leaf) 3

example : Tree.depthAt (.node (fun _ => .leaf) .leaf) 3 = 1 := rfl

/-! ## Parameters and universe parameters

The parameters lead every arity, every constructor and the recursor, and are
implicit on the last two.  The universe parameters are shared by the whole
block, as they are for a Lean `mutual`.
-/

mutual
inductive Bag (α : Type u) (β : Type v) : Nat → Type (max u v) where
  | nil : Bag α β 0
  | cons : (n : Nat) → (b : Bag α β n) → (t : Tag2 α β) → OkB α β n b t → Bag α β (n + 1)
inductive Tag2 (α : Type u) (β : Type v) : Type (max u v) where
  | mk : α → β → Tag2 α β
inductive OkB (α : Type u) (β : Type v) : (n : Nat) → Bag α β n → Tag2 α β → Prop where
  | nil : (t : Tag2 α β) → OkB α β 0 .nil t
end

/-- info: Bag : Type u_1 → Type u_2 → Nat → Type (max u_1 u_2) -/
#guard_msgs in
#check @Bag

/-- info: OkB : (α : Type u_1) → (β : Type u_2) → (n : Nat) → Bag α β n → Tag2 α β → Prop -/
#guard_msgs in
#check @OkB

/--
info: @Bag.cons : {α : Type u_1} →
  {β : Type u_2} → (n : Nat) → (b : Bag α β n) → (t : Tag2 α β) → OkB α β n b t → Bag α β (n + 1)
-/
#guard_msgs in
#check @Bag.cons

/-- info: @OkB.nil : ∀ {α : Type u_1} {β : Type u_2} (t : Tag2 α β), OkB α β 0 Bag.nil t -/
#guard_msgs in
#check @OkB.nil

/--
info: @Bag.rec : {α : Type u_2} →
  {β : Type u_3} →
    {C_Bag : (a : Nat) → Bag α β a → Sort u_1} →
      {C_Tag2 : Tag2 α β → Sort u_1} →
        C_Bag 0 Bag.nil →
          ((n : Nat) →
              (b : Bag α β n) →
                (t : Tag2 α β) → (a : OkB α β n b t) → C_Bag n b → C_Tag2 t → C_Bag (n + 1) (Bag.cons n b t a)) →
            ((a : α) → (a_1 : β) → C_Tag2 (Tag2.mk a a_1)) → (a : Nat) → (t : Bag α β a) → C_Bag a t
-/
#guard_msgs in
#check @Bag.rec

def Bag.count {α : Type u} {β : Type v} : (n : Nat) → Bag α β n → Nat :=
  fun n b => Bag.rec (C_Bag := fun _ _ => Nat) (C_Tag2 := fun _ => Nat)
    0 (fun _ _ _ _ ih _ => ih + 1) (fun _ _ => 0) n b

def exBag : Bag String Nat 1 := .cons 0 .nil (.mk "a" 3) (.nil (.mk "a" 3))

/-- info: 1 -/
#guard_msgs in
#eval exBag.count

example : Bag.count 1 exBag = 1 := rfl

/-- info: 'exBag' does not depend on any axioms -/
#guard_msgs in
#print axioms exBag

/-- info: 'Bag.count' does not depend on any axioms -/
#guard_msgs in
#print axioms Bag.count

/-! ## Resulting types left out, and members named under one another

A member that gives no resulting type at all is read as `Type`, which is what
`inductive Tree where` means.  This block also names two of its `Prop` members
*under* a data member -- `TreeNested.WF` beside `TreeNested` -- so "this type
mentions a data member" has to be decided by exact name and not by prefix; and
its three data members form a cycle that runs through both `Prop` members.

All five recursors are pinned below.  What that is checking, beyond the shapes,
is that none of them mentions a name the user did not write: no `_pre`, no
`_wf`, no `nested_` copy.
-/

mutual
inductive TreeNested where
  | empty
  | node (key : Nat) (value : RecWFTree) (l r : TreeNested)
inductive TreeNested.WFWith : TreeNested → List Nat → Prop where
  | empty : TreeNested.WFWith .empty []
  | node {llist rlist : List Nat} (key : Nat) (value : RecWFTree) (l r : TreeNested)
    (hl : TreeNested.WFWith l llist) (hr : TreeNested.WFWith r rlist)
    (hl' : ∀ a ∈ llist, a < key) (hr' : ∀ a ∈ rlist, key < a) :
    TreeNested.WFWith (.node key value l r) (llist ++ key :: rlist)
inductive TreeNested.WF : TreeNested → Prop where
  | intro (l : List Nat) (t : TreeNested) (h : TreeNested.WFWith t l) : TreeNested.WF t
inductive WFTreeNested where
  | mk (x : TreeNested) (h : TreeNested.WF x) : WFTreeNested
inductive RecWFTree where
  | mk (x : WFTreeNested)
end

/-- info: TreeNested : Type -/
#guard_msgs in
#check @TreeNested

/-- info: TreeNested.node : Nat → RecWFTree → TreeNested → TreeNested → TreeNested -/
#guard_msgs in
#check @TreeNested.node

/-- info: TreeNested.WFWith : TreeNested → List Nat → Prop -/
#guard_msgs in
#check @TreeNested.WFWith

/-- info: WFTreeNested.mk : (x : TreeNested) → x.WF → WFTreeNested -/
#guard_msgs in
#check @WFTreeNested.mk

/--
info: @TreeNested.rec : {C_TreeNested : TreeNested → Sort u_1} →
  {C_WFTreeNested : WFTreeNested → Sort u_1} →
    {C_RecWFTree : RecWFTree → Sort u_1} →
      C_TreeNested TreeNested.empty →
        ((key : Nat) →
            (value : RecWFTree) →
              (l r : TreeNested) →
                C_RecWFTree value → C_TreeNested l → C_TreeNested r → C_TreeNested (TreeNested.node key value l r)) →
          ((x : TreeNested) → (h : x.WF) → C_TreeNested x → C_WFTreeNested (WFTreeNested.mk x h)) →
            ((x : WFTreeNested) → C_WFTreeNested x → C_RecWFTree (RecWFTree.mk x)) → (t : TreeNested) → C_TreeNested t
-/
#guard_msgs in
#check @TreeNested.rec

/--
info: @WFTreeNested.rec : {C_TreeNested : TreeNested → Sort u_1} →
  {C_WFTreeNested : WFTreeNested → Sort u_1} →
    {C_RecWFTree : RecWFTree → Sort u_1} →
      C_TreeNested TreeNested.empty →
        ((key : Nat) →
            (value : RecWFTree) →
              (l r : TreeNested) →
                C_RecWFTree value → C_TreeNested l → C_TreeNested r → C_TreeNested (TreeNested.node key value l r)) →
          ((x : TreeNested) → (h : x.WF) → C_TreeNested x → C_WFTreeNested (WFTreeNested.mk x h)) →
            ((x : WFTreeNested) → C_WFTreeNested x → C_RecWFTree (RecWFTree.mk x)) →
              (t : WFTreeNested) → C_WFTreeNested t
-/
#guard_msgs in
#check @WFTreeNested.rec

/--
info: @RecWFTree.rec : {C_TreeNested : TreeNested → Sort u_1} →
  {C_WFTreeNested : WFTreeNested → Sort u_1} →
    {C_RecWFTree : RecWFTree → Sort u_1} →
      C_TreeNested TreeNested.empty →
        ((key : Nat) →
            (value : RecWFTree) →
              (l r : TreeNested) →
                C_RecWFTree value → C_TreeNested l → C_TreeNested r → C_TreeNested (TreeNested.node key value l r)) →
          ((x : TreeNested) → (h : x.WF) → C_TreeNested x → C_WFTreeNested (WFTreeNested.mk x h)) →
            ((x : WFTreeNested) → C_WFTreeNested x → C_RecWFTree (RecWFTree.mk x)) → (t : RecWFTree) → C_RecWFTree t
-/
#guard_msgs in
#check @RecWFTree.rec

-- the minors of a `Prop` recursor conclude at a constructor application, which
-- is what this test is about; without `pp.proofs` they all print as `⋯`
/--
info: @TreeNested.WFWith.rec : ∀ {C_WFWith : (a : TreeNested) → (a_1 : List Nat) → a.WFWith a_1 → Prop}
  {C_WF : (a : TreeNested) → a.WF → Prop},
  C_WFWith TreeNested.empty [] TreeNested.WFWith.empty →
    (∀ {llist rlist : List Nat} (key : Nat) (value : RecWFTree) (l r : TreeNested) (hl : l.WFWith llist)
        (hr : r.WFWith rlist) (hl' : ∀ (a : Nat), a ∈ llist → a < key) (hr' : ∀ (a : Nat), a ∈ rlist → key < a),
        C_WFWith l llist hl →
          C_WFWith r rlist hr →
            C_WFWith (TreeNested.node key value l r) (llist ++ key :: rlist)
              (TreeNested.WFWith.node key value l r hl hr hl' hr')) →
      (∀ (l : List Nat) (t : TreeNested) (h : t.WFWith l), C_WFWith t l h → C_WF t (TreeNested.WF.intro l t h)) →
        ∀ (a : TreeNested) (a_1 : List Nat) (h : a.WFWith a_1), C_WFWith a a_1 h
-/
#guard_msgs in
set_option pp.proofs true in
#check @TreeNested.WFWith.rec

/--
info: @TreeNested.WF.rec : ∀ {C_WFWith : (a : TreeNested) → (a_1 : List Nat) → a.WFWith a_1 → Prop}
  {C_WF : (a : TreeNested) → a.WF → Prop},
  C_WFWith TreeNested.empty [] TreeNested.WFWith.empty →
    (∀ {llist rlist : List Nat} (key : Nat) (value : RecWFTree) (l r : TreeNested) (hl : l.WFWith llist)
        (hr : r.WFWith rlist) (hl' : ∀ (a : Nat), a ∈ llist → a < key) (hr' : ∀ (a : Nat), a ∈ rlist → key < a),
        C_WFWith l llist hl →
          C_WFWith r rlist hr →
            C_WFWith (TreeNested.node key value l r) (llist ++ key :: rlist)
              (TreeNested.WFWith.node key value l r hl hr hl' hr')) →
      (∀ (l : List Nat) (t : TreeNested) (h : t.WFWith l), C_WFWith t l h → C_WF t (TreeNested.WF.intro l t h)) →
        ∀ (a : TreeNested) (h : a.WF), C_WF a h
-/
#guard_msgs in
set_option pp.proofs true in
#check @TreeNested.WF.rec

theorem leafWF : TreeNested.WF .empty := .intro [] _ .empty

def leaf : RecWFTree := .mk (.mk .empty leafWF)

def one : TreeNested := .node 3 leaf .empty .empty

theorem oneWFWith : TreeNested.WFWith one [3] :=
  .node 3 leaf .empty .empty .empty .empty (by simp) (by simp)

theorem oneWF : TreeNested.WF one := .intro _ _ oneWFWith

def oneR : RecWFTree := .mk (.mk one oneWF)

def TreeNested.size : TreeNested → Nat :=
  TreeNested.rec (C_TreeNested := fun _ => Nat) (C_WFTreeNested := fun _ => Nat)
    (C_RecWFTree := fun _ => Nat)
    0 (fun _ _ _ _ v l r => v + l + r + 1) (fun _ _ n => n) (fun _ n => n)

example : TreeNested.size .empty = 0 := rfl
example : TreeNested.size one = 1 := rfl

/-- info: 3 -/
#guard_msgs in
#eval TreeNested.size (.node 1 oneR one .empty)

/-- info: 'TreeNested.size' does not depend on any axioms -/
#guard_msgs in
#print axioms TreeNested.size

/-- info: 'leafWF' does not depend on any axioms -/
#guard_msgs in
#print axioms leafWF

example (t : TreeNested) (h : t.WF) : True := by cases h; trivial

/-! ## A block we must not claim

An arity mentioning a member's short name is only the *signature* of
induction-induction.  Here `Tag` in `Uses`'s arity means the global `Tag`, not
the sibling being declared, so the block elaborates the way Lean elaborates it
and we never see it: the routing asks whether the headers failed first, and only
then whether an arity names a sibling.
-/

def Tag : Type := Nat

namespace Inner

mutual
inductive Tag : Type where
  | mk : Tag
inductive Uses : Tag → Type where
  | mk : (n : Nat) → Uses n
end

-- the arity resolved to the global, exactly as it does without `Mumi` imported
/-- info: Uses : _root_.Tag → Type -/
#guard_msgs in
#check @Uses

-- and Lean's own elaborator ran: a genuine mutual recursor, with two motives
/--
info: @Uses.rec : {motive_1 : Tag → Sort u_1} →
  {motive_2 : (a : _root_.Tag) → Uses a → Sort u_1} →
    motive_1 Tag.mk → ((n : Nat) → motive_2 n (Uses.mk n)) → {a : _root_.Tag} → (t : Uses a) → motive_2 a t
-/
#guard_msgs in
#check @Uses.rec

-- real constructors, so `match` works -- which is what our lowering gives up
example : (match Uses.mk 3 with | .mk n => n) = 3 := rfl

end Inner

/-! ## Outside the narrow class

Every one of these is rejected with an explanation of what erasure could not do,
rather than lowered wrongly.
-/

-- genuine induction-induction through *data*: erasure has nothing to erase
/--
error: The arity of `Len` mentions the block.  Erasure can only reach an induction-induction whose dependency runs through `Prop`, and this one indexes data by data
-/
#guard_msgs in
mutual
inductive Vec4 : Type where
  | nil : Vec4
  | cons : (v : Vec4) → (n : Len v) → Vec4
inductive Len : Vec4 → Type where
  | nil : Len .nil
end

-- a proposition of the block hidden inside a piece of data
/--
error: The field `n` of `Vec2.cons` mentions the block, but is neither a member's type nor a proof of one of the block's propositions, so this lowering cannot erase it:
  { m // Ok2 v }
-/
#guard_msgs in
mutual
inductive Vec2 : Type where
  | nil : Vec2
  | cons : (v : Vec2) → (n : { m : Nat // Ok2 v }) → Vec2
inductive Ok2 : Vec2 → Prop where
  | nil : Ok2 .nil
end

-- an erased field whose type mentions a *data* member: `a = b` and
-- `a.val = b.val` are different propositions, so erasing it is visible
/--
error: The field `h` of `C1.snoc` mentions the block, but is neither a member's type nor a proof of one of the block's propositions, so this lowering cannot erase it:
  a = b
-/
#guard_msgs in
mutual
inductive C1 : Type where
  | nil : C1
  | snoc : (a : C1) → (b : C1) → (h : a = b) → P1 a → C1
inductive P1 : C1 → Prop where
  | nil : P1 .nil
end

-- a recursive field that *binds* a member: there is no way back from the
-- pre-world without a well-formedness proof, so `f` could not be applied
/--
error: The field `f` of `T3.node` binds a member of the block before recursing, which erasure cannot follow: a pre-world value cannot be turned back into a real one without its well-formedness proof.
  T3 → T3
-/
#guard_msgs in
mutual
inductive T3 : Type where
  | leaf : T3
  | node : (f : T3 → T3) → G3 f → T3
inductive G3 : (T3 → T3) → Prop where
  | id : G3 id
end

-- the data members share one pre-block, so the kernel's own rule applies
/--
error: The data members `A4` and `B4` of this induction-inductive block live in different universes, `Type` and `Type 1`; the erased pre-block is a single mutual inductive, so they must agree
-/
#guard_msgs in
mutual
inductive A4 : Type where
  | mk : (b : B4) → P4 b → A4
inductive B4 : Type 1 where
  | mk : B4
inductive P4 : B4 → Prop where
  | mk : P4 .mk
end

-- a `Prop` member's index is rewritten one index at a time, and `List C5` has
-- no image on the erased types
/--
error: The index `a✝` of `P5` mentions the block without being a member's type, so it has no counterpart on the erased types:
  List C5
-/
#guard_msgs in
mutual
inductive C5 : Type where
  | nil : C5
  | snoc : (a : C5) → P5 [a] → C5
inductive P5 : List C5 → Prop where
  | nil : P5 []
end

-- a data member is encoded as a `Subtype`, which lands in `Sort (max 1 u)`
/--
error: The data member `S` lives at `Sort u`, which could still be `Prop`.  It is encoded as a subtype, and `Subtype` lands one universe up from `Prop`, so a data member's universe has to be visibly non-zero -- `Type v` rather than `Sort v`
-/
#guard_msgs in
mutual
inductive S (α : Sort u) : Sort u where
  | mk : (a : S α) → PS α a → S α
inductive PS (α : Sort u) : S α → Prop where
  | mk : (a : S α) → PS α a
end

-- the whole encoding runs under one telescope of parameters
/--
error: `P7` takes 1 parameter(s) and `Q7` takes 0; every member of a mutual block must take the same ones
-/
#guard_msgs in
mutual
inductive P7 (α : Type) : Type where
  | nil : P7 α
  | mk : (x : P7 α) → Q7 x → P7 α
inductive Q7 : P7 Nat → Prop where
  | nil : Q7 .nil
end

-- and one list of universe parameters
/--
error: `K1` and `K2` declare different universe parameters; every member of a mutual block must declare the same ones
-/
#guard_msgs in
mutual
inductive K1.{u} : Type u where
  | mk : (k : K1.{u}) → K2 k → K1
inductive K2.{u, v} : K1.{u} → Prop where
  | mk : (k : K1.{u}) → K2 k
end

-- a constructor of an indexed family has to say what its indices are, or the
-- resulting type would be the unapplied family, which is not a proposition
/--
error: Missing resulting type for constructor `Q8.mk`.  It must be given because `Q8` is an inductive family
-/
#guard_msgs in
mutual
inductive P8 where
  | nil
  | mk : (x : P8) → Q8 x → P8
inductive Q8 : P8 → Prop where
  | mk
end

-- a resulting type left out is read as `Type`, and the fields have to fit: the
-- guess is already in the sibling's elaborated fields by the time we know
/--
error: `Cell` gives no resulting type, so it was read as `Type`; but the field `α` of `Cell.mk` lives in `Type 1`, which does not fit.  Write the resulting type out: `inductive Cell : Type 1`
-/
#guard_msgs in
mutual
inductive Cell where
  | mk : (α : Type) → (c : Cell) → CellOk c → Cell
inductive CellOk : Cell → Prop where
  | mk : (c : Cell) → CellOk c
end
