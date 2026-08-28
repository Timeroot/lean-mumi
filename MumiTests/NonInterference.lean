import Mumi

/-!
# Everything else still goes through Lean

`Mumi.elabMutualHeterogeneous` steps aside for every block except one of two or
more plain `inductive`s that Lean would reject for living in several universes.
These are the blocks it must not touch.
-/

/-! ## `mutual def` -/

mutual
  def foo : Nat → Nat
    | 0 => 0
    | n + 1 => bar n
  def bar : Nat → Nat
    | 0 => 1
    | n + 1 => foo n
end

example : foo 4 = 0 := rfl
example : bar 4 = 1 := rfl

/-- info: 0 -/
#guard_msgs in
#eval foo 4

/-! ## `mutual theorem` -/

mutual
  theorem evenSucc : ∀ n, foo n = 0 ∨ foo n = 1
    | 0 => Or.inl rfl
    | n + 1 => oddSucc n
  theorem oddSucc : ∀ n, bar n = 0 ∨ bar n = 1
    | 0 => Or.inr rfl
    | n + 1 => evenSucc n
end

/-! ## A homogeneous inductive block

This is the case the library must leave alone even though it *is* a mutual
inductive block: it gets Lean's own `rec`, and no `mutualRec`. -/

mutual
inductive T1 : Type where
  | mk : T2 → T1
inductive T2 : Type where
  | stop : T2
  | mk : T1 → T2
end

-- `noncomputable` because Lean does not give a homogeneous block's `rec` a
-- compiler implementation; that it is still needed here is the clearest sign
-- that this block went through Lean and not through us
noncomputable def t1Depth : T1 → Nat :=
  @T1.rec (fun _ => Nat) (fun _ => Nat) (fun _ ih => ih + 1) 0 (fun _ ih => ih + 1)

example : t1Depth (T1.mk (T2.mk (T1.mk T2.stop))) = 3 := rfl

/-- error: Unknown constant `T1.mutualRec` -/
#guard_msgs in
#check @T1.mutualRec

/-! ## An all-`Prop` homogeneous block -/

mutual
inductive PEven : Nat → Prop where
  | zero : PEven 0
  | succ : (n : Nat) → POdd n → PEven (n + 1)
inductive POdd : Nat → Prop where
  | succ : (n : Nat) → PEven n → POdd (n + 1)
end

example : POdd 3 := .succ 2 (.succ 1 (.succ 0 .zero))

/-! ## Structures and classes in a `mutual` block -/

mutual
structure SA where
  n : Nat
  b : Option SB
structure SB where
  m : Nat
  a : Option SA
end

example : (SA.mk 3 none).n = 3 := rfl

mutual
inductive CA : Type where
  | mk : CB → CA
inductive CB : Type where
  | stop : CB
  | mk : CA → CB
  deriving Repr
end

/-! ## `deriving` on a homogeneous block -/

mutual
inductive DA : Type where
  | mk : DB → DA
  deriving Repr
inductive DB : Type where
  | stop : DB
  | mk : DA → DB
  deriving Repr
end

/-- info: DA.mk (DB.stop) -/
#guard_msgs in
#eval repr (DA.mk DB.stop)

/-! ## A single, non-mutual inductive -/

inductive Solo : Type where
  | leaf : Nat → Solo
  | node : Solo → Solo → Solo

/-! ## Nested inductives that work

Denesting happens in the *kernel*, which specialises the nesting type to the
block and checks the enlarged block instead.  `Mumi.Declaration` watches for
that check failing, so a nested inductive the kernel accepts is elaborated
entirely by Lean, and is exactly the declaration it always was.

The clearest evidence is `Tree.rec_1`, the auxiliary recursor the kernel adds
for the specialised `List`: nothing in this library produces one. -/

inductive Tree : Type where
  | node : List Tree → Tree

def treeSize : Tree → Nat
  | .node ts => 1 + go ts
where
  go : List Tree → Nat
    | [] => 0
    | t :: rest => treeSize t + go rest

example : treeSize (.node [.node [], .node []]) = 3 := rfl

/--
info: @Tree.rec_1 : {motive_1 : Tree → Sort u_1} →
  {motive_2 : List Tree → Sort u_1} →
    ((a : List Tree) → motive_2 a → motive_1 (Tree.node a)) →
      motive_2 [] →
        ((head : Tree) → (tail : List Tree) → motive_1 head → motive_2 tail → motive_2 (head :: tail)) →
          (t : List Tree) → motive_2 t
-/
#guard_msgs in
#check @Tree.rec_1

/-- error: Unknown constant `Tree.mutualRec` -/
#guard_msgs in
#check @Tree.mutualRec

/-- error: Unknown constant `Tree.nested_List_1` -/
#guard_msgs in
#check @Tree.nested_List_1

inductive ATree : Type where
  | node : Array ATree → ATree

/-- error: Unknown constant `ATree.mutualRec` -/
#guard_msgs in
#check @ATree.mutualRec

inductive ETree : Type where
  | node : Except String ETree → ETree

/-- error: Unknown constant `ETree.mutualRec` -/
#guard_msgs in
#check @ETree.mutualRec

/-! ## Nested inductives that fail for other reasons

Failing is not enough to be rescued: denesting has to be what turns the block
heterogeneous.  These four fail for reasons of their own, and get Lean's own
message, once. -/

-- the wrapper is a universe up, so the field does not fit its own member;
-- this is a genuine error and the elaborator catches it before the kernel
inductive HBox (α : Type) : Type 1 where
  | intro : α → HBox α

/--
error: Invalid universe level in constructor `Bad1.mk`: Parameter has type
  HBox Bad1
at universe level
  2
which is not less than or equal to the inductive type's resulting universe level
  1
-/
#guard_msgs in
inductive Bad1 : Type where
  | mk : HBox Bad1 → Bad1

-- `Squash` is a quotient, not an inductive, so there is nothing to specialise
/--
error: (kernel) arg #1 of 'Bad2.mk' contains a non valid occurrence of the datatypes being declared
-/
#guard_msgs in
inductive Bad2 : Type where
  | mk : Squash Bad2 → Bad2

/--
error: (kernel) arg #1 of 'Bad3.mk' has a non positive occurrence of the datatypes being declared
-/
#guard_msgs in
inductive Bad3 : Type where
  | mk : (Bad3 → Bad3) → Bad3

/--
error: Constructor field `NoSuchType` of `Bad4.mk` contains universe level metavariables at the expression
  Sort ?u.4
in its type
  Sort ?u.4
-/
#guard_msgs in
inductive Bad4 : Type where
  | mk : NoSuchType → Bad4

/-! ## Errors are still Lean's

A block that is heterogeneous *and* has a field too big for its own member is
reported against that member, by the same check Lean uses. -/

/--
error: Invalid universe level in constructor `U2.mk`: Parameter `t` has type
  Type 1
at universe level
  3
which is not less than or equal to the inductive type's resulting universe level
  1
-/
#guard_msgs in
mutual
inductive U1 : Prop where
  | mk : U2 → U1
inductive U2 : Type 0 where
  | mk : (t : Type 1) → U1 → U2
end

/-! ## The off switch

With `mumi.enabled` false the block is handed straight back to Lean, which
rejects it exactly as it does without this library imported. -/

/--
error: Invalid mutually inductive types: The resulting type of this declaration
  Type
differs from a preceding one
  Prop

Note: All inductive types declared in the same `mutual` block must belong to the same type universe
-/
#guard_msgs in
set_option mumi.enabled false in
mutual
inductive OffA : Prop where
  | mk : OffB → OffA
inductive OffB : Type where
  | mk : OffA → OffB
end
