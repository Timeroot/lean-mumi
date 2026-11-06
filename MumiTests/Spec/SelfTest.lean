import MumiTests.Spec.Harness

/-!
# The harness, tested

What Lean declares of a block it takes is the specification's ground truth, so
`mumi_spec` passes Lean's own blocks whole: an indexed mutual family, a nested
inductive, an inductive predicate that eliminates into any sort, and blocks with no
constructor at all.  And it
reports, at the block, each way a test's marks are wrong: a rule said to hold
only by `simp` that holds by `rfl`, a rule the specification does not state, a
kind of claim marked to fail that holds, a block said to be rejected that is
declared.
-/

set_option autoImplicit false

namespace Native

/-! What Lean's tactics do with an equation between constructors, on a nested inductive.
`MumiTests.Demo`'s last section pins where a block of ours does not do this yet. -/
namespace TacticsAtCtors
inductive T : Type where
  | leaf
  | node (cs : List T) (n : Nat)
example (cs n) : T.leaf ≠ T.node cs n := by intro h; contradiction
example (cs n) : T.leaf ≠ T.node cs n := fun e => T.noConfusion e
example (a b n m) (e : T.node a n = T.node b m) : a = b := by
  injection e with h1 h2
example (a b n m) (e : T.node a n = T.node b m) : a = b := by
  cases e; rfl
-- the other ways in, each of which goes through here
example (a b n m) (e : T.node a n = T.node b m) : a = b := by injections
example (a b n m) (e : T.node a n = T.node b m) : a = b := by rcases e with ⟨⟩; rfl
example (a n) (b : T) (e : T.node a n = b) : T.node a n = b := by rcases e with rfl; rfl
example (a n) (b : T) (e : T.node a n = b) : T.node a n = b := by obtain rfl := e; rfl
example (a b n m) (e : T.node a n = T.node b m) : a = b := by obtain ⟨⟩ := e; rfl
example (a b n m) (e : T.node a n = T.node b m) : a = b := by cases e with | refl => rfl
example (cs n) (h : T.leaf = T.node cs n) : False := by cases h with
example (cs n) (h : T.leaf = T.node cs n) : False := by rcases h with ⟨⟩
example (cs n) (h : T.leaf = T.node cs n) : False := by injections
-- `cases` where an index is a constructor application, which it has to solve
inductive At : T → Type where
  | atLeaf : At .leaf
  | atNode (cs n) : At (.node cs n)
inductive PAt : T → Prop where
  | leaf : PAt .leaf
  | node (cs n) : PAt (.node cs n)
example (a : At .leaf) : True := by cases a; trivial
example (cs n) (a : At (.node cs n)) : True := by cases a; trivial
example (cs n) (a : At (.node cs n)) : True := by cases a with | atNode => trivial
example (h : PAt .leaf) : True := by cases h; trivial
example (cs n) (h : PAt (.node cs n)) : True := by cases h; trivial
example (cs n) (h : PAt (.node cs n)) : True := by cases h with | node => trivial
example (cs n) (h : PAt (.node cs n)) : True := by rcases h with ⟨⟩; trivial
-- and where the constructor at the index rules a case out
example (a : At .leaf) : a = .atLeaf := by cases a; rfl
example (cs n) (a : At (.node cs n)) : a = .atNode cs n := by cases a; rfl
example (cs n) (a : At (.node cs n)) : a = .atNode cs n := by cases a with | atNode c m => rfl
example (cs n) (a b : At (.node cs n)) : a = b := by cases a; cases b; rfl
-- two such indices, one solved by the other's, and one ruling the only case out
inductive Two : T → T → Prop where
  | mk (cs n) : Two (.node cs n) (.node cs n)
example (a b n m) (h : Two (.node a n) (.node b m)) : a = b := by cases h; rfl
example (cs n) (h : Two .leaf (.node cs n)) : False := by cases h
example (cs n) (h : Two .leaf (.node cs n)) : False := nomatch h
example (x : T) (h : Two x x) : True := by cases h; trivial
-- under another inductive's constructor
inductive Deep : Option T → Prop where
  | mk (cs n) : Deep (some (.node cs n))
example (a n) (p : Deep (some (.node a n))) : True := by cases p; trivial
example (a b n m) (e : some (T.node a n) = some (T.node b m)) : a = b := by cases e; rfl
example (a b n m) (e : some (T.node a n) = some (T.node b m)) : a = b := by injections
-- naming the fields, and `match`, at such an index
inductive V : T → Type where
  | atNode (cs n) (m : Nat) : V (.node cs n)
inductive W : T → Type where
  | l : W .leaf
  | n (cs k) (w : W .leaf) : W (.node cs k)
example (cs n) (v : V (.node cs n)) : Nat := by rcases v with ⟨c, k, m⟩; exact m
example (cs n) (v : V (.node cs n)) : True := by obtain ⟨c, k, m⟩ := v; trivial
example (cs n) (v : V (.node cs n)) : Nat := match v with | .atNode _ _ m => m
example (cs n) : V (.node cs n) → Nat | .atNode _ _ m => m
example (cs n) (v : W (.node cs n)) : True := by match v with | .n _ _ _ => trivial
example (cs n) (v : W (.node cs n)) : True := by cases v with | n c k x => cases x; trivial
-- these Lean refuses of its own, so they owe nothing elsewhere
example (cs n) (v : W (.node cs n)) : True := by
  fail_if_success induction v with | l => trivial | n => trivial
  trivial
example (a b n m) (e : T.node a n = T.node b m) : a = b := by
  fail_if_success subst e
  cases e; rfl
-- `match` at such an index, with what comes with it
inductive Z : T → Type where
  | l (k : Nat) : Z .leaf
  | n (cs k) (w : Option Nat) : Z (.node cs k)
inductive R : T → Type where
  | stop (cs n) : R (.node cs n)
  | go (cs n) (r : R (.node cs n)) : R (.node cs n)
-- a field has both its names
example (cs n) (v : V (.node cs n)) : List T := match v with | .atNode c _ _ => c
example (cs n) (v : V (.node cs n)) : List T := match v with | .atNode _ _ _ => cs
-- a name that is a constructor is that constructor
def zval (cs n) (z : Z (.node cs n)) : Nat := match z with
  | .n _ _ none => 0
  | .n _ _ (some k) => k
example (cs n) : zval cs n (.n cs n (some 3)) = 3 := rfl
example (cs n) (z : Z (.node cs n)) (b : Bool) : Nat := match z, b with
  | .n _ _ none, true => 0
  | .n _ _ none, false => 1
  | .n _ _ (some k), _ => k
example (cs n) (z : Z (.node cs n)) : Nat := match z with | _ => 7
example (cs n) (z : Z (.node cs n)) : Nat := match z with | .n .. => 7
-- what is wrong is said
/--
error: Missing cases:
(Z.n _ _ (some _))
-/
#guard_msgs (error, drop warning) in
example (cs n) (z : Z (.node cs n)) : Nat := match z with | .n _ _ none => 0
-- and recursion, which even here is well-founded, so `simp` has its equations and `rfl` not
def rlen (cs n) : R (.node cs n) → Nat
  | .stop _ _ => 0
  | .go _ _ r => rlen cs n r + 1
example (cs n r) : rlen cs n (.go cs n r) = rlen cs n r + 1 := by simp [rlen]
-- an index no unifier solves is refused by Lean too: a block's `matching` mark can be this
inductive C : Nat → Type where
  | nil : C 0
  | join (n m : Nat) (x : C n) (y : C m) : C (n + m)
inductive CAt : {n : Nat} → C n → Prop where
  | nil : CAt .nil
  | join (n m x y) : CAt (.join n m x y)
example (h : CAt .nil) : True := by
  fail_if_success cases h
  trivial
end TacticsAtCtors


mumi_spec
mutual
inductive Ev : Nat → Type where
  | zero : Ev 0
  | succ {n : Nat} (o : Od n) : Ev (n + 1)
inductive Od : Nat → Type where
  | succ {n : Nat} (e : Ev n) (k : Nat) : Od (n + 1)
end

mumi_spec
inductive Rose (α : Type) : Type where
  | node (a : α) (kids : List (Rose α))

/-! Minor premises are named by their constructors' last names, and a name two
constructors share is bound twice: Lean does not rename the second, which a
named argument then cannot reach.  A member's constructor against a nesting's
(`nil` and `List.nil`), two nestings' (`Prod.mk` and `PProd.mk`, or `Prod.mk`
twice), and two members' (`A.mk` and `B.mk`). -/

namespace Names

mumi_spec
inductive T1 where
  | nil : T1
  | ofL : List T1 → T1

mumi_spec
inductive T2 where
  | base : T2
  | left : Prod T2 Nat → T2
  | right : PProd Nat T2 → T2

mumi_spec
inductive T3 where
  | fst : T3
  | left : Prod T3 Nat → T3
  | right : Prod T3 String → T3

mumi_spec
mutual
inductive A where
  | mk : A
  | b : B → A
inductive B where
  | mk : B
  | a : A → B
end

open Lean Meta in
/-- info: [motive_1, motive_2, nil, ofL, nil, cons, t] -/
#guard_msgs in
run_meta do
  forallTelescope (← getConstInfo ``T1.rec).type fun xs _ => do
    logInfo m!"{← xs.mapM fun x => return (← x.fvarId!.getDecl).userName}"

end Names

-- an instance parameter: `inj` takes it implicitly, `injEq` as an instance
mumi_spec
inductive WithInst (α : Type) [Inhabited α] : Type where
  | leaf : α → WithInst α

mumi_spec
inductive Le : Nat → Nat → Prop where
  | refl (n : Nat) : Le n n

-- no constructor anywhere: the motive is explicit, and the indices promoted
mumi_spec
inductive Never : Prop

mumi_spec
inductive Gap (n : Nat) : Nat → Type

/-! An inductive met in a nesting brings its whole mutual block with it, in that block's
order, before anything found inside it: `FamRose (FamForest X)` brings `FamForest
(FamForest X)` next, and only then what `FamRose`'s constructors name. -/

namespace Siblings

universe u

mutual
inductive FamRose (α : Type u) : Type u where
  | node : α → FamForest α → FamRose α
inductive FamForest (α : Type u) : Type u where
  | nil : FamForest α
  | cons : FamRose α → FamForest α → FamForest α
end

mutual
inductive MA (α : Type u) : Type u where
  | a : α → List (MB α) → MA α
inductive MB (α : Type u) : Type u where
  | b : MA α → MB α
  | b0 : MB α
end

mumi_spec
mutual
inductive Mu7A : Type 1 where
  | tip : Mu7A
  | mk : FamRose (FamForest Mu7A) → Mu7A
inductive Mu7B : Type 1 where
  | b : Mu7B
end

mumi_spec
mutual
inductive Nn5 : Type 1 where
  | tip : Nn5
  | mk : MA Nn5 → Nn5
inductive Nn6 : Type 1 where
  | b : Nn6
end

mumi_spec
mutual
inductive Mu6A : Type 1 where
  | tip : Mu6A
  | one : FamRose Mu6A → Mu6A
  | two : FamRose (List Mu6A) → Mu6A
inductive Mu6B : Type 1 where
  | b : Mu6B
end

end Siblings

/-! What Lean gives a nested type for recursion, which is what the tests of blocks it
rejects are measured against.  `below` and `brecOn` take every motive.  A block with a
`Prop` nesting has neither.  A definition forced through well-founded recursion costs
`propext` and `Quot.sound` whatever it is over, and its equation is still unconditional. -/

namespace ForRecursion

inductive R where
  | node : List R → R
  | leaf : R

/-- info: @R.below : {motive_1 : R → Sort u_1} → {motive_2 : List R → Sort u_1} → R → Sort (max 1 u_1) -/
#guard_msgs in
#check @R.below

/-- info: @R.below_1 : {motive_1 : R → Sort u_1} → {motive_2 : List R → Sort u_1} → List R → Sort (max 1 u_1) -/
#guard_msgs in
#check @R.below_1

mutual
def size : R → Nat
  | .node cs => 1 + sizes cs
  | .leaf => 1
termination_by t => sizeOf t
def sizes : List R → Nat
  | [] => 0
  | t :: ts => size t + sizes ts
termination_by t => sizeOf t
end

/-- info: 'Native.ForRecursion.size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms size

/-- info: size.eq_1 : ∀ (cs : List R), size (R.node cs) = 1 + sizes cs -/
#guard_msgs in
#check @size.eq_1

example (cs : List R) : size (.node cs) = 1 + sizes cs := by simp [size]

inductive PI where
  | leaf : Nat → PI
  | ghost : Nonempty PI → PI

/-- error: Unknown constant `Native.ForRecursion.PI.below` -/
#guard_msgs in
#check @PI.below

/-- error: Unknown constant `Native.ForRecursion.PI.brecOn` -/
#guard_msgs in
#check @PI.brecOn

end ForRecursion

end Native

namespace Marks
set_option mumi.mahlo false

/--
error: [rules] the rule `Marks.U.rec_base`
  ∀ {motive : U → Sort u_spec} (base : motive U.base)
    (pi : (a : U) → (b : El a → U) → motive a → ((a : El a) → motive (b a)) → motive (a.pi b)),
    U.rec base pi U.base = base
holds by `rfl`, expected only by `simp` with its lemma
---
error: [rules] `Marks.U.rec_none` is not a rule the specification states
---
error: `xfail := [cases]`, but every claim of the kind holds
-/
#guard_msgs in
mumi_spec (simp := [U.rec_base]) (unproven := [U.rec_none]) (xfail := [cases])
mutual
inductive U : Type where
  | base : U
  | pi (a : U) (b : El a → U) : U
def El : U → Type
  | .base => Nat
  | .pi a b => (x : El a) → El (b x)
end

/-- error: the block is to be rejected, and was declared -/
#guard_msgs in
mumi_spec (rejects)
inductive Fine : Type where
  | mk

-- and one that is
mumi_spec (rejects)
inductive Bad : Type where
  | mk : (Bad → Nat) → Bad

end Marks
