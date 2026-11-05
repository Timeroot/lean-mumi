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
