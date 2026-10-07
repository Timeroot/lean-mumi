import MumiTests.Spec.Harness

/-!
# The harness, tested

What Lean declares of a block it takes is the specification's ground truth, so
`mumi_spec` passes Lean's own blocks whole: an indexed mutual family, a nested
inductive, an inductive predicate that eliminates into any sort.  And it
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

mumi_spec
inductive Le : Nat → Nat → Prop where
  | refl (n : Nat) : Le n n

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
