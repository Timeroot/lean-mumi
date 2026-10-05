import MumiTests.IRSpec.Harness

/-!
# The harness, tested

`ir_spec` passes a block whose declarations are what the specification says,
and reports, at the block, each way one is not: here a rule said to hold only
by `simp` that holds by `rfl`, and a rule the specification does not state.
-/

set_option autoImplicit false

namespace Passes
set_option mumi.mahlo false

ir_spec
mutual
inductive U : Type where
  | base : U
  | pi (a : U) (b : El a → U) : U
def El : U → Type
  | .base => Nat
  | .pi a b => (x : El a) → El (b x)
end

end Passes

namespace Fails
set_option mumi.mahlo false

/--
error: the rule `Fails.U.rec_base`
  ∀ {motive : U → Sort u_spec} (base : motive U.base)
    (pi : (a : U) → (b : El a → U) → motive a → ((a : El a) → motive (b a)) → motive (a.pi b)),
    U.rec base pi U.base = base
holds by `rfl`, expected only by `simp` with its lemma
---
error: `Fails.U.rec_none` is not a rule the specification states
-/
#guard_msgs in
ir_spec (simp := [U.rec_base]) (unproven := [U.rec_none])
mutual
inductive U : Type where
  | base : U
  | pi (a : U) (b : El a → U) : U
def El : U → Type
  | .base => Nat
  | .pi a b => (x : El a) → El (b x)
end

end Fails
