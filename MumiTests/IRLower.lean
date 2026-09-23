import Mumi

set_option autoImplicit false
set_option mumi.mahlo true
set_option maxRecDepth 4000

namespace IRLower
universe u

mutual
  inductive U (A : Type u) : Type u where
    | base : U A
    | pi (a : U A) (b : El A a → U A) : U A
  def El (A : Type u) : U A → Type u
    | .base => A
    | .pi a b => (x : El A a) → El A (b x)
end

example (A : Type u) : Type u := U A
example (A : Type u) : El A (U.base A) = A := rfl
example (A : Type u) (a : U A) (b : El A a → U A) :
    El A (U.pi A a b) = ((x : El A a) → El A (b x)) := rfl

example : Type 1 := U Type
example : El Type (U.base Type) = Type := rfl
example : El (Type 3) (U.base (Type 3)) = Type 3 := rfl

-- A variable-general kernel equation does not imply uniform closed normalization.
example : El Nat (U.pi Nat (U.base Nat) (fun _ => U.base Nat)) = (Nat → Nat) := by
  fail_if_success exact rfl
  rw [El_pi, El_base]

noncomputable def inhabit (A : Type u) (a₀ : A) (a : U A) : El A a :=
  U.rec A a₀ (fun _ _ _ ih => fun x => ih x) a

example (A : Type u) (a₀ : A) : inhabit A a₀ (U.base A) = a₀ := rfl
example (A : Type u) (a₀ : A) (a : U A) (b : El A a → U A) (x : El A a) :
    inhabit A a₀ (U.pi A a b) x = inhabit A a₀ (b x) := rfl

noncomputable def top (A : Type u) (a : U A) : Bool :=
  match U._ir_view A a with
  | .base => true
  | .pi _ _ => false

example (A : Type u) : top A (U.base A) = true := rfl
example (A : Type u) (a : U A) (b : El A a → U A) : top A (U.pi A a b) = false := rfl
example (A : Type u) (a : U A) : True := by induction a <;> trivial
example (A : Type u) (a : U A) : True := by cases a <;> trivial

end IRLower
