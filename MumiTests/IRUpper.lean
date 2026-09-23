import Mumi

set_option autoImplicit false
set_option mumi.mahlo false

namespace IRUpper
universe u

mutual
  inductive U (A : Type u) : Type u where
    | base : U A
    | pi (a : U A) (b : El A a → U A) : U A
  def El (A : Type u) : U A → Type u
    | .base => A
    | .pi a b => (x : El A a) → El A (b x)
end

example (A : Type u) : Type (u+1) := U A
example (A : Type u) : El A (U.base A) = A := rfl
example (A : Type u) (a : U A) (b : El A a → U A) :
    El A (U.pi A a b) = ((x : El A a) → El A (b x)) := rfl
example : El Nat (U.pi Nat (U.base Nat) (fun _ => U.base Nat)) = (Nat → Nat) := rfl

def inhabit (A : Type u) (a₀ : A) (a : U A) : El A a :=
  U.rec A a₀ (fun _ _ _ ih => fun x => ih x) a

example : inhabit Nat 7 (U.base Nat) = 7 := rfl
example : inhabit Nat 7 (U.pi Nat (U.base Nat) (fun _ => U.base Nat)) 42 = 7 := rfl

/-- info: 7 -/
#guard_msgs in
#eval inhabit Nat 7 (U.base Nat)

/-- info: 7 -/
#guard_msgs in
#eval inhabit Nat 7 (U.pi Nat (U.base Nat) (fun _ => U.base Nat)) 42

example : Type 2 := U Type
example : El Type (U.base Type) = Type := rfl
example : El (Type 3) (U.base (Type 3)) = Type 3 := rfl

def top (A : Type u) (a : U A) : Bool :=
  match U._ir_view A a with
  | .base => true
  | .pi _ _ => false

example (A : Type u) : top A (U.base A) = true := rfl
example (A : Type u) (a : U A) (b : El A a → U A) : top A (U.pi A a b) = false := rfl
example (A : Type u) (a : U A) : True := by induction a <;> trivial
example (A : Type u) (a : U A) : True := by cases a <;> trivial

end IRUpper

namespace IRPatternsUpper
mutual
  inductive Code : Type where
    | nat : Code
    | bool : Code
  def El : Code → Type
    | .nat => Nat
    | .bool => Bool
end

def isNat : Code → Bool
  | Code.nat => true
  | Code.bool => false

example : isNat Code.nat = true := rfl
end IRPatternsUpper
