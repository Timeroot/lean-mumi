import Mumi

/-!
# The baseline, one universe up

A plain test of the smallest induction-recursion, written out by hand, as a
reader's first stop: what the block declares, its recursor in the shape Lean
gives one, its equations by `rfl`, values computed and run.  The other test
files state the same of their blocks through `mumi_spec`
(`MumiTests/Spec/Harness.lean`), which checks every declaration and rule of
a block against what Lean's own rules say it should be.
-/

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

/--
info: @U.rec : {A : Type u_2} →
  {motive : U A → Sort u_1} →
    motive U.base →
      ((a : U A) → (b : El A a → U A) → motive a → ((a_1 : El A a) → motive (b a_1)) → motive (a.pi b)) →
        (t : U A) → motive t
-/
#guard_msgs in
#check @U.rec

example (A : Type u) : Type (u+1) := U A
example (A : Type u) : El A .base = A := rfl
example (A : Type u) (a : U A) (b : El A a → U A) :
    El A (U.pi a b) = ((x : El A a) → El A (b x)) := rfl
example : El Nat (.pi .base (fun _ => .base)) = (Nat → Nat) := rfl

def inhabit (A : Type u) (a₀ : A) (a : U A) : El A a :=
  U.rec a₀ (fun _ _ _ ih => fun x => ih x) a

example : inhabit Nat 7 .base = 7 := rfl
example : inhabit Nat 7 (.pi .base (fun _ => .base)) 42 = 7 := rfl

/-- info: 7 -/
#guard_msgs in
#eval inhabit Nat 7 .base

/-- info: 7 -/
#guard_msgs in
#eval inhabit Nat 7 (.pi .base (fun _ => .base)) 42

example : Type 2 := U Type
example : El Type .base = Type := rfl
example : El (Type 3) .base = Type 3 := rfl

def top (A : Type u) (a : U A) : Bool :=
  match U._ir_view A a with
  | .base => true
  | .pi _ _ => false

example (A : Type u) : top A .base = true := rfl
example (A : Type u) (a : U A) (b : El A a → U A) : top A (.pi a b) = false := rfl
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
