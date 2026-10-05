import Mumi

/-!
# The baseline, at the universe written

`IRUpper.lean`'s block on the reflection axiom, where the carrier stays in the
universe it was written at.  Written out by hand, as a reader's first stop.
-/

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

/--
info: @U.rec : {A : Type u_2} →
  {motive : U A → Sort u_1} →
    motive U.base →
      ((a : U A) → (b : El A a → U A) → motive a → ((a_1 : El A a) → motive (b a_1)) → motive (a.pi b)) →
        (t : U A) → motive t
-/
#guard_msgs in
#check @U.rec

example (A : Type u) : Type u := U A
example (A : Type u) : El A .base = A := rfl
example (A : Type u) (a : U A) (b : El A a → U A) :
    El A (U.pi a b) = ((x : El A a) → El A (b x)) := rfl

example : Type 1 := U Type
example : El Type .base = Type := rfl
example : El (Type 3) .base = Type 3 := rfl

-- A variable-general kernel equation does not imply uniform closed normalization.
example : El Nat (.pi .base (fun _ => .base)) = (Nat → Nat) := by
  fail_if_success exact rfl
  rw [El_pi, El_base]

def inhabit (A : Type u) (a₀ : A) (a : U A) : El A a :=
  U.rec a₀ (fun _ _ _ ih => fun x => ih x) a

example (A : Type u) (a₀ : A) : inhabit A a₀ .base = a₀ := rfl
example (A : Type u) (a₀ : A) (a : U A) (b : El A a → U A) (x : El A a) :
    inhabit A a₀ (.pi a b) x = inhabit A a₀ (b x) := rfl

-- what is defined through the recursor runs: a value is its arguments at run time
/-- info: 7 -/
#guard_msgs in
#eval inhabit Nat 7 .base

/-- info: 7 -/
#guard_msgs in
#eval (cast (by rw [El_pi, El_base] : El Nat (.pi .base fun _ => .base) = (Nat → Nat))
  (inhabit Nat 7 (.pi .base fun _ => .base))) 42

def top (A : Type u) (a : U A) : Bool :=
  match U._ir_view A a with
  | .base => true
  | .pi _ _ => false

/-- info: false -/
#guard_msgs in
#eval top Nat (.pi .base fun _ => .base)

example (A : Type u) : top A .base = true := rfl
example (A : Type u) (a : U A) (b : El A a → U A) : top A (.pi a b) = false := rfl
example (A : Type u) (a : U A) : True := by induction a <;> trivial
example (A : Type u) (a : U A) : True := by cases a <;> trivial

end IRLower
