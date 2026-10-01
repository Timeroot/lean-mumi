import Mumi

/-!
# Members in different universes

A block is declared one strongly connected component at a time, dependencies
first, so its members may sit in different universes as long as no component
mixes them -- and without a `Prop` to run the dependency through, none can: a
`Type 1` carrier cannot take a `Type 3` field, so `A` and `F` are one
component, `B` and `G`, which read them, another.  One universe up each lands
one above where it was written; at the written universe, where it was written.
-/

set_option autoImplicit false

namespace UnivUpper
set_option mumi.mahlo false

mutual
inductive A : Type 1 where
  | a0 : A
  | a1 (x : A) (f : F x → A) : A
inductive B : Type 3 where
  | b0 : B
  | b1 (x : A) (v : F x) (b : B) (g : G b → B) : B
def F : A → Type 1
  | .a0 => Type
  | .a1 x f => (y : F x) → F (f y)
def G : B → Type 3
  | .b0 => Type 2
  | .b1 x v b g => F x × ((z : G b) → G (g z))
end

example : Type 2 := A
example : Type 4 := B
example (x : A) (f : F x → A) : F (A.a1 x f) = ((y : F x) → F (f y)) := rfl
example (x : A) (v : F x) (b : B) (g : G b → B) : G (B.b1 x v b g) = (F x × ((z : G b) → G (g z))) := rfl
example : F (A.a1 A.a0 (fun _ => A.a0)) = (Type → Type) := rfl
example : G (B.b1 A.a0 Nat B.b0 (fun _ => B.b0)) = (Type × (Type 2 → Type 2)) := rfl

/-- `B` recurses on its `A` through `A`'s own recursor: each is Lean's. -/
def sizeA : A → Nat := A.rec 0 (fun _ _ ih _ => ih + 1)
def sizeB : B → Nat := B.rec 0 (fun x _ _ _ ih _ => sizeA x + ih + 1)

example : sizeB (B.b1 (A.a1 A.a0 fun _ => A.a0) (fun x => x) B.b0 fun _ => B.b0) = 2 := rfl

/-- info: 2 -/
#guard_msgs in
#eval sizeB (B.b1 (A.a1 A.a0 fun _ => A.a0) (fun x => x) B.b0 fun _ => B.b0)

/-- info: 'UnivUpper.sizeB' does not depend on any axioms -/
#guard_msgs in
#print axioms sizeB

end UnivUpper

namespace UnivLower
set_option mumi.mahlo true

mutual
inductive A : Type 1 where
  | a0 : A
  | a1 (x : A) (f : F x → A) : A
inductive B : Type 3 where
  | b0 : B
  | b1 (x : A) (v : F x) (b : B) (g : G b → B) : B
def F : A → Type 1
  | .a0 => Type
  | .a1 x f => (y : F x) → F (f y)
def G : B → Type 3
  | .b0 => Type 2
  | .b1 x v b g => F x × ((z : G b) → G (g z))
end

example : Type 1 := A
example : Type 3 := B
example (x : A) (f : F x → A) : F (A.a1 x f) = ((y : F x) → F (f y)) := rfl
example (x : A) (v : F x) (b : B) (g : G b → B) : G (B.b1 x v b g) = (F x × ((z : G b) → G (g z))) := rfl

def sizeA : A → Nat := A.rec 0 (fun _ _ ih _ => ih + 1)
def sizeB : B → Nat := B.rec 0 (fun x _ _ _ ih _ => sizeA x + ih + 1)

-- a closed `F`/`G` does not normalise here; the values are given through the equations
def v0 : F A.a0 := cast F_a0.symm Nat
/-- info: 2 -/
#guard_msgs in
#eval sizeB (B.b1 (A.a1 A.a0 fun _ => A.a0) (cast (F_a1 A.a0 fun _ => A.a0).symm fun _ => v0) B.b0 fun _ => B.b0)

/-- info: 'UnivLower.sizeB' depends on axioms: [IR.mahlo] -/
#guard_msgs in
#print axioms sizeB

end UnivLower

/-! Components in one universe stay one block, with one joint recursion, as a
`mutual` has; a component of definitions alone is Lean's. -/

namespace Split

mutual
inductive U : Type where
  | base : U
  | pi (a : U) (b : El a → U) : U
def El : U → Type
  | .base => Nat
  | .pi a b => (x : El a) → El (b x)
inductive Code : Type where
  | nat : Code
  | pair (c : Code) (f : Nat → Code) : Code
def Val : Code → Type
  | .nat => Nat
  | .pair c f => Val c × ((n : Nat) → Val (f n))
def twice (n : Nat) : Nat := thrice n + n
def thrice (n : Nat) : Nat := n + n + n
end

example (c : Code) (f : Nat → Code) : Val (Code.pair c f) = (Val c × ((n : Nat) → Val (f n))) := rfl
example : twice 1 = 4 := rfl
-- one block: `U.rec` takes a motive for `Code` as well
example : U → Nat := U.rec (motive_2 := fun _ => Unit) 0 (fun _ _ ih _ => ih + 1) () (fun _ _ _ _ => ())

end Split
