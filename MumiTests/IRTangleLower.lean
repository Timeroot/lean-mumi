import MumiTests.IRSpec.Harness

/-!
# One strongly connected block of everything

`A` holds a `B` and a `D`; `F` is a type computed from an `A`, and reads `D` at
the `B` inside; `B` is indexed by an `A` and by `F` of it; `D` is a type computed
from a `B`, and reads `F` and itself; `E` is indexed by all of `A`, `F` and `B`,
and `G` counts through it.  Nothing here means anything.  The point is that one
block lowers, every carrier gets its recursor, every decoder its equations, and
all of it is `rfl`. `ir_spec` checks every declaration
and equation; what follows is what that leaves out.
-/

set_option autoImplicit false
set_option mumi.mahlo true

namespace TangleL

ir_spec
mutual
inductive A : Type where
  | nil : A
  | cons (x : A) (c : F x) (b : B x c) (d : D x c b) : A
inductive B : (x : A) → F x → Type where
  | leaf (x : A) (c : F x) : B x c
  | node (x : A) (c : F x) (b : B x c) (e : D x c b)
      (f : (y : D x c b) → B (A.cons x c b y) (c, y)) : B x c
inductive E : (x : A) → (c : F x) → B x c → Type where
  | mk (x : A) (c : F x) (b : B x c) (d : D x c b) : E x c b
  | up (x : A) (c : F x) (b : B x c) (e : E x c b) (d : D x c b) :
      E (A.cons x c b d) (c, d) (B.leaf (A.cons x c b d) (c, d))
def F : A → Type
  | .nil => PUnit
  | .cons x c b d => F x × D x c b
def D : (x : A) → (c : F x) → B x c → Type
  | _, _, .leaf x c => F x
  | _, _, .node x c b e f => (y : D x c b) → D (A.cons x c b y) (c, y) (f y)
def G : (x : A) → (c : F x) → (b : B x c) → E x c b → Nat
  | _, _, _, .mk x c b d => 0
  | _, _, _, .up x c b e d => G x c b e + 1
end

/-! ## Through the recursors -/

/-- The number of `cons`es in an `A`, counting through the `B` it holds. -/
def size : A → Nat :=
  A.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ _ => Nat) (motive_3 := fun _ _ _ _ => Unit)
    0 (fun _ _ _ _ ihx ihb => ihx + ihb + 1)
    (fun _ _ ihx => ihx) (fun _ _ _ _ _ ihx ihb _ => ihx + ihb)
    (fun _ _ _ _ _ _ => ()) (fun _ _ _ _ _ _ _ _ => ())

/-- info: 'TangleL.size' depends on axioms: [IR.mahlo] -/
#guard_msgs in
#print axioms size

/-- A closed term through every carrier.  A closed term does not normalise
here, so a field at a decoder of one is stated through the equations. -/
def d0 : D A.nil PUnit.unit (B.leaf A.nil PUnit.unit) := cast (D_leaf A.nil PUnit.unit).symm PUnit.unit
def a1 : A := A.cons A.nil PUnit.unit (B.leaf A.nil PUnit.unit) d0
def c1 : F a1 := cast (F_cons A.nil PUnit.unit (B.leaf A.nil PUnit.unit) d0).symm (PUnit.unit, d0)

/-- info: 1 -/
#guard_msgs in
#eval size a1

/-- info: 3 -/
#guard_msgs in
#eval size (A.cons a1 c1 (B.leaf a1 c1) (cast (D_leaf a1 c1).symm c1))

example (x : A) (c : F x) (b : B x c) (e : E x c b) : True := by
  induction e with
  | mk _ _ _ _ => trivial
  | up _ _ _ _ _ ih => trivial

example (x : A) (c : F x) (b : B x c) : True := by cases b <;> trivial

end TangleL

/-! ## A decoder whose result is a value of an earlier decoder

`dflt` lands in `El Γ A`, which `El` computed a line earlier. -/

namespace DependentL

ir_spec
mutual
inductive Ctx : Type where
  | nil : Ctx
  | ext (Γ : Ctx) (A : Ty Γ) : Ctx
inductive Ty : (Γ : Ctx) → Type where
  | nat (Γ : Ctx) : Ty Γ
  | arr (Γ : Ctx) (A B : Ty Γ) : Ty Γ
def El : (Γ : Ctx) → Ty Γ → Type
  | _, .nat Γ => Nat
  | _, .arr Γ A B => El Γ A → El Γ B
def dflt : (Γ : Ctx) → (A : Ty Γ) → El Γ A
  | _, .nat Γ => 0
  | _, .arr Γ A B => fun _ => dflt Γ B
end

end DependentL
