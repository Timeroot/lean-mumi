import Mumi

/-!
# One strongly connected block of everything

`A` holds a `B` and a `D`; `F` is a type computed from an `A`, and reads `D` at
the `B` inside; `B` is indexed by an `A` and by `F` of it; `D` is a type computed
from a `B`, and reads `F` and itself; `E` is indexed by all of `A`, `F` and `B`,
and `G` counts through it.  Nothing here means anything.  The point is that one
block lowers, every carrier gets its recursor, every decoder its equations, and
all of it is `rfl`.
-/

set_option autoImplicit false
set_option mumi.mahlo false

namespace Tangle

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

/-! ## The decoders compute -/

example : F A.nil = PUnit := rfl
example (x : A) (c : F x) (b : B x c) (d : D x c b) : F (A.cons x c b d) = (F x × D x c b) := rfl
example (x : A) (c : F x) : D x c (B.leaf x c) = F x := rfl
example (x : A) (c : F x) (b : B x c) (e : D x c b) (f : (y : D x c b) → B (A.cons x c b y) (c, y)) :
    D x c (B.node x c b e f) = ((y : D x c b) → D (A.cons x c b y) (c, y) (f y)) := rfl
example (x : A) (c : F x) (b : B x c) (e : E x c b) (d : D x c b) :
    G _ _ _ (E.up x c b e d) = G x c b e + 1 := rfl

/-- A closed term through every carrier. -/
def a1 : A := A.cons A.nil PUnit.unit (B.leaf A.nil PUnit.unit) PUnit.unit
example : F a1 = (PUnit × PUnit) := rfl
example : G _ _ _ (E.up A.nil PUnit.unit (B.leaf _ _) (E.mk _ _ _ PUnit.unit) PUnit.unit) = 1 := rfl

/-! ## The recursors -/

/--
info: @E.rec : {motive : A → Sort u_1} →
  {motive_2 : (x : A) → (_ir_arg1 : F x) → B x _ir_arg1 → Sort u_1} →
    {motive_3 : (x : A) → (c : F x) → (_ir_arg2 : B x c) → E x c _ir_arg2 → Sort u_1} →
      motive A.nil →
        ((x : A) → (c : F x) → (b : B x c) → (d : D x c b) → motive x → motive_2 x c b → motive (x.cons c b d)) →
          ((x : A) → (c : F x) → motive x → motive_2 x c (B.leaf x c)) →
            ((x : A) →
                (c : F x) →
                  (b : B x c) →
                    (e : D x c b) →
                      (f : (y : D x c b) → B (x.cons c b y) (c, y)) →
                        motive x →
                          motive_2 x c b →
                            ((_ir_index_f_0 : D x c b) →
                                motive_2 (x.cons c b _ir_index_f_0) (c, _ir_index_f_0) (f _ir_index_f_0)) →
                              motive_2 x c (B.node x c b e f)) →
              ((x : A) →
                  (c : F x) → (b : B x c) → (d : D x c b) → motive x → motive_2 x c b → motive_3 x c b (E.mk x c b d)) →
                ((x : A) →
                    (c : F x) →
                      (b : B x c) →
                        (e : E x c b) →
                          (d : D x c b) →
                            motive x →
                              motive_2 x c b →
                                motive_3 x c b e →
                                  motive_3 (x.cons c b d) (c, d) (B.leaf (x.cons c b d) (c, d)) (E.up x c b e d)) →
                  {x : A} →
                    {c : F x} → {_ir_arg2 : B x c} → (_ir_self : E x c _ir_arg2) → motive_3 x c _ir_arg2 _ir_self
-/
#guard_msgs in
#check @E.rec

/-- The number of `cons`es in an `A`, counting through the `B` it holds. -/
def size : A → Nat :=
  A.rec (motive := fun _ => Nat) (motive_2 := fun _ _ _ => Nat) (motive_3 := fun _ _ _ _ => Unit)
    0 (fun _ _ _ _ ihx ihb => ihx + ihb + 1)
    (fun _ _ ihx => ihx) (fun _ _ _ _ _ ihx ihb _ => ihx + ihb)
    (fun _ _ _ _ _ _ => ()) (fun _ _ _ _ _ _ _ _ => ())

example : size a1 = 1 := rfl
example : size (A.cons a1 (PUnit.unit, PUnit.unit) (B.leaf a1 _) (PUnit.unit, PUnit.unit)) = 3 := rfl

/-- info: 'Tangle.size' does not depend on any axioms -/
#guard_msgs in
#print axioms size

example (x : A) (c : F x) (b : B x c) (e : E x c b) : True := by
  induction e with
  | mk _ _ _ _ => trivial
  | up _ _ _ _ _ ih => trivial

example (x : A) (c : F x) (b : B x c) : True := by cases b <;> trivial

end Tangle

/-! ## A decoder whose result is a value of an earlier decoder

`dflt` lands in `El Γ A`, which `El` computed a line earlier. -/

namespace Dependent

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

example (Γ : Ctx) (A B : Ty Γ) : dflt Γ (Ty.arr Γ A B) = fun _ => dflt Γ B := rfl
example : dflt Ctx.nil (Ty.arr _ (Ty.nat _) (Ty.nat _)) 5 = 0 := rfl

end Dependent
