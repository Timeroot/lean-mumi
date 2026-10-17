import MumiTests.Spec.Harness

/-!
# Implicit arguments, as Lean's own declarations have them

Every binder annotation Lean gives a declaration is given the public
declarations of an IR block the same way: instance parameters `[BEq α]`,
strict-implicit fields `⦃Γ : Ctx⦄`, implicit fields, and implicit decoder
binders.  Inside the block a constructor application in an index term writes
only the explicit fields, as a Lean term does: the implicit ones are read off the
types of the explicit ones and off the index the application stands at.
`mumi_spec` checks every binder annotation of every public declaration, the
minor premises' included, where an implicit field stays implicit as in Lean's.
-/

set_option autoImplicit false

/-! ## Instance parameters -/

namespace Inst
set_option mumi.mahlo false

mumi_spec
mutual
inductive U (α : Type) [BEq α] : Type where
  | base : U α
  | eq (x y : α) : U α
  | pi (a : U α) (b : El α a → U α) : U α
def El (α : Type) [BEq α] : U α → Type
  | .base => α
  | .eq x y => PLift ((x == y) = true)
  | .pi a b => (x : El α a) → El α (b x)
end

def depth {α : Type} [BEq α] (t : U α) : Nat := U.rec 0 (fun _ _ => 0) (fun _ _ ih _ => ih + 1) t
example : depth (U.pi (.eq 1 2) fun _ => .base) = 1 := rfl
example (t : U Nat) : True := by induction t <;> trivial

end Inst

namespace InstLower
set_option mumi.mahlo true
set_option maxRecDepth 6000

mumi_spec
mutual
inductive U (α : Type) [BEq α] : Type where
  | base : U α
  | eq (x y : α) : U α
  | pi (a : U α) (b : El α a → U α) : U α
def El (α : Type) [BEq α] : U α → Type
  | .base => α
  | .eq x y => PLift ((x == y) = true)
  | .pi a b => (x : El α a) → El α (b x)
end

def depth {α : Type} [BEq α] (t : U α) : Nat := U.rec 0 (fun _ _ => 0) (fun _ _ ih _ => ih + 1) t
example (t : U Nat) : True := by induction t <;> trivial

end InstLower

/-! ## Implicit and strict-implicit fields, left out inside the block

`.pi A B` stands for `.pi Γ A B`, `Γ` read off the type of `A`; `.base` at an
index of type `Ty (.snoc Γ A)` stands for `.base (.snoc Γ A)`. -/

namespace Fields
set_option mumi.mahlo false

mumi_spec
mutual
inductive Ctx : Type where
  | nil : Ctx
  | snoc (Γ : Ctx) (A : Ty Γ) : Ctx
inductive Ty : Ctx → Type where
  | base {Γ : Ctx} : Ty Γ
  | pi {Γ : Ctx} (A : Ty Γ) (B : Ty (.snoc Γ A)) : Ty Γ
inductive Tm : (Γ : Ctx) → Ty Γ → Type where
  | lam {Γ : Ctx} {A : Ty Γ} {B : Ty (.snoc Γ A)} (t : Tm (.snoc Γ A) B) : Tm Γ (.pi A B)
  | app ⦃Γ : Ctx⦄ {A : Ty Γ} (f : Tm Γ (.pi A .base)) (x : Tm Γ A) : Tm Γ .base
def El : Ctx → Type
  | .nil => Unit
  | .snoc Γ A => El Γ × Val A
def Val {Γ : Ctx} : Ty Γ → Type
  | .base => Nat
  | .pi A B => (x : Val A) → Val B
end

-- a minor premise binds an implicit field implicitly, as Lean's do
def size {Γ : Ctx} {A : Ty Γ} (t : Tm Γ A) : Nat :=
  Tm.rec (motive_1 := fun _ => Unit) (motive_2 := fun _ _ => Unit) (motive_3 := fun _ _ _ => Nat)
    () (fun _ _ _ _ => ()) (fun {_} _ => ()) (fun {_} _ _ _ _ _ => ())
    (fun {_} {_} {_} _ _ _ _ ih => ih + 1) (fun ⦃_⦄ {_} _ _ _ _ ihf ihx => ihf + ihx + 1) t
example (Γ : Ctx) (A : Ty Γ) (B : Ty (.snoc Γ A)) (t : Tm (.snoc Γ A) B) : size (Tm.lam t) = size t + 1 := rfl
example (Γ : Ctx) (A : Ty Γ) (f : Tm Γ (.pi A .base)) (x : Tm Γ A) : size (Tm.app f x) = size f + size x + 1 := rfl
theorem Tm.t {Γ : Ctx} {A : Ty Γ} (t : Tm Γ A) : True := by
  induction t with
  | lam t ih => trivial
  | app f x ihf ihx => trivial

end Fields

-- at the written universe a constructor nested in another's in an index,
-- `Tm Γ (.pi A .base)`, has a decode that does not reduce; its coherence is
-- rewritten by the constructors' semantic rules instead
namespace FieldsLower
set_option mumi.mahlo true
set_option maxRecDepth 8000

mumi_spec (xfail := [axioms])
mutual
inductive Ctx : Type where
  | nil : Ctx
  | snoc (Γ : Ctx) (A : Ty Γ) : Ctx
inductive Ty : Ctx → Type where
  | base {Γ : Ctx} : Ty Γ
  | pi {Γ : Ctx} (A : Ty Γ) (B : Ty (.snoc Γ A)) : Ty Γ
inductive Tm : (Γ : Ctx) → Ty Γ → Type where
  | lam {Γ : Ctx} {A : Ty Γ} {B : Ty (.snoc Γ A)} (t : Tm (.snoc Γ A) B) : Tm Γ (.pi A B)
  | app ⦃Γ : Ctx⦄ {A : Ty Γ} (f : Tm Γ (.pi A .base)) (x : Tm Γ A) : Tm Γ .base
def El : Ctx → Type
  | .nil => Unit
  | .snoc Γ A => El Γ × Val A
def Val {Γ : Ctx} : Ty Γ → Type
  | .base => Nat
  | .pi A B => (x : Val A) → Val B
end

-- a minor premise binds an implicit field implicitly, as Lean's do
def size {Γ : Ctx} {A : Ty Γ} (t : Tm Γ A) : Nat :=
  Tm.rec (motive_1 := fun _ => Unit) (motive_2 := fun _ _ => Unit) (motive_3 := fun _ _ _ => Nat)
    () (fun _ _ _ _ => ()) (fun {_} _ => ()) (fun {_} _ _ _ _ _ => ())
    (fun {_} {_} {_} _ _ _ _ ih => ih + 1) (fun ⦃_⦄ {_} _ _ _ _ ihf ihx => ihf + ihx + 1) t
example (Γ : Ctx) (A : Ty Γ) (B : Ty (.snoc Γ A)) (t : Tm (.snoc Γ A) B) : size (Tm.lam t) = size t + 1 := rfl
example (Γ : Ctx) (A : Ty Γ) (f : Tm Γ (.pi A .base)) (x : Tm Γ A) : size (Tm.app f x) = size f + size x + 1 := rfl
theorem Tm.t {Γ : Ctx} {A : Ty Γ} (t : Tm Γ A) : True := by
  induction t with
  | lam t ih => trivial
  | app f x ihf ihx => trivial

end FieldsLower
