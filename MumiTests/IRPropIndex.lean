import MumiTests.Spec.Harness

/-!
# A `Prop` member as an index domain

A carrier may be indexed by a proof of one of the block's propositions, as
`Tm : (Γ : Ctx) → Closed Γ → Ty Γ → Type`.  A proof is never data: the index is
there for the types to say, and nothing is stored for it, so `Tm Γ h A` and
`Tm Γ h' A` are the same type by `rfl`, as they are of a real inductive family.
The recursors take it like any other index.  `mumi_spec` checks each block's
declarations and rules; what follows is what that leaves out.
-/

set_option autoImplicit false

namespace Simple
set_option mumi.mahlo false

mumi_spec
mutual
inductive Ctx : Type where
  | nil : Ctx
  | snoc (Γ : Ctx) (A : Ty Γ) : Ctx
inductive Ty : Ctx → Type where
  | base (Γ : Ctx) : Ty Γ
  | arr (Γ : Ctx) (A B : Ty Γ) : Ty Γ
inductive Closed : Ctx → Prop where
  | nil : Closed .nil
  | snoc (Γ : Ctx) (A : Ty Γ) (h : Closed Γ) : Closed (.snoc Γ A)
inductive Tm : (Γ : Ctx) → Closed Γ → Ty Γ → Type where
  | lit (Γ : Ctx) (h : Closed Γ) : Tm Γ h (.base Γ)
  | app (Γ : Ctx) (h : Closed Γ) (A B : Ty Γ) (f : Tm Γ h (.arr Γ A B)) (x : Tm Γ h A) : Tm Γ h B
def El : Ctx → Type
  | .nil => Unit
  | .snoc Γ A => El Γ × Val Γ A
def Val : (Γ : Ctx) → Ty Γ → Type
  | _, .base Γ => Nat
  | _, .arr Γ A B => Val Γ A → Val Γ B
end

-- a proof is no data: the index is irrelevant
example (Γ : Ctx) (h h' : Closed Γ) (A : Ty Γ) : Tm Γ h A = Tm Γ h' A := rfl

-- the block's recursion: a hypothesis at every field, the proof `h` too, and
-- `Closed`'s motive displayed, taking the value at its context
def size {Γ : Ctx} {h : Closed Γ} {A : Ty Γ} (t : Tm Γ h A) : Nat :=
  Tm.rec (motive_1 := fun _ => Unit) (motive_2 := fun _ _ => Unit) (motive_3 := fun _ _ _ => True)
    (motive_4 := fun _ _ _ _ => Nat)
    () (fun _ _ _ _ => ()) (fun _ _ => ()) (fun _ _ _ _ _ _ => ())
    trivial (fun _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ => 1) (fun _ _ _ _ _ _ _ _ _ _ ihf ihx => ihf + ihx + 1) t
example (Γ : Ctx) (h : Closed Γ) : size (Tm.lit Γ h) = 1 := rfl
example (Γ : Ctx) (h : Closed Γ) (A B : Ty Γ) (f : Tm Γ h (.arr Γ A B)) (x : Tm Γ h A) :
    size (Tm.app Γ h A B f x) = size f + size x + 1 := rfl
theorem Tm.t {Γ : Ctx} {h : Closed Γ} {A : Ty Γ} (t : Tm Γ h A) : True := by
  induction t with
  | lit => trivial
  | app Γ h A B f x ihf ihx => trivial

end Simple

namespace SimpleLower
set_option mumi.mahlo true
set_option maxRecDepth 8000

mumi_spec (xfail := [discr])
mutual
inductive Ctx : Type where
  | nil : Ctx
  | snoc (Γ : Ctx) (A : Ty Γ) : Ctx
inductive Ty : Ctx → Type where
  | base (Γ : Ctx) : Ty Γ
  | arr (Γ : Ctx) (A B : Ty Γ) : Ty Γ
inductive Closed : Ctx → Prop where
  | nil : Closed .nil
  | snoc (Γ : Ctx) (A : Ty Γ) (h : Closed Γ) : Closed (.snoc Γ A)
inductive Tm : (Γ : Ctx) → Closed Γ → Ty Γ → Type where
  | lit (Γ : Ctx) (h : Closed Γ) : Tm Γ h (.base Γ)
  | app (Γ : Ctx) (h : Closed Γ) (A B : Ty Γ) (f : Tm Γ h (.arr Γ A B)) (x : Tm Γ h A) : Tm Γ h B
def El : Ctx → Type
  | .nil => Unit
  | .snoc Γ A => El Γ × Val Γ A
def Val : (Γ : Ctx) → Ty Γ → Type
  | _, .base Γ => Nat
  | _, .arr Γ A B => Val Γ A → Val Γ B
end

example (Γ : Ctx) (h h' : Closed Γ) (A : Ty Γ) : Tm Γ h A = Tm Γ h' A := rfl

-- the block's recursion: a hypothesis at every field, the proof `h` too, and
-- `Closed`'s motive displayed, taking the value at its context
def size {Γ : Ctx} {h : Closed Γ} {A : Ty Γ} (t : Tm Γ h A) : Nat :=
  Tm.rec (motive_1 := fun _ => Unit) (motive_2 := fun _ _ => Unit) (motive_3 := fun _ _ _ => True)
    (motive_4 := fun _ _ _ _ => Nat)
    () (fun _ _ _ _ => ()) (fun _ _ => ()) (fun _ _ _ _ _ _ => ())
    trivial (fun _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ => 1) (fun _ _ _ _ _ _ _ _ _ _ ihf ihx => ihf + ihx + 1) t
example (Γ : Ctx) (h : Closed Γ) (A B : Ty Γ) (f : Tm Γ h (.arr Γ A B)) (x : Tm Γ h A) :
    size (Tm.app Γ h A B f x) = size f + size x + 1 := rfl

end SimpleLower

/-! ## The proposition tied into the block both ways

`Ok Γ` says a context is well formed, and a type is indexed by that proof;
extending a context takes a type at it. -/

namespace Tied
set_option mumi.mahlo false

mumi_spec
mutual
inductive Ctx : Type where
  | nil : Ctx
  | snoc (Γ : Ctx) (h : Ok Γ) (A : Ty Γ h) : Ctx
inductive Ok : Ctx → Prop where
  | nil : Ok .nil
  | snoc (Γ : Ctx) (h : Ok Γ) (A : Ty Γ h) : Ok (.snoc Γ h A)
inductive Ty : (Γ : Ctx) → Ok Γ → Type where
  | base (Γ : Ctx) (h : Ok Γ) : Ty Γ h
  | pi (Γ : Ctx) (h : Ok Γ) (A : Ty Γ h) (B : Ty (.snoc Γ h A) (.snoc Γ h A)) : Ty Γ h
def El : Ctx → Type
  | .nil => Unit
  | .snoc Γ h A => El Γ × Val Γ h A
def Val : (Γ : Ctx) → (h : Ok Γ) → Ty Γ h → Type
  | _, _, .base Γ h => Nat
  | _, _, .pi Γ h A B => (x : Val Γ h A) → Val (.snoc Γ h A) (.snoc Γ h A) B
end

def depth {Γ : Ctx} {h : Ok Γ} (A : Ty Γ h) : Nat :=
  Ty.rec (motive_1 := fun _ => Unit) (motive_2 := fun _ _ _ => True) (motive_3 := fun _ _ _ => Nat)
    () (fun _ _ _ _ _ _ => ()) trivial (fun _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ => 0) (fun _ _ _ _ _ _ ihA ihB => max ihA ihB + 1) A
example (Γ : Ctx) (h : Ok Γ) (A : Ty Γ h) (B : Ty (.snoc Γ h A) (.snoc Γ h A)) :
    depth (.pi Γ h A B) = max (depth A) (depth B) + 1 := rfl

end Tied

namespace TiedLower
set_option mumi.mahlo true
set_option maxRecDepth 8000

mumi_spec (xfail := [discr])
mutual
inductive Ctx : Type where
  | nil : Ctx
  | snoc (Γ : Ctx) (h : Ok Γ) (A : Ty Γ h) : Ctx
inductive Ok : Ctx → Prop where
  | nil : Ok .nil
  | snoc (Γ : Ctx) (h : Ok Γ) (A : Ty Γ h) : Ok (.snoc Γ h A)
inductive Ty : (Γ : Ctx) → Ok Γ → Type where
  | base (Γ : Ctx) (h : Ok Γ) : Ty Γ h
  | pi (Γ : Ctx) (h : Ok Γ) (A : Ty Γ h) (B : Ty (.snoc Γ h A) (.snoc Γ h A)) : Ty Γ h
def El : Ctx → Type
  | .nil => Unit
  | .snoc Γ h A => El Γ × Val Γ h A
def Val : (Γ : Ctx) → (h : Ok Γ) → Ty Γ h → Type
  | _, _, .base Γ h => Nat
  | _, _, .pi Γ h A B => (x : Val Γ h A) → Val (.snoc Γ h A) (.snoc Γ h A) B
end

def depth {Γ : Ctx} {h : Ok Γ} (A : Ty Γ h) : Nat :=
  Ty.rec (motive_1 := fun _ => Unit) (motive_2 := fun _ _ _ => True) (motive_3 := fun _ _ _ => Nat)
    () (fun _ _ _ _ _ _ => ()) trivial (fun _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ => 0) (fun _ _ _ _ _ _ ihA ihB => max ihA ihB + 1) A
example (Γ : Ctx) (h : Ok Γ) (A : Ty Γ h) (B : Ty (.snoc Γ h A) (.snoc Γ h A)) :
    depth (.pi Γ h A B) = max (depth A) (depth B) + 1 := rfl

end TiedLower
