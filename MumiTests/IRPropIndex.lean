import Mumi

/-!
# A `Prop` member as an index domain

A carrier may be indexed by a proof of one of the block's propositions, as
`Tm : (Γ : Ctx) → Closed Γ → Ty Γ → Type`.  A proof is never data: the index is
there for the types to say, and nothing is stored for it, so `Tm Γ h A` and
`Tm Γ h' A` are the same type by `rfl`, as they are of a real inductive family.
The recursors take it like any other index.
-/

set_option autoImplicit false

namespace Simple
set_option mumi.mahlo false

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

/-- info: Simple.Tm (Γ : Ctx) (a : Closed Γ) (a_1 : Ty Γ) : Type 1 -/
#guard_msgs in
#check Tm

/-- info: Tm.app : (Γ : Ctx) → (h : Closed Γ) → (A B : Ty Γ) → Tm Γ h (Ty.arr Γ A B) → Tm Γ h A → Tm Γ h B -/
#guard_msgs in
#check @Tm.app

-- a proof is no data: the index is irrelevant
example (Γ : Ctx) (h h' : Closed Γ) (A : Ty Γ) : Tm Γ h A = Tm Γ h' A := rfl

/--
info: @Tm.rec : {motive_1 : Ctx → Sort u_1} →
  {motive_2 : (a : Ctx) → Ty a → Sort u_1} →
    {motive_3 : (Γ : Ctx) → (a : Closed Γ) → (a_1 : Ty Γ) → Tm Γ a a_1 → Sort u_1} →
      motive_1 Ctx.nil →
        ((Γ : Ctx) → (A : Ty Γ) → motive_1 Γ → motive_2 Γ A → motive_1 (Γ.snoc A)) →
          ((Γ : Ctx) → motive_1 Γ → motive_2 Γ (Ty.base Γ)) →
            ((Γ : Ctx) → (A B : Ty Γ) → motive_1 Γ → motive_2 Γ A → motive_2 Γ B → motive_2 Γ (Ty.arr Γ A B)) →
              ((Γ : Ctx) → (h : Closed Γ) → motive_1 Γ → motive_3 Γ h (Ty.base Γ) (Tm.lit Γ h)) →
                ((Γ : Ctx) →
                    (h : Closed Γ) →
                      (A B : Ty Γ) →
                        (f : Tm Γ h (Ty.arr Γ A B)) →
                          (x : Tm Γ h A) →
                            motive_1 Γ →
                              motive_2 Γ A →
                                motive_2 Γ B →
                                  motive_3 Γ h (Ty.arr Γ A B) f →
                                    motive_3 Γ h A x → motive_3 Γ h B (Tm.app Γ h A B f x)) →
                  {Γ : Ctx} → {a : Closed Γ} → {a_1 : Ty Γ} → (t : Tm Γ a a_1) → motive_3 Γ a a_1 t
-/
#guard_msgs in
#check @Tm.rec

def size {Γ : Ctx} {h : Closed Γ} {A : Ty Γ} (t : Tm Γ h A) : Nat :=
  Tm.rec (motive_1 := fun _ => Unit) (motive_2 := fun _ _ => Unit) (motive_3 := fun _ _ _ _ => Nat)
    () (fun _ _ _ _ => ()) (fun _ _ => ()) (fun _ _ _ _ _ _ => ())
    (fun _ _ _ => 1) (fun _ _ _ _ _ _ _ _ _ ihf ihx => ihf + ihx + 1) t
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

/-- info: SimpleLower.Tm (Γ : Ctx) (a : Closed Γ) (a_1 : Ty Γ) : Type -/
#guard_msgs in
#check Tm

example (Γ : Ctx) (h h' : Closed Γ) (A : Ty Γ) : Tm Γ h A = Tm Γ h' A := rfl

def size {Γ : Ctx} {h : Closed Γ} {A : Ty Γ} (t : Tm Γ h A) : Nat :=
  Tm.rec (motive_1 := fun _ => Unit) (motive_2 := fun _ _ => Unit) (motive_3 := fun _ _ _ _ => Nat)
    () (fun _ _ _ _ => ()) (fun _ _ => ()) (fun _ _ _ _ _ _ => ())
    (fun _ _ _ => 1) (fun _ _ _ _ _ _ _ _ _ ihf ihx => ihf + ihx + 1) t
example (Γ : Ctx) (h : Closed Γ) (A B : Ty Γ) (f : Tm Γ h (.arr Γ A B)) (x : Tm Γ h A) :
    size (Tm.app Γ h A B f x) = size f + size x + 1 := rfl

end SimpleLower

/-! ## The proposition tied into the block both ways

`Ok Γ` says a context is well formed, and a type is indexed by that proof;
extending a context takes a type at it. -/

namespace Tied
set_option mumi.mahlo false

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

-- the proof index is displayed as Lean displays proofs
/-- info: Ty.pi : (Γ : Ctx) → (h : Ok Γ) → (A : Ty Γ h) → Ty (Γ.snoc h A) ⋯ → Ty Γ h -/
#guard_msgs in
#check @Ty.pi

example (Γ : Ctx) (h : Ok Γ) (A : Ty Γ h) (B : Ty (.snoc Γ h A) (.snoc Γ h A)) :
    Val Γ h (.pi Γ h A B) = ((x : Val Γ h A) → Val (.snoc Γ h A) (.snoc Γ h A) B) := rfl
def depth {Γ : Ctx} {h : Ok Γ} (A : Ty Γ h) : Nat :=
  Ty.rec (motive_1 := fun _ => Unit) (motive_2 := fun _ _ _ => Nat)
    () (fun _ _ _ _ _ => ()) (fun _ _ _ => 0) (fun _ _ _ _ _ ihA ihB => max ihA ihB + 1) A
example (Γ : Ctx) (h : Ok Γ) (A : Ty Γ h) (B : Ty (.snoc Γ h A) (.snoc Γ h A)) :
    depth (.pi Γ h A B) = max (depth A) (depth B) + 1 := rfl

end Tied

namespace TiedLower
set_option mumi.mahlo true
set_option maxRecDepth 8000

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

example (Γ : Ctx) (h : Ok Γ) (A : Ty Γ h) (B : Ty (.snoc Γ h A) (.snoc Γ h A)) :
    Val Γ h (.pi Γ h A B) = ((x : Val Γ h A) → Val (.snoc Γ h A) (.snoc Γ h A) B) := Val_pi Γ h A B
def depth {Γ : Ctx} {h : Ok Γ} (A : Ty Γ h) : Nat :=
  Ty.rec (motive_1 := fun _ => Unit) (motive_2 := fun _ _ _ => Nat)
    () (fun _ _ _ _ _ => ()) (fun _ _ _ => 0) (fun _ _ _ _ _ ihA ihB => max ihA ihB + 1) A
example (Γ : Ctx) (h : Ok Γ) (A : Ty Γ h) (B : Ty (.snoc Γ h A) (.snoc Γ h A)) :
    depth (.pi Γ h A B) = max (depth A) (depth B) + 1 := rfl

end TiedLower
