import Mumi

/-!
# Notations and implicit binders

What a clause says is passed through as the term it is: `∃`, `Σ`, `×`, `×'`,
subtypes, `fun x ↦`, typed or not.  A binder of a field written without a
type is left to inference; a field is still a carrier, a function into one,
a proof of a `Prop` member under binders, or a plain type, so `∃ x, Good (b x)`
is a clause's to say, not a field's.  A constructor field written `{x : T}` is
implicit in the public constructor and bound explicitly in the minor
premises, as Lean's own are; an index of a decoder written `{Γ : Ctx}` is
implicit in the public decoder, and the clauses write the explicit ones
only.  Inside the block a constructor application in an index term lists
every field, the implicit ones included, since the reader resolves it itself.
-/

set_option autoImplicit false

namespace Notations
set_option mumi.mahlo false

mutual
inductive U : Type where
  | base : U
  | pi (a : U) (b : El a → U) (h : Good a) : U
  | sig (a : U) (b : El a → U) : U
inductive Good : U → Prop where
  | base : Good .base
  | pi (a : U) (b : El a → U) (h : Good a) (hb : ∀ x, Good (b x)) : Good (.pi a b h)
  | sig (a : U) (b : El a → U) (ha : Good a) (hb : ∀ x, Good (b x)) : Good (.sig a b)
def El : U → Type
  | .base => Nat
  | .pi a b h => (x : El a) → El (b x)
  | .sig a b => Σ x : El a, El (b x)
def Inh : U → Prop
  | .base => True
  | .pi a b h => ∀ x, Inh (b x)
  | .sig a b => ∃ x, Inh (b x)
def Pair : U → Type
  | .base => Nat × Nat
  | .pi a b h => {f : (x : El a) → Pair (b x) // True}
  | .sig a b => (x : El a) ×' Pair (b x)
def Fn : U → Nat → Nat
  | .base => fun n ↦ n
  | .pi a b h => fun n ↦ n + 1
  | .sig a b => λ n => n + 2
end

example (a : U) (b : El a → U) : Inh (U.sig a b) = ∃ x, Inh (b x) := rfl
example (a : U) (b : El a → U) : El (U.sig a b) = Σ x : El a, El (b x) := rfl
example (a : U) (b : El a → U) (h : Good a) : Fn (U.pi a b h) 3 = 4 := rfl
theorem Good.t (u : U) (g : Good u) : True := by
  induction g with
  | base => trivial
  | pi a b h hb ih ihb => trivial
  | sig a b ha hb ih => trivial

end Notations

namespace NotationsLower
set_option mumi.mahlo true
set_option maxRecDepth 6000

mutual
inductive U : Type where
  | base : U
  | pi (a : U) (b : El a → U) (h : Good a) : U
  | sig (a : U) (b : El a → U) : U
inductive Good : U → Prop where
  | base : Good .base
  | pi (a : U) (b : El a → U) (h : Good a) (hb : ∀ x, Good (b x)) : Good (.pi a b h)
  | sig (a : U) (b : El a → U) (ha : Good a) (hb : ∀ x, Good (b x)) : Good (.sig a b)
def El : U → Type
  | .base => Nat
  | .pi a b h => (x : El a) → El (b x)
  | .sig a b => Σ x : El a, El (b x)
def Inh : U → Prop
  | .base => True
  | .pi a b h => ∀ x, Inh (b x)
  | .sig a b => ∃ x, Inh (b x)
def Fn : U → Nat → Nat
  | .base => fun n ↦ n
  | .pi a b h => fun n ↦ n + 1
  | .sig a b => λ n => n + 2
end

example (a : U) (b : El a → U) : Inh (U.sig a b) = ∃ x, Inh (b x) := rfl
example (a : U) (b : El a → U) (h : Good a) : Fn (U.pi a b h) 3 = 4 := rfl
theorem Good.t (u : U) (g : Good u) : True := by
  induction g with
  | base => trivial
  | pi a b h hb ih ihb => trivial
  | sig a b ha hb ih => trivial

end NotationsLower

namespace Implicit
set_option mumi.mahlo false

mutual
inductive Ctx : Type where
  | nil : Ctx
  | snoc (Γ : Ctx) (A : Ty Γ) : Ctx
inductive Ty : Ctx → Type where
  | base {Γ : Ctx} : Ty Γ
  | pi {Γ : Ctx} (A : Ty Γ) (B : Ty (.snoc Γ A)) : Ty Γ
def El : Ctx → Type
  | .nil => Unit
  | .snoc Γ A => El Γ × Val A
def Val {Γ : Ctx} : Ty Γ → Type
  | .base => Nat
  | .pi A B => (x : Val A) → Val B
end

/-- info: @Implicit.Ty.pi : {Γ : Ctx} → (A : Ty Γ) → Ty (Γ.snoc A) → Ty Γ -/
#guard_msgs in
#check @Ty.pi

/-- info: Implicit.Val {Γ : Ctx} : Ty Γ → Type -/
#guard_msgs in
#check Val

example (Γ : Ctx) (A : Ty Γ) : Val (Ty.pi A Ty.base) = ((x : Val A) → Nat) := rfl
example (Γ : Ctx) (A : Ty Γ) (B : Ty (Ctx.snoc Γ A)) : Val (Ty.pi A B) = ((x : Val A) → Val B) := Val_pi Γ A B
/-- The minor premises bind every field, as Lean's own recursors do. -/
def tsize : (Γ : Ctx) → Ty Γ → Nat :=
  Ty.rec (motive := fun _ => Nat) (motive_2 := fun _ _ => Nat) 0 (fun _ _ ih _ => ih + 1) (fun _ _ => 0) (fun _ _ _ _ ihA ihB => ihA + ihB + 1)
example (Γ : Ctx) (A : Ty Γ) (B : Ty (Ctx.snoc Γ A)) : tsize Γ (Ty.pi A B) = tsize Γ A + tsize _ B + 1 := rfl
theorem Ty.t (Γ : Ctx) (A : Ty Γ) : True := by
  induction A with
  | base => trivial
  | pi A B ihA ihB => trivial

end Implicit

namespace ImplicitLower
set_option mumi.mahlo true
set_option maxRecDepth 6000

mutual
inductive Ctx : Type where
  | nil : Ctx
  | snoc (Γ : Ctx) (A : Ty Γ) : Ctx
inductive Ty : Ctx → Type where
  | base {Γ : Ctx} : Ty Γ
  | pi {Γ : Ctx} (A : Ty Γ) (B : Ty (.snoc Γ A)) : Ty Γ
def El : Ctx → Type
  | .nil => Unit
  | .snoc Γ A => El Γ × Val A
def Val {Γ : Ctx} : Ty Γ → Type
  | .base => Nat
  | .pi A B => (x : Val A) → Val B
end

/-- info: @ImplicitLower.Ty.pi : {Γ : Ctx} → (A : Ty Γ) → Ty (Γ.snoc A) → Ty Γ -/
#guard_msgs in
#check @Ty.pi

example (Γ : Ctx) (A : Ty Γ) (B : Ty (Ctx.snoc Γ A)) : Val (Ty.pi A B) = ((x : Val A) → Val B) := Val_pi Γ A B
def tsize : (Γ : Ctx) → Ty Γ → Nat :=
  Ty.rec (motive := fun _ => Nat) (motive_2 := fun _ _ => Nat) 0 (fun _ _ ih _ => ih + 1) (fun _ _ => 0) (fun _ _ _ _ ihA ihB => ihA + ihB + 1)
example (Γ : Ctx) (A : Ty Γ) (B : Ty (Ctx.snoc Γ A)) : tsize Γ (Ty.pi A B) = tsize Γ A + tsize _ B + 1 := rfl
theorem Ty.t (Γ : Ctx) (A : Ty Γ) : True := by
  induction A with
  | base => trivial
  | pi A B ihA ihB => trivial

end ImplicitLower

/-! Shared parameters are explicit, and say so. -/

/-- error: IR prototype takes shared parameters explicit; write `(x : T)` -/
#guard_msgs in
mutual
inductive U {α : Type} : Type where
  | base : U
  | pi (a : U) (b : El a → U) : U
def El {α : Type} : U (α := α) → Type
  | .base => α
  | .pi a b => (x : El a) → El (b x)
end
