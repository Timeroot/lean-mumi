import MumiTests.Spec.Harness

/-!
# Notations and implicit binders

What a clause says is passed through as the term it is: `∃`, `Σ`, `×`, `×'`,
subtypes, `fun x ↦`, typed or not.  A binder of a field written without a
type is left to inference; a field is still a carrier, a function into one,
a proof of a `Prop` member under binders, or a plain type, so `∃ x, Good (b x)`
is a clause's to say, not a field's.  A constructor field written `{x : T}` is
implicit in the public constructor and in the minor premises, as Lean's own
are; an index of a decoder written `{Γ : Ctx}` is implicit in the public
decoder, and the clauses write the explicit ones only.  `mumi_spec` checks the
declarations and equations of each block; what follows is what that leaves out.
-/

set_option autoImplicit false

namespace Notations
set_option mumi.mahlo false

mumi_spec
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

theorem Good.t (u : U) (g : Good u) : True := by
  cases g with
  | base => trivial
  | pi a b h hb => trivial
  | sig a b ha hb => trivial

end Notations

namespace NotationsLower
set_option mumi.mahlo true
set_option maxRecDepth 6000

mumi_spec (xfail := [discr])
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

theorem Good.t (u : U) (g : Good u) : True := by
  cases g with
  | base => trivial
  | pi a b h hb => trivial
  | sig a b ha hb => trivial

end NotationsLower

namespace Implicit
set_option mumi.mahlo false

mumi_spec
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

/-- The minor premises bind every field, an implicit one implicitly, as Lean's
own recursors do. -/
def tsize (Γ : Ctx) (A : Ty Γ) : Nat :=
  Ty.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat) 0 (fun _ _ ih _ => ih + 1) (fun _ => 0) (fun _ _ _ ihA ihB => ihA + ihB + 1) A
example (Γ : Ctx) (A : Ty Γ) (B : Ty (Ctx.snoc Γ A)) : tsize Γ (Ty.pi A B) = tsize Γ A + tsize _ B + 1 := rfl
theorem Ty.t (Γ : Ctx) (A : Ty Γ) : True := by
  induction A with
  | base => trivial
  | pi A B ihA ihB => trivial

end Implicit

namespace ImplicitLower
set_option mumi.mahlo true
set_option maxRecDepth 6000

mumi_spec (xfail := [discr])
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

def tsize (Γ : Ctx) (A : Ty Γ) : Nat :=
  Ty.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat) 0 (fun _ _ ih _ => ih + 1) (fun _ => 0) (fun _ _ _ ihA ihB => ihA + ihB + 1) A
example (Γ : Ctx) (A : Ty Γ) (B : Ty (Ctx.snoc Γ A)) : tsize Γ (Ty.pi A B) = tsize Γ A + tsize _ B + 1 := rfl
theorem Ty.t (Γ : Ctx) (A : Ty Γ) : True := by
  induction A with
  | base => trivial
  | pi A B ihA ihB => trivial

end ImplicitLower

/-! Shared parameters follow Lean's convention: the carriers take them
explicitly, their constructors and eliminators implicitly, and a decoder as its
author binds them.  Inside the block a constructor is written without them, and
a decoder call writes the ones its declaration binds explicitly. -/

namespace Params
set_option mumi.mahlo false

mumi_spec
mutual
inductive Ctx (X : Type) : Type where
  | nil : Ctx X
  | snoc (Γ : Ctx X) (A : Ty X Γ) : Ctx X
inductive Ty (X : Type) : Ctx X → Type where
  | base {Γ : Ctx X} (x : X) : Ty X Γ
  | pi {Γ : Ctx X} (A : Ty X Γ) (B : Ty X (Ctx.snoc Γ A)) : Ty X Γ
def El {X : Type} : Ctx X → Type
  | .nil => Unit
  | .snoc Γ A => El Γ × Val X A
def Val (X : Type) {Γ : Ctx X} : Ty X Γ → Type
  | .base x => X
  | .pi A B => (x : Val X A) → Val X B
end

example (A : Ty Nat .nil) : El (.snoc .nil A) = (Unit × Val Nat A) := rfl
example : Val Nat (Ty.pi (Γ := .nil) (.base 0) (.base 1)) = (Nat → Nat) := rfl
def tsize {X : Type} (Γ : Ctx X) (A : Ty X Γ) : Nat :=
  Ty.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat) 0 (fun _ _ ih _ => ih + 1) (fun _ _ => 0) (fun _ _ _ ihA ihB => ihA + ihB + 1) A
example : tsize .nil (Ty.pi (X := Nat) (.base 0) (.base 1)) = 1 := rfl
theorem Ty.t (X : Type) (Γ : Ctx X) (A : Ty X Γ) : True := by
  induction A with
  | base => trivial
  | pi A B ihA ihB => trivial

end Params

namespace ParamsLower
set_option mumi.mahlo true
set_option maxRecDepth 6000

mumi_spec (xfail := [discr])
mutual
inductive Ctx (X : Type) : Type where
  | nil : Ctx X
  | snoc (Γ : Ctx X) (A : Ty X Γ) : Ctx X
inductive Ty (X : Type) : Ctx X → Type where
  | base {Γ : Ctx X} (x : X) : Ty X Γ
  | pi {Γ : Ctx X} (A : Ty X Γ) (B : Ty X (Ctx.snoc Γ A)) : Ty X Γ
def El {X : Type} : Ctx X → Type
  | .nil => Unit
  | .snoc Γ A => El Γ × Val X A
def Val (X : Type) {Γ : Ctx X} : Ty X Γ → Type
  | .base x => X
  | .pi A B => (x : Val X A) → Val X B
end

def tsize {X : Type} (Γ : Ctx X) (A : Ty X Γ) : Nat :=
  Ty.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat) 0 (fun _ _ ih _ => ih + 1) (fun _ _ => 0) (fun _ _ _ ihA ihB => ihA + ihB + 1) A
theorem Ty.t (X : Type) (Γ : Ctx X) (A : Ty X Γ) : True := by
  induction A with
  | base => trivial
  | pi A B ihA ihB => trivial

end ParamsLower

/-! A carrier's parameter may be implicit too, as Lean allows of any
inductive (`MumiTests/IRParams.lean` has more). -/

namespace ImplicitCarrier
mumi_spec
mutual
inductive U {α : Type} : Type where
  | base : U
  | pi (a : U) (b : El a → U) : U
def El {α : Type} : U (α := α) → Type
  | .base => α
  | .pi a b => (x : El a) → El (b x)
end

example : El (α := Nat) .base = Nat := rfl
end ImplicitCarrier
