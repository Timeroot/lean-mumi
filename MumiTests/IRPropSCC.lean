import Mumi

/-!
# A `Prop` member the carriers depend on

`Good : U → Prop` is part of the induction-recursion proper: `U.pi` takes a
proof of it, so the block cannot be declared without it, and `Good` reads `El`
and `Inh` and recurses into itself.  One universe up the `Prop` member's graph
is a `Prop` family indexed by the carriers' graphs, in the one `mutual` with
them, which `Mumi` declares across the two universes: `U.rec` is over the data
with the proof as a field, and `Good.rec` is the predicate's own.
-/

set_option autoImplicit false
set_option mumi.mahlo false

namespace PropSCC

mutual
inductive U : Type where
  | base : U
  | pi (a : U) (b : El a → U) (h : Good a) : U
inductive Good : U → Prop where
  | base : Good .base
  | pi (a : U) (b : El a → U) (h : Good a) (ha : Inh a) (hb : ∀ x : El a, Good (b x)) : Good (.pi a b h)
def El : U → Type
  | .base => Nat
  | .pi a b h => (x : El a) → El (b x)
def Inh : U → Prop
  | .base => True
  | .pi a b h => ∀ x : El a, Inh (b x)
end

example (a : U) (b : El a → U) (h : Good a) : El (U.pi a b h) = ((x : El a) → El (b x)) := rfl
example (a : U) (b : El a → U) (h : Good a) : Inh (U.pi a b h) = ∀ x : El a, Inh (b x) := rfl
example : Good .base := Good.base

/-- The data recursor: the proof is a field, with no hypothesis of its own. -/
def depth : U → Nat := U.rec 0 (fun _ _ _ ih _ => ih + 1)
example (a : U) (b : El a → U) (h : Good a) : depth (U.pi a b h) = depth a + 1 := rfl

/-- The predicate's recursor, by `induction`. -/
theorem Good.inh (u : U) (g : Good u) : Inh u := by
  induction g with
  | base => trivial
  | pi a b h ha hb ih ihb => exact fun x => ihb x

theorem Good.depth_pos (u : U) (g : Good u) : u = .base ∨ 0 < depth u := by
  cases g with
  | base => exact .inl rfl
  | pi a b h ha hb => exact .inr (Nat.succ_pos _)

def u1 : U := U.pi U.base (fun _ => U.base) Good.base
example : depth u1 = 1 := rfl
-- the proof `U.pi` was built with is no field of the data, so it has to be named
example : Good u1 := .pi _ _ Good.base trivial (fun _ => .base)

/-- info: 1 -/
#guard_msgs in
#eval depth u1

/-- info: 'PropSCC.Good.inh' does not depend on any axioms -/
#guard_msgs in
#print axioms Good.inh

end PropSCC

/-! An indexed carrier with a `Prop` the block needs: a context may only be
extended by a type that is `Ok`, and `Ok` is stated over the types of the
block, which are induction-inductive.  The graphs go through `Mumi.IndInd` and
the well-formedness sits on top of them. -/

namespace PropIdx
set_option mumi.mahlo false

mutual
inductive Ctx : Type where
  | nil : Ctx
  | snoc (Γ : Ctx) (A : Ty Γ) (h : Ok Γ A) : Ctx
inductive Ty : Ctx → Type where
  | base (Γ : Ctx) : Ty Γ
  | pi (Γ : Ctx) (A : Ty Γ) (h : Ok Γ A) (B : Ty (.snoc Γ A h)) : Ty Γ
inductive Ok : (Γ : Ctx) → Ty Γ → Prop where
  | base (Γ : Ctx) : Ok Γ (.base Γ)
  | pi (Γ : Ctx) (A : Ty Γ) (h : Ok Γ A) (B : Ty (.snoc Γ A h)) (hB : Ok (.snoc Γ A h) B) : Ok Γ (.pi Γ A h B)
def El : Ctx → Type
  | .nil => Unit
  | .snoc Γ A h => El Γ × Val Γ A
def Val : (Γ : Ctx) → Ty Γ → Type
  | _, .base Γ => Nat
  | _, .pi Γ A h B => (x : Val Γ A) → Val (.snoc Γ A h) B
end

example (Γ : Ctx) (A : Ty Γ) (h : Ok Γ A) : El (Ctx.snoc Γ A h) = (El Γ × Val Γ A) := rfl
example (Γ : Ctx) (A : Ty Γ) (h : Ok Γ A) (B : Ty (.snoc Γ A h)) :
    Val Γ (Ty.pi Γ A h B) = ((x : Val Γ A) → Val (.snoc Γ A h) B) := rfl

/-- One joint recursion over `Ctx` and `Ty`, the proofs as fields. -/
def clen : Ctx → Nat :=
  Ctx.rec (motive_2 := fun _ _ => Nat) 0 (fun _ _ _ ih _ => ih + 1) (fun _ _ => 0) (fun _ _ _ _ _ ihA ihB => ihA + ihB + 1)
example (Γ : Ctx) (A : Ty Γ) (h : Ok Γ A) : clen (Ctx.snoc Γ A h) = clen Γ + 1 := rfl

theorem Ok.base_or_pi (Γ : Ctx) (A : Ty Γ) (h : Ok Γ A) :
    A = Ty.base Γ ∨ ∃ A' h' B, A = Ty.pi Γ A' h' B := by
  induction h with
  | base Γ => exact .inl rfl
  | pi Γ A h B hB ih ihB => exact .inr ⟨A, h, B, rfl⟩

/-- info: 1 -/
#guard_msgs in
#eval clen (Ctx.snoc .nil (.base .nil) (.base .nil))

/-- info: 'PropIdx.Ok.base_or_pi' does not depend on any axioms -/
#guard_msgs in
#print axioms Ok.base_or_pi

end PropIdx

/-! At the written universe the proofs are the certificates': `Good` is a
certificate over the raw terms in the one `mutual` with `U`'s, and the
public `U` is the subtype by its own.  Everything below is as one universe
up, on the one axiom. -/

namespace PropSCCLower
set_option mumi.mahlo true
set_option maxRecDepth 6000

mutual
inductive U : Type where
  | base : U
  | pi (a : U) (b : El a → U) (h : Good a) : U
inductive Good : U → Prop where
  | base : Good .base
  | pi (a : U) (b : El a → U) (h : Good a) (ha : Inh a) (hb : ∀ x : El a, Good (b x)) : Good (.pi a b h)
def El : U → Type
  | .base => Nat
  | .pi a b h => (x : El a) → El (b x)
def Inh : U → Prop
  | .base => True
  | .pi a b h => ∀ x : El a, Inh (b x)
end

example : Type := U
example (a : U) (b : El a → U) (h : Good a) : El (U.pi a b h) = ((x : El a) → El (b x)) := rfl
example (a : U) (b : El a → U) (h : Good a) : Inh (U.pi a b h) = ∀ x : El a, Inh (b x) := rfl

def depth : U → Nat := U.rec 0 (fun _ _ _ ih _ => ih + 1)
example (a : U) (b : El a → U) (h : Good a) : depth (U.pi a b h) = depth a + 1 := rfl

theorem Good.inh (u : U) (g : Good u) : Inh u := by
  induction g with
  | base => trivial
  | pi a b h ha hb ih ihb => exact fun x => ihb x

theorem Good.depth_pos (u : U) (g : Good u) : u = .base ∨ 0 < depth u := by
  cases g with
  | base => exact .inl rfl
  | pi a b h ha hb => exact .inr (Nat.succ_pos _)

def u1 : U := U.pi U.base (fun _ => U.base) Good.base
example : Good u1 := .pi _ _ Good.base trivial (fun _ => .base)

/-- info: 1 -/
#guard_msgs in
#eval depth u1

/-- info: 'PropSCCLower.Good.inh' depends on axioms: [IR.mahlo] -/
#guard_msgs in
#print axioms Good.inh

end PropSCCLower

namespace PropIdxLower
set_option mumi.mahlo true
set_option maxRecDepth 6000

mutual
inductive Ctx : Type where
  | nil : Ctx
  | snoc (Γ : Ctx) (A : Ty Γ) (h : Ok Γ A) : Ctx
inductive Ty : Ctx → Type where
  | base (Γ : Ctx) : Ty Γ
  | pi (Γ : Ctx) (A : Ty Γ) (h : Ok Γ A) (B : Ty (.snoc Γ A h)) : Ty Γ
inductive Ok : (Γ : Ctx) → Ty Γ → Prop where
  | base (Γ : Ctx) : Ok Γ (.base Γ)
  | pi (Γ : Ctx) (A : Ty Γ) (h : Ok Γ A) (B : Ty (.snoc Γ A h)) (hB : Ok (.snoc Γ A h) B) : Ok Γ (.pi Γ A h B)
def El : Ctx → Type
  | .nil => Unit
  | .snoc Γ A h => El Γ × Val Γ A
def Val : (Γ : Ctx) → Ty Γ → Type
  | _, .base Γ => Nat
  | _, .pi Γ A h B => (x : Val Γ A) → Val (.snoc Γ A h) B
end

example (Γ : Ctx) (A : Ty Γ) (h : Ok Γ A) : El (Ctx.snoc Γ A h) = (El Γ × Val Γ A) := rfl
example (Γ : Ctx) (A : Ty Γ) (h : Ok Γ A) (B : Ty (.snoc Γ A h)) :
    Val Γ (Ty.pi Γ A h B) = ((x : Val Γ A) → Val (.snoc Γ A h) B) := rfl

def clen : Ctx → Nat :=
  Ctx.rec (motive_2 := fun _ _ => Nat) 0 (fun _ _ _ ih _ => ih + 1) (fun _ _ => 0) (fun _ _ _ _ _ ihA ihB => ihA + ihB + 1)
example (Γ : Ctx) (A : Ty Γ) (h : Ok Γ A) : clen (Ctx.snoc Γ A h) = clen Γ + 1 := rfl

theorem Ok.base_or_pi (Γ : Ctx) (A : Ty Γ) (h : Ok Γ A) :
    A = Ty.base Γ ∨ ∃ A' h' B, A = Ty.pi Γ A' h' B := by
  induction h with
  | base Γ => exact .inl rfl
  | pi Γ A h B hB ih ihB => exact .inr ⟨A, h, B, rfl⟩

/-- info: 1 -/
#guard_msgs in
#eval clen (Ctx.snoc .nil (.base .nil) (.base .nil))

/-- info: 'PropIdxLower.Ok.base_or_pi' depends on axioms: [IR.mahlo] -/
#guard_msgs in
#print axioms Ok.base_or_pi

end PropIdxLower

/-! Several `Prop` members in the component, mutual with each other, over a
parameter, with the constructors written `.c` and documentation on the members:
one joint `Good.rec` over both, named minor premises apart, and each member's
own `casesOn`.  A `Prop` with no index at all is taken the same way. -/

namespace Several
set_option mumi.mahlo false

mutual
/-- codes over `α` -/
inductive U (α : Type) : Type where
  | base : U α
  | pi (a : U α) (b : El α a → U α) (h : Good α a) (h' : Fine α a) : U α
inductive Good (α : Type) : U α → Prop where
  | base : Good α .base
  | pi (a : U α) (b : El α a → U α) (h : Good α a) (h' : Fine α a) (hb : ∀ x : El α a, Fine α (b x)) : Good α (.pi a b h h')
inductive Fine (α : Type) : U α → Prop where
  | base : Fine α .base
  | pi (a : U α) (b : El α a → U α) (h : Good α a) (h' : Fine α a) (hb : ∀ x : El α a, Good α (b x)) : Fine α (.pi a b h h')
/-- decoding -/
def El (α : Type) : U α → Type
  | .base => α
  | .pi a b h h' => (x : El α a) → El α (b x)
end

example (α : Type) : El α .base = α := rfl
example (α : Type) (a : U α) (b : El α a → U α) (h : Good α a) (h' : Fine α a) :
    El α (U.pi a b h h') = ((x : El α a) → El α (b x)) := rfl
theorem Good.t (α : Type) (u : U α) (g : Good α u) : True := by
  induction g using Good.rec (motive_3 := fun _ _ => True) with
  | Good_base => trivial | Good_pi => trivial | Fine_base => trivial | Fine_pi => trivial
theorem Fine.c (α : Type) (u : U α) (g : Fine α u) : True := by
  cases g with | base => trivial | pi a b h h' hb => trivial

mutual
inductive T : Type where
  | base : T
  | pi (a : T) (b : D a → T) (h : Ok) : T
inductive Ok : Prop where
  | yes (t : T) (h : Ok) : Ok
  | base : Ok
def D : T → Type
  | .base => Nat
  | .pi a b h => (x : D a) → D (b x)
end
theorem Ok.t (h : Ok) : True := by induction h with | yes t h ih => trivial | base => trivial

-- the documentation goes onto the public declarations
open Lean Elab Command in
/-- info: (some "codes over `α` ", some "decoding ") -/
#guard_msgs in
#eval show CommandElabM _ from do
  return (← findDocString? (← getEnv) ``Several.U, ← findDocString? (← getEnv) ``Several.El)

end Several

namespace SeveralLower
set_option mumi.mahlo true
set_option maxRecDepth 6000

mutual
/-- codes over `α` -/
inductive U (α : Type) : Type where
  | base : U α
  | pi (a : U α) (b : El α a → U α) (h : Good α a) (h' : Fine α a) : U α
inductive Good (α : Type) : U α → Prop where
  | base : Good α .base
  | pi (a : U α) (b : El α a → U α) (h : Good α a) (h' : Fine α a) (hb : ∀ x : El α a, Fine α (b x)) : Good α (.pi a b h h')
inductive Fine (α : Type) : U α → Prop where
  | base : Fine α .base
  | pi (a : U α) (b : El α a → U α) (h : Good α a) (h' : Fine α a) (hb : ∀ x : El α a, Good α (b x)) : Fine α (.pi a b h h')
/-- decoding -/
def El (α : Type) : U α → Type
  | .base => α
  | .pi a b h h' => (x : El α a) → El α (b x)
end

example (α : Type) (a : U α) (b : El α a → U α) (h : Good α a) (h' : Fine α a) :
    El α (U.pi a b h h') = ((x : El α a) → El α (b x)) := rfl
theorem Good.t (α : Type) (u : U α) (g : Good α u) : True := by
  induction g using Good.rec (motive_3 := fun _ _ => True) with
  | Good_base => trivial | Good_pi => trivial | Fine_base => trivial | Fine_pi => trivial
theorem Fine.c (α : Type) (u : U α) (g : Fine α u) : True := by
  cases g with | base => trivial | pi a b h h' hb => trivial

mutual
inductive T : Type where
  | base : T
  | pi (a : T) (b : D a → T) (h : Ok) : T
inductive Ok : Prop where
  | yes (t : T) (h : Ok) : Ok
  | base : Ok
def D : T → Type
  | .base => Nat
  | .pi a b h => (x : D a) → D (b x)
end
theorem Ok.t (h : Ok) : True := by induction h with | yes t h ih => trivial | base => trivial

end SeveralLower

/-! Parameters, a constructor nested in an index term with a proof among its
arguments, and the constructors written `.c` in the index terms and the
clauses: given their full names when the block is read. -/

namespace NestedProp
set_option mumi.mahlo false

mutual
inductive Ctx (X : Type) : Type where
  | nil : Ctx X
  | snoc (Γ : Ctx X) (A : Ty X Γ) (h : Ok X Γ A) : Ctx X
inductive Ty (X : Type) : Ctx X → Type where
  | base (Γ : Ctx X) (x : X) : Ty X Γ
  | pi (Γ : Ctx X) (A : Ty X Γ) (h : Ok X Γ A) (B : Ty X (.snoc Γ A h)) : Ty X Γ
inductive Ok (X : Type) : (Γ : Ctx X) → Ty X Γ → Prop where
  | base (Γ : Ctx X) (x : X) : Ok X Γ (.base Γ x)
  | pi (Γ : Ctx X) (A : Ty X Γ) (h : Ok X Γ A) (B : Ty X (.snoc Γ A h)) (hB : Ok X (.snoc Γ A h) B) : Ok X Γ (.pi Γ A h B)
def El (X : Type) : Ctx X → Type
  | .nil => Unit
  | .snoc Γ A h => El X Γ × Val X Γ A
def Val (X : Type) : (Γ : Ctx X) → Ty X Γ → Type
  | _, .base Γ x => X
  | _, .pi Γ A h B => (x : Val X Γ A) → Val X (.snoc Γ A h) B
end

example (X : Type) (Γ : Ctx X) (A : Ty X Γ) (h : Ok X Γ A) (B : Ty X (Ctx.snoc Γ A h)) :
    Val X Γ (Ty.pi Γ A h B) = ((x : Val X Γ A) → Val X (Ctx.snoc Γ A h) B) := Val_pi X Γ A h B
def clen (X : Type) : Ctx X → Nat :=
  Ctx.rec (motive_2 := fun _ _ => Nat) 0 (fun _ _ _ ih _ => ih + 1) (fun _ _ _ => 0) (fun _ _ _ _ _ ihA ihB => ihA + ihB + 1)
theorem Ok.t (X : Type) (Γ : Ctx X) (A : Ty X Γ) (h : Ok X Γ A) : True := by
  induction h with | base Γ x => trivial | pi Γ A h B hB ih ihB => trivial

/-- info: 1 -/
#guard_msgs in
#eval clen Nat (Ctx.snoc (X := Nat) .nil (Ty.base .nil 3) (Ok.base .nil 3))

end NestedProp

namespace NestedPropLower
set_option mumi.mahlo true
set_option maxRecDepth 6000

mutual
inductive Ctx (X : Type) : Type where
  | nil : Ctx X
  | snoc (Γ : Ctx X) (A : Ty X Γ) (h : Ok X Γ A) : Ctx X
inductive Ty (X : Type) : Ctx X → Type where
  | base (Γ : Ctx X) (x : X) : Ty X Γ
  | pi (Γ : Ctx X) (A : Ty X Γ) (h : Ok X Γ A) (B : Ty X (.snoc Γ A h)) : Ty X Γ
inductive Ok (X : Type) : (Γ : Ctx X) → Ty X Γ → Prop where
  | base (Γ : Ctx X) (x : X) : Ok X Γ (.base Γ x)
  | pi (Γ : Ctx X) (A : Ty X Γ) (h : Ok X Γ A) (B : Ty X (.snoc Γ A h)) (hB : Ok X (.snoc Γ A h) B) : Ok X Γ (.pi Γ A h B)
def El (X : Type) : Ctx X → Type
  | .nil => Unit
  | .snoc Γ A h => El X Γ × Val X Γ A
def Val (X : Type) : (Γ : Ctx X) → Ty X Γ → Type
  | _, .base Γ x => X
  | _, .pi Γ A h B => (x : Val X Γ A) → Val X (.snoc Γ A h) B
end

example (X : Type) (Γ : Ctx X) (A : Ty X Γ) (h : Ok X Γ A) (B : Ty X (Ctx.snoc Γ A h)) :
    Val X Γ (Ty.pi Γ A h B) = ((x : Val X Γ A) → Val X (Ctx.snoc Γ A h) B) := Val_pi X Γ A h B
def clen (X : Type) : Ctx X → Nat :=
  Ctx.rec (motive_2 := fun _ _ => Nat) 0 (fun _ _ _ ih _ => ih + 1) (fun _ _ _ => 0) (fun _ _ _ _ _ ihA ihB => ihA + ihB + 1)
theorem Ok.t (X : Type) (Γ : Ctx X) (A : Ty X Γ) (h : Ok X Γ A) : True := by
  induction h with | base Γ x => trivial | pi Γ A h B hB ih ihB => trivial

/-- info: 1 -/
#guard_msgs in
#eval clen Nat (Ctx.snoc (X := Nat) .nil (Ty.base .nil 3) (Ok.base .nil 3))

end NestedPropLower
