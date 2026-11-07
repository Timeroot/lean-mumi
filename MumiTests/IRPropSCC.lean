import MumiTests.Spec.Harness

/-!
# A `Prop` member the carriers depend on

`Good : U → Prop` is part of the induction-recursion proper: `U.pi` takes a
proof of it, so the block cannot be declared without it, and `Good` reads `El`
and `Inh` and recurses into itself.  One universe up the `Prop` member's graph
is a `Prop` family indexed by the carriers' graphs, in the one `mutual` with
them, which `Mumi` declares across the two universes.  `U.rec` and `Good.rec`
are the block's one recursion, as a `mutual` Lean accepted would have: a
hypothesis at the proof `U.pi` takes, and `Good`'s motive displayed, taking the
value the recursion computed at its index (`Mumi.Displayed`).  `mumi_spec`
checks each block; what follows is what that leaves out.
-/

set_option autoImplicit false
set_option mumi.mahlo false

namespace PropSCC

mumi_spec
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

example : Good .base := Good.base

/-- The block's recursion: the proof `U.pi` takes is a field with a hypothesis
of its own, at `Good`'s motive, which takes the value at its index. -/
def depth : U → Nat :=
  U.rec (motive_2 := fun _ _ _ => True) 0 (fun _ _ _ ih _ _ => ih + 1) trivial (fun _ _ _ _ _ _ _ _ _ => trivial)
example (a : U) (b : El a → U) (h : Good a) : depth (U.pi a b h) = depth a + 1 := rfl

/-- The predicate's recursion, which is the block's: `induction` does not take a
member of a mutual block, so it is written out. -/
theorem Good.inh (u : U) (g : Good u) : Inh u :=
  Good.rec (motive_1 := fun _ => Unit) (motive_2 := fun u _ _ => Inh u)
    ⟨⟩ (fun _ _ _ _ _ _ => ⟨⟩) trivial (fun _ _ _ _ _ _ _ _ ihb => fun x => ihb x) g

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

mumi_spec
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

/-- One joint recursion over `Ctx`, `Ty` and `Ok`, a hypothesis at every field:
`Ok`'s motive takes the values at both its indices. -/
def clen : Ctx → Nat :=
  Ctx.rec (motive_2 := fun _ _ => Nat) (motive_3 := fun _ _ _ _ _ => True)
    0 (fun _ _ _ ih _ _ => ih + 1) (fun _ _ => 0) (fun _ _ _ _ _ ihA _ ihB => ihA + ihB + 1)
    (fun _ _ => trivial) (fun _ _ _ _ _ _ _ _ _ _ => trivial)
example (Γ : Ctx) (A : Ty Γ) (h : Ok Γ A) : clen (Ctx.snoc Γ A h) = clen Γ + 1 := rfl

theorem Ok.base_or_pi (Γ : Ctx) (A : Ty Γ) (h : Ok Γ A) :
    A = Ty.base Γ ∨ ∃ A' h' B, A = Ty.pi Γ A' h' B := by
  cases h with
  | base Γ => exact .inl rfl
  | pi Γ A h B hB => exact .inr ⟨A, h, B, rfl⟩

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

mumi_spec (xfail := [discr])
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


def depth : U → Nat :=
  U.rec (motive_2 := fun _ _ _ => True) 0 (fun _ _ _ ih _ _ => ih + 1) trivial (fun _ _ _ _ _ _ _ _ _ => trivial)
example (a : U) (b : El a → U) (h : Good a) : depth (U.pi a b h) = depth a + 1 := rfl

theorem Good.inh (u : U) (g : Good u) : Inh u :=
  Good.rec (motive_1 := fun _ => Unit) (motive_2 := fun u _ _ => Inh u)
    ⟨⟩ (fun _ _ _ _ _ _ => ⟨⟩) trivial (fun _ _ _ _ _ _ _ _ ihb => fun x => ihb x) g

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

mumi_spec (xfail := [discr])
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

def clen : Ctx → Nat :=
  Ctx.rec (motive_2 := fun _ _ => Nat) (motive_3 := fun _ _ _ _ _ => True)
    0 (fun _ _ _ ih _ _ => ih + 1) (fun _ _ => 0) (fun _ _ _ _ _ ihA _ ihB => ihA + ihB + 1)
    (fun _ _ => trivial) (fun _ _ _ _ _ _ _ _ _ _ => trivial)
example (Γ : Ctx) (A : Ty Γ) (h : Ok Γ A) : clen (Ctx.snoc Γ A h) = clen Γ + 1 := rfl

theorem Ok.base_or_pi (Γ : Ctx) (A : Ty Γ) (h : Ok Γ A) :
    A = Ty.base Γ ∨ ∃ A' h' B, A = Ty.pi Γ A' h' B := by
  cases h with
  | base Γ => exact .inl rfl
  | pi Γ A h B hB => exact .inr ⟨A, h, B, rfl⟩

/-- info: 1 -/
#guard_msgs in
#eval clen (Ctx.snoc .nil (.base .nil) (.base .nil))

/-- info: 'PropIdxLower.Ok.base_or_pi' depends on axioms: [IR.mahlo] -/
#guard_msgs in
#print axioms Ok.base_or_pi

end PropIdxLower

/-! Several `Prop` members in the component, mutual with each other, over a
parameter, with the constructors written `.c` and documentation on the members:
one joint `Good.rec` over both, and each member's own `casesOn`.  The minor
premises are named by their constructors, as Lean names a mutual block's, so
two are `base` and two `pi`.  A `Prop` with no index at all is taken the same
way. -/

namespace Several
set_option mumi.mahlo false

mumi_spec
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

theorem Good.t (α : Type) (u : U α) (g : Good α u) : True :=
  Good.rec (motive_1 := fun _ => Unit) (motive_2 := fun _ _ _ => True) (motive_3 := fun _ _ _ => True)
    ⟨⟩ (fun _ _ _ _ _ _ _ _ => ⟨⟩) trivial (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    trivial (fun _ _ _ _ _ _ _ _ _ _ => trivial) g
theorem Fine.c (α : Type) (u : U α) (g : Fine α u) : True := by
  cases g with | base => trivial | pi a b h h' hb => trivial

mumi_spec
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
theorem Ok.t (h : Ok) : True := by cases h with | yes t h => trivial | base => trivial

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

mumi_spec (xfail := [discr])
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

theorem Good.t (α : Type) (u : U α) (g : Good α u) : True :=
  Good.rec (motive_1 := fun _ => Unit) (motive_2 := fun _ _ _ => True) (motive_3 := fun _ _ _ => True)
    ⟨⟩ (fun _ _ _ _ _ _ _ _ => ⟨⟩) trivial (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    trivial (fun _ _ _ _ _ _ _ _ _ _ => trivial) g
theorem Fine.c (α : Type) (u : U α) (g : Fine α u) : True := by
  cases g with | base => trivial | pi a b h h' hb => trivial

mumi_spec (xfail := [discr])
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
theorem Ok.t (h : Ok) : True := by cases h with | yes t h => trivial | base => trivial

end SeveralLower

/-! Parameters, a constructor nested in an index term with a proof among its
arguments, and the constructors written `.c` in the index terms and the
clauses: given their full names when the block is read. -/

namespace NestedProp
set_option mumi.mahlo false

mumi_spec
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

def clen (X : Type) : Ctx X → Nat :=
  Ctx.rec (motive_2 := fun _ _ => Nat) (motive_3 := fun _ _ _ _ _ => True)
    0 (fun _ _ _ ih _ _ => ih + 1) (fun _ _ _ => 0) (fun _ _ _ _ _ ihA _ ihB => ihA + ihB + 1)
    (fun _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ _ _ => trivial)
theorem Ok.t (X : Type) (Γ : Ctx X) (A : Ty X Γ) (h : Ok X Γ A) : True := by
  cases h with | base Γ x => trivial | pi Γ A h B hB => trivial

/-- info: 1 -/
#guard_msgs in
#eval clen Nat (Ctx.snoc (X := Nat) .nil (Ty.base .nil 3) (Ok.base .nil 3))

end NestedProp

namespace NestedPropLower
set_option mumi.mahlo true
set_option maxRecDepth 6000

mumi_spec (xfail := [discr])
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

def clen (X : Type) : Ctx X → Nat :=
  Ctx.rec (motive_2 := fun _ _ => Nat) (motive_3 := fun _ _ _ _ _ => True)
    0 (fun _ _ _ ih _ _ => ih + 1) (fun _ _ _ => 0) (fun _ _ _ _ _ ihA _ ihB => ihA + ihB + 1)
    (fun _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ _ _ => trivial)
theorem Ok.t (X : Type) (Γ : Ctx X) (A : Ty X Γ) (h : Ok X Γ A) : True := by
  cases h with | base Γ x => trivial | pi Γ A h B hB => trivial

/-- info: 1 -/
#guard_msgs in
#eval clen Nat (Ctx.snoc (X := Nat) .nil (Ty.base .nil 3) (Ok.base .nil 3))

end NestedPropLower

/-! A datum no index names may be a function: the induction over the block has a
hypothesis at each of its values, and the value of the recursion there is computed
pointwise.  The minor premise binds it as any other, and uses it. -/

namespace SeveralFun
set_option mumi.mahlo false

mumi_spec
mutual
inductive T : Type where
  | base : T
  | pi (a : T) (b : D a → T) (h : Ok) : T
inductive Ok : Prop where
  | yes (f : Nat → T) (h : Ok) : Ok
  | base : Ok
def D : T → Type
  | .base => Nat
  | .pi a b h => (x : D a) → D (b x)
end

/-- The hypothesis at `f` is the recursion's value at each `f n`. -/
theorem Ok.values (h : Ok) : True :=
  Ok.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => True)
    0 (fun _ _ _ ih _ _ => ih + 1) (fun _ _ f_ih _ => (fun _ : Nat => trivial) (f_ih 0)) trivial h

/-- info: 'SeveralFun.Ok.values' does not depend on any axioms -/
#guard_msgs in
#print axioms Ok.values

end SeveralFun

namespace SeveralFunLower
set_option mumi.mahlo true
set_option maxRecDepth 6000

mumi_spec (xfail := [discr])
mutual
inductive T : Type where
  | base : T
  | pi (a : T) (b : D a → T) (h : Ok) : T
inductive Ok : Prop where
  | yes (f : Nat → T) (h : Ok) : Ok
  | base : Ok
def D : T → Type
  | .base => Nat
  | .pi a b h => (x : D a) → D (b x)
end

end SeveralFunLower
