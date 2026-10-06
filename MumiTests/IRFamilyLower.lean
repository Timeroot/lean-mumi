import MumiTests.Spec.Harness

/-!
# Induction-induction and induction-recursion in one block, at the universe written

The `Family` path of the IR frontend: carriers indexed by other carriers and by
decoder values, decoders over indexed carriers, and the equations each of them
comes with.  Everything here stays at the universe it was written at, on the reflection
axiom, and every equation is still `rfl` but two at nested indices; what is
given up is closed normalisation, so the closed checks of the upper file are
not repeated.  `mumi_spec` checks each block's declarations and rules; what
follows a block is what that leaves out.
-/

set_option autoImplicit false
set_option mumi.mahlo true

/-! ## The canonical case

`Ty` is indexed by `Ctx`, `Env` computes a type from a `Ctx`, and `El` computes
a type from a `Ty` at an environment.  `Ty.Pi` builds the index of its second
field out of a constructor. -/

namespace CtxTyL

mumi_spec (xfail := [casesOn, injEq])
mutual
inductive Ctx : Type where
  | nil : Ctx
  | ext (Γ : Ctx) (A : Ty Γ) : Ctx
inductive Ty : (Γ : Ctx) → Type where
  | U (Γ : Ctx) : Ty Γ
  | Pi (Γ : Ctx) (A : Ty Γ) (B : Ty (Ctx.ext Γ A)) : Ty Γ
def Env : Ctx → Type
  | .nil => PUnit
  | .ext Γ A => (ρ : Env Γ) × El Γ A ρ
def El : (Γ : Ctx) → Ty Γ → Env Γ → Type
  | _, .U Γ => fun _ => Nat
  | _, .Pi Γ A B => fun ρ => (a : El Γ A ρ) → El (Ctx.ext Γ A) B ⟨ρ, a⟩
end

/-- The one-motive recursor `induction` drives: the other motive is discharged at
`PUnit`, and the hypothesis at a field of the other carrier goes with it. -/
example (Γ : Ctx) (A : Ty Γ) : True := by
  induction A with
  | U _ => trivial
  | Pi _ _ _ ihA ihB => trivial

/--
info: @Ty.recD : {motive : (Γ : Ctx) → Ty Γ → Sort u_1} →
  {Γ : Ctx} →
    (t : Ty Γ) →
      ((Γ : Ctx) → motive Γ (Ty.U Γ)) →
        ((Γ : Ctx) → (A : Ty Γ) → (B : Ty (Γ.ext A)) → motive Γ A → motive (Γ.ext A) B → motive Γ (Ty.Pi Γ A B)) →
          motive Γ t
-/
#guard_msgs in
#check @Ty.recD

/-- The number of `ext`s, by the recursor. -/
def len : Ctx → Nat :=
  Ctx.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Unit)
    0 (fun _ _ ih _ => ih + 1) (fun _ _ => ()) (fun _ _ _ _ _ _ => ())

/-- info: 2 -/
#guard_msgs in
#eval len (Ctx.ext (Ctx.ext Ctx.nil (Ty.U Ctx.nil)) (Ty.U _))


/-- A closed environment for every context, by the joint recursion. -/
def env : (Γ : Ctx) → Env Γ :=
  Ctx.rec (motive_1 := fun Γ => Env Γ) (motive_2 := fun Γ A => (ρ : Env Γ) → El Γ A ρ)
    PUnit.unit
    (fun _ _ ρ a => ⟨ρ, a ρ⟩)
    (fun _ _ _ => (0 : Nat))
    (fun _ _ _ _ _ ihB ρ => fun a => ihB ⟨ρ, a⟩)

example (Γ : Ctx) (A : Ty Γ) : (env (Ctx.ext Γ A)).1 = env Γ := rfl

example (Γ : Ctx) : True := by cases Γ <;> trivial
example (Γ : Ctx) (A : Ty Γ) : True := by cases A <;> trivial

/-- info: 'CtxTyL.env' depends on axioms: [IR.mahlo] -/
#guard_msgs in
#print axioms env

end CtxTyL

/-! ## A decoder into values, and an index a decoder computes

`size` is a decoder into `Nat`; `Path` is indexed by a `Code` and by a `Nat`
that its constructors fill with `size` of their fields. -/

namespace ByValueL

mumi_spec (xfail := [casesOn, injEq])
mutual
inductive Code : Type where
  | one : Code
  | pair (a b : Code) : Code
inductive Path : (c : Code) → Nat → Type where
  | stop (c : Code) : Path c (size c)
  | left (a b : Code) (p : Path a (size a)) : Path (Code.pair a b) (size a + size b)
def size : Code → Nat
  | .one => 1
  | .pair a b => size a + size b
def depth : (c : Code) → (n : Nat) → Path c n → Nat
  | _, _, .stop c => 0
  | _, _, .left a b p => depth a (size a) p + 1
end

/-- info: 'ByValueL.depth_left' depends on axioms: [IR.mahlo] -/
#guard_msgs in
#print axioms depth_left

end ByValueL

/-! ## Universe polymorphism, parameters, and an infinitary field at a built index -/

namespace PolyL
universe u

mumi_spec (xfail := [casesOn, injEq])
mutual
inductive Ctx (X : Type u) : Type u where
  | nil : Ctx X
  | ext (Γ : Ctx X) (A : Ty X Γ) : Ctx X
inductive Ty (X : Type u) : (Γ : Ctx X) → Type u where
  | base (Γ : Ctx X) (x : X) : Ty X Γ
  | pi (Γ : Ctx X) (A : Ty X Γ) (B : El X Γ A → Ty X (Ctx.ext Γ A)) : Ty X Γ
def El (X : Type u) : (Γ : Ctx X) → Ty X Γ → Type u
  | _, .base Γ x => PUnit
  | _, .pi Γ A B => (a : El X Γ A) → El X (Ctx.ext Γ A) (B a)
end

/-- info: 'PolyL.El_pi' depends on axioms: [IR.mahlo] -/
#guard_msgs in
#print axioms El_pi

end PolyL

/-! ## Constructors written with a dot -/

namespace DottedL

mumi_spec (xfail := [casesOn, injEq])
mutual
inductive Ctx : Type where
  | nil : Ctx
  | ext (Γ : Ctx) (A : Ty Γ) : Ctx
inductive Ty : (Γ : Ctx) → Type where
  | base (Γ : Ctx) : Ty Γ
  | many (Γ : Ctx) (A : Ty Γ) (g : Nat → Ty (.ext Γ A)) : Ty Γ
def El : (Γ : Ctx) → Ty Γ → Type
  | _, .base Γ => Nat
  | _, .many Γ A g => (n : Nat) → El (.ext Γ A) (g n)
end

example (Γ : Ctx) (A : Ty Γ) : True := by
  induction A with
  | base _ => trivial
  | many _ _ _ ihA ihg => trivial

end DottedL

/-! ## No carrier in any arity

`Vec` is indexed by a `Nat` only.  One universe up the graph block is a plain
mutual family whose kernel recursor the code generator does not compile; here
the recursor is the stage engine's, and it runs. -/

namespace PlainL

mumi_spec (xfail := [casesOn, injEq])
mutual
inductive Vec : Nat → Type where
  | nil : Vec 0
  | cons (n : Nat) (a : Code) (v : Vec n) : Vec (n + 1)
inductive Code : Type where
  | one : Code
  | many (n : Nat) (v : Vec n) : Code
def El : Code → Type
  | .one => Nat
  | .many n v => Env n v
def Env : (n : Nat) → Vec n → Type
  | _, .nil => PUnit
  | _, .cons n a v => El a × Env n v
end

def len (n : Nat) (v : Vec n) : Nat :=
  Vec.rec (motive_1 := fun _ _ => Nat) (motive_2 := fun _ => Unit)
    0 (fun _ _ _ _ ih => ih + 1) () (fun _ _ _ => ()) v

/-- info: 2 -/
#guard_msgs in
#eval len 2 (Vec.cons 1 Code.one (Vec.cons 0 Code.one Vec.nil))

example (n : Nat) (v : Vec n) : True := by
  induction v with
  | nil => trivial
  | cons _ _ _ ih => trivial

/-- info: 'PlainL.len' depends on axioms: [IR.mahlo] -/
#guard_msgs in
#print axioms len

end PlainL

/-! ## What the path declines -/

open Lean Elab Command in
elab "reject_ir " expected:str " in " c:command : command => do
  let saved ← get
  let count := saved.messages.reportedPlusUnreported.size
  try elabCommand c
  catch ex => logException ex
  let errors := ((← get).messages.reportedPlusUnreported.toList.drop count).filter (·.severity == .error)
  let messages ← errors.mapM (fun e => e.data.toString)
  set saved
  unless messages.any (fun s => (s.splitOn expected.getString).length > 1) do
    throwError "Expected IR rejection containing {expected.getString}, got {messages}"

namespace RejectedL

-- an index domain mentioning a carrier is that carrier applied outright, or,
-- not yet, a nested application of it
reject_ir "indexed by a nested application" in
mutual
inductive A : Type where
  | nil : A
inductive B : List A → Type where
  | mk (a : A) : B [a]
def f : A → Type
  | .nil => Nat
end

-- a decoder binds the indices of its carrier, in order, just before it
reject_ir "bound in order just before it" in
mutual
inductive A : Type where
  | nil : A
inductive B : A → Type where
  | mk (a : A) : B a
def f : (b : B A.nil) → Type
  | .mk a => Nat
end

-- a field of carrier type is read only through decoders
reject_ir "only through their decoders" in
mutual
inductive A : Type where
  | nil : A
  | mk (x y : A) (h : x = y) : A
inductive B : A → Type where
  | mk (a : A) : B a
def f : A → Type
  | .nil => Nat
  | .mk x y h => Nat
end

end RejectedL

/-! ## An index built out of a function field applied to a binder

One universe up this block is rejected: the erasure underneath cannot delete
an index that recurses under a binder.  At the universe it is written at
nothing is erased, so it goes through, equations included. -/

namespace UnderBinderL

mumi_spec (xfail := [casesOn, injEq])
mutual
inductive Ctx : Type where
  | nil : Ctx
  | ext (Γ : Ctx) (A : Ty Γ) : Ctx
inductive Ty : (Γ : Ctx) → Type where
  | base (Γ : Ctx) : Ty Γ
  | many (Γ : Ctx) (f : Nat → Ty Γ) (g : (n : Nat) → Ty (.ext Γ (f n))) : Ty Γ
def El : (Γ : Ctx) → Ty Γ → Type
  | _, .base Γ => Nat
  | _, .many Γ f g => (n : Nat) → El (.ext Γ (f n)) (g n)
end

end UnderBinderL

/-! ## Constructors nested inside constructors in index terms

At the written universe the decode of a nested constructor does not reduce,
so the lower view names each nested application by a hidden raw field the
constructor supplies and the certificate pins; nothing is asked of the user,
and every equation is still definitional. -/

namespace NestedL

-- What is given up: a decoder equation whose right-hand side reads a decoder
-- at a nested index transports along the decode of that index, which does not
-- reduce here, so `El_deep` and `El_shift` are not definitional and are not
-- stated; the iota rules are.
mumi_spec (unproven := [El_deep, El_shift]) (xfail := [casesOn, injEq])
mutual
inductive Ctx : Type where
  | nil : Ctx
  | ext (Γ : Ctx) (A : Ty Γ) : Ctx
inductive Ty : (Γ : Ctx) → Type where
  | U (Γ : Ctx) : Ty Γ
  -- a field at an index three deep
  | deep (Γ : Ctx) (A : Ty Γ) (B : Ty (.ext Γ A)) (C : Ty (.ext (.ext Γ A) B)) : Ty Γ
  -- a conclusion three deep, and a function field whose index nests under its binder
  | shift (Γ : Ctx) (A : Ty Γ) (B : Ty (.ext Γ A)) (f : (n : Nat) → Ty (.ext (.ext Γ A) B)) :
      Ty (.ext (.ext Γ A) B)
def El : (Γ : Ctx) → Ty Γ → Type
  | _, .U Γ => Nat
  | _, .deep Γ A B C => El (.ext (.ext Γ A) B) C
  | _, .shift Γ A B f => (n : Nat) → El (.ext (.ext Γ A) B) (f n)
-- a decoder on the nested carrier, so that its semantics is not trivial
def depth : Ctx → Nat
  | .nil => 0
  | .ext Γ A => depth Γ + 1
end

/-- How many `ext`s a context has, counting through the types it holds. -/
def size : Ctx → Nat :=
  Ctx.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    0 (fun _ _ ihΓ ihA => ihΓ + ihA + 1) (fun _ _ => 0)
    (fun _ _ _ _ _ ihA ihB ihC => ihA + ihB + ihC) (fun _ _ _ _ _ ihA ihB ihf => ihA + ihB + ihf 0)

/-- info: 2 -/
#guard_msgs in
#eval size (.ext (.ext .nil (.U .nil)) (.deep (.ext .nil (.U .nil)) (.U _) (.U _) (.U _)))

/-- info: 'NestedL.size' depends on axioms: [IR.mahlo] -/
#guard_msgs in
#print axioms size

example (Γ : Ctx) (A : Ty Γ) : True := by induction A <;> trivial
example (Γ : Ctx) (A : Ty Γ) : True := by cases A <;> trivial

end NestedL
