import Mumi

/-!
# Induction-induction and induction-recursion in one block

The `Family` path of the IR frontend: carriers indexed by other carriers and by
decoder values, decoders over indexed carriers, and the equations each of them
comes with.  Everything here is one universe up, and every equation is `rfl`.
-/

set_option autoImplicit false
set_option mumi.mahlo false

/-! ## The canonical case

`Ty` is indexed by `Ctx`, `Env` computes a type from a `Ctx`, and `El` computes
a type from a `Ty` at an environment.  `Ty.Pi` builds the index of its second
field out of a constructor. -/

namespace CtxTy

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

example : Type 1 := Ctx
example (Γ : Ctx) : Type 1 := Ty Γ
example : Env Ctx.nil = PUnit := rfl
example (Γ : Ctx) (A : Ty Γ) : Env (Ctx.ext Γ A) = ((ρ : Env Γ) × El Γ A ρ) := rfl
example (Γ : Ctx) : El Γ (Ty.U Γ) = fun _ => Nat := rfl
example (Γ : Ctx) (A : Ty Γ) (B : Ty (Ctx.ext Γ A)) :
    El Γ (Ty.Pi Γ A B) = fun ρ => (a : El Γ A ρ) → El (Ctx.ext Γ A) B ⟨ρ, a⟩ := rfl

/--
info: @Ty.rec : {motive : Ctx → Sort u_1} →
  {motive_2 : (Γ : Ctx) → Ty Γ → Sort u_1} →
    motive Ctx.nil →
      ((Γ : Ctx) → (A : Ty Γ) → motive Γ → motive_2 Γ A → motive (Γ.ext A)) →
        ((Γ : Ctx) → motive Γ → motive_2 Γ (Ty.U Γ)) →
          ((Γ : Ctx) →
              (A : Ty Γ) →
                (B : Ty (Γ.ext A)) → motive Γ → motive_2 Γ A → motive_2 (Γ.ext A) B → motive_2 Γ (Ty.Pi Γ A B)) →
            {Γ : Ctx} → (t : Ty Γ) → motive_2 Γ t
-/
#guard_msgs in
#check @Ty.rec

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
  Ctx.rec (motive := fun _ => Nat) (motive_2 := fun _ _ => Unit)
    0 (fun _ _ ih _ => ih + 1) (fun _ _ => ()) (fun _ _ _ _ _ _ => ())

example : len (Ctx.ext (Ctx.ext Ctx.nil (Ty.U _)) (Ty.U _)) = 2 := rfl

/-- A closed environment for every context, by the joint recursion. -/
def env : (Γ : Ctx) → Env Γ :=
  Ctx.rec (motive := fun Γ => Env Γ) (motive_2 := fun Γ A => (ρ : Env Γ) → El Γ A ρ)
    PUnit.unit
    (fun _ _ ρ a => ⟨ρ, a ρ⟩)
    (fun _ _ _ => 0)
    (fun _ _ _ _ _ ihB ρ => fun a => ihB ⟨ρ, a⟩)

example : env Ctx.nil = PUnit.unit := rfl
example (Γ : Ctx) (A : Ty Γ) : (env (Ctx.ext Γ A)).1 = env Γ := rfl

example (Γ : Ctx) : True := by cases Γ <;> trivial
example (Γ : Ctx) (A : Ty Γ) : True := by cases A <;> trivial

/-- info: 'CtxTy.env' does not depend on any axioms -/
#guard_msgs in
#print axioms env

end CtxTy

/-! ## A decoder into values, and an index a decoder computes

`size` is a decoder into `Nat`; `Path` is indexed by a `Code` and by a `Nat`
that its constructors fill with `size` of their fields. -/

namespace ByValue

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

example (a b : Code) : size (Code.pair a b) = size a + size b := rfl
example (a b : Code) (p : Path a (size a)) :
    depth (Code.pair a b) (size a + size b) (Path.left a b p) = depth a (size a) p + 1 := rfl
example : size (Code.pair Code.one Code.one) = 2 := rfl
example : depth _ _ (Path.left Code.one Code.one (Path.stop Code.one)) = 1 := rfl

/-- info: 'ByValue.depth_left' does not depend on any axioms -/
#guard_msgs in
#print axioms depth_left

end ByValue

/-! ## Universe polymorphism, parameters, and an infinitary field at a built index -/

namespace Poly
universe u

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

example (X : Type u) (Γ : Ctx X) (A : Ty X Γ) (B : El X Γ A → Ty X (Ctx.ext Γ A)) :
    El X Γ (Ty.pi Γ A B) = ((a : El X Γ A) → El X (Ctx.ext Γ A) (B a)) := rfl

/-- info: 'Poly.El_pi' does not depend on any axioms -/
#guard_msgs in
#print axioms El_pi

end Poly

/-! ## Constructors written with a dot -/

namespace Dotted

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

example (Γ : Ctx) (A : Ty Γ) (g : Nat → Ty (Ctx.ext Γ A)) :
    El Γ (Ty.many Γ A g) = ((n : Nat) → El (Ctx.ext Γ A) (g n)) := rfl

example (Γ : Ctx) (A : Ty Γ) : True := by
  induction A with
  | base _ => trivial
  | many _ _ _ ihA ihg => trivial

end Dotted

/-! ## No carrier in any arity

`Vec` is indexed by a `Nat` only, so the graph block is a plain mutual family
and Lean declares it; its recursor is a kernel recursor of a mutual family,
which the code generator does not compile, so `Vec.rec` and what is defined
through it are `noncomputable`. -/

namespace Plain

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

example (n : Nat) (a : Code) (v : Vec n) : Env (n + 1) (Vec.cons n a v) = (El a × Env n v) := rfl

noncomputable def len (n : Nat) (v : Vec n) : Nat :=
  Vec.rec (motive := fun _ _ => Nat) (motive_2 := fun _ => Unit)
    0 (fun _ _ _ _ ih => ih + 1) () (fun _ _ _ => ()) v

example : len 2 (Vec.cons 1 Code.one (Vec.cons 0 Code.one Vec.nil)) = 2 := rfl
example (n : Nat) (v : Vec n) : True := by
  induction v with
  | nil => trivial
  | cons _ _ _ ih => trivial

/-- info: 'Plain.len' does not depend on any axioms -/
#guard_msgs in
#print axioms len

end Plain

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

namespace Rejected

-- an index domain has to be a carrier applied outright
reject_ir "applied to its indices" in
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

-- an index built out of a function field applied to a binder is one the
-- erasure underneath cannot delete
reject_ir "recurses under the index" in
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

end Rejected
