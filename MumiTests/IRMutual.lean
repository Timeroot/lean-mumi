import MumiTests.Spec.Harness

/-!
# Mutual carriers, and functions over them in the same block

Two carriers in one recursion, their decoders, and functions into the
decoders' values beside them -- `default`, `measure` -- as one block.  `mumi_spec`
checks every declaration and equation; what follows is what that leaves out.
-/

set_option maxRecDepth 6000

namespace IRMutualUpper
set_option mumi.mahlo false

mumi_spec (xfail := [casesOn, injEq])
mutual
  inductive Ty : Type where
    | base : Ty
    | pi (a : Ty) (b : El a → Ty) : Ty
    | record (g : Ctx) : Ty
  inductive Ctx : Type where
    | empty : Ctx
    | extend (g : Ctx) (a : Env g → Ty) : Ctx
  def El : Ty → Type
    | .base => Nat
    | .pi a b => (x : El a) → El (b x)
    | .record g => Env g
  def Env : Ctx → Type
    | .empty => PUnit
    | .extend g a => (x : Env g) × El (a x)
  def default : (a : Ty) → El a
    | .base => (0 : Nat)
    | .pi a b => fun x => default (b x)
    | .record g => defaultEnv g
  def defaultEnv : (g : Ctx) → Env g
    | .empty => PUnit.unit
    | .extend g a => ⟨defaultEnv g, default (a (defaultEnv g))⟩
  def measure : Ty → Nat
    | .base => 1
    | .pi a b => measure a + measure (b (default a)) + 1
    | .record g => measureCtx g + 1
  def measureCtx : Ctx → Nat
    | .empty => 0
    | .extend g a => measureCtx g + measure (a (defaultEnv g)) + 1
end

noncomputable def exampleCtx : Ctx := Ctx.extend Ctx.empty (fun _ => Ty.base)
example : measureCtx exampleCtx = 2 := by
  rw [exampleCtx, measureCtx_extend, measureCtx_empty, measure_base]
example (a : Ty) : True := by
  cases a <;> trivial
example (g : Ctx) : True := by
  cases g <;> trivial

end IRMutualUpper

namespace IRMutualLower
set_option mumi.mahlo true

mumi_spec (xfail := [casesOn, injEq])
mutual
  inductive Ty : Type where
    | base : Ty
    | pi (a : Ty) (b : El a → Ty) : Ty
    | record (g : Ctx) : Ty
  inductive Ctx : Type where
    | empty : Ctx
    | extend (g : Ctx) (a : Env g → Ty) : Ctx
  def El : Ty → Type
    | .base => Nat
    | .pi a b => (x : El a) → El (b x)
    | .record g => Env g
  def Env : Ctx → Type
    | .empty => PUnit
    | .extend g a => (x : Env g) × El (a x)
  def default : (a : Ty) → El a
    | .base => (0 : Nat)
    | .pi a b => fun x => default (b x)
    | .record g => defaultEnv g
  def defaultEnv : (g : Ctx) → Env g
    | .empty => PUnit.unit
    | .extend g a => ⟨defaultEnv g, default (a (defaultEnv g))⟩
  def measure : Ty → Nat
    | .base => 1
    | .pi a b => measure a + measure (b (default a)) + 1
    | .record g => measureCtx g + 1
  def measureCtx : Ctx → Nat
    | .empty => 0
    | .extend g a => measureCtx g + measure (a (defaultEnv g)) + 1
end

def exampleCtx : Ctx := Ctx.extend Ctx.empty (fun _ => Ty.base)
example : measureCtx exampleCtx = 2 := by
  rw [exampleCtx, measureCtx_extend, measureCtx_empty, measure_base]

/-- info: 2 -/
#guard_msgs in
#eval measureCtx exampleCtx

example (a : Ty) : True := by
  cases a <;> trivial
example (g : Ctx) : True := by
  cases g <;> trivial

end IRMutualLower

example (a : IRMutualLower.Ty) : True := by
  induction a using IRMutualLower.Ty.rec (motive_2 := fun _ => True) <;> trivial

example (g : IRMutualUpper.Ctx) : True := by
  induction g using IRMutualUpper.Ctx.rec (motive_1 := fun _ => True) <;> trivial
