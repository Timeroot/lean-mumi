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
example : Good u1 := .pi _ _ _ trivial (fun _ => .base)

/-- info: 1 -/
#guard_msgs in
#eval depth u1

/-- info: 'PropSCC.Good.inh' does not depend on any axioms -/
#guard_msgs in
#print axioms Good.inh

end PropSCC

/-! At the written universe this is not taken yet, and says so. -/

namespace PropSCCLower
set_option mumi.mahlo true

/--
error: The `Prop` member `Good` is not lowered at the universe the block is written at yet; one universe up, `set_option mumi.mahlo false`, it is
-/
#guard_msgs in
mutual
inductive U : Type where
  | base : U
  | pi (a : U) (b : El a → U) (h : Good a) : U
inductive Good : U → Prop where
  | base : Good .base
  | pi (a : U) (b : El a → U) (h : Good a) (hb : ∀ x : El a, Good (b x)) : Good (.pi a b h)
def El : U → Type
  | .base => Nat
  | .pi a b h => (x : El a) → El (b x)
end

end PropSCCLower
