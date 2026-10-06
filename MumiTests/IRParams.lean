import MumiTests.Spec.Harness

/-!
# Parameters and universes: implicit, non-uniform, `Sort`

* A carrier's parameter may be implicit, `inductive U {α : Type}`, as Lean
  allows of any inductive: the type takes it implicitly, and so does every
  public declaration.
* A parameter may vary, `wrap (u : U (List α)) : U α`.  Lean 4 refuses this; it
  is sound, as in Coq: the parameter is an index, bound implicitly by each
  constructor and each minor premise, and the recursor's motive takes it.  One universe up it costs
  nothing; at the written universe a carrier records its indices, so one of
  type `Type` needs a carrier in `Type 1`.
* `Sort (u+1)` is `Type u`.  `Sort u` is refused, as Lean refuses it: at `u = 0`
  the carrier would be a proposition, and a decoder into a type would tell
  equal proofs apart.

`mumi_spec` checks each block's declarations and rules; what follows a block is
what that leaves out.
-/

set_option autoImplicit false

/-! ## An implicit parameter of the type -/

namespace ImplicitType
set_option mumi.mahlo false

mumi_spec (xfail := [injEq])
mutual
inductive U {α : Type} : Type where
  | base : U
  | pi (a : U) (b : El a → U) : U
def El {α : Type} : U (α := α) → Type
  | .base => α
  | .pi a b => (x : El a) → El (b x)
end

example : El (α := Nat) .base = Nat := rfl
def depth {α : Type} (t : U (α := α)) : Nat := U.rec 0 (fun _ _ ih _ => ih + 1) t
example (a : U (α := Nat)) (b : El a → U) : depth (.pi a b) = depth a + 1 := rfl

end ImplicitType

namespace ImplicitTypeLower
set_option mumi.mahlo true
set_option maxRecDepth 8000

mumi_spec (xfail := [injEq])
mutual
inductive U {α : Type} : Type where
  | base : U
  | pi (a : U) (b : El a → U) : U
def El {α : Type} : U (α := α) → Type
  | .base => α
  | .pi a b => (x : El a) → El (b x)
end

example : El (α := Nat) .base = Nat := rfl
def depth {α : Type} (t : U (α := α)) : Nat := U.rec 0 (fun _ _ ih _ => ih + 1) t
example (a : U (α := Nat)) (b : El a → U) : depth (.pi a b) = depth a + 1 := rfl

end ImplicitTypeLower

/-! ## A parameter that varies -/

namespace NonUniform
set_option mumi.mahlo false

mumi_spec (xfail := [injEq])
mutual
inductive U (α : Type) : Type where
  | atom (a : α) : U α
  | wrap (u : U (List α)) : U α
  | pi (a : U α) (b : El α a → U α) : U α
def El (α : Type) : U α → Type
  | .atom a => α
  | .wrap u => El (List α) u
  | .pi a b => (x : El α a) → El α (b x)
end

example : El Nat (.wrap (.atom [1, 2])) = List Nat := rfl
-- the parameter that varies is an implicit field of each minor premise
def size : {α : Type} → U α → Nat :=
  @U.rec (fun _ _ => Nat) (fun _ => 1) (fun _ ih => ih + 1) (fun _ _ ih _ => ih + 1)
example (α : Type) (u : U (List α)) : size (.wrap u) = size u + 1 := rfl
example : size (U.wrap (U.wrap (U.atom [[(3 : Nat)]]))) = 3 := rfl

end NonUniform

-- a small parameter varies at the written universe as well
namespace NonUniformSmall
set_option mumi.mahlo true
set_option maxRecDepth 8000

mumi_spec (xfail := [injEq])
mutual
inductive T (n : Nat) : Type where
  | leaf : T n
  | up (t : T (n + 1)) : T n
  | arr (a : T n) (b : D n a → T n) : T n
def D (n : Nat) : T n → Type
  | .leaf => Fin (n + 1)
  | .up t => D (n + 1) t
  | .arr a b => (x : D n a) → D n (b x)
end

def height : {n : Nat} → T n → Nat :=
  @T.rec (fun _ _ => Nat) (fun {_} => 0) (fun _ ih => ih + 1) (fun _ _ ih _ => ih)
example (n : Nat) (t : T (n + 1)) : height (.up t) = height t + 1 := rfl

end NonUniformSmall

-- `α : Type` varies at the written universe: the carrier records it, so it is in `Type 1`
namespace NonUniformLower
set_option mumi.mahlo true
set_option maxRecDepth 8000

mumi_spec (xfail := [injEq])
mutual
inductive U (α : Type) : Type 1 where
  | atom (a : α) : U α
  | wrap (u : U (List α)) : U α
def El (α : Type) : U α → Type
  | .atom a => α
  | .wrap u => El (List α) u
end

end NonUniformLower

/--
error: The parameter `α` of `U` varies (it is `List α` in `U.wrap`), so it is an index, which a value of `U` at the written universe records: `U` has to be declared in `Type 1` to hold a `Type`
-/
#guard_msgs in
set_option mumi.mahlo true in
mutual
inductive U (α : Type) : Type where
  | atom (a : α) : U α
  | wrap (u : U (List α)) : U α
def El (α : Type) : U α → Type
  | .atom a => α
  | .wrap u => El (List α) u
end

-- varying beside a uniform one, with an instance and a nested occurrence at a
-- closed index
namespace NonUniformMixed
set_option mumi.mahlo false

mumi_spec (simp := [U.rec_many]) (xfail := [recOn, casesOn, injEq, axioms])
mutual
inductive U (β : Type) [Inhabited β] (n : Nat) : Type where
  | here (b : β) : U β n
  | deeper (u : U β (n + 1)) : U β n
  | many (us : List (U β 0)) : U β n
def El (β : Type) [Inhabited β] (n : Nat) : U β n → Type
  | .here b => Fin (n + 1)
  | .deeper u => El β (n + 1) u
  | .many us => Els β us
def Els (β : Type) [Inhabited β] : List (U β 0) → Type
  | [] => Unit
  | u :: us => El β 0 u × Els β us
end

example (u : U Nat 1) : El Nat 0 (.deeper u) = El Nat 1 u := rfl
example (u : U Nat 0) : El Nat 3 (.many [u]) = (El Nat 0 u × Unit) := rfl

end NonUniformMixed

-- nesting at an index that varies would need a copy indexed by it
/--
error: IR prototype does not yet take a nested occurrence whose arguments name a field or an index, as `n` here (a parameter that varies is an index)
-/
#guard_msgs in
set_option mumi.mahlo false in
mutual
inductive V (n : Nat) : Type where
  | deeper (v : V (n + 1)) : V n
  | many (vs : List (V n)) : V n
def VEl (n : Nat) : V n → Type
  | .deeper v => VEl (n + 1) v
  | .many vs => Unit
end

/-! ## `Sort` -/

namespace SortSucc
set_option mumi.mahlo false
universe u

mumi_spec (xfail := [casesOn, injEq])
mutual
inductive U : Sort (u + 1) where
  | base : U
  | pi (a : U) (b : El a → U) : U
def El : U → Sort (u + 1)
  | .base => PUnit
  | .pi a b => (x : El a) → El (b x)
end

end SortSucc

/--
error: An IR carrier in `Sort w` would be a proposition at `w = 0`, where a decoder into a type would tell equal proofs apart; declare it in `Type u` (or `Sort (u+1)`), or in `Prop` without a decoder
-/
#guard_msgs in
universe w in
mutual
inductive Bad : Sort w where
  | a : Bad
  | b : Bad
def BadEl : Bad → Type
  | .a => Nat
  | .b => Bool
end
