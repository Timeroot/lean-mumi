import Mumi

/-!
# Parameters and universes: implicit, non-uniform, `Sort`

* A carrier's parameter may be implicit, `inductive U {α : Type}`, as Lean
  allows of any inductive: the type takes it implicitly, and so does every
  public declaration.
* A parameter may vary, `wrap (u : U (List α)) : U α`.  Lean 4 refuses this; it
  is sound, as in Coq: the parameter is an index, bound implicitly by each
  constructor, and the recursor's motive takes it.  One universe up it costs
  nothing; at the written universe a carrier records its indices, so one of
  type `Type` needs a carrier in `Type 1`.
* `Sort (u+1)` is `Type u`.  `Sort u` is refused, as Lean refuses it: at `u = 0`
  the carrier would be a proposition, and a decoder into a type would tell
  equal proofs apart.
-/

set_option autoImplicit false

/-! ## An implicit parameter of the type -/

namespace ImplicitType
set_option mumi.mahlo false

mutual
inductive U {α : Type} : Type where
  | base : U
  | pi (a : U) (b : El a → U) : U
def El {α : Type} : U (α := α) → Type
  | .base => α
  | .pi a b => (x : El a) → El (b x)
end

/-- info: ImplicitType.U {α : Type} : Type 1 -/
#guard_msgs in
#check U

/-- info: @U.pi : {α : Type} → (a : U) → (El a → U) → U -/
#guard_msgs in
#check @U.pi

/--
info: @U.rec : {α : Type} →
  {motive : U → Sort u_1} →
    motive U.base → ((a : U) → (b : El a → U) → motive a → ((a_1 : El a) → motive (b a_1)) → motive (a.pi b)) → (t : U) → motive t
-/
#guard_msgs in
#check @U.rec

example : El (α := Nat) .base = Nat := rfl
example (a : U (α := Nat)) (b : El a → U) : El (.pi a b) = ((x : El a) → El (b x)) := rfl
def depth {α : Type} (t : U (α := α)) : Nat := U.rec 0 (fun _ _ ih _ => ih + 1) t
example (a : U (α := Nat)) (b : El a → U) : depth (.pi a b) = depth a + 1 := rfl

end ImplicitType

namespace ImplicitTypeLower
set_option mumi.mahlo true
set_option maxRecDepth 8000

mutual
inductive U {α : Type} : Type where
  | base : U
  | pi (a : U) (b : El a → U) : U
def El {α : Type} : U (α := α) → Type
  | .base => α
  | .pi a b => (x : El a) → El (b x)
end

/-- info: ImplicitTypeLower.U {α : Type} : Type -/
#guard_msgs in
#check U

example : El (α := Nat) .base = Nat := rfl
example (a : U (α := Nat)) (b : El a → U) : El (.pi a b) = ((x : El a) → El (b x)) := rfl
def depth {α : Type} (t : U (α := α)) : Nat := U.rec 0 (fun _ _ ih _ => ih + 1) t
example (a : U (α := Nat)) (b : El a → U) : depth (.pi a b) = depth a + 1 := rfl

end ImplicitTypeLower

/-! ## A parameter that varies -/

namespace NonUniform
set_option mumi.mahlo false

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

/-- info: NonUniform.U (α : Type) : Type 1 -/
#guard_msgs in
#check U

/-- info: @U.wrap : {α : Type} → U (List α) → U α -/
#guard_msgs in
#check @U.wrap

-- the parameter is an index: the motive takes it, each case binds it
/--
info: @U.rec : {motive : (α : Type) → U α → Sort u_1} →
  ((α : Type) → (a : α) → motive α (U.atom a)) →
    ((α : Type) → (u : U (List α)) → motive (List α) u → motive α u.wrap) →
      ((α : Type) →
          (a : U α) → (b : El α a → U α) → motive α a → ((a_1 : El α a) → motive α (b a_1)) → motive α (a.pi b)) →
        {α : Type} → (t : U α) → motive α t
-/
#guard_msgs in
#check @U.rec

example (α : Type) (u : U (List α)) : El α (.wrap u) = El (List α) u := rfl
example : El Nat (.wrap (.atom [1, 2])) = List Nat := rfl
def size : {α : Type} → U α → Nat :=
  @U.rec (fun _ _ => Nat) (fun _ _ => 1) (fun _ _ ih => ih + 1) (fun _ _ _ ih _ => ih + 1)
example (α : Type) (u : U (List α)) : size (.wrap u) = size u + 1 := rfl
example : size (U.wrap (U.wrap (U.atom [[(3 : Nat)]]))) = 3 := rfl

end NonUniform

-- a small parameter varies at the written universe as well
namespace NonUniformSmall
set_option mumi.mahlo true
set_option maxRecDepth 8000

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

/-- info: @T.up : {n : Nat} → T (n + 1) → T n -/
#guard_msgs in
#check @T.up

example (n : Nat) (t : T (n + 1)) : D n (.up t) = D (n + 1) t := D_up n t
def height : {n : Nat} → T n → Nat :=
  @T.rec (fun _ _ => Nat) (fun _ => 0) (fun _ _ ih => ih + 1) (fun _ _ _ ih _ => ih)
example (n : Nat) (t : T (n + 1)) : height (.up t) = height t + 1 := rfl

end NonUniformSmall

-- `α : Type` varies at the written universe: the carrier records it, so it is in `Type 1`
namespace NonUniformLower
set_option mumi.mahlo true
set_option maxRecDepth 8000

mutual
inductive U (α : Type) : Type 1 where
  | atom (a : α) : U α
  | wrap (u : U (List α)) : U α
def El (α : Type) : U α → Type
  | .atom a => α
  | .wrap u => El (List α) u
end

example (α : Type) (u : U (List α)) : El α (.wrap u) = El (List α) u := El_wrap α u

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

-- varying beside a uniform one, with an instance and a nested occurrence
namespace NonUniformMixed
set_option mumi.mahlo false

mutual
inductive U (β : Type) [Inhabited β] (n : Nat) : Type where
  | here (b : β) : U β n
  | deeper (u : U β (n + 1)) : U β n
  | many (us : List (U β n)) : U β n
def El (β : Type) [Inhabited β] (n : Nat) : U β n → Type
  | .here b => Fin (n + 1)
  | .deeper u => El β (n + 1) u
  | .many us => Els β n us
def Els (β : Type) [Inhabited β] (n : Nat) : List (U β n) → Type
  | [] => Unit
  | u :: us => El β n u × Els β n us
end

/-- info: @U.deeper : {β : Type} → [inst : Inhabited β] → {n : Nat} → U β (n + 1) → U β n -/
#guard_msgs in
#check @U.deeper

example (u : U Nat 1) : El Nat 0 (.deeper u) = El Nat 1 u := rfl
example (u : U Nat 0) : El Nat 0 (.many [u]) = (El Nat 0 u × Unit) := rfl

end NonUniformMixed

/-! ## `Sort` -/

namespace SortSucc
set_option mumi.mahlo false
universe u

mutual
inductive U : Sort (u + 1) where
  | base : U
  | pi (a : U) (b : El a → U) : U
def El : U → Sort (u + 1)
  | .base => PUnit
  | .pi a b => (x : El a) → El (b x)
end

/-- info: U : Type (u + 1) -/
#guard_msgs in
#check U.{u}

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
