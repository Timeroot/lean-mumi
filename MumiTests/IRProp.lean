import MumiTests.Spec.Harness

/-!
# A `Prop` in the block

A decoder may land in `Prop`, and a constructor may take a proof of it as a
field: `Inh : U → Prop` is recursive with `U` and `El`, and `U.pi` asks for
`Inh a`.  A `Prop` inductive may sit in the same `mutual` as well: `Good` is
indexed by `U` and reads `El` and `Inh`, and `Fine` is mutual with it.  Such a
member is not part of the induction-recursion -- nothing is defined by
recursion on a proof -- so it is declared right after the block it refers to,
in both modes; one the block's carriers or decoders mention is part of the
induction-recursion, which `IRPropSCC.lean` covers.  `mumi_spec` checks each
block, the `Prop` members' joint recursor included; what follows is what that
leaves out.
-/

set_option autoImplicit false

namespace PropUpper
set_option mumi.mahlo false

mumi_spec (xfail := [rec, recOn, casesOn, injEq])
mutual
inductive U : Type where
  | base : U
  | pi (a : U) (b : El a → U) (h : Inh a) : U
inductive Good : U → Prop where
  | base : Good .base
  | pi (a : U) (b : El a → U) (h : Inh a) (ha : Good a) (hb : ∀ x, Fine (b x)) : Good (.pi a b h)
inductive Fine : U → Prop where
  | base : Fine .base
  | pi (a : U) (b : El a → U) (h : Inh a) (ha : Good a) (hb : ∀ x, Fine (b x)) : Fine (.pi a b h)
def El : U → Type
  | .base => Nat
  | .pi a b h => (x : El a) → El (b x)
def Inh : U → Prop
  | .base => True
  | .pi a b h => ∀ x : El a, Inh (b x)
end

/-- A certified code is inhabited, by the joint recursor of the two `Prop`s
(`induction` does not take a mutual inductive). -/
theorem Good.inh (u : U) (g : Good u) : Inh u :=
  Good.rec (motive_1 := fun u _ => Inh u) (motive_2 := fun u _ => Inh u)
    trivial (fun _ _ _ _ _ _ ihb => fun x => ihb x)
    trivial (fun _ _ _ _ _ _ ihb => fun x => ihb x) g

theorem Fine.inh (u : U) (f : Fine u) : Inh u :=
  Fine.rec (motive_1 := fun u _ => Inh u) (motive_2 := fun u _ => Inh u)
    trivial (fun _ _ _ _ _ _ ihb => fun x => ihb x)
    trivial (fun _ _ _ _ _ _ ihb => fun x => ihb x) f

example : Good (U.pi U.base (fun _ => U.base) trivial) :=
  .pi _ _ _ .base (fun _ => Fine.base)

/-- info: 'PropUpper.Good.inh' does not depend on any axioms -/
#guard_msgs in
#print axioms Good.inh

end PropUpper

namespace PropLower
set_option mumi.mahlo true

mumi_spec (xfail := [rec, recOn, casesOn, injEq])
mutual
inductive U : Type where
  | base : U
  | pi (a : U) (b : El a → U) (h : Inh a) : U
inductive Good : U → Prop where
  | base : Good .base
  | pi (a : U) (b : El a → U) (h : Inh a) (ha : Good a) (hb : ∀ x, Fine (b x)) : Good (.pi a b h)
inductive Fine : U → Prop where
  | base : Fine .base
  | pi (a : U) (b : El a → U) (h : Inh a) (ha : Good a) (hb : ∀ x, Fine (b x)) : Fine (.pi a b h)
def El : U → Type
  | .base => Nat
  | .pi a b h => (x : El a) → El (b x)
def Inh : U → Prop
  | .base => True
  | .pi a b h => ∀ x : El a, Inh (b x)
end

theorem Good.inh (u : U) (g : Good u) : Inh u :=
  Good.rec (motive_1 := fun u _ => Inh u) (motive_2 := fun u _ => Inh u)
    trivial (fun _ _ _ _ _ _ ihb => fun x => ihb x)
    trivial (fun _ _ _ _ _ _ ihb => fun x => ihb x) g

theorem Fine.inh (u : U) (f : Fine u) : Inh u :=
  Fine.rec (motive_1 := fun u _ => Inh u) (motive_2 := fun u _ => Inh u)
    trivial (fun _ _ _ _ _ _ ihb => fun x => ihb x)
    trivial (fun _ _ _ _ _ _ ihb => fun x => ihb x) f

-- a closed code: `Inh U.base` is `True` by the equation, not by normalisation
example : Good (U.pi U.base (fun _ => U.base) (cast (Inh_base).symm trivial)) :=
  .pi _ _ _ .base (fun _ => Fine.base)

/-- A proof-carrying consumer runs. -/
def depth : U → Nat :=
  U.rec 0 (fun _ _ _ ih _ => ih + 1)

/-- info: 1 -/
#guard_msgs in
#eval depth (U.pi U.base (fun _ => U.base) (cast (Inh_base).symm trivial))

/-- info: 'PropLower.Good.inh' depends on axioms: [IR.mahlo] -/
#guard_msgs in
#print axioms Good.inh

end PropLower
