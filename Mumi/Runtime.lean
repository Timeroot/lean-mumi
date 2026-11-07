/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Init.Data.Repr

/-!
# What the encoding refers to at run time

A data member of an induction-inductive block is a wrapper around its pre-type.
A class instance for the wrapper is the pre-type's instance read through the
wrapper's `.val`, which is how `Subtype` gets its instances in core.  Building
each such instance directly as an `Expr` would repeat the same term per class.

These three functions replace that: an emitted instance is one application of
one of them.  Each takes the map down to the underlying type, and, where the
class must also go back, a proof that the map is injective.
-/

public section

namespace Mumi

/-- `Nat.beq_refl`, which core proves by `simp` at the cost of `propext`. -/
theorem beq_self : (n : Nat) → Nat.beq n n = true
  | 0 => rfl
  | n + 1 => beq_self n

/-- What `X.noConfusionType` is between two terms of one constructor, from the same thing
in the case the indices are not yet known to agree. -/
@[reducible] def condOfEq.{w} {C P : Sort w} {i j : Nat} (h : i = j) (c : C) :
    cond (Nat.beq i j) C P :=
  match j, h with
  | _, rfl => @Eq.rec Bool true (fun r _ => cond r C P) c (Nat.beq i i) (beq_self i).symm

/-- Two terms a function sends to different numerals are different. -/
theorem ne_of_ctorIdx.{w} {α : Sort w} (f : α → Nat) {a b : α} {i j : Nat}
    (ha : f a = i) (hb : f b = j) (hne : Nat.beq i j = false) : a ≠ b :=
  fun h => Nat.ne_of_beq_eq_false hne (ha.symm.trans ((congrArg f h).trans hb))

universe u v

/-- Show `a` as whatever `f a` shows as.  This is the `Repr` that `Subtype` has. -/
@[instance_reducible]
def reprOfVal {α : Type u} {β : Type v} [Repr β] (f : α → β) : Repr α where
  reprPrec a := reprPrec (f a)

/-- Hash `a` as `f a` hashes.  This is the `Hashable` that `Subtype` has. -/
@[instance_reducible]
def hashableOfVal {α : Type u} {β : Type v} [Hashable β] (f : α → β) : Hashable α where
  hash a := hash (f a)

/-- Compare `a` and `b` as `f a` and `f b` compare.  This is the `BEq` that `Subtype` has. -/
@[instance_reducible]
def beqOfVal {α : Type u} {β : Type v} [BEq β] (f : α → β) : BEq α where
  beq a b := f a == f b

/-- Order `a` and `b` as `f a` and `f b` are ordered. -/
@[instance_reducible]
def ordOfVal {α : Type u} {β : Type v} [Ord β] (f : α → β) : Ord α where
  compare a b := compare (f a) (f b)

/-- Decide `a = b` by deciding `f a = f b`, which is valid when `f` is injective.
This is the `DecidableEq` that `Subtype` has, with `f` its `.val` and `ext` its
`Subtype.ext`. -/
def decEqOfVal {α : Sort u} {β : Sort v} [DecidableEq β] (f : α → β)
    (ext : ∀ {a b : α}, f a = f b → a = b) : DecidableEq α := fun a b =>
  if h : f a = f b then isTrue (ext h) else isFalse fun e => h (congrArg f e)

/-- Two proofs of equal propositions, with no `propext`: what a rule at a constructor with a proof
over a copy comes to, its index read through a round trip on one side. -/
theorem heq_of_proofs {p q : Prop} (e : p = q) (a : p) (b : q) : HEq a b := by
  subst e
  exact HEq.rfl

/-- A displayed motive at the same index and value by another road. -/
theorem motive_along {α : Sort u} {β : α → Sort v} {R : α → Prop} (M : (a : α) → β a → R a → Prop)
    {a' a : α} (e : a' = a) {v' : β a'} {v : β a} (h : HEq v' v) (r' : R a') (r : R a)
    (p : M a' v' r') : M a v r := by
  subst e
  cases h
  exact p

end Mumi
