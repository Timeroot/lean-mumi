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

universe u v

/-- Show `a` as whatever `f a` shows as.  This is the `Repr` that `Subtype` has. -/
@[instance_reducible]
def reprOfVal {α : Type u} {β : Type v} [Repr β] (f : α → β) : Repr α where
  reprPrec a := reprPrec (f a)

/-- Hash `a` as `f a` hashes.  This is the `Hashable` that `Subtype` has. -/
@[instance_reducible]
def hashableOfVal {α : Type u} {β : Type v} [Hashable β] (f : α → β) : Hashable α where
  hash a := hash (f a)

/-- Decide `a = b` by deciding `f a = f b`, which is valid when `f` is injective.
This is the `DecidableEq` that `Subtype` has, with `f` its `.val` and `ext` its
`Subtype.ext`. -/
def decEqOfVal {α : Sort u} {β : Sort v} [DecidableEq β] (f : α → β)
    (ext : ∀ {a b : α}, f a = f b → a = b) : DecidableEq α := fun a b =>
  if h : f a = f b then isTrue (ext h) else isFalse fun e => h (congrArg f e)

end Mumi
