/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Init.Data.Repr

/-!
# What the encoding refers to at run time

A data member of an induction-inductive block is a wrapper around its pre-type,
and a class instance for the wrapper is the pre-type's instance read through the
wrapper's `.val`.  `Subtype` has those instances in core.  A wrapper this
library declares per member has to be given them, and giving each one directly
as an `Expr` would be a term of build code apiece for something that says the
same thing every time.

So they are three functions here instead, and an emitted instance is one
application of one of them.  Nothing here knows what an induction-inductive
block is: each takes the map down to the underlying type, and, where the class
needs to go back the other way, the proof that the map loses nothing.
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

/--
Decide `a = b` by deciding `f a = f b`, which settles it when `f` loses nothing.
This is the `DecidableEq` that `Subtype` has, with `f` its `.val` and `ext` its
`Subtype.ext`.
-/
def decEqOfVal {α : Sort u} {β : Sort v} [DecidableEq β] (f : α → β)
    (ext : ∀ {a b : α}, f a = f b → a = b) : DecidableEq α := fun a b =>
  if h : f a = f b then isTrue (ext h) else isFalse fun e => h (congrArg f e)

end Mumi
