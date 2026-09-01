/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public meta import Mumi.Options
public meta import Mumi.Elab
public meta import Mumi.Rescue
public meta import Lean.Elab.Declaration

/-!
# Rescuing a nested inductive

A *nested* inductive mentions itself inside the parameters of another type:

```lean
inductive T : Type where
  | mk1 : T
  | mkT : Nonempty T → T
```

The kernel handles these by specialising the nesting type constructor to the
block -- here making a copy of `Nonempty` at `T` -- and checking the enlarged
block instead.  That is why `T.rec` for a working nested inductive has a motive
for the nesting type as well as for `T`.

The enlarged block is a mutual block, so it has to be homogeneous, and the copy
of `Nonempty T` is a `Prop` while `T` is a `Type`.  So the declaration above is
rejected, with the same "must belong to the same type universe" error a
handwritten heterogeneous `mutual` block gets -- only from the kernel rather
than from the elaborator, and about a block the user never wrote.

`Mumi.Denest` can build that enlarged block at the elaborator level, and
`Mumi.Lowering` can lower it.  This module is the trigger: it lets Lean try
first, and steps in only if Lean fails *and* the enlarged block turns out to be
one we have a lowering for.

Heterogeneity is not the only way denesting can produce a block the kernel
refuses.  If the nesting type is a family indexed by another type being copied,
the enlarged block is *induction-inductive*, and `Mumi.IndInd` handles the case
where the induction-induction runs only through `Prop`:

```lean
inductive RecWFTree where
  | mk (x : WFTree RecWFTree)   -- `WFTree α := { t : Tree α // t.WF }`, roughly
```

Copying `WFTree` at `RecWFTree` drags in `Tree`, `Tree.WF` and `Tree.WFWith`,
and the last two are indexed by the copy of `Tree`.  See `Mumi.IndInd` for the
block that comes out.

## Why catch-and-retry

Nested inductives that work are the kernel's business, and should stay that way:
the kernel's denesting is trusted code with its own `rec`, `below`, `brecOn` and
`sizeOf` handling, and replacing it with ours would be a large, invisible change
to declarations that were perfectly fine.  So we let Lean answer the question of
whether a declaration is one of ours, and step in only if it says no.
`Mumi.Rescue` has the machinery and the rest of the argument.

## The gate

Each retry is gated on the enlarged block being one Lean could not have handled.
`Mumi.IndInd.elabNestedInductive` requires denesting to produce at least one new
member, and then either the enlarged block to be induction-inductive, or a copy
to have taken a field of the constructor it sat in as an index.
`elabHeterogeneousInductive` with `requireHeterogeneous` lowers the block only if
denesting it yields members in more than one universe, or needs such a field.
Both conditions are ones Lean cannot be in: if the denested block were
homogeneous, not induction-inductive and indexed only at closed parameters, the
kernel would have handled it, so the failure was a real one.

## Why there are three retries and not two

The two gates overlap on the constructor-field case, and neither route is better
on all of it.  `Mumi.IndInd` can state the block over the original nesting types
-- `Pair2 R n m` rather than `R.nested_Pair2_1 n m` -- which lowering never does.
But its bridge does not always go through, and a block that comes out of it with
the copies visible is worse than the same block lowered, which at least relates
the two with `eq_orig`.  So the good case is asked for first, by way of
`requireBridge`, lowering gets the block if that is declined, and the third retry
is the same route with the bridge no longer required -- reached only when
lowering will not have the block either.
-/

public section

open Lean Lean.Elab Lean.Elab.Command

namespace Mumi

/--
Elaborates a declaration by handing it to Lean, and, if it is an `inductive`
that Lean rejects and denesting makes heterogeneous, lowers it instead.

Every other declaration -- and every `inductive` Lean accepts -- is elaborated
by Lean's own `elabDeclaration`, unchanged, and this adds nothing to it.
-/
@[command_elab Lean.Parser.Command.declaration]
meta def elabDeclarationRescuingNested : CommandElab := fun stx => do
  unless mumi.enabled.get (← getOptions) do
    throwUnsupportedSyntax
  -- everything that is not a plain `inductive` goes back to Lean untouched, so
  -- that `def`s keep their incremental elaboration
  unless stx[1].getKind == ``Lean.Parser.Command.«inductive» do
    throwUnsupportedSyntax
  -- denesting either makes the block induction-inductive, which `Mumi.IndInd`
  -- takes, or heterogeneous, which `Mumi.Lowering` takes
  rescuing (elabDeclaration stx) #[
    ("the induction-inductive retry, over the originals",
      IndInd.elabNestedInductive #[stx] (requireBridge := true)),
    ("lowering the denested block",
      elabHeterogeneousInductive #[stx] (requireHeterogeneous := true)),
    ("the induction-inductive retry",
      IndInd.elabNestedInductive #[stx])]

end Mumi
