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

The kernel specialises the nesting type constructor to the block -- here copying
`Nonempty` at `T` -- and checks the enlarged block.  This is why `T.rec` has a
motive for the nesting type as well as for `T`.

The enlarged block is mutual and so must be homogeneous, but the copy of
`Nonempty T` is in `Prop` while `T` is in `Type`.  The kernel rejects the
declaration with the "must belong to the same type universe" error, about a
block the user never wrote.

`Mumi.Denest` builds the enlarged block at the elaborator level and
`Mumi.Lowering` lowers it.  This module is the trigger.

Denesting can also produce an *induction-inductive* block, when the nesting type
is a family indexed by another type being copied.  `Mumi.IndInd` handles that
when the induction-induction runs only through `Prop`:

```lean
inductive RecWFTree where
  | mk (x : WFTree RecWFTree)   -- `WFTree α := { t : Tree α // t.WF }`, roughly
```

Copying `WFTree` at `RecWFTree` drags in `Tree`, `Tree.WF` and `Tree.WFWith`;
the last two are indexed by the copy of `Tree`.

## Why catch-and-retry

Nested inductives that already work belong to the kernel, whose denesting is
trusted and carries its own `rec`, `below`, `brecOn` and `sizeOf` handling.  So
Lean decides whether a declaration is one of ours, and we act only after it
fails.  See `Mumi.Rescue`.

## The gate

Each retry requires an enlarged block that Lean could not have handled.
`IndInd.elabNestedInductive` requires denesting to add a member, and then the
block to be induction-inductive, or a copy to have taken a field of its
constructor as an index.  `elabHeterogeneousInductive` with
`requireHeterogeneous` requires members in more than one universe, or such a
field.  A denested block that is homogeneous, not induction-inductive and
indexed only at closed parameters is one the kernel would have accepted, so its
failure was genuine.

## Why there are three retries

The two gates overlap on the constructor-field case.  `Mumi.IndInd` states the
block over the original nesting types, `Pair2 R n m` rather than
`R.nested_Pair2_1 n m`, which lowering never does; but its bridge can fail, and
a block with the copies visible is worse than the same block lowered, which at
least relates the two by `eq_orig`.  So `requireBridge` asks for the good case
first, lowering takes the block if that declines, and the third retry repeats
the first route without the bridge.

The third retry also drops `requireDeriving`.  An unhonoured `deriving` clause
is a logged error, and a logged error is how a route declines -- correct while
another route might still honour it.  By the third retry there is none, so what
could not be derived becomes a warning instead of losing the block.
-/

public section

open Lean Lean.Elab Lean.Elab.Command

namespace Mumi

/-- Elaborate a declaration with Lean's own `elabDeclaration`. -/
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
      IndInd.elabNestedInductive #[stx] (requireDeriving := false))]

end Mumi
