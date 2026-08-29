/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public meta import Mumi.Options
public meta import Mumi.Elab
public meta import Lean.Message
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
to declarations that were perfectly fine.  Deciding up front whether a given
inductive is one Lean can handle means reimplementing the kernel's positivity
and universe analysis, and being wrong in either direction is bad: too eager and
we take over working declarations, too shy and we miss the ones we exist for.

Letting Lean answer the question is exact, and costs nothing on the path that
matters -- a declaration Lean accepts is elaborated once, by Lean, and we never
run.  Only a declaration that was going to be an error anyway is elaborated
twice.

## The gate

Failure alone is not enough of a reason to take over: an inductive can fail for
any number of reasons that are nothing to do with us, and we must not "rescue"
one by quietly building a different declaration.

So each retry is gated on the enlarged block being one Lean could not have
handled.  The first runs with `requireHeterogeneous`, which lowers the block
only if denesting it yields members in more than one universe.  The second,
`Mumi.IndInd.elabNestedInductive`, requires denesting to produce at least one
new member *and* the enlarged block to be induction-inductive.  Both conditions
are ones Lean cannot be in: if the denested block were homogeneous and not
induction-inductive, the kernel would have handled it, so the failure was a real
one.  When both gates reject, or both retries fail for any other reason, the
original error is reported and every trace of the retries is dropped.
-/

public section

open Lean Lean.Elab Lean.Elab.Command

namespace Mumi

/-- Has an error been logged since the log had `n` messages in it? -/
private meta def errorLoggedSince (n : Nat) : CommandElabM Bool := do
  let msgs := (← get).messages.reportedPlusUnreported
  return (msgs.toList.drop n).any (·.severity matches .error)

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
  let saved ← get
  let nmsgs := saved.messages.reportedPlusUnreported.size
  let stockEx? ←
    try
      elabDeclaration stx
      pure none
    catch ex =>
      pure (some ex)
  if stockEx?.isNone && !(← errorLoggedSince nmsgs) then
    return
  -- Lean rejected it; see whether it is one of ours
  let stockState ← get
  let attempt (k : CommandElabM Unit) : CommandElabM Bool := do
    set saved
    try
      withExporting (isExporting := (← getScope).isPublic) do
      withoutCommandIncrementality true do
        k
      if ← errorLoggedSince nmsgs then
        throwError "the rescued declaration did not elaborate"
      return true
    catch _ =>
      return false
  -- denesting either makes the block heterogeneous, which `Mumi.Lowering`
  -- takes, or induction-inductive, which `Mumi.IndInd` takes
  if ← attempt (elabHeterogeneousInductive #[stx] (requireHeterogeneous := true)) then
    return
  if ← attempt (IndInd.elabNestedInductive #[stx]) then
    return
  -- not ours, or ours and broken: report exactly what Lean reported
  set stockState
  match stockEx? with
  | some ex => throw ex
  | none    => pure ()

end Mumi
