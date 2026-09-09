/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Lean.Exception
public import Lean.Message

/-!
# Marking an error as being about a block we recognised

`Mumi.Rescue` reports Lean's error and not the errors from its retries.  A
failed retry almost always ran on a block that was never ours, so reporting it
would be a guess.

Some failures are the other way round.  A block can be induction-inductive and
still lie outside the class this library encodes.  Lean's own error is then
about the enlarged block it could not build, which is true but unhelpful.  An
error thrown through `owning` carries a tag saying so, and `Mumi.Rescue.rescuing`
reports tagged errors next to Lean's.

This is a separate module because the two sides of the tag are in different
compilation phases: `rescuing` is `meta`, the checks that raise a marked error
are not, and one module cannot have a declaration of each phase reach the other.
-/

public section

namespace Mumi

open Lean

/-- The tag that marks an error as one about a block this library recognised. -/
def ownedTag : Name := `Mumi.owned

/-- Mark every error `k` throws as one about a block this library recognised. -/
def owning {m : Type → Type} [MonadExcept Exception m] {α} (k : m α) : m α :=
  tryCatch k fun
    | .error ref msg => throw (.error ref (.tagged ownedTag msg))
    | ex => throw ex

/-- Was this error marked by `Mumi.owning`? -/
def isOwned (msg : MessageData) : Bool := msg.hasTag (· == ownedTag)

end Mumi
