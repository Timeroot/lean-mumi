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

`Mumi.Rescue` reports the error Lean gave and not the ones its retries gave,
because a retry that fails has almost always failed on a block that was never
ours, and saying otherwise would be a guess dressed up as a diagnosis.

Some failures are the other way round.  A block really can be an
induction-inductive one and still be outside the narrow class that can be
encoded; Lean's own error is then about the enlarged block it could not build,
which is true and beside the point.  An error thrown through `owning` carries a
tag saying so, and `Mumi.Rescue.rescuing` reports those next to Lean's rather
than only in the trace.

This lives in a module of its own because the two sides of the tag are in
different compilation phases: `rescuing` is `meta`, the checks that raise a
marked error are not, and neither phase may reach a declaration of the other
within a single module.
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
