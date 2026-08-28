/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public meta import Mumi.Options
public meta import Mumi.Elab

/-!
# Taking over `mutual`

Importing this module makes `mutual` accept inductive blocks whose members live
in different universes.  Nothing else about `mutual` changes.

The mechanism is that a `@[command_elab]` registered downstream is tried
*before* the builtin one -- `Lean.KeyedDeclsAttribute` prepends -- and
`throwUnsupportedSyntax` hands the block back to the builtin, with any state the
override touched rolled back.  So the elaborator below is a filter: it looks at
the block, and either lowers it or steps aside.

It steps aside for everything except a block of two or more plain `inductive`
declarations whose headers `Lean.Elab.Command.checkHeaders` would reject for
living in several universes.  In particular `mutual def`, `structure`, `class`,
`coinductive`, and every homogeneous inductive block are elaborated by Lean
exactly as they were before, by the same code as before.

Set `mumi.enabled` to `false` to step aside unconditionally.
-/

public section

open Lean Lean.Elab Lean.Elab.Command

namespace Mumi

/--
Elaborates a `mutual` block whose inductive members are not all in one universe,
and defers to Lean's own elaborator for every other block.
-/
@[command_elab Lean.Parser.Command.«mutual»]
meta def elabMutualHeterogeneous : CommandElab := fun stx => do
  unless mumi.enabled.get (← getOptions) do
    throwUnsupportedSyntax
  let elems := stx[1].getArgs
  let route ← classifyBlock elems
  if route == .stock then
    throwUnsupportedSyntax
  withExporting (isExporting := (← getScope).isPublic) do
  withoutCommandIncrementality true do
    match route with
    | .indind => IndInd.elabInductionInductive elems
    | _ => elabHeterogeneousInductive elems

end Mumi
