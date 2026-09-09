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
# Taking over `mutual`

Importing this module makes `mutual` accept inductive blocks whose members live
in different universes.  Nothing else about `mutual` changes.

A `@[command_elab]` registered downstream runs *before* the builtin one, because
`Lean.KeyedDeclsAttribute` prepends.  `throwUnsupportedSyntax` hands the block
back to the builtin and rolls back any state the override touched.  So the
elaborator below is a filter: it either lowers the block or steps aside.

It steps aside for everything except a block of plain `inductive` declarations.
`mutual def`, `structure`, `class` and `coinductive` blocks reach the same Lean
code as before and keep their incremental elaboration.

A block of plain `inductive`s is lowered if `Lean.Elab.Command.checkHeaders`
would reject its headers for living in several universes.  Otherwise it goes to
Lean's `elabMutual`, and if that fails it is retried as an induction-inductive
block, which is the only way a homogeneous `mutual` whose members nest can
succeed.  `Mumi.Rescue` says why the retry waits for Lean to fail.

Set `mumi.enabled` to `false` to step aside unconditionally.
-/

public section

open Lean Lean.Elab Lean.Elab.Command

namespace Mumi

/-- Elaborate a `mutual` block whose inductive members are not all in one
universe; defer to Lean's own elaborator for every other block. -/
@[command_elab Lean.Parser.Command.«mutual»]
meta def elabMutualHeterogeneous : CommandElab := fun stx => do
  unless mumi.enabled.get (← getOptions) do
    throwUnsupportedSyntax
  let elems := stx[1].getArgs
  let route ← classifyBlock elems
  if route == .stock then
    -- anything else keeps its incremental elaboration, and `mutual def` needs it
    unless elems.all (·[1].getKind == ``Lean.Parser.Command.«inductive») do
      throwUnsupportedSyntax
    -- a block Lean rejects may still be one whose members nest into each other,
    -- which denesting makes induction-inductive; or one whose nesting is applied
    -- to a constructor-local, which `Mumi.Denest` handles by making the local an
    -- index; or an induction-induction that reached here only because its members
    -- shadow globals of the same name, so its arities elaborated against those
    -- and `classifyBlock` saw nothing to route on
    rescuing (elabMutual stx)
      #[("the induction-inductive retry", IndInd.elabNestedInductive elems),
        ("lowering the denested block",
          elabHeterogeneousInductive elems (requireHeterogeneous := true)),
        ("the induction-inductive retry, with the members shadowing the globals",
          IndInd.elabInductionInductive elems (requireIndInd := true)
            (requireDeriving := false))]
    return
  withExporting (isExporting := (← getScope).isPublic) do
  withoutCommandIncrementality true do
    match route with
    | .indind =>
      -- the bridge that hides what an induction-inductive block denested into is
      -- all or nothing, so a declaration the kernel rejects must be rejected
      -- here; otherwise `addDecl` checks in a background task and the error
      -- surfaces after the point where rollback was possible
      withScope (fun sc => { sc with opts := Elab.async.set sc.opts false }) do
        discardingInfoOnError (IndInd.elabInductionInductive elems)
    | _ =>
      rescuing (elabHeterogeneousInductive elems)
        #[("the induction-inductive retry", IndInd.elabInductionInductive elems)]

end Mumi
