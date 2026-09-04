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

The mechanism is that a `@[command_elab]` registered downstream is tried
*before* the builtin one -- `Lean.KeyedDeclsAttribute` prepends -- and
`throwUnsupportedSyntax` hands the block back to the builtin, with any state the
override touched rolled back.  So the elaborator below is a filter: it looks at
the block, and either lowers it or steps aside.

It steps aside for everything except a block of plain `inductive` declarations.
In particular `mutual def`, `structure`, `class` and `coinductive` blocks are
elaborated by Lean exactly as they were before, by the same code as before, and
keep their incremental elaboration.

A block of plain `inductive`s is either lowered, if its headers are ones
`Lean.Elab.Command.checkHeaders` would reject for living in several universes,
or handed to Lean's own `elabMutual` -- and if *that* fails, retried as an
induction-inductive block, which is the only way a homogeneous `mutual` whose
members nest can get through.  See `Mumi.Rescue` for why the retry waits for
Lean to fail rather than deciding up front.

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
    -- anything else keeps its incremental elaboration, and `mutual def` needs it
    unless elems.all (·[1].getKind == ``Lean.Parser.Command.«inductive») do
      throwUnsupportedSyntax
    -- a homogeneous block Lean takes is Lean's; one it does not may still be a
    -- block whose members nest into each other, which denesting turns into an
    -- induction-inductive block and `Mumi.IndInd` takes -- or one whose nesting
    -- is applied to a constructor-local, which the kernel refuses to denest and
    -- `Mumi.Denest` handles by making the local an index.  Last of all, it may
    -- be an induction-induction that got this far only because its members
    -- shadow globals of the same name, so that its arities elaborated against
    -- those and `classifyBlock` saw no failure to route on
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
      -- an induction-inductive block may denest, and what it denests into it
      -- then tries to hide again behind a bridge; the bridge is all or nothing,
      -- so a declaration the kernel rejects has to be rejected *here*, and
      -- `addDecl` otherwise hands the checking to a background task and the
      -- error surfaces long after the rollback could have happened
      withScope (fun sc => { sc with opts := Elab.async.set sc.opts false }) do
        discardingInfoOnError (IndInd.elabInductionInductive elems)
    | _ =>
      rescuing (elabHeterogeneousInductive elems)
        #[("the induction-inductive retry", IndInd.elabInductionInductive elems)]

end Mumi
