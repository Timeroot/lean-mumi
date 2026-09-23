/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public meta import Mumi.Options
public meta import Mumi.Elab
public meta import Mumi.IR.Frontend
public import Mumi.IR.Basic

/-!
# Taking over `mutual`

Importing this module makes `mutual` accept heterogeneous inductive blocks,
proof-mediated induction-induction, and a bounded experimental IR fragment.

The mechanism is that a `@[command_elab]` registered downstream is tried
*before* the builtin one -- `Lean.KeyedDeclsAttribute` prepends -- and
`throwUnsupportedSyntax` hands the block back to the builtin, with any state the
override touched rolled back.  So the elaborator below is a filter: it looks at
the block, and either lowers it or steps aside.

For a block mixing plain `inductive` and `def` declarations, stock Lean gets the
first attempt. Only its mixed-block rejection triggers the IR frontend. The
`mumi.mahlo` option selects the upper graph (default) or lower reflected carrier.
IR generation is transactional, including errors reported without exceptions.

Otherwise the existing heterogeneous/induction-inductive classifier is used.
In particular, `mutual def`, `structure`, `class`, `coinductive`, and ordinary
homogeneous inductive blocks retain their stock elaboration.

Set `mumi.enabled` to `false` to step aside unconditionally.
-/

public section

open Lean Lean.Elab Lean.Elab.Command

namespace Mumi

/--
Shared interception point for all Mumi mutual-block translations. Mixed IR
blocks try stock Lean first; the other routes retain their existing classifier.
-/
@[command_elab Lean.Parser.Command.«mutual»]
meta def elabMutualHeterogeneous : CommandElab := fun stx => do
  unless mumi.enabled.get (← getOptions) do
    throwUnsupportedSyntax
  let elems := stx[1].getArgs
  trace[Mumi.ir] "mutual gate: {stx.getKind}, IR = {IndRec.isIRBlock elems}"
  if IndRec.isIRBlock elems then
    let saved ← get
    let stockAccepted ← try
      -- Stock Lean gets the first opportunity, even for a syntactically mixed block.
      elabMutual stx
      pure true
    catch ex =>
      trace[Mumi.ir] "stock rejected: {ex.toMessageData}"
      unless (← ex.toMessageData.toString).startsWith "invalid mutual block:" do throw ex
      set saved
      pure false
    unless stockAccepted do
      try
        withExporting (isExporting := (← getScope).isPublic) do
        withoutCommandIncrementality true do
        withScope (fun sc => { sc with opts := Elab.async.set sc.opts false }) do
          IndRec.elaborate elems
      catch ex =>
        set saved
        logException ex
    return
  let route ← classifyBlock elems
  if route == .stock then
    throwUnsupportedSyntax
  withExporting (isExporting := (← getScope).isPublic) do
  withoutCommandIncrementality true do
    match route with
    | .indind => IndInd.elabInductionInductive elems
    | _ => elabHeterogeneousInductive elems

end Mumi
