/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public meta import Lean.Elab.Command
public meta import Mumi.Owned
import Lean.Util.Trace

/-!
# Letting Lean answer first

Both entry points -- `inductive` in `Mumi.Declaration` and `mutual` in
`Mumi.Mutual` -- hand the declaration to Lean and step in only if Lean rejects
it *and* the rejected block is one this library has a lowering for.  `rescuing`
below is that shape.

The test is exact and free on the path that matters: a declaration Lean accepts
is elaborated once, by Lean, and no retry runs.  Deciding up front would mean
reimplementing the kernel's positivity and universe analysis, where an error
either way is bad -- too eager takes over working declarations, too shy misses
the ones this library exists for.

Failure alone does not license a takeover, since a declaration can fail for
unrelated reasons.  Each retry is gated on the block being one Lean could not
have handled; the two callers state their gates.  When every gate rejects, the
original error is reported and the retries leave no trace.  That hides a bug in
the lowering behind Lean's own complaint, so `set_option trace.Mumi.rescue true`
keeps the reasons.
-/

public section

open Lean Lean.Elab Lean.Elab.Command

namespace Mumi

initialize registerTraceClass `Mumi.rescue

/-- Has an error been logged since the log had `n` messages in it? -/
meta def errorLoggedSince (n : Nat) : CommandElabM Bool := do
  let msgs := (← get).messages.reportedPlusUnreported
  return (msgs.toList.drop n).any (·.severity matches .error)

/-- The errors logged since the log had `n` messages in it. -/
meta def errorsSince (n : Nat) : CommandElabM (List MessageData) := do
  let msgs := (← get).messages.reportedPlusUnreported
  return (msgs.toList.drop n).filterMap fun m =>
    if m.severity matches .error then some m.data else none

/-- Run `k`, and if it throws, drop the info trees it recorded before rethrowing. -/
meta def discardingInfoOnError (k : CommandElabM Unit) : CommandElabM Unit := do
  let saved := (← get).infoState
  try k catch ex =>
    modify ({ · with infoState := saved })
    throw ex

/--
Elaborate a command with `stock`; if that fails, try each of `retries` in turn
from the state `stock` started in. -/
meta def rescuing (stock : CommandElabM Unit)
    (retries : Array (String × CommandElabM Unit)) : CommandElabM Unit := do
  let saved ← get
  let nmsgs := saved.messages.reportedPlusUnreported.size
  let stockEx? ←
    try
      stock
      pure none
    catch ex =>
      pure (some ex)
  if stockEx?.isNone && !(← errorLoggedSince nmsgs) then
    return
  -- Lean rejected it; see whether it is one of ours
  let stockState ← get
  -- held in hand rather than traced here: restoring the state to try a retry
  -- would take the trace with it
  let stockWhys : Array MessageData ← match stockEx? with
    | some ex => pure #[ex.toMessageData]
    | none    => pure (← errorsSince nmsgs).toArray
  let traceStock : CommandElabM Unit := do
    for why in stockWhys do
      trace[Mumi.rescue] "the route tried first did not take: {why}"
  -- `none` on success; on failure the reason, held back until the state that
  -- would have swallowed it is restored
  let attempt (k : CommandElabM Unit) : CommandElabM (Option MessageData) := do
    set saved
    try
      withExporting (isExporting := (← getScope).isPublic) do
      withoutCommandIncrementality true do
      -- synchronously, so a kernel error in an added declaration is thrown where
      -- it can be caught; `addDecl` otherwise checks in a background task and the
      -- error surfaces after the retry reported success
      withScope (fun sc => { sc with opts := Elab.async.set sc.opts false }) do
        k
      match ← errorsSince nmsgs with
      | []   => return none
      | errs => throwError "the rescued declaration did not elaborate:{
                  MessageData.joinSep errs ", "}"
    catch ex =>
      return some ex.toMessageData
  let mut whys := #[]
  for (label, k) in retries do
    match ← attempt k with
    | none     =>
      -- the retries are in preference order, so the ones passed over are the
      -- informative half of the diagnosis
      traceStock
      for (label, why) in whys do
        trace[Mumi.rescue] "{label} did not take: {why}"
      trace[Mumi.rescue] "{label} took it"
      return
    | some why => whys := whys.push (label, why)
  -- not ours, or ours and broken: report what Lean reported, plus any reason a
  -- retry marked as being about a block it did recognise
  set stockState
  for (label, why) in whys do
    trace[Mumi.rescue] "{label} did not take: {why}"
  -- a route may see the same block twice under different conditions, and two
  -- attempts failing for one reason is still one reason
  let mut owned : Array MessageData := #[]
  let mut seen : Array String := #[]
  for (_, why) in whys do
    if isOwned why then
      let s := toString (← why.format)
      unless seen.contains s do
        seen := seen.push s
        owned := owned.push why
  match stockEx? with
  | some (.error ref msg) =>
    throw (.error ref (owned.foldl (fun m why => m ++ .hint' why) msg))
  | some ex => throw ex
  | none    =>
    for why in owned do
      logError why

end Mumi
