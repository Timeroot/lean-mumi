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

Two of this library's entry points -- `inductive` in `Mumi.Declaration` and
`mutual` in `Mumi.Mutual` -- work the same way: hand the declaration to Lean,
and step in only if Lean rejects it *and* what it rejected turns out to be a
block we have a lowering for.  `rescuing` below is that shape.

Letting Lean answer the question of whether a declaration needs us is exact,
and costs nothing on the path that matters: a declaration Lean accepts is
elaborated once, by Lean, and the retries never run.  Only a declaration that
was going to be an error anyway is elaborated twice.  Deciding up front instead
would mean reimplementing the kernel's positivity and universe analysis, and
being wrong in either direction is bad -- too eager and we take over working
declarations, too shy and we miss the ones we exist for.

Failure alone is not enough of a reason to take over: a declaration can fail
for any number of reasons that are nothing to do with us, and we must not
"rescue" one by quietly building a different declaration.  So each retry is
gated on the block being one Lean could not have handled; see the two callers
for what those gates are.  When every gate rejects, or every retry fails for
some other reason, the original error is reported and every trace of the
retries is dropped.

Dropping them is right for a declaration that was never ours, and unhelpful
for one that was: a bug in the lowering shows up as Lean's own complaint, with
nothing to say where it really went wrong.  `set_option trace.Mumi.rescue true`
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

/--
Run `k`, and if it throws, drop the info trees it recorded before rethrowing.

An induction-inductive block is elaborated against *scratch axioms* standing for
its members, which `emit` replaces with the real declarations at the end.  A
block that never reaches the end leaves info trees naming constants that are not
in the environment, and anything that walks them afterwards -- the
`constructorNameAsVariable` linter does, on every command -- fails on a name the
user cannot see, on top of the real error.  Dropping them costs the hover
information for a declaration that does not exist.

`rescuing` restores the whole state, so a retry gets this for free; a route that
is nobody's retry has to ask.
-/
meta def discardingInfoOnError (k : CommandElabM Unit) : CommandElabM Unit := do
  let saved := (← get).infoState
  try k catch ex =>
    modify ({ · with infoState := saved })
    throw ex

/--
Elaborate a command with `stock`, and if that fails, try each of `retries` in
turn, from the state `stock` started in.  The first one that succeeds wins.

If none does, the state `stock` left behind is restored -- so the user sees
exactly what Lean reported, and nothing about the retries except under
`set_option trace.Mumi.rescue true`, where each retry's `label` is paired with
its reason for not taking.

A retry counts as failing if it logs an error as well as if it throws one:
elaboration reports plenty of things without throwing, and a retry that leaves
an error behind has not rescued anything.
-/
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
  -- the reason the route tried first did not take is thrown away as soon as a
  -- retry does, and when that route is one of ours it is the half of the
  -- diagnosis worth having.  It has to be kept in hand rather than traced here,
  -- since restoring the state to try a retry would take the trace with it
  let stockWhys : Array MessageData ← match stockEx? with
    | some ex => pure #[ex.toMessageData]
    | none    => pure (← errorsSince nmsgs).toArray
  let traceStock : CommandElabM Unit := do
    for why in stockWhys do
      trace[Mumi.rescue] "the route tried first did not take: {why}"
  -- `none` on success, and on failure the reason, held back until the state
  -- that would have swallowed it has been restored
  let attempt (k : CommandElabM Unit) : CommandElabM (Option MessageData) := do
    set saved
    try
      withExporting (isExporting := (← getScope).isPublic) do
      withoutCommandIncrementality true do
      -- synchronously, so that a kernel error in one of the declarations we add
      -- is thrown where it can be caught: `addDecl` otherwise hands the checking
      -- to a background task, and the error would surface long after the retry
      -- had reported success
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
      -- the retries are in preference order, so which ones were passed over on
      -- the way to the one that took is the interesting half of the diagnosis
      traceStock
      for (label, why) in whys do
        trace[Mumi.rescue] "{label} did not take: {why}"
      trace[Mumi.rescue] "{label} took it"
      return
    | some why => whys := whys.push (label, why)
  -- not ours, or ours and broken: report exactly what Lean reported, plus any
  -- reason a retry marked as being about a block it did recognise
  set stockState
  for (label, why) in whys do
    trace[Mumi.rescue] "{label} did not take: {why}"
  -- a route may be offered the same block twice under different conditions, and
  -- when both attempts fail for the one reason it is still one reason
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
