/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public meta import Mumi.Options
public meta import Mumi.Elab
public meta import Mumi.Rescue
public meta import Mumi.IR.Frontend
public meta import Mumi.IR.Family
public import Mumi.IR.Basic
public meta import Lean.Elab.Declaration
public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Meta.Closure

/-!
# Taking over `mutual`

Importing this module makes `mutual` accept heterogeneous inductive blocks,
proof-mediated induction-induction, and a bounded experimental IR fragment.

A `@[command_elab]` registered downstream runs *before* the builtin one, because
`Lean.KeyedDeclsAttribute` prepends.  `throwUnsupportedSyntax` hands the block
back to the builtin and rolls back any state the override touched.  So the
elaborator below is a filter: it either lowers the block or steps aside.

For a block mixing plain `inductive` and `def` declarations, stock Lean gets the
first attempt. Only its mixed-block rejection triggers the IR frontend. The
`mumi.mahlo` option selects the upper graph (default) or lower reflected carrier.
IR generation is transactional, including errors reported without exceptions.

Otherwise it steps aside for everything except a block of plain `inductive`
declarations.  `mutual def`, `structure`, `class` and `coinductive` blocks reach
the same Lean code as before and keep their incremental elaboration.

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

/--
`inj` and `injEq` for the constructors of the data members an induction-recursion
declared as definitions, read back through each member's `casesOn`. -/
meta def publishIRInjs (elems : Array Syntax) : CommandElabM Unit := do
  let ns ← getCurrNamespace
  for e in elems do
    unless e[1].isOfKind ``Lean.Parser.Command.«inductive» do continue
    let mem := ns ++ e[1][1][0].getId
    let env ← getEnv
    unless (env.find? mem).any (·.isDefinition) do continue
    let ctors := e[1][4].getArgs.map fun c => mem ++ c[3].getId
    unless ctors.all env.contains && env.contains (mem ++ `casesOn) do continue
    liftTermElabM do
      if ← Meta.forallTelescope (← getConstInfo mem).type fun _ s => pure s.isProp then return
      let np ← casesParams mem
      for c in ctors do
        if (← getConstInfo c).isCtor then continue
        discard <| MultiuniverseInductive.attempt? `Mumi m!"no injectivity for `{c}`" <|
          addInjViaCases np mem c ctors

/-- Shared interception point for every Mumi `mutual` translation.  A mixed
`inductive`/`def` block tries stock Lean first and falls to the IR frontend; an
all-`inductive` block goes to the heterogeneous and induction-inductive routes;
everything else is deferred to Lean's own elaborator. -/
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
          IndRec.elaborateAny elems
          publishIRInjs elems
      catch ex =>
        unless mumi.ir.debug.get (← getOptions) do set saved
        logException ex
    return
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

/-- `lhs = rhs` by `rfl`, checked by the kernel alone: the goal becomes an
auxiliary theorem whose proof is `Eq.refl lhs`, which nothing but the kernel
looks at.  What the IR frontend states at variables of the written universe
is definitional there, and stays so at any terms put for them, but Meta's
unifier can wander off into the stage engine where the kernel decides it at
once; the frontend closes such goals, a constructor nested in an index among
them, this way. -/
syntax (name := irKernelRfl) "ir_kernel_rfl" : tactic

open Lean Elab Tactic in
@[tactic irKernelRfl] meta def evalIrKernelRfl : Tactic := fun _ => withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let some (_, lhs, _) := ty.eq? | throwError "ir_kernel_rfl: the goal is not an equation{indentExpr ty}"
  if ty.hasExprMVar then throwError "ir_kernel_rfl: the goal has metavariables{indentExpr ty}"
  g.assign (← Meta.mkAuxTheorem ty (← Meta.mkEqRefl lhs))
  replaceMainGoal []

end Mumi
