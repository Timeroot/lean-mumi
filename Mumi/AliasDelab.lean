/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public meta import Mumi.Public
public meta import Lean.PrettyPrinter.Delaborator.Basic
public meta import Lean.PrettyPrinter.Delaborator.Builtins
public meta import Lean.Elab.Print

/-!
# Displaying an aliased member under the writer's name

An aliased data member is declared as `X._ind` with constructors `X._ind.c`, and
`X` and `X.c` unfold to them (`Lean.Elab.MultiuniverseInductive.addAliasedInds`).
What Lean computes -- the goals `cases` leaves, the type of a field a `match`
binds -- is stated over the inductive, so it would read `X._ind`.  The two are
the same up to unfolding, so this delaborator shows the writer's name wherever
the internal one would appear.  `pp.explicit` shows the term as it is.

`#print X` and `#print X.c` print what Lean prints for an inductive and its
constructor, which is what the writer declared; `#print X._ind` shows the
declaration as it is.
-/

public section

namespace Mumi

open Lean PrettyPrinter Delaborator SubExpr in
/-- Display `X._ind` as `X`, and `X._ind.c` as `X.c`. -/
@[delab app, delab const]
meta def delabAliased : Delab := do
  if ← getPPOption getPPExplicit then failure
  let e ← getExpr
  let .const n us := e.getAppFn | failure
  let some pub := publicName? (← getEnv) n | failure
  withTheReader SubExpr ({ · with expr := mkAppN (.const pub us) e.getAppArgs }) delab

open Lean Elab Command Lean.Elab in
/-- `#print` an aliased member as the inductive it was written as, and its
constructors as constructors. -/
@[command_elab Lean.Parser.Command.print]
meta def elabPrintAliased : CommandElab
  | `(#print%$tk $id:ident) => withRef tk do
    let env ← getEnv
    let some n ← (try some <$> liftCoreM (realizeGlobalConstNoOverload id) catch _ => pure none)
      | throwUnsupportedSyntax
    let some ci := env.find? n | throwUnsupportedSyntax
    unless ci.isDefinition do throwUnsupportedSyntax
    let lvls : MessageData := match ci.levelParams with
      | [] => ""
      | u :: us => us.foldl (fun m v => m ++ ", " ++ toMessageData v) (m!".\{{u}") ++ "}"
    if let some (.inductInfo ii) := env.find? (MultiuniverseInductive.aliasIndName n) then
      let mut m : MessageData := m!"inductive {n}{lvls} : {ci.type}"
      m := m ++ Format.line ++ m!"number of parameters: {ii.numParams}"
      m := m ++ Format.line ++ "constructors:"
      for c in ii.ctors do
        let pub := Name.str n c.getString!
        let some pc := env.find? pub | throwUnsupportedSyntax
        m := m ++ Format.line ++ m!"{pub} : {pc.type}"
      logInfo m
    else if let some (.ctorInfo _) := env.find? (Name.str (MultiuniverseInductive.aliasIndName n.getPrefix) n.getString!) then
      logInfo m!"constructor {n}{lvls} : {ci.type}"
    else throwUnsupportedSyntax
  | _ => throwUnsupportedSyntax

end Mumi
