/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public meta import Mumi.Public
public meta import Lean.Elab.Print

/-!
# Commands at an aliased member

An aliased data member is declared as `X._ind` with constructors `X._ind.c`, and
`X` and `X.c` unfold to them (`Lean.Elab.MultiuniverseInductive.addAliasedInds`).
Nothing is displayed under a name it does not have: what `cases` and `induction`
leave is stated over `X` because their eliminators are (`Mumi.Public`), not
because `X._ind` is printed as `X`.

`#print X` and `#print X.c` print the declarations the writer has under those
names -- the type former `X` and its constructors, at their own types -- in the
form Lean prints an inductive in; `#print X._ind` shows the kernel's.
`deriving instance C for X` is the handler's for `X._ind`.
-/

public section

namespace Mumi

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

open Lean Elab Command Lean.Elab in
/-- `deriving instance C for X`, for an aliased `X`, is the handler's for `X._ind`,
which `X` unfolds to: what it builds is found for `X` by instance search. -/
@[command_elab Lean.Parser.Command.«deriving»]
meta def elabDerivingAliased : CommandElab := fun stx => do
  let `(deriving $[noncomputable%$_nc?]? instance $[$_classes],* for $[$decls],*) := stx
    | throwUnsupportedSyntax
  let env ← getEnv
  let mut repl : Array (Syntax × Syntax) := #[]
  for d in decls do
    unless d.raw.isIdent do continue
    let some n ← (try some <$> liftCoreM (realizeGlobalConstNoOverload d.raw) catch _ => pure none)
      | continue
    let ind := MultiuniverseInductive.aliasIndName n
    if (env.find? n).any (·.isDefinition) && (env.find? ind).any (·.isInductive) then
      repl := repl.push (d.raw, mkIdentFrom d.raw (`_root_ ++ ind))
  if repl.isEmpty then throwUnsupportedSyntax
  let stx' ← stx.replaceM fun s => pure <| (repl.find? fun (d, _) =>
    s.isIdent && s.getId == d.getId && s.getPos? == d.getPos?).map (·.2)
  elabCommand stx'

end Mumi
