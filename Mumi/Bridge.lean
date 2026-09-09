/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public meta import Mumi.Options
public meta import Mumi.Denest
public meta import Lean.Meta.Basic
public meta import Lean.Elab.Term
public meta import Lean.PrettyPrinter.Delaborator.Basic
public meta import Lean.PrettyPrinter.Delaborator.Builtins

/-!
# Displaying an auxiliary member as the type it copies

Denesting replaces a nested occurrence by a *copy* of the nested type: a
constructor written as taking `Nonempty T` takes a `T.nested_Nonempty_1`.  The
copy is an implementation detail, and this module hides it.

Most nestings need no copy.  When the head is data the kernel denests the
occurrence itself, and `Mumi.Lowering` lets it, so no copy exists.  A copy is
needed only for a nesting the kernel rejects: a head in `Prop` under a member in
`Type`.  There it is unavoidable, since `T.mkT : Nonempty T → T` is exactly the
declaration the kernel refuses.

What can be arranged is that no one writes or reads the copy's name.
`Mumi.Denest` proves the copy equal to the original and registers a coercion in
each direction; the delaborator below displays the copy as the original.
Together these make `#check @T.mkT`, `#print T`, `@T.rec`, a `match`, and the
equation lemmas of a function defined by one all read `Nonempty T`.  Anonymous
constructor notation bypasses coercions, because it reads the expected type
before elaborating, so `elabAnonymousCtorNested` handles it here.

Only a member carrying the equality is displayed this way.  A data copy is
isomorphic to its original but not equal to it, so it keeps its own name;
`Mumi.IndInd` instead defines its constructors and recursor over the original
directly, using the isomorphism.

`set_option mumi.pp.nested false` disables the display.  `pp.explicit` disables
it too, so an error about a copy/original mismatch shows the difference.
-/

public section

namespace Lean.Elab.MultiuniverseInductive

open Lean Meta

/-- The type `n lvls args` copies, if `n` is an auxiliary member identified with
one and is applied to all its parameters and indices. -/
meta def origType? (n : Name) (lvls : List Level) (args : Array Expr) :
    MetaM (Option Expr) := do
  -- only an equality licenses the display: a data copy has the same coercions
  -- but is merely isomorphic, so showing it as the original would print two
  -- distinct types the same way
  unless (← getEnv).contains (n ++ `eq_orig) do return none
  let some ci := (← getEnv).find? (origCoeName n) | return none
  forallTelescope ci.type fun ys body => do
    -- a partially applied copy has no original to show: the original's
    -- parameters may mention any binder, so there is nothing to abstract over
    unless ys.size == args.size do return none
    let .app (.app (.const ``CoeOut _) src) tgt := body | return none
    unless src.getAppFn.constName? == some n && src.getAppArgs == ys do return none
    let abs ← mkLambdaFVars ys tgt
    return some ((abs.instantiateLevelParams ci.levelParams lvls).beta args)

open Elab Term in
/--
Elaborate `⟨...⟩` at an identified auxiliary member as if written at the type
that member copies. -/
@[term_elab Lean.Parser.Term.anonymousCtor]
meta def elabAnonymousCtorNested : TermElab := fun stx expectedType? => do
  unless mumi.enabled.get (← getOptions) do throwUnsupportedSyntax
  let some expectedType := expectedType? | throwUnsupportedSyntax
  let expectedType ← instantiateMVars expectedType
  let .const n lvls := expectedType.getAppFn | throwUnsupportedSyntax
  let some orig ← origType? n lvls expectedType.getAppArgs | throwUnsupportedSyntax
  -- elaborating at `orig` re-enters this elaborator, which then falls through:
  -- the original is not a copy of anything
  ensureHasType expectedType (← elabTerm stx orig)

open PrettyPrinter Delaborator SubExpr in
/-- Display an identified auxiliary member as the type it copies. -/
@[delab app, delab const]
meta def delabNestedAux : Delab := withIncRecDepth do
  unless mumi.pp.nested.get (← getOptions) do failure
  -- `pp.explicit` asks for the term as it is
  if ← getPPOption getPPExplicit then failure
  let e ← getExpr
  let .const n lvls := e.getAppFn | failure
  let some orig ← origType? n lvls e.getAppArgs | failure
  -- the position stays that of the whole application, so the replacement is one
  -- clickable unit with no misattributed children
  annotateCurPos (← withTheReader SubExpr ({ · with expr := orig }) delab)

end Lean.Elab.MultiuniverseInductive
