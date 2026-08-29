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
# Presenting an auxiliary member as the type it copies

Denesting replaces a nested occurrence with a *copy* of the type that was
nested, so the constructor the user wrote as taking a `Nonempty T` takes a
`T.nested_Nonempty_1` instead.  That copy is an implementation detail, and this
module is what keeps it from leaking.

The copy cannot be avoided.  A nested inductive whose denesting is
universe-heterogeneous is exactly the declaration the kernel refuses, so
`T.mkT : Nonempty T → T` can never be a kernel constructor here: the field's
type has to be something other than `Nonempty T`, or there is nothing to
declare.  What *can* be arranged is that nobody has to write the copy's name or
read it, and `Mumi.Denest` arranges most of it.  It proves the copy equal to the
original and registers a coercion each way, so the original type can be passed
to the constructor and a field bound by a pattern match can be used as the
original; the delaborator below then displays the copy as the original, so
signatures, goals and error messages read the way the declaration was written.
Between them, `#check @T.mkT`, `#print T`, `@T.rec`, a `match`, and the equation
lemmas of a function defined by one all read `Nonempty T`.

One notation escapes the coercions and so is handled here too: `⟨...⟩` reads the
expected type rather than being elaborated and then adjusted, so it has to be
sent to the original itself.

Only a member carrying that coercion is displayed this way.  A copy that is
merely *isomorphic* to what it copies -- any data member -- keeps its own name,
which is the honest thing to show.  `Mumi.IndInd` deals with those copies the
other way round: rather than displaying one as its original, it defines the
constructors and recursor over the originals outright, out of the isomorphism,
so there is nothing left for a delaborator to hide.

`set_option mumi.pp.nested false` turns the display off, which is what to reach
for when a mismatch between a copy and its original has to be seen.  It is off
under `pp.explicit` anyway, so the one error where the difference matters
exposes itself.
-/

public section

namespace Lean.Elab.MultiuniverseInductive

open Lean Meta

/--
The type that `n lvls args` is a copy of, if it is an auxiliary member that has
been identified with one, and is applied to all of its parameters and indices.
-/
meta def origType? (n : Name) (lvls : List Level) (args : Array Expr) :
    MetaM (Option Expr) := do
  let some ci := (← getEnv).find? (origCoeName n) | return none
  forallTelescope ci.type fun ys body => do
    -- a partially applied copy has no original to show: the original's
    -- parameters may mention any of the binders, so there is nothing to
    -- abstract over
    unless ys.size == args.size do return none
    let .app (.app (.const ``CoeOut _) src) tgt := body | return none
    unless src.getAppFn.constName? == some n && src.getAppArgs == ys do return none
    let abs ← mkLambdaFVars ys tgt
    return some ((abs.instantiateLevelParams ci.levelParams lvls).beta args)

open Elab Term in
/--
Elaborate `⟨...⟩` at an identified auxiliary member as if it had been written at
the type that member copies.

A coercion cannot help here: `⟨...⟩` reads the expected type rather than being
elaborated and then adjusted, and what it reads is the copy, whose constructors
belong to the shadow block the lowering built.  So `T.mkT ⟨T.mk1⟩` would
otherwise ask for a `T._shadow` -- a name from two translations down, for a
field whose type reads `Nonempty T`.

Anything else is left to Lean: an unknown expected type, a type that is not a
copy, or a copy with no original recorded all fall through untouched.
-/
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
/--
Display an identified auxiliary member as the type it copies.

Registered for `const` as well as `app` because a copy with no parameters or
indices of its own -- the common case -- is a bare constant.
-/
@[delab app, delab const]
meta def delabNestedAux : Delab := withIncRecDepth do
  unless mumi.pp.nested.get (← getOptions) do failure
  -- `pp.explicit` asks for the term as it is, and a mismatch between a copy and
  -- its original is exactly where that matters: `addPPExplicitToExposeDiff`
  -- turns it on when the two sides of a type error print the same, so standing
  -- aside here is what keeps such an error from reading `expected Nonempty T,
  -- got Nonempty T`
  if ← getPPOption getPPExplicit then failure
  let e ← getExpr
  let .const n lvls := e.getAppFn | failure
  let some orig ← origType? n lvls e.getAppArgs | failure
  -- the position stays that of the whole application, so the replacement is one
  -- clickable unit rather than one with misattributed children
  annotateCurPos (← withTheReader SubExpr ({ · with expr := orig }) delab)

end Lean.Elab.MultiuniverseInductive
