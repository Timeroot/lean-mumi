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

/-!
# Writing the original where a copy is expected

Denesting replaces a nested occurrence by a *copy* of the nested type: the
kernel's constructor for one written as taking `Nonempty T` takes a
`T.nested_Nonempty_1`.

Most nestings need no copy.  When the head is data the kernel denests the
occurrence itself, and `Mumi.Lowering` lets it, so no copy exists.  A copy is
needed only for a nesting the kernel rejects: a head in `Prop` under a member in
`Type`.  There it is unavoidable, since `T.mkT : Nonempty T → T` is exactly the
declaration the kernel refuses.

What can be arranged is that no one has to write the copy's name: the writer's
constructors and recursors take the original (`Mumi.Public.publishOverOriginals`),
and `Mumi.Denest` registers a coercion in each direction for a value that does
meet the copy.  Anonymous constructor notation bypasses coercions, because it
reads the expected type before elaborating, so `elabAnonymousCtorNested` reads
`⟨...⟩` at a copy as written at the original.  Nothing here changes how anything
is displayed: a copy is shown under its own name wherever it is the type.
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

end Lean.Elab.MultiuniverseInductive
