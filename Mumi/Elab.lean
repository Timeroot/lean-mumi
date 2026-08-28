/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg

The `het` functions below are adapted from `Lean.Elab.Command`'s inductive
pipeline (`src/Lean/Elab/MutualInductive.lean` and `src/Lean/Elab/Inductive.lean`
in leanprover/lean4, v4.33.1), which is Copyright (c) Microsoft Corporation and
released under the same license.
-/
module

public import Mumi.Lowering
public import Mumi.Denest
import all Lean.Elab.MutualInductive

/-!
# Elaborating a universe-heterogeneous block

`Mumi.Lowering` turns an *elaborated* heterogeneous block into declarations the
kernel accepts.  This module is the part in front of it: it takes the block's
syntax through exactly the elaboration `mutual` does -- same headers, same
constructors, same parameter and universe analysis -- and hands the result to
`Lean.Elab.MultiuniverseInductive.lower`.

Doing that in a downstream library means reaching into `Lean.Elab.Command`,
whose inductive pipeline is `private`.  `import all` gives us access, but not
the ability to *edit* those functions, and two of them enforce the very
restriction we are lifting:

* `checkParamsAndResultType` rejects a member whose resulting sort differs from
  the first member's, while the headers are being elaborated; and
* `checkResultingUniverses` checks every member's constructor fields against
  the *block's* universe, meaning the first member's.

So the five functions on the path between `elabMutualInductive` and the point
where the block is finally added are reproduced here, adapted.  They are marked
`het` and are copies of the v4.33.1 originals; the adaptation in each case is
small and flagged in a comment.  Everything they call is used unmodified from
`Lean.Elab.Command`.
-/

public section

namespace Mumi

open Lean Lean.Meta Lean.Elab Lean.Elab.Command

variable {α : Type}

/-! ## Header elaboration without the same-universe check -/

/--
`Lean.Elab.Command.checkParamsAndResultType`, minus the check that this member's
resulting sort matches the preceding member's.  Parameter compatibility is still
checked, and the resulting type must still be a sort.
-/
private def checkParamsAndResultTypeHet (type firstType : Expr) (numParams : Nat) :
    TermElabM Unit := do
  try
    forallTelescopeCompatible type firstType numParams fun _ type _ =>
    forallTelescopeReducing type fun _ type => do
      let type ← whnfD type
      match type with
      | .sort .. => pure ()
      | _ => throwError "The specified resulting type{inlineExpr type}is not a type"
  catch
    | Exception.error ref msg =>
      throw (Exception.error ref m!"Invalid mutually inductive types: {msg}")
    | ex => throw ex

/-- `Lean.Elab.Command.checkHeaders`, using `checkParamsAndResultTypeHet`. -/
private def checkHeadersHet (rs : Array PreElabHeaderResult) (numParams : Nat) (i : Nat)
    (firstType? : Option Expr) : TermElabM Unit := do
  if h : i < rs.size then
    let type ← checkHeader rs[i] numParams firstType?
    checkHeadersHet rs numParams (i + 1) type
where
  checkHeader (r : PreElabHeaderResult) (numParams : Nat) (firstType? : Option Expr) :
      TermElabM Expr := do
    let type := r.type
    match firstType? with
    | none => return type
    | some firstType =>
      withRef r.view.ref <| checkParamsAndResultTypeHet type firstType numParams
      return firstType

/-- `Lean.Elab.Command.elabHeaders`, using `checkHeadersHet`. -/
private def elabHeadersHet (views : Array InductiveView) :
    TermElabM (Array PreElabHeaderResult) := do
  let rs ← elabHeadersAux views 0 #[]
  if rs.size > 1 then
    checkUnsafe rs
    checkClass rs
    let numParams ← checkNumParams rs
    checkHeadersHet rs numParams 0 none
  return rs

/-! ## Per-member universe checking -/

/-- The resulting universe of a single member, rather than of the block. -/
private def getIndTypeUniverse (indType : InductiveType) : TermElabM Level :=
  forallTelescopeReducing indType.type fun _ r => do
    let r ← whnfD r
    match r with
    | .sort u => return u
    | _ => throwError "Unexpected inductive type resulting type{indentExpr r}"

/--
`Lean.Elab.Command.checkResultingUniverses`, but checking each member's
constructor fields against *that member's* own resulting universe rather than
against the block's.

This is what the lowering needs: its members end up in separate inductive
declarations, so a member's fields only ever have to fit that member's universe.
-/
private def checkResultingUniversesPerType (views : Array InductiveView)
    (elabs' : Array InductiveElabStep2) (numParams : Nat) (indTypes : List InductiveType) :
    TermElabM Unit := do
  for h : i in *...indTypes.length do
    let indType := indTypes[i]
    let u := (← instantiateLevelMVars (← getIndTypeUniverse indType)).normalize
    checkResultingUniversePolymorphism #[views[i]!] u numParams indTypes
    if u.isZero then continue
    -- See if there is a custom error. If so, this should throw an error first:
    elabs'[i]!.checkUniverses numParams u
    indType.ctors.forM fun ctor =>
    forallTelescopeReducing ctor.type fun ctorArgs _ => do
      for ctorArg in ctorArgs[numParams...*] do
        let type ← inferType ctorArg
        let v := (← instantiateLevelMVars (← getLevel type)).normalize
        unless u.geq v do
          let mut msg := m!"Invalid universe level in constructor `{ctor.name}`: Parameter"
          unless (← ctorArg.fvarId!.getUserName).hasMacroScopes do
            msg := msg ++ m!" `{ctorArg}`"
          msg := msg ++ m!" has type{indentExpr type}\n\
            at universe level{indentD v}\n\
            which is not less than or equal to the inductive type's resulting universe \
            level{indentD u}"
          withCtorRef views ctor.name <| throwError msg

/-! ## The elaboration pipeline -/

/--
`Lean.Elab.Command.mkInductiveDeclCore`, using `checkResultingUniversesPerType`.
-/
private def mkInductiveDeclCoreHet (callback : AddAndFinalizeContext → TermElabM α)
    (vars : Array Expr) (elabs : Array InductiveElabStep1) (rs : Array PreElabHeaderResult)
    (scopeLevelNames : List Name) : TermElabM α := do
  let views := elabs.map (·.view)
  let view0 := views[0]!
  let allUserLevelNames := rs[0]!.levelNames
  let isUnsafe := view0.modifiers.isUnsafe
  withInductiveLocalDecls rs fun params indFVars => do
    trace[Elab.inductive] "indFVars: {indFVars}"
    /- Start elaborating constructors: -/
    let rs := Array.zipWith (fun r indFVar => { r with indFVar : ElabHeaderResult }) rs indFVars
    let mut indTypesArray : Array InductiveType := #[]
    let mut elabs' := #[]
    for h : i in *...views.size do
      Term.addLocalVarInfo views[i].declId indFVars[i]!
      let r := rs[i]!
      let elab' ← Term.withDeprecationContextFromAttrs views[i].modifiers.attrs <|
        elabs[i]!.elabCtors rs r params
      elabs' := elabs'.push elab'
      indTypesArray := indTypesArray.push
        { name := r.view.declName, type := r.type, ctors := elab'.ctors }
    Term.synthesizeSyntheticMVarsNoPostponing
    let indTypes ← indTypesArray.toList.mapM instantiateMVarsAtInductive
    /- Constructor elaboration complete. -/
    let numExplicitParams ← fixedIndicesToParams params.size indTypes indFVars
    trace[Elab.inductive] "numExplicitParams: {numExplicitParams}"
    withUsed elabs' vars indTypes fun vars => do
      let numVars := vars.size
      let numParams := numVars + numExplicitParams
      let indTypes ← updateParams vars indTypes
      let indTypes ← indTypes.mapM instantiateMVarsAtInductive
      ensureNoUnassignedMVarsAtInductives indTypes
      let indTypes ← withoutExporting do
        let typeLMVarIds ← do
          let mut lmvars := {}
          for indType in indTypes do
            lmvars := collectLevelMVars lmvars indType.type
          lmvars ← Prod.snd <$> (elabs'.forM InductiveElabStep2.collectExtraHeaderLMVars).run lmvars
          pure lmvars.result
        let inferResult ← inferResultingUniverse views numParams indTypes indFVars typeLMVarIds
        propagateUniversesToConstructors numParams indTypes inferResult
        levelMVarToParamAtInductives indTypes typeLMVarIds inferResult
        inferResult.assign
        indTypes.mapM instantiateMVarsAtInductive
      withoutExporting do
        elabs'.forM fun elab' => elab'.finalizeTermElab
        ensureNoUnassignedLevelMVarsAtInductives views indTypes
        -- the one change: per member, not per block
        checkResultingUniversesPerType views elabs' numParams indTypes
      let usedLevelNames := collectLevelParamsInInductive indTypes
      match sortDeclLevelParams scopeLevelNames allUserLevelNames usedLevelNames with
      | .error msg => throwErrorAt view0.declId msg
      | .ok levelParams =>
        callback {
          views := views
          elabs' := elabs'
          indFVars := indFVars
          vars := vars
          levelParams := levelParams
          indTypes := indTypes
          isUnsafe := isUnsafe
          rs := rs
          params := params
          isCoinductive := false
          numVars := numVars
          numParams := numParams
        }

/-- `Lean.Elab.Command.withElaboratedHeaders`, using `elabHeadersHet`. -/
private def withElaboratedHeadersHet (vars : Array Expr) (elabs : Array InductiveElabStep1)
    (k : Array Expr → Array InductiveElabStep1 → Array PreElabHeaderResult → List Name →
      TermElabM α) : TermElabM α :=
  Term.withoutSavingRecAppSyntax do
    let views := elabs.map (·.view)
    let view0 := views[0]!
    let scopeLevelNames ← Term.getLevelNames
    InductiveElabStep1.checkLevelNames views
    let allUserLevelNames := view0.levelNames
    withRef view0.ref <| Term.withLevelNames allUserLevelNames do
      let rs ← elabHeadersHet views
      Term.synthesizeSyntheticMVarsNoPostponing
      ElabHeaderResult.checkLevelNames rs
      trace[Elab.inductive] "level names: {allUserLevelNames}"
      k vars elabs rs scopeLevelNames

/--
`Lean.Elab.Command.elabInductiveViews`, but lowering the block instead of adding
it as one mutual inductive declaration.

`lower` makes the auxiliary constructions itself as it emits each declaration,
so there is nothing left to do for them here.
-/
private def elabHeterogeneousInductiveViews (requireHeterogeneous : Bool) (vars : Array Expr)
    (elabs : Array InductiveElabStep1) : TermElabM FinalizeContext := do
  let view0 := elabs[0]!.view
  Term.withDeclName view0.declName do withRef view0.ref do
  withExporting (isExporting := !isPrivateName view0.declName) do
    let res ← withElaboratedHeadersHet vars elabs fun vars elabs rs scopeLevelNames =>
      mkInductiveDeclCoreHet (callback := fun context => do
          let indTypes := context.indTypes.toArray
          let inp : MultiuniverseInductive.Input := {
            levelParams := context.levelParams
            numVars     := context.numVars
            numParams   := context.numParams
            memberFVars := context.indFVars
            memberNames := indTypes.map (·.name)
            memberTypes := indTypes.map (·.type)
            ctorNames   := indTypes.map (·.ctors.toArray.map (·.name))
            ctorTypes   := indTypes.map (·.ctors.toArray.map (·.type))
            isClass     := view0.isClass
          }
          -- a block with no nested occurrence comes back from `denest` unchanged
          MultiuniverseInductive.denest inp fun inp => do
            if requireHeterogeneous && !(← inp.isHeterogeneous) then
              throwError "This block is homogeneous once denested, so it is Lean's to elaborate"
            MultiuniverseInductive.lower inp
          buildFinalizeContext context.elabs' context.levelParams context.vars context.params
            context.views context.indFVars context.rs)
        vars elabs rs scopeLevelNames
    for e in elabs do
      enableRealizationsForConst e.view.declName
      for ctor in e.view.ctors do
        enableRealizationsForConst ctor.declName
    return res

/--
Elaborates a universe-heterogeneous mutual inductive block, given the elements
of the `mutual` block (`stx[1].getArgs`).

The caller is responsible for having established that every element is an
`inductive` declaration.

With `requireHeterogeneous`, the block is only lowered if it really is
heterogeneous once denested, and an error is thrown otherwise.  A caller that
has not already checked -- the nested-inductive rescue, which cannot know
without denesting -- uses this to be sure it is not taking over a block Lean
handles itself.
-/
def elabHeterogeneousInductive (elems : Array Syntax) (requireHeterogeneous := false) :
    CommandElabM Unit := do
  let inductives ← elems.mapM fun stx => do
    let modifiers ← elabModifiers ⟨stx[0]⟩
    pure (modifiers, stx[1])
  if inductives.any (·.1.isMeta) && inductives.any (!·.1.isMeta) then
    throwError "A mix of `meta` and non-`meta` declarations in the same `mutual` block is \
      not supported"
  let elabs ← runTermElabM fun _ => inductives.mapM fun (modifiers, stx) =>
    mkInductiveView modifiers stx
  checkNoInductiveNameConflicts elabs
  elabs.forM fun e => checkValidInductiveModifier e.view.modifiers
  liftTermElabM <| elabs.forM fun e => withRef e.view.ref do
    Term.applyAttributesAt e.view.declName e.view.modifiers.attrs .beforeElaboration
  let res ← runTermElabM fun vars =>
    elabHeterogeneousInductiveViews requireHeterogeneous vars elabs
  elabInductiveViewsFinalize (elabs.map (·.view)) res
  elabInductiveViewsPostprocessing (elabs.map (·.view))

/-! ## Deciding whether a block needs us -/

/--
Elaborates the block's headers and reports whether the stock same-universe check
would reject them.

The check that decides this is `Lean.Elab.Command.checkHeaders`, called
unmodified, so the answer is exactly "would `mutual` reject this block for
living in several universes?".  Header elaboration itself is done without that
check, so a heterogeneous block gets far enough to be asked about.
-/
private def headersAreHeterogeneous (elabs : Array InductiveElabStep1) : TermElabM Bool :=
  Term.withoutSavingRecAppSyntax do
    let views := elabs.map (·.view)
    let view0 := views[0]!
    InductiveElabStep1.checkLevelNames views
    withRef view0.ref <| Term.withLevelNames view0.levelNames do
      let rs ← Term.withoutErrToSorry <| elabHeadersHet views
      Term.synthesizeSyntheticMVarsNoPostponing
      if rs.size ≤ 1 then return false
      let numParams ← checkNumParams rs
      try
        checkHeaders rs numParams 0 none
        return false
      catch _ =>
        return true

/--
Whether this `mutual` block is one we should take over: every element a plain
`inductive`, and the members not all in one universe.

Anything that goes wrong while finding out -- an ill-formed header, a missing
name, an unrelated elaboration failure -- answers `false`, so that the stock
elaborator runs and reports it.  All state touched here is rolled back.
-/
def blockNeedsLowering (elems : Array Syntax) : CommandElabM Bool := do
  unless elems.all (·[1].getKind == ``Lean.Parser.Command.«inductive») do
    return false
  if elems.size ≤ 1 then
    return false
  let saved ← get
  let res ←
    try
      let inductives ← elems.mapM fun stx => do
        let modifiers ← elabModifiers ⟨stx[0]⟩
        pure (modifiers, stx[1])
      runTermElabM fun _ => do
        let elabs ← inductives.mapM fun (modifiers, stx) => mkInductiveView modifiers stx
        if elabs.any (·.view.isCoinductive) then
          return false
        headersAreHeterogeneous elabs
    catch _ =>
      pure false
  set saved
  return res

end Mumi
