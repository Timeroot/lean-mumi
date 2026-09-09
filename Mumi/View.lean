/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Mumi.Lowering
import all Lean.Meta.SizeOf

public section

/-!
# Seeing a member as the inductive it was written as

An induction-inductive member is emitted as a definition over a wrapper.  `Ctx`
is `Ctx._sub`, a one-constructor inductive; `Ctx.snoc` is a definition that packs
a `Ctx._pre.snoc` beside a proof that the pre-term is well formed.  Statements
about the block read as written, and `induction` and `cases` use the eliminators
that step 10 of the emit adds.  `match` is the exception.

The equation compiler finds the discriminant's inductive by reducing its type,
so it always reaches the wrapper, and the `@[match_pattern]` constructors unfold
on the way in.  `Ctx.snoc Γ h` becomes `⟨Γ.val.snoc, _⟩`, whose `Γ` sits under a
projection and is no longer a pattern variable.  `Tm.var Γ h` becomes
`⟨Tm._pre.var, True.intro⟩`, which has lost its arguments.  `Lean.Meta.Match`
reduces the type itself, so there is no hook to redirect it.

Instead the member is given something to be matched *through*.  A **view** is an
inductive indexed by the member, with one constructor per constructor of the
member, concluding at that constructor's value:

```lean
inductive Ctx.View : Ctx → Type where
  | nil : Ctx.View .nil
  | snoc (Γ : Ctx) (h : Ok Γ) : Ctx.View (.snoc Γ h)
```

This is legal where the member's own declaration was not: `Ctx` already exists
to be indexed by, and the view is not recursive.  A case split on `Ctx.View c`
refines `c` to the constructor in its index, so matching `c` alongside `c.view`
recovers the alternatives that were written.  `Mumi.MatchView` is that rewrite;
this module builds what it needs.

## Indices that are proofs

A constructor may take a proof of an index as a field, as in `Tm.var (Γ : Ctx)
(h : Ok Γ) : Tm Γ h`.  A pattern may not bind that proof: Lean cannot state that
the field and the index are the same proof, and leaves a metavariable where the
field should be.  A hand-written `inductive T : (n : Nat) → P n → Type` fails the
same way.

Lean's own `cases` responds by not offering the field, and the view encodes that
in its shape.  Leading indices become **parameters** of the view, which drops
their fields from its constructors.  A parameter may not depend on an index, so
promoting a proof index promotes everything before it:

```lean
inductive Tm.View (Γ : Ctx) (h : Ok Γ) : Tm Γ h → Type where
  | var : Tm.View Γ h (.var Γ h)
  | wk (t : Tm Γ h) : Tm.View Γ h (.wk Γ h t)
```

`Γ` and `h` are then named at the discriminant, not in the pattern, which is
what `cases` presents too.

## Recursion

Recursion over a member is structural where it can be.  The member unfolds to
its wrapper, and the wrapper has a `below` and a `brecOn` built from the block's
recursors, so the equation compiler finds what it looks for.  Indexed members
are covered whether the pre-type deleted the index, making it a parameter of the
wrapper, or kept it, in which case the recursor binds it and the table is
generalised over everything that mentions it.

A recursive call at a *different* index is not structural: `below` builds its
table at fixed parameters, so there is no column for a row at another one, and
no way to write the motive of one.  Such a recursion can still be well founded
given a `SizeOf` instance to measure with and the specification lemmas the
termination tactic simplifies with, so this module builds those too.  The
measure is the pre-term's size, which is what remains after the proofs are
erased and is exactly the size of what was written.
-/

namespace Mumi

open Lean Meta Lean.Elab.MultiuniverseInductive

initialize registerTraceClass `Mumi.view (inherited := true)

/-- The inductive that presents `mem`'s constructors as constructors. -/
def viewName (mem : Name) : Name := mem ++ `View

/-- The function that takes an element of `mem` to its view. -/
def viewFnName (mem : Name) : Name := mem ++ `view

/-- Every member a view was built for. -/
structure Viewed where
  /-- The members that have a view. -/
  members : NameSet := {}
  /-- What their constructors are called, last component only. -/
  ctors : NameSet := {}
  deriving Inhabited

/-- Record that `mem`'s view was built, with `cs` for its constructors. -/
def Viewed.add (s : Viewed) : Name × Array Name → Viewed
  | (mem, cs) =>
    { members := s.members.insert mem
      ctors := cs.foldl (init := s.ctors) fun t c =>
        match c with
        | .str _ c => t.insert (.mkSimple c)
        | _ => t }

initialize viewedExt : SimplePersistentEnvExtension (Name × Array Name) Viewed ←
  registerSimplePersistentEnvExtension {
    addEntryFn    := Viewed.add
    addImportedFn := fun as => as.foldl (init := {}) fun s a => a.foldl Viewed.add s
  }

/-- The members in this environment that have a view. -/
def viewedMembers (env : Environment) : NameSet :=
  (viewedExt.getState env).members

/-- What the constructors of those members are called, last component only. -/
def viewedCtors (env : Environment) : NameSet :=
  (viewedExt.getState env).ctors

/-- `mem`'s view and the function into it, if this library built them. -/
def viewOf? (env : Environment) (mem : Name) : Option (Name × Name) := do
  guard ((viewedMembers env).contains mem)
  some (viewName mem, viewFnName mem)

/--
Make the first `n` binders of a telescope implicit, leaving binders that are
already inferred some other way alone. -/
private partial def implicitUpTo (n : Nat) (e : Expr) : Expr :=
  match n, e with
  | 0, e => e
  | n + 1, .forallE nm t b bi =>
    .forallE nm t (implicitUpTo n b) (if bi.isExplicit then .implicit else bi)
  | _, e => e

/-- The pre-term inside a member's element, which is what it is measured by. -/
private def preOf (x : Expr) : MetaM Expr := do
  let ty ← whnf (← inferType x)
  let .const n@(.str _ "_sub") us := ty.getAppFn
    | throwError "`{← inferType x}` is not the wrapper a member unfolds to"
  return mkAppN (mkConst (n ++ `val) us) (ty.getAppArgs.push x)

/-- `SizeOf` for a member, measuring an element by the pre-term it wraps. -/
def addSizeOfInst (numParams : Nat) (mem : Name) : MetaM Unit := do
  let mi ← getConstInfo mem
  let instName := mem ++ `_sizeOf_inst
  if (← getEnv).contains instName then return
  let us := mi.levelParams.map mkLevelParam
  forallTelescope mi.type fun binders _ => do
    mkLocalInstances (binders.extract 0 numParams) fun insts => do
      let selfTy := mkAppN (mkConst mem us) binders
      let value ← withLocalDeclD `x selfTy fun x => do
        let fn ← mkLambdaFVars #[x] (← mkAppM ``SizeOf.sizeOf #[← preOf x])
        mkLambdaFVars (binders ++ insts) (← mkAppOptM ``SizeOf.mk #[selfTy, fn])
      addDecl <| .defnDecl {
        name        := instName
        levelParams := mi.levelParams
        type        := ← mkForallFVars (binders ++ insts) (← mkAppM ``SizeOf #[selfTy])
        value
        hints       := .abbrev
        safety      := .safe
      }
  registerInstance instName .global (eval_prio default)

/--
`sizeOf (X.c ..) = 1 + sizeOf f₁ + ..`, in the form and by the reckoning Lean
uses for an ordinary constructor, so the termination tactic -- which simplifies
with these and then calls `omega` -- finds what it expects. -/
def addSizeOfSpec (numParams : Nat) (levelParams : List Name) (mem c : Name) : MetaM Unit := do
  let ci ← getConstInfo c
  let thmName := c ++ `sizeOf_spec
  if (← getEnv).contains thmName then return
  let us := levelParams.map mkLevelParam
  forallTelescope ci.type fun xs concl => do
    let ps := xs.extract 0 numParams
    let fields := xs.extract numParams xs.size
    mkLocalInstances ps fun insts => do
      let idxs := concl.getAppArgs.extract numParams concl.getAppArgs.size
      let inst := mkAppN (mkConst (mem ++ `_sizeOf_inst) us) (ps ++ idxs ++ insts)
      let ctorApp := mkAppN (mkConst c us) xs
      let lhs := mkApp3 (mkConst ``SizeOf.sizeOf [← getLevel concl]) concl inst ctorApp
      -- what the constructor actually packed, read off the pre-term it built
      let pre ← whnf (← preOf ctorApp)
      let kept := if pre.getAppFn.isConst then pre.getAppArgs else fields
      let mut rhs ← mkNumeral (mkConst ``Nat) 1
      for f in fields do
        if (← whnf (← inferType f)).isForall then continue
        let asPre ← try preOf f catch _ => pure f
        unless (← isProof f) || (← kept.anyM fun a => isDefEq a asPre <||> isDefEq a f) do
          continue
        rhs ← mkAdd rhs (← mkAppM ``SizeOf.sizeOf #[f])
      unless ← isDefEq lhs rhs do
        throwError "`sizeOf` of `{c}` is not the sum of its fields'"
      let thmParams := ps ++ insts ++ fields
      addDecl <| .thmDecl {
        name        := thmName
        levelParams := ci.levelParams
        type        := ← mkForallFVars thmParams (← mkEq lhs rhs)
        value       := ← mkLambdaFVars thmParams (← mkEqRefl rhs)
      }
  let simpAttr ← ofExcept <| getAttributeImpl (← getEnv) `simp
  simpAttr.add thmName default .global

/--
How many of `mem`'s indices its view must take as parameters: everything up to
and including the last index some constructor supplies a proof for, since a
pattern cannot bind that proof and a parameter cannot depend on an index. -/
private def promoted (numParams : Nat) (ctors : Array Name)
    (binders : Array Expr) : MetaM Nat := do
  let mut k := 0
  for j in *...(binders.size - numParams) do
    if ← isProof binders[numParams + j]! then k := j + 1
  if k == 0 then return 0
  for c in ctors do
    let pinned ← forallTelescope (← getConstInfo c).type fun xs concl => do
      let fs := xs.extract numParams xs.size
      let is := concl.getAppArgs.extract numParams concl.getAppArgs.size
      let mut p := 0
      for j in *...(min fs.size is.size) do
        unless is[j]! == fs[j]! && (← fs[j]!.fvarId!.getBinderInfo).isExplicit do break
        p := j + 1
      pure p
    if pinned < k then return 0
  return k

/-- The view of `mem`, and the function into it. -/
def addView (numParams : Nat) (mem : Name) (ctors : Array Name) : MetaM Unit := do
  let mi ← getConstInfo mem
  let lps := mi.levelParams
  let us := lps.map mkLevelParam
  let vName := viewName mem
  let vCtor (c : Name) : Name := c.replacePrefix mem vName
  forallTelescope mi.type fun binders sort => do
    let .sort v := sort | throwError "`{mem}` does not end at a sort"
    let k ← promoted numParams ctors binders
    let mut big := Level.max (.succ .zero) v
    for c in ctors do
      big ← forallTelescope (← getConstInfo c).type fun xs _ => do
        let mut w := big
        for x in xs.extract (numParams + k) xs.size do
          w := .max w (← getLevel (← inferType x))
        return w
    let v' := big.normalize
    let ps := binders.extract 0 numParams
    let is := binders.extract numParams binders.size
    let selfTy := mkAppN (mkConst mem us) binders
    let viewTy ← withLocalDeclD `x selfTy fun x => mkForallFVars (binders.push x) (.sort v')
    let mut vctors := #[]
    for c in ctors do
      let ty ← forallTelescope (← getConstInfo c).type fun xs concl => do
        let cis := concl.getAppArgs.extract numParams concl.getAppArgs.size
        let args := xs.extract 0 (numParams + k) ++ cis.extract k cis.size
          |>.push (mkAppN (mkConst c us) xs)
        mkForallFVars xs (mkAppN (mkConst vName us) args)
      vctors := vctors.push { name := vCtor c, type := implicitUpTo (numParams + k) ty }
    addInd lps (numParams + k) #[{ name := vName, type := viewTy, ctors := vctors.toList }]
      (genSizeOf := false)
    -- the function is built by hand rather than by the equation compiler, which
    -- is the thing that does not work here yet
    let cdName := mem ++ `casesD
    let some cd := (← getEnv).find? cdName | throwError "no `{cdName}` to see through"
    unless cd.levelParams.length == lps.length + 1 do
      throwError "`{cdName}` does not eliminate into a sort of its own"
    withLocalDeclD `x selfTy fun x => do
      let motive ← mkLambdaFVars (is.push x) (mkAppN (mkConst vName us) (binders.push x))
      let mut minors := #[]
      for c in ctors do
        minors := minors.push <| ←
          forallTelescope (← instantiateForall (← getConstInfo c).type ps) fun fs _ =>
            mkLambdaFVars fs (mkAppN (mkConst (vCtor c) us) (ps ++ fs))
      let value := mkAppN (mkConst cdName (v' :: us)) (ps ++ #[motive] ++ minors ++ is ++ #[x])
      let ty ← mkForallFVars (binders.push x) (mkAppN (mkConst vName us) (binders.push x))
      addDef (viewFnName mem) lps (implicitUpTo binders.size ty)
        (← mkLambdaFVars (binders.push x) value)
      modifyEnv (viewedExt.addEntry · (mem, ctors))

/--
Give every member encoded as a subtype a `SizeOf` instance, its specification
lemmas, and a view, in three passes so a constructor whose field is a sibling
finds the sibling's instance already there. -/
def addViews (numParams : Nat) (members : Array (Name × Array Name)) : MetaM Unit := do
  let members ← members.filterM fun (_, ctors) => do
    let some c := ctors[0]? | return false
    return !((← getEnv).find? c).any (·.isCtor)
  for (mem, _) in members do
    discard <| attempt? `Mumi.view m!"no `sizeOf` for `{mem}`" <| addSizeOfInst numParams mem
  for (mem, ctors) in members do
    let lps := (← getConstInfo mem).levelParams
    for c in ctors do
      discard <| attempt? `Mumi.view m!"no `sizeOf` lemma for `{c}`" <|
        addSizeOfSpec numParams lps mem c
  for (mem, ctors) in members do
    discard <| attempt? `Mumi.view m!"no view for `{mem}`" <| addView numParams mem ctors

end Mumi
