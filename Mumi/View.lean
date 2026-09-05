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

An induction-inductive member is emitted as a definition over a subtype: `Ctx`
is `Subtype Ctx._wf`, and `Ctx.snoc` is a definition that packs a
`Ctx._pre.snoc` next to a proof that the pre-term is well formed.  Everything a
writer states about the block is stated in those names and reads exactly as
written, and `induction` and `cases` are driven by the eliminators step 10 of
the emit adds.  `match` is the one thing that does not go through.

It cannot.  The equation compiler asks the discriminant's type for an inductive
by reducing it, so it always arrives at `Subtype`, and the constructors --
`@[match_pattern]` definitions -- unfold on the way in.  `Ctx.snoc Γ h` becomes
`⟨Γ.val.snoc, _⟩`, whose `Γ` is under a projection and so no longer a pattern
variable, and `Tm.var Γ h` becomes `⟨Tm._pre.var, True.intro⟩`, which has lost
its arguments altogether.  There is no hook to point the compiler somewhere
else with: `Lean.Meta.Match` reduces the type itself and takes what it finds.

So the member is given something to be matched *through*.  A **view** is a
genuine inductive over the member, indexed by it, with one constructor per
constructor of the member concluding at that constructor's value:

```lean
inductive Ctx.View : Ctx → Type where
  | nil : Ctx.View .nil
  | snoc (Γ : Ctx) (h : Ok Γ) : Ctx.View (.snoc Γ h)
```

This is legal where the member's own declaration was not, because `Ctx` is
already there to be indexed by, and nothing in the view is recursive.  A case
split on `Ctx.View c` refines `c` to the constructor in its index, so matching
`c` alongside `c.view` gives back exactly the alternatives that were written.
`Mumi.MatchView` is the rewrite that does that; this module builds what it
needs.

## Indices that are proofs

A constructor may take a proof of an index as a field -- `Tm.var (Γ : Ctx) (h :
Ok Γ) : Tm Γ h` -- and a pattern may not bind one: Lean has no way to state
that the proof in the index and the proof in the field are the same, and gives
up with a metavariable where the field should be.  This is not particular to
this library; a hand-written `inductive T : (n : Nat) → P n → Type` fails the
same way.

What Lean's own `cases` does is refuse to offer the field at all, and the view
can say that in its shape.  Making the leading indices **parameters** of the
view drops their fields from its constructors, and since a parameter may not
depend on an index, promoting a proof index promotes everything before it:

```lean
inductive Tm.View (Γ : Ctx) (h : Ok Γ) : Tm Γ h → Type where
  | var : Tm.View Γ h (.var Γ h)
  | wk (t : Tm Γ h) : Tm.View Γ h (.wk Γ h t)
```

The writer names `Γ` and `h` where the discriminant is, not in the pattern,
which is what `cases` presents too.

## Recursion

A definition by recursion over a member cannot be structural: `Subtype Ctx._wf`
has no `brecOn`, and the view is not recursive.  It can be well founded, given
a `SizeOf` instance to measure with and the specification lemmas the termination
tactic simplifies with, so those are built here as well.  The measure is the
pre-term's, which is the only thing left after the proofs are erased and is
exactly the size of what was written.
-/

namespace Mumi

open Lean Meta Lean.Elab.MultiuniverseInductive

initialize registerTraceClass `Mumi.view (inherited := true)

/-- The inductive that presents `mem`'s constructors as constructors. -/
def viewName (mem : Name) : Name := mem ++ `View

/-- The function that takes an element of `mem` to its view. -/
def viewFnName (mem : Name) : Name := mem ++ `view

/--
Every member a view was built for, so that the rewrite `match` goes through can
step aside without looking at anything in a file that has no such member -- and
so that what it recognises is what this library made, not anything that happens
to be spelled the same way.

`ctors` holds the last component of each of their constructors' names, which is
all a `match` can be recognised by before anything has been elaborated.  It is
what the rewrite reads first, and the whole of the cost it puts on a `match` it
has no business with.
-/
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
Make the first `n` binders of a telescope implicit, leaving the ones that are
already inferred some other way as they are.

The view's promoted indices arrive as explicit fields of a constructor and
leave as parameters, and a parameter is not written at a use site.
-/
private partial def implicitUpTo (n : Nat) (e : Expr) : Expr :=
  match n, e with
  | 0, e => e
  | n + 1, .forallE nm t b bi =>
    .forallE nm t (implicitUpTo n b) (if bi.isExplicit then .implicit else bi)
  | _, e => e

/-- The pre-term inside a member's element, which is what it is measured by. -/
private def preOf (x : Expr) : MetaM Expr := do
  let ty ← whnf (← inferType x)
  let .app (.app (.const ``Subtype [u]) α) p := ty
    | throwError "`{← inferType x}` is not a subtype"
  return mkApp3 (mkConst ``Subtype.val [u]) α p x

/--
`SizeOf` for a member, measuring an element by the pre-term it wraps.

Not compiled, exactly as Lean does not compile the instances it generates for
an ordinary inductive: `sizeOf` is there for termination proofs, which are
erased, and a definition by well-founded recursion is compiled from its
unfolding and never asks for the measure.
-/
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
`sizeOf (X.c ..) = 1 + sizeOf f₁ + ..`, in the same form and by the same
reckoning Lean uses for an ordinary constructor, so that the termination
tactic -- which simplifies with these and then calls `omega` -- finds what it
expects to find.

The sum runs over the fields the pre-constructor kept, which is what the
measure is really counting.  A field that is a proof stays in, contributing
zero, so that the statement reads like the one an ordinary block would get; a
field that is an *index* supplied at the constructor does not, because the
pre-term has no room for it.  `Tm.wk (Γ : Ctx) (h : Ok Γ) (t : Tm Γ h)` is
measured by `t` alone, and a recursion that shrinks only the context it is
written in will have to say what it decreases by itself.
-/
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
How many of `mem`'s indices its view has to take as parameters.

Everything up to and including the last index a constructor supplies a proof
for, since a pattern cannot bind that proof and a parameter cannot depend on an
index.  A constructor that does not pin those indices to its own leading fields
-- in order, and explicitly -- has nothing for the view to take them from, and
then nothing is promoted and that one constructor is the only one that will not
match.
-/
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

/--
The view of `mem`, and the function into it.

The view lives at the member's own sort, raised away from `Prop` -- a case
split on a proof tells you nothing -- and the function is the member's `casesD`
with the view for a motive, so it computes: matching through a view costs a
constructor tag and nothing else.
-/
def addView (numParams : Nat) (mem : Name) (ctors : Array Name) : MetaM Unit := do
  let mi ← getConstInfo mem
  let lps := mi.levelParams
  let us := lps.map mkLevelParam
  let vName := viewName mem
  let vCtor (c : Name) : Name := c.replacePrefix mem vName
  forallTelescope mi.type fun binders sort => do
    let .sort v := sort | throwError "`{mem}` does not end at a sort"
    let k ← promoted numParams ctors binders
    let v' := (Level.max (.succ .zero) v).normalize
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
Give every member that is encoded as a subtype a `SizeOf` instance, the
specification lemmas that go with it, and a view, in three passes so that a
constructor whose field is a sibling finds the sibling's instance already
there.  A member that kept a real inductive of its own -- one the block could
be split around -- needs none of this and is left alone.  Each piece is traced
and dropped on failure: what it costs is `match`, not the block.
-/
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
