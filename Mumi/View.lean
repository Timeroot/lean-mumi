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
this module builds what it needs.  A member with a constructor the writer has at
the original of a `Prop` copy is matched the same way, for the same reason --
the kernel's constructor holds what the writer's was given packed -- and its
view's function is a case split on the kernel's inductive
(`Mumi.Public.publishAliased`).

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
no way to write the motive of one.  A call that descends through a *nesting* is
not structural either, for the same reason it is not in plain Lean.  Both are
still well founded given a `SizeOf` instance to measure with and the
specification lemmas the termination tactic simplifies with, so this module
builds those too.  The measure is the pre-term's size, which is what remains
after the proofs are erased and is exactly the size of what was written.

A field the block denested is packed as a copy of its container, so the
specification lemma states the copy's size where the field's is wanted.  The two
are equal, but only provably: they agree on a constructor by computation apart
from the container's recursive positions.  `sizeOf_ofOrig` closes that gap by
induction over the container, one lemma per copy, and the specification lemma is
proved by rewriting with it rather than by `rfl`.
-/

namespace Mumi

open Lean Meta Lean.Elab Lean.Elab.MultiuniverseInductive

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

/-- How many of the copy's pre-type's indices are locals the copy is taken at, rather
than indices of what it copies; `0` for anything that is not a copy. -/
private def copyLocals (pre : Name) : MetaM Nat := do
  let copy := pre.getPrefix
  let some (.defnInfo oi) := (← getEnv).find? (copy ++ `ofOrig) | return 0
  let .inductInfo pi ← getConstInfo pre | return 0
  forallTelescope oi.type fun xs _ => do
    let some a := xs.back? | return 0
    let some orig := (← whnf (← inferType a)).getAppFn.constName? | return 0
    let .inductInfo ii ← getConstInfo orig | return 0
    return pi.numIndices - ii.numIndices

/--
A measure of a pre-block one of whose copies is taken at a local.  Such a copy's
constructors store that local, since its pre-type is indexed by it, so Lean's measure
counts it at every node: `[]` at `n` has size `1 + sizeOf n` as a copy and `1` as a list,
and no statement of the copy's size at the original can be true.  This one counts what
was written: Lean's sum over the fields, with what a copy stores for its locals left out.
Registered after Lean's, it is the instance everything here finds.  A pre-block with no
such copy keeps Lean's. -/
def addPreMeasure (pre : Name) : MetaM Unit := do
  let .inductInfo first ← getConstInfo pre | return
  let inst (m : Name) : Name := m ++ `_measure_inst
  if (← getEnv).contains (inst first.all.head!) then return
  let locals ← first.all.toArray.mapM copyLocals
  unless locals.any (· > 0) do return
  let all := first.all.toArray
  let .recInfo rv ← getConstInfo (pre ++ `rec) | return
  let us := first.levelParams.map mkLevelParam
  -- the recursor's level for the sort of the motive comes first, where it has one
  let recLvls := if rv.levelParams.length == first.levelParams.length + 1 then
    Level.succ .zero :: us else us
  for h : k in *...all.size do
    let m := all[k]
    let mi ← getConstInfo m
    forallTelescope mi.type fun binders _ => do
      let ps := binders.extract 0 rv.numParams
      let idxs := binders.extract rv.numParams binders.size
      mkLocalInstances ps fun insts => do
        let selfTy := mkAppN (mkConst m us) binders
        let recFn := mkAppN (mkConst (m ++ `rec) recLvls) ps
        let motiveTys ← forallBoundedTelescope (← inferType recFn) rv.numMotives
          fun ms _ => ms.mapM inferType
        let motives ← motiveTys.mapM fun ty =>
          forallTelescope ty fun ys _ => mkLambdaFVars ys (mkConst ``Nat)
        let mut app := mkAppN recFn motives
        let ctors := (← all.mapM fun n => do
          return ((← getConstInfoInduct n).ctors.toArray.map (n, ·))).flatMap id
        for (owner, cn) in ctors do
          let .forallE _ minorTy _ _ ← whnf (← inferType app)
            | throwError "`{m}.rec` takes fewer cases than `{m}` has constructors"
          let cv ← getConstInfoCtor cn
          let nLocals := locals[all.idxOf owner]!
          app := mkApp app <| ← forallTelescope minorTy fun ys _ => do
            let fields := ys.extract 0 cv.numFields
            let ihs := ys.extract cv.numFields ys.size
            -- what this constructor stores for its member's locals
            let concl ← forallBoundedTelescope (cv.type.instantiateLevelParams cv.levelParams
              (us)) (rv.numParams + cv.numFields) fun zs c => do
                return c.replaceFVars zs (ps ++ fields)
            let stored := (concl.getAppArgs.extract rv.numParams
              (rv.numParams + nLocals)).filter (·.isFVar)
            let mut rhs ← mkNumeral (mkConst ``Nat) 1
            let mut nextIh := 0
            for f in fields do
              let fty ← whnf (← inferType f)
              let recursive := fty.getAppFn.constName?.any all.contains
              let ih? := if recursive then ihs[nextIh]? else none
              if recursive then nextIh := nextIh + 1
              -- as Lean's measure does, a function counts for nothing
              if fty.isForall then
                if (← forallTelescope fty fun _ b => do
                    return (← whnf b).getAppFn.constName?.any all.contains) then
                  nextIh := nextIh + 1
                continue
              if stored.contains f then continue
              rhs ← mkAdd rhs (← match ih? with
                | some ih => pure ih
                | none => mkAppM ``SizeOf.sizeOf #[f])
            mkLambdaFVars ys rhs
        -- the remaining minors are consumed above, so what is left is the major
        let fnName := m ++ `_measure
        withLocalDeclD `x selfTy fun x => do
          let value := mkAppN app (idxs.push x)
          let all' := ps ++ insts ++ idxs.push x
          addDecl <| .defnDecl {
            name := fnName, levelParams := mi.levelParams, type := ← mkForallFVars all' (mkConst ``Nat)
            value := ← mkLambdaFVars all' value, hints := .abbrev, safety := .safe }
          let fn ← mkLambdaFVars #[x] (mkAppN (mkConst fnName us) all')
          let v ← mkLambdaFVars (ps ++ insts ++ idxs) (← mkAppOptM ``SizeOf.mk #[selfTy, fn])
          addDecl <| .defnDecl {
            name := inst m, levelParams := mi.levelParams
            type := ← mkForallFVars (ps ++ insts ++ idxs) (← mkAppM ``SizeOf #[selfTy])
            value := v, hints := .abbrev, safety := .safe }
          registerInstance (inst m) .global (eval_prio default)

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
A proof of `target' = target`, where `target'` is `target` with the right side of
every equation in `eqs` put back to its left side.  An equation that matches
nothing is skipped. -/
private def rewriteBack (target : Expr) (eqs : Array Expr) : MetaM Expr := do
  let mut cur := target
  let mut proof ← mkEqRefl target
  for h in eqs do
    let some (α, a, b) := (← instantiateMVars (← inferType h)).eq? | continue
    let abst ← kabstract cur b
    unless abst.hasLooseBVars do continue
    proof ← mkEqTrans (← mkCongrArg (.lam `n α abst .default) h) proof
    cur := abst.instantiate1 a
  return proof

/-- Every application of an `ofOrig` in `e`, each at its full spine. -/
private partial def ofOrigApps (e : Expr) : Array Expr := visit e #[]
where
  /-- Collect from `e` into `acc`. -/
  visit (e : Expr) (acc : Array Expr) : Array Expr :=
    match e with
    | .app .. =>
      let acc := match e.getAppFn with
        | .const (.str _ "ofOrig") _ => acc.push e
        | _ => acc
      e.getAppArgs.foldl (init := acc) fun acc a => visit a acc
    | .lam _ t b _ | .forallE _ t b _ => visit b (visit t acc)
    | .letE _ t v b _ => visit b (visit v (visit t acc))
    | .mdata _ b | .proj _ _ b => visit b acc
    | _ => acc

/-- The right side of `e`, if `e` is an equation. -/
private def rhsOf? (e : Expr) : MetaM (Option Expr) := do
  return (← instantiateMVars e).eq?.map (·.2.2)

/-- What Lean states of the size of `app`, a constructor `cn` applied, if it does. -/
private def ctorSizeSpec? (cn : Name) (app : Expr) : MetaM (Option Expr) := do
  unless (← getEnv).contains (cn ++ `sizeOf_spec) do return none
  try
    let f ← mkConstWithFreshMVarLevels (cn ++ `sizeOf_spec)
    let (ms, _, body) ← forallMetaTelescope (← inferType f)
    let some (_, lhs, _) := body.eq? | return none
    unless ← isDefEq lhs (← mkAppM ``SizeOf.sizeOf #[app]) do return none
    let spec ← instantiateMVars (mkAppN f ms)
    return if spec.hasMVar then none else some spec
  catch _ => return none

/-- What Lean reckons the size of `app`, a constructor `cn` applied, to be, as a sum
over its fields. -/
private def ctorSizeSum (cn : Name) (app : Expr) (fields : Array Expr) : MetaM Expr := do
  if let some spec ← ctorSizeSpec? cn app then
    if let some rhs ← rhsOf? (← inferType spec) then return rhs
  let mut rhs ← mkNumeral (mkConst ``Nat) 1
  for f in fields do
    if (← isProof f) || (← whnf (← inferType f)).isForall then continue
    rhs ← mkAdd rhs (← mkAppM ``SizeOf.sizeOf #[f])
  return rhs

/-- `ofOrig t` of the copy beside `copy` that takes `t`, and that copy: `copy` if it
does, else whichever `root.nested_C_k` there is of the inductive `t` is a type of. -/
private def copyTaking? (copy : Name) (t : Expr) : MetaM (Option (Name × Expr)) := do
  let tryCopy (c : Name) : MetaM (Option (Name × Expr)) := do
    let f ← mkConstWithFreshMVarLevels (c ++ `ofOrig)
    let (ms, _, _) ← forallMetaTelescope (← inferType f)
    let some m := ms.back? | return none
    unless ← isDefEq (← inferType m) (← inferType t) do return none
    return some (c, ← instantiateMVars (mkApp (mkAppN f ms.pop) t))
  if let some r ← tryCopy copy then return some r
  let .const (.str _ short) _ := (← whnf (← inferType t)).getAppFn | return none
  let root := copy.getPrefix
  -- the suffix counts the block's copies, of whatever inductive
  let mut k := 1
  let mut misses := 0
  while misses < 64 do
    let c := root ++ Name.mkSimple s!"nested_{short}_{k}"
    k := k + 1
    if (← getEnv).contains (c ++ `ofOrig) then
      misses := 0
      if let some r ← tryCopy c then return some r
    else
      misses := misses + 1
  return none

mutual

/--
`sizeOf (X.nested_C_k.ofOrig a).val = sizeOf a`: a denested copy of a container
measures the same as the container it copies.  The two agree on a constructor by
computation apart from the recursive positions, which is what the induction
supplies.

The induction is the container's own recursor.  Where the container is itself nested
or mutual that recursor has a motive for each of its block's types, and each of those
says the same of the copy taking that type: `Rose RT`'s says it of the copy of
`Rose RT`, and the motive for its `List (Rose RT)` of the copy of that.  A type of the
block with no copy is one nothing here reaches, so its motive claims nothing. -/
partial def addOfOrigSizeOf (copy : Name) : MetaM Unit := do
  let thmName := copy ++ `sizeOf_ofOrig
  if (← getEnv).contains thmName then return
  let ofOrig := copy ++ `ofOrig
  let oi ← getConstInfo ofOrig
  let us := oi.levelParams.map mkLevelParam
  forallTelescope oi.type fun xs _ => do
    let some a := xs.back? | throwError "`{ofOrig}` takes nothing to copy"
    let bs := xs.pop
    -- a parameter is measured by whatever instance the use has for it
    mkLocalInstances bs fun insts => do
    let origTy ← whnf (← inferType a)
    let some orig := origTy.getAppFn.constName? | throwError "`{ofOrig}` copies no inductive"
    let .inductInfo ii ← getConstInfo orig | throwError "`{orig}` is not an inductive"
    let .recInfo rv ← getConstInfo (orig ++ `rec) | throwError "`{orig}` has no recursor"
    let origLvls := origTy.getAppFn.constLevels!
    let args := origTy.getAppArgs
    let params := args.extract 0 rv.numParams
    let idxs := args.extract rv.numParams (rv.numParams + rv.numIndices)
    -- a copy is taken at one index at a time, so the index is a binder of
    -- `ofOrig`, and the statement is what that binder is generalised over
    for i in idxs do
      unless bs.contains i do throwError "`{ofOrig}` copies at a fixed index"
    let sizeEq (app t : Expr) : MetaM Expr := do
      mkEq (← mkAppM ``SizeOf.sizeOf #[← preOf app]) (← mkAppM ``SizeOf.sizeOf #[t])
    let recFn := mkConst (orig ++ `rec)
      (if rv.levelParams.length == ii.levelParams.length + 1 then Level.zero :: origLvls
       else origLvls)
    let motiveTys ← forallBoundedTelescope (← instantiateForall (← inferType recFn) params)
      rv.numMotives fun ms _ => ms.mapM inferType
    -- the copies this induction speaks of; any other has a lemma of its own
    let mut here := #[copy]
    let mut motives := #[]
    for ty in motiveTys do
      let (m, c?) ← forallTelescope ty fun ys _ => do
        let some t := ys.back? | throwError "`{orig}.rec` has a motive of no major"
        match ← copyTaking? copy t with
        | some (c, app) => return (← mkLambdaFVars ys (← sizeEq app t), some c)
        | none => return (← mkLambdaFVars ys (mkConst ``True), none)
      motives := motives.push m
      if let some c := c? then
        unless here.contains c do here := here.push c
    let group := here
    let mut app := mkAppN recFn (params ++ motives)
    for _ in *...rv.numMinors do
      let .forallE _ minorTy _ _ ← whnf (← inferType app)
        | throwError "`{orig}.rec` takes fewer cases than it has constructors"
      app := mkApp app <| ← forallTelescope minorTy fun ys concl => do
        let concl := concl.headBeta
        if concl.isConstOf ``True then return ← mkLambdaFVars ys (mkConst ``True.intro)
        let some (_, lhs, rhs) := concl.eq?
          | throwError "`{orig}.rec` has a case of something else"
        let ctorApp := rhs.appArg!
        let .const cn _ := ctorApp.getAppFn | throwError "`{orig}.rec` has a case of no constructor"
        let cv ← getConstInfoCtor cn
        let fields := ys.extract 0 cv.numFields
        let pre ← whnf lhs.appArg!
        let eqs := ys.extract cv.numFields ys.size ++ (← transportsIn pre group)
        let proof ← rewriteBack (← ctorSizeSum cn ctorApp fields) eqs
        -- the container's own measure of a nested constructor is a sum only by Lean's lemma
        let proof ← match ← ctorSizeSpec? cn ctorApp with
          | some spec => mkEqTrans proof (← mkEqSymm spec)
          | none => pure proof
        unless ← isDefEq (← inferType proof) concl do
          throwError "the copy `{copy}` does not measure `{cn}` the way `{orig}` does"
        mkLambdaFVars ys (← mkExpectedTypeHint proof concl)
    addDecl <| .thmDecl {
      name        := thmName
      levelParams := oi.levelParams
      type        := ← mkForallFVars (bs ++ insts ++ #[a]) (← sizeEq (mkAppN (mkConst ofOrig us) xs) a)
      value       := ← mkLambdaFVars (bs ++ insts ++ #[a]) (mkAppN app (idxs.push a))
    }

/--
An equation `sizeOf (ofOrig ..) = sizeOf ..` for every copy `pre` was built through
other than those in `here`, which the induction in progress answers for: the copy's
own lemma, emitted on demand. -/
partial def transportsIn (pre : Expr) (here : Array Name) : MetaM (Array Expr) := do
  let mut out := #[]
  for app in ofOrigApps pre do
    let some n := app.getAppFn.constName? | continue
    let copy := n.getPrefix
    unless here.contains copy do
      addOfOrigSizeOf copy
      let thm := mkConst (copy ++ `sizeOf_ofOrig) app.getAppFn.constLevels!
      let args := app.getAppArgs
      -- the copy's binders, the instances for them as they are here, and the argument
      let (ms, _, _) ← forallMetaTelescope (← inferType thm)
      let nb := args.size - 1
      for k in *...nb do ms[k]!.mvarId!.assign args[k]!
      ms.back!.mvarId!.assign args.back!
      for m in ms.extract nb (ms.size - 1) do
        m.mvarId!.assign (← synthInstance (← instantiateMVars (← inferType m)))
      out := out.push (← instantiateMVars (mkAppN thm ms))
  return out

end

/--
`sizeOf (X.c ..) = 1 + sizeOf f₁ + ..`, in the form and by the reckoning Lean
uses for an ordinary constructor, so the termination tactic -- which simplifies
with these and then calls `omega` -- finds what it expects.  A field the block
denested is measured at the copy, which is the same size but only provably so,
so the proof is a rewrite rather than `rfl`. -/
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
      -- a field the block denested is packed as a copy of itself, so it is the
      -- copy's argument that appears rather than the field
      let copied := (ofOrigApps pre).filterMap fun a => if a.isApp then some a.appArg! else none
      let kept := (if pre.getAppFn.isConst then pre.getAppArgs else fields) ++ copied
      let mut rhs ← mkNumeral (mkConst ``Nat) 1
      for f in fields do
        if (← whnf (← inferType f)).isForall then continue
        let asPre ← try preOf f catch _ => pure f
        unless (← isProof f) || (← kept.anyM fun a => isDefEq a asPre <||> isDefEq a f) do
          continue
        rhs ← mkAdd rhs (← mkAppM ``SizeOf.sizeOf #[f])
      let mut proof ← mkEqRefl rhs
      unless ← isDefEq lhs rhs do
        proof ← rewriteBack rhs (← transportsIn pre #[])
        let some (_, lhs', _) := (← instantiateMVars (← inferType proof)).eq?
          | throwError "`sizeOf` of `{c}` is not the sum of its fields'"
        unless ← isDefEq lhs lhs' do
          throwError "`sizeOf` of `{c}` is not the sum of its fields'"
      let thmParams := ps ++ insts ++ fields
      addDecl <| .thmDecl {
        name        := thmName
        levelParams := ci.levelParams
        type        := ← mkForallFVars thmParams (← mkEq lhs rhs)
        value       := ← mkLambdaFVars thmParams proof
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

/-- The view of `mem`, and the function into it.  The function is a case split
by `X.casesD` unless `fnValue?` builds it, from `mem`'s binders, the element and
the view's motive at them. -/
def addView (numParams : Nat) (mem : Name) (ctors : Array Name)
    (fnValue? : Option (Array Expr → Expr → Expr → MetaM Expr) := none) : MetaM Unit := do
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
    if fnValue?.isNone then
      let some cd := (← getEnv).find? cdName | throwError "no `{cdName}` to see through"
      unless cd.levelParams.length == lps.length + 1 do
        throwError "`{cdName}` does not eliminate into a sort of its own"
    withLocalDeclD `x selfTy fun x => do
      let motive ← mkLambdaFVars (is.push x) (mkAppN (mkConst vName us) (binders.push x))
      let value ← match fnValue? with
        | some f => f binders x motive
        | none => do
          let mut minors := #[]
          for c in ctors do
            minors := minors.push <| ←
              forallTelescope (← instantiateForall (← getConstInfo c).type ps) fun fs _ =>
                mkLambdaFVars fs (mkAppN (mkConst (vCtor c) us) (ps ++ fs))
          pure <| mkAppN (mkConst cdName (v' :: us)) (ps ++ #[motive] ++ minors ++ is ++ #[x])
      let ty ← mkForallFVars (binders.push x) (mkAppN (mkConst vName us) (binders.push x))
      addDef (viewFnName mem) lps (implicitUpTo binders.size ty)
        (← mkLambdaFVars (binders.push x) value)
      modifyEnv (viewedExt.addEntry · (mem, ctors))

/-! ## The declarations an `inductive` answers to

A member erased to a subtype is a definition, so Lean builds none of the
auxiliary declarations it builds beside an `inductive`.  They are added here out
of what the block already has and out of the view's, which are Lean's own: the
view is a genuine inductive, so Lean generated its `noConfusion`.

* `X.casesOn` and `X.recOn` permute the telescope of `X.casesD` and `X.rec`, by
  the permutation `Lean.mkRecOn` applies to a recursor;
* `X.noConfusionType` and `X.noConfusion` restate the view's along `X.view`;
* `X.ctorIdx` counts through the view.

`injection` and `contradiction` are not among what this reaches.  Both reduce
the type of the equation before they look for a `noConfusion`, so both arrive at
`X._sub` and use its.  `simp` and `X.c.inj` state the same thing about the
member.
-/

/--
Apply `f` to `args` at its explicit positions and infer the rest, from `args`
and from what the application is expected to conclude at. -/
private def appExplicit (f : Expr) (args : Array Expr) (expected? : Option Expr := none) :
    MetaM Expr := do
  let (mvs, bis, concl) ← forallMetaTelescope (← inferType f)
  if let some expected := expected? then
    unless ← isDefEq concl expected do
      throwError "`{f}` does not conclude at `{expected}`"
  let mut k := 0
  for i in *...mvs.size do
    unless bis[i]!.isExplicit do continue
    unless k < args.size do throwError "`{f}` takes more explicit arguments than {args.size}"
    unless ← isDefEq mvs[i]! args[k]! do
      throwError "`{f}` does not take `{args[k]!}` at argument {i}"
    k := k + 1
  unless k == args.size do throwError "`{f}` takes only {k} explicit arguments"
  instantiateMVars (mkAppN f mvs)

/-- Reset the name and the annotation of each `∀`-binder from `f`, outermost first. -/
private partial def annotate (f : Nat → Name → BinderInfo → Name × BinderInfo) (e : Expr)
    (i : Nat := 0) : Expr :=
  match e with
  | .forallE n d b bi =>
    let (n, bi) := f i n bi
    .forallE n d (annotate f b (i + 1)) bi
  | e => e

/-- The reshaping that renames nothing and infers every binder but those at `keep`. -/
private def inferredBut (keep : Nat → Bool) (i : Nat) (nm : Name) (bi : BinderInfo) :
    Name × BinderInfo :=
  (nm, if keep i then .default else if bi.isExplicit then .implicit else bi)

/--
Where the minor premises of an eliminator start, which is after its parameters
and its motives.  A motive is a binder whose type ends at a sort, and the motives
are the run of them that follows the parameters.  The parameters are counted
rather than matched, because a parameter can end at a sort too.

Matching a single sort is not enough: the motives of one block need not all end
at the same one.  A `Prop` member never large-eliminates, so its motive ends at
`Prop` while a data member's ends at the sort the eliminator is generic in. -/
private def minorsStart (numParams : Nat) (xs : Array Expr) (numIndices : Nat) : MetaM Nat := do
  let mut start := numParams
  for i in numParams...(xs.size - numIndices - 1) do
    let isMotive ← forallTelescopeReducing (← inferType xs[i]!) fun _ concl => pure concl.isSort
    unless isMotive do break
    start := i + 1
  if start == numParams then throwError "no motive among the binders of the eliminator"
  return start

/--
The name of the motive `X.rec` takes for member `mem`: the one whose major
premise is of `mem`'s type. -/
def motiveNameOf? (numParams : Nat) (mem : Name) : MetaM (Option Name) := do
  let some info := (← getEnv).find? (mem ++ `rec) | return none
  forallTelescope info.type fun xs _ => do
    for x in xs[numParams...xs.size] do
      let d ← x.fvarId!.getDecl
      let found ← forallTelescope d.type fun ys concl => do
        unless concl.isSort do return false
        let some y := ys.back? | return false
        return (← inferType y).getAppFn.constName? == some mem
      if found then return some d.userName
    return none

/--
`X.casesOn` from `X.casesD`, or `X.recOn` from `X.rec`: the same eliminator with
the indices and the major premise moved in front of the minor premises.

The result is not tagged as an auxiliary recursor, which is the one place this
departs from `Lean.mkRecOn`.  The code generator turns an application of a tagged
`casesOn` into a case split over the constructors of an inductive, and the member
is not one, so a tagged `X.casesOn` is uncompilable at every use site.  Untagged
it is a reducible definition ending at `X.casesD`, which does compile, and
`induction ... using` reads the case names off its minor premises either way. -/
def addMajorFirst (numParams : Nat) (mem src dst : Name) : MetaM Unit := do
  if (← getEnv).contains dst then return
  let mi ← getConstInfo mem
  let numIndices ← forallTelescope mi.type fun bs _ => pure (bs.size - numParams)
  let some info := (← getEnv).find? src | throwError "no `{src}` to reorder"
  let us := info.levelParams.map mkLevelParam
  -- a one-motive eliminator names its motive as the block's recursor names
  -- this member's, as Lean's `casesOn` does
  let motiveName? ← motiveNameOf? numParams mem
  let (type, value) ← forallTelescope info.type fun xs concl => do
    let start ← minorsStart numParams xs numIndices
    unless start + numIndices + 1 ≤ xs.size do
      throwError "`{src}` ends before its {numIndices} indices and its major premise"
    let numMinors := xs.size - start - numIndices - 1
    let vs := xs[*...start] ++ xs[(start + numMinors)...xs.size] ++
      xs[start...(start + numMinors)]
    let type ← mkForallFVars vs concl
    let type := match motiveName? with
      | some n => if start == numParams + 1 then
          annotate (fun i nm bi => (if i == numParams then n else nm, bi)) type else type
      | none => type
    return (type, ← mkLambdaFVars vs (mkAppN (mkConst src us) xs))
  addDef dst info.levelParams type value (hints := .abbrev)
  setReducibleAttribute dst
  modifyEnv fun env => addProtected env dst

/-- `X.ctorIdx`: the pre-term's, which any constructor computes, its head being there
whatever its fields' round trips do; through the view where there is no pre-term. -/
def addCtorIdx (mem : Name) : MetaM Unit := do
  let dst := mem ++ `ctorIdx
  if (← getEnv).contains dst then return
  let mi ← getConstInfo mem
  let us := mi.levelParams.map mkLevelParam
  forallTelescope mi.type fun bs _ =>
    withLocalDeclD `x (mkAppN (mkConst mem us) bs) fun x => do
      let preIdx := mem ++ `_pre ++ `ctorIdx
      let value ← if (← getEnv).contains preIdx then
          appExplicit (← mkConstWithFreshMVarLevels preIdx) #[← preOf x]
        else
          let view := mkAppN (mkConst (viewFnName mem) us) (bs.push x)
          appExplicit (← mkConstWithFreshMVarLevels (viewName mem ++ `ctorIdx)) #[view]
      let xs := bs.push x
      addDef dst mi.levelParams
        (annotate (inferredBut (· == bs.size)) (← mkForallFVars xs (mkConst ``Nat)))
        (← mkLambdaFVars xs value)
      modifyEnv fun env => addProtected env dst

/-- `X.ctorIdx_c : X.ctorIdx (X.c …) = i` for each constructor, by `rfl`: what says which
constructor a term is, to whatever cannot tell by looking (`Mumi.CtorTactics`). -/
def addCtorIdxRules (mem : Name) (ctors : Array Name) : MetaM Unit := do
  let mut i := 0
  for c in ctors do
    let k := i
    i := i + 1
    let ci ← getConstInfo c
    let us := ci.levelParams.map mkLevelParam
    let name := Name.mkStr mem s!"ctorIdx_{c.getString!}"
    if (← getEnv).contains name then continue
    discard <| attempt? `Mumi.view m!"`{mem}.ctorIdx` does not compute at `{c}`" do
      forallTelescope ci.type fun xs _ => do
        let lhs ← mkAppM (mem ++ `ctorIdx) #[mkAppN (mkConst c us) xs]
        addDecl <| .thmDecl {
          name, levelParams := ci.levelParams
          type := ← mkForallFVars xs (mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) lhs (mkNatLit k))
          value := ← mkLambdaFVars xs (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) lhs) }

/-- The `ctorIdx` of what `x` wraps: down a wrapper's fields to the inductive with `n`
constructors, whose head any constructor of the member builds. -/
private partial def wrappedIdx? (x : Expr) (n : Nat) (depth : Nat := 6) : MetaM (Option Expr) := do
  if depth == 0 then return none
  let ty ← whnf (← inferType x)
  let .const i _ := ty.getAppFn | return none
  let some (.inductInfo ii) := (← getEnv).find? i | return none
  -- what the encoding built: a `Nat` among a semantics' fields has two constructors too
  let ours := i.components.any fun c => c.toString.startsWith "_ir_"
  if ours && ii.ctors.length == n && (← getEnv).contains (i ++ `ctorIdx) then
    return some (← appExplicit (← mkConstWithFreshMVarLevels (i ++ `ctorIdx)) #[x])
  unless ii.ctors.length == 1 do return none
  let .ctorInfo cv ← getConstInfo ii.ctors.head! | return none
  for k in *...cv.numFields do
    let f := Expr.proj i k x
    let fty ← inferType f
    if (← isProp fty) || (← whnf fty).isSort then continue
    if let some r ← wrappedIdx? f n (depth - 1) then return some r
  return none

/-- `X.ctorIdx` for a member with no pre-term: of what it wraps where the head of that
says, which holds at a constructor whatever its fields do; else by its own case split. -/
def addCtorIdxByCases (mem : Name) (ctors : Array Name) : MetaM Unit := do
  let dst := mem ++ `ctorIdx
  if (← getEnv).contains dst then return
  let mi ← getConstInfo mem
  let us := mi.levelParams.map mkLevelParam
  let wrapped ← forallTelescope mi.type fun bs _ =>
    withLocalDeclD `x (mkAppN (mkConst mem us) bs) fun x => do
      let some v ← wrappedIdx? x ctors.size | return false
      let xs := bs.push x
      addDef dst mi.levelParams
        (annotate (inferredBut (· == bs.size)) (← mkForallFVars xs (mkConst ``Nat)))
        (← mkLambdaFVars xs v)
      modifyEnv fun env => addProtected env dst
      return true
  if wrapped then return
  let casesOn ← getConstInfo (mem ++ `casesOn)
  let f := mkConst (mem ++ `casesOn) (Level.succ .zero :: us)
  forallTelescope mi.type fun bs _ =>
    withLocalDeclD `x (mkAppN (mkConst mem us) bs) fun x => do
      let (ms, _, _) ← forallMetaTelescope (← inferType f)
      let names := casesOn.type.getForallBinderNames
      let some tAt := names.idxOf? `t | throwError "`{mem}.casesOn` has no major"
      let some mAt := names.findIdx? (·.toString.startsWith "motive")
        | throwError "`{mem}.casesOn` has no motive"
      unless ← isDefEq (← inferType ms[tAt]!) (← inferType x) do
        throwError "`{mem}.casesOn` is not at `{mem}`"
      ms[tAt]!.mvarId!.assign x
      let motive ← forallTelescope (← instantiateMVars (← inferType ms[mAt]!)) fun ys _ =>
        mkLambdaFVars ys (mkConst ``Nat)
      ms[mAt]!.mvarId!.assign motive
      for h : k in *...ctors.size do
        let m := ms[ms.size - ctors.size + k]!
        let v ← forallTelescope (← instantiateMVars (← inferType m)) fun ys _ =>
          mkLambdaFVars ys (mkNatLit k)
        m.mvarId!.assign v
      let xs := bs.push x
      addDef dst mi.levelParams
        (annotate (inferredBut (· == bs.size)) (← mkForallFVars xs (mkConst ``Nat)))
        (← mkLambdaFVars xs (← instantiateMVars (mkAppN f ms)))
      -- this case split reaches an encoding Meta's unifier can spend for ever in, outside
      -- any heartbeat limit, so it does not get to look: the kernel computes it, and what
      -- is wanted of it is said by `X.ctorIdx_c`
      setIrreducibleAttribute dst
      modifyEnv fun env => addProtected env dst

/--
A measure of data members with no pre-term, by the block's own recursor: at a constructor
one and the sum of its fields, a recursive one by its hypothesis and a function counting
for nothing, as Lean reckons.  `X.c.sizeOf_spec` then holds by that recursor's rule, which
is `rfl` where the recursor computes; where it does not there is no lemma. -/
def addMeasureByRec (numParams : Nat) (mem : Name) : MetaM Unit := do
  let instName := mem ++ `_sizeOf_inst
  if (← getEnv).contains instName then return
  let mi ← getConstInfo mem
  let ri ← getConstInfo (mem ++ `rec)
  unless ri.levelParams.length == mi.levelParams.length + 1 do return
  let us := mi.levelParams.map mkLevelParam
  let fn := mem ++ `_measure
  forallTelescope mi.type fun bs _ => do
    let ps := bs.extract 0 numParams
    let idx := bs.extract numParams bs.size
    mkLocalInstances ps fun insts => do
      let selfTy := mkAppN (mkConst mem us) bs
      let mut app := mkAppN (mkConst (mem ++ `rec) (Level.succ .zero :: us)) ps
      repeat
        let .forallE n d _ bi ← whnfCore (← inferType app) | break
        if n.toString.startsWith "motive" then
          app := mkApp app <| ← forallTelescope d fun ys s =>
            mkLambdaFVars ys (if s.isProp then mkConst ``True else mkConst ``Nat)
        else if bi.isExplicit && n != `t then
          app := mkApp app <| ← forallTelescope d fun ys concl => do
            if concl.headBeta.isConstOf ``True then
              return ← mkLambdaFVars ys (mkConst ``True.intro)
            let named ← ys.mapM fun y => do return (← y.fvarId!.getUserName).eraseMacroScopes
            let mut rhs ← mkNumeral (mkConst ``Nat) 1
            for y in ys, nm in named do
              if nm.isStr && nm.getString!.endsWith "_ih" then
                let base := (nm.getString!.dropEnd 3).toString
                if named.any (· == nm.getPrefix.str base) then continue
              if (← whnf (← inferType y)).isForall then continue
              let ihName := nm.appendAfter "_ih"
              let ih? ← (named.idxOf? ihName).bindM fun j => do
                let ih := ys[j]!
                return if (← inferType ih).isConstOf ``Nat then some ih else none
              rhs ← mkAdd rhs (← match ih? with
                | some ih => pure ih
                | none => mkAppM ``SizeOf.sizeOf #[y])
            mkLambdaFVars ys rhs
        else break
      withLocalDeclD `x selfTy fun x => do
        let all := ps ++ insts ++ idx.push x
        addDecl <| .defnDecl {
          name := fn, levelParams := mi.levelParams
          type := ← mkForallFVars all (mkConst ``Nat)
          value := ← mkLambdaFVars all (mkAppN app (idx.push x))
          hints := .abbrev, safety := .safe }
        let call ← mkLambdaFVars #[x] (mkAppN (mkConst fn us) all)
        addDecl <| .defnDecl {
          name := instName, levelParams := mi.levelParams
          type := ← mkForallFVars (ps ++ insts ++ idx) (← mkAppM ``SizeOf #[selfTy])
          value := ← mkLambdaFVars (ps ++ insts ++ idx) (← mkAppOptM ``SizeOf.mk #[selfTy, call])
          hints := .abbrev, safety := .safe }
        registerInstance instName .global (eval_prio default)

/-- `X.c.sizeOf_spec` for a member `addMeasureByRec` measured, once its siblings are too. -/
def addMeasureSpecs (numParams : Nat) (mem : Name) (ctors : Array Name) : MetaM Unit := do
  unless (← getEnv).contains (mem ++ `_measure) do return
  let simpAttr ← ofExcept <| getAttributeImpl (← getEnv) `simp
  for c in ctors do
    let ci ← getConstInfo c
    let name := c ++ `sizeOf_spec
    discard <| attempt? `Mumi.view m!"no `sizeOf` lemma for `{c}`" do
      forallTelescope ci.type fun xs _ => do
        let cps := xs.extract 0 numParams
        let fields := xs.extract numParams xs.size
        mkLocalInstances cps fun insts => do
          let lhs ← mkAppM ``SizeOf.sizeOf #[mkAppN (mkConst c (ci.levelParams.map mkLevelParam)) xs]
          let mut rhs ← mkNumeral (mkConst ``Nat) 1
          for f in fields do
            if (← whnf (← inferType f)).isForall then continue
            rhs ← mkAdd rhs (← mkAppM ``SizeOf.sizeOf #[f])
          let all := cps ++ insts ++ fields
          addDecl <| .thmDecl {
            name, levelParams := ci.levelParams
            type := ← mkForallFVars all (mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) lhs rhs)
            value := ← mkLambdaFVars all (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) lhs) }
      simpAttr.add name default .global

/-- `Nat.beq (X.ctorIdx t) (X.ctorIdx t')`. -/
private def mkBeqIdx (mem : Name) (t t' : Expr) : MetaM Expr := do
  return mkApp2 (mkConst ``Nat.beq) (← mkAppM (mem ++ `ctorIdx) #[t]) (← mkAppM (mem ++ `ctorIdx) #[t'])

/-- `cond c x y`, at a sort. -/
private def mkCond (c x y : Expr) : MetaM Expr := do
  let α ← inferType x
  return mkApp4 (mkConst ``cond [← getLevel α]) α c x y

/--
`X.noConfusionType` and `X.noConfusion` from the view's.  Two elements of `X`
are confused exactly when their views are, so the statement is the view's along
`X.view`, and the equations it takes are read off the view's rather than
recomputed. -/
def addNoConfusion (mem : Name) : TermElabM Unit := do
  let vType := viewName mem ++ `noConfusionType
  let vConf := viewName mem ++ `noConfusion
  let some tInfo := (← getEnv).find? vType | throwError "no `{vType}` to restate"
  let mi ← getConstInfo mem
  let lps := tInfo.levelParams
  let us := mi.levelParams.map mkLevelParam
  let [w] := lps.filter (!mi.levelParams.contains ·)
    | throwError "`{vType}` is not generic in exactly one sort"
  let dType := mem ++ `noConfusionType
  let dConf := mem ++ `noConfusion
  forallTelescope mi.type fun bs _ =>
  forallTelescope mi.type fun bs' _ =>
  withLocalDeclD `P (mkSort (.param w)) fun p =>
  withLocalDeclD `t (mkAppN (mkConst mem us) bs) fun t =>
  withLocalDeclD `t' (mkAppN (mkConst mem us) bs') fun t' => do
    let view (b : Array Expr) (x : Expr) : Expr :=
      mkAppN (mkConst (viewFnName mem) us) (b.push x)
    let xs := #[p] ++ bs ++ #[t] ++ bs' ++ #[t']
    let n := bs.size
    -- the sort and the two elements are what the statement is about; everything
    -- else follows from them, and the second copy of the member's binders is
    -- named apart as Lean names it in an ordinary `noConfusionType`
    let shape (keep : Nat → Bool) (i : Nat) (nm : Name) (bi : BinderInfo) : Name × BinderInfo :=
      ((if n + 2 ≤ i && i ≤ 2 * n + 1 then nm.appendAfter "'" else nm),
        (inferredBut keep i nm bi).2)
    let major (i : Nat) : Bool := i == 0 || i == n + 1 || i == 2 * n + 2
    unless (← getEnv).contains dType do
      -- two different constructors are told apart by their `ctorIdx`, which computes
      -- at any, where a view need not
      let core ← appExplicit (← mkConstWithFreshMVarLevels vType)
        #[p, view bs t, view bs' t']
      let value ← mkCond (← mkBeqIdx mem t t') core p
      addDef dType lps (annotate (shape major) (← mkForallFVars xs (mkSort (.param w))))
        (← mkLambdaFVars xs value) (hints := .abbrev) (compile := false)
      setReducibleAttribute dType
      modifyEnv fun env => addProtected env dType
    if (← getEnv).contains dConf then return
    let goal ← appExplicit (mkConst dType (lps.map mkLevelParam)) #[p, t, t']
    let coreGoal ← appExplicit (← mkConstWithFreshMVarLevels vType)
      #[p, view bs t, view bs' t']
    -- what equations the view is confused by, and hence what this one is: the
    -- view's last one is about the views themselves and is discharged here, the
    -- ones before it are about the member and become the binders
    let (tys, vGoal) ← do
      let (mvs, bis, concl) ← forallMetaTelescope (← getConstInfo vConf).type
      unless ← isDefEq concl coreGoal do throwError "`{vConf}` does not conclude at `{dType}`"
      let mut given := #[]
      for i in *...mvs.size do
        if bis[i]!.isExplicit then given := given.push mvs[i]!
      let some vEq := given.back? | throwError "`{vConf}` takes no equation"
      pure (← given.pop.mapM fun m => do instantiateMVars (← inferType m),
        ← instantiateMVars (← inferType vEq))
    withLocalDeclsDND (tys.mapIdx fun i ty => (Name.mkSimple s!"mumiEq{i}", ty)) fun hs => do
      let last := mkIdent (Name.mkSimple s!"mumiEq{hs.size - 1}")
      let proof ← proveBy vGoal <| ←
        `(Lean.Parser.Tactic.tacticSeq|
            try subst_vars
            first
              | exact rfl
              | exact HEq.rfl
              | (cases $last:ident; first | exact rfl | exact HEq.rfl))
      let all := xs ++ hs
      let idxEq ← mkEq (← mkAppM (mem ++ `ctorIdx) #[t]) (← mkAppM (mem ++ `ctorIdx) #[t'])
      let idxProof ← proveBy idxEq <| ←
        `(Lean.Parser.Tactic.tacticSeq|
            try subst_vars
            first
              | exact rfl
              | (cases $last:ident; exact rfl))
      let core ← appExplicit (← mkConstWithFreshMVarLevels vConf) (hs.push proof) coreGoal
      addDef dConf lps
        (annotate (shape (· ≥ xs.size)) (← mkForallFVars all goal))
        (← mkLambdaFVars all (← mkAppOptM `Mumi.condOfEq #[none, p, none, none, idxProof, core]))
        (hints := .abbrev) (compile := false)
      setReducibleAttribute dConf
      modifyEnv fun env => addProtected env dConf

/--
`X.noConfusionType` and `X.noConfusion` for a member with no view.  Two different
constructors are refuted through `X.ctorIdx`; at one constructor there are no fields'
equations to offer, as a view has them, so what it gives is the equation itself, and
`X.c.inj` is what takes it apart. -/
def addNoConfusionByIdx (numParams : Nat) (mem : Name) : TermElabM Unit := do
  let dType := mem ++ `noConfusionType
  let dConf := mem ++ `noConfusion
  if (← getEnv).contains dType then return
  let mi ← getConstInfo mem
  let us := mi.levelParams.map mkLevelParam
  let w := (`w : Name)
  let lps := w :: mi.levelParams
  forallTelescope mi.type fun bs _ => do
  let ps := bs.extract 0 numParams
  let is₁ := bs.extract numParams bs.size
  -- the indices again, the parameters being the one
  let ty' ← instantiateForall mi.type ps
  forallTelescope ty' fun is₂ _ =>
  withLocalDeclD `P (mkSort (.param w)) fun p =>
  withLocalDeclD `t (mkAppN (mkConst mem us) (ps ++ is₁)) fun t =>
  withLocalDeclD `t' (mkAppN (mkConst mem us) (ps ++ is₂)) fun t' => do
    let same ← mkEqHEq t t'
    let core ← mkArrow (← mkArrow same p) p
    let value ← mkCond (← mkBeqIdx mem t t') core p
    let xs := #[p] ++ ps ++ is₁ ++ #[t] ++ is₂ ++ #[t']
    let implicitBut (keep : Nat → Bool) (i : Nat) (nm : Name) (bi : BinderInfo) : Name × BinderInfo :=
      (nm, (inferredBut keep i nm bi).2)
    addDef dType lps (annotate (implicitBut fun i => i == 0 || i == ps.size + is₁.size + 1 || i == xs.size - 1)
        (← mkForallFVars xs (mkSort (.param w))))
      (← mkLambdaFVars xs value) (hints := .abbrev) (compile := false)
    setReducibleAttribute dType
    modifyEnv fun env => addProtected env dType
    let goal := mkAppN (mkConst dType (lps.map mkLevelParam)) xs
    -- as Lean takes them: an equation at each index, and then the two terms
    let mut hyps : Array (Name × Expr) := #[]
    for a in is₁, b in is₂ do
      hyps := hyps.push (Name.mkSimple s!"mumiEq{hyps.size}", ← mkEqHEq a b)
    hyps := hyps.push (Name.mkSimple s!"mumiEq{hyps.size}", same)
    withLocalDeclsDND hyps fun hs => do
      let last := mkIdent (Name.mkSimple s!"mumiEq{hs.size - 1}")
      let idxEq ← mkEq (← mkAppM (mem ++ `ctorIdx) #[t]) (← mkAppM (mem ++ `ctorIdx) #[t'])
      let idxProof ← proveBy idxEq <| ←
        `(Lean.Parser.Tactic.tacticSeq|
            try subst_vars
            first
              | exact rfl
              | (cases $last:ident; exact rfl))
      let inner ← withLocalDeclD `k (← mkArrow same p) fun k => do
        mkLambdaFVars #[k] (mkApp k hs.back!)
      let all := xs ++ hs
      addDef dConf lps
        (annotate (implicitBut (· ≥ xs.size)) (← mkForallFVars all goal))
        (← mkLambdaFVars all (← mkAppOptM `Mumi.condOfEq #[none, p, none, none, idxProof, inner]))
        (hints := .abbrev) (compile := false)
      setReducibleAttribute dConf
      modifyEnv fun env => addProtected env dConf

/-- What a block with no pre-terms gets of what `addViews` gives the others: `X.ctorIdx`
and its rules, and a measure.  Each member's own failure is its own. -/
def addFactsOverRec (numParams : Nat) (members : Array (Name × Array Name)) : TermElabM Unit := do
  for (mem, ctors) in members do
    discard <| attempt? `Mumi.view m!"no `ctorIdx` for `{mem}`" <| addCtorIdxByCases mem ctors
    addCtorIdxRules mem ctors
    discard <| attempt? `Mumi.view m!"no `noConfusion` for `{mem}`" <| addNoConfusionByIdx numParams mem
  for (mem, _) in members do
    discard <| attempt? `Mumi.view m!"no measure for `{mem}`" <| addMeasureByRec numParams mem
  for (mem, ctors) in members do
    addMeasureSpecs numParams mem ctors

/--
Give every member encoded as a subtype a `SizeOf` instance, its specification
lemmas, a view, and the declarations an `inductive` answers to, in passes so a
constructor whose field is a sibling finds the sibling's instance already
there. -/
def addViews (numParams : Nat) (members : Array (Name × Array Name)) : TermElabM Unit := do
  let members ← members.filterM fun (_, ctors) => do
    let some c := ctors[0]? | return false
    return !((← getEnv).find? c).any (·.isCtor)
  -- a pre-term has no room for what an index already says, so measuring by it leaves out a
  -- field Lean counts, and a recursion into that field does not terminate.  The block's
  -- recursor has a hypothesis at every field, so it measures what was written, where it
  -- computes at every constructor; a copy of a container has to measure what the container
  -- does, by its own lemma, and keeps the pre-term's
  let byRec ← if members.any (fun (m, _) => m.getString!.startsWith "nested_") then pure false
    else
      let env ← getEnv
      try
        for (mem, _) in members do addMeasureByRec numParams mem
        for (mem, ctors) in members do addMeasureSpecs numParams mem ctors
        let all ← members.allM fun (_, ctors) => ctors.allM fun c =>
          return (← getEnv).contains (c ++ `sizeOf_spec)
        unless all do setEnv env
        pure all
      catch _ =>
        setEnv env
        pure false
  for (mem, _) in members do
    if byRec then break
    if (← getEnv).contains (mem ++ `_pre) then
      discard <| attempt? `Mumi.view m!"no measure of `{mem}`" <| addPreMeasure (mem ++ `_pre)
  for (mem, _) in members do
    discard <| attempt? `Mumi.view m!"no `sizeOf` for `{mem}`" <| addSizeOfInst numParams mem
  for (mem, ctors) in members do
    let lps := (← getConstInfo mem).levelParams
    for c in ctors do
      discard <| attempt? `Mumi.view m!"no `sizeOf` lemma for `{c}`" <|
        addSizeOfSpec numParams lps mem c
  for (mem, ctors) in members do
    discard <| attempt? `Mumi.view m!"no view for `{mem}`" <| addView numParams mem ctors
  for (mem, ctors) in members do
    discard <| attempt? `Mumi.view m!"no `casesOn` for `{mem}`" <|
      addMajorFirst numParams mem (mem ++ `casesD) (mem ++ `casesOn)
    discard <| attempt? `Mumi.view m!"no `recOn` for `{mem}`" <|
      addMajorFirst numParams mem (mem ++ `rec) (mem ++ `recOn)
    discard <| attempt? `Mumi.view m!"no `ctorIdx` for `{mem}`" <| addCtorIdx mem
    addCtorIdxRules mem ctors
    discard <| attempt? `Mumi.view m!"no `noConfusion` for `{mem}`" <| addNoConfusion mem

/--
`X.casesOn` and `X.recOn` for a `Prop` member, which has no view and needs none:
both restate an eliminator the block already has.  `X.casesOn` comes from
`X.casesP` rather than from `X.casesD`, because a `Prop` member of a block with
more than one member never eliminates into anything but `Prop`. -/
def addPropEliminators (numParams : Nat) (mem : Name) : MetaM Unit := do
  discard <| attempt? `Mumi.view m!"no `casesOn` for `{mem}`" <|
    addMajorFirst numParams mem (mem ++ `casesP) (mem ++ `casesOn)
  discard <| attempt? `Mumi.view m!"no `recOn` for `{mem}`" <|
    addMajorFirst numParams mem (mem ++ `rec) (mem ++ `recOn)

end Mumi
