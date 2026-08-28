/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Mumi.Lowering

/-!
# Denesting

A *nested* occurrence is a member of the block appearing inside the parameters
of some other inductive type, as `T` does in

```lean
inductive T : Type where
  | mk1 : T
  | mkT : Nonempty T → T
```

Lean's kernel handles these itself: it specialises the nested type constructor
to the block, giving an auxiliary member, and checks the enlarged block instead.
That is why `T.rec` above would have a motive for `Nonempty T` as well as one
for `T`.  It is also why the declaration is rejected -- the enlarged block has
`T` in `Type` and the copy of `Nonempty` in `Prop`, and the kernel insists that
a mutual block live in one universe.

This module performs the same specialisation at the elaborator level, so that
the enlarged block can be handed to `lower` rather than to the kernel.  It is a
pure `Input → Input` pass: a block with no nested occurrence comes back
untouched, and one with nested occurrences comes back with a new member per
distinct nested application.

Only strictly-positive positions are denested.  A field's type is stripped of
its leading binders and the nested application is looked for at the head of what
remains, which is exactly where a legal occurrence can be; occurrences in a
binder's domain are left alone for `analyzeField` to reject.
-/

public section

namespace Lean.Elab.MultiuniverseInductive

open Lean Meta

instance : Inhabited Input where
  default :=
    { levelParams := [], numVars := 0, numParams := 0, memberFVars := #[], memberNames := #[],
      memberTypes := #[], ctorNames := #[], ctorTypes := #[] }

/--
One nested application, and the member it is about to become.

The application's parameters may mention *locals* -- constructor fields, or
binders of the field's own type -- as `Nonempty (Ix n)` mentions `n` in

```lean
inductive Ix : Nat → Type where
  | base : Ix 0
  | step : (n : Nat) → Nonempty (Ix n) → Ix (n + 1)
```

There is no single member such an occurrence could become, so the locals are
abstracted and become *indices* of the new member: one member
`Ix.nested_Nonempty_1 : Nat → Prop`, with `intro : (n : Nat) → Ix n → …`, and
the occurrence rewritten to `Ix.nested_Nonempty_1 n`.  Everything below is
stored in abstracted form so that the locals can be reopened as fresh binders
when the member is built.  (The kernel refuses this case outright: *nested
inductive datatypes parameters cannot contain local variables*.)
-/
private structure AuxSpec where
  /-- `I p₁ … p_k` with the locals abstracted: the type constructor applied to
  its parameters, and nothing else.  Two occurrences that agree up to their
  locals share one member, so this is the key. -/
  key       : Expr
  /-- The name the new member gets. -/
  name      : Name
  /-- The abstracted locals, in local-context order, each type abstracted over
  the ones before it.  These become the new member's extra indices, and the
  leading fields of each of its constructors. -/
  extras    : Array (Name × Expr)
  /-- `I`'s parameters, abstracted over `extras`. -/
  paramsAbs : Array Expr
  /-- `∀ idxs, Sort l`, `I`'s type with its parameters fixed, abstracted over
  `extras`.  Mentions no member of the block. -/
  resType   : Expr
  indName   : Name
  levels    : List Level
  ctors     : Array Name
  deriving Inhabited

private structure DenestState where
  specs : Array AuxSpec := #[]

private abbrev DenestM := StateRefT DenestState MetaM

private def mentionsAny (members : Array Expr) (e : Expr) : Bool :=
  members.any fun f => e.containsFVar f.fvarId!

/--
Unfold definitions at the head of `e` until an inductive type constructor is
exposed, so that a nested occurrence behind an `abbrev` is still seen.  Gives up
after a few steps, and on anything that is not a definition.
-/
private def exposeInduct (e : Expr) : MetaM Expr := do
  let mut e := e
  for _ in *...8 do
    let .const n _ := e.getAppFn | return e
    if let some (.inductInfo _) := (← getEnv).find? n then return e
    let some e' ← unfoldDefinition? e | return e
    e := e'
  return e

/--
Recognise a nested occurrence at the head of a strictly-positive position.

Answers `none` for anything that is not one: a position with no member in it at
all, a member applied to its own arguments, a type constructor that is not
inductive (`Quot`, a function), or an inductive applied to a member only outside
its parameters.
-/
private def nestedApp? (members : Array Expr) (body : Expr) :
    MetaM (Option (Expr × InductiveVal × List Level × Array Expr × Array Expr)) := do
  if !mentionsAny members body then return none
  if members.any (· == body.getAppFn) then return none
  let body ← exposeInduct body
  let .const iname lvls := body.getAppFn | return none
  let some (.inductInfo info) := (← getEnv).find? iname | return none
  let args := body.getAppArgs
  if args.size < info.numParams then return none
  let params := args.extract 0 info.numParams
  if !params.any (mentionsAny members ·) then return none
  return some (mkAppN (.const iname lvls) params, info, lvls,
    params, args.extract info.numParams args.size)

/--
The local variables a nested application's parameters depend on, closed under
the dependencies of their own types and ordered as the local context orders
them.  The block's parameters and members are not locals in this sense: the
former are shared by every member, and the latter are what makes the occurrence
nested in the first place.
-/
private def extraLocals (ps members : Array Expr) (es : Array Expr) : MetaM (Array Expr) := do
  let mut excluded : FVarIdSet := {}
  for p in ps ++ members do
    if p.isFVar then excluded := excluded.insert p.fvarId!
  let mut found : FVarIdSet := {}
  let mut order : Array FVarId := #[]
  let mut queue := es
  while !queue.isEmpty do
    let e := queue.back!
    queue := queue.pop
    for fv in (collectFVars {} e).fvarIds do
      unless excluded.contains fv || found.contains fv do
        found := found.insert fv
        order := order.push fv
        queue := queue.push (← fv.getType)
  let lctx ← getLCtx
  let idx (fv : FVarId) : Nat := match lctx.find? fv with | some d => d.index | none => 0
  return (order.qsort fun a b => idx a < idx b).map mkFVar

/-- The last component of a name, for building a readable auxiliary name. -/
private def shortName (n : Name) : String :=
  match n with
  | .str _ s => s
  | _        => "nested"

mutual

/--
Intern the nested application at the head of `body`, if there is one, and then
look through the copy's own fields for further nesting.
-/
private partial def internNested (root : Name) (members ps : Array Expr) (body : Expr) :
    DenestM Unit := do
  let some (app, info, lvls, params, idxArgs) ← nestedApp? members body | return
  let xs ← extraLocals ps members params
  let key := app.abstract xs
  if (← get).specs.any (·.key == key) then return
  for a in idxArgs do
    if mentionsAny members a then
      throwError m!"Cannot denest{indentExpr body}"
        ++ .note m!"`{info.name}` is applied to a member of the block in an index rather than \
          a parameter, and only parameters can be specialised"
  for x in xs do
    if mentionsAny members (← inferType x) then
      throwError m!"Cannot denest{indentExpr body}"
        ++ .note m!"`{info.name}` is applied to something depending on `{x}`, whose own type \
          mentions a member of the block"
  let some ci := (← getEnv).find? info.name | return
  let resType ← instantiateForall (ci.instantiateTypeLevelParams lvls) params
  if mentionsAny members resType then
    throwError m!"Cannot denest{indentExpr body}"
      ++ .note m!"the type of `{info.name}` still mentions a member of the block once its \
        parameters are fixed"
  let mut extras : Array (Name × Expr) := #[]
  for i in *...xs.size do
    extras := extras.push
      (← xs[i]!.fvarId!.getUserName, (← inferType xs[i]!).abstract (xs.extract 0 i))
  let name := root ++ Name.mkSimple s!"nested_{shortName info.name}_{(← get).specs.size + 1}"
  let spec : AuxSpec :=
    { key, name, extras, paramsAbs := params.map (·.abstract xs), resType := resType.abstract xs,
      indName := info.name, levels := lvls, ctors := info.ctors.toArray }
  modify fun s => { s with specs := s.specs.push spec }
  for c in info.ctors do
    let cinfo ← getConstInfoCtor c
    let cty ← instantiateForall
      (cinfo.type.instantiateLevelParams cinfo.levelParams lvls) params
    forallTelescope cty fun fields _ =>
      for x in fields do
        scanPos root members ps (← inferType x)

/-- Scan one strictly-positive position: strip the leading binders, look at the head. -/
private partial def scanPos (root : Name) (members ps : Array Expr) (ty : Expr) : DenestM Unit :=
  forallTelescope ty fun _ys body => internNested root members ps body

end

/-- Scan every constructor field of the block for nested occurrences. -/
private def scanBlock (root : Name) (members ps : Array Expr) (inp : Input) : DenestM Unit := do
  for cts in inp.ctorTypes do
    for ct in cts do
      forallTelescope (← instantiateForall ct ps) fun fields _ => do
        for x in fields do
          scanPos root members ps (← inferType x)

/-- Everything the rewrite needs. -/
private structure RwCtx where
  members  : Array Expr
  /-- The parameters an occurrence is applied to: a member free variable stands
  for the member already applied to the section variables, so the leading
  `numVars` parameters are *not* part of an occurrence's argument list.  The
  auxiliary members follow the same convention. -/
  appPs    : Array Expr
  /-- All of the block's parameters, needed to recognise a local. -/
  ps       : Array Expr
  specs    : Array AuxSpec
  auxFVars : Array Expr

/-- Replace a nested application at the head of a strictly-positive position. -/
private def RwCtx.head (c : RwCtx) (body : Expr) : MetaM Expr := do
  let some (app, _, _, params, idxArgs) ← nestedApp? c.members body | return body
  let xs ← extraLocals c.ps c.members params
  let some k := c.specs.findIdx? (·.key == app.abstract xs)
    | throwError m!"Cannot denest{indentExpr body}"
        ++ .note "this occurrence was not seen when the block was scanned"
  return mkAppN c.auxFVars[k]! (c.appPs ++ xs ++ idxArgs)

/-- Rewrite one strictly-positive position. -/
private def RwCtx.pos (c : RwCtx) (ty : Expr) : MetaM Expr :=
  forallTelescope ty fun ys body => do mkForallFVars ys (← c.head body)

/-- Rewrite a constructor's fields and result. -/
private partial def RwCtx.pi (c : RwCtx) (e : Expr) : MetaM Expr := do
  match e with
  | .forallE n d b bi =>
    withLocalDecl n bi (← c.pos d) fun x => do
      mkForallFVars #[x] (← c.pi (b.instantiate1 x))
  | _ => c.pos e

/-- Reopen a spec's abstracted locals as fresh binders. -/
private def withExtras {α : Type} [Inhabited α] (s : AuxSpec) (k : Array Expr → MetaM α) :
    MetaM α :=
  withLocalDeclsD (s.extras.map fun (n, t) => (n, fun xs => pure (t.instantiateRev xs))) k

/-! ## The bridge

An auxiliary member is a *copy* of the type that was nested, so the constructor
that took a `Nonempty T` now takes a `T.nested_Nonempty_1`.  When the copy is a
`Prop` the two are not merely isomorphic but equal, and saying so once lets the
original type back into the user's code:

```lean
example (h : Nonempty T) : T := T.mkT (T.nested_Nonempty_1.eq_orig ▸ h)
```

`propext` is the only axiom involved.  Both directions are the copy's recursor
against the original's, which is possible exactly because the two have the same
constructors: `A.cᵢ`'s fields are `I.cᵢ`'s with the nested occurrences
rewritten, so when no field mentions an auxiliary member the two constructors
take *the same* arguments and each direction is one recursor call per
constructor.

That proviso is the whole restriction.  It rules out a wrapper that is
recursive through the nesting (`A`'s own field would be an `A`) and a nesting
inside a nesting (the field is the inner copy, which for a data member is only
isomorphic to the original, not equal to it).  Everything that does not qualify
simply gets no bridge; the type itself is unaffected either way.
-/

/-- Does no field of this rewritten constructor type mention an auxiliary member? -/
private def fieldsClean (auxFVars : Array Expr) (cty : Expr) : MetaM Bool :=
  forallTelescope cty fun fields _ => do
    for f in fields do
      if mentionsAny auxFVars (← inferType f) then return false
    return true

/--
Copy the first `n` binder annotations of `model` onto `e`.

Rewriting a constructor means taking its parameters apart and putting them back,
and `mkForallFVars` annotates each binder the way its local declaration is
annotated.  The parameters here come from the type former, where they are
explicit; in a constructor they are implicit -- or strict-implicit, or instance
-- so what the block was declared with has to be read back off a constructor
that still has it.  Getting this wrong is not cosmetic: it decides whether
`P.ghost h` or `P.ghost α h` is the way to write the constructor.
-/
private def withLeadingBinderInfo : Nat → Expr → Expr → Expr
  | 0, _, e => e
  | n + 1, .forallE _ _ mb mbi, .forallE nm ty b _ =>
    .forallE nm ty (withLeadingBinderInfo n mb b) mbi
  | _, _, e => e

/-- An auxiliary member, and the original type it is a copy of. -/
private structure Bridge where
  spec : AuxSpec
  /-- The block's members as free variables, and as the constants that now
  denote them. -/
  members : Array Expr
  repl    : Array Expr

/--
`I`'s parameters for a given choice of extras.

The substitution has to happen *after* the extras are put back, because
`Expr.replaceFVars` abstracts and reinstantiates, which would capture the
extras' own loose bound variables.
-/
private def Bridge.paramsAt (b : Bridge) (xs : Array Expr) : Array Expr :=
  b.spec.paramsAbs.map fun p => (p.instantiateRev xs).replaceFVars b.members b.repl

/--
The uniform recursor's motives: the original type for the member being bridged,
and `True` for every other member, which is why the recursor's motive universe
can be instantiated to zero.
-/
private def bridgeMotives (b : Bridge) (j : Nat) (mtypes : Array Expr) : MetaM (Array Expr) := do
  let mut vals : Array Expr := #[]
  for i in *...mtypes.size do
    let v ← forallTelescope mtypes[i]! fun ys _ => do
      if i != j then
        mkLambdaFVars ys (.const ``True [])
      else
        -- `ys` is the member's indices followed by the element itself, and the
        -- auxiliary member's indices are `extras` first, then `I`'s own
        let xs := ys.extract 0 b.spec.extras.size
        let idxs := ys.extract b.spec.extras.size (ys.size - 1)
        let orig := mkAppN (.const b.spec.indName b.spec.levels) (b.paramsAt xs)
        mkLambdaFVars ys (mkAppN orig idxs)
    vals := vals.push v
  return vals

/--
The coercion out of an auxiliary member and into the type it copies.

Its presence is what marks a member as identified with its original, and its
type is where `Mumi.Bridge` reads that original back from, so the name is
declared once rather than written out on both sides.  Keying the display off a
declaration denesting adds anyway -- rather than off the equality, whose name a
user might reasonably pick for something of their own -- is what keeps it from
changing how unrelated types print.
-/
def origCoeName (aux : Name) : Name := aux ++ `coeToOrig

/--
Register a coercion from one side of the identification to the other.

The equality alone would still leave the copy's name to be written out at every
use.  The pair of coercions is what removes it: one lets the original be passed
to a constructor that asks for the copy, the other lets a field bound by a
pattern match be used as the original.

Like any coercion, one is inserted only where the type it has to reach is
known; a consumer whose own type argument is still a metavariable needs the
field ascribed, and the ascription names the original rather than the copy.
-/
private def mkCoe (name : Name) (levelParams : List Name) (binders : Array Expr)
    (src tgt eq : Expr) : MetaM Unit :=
  withLocalDeclD `h src fun h => do
    let f     ← mkLambdaFVars #[h] (← mkAppM ``cast #[eq, h])
    let type  ← mkForallFVars binders (← mkAppM ``CoeOut #[src, tgt])
    let value ← mkLambdaFVars binders (← mkAppM ``CoeOut.mk #[f])
    check value
    unless ← isDefEq (← inferType value) type do return
    addDecl (.defnDecl
      { name, levelParams, type, value, hints := .abbrev, safety := .safe })
    setReducibleAttribute name
    Meta.addInstance name .global 1000

/--
Prove `A ps xs idxs = I params idxs` and add it as `A.eq_orig`, then make the
identification usable without naming `A`, by registering a coercion in each
direction.  The forward one doubles as the marker `Mumi.Bridge` reads to display
`A` as the type it copies.

Nothing here can make the block worse: it runs after the block has been
declared, and reads only what is already in the environment.
-/
private def mkBridge (inp : Input) (ps : Array Expr) (ctorNames : Array (Array Name))
    (j : Nat) (b : Bridge) : TermElabM Unit := do
  let s := b.spec
  let ownLevels := inp.levelParams.map Level.param
  -- the copy's `rec` is a definition standing for its `mutualRec`, the
  -- original's is a genuine recursor; only the type and levels matter here
  let some recInfo := (← getEnv).find? (s.name ++ `rec) | return
  let some origRec := (← getEnv).find? (s.indName ++ `rec) | return
  -- the recursor's motive universe is the one level it does not share with the
  -- block; every motive we supply is a `Prop`, so it goes to zero
  let recLevels := recInfo.levelParams.map fun p =>
    if inp.levelParams.contains p then .param p else .zero
  -- the original's recursor puts its motive universe first, if it has one
  let origLevels :=
    if origRec.levelParams.length == s.levels.length + 1 then .zero :: s.levels else s.levels
  unless origRec.levelParams.length == origLevels.length do return
  withExtras s fun xs => do
    let params := b.paramsAt xs
    let orig := mkAppN (.const s.indName s.levels) params
    forallTelescope (s.resType.instantiateRev xs) fun idxs sortE => do
      let .sort lvl := sortE | return
      unless lvl.normalize.isZero do return
      let lhs := mkAppN (.const s.name ownLevels) (ps ++ xs ++ idxs)
      let rhs := mkAppN orig idxs
      -- forward: the copy's recursor, one case per constructor
      let recTy ← instantiateForall
        (recInfo.type.instantiateLevelParams recInfo.levelParams recLevels) ps
      let mtypes ← forallBoundedTelescope recTy (some ctorNames.size) fun mvs _ =>
        mvs.mapM inferType
      let motives ← bridgeMotives b j mtypes
      let afterMotives ← instantiateForall recTy motives
      let nCases := ctorNames.foldl (fun n cs => n + cs.size) 0
      let ctypes ← forallBoundedTelescope afterMotives (some nCases) fun cvs _ =>
        cvs.mapM inferType
      let mut cases : Array Expr := #[]
      for i in *...ctorNames.size do
        for q in *...ctorNames[i]!.size do
          let cty := ctypes[cases.size]!
          cases := cases.push (← forallTelescope cty fun bs _ => do
            if i != j then
              mkLambdaFVars bs (.const ``True.intro [])
            else
              -- the leading arguments of the copy's constructor are the extras
              -- and then the original constructor's own fields; the rest of the
              -- case's binders are induction hypotheses, which a bridged member
              -- never needs
              let n := s.extras.size + (← getConstInfoCtor s.ctors[q]!).numFields
              let xs' := bs.extract 0 s.extras.size
              let flds := bs.extract s.extras.size n
              mkLambdaFVars bs
                (mkAppN (.const s.ctors[q]! s.levels) (b.paramsAt xs' ++ flds)))
      let fwd := mkAppN (.const (s.name ++ `rec) recLevels) (ps ++ motives ++ cases ++ xs ++ idxs)
      -- backward: the original's recursor, rebuilding each constructor as the copy's
      let origTy ← instantiateForall
        (origRec.type.instantiateLevelParams origRec.levelParams origLevels) params
      let omtype ← forallBoundedTelescope origTy (some 1) fun mvs _ => inferType mvs[0]!
      let omotive ← forallTelescope omtype fun ys _ =>
        mkLambdaFVars ys (mkAppN (.const s.name ownLevels) (ps ++ xs ++ ys.extract 0 (ys.size - 1)))
      let afterOMotive ← instantiateForall origTy #[omotive]
      let otypes ← forallBoundedTelescope afterOMotive (some s.ctors.size) fun cvs _ =>
        cvs.mapM inferType
      let mut minors : Array Expr := #[]
      for q in *...s.ctors.size do
        minors := minors.push (← forallTelescope otypes[q]! fun bs _ => do
          let n := (← getConstInfoCtor s.ctors[q]!).numFields
          mkLambdaFVars bs
            (mkAppN (.const ctorNames[j]![q]! ownLevels) (ps ++ xs ++ bs.extract 0 n)))
      let bwd := mkAppN (.const (s.indName ++ `rec) origLevels)
        (params ++ #[omotive] ++ minors ++ idxs)
      let proof := mkApp3 (.const ``propext []) lhs rhs
        (mkApp4 (.const ``Iff.intro []) lhs rhs fwd bwd)
      let type ← mkForallFVars (ps ++ xs ++ idxs) (← mkEq lhs rhs)
      let value ← mkLambdaFVars (ps ++ xs ++ idxs) proof
      -- check before adding: `addDecl` reports a bad declaration rather than
      -- refusing it, and a bridge must never be able to say anything
      check value
      unless ← isDefEq (← inferType value) type do return
      addDecl (.thmDecl { name := s.name ++ `eq_orig, levelParams := inp.levelParams, type, value })
      let bs := ps ++ xs ++ idxs
      let eqApp := mkAppN (.const (s.name ++ `eq_orig) ownLevels) bs
      mkCoe (origCoeName s.name) inp.levelParams bs lhs rhs eqApp
      mkCoe (s.name ++ `coeOfOrig) inp.levelParams bs rhs lhs (← mkEqSymm eqApp)

/--
Add one member per distinct nested application, rewrite the constructors to
refer to those members instead, and run `k` on the result.

A block with no nested occurrence is passed to `k` unchanged, so this is safe to
run on every block.

This is written in continuation-passing style because the new members are free
variables, and a free variable is only meaningful inside the scope that declares
it.
-/
def denest {α : Type} [Inhabited α] (inp : Input) (k : Input → TermElabM α) : TermElabM α := do
  if inp.memberTypes.isEmpty then return (← k inp)
  let members := inp.memberFVars
  let root := inp.memberNames[0]!
  forallBoundedTelescope inp.memberTypes[0]! (some inp.numParams) fun ps _ => do
    let (_, st) ← (scanBlock root members ps inp).run {}
    if st.specs.isEmpty then return (← k inp)
    let appPs := ps.extract inp.numVars ps.size
    let mut decls : Array (Name × Expr) := #[]
    let mut auxTypes : Array Expr := #[]
    for s in st.specs do
      let (full, app) ← withExtras s fun xs => do
        let res := s.resType.instantiateRev xs
        return (← mkForallFVars (ps ++ xs) res, ← mkForallFVars (appPs ++ xs) res)
      decls := decls.push (s.name, app)
      auxTypes := auxTypes.push full
    withLocalDeclsDND decls fun auxFVars => do
      let c : RwCtx := { members, appPs, ps, specs := st.specs, auxFVars }
      let mut memberNames := inp.memberNames
      let mut memberTypes := inp.memberTypes
      let mut memberFVars := inp.memberFVars
      let mut ctorNames   := inp.ctorNames
      let mut ctorTypes   := inp.ctorTypes
      let mut bridgeOk    : Array Bool := #[]
      -- any of the block's own constructors will do: they all carry the same
      -- parameters, and an auxiliary member only exists because one of them
      -- nests something, so there is always at least one
      let model? := inp.ctorTypes.findSome? (·[0]?)
      for i in *...ctorTypes.size do
        let mut cts : Array Expr := #[]
        for ct in ctorTypes[i]! do
          cts := cts.push (withLeadingBinderInfo inp.numParams ct
            (← mkForallFVars ps (← c.pi (← instantiateForall ct ps))))
        ctorTypes := ctorTypes.set! i cts
      for j in *...st.specs.size do
        let s := st.specs[j]!
        memberNames := memberNames.push s.name
        memberTypes := memberTypes.push auxTypes[j]!
        memberFVars := memberFVars.push auxFVars[j]!
        let (cts, ok) ← withExtras s fun xs => do
          let params := s.paramsAbs.map (·.instantiateRev xs)
          let mut cts : Array Expr := #[]
          let mut ok := true
          for ctor in s.ctors do
            let cinfo ← getConstInfoCtor ctor
            let cty ← instantiateForall
              (cinfo.type.instantiateLevelParams cinfo.levelParams s.levels) params
            let rw ← c.pi cty
            unless ← fieldsClean auxFVars rw do ok := false
            let full ← mkForallFVars (ps ++ xs) rw
            cts := cts.push (match model? with
              | some m => withLeadingBinderInfo inp.numParams m full
              | none   => full)
          return (cts, ok)
        ctorNames := ctorNames.push (s.ctors.map (reroot s.indName s.name))
        ctorTypes := ctorTypes.push cts
        bridgeOk := bridgeOk.push ok
      let out ← k { inp with memberNames, memberTypes, memberFVars, ctorNames, ctorTypes }
      -- the members exist now, so the copies can be identified with the originals
      let ownLevels := inp.levelParams.map Level.param
      let vars := ps.extract 0 inp.numVars
      let repl := inp.memberNames.map fun n => mkAppN (.const n ownLevels) vars
      for j in *...st.specs.size do
        if bridgeOk[j]! then
          let b : Bridge := { spec := st.specs[j]!, members, repl }
          -- a bridge is a convenience; never let one failing take the block with it
          try
            mkBridge inp ps ctorNames (inp.memberNames.size + j) b
          catch _ => pure ()
      return out

/-- Do the members of the block end up in more than one universe? -/
def Input.isHeterogeneous (inp : Input) : MetaM Bool := do
  let mut first : Option Level := none
  for ty in inp.memberTypes do
    let l ← forallTelescope ty fun _ body => do
      let .sort l := (← whnf body) | return Level.zero
      return l
    match first with
    | none    => first := some l.normalize
    | some l0 => if l0 != l.normalize then return true
  return false

end Lean.Elab.MultiuniverseInductive
