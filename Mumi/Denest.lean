/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Mumi.Lowering
import Lean.Compiler.ImplementedByAttr

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
  /-- The application as it was *written*, abstracted over `extras`: `key` with
  a reducible alias left in place of the inductive behind it.  What the copy is
  identified with, so that it reads back as the type the writer named. -/
  origAbs   : Expr
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
Recognise a nested occurrence at the head of a strictly-positive position.

Answers `none` for anything that is not one: a position with no member in it at
all, a member applied to its own arguments, a type constructor that is not
inductive (`Quot`, a function), or an inductive applied to a member only outside
its parameters.
-/
private def nestedApp? (members : Array Expr) (body : Expr) :
    MetaM (Option (Expr × Expr × InductiveVal × List Level × Array Expr × Array Expr)) := do
  -- Specialising a parameter that is a function -- `Sigma`'s `β`, `Subtype`'s
  -- `p` -- leaves the fields of that type as redexes, and the nesting is only
  -- visible once they are reduced.
  let written := body.headBeta
  if !mentionsAny members written then return none
  if members.any (· == written.getAppFn) then return none
  let body ← exposeInduct written
  let .const iname lvls := body.getAppFn | return none
  let some (.inductInfo info) := (← getEnv).find? iname | return none
  let args := body.getAppArgs
  if args.size < info.numParams then return none
  let params := args.extract 0 info.numParams
  if !params.any (mentionsAny members ·) then return none
  -- A member `lower` produced is a reducible alias for its shadow, and the
  -- alias is what the writer typed.  Finding the inductive means seeing through
  -- it, but the copy should still read back as what was written, so the written
  -- head is kept when it stands for this very application.
  let visFn :=
    match written.getAppFn with
    | .const vn vls =>
      if iname == vn ++ `_shadow && written.getAppArgs.size == args.size then .const vn vls
      else .const iname lvls
    | _ => .const iname lvls
  return some (mkAppN (.const iname lvls) params, mkAppN visFn params, info, lvls,
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

mutual

/--
Intern the nested application at the head of `body`, if there is one, and then
look through the copy's own fields for further nesting.
-/
private partial def internNested (root : Name) (members ps : Array Expr) (body : Expr) :
    DenestM Unit := do
  let some (app, vis, info, lvls, params, idxArgs) ← nestedApp? members body | return
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
      origAbs := vis.abstract xs, indName := info.name, levels := lvls,
      ctors := info.ctors.toArray }
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
  forallTelescope ty.headBeta fun _ys body => internNested root members ps body

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
  /-- The copies that are being made. -/
  specs    : Array AuxSpec
  /-- Keys of the copies that are not, which are left as the writer wrote them. -/
  dropped  : Array Expr
  auxFVars : Array Expr

/-- Replace a nested application at the head of a strictly-positive position. -/
private def RwCtx.head (c : RwCtx) (body : Expr) : MetaM Expr := do
  let some (app, _, _, _, params, idxArgs) ← nestedApp? c.members body | return body
  let xs ← extraLocals c.ps c.members params
  let key := app.abstract xs
  let some k := c.specs.findIdx? (·.key == key)
    | if c.dropped.contains key then return body
      throwError m!"Cannot denest{indentExpr body}"
        ++ .note "this occurrence was not seen when the block was scanned"
  return mkAppN c.auxFVars[k]! (c.appPs ++ xs ++ idxArgs)

/-- Rewrite one strictly-positive position. -/
private def RwCtx.pos (c : RwCtx) (ty : Expr) : MetaM Expr :=
  forallTelescope ty.headBeta fun ys body => do mkForallFVars ys (← c.head body)

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

/-! ## Which copies are worth making

The kernel denests too, and better than this module can: it leaves the
constructor stated at the type the writer wrote, so `T.mk : List T → T` really
does have that type and `T.rec` really does get a motive at `List T`.  Making a
copy here costs all of that, and is worth paying for only where the kernel
would refuse -- which is the whole reason a block comes this way.

The clearest case where it would not refuse is a nesting that is not recursive
at all.  `List B` inside a member `A` names `B`, and if `B` names nothing of
`A`'s then `B` is declared first; by the time `A` is declared `List B` is an
ordinary closed type, and there is nothing to denest.  Such an occurrence is
left exactly as written.

A genuine nesting -- `Tree S` inside `S` -- is left alone too, as long as the
kernel would put the type it invents in the same universe as the component it
is invented for, because a mutual block has only one.  What that costs `lower`
is that its recursors have to range over more than the members it was handed;
what it buys is a constructor stated at the type the writer wrote.
-/

/--
The nodes a strictly-positive position depends on: every member it mentions,
and the copy it would become if it is a nested occurrence.  Members are numbered
as the block numbers them, and the copies follow.
-/
private def posDeps (members ps : Array Expr) (specs : Array AuxSpec) (ty : Expr) :
    MetaM (Array Nat) :=
  forallTelescope ty.headBeta fun _ body => do
    let mut out : Array Nat := #[]
    for i in *...members.size do
      if body.containsFVar members[i]!.fvarId! then out := out.push i
    if let some (app, _, _, _, params, _) ← nestedApp? members body then
      let xs ← extraLocals ps members params
      if let some k := specs.findIdx? (·.key == app.abstract xs) then
        out := out.push (members.size + k)
    return out

/-- The universe a member or a copy ends up in. -/
private def sortOf (ty : Expr) : MetaM Level :=
  forallTelescope ty fun _ body => do
    let .sort l := (← whnf body) | return Level.zero
    return l

/-- What is to become of a copy the scan found. -/
inductive SpecDecision where
  /-- Not made at all: the occurrence stays as the writer wrote it. -/
  | drop
  /-- Made, as a member of the block in the shadow and in the real world alike. -/
  | keep
  /-- Made in the shadow only, with the type it copies standing in for it
  everywhere else.  See `Lean.Elab.MultiuniverseInductive.GhostInfo`. -/
  | ghost
  deriving Inhabited, DecidableEq

/--
Is this copy one that could stand in the shadow alone?

What that asks of the copied type is that everything the real world would have
said about the copy can be said about it instead.  Its recursor has to be the
recursor of one type rather than of a family, since a ghost is one slot of the
block and one recursor is what a slot gets; and it must not itself be nested,
since the kernel's extra recursors for what it denested would then have no
slot to answer to.  Locals among the copy's parameters rule it out too: those
are what make a copy differ from the type it copies, and a nesting the kernel
will not take besides.

The rest of the conditions are about the block rather than about the type, and
`specDecisions` works them out.
-/
private def ghostable (s : AuxSpec) : MetaM Bool := do
  unless s.extras.isEmpty do return false
  let some (.inductInfo info) := (← getEnv).find? s.indName | return false
  if info.isNested || info.all.length != 1 then return false
  unless (← getEnv).contains (s.indName ++ `casesOn) do return false
  let some (.recInfo r) := (← getEnv).find? (s.indName ++ `rec) | return false
  return r.numMotives == 1 && r.numMinors == s.ctors.size

/--
Decide which of the copies the scan found actually have to be made, and which
of those the real world can do without.

A copy can be dropped when nothing it names is being declared alongside it: the
occurrence is then a closed type where it stands, and leaving it alone hands the
kernel an ordinary field.  Answering that takes the same condensation `analyze`
computes, run here on the enlarged block the copies would make.

Three things keep a copy:

* a `Prop` anywhere in the enlarged block.  The shadow copies every constructor
  field verbatim with the members redirected to their shadows, and a redirected
  `List B` reads `List B._shadow`, which is not even well-typed.
* locals among the copy's parameters, which the kernel refuses outright.
* sharing a component with a member of the block whose universe it does not
  share.  That is a genuine nesting, so the kernel would have to invent a type
  and declare it alongside the component -- which it can only do at the
  component's own universe.  Specialising is what lowers a copy's universe
  below the original's, and where it does, the copy is the only way through.

Keeping spreads along the copies' own dependencies, in both directions.  A copy
that stands is written into the fields of the copies above it, and a copy that
is dropped is written into their text, so two that reach each other have to be
kept or dropped together.

A copy kept for the first of those reasons is kept for the shadow's sake alone,
and the real world may still be able to do without it -- to write `List B`
where the shadow writes a member.  Such a copy becomes a *ghost*, which is what
keeps `Prop` out of the names the writer reads.  Beyond what `ghostable` asks of
the copied type, three things about the block have to hold, and they depend on
one another, so they are settled by retracting candidates until nothing more
gives way:

* a field at a ghost has to be one that can be written out in full.  In a `Prop`
  member's constructor, which the lowering emits as a definition, anything can
  be; in a data member's, which is the kernel's, `List B` is a nesting and the
  kernel has to be able to denest it -- so the two have to share a component and
  a universe, which is what makes it the nesting the kernel would have taken had
  no `Prop` forced a copy at all.
* a ghost's own fields have to be the copied type's, so every copy they mention
  must in turn stand for what it copies.
* its component has to have something declared in it, or be itself alone.  The
  recursion a ghost gets is its component's: the kernel's own, over what it
  denested, where there is a declared member to have handed it to, and the
  copied type's where the ghost stands by itself.  Two ghosts that recurse into
  each other and into nothing else have neither.
-/
private def specDecisions (inp : Input) (ps : Array Expr) (specs : Array AuxSpec) :
    MetaM (Array SpecDecision) := do
  let members := inp.memberFVars
  let n := members.size
  let m := specs.size
  let tot := n + m
  let mut isData : Array Bool := #[]
  let mut lvls : Array Level := #[]
  for ty in inp.memberTypes do
    let l := (← sortOf ty).normalize
    isData := isData.push (l != .zero)
    lvls := lvls.push l
  for s in specs do
    let l ← withExtras s fun xs => sortOf (s.resType.instantiateRev xs)
    let l := l.normalize
    isData := isData.push (l != .zero)
    lvls := lvls.push l
  let hasProp := isData.any (!·)
  let mut edges : Array (Array Bool) := Array.replicate tot (Array.replicate tot false)
  for i in *...n do
    for ct in inp.ctorTypes[i]! do
      let ds ← forallTelescope (← instantiateForall ct ps) fun fields _ => do
        let mut ds : Array Nat := #[]
        for x in fields do
          ds := ds ++ (← posDeps members ps specs (← inferType x))
        return ds
      for d in ds do edges := edges.modify i (·.set! d true)
  for j in *...m do
    let s := specs[j]!
    let ds ← withExtras s fun xs => do
      let params := s.paramsAbs.map (·.instantiateRev xs)
      let mut ds : Array Nat := #[]
      for ctor in s.ctors do
        let cinfo ← getConstInfoCtor ctor
        let cty ← instantiateForall
          (cinfo.type.instantiateLevelParams cinfo.levelParams s.levels) params
        ds := ds ++ (← forallTelescope cty fun fields _ => do
          let mut inner : Array Nat := #[]
          for x in fields do
            inner := inner ++ (← posDeps members ps specs (← inferType x))
          return inner)
      return ds
    for d in ds do edges := edges.modify (n + j) (·.set! d true)
  let (_, compOf) := computeSCCs tot isData edges
  let mut kept : Array Bool := #[]
  for j in *...m do
    kept := kept.push <| hasProp || !specs[j]!.extras.isEmpty ||
      (Array.range n).any fun i =>
        compOf[i]! == compOf[n + j]! && !lvls[i]!.isEquiv lvls[n + j]!
  let mut changed := true
  while changed do
    changed := false
    for a in *...m do
      for b in *...m do
        if a != b && kept[a]! && !kept[b]! &&
            (edges[n + a]![n + b]! || edges[n + b]![n + a]!) then
          kept := kept.set! b true
          changed := true
  unless hasProp do
    return kept.map fun k => if k then .keep else .drop
  -- a `Prop` in the block keeps every copy, so from here on nothing is dropped
  let mut ghost : Array Bool := #[]
  for j in *...m do
    ghost := ghost.push (isData[n + j]! && (← ghostable specs[j]!))
  changed := true
  while changed do
    changed := false
    for j in *...m do
      unless ghost[j]! do continue
      let declared (t : Nat) : Bool := isData[t]! && (t < n || !ghost[t - n]!)
      let sameComp (t : Nat) : Bool := compOf[t]! == compOf[n + j]!
      let fieldsOk := (Array.range tot).all fun t =>
        !(edges[t]![n + j]! && declared t) || (sameComp t && lvls[t]!.isEquiv lvls[n + j]!)
      let ownFieldsOk := (Array.range m).all fun k =>
        k == j || !edges[n + j]![n + k]! || ghost[k]!
      let baseOk := (Array.range tot).any (fun t => sameComp t && declared t) ||
        (Array.range tot).all fun t => t == n + j || !sameComp t
      unless fieldsOk && ownFieldsOk && baseOk do
        ghost := ghost.set! j false
        changed := true
  return (Array.range m).map fun j => if ghost[j]! then .ghost else .keep

/-! ## The bridge

An auxiliary member is a *copy* of the type that was nested, so the constructor
that took a `Nonempty T` now takes a `T.nested_Nonempty_1`.  When the copy is a
`Prop` the two are not merely isomorphic but equal, and saying so once lets the
original type back into the user's code:

```lean
example (h : Nonempty T) : T := T.mkT (T.nested_Nonempty_1.eq_orig ▸ h)
```

Both directions are the copy's recursor against the original's, which is
possible exactly because the two have the same constructors: `A.cᵢ`'s fields are
`I.cᵢ`'s with the nested occurrences rewritten, so each direction is one
recursor call per constructor, and the only question is what to hand the
constructor on the other side.  A field the rewriting left alone is handed over
as it stands.  A field at the copy being bridged is handed its induction
hypothesis, which is that field already on the other side.  A field at *another*
copy goes through that copy's own bridge -- so a nesting inside a nesting works,
as long as the inner one does, and the bridges are built innermost first.

`propext` turns the two implications into an equality and is the only axiom the
equality needs.  It is not needed to *use* the identification: the coercions
below are the implications themselves, so a term that moves a value between a
copy and its original depends on no axioms and still reduces.

What is left out is a field that mentions a copy anywhere else: in the domain of
one of its own binders, or in a nested position.  Nothing can be handed over for
such a field, so the member simply gets no bridge; the type itself is unaffected
either way.
-/

/--
Can this rewritten constructor type be sent across the bridge, and what does
that lean on?

A field that mentions no auxiliary member at all can be handed over as it
stands.  So can one whose own type *is* the member being bridged, however deep
under a telescope: the recursor supplies a hypothesis for such a field, already
at the type the other side wants.  A field at a *different* copy can be handed
over through that copy's own bridge, so the answer names which copies that is.
Anything else -- a copy in a nested position, or in a binder's domain -- has
nothing to be handed over as, and the answer is `none`.
-/
private def fieldsBridgeable (auxFVars : Array Expr) (self : Nat) (cty : Expr) :
    MetaM (Option (Array Nat)) :=
  forallTelescope cty fun fields _ => do
    let mut deps : Array Nat := #[]
    for f in fields do
      let some ks ← forallTelescope (← inferType f) fun ys concl => do
          for y in ys do
            if mentionsAny auxFVars (← inferType y) then return none
          let some k := auxFVars.idxOf? concl.getAppFn
            | return if mentionsAny auxFVars concl then none else some (#[] : Array Nat)
          if concl.getAppArgs.any (mentionsAny auxFVars ·) then return none
          return some #[k]
        | return none
      deps := deps ++ ks.filter (· != self)
    return some deps

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
  deriving Inhabited

/--
`I`'s parameters for a given choice of extras.

The substitution has to happen *after* the extras are put back, because
`Expr.replaceFVars` abstracts and reinstantiates, which would capture the
extras' own loose bound variables.
-/
private def Bridge.paramsAt (b : Bridge) (xs : Array Expr) : Array Expr :=
  b.spec.paramsAbs.map fun p => (p.instantiateRev xs).replaceFVars b.members b.repl

/-- The type the copy is identified with, for a given choice of extras: the
application the writer wrote, which is `I` at `paramsAt` up to unfolding a
reducible alias. -/
private def Bridge.origAt (b : Bridge) (xs : Array Expr) : Expr :=
  (b.spec.origAbs.instantiateRev xs).replaceFVars b.members b.repl

/--
Open the copy's index telescope and hand `k` the two sides of the
identification, along with the binders everything about it is stated over: the
block's parameters, the extras this copy was taken at, and the indices.
-/
private def Bridge.withSides {α : Type} [Inhabited α] (b : Bridge) (ownLevels : List Level)
    (ps xs : Array Expr) (k : Array Expr → Expr → Expr → Array Expr → MetaM α) : MetaM α :=
  forallTelescope (b.spec.resType.instantiateRev xs) fun idxs _ =>
    k idxs (mkAppN (.const b.spec.name ownLevels) (ps ++ xs ++ idxs))
      (mkAppN (b.origAt xs) idxs) (ps ++ xs ++ idxs)

/--
The recursor's motives: the original type for each member being bridged, and
`unit` -- the one-element type in whatever universe the recursor is being run
at -- for every other member it asks about.  Nothing is asked of those members,
which is why a `Prop` copy can pull the motive universe all the way down to
zero.

More than one member can be bridged at once because a nesting over a *mutual*
family copies every member of it, and each copy's fields reach the others.  Give
them all real motives and one pass of the recursor takes the whole family
across; the induction hypothesis for a field at a sibling then arrives already
on the other side, exactly as for a field at the copy itself.

`mIdxs` says which member each motive is for, since the recursor of a copy that
lowering could give a one-motive form to asks about only that copy.
-/
private def bridgeMotives (bridgeFor : Nat → Option Bridge) (unit : Expr) (mIdxs : Array Nat)
    (mtypes : Array Expr) : MetaM (Array Expr) := do
  let mut vals : Array Expr := #[]
  for i in *...mtypes.size do
    let v ← forallTelescope mtypes[i]! fun ys _ => do
      match bridgeFor mIdxs[i]! with
      | none => mkLambdaFVars ys unit
      | some b =>
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
Register a coercion from one side of the identification to the other, given `f`
taking the one to the other.

The equality alone would still leave the copy's name to be written out at every
use.  The pair of coercions is what removes it: one lets the original be passed
to a constructor that asks for the copy, the other lets a field bound by a
pattern match be used as the original.

`f` is one half of the `Iff` the equality was built from rather than a `cast`
along the equality, so a coerced term neither depends on `propext` nor gets
stuck on it.

Like any coercion, one is inserted only where the type it has to reach is
known; a consumer whose own type argument is still a metavariable needs the
field ascribed, and the ascription names the original rather than the copy.
`⟨...⟩` reads the expected type instead of being coerced afterwards, and is
handled separately in `Mumi.Bridge`.
-/
private def coeDecl (binders : Array Expr) (src tgt f : Expr) : MetaM (Expr × Expr) := do
  let type  ← mkForallFVars binders (← mkAppM ``CoeOut #[src, tgt])
  let value ← mkLambdaFVars binders (← mkAppM ``CoeOut.mk #[f])
  return (type, value)

/-- Add what `coeDecl` built, once the function it coerces by really exists. -/
private def addCoe (name : Name) (levelParams : List Name) (type value : Expr) : MetaM Unit := do
  check value
  unless ← isDefEq (← inferType value) type do return
  addDecl (.defnDecl
    { name, levelParams, type, value, hints := .abbrev, safety := .safe })
  setReducibleAttribute name
  Meta.addInstance name .global 1000

/-- How many binders a telescope starts with. -/
private def numForalls : Expr → Nat
  | .forallE _ _ b _ => numForalls b + 1
  | _ => 0

/--
The types the copy's constructor gives its fields, with the fields being handed
to it put in their place.

Going backwards, nothing in the original's own fields says that one of them
stands for a copy; only the copy's constructor knows, so its telescope is walked
alongside.
-/
private def copyFieldTypes (cty : Expr) (flds : Array Expr) : Array Expr := Id.run do
  let mut out : Array Expr := #[]
  let mut e := cty
  for f in flds do
    let .forallE _ d b _ := e | break
    out := out.push d
    e := b.instantiate1 f
  return out

/--
Send one field through another copy's bridge, if that is what it needs.

`ct` is the field's type on the copy's side, which is the side a copy shows up
on in either direction: going forwards it is the field's own type, going
backwards it is the type the copy's constructor wants.  When its head is a copy
with a bridge of its own, that bridge is what carries the field over -- pointwise,
under whatever binders an infinitary field takes.  Anything else already has the
type the other side wants and is handed over as it stands.

`over` is consulted before the environment is, and answers with a *term* to cross
by rather than a name.  That is what lets a group of copies that reach each other
be crossed by functions which do not exist yet: the companions of a mutual family
are built against variables standing for one another, and only then tied together.
-/
private def crossField (f ct : Expr) (dir : Name) (lvls : List Level) (copies : Array Name)
    (over : Name → Option Expr) : MetaM Expr := do
  forallBoundedTelescope (← inferType f) (some (numForalls ct)) fun ys _ => do
    let concl ← instantiateForall ct ys
    let some k := concl.getAppFn.constName? | return f
    let fn ←
      match over k with
      | some e => pure e
      | none   =>
        unless copies.contains k && (← getEnv).contains (k ++ dir) do return f
        pure (.const (k ++ dir) lvls)
    mkLambdaFVars ys (mkApp (mkAppN fn concl.getAppArgs) (mkAppN f ys))

/--
Which induction hypothesis, if any, each field of a minor premise has.

A minor premise binds the constructor's fields and then one hypothesis per
recursive field, and each hypothesis says which field it belongs to: its type
ends in the motive applied to that field.  Reading the pairing off that way is
the only reliable way to get it.  Counting fields whose head is the type being
recursed on does not do: a field can be at that very type without being a
recursive occurrence, as the field of `Nonempty (Nonempty α)` is.

This has to happen before the motives are instantiated, since instantiating them
is exactly what throws away the field a hypothesis names.  `mvs` are the motives
as they are still bound; a binder is a hypothesis when its type ends in one.
-/
private def minorPairing (mvs : Array Expr) (cty : Expr) : MetaM (Option (Array (Option Nat))) :=
  forallTelescope cty fun bs _ => do
    let mut ihFor : Array (Option Nat) := #[]
    let mut fields : Array Expr := #[]
    let mut nIH := 0
    for b in bs do
      let concl ← forallTelescope (← inferType b) fun _ c => pure c
      if mvs.contains concl.getAppFn then
        let some tgt := concl.getAppArgs.back? | return none
        let some i := fields.idxOf? tgt.getAppFn | return none
        if (ihFor[i]!).isSome then return none
        ihFor := ihFor.set! i (some nIH)
        nIH := nIH + 1
      else
        fields := fields.push b
        ihFor := ihFor.push none
    return some ihFor

/--
A recursor's minor premises: the type of each, and for each the field its
induction hypotheses are about.

The pairing has to be read while the motives are still bound, because
instantiating them is exactly what throws away which motive a hypothesis was
at.  The types have to be read after.  Two readings of one telescope that must
stay in step, so they are taken together.
-/
private def minorsOf (what : MessageData) (recTy : Expr) (motives : Array Expr)
    (numMinors : Nat) : MetaM (Array Expr × Array (Option (Array (Option Nat)))) := do
  let types ← forallBoundedTelescope (← instantiateForall recTy motives) (some numMinors)
    fun cvs _ => cvs.mapM inferType
  unless types.size == numMinors do
    throwError "{what} takes {types.size} cases, not {numMinors}"
  let pairings ← forallBoundedTelescope recTy (some motives.size) fun mvs body =>
    forallBoundedTelescope body (some numMinors) fun cvs _ =>
      cvs.mapM fun c => do minorPairing mvs (← inferType c)
  return (types, pairings)

/--
The arguments to give the constructor on the other side of the bridge.

A field at one of the members being bridged is handed over as its induction
hypothesis, which is already the value on the other side -- and for an
infinitary field is that function pointwise.  That covers the copy itself and,
when a whole mutual family is crossed at once, its siblings: they all have real
motives, so they all have usable hypotheses.  A field at a copy *outside* the
group goes through that copy's own bridge.  Anything else stands as it is,
including a field at a different member of the block, which is the same type on
both sides even though the recursor made a hypothesis for it too.

Which of those a field is, is decided by its type on the *copy's* side, `selves`
being the names of the copies this recursor pass settles: that is the one side
where the distinction is written down, and it reads the same going either way.
`over` carries a field at a copy outside that set but still being built, whose
direction is a variable until the group is put in.
-/
private def bridgeArgs (flds ihs copyTys : Array Expr) (ihFor : Array (Option Nat))
    (selves : Array Name) (dir : Name) (lvls : List Level) (copies : Array Name)
    (over : Name → Option Expr) : MetaM (Option (Array Expr)) := do
  let mut out : Array Expr := #[]
  for i in *...flds.size do
    let ct := copyTys[i]?.getD (← inferType flds[i]!)
    let atSelf ← forallTelescope ct fun _ c => pure
      (c.getAppFn.constName?.any (selves.contains ·))
    if atSelf then
      let some (some k) := ihFor[i]? | return none
      let some ih := ihs[k]? | return none
      out := out.push ih
    else
      out := out.push (← crossField flds[i]! ct dir lvls copies over)
  return some out

/--
Write one direction of a data bridge a second time, out of `casesOn` and a
recursive call, so that it can actually run.

The direction itself is a recursor application, and the code generator compiles
no recursor application at all; it does compile a `casesOn`, and it does compile
recursion inside an `unsafe` definition.  So the same function is built again in
a shape the compiler will take, and attached to the real one with
`@[implemented_by]`.  Nothing is trusted here: the safe definition is what the
kernel checked and what every proof sees, and a direction whose companion does
not go through simply stays `noncomputable`.

`casesOn` binds its parameters, then the motive, then the indices and the term
being taken apart, then one minor premise per constructor.  Each minor binds
`nLead` arguments the target constructor does not share -- the extras a copy
carries -- and then the fields; a field at `self` becomes a recursive call,
pointwise under whatever binders an infinitary one takes, and `rc` says at which
arguments.  A field at another copy crosses the same way it does in the checked
definition, through that copy's own direction, which has a companion of its own
and so runs; `copyTysOf` gives the copy's side of each field.  When that other
copy is a sibling in the same mutual family, `over` answers with the variable
standing for its companion instead, and the two end up genuinely mutually
recursive.
-/
private def implDirection (casesName : Name) (csLevels : List Level) (pre : Array Expr)
    (motive : Expr) (idxArgs : Array Expr) (srcTy : Expr) (nCtors nLead : Nat)
    (self : Name) (dir : Name) (lvls : List Level) (copies : Array Name)
    (over : Name → Option Expr)
    (copyTysOf : Nat → Array Expr → MetaM (Array Expr))
    (rc : Expr → Expr) (mkTarget : Nat → Array Expr → Array Expr → Expr) :
    MetaM (Option Expr) := do
  let some csInfo := (← getEnv).find? casesName | return none
  unless csInfo.levelParams.length == csLevels.length do return none
  let csTy ← instantiateForall
    (csInfo.type.instantiateLevelParams csInfo.levelParams csLevels) pre
  let afterMotive ← instantiateForall csTy #[motive]
  withLocalDeclD `x srcTy fun x => do
    let afterMajor ← instantiateForall afterMotive (idxArgs ++ #[x])
    let mtys ← forallBoundedTelescope afterMajor (some nCtors) fun mvs _ => mvs.mapM inferType
    unless mtys.size == nCtors do return none
    let mut minors : Array Expr := #[]
    for q in *...nCtors do
      minors := minors.push (← forallTelescope mtys[q]! fun flds _ => do
        let fs := flds.extract nLead flds.size
        let cts ← copyTysOf q fs
        let mut args : Array Expr := #[]
        for i in *...fs.size do
          let f := fs[i]!
          let fty ← inferType f
          let ct := cts[i]?.getD fty
          if ← forallTelescope ct fun _ c => pure (c.getAppFn.constName? == some self) then
            args := args.push (← forallTelescope fty fun ys concl =>
              mkLambdaFVars ys (mkApp (rc concl) (mkAppN f ys)))
          else
            args := args.push (← crossField f ct dir lvls copies over)
        mkLambdaFVars flds (mkTarget q (flds.extract 0 nLead) args))
    return some (← mkLambdaFVars #[x]
      (mkAppN (.const casesName csLevels) (pre ++ #[motive] ++ idxArgs ++ #[x] ++ minors)))

/--
Add the directions of a group of data bridges, with compiled companions if they
can be built.  A companion has to be in place before its direction is handed to
the code generator, which is why the two are added together.

`mkImpls` is handed one *variable* per direction, standing for every recursive
call the companions may make -- their own and each other's -- and gives back one
body per direction, closed but for those variables.  That is what lets the
companions be checked here rather than left to the kernel: once they are in the
environment their recursion is real, and a bad one would be reported at the
declaration the writer wrote rather than caught.  It is also what lets the
copies of a mutual family call one another, since the variables become names
only after every body is in hand, and the bodies then go in as a single block.

Companions are all-or-nothing, since a mutual block is: if any body cannot be
built or the block does not compile, every direction in the group stays
`noncomputable` and the environment is put back as it was.
-/
private def addDirections (levelParams : List Name) (ds : Array (Name × Expr × Expr))
    (mkImpls : Array Expr → MetaM (Option (Array Expr))) : MetaM Unit := do
  let decls := ds.map fun (name, type, value) =>
    Declaration.defnDecl { name, levelParams, type, value, hints := .regular 0, safety := .safe }
  for d in decls do addDecl d
  let lvls := levelParams.map Level.param
  let implNames := ds.map fun (name, _, _) => name ++ `impl
  let saved ← getEnv
  try
    let values ← withLocalDeclsD (ds.map fun (_, type, _) => (`rec_, fun _ => pure type))
        fun selves => do
      let some bodies ← mkImpls selves | throwError "no companion"
      unless bodies.size == selves.size do throwError "no companion"
      let consts := implNames.map fun n => Expr.const n lvls
      bodies.mapM fun body => do
        check (← mkLambdaFVars selves body)
        return body.replaceFVars selves consts
    let mut defns : Array DefinitionVal := #[]
    for i in *...ds.size do
      defns := defns.push
        { name := implNames[i]!, levelParams, type := ds[i]!.2.1, value := values[i]!,
          hints := .opaque, safety := .unsafe }
    let implDecl := match defns.toList with
      | [d] => Declaration.defnDecl d
      | l   => Declaration.mutualDefnDecl l
    addDecl implDecl
    compileDecl implDecl (logErrors := false)
    for n in implNames do
      if Lean.isNoncomputable (← getEnv) n then throwError "companion did not compile"
    for i in *...ds.size do Lean.setImplementedBy ds[i]!.1 implNames[i]!
  catch _ =>
    setEnv saved
  for d in decls do compileDecl d (logErrors := false)

/-- What one member's way back needs: the original's recursor read at this
member's parameters, with a motive for every copy one pass of it can settle and
`unit` for anything else it quantifies over. -/
private structure BwdData where
  levels  : List Level
  params  : Array Expr
  motives : Array Expr
  minors  : Array Expr
  /-- The motive standing for this member itself, which its compiled companion
  recurses at. -/
  selfMot : Expr
  /-- How many parameters the original takes, so that a recursive field of it
  can be cut down to its indices. -/
  numPs   : Nat
  deriving Inhabited

/-- Everything one member of a group contributes, worked out under its own
indices and then closed up, so that a group can be checked before any of it is
added. -/
private structure DirData where
  /-- Which of the group this is. -/
  gpos     : Nat
  /-- Which member of the block the copy belongs to. -/
  member   : Nat
  typeFwd  : Expr
  typeBwd  : Expr
  valueFwd : Expr
  valueBwd : Expr
  /-- The equality between the copy and its original, and its proof: a `Prop`
  copy has one, a data copy has only the two directions. -/
  eq?      : Option (Expr × Expr)
  /-- The motive this member's own forward companion recurses at. -/
  motiveJ  : Expr
  bwd      : BwdData
  deriving Inhabited

/--
Identify each `A ps xs idxs` in a group with the `I params idxs` it copies, and
make the identification usable without naming `A`, by registering a coercion in
each direction.

Two copies are equal to their originals to different degrees.  A `Prop` copy has
the same elements *and* the same proof irrelevance, so the two types are equal
outright, and that goes in as `A.eq_orig`; the forward coercion doubles as the
marker `Mumi.Bridge` reads to display `A` as the type it copies.  A data copy is
only isomorphic -- its constructors are genuinely different constants -- so all
there is to say is the pair of maps, and they go in under their own names,
`A.toOrig` and `A.ofOrig`.  Either way the coercions are what let the copy's
name stay out of the way at the use site.

A whole `group` is bridged at once, because nesting over a *mutual* family
copies every member of it and the copies reach each other: `Rose`'s copy has a
field at `Forest`'s and the other way about, so neither can be crossed before
the other.  Giving every copy in the family a real motive settles both at once,
and one pass of the recursor carries the family across.  A family of one is the
ordinary case and takes the same road.

Which copies one pass settles is not the same question as which family a type
belongs to, so it is read off the recursor: a motive is matched to a copy by the
whole application it quantifies over.  That is what lets a nesting over a type
which is *itself* nested work.  `RL α`, defined through `List (RL α)`, copies
both, and its recursor has a motive at each even though `List` is no relation of
it; `List`'s own recursor, meanwhile, reaches only the one.  A member whose
recursor falls short crosses the shortfall on its sibling's direction instead,
which is why the members are built against variables standing for one another
and only then put in, in an order in which each one's definition already exists.
A member that cannot be built at all costs the others nothing.

Nothing here can make the block worse: it runs after the block has been
declared, and reads only what is already in the environment.
-/
private def mkBridges (inp : Input) (ps : Array Expr) (ctorNames : Array (Array Name))
    (memberNames : Array Name) (group : Array (Nat × Bridge)) : TermElabM Unit := do
  let some (_, b0) := group[0]? | return
  let s0 := b0.spec
  let ownLevels := inp.levelParams.map Level.param
  -- The copies in a group all come of one nesting, so they share the locals
  -- abstracted out of it and the universes it was written at.  They need not be
  -- one family, and need not even be of one type constructor.
  unless group.all (fun (_, b) => b.spec.extras == s0.extras && b.spec.levels == s0.levels) do
    throwError "the copies in this group were not taken at one nesting"
  let selves := group.map fun (_, b) => b.spec.name
  let bridgeOf (i : Nat) : Option Bridge := (group.find? (·.1 == i)).map (·.2)
  withExtras s0 fun xs => do
    let sortOf (s : AuxSpec) : MetaM Level :=
      forallTelescope (s.resType.instantiateRev xs) fun _ sortE => do
        let .sort l := sortE | throwError "the copy does not end in a sort"
        return l
    let lvl ← sortOf s0
    let isProp := lvl.normalize.isZero
    -- a group is crossed by one recursor pass at one motive universe, so a
    -- `Prop` copy and a data copy cannot be in it together
    for (_, b) in group do
      unless (← sortOf b.spec).normalize.isZero == isProp do
        throwError "the group has a `Prop` copy and a data copy in it"
    -- the recursor's motive universe is the one level it does not share with
    -- the block.  A `Prop` copy asks only for a proposition, so it goes to
    -- zero; a data copy asks for the type it copies, and its recursor has to
    -- eliminate that far
    let mlvl := if isProp then Level.zero else lvl
    let unit    := if isProp then .const ``True [] else .const ``PUnit [mlvl]
    let unitVal := if isProp then .const ``True.intro [] else .const ``PUnit.unit [mlvl]
    -- the two statements, which are all that is needed to stand a member in for
    -- itself while the others are being built
    let statements ← group.mapM fun (_, b) =>
      b.withSides ownLevels ps xs fun _ lhs rhs bs => do
        return (← mkForallFVars bs (← mkArrow lhs rhs), ← mkForallFVars bs (← mkArrow rhs lhs))
    -- Which copy a motive of a recursor is for is read off the application it
    -- quantifies over.  A mutual family's recursor has a motive at each member;
    -- the recursor of a type that is itself nested has one at the type it nests
    -- through, which is no member of its family at all.
    let copyOfDomain (dty : Expr) : MetaM (Option (Nat × Bridge)) := do
      let some hd := dty.getAppFn.constName? | return none
      let some (.inductInfo hi) := (← getEnv).find? hd | return none
      let dps := dty.getAppArgs.extract 0 hi.numParams
      let mut hit : Option (Nat × Bridge) := none
      for (j, b) in group do
        if hit.isNone && b.spec.indName == hd then
          let key := mkAppN (.const b.spec.indName b.spec.levels) (b.paramsAt xs)
          if ← isDefEq (mkAppN (.const hd b.spec.levels) dps) key then
            hit := some (j, b)
      return hit
    withLocalDeclsD (statements.map fun (t, _) => (`fwd_, fun _ => pure t)) fun fvs => do
    withLocalDeclsD (statements.map fun (_, t) => (`bwd_, fun _ => pure t)) fun bvs => do
    -- a field at a copy the recursor in hand cannot settle crosses on that
    -- copy's own direction, which need not exist yet: the variable stands for
    -- it until the order in which they go in has been worked out
    let posIn (sel : Array Name) (vars : Array Expr) : Name → Option Expr := fun n =>
      (sel.idxOf? n).map fun i => vars[i]!
    let overF := posIn selves fvs
    let overB := posIn selves bvs
    -- Backward: the original's recursor, rebuilding each constructor as the
    -- copy's.  A motive with no copy behind it -- a family member this nesting
    -- never reached -- goes to `unit`, as do its cases.
    let bwdDataFor (b : Bridge) : MetaM BwdData := do
      let s := b.spec
      let bparams := b.paramsAt xs
      let some origRec := (← getEnv).find? (s.indName ++ `rec)
        | throwError "`{s.indName}` has no recursor"
      -- the original's recursor puts its motive universe first, if it has one
      let bLevels :=
        if origRec.levelParams.length == s.levels.length + 1 then mlvl :: s.levels else s.levels
      unless origRec.levelParams.length == bLevels.length do
        throwError "`{s.indName}.rec` takes {origRec.levelParams.length} universes, not \
          {bLevels.length}"
      let origTy ← instantiateForall
        (origRec.type.instantiateLevelParams origRec.levelParams bLevels) bparams
      -- the leading binders whose own type ends in a sort are the motives
      let nM ← forallTelescope origTy fun mvs _ => do
        let mut n := 0
        for m in mvs do
          let isS ← forallTelescope (← inferType m) fun _ c => pure c.isSort
          unless isS do break
          n := n + 1
        return n
      let mtypes ← forallBoundedTelescope origTy (some nM) fun mvs _ => mvs.mapM inferType
      let mut mFor  : Array (Option (Nat × Bridge)) := #[]
      let mut heads : Array Name := #[]
      for mt in mtypes do
        let (hit, hd) ← forallTelescope mt fun ys _ => do
          let some last := ys.back?
            | throwError "a motive of `{s.indName}.rec` quantifies over nothing"
          let dty ← inferType last
          let some hd := dty.getAppFn.constName?
            | throwError "a motive of `{s.indName}.rec` is not at an inductive type"
          return (← copyOfDomain dty, hd)
        mFor := mFor.push hit
        heads := heads.push hd
      let some k0 := mFor.findIdx? (fun h => h.any (·.2.spec.name == s.name))
        | throwError "`{s.indName}.rec` has no motive for the copy being bridged"
      let mut omotives : Array Expr := #[]
      for k in *...nM do
        omotives := omotives.push (← forallTelescope mtypes[k]! fun ys _ =>
          match mFor[k]! with
          | none => mkLambdaFVars ys unit
          | some (_, bj) => mkLambdaFVars ys
              (mkAppN (.const bj.spec.name ownLevels) (ps ++ xs ++ ys.extract 0 (ys.size - 1))))
      let mut nOMinors := 0
      for h in heads do nOMinors := nOMinors + (← getConstInfoInduct h).ctors.length
      let (otypes, opairings) ←
        minorsOf m!"`{s.indName}.rec`" origTy omotives nOMinors
      -- a field at a copy this recursor has a motive for arrives as an
      -- induction hypothesis; one at a copy it does not have to cross
      let covered := mFor.filterMap (·.map (·.2.spec.name))
      let mut ominors : Array Expr := #[]
      for k in *...nM do
        let kctors := (← getConstInfoInduct heads[k]!).ctors.toArray
        let copy? := mFor[k]!
        for q in *...kctors.size do
          let idx := ominors.size
          let some mnr ← (forallTelescope otypes[idx]! fun bs _ => do
            let some (jk, _) := copy? | return some (← mkLambdaFVars bs unitVal)
            let n := (← getConstInfoCtor kctors[q]!).numFields
            let flds := bs.extract 0 n
            let some ihFor := opairings[idx]! | return none
            -- The copy's own constructor is what says which of the original's
            -- fields stands for a copy, and at which arguments.  It need not be a
            -- kernel constructor: lowering leaves the user-visible ones as
            -- definitions over the shadow block it built, so only the type can be
            -- asked for.
            let ci ← getConstInfo ctorNames[jk]![q]!
            let cct ← instantiateForall
              (ci.type.instantiateLevelParams ci.levelParams ownLevels) (ps ++ xs)
            let some args ← bridgeArgs flds (bs.extract n bs.size) (copyFieldTypes cct flds)
                ihFor covered `ofOrig ownLevels memberNames overB | return none
            return some (← mkLambdaFVars bs
              (mkAppN (.const ctorNames[jk]![q]! ownLevels) (ps ++ xs ++ args))))
            | throwError "no arguments for `{kctors[q]!}` going back"
          ominors := ominors.push mnr
      return { levels := bLevels, params := bparams, motives := omotives, minors := ominors,
               selfMot := omotives[k0]!, numPs := (← getConstInfoInduct s.indName).numParams }
    -- Forward: each copy's recursor, one case per constructor it asks about.
    -- That is every member of the lowered block -- unless lowering managed to
    -- give this copy a recursor over fewer, in which case only those get a
    -- hypothesis and the rest of the group is crossed.
    let mut built : Array DirData := #[]
    for gp in *...group.size do
      let (jm, b) := group[gp]!
      try
        let s := b.spec
        let some recInfo := (← getEnv).find? (s.name ++ `rec)
          | throwError "the copy has no recursor"
        let recLevels := recInfo.levelParams.map fun p =>
          if inp.levelParams.contains p then .param p else mlvl
        let recTy ← instantiateForall
          (recInfo.type.instantiateLevelParams recInfo.levelParams recLevels) ps
        -- Which motive is whose is read off what it quantifies over, since a
        -- native recursor's motives run over its own block and then over whatever
        -- the kernel denested, and only their domains tell those apart.  The
        -- block-wide recursor the lowering builds needs no guessing -- it has one
        -- motive per member, in member order -- and must not be guessed at: a
        -- ghost's motive is at the type it stands for, which names no member.
        let mIdxs ←
          if recInfo matches .recInfo _ then
            forallBoundedTelescope recTy (some ctorNames.size) fun mvs _ => do
              let mut out : Array Nat := #[]
              for m in mvs do
                let k? ← forallTelescope (← inferType m) fun ys c => do
                  unless c.isSort do return none
                  let some last := ys.back? | return none
                  let some hd := (← inferType last).getAppFn.constName? | return none
                  return memberNames.idxOf? hd
                let some k := k? | break
                out := out.push k
              return out
          else
            pure (Array.range ctorNames.size)
        unless mIdxs.contains jm do
          throwError "the copy's recursor has no motive for it"
        let mtypes ← forallBoundedTelescope recTy (some mIdxs.size) fun mvs _ =>
          mvs.mapM inferType
        let motives ← bridgeMotives bridgeOf unit mIdxs mtypes
        -- only the copies this recursor reaches have a hypothesis to offer
        let fselves := mIdxs.filterMap fun i => (bridgeOf i).map (·.spec.name)
        let nCases := mIdxs.foldl (fun n i => n + ctorNames[i]!.size) 0
        let (ctypes, pairings) ←
          minorsOf m!"the copy's recursor" recTy motives nCases
        let mut cases : Array Expr := #[]
        for i in mIdxs do
          let bi? := bridgeOf i
          for q in *...ctorNames[i]!.size do
            let idx := cases.size
            let some cse ← (forallTelescope ctypes[idx]! fun bs _ => do
              let some bi := bi? | return some (← mkLambdaFVars bs unitVal)
              let si := bi.spec
              -- the leading arguments of the copy's constructor are the extras and
              -- then the original constructor's own fields; the rest of the case's
              -- binders are the induction hypotheses
              let n := si.extras.size + (← getConstInfoCtor si.ctors[q]!).numFields
              let xs' := bs.extract 0 si.extras.size
              let flds := bs.extract si.extras.size n
              let some ihFor := pairings[idx]! | return none
              let some args ← bridgeArgs flds (bs.extract n bs.size) (← flds.mapM inferType)
                  (ihFor.extract si.extras.size ihFor.size) fselves `toOrig ownLevels memberNames
                  overF
                | return none
              return some (← mkLambdaFVars bs
                (mkAppN (.const si.ctors[q]! si.levels) (bi.paramsAt xs' ++ args))))
              | throwError "no arguments for `{ctorNames[i]![q]!}` going forwards"
            cases := cases.push cse
        let bwd ← bwdDataFor b
        let (typeFwd, typeBwd) := statements[gp]!
        let d ← b.withSides ownLevels ps xs fun idxs lhs rhs bs => do
          let fwdE := mkAppN (.const (s.name ++ `rec) recLevels)
            (ps ++ motives ++ cases ++ xs ++ idxs)
          let bwdE := mkAppN (.const (s.indName ++ `rec) bwd.levels)
            (bwd.params ++ bwd.motives ++ bwd.minors ++ idxs)
          let eq? ← if isProp then
              let proof := mkApp3 (.const ``propext []) lhs rhs
                (mkApp4 (.const ``Iff.intro []) lhs rhs fwdE bwdE)
              pure (some (← mkForallFVars bs (← mkEq lhs rhs), ← mkLambdaFVars bs proof))
            else pure none
          return { gpos := gp, member := jm, typeFwd, typeBwd,
                   valueFwd := ← mkLambdaFVars bs fwdE, valueBwd := ← mkLambdaFVars bs bwdE,
                   eq?, motiveJ := motives[mIdxs.idxOf jm]!, bwd }
        -- Check before adding: `addDecl` reports a bad declaration rather than
        -- refusing it, and a bridge must never be able to say anything.  A
        -- variable standing in for a sibling has exactly the type the constant
        -- replacing it will have, so what is checked here is what goes in.
        let checked (what : String) (type value : Expr) : MetaM Unit := do
          check value
          unless ← isDefEq (← inferType value) type do
            throwError "{what}: {← inferType value} is not {type}"
        checked "forwards" d.typeFwd d.valueFwd
        checked "backwards" d.typeBwd d.valueBwd
        if let some (type, value) := d.eq? then checked "the equality" type value
        built := built.push d
      catch e =>
        trace[Mumi] "no bridge from `{b.spec.name}` to `{b.spec.indName}`: {e.toMessageData}"
    -- A definition can only name one already in the environment, so those that
    -- crossed on a sibling go in after it.  A cycle would need them defined
    -- simultaneously, which no recursor can do, so a member left in one is
    -- dropped -- as is one waiting on a sibling that could not be built.
    let ids := (fvs ++ bvs).map (·.fvarId!)
    let needs := built.map fun d =>
      (Array.range group.size).filter fun j =>
        j != d.gpos &&
          [d.valueFwd, d.valueBwd].any fun v =>
            v.hasAnyFVar fun i => i == ids[j]! || i == ids[group.size + j]!
    let mut ord : Array Nat := #[]
    let mut changed := true
    while changed do
      changed := false
      for k in *...built.size do
        unless ord.contains k do
          let ready := needs[k]!.all fun j =>
            match built.findIdx? (·.gpos == j) with
            | none   => false
            | some i => i == k || ord.contains i
          if ready then
            ord := ord.push k
            changed := true
    if ord.isEmpty then return
    -- what stayed has been checked, and can now be said in terms of itself
    let names := ord.map fun k => group[built[k]!.gpos]!.2.spec.name
    let toConsts (e : Expr) : Expr := e.replaceFVars (fvs ++ bvs)
      ((group.map fun (_, b) => .const (b.spec.name ++ `toOrig) ownLevels) ++
       (group.map fun (_, b) => .const (b.spec.name ++ `ofOrig) ownLevels))
    let ok := ord.map fun k =>
      let d := built[k]!
      { d with valueFwd := toConsts d.valueFwd, valueBwd := toConsts d.valueBwd,
               eq? := d.eq?.map fun (t, v) => (t, toConsts v) }
    if isProp then
      -- an implication between propositions is a theorem, and nothing the code
      -- generator has to be told about
      for k in *...ok.size do
        let d := ok[k]!
        addDecl (.thmDecl { name := names[k]! ++ `toOrig, levelParams := inp.levelParams,
                            type := d.typeFwd, value := d.valueFwd })
        addDecl (.thmDecl { name := names[k]! ++ `ofOrig, levelParams := inp.levelParams,
                            type := d.typeBwd, value := d.valueBwd })
        if let some (type, value) := d.eq? then
          addDecl (.thmDecl
            { name := names[k]! ++ `eq_orig, levelParams := inp.levelParams, type, value })
    else
      -- Each direction is a recursor application, which the code generator
      -- cannot take, so each is given a compiled companion; if that does not go
      -- through the definition stays `noncomputable`, and the error at the use
      -- site then names `toOrig` rather than a recursor the writer never
      -- mentioned.  The group's companions in one direction go in together,
      -- since a family that reaches itself needs them mutually recursive.
      let csLevels? (n : Name) : MetaM (Option (List Level)) := do
        let some ci := (← getEnv).find? n | return none
        return some (ci.levelParams.map fun p =>
          if inp.levelParams.contains p then .param p else mlvl)
      -- a field at a sibling crosses by the variable standing for that sibling's
      -- companion, which is what ties the block together
      let over := posIn names
      let fwdDs := ok.mapIdx fun k d => (names[k]! ++ `toOrig, d.typeFwd, d.valueFwd)
      let bwdDs := ok.mapIdx fun k d => (names[k]! ++ `ofOrig, d.typeBwd, d.valueBwd)
      -- a direction goes in whole or not at all, so one member the `casesOn`
      -- cannot be written for gives up the whole group's companions
      let bodiesOf (f : Nat → DirData → Bridge → Array Expr → Expr → Expr →
            Array Expr → MetaM (Option Expr)) (vars : Array Expr) :
          MetaM (Option (Array Expr)) := do
        let mut bodies : Array Expr := #[]
        for k in *...ok.size do
          let d := ok[k]!
          let b := group[d.gpos]!.2
          let some body ← (b.withSides ownLevels ps xs fun idxs lhs rhs bs => do
            let some e ← f k d b idxs lhs rhs vars | return none
            return some (← mkLambdaFVars bs e))
            | return none
          bodies := bodies.push body
        return some bodies
      addDirections inp.levelParams fwdDs <| bodiesOf fun k d b idxs lhs _ vars => do
        let s := b.spec
        let some csLevels ← csLevels? (s.name ++ `casesOn) | return none
        -- a recursive field of the copy is the copy at its own arguments, and
        -- those are exactly the arguments the companion takes
        implDirection (s.name ++ `casesOn) csLevels ps d.motiveJ
          (xs ++ idxs) lhs ctorNames[d.member]!.size s.extras.size s.name `toOrig ownLevels
          memberNames (over vars) (fun _ fs => fs.mapM inferType)
          (fun concl => mkAppN vars[k]! concl.getAppArgs)
          (fun q lead args => mkAppN (.const s.ctors[q]! s.levels) (b.paramsAt lead ++ args))
      addDirections inp.levelParams bwdDs <| bodiesOf fun k d b idxs _ rhs vars => do
        let s := b.spec
        -- the original's parameters are fixed by the extras, so a recursive
        -- field of the original differs from this one only in its indices
        implDirection (s.indName ++ `casesOn) d.bwd.levels d.bwd.params
          d.bwd.selfMot idxs rhs s.ctors.size 0 s.name `ofOrig ownLevels
          memberNames (over vars)
          (fun q fs => do
            let ci ← getConstInfo ctorNames[d.member]![q]!
            return copyFieldTypes (← instantiateForall
              (ci.type.instantiateLevelParams ci.levelParams ownLevels) (ps ++ xs)) fs)
          (fun concl => mkAppN vars[k]!
            (ps ++ xs ++ concl.getAppArgs.extract d.bwd.numPs concl.getAppArgs.size))
          (fun q _ args =>
            mkAppN (.const ctorNames[d.member]![q]! ownLevels) (ps ++ xs ++ args))
    -- The coercions name the two directions, so they come last.  For a `Prop`
    -- copy those are the two halves of the `Iff` rather than a `cast` along the
    -- equality: `propext` is what makes the two *types* equal, and nothing that
    -- merely moves a value between them should depend on it.
    for k in *...ok.size do
      let d := ok[k]!
      let s := group[d.gpos]!.2.spec
      group[d.gpos]!.2.withSides ownLevels ps xs fun _ lhs rhs bs => do
        let (t, v) ← coeDecl bs lhs rhs (mkAppN (.const (s.name ++ `toOrig) ownLevels) bs)
        addCoe (origCoeName s.name) inp.levelParams t v
        let (t, v) ← coeDecl bs rhs lhs (mkAppN (.const (s.name ++ `ofOrig) ownLevels) bs)
        addCoe (s.name ++ `coeOfOrig) inp.levelParams t v

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
    -- a copy the kernel can do without is not made, and the occurrence stays as
    -- the writer wrote it; the ones that are made are renumbered so that their
    -- names have no gaps
    let decisions ← specDecisions inp ps st.specs
    let mut dropped : Array Expr := #[]
    let mut specs : Array AuxSpec := #[]
    let mut isGhost : Array Bool := #[]
    for j in *...st.specs.size do
      let s := st.specs[j]!
      match decisions[j]! with
      | .drop => dropped := dropped.push s.key
      | d =>
        specs := specs.push { s with
          name := root ++ Name.mkSimple s!"nested_{shortName s.indName}_{specs.size + 1}" }
        isGhost := isGhost.push (d == .ghost)
    if specs.isEmpty then return (← k inp)
    let appPs := ps.extract inp.numVars ps.size
    let mut decls : Array (Name × Expr) := #[]
    let mut auxTypes : Array Expr := #[]
    for s in specs do
      let (full, app) ← withExtras s fun xs => do
        let res := s.resType.instantiateRev xs
        return (← mkForallFVars (ps ++ xs) res, ← mkForallFVars (appPs ++ xs) res)
      decls := decls.push (s.name, app)
      auxTypes := auxTypes.push full
    withLocalDeclsDND decls fun auxFVars => do
      let c : RwCtx := { members, appPs, ps, specs, dropped, auxFVars }
      let mut memberNames := inp.memberNames
      let mut memberTypes := inp.memberTypes
      let mut memberFVars := inp.memberFVars
      let mut ctorNames   := inp.ctorNames
      let mut ctorTypes   := inp.ctorTypes
      let mut bridgeDeps  : Array (Option (Array Nat)) := #[]
      let mut memberGhost : Array (Option GhostInfo) :=
        Array.replicate inp.memberNames.size none
      -- A ghost's free variable stands for the type it copies, so a field at
      -- one is an ordinary field of that type and needs no bridge; taking it
      -- for a copy would leave the copies above it waiting for a bridge that is
      -- never built.  What the block itself is handed keeps the free variable:
      -- the ghost is still a member there, and `lower` substitutes.
      let ghostFVars := (Array.range specs.size).filterMap fun j =>
        if isGhost[j]! then some auxFVars[j]! else none
      let ghostVals ← (Array.range specs.size).filterMapM fun j =>
        if isGhost[j]! then
          return some (← mkLambdaFVars appPs specs[j]!.origAbs)
        else
          return none
      let unghost (e : Expr) : MetaM Expr :=
        if ghostFVars.isEmpty then pure e
        else Core.betaReduce (e.replaceFVars ghostFVars ghostVals)
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
      for j in *...specs.size do
        let s := specs[j]!
        memberNames := memberNames.push s.name
        memberTypes := memberTypes.push auxTypes[j]!
        memberFVars := memberFVars.push auxFVars[j]!
        let (cts, deps) ← withExtras s fun xs => do
          let params := s.paramsAbs.map (·.instantiateRev xs)
          let mut cts : Array Expr := #[]
          let mut deps : Option (Array Nat) := some #[]
          for ctor in s.ctors do
            let cinfo ← getConstInfoCtor ctor
            let cty ← instantiateForall
              (cinfo.type.instantiateLevelParams cinfo.levelParams s.levels) params
            let rw ← c.pi cty
            match ← fieldsBridgeable auxFVars j (← unghost rw) with
            | none    => deps := none
            | some ds => if let some acc := deps then deps := some (acc ++ ds)
            let full ← mkForallFVars (ps ++ xs) rw
            cts := cts.push (match model? with
              | some m => withLeadingBinderInfo inp.numParams m full
              | none   => full)
          return (cts, deps)
        ctorNames := ctorNames.push (s.ctors.map (reroot s.indName s.name))
        ctorTypes := ctorTypes.push cts
        -- a ghost is its own original, so there is nothing to bridge to
        bridgeDeps := bridgeDeps.push (if isGhost[j]! then none else deps)
        let ghost? : Option GhostInfo ←
          if isGhost[j]! then do
            let value ← mkLambdaFVars ps s.origAbs
            let numParams := (← getConstInfoInduct s.indName).numParams
            pure (some { value, head := s.indName, levels := s.levels, numParams,
                         ctors := s.ctors })
          else
            pure none
        memberGhost := memberGhost.push ghost?
      let out ← k { inp with memberNames, memberTypes, memberFVars, ctorNames, ctorTypes,
                             memberGhost,
                             localIndices := specs.any (!·.extras.isEmpty) }
      -- the members exist now, so the copies can be identified with the originals
      let ownLevels := inp.levelParams.map Level.param
      let vars := ps.extract 0 inp.numVars
      let repl := inp.memberNames.map fun n => mkAppN (.const n ownLevels) vars
      -- Copies that reach each other cannot be crossed one at a time: nesting
      -- over a mutual family copies every member of it, and `Rose`'s copy has a
      -- field at `Forest`'s exactly as `Forest`'s has one at `Rose`'s, so
      -- neither bridge can be built before the other.  Those go together, and
      -- the groups are precisely the cycles of the dependency graph.  Being of
      -- one family is not enough on its own: two members of a `mutual` block
      -- that do not actually reach each other are still bridged one at a time,
      -- and the second then crosses its field on the first's bridge.
      let n := specs.size
      let mut reach : Array (Array Bool) := Array.replicate n (Array.replicate n false)
      for j in *...n do
        if let some ds := bridgeDeps[j]! then
          for k in ds do
            if k < n then reach := reach.modify j (·.set! k true)
      for m in *...n do
        for j in *...n do
          if reach[j]![m]! then
            for k in *...n do
              if reach[m]![k]! then reach := reach.modify j (·.set! k true)
      let mut gid    : Array Nat := Array.replicate n n
      let mut groups : Array (Array Nat) := #[]
      for j in *...n do
        if gid[j]! != n then continue
        let g := groups.size
        let mut mem : Array Nat := #[j]
        gid := gid.set! j g
        for k in *...n do
          if k > j && gid[k]! == n && reach[j]![k]! && reach[k]![j]! then
            gid := gid.set! k g
            mem := mem.push k
        groups := groups.push mem
      -- A group that leans on another group's bridges only has them if that one
      -- does, and has to be built after it.  Which comes first is not decided by
      -- the order they were interned in -- two occurrences of the same nesting
      -- share one member, so `List (List T)` finds its inner copy already
      -- there -- so the order is worked out here instead.  Nesting is well
      -- founded, so taking whichever group is ready next always finishes.
      let mut built : Array Bool := Array.replicate specs.size false
      let mut done  : Array Bool := Array.replicate groups.size false
      let mut progress := true
      while progress do
        progress := false
        for g in *...groups.size do
          if done[g]! then continue
          let mut ready := true
          for j in groups[g]! do
            match bridgeDeps[j]! with
            | none    => ready := false
            | some ds => unless ds.all (fun k =>
                k < specs.size && (gid[k]! == g || built[k]!)) do ready := false
          unless ready do continue
          done := done.set! g true
          progress := true
          let grp := groups[g]!.map fun j =>
            (inp.memberNames.size + j, ({ spec := specs[j]!, members, repl } : Bridge))
          -- a bridge is a convenience; never let one failing take the block with it
          try
            mkBridges inp ps ctorNames memberNames grp
          catch e =>
            let s := specs[groups[g]![0]!]!
            trace[Mumi] "no bridge from `{s.name}` to `{s.indName}`: {e.toMessageData}"
          -- what the copies that lean on these need is the pair of directions,
          -- so whether they can go ahead is exactly whether it is there -- not
          -- whether `mkBridges` was asked to build it
          for j in groups[g]! do
            if (← getEnv).contains (specs[j]!.name ++ `toOrig) then
              built := built.set! j true
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
