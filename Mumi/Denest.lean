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
      for i in *...ctorTypes.size do
        let mut cts : Array Expr := #[]
        for ct in ctorTypes[i]! do
          cts := cts.push (← mkForallFVars ps (← c.pi (← instantiateForall ct ps)))
        ctorTypes := ctorTypes.set! i cts
      for j in *...st.specs.size do
        let s := st.specs[j]!
        memberNames := memberNames.push s.name
        memberTypes := memberTypes.push auxTypes[j]!
        memberFVars := memberFVars.push auxFVars[j]!
        let cts ← withExtras s fun xs => do
          let params := s.paramsAbs.map (·.instantiateRev xs)
          let mut cts : Array Expr := #[]
          for ctor in s.ctors do
            let cinfo ← getConstInfoCtor ctor
            let cty ← instantiateForall
              (cinfo.type.instantiateLevelParams cinfo.levelParams s.levels) params
            cts := cts.push (← mkForallFVars (ps ++ xs) (← c.pi cty))
          return cts
        ctorNames := ctorNames.push (s.ctors.map (reroot s.indName s.name))
        ctorTypes := ctorTypes.push cts
      k { inp with memberNames, memberTypes, memberFVars, ctorNames, ctorTypes }

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
