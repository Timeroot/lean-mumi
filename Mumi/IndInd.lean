/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Mumi.Lowering
public import Lean.Elab.MutualInductive
import all Lean.Elab.MutualInductive

/-!
# Induction-induction, when the dependency runs only through `Prop`

A block is *induction-inductive* when one member's **arity** mentions another,

```lean
mutual
inductive Ctx : Type where
  | nil  : Ctx
  | snoc : (Γ : Ctx) → (x : String) → Fresh x Γ → Ctx
inductive Fresh : String → Ctx → Prop where
  | nil  : (x : String) → Fresh x .nil
  | snoc : (x y : String) → (Γ : Ctx) → (h : Fresh y Γ) → x ≠ y → Fresh x Γ →
      Fresh x (.snoc Γ y h)
end
```

`Fresh`'s arity mentions `Ctx`.  This is a different obstruction from the one
`Mumi.Lowering` lifts.  Universe heterogeneity is a *check* on an elaborated
block; here the block does not elaborate at all, because Lean elaborates every
member's arity before any member is in scope, so `Ctx` in `Fresh`'s arity is an
unknown identifier.  Collapsing the block to one universe does not help.

## The narrow class

We handle the case where the induction-induction runs **only through proofs**:
every field of a data constructor whose type mentions a `Prop` member of the
block is itself a proof.  Then that field can be *erased*, and what is left is
an ordinary, non-induction-inductive block.  For the example above:

```lean
inductive Ctx._pre : Type where
  | nil  : Ctx._pre
  | snoc : Ctx._pre → String → Ctx._pre

inductive Fresh._pre : String → Ctx._pre → Prop where
  | nil  (x : String) : Fresh._pre x .nil
  | snoc (x y : String) (Γ : Ctx._pre) (h : Fresh._pre y Γ) (hne : x ≠ y)
      (hx : Fresh._pre x Γ) : Fresh._pre x (.snoc Γ y)
```

`Ctx._pre` has forgotten which of its elements are real `Ctx`s, so a predicate
puts that back.  It is a *function*, not an inductive:

```lean
def Ctx._wf : Ctx._pre → Prop :=
  Ctx._pre.rec (motive := fun _ => Prop) True (fun Γ x ih => ih ∧ Fresh._pre x Γ)

def Ctx   := { Γ : Ctx._pre // Ctx._wf Γ }
def Fresh (x : String) (Γ : Ctx) : Prop := Fresh._pre x Γ.val
```

Being a function is what makes the encoding cheap: `Ctx._wf (.snoc Γ x)` *is*
`Ctx._wf Γ ∧ Fresh._pre x Γ`, definitionally, so "inversion" is `And.left` and
`And.right` and no inversion lemmas have to be generated.  One conjunct per
recursive field (the sub-term is well formed) and one per erased field (the
proof it carried).

The constructors are then definitions rather than constructors, and the
recursor is written by structural recursion on the pre-type with the
well-formedness proof threaded through:

```lean
def Ctx.recAux {C : Ctx → Sort u} (nil : C Ctx.nil)
    (snoc : (Γ : Ctx) → (x : String) → (h : Fresh x Γ) → C Γ → C (Ctx.snoc Γ x h)) :
    (Γ₀ : Ctx._pre) → (w : Ctx._wf Γ₀) → C ⟨Γ₀, w⟩
  | .nil,          _ => nil
  | .snoc Γ₀ x,    w => snoc ⟨Γ₀, w.1⟩ x w.2 (Ctx.recAux nil snoc Γ₀ w.1)

def Ctx.recursor {C : Ctx → Sort u} .. (Γ : Ctx) : C Γ :=
  Ctx.recAux nil snoc Γ.val Γ.property
```

Both iota rules hold by `rfl`, and the encoding adds no axioms.  That rests on
the same two things the heterogeneous lowering rests on: definitional proof
irrelevance, which collapses the `_wf` proofs, and definitional eta for
structures, which gives `⟨Γ.val, Γ.property⟩ ≡ Γ`.

`recAux` is written by structural recursion rather than as a `Ctx._pre.rec`
application for the reason spelled out in `Mumi.Lowering`: the code generator
compiles no recursor application, so the direct term would be `noncomputable`
and so would everything downstream.  Lean's own `Structural.structuralRecursion`
does the work; if it cannot see that the definition terminates, that is an
error at the point of the block rather than a silent fallback.

## What this does not do

* Only one data member.  Several `Prop` members are fine.
* No parameters, no section `variable`s, no user universe parameters, and the
  data member may not be indexed.
* A data constructor field mentioning a `Prop` member must be a proof; that is
  the "narrow" in narrow class.  A block whose data genuinely depends on data
  -- `Ctx` indexed by its own length, say -- is out of scope.
* The data member's constructors are `def`s, so `match` on them does not work
  and there is no `injEq` or `noConfusion`.  Reason with
  `induction Γ using Ctx.recursor with | nil => .. | snoc Γ x h ih => ..`; a
  bare `induction` or `cases` destructs the subtype and leaks `Ctx._pre` into
  the goal.
* `cases` on a `Prop` member fails ("dependent elimination failed"), because its
  recursor is still `Fresh._pre`'s, stated over the pre-type.  Deriving a real
  `Fresh.rec` from it -- motive `fun x Γ₀ h => ∀ w, motive x ⟨Γ₀, w⟩ h` -- is
  the obvious next step and is not done here.
-/

public section

namespace Mumi.IndInd

open Lean Lean.Meta Lean.Elab Lean.Elab.Command
open Lean.Elab.MultiuniverseInductive (addDef addInd reroot)

/-! ## Names -/

/-- The erased pre-type of member `n`. -/
def preName (n : Name) : Name := n ++ `_pre

/-- `X._wf : X._pre → Prop`, the well-formedness predicate on the pre-type. -/
def wfName (n : Name) : Name := n ++ `_wf

/-! ## The block, as we analyse it -/

/-- What becomes of one field of a constructor under erasure. -/
inductive FieldKind where
  /-- Mentions no member of the block; kept as it stands. -/
  | plain
  /-- Its type *is* the data member; kept, at the pre-type. -/
  | recur
  /-- A proof mentioning a `Prop` member; dropped, and remembered by `_wf`. -/
  | erased
  deriving Inhabited, DecidableEq, Repr

structure CtorSpec where
  name  : Name
  /-- `∀ fields, M idxs`, with the members and their constructors as constants. -/
  type  : Expr
  kinds : Array FieldKind
  deriving Inhabited

structure MemberSpec where
  name   : Name
  /-- `∀ idxs, Sort l`, with the members as constants. -/
  type   : Expr
  isProp : Bool
  ctors  : Array CtorSpec
  deriving Inhabited

structure Block where
  members : Array MemberSpec
  /-- Index into `members` of the one data member. -/
  dataIdx : Nat
  deriving Inhabited

def Block.data (b : Block) : MemberSpec := b.members[b.dataIdx]!

def Block.props (b : Block) : Array MemberSpec := b.members.filter (·.isProp)

/-- The positions of the fields a constructor keeps. -/
def keptPositions (kinds : Array FieldKind) : Array Nat := Id.run do
  let mut out := #[]
  for i in *...kinds.size do
    if kinds[i]! != .erased then out := out.push i
  return out

/-- The positions of a constructor's recursive fields. -/
def recPositions (kinds : Array FieldKind) : Array Nat := Id.run do
  let mut out := #[]
  for i in *...kinds.size do
    if kinds[i]! == .recur then out := out.push i
  return out

/-- `X ↦ X._pre`, and `X.c ↦ X._pre.c` for a constructor of `X`. -/
def Block.preOf (b : Block) (n : Name) : Name := Id.run do
  for m in b.members do
    if n == m.name then return preName m.name
    for c in m.ctors do
      if n == c.name then return reroot m.name (preName m.name) c.name
  return n

/-- The fields a data constructor keeps, or `none` if `n` is not one. -/
def Block.keptOf (b : Block) (n : Name) : Option (Array Nat) := Id.run do
  for m in b.members do
    unless m.isProp do
      for c in m.ctors do
        if n == c.name then return some (keptPositions c.kinds)
  return none

/--
The block's own view of an expression, rewritten to the pre-world: members and
their constructors are re-rooted, and a data constructor's erased arguments are
dropped.
-/
partial def Block.tr (b : Block) (e : Expr) : Expr :=
  match e with
  | .const n us => .const (b.preOf n) us
  | .app .. =>
    e.withApp fun f args =>
      let args := args.map b.tr
      match f with
      | .const n us =>
        match b.keptOf n with
        | some ks => mkAppN (.const (b.preOf n) us) (ks.filterMap fun i => args[i]?)
        | none    => mkAppN (.const (b.preOf n) us) args
      | _ => mkAppN (b.tr f) args
  | .lam n d v bi     => .lam n (b.tr d) (b.tr v) bi
  | .forallE n d v bi => .forallE n (b.tr d) (b.tr v) bi
  | .letE n t v x nd  => .letE n (b.tr t) (b.tr v) (b.tr x) nd
  | .mdata d x        => .mdata d (b.tr x)
  | .proj s i x       => .proj s i (b.tr x)
  | _ => e

/-- Whether `e` mentions any member of the block, or any of their constructors. -/
def Block.mentions (b : Block) (e : Expr) : Bool :=
  e.getUsedConstants.any fun c =>
    b.members.any fun m => c == m.name || m.name.isPrefixOf c

/-! ## Conjunctions

`X._wf` at a constructor is a right-associated conjunction, one conjunct per
recursive field followed by one per erased field, and `True` when there are
none.  These three functions are the only place that shape is fixed; the
constructors build it, the recursor takes it apart, and they have to agree. -/

/-- `cs[i] ∧ (cs[i+1] ∧ ..)`, and `True` when `i` is past the end. -/
partial def foldConj (cs : Array Expr) (i : Nat) : Expr :=
  if h : i < cs.size then
    if i + 1 == cs.size then cs[i] else mkApp2 (mkConst ``And) cs[i] (foldConj cs (i + 1))
  else
    mkConst ``True

/-- A proof of `cs[i]` from a proof `w` of `foldConj cs 0`. -/
def projConj (cs : Array Expr) (w : Expr) (i : Nat) : Expr := Id.run do
  let mut e := w
  for j in *...i do
    e := mkApp3 (mkConst ``And.right) cs[j]! (foldConj cs (j + 1)) e
  if i + 1 < cs.size then
    e := mkApp3 (mkConst ``And.left) cs[i]! (foldConj cs (i + 1)) e
  return e

/-- A proof of `foldConj cs 0` from proofs `ps` of each conjunct. -/
partial def introConj (cs ps : Array Expr) (i : Nat) : Expr :=
  if h : i < cs.size then
    if i + 1 == cs.size then ps[i]!
    else mkApp4 (mkConst ``And.intro) cs[i] (foldConj cs (i + 1)) ps[i]! (introConj cs ps (i + 1))
  else
    mkConst ``True.intro

/-! ## Rebuilding a telescope in the pre-world -/

/--
Walk a constructor's fields, rebuilding the telescope in the pre-world: erased
fields are dropped and everything else keeps its place with `Block.tr` applied
to its type and the earlier fields replaced by their pre-world counterparts.

`k` receives the original fields that survive, their pre-world counterparts (in
step), an image per *original* field (`none` for an erased one) and the
pre-world type of each erased field, in order.
-/
partial def withPreFieldsAux {α} [Inhabited α] (b : Block) (kinds : Array FieldKind)
    (xs : Array Expr) (i : Nat) (olds news : Array Expr) (imgs : Array (Option Expr))
    (erasedTys : Array Expr)
    (k : Array Expr → Array Expr → Array (Option Expr) → Array Expr → MetaM α) : MetaM α := do
  if h : i < xs.size then
    let x := xs[i]
    let ty := b.tr ((← inferType x).replaceFVars olds news)
    if kinds[i]! == .erased then
      withPreFieldsAux b kinds xs (i + 1) olds news (imgs.push none) (erasedTys.push ty) k
    else
      withLocalDeclD (← x.fvarId!.getUserName) ty fun y =>
        withPreFieldsAux b kinds xs (i + 1) (olds.push x) (news.push y)
          (imgs.push (some y)) erasedTys k
  else
    k olds news imgs erasedTys

@[inherit_doc withPreFieldsAux]
def withPreFields {α} [Inhabited α] (b : Block) (kinds : Array FieldKind) (xs : Array Expr)
    (k : Array Expr → Array Expr → Array (Option Expr) → Array Expr → MetaM α) : MetaM α :=
  withPreFieldsAux b kinds xs 0 #[] #[] #[] #[] k

/-! ## Elaborating the headers, with the members as scratch axioms

The members' arities have to be elaborated with the *other* members in scope,
which is exactly what `mutual` refuses to do.  So each member is declared as a
temporary `axiom` as soon as its own arity is known, inside
`withoutModifyingEnv`; the constructors are elaborated against those, and the
data constructors become axioms too so that `.snoc` in a `Prop` constructor's
type resolves the way the writer meant.  The environment is then rolled back and
the real declarations are made under the very same names, so the expressions we
extracted stay meaningful.

Elaborating the arities needs an order, and the writer is under no obligation to
supply one, so they are elaborated by a worklist: go round the members, keep
whichever succeed, and stop when a round adds nothing.  A genuine circularity --
`A`'s arity mentioning `B` and `B`'s mentioning `A` -- fails every round, and is
reported with the error of the last attempt. -/

private def stubAxiom (name : Name) (type : Expr) : TermElabM Unit :=
  addDecl (.axiomDecl { name, levelParams := [], type, isUnsafe := false })

private def elabArity (view : InductiveView) : TermElabM Expr := do
  match view.type? with
  | none => throwError "The type of `{view.declName}` must be given explicitly"
  | some typeStx =>
    withRef typeStx <| Term.withoutErrToSorry do
      let type ← Term.elabType typeStx
      Term.synthesizeSyntheticMVarsNoPostponing
      instantiateMVars type

private def elabCtorType (view : InductiveView) (ctor : CtorView) : TermElabM Expr :=
  withRef ctor.ref <| Term.withoutErrToSorry do
    Term.elabBinders ctor.binders.getArgs fun fields => do
      let ty ← match ctor.type? with
        | some typeStx => Term.elabType typeStx
        | none => pure (mkConst view.declName [])
      Term.synthesizeSyntheticMVarsNoPostponing
      instantiateMVars (← mkForallFVars fields ty)

/-- Reject up front everything the lowering below does not know how to do. -/
private def checkSupported (views : Array InductiveView) : TermElabM Unit := do
  for v in views do
    withRef v.ref do
      unless v.levelNames.isEmpty do
        throwError "Induction-inductive blocks with universe parameters are not supported"
      unless v.binders.getArgs.isEmpty do
        throwError "Induction-inductive blocks with parameters are not supported"
      if v.isClass then
        throwError "An induction-inductive block may not declare a class"
      if v.isCoinductive then
        throwError "An induction-inductive block may not be coinductive"
      unless v.derivingClasses.isEmpty do
        throwError "`deriving` is not supported for an induction-inductive block"
      unless v.computedFields.isEmpty do
        throwError "Computed fields are not supported for an induction-inductive block"

/--
Everything that has to be built while the scratch axioms are still in the
environment.

`Meta.forallTelescope` looks each binder's type up -- `withNewLocalInstances`
asks `isClass?` about it -- so a telescope over a constructor's type only works
where the members are declared.  That is true of the scratch environment and
false of the one the real declarations go into, up until the member being
telescoped over has itself been added.  So the pre-world types, which are
telescoped from the original ones, are all built here, against scratch axioms
for the pre-types as well; everything from `X` itself onwards is built during
emission, by which point the constants it telescopes over are real.
-/
structure Plan where
  block : Block
  /-- The data member's pre-type constructors. -/
  preDataCtors : Array Constructor
  /-- The `Prop` members, over the pre-type. -/
  prePropInds : Array InductiveType
  /-- `X._pre.rec (motive := fun _ => Prop) ..`, the body of `X._wf`. -/
  wfValue : Expr
  deriving Inhabited

/-- The block, elaborated and checked, ready for `emit`. -/
def prepare (views : Array InductiveView) : TermElabM Plan := do
  checkSupported views
  withoutModifyingEnv do
    let n := views.size
    -- the arities, by worklist
    let mut arities : Array (Option Expr) := (List.replicate n none).toArray
    let mut lastErr : Option Exception := none
    let mut progress := true
    while progress do
      progress := false
      for i in *...n do
        if arities[i]!.isSome then
          continue
        let s ← Term.saveState
        try
          let ty ← elabArity views[i]!
          unless ← isTypeFormerType ty do
            throwError "The resulting type of `{views[i]!.declName}` is not a sort"
          stubAxiom views[i]!.declName ty
          arities := arities.set! i (some ty)
          progress := true
        catch ex =>
          lastErr := some ex
          s.restore
    for i in *...n do
      if arities[i]!.isNone then
        match lastErr with
        | some ex => throw ex
        | none => throwError "Could not elaborate the arity of `{views[i]!.declName}`"
    -- which members are propositions
    let mut isProp : Array Bool := #[]
    for i in *...n do
      let p ← forallTelescopeReducing arities[i]!.get! fun _ r => do
        match ← whnfD r with
        | .sort u => return u.normalize == Level.zero
        | _ => throwError "The resulting type of `{views[i]!.declName}` is not a sort"
      isProp := isProp.push p
    let dataIdxs := (Array.range n).filter (!isProp[·]!)
    unless dataIdxs.size == 1 do
      throwError "This induction-inductive block has {dataIdxs.size} members that are not \
        propositions; exactly one is supported"
    let propIdxs := (Array.range n).filter (isProp[·]!)
    -- the constructors: the data member's first, so that its constructors are
    -- in scope for the `Prop` members' -- that is where `.snoc` has to resolve
    let mut ctorTypes : Array (Array Expr) := (List.replicate n (#[] : Array Expr)).toArray
    for i in dataIdxs do
      let tys ← views[i]!.ctors.mapM (elabCtorType views[i]! ·)
      ctorTypes := ctorTypes.set! i tys
      for j in *...tys.size do
        stubAxiom views[i]!.ctors[j]!.declName tys[j]!
    for i in propIdxs do
      ctorTypes := ctorTypes.set! i (← views[i]!.ctors.mapM (elabCtorType views[i]! ·))
    -- a skeleton is enough for `Block.mentions` and `Block.preOf`
    let skeleton : Block :=
      { dataIdx := dataIdxs[0]!
        members := (Array.range n).map fun i =>
          { name := views[i]!.declName, type := arities[i]!.get!, isProp := isProp[i]!
            ctors := (Array.range ctorTypes[i]!.size).map fun j =>
              { name := views[i]!.ctors[j]!.declName, type := ctorTypes[i]![j]!,
                kinds := #[] } } }
    let dName := skeleton.data.name
    let propNames := skeleton.props.map (·.name)
    -- classify the data constructors' fields
    let mut members := skeleton.members
    for i in dataIdxs do
      let mut cs := #[]
      for c in skeleton.members[i]!.ctors do
        cs := cs.push { c with kinds := ← classifyDataCtor skeleton dName propNames c }
      members := members.set! i { members[i]! with ctors := cs }
    for i in propIdxs do
      let mut cs := #[]
      for c in skeleton.members[i]!.ctors do
        cs := cs.push { c with kinds := ← classifyPropCtor skeleton dName c }
      members := members.set! i { members[i]! with ctors := cs }
    let b : Block := { skeleton with members }
    -- the pre-world, still against scratch axioms
    let dm := b.data
    let preD := preName dm.name
    let preDConst := mkConst preD []
    stubAxiom preD dm.type
    let mut preDataCtors : Array Constructor := #[]
    for c in dm.ctors do
      let type ← forallTelescope c.type fun xs _ =>
        withPreFields b c.kinds xs fun _ news _ _ => mkForallFVars news preDConst
      stubAxiom (b.preOf c.name) type
      preDataCtors := preDataCtors.push { name := b.preOf c.name, type }
    for m in b.props do
      stubAxiom (preName m.name) (b.tr m.type)
    let mut prePropInds : Array InductiveType := #[]
    for m in b.props do
      let mut cs : Array Constructor := #[]
      for c in m.ctors do
        let type ← forallTelescope c.type fun xs concl =>
          withPreFields b c.kinds xs fun olds news _ _ =>
            mkForallFVars news (b.tr (concl.replaceFVars olds news))
        cs := cs.push { name := b.preOf c.name, type }
      prePropInds := prePropInds.push
        { name := preName m.name, type := b.tr m.type, ctors := cs.toList }
    -- `X._wf`, one conjunct per recursive field and one per erased proof field
    let motive := Expr.lam `t preDConst (mkSort .zero) .default
    let mut wfMinors : Array Expr := #[]
    for c in dm.ctors do
      let minor ← forallTelescope c.type fun xs _ =>
        withPreFields b c.kinds xs fun _ news _ erasedTys => do
          let ihDecls := (recPositions c.kinds).map fun _ =>
            (`ih, fun _ => pure (mkSort Level.zero))
          withLocalDeclsD ihDecls fun ihs =>
            mkLambdaFVars (news ++ ihs) (foldConj (ihs ++ erasedTys) 0)
      wfMinors := wfMinors.push minor
    let wfValue := mkAppN (mkConst (preD ++ `rec) [Level.one]) (#[motive] ++ wfMinors)
    return { block := b, preDataCtors, prePropInds, wfValue }
where
  /-- Every field is `plain`, `recur` or `erased`, and no later field's type may
  mention an erased one. -/
  classifyDataCtor (b : Block) (dName : Name) (propNames : Array Name) (c : CtorSpec) :
      TermElabM (Array FieldKind) :=
    withRef .missing <| forallTelescope c.type fun xs concl => do
      unless concl == mkConst dName [] do
        throwError "The resulting type of `{c.name}` must be `{dName}` itself"
      let mut kinds := #[]
      for x in xs do
        let ty ← inferType x
        if ty == mkConst dName [] then
          kinds := kinds.push .recur
        else if (ty.getUsedConstants.any fun k => propNames.any (·.isPrefixOf k))
            && (← isProp ty) then
          kinds := kinds.push .erased
        else if b.mentions ty then
          throwError "The field `{← x.fvarId!.getUserName}` of `{c.name}` mentions the block, \
            but is neither `{dName}` nor a proof, so this lowering cannot erase \
            it:{indentExpr ty}"
        else
          kinds := kinds.push .plain
      -- an erased field must not be referred to by anything that survives
      for i in *...xs.size do
        if kinds[i]! == .erased then
          for j in *...xs.size do
            if j > i && kinds[j]! != .erased then
              if (← inferType xs[j]!).containsFVar xs[i]!.fvarId! then
                throwError "The field `{← xs[j]!.fvarId!.getUserName}` of `{c.name}` mentions \
                  the erased proof field `{← xs[i]!.fvarId!.getUserName}`"
      return kinds
  /-- A `Prop` constructor erases nothing; the check is that each field is
  either the data member itself or does not mention it as a type. -/
  classifyPropCtor (_b : Block) (dName : Name) (c : CtorSpec) : TermElabM (Array FieldKind) :=
    forallTelescope c.type fun xs _ => do
      let mut kinds := #[]
      for x in xs do
        let ty ← inferType x
        if ty == mkConst dName [] then
          kinds := kinds.push .recur
        else if ty.getUsedConstants.contains dName then
          throwError "The field `{← x.fvarId!.getUserName}` of `{c.name}` mentions `{dName}` \
            other than as its own type, which this lowering cannot rewrite:{indentExpr ty}"
        else
          kinds := kinds.push .plain
      return kinds

/-! ## Emitting the declarations -/

/--
Emit the whole encoding for a prepared block.

Everything here telescopes over types that mention the block's members, so the
order matters twice over: the pre-world declarations of steps 1--3 come out of
the `Plan` already built (they could only be built while the scratch axioms were
in scope), and from step 4 on each member is a real constant by the time a later
step looks through its type.
-/
def emit (p : Plan) : TermElabM Unit := do
  let b := p.block
  let docCtx := (← getLCtx, ← getLocalInstances)
  let dm := b.data
  let dName := dm.name
  let preD := preName dName
  let wfD := wfName dName
  let .sort du := dm.type
    | throwError "An indexed data member is not supported by this lowering"
  let dConst := mkConst dName []
  let preDConst := mkConst preD []
  let wfConst := mkConst wfD []
  let sVal  (e : Expr) : Expr := mkApp3 (mkConst ``Subtype.val [du]) preDConst wfConst e
  let sProp (e : Expr) : Expr := mkApp3 (mkConst ``Subtype.property [du]) preDConst wfConst e
  let sMk (v p : Expr) : Expr := mkApp4 (mkConst ``Subtype.mk [du]) preDConst wfConst v p
  /- The pre-world value of an original field: a recursive one loses its
  well-formedness proof, everything else passes through. -/
  let valify (kinds : Array FieldKind) (xs : Array Expr) : Array Expr := Id.run do
    let mut out := #[]
    for i in *...xs.size do
      out := out.push (if kinds[i]! == .recur then sVal xs[i]! else xs[i]!)
    return out

  -- 1. the data member's pre-type
  addInd [] 0 #[{ name := preD, type := dm.type, ctors := p.preDataCtors.toList }]

  -- 2. the `Prop` members, over the pre-type
  unless p.prePropInds.isEmpty do
    addInd [] 0 p.prePropInds

  -- 3. `X._wf`, by recursion on the pre-type
  let wfType := Expr.forallE `t preDConst (mkSort Level.zero) .default
  addDef wfD [] wfType p.wfValue (compile := false)

  -- 4. the data member itself
  addDef dName [] dm.type (mkApp2 (mkConst ``Subtype [du]) preDConst wfConst) (compile := false)

  -- 5. the `Prop` members, at the subtype
  for m in b.props do
    let value ← forallTelescope m.type fun idxs _ => do
      let args ← idxs.mapM fun y => do
        return if (← inferType y) == dConst then sVal y else y
      mkLambdaFVars idxs (mkAppN (mkConst (preName m.name) []) args)
    addDef m.name [] m.type value (compile := false)

  -- 6. the data constructors
  for c in dm.ctors do
    let value ← forallTelescope c.type fun xs _ => do
      let imgs := valify c.kinds xs
      let kept := (keptPositions c.kinds).map (imgs[·]!)
      let mut conjs : Array Expr := #[]
      let mut proofs : Array Expr := #[]
      for i in recPositions c.kinds do
        conjs := conjs.push (mkApp wfConst imgs[i]!)
        proofs := proofs.push (sProp xs[i]!)
      for i in *...xs.size do
        if c.kinds[i]! == .erased then
          conjs := conjs.push (b.tr ((← inferType xs[i]!).replaceFVars xs imgs))
          proofs := proofs.push xs[i]!
      mkLambdaFVars xs
        (sMk (mkAppN (mkConst (b.preOf c.name) []) kept) (introConj conjs proofs 0))
    addDef c.name [] c.type value

  -- 7. the `Prop` constructors
  for m in b.props do
    for c in m.ctors do
      let value ← forallTelescope c.type fun xs _ =>
        mkLambdaFVars xs (mkAppN (mkConst (b.preOf c.name) []) (valify c.kinds xs))
      addDecl (.thmDecl { name := c.name, levelParams := [], type := c.type, value })

  -- 8. the recursor
  let lp := `u
  let lvl := Level.param lp
  let recAuxName := dName ++ `recAux
  let recName := dName ++ `recursor
  let (recAuxType, recAuxValue, recType, recValue) ←
    withLocalDecl `C .implicit (.forallE `t dConst (mkSort lvl) .default) fun C => do
      let minorDecls : Array (Name × (Array Expr → TermElabM Expr)) := dm.ctors.map fun c =>
        (Name.mkSimple c.name.getString!, fun _ =>
          forallTelescope c.type fun xs _ => do
            let ihDecls := (recPositions c.kinds).map fun i => (`ih, fun _ => pure (mkApp C xs[i]!))
            withLocalDeclsD ihDecls fun ihs =>
              mkForallFVars (xs ++ ihs) (mkApp C (mkAppN (mkConst c.name []) xs)))
      withLocalDeclsD minorDecls fun minors => do
        withLocalDeclD `t preDConst fun t0 => withLocalDeclD `w (mkApp wfConst t0) fun w => do
          let recAuxType ← mkForallFVars (#[C] ++ minors ++ #[t0, w]) (mkApp C (sMk t0 w))
          -- the motive of the `casesOn`: the well-formedness proof stays under it
          let inner ← mkForallFVars #[w] (mkApp C (sMk t0 w))
          let elim ← getLevel inner
          let motive ← mkLambdaFVars #[t0] inner
          let mut alts : Array Expr := #[]
          for ci in *...dm.ctors.size do
            let c := dm.ctors[ci]!
            let alt ← forallTelescope c.type fun xs _ =>
              withPreFields b c.kinds xs fun _ news imgs erasedTys => do
                let head := mkAppN (mkConst (b.preOf c.name) []) news
                withLocalDeclD `w (mkApp wfConst head) fun wc => do
                  let recPos := recPositions c.kinds
                  let mut conjs : Array Expr := #[]
                  for i in recPos do
                    conjs := conjs.push (mkApp wfConst (imgs[i]!).get!)
                  conjs := conjs ++ erasedTys
                  -- the original fields, rebuilt at the subtype
                  let mut real : Array Expr := #[]
                  let mut nrec := 0
                  let mut nera := 0
                  for i in *...xs.size do
                    match c.kinds[i]! with
                    | .recur =>
                      real := real.push (sMk (imgs[i]!).get! (projConj conjs wc nrec))
                      nrec := nrec + 1
                    | .plain => real := real.push (imgs[i]!).get!
                    | .erased =>
                      real := real.push (projConj conjs wc (recPos.size + nera))
                      nera := nera + 1
                  let mut ihs : Array Expr := #[]
                  for k in *...recPos.size do
                    let i := recPos[k]!
                    ihs := ihs.push <| mkAppN (mkConst recAuxName [lvl])
                      (#[C] ++ minors ++ #[(imgs[i]!).get!, projConj conjs wc k])
                  mkLambdaFVars (news ++ #[wc]) (mkAppN minors[ci]! (real ++ ihs))
            alts := alts.push alt
          let body := mkApp (mkAppN (mkConst (preD ++ `casesOn) [elim])
            (#[motive, t0] ++ alts)) w
          let recAuxValue ← mkLambdaFVars (#[C] ++ minors ++ #[t0, w]) body
          let (recType, recValue) ← withLocalDeclD `t dConst fun t => do
            let ty ← mkForallFVars (#[C] ++ minors ++ #[t]) (mkApp C t)
            let val ← mkLambdaFVars (#[C] ++ minors ++ #[t])
              (mkAppN (mkConst recAuxName [lvl]) (#[C] ++ minors ++ #[sVal t, sProp t]))
            return (ty, val)
          return (recAuxType, recAuxValue, recType, recValue)
  let preDef : PreDefinition :=
    { ref := .missing, kind := .def, levelParams := [lp], modifiers := {},
      declName := recAuxName, binders := .missing, type := recAuxType, value := recAuxValue,
      termination := TerminationHints.none }
  Structural.structuralRecursion docCtx #[preDef] #[none]
  addDef recName [lp] recType recValue

/-! ## The entry point -/

/--
Whether some member's arity mentions a sibling -- the syntactic signature of
induction-induction, and the reason the block does not elaborate.  Used only
after header elaboration has already failed, so a block that happens to mention
a *global* of the same name is not affected: that one elaborates.
-/
def viewsAreInductionInductive (views : Array InductiveView) : Bool := Id.run do
  let names := views.map (·.shortDeclName)
  let mentions (stx : Syntax) : Bool :=
    (stx.find? fun s => s.isIdent && names.contains s.getId.eraseMacroScopes).isSome
  for v in views do
    if let some t := v.type? then
      if mentions t then return true
    if mentions v.binders then return true
  return false

/-- Elaborate an induction-inductive block by erasing its proof fields. -/
def elabInductionInductive (elems : Array Syntax) : CommandElabM Unit := do
  let inductives ← elems.mapM fun stx => do
    let modifiers ← elabModifiers ⟨stx[0]⟩
    pure (modifiers, stx[1])
  let elabs ← runTermElabM fun _ => inductives.mapM fun (m, s) => mkInductiveView m s
  let views := elabs.map (·.view)
  runTermElabM fun vars => do
    unless vars.isEmpty do
      throwError "Section variables are not supported for an induction-inductive block"
    emit (← prepare views)

end Mumi.IndInd
