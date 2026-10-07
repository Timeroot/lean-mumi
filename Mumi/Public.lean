/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Mumi.Lowering
public import Mumi.View
import all Lean.Meta.Injective

public section

/-!
# The declarations an aliased member answers to

A data member whose `X.rec` is owed to a recursion over more than its own kernel
block is declared as `X._ind`, and the writer's `X` and `X.c` are reducible
definitions unfolding to it (`addAliasedInds`).  Lean builds everything an
inductive comes with for `X._ind`; this module restates each piece under the
name an inductive `X` would have given it, with `X._ind` and its constructors
read back as `X` and `X.c` wherever they appear.  Every restatement is the
original constant at a type it already has up to unfolding, so nothing here is
proved twice:

* `X.casesOn`, `X.noConfusionType`, `X.noConfusion`, `X.ctorIdx`, `X.below`
  and `X.brecOn`;
* `X.c.inj`, `X.c.injEq` and `X.c.sizeOf_spec`, the last two `@[simp]` as Lean
  makes them.

`X.recOn` is not among them: it is the block's `X.rec` with the major premise
first, as `Lean.mkRecOn` builds it, and the kernel's would be over `X._ind`'s
block alone.  A `Prop` member of such a block has no inductive of its own under
its name either, so its `casesOn` is cut out of the block's recursor.

A `casesOn` names its motive the way the block's recursor names the member's,
as Lean's does for a `mutual` block.
-/

namespace Mumi

open Lean Meta Lean.Elab Lean.Elab.MultiuniverseInductive

/-- The writer's name for a constant of an aliased inductive: `X` for `X._ind`,
and `X.c` for `X._ind.c` -- each only where the writer's name exists. -/
def publicName? (env : Environment) (n : Name) : Option Name :=
  match n with
  | .str p@(.str q "_ind") c =>
    let pub := Name.str q c
    if env.contains pub && env.contains p then some pub else none
  | .str q "_ind" => if env.contains q then some q else none
  | _ => none

/-- `e` with every constant of an aliased inductive read back under the writer's name. -/
def publicize (e : Expr) : MetaM Expr := do
  let env ← getEnv
  return e.replace fun
    | .const n us => (publicName? env n).map (.const · us)
    | _ => none

/-- Rename the `∀`-binder at position `i` of `e`. -/
private partial def renameBinder (i : Nat) (nm : Name) : Expr → Expr
  | .forallE n d b bi =>
    if i == 0 then .forallE nm d b bi else .forallE n d (renameBinder (i - 1) nm b) bi
  | e => e

/--
Restate `src` as `dst`, at its own type read back under the writer's names.
`motiveAt` renames one binder, which is how a one-motive eliminator takes the
name the block's recursor gives the member's motive. -/
def restate (src dst : Name) (motiveAt : Option (Nat × Name) := none) (simp := false)
    (reducible := true) : MetaM Unit := do
  let env ← getEnv
  if env.contains dst then return
  let some info := env.find? src | return
  let lps := info.levelParams
  let mut type ← publicize info.type
  if let some (i, nm) := motiveAt then type := renameBinder i nm type
  let value := mkConst src (lps.map Level.param)
  if info.isTheorem || (← isProp type) then
    addDecl (.thmDecl { name := dst, levelParams := lps, type, value })
  else
    addDef dst lps type value (hints := .abbrev) (compile := false)
    if reducible then setReducibleAttribute dst
    -- compiled where the original is, so that a use of the restatement runs
    unless isNoncomputable env src do
      try compileDecl (.defnDecl (← getConstInfoDefn dst)) (logErrors := false) catch _ => pure ()
  modifyEnv fun env => addProtected env dst
  if simp then
    let simpAttr ← ofExcept <| getAttributeImpl (← getEnv) `simp
    simpAttr.add dst default .global

/--
Everything Lean built for `X._ind`, under the names it would have built it under
for an inductive `X`, for each aliased data member of a block with `numParams`
parameters; and for each `Prop` member, the one-motive `casesOn` the block's
recursor cuts down to. -/
def publishAliased (numParams : Nat) (members : Array Name) : TermElabM Unit := do
  for mem in members do
    let ind := aliasIndName mem
    let env ← getEnv
    unless env.contains mem do continue
    match env.find? ind with
    | some (.inductInfo ii) =>
      let motive? ← motiveNameOf? numParams mem
      discard <| attempt? `Mumi m!"no `casesOn` for `{mem}`" <|
        restate (ind ++ `casesOn) (mem ++ `casesOn) (motive?.map (numParams, ·))
      for s in [`noConfusionType, `noConfusion, `ctorIdx, `below, `brecOn] do
        discard <| attempt? `Mumi m!"no `{s}` for `{mem}`" <| restate (ind ++ s) (mem ++ s)
      for c in ii.ctors do
        let pub := Name.str mem c.getString!
        discard <| attempt? `Mumi m!"no injectivity for `{pub}`" do
          restate (c ++ `inj) (pub ++ `inj)
          restate (c ++ `injEq) (pub ++ `injEq) (simp := true)
        discard <| attempt? `Mumi m!"no `sizeOf` lemma for `{pub}`" <|
          restate (c ++ `sizeOf_spec) (pub ++ `sizeOf_spec) (simp := true)
    | _ =>
      -- a `Prop` member, whose name is its shadow's: its case split is the
      -- block's recursion with every hypothesis and every other motive dropped
      unless ← forallTelescope (← getConstInfo mem).type fun _ s => pure s.isProp do
        continue
      unless env.contains (mem ++ `rec) do continue
      -- the recursor's own universe is the first, as Lean orders them
      let elim := (← getConstInfo (mem ++ `rec)).levelParams.take 1
      discard <| attempt? `Mumi m!"no `casesOn` for `{mem}`" do
        addSoloElim numParams elim.toArray true (mem ++ `rec) (mem ++ `casesP)
          (forCases := true) (evenIfWeaker := true)
        addMajorFirst numParams mem (mem ++ `casesP) (mem ++ `casesOn)
    discard <| attempt? `Mumi m!"no `recOn` for `{mem}`" <|
      addMajorFirst numParams mem (mem ++ `rec) (mem ++ `recOn)

/-! ## Injectivity of a constructor that is a definition

A member that is a definition over an encoding has constructors that are
definitions too, and `injection` does not see through one.  What every such
member does have is a `casesOn` that computes, so the fields of a constructor
can be read back out of its value: a case split sending the constructor to its
fields, gathered in a tuple, and every other constructor to nothing.  Equal
values give equal tuples, and a tuple's components are taken apart one at a time,
each equation substituted before the next is read, as `injection` would.  The
statements are Lean's own (`mkInjectiveTheoremTypeCore?`).
-/

/-- The binders of `ty` up to its conclusion as one nested `PSigma`, ending at `PUnit`. -/
private partial def tupleType (ty : Expr) : MetaM Expr := do
  match ty with
  | .forallE n d b bi =>
    withLocalDecl n bi d fun x => do
      mkAppOptM ``PSigma #[d, ← mkLambdaFVars #[x] (← tupleType (b.instantiate1 x))]
  | .mdata _ e => tupleType e
  | _ => return mkConst ``PUnit [Level.one]

/-- `args`, for the binders of `ty`, as an element of `tupleType ty`. -/
private partial def tupleOf (ty : Expr) (args : List Expr) : MetaM Expr := do
  match ty, args with
  | .forallE n d b bi, a :: as =>
    let beta ← withLocalDecl n bi d fun x => do mkLambdaFVars #[x] (← tupleType (b.instantiate1 x))
    mkAppOptM ``PSigma.mk #[d, beta, a, ← tupleOf (b.instantiate1 a) as]
  | .mdata _ e, as => tupleOf e as
  | _, _ => return mkConst ``PUnit.unit [Level.one]

/-- The conjuncts of a right-nested `And`. -/
private partial def conjunctsOf (e : Expr) : Array Expr :=
  if e.isAppOfArity ``And 2 then #[e.appFn!.appArg!] ++ conjunctsOf e.appArg! else #[e]

/--
`c.inj` and `c.injEq` for a constructor `ctor` of `mem` that is a definition,
read back through `mem.casesOn`, whose minor premises are for `ctors` in order. -/
def addInjViaCases (numParams : Nat) (mem ctor : Name) (ctors : Array Name) : TermElabM Unit := do
  let injName := mkInjectiveTheoremNameFor ctor
  let eqName := mkInjectiveEqTheoremNameFor ctor
  if (← getEnv).contains injName then return
  let info ← getConstInfo ctor
  let arity ← forallTelescope info.type fun xs _ => pure xs.size
  let cv : ConstructorVal :=
    { name := ctor, levelParams := info.levelParams, type := info.type, induct := mem,
      cidx := 0, numParams, numFields := arity - numParams, isUnsafe := false }
  let some injTy ← mkInjectiveTheoremTypeCore? cv false | return
  let some eqTy ← mkInjectiveTheoremTypeCore? cv true | return
  let us := info.levelParams.map Level.param
  let ident (s : String) (k : Nat) := mkIdent (Name.mkSimple s!"{s}{k}")
  let injVal ← forallTelescope injTy fun xs conj => do
    let h := xs.back!
    let some (_, lhs, rhs) := (← inferType h).eq? | throwError "`{injName}` states no equation"
    let ps := lhs.getAppArgs.extract 0 numParams
    let fieldsTy ← instantiateForall (info.instantiateTypeLevelParams us) ps
    let tupleTy ← tupleType fieldsTy
    let resTy := mkApp2 (mkConst ``PSum [Level.one, ← getLevel tupleTy])
      (mkConst ``PUnit [Level.one]) tupleTy
    let resLvl ← getLevel resTy
    -- the case split into the tuple, at an element of the constructor's type
    let selTy ← inferType lhs
    let sel ← withLocalDeclD `t selTy fun t => do
      let ci ← getConstInfo (mem ++ `casesOn)
      let mut e := mkAppN (mkConst (mem ++ `casesOn) (resLvl :: us)) ps
      let mut ty ← instantiateForall (ci.instantiateTypeLevelParams (resLvl :: us)) ps
      -- the motive, the indices and the major, as the type of `t` gives them
      let .forallE _ motTy _ _ := ty | throwError "`{mem}.casesOn` takes no motive"
      let motive ← forallTelescope motTy fun ys _ => mkLambdaFVars ys resTy
      e := mkApp e motive
      ty ← instantiateForall ty #[motive]
      let idxs := selTy.getAppArgs.extract numParams selTy.getAppNumArgs
      for a in idxs.push t do
        e := mkApp e a
        ty ← instantiateForall ty #[a]
      for c in ctors do
        let .forallE _ d _ _ := ty
          | throwError "`{mem}.casesOn` takes fewer minor premises than `{mem}` has constructors"
        let minor ← forallTelescope d fun fs _ => do
          let v ← if c == ctor then
              mkAppOptM ``PSum.inr #[mkConst ``PUnit [Level.one], tupleTy, ← tupleOf fieldsTy fs.toList]
            else
              mkAppOptM ``PSum.inl #[mkConst ``PUnit [Level.one], tupleTy, mkConst ``PUnit.unit [Level.one]]
          mkLambdaFVars fs v
        e := mkApp e minor
        ty ← instantiateForall ty #[minor]
      mkLambdaFVars #[t] e
    -- one field at a time: its equation, substituted where it can be, then the
    -- rest of the tuple, at one type once it has been
    let n := arity - numParams
    let mut steps : Array (TSyntax `tactic) := #[← `(tactic| intro $(ident "mumiT" 0):ident)]
    for k in *...n do
      let t := ident "mumiT" k
      let p := ident "mumiP" k
      let e := ident "mumiE" k
      let r := ident "mumiR" k
      steps := steps ++ #[
        ← `(tactic| have $p:ident := PSigma.mk.inj $t:ident),
        ← `(tactic| have $e:ident := $p:ident.1),
        ← `(tactic| have $r:ident := $p:ident.2),
        ← `(tactic| first | subst $e | skip),
        ← `(tactic| have $(ident "mumiT" (k + 1)):ident := eq_of_heq $r:ident)]
    let terms ← (conjunctsOf conj).mapM fun c =>
      if c.isAppOf ``HEq then `(term| HEq.rfl) else `(term| rfl)
    steps := steps.push <| ← match terms with
      | #[t] => `(tactic| exact $t)
      | _ => `(tactic| exact ⟨$terms,*⟩)
    -- the two tuples, stated over the fields themselves: read off the case
    -- split instead, a field of a structure type would come back eta-expanded
    -- and no longer be a variable to substitute
    let as := lhs.getAppArgs.extract numParams lhs.getAppNumArgs
    let bs := rhs.getAppArgs.extract numParams rhs.getAppNumArgs
    let tA ← tupleOf fieldsTy as.toList
    let tB ← tupleOf (← instantiateForall (info.instantiateTypeLevelParams us) ps) bs.toList
    -- the step from the values to the tuples is the case split computing, which
    -- is left to the kernel: Meta's unifier can wander off into an encoding the
    -- kernel decides at once
    let selEq := mkApp6 (mkConst ``congrArg [← getLevel selTy, resLvl]) selTy resTy lhs rhs sel h
    let tuples := mkApp5 (mkConst ``PSum.inr.inj [Level.one, ← getLevel tupleTy])
      (mkConst ``PUnit [Level.one]) tupleTy tA tB selEq
    let goal ← mkArrow (← mkEq tA tB) conj
    let prf ← proveBy goal (← `(Lean.Parser.Tactic.tacticSeq| $[$steps]*))
    mkLambdaFVars xs (mkApp prf tuples)
  addDecl (.thmDecl { name := injName, levelParams := info.levelParams,
                      type := ← instantiateMVars injTy, value := ← instantiateMVars injVal })
  let eqVal ← forallTelescope eqTy fun xs goal => do
    let comps := conjunctsOf goal.appArg!
    let hC := mkIdent `mumiC
    let mut bwd : Array (TSyntax `tactic) := #[← `(tactic| intro $hC:ident)]
    for k in *...comps.size do
      let mut t : Term := hC
      for _ in *...k do t ← `($t.2)
      if k + 1 != comps.size then t ← `($t.1)
      bwd := bwd.push (← `(tactic| have $(ident "mumiQ" k):ident := $t))
    for k in *...comps.size do
      bwd := bwd.push <| ← `(tactic| first | subst $(ident "mumiQ" k) | cases $(ident "mumiQ" k):term)
    bwd := bwd.push (← `(tactic| rfl))
    let back ← proveBy (← mkArrow goal.appArg! goal.appFn!.appArg!)
      (← `(Lean.Parser.Tactic.tacticSeq| $[$bwd]*))
    mkLambdaFVars xs (← mkAppM ``Eq.propIntro #[mkAppN (mkConst injName us) xs, back])
  addDecl (.thmDecl { name := eqName, levelParams := info.levelParams,
                      type := ← instantiateMVars eqTy, value := ← instantiateMVars eqVal })
  let simpAttr ← ofExcept <| getAttributeImpl (← getEnv) `simp
  simpAttr.add eqName default .global

/-! ## Rules that hold up to a round trip

A field of a constructor that a nested copy stands for is stored as the copy and
read back through `toOrig (ofOrig x)`, which is `x` by induction rather than by
computation.  So `R.casesOn (R.mk xs) mk = mk xs`, and the recursors' rules at
such a constructor, are stated as `@[simp]` lemmas under the names `rfl` would
have proved them under.  Each is proved by taking the two sides apart: a cast is
dropped, two applications of one function are compared argument by argument, a
round trip is closed by the copy's `toOrig_ofOrig`, and what does not yet look
alike is unfolded one step.
-/

/-- Two dependent functions on one domain that agree up to `HEq` everywhere. -/
theorem hfunext_of_heq {α : Sort u} {β β' : α → Sort v} {f : (a : α) → β a}
    {g : (a : α) → β' a} (h : ∀ a, HEq (f a) (g a)) : HEq f g := by
  have hβ : β = β' := funext fun a => type_eq_of_heq (h a)
  subst hβ
  exact heq_of_eq (funext fun a => eq_of_heq (h a))

/-- One step of unfolding at the head, at the default transparency. -/
private def unfoldStep (e : Expr) : MetaM (Option Expr) := do
  let e' ← whnfCore e
  if e' != e then return some e'
  unfoldDefinition? e

/-- What the cast `a` casts, and a proof that `a` and it are `HEq`. -/
private partial def castOf? (a : Expr) (fuel : Nat := 4) : MetaM (Option (Expr × Expr)) := do
  let a ← whnfCore a
  let args := a.getAppArgs
  match a.getAppFn with
  | .const ``Eq.rec us =>
    unless args.size == 6 do return none
    let (α, x, m, e, y, h) := (args[0]!, args[1]!, args[2]!, args[3]!, args[4]!, args[5]!)
    -- `HEq (h ▸ e) e`, by the cast's own recursion: at `rfl` the two are one
    let prf ← withLocalDeclD `y α fun yv => do
      withLocalDeclD `h (← mkEq x yv) fun hv => do
        let motive ← mkLambdaFVars #[yv, hv]
          (← mkHEq (mkAppN (.const ``Eq.rec us) #[α, x, m, e, yv, hv]) e)
        return mkAppN (.const ``Eq.rec [.zero, us[1]!]) #[α, x, motive, ← mkHEqRefl e, y, h]
    return some (e, prf)
  | .const n _ =>
    -- the other spellings of a cast are definitions that end at `Eq.rec`
    unless fuel > 0 && [``Eq.ndrec, ``Eq.mpr, ``Eq.mp, ``cast, ``Eq.recOn, ``Eq.ndrecOn,
        ``Eq.casesOn, ``Eq.subst].contains n do return none
    let some a' ← unfoldDefinition? a | return none
    castOf? a' (fuel - 1)
  | _ => return none

/--
`HEq a b`, for two terms equal up to casts and round trips through the copies
whose `toOrig_ofOrig` lemmas are `trips`. -/
partial def heqUpToTrips (trips : Array Name) (used : IO.Ref Bool) (a b : Expr)
    (fuel : Nat := 40) : MetaM Expr := do
  let heqUpToTrips := fun a b fuel => heqUpToTrips trips used a b fuel
  if fuel == 0 then
    throwError "the two sides do not meet:{indentExpr a}\nand{indentExpr b}"
  let fuel := fuel - 1
  -- the cheap comparison first: a full one that fails unfolds a long way
  if a == b then return ← mkHEqRefl a
  if ← withReducible (isDefEq (← inferType a) (← inferType b) <&&> isDefEq a b) then
    return ← mkHEqRefl a
  -- a cast on either side is dropped
  if let some (e, h) ← castOf? a then
    return ← mkHEqTrans h (← heqUpToTrips e b fuel)
  if let some (e, h) ← castOf? b then
    return ← mkHEqTrans (← heqUpToTrips a e fuel) (← mkHEqSymm h)
  -- a round trip on either side is closed
  let trip? (x : Expr) : MetaM (Option (Expr × Expr)) := do
    -- only a copy's `toOrig` can be a round trip
    let .const hd _ := (← whnfR x).getAppFn | return none
    unless hd.isStr && hd.getString! == "toOrig" && trips.contains (hd.getPrefix ++ `toOrig_ofOrig) do
      return none
    for t in trips do
      let tc ← mkConstWithFreshMVarLevels t
      let (ms, _, ty) ← forallMetaTelescope (← inferType tc)
      let some (_, l, r) := ty.eq? | continue
      if ← isDefEq l x then
        return some (← instantiateMVars r, ← mkHEqOfEq (← instantiateMVars (mkAppN tc ms)))
    return none
  if let some (r, h) ← trip? a then
    used.set true
    return ← mkHEqTrans h (← heqUpToTrips r b fuel)
  if let some (r, h) ← trip? b then
    used.set true
    return ← mkHEqTrans (← heqUpToTrips a r fuel) (← mkHEqSymm h)
  -- two proofs: of propositions equal by the same means, and then the same
  let tyA ← inferType a
  if ← isProp tyA then
    let tyB ← inferType b
    let tyEq ← mkEqOfHEq (← heqUpToTrips tyA tyB fuel)
    let motive ← withLocalDeclD `q (mkSort .zero) fun q => do
      withLocalDeclD `e (← mkEq tyA q) fun eq =>
        withLocalDeclD `h q fun h => do
          mkLambdaFVars #[q, eq] (← mkForallFVars #[h] (← mkHEq a h))
    let base ← withLocalDeclD `h tyA fun h => do mkLambdaFVars #[h] (← mkHEqRefl a)
    return mkApp (mkApp6 (mkConst ``Eq.rec [.zero, .succ .zero]) (mkSort .zero) tyA motive base
      tyB tyEq) b
  -- two functions of one type: equal at every argument, then by `funext`
  let tyA' ← whnf tyA
  if tyA'.isForall then
    let tyB' ← whnf (← inferType b)
    if (← isDefEq tyA tyB') then
      let attempt ← observing? do
        withLocalDecl tyA'.bindingName! tyA'.bindingInfo! tyA'.bindingDomain! fun x => do
          let h ← heqUpToTrips (mkApp a x).headBeta (mkApp b x).headBeta fuel
          let e ← mkEqOfHEq h
          mkHEqOfEq (← mkFunExt (← mkLambdaFVars #[x] e))
      if let some prf := attempt then return prf
    -- or of one domain, the values' types differing as the arguments' round trips do
    let tyB' ← whnf (← inferType b)
    if tyB'.isForall && (← isDefEq tyA'.bindingDomain! tyB'.bindingDomain!) then
      let attempt ← observing? do
        withLocalDecl tyA'.bindingName! tyA'.bindingInfo! tyA'.bindingDomain! fun x => do
          let h ← heqUpToTrips (mkApp a x).headBeta (mkApp b x).headBeta fuel
          mkAppM ``hfunext_of_heq #[← mkLambdaFVars #[x] h]
      if let some prf := attempt then return prf
  -- one function at two lots of arguments, compared argument by argument
  let fa := a.getAppFn
  let n := a.getAppNumArgs
  if n > 0 && n == b.getAppNumArgs && (← isDefEq fa b.getAppFn) then
    let attempt ← observing? do
      let ct ← mkHCongrWithArity fa n
      let mut prf := ct.proof
      let mut cty := ct.type
      for i in *...n do
        let x := a.getArg! i
        let y := b.getArg! i
        let rest := (cty.bindingBody!.instantiate1 x).bindingBody!.instantiate1 y
        let h ← heqUpToTrips x y fuel
        let h ← if rest.bindingDomain!.isAppOf ``Eq then mkEqOfHEq h else pure h
        prf := mkApp3 prf x y h
        cty := rest.bindingBody!.instantiate1 h
      return prf
    if let some prf := attempt then return prf
  -- a side that still mentions a copy is a round trip still to be found, and is
  -- unfolded towards it; two that do not are compared in full, which is what a
  -- failing comparison would cost anyway
  let copies := trips.map (·.getPrefix)
  let mentions (e : Expr) : Bool := (e.find? fun
    | .const n _ => copies.contains n.getPrefix || copies.contains n
    | _ => false).isSome
  let full : MetaM Bool := do
    return (← isDefEq (← inferType a) (← inferType b)) && (← isDefEq a b)
  if !(mentions a || mentions b) && (← full) then return ← mkHEqRefl a
  if let some a' ← unfoldStep a then return ← heqUpToTrips a' b fuel
  if let some b' ← unfoldStep b then return ← heqUpToTrips a b' fuel
  if ← full then return ← mkHEqRefl a
  throwError "the two sides do not meet:{indentExpr a}\nand{indentExpr b}"

/-- `base`'s rule at the minor premise `c`: `X.rec_c`, `X.rec_1_c`, `X.casesOn_c`. -/
private def ruleNameOf (base c : Name) : Name :=
  base.getPrefix ++ Name.mkSimple (base.getString! ++ "_" ++ c.eraseMacroScopes.getString!)

/-- Add `name : ∀ xs, lhs = rhs`, proved up to round trips, as a `@[simp]` lemma. -/
private def addTripRule (trips : Array Name) (lps : List Name) (name : Name)
    (xs : Array Expr) (lhs rhs : Expr) : MetaM Unit := do
  if (← getEnv).contains name then return
  -- a rule whose proof crosses no round trip is one `rfl` proves already
  let used ← IO.mkRef false
  let a ← whnfCore lhs
  let prf ← mkEqOfHEq (← heqUpToTrips trips used a rhs)
  unless ← used.get do return
  let type ← mkForallFVars xs (← mkEq lhs rhs)
  let value ← instantiateMVars (← mkLambdaFVars xs (← mkExpectedTypeHint prf (← mkEq lhs rhs)))
  addDecl (.thmDecl { name, levelParams := lps, type, value })
  let simpAttr ← ofExcept <| getAttributeImpl (← getEnv) `simp
  simpAttr.add name default .global

/--
The rules of the recursors `recs` and of the case splits `cases` that `rfl`
does not prove, as `@[simp]` lemmas, for a block with `numParams` parameters
whose copies' round trips are `trips`.  A recursor's rule at a constructor is its
minor premise at the fields and at the recursion's value at each field that
takes a hypothesis; a case split's is its minor premise at the fields. -/
def addTripRules (numParams : Nat) (trips : Array Name) (recs cases : Array Name) :
    TermElabM Unit := do
  for r in recs do
    let ci ← getConstInfo r
    let us := ci.levelParams.map Level.param
    discard <| MultiuniverseInductive.attempt? `Mumi m!"no rules for `{r}`" do
    forallTelescope ci.type fun xs concl => do
      let ps := xs.extract 0 numParams
      -- the motives lead, then the minors, then the indices and the major
      let mut nMot := 0
      for x in xs.extract numParams xs.size do
        unless ← forallTelescope (← inferType x) fun _ c => pure c.isSort do break
        nMot := nMot + 1
      let motives := xs.extract numParams (numParams + nMot)
      let isMinor (x : Expr) : MetaM Bool := do
        forallTelescope (← inferType x) fun _ c => pure (motives.contains c.getAppFn)
      let mut nMin := 0
      for x in xs.extract (numParams + nMot) xs.size do
        unless ← isMinor x do break
        nMin := nMin + 1
      let minors := xs.extract (numParams + nMot) (numParams + nMot + nMin)
      let front := ps ++ motives ++ minors
      let self := concl.getAppFn
      -- a proposition's rules are between proofs, and say nothing
      if ← forallTelescope (← inferType self) fun _ c => pure c.isProp then return
      -- which recursor concludes at which motive
      let recAt ← motives.mapM fun m => recs.findM? fun r' => do
        forallTelescope (← getConstInfo r').type fun ys c => do
          let k? := (ys.extract numParams ys.size).idxOf? c.getAppFn
          return k? == motives.idxOf? m
      -- `r'` at whatever makes its conclusion `goal`
      let callAt (r' : Name) (goal : Expr) : MetaM Expr := do
        let f := mkAppN (mkConst r' us) front
        let (ms, _, c) ← forallMetaTelescope (← inferType f)
        unless ← isDefEq c goal do throwError "`{r'}` does not conclude at{indentExpr goal}"
        instantiateMVars (mkAppN f ms)
      for m in minors do
        unless (← forallTelescope (← inferType m) fun _ c => pure c.getAppFn) == self do continue
        let name := ruleNameOf r (← m.fvarId!.getUserName)
        forallTelescope (← inferType m) fun zs c => do
          -- the fields, then a hypothesis at each that takes one
          let mut fields := #[]
          let mut ihs := #[]
          let mut ihVals := #[]
          for z in zs do
            -- a displayed motive names the hypotheses before it, which are the
            -- recursion's values
            let zty := (← inferType z).replaceFVars ihs ihVals
            let hyp ← forallTelescope zty fun ws hc => do
              let some k := motives.idxOf? hc.getAppFn | return none
              let some (some r') := recAt[k]? | throwError "no recursor at motive {k}"
              return some (← mkLambdaFVars ws (← callAt r' hc))
            match hyp with
            | some v => ihs := ihs.push z; ihVals := ihVals.push v
            | none => fields := fields.push z
          let lhs ← callAt r c
          let rhs := mkAppN m (fields ++ ihVals)
          addTripRule trips ci.levelParams name (front ++ fields) lhs rhs
  for cs in cases do
    let ci ← getConstInfo cs
    discard <| MultiuniverseInductive.attempt? `Mumi m!"no rules for `{cs}`" do
    forallTelescope ci.type fun xs _ => do
      let ps := xs.extract 0 numParams
      let motive := xs[numParams]!
      if ← forallTelescope (← inferType motive) fun _ c => pure c.isProp then return
      let minors ← (xs.extract (numParams + 1) xs.size).filterM fun x => do
        forallTelescope (← inferType x) fun _ c => pure (c.getAppFn == motive)
      for m in minors do
        let name := ruleNameOf cs (← m.fvarId!.getUserName)
        forallTelescope (← inferType m) fun fields c => do
          -- the case split at the constructor: its indices and major read off
          -- the minor's conclusion
          let f := mkAppN (mkConst cs (ci.levelParams.map Level.param)) (ps.push motive)
          let (ms, _, cc) ← forallMetaTelescope (← inferType f)
          -- the indices and the major, then the minors
          let args := ms.extract 0 (ms.size - minors.size)
          unless ← isDefEq cc c do throwError "`{cs}` does not conclude at{indentExpr c}"
          let lhs ← instantiateMVars (mkAppN f (args ++ minors))
          addTripRule (trips) ci.levelParams name (ps ++ #[motive] ++ minors ++ fields) lhs
            (mkAppN m fields)

/-- How many parameters `mem.casesOn` takes before its motive: those of the block. -/
def casesParams (mem : Name) : MetaM Nat := do
  let ci ← getConstInfo (mem ++ `casesOn)
  forallTelescope ci.type fun xs _ => do
    for h : k in *...xs.size do
      let isMotive ← forallTelescope (← inferType xs[k]) fun ys c => do
        let some y := ys.back? | return false
        return c.isSort && (← inferType y).getAppFn.constName? == some mem
      if isMotive then return k
    throwError "`{mem}.casesOn` has no motive"

end Mumi
