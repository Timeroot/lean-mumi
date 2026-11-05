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
    -- only where the writer's constructor is the kernel's under another name: one
    -- that takes a field at the original of a copy is a different function
    let alias := match env.find? pub with
      | some (.defnInfo d) => d.value.getAppFn.constName? == some n && d.value.isConst
      | _ => false
    if alias && env.contains p then some pub else none
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

/-- The recursors over a block's copies whose rules hold by `rfl` in the kernel, for
a block with this many parameters.  Meta has no business unfolding them: what they
compute it reaches a long way down, through the graph and the recursions they are
built from (`Mumi.Displayed`), when the answer is known. -/
structure JointRecs where
  numParams : Nat := 0
  names : Array Name := #[]
  deriving Inhabited

/-- What `e`, one of the joint recursors at a constructor, reduces to: its minor
premise at the fields and at the recursors at those fields.  Never compared in
Meta: the kernel checks it when the proof is declared. -/
private def jointStep? (joints : JointRecs) (e : Expr) : MetaM (Option Expr) := do
  let .const n us := e.getAppFn | return none
  unless joints.names.contains n do return none
  let info ← getConstInfo n
  let args := e.getAppArgs
  let np := joints.numParams
  forallTelescope (info.instantiateTypeLevelParams us) fun xs concl => do
    unless args.size == xs.size do return none
    if ← isProp concl then return none
    -- the motives lead, then the minors, then the indices and the major
    let mut nMot := 0
    for x in xs.extract np xs.size do
      unless ← forallTelescope (← inferType x) fun _ c => pure c.isSort do break
      nMot := nMot + 1
    let motives := xs.extract np (np + nMot)
    let mut minors := #[]
    for x in xs.extract (np + nMot) xs.size do
      unless ← forallTelescope (← inferType x) fun _ c => pure (motives.contains c.getAppFn) do break
      minors := minors.push x
    let front := xs.extract 0 (np + nMot + minors.size)
    -- the major premise as a constructor of the block, as far as it unfolds to one
    let ctorOfMinor (m : Expr) : MetaM (Option Name) := do
      forallTelescope (← inferType m) fun _ c =>
        pure (c.getAppArgs.back?.bind (·.getAppFn.constName?))
    let names ← minors.mapM ctorOfMinor
    let mut major := args.back!
    let mut found := none
    for _ in [:16] do
      major ← whnfCore major
      if let .const c _ := major.getAppFn then
        if let some i := names.findIdx? (· == some c) then
          found := some i
          break
      let some m' ← unfoldDefinition? major | return none
      major := m'
    let some i := found | return none
    let fields := major.getAppArgs.extract np major.getAppNumArgs
    -- which recursor concludes at which motive
    let recAt (q : Nat) : MetaM (Option Name) := joints.names.findM? fun r => do
      forallTelescope (← getConstInfo r).type fun ys c =>
        return (ys.extract np ys.size).idxOf? c.getAppFn == some q
    let ms := minors[i]!
    let template : Expr ← forallTelescope (← inferType ms) fun zs _ => do
      unless fields.size ≤ zs.size do throwError "`{n}` at a constructor with too many fields"
      let fs := zs.extract 0 fields.size
      let vals ← (zs.extract fields.size zs.size).mapM fun h => do
        forallTelescope (← inferType h) fun ws c => do
          let some q := motives.idxOf? c.getAppFn | throwError "a hypothesis not at a motive"
          let some r ← recAt q | throwError "no recursor at motive {q}"
          let tgt := c.getAppArgs.back!
          let tty ← inferType tgt
          let idx := tty.getAppArgs.extract np tty.getAppNumArgs
          mkLambdaFVars ws (mkAppN (mkConst r us) (front ++ idx.push tgt))
      mkLambdaFVars (front ++ fs) (mkAppN ms (fs ++ vals))
    return some (template.beta (args.extract 0 front.size ++ fields)).headBeta

/-- One step of unfolding at the head, at the default transparency. -/
private def unfoldStep (joints : JointRecs) (e : Expr) : MetaM (Option Expr) := do
  if let some r ← jointStep? joints e then return some r
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
partial def heqUpToTrips (trips : Array Name) (joints : JointRecs) (used : IO.Ref Bool) (a b : Expr)
    (fuel : Nat := 40) : MetaM Expr := do
  let heqUpToTrips := fun a b fuel => heqUpToTrips trips joints used a b fuel
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
  if let some a' ← unfoldStep joints a then return ← heqUpToTrips a' b fuel
  if let some b' ← unfoldStep joints b then return ← heqUpToTrips a b' fuel
  if ← full then return ← mkHEqRefl a
  throwError "the two sides do not meet:{indentExpr a}\nand{indentExpr b}"

/-- `base`'s rule at the minor premise `c`: `X.rec_c`, `X.rec_1_c`, `X.casesOn_c`. -/
private def ruleNameOf (base c : Name) : Name :=
  base.getPrefix ++ Name.mkSimple (base.getString! ++ "_" ++ c.eraseMacroScopes.getString!)

/-- Add `name : ∀ xs, lhs = rhs`, proved up to round trips, as a `@[simp]` lemma. -/
private def addTripRule (trips : Array Name) (joints : JointRecs) (lps : List Name) (name : Name)
    (xs : Array Expr) (lhs rhs : Expr) : MetaM Unit := do
  if (← getEnv).contains name then return
  withCurrHeartbeats do
  -- a rule whose proof crosses no round trip is one `rfl` proves already
  let used ← IO.mkRef false
  let a ← whnfCore lhs
  let prf ← mkEqOfHEq (← heqUpToTrips trips joints used a rhs)
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
def addTripRules (numParams : Nat) (trips : Array Name) (recs cases : Array Name)
    (joints : Array Name := #[]) : TermElabM Unit :=
  withCanUnfoldPred (fun cfg info => do
      if joints.contains info.name then return false
      canUnfoldDefault cfg info) do
  let joints : JointRecs := { numParams, names := joints }
  for r in recs do
    let ci ← getConstInfo r
    let us := ci.levelParams.map Level.param
    discard <| MultiuniverseInductive.attempt? `Mumi m!"no rules for `{r}`" <| withCurrHeartbeats do
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
          addTripRule trips joints ci.levelParams name (front ++ fields) lhs rhs
  for cs in cases do
    let ci ← getConstInfo cs
    discard <| MultiuniverseInductive.attempt? `Mumi m!"no rules for `{cs}`" <| withCurrHeartbeats do
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
          addTripRule trips joints ci.levelParams name (ps ++ #[motive] ++ minors ++ fields) lhs
            (mkAppN m fields)

/-! ## A block of aliased inductives, joined

A block whose members do not all depend on each other is declared one component
at a time, each an ordinary inductive `X._ind`, and the kernel writes each a
recursor over its own component.  `X.rec` is owed to the whole block: a motive at
every member, a minor premise at every constructor, and a hypothesis at every
field at a member, whichever component that member is in.  It is built by
composing the components' recursors in the order they were declared: a field at
an earlier component is handed that component's recursion as its hypothesis, and
a `Prop` member's motive takes, after each index at a data member, the value the
recursion computes there -- which is always at an earlier component, the kernel
keeping indices out of a component's own types.
-/

/--
Give each member `X` declared as `X._ind` the writer's names: `X` itself, and
`X.c` at the constructor's type read back under them. -/
def addPublicAliases (members : Array Name) : MetaM Unit := do
  let matchPattern ← ofExcept <| getAttributeImpl (← getEnv) `match_pattern
  for m in members do
    let ii ← getConstInfoInduct (aliasIndName m)
    let us := ii.levelParams.map Level.param
    unless (← getEnv).contains m do
      addDef m ii.levelParams ii.type (mkConst ii.name us) .abbrev
      setReducibleAttribute m
  for m in members do
    let ii ← getConstInfoInduct (aliasIndName m)
    for c in ii.ctors do
      let pub := Name.str m c.getString!
      if (← getEnv).contains pub then continue
      let ci ← getConstInfo c
      addDef pub ci.levelParams (← publicize ci.type) (mkConst c (ci.levelParams.map Level.param))
        .abbrev
      setReducibleAttribute pub
      matchPattern.add pub .missing .global

/-- Overwrite the binder annotations of the leading `∀`s, keeping instance ones. -/
private partial def setBinderInfos (bis : Array BinderInfo) (e : Expr) (i : Nat := 0) : Expr :=
  if h : i < bis.size then
    match e with
    | .forallE n d b bi =>
      .forallE n d (setBinderInfos bis b (i + 1)) (if bi.isInstImplicit then bi else bis[i])
    | _ => e
  else e

/--
`X.rec` for every member of a block declared, component by component, as aliased
inductives `X._ind`: `members` as written, `defOrder` the order the components
were declared in, which is the order each recursion can call the others in. -/
partial def addJointRecs (members : Array Name) (defOrder : Array Nat) : TermElabM Unit := do
  let env ← getEnv
  let infos ← members.mapM fun m => getConstInfoInduct (aliasIndName m)
  if infos.any (·.isNested) then throwError "a component the kernel denested"
  -- the block's parameters: the fewest any member takes, the rest of a
  -- member's being parameters only of its own component
  let np := infos.foldl (fun a i => min a i.numParams) infos[0]!.numParams
  let mut lps : List Name := []
  for i in infos do
    for l in i.levelParams do
      unless lps.contains l do lps := lps ++ [l]
  let u := Level.param (elimLevelName lps)
  let pub (k : Nat) : Expr :=
    mkConst members[k]! (infos[k]!.levelParams.map Level.param)
  let isPropM ← members.mapM fun m => do
    forallTelescope (← getConstInfo m).type fun _ s => pure s.isProp
  let memberOf (e : Expr) : Option Nat := match e.getAppFn with
    | .const n _ => members.findIdx? fun m => n == m || n == aliasIndName m
    | _ => none
  forallBoundedTelescope (← getConstInfo members[0]!).type np fun ps _ => do
  let idxTy (k : Nat) : MetaM Expr := do instantiateForall (← getConstInfo members[k]!).type ps
  -- at which of a `Prop` member's indices its motive takes a data value
  let displayAt ← (Array.range members.size).mapM fun k => do
    unless isPropM[k]! do return #[]
    forallTelescope (← idxTy k) fun idx _ => idx.mapM fun i => do
      return (memberOf (← whnfR (← inferType i))).filter (!isPropM[·]!)
  -- the targets, written order save that a proposition follows the data it shows
  let mut order : Array Nat := #[]
  while order.size < members.size do
    let some k := (Array.range members.size).find? fun k =>
        !order.contains k && displayAt[k]!.all fun j? => j?.all order.contains
      | throwError "no order of the members settles their motives"
    order := order.push k
  let pos (k : Nat) : Nat := (order.idxOf? k).getD 0
  let motiveName (k : Nat) := Name.mkSimple s!"motive_{pos k + 1}"
  let sortOf (k : Nat) : Expr := if isPropM[k]! then mkSort .zero else mkSort u
  -- a motive applied at indices, the data values there, and a major
  let motiveApp (motives : Array Expr) (k : Nat) (idx : Array Expr) (vals : Array (Option Expr))
      (major : Expr) : Expr := Id.run do
    let mut out := #[]
    for i in *...idx.size do
      out := out.push idx[i]!
      if let some (some v) := vals[i]? then out := out.push v
    return mkAppN motives[pos k]! (out.push major)
  let idxArgs (ty : Expr) : Array Expr := ty.getAppArgs.extract np ty.getAppNumArgs
  let motiveDecls := order.map fun k => (motiveName k, BinderInfo.implicit,
    fun (prev : Array Expr) => do
      forallTelescope (← idxTy k) fun idx _ => do
        let mut shown : Array (Nat × Expr) := #[]
        for i in *...idx.size do
          if let some (some j) := displayAt[k]![i]? then
            let ty ← whnfR (← inferType idx[i]!)
            shown := shown.push (i, mkAppN prev[pos j]! ((idxArgs ty).push idx[i]!))
        let v ← mkFreshUserName `v
        withLocalDeclsD (shown.map fun (_, ty) => (v, fun _ => pure ty)) fun vs => do
        withLocalDeclD `t (mkAppN (pub k) (ps ++ idx)) fun t => do
          let mut binders := #[]
          for i in *...idx.size do
            binders := binders.push idx[i]!
            if let some q := shown.findIdx? (·.1 == i) then binders := binders.push vs[q]!
          mkForallFVars (binders.push t) (sortOf k))
  withLocalDecls motiveDecls fun motives => do
  -- the minor premises, in target order, each over those before it
  let ctorsOf (k : Nat) : Array Name := infos[k]!.ctors.toArray
  let mut minorDecls : Array (Name × BinderInfo × (Array Expr → TermElabM Expr)) := #[]
  let mut owners : Array Name := #[]
  for k in order do
    for c in ctorsOf k do
      let before := owners
      minorDecls := minorDecls.push (Name.mkSimple c.getString!, .default, fun prev => do
        let pubC := Name.str members[k]! c.getString!
        let cty ← instantiateForall ((← getConstInfo pubC).instantiateTypeLevelParams
          (infos[k]!.levelParams.map Level.param)) ps
        forallTelescope cty fun xs res => do
          -- the data value at a term, where the recursion can follow it: a
          -- field, by its hypothesis; a constructor of the block, by its minor
          let rec valueOf (hyps : Array (Expr × Expr)) (e : Expr) : MetaM Expr := do
            let e := e.headBeta
            if let some (_, h) := hyps.find? (·.1 == e.getAppFn) then
              return mkAppN h e.getAppArgs
            let .const cn _ := e.getAppFn | throwError "no value at{indentExpr e}"
            let some q := before.findIdx? (fun n => n == cn || publicName? env n == some cn
                || n == (publicName? env cn).getD .anonymous)
              | throwError "no value at{indentExpr e}"
            let m := prev[q]!
            let args := e.getAppArgs.extract np e.getAppNumArgs
            let mut v := mkAppN m args
            let mut ty ← instantiateForall (← inferType m) args
            while ty.isForall do
              let .forallE _ d _ _ := ty | break
              let h ← forallTelescope d fun dom c => do
                mkLambdaFVars dom (← valueOf hyps c.appArg!)
              v := mkApp v h
              ty := ty.bindingBody!.instantiate1 h
            return v
          let displayed (j : Nat) (hyps : Array (Expr × Expr)) (idx : Array Expr) :
              MetaM (Array (Option Expr)) :=
            (Array.range idx.size).mapM fun i => do
              if let some (some _) := displayAt[j]![i]? then return some (← valueOf hyps idx[i]!)
              else return none
          -- a hypothesis after the fields at each that is at a member
          let rec bind (i : Nat) (hyps : Array (Expr × Expr)) : TermElabM Expr := do
            if h : i < xs.size then
              let x := xs[i]
              let ihTy? ← forallTelescope (← inferType x) fun ys body => do
                let body ← whnfR body
                let some j := memberOf body | return none
                let idx := idxArgs body
                return some (← mkForallFVars ys
                  (motiveApp motives j idx (← displayed j hyps idx) (mkAppN x ys)))
              match ihTy? with
              | none => bind (i + 1) hyps
              | some ty =>
                withLocalDeclD ((← x.fvarId!.getUserName).appendAfter "_ih") ty fun ih =>
                  bind (i + 1) (hyps.push (x, ih))
            else
              let idx := idxArgs res
              let c := mkAppN (mkConst pubC (infos[k]!.levelParams.map Level.param)) (ps ++ xs)
              let body := motiveApp motives k idx (← displayed k hyps idx) c
              mkForallFVars (xs ++ hyps.map (·.2)) body
          bind 0 #[])
      owners := owners.push (Name.str members[k]! c.getString!)
  withLocalDecls minorDecls fun minors => do
  let front := ps ++ motives ++ minors
  let recLps := elimLevelName lps :: lps
  let recUs := recLps.map Level.param
  -- the joint recursion at a member, at the indices and major of `ty`
  let call (j : Nat) (ty x : Expr) : Expr :=
    mkAppN (mkConst (members[j]! ++ `rec) recUs) (front ++ idxArgs ty |>.push x)
  -- the joint recursion's value at each data index of a proposition's motive
  let shownAt (k : Nat) (idx : Array Expr) : MetaM (Array (Option Expr)) :=
    (Array.range idx.size).mapM fun i => do
      let some (some j) := displayAt[k]![i]? | return none
      let ty ← whnfR (← inferType idx[i]!)
      return some (call j ty idx[i]!)
  for k in defOrder do
    let m := members[k]!
    let ii := infos[k]!
    let kr ← getConstInfoRec (aliasIndName m ++ `rec)
    let groupMembers := ii.all.toArray.filterMap fun n => members.findIdx? (aliasIndName · == n)
    let (type, value) ← forallTelescope (← idxTy k) fun idx _ => do
      withLocalDeclD `t (mkAppN (pub k) (ps ++ idx)) fun t => do
        let concl := motiveApp motives k idx (← shownAt k idx) t
        -- the component's own parameters: the block's, and those of its indices
        -- the component took as parameters
        let extra := idx.extract 0 (ii.numParams - np)
        let kps := ps ++ extra
        let elim := if kr.levelParams.length == ii.levelParams.length + 1 then
            [if isPropM[k]! then Level.zero else u] else []
        let kUs := elim ++ ii.levelParams.map Level.param
        let mut e := mkAppN (mkConst kr.name kUs) kps
        -- its motives, at the block's
        for gm in groupMembers do
          let ty ← whnf (← inferType e)
          let .forallE _ mty _ _ := ty | throwError "`{kr.name}` takes fewer motives"
          let mot ← forallTelescope mty fun zs _ => do
            let gidx := extra ++ zs.pop
            mkLambdaFVars zs (motiveApp motives gm gidx (← shownAt gm gidx) zs.back!)
          e := mkApp e mot
        -- its minors, the block's at the hypotheses the kernel does not give
        for gm in groupMembers do
          for c in ctorsOf gm do
            let ty ← whnf (← inferType e)
            let .forallE _ mty _ _ := ty | throwError "`{kr.name}` takes fewer minors"
            let q := owners.idxOf (Name.str members[gm]! c.getString!)
            let nf := (← getConstInfoCtor c).numFields
            let minor ← forallTelescope mty fun zs _ => do
              let fields := zs.extract 0 nf
              let kihs := zs.extract nf zs.size
              let mut taken := 0
              let mut ihs := #[]
              for x in fields do
                let ih? ← forallTelescope (← inferType x) fun ys body => do
                  let body ← whnfR body
                  let some j := memberOf body | return none
                  return some (j, ← mkLambdaFVars ys (call j body (mkAppN x ys)))
                let some (j, v) := ih? | continue
                if groupMembers.contains j then
                  ihs := ihs.push kihs[taken]!
                  taken := taken + 1
                else ihs := ihs.push v
              mkLambdaFVars zs (mkAppN minors[q]! (fields ++ ihs))
            e := mkApp e minor
        let app := mkAppN e (idx.extract (ii.numParams - np) idx.size |>.push t)
        let all := front ++ idx ++ #[t]
        -- parameters, motives and indices implicit; minors and the major explicit
        let infos := (ps.map fun _ => BinderInfo.implicit) ++ motives.map (fun _ => BinderInfo.implicit)
          ++ minors.map (fun _ => BinderInfo.default) ++ idx.map (fun _ => BinderInfo.implicit)
          ++ #[BinderInfo.default]
        let ty ← mkForallFVars all concl
        return (setBinderInfos infos ty, ← mkLambdaFVars all app)
    addDef (m ++ `rec) recLps type value (compile := false)
    MultiuniverseInductive.markElabAsElim (m ++ `rec)

/-! ## Stated over the originals, a `Prop` copy's bridge crossed by proof irrelevance

A constructor with a field at a `Prop` copy `denest` made -- `T.mkT : Nonempty T
→ T`, where the kernel holds a `T.nested_Nonempty_1` -- is the kernel's with the
copy until the bridge `ofOrig`/`toOrig` exists.  Then the writer's `T.mkT` takes
the original and packs it, and the block's recursion is stated over the
originals: a motive at `Nonempty T`, a minor at `Nonempty.intro`.  Its value is
the lowering's `mutualRec` at motives and minors moved across the bridge, and
every such move is definitional, because the two sides of a `Prop` bridge are
proofs and any two proofs of one proposition are one. -/

/-- The bridge out of the copy `e` is an application of, if it is one: what it
copies, and `ofOrig` and `toOrig` at its arguments. -/
private def bridgeAt? (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let .const n us := e.getAppFn | return none
  let env ← getEnv
  unless env.contains (n ++ `ofOrig) && env.contains (n ++ `toOrig) do return none
  let args := e.getAppArgs
  let toO := mkAppN (mkConst (n ++ `toOrig) us) args
  let ofO := mkAppN (mkConst (n ++ `ofOrig) us) args
  let ty ← whnf (← inferType toO)
  unless ty.isForall do return none
  return some (ty.bindingBody!, ofO, toO)

/-- `e` read over the originals: a round trip through a bridge dropped, a copy's
constructor read as the original's, a held constructor at a packed field as the
writer's at the field. -/
private partial def overOriginals (held : Array (Name × Name)) (e : Expr) : MetaM Expr := do
  let post (e : Expr) : MetaM TransformStep := do
    let f := e.getAppFn
    let args := e.getAppArgs
    match f with
    | .const n us =>
      -- only a whole application: `transform` meets the head and every partial
      -- application on the way out to it
      let arity ← try forallTelescope (← getConstInfo n).type fun xs _ => pure xs.size
        catch _ => pure 0
      unless args.size == arity && arity > 0 do return .continue
      -- `toOrig (ofOrig y)` is `y`, and `toOrig (C.c xs)` is the original's `c`
      if n.isStr && n.getString! == "toOrig" then
        let x := args.back!
        let xf := x.getAppFn
        if let .const m _ := xf then
          if m == n.getPrefix ++ `ofOrig then return .done x.appArg!
          if m.getPrefix == n.getPrefix && (← getEnv).contains m then
            -- the copy's constructor, and the original's of the same name
            let ty ← whnf (← inferType e)
            if let .const o ous := ty.getAppFn then
              let oc := Name.str o m.getString!
              if (← getEnv).contains oc then
                let ii ← getConstInfoInduct o
                let fields := x.getAppArgs.extract (x.getAppNumArgs - ((← getConstInfoCtor oc).numFields)) x.getAppNumArgs
                -- a field at a copy in turn goes back to what it copies
                let fields ← fields.mapM fun f => do
                  match ← bridgeAt? (← inferType f) with
                  | some (_, _, toO) => overOriginals held (mkApp toO f)
                  | none => pure f
                return .done (mkAppN (mkConst oc ous) (ty.getAppArgs.extract 0 ii.numParams ++ fields))
      -- a held constructor at a field packed by `ofOrig` is the writer's at it
      if let some (_, pub) := held.find? (·.1 == n) then
        let args' := args.map fun a => match a.getAppFn with
          | .const m _ => if m.isStr && m.getString! == "ofOrig" then a.appArg! else a
          | _ => a
        return .done (mkAppN (mkConst pub us) args')
      return .continue
    | _ => return .continue
  Meta.transform e (post := post)

/--
Rebuild a telescope over the originals: each binder at a copy is put at what it
copies and stands, under the binders after it, for its `ofOrig`; a motive over a
copy is put over the original and stands for itself at `toOrig`; a minor premise
is rebuilt in turn and stands for itself at its fields' `toOrig`. -/
private partial def rebuildPi (held : Array (Name × Name)) (motives : Array Expr) (ty : Expr)
    (k : Array Expr → Array Expr → Expr → MetaM α) (olds : Array Expr := #[]) : MetaM α := do
  match ty with
  | .forallE n d b bi =>
    let d ← overOriginals held (← Core.betaReduce d)
    if let some (orig, ofO, _) ← bridgeAt? d then
      withLocalDecl n bi orig fun y =>
        rebuildPi held motives (b.instantiate1 (mkApp ofO y)) k (olds.push y)
    else
      withLocalDecl n bi d fun y =>
        rebuildPi held motives (b.instantiate1 y) k (olds.push y)
  | _ => k olds #[] (← overOriginals held (← Core.betaReduce ty))

/--
`dst` as `src` stated over the originals: `src` is the lowering's `mutualRec`
for a member or a copy, its component universes all `u`. -/
partial def restateOverOriginals (held : Array (Name × Name)) (blockLps : List Name) (src dst : Name) :
    MetaM Unit := do
  let info ← getConstInfo src
  let u := elimLevelName blockLps
  let lvls := info.levelParams.map fun l => if blockLps.contains l then Level.param l else .param u
  let ty := info.instantiateTypeLevelParams lvls
  -- the new binders, and what each old one stands for in terms of them
  let rec go (ty : Expr) (news images : Array Expr) : MetaM (Expr × Expr) := do
    match ty with
    | .forallE n d b bi =>
      let d := d.headBeta
      -- a motive over a copy: over the original, and the old one is it at `toOrig`
      let motiveOverCopy? ← forallTelescope d fun zs s => do
        unless s.isSort do return none
        let some z := zs.back? | return none
        let some (orig, _, toO) ← bridgeAt? (← inferType z) | return none
        let newTy ← mkForallFVars zs.pop (← withLocalDecl `t .default orig fun t => do
          mkForallFVars #[t] s)
        return some (newTy, toO, zs.size)
      if let some (newTy, _, arity) := motiveOverCopy? then
        return ← withLocalDecl n bi newTy fun m => do
          let img ← forallTelescope d fun zs _ => do
            let some (_, _, toO) ← bridgeAt? (← inferType zs.back!) | throwError "lost the bridge"
            mkLambdaFVars zs (mkAppN m (zs.pop.push (mkApp toO zs.back!)))
          let _ := arity
          go (b.instantiate1 img) (news.push m) (images.push img)
      -- a binder at a copy: at the original, and the old one is its `ofOrig`
      if let some (orig, ofO, _) ← bridgeAt? d then
        return ← withLocalDecl n bi orig fun y =>
          go (b.instantiate1 (mkApp ofO y)) (news.push y) (images.push (mkApp ofO y))
      -- a minor premise, or anything else: rebuilt over the originals, and the old
      -- one is the new at its arguments' `toOrig`
      let isPi := d.isForall
      let newTy ← if isPi then
          rebuildPi held #[] d fun ys _ body => do mkForallFVars ys body
        else overOriginals held d
      withLocalDecl n bi newTy fun y => do
        let img ← if !isPi then pure y else forallTelescope d fun xs _ => do
          let mut args := #[]
          for x in xs do
            if let some (_, _, toO) ← bridgeAt? (← inferType x) then args := args.push (mkApp toO x)
            else args := args.push x
          mkLambdaFVars xs (mkAppN y args)
        go (b.instantiate1 img) (news.push y) (images.push img)
    | body =>
      let body ← overOriginals held (← Core.betaReduce body)
      let value := mkAppN (mkConst src lvls) images
      return (← mkForallFVars news body, ← mkLambdaFVars news value)
  let (type, value) ← go ty #[] #[]
  addDef dst (u :: blockLps) type value (compile := false)
  markElabAsElim dst

/--
For an aliased block whose `Prop` copies have their bridge: the writer's
constructors held back at the copies, and the block's recursors stated over the
originals, `X.rec` at each member written and `X.rec_k` at each copy. -/
partial def publishOverOriginals (written : Array Name) : MetaM Unit := do
  let env ← getEnv
  let mut held : Array (Name × Name) := #[]
  for m in written do
    let some (.inductInfo ii) := env.find? (aliasIndName m) | continue
    for c in ii.ctors do
      let pub := Name.str m c.getString!
      unless env.contains pub do held := held.push (c, pub)
  if held.isEmpty then return
  -- the constructors, each at the originals, packing what it is handed
  for (c, pub) in held do
    let ci ← getConstInfo c
    let us := ci.levelParams.map Level.param
    let rec build (ty : Expr) (news args : Array Expr) : MetaM (Expr × Expr) := do
      match ty with
      | .forallE n d b bi =>
        if let some (orig, ofO, _) ← bridgeAt? d then
          withLocalDecl n bi orig fun y =>
            build (b.instantiate1 (mkApp ofO y)) (news.push y) (args.push (mkApp ofO y))
        else
          withLocalDecl n bi d fun y => build (b.instantiate1 y) (news.push y) (args.push y)
      | body => return (← mkForallFVars news body, ← mkLambdaFVars news (mkAppN (mkConst c us) args))
    let (type, value) ← build ci.type #[] #[]
    addDef pub ci.levelParams (← publicize type) value .abbrev
    setReducibleAttribute pub
  -- the recursions, the members' and then the copies' in the lowering's order
  let mut lps : List Name := []
  for m in written do
    for l in (← getConstInfo m).levelParams do
      unless lps.contains l do lps := lps ++ [l]
  for m in written do
    if env.contains (m ++ `mutualRec) && !env.contains (m ++ `rec) then
      restateOverOriginals held lps (m ++ `mutualRec) (m ++ `rec)
  -- every copy's recursion, at the major it copies
  let some first := written[0]? | return
  let mut k := 1
  let copies := env.constants.map₂.toList.filterMap fun (n, _) =>
    if n.getPrefix == first && n.isStr && (n.getString!.startsWith "nested_")
        && env.contains (n ++ `mutualRec) && env.contains (n ++ `toOrig) then some n else none
  let copies := copies.toArray.qsort fun a b =>
    (a.getString!.splitOn "_").getLast!.toNat! < (b.getString!.splitOn "_").getLast!.toNat!
  for c in copies do
    restateOverOriginals held lps (c ++ `mutualRec) (first ++ `rec |>.appendIndexAfter k)
    k := k + 1

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

/-- The function into the view of a member with held constructors, as a case
split by the kernel's `casesOn`, which the compiler implements.  A held field is
read back out of its copy; the writer's constructor packs it in again, which is
the kernel's field up to proof irrelevance. -/
private def heldViewFn (numParams : Nat) (ind : Name) (kctors : Array Name)
    (binders : Array Expr) (x motive : Expr) : MetaM Expr := do
  let .const _ us := (← whnfR (← inferType x)).getAppFn | throwError "no inductive under `{x}`"
  let ps := binders.extract 0 numParams
  let is := binders.extract numParams binders.size
  let vName := viewName ind.getPrefix
  let lvl ← getLevel (← instantiateLambda motive (is.push x))
  let mut minors := #[]
  for kc in kctors do
    let kt ← instantiateForall ((← getConstInfo kc).instantiateTypeLevelParams us) ps
    minors := minors.push <| ← forallTelescope kt fun fs _ => do
      let args ← fs.mapM fun f => do
        let ty ← inferType f
        if let some (_, _, toO) ← bridgeAt? ty then
          if ← isProp ty then return mkApp toO f
        return f
      mkLambdaFVars fs (mkAppN (mkConst (Name.str vName kc.getString!) us) (ps ++ args))
  return mkAppN (mkConst (ind ++ `casesOn) (lvl :: us)) (ps ++ #[motive] ++ is ++ #[x] ++ minors)

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
      -- a constructor the writer has at the originals of a copy is not the
      -- kernel's, nor are what the kernel's `casesOn` and injectivity say of it
      let heldCtor (c : Name) : Bool := (publicName? env c).isNone
      unless ii.ctors.any heldCtor do
        discard <| attempt? `Mumi m!"no `casesOn` for `{mem}`" <|
          restate (ind ++ `casesOn) (mem ++ `casesOn) (motive?.map (numParams, ·))
      -- a constructor at the originals rather than the kernel's is not the
      -- kernel's `casesOn`'s to state, and the case split is cut out of `X.rec`
      if !(← getEnv).contains (mem ++ `casesOn) && (← getEnv).contains (mem ++ `rec) then
        let elim := (← getConstInfo (mem ++ `rec)).levelParams.take 1
        discard <| attempt? `Mumi m!"no `casesOn` for `{mem}`" do
          addSoloElim numParams elim.toArray false (mem ++ `rec) (mem ++ `casesD)
            (forCases := true) (evenIfWeaker := true)
          addMajorFirst numParams mem (mem ++ `casesD) (mem ++ `casesOn)
      -- the equation compiler would take such a constructor apart as the
      -- kernel's, so a `match` goes through a view, which presents it as the
      -- writer's (`Mumi.MatchView`)
      if ii.ctors.any heldCtor then
        discard <| attempt? `Mumi m!"no view for `{mem}`" <|
          addView numParams mem (ii.ctors.toArray.map fun c => Name.str mem c.getString!)
            (fnValue? := some (heldViewFn numParams ind ii.ctors.toArray))
      -- `cases` and `induction` reach for an eliminator by the type's head, and
      -- the kernel's are stated over `X._ind`: the writer's are registered, so
      -- what the tactics leave is stated over `X`
      if (← getEnv).contains (mem ++ `casesOn) then
        markElabAsElim (mem ++ `casesOn) (induction := false)
      if (← getEnv).contains (mem ++ `rec) && !(← getEnv).contains (mem ++ `recD) then
        let elim := (← getConstInfo (mem ++ `rec)).levelParams.take 1
        -- a proposition's eliminates into `Prop`, its other universe pinned
        let isPropMem ← forallTelescope (← getConstInfo mem).type fun _ s => pure s.isProp
        discard <| attempt? `Mumi m!"no one-motive recursor for `{mem}`" <|
          addSoloElim numParams elim.toArray isPropMem (mem ++ `rec) (mem ++ `recD)
            (forCases := false) (evenIfWeaker := true)
      for s in [`noConfusionType, `noConfusion, `ctorIdx, `below, `brecOn] do
        discard <| attempt? `Mumi m!"no `{s}` for `{mem}`" <| restate (ind ++ s) (mem ++ s)
      let pubs := ii.ctors.toArray.map fun c => Name.str mem c.getString!
      for c in ii.ctors do
        let pub := Name.str mem c.getString!
        unless heldCtor c do
          discard <| attempt? `Mumi m!"no injectivity for `{pub}`" do
            restate (c ++ `inj) (pub ++ `inj)
            restate (c ++ `injEq) (pub ++ `injEq) (simp := true)
        -- and its injectivity is read back through the case split
        if !(← getEnv).contains (pub ++ `inj) && ((← getEnv).find? pub).any (·.isDefinition) then
          discard <| attempt? `Mumi m!"no injectivity for `{pub}`" <|
            addInjViaCases numParams mem pub pubs
        unless heldCtor c do
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

end Mumi
