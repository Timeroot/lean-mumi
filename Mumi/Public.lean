/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Mumi.Lowering
public import Mumi.View
import all Lean.Meta.Injective
import Lean.Meta.Tactic.Simp.Main
import all Lean.Elab.PreDefinition.Eqns

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
    (reducible := true) (pinElim := false) : MetaM Unit := do
  let env ← getEnv
  if env.contains dst then return
  let some info := env.find? src | return
  -- a proposition's eliminator, into `Prop`: its own universe, the first, goes
  let pin := pinElim && !info.levelParams.isEmpty
  let lps := if pin then info.levelParams.drop 1 else info.levelParams
  let srcUs := if pin then Level.zero :: lps.map Level.param else lps.map Level.param
  let mut type ← publicize (info.instantiateTypeLevelParams srcUs)
  if let some (i, nm) := motiveAt then type := renameBinder i nm type
  let value := mkConst src srcUs
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
  -- with no data every motive is a proposition, and no universe is left to name
  let allProp := isPropM.all id
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
  let recLps := if allProp then lps else elimLevelName lps :: lps
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
      -- a proposition of a block eliminates into `Prop`, as any `Prop` in a block
      -- with data does, whatever the kernel would let it do on its own
      let isPropMem ← forallTelescope (← getConstInfo mem).type fun _ s => pure s.isProp
      let largeCases := isPropMem &&
        ((env.find? (ind ++ `casesOn)).any (·.levelParams.length == ii.levelParams.length + 1))
      unless ii.ctors.any heldCtor do
        discard <| attempt? `Mumi m!"no `casesOn` for `{mem}`" <|
          restate (ind ++ `casesOn) (mem ++ `casesOn) (motive?.map (numParams, ·)) (pinElim := largeCases)
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
        let recLps := (← getConstInfo (mem ++ `rec)).levelParams
        let elim := if recLps.length == ii.levelParams.length then [] else recLps.take 1
        -- a proposition's eliminates into `Prop`, its other universe pinned
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

/-! ## Members that left the block, put back

A `Prop` member that left an induction-inductive block (`Big` beside `T` and `Ok`,
`Big.node (cs hs : List T) (h : Ok cs) : Big (.node cs h)`) is an ordinary inductive
stated over the block, and nothing in the block mentions it.  So the recursion over
the rest needs no widening to speak of: it ignores what it is handed for the member
that left.  And that member's own recursion is the kernel's, into its displayed
motive at whatever the block's recursion computes: every field's hypothesis is a call
of the block's recursion, with none of the circularity the graph in `Mumi.Displayed`
is for, so a field the conclusion does not name is no trouble at all.

Where a rule of the block's recursion crosses a copy's round trip (`T.rec` at
`T.node`), a minor's conclusion is only propositionally what the kernel asks for, and
is carried across by those rules. -/

/-- What a motive of the widened recursion is at. -/
private inductive WideTarget where
  /-- the `q`th motive of the recursion over the block -/
  | core (q : Nat)
  /-- the `k`th member that left -/
  | peeled (k : Nat)
  deriving BEq, Inhabited

/-- The value at `e` a minor premise's statement names: a field, by its hypothesis; a
constructor, by its minor, which must have been bound already. -/
private partial def wideValueOf (np : Nat) (ctors : Array Name) (prev : Array Expr)
    (hyps : Array (Expr × Expr)) (e : Expr) : MetaM Expr := do
  let e := e.headBeta
  if let some (_, h) := hyps.find? (·.1 == e.getAppFn) then
    return mkAppN h e.getAppArgs
  let .const cn _ := e.getAppFn | throwError "no value at{indentExpr e}"
  let some q := (ctors.extract 0 prev.size).idxOf? cn
    | throwError "no value at{indentExpr e}"
  let ctorParams := match (← getEnv).find? cn with
    | some (.ctorInfo v) => v.numParams
    | _ => np
  let m := prev[q]!
  let args := e.getAppArgs.extract ctorParams e.getAppNumArgs
  let mut v := mkAppN m args
  let mut ty ← instantiateForall (← inferType m) args
  while ty.isForall do
    let .forallE _ d _ _ := ty | break
    let h ← forallTelescope d fun dom c => do
      mkLambdaFVars dom (← wideValueOf np ctors prev hyps c.appArg!)
    v := mkApp v h
    ty := ty.bindingBody!.instantiate1 h
  return v

/--
Put the members `peeled`, declared as `X._ind`, back into the recursion over the rest
of the block.  `written` is the block as the writer has it, `cores` the recursors over
what stayed with the names they are to be widened to, `groups` the peeled members in
the order they were declared.  `trips` and `joints` are what `addTripRules` wants, the
rules being stated over the widened recursors. -/
def addWidenedRecs (np : Nat) (written : Array Name) (cores : Array (Name × Name))
    (peeled : Array Name) (order₀ : Array Nat) (trips joints : Array Name) :
    TermElabM Unit := do
  let info0 ← getConstInfo cores[0]!.1
  let recLps := info0.levelParams
  let recUs := recLps.map Level.param
  for (c, _) in cores do
    unless (← getConstInfo c).levelParams == recLps do
      throwError "`{c}` and `{cores[0]!.1}` have different universes"
  let infos ← peeled.mapM fun m => getConstInfoInduct (aliasIndName m)
  if infos.any (·.isNested) then throwError "a member that left is nested"
  forallTelescope info0.type fun xs _ => do
  let ps := xs.extract 0 np
  let mut nMot := 0
  for x in xs.extract np xs.size do
    unless ← forallTelescope (← inferType x) fun _ c => pure c.isSort do break
    nMot := nMot + 1
  let oldMot := xs.extract np (np + nMot)
  let mut nMin := 0
  for x in xs.extract (np + nMot) xs.size do
    unless ← forallTelescope (← inferType x) fun _ c => pure (oldMot.contains c.getAppFn) do break
    nMin := nMin + 1
  let oldMin := xs.extract (np + nMot) (np + nMot + nMin)
  -- which core concludes at which motive
  let mut coreAt : Array (Option (Name × Name)) := oldMot.map fun _ => none
  for (c, w) in cores do
    let q? ← forallTelescope (← getConstInfo c).type fun ys concl =>
      pure ((ys.extract np ys.size).idxOf? concl.getAppFn)
    if let some q := q? then coreAt := coreAt.set! q (some (c, w))
  -- at which of its indices a core motive takes a value, and whether it is a `Prop`'s
  let isValue (z : Expr) : MetaM Bool := do
    forallTelescope (← inferType z) fun _ c => pure (oldMot.contains c.getAppFn)
  let coreShown ← oldMot.mapM fun m => do
    forallTelescope (← inferType m) fun zs _ => do
      let mut out : Array Bool := #[]
      for z in zs.pop do
        if ← isValue z then
          out := out.set! (out.size - 1) true
        else out := out.push false
      return out
  let coreIsProp ← oldMot.mapM fun m => do
    forallTelescope (← inferType m) fun _ c => pure c.isProp
  -- the target a type is at, and its indices
  let targetOf (ty : Expr) : MetaM (Option (WideTarget × Array Expr)) := do
    let ty ← instantiateMVars ty
    let .const n _ := ty.getAppFn | return none
    if let some k := peeled.findIdx? (fun m => m == n || aliasIndName m == n) then
      return some (.peeled k, ty.getAppArgs.extract np ty.getAppNumArgs)
    for q in *...oldMot.size do
      let (ms, _, _) ← forallMetaTelescope (← inferType oldMot[q]!)
      let mTy ← instantiateMVars (← inferType ms.back!)
      unless mTy.getAppFn.isConstOf n do continue
      if ← isDefEq mTy ty then
        -- the motive's binders, the values it shows taken out
        let mut idx : Array Expr := #[]
        for z in ms.pop do
          unless ← forallTelescope (← inferType z) (fun _ c => pure (oldMot.contains c.getAppFn)) do
            idx := idx.push (← instantiateMVars z)
        return some (.core q, idx)
    return none
  let peeledIsProp ← peeled.mapM fun m => do
    forallTelescope (← getConstInfo m).type fun _ s => pure s.isProp
  let isDataTarget : WideTarget → Bool
    | .core q => !coreIsProp[q]!
    | .peeled k => !peeledIsProp[k]!
  -- the universe of the recursion, the first of a core's
  let elimU := recUs.headD levelZero
  let idxTy (k : Nat) : MetaM Expr := do instantiateForall (← getConstInfo peeled[k]!).type ps
  let peeledShown ← (Array.range peeled.size).mapM fun k => do
    forallTelescope (← idxTy k) fun idx _ => idx.mapM fun i => do
      return peeledIsProp[k]! && ((← targetOf (← inferType i)).map (·.1)).any isDataTarget
  let shown : WideTarget → Array Bool
    | .core q => coreShown[q]!
    | .peeled k => peeledShown[k]!
  -- the order of the targets: as written, a proposition after the data it shows,
  -- the nested ones after the members
  let mut entries : Array WideTarget := #[]
  for n in written do
    if let some k := peeled.idxOf? n then entries := entries.push (.peeled k)
    else
      for q in *...oldMot.size do
        let isIt ← forallTelescope (← inferType oldMot[q]!) fun zs _ => do
          return (← inferType zs.back!).getAppFn.isConstOf n
        if isIt then entries := entries.push (.core q)
  for q in *...oldMot.size do
    unless entries.contains (.core q) do entries := entries.push (.core q)
  let depsOf : WideTarget → TermElabM (Array WideTarget)
    | .core q => do
      let ty ← inferType oldMot[q]!
      return (Array.range oldMot.size).filterMap fun r =>
        if ty.containsFVar oldMot[r]!.fvarId! then some (.core r) else none
    | .peeled k => do
      if !peeledIsProp[k]! then return #[]
      forallTelescope (← idxTy k) fun idx _ => do
        let mut out := #[]
        for i in idx do
          if let some (t, _) ← targetOf (← inferType i) then
            if isDataTarget t then out := out.push t
        return out
  let deps ← entries.mapM depsOf
  let mut order : Array WideTarget := #[]
  while order.size < entries.size do
    let mut next := none
    for q in *...entries.size do
      if !order.contains entries[q]! && deps[q]!.all order.contains then
        next := some entries[q]!
        break
    let some t := next | throwError "no order of the members settles their motives"
    order := order.push t
  let pos (t : WideTarget) : Nat := (order.idxOf? t).getD 0
  let pub (k : Nat) : Expr := mkConst peeled[k]! (infos[k]!.levelParams.map Level.param)
  let motiveApp (motives : Array Expr) (t : WideTarget) (idx : Array Expr)
      (value : Expr → MetaM Expr) (major : Expr) : MetaM Expr := do
    let mut out := #[]
    let sh := shown t
    for i in *...idx.size do
      out := out.push idx[i]!
      if sh[i]?.getD false then out := out.push (← value idx[i]!)
    return mkAppN motives[pos t]! (out.push major)
  let motiveDecls : Array (Name × BinderInfo × (Array Expr → TermElabM Expr)) :=
    order.mapIdx fun at_ t => (Name.mkSimple s!"motive_{at_ + 1}", BinderInfo.implicit,
    fun (prev : Array Expr) => do
      match t with
      | .core q =>
        let done := (Array.range prev.size).filterMap fun p =>
          match order[p]! with
          | .core r => some (oldMot[r]!, prev[p]!)
          | _ => none
        return (← inferType oldMot[q]!).replaceFVars (done.map (·.1)) (done.map (·.2))
      | .peeled k =>
        forallTelescope (← idxTy k) fun idx _ => do
          let mut decls : Array (Nat × Expr) := #[]
          for i in *...idx.size do
            if peeledShown[k]![i]! then
              let some (j, args) ← targetOf (← inferType idx[i]!) | throwError "no target"
              decls := decls.push (i, mkAppN prev[pos j]! (args.push idx[i]!))
          let v ← mkFreshUserName `v
          withLocalDeclsD (decls.map fun (_, ty) => (v, fun _ => pure ty)) fun vs => do
          withLocalDeclD `t (mkAppN (pub k) (ps ++ idx)) fun x => do
            let mut binders := #[]
            for i in *...idx.size do
              binders := binders.push idx[i]!
              if let some q := decls.findIdx? (·.1 == i) then binders := binders.push vs[q]!
            mkForallFVars (binders.push x)
              (mkSort (if peeledIsProp[k]! then .zero else elimU)))
  withLocalDecls motiveDecls fun motives => do
  let coreMotives := (Array.range oldMot.size).map fun q => motives[pos (.core q)]!
  -- the minors, in target order; `some i` is the core's `i`th
  let mut minorSrc : Array (WideTarget × Option Nat × Name) := #[]
  let mut minorCtor : Array Name := #[]
  for t in order do
    match t with
    | .core q =>
      for i in *...oldMin.size do
        let (hd, c) ← forallTelescope (← inferType oldMin[i]!) fun _ c =>
          pure (c.getAppFn, (c.getAppArgs.back?.bind (·.getAppFn.constName?)).getD .anonymous)
        if hd == oldMot[q]! then
          minorSrc := minorSrc.push (t, some i, ← oldMin[i]!.fvarId!.getUserName)
          minorCtor := minorCtor.push c
    | .peeled k =>
      for c in infos[k]!.ctors do
        minorSrc := minorSrc.push (t, none, Name.mkSimple c.getString!)
        minorCtor := minorCtor.push (Name.str peeled[k]! c.getString!)
  let minorDecls : Array (Name × BinderInfo × (Array Expr → TermElabM Expr)) :=
    minorSrc.mapIdx fun at_ (t, src, name) => (name, BinderInfo.default,
    fun (prev : Array Expr) => do
      match t, src with
      | _, some i =>
        let done := (Array.range prev.size).filterMap fun p =>
          minorSrc[p]!.2.1.map fun r => (oldMin[r]!, prev[p]!)
        return (← inferType oldMin[i]!).replaceFVars
          (oldMot ++ done.map (·.1)) (coreMotives ++ done.map (·.2))
      | .peeled k, none =>
        let pubC := minorCtor[at_]!
        let us := infos[k]!.levelParams.map Level.param
        let cty ← instantiateForall ((← getConstInfo pubC).instantiateTypeLevelParams us) ps
        forallTelescope cty fun fs res => do
          let rec bind (i : Nat) (hyps : Array (Expr × Expr)) : TermElabM Expr := do
            if h : i < fs.size then
              let x := fs[i]
              let ihTy? ← forallTelescope (← inferType x) fun ys body => do
                let some (j, idx) ← targetOf body | return none
                return some (← mkForallFVars ys
                  (← motiveApp motives j idx (wideValueOf np minorCtor prev hyps) (mkAppN x ys)))
              match ihTy? with
              | none => bind (i + 1) hyps
              | some ty =>
                withLocalDeclD ((← x.fvarId!.getUserName).appendAfter "_ih") ty fun ih =>
                  bind (i + 1) (hyps.push (x, ih))
            else
              let idx := res.getAppArgs.extract np res.getAppNumArgs
              let body ← motiveApp motives t idx (wideValueOf np minorCtor prev hyps)
                (mkAppN (mkConst pubC us) (ps ++ fs))
              mkForallFVars (fs ++ hyps.map (·.2)) body
          bind 0 #[]
      | _, _ => throwError "a minor with no source")
  withLocalDecls minorDecls fun minors => do
  let front := ps ++ motives ++ minors
  let coreMinors := (Array.range oldMin.size).map fun i =>
    minors[(minorSrc.findIdx? (·.2.1 == some i)).getD 0]!
  let coreFront := ps ++ coreMotives ++ coreMinors
  -- a core stated at the block's recursion, read at the widened one
  let toWide (e : Expr) : Expr := e.replace fun e' =>
    match e'.getAppFn with
    | .const n _ =>
      match cores.find? (·.1 == n) with
      | some (_, w) =>
        if e'.getAppNumArgs ≥ coreFront.size then
          some (mkAppN (mkConst w recUs)
            (front ++ e'.getAppArgs.extract coreFront.size e'.getAppNumArgs))
        else none
      | none => none
    | _ => none
  -- the data first: a proposition's conclusion names the value at its indices
  let dataFirst := (Array.range oldMot.size).filter (!coreIsProp[·]!) ++
    (Array.range oldMot.size).filter (coreIsProp[·]!)
  for q in dataFirst do
    let some (c, w) := coreAt[q]! | continue
    let (type, value) ← forallTelescope
        (← instantiateForall (← getConstInfo c).type coreFront) fun rest concl => do
      let all := front ++ rest
      return (← mkForallFVars all (toWide concl),
        ← mkLambdaFVars all (mkAppN (mkConst c recUs) (coreFront ++ rest)))
    if coreIsProp[q]! then
      addDecl (.thmDecl { name := w, levelParams := recLps, type, value })
    else
      addDef w recLps type value (compile := false)
      -- compiled where what it is over is, so that a use of it runs
      unless isNoncomputable (← getEnv) c do
        try compileDecl (.defnDecl (← getConstInfoDefn w)) (logErrors := false) catch _ => pure ()
    markElabAsElim w
  let wideNames := dataFirst.filterMap fun q => coreAt[q]!.map (·.2)
  unless trips.isEmpty do
    addTripRules np trips wideNames #[] joints
  -- the rules, for a conclusion the kernel will not take as it stands
  let mut rules : Array Name := #[]
  for q in dataFirst do
    let some (_, w) := coreAt[q]! | continue
    for i in *...oldMin.size do
      let hd ← forallTelescope (← inferType oldMin[i]!) fun _ c => pure c.getAppFn
      unless hd == oldMot[q]! do continue
      let r := ruleNameOf w (← oldMin[i]!.fvarId!.getUserName)
      if (← getEnv).contains r then rules := rules.push r
  let simpThms ← rules.foldlM (init := ({} : SimpTheorems)) fun s r => s.addConst r
  -- each side to its normal form by the rules alone, so that nothing is rewritten in
  -- a proposition and no axiom is used; that the two forms agree is the kernel's to say
  let proveEq (a b : Expr) : MetaM Expr := withCanUnfoldPred (fun cfg info => do
      if joints.contains info.name then return false
      canUnfoldDefault cfg info) do
    let ctx ← Simp.mkContext (simpTheorems := #[simpThms])
      (congrTheorems := ← getSimpCongrTheorems)
    let (ra, _) ← simp a ctx
    let (rb, _) ← simp b ctx
    mkEqTrans (← ra.getProof) (← mkEqSymm (← rb.getProof))
  -- the widened recursion at a value of a member
  let callAt (x : Expr) : MetaM Expr := do
    let some (t, idx) ← targetOf (← inferType x) | throwError "no recursion at{indentExpr x}"
    let w ← match t with
      | .peeled k => pure (peeled[k]! ++ `rec)
      | .core q =>
        let some (_, w) := coreAt[q]! | throwError "no recursion at{indentExpr x}"
        pure w
    return mkAppN (mkConst w recUs) (front ++ idx.push x)
  for k in order₀ do
    let m := peeled[k]!
    let ii := infos[k]!
    let kr ← getConstInfoRec (aliasIndName m ++ `rec)
    let group := ii.all.toArray.filterMap fun n => peeled.findIdx? (aliasIndName · == n)
    let (type, value) ← forallTelescope (← idxTy k) fun idx _ => do
      withNewBinderInfos (idx.map (·.fvarId!, BinderInfo.implicit)) do
      withLocalDeclD `t (mkAppN (pub k) (ps ++ idx)) fun t => do
        let concl ← motiveApp motives (.peeled k) idx callAt t
        let elim := if kr.levelParams.length == ii.levelParams.length + 1 then
            [if peeledIsProp[k]! then Level.zero else elimU] else []
        let kUs := elim ++ ii.levelParams.map Level.param
        let mut e := mkAppN (mkConst kr.name kUs) ps
        for gm in group do
          let ty ← whnf (← inferType e)
          let .forallE _ mty _ _ := ty | throwError "`{kr.name}` takes fewer motives"
          let mot ← forallTelescope mty fun zs _ => do
            mkLambdaFVars zs (← motiveApp motives (.peeled gm) zs.pop callAt zs.back!)
          e := mkApp e mot
        for gm in group do
          for c in infos[gm]!.ctors do
            let ty ← whnf (← inferType e)
            let .forallE _ mty _ _ := ty | throwError "`{kr.name}` takes fewer minors"
            let q := minorCtor.idxOf (Name.str peeled[gm]! c.getString!)
            let nf := (← getConstInfoCtor c).numFields
            let minor ← forallTelescope mty fun zs want => do
              let fields := zs.extract 0 nf
              let kihs := zs.extract nf zs.size
              let mut taken := 0
              let mut ihs : Array Expr := #[]
              for x in fields do
                let ih? ← forallTelescope (← inferType x) fun ys body => do
                  let some (j, _) ← targetOf body | return none
                  return some (j, ← mkLambdaFVars ys (← callAt (mkAppN x ys)))
                let some (j, v) := ih? | continue
                if let .peeled r := j then
                  if group.contains r then
                    ihs := ihs.push kihs[taken]!
                    taken := taken + 1
                    continue
                ihs := ihs.push v
              let app := mkAppN minors[q]! (fields ++ ihs)
              -- what the minor concludes, carried to what the kernel asks for at
              -- each value that differs
              let want := (← instantiateMVars want).headBeta
              let got := (← instantiateMVars (← inferType app)).headBeta
              let mut cur := app
              let mut args := got.getAppArgs
              let wantArgs := want.getAppArgs
              for p in *...args.size do
                let a := args[p]!
                let b := wantArgs[p]!
                if a == b then continue
                let same ← ofExceptKernelException
                  (Kernel.isDefEq (← getEnv) (← getLCtx) a b)
                if same then continue
                let h ← proveEq a b
                let mot ← withLocalDeclD `v (← inferType a) fun v =>
                  mkLambdaFVars #[v] (mkAppN got.getAppFn (args.set! p v))
                cur ← mkEqNDRec mot cur h
                args := args.set! p b
              mkLambdaFVars zs cur
            e := mkApp e minor
        let app := mkAppN e (idx.push t)
        let all := front ++ idx ++ #[t]
        return (← mkForallFVars all concl, ← mkLambdaFVars all app)
    if peeledIsProp[k]! then
      addDecl (.thmDecl { name := m ++ `rec, levelParams := recLps, type, value })
    else
      addDef (m ++ `rec) recLps type value (compile := false)
    markElabAsElim (m ++ `rec)

/--
The same for a block that came apart into data the kernel denested and whatever else
(`T.node : List T → T` beside `Ok : T → Prop`): the kernel's recursion over the data,
`X.rec_k` included, is the recursion the others are put back into. `groups` are the
components as declared, the denested data first, indexing `members`. -/
def addWidenedOverNested (np : Nat) (members : Array Name) (groups : Array (Array Nat)) :
    TermElabM Unit := do
  let isPropM ← members.mapM fun m => do
    forallTelescope (← getConstInfo m).type fun _ s => pure s.isProp
  let data := groups[0]!
  unless data.all (!isPropM[·]!) do
    throwError "not data the kernel denested first"
  unless (← getConstInfoInduct (aliasIndName members[data[0]!]!)).isNested do
    throwError "the data was not denested"
  let mut cores : Array (Name × Name) := #[]
  for i in data do
    let m := members[i]!
    restate (aliasIndName m ++ `rec) (Name.mkStr m "_core_rec")
    cores := cores.push (Name.mkStr m "_core_rec", m ++ `rec)
  let first := members[data[0]!]!
  let mut k := 1
  while (← getEnv).contains (Name.mkStr (aliasIndName first) s!"rec_{k}") do
    restate (Name.mkStr (aliasIndName first) s!"rec_{k}") (Name.mkStr first s!"_core_rec_{k}")
    cores := cores.push (Name.mkStr first s!"_core_rec_{k}", Name.mkStr first s!"rec_{k}")
    k := k + 1
  let rest := (groups.extract 1 groups.size).flatMap id
  addWidenedRecs np members cores (rest.map (members[·]!))
    (Array.range rest.size) #[] #[]

/-! ## A block that came apart, nested over an earlier component

`A.mk (x : List B)` beside `B`: `B` is declared first, and to `A`'s component `List B`
is an ordinary type, so the kernel denests nothing.  The block is still owed a motive
at `List B`, and it has the recursion to fill it with: `List.rec` at `B`, a hypothesis
at a field of type `B` being `B`'s own recursion.  So the nested targets are components
like any other, each with a kernel recursor already in the environment. -/

/-- A target of a block that came apart. -/
private structure ExtTarget where
  /-- The type former at the block's parameters: `A ps` or `List B`. -/
  app : Expr
  /-- What its recursion is called. -/
  recName : Name
  info : InductiveVal
  /-- The inductive's parameters, as the kernel's recursor takes them. -/
  kparams : Array Expr
  /-- The levels of the kernel's constants. -/
  us : List Level
  /-- Its constructors, at the kernel's name and as the writer reads them, at `kparams`. -/
  ctors : Array (Name × Expr)
  isProp : Bool
  deriving Inhabited

/-- The inductive application `ty` nests a member in, as the kernel would take it. -/
private def externalAt (members : Array Name) (ps : Array Expr) (ty : Expr) :
    MetaM (Option (Name × List Level × Array Expr)) := do
  forallTelescope ty fun ys t => do
    let t ← instantiateMVars t
    let .const i us := t.getAppFn | return none
    if members.any (fun m => m == i || aliasIndName m == i) then return none
    let some (.inductInfo info) := (← getEnv).find? i | return none
    let args := t.getAppArgs.extract 0 info.numParams
    unless args.any (fun a => members.any fun m =>
        (a.find? fun e => e.isConstOf m || e.isConstOf (aliasIndName m)).isSome) do return none
    -- at a field or an index of its own: not this construction's to state
    if args.any (fun a => (a.find? fun e => e.isFVar && !ps.contains e).isSome) then
      throwError "a nesting at a local"
    let _ := ys
    return some (i, us, args)

/--
Whether the block `members`, its components declared as aliased inductives, is nested
over an earlier component: some field of a member at an inductive that is no member,
applied to one. -/
def nestsOverComponent (members : Array Name) : MetaM Bool := do
  let infos ← members.mapM fun m => getConstInfoInduct (aliasIndName m)
  let np := infos.foldl (fun a i => min a i.numParams) infos[0]!.numParams
  forallBoundedTelescope (← getConstInfo members[0]!).type np fun ps _ => do
    for ii in infos do
      for c in ii.ctors do
        let ci ← getConstInfo c
        let cty ← instantiateForall ci.type ps
        let hit ← forallTelescope cty fun fs _ => do
          for f in fs do
            if ((← externalAt members ps (← inferType f)).isSome) then return true
          return false
        if hit then return true
    return false

/--
`X.rec` and `X.rec_k` for a block whose components were declared as aliased inductives,
where a member nests over an earlier component (see above). -/
def addJointRecsOverComponents (members : Array Name) : TermElabM Unit := do
  let infos ← members.mapM fun m => getConstInfoInduct (aliasIndName m)
  if infos.any (·.isNested) then throwError "a component the kernel denested"
  let np := infos.foldl (fun a i => min a i.numParams) infos[0]!.numParams
  if infos.any (·.numParams != np) then
    throwError "a component took one of the block's indices as a parameter"
  let mut lps : List Name := []
  for i in infos do
    for l in i.levelParams do
      unless lps.contains l do lps := lps ++ [l]
  let elimName := elimLevelName lps
  let u := Level.param elimName
  let recLps := elimName :: lps
  let recUs := recLps.map Level.param
  forallBoundedTelescope (← getConstInfo members[0]!).type np fun ps _ => do
  -- the members, then what they nest, in the order met: an inductive of a mutual
  -- block brings that block's others with it
  let isPropOf (ty : Expr) : MetaM Bool := forallTelescope ty fun _ s => pure s.isProp
  let mut targets : Array ExtTarget := #[]
  for k in *...members.size do
    let ii := infos[k]!
    let us := ii.levelParams.map Level.param
    targets := targets.push
      { app := mkAppN (mkConst members[k]! us) ps, recName := members[k]! ++ `rec, info := ii,
        kparams := ps, us
        ctors := ii.ctors.toArray.map fun c =>
          (c, mkAppN (mkConst (Name.str members[k]! c.getString!) us) ps)
        isProp := ← isPropOf (← instantiateForall ii.type ps) }
  let scan (t : ExtTarget) : MetaM (Array (Name × List Level × Array Expr)) := do
    let mut out := #[]
    for (c, _) in t.ctors do
      let cty ← instantiateForall ((← getConstInfo c).instantiateTypeLevelParams t.us) t.kparams
      out := out ++ (← forallTelescope cty fun fs _ => do
        let mut acc := #[]
        for f in fs do
          if let some e ← externalAt members ps (← inferType f) then acc := acc.push e
        return acc)
    return out
  let mut nExt := 0
  let mut i := 0
  let mut todo : Array Nat := (Array.range members.size).filter (!targets[·]!.isProp) ++
    (Array.range members.size).filter (targets[·]!.isProp)
  while i < todo.size do
    let t := targets[todo[i]!]!
    i := i + 1
    for (n, us, args) in ← scan t do
      let app := mkAppN (.const n us) args
      if targets.any (·.app == app) then continue
      let ii ← getConstInfoInduct n
      if ii.isNested then throwError "`{n}` is itself nested"
      for j in ii.all do
        let jj ← getConstInfoInduct j
        nExt := nExt + 1
        todo := todo.push targets.size
        targets := targets.push
          { app := mkAppN (.const j us) args
            recName := Name.mkStr members[0]! s!"rec_{nExt}", info := jj, kparams := args, us
            ctors := jj.ctors.toArray.map fun c => (c, mkAppN (.const c us) args)
            isProp := ← isPropOf
              (← instantiateForall (jj.type.instantiateLevelParams jj.levelParams us) args) }
  let idxTy (t : ExtTarget) : MetaM Expr :=
    instantiateForall (t.info.type.instantiateLevelParams t.info.levelParams t.us) t.kparams
  -- the target a type is at, and its indices
  let targetOf (ty : Expr) : MetaM (Option (Nat × Array Expr)) := do
    let ty ← instantiateMVars ty
    let .const n _ := ty.getAppFn | return none
    for q in *...targets.size do
      let t := targets[q]!
      let hd := t.app.getAppFn.constName!
      unless n == hd || n == t.info.name do continue
      let np' := t.kparams.size
      unless ty.getAppNumArgs ≥ np' do continue
      let here := mkAppN (mkConst hd t.us) (ty.getAppArgs.extract 0 np')
      if here == t.app || (← isDefEq here t.app) then
        return some (q, ty.getAppArgs.extract np' ty.getAppNumArgs)
    return none
  -- which of a target's indices its motive shows a value at
  let shownOf ← targets.mapM fun t => do
    forallTelescope (← idxTy t) fun idx _ => idx.mapM fun x => do
      unless t.isProp do return false
      let some (j, _) ← targetOf (← inferType x) | return false
      return !targets[j]!.isProp
  -- the order: as written, a proposition after the data it shows
  let deps ← (Array.range targets.size).mapM fun q => do
    let t := targets[q]!
    forallTelescope (← idxTy t) fun idx _ => do
      let mut out : Array Nat := #[]
      for x in idx do
        if let some (j, _) ← targetOf (← inferType x) then
          if t.isProp && !targets[j]!.isProp then out := out.push j
      return out
  let mut order : Array Nat := #[]
  while order.size < targets.size do
    let mut next := none
    for q in *...targets.size do
      if !order.contains q && deps[q]!.all order.contains then
        next := some q
        break
    let some q := next | throwError "no order of the targets settles their motives"
    order := order.push q
  let pos (q : Nat) : Nat := (order.idxOf? q).getD 0
  let sortOf (t : ExtTarget) : Expr := if t.isProp then mkSort .zero else mkSort u
  let motiveApp (motives : Array Expr) (q : Nat) (idx : Array Expr)
      (value : Expr → MetaM Expr) (major : Expr) : MetaM Expr := do
    let mut out := #[]
    for j in *...idx.size do
      out := out.push idx[j]!
      if shownOf[q]![j]?.getD false then out := out.push (← value idx[j]!)
    return mkAppN motives[pos q]! (out.push major)
  let motiveDecls : Array (Name × BinderInfo × (Array Expr → TermElabM Expr)) :=
    order.mapIdx fun at_ q => (Name.mkSimple s!"motive_{at_ + 1}", BinderInfo.implicit,
    fun (prev : Array Expr) => do
      let t := targets[q]!
      forallTelescope (← idxTy t) fun idx _ => do
        let mut decls : Array (Nat × Expr) := #[]
        for j in *...idx.size do
          if shownOf[q]![j]! then
            let some (r, args) ← targetOf (← inferType idx[j]!) | throwError "no target"
            decls := decls.push (j, mkAppN prev[pos r]! (args.push idx[j]!))
        let v ← mkFreshUserName `v
        withLocalDeclsD (decls.map fun (_, ty) => (v, fun _ => pure ty)) fun vs => do
        withLocalDeclD `t (mkAppN t.app idx) fun x => do
          let mut binders := #[]
          for j in *...idx.size do
            binders := binders.push idx[j]!
            if let some r := decls.findIdx? (·.1 == j) then binders := binders.push vs[r]!
          mkForallFVars (binders.push x) (sortOf t))
  withLocalDecls motiveDecls fun motives => do
  -- the minors, in target order
  let mut minorOf : Array (Nat × Nat) := #[]
  for q in order do
    for c in *...targets[q]!.ctors.size do
      minorOf := minorOf.push (q, c)
  let ctorHead (q c : Nat) : Name := targets[q]!.ctors[c]!.2.getAppFn.constName!
  let minorCtor := minorOf.map fun (q, c) => ctorHead q c
  let minorDecls : Array (Name × BinderInfo × (Array Expr → TermElabM Expr)) :=
    minorOf.map fun (q, c) =>
      (Name.mkSimple (ctorHead q c).getString!, BinderInfo.default, fun (prev : Array Expr) => do
        let t := targets[q]!
        let pubC := t.ctors[c]!.2
        forallTelescope (← inferType pubC) fun fs res => do
          let rec bind (i : Nat) (hyps : Array (Expr × Expr)) : TermElabM Expr := do
            if h : i < fs.size then
              let x := fs[i]
              let ihTy? ← forallTelescope (← inferType x) fun ys body => do
                let some (j, idx) ← targetOf body | return none
                return some (← mkForallFVars ys
                  (← motiveApp motives j idx (wideValueOf np minorCtor prev hyps) (mkAppN x ys)))
              match ihTy? with
              | none => bind (i + 1) hyps
              | some ty =>
                withLocalDeclD ((← x.fvarId!.getUserName).appendAfter "_ih") ty fun ih =>
                  bind (i + 1) (hyps.push (x, ih))
            else
              let idx := res.getAppArgs.extract t.kparams.size res.getAppNumArgs
              let body ← motiveApp motives q idx (wideValueOf np minorCtor prev hyps)
                (mkAppN pubC fs)
              mkForallFVars (fs ++ hyps.map (·.2)) body
          bind 0 #[])
  withLocalDecls minorDecls fun minors => do
  let front := ps ++ motives ++ minors
  -- the recursion at a value of a target
  let callAt (x : Expr) : MetaM Expr := do
    let some (q, idx) ← targetOf (← inferType x) | throwError "no recursion at{indentExpr x}"
    return mkAppN (mkConst targets[q]!.recName recUs) (front ++ idx.push x)
  -- what a target's recursion calls outside its own mutual group
  let groupOf (q : Nat) : Array Nat := (Array.range targets.size).filter fun r =>
    targets[q]!.info.all == targets[r]!.info.all && targets[q]!.kparams == targets[r]!.kparams
  let callsOf ← (Array.range targets.size).mapM fun q => do
    let t := targets[q]!
    let mut out := deps[q]!
    for (_, pubC) in t.ctors do
      out := out ++ (← forallTelescope (← inferType pubC) fun fs _ => do
        let mut acc : Array Nat := #[]
        for f in fs do
          if let some (j, _) ← forallTelescope (← inferType f) fun _ b => targetOf b then
            acc := acc.push j
        return acc)
    return out
  let mut done : Array Nat := #[]
  while done.size < targets.size do
    let mut ready : Option Nat := none
    for q in *...targets.size do
      if done.contains q then continue
      let g := groupOf q
      if g.all fun r => callsOf[r]!.all fun c => g.contains c || done.contains c then
        ready := some q
        break
    let some q0 := ready | throwError "the targets' recursions call each other across components"
    let group := groupOf q0
    for q in group do
      let t := targets[q]!
      let kr ← getConstInfoRec (t.info.name ++ `rec)
      let (type, value) ← forallTelescope (← idxTy t) fun idx _ => do
        withNewBinderInfos (idx.map (·.fvarId!, BinderInfo.implicit)) do
        withLocalDeclD `t (mkAppN t.app idx) fun x => do
          let concl ← motiveApp motives q idx callAt x
          let elim := if kr.levelParams.length == t.info.levelParams.length + 1 then
              [if t.isProp then Level.zero else u] else []
          let mut e := mkAppN (mkConst kr.name (elim ++ t.us)) t.kparams
          for gm in group do
            let ty ← whnf (← inferType e)
            let .forallE _ mty _ _ := ty | throwError "`{kr.name}` takes fewer motives"
            let mot ← forallTelescope mty fun zs _ => do
              mkLambdaFVars zs (← motiveApp motives gm zs.pop callAt zs.back!)
            e := mkApp e mot
          for gm in group do
            for c in *...targets[gm]!.ctors.size do
              let ty ← whnf (← inferType e)
              let .forallE _ mty _ _ := ty | throwError "`{kr.name}` takes fewer minors"
              let mq := (minorOf.findIdx? (· == (gm, c))).getD 0
              let nf := (← getConstInfoCtor targets[gm]!.ctors[c]!.1).numFields
              let minor ← forallTelescope mty fun zs _ => do
                let fields := zs.extract 0 nf
                let kihs := zs.extract nf zs.size
                let mut taken := 0
                let mut ihs : Array Expr := #[]
                for f in fields do
                  let ih? ← forallTelescope (← inferType f) fun ys body => do
                    let some (j, _) ← targetOf body | return none
                    return some (j, ← mkLambdaFVars ys (← callAt (mkAppN f ys)))
                  let some (j, v) := ih? | continue
                  if group.contains j then
                    ihs := ihs.push kihs[taken]!
                    taken := taken + 1
                  else ihs := ihs.push v
                mkLambdaFVars zs (mkAppN minors[mq]! (fields ++ ihs))
              e := mkApp e minor
          let all := front ++ idx ++ #[x]
          return (← mkForallFVars all concl, ← mkLambdaFVars all (mkAppN e (idx.push x)))
      if t.isProp then
        addDecl (.thmDecl { name := t.recName, levelParams := recLps, type, value })
      else
        addDef t.recName recLps type value (compile := false)
      markElabAsElim t.recName
    done := done ++ group

/-- A member that left, its kernel recursion under the writer's names. -/
def restateKernelRec (m : Name) (to : Name) : TermElabM Unit := do
  restate (aliasIndName m ++ `rec) to
  markElabAsElim to

/-! ## Equations of a definition over a member

A `match` on a viewed member goes through `X.view`, and at a constructor with a
copy-typed field `X.view` is not definitionally its value: the field comes back through
a round trip.  Left alone, Lean's equation generator keeps what it could not settle:

```
size.eq_1 : ∀ cs a, (T.node cs a).view = T.View.node cs a → size (T.node cs a) = 1 + sizes cs
```

which names an internal and stops `simp [size]` and `rw [size]` at the constructor.  The
view's rule at a constructor (`X.view_c`) is a theorem, so the hypothesis can be
discharged, and that is all this does: the statements are Lean's own (`mkEqnTypes`) with
such hypotheses dropped and a lowered member's constructors read under the writer's
names, and each proof is Lean's own (`mkEqnProof`) at the view's rule.  A definition with
nothing of this to settle is left to Lean, as is one where anything here does not go
through: the worst this can do is what Lean would have done. -/

/-- `X.view` at each constructor: `X.view_c`, for a block some of whose rules have no
`rfl`.  By the case split's rule where it has one, and by `rfl` where it does not, so
that `simp` can settle a `match` on any constructor of the member and not only the ones
with a copy-typed field. -/
def addViewRules (numParams : Nat) (mem : Name) (ctors : Array Name) : TermElabM Unit := do
  let viewN := viewFnName mem
  let some (.defnInfo info) := (← getEnv).find? viewN | return
  let vlvls := info.levelParams.map Level.param
  for c in ctors do
    let rule := ruleNameOf (mem ++ `casesOn) (Name.mkSimple c.getString!)
    let name := Name.mkStr mem s!"view_{c.getString!}"
    let cIdx := ctors.idxOf c
    discard <| attempt? `Mumi m!"no rule of `{viewN}` at `{c}`" do
      lambdaTelescope info.value fun xs body => do
        let .const elim us := body.getAppFn | throwError "`{viewN}` is not a case split"
        let bargs := body.getAppArgs
        let ps := xs.extract 0 numParams
        let nIdx := xs.size - numParams - 1
        let front := bargs.extract 0 (numParams + 1 + ctors.size)
        let elimInfo ← getConstInfo elim
        -- the minor premise's type says what the constructor is at its fields
        let afterMotive ← instantiateForall (elimInfo.instantiateTypeLevelParams us)
          (bargs.extract 0 (numParams + 1))
        let some minorTy ← (do
            let mut ty := afterMotive
            let mut out := none
            for q in *...ctors.size do
              let .forallE _ d b _ ← whnf ty | break
              if q == cIdx then out := some d
              ty := b.instantiate1 bargs[numParams + 1 + q]!
            return out) | throwError "`{elim}` has no minor at `{c}`"
        let (type, value) ← forallTelescope minorTy fun fs concl => do
          let cargs := concl.headBeta.getAppArgs
          let at_ := cargs.extract (cargs.size - nIdx - 1) cargs.size
          let vl := mkAppN (mkConst viewN vlvls) (ps ++ at_)
          let rhs := (mkAppN bargs[numParams + 1 + cIdx]! fs).headBeta
          let all := ps ++ fs
          let proof ← if (← getEnv).contains rule then pure (mkAppN (mkConst rule us) (front ++ fs))
            else mkEqRefl vl
          return (← mkForallFVars all (← mkEq vl rhs), ← mkLambdaFVars all proof)
        addDecl (.thmDecl { name, levelParams := info.levelParams, type, value })
        let simpAttr ← ofExcept <| getAttributeImpl (← getEnv) `simp
        simpAttr.add name default .global

/-- Whether `e` names a view function, or a constructor of a member behind an alias. -/
private def namesViewOrAlias (env : Environment) (e : Expr) : Bool :=
  (e.find? fun x => match x with
    | .const n _ =>
      (match n with
        | .str p "view" => (viewedMembers env).contains p
        | _ => false) || (publicName? env n).isSome
    | _ => false).isSome

/-- A proof of `(X.c …).view = X.View.c …`, a hypothesis Lean's generator left, if it is one. -/
private def viewRuleProof? (ty : Expr) : MetaM (Option Expr) := do
  let some (_, lhs, rhs) := ty.eq? | return none
  let .const (.str mem "view") _ := lhs.getAppFn | return none
  unless (viewedMembers (← getEnv)).contains mem do return none
  let .const (.str _ c) _ := rhs.getAppFn | return none
  let rule := Name.mkStr mem s!"view_{c}"
  if (← getEnv).contains rule then
    let thm ← mkConstWithFreshMVarLevels rule
    let (ms, _, concl) ← forallMetaTelescope (← inferType thm)
    if ← isDefEq concl ty then
      return some (← instantiateMVars (mkAppN thm ms))
    return none
  -- a constructor with no copy-typed field holds by `rfl`
  let refl ← mkEqRefl lhs
  return if ← isDefEq lhs rhs then some refl else none

/-- Whether `ty` is `x.view ≍ …` or `x.view = …`: a premise a side condition has only
because the `match` went through the view. -/
private def isViewPremise (ty : Expr) : MetaM Bool := do
  let lhs? : Option Expr :=
    if ty.isAppOfArity ``Eq 3 then some ty.appFn!.appArg!
    else if ty.isAppOfArity ``HEq 4 then some ty.appFn!.appFn!.appArg!
    else none
  let some lhs := lhs? | return false
  let .const (.str mem "view") _ := lhs.getAppFn | return false
  return (viewedMembers (← getEnv)).contains mem

/-- A side condition ending in `False`, its view premises taken out: what it says of the
fields is all a reader has to prove, and the original follows by ignoring the rest. -/
private def tidySideCondition? (ty : Expr) : MetaM (Option Expr) := do
  forallTelescope ty fun ys concl => do
    unless concl.isFalse do return none
    let mut kept : Array Expr := #[]
    for y in ys do
      unless ← isViewPremise (← inferType y) do kept := kept.push y
    if kept.size == ys.size then return none
    -- a view premise nothing else may mention
    for k in kept do
      for y in ys do
        if !kept.contains y && (← inferType k).containsFVar y.fvarId! then return none
    return some (← mkForallFVars kept concl)

/-- The original side condition `ty`, out of a proof `h` of the tidied one. -/
private def sideConditionFrom (ty h : Expr) : MetaM Expr := do
  forallTelescope ty fun ys _ => do
    let mut kept : Array Expr := #[]
    for y in ys do
      unless ← isViewPremise (← inferType y) do kept := kept.push y
    mkLambdaFVars ys (mkAppN h kept)

/-- A statement of Lean's generator and its proof, tidied; `none` if there is nothing to
tidy, or it cannot be done. -/
private def tidyEqn (type cond : Expr) : MetaM (Option (Expr × Expr)) := do
  forallTelescope type fun xs body => do
    -- for each binder, what discharges it, or the statement it keeps
    let mut decls : Array (Name × BinderInfo × Expr) := #[]
    let mut proofs : Array (Option Expr) := #[]
    let mut tidied : Array Bool := #[]
    let mut changed := false
    for x in xs do
      let ty ← instantiateMVars (← inferType x)
      if let some p ← viewRuleProof? ty then
        proofs := proofs.push (some (← instantiateMVars p))
        tidied := tidied.push false
        changed := true
        continue
      proofs := proofs.push none
      let d ← x.fvarId!.getDecl
      if let some ty' ← tidySideCondition? ty then
        decls := decls.push (d.userName, d.binderInfo, ty')
        tidied := tidied.push true
        changed := true
      else
        decls := decls.push (d.userName, d.binderInfo, ty)
        tidied := tidied.push false
    let body' ← publicize body
    unless changed || body' != body do return none
    let keptX := (Array.range xs.size).filterMap fun i =>
      if proofs[i]!.isNone then some xs[i]! else none
    let droppedX := (Array.range xs.size).filterMap fun i =>
      if proofs[i]!.isSome then some xs[i]! else none
    let names (e : Expr) := droppedX.any fun d => e.containsFVar d.fvarId!
    if names body' || decls.any (fun (_, _, t) => names t) then return none
    -- the same binders over themselves: a later one's statement names an earlier
    let newLocals : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
      decls.map fun (n, bi, t) =>
        (n, bi, fun prev => pure (t.replaceFVars (keptX.extract 0 prev.size) prev))
    withLocalDecls newLocals fun ys => do
      let mut args : Array Expr := #[]
      let mut q := 0
      for i in *...xs.size do
        if let some p := proofs[i]! then
          args := args.push (p.replaceFVars keptX ys)
        else
          let ty := (← inferType xs[i]!).replaceFVars keptX ys
          let v ← if tidied[i]! then sideConditionFrom ty ys[q]! else pure ys[q]!
          args := args.push v
          q := q + 1
      return some (← mkForallFVars ys (body'.replaceFVars keptX ys),
        ← mkLambdaFVars ys (mkAppN cond args))

/-- The equations of `declName`, where there is something of ours to settle in them. -/
private def mumiEqns (declName : Name) : MetaM (Option (Array Name)) := do
  let some (.defnInfo info) := (← getEnv).find? declName | return none
  unless backward.eqns.nonrecursive.get (← getOptions) || (← isRecursiveDefinition declName) do
    return none
  try
    withOptions (tactic.hygienic.set · false) do
    let target ← Lean.Elab.Eqns.unfoldThmType declName
    -- a lowered member's constructors are in the `match`'s own type, not the definition's
    let env ← getEnv
    let aliased := target.getUsedConstants.any fun n => Id.run do
      unless (Lean.Meta.Match.Extension.getMatcherInfo? env n).isSome do return false
      let some ci := env.find? n | return false
      return namesViewOrAlias env ci.type
    unless namesViewOrAlias env target || aliased do return none
    let declNames := if ← isRecursiveDefinition declName then info.all.toArray else #[]
    let types ← withNewMCtxDepth <|
      forallTelescope (cleanupAnnotations := true) target fun _ target => do
        let goal ← mkFreshExprSyntheticOpaqueMVar target
        withReducible do Lean.Elab.Eqns.mkEqnTypes declNames goal.mvarId!
    -- proved before anything is declared, so that a failure leaves it all to Lean
    let mut decls : Array (Name × Expr × Expr) := #[]
    let mut any := false
    for h : i in *...types.size do
      let name := mkEqLikeNameFor (← getEnv) declName s!"{eqnThmSuffixBasePrefix}{i + 1}"
      let cond ← instantiateMVars (← Lean.Elab.Eqns.mkEqnProof declName types[i])
      -- Lean's own leftovers first, as it would have removed them
      let (t, v) ← Lean.Elab.Eqns.removeUnusedEqnHypotheses types[i] cond
      match ← tidyEqn t v with
      | some (t', v') =>
        any := true
        let (t', v') ← Lean.Elab.Eqns.removeUnusedEqnHypotheses t' (← instantiateMVars v')
        decls := decls.push (name, t', v')
      | none => decls := decls.push (name, t, v)
    unless any do return none
    for (name, type, value) in decls do
      realizeConst declName name do
        addDecl (.thmDecl { name, levelParams := info.levelParams, type, value })
    return some (decls.map (·.1))
  catch ex =>
    trace[Mumi] "the equations of `{declName}` are left to Lean: {ex.toMessageData}"
    return none

initialize registerGetEqnsFn mumiEqns

end Mumi
