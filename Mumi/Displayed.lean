/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Mumi.Public
import Lean.Elab.App

public section

/-!
# One recursion over the data and the proofs of a block

A block whose data members take proofs of its `Prop` members -- `U.pi (a : U)
(b : El a → U) (h : Good a)` beside `Good : U → Prop` -- has, were Lean to
accept it, one recursor over all of it.  Its `Prop` motives are *displayed*:
after each index of data type they take the value the data recursion computed
there, `motive_2 : (a : U) → motive_1 a → Good a → Prop`, and every minor premise
takes a hypothesis at every field, the proofs included:

```lean
pi : (a : U) → (b : El a → U) → (h : Good a) → (a_ih : motive_1 a) →
  (b_ih : (x : El a) → motive_1 (b x)) → motive_2 a a_ih h → motive_1 (U.pi a b h)
```

An encoding that declares the data and the proofs apart has two recursions
instead: one over the data, with no hypothesis at a proof, and one over the
proofs into `Prop`, with none at a datum.  This module builds the joint one out
of those two, whatever the encoding:

* `G x r` -- *`r` is the recursion's value at `x`* -- by the data recursion into
  `M x → Prop`: at a constructor, there are values at the fields `G` relates to
  them and proofs of the displayed motives at the proofs, and `r` is the minor
  premise at all of that;
* `UNIQ`: `G` is functional, by the data recursion into `Prop`;
* `LEM`, by the recursion over the proofs: a displayed motive holds at any
  values `G` relates to the proof's indices.  At a `Prop` constructor, the
  values at its data fields are read off `G` at the indices that name them, which
  the constructor's conclusion does; a field named twice is read once, `UNIQ`
  saying the readings agree;
* `J' x : (r : M x) ×' G x r` by the data recursion, the hypotheses at proofs
  from `LEM`;
* `X.rec := (J' …).1` and `P.rec := LEM` at those values.

All that is said of a proof is in `Prop`, so nothing is chosen and no axiom is
used.  `X.rec` at a constructor unfolds to `J'` there, which the data recursion
reduces to the minor premise at the fields' values: each rule holds by `rfl`
exactly where the data recursion's own do.

What this does not reach, the caller publishing its own eliminators instead
(`publish`): a datum a `Prop` constructor takes without its conclusion naming it
(`Ok.yes (t : T)` beside `T.pi … (h : Ok)`), whose value only a recursion
through the proof computes; a field named twice whose member's recursion is
higher order, where `G` is functional only up to `funext`; and a field named in
a constructor nested inside another index.

Everything is assembled as terms and checked by the kernel alone: the
statements unfold (`G` at a constructor) only definitionally, and for a block
lowered at the universe it is written at, Meta's unifier does not follow that
unfolding in reasonable time.
-/

namespace Mumi.Displayed
open Lean Meta Lean.Elab.MultiuniverseInductive

/-- `k` with the binders of `xs` given the annotation `bi`. -/
private def withInfos {α} (xs : Array Expr) (bi : BinderInfo → BinderInfo) (k : MetaM α) : MetaM α := do
  let infos ← xs.mapM fun x => do return (x.fvarId!, bi (← x.fvarId!.getDecl).binderInfo)
  withNewBinderInfos infos k

/-- A member of the block, as the frontend declared it. -/
structure Member where
  /-- The type former. -/
  name : Name
  prop : Bool
  /-- The constructors, as the writer has them. -/
  ctors : Array Name
  /-- A data member's: the data members whose motives its recursion over the
  data takes, in order. -/
  scope : Array Nat := #[]
  /-- Its recursion, where it is not `X.<internal>rec`: a data member's over the
  data, a `Prop` member's into `Prop` (or any sort) over the `Prop` members of
  its `scope`, all of them when that is empty. -/
  source : Name := .anonymous
  deriving Inhabited

/-- What the block is. -/
structure Input where
  numParams : Nat
  members : Array Member
  /-- What the frontend's own eliminators are called: `X.<internal>rec` and so on. -/
  internal : String
  deriving Inhabited

private def Input.elim (inp : Input) (k : Nat) (s : String) : Name :=
  if s == "rec" && !inp.members[k]!.source.isAnonymous then inp.members[k]!.source
  else inp.members[k]!.name ++ Name.mkSimple (inp.internal ++ s)

/-- The construction cannot be made for this block. -/
private def gap {α} (msg : MessageData) : MetaM α :=
  throwError m!"no joint recursor: {msg}"

/-- What a hypothesis of a minor premise is at: a field of a data member, or a
proof of a `Prop` member. -/
private inductive Kind where
  | data (field member : Nat)
  | proof (field member : Nat)
  deriving Inhabited

private def Kind.field : Kind → Nat
  | .data f _ | .proof f _ => f

private def Kind.member : Kind → Nat
  | .data _ m | .proof _ m => m

private def Kind.isData : Kind → Bool
  | .data .. => true
  | .proof .. => false

/-- The kinds of the hypotheses at fields `fields`, in order. -/
private def kindsOf (inp : Input) (fields : Array Expr) : MetaM (Array Kind) := do
  let mut out := #[]
  for i in [:fields.size] do
    let k? ← forallTelescope (← inferType fields[i]!) fun _ ty => do
      let ty := (← instantiateMVars ty).headBeta
      let .const n _ := ty.getAppFn | return none
      return inp.members.findIdx? (·.name == n)
    if let some k := k? then
      out := out.push (if inp.members[k]!.prop then .proof i k else .data i k)
  return out

/-- The block, with everything the construction is abstracted over bound. -/
private structure Ctx where
  inp : Input
  ps : Array Expr
  /-- The block's universes. -/
  blockLvls : List Name
  /-- The motive's universe. -/
  u : Name
  /-- Members in the recursion's order: as written, a `Prop` one after the data
  its motive displays. -/
  targets : Array Nat
  /-- By target. -/
  motives : Array Expr
  /-- By member, by constructor. -/
  minorOf : Array (Array Expr)
  /-- In the order bound. -/
  minors : Array Expr
  /-- By member, by index: the data member a `Prop` member's index is of. -/
  displayAt : Array (Array (Option Nat))
  /-- The data members with a `UNIQ`. -/
  uniq : Array Nat := #[]

private def Ctx.np (c : Ctx) : Nat := c.inp.numParams
private def Ctx.pre (c : Ctx) : Array Expr := c.ps ++ c.motives ++ c.minors
private def Ctx.lps (c : Ctx) : List Name := c.u :: c.blockLvls
private def Ctx.uLvl (c : Ctx) : Level := mkLevelParam c.u
private def Ctx.motiveOf (c : Ctx) (k : Nat) : Expr := c.motives[(c.targets.idxOf? k).get!]!

/-- An auxiliary constant of member `k`. -/
private def auxName (inp : Input) (k : Nat) (s : String) : Name :=
  inp.members[k]!.name ++ Name.mkSimple ("_joint_" ++ s)

/-- An auxiliary constant at everything the construction is abstracted over. -/
private def Ctx.aux (c : Ctx) (k : Nat) (s : String) : Expr :=
  mkAppN (mkConst (auxName c.inp k s) (c.lps.map mkLevelParam)) c.pre

private def constAt (n : Name) : MetaM Expr := do
  let info ← getConstInfo n
  return mkConst n (info.levelParams.map mkLevelParam)

/-- Member `k` at the parameters and `idx`. -/
private def Ctx.memberAt (c : Ctx) (k : Nat) (idx : Array Expr) : MetaM Expr := do
  return mkAppN (← constAt c.inp.members[k]!.name) (c.ps ++ idx)

/-- The arity of member `k` at the parameters. -/
private def Ctx.arity (c : Ctx) (k : Nat) : MetaM Expr := do
  instantiateForall (← getConstInfo c.inp.members[k]!.name).type c.ps

/-- A motive at index arguments, the values displayed after those that have
one, and a major premise. -/
private def Ctx.motiveApp (c : Ctx) (k : Nat) (args : Array Expr) (vals : Array (Option Expr)) (major : Expr) : Expr :=
  Id.run do
    let mut out := #[]
    for i in [:args.size] do
      out := out.push args[i]!
      if let some (some v) := vals[i]? then out := out.push v
    mkAppN (c.motiveOf k) (out.push major)

/-- Read a displayed motive's arguments back: the index arguments, and the
values after the displayed ones. -/
private def Ctx.splitDisplayed (c : Ctx) (k : Nat) (args : Array Expr) : Array Expr × Array Expr := Id.run do
  let shown := c.displayAt[k]!
  let mut idx := #[]
  let mut vals := #[]
  let mut i := 0
  for a in [:shown.size] do
    idx := idx.push args[i]!
    i := i + 1
    if shown[a]!.isSome then
      vals := vals.push args[i]!
      i := i + 1
  return (idx, vals)

/-- The member and index of constructor `n`, if it is one of the block's. -/
private def ctorOf? (inp : Input) (n : Name) : Option (Nat × Nat) := Id.run do
  for k in [:inp.members.size] do
    if let some ci := inp.members[k]!.ctors.idxOf? n then return some (k, ci)
  return none

/-- Constructor `ci` of member `k` at the parameters and `fields`: its index
arguments and itself. -/
private def Ctx.ctorAt (c : Ctx) (k ci : Nat) (fields : Array Expr) : MetaM (Array Expr × Expr) := do
  let ctor ← constAt c.inp.members[k]!.ctors[ci]!
  let res ← instantiateForall (← inferType ctor) (c.ps ++ fields)
  return (res.getAppArgs.extract c.np res.getAppNumArgs, mkAppN ctor (c.ps ++ fields))

/-- How many fields constructor `ci` of member `k` has. -/
private def Ctx.numFields (c : Ctx) (k ci : Nat) : MetaM Nat := do
  forallTelescope (← getConstInfo c.inp.members[k]!.ctors[ci]!).type fun xs _ => pure (xs.size - c.np)

/-- The recursion's value at `e`, where it can follow it: a field, by its
hypothesis; a constructor of the block, by its minor premise at such values.
As the specification reads it. -/
private partial def valueOf (inp : Input) (minorOf : Array (Array Expr)) (hyps : Array (Expr × Expr))
    (e : Expr) : MetaM (Option Expr) := do
  let e ← instantiateMVars e
  let f := e.getAppFn
  let args := e.getAppArgs
  if f.isFVar then
    return (hyps.find? (·.1 == f)).map fun (_, h) => mkAppN h args
  let .const n _ := f | return none
  let some (k, ci) := ctorOf? inp n | return none
  let some m := (minorOf[k]?).bind (·[ci]?) | return none
  let fieldArgs := args.extract inp.numParams args.size
  let mut v := mkAppN m fieldArgs
  let mut ty ← instantiateForall (← inferType m) fieldArgs
  while ty.isForall do
    let .forallE _ d body _ := ty | break
    let some h ← forallTelescope d fun dom concl => do
        let some val ← valueOf inp minorOf hyps concl.appArg! | return none
        return some (← mkLambdaFVars dom val)
      | return none
    v := mkApp v h
    ty := body.instantiate1 h
  return some v

/-- Bind the parameters, the motives and the minor premises of the joint
recursor, as the block's own would have them. -/
private def withSpec {α} (inp : Input) (k : Ctx → MetaM α) : MetaM α := do
  let mut blockLvls : List Name := []
  for m in inp.members do
    for l in (← getConstInfo m.name).levelParams do
      unless blockLvls.contains l do blockLvls := blockLvls ++ [l]
  let u := ((List.range (blockLvls.length + 1)).map fun i =>
    if i == 0 then `u else Name.mkSimple s!"u_{i}").find? (!blockLvls.contains ·) |>.getD `u
  let info0 ← getConstInfo inp.members[0]!.name
  forallBoundedTelescope info0.type inp.numParams fun ps _ => do
  withInfos ps (fun _ => .implicit) do
  let c0 : Ctx :=
    { inp, ps, blockLvls, u, targets := #[], motives := #[], minorOf := inp.members.map fun _ => #[],
      minors := #[], displayAt := #[] }
  let displayAt ← (Array.range inp.members.size).mapM fun k => do
    if !inp.members[k]!.prop then return #[]
    forallTelescope (← c0.arity k) fun idx _ => idx.mapM fun i => do
      let ty ← instantiateMVars (← inferType i)
      let .const n _ := ty.getAppFn | return none
      return (inp.members.findIdx? (·.name == n)).filter (!inp.members[·]!.prop)
  -- the members as written, a `Prop` one after the data its motive displays
  let mut targets : Array Nat := #[]
  while targets.size < inp.members.size do
    let some q := (Array.range inp.members.size).find? fun q =>
        !targets.contains q && displayAt[q]!.all fun j? => j?.all targets.contains
      | break
    targets := targets.push q
  let c0 := { c0 with displayAt, targets }
  let motiveName (t : Nat) := Name.mkSimple (if targets.size == 1 then "motive" else s!"motive_{t + 1}")
  -- the motives, each over those before it
  let rec motivesFrom (t : Nat) (c : Ctx) (k' : Ctx → MetaM α) : MetaM α := do
    if h : t < targets.size then
      let mk := targets[t]
      let ty ← forallTelescope (← c.arity mk) fun idx _ => do
        let major ← c.memberAt mk idx
        if !inp.members[mk]!.prop then
          withLocalDeclD `t major fun x => mkForallFVars (idx.push x) (mkSort c.uLvl)
        else
          -- after each index of data type, the value there
          let shown ← (Array.range idx.size).filterMapM fun i => do
            let some j := displayAt[mk]![i]! | return none
            let ity ← instantiateMVars (← inferType idx[i]!)
            return some (i, mkAppN (c.motiveOf j) ((ity.getAppArgs.extract inp.numParams ity.getAppNumArgs).push idx[i]!))
          let v ← mkFreshUserName `v
          withLocalDecls (shown.map fun (_, ty) => (v, BinderInfo.default, fun _ => pure ty)) fun vs => do
          withLocalDeclD `t major fun x => do
            let mut binders := #[]
            for i in [:idx.size] do
              binders := binders.push idx[i]!
              if let some n := shown.findIdx? (·.1 == i) then binders := binders.push vs[n]!
            mkForallFVars (binders.push x) (mkSort .zero)
      withLocalDecl (motiveName t) .implicit ty fun m =>
        motivesFrom (t + 1) { c with motives := c.motives.push m } k'
    else k' c
  motivesFrom 0 c0 fun c1 => do
  -- the minor premises, each over those before it
  let order : Array (Nat × Nat) := targets.flatMap fun mk =>
    (Array.range inp.members[mk]!.ctors.size).map (mk, ·)
  let rec minorsFrom (i : Nat) (c : Ctx) (k' : Ctx → MetaM α) : MetaM α := do
    if h : i < order.size then
      let (mk, ci) := order[i]
      let ctor := inp.members[mk]!.ctors[ci]!
      let ty ← forallTelescope (← instantiateForall (← inferType (← constAt ctor)) ps) fun fields _ => do
        let (idx, self) ← c.ctorAt mk ci fields
        let kinds ← kindsOf inp fields
        let rec hypsFrom (j : Nat) (hyps : Array (Expr × Expr)) : MetaM Expr := do
          if h : j < kinds.size then
            let f := fields[kinds[j].field]!
            let hty ← forallTelescope (← inferType f) fun dom fty => do
              let fty := (← instantiateMVars fty).headBeta
              let args := fty.getAppArgs.extract inp.numParams fty.getAppNumArgs
              match kinds[j] with
              | .data _ jm => mkForallFVars dom (mkAppN (c.motiveOf jm) (args.push (mkAppN f dom)))
              | .proof _ jm =>
                let mut vals := #[]
                for a in [:args.size] do
                  if (displayAt[jm]![a]?).join.isSome then
                    let some v ← valueOf inp c.minorOf hyps args[a]!
                      | gap m!"the hypothesis at a proof in `{ctor}`, at {args[a]!}"
                    vals := vals.push (some v)
                  else vals := vals.push none
                mkForallFVars dom (c.motiveApp jm args vals (mkAppN f dom))
            let n := (← f.fvarId!.getDecl).userName.appendAfter "_ih"
            withLocalDeclD n hty fun ih => hypsFrom (j + 1) (hyps.push (f, ih))
          else
            let mut vals := #[]
            if inp.members[mk]!.prop then
              for a in [:idx.size] do
                if (displayAt[mk]![a]?).join.isSome then
                  let some v ← valueOf inp c.minorOf hyps idx[a]!
                    | gap m!"the conclusion of `{ctor}`, at {idx[a]!}"
                  vals := vals.push (some v)
                else vals := vals.push none
            mkForallFVars (fields ++ hyps.map (·.2)) (c.motiveApp mk idx vals self)
        hypsFrom 0 #[]
      withLocalDeclD (Name.mkSimple ctor.getString!) ty fun m =>
        minorsFrom (i + 1) { c with minorOf := c.minorOf.modify mk (·.push m), minors := c.minors.push m } k'
    else k' c
  minorsFrom 0 c1 k

/-! ## Terms by hand -/

private def mkExists (α p : Expr) : MetaM Expr := do
  return mkApp2 (mkConst ``Exists [← getLevel α]) α p

/-- `@Eq.ndrec α a motive h b e : motive b`, into `Prop`. -/
private def ndrec (α a motive h b e : Expr) : MetaM Expr := do
  return mkAppN (mkConst ``Eq.ndrec [.zero, ← getLevel α]) #[α, a, motive, h, b, e]

/-- What a datum's value is to satisfy: `G` at each point of its domain.  `d` is
the hypothesis' type, `∀ dom, M args (f dom)`. -/
private def factAt (c : Ctx) (j : Nat) (d x : Expr) : MetaM Expr :=
  forallTelescope d fun dom body => do
    let args := body.getAppArgs
    mkForallFVars dom (mkAppN (c.aux j "G") (args ++ #[mkAppN x dom]))

/-- From the hypothesis `ty` of minor premise `m` at `fields` on, with values
`acc` given to the ones before: `∃ x, fact x ∧ …` at a datum, `∃ p, …` at a
proof, and at the end `r = m fields acc`. -/
private partial def stmtFrom (c : Ctx) (m : Expr) (fields : Array Expr) (r : Expr)
    (ty : Expr) (ks : List Kind) (acc : Array Expr) : MetaM Expr := do
  match ks with
  | [] => mkEq r (mkAppN m (fields ++ acc))
  | kd :: ks =>
    let .forallE n d body _ := ty | throwError "a minor premise ended early"
    withLocalDeclD n d fun x => do
      let rest ← stmtFrom c m fields r (body.instantiate1 x) ks (acc.push x)
      let inner ← if kd.isData then pure (mkAnd (← factAt c kd.member d x) rest) else pure rest
      mkExists d (← mkLambdaFVars #[x] inner)

/-- `G` at a constructor of the data, unfolded: the statement minor premise `m`
at `fields` makes of `r`. -/
private def graphStmt (c : Ctx) (m : Expr) (fields : Array Expr) (r : Expr) : MetaM Expr := do
  stmtFrom c m fields r (← instantiateForall (← inferType m) fields) (← kindsOf c.inp fields).toList #[]

/-- The predicate an existential of `stmtFrom` is over, at its first hypothesis. -/
private def predAt (c : Ctx) (m : Expr) (fields : Array Expr) (r : Expr) (kd : Kind)
    (n : Name) (d body : Expr) (ks : List Kind) (acc : Array Expr) : MetaM Expr :=
  withLocalDeclD n d fun x => do
    let rest ← stmtFrom c m fields r (body.instantiate1 x) ks (acc.push x)
    if kd.isData then mkLambdaFVars #[x] (mkAnd (← factAt c kd.member d x) rest)
    else mkLambdaFVars #[x] rest

/-- A proof of `stmtFrom … ty ks acc`, each hypothesis' value, and at a datum
the proof of its fact, given by `supply`. -/
private partial def introFrom (c : Ctx) (m : Expr) (fields : Array Expr) (r : Expr)
    (supply : Kind → Expr → MetaM (Expr × Option Expr)) (ty : Expr) (ks : List Kind) (acc : Array Expr) :
    MetaM Expr := do
  match ks with
  | [] =>
    let rty ← inferType r
    return mkApp2 (mkConst ``Eq.refl [← getLevel rty]) rty r
  | kd :: ks' =>
    let .forallE n d body _ := ty | throwError "a minor premise ended early"
    let (w, wf?) ← supply kd d
    let rest ← introFrom c m fields r supply (body.instantiate1 w) ks' (acc.push w)
    let p ← predAt c m fields r kd n d body ks' acc
    let proof ← match kd, wf? with
      | .data .., some wf =>
        let restW ← stmtFrom c m fields r (body.instantiate1 w) ks' (acc.push w)
        pure (mkApp4 (mkConst ``And.intro) (← factAt c kd.member d w) restW wf rest)
      | .data .., none => throwError "a datum without its fact"
      | .proof .., _ => pure rest
    return mkApp4 (mkConst ``Exists.intro [← getLevel d]) d p w proof

/-- Take apart a proof `h` of `stmtFrom … ty ks acc` in a proof of `goal`.  At a
datum, `hook` may say the value is another already at hand, with an equation
and that one's fact, and the rest is read at it.  `k` gets the values and
proofs, the facts of the data, and the closing equation. -/
private partial def destructFrom (c : Ctx) (m : Expr) (fields : Array Expr) (r : Expr) (goal : Expr)
    (hook : Kind → Expr → Expr → Expr → MetaM (Option (Expr × Expr × Expr)))
    (h : Expr) (ty : Expr) (ks : List Kind) (acc facts : Array Expr)
    (k : Array Expr → Array Expr → Expr → MetaM Expr) : MetaM Expr := do
  match ks with
  | [] => k acc facts h
  | kd :: ks' =>
    let .forallE n d body _ := ty | throwError "a minor premise ended early"
    let p ← predAt c m fields r kd n d body ks' acc
    let cont ← withLocalDeclD n d fun x => do
      let px := (p.bindingBody!.instantiate1 x)
      withLocalDeclD `h px fun hx => do
        let inner ← if kd.isData then do
            let fx ← factAt c kd.member d x
            let restX ← stmtFrom c m fields r (body.instantiate1 x) ks' (acc.push x)
            let fact := mkApp3 (mkConst ``And.left) fx restX hx
            let rest := mkApp3 (mkConst ``And.right) fx restX hx
            match ← hook kd d x fact with
            | none => destructFrom c m fields r goal hook rest (body.instantiate1 x) ks' (acc.push x) (facts.push fact) k
            | some (y, e, fy) =>
              -- the rest, read at the value already at hand
              let mot ← withLocalDeclD n d fun z => do
                mkLambdaFVars #[z] (← stmtFrom c m fields r (body.instantiate1 z) ks' (acc.push z))
              let rest' ← ndrec d x mot rest y e
              destructFrom c m fields r goal hook rest' (body.instantiate1 y) ks' (acc.push y) (facts.push fy) k
          else destructFrom c m fields r goal hook hx (body.instantiate1 x) ks' (acc.push x) facts k
        mkLambdaFVars #[x, hx] inner
    return mkAppN (mkConst ``Exists.elim [← getLevel d]) #[d, p, goal, h, cont]

/-! ## The construction -/

/-- A data member's recursion over the data at an elimination universe. -/
private def Ctx.dataRec (c : Ctx) (k : Nat) (lvl : Level) : MetaM Expr := do
  let info ← getConstInfo (c.inp.elim k "rec")
  let some e := info.levelParams.find? (!c.blockLvls.contains ·)
    | gap m!"`{info.name}` has no universe to eliminate into"
  return mkConst info.name (info.levelParams.map fun n => if n == e then lvl else mkLevelParam n)

/-- The binder types of the `n` minor premises a recursor takes after `args`. -/
private def minorTypes (rec : Expr) (args : Array Expr) (n : Nat) : MetaM (Array Expr) := do
  let mut ty ← instantiateForall (← inferType rec) args
  let mut out := #[]
  for _ in [:n] do
    let .forallE _ d b _ := ty | throwError "the recursor has fewer minor premises than constructors"
    out := out.push d
    ty := b
  return out

/-- A recursion's minor premise as a lambda over the binders its type has: the
fields and the hypotheses. -/
private def minorLambda (minorTy : Expr) (numFields : Nat) (body : Array Expr → Array Expr → MetaM Expr) :
    MetaM Expr :=
  forallTelescope minorTy fun xs _ => do
    mkLambdaFVars xs (← body (xs.extract 0 numFields) (xs.extract numFields xs.size))

/-- `fun idx x => body idx x` over member `k`. -/
private def Ctx.overMember (c : Ctx) (k : Nat) (body : Array Expr → Expr → MetaM Expr) : MetaM Expr := do
  forallTelescope (← c.arity k) fun idx _ => do
    withLocalDeclD `x (← c.memberAt k idx) fun x => do
      mkLambdaFVars (idx.push x) (← body idx x)

/-- `∀ idx x, body idx x` over member `k`. -/
private def Ctx.forallMember (c : Ctx) (k : Nat) (body : Array Expr → Expr → MetaM Expr) : MetaM Expr := do
  forallTelescope (← c.arity k) fun idx _ => do
    withLocalDeclD `x (← c.memberAt k idx) fun x => do
      mkForallFVars (idx.push x) (← body idx x)

/-- A definition or theorem over everything the construction is abstracted over. -/
private def Ctx.add (c : Ctx) (name : Name) (type value : Expr) (thm : Bool) : MetaM Unit := do
  let type ← mkForallFVars c.pre type
  let value ← mkLambdaFVars c.pre value
  if thm then addDecl (.thmDecl { name, levelParams := c.lps, type, value })
  else addDef name c.lps type value (hints := .abbrev)

/-- One recursion of the data, over `scope`, at motives `mots` and with a minor
premise at each constructor built by `minor` from the member, the constructor,
the fields and the hypotheses the recursion gives at those in `scope`. -/
private def Ctx.recursion (c : Ctx) (scope : Array Nat) (lvl : Level) (mots : Array Expr)
    (minor : Nat → Nat → Array Expr → Array Expr → MetaM Expr) : MetaM (Array Expr) := do
  let rec0 ← c.dataRec scope[0]! lvl
  let n := scope.foldl (fun n s => n + c.inp.members[s]!.ctors.size) 0
  let tys ← minorTypes rec0 (c.ps ++ mots) n
  let mut out := #[]
  let mut i := 0
  for s in scope do
    for ci in [:c.inp.members[s]!.ctors.size] do
      out := out.push (← minorLambda tys[i]! (← c.numFields s ci) (minor s ci))
      i := i + 1
  return out

/-- The hypotheses the recursion over `scope` gives at `fields`: one per datum of the scope, in order. -/
private def scopedIhs (scope : Array Nat) (kinds : Array Kind) (ihs : Array Expr) : Array (Nat × Expr) := Id.run do
  let mut out := #[]
  let mut n := 0
  for kd in kinds do
    if let .data f j := kd then
      if scope.contains j then
        out := out.push (f, ihs[n]!)
        n := n + 1
  return out

/-- `G` for the members of `scope`. -/
private def Ctx.addGraph (c : Ctx) (scope : Array Nat) : MetaM Unit := do
  let lvl := mkLevelMax' (mkLevelSucc .zero) c.uLvl
  let mots ← scope.mapM fun s => c.overMember s fun idx x =>
    mkArrow (mkAppN (c.motiveOf s) (idx.push x)) (mkSort .zero)
  let minors ← c.recursion scope lvl mots fun s ci fs ihs => do
    let kinds ← kindsOf c.inp fs
    let (idx, self) ← c.ctorAt s ci fs
    let ihAt := scopedIhs scope kinds ihs
    let m := c.minorOf[s]![ci]!
    -- the facts: the recursion's own predicate at a field of the scope, `G` elsewhere
    let rec go (ty : Expr) (ks : List Kind) (acc : Array Expr) (r : Expr) : MetaM Expr := do
      match ks with
      | [] => mkEq r (mkAppN m (fs ++ acc))
      | kd :: ks =>
        let .forallE n d body _ := ty | throwError "a minor premise ended early"
        withLocalDeclD n d fun x => do
          let rest ← go (body.instantiate1 x) ks (acc.push x) r
          let inner ← if let .data f j := kd then do
              let fact ← match ihAt.find? (·.1 == f) with
                | some (_, ih) => forallTelescope d fun dom _ => mkForallFVars dom (mkApp (mkAppN ih dom) (mkAppN x dom))
                | none => factAt c j d x
              pure (mkAnd fact rest)
            else pure rest
          mkExists d (← mkLambdaFVars #[x] inner)
    withLocalDeclD `r (mkAppN (c.motiveOf s) (idx.push self)) fun r => do
      mkLambdaFVars #[r] (← go (← instantiateForall (← inferType m) fs) kinds.toList #[] r)
  for s in scope do
    let recS ← c.dataRec s lvl
    let value ← c.overMember s fun idx x => pure (mkAppN recS (c.ps ++ mots ++ minors ++ idx ++ #[x]))
    let type ← c.forallMember s fun idx x => mkArrow (mkAppN (c.motiveOf s) (idx.push x)) (mkSort .zero)
    c.add (auxName c.inp s "G") type value false

/-- The data members `G` is functional at with no `funext`: those whose
constructors' data fields are first order, of members that are so too. -/
private def Ctx.firstOrder (c : Ctx) : MetaM (Array Nat) := do
  -- each member's constructors' data fields: whether all first order, and of which members
  let mut deps : Array (Option (Array Nat)) := #[]
  for s in [:c.inp.members.size] do
    if c.inp.members[s]!.prop then
      deps := deps.push none
      continue
    let mut ms : Option (Array Nat) := some #[]
    for ci in [:c.inp.members[s]!.ctors.size] do
      let r ← forallTelescope (← instantiateForall (← inferType (← constAt c.inp.members[s]!.ctors[ci]!)) c.ps)
        fun fields _ => do
          let mut out := #[]
          for kd in ← kindsOf c.inp fields do
            if kd.isData then
              let higher ← forallTelescope (← inferType fields[kd.field]!) fun dom _ => pure !dom.isEmpty
              if higher then return none
              out := out.push kd.member
          return some out
      ms := match ms, r with
        | some a, some b => some (a ++ b)
        | _, _ => none
    deps := deps.push ms
  -- the greatest set closed under them
  let mut q := (Array.range c.inp.members.size).filter fun s => deps[s]!.isSome
  let mut changed := true
  while changed do
    let q' := q.filter fun s => deps[s]!.get!.all q.contains
    changed := q'.size != q.size
    q := q'
  return q

/-- `UNIQ` for the members of `scope` in `q`: `G x r → G x r' → r = r'`, the
others at `True`. -/
private def Ctx.addUniq (c : Ctx) (scope q : Array Nat) : MetaM Unit := do
  let stmt (s : Nat) (idx : Array Expr) (x : Expr) : MetaM Expr := do
    let mty := mkAppN (c.motiveOf s) (idx.push x)
    withLocalDeclD `r mty fun r => withLocalDeclD `r' mty fun r' => do
      let g := mkAppN (c.aux s "G") (idx ++ #[x])
      withLocalDeclD `hr (mkApp g r) fun hr => withLocalDeclD `hr' (mkApp g r') fun hr' => do
        mkForallFVars #[r, r', hr, hr'] (← mkEq r r')
  let mots ← scope.mapM fun s => c.overMember s fun idx x =>
    if q.contains s then stmt s idx x else pure (mkConst ``True)
  let minors ← c.recursion scope .zero mots fun s ci fs ihs => do
    unless q.contains s do return mkConst ``True.intro
    let kinds ← kindsOf c.inp fs
    let (idx, self) ← c.ctorAt s ci fs
    let ihAt := scopedIhs scope kinds ihs
    let m := c.minorOf[s]![ci]!
    let mty ← instantiateForall (← inferType m) fs
    let rty := mkAppN (c.motiveOf s) (idx.push self)
    withLocalDeclD `r rty fun r => withLocalDeclD `r' rty fun r' => do
    let gr ← graphStmt c m fs r
    let gr' ← graphStmt c m fs r'
    withLocalDeclD `hr gr fun hr => withLocalDeclD `hr' gr' fun hr' => do
    let goal ← mkEq r r'
    let proof ← destructFrom c m fs r goal (fun _ _ _ _ => pure none) hr mty kinds.toList #[] #[] fun acc1 facts1 e1 => do
      -- the second, each value read at the first's
      let datas := (kinds.zipIdx.filter (·.1.isData)).map (·.2)
      let hook (kd : Kind) (d x fact : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
        let .data f j := kd | return none
        let some pos := kinds.findIdx? (·.field == f) | return none
        let some di := datas.idxOf? pos | return none
        let y := acc1[pos]!
        let fy := facts1[di]!
        let args := (← whnfCore d).getAppArgs
        let uniq := match ihAt.find? (·.1 == f) with
          | some (_, ih) => mkApp4 ih x y fact fy
          | none => mkAppN (c.aux j "UNIQ") (args ++ #[x, y, fact, fy])
        return some (y, uniq, fy)
      destructFrom c m fs r' goal hook hr' mty kinds.toList #[] #[] fun _ _ e2 => do
        -- `r = m fs acc₁` and `r' = m fs acc₂`, the two the same but for proofs
        mkEqTrans e1 (← mkEqSymm e2)
    mkLambdaFVars #[r, r', hr, hr'] proof
  for s in scope do
    unless q.contains s do continue
    let recS ← c.dataRec s .zero
    let value ← c.overMember s fun idx x => pure (mkAppN recS (c.ps ++ mots ++ minors ++ idx ++ #[x]))
    let type ← c.forallMember s (stmt s)
    c.add (auxName c.inp s "UNIQ") type value true

/-- A proof that `G` relates the index term `t` to the value `w`: a value at
hand, or a minor premise at fields and values, whose `G` is by construction. -/
private partial def proveG (c : Ctx) (known : Array (Expr × Expr)) (w : Expr) : MetaM Expr := do
  let w := w.headBeta
  if let some (_, fact) := known.find? (·.1 == w) then return fact
  let f := w.getAppFn
  if let some (_, fact) := known.find? (·.1 == f) then return mkAppN fact w.getAppArgs
  -- a minor premise at its fields and hypotheses
  for k in [:c.inp.members.size] do
    if let some ci := c.minorOf[k]!.idxOf? f then
      let nf ← c.numFields k ci
      let args := w.getAppArgs
      let fs := args.extract 0 nf
      let hyps := args.extract nf args.size
      let kinds ← kindsOf c.inp fs
      let mty ← instantiateForall (← inferType f) fs
      let mut i := 0
      let mut supplied := #[]
      for kd in kinds do
        let v := hyps[i]!
        i := i + 1
        if kd.isData then
          let d ← forallTelescope (← inferType fs[kd.field]!) fun dom _ => pure dom.isEmpty
          let fact ← if d then proveG c known v else
            -- over a domain: pointwise
            forallTelescope (← inferType v) fun dom _ => do
              mkLambdaFVars dom (← proveG c known (mkAppN v dom))
          supplied := supplied.push (v, some fact)
        else supplied := supplied.push (v, none)
      let given := supplied
      let idxRef ← IO.mkRef 0
      return ← introFrom c f fs w (fun _ _ => do
          let n ← idxRef.get
          idxRef.set (n + 1)
          return given[n]!) mty kinds.toList #[]
  gap m!"no reading of `G` at {w}"

/-- The proof of a displayed motive at a proof field: `LEM` at the values the
hypothesis' type displays, with their facts. -/
private def proofHyp (c : Ctx) (known : Array (Expr × Expr)) (j : Nat) (h d : Expr) : MetaM Expr :=
  forallTelescope d fun dom body => do
    let args := body.getAppArgs
    let (idx, vals) := c.splitDisplayed j args.pop
    let facts ← vals.mapM (proveG c known)
    mkLambdaFVars dom (mkAppN (c.aux j "LEM") (idx ++ #[mkAppN h dom] ++ vals ++ facts))

/-- `LEM` for the `Prop` members of `props`, out of their recursion into `Prop`;
a proof of one outside it by its `LEM`, which comes first. -/
private def Ctx.addLem (c : Ctx) (props : Array Nat) : MetaM Unit := do
  -- `∀ vs, facts → motive (displayed) g`
  let stmt (j : Nat) (idx : Array Expr) (g : Expr) : MetaM Expr := do
    let shown := c.displayAt[j]!
    let rec go (a : Nat) (vals : Array (Option Expr)) (vs facts : Array Expr) : MetaM Expr := do
      if h : a < idx.size then
        match shown[a]! with
        | none => go (a + 1) (vals.push none) vs facts
        | some k =>
          let ity ← instantiateMVars (← inferType idx[a])
          let iargs := ity.getAppArgs.extract c.np ity.getAppNumArgs
          withLocalDeclD `v (mkAppN (c.motiveOf k) (iargs.push idx[a])) fun v =>
            go (a + 1) (vals.push (some v)) (vs.push v) (facts.push (mkAppN (c.aux k "G") (iargs ++ #[idx[a], v])))
      else
        let body := c.motiveApp j idx vals g
        let rec bindFacts (i : Nat) (hs : Array Expr) : MetaM Expr := do
          if h : i < facts.size then withLocalDeclD `hv facts[i] fun hv => bindFacts (i + 1) (hs.push hv)
          else mkForallFVars (vs ++ hs) body
        bindFacts 0 #[]
    go 0 #[] #[] #[]
  let mots ← props.mapM fun j => c.overMember j (stmt j)
  -- a recursion that may eliminate into any sort does so into `Prop`
  let recAt (j : Nat) : MetaM Expr := do
    let info ← getConstInfo (c.inp.elim j "rec")
    return mkConst info.name (info.levelParams.map fun n =>
      if c.blockLvls.contains n then mkLevelParam n else .zero)
  let rec0 ← recAt props[0]!
  let n := props.foldl (fun n j => n + c.inp.members[j]!.ctors.size) 0
  let tys ← minorTypes rec0 (c.ps ++ mots) n
  let mut minors := #[]
  let mut ti := 0
  for j in props do
    for ci in [:c.inp.members[j]!.ctors.size] do
      let mty := tys[ti]!
      ti := ti + 1
      minors := minors.push <| ← minorLambda mty (← c.numFields j ci) fun fs pihs => do
        let kinds ← kindsOf c.inp fs
        let (cidx, self) ← c.ctorAt j ci fs
        let pihOf := (kinds.filter fun kd => !kd.isData && props.contains kd.member).map (·.field) |>.zip pihs
        let goalTy := (← instantiateForall mty (fs ++ pihs)).headBeta
        forallTelescope goalTy fun vhs goal => do
          let nv := vhs.size / 2
          let vs := vhs.extract 0 nv
          let hs := vhs.extract nv vhs.size
          let shownAt := (Array.range cidx.size).filter fun a => c.displayAt[j]![a]!.isSome
          -- the values at the data fields, read off `G` at the indices that name them
          let known ← IO.mkRef (#[] : Array (Expr × Expr × Expr))
          let disp ← IO.mkRef (#[] : Array (Expr × Option Expr))
          let rec atIndex (n : Nat) : MetaM Expr := do
            if h : n < shownAt.size then
              let a := shownAt[n]
              let t := cidx[a]!
              let k := c.displayAt[j]![a]!.get!
              let v := vs[n]!
              let hv := hs[n]!
              if t.isFVar && fs.contains t then
                match (← known.get).find? (·.1 == t) with
                | some (_, y, fy) =>
                  unless c.uniq.contains k do gap m!"a field named twice, of `{c.inp.members[k]!.name}`"
                  let ity ← instantiateMVars (← inferType t)
                  let iargs := ity.getAppArgs.extract c.np ity.getAppNumArgs
                  disp.modify (·.push (y, some (mkAppN (c.aux k "UNIQ") (iargs ++ #[t, y, v, fy, hv]))))
                | none =>
                  known.modify (·.push (t, v, hv))
                  disp.modify (·.push (v, none))
                atIndex (n + 1)
              else
                let .const cn _ := t.getAppFn | gap m!"an index the recursion cannot follow: {t}"
                let some (s, ci') := ctorOf? c.inp cn | gap m!"an index the recursion cannot follow: {t}"
                let targs := t.getAppArgs.extract c.np t.getAppNumArgs
                let m := c.minorOf[s]![ci']!
                let mty ← instantiateForall (← inferType m) targs
                let tkinds ← kindsOf c.inp targs
                let hook (kd : Kind) (d x fact : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
                  let a' := targs[kd.field]!
                  unless a'.isFVar && fs.contains a' do return none
                  match (← known.get).find? (·.1 == a') with
                  | some (_, y, fy) =>
                    unless c.uniq.contains kd.member do gap m!"a field named twice, of `{c.inp.members[kd.member]!.name}`"
                    let args := (← whnfCore d).getAppArgs
                    return some (y, mkAppN (c.aux kd.member "UNIQ") (args ++ #[x, y, fact, fy]), fy)
                  | none =>
                    known.modify (·.push (a', x, fact))
                    return none
                destructFrom c m targs v goal hook hv mty tkinds.toList #[] #[] fun acc _ e => do
                  disp.modify (·.push (mkAppN m (targs ++ acc), some (← mkEqSymm e)))
                  atIndex (n + 1)
            else
              -- every datum of the constructor has its value
              let ks := (← known.get)
              for kd in kinds do
                if kd.isData && !(ks.any (·.1 == fs[kd.field]!)) then
                  gap m!"a datum of `{c.inp.members[j]!.ctors[ci]!}` its conclusion does not name"
              let facts := ks.map fun (_, y, fy) => (y, fy)
              let mut hyps := #[]
              let mut ty ← instantiateForall (← inferType c.minorOf[j]![ci]!) fs
              for kd in kinds do
                let .forallE _ d body _ := ty | throwError "a minor premise ended early"
                let v ← if kd.isData then
                    pure ((ks.find? (·.1 == fs[kd.field]!)).get!.2.1)
                  else if !props.contains kd.member then
                    proofHyp c facts kd.member fs[kd.field]! d
                  else
                    let some (_, pih) := pihOf.find? (·.1 == kd.field) | throwError "no hypothesis at a proof"
                    -- the recursion's hypothesis there, at its values
                    forallTelescope d fun dom dbody => do
                      let dargs := dbody.getAppArgs
                      let (_, vals) := c.splitDisplayed kd.member dargs.pop
                      let vfacts ← vals.mapM (proveG c facts)
                      mkLambdaFVars dom (mkAppN pih (dom ++ vals ++ vfacts))
                hyps := hyps.push v
                ty := body.instantiate1 v
              let mut proof := mkAppN c.minorOf[j]![ci]! (fs ++ hyps)
              -- the displayed values carried over to the ones given
              let ds ← disp.get
              for i in [:ds.size] do
                let some e := ds[i]!.2 | continue
                let before := (vs.extract 0 i).map some
                let after := (ds.extract (i + 1) ds.size).map (some ·.1)
                let vty ← inferType vs[i]!
                let mot ← withLocalDeclD `x vty fun x => do
                  let ws := before ++ #[some x] ++ after
                  let mut vals := #[]
                  let mut wi := 0
                  for a in [:cidx.size] do
                    if c.displayAt[j]![a]!.isSome then
                      vals := vals.push ws[wi]!
                      wi := wi + 1
                    else vals := vals.push none
                  mkLambdaFVars #[x] (c.motiveApp j cidx vals self)
                proof ← ndrec vty ds[i]!.1 mot proof vs[i]! e
              return proof
          mkLambdaFVars vhs (← atIndex 0)
  for j in props do
    let recJ ← recAt j
    let value ← c.overMember j fun idx g => pure (mkAppN recJ (c.ps ++ mots ++ minors ++ idx ++ #[g]))
    let type ← c.forallMember j (stmt j)
    c.add (auxName c.inp j "LEM") type value true

/-- `J'` for the members of `scope`: the value and its `G`. -/
private def Ctx.addValue (c : Ctx) (scope : Array Nat) : MetaM Unit := do
  let lvl := mkLevelMax' (mkLevelSucc .zero) c.uLvl
  let sigmaOf (s : Nat) (idx : Array Expr) (x : Expr) : MetaM Expr := do
    let α := mkAppN (c.motiveOf s) (idx.push x)
    let β ← withLocalDeclD `r α fun r => mkLambdaFVars #[r] (mkAppN (c.aux s "G") (idx ++ #[x, r]))
    return mkApp2 (mkConst ``PSigma [c.uLvl, .zero]) α β
  let mots ← scope.mapM fun s => c.overMember s (sigmaOf s)
  let minors ← c.recursion scope lvl mots fun s ci fs ihs => do
    let kinds ← kindsOf c.inp fs
    let (idx, self) ← c.ctorAt s ci fs
    let ihAt := scopedIhs scope kinds ihs
    let m := c.minorOf[s]![ci]!
    let mty ← instantiateForall (← inferType m) fs
    -- each datum's value and fact: the recursion's, or `J'` across components
    let mut known := #[]
    let mut supplied := #[]
    let mut ty := mty
    for kd in kinds do
      let .forallE _ d body _ := ty | throwError "a minor premise ended early"
      let (v, fact?) ← if let .data f j := kd then do
          let pair ← forallTelescope d fun dom dbody => do
            let p := match ihAt.find? (·.1 == f) with
              | some (_, ih) => mkAppN ih dom
              | none => mkAppN (c.aux j "J") (dbody.getAppArgs)
            let pty ← whnfCore (← inferType p)
            let .app (.app _ α) β := pty | throwError "not a pair: {pty}"
            let fst := mkApp3 (mkConst ``PSigma.fst [c.uLvl, .zero]) α β p
            let snd := mkApp3 (mkConst ``PSigma.snd [c.uLvl, .zero]) α β p
            return (← mkLambdaFVars dom fst, ← mkLambdaFVars dom snd)
          pure (pair.1, some pair.2)
        else do
          let .proof f j := kd | unreachable!
          pure (← proofHyp c known j fs[f]! d, none)
      if let some fact := fact? then known := known.push (v, fact)
      supplied := supplied.push (v, fact?)
      ty := body.instantiate1 v
    let val := mkAppN m (fs ++ supplied.map (·.1))
    let idxRef ← IO.mkRef 0
    let gproof ← introFrom c m fs val (fun _ _ => do
        let n ← idxRef.get
        idxRef.set (n + 1)
        return supplied[n]!) mty kinds.toList #[]
    let α := mkAppN (c.motiveOf s) (idx.push self)
    let β ← withLocalDeclD `r α fun r => mkLambdaFVars #[r] (mkAppN (c.aux s "G") (idx ++ #[self, r]))
    return mkApp4 (mkConst ``PSigma.mk [c.uLvl, .zero]) α β val gproof
  for s in scope do
    let recS ← c.dataRec s lvl
    let value ← c.overMember s fun idx x => pure (mkAppN recS (c.ps ++ mots ++ minors ++ idx ++ #[x]))
    let type ← c.forallMember s (sigmaOf s)
    c.add (auxName c.inp s "J") type value false

/-- The public recursors: a data member's the value `J'` computes, a `Prop`
member's `LEM` at those values. -/
private def Ctx.addRecs (c : Ctx) : MetaM Unit := do
  let lvls := c.lps.map mkLevelParam
  let implicitIdx {α} (idx : Array Expr) (k : MetaM α) : MetaM α := withInfos idx (fun bi => if bi == .instImplicit then bi else .implicit) k
  for k in [:c.inp.members.size] do
    let mem := c.inp.members[k]!
    let (type, value) ← forallTelescope (← c.arity k) fun idx _ => implicitIdx idx do
      withLocalDeclD `t (← c.memberAt k idx) fun t => do
        if !mem.prop then
          let p := mkAppN (c.aux k "J") (idx.push t)
          let α := mkAppN (c.motiveOf k) (idx.push t)
          let β ← withLocalDeclD `r α fun r => mkLambdaFVars #[r] (mkAppN (c.aux k "G") (idx ++ #[t, r]))
          let v := mkApp3 (mkConst ``PSigma.fst [c.uLvl, .zero]) α β p
          return (← mkForallFVars (c.pre ++ idx.push t) α, ← mkLambdaFVars (c.pre ++ idx.push t) v)
        else
          let mut vals := #[]
          let mut facts := #[]
          for a in [:idx.size] do
            match c.displayAt[k]![a]! with
            | none => vals := vals.push none
            | some j =>
              let ity ← instantiateMVars (← inferType idx[a]!)
              let iargs := ity.getAppArgs.extract c.np ity.getAppNumArgs
              let recJ := mkAppN (mkConst (c.inp.members[j]!.name ++ `rec) lvls) (c.pre ++ iargs.push idx[a]!)
              vals := vals.push (some recJ)
              let p := mkAppN (c.aux j "J") (iargs.push idx[a]!)
              let α := mkAppN (c.motiveOf j) (iargs.push idx[a]!)
              let β ← withLocalDeclD `r α fun r => mkLambdaFVars #[r] (mkAppN (c.aux j "G") (iargs ++ #[idx[a]!, r]))
              facts := facts.push (mkApp3 (mkConst ``PSigma.snd [c.uLvl, .zero]) α β p)
          let concl := c.motiveApp k idx vals t
          let v := mkAppN (c.aux k "LEM") (idx ++ #[t] ++ vals.filterMap id ++ facts)
          return (← mkForallFVars (c.pre ++ idx.push t) concl, ← mkLambdaFVars (c.pre ++ idx.push t) v)
    let name := mem.name ++ `rec
    if mem.prop then addDecl (.thmDecl { name, levelParams := c.lps, type, value })
    else addDef name c.lps type value

/-- Build the joint recursor of a block, or say why it cannot be. -/
private def build (inp : Input) : MetaM Unit := withSpec inp fun c => do
  -- the data's recursions, in the order the frontend declared them
  let mut scopes : Array (Array Nat) := #[]
  for k in [:inp.members.size] do
    let m := inp.members[k]!
    if !m.prop && !scopes.contains m.scope then scopes := scopes.push m.scope
  for scope in scopes do c.addGraph scope
  let q ← c.firstOrder
  for scope in scopes do
    if scope.any q.contains then c.addUniq scope q
  let c := { c with uniq := q }
  -- the propositions' recursions, in the order given
  let mut propScopes : Array (Array Nat) := #[]
  let allProps := (Array.range inp.members.size).filter (inp.members[·]!.prop)
  for k in allProps do
    let sc := if inp.members[k]!.scope.isEmpty then allProps else inp.members[k]!.scope
    if !propScopes.contains sc then propScopes := propScopes.push sc
  for sc in propScopes do c.addLem sc
  for scope in scopes do c.addValue scope
  c.addRecs

/-- Tag `n` `@[elab_as_elim]`, without registering it with the tactics. -/
private def tagElim (n : Name) : MetaM Unit := do
  try
    discard <| Lean.Elab.Term.getElabElimInfo n
    Lean.Elab.Term.elabAsElim.setTag n
  catch _ => pure ()

/-- Give the frontend's own eliminators the public names, as they are. -/
private def publishOwn (inp : Input) : MetaM Unit := do
  let props := inp.members.filter (·.prop)
  for k in [:inp.members.size] do
    let m := inp.members[k]!
    let names := if m.prop then #["rec", "casesOn"] else #["rec", "recOn", "casesOn", "recD", "cases"]
    for s in names do
      discard <| attempt? `Mumi m!"no `{s}` for `{m.name}`" <| restate (inp.elim k s) (m.name ++ Name.mkSimple s)
    tagElim (m.name ++ `rec)
    if m.prop then
      if props.size == 1 then markElabAsElim (m.name ++ `rec) (induction := true)
      markElabAsElim (m.name ++ `casesOn) (induction := false)
    else
      tagElim (m.name ++ `recOn)
      tagElim (m.name ++ `cases)
      markElabAsElim (m.name ++ `recD) (induction := true)
      markElabAsElim (m.name ++ `casesOn) (induction := false)

/-- Everything else under the public names, around the joint recursor. -/
private def publishAround (inp : Input) : MetaM Unit := do
  for k in [:inp.members.size] do
    let m := inp.members[k]!
    tagElim (m.name ++ `rec)
    discard <| attempt? `Mumi m!"no `recOn` for `{m.name}`" <|
      addMajorFirst inp.numParams m.name (m.name ++ `rec) (m.name ++ `recOn)
    tagElim (m.name ++ `recOn)
    if m.prop then
      discard <| attempt? `Mumi m!"no `casesOn` for `{m.name}`" <|
        addMajorFirst inp.numParams m.name (inp.elim k "casesOn") (m.name ++ `casesOn)
      markElabAsElim (m.name ++ `casesOn) (induction := false)
    else
      let motive? ← motiveNameOf? inp.numParams m.name
      discard <| attempt? `Mumi m!"no `casesOn` for `{m.name}`" <|
        restate (inp.elim k "casesOn") (m.name ++ `casesOn) (motive?.map (inp.numParams, ·))
      markElabAsElim (m.name ++ `casesOn) (induction := false)
      for s in ["recD", "cases"] do
        discard <| attempt? `Mumi m!"no `{s}` for `{m.name}`" <|
          restate (inp.elim k s) (m.name ++ Name.mkSimple s)
      markElabAsElim (m.name ++ `recD) (induction := true)
      tagElim (m.name ++ `cases)

/-- Build the joint recursor under the public names `X.rec`, out of the
recursions the members name; whether it could be, the environment as it was
when it could not. -/
def buildJoint (inp : Input) : MetaM Bool := do
  let env ← getEnv
  try
    build inp
    return true
  catch e =>
    setEnv env
    trace[Mumi] "{e.toMessageData}"
    return false

/-- Publish the block's eliminators: the joint recursor where it can be built,
the frontend's own otherwise. -/
def publish (inp : Input) : MetaM Unit := do
  let env ← getEnv
  try
    build inp
    publishAround inp
  catch e =>
    setEnv env
    trace[Mumi] "{e.toMessageData}; the frontend's own eliminators are published"
    publishOwn inp

end Mumi.Displayed
