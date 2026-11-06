/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Mumi.Runtime
public meta import Mumi.View
public meta import Lean.Elab.Tactic.ElabTerm
public meta import Lean.Elab.Tactic.Induction
public meta import Lean.Meta.Tactic.Cases
public meta import Lean.Meta.Tactic.Assert
public meta import Lean.Meta.Tactic.Simp.Simproc

/-!
# Equations between constructors

Lean's `contradiction`, `injection` and `cases` read an equation `a = b` off the
constructors at its head, and recognise a constructor by being one, in the kernel.  A
constructor of an encoded member is a definition, whose unfolding is a wrapper's one
constructor: to those tactics any two of them look the same, and they conclude nothing
of use, or stop at an equation between internals.

What they would want is in `X.ctorIdx_c` (`Mumi.View`), which says which constructor a
term is without unfolding it, and `X.c.inj`.  So each tactic gets a first look here, at an
equation between two such constructors; on anything else it is Lean's, untouched.  `simp`
gets the same through a simproc.  Nothing stated mentions an internal, and each proof goes
through `X.ctorIdx`, which the kernel computes.
-/

public meta section

namespace Mumi

open Lean Meta Lean.Elab Lean.Elab.Tactic

/-- A constructor of an encoded member, applied: its name, what says which it is, and
its position. -/
private structure EncodedCtor where
  name : Name
  rule : Name
  idx : Nat

/-- `e` as a fully applied constructor of an encoded member. -/
private def encodedCtor? (e : Expr) : MetaM (Option EncodedCtor) := do
  let e := (← instantiateMVars e).consumeMData
  let .const c _ := e.getAppFn | return none
  let .str mem s := c | return none
  let rule := Name.mkStr mem s!"ctorIdx_{s}"
  let some ci := (← getEnv).find? rule | return none
  let some idx ← forallTelescope ci.type fun xs body => do
      unless xs.size == e.getAppNumArgs do return none
      let some (_, _, rhs) := body.eq? | return none
      return rhs.nat?
    | return none
  return some { name := c, rule, idx }

/-- The two sides of an equation or a heterogeneous one. -/
private def sides? (ty : Expr) : Option (Expr × Expr) :=
  match ty.eq? with
  | some (_, a, b) => some (a, b)
  | none => match ty.heq? with
    | some (_, a, _, b) => some (a, b)
    | none => none

/-- A proof of `False` from `h : a = b`, at two different constructors. -/
private def refute (h a b : Expr) (ca cb : EncodedCtor) : MetaM Expr := do
  let mem := ca.name.getPrefix
  let f ← withLocalDeclD `x (← inferType a) fun x => do
    mkLambdaFVars #[x] (← mkAppM (mem ++ `ctorIdx) #[x])
  let ruleAt (c : EncodedCtor) (e : Expr) : MetaM Expr :=
    -- at the constructor's own universes: a fresh one is out of `mkAppM`'s reach to assign
    return mkAppN (mkConst c.rule e.getAppFn.constLevels!) e.getAppArgs
  let ha ← ruleAt ca a
  let hb ← ruleAt cb b
  let ne ← mkAppM ``Mumi.ne_of_ctorIdx
    #[f, ha, hb, ← mkEqRefl (mkConst ``Bool.false)]
  return mkApp ne h

/-- `h`, as an equation, if it is one or a heterogeneous one at the one type. -/
private def asEq? (h : Expr) : MetaM (Option Expr) := do
  let ty ← instantiateMVars (← inferType h)
  if ty.isEq then return some h
  if ty.isHEq then
    try return some (← mkEqOfHEq h) catch _ => return none
  return none

/-- The equations `X.c.inj` gives at `h : X.c … = X.c …`, and their proofs. -/
private partial def fieldEqs (c : Name) (h : Expr) : MetaM (Array (Expr × Expr)) := do
  unless (← getEnv).contains (c ++ `inj) do return #[]
  let rec split (p ty : Expr) (acc : Array (Expr × Expr)) : MetaM (Array (Expr × Expr)) := do
    let ty := (← instantiateMVars ty).consumeMData
    if ty.isAppOfArity ``And 2 then
      let a := ty.getArg! 0
      let b := ty.getArg! 1
      split (mkApp3 (mkConst ``And.right) a b p) b
        (acc.push (a, mkApp3 (mkConst ``And.left) a b p))
    else
      return acc.push (ty, p)
  let p ← mkAppM (c ++ `inj) #[h]
  split p (← inferType p) #[]

/-- Both sides of the hypothesis `h`, each a constructor of an encoded member. -/
private def encodedSides? (h : Expr) : MetaM (Option (Expr × Expr × EncodedCtor × EncodedCtor)) := do
  let some (a, b) := sides? (← instantiateMVars (← inferType h)) | return none
  let some ca ← encodedCtor? a | return none
  let some cb ← encodedCtor? b | return none
  return some (a.consumeMData, b.consumeMData, ca, cb)

/-- `contradiction`: a hypothesis equating two different constructors of an encoded
member.  Lean's looks for everything else. -/
@[tactic Lean.Parser.Tactic.contradiction]
def evalContradictionEncoded : Tactic := fun _ => withMainContext do
  let g ← getMainGoal
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let some (a, b, ca, cb) ← encodedSides? d.toExpr | continue
    if ca.name == cb.name then continue
    let some h ← asEq? d.toExpr | continue
    g.assign (← mkFalseElim (← g.getType) (← refute h a b ca cb))
    replaceMainGoal []
    return
  throwUnsupportedSyntax

/-- `injection h with …` at an equation between constructors of an encoded member: at
two different ones the goal is closed, and at one its fields' equations are hypotheses. -/
@[tactic Lean.Parser.Tactic.injection]
def evalInjectionEncoded : Tactic := fun stx => withMainContext do
  let h ← elabAsFVar stx[1]
  let hE := mkFVar h
  let some (a, b, ca, cb) ← encodedSides? hE | throwUnsupportedSyntax
  let some eq ← asEq? hE | throwUnsupportedSyntax
  let ids := if stx[2].isNone then #[] else stx[2][1].getArgs.map (·.getId)
  let g ← getMainGoal
  if ca.name != cb.name then
    g.assign (← mkFalseElim (← g.getType) (← refute eq a b ca cb))
    replaceMainGoal []
    return
  let eqs ← fieldEqs ca.name eq
  if ids.size > eqs.size then
    throwTacticEx `injection g m!"too many identifiers provided, unused: {ids.extract eqs.size ids.size}"
  let hyps ← eqs.mapIdxM fun i (ty, value) => do
    return { userName := ← (match ids[i]? with
                | some n => pure n
                | none => mkFreshUserName `h), type := ty, value : Hypothesis }
  let (_, g) ← g.assertHypotheses hyps
  let g ← g.tryClear h
  if ← g.assumptionCore then replaceMainGoal [] else replaceMainGoal [g]

/-- Discharge the first `n` premises of `g`'s target, each an equation, as `cases` does
one: between two different constructors the goal is gone, between one the fields'
equations take its place, and anything else is Lean's. -/
private partial def peelEqs (g : MVarId) (n : Nat) : MetaM (List MVarId) := do
  if n == 0 then return [g]
  let (h, g) ← g.intro1
  g.withContext do
    let hE := mkFVar h
    if let some (a, b, ca, cb) ← encodedSides? hE then
      if let some eq ← asEq? hE then
        if ca.name != cb.name then
          g.assign (← mkFalseElim (← g.getType) (← refute eq a b ca cb))
          return []
        let eqs ← fieldEqs ca.name eq
        let target ← g.getType
        let next ← eqs.foldrM (fun (ty, _) acc => mkArrow ty acc) target
        let g' ← mkFreshExprSyntheticOpaqueMVar next (← g.getTag)
        g.assign (mkAppN g' (eqs.map (·.2)))
        let g'' ← g'.mvarId!.tryClear h
        return ← peelEqs g'' (eqs.size + n - 1)
    let subs ← Cases.cases g h
    let mut out := []
    for s in subs do
      out := out ++ (← peelEqs s.mvarId (n - 1))
    return out

/-- `cases h` at an equation between constructors of an encoded member. -/
@[tactic Lean.Parser.Tactic.cases]
def evalCasesEncoded : Tactic := fun stx => withMainContext do
  -- `cases` target,+ (using)? (alts)?
  let targets := stx[1].getSepArgs
  unless targets.size == 1 && stx[2].isNone && stx[3].isNone do throwUnsupportedSyntax
  let t := targets[0]![1]
  unless t.isIdent do throwUnsupportedSyntax
  let some d := (← getLCtx).findFromUserName? t.getId | throwUnsupportedSyntax
  let some _ ← encodedSides? d.toExpr | throwUnsupportedSyntax
  let g ← getMainGoal
  let (rev, g) ← g.revert #[d.fvarId] (preserveOrder := true)
  -- what depended on the equation comes back, by the names it had
  let goals ← peelEqs g 1
  let goals ← goals.mapM fun m => do
    let (_, m) ← m.introNP (rev.size - 1)
    return m
  replaceMainGoal goals

/-- `(X.c₁ .. = X.c₂ ..) = False`, for two different constructors of an encoded member. -/
simproc [simp] ctorIdxNoConfusion (_ = _) := fun e => do
  let some (_, a, b) := e.eq? | return .continue
  let some ca ← encodedCtor? a | return .continue
  let some cb ← encodedCtor? b | return .continue
  if ca.name == cb.name then return .continue
  try
    let prf ← withDefault <| withLocalDeclD `h e fun h => do
      mkLambdaFVars #[h] (← refute h a.consumeMData b.consumeMData ca cb)
    return .done { expr := mkConst ``False, proof? := ← mkAppM ``eq_false #[prf] }
  catch _ =>
    return .continue

end Mumi
