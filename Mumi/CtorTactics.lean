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
public meta import Lean.Meta.Tactic.Injection
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

`cases` meets those equations a second way: on a term whose index is such a constructor,
`At (X.c …)`, it has to solve that index against each case, and stops where it reaches one.
So it is done here in Lean's steps, with `peelEqs` doing the solving (`casesIndexed`).
`rcases` and `obtain` take the same route where their pattern asks for nothing but that.

These are `@[no_fallback]`.  Lean otherwise tries its own elaborator of the tactic when one
fails, which here would answer about the wrapper, or report a mistake in a `| refl => …` as an
equation it could not solve.  What is not for here is declined with `throwUnsupportedSyntax`
before anything is done, and that is Lean's as ever.
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
@[tactic Lean.Parser.Tactic.injection, no_fallback]
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

/-- Whether `e` mentions a constructor of an encoded member. -/
private def mentionsEncodedCtor (env : Environment) (e : Expr) : Bool :=
  (e.find? fun x => match x with
    | .const (.str mem s) _ => env.contains (Name.mkStr mem s!"ctorIdx_{s}")
    | _ => false).isSome

/-- Whether `h` equates two of Lean's own constructors with one of an encoded member
inside: Lean's `cases` would go in and stop at it. -/
private def overNativeCtors (h : Expr) : MetaM Bool := do
  let some (a, b) := sides? (← instantiateMVars (← inferType h)) | return false
  let env ← getEnv
  unless mentionsEncodedCtor env a || mentionsEncodedCtor env b do return false
  -- as they stand: reducing one of these is what is to be avoided
  return (← isConstructorApp (← whnfR a)) && (← isConstructorApp (← whnfR b))

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
    -- anything else is Lean's, as an equation where it can be one
    let (h, g) ← if (← h.getType).isHEq then
        try heqToEq g h catch _ => pure (h, g)
      else pure (h, g)
    -- `h` may be new, so in the goal that has it
    if ← g.withContext (overNativeCtors (mkFVar h)) then
      match ← injectionCore g h with
      | .solved => return []
      | .subgoal g' numEqs => return ← peelEqs g' (numEqs + n - 1)
    let subs ← Cases.cases g h
    let mut out := []
    for s in subs do
      out := out ++ (← peelEqs s.mvarId (n - 1))
    return out

/-- The inductive `x` is of, if it is one with such a constructor at an index. -/
private def indexedAtEncoded? (x : Expr) : MetaM (Option InductiveVal) := do
  let ty ← whnfR (← instantiateMVars (← inferType x))
  let .const i _ := ty.getAppFn | return none
  if i == ``Eq || i == ``HEq then return none
  let some (.inductInfo ii) := (← getEnv).find? i | return none
  let env ← getEnv
  let idxs := ty.getAppArgs.extract ii.numParams ty.getAppNumArgs
  return if idxs.any (mentionsEncodedCtor env) then some ii else none

/-- `cases` on `major`, whose index is a constructor of an encoded member: each of its
inductive's constructors with the name it has, and what is left once its indices are
solved, none where they cannot be. -/
private def casesIndexed (g : MVarId) (major : FVarId) (ii : InductiveVal)
    (givenNames : Array AltVarNames := #[]) : MetaM (Array (Name × List MVarId)) := do
  let s ← generalizeIndices g major
  let subs ← s.mvarId.induction s.fvarId (ii.name ++ `casesOn) givenNames
  let mut out := #[]
  for sub in subs, c in ii.ctors do
    let mut m := sub.mvarId
    -- the indices stand for what the case's constructor concludes at now
    for ix in s.indicesFVarIds do
      if let some (.fvar y) := sub.subst.find? ix then m ← m.tryClear y
      else m ← m.tryClear ix
    out := out.push (c, ← peelEqs m s.numEqs)
  return out

/-! An `inductionAlt`, read as Lean reads one, whose helpers are not exported. -/

private def altLhs (alt : Syntax) : Syntax := alt[0][0]
private def getAltName? (alt : Syntax) : Option Name :=
  let head := (altLhs alt)[1]
  if head.isOfKind ``Parser.Term.hole then some `_
  else if head[1].isIdent then some head[1].getId.eraseMacroScopes else none
private def altHasExplicitModifier (alt : Syntax) : Bool :=
  let head := (altLhs alt)[1]
  !head.isOfKind ``Parser.Term.hole && !head[0].isNone
private def getAltVars (alt : Syntax) : Array Syntax := (altLhs alt)[2].getArgs
private def hasAltRHS (alt : Syntax) : Bool := alt[1].getNumArgs > 0
private def getAltRHS (alt : Syntax) : Syntax := alt[1][1]
private def isHoleRHS (rhs : Syntax) : Bool :=
  rhs.isOfKind ``Parser.Term.syntheticHole || rhs.isOfKind ``Parser.Term.hole

/-- Each alternative's tactics run on what is left of its case; a case nothing is left of
needs none. -/
private def runAlts (alts : Array Syntax) (cases : Array (Name × List MVarId)) : TacticM (List MVarId) := do
  let mut out : List MVarId := []
  for (c, goals) in cases do
    let short := c.getString!
    for m in goals do
      let alt? := alts.find? fun a => getAltName? a == some (Name.mkSimple short)
      let alt? := alt?.orElse fun _ => alts.find? fun a => getAltName? a == some `_
      match alt? with
      | none => out := out ++ [m]
      | some alt =>
        if !hasAltRHS alt || isHoleRHS (getAltRHS alt) then
          out := out ++ [m]
        else
          setGoals [m]
          evalTactic (getAltRHS alt)
          out := out ++ (← getUnsolvedGoals)
  return out

/-- What the alternatives written name of each of `ii`'s constructors' fields. -/
private def givenNamesOf (ii : InductiveVal) (alts : Array Syntax) : Array AltVarNames :=
  ii.ctors.toArray.map fun c =>
    match alts.find? fun a => getAltName? a == some (Name.mkSimple c.getString!) with
    | some a =>
      { explicit := altHasExplicitModifier a
        varNames := (getAltVars a).toList.map fun v =>
          if v.isIdent then v.getId else `_ }
    | none => {}

/-- Whether `cases` on the local `h` needs doing here. -/
private def wantedHere (h : FVarId) : MetaM Bool := do
  let hE := mkFVar h
  return (← encodedSides? hE).isSome || (← overNativeCtors hE) || (← indexedAtEncoded? hE).isSome

/-- `cases`, on the local `h`, where it needs doing here; `false` where it is Lean's.  Each
goal it leaves is under the alternative for its case, if there are any. -/
private def casesHere (h : FVarId) (alts : Array Syntax) : TacticM Bool := withMainContext do
  let hE := mkFVar h
  let g ← getMainGoal
  -- an alternative's tactics replace the goal list, so what is not this goal is kept here
  let others := (← getGoals).filter (· != g)
  if (← encodedSides? hE).isSome || (← overNativeCtors hE) then
    let (rev, g) ← g.revert #[h] (preserveOrder := true)
    let goals ← peelEqs g 1
    let goals ← goals.mapM fun m => do
      let (_, m) ← m.introNP (rev.size - 1)
      return m
    -- an equation has the one case
    let rest ← if alts.isEmpty then pure goals
      else runAlts alts #[(`Eq.refl, goals)]
    setGoals (rest ++ others)
    return true
  let some ii ← indexedAtEncoded? hE | return false
  let cases ← casesIndexed g h ii (givenNamesOf ii alts)
  let rest ← if alts.isEmpty then pure (cases.toList.flatMap (·.2)) else runAlts alts cases
  setGoals (rest ++ others)
  return true

/-- `cases h`, alternatives or none, at an equation between constructors of an encoded
member or on a term with one at an index. -/
@[tactic Lean.Parser.Tactic.cases, no_fallback]
def evalCasesEncoded : Tactic := fun stx => withMainContext do
  -- `cases` target,+ (using)? (alts)?
  let targets := stx[1].getSepArgs
  unless targets.size == 1 && stx[2].isNone do throwUnsupportedSyntax
  let t := targets[0]![1]
  unless t.isIdent do throwUnsupportedSyntax
  let some d := (← getLCtx).findFromUserName? t.getId | throwUnsupportedSyntax
  let alts := if stx[3].isNone then #[] else stx[3][0][2].getArgs
  -- `with tac` before the alternatives is not a thing this reads
  unless stx[3].isNone || stx[3][0][1].isNone do throwUnsupportedSyntax
  unless ← wantedHere d.fvarId do throwUnsupportedSyntax
  discard <| casesHere d.fvarId alts

/-- The atoms and identifiers of `s`, in order. -/
private partial def tokens (s : Syntax) : List String :=
  match s with
  | .atom _ v => [v]
  | .ident _ _ n _ => [n.eraseMacroScopes.toString]
  | .node _ _ args => args.toList.flatMap tokens
  | .missing => []

/-- A pattern that asks only for the case split: `⟨⟩`, and at an equation `rfl`. -/
private def splitPattern? (pat : Syntax) : Option String :=
  match tokens pat with
  | ["⟨", "⟩"] => some "⟨⟩"
  | ["rfl"] => some "rfl"
  | _ => none

/-- The names of a pattern `⟨x, y, _⟩` that does nothing but name a constructor's fields. -/
private def fieldPattern? (pat : Syntax) : Option (List Name) := do
  let ts := tokens pat
  guard (ts.length ≥ 3 && ts.head? == some "⟨" && ts.getLast? == some "⟩")
  let inner := (ts.drop 1).dropLast
  -- what is between the commas, one token each
  let names := inner.zipIdx.filter fun (_, i) => i % 2 == 0
  let commas := inner.zipIdx.filter fun (_, i) => i % 2 == 1
  guard (commas.all (·.1 == ","))
  names.mapM fun (s, _) =>
    if s == "⟨" || s == "⟩" || s == "|" || s == "-" || s == "@" || s == "rfl" || s == "(" || s == ")" then
      none
    else some (if s == "_" then `_ else s.toName)

/-- `rcases`/`obtain` on the local named `t` with such a pattern, where it needs doing here. -/
private def rcasesHere (t pat : Syntax) : TacticM Unit := withMainContext do
  unless t.isIdent do throwUnsupportedSyntax
  let some d := (← getLCtx).findFromUserName? t.getId | throwUnsupportedSyntax
  -- a one-constructor inductive at such an index, its fields named
  if let some names := fieldPattern? pat then
    let some ii ← indexedAtEncoded? d.toExpr | throwUnsupportedSyntax
    unless ii.ctors.length == 1 do throwUnsupportedSyntax
    let g ← getMainGoal
    let others := (← getGoals).filter (· != g)
    let cases ← casesIndexed g d.fvarId ii #[{ varNames := names }]
    setGoals (cases.toList.flatMap (·.2) ++ others)
    return
  let some kind := splitPattern? pat | throwUnsupportedSyntax
  if kind == "rfl" then
    -- only at an equation between constructors: against a variable it is a substitution
    if (← encodedSides? d.toExpr).isNone then throwUnsupportedSyntax
  unless ← wantedHere d.fvarId do throwUnsupportedSyntax
  discard <| casesHere d.fvarId #[]

/-- `rcases h with ⟨⟩`. -/
@[tactic Lean.Parser.Tactic.rcases, no_fallback]
def evalRCasesEncoded : Tactic := fun stx => do
  -- `rcases` target,* (with pat)?
  let targets := stx[1].getSepArgs
  unless targets.size == 1 && !stx[2].isNone do throwUnsupportedSyntax
  rcasesHere targets[0]![1] stx[2][1]

/-- `obtain ⟨⟩ := h`. -/
@[tactic Lean.Parser.Tactic.obtain, no_fallback]
def evalObtainEncoded : Tactic := fun stx => do
  -- `obtain` pat? (: ty)? (:= val,+)?
  unless !stx[1].isNone && stx[2].isNone && !stx[3].isNone do throwUnsupportedSyntax
  let vals := stx[3][1].getSepArgs
  unless vals.size == 1 do throwUnsupportedSyntax
  rcasesHere vals[0]! stx[1][0]

/-- `injection` on every hypothesis that is such an equation, and on what that gives. -/
private partial def injectAll (g : MVarId) (ids : List Name) (did : Bool := false) :
    MetaM (Option MVarId × List Name × Bool) := g.withContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let some (a, b, ca, cb) ← encodedSides? d.toExpr
      | -- one of Lean's own around one of these: Lean's `injections` would go through to the wrapper
        unless ← overNativeCtors d.toExpr do continue
        match ← injectionCore g d.fvarId with
        | .solved => return (none, ids, true)
        | .subgoal g' n =>
          let (_, g') ← g'.introNP n
          return ← injectAll g' ids true
    let some eq ← asEq? d.toExpr | continue
    if ca.name != cb.name then
      g.assign (← mkFalseElim (← g.getType) (← refute eq a b ca cb))
      return (none, ids, true)
    let eqs ← fieldEqs ca.name eq
    let mut rest := ids
    let mut hyps : Array Hypothesis := #[]
    for (ty, value) in eqs do
      let userName ← match rest with
        | n :: r =>
          rest := r
          pure n
        | [] => mkFreshUserName `h
      hyps := hyps.push { userName, type := ty, value }
    let (_, g') ← g.assertHypotheses hyps
    let g' ← g'.tryClear d.fvarId
    return ← injectAll g' rest true
  return (some g, ids, did)

/-- `injections`: Lean's, once the equations it cannot read have been read here, and these
again for any it finds under an inductive of its own. -/
@[tactic Lean.Parser.Tactic.injections, no_fallback]
def evalInjectionsEncoded : Tactic := fun stx => withMainContext do
  let ids := stx[1].getArgs.toList.map (·.getId)
  let (g?, ids, did) ← injectAll (← getMainGoal) ids
  unless did do throwUnsupportedSyntax
  let some g := g? | replaceMainGoal []; return
  match ← Meta.injections g ids with
  | .solved => replaceMainGoal []
  | .subgoal g ids _ =>
    let (g?, ids, _) ← injectAll g ids
    let some g := g? | replaceMainGoal []; return
    unless ids.isEmpty do
      throwTacticEx `injections g m!"too many identifiers provided, unused: {ids}"
    if ← g.assumptionCore then replaceMainGoal [] else replaceMainGoal [g]

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
