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
public meta import Lean.Meta.Tactic.Subst
public meta import Lean.Elab.Match
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
`rcases` and `obtain` take the same route where their pattern asks for nothing but that, and
so does `match`, whose compiler solves its indices the same way.

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
equations take its place, and anything else is Lean's.  `track` is what is wanted of each
goal left: what those terms have become.  Against a variable of the context a variable of
`track` is the one that goes, so the context keeps the names it had. -/
private partial def peelEqs (g : MVarId) (n : Nat) (track : Array Expr := #[]) :
    MetaM (List (MVarId × Array Expr)) := do
  if n == 0 then return [(g, track)]
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
        return ← peelEqs g'' (eqs.size + n - 1) track
    -- anything else is Lean's, as an equation where it can be one
    let (h, g) ← if (← h.getType).isHEq then
        try heqToEq g h catch _ => pure (h, g)
      else pure (h, g)
    -- `h` may be new, so in the goal that has it
    if ← g.withContext (overNativeCtors (mkFVar h)) then
      match ← injectionCore g h with
      | .solved => return []
      | .subgoal g' numEqs => return ← peelEqs g' (numEqs + n - 1) track
    -- a field against a variable from outside: the field goes
    let oriented ← g.withContext do
      let some (_, a, b) := (← instantiateMVars (← h.getType)).eq? | return false
      return a.isFVar && b.isFVar && track.contains a && !track.contains b
    if oriented then
      let (subst, g') ← substCore g h (symm := true)
      return ← peelEqs g' (n - 1) (track.map subst.apply)
    let subs ← Cases.cases g h
    let mut out := []
    for s in subs do
      out := out ++ (← peelEqs s.mvarId (n - 1) (track.map s.subst.apply))
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
    -- a field that came out as something else keeps its name, for that
    let names ← m.withContext do
      sub.fields.mapM fun f => match f with
        | .fvar y => y.getUserName
        | _ => pure .anonymous
    let left ← peelEqs m s.numEqs sub.fields
    let given : List Name := (givenNames[out.size]?.map (·.varNames)).getD []
    let left ← left.mapM fun (m, now) => do
      let mut m := m
      for f in sub.fields, v in now, nm in names do
        -- only what was asked for by name, not everything a case happened to bind
        unless f != v && given.contains nm do continue
        let ty ← m.withContext (inferType v)
        let m' ← m.define nm ty v
        let (_, m') ← m'.intro1P
        m := m'
      return m
    out := out.push (c, left)
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
    let goals ← goals.mapM fun (m, _) => do
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

/-- `X.noConfusion h`, where `h` equates two different constructors of an encoded member and
what is wanted of it is known.  What it should be is `X.noConfusionType P a b`, which is `P`
when `X.ctorIdx` is reduced; where that is a case split through an encoding Meta's unifier is
kept out of, this says so rather than leaving it stuck.  An indexed member's takes equations
at the indices first, which say nothing the last does not. -/
@[term_elab Lean.Parser.Term.app]
def elabNoConfusionAtCtors : Term.TermElab := fun stx expectedType? => do
  let f := stx[0]
  unless f.isIdent do throwUnsupportedSyntax
  let .str _ "noConfusion" := f.getId.eraseMacroScopes | throwUnsupportedSyntax
  let some expected := expectedType? | throwUnsupportedSyntax
  let some h := stx[1].getArgs.back? | throwUnsupportedSyntax
  let some (.const (Name.str mem _) _) ← Term.resolveId? f | throwUnsupportedSyntax
  unless (← getEnv).contains mem do throwUnsupportedSyntax
  let saved ← saveState
  let some (hE, a, b, ca, cb) ← (do
      let hE ← Term.elabTerm h none
      Term.synthesizeSyntheticMVarsNoPostponing
      let hE ← instantiateMVars hE
      let some (a, b, ca, cb) ← encodedSides? hE | return none
      unless ca.name != cb.name && ca.name.getPrefix == mem do return none
      return some (hE, a, b, ca, cb))
    | saved.restore; throwUnsupportedSyntax
  let some eq ← asEq? hE | saved.restore; throwUnsupportedSyntax
  mkFalseElim expected (← refute eq a b ca cb)

/-! ## `match` where an index is such a constructor

Lean's match compiler solves that index by its own `cases`, which nothing here reaches.  So
such a `match` is not given to it: it is written as the `cases` above, each case's
right-hand side elaborated where that `cases` leaves it, and what a pattern asks of a field
left to a `match` on that field, which is Lean's or this again. -/

/-- What a pattern asks of the discriminant being split. -/
private inductive Head where
  | ctor (short : Name) (args : Array Syntax)
  | any

/-- `p` as one of `ctors` and its explicit arguments as written, or `_`. -/
private partial def headOfPat (ctors : List Name) (p : Syntax) : TermElabM (Option Head) := do
  if p.isOfKind ``Parser.Term.paren then return ← headOfPat ctors p[1]
  if p.isOfKind ``Parser.Term.hole then return some .any
  let isCtor (s : Name) : Bool := ctors.any (·.getString! == s.toString)
  let (f, args) := if p.isOfKind ``Parser.Term.app then (p[0], p[1].getArgs) else (p, #[])
  let short? ← do
    if f.isOfKind ``Parser.Term.dotIdent then
      pure (some f[1].getId.eraseMacroScopes)
    else if f.isIdent then
      -- a variable is not a constructor, however it is spelled
      let cands := (← resolveGlobalName f.getId).filter (·.2.isEmpty) |>.map (·.1)
      pure ((cands.find? ctors.contains).map fun c => Name.mkSimple c.getString!)
    else pure none
  let some short := short? | return none
  unless isCtor short do return none
  if args.any (fun a => a.isOfKind ``Parser.Term.namedArgument) then return none
  return some (.ctor short args)

/-- How many explicit binders `c` has: its fields, a constructor's parameters being implicit. -/
private def explicitFields (numParams : Nat) (c : Name) : MetaM Nat := do
  let ci ← getConstInfo c
  return (go ci.type numParams 0)
where
  go : Expr → Nat → Nat → Nat
    | .forallE _ _ b bi, skip, acc =>
      if skip > 0 then go b (skip - 1) acc
      else go b 0 (if bi.isExplicit then acc + 1 else acc)
    | _, _, acc => acc

/-- What a `match` on a discriminant is split over: the constructors, and how many of their
leading binders are parameters that are not the pattern's. -/
private structure Split where
  ctors : List Name
  numParams : Nat

/-- A pattern a field can be bound by, with no further `match`: `_`, or a name that is not a
constructor's or a `[match_pattern]`'s, which is Lean's rule for a variable in a pattern. -/
private def bindsOnly (p : Syntax) : TermElabM Bool := do
  if p.isOfKind ``Parser.Term.hole then return true
  unless p.isIdent do return false
  let env ← getEnv
  let cands := (← resolveGlobalName p.getId).filter (·.2.isEmpty) |>.map (·.1)
  return !cands.any fun c => (env.find? c).any (·.isCtor) || hasMatchPatternAttribute env c

/-- One row of a `match`: its patterns, in the order of the discriminants, and what it does. -/
private structure Row where
  pats : Array Syntax
  rhs : Syntax
  deriving Inhabited

/-- `_`, as a pattern. -/
private def holePat : Syntax := (mkHole .missing).raw

/-- The cases of a `match` on `discrs`, split on the one at `at_`: for each constructor with a
row, its fields' names and what to do there, which `leaf` writes for a row that binds them
all and `inner` for what takes a `match`. -/
private def splitRows (sp : Split) (others : Array Syntax) (at_ : Nat) (rows : Array Row)
    (leaf : Syntax → TermElabM Syntax)
    (inner : Array Syntax → Array Row → TermElabM Syntax) :
    TermElabM (Option (Array Syntax)) := do
  let mut alts := #[]
  let mut shadowed : Array Syntax := #[]
  let mut heads : Array Head := #[]
  for r in rows do
    let some h ← headOfPat sp.ctors r.pats[at_]! | return none
    heads := heads.push h
  for c in sp.ctors do
    let short := Name.mkSimple c.getString!
    let n ← explicitFields sp.numParams c
    let mut here : Array Row := #[]
    let mut named := false
    for r in rows, h in heads do
      let rest := r.pats.eraseIdx! at_
      match h with
      | .any =>
        here := here.push { pats := (Array.replicate n holePat) ++ rest, rhs := r.rhs }
      | .ctor s args =>
        unless s == short do continue
        named := true
        -- `..` is as many `_` as it leaves out
        let written := args.filter (!·.isOfKind ``Parser.Term.ellipsis)
        if written.size > n then return none
        let pad := Array.replicate (n - written.size) holePat
        here := here.push { pats := written ++ pad ++ rest, rhs := r.rhs }
    if here.isEmpty then continue
    let _ := named
    let first := here[0]!
    let (vars, body) ← do
      if others.isEmpty && (← first.pats.allM bindsOnly) then
        -- it takes everything of this constructor, so no later row gets any
        for r in here.extract 1 here.size do
          shadowed := shadowed.push r.rhs
        pure (first.pats, ← leaf first.rhs)
      else
        let ys ← (Array.range n).mapM fun _ => do
          return (mkIdent (← mkFreshUserName `y)).raw
        pure (ys, ← inner (ys ++ others) here)
    let alt ← `(Lean.Parser.Tactic.inductionAlt| | $(mkIdent short):ident => skip)
    let lhs := alt.raw[0][0].setArg 2 (mkNullNode vars)
    let alt := alt.raw.setArg 0 (mkNullNode #[lhs])
    let alt := alt.setArg 1 (alt[1].setArg 1 body)
    alts := alts.push alt
  -- as Lean says of a row no case reaches: one still in use for another constructor is not that
  for r in rows, h in heads do
    if shadowed.contains r.rhs then
      match h with
      | .ctor .. => logErrorAt r.pats[at_]! (Term.mkRedundantAlternativeMsg none none)
      | .any => pure ()
  return some alts

/-- A `Prop` member that is a definition: its constructors, whose names its `casesOn` has for
its cases.  Lean's `match` has nothing to elaborate its patterns against, `cases` does. -/
private def propMember? (x : Expr) : MetaM (Option Split) := do
  -- as written: one may be a reducible name for what it is built from
  let ty ← instantiateMVars (← inferType x)
  let .const m _ := ty.getAppFn | return none
  let env ← getEnv
  unless (env.find? m).any (·.isDefinition) do return none
  unless ← isProp ty do return none
  let some casesOn := env.find? (m ++ `casesOn) | return none
  let names := casesOn.type.getForallBinderNames
  let some tAt := names.idxOf? `t | return none
  let ctors := (names.drop (tAt + 1)).map (m ++ ·)
  unless ctors.all env.contains do return none
  -- a constructor that is a pattern already is Lean's to compile
  if ctors.any (hasMatchPatternAttribute env) then return none
  return some { ctors, numParams := 0 }

/-- The one discriminant to split at, if any: a local whose type is at such an index, or a
`Prop` member. -/
private def discrToSplit? (discrs : Array Syntax) : TermElabM (Option (Nat × Syntax × Split)) := do
  for d in discrs, i in *...discrs.size do
    unless d[0].isNone do continue
    -- an equation-style definition's comes as `@x`
    let t := if d[1].isOfKind ``Parser.Term.explicit then d[1][1] else d[1]
    unless t.isIdent do continue
    let some x := (← getLCtx).findFromUserName? t.getId | continue
    if let some ii ← indexedAtEncoded? x.toExpr then
      return some (i, t, { ctors := ii.ctors, numParams := ii.numParams })
    if let some sp ← propMember? x.toExpr then return some (i, t, sp)
  return none

/-- Without the discriminants no row asks anything of: `match t, h with | _, .leaf => …` is
about `h`, and splitting that takes `t` with it. -/
private def dropUnasked (discrs : Array Syntax) (at_ : Nat) (rows : Array Row) :
    Array Syntax × Nat × Array Row := Id.run do
  let keep := (Array.range discrs.size).filter fun i =>
    i == at_ || rows.any fun r => !r.pats[i]!.isOfKind ``Parser.Term.hole
  let at_' := keep.idxOf at_
  return (keep.map (discrs[·]!), at_', rows.map fun r => { r with pats := keep.map (r.pats[·]!) })

/-- Without the discriminants every row only names, each name a `let` in its right-hand side:
a `match` on them would rebind what the split's fields are typed by. -/
private def letNamed (discrs : Array Syntax) (at_ : Nat) (rows : Array Row) :
    TermElabM (Array Syntax × Nat × Array Row) := do
  let mut keep : Array Nat := #[]
  let mut named : Array Nat := #[]
  for i in *...discrs.size do
    if i != at_ && !discrs[i]![0].isNone then
      keep := keep.push i
    else if i == at_ then
      keep := keep.push i
    else if ← rows.allM fun r => bindsOnly r.pats[i]! then
      named := named.push i
    else
      keep := keep.push i
  let mut out : Array Row := #[]
  for r in rows do
    let mut rhs := r.rhs
    for i in named.reverse do
      let p := r.pats[i]!
      if p.isIdent then
        rhs := (← `(let $(⟨p⟩):ident := $(⟨discrs[i]![1]⟩):term; $(⟨rhs⟩):term)).raw
    out := out.push { pats := keep.map (r.pats[·]!), rhs }
  return (keep.map (discrs[·]!), keep.idxOf at_, out)

/-- `rhs`, without the `clear% x` an equation-style definition wraps it in: `cases` has taken
`x` already. -/
private partial def withoutClear (x : Syntax) (rhs : Syntax) : Syntax :=
  if rhs.isOfKind ``Parser.Term.clear then
    if rhs[1].getId == x.getId then withoutClear x rhs[3]
    else rhs.setArg 3 (withoutClear x rhs[3])
  else rhs

/-- The rows of `alts`, one to a pattern list. -/
private def rowsOf (alts : Array Syntax) (numDiscrs : Nat) (x : Syntax) : Option (Array Row) := Id.run do
  let mut rows := #[]
  for alt in alts do
    for pl in alt[1].getSepArgs do
      let pats := pl.getSepArgs
      unless pats.size == numDiscrs do return none
      rows := rows.push { pats, rhs := withoutClear x alt[3] }
  return some rows

/-- `match` as a term, at such an index. -/
@[term_elab Lean.Parser.Term.match]
def elabMatchAtIndex : Term.TermElab := fun stx expectedType? => do
  -- no motive of the writer's: this has none to put it in
  unless stx[1].isNone && stx[2].isNone do throwUnsupportedSyntax
  let discrs := stx[3].getSepArgs
  let some (at_, t, sp) ← discrToSplit? discrs | throwUnsupportedSyntax
  let alts := stx[5][0].getArgs
  let some rows := rowsOf alts discrs.size t | throwUnsupportedSyntax
  let (discrs, at_, rows) := dropUnasked discrs at_ rows
  let (discrs, at_, rows) ← letNamed discrs at_ rows
  let others := (discrs.eraseIdx! at_)
  let leaf (rhs : Syntax) : TermElabM Syntax := do
    `(Lean.Parser.Tactic.tacticSeq| exact $(⟨rhs⟩):term)
  let inner (ds : Array Syntax) (rs : Array Row) : TermElabM Syntax := do
    let discrStx ← ds.mapM fun d => do
      if d.isOfKind ``Parser.Term.matchDiscr then return d
      return (← `(Lean.Parser.Term.matchDiscr| $(⟨d⟩):term)).raw
    let alts ← rs.mapM fun r => do
      let alt ← `(Lean.Parser.Term.matchAltExpr| | _ => $(⟨r.rhs⟩):term)
      return alt.raw.setArg 1 (mkNullNode #[mkNullNode (mkSepArray r.pats (mkAtom ","))])
    let m ← `(term| match x with | _ => x)
    let m := m.raw.setArg 3 (mkNullNode (mkSepArray discrStx (mkAtom ",")))
    let m := m.setArg 5 (m[5].setArg 0 (mkNullNode alts))
    `(Lean.Parser.Tactic.tacticSeq| exact $(⟨m⟩):term)
  let some caseAlts ← splitRows sp others at_ rows leaf inner | throwUnsupportedSyntax
  let tac ← `(by cases $(⟨t⟩):ident with $(caseAlts.map (⟨·⟩)):inductionAlt*)
  trace[Mumi.view] "a `match` at an index, by `cases`:{indentD m!"{tac}"}"
  Term.elabTerm tac expectedType?

/-- `match` as tactics, at such an index: each alternative's tactics run on what `cases`
leaves of its case. -/
@[tactic Lean.Parser.Tactic.match, no_fallback]
def evalMatchAtIndex : Tactic := fun stx => withMainContext do
  unless stx[1].isNone && stx[2].isNone do throwUnsupportedSyntax
  let discrs := stx[3].getSepArgs
  let some (at_, t, sp) ← discrToSplit? discrs | throwUnsupportedSyntax
  let alts := stx[5][0].getArgs
  let some rows := rowsOf alts discrs.size t | throwUnsupportedSyntax
  let (discrs, at_, rows) := dropUnasked discrs at_ rows
  let others := discrs.eraseIdx! at_
  -- a field's pattern taking a `match` of its own is for a term's rewrite
  let leaf (rhs : Syntax) : TermElabM Syntax := pure rhs
  let inner (_ : Array Syntax) (_ : Array Row) : TermElabM Syntax := throwUnsupportedSyntax
  let some caseAlts ← Term.withoutErrToSorry <| splitRows sp others at_ rows leaf inner
    | throwUnsupportedSyntax
  evalTactic (← `(tactic| cases $(⟨t⟩):ident with $(caseAlts.map (⟨·⟩)):inductionAlt*))

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
