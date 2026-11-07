import Mumi

/-!
# A specification-driven harness for Mumi's blocks

`mumi_spec mutual … end` (or a single `inductive`) elaborates the block, then
checks what it declared against what Lean's own rules say such a block should
declare -- computed from the block as written and nothing else.  For a block
Lean takes, that is what Lean does; for one it refuses, it is what Lean would do
were the restriction lifted:

* each type former, at the universe written (one up for an induction-recursion
  when `mumi.mahlo` is off, the graph encoding's cost);
* each constructor: the shared parameters implicit, the fields as written; a
  parameter that varies is an index, which the constructor binds implicitly;
* one recursion over the whole block, as a `mutual` has (its recursion at a
  nested target, `X.rec_k`, owed by name only where a displayed motive mentions
  it): motives for the data
  members in the order written, then each nested application in the order met,
  an inductive of a mutual block bringing the block's others with it as the kernel does,
  then the `Prop` members (`motive` alone when there is one).  A `Prop` member's
  motive is *displayed*: at each index of data type it takes the value the data
  recursion produced there, and into `Prop` unless Lean would let it eliminate
  into any sort.  The minor premises follow the same order, named by their
  constructors, binding the fields as the constructor does and then a
  hypothesis `f_ih` at each field of the block -- data or proof; the major `t`,
  the indices implicit, the universes the motive's and then the member's.
  Where a hypothesis at a proof field cannot be stated, its index going
  through what the recursion cannot follow, the block is a *gap*: it is to be
  rejected, or, under `mumi.partialRecursors`, declared without it;
* `X.recOn` and `X.casesOn` as Lean derives them, `X.c.inj` and `X.c.injEq` as
  Lean states them;
* `cases` on every member, and `induction` on a lone one;
* of each data member's constructors, as Lean's own behave: `X.c.sizeOf_spec` as Lean
  states it, `X.ctorIdx` by `rfl`, and the tactics on an equation between constructors --
  at two different ones `contradiction`, `cases`, `rcases`, `obtain`, `injections`, `simp`
  and `X.noConfusion` refute it, at one
  `injection`, `injections`, `cases`, `rcases` and `obtain` give the equations of its fields;
* `match` on each member, as a term, a tactic and a `fun`; and `match` and `cases` on a term
  whose index is a constructor of a data member, at a type the check declares for the purpose;
* each decoder of an induction-recursion, as written, and its equations;
* no axiom in any of it, but `propext` in an `injEq` and `IR.mahlo` under
  `mumi.mahlo`.

Types must agree up to definitional equality, binder names, annotations and
universes exactly, and no internal name (`_ir_…`, `_nested…`, `nested_…`) may
show where a reader would see it.  Every rule -- a recursor's or a `casesOn`'s
at a constructor, a decoder's at a clause -- is to hold by `rfl` in the kernel,
unless listed `(simp := [...])` (only by `simp` with its lemma) or
`(unproven := [...])` (no lemma states it).  `(xfail := [rec, injEq, …])` marks
the kinds of claim a block is known to fail: they are then not reported, but a
listed kind that holds is.  `(rejects)` says the block is to be refused.
-/

namespace Mumi.Spec
open Lean Elab Command Term Meta

/-! ## Claims and problems -/

/-- The kinds of claim the specification makes: what a test marks known to fail. -/
inductive Claim where
  | types | ctors | recursor | rules | recOnForm | casesOnForm | injEq | cases | induction | decoders | axioms | gap
  | sizeOf | ctorIndex | discr | inject | matching
  deriving BEq, Inhabited

def Claim.all : Array (Name × Claim) :=
  #[(`types, .types), (`ctors, .ctors), (`rec, .recursor), (`rules, .rules), (`recOn, .recOnForm),
    (`casesOn, .casesOnForm), (`injEq, .injEq), (`cases, .cases), (`induction, .induction),
    (`decoders, .decoders), (`axioms, .axioms), (`gap, .gap),
    (`sizeOf, .sizeOf), (`ctorIdx, .ctorIndex), (`discr, .discr), (`inject, .inject), (`matching, .matching)]

instance : ToString Claim where
  toString c := ((Claim.all.find? (·.2 == c)).map (·.1.toString)).getD "?"

register_option mumi.spec.showXFail : Bool := {
  defValue := false
  descr := "report the problems of the claims a `mumi_spec` marks known to fail, as information"
}

/-- One run of the specification: what it found, and what the test says of it. -/
structure Run where
  problems : IO.Ref (Array (Claim × MessageData))
  /-- The rules stated, so that an option naming another is caught. -/
  stated : IO.Ref (Array Name)
  /-- The public constants checked, for the axiom audit. -/
  checked : IO.Ref (Array Name)
  /-- The rules that hold only by `simp`, by their lemmas' names. -/
  simpRules : Array Name
  /-- The rules no lemma states. -/
  unproven : Array Name
  /-- Under `mumi.partialRecursors`: a hypothesis that cannot be stated is left out. -/
  partialRecs : Bool

private def problem (r : Run) (c : Claim) (m : MessageData) : MetaM Unit := r.problems.modify (·.push (c, m))

/-! ## Reading the block -/

/-- A member as written. -/
structure Member where
  name : Name
  /-- The declaration's syntax. -/
  decl : Syntax
  prop : Bool
  /-- The names of all the block's members. -/
  block : Array Name
  /-- Its binders beyond those all members share: indices, to the encoding. -/
  extra : Array Syntax := #[]
  deriving Inhabited

private def isInductive (e : Syntax) := e[1].isOfKind ``Parser.Command.«inductive»

/-! ## Comparing -/

/-- Whether a name is internal to an encoding. -/
private def internal (n : Name) : Bool :=
  n.components.any fun c =>
    let s := c.toString
    s.startsWith "_ir_" || s.startsWith "_nested" || s.startsWith "nested_"

/-- Internal names shown in `e`, as a reader sees it: of binders, of constants,
of projected structures -- but not in an implicit argument, which display
hides, and which may hold the encoding a decoder unfolds to where an index
term was elaborated against it. -/
private partial def leaks (e : Expr) : MetaM (Array Name) := do
  let binder (n : Name) := if internal n && !n.hasMacroScopes then #[n] else #[]
  match e with
  | .forallE n t b bi | .lam n t b bi =>
    let inT ← leaks t
    withLocalDecl n bi t fun x => return binder n ++ inT ++ (← leaks (b.instantiate1 x))
  | .letE n t v b _ =>
    let outer := binder n ++ (← leaks t) ++ (← leaks v)
    withLetDecl n t v fun x => return outer ++ (← leaks (b.instantiate1 x))
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    let info ← try some <$> getFunInfoNArgs f args.size catch _ => pure none
    let mut out ← if f.isApp then pure #[] else leaks f
    for i in [:args.size] do
      let shown : Bool := match info.bind (·.paramInfo[i]?) with
        | some p => p.binderInfo.isExplicit
        | none => true
      if shown then out := out ++ (← leaks args[i]!)
    return out
  | .const c _ => return if internal c then #[c] else #[]
  | .proj s _ x => return (if internal s then #[s] else #[]) ++ (← leaks x)
  | .mdata _ x => leaks x
  | _ => return #[]

/-- The binders of a telescope: names and annotations, down to `depth`. -/
private partial def skeleton (e : Expr) (depth : Nat) : List (Name × BinderInfo × List (Name × BinderInfo)) :=
  match e with
  | .forallE n t b bi =>
    let inner := if depth > 0 then (skeleton t (depth - 1)).map fun (n, bi, _) => (n, bi) else []
    (n, bi, inner) :: skeleton b depth
  | _ => []

/-- A binder's name in its brackets. -/
private def bracketed (bi : BinderInfo) (n : String) : String :=
  match bi with
  | .implicit => "{" ++ n ++ "}"
  | .strictImplicit => "⦃" ++ n ++ "⦄"
  | .instImplicit => "[" ++ n ++ "]"
  | _ => "(" ++ n ++ ")"

/-- Checks the constant `c` against the expected type: definitionally equal,
the same binders down a level (minor premises), the universes `levels` if
given, nothing internal shown. -/
def checkConst (r : Run) (claim : Claim) (c : Name) (expected : Expr) (innerNames := true)
    (levels : Option (List Name) := none) : MetaM Bool := do
  let before := (← r.problems.get).size
  checkConst' r claim c expected innerNames levels
  return (← r.problems.get).size == before
where
  checkConst' (r : Run) (claim : Claim) (c : Name) (expected : Expr) (innerNames : Bool)
      (levels : Option (List Name)) : MetaM Unit := do
  let some ci := (← getEnv).find? c | return ← problem r claim m!"`{c}` is not declared"
  r.checked.modify (·.push c)
  if let some ls := levels then
    unless ci.levelParams == ls do problem r claim m!"`{c}` has universes {ci.levelParams}, expected {ls}"
  -- the block's universes are the ones the test wrote; another, the motive's, is to be found
  let written := (collectLevelParams {} expected).params
  let actual ← instantiateTypeLevelParams ci.toConstantVal
    (← ci.levelParams.mapM fun n => if written.contains n then pure (mkLevelParam n) else mkFreshLevelMVar)
  let leaked := (← leaks ci.type).toList.eraseDups
  unless leaked.isEmpty do problem r claim m!"`{c}` shows internal names: {leaked}"
  let same ← try withReducible (isDefEq expected actual) <||> isDefEq expected actual catch _ => pure false
  unless same do
    problem r claim m!"`{c}` has type{indentExpr actual}\nexpected{indentExpr expected}"
    return
  let depth := if innerNames then 1 else 0
  let e := skeleton (← instantiateMVars expected) depth
  let a := skeleton ci.type depth
  -- an inaccessible name expected is any name shown
  let name (x y : Name) := x.hasMacroScopes || x == y
  let bind (x y : Name × BinderInfo) := name x.1 y.1 && x.2 == y.2
  let same := e.length == a.length && (e.zip a).all fun (x, y) =>
    bind (x.1, x.2.1) (y.1, y.2.1) && x.2.2.length == y.2.2.length && (x.2.2.zip y.2.2).all fun (x, y) => bind x y
  unless same do
    let one (x : Name × BinderInfo) : String := bracketed x.2 x.1.eraseMacroScopes.toString
    let render (s : List (Name × BinderInfo × List (Name × BinderInfo))) : MessageData :=
      m!"{s.map fun x => one (x.1, x.2.1) ++ (if x.2.2.isEmpty then "" else " " ++ toString (x.2.2.map one))}"
    problem r claim m!"`{c}` binds{indentD (render a)}\nexpected{indentD (render e)}"

/-! ## Elaborating what was written -/

/-- `k` with the binders of `xs` given the annotation `bi`. -/
private def withInfos {α} (xs : Array Expr) (bi : BinderInfo → BinderInfo) (k : TermElabM α) : TermElabM α := do
  let infos ← xs.mapM fun x => do return (x.fvarId!, bi (← x.fvarId!.getDecl).binderInfo)
  withNewBinderInfos infos k

/-- The names a binder group binds. -/
private def groupNames (g : Syntax) : Array Name := g[1].getArgs.map (·.getId)

/-- The annotation of each binder the groups `gs` bind, as written. -/
private def groupInfos (gs : Array Syntax) : Array BinderInfo :=
  gs.flatMap fun g =>
    let bi := if g.isOfKind ``Parser.Term.implicitBinder then BinderInfo.implicit
      else if g.isOfKind ``Parser.Term.strictImplicitBinder then .strictImplicit
      else if g.isOfKind ``Parser.Term.instBinder then .instImplicit
      else .default
    if g.isOfKind ``Parser.Term.instBinder then #[bi] else (groupNames g).map fun _ => bi

/-- How many binder groups all the declarations `ds` begin with alike. -/
private def sharedGroups (ds : Array Syntax) : Nat := Id.run do
  let groups := ds.map (·[2][0].getArgs)
  let mut n := 0
  while groups.all (fun g => n < g.size) && groups.all (fun g => groupNames g[n]! == groupNames groups[0]![n]!) do
    n := n + 1
  return n

/-- The type after a member's shared parameters: its own further binders, then
what its `: T` says; if nothing, `Type _`, whose universe Lean infers. -/
private def declType (m : Member) : TermElabM Expr := do
  let d := m.decl
  Term.elabBinders m.extra fun xs => do
    let ty ← if d[2][1].getNumArgs == 0 then pure (mkSort (.succ (← mkFreshLevelMVar))) else Term.elabType d[2][1][0][1]
    mkForallFVars xs ty

/-- The occurrences of the carriers `names` in `e`, at any depth, applied or not
(and partially).  Each shared subterm is visited once: in lower mode an index
term elaborated against a decoder holds the encoding it unfolds to, a small
graph but an enormous tree. -/
private def carrierApps (names : Array Name) (e : Expr) : MetaM (Array Expr) := do
  let out ← IO.mkRef #[]
  e.forEachWhere (fun sub => names.any sub.getAppFn.isConstOf) fun sub => out.modify (·.push sub)
  out.get

/-- Each constructor's type as elaborated, over the parameters, by member and
constructor: elaborating it again, in lower mode, is costly. -/
initialize ctorTypes : IO.Ref (Std.HashMap (Name × Name) (Expr × Nat)) ← IO.mkRef {}

/-- A constructor's fields and conclusion, elaborated once where the parameters
(or some of them) are bound: the member's own further parameters, implicit,
then its fields as written. -/
private def elabCtor {α} (m : Member) (params : Array Expr) (c : Syntax) (k : Array Expr → Expr → TermElabM α) : TermElabM α := do
  let key := (m.name, c[3].getId)
  let (ty, n) ← match (← ctorTypes.get)[key]? with
    | some e => pure e
    | none =>
      -- a member's own further parameters are its constructors' implicit fields
      let e ← Term.elabBinders m.extra fun own => withInfos own (fun _ => .implicit) do
        let params := params ++ own
        -- a name a constructor's type leaves unbound is an implicit field of it, as in Lean's
        Term.withAutoBoundImplicit <| Term.elabBinders c[4][0].getArgs fun fs => do
          let ty ← if c[4][1].getNumArgs == 0 then pure (mkAppN (← mkConstWithLevelParams m.name) params)
            else Term.elabType c[4][1][0][1]
          -- a member's parameters left implicit are the declaration's, as Lean fixes them
          for e in (← fs.mapM fun f => inferType f).push ty do
            let e ← instantiateMVars e
            for app in ← carrierApps m.block e do
              -- and so are its universes
              discard <| isDefEq app.getAppFn (← mkConstWithLevelParams app.getAppFn.constName!)
              let args := app.getAppArgs
              for j in [:min args.size params.size] do
                if let .mvar g := args[j]! then
                  unless ← g.isAssigned do discard <| isDefEq args[j]! params[j]!
          Term.synthesizeSyntheticMVarsNoPostponing
          let ty ← instantiateMVars ty
          let fs ← Term.addAutoBoundImplicits fs none
          forallTelescope ty fun more res => do
            let fields := own ++ fs ++ more
            return (← mkForallFVars fields res, fields.size)
      ctorTypes.modify (·.insert key e)
      pure e
  forallBoundedTelescope ty n k

/-- Where a nested application of the block is, as Lean's kernel takes it --
the inductive at its parameters, which name a member (`List U`, `Vector U` of
`Vector U 3`) -- and abstracted over the fields and indices those name (`fun Γ =>
List (Ty Γ)`, which Lean's kernel does not take): the copy's indices before
its own. -/
private def nestedHead? (members : Array Name) (params : Array Expr) (t : Expr) : MetaM (Option Expr) := do
  let t ← instantiateMVars t
  let .const i _ := t.getAppFn | return none
  if members.contains i then return none
  let some (.inductInfo info) := (← getEnv).find? i | return none
  let n := mkAppN t.getAppFn (t.getAppArgs.extract 0 info.numParams)
  unless members.any (fun m => (n.find? (·.isConstOf m)).isSome) do return none
  if n.hasLooseBVars then return none
  -- the locals it names, and those their types name, in the order bound
  let mut locals : Array FVarId := #[]
  let mut todo := (collectFVars {} n).fvarIds.filter fun x => !params.contains (mkFVar x)
  while h : 0 < todo.size do
    let x := todo.back
    todo := todo.pop
    if locals.contains x then continue
    locals := locals.push x
    for y in (collectFVars {} (← instantiateMVars (← x.getType))).fvarIds do
      unless params.contains (mkFVar y) do todo := todo.push y
  let lctx ← getLCtx
  let sorted := (locals.qsort fun a b => (lctx.get! a).index < (lctx.get! b).index).map mkFVar
  mkLambdaFVars sorted n

/-- A nested target's application, under its locals' binders. -/
private def nestedBody : Expr → Expr
  | .lam _ _ b _ => nestedBody b
  | a => a

/-- How many locals a nested target is abstracted over. -/
private def nestedLocals : Expr → Nat
  | .lam _ _ b _ => 1 + nestedLocals b
  | _ => 0

/-- `pat`, with loose bound variables below `n` for the locals, at `e`: the
values found for them.  Under `depth` binders of the pattern (a local may sit in
`Sigma`'s `fun _ => …`), the lowest variables are those binders', which stand for
themselves, and a local's value cannot mention them. -/
private partial def matchPat (n : Nat) (pat e : Expr) (acc : Array (Option Expr)) (depth : Nat := 0) :
    Option (Array (Option Expr)) :=
  match pat, e with
  | .bvar i, _ =>
    if i < depth then
      if e == pat then some acc else none
    else if i - depth < n then
      if e.hasLooseBVars then none else
      match acc[i - depth]! with
      | none => some (acc.set! (i - depth) (some e))
      | some v => if v == e then some acc else none
    else none
  | .app f a, .app f' a' => (matchPat n f f' acc depth).bind (matchPat n a a' · depth)
  | .lam _ d b _, .lam _ d' b' _ | .forallE _ d b _, .forallE _ d' b' _ =>
    (matchPat n d d' acc depth).bind (matchPat n b b' · (depth + 1))
  -- a constant at universes written differently is the same constant
  | .const c _, .const c' _ => if c == c' then some acc else none
  | .sort _, .sort _ => some acc
  | _, _ => if !pat.hasLooseBVars && pat == e then some acc else none

/-- The arguments a nested target's motive takes of `t`, if it is a type of the
target: its locals' values, then its indices. -/
private def nestedArgs? (a t : Expr) : Option (Array Expr) := Id.run do
  let body := nestedBody a
  let n := nestedLocals a
  let np := body.getAppNumArgs
  unless t.getAppFn.constName? == body.getAppFn.constName? && t.getAppNumArgs ≥ np do return none
  let mut acc : Array (Option Expr) := .replicate n none
  for (p, e) in body.getAppArgs.zip (t.getAppArgs.extract 0 np) do
    let some acc' := matchPat n p e acc | return none
    acc := acc'
  let vals := (Array.range n).filterMap fun i => acc[n - 1 - i]!
  unless vals.size == n do return none
  return some (vals ++ t.getAppArgs.extract np t.getAppNumArgs)

/-! ## Rules -/

/-- How a rule held. -/
inductive Held where
  | rfl | simp | no
  deriving BEq

instance : ToString Held where
  toString
    | .rfl => "by `rfl`"
    | .simp => "only by `simp` with its lemma"
    | .no => "neither by `rfl` nor by `simp` with a lemma"

/-- Whether the closed `stmt` holds by `rfl` in the kernel: `∀ …, lhs = rhs`. -/
private def kernelRfl (stmt : Expr) : TermElabM Bool := do
  let stmt ← Term.levelMVarToParam (← instantiateMVars stmt)
  -- the kernel alone: Meta's unifier may wander into an encoding
  try
    let v ← forallTelescope stmt fun xs body => do
      let some (_, lhs, _) := body.eq? | throwError "not an equation"
      mkLambdaFVars xs (← mkEqRefl lhs)
    let lps := (collectLevelParams {} stmt).params.toList
    let decl := Declaration.thmDecl { name := `_spec_rfl_check, levelParams := lps, type := stmt, value := v }
    pure (Kernel.Environment.addDecl (← getEnv).toKernelEnv (← getOptions) decl matches .ok _)
  catch _ => pure false

/-- Whether `stmt` holds by `rfl` in the kernel, by `simp only [rule]`, or neither. -/
private def holds (stmt : Expr) (rule : Name) : TermElabM Held := do
  if ← kernelRfl stmt then return .rfl
  unless (← getEnv).contains rule do return .no
  let stmt ← Term.levelMVarToParam (← instantiateMVars stmt)
  let saved ← Core.getMessageLog
  let bySimp ← withoutModifyingEnv do
    try
      let g ← mkFreshExprMVar stmt
      let tac ← `(tactic| (intros; simp only [$(mkIdent rule):ident]))
      let rest ← Term.withoutErrToSorry do
        Lean.Elab.Tactic.run g.mvarId! (Lean.Elab.Tactic.evalTactic tac)
      pure rest.isEmpty
    catch _ => pure false
  Core.setMessageLog saved
  return if bySimp then .simp else .no

/-- Records how a rule held against what the test says it should. -/
private def expectRule (r : Run) (rule : Name) (stmt : Expr) : TermElabM Unit := do
  r.stated.modify (·.push rule)
  if (← getEnv).contains rule then r.checked.modify (·.push rule)
  let h ← holds stmt rule
  let want := if r.simpRules.contains rule then Held.simp
    else if r.unproven.contains rule then Held.no else Held.rfl
  unless h == want do
    problem r .rules m!"the rule `{rule}`{indentExpr (← instantiateMVars stmt)}\nholds {h}, expected {want}"

/-- The lemma of rule `base` (`X.rec`, `X.casesOn`, `d`) at constructor `c`: `X.rec_c`. -/
private def ruleName (base : Name) (c : Name) : Name :=
  base.getPrefix ++ Name.mkSimple (base.getString! ++ "_" ++ c.getString!)

/-! ## The recursion -/

/-- What the specification reads of the block, its parameters bound. -/
structure Block where
  members : Array Member
  /-- Each type former's type after the parameters. -/
  tys : Array Expr
  params : Array Expr
  /-- The parameters before this one are uniform; from it on they vary. -/
  uniform : Nat

/-- A target of the recursion: a member, or a nested application abstracted
over the locals it names. -/
inductive Target where
  | member (k : Nat)
  | nested (a : Expr)
  deriving Inhabited

/-- Whether Lean lets the `Prop` members `props` eliminate into any sort,
declared on their own: one of them, with no constructor, or one whose fields
are proofs or appear in its indices. -/
private def largeElim (b : Block) (props : Array Nat) : TermElabM Bool := do
  let #[k] := props | return false
  let m := b.members[k]!
  match m.decl[4].getArgs with
  | #[] => return true
  | #[c] => elabCtor m b.params c fun fields res => do
      let res ← instantiateMVars res
      fields.allM fun f => do
        return (← isProp (← inferType f)) || res.getAppArgs.contains f
  | _ => return false

/-- The hypotheses bound so far: at which field, which hypothesis. -/
private abbrev Hyps := Array (Expr × Expr)

/-- The minor premises bound so far: at which constructor, which minor, how
many of the constructor's arguments come before its fields, and for a nested
target over locals, the target, at whose type the locals are read. -/
private abbrev Minors := Array (Name × Expr × Nat × Option Expr)

/-- The data recursion's value at `e`, where the recursion can follow it: a
field, by its hypothesis; a constructor of the block whose minor premise is
bound, at such values; nothing else. -/
private partial def valueOf (minors : Minors) (hyps : Hyps) (e : Expr) : MetaM (Option Expr) := do
  let e ← instantiateMVars e
  let f := e.getAppFn
  let args := e.getAppArgs
  if f.isFVar then
    return (hyps.find? (·.1 == f)).map fun (_, h) => mkAppN h args
  let .const c _ := f | return none
  let ty ← instantiateMVars (← inferType e)
  -- the minor at the constructor; of a nested target over locals, the one whose type `e` has
  let found := minors.findSome? fun (n, m, drop, a?) =>
    if n != c then none else match a? with
      | none => some (m, drop, #[])
      | some a => (nestedArgs? a ty).map fun vals => (m, drop, vals.extract 0 (nestedLocals a))
  let some (m, drop, locals) := found | return none
  let fieldArgs := locals ++ args.extract drop args.size
  let mut v := mkAppN m fieldArgs
  let mut ty ← instantiateForall (← inferType m) fieldArgs
  -- the hypotheses its minor premise takes there: data values, and proofs of
  -- displayed motives where the hypothesis at the proof is at hand
  while ty.isForall do
    let .forallE _ d body _ := ty | break
    let some h ← forallTelescope d fun dom concl => do
        let some val ← valueOf minors hyps concl.appArg! | return none
        return some (← mkLambdaFVars dom val)
      | return none
    v := mkApp v h
    ty := body.instantiate1 h
  return some v

/-- What there is at a field: no hypothesis, one that cannot be stated, or one. -/
private inductive Hyp where
  | none | gap | some (ty : Expr)

/-- `k` with a hypothesis bound after the fields at each that `hypAt` gives one,
each over those before it; and the fields where one cannot be stated. -/
private partial def bindHyps {α} (fields : Array Expr) (hypAt : Hyps → Expr → TermElabM Hyp)
    (k : Hyps → Array Name → TermElabM α) (i : Nat := 0) (hyps : Hyps := #[]) (gaps : Array Name := #[]) :
    TermElabM α := do
  if h : i < fields.size then
    let f := fields[i]
    match ← hypAt hyps f with
    | .none => bindHyps fields hypAt k (i + 1) hyps gaps
    | .gap => bindHyps fields hypAt k (i + 1) hyps (gaps.push (← f.fvarId!.getDecl).userName)
    | .some ty =>
      -- `f_ih`, inaccessible where the field is, as Lean names it
      withLocalDeclD ((← f.fvarId!.getDecl).userName.appendAfter "_ih") ty fun ih =>
        bindHyps fields hypAt k (i + 1) (hyps.push (f, ih)) gaps
  else k hyps gaps

/-- The block's recursion: its recursors, `recOn`s and `casesOn`s, and their rules. -/
private def recursion (r : Run) (b : Block) (targets : Array Target) (large : Bool) : TermElabM Unit := do
  let { members, tys, params, uniform } := b
  let uniformPs := params.extract 0 uniform
  let promotedPs := params.extract uniform params.size
  let u := Level.param `u_spec
  -- whether a target is a proposition: a `Prop` member, or a nested one in `Prop`
  let props ← targets.mapM fun t => match t with
    | .member k => pure members[k]!.prop
    | .nested a => lambdaTelescope a fun _ n => do forallTelescope (← inferType n) fun _ s => pure s.isProp
  let isPropT (t : Nat) : Bool := props[t]!
  -- the sort a target's motive lands in
  let sortOf (t : Nat) : Expr := if isPropT t && !large then mkSort .zero else mkSort u
  let anySort := (List.range targets.size).any fun t => !(sortOf t).isProp
  -- `motive_1`, `motive_2`, … as Lean names a mutual block's; `motive` alone
  let motiveName (t : Nat) := Name.mkSimple (if targets.size == 1 then "motive" else "motive_" ++ toString (t + 1))
  -- the first member's name, which a nested target's recursor is under
  let firstName := (targets.findSome? fun t => match t with | .member k => some members[k]!.name | _ => none).getD .anonymous
  -- `rec_k` counts the nested targets alone: a `Prop` member may sit among them
  let recOf (t : Nat) : Name := match targets[t]! with
    | .member k => members[k]!.name ++ `rec
    | .nested _ => firstName ++ Name.mkSimple ("rec_" ++ toString
        ((targets.toList.take (t + 1)).countP fun x => match x with | .nested _ => true | _ => false))
  -- of a target over locals and a narrower one, the narrower: `List (W 0)` is one
  -- type where `fun n => List (W n)` is a family, and is its own target
  let targetOf (t : Expr) : Option Nat := Id.run do
    let mut best : Option (Nat × Nat) := none
    for j in [:targets.size] do
      let locals? := match targets[j]! with
        | .member k => if t.getAppFn.isConstOf members[k]!.name then some 0 else none
        | .nested a => if (nestedArgs? a t).isSome then some (nestedLocals a) else none
      if let some n := locals? then
        match best with
        | some (_, m) => if n < m then best := some (j, n)
        | none => best := some (j, n)
    return best.map (·.1)
  -- the index arguments a target's motive takes of a type of it
  let motiveArgs (j : Nat) (t : Expr) : Array Expr := match targets[j]! with
    | .member _ => t.getAppArgs.extract uniform t.getAppArgs.size
    | .nested a => (nestedArgs? a t).getD #[]
  -- the constructors of each target: name, constant, arguments before the fields
  let ctorsOf (t : Nat) : TermElabM (Array (Name × Name × Nat)) := do
    match targets[t]! with
    | .member k => return members[k]!.decl[4].getArgs.map fun c =>
        (c[3].getId, members[k]!.name ++ c[3].getId, uniform)
    | .nested a =>
      let n := nestedBody a
      let .const ind _ := n.getAppFn | return #[]
      let some (.inductInfo info) := (← getEnv).find? ind | return #[]
      return info.ctors.toArray.map fun c => (Name.mkSimple c.getString!, c, n.getAppNumArgs)
  -- constructor `ci` of target `t`, its arguments bound: `k before ctor fields indices`,
  -- where `before` are the parameters that vary, which a minor premise binds
  -- implicitly before the fields
  let atCtor {α} (t ci : Nat) (k : Array Expr → Expr → Array Expr → Array Expr → TermElabM α) : TermElabM α := do
    match targets[t]! with
    | .member m =>
      let m := members[m]!
      let c := m.decl[4].getArgs[ci]!
      elabCtor m params c fun fields res => do
        k promotedPs (mkAppN (← mkConstWithLevelParams (m.name ++ c[3].getId)) (params ++ fields)) fields (motiveArgs t res)
    | .nested a =>
      lambdaTelescope a fun locals n => do
      let .const ind lvls := n.getAppFn | throwError "not a nested application"
      let some (.inductInfo info) := (← getEnv).find? ind | throwError "not an inductive"
      let ctor := info.ctors[ci]!
      let cty ← instantiateForall ((← getConstInfo ctor).instantiateTypeLevelParams lvls) n.getAppArgs
      -- the locals are the copy's fields before the container's own, as a field
      -- an index is read off is: explicit, with its hypothesis
      forallTelescope cty fun fields res =>
        k #[] (mkAppN (mkConst ctor lvls) (n.getAppArgs ++ fields)) (locals ++ fields)
          (locals ++ res.getAppArgs.extract n.getAppNumArgs res.getAppNumArgs)
  -- at which of a `Prop` target's indices its motive takes a data value
  let displayAt ← (Array.range targets.size).mapM fun t => do
    match targets[t]! with
    | .member k =>
      if !members[k]!.prop then return #[]
      forallTelescope tys[k]! fun idx _ => (promotedPs ++ idx).mapM fun i => do
        return (targetOf (← instantiateMVars (← inferType i))).filter (!isPropT ·)
    -- a nested proposition displays as a member does: `Tree.WF R a` takes the
    -- value at its `Tree R`
    | .nested a =>
      if !isPropT t then return #[]
      lambdaTelescope a fun locals n => do
        forallTelescope (← inferType n) fun idx _ => (locals ++ idx).mapM fun i => do
          return (targetOf (← instantiateMVars (← inferType i))).filter (!isPropT ·)
  -- a motive at index arguments, the data values there, and a major
  let motiveApp (motives : Array Expr) (t : Nat) (args : Array Expr) (vals : Array (Option Expr)) (major : Expr) : Expr :=
    Id.run do
      let mut out := #[]
      for i in [:args.size] do
        out := out.push args[i]!
        if let some (some v) := vals[i]? then out := out.push v
      mkAppN motives[t]! (out.push major)
  -- the motive of target `t` over its indices `ixs` and a major of type `major`;
  -- a displayed one takes after each index of data type the value there
  let motiveOver (t : Nat) (prev ixs : Array Expr) (major : Expr) : TermElabM Expr := do
      let mut shown := #[]
      for i in [:ixs.size] do
        if let some (some j) := displayAt[t]![i]? then
          let ty ← instantiateMVars (← inferType ixs[i]!)
          shown := shown.push (i, mkAppN prev[j]! ((motiveArgs j ty).push ixs[i]!))
      -- nothing is said of a value by name: its binder is inaccessible
      let v ← mkFreshUserName `v
      withLocalDecls (shown.map fun (_, ty) => (v, BinderInfo.default, fun _ => pure ty)) fun vs => do
      withLocalDeclD `t major fun x => do
        let mut binders := #[]
        for i in [:ixs.size] do
          binders := binders.push ixs[i]!
          if let some n := shown.findIdx? (·.1 == i) then binders := binders.push vs[n]!
        mkForallFVars (binders.push x) (sortOf t)
  -- a motive is implicit, as there is a minor premise to read it off -- explicit
  -- in a block with no constructor at all, as `False.rec`'s is
  let noCtors ← (Array.range targets.size).allM fun t => return (← ctorsOf t).isEmpty
  let motiveInfo := if noCtors then BinderInfo.default else BinderInfo.implicit
  let motiveDecls := (Array.range targets.size).map fun t =>
    (motiveName t, motiveInfo, fun (prev : Array Expr) => do
      match targets[t]! with
      | .member k =>
        forallTelescope tys[k]! fun idx _ => do
          let major := mkAppN (← mkConstWithLevelParams members[k]!.name) (params ++ idx)
          motiveOver t prev (promotedPs ++ idx) major
      | .nested a => lambdaTelescope a fun locals n => do
        forallTelescope (← inferType n) fun idx _ => motiveOver t prev (locals ++ idx) (mkAppN n idx))
  withLocalDecls motiveDecls fun motives => do
  -- the hypothesis at a field: at a field of a target, the motive at its
  -- indices, their data values, and the field
  let hypAt (minors : Minors) (hyps : Hyps) (f : Expr) : TermElabM Hyp := do
    forallTelescope (← inferType f) fun dom ty => do
      let ty := (← instantiateMVars ty).headBeta
      let some j := targetOf ty | return .none
      let args := motiveArgs j ty
      let mut vals := #[]
      for i in [:args.size] do
        if let some (some _) := displayAt[j]![i]? then
          let some v ← valueOf minors hyps args[i]! | return .gap
          vals := vals.push (some v)
        else vals := vals.push none
      return .some (← mkForallFVars dom (motiveApp motives j args vals (mkAppN f dom)))
  -- the minor premises, in target order, each over those before it; where one
  -- cannot be stated, `True` stands for it and the gap is recorded
  let gaps ← IO.mkRef (#[] : Array MessageData)
  let hypGaps ← IO.mkRef (#[] : Array (Array Name))
  let mut minorDecls : Array (Name × BinderInfo × (Array Expr → TermElabM Expr)) := #[]
  let mut owners : Array (Name × Nat × Option Expr) := #[]
  for t in [:targets.size] do
    let cs ← ctorsOf t
    for ci in [:cs.size] do
      let (c, const, drop) := cs[ci]!
      let before := owners
      minorDecls := minorDecls.push (c, .default, fun prev => do
        let bound : Minors := (before.zip prev).map fun ((n, d, a), m) => (n, m, d, a)
        atCtor t ci fun promoted ctor fields idx => do
          bindHyps fields (hypAt bound) fun hyps missing => do
            hypGaps.modify (·.push missing)
            for g in missing do gaps.modify (·.push m!"the hypothesis at `{g}` in `{const}`")
            let mut vals := #[]
            for i in [:idx.size] do
              if let some (some _) := displayAt[t]![i]? then
                let some v ← valueOf bound hyps idx[i]! | do
                  gaps.modify (·.push m!"the conclusion of `{const}`, at {idx[i]!}")
                  return mkConst ``True
                vals := vals.push (some v)
              else vals := vals.push none
            let body ← mkForallFVars (hyps.map (·.2)) (motiveApp motives t idx vals ctor)
            withInfos promoted (fun _ => .implicit) (mkForallFVars (promoted ++ fields) body))
      owners := owners.push (const, drop, match targets[t]! with | .nested a => some a | _ => none)
  withLocalDecls minorDecls fun minors => do
  let gaps ← gaps.get
  unless gaps.isEmpty do
    unless r.partialRecs do
      problem r .gap m!"the recursor cannot state{indentD (MessageData.joinSep gaps.toList "\n")}\n\
        so the block is to be rejected, or declared without them under `mumi.partialRecursors`"
      return
  let hypGaps ← hypGaps.get
  -- a recursor's universes: the motive's first, `u` or the first `u_i` the member's do not use
  let levelsOf (owner : Name) (sorted : Bool) (joint := true) : TermElabM (List Name) := do
    -- a recursor over the whole block mentions every member, so it carries the
    -- universes of all of them, as Lean's do; a case split only its own
    let mut own : List Name := []
    if !joint then own := (← getConstInfo owner).levelParams
    if joint then
      for m in members do
        for l in (← getConstInfo m.name).levelParams do
          unless own.contains l do own := own ++ [l]
    let elim := (List.range (own.length + 1)).map (fun i => if i == 0 then `u else Name.mkSimple s!"u_{i}")
      |>.find? (!own.contains ·) |>.getD `u
    return if sorted then elim :: own else own
  let ownerOf (t : Nat) := match targets[t]! with | .member k => members[k]!.name | .nested _ => firstName
  let recAt (t : Nat) (args : Array Expr) : TermElabM Expr := do
    instantiateMVars (← mkAppOptM (recOf t) ((uniformPs ++ motives ++ minors ++ args).map some))
  let implicit (bi : BinderInfo) := if bi == .instImplicit then bi else .implicit
  -- the recursion at a nested target, `X.rec_k`, is owed by name only where a
  -- public recursor's type mentions it -- a displayed motive at an index of that
  -- target.  Nothing else of Lean's reaches it by name: `below`, `brecOn`,
  -- `sizeOf` and structural recursion read it off a kernel inductive's
  -- `numNested`, which a block declared otherwise does not have.  Where it is
  -- declared anyway, it is checked like any other
  let shown : Array Nat := displayAt.foldl (fun acc row => acc ++ row.filterMap id) #[]
  let isNested (t : Nat) : Bool := match targets[t]! with | .nested _ => true | _ => false
  let owed (t : Nat) : TermElabM Bool := do
    return !isNested t || shown.contains t || (← getEnv).contains (recOf t)
  let mut recsOk := true
  -- each recursor and `recOn`: the parameters, motives and minors, the indices
  -- implicit, the major `t`; a displayed motive at the recursion's values
  for t in [:targets.size] do
    unless ← owed t do continue
    let some (rec', recOn') ← (try
        match targets[t]! with
          | .member k =>
            forallTelescope tys[k]! fun idx _ => do
              let major := mkAppN (← mkConstWithLevelParams members[k]!.name) (params ++ idx)
              withLocalDeclD `t major fun x => do
                let ixs := promotedPs ++ idx
                let mut vals := #[]
                for i in [:ixs.size] do
                  if let some (some j) := displayAt[t]![i]? then
                    let ty ← instantiateMVars (← inferType ixs[i]!)
                    vals := vals.push (some (← recAt j ((motiveArgs j ty).push ixs[i]!)))
                  else vals := vals.push none
                let concl := motiveApp motives t ixs vals x
                withInfos (uniformPs ++ ixs) implicit do
                  return some (← mkForallFVars (uniformPs ++ motives ++ minors ++ ixs ++ #[x]) concl,
                    ← mkForallFVars (uniformPs ++ motives ++ ixs ++ #[x] ++ minors) concl)
          | .nested a =>
            lambdaTelescope a fun locals n => do
            forallTelescope (← inferType n) fun idx _ =>
            withLocalDeclD `t (mkAppN n idx) fun x => withInfos (uniformPs ++ locals ++ idx) implicit do
              let ixs := locals ++ idx
              let mut vals := #[]
              for i in [:ixs.size] do
                if let some (some j) := displayAt[t]![i]? then
                  let ty ← instantiateMVars (← inferType ixs[i]!)
                  vals := vals.push (some (← recAt j ((motiveArgs j ty).push ixs[i]!)))
                else vals := vals.push none
              let concl := motiveApp motives t ixs vals x
              return some (← mkForallFVars (uniformPs ++ motives ++ minors ++ locals ++ idx ++ #[x]) concl,
                ← mkForallFVars (uniformPs ++ motives ++ locals ++ idx ++ #[x] ++ minors) concl)
      catch e => do problem r .recursor m!"the recursor `{recOf t}`: {e.toMessageData}"; pure none)
      | recsOk := false; continue
    let levels ← levelsOf (ownerOf t) anySort
    let ok ← checkConst r .recursor (recOf t) rec' (levels := levels)
    recsOk := recsOk && ok
    -- `recOn` is the recursor with the indices and major before the minors
    let .member k := targets[t]! | continue
    let recOn := members[k]!.name ++ `recOn
    if (← checkConst r .recOnForm recOn recOn' (levels := levels)) && ok then
      let stmt ← forallTelescope recOn' fun xs _ => do
        let nm := uniformPs.size + motives.size
        let ni := xs.size - nm - minors.size
        let vs := xs.extract 0 nm ++ xs.extract (nm + ni) xs.size ++ xs.extract nm (nm + ni)
        mkForallFVars xs (← mkEq (← mkAppOptM recOn (xs.map some)) (← mkAppOptM (recOf t) (vs.map some)))
      unless ← kernelRfl stmt do problem r .recOnForm m!"`{recOn}` is not the recursor, by `rfl`"
  -- each rule, of a motive not into `Prop`: the recursor at a constructor is
  -- its minor premise at the recursion's values; stated where the recursors are as specified
  let mut mi := 0
  for t in [:(if recsOk then targets.size else 0)] do
    for ci in [:(← ctorsOf t).size] do
      let (c, _, _) := (← ctorsOf t)[ci]!
      let missing := hypGaps[mi]!
      let minor := minors[mi]!
      mi := mi + 1
      if (sortOf t).isProp then continue
      -- a rule at a nested target, or with a hypothesis there, is stated with
      -- that target's recursion, and so only where it has a name
      unless ← owed t do continue
      atCtor t ci fun promoted ctor fields idx => do
        let lhs ← recAt t (idx.push ctor)
        let mut ihs := #[]
        for f in fields do
          if missing.contains (← f.fvarId!.getDecl).userName then continue
          -- `none`: no hypothesis; `some none`: one at a target with no name
          let ih? : Option (Option Expr) ← forallTelescope (← inferType f) fun dom ty => do
            let ty := (← instantiateMVars ty).headBeta
            let some j := targetOf ty | return none
            unless ← owed j do return some none
            return some (some (← mkLambdaFVars dom (← recAt j ((motiveArgs j ty).push (mkAppN f dom)))))
          let some ih := ih? | continue
          let some ih := ih | return
          ihs := ihs.push ih
        let rhs ← mkAppOptM' minor ((promoted ++ fields ++ ihs).map some)
        let stmt ← mkForallFVars (uniformPs ++ motives ++ minors ++ promoted ++ fields) (← mkEq lhs rhs)
        expectRule r (ruleName (recOf t) c) stmt
  -- each member's `casesOn`: one motive, as the recursor names it, no hypotheses
  for t in [:targets.size] do
    let .member k := targets[t]! | continue
    let m := members[k]!
    let casesOn := m.name ++ `casesOn
    let cs ← ctorsOf t
    let ok ← try
        forallTelescope tys[k]! fun idx _ => do
        let major := mkAppN (← mkConstWithLevelParams m.name) (params ++ idx)
        let ixs := promotedPs ++ idx
        let mty ← withLocalDeclD `t major fun x => mkForallFVars (ixs.push x) (sortOf t)
        withLocalDecl (motiveName t) motiveInfo mty fun mot => do
        let decls := (Array.range cs.size).map fun ci => (cs[ci]!.1, BinderInfo.default, fun (_ : Array Expr) =>
          atCtor t ci fun _ ctor fields cidx => withInfos promotedPs (fun _ => .implicit) do
            mkForallFVars (promotedPs ++ fields) (mkAppN mot (cidx.push ctor)))
        withLocalDecls decls fun cminors => do
        withLocalDeclD `t major fun x => do
          let expected ← withInfos (uniformPs ++ ixs) implicit do
            mkForallFVars (uniformPs ++ #[mot] ++ ixs ++ #[x] ++ cminors) (mkAppN mot (ixs.push x))
          let ok ← checkConst r .casesOnForm casesOn expected
            (levels := ← levelsOf m.name (!(sortOf t).isProp) (joint := false))
          -- its rules: `casesOn` at a constructor is the minor premise at the fields
          unless (sortOf t).isProp || !ok do
            for ci in [:cs.size] do
              atCtor t ci fun _ ctor fields cidx => do
                let lhs ← mkAppOptM casesOn ((uniformPs ++ #[mot] ++ cidx ++ #[ctor] ++ cminors).map some)
                let rhs ← mkAppOptM' cminors[ci]! ((promotedPs ++ fields).map some)
                let stmt ← mkForallFVars (uniformPs ++ #[mot] ++ cminors ++ promotedPs ++ fields) (← mkEq lhs rhs)
                expectRule r (ruleName casesOn cs[ci]!.1) stmt
        pure true
      catch e => do problem r .casesOnForm m!"`{casesOn}`: {e.toMessageData}"; pure false
    let _ := ok

/-! ## Injectivity -/

/-! ## Constructors, as Lean's behave -/

/-- Whether `tac` closes `goal`.  Nothing it says is kept, and it does not get to spend
the block's whole budget: a tactic that loses itself in an encoding has failed. -/
private def closes (goal : Expr) (tac : Syntax) : TermElabM Bool := do
  let saved ← Core.getMessageLog
  let ok ← withTheReader Core.Context (fun c => { c with maxHeartbeats := 100000 * 1000 }) do
    withCurrHeartbeats do
      tryCatchRuntimeEx
        (do
          let g ← mkFreshExprMVar goal
          let rest ← Term.withoutErrToSorry <|
            Lean.Elab.Tactic.run g.mvarId! (Lean.Elab.Tactic.evalTactic tac)
          pure rest.isEmpty)
        (fun _ => pure false)
  Core.setMessageLog saved
  return ok

/-- `k` with an instance of `SizeOf` for each of `params` that is a type or a family of
them, as the statement of Lean's `sizeOf_spec` takes them. -/
private def withSizeOfInsts {α} (params : Array Expr) (k : Array Expr → TermElabM α) : TermElabM α :=
  go 0 #[]
where
  go (i : Nat) (insts : Array Expr) : TermElabM α := do
    if h : i < params.size then
      let x := params[i]
      let inst? ← forallTelescopeReducing (← inferType x) fun xs s => do
        unless s.isSort do return none
        return some (← mkForallFVars xs (← mkAppM ``SizeOf #[mkAppN x xs]))
      match inst? with
      | some ty => withLocalDecl (← mkFreshUserName `inst) .instImplicit ty fun y => go (i + 1) (insts.push y)
      | none => go (i + 1) insts
    else k insts
  termination_by params.size - i

/-- `X.c.sizeOf_spec`: one and the sum of the fields, a function counting for nothing.  A
parameter from `uniform` on varies, so it is an index, which a constructor has as a field. -/
private def sizeOfSpec (r : Run) (m : Member) (params : Array Expr) (uniform : Nat) (c : Syntax) :
    TermElabM Unit := do
  let ctorName := m.name ++ c[3].getId
  try
    let fixed := params.extract 0 uniform
    let varying := params.extract uniform params.size
    let ty ← elabCtor m params c fun fields _ => withSizeOfInsts fixed fun insts => do
      let app := mkAppN (← mkConstWithLevelParams ctorName) (params ++ fields)
      let mut rhs ← mkNumeral (mkConst ``Nat) 1
      for f in varying ++ fields do
        if (← whnf (← inferType f)).isForall then continue
        rhs ← mkAdd rhs (← Lean.Elab.MultiuniverseInductive.sizeOfTerm f)
      let stmt ← mkEq (← Lean.Elab.MultiuniverseInductive.sizeOfTerm app) rhs
      withInfos params (fun bi => if bi == .default then .implicit else bi) do
        mkForallFVars (fixed ++ insts ++ varying ++ fields) stmt
    discard <| checkConst r .sizeOf (ctorName ++ `sizeOf_spec) ty (innerNames := false)
  catch e =>
    problem r .sizeOf m!"`{ctorName}.sizeOf_spec` could not be stated: {e.toMessageData}"

/-- `X.ctorIdx` at each constructor, by `rfl`. -/
private def ctorIdxRules (r : Run) (m : Member) (params : Array Expr) : TermElabM Unit := do
  let mut i := 0
  for c in m.decl[4].getArgs do
    let ctorName := m.name ++ c[3].getId
    let ok ← try
        let stmt ← elabCtor m params c fun fields _ => do
          let app := mkAppN (← mkConstWithLevelParams ctorName) (params ++ fields)
          let idx ← mkAppM (m.name ++ `ctorIdx) #[app]
          mkForallFVars (params ++ fields) (← mkEq idx (mkNatLit i))
        kernelRfl stmt
      catch _ => pure false
    unless ok do problem r .ctorIndex m!"`{m.name}.ctorIdx` is not {i} at `{ctorName}` by `rfl`"
    i := i + 1

/-- Two different constructors are refuted by each of the ways Lean has of refuting them.
Each constructor is asked about against the next, where their types can agree at all. -/
private def discrimination (r : Run) (m : Member) (params : Array Expr) : TermElabM Unit := do
  let ctors := m.decl[4].getArgs.map fun c => m.name ++ c[3].getId
  for h : i in [:ctors.size - 1] do
    let c1 := ctors[i]!
    let c2 := ctors[i + 1]!
    try
      let app1 := mkAppN (← mkConstWithLevelParams c1) params
      let app2 := mkAppN (← mkConstWithLevelParams c2) params
      let (ms1, _, t1) ← forallMetaTelescope (← inferType app1)
      let (ms2, _, t2) ← forallMetaTelescope (← inferType app2)
      unless ← withReducible (isDefEq t1 t2) do continue
      let stmt ← mkArrow (← mkEq (mkAppN app1 ms1) (mkAppN app2 ms2)) (mkConst ``False)
      let abs ← abstractMVars (← instantiateMVars stmt)
      lambdaTelescope abs.expr fun _ goal => do
        let conf := mkCIdent (m.name ++ `noConfusion)
        unless ← closes goal (← `(tactic| (intro h; contradiction))) do
          problem r .discr m!"`contradiction` does not refute `{c1} … = {c2} …`"
        unless ← closes goal (← `(tactic| (intro h; cases h))) do
          problem r .discr m!"`cases` does not refute `{c1} … = {c2} …`"
        unless ← closes goal (← `(tactic| (intro h; simp at h))) do
          problem r .discr m!"`simp` does not refute `{c1} … = {c2} …`"
        unless ← closes goal (← `(tactic| (intro h; cases h with))) do
          problem r .discr m!"`cases … with` does not refute `{c1} … = {c2} …`"
        unless ← closes goal (← `(tactic| (intro h; rcases h with ⟨⟩))) do
          problem r .discr m!"`rcases` does not refute `{c1} … = {c2} …`"
        unless ← closes goal (← `(tactic| (intro h; obtain ⟨⟩ := h))) do
          problem r .discr m!"`obtain` does not refute `{c1} … = {c2} …`"
        unless ← closes goal (← `(tactic| (intro h; injections))) do
          problem r .discr m!"`injections` does not refute `{c1} … = {c2} …`"
        -- an indexed member's takes an equation at each index first
        unless ← closes goal (← `(tactic| first
            | exact fun h => $conf h
            | exact fun h => $conf rfl (heq_of_eq h)
            | exact fun h => $conf rfl rfl (heq_of_eq h)
            | exact fun h => $conf rfl rfl rfl (heq_of_eq h)
            | exact fun h => $conf rfl HEq.rfl (heq_of_eq h)
            | exact fun h => $conf rfl HEq.rfl HEq.rfl (heq_of_eq h)
            | exact fun h => $conf rfl rfl HEq.rfl (heq_of_eq h))) do
          problem r .discr m!"`{m.name}.noConfusion` does not refute `{c1} … = {c2} …`"
    catch e =>
      problem r .discr m!"`{c1} … = {c2} …` could not be stated: {e.toMessageData}"

/-- What `X.c.inj` states, by the tactics: `injection` and `cases` at the equation give
the equations of the fields.  `inj` is the statement, read from what `injectivity` built. -/
private def injectionBehaves (r : Run) (ctorName : Name) (inj : Expr) : TermElabM Unit := do
  forallTelescope inj fun xs ands => do
    let some h := xs.back? | return
    let goal ← mkArrow (← inferType h) ands
    withErasedFVars #[h.fvarId!] do
      unless ← closes goal (← `(tactic| (intro h; injection h; all_goals (and_intros <;> assumption)))) do
        problem r .inject m!"`injection` at an equation of `{ctorName}` does not give those of its fields"
      unless ← closes goal (← `(tactic| (intro h; cases h; all_goals (and_intros <;> first | rfl | exact HEq.rfl)))) do
        problem r .inject m!"`cases` at an equation of `{ctorName}` does not give those of its fields"
      unless ← closes goal (← `(tactic| (intro h; injections; all_goals (and_intros <;> assumption)))) do
        problem r .inject m!"`injections` at an equation of `{ctorName}` does not give those of its fields"
      unless ← closes goal (← `(tactic| (intro h; cases h with | refl => (and_intros <;> first | rfl | exact HEq.rfl)))) do
        problem r .inject m!"`cases … with` at an equation of `{ctorName}` does not give those of its fields"
      unless ← closes goal (← `(tactic| (intro h; rcases h with ⟨⟩; all_goals (and_intros <;> first | rfl | exact HEq.rfl)))) do
        problem r .inject m!"`rcases` at an equation of `{ctorName}` does not give those of its fields"
      unless ← closes goal (← `(tactic| (intro h; obtain ⟨⟩ := h; all_goals (and_intros <;> first | rfl | exact HEq.rfl)))) do
        problem r .inject m!"`obtain` at an equation of `{ctorName}` does not give those of its fields"

/-- `X.c.inj` and `X.c.injEq` as Lean states them: the fields that appear in the
conclusion shared, the others twice, an equation (or `HEq`) at each that is
not a proof, conjoined; none at all where there is none. -/
private def injectivity (r : Run) (m : Member) (params : Array Expr) (c : Syntax) : TermElabM Unit := do
  let ctorName := m.name ++ c[3].getId
  let some (injTy, injEqTy) ← elabCtor m params c fun args1 res => do
      let ctor ← mkConstWithLevelParams ctorName
      let lctx ← getLCtx
      let rec go (i : Nat) (args2 new : Array Expr) (useEq : Bool) : TermElabM (Option Expr) := do
        if h : i < args1.size then
          let a := args1[i]
          if occursOrInType lctx a res then go (i + 1) (args2.push a) new useEq
          else
            let d ← instantiateMVars (← inferType a)
            let d := d.replaceFVars args1[:i].toArray args2
            withLocalDecl (← a.fvarId!.getDecl).userName (if useEq then .default else .implicit) d fun a2 =>
              go (i + 1) (args2.push a2) (new.push a2) useEq
        else
          let lhs := mkAppN ctor (params ++ args1)
          let rhs := mkAppN ctor (params ++ args2)
          let eq ← mkEq lhs rhs
          let mut eqs := #[]
          for a1 in args1, a2 in args2 do
            if !(← isProp (← inferType a1)) && a1 != a2 then eqs := eqs.push (← mkEqHEq a1 a2)
          let some ands := eqs.back? | return none
          let ands := eqs.pop.foldr (fun e acc => mkApp2 (mkConst ``And) e acc) ands
          let body ← if useEq then mkEq eq ands else pure (← mkArrow eq ands)
          -- `inj` takes every parameter implicitly, an instance's too, and
          -- `injEq` keeps an instance's as it is: as Lean does
          withInfos params (fun bi => if bi == .default || !useEq then .implicit else bi) do
            if useEq then mkForallFVars params (← mkForallFVars args1 (← mkForallFVars new body))
            else withInfos args1 (fun _ => .implicit) do
              mkForallFVars params (← mkForallFVars args1 (← mkForallFVars new body))
      let inj ← go 0 #[] #[] false
      let injEq ← go 0 #[] #[] true
      return inj.bind fun a => injEq.map (a, ·)
    | return
  discard <| checkConst r .injEq (ctorName ++ `inj) injTy (levels := (← getConstInfo m.name).levelParams)
  discard <| checkConst r .injEq (ctorName ++ `injEq) injEqTy (levels := (← getConstInfo m.name).levelParams)
  injectionBehaves r ctorName injTy

/-! ## Tactics -/

/-- Whether `tac` (on the major `t`) closes `True` over each member: the
alternatives named by the constructors. -/
private def tactic (r : Run) (claim : Claim) (b : Block) (k : Nat)
    (mk : Syntax → Array Syntax → TermElabM Syntax) : TermElabM Unit := do
  let m := b.members[k]!
  let ok ← forallTelescope b.tys[k]! fun idx _ => do
    let major := mkAppN (← mkConstWithLevelParams m.name) (b.params ++ idx)
    withLocalDeclD `t major fun _ => do
      let g ← mkFreshExprMVar (mkConst ``True)
      let alts := m.decl[4].getArgs.map (·[3])
      let tac ← mk (mkIdent `t) alts
      let saved ← Core.getMessageLog
      let ok ← try
          let rest ← Term.withoutErrToSorry <| Lean.Elab.Tactic.run g.mvarId! (Lean.Elab.Tactic.evalTactic tac)
          pure rest.isEmpty
        catch _ => pure false
      Core.setMessageLog saved
      pure ok
  unless ok do problem r claim m!"`{claim}` on a `{m.name}`, its alternatives named by the constructors, does not go through"

/-! ## `match` -/

/-- The tactic written `s`. -/
private def tacticOf (s : String) : TermElabM Syntax :=
  do ofExcept (Parser.runParserCategory (← getEnv) `tactic s)

/-- A constructor's name as a pattern can have it, wherever the check is run from. -/
private def patName (c : Name) : String :=
  if isPrivateName c then s!"{privateToUserName c}" else s!"_root_.{c}"

/-- `match` on a member at its indices: by a term, by `fun`, and by tactics. -/
private def matching (r : Run) (m : Member) (params : Array Expr) (ty : Expr) : TermElabM Unit := do
  let ctors := m.decl[4].getArgs.map fun c => m.name ++ c[3].getId
  if ctors.isEmpty then return
  let alts (rhs : String) := " ".intercalate (ctors.toList.map fun c => s!"| {patName c} .. => {rhs}")
  forallTelescope ty fun idx _ => do
    let major := mkAppN (← mkConstWithLevelParams m.name) (params ++ idx)
    withLocalDeclD `_spec_t major fun _ => do
      let check (goal : Expr) (how s : String) : TermElabM Unit := do
        let ok ← try closes goal (← tacticOf s) catch _ => pure false
        unless ok do
          problem r .matching m!"`match` {how} on a `{m.name}` does not go through"
      check (mkConst ``True) "as tactics" s!"match _spec_t with {alts "trivial"}"
      if m.prop then
        check (mkConst ``True) "as a term" s!"exact match _spec_t with {alts "trivial"}"
      else
        check (mkConst ``Nat) "as a term" s!"exact match _spec_t with {alts "0"}"
        check (← mkArrow major (mkConst ``Nat)) "by `fun`" s!"exact fun {alts "0"}"

/-- Whether `a`, where a constructor concludes, is something Lean's `cases` cannot solve against
another's: neither a variable nor a constructor applied, nor a numeral or `n + 1`. -/
private partial def isComputedIndex (fields : Array Expr) (a : Expr) : MetaM Bool := do
  let a := a.consumeMData
  if a.isFVar || a.isLit then return false
  if (← isOffset? a).isSome then return false
  let .const c _ := a.getAppFn | return true
  if a.isAppOf ``OfNat.ofNat then return false
  let env ← getEnv
  -- a constructor, or one of an encoded member's, which is a definition with a rule for it
  let ctorLike := (env.find? c).any (·.isCtor) ||
    (match c with
      | .str mem s => env.contains (Name.mkStr mem s!"ctorIdx_{s}")
      | _ => false)
  unless ctorLike do return true
  a.getAppArgs.anyM (isComputedIndex fields)

/-- `match` and `cases` on a term whose index is a constructor of a data member, at
`At : (x : X …) → Prop` with a constructor for each of `X`'s, which is declared here and goes
when the check does. -/
private def matchingAtIndex (r : Run) (m : Member) (params : Array Expr) (ty : Expr) : TermElabM Unit := do
  let cs := m.decl[4].getArgs
  if cs.isEmpty then return
  let saved ← getEnv
  try
    let lps := (← getConstInfo m.name).levelParams
    let us := lps.map mkLevelParam
    let at_ := m.name ++ `_specAt
    let atTy ← forallTelescope ty fun idx _ => do
      let major := mkAppN (mkConst m.name us) (params ++ idx)
      withLocalDeclD `x major fun x => do
        instantiateMVars (← mkForallFVars (params ++ idx ++ #[x]) (mkSort .zero))
    let atApp (idx : Array Expr) (x : Expr) := mkAppN (mkConst at_ us) (params ++ idx ++ #[x])
    let ctorIdxOf (res : Expr) := res.getAppArgs.extract params.size res.getAppNumArgs
    let ctors ← cs.mapM fun c => elabCtor m params c fun fields res => do
      let app := mkAppN (mkConst (m.name ++ c[3].getId) us) (params ++ fields)
      withInfos params (fun bi => if bi == .default then .implicit else bi) do
        let type ← instantiateMVars (← mkForallFVars (params ++ fields) (atApp (ctorIdxOf res) app))
        return ({ name := at_ ++ c[3].getId, type } : Constructor)
    -- Lean solves an index against a case's by its variables and constructors.  Where a
    -- constructor of the member concludes at anything else, `n + m` or a decoder's value, Lean's
    -- own `cases` stops there too (`SelfTest`), so each constructor is asked about alone
    let askAt (c : Syntax) : TermElabM Unit := do
      elabCtor m params c fun fields res => do
        let app := mkAppN (mkConst (m.name ++ c[3].getId) us) (params ++ fields)
        withLocalDeclD `_spec_h (atApp (ctorIdxOf res) app) fun _ => do
          let alt := s!"| {patName (at_ ++ c[3].getId)} .. => trivial"
          let check (how s : String) : TermElabM Unit := do
            let ok ← try closes (mkConst ``True) (← tacticOf s) catch _ => pure false
            unless ok do
              problem r .matching m!"{how} at an index `{m.name ++ c[3].getId} …` does not go through"
          check "`cases`" "cases _spec_h <;> trivial"
          check "`match` as tactics" s!"match _spec_h with {alt}"
          check "`match` as a term" s!"exact match _spec_h with {alt}"
    let computed ← cs.anyM fun c => elabCtor m params c fun fields res =>
      (ctorIdxOf res).anyM fun a => isComputedIndex fields a
    if computed then
      for c in cs do
        let env := (← getEnv)
        setEnv saved
        let one := ctors.filter fun k => k.name == at_ ++ c[3].getId
        addDecl (.inductDecl lps params.size [{ name := at_, type := atTy, ctors := one.toList }] false)
        mkCasesOn at_
        askAt c
        setEnv env
    else
    addDecl (.inductDecl lps params.size [{ name := at_, type := atTy, ctors := ctors.toList }] false)
    mkCasesOn at_
    for c in cs do
      askAt c
  catch e =>
    problem r .matching m!"a type indexed by `{m.name}` could not be asked about: {e.toMessageData}"
  finally
    setEnv saved

/-! ## Decoders -/

/-- The identifiers of a pattern that name nothing: its variables. -/
private partial def patternVars (p : Syntax) : TermElabM (Array Name) := do
  if p.isOfKind ``Parser.Term.dotIdent then return #[]
  if p.isOfKind ``Parser.Term.namedArgument then return ← patternVars p[3]
  if p.isIdent then
    let n := p.getId
    return if n.isAtomic && !n.isAnonymous && (← resolveGlobalName n).isEmpty then #[n] else #[]
  p.getArgs.foldlM (fun acc a => return acc ++ (← patternVars a)) #[]

/-- A pattern with each `_` a variable of its own, so that the rule binds it. -/
private partial def nameHoles (p : Syntax) : StateM Nat Syntax := do
  if p.isOfKind ``Parser.Term.hole then
    let i ← modifyGet fun i => (i, i + 1)
    return mkIdent (Name.mkSimple s!"_spec_hole_{i}")
  match p with
  | .node info k args => return .node info k (← args.mapM nameHoles)
  | _ => return p

/-- `k`, with `n := v` bound for each named value. -/
private def withLets {α} : List (Name × Expr) → (Array Expr → TermElabM α) → TermElabM α
  | [], k => k #[]
  | (n, v) :: rest, k => do
    let v ← instantiateMVars v
    withLetDecl n (← inferType v) v fun x => withLets rest fun xs => k (#[x] ++ xs)

/-- Each equation of decoder `name` (declaration `d`) as written: the decoder at
the pattern is the clause's right-hand side. -/
private def decoderRules (r : Run) (name : Name) (d : Syntax) : TermElabM Unit := do
  let eqns := d[3]
  unless eqns.isOfKind ``Parser.Command.declValEqns do return
  Term.elabBinders d[2][0].getArgs fun bs => do
  for alt in eqns[0][0][0].getArgs do
    for group in alt[1].getSepArgs do
      let pats := group.getSepArgs
      let major := (nameHoles pats.back!).run' 0
      let vars ← patternVars major
      let decls := vars.map fun v => (v, BinderInfo.default, fun (_ : Array Expr) => (mkFreshTypeMVar : TermElabM Expr))
      withLocalDecls decls fun xs => do
        let fn ← mkConstWithLevelParams name
        let (mvs, _, _) ← forallMetaTelescopeReducing (← instantiateForall (← inferType fn) bs) (some pats.size)
        let pat ← Term.elabTermEnsuringType major (← inferType mvs.back!)
        Term.synthesizeSyntheticMVarsNoPostponing
        unless ← isDefEq mvs.back! pat do
          return ← problem r .decoders m!"the pattern {major} of `{name}` does not fit"
        let lhs ← instantiateMVars (mkAppN fn (bs ++ mvs))
        let named := (pats.pop.zip mvs.pop).toList.filterMap fun (p, v) => if p.isIdent then some (p.getId, v) else none
        let rhs ← withLets named fun lets => do
          -- against the decoder's type where Meta can see it through; else on
          -- its own, the kernel judging the equation (a numeral in lower mode)
          let saved ← saveState
          let r ← try
              let r ← Term.withoutErrToSorry <| Term.elabTermEnsuringType alt[3] (← inferType lhs)
              Term.synthesizeSyntheticMVarsNoPostponing
              pure r
            catch _ =>
              saved.restore
              let r ← Term.elabTerm alt[3] none
              Term.synthesizeSyntheticMVarsNoPostponing
              pure r
          let vals ← named.toArray.mapM (instantiateMVars ·.2)
          return (← instantiateMVars r).replaceFVars lets vals
        let some c := (← instantiateMVars pat).getAppFn.constName? | return
        let stmt ← mkForallFVars (bs ++ xs) (← mkEq lhs rhs)
        expectRule r (name.getPrefix ++ Name.mkSimple (name.getString! ++ "_" ++ c.getString!)) stmt

/-! ## The whole block -/

/-- The identifiers in `s`. -/
private partial def identsIn (s : Syntax) : Array Name :=
  if s.isIdent then #[s.getId] else s.getArgs.flatMap identsIn

/-- `s` with each identifier `f` gives a replacement for replaced. -/
private partial def replaceIdents (f : Name → Option Syntax) (s : Syntax) : Syntax :=
  if s.isIdent then (f s.getId).getD s
  else match s with
    | .node info k args => .node info k (args.map (replaceIdents f))
    | _ => s

/-- How many leading indices Lean promotes to parameters
(`inductive.autoPromoteIndices`): a prefix of those that, in every constructor
of every member, are the constructor's own field at their place and are passed
along unchanged at every occurrence of the block, at one type throughout. -/
private def fixedIndices (members : Array Member) (params : Array Expr) (tys : Array Expr) : TermElabM Nat := do
  unless inductive.autoPromoteIndices.get (← getOptions) do return 0
  if members.any (!·.extra.isEmpty) then return 0
  let names := members.map (·.name)
  let mut masks : Array (Array Bool) := #[]
  for m in members, ty in tys do
    let arity ← forallTelescope ty fun xs _ => pure xs.size
    let mut mask := Array.replicate arity true
    for c in m.decl[4].getArgs do
      mask ← elabCtor m params c fun fields res => do
        let mut mask := mask
        let resArgs := res.getAppArgs.extract params.size res.getAppArgs.size
        for i in [:arity] do
          unless fields[i]? == resArgs[i]? && fields[i]?.isSome do mask := mask.set! i false
        for f in fields do
          for e in ← carrierApps names (← instantiateMVars (← inferType f)) do
            let eArgs := e.getAppArgs.extract params.size e.getAppArgs.size
            for i in [:arity] do
              unless eArgs[i]? == resArgs[i]? && eArgs[i]?.isSome do mask := mask.set! i false
        pure mask
    masks := masks.push mask
  -- the prefix, where every index there is at one type, and so every field
  let some first := tys[0]? | return 0
  let mut k := 0
  while masks.all (fun mask => mask[k]?.getD false) do
    let indexAt (ty : Expr) : TermElabM Expr := forallTelescope ty fun xs _ => do
      let some x := xs[k]? | throwError "no index"
      mkForallFVars (xs.extract 0 k) (← inferType x)
    let want ← indexAt first
    let ok ← tys.allM fun ty => do isDefEq (← indexAt ty) want
    let ok ← pure ok <&&> members.allM fun m => m.decl[4].getArgs.allM fun c =>
      elabCtor m params c fun fields _ => do
        let some x := fields[k]? | return false
        isDefEq (← mkForallFVars (fields.extract 0 k) (← inferType x)) want
    unless ok do break
    k := k + 1
  return k

/-- The targets in the order written, members then nested applications, save
that a `Prop` member follows the data targets its motive takes values of. -/
private def targetOrder (members : Array Member) (tys params : Array Expr) (uniform : Nat) (nested : Array Expr) :
    TermElabM (Array Target) := do
  let written : Array Target := (Array.range members.size).map .member ++ nested.map .nested
  let depsOf (t : Target) : TermElabM (Array Nat) := do
    let atIdxs (idx : Array Expr) : TermElabM (Array Nat) := do
      let mut out := #[]
      for x in idx do
        let ty ← instantiateMVars (← inferType x)
        let q? := written.findIdx? fun w => match w with
          | .member j => !members[j]!.prop && ty.getAppFn.isConstOf members[j]!.name
          | .nested a => (nestedArgs? a ty).isSome
        if let some q := q? then out := out.push q
      return out
    match t with
    | .nested a =>
      -- a nested proposition follows the data its motive displays
      lambdaTelescope a fun locals n => do forallTelescope (← inferType n) fun idx s => do
        if s.isProp then atIdxs (locals ++ idx) else return #[]
    | .member k =>
    unless members[k]!.prop do return #[]
    forallTelescope tys[k]! fun idx _ => do
      let mut out := #[]
      for x in params.extract uniform params.size ++ idx do
        let ty ← instantiateMVars (← inferType x)
        let q? := written.findIdx? fun w => match w with
          | .member j => !members[j]!.prop && ty.getAppFn.isConstOf members[j]!.name
          | .nested a => (nestedArgs? a ty).isSome
        if let some q := q? then out := out.push q
      return out
  let deps ← written.mapM depsOf
  let mut order : Array Nat := #[]
  while order.size < written.size do
    let some q := (Array.range written.size).find? fun q =>
        !order.contains q && deps[q]!.all order.contains
      | break
    order := order.push q
  return order.map (written[·]!)

set_option maxHeartbeats 1000000 in
/-- The whole specification of the block, checked against what it declared. -/
def specify (r : Run) (elems : Array Syntax) (sectionVars : Array Expr) (native : Bool) : TermElabM Unit := do
  let upper := !(mumi.mahlo.get (← getOptions))
  let ns ← getCurrNamespace
  let inductives := elems.filter isInductive
  let defs := elems.filter (!isInductive ·)
  let some first := inductives[0]? | return
  -- a member's constant, under its private name where it is `private`
  let env ← getEnv
  let real (n : Name) : Name := if env.contains n then n else
    let p := mkPrivateName env n
    if env.contains p then p else n
  let memberNames := inductives.map fun e => real (ns ++ e[1][1][0].getId)
  -- an induction-recursion -- a definition over a member -- lands one universe
  -- up without `mumi.mahlo`
  let shortNames := inductives.map (·[1][1][0].getId)
  let bump := upper && defs.any fun d => (identsIn d[1][2]).any shortNames.contains
  -- the universes the members were declared at, written or bound automatically
  let mut univs := (← getLevelNames)
  for n in memberNames do
    if let some ci := (← getEnv).find? n then
      for l in ci.levelParams do
        unless univs.contains l do univs := univs ++ [l]
  Term.withLevelNames univs do
  -- the parameters all members declare alike; beyond them, a member's own are indices
  let shared := sharedGroups (inductives.map (·[1]))
  -- the section's variables the members took, before the parameters written:
  -- by name, as a constructor binds them
  let ctorNames := first[1][4].getArgs.map (memberNames[0]! ++ ·[3].getId)
  let taken ← match ctorNames[0]? >>= ((← getEnv).find? ·) with
    | none => pure #[]
    | some ci => forallTelescope ci.type fun xs _ => do
      let mut taken := #[]
      let mut i := 0
      for v in sectionVars do
        let some x := xs[i]? | break
        -- an instance bound anonymously has a name of its own each time
        let vd ← v.fvarId!.getDecl
        let xd ← x.fvarId!.getDecl
        if xd.userName == vd.userName || (xd.binderInfo.isInstImplicit && vd.binderInfo.isInstImplicit) then
          taken := taken.push v
          i := i + 1
      pure taken
  -- inside the block, a member's name stands for it at those variables
  let args ← taken.mapM fun v => do return mkIdent (← v.fvarId!.getUserName)
  let atVars ← if taken.isEmpty then pure #[] else
    (inductives.zip memberNames).mapM fun (e, n) => do
      return (e[1][1][0].getId, ← `((@$(mkIdent n) $args*)))
  let fix := replaceIdents fun n => (atVars.find? (·.1 == n)).map (·.2)
  -- a block Lean takes on its own reads its headers as Lean does, before the
  -- members exist: a name that is a member's and something else's is the other's
  let mut headers := #[]
  for e in inductives do
    unless native do
      headers := headers.push e[1][2]
      continue
    let mut outside : Array (Name × Syntax) := #[]
    for x in identsIn e[1][2] do
      let cands := (← resolveGlobalName x).filter (·.2.isEmpty) |>.map (·.1)
      unless cands.any memberNames.contains do continue
      -- what it names with the members not yet there: the innermost namespace's first
      let mut p := ns
      let mut found := none
      repeat
        let c := p ++ x
        if (← getEnv).contains c && !memberNames.contains c then
          found := some c
          break
        if p.isAnonymous then break
        p := p.getPrefix
      if let some o := found then outside := outside.push (x, mkIdent (`_root_ ++ o))
    headers := headers.push (replaceIdents (fun n => (outside.find? (·.1 == n)).map (·.2)) e[1][2])
  let inductives := (inductives.zip headers).map fun (e, h) =>
    let d := e[1].setArg 2 h
    e.setArg 1 ((fix d).setArg 1 e[1][1])
  let first := inductives[0]!
  Term.elabBinders (first[1][2][0].getArgs.extract 0 shared) fun written => do
  let params := taken ++ written
  -- the type formers
  let mut members : Array Member := #[]
  let mut tys : Array Expr := #[]
  for e in inductives do
    let own := e[1][2][0].getArgs
    let m : Member := { name := real (ns ++ e[1][1][0].getId), decl := e[1], prop := false, block := memberNames, extra := own.extract shared own.size }
    let ty ← instantiateMVars (← declType m)
    let prop ← forallTelescope ty fun _ s => pure s.isProp
    let m := { m with prop }
    members := members.push m
    tys := tys.push ty
    let bumped ← forallTelescope ty fun idx s => do
      let s := if bump && !prop then (match s with | .sort l => mkSort (.succ l) | s => s) else s
      mkForallFVars idx s
    -- the shared parameters as this member annotates them
    let own := groupInfos (e[1][2][0].getArgs.extract 0 shared)
    let infos ← (written.zip own).mapM fun (x, bi) => do return (x.fvarId!, bi)
    discard <| checkConst r .types m.name (← withNewBinderInfos infos (mkForallFVars params bumped)) (innerNames := false)
    -- an inferred universe is the one Lean found
    tys := tys.set! (tys.size - 1) (← instantiateMVars ty)
  -- the constructors, as written
  for m in members do
    for c in m.decl[4].getArgs do
      elabCtor m params c fun fields res => do
        withInfos params (fun bi => if bi == .default then .implicit else bi) do
          discard <| checkConst r .ctors (m.name ++ c[3].getId) (← mkForallFVars params (← mkForallFVars fields res)) (innerNames := false)
            (levels := (← getConstInfo m.name).levelParams)
  let data := (Array.range members.size).filter fun k => !members[k]!.prop
  let props := (Array.range members.size).filter fun k => members[k]!.prop
  -- injectivity, of the data members' constructors
  for k in data do
    for c in members[k]!.decl[4].getArgs do
      injectivity r members[k]! params c
  -- `cases` on every member; `induction` on a lone one, as Lean's own
  let written : Block := { members, tys, params, uniform := params.size }
  for k in [:members.size] do
    tactic r .cases written k fun t alts => do
      let alts ← alts.mapM fun a => `(Lean.Parser.Tactic.inductionAlt| | $(mkIdent a.getId):ident => trivial)
      `(tactic| cases $(⟨t⟩):ident with $alts:inductionAlt*)
  let nestedIn (params : Array Expr) (fields : Array Expr) : TermElabM (Array Expr) := do
    let mut out := #[]
    for f in fields do
      -- a field is its beta-normal form: a predicate a container takes is applied there
      let t ← forallTelescope (← inferType f) fun _ t => return (← instantiateMVars t).headBeta
      if let some n ← nestedHead? memberNames params t then out := out.push n
    return out
  let lone := members.size == 1 && (← members[0]!.decl[4].getArgs.allM fun c =>
    elabCtor members[0]! params c fun fields _ => do return (← nestedIn params fields).isEmpty)
  if lone then
    tactic r .induction written 0 fun t alts => do
      let alts ← alts.mapM fun a => `(Lean.Parser.Tactic.inductionAlt| | $(mkIdent a.getId):ident => trivial)
      `(tactic| induction $(⟨t⟩):ident with $alts:inductionAlt*)
  -- the recursion is over the indices Lean leaves indices: a fixed prefix of
  -- them it promotes to parameters, each constructor's field there theirs
  let promoted ← fixedIndices members params tys
  forallBoundedTelescope tys[0]! promoted fun lifted _ => do
  let params := params ++ lifted
  let tys ← tys.mapM fun t => instantiateForall t lifted
  unless lifted.isEmpty do
    for (key, ty, n) in (← ctorTypes.get).toList do
      ctorTypes.modify (·.insert key (← instantiateForall ty lifted, n - lifted.size))
  -- from which parameter on an occurrence varies them
  let mut uniform := params.size
  for m in members do
    for c in m.decl[4].getArgs do
      let vary ← elabCtor m params c fun fields res => do
        let mut v := params.size
        for e in (← fields.mapM fun f => inferType f).push res do
          for app in ← carrierApps memberNames (← instantiateMVars e) do
            let args := app.getAppArgs
            for j in [:min args.size params.size] do
              unless args[j]! == params[j]! do v := min v j
        pure v
      uniform := min uniform vary
  -- an inductive met in a nesting comes with its whole mutual block, in the order
  -- that block has it, as the kernel takes it: `FamForest X` brings `FamRose X` first
  let withSiblings (a : Expr) : TermElabM (Array Expr) := lambdaTelescope a fun ls n => do
    let .const ind lvls := n.getAppFn | return #[a]
    let some (.inductInfo info) := (← getEnv).find? ind | return #[a]
    info.all.toArray.mapM fun j => mkLambdaFVars ls (mkAppN (.const j lvls) n.getAppArgs)
  -- the targets: data members, nested applications in the order met, `Prop` members
  let mut nested : Array Expr := #[]
  for k in data ++ props do
    for c in members[k]!.decl[4].getArgs do
      for n in ← elabCtor members[k]! params c fun fields _ => nestedIn params fields do
        unless nested.contains n do nested := nested ++ (← withSiblings n).filter (!nested.contains ·)
  let mut i := 0
  while i < nested.size do
    let a := nested[i]!
    i := i + 1
    let found ← lambdaTelescope a fun _ n => do
      let .const ind lvls := n.getAppFn | return #[]
      let some (.inductInfo info) := (← getEnv).find? ind | return #[]
      info.ctors.toArray.flatMapM fun ctor => do
        let cty ← instantiateForall ((← getConstInfo ctor).instantiateTypeLevelParams lvls) n.getAppArgs
        forallTelescope cty fun fields _ => nestedIn params fields
    for m in found do
      unless nested.contains m do nested := nested ++ (← withSiblings m).filter (!nested.contains ·)
  let b : Block := { members, tys, params, uniform }
  -- the constructors, as Lean's behave
  for k in data do
    let m := members[k]!
    for c in m.decl[4].getArgs do
      -- a block Lean takes on its own has Lean's lemma, which is what the claim is
      if native then
        unless (← getEnv).contains (m.name ++ c[3].getId ++ `sizeOf_spec) do
          problem r .sizeOf m!"`{m.name ++ c[3].getId}.sizeOf_spec` is not declared"
      else sizeOfSpec r m params uniform c
    ctorIdxRules r m params
    discrimination r m params
    matchingAtIndex r m params tys[k]!
  for k in [:members.size] do
    matching r members[k]! params tys[k]!
  -- a `Prop` member alone eliminates as Lean lets it; beside others, into
  -- `Prop`, as a `mutual` of more than one type does
  let large ← if members.size == 1 then largeElim b props else pure false
  let order ← targetOrder members tys params uniform nested
  try recursion r b order large
  catch e => problem r .recursor m!"the recursion could not be stated: {e.toMessageData}"
  -- the decoders: their types and equations as written
  for d in defs do
    let name := ns ++ d[1][1][0].getId
    let sig ← Term.elabBinders d[1][2][0].getArgs fun bs => do
      let ty ← Term.elabType d[1][2][1][0][1]
      Term.synthesizeSyntheticMVarsNoPostponing
      mkForallFVars bs (← instantiateMVars ty)
    discard <| checkConst r .decoders name sig (innerNames := false)
    decoderRules r name d[1]
  -- the axioms: none but `IR.mahlo` under `mumi.mahlo`, and `propext` in an `injEq`
  for c in (← r.checked.get).toList.eraseDups do
    let allowed := (if upper then #[] else #[``IR.mahlo]) ++ (if c.getString! == "injEq" then #[``propext] else #[])
    let extra := (← collectAxioms c).filter (!allowed.contains ·)
    unless extra.isEmpty do problem r .axioms m!"`{c}` depends on axioms {extra.toList}"

/-! ## The command -/

/-- `mumi_spec mutual … end` (or one `inductive`): the block, then its
specification checked.  Options: `(simp := [X.rec_c, …])` the rules that hold
only by `simp`; `(unproven := [d_c, …])` those that hold neither way;
`(xfail := [rec, injEq, …])` the kinds of claim known to fail; `(rejects)` that
the block is to be refused. -/
syntax specOption := "(" ident (" := " "[" ident,* "]")? ")"
syntax (name := mumiSpec) "mumi_spec" specOption* ppLine command : command

/-- The declarations of a block: a `mutual`'s, or one declaration. -/
private def blockElems (cmd : Syntax) : Option (Array Syntax) :=
  if cmd.isOfKind ``Parser.Command.«mutual» then some cmd[1].getArgs
  else if cmd.isOfKind ``Parser.Command.declaration then some #[cmd]
  else none

@[command_elab mumiSpec] def elabMumiSpec : CommandElab := fun stx => do
  let ns ← getCurrNamespace
  let mut simpRules := #[]
  let mut unproven := #[]
  let mut xfail : Array Claim := #[]
  let mut rejects := false
  for o in stx[1].getArgs do
    let names := if o[2].getNumArgs == 0 then #[] else o[2][2].getSepArgs
    match o[1].getId with
    | `simp => simpRules := simpRules ++ names.map (ns ++ ·.getId)
    | `unproven => unproven := unproven ++ names.map (ns ++ ·.getId)
    | `xfail =>
      for n in names do
        let some (_, c) := Claim.all.find? (·.1 == n.getId)
          | throwErrorAt n "unknown claim `{n.getId}`: one of {Claim.all.map (·.1)}"
        xfail := xfail.push c
    | `rejects => rejects := true
    | k => throwErrorAt o[1] "unknown mumi_spec option `{k}`: `simp`, `unproven`, `xfail` or `rejects`"
  let cmd := stx[2]
  let n := (← get).messages.reportedPlusUnreported.size
  if rejects then
    -- a block to be refused: refused it must be, and nothing of it kept
    let saved ← get
    elabCommand cmd
    let failed := ((← get).messages.reportedPlusUnreported.toList.drop n).any (·.severity == .error)
    set saved
    unless failed || xfail.contains .gap do logErrorAt cmd "the block is to be rejected, and was declared"
    if failed && xfail.contains .gap then logErrorAt cmd "`xfail := [gap]`, but the block is rejected"
    return
  -- whether Lean takes the block on its own
  let native ← do
    let saved ← get
    let before := saved.messages.reportedPlusUnreported.size
    let ok ← try
        withScope (fun sc => { sc with opts := sc.opts.setBool `mumi.enabled false }) (elabCommand cmd)
        pure !((← get).messages.reportedPlusUnreported.toList.drop before).any (·.severity == .error)
      catch _ => pure false
    set saved
    pure ok
  elabCommand cmd
  if ((← get).messages.reportedPlusUnreported.toList.drop n).any (·.severity == .error) then return
  let problems ← IO.mkRef #[]
  let stated ← IO.mkRef #[]
  let checked ← IO.mkRef #[]
  let r : Run := { problems, stated, checked, simpRules, unproven, partialRecs := false }
  -- under the block's own `set_option … in`
  withSetOptionIn (fun inner => do
    let some elems := blockElems inner | throwErrorAt cmd "mumi_spec expects a `mutual` block or an `inductive`"
    let r := { r with partialRecs := mumi.partialRecursors.get (← getOptions) }
    -- the block's syntax elaborated again, but recorded nowhere: no linter sees it
    ctorTypes.set {}
    -- the checks have a budget each, and a large block has many
    withEnableInfoTree false <| runTermElabM fun vars =>
      withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) do
        specify r elems vars native) cmd
  let stated ← r.stated.get
  for rule in simpRules ++ unproven do
    unless stated.contains rule do r.problems.modify (·.push (.rules, m!"`{rule}` is not a rule the specification states"))
  let problems ← r.problems.get
  let display := mumi.spec.showXFail.get (← getOptions)
  for (c, p) in problems do
    if xfail.contains c then
      if display then logInfoAt cmd m!"known to fail, [{c}]: {p}"
    else logErrorAt cmd m!"[{c}] {p}"
  for c in xfail do
    unless problems.any (·.1 == c) do logErrorAt cmd m!"`xfail := [{c}]`, but every claim of the kind holds"

end Mumi.Spec
