import Mumi

/-!
# A specification-driven harness for IR blocks

`ir_spec mutual … end` elaborates the block, then checks what it declared
against what Lean's own rules say such a block should declare, computed from
the block as written and nothing else:

* each carrier's type former, at the universe written (one up when
  `mumi.mahlo` is off, the graph encoding's cost);
* each constructor: the shared parameters implicit, the fields as written;
* each recursor, in the shape Lean gives a mutual or nested block, one per
  universe as a `mutual` has one: motives `motive_1`, `motive_2`, … (`motive`
  alone) for the data members and then each nested application in the order
  met, the minor premises named by their constructors, binding the fields as
  written and a hypothesis `f_ih` at each recursive field, the indices
  implicit and the major `t`, the universes the motive's and then the
  member's; a nested application's own entry `X.rec_k`;
* the `Prop` members' joint recursor, as Lean gives a block of them declared
  after the rest: into `Prop`, or into any sort where Lean's own rule allows it;
* each decoder, as written, and its equations, from its clauses.

A parameter that varies is an index: the motives take it, and the minor
premises bind it implicitly, as a constructor does.  Types must agree up to
definitional equality, binder names and annotations exactly -- of the
declaration and of each minor premise -- and no internal name (`_ir_…`,
`_nested…`, `nested_…`) may show in a public type where a reader would see it.
Then every rule the specification states -- a recursor's at each constructor, a
decoder's at each equation -- is checked: by `rfl` in the kernel, or failing
that by `simp only` with the rule's own lemma.  Each has to fall where the test
says: `rfl`, unless listed `(simp := [...])`, or `(unproven := [...])` where no
lemma states it.
-/

namespace Mumi.IRSpec
open Lean Elab Command Term Meta

/-- What the test expects beyond the default. -/
structure Options where
  /-- The rules that hold only by `simp`, by the names of their lemmas. -/
  simpRules : Array Name := #[]
  /-- The rules that hold neither way: no lemma states them. -/
  unproven : Array Name := #[]
  /-- The rules the specification stated, so that an option naming another is caught. -/
  stated : IO.Ref (Array Name)

/-- A failure, collected rather than thrown, so that one run reports them all. -/
abbrev Problems := IO.Ref (Array MessageData)

private def problem (ps : Problems) (m : MessageData) : MetaM Unit := ps.modify (·.push m)

/-! ## Reading the block -/

/-- A carrier or proposition as written. -/
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

/-- Whether a name is internal to the encoding. -/
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
the same binders down a level (minor premises), nothing internal shown. -/
def checkConst (ps : Problems) (c : Name) (expected : Expr) (innerNames := true) (levels : Option (List Name) := none) :
    MetaM Unit := do
  let some ci := (← getEnv).find? c | return ← problem ps m!"`{c}` is not declared"
  if let some ls := levels then
    unless ci.levelParams == ls do problem ps m!"`{c}` has universes {ci.levelParams}, expected {ls}"
  -- the block's universes are the ones the test wrote; another, the motive's, is to be found
  let written := (collectLevelParams {} expected).params
  let actual ← instantiateTypeLevelParams ci.toConstantVal
    (← ci.levelParams.mapM fun n => if written.contains n then pure (mkLevelParam n) else mkFreshLevelMVar)
  let leaked := (← leaks ci.type).toList.eraseDups
  unless leaked.isEmpty do problem ps m!"`{c}` shows internal names: {leaked}"
  let same ← try withReducible (isDefEq expected actual) <||> isDefEq expected actual catch _ => pure false
  unless same do
    problem ps m!"`{c}` has type{indentExpr actual}\nexpected{indentExpr expected}"
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
    problem ps m!"`{c}` binds{indentD (render a)}\nexpected{indentD (render e)}"

/-! ## The specification -/

/-- `e` with the binders of `xs` given the annotation `bi`. -/
private def withInfos {α} (xs : Array Expr) (bi : BinderInfo → BinderInfo) (k : TermElabM α) : TermElabM α := do
  let infos ← xs.mapM fun x => do return (x.fvarId!, bi (← x.fvarId!.getDecl).binderInfo)
  withNewBinderInfos infos k

/-- The names a binder group binds. -/
private def groupNames (g : Syntax) : Array Name := g[1].getArgs.map (·.getId)

/-- How many binder groups all the declarations `ds` begin with alike. -/
private def sharedGroups (ds : Array Syntax) : Nat := Id.run do
  let groups := ds.map (·[2][0].getArgs)
  let mut n := 0
  while groups.all (fun g => n < g.size) && groups.all (fun g => groupNames g[n]! == groupNames groups[0]![n]!) do
    n := n + 1
  return n

/-- The type after a member's shared parameters: its own further binders, then
what its `: T` says, `Type` if nothing. -/
private def declType (m : Member) : TermElabM Expr := do
  let d := m.decl
  Term.elabBinders m.extra fun xs => do
    let ty ← if d[2][1].getNumArgs == 0 then pure (mkSort (.succ .zero)) else Term.elabType d[2][1][0][1]
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
        Term.elabBinders c[4][0].getArgs fun fs => do
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
          forallTelescope ty fun more res => do
            let fields := own ++ fs ++ more
            return (← mkForallFVars fields res, fields.size)
      ctorTypes.modify (·.insert key e)
      pure e
  forallBoundedTelescope ty n k

/-- Where a nested application of the block is: `List U` in a field. -/
private def nestedHead? (members : Array Name) (t : Expr) : MetaM (Option Expr) := do
  let t ← instantiateMVars t
  let .const i _ := t.getAppFn | return none
  if members.contains i then return none
  unless members.any (fun m => (t.find? (·.isConstOf m)).isSome) do return none
  let some (.inductInfo _) := (← getEnv).find? i | return none
  if t.hasLooseBVars then return none
  return some t

/-- A target of the recursion: a data member, or a nested application. -/
inductive Target where
  | member (k : Nat)
  | nested (t : Expr)
  deriving Inhabited

/-- How a rule held. -/
inductive Held where
  | rfl | simp | no
  deriving BEq

instance : ToString Held where
  toString
    | .rfl => "by `rfl`"
    | .simp => "only by `simp` with its lemma"
    | .no => "neither by `rfl` nor by `simp` with a lemma"

/-- Whether `stmt` (closed, `∀ …, lhs = rhs`) holds by `rfl` in the kernel,
by `simp only [rule]`, or neither. -/
private def holds (stmt : Expr) (rule : Name) : TermElabM Held := do
  let stmt ← Term.levelMVarToParam (← instantiateMVars stmt)
  -- `rfl` in the kernel alone: Meta's unifier may wander into the stage engine
  let byRfl ← try
      let v ← forallTelescope stmt fun xs body => do
        let some (_, lhs, _) := body.eq? | throwError "not an equation"
        mkLambdaFVars xs (← mkEqRefl lhs)
      let lps := (collectLevelParams {} stmt).params.toList
      let decl := Declaration.thmDecl { name := `_spec_rfl_check, levelParams := lps, type := stmt, value := v }
      pure (Kernel.Environment.addDecl (← getEnv).toKernelEnv (← getOptions) decl matches .ok _)
    catch _ => pure false
  if byRfl then return .rfl
  unless (← getEnv).contains rule do return .no
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
private def expectRule (ps : Problems) (opts : Options) (rule : Name) (stmt : Expr) : TermElabM Unit := do
  opts.stated.modify (·.push rule)
  let h ← holds stmt rule
  let want := if opts.simpRules.contains rule then Held.simp
    else if opts.unproven.contains rule then Held.no else Held.rfl
  unless h == want do
    problem ps m!"the rule `{rule}`{indentExpr (← instantiateMVars stmt)}\nholds {h}, expected {want}"

/-- The rule lemma of recursor `r` at constructor `c`: `X.rec_c`, `X.rec_1_c`. -/
private def ruleName (r : Name) (c : Name) : Name :=
  r.getPrefix ++ Name.mkSimple (r.getString! ++ "_" ++ c.getString!)

/-- What the specification reads of the block, its parameters bound. -/
structure Block where
  members : Array Member
  /-- Each type former's type after the parameters. -/
  tys : Array Expr
  params : Array Expr
  /-- The parameters before this one are uniform; from it on they vary. -/
  uniform : Nat

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

/-- The recursors over `targets`, motives into `sort`, and if `rules` the rules. -/
private def recursion (ps : Problems) (opts : Options) (b : Block) (targets : Array Target) (sort : Expr) (rules : Bool) :
    TermElabM Unit := do
  let { members, tys, params, uniform } := b
  let uniformPs := params.extract 0 uniform
  let promotedPs := params.extract uniform params.size
  let single := targets.size == 1
  -- `motive_1`, `motive_2`, … as Lean names a mutual block's; `motive` alone
  let motiveName (t : Nat) := Name.mkSimple (if single then "motive" else "motive_" ++ toString (t + 1))
  let firstName := match targets[0]! with | .member k => members[k]!.name | .nested _ => .anonymous
  let memberCount := (targets.filter fun t => match t with | .member _ => true | _ => false).size
  let recOf (t : Nat) : Name := match targets[t]! with
    | .member k => members[k]!.name ++ `rec
    | .nested _ => firstName ++ Name.mkSimple ("rec_" ++ toString (t + 1 - memberCount))
  let targetOf (t : Expr) : Option Nat := targets.findIdx? fun x => match x with
    | .member j => t.getAppFn.isConstOf members[j]!.name
    | .nested n => n == t
  -- the index arguments a target's motive takes of a type of it
  let motiveArgs (j : Nat) (t : Expr) : Array Expr := match targets[j]! with
    | .member _ => t.getAppArgs.extract uniform t.getAppArgs.size
    | .nested _ => #[]
  let motiveTypes ← targets.mapM fun t => do
    match t with
    | .member k =>
      forallTelescope tys[k]! fun idx _ => do
        let major := mkAppN (← mkConstWithLevelParams members[k]!.name) (params ++ idx)
        withLocalDeclD `t major fun x => do mkForallFVars (promotedPs ++ idx) (← mkForallFVars #[x] sort)
    | .nested n => withLocalDeclD `t n fun x => mkForallFVars #[x] sort
  let decls := (Array.range targets.size).map fun t => (motiveName t, BinderInfo.implicit, fun (_ : Array Expr) => pure motiveTypes[t]!)
  withLocalDecls decls fun motives => do
  -- the hypotheses at a constructor's recursive fields: `f_ih`
  let withHyps {α} [Inhabited α] (fields : Array Expr) (k : Array Expr → TermElabM α) : TermElabM α := do
    let mut ds := #[]
    for f in fields do
      let some ih ← forallTelescope (← inferType f) fun dom t => do
          let t ← instantiateMVars t
          let some j := targetOf t | return none
          return some (← mkForallFVars dom (mkAppN motives[j]! ((motiveArgs j t).push (mkAppN f dom))))
        | continue
      let n := (← f.fvarId!.getDecl).userName.eraseMacroScopes
      ds := ds.push (Name.mkSimple (n.toString ++ "_ih"), BinderInfo.default, fun (_ : Array Expr) => pure ih)
    withLocalDecls ds k
  -- each constructor of each target, with its fields bound: `k ctor fields`
  let eachCtor {α} [Inhabited α] (t : Nat) (k : Name → Expr → Array Expr → Array Expr → TermElabM α) : TermElabM (Array α) := do
    match targets[t]! with
    | .member m =>
      let m := members[m]!
      m.decl[4].getArgs.mapM fun c => elabCtor m params c fun fields res => do
        let ctor := mkAppN (← mkConstWithLevelParams (m.name ++ c[3].getId)) (params ++ fields)
        k c[3].getId ctor fields (motiveArgs t res)
    | .nested n =>
      let .const ind lvls := n.getAppFn | return #[]
      let some (.inductInfo info) := (← getEnv).find? ind | return #[]
      info.ctors.toArray.mapM fun ctor => do
        let cty ← instantiateForall ((← getConstInfo ctor).instantiateTypeLevelParams lvls) n.getAppArgs
        forallTelescope cty fun fields _ =>
          k (Name.mkSimple ctor.getString!) (mkAppN (mkConst ctor lvls) (n.getAppArgs ++ fields)) fields #[]
  -- the minor premises: the fields as written, a hypothesis at each recursive one
  let mut minorDecls : Array (Name × BinderInfo × (Array Expr → TermElabM Expr)) := #[]
  for t in [:targets.size] do
    let promoted := match targets[t]! with | .member _ => promotedPs | .nested _ => #[]
    let ms ← eachCtor t fun c ctor fields idx => do
      let body ← withHyps fields fun ihs => mkForallFVars ihs (mkAppN motives[t]! (idx.push ctor))
      return (c, ← withInfos promoted (fun _ => .implicit) (mkForallFVars (promoted ++ fields) body))
    for (c, ty) in ms do
      minorDecls := minorDecls.push (c, .default, fun _ => pure ty)
  withLocalDecls minorDecls fun minors => do
  -- each recursor: the parameters, motives and minors, the indices implicit, the major `t`
  for t in [:targets.size] do
    let expected ← match targets[t]! with
      | .member k =>
        forallTelescope tys[k]! fun idx _ => do
          let major := mkAppN (← mkConstWithLevelParams members[k]!.name) (params ++ idx)
          withLocalDeclD `t major fun x => do
            withInfos (uniformPs ++ promotedPs ++ idx) (fun bi => if bi == .instImplicit then bi else .implicit) do
              mkForallFVars (uniformPs ++ motives ++ minors ++ promotedPs ++ idx ++ #[x])
                (mkAppN motives[t]! ((promotedPs ++ idx).push x))
      | .nested n =>
        withLocalDeclD `t n fun x => do
          withInfos uniformPs (fun bi => if bi == .instImplicit then bi else .implicit) do
            mkForallFVars (uniformPs ++ motives ++ minors ++ #[x]) (mkApp motives[t]! x)
    -- the motive's universe first, `u` or the first `u_i` the member's do not use
    let owner := match targets[t]! with | .member k => members[k]!.name | .nested _ => firstName
    let own := (← getConstInfo owner).levelParams
    let elim := (List.range (own.length + 1)).map (fun i => if i == 0 then `u else Name.mkSimple s!"u_{i}")
      |>.find? (!own.contains ·) |>.getD `u
    checkConst ps (recOf t) expected (levels := if sort.isProp then own else elim :: own)
  unless rules do return
  -- each rule: the recursor at a constructor is its minor premise at the recursion's values
  let recAt (t : Nat) (args : Array Expr) : TermElabM Expr := do
    instantiateMVars (← mkAppOptM (recOf t) ((uniformPs ++ motives ++ minors ++ args).map some))
  let next ← IO.mkRef 0
  for t in [:targets.size] do
    let promoted := match targets[t]! with | .member _ => promotedPs | .nested _ => #[]
    let _ ← eachCtor t fun c ctor fields idx => do
      let mi ← next.modifyGet fun n => (n, n + 1)
      let lhs ← recAt t (idx.push ctor)
      let mut ihs := #[]
      for f in fields do
        let some ih ← forallTelescope (← inferType f) fun dom ty => do
            let ty ← instantiateMVars ty
            let some j := targetOf ty | return none
            return some (← mkLambdaFVars dom (← recAt j ((motiveArgs j ty).push (mkAppN f dom))))
          | continue
        ihs := ihs.push ih
      let rhs := mkAppN minors[mi]! (promoted ++ fields ++ ihs)
      let stmt ← mkForallFVars (uniformPs ++ motives ++ minors ++ promoted ++ fields) (← mkEq lhs rhs)
      expectRule ps opts (ruleName (recOf t) c) stmt

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
private def decoderRules (ps : Problems) (opts : Options) (name : Name) (d : Syntax) : TermElabM Unit := do
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
          return ← problem ps m!"the pattern {major} of `{name}` does not fit"
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
        expectRule ps opts (name.getPrefix ++ Name.mkSimple (name.getString! ++ "_" ++ c.getString!)) stmt

/-- The whole specification of the block, checked against what it declared. -/
def specify (ps : Problems) (opts : Options) (elems : Array Syntax) : TermElabM Unit := do
  let upper := !(mumi.mahlo.get (← getOptions))
  let ns ← getCurrNamespace
  let inductives := elems.filter isInductive
  let defs := elems.filter (!isInductive ·)
  let some first := inductives[0]? | return
  let memberNames := inductives.map fun e => ns ++ e[1][1][0].getId
  -- the parameters all members declare alike; beyond them, a member's own are indices
  let shared := sharedGroups (inductives.map (·[1]))
  Term.elabBinders (first[1][2][0].getArgs.extract 0 shared) fun params => do
  -- the type formers
  let mut members : Array Member := #[]
  let mut tys : Array Expr := #[]
  for e in inductives do
    let own := e[1][2][0].getArgs
    let m : Member := { name := ns ++ e[1][1][0].getId, decl := e[1], prop := false, block := memberNames, extra := own.extract shared own.size }
    let ty ← instantiateMVars (← declType m)
    let prop ← forallTelescope ty fun _ s => pure s.isProp
    let m := { m with prop }
    members := members.push m
    tys := tys.push ty
    let bumped ← forallTelescope ty fun idx s => do
      let s := if upper && !prop then (match s with | .sort l => mkSort (.succ l) | s => s) else s
      mkForallFVars idx s
    checkConst ps m.name (← mkForallFVars params bumped) (innerNames := false)
  -- the constructors, and from which parameter on an occurrence varies them
  let mut uniform := params.size
  for m in members do
    for c in m.decl[4].getArgs do
      let vary ← elabCtor m params c fun fields res => do
        withInfos params (fun bi => if bi == .default then .implicit else bi) do
          checkConst ps (m.name ++ c[3].getId) (← mkForallFVars params (← mkForallFVars fields res)) (innerNames := false)
            (levels := (← getConstInfo m.name).levelParams)
        let mut v := params.size
        for e in (← fields.mapM fun f => inferType f).push res do
          for app in ← carrierApps memberNames (← instantiateMVars e) do
            let args := app.getAppArgs
            for j in [:min args.size params.size] do
              unless args[j]! == params[j]! do v := min v j
        pure v
      uniform := min uniform vary
  -- data and `Prop` members; a nested application of the block, in a field
  let data := (Array.range members.size).filter fun k => !members[k]!.prop
  let props := (Array.range members.size).filter fun k => members[k]!.prop
  let nestedIn (fields : Array Expr) : TermElabM (Array Expr) := do
    let mut out := #[]
    for f in fields do
      let t ← forallTelescope (← inferType f) fun _ t => instantiateMVars t
      if let some n ← nestedHead? memberNames t then out := out.push n
    return out
  let b : Block := { members, tys, params, uniform }
  let u := mkSort (.param `u_spec)
  -- the data members' recursion, into any sort: one per universe, as Lean
  -- gives a `mutual` (which has one), each with the nested applications its
  -- members meet, in the order met
  let levels ← data.mapM fun k => forallTelescope tys[k]! fun _ s => do return (← instantiateMVars s).sortLevel!.normalize
  for l in levels.toList.eraseDups do
    let group := (data.zip levels).filterMap fun (k, l') => if l' == l then some k else none
    let mut nested : Array Expr := #[]
    for k in group do
      for c in members[k]!.decl[4].getArgs do
        for n in ← elabCtor members[k]! params c fun fields _ => nestedIn fields do
          unless nested.contains n do nested := nested.push n
    let mut i := 0
    while i < nested.size do
      let n := nested[i]!
      i := i + 1
      let .const ind lvls := n.getAppFn | continue
      let some (.inductInfo info) := (← getEnv).find? ind | continue
      for ctor in info.ctors do
        let cty ← instantiateForall ((← getConstInfo ctor).instantiateTypeLevelParams lvls) n.getAppArgs
        for m in ← forallTelescope cty fun fields _ => nestedIn fields do
          unless nested.contains m do nested := nested.push m
    recursion ps opts b (group.map .member ++ nested.map .nested) u true
  -- the `Prop` members', as Lean gives a block of them declared after: into
  -- `Prop`, or into any sort where Lean allows it
  unless props.isEmpty do
    let large ← largeElim b props
    recursion ps opts b (props.map .member) (if large then u else mkSort .zero) large
  -- the decoders: their types and equations as written
  for d in defs do
    let name := ns ++ d[1][1][0].getId
    let sig ← Term.elabBinders d[1][2][0].getArgs fun bs => do
      let ty ← Term.elabType d[1][2][1][0][1]
      Term.synthesizeSyntheticMVarsNoPostponing
      mkForallFVars bs (← instantiateMVars ty)
    checkConst ps name sig (innerNames := false)
    decoderRules ps opts name d[1]

/-! ## The command -/

/-- `ir_spec mutual … end`: the block, then its specification checked.
Options name the rules that do not hold by `rfl`, by their lemmas:
`(simp := [X.rec_c, …])` those that hold only by `simp`, and
`(unproven := [d_c, …])` those that hold neither way. -/
syntax irSpecOption := "(" ident " := " "[" ident,* "]" ")"
syntax (name := irSpec) "ir_spec" irSpecOption* ppLine command : command

@[command_elab irSpec] def elabIrSpec : CommandElab := fun stx => do
  let ns ← getCurrNamespace
  let mut simpRules := #[]
  let mut unproven := #[]
  for o in stx[1].getArgs do
    let names := o[4].getSepArgs.map (ns ++ ·.getId)
    match o[1].getId with
    | `simp => simpRules := simpRules ++ names
    | `unproven => unproven := unproven ++ names
    | k => throwErrorAt o[1] "unknown ir_spec option `{k}`: `simp` or `unproven`"
  let cmd := stx[2]
  let n := (← get).messages.reportedPlusUnreported.size
  elabCommand cmd
  if ((← get).messages.reportedPlusUnreported.toList.drop n).any (·.severity == .error) then return
  let stated ← IO.mkRef #[]
  let ps ← IO.mkRef #[]
  -- under the block's own `set_option … in`
  withSetOptionIn (fun inner => do
    unless inner.isOfKind ``Parser.Command.«mutual» do throwErrorAt cmd "ir_spec expects a `mutual` block"
    -- the block's syntax elaborated again, but recorded nowhere: no linter sees it
    ctorTypes.set {}
    withEnableInfoTree false <| liftTermElabM <| withCurrHeartbeats do
      specify ps { simpRules, unproven, stated } inner[1].getArgs) cmd
  let stated ← stated.get
  for r in simpRules ++ unproven do
    unless stated.contains r do ps.modify (·.push m!"`{r}` is not a rule the specification states")
  for p in ← ps.get do logErrorAt cmd p

end Mumi.IRSpec
