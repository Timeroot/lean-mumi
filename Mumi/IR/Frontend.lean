module

public import Lean
public import Mumi.IR.Basic
public import Mumi.Options

public section

/-! A deliberately bounded syntax frontend for positive, unindexed IR blocks.
Every generated command is elaborated and kernel checked normally. No temporary
axioms, unchecked declarations, or sorry terms are used by this frontend.
-/

namespace Mumi.IndRec
open Lean Elab Command

structure Binder where
  name : Name
  type : Syntax
  deriving Inhabited

structure Field extends Binder where
  target : Option Nat := none
  domain : Array Binder := #[]
  deriving Inhabited

structure Ctor where
  name : Name
  fields : Array Field
  deriving Inhabited

structure Member where
  name : Name
  ctors : Array Ctor
  deriving Inhabited

structure Decoder where
  name : Name
  target : Nat
  major : Name
  result : Syntax
  clauses : Array Syntax
  deriving Inhabited

structure Block where
  members : Array Member
  decoders : Array Decoder
  params : Array Binder
  level : String
  deriving Inhabited

private def par (s : String) := "(" ++ s ++ ")"
private def join (xs : Array String) := String.intercalate " " xs.toList
private def app (f : String) (xs : Array String) := par (f ++ " " ++ join xs)
private def pname (n : Name) := n.toString
private def aux (n : Name) (suffix := "") : String :=
  (n.getPrefix ++ Name.mkSimple ("_ir_" ++ n.getString! ++ suffix)).toString
private def sem (m : Member) := aux m.name "_Sem"
private def graph (m : Member) := aux m.name
private def good (m : Member) := aux m.name "_Good"
private def raw (m : Member) := aux m.name "_Raw"
private def semVar (f : Field) := "_ir_sem_" ++ f.name.toString
private def ihVar (f : Field) := "_ir_ih_" ++ f.name.toString
private def outField (i : Nat) := "_ir_out" ++ toString i
private def pArgs (b : Block) := b.params.map (pname ∘ Binder.name)
private def atParams (b : Block) (n : String) := app n (pArgs b)
private def typeAt (b : Block) (i : Nat) := atParams b b.members[i]!.name.toString

private def parseTerm (s : String) : CommandElabM Syntax := do
  match Parser.runParserCategory (← getEnv) `term s with
  | .ok t => return t
  | .error e => throwError "IR frontend generated an invalid term:\n{s}\n{e}"

private def text (s : Syntax) : CommandElabM String := do
  return (← liftCoreM <| PrettyPrinter.ppTerm ⟨s⟩).pretty

private partial def exposeDefs (s attr : Syntax) : Syntax :=
  if s.isOfKind ``Parser.Command.declaration && s[1].isOfKind ``Parser.Command.definition then
    let old := s[0][1]
    let attrs := if old.getNumArgs == 0 then attr else
      old.setArg 0 (old[0].setArg 1 (mkNullNode (old[0][1].getArgs ++ #[mkAtom ",", attr[0][1][0]])))
    s.setArg 0 (s[0].setArg 1 attrs)
  else if s.isOfKind ``Parser.Command.«mutual» then
    s.setArg 1 (mkNullNode (s[1].getArgs.map (exposeDefs · attr)))
  else s

private def emit (s : String) : CommandElabM Unit := do
  trace[Mumi.ir] "{s}"
  let stx ← match Parser.runParserCategory (← getEnv) `command s with
    | .ok t => pure t
    | .error e => throwError "IR frontend generated an invalid declaration:\n{s}\n{e}"
  let .ok template := Parser.runParserCategory (← getEnv) `command "@[expose] def _ir_expose_template := 0"
    | throwError "IR frontend could not parse its exposure attribute"
  let stx := if (← getEnv).header.isModule then exposeDefs stx template[0][1] else stx
  let n := (← get).messages.reportedPlusUnreported.size
  try
    if stx.isOfKind ``Parser.Command.universe then elabCommand stx
    else
      withScope (fun sc => { sc with opts := sc.opts.setBool `linter.unusedVariables false }) do
        elabCommand stx
  catch e => throwError "While generating IR declaration:\n{s}\n{← e.toMessageData.toString}"
  let errors := ((← get).messages.reportedPlusUnreported.toList.drop n).filter (·.severity == .error)
  unless errors.isEmpty do
    let messages ← errors.mapM (fun e => e.data.toString)
    throwError "While generating IR declaration:\n{s}\n{String.intercalate "\n" messages}"

initialize registerTraceClass `Mumi.ir

private partial def unparen (s : Syntax) : Syntax :=
  if s.isOfKind ``Parser.Term.paren then unparen s[1] else s

private partial def unapp (s : Syntax) : Syntax × Array Syntax :=
  let s := unparen s
  if s.isOfKind ``Parser.Term.app then
    let (f, xs) := unapp s[0]
    (f, xs ++ s[1].getArgs)
  else (s, #[])

private def same (s : Syntax) (n : Name) : Bool := s.isIdent && s.getId == n

private partial def subst (s : Syntax) (pairs : Array (Name × Syntax)) : Syntax :=
  if s.isIdent then
    match pairs.find? (·.1 == s.getId) with
    | some (_, t) => t
    | none =>
      match pairs.find? (fun (n,t) => t.isIdent && n.isPrefixOf s.getId) with
      | some (n,t) => mkIdentFrom s (s.getId.replacePrefix n t.getId)
      | none => s
  else match s with
    | .node info k args => .node info k (args.map (subst · pairs))
    | _ => s

private def binders (s : Syntax) : CommandElabM (Array Binder) := do
  unless s.isOfKind ``Parser.Term.explicitBinder && s[2].getNumArgs == 2 && s[3].getNumArgs == 0 do
    throwErrorAt s "IR prototype requires explicitly typed, explicit binders (no defaults)"
  s[1].getArgs.mapM fun n => do
    unless n.isIdent do throwErrorAt n "IR prototype requires named binders"
    if n.getId.toString.startsWith "_ir_" then throwErrorAt n "Names beginning with '_ir_' are reserved inside IR blocks"
    return { name := n.getId, type := s[2][1] }

private def telescopeHead (s : Syntax) (n := 0) : CommandElabM (Array Binder × Syntax) := do
  let s := unparen s
  if s.isOfKind ``Parser.Term.arrow then
    return (#[{ name := Name.mkSimple ("_ir_arg" ++ toString n), type := s[0] }], s[2])
  if s.isOfKind ``Parser.Term.depArrow then
    let bs ← binders s[0]
    return (bs, s[2])
  if s.isOfKind ``Parser.Term.forall then
    let bs ← if s[2].getNumArgs == 0 then s[1].getArgs.flatMapM binders else
      s[1].getArgs.mapM fun x => do
        unless x.isIdent do throwErrorAt x "IR prototype requires typed forall binders"
        return { name := x.getId, type := s[2][0][1] : Binder }
    return (bs, s[4])
  return (#[], s)

private partial def telescope (s : Syntax) (n := 0) : CommandElabM (Array Binder × Syntax) := do
  let (bs, r) ← telescopeHead s n
  if bs.isEmpty then return (bs, r)
  let (cs, result) ← telescope r (n+bs.size)
  return (bs ++ cs, result)

private def signature (s : Syntax) : CommandElabM (Array Binder × Syntax) := do
  let bs ← s[0].getArgs.flatMapM binders
  let r ← if s[1].getNumArgs == 0 then parseTerm "Type" else pure s[1][0][1]
  return (bs, r)

private def target? (members : Array Member) (params : Array Binder) (s : Syntax) : Option Nat := Id.run do
  let (head, args) := unapp s
  let some i := members.findIdx? (same head ·.name) | return none
  if args.size != params.size then return none
  if !(args.zip params).all (fun (a, p) => same a p.name) then return none
  return some i

private partial def mentions (s : Syntax) (ns : Array Name) : Bool :=
  (s.isIdent && ns.contains s.getId) || s.getArgs.any (mentions · ns)

private partial def mentionsPrefix (s : Syntax) (n : Name) : Bool :=
  (s.isIdent && n.isPrefixOf s.getId) || s.getArgs.any (mentionsPrefix · n)

-- This is a syntax frontend, not an arbitrary-term binder elaborator. Refuse
-- shadowing before doing any renaming: otherwise even an ordinary field's
-- equation could silently acquire a different meaning after substitution.
private partial def checkPatternNames (protectedNames : Array Name) (s : Syntax) : CommandElabM Unit := do
  if s.isIdent && protectedNames.contains s.getId then
    throwErrorAt s "IR prototype does not support shadowing a block, parameter, field, or equation-variable name"
  for a in s.getArgs do checkPatternNames protectedNames a

private partial def checkTermBinders (protectedNames : Array Name) (s : Syntax) : CommandElabM Unit := do
  if s.isOfKind ``Parser.Term.byTactic || s.isOfKind ``Parser.Term.byTactic' ||
      s.isOfKind ``Parser.Term.«letrec» || s.getKind == `Lean.Parser.Term.do then
    throwErrorAt s "IR prototype requires ordinary term expressions inside the block; move tactics, do notation, and local recursion to external helpers"
  if s.isOfKind ``Parser.Term.basicFun then
    for b in s[0].getArgs do
      -- Typed lambda binders parse as type ascriptions, not explicitBinder.
      if b.isOfKind ``Parser.Term.typeAscription then checkPatternNames protectedNames b[1]
      else if b.isIdent then checkPatternNames protectedNames b
      else if !(b.isOfKind ``Parser.Term.explicitBinder || b.isOfKind ``Parser.Term.implicitBinder ||
          b.isOfKind ``Parser.Term.strictImplicitBinder || b.isOfKind ``Parser.Term.instBinder) then
        checkPatternNames protectedNames b
  if s.isOfKind ``Parser.Term.explicitBinder || s.isOfKind ``Parser.Term.implicitBinder ||
      s.isOfKind ``Parser.Term.strictImplicitBinder || s.isOfKind ``Parser.Term.instBinder then
    checkPatternNames protectedNames s[1]
  if s.isOfKind ``Parser.Term.forall then
    for b in s[1].getArgs do
      if b.isIdent then checkPatternNames protectedNames b
  if s.isOfKind ``Parser.Term.letId then checkPatternNames protectedNames s
  if s.isOfKind ``Parser.Term.letIdDecl || s.isOfKind ``Parser.Term.letEqnsDecl then
    for b in s[1].getArgs do
      if b.isIdent then checkPatternNames protectedNames b
  if s.isOfKind ``Parser.Term.letPatDecl then checkPatternNames protectedNames s[0]
  if s.isOfKind ``Parser.Term.matchAlt then checkPatternNames protectedNames s[1]
  if s.isOfKind ``Parser.Term.matchDiscr then checkPatternNames protectedNames s[0]
  if s.isOfKind ``Parser.Term.namedPattern then checkPatternNames protectedNames s[0]
  if s.isOfKind ``Parser.Term.letOptEq then checkPatternNames protectedNames s[3]
  if s.isOfKind ``Parser.Term.sufficesDecl then checkPatternNames protectedNames s[0]
  if s.isOfKind ``termDepIfThenElse then checkPatternNames protectedNames s[1]
  if s.isOfKind ``termIfLet then checkPatternNames protectedNames s[2]
  for a in s.getArgs do checkTermBinders protectedNames a

private partial def checkReservedNames (s : Syntax) : CommandElabM Unit := do
  if s.isIdent && s.getId.toString.startsWith "_ir_" then
    throwErrorAt s "Names beginning with '_ir_' are reserved inside IR blocks"
  for a in s.getArgs do checkReservedNames a

private def checkDistinct (names : Array Name) (reserved : Array Name) : CommandElabM Unit := do
  let mut seen := reserved
  for n in names do
    if seen.contains n then throwError "IR prototype requires distinct binder names; '{n}' is already in scope"
    if n == `motive || n.toString.startsWith "motive_" then
      throwError "IR prototype reserves 'motive' and 'motive_...' for recursor motives"
    seen := seen.push n

private def plainModifiers (s : Syntax) : Bool := s.getArgs.all (·.getNumArgs == 0)

def isIRBlock (elems : Array Syntax) : Bool :=
  elems.all (fun e => e.isOfKind ``Parser.Command.declaration &&
    (e[1].isOfKind ``Parser.Command.«inductive» || e[1].isOfKind ``Parser.Command.definition)) &&
  elems.any (·[1].isOfKind ``Parser.Command.«inductive») &&
  elems.any (·[1].isOfKind ``Parser.Command.definition)

private def readBlock (elems : Array Syntax) : CommandElabM Block := do
  unless (← getScope).varDecls.isEmpty do
    throwError "IR prototype does not yet support section variables; write shared parameters on each declaration"
  let mut members : Array Member := #[]
  let mut params : Array Binder := #[]
  let mut level := ""
  let globalNames := elems.map (·[1][1][0].getId)
  for e in elems do
    checkReservedNames e
    unless plainModifiers e[0] do throwErrorAt e "IR prototype does not yet support declaration modifiers or attributes inside a block"
    let d := e[1]
    unless d[1][0].getId.isAtomic do
      throwErrorAt d "IR prototype requires simple declaration names; place the mutual block inside a namespace"
    unless d[1][1].getNumArgs == 0 do throwErrorAt d "IR prototype uses surrounding universe declarations, not explicit declaration universe lists"
    if d.isOfKind ``Parser.Command.«inductive» then
      let (ps, result) ← signature d[2]
      unless result.isOfKind ``Parser.Term.type do
        throwErrorAt result "IR prototype supports unindexed carriers declared in Type u"
      let l ← if result[1].getNumArgs == 0 then pure "0" else pure (result[1][0].reprint.getD "0" |>.trimAscii.toString)
      if members.isEmpty then params := ps; level := l
      else
        unless ps.size == params.size && (ps.zip params).all (fun (a,b) => a.name == b.name && a.type == b.type) do
          -- Syntax equality includes source positions; compare the rendered binders below.
          unless ps.size == params.size && (← (ps.zip params).allM fun (a,b) => do return a.name == b.name && (← text a.type) == (← text b.type)) do
            throwErrorAt d "IR prototype requires identical shared parameters on all declarations"
        unless l == level do throwErrorAt result "IR prototype requires all carriers to share the declared universe"
      unless d[6][0].getNumArgs == 0 do throwErrorAt d "IR prototype does not yet support deriving clauses"
      members := members.push { name := d[1][0].getId, ctors := #[] }
  checkDistinct (params.map (·.name)) globalNames
  for p in params do checkTermBinders (globalNames ++ params.map (·.name)) p.type
  let mut mi := 0
  for e in elems do
    let d := e[1]
    if d.isOfKind ``Parser.Command.«inductive» then
      let mut ctors := #[]
      for c in d[4].getArgs do
        unless plainModifiers c[2] do throwErrorAt c "IR prototype does not yet support constructor modifiers"
        let (bs, result) ← signature c[4]
        let (tail, result) ← telescope result bs.size
        unless c[3].getId.isAtomic do throwErrorAt c "IR prototype requires simple constructor names"
        checkDistinct ((bs ++ tail).map (·.name)) (globalNames ++ params.map (·.name))
        let result ← if c[4][1].getNumArgs == 0 then parseTerm (app members[mi]!.name.toString (params.map (pname ∘ Binder.name))) else pure result
        unless target? members params result == some mi do throwErrorAt c "IR constructor must return its own carrier at the unchanged parameters"
        let fs ← (bs ++ tail).mapM fun f => do
          checkTermBinders (globalNames ++ params.map (·.name) ++ (bs ++ tail).map (·.name)) f.type
          let (domain, r) ← telescope f.type
          let target := target? members params r
          if target.isNone && mentions f.type (members.map (·.name)) then
            throwErrorAt f.type "IR recursive occurrences must be a carrier or a function returning a carrier; nested and negative occurrences are not supported"
          if domain.any (fun x => mentions x.type (members.map (·.name))) && target.isSome then
            throwErrorAt f.type "IR recursive argument domains cannot contain the carriers themselves"
          let mut renamed := #[]
          let mut pairs := #[]
          for k in [:domain.size] do
            let x := domain[k]!
            let name := Name.mkSimple ("_ir_index_" ++ f.name.toString ++ "_" ++ toString k)
            renamed := renamed.push { name, type := subst x.type pairs : Binder }
            pairs := pairs.push (x.name, mkIdent name)
          return { f with target, domain := if target.isSome then renamed else #[] : Field }
        ctors := ctors.push { name := c[3].getId, fields := fs }
      if ctors.isEmpty then throwErrorAt d "IR prototype currently requires at least one constructor per carrier"
      members := members.modify mi fun m => { m with ctors }
      mi := mi+1
  let mut decoders := #[]
  for e in elems do
    let d := e[1]
    if d.isOfKind ``Parser.Command.definition then
      let (ps, ty) ← signature d[2]
      unless ps.size == params.size && (← (ps.zip params).allM fun (a,b) => do return a.name == b.name && (← text a.type) == (← text b.type)) do
        throwErrorAt d "IR decoder must repeat the shared parameters, followed by a single carrier argument in its result signature"
      let (args, result) ← telescopeHead ty
      unless args.size == 1 do throwErrorAt ty "IR decoder must have signature Carrier → Result or (a : Carrier) → Result"
      let some i := target? members params args[0]!.type | throwErrorAt ty "IR decoder must recurse over a carrier of this block"
      checkDistinct (args.map (·.name)) (globalNames ++ params.map (·.name))
      checkTermBinders (globalNames ++ params.map (·.name) ++ args.map (·.name)) result
      unless d[3].isOfKind ``Parser.Command.declValEqns do throwErrorAt d[3] "IR prototype requires equation-style decoder definitions"
      let eqns := d[3][0]
      unless eqns[1].getArgs.all (·.getNumArgs == 0) && eqns[2].getNumArgs == 0 do
        throwErrorAt eqns "IR prototype does not accept termination annotations or where declarations"
      let alts := eqns[0][0].getArgs
      let mut clauses := Array.replicate members[i]!.ctors.size Syntax.missing
      for alt in alts do
        unless alt[1].getNumArgs == 1 && alt[1][0].getNumArgs == 1 do throwErrorAt alt "IR equations need one flat constructor pattern"
        let (h, xs) := unapp alt[1][0][0]
        let n := if h.isOfKind ``Parser.Term.dotIdent then h[1].getId else h.getId
        let some ci := members[i]!.ctors.findIdx? (fun c => n == c.name || n == members[i]!.name ++ c.name)
          | throwErrorAt h "Unknown constructor in IR equation"
        let c := members[i]!.ctors[ci]!
        unless xs.size == c.fields.size && xs.all (·.isIdent) do throwErrorAt alt "IR equations require one variable for each constructor field (no nested patterns)"
        checkDistinct (xs.map (·.getId)) (globalNames ++ params.map (·.name))
        checkTermBinders (globalNames ++ params.map (·.name) ++ c.fields.map (·.name) ++ xs.map (·.getId)) alt[3]
        for f in c.fields do
          if !(xs.any (same · f.name)) && mentionsPrefix alt[3] f.name then
            throwErrorAt alt[3] "IR equation would capture constructor field name '{f.name}'; use the constructor's variable names or qualify the external reference"
        unless clauses[ci]!.isMissing do throwErrorAt alt "Duplicate IR constructor equation"
        let pairs := xs.zip c.fields |>.map fun (x,f) => (x.getId, mkIdent f.name)
        clauses := clauses.set! ci (subst alt[3] pairs)
      if clauses.any (·.isMissing) then throwErrorAt d "IR decoder must have exactly one equation for every constructor"
      decoders := decoders.push { name := d[1][0].getId, target := i, major := args[0]!.name, result, clauses }
  return { members, decoders, params, level }

private def fieldDecl (f : Binder) : CommandElabM String := do
  return par (f.name.toString ++ " : " ++ (← text f.type))
private def paramsDecl (b : Block) : CommandElabM String := return join (← b.params.mapM fieldDecl)
private def fieldsDecl (fs : Array Field) : CommandElabM String := return join (← fs.mapM (fieldDecl ∘ Field.toBinder))
private def names (fs : Array Field) := fs.map (pname ∘ Binder.name ∘ Field.toBinder)
private def lambda (bs : Array Binder) (body : String) : CommandElabM String := do
  if bs.isEmpty then return body
  return par ("fun " ++ join (← bs.mapM fieldDecl) ++ " => " ++ body)
private def forallS (bs : Array Binder) (body : String) : CommandElabM String := do
  if bs.isEmpty then return body
  return par ("∀ " ++ join (← bs.mapM fieldDecl) ++ ", " ++ body)
private def applyDomain (f : String) (bs : Array Binder) :=
  if bs.isEmpty then f else app f (bs.map (pname ∘ Binder.name))

-- A semantic occurrence is permitted only at an earlier recursive field.
private partial def semantic (b : Block) (sources : Array (Name × String)) (s : Syntax) : CommandElabM Syntax := do
  let (head, args) := unapp s
  if let some di := b.decoders.findIdx? (same head ·.name) then
    unless args.size >= b.params.size+1 do throwErrorAt s "IR decoder calls must be fully applied to a recursive field"
    unless (args.extract 0 b.params.size |>.zip b.params).all (fun (a,p) => same a p.name) do
      throwErrorAt s "IR decoder parameters must remain unchanged"
    let (x, ys) := unapp args[b.params.size]!
    let some (_, image) := sources.find? (same x ·.1)
      | throwErrorAt s "IR decoder calls must target an earlier recursive field (possibly applied to its arguments)"
    let ys ← ys.mapM (semantic b sources)
    let ysText ← ys.mapM text
    let base := if image.isEmpty then outField di else
      par (app image ysText) ++ "." ++ outField di
    let extra ← (args.extract (b.params.size+1) args.size).mapM (semantic b sources)
    let extraText ← extra.mapM text
    return ← parseTerm (if extra.isEmpty then base else app base extraText)
  if s.isIdent && (sources.any (·.1 == s.getId) || b.members.any (·.name == s.getId) || b.decoders.any (·.name == s.getId)) then
    throwErrorAt s "IR continuations may use recursive fields only through their decoders"
  if s.isOfKind ``Parser.Term.explicitBinder then
    for n in s[1].getArgs do
      if sources.any (·.1 == n.getId) then throwErrorAt n "IR prototype does not support shadowing a recursive field name"
  match s with
  | .node info k xs => return .node info k (← xs.mapM (semantic b sources))
  | _ => return s

private def semText (b : Block) (src : Array (Name × String)) (s : Syntax) : CommandElabM String :=
  semantic b src s >>= text
private def sources (c : Ctor) := c.fields.filterMap fun f => f.target.map fun _ => (f.name, semVar f)
private def ctorValue (b : Block) (i ci : Nat) : CommandElabM String := do
  let c := b.members[i]!.ctors[ci]!
  let vals ← (b.decoders.filter (·.target == i)).mapM fun d => semText b (sources c) d.clauses[ci]!
  return "⟨" ++ String.intercalate ", " (if vals.isEmpty then ["PUnit.unit"] else vals.toList) ++ "⟩"

private def emitSemantics (b : Block) : CommandElabM Unit := do
  let ps ← paramsDecl b
  for i in [:b.members.size] do
    let mut fields := #[]
    for j in [:b.decoders.size] do
      let d := b.decoders[j]!
      if d.target == i then
        fields := fields.push ("  " ++ outField j ++ " : " ++ (← semText b #[(d.major, "")] d.result))
    if fields.isEmpty then fields := #["  _unit : PUnit"]
    emit ("structure " ++ sem b.members[i]! ++ " " ++ ps ++ " : Type (" ++ b.level ++ "+1) where\n" ++ String.intercalate "\n" fields.toList)

private def graphFields (b : Block) (c : Ctor) : CommandElabM String := do
  let mut out := #[]
  let mut earlier := #[]
  for f in c.fields do
    if let some i := f.target then
      let dom ← f.domain.mapM fun x => do return { x with type := ← semantic b earlier x.type }
      out := out.push (par (semVar f ++ " : " ++ (← forallS dom (atParams b (sem b.members[i]!)))))
      out := out.push (par (f.name.toString ++ " : " ++ (← forallS dom (app (atParams b (graph b.members[i]!)) #[applyDomain (semVar f) dom]))))
      earlier := earlier.push (f.name, semVar f)
    else out := out.push (par (f.name.toString ++ " : " ++ (← semText b earlier f.type)))
  return join out

private def emitUpper (b : Block) : CommandElabM Unit := do
  let ps ← paramsDecl b
  let mut ds := #[]
  for i in [:b.members.size] do
    let m := b.members[i]!
    let mut cs := #[]
    for ci in [:m.ctors.size] do
      let c := m.ctors[ci]!
      cs := cs.push ("  | " ++ c.name.toString ++ " " ++ (← graphFields b c) ++ " : " ++ app (atParams b (graph m)) #[(← ctorValue b i ci)])
    ds := ds.push ("inductive " ++ graph m ++ " " ++ ps ++ " : " ++ atParams b (sem m) ++ " → Type (" ++ b.level ++ "+1) where\n" ++ String.intercalate "\n" cs.toList)
  emit ("mutual\n" ++ String.intercalate "\n" ds.toList ++ "\nend")
  for m in b.members do
    emit ("@[reducible] def " ++ m.name.toString ++ " " ++ ps ++ " : Type (" ++ b.level ++ "+1) := Mumi.IR.Graph.Carrier " ++ par (atParams b (graph m)))
  for j in [:b.decoders.size] do
    let d := b.decoders[j]!
    let result := subst d.result #[(d.major, mkIdent `_ir_self)]
    emit ("@[reducible] def " ++ d.name.toString ++ " " ++ ps ++ " (_ir_self : " ++ typeAt b d.target ++ ") : " ++ (← text result) ++ " := _ir_self.1." ++ outField j)
  for i in [:b.members.size] do
    let m := b.members[i]!
    for ci in [:m.ctors.size] do
      let c := m.ctors[ci]!
      let mut xs := #[]
      for f in c.fields do
        if f.target.isSome then
          xs := xs.push (← lambda f.domain (par (applyDomain f.name.toString f.domain) ++ ".1"))
          xs := xs.push (← lambda f.domain (par (applyDomain f.name.toString f.domain) ++ ".2"))
        else xs := xs.push f.name.toString
      let attrs := if c.fields.isEmpty then "@[reducible, match_pattern] " else "@[reducible] "
      emit (attrs ++ "def " ++ m.name.toString ++ "." ++ c.name.toString ++ " " ++ ps ++ " " ++ (← fieldsDecl c.fields) ++ " : " ++ typeAt b i ++ " := ⟨_, " ++ app (graph m ++ "." ++ c.name.toString) xs ++ "⟩")

private def motive (i : Nat) := if i == 0 then "motive" else "motive_" ++ toString (i+1)
private def minor (b : Block) (i ci : Nat) := Id.run do
  let c := b.members[i]!.ctors[ci]!
  let count := b.members.foldl (fun n m => n + (m.ctors.filter (·.name == c.name)).size) 0
  let n := if count == 1 then c.name.toString else
    b.members[i]!.name.toString.replace "." "_" ++ "_" ++ c.name.toString
  let used := b.params.any (fun p => p.name.toString == n) ||
    b.members.any (fun m => m.ctors.any (fun c => c.fields.any (fun f => f.name.toString == n)))
  return if used then "_ir_case" ++ toString i ++ "_" ++ toString ci else n
private def motiveArgs (b : Block) := (Array.range b.members.size).map motive
private def minorArgs (b : Block) := (Array.range b.members.size).flatMap fun i => (Array.range b.members[i]!.ctors.size).map (minor b i)
private def motiveDecls (b : Block) := join ((Array.range b.members.size).map fun i => "{" ++ motive i ++ " : " ++ typeAt b i ++ " → Sort _ir_elim}")
private def ctorApp (b : Block) (i ci : Nat) (xs : Array String) :=
  app (b.members[i]!.name.toString ++ "." ++ b.members[i]!.ctors[ci]!.name.toString) (pArgs b ++ xs)

private def minorDecls (b : Block) (induction : Bool) : CommandElabM String := do
  let mut out := #[]
  for i in [:b.members.size] do
    for ci in [:b.members[i]!.ctors.size] do
      let c := b.members[i]!.ctors[ci]!
      let mut ihs := #[]
      if induction then
        for f in c.fields do
          if let some j := f.target then
            ihs := ihs.push (par (ihVar f ++ " : " ++ (← forallS f.domain (app (motive j) #[applyDomain f.name.toString f.domain]))))
      let ty := "∀ " ++ (← fieldsDecl c.fields) ++ " " ++ join ihs ++ ", " ++ app (motive i) #[ctorApp b i ci (names c.fields)]
      let ty := if c.fields.isEmpty then app (motive i) #[ctorApp b i ci #[]] else ty
      out := out.push (par (minor b i ci ++ " : " ++ ty))
  return join out

private def emitUpperRec (b : Block) : CommandElabM Unit := do
  let ps ← paramsDecl b
  let common := ps ++ " " ++ motiveDecls b ++ " " ++ (← minorDecls b true)
  let args := pArgs b ++ motiveArgs b ++ minorArgs b
  let mut ds := #[]
  for i in [:b.members.size] do
    let m := b.members[i]!
    let mut cs := #[]
    for ci in [:m.ctors.size] do
      let c := m.ctors[ci]!
      let mut pats := #[]
      let mut ihs := #[]
      let mut images := #[]
      -- Domain annotations refer to decoded values, which are available in this graph case.
      for f in c.fields do
        if let some j := f.target then
          pats := pats.push (semVar f) |>.push f.name.toString
          let dom ← f.domain.mapM fun x => do return { x with type := ← semantic b (sources c) x.type }
          images := images.push (← lambda dom ("⟨" ++ applyDomain (semVar f) dom ++ ", " ++ applyDomain f.name.toString dom ++ "⟩"))
          ihs := ihs.push (← lambda dom (app ("@" ++ b.members[j]!.name.toString ++ "._ir_rec") (args ++ #[applyDomain (semVar f) dom, applyDomain f.name.toString dom])))
        else
          pats := pats.push f.name.toString
          images := images.push f.name.toString
      cs := cs.push ("  | ." ++ c.name.toString ++ " " ++ join pats ++ " => " ++ app (minor b i ci) (images ++ ihs))
    let termination := if m.ctors.any (fun c => c.fields.any (·.target.isSome)) then "\ntermination_by structural _ir_code" else ""
    ds := ds.push ("def " ++ m.name.toString ++ "._ir_rec " ++ common ++ " {_ir_sem : " ++ atParams b (sem m) ++ "} (_ir_code : " ++ app (atParams b (graph m)) #["_ir_sem"] ++ ") : " ++ app (motive i) #["⟨_ir_sem, _ir_code⟩"] ++ " :=\n  match _ir_code with\n" ++ String.intercalate "\n" cs.toList ++ termination)
  emit ("mutual\n" ++ String.intercalate "\n" ds.toList ++ "\nend")
  for i in [:b.members.size] do
    let m := b.members[i]!
    emit ("@[elab_as_elim, induction_eliminator] def " ++ m.name.toString ++ ".rec " ++ common ++ " (_ir_self : " ++ typeAt b i ++ ") : " ++ app (motive i) #["_ir_self"] ++ " := " ++ app ("@" ++ m.name.toString ++ "._ir_rec") (args ++ #["_ir_self.1", "_ir_self.2"]))

private def sortName (b : Block) := aux b.members[0]!.name "_Sort"
private def sigName (b : Block) := aux b.members[0]!.name "_sig"
private def dName (b : Block) := aux b.members[0]!.name "_D"
private def sortValue (b : Block) (i : Nat) := "⟨" ++ sortName b ++ ".s" ++ toString i ++ "⟩"
private def tagName (m : Member) := aux m.name "_Tag"
private def signatureAt (b : Block) := atParams b (sigName b)
private def relationAt (b : Block) := par ("Mumi.IR.model " ++ signatureAt b) ++ ".lt"

private def rawSyntax (b : Block) (s : Syntax) : CommandElabM Syntax := do
  let mut pairs := #[]
  for m in b.members do pairs := pairs.push (m.name, ← parseTerm (raw m))
  for d in b.decoders do pairs := pairs.push (d.name, ← parseTerm (aux d.name))
  return subst s pairs

private def rawFields (b : Block) (c : Ctor) : CommandElabM (Array Field) :=
  c.fields.mapM fun f => do
    let ty ← rawSyntax b f.type
    let domain ← f.domain.mapM fun x => do return { x with type := ← rawSyntax b x.type }
    return { f with type := ty, domain }

private def packedType (b : Block) (dom : Array Binder) : CommandElabM String := do
  let mut t := "PUnit.{1}"
  for x in dom.reverse do t := par (par (x.name.toString ++ " : " ++ (← text x.type)) ++ " ×' " ++ t)
  return "ULift.{" ++ b.level ++ "} " ++ par t

private def packedValue (dom : Array Binder) : String := Id.run do
  let mut t := "PUnit.unit"
  for x in dom.reverse do t := "⟨" ++ x.name.toString ++ ", " ++ t ++ "⟩"
  return "⟨" ++ t ++ "⟩"

private def unpacked (dom : Array Binder) (p : String) : Array String := Id.run do
  let mut t := p ++ ".down"
  let mut out := #[]
  for _ in dom do
    out := out.push (t ++ ".1")
    t := t ++ ".2"
  return out

private def tuple (tag : String) (values : Array String) : String := Id.run do
  let mut t := "PUnit.unit"
  for x in values.reverse do t := "⟨" ++ x ++ ", " ++ t ++ "⟩"
  return "⟨⟨" ++ tag ++ "⟩, " ++ t ++ "⟩"

private def rawCtorApp (b : Block) (i ci : Nat) (xs : Array String) :=
  app (raw b.members[i]! ++ "." ++ b.members[i]!.ctors[ci]!.name.toString) (pArgs b ++ xs)

private def certType (b : Block) (f : Field) : CommandElabM String := do
  let some i := f.target | return "True"
  return ← forallS f.domain (app (atParams b (good b.members[i]!)) #[applyDomain f.name.toString f.domain])

private def certDecls (b : Block) (fs : Array Field) : CommandElabM String := do
  return join (← (fs.filter (·.target.isSome)).mapM fun f => do
    return par (ihVar f ++ " : " ++ (← certType b f)))

private def shapeProp (b : Block) (i ci : Nat) (fs : Array Field) (node : String) : CommandElabM String := do
  let certs ← (fs.filter (·.target.isSome)).mapM (certType b)
  return par (node ++ " = " ++ rawCtorApp b i ci (names fs)) ++ " ∧ " ++
    String.intercalate " ∧ " (certs.toList ++ ["True"])

private def tuplePattern (m : Member) (c : Ctor) : String :=
  tuple (tagName m ++ "." ++ c.name.toString) (c.fields.map fun f =>
    if f.target.isSome then "_ir_packed_" ++ f.name.toString else "⟨⟨" ++ f.name.toString ++ ", PUnit.unit⟩⟩")

private def fieldLets (b : Block) (fs : Array Field) (pred : Bool) : CommandElabM String := do
  let mut out := ""
  for f in fs do
    if let some j := f.target then
      let v := app ("_ir_packed_" ++ f.name.toString) #[packedValue f.domain]
      let v := if pred then app "Mumi.IR.raise" #[signatureAt b, relationAt b, "(children := _ir_children)", sortValue b j, v] else v
      out := out ++ "let " ++ f.name.toString ++ " := " ++ (← lambda f.domain v) ++ "; "
  return out

private def emitLower (b : Block) : CommandElabM Unit := do
  let ps ← paramsDecl b
  emit ("inductive " ++ sortName b ++ " where\n" ++ String.intercalate "\n" ((Array.range b.members.size).toList.map fun i => "  | s" ++ toString i))
  for m in b.members do
    emit ("inductive " ++ tagName m ++ " where\n" ++ String.intercalate "\n" (m.ctors.toList.map fun c => "  | " ++ c.name.toString))
  emit ("def " ++ dName b ++ " " ++ ps ++ " : ULift.{" ++ b.level ++ "} " ++ sortName b ++ " → Type (" ++ b.level ++ "+1)\n" ++
    String.intercalate "\n" ((Array.range b.members.size).toList.map fun i => "  | " ++ sortValue b i ++ " => " ++ atParams b (sem b.members[i]!)))
  let mut ss := #[]
  for i in [:b.members.size] do
    let m := b.members[i]!
    let mut cs := #[]
    for ci in [:m.ctors.size] do
      let c := m.ctors[ci]!
      let mut body := ".ret " ++ (← ctorValue b i ci)
      for fi in (List.range c.fields.size).reverse do
        let f := c.fields[fi]!
        let earlier := sources { c with fields := c.fields.extract 0 fi }
        if let some j := f.target then
          let dom ← f.domain.mapM fun x => do return { x with type := ← semantic b earlier x.type }
          let val := app ("_ir_values_" ++ f.name.toString) #[packedValue dom]
          body := ".delta " ++ par (← packedType b dom) ++ " (fun _ => " ++ sortValue b j ++ ") (fun _ir_values_" ++ f.name.toString ++ " => let " ++ semVar f ++ " := " ++ (← lambda dom val) ++ "; " ++ body ++ ")"
        else
          body := ".sigma (ULift.{" ++ b.level ++ "} ((_ : " ++ (← semText b earlier f.type) ++ ") ×' PUnit.{1})) (fun _ir_box_" ++ f.name.toString ++ " => let " ++ f.name.toString ++ " := _ir_box_" ++ f.name.toString ++ ".down.1; " ++ body ++ ")"
      cs := cs.push ("    | ." ++ c.name.toString ++ " => " ++ body)
    ss := ss.push ("  | " ++ sortValue b i ++ " => .choose " ++ tagName m ++ " (fun\n" ++ String.intercalate "\n" cs.toList ++ ")")
  emit ("def " ++ sigName b ++ " " ++ ps ++ " : Mumi.IR.Signature (ULift.{" ++ b.level ++ "} " ++ sortName b ++ ") " ++ par (atParams b (dName b)) ++ "\n" ++ String.intercalate "\n" ss.toList)
  for i in [:b.members.size] do
    emit ("noncomputable def " ++ raw b.members[i]! ++ " " ++ ps ++ " : Type " ++ b.level ++ " := Mumi.IR.Raw " ++ signatureAt b ++ " " ++ sortValue b i)
  for j in [:b.decoders.size] do
    let d := b.decoders[j]!
    let result ← rawSyntax b (subst d.result #[(d.major, mkIdent `_ir_self)])
    emit ("@[reducible] noncomputable def " ++ aux d.name ++ " " ++ ps ++ " (_ir_self : " ++ atParams b (raw b.members[d.target]!) ++ ") : " ++ (← text result) ++ " := (Mumi.IR.decode " ++ signatureAt b ++ " " ++ sortValue b d.target ++ " _ir_self)." ++ outField j)
  for i in [:b.members.size] do
    let m := b.members[i]!
    for c in m.ctors do
      let fs ← rawFields b c
      let values := fs.map fun f => if f.target.isSome then
        "(fun _ir_position => " ++ app f.name.toString (unpacked f.domain "_ir_position") ++ ")"
        else "⟨⟨" ++ f.name.toString ++ ", PUnit.unit⟩⟩"
      emit ("noncomputable def " ++ raw m ++ "." ++ c.name.toString ++ " " ++ ps ++ " " ++ (← fieldsDecl fs) ++ " : " ++ atParams b (raw m) ++ " := Mumi.IR.roll " ++ signatureAt b ++ " " ++ sortValue b i ++ " " ++ tuple (tagName m ++ "." ++ c.name.toString) values)
  let mut gs := #[]
  for i in [:b.members.size] do
    let m := b.members[i]!
    let mut cs := #[]
    for ci in [:m.ctors.size] do
      let c := m.ctors[ci]!
      let fs ← rawFields b c
      cs := cs.push ("  | " ++ c.name.toString ++ " " ++ (← fieldsDecl fs) ++ " " ++ (← certDecls b fs) ++ " : " ++ app (atParams b (good m)) #[rawCtorApp b i ci (names fs)])
    gs := gs.push ("inductive " ++ good m ++ " " ++ ps ++ " : " ++ atParams b (raw m) ++ " → Prop where\n" ++ String.intercalate "\n" cs.toList)
  emit ("mutual\n" ++ String.intercalate "\n" gs.toList ++ "\nend")
  for m in b.members do
    emit ("def " ++ m.name.toString ++ " " ++ ps ++ " : Type " ++ b.level ++ " := { a : " ++ atParams b (raw m) ++ " // " ++ app (atParams b (good m)) #["a"] ++ " }")
  for d in b.decoders do
    let result := subst d.result #[(d.major, mkIdent `_ir_self)]
    emit ("@[reducible] noncomputable def " ++ d.name.toString ++ " " ++ ps ++ " (_ir_self : " ++ typeAt b d.target ++ ") : " ++ (← text result) ++ " := " ++ app (aux d.name) (pArgs b ++ #["_ir_self.val"]))
  for i in [:b.members.size] do
    let m := b.members[i]!
    for ci in [:m.ctors.size] do
      let c := m.ctors[ci]!
      let mut values := #[]
      let mut certs := #[]
      for f in c.fields do
        if f.target.isSome then
          values := values.push (← lambda f.domain (par (applyDomain f.name.toString f.domain) ++ ".val"))
          certs := certs.push (← lambda f.domain (par (applyDomain f.name.toString f.domain) ++ ".property"))
        else values := values.push f.name.toString
      emit ("noncomputable def " ++ m.name.toString ++ "." ++ c.name.toString ++ " " ++ ps ++ " " ++ (← fieldsDecl c.fields) ++ " : " ++ typeAt b i ++ " := ⟨" ++ rawCtorApp b i ci values ++ ", " ++ app (good m ++ "." ++ c.name.toString) (values ++ certs) ++ "⟩")
  for i in [:b.members.size] do
    let m := b.members[i]!
    let mut cs := #[]
    let mut proofs := #[]
    for ci in [:m.ctors.size] do
      let c := m.ctors[ci]!
      let fs ← rawFields b c
      cs := cs.push ("  | " ++ tuplePattern m c ++ " => " ++ (← fieldLets b fs false) ++ (← shapeProp b i ci fs "_ir_self"))
      let hs := (fs.filter (·.target.isSome)).map ihVar
      proofs := proofs.push ("  | " ++ c.name.toString ++ " " ++ join (names fs ++ hs) ++ " => exact ⟨rfl, " ++ String.intercalate ", " (hs.toList ++ ["True.intro"]) ++ "⟩")
    emit ("noncomputable def " ++ aux m.name "_Shape" ++ " " ++ ps ++ " (_ir_self : " ++ atParams b (raw m) ++ ") : Mumi.IR.Args (Mumi.IR.Raw " ++ signatureAt b ++ ") (Mumi.IR.decode " ++ signatureAt b ++ ") (" ++ signatureAt b ++ " " ++ sortValue b i ++ ") → Prop\n" ++ String.intercalate "\n" cs.toList)
    emit ("theorem " ++ aux m.name "_shape" ++ " " ++ ps ++ " {_ir_self : " ++ atParams b (raw m) ++ "} (_ir_good : " ++ app (atParams b (good m)) #["_ir_self"] ++ ") : " ++ app (atParams b (aux m.name "_Shape")) #["_ir_self", "(Mumi.IR.view " ++ signatureAt b ++ " " ++ sortValue b i ++ " _ir_self)"] ++ " := by\n  cases _ir_good with\n" ++ String.intercalate "\n" proofs.toList)

private def emitLowerRec (b : Block) : CommandElabM Unit := do
  let ps ← paramsDecl b
  let common := ps ++ " " ++ motiveDecls b ++ " " ++ (← minorDecls b true)
  let args := pArgs b ++ motiveArgs b ++ minorArgs b
  let cm := aux b.members[0]!.name "_Motive"
  emit ("def " ++ cm ++ " " ++ ps ++ " " ++ motiveDecls b ++ " : (s : ULift.{" ++ b.level ++ "} " ++ sortName b ++ ") → Mumi.IR.Raw " ++ signatureAt b ++ " s → Sort _ir_elim\n" ++
    String.intercalate "\n" ((Array.range b.members.size).toList.map fun i => "  | " ++ sortValue b i ++ ", a => ∀ h : " ++ app (atParams b (good b.members[i]!)) #["a"] ++ ", " ++ app (motive i) #["⟨a, h⟩"]))
  let motiveApp := app ("@" ++ cm) (pArgs b ++ motiveArgs b)
  let mut ss := #[]
  for i in [:b.members.size] do
    let m := b.members[i]!
    let mut cs := #[]
    for ci in [:m.ctors.size] do
      let c := m.ctors[ci]!
      let fs ← rawFields b c
      let node := app "Mumi.IR.pack" #[signatureAt b, relationAt b, "_ir_stage", "_ir_children", sortValue b i, tuplePattern m c]
      let mut body := (← fieldLets b fs true) ++ "let _ir_node := " ++ node ++ "; "
      body := body ++ "let _ir_shape : " ++ (← shapeProp b i ci fs "_ir_node") ++ " := " ++ app (aux m.name "_shape") (pArgs b ++ #["_ir_good"]) ++ "; "
      let mut images := #[]
      let mut ihs := #[]
      let mut hp := "_ir_shape.2"
      for f in fs do
        if let some j := f.target then
          let proof := hp ++ ".1"
          let image := "_ir_public_" ++ f.name.toString
          body := body ++ "let " ++ image ++ " := " ++ (← lambda f.domain ("(⟨" ++ applyDomain f.name.toString f.domain ++ ", " ++ applyDomain proof f.domain ++ "⟩ : " ++ typeAt b j ++ ")")) ++ "; "
          images := images.push image
          ihs := ihs.push (← lambda f.domain (app "_ir_recurse" #[sortValue b j, app ("_ir_packed_" ++ f.name.toString) #[packedValue f.domain], applyDomain proof f.domain]))
          hp := hp ++ ".2"
        else images := images.push f.name.toString
      body := body ++ "let _ir_equal : (⟨_ir_node, _ir_good⟩ : " ++ typeAt b i ++ ") = " ++ ctorApp b i ci images ++ " := Subtype.ext _ir_shape.1; _ir_equal.symm ▸ " ++ app (minor b i ci) (images ++ ihs)
      cs := cs.push ("      | " ++ tuplePattern m c ++ " => fun _ir_good => " ++ body)
    ss := ss.push ("    | " ++ sortValue b i ++ " => match _ir_args with\n" ++ String.intercalate "\n" cs.toList)
  let recName := aux b.members[0]!.name "_induction"
  emit ("noncomputable def " ++ recName ++ " " ++ common ++ " : ∀ s a, " ++ app motiveApp #["s", "a"] ++ " :=\n  Mumi.IR.induction " ++ signatureAt b ++ " (C := " ++ motiveApp ++ ") (fun _ir_stage _ir_children _ir_sort _ir_args _ir_recurse =>\n    match _ir_sort with\n" ++ String.intercalate "\n" ss.toList ++ ")")
  for i in [:b.members.size] do
    emit ("@[elab_as_elim, induction_eliminator] noncomputable def " ++ b.members[i]!.name.toString ++ ".rec " ++ common ++ " (_ir_self : " ++ typeAt b i ++ ") : " ++ app (motive i) #["_ir_self"] ++ " := " ++ app ("@" ++ recName) (args ++ #[sortValue b i, "_ir_self.val", "_ir_self.property"]))

private def emitEquations (b : Block) (lower : Bool) : CommandElabM Unit := do
  let ps ← paramsDecl b
  for d in b.decoders do
    for ci in [:b.members[d.target]!.ctors.size] do
      let c := b.members[d.target]!.ctors[ci]!
      emit ("@[simp] theorem " ++ d.name.toString ++ "_" ++ c.name.toString ++ " " ++ ps ++ " " ++ (← fieldsDecl c.fields) ++ " : " ++ app d.name.toString (pArgs b ++ #[ctorApp b d.target ci (names c.fields)]) ++ " = " ++ par (← text d.clauses[ci]!) ++ " := rfl")
  let common := ps ++ " " ++ motiveDecls b ++ " " ++ (← minorDecls b true)
  let args := pArgs b ++ motiveArgs b ++ minorArgs b
  for i in [:b.members.size] do
    for ci in [:b.members[i]!.ctors.size] do
      let c := b.members[i]!.ctors[ci]!
      let mut ihs := #[]
      for f in c.fields do
        if let some j := f.target then
          ihs := ihs.push (← lambda f.domain (app ("@" ++ b.members[j]!.name.toString ++ ".rec") (args ++ #[applyDomain f.name.toString f.domain])))
      emit ("@[simp] theorem " ++ b.members[i]!.name.toString ++ ".rec_" ++ c.name.toString ++ " " ++ common ++ " " ++ (← fieldsDecl c.fields) ++ " : " ++ app ("@" ++ b.members[i]!.name.toString ++ ".rec") (args ++ #[ctorApp b i ci (names c.fields)]) ++ " = " ++ app (minor b i ci) (names c.fields ++ ihs) ++ " := rfl")
  let kw := if lower then "noncomputable def " else "def "
  for i in [:b.members.size] do
    let m := b.members[i]!
    emit ("@[elab_as_elim] " ++ kw ++ m.name.toString ++ ".recOn " ++ ps ++ " " ++ motiveDecls b ++ " (_ir_self : " ++ typeAt b i ++ ") " ++ (← minorDecls b true) ++ " : " ++ app (motive i) #["_ir_self"] ++ " := " ++ app ("@" ++ m.name.toString ++ ".rec") (args ++ #["_ir_self"]))

private def viewName (m : Member) := m.name.toString ++ "._ir_View"

private def emitViews (b : Block) (lower : Bool) : CommandElabM Unit := do
  let ps ← paramsDecl b
  let kw := if lower then "noncomputable def " else "def "
  let level := if lower then b.level else "(" ++ b.level ++ "+1)"
  for i in [:b.members.size] do
    let m := b.members[i]!
    let mut cs := #[]
    for ci in [:m.ctors.size] do
      let c := m.ctors[ci]!
      cs := cs.push ("  | " ++ c.name.toString ++ " " ++ (← fieldsDecl c.fields) ++ " : " ++ app (atParams b (viewName m)) #[ctorApp b i ci (names c.fields)])
    emit ("inductive " ++ viewName m ++ " " ++ ps ++ " : " ++ typeAt b i ++ " → Type " ++ level ++ " where\n" ++ String.intercalate "\n" cs.toList)
    let mut cases := #[]
    for ci in [:m.ctors.size] do
      let c := m.ctors[ci]!
      if lower then
        let fs ← rawFields b c
        let mut body := (← fieldLets b fs false)
        let mut images := #[]
        let mut hp := "_ir_shape.2"
        for f in fs do
          if let some j := f.target then
            let image := "_ir_public_" ++ f.name.toString
            body := body ++ "let " ++ image ++ " := " ++ (← lambda f.domain ("(⟨" ++ applyDomain f.name.toString f.domain ++ ", " ++ applyDomain (hp ++ ".1") f.domain ++ "⟩ : " ++ typeAt b j ++ ")")) ++ "; "
            hp := hp ++ ".2"
            images := images.push image
          else images := images.push f.name.toString
        body := body ++ "let _ir_equal : _ir_self = " ++ ctorApp b i ci images ++ " := Subtype.ext _ir_shape.1; _ir_equal.symm ▸ " ++ app (viewName m ++ "." ++ c.name.toString) images
        cases := cases.push ("    | " ++ tuplePattern m c ++ " => fun _ir_shape => " ++ body)
      else
        let mut pats := #[]
        let mut images := #[]
        for f in c.fields do
          if f.target.isSome then
            pats := pats.push (semVar f) |>.push f.name.toString
            let dom ← f.domain.mapM fun x => do return { x with type := ← semantic b (sources c) x.type }
            images := images.push (← lambda dom ("⟨" ++ applyDomain (semVar f) dom ++ ", " ++ applyDomain f.name.toString dom ++ "⟩"))
          else
            pats := pats.push f.name.toString
            images := images.push f.name.toString
        cases := cases.push ("    | ." ++ c.name.toString ++ " " ++ join pats ++ " => " ++ app (viewName m ++ "." ++ c.name.toString) images)
    let mut body := ""
    if lower then
      let argsTy := "Mumi.IR.Args (Mumi.IR.Raw " ++ signatureAt b ++ ") (Mumi.IR.decode " ++ signatureAt b ++ ") (" ++ signatureAt b ++ " " ++ sortValue b i ++ ")"
      body := "  let _ir_expose (_ir_args : " ++ argsTy ++ ") : " ++ app (atParams b (aux m.name "_Shape")) #["_ir_self.val", "_ir_args"] ++ " → " ++ app (atParams b (viewName m)) #["_ir_self"] ++ " :=\n    match _ir_args with\n" ++ String.intercalate "\n" cases.toList ++ "\n  _ir_expose (Mumi.IR.view " ++ signatureAt b ++ " " ++ sortValue b i ++ " _ir_self.val) " ++ app (aux m.name "_shape") (pArgs b ++ #["_ir_self.property"])
    else
      body := "  match _ir_self with\n  | ⟨_, _ir_code⟩ => match _ir_code with\n" ++ String.intercalate "\n" cases.toList
    emit (kw ++ m.name.toString ++ "._ir_view " ++ ps ++ " (_ir_self : " ++ typeAt b i ++ ") : " ++ app (atParams b (viewName m)) #["_ir_self"] ++ " :=\n" ++ body)
    for ci in [:m.ctors.size] do
      let c := m.ctors[ci]!
      emit ("@[simp] theorem " ++ m.name.toString ++ "._ir_view_" ++ c.name.toString ++ " " ++ ps ++ " " ++ (← fieldsDecl c.fields) ++ " : " ++ app (m.name.toString ++ "._ir_view") (pArgs b ++ #[ctorApp b i ci (names c.fields)]) ++ " = " ++ app (viewName m ++ "." ++ c.name.toString) (names c.fields) ++ " := rfl")
    let mut minors := #[]
    let mut branches := #[]
    for ci in [:m.ctors.size] do
      let c := m.ctors[ci]!
      let result := app "motive" #[ctorApp b i ci (names c.fields)]
      let decls ← fieldsDecl c.fields
      let ty := if c.fields.isEmpty then result else "∀ " ++ decls ++ ", " ++ result
      minors := minors.push (par (minor b i ci ++ " : " ++ ty))
      branches := branches.push ("  | ." ++ c.name.toString ++ " " ++ join (names c.fields) ++ " => " ++ app (minor b i ci) (names c.fields))
    let mot := "{motive : " ++ typeAt b i ++ " → Sort _ir_elim}"
    let minorNames := (Array.range m.ctors.size).map (minor b i)
    emit ("@[elab_as_elim, cases_eliminator] " ++ kw ++ m.name.toString ++ ".casesOn " ++ ps ++ " " ++ mot ++ " (_ir_self : " ++ typeAt b i ++ ") " ++ join minors ++ " : motive _ir_self :=\n  match " ++ app (m.name.toString ++ "._ir_view") (pArgs b ++ #["_ir_self"]) ++ " with\n" ++ String.intercalate "\n" branches.toList)
    emit ("@[elab_as_elim] " ++ kw ++ m.name.toString ++ ".cases " ++ ps ++ " " ++ mot ++ " " ++ join minors ++ " (_ir_self : " ++ typeAt b i ++ ") : motive _ir_self := " ++ app ("@" ++ m.name.toString ++ ".casesOn") (pArgs b ++ #["motive", "_ir_self"] ++ minorNames))
    for ci in [:m.ctors.size] do
      let c := m.ctors[ci]!
      emit ("@[simp] theorem " ++ m.name.toString ++ ".casesOn_" ++ c.name.toString ++ " " ++ ps ++ " " ++ mot ++ " " ++ join minors ++ " " ++ (← fieldsDecl c.fields) ++ " : " ++ app ("@" ++ m.name.toString ++ ".casesOn") (pArgs b ++ #["motive", ctorApp b i ci (names c.fields)] ++ minorNames) ++ " = " ++ app (minor b i ci) (names c.fields) ++ " := rfl")

def elaborate (elems : Array Syntax) : CommandElabM Unit := do
  let b ← readBlock elems
  emit "universe _ir_elim"
  emitSemantics b
  if mumi.mahlo.get (← getOptions) then
    emitLower b
    emitLowerRec b
    emitEquations b true
    emitViews b true
  else
    emitUpper b
    emitUpperRec b
    emitEquations b false
    emitViews b false

end Mumi.IndRec
