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
  /-- As written: `(x : T)`, `{x : T}`, `⦃x : T⦄` or `[x : T]`, which is what the
  public declaration it is a binder of binds it as. -/
  info : BinderInfo := .default
  /-- An instance binder written without a name, `[T]`: named `inst` (`inst_1`,
  …) as Lean displays it, and bound as `[T]` again by the carrier and decoder
  declarations, whose bodies pass it as `argText`, `‹T›`. -/
  anon : Bool := false
  argText : String := ""
  deriving Inhabited

/-- Whether the binder is anything but explicit. -/
def Binder.implicit (b : Binder) : Bool := b.info != .default

/-- `d` bracketed as a binder with `info` is. -/
def bracket (info : BinderInfo) (d : String) : String :=
  match info with
  | .implicit => "{" ++ d ++ "}"
  | .strictImplicit => "⦃" ++ d ++ "⦄"
  | .instImplicit => "[" ++ d ++ "]"
  | _ => "(" ++ d ++ ")"

structure Field extends Binder where
  target : Option Nat := none
  domain : Array Binder := #[]
  deriving Inhabited

structure Ctor where
  name : Name
  fields : Array Field
  /-- The documentation written on it, `/-- … -/` with a newline, or `""`. -/
  doc : String := ""
  deriving Inhabited

structure Member where
  name : Name
  ctors : Array Ctor
  doc : String := ""
  deriving Inhabited

structure Decoder where
  name : Name
  target : Nat
  major : Name
  result : Syntax
  clauses : Array Syntax
  doc : String := ""
  deriving Inhabited

/-- The name a decoder's major premise shows: its author's, or none, `_ir_self`
(published as `t`). -/
private def selfName (d : Decoder) : Name :=
  if d.major.hasMacroScopes || d.major.toString.startsWith "_ir" then `_ir_self else d.major

structure Block where
  members : Array Member
  decoders : Array Decoder
  params : Array Binder
  level : String
  deriving Inhabited

def par (s : String) := "(" ++ s ++ ")"
def join (xs : Array String) := String.intercalate " " xs.toList
def app (f : String) (xs : Array String) := par (f ++ " " ++ join xs)
def pname (n : Name) := n.toString
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

def parseTerm (s : String) : CommandElabM Syntax := do
  match Parser.runParserCategory (← getEnv) `term s with
  | .ok t => return t
  | .error e => throwError "IR frontend generated an invalid term:\n{s}\n{e}"

def text (s : Syntax) : CommandElabM String := do
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

/-- The constants the block being declared has declared so far, with the
constructors of its inductives: what `pinUniverses` pins the universes of.
Not what Lean or `Mumi` declared alongside, whose universes are their own. -/
initialize blockConsts : IO.Ref NameSet ← IO.mkRef {}

/-- The universe of the motive of each eliminator the block has declared, named
as Lean names a recursor's: what a generated declaration binds as `_ir_elim`. -/
initialize elimUniverse : IO.Ref (NameMap Name) ← IO.mkRef {}

/-- The names a command declares, relative to the namespace. -/
private partial def declaredNames (stx : Syntax) : Array Name :=
  if stx.isOfKind ``Parser.Command.declaration then
    let d := stx[1]
    if d.isOfKind ``Parser.Command.«inductive» || d.isOfKind ``Parser.Command.structure then #[d[1][0].getId]
    else if d.getNumArgs > 1 && d[1].isOfKind ``Parser.Command.declId then #[d[1][0].getId]
    else #[]
  else if stx.isOfKind ``Parser.Command.«mutual» then stx[1].getArgs.flatMap declaredNames
  else if stx.isOfKind ``Parser.Command.in then declaredNames stx[2]
  else #[]

/-- `s` with every constant of the block it names given its universes
explicitly: the parameters it was declared with, which are the scope's
universe names it uses.  Left to inference, a reference's universes are level
metavariables, and in a block whose members sit in several polymorphic
universes the elaborator makes fresh parameters of those before the body can
pin them, and the body then fails to typecheck. -/
def pinUniverses (s : String) : CommandElabM String := do
  let env ← getEnv
  let ns ← getCurrNamespace
  let inScope := (← getScope).levelNames
  let block ← blockConsts.get
  let elims ← elimUniverse.get
  let isId (c : Char) := c.isAlphanum || c == '_' || c == '.' || c == '\'' || c.val > 127
  let a := s.toList.toArray
  let mut out := ""
  let mut i := 0
  while i < a.size do
    let c := a[i]!
    if isId c && (i == 0 || !isId a[i-1]!) then
      let mut j := i
      while j < a.size && isId a[j]! do j := j + 1
      let tok := String.mk (a.extract i j).toList
      -- a trailing `.` belongs to what follows: `.{…}` already there, or a projection
      let base := if tok.endsWith "." then tok.dropRight 1 else tok
      let pinned := tok.endsWith "." && j < a.size && a[j]! == '{'
      let mut res := tok
      -- an attribute names a declaration, bare
      let bare := out.endsWith "implemented_by " || s.startsWith "attribute ["
      if !pinned && !bare && block.contains (ns ++ base.toName) then
        if let some ci := env.find? (ns ++ base.toName) then
          -- an eliminator's motive universe, published under a name of Lean's, is
          -- the one the generated declarations bind
          let elim := elims.find? (ns ++ base.toName)
          let lps := ci.levelParams.map fun l => if elim == some l then `_ir_elim else l
          if !lps.isEmpty && lps.all inScope.contains then
            res := base ++ ".{" ++ String.intercalate ", " (lps.map toString) ++ "}" ++ (if tok.endsWith "." then "." else "")
      out := out ++ res
      i := j
    else
      out := out.push c
      i := i + 1
  return out

/-- Whether `c` may be part of an identifier. -/
private def identChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\'' || c.val > 127

/-- `s` with every occurrence of the identifier `old` -- not part of a longer
one; a projection after it is kept -- replaced by `new`. -/
def renameToken (s old new : String) : String := Id.run do
  let a := s.toList.toArray
  let o := old.toList.toArray
  let mut out := ""
  let mut i := 0
  while i < a.size do
    if a.extract i (i + o.size) == o && (i == 0 || !(identChar a[i-1]! || a[i-1]! == '.')) &&
        (i + o.size == a.size || !identChar a[i + o.size]!) then
      out := out ++ new
      i := i + o.size
    else
      out := out.push a[i]!
      i := i + 1
  return out

/-- Whether the identifier `x` occurs in `s`. -/
def mentionsToken (s x : String) : Bool := renameToken s x "\u0000" != s

/-- The identifiers `s` mentions. -/
partial def identsOf (s : Syntax) : Array Name :=
  if s.isIdent then #[s.getId] else s.getArgs.flatMap identsOf

/-- `x`, or `x_1`, `x_2`, … : the first that is not `taken`. -/
private def freshFrom (taken : String → Bool) (x : String) : String := Id.run do
  let mut n := x
  let mut i := 1
  while taken n do
    n := x ++ "_" ++ toString i
    i := i + 1
  return n

/-- The minor premise at constructor `ci` of member `i`, as the frontend
writes it: a name of its own, which a public declaration shows as the
constructor's, `c`, as Lean does, however many members have one. -/
def minorVar (i ci : Nat) (c : Name) : String :=
  "_ir_minor_" ++ toString i ++ "_" ++ toString ci ++ "_" ++ c.toString

/-- The constructor name in a minor premise's own, `_ir_minor_i_ci_c`. -/
private def minorCtor (tok : String) : String :=
  match ((tok.drop "_ir_minor_".length).toString.splitOn "_").drop 2 with
  | [] => tok
  | cs =>
    let c := "_".intercalate cs
    -- the nested pass's own name for a constructor it renames, `_nested_c`
    if c.startsWith "_nested_" then (c.drop "_nested_".length).toString else c

/-- The distinct identifiers in `s` that begin with `pre`. -/
private def tokensWith (s pre : String) : Array String :=
  (((s.splitOn pre).drop 1).map fun piece => pre ++ String.mk (piece.toList.takeWhile identChar)).eraseDups.toArray

/-- How many times the identifier `x` occurs in `s`. -/
private def occurrences (s x : String) : Nat :=
  ((renameToken s x "\u0000").toList.filter (· == '\u0000')).length

/-- The type of a public declaration with its binders named as Lean names
them: the major premise `t`, the hypothesis at field `x` `x_ih`, the minor
premise at constructor `c` `c` -- or, where the type refers to one by name,
the first name of that sort that says nothing else.  `outer` are the names the
declaration's own binders give, which a later binder could capture. -/
private def publicType (ty : String) (outer : Array String) : String := Id.run do
  let mut ty := ty
  if mentionsToken ty "_ir_self" then
    ty := renameToken ty "_ir_self" (freshFrom outer.contains "t")
  for old in tokensWith ty "_ir_ih_" do
    ty := renameToken ty old (freshFrom (mentionsToken ty) ((old.drop "_ir_ih_".length).toString ++ "_ih"))
  for old in tokensWith ty "_ir_minor_" do
    let c := minorCtor old
    -- bound and never mentioned: the constructor's name, as two minors may share
    let new := if occurrences ty old == 1 && !outer.contains c then c else freshFrom (mentionsToken ty) c
    ty := renameToken ty old new
  return ty

/-- Whether `s` names something the public binders rename. -/
private def internalBinders (s : String) : Bool :=
  mentionsToken s "_ir_self" || !(tokensWith s "_ir_ih_").isEmpty || !(tokensWith s "_ir_minor_").isEmpty

/-- The first node in `s` of one of the kinds `k`. -/
private partial def findKind (k : Array SyntaxNodeKind) (s : Syntax) : Option Syntax :=
  if k.any s.isOfKind then some s else s.getArgs.findSome? (findKind k)

/-- A public declaration `s` (parsed, `cmd`) with its binders as Lean names
them.  Those before the colon move into the type, `def f bs : T := v` written
`def f : ∀ bs, T := fun bs => v`: the type takes the public names and the
value keeps the frontend's own, so that the value refers to each binder by a
name of its own. -/
private def publish (s : String) (cmd : Syntax) : String := Id.run do
  let some sig := findKind #[``Parser.Command.declSig, ``Parser.Command.optDeclSig] cmd | return s
  let some val := findKind #[``Parser.Command.declValSimple, ``Parser.Command.declValEqns] cmd | return s
  let ty := if sig.isOfKind ``Parser.Command.declSig then sig[1] else sig[1][0]
  let (some sigStart, some colon, some valStart) := (sig.getPos?, ty.getPos?, val.getPos?) | return s
  let binders := (String.Pos.Raw.extract s sigStart colon).trim
  let type := (String.Pos.Raw.extract s colon valStart).trim.drop 1 |>.toString.trim
  unless internalBinders binders || internalBinders type do return s
  let pre := String.Pos.Raw.extract s 0 sigStart
  let value := String.Pos.Raw.extract s valStart s.rawEndPos
  let outer := (sig[0].getArgs.flatMap fun b => identsOf b[1]).map (·.toString)
  if binders.isEmpty then
    return pre ++ " : " ++ publicType type outer ++ " " ++ value
  let body := if val.isOfKind ``Parser.Command.declValSimple then (value.trim.drop 2).toString else "fun\n" ++ value
  return pre ++ " : ∀ " ++ publicType (binders ++ ", " ++ type) outer ++ " :=\n  fun " ++ binders ++ " =>\n  " ++ body

/-- The universe names `s` writes: in `Sort l`, `Type l` and `c.{l, …}`. -/
private def universesIn (s : String) : Array Name := Id.run do
  let a := s.toList.toArray
  let mut out := #[]
  let mut i := 0
  while i < a.size do
    -- where a universe expression starts, and how far it runs
    let start? : Option Nat :=
      if a[i]! == '.' && a[i+1]? == some '{' then some (i + 2)
      else if (String.mk (a.extract i (i + 5)).toList == "Sort " || String.mk (a.extract i (i + 5)).toList == "Type ") &&
          (i == 0 || !identChar a[i-1]!) then some (i + 5)
      else none
    match start? with
    | none => i := i + 1
    | some j =>
      -- a bracketed expression to its close; else one identifier
      let mut k := j
      let mut depth := 0
      let bracketed := a[j]? == some '(' || a[i]! == '.'
      while k < a.size && (if bracketed then !(depth == 0 && (a[k]! == ')' || a[k]! == '}') && k > j) || (a[k]! == '(' && k == j)
          else identChar a[k]!) do
        if a[k]! == '(' then depth := depth + 1
        if a[k]! == ')' then depth := depth - 1
        k := k + 1
      let expr := String.mk (a.extract j k).toList
      for w in (expr.split fun c => !identChar c) do
        let w := w.toString
        if !w.isEmpty && !(w.all Char.isDigit) && w != "max" && w != "imax" then out := out.push (Name.mkSimple w)
      i := k
  return out

/-- The nodes in `s` of kind `k`. -/
private partial def allKind (k : SyntaxNodeKind) (s : Syntax) : Array Syntax :=
  if s.isOfKind k then #[s] else s.getArgs.flatMap (allKind k)

/-- An eliminator's universes as Lean orders and names a recursor's: the
motive's first, `u` or the first `u_i` the others do not use, then those of the
member it eliminates -- for the public one, and for the companions it is
implemented by alike.  The declarations list them all, so these are to be
taken out of the section's while they are elaborated: it returns them. -/
private def elimUniverses (s : String) (cmd : Syntax) : CommandElabM (String × List Name) := do
  unless mentionsToken s "_ir_elim" do return (s, [])
  let ns ← getCurrNamespace
  let block ← blockConsts.get
  let ids := allKind ``Parser.Command.declId cmd
  -- each declaration a member's, and one list for all, as a `mutual` has
  let mut found : Option (List Name) := none
  for id in ids do
    unless id[1].isNone do return (s, [])
    let owner := (ns ++ id[0].getId).getPrefix
    let some ci := (← getEnv).find? owner | return (s, [])
    unless block.contains owner do return (s, [])
    if found.any (· != ci.levelParams) then return (s, [])
    found := some ci.levelParams
  let some own := found | return (s, [])
  -- what the declaration names besides; a universe of the section it does not
  -- name is no matter, as it is not the kernel's for Lean's own
  let others := own ++ ((universesIn s).filter (!own.contains ·)).toList
  let mut elim := `u
  let mut i := 1
  while others.contains elim do
    elim := Name.mkSimple ("u_" ++ toString i)
    i := i + 1
  let listed := ".{" ++ ", ".intercalate ((elim :: own).map toString) ++ "}"
  -- from the last, so that the positions before stay
  let mut s := s
  for id in ids.reverse do
    let some tail := id[0].getTailPos? | return (s, [])
    s := String.Pos.Raw.extract s 0 tail ++ listed ++ String.Pos.Raw.extract s tail s.rawEndPos
  return (renameToken s "_ir_elim" elim.toString, elim :: own)

/-- Whether a declared name is public, its binders displayed: an eliminator the
block's public one is restated from (`X._ir_elim_casesOn`, see `Mumi.Displayed`) is. -/
private def isPublic (n : Name) : Bool :=
  !n.components.any fun c =>
    let c := c.toString
    (c.startsWith "_ir" && !c.startsWith "_ir_elim_") ||
      c.startsWith "_nested"

/-- The names of the binders of a recursive field's domain: each its own, or `a`
for one written as an arrow, as Lean names it, fresh against `avoid`. -/
def domainNames (xs : Array Name) (avoid : Array Name) : Array Name := Id.run do
  let mut out := #[]
  for x in xs do
    let base := if x.toString.startsWith "_ir_arg" then "a" else x.toString
    let mut n := Name.mkSimple base
    let mut i := 1
    while avoid.contains n || out.contains n do
      n := Name.mkSimple (base ++ "_" ++ toString i)
      i := i + 1
    out := out.push n
  return out

/-- A declaration as Lean's own would read: a public one's binders, and an
eliminator's universes, named as Lean names them; and the section's universes
it lists itself. -/
private def publicForm (s : String) : CommandElabM (String × List Name) := do
  let .ok t := Parser.runParserCategory (← getEnv) `command s | return (s, [])
  let s := if (declaredNames t).any isPublic then publish s t else s
  let .ok t := Parser.runParserCategory (← getEnv) `command s | return (s, [])
  elimUniverses s t

def emit (s : String) : CommandElabM Unit := do
  let s ← pinUniverses s
  -- a public declaration's binders are displayed: they get the names Lean gives them
  let (s, listed) ← publicForm s
  trace[Mumi.ir] "{s}"
  let stx ← match Parser.runParserCategory (← getEnv) `command s with
    | .ok t => pure t
    | .error e => throwError "IR frontend generated an invalid declaration:\n{s}\n{e}"
  let .ok template := Parser.runParserCategory (← getEnv) `command "@[expose] def _ir_expose_template := 0"
    | throwError "IR frontend could not parse its exposure attribute"
  let stx := if (← getEnv).header.isModule then exposeDefs stx template[0][1] else stx
  let n := (← get).messages.reportedPlusUnreported.size
  try
    if stx.isOfKind ``Parser.Command.universe then
      -- declared once per scope: a block's later components reuse it
      let names := stx[1].getArgs.map (·.getId)
      unless names.all (← getScope).levelNames.contains do elabCommand stx
    else
      let opts (o : Options) := (o.setBool `linter.unusedVariables false).setBool `linter.unusedSimpArgs false
      withScope (fun sc => { sc with opts := opts sc.opts, levelNames := sc.levelNames.filter (!listed.contains ·) }) do
        elabCommand stx
  catch e => throwError "While generating IR declaration:\n{s}\n{← e.toMessageData.toString}"
  let errors := ((← get).messages.reportedPlusUnreported.toList.drop n).filter (·.severity == .error)
  unless errors.isEmpty do
    let messages ← errors.mapM (fun e => e.data.toString)
    throwError "While generating IR declaration:\n{s}\n{String.intercalate "\n" messages}"
  -- what this declared, with the constructors of an inductive, is the block's
  let ns ← getCurrNamespace
  let env ← getEnv
  for n in declaredNames stx do
    let n := ns ++ n
    if env.contains n then
      blockConsts.modify (·.insert n)
      if let some elim := listed.head? then elimUniverse.modify (·.insert n elim)
      if let some (.inductInfo info) := env.find? n then
        for c in info.ctors do blockConsts.modify (·.insert c)

/-- A `def`, `noncomputable` only where the code generator cannot follow: at
the universe a block is written at every primitive has a run-time
implementation, so it ordinarily can. -/
def emitDefinition (attrs rest : String) : CommandElabM Unit := do
  let saved ← get
  try emit (attrs ++ "def " ++ rest)
  catch _ =>
    set saved
    emit (attrs ++ "noncomputable def " ++ rest)

initialize registerTraceClass `Mumi.ir

partial def unparen (s : Syntax) : Syntax :=
  if s.isOfKind ``Parser.Term.paren then unparen s[1] else s

partial def unapp (s : Syntax) : Syntax × Array Syntax :=
  let s := unparen s
  if s.isOfKind ``Parser.Term.app then
    let (f, xs) := unapp s[0]
    (f, xs ++ s[1].getArgs)
  else (s, #[])

def same (s : Syntax) (n : Name) : Bool := s.isIdent && s.getId == n

partial def subst (s : Syntax) (pairs : Array (Name × Syntax)) : Syntax :=
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

def binders (s : Syntax) : CommandElabM (Array Binder) := do
  if s.isOfKind ``Parser.Term.instBinder then
    -- `[x : T]` or `[T]`
    if s[1].getNumArgs == 0 then
      return #[{ name := `_ir_inst, type := s[2], info := .instImplicit, anon := true,
                 argText := "‹" ++ (← text s[2]) ++ "›" }]
    let n := s[1][0]
    if n.getId.toString.startsWith "_ir_" then throwErrorAt n "Names beginning with '_ir_' are reserved inside IR blocks"
    return #[{ name := n.getId, type := s[2], info := .instImplicit }]
  let info : BinderInfo :=
    if s.isOfKind ``Parser.Term.implicitBinder then .implicit
    else if s.isOfKind ``Parser.Term.strictImplicitBinder then .strictImplicit
    else .default
  unless (s.isOfKind ``Parser.Term.explicitBinder && s[3].getNumArgs == 0 || info != .default) && s[2].getNumArgs == 2 do
    throwErrorAt s "IR prototype requires explicitly typed binders (no default values)"
  s[1].getArgs.mapM fun n => do
    unless n.isIdent do throwErrorAt n "IR prototype requires named binders"
    if n.getId.toString.startsWith "_ir_" then throwErrorAt n "Names beginning with '_ir_' are reserved inside IR blocks"
    return { name := n.getId, type := s[2][1], info }

def telescopeHead (s : Syntax) (n := 0) : CommandElabM (Array Binder × Syntax) := do
  let s := unparen s
  if s.isOfKind ``Parser.Term.arrow then
    return (#[{ name := Name.mkSimple ("_ir_arg" ++ toString n), type := s[0] }], s[2])
  if s.isOfKind ``Parser.Term.depArrow then
    let bs ← binders s[0]
    return (bs, s[2])
  if s.isOfKind ``Parser.Term.forall then
    -- a binder without a type is left to inference, as a hole
    let bs ← if s[2].getNumArgs == 0 then s[1].getArgs.flatMapM (fun x => do
        if x.isIdent then return #[{ name := x.getId, type := ← parseTerm "_" : Binder }] else binders x)
      else s[1].getArgs.mapM fun x => do
        unless x.isIdent do throwErrorAt x "IR prototype requires named forall binders"
        return { name := x.getId, type := s[2][0][1] : Binder }
    return (bs, s[4])
  return (#[], s)

partial def telescope (s : Syntax) (n := 0) : CommandElabM (Array Binder × Syntax) := do
  let (bs, r) ← telescopeHead s n
  if bs.isEmpty then return (bs, r)
  let (cs, result) ← telescope r (n+bs.size)
  return (bs ++ cs, result)

def signature (s : Syntax) : CommandElabM (Array Binder × Syntax) := do
  let bs ← s[0].getArgs.flatMapM binders
  -- an anonymous instance is named as Lean displays it, the same on every declaration
  let mut out := #[]
  let mut k := 0
  for b in bs do
    if b.anon then
      out := out.push { b with name := Name.mkSimple (if k == 0 then "inst" else "inst_" ++ toString k) }
      k := k + 1
    else out := out.push b
  let bs := out
  let r ← if s[1].getNumArgs == 0 then parseTerm "Type" else pure s[1][0][1]
  return (bs, r)

private def target? (members : Array Member) (params : Array Binder) (s : Syntax) : Option Nat := Id.run do
  let (head, args) := unapp s
  let some i := members.findIdx? (same head ·.name) | return none
  if args.size != params.size then return none
  if !(args.zip params).all (fun (a, p) => same a p.name) then return none
  return some i

partial def mentions (s : Syntax) (ns : Array Name) : Bool :=
  (s.isIdent && ns.contains s.getId) || s.getArgs.any (mentions · ns)

partial def mentionsPrefix (s : Syntax) (n : Name) : Bool :=
  (s.isIdent && n.isPrefixOf s.getId) || s.getArgs.any (mentionsPrefix · n)

-- This is a syntax frontend, not an arbitrary-term binder elaborator. Refuse
-- shadowing before doing any renaming: otherwise even an ordinary field's
-- equation could silently acquire a different meaning after substitution.
partial def checkPatternNames (protectedNames : Array Name) (s : Syntax) : CommandElabM Unit := do
  if s.isIdent && protectedNames.contains s.getId then
    throwErrorAt s "IR prototype does not support shadowing a block, parameter, field, or equation-variable name"
  for a in s.getArgs do checkPatternNames protectedNames a

partial def checkTermBinders (protectedNames : Array Name) (s : Syntax) : CommandElabM Unit := do
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

partial def checkReservedNames (s : Syntax) : CommandElabM Unit := do
  if s.isIdent && s.getId.toString.startsWith "_ir_" then
    throwErrorAt s "Names beginning with '_ir_' are reserved inside IR blocks"
  for a in s.getArgs do checkReservedNames a

def checkDistinct (names : Array Name) (reserved : Array Name) : CommandElabM Unit := do
  let mut seen := reserved
  for n in names do
    if seen.contains n then throwError "IR prototype requires distinct binder names; '{n}' is already in scope"
    if n == `motive || n.toString.startsWith "motive_" then
      throwError "IR prototype reserves 'motive' and 'motive_...' for recursor motives"
    seen := seen.push n

/-- Whether declaration modifiers are empty, a documentation comment aside. -/
def plainModifiers (s : Syntax) : Bool := (s.getArgs.extract 1 s.getNumArgs).all (·.getNumArgs == 0)
/-- The documentation comment of declaration modifiers, or of a constructor's
optional one, as text to put before a declaration. -/
def docOf (s : Syntax) : String :=
  let s := if s.isOfKind ``Parser.Command.declModifiers then s[0] else s
  if s.getNumArgs == 0 then "" else ((s[0].reprint.getD "").trimAscii.toString) ++ "\n"

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
      if ps.any (·.implicit) then throwErrorAt d "IR prototype takes shared parameters explicit; write `(x : T)`"
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
      members := members.push { name := d[1][0].getId, ctors := #[], doc := docOf e[0] }
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
          let fresh := domainNames (domain.map (·.name))
            (globalNames ++ params.map (·.name) ++ (bs ++ tail).map (·.name) ++
              (identsOf f.type).filter fun n => !(domain.map (·.name)).contains n)
          for k in [:domain.size] do
            let x := domain[k]!
            let name := fresh[k]!
            renamed := renamed.push { name, type := subst x.type pairs : Binder }
            pairs := pairs.push (x.name, mkIdent name)
          return { f with target, domain := if target.isSome then renamed else #[] : Field }
        ctors := ctors.push { name := c[3].getId, fields := fs, doc := docOf c[0] }
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
      decoders := decoders.push { name := d[1][0].getId, target := i, major := args[0]!.name, result, clauses, doc := docOf e[0] }
  return { members, decoders, params, level }

private def fieldDecl (f : Binder) : CommandElabM String := do
  let d := f.name.toString ++ " : " ++ (← text f.type)
  return bracket f.info d
private def paramsDecl (b : Block) : CommandElabM String := return join (← b.params.mapM fieldDecl)
/-- The shared parameters as a public constructor or eliminator binds them:
implicit, as Lean's own do.  Every application the frontend writes of one is
`@`-qualified and positional. -/
private def pubParamsDecl (b : Block) : CommandElabM String :=
  return join (← b.params.mapM fun p => fieldDecl { p with info := .implicit })
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
    emit (m.doc ++ "@[reducible] def " ++ m.name.toString ++ " " ++ ps ++ " : Type (" ++ b.level ++ "+1) := Mumi.IR.Graph.Carrier " ++ par (atParams b (graph m)))
  for j in [:b.decoders.size] do
    let d := b.decoders[j]!
    let self := selfName d
    let result := subst d.result #[(d.major, mkIdent self)]
    emit (d.doc ++ "@[reducible] def " ++ d.name.toString ++ " " ++ ps ++ " (" ++ self.toString ++ " : " ++ typeAt b d.target ++ ") : " ++ (← text result) ++ " := " ++ self.toString ++ ".1." ++ outField j)
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
      emit (c.doc ++ attrs ++ "def " ++ m.name.toString ++ "." ++ c.name.toString ++ " " ++ (← pubParamsDecl b) ++ " " ++ (← fieldsDecl c.fields) ++ " : " ++ typeAt b i ++ " := ⟨_, " ++ app (graph m ++ "." ++ c.name.toString) xs ++ "⟩")

/-- The motive of member `i` of a joint recursion, `motive_1`, `motive_2`, …,
as Lean names a mutual block's; `single` when there is one motive, then
`motive`, as Lean names an inductive's. -/
def motiveFor (single : Bool) (i : Nat) := if single then "motive" else "motive_" ++ toString (i+1)

/-- `s` with every occurrence of the identifier `motive` -- the whole word, so not
`motive_1` -- renamed to `to`: a one-motive eliminator written over `motive`
takes the name the joint recursor gives the member's motive, as Lean's does. -/
def renameMotive (to s : String) : String := Id.run do
  if to == "motive" then return s
  let word (c : Char) := c.isAlphanum || c == '_' || c == '\'' || c == '.' || c == '?' || c == '!'
  let cs := s.toList.toArray
  let pat := "motive".toList.toArray
  let mut out := ""
  let mut i := 0
  while i < cs.size do
    let isAt := i + pat.size ≤ cs.size && (List.range pat.size).all (fun k => cs[i + k]! == pat[k]!)
    let before := i == 0 || !word cs[i - 1]!
    let after := i + pat.size ≥ cs.size || !word cs[i + pat.size]!
    if isAt && before && after then
      out := out ++ to
      i := i + pat.size
    else
      out := out.push cs[i]!
      i := i + 1
  return out
private def motive (b : Block) (i : Nat) := motiveFor (b.members.size == 1) i
private def minor (b : Block) (i ci : Nat) := minorVar i ci b.members[i]!.ctors[ci]!.name
private def motiveArgs (b : Block) := (Array.range b.members.size).map (motive b)
private def minorArgs (b : Block) := (Array.range b.members.size).flatMap fun i => (Array.range b.members[i]!.ctors.size).map (minor b i)
private def motiveDecls (b : Block) := join ((Array.range b.members.size).map fun i => "{" ++ motive b i ++ " : (t : " ++ typeAt b i ++ ") → Sort _ir_elim}")
/-- `@X.c params xs`. -/
private def ctorApp (b : Block) (i ci : Nat) (xs : Array String) :=
  app ("@" ++ b.members[i]!.name.toString ++ "." ++ b.members[i]!.ctors[ci]!.name.toString) (pArgs b ++ xs)

private def minorDecls (b : Block) (induction : Bool) : CommandElabM String := do
  let mut out := #[]
  for i in [:b.members.size] do
    for ci in [:b.members[i]!.ctors.size] do
      let c := b.members[i]!.ctors[ci]!
      let mut ihs := #[]
      if induction then
        for f in c.fields do
          if let some j := f.target then
            ihs := ihs.push (par (ihVar f ++ " : " ++ (← forallS f.domain (app (motive b j) #[applyDomain f.name.toString f.domain]))))
      let ty := "∀ " ++ (← fieldsDecl c.fields) ++ " " ++ join ihs ++ ", " ++ app (motive b i) #[ctorApp b i ci (names c.fields)]
      let ty := if c.fields.isEmpty then app (motive b i) #[ctorApp b i ci #[]] else ty
      out := out.push (par (minor b i ci ++ " : " ++ ty))
  return join out

private def emitUpperRec (b : Block) : CommandElabM Unit := do
  let ps ← paramsDecl b
  let common := ps ++ " " ++ motiveDecls b ++ " " ++ (← minorDecls b true)
  let pubCommon := (← pubParamsDecl b) ++ " " ++ motiveDecls b ++ " " ++ (← minorDecls b true)
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
    ds := ds.push ("def " ++ m.name.toString ++ "._ir_rec " ++ common ++ " {_ir_sem : " ++ atParams b (sem m) ++ "} (_ir_code : " ++ app (atParams b (graph m)) #["_ir_sem"] ++ ") : " ++ app (motive b i) #["⟨_ir_sem, _ir_code⟩"] ++ " :=\n  match _ir_code with\n" ++ String.intercalate "\n" cs.toList ++ termination)
  emit ("mutual\n" ++ String.intercalate "\n" ds.toList ++ "\nend")
  for i in [:b.members.size] do
    let m := b.members[i]!
    emit ("@[elab_as_elim, induction_eliminator] def " ++ m.name.toString ++ ".rec " ++ pubCommon ++ " (_ir_self : " ++ typeAt b i ++ ") : " ++ app (motive b i) #["_ir_self"] ++ " := " ++ app ("@" ++ m.name.toString ++ "._ir_rec") (args ++ #["_ir_self.1", "_ir_self.2"]))

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
    emitDefinition "" (raw b.members[i]! ++ " " ++ ps ++ " : Type " ++ b.level ++ " := Mumi.IR.Raw " ++ signatureAt b ++ " " ++ sortValue b i)
  for j in [:b.decoders.size] do
    let d := b.decoders[j]!
    let result ← rawSyntax b (subst d.result #[(d.major, mkIdent `_ir_self)])
    emitDefinition "@[reducible] " (aux d.name ++ " " ++ ps ++ " (_ir_self : " ++ atParams b (raw b.members[d.target]!) ++ ") : " ++ (← text result) ++ " := (Mumi.IR.decode " ++ signatureAt b ++ " " ++ sortValue b d.target ++ " _ir_self)." ++ outField j)
  for i in [:b.members.size] do
    let m := b.members[i]!
    for c in m.ctors do
      let fs ← rawFields b c
      let values := fs.map fun f => if f.target.isSome then
        "(fun _ir_position => " ++ app f.name.toString (unpacked f.domain "_ir_position") ++ ")"
        else "⟨⟨" ++ f.name.toString ++ ", PUnit.unit⟩⟩"
      emitDefinition "" (raw m ++ "." ++ c.name.toString ++ " " ++ ps ++ " " ++ (← fieldsDecl fs) ++ " : " ++ atParams b (raw m) ++ " := Mumi.IR.roll " ++ signatureAt b ++ " " ++ sortValue b i ++ " " ++ tuple (tagName m ++ "." ++ c.name.toString) values)
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
    emit (m.doc ++ "def " ++ m.name.toString ++ " " ++ ps ++ " : Type " ++ b.level ++ " := { a : " ++ atParams b (raw m) ++ " // " ++ app (atParams b (good m)) #["a"] ++ " }")
  for d in b.decoders do
    let self := selfName d
    let result := subst d.result #[(d.major, mkIdent self)]
    emitDefinition (d.doc ++ "@[reducible] ") (d.name.toString ++ " " ++ ps ++ " (" ++ self.toString ++ " : " ++ typeAt b d.target ++ ") : " ++ (← text result) ++ " := " ++ app (aux d.name) (pArgs b ++ #[self.toString ++ ".val"]))
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
      emitDefinition c.doc (m.name.toString ++ "." ++ c.name.toString ++ " " ++ (← pubParamsDecl b) ++ " " ++ (← fieldsDecl c.fields) ++ " : " ++ typeAt b i ++ " := ⟨" ++ rawCtorApp b i ci values ++ ", " ++ app (good m ++ "." ++ c.name.toString) (values ++ certs) ++ "⟩")
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
    emitDefinition "" (aux m.name "_Shape" ++ " " ++ ps ++ " (_ir_self : " ++ atParams b (raw m) ++ ") : Mumi.IR.Args (Mumi.IR.Raw " ++ signatureAt b ++ ") (Mumi.IR.decode " ++ signatureAt b ++ ") (" ++ signatureAt b ++ " " ++ sortValue b i ++ ") → Prop\n" ++ String.intercalate "\n" cs.toList)
    emit ("theorem " ++ aux m.name "_shape" ++ " " ++ ps ++ " {_ir_self : " ++ atParams b (raw m) ++ "} (_ir_good : " ++ app (atParams b (good m)) #["_ir_self"] ++ ") : " ++ app (atParams b (aux m.name "_Shape")) #["_ir_self", "(Mumi.IR.view " ++ signatureAt b ++ " " ++ sortValue b i ++ " _ir_self)"] ++ " := by\n  cases _ir_good with\n" ++ String.intercalate "\n" proofs.toList)

private def emitLowerRec (b : Block) : CommandElabM Unit := do
  let ps ← paramsDecl b
  let common := ps ++ " " ++ motiveDecls b ++ " " ++ (← minorDecls b true)
  let pubCommon := (← pubParamsDecl b) ++ " " ++ motiveDecls b ++ " " ++ (← minorDecls b true)
  let args := pArgs b ++ motiveArgs b ++ minorArgs b
  let cm := aux b.members[0]!.name "_Motive"
  emit ("def " ++ cm ++ " " ++ ps ++ " " ++ motiveDecls b ++ " : (s : ULift.{" ++ b.level ++ "} " ++ sortName b ++ ") → Mumi.IR.Raw " ++ signatureAt b ++ " s → Sort _ir_elim\n" ++
    String.intercalate "\n" ((Array.range b.members.size).toList.map fun i => "  | " ++ sortValue b i ++ ", a => ∀ h : " ++ app (atParams b (good b.members[i]!)) #["a"] ++ ", " ++ app (motive b i) #["⟨a, h⟩"]))
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
  emitDefinition "" (recName ++ " " ++ common ++ " : ∀ s a, " ++ app motiveApp #["s", "a"] ++ " :=\n  Mumi.IR.induction " ++ signatureAt b ++ " (C := " ++ motiveApp ++ ") (fun _ir_stage _ir_children _ir_sort _ir_args _ir_recurse =>\n    match _ir_sort with\n" ++ String.intercalate "\n" ss.toList ++ ")")
  for i in [:b.members.size] do
    emitDefinition "@[elab_as_elim, induction_eliminator] " (b.members[i]!.name.toString ++ ".rec " ++ pubCommon ++ " (_ir_self : " ++ typeAt b i ++ ") : " ++ app (motive b i) #["_ir_self"] ++ " := " ++ app ("@" ++ recName) (args ++ #[sortValue b i, "_ir_self.val", "_ir_self.property"]))

private def emitEquations (b : Block) : CommandElabM Unit := do
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
  for i in [:b.members.size] do
    let m := b.members[i]!
    emitDefinition "@[elab_as_elim] " (m.name.toString ++ ".recOn " ++ (← pubParamsDecl b) ++ " " ++ motiveDecls b ++ " (_ir_self : " ++ typeAt b i ++ ") " ++ (← minorDecls b true) ++ " : " ++ app (motive b i) #["_ir_self"] ++ " := " ++ app ("@" ++ m.name.toString ++ ".rec") (args ++ #["_ir_self"]))

private def viewName (m : Member) := m.name.toString ++ "._ir_View"

private def emitViews (b : Block) (lower : Bool) : CommandElabM Unit := do
  let ps ← paramsDecl b
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
    emitDefinition "" (m.name.toString ++ "._ir_view " ++ ps ++ " (_ir_self : " ++ typeAt b i ++ ") : " ++ app (atParams b (viewName m)) #["_ir_self"] ++ " :=\n" ++ body)
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
    -- the motive named as the joint recursor names this member's, over a major `t`
    let cmot := "{motive : (t : " ++ typeAt b i ++ ") → Sort _ir_elim}"
    emitDefinition "@[elab_as_elim, cases_eliminator] " (renameMotive (motive b i) (m.name.toString ++ ".casesOn " ++ (← pubParamsDecl b) ++ " " ++ cmot ++ " (_ir_self : " ++ typeAt b i ++ ") " ++ join minors ++ " : motive _ir_self :=\n  match " ++ app (m.name.toString ++ "._ir_view") (pArgs b ++ #["_ir_self"]) ++ " with\n" ++ String.intercalate "\n" branches.toList))
    emitDefinition "@[elab_as_elim] " (m.name.toString ++ ".cases " ++ (← pubParamsDecl b) ++ " " ++ mot ++ " " ++ join minors ++ " (_ir_self : " ++ typeAt b i ++ ") : motive _ir_self := " ++ app ("@" ++ m.name.toString ++ ".casesOn") (pArgs b ++ #["motive", "_ir_self"] ++ minorNames))
    for ci in [:m.ctors.size] do
      let c := m.ctors[ci]!
      emit ("@[simp] theorem " ++ m.name.toString ++ ".casesOn_" ++ c.name.toString ++ " " ++ ps ++ " " ++ mot ++ " " ++ join minors ++ " " ++ (← fieldsDecl c.fields) ++ " : " ++ app ("@" ++ m.name.toString ++ ".casesOn") (pArgs b ++ #["motive", ctorApp b i ci (names c.fields)] ++ minorNames) ++ " = " ++ app (minor b i ci) (names c.fields) ++ " := rfl")

def elaborate (elems : Array Syntax) : CommandElabM Unit := do
  let b ← readBlock elems
  blockConsts.set {}
  elimUniverse.set {}
  emit "universe _ir_elim"
  emitSemantics b
  if mumi.mahlo.get (← getOptions) then
    emitLower b
    emitLowerRec b
    emitEquations b
    emitViews b true
  else
    emitUpper b
    emitUpperRec b
    emitEquations b
    emitViews b false

end Mumi.IndRec
