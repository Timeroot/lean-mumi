/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public meta import Mumi.View
public meta import Mumi.Public
public meta import Lean.Elab.Match
public meta import Lean.Elab.Do.Basic
public meta import Lean.Elab.Tactic.Basic

/-!
# Taking over `match`

Importing this module makes `match` work on the members it has views of.
Nothing else about `match` changes.

`Mumi.View` says why the equation compiler cannot be pointed at such a member
directly, and what a view is.  Two kinds of member have one: an
induction-inductive member, which is a definition over a wrapper, and a member
with a constructor the writer has at the original of a `Prop` copy
(`Mumi.Public.publishOverOriginals`), which the kernel's constructor holds
packed.  This module is the rewrite that puts the view in the way.  An
alternative written against the member,

```lean
def len (c : Ctx) : Nat :=
  match c with
  | .nil      => 0
  | .snoc Γ _ => len Γ + 1
```

is elaborated as if written against the view:

```lean
def len (c : Ctx) : Nat :=
  match c, c.view with
  | _, .nil      => 0
  | _, .snoc Γ _ => len Γ + 1
```

That is a `match` on a genuine inductive.  The member is still a discriminant
and still listed first, so it is generalised before the view is read and the
view's index refines it.

## Patterns inside patterns

A view presents the constructor a member was built by and stops, so a pattern
under one, `.node (.leaf a) t`, is taken apart by a `match` of its own.  The
alternatives are compiled the standard way, one column at a time: the leftmost
column some alternative takes apart through a view is split into one `match`
alternative per constructor named there, each continuing with the alternatives
that fit it -- those naming that constructor, its arguments now columns of their
own, and those with a variable or `_` there -- in their order, so the first
alternative that fits is the one taken.  A column of an ordinary inductive is
split the same way, without a view, when a pattern in it has a viewed
constructor somewhere inside.  What is left once no column needs a view is an
ordinary `match`, on what remains, with the alternatives that remain.

An alternative that fits on no branch is reported as Lean reports it.  One that
fits only on some is not: the `match`es written for a branch are told to expect
alternatives that do not reach them.

## What is not rewritten

An explicit `(motive := ..)` fixes the number of patterns per alternative, which
the rewrite changes, so such a `match` falls through to Lean.

A promoted argument -- one the view carries as a parameter, see `Mumi.View` --
is settled by the discriminant's type, so a pattern cannot constrain it.  Where
the writer named one on a discriminant of the `match` it is bound by a `let` on
the right-hand side, to the index that type supplies; inside another pattern it
can be written only as `_`.

The mechanism is the one `Mumi.Mutual` uses for `mutual`.  A `@[term_elab]`
registered downstream is tried before the builtin one, and
`throwUnsupportedSyntax` hands the term back with any state the override touched
rolled back.  A `do` block's `match` is a `do` element with its own elaborator,
so it gets its own override on the same plan, and the rewritten `match` goes
back to that elaborator, which keeps `return`, `break`, `continue` and mutable
variables working inside an alternative.
-/

public section

open Lean Lean.Elab Lean.Elab.Term Lean.Meta

namespace Mumi

/-- A `match` this module wrote for one branch of another, whose alternatives
need not all be reachable on that branch. -/
syntax (name := branchMatch) "mumi_branch% " term : term

/-- A right-hand side the writer wrote, inside a `mumi_branch%`. -/
syntax (name := writtenRhs) "mumi_written% " term : term

/-- The option Lean reads to report an alternative no input reaches. -/
private meta def ignoreUnusedAlts : Name := `match.ignoreUnusedAlts

@[term_elab branchMatch]
meta def elabBranchMatch : TermElab := fun stx expectedType? =>
  withOptions (·.setBool ignoreUnusedAlts true) (elabTerm stx[1] expectedType?)

@[term_elab writtenRhs]
meta def elabWrittenRhs : TermElab := fun stx expectedType? =>
  withOptions (·.setBool ignoreUnusedAlts false) (elabTerm stx[1] expectedType?)

/-- A right-hand side the writer wrote, under variables this module bound only
to match again, which it is elaborated without. -/
syntax (name := withoutTemps) "mumi_without% " ident* " => " term : term

/-- Elaborate a right-hand side in the context Lean's own `match` would have
given it.  A variable bound for a constructor that is then matched again further
in is stale once it has been: the value it stood for is the pattern now, and
Lean's `match` leaves no such thing behind.  Those nothing else in scope
depends on are left out of the context, which is sound because a term that
does not mention them is a term with them. -/
@[term_elab withoutTemps]
meta def elabWithoutTemps : TermElab := fun stx expectedType? => do
  let expected? ← expectedType?.mapM instantiateMVars
  let mut lctx ← getLCtx
  for id in stx[1].getArgs.reverse do
    let some d := lctx.findFromUserName? id.getId | continue
    let uses (e : Expr) := e.containsFVar d.fvarId
    if expected?.any uses then continue
    let needed := lctx.foldl (init := false) fun acc d' =>
      acc || (d'.fvarId != d.fvarId && (uses d'.type || d'.value?.any uses))
    if needed then continue
    lctx := lctx.erase d.fvarId
  withLCtx lctx (← getLocalInstances) (elabTerm stx[3] expectedType?)

/-- A `match` this module wrote to split a column, with what to say for each
constructor it has no alternative for: one line per constructor, its last name,
the position of the discriminant split, and the alternative the writer would
add, separated by tabs. -/
syntax (name := splitMatch) "mumi_split% " str term : term

/-- The same, in a `do` block. -/
syntax (name := splitDo) "mumi_split% " str doElem : doElem

/-- `s` split at its top-level commas, as a counterexample lists patterns. -/
private meta def splitTop (s : String) : Array String := Id.run do
  let mut out := #[]
  let mut cur := ""
  let mut depth : Int := 0
  for ch in s.toList do
    if ch == '(' || ch == '[' || ch == '⟨' then depth := depth + 1
    if ch == ')' || ch == ']' || ch == '⟩' then depth := depth - 1
    if ch == ',' && depth == 0 then
      out := out.push cur
      cur := ""
    else unless ch == ' ' && cur.isEmpty do
      cur := cur.push ch
  return out.push cur

/-- Whether a pattern as Lean prints it is headed by a constructor called `c`. -/
private meta def headedBy (pat c : String) : Bool :=
  let head := String.ofList ((pat.toList.dropWhile (· == '(')).takeWhile (· != ' '))
  let head := String.ofList (head.toList.reverse.dropWhile (· == ')')).reverse
  head == c || head.endsWith ("." ++ c)

/-- Run `k`; then say what Lean reports missing from the `match` at `ref` as
the alternatives the writer would add, which `info` lists. -/
private meta def explainMissing {m : Type → Type} [Monad m] [MonadLiftT CoreM m] {α}
    (ref : Syntax) (info : String) (k : m α) : m α := do
  let before ← liftM (m := CoreM) do return (← Core.getMessageLog).unreported.size
  let r ← k
  liftM (m := CoreM) do
    let some pos := ref.getPos? | return
    let p := (← getFileMap).toPosition pos
    let entries := (info.splitOn "\n").filterMap fun e =>
      match e.splitOn "\t" with
      | [c, i, line] => some (c, i.toNat!, line)
      | _ => none
    let log ← Core.getMessageLog
    let mut msgs := log.unreported
    for idx in before...msgs.size do
      let msg := msgs[idx]!
      unless msg.pos == p && msg.severity == .error do continue
      if msg.data.hasTag (· == `Mumi.missing) then continue
      let text ← msg.data.toString
      unless text.startsWith "Missing cases:" do continue
      let mut out := #[]
      for l in (text.splitOn "\n").drop 1 do
        let parts := splitTop l
        for (c, i, line) in entries do
          if let some part := parts[i]? then
            if headedBy part c && !out.contains line then out := out.push line
      if out.isEmpty then continue
      let data := MessageData.tagged `Mumi.missing
        m!"Missing cases:\n{"\n".intercalate out.toList}"
      msgs := msgs.set idx { msg with data }
    -- the splits that found them each said so: said once, as Lean would
    let mut kept := #[]
    let mut first? : Option Nat := none
    let mut lines := #[]
    for msg in msgs.toArray, idx in *...msgs.size do
      if idx >= before && msg.pos == p && msg.data.hasTag (· == `Mumi.missing) then
        for l in ((← msg.data.toString).splitOn "\n").drop 1 do
          unless lines.contains l do lines := lines.push l
        if first?.isSome then continue
        first? := some kept.size
      kept := kept.push msg
    if let some i := first? then
      let data := MessageData.tagged `Mumi.missing
        m!"Missing cases:\n{"\n".intercalate lines.toList}"
      kept := kept.modify i ({ · with data })
    Core.setMessageLog { log with unreported := kept.toPArray' }
  return r

@[term_elab splitMatch]
meta def elabSplitMatch : TermElab := fun stx expectedType? => do
  let some info := stx[1].isStrLit? | throwUnsupportedSyntax
  explainMissing stx[2] info (elabTerm stx[2] expectedType?)

@[doElem_elab splitDo]
meta def elabSplitDo : Lean.Elab.Do.DoElab := fun stx cont => do
  let some info := stx.raw[1].isStrLit? | throwUnsupportedSyntax
  explainMissing stx.raw[2] info (Lean.Elab.Do.elabDoElem ⟨stx.raw[2]⟩ cont)

/-- A pattern, as far as the compiler takes it apart. -/
private inductive Pat where
  /-- `_`, or a variable, which is given what is in the column. -/
  | wild (name? : Option Syntax)
  /-- A constructor of the column's type at its written arguments, under the
  name in `x@p` if it was written so. -/
  | ctor (name? : Option Syntax) (c : Name) (args : Array Syntax)
  /-- Anything else, which is left to Lean. -/
  | other

/-- What a column's type is, as far as splitting it goes. -/
private structure Head where
  /-- The inductive, or the member where it has a view. -/
  ind : Name
  /-- What the type was called on the way to `ind`, for `.c` to be read against. -/
  names : Array Name
  /-- The view, for a member matched through one. -/
  view? : Option Name
  /-- The constructors, under the writer's names. -/
  ctors : Array Name
  levels : List Level
  /-- What the type is applied to. -/
  args : Array Expr
  /-- How many of those the inductive, or the view, takes as parameters. -/
  numParams : Nat
  /-- How many written arguments of a constructor the view carries as
  parameters instead. -/
  promoted : Nat := 0

/-- How many arguments a constant is written with. -/
private meta def explicitArity (n : Name) : MetaM Nat := do
  forallTelescope (← getConstInfo n).type fun xs _ =>
    xs.foldlM (init := 0) fun acc x =>
      return acc + (if (← x.fvarId!.getBinderInfo).isExplicit then 1 else 0)

/-- What `ty` is headed by: a member with a view, or failing that an inductive
reached by unfolding. -/
private meta def headOf? (ty? : Option Expr) : MetaM (Option Head) := do
  let some ty := ty? | return none
  let mut ty ← instantiateMVars ty
  let mut names := #[]
  for _ in *...32 do
    ty ← whnfCore ty
    let .const c us := ty.getAppFn | return none
    names := names.push c
    let env ← getEnv
    -- the kernel's `X._ind` is the writer's `X`
    let mem := match c with
      | .str p "_ind" => if (viewedMembers env).contains p then p else c
      | _ => c
    if let some (view, _) := viewOf? env mem then
      let vi ← getConstInfoInduct view
      let ctors := vi.ctors.toArray.map (·.replacePrefix view mem)
      let promoted ← match ctors[0]?, vi.ctors[0]? with
        | some c, some vc => pure ((← explicitArity c) - (← explicitArity vc))
        | _, _ => pure 0
      return some
        { ind := mem, names := names.push mem, view? := some view, ctors := ctors,
          levels := us, args := ty.getAppArgs, numParams := vi.numParams, promoted }
    if let some (.inductInfo ii) := env.find? c then
      return some
        { ind := c, names, view? := none, ctors := ii.ctors.toArray,
          levels := us, args := ty.getAppArgs, numParams := ii.numParams }
    let some ty' ← unfoldDefinition? ty | return none
    ty := ty'
  return none

/-- The constructor of `h` a pattern's head names, if it names one. -/
private meta def ctorNamed? (h : Head) (fn : Syntax) : TermElabM (Option Name) := do
  let env ← getEnv
  let ctorFor (n : Name) : Option Name :=
    h.ctors.find? fun c => c == n || publicName? env c == some n
  if fn.getKind == ``Lean.Parser.Term.dotIdent then
    let id := fn[1].getId.eraseMacroScopes
    return h.names.findSome? fun a => ctorFor (a ++ id)
  if fn.isIdent then
    for n in (← try resolveGlobalConst fn catch _ => pure []) do
      if let some c := ctorFor n then return some c
  return none

/-- Whether an identifier in a pattern is a constant rather than a variable. -/
private meta def isPatternConst (id : Syntax) : TermElabM Bool := do
  let env ← getEnv
  let cs ← try resolveGlobalConst id catch _ => pure []
  return cs.any fun c => (env.find? c).any (·.isCtor) || hasMatchPatternAttribute env c

/-- Run `k` on the types of what a constructor of `h` is written with past what
the view carries, in the context of their telescope. -/
private meta def withFields {m : Type → Type} [Monad m] [MonadControlT MetaM m]
    [MonadLiftT MetaM m] {α} (h : Head) (c : Name) (k : Array Expr → m α) : m α := do
  let src := match h.view? with
    | some v => c.replacePrefix h.ind v
    | none => c
  let ty ← liftM (m := MetaM) do
    instantiateForall ((← getConstInfo src).instantiateTypeLevelParams h.levels)
      (h.args.extract 0 h.numParams)
  forallTelescope ty fun xs _ => do
    let tys ← liftM (m := MetaM) <| xs.filterMapM fun x => do
      unless (← x.fvarId!.getBinderInfo).isExplicit do return none
      return some (← inferType x)
    k tys

/-- `p`, parentheses and ascriptions off. -/
private meta partial def unwrap (p : Syntax) : Syntax :=
  if p.getKind == ``Lean.Parser.Term.paren || p.getKind == ``Lean.Parser.Term.typeAscription then
    unwrap p[1]
  else p

/-- A `sepBy1` node, which is what `match` holds both its discriminants and its
patterns in. -/
private meta def sepNode (sep : String) (elems : Array Syntax) : Syntax :=
  mkNullNode <| Id.run do
    let mut out := #[]
    for e in elems do
      if !out.isEmpty then out := out.push (mkAtom sep)
      out := out.push e
    return out

/-- What a pattern is, in a column whose type is `h`. -/
private meta partial def classify (h : Head) (p : Syntax) : TermElabM Pat := do
  let p := unwrap p
  let k := p.getKind
  if k == ``Lean.Parser.Term.hole then return .wild none
  if k == ``Lean.Parser.Term.namedPattern then
    unless p[2].isNone do return .other
    return match ← classify h p[3] with
      | .ctor _ c args => .ctor p[0] c args
      | .wild none => .wild p[0]
      | _ => .other
  let written (c : Name) : TermElabM Nat := do
    return h.promoted + (← withFields h c fun tys => pure tys.size)
  if k == ``Lean.Parser.Term.anonymousCtor then
    let #[c] := h.ctors | return .other
    let n ← written c
    let args := p[1].getSepArgs
    if n == 0 || args.size < n then return .other
    -- the last field takes what is left over, as anonymous constructor notation does
    let args := if args.size == n then args else
      (args.extract 0 (n - 1)).push (p.setArg 1 (sepNode ", " (args.extract (n - 1) args.size)))
    return .ctor none c args
  let (fn, args) := if k == ``Lean.Parser.Term.app then (p[0], p[1].getArgs) else (p, #[])
  if let some c ← ctorNamed? h fn then
    if args.any (·.getKind == ``Lean.Parser.Term.namedArgument) then return .other
    let n ← written c
    let holes (i : Nat) : Array Syntax := .replicate i (mkHole p)
    let args := match args.findIdx? (·.getKind == ``Lean.Parser.Term.ellipsis) with
      | some i => args.extract 0 i ++ holes (n + 1 - args.size) ++ args.extract (i + 1) args.size
      | none => args
    return .ctor none c args
  if p.isIdent then
    return if ← isPatternConst p then .other else .wild p
  -- notation for a constructor, `a :: as`, is read as what it stands for
  if let some p' ← (try liftMacroM (expandMacro? p) catch _ => pure none) then
    if let r@(.ctor ..) ← classify h p' then return r
  return .other

/-- Whether a pattern in a column of type `ty?` takes something apart through a
view, at its head or anywhere under it. -/
private meta partial def needs (ty? : Option Expr) (p : Syntax) : TermElabM Bool := do
  let some h ← headOf? ty? | return false
  let .ctor _ c args ← classify h p | return false
  if h.view?.isSome then return true
  withFields h c fun tys => do
    for a in args, t in tys do
      if ← needs (some t) a then return true
    return false

/-- Whether a pattern matches whatever it is given. -/
private meta partial def irrefutable (p : Syntax) : TermElabM Bool := do
  let p := unwrap p
  if p.getKind == ``Lean.Parser.Term.hole then return true
  if p.getKind == ``Lean.Parser.Term.namedPattern then
    return p[2].isNone && (← irrefutable p[3])
  if p.isIdent then return !(← isPatternConst p)
  return false

/-- The `matchDiscr` for a term, with the `h :` it carries if any. -/
private meta def mkDiscr (name : Syntax) (t : Syntax) : Syntax :=
  Syntax.node .none ``Lean.Parser.Term.matchDiscr #[name, t]

/-- The bindings in front of a term. -/
private meta def termLets (lets : Array (Ident × Term)) (rhs : Syntax) : TermElabM Syntax := do
  let mut r : Term := ⟨rhs⟩
  for (x, v) in lets.reverse do
    r ← `(let $x := $v; $r)
  return r.raw

/-- The bindings in front of a `do` sequence, which keeps its elements in a
different place depending on whether it was written with braces. -/
private meta def doLets (lets : Array (Ident × Term)) (seq : Syntax) : TermElabM Syntax := do
  if lets.isEmpty then return seq
  let items ← lets.mapM fun (x, v) => do
    return mkNode ``Lean.Parser.Term.doSeqItem #[(← `(doElem| let $x := $v)).raw, mkNullNode]
  let i := if seq.getKind == ``Lean.Parser.Term.doSeqBracketed then 1 else 0
  return seq.setArg i (mkNullNode (items ++ seq[i].getArgs))

/-- Something being matched: a discriminant as written, or a part of one bound
by a `match` written on the way. -/
private structure Col where
  term : Syntax
  /-- Its type, where it is known. -/
  ty? : Option Expr
  /-- The `h :` the writer gave it, until the first `match` is written. -/
  hName : Syntax := mkNullNode
  /-- Whether it is a discriminant as written, whose type is in scope. -/
  written : Bool := false
  /-- What stands for it in the patterns a missing alternative is described by. -/
  ph : String := ""

private meta instance : Inhabited Col := ⟨{ term := .missing, ty? := none }⟩

/-- An alternative, or one of its pattern lists, as far as it has been taken
apart. -/
private structure Row where
  pats : Array Syntax
  rhs : Syntax
  /-- Promoted arguments named in it, given by definition. -/
  lets : Array (Ident × Term) := #[]
  /-- Which written alternative it comes from. -/
  alt : Nat
  /-- Which pattern list of which alternative it is. -/
  id : Nat

/-- The `match` being compiled, which every `match` written for it is built from. -/
private structure Gen where
  stx : Syntax
  isDo : Bool
  /-- An alternative of it, to build the others from. -/
  alt : Syntax
  /-- Whether the writer turned the report of unused alternatives off. -/
  ignore : Bool

/-- A `match` like the one being compiled, on `discrs`. -/
private meta def Gen.mkMatch (g : Gen) (discrs : Array Syntax)
    (alts : Array (Array Syntax × Syntax)) : Syntax :=
  let alts := alts.map fun (pats, rhs) =>
    g.alt.setArg 1 (sepNode " | " #[sepNode ", " pats]) |>.setArg 3 rhs
  let (d, a) := if g.isDo then (4, 6) else (3, 5)
  g.stx.setArg d (sepNode ", " discrs) |>.setArg a (g.stx[a].setArg 0 (mkNullNode alts))

/-- A `match` this module wrote, as the right-hand side of another. -/
private meta def Gen.asRhs (g : Gen) (m : Syntax) : Syntax :=
  if g.isDo then
    mkNode ``Lean.Parser.Term.doSeqIndent
      #[mkNullNode #[mkNode ``Lean.Parser.Term.doSeqItem #[m, mkNullNode]]]
  else m

/-- What compiling keeps track of. -/
private structure CState where
  /-- Whether each written alternative has been reached. -/
  used : Array Bool
  /-- The next placeholder in a described pattern. -/
  next : Nat
  /-- How many times each row's right-hand side has been written out. -/
  emitted : Array Nat
  /-- Named holes written as right-hand sides on more than one branch: the name
  written, and the one each further copy got. -/
  copies : Array (Syntax × Syntax) := #[]
  /-- The variables bound on the way to a right-hand side that the writer did
  not name: what is under a constructor matched again further in. -/
  temps : Array Syntax := #[]

private abbrev CompileM := StateRefT CState TermElabM

/-- A row's right-hand side, with its bindings.  A row that fits on several
branches is written out on each; where it is a named hole, each copy is a goal
of its own under a name of its own. -/
private meta def Gen.rhsOf (g : Gen) (r : Row) (inBranch : Bool) : CompileM Syntax := do
  let n := (← get).emitted[r.id]!
  modify fun s => { s with emitted := s.emitted.modify r.id (· + 1) }
  let mut body := r.rhs
  if n > 0 && body.isOfKind ``Lean.Parser.Term.syntheticHole && body[1].isIdent then
    let id := body[1]
    let id' := mkIdentFrom id (← mkFreshUserName id.getId.eraseMacroScopes)
    modify fun s => { s with copies := s.copies.push (id, id') }
    body := body.setArg 1 id'
  if g.isDo then return ← doLets r.lets body
  let mut rhs ← termLets r.lets body
  if inBranch then rhs := mkNode ``writtenRhs #[mkAtom "mumi_written%", rhs]
  let temps := (← get).temps
  unless temps.isEmpty do
    rhs := mkNode ``withoutTemps #[mkAtom "mumi_without%", mkNullNode temps, mkAtom "=>", rhs]
  return rhs

/-- The rows up to the first that matches whatever it is given, which leaves
nothing for those after it. -/
private meta def prune (rows : Array Row) : TermElabM (Array Row) := do
  let mut live := #[]
  for r in rows do
    live := live.push r
    if ← r.pats.allM irrefutable then break
  return live

/-- A fresh placeholder. -/
private meta def freshPh : CompileM String :=
  modifyGet fun s => (s!"‹{s.next}›", { s with next := s.next + 1 })

/-- The placeholders in a described pattern, as `_`. -/
private meta def scrub (s : String) : String := Id.run do
  let mut out := ""
  let mut inPh := false
  for ch in s.toList do
    if ch == '‹' then
      inPh := true
      out := out.push '_'
    else if ch == '›' then inPh := false
    else unless inPh do out := out.push ch
  return out

/-- A constructor applied to described arguments, as Lean prints a pattern. -/
private meta def ctorText (c : Name) (args : Array String) : CoreM String := do
  let ns ← getCurrNamespace
  let c := if ns.isPrefixOf c && ns != c then c.replacePrefix ns .anonymous else c
  return if args.isEmpty then toString c else s!"({" ".intercalate (toString c :: args.toList)})"

/-- The promoted arguments of a constructor pattern taken off, the ones named
given by definition. -/
private meta def takePromoted (h : Head) (col : Col) (c : Name) (args : Array Syntax) :
    TermElabM (Array Syntax × Array (Ident × Term)) := do
  let mut lets := #[]
  for i in *...h.promoted do
    let some a := args[i]? | break
    let a := unwrap a
    if a.isIdent && col.written then
      let some v := h.args[h.numParams - h.promoted + i]? | throwErrorAt a "unexpected argument"
      lets := lets.push (⟨a⟩, ← exprToSyntax v)
    else unless a.getKind == ``Lean.Parser.Term.hole do
      throwErrorAt a "This argument of `{c}` is settled by the type of what is being \
        matched rather than by the pattern, so it can be written only as `_`{
        if col.written then ", or as a name to have it under" else " here"}."
  return (args.extract h.promoted args.size, lets)

/-- The rows that remain, as a `match`, or as the right-hand side of the first
when nothing is left to match. -/
private meta partial def compile (g : Gen) (cols : Array Col) (rows : Array Row)
    (shape : Array String) : CompileM Syntax := do
  for j in *...cols.size do
    for r in rows do
      if ← needs cols[j]!.ty? r.pats[j]! then
        return ← split j
  leaf
where
  /-- No column needs a view: what remains is Lean's. -/
  leaf : CompileM Syntax := do
    let live ← prune rows
    for r in live do modify fun s => { s with used := s.used.set! r.alt true }
    let keep := (Array.range cols.size).filter fun j =>
      !cols[j]!.hName.isNone ||
        live.any fun r => (unwrap r.pats[j]!).getKind != ``Lean.Parser.Term.hole
    let some first := live[0]? | throwError "no alternative is left to match"
    if keep.isEmpty then return ← g.rhsOf first false
    -- the rows after the first are those that fit on some branch, perhaps not this one
    let inBranch := live.size > 1 && !g.ignore && !g.isDo
    let alts ← live.mapM fun r => return (keep.map (r.pats[·]!), ← g.rhsOf r inBranch)
    let m := g.mkMatch (keep.map fun j => mkDiscr cols[j]!.hName cols[j]!.term) alts
    return g.asRhs <| if inBranch then mkNode ``branchMatch #[mkAtom "mumi_branch%", m] else m
  /-- Split column `j` by the constructor at its head. -/
  split (j : Nat) : CompileM Syntax := do
    let col := cols[j]!
    let some h ← headOf? col.ty? | throwError "no type to split `{col.term}` by"
    let pats ← rows.mapM fun r => classify h r.pats[j]!
    for r in rows, p in pats do
      if let .other := p then
        throwErrorAt r.pats[j]! "Another alternative takes apart a constructor of \
          `{h.ind}` here, so only a constructor, a variable or `_` can be written in \
          this position."
    let hole := (mkHole col.term).raw
    -- the columns some row still looks at are passed on, so that whatever
    -- depends on the one being split is generalised with it
    let live := (Array.range cols.size).filter fun i =>
      i == j || !cols[i]!.hName.isNone ||
        rows.any fun r => (unwrap r.pats[i]!).getKind != ``Lean.Parser.Term.hole
    -- the view goes in right after what it is the view of, so that it is
    -- generalised before the type that refines it is read
    let viewAt := (live.idxOf? j).getD 0 + 1
    let withView (xs : Array Syntax) (v : Syntax) : Array Syntax :=
      (xs.extract 0 viewAt).push v ++ xs.extract viewAt xs.size
    let mut discrs := live.map fun i => mkDiscr cols[i]!.hName cols[i]!.term
    if h.view?.isSome then
      discrs := withView discrs <| mkDiscr mkNullNode <|
        (Syntax.mkApp (mkCIdentFrom col.term (viewFnName h.ind)) #[⟨col.term⟩]).raw
    let next := cols.map ({ · with hName := mkNullNode })
    let named := h.ctors.filter fun c => pats.any fun
      | .ctor _ c' _ => c' == c
      | _ => false
    let mut alts := #[]
    for c in named do
      alts := alts.push <| ← withFields h c fun tys => do
        let mut sub := #[]
        for r in rows, p in pats do
          match p with
          | .wild n? =>
            sub := sub.push { r with pats := r.pats.set! j (n?.getD hole) ++ tys.map fun _ => hole }
          | .ctor n? c' args =>
            unless c' == c do continue
            let (args, lets) ← if h.view?.isSome then takePromoted h col c args
              else pure (args, #[])
            unless args.size == tys.size do
              throwErrorAt r.pats[j]! "`{c}` is written with {h.promoted + tys.size}                 arguments in a pattern, but {h.promoted + args.size} were given."
            sub := sub.push
              { r with pats := r.pats.set! j (n?.getD hole) ++ args, lets := r.lets ++ lets }
          | .other => pure ()
        let subCols ← tys.mapM fun t => return ({ term := .missing, ty? := some t, ph := ← freshPh } : Col)
        let here ← ctorText c ((Array.replicate h.promoted "_") ++ subCols.map (·.ph))
        let (binders, cols', rows') ← bind (next ++ subCols) (← prune sub) (live.filter (· != j))
          (Array.range' cols.size tys.size)
        let ys := (Array.range' cols.size tys.size).map (binders[·]!)
        let src := match h.view? with
          | some v => c.replacePrefix h.ind v
          | none => c
        -- a view's constructor is written `.c`, so that its parameters are read
        -- off the type it is expected at, the promoted proofs among them
        let head : Syntax := if h.view?.isSome then
            mkNode ``Lean.Parser.Term.dotIdent
              #[mkAtomFrom col.term ".", mkIdentFrom col.term (.mkSimple src.getString!)]
          else (mkCIdentFrom col.term src).raw
        let ctorPat := (Syntax.mkApp (⟨head⟩ : Term) (ys.map (⟨·⟩))).raw
        let rhs ← compile g cols' rows' (shape.map (·.replace col.ph here))
        let pats := live.map fun i => if i == j then (if h.view?.isSome then hole else ctorPat)
          else binders[i]!
        return (if h.view?.isSome then withView pats ctorPat else pats, rhs)
    -- the constructors no alternative names go to those that take anything
    let mut missing := #[]
    if named.size < h.ctors.size then
      let dflt := (rows.zip pats).filterMap fun
        | (r, .wild n?) => some { r with pats := r.pats.set! j (n?.getD hole) }
        | _ => none
      if dflt.isEmpty then
        -- and where there are none, Lean reports them in terms of this `match`,
        -- which the writer never wrote: what they would write is said instead
        let pos := (live.idxOf? j).getD 0 + if h.view?.isSome then 1 else 0
        for c in h.ctors do
          if named.contains c then continue
          let n ← withFields h c fun tys => pure tys.size
          let here ← ctorText c (.replicate (h.promoted + n) "_")
          let line := scrub (", ".intercalate (shape.map (·.replace col.ph here)).toList)
          let short := match c with
            | .str _ s => s
            | _ => toString c
          missing := missing.push s!"{short}\t{pos}\t{line}"
      else
        let (binders, cols', rows') ← bind next (← prune dflt) (live.filter (· != j)) #[]
        let rhs ← compile g cols' rows' shape
        let pats := live.map fun i => if i == j then hole else binders[i]!
        alts := alts.push (if h.view?.isSome then withView pats hole else pats, rhs)
    let m := g.mkMatch discrs alts
    if missing.isEmpty then return g.asRhs m
    let info := Syntax.mkStrLit ("\n".intercalate missing.toList)
    return g.asRhs <| mkNode (if g.isDo then ``splitDo else ``splitMatch)
      #[mkAtom "mumi_split%", info, m]
  /-- What a branch binds the columns `passed` and `fresh` to: the variable every
  row there names, which is then the column, or else `_` for a variable already
  in scope and a fresh one for anything else. -/
  bind (cols : Array Col) (rows : Array Row) (passed fresh : Array Nat) :
      CompileM (Array Syntax × Array Col × Array Row) := do
    let mut binders := Array.replicate cols.size (mkHole cols[0]!.term).raw
    let mut cols := cols
    let mut rows := rows
    for i in passed ++ fresh do
      let c := cols[i]!
      -- what no row looks at is left for Lean to name
      if rows.all fun r => (unwrap r.pats[i]!).getKind == ``Lean.Parser.Term.hole then
        continue
      if let some v ← sameVar? rows i then
        binders := binders.set! i v
        cols := cols.set! i { c with term := v }
        rows := rows.map fun r => { r with pats := r.pats.set! i (mkHole v).raw }
      else if fresh.contains i || !c.term.isIdent then
        let y := (← withFreshMacroScope `(x)).raw
        modify fun s => { s with temps := s.temps.push y }
        binders := binders.set! i y
        cols := cols.set! i { c with term := y }
    return (binders, cols, rows)
  /-- The variable every row names at column `i`, if they all name the same. -/
  sameVar? (rows : Array Row) (i : Nat) : TermElabM (Option Syntax) := do
    let some r := rows[0]? | return none
    let v := r.pats[i]!
    unless v.isIdent && !(← isPatternConst v) do return none
    return if rows.all (fun r => r.pats[i]!.isIdent && r.pats[i]!.getId == v.getId)
      then some v else none

/-- The type of a discriminant, where it can be read with nothing left to solve.
Read under a sandbox that is thrown away; the elaboration that found it happens
again in earnest only if the rewrite is going to happen at all. -/
private meta def discrType? (d : Syntax) : TermElabM (Option Expr) :=
  withoutModifyingState do
    try
      let e ← withoutErrToSorry <| withSynthesize <| elabTerm d none
      let ty ← instantiateMVars (← inferType e)
      return if ty.hasMVar then none else some ty
    catch _ =>
      return none

/-- Whether some identifier in some alternative's patterns is called what a
viewed constructor is, which is the cheap look that comes before anything is
elaborated. -/
private meta def namesViewed (viewed : NameSet) (alts : Array Syntax) : Bool :=
  alts.any fun alt => (alt[1].find? fun s => s.isIdent &&
    match s.getId.eraseMacroScopes with
    | .str _ c => viewed.contains (.mkSimple c)
    | _ => false).isSome

/-- A `match`, or a `do` block's, compiled to `match`es Lean can take, if some
pattern in it needs a view. -/
private meta def compileMatch (stx : Syntax) (isDo : Bool) :
    TermElabM (Option (Syntax × CState)) := do
  let viewed := viewedCtors (← getEnv)
  if viewed.isEmpty then return none
  let (mI, dI, aI) := if isDo then (3, 4, 6) else (2, 3, 5)
  unless stx[mI].isNone do return none
  let alts := stx[aI][0].getArgs
  unless namesViewed viewed alts do return none
  let discrs := stx[dI].getSepArgs
  let mut cols := #[]
  for d in discrs, i in *...discrs.size do
    cols := cols.push
      { term := d[1], ty? := ← discrType? d[1], hName := d[0], written := true, ph := s!"‹{i}›" }
  let mut rows := #[]
  for alt in alts, i in *...alts.size do
    for pl in alt[1].getSepArgs do
      let pats := pl.getSepArgs
      if pats.size != cols.size then return none
      rows := rows.push { pats, rhs := alt[3], alt := i, id := rows.size }
  unless ← rows.anyM fun r => (r.pats.zip cols).anyM fun (p, c) => needs c.ty? p do
    return none
  let some alt := alts[0]? | return none
  let ignore := (← getOptions).getBool ignoreUnusedAlts false
  let g : Gen := { stx, isDo, alt, ignore }
  let (out, st) ← (compile g cols rows (cols.map (·.ph))).run
    { used := .replicate alts.size false, next := cols.size, emitted := .replicate rows.size 0 }
  unless ignore do
    for alt in alts, u in st.used do
      unless u do logErrorAt alt[1] (mkRedundantAlternativeMsg none none)
  -- a `do` block's comes back as the sequence it would be a right-hand side as
  return some (if isDo then out[0][0][0] else out, st)

/-- Elaborate a `match` on a member by elaborating `match`es on its view. -/
@[term_elab Lean.Parser.Term.match]
meta def elabMatchThroughView : TermElab := fun stx expectedType? => do
  let some (stx, _) ← compileMatch stx false | throwUnsupportedSyntax
  trace[Mumi.view] "matching through a view:{indentD m!"{stx}"}"
  elabTerm stx expectedType?

/-- The same, for the `match` of a `do` block, which has its own elaborator. -/
@[doElem_elab Lean.Parser.Term.doMatch]
meta def elabDoMatchThroughView : Lean.Elab.Do.DoElab := fun stx cont => do
  let some (stx, _) ← compileMatch stx.raw true | throwUnsupportedSyntax
  trace[Mumi.view] "matching through a view in a `do` block:{indentD m!"{stx}"}"
  Lean.Elab.Do.elabDoElem ⟨stx⟩ cont

/-- The same, for the `match` tactic.  Lean reads one as a `match` whose
right-hand sides are goals, each alternative's tactics then run on its own; a
row that fits on several branches is a goal on each, so its tactics are run on
each. -/
@[tactic Lean.Parser.Tactic.match]
meta def evalMatchThroughView : Lean.Elab.Tactic.Tactic := fun stx => do
  if (viewedCtors (← getEnv)).isEmpty then throwUnsupportedSyntax
  let tag ← Lean.Elab.Tactic.getMainTag
  let alts := stx[5][0].getArgs
  let mut newAlts := #[]
  let mut cases := #[]
  let mut nextIdx := 1
  for alt in alts do
    let alt := alt.setKind ``Lean.Parser.Term.matchAlt
    let rhs := alt[3]
    -- as Lean has it: a goal per pattern list, since each binds its own variables
    for patGroup in alt[1].getSepArgs do
      let mut alt := alt.setArg 1 (mkNullNode #[patGroup])
      if rhs.isOfKind ``Lean.Parser.Term.syntheticHole then
        pure ()
      else if rhs.isOfKind ``Lean.Parser.Term.hole then
        let tag' := if alts.size > 1 then tag ++ (`match).appendIndexAfter nextIdx else tag
        nextIdx := nextIdx + 1
        alt := alt.setArg 3 (← `(?$(mkIdentFrom rhs tag'):ident))
      else
        let hole ← withFreshMacroScope `(?rhs)
        cases := cases.push (hole.raw[1], alt[0], alt[2], rhs)
        alt := alt.setArg 3 hole
      newAlts := newAlts.push alt
  let term := stx.setKind ``Lean.Parser.Term.«match»
    |>.setArg 5 (mkNode ``Lean.Parser.Term.matchAlts #[mkNullNode newAlts])
  let some (compiled, st) ← compileMatch term false | throwUnsupportedSyntax
  let mut tacs := #[← `(tactic| refine no_implicit_lambda% $(⟨compiled⟩))]
  for (id, _, arrow, seq) in cases do
    let ids := #[id] ++ st.copies.filterMap fun (o, n) => if o.getId == id.getId then some n else none
    let seq : TSyntax ``Lean.Parser.Tactic.tacticSeq := ⟨seq⟩
    for id in ids do
      tacs := tacs.push <| ← `(tactic| case $(⟨id⟩):ident =>%$arrow $seq:tacticSeq)
  let stxNew := mkNullNode tacs
  withMacroExpansion stx stxNew <| Lean.Elab.Tactic.evalTactic stxNew

end Mumi
