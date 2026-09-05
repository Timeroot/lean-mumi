/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public meta import Mumi.View
public meta import Lean.Elab.Match

/-!
# Taking over `match`

Importing this module makes `match` work on the members of an
induction-inductive block.  Nothing else about `match` changes.

`Mumi.View` explains why the equation compiler cannot be pointed at a member
directly and what a view is.  This module is the rewrite that puts one in the
way: an alternative written against the member

```lean
def len (c : Ctx) : Nat :=
  match c with
  | .nil      => 0
  | .snoc Γ _ => len Γ + 1
```

is elaborated as if it had been written against the view,

```lean
def len (c : Ctx) : Nat :=
  match c, c.view with
  | _, .nil      => 0
  | _, .snoc Γ _ => len Γ + 1
```

which is a `match` on a genuine inductive and goes through as it stands.  The
member is still a discriminant, and still listed first, so it is generalised
before the view is looked at and the view's index refines it: each alternative
sees `c` as the constructor it matched, exactly as it would have.

The mechanism is the one `Mumi.Mutual` uses for `mutual`.  A `@[term_elab]`
registered downstream is tried before the builtin one, and
`throwUnsupportedSyntax` hands the term back with any state the override
touched rolled back.  So this is a filter, and it is a narrow one: a file with
no member that has a view never gets past the first line, and a `match` whose
alternatives name no constructor of such a member never gets past the third.

## What is not rewritten

An explicit `(motive := ..)` fixes the number of alternatives' patterns, which
the rewrite changes, so a `match` that has one falls through to Lean, which
says what it always said.

Two shapes are rewritten as far as they go and then reported here, because
Lean, asked about them, would answer in terms of a view the writer never
mentioned.  One is a constructor written inside another pattern: a view
presents the constructor a member was built by and stops there, so what is
under one is out of its reach and has to be reached by a `match` of its own.

The other is a promoted argument -- one the view carries as a parameter rather
than as a field, see `Mumi.View`.  It is settled by the discriminant's type, so
the pattern cannot constrain it; where the writer merely named one it is bound
by a `let` on the right-hand side instead, to the index that type supplies.
-/

public section

open Lean Lean.Elab Lean.Elab.Term Lean.Meta

namespace Mumi

/-- A pattern's head and the arguments it is applied to. -/
private meta def patHead (p : Syntax) : Syntax × Array Syntax :=
  if p.getKind == ``Lean.Parser.Term.app then (p[0], p[1].getArgs) else (p, #[])

/--
The constructor of `mem` a pattern names, and the arguments it was given.

`none` covers everything that is not one, which is most of what can be written:
a variable, a hole, a literal, a constructor of some other type.  An identifier
that does not resolve is a pattern variable and is one of those.
-/
private meta def ctorOf? (mem : Name) (ctors : NameSet) (p : Syntax) :
    TermElabM (Option (Name × Array Syntax)) := do
  let (fn, args) := patHead p
  if fn.getKind == ``Lean.Parser.Term.dotIdent then
    let some id := fn.find? (·.isIdent) | return none
    let c := mem ++ id.getId.eraseMacroScopes
    return if ctors.contains c then some (c, args) else none
  if fn.isIdent then
    for c in (← try resolveGlobalConst fn catch _ => pure []) do
      if ctors.contains c then return some (c, args)
  return none

/--
Whether a pattern is headed by a name some viewed constructor goes by.

This is the whole of what the rewrite costs a `match` it has no business with:
the alternatives are read as they were written, before any discriminant has
been elaborated or any name resolved.  A name that only looks like one of ours
gets a little further and then finds no member.
-/
private meta def headsAtViewed (viewed : NameSet) (p : Syntax) : Bool :=
  let fn := (patHead p).1
  let nm :=
    if fn.getKind == ``Lean.Parser.Term.dotIdent then (fn.find? (·.isIdent)).map (·.getId)
    else if fn.isIdent then some fn.getId
    else none
  match nm.map Name.eraseMacroScopes with
  | some (.str _ s) => viewed.contains (.mkSimple s)
  | _ => false

/-- How many arguments a constructor is written with. -/
private meta def explicitArity (n : Name) : MetaM Nat := do
  forallTelescope (← getConstInfo n).type fun xs _ =>
    xs.foldlM (init := 0) fun acc x =>
      return acc + (if (← x.fvarId!.getBinderInfo).isExplicit then 1 else 0)

/-- What each of a constructor's written arguments has for the head of its type,
which is `Name.anonymous` where that is not a constant. -/
private meta def explicitFieldHeads (n : Name) : MetaM (Array Name) := do
  forallTelescope (← getConstInfo n).type fun xs _ =>
    xs.filterMapM fun x => do
      unless (← x.fvarId!.getBinderInfo).isExplicit do return none
      let .const h _ := (← whnfR (← inferType x)).getAppFn | return some Name.anonymous
      return some h

/-- What the rewrite needs to know about one discriminant it is going through. -/
private structure Through where
  /-- The member the discriminant is an element of. -/
  mem : Name
  /-- Its constructors, under the names the writer knows them by. -/
  ctors : NameSet
  /-- The view. -/
  view : Name
  /-- The number of leading fields the view carries as parameters instead. -/
  promoted : Nat
  /-- What those fields are, read off the discriminant's own type.  Empty where
  no alternative gave one a name and so nothing needs to know. -/
  args : Array Term
  /-- The discriminant's term, which the view is applied to as well. -/
  discr : Term

/-- The `matchDiscr` for a term, keeping whatever `h :` the original carried. -/
private meta def mkDiscr (name : Syntax) (t : Term) : Syntax :=
  Syntax.node .none ``Lean.Parser.Term.matchDiscr #[name, t.raw]

/--
A `.c`, positioned at `src`.

The view's constructor is named this way rather than outright because a pattern
that spells a constructor out in full is elaborated without the expected type in
hand, and a view whose parameters are only there to be read off that type is
then left with them unsolved.  Dot notation asks for the type first, so the
parameters are known before the constructor is looked at.
-/
private meta def mkDotIdent (src : Syntax) (c : Name) : Term :=
  ⟨Syntax.node (.fromRef src) ``Lean.Parser.Term.dotIdent
    #[mkAtomFrom src ".", mkIdentFrom src c]⟩

/-- A `sepBy1` node, which is what `match` holds both its discriminants and its
patterns in. -/
private meta def sepNode (sep : String) (elems : Array Syntax) : Syntax :=
  mkNullNode <| Id.run do
    let mut out := #[]
    for e in elems do
      if !out.isEmpty then out := out.push (mkAtom sep)
      out := out.push e
    return out

/--
The member a discriminant's type is at, if it has a view.

Read under a sandbox that is thrown away: what comes out is a name, and the
elaboration that found it happens again in earnest only if the rewrite is going
to happen at all.
-/
private meta def memberOf? (d : Syntax) : TermElabM (Option Name) :=
  withoutModifyingState do
    try
      let e ← withoutErrToSorry <| elabTerm d[1] none
      let ty ← whnfR (← instantiateMVars (← inferType e))
      let .const mem _ := ty.getAppFn | return none
      return if (viewedMembers (← getEnv)).contains mem then some mem else none
    catch _ =>
      return none

/--
Elaborate a `match` on a member by elaborating the same `match` on its view.

Steps aside -- `throwUnsupportedSyntax`, which hands the term to Lean's own
elaborator with nothing changed -- wherever the rewrite does not apply.
-/
@[term_elab Lean.Parser.Term.match]
meta def elabMatchThroughView : TermElab := fun stx expectedType? => do
  -- the cheap look first: unless some alternative is headed by a name a viewed
  -- constructor goes by, this is a `match` on something else and the
  -- discriminants are not worth elaborating to find that out
  let viewed := viewedCtors (← getEnv)
  if viewed.isEmpty then throwUnsupportedSyntax
  unless stx[2].isNone do throwUnsupportedSyntax
  let discrs := stx[3].getSepArgs
  let alts := stx[5][0].getArgs
  let patLists (alt : Syntax) : Array Syntax := alt[1].getSepArgs
  unless alts.any fun alt =>
      (patLists alt).any fun pl => pl.getSepArgs.any (headsAtViewed viewed) do
    throwUnsupportedSyntax
  -- a discriminant is gone through only where an alternative names a
  -- constructor of it, so a `match` Lean already handles is handed straight back
  let mut through : Array (Option Through) := #[]
  for d in discrs do
    let some mem ← memberOf? d | through := through.push none; continue
    let some (view, _) := viewOf? (← getEnv) mem | through := through.push none; continue
    let vi ← getConstInfoInduct view
    let ctors := vi.ctors.foldl (init := ({} : NameSet)) fun s c =>
      s.insert (c.replacePrefix view mem)
    let some c := vi.ctors[0]? | through := through.push none; continue
    let k := (← explicitArity (c.replacePrefix view mem)) - (← explicitArity c)
    let i := through.size
    let mut named := false
    let mut namedPromoted := false
    for alt in alts do
      for pl in patLists alt do
        let pats := pl.getSepArgs
        if h : i < pats.size then
          if let some (_, args) ← ctorOf? mem ctors pats[i] then
            named := true
            if (args.extract 0 (min k args.size)).any (·.isIdent) then namedPromoted := true
    unless named do through := through.push none; continue
    -- what the discriminant's own type says the promoted fields are.  Reading
    -- it costs an elaboration, so it is done only where a name wants one
    let mut args := #[]
    if namedPromoted then
      let ty ← whnfR (← instantiateMVars (← inferType (← elabTerm d[1] none)))
      let tyArgs := ty.getAppArgs
      if vi.numParams > tyArgs.size then through := through.push none; continue
      args ← (tyArgs.extract (vi.numParams - k) vi.numParams).mapM exprToSyntax
    through := through.push <| some
      { mem, ctors, view, promoted := k, args, discr := ⟨d[1]⟩ }
  unless through.any (·.isSome) do throwUnsupportedSyntax
  -- the view of each discriminant goes in right after it, so that the
  -- discriminant is generalised before the type that refines it is read
  let mut newDiscrs := #[]
  for d in discrs, t? in through do
    match t? with
    | none => newDiscrs := newDiscrs.push d
    | some t =>
      newDiscrs := newDiscrs.push (mkDiscr d[0] t.discr)
      newDiscrs := newDiscrs.push
        (mkDiscr (mkNullNode #[]) (← `($(mkIdent (viewFnName t.mem)) $(t.discr))))
  let mut newAlts := #[]
  for alt in alts do
    let mut lists := #[]
    let mut lets : Array (Ident × Term) := #[]
    for pl in patLists alt do
      let pats := pl.getSepArgs
      if pats.size != discrs.size then throwUnsupportedSyntax
      let mut newPats := #[]
      for p in pats, t? in through do
        match t? with
        | none => newPats := newPats.push p
        | some t =>
          match ← ctorOf? t.mem t.ctors p with
          | none => newPats := newPats.push p; newPats := newPats.push (← `(_))
          | some (c, args) =>
            if args.size < t.promoted then throwUnsupportedSyntax
            for j in *...t.promoted do
              let a := args[j]!
              if a.isIdent then
                let some v := t.args[j]? | throwUnsupportedSyntax
                lets := lets.push (⟨a⟩, v)
              else unless a.getKind == ``Lean.Parser.Term.hole do
                throwErrorAt a "This argument of `{c}` is settled by the type of \
                  what is being matched rather than by the pattern, so it can be \
                  written only as `_`, or as a name to have it under."
            let head := mkDotIdent p (Name.mkSimple c.getString!)
            let rest := args.extract t.promoted args.size
            -- a view presents the constructor a member was built by and stops
            -- there, so a constructor written under one is out of its reach.
            -- Only a pattern that is not already a variable can be one
            let isVar (a : Syntax) := a.isIdent || a.getKind == ``Lean.Parser.Term.hole
            if rest.any (!isVar ·) then
              let heads ← explicitFieldHeads c
              for j in *...rest.size do
                let a := rest[j]!
                if isVar a then continue
                let some sub := heads[t.promoted + j]? | continue
                if (viewedMembers (← getEnv)).contains sub then
                  throwErrorAt a "A constructor of `{sub}` cannot be written inside \
                    another pattern. `{sub}` is matched through a view, which \
                    presents one constructor and stops, so this one has to be \
                    reached by a `match` of its own."
            newPats := newPats.push (← `(_))
            newPats := newPats.push <|
              if rest.isEmpty then head.raw
              else Syntax.node .none ``Lean.Parser.Term.app #[head, mkNullNode rest]
      lists := lists.push (sepNode ", " newPats)
    -- what the view carries as a parameter is not in the pattern to be bound,
    -- so a writer who named it is given it by definition instead
    if lets.size > 0 && lists.size > 1 then throwUnsupportedSyntax
    let mut rhs : Term := ⟨alt[3]⟩
    for (x, v) in lets.reverse do
      rhs ← `(let $x := $v; $rhs)
    newAlts := newAlts.push <| alt.setArg 1 (sepNode " | " lists) |>.setArg 3 rhs.raw
  let stx := stx.setArg 3 (sepNode ", " newDiscrs)
    |>.setArg 5 (stx[5].setArg 0 (mkNullNode newAlts))
  trace[Mumi.view] "matching through a view:{indentD m!"{stx}"}"
  elabTerm stx expectedType?

end Mumi
