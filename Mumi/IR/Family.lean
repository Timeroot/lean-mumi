module

public import Lean
public import Mumi.IR.Frontend
public import Mumi.Options

public section

/-!
# Induction-induction and induction-recursion together, one universe up

`Mumi.IR.Frontend` reads a block of unindexed carriers and their decoders.  This
module reads the general shape: carriers may be *indexed*, an index domain may
be another carrier of the block (induction-induction) or a decoder's value
(a type computed by recursion), and a decoder may recurse over an indexed
carrier.  Everything is lowered to the *graph* encoding the frontend uses one
universe up, and the induction-induction that is left after the decoders have
become indices is handed to `Mumi.IndInd` through the ordinary `mutual` command.

## The encoding

For every carrier `X (params) : (i₁ : I₁) → … → Type u` with decoders
`f₁ … fₖ`, a record `_ir_X_Sem` holds one field per decoder -- the *semantics* a
value of `X` computes -- and a graph `_ir_X` is indexed by those semantics:

```lean
structure _ir_X_Sem (params) (semantic halves of i₁ … iₙ) : Type (u+1) where
  _ir_out0 : R₁
  …
inductive _ir_X (params) : (i₁ … iₙ, each carrier-typed one split in two) →
    _ir_X_Sem … → Type (u+1)
```

An index `(Γ : Ctx)` of carrier type is split into its semantic half
`_ir_sem_Γ : _ir_Ctx_Sem` and its graph half `Γ : _ir_Ctx _ir_sem_Γ`; a plain
index keeps its type, rewritten so that every decoder application reads the
semantic half it is about.  A constructor field of carrier type splits the same
way, and the constructor's conclusion carries the decoders' clauses as its last
index.  The graph block is still induction-inductive whenever the block was --
`_ir_Ty`'s arity names `_ir_Ctx` -- and that is `Mumi.IndInd`'s job.

The public carrier is `X idx := (s : _ir_X_Sem …) × _ir_X … s`, a decoder is the
projection `fⱼ x := x.1._ir_outj`, a constructor packs the clauses with the graph
constructor, and the recursor is the graph's own recursor with its motives and
minor premises repacked.  Every decoder equation and every iota rule is `rfl`.

Each carrier's graph lands one universe above where the carrier was written,
so a block whose carriers sit in different universes is declared by `Mumi`
across them, and the recursor of each graph then takes motives for the
members of its own strongly connected component only; `X.rec` is read off it
(`graphRecMembers`).

## A `Prop` member

A `Prop` member of the block -- `P : A → Prop`, with `A.a1 … (h : P x)` -- has
no graph.  Its proofs are the well-formedness of the data: the graph
constructors take no proof fields, and after the graph block a `mutual` of
Lean's own declares, in `Prop`, a predicate `_ir_X_W` over every data member's
graph -- a node is well formed when its fields are and the proofs the
constructor was written with are at hand -- and `_ir_P_W` for every `Prop`
member, its fields of carrier type each followed by their well-formedness.
This is what lets a `Prop` constructor take a `B : Type 3` while `A : Type 1`
takes a proof of it: `Mumi.IndInd`'s erasure would lose the well-formedness
of a field the constructor's conclusion does not mention, whereas here the
proof carries it.  The public carrier is then the subtype
`{a : (s : _ir_X_Sem …) × _ir_X … s // _ir_X_W … a.1 a.2}`, `P idx := _ir_P_W …`,
and `X.rec` runs the graph's recursor at the motive
`fun s g => ∀ w, motive ⟨⟨s, g⟩, w⟩`, each minor premise reading the fields'
well-formedness and the proofs off the node's (`_ir_X_invert`, by cases on
the predicate at a motive `_ir_X_Inv` computed by cases on the node).  Iota
is `rfl` by structure eta and proof irrelevance.  `P.rec` and `P.casesOn` come
from `_ir_P_W`'s, with a hypothesis at each proof of a `Prop` member.

## What is not here yet

The carrier lands in `Type (u+1)`; the reflection axiom of `Mumi/IR/Mahlo.lean`
that keeps it at `Type u` is not wired to this path.  No view, `match`
rewriting or `deriving`; recursive consumers go through `X.rec`.
-/

namespace Mumi.IndRec.Family
open Lean Elab Command

/-- A binder of a carrier's arity, after the shared parameters. -/
structure Index where
  name : Name
  type : Syntax
  /-- `some (k, args)` when the binder's type is carrier `k` at index arguments `args`. -/
  member : Option (Nat × Array Syntax) := none
  deriving Inhabited

structure Field where
  name : Name
  type : Syntax
  /-- `some (k, args)` when the field is a carrier `k` at index arguments `args`,
  possibly under the binders `domain`. -/
  target : Option (Nat × Array Syntax) := none
  domain : Array Binder := #[]
  /-- `some t` for a hidden field: one the lower view adds for a constructor
  application `t` in an index term, over `domain`: an argument of another
  constructor application (`hiddenArg`), whose semantics is its value's, or a
  conclusion index with such an argument, whose semantics is its own decode. -/
  value : Option Syntax := none
  hiddenArg : Bool := false
  deriving Inhabited

structure Ctor where
  name : Name
  fields : Array Field
  /-- The index arguments of the conclusion. -/
  result : Array Syntax
  /-- At the written universe: the fields and conclusion with every constructor
  application nested inside another in an index term named by a hidden field,
  so that each index term applies a constructor to fields only. -/
  lower : Option (Array Field × Array Syntax) := none
  deriving Inhabited

/-- The constructor as the raw world sees it. -/
def Ctor.lowerOf (c : Ctor) : Ctor :=
  match c.lower with
  | some (fields, result) => { c with fields, result }
  | none => c

structure Member where
  name : Name
  indices : Array Index
  ctors : Array Ctor
  /-- A member declared in `Prop`: it has no decoders, no semantics and no
  graph; a field of its type is a proof, and one universe up it is a
  well-formedness predicate over the graphs. -/
  prop : Bool := false
  /-- The level of the member's `Type`, as written; `""` for a `Prop` member. -/
  level : String := ""
  deriving Inhabited

structure Decoder where
  name : Name
  target : Nat
  /-- The decoder's own binders for the target's indices, as written. -/
  idx : Array Binder
  major : Name
  majorType : Syntax
  result : Syntax
  /-- One clause per constructor of the target, over the constructor's own field
  names, with the index patterns replaced by the conclusion's index terms. -/
  clauses : Array Syntax
  deriving Inhabited

structure Block where
  members : Array Member
  decoders : Array Decoder
  params : Array Binder
  /-- The level of the first carrier's `Type`; at the written universe, of every carrier's. -/
  level : String
  /-- Whether the block is lowered at its own universe (`mumi.mahlo true`). -/
  lower : Bool := false
  /-- One universe up, whether the block has a `Prop` member: then every
  public carrier is the subtype of its graph by a well-formedness predicate,
  and the proofs are fields of those predicates' constructors, not of the graph's. -/
  wf : Bool := false
  /-- One universe up, for each data member, the data members whose motives
  its graph's recursor takes, in the recursor's order: every one when Lean
  declared the graph block, those of one strongly connected component when
  `Mumi` declared it across universes.  Empty until the graph is declared, and
  at the written universe, where the recursion is always joint. -/
  recs : Array (Array Nat) := #[]
  /-- At the written universe, the data members by universe, in an order every
  carrier's fields and indices of carrier type come before it: each is one
  stage engine, and to a later engine a carrier of an earlier one is a value
  of a type already declared. -/
  groups : Array (Array Nat) := #[]
  deriving Inhabited

/-- A variable of carrier type as the encoding sees it: its semantic half, and
its graph half one universe up, or its raw half and the coherence of that raw
half's decode with the semantics at the universe the block was written at. -/
structure Source where
  name : Name
  sem : String
  graph : String
  /-- At the written universe the coherence; one universe up in a block with
  a `Prop` member, the well-formedness of the graph half (`""` where none is in scope). -/
  coh : String := ""
  deriving Inhabited

/-- Whether a field with this target is a proof: of a `Prop` member. -/
private def isProofTarget (b : Block) (t : Option (Nat × Array Syntax)) : Bool :=
  t.any fun (k, _) => b.members[k]!.prop
/-- The field's target when it is a data member: the recursive fields. -/
private def dataTarget (b : Block) (f : Field) : Option (Nat × Array Syntax) :=
  f.target.filter fun (k, _) => !b.members[k]!.prop
/-- The data members, in order. -/
private def dataMembers (b : Block) : Array Nat :=
  (Array.range b.members.size).filter fun i => !b.members[i]!.prop
/-- The data members `X.rec` takes motives for: those its graph's recursor
does, or, where that is not known, every one. -/
private def scope (b : Block) (i : Nat) : Array Nat :=
  match b.recs[i]? with
  | some s => if s.isEmpty then dataMembers b else s
  | none => dataMembers b
/-- The field's target when it is a data member of `scope`: a field the recursor gives a hypothesis at. -/
private def scopedTarget (b : Block) (scope : Array Nat) (f : Field) : Option (Nat × Array Syntax) :=
  (dataTarget b f).filter fun (k, _) => scope.contains k

private def aux (n : Name) (suffix := "") : String :=
  (n.getPrefix ++ Name.mkSimple ("_ir_" ++ n.getString! ++ suffix)).toString
private def semName (m : Member) := aux m.name "_Sem"
/-- The graph of a data member; the well-formedness predicate of a `Prop` member, which has no graph. -/
private def graphName (m : Member) := if m.prop then aux m.name "_W" else aux m.name
/-- The well-formedness predicate over the graph. -/
private def wfName (m : Member) := aux m.name "_W"
/-- What the well-formedness of a node says of its fields, by cases on the node. -/
private def invName (m : Member) := aux m.name "_Inv"
private def invertName (m : Member) := aux m.name "_invert"
private def wfVar (n : Name) := "_ir_wf_" ++ n.toString
/-- The `Prop` members, in order. -/
private def propMembers (b : Block) : Array Nat :=
  (Array.range b.members.size).filter fun i => b.members[i]!.prop
private def semVar (n : Name) := "_ir_sem_" ++ n.toString
private def ihVar (n : Name) := "_ir_ih_" ++ n.toString
private def outField (i : Nat) := "_ir_out" ++ toString i
private def pArgs (b : Block) := b.params.map (pname ∘ Binder.name)
private def atParams (b : Block) (n : String) := if b.params.isEmpty then n else app n (pArgs b)
private def withParams (b : Block) (n : String) (xs : Array String) := app n (pArgs b ++ xs)
private def fieldDecl (f : Binder) : CommandElabM String := do
  return par (f.name.toString ++ " : " ++ (← text f.type))
private def paramsDecl (b : Block) : CommandElabM String := return join (← b.params.mapM fieldDecl)
private def lambda (bs : Array Binder) (body : String) : CommandElabM String := do
  if bs.isEmpty then return body
  return par ("fun " ++ join (← bs.mapM fieldDecl) ++ " => " ++ body)
private def forallS (bs : Array Binder) (body : String) : CommandElabM String := do
  if bs.isEmpty then return body
  return par ("∀ " ++ join (← bs.mapM fieldDecl) ++ ", " ++ body)
private def applyDomain (f : String) (bs : Array Binder) :=
  if bs.isEmpty then f else app f (bs.map (pname ∘ Binder.name))
private def untypedLambda (xs : Array String) (body : String) : String :=
  if xs.isEmpty then body else par ("fun " ++ join xs ++ " => " ++ body)

/-- The engine data member `k` belongs to, at the written universe. -/
private def groupOf (b : Block) (k : Nat) : Nat := (b.groups.findIdx? (·.contains k)).getD 0
/-- The member engine `g` is named after: its first. -/
private def gfirst (b : Block) (g : Nat) : Name := b.members[((b.groups[g]?.bind (·[0]?)).getD 0)]!.name
/-- The universe of engine `g`. -/
private def glevel (b : Block) (g : Nat) : String :=
  let l := b.members[((b.groups[g]?.bind (·[0]?)).getD 0)]!.level
  if l.isEmpty then b.level else l
/-- Whether carrier `j` is of another engine than carrier `k`'s. -/
private def foreign (b : Block) (k j : Nat) : Bool := groupOf b k != groupOf b j
private def sortName (b : Block) (g : Nat) := aux (gfirst b g) "_Sort"
private def sigName (b : Block) (g : Nat) := aux (gfirst b g) "_sig"
private def famName (b : Block) (g : Nat) := aux (gfirst b g) "_Fam"
private def motiveName (b : Block) (g : Nat) := aux (gfirst b g) "_Motive"
private def indName (b : Block) (g : Nat) := aux (gfirst b g) "_induction"
private def sortPat (b : Block) (i : Nat) := "⟨" ++ sortName b (groupOf b i) ++ ".s" ++ toString i ++ "⟩"
private def sortValue (b : Block) (i : Nat) := par (sortPat b i ++ " : ULift " ++ sortName b (groupOf b i))
private def tagName (m : Member) := aux m.name "_Tag"
private def iName (m : Member) := aux m.name "_I"
private def dName (m : Member) := aux m.name "_D"
private def trName (m : Member) := aux m.name "_tr"
private def rawName (m : Member) := aux m.name "_Raw"
private def decName (m : Member) := aux m.name "_dec"
private def goodName (m : Member) := aux m.name "_Good"
private def pubSemName (m : Member) := aux m.name "_sem"
private def shapeName (m : Member) := aux m.name "_Shape"
private def shapeLemma (m : Member) := aux m.name "_shape"
private def castName (m : Member) := aux m.name "_cast"
private def pieceName (m : Member) (c : Ctor) := aux m.name ("_" ++ c.name.toString ++ "_sem")
private def contName (m : Member) (c : Ctor) (i : Nat) := aux m.name ("_" ++ c.name.toString ++ "_k" ++ toString i)
private def stepName (m : Member) (c : Ctor) := aux m.name ("_" ++ c.name.toString ++ "_step")
/-- The decode of a raw constructor is its piece: at variables, `rfl`. -/
private def valLemma (m : Member) (c : Ctor) := aux m.name ("_" ++ c.name.toString ++ "_val")
/-- A public constructor's raw half is the raw constructor: `rfl`. -/
private def rawLemma (m : Member) (c : Ctor) := aux m.name ("_" ++ c.name.toString ++ "_raw")
private def cohVar (n : Name) := "_ir_coh_" ++ n.toString
/-- The equation pinning a hidden field to its value. -/
private def eqVar (n : Name) := "_ir_eq_" ++ n.toString
private def hVar (n : Name) := "_ir_h_" ++ n.toString
private def pubVar (n : Name) := "_ir_pub_" ++ n.toString
private def packedVar (n : Name) := "_ir_packed_" ++ n.toString
private def cohboxVar (n : Name) := "_ir_cohbox_" ++ n.toString
private def boxVar (n : Name) := "_ir_box_" ++ n.toString
private def valuesVar (n : Name) := "_ir_values_" ++ n.toString
private def sigAt (b : Block) (g : Nat) := atParams b (sigName b g)
private def relationAt (b : Block) (g : Nat) := par ("Mumi.IR.model " ++ sigAt b g) ++ ".lt"
private def indexed (b : Block) (k : Nat) := !b.members[k]!.indices.isEmpty

/-- `s` read as carrier `k` at the shared parameters and some index arguments. -/
private def memberApp? (names : Array Name) (params : Array Binder) (s : Syntax) :
    Option (Nat × Array Syntax) := Id.run do
  let (head, args) := unapp s
  let some i := names.findIdx? (same head ·) | return none
  if args.size < params.size then return none
  if !((args.extract 0 params.size).zip params).all (fun (a, p) => same a p.name) then return none
  return some (i, args.extract params.size args.size)

/-- The constructor `s` names, as `X.c` or `.c` against the expected carrier. -/
private def ctorRef? (b : Block) (expect : Option Nat) (s : Syntax) : Option (Nat × Nat) := Id.run do
  if s.isOfKind ``Parser.Term.dotIdent then
    let some k := expect | return none
    let some ci := b.members[k]!.ctors.findIdx? (·.name == s[1].getId) | return none
    return some (k, ci)
  unless s.isIdent do return none
  let n := s.getId
  for k in [:b.members.size] do
    let m := b.members[k]!
    if m.name.isPrefixOf n && n != m.name then
      if let some ci := m.ctors.findIdx? (fun c => n == m.name ++ c.name) then
        return some (k, ci)
  return none

/-- The state `emit` is retried from when a variant of a declaration fails. -/
private def emitFirst (variants : Array String) : CommandElabM Unit := do
  let mut last : Option Exception := none
  for v in variants do
    let saved ← get
    try
      emit v
      return
    catch e =>
      set saved
      last := some e
  if let some e := last then throw e

/-- A `def` that may have to be `noncomputable`: the graph recursor is a kernel
recursor when Lean declared the graph block, and a compiled definition when
`Mumi.IndInd` did. -/
private def emitDef (attrs : String) (rest : String) : CommandElabM Unit :=
  emitFirst #[attrs ++ "def " ++ rest, attrs ++ "noncomputable def " ++ rest]

/-! ## Reading the block -/

private def readBlock (elems : Array Syntax) : CommandElabM Block := do
  unless (← getScope).varDecls.isEmpty do
    throwError "IR prototype does not yet support section variables; write shared parameters on each declaration"
  let globalNames := elems.map (·[1][1][0].getId)
  let mut params : Array Binder := #[]
  let mut level := ""
  let mut heads : Array (Name × Array Binder × Bool × String) := #[]
  for e in elems do
    checkReservedNames e
    unless plainModifiers e[0] do throwErrorAt e "IR prototype does not yet support declaration modifiers or attributes inside a block"
    let d := e[1]
    unless d[1][0].getId.isAtomic do
      throwErrorAt d "IR prototype requires simple declaration names; place the mutual block inside a namespace"
    unless d[1][1].getNumArgs == 0 do throwErrorAt d "IR prototype uses surrounding universe declarations, not explicit declaration universe lists"
    if d.isOfKind ``Parser.Command.«inductive» then
      let (ps, result) ← signature d[2]
      let (idx, result) ← telescope result
      let prop := result.isOfKind ``Parser.Term.prop
      unless prop || result.isOfKind ``Parser.Term.type do
        throwErrorAt result "IR prototype supports carriers declared in Type u, possibly indexed, and members in Prop"
      let l ← if prop then pure "" else if result[1].getNumArgs == 0 then pure "0" else pure (result[1][0].reprint.getD "0" |>.trimAscii.toString)
      if heads.isEmpty then params := ps
      else
        unless ps.size == params.size && (← (ps.zip params).allM fun (a,b) => do return a.name == b.name && (← text a.type) == (← text b.type)) do
          throwErrorAt d "IR prototype requires identical shared parameters on all declarations"
      unless prop do
        if level.isEmpty then level := l
      unless d[6][0].getNumArgs == 0 do throwErrorAt d "IR prototype does not yet support deriving clauses"
      heads := heads.push (d[1][0].getId, idx, prop, l)
  checkDistinct (params.map (·.name)) globalNames
  for p in params do checkTermBinders (globalNames ++ params.map (·.name)) p.type
  let names := heads.map (·.1)
  -- the arities, now that every carrier's name and arity length are known
  let mut members : Array Member := #[]
  for (n, idx, prop, l) in heads do
    checkDistinct (idx.map (·.name)) (globalNames ++ params.map (·.name))
    let mut indices := #[]
    for x in idx do
      checkTermBinders (globalNames ++ params.map (·.name) ++ idx.map (·.name)) x.type
      let member := memberApp? names params x.type
      if let some (k, args) := member then
        unless args.size == heads[k]!.2.1.size do
          throwErrorAt x.type "The carrier `{names[k]!}` takes {heads[k]!.2.1.size} indices"
        if heads[k]!.2.2.1 then
          throwErrorAt x.type "A `Prop` member as an index domain is not supported yet"
      else if mentions x.type names then
        throwErrorAt x.type "An index domain may name a carrier only as that carrier applied to its indices; anything else has to go through a decoder"
      indices := indices.push { name := x.name, type := x.type, member }
    members := members.push { name := n, indices, ctors := #[], prop, level := l }
  -- constructors
  let mut mi := 0
  for e in elems do
    let d := e[1]
    if d.isOfKind ``Parser.Command.«inductive» then
      let m := members[mi]!
      let mut ctors := #[]
      for c in d[4].getArgs do
        unless plainModifiers c[2] do throwErrorAt c "IR prototype does not yet support constructor modifiers"
        unless c[3].getId.isAtomic do throwErrorAt c "IR prototype requires simple constructor names"
        let (bs, result) ← signature c[4]
        let (tail, result) ← telescope result bs.size
        checkDistinct ((bs ++ tail).map (·.name)) (globalNames ++ params.map (·.name))
        let result ← if c[4][1].getNumArgs == 0 then
            if m.indices.isEmpty then parseTerm (atParams { members, decoders := #[], params, level } m.name.toString)
            else throwErrorAt c "A constructor of the indexed carrier `{m.name}` has to state its conclusion"
          else pure result
        let some (k, idxArgs) := memberApp? names params result
          | throwErrorAt result "IR constructor must return its own carrier at the unchanged parameters"
        unless k == mi do throwErrorAt result "IR constructor must return its own carrier at the unchanged parameters"
        unless idxArgs.size == m.indices.size do
          throwErrorAt result "The carrier `{m.name}` takes {m.indices.size} indices"
        let fieldNames := (bs ++ tail).map (·.name)
        let fs ← (bs ++ tail).mapM fun f => do
          checkTermBinders (globalNames ++ params.map (·.name) ++ fieldNames) f.type
          let (domain, r) ← telescope f.type
          let target := memberApp? names params r
          if let some (k, args) := target then
            unless args.size == members[k]!.indices.size do
              throwErrorAt r "The carrier `{names[k]!}` takes {members[k]!.indices.size} indices"
          if target.isNone && mentions f.type names then
            throwErrorAt f.type "IR recursive occurrences must be a carrier or a function returning a carrier; nested and negative occurrences are not supported"
          if domain.any (fun x => mentions x.type names) && target.isSome then
            throwErrorAt f.type "IR recursive argument domains cannot contain the carriers themselves"
          let mut renamed := #[]
          let mut pairs := #[]
          for k in [:domain.size] do
            let x := domain[k]!
            let name := Name.mkSimple ("_ir_index_" ++ f.name.toString ++ "_" ++ toString k)
            renamed := renamed.push { name, type := subst x.type pairs : Binder }
            pairs := pairs.push (x.name, mkIdent name)
          let target := target.map fun (k, args) => (k, args.map (subst · pairs))
          return { name := f.name, type := f.type, target, domain := if target.isSome then renamed else #[] : Field }
        for x in idxArgs do checkTermBinders (globalNames ++ params.map (·.name) ++ fieldNames) x
        ctors := ctors.push { name := c[3].getId, fields := fs, result := idxArgs }
      if ctors.isEmpty then throwErrorAt d "IR prototype currently requires at least one constructor per carrier"
      members := members.modify mi fun m => { m with ctors }
      mi := mi + 1
  -- decoders
  let mut decoders : Array Decoder := #[]
  for e in elems do
    let d := e[1]
    if d.isOfKind ``Parser.Command.definition then
      let (ps, ty) ← signature d[2]
      unless ps.size == params.size && (← (ps.zip params).allM fun (a,b) => do return a.name == b.name && (← text a.type) == (← text b.type)) do
        throwErrorAt d "IR decoder must repeat the shared parameters, followed by the carrier's indices and one carrier argument after the colon"
      -- the major is the last binder that is a carrier at exactly the binders
      -- before it; what follows it is the result
      let mut acc : Array Binder := #[]
      let mut cur := ty
      let mut found : Option (Nat × Nat) := none
      let mut result := ty
      repeat
        let (bs, rest) ← telescopeHead cur acc.size
        if bs.isEmpty then break
        for k in [:bs.size] do
          let x := bs[k]!
          if let some (i, idxArgs) := memberApp? names params x.type then
            if acc.size == members[i]!.indices.size && (idxArgs.zip acc).all (fun (a, y) => same a y.name) then
              found := some (i, acc.size)
              let trailing := bs.extract (k+1) bs.size
              result ← if trailing.isEmpty then pure rest else parseTerm (← forallS trailing (← text rest))
          acc := acc.push x
        cur := rest
      let some (i, pos) := found
        | throwErrorAt ty "IR decoder must have signature (indices) → Carrier indices → Result, with the carrier's indices bound in order just before it"
      let m := members[i]!
      if m.prop then throwErrorAt ty "A decoder may not recurse over a `Prop` member"
      let args := acc.extract 0 (pos+1)
      let major := args.back!
      checkDistinct (args.map (·.name)) (globalNames ++ params.map (·.name))
      for x in args do checkTermBinders (globalNames ++ params.map (·.name) ++ args.map (·.name)) x.type
      checkTermBinders (globalNames ++ params.map (·.name) ++ args.map (·.name)) result
      unless d[3].isOfKind ``Parser.Command.declValEqns do throwErrorAt d[3] "IR prototype requires equation-style decoder definitions"
      let eqns := d[3][0]
      unless eqns[1].getArgs.all (·.getNumArgs == 0) && eqns[2].getNumArgs == 0 do
        throwErrorAt eqns "IR prototype does not accept termination annotations or where declarations"
      let alts := eqns[0][0].getArgs
      let mut clauses := Array.replicate m.ctors.size Syntax.missing
      for alt in alts do
        unless alt[1].getNumArgs == 1 do throwErrorAt alt "IR equations need one pattern list"
        let pats := alt[1][0].getSepArgs
        unless pats.size == m.indices.size + 1 do
          throwErrorAt alt "IR equations over `{m.name}` need {m.indices.size + 1} patterns: one per index (`_` or a name) and one flat constructor pattern"
        let mut idxPats : Array (Option Name) := #[]
        for p in pats.extract 0 m.indices.size do
          if p.isOfKind ``Parser.Term.hole then idxPats := idxPats.push none
          else if p.isIdent then idxPats := idxPats.push (some p.getId)
          else throwErrorAt p "An index pattern of an IR equation is `_` or a name"
        let (h, xs) := unapp pats.back!
        let some (k, ci) := ctorRef? { members, decoders := #[], params, level } (some i) h
          | throwErrorAt h "Unknown constructor in IR equation"
        unless k == i do throwErrorAt h "This constructor belongs to `{names[k]!}`, not `{m.name}`"
        let c := m.ctors[ci]!
        unless xs.size == c.fields.size && xs.all (·.isIdent) do throwErrorAt alt "IR equations require one variable for each constructor field (no nested patterns)"
        let idxNames := idxPats.filterMap id
        checkDistinct (xs.map (·.getId) ++ idxNames) (globalNames ++ params.map (·.name))
        for n in idxNames do
          if c.fields.any (·.name == n) then
            throwErrorAt alt "The index name `{n}` is also a field name of `{c.name}`; rename one"
        checkTermBinders (globalNames ++ params.map (·.name) ++ c.fields.map (·.name) ++ xs.map (·.getId) ++ idxNames) alt[3]
        for f in c.fields do
          if !(xs.any (same · f.name)) && mentionsPrefix alt[3] f.name then
            throwErrorAt alt[3] "IR equation would capture constructor field name '{f.name}'; use the constructor's variable names or qualify the external reference"
        unless clauses[ci]!.isMissing do throwErrorAt alt "Duplicate IR constructor equation"
        let pairs := xs.zip c.fields |>.map fun (x,f) => (x.getId, mkIdent f.name)
        let rhs := subst alt[3] pairs
        -- an index the equation named stands for what the conclusion says it is
        let idxPairs := (idxPats.zip c.result).filterMap fun (p, t) => p.map fun n => (n, t)
        clauses := clauses.set! ci (subst rhs idxPairs)
      if clauses.any (·.isMissing) then throwErrorAt d "IR decoder must have exactly one equation for every constructor"
      let idx := args.extract 0 m.indices.size
      let name := d[1][0].getId
      decoders := decoders.push { name, target := i, idx, major := major.name, majorType := major.type, result, clauses }
  return { members, decoders, params, level }

/-! ## The semantic world

Everything a decoder's clause, a decoder's result type, a plain index domain and
a non-recursive field are stated in, read so that a decoder applied to a
variable of carrier type becomes a projection out of that variable's semantic
half. -/

/-- Where `s` is `x ys` for a source `x`, the source and the arguments. -/
private def sourceApp? (src : Array Source) (s : Syntax) : Option (Source × Array Syntax) :=
  let (h, ys) := unapp s
  if h.isIdent then (src.findRev? (·.name == h.getId)).map (·, ys) else none

mutual

/-- `s` rewritten into the semantic world. -/
partial def semantic (b : Block) (src : Array Source) (s : Syntax) : CommandElabM Syntax := do
  let (head, args) := unapp s
  if let some di := b.decoders.findIdx? (same head ·.name) then
    let d := b.decoders[di]!
    let nidx := b.members[d.target]!.indices.size
    unless args.size ≥ b.params.size + nidx + 1 do
      throwErrorAt s "IR decoder calls must be fully applied to a value of the carrier"
    unless ((args.extract 0 b.params.size).zip b.params).all (fun (a,p) => same a p.name) do
      throwErrorAt s "IR decoder parameters must remain unchanged"
    -- the index arguments are determined by the major and are not read
    let major := args[b.params.size + nidx]!
    let base ← semOfMajor b src major
    let base := if base.isEmpty then outField di else par base ++ "." ++ outField di
    let extra ← (args.extract (b.params.size + nidx + 1) args.size).mapM (semantic b src)
    let extraText ← extra.mapM text
    return ← parseTerm (if extra.isEmpty then base else app base extraText)
  if s.isIdent && (src.any (·.name == s.getId) || b.members.any (·.name == s.getId) || b.decoders.any (·.name == s.getId)) then
    throwErrorAt s "IR continuations may use recursive fields and indices of carrier type only through their decoders"
  if s.isOfKind ``Parser.Term.explicitBinder then
    for n in s[1].getArgs do
      if src.any (·.name == n.getId) then throwErrorAt n "IR prototype does not support shadowing a recursive field name"
  match s with
  | .node info k xs => return .node info k (← xs.mapM (semantic b src))
  | _ => return s

/-- The semantic half of the major of a decoder call: `""` for the value a
decoder's result is about, otherwise a term. -/
partial def semOfMajor (b : Block) (src : Array Source) (s : Syntax) : CommandElabM String := do
  if let some (x, ys) := sourceApp? src s then
    if x.sem.isEmpty then
      unless ys.isEmpty do throwErrorAt s "A decoder's result may mention an earlier decoder of the same value only"
      return ""
    let ys ← ys.mapM (semText b src)
    return if ys.isEmpty then x.sem else app x.sem ys
  if (ctorRef? b none (unapp s).1).isSome then
    return (← pair b src none s).1
  throwErrorAt s "IR decoder calls must target a recursive field, an index of carrier type, or a constructor application"

/-- `semantic`, as text, parenthesised so that it can stand as an argument. -/
partial def semText (b : Block) (src : Array Source) (s : Syntax) : CommandElabM String := do
  return par (← text (← semantic b src s))

/-- A term of carrier type, as its halves: the semantic one, the graph or raw
one, and in lower mode the coherence of the raw one.  It is a source, a source
applied to arguments, or a constructor application. -/
partial def pair (b : Block) (src : Array Source) (expect : Option Nat) (s : Syntax) :
    CommandElabM (String × String × String) := do
  if let some (x, ys) := sourceApp? src s then
    if x.sem.isEmpty then throwErrorAt s "A decoder's result may mention the value it is about only through decoders"
    let ys ← ys.mapM (semText b src)
    let at_ (t : String) := if ys.isEmpty then t else app t ys
    return (at_ x.sem, at_ x.graph, if x.coh.isEmpty then "" else at_ x.coh)
  let (h, args) := unapp s
  let some (k, ci) := ctorRef? b expect h
    | throwErrorAt s "An index of carrier type has to be a recursive field, one applied to its arguments, or a constructor application"
  if let some e := expect then
    unless e == k do throwErrorAt s "Expected a value of `{b.members[e]!.name}`"
  let m := b.members[k]!
  let c := m.ctors[ci]!
  unless args.size == b.params.size + c.fields.size do
    throwErrorAt s "The constructor `{m.name}.{c.name}` takes {b.params.size + c.fields.size} explicit arguments here"
  unless ((args.extract 0 b.params.size).zip b.params).all (fun (a,p) => same a p.name) do
    throwErrorAt s "IR constructor parameters must remain unchanged"
  let fargs := args.extract b.params.size args.size
  let (inner, pairs, split, semArgs, rawArgs) ← instantiate b src c fargs
  ctorPair b src inner pairs split semArgs rawArgs k ci

/-- The fields of `c` at the arguments `fargs`: sources for the recursive ones,
substitutions for the rest, the arguments the graph constructor takes, and the
semantic arguments and raw arguments the lower mode takes. -/
partial def instantiate (b : Block) (src : Array Source) (c : Ctor) (fargs : Array Syntax) :
    CommandElabM (Array Source × Array (Name × Syntax) × Array String × Array String × Array String) := do
  let mut inner : Array Source := #[]
  let mut pairs : Array (Name × Syntax) := #[]
  let mut split : Array String := #[]
  let mut semArgs : Array String := #[]
  let mut rawArgs : Array String := #[]
  let fpairs := (c.fields.zip fargs).map fun (f, a) => (f.name, a)
  for f in c.lowerOf.fields do
    -- a hidden field stands for its value at the arguments
    let a := match f.value with
      | some v => subst v fpairs
      | none => ((fpairs.find? (·.1 == f.name)).map (·.2)).getD Syntax.missing
    if let some (k, _) := dataTarget b f then
      unless f.value.isSome || f.domain.isEmpty || (unapp a).2.isEmpty || (sourceApp? src a).isSome do
        throwErrorAt a "A function-valued field passed to a constructor here has to be a name"
      let (sa, ga, ca) ← pair b src (some k) a
      -- a hidden field under binders is a function of them
      let dom := if f.value.isSome then f.domain else #[]
      let sa ← lambda dom sa
      let ga ← lambda dom ga
      let ca ← if ca.isEmpty then pure "" else lambda dom ca
      if f.value.isNone then
        inner := inner.push { name := f.name, sem := sa, graph := ga, coh := ca }
        split := split.push sa |>.push ga
      unless f.hiddenArg do semArgs := semArgs.push sa
      rawArgs := rawArgs.push ga
      if b.lower && !b.members[k]!.indices.isEmpty then rawArgs := rawArgs.push ca
    else
      pairs := pairs.push (f.name, a)
      let v ← semText b src a
      -- a proof of a `Prop` member is no argument of the graph or raw
      -- constructor, nor of a semantic piece: it is the certificate's
      unless isProofTarget b f.target do
        split := split.push v
        semArgs := semArgs.push v
        rawArgs := rawArgs.push v
  return (inner, pairs, split, semArgs, rawArgs)

/-- The decoders' clauses at `X.c`, with the fields read as `ctx`/`pairs`. -/
partial def ctorVals (b : Block) (ctx : Array Source) (k ci : Nat) (pairs : Array (Name × Syntax)) :
    CommandElabM (Array String) := do
  let mut vals := #[]
  for di in [:b.decoders.size] do
    let d := b.decoders[di]!
    if d.target == k then vals := vals.push (← semText b ctx (subst d.clauses[ci]! pairs))
  return if vals.isEmpty then #["PUnit.unit"] else vals

/-- The halves of `X.c` at fields read as `inner`/`pairs`, whose graph
arguments are `split`, and whose semantic and raw arguments are `semArgs` and
`rawArgs`.  In lower mode the raw half is the raw constructor and the
coherence is `rfl`, the decode of a rolled raw term reducing to its semantics. -/
partial def ctorPair (b : Block) (src : Array Source) (inner : Array Source) (pairs : Array (Name × Syntax))
    (split semArgs rawArgs : Array String) (k ci : Nat) : CommandElabM (String × String × String) := do
  let m := b.members[k]!
  let c := m.ctors[ci]!
  let ctx := src ++ inner
  if b.lower then
    -- its coherence is the constructor's `_at` lemma, proved once at variables:
    -- inline `rfl` would need the decode of a rolled term inside another to
    -- reduce, which the stage engine does not do
    let coh := if m.indices.isEmpty then "" else withParams b (aux m.name ("_" ++ c.name.toString ++ "_at")) rawArgs
    return (par (withParams b (pieceName m c) semArgs ++ "._ir_val"),
      withParams b (rawName m ++ "." ++ c.name.toString) rawArgs, coh)
  -- the semantic halves of the conclusion's indices
  let mut semIdx := #[]
  for (x, t) in m.indices.zip c.result do
    let t := subst t pairs
    if let some (j, _) := x.member then semIdx := semIdx.push (← pair b ctx (some j) t).1
    else semIdx := semIdx.push (← semText b ctx t)
  let vals ← ctorVals b ctx k ci pairs
  let sem := app ("@" ++ semName m ++ ".mk") (pArgs b ++ semIdx ++ vals)
  -- in a well-formed block the third half is the node's well-formedness: the
  -- constructor of the predicate at the fields' and the proofs the arguments supply
  let wf ← if !b.wf || inner.any (·.coh.isEmpty) then pure "" else do
    let props ← (c.fields.filter fun f => isProofTarget b f.target).mapM fun f =>
      semText b src (((pairs.find? (·.1 == f.name)).map (·.2)).getD Syntax.missing)
    pure (app (wfName m ++ "." ++ c.name.toString) (split ++ inner.map (·.coh) ++ props))
  -- the graph constructor takes the block's parameters implicitly, as any constructor does
  return (sem, app (graphName m ++ "." ++ c.name.toString) split, wf)

end

/-- The index arguments `args` of carrier `k`, as the graph takes them: two
halves for an index of carrier type, one for a plain one. -/
private def graphIdx (b : Block) (src : Array Source) (k : Nat) (args : Array Syntax) : CommandElabM (Array String) := do
  let mut out := #[]
  for (x, t) in b.members[k]!.indices.zip args do
    if let some (j, _) := x.member then
      let (s, g, _) ← pair b src (some j) t
      out := out.push s |>.push g
    else out := out.push (← semText b src t)
  return out

/-- The semantic halves alone. -/
private def semIdx (b : Block) (src : Array Source) (k : Nat) (args : Array Syntax) : CommandElabM (Array String) := do
  let mut out := #[]
  for (x, t) in b.members[k]!.indices.zip args do
    if let some (j, _) := x.member then out := out.push (← pair b src (some j) t).1
    else out := out.push (← semText b src t)
  return out

/-- The arity of carrier `i` as the graph takes it, and the sources it binds. -/
private def graphArity (b : Block) (i : Nat) (implicit := false) : CommandElabM (Array String × Array Source) := do
  let mut out := #[]
  let mut src : Array Source := #[]
  let bind (d : String) := if implicit then "{" ++ d ++ "}" else par d
  for x in b.members[i]!.indices do
    if let some (k, args) := x.member then
      let sIdx ← semIdx b src k args
      let gIdx ← graphIdx b src k args
      out := out.push (bind (semVar x.name ++ " : " ++ withParams b (semName b.members[k]!) sIdx))
      out := out.push (bind (x.name.toString ++ " : " ++ withParams b (graphName b.members[k]!) (gIdx ++ #[semVar x.name])))
      src := src.push { name := x.name, sem := semVar x.name, graph := x.name.toString, coh := wfVar x.name }
    else
      out := out.push (bind (x.name.toString ++ " : " ++ (← semText b src x.type)))
  return (out, src)

/-- In a well-formed block, the well-formedness of a value of carrier `k` at
the graph index arguments `gIdx`, with the halves `s` and `g`. -/
private def wfAt (b : Block) (k : Nat) (gIdx : Array String) (s g : String) : String :=
  withParams b (wfName b.members[k]!) (gIdx ++ #[s, g])

/-- The well-formedness hypotheses of carrier `i`'s arity, one per index of
carrier type: `_ir_wf_x` and its type. -/
private def arityWf (b : Block) (i : Nat) : CommandElabM (Array (String × String)) := do
  let mut out := #[]
  let mut src : Array Source := #[]
  for x in b.members[i]!.indices do
    if let some (k, args) := x.member then
      let gIdx ← graphIdx b src k args
      out := out.push (wfVar x.name, wfAt b k gIdx (semVar x.name) x.name.toString)
      src := src.push { name := x.name, sem := semVar x.name, graph := x.name.toString, coh := wfVar x.name }
  return out

/-- The semantic halves of the arity of carrier `i`: what its `Sem` record is parameterised by. -/
private def semArity (b : Block) (i : Nat) : CommandElabM (Array String × Array Source) := do
  let mut out := #[]
  let mut src : Array Source := #[]
  for x in b.members[i]!.indices do
    if let some (k, args) := x.member then
      let sIdx ← semIdx b src k args
      out := out.push (par (semVar x.name ++ " : " ++ withParams b (semName b.members[k]!) sIdx))
      src := src.push { name := x.name, sem := semVar x.name, graph := x.name.toString }
    else
      out := out.push (par (x.name.toString ++ " : " ++ (← semText b src x.type)))
  return (out, src)

/-- The names the arity of carrier `i` binds, in the graph world / the semantic world. -/
private def graphIdxNames (b : Block) (i : Nat) : Array String :=
  b.members[i]!.indices.flatMap fun x =>
    if x.member.isSome then #[semVar x.name, x.name.toString] else #[x.name.toString]
private def semIdxNames (b : Block) (i : Nat) : Array String :=
  b.members[i]!.indices.map fun x => if x.member.isSome then semVar x.name else x.name.toString
/-- The public index arguments of carrier `i`, at its own arity names. -/
private def pubIdxNames (b : Block) (i : Nat) : Array String :=
  b.members[i]!.indices.map (·.name.toString)
/-- Public index terms, as the graph takes them: `x.1 x.2` for one of carrier
type, `x.1.1 x.1.2` in a well-formed block. -/
private def pubPairIdx (b : Block) (i : Nat) (args : Array String) : Array String :=
  (b.members[i]!.indices.zip args).flatMap fun (x, a) =>
    if x.member.isSome then
      if b.wf then #[par a ++ ".1.1", par a ++ ".1.2"] else #[par a ++ ".1", par a ++ ".2"]
    else #[a]
/-- The well-formedness of the public index arguments `args` of carrier `i`: `x.2` at each of carrier type. -/
private def pubIdxWf (b : Block) (i : Nat) (args : Array String) : Array String :=
  (b.members[i]!.indices.zip args).filterMap fun (x, a) =>
    if x.member.isSome then some (par a ++ ".2") else none
/-- The public value of each index of carrier `i` out of its halves, at the arity's names. -/
private def repackIdx (b : Block) (i : Nat) : Array String :=
  b.members[i]!.indices.map fun x =>
    if x.member.isSome then
      if b.wf then "⟨⟨" ++ semVar x.name ++ ", " ++ x.name.toString ++ "⟩, " ++ wfVar x.name ++ "⟩"
      else "⟨" ++ semVar x.name ++ ", " ++ x.name.toString ++ "⟩"
    else x.name.toString
/-- The arity of carrier `i` as written, as binders. -/
private def pubArity (b : Block) (i : Nat) (implicit := false) : CommandElabM String := do
  let bs ← b.members[i]!.indices.mapM fun x => do
    let d := x.name.toString ++ " : " ++ (← text x.type)
    return if implicit then "{" ++ d ++ "}" else par d
  return join bs
/-- `X params idx`. -/
private def typeAt (b : Block) (i : Nat) (idx : Array String) : String :=
  let m := b.members[i]!
  if b.params.isEmpty && idx.isEmpty then m.name.toString else withParams b m.name.toString idx

/-- Members and decoders in an order every arity and signature can be declared in. -/
private def declarationOrder (b : Block) : CommandElabM (Array (Sum Nat Nat)) := do
  let n := b.members.size
  let names := b.members.map (·.name) ++ b.decoders.map (·.name)
  let node (x : Name) : Option Nat := names.findIdx? (· == x)
  let mentioned (ss : Array Syntax) : Array Nat := Id.run do
    let mut out := #[]
    for j in [:names.size] do
      if ss.any (mentions · #[names[j]!]) then out := out.push j
    return out
  let mut deps : Array (Array Nat) := #[]
  for m in b.members do deps := deps.push (mentioned (m.indices.map (·.type)))
  for d in b.decoders do
    deps := deps.push ((mentioned (d.idx.map (·.type) ++ #[d.majorType, d.result])).push d.target)
  let mut order := #[]
  let mut done : Array Bool := Array.replicate names.size false
  for _ in [:names.size] do
    for j in [:names.size] do
      if !done[j]! && deps[j]!.all (fun k => k == j || done[k]!) then
        done := done.set! j true
        order := order.push (if j < n then Sum.inl j else Sum.inr (j - n))
  unless order.size == names.size do
    throwError "The arities and decoder signatures of this block depend on one another in a cycle; \
      a carrier's arity may name an earlier carrier or decoder only"
  let _ := node
  return order

/-! ## Emitting -/

private def emitSemantics (b : Block) (order : Array (Sum Nat Nat)) : CommandElabM Unit := do
  let ps ← paramsDecl b
  for o in order do
    let .inl i := o | continue
    let m := b.members[i]!
    if m.prop then continue
    let (arity, src) ← semArity b i
    let mut fields := #[]
    for j in [:b.decoders.size] do
      let d := b.decoders[j]!
      if d.target == i then
        -- the decoder's own index names stand for the arity's
        let pairs := (d.idx.zip m.indices).map fun (x, y) => (x.name, mkIdent y.name)
        let result := subst d.result pairs
        fields := fields.push ("  " ++ outField j ++ " : " ++ (← semText b (src.push { name := d.major, sem := "", graph := "" }) result))
    if fields.isEmpty then fields := #["  _unit : PUnit.{" ++ m.level ++ "+1}"]
    emit ("structure " ++ semName m ++ " " ++ ps ++ " " ++ join arity ++ " : Type (" ++ m.level ++ "+1) where\n" ++ String.intercalate "\n" fields.toList)

/-- The fields of a constructor as the graph constructor takes them, and what
the well-formedness constructor adds. -/
private structure GraphFields where
  /-- The graph constructor's binders: a field of carrier type as its two halves. -/
  fields : Array String := #[]
  /-- Their names. -/
  names : Array String := #[]
  /-- Per field of carrier type, `_ir_wf_f` and its type: the well-formedness of the graph half. -/
  wf : Array (String × String) := #[]
  /-- Per proof of a `Prop` member, the field and its type at the graph halves. -/
  props : Array (String × String) := #[]
  src : Array Source := #[]

/-- The fields of `c` as the graph constructor takes them -- a proof of a
`Prop` member left out, it being the well-formedness constructor's -- and the
sources they bind. -/
private def graphFields (b : Block) (c : Ctor) : CommandElabM GraphFields := do
  let mut g : GraphFields := {}
  for f in c.fields do
    if let some (k, args) := f.target then
      let dom ← f.domain.mapM fun x => do return { x with type := ← semantic b g.src x.type }
      let gIdx ← graphIdx b g.src k args
      if b.members[k]!.prop then
        g := { g with props := g.props.push (f.name.toString, ← forallS dom (withParams b (wfName b.members[k]!) gIdx)) }
        continue
      let sIdx ← semIdx b g.src k args
      let sem := applyDomain (semVar f.name) dom
      g := { g with
        fields := g.fields.push (par (semVar f.name ++ " : " ++ (← forallS dom (withParams b (semName b.members[k]!) sIdx))))
          |>.push (par (f.name.toString ++ " : " ++ (← forallS dom (withParams b (graphName b.members[k]!) (gIdx ++ #[sem])))))
        names := g.names.push (semVar f.name) |>.push f.name.toString
        wf := g.wf.push (wfVar f.name, ← forallS dom (wfAt b k gIdx sem (applyDomain f.name.toString dom)))
        src := g.src.push { name := f.name, sem := semVar f.name, graph := f.name.toString, coh := wfVar f.name } }
    else
      g := { g with fields := g.fields.push (par (f.name.toString ++ " : " ++ (← semText b g.src f.type))), names := g.names.push f.name.toString }
  return g

private def emitGraph (b : Block) : CommandElabM Unit := do
  let ps ← paramsDecl b
  let mut ds := #[]
  for i in dataMembers b do
    let m := b.members[i]!
    let (arity, _) ← graphArity b i
    let mut cs := #[]
    for ci in [:m.ctors.size] do
      let c := m.ctors[ci]!
      let g ← graphFields b c
      let idx ← graphIdx b g.src i c.result
      let (sem, _, _) ← ctorPair b g.src #[] #[] #[] #[] #[] i ci
      cs := cs.push ("  | " ++ c.name.toString ++ " " ++ join g.fields ++ " : " ++ withParams b (graphName m) (idx ++ #[sem]))
    let arity := if arity.isEmpty then "" else String.intercalate " → " arity.toList ++ " → "
    ds := ds.push ("inductive " ++ graphName m ++ " " ++ ps ++ " : " ++ arity ++ withParams b (semName m) (semIdxNames b i) ++ " → Type (" ++ m.level ++ "+1) where\n" ++ String.intercalate "\n" cs.toList)
  -- the block is induction-inductive whenever the written one was; keep the joint recursor
  emit ("set_option mumi.separate false in\nmutual\n" ++ String.intercalate "\n" ds.toList ++ "\nend")

/-- For each data member, the data members whose motives its graph's recursor
takes, read off the recursor's type. -/
private def graphRecMembers (b : Block) : CommandElabM (Array (Array Nat)) := do
  let ns ← getCurrNamespace
  let graphs := b.members.map fun m => ns ++ (graphName m).toName
  let mut out := #[]
  for i in [:b.members.size] do
    if b.members[i]!.prop then
      out := out.push #[]
      continue
    let recName := graphs[i]! ++ `rec
    let some info := (← getEnv).find? recName
      | throwError "IR frontend: the graph recursor `{recName}` was not declared"
    let members ← liftTermElabM <| Meta.forallTelescope info.type fun xs _ => do
      let mut ms := #[]
      for x in xs do
        -- a motive: binders ending in a sort, the last of them the major premise
        let k? ← Meta.forallTelescope (← Meta.inferType x) fun ys body => do
          unless body.isSort do return none
          let some y := ys.back? | return none
          return (← Meta.inferType y).getAppFn.constName?.bind fun n => graphs.findIdx? (· == n)
        if let some k := k? then ms := ms.push k
      return ms
    out := out.push members
  return out

/-- The well-formedness predicates: one `Prop` family per member over the
graphs, in one `mutual` of Lean's own.  A data member's says of a node that its
fields are well formed and carries the proofs the constructor was written with;
a `Prop` member's is the member itself, its fields of carrier type each
followed by their well-formedness. -/
private def emitWf (b : Block) : CommandElabM Unit := do
  let ps ← paramsDecl b
  let mut ds := #[]
  for i in dataMembers b ++ propMembers b do
    let m := b.members[i]!
    let (arity, _) ← graphArity b i
    let mut cs := #[]
    for ci in [:m.ctors.size] do
      let c := m.ctors[ci]!
      let g ← graphFields b c
      let idx ← graphIdx b g.src i c.result
      let binders := g.fields ++ (g.wf ++ g.props).map fun (n, t) => par (n ++ " : " ++ t)
      let concl := if m.prop then withParams b (wfName m) idx
        else withParams b (wfName m) (idx ++ #["_", app (graphName m ++ "." ++ c.name.toString) g.names])
      cs := cs.push ("  | " ++ c.name.toString ++ " " ++ join binders ++ " : " ++ concl)
    let arity := if arity.isEmpty then "" else String.intercalate " → " arity.toList ++ " → "
    let self := if m.prop then "" else
      "(_ir_s : " ++ withParams b (semName m) (semIdxNames b i) ++ ") → (_ir_a : " ++ withParams b (graphName m) (graphIdxNames b i ++ #["_ir_s"]) ++ ") → "
    ds := ds.push ("inductive " ++ wfName m ++ " " ++ ps ++ " : " ++ arity ++ self ++ "Prop where\n" ++ String.intercalate "\n" cs.toList)
  emit ("mutual\n" ++ String.intercalate "\n" ds.toList ++ "\nend")

/-- The conjunction of what constructor `ci` of `i`'s well-formedness carries, over the graph fields. -/
private def wfConj (b : Block) (i ci : Nat) : CommandElabM (GraphFields × String) := do
  let g ← graphFields b b.members[i]!.ctors[ci]!
  return (g, (g.wf ++ g.props).foldr (fun (_, t) acc => par (t ++ " ∧ " ++ acc)) "True")

/-- The inversion of a data member's well-formedness: `_ir_X_Inv`, by
recursion on the node -- the graph's recursor, which every graph has whoever
declared it, at `Prop` and with its hypotheses unused -- is the conjunction of
what the constructor's well-formedness carries, and `_ir_X_invert` proves it,
by cases on the well-formedness at that motive. -/
private def emitInv (b : Block) : CommandElabM Unit := do
  let ps ← paramsDecl b
  for i in dataMembers b do
    let m := b.members[i]!
    let scope := scope b i
    let (arity, _) ← graphArity b i
    let (implicitArity, _) ← graphArity b i (implicit := true)
    let gIdx := graphIdxNames b i
    let semTy := withParams b (semName m) (semIdxNames b i)
    let selfTy := withParams b (graphName m) (gIdx ++ #["_ir_s"])
    let mut rargs := pArgs b
    for k in scope do rargs := rargs.push (untypedLambda (graphIdxNames b k ++ #["_", "_"]) "Prop")
    for k in scope do
      for ck in [:b.members[k]!.ctors.size] do
        let (g, conj) ← wfConj b k ck
        let ihs := (b.members[k]!.ctors[ck]!.fields.filter fun f => (scopedTarget b scope f).isSome).map fun _ => "_"
        rargs := rargs.push (untypedLambda (g.names ++ ihs) conj)
    let mut inverts := #[]
    for ci in [:m.ctors.size] do
      let (g, conj) ← wfConj b i ci
      let parts := g.wf ++ g.props
      let witness := parts.foldr (fun (n, _) acc => "⟨" ++ n ++ ", " ++ acc ++ "⟩") "trivial"
      inverts := inverts.push (untypedLambda (g.names ++ parts.map (·.1)) (par (witness ++ " : " ++ conj)))
    let arityArrows := if arity.isEmpty then "" else String.intercalate " → " arity.toList ++ " → "
    emit ("def " ++ invName m ++ " " ++ ps ++ " : " ++ arityArrows ++ "(_ir_s : " ++ semTy ++ ") → " ++ selfTy ++ " → Prop := " ++
      untypedLambda (gIdx ++ #["_ir_s", "_ir_a"]) (app ("@" ++ graphName m ++ ".rec") (rargs ++ gIdx ++ #["_ir_s", "_ir_a"])))
    emit ("theorem " ++ invertName m ++ " " ++ ps ++ " " ++ join implicitArity ++ " {_ir_s : " ++ semTy ++ "} {_ir_a : " ++ selfTy ++ "} (_ir_w : " ++ wfAt b i gIdx "_ir_s" "_ir_a" ++ ") : " ++ withParams b (invName m) (gIdx ++ #["_ir_s", "_ir_a"]) ++ " := " ++
      app ("@" ++ wfName m ++ ".casesOn") (pArgs b ++ #[untypedLambda (gIdx ++ #["_ir_s", "_ir_a", "_"]) (withParams b (invName m) (gIdx ++ #["_ir_s", "_ir_a"]))] ++ gIdx ++ #["_ir_s", "_ir_a", "_ir_w"] ++ inverts))

private def emitPublic (b : Block) (order : Array (Sum Nat Nat)) : CommandElabM Unit := do
  let ps ← paramsDecl b
  for o in order do
    match o with
    | .inl i =>
      let m := b.members[i]!
      let ppi := pubPairIdx b i (pubIdxNames b i)
      if m.prop then
        emit ("@[reducible] def " ++ m.name.toString ++ " " ++ ps ++ " " ++ (← pubArity b i) ++ " : Prop := " ++ withParams b (wfName m) ppi)
      else if b.wf then
        emit ("@[reducible] def " ++ m.name.toString ++ " " ++ ps ++ " " ++ (← pubArity b i) ++ " : Type (" ++ m.level ++ "+1) := { _ir_a : Mumi.IR.Graph.Carrier " ++ withParams b (graphName m) ppi ++ " // " ++ withParams b (wfName m) (ppi ++ #["_ir_a.1", "_ir_a.2"]) ++ " }")
      else
        emit ("@[reducible] def " ++ m.name.toString ++ " " ++ ps ++ " " ++ (← pubArity b i) ++ " : Type (" ++ m.level ++ "+1) := Mumi.IR.Graph.Carrier " ++ withParams b (graphName m) ppi)
    | .inr j =>
      let d := b.decoders[j]!
      let idx ← d.idx.mapM fieldDecl
      let result := subst d.result #[(d.major, mkIdent `_ir_self)]
      let node := if b.wf then "_ir_self.1.1." else "_ir_self.1."
      emit ("@[reducible] def " ++ d.name.toString ++ " " ++ ps ++ " " ++ join idx ++ " (_ir_self : " ++ (← text d.majorType) ++ ") : " ++ (← text result) ++ " := " ++ node ++ outField j)
  for i in [:b.members.size] do
    let m := b.members[i]!
    for ci in [:m.ctors.size] do
      let c := m.ctors[ci]!
      let mut xs := #[]
      let mut wfs := #[]
      let mut props := #[]
      for f in c.fields do
        if (dataTarget b f).isSome then
          let v := par (applyDomain f.name.toString f.domain)
          if b.wf then
            xs := xs.push (← lambda f.domain (v ++ ".1.1")) |>.push (← lambda f.domain (v ++ ".1.2"))
            wfs := wfs.push (← lambda f.domain (v ++ ".2"))
          else
            xs := xs.push (← lambda f.domain (v ++ ".1")) |>.push (← lambda f.domain (v ++ ".2"))
        else if isProofTarget b f.target then props := props.push f.name.toString
        else xs := xs.push f.name.toString
      let attrs := if c.fields.isEmpty then "@[reducible, match_pattern] " else "@[reducible] "
      let fields ← c.fields.mapM fun f => fieldDecl { name := f.name, type := f.type }
      let result ← c.result.mapM text
      let head := m.name.toString ++ "." ++ c.name.toString ++ " " ++ ps ++ " " ++ join fields ++ " : " ++ typeAt b i result
      let wfApp := app (wfName m ++ "." ++ c.name.toString) (xs ++ wfs ++ props)
      if m.prop then
        emit ("theorem " ++ head ++ " := " ++ wfApp)
      else if b.wf then
        emit (attrs ++ "def " ++ head ++ " := ⟨⟨_, " ++ app (graphName m ++ "." ++ c.name.toString) xs ++ "⟩, " ++ wfApp ++ "⟩")
      else
        emit (attrs ++ "def " ++ head ++ " := ⟨_, " ++ app (graphName m ++ "." ++ c.name.toString) xs ++ "⟩")

/-! ## Recursors -/

private def minor (b : Block) (i ci : Nat) := Id.run do
  let c := b.members[i]!.ctors[ci]!
  let count := b.members.foldl (fun n m => n + (m.ctors.filter (·.name == c.name)).size) 0
  let n := if count == 1 then c.name.toString else
    b.members[i]!.name.toString.replace "." "_" ++ "_" ++ c.name.toString
  let used := b.params.any (fun p => p.name.toString == n) ||
    b.members.any (fun m => m.ctors.any (fun c => c.fields.any (fun f => f.name.toString == n))) ||
    b.members.any (fun m => m.indices.any (fun x => x.name.toString == n))
  return if used then "_ir_case" ++ toString i ++ "_" ++ toString ci else n
private def motiveArgs (b : Block) (scope : Array Nat := dataMembers b) := scope.map motive
private def minorArgs (b : Block) (scope : Array Nat := dataMembers b) :=
  scope.flatMap fun i => (Array.range b.members[i]!.ctors.size).map (minor b i)
private def motiveType (b : Block) (i : Nat) : CommandElabM String := do
  let arity ← pubArity b i
  let self := "(_ir_self : " ++ typeAt b i (pubIdxNames b i) ++ ")"
  return "∀ " ++ arity ++ " " ++ self ++ ", Sort _ir_elim"
private def motiveDecls (b : Block) (scope : Array Nat := dataMembers b) : CommandElabM String := do
  return join (← scope.mapM fun i => do return "{" ++ motive i ++ " : " ++ (← motiveType b i) ++ "}")
private def ctorApp (b : Block) (i ci : Nat) (xs : Array String) :=
  withParams b (b.members[i]!.name.toString ++ "." ++ b.members[i]!.ctors[ci]!.name.toString) xs
private def fieldNames (c : Ctor) := c.fields.map (·.name.toString)
private def fieldsDecl (c : Ctor) : CommandElabM String := do
  return join (← c.fields.mapM fun f => fieldDecl { name := f.name, type := f.type })
private def applyTo (f : String) (xs : Array String) := if xs.isEmpty then f else app f xs

/-- `motive_j idx (f dom)` for the recursive field `f`. -/
private def ihType (f : Field) (name : Option String := none) : CommandElabM String := do
  let some (j, args) := f.target | unreachable!
  let args ← args.mapM text
  forallS f.domain (app (name.getD (motive j)) (args ++ #[applyDomain f.name.toString f.domain]))

private def minorDecls (b : Block) (induction : Bool) (scope : Array Nat := dataMembers b) : CommandElabM String := do
  let mut out := #[]
  for i in scope do
    for ci in [:b.members[i]!.ctors.size] do
      let c := b.members[i]!.ctors[ci]!
      let mut ihs := #[]
      if induction then
        for f in c.fields do
          if (scopedTarget b scope f).isSome then
            ihs := ihs.push (par (ihVar f.name ++ " : " ++ (← ihType f)))
      let result ← c.result.mapM text
      let concl := app (motive i) (result ++ #[ctorApp b i ci (fieldNames c)])
      let decls ← fieldsDecl c
      let ty := if c.fields.isEmpty then concl else "∀ " ++ decls ++ " " ++ join ihs ++ ", " ++ concl
      out := out.push (par (minor b i ci ++ " : " ++ ty))
  return join out

/-- The graph motive standing for the public `motive_i`: in a well-formed
block, under the well-formedness of the indices and of the node. -/
private def graphMotive (b : Block) (i : Nat) : CommandElabM String := do
  let value := app (motive i) (repackIdx b i ++ #[if b.wf then "⟨⟨_ir_s, _ir_g⟩, _ir_w⟩" else "⟨_ir_s, _ir_g⟩"])
  let body ← if b.wf then do
      let hyps := ((← arityWf b i).map fun (n, t) => par (n ++ " : " ++ t)).push
        (par ("_ir_w : " ++ wfAt b i (graphIdxNames b i) "_ir_s" "_ir_g"))
      pure ("∀ " ++ join hyps ++ ", " ++ value)
    else pure value
  return untypedLambda (graphIdxNames b i ++ #["_ir_s", "_ir_g"]) body

/-- The `j`th conjunct of an inversion. -/
private def conjunct (inv : String) (j : Nat) : String :=
  par inv ++ String.join (List.replicate j ".2") ++ ".1"
/-- Where field `f` of `c` sits among the conjuncts: the fields of carrier type first, then the proofs. -/
private def conjunctIdx (b : Block) (c : Ctor) (f : Field) : Nat := Id.run do
  let data := c.fields.filter fun g => (dataTarget b g).isSome
  if let some j := data.findIdx? (·.name == f.name) then return j
  let props := c.fields.filter fun g => isProofTarget b g.target
  return data.size + ((props.findIdx? (·.name == f.name)).getD 0)

/-- The graph minor premise standing for the public one: the split fields
repacked, and in a well-formed block each with its well-formedness read off
the node's inversion, the proof fields too; a hypothesis is passed on at the
well-formedness of the field's indices and its own. -/
private def recImplName (m : Member) := m.name.toString ++ "._ir_recImpl"

/-- The graph minor premise standing for the public one: the split fields
repacked, and in a well-formed block each with its well-formedness read off
the node's inversion, the proof fields too; a hypothesis is passed on at the
well-formedness of the field's indices and its own.  For the compiled
companion (`impl`), a `casesOn` minor: no hypotheses are taken, and each is a
recursive call on the repacked field. -/
private def graphMinor (b : Block) (i ci : Nat) (minorName : String) (ihs : Bool) (scope : Array Nat) (impl := false) : CommandElabM String := do
  let c := b.members[i]!.ctors[ci]!
  let inv := withParams b (invertName b.members[i]!) #["_ir_w"]
  -- a proof field is no binder here: where an index term names one, it is the inversion's conjunct
  let propPairs ← (c.fields.filter fun f => isProofTarget b f.target).mapM fun f => do
    return (f.name, ← parseTerm (conjunct inv (conjunctIdx b c f)))
  let mut binders := #[]
  let mut images := #[]
  let mut ihNames := #[]
  let mut ihImages := #[]
  let mut src : Array Source := #[]
  for f in c.fields do
    if let some (k, args) := dataTarget b f then
      binders := binders.push (semVar f.name) |>.push f.name.toString
      let dom ← f.domain.mapM fun x => do return { x with type := ← semantic b src x.type }
      let w := if b.wf then conjunct inv (conjunctIdx b c f) else ""
      let halves := "⟨" ++ applyDomain (semVar f.name) dom ++ ", " ++ applyDomain f.name.toString dom ++ "⟩"
      let image := if b.wf then "⟨" ++ halves ++ ", " ++ applyDomain w dom ++ "⟩" else halves
      images := images.push (← lambda dom image)
      if scope.contains k then
        if impl then
          let recArgs := pArgs b ++ motiveArgs b scope ++ minorArgs b scope ++ b.members[k]!.indices.map (fun _ => "_")
          ihImages := ihImages.push (← lambda dom (app ("@" ++ recImplName b.members[k]!) (recArgs.push image)))
        else
          ihNames := ihNames.push (ihVar f.name)
          if b.wf then
            let mut ws := #[]
            for (x, t) in b.members[k]!.indices.zip args do
              if let some (j, _) := x.member then ws := ws.push (← pair b src (some j) (subst t propPairs)).2.2
            ihImages := ihImages.push (← lambda dom (app (applyDomain (ihVar f.name) dom) (ws.push (applyDomain w dom))))
          else ihImages := ihImages.push (ihVar f.name)
      src := src.push { name := f.name, sem := semVar f.name, graph := f.name.toString, coh := w }
    else if isProofTarget b f.target then
      images := images.push (conjunct inv (conjunctIdx b c f))
    else
      binders := binders.push f.name.toString
      images := images.push f.name.toString
  let idxWf ← arityWf b i
  let tail := if b.wf then (idxWf.map (·.1)).push "_ir_w" else #[]
  return untypedLambda (binders ++ ihNames ++ tail) (app minorName (images ++ (if ihs then ihImages else #[])))

/-- `X.rec` is the graph's recursor at repacked motives and minor premises --
a kernel recursor application when Lean declared the graph block, which the
code generator does not compile -- so it is published beside a compiled
companion written out of the graph's `casesOn` and recursive calls, one
`mutual` of `unsafe` definitions per joint recursion, and wired up with
`implemented_by`; where the companion cannot be written, `X.rec` is
`noncomputable`. -/
private def emitRec (b : Block) : CommandElabM Unit := do
  let ps ← paramsDecl b
  let mut done : Array (Array Nat) := #[]
  for i in dataMembers b do
    let scope := scope b i
    if done.contains scope then continue
    done := done.push scope
    let common := ps ++ " " ++ (← motiveDecls b scope) ++ " " ++ (← minorDecls b true scope)
    -- the companions, one per member of the joint recursion, out of the
    -- graph's `casesOn` (major first) or `casesD` (major last), whichever it has
    let ns ← getCurrNamespace
    let mut impls := #[]
    let mut able := true
    for k in scope do
      let m := b.members[k]!
      let idx := pubIdxNames b k
      let major := if b.wf then #["_ir_self.1.1", "_ir_self.1.2"] else #["_ir_self.1", "_ir_self.2"]
      let extra := if b.wf then pubIdxWf b k idx ++ #["_ir_self.2"] else #[]
      let mut minors := #[]
      for ck in [:m.ctors.size] do
        minors := minors.push (← graphMinor b k ck (minor b k ck) true scope (impl := true))
      let cases ← if (← getEnv).contains (ns ++ (graphName m).toName ++ `casesOn) then
          pure (app ("@" ++ graphName m ++ ".casesOn") (pArgs b ++ #[← graphMotive b k] ++ pubPairIdx b k idx ++ major ++ minors ++ extra))
        else if (← getEnv).contains (ns ++ (graphName m).toName ++ `casesD) then
          pure (app ("@" ++ graphName m ++ ".casesD") (pArgs b ++ #[← graphMotive b k] ++ minors ++ pubPairIdx b k idx ++ major ++ extra))
        else
          able := false
          pure ""
      impls := impls.push ("unsafe def " ++ recImplName m ++ " " ++ common ++ " " ++ (← pubArity b k (implicit := true)) ++ " (_ir_self : " ++ typeAt b k idx ++ ") : " ++ app (motive k) (idx ++ #["_ir_self"]) ++ " := " ++ cases)
    let saved ← get
    let compiled ← if !able then pure false else try
        emit ("mutual\n" ++ String.intercalate "\n" impls.toList ++ "\nend")
        pure true
      catch e =>
        set saved
        trace[Mumi.ir] "no compiled companion for the recursors of {scope.map (b.members[·]!.name)}, which are noncomputable:\n{e.toMessageData}"
        pure false
    let mut gargs := pArgs b
    for k in scope do gargs := gargs.push (← graphMotive b k)
    for k in scope do
      for ck in [:b.members[k]!.ctors.size] do
        gargs := gargs.push (← graphMinor b k ck (minor b k ck) true scope)
    for k in scope do
      let m := b.members[k]!
      let idx := pubIdxNames b k
      let self := if b.wf then #["_ir_self.1.1", "_ir_self.1.2"] ++ pubIdxWf b k idx ++ #["_ir_self.2"] else #["_ir_self.1", "_ir_self.2"]
      let rest := m.name.toString ++ ".rec " ++ common ++ " " ++ (← pubArity b k (implicit := true)) ++ " (_ir_self : " ++ typeAt b k idx ++ ") : " ++ app (motive k) (idx ++ #["_ir_self"]) ++ " := " ++ app ("@" ++ graphName m ++ ".rec") (gargs ++ pubPairIdx b k idx ++ self)
      let attrs := if compiled then "@[implemented_by " ++ recImplName m ++ ", elab_as_elim] " else "@[elab_as_elim] "
      emitDef attrs rest

/-- The minor premise of a `Prop` member's recursor at constructor `ci`: the
constructor's name, which nothing else of the member's takes. -/
private def propMinor (b : Block) (i ci : Nat) : String := Id.run do
  let m := b.members[i]!
  let n := m.ctors[ci]!.name.toString
  let used := b.params.any (fun p => p.name.toString == n) ||
    m.ctors.any (fun c => c.fields.any (fun f => f.name.toString == n)) ||
    m.indices.any (fun x => x.name.toString == n)
  return if used then "_ir_case" ++ toString i ++ "_" ++ toString ci else n
/-- The motive of `Prop` member `j`: `motive` when it is the only one. -/
private def propMotive (b : Block) (j : Nat) : String :=
  if (propMembers b).size == 1 then "motive" else motive j

/-- The number of binders the well-formedness recursor's minor premise at a
data member's constructor takes: the graph fields, the well-formedness and
proof fields, and a hypothesis at each of the latter. -/
private def wfMinorArity (b : Block) (c : Ctor) : Nat :=
  c.fields.foldl (fun n f => n + (if (dataTarget b f).isSome then 4 else if isProofTarget b f.target then 2 else 1)) 0

/-- A `Prop` member's minor premise, public and as the well-formedness
recursor takes it: at `rec` with a hypothesis at each proof of a `Prop`
member, with `conclName` the motive the public one concludes at. -/
private def propMinorPair (b : Block) (j ci : Nat) (ihs : Bool) (conclName : String) : CommandElabM (String × String) := do
  let m := b.members[j]!
  let c := m.ctors[ci]!
  let mut hyps := #[]
  if ihs then
    for f in c.fields do
      if let some (k, _) := f.target then
        if b.members[k]!.prop then hyps := hyps.push (par (ihVar f.name ++ " : " ++ (← ihType f (some (propMotive b k)))))
  let result ← c.result.mapM text
  let concl := app conclName (result ++ #[ctorApp b j ci (fieldNames c)])
  let decls ← fieldsDecl c
  let ty := if c.fields.isEmpty then concl else "∀ " ++ decls ++ " " ++ join hyps ++ ", " ++ concl
  let pub := par (propMinor b j ci ++ " : " ++ ty)
  -- the graph minor's binders: the graph fields, the well-formedness of each
  -- field of carrier type, the proof fields, a hypothesis at each of the
  -- latter two, and the well-formedness of the arity
  let mut binders := #[]
  let mut images := #[]
  let mut wfs := #[]
  let mut props := #[]
  let mut ihBinders := #[]
  let mut ihImages := #[]
  let mut src : Array Source := #[]
  for f in c.fields do
    if (dataTarget b f).isSome then
      binders := binders.push (semVar f.name) |>.push f.name.toString
      let dom ← f.domain.mapM fun x => do return { x with type := ← semantic b src x.type }
      images := images.push (← lambda dom ("⟨⟨" ++ applyDomain (semVar f.name) dom ++ ", " ++ applyDomain f.name.toString dom ++ "⟩, " ++ applyDomain (wfVar f.name) dom ++ "⟩"))
      wfs := wfs.push (wfVar f.name)
      src := src.push { name := f.name, sem := semVar f.name, graph := f.name.toString, coh := wfVar f.name }
    else if let some (k, args) := f.target then
      props := props.push f.name.toString
      images := images.push f.name.toString
      if ihs then
        ihBinders := ihBinders.push (ihVar f.name)
        let dom ← f.domain.mapM fun x => do return { x with type := ← semantic b src x.type }
        let mut ws := #[]
        for (x, t) in b.members[k]!.indices.zip args do
          if let some (jj, _) := x.member then ws := ws.push (← pair b src (some jj) t).2.2
        ihImages := ihImages.push (← lambda dom (applyTo (applyDomain (ihVar f.name) dom) ws))
    else
      binders := binders.push f.name.toString
      images := images.push f.name.toString
  let wfIhs := if ihs then wfs.map fun _ => "_" else #[]
  let tail := (← arityWf b j).map (·.1)
  let g := untypedLambda (binders ++ wfs ++ props ++ wfIhs ++ ihBinders ++ tail) (app (propMinor b j ci) (images ++ (if ihs then ihImages else #[])))
  return (pub, g)

/-- The `Prop` members' recursors and `casesOn`, from the well-formedness
block's: `rec` joint over the `Prop` members, with a hypothesis at each proof
of one, the data members' predicates at `True`; `casesOn` with one motive. -/
private def emitPropRec (b : Block) : CommandElabM Unit := do
  let ps ← paramsDecl b
  let props := propMembers b
  let mut motives := #[]
  for j in props do
    motives := motives.push ("{" ++ propMotive b j ++ " : ∀ " ++ (← pubArity b j) ++ " (_ir_self : " ++ typeAt b j (pubIdxNames b j) ++ "), Prop}")
  let mut gargs := pArgs b
  for k in dataMembers b ++ props do
    if b.members[k]!.prop then
      let hyps := (← arityWf b k).map fun (n, t) => par (n ++ " : " ++ t)
      let value := app (propMotive b k) (repackIdx b k ++ #["_ir_h"])
      gargs := gargs.push (untypedLambda (graphIdxNames b k ++ #["_ir_h"]) (if hyps.isEmpty then value else "∀ " ++ join hyps ++ ", " ++ value))
    else
      gargs := gargs.push (untypedLambda (graphIdxNames b k ++ #["_ir_s", "_ir_a", "_ir_w"]) "True")
  let mut minors := #[]
  for k in dataMembers b ++ props do
    for ck in [:b.members[k]!.ctors.size] do
      if b.members[k]!.prop then
        let (pub, g) ← propMinorPair b k ck true (propMotive b k)
        minors := minors.push pub
        gargs := gargs.push g
      else
        gargs := gargs.push (untypedLambda ((Array.range (wfMinorArity b b.members[k]!.ctors[ck]!)).map fun _ => "_") "trivial")
  for j in props do
    let m := b.members[j]!
    let idx := pubIdxNames b j
    let attrs := if props.size == 1 then "@[elab_as_elim, induction_eliminator] " else "@[elab_as_elim] "
    emit (attrs ++ "theorem " ++ m.name.toString ++ ".rec " ++ ps ++ " " ++ join motives ++ " " ++ join minors ++ " " ++ (← pubArity b j (implicit := true)) ++ " (_ir_self : " ++ typeAt b j idx ++ ") : " ++ app (propMotive b j) (idx ++ #["_ir_self"]) ++ " := " ++ app ("@" ++ wfName m ++ ".rec") (gargs ++ pubPairIdx b j idx ++ #["_ir_self"] ++ pubIdxWf b j idx))
    -- `casesOn`: the member's own constructors, no hypotheses
    let mot := "{motive : ∀ " ++ (← pubArity b j) ++ " (_ir_self : " ++ typeAt b j idx ++ "), Prop}"
    let hyps := (← arityWf b j).map fun (n, t) => par (n ++ " : " ++ t)
    let value := app "motive" (repackIdx b j ++ #["_ir_h"])
    let gmotive := untypedLambda (graphIdxNames b j ++ #["_ir_h"]) (if hyps.isEmpty then value else "∀ " ++ join hyps ++ ", " ++ value)
    let mut cminors := #[]
    let mut cgminors := #[]
    for ci in [:m.ctors.size] do
      let (pub, g) ← propMinorPair b j ci false "motive"
      cminors := cminors.push pub
      cgminors := cgminors.push g
    emit ("@[elab_as_elim, cases_eliminator] theorem " ++ m.name.toString ++ ".casesOn " ++ ps ++ " " ++ mot ++ " " ++ join cminors ++ " " ++ (← pubArity b j (implicit := true)) ++ " (_ir_self : " ++ typeAt b j idx ++ ") : " ++ app "motive" (idx ++ #["_ir_self"]) ++ " := " ++ app ("@" ++ wfName m ++ ".casesOn") (pArgs b ++ #[gmotive] ++ pubPairIdx b j idx ++ #["_ir_self"] ++ cgminors ++ pubIdxWf b j idx))

/-- An equation that is `rfl` where the encoding reduces.  One universe up it
is stated as a theorem and elaborated as any other.  At the universe the block
is written at, Meta's unifier is handed only the statement: the proof `Eq.refl`
goes straight to the kernel.  The two sides of such an equation are small as
shared graphs but astronomically large as trees -- a stage embeds the arguments
it bounds, a decode embeds the stage, an index embeds decodes, a transport
embeds indices, and so on down the block's dependency chain -- and the unifier
walks a bound variable's type without sharing (`getFunInfo`'s dependency scan)
once per variable it introduces, which takes a minute each for a block of any
depth; the kernel's definitional check is cached on the shared graph and takes
milliseconds.  An equation the kernel rejects -- a constructor whose conclusion
nests a constructor inside another -- is skipped and reported, rather than
failing the block. -/
private def emitEquation (b : Block) (name binders stmt : String) : CommandElabM Unit := do
  unless b.lower do
    return ← emit ("@[simp] theorem " ++ name ++ " " ++ binders ++ " : " ++ stmt ++ " := rfl")
  let text := if binders.trim.isEmpty then stmt else "∀ " ++ binders ++ ", " ++ stmt
  unless mumi.ir.equations.get (← getOptions) do
    trace[Mumi.ir] "not tried, `mumi.ir.equations` is off:\n{name} : {text}"
    return
  trace[Mumi.ir] "kernel rfl: {name} : {text}"
  let stx ← match Parser.runParserCategory (← getEnv) `term text with
    | .ok t => pure t
    | .error e => throwError "IR frontend generated an invalid statement:\n{text}\n{e}"
  let declName := (← getCurrNamespace) ++ name.toName
  let levelNames := (← getScope).levelNames
  let saved ← get
  try
    liftTermElabM do
      let ty ← Term.elabType stx
      Term.synthesizeSyntheticMVarsNoPostponing
      let ty ← instantiateMVars ty
      let val ← Meta.forallTelescope ty fun xs body => do
        let some (_, lhs, _) := body.eq? | throwError "not an equation"
        Meta.mkLambdaFVars xs (← Meta.mkEqRefl lhs)
      let lps ← match sortDeclLevelParams levelNames [] (collectLevelParams {} ty).params with
        | .ok lps => pure lps
        | .error e => throwError e
      addDecl (.thmDecl { name := declName, levelParams := lps, type := ty, value := val })
    emit ("attribute [simp] " ++ declName.toString)
  catch e =>
    set saved
    trace[Mumi.ir] "not definitional here, skipped:\n{name} : {text}\n{e.toMessageData}"

private def emitEquations (b : Block) : CommandElabM Unit := do
  let ps ← paramsDecl b
  for j in [:b.decoders.size] do
    let d := b.decoders[j]!
    for ci in [:b.members[d.target]!.ctors.size] do
      let c := b.members[d.target]!.ctors[ci]!
      let result ← c.result.mapM text
      emitEquation b (d.name.toString ++ "_" ++ c.name.toString) (ps ++ " " ++ (← fieldsDecl c)) (withParams b d.name.toString (result ++ #[ctorApp b d.target ci (fieldNames c)]) ++ " = " ++ par (← text d.clauses[ci]!))
  for i in dataMembers b do
    let scope := scope b i
    let common := ps ++ " " ++ (← motiveDecls b scope) ++ " " ++ (← minorDecls b true scope)
    let args := pArgs b ++ motiveArgs b scope ++ minorArgs b scope
    for ci in [:b.members[i]!.ctors.size] do
      let c := b.members[i]!.ctors[ci]!
      let mut ihs := #[]
      for f in c.fields do
        if let some (j, idx) := scopedTarget b scope f then
          let idx ← idx.mapM text
          ihs := ihs.push (← lambda f.domain (app ("@" ++ b.members[j]!.name.toString ++ ".rec") (args ++ idx ++ #[applyDomain f.name.toString f.domain])))
      let result ← c.result.mapM text
      emitEquation b (b.members[i]!.name.toString ++ ".rec_" ++ c.name.toString) (common ++ " " ++ (← fieldsDecl c)) (app ("@" ++ b.members[i]!.name.toString ++ ".rec") (args ++ result ++ #[ctorApp b i ci (fieldNames c)]) ++ " = " ++ app (minor b i ci) (fieldNames c ++ ihs))
    let m := b.members[i]!
    let idx := pubIdxNames b i
    emitDef "@[elab_as_elim] " (m.name.toString ++ ".recOn " ++ ps ++ " " ++ (← motiveDecls b scope) ++ " " ++ (← pubArity b i (implicit := true)) ++ " (_ir_self : " ++ typeAt b i idx ++ ") " ++ (← minorDecls b true scope) ++ " : " ++ app (motive i) (idx ++ #["_ir_self"]) ++ " := " ++ app ("@" ++ m.name.toString ++ ".rec") (args ++ idx ++ #["_ir_self"]))

/-- The minor premises of a one-motive eliminator for carrier `i`: with the
hypotheses at its own fields when `ihs`, none otherwise. -/
private def soloMinors (b : Block) (i : Nat) (ihs : Bool) : CommandElabM (Array String) := do
  let m := b.members[i]!
  let mut minors := #[]
  for ci in [:m.ctors.size] do
    let c := m.ctors[ci]!
    let mut hyps := #[]
    if ihs then
      for f in c.fields do
        if (dataTarget b f).any (·.1 == i) then
          hyps := hyps.push (par (ihVar f.name ++ " : " ++ (← ihType f (some "motive"))))
    let result ← c.result.mapM text
    let concl := app "motive" (result ++ #[ctorApp b i ci (fieldNames c)])
    let decls ← fieldsDecl c
    let ty := if c.fields.isEmpty then concl else "∀ " ++ decls ++ " " ++ join hyps ++ ", " ++ concl
    minors := minors.push (par (minor b i ci ++ " : " ++ ty))
  return minors

/-- The recursor's arguments for a one-motive eliminator of carrier `i`: `motive`
there and `PUnit` everywhere else, with the minor premises to match. -/
private def soloArgs (b : Block) (i : Nat) (ihs : Bool) : Array String := Id.run do
  let scope := scope b i
  let mut args := pArgs b
  for k in scope do
    args := args.push (if k == i then "motive" else
      untypedLambda ((Array.range (b.members[k]!.indices.size + 1)).map fun _ => "_") "PUnit")
  for k in scope do
    for ck in [:b.members[k]!.ctors.size] do
      let c := b.members[k]!.ctors[ck]!
      let recursive := c.fields.filter fun f => (scopedTarget b scope f).isSome
      if k == i then
        let own := recursive.filter fun f => (dataTarget b f).any (·.1 == i)
        let binders := fieldNames c ++ recursive.map (ihVar ·.name)
        args := args.push (untypedLambda binders (app (minor b i ck) (fieldNames c ++ (if ihs then own.map (ihVar ·.name) else #[]))))
      else
        args := args.push (untypedLambda ((Array.range (c.fields.size + recursive.size)).map fun _ => "_") "PUnit.unit")
  return args

/-- `recD`, `casesOn` and `cases`: one motive, the others at `PUnit`.  `recD` is
what `induction` uses and `casesOn` what `cases` uses; the joint `rec` asks for
every motive and is for `induction … using`. -/
private def emitSolo (b : Block) : CommandElabM Unit := do
  let ps ← paramsDecl b
  for i in dataMembers b do
    let m := b.members[i]!
    let idx := pubIdxNames b i
    let mot := "{motive : " ++ (← motiveType b i) ++ "}"
    let arity ← pubArity b i (implicit := true)
    let self := "(_ir_self : " ++ typeAt b i idx ++ ")"
    let concl := app "motive" (idx ++ #["_ir_self"])
    let recD ← soloMinors b i true
    let recDRest := m.name.toString ++ ".recD " ++ ps ++ " " ++ mot ++ " " ++ arity ++ " " ++ self ++ " " ++ join recD ++ " : " ++ concl ++ " := " ++ app ("@" ++ m.name.toString ++ ".rec") (soloArgs b i true ++ idx ++ #["_ir_self"])
    emitFirst #["@[elab_as_elim, induction_eliminator] def " ++ recDRest,
      "@[elab_as_elim, induction_eliminator] noncomputable def " ++ recDRest,
      "@[elab_as_elim] def " ++ recDRest, "@[elab_as_elim] noncomputable def " ++ recDRest]
    let minors ← soloMinors b i false
    let minorNames := (Array.range m.ctors.size).map (minor b i)
    let casesRest := m.name.toString ++ ".casesOn " ++ ps ++ " " ++ mot ++ " " ++ arity ++ " " ++ self ++ " " ++ join minors ++ " : " ++ concl ++ " := " ++ app ("@" ++ m.name.toString ++ ".rec") (soloArgs b i false ++ idx ++ #["_ir_self"])
    emitFirst #["@[elab_as_elim, cases_eliminator] def " ++ casesRest,
      "@[elab_as_elim, cases_eliminator] noncomputable def " ++ casesRest,
      "@[elab_as_elim] def " ++ casesRest, "@[elab_as_elim] noncomputable def " ++ casesRest]
    emitDef "@[elab_as_elim] " (m.name.toString ++ ".cases " ++ ps ++ " " ++ mot ++ " " ++ join minors ++ " " ++ arity ++ " " ++ self ++ " : " ++ concl ++ " := " ++ app ("@" ++ m.name.toString ++ ".casesOn") (pArgs b ++ #["motive"] ++ idx ++ #["_ir_self"] ++ minorNames))
    for ci in [:m.ctors.size] do
      let c := m.ctors[ci]!
      let result ← c.result.mapM text
      emitEquation b (m.name.toString ++ ".casesOn_" ++ c.name.toString) (ps ++ " " ++ mot ++ " " ++ join minors ++ " " ++ (← fieldsDecl c)) (app ("@" ++ m.name.toString ++ ".casesOn") (pArgs b ++ #["motive"] ++ result ++ #[ctorApp b i ci (fieldNames c)] ++ minorNames) ++ " = " ++ app (minor b i ci) (fieldNames c))

/-! ## Lower mode: the carrier at `Type u`

Under `mumi.mahlo true` the carriers stay at the universe they were written at,
on the same stage engine and reflection axiom as the unindexed frontend
(`Mumi/IR/Mahlo.lean`).  A sort has to live in `Type u`, so a raw carrier
cannot be indexed by another carrier's semantics; every raw carrier is
unindexed, and each decoder output *records* the index semantics it is at:

```lean
structure _ir_Ty_I : Type (u+1) where            -- the semantic halves of the arity
  _ir_sem_Γ : _ir_Ctx_Sem
structure _ir_Ty_D : Type (u+1) where            -- what a raw `Ty` decodes to
  _ir_at : _ir_Ty_I
  _ir_val : _ir_Ty_Sem _ir_at._ir_sem_Γ
```

A recursive field of carrier type is followed in the description by a
*coherence* proof that its decode is at the semantics of the index it was
written at, and the field's semantics is transported along it (`_ir_Ty_tr`).
The certificates `_ir_X_Good` are indexed by the raw halves of the indices and
by the same coherence proofs, and the public carrier is the subtype.  A decoder
transports along the coherence its certificate yields, so at a constructor the
transport is along an equation whose sides are definitionally equal and
`Eq.rec` reduces: every decoder equation and iota rule is `rfl`.

The recursion is `Mumi.IR.induction` at a motive quantifying over the raw
indices and the certificate.  The step reads the constructor's arguments, the
certificate's shape gives the node, the indices and the sub-certificates as
equations, and `_ir_X_cast` transports the minor premise across all of them at
once, which `Eq.rec` again reduces at a constructor.

Two things keep the reduction tractable.  Every semantic value a constructor
computes, and every level of a constructor's description, is its own named
definition, so `whnf` instantiates a small application instead of copying a
continuation; and every coherence is stated at the semantic *expression* of the
index it is about, never at the decode of a rolled raw term.

A `Prop` member is here what it is one universe up, a certificate: the raw
terms carry no proof of one, a data member's certificate constructor takes
each proof where it was written, as a proof of the `Prop` member's
certificate `_ir_P_Good` over the raw halves of its indices, which is in the
one `mutual` with the others, and the shape of a certificate yields the proofs
beside the fields' certificates.  `P.rec` is the certificates' joint recursor
at `True` for the data members, closed by tactic since it is a proof.

A sort lives in one `Type u`, so carriers in different universes are on
different stage engines: one per universe (`Block.groups`), in an order every
carrier's fields and indices of carrier type come before it, which their
universes guarantee.  To a later engine a carrier of an earlier one is a value
of a type already declared: a plain field of the description, boxed, with
the box of its coherence beside it when that carrier is indexed, its
semantics read off its decode; its certificate is demanded by the later
member's as a field's of the same engine is, so the public value is rebuilt
in the minor premises, but the recursion gives no hypothesis at it.  The
certificates of every member are one `mutual` after every engine, which is
what lets a `Prop` tie the universes together. -/

private def semAt (b : Block) (k : Nat) (idx : Array String) := withParams b (semName b.members[k]!) idx
private def rawAt (b : Block) (k : Nat) := atParams b (rawName b.members[k]!)
private def decAt (b : Block) (k : Nat) (a : String) := par (withParams b (decName b.members[k]!) #[a])
private def iAt (b : Block) (k : Nat) := atParams b (iName b.members[k]!)
private def trAt (b : Block) (k : Nat) (h v : String) := withParams b (trName b.members[k]!) #[h, v]
/-- Every command of this mode is emitted under a deeper recursion limit. -/
private def emitL (s : String) : CommandElabM Unit := emit ("set_option maxRecDepth 8000 in\n" ++ s)
private def emitDefL (attrs rest : String) : CommandElabM Unit :=
  emitFirst #["set_option maxRecDepth 8000 in\n" ++ attrs ++ "def " ++ rest,
    "set_option maxRecDepth 8000 in\n" ++ attrs ++ "noncomputable def " ++ rest]

private def packedType (b : Block) (g : Nat) (dom : Array Binder) : CommandElabM String := do
  let mut t := "PUnit.{1}"
  for x in dom.reverse do t := par (par (x.name.toString ++ " : " ++ (← text x.type)) ++ " ×' " ++ t)
  return "ULift.{" ++ glevel b g ++ "} " ++ par t
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
/-- `.1`, `.2.1`, … into a right-nested conjunction. -/
private def conj (n : Nat) : String := String.join ((List.replicate n ".2")) ++ ".1"
/-- `⟨x₁, …, xₙ⟩ : _ir_X_I params`, as the `I` record of carrier `k`. -/
private def iMk (b : Block) (k : Nat) (xs : Array String) : String :=
  par ("⟨" ++ String.intercalate ", " xs.toList ++ "⟩ : " ++ iAt b k)
/-- The domain of a field with its binder types read in the world of `src`. -/
private def domIn (b : Block) (src : Array Source) (f : Field) : CommandElabM (Array Binder) :=
  f.domain.mapM fun x => do return { x with type := ← semantic b src x.type }

/-- The semantic value of index argument term `t` of carrier `j`, and for one of
carrier type the raw half and the coherence it comes with. -/
private def triple (b : Block) (src : Array Source) (j : Nat) (t : Syntax) : CommandElabM (String × String × String) :=
  pair b src (some j) t
/-- The arguments a certificate of carrier `k` takes at index arguments `args`:
the raw half, then the coherence when that carrier is indexed, for an index of
carrier type; the value for a plain one. -/
private def goodIdx (b : Block) (src : Array Source) (k : Nat) (args : Array Syntax) : CommandElabM (Array String) := do
  let mut out := #[]
  for (x, t) in b.members[k]!.indices.zip args do
    if let some (j, _) := x.member then
      let (_, r, c) ← triple b src j t
      out := out.push r
      if indexed b j then out := out.push c
    else out := out.push (← semText b src t)
  return out

/-- A public index term of carrier `expect` as text, with a constructor written
`.c` given its full name, recursively into its arguments, so that the term can
be read where no expected type resolves the dot -- under `.val`, say. -/
private partial def qualifyText (b : Block) (expect : Option Nat) (s : Syntax) : CommandElabM String := do
  let (h, args) := unapp s
  let some (k, ci) := ctorRef? b expect h | text s
  let m := b.members[k]!
  let c := m.ctors[ci]!
  -- the dotted form carries no parameters; the qualified one carries them all
  let fargs := if h.isOfKind ``Parser.Term.dotIdent then args else args.extract b.params.size args.size
  unless fargs.size == c.fields.size do return ← text s
  let mut out := #[]
  for (f, a) in c.fields.zip fargs do
    out := out.push (← qualifyText b (f.target.map (·.1)) a)
  return withParams b (m.name.toString ++ "." ++ c.name.toString) out

/-- The arity of carrier `k` in the raw world: the raw half of an index of
carrier type with, when that carrier is indexed, its coherence; and the sources
they bind, whose semantic halves are transported along those coherences. -/
private def rawArity (b : Block) (k : Nat) : CommandElabM (Array String × Array Source) := do
  let mut out := #[]
  let mut src : Array Source := #[]
  -- every index is bound under a name of its own, so that a field of the same
  -- name can be bound beside it
  let mut pairs : Array (Name × Syntax) := #[]
  for x in b.members[k]!.indices do
    let n := "_ir_idx_" ++ x.name.toString
    if let some (j, args) := x.member then
      let args := args.map (subst · pairs)
      out := out.push (par (n ++ " : " ++ rawAt b j))
      if indexed b j then
        let sIdx ← semIdx b src j args
        out := out.push (par (cohVar x.name ++ " : " ++ decAt b j n ++ "._ir_at = " ++ iMk b j sIdx))
        src := src.push { name := x.name, sem := par (trAt b j (cohVar x.name) (decAt b j n ++ "._ir_val")), graph := n, coh := cohVar x.name }
      else
        src := src.push { name := x.name, sem := par (decAt b j n ++ "._ir_val"), graph := n }
    else
      out := out.push (par (n ++ " : " ++ (← semText b src (subst x.type pairs))))
      pairs := pairs.push (x.name, mkIdent (Name.mkSimple n))
  return (out, src)
/-- The names `rawArity` binds, in order. -/
private def rawArityNames (b : Block) (k : Nat) : Array String :=
  b.members[k]!.indices.flatMap fun x =>
    let n := "_ir_idx_" ++ x.name.toString
    match x.member with
    | some (j, _) => if indexed b j then #[n, cohVar x.name] else #[n]
    | none => #[n]
/-- The `I` record of carrier `k` at the sources `rawArity` binds. -/
private def iOfArity (b : Block) (k : Nat) (src : Array Source) : String :=
  iMk b k (b.members[k]!.indices.map fun x =>
    if x.member.isSome then (src.find? (·.name == x.name)).map (·.sem) |>.getD x.name.toString
    else "_ir_idx_" ++ x.name.toString)

/-- The arity of carrier `k` at public values: per index of carrier type the
raw half `_ir_idx_x` and its certificate `_ir_hx_x`, each with its type, from
which the public value `⟨x, hx⟩` and the coherence are made, and a plain index
under a name of its own; the public index terms over those names; and the
certificate's index arguments over them. -/
private def pubTele (b : Block) (k : Nat) : CommandElabM (Array (String × String) × Array String × Array String) := do
  let mut comps : Array (String × String) := #[]
  let mut pub := #[]
  let mut good := #[]
  let mut pairs : Array (Name × Syntax) := #[]
  for x in b.members[k]!.indices do
    -- the raw index gets a name of its own, so that a field of the same name
    -- can be bound beside it
    let n := "_ir_idx_" ++ x.name.toString
    if let some (j, args) := x.member then
      let hx := "_ir_hx_" ++ x.name.toString
      -- the certificate of `x` is at the public readings of its own indices
      let gargs ← goodIdxPub b j (args.map (subst · pairs))
      comps := comps.push (n, rawAt b j)
      comps := comps.push (hx, withParams b (goodName b.members[j]!) (gargs ++ #[n]))
      let p := par ("⟨" ++ n ++ ", " ++ hx ++ "⟩ : " ++ typeAt b j (← (args.map (subst · pairs)).mapM text))
      pub := pub.push p
      good := good.push n
      if indexed b j then good := good.push (par (withParams b (goodName b.members[j]! ++ ".coh") #[hx, "rfl"]))
      pairs := pairs.push (x.name, ← parseTerm p)
    else
      comps := comps.push (n, ← text (subst x.type pairs))
      pub := pub.push n
      good := good.push n
      pairs := pairs.push (x.name, mkIdent (Name.mkSimple n))
  return (comps, pub, good)
where
  /-- The certificate's index arguments at public terms: `.val`, the coherence
  from `.property`, or the plain value. -/
  goodIdxPub (b : Block) (j : Nat) (args : Array Syntax) : CommandElabM (Array String) := do
    let mut out := #[]
    for (y, t) in b.members[j]!.indices.zip args do
      if let some (i, _) := y.member then
        let t ← qualifyText b (some i) t
        out := out.push (par t ++ ".val")
        if indexed b i then out := out.push (par (withParams b (goodName b.members[i]! ++ ".coh") #[par t ++ ".property", "rfl"]))
      else out := out.push (← text t)
    return out

/-- The arity of carrier `k` as a motive sees it, packed into one `PSigma` of
`Type u` so that every carrier's arm of the motive lands in the same sort.
Returns the packed type, the names each component is read under with its
projection out of `_ir_p`, the public index terms and the certificate's index
arguments, both over those names. -/
private def motiveTele (b : Block) (k : Nat) : CommandElabM (String × Array (String × String) × Array String × Array String) := do
  let (comps, pub, good) ← pubTele b k
  -- the packed type, right-nested, with the components' names in scope for later ones
  let mut packed := "PUnit.{" ++ glevel b (groupOf b k) ++ "+1}"
  for (n, t) in comps.reverse do packed := par ("(" ++ n ++ " : " ++ t ++ ") ×' " ++ packed)
  let mut proj := #[]
  for i in [:comps.size] do
    proj := proj.push (comps[i]!.1, "_ir_p" ++ String.join (List.replicate i ".2") ++ ".1")
  return (packed, proj, pub, good)

/-- `s` with each packed component's name read as its projection. -/
private def atProj (proj : Array (String × String)) (s : String) : String := Id.run do
  let mut s := s
  -- longer names first, so that a name is never replaced inside another
  for (n, p) in proj.qsort (fun a b => a.1.length > b.1.length) do
    s := s.replace n p
  return s
/-- The packed components, as a value. -/
private def packTuple (xs : Array String) : String :=
  if xs.isEmpty then "PUnit.unit" else "⟨" ++ String.intercalate ", " (xs.toList ++ ["PUnit.unit"]) ++ "⟩"
/-- The `let`s that bind the packed components under their names. -/
private def projLets (proj : Array (String × String)) : String :=
  String.join (proj.toList.map fun (n, p) => "let " ++ n ++ " := " ++ p ++ "\n  ")

/-- The certificate's index arguments at public terms. -/
private def goodIdxPub (b : Block) (j : Nat) (args : Array Syntax) : CommandElabM (Array String) :=
  pubTele.goodIdxPub b j args

/-- The fields of `c` the raw term carries: every one but a proof of a `Prop`
member, which is the certificate's. -/
private def lowerFields (b : Block) (c : Ctor) : Array Field :=
  c.lowerOf.fields.filter fun f => !isProofTarget b f.target

/-! ### The description -/

/-! ### Constructors nested in index terms

At the written universe the decode of a constructor application nested inside
another does not reduce -- a node's field is decoded through the stage
engine's uniform accessibility proof, which is opaque -- so every raw index
term has to apply a constructor to fields only.  The lower view of a
constructor names each nested application by a hidden field: a raw field the
public constructor supplies with the application itself, and the certificate
pins to it rather than binding.  Both sides of every coherence then carry the
sub-node unreduced, and everything stays definitional. -/

mutual

/-- An index term of carrier `expect`: a constructor application has its
arguments of carrier type flattened, and when that named any, a conclusion's
(`conclusion`) becomes a hidden field itself; anything else stays. -/
private partial def flattenTop (b : Block) (expect : Option Nat) (conclusion : Bool) (dom : Array Binder) (t : Syntax) :
    StateT (Array Field) CommandElabM Syntax := do
  let (h, args) := unapp t
  let some (k, ci) := ctorRef? b expect h | return t
  let c := b.members[k]!.ctors[ci]!
  unless args.size == b.params.size + c.fields.size do return t
  let before := (← get).size
  let mut out := args.extract 0 b.params.size
  for (f, a) in c.fields.zip (args.extract b.params.size args.size) do
    out := out.push (← match f.target with
      | some (j, _) => flattenArg b (some j) dom a
      | none => pure a)
  let texts ← (out.mapM text : CommandElabM (Array String))
  let t ← parseTerm (app (← text h) texts)
  if conclusion && (← get).size > before then hide b k c out dom t (arg := false) else return t

/-- An argument of carrier `expect`: a constructor application becomes a hidden
field. -/
private partial def flattenArg (b : Block) (expect : Option Nat) (dom : Array Binder) (a : Syntax) :
    StateT (Array Field) CommandElabM Syntax := do
  if (ctorRef? b expect (unapp a).1).isNone then return a
  let t ← flattenTop b expect false dom a
  let (h, args) := unapp t
  let some (k, ci) := ctorRef? b expect h | return a
  hide b k b.members[k]!.ctors[ci]! args dom t (arg := true)

/-- A hidden field for the application `t` of constructor `c` of carrier `k`
to `args`, at the indices `c`'s conclusion has there. -/
private partial def hide (b : Block) (k : Nat) (c : Ctor) (args : Array Syntax) (dom : Array Binder) (t : Syntax) (arg : Bool) :
    StateT (Array Field) CommandElabM Syntax := do
  let pairs := (c.fields.zip (args.extract b.params.size args.size)).map fun (f, x) => (f.name, x)
  let idx ← ((b.members[k]!.indices.zip c.result).map fun (x, r) => (x.member.map (·.1), subst r pairs)).mapM
    fun (e, r) => flattenTop b e false dom r
  let name := Name.mkSimple ("_ir_sub_" ++ toString (← get).size)
  let idxTexts ← (idx.mapM text : CommandElabM (Array String))
  let type ← parseTerm (← forallS dom (typeAt b k idxTexts))
  modify (·.push { name, type, target := some (k, idx), domain := dom, value := some t, hiddenArg := arg })
  parseTerm (applyDomain name.toString dom)

end

/-- The lower view of `c`: each hidden field just before the field whose index
term names it, and those of the conclusion last. -/
private def flattenCtor (b : Block) (m : Member) (c : Ctor) : CommandElabM Ctor := do
  let mut hidden : Array Field := #[]
  let mut fields : Array Field := #[]
  for f in c.fields do
    if let some (j, args) := f.target then
      let before := hidden.size
      let expects := b.members[j]!.indices.map (·.member.map (·.1))
      let (args, hidden') ← ((args.zip expects).mapM fun (a, e) => flattenTop b e false f.domain a).run hidden
      hidden := hidden'
      fields := fields ++ hidden.extract before hidden.size
      fields := fields.push { f with target := some (j, args) }
    else fields := fields.push f
  let before := hidden.size
  let expects := m.indices.map (·.member.map (·.1))
  let (result, hidden') ← ((c.result.zip expects).mapM fun (r, e) => flattenTop b e true #[] r).run hidden
  hidden := hidden'
  fields := fields ++ hidden.extract before hidden.size
  if hidden.isEmpty then return c
  return { c with lower := some (fields, result) }

private def flattenLower (b : Block) : CommandElabM Block := do
  let members ← b.members.mapM fun m => do
    return { m with ctors := ← m.ctors.mapM (flattenCtor b m) }
  return { b with members }

/-- A hidden field as a source: the halves of its value at the sources so far. -/
private def hiddenSource (b : Block) (src : Array Source) (f : Field) : CommandElabM Source := do
  let some (j, _) := f.target | throwError "a hidden field is of carrier type"
  let some v := f.value | throwError "a hidden field has a value"
  let dom ← domIn b src f
  let (sem, graph, coh) ← pair b src (some j) v
  let sem ← lambda dom sem
  let graph ← lambda dom graph
  let coh ← if coh.isEmpty then pure "" else lambda dom coh
  return { name := f.name, sem, graph, coh }

/-- The sources the fields before `upto` of `c` bind in the description world,
and their binders: a recursive field is its (transported) semantics, a plain
one its value. -/
private def descSources (b : Block) (c : Ctor) (upto : Nat) : CommandElabM (Array Source × Array String) := do
  let mut src : Array Source := #[]
  let mut binders := #[]
  for f in (lowerFields b c).extract 0 upto do
    if f.hiddenArg then
      -- an argument's semantics is its value's: what is typed at it needs that
      src := src.push { ← hiddenSource b src f with graph := "", coh := "" }
      continue
    if let some (j, args) := f.target then
      let dom ← domIn b src f
      let sIdx ← semIdx b src j args
      binders := binders.push (par (semVar f.name ++ " : " ++ (← forallS dom (semAt b j sIdx))))
      src := src.push { name := f.name, sem := semVar f.name, graph := "", coh := "" }
    else
      binders := binders.push (par (f.name.toString ++ " : " ++ (← semText b src f.type)))
  return (src, binders)
private def descNames (b : Block) (c : Ctor) (upto : Nat) : Array String :=
  (((lowerFields b c).extract 0 upto).filter (!·.hiddenArg)).map fun f => if f.target.isSome then semVar f.name else f.name.toString

private def emitLowerSemantics (b : Block) (order : Array (Sum Nat Nat)) : CommandElabM Unit := do
  let ps ← paramsDecl b
  for o in order do
    let .inl k := o | continue
    let m := b.members[k]!
    if m.prop then continue
    let (arity, _) ← semArity b k
    emitL ("structure " ++ iName m ++ " " ++ ps ++ " : Type (" ++ m.level ++ "+1) where\n" ++
      String.intercalate "\n" (arity.toList.map ("  " ++ ·)))
    let at_ := semIdxNames b k |>.map ("_ir_at." ++ ·)
    emitL ("structure " ++ dName m ++ " " ++ ps ++ " : Type (" ++ m.level ++ "+1) where\n  _ir_at : " ++ iAt b k ++ "\n  _ir_val : " ++ semAt b k at_)
    if indexed b k then
      let atI := semIdxNames b k |>.map ("_ir_i." ++ ·)
      let atJ := semIdxNames b k |>.map ("_ir_j." ++ ·)
      emitL ("def " ++ trName m ++ " " ++ ps ++ " {_ir_i _ir_j : " ++ iAt b k ++ "} (_ir_h : _ir_i = _ir_j) (_ir_v : " ++ semAt b k atI ++ ") : " ++ semAt b k atJ ++ " := @Eq.rec " ++ par (iAt b k) ++ " _ir_i (fun _ir_j _ => " ++ semAt b k atJ ++ ") _ir_v _ir_j _ir_h")
  -- one semantic value per constructor
  for k in dataMembers b do
    let m := b.members[k]!
    for ci in [:m.ctors.size] do
      let c := m.ctors[ci]!.lowerOf
      let (src, binders) ← descSources b c (lowerFields b c).size
      let sIdx ← semIdx b src k c.result
      let vals ← ctorVals b src k ci #[]
      emitL ("def " ++ pieceName m c ++ " " ++ ps ++ " " ++ join binders ++ " : " ++ atParams b (dName m) ++ " := ⟨" ++ iMk b k sIdx ++ ", " ++ app ("@" ++ semName m ++ ".mk") (pArgs b ++ sIdx ++ vals) ++ "⟩")

/-- Level `i` of the description of `X.c`: field `i` and what follows.  A
field of a carrier of another engine is a plain field -- a value of a type
already declared -- with, when that carrier is indexed, its coherence beside
it; what follows reads its semantics off its decode. -/
private def emitContinuations (b : Block) (g : Nat) : CommandElabM Unit := do
  let ps ← paramsDecl b
  let lvl := glevel b g
  for k in b.groups[g]! do
    let m := b.members[k]!
    for c in m.ctors do
      let c := c.lowerOf
      let fs := lowerFields b c
      for i in (List.range (fs.size + 1)).reverse do
        let (src, binders) ← descSources b c i
        let ty := "Mumi.IR.Desc " ++ atParams b (famName b g) ++ " " ++ sortValue b k
        let earlier := descNames b c i
        let body ←
          if i == fs.size then
            pure (".ret " ++ withParams b (pieceName m c) earlier)
          else
            let f := fs[i]!
            let next (x : String) :=
              if f.hiddenArg then withParams b (contName m c (i+1)) earlier
              else withParams b (contName m c (i+1)) (earlier ++ #[x])
            if let some (j, args) := f.target then
              let dom ← domIn b src f
              if foreign b k j then
                let box := boxVar f.name
                let value := applyDomain (box ++ ".down.1") dom
                let rawTy ← forallS dom (rawAt b j)
                if indexed b j then
                  let sIdx ← semIdx b src j args
                  let stmt ← forallS dom (decAt b j value ++ "._ir_at = " ++ iMk b j sIdx)
                  let sem ← lambda dom (trAt b j (applyDomain (cohboxVar f.name ++ ".down.1") dom) (decAt b j value ++ "._ir_val"))
                  pure (".sigma (ULift.{" ++ lvl ++ "} ((_ : " ++ rawTy ++ ") ×' PUnit.{1})) (fun " ++ box ++ " => .sigma (ULift.{" ++ lvl ++ "} ((_ : " ++ stmt ++ ") ×' PUnit.{1})) (fun " ++ cohboxVar f.name ++ " => " ++ next sem ++ "))")
                else
                  let sem ← lambda dom (decAt b j value ++ "._ir_val")
                  pure (".sigma (ULift.{" ++ lvl ++ "} ((_ : " ++ rawTy ++ ") ×' PUnit.{1})) (fun " ++ box ++ " => " ++ next sem ++ ")")
              else
                let packed ← packedType b g dom
                let value := app (valuesVar f.name) #[packedValue dom]
                if indexed b j then
                  let sIdx ← semIdx b src j args
                  -- the coherence, over the packed argument
                  let stmt := "∀ (_ir_p : " ++ packed ++ "), " ++ app (lambda' dom (par (app (valuesVar f.name) #["_ir_p"]) ++ "._ir_at = " ++ iMk b j sIdx)) (unpacked dom "_ir_p")
                  let sem ← lambda dom (trAt b j (par (cohVar f.name ++ ".down.1 " ++ packedValue dom)) (par value ++ "._ir_val"))
                  pure (".delta " ++ par packed ++ " (fun _ => " ++ sortValue b j ++ ") (fun " ++ valuesVar f.name ++ " => .sigma (ULift.{" ++ lvl ++ "} ((_ : " ++ stmt ++ ") ×' PUnit.{1})) (fun " ++ cohVar f.name ++ " => " ++ next sem ++ "))")
                else
                  let sem ← lambda dom (par value ++ "._ir_val")
                  pure (".delta " ++ par packed ++ " (fun _ => " ++ sortValue b j ++ ") (fun " ++ valuesVar f.name ++ " => " ++ next sem ++ ")")
            else
              pure (".sigma (ULift.{" ++ lvl ++ "} ((_ : " ++ (← semText b src f.type) ++ ") ×' PUnit.{1})) (fun " ++ boxVar f.name ++ " => " ++ next (boxVar f.name ++ ".down.1") ++ ")")
        emitL ("def " ++ contName m c i ++ " " ++ ps ++ " " ++ join binders ++ " : " ++ ty ++ " :=\n  " ++ body)
where
  /-- A lambda over the binders, or the body when there are none, applied by the caller. -/
  lambda' (bs : Array Binder) (body : String) : String :=
    if bs.isEmpty then body else par ("fun " ++ join (bs.map fun x => x.name.toString) ++ " => " ++ body)

private def emitLowerSorts (b : Block) (g : Nat) : CommandElabM Unit := do
  let ps ← paramsDecl b
  let members := b.groups[g]!
  emitL ("inductive " ++ sortName b g ++ " where\n" ++ String.intercalate "\n" (members.toList.map fun i => "  | s" ++ toString i))
  for i in members do
    let m := b.members[i]!
    emitL ("inductive " ++ tagName m ++ " where\n" ++ String.intercalate "\n" (m.ctors.toList.map fun c => "  | " ++ c.name.toString))
  emitL ("def " ++ famName b g ++ " " ++ ps ++ " : ULift.{" ++ glevel b g ++ "} " ++ sortName b g ++ " → Type (" ++ glevel b g ++ "+1)\n" ++
    String.intercalate "\n" (members.toList.map fun i => "  | " ++ sortPat b i ++ " => " ++ atParams b (dName b.members[i]!)))

private def emitLowerSignature (b : Block) (g : Nat) : CommandElabM Unit := do
  let ps ← paramsDecl b
  let mut ss := #[]
  for k in b.groups[g]! do
    let m := b.members[k]!
    let cs := m.ctors.toList.map fun c => "    | ." ++ c.name.toString ++ " => " ++ atParams b (contName m c 0)
    ss := ss.push ("  | " ++ sortPat b k ++ " => .choose " ++ tagName m ++ " (fun\n" ++ String.intercalate "\n" cs ++ ")")
  emitL ("def " ++ sigName b g ++ " " ++ ps ++ " : Mumi.IR.Signature (ULift.{" ++ glevel b g ++ "} " ++ sortName b g ++ ") " ++ par (atParams b (famName b g)) ++ "\n" ++ String.intercalate "\n" ss.toList)
  for k in b.groups[g]! do
    let m := b.members[k]!
    emitDefL "" (rawName m ++ " " ++ ps ++ " : Type " ++ glevel b g ++ " := Mumi.IR.Raw " ++ sigAt b g ++ " " ++ sortValue b k)
    emitDefL "@[reducible] " (decName m ++ " " ++ ps ++ " (_ir_a : " ++ rawAt b k ++ ") : " ++ atParams b (dName m) ++ " := Mumi.IR.decode " ++ sigAt b g ++ " " ++ sortValue b k ++ " _ir_a")

/-! ### Raw constructors and certificates -/

/-- The kind of an argument of a certificate constructor. -/
private inductive GoodArg where
  /-- A raw field. -/
  | raw
  /-- The coherence of a raw field of an indexed carrier. -/
  | coh
  /-- The equation pinning a hidden conclusion field to its value. -/
  | eq
  /-- The certificate of a field of carrier type. -/
  | cert
  /-- A proof of a `Prop` member. -/
  | proof
  /-- A plain field. -/
  | plain
  deriving BEq, Inhabited

/-- The fields of `c` in the raw world: their binders, each under its name and
kind, the sources they bind, and the arguments the raw constructor is applied
to. -/
private structure RawFields where
  binders : Array String := #[]
  names : Array (String × GoodArg) := #[]
  src : Array Source := #[]
  rawArgs : Array String := #[]

private def RawFields.bind (r : RawFields) (n t : String) (k : GoodArg) : RawFields :=
  { r with binders := r.binders.push (par (n ++ " : " ++ t)), names := r.names.push (n, k) }
private def RawFields.arg (r : RawFields) (a : String) : RawFields := { r with rawArgs := r.rawArgs.push a }
private def RawFields.source (r : RawFields) (x : Source) : RawFields := { r with src := r.src.push x }

/-- The fields of `c` in the raw world, with their coherences.  For the
certificate (`forGood`) a hidden argument is not bound but stands for its
value, a hidden conclusion index is pinned to its value by an equation, a
field of carrier type is followed by its certificate, and a proof of a `Prop`
member -- which the raw term does not carry -- is bound as a proof of that
member's certificate, where it was written. -/
private def rawFields (b : Block) (c : Ctor) (forGood := false) : CommandElabM RawFields := do
  let mut r : RawFields := {}
  for f in c.lowerOf.fields do
    if let some (j, args) := f.target then
      if b.members[j]!.prop then
        if forGood then
          let dom ← domIn b r.src f
          r := r.bind f.name.toString (← forallS dom (withParams b (goodName b.members[j]!) (← goodIdx b r.src j args))) .proof
        continue
    if f.value.isSome then
      let some (j, args) := f.target | continue
      if forGood && f.hiddenArg then
        -- an argument stands for its value, whose decode reduces where it is used
        let h ← hiddenSource b r.src f
        r := r.source h |>.arg h.graph
        if h.coh != "" then r := r.arg h.coh
        continue
      let dom ← domIn b r.src f
      let value := applyDomain f.name.toString dom
      r := r.bind f.name.toString (← forallS dom (rawAt b j)) .raw |>.arg f.name.toString
      if indexed b j then
        let sIdx ← semIdx b r.src j args
        r := r.bind (cohVar f.name) (← forallS dom (decAt b j value ++ "._ir_at = " ++ iMk b j sIdx)) .coh |>.arg (cohVar f.name)
      if forGood then
        -- a conclusion index is bound, and pinned to its value at the fields
        let h ← hiddenSource b r.src f
        r := r.bind (eqVar f.name) (← forallS dom (value ++ " = " ++ app h.graph (dom.map (·.name.toString)))) .eq
      let coh := if indexed b j then cohVar f.name else ""
      if f.hiddenArg then
        r := r.source { ← hiddenSource b r.src f with graph := f.name.toString, coh }
      else if indexed b j then
        r := r.source { name := f.name, sem := ← lambda dom (trAt b j (applyDomain (cohVar f.name) dom) (decAt b j value ++ "._ir_val")), graph := f.name.toString, coh }
      else
        r := r.source { name := f.name, sem := ← lambda dom (decAt b j value ++ "._ir_val"), graph := f.name.toString }
      continue
    r := r.arg f.name.toString
    if let some (j, args) := f.target then
      if indexed b j then r := r.arg (cohVar f.name)
      let dom ← domIn b r.src f
      r := r.bind f.name.toString (← forallS dom (rawAt b j)) .raw
      let value := applyDomain f.name.toString dom
      if indexed b j then
        let sIdx ← semIdx b r.src j args
        r := r.bind (cohVar f.name) (← forallS dom (decAt b j value ++ "._ir_at = " ++ iMk b j sIdx)) .coh
        r := r.source { name := f.name, sem := ← lambda dom (trAt b j (applyDomain (cohVar f.name) dom) (decAt b j value ++ "._ir_val")), graph := f.name.toString, coh := cohVar f.name }
      else
        r := r.source { name := f.name, sem := ← lambda dom (decAt b j value ++ "._ir_val"), graph := f.name.toString }
      if forGood then
        r := r.bind (hVar f.name) (← forallS dom (withParams b (goodName b.members[j]!) ((← goodIdx b r.src j args) ++ #[value]))) .cert
    else
      r := r.bind f.name.toString (← semText b r.src f.type) .plain
  return r

private def emitRawCtors (b : Block) (g : Nat) : CommandElabM Unit := do
  let ps ← paramsDecl b
  for k in b.groups[g]! do
    let m := b.members[k]!
    for c in m.ctors do
      let r ← rawFields b c
      let (binders, src, args) := (r.binders, r.src, r.rawArgs)
      let mut values := #[]
      for f in lowerFields b c do
        if let some (j, _) := f.target then
          if foreign b k j then
            -- a value of another engine: a plain field, with its coherence
            values := values.push ("⟨⟨" ++ f.name.toString ++ ", PUnit.unit⟩⟩")
            if indexed b j then values := values.push ("⟨⟨" ++ cohVar f.name ++ ", PUnit.unit⟩⟩")
            continue
          values := values.push ("(fun _ir_position => " ++ app f.name.toString (unpacked f.domain "_ir_position") ++ ")")
          if indexed b j then
            values := values.push ("⟨⟨(fun _ir_position => " ++ app (cohVar f.name) (unpacked f.domain "_ir_position") ++ "), PUnit.unit⟩⟩")
        else values := values.push ("⟨⟨" ++ f.name.toString ++ ", PUnit.unit⟩⟩")
      emitDefL "" (rawName m ++ "." ++ c.name.toString ++ " " ++ ps ++ " " ++ join binders ++ " : " ++ rawAt b k ++ " := Mumi.IR.roll " ++ sigAt b g ++ " " ++ sortValue b k ++ " " ++ tuple (tagName m ++ "." ++ c.name.toString) values)
      -- what the constructor's decode is at, stated once over its raw fields
      if indexed b k then
        let sIdx ← semIdx b src k c.lowerOf.result
        emitL ("theorem " ++ aux m.name ("_" ++ c.name.toString ++ "_at") ++ " " ++ ps ++ " " ++ join binders ++ " : " ++ decAt b k (withParams b (rawName m ++ "." ++ c.name.toString) args) ++ "._ir_at = " ++ iMk b k sIdx ++ " := rfl")
      -- and what its decode is: its piece at the fields' semantics, which a
      -- constructor nested inside another in an index is rewritten by
      let sems := ((lowerFields b c).filter (!·.hiddenArg)).map fun f =>
        if f.target.isSome then ((src.findRev? (·.name == f.name)).map (·.sem)).getD f.name.toString else f.name.toString
      -- not `rfl` outright: `simp` would then rewrite by it definitionally,
      -- which at a nested instance the kernel cannot follow
      emitL ("theorem " ++ valLemma m c ++ " " ++ ps ++ " " ++ join binders ++ " : " ++ decAt b k (withParams b (rawName m ++ "." ++ c.name.toString) args) ++ "._ir_val = " ++ par (withParams b (pieceName m c) sems) ++ "._ir_val := Eq.trans rfl rfl")

/-- The certificates, one `Prop` family per member over the raw terms in one
`mutual` of Lean's own: a data member's says of a raw term which constructor
it is, at which indices, that its fields are certified and that the proofs
the constructor was written with are at hand; a `Prop` member's is the
member itself, over the raw halves of its indices, its fields of carrier type
each followed by their certificate. -/
private def emitGood (b : Block) : CommandElabM Unit := do
  let ps ← paramsDecl b
  let mut gs := #[]
  for k in [:b.members.size] do
    let m := b.members[k]!
    let (arity, _) ← rawArity b k
    let mut cs := #[]
    for c in m.ctors do
      let r ← rawFields b c (forGood := true)
      let concl ← goodIdx b r.src k c.lowerOf.result
      let head := if m.prop then withParams b (goodName m) concl
        else withParams b (goodName m) (concl ++ #[withParams b (rawName m ++ "." ++ c.name.toString) r.rawArgs])
      cs := cs.push ("  | " ++ c.name.toString ++ " " ++ join r.binders ++ " : " ++ head)
    let arity := if arity.isEmpty then "" else String.intercalate " → " arity.toList ++ " → "
    let self := if m.prop then "" else rawAt b k ++ " → "
    gs := gs.push ("inductive " ++ goodName m ++ " " ++ ps ++ " : " ++ arity ++ self ++ "Prop where\n" ++ String.intercalate "\n" cs.toList)
  emitL ("mutual\n" ++ String.intercalate "\n" gs.toList ++ "\nend")
  -- the coherence a certificate yields, stated at whatever the index's semantics is defeq to
  for k in dataMembers b do
    if !indexed b k then continue
    let m := b.members[k]!
    let (arity, src) ← rawArity b k
    let names := rawArityNames b k
    let arity := arity.map fun x => "{" ++ ((x.toSubstring.drop 1).dropRight 1).toString ++ "}"
    emitL ("theorem " ++ goodName m ++ ".coh " ++ ps ++ " " ++ join arity ++ " {_ir_a : " ++ rawAt b k ++ "} (_ir_h : " ++ withParams b (goodName m) (names ++ #["_ir_a"]) ++ ") {_ir_s : " ++ iAt b k ++ "} (_ir_hs : " ++ iOfArity b k src ++ " = _ir_s) : " ++ decAt b k "_ir_a" ++ "._ir_at = _ir_s := by\n  subst _ir_hs; cases _ir_h <;> rfl")

/-! ### The public declarations -/

private def emitLowerPublic (b : Block) (order : Array (Sum Nat Nat)) : CommandElabM Unit := do
  let ps ← paramsDecl b
  for o in order do
    match o with
    | .inl k =>
      let m := b.members[k]!
      let gargs ← goodIdxPub b k (m.indices.map fun x => mkIdent x.name)
      if m.prop then
        emitL ("@[reducible] def " ++ m.name.toString ++ " " ++ ps ++ " " ++ (← pubArity b k) ++ " : Prop := " ++ withParams b (goodName m) gargs)
        continue
      emitL ("def " ++ m.name.toString ++ " " ++ ps ++ " " ++ (← pubArity b k) ++ " : Type " ++ m.level ++ " := { _ir_a : " ++ rawAt b k ++ " // " ++ withParams b (goodName m) (gargs ++ #["_ir_a"]) ++ " }")
      -- the semantics of a public value, at the semantics of its indices
      let idx := pubIdxNames b k
      let sIdx ← m.indices.mapM fun x => do
        if let some (j, args) := x.member then return app (pubSemName b.members[j]!) (pArgs b ++ (← args.mapM text) ++ #[x.name.toString])
        else return x.name.toString
      let body := if indexed b k then
          trAt b k (par (withParams b (goodName m ++ ".coh") #["_ir_x.property", "rfl"])) (decAt b k "_ir_x.val" ++ "._ir_val")
        else decAt b k "_ir_x.val" ++ "._ir_val"
      emitDefL "@[reducible] " (pubSemName m ++ " " ++ ps ++ " " ++ (← pubArity b k) ++ " (_ir_x : " ++ typeAt b k idx ++ ") : " ++ semAt b k sIdx ++ " := " ++ body)
    | .inr j =>
      let d := b.decoders[j]!
      let m := b.members[d.target]!
      let idx ← d.idx.mapM fieldDecl
      let result := subst d.result #[(d.major, mkIdent `_ir_self)]
      emitDefL "@[reducible] " (d.name.toString ++ " " ++ ps ++ " " ++ join idx ++ " (_ir_self : " ++ (← text d.majorType) ++ ") : " ++ (← text result) ++ " := " ++ par (app (pubSemName m) (pArgs b ++ d.idx.map (·.name.toString) ++ #["_ir_self"])) ++ "." ++ outField j)
  let mut lemmas : Array String := b.members.flatMap fun m => m.ctors.map (valLemma m)
  for k in [:b.members.size] do
    let m := b.members[k]!
    for ci in [:m.ctors.size] do
      let c := m.ctors[ci]!
      let mut raw := #[]
      -- the certificate's arguments interleave each field with its coherence
      -- and hypothesis; a hidden field is supplied with its value, which the
      -- certificate binds and pins for a conclusion index, and substitutes
      -- for an argument
      let mut gargs := #[]
      let mut hiddenPairs : Array (Name × Syntax) := #[]
      for f in c.lowerOf.fields do
        if isProofTarget b f.target then
          -- the certificate's, where it was written
          gargs := gargs.push f.name.toString
        else if let some (j, args) := f.target then
          let mut v := applyDomain f.name.toString f.domain
          if let some value := f.value then
            v ← qualifyText b (some j) (subst value hiddenPairs)
            hiddenPairs := hiddenPairs.push (f.name, ← parseTerm (← lambda f.domain v))
          raw := raw.push (← lambda f.domain (par v ++ ".val"))
          unless f.hiddenArg do gargs := gargs.push raw.back!
          if indexed b j then
            -- at an index with a constructor nested inside another, the
            -- decode of the nested one is not definitional and is rewritten
            let nested := (← args.mapM text).any fun t => (t.splitOn "_ir_sub_").length > 1
            let hs := if nested then "(by simp only [" ++ String.intercalate ", " lemmas.toList ++ "] <;> rfl)" else "rfl"
            raw := raw.push (← lambda f.domain (withParams b (goodName b.members[j]! ++ ".coh") #[par v ++ ".property", hs]))
            unless f.hiddenArg do gargs := gargs.push raw.back!
          if f.value.isNone then
            gargs := gargs.push (← lambda f.domain (par v ++ ".property"))
          else if !f.hiddenArg then
            gargs := gargs.push (← lambda f.domain "rfl")
        else
          raw := raw.push f.name.toString
          gargs := gargs.push f.name.toString
      let result ← c.result.mapM text
      -- the certificate's constructor takes the block's parameters implicitly, as any constructor does
      if m.prop then
        emitL ("theorem " ++ m.name.toString ++ "." ++ c.name.toString ++ " " ++ ps ++ " " ++ (← fieldsDecl c) ++ " : " ++ typeAt b k result ++ " := " ++ app (goodName m ++ "." ++ c.name.toString) gargs)
        continue
      emitDefL "" (m.name.toString ++ "." ++ c.name.toString ++ " " ++ ps ++ " " ++ (← fieldsDecl c) ++ " : " ++ typeAt b k result ++ " := ⟨" ++ withParams b (rawName m ++ "." ++ c.name.toString) raw ++ ", " ++ app (goodName m ++ "." ++ c.name.toString) gargs ++ "⟩")
      emitL ("theorem " ++ rawLemma m c ++ " " ++ ps ++ " " ++ (← fieldsDecl c) ++ " : " ++ par (ctorApp b k ci (fieldNames c)) ++ ".val = " ++ withParams b (rawName m ++ "." ++ c.name.toString) raw ++ " := Eq.trans rfl rfl")
      lemmas := lemmas.push (rawLemma m c)

/-! ### The recursor -/

/-- The value the recursion computes at a raw value of carrier `k`: the motive at
the public value, for every raw index and certificate it could be at. -/
private def emitMotive (b : Block) (g : Nat) : CommandElabM Unit := do
  let ps ← paramsDecl b
  let mut cs := #[]
  for k in b.groups[g]! do
    let m := b.members[k]!
    let (packed, proj, pub, good) ← motiveTele b k
    -- one binder of `Type u` per arm, so that every arm lands in the same sort
    cs := cs.push ("  | " ++ sortPat b k ++ ", _ir_a => ∀ (_ir_p : " ++ packed ++ ") (_ir_h : " ++ atProj proj (withParams b (goodName m) (good ++ #["_ir_a"])) ++ "), " ++ atProj proj (app (motive k) (pub ++ #["⟨_ir_a, _ir_h⟩"])))
  emitL ("def " ++ motiveName b g ++ " " ++ ps ++ " " ++ (← motiveDecls b b.groups[g]!) ++ " : (_ir_s : ULift.{" ++ glevel b g ++ "} " ++ sortName b g ++ ") → Mumi.IR.Raw " ++ sigAt b g ++ " _ir_s → Sort (imax (" ++ glevel b g ++ "+1) _ir_elim)\n" ++ String.intercalate "\n" cs.toList)

/-- The tuple pattern of `c`'s arguments, and the `let`s that unpack them into
the raw fields and coherences, in the world of `X`. -/
private def unpackedFields (b : Block) (k : Nat) (c : Ctor) (value : String → Array Binder → Nat → CommandElabM String) : CommandElabM (Array String × String × Array Source) := do
  let mut pats := #[]
  let mut lets := ""
  let mut src : Array Source := #[]
  for f in lowerFields b c do
    if let some (j, _) := f.target then
      let dom ← domIn b src f
      if foreign b k j then
        -- a value of another engine is a box, as a plain field is
        pats := pats.push (boxVar f.name)
        if indexed b j then pats := pats.push (cohboxVar f.name)
        if f.value.isSome then
          src := src.push (← hiddenSource b src f)
          continue
        lets := lets ++ "let " ++ f.name.toString ++ " := " ++ boxVar f.name ++ ".down.1\n  "
        if indexed b j then
          lets := lets ++ "let " ++ cohVar f.name ++ " := " ++ cohboxVar f.name ++ ".down.1\n  "
          src := src.push { name := f.name, sem := ← lambda dom (trAt b j (applyDomain (cohVar f.name) dom) (decAt b j (applyDomain f.name.toString dom) ++ "._ir_val")), graph := f.name.toString, coh := cohVar f.name }
        else
          src := src.push { name := f.name, sem := ← lambda dom (decAt b j (applyDomain f.name.toString dom) ++ "._ir_val"), graph := f.name.toString }
        continue
      pats := pats.push (packedVar f.name)
      if indexed b j then pats := pats.push (cohboxVar f.name)
      if f.value.isSome then
        -- the certificate pinned it to its value, and so does the shape
        src := src.push (← hiddenSource b src f)
        continue
      lets := lets ++ "let " ++ f.name.toString ++ " := " ++ (← lambda dom (← value (packedVar f.name) dom j)) ++ "\n  "
      if indexed b j then
        lets := lets ++ "let " ++ cohVar f.name ++ " := " ++ (← lambda dom (cohboxVar f.name ++ ".down.1 " ++ packedValue dom)) ++ "\n  "
        src := src.push { name := f.name, sem := ← lambda dom (trAt b j (applyDomain (cohVar f.name) dom) (decAt b j (applyDomain f.name.toString dom) ++ "._ir_val")), graph := f.name.toString, coh := cohVar f.name }
      else
        src := src.push { name := f.name, sem := ← lambda dom (decAt b j (applyDomain f.name.toString dom) ++ "._ir_val"), graph := f.name.toString }
    else
      pats := pats.push (boxVar f.name)
      lets := lets ++ "let " ++ f.name.toString ++ " := " ++ boxVar f.name ++ ".down.1\n  "
  return (pats, lets, src)

/-- The raw constructor's arguments at the sources `src`: a hidden field is
what its source says. -/
private def rawArgsAt (b : Block) (c : Ctor) (src : Array Source) : Array String :=
  (lowerFields b c).flatMap fun f => match f.target with
    | some (j, _) =>
      if f.value.isSome then
        match src.findRev? (·.name == f.name) with
        | some h => if h.coh.isEmpty then #[h.graph] else #[h.graph, h.coh]
        | none => #[]
      else if indexed b j then #[f.name.toString, cohVar f.name] else #[f.name.toString]
    | none => #[f.name.toString]

/-- What a certificate of `X.c` at raw indices `idx` says, over the raw fields:
the node, the indices, the sub-certificates. -/
private def shapeStmt (b : Block) (k ci : Nat) (idxNames : Array String) (src : Array Source) (self : String) : CommandElabM String := do
  let m := b.members[k]!
  let c := m.ctors[ci]!.lowerOf
  let mut parts := #[self ++ " = " ++ withParams b (rawName m ++ "." ++ c.name.toString) (rawArgsAt b c src)]
  -- one equation per index that is not a coherence
  let mut ni := 0
  for (x, t) in m.indices.zip c.result do
    if let some (j, _) := x.member then
      parts := parts.push (idxNames[ni]! ++ " = " ++ (← triple b src j t).2.1)
      ni := ni + (if indexed b j then 2 else 1)
    else
      -- heterogeneous: its type mentions the carrier indices before it, which
      -- are equated rather than substituted here
      parts := parts.push ("HEq " ++ idxNames[ni]! ++ " " ++ (← semText b src t))
      ni := ni + 1
  for f in c.fields do
    if f.value.isSome then continue
    if let some (j, args) := f.target then
      let dom ← domIn b src f
      -- a proof of a `Prop` member is a certificate too, of that member's, without a node
      let node := if b.members[j]!.prop then #[] else #[applyDomain f.name.toString dom]
      parts := parts.push (← forallS dom (withParams b (goodName b.members[j]!) ((← goodIdx b src j args) ++ node)))
  return String.intercalate " ∧ " (parts.toList ++ ["True"])

private def emitShapes (b : Block) (g : Nat) : CommandElabM Unit := do
  let ps ← paramsDecl b
  for k in b.groups[g]! do
    let m := b.members[k]!
    let (arity, _) ← rawArity b k
    let names := rawArityNames b k
    let mut cs := #[]
    let mut proofs := #[]
    for ci in [:m.ctors.size] do
      let c := m.ctors[ci]!
      let (pats, lets, src) ← unpackedFields b k c (fun p dom _ => pure (app p #[packedValue dom]))
      cs := cs.push ("  | " ++ tuple (tagName m ++ "." ++ c.name.toString) pats ++ " =>\n  " ++ lets ++ (← shapeStmt b k ci names src "_ir_self"))
      -- `cases` names the constructor's arguments in declaration order
      let r ← rawFields b c (forGood := true)
      let ordered := r.names.map (·.1)
      let hs := (r.names.filter fun (_, kind) => kind == .cert || kind == .proof).map (·.1)
      let eqs' := (r.names.filter (·.2 == .eq)).map (·.1)
      let eqs := m.indices.toList.map fun x => if x.member.isSome then "rfl" else "HEq.rfl"
      let substs := if eqs'.isEmpty then "" else "subst " ++ join eqs' ++ "; "
      proofs := proofs.push ("  | " ++ c.name.toString ++ " " ++ join ordered ++ " => " ++ substs ++ "exact ⟨rfl, " ++ String.intercalate ", " (eqs ++ hs.toList ++ ["trivial"]) ++ "⟩")
    emitDefL "" (shapeName m ++ " " ++ ps ++ " " ++ join arity ++ " (_ir_self : " ++ rawAt b k ++ ") : Mumi.IR.Args (Mumi.IR.Raw " ++ sigAt b g ++ ") (Mumi.IR.decode " ++ sigAt b g ++ ") (" ++ sigAt b g ++ " " ++ sortValue b k ++ ") → Prop\n" ++ String.intercalate "\n" cs.toList)
    emitL ("theorem " ++ shapeLemma m ++ " " ++ ps ++ " " ++ join arity ++ " {_ir_self : " ++ rawAt b k ++ "} (_ir_good : " ++ withParams b (goodName m) (names ++ #["_ir_self"]) ++ ") : " ++ withParams b (shapeName m) (names ++ #["_ir_self", "(Mumi.IR.view " ++ sigAt b g ++ " " ++ sortValue b k ++ " _ir_self)"]) ++ " := by\n  cases _ir_good with\n" ++ String.intercalate "\n" proofs.toList)

/-- Transport a value of the motive across the equations a certificate yields:
every index, and the node. -/
private def emitCasts (b : Block) (g : Nat) : CommandElabM Unit := do
  let ps ← paramsDecl b
  for k in b.groups[g]! do
    let m := b.members[k]!
    let mut binders := #[]
    let mut discr := #[]
    let mut pats := #[]
    let mut pub := #[]
    let mut pub' := #[]
    let mut good := #[]
    let mut good' := #[]
    let mut pairs : Array (Name × Syntax) := #[]
    let mut pairs' : Array (Name × Syntax) := #[]
    for x in m.indices do
      let n := x.name.toString
      if let some (j, args) := x.member then
        let hx := "_ir_hx_" ++ n
        let gargs ← goodIdxPub b j (args.map (subst · pairs))
        let gargs' ← goodIdxPub b j (args.map (subst · pairs'))
        binders := binders.push (par (n ++ " " ++ n ++ "' : " ++ rawAt b j))
        binders := binders.push (par ("_ir_e_" ++ n ++ " : " ++ n ++ " = " ++ n ++ "'"))
        binders := binders.push (par (hx ++ " : " ++ withParams b (goodName b.members[j]!) (gargs ++ #[n])))
        binders := binders.push (par (hx ++ "' : " ++ withParams b (goodName b.members[j]!) (gargs' ++ #[n ++ "'"])))
        -- the certificate right after its index, since the indices after
        -- it are typed at the public value `⟨x', hx'⟩`
        discr := discr.push (n ++ "'") |>.push ("_ir_e_" ++ n) |>.push (hx ++ "'")
        pats := pats.push "_" |>.push "rfl" |>.push "_"
        let ty ← (args.map (subst · pairs)).mapM text
        let ty' ← (args.map (subst · pairs')).mapM text
        pub := pub.push (par ("⟨" ++ n ++ ", " ++ hx ++ "⟩ : " ++ typeAt b j ty))
        pub' := pub'.push (par ("⟨" ++ n ++ "', " ++ hx ++ "'⟩ : " ++ typeAt b j ty'))
        good := good.push n
        good' := good'.push (n ++ "'")
        if indexed b j then
          good := good.push (par (withParams b (goodName b.members[j]! ++ ".coh") #[hx, "rfl"]))
          good' := good'.push (par (withParams b (goodName b.members[j]! ++ ".coh") #[hx ++ "'", "rfl"]))
        pairs := pairs.push (x.name, ← parseTerm (par ("⟨" ++ n ++ ", " ++ hx ++ "⟩ : " ++ typeAt b j ty)))
        pairs' := pairs'.push (x.name, ← parseTerm (par ("⟨" ++ n ++ "', " ++ hx ++ "'⟩ : " ++ typeAt b j ty')))
      else
        binders := binders.push (par (n ++ " : " ++ (← text (subst x.type pairs))))
        binders := binders.push (par (n ++ "' : " ++ (← text (subst x.type pairs'))))
        binders := binders.push (par ("_ir_e_" ++ n ++ " : HEq " ++ n ++ " " ++ n ++ "'"))
        discr := discr.push (n ++ "'") |>.push ("_ir_e_" ++ n)
        pats := pats.push "_" |>.push "HEq.rfl"
        pub := pub.push n
        pub' := pub'.push (n ++ "'")
        good := good.push n
        good' := good'.push (n ++ "'")
        pairs' := pairs'.push (x.name, mkIdent (Name.mkSimple (n ++ "'")))
    emitL ("def " ++ castName m ++ " " ++ ps ++ " " ++ (← motiveDecls b b.groups[g]!) ++ " " ++ join binders ++ " (_ir_a _ir_a' : " ++ rawAt b k ++ ") (_ir_ea : _ir_a = _ir_a') (_ir_good : " ++ withParams b (goodName m) (good ++ #["_ir_a"]) ++ ") (_ir_good' : " ++ withParams b (goodName m) (good' ++ #["_ir_a'"]) ++ ") (_ir_v : " ++ app (motive k) (pub' ++ #["⟨_ir_a', _ir_good'⟩"]) ++ ") : " ++ app (motive k) (pub ++ #["⟨_ir_a, _ir_good⟩"]) ++ " :=\n  match " ++ String.intercalate ", " (discr.toList ++ ["_ir_a'", "_ir_ea", "_ir_good'"]) ++ " with\n  | " ++ String.intercalate ", " (pats.toList ++ ["_", "rfl", "_"]) ++ " => _ir_v")

/-- The step of the recursion at `X.c`: the constructor's arguments in the
predecessor family, the certificate, and every motive and minor premise. -/
private def emitSteps (b : Block) (g : Nat) : CommandElabM Unit := do
  let ps ← paramsDecl b
  let scope := b.groups[g]!
  let lvl := glevel b g
  let common := ps ++ " " ++ (← motiveDecls b scope) ++ " " ++ (← minorDecls b true scope)
  let lt := relationAt b g
  let prev := "(fun _ir_j _ir_h => IR.Stage.build " ++ sigAt b g ++ " " ++ lt ++ " _ir_j (_ir_children _ir_j _ir_h))"
  let predAt (j : Nat) := "IR.Stage.Pred " ++ lt ++ " _ir_stage " ++ prev ++ " " ++ sortValue b j
  let predDecode (j : Nat) (p : String) := par ("IR.Stage.predDecode " ++ lt ++ " " ++ sortValue b j ++ " " ++ p)
  for k in scope do
    let m := b.members[k]!
    let (mPacked, mProj, mPub, mGood) ← motiveTele b k
    for ci in [:m.ctors.size] do
      let c := m.ctors[ci]!
      -- the arguments, in the predecessor world
      let mut comps := #[]
      let mut names := #[]
      let mut psrc : Array Source := #[]
      -- a plain field is a box in the predecessor world; what follows reads it unboxed
      let mut boxes : Array (Name × Syntax) := #[]
      for f in lowerFields b c do
        let unbox (s : Syntax) : Syntax := subst s boxes
        let f : Field := { f with type := unbox f.type, target := f.target.map (fun p => (p.1, p.2.map unbox)), domain := f.domain.map (fun x => { name := x.name, type := unbox x.type }), value := f.value.map unbox }
        if let some (j, args) := f.target then
          let dom ← domIn b psrc f
          if foreign b k j then
            -- a value of another engine: a box, and the box of its coherence
            let value := applyDomain (boxVar f.name ++ ".down.1") dom
            comps := comps.push (par (boxVar f.name ++ " : ULift.{" ++ lvl ++ "} ((_ : " ++ (← forallS dom (rawAt b j)) ++ ") ×' PUnit.{1})"))
            names := names.push (boxVar f.name)
            if indexed b j then
              let sIdx ← semIdx b psrc j args
              let stmt ← forallS dom (decAt b j value ++ "._ir_at = " ++ iMk b j sIdx)
              comps := comps.push (par (cohboxVar f.name ++ " : ULift.{" ++ lvl ++ "} ((_ : " ++ stmt ++ ") ×' PUnit.{1})"))
              names := names.push (cohboxVar f.name)
              psrc := psrc.push { name := f.name, sem := ← lambda dom (trAt b j (applyDomain (cohboxVar f.name ++ ".down.1") dom) (decAt b j value ++ "._ir_val")), graph := f.name.toString, coh := "" }
            else
              psrc := psrc.push { name := f.name, sem := ← lambda dom (decAt b j value ++ "._ir_val"), graph := f.name.toString }
            if f.hiddenArg then
              psrc := psrc.pop.push { ← hiddenSource b psrc.pop f with graph := f.name.toString, coh := "" }
            continue
          let packed ← packedType b g dom
          comps := comps.push (par (packedVar f.name ++ " : " ++ packed ++ " → " ++ predAt j))
          names := names.push (packedVar f.name)
          let value (p : String) := predDecode j (app (packedVar f.name) #[p])
          if indexed b j then
            let sIdx ← semIdx b psrc j args
            let stmt := "∀ (_ir_p : " ++ packed ++ "), " ++ app (lambdaN dom (value "_ir_p" ++ "._ir_at = " ++ iMk b j sIdx)) (unpacked dom "_ir_p")
            comps := comps.push (par (cohboxVar f.name ++ " : ULift.{" ++ lvl ++ "} ((_ : " ++ stmt ++ ") ×' PUnit.{1})"))
            names := names.push (cohboxVar f.name)
            psrc := psrc.push { name := f.name, sem := ← lambda dom (trAt b j (par (cohboxVar f.name ++ ".down.1 " ++ packedValue dom)) (value (packedValue dom) ++ "._ir_val")), graph := f.name.toString, coh := "" }
          else
            psrc := psrc.push { name := f.name, sem := ← lambda dom (value (packedValue dom) ++ "._ir_val"), graph := f.name.toString }
          if f.hiddenArg then
            psrc := psrc.pop.push { ← hiddenSource b psrc.pop f with graph := f.name.toString, coh := "" }
        else
          comps := comps.push (par (boxVar f.name ++ " : ULift.{" ++ lvl ++ "} ((_ : " ++ (← semText b psrc f.type) ++ ") ×' PUnit.{1})"))
          names := names.push (boxVar f.name)
          boxes := boxes.push (f.name, ← parseTerm (boxVar f.name ++ ".down.1"))
      let node := "Mumi.IR.pack " ++ sigAt b g ++ " " ++ lt ++ " _ir_stage _ir_children " ++ sortValue b k ++ " " ++ tuple (tagName m ++ "." ++ c.name.toString) names
      let recurse := "(_ir_recurse : ∀ _ir_t (_ir_p : IR.Stage.Pred " ++ lt ++ " _ir_stage " ++ prev ++ " _ir_t), " ++ withParams b ("@" ++ motiveName b g) (motiveArgs b scope ++ #["_ir_t", "(Mumi.IR.raise " ++ sigAt b g ++ " " ++ lt ++ " _ir_t _ir_p)"]) ++ ")"
      -- the body: raise the fields, read the shape, rebuild the public fields, recurse, transport
      let (_, lets, src) ← unpackedFields b k c (fun p dom j => pure ("Mumi.IR.raise " ++ sigAt b g ++ " " ++ lt ++ " (children := _ir_children) " ++ sortValue b j ++ " " ++ par (app p #[packedValue dom])))
      let mut body := projLets mProj ++ lets ++ "let _ir_node := " ++ node ++ "\n  "
      body := body ++ "let _ir_shape : " ++ (← shapeStmt b k ci mGood src "_ir_node") ++ " := " ++ withParams b (shapeLemma m) (mGood ++ #["_ir_good"]) ++ "\n  "
      -- public fields and hypotheses
      let mut pubPairs : Array (Name × Syntax) := #[]
      let mut images := #[]
      let mut ihs := #[]
      let mut certAt := 1 + m.indices.size
      for f in c.fields do
        if isProofTarget b f.target then
          -- the proof the constructor was written with, off the shape; what
          -- follows may name it, in an index term
          let cert := "_ir_shape" ++ conj certAt
          certAt := certAt + 1
          images := images.push cert
          pubPairs := pubPairs.push (f.name, ← parseTerm cert)
        else if let some (j, args) := f.target then
          let pdom := f.domain.map fun x => { x with type := subst x.type pubPairs }
          let pargs ← (args.map (subst · pubPairs)).mapM text
          let cert := "_ir_shape" ++ conj certAt
          certAt := certAt + 1
          body := body ++ "let " ++ pubVar f.name ++ " : " ++ (← forallS pdom (typeAt b j pargs)) ++ " := " ++ (← lambda pdom ("⟨" ++ applyDomain f.name.toString f.domain ++ ", " ++ applyDomain cert f.domain ++ "⟩")) ++ "\n  "
          -- a value of another engine is no part of this recursion: no hypothesis
          unless foreign b k j do
            let margs ← motiveArgsAt b j (args.map (subst · pubPairs))
            body := body ++ "let " ++ ihVar f.name ++ " : " ++ (← forallS pdom (app (motive j) (pargs ++ #[applyDomain (pubVar f.name) pdom]))) ++ " := " ++ (← lambda pdom (app "_ir_recurse" (#[sortValue b j, par (app (packedVar f.name) #[packedValue f.domain]), packTuple margs] ++ #[applyDomain cert f.domain]))) ++ "\n  "
            ihs := ihs.push (ihVar f.name)
          images := images.push (pubVar f.name)
          pubPairs := pubPairs.push (f.name, mkIdent (Name.mkSimple (pubVar f.name)))
        else
          images := images.push f.name.toString
      let ctor := ctorApp b k ci images
      -- the cast: for each index, the raw variable of the motive and the public term's raw half
      let mut castArgs := #[]
      let mut ei := 1
      for (x, t) in m.indices.zip c.result do
        let pt ← qualifyText b (x.member.map (·.1)) (subst t pubPairs)
        if x.member.isSome then
          castArgs := castArgs.push ("_ir_idx_" ++ x.name.toString) |>.push (par pt ++ ".val") |>.push ("_ir_shape" ++ conj ei) |>.push ("_ir_hx_" ++ x.name.toString) |>.push (par pt ++ ".property")
        else
          castArgs := castArgs.push ("_ir_idx_" ++ x.name.toString) |>.push pt |>.push ("_ir_shape" ++ conj ei)
        ei := ei + 1
      body := body ++ withParams b ("@" ++ castName m) (motiveArgs b scope ++ castArgs ++ #["_ir_node", par ctor ++ ".val", "_ir_shape.1", "_ir_good", par ctor ++ ".property", app (minor b k ci) (images ++ ihs)])
      emitDefL "" (stepName m c ++ " " ++ common ++ " (_ir_stage : (Mumi.IR.model " ++ sigAt b g ++ ").Level) (_ir_children : ∀ _ir_j, " ++ lt ++ " _ir_j _ir_stage → Acc " ++ lt ++ " _ir_j) " ++ join comps ++ " " ++ recurse ++ " (_ir_p : " ++ mPacked ++ ") (_ir_good : " ++ atProj mProj (withParams b (goodName m) (mGood ++ #[par node])) ++ ") : " ++ atProj mProj (app (motive k) (mPub ++ #["⟨" ++ node ++ ", _ir_good⟩"])) ++ " :=\n  " ++ body)
  -- the induction itself, and the public recursors
  let mut ss := #[]
  for k in scope do
    let m := b.members[k]!
    let mut cs := #[]
    for ci in [:m.ctors.size] do
      let c := m.ctors[ci]!
      let (pats, _, _) ← unpackedFields b k c (fun p _ _ => pure p)
      cs := cs.push ("      | " ++ tuple (tagName m ++ "." ++ c.name.toString) pats ++ " => " ++ withParams b ("@" ++ stepName m c) (motiveArgs b scope ++ minorArgs b scope ++ #["_ir_stage", "_ir_children"] ++ pats ++ #["_ir_recurse"]))
    ss := ss.push ("    | " ++ sortPat b k ++ " => match _ir_args with\n" ++ String.intercalate "\n" cs.toList)
  emitDefL "" (indName b g ++ " " ++ common ++ " : ∀ _ir_s _ir_a, " ++ withParams b ("@" ++ motiveName b g) (motiveArgs b scope ++ #["_ir_s", "_ir_a"]) ++ " :=\n  Mumi.IR.induction " ++ sigAt b g ++ " (C := " ++ withParams b ("@" ++ motiveName b g) (motiveArgs b scope) ++ ") (fun _ir_stage _ir_children _ir_sort _ir_args _ir_recurse =>\n    match _ir_sort with\n" ++ String.intercalate "\n" ss.toList ++ ")")
  for k in scope do
    let m := b.members[k]!
    let idx := pubIdxNames b k
    let margs ← motiveArgsAt b k (m.indices.map fun x => mkIdent x.name)
    emitDefL "@[elab_as_elim] " (m.name.toString ++ ".rec " ++ common ++ " " ++ (← pubArity b k (implicit := true)) ++ " (_ir_self : " ++ typeAt b k idx ++ ") : " ++ app (motive k) (idx ++ #["_ir_self"]) ++ " := " ++ withParams b ("@" ++ indName b g) (motiveArgs b scope ++ minorArgs b scope ++ #[sortValue b k, "_ir_self.val", packTuple margs, "_ir_self.property"]))
where
  /-- A lambda over the binders' names alone. -/
  lambdaN (bs : Array Binder) (body : String) : String :=
    if bs.isEmpty then body else par ("fun " ++ join (bs.map fun x => x.name.toString) ++ " => " ++ body)
  /-- The arguments the motive at carrier `j` takes at public index terms:
  `.val` and `.property` of an index of carrier type, the value of a plain one. -/
  motiveArgsAt (b : Block) (j : Nat) (args : Array Syntax) : CommandElabM (Array String) := do
    let mut out := #[]
    for (y, t) in b.members[j]!.indices.zip args do
      if let some (i, _) := y.member then
        let t ← qualifyText b (some i) t
        out := out.push (par t ++ ".val") |>.push (par t ++ ".property")
      else out := out.push (← text t)
    return out

/-- A `Prop` member's minor premise at the written universe, public and as
the certificates' recursor takes it.  The latter is a proof, so it is closed
by tactic: the equations pinning hidden conclusion fields substituted, the
written minor premise applied at the public values of the fields, and a
hypothesis at the certificates of its field's indices. -/
private def lowerPropMinor (b : Block) (j ci : Nat) (ihs : Bool) (conclName : String) : CommandElabM (String × String) := do
  let m := b.members[j]!
  let c := m.ctors[ci]!
  let mut hyps := #[]
  if ihs then
    for f in c.fields do
      if let some (k, _) := f.target then
        if b.members[k]!.prop then hyps := hyps.push (par (ihVar f.name ++ " : " ++ (← ihType f (some (propMotive b k)))))
  let result ← c.result.mapM text
  let concl := app conclName (result ++ #[ctorApp b j ci (fieldNames c)])
  let decls ← fieldsDecl c
  let ty := if c.fields.isEmpty then concl else "∀ " ++ decls ++ " " ++ join hyps ++ ", " ++ concl
  let pub := par (propMinor b j ci ++ " : " ++ ty)
  -- the certificate's arguments, a hypothesis per certificate among them, the arity's certificates
  let r ← rawFields b c (forGood := true)
  let ihNames := (r.names.filter fun (_, kind) => kind == .cert || kind == .proof).map fun (n, kind) =>
    if kind == .proof then "_ir_ih_" ++ n else "_"
  let (comps, _, _) ← pubTele b j
  let hxs := (comps.filter fun (n, _) => n.startsWith "_ir_hx_").map (·.1)
  let binders := r.names.map (·.1) ++ (if ihs then ihNames else #[]) ++ hxs
  let mut pubPairs : Array (Name × Syntax) := #[]
  let mut lets := ""
  let mut images := #[]
  let mut ihImages := #[]
  for f in c.fields do
    if let some (k, args) := f.target then
      let pdom := f.domain.map fun x => { x with type := subst x.type pubPairs }
      if b.members[k]!.prop then
        images := images.push f.name.toString
        if ihs then
          let mut certs := #[]
          for (y, t) in b.members[k]!.indices.zip (args.map (subst · pubPairs)) do
            if let some (i, _) := y.member then certs := certs.push (par (← qualifyText b (some i) t) ++ ".property")
          ihImages := ihImages.push (← lambda pdom (applyTo (applyDomain (ihVar f.name) f.domain) certs))
      else
        let pargs ← (args.map (subst · pubPairs)).mapM text
        lets := lets ++ "let " ++ pubVar f.name ++ " : " ++ (← forallS pdom (typeAt b k pargs)) ++ " := " ++ (← lambda pdom ("⟨" ++ applyDomain f.name.toString f.domain ++ ", " ++ applyDomain (hVar f.name) f.domain ++ "⟩")) ++ "\n      "
        images := images.push (pubVar f.name)
        pubPairs := pubPairs.push (f.name, mkIdent (Name.mkSimple (pubVar f.name)))
    else images := images.push f.name.toString
  let eqs := (r.names.filter (·.2 == .eq)).map (·.1)
  let substs := if eqs.isEmpty then "" else "subst " ++ join eqs ++ "; "
  let g := untypedLambda binders ("by " ++ substs ++ "exact\n      " ++ lets ++ app (propMinor b j ci) (images ++ (if ihs then ihImages else #[])))
  return (pub, g)

/-- The `Prop` members' recursors and `casesOn` at the written universe, from
the certificates' joint recursor: a data member's certificate at the motive
`True`, a `Prop` member's at its public motive under the certificates of its
indices, which make the public values of those. -/
private def emitLowerPropRec (b : Block) : CommandElabM Unit := do
  let ps ← paramsDecl b
  let props := propMembers b
  let mut motives := #[]
  for j in props do
    motives := motives.push ("{" ++ propMotive b j ++ " : ∀ " ++ (← pubArity b j) ++ " (_ir_self : " ++ typeAt b j (pubIdxNames b j) ++ "), Prop}")
  let gmotive (k : Nat) (name : String) : CommandElabM String := do
    let (comps, pub, _) ← pubTele b k
    let hyps := (comps.filter fun (n, _) => n.startsWith "_ir_hx_").map fun (n, t) => par (n ++ " : " ++ t)
    let value := app name (pub ++ #["_ir_h"])
    return untypedLambda (rawArityNames b k ++ #["_ir_h"]) (if hyps.isEmpty then value else "∀ " ++ join hyps ++ ", " ++ value)
  let mut gargs := pArgs b
  for k in [:b.members.size] do
    if b.members[k]!.prop then gargs := gargs.push (← gmotive k (propMotive b k))
    else gargs := gargs.push (untypedLambda (rawArityNames b k ++ #["_ir_a", "_ir_h"]) "True")
  let mut minors := #[]
  for k in [:b.members.size] do
    for ck in [:b.members[k]!.ctors.size] do
      if b.members[k]!.prop then
        let (pub, g) ← lowerPropMinor b k ck true (propMotive b k)
        minors := minors.push pub
        gargs := gargs.push g
      else
        let r ← rawFields b b.members[k]!.ctors[ck]! (forGood := true)
        let certs := r.names.filter fun (_, kind) => kind == .cert || kind == .proof
        gargs := gargs.push (untypedLambda ((r.names ++ certs).map fun _ => "_") "trivial")
  for j in props do
    let m := b.members[j]!
    let idx := pubIdxNames b j
    let gIdx ← goodIdxPub b j (m.indices.map fun x => mkIdent x.name)
    let certs := m.indices.filterMap fun x => if x.member.isSome then some (x.name.toString ++ ".property") else none
    let attrs := if props.size == 1 then "@[elab_as_elim, induction_eliminator] " else "@[elab_as_elim] "
    emitL (attrs ++ "theorem " ++ m.name.toString ++ ".rec " ++ ps ++ " " ++ join motives ++ " " ++ join minors ++ " " ++ (← pubArity b j (implicit := true)) ++ " (_ir_self : " ++ typeAt b j idx ++ ") : " ++ app (propMotive b j) (idx ++ #["_ir_self"]) ++ " := " ++ app ("@" ++ goodName m ++ ".rec") (gargs ++ gIdx ++ #["_ir_self"] ++ certs))
    let mot := "{motive : ∀ " ++ (← pubArity b j) ++ " (_ir_self : " ++ typeAt b j idx ++ "), Prop}"
    let mut cminors := #[]
    let mut cgminors := #[]
    for ci in [:m.ctors.size] do
      let (pub, g) ← lowerPropMinor b j ci false "motive"
      cminors := cminors.push pub
      cgminors := cgminors.push g
    emitL ("@[elab_as_elim, cases_eliminator] theorem " ++ m.name.toString ++ ".casesOn " ++ ps ++ " " ++ mot ++ " " ++ join cminors ++ " " ++ (← pubArity b j (implicit := true)) ++ " (_ir_self : " ++ typeAt b j idx ++ ") : " ++ app "motive" (idx ++ #["_ir_self"]) ++ " := " ++ app ("@" ++ goodName m ++ ".casesOn") (pArgs b ++ #[← gmotive j "motive"] ++ gIdx ++ #["_ir_self"] ++ cgminors ++ certs))

/-- The engines: the data members by universe, each group in an order every
carrier's fields and indices of carrier type come before it -- a carrier's
are at its universe or below, so there is one. -/
private def lowerGroups (b : Block) : CommandElabM (Array (Array Nat)) := do
  let mut groups : Array (String × Array Nat) := #[]
  for k in dataMembers b do
    let l := b.members[k]!.level
    if let some gi := groups.findIdx? (·.1 == l) then groups := groups.modify gi fun (l, ms) => (l, ms.push k)
    else groups := groups.push (l, #[k])
  let n := groups.size
  let names (a c : Nat) : Bool := groups[a]!.2.any fun k =>
    let m := b.members[k]!
    (m.indices.any fun x => x.member.any fun (j, _) => groups[c]!.2.contains j) ||
    (m.ctors.any fun ct => ct.fields.any fun f => f.target.any fun (j, _) => groups[c]!.2.contains j)
  let mut order := #[]
  let mut placed := Array.replicate n false
  for _ in [:n] do
    for a in [:n] do
      if !placed[a]! && (Array.range n).all (fun c => c == a || placed[c]! || !names a c) then
        placed := placed.set! a true
        order := order.push a
  unless order.size == n do
    throwError "Carriers in different universes name one another in their fields or indices both ways, which no universe allows"
  return order.map (groups[·]!.2)

/-- Lower mode, end to end: one stage engine per universe, in order, the
certificates of every member in one `mutual` after them all, and the
recursion of each engine at its own motives. -/
private def elaborateLower (b : Block) (order : Array (Sum Nat Nat)) : CommandElabM Unit := do
  let b ← flattenLower b
  let groups ← lowerGroups b
  let b := { b with groups }
  let b := { b with recs := b.members.mapIdx fun k m => if m.prop then #[] else groups[groupOf b k]! }
  emit "universe _ir_elim"
  emitSemantics b order
  emitLowerSemantics b order
  for g in [:groups.size] do
    emitLowerSorts b g
    emitContinuations b g
    emitLowerSignature b g
    emitRawCtors b g
  emitGood b
  emitLowerPublic b order
  for g in [:groups.size] do
    emitMotive b g
    emitShapes b g
    emitCasts b g
    emitSteps b g
  if b.members.any (·.prop) then emitLowerPropRec b
  emitEquations b
  emitSolo b

/-- Whether a block needs this path: some carrier is indexed. -/
def isIndexed (elems : Array Syntax) : CommandElabM Bool := do
  for e in elems do
    let d := e[1]
    if d.isOfKind ``Parser.Command.«inductive» then
      let (_, result) ← signature d[2]
      unless (unparen result).isOfKind ``Parser.Term.type do return true
  return false

def elaborate (elems : Array Syntax) : CommandElabM Unit := do
  let b ← readBlock elems
  let order ← declarationOrder b
  if mumi.mahlo.get (← getOptions) then
    elaborateLower { b with lower := true } order
    return
  emit "universe _ir_elim"
  let b := { b with wf := b.members.any (·.prop) }
  emitSemantics b order
  emitGraph b
  let b := { b with recs := ← graphRecMembers b }
  if b.wf then
    emitWf b
    emitInv b
  emitPublic b order
  emitRec b
  if b.wf then emitPropRec b
  emitEquations b
  emitSolo b

end Mumi.IndRec.Family

namespace Mumi.IndRec
open Lean Elab Command

/-- Whether `e` declares an inductive in `Prop`. -/
private def isPropInductive (e : Syntax) : CommandElabM Bool := do
  let d := e[1]
  unless d.isOfKind ``Parser.Command.«inductive» do return false
  let (_, result) ← signature d[2]
  let (_, result) ← telescope result
  return result.isOfKind ``Parser.Term.prop

/-- The carrier a definition recurses over: the last binder of its signature
whose type is one of the block's inductives, if any. -/
private def majorOf (inductives : Array Name) (e : Syntax) : CommandElabM (Option Name) := do
  let d := e[1]
  unless d.isOfKind ``Parser.Command.definition do return none
  let (ps, ty) ← signature d[2]
  let (tele, _) ← telescope ty
  let mut out := none
  for b in ps ++ tele do
    let h := (unapp b.type).1
    if h.isIdent && inductives.contains h.getId then out := some h.getId
  return out

/-- The components of the block's declarations, each in source order,
dependencies first.  `e` depends on `f` when it mentions `f`'s name, and a
definition recursing over one of the block's inductives is kept with it, since
it matches on constructors that are the induction-recursion's to give. -/
private def components (elems : Array Syntax) : CommandElabM (Array (Array Syntax)) := do
  let names := elems.map (·[1][1][0].getId)
  let n := elems.size
  let inductives := (elems.zip names).filterMap fun (e, nm) =>
    if e[1].isOfKind ``Parser.Command.«inductive» then some nm else none
  -- a definition and the carrier it recurses over are one node
  let mut group : Array Nat := Array.range n
  for i in [:n] do
    if let some m ← majorOf inductives elems[i]! then
      if let some k := names.findIdx? (· == m) then
        let (gi, gk) := (group[i]!, group[k]!)
        group := group.map fun g => if g == gi then gk else g
  let roots := (Array.range n).filter fun i => group[i]! == i
  let members := roots.map fun r => (Array.range n).filter fun i => group[i]! == r
  let m := roots.size
  let deps : Array (Array Nat) := (Array.range m).map fun a =>
    (Array.range m).filter fun b => a != b &&
      members[a]!.any fun i => members[b]!.any fun j => mentions elems[i]! #[names[j]!]
  -- Tarjan over the quotient: components come out dependencies first
  let mut index : Array (Option Nat) := Array.replicate m none
  let mut low : Array Nat := Array.replicate m 0
  let mut onStack : Array Bool := Array.replicate m false
  let mut stack : Array Nat := #[]
  let mut counter := 0
  let mut out : Array (Array Nat) := #[]
  for root in [:m] do
    if index[root]!.isSome then continue
    let mut work : Array (Nat × Nat) := #[(root, 0)]
    index := index.set! root (some counter); low := low.set! root counter; counter := counter + 1
    stack := stack.push root; onStack := onStack.set! root true
    while !work.isEmpty do
      let (v, k) := work.back!
      if k < deps[v]!.size then
        work := work.pop.push (v, k + 1)
        let w := deps[v]![k]!
        match index[w]! with
        | none =>
          index := index.set! w (some counter); low := low.set! w counter; counter := counter + 1
          stack := stack.push w; onStack := onStack.set! w true
          work := work.push (w, 0)
        | some iw => if onStack[w]! then low := low.set! v (min low[v]! iw)
      else
        work := work.pop
        if let some (u, _) := work.back? then low := low.set! u (min low[u]! low[v]!)
        if low[v]! == index[v]!.get! then
          let mut comp := #[]
          let mut go := true
          while go do
            let w := stack.back!
            stack := stack.pop; onStack := onStack.set! w false
            comp := comp.push w
            go := w != v
          out := out.push comp
  return out.map fun comp => ((comp.flatMap fun a => members[a]!).qsort (· < ·)).map (elems[·]!)

/-- The universe an inductive is declared in, as written: `"Prop"`, or the
level of its `Type`. -/
private def levelOf (e : Syntax) : CommandElabM String := do
  let (_, result) ← signature e[1][2]
  let (_, result) ← telescope result
  if result.isOfKind ``Parser.Term.prop then return "Prop"
  if result.isOfKind ``Parser.Term.type then
    return if result[1].getNumArgs == 0 then "0" else (result[1][0].reprint.getD "0").trimAscii.toString
  return "?"

/-- The IR frontend.  The block is split only where it has to be: into its
strongly connected components, dependencies first, which are then regrouped
as far as a group can be one block -- carriers in one universe, with their
decoders and any inductives alone there -- so that a block in one universe
stays one block with one joint recursion, as a `mutual` is.  A group of
carriers and decoders is an induction-recursion and goes one universe up
through `Family` when indexed, otherwise through the original path; a group of
definitions alone, or of `Prop` inductives, is Lean's.  So members may sit in
different universes, and a `Prop` inductive the rest only refers to is
declared right after what it refers to; a `Prop` inductive the carriers or
decoders of its component mention is not taken yet. -/
def elaborateAny (elems : Array Syntax) : CommandElabM Unit := do
  let isInductive (e : Syntax) := e[1].isOfKind ``Parser.Command.«inductive»
  -- regroup: a component joins the group before it when both are carriers in
  -- the same universe (with their decoders)
  let mut groups : Array (Array Syntax × String) := #[]
  for comp in ← components elems do
    let inductives := comp.filter isInductive
    let levels ← inductives.mapM levelOf
    let level := levels.getD 0 ""
    let level := (levels.filter (· != "Prop")).getD 0 level
    let plain := level != "Prop" && !inductives.isEmpty
    if plain then
      if let some (g, l) := groups.back? then
        if l == level then
          groups := groups.pop.push (g ++ comp, l)
          continue
    groups := groups.push (comp, if plain then level else "")
  for (comp, _) in groups do
    let inductives := comp.filter isInductive
    let props ← inductives.filterM isPropInductive
    if inductives.isEmpty || inductives.size == comp.size || props.size == inductives.size then
      -- Lean's own: a block of definitions, or of inductives, with `mutual` taking several
      if h : comp.size = 1 then elabCommand comp[0]
      else elabCommand (mkNode ``Parser.Command.«mutual» #[mkAtom "mutual", mkNullNode comp, mkAtom "end", mkNullNode])
    else if ← Family.isIndexed comp then Family.elaborate comp
    else elaborate comp

end Mumi.IndRec
