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
  /-- The binder's type is a `Prop` member: the index is a proof, no data. -/
  proof : Bool := false
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
  /-- As written: what the public constructor binds it as. -/
  info : BinderInfo := .default
  /-- The target's index arguments as written, proofs among them; `target` has
  the others, which are all the encoding sees. -/
  pubArgs : Array Syntax := #[]
  deriving Inhabited

def Field.implicit (f : Field) : Bool := f.info != .default

structure Ctor where
  name : Name
  fields : Array Field
  /-- The index arguments of the conclusion: those that are no proof. -/
  result : Array Syntax
  /-- Every index argument of the conclusion, as written. -/
  pubResult : Array Syntax := #[]
  /-- At the written universe: the fields and conclusion with every constructor
  application nested inside another in an index term named by a hidden field,
  so that each index term applies a constructor to fields only. -/
  lower : Option (Array Field × Array Syntax) := none
  /-- The documentation written on it, `/-- … -/` with a newline, or `""`. -/
  doc : String := ""
  deriving Inhabited

/-- The constructor as the raw world sees it. -/
def Ctor.lowerOf (c : Ctor) : Ctor :=
  match c.lower with
  | some (fields, result) => { c with fields, result }
  | none => c

structure Member where
  name : Name
  /-- The indices that are no proof: what the encoding sees. -/
  indices : Array Index
  /-- Every index, as written, proofs of the block's propositions among them. -/
  pubIndices : Array Index := #[]
  ctors : Array Ctor
  /-- A member declared in `Prop`: it has no decoders, no semantics and no
  graph; a field of its type is a proof, and one universe up it is a
  well-formedness predicate over the graphs. -/
  prop : Bool := false
  /-- The level of the member's `Type`, as written; `""` for a `Prop` member. -/
  level : String := ""
  doc : String := ""
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
  doc : String := ""
  /-- The shared parameters as the decoder binds them: explicit or implicit, as written. -/
  params : Array Binder := #[]
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
  /-- Put before the eliminators' names: `_nested_` when the block is a nested
  one's denesting, whose eliminators over the copies are its own, the public
  ones being stated over the originals afterwards. -/
  elimPrefix : String := ""
  deriving Inhabited

/-- The eliminator prefix the block being elaborated is given: `_nested_` while
a denesting is. -/
initialize nestedPrefix : IO.Ref String ← IO.mkRef ""

/-- `s` with each subterm `f` maps replaced, outermost first. -/
partial def replaceStx (f : Syntax → Option Syntax) (s : Syntax) : Syntax :=
  match f s with
  | some t => t
  | none => match s with
    | .node info k xs => .node info k (xs.map (replaceStx f))
    | _ => s

/-- The name of member `m`'s eliminator `base`: `X.rec`, or `X._nested_rec`. -/
def elimName (b : Block) (m : Member) (base : String) : String :=
  m.name.toString ++ "." ++ b.elimPrefix ++ base

/-- `attrs` without the tactic registrations where the eliminators are not the
public ones. -/
def elimAttrs (b : Block) (attrs : String) : String :=
  if b.elimPrefix.isEmpty then attrs
  else (attrs.replace ", induction_eliminator" "").replace ", cases_eliminator" ""

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
/-- The parameters as arguments where an anonymous instance is bound anonymously:
by `‹T›`. -/
private def anonArgs (b : Block) := b.params.map fun p => if p.anon then p.argText else pname p.name
private def withAnonParams (b : Block) (n : String) (xs : Array String) := app n (anonArgs b ++ xs)
private def atParams (b : Block) (n : String) := if b.params.isEmpty then n else app n (pArgs b)
private def withParams (b : Block) (n : String) (xs : Array String) := app n (pArgs b ++ xs)
private def fieldDecl (f : Binder) : CommandElabM String := do
  let d := f.name.toString ++ " : " ++ (← text f.type)
  -- an anonymous instance is bound as written where it is bound as written
  if f.anon && f.info == .instImplicit then return "[" ++ (← text f.type) ++ "]"
  return bracket f.info d
/-- The shared parameters as a generated declaration binds them: explicit, an
instance among them too, which is a local instance all the same.  Every
application of one is positional. -/
private def paramsDecl (b : Block) : CommandElabM String :=
  return join (← b.params.mapM fun p => fieldDecl { p with info := .default, anon := false })
/-- The shared parameters as the carriers bind them: as written. -/
private def carrierParamsDecl (b : Block) : CommandElabM String := return join (← b.params.mapM fieldDecl)
/-- The shared parameters as a public constructor or eliminator binds them: an
explicit one implicit, as Lean's own do, an instance an instance.  Every
application the frontend writes of one is `@`-qualified and positional. -/
private def pubParamsDecl (b : Block) : CommandElabM String :=
  return join (← b.params.mapM fun p => fieldDecl { p with info := if p.info == .default then .implicit else p.info, anon := false })
/-- A decoder's type after its indices: `X idx → R`, or `(a : X idx) → R` where
the result mentions the major, as Lean displays one declared either way. -/
private def decoderTail (d : Decoder) : CommandElabM String := do
  if mentions d.result #[d.major] then
    return "(" ++ d.major.toString ++ " : " ++ (← text d.majorType) ++ ") → " ++ (← text d.result)
  return (← text d.majorType) ++ " → " ++ (← text d.result)
/-- A decoder's shared parameters as its author bound them. -/
private def decParamsDecl (d : Decoder) : CommandElabM String := return join (← d.params.mapM fieldDecl)
/-- The shared parameters a call of decoder `d` writes: its explicit ones. -/
private def writtenParams (d : Decoder) : Array Binder := d.params.filter (!·.implicit)
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
  -- a carrier is written at its explicit parameters, as Lean's own is
  let params := params.filter (·.info == .default)
  let (head, args) := unapp s
  let some i := names.findIdx? (same head ·) | return none
  if args.size < params.size then return none
  if !((args.extract 0 params.size).zip params).all (fun (a, p) => same a p.name) then return none
  return some (i, args.extract params.size args.size)

/-- The constructor `s` names, as `X.c` or `.c` against the expected carrier. -/
private def ctorRef? (b : Block) (expect : Option Nat) (s : Syntax) : Option (Nat × Nat) := Id.run do
  -- `@X.c`, as the reader itself writes a qualified constructor
  let s := if s.isOfKind ``Parser.Term.explicit then s[1] else s
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

/-- The fields of constructor `ci` of carrier `k` an application of it with head
`h` writes, one per field, `none` for an implicit one left out: `@X.c` writes the
parameters and every field, `X.c` and `.c` every field or the explicit ones. -/
private def fieldArgs (b : Block) (k ci : Nat) (h : Syntax) (args : Array Syntax) : Option (Array (Option Syntax)) :=
  let c := b.members[k]!.ctors[ci]!
  if h.isOfKind ``Parser.Term.explicit then
    let fargs := args.extract b.params.size args.size
    if fargs.size == c.fields.size then some (fargs.map some) else none
  else if args.size == c.fields.size then some (args.map some)
  else if args.size == (c.fields.filter (!·.implicit)).size then Id.run do
    let mut out := #[]
    let mut j := 0
    for f in c.fields do
      if f.implicit then out := out.push none
      else
        out := out.push (some args[j]!)
        j := j + 1
    return some out
  else none

/-- `sol` extended by matching `p`, a term over the names `unknowns`, against `t`,
both of carrier `expect` if known: a sought name matches anything, and two
applications of one constructor of the block match field by field where both
write the field.  Anything else says nothing. -/
private partial def matchInto (b : Block) (unknowns : Array Name) (expect : Option Nat)
    (sol : Array (Name × Syntax)) (p t : Syntax) : Array (Name × Syntax) := Id.run do
  let p := unparen p
  let t := unparen t
  if p.isIdent && unknowns.contains p.getId then
    return if sol.any (·.1 == p.getId) then sol else sol.push (p.getId, t)
  let (hp, ap) := unapp p
  let (ht, at_) := unapp t
  -- a dotted head is resolved against the other side's, or the expected carrier
  let expect := expect <|> (ctorRef? b none hp).map (·.1) <|> (ctorRef? b none ht).map (·.1)
  let some (k, ci) := ctorRef? b expect hp | return sol
  unless ctorRef? b expect ht == some (k, ci) do return sol
  let some fp := fieldArgs b k ci hp ap | return sol
  let some ft := fieldArgs b k ci ht at_ | return sol
  let mut sol := sol
  for ((f, x), y) in (b.members[k]!.ctors[ci]!.fields.zip fp).zip ft do
    if let (some x, some y) := (x, y) then
      sol := matchInto b unknowns (f.target.map (·.1)) sol x y
  return sol

/-- The index arguments of a term of carrier `k`: of a variable, as `ctx`
declares it; of a constructor application of the block, its conclusion at the
fields it writes (`qualified`, the application with every field). -/
private def indicesOf (b : Block) (ctx : Array Binder) (k : Nat) (t : Syntax) (qualified : Option Syntax) :
    Option (Array Syntax) := Id.run do
  let t := unparen t
  if t.isIdent then
    let some x := ctx.findRev? (·.name == t.getId) | return none
    let some (k', idx) := memberApp? (b.members.map (·.name)) b.params x.type | return none
    return if k' == k then some idx else none
  let some q := qualified | return none
  let (h, args) := unapp q
  let some (k', ci) := ctorRef? b (some k) h | return none
  unless k' == k do return none
  let some fs := fieldArgs b k ci h args | return none
  let c := b.members[k]!.ctors[ci]!
  let pairs := (c.fields.zip fs).filterMap fun (f, a) => a.map (f.name, ·)
  return some (c.result.map (subst · pairs))

/-- A public index term of carrier `expect` as text, every constructor
application of the block in it given its full name with the parameters and
every field, so that the term can be read where no expected type resolves the
dot -- under `.val`, say -- and the encoding can see every field.  An implicit
field written nowhere is found as Lean's elaborator would find it, by matching
the constructor's conclusion against `expectIdx`, the index arguments the term
stands at, and the types of its explicit fields against those of the arguments,
which `ctx` declares where they are variables. -/
private partial def qualifyText (b : Block) (expect : Option Nat) (s : Syntax)
    (ctx : Array Binder := #[]) (expectIdx : Option (Array Syntax) := none) : CommandElabM String := do
  let (h, args) := unapp s
  let some (k, ci) := ctorRef? b expect h | text s
  let m := b.members[k]!
  let c := m.ctors[ci]!
  let some written := fieldArgs b k ci h args | text s
  -- the fields left out, solved for
  let unknowns := (c.fields.zip written).filterMap fun (f, a) => if a.isNone then some f.name else none
  let known := (c.fields.zip written).filterMap fun (f, a) => a.map (f.name, ·)
  let mut sol : Array (Name × Syntax) := #[]
  if !unknowns.isEmpty then
    if let some es := expectIdx then
      for ((x, r), e) in (m.indices.zip c.result).zip es do
        sol := matchInto b unknowns (x.member.map (·.1)) sol (subst r known) e
    for (f, a) in c.fields.zip written do
      let (some (j, pats), some a) := (f.target, a) | continue
      unless f.domain.isEmpty do continue
      let pats := pats.map (subst · known)
      let qa ← if (unapp a).1.isIdent && ctx.any (·.name == (unapp a).1.getId) then pure none
        else
          let solved := unknowns.all fun n => sol.any (·.1 == n)
          let ex := if solved then some (pats.map (subst · sol)) else none
          try pure (some (← parseTerm (← qualifyText b (some j) a ctx ex))) catch _ => pure none
      if let some idx := indicesOf b ctx j a qa then
        for ((x, pt), it) in (b.members[j]!.indices.zip pats).zip idx do
          sol := matchInto b unknowns (x.member.map (·.1)) sol pt it
    for n in unknowns do
      unless sol.any (·.1 == n) do
        throwErrorAt s "Cannot find the implicit field `{n}` of `{m.name}.{c.name}` here; write every field, `{m.name}.{c.name} {c.fields.map (·.name)}`"
  let full := (c.fields.zip written).map fun (f, a) => a.getD ((sol.find? (·.1 == f.name)).map (·.2) |>.getD Syntax.missing)
  let pairs := c.fields.zip full |>.map fun (f, a) => (f.name, a)
  let mut out := #[]
  for (f, a) in c.fields.zip full do
    let ex := f.target.bind fun (_, pats) => if f.domain.isEmpty then some (pats.map (subst · pairs)) else none
    out := out.push (← qualifyText b (f.target.map (·.1)) a ctx ex)
  -- every field, the implicit ones included, so `@`
  return withParams b ("@" ++ m.name.toString ++ "." ++ c.name.toString) out

/-- A decoder's clause with every constructor written `.c` in an index
argument of a decoder application, or in a constructor application of the
block, given its full name with the parameters, as `qualifyText` does for an
index term; the rest of the term is left as written. -/
private partial def qualifyClause (b : Block) (s : Syntax) : CommandElabM Syntax := do
  let (h, args) := unapp s
  if h.isIdent then
    if let some d := b.decoders.find? (·.name == h.getId) then
      let m := b.members[d.target]!
      let written := (Array.range d.idx.size).filter fun j => !d.idx[j]!.implicit
      let nidx := written.size
      let np := (writtenParams d).size
      if args.size ≥ np + nidx + 1 then
        let mut out := #[]
        for i in [:args.size] do
          let a := args[i]!
          if np ≤ i && i < np + nidx then
            let x := m.indices[written[i - np]!]!
            out := out.push (← parseTerm (← qualifyText b (x.member.map (·.1)) a))
          else out := out.push (← qualifyClause b a)
        return ← parseTerm (app (← text h) (← out.mapM text))
    if (ctorRef? b none h).isSome then
      return ← parseTerm (← qualifyText b none s)
  match s with
  | .node info k xs => return .node info k (← xs.mapM (qualifyClause b))
  | _ => return s

/-- The arguments `args` of carrier `k`'s indices as written, without those at a proof. -/
private def eraseArgs (members : Array Member) (k : Nat) (args : Array Syntax) : Array Syntax :=
  (members[k]!.indices.zip args).filterMap fun (x, a) => if x.proof then none else some a

/-- The block as the encoding sees it: an index that is a proof of one of the
block's propositions is no data, and is dropped from every arity, conclusion
and recursive field's indices, which keep what was written as `pubIndices`,
`pubResult` and `pubArgs` for the public declarations. -/
private def eraseProofs (b : Block) : Block :=
  let ms := b.members
  let members := ms.map fun m =>
    let indices := m.indices.filter (!·.proof) |>.map fun x =>
      { x with member := x.member.map fun (k, args) => (k, eraseArgs ms k args) }
    let ctors := m.ctors.map fun c =>
      let fields := c.fields.map fun f =>
        { f with target := f.target.map (fun (k, args) => (k, eraseArgs ms k args)),
                 pubArgs := (f.target.map (·.2)).getD #[] }
      { c with fields, result := eraseArgs ms (ms.findIdx? (·.name == m.name) |>.getD 0) c.result, pubResult := c.result }
    { m with indices, ctors, pubIndices := m.indices }
  { b with members }

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
  let mut heads : Array (Name × Array Binder × Bool × String × String) := #[]
  for e in elems do
    checkReservedNames e
    unless plainModifiers e[0] do throwErrorAt e "IR prototype does not yet support declaration modifiers or attributes inside a block"
    let d := e[1]
    -- a copy of a nested application is named under the first carrier
    unless d[1][0].getId.isAtomic || (d[1][0].getId.getString!.startsWith "nested_" && (← nestedPrefix.get) != "") do
      throwErrorAt d "IR prototype requires simple declaration names; place the mutual block inside a namespace"
    unless d[1][1].getNumArgs == 0 do throwErrorAt d "IR prototype uses surrounding universe declarations, not explicit declaration universe lists"
    if d.isOfKind ``Parser.Command.«inductive» then
      let (ps, result) ← signature d[2]
      if ps.any fun p => p.info == .implicit || p.info == .strictImplicit then
        throwErrorAt d "IR carriers take their shared parameters explicitly, `(x : T)`, or as instances, `[C x]`; their constructors and eliminators take them implicitly"
      let (idx, result) ← telescope result
      -- an index written as an arrow is named as Lean names it, `a`
      let fresh := domainNames (idx.map (·.name))
        -- fresh against every name the block uses: the encoding derives names from both
        (globalNames ++ ps.map (·.name) ++ elems.flatMap identsOf)
      let idx := (idx.zip fresh).map fun (x, n) =>
        if x.name.toString.startsWith "_ir_arg" then { x with name := n } else x
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
      heads := heads.push (d[1][0].getId, idx, prop, l, docOf e[0])
  checkDistinct (params.map (·.name)) globalNames
  for p in params do checkTermBinders (globalNames ++ params.map (·.name)) p.type
  let names := heads.map (·.1)
  -- the arities, now that every carrier's name and arity length are known
  let mut members : Array Member := #[]
  for (n, idx, prop, l, doc) in heads do
    checkDistinct (idx.map (·.name)) (globalNames ++ params.map (·.name))
    let mut indices := #[]
    for x in idx do
      checkTermBinders (globalNames ++ params.map (·.name) ++ idx.map (·.name)) x.type
      let member := memberApp? names params x.type
      if let some (k, args) := member then
        unless args.size == heads[k]!.2.1.size do
          throwErrorAt x.type "The carrier `{names[k]!}` takes {heads[k]!.2.1.size} indices"
      else if mentions x.type names then
        throwErrorAt x.type "An index domain may name a carrier only as that carrier applied to its indices; anything else has to go through a decoder"
      let proof := member.any fun (k, _) => heads[k]!.2.2.1
      if proof && prop then throwErrorAt x.type "A `Prop` member indexed by a proof is not supported yet"
      indices := indices.push { name := x.name, type := x.type, member, proof }
    members := members.push { name := n, indices, ctors := #[], prop, level := l, doc }
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
            if m.indices.isEmpty then parseTerm (app m.name.toString ((params.filter (·.info == .default)).map (pname ∘ Binder.name)))
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
          let fresh := domainNames (domain.map (·.name))
            (globalNames ++ params.map (·.name) ++ fieldNames ++ m.indices.map (·.name) ++
              (identsOf f.type).filter fun n => !(domain.map (·.name)).contains n)
          for k in [:domain.size] do
            let x := domain[k]!
            let name := fresh[k]!
            renamed := renamed.push { name, type := subst x.type pairs : Binder }
            pairs := pairs.push (x.name, mkIdent name)
          let target := target.map fun (k, args) => (k, args.map (subst · pairs))
          return { name := f.name, type := f.type, target, domain := if target.isSome then renamed else #[], info := f.info : Field }
        for x in idxArgs do checkTermBinders (globalNames ++ params.map (·.name) ++ fieldNames) x
        ctors := ctors.push { name := c[3].getId, fields := fs, result := idxArgs, doc := docOf c[0] }
      if ctors.isEmpty then throwErrorAt d "IR prototype currently requires at least one constructor per carrier"
      members := members.modify mi fun m => { m with ctors }
      mi := mi + 1
  -- a constructor written `.c` or `X.c` in an index term is given its full
  -- name, applied to the parameters with `@`; a field's type is restated only
  -- where that changed it
  let tmp : Block := { members, decoders := #[], params, level }
  members ← members.mapIdxM fun mi' m => do
    let ctors ← m.ctors.mapM fun c => do
      let ctx := c.fields.map fun f => ({ name := f.name, type := f.type } : Binder)
      -- an index's own type at the arguments before it
      let at_ (k : Nat) (args : Array Syntax) (j : Nat) : Option (Array Syntax) := do
        let x := members[k]!.indices[j]!
        let some (_, idx) := x.member | none
        let pairs := (members[k]!.indices.zip args).extract 0 j |>.map fun (y, a) => (y.name, a)
        some (idx.map (subst · pairs))
      let mut qresult := #[]
      for j in [:m.indices.size] do
        let x := m.indices[j]!
        qresult := qresult.push (← parseTerm (← qualifyText tmp (x.member.map (·.1)) c.result[j]! ctx (at_ mi' c.result j)))
      let result := qresult
      let fields ← c.fields.mapM fun f => do
        let some (k, args) := f.target | pure f
        let mut qargs := #[]
        for j in [:members[k]!.indices.size] do
          let x := members[k]!.indices[j]!
          qargs := qargs.push (← parseTerm (← qualifyText tmp (x.member.map (·.1)) args[j]! (ctx ++ f.domain) (at_ k args j)))
        -- restated only where a dotted constructor was resolved: the `@` a
        -- qualified one gains is no change
        let plain (q : Syntax) : CommandElabM String := do return (← text q).replace "@" ""
        if (← args.mapM plain) == (← qargs.mapM plain) then return f
        let type ← parseTerm (← forallS f.domain (withParams tmp ("@" ++ members[k]!.name.toString) (← qargs.mapM text)))
        pure { f with target := some (k, qargs), type }
      pure { c with result, fields }
    pure { m with ctors }
  -- decoders
  let mut decoders : Array Decoder := #[]
  for e in elems do
    let d := e[1]
    if d.isOfKind ``Parser.Command.definition then
      let (ps, ty) ← signature d[2]
      -- explicit or implicit, as the author wishes
      unless ps.size ≥ params.size && (← (ps.zip params).allM fun (a,b) => do return a.name == b.name && (← text a.type) == (← text b.type)) do
        throwErrorAt d "IR decoder must repeat the shared parameters, followed by the carrier's indices and one carrier argument"
      -- the major is the last binder that is a carrier at exactly the binders
      -- before it; what follows it is the result.  Indices may be bound before
      -- the colon, implicit there if wished
      let mut acc : Array Binder := ps.extract params.size ps.size
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
        -- an implicit index may be left out of the patterns, as Lean's own are
        let explicitIdx := (args.pop.filter (!·.implicit)).size
        let pats ← if pats.size == explicitIdx + 1 && explicitIdx < m.indices.size then do
            let mut full := #[]
            let mut k := 0
            for x in args.pop do
              if x.implicit then full := full.push (← parseTerm "_")
              else
                full := full.push pats[k]!
                k := k + 1
            pure (full.push pats.back!)
          else pure pats
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
        -- an implicit field may be left out of the pattern, as Lean's own are; it then goes by its own name
        let explicitFields := c.fields.filter (!·.implicit)
        let xs : Array Syntax := if xs.size == explicitFields.size && explicitFields.size < c.fields.size then Id.run do
            let mut full : Array Syntax := #[]
            let mut k := 0
            for f in c.fields do
              if f.implicit then full := full.push (mkIdent f.name).raw
              else
                full := full.push xs[k]!
                k := k + 1
            full
          else xs
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
      decoders := decoders.push { name, target := i, idx, major := major.name, majorType := major.type, result, clauses, doc := docOf e[0], params := ps.extract 0 params.size }
  let b : Block := { members, decoders, params, level }
  let qualified ← decoders.mapM fun d => do return { d with clauses := ← d.clauses.mapM (qualifyClause b) }
  return eraseProofs { b with decoders := qualified }

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
    -- the implicit indices are not written
    let nidx := (d.idx.filter (!·.implicit)).size
    -- and the implicit parameters
    let ps := writtenParams d
    unless args.size ≥ ps.size + nidx + 1 do
      throwErrorAt s "IR decoder calls must be fully applied to a value of the carrier"
    unless ((args.extract 0 ps.size).zip ps).all (fun (a,p) => same a p.name) do
      throwErrorAt s "IR decoder parameters must remain unchanged"
    -- the index arguments are determined by the major and are not read
    let major := args[ps.size + nidx]!
    let base ← semOfMajor b src major
    let base := if base.isEmpty then outField di else par base ++ "." ++ outField di
    let extra ← (args.extract (ps.size + nidx + 1) args.size).mapM (semantic b src)
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
  -- `@X.c` carries the parameters; `X.c` and `.c` leave them implicit
  let np := if h.isOfKind ``Parser.Term.explicit then b.params.size else 0
  unless args.size == np + c.fields.size do
    throwErrorAt s "The constructor `{m.name}.{c.name}` takes {np + c.fields.size} arguments here, every field included"
  unless ((args.extract 0 np).zip b.params).all (fun (a,p) => same a p.name) do
    throwErrorAt s "IR constructor parameters must remain unchanged"
  let fargs := args.extract np args.size
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
/-- Every index of carrier `i` as written, proofs among them. -/
private def pubIndicesOf (b : Block) (i : Nat) : Array Index :=
  let m := b.members[i]!
  if m.pubIndices.size ≥ m.indices.size then m.pubIndices else m.indices
/-- The public index arguments of carrier `i`, at its own arity names. -/
private def pubIdxNames (b : Block) (i : Nat) : Array String :=
  (pubIndicesOf b i).map (·.name.toString)
/-- Public index terms, as the graph takes them: `x.1 x.2` for one of carrier
type, `x.1.1 x.1.2` in a well-formed block, none for a proof. -/
private def pubPairIdx (b : Block) (i : Nat) (args : Array String) : Array String :=
  ((pubIndicesOf b i).zip args).flatMap fun (x, a) =>
    if x.proof then #[]
    else if x.member.isSome then
      if b.wf then #[par a ++ ".1.1", par a ++ ".1.2"] else #[par a ++ ".1", par a ++ ".2"]
    else #[a]
/-- The well-formedness of the public index arguments `args` of carrier `i`:
`x.2` at each of carrier type; then the proofs among them, as they are. -/
private def pubIdxWf (b : Block) (i : Nat) (args : Array String) : Array String :=
  let is := (pubIndicesOf b i).zip args
  (is.filterMap fun (x, a) => if x.member.isSome && !x.proof then some (par a ++ ".2") else none) ++
    (is.filterMap fun (x, a) => if x.proof then some a else none)
/-- The public value of each index of carrier `i` out of its halves, at the
arity's names; a proof by its own name, which the motive binds. -/
private def repackIdx (b : Block) (i : Nat) : Array String :=
  (pubIndicesOf b i).map fun x =>
    if x.proof then "_ir_pf_" ++ x.name.toString
    else if x.member.isSome then
      if b.wf then "⟨⟨" ++ semVar x.name ++ ", " ++ x.name.toString ++ "⟩, " ++ wfVar x.name ++ "⟩"
      else "⟨" ++ semVar x.name ++ ", " ++ x.name.toString ++ "⟩"
    else x.name.toString
/-- The proofs among carrier `i`'s indices, bound at the graph's names: each
its own name and its type at the public values of the indices before it. -/
private def arityProofs (b : Block) (i : Nat) : CommandElabM (Array (String × String)) := do
  let is := pubIndicesOf b i
  let values := repackIdx b i
  let mut pairs : Array (Name × Syntax) := #[]
  let mut out := #[]
  for (x, v) in is.zip values do
    if x.proof then out := out.push ("_ir_pf_" ++ x.name.toString, ← text (subst x.type pairs))
    pairs := pairs.push (x.name, ← parseTerm v)
  return out
/-- The arity of carrier `i` as written, as binders. -/
private def pubArity (b : Block) (i : Nat) (implicit := false) : CommandElabM String := do
  let bs ← (pubIndicesOf b i).mapM fun x => do
    let d := x.name.toString ++ " : " ++ (← text x.type)
    return if implicit then "{" ++ d ++ "}" else par d
  return join bs
/-- `X params idx`. -/
private def typeAt (b : Block) (i : Nat) (idx : Array String) : String :=
  let m := b.members[i]!
  if b.params.isEmpty && idx.isEmpty then m.name.toString else withParams b ("@" ++ m.name.toString) idx

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
        emit (m.doc ++ "@[reducible] def " ++ m.name.toString ++ " " ++ (← carrierParamsDecl b) ++ " " ++ (← pubArity b i) ++ " : Prop := " ++ withAnonParams b (wfName m) ppi)
      else if b.wf then
        emit (m.doc ++ "@[reducible] def " ++ m.name.toString ++ " " ++ (← carrierParamsDecl b) ++ " " ++ (← pubArity b i) ++ " : Type (" ++ m.level ++ "+1) := { _ir_a : Mumi.IR.Graph.Carrier " ++ withAnonParams b (graphName m) ppi ++ " // " ++ withAnonParams b (wfName m) (ppi ++ #["_ir_a.1", "_ir_a.2"]) ++ " }")
      else
        emit (m.doc ++ "@[reducible] def " ++ m.name.toString ++ " " ++ (← carrierParamsDecl b) ++ " " ++ (← pubArity b i) ++ " : Type (" ++ m.level ++ "+1) := Mumi.IR.Graph.Carrier " ++ withAnonParams b (graphName m) ppi)
    | .inr j =>
      let d := b.decoders[j]!
      let idx ← d.idx.mapM fieldDecl
      let node := if b.wf then "_ir_self.1.1." else "_ir_self.1."
      emit (d.doc ++ "@[reducible] def " ++ d.name.toString ++ " " ++ (← decParamsDecl d) ++ " " ++ join idx ++ " : " ++ (← decoderTail d) ++ " := fun _ir_self => " ++ node ++ outField j)
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
      let fields ← c.fields.mapM fun f => fieldDecl { name := f.name, type := f.type, info := f.info }
      let _ := fields
      let result ← c.pubResult.mapM text
      let head := m.name.toString ++ "." ++ c.name.toString ++ " " ++ (← pubParamsDecl b) ++ " " ++ join fields ++ " : " ++ typeAt b i result
      let wfApp := app (wfName m ++ "." ++ c.name.toString) (xs ++ wfs ++ props)
      if m.prop then
        emit (c.doc ++ "theorem " ++ head ++ " := " ++ wfApp)
      else if b.wf then
        emit (c.doc ++ attrs ++ "def " ++ head ++ " := ⟨⟨_, " ++ app (graphName m ++ "." ++ c.name.toString) xs ++ "⟩, " ++ wfApp ++ "⟩")
      else
        emit (c.doc ++ attrs ++ "def " ++ head ++ " := ⟨_, " ++ app (graphName m ++ "." ++ c.name.toString) xs ++ "⟩")

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
/-- `@X.c params xs`: every field, the implicit ones included. -/
private def ctorApp (b : Block) (i ci : Nat) (xs : Array String) :=
  withParams b ("@" ++ b.members[i]!.name.toString ++ "." ++ b.members[i]!.ctors[ci]!.name.toString) xs
private def fieldNames (c : Ctor) := c.fields.map (·.name.toString)
private def fieldsDecl (c : Ctor) : CommandElabM String := do
  return join (← c.fields.mapM fun f => fieldDecl { name := f.name, type := f.type })
/-- The fields of `c` as the public constructor binds them: an implicit one implicit. -/
private def ctorDecl (c : Ctor) : CommandElabM String := do
  return join (← c.fields.mapM fun f => fieldDecl { name := f.name, type := f.type, info := f.info })
private def applyTo (f : String) (xs : Array String) := if xs.isEmpty then f else app f xs

/-- `motive_j idx (f dom)` for the recursive field `f`. -/
private def ihType (f : Field) (name : Option String := none) : CommandElabM String := do
  let some (j, args) := f.target | unreachable!
  let args := if f.pubArgs.size ≥ args.size then f.pubArgs else args
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
      let result ← c.pubResult.mapM text
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
      let hyps := ((← arityWf b i) ++ (← arityProofs b i)).map (fun (n, t) => par (n ++ " : " ++ t)) |>.push
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
  -- each earlier field's public value, for a proof index term to be read at
  let mut pubPairs := propPairs
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
          let recArgs := pArgs b ++ motiveArgs b scope ++ minorArgs b scope ++ (pubIndicesOf b k).map (fun _ => "_")
          ihImages := ihImages.push (← lambda dom (app ("@" ++ recImplName b.members[k]!) (recArgs.push image)))
        else
          ihNames := ihNames.push (ihVar f.name)
          if b.wf then
            let mut ws := #[]
            for (x, t) in b.members[k]!.indices.zip args do
              if let some (j, _) := x.member then ws := ws.push (← pair b src (some j) (subst t propPairs)).2.2
            -- a proof index of the field's type: the term written there, a proof field's conjunct
            for (x, t) in (pubIndicesOf b k).zip f.pubArgs do
              if x.proof then ws := ws.push (← qualifyText b (x.member.map (·.1)) (subst t pubPairs))
            ihImages := ihImages.push (← lambda dom (app (applyDomain (ihVar f.name) dom) (ws.push (applyDomain w dom))))
          else ihImages := ihImages.push (ihVar f.name)
      src := src.push { name := f.name, sem := semVar f.name, graph := f.name.toString, coh := w }
      if dom.isEmpty then pubPairs := pubPairs.push (f.name, ← parseTerm image)
    else if isProofTarget b f.target then
      images := images.push (conjunct inv (conjunctIdx b c f))
    else
      binders := binders.push f.name.toString
      images := images.push f.name.toString
  let idxWf := (← arityWf b i) ++ (← arityProofs b i)
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
  let ps ← pubParamsDecl b
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
      let rest := elimName b m "rec" ++ " " ++ common ++ " " ++ (← pubArity b k (implicit := true)) ++ " (_ir_self : " ++ typeAt b k idx ++ ") : " ++ app (motive k) (idx ++ #["_ir_self"]) ++ " := " ++ app ("@" ++ graphName m ++ ".rec") (gargs ++ pubPairIdx b k idx ++ self)
      let attrs := if compiled then "@[implemented_by " ++ recImplName m ++ ", elab_as_elim] " else "@[elab_as_elim] "
      emitDef attrs rest

/-- The minor premise of a `Prop` member's recursor at constructor `ci`: the
constructor's name, which nothing else of the member's takes. -/
private def propMinor (b : Block) (i ci : Nat) (joint := true) : String := Id.run do
  let m := b.members[i]!
  let c := m.ctors[ci]!
  let props := if joint then (propMembers b).map (b.members[·]!) else #[m]
  -- the `Prop` members share one recursor, so a name two of them use is qualified there
  let count := props.foldl (fun n m => n + (m.ctors.filter (·.name == c.name)).size) 0
  let n := if count == 1 then c.name.toString else m.name.toString.replace "." "_" ++ "_" ++ c.name.toString
  let used := b.params.any (fun p => p.name.toString == n) ||
    props.any (fun m => m.ctors.any (fun c => c.fields.any (fun f => f.name.toString == n))) ||
    props.any (fun m => m.indices.any (fun x => x.name.toString == n))
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
private def propMinorPair (b : Block) (j ci : Nat) (ihs : Bool) (conclName : String) (joint := true) : CommandElabM (String × String) := do
  let m := b.members[j]!
  let c := m.ctors[ci]!
  let mut hyps := #[]
  if ihs then
    for f in c.fields do
      if let some (k, _) := f.target then
        if b.members[k]!.prop then hyps := hyps.push (par (ihVar f.name ++ " : " ++ (← ihType f (some (propMotive b k)))))
  let result ← c.pubResult.mapM text
  let concl := app conclName (result ++ #[ctorApp b j ci (fieldNames c)])
  let decls ← fieldsDecl c
  let ty := if c.fields.isEmpty then concl else "∀ " ++ decls ++ " " ++ join hyps ++ ", " ++ concl
  let pub := par (propMinor b j ci joint ++ " : " ++ ty)
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
  let g := untypedLambda (binders ++ wfs ++ props ++ wfIhs ++ ihBinders ++ tail) (app (propMinor b j ci joint) (images ++ (if ihs then ihImages else #[])))
  return (pub, g)

/-- The `Prop` members' recursors and `casesOn`, from the well-formedness
block's: `rec` joint over the `Prop` members, with a hypothesis at each proof
of one, the data members' predicates at `True`; `casesOn` with one motive. -/
private def emitPropRec (b : Block) : CommandElabM Unit := do
  let ps ← pubParamsDecl b
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
    emit (elimAttrs b attrs ++ "theorem " ++ elimName b m "rec" ++ " " ++ ps ++ " " ++ join motives ++ " " ++ join minors ++ " " ++ (← pubArity b j (implicit := true)) ++ " (_ir_self : " ++ typeAt b j idx ++ ") : " ++ app (propMotive b j) (idx ++ #["_ir_self"]) ++ " := " ++ app ("@" ++ wfName m ++ ".rec") (gargs ++ pubPairIdx b j idx ++ #["_ir_self"] ++ pubIdxWf b j idx))
    -- `casesOn`: the member's own constructors, no hypotheses
    let mot := "{motive : ∀ " ++ (← pubArity b j) ++ " (_ir_self : " ++ typeAt b j idx ++ "), Prop}"
    let hyps := (← arityWf b j).map fun (n, t) => par (n ++ " : " ++ t)
    let value := app "motive" (repackIdx b j ++ #["_ir_h"])
    let gmotive := untypedLambda (graphIdxNames b j ++ #["_ir_h"]) (if hyps.isEmpty then value else "∀ " ++ join hyps ++ ", " ++ value)
    let mut cminors := #[]
    let mut cgminors := #[]
    for ci in [:m.ctors.size] do
      let (pub, g) ← propMinorPair b j ci false "motive" (joint := false)
      cminors := cminors.push pub
      cgminors := cgminors.push g
    emit (elimAttrs b "@[elab_as_elim, cases_eliminator] " ++ "theorem " ++ elimName b m "casesOn" ++ " " ++ ps ++ " " ++ mot ++ " " ++ join cminors ++ " " ++ (← pubArity b j (implicit := true)) ++ " (_ir_self : " ++ typeAt b j idx ++ ") : " ++ app "motive" (idx ++ #["_ir_self"]) ++ " := " ++ app ("@" ++ wfName m ++ ".casesOn") (pArgs b ++ #[gmotive] ++ pubPairIdx b j idx ++ #["_ir_self"] ++ cgminors ++ pubIdxWf b j idx))

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
  let text ← pinUniverses (if binders.trim.isEmpty then stmt else "∀ " ++ binders ++ ", " ++ stmt)
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
      let result ← c.pubResult.mapM text
      emitEquation b (d.name.toString ++ "_" ++ c.name.toString) (ps ++ " " ++ (← fieldsDecl c)) (withParams b ("@" ++ d.name.toString) (result ++ #[ctorApp b d.target ci (fieldNames c)]) ++ " = " ++ par (← text d.clauses[ci]!))
  for i in dataMembers b do
    let scope := scope b i
    let common := ps ++ " " ++ (← motiveDecls b scope) ++ " " ++ (← minorDecls b true scope)
    let args := pArgs b ++ motiveArgs b scope ++ minorArgs b scope
    for ci in [:b.members[i]!.ctors.size] do
      let c := b.members[i]!.ctors[ci]!
      let mut ihs := #[]
      for f in c.fields do
        if let some (j, idx) := scopedTarget b scope f then
          let idx ← (if f.pubArgs.size ≥ idx.size then f.pubArgs else idx).mapM text
          ihs := ihs.push (← lambda f.domain (app ("@" ++ elimName b b.members[j]! "rec") (args ++ idx ++ #[applyDomain f.name.toString f.domain])))
      let result ← c.pubResult.mapM text
      emitEquation b (elimName b b.members[i]! "rec" ++ "_" ++ c.name.toString) (common ++ " " ++ (← fieldsDecl c)) (app ("@" ++ elimName b b.members[i]! "rec") (args ++ result ++ #[ctorApp b i ci (fieldNames c)]) ++ " = " ++ app (minor b i ci) (fieldNames c ++ ihs))
    let m := b.members[i]!
    let idx := pubIdxNames b i
    emitDef "@[elab_as_elim] " (elimName b m "recOn" ++ " " ++ (← pubParamsDecl b) ++ " " ++ (← motiveDecls b scope) ++ " " ++ (← pubArity b i (implicit := true)) ++ " (_ir_self : " ++ typeAt b i idx ++ ") " ++ (← minorDecls b true scope) ++ " : " ++ app (motive i) (idx ++ #["_ir_self"]) ++ " := " ++ app ("@" ++ elimName b m "rec") (args ++ idx ++ #["_ir_self"]))

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
    let result ← c.pubResult.mapM text
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
      untypedLambda ((Array.range ((pubIndicesOf b k).size + 1)).map fun _ => "_") "PUnit")
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
  let pubPs ← pubParamsDecl b
  for i in dataMembers b do
    let m := b.members[i]!
    let idx := pubIdxNames b i
    let mot := "{motive : " ++ (← motiveType b i) ++ "}"
    let arity ← pubArity b i (implicit := true)
    let self := "(_ir_self : " ++ typeAt b i idx ++ ")"
    let concl := app "motive" (idx ++ #["_ir_self"])
    let recD ← soloMinors b i true
    let recDRest := elimName b m "recD" ++ " " ++ pubPs ++ " " ++ mot ++ " " ++ arity ++ " " ++ self ++ " " ++ join recD ++ " : " ++ concl ++ " := " ++ app ("@" ++ elimName b m "rec") (soloArgs b i true ++ idx ++ #["_ir_self"])
    emitFirst #[elimAttrs b "@[elab_as_elim, induction_eliminator] " ++ "def " ++ recDRest,
      elimAttrs b "@[elab_as_elim, induction_eliminator] " ++ "noncomputable def " ++ recDRest,
      "@[elab_as_elim] def " ++ recDRest, "@[elab_as_elim] noncomputable def " ++ recDRest]
    let minors ← soloMinors b i false
    let minorNames := (Array.range m.ctors.size).map (minor b i)
    let casesRest := elimName b m "casesOn" ++ " " ++ pubPs ++ " " ++ mot ++ " " ++ arity ++ " " ++ self ++ " " ++ join minors ++ " : " ++ concl ++ " := " ++ app ("@" ++ elimName b m "rec") (soloArgs b i false ++ idx ++ #["_ir_self"])
    emitFirst #[elimAttrs b "@[elab_as_elim, cases_eliminator] " ++ "def " ++ casesRest,
      elimAttrs b "@[elab_as_elim, cases_eliminator] " ++ "noncomputable def " ++ casesRest,
      "@[elab_as_elim] def " ++ casesRest, "@[elab_as_elim] noncomputable def " ++ casesRest]
    emitDef "@[elab_as_elim] " (elimName b m "cases" ++ " " ++ pubPs ++ " " ++ mot ++ " " ++ join minors ++ " " ++ arity ++ " " ++ self ++ " : " ++ concl ++ " := " ++ app ("@" ++ elimName b m "casesOn") (pArgs b ++ #["motive"] ++ idx ++ #["_ir_self"] ++ minorNames))
    for ci in [:m.ctors.size] do
      let c := m.ctors[ci]!
      let result ← c.pubResult.mapM text
      emitEquation b (elimName b m "casesOn" ++ "_" ++ c.name.toString) (ps ++ " " ++ mot ++ " " ++ join minors ++ " " ++ (← fieldsDecl c)) (app ("@" ++ elimName b m "casesOn") (pArgs b ++ #["motive"] ++ result ++ #[ctorApp b i ci (fieldNames c)] ++ minorNames) ++ " = " ++ app (minor b i ci) (fieldNames c))

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
  for x in pubIndicesOf b k do
    -- the raw index gets a name of its own, so that a field of the same name
    -- can be bound beside it
    let n := "_ir_idx_" ++ x.name.toString
    if x.proof then
      -- a proof: a component of its own, which the certificate does not take
      comps := comps.push (n, ← text (subst x.type pairs))
      pub := pub.push n
      pairs := pairs.push (x.name, mkIdent (Name.mkSimple n))
    else if let some (j, args) := x.member then
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
  let np := if h.isOfKind ``Parser.Term.dotIdent then 0 else b.params.size
  unless args.size == np + c.fields.size do return t
  let before := (← get).size
  let mut out := args.extract 0 np
  for (f, a) in c.fields.zip (args.extract np args.size) do
    out := out.push (← match f.target with
      | some (j, _) => flattenArg b (some j) dom a
      | none => pure a)
  let texts ← (out.mapM text : CommandElabM (Array String))
  let t ← parseTerm (app (← text h) texts)
  if conclusion && (← get).size > before then hide b k c (out.extract np out.size) dom t (arg := false) else return t

/-- An argument of carrier `expect`: a constructor application becomes a hidden
field. -/
private partial def flattenArg (b : Block) (expect : Option Nat) (dom : Array Binder) (a : Syntax) :
    StateT (Array Field) CommandElabM Syntax := do
  if (ctorRef? b expect (unapp a).1).isNone then return a
  let t ← flattenTop b expect false dom a
  let (h, args) := unapp t
  let some (k, ci) := ctorRef? b expect h | return a
  let np := if h.isOfKind ``Parser.Term.dotIdent then 0 else b.params.size
  hide b k b.members[k]!.ctors[ci]! (args.extract np args.size) dom t (arg := true)

/-- A hidden field for the application `t` of constructor `c` of carrier `k`
to the field arguments `fargs`, at the indices `c`'s conclusion has there. -/
private partial def hide (b : Block) (k : Nat) (c : Ctor) (fargs : Array Syntax) (dom : Array Binder) (t : Syntax) (arg : Bool) :
    StateT (Array Field) CommandElabM Syntax := do
  let pairs := (c.fields.zip fargs).map fun (f, x) => (f.name, x)
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
        emitL (m.doc ++ "@[reducible] def " ++ m.name.toString ++ " " ++ (← carrierParamsDecl b) ++ " " ++ (← pubArity b k) ++ " : Prop := " ++ withAnonParams b (goodName m) gargs)
        continue
      emitL (m.doc ++ "def " ++ m.name.toString ++ " " ++ (← carrierParamsDecl b) ++ " " ++ (← pubArity b k) ++ " : Type " ++ m.level ++ " := { _ir_a : " ++ app (rawName m) (anonArgs b) ++ " // " ++ withAnonParams b (goodName m) (gargs ++ #["_ir_a"]) ++ " }")
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
      emitDefL (d.doc ++ "@[reducible] ") (d.name.toString ++ " " ++ (← decParamsDecl d) ++ " " ++ join idx ++ " : " ++ (← decoderTail d) ++ " := fun _ir_self => " ++ par (app (pubSemName m) (anonArgs b ++ d.idx.map (·.name.toString) ++ #["_ir_self"])) ++ "." ++ outField j)
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
      let result ← c.pubResult.mapM text
      -- the certificate's constructor takes the block's parameters implicitly, as any constructor does
      if m.prop then
        emitL (c.doc ++ "theorem " ++ m.name.toString ++ "." ++ c.name.toString ++ " " ++ (← pubParamsDecl b) ++ " " ++ (← ctorDecl c) ++ " : " ++ typeAt b k result ++ " := " ++ app (goodName m ++ "." ++ c.name.toString) gargs)
        continue
      emitDefL c.doc (m.name.toString ++ "." ++ c.name.toString ++ " " ++ (← pubParamsDecl b) ++ " " ++ (← ctorDecl c) ++ " : " ++ typeAt b k result ++ " := ⟨" ++ withParams b (rawName m ++ "." ++ c.name.toString) raw ++ ", " ++ app (goodName m ++ "." ++ c.name.toString) gargs ++ "⟩")
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
    for x in pubIndicesOf b k do
      let n := x.name.toString
      if x.proof then
        -- a proof on each side, which the match generalises: the two are one
        binders := binders.push (par (n ++ " : " ++ (← text (subst x.type pairs))))
        binders := binders.push (par (n ++ "' : " ++ (← text (subst x.type pairs'))))
        discr := discr.push (n ++ "'")
        pats := pats.push "_"
        pub := pub.push n
        pub' := pub'.push (n ++ "'")
        pairs := pairs.push (x.name, mkIdent x.name)
        pairs' := pairs'.push (x.name, mkIdent (Name.mkSimple (n ++ "'")))
      else if let some (j, args) := x.member then
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
          let args := if f.pubArgs.size ≥ args.size then f.pubArgs else args
          let pdom := f.domain.map fun x => { x with type := subst x.type pubPairs }
          let pargs ← ((if f.pubArgs.size ≥ args.size then f.pubArgs else args).map (subst · pubPairs)).mapM text
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
      for (x, t) in (pubIndicesOf b k).zip c.pubResult do
        let pt ← qualifyText b (x.member.map (·.1)) (subst t pubPairs)
        if x.proof then
          -- a proof: the motive's and the conclusion's, which is no conjunct of the shape
          castArgs := castArgs.push ("_ir_idx_" ++ x.name.toString) |>.push pt
          continue
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
    let margs ← motiveArgsAt b k ((pubIndicesOf b k).map fun x => mkIdent x.name)
    let common := (← pubParamsDecl b) ++ " " ++ (← motiveDecls b scope) ++ " " ++ (← minorDecls b true scope)
    emitDefL "@[elab_as_elim] " (elimName b m "rec" ++ " " ++ common ++ " " ++ (← pubArity b k (implicit := true)) ++ " (_ir_self : " ++ typeAt b k idx ++ ") : " ++ app (motive k) (idx ++ #["_ir_self"]) ++ " := " ++ withParams b ("@" ++ indName b g) (motiveArgs b scope ++ minorArgs b scope ++ #[sortValue b k, "_ir_self.val", packTuple margs, "_ir_self.property"]))
where
  /-- A lambda over the binders' names alone. -/
  lambdaN (bs : Array Binder) (body : String) : String :=
    if bs.isEmpty then body else par ("fun " ++ join (bs.map fun x => x.name.toString) ++ " => " ++ body)
  /-- The arguments the motive at carrier `j` takes at public index terms:
  `.val` and `.property` of an index of carrier type, the value of a plain one. -/
  motiveArgsAt (b : Block) (j : Nat) (args : Array Syntax) : CommandElabM (Array String) := do
    let mut out := #[]
    for (y, t) in (pubIndicesOf b j).zip args do
      if y.proof then out := out.push (← text t)
      else if let some (i, _) := y.member then
        let t ← qualifyText b (some i) t
        out := out.push (par t ++ ".val") |>.push (par t ++ ".property")
      else out := out.push (← text t)
    return out

/-- A `Prop` member's minor premise at the written universe, public and as
the certificates' recursor takes it.  The latter is a proof, so it is closed
by tactic: the equations pinning hidden conclusion fields substituted, the
written minor premise applied at the public values of the fields, and a
hypothesis at the certificates of its field's indices. -/
private def lowerPropMinor (b : Block) (j ci : Nat) (ihs : Bool) (conclName : String) (joint := true) : CommandElabM (String × String) := do
  let m := b.members[j]!
  let c := m.ctors[ci]!
  let mut hyps := #[]
  if ihs then
    for f in c.fields do
      if let some (k, _) := f.target then
        if b.members[k]!.prop then hyps := hyps.push (par (ihVar f.name ++ " : " ++ (← ihType f (some (propMotive b k)))))
  let result ← c.pubResult.mapM text
  let concl := app conclName (result ++ #[ctorApp b j ci (fieldNames c)])
  let decls ← fieldsDecl c
  let ty := if c.fields.isEmpty then concl else "∀ " ++ decls ++ " " ++ join hyps ++ ", " ++ concl
  let pub := par (propMinor b j ci joint ++ " : " ++ ty)
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
        let pargs ← ((if f.pubArgs.size ≥ args.size then f.pubArgs else args).map (subst · pubPairs)).mapM text
        lets := lets ++ "let " ++ pubVar f.name ++ " : " ++ (← forallS pdom (typeAt b k pargs)) ++ " := " ++ (← lambda pdom ("⟨" ++ applyDomain f.name.toString f.domain ++ ", " ++ applyDomain (hVar f.name) f.domain ++ "⟩")) ++ "\n      "
        images := images.push (pubVar f.name)
        pubPairs := pubPairs.push (f.name, mkIdent (Name.mkSimple (pubVar f.name)))
    else images := images.push f.name.toString
  let eqs := (r.names.filter (·.2 == .eq)).map (·.1)
  let substs := if eqs.isEmpty then "" else "subst " ++ join eqs ++ "; "
  let body := "by " ++ substs ++ "exact\n      " ++ lets ++ app (propMinor b j ci joint) (images ++ (if ihs then ihImages else #[]))
  let g := if binders.isEmpty then par body else untypedLambda binders body
  return (pub, g)

/-- The `Prop` members' recursors and `casesOn` at the written universe, from
the certificates' joint recursor: a data member's certificate at the motive
`True`, a `Prop` member's at its public motive under the certificates of its
indices, which make the public values of those. -/
private def emitLowerPropRec (b : Block) : CommandElabM Unit := do
  let ps ← pubParamsDecl b
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
    emitL (elimAttrs b attrs ++ "theorem " ++ elimName b m "rec" ++ " " ++ ps ++ " " ++ join motives ++ " " ++ join minors ++ " " ++ (← pubArity b j (implicit := true)) ++ " (_ir_self : " ++ typeAt b j idx ++ ") : " ++ app (propMotive b j) (idx ++ #["_ir_self"]) ++ " := " ++ app ("@" ++ goodName m ++ ".rec") (gargs ++ gIdx ++ #["_ir_self"] ++ certs))
    let mot := "{motive : ∀ " ++ (← pubArity b j) ++ " (_ir_self : " ++ typeAt b j idx ++ "), Prop}"
    let mut cminors := #[]
    let mut cgminors := #[]
    for ci in [:m.ctors.size] do
      let (pub, g) ← lowerPropMinor b j ci false "motive" (joint := false)
      cminors := cminors.push pub
      cgminors := cgminors.push g
    emitL (elimAttrs b "@[elab_as_elim, cases_eliminator] " ++ "theorem " ++ elimName b m "casesOn" ++ " " ++ ps ++ " " ++ mot ++ " " ++ join cminors ++ " " ++ (← pubArity b j (implicit := true)) ++ " (_ir_self : " ++ typeAt b j idx ++ ") : " ++ app "motive" (idx ++ #["_ir_self"]) ++ " := " ++ app ("@" ++ goodName m ++ ".casesOn") (pArgs b ++ #[← gmotive j "motive"] ++ gIdx ++ #["_ir_self"] ++ cgminors ++ certs))

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

/-- Whether `s` has an implicit binder anywhere. -/
private partial def hasImplicit (s : Syntax) : Bool :=
  s.isOfKind ``Parser.Term.implicitBinder || s.isOfKind ``Parser.Term.strictImplicitBinder ||
    s.isOfKind ``Parser.Term.instBinder || s.getArgs.any hasImplicit

/-- Whether a block needs this path: some carrier is indexed, or a binder is implicit. -/
def isIndexed (elems : Array Syntax) : CommandElabM Bool := do
  for e in elems do
    let d := e[1]
    if d.isOfKind ``Parser.Command.«inductive» then
      let (_, result) ← signature d[2]
      unless (unparen result).isOfKind ``Parser.Term.type do return true
    if hasImplicit e then return true
  return false

def elaborate (elems : Array Syntax) : CommandElabM Unit := do
  let b ← readBlock elems
  let b := { b with elimPrefix := ← nestedPrefix.get }
  blockConsts.set {}
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


/-! ## Nested occurrences

A carrier occurring inside another inductive type, `(fs : List U)`, is what Lean
calls a nested occurrence, and the kernel takes one by specialising the outer
type to the block: a copy `U.nested_List_1` with `nil` and `cons (head : U)
(tail : U.nested_List_1)`, declared with the block.  Here the copy is a carrier
of the block like any other, and the block is elaborated with every nested
application replaced by its copy -- a decoder over `List U` becoming one over
the copy, its `[]` and `a :: as` patterns the copy's constructors.  What the
writer sees is then stated over the originals, as `Mumi.IndInd` does for a
data copy: `ofOrig` and `toOrig` translate, the constructor `U.tuple` takes a
`List U`, the decoder `Els` is over `List U`, and `U.rec` has a motive for
`List U` with cases for `[]` and `::`, `U.rec_1` entering the recursion there.
The block's own eliminators, over the copies, keep the names `X._nested_rec`
and so on.

A value stores the copy, so the recursor's rule at a constructor with a nested
field holds as an equation, `U.rec_tuple`, proved through `toOrig (ofOrig fs)
= fs`; at a closed list it is `rfl`.  Every other rule, and every decoder
equation, is definitional. -/

/-- A nested application `I args` of the block's carriers and its copy. -/
structure Nesting where
  /-- `I args` as written. -/
  orig : String
  ind : Name
  args : Array String
  copy : Name
  deriving Inhabited

/-- What denesting did to the block. -/
structure Denested where
  /-- The block with every nested application replaced by its copy. -/
  elems : Array Syntax
  /-- The block as written. -/
  original : Array Syntax
  nestings : Array Nesting
  /-- `(member, constructor)` of each constructor with a nested field, declared as `_nested_c`. -/
  ctors : Array (Name × Name)
  /-- Each decoder over a nested application, declared as `_nested_d`, and the nesting. -/
  decoders : Array (Name × Nat)
  deriving Inhabited


private def hidden (n : Name) : Name := Name.mkSimple ("_nested_" ++ n.toString)

/-- `I args` where `s` is an application of an inductive type declared before
the block, not indexed, to arguments mentioning the carriers `members`. -/
private def nestedApp? (members : Array Name) (s : Syntax) : CommandElabM (Option (Name × Array Syntax)) := do
  let s := unparen s
  -- a notation for one, `U × U`, as what it stands for
  let s ← if (s.getKind.toString.startsWith "«term") && mentions s members then liftMacroM (expandMacros s) else pure s
  let (h, args) := unapp s
  unless h.isIdent && !members.contains h.getId && mentions s members do return none
  let some ind ← (try some <$> resolveGlobalConstNoOverload h catch _ => pure none) | return none
  let some (.inductInfo info) := (← getEnv).find? ind | return none
  unless args.size == info.numParams do return none
  unless info.numIndices == 0 do
    throwErrorAt s "IR prototype does not yet take a carrier nested in an indexed family"
  return some (ind, args)

/-- The fields of `I`'s constructor `ctor` at the parameters `args`, as binders
written as text: Lean's own names, the parameters replaced by the arguments. -/
private def ctorFieldsAt (ind ctor : Name) (args : Array Syntax) : CommandElabM (Array (Name × String)) := do
  let some (.inductInfo info) := (← getEnv).find? ind | throwError "not an inductive: {ind}"
  let some ci := (← getEnv).find? ctor | throwError "unknown constructor {ctor}"
  let raw ← liftTermElabM do
    Meta.forallTelescope ci.type fun xs _ => do
      let ps := xs.extract 0 info.numParams
      let fs := xs.extract info.numParams xs.size
      let pnames ← ps.mapM fun p => return (← p.fvarId!.getDecl).userName
      let out ← fs.mapM fun f => do
        let d ← f.fvarId!.getDecl
        let stx ← PrettyPrinter.delab d.type
        return (d.userName.eraseMacroScopes, stx.raw)
      return (pnames, out)
  let (pnames, out) := raw
  let pairs := pnames.zip args |>.map fun (n, a) => (n, a)
  out.mapM fun (n, t) => do return (n, ← text (subst t pairs))

/-- `s` with every nested application the table names replaced by its copy,
and each new one added to the table.  `params` are the copies' arguments. -/
private partial def replaceNested (members : Array Name) (first : Name) (params : String)
    (table : IO.Ref (Array (String × Nesting))) (s : Syntax) : CommandElabM Syntax := do
  if let some (ind, args) ← nestedApp? members s then
    let key ← text (unparen s)
    let tbl ← table.get
    let n ← match tbl.find? (·.1 == key) with
      | some (_, n) => pure n
      | none =>
        let copy := first ++ Name.mkSimple ("nested_" ++ ind.getString! ++ "_" ++ toString (tbl.size + 1))
        let n : Nesting := { orig := key, ind, args := ← args.mapM text, copy }
        table.modify (·.push (key, n))
        pure n
    return ← parseTerm (if params.isEmpty then n.copy.toString else "(" ++ n.copy.toString ++ " " ++ params ++ ")")
  match s with
  | .node info k xs => return .node info k (← xs.mapM (replaceNested members first params table))
  | _ => return s

/-- `s` with the qualified and dotted names of the renamed constructors, and
the names of the renamed decoders, given their hidden names. -/
private partial def renameHidden (ctors : Array (Name × Name)) (decoders : Array Name) (s : Syntax) : Syntax :=
  if s.isIdent then
    let n := s.getId
    if decoders.contains n then mkIdentFrom s (hidden n)
    else match ctors.find? (fun (m, c) => n == m ++ c) with
      | some (m, c) => mkIdentFrom s (m ++ hidden c)
      | none => s
  else if s.isOfKind ``Parser.Term.dotIdent && ctors.any (·.2 == s[1].getId) then
    s.setArg 1 (mkIdentFrom s[1] (hidden s[1].getId))
  else match s with
    | .node info k xs => .node info k (xs.map (renameHidden ctors decoders))
    | _ => s

/-- A decoder's constructor pattern over a nested application as one over its
copy: `[]` as `.nil`, `a :: as` as `.cons a as`, whatever notation it uses. -/
private def copyPattern (n : Nesting) (p : Syntax) : CommandElabM Syntax := do
  let p' ← liftMacroM (expandMacros p)
  let (h, args) := unapp p'
  let short? : Option Name ← do
    if h.isOfKind ``Parser.Term.dotIdent then pure (some h[1].getId)
    else if h.isIdent then
      match ← (try some <$> resolveGlobalConstNoOverload h catch _ => pure none) with
      | some c => pure (if c.getPrefix == n.ind then some (Name.mkSimple c.getString!) else none)
      | none => pure none
    else pure none
  let some short := short? | throwErrorAt p "Expected a constructor of `{n.ind}` here"
  parseTerm (app ("." ++ short.toString) (← args.mapM text))

/-- The block with its nested applications replaced by copies, and the copies
declared as carriers of it, or `none` where there is no nested application. -/
def denest (elems : Array Syntax) : CommandElabM (Option Denested) := do
  let inductives := elems.filter (·[1].isOfKind ``Parser.Command.«inductive»)
  if inductives.isEmpty then return none
  let members := inductives.map (·[1][1][0].getId)
  let first := members[0]!
  let d0 := inductives[0]![1]
  let (ps, _) ← signature d0[2]
  -- the copies take the block's parameters, explicit ones as arguments
  let paramsText := String.intercalate " " ((ps.filter (·.info == .default)).map (·.name.toString)).toList
  let paramsDecl := String.intercalate " " (d0[2][0].getArgs.map fun x => (x.reprint.getD "").trimAscii.toString).toList
  let table ← IO.mkRef (#[] : Array (String × Nesting))
  -- the constructors with a nested field, and the decoders over a nested application
  let mut ctors : Array (Name × Name) := #[]
  for e in inductives do
    let d := e[1]
    for c in d[4].getArgs do
      let (bs, result) ← signature c[4]
      let (tail, _) ← telescope result bs.size
      for f in bs ++ tail do
        let (_, r) ← telescope f.type
        if (← nestedApp? members r).isSome then
          ctors := ctors.push (d[1][0].getId, c[3].getId)
          break
  let mut decoders : Array Name := #[]
  for e in elems do
    let d := e[1]
    if d.isOfKind ``Parser.Command.definition then
      let (_, ty) ← signature d[2]
      let (bs, _) ← telescope ty
      if let some x := bs.back? then
        if (← nestedApp? members x.type).isSome then decoders := decoders.push d[1][0].getId
  if ctors.isEmpty && decoders.isEmpty then return none
  -- rewrite: names first, then the nested applications
  let mut out := #[]
  for e in elems do
    let e := renameHidden ctors decoders e
    -- the declared name itself
    let e := if e[1].isOfKind ``Parser.Command.«inductive» then
        let d := e[1]
        let cs := d[4].getArgs.map fun c =>
          if ctors.contains (d[1][0].getId, c[3].getId) then c.setArg 3 (mkIdentFrom c[3] (hidden c[3].getId)) else c
        e.setArg 1 (d.setArg 4 (mkNullNode cs))
      else e
    out := out.push (← replaceNested members first paramsText table e)
  -- the decoders' patterns over a nested application
  let mut decoderNestings : Array (Name × Nat) := #[]
  for i in [:out.size] do
    let d := out[i]![1]
    unless d.isOfKind ``Parser.Command.definition do continue
    let name := d[1][0].getId
    unless decoders.any (hidden · == name) do continue
    let (_, ty) ← signature d[2]
    let (bs, _) ← telescope ty
    let major := (unapp bs.back!.type).1
    let tbl ← table.get
    let some ni := tbl.findIdx? (·.2.copy == major.getId) | throwErrorAt ty "IR decoder over a nested application not understood"
    let n := tbl[ni]!.2
    decoderNestings := decoderNestings.push (decoders.find? (hidden · == name) |>.get!, ni)
    let alts := d[3][0][0][0].getArgs
    let alts ← alts.mapM fun alt => do
      let pats := alt[1][0].getSepArgs
      let last := pats.back!
      let last' ← copyPattern n last
      return alt.setArg 1 (replaceStx (fun s => if s == last then some last' else none) alt[1])
    out := out.set! i (out[i]!.setArg 1 (d.setArg 3 (d[3].setArg 0 (d[3][0].setArg 0 (d[3][0][0].setArg 0 (mkNullNode alts))))))
  -- the copies, each a carrier of the block; a copy's fields may nest further
  let level ← do
    let (_, r) ← signature d0[2]
    let (_, r) ← telescope r
    text r
  let mut done := 0
  let mut copies := #[]
  while done < (← table.get).size do
    let n := (← table.get)[done]!.2
    done := done + 1
    let some (.inductInfo info) := (← getEnv).find? n.ind | unreachable!
    let args ← n.args.mapM parseTerm
    let mut cs := #[]
    for ctor in info.ctors do
      let fs ← ctorFieldsAt n.ind ctor args
      let mut binders := #[]
      for (fname, fty) in fs do
        let fty ← replaceNested members first paramsText table (← parseTerm fty)
        binders := binders.push ("(" ++ fname.toString ++ " : " ++ (← text fty) ++ ")")
      let result := if paramsText.isEmpty then n.copy.toString else n.copy.toString ++ " " ++ paramsText
      cs := cs.push ("  | " ++ ctor.getString! ++ " " ++ String.intercalate " " binders.toList ++ " : " ++ result)
    let src := "inductive " ++ n.copy.toString ++ " " ++ paramsDecl ++ " : " ++ level ++ " where\n" ++ String.intercalate "\n" cs.toList
    let .ok stx := Parser.runParserCategory (← getEnv) `command src
      | throwError "IR frontend generated an invalid copy:\n{src}"
    copies := copies.push stx
  return some { elems := out ++ copies, original := elems, nestings := (← table.get).map (·.2),
                ctors, decoders := decoderNestings }

/-- Whether `c` may continue a name, a `.` included. -/
private def qualChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\'' || c == '.' || c.val > 127

/-- `s` with every occurrence of `old` that is not part of a longer name
replaced by `new`. -/
private def replaceName (s old new : String) : String := Id.run do
  let a := s.toList.toArray
  let o := old.toList.toArray
  let mut out := ""
  let mut i := 0
  while i < a.size do
    if a.extract i (i + o.size) == o && (i == 0 || !qualChar a[i-1]!) &&
        (i + o.size == a.size || !qualChar a[i + o.size]!) then
      out := out ++ new
      i := i + o.size
    else
      out := out.push a[i]!
      i := i + 1
  return out

/-- Text the block's generators wrote over the copies, over the originals: a
copy as the application it copies, a copy's constructor as the original's, a
hidden constructor or decoder by its own name. -/
private def deCopy (b : Block) (dn : Denested) (s : String) : CommandElabM String := do
  let pa := pArgs b
  let paS := if pa.isEmpty then "" else " " ++ join pa
  let mut s := s
  for n in dn.nestings do
    let some (.inductInfo info) := (← getEnv).find? n.ind | continue
    for ctor in info.ctors do
      s := replaceName s ("@" ++ n.copy.toString ++ "." ++ ctor.getString! ++ paS)
        ("@" ++ ctor.toString ++ " " ++ join (n.args.map par))
    s := replaceName s ("@" ++ n.copy.toString ++ paS) (par n.orig)
    s := replaceName s (n.copy.toString ++ paS) (par n.orig)
  for (m, c) in dn.ctors do
    s := replaceName s (m ++ hidden c).toString (m ++ c).toString
    s := replaceName s (hidden c).toString c.toString
  for (d, _) in dn.decoders do
    s := replaceName s (hidden d).toString d.toString
  return s

/-- The public API of a denested block, over the originals. -/
def emitNestedPublic (dn : Denested) : CommandElabM Unit := do
  let lower := mumi.mahlo.get (← getOptions)
  let b ← readBlock dn.elems
  let b := { b with lower, elimPrefix := "_nested_" }
  let dc (s : String) := deCopy b dn s
  let ps ← paramsDecl b
  let pubPs ← pubParamsDecl b
  let pa := pArgs b
  let scope := dataMembers b
  let copyOf (k : Nat) : Option Nat := dn.nestings.findIdx? (·.copy == b.members[k]!.name)
  let memberOf (i : Nat) : Nat := (b.members.findIdx? (·.name == dn.nestings[i]!.copy)).getD 0
  let first := b.members[0]!.name.toString
  let recOf (k : Nat) : String := match copyOf k with
    | some i => first ++ ".rec_" ++ toString (i + 1)
    | none => b.members[k]!.name.toString ++ ".rec"
  let copyName (i : Nat) := dn.nestings[i]!.copy.toString
  let orig (i : Nat) := par dn.nestings[i]!.orig
  let at_ (n : String) (xs : Array String) := app ("@" ++ n) (pa ++ xs)
  -- an eliminator at a universe of its own: not the block's, which `emit` pins
  let ns ← getCurrNamespace
  let free (n : String) := "_root_." ++ (ns ++ n.toName).toString
  let motiveArgs := motiveArgs b scope
  let minorArgs ← (minorArgs b scope).mapM dc
  let motives ← dc (← motiveDecls b scope)
  let minors ← dc (← minorDecls b true scope)
  -- the copies, the inner ones (found later) first
  let order := (Array.range dn.nestings.size).reverse
  -- a copy-typed field of a constructor: its copy
  let copyField (f : Field) : Option Nat := f.target.bind fun (j, _) => if f.domain.isEmpty then copyOf j else none
  for i in order do
    let k := memberOf i
    let m := b.members[k]!
    let C := copyName i
    -- `ofOrig`, by structural recursion on the original
    let mut cs := #[]
    for ci in [:m.ctors.size] do
      let c := m.ctors[ci]!
      let conv := c.fields.map fun f => match copyField f with
        | some i' => at_ (copyName i' ++ ".ofOrig") #[f.name.toString]
        | none => f.name.toString
      cs := cs.push ("  | ." ++ c.name.toString ++ " " ++ join (fieldNames c) ++ " => " ++ ctorApp b k ci conv)
    emitDef "" (C ++ ".ofOrig " ++ pubPs ++ " : " ++ orig i ++ " → " ++ typeAt b k #[] ++ "\n" ++ String.intercalate "\n" cs.toList)
    -- `toOrig`, by the copy's own recursion
    let mut ms := #[]
    for ci in [:m.ctors.size] do
      let c := m.ctors[ci]!
      let own := c.fields.filter fun f => (dataTarget b f).any (·.1 == k)
      let conv := c.fields.map fun f =>
        if (dataTarget b f).any (·.1 == k) then ihVar f.name
        else match copyField f with
          | some i' => at_ (copyName i' ++ ".toOrig") #[f.name.toString]
          | none => f.name.toString
      ms := ms.push (untypedLambda (fieldNames c ++ own.map (ihVar ·.name)) (← dc (ctorApp b k ci conv)))
    emitDef "" (C ++ ".toOrig " ++ pubPs ++ " (_ir_c : " ++ typeAt b k #[] ++ ") : " ++ orig i ++ " := " ++
      app ("@" ++ free (elimName b m "recD")) (pa ++ #["(fun _ => " ++ orig i ++ ")", "_ir_c"] ++ ms))
    let mut eqs := #[]
    for ci in [:m.ctors.size] do
      let c := m.ctors[ci]!
      let conv := c.fields.map fun f => match copyField f with
        | some i' => at_ (copyName i' ++ ".toOrig") #[f.name.toString]
        | none => f.name.toString
      let name := C ++ ".toOrig_" ++ c.name.toString
      eqs := eqs.push name
      emitEquation b name (ps ++ " " ++ (← fieldsDecl c)) (at_ (C ++ ".toOrig") #[ctorApp b k ci (fieldNames c)] ++ " = " ++ (← dc (ctorApp b k ci conv)))
    -- the round trips; an inner copy's are already there
    let inner := (List.range dn.nestings.size).filter (· > i)
    let there := inner.map fun i' => copyName i' ++ ".toOrig_ofOrig"
    let back := inner.map fun i' => copyName i' ++ ".ofOrig_toOrig"
    emit ("theorem " ++ C ++ ".toOrig_ofOrig " ++ pubPs ++ " (_ir_x : " ++ orig i ++ ") : " ++
      at_ (C ++ ".toOrig") #[at_ (C ++ ".ofOrig") #["_ir_x"]] ++ " = _ir_x := by\n  induction _ir_x <;> simp only [" ++
      String.intercalate ", " (eqs.toList ++ [C ++ ".ofOrig"] ++ there ++ ["*"]) ++ "]")
    let mut bs := #[]
    for ci in [:m.ctors.size] do
      let c := m.ctors[ci]!
      let own := c.fields.filter fun f => (dataTarget b f).any (·.1 == k)
      bs := bs.push (untypedLambda (fieldNames c ++ own.map (ihVar ·.name))
        ("(by simp only [" ++ String.intercalate ", " (eqs.toList ++ [C ++ ".ofOrig"] ++ back ++ ["*"]) ++ "])"))
    emit ("theorem " ++ C ++ ".ofOrig_toOrig " ++ pubPs ++ " (_ir_c : " ++ typeAt b k #[] ++ ") : " ++
      at_ (C ++ ".ofOrig") #[at_ (C ++ ".toOrig") #["_ir_c"]] ++ " = _ir_c := " ++
      app ("@" ++ free (elimName b m "recD")) (pa ++ #["(fun _ir_c => " ++ at_ (C ++ ".ofOrig") #[at_ (C ++ ".toOrig") #["_ir_c"]] ++ " = _ir_c)", "_ir_c"] ++ bs))
  -- the public constructors
  for (mn, cn) in dn.ctors do
    let some k := b.members.findIdx? (·.name == mn) | continue
    let some ci := b.members[k]!.ctors.findIdx? (·.name == hidden cn) | continue
    let c := b.members[k]!.ctors[ci]!
    for f in c.fields do
      if let some (j, _) := f.target then
        if (copyOf j).isSome && !f.domain.isEmpty then
          throwError "IR prototype does not yet take a nested occurrence under binders, as in `{f.name}`"
    let conv := c.fields.map fun f => match copyField f with
      | some i' => at_ (copyName i' ++ ".ofOrig") #[f.name.toString]
      | none => f.name.toString
    let result ← c.pubResult.mapM text
    emitDef (c.doc ++ "@[reducible] ") ((mn ++ cn).toString ++ " " ++ pubPs ++ " " ++ (← dc (← ctorDecl c)) ++ " : " ++
      typeAt b k result ++ " := " ++ ctorApp b k ci conv)
  -- the public decoders over a nested application
  for (dname, i) in dn.decoders do
    let some d := b.decoders.find? (·.name == hidden dname) | continue
    let dargs := d.params.map fun p => if p.anon then p.argText else p.name.toString
    emitDef (d.doc ++ "@[reducible] ") (dname.toString ++ " " ++ (← decParamsDecl d) ++ " : " ++ (← dc (← decoderTail d)) ++
      " := fun _ir_x => " ++ app ("@" ++ (hidden dname).toString) (dargs ++ #[at_ (copyName i ++ ".ofOrig") #["_ir_x"]]))
  -- the decoders' equations at what changed: a hidden constructor, a copy's
  for j in [:b.decoders.size] do
    let d := b.decoders[j]!
    let k := d.target
    let m := b.members[k]!
    let isCopy := (copyOf k).isSome
    for ci in [:m.ctors.size] do
      let c := m.ctors[ci]!
      unless isCopy || dn.ctors.any (fun (mn, cn) => mn == m.name && hidden cn == c.name) do continue
      let result ← c.pubResult.mapM text
      let dargs := d.params.map fun p => if p.anon then p.argText else p.name.toString
      let name := (← dc d.name.toString) ++ "_" ++ (← dc c.name.toString)
      emitEquation b name (← dc (ps ++ " " ++ (← fieldsDecl c)))
        (← dc (app ("@" ++ d.name.toString) (dargs ++ result ++ #[ctorApp b k ci (fieldNames c)]) ++ " = " ++ par (← text d.clauses[ci]!)))
  -- the eliminators
  let common := pubPs ++ " " ++ motives ++ " " ++ minors
  let mut motivesC := #[]
  for j in scope do
    motivesC := motivesC.push (match copyOf j with
      | some i => "(fun (_ir_c : " ++ typeAt b j #[] ++ ") => " ++ app (motive j) #[at_ (copyName i ++ ".toOrig") #["_ir_c"]] ++ ")"
      | none => motive j)
  let pubMinor (j ci : Nat) : CommandElabM String := dc (minor b j ci)
  -- a minor premise of the recursion over the copies, from the public one
  let copyMinor (j ci : Nat) (ihs : Bool) (motiveName : String) : CommandElabM String := do
    let m := b.members[j]!
    let c := m.ctors[ci]!
    let recs := if ihs then c.fields.filter fun f => (scopedTarget b scope f).isSome else #[]
    let binders := fieldNames c ++ recs.map (ihVar ·.name)
    let conv := c.fields.map fun f => match copyField f with
      | some i' => at_ (copyName i' ++ ".toOrig") #[f.name.toString]
      | none => f.name.toString
    let base := app (← pubMinor j ci) (conv ++ recs.map (ihVar ·.name))
    if (copyOf j).isSome then return untypedLambda binders base
    let copies := (Array.range c.fields.size).filter fun x => (copyField c.fields[x]!).isSome
    if copies.isEmpty then return untypedLambda binders base
    -- transported along `ofOrig (toOrig x) = x`, one copy-typed field at a time
    let result ← c.pubResult.mapM text
    let mut v := base
    for x in copies do
      let f := c.fields[x]!
      let i' := (copyField f).get!
      let args := (Array.range c.fields.size).map fun y =>
        let g := c.fields[y]!
        if y == x then "_ir_y"
        else if copies.contains y && y > x then
          let iy := (copyField g).get!
          at_ (copyName iy ++ ".ofOrig") #[at_ (copyName iy ++ ".toOrig") #[g.name.toString]]
        else g.name.toString
      let fam := "(fun _ir_y => " ++ app motiveName (result ++ #[ctorApp b j ci args]) ++ ")"
      v := "(cast (congrArg " ++ fam ++ " " ++ at_ (copyName i' ++ ".ofOrig_toOrig") #[f.name.toString] ++ ") " ++ v ++ ")"
    return untypedLambda binders v
  let mut minorsC := #[]
  for j in scope do
    for ci in [:b.members[j]!.ctors.size] do
      minorsC := minorsC.push (← copyMinor j ci true (motive j))
  -- `X.rec`, for each member written
  for k in scope do
    if (copyOf k).isSome then continue
    let m := b.members[k]!
    let idx := pubIdxNames b k
    emitDef "@[elab_as_elim] " (m.name.toString ++ ".rec " ++ common ++ " " ++ (← pubArity b k (implicit := true)) ++
      " (_ir_self : " ++ typeAt b k idx ++ ") : " ++ app (motive k) (idx ++ #["_ir_self"]) ++ " := " ++
      app ("@" ++ elimName b m "rec") (pa ++ motivesC ++ minorsC ++ idx ++ #["_ir_self"]))
  -- `F.rec_i`, for each copy, by structural recursion on the original
  for i in order do
    let k := memberOf i
    let m := b.members[k]!
    let mut cs := #[]
    for ci in [:m.ctors.size] do
      let c := m.ctors[ci]!
      let mut ihs := #[]
      for f in c.fields do
        if let some (j, args) := scopedTarget b scope f then
          let args ← args.mapM text
          ihs := ihs.push (app ("@" ++ recOf j) (pa ++ motiveArgs ++ minorArgs ++ (if (copyOf j).isSome then #[] else args) ++ #[f.name.toString]))
      cs := cs.push ("  | ." ++ c.name.toString ++ " " ++ join (fieldNames c) ++ " => " ++ app (← pubMinor k ci) (fieldNames c ++ ihs))
    emitDef "@[elab_as_elim] " (recOf k ++ " " ++ common ++ " : (_ir_self : " ++ orig i ++ ") → " ++ app (motive k) #["_ir_self"] ++ "\n" ++
      String.intercalate "\n" cs.toList)
  -- `X.casesOn`, for each member written
  for k in scope do
    if (copyOf k).isSome then continue
    let m := b.members[k]!
    let idx := pubIdxNames b k
    let mot := "{motive : " ++ (← motiveType b k) ++ "}"
    let cminors ← (← soloMinors b k false).mapM dc
    let mut cargs := #[]
    for ci in [:m.ctors.size] do
      cargs := cargs.push (← copyMinor k ci false "motive")
    emitDef "@[elab_as_elim, cases_eliminator] " (m.name.toString ++ ".casesOn " ++ pubPs ++ " " ++ mot ++ " " ++
      (← pubArity b k (implicit := true)) ++ " (_ir_self : " ++ typeAt b k idx ++ ") " ++ join cminors ++ " : " ++
      app "motive" (idx ++ #["_ir_self"]) ++ " := " ++
      app ("@" ++ elimName b m "casesOn") (pa ++ #["motive"] ++ idx ++ #["_ir_self"] ++ cargs))
  -- the rules: at a copy's constructor and at a constructor without nested fields, `rfl`
  let eqBinders := ps ++ " " ++ motives ++ " " ++ minors
  let ihsAt (c : Ctor) : CommandElabM (Array String) := do
    let mut ihs := #[]
    for f in c.fields do
      if let some (j, args) := scopedTarget b scope f then
        let args ← args.mapM text
        ihs := ihs.push (← lambda f.domain (app ("@" ++ recOf j) (pa ++ motiveArgs ++ minorArgs ++
          (if (copyOf j).isSome then #[] else args) ++ #[applyDomain f.name.toString f.domain])))
    return ihs
  for k in scope do
    let m := b.members[k]!
    for ci in [:m.ctors.size] do
      let c := m.ctors[ci]!
      let result ← c.pubResult.mapM text
      let major ← dc (ctorApp b k ci (fieldNames c))
      let lhs := app ("@" ++ recOf k) (pa ++ motiveArgs ++ minorArgs ++ (if (copyOf k).isSome then #[] else result) ++ #[major])
      let rhs := app (← pubMinor k ci) (fieldNames c ++ (← ihsAt c))
      let name := recOf k ++ "_" ++ (← dc c.name.toString)
      let copies := c.fields.filter fun f => (copyField f).isSome
      if (copyOf k).isSome || copies.isEmpty then
        emitEquation b name (eqBinders ++ " " ++ (← dc (← fieldsDecl c))) (lhs ++ " = " ++ rhs)
  -- the copies' recursions agree with the public ones at `ofOrig`, by induction on the original
  for i in order do
    let k := memberOf i
    let m := b.members[k]!
    let C := copyName i
    let copyRec (x : String) := app ("@" ++ elimName b m "rec") (pa ++ motivesC ++ minorsC ++ #[at_ (C ++ ".ofOrig") #[x]])
    let mut alts := #[]
    for ci in [:m.ctors.size] do
      let c := m.ctors[ci]!
      let own := c.fields.filter fun f => (dataTarget b f).any (·.1 == k)
      -- the copy's rule needs `toOrig` unfolded to match: `erw`
      let mut steps := #["simp only [" ++ C ++ ".ofOrig]", "erw [" ++ elimName b m "rec" ++ "_" ++ c.name.toString ++ "]",
        "simp only [" ++ recOf k ++ "_" ++ (← dc c.name.toString) ++ "]"]
      for f in c.fields do
        let some i' := copyField f | continue
        let h := if i' == i then "_ir_ihI_" ++ f.name.toString
          else app ("@" ++ copyName i' ++ ".rec_ofOrig") (pa ++ motiveArgs ++ minorArgs ++ #[f.name.toString])
        steps := steps ++ #["have _ir_E_" ++ f.name.toString ++ " := " ++ at_ (copyName i' ++ ".toOrig_ofOrig") #[f.name.toString],
          "have _ir_H_" ++ f.name.toString ++ " := " ++ h]
      -- argument by argument: a copy-typed field by its round trip, its hypothesis by the agreement
      steps := steps.push "congr 1 <;> first | rfl | assumption | exact HEq.rfl"
      alts := alts.push ("  | " ++ c.name.toString ++ " " ++ join (fieldNames c) ++ " " ++ join (own.map fun f => "_ir_ihI_" ++ f.name.toString) ++
        " =>\n    " ++ String.intercalate "\n    " steps.toList)
    emit ("theorem " ++ C ++ ".rec_ofOrig " ++ common ++ " (_ir_x : " ++ orig i ++ ") : HEq " ++ copyRec "_ir_x" ++ " " ++
      app ("@" ++ recOf k) (pa ++ motiveArgs ++ minorArgs ++ #["_ir_x"]) ++ " := by\n  induction _ir_x with\n" ++ String.intercalate "\n" alts.toList)
  -- the rule at a constructor with a nested field, by those
  for k in scope do
    if (copyOf k).isSome then continue
    let m := b.members[k]!
    for ci in [:m.ctors.size] do
      let c := m.ctors[ci]!
      let copies := c.fields.filter fun f => (copyField f).isSome
      if copies.isEmpty then continue
      let result ← c.pubResult.mapM text
      let major ← dc (ctorApp b k ci (fieldNames c))
      let lhs := app ("@" ++ recOf k) (pa ++ motiveArgs ++ minorArgs ++ result ++ #[major])
      let rhs := app (← pubMinor k ci) (fieldNames c ++ (← ihsAt c))
      let pubCtor ← dc (m.name.toString ++ "." ++ c.name.toString)
      let mut steps := #["simp only [" ++ recOf k ++ ".eq_1, " ++ pubCtor ++ "]", "erw [" ++ elimName b m "rec" ++ "_" ++ c.name.toString ++ "]",
        "try dsimp only", "apply eq_of_heq"]
      for _ in copies do steps := steps.push "refine (cast_heq _ _).trans ?_"
      for f in copies do
        let i' := (copyField f).get!
        steps := steps ++ #["have _ir_E_" ++ f.name.toString ++ " := " ++ at_ (copyName i' ++ ".toOrig_ofOrig") #[f.name.toString],
          "have _ir_H_" ++ f.name.toString ++ " := " ++ app ("@" ++ copyName i' ++ ".rec_ofOrig") (pa ++ motiveArgs ++ minorArgs ++ #[f.name.toString])]
      steps := steps.push "congr 1 <;> first | rfl | assumption | exact HEq.rfl"
      let name := recOf k ++ "_" ++ (← dc c.name.toString)
      emit ("theorem " ++ name ++ " " ++ eqBinders ++ " " ++ (← dc (← fieldsDecl c)) ++ " : " ++ lhs ++ " = " ++ rhs ++
        " := by\n  " ++ String.intercalate "\n  " steps.toList)

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
declared right after what it refers to.  An inductive of a group's universe
that names its carriers joins it, with the groups between. -/
partial def elaborateAny (elems : Array Syntax) : CommandElabM Unit := do
  -- a nested occurrence: the block with copies, then its API over the originals
  if (← Family.nestedPrefix.get).isEmpty then
    if let some dn ← Family.denest elems then
      Family.nestedPrefix.set "_nested_"
      try
        elaborateAny dn.elems
        Family.emitNestedPublic dn
      finally Family.nestedPrefix.set ""
      return
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
  -- an inductive of the same universe naming the carriers of an earlier
  -- induction-recursion joins it, with what lies between, which it may need:
  -- one recursion, as in a `mutual`, and one universe up the only place its
  -- indices can be
  let isIR (g : Array Syntax) := g.any isInductive && g.any (·[1].isOfKind ``Parser.Command.definition)
  let mut i := 0
  while i < groups.size do
    let (comp, l) := groups[i]!
    if !l.isEmpty && !isIR comp then
      let carriers (g : Array Syntax) := (g.filter isInductive).map (·[1][1][0].getId)
      if let some j := (Array.range i).find? fun j =>
          groups[j]!.2 == l && isIR groups[j]!.1 && comp.any (mentions · (carriers groups[j]!.1)) then
        let merged := (groups.extract j (i+1)).flatMap (·.1)
        groups := (groups.extract 0 j).push (merged, l) ++ groups.extract (i+1) groups.size
        i := j + 1
        continue
    i := i + 1
  for (comp, _) in groups do
    let inductives := comp.filter isInductive
    let props ← inductives.filterM isPropInductive
    if inductives.isEmpty || inductives.size == comp.size || props.size == inductives.size then
      -- Lean's own: a block of definitions, or of inductives, with `mutual` taking several
      if h : comp.size = 1 then elabCommand comp[0]
      else elabCommand (mkNode ``Parser.Command.«mutual» #[mkAtom "mutual", mkNullNode comp, mkAtom "end", mkNullNode])
    else if (← Family.isIndexed comp) || !(← Family.nestedPrefix.get).isEmpty then Family.elaborate comp
    else elaborate comp

end Mumi.IndRec
