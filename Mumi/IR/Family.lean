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
  deriving Inhabited

structure Ctor where
  name : Name
  fields : Array Field
  /-- The index arguments of the conclusion. -/
  result : Array Syntax
  deriving Inhabited

structure Member where
  name : Name
  indices : Array Index
  ctors : Array Ctor
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
  level : String
  deriving Inhabited

/-- A variable of carrier type as the graph world sees it: the names of its two halves. -/
structure Source where
  name : Name
  sem : String
  graph : String
  deriving Inhabited

private def aux (n : Name) (suffix := "") : String :=
  (n.getPrefix ++ Name.mkSimple ("_ir_" ++ n.getString! ++ suffix)).toString
private def semName (m : Member) := aux m.name "_Sem"
private def graphName (m : Member) := aux m.name
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
  let mut heads : Array (Name × Array Binder) := #[]
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
      unless result.isOfKind ``Parser.Term.type do
        throwErrorAt result "IR prototype supports carriers declared in Type u, possibly indexed"
      let l ← if result[1].getNumArgs == 0 then pure "0" else pure (result[1][0].reprint.getD "0" |>.trimAscii.toString)
      if heads.isEmpty then params := ps; level := l
      else
        unless ps.size == params.size && (← (ps.zip params).allM fun (a,b) => do return a.name == b.name && (← text a.type) == (← text b.type)) do
          throwErrorAt d "IR prototype requires identical shared parameters on all declarations"
        unless l == level do throwErrorAt result "IR prototype requires all carriers to share the declared universe"
      unless d[6][0].getNumArgs == 0 do throwErrorAt d "IR prototype does not yet support deriving clauses"
      heads := heads.push (d[1][0].getId, idx)
  checkDistinct (params.map (·.name)) globalNames
  for p in params do checkTermBinders (globalNames ++ params.map (·.name)) p.type
  let names := heads.map (·.1)
  -- the arities, now that every carrier's name and arity length are known
  let mut members : Array Member := #[]
  for (n, idx) in heads do
    checkDistinct (idx.map (·.name)) (globalNames ++ params.map (·.name))
    let mut indices := #[]
    for x in idx do
      checkTermBinders (globalNames ++ params.map (·.name) ++ idx.map (·.name)) x.type
      let member := memberApp? names params x.type
      if let some (k, args) := member then
        unless args.size == heads[k]!.2.size do
          throwErrorAt x.type "The carrier `{names[k]!}` takes {heads[k]!.2.size} indices"
      else if mentions x.type names then
        throwErrorAt x.type "An index domain may name a carrier only as that carrier applied to its indices; anything else has to go through a decoder"
      indices := indices.push { name := x.name, type := x.type, member }
    members := members.push { name := n, indices, ctors := #[] }
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

/-- A term of carrier type, as its two halves.  It is a source, a source applied
to arguments, or a constructor application. -/
partial def pair (b : Block) (src : Array Source) (expect : Option Nat) (s : Syntax) :
    CommandElabM (String × String) := do
  if let some (x, ys) := sourceApp? src s then
    if x.sem.isEmpty then throwErrorAt s "A decoder's result may mention the value it is about only through decoders"
    let ys ← ys.mapM (semText b src)
    return (if ys.isEmpty then x.sem else app x.sem ys, if ys.isEmpty then x.graph else app x.graph ys)
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
  let (inner, pairs, split) ← instantiate b src c fargs
  ctorPair b src inner pairs split k ci

/-- The fields of `c` at the arguments `fargs`: sources for the recursive ones,
substitutions for the rest, and the arguments the graph constructor takes. -/
partial def instantiate (b : Block) (src : Array Source) (c : Ctor) (fargs : Array Syntax) :
    CommandElabM (Array Source × Array (Name × Syntax) × Array String) := do
  let mut inner : Array Source := #[]
  let mut pairs : Array (Name × Syntax) := #[]
  let mut split : Array String := #[]
  for (f, a) in c.fields.zip fargs do
    if let some (k, _) := f.target then
      unless f.domain.isEmpty || (unapp a).2.isEmpty || (sourceApp? src a).isSome do
        throwErrorAt a "A function-valued field passed to a constructor here has to be a name"
      let (sa, ga) ← pair b src (some k) a
      inner := inner.push { name := f.name, sem := sa, graph := ga }
      split := split.push sa |>.push ga
    else
      pairs := pairs.push (f.name, a)
      split := split.push (← semText b src a)
  return (inner, pairs, split)

/-- The two halves of `X.c` at fields read as `inner`/`pairs`, whose graph
arguments are `split`. -/
partial def ctorPair (b : Block) (src : Array Source) (inner : Array Source) (pairs : Array (Name × Syntax))
    (split : Array String) (k ci : Nat) : CommandElabM (String × String) := do
  let m := b.members[k]!
  let c := m.ctors[ci]!
  let ctx := src ++ inner
  -- the semantic halves of the conclusion's indices
  let mut semIdx := #[]
  for (x, t) in m.indices.zip c.result do
    let t := subst t pairs
    if let some (j, _) := x.member then semIdx := semIdx.push (← pair b ctx (some j) t).1
    else semIdx := semIdx.push (← semText b ctx t)
  let mut vals := #[]
  for di in [:b.decoders.size] do
    let d := b.decoders[di]!
    if d.target == k then vals := vals.push (← semText b ctx (subst d.clauses[ci]! pairs))
  if vals.isEmpty then vals := #["PUnit.unit"]
  let sem := app ("@" ++ semName m ++ ".mk") (pArgs b ++ semIdx ++ vals)
  -- the graph constructor takes the block's parameters implicitly, as any constructor does
  return (sem, app (graphName m ++ "." ++ c.name.toString) split)

end

/-- The index arguments `args` of carrier `k`, as the graph takes them: two
halves for an index of carrier type, one for a plain one. -/
private def graphIdx (b : Block) (src : Array Source) (k : Nat) (args : Array Syntax) : CommandElabM (Array String) := do
  let mut out := #[]
  for (x, t) in b.members[k]!.indices.zip args do
    if let some (j, _) := x.member then
      let (s, g) ← pair b src (some j) t
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
private def graphArity (b : Block) (i : Nat) : CommandElabM (Array String × Array Source) := do
  let mut out := #[]
  let mut src : Array Source := #[]
  for x in b.members[i]!.indices do
    if let some (k, args) := x.member then
      let sIdx ← semIdx b src k args
      let gIdx ← graphIdx b src k args
      out := out.push (par (semVar x.name ++ " : " ++ withParams b (semName b.members[k]!) sIdx))
      out := out.push (par (x.name.toString ++ " : " ++ withParams b (graphName b.members[k]!) (gIdx ++ #[semVar x.name])))
      src := src.push { name := x.name, sem := semVar x.name, graph := x.name.toString }
    else
      out := out.push (par (x.name.toString ++ " : " ++ (← semText b src x.type)))
  return (out, src)

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
/-- Public index terms, as the graph takes them: `x.1 x.2` for one of carrier type. -/
private def pubPairIdx (b : Block) (i : Nat) (args : Array String) : Array String :=
  (b.members[i]!.indices.zip args).flatMap fun (x, a) =>
    if x.member.isSome then #[par a ++ ".1", par a ++ ".2"] else #[a]
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
    let (arity, src) ← semArity b i
    let mut fields := #[]
    for j in [:b.decoders.size] do
      let d := b.decoders[j]!
      if d.target == i then
        -- the decoder's own index names stand for the arity's
        let pairs := (d.idx.zip m.indices).map fun (x, y) => (x.name, mkIdent y.name)
        let result := subst d.result pairs
        fields := fields.push ("  " ++ outField j ++ " : " ++ (← semText b (src.push { name := d.major, sem := "", graph := "" }) result))
    if fields.isEmpty then fields := #["  _unit : PUnit.{" ++ b.level ++ "+1}"]
    emit ("structure " ++ semName m ++ " " ++ ps ++ " " ++ join arity ++ " : Type (" ++ b.level ++ "+1) where\n" ++ String.intercalate "\n" fields.toList)

/-- The fields of `c` as the graph constructor takes them, and the sources they bind. -/
private def graphFields (b : Block) (c : Ctor) : CommandElabM (Array String × Array Source) := do
  let mut out := #[]
  let mut src : Array Source := #[]
  for f in c.fields do
    if let some (k, args) := f.target then
      let dom ← f.domain.mapM fun x => do return { x with type := ← semantic b src x.type }
      let sIdx ← semIdx b src k args
      let gIdx ← graphIdx b src k args
      out := out.push (par (semVar f.name ++ " : " ++ (← forallS dom (withParams b (semName b.members[k]!) sIdx))))
      out := out.push (par (f.name.toString ++ " : " ++ (← forallS dom (withParams b (graphName b.members[k]!) (gIdx ++ #[applyDomain (semVar f.name) dom])))))
      src := src.push { name := f.name, sem := semVar f.name, graph := f.name.toString }
    else
      out := out.push (par (f.name.toString ++ " : " ++ (← semText b src f.type)))
  return (out, src)

private def emitGraph (b : Block) : CommandElabM Unit := do
  let ps ← paramsDecl b
  let mut ds := #[]
  for i in [:b.members.size] do
    let m := b.members[i]!
    let (arity, _) ← graphArity b i
    let mut cs := #[]
    for ci in [:m.ctors.size] do
      let c := m.ctors[ci]!
      let (fields, src) ← graphFields b c
      let (sem, _) ← ctorPair b src #[] #[] #[] i ci
      let idx ← graphIdx b src i c.result
      cs := cs.push ("  | " ++ c.name.toString ++ " " ++ join fields ++ " : " ++ withParams b (graphName m) (idx ++ #[sem]))
    let arity := if arity.isEmpty then "" else String.intercalate " → " arity.toList ++ " → "
    ds := ds.push ("inductive " ++ graphName m ++ " " ++ ps ++ " : " ++ arity ++ withParams b (semName m) (semIdxNames b i) ++ " → Type (" ++ b.level ++ "+1) where\n" ++ String.intercalate "\n" cs.toList)
  -- the block is induction-inductive whenever the written one was; keep the joint recursor
  emit ("set_option mumi.separate false in\nmutual\n" ++ String.intercalate "\n" ds.toList ++ "\nend")

private def emitPublic (b : Block) (order : Array (Sum Nat Nat)) : CommandElabM Unit := do
  let ps ← paramsDecl b
  for o in order do
    match o with
    | .inl i =>
      let m := b.members[i]!
      emit ("@[reducible] def " ++ m.name.toString ++ " " ++ ps ++ " " ++ (← pubArity b i) ++ " : Type (" ++ b.level ++ "+1) := Mumi.IR.Graph.Carrier " ++ withParams b (graphName m) (pubPairIdx b i (pubIdxNames b i)))
    | .inr j =>
      let d := b.decoders[j]!
      let idx ← d.idx.mapM fieldDecl
      let result := subst d.result #[(d.major, mkIdent `_ir_self)]
      emit ("@[reducible] def " ++ d.name.toString ++ " " ++ ps ++ " " ++ join idx ++ " (_ir_self : " ++ (← text d.majorType) ++ ") : " ++ (← text result) ++ " := _ir_self.1." ++ outField j)
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
      let fields ← c.fields.mapM fun f => fieldDecl { name := f.name, type := f.type }
      let result ← c.result.mapM text
      emit (attrs ++ "def " ++ m.name.toString ++ "." ++ c.name.toString ++ " " ++ ps ++ " " ++ join fields ++ " : " ++ typeAt b i result ++ " := ⟨_, " ++ app (graphName m ++ "." ++ c.name.toString) xs ++ "⟩")

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
private def motiveArgs (b : Block) := (Array.range b.members.size).map motive
private def minorArgs (b : Block) := (Array.range b.members.size).flatMap fun i => (Array.range b.members[i]!.ctors.size).map (minor b i)
private def motiveType (b : Block) (i : Nat) : CommandElabM String := do
  let arity ← pubArity b i
  let self := "(_ir_self : " ++ typeAt b i (pubIdxNames b i) ++ ")"
  return "∀ " ++ arity ++ " " ++ self ++ ", Sort _ir_elim"
private def motiveDecls (b : Block) : CommandElabM String := do
  return join (← (Array.range b.members.size).mapM fun i => do return "{" ++ motive i ++ " : " ++ (← motiveType b i) ++ "}")
private def ctorApp (b : Block) (i ci : Nat) (xs : Array String) :=
  withParams b (b.members[i]!.name.toString ++ "." ++ b.members[i]!.ctors[ci]!.name.toString) xs
private def fieldNames (c : Ctor) := c.fields.map (·.name.toString)
private def fieldsDecl (c : Ctor) : CommandElabM String := do
  return join (← c.fields.mapM fun f => fieldDecl { name := f.name, type := f.type })

/-- `motive_j idx (f dom)` for the recursive field `f`. -/
private def ihType (f : Field) (name : Option String := none) : CommandElabM String := do
  let some (j, args) := f.target | unreachable!
  let args ← args.mapM text
  forallS f.domain (app (name.getD (motive j)) (args ++ #[applyDomain f.name.toString f.domain]))

private def minorDecls (b : Block) (induction : Bool) : CommandElabM String := do
  let mut out := #[]
  for i in [:b.members.size] do
    for ci in [:b.members[i]!.ctors.size] do
      let c := b.members[i]!.ctors[ci]!
      let mut ihs := #[]
      if induction then
        for f in c.fields do
          if f.target.isSome then
            ihs := ihs.push (par (ihVar f.name ++ " : " ++ (← ihType f)))
      let result ← c.result.mapM text
      let concl := app (motive i) (result ++ #[ctorApp b i ci (fieldNames c)])
      let decls ← fieldsDecl c
      let ty := if c.fields.isEmpty then concl else "∀ " ++ decls ++ " " ++ join ihs ++ ", " ++ concl
      out := out.push (par (minor b i ci ++ " : " ++ ty))
  return join out

/-- The graph motive standing for the public `motive_i`. -/
private def graphMotive (b : Block) (i : Nat) : String :=
  let m := b.members[i]!
  let repack := m.indices.map fun x =>
    if x.member.isSome then "⟨" ++ semVar x.name ++ ", " ++ x.name.toString ++ "⟩" else x.name.toString
  untypedLambda (graphIdxNames b i ++ #["_ir_s", "_ir_g"]) (app (motive i) (repack ++ #["⟨_ir_s, _ir_g⟩"]))

/-- The graph minor premise standing for the public one: the split fields repacked. -/
private def graphMinor (b : Block) (i ci : Nat) (minorName : String) (ihs : Bool) : CommandElabM String := do
  let c := b.members[i]!.ctors[ci]!
  let mut binders := #[]
  let mut images := #[]
  let mut ihNames := #[]
  let mut src : Array Source := #[]
  for f in c.fields do
    if f.target.isSome then
      binders := binders.push (semVar f.name) |>.push f.name.toString
      let dom ← f.domain.mapM fun x => do return { x with type := ← semantic b src x.type }
      images := images.push (← lambda dom ("⟨" ++ applyDomain (semVar f.name) dom ++ ", " ++ applyDomain f.name.toString dom ++ "⟩"))
      ihNames := ihNames.push (ihVar f.name)
      src := src.push { name := f.name, sem := semVar f.name, graph := f.name.toString }
    else
      binders := binders.push f.name.toString
      images := images.push f.name.toString
  return untypedLambda (binders ++ ihNames) (app minorName (images ++ (if ihs then ihNames else #[])))

private def emitRec (b : Block) : CommandElabM Unit := do
  let ps ← paramsDecl b
  let common := ps ++ " " ++ (← motiveDecls b) ++ " " ++ (← minorDecls b true)
  let mut gargs := pArgs b
  for i in [:b.members.size] do gargs := gargs.push (graphMotive b i)
  for i in [:b.members.size] do
    for ci in [:b.members[i]!.ctors.size] do
      gargs := gargs.push (← graphMinor b i ci (minor b i ci) true)
  for i in [:b.members.size] do
    let m := b.members[i]!
    let idx := pubIdxNames b i
    let rest := m.name.toString ++ ".rec " ++ common ++ " " ++ (← pubArity b i (implicit := true)) ++ " (_ir_self : " ++ typeAt b i idx ++ ") : " ++ app (motive i) (idx ++ #["_ir_self"]) ++ " := " ++ app ("@" ++ graphName m ++ ".rec") (gargs ++ pubPairIdx b i idx ++ #["_ir_self.1", "_ir_self.2"])
    emitDef "@[elab_as_elim] " rest

private def emitEquations (b : Block) : CommandElabM Unit := do
  let ps ← paramsDecl b
  for j in [:b.decoders.size] do
    let d := b.decoders[j]!
    for ci in [:b.members[d.target]!.ctors.size] do
      let c := b.members[d.target]!.ctors[ci]!
      let result ← c.result.mapM text
      emit ("@[simp] theorem " ++ d.name.toString ++ "_" ++ c.name.toString ++ " " ++ ps ++ " " ++ (← fieldsDecl c) ++ " : " ++ withParams b d.name.toString (result ++ #[ctorApp b d.target ci (fieldNames c)]) ++ " = " ++ par (← text d.clauses[ci]!) ++ " := rfl")
  let common := ps ++ " " ++ (← motiveDecls b) ++ " " ++ (← minorDecls b true)
  let args := pArgs b ++ motiveArgs b ++ minorArgs b
  for i in [:b.members.size] do
    for ci in [:b.members[i]!.ctors.size] do
      let c := b.members[i]!.ctors[ci]!
      let mut ihs := #[]
      for f in c.fields do
        if let some (j, idx) := f.target then
          let idx ← idx.mapM text
          ihs := ihs.push (← lambda f.domain (app ("@" ++ b.members[j]!.name.toString ++ ".rec") (args ++ idx ++ #[applyDomain f.name.toString f.domain])))
      let result ← c.result.mapM text
      emit ("@[simp] theorem " ++ b.members[i]!.name.toString ++ ".rec_" ++ c.name.toString ++ " " ++ common ++ " " ++ (← fieldsDecl c) ++ " : " ++ app ("@" ++ b.members[i]!.name.toString ++ ".rec") (args ++ result ++ #[ctorApp b i ci (fieldNames c)]) ++ " = " ++ app (minor b i ci) (fieldNames c ++ ihs) ++ " := rfl")
  for i in [:b.members.size] do
    let m := b.members[i]!
    let idx := pubIdxNames b i
    emitDef "@[elab_as_elim] " (m.name.toString ++ ".recOn " ++ ps ++ " " ++ (← motiveDecls b) ++ " " ++ (← pubArity b i (implicit := true)) ++ " (_ir_self : " ++ typeAt b i idx ++ ") " ++ (← minorDecls b true) ++ " : " ++ app (motive i) (idx ++ #["_ir_self"]) ++ " := " ++ app ("@" ++ m.name.toString ++ ".rec") (args ++ idx ++ #["_ir_self"]))

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
        if f.target.any (·.1 == i) then
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
  let mut args := pArgs b
  for k in [:b.members.size] do
    args := args.push (if k == i then "motive" else
      untypedLambda ((Array.range (b.members[k]!.indices.size + 1)).map fun _ => "_") "PUnit")
  for k in [:b.members.size] do
    for ck in [:b.members[k]!.ctors.size] do
      let c := b.members[k]!.ctors[ck]!
      let recursive := c.fields.filter (·.target.isSome)
      if k == i then
        let own := recursive.filter (·.target.any (·.1 == i))
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
  for i in [:b.members.size] do
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
      emit ("@[simp] theorem " ++ m.name.toString ++ ".casesOn_" ++ c.name.toString ++ " " ++ ps ++ " " ++ mot ++ " " ++ join minors ++ " " ++ (← fieldsDecl c) ++ " : " ++ app ("@" ++ m.name.toString ++ ".casesOn") (pArgs b ++ #["motive"] ++ result ++ #[ctorApp b i ci (fieldNames c)] ++ minorNames) ++ " = " ++ app (minor b i ci) (fieldNames c) ++ " := rfl")

/-- Whether a block needs this path: some carrier is indexed. -/
def isIndexed (elems : Array Syntax) : CommandElabM Bool := do
  for e in elems do
    let d := e[1]
    if d.isOfKind ``Parser.Command.«inductive» then
      let (_, result) ← signature d[2]
      unless (unparen result).isOfKind ``Parser.Term.type do return true
  return false

def elaborate (elems : Array Syntax) : CommandElabM Unit := do
  if mumi.mahlo.get (← getOptions) then
    throwError "An indexed induction-recursion block is lowered one universe up only; \
      `set_option mumi.mahlo false`"
  let b ← readBlock elems
  let order ← declarationOrder b
  emit "universe _ir_elim"
  emitSemantics b order
  emitGraph b
  emitPublic b order
  emitRec b
  emitEquations b
  emitSolo b

end Mumi.IndRec.Family

namespace Mumi.IndRec
open Lean Elab Command

/-- The IR frontend: indexed blocks go one universe up through `Family`, the rest
through the original path. -/
def elaborateAny (elems : Array Syntax) : CommandElabM Unit := do
  if ← Family.isIndexed elems then Family.elaborate elems else elaborate elems

end Mumi.IndRec
