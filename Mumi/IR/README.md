# Experimental induction–recursion frontend

On the `mahlo-ir` branch, `import Mumi` also enables a syntax-directed IR
prototype. It shares Mumi's existing `mutual` interceptor. Stock Lean is tried
first; only the rejection of a block mixing `inductive` and `def` triggers IR
translation. Ordinary mutual definitions and inductives keep their existing
elaboration. `set_option mumi.enabled false` disables all Mumi interception.

## Two representations

For a carrier written `inductive U : Type u`:

| Option | Generated carrier | Additional axiom used | Computation |
| --- | --- | --- | --- |
| `mumi.mahlo false` (default) | `U : Type (u+1)` | None | Ordinary graph induction; kernel reduction and compiled execution |
| `mumi.mahlo true` | `U : Type u` | `IR.mahlo.{u}` | Stage-based induction; general constructor equations reduce, but some closed reductions get stuck; compiled execution |

Upper mode deliberately changes the declared carrier universe. Decoder result
types are not shifted. Both modes use the same source syntax and public API.
Importing `Mumi` declares the reflection axiom in the environment even in upper
mode, but upper-mode definitions do not depend on it.

```lean
import Mumi

set_option mumi.mahlo false -- change to true for the small carrier
universe u
namespace MyTypes

mutual
  inductive U (A : Type u) : Type u where
    | base : U A
    | pi (a : U A) (b : El A a → U A) : U A
  def El (A : Type u) : U A → Type u
    | .base => A
    | .pi a b => (x : El A a) → El A (b x)
end

example (A : Type u) (a : U A) (b : El A a → U A) :
    El A (U.pi A a b) = ((x : El A a) → El A (b x)) := rfl

def inhabit (A : Type u) (a₀ : A) (a : U A) : El A a :=
  U.rec A a₀ (fun _ _ _ ih => fun x => ih x) a

example : inhabit Nat 7 (U.pi Nat (U.base Nat) (fun _ => U.base Nat)) 42 = 7 := rfl
#eval inhabit Nat 7 (U.pi Nat (U.base Nat) (fun _ => U.base Nat)) 42 -- 7

end MyTypes
```

The last closed example and `#eval` demonstrate upper mode, not a promise of
closed normalization or executable constructors in lower mode. In lower mode,
for example, the closed equality
`El Nat (U.pi Nat (U.base Nat) (fun _ => U.base Nat)) = (Nat → Nat)`
needs `by rw [El_pi, El_base]` instead of `rfl`. The variable-general `El_pi`
and dependent recursor equations themselves are generated with literal `rfl`
proofs. This distinction is tested, not hidden behind simplification.

## Generated API

Each member gets its named constructors and:

- `U.rec`: dependent mutual elimination into any `Sort`, with recursive
  hypotheses for every direct or function-valued recursive field;
- `U.recOn`: the major premise precedes the constructor cases;
- `U.cases` and `U.casesOn`: nonrecursive, dependent case analysis;
- `@[simp]` decoder equations such as `El_pi`, recursor equations such as
  `U.rec_pi`, and case equations such as `U.casesOn_pi`.

Shared explicit parameters remain explicit. All recursor motives share one
elimination universe. For mutual blocks the motives are named `motive`,
`motive_2`, etc., in carrier declaration order. Cases follow carrier order and
then constructor order; recursive hypotheses follow the constructor's ordinary
arguments. Repeated constructor names are disambiguated in the case binders.

The recursors are registered with `induction_eliminator`; case analysis uses
`cases_eliminator`. Thus ordinary `induction a` works for a single carrier, and
`cases a` works for single and mutual carriers. For mutual induction, specify
the other motives when Lean cannot infer them, for example:

```lean
-- For the two-carrier example in MumiTests/IRMutual.lean:
example (a : IRMutualLower.Ty) : True := by
  induction a using IRMutualLower.Ty.rec (motive_2 := fun _ => True) <;> trivial
```

The public carriers are definitions, not new kernel inductive declarations.
General constructor aliases cannot reliably serve as ordinary match patterns.
Every carrier therefore also gets a dependent one-step view:

```lean
-- In the MyTypes namespace from above:
def top (A : Type u) (a : U A) : Bool :=
  match U._ir_view A a with
  | .base => true
  | .pi _ _ => false
```

This compiles and runs in both modes. The view equations are `rfl`,
and viewing a node does not recursively traverse its children. Nullary
upper-mode constructors additionally receive `@[match_pattern]`. There is no
general match elaborator override, automatic structural-recursion recognition
for the public carriers, `deriving`, public injectivity API, or `noConfusion`
wrapper yet; define recursive consumers using `.rec`.

## Indexed carriers, and induction-induction in the same block

A carrier may be *indexed*, and an index domain may be another carrier of
the block or a type a decoder computes.  A decoder may then recurse
over an indexed carrier, and its result may read the decoders of the indices.
So one `mutual` may hold induction-induction and induction-recursion at once:

```lean
mutual
inductive Ctx : Type where
  | nil : Ctx
  | ext (Γ : Ctx) (A : Ty Γ) : Ctx
inductive Ty : (Γ : Ctx) → Type where
  | U (Γ : Ctx) : Ty Γ
  | Pi (Γ : Ctx) (A : Ty Γ) (B : Ty (Ctx.ext Γ A)) : Ty Γ
def Env : Ctx → Type
  | .nil => PUnit
  | .ext Γ A => (ρ : Env Γ) × El Γ A ρ
def El : (Γ : Ctx) → Ty Γ → Env Γ → Type
  | _, .U Γ => fun _ => Nat
  | _, .Pi Γ A B => fun ρ => (a : El Γ A ρ) → El (Ctx.ext Γ A) B ⟨ρ, a⟩
end

example (Γ : Ctx) (A : Ty Γ) (B : Ty (Ctx.ext Γ A)) :
    El Γ (Ty.Pi Γ A B) = fun ρ => (a : El Γ A ρ) → El (Ctx.ext Γ A) B ⟨ρ, a⟩ := rfl
```

`MumiTests/IRTangle.lean` is the stress case: a carrier `A` holding a `B` and a
`D`, `F : A → Type` reading `D` at the `B` inside, `B` indexed by an `A` and by
`F` of it, `D` a type computed from a `B`, and `E` indexed by all three, in one
strongly connected block.

One universe up, [Family.lean](Family.lean) does this by the same graph
encoding as above.  A carrier `X` with decoders `f₁ … fₖ` becomes a record
`_ir_X_Sem` of the decoders' values and a graph `_ir_X` indexed by it; an index
of carrier type is split into its semantic half and its graph half, and a
decoder applied to it reads the semantic half.  What is left is a `mutual` of
indexed graph families that is still induction-inductive wherever the written
block was, and it goes through the ordinary `mutual` command -- to Lean when
its arities are plain, to `Mumi.IndInd` when they name each other, with
`mumi.separate false` so the joint recursor is kept.  The public carrier is
`(s : _ir_X_Sem …) × _ir_X … s`, a decoder is a projection, a constructor packs
the decoders' clauses with the graph constructor, and `X.rec` is the graph's
recursor with its motives and minor premises repacked.  Every decoder equation
and iota rule is `rfl`, and no axiom is added.

At the universe the block is written at, `set_option mumi.mahlo true`, the
same block goes through the stage engine.  The raw carriers are not indexed:
one signature holds every carrier, its descriptions read the indices'
semantics off the decoded fields, and a constructor's coherence -- that the
index recorded in its decode is the one written -- is a proof field after its
recursive fields.  On top of the raw carriers sits `_ir_X_Good`, a mutual
`Prop` family over raw values and their coherences, and the public `X i₁ … iₙ`
is the subtype of raw values it certifies; a decoder is the recorded semantics
transported along the certificate's coherence, and `X.rec` is the stage
engine's induction with the packed index and certificate as its motive's
arguments, cast back to the written index by the equations the certificate
yields.  The decoder equations and iota rules are still definitional, and are
stated as `@[simp]` theorems proved by `Eq.refl` -- checked by the kernel
directly, with only the statement elaborated: the two sides are small as
shared graphs but astronomically large as trees, which the elaborator's
unifier walks without sharing and the kernel does not.  One the kernel rejects
is skipped and reported under `trace.Mumi.ir` rather than failing the block;
`set_option mumi.ir.equations false` states none of them.  As everywhere in
lower mode, a closed term does not normalise, so numerals a decoder computes
want an ascription, `(0 : Nat)`.  What is defined through the recursors
compiles and runs: at run time a value is its constructor arguments together
with its outputs, computed once when it is built (`IR.Stage.Runtime`), a
node's field is the same object, and the reflection axiom is never executed.

The generated API is as above -- `X.rec` over every motive in the block,
`X.recOn`, `X.casesOn`, `X.cases`, `@[simp]` decoder, recursor and case
equations -- plus `X.recD`, the one-motive recursor with the other carriers'
motives discharged at `PUnit`, which is what `induction x` uses (`X.rec` asks for
every motive, so it is for `induction … using` and term mode).  Motives are
`motive`, `motive_2`, … in carrier order.

Its restrictions, beyond the general ones below:

- A decoder is `def f (params) : (i₁ : I₁) → … → (iₙ : Iₙ) → X params i₁ … iₙ → R`:
  the carrier's indices bound in order just before it, at exactly those names.
  Its equations take one pattern per index (`_` or a name) and one flat
  constructor pattern.
- An index domain that mentions a carrier is that carrier applied outright to
  its indices; `List Ctx` is not one.  Anything else about a value of carrier
  type -- an index, a field, the value a decoder is about -- is read only
  through decoders, so `(h : x = y)` for fields `x y : A` is rejected.
- An index argument of carrier type is a field, a field applied to its own
  binders, or a constructor application (written `Ctx.ext Γ A` or `.ext Γ A`).
  One universe up, a constructor application whose argument is a function
  field applied to a binder, `Ty (.ext Γ (f n))`, is not deleted by the
  erasure underneath and is rejected by it; at the written universe nothing is
  erased and it goes through.  A constructor nested inside another in an
  index term, `E (A.cons (A.cons …) …) …`, goes through at the written
  universe as well, although the decode of a nested node does not reduce
  there: the lower view names each nested application by a hidden raw field
  the public constructor supplies -- one that is an argument of another
  application is substituted for in the certificate, one that is a conclusion
  index is bound and pinned by an equation -- and the recursors, `casesOn` and
  iota rules are definitional as before.  What is given up is a decoder
  equation whose right-hand side reads a decoder at such a nested index, as
  `El Γ (Ty.deep Γ A B C) = El (.ext (.ext Γ A) B) C` does: it transports
  along the decode of that index, so the kernel does not accept it as
  definitional and it is skipped; at an index one constructor deep, `E (A.cons
  x c b d) …`, every equation is kept.
- When Lean declares the graph block -- no carrier in any arity -- `X.rec` is
  a kernel recursor application, which the code generator compiles for a single
  carrier and not for a mutual family; it is then `noncomputable`, and so is
  what is defined through it.  When `Mumi.IndInd` declares the block, it
  compiles.
- An indexed carrier gets no view, no `match` on its constructors, and no
  `deriving` yet; recursive consumers go through `X.rec` and `X.recD`.

## Components, and members in different universes

A block is split only where it has to be.  Its strongly connected components,
dependencies first, are regrouped as far as a group can be one block --
carriers in one universe with their decoders -- so that a block in one
universe stays one block with one joint recursion, as a `mutual` has.  A group
of carriers and decoders is an induction-recursion of its own; one of
definitions alone, or of `Prop` inductives, is Lean's.  So the members may sit
in different universes as long as no component mixes them -- and without a
`Prop` to run a dependency through, none can, since a `Type 1` carrier cannot
take a `Type 3` field: in `MumiTests/IRUniverses.lean` `A : Type 1` and `F`
are one group, `B : Type 3` and `G`, which read them, another, and each lands
where it was written (one universe up, one above).  With a `Prop` to run the
dependency through, one component does span universes: `A : Type 1` takes a
proof of `P x`, `P`'s constructor takes a `B : Type 3`, and `B` takes an `A`.
One universe up that is taken, as the next section says;
`MumiTests/IRUniversesProp.lean` is it, in both modes: at the written
universe each carrier stays where it was written, on one stage engine per
universe, `A`'s first, `B`'s reading `A`'s raw terms and decoder as values of
a type already there -- a plain field, with its certificate demanded by `B`'s
-- and the certificates of all of them in one `mutual` after every engine.
`B.rec` is then the recursion of `B`'s engine, with no hypothesis at its
`A`, as one universe up.

## A `Prop` in the block

A decoder may land in `Prop`, and a constructor may take a proof of it as a
field: `Inh : U → Prop` below is recursive with `U` and `El`, and `U.pi`
asks for `Inh a`.  A `Prop` inductive may sit in the same `mutual` too, indexed
by the carriers and reading the decoders -- `Good` here, with `Fine` mutual
with it.  Such a member is no part of the induction-recursion, since nothing
is defined by recursion on a proof, so when nothing else in the block mentions
it, it is a component of its own, declared right after what it refers to, in
both modes, with Lean's own recursors.

When a carrier does mention it -- `U.pi (a : U) (b : El a → U) (h : Good a)`,
with `Good : U → Prop` in the block -- the `Prop` member is in the component
and goes through the encoding with it, one universe up, as the data's
well-formedness: the graph constructors take no proof fields, and after the
graph block a `mutual` of Lean's own declares, in `Prop`, a predicate over
every carrier's graph -- a node is well formed when its fields are and the
proofs the constructor was written with are at hand -- and the `Prop` member
itself, over the graphs, its fields of carrier type each followed by their
well-formedness.  The public carrier is the subtype of its graph by the
predicate.  So `U.rec` is over the data with the proof as a field and no
hypothesis of its own, and `Good.rec` and `Good.casesOn` are the predicate's
own, into `Prop`, with hypotheses at its proofs of `Prop` members; `induction`
and `cases` drive them, and iota is still `rfl`.  A `Prop` constructor may
take a field of carrier type its conclusion does not mention -- the proof
carries its well-formedness -- which is what lets a `Prop` tie carriers in
different universes together (`MumiTests/IRUniversesProp.lean`).  One thing
changes for the writer: a proof a constructor was built with is no field of
the data, so `Good.pi _ _ h …` has to name `h` where `Good.pi _ _ _ …` used to
infer it.  A decoder may not recurse over a `Prop` member, and a `Prop` member
cannot be an index domain.

At the written universe the same idea lands on what is already there: the
raw terms carry no proofs, the certificates `_ir_X_Good` do -- a data member's
constructor takes each proof where it was written, as a proof of the `Prop`
member's certificate -- and the `Prop` member is a certificate `_ir_P_Good`
over the raw halves of its indices, in the one `mutual` with the others.  The
recursion reads the proofs off the certificate's shape like the fields'
certificates, `P.rec` and `P.casesOn` come from the certificates' joint
recursor, and every equation is `rfl` as before.
`MumiTests/IRPropSCC.lean` is this block, and an indexed one with a `Prop`
its carriers need, in both modes.

```lean
mutual
inductive U : Type where
  | base : U
  | pi (a : U) (b : El a → U) (h : Inh a) : U
inductive Good : U → Prop where
  | base : Good .base
  | pi (a : U) (b : El a → U) (h : Inh a) (ha : Good a) (hb : ∀ x, Good (b x)) : Good (.pi a b h)
inductive Fine : U → Prop where
  | base : Fine .base
  | pi (a : U) (b : El a → U) (h : Inh a) (ha : Good a) (hb : ∀ x, Fine (b x)) : Fine (.pi a b h)
def El : U → Type
  | .base => Nat
  | .pi a b h => (x : El a) → El (b x)
def Inh : U → Prop
  | .base => True
  | .pi a b h => ∀ x : El a, Inh (b x)
end
```

`MumiTests/IRProp.lean` is this block in both modes, and
`MumiTests/IRUniverses.lean` has carriers in `Type 1` and `Type 3`, one
component each, in both modes.

## Supported input fragment

The prototype supports several carriers and several recursive functions per
carrier, including dependent outputs. A later decoder's result may refer to an
earlier decoder on the same argument. Constructor fields can use earlier
recursive arguments' decoded types, values, and numerical measures. Recursive
fields may be dependent functions with several arguments, and ordinary fields
may be proofs. Function-valued decoder results are supported as well.

Current restrictions are explicit:

- Carriers are nonempty declarations in the same `Type u`, unindexed except in
  upper mode (see the section above). Their recursive occurrences are direct or
  functions returning a carrier. Nested occurrences, negative occurrences, and
  carriers in recursive argument domains are rejected.
- Shared parameters must be typed, explicit, and repeated identically on all
  declarations. Use surrounding `universe` declarations; members may sit at
  different levels of them, `Type u` beside `Type (u+1)`. Section variables,
  implicit/default parameters, and per-declaration universe lists are not
  supported.
- Decoder headers have the form `def f (params) : U params → Result` or
  `def f (params) : (a : U params) → Result a`. Equations have exactly one flat
  constructor pattern with named variables, one equation per constructor.
  Recursive calls must explicitly name the decoder, repeat the shared parameters,
  and target an earlier recursive field (possibly applied to its arguments).
- Use simple declaration names inside a `namespace`. A documentation comment
  on a member, a constructor or a decoder goes onto the public declaration;
  attributes, other modifiers, `deriving`, `where` declarations, and
  termination annotations are not yet supported.
- This is syntax-directed translation, not arbitrary Lean term elaboration:
  opaque binding macros and hidden/aliased recursive occurrences are outside
  its contract. Ordinary lambdas, dependent function types, lets, and matches
  are supported with fresh local names. Shadowing block/parameter/field/equation
  names is rejected, as are ambiguous equation-variable renamings. Move tactic
  proofs, `do` notation, and local recursive definitions into external helpers.
  `_ir_...` names are reserved, as are recursor binder names `motive...`.
- Lower-mode ordinary argument types and recursive index domains must fit in
  `Type u` (proof arguments are boxed automatically). Both modes' bundled
  decoder outputs must fit in `Type (u+1)`.

Rejected generation is rolled back, including declarations already emitted
before a later type error; `set_option mumi.ir.debug true` keeps what was
emitted instead, so that it can be inspected. Turn on
`set_option trace.Mumi.ir true` to inspect the generated commands. Large
lower-mode blocks may need a higher `maxRecDepth`; tests use 4000–6000.

## Implementation and trust boundary

[Frontend.lean](Frontend.lean) generates ordinary Lean declarations and has them
elaborated and kernel checked. It does not introduce placeholder axioms, skip
kernel checking, or use `sorry` or `implemented_by`. Public computational
definitions are exposed across modern Lean `module` boundaries; the tests
include a separate importing module.

Upper mode generates semantic records and a mutually inductive graph of their
interpretations. The public carrier pairs an interpretation with its graph
derivation. Lower mode generates positive descriptions, uses the shared
accessibility/stage engine, and restricts raw codes by mutually inductive `Prop`
certificates. The certificates recover canonical children for the stage-free
public eliminators. Proof irrelevance is essential to their conversion behavior.

[Basic.lean](Basic.lean) provides the shared `Mumi.IR` vocabulary; the stage
engine is not regenerated per block. For `MyTypes.Biggie`, block-specific names
look like `MyTypes._ir_Biggie`, `MyTypes._ir_Biggie_Sem`,
`MyTypes._ir_Biggie_Good`, and `MyTypes.Biggie._ir_view`. These are deliberately
underscored, not opaque or inaccessible private declarations.

The underlying backend retains its `IR` namespace for compatibility, including
the exact sole additional axiom in [Mahlo.lean](Mahlo.lean):

```lean
axiom IR.mahlo.{u} : IR.Reflection.{u,u+1}
```

This is an operational Mahlo-style reflection assumption. Its proposed
set-theoretic justification is not formalized, and kernel checks do not prove
its consistency. Adding blocks does not add axioms. Generated upper-mode definitions are
axiom-free; lower-mode definitions use only `IR.mahlo`. As usual, Lean's own
automatically generated constructor `injEq` lemmas can use `propext`.

## Tests

Run `lake test`, or `lake build Mumi MumiTests`.
`MumiTests/IRFamily.lean` and `MumiTests/IRTangle.lean` cover the indexed and
induction-inductive blocks of the section above one universe up, what they
reject included; `MumiTests/IRFamilyLower.lean` and
`MumiTests/IRTangleLower.lean` cover the same blocks at the written universe.
`MumiTests/IRTangle2.lean` and `MumiTests/IRTangle2Lower.lean` add a data
decoder the rest of the block reads: as a field's type, as the index a
constructor sits at, and as what two type-valued decoders compute with.
The rest of the `MumiTests/IR*.lean` suite covers both modes, polymorphic universes, two
carriers with six recursive outputs, dependent type/value outputs, numerical
branching, multi-argument recursive domains, proof fields, equation-variable
renaming, dependent elimination, views, tactics, compiled upper-mode execution,
module boundaries, rejection/rollback, and transitive axiom audits.
