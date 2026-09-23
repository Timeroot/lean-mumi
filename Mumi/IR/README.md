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
| `mumi.mahlo true` | `U : Type u` | `IR.mahlo.{u}` | Stage-based induction; general constructor equations reduce, but some closed reductions get stuck |

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

-- Add `noncomputable` to this definition in lower mode.
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

Use `noncomputable def` for this in lower mode. The view equations are `rfl`,
and viewing a node does not recursively traverse its children. Nullary
upper-mode constructors additionally receive `@[match_pattern]`. There is no
general match elaborator override, automatic structural-recursion recognition
for the public carriers, `deriving`, public injectivity API, or `noConfusion`
wrapper yet; define recursive consumers using `.rec`.

## Supported input fragment

The prototype supports several carriers and several recursive functions per
carrier, including dependent outputs. A later decoder's result may refer to an
earlier decoder on the same argument. Constructor fields can use earlier
recursive arguments' decoded types, values, and numerical measures. Recursive
fields may be dependent functions with several arguments, and ordinary fields
may be proofs. Function-valued decoder results are supported as well.

Current restrictions are explicit:

- Carriers are unindexed, nonempty declarations in the same `Type u`. Their
  recursive occurrences are direct or functions returning a carrier. Nested
  occurrences, negative occurrences, and carriers in recursive argument domains
  are rejected. The generic backend supports fixed indices, but the frontend
  does not yet generate indexed blocks.
- Shared parameters must be typed, explicit, and repeated identically on all
  declarations. Use surrounding `universe` declarations. Section variables,
  implicit/default parameters, and per-declaration universe lists are not
  supported.
- Decoder headers have the form `def f (params) : U params → Result` or
  `def f (params) : (a : U params) → Result a`. Equations have exactly one flat
  constructor pattern with named variables, one equation per constructor.
  Recursive calls must explicitly name the decoder, repeat the shared parameters,
  and target an earlier recursive field (possibly applied to its arguments).
- Use simple declaration names inside a `namespace`. Attributes, modifiers,
  documentation comments inside the block, `deriving`, `where` declarations,
  and termination annotations are not yet supported.
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
before a later type error. Turn on `set_option trace.Mumi.ir true` to inspect
the generated commands. Large lower-mode blocks may need a higher
`maxRecDepth`; tests use 4000–6000.

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
its consistency. See the [backend discussion](../../IRResearch/General/README.md).
Adding blocks does not add axioms. Generated upper-mode definitions are
axiom-free; lower-mode definitions use only `IR.mahlo`. As usual, Lean's own
automatically generated constructor `injEq` lemmas can use `propext`.

## Tests

Run `lake test`, or `lake build Mumi MumiTests IRResearch.General.AxiomAudit`.
The `MumiTests/IR*.lean` suite covers both modes, polymorphic universes, two
carriers with six recursive outputs, dependent type/value outputs, numerical
branching, multi-argument recursive domains, proof fields, equation-variable
renaming, dependent elimination, views, tactics, compiled upper-mode execution,
module boundaries, rejection/rollback, and transitive axiom audits.

The historical `IRResearch.General.*` module paths remain compatibility imports
of the shared backend. The older example-specific `IRResearch` entry point is
not imported by `Mumi`.
