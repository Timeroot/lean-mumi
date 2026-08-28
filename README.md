# lean-mumi

**Mu**ltiple-**u**niverse **m**utual **i**nductives for Lean 4.

Lean requires every member of a `mutual` inductive block to land in the same
universe:

```lean
mutual
inductive A : Prop where
  | mk : B → A
inductive B : Type where
  | leaf : Nat → B
  | fromA : A → B
end
```

```
error: Invalid mutually inductive types: The resulting type of this declaration
  Type
differs from a preceding one
  Prop

Note: All inductive types declared in the same `mutual` block must belong to the same type universe
```

Import `Mumi` and that block compiles, with recursors that reduce in the kernel
and run in compiled code:

```lean
import Mumi

mutual
inductive A : Prop where
  | mk : B → A
inductive B : Type where
  | leaf : Nat → B
  | fromA : A → B
end

def bTag : B → Nat :=
  @B.mutualRec (fun _ => True) (fun _ => Nat) (fun _ _ => trivial) (fun n => n) (fun _ _ => 0)

example : bTag (B.leaf 7) = 7 := rfl   -- iota, in the kernel
#eval bTag (B.leaf 7)                  -- 7, in compiled code
```

No changes to Lean and no new syntax: you write `mutual` and it works.

The same restriction reaches *nested* inductives, because the kernel denests
them into a mutual block. Those are rescued too:

```lean
inductive T : Type where
  | mk1 : T
  | mkT : Nonempty T → T   -- without Mumi: "(kernel) mutually inductive types must live in the same universe"
```

## Installing

```toml
[[require]]
name = "lean-mumi"
git = "https://github.com/Timeroot/lean-mumi"
rev = "main"
```

Built against `leanprover/lean4:v4.33.1`.

## What you get

For a block with members `X₁ … Xₙ`:

* each member under its own name, with its own constructors;
* one recursor per member, `Xᵢ.mutualRec`, all sharing the telescope
  `{params} {motive₁ … motiveₙ} (case₁ … case_K) {idxs} (t : Xᵢ idxs) : motiveᵢ idxs t`;
* `Xᵢ.rec` as well, for the `Prop` members;
* a compiler implementation for each data member's recursor, so definitions
  built from `mutualRec` are computable rather than `noncomputable`.

Universes are derived per member. **Elimination is not.** A `Prop` member is
still small-eliminating unless it independently qualifies (subsingleton
elimination), exactly as it would be on its own. That boundary is what makes the
translation conservative: everything the block produces is definable in vanilla
Lean, just tediously.

A `Prop` member's recursor uses `Classical.choice` when any member of the block
has an infinitary field; a data member's recursor inherits that only if it has a
field of a `Prop` member's type. `#print axioms` will tell you which case you
are in.

## How it works

The block is lowered to declarations Lean's kernel already accepts:

1. an all-`Prop` **shadow** of the whole block, which is a legal homogeneous
   mutual inductive;
2. the **data members**, declared separately against that shadow, grouped into
   strongly connected components of the data-only dependency graph and emitted
   in topological order;
3. the **user-facing** names, constructors and recursors on top.

`Mumi/Lowering.lean` does that, and its module docstring carries the argument:
what each stage is for, why every SCC of data members is necessarily
homogeneous, why the derived recursors have exactly the elimination strength
they should, and why each iota rule holds — by proof irrelevance for the `Prop`
members, by delta plus native iota for the data ones.

Each data member's recursor gets a `Xᵢ.mutualRec.impl` — a `casesOn` recursion
put through Lean's own `Structural.structuralRecursion` — plus a kernel-checked
`Xᵢ.mutualRec.eq_impl : @Xᵢ.mutualRec = @Xᵢ.mutualRec.impl` registered with
`@[csimp]`. Nothing is `unsafe` and nothing is `implemented_by`: if the proof
cannot be produced you get an error at declaration time, never a miscompilation.

### Taking over `mutual`

`Lean.KeyedDeclsAttribute` *prepends*, so a `@[command_elab]` registered by an
imported library is tried before the builtin one, and `throwUnsupportedSyntax`
hands the block back to the builtin with any state the override touched rolled
back. `Mumi/Mutual.lean` is therefore a filter, not a replacement.

To decide, it elaborates the block's headers with the same-universe check
removed, then runs Lean's **own, unmodified** `checkHeaders` on the result and
takes over exactly when that throws. Any other outcome — a syntax error, a
`mutual def`, an unknown identifier, a genuine universe error inside one member
— answers "not ours", and Lean elaborates the block itself and reports it in its
own words. The probe's state is discarded either way.

`MumiTests/NonInterference.lean` pins this down: `mutual def`, `mutual theorem`,
`structure`, `deriving`, homogeneous inductive blocks, working nested inductives
and single inductives all still go through Lean, and error messages are
unchanged down to the byte.

Reaching Lean's `private` elaboration functions from downstream is done with
`import all Lean.Elab.MutualInductive`. Five of them sit on the path between
`mutual` and the kernel and two enforce the restriction being lifted, so those
five are reproduced in `Mumi/Elab.lean` with the check dropped; everything else
is called unmodified.

### Rescuing nested inductives

A *nested* inductive mentions itself under another type constructor. The kernel
handles these by specialising the nesting type to the block and checking the
enlarged block instead — so a nested inductive is really a mutual block in
disguise, and it inherits the same-universe restriction:

```lean
inductive T : Type where
  | mk1 : T
  | mkT : Nonempty T → T
```

```
error: (kernel) mutually inductive types must live in the same universe
```

`Nonempty T` is a `Prop` and `T` is a `Type`, so the block the kernel builds is
heterogeneous, and this is exactly the restriction being lifted. With `Mumi`
imported it goes through, and reads the way it was written:

```lean
#check @T.mkT   -- Nonempty T → T

example (h : Nonempty T) : T := T.mkT h
```

The rescued type is an ordinary inductive: it pattern-matches, it recurses
structurally, and it runs.

Underneath, the nesting becomes a *copy* of `Nonempty` specialised to `T`, an
auxiliary member of the block, and the constructor really takes that:

```lean
set_option mumi.pp.nested false in
#check @T.mkT   -- T.nested_Nonempty_1 → T
```

The copy cannot be avoided. A nested inductive whose denesting is
universe-heterogeneous is precisely the declaration the kernel refuses, so
`T.mkT : Nonempty T → T` can never be a kernel constructor here — the field's
type has to be something other than `Nonempty T`, or there is nothing to
declare. What *can* be arranged is that the copy's name is never needed, and
that is what the rest of this section is about.

When the copy is a `Prop` it is not merely isomorphic to the original but
*equal*, and saying so once is what makes it disappear:

```lean
set_option mumi.pp.nested false in
#check @T.nested_Nonempty_1.eq_orig  -- T.nested_Nonempty_1 = Nonempty T
```

Both directions are one recursor call per constructor, which works because
`A.cᵢ`'s fields are `I.cᵢ`'s with the nested occurrences rewritten — so when no
field mentions an auxiliary member, the two constructors take the same
arguments. That proviso rules out a wrapper that recurses through the nesting
and a nesting inside a nesting; those get no `eq_orig`, and are otherwise
unaffected.

From those two implications the block gets a coercion each way and, keyed off
the coercion, a delaborator. Together they mean the copy is neither written nor
read: the original can be handed to the constructor, a field bound by a pattern
match can be handed to anything that wants the original, and signatures, goals
and error messages all show the original.

```lean
def T.witnessed (_ : Nonempty T) : Prop := True

def T.probe : T → Prop
  | .mk1 => False
  | .mkT h => T.witnessed h   -- `h` is the copy; the coercion is inserted
```

`propext` is what makes the two *types* equal, and `eq_orig` needs it. Moving a
value between them does not: each coercion is one half of the `Iff` rather than
a `cast` along the equality, so a rescued value depends on no axioms and still
reduces.

```lean
def T.coerced : T := T.mkT (Nonempty.intro T.mk1)
#print axioms T.coerced   -- 'T.coerced' does not depend on any axioms
```

`⟨...⟩` gets its own treatment, because it reads the expected type rather than
being elaborated and then coerced; left alone it would reach past the copy into
the shadow block the lowering builds and ask for a `T._shadow`. Instead it is
elaborated at the original:

```lean
example : T := T.mkT ⟨T.mk1⟩
```

A coercion needs somewhere to go, so a consumer whose type argument is still
open does not get one — `Nonempty.elim h fun _ => trivial` needs the field
ascribed, as `Nonempty.elim (h : Nonempty T) fun _ => trivial`. The copy's name
is still not what gets written.

A member with no `eq_orig` keeps its own name in both respects. A data copy is
only isomorphic to what it copies, so displaying the original would be a lie,
and `N.nested_List_2` stays `N.nested_List_2`.

`set_option mumi.pp.nested false` turns the display off, which is what to reach
for when a mismatch between a copy and its original has to be seen. It is off
automatically under `pp.explicit`, so a type error whose two sides would
otherwise both print as `Nonempty T` exposes the copy by itself.

**Nested inductives that already work are not touched.** Denesting is the
kernel's own feature and there is no reason to reimplement it, so
`Mumi/Declaration.lean` is a *catch-and-retry*: Lean elaborates the declaration
first, and only if that fails do we denest it ourselves — and then only if
denesting is what made the block heterogeneous. Anything else is rolled back and
Lean's error is rethrown verbatim. So the second elaboration only ever happens to
a declaration that was going to be an error anyway, and a working nested
inductive still gets the kernel's `T.rec_1` and no `mutualRec`.

Denesting at the elaborator instead of the kernel also lifts a second
restriction. The kernel requires a nested application's parameters to be closed:

```lean
inductive Ix : Nat → Type where
  | base : Ix 0
  | step : (n : Nat) → Nonempty (Ix n) → Ix (n + 1)
```

```
error: (kernel) nested inductive datatypes parameters cannot contain local variables
```

Here `Ix n` mentions a constructor field, so there is no single member it could
become. We abstract the field and make it an *index* of the auxiliary member —
`Ix.nested_Nonempty_1 : Nat → Prop` — which works whether or not the universes
line up. Occurrences that differ only in which local they mention share one
member.

`MumiTests/Nested.lean` covers the classic case, the bridges, the coercions and
the display, structural recursion and `#eval` on a rescued type, other `Prop`
wrappers, parameters, indices, nesting inside a hand-written heterogeneous
block, and nesting inside nesting.

### Turning it off

```lean
set_option mumi.enabled false
```

Stock behaviour returns immediately, including the stock error message.

## Limitations

* A member's universe must be decidably `Prop`-or-not, so `inductive X : Sort u`
  and `inductive X : Sort (imax u v)` are rejected — as they are by Lean itself.
  `imax` inside a *field* is fine; it is only the member's own resulting universe
  that has to be classifiable.
* Two data members that hold each other are in one component and must share a
  universe. Universes may differ only across components.
* Universe parameters have to be declared with `universe` up front. With
  auto-bound implicits each member gets its own parameter list, and `mutual`
  rejects the block before we see it.
* Structures, classes and coinductive members are not lowered; a `mutual` block
  containing one is left to Lean.
* A rescued nested inductive's constructor really takes a copy of the nested
  type, and only a copy that is a `Prop` gets the equality, the coercions and
  the display that hide it. A *data* copy — `N.nested_List_2` for
  `Nonempty (List N)`, or a `List` nested inside a hand-written heterogeneous
  block — is merely isomorphic to what it copies, and you are on your own.
* A coercion is inserted only where the type it has to reach is known, so a
  consumer whose own type argument is still a metavariable does not get one:
  `Nonempty.elim h fun _ => …` on a field bound by a pattern match needs `h`
  ascribed, or the argument given as `Nonempty.elim (α := T)`. The ascription
  names the original, not the copy.
* Importing this library changes the formatting of a few kernel error messages
  (some gain a `(kernel)` prefix). This predates the nested support and affects
  declarations the library never touches; `set_option mumi.enabled false` does
  not suppress it.

## Status

This started as an in-tree Lean elaborator under a separate
`mutual_multiuniverse` command, and there is an open draft PR to put similar
functionality into core Lean:
[leanprover/lean4#14945](https://github.com/leanprover/lean4/pull/14945). This
library is the downstream version of it, and needs no patched toolchain. If you
want this in Lean proper, saying so upstream is the thing that would help.

## License

Apache 2.0, matching Lean. `Mumi/Elab.lean` contains code adapted from
leanprover/lean4; see the header there.
