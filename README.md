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

`Mumi/Lowering.lean` does that. The derivation, with worked examples and the
argument that the result is conservative, is written up separately in
`docs/heterogeneous-mutual-lowering.md`.

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
`structure`, `deriving`, homogeneous inductive blocks, nested inductives and
single inductives all still go through Lean, and error messages are unchanged
down to the byte.

Reaching Lean's `private` elaboration functions from downstream is done with
`import all Lean.Elab.MutualInductive`. Five of them sit on the path between
`mutual` and the kernel and two enforce the restriction being lifted, so those
five are reproduced in `Mumi/Elab.lean` with the check dropped; everything else
is called unmodified.

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
