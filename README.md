# lean-mumi

**Mu**ltiple-**u**niverse **m**utual **i**nductives for Lean 4.

Lean puts two restrictions on `mutual` inductive blocks that the type theory
does not force: every member must land in the same universe, and no member's
*arity* may mention a sibling. Import `Mumi` and both are lifted. There is no
new syntax and no patched toolchain — you write `mutual`, and the recursors you
get reduce in the kernel and run in compiled code.

```toml
[[require]]
name = "lean-mumi"
git = "https://github.com/Timeroot/lean-mumi"
rev = "main"
```

Built against `leanprover/lean4:v4.33.1`.

## Members in different universes

Stock Lean:

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

With `import Mumi` the same block compiles, and every member gets a recursor
over the whole family:

```lean
def bTag : B → Nat :=
  @B.mutualRec (fun _ => True) (fun _ => Nat) (fun _ _ => trivial) (fun n => n) (fun _ _ => 0)

example : bTag (B.leaf 7) = 7 := rfl   -- iota, in the kernel
#eval bTag (B.leaf 7)                  -- 7, in compiled code
```

`Xᵢ.mutualRec` shares one telescope across the block —
`{params} {motive₁ … motiveₙ} (case₁ … case_K) {idxs} (t : Xᵢ idxs) : motiveᵢ idxs t`
— and the `Prop` members get `Xᵢ.rec` as well.

### Indices, parameters and several universes

Nothing above is special to two members or to `Prop`-and-`Type`. Universes are
derived per member, so each one sits exactly where it would if you had declared
it alone:

```lean
universe u v w

mutual
inductive Wf (α : Type u) (β : Type v) : Nat → Prop where
  | zero : Wf α β 0
  | succ (n : Nat) : Layer α β n → Wf α β (n + 1)
inductive Layer (α : Type u) (β : Type v) : Nat → Type (max u v) where
  | base : α → β → Layer α β 0
  | more (n : Nat) (h : Wf α β n) : Layer α β n → Layer α β (n + 1)
inductive Tagged (α : Type u) (β : Type v) : Type (max u v (w + 1)) where
  | mk : Type w → Layer α β 1 → Tagged α β
end

#check Layer   -- Layer.{u, v, w} (α : Type u) (β : Type v) : Nat → Type (max u v)
#check Tagged  -- Tagged.{u, v, w} (α : Type u) (β : Type v) : Type (max u v (w + 1))
```

and it still computes:

```lean
def depth {α : Type u} {β : Type v} : (n : Nat) → Layer α β n → Nat :=
  fun n t => @Layer.mutualRec α β (fun _ _ => True) (fun _ _ => Nat) (fun _ => Nat)
    trivial (fun _ _ _ => trivial)
    (fun _ _ => 0) (fun _ _ _ _ ih => ih + 1)
    (fun _ _ ih => ih) n t

example : depth 1 (Layer.more 0 .zero (.base 1 "x")) = 1 := rfl
#eval depth.{0, 0, 0} 1 (Layer.more 0 .zero (.base 1 "x"))   -- 1
```

**Elimination is not derived per member.** A `Prop` member is still
small-eliminating unless it independently qualifies for subsingleton
elimination, exactly as it would be on its own. That boundary is what makes the
translation conservative: everything the block produces is definable in vanilla
Lean, just tediously. One axiom does show up — a `Prop` member's recursor uses
`Classical.choice` when any member of the block has an infinitary field, and a
data member's recursor inherits that only if it has a field of a `Prop` member's
type. `#print axioms` will say which case you are in.

### Nested inductives

A nested inductive mentions itself under another type constructor. The kernel
handles one by specialising the nesting type to the block and checking the
enlarged block instead — so a nested inductive is a mutual block in disguise,
and it inherits the same restriction:

```lean
inductive T : Type where
  | mk1 : T
  | mkT : Nonempty T → T   -- (kernel) mutually inductive types must live in the same universe
```

`Nonempty T` is a `Prop` and `T` is a `Type`. With `Mumi` imported the
declaration goes through, and reads the way it was written:

```lean
#check @T.mkT          -- Nonempty T → T

def T.two : T := T.mkT ⟨T.mk1⟩
#print axioms T.two    -- 'T.two' does not depend on any axioms
```

Underneath, the field really has the type of an auxiliary *copy* of `Nonempty`
specialised to `T`, and the copy cannot be avoided: `T.mkT : Nonempty T → T` is
precisely the constructor the kernel refuses. What can be arranged is that its
name is never needed. A `Prop` copy is not merely isomorphic to the original but
*equal*, by `propext`, and from the two halves of that `Iff` come a coercion each
way plus a delaborator keyed off it — so the original goes in, comes out, and is
what every signature, goal and error message shows. Crossing between them uses
the coercions rather than a `cast` along the equality, which is why a rescued
value depends on no axioms and still reduces. `set_option mumi.pp.nested false`
turns the display off, and it is off under `pp.explicit` anyway, so a mismatch
between a copy and its original cannot hide behind it.

**Nested inductives that already work are untouched.** Denesting is the kernel's
own feature, so `Mumi/Declaration.lean` is a *catch-and-retry*: Lean elaborates
the declaration first, and only if that fails — and only if denesting is what
made the block heterogeneous — do we denest it ourselves. Anything else is
rolled back and Lean's error rethrown verbatim.

Doing it in the elaborator lifts a second kernel restriction along the way, that
a nested application's parameters be closed:

```lean
inductive Ix : Nat → Type where
  | base : Ix 0
  | step : (n : Nat) → Nonempty (Ix n) → Ix (n + 1)
  -- (kernel) invalid nested inductive datatype 'Nonempty', nested inductive
  -- datatypes parameters cannot contain local variables.
```

`Ix n` mentions a constructor field, so there is no single member it could
become; we abstract the field and make it an *index* of the auxiliary member.
`MumiTests/Nested.lean` covers all of this.

### How it works

The block is lowered to declarations the kernel already accepts: an all-`Prop`
**shadow** of the whole block, which is a legal homogeneous mutual inductive;
then the **data members**, declared separately against that shadow, grouped into
strongly connected components of the data-only dependency graph and emitted in
topological order; then the user-facing names, constructors and recursors on
top. `Mumi/Lowering.lean`'s module docstring carries the argument — why every
data SCC is necessarily homogeneous, why the derived recursors have exactly the
elimination strength they should, and why each iota rule holds.

Each data recursor also gets a `Xᵢ.mutualRec.impl` — a `casesOn` recursion put
through Lean's own `Structural.structuralRecursion` — plus a kernel-checked
`Xᵢ.mutualRec.eq_impl` registered with `@[csimp]`. Nothing is `unsafe` and
nothing is `implemented_by`: an unprovable equation is an error at declaration
time, never a miscompilation.

`Mumi` is a filter on `mutual`, not a replacement. `Lean.KeyedDeclsAttribute`
prepends, so an imported `@[command_elab]` is tried before the builtin, and
`throwUnsupportedSyntax` hands the block back with any state the override
touched rolled back. To decide, it elaborates the headers with the same-universe
check removed and runs Lean's **own, unmodified** `checkHeaders` on the result,
taking over exactly when that throws. A syntax error, a `mutual def`, an unknown
identifier, a genuine universe error inside one member — all answer "not ours",
and Lean elaborates the block and reports it in its own words;
`MumiTests/NonInterference.lean` pins that down to the byte. Reaching Lean's
`private` elaboration functions from downstream is done with
`import all Lean.Elab.MutualInductive`: five sit on the path from `mutual` to
the kernel and two of them enforce the restriction being lifted, so those five
are reproduced in `Mumi/Elab.lean` with the check dropped.

## Induction-induction through `Prop`

A block is *induction-inductive* when one member's arity mentions another. This
is a different obstruction: the block does not elaborate at all, because Lean
elaborates every arity before any member is in scope. Collapsing the block to
one universe would not help.

```lean
mutual
inductive Ctx : Type where
  | nil : Ctx
  | snoc : (Γ : Ctx) → (x : String) → Fresh x Γ → Ctx   -- unknown identifier 'Fresh'
inductive Fresh : String → Ctx → Prop where             -- unknown identifier 'Ctx'
  | nil : (x : String) → Fresh x .nil
  | snoc : (x y : String) → (Γ : Ctx) → (h : Fresh y Γ) → x ≠ y → Fresh x Γ →
    Fresh x (.snoc Γ y h)
end
```

`Mumi` takes such a block when the dependency runs **only through proofs** —
every field of a data constructor whose type mentions a `Prop` member is itself
a proof. Both kinds of member then get a recursor stated over the block as
written:

```lean
def Ctx.length (Γ : Ctx) : Nat :=
  Ctx.rec (C := fun _ => Nat) 0 (fun _ _ _ ih => ih + 1) Γ

example (x : String) (Γ : Ctx) (h : Fresh x Γ) : 0 ≤ Γ.length := by
  induction x, Γ, h using Fresh.rec with
  | nil x => simp [Ctx.length]
  | snoc x y Γ h hne h' ih ih' => simp
```

Any number of members of either kind are allowed, with parameters, universe
parameters, indices on either kind, infinitary recursive fields, and members
named under one another. What erasure cannot reach is rejected with an
explanation rather than lowered wrongly: a *data* member's arity mentioning the
block, a field that is neither a member's type nor a proof of one of the block's
propositions (`(h : Γ = Γ')`, where erasing would have to transport between
`Γ = Γ'` and `Γ.val = Γ'.val`), a field that *binds* a member (`(f : Ctx → Ctx)`),
and a `Prop` index that merely contains one (`List Ctx`). We only claim a block
whose headers Lean has *already* failed to elaborate and one of whose arities
names a sibling; `MumiTests/IndInd.lean` pins all of it.

### A nested type that denests to one

Nobody writes an induction-inductive block by accident, but Lean will build one
for you. Denesting specialises the nesting type constructor to the block, and if
that type is a family indexed by another type being specialised, the enlarged
block is induction-inductive. A tree that is well-formed by construction and
stores itself is the smallest interesting case:

```lean
inductive Tree (α : Type u) where
  | empty
  | node (key : Nat) (value : α) (l r : Tree α)
inductive Tree.WFWith (α : Type u) : Tree α → List Nat → Prop where ...
inductive Tree.WF (α : Type u) : Tree α → Prop where
  | intro (l : List Nat) (t : Tree α) (h : Tree.WFWith α t l) : Tree.WF α t
inductive WFTree (α : Type u) : Type u where
  | mk (x : Tree α) (h : x.WF)

inductive RecWFTree where
  | mk (x : WFTree RecWFTree)
```

Copying `WFTree` at `RecWFTree` drags in `Tree`, and copying `Tree` drags in
`Tree.WF` and `Tree.WFWith`, whose arities are indexed by the copy of `Tree`:
five members, and exactly the narrow class above. Here the copies are only
*isomorphic* to the originals — the `propext` route does not apply, and
`WFTree RecWFTree` cannot even be written until `RecWFTree` exists — but the
isomorphism is definable, so everything anyone reads is stated over the
originals anyway:

```lean
#check @RecWFTree.mk    -- WFTree RecWFTree → RecWFTree
#check @RecWFTree.rec
-- {C_RecWFTree : RecWFTree → Sort u_1} → {C_WFTree : WFTree RecWFTree → Sort u_1} →
--   {C_Tree : Tree RecWFTree → Sort u_1} →
--     ((x : WFTree RecWFTree) → C_WFTree x → C_RecWFTree (RecWFTree.mk x)) → … →
--       (t : RecWFTree) → C_RecWFTree t
```

`RecWFTree._nested_mk` and `._nested_rec` are the kernel-facing forms; the plain
names are built from them out of `X.ofOrig`, `X.toOrig` and the round-trip
equation `X.ofOrig_toOrig`. The plain `.rec` is always free to take, because
every member of a lowered block is a `def` and Lean generates no recursor of its
own for it. The bridge is all or nothing: if any step fails — two copies that
need each other have no order to build it in — the environment is rolled back
and the plain names are the raw declarations again.
`MumiTests/NestedIndInd.lean` pins that, along with parameters and indices
carried into the copies.

### How it works

Erase the proof fields and declare what is left; put back what erasure forgot
with a *function*, not an inductive; take the subtype.

```lean
inductive Ctx._pre : Type where
  | nil  : Ctx._pre
  | snoc : Ctx._pre → String → Ctx._pre

inductive Fresh._pre : String → Ctx._pre → Prop where ...

def Ctx._wf : Ctx._pre → Prop :=
  Ctx._pre.rec (motive := fun _ => Prop) True (fun Γ x ih => ih ∧ Fresh._pre x Γ)

def Ctx := { Γ : Ctx._pre // Ctx._wf Γ }
def Fresh (x : String) (Γ : Ctx) : Prop := Fresh._pre x Γ.val
```

`_wf` being a function is what makes this cheap: `Ctx._wf (.snoc Γ x)` *is*
`Ctx._wf Γ ∧ Fresh._pre x Γ`, definitionally, so "inversion" is `And.left` and
`And.right` and no inversion lemmas have to be generated — one conjunct per
recursive field, one per erased proof.

`Ctx.rec` is structural recursion on the pre-type with the well-formedness proof
threaded through, so it is computable for the same reason the heterogeneous
recursors are. Both iota rules hold by `rfl` and nothing depends on an axiom,
resting on the same two things as the lowering above: proof irrelevance, which
collapses the `_wf` proofs, and definitional eta for structures, which gives
`⟨Γ.val, Γ.property⟩ ≡ Γ`.

`Fresh.rec` needs none of that machinery, because `Fresh` *is* `Fresh._pre` at
the `.val`s of its indices — the only thing wrong with `Fresh._pre.rec` is the
world its motive and minor premises are stated in. So it is run at the
transported motive `fun Γ₀ h => ∀ w, C ⟨Γ₀, w⟩ h`, a statement about *every* way
of making `Γ₀` well-formed, and the result applied to the major premise's own
indices, where `⟨Γ.val, Γ.property⟩ ≡ Γ` closes it. A minor handed a data field
in the pre-world puts it back at its subtype using a proof read off the
conclusion's `_wf`, which contains the well-formedness of everything the
constructor was built from.

## Turning it off

```lean
set_option mumi.enabled false
```

Stock behaviour returns immediately, including the stock error message.

## Limitations

* A member's universe has to be decidably `Prop`-or-not, so `inductive X : Sort u`
  and `Sort (imax u v)` are rejected — as they are by Lean itself. `imax` inside
  a *field* is fine.
* Two data members that hold each other are in one component and must share a
  universe. Universes may differ only across components.
* For a heterogeneous block, universe parameters have to be declared with
  `universe` up front: with auto-bound implicits each member gets its own
  parameter list, and `mutual` rejects the block before we see it. (An
  induction-inductive block elaborates its own headers, so `Type u` works
  undeclared there.)
* Structures, classes and coinductive members are not lowered; a `mutual` block
  containing one is left to Lean.
* In a *heterogeneous* denesting, only a copy that is a `Prop` gets the equality,
  the coercions and the display that hide it. A *data* copy — `N.nested_List_2`
  for `Nonempty (List N)` — is merely isomorphic to what it copies, and you are
  on your own. (The induction-inductive path builds that isomorphism; this one
  does not.)
* A coercion needs a target, so a consumer whose own type argument is still a
  metavariable does not get one: `Nonempty.elim h fun _ => …` on a field bound by
  a pattern match needs `h` ascribed, or `Nonempty.elim (α := T)`.
* An induction-inductive block must be *narrow*, and one whose data genuinely
  depends on data — `Ctx` indexed by its own length — is out of scope. Its data
  members share one erased pre-block, hence one universe, and none may sit at a
  bare `Sort u`. Section `variable`s are not supported.
* Its constructors are `def`s, so `match` does not work and there is no `injEq`
  or `noConfusion`; a bare `induction`/`cases` destructs the underlying subtype
  and leaks `Ctx._pre` into the goal. Use `induction Γ using Ctx.rec`, and for a
  `Prop` member list the indices as targets — `induction x, Γ, h using Fresh.rec`.
  A bare `cases` on a `Prop` member reaches for the pre-type's `casesOn` and so
  works only where the motive does not depend on the indices.
* A nested inductive whose denesting is induction-inductive is rescued only from
  a standalone `inductive`, not from a member of a `mutual` block, and only when
  the nesting type is not itself part of a mutual family. Nesting parameters
  that mention a constructor-local are out on that path too, though not on the
  merely heterogeneous one.
* Importing this library changes the formatting of a few kernel error messages
  (some gain a `(kernel)` prefix). This affects declarations the library never
  touches, and `set_option mumi.enabled false` does not suppress it.

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
