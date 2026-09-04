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
the declaration first, and only if that fails, and only if denesting it ourselves
yields something Lean could not have yielded, do we take the block over. Anything
else is rolled back and Lean's error rethrown verbatim.

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

That is the second thing denesting can yield that Lean cannot, and it is a reason
to take a block over in its own right — the result need not be heterogeneous at
all. A plain data nesting whose parameter mentions a field works the same way:

```lean
inductive Wrap (α : Type) (n : Nat) | mk (a : α)

inductive A where
  | tip
  | mk (n : Nat) (v : List (Wrap A n))     -- same kernel refusal, same rescue

#check @A.mk    -- (n : Nat) → List (Wrap A n) → A
```

so does the same shape inside a `mutual` of data members.

Both retries recognise this shape, and the induction-inductive one is offered it
first, because that route can state the block back over the type it copied: it
is `A.mk 3 [.mk .tip]` written with list syntax, and `A.rec`'s minor premises
are `List`'s own. The price is the one that route always charges — `A.mk` is a
`def`, so `match` and `cases` do not work on it, and one recursor serves the
whole block.

Lowering relates a data copy to its original too, but by an isomorphism rather
than an equality, which is the most that can be true of two distinct data types.
Each copy gets `toOrig` and `ofOrig` and a coercion each way, so a list already
in hand goes in and comes out, and both directions compile. What it does not get
is the display: a `Prop` copy is *equal* to its original and can be shown as it,
and a data copy has to be shown under its own name. Which copies are settled
together is read off the recursor, so a copy reached through another copy —
`RL` defined through `List (RL α)`, nested in a heterogeneous block — is bridged
in the same pass, and a cycle of them goes in as one mutually recursive group.
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

`Mumi` takes such a block when it is **narrow** — every field of a data
constructor whose type mentions a `Prop` member is itself a proof. Every member
then gets a recursor stated over the block as written, and
they are all the *same* recursion: one `Sort u` motive per data member, and one
`Prop` motive per predicate, each taking the value the data motive produced at
the index it is about. That last argument is the point — it is what lets a proof
by `Fresh.rec` say something about a function defined by `Ctx.rec`.

```lean
def Ctx.names : Ctx → List String :=
  Ctx.rec (motive_1 := fun _ => List String) (motive_2 := fun x _ ns _ => x ∉ ns)
    [] (fun _ x _ ih _ => x :: ih)
    (fun _ => by simp)
    (fun _ _ _ _ hne _ _ _ ih => by simp only [List.mem_cons, not_or]; exact ⟨hne, ih⟩)

theorem Fresh.not_mem {x : String} {Γ : Ctx} (h : Fresh x Γ) : x ∉ Γ.names :=
  Fresh.rec (motive_1 := fun _ => List String) (motive_2 := fun x _ ns _ => x ∉ ns)
    [] (fun _ x _ ih _ => x :: ih)
    (fun _ => by simp)
    (fun _ _ _ _ hne _ _ _ ih => by simp only [List.mem_cons, not_or]; exact ⟨hne, ih⟩)
    x Γ h
```

The dependency need not run through a proof. A *data* member's arity may mention
the block as well, which is the shape every dependent type theory is written in:

```lean
mutual
inductive Ctx : Type where
  | nil  : Ctx
  | snoc : (Γ : Ctx) → Ty Γ → Ctx
inductive Ty : Ctx → Type where
  | base : (Γ : Ctx) → Ty Γ
  | pi   : (Γ : Ctx) → (A : Ty Γ) → Ty (Ctx.snoc Γ A) → Ty Γ
inductive Tm : (Γ : Ctx) → Ty Γ → Type where
  | var : (Γ : Ctx) → (A : Ty Γ) → Tm (Ctx.snoc Γ A) (Ty.base (Ctx.snoc Γ A))
  | lam : (Γ : Ctx) → (A : Ty Γ) → (B : Ty (Ctx.snoc Γ A)) →
      Tm (Ctx.snoc Γ A) B → Tm Γ (Ty.pi Γ A B)
end

#check @Tm.rec
-- … → ((Γ : Ctx) → (A : Ty Γ) → motive_1 Γ → motive_2 Γ A →
--        motive_3 (Γ.snoc A) (Ty.base (Γ.snoc A)) (Tm.var Γ A)) → …
```

An index like `Ty`'s is *deleted*: the pre-world has no `Ctx` to state a `Ty` at,
so `Ty._pre` carries no index and the well-formedness puts a `Ctx._pre` back. A
constructor either gives a deleted index as a field of its own or **builds** it —
`Tm.var` builds both of its, the second out of the first — and the alternative is
handed the index the recursion arrived at rather than the constructor's reading
of it, with the equation the well-formedness carries to get from the one to the
other. What comes out is the alternative the block was written with, and terms
compute.

Motives and minor premises are named as they are for a Lean `mutual` —
`motive_1 … motive_n` in block order (just `motive` when a recursor has one),
minors after their constructors with repeats numbered — so `induction Γ using
Ctx.rec with | nil | snoc … | nil_1 | snoc_1` reads the way it would for a real
inductive.

That recursor asks for every motive in the block, and a goal about one member
determines only its own, so it is `using`-only — as a Lean `mutual` block's
recursors are. So each member also gets a recursor with the others' motives
discharged and one motive left:

```lean
#check @Ctx.recD    -- {motive : Ctx → Sort u_1} → …, every `Prop` motive at `True`
#check @Fresh.recP  -- {motive : … → Prop} → …, every data motive at `Unit`

example (Γ : Ctx) : True := by induction Γ with | nil => trivial | snoc Γ x h ih => trivial
```

Discharging a motive of the *other* kind costs nothing a proof of that shape
could have used: `True` is what a goal with no predicate motive was going to
prove at each proposition anyway, and `Unit` is what a proof about a predicate
was going to compute at each data member. Discharging one of the same kind —
two data members, or two propositions — does cost the hypotheses at the member
that went, and is done anyway: a member here is a `def`, so a bare `induction`
that finds no eliminator does not stop the way mainline stops a `mutual`, it
unfolds the member and splits on the subtype. `X.recD` keeps the full `Sort u`
elimination; `X.recP` lands in `Prop`, as the block-wide recursion does. Both
are registered as the `induction` tactic's default eliminator for their member,
so a bare `induction Γ` and a bare `induction h` work, and the corresponding
`X.casesD` and `X.casesP` do the same for `cases`. `MumiTests/SoloRec.lean`
pins which blocks get what.

Every recursor is `@[elab_as_elim]`, which Lean gives its own recursors for free
and a `def` has to be told, so an application generalises its motive over the
major premise rather than taking whatever the expected type unifies with. The
block-wide recursor is the exception at a predicate: `Fresh.rec` is for term
mode, because `induction … using` reads an eliminator's targets only up to the
first motive argument that is not a local variable, and for a predicate motive
that is the data value the proposition stands at. `Fresh.recP`, which has no
data motive left to take one, is the one the tactic drives.

A block keeps the older split — a data recursor with no predicate motives, and a
separate recursor per predicate, free to eliminate into `Sort u` — in two cases.
One is a `Prop` member not indexed by exactly one data member: a relation
`Rel : Lst α → Lst α → Prop` is not a fact about either of its arguments, and
there is no one value for the recursion to carry it alongside. The other is a
`Prop` constructor whose index *pins* a field of the data constructor it stands
at instead of naming it — `Short.cons (a : α) : Short (.cons a .nil)` fixes the
tail to `.nil`, and the recursion, which has a call at that tail, would be left
computing at a term it is not recursing on. `set_option trace.Mumi true` reports
which recursor a block got, and which ones took `@[elab_as_elim]`.

Any number of members of either kind are allowed, with parameters, universe
parameters, indices on either kind, infinitary recursive fields, and members
named under one another. A data member may be indexed by one of the propositions
— `Tm : (Γ : Ctx) → Ok Γ → Type` — and the index is deleted like any other and
handed back to the well-formedness, where being a proof only means the predicate
never looks at it: `Tm Γ h` and `Tm Γ h'` are then the same type by `rfl`, as
they are of a real inductive family. What erasure cannot reach is rejected with
an explanation rather than lowered wrongly: a *data* member's arity mentioning
the block, a field that is neither a member's type nor a proof of one of the
block's propositions (`(h : Γ = Γ')`, where erasing would have to transport
between `Γ = Γ'` and `Γ.val = Γ'.val`), a field that *binds* a member
(`(f : Ctx → Ctx)`), a `Prop` index that merely contains one (`List Ctx`), and a
proof index a constructor *builds* rather than takes as a field
(`Tm.top : Tm .nil .nil`), for which there is no equation the pre-world could
state. We only claim a block
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
-- {motive_1 : RecWFTree → Sort u_1} → {motive_2 : WFTree RecWFTree → Sort u_1} →
--   {motive_3 : Tree RecWFTree → Sort u_1} →
--     {motive_4 : (a : Tree RecWFTree) → motive_3 a → Tree.WF RecWFTree a → Prop} →
--       {motive_5 : (a : Tree RecWFTree) → (l : List Nat) → motive_3 a →
--                     Tree.WFWith RecWFTree a l → Prop} →
--         ((x : WFTree RecWFTree) → motive_2 x → motive_1 (RecWFTree.mk x)) → … →
--           (t : RecWFTree) → motive_1 t
```

Five members, five motives, seven minors — the same single recursor the block
would get if it had been written out by hand, and none of it mentions a copy.
The predicate motives are the reason to want it. Without them, the minor for
`WFTree.mk (x : Tree α) (h : x.WF)` is handed a proof that the tree it was
*given* is well-formed and asked for a value at the tree the recursion *built*,
and nothing bridges the two: a map defined by recursion over `RecWFTree` gets
stuck at exactly that step. With them, `motive_4` says the rebuilt tree is
well-formed, the `WFWith` minors maintain it, and an isomorphism between two
copies of this block is definable from the user-side constants alone — no
`sorry`, no appeal to the underlying subtype, and no axioms.

`RecWFTree._nested_mk` and `._nested_rec` are the kernel-facing forms; the plain
names are built from them out of `X.ofOrig`, `X.toOrig` and the round-trip
equation `X.ofOrig_toOrig`. The plain `.rec` is always free to take, because
every member of a lowered block is a `def` and Lean generates no recursor of its
own for it. The bridge is all or nothing: if any step fails — a group of copies
mixing data and `Prop` has no shape to compile in, one being a function and the
other a theorem — the environment is rolled back and the plain names are the raw
declarations again, which `set_option trace.Mumi.indind true` will say.

Copies that need each other are found and built together rather than in
sequence: `Rose α`, whose own field is a `List (Rose α)`, and the two members of
a `mutual` family, since specialising one of those calls for specialising all of
them. Each copy in such a group is given a real motive when the others are
built, so a sibling arrives as an induction hypothesis instead of as a call to a
declaration that does not exist yet.

Only the type the writer declared gets its own name for the whole-block
recursor. The other members of a denested block are types that already existed,
and their `.rec` is Lean's own; the recursion over the enlarged block is reached
through the writer's.

`MumiTests/NestedIndInd.lean` pins the motivating block, along with parameters
and indices carried into the copies, a nesting type that nests again
(`Rose`, into `List (Rose _)`), one that is a member of a `mutual` family, and
one applied to a field of the constructor it sits in, which copies a whole
family at once and indexes it by that field.
Two sweeps follow it. `MumiTests/GrandRec.lean` varies the block: abstract
universes and two parameters, two predicates over one data member, infinitary
fields in both the data and the `Prop` member, two unrelated nesting families in
one constructor, and a `mutual` family of two `Prop`s where the copy of the
member nobody wrote still gets a motive.
`MumiTests/Shapes.lean` varies the path from the writer's constructor down to
the recursive occurrence, holding one family fixed: through a second copy of
that family (`WFTree (WFTree R)`, which copies it twice over and gives seven
motives), through a `List`, twice in one constructor, at an indexed member,
through a function field, from a writer with its own parameter at an
abstract universe, and from an indexed writer that passes its own index into the
nesting (`mk (n : Nat) (x : WFTree (R n)) : R n`). It also varies how the bundle of a value and its proof is
spelled — an `inductive`, a `structure`, or just `{ t : Tree R // t.WF }`, which
needs no new declaration at all and gives the same four-motive recursor — and
puts an ordinary nesting beside the induction-inductive one (`mk (x : WFTree R)
(l : List R)`), a container inside the family's parameter (`WFTree (Option R)`),
and a second writer nested at a first (`WFTree (Ra × Rb)`, where only `Rb` is
being defined and only `Rb` gets an induction hypothesis). Both sweeps also hold
the shapes that fall back to split recursors or are not rescued at all.

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

The recursion is structural on the pre-type with the well-formedness proof
threaded through, so it is computable for the same reason the heterogeneous
recursors are. The iota rules hold by `rfl`, resting on the same two things as
the lowering above: proof irrelevance, which collapses the `_wf` proofs, and
definitional eta for structures, which gives `⟨Γ.val, Γ.property⟩ ≡ Γ`.

What that recursion computes is a *bundle*: at each data pre-value, the value of
the data motive, paired with a proof of the predicate motive for every proof of
every `Prop` member standing at that value. One `PSigma`, so all of it lands in
one universe, and one recursion, so the two halves see each other — that is why
a minor premise for a data constructor may use the induction hypotheses of the
proofs it carries, and why a predicate's minor premise gets to talk about the
value the data motive produced. `Ctx.rec` is the bundle's first projection and
`Fresh.rec` the matching conjunct of its second, so the cross-member iota rule
above is `rfl` too.

Where the block falls back to split recursors, the `Prop` half needs none of
that machinery, because `Fresh` *is* `Fresh._pre` at the `.val`s of its indices —
the only thing wrong with `Fresh._pre.rec` is the world its motive and minor
premises are stated in. So it is run at the transported motive
`fun Γ₀ h => ∀ w, C ⟨Γ₀, w⟩ h`, a statement about *every* way of making `Γ₀`
well-formed, and the result applied to the major premise's own indices, where
`⟨Γ.val, Γ.property⟩ ≡ Γ` closes it. A minor handed a data field in the
pre-world puts it back at its subtype using a proof read off the conclusion's
`_wf`, which contains the well-formedness of everything the constructor was
built from.

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
* In a *heterogeneous* denesting, only a copy that is a `Prop` gets the equality
  and the display that hide it. A *data* copy — `N.nested_List_2` for
  `Nonempty (List N)` — is only isomorphic to what it copies, which is the most
  two distinct data types can be, so it keeps its own name in signatures, goals
  and error messages; `toOrig`, `ofOrig` and a coercion each way cross between
  them. A copy this route cannot bridge is dropped from the group and the rest
  still land, so a block may come out with some copies related to their
  originals and others bare; `set_option trace.Mumi true` names the ones that
  did not go through and why.
* A data copy has to be *named*, not only read, to recurse into the nesting. A
  function on `S` that recurses through an `S.t : Tree S → S` needs a companion
  at the nested type, and the companion has to be declared at
  `S.nested_Tree_1`: the coercion from `Tree S` is a function, so an argument of
  the original type is a subterm of nothing and no measure decreases. Declared
  at the copy it goes through and computes. This is the one place the copy is
  more than a matter of display, and only the lowering route has it — over on
  the induction-inductive route the block is stated over the originals outright,
  so the question never comes up.
* A coercion needs a target, so a consumer whose own type argument is still a
  metavariable does not get one: `Nonempty.elim h fun _ => …` on a field bound by
  a pattern match needs `h` ascribed, or `Nonempty.elim (α := T)`.
* An induction-inductive block must be *narrow*. A data member's index may
  mention the block, and the erasure deletes such an index outright, so it has
  to be a member's own type applied to arguments — `(f : Nat → Ctx)` is not one,
  and neither is a proof of one of the block's propositions, since erasure keeps
  a proposition's proofs nowhere. What is left of the deleted index's type may
  name the indices that *stayed* but not the ones that went, because the deleted
  indices are handed round as an array and an array has nowhere for one entry to
  have bound another: `Ctx : Nat → Type` beside `Ty : (n : Nat) → Ctx n → Type`
  is fine, the deleted `Ctx n` reading `Ctx._pre n` and `n` being an index that
  stayed. An index that stays may not mention one that goes. No data member may
  sit at a bare `Sort u`. Section `variable`s are not supported.
  Its data members need not share a universe: they become one erased pre-block,
  and that pre-block is emitted through the lowering rather than straight to the
  kernel, so the two passes compose — erasure removes the arity dependency, and
  the lowering removes the universe difference in what is left. The rules
  underneath survive: data members that recurse into *one another* still have to
  agree, since an edge puts one universe at or below the other and a cycle makes
  them equal, and a field still has to fit inside the member it belongs to.
* Its constructors are `def`s, so `match` does not work and there is no
  `noConfusion` at the name one would reach for. They do get `X.c.inj` and a
  `@[simp] X.c.injEq`, stated exactly
  as the ones a real inductive's constructors get — the field an index pins is
  shared rather than compared, a proof field is left out, a dependent field is
  compared with `HEq` — so `simp` takes a constructor equation apart the way it
  would anywhere else. A field at a *denested copy* works too: the equation
  reduces to that copy's `ofOrig` of either side, and the bridge proves each
  copy an `X.ofOrig_inj` out of the round trip taken from the original, which
  reads it back. Two *different* constructors
  are told apart by a simproc instead of a theorem — a lemma per pair would be
  quadratically many declarations, and the one simproc pushes the equation
  through `Subtype.val` and asks the erased pre-block's own `noConfusion` — so
  `Ctx.nil ≠ Ctx.snoc Γ A` and the rest of that family go by `simp` as well, at
  a denested copy included. `induction` and `cases` work,
  on the `X.recD`/`X.recP` and
  `X.casesD`/`X.casesP` registered as their defaults; where the block had to
  discharge a motive of the same kind to get one — two data members, or two
  propositions — the hypotheses at the member that went are gone with it, and
  `induction Γ using Ctx.rec` with the motives the goal does not fix is still
  the strong reading. The block-wide recursor does not drive `induction … using`
  at a *predicate* — `getElimInfo` reads targets only up to the first motive
  argument that is not a local, and the data value is not one — so use that one
  in term mode, or wrap it in a lemma whose motive takes only the indices.
* `deriving` on an induction-inductive block reaches its members only through
  `Subtype`, since a data member there *is* one. The class is derived for the
  pre-type, where the constructors are, and lifted; `DecidableEq` and `Repr`
  come across that way, `Repr` printing the pre-term, constructor names and all.
  A class with nothing to lift, `Inhabited` among them, says so and leaves the
  block standing. For a block that was rescued rather than written as a
  `mutual`, the clause helps pick the route: a class this path can answer keeps
  the field as it was written, and one it cannot sends the block to lowering,
  which can.
* One recursor serves the whole block, so every use supplies every motive, and
  two recursions that differ in the motives they were given are not defeq. A
  `Prop` member covered by it eliminates only into `Prop`, even a subsingleton
  one that could have had large elimination under the split.
* A `Prop` member indexed by no data member, or by two, keeps the split
  recursors, and so does one whose constructor pins a field of the data
  constructor it stands at rather than naming it. The consolation is that a
  split `Prop` recursor may eliminate into `Sort u`.
* A `Prop` constructor with a data field its *conclusion* never mentions —
  `Pair.cons (a : α) (t u : Chain α) (h : Pair t) : Pair (.cons a t)`, where `u`
  goes nowhere — costs more than that. Such a field cannot be put back at its
  subtype: a `Prop` constructor carries no well-formedness of its own, only what
  its indices bring it, so there is nothing to state that minor premise with.
  The `Prop` members share one erased recursion, so one such constructor costs
  the block every `Prop` recursor, and in a denested block the map back to the
  originals goes through those recursors, so the copies stay visible too. The
  writer's own type still works and the block is still sound; it is the
  presentation that degrades. `set_option trace.Mumi.indind true` names the
  constructor and the field.
* Two `Prop` members each in the other's arity are out of scope, and that is all
  that is left of the restriction. No member of a mutual inductive may appear in
  another's arity, but nothing says the propositions have to be *one* mutual
  inductive: nothing is defined by recursion across the whole of them, so they
  are declared in layers, and one indexed by an earlier one names its pre-type
  as freely as it names the data. A genuine cycle admits no such order.
* A copy's parameters are fixed before its constructors are known, so a nesting
  applied to something that mentions a field of the constructor it appears in
  cannot be copied at one parameter. Both routes abstract the field out and make
  it an *index* of the copy instead, so one copy stands for the whole family:
  `mk (n : Nat) (x : WFTree (R n)) : R n` gets a copy
  `R.nested_WFTree_1 : Nat → Type`, and the recursor's motive for it is over
  `WFTree (R n)` with the `n` in front. The field's own type has to be free of
  the block for that telescope to be writable. In `mk (b : Box R) (h : b.Never)`
  it is not, so that one turns on where `Never` puts its `Box α` binder: an
  *index* is never specialised in the first place and the block goes through,
  while a declared *parameter* wants a copy indexed by `Box R`, which is itself
  a member. The sharpest form of that is a
  nesting over an equation between two fields — `mk (a b : Z) (h : a = b)` —
  where the abstracted field is of block type, so the copy would have to be
  *indexed by* a member and the block would have to be routed back through the
  induction-inductive path it came out of. It reports *Cannot denest `a = b`*.
* The head of a nesting has to be an inductive, so `Quot` at one is out and
  stays out: there is nothing to specialise to the block.
* In a denested block only the writer's own type carries the whole-block
  recursor; the other members are pre-existing types whose `.rec` is Lean's.
* An *indexed* block's recursor depends on `propext`, by way of the `injEq`
  Lean's own `cases` uses to unify indices, and a denested block with an
  *infinitary* constructor depends on `Quot.sound`, because the round trip
  between a copy and its original is the identity only up to `funext`. Blocks
  with neither add no axiom.
* A nested inductive whose denesting is induction-inductive is rescued from a
  standalone `inductive` and from a `mutual` block of data members alike, the
  nesting type may itself be a member of a mutual family, and the nesting's
  parameters may mention a field of the constructor they sit in. A `Prop` member
  with *no constructors* is asked for its parameters with no constructors to
  read them off, so Lean promotes the index it was written with to one;
  denesting specialises only as far as the block reaches, which leaves the
  promotion an index of the copy again and gets the writer the block they wrote.
  A declaration we decline reports *Lean's* error and
  drops ours, which is right for a block that was never ours and unhelpful for
  one that was: `set_option trace.Mumi.rescue true` keeps every retry's reason.
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
