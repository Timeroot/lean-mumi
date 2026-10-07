/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import MumiTests.Spec.Harness

/-!
# Shapes at the edge of what the block elaborators take

The other test files each grow out of one construction and vary it.  This one
is the opposite: a sweep of block shapes written down without reference to how
the library works, kept because they came out whole and so are worth being told
about if they stop doing so.  Several of them are combinations -- a nesting at
a member another member indexes, an ind-ind block across two universes, a
denesting that wants a constructor's field as an index of a copy -- that each
of the other files exercises one half of.

The last section is the one shape in the sweep that does not come out.  It is
here for the same reason `MumiTests.Shapes` keeps its two: so that a change in
what the library accepts is a test failure and not a surprise.
-/

namespace MumiTests.Boundary

/-! ## A member indexed by a list of another

`Sub` is data, and its index is a `List Ctx` -- a nesting of a member, in the
*arity* of a member.  The arity is where a member may not appear, so the index
is deleted and given back by the well-formedness; that the thing deleted is a
container of a member rather than a member is what this pins.
-/

namespace ListIdx

mumi_spec (xfail := [rec, recOn, casesOn])
mutual
inductive Ctx : Type where
  | nil
  | snoc (Γ : Ctx) (A : Ty Γ) : Ctx
inductive Ty : Ctx → Type where
  | base (Γ : Ctx) : Ty Γ
inductive Sub : List Ctx → Type where
  | nil : Sub []
  | cons (Γ : Ctx) (Γs : List Ctx) (A : Ty Γ) (s : Sub Γs) : Sub (Γ :: Γs)
end

example : Sub [.nil] := .cons .nil [] (.base .nil) .nil

end ListIdx

/-! ## A nesting at a member another member indexes

`Ctx.many` reaches its own block through a `List`, and `Ty` is indexed by
`Ctx`.  The recursion the block gets has a motive for the container as well as
for the two members, which is what a nesting always adds, and the container's
motive is indexed by the context the list is at.
-/

namespace ListNest

mumi_spec (simp := [Ctx.rec_many, Ty.rec_list, Ctx.rec_1_cons, Ctx.casesOn_many, Ty.casesOn_list])
mutual
inductive Ctx : Type where
  | nil
  | many (Γ : Ctx) (As : List (Ty Γ)) : Ctx
inductive Ty : Ctx → Type where
  | base (Γ : Ctx) : Ty Γ
  | list (Γ : Ctx) (As : List (Ty Γ)) : Ty Γ
end

example : Ctx := .many .nil [.base .nil, .list .nil []]

end ListNest

/-! ## The same, through `Prod`, `Option` and `Except`

A container with two fields of the nested type, one with none, and one whose
other summand is unrelated.
-/

namespace OtherNests

mumi_spec (simp := [Ctx.rec_maybe, Ctx.rec_either, Ctx.casesOn_maybe, Ctx.casesOn_either])
mutual
inductive Ctx : Type where
  | nil
  | pair (Γ : Ctx) (p : Ty Γ × Ty Γ) : Ctx
  | maybe (Γ : Ctx) (A : Option (Ty Γ)) : Ctx
  | either (Γ : Ctx) (A : Except Nat (Ty Γ)) : Ctx
inductive Ty : Ctx → Type where
  | base (Γ : Ctx) : Ty Γ
end

example : Ctx := .pair .nil (.base .nil, .base .nil)
example : Ctx := .maybe .nil none
example : Ctx := .either .nil (.error 3)

end OtherNests

/-! ## A nesting whose parameters mention a field of the constructor

`Vec (Ty Γ) n` takes its length from `n`, which `Ctx.snoc` binds.  That is the
denesting the kernel refuses outright -- it specialises a nesting only at
closed parameters -- so the copy is one the library has to make, inside a block
that is induction-inductive besides.
-/

namespace LocalNest

mumi_spec
inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons {n} (a : α) (v : Vec α n) : Vec α (n + 1)

mumi_spec (simp := [Ctx.rec_snoc, Ctx.rec_1_cons, Ctx.casesOn_snoc])
mutual
inductive Ctx : Type where
  | nil
  | snoc (n : Nat) (Γ : Ctx) (v : Vec (Ty Γ) n) : Ctx
inductive Ty : Ctx → Type where
  | base (Γ : Ctx) : Ty Γ
end

example : Ctx := .snoc 1 .nil (.cons (.base .nil) .nil)

end LocalNest

/-! ## An infinitary field at an indexed member

`Ctx.fam` holds a family of types over its own context, so the recursion's
hypothesis about it is a family of hypotheses.
-/

namespace Infinitary

mumi_spec (xfail := [injEq])
mutual
inductive Ctx : Type where
  | nil
  | fam (Γ : Ctx) (f : Nat → Ty Γ) : Ctx
inductive Ty : Ctx → Type where
  | base (Γ : Ctx) : Ty Γ
end

example : Ctx := .fam .nil fun _ => .base .nil

end Infinitary

/-! ## Two universes across an induction-induction

`Ctx` is a `Type 1` and `Ty` a `Type`, so the block is heterogeneous *and*
induction-inductive.  Only one of the two elaborators can have it, and it is
the ind-ind one: the arity is what decides, and the universes then sort
themselves out because the pre-types are the ones that have to agree.
-/

namespace TwoUniverses

mumi_spec
mutual
inductive Ctx : Type 1 where
  | nil
  | snoc (Γ : Ctx) (A : Ty Γ) : Ctx
inductive Ty : Ctx → Type where
  | base (Γ : Ctx) : Ty Γ
end

example : Ctx := .snoc .nil (.base .nil)

end TwoUniverses

/-! ## One constructor each

Nothing here is recursive except through the index, so the block is the
smallest induction-induction there is.
-/

namespace SingleCtor

mumi_spec
mutual
inductive Ctx : Type where
  | mk (n : Nat) (A : Ty n) : Ctx
inductive Ty : Nat → Type where
  | mk (n : Nat) : Ty n
end

example : Ctx := .mk 2 (.mk 2)

end SingleCtor

/-! ## A section variable the block picks up

`α` is a variable of the section and is used by one member only; both members
take it as a parameter, which is what Lean does for a `mutual` block of its
own.
-/

namespace SectionVar

section
variable (α : Type)

mumi_spec
mutual
inductive Ctx : Type where
  | nil
  | snoc (Γ : Ctx) (A : Ty Γ) : Ctx
inductive Ty : Ctx → Type where
  | base (Γ : Ctx) (a : α) : Ty Γ
end

end

example : Ctx Nat := .snoc .nil (.base .nil 3)

end SectionVar

/-! ## A member indexed by two others of the same type

`Sub.id` gives its context as both indices, which is the case where a field
can stand for only one of the positions it is written at and the other is
treated as one the constructor built.
-/

namespace TwoIdx

mumi_spec (xfail := [recOn, casesOn])
mutual
inductive Ctx : Type where
  | nil
  | snoc (Γ : Ctx) (A : Ty Γ) : Ctx
inductive Ty : Ctx → Type where
  | base (Γ : Ctx) : Ty Γ
inductive Sub : Ctx → Ctx → Type where
  | id (Γ : Ctx) : Sub Γ Γ
  | wk (Γ : Ctx) (A : Ty Γ) : Sub (.snoc Γ A) Γ
end

example : Sub (.snoc .nil (.base .nil)) .nil := .wk .nil (.base .nil)

end TwoIdx

/-! ## The recursor computes

Both iota rules of an ind-ind block are definitional, and `rfl` is what says
so at a recursor applied by hand rather than through `induction`.
-/

namespace Iota

mumi_spec
mutual
inductive Ctx : Type where
  | nil
  | snoc (Γ : Ctx) (A : Ty Γ) : Ctx
inductive Ty : Ctx → Type where
  | base (Γ : Ctx) : Ty Γ
end

def depth : Ctx → Nat :=
  Ctx.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    0 (fun _ _ n _ => n + 1) (fun _ _ => 0)

example : depth .nil = 0 := rfl
example : depth (.snoc .nil (.base .nil)) = 1 := rfl
example : depth (.snoc (.snoc .nil (.base .nil)) (.base _)) = 2 := rfl

end Iota

/-! ## Two propositions over one data member, each naming the other

The recursion is one recursion over all three, so each proposition's motive is
stated over the data member's motive and the two hypotheses are available to
each other.
-/

namespace EvenOdd

mumi_spec
mutual
inductive Tm : Type where
  | z
  | s (t : Tm)
inductive Even : Tm → Prop where
  | z : Even .z
  | s (t : Tm) (h : Odd t) : Even (.s t)
inductive Odd : Tm → Prop where
  | s (t : Tm) (h : Even t) : Odd (.s t)
end

example : Even (.s (.s .z)) := .s _ (.s _ .z)

end EvenOdd

/-! ## A recursor that cannot be written in full

`Ctx.many` carries a proof of `Ok` at `Γs.headD Γ`, an index the recursion
cannot follow: the hypothesis at `h` would have to speak of the value the data
recursion produces at `Γs.headD Γ`, which is no field of `many` nor built from
one by a constructor of the block.  The recursor the block is owed cannot be
stated, so by default the block is rejected. -/

namespace Gap

mumi_spec (rejects)
mutual
inductive Ctx : Type where
  | nil : Ctx
  | many (Γ : Ctx) (Γs : List Ctx) (h : Ok (Γs.headD Γ)) : Ctx
inductive Ok : Ctx → Prop where
  | nil : Ok .nil
end

/-! Under `mumi.partialRecursors` the block is to be declared with the recursor
it can have, the hypothesis at `h` left out, and pinned by `mumi_spec` there.
What it does today -- and so what to work on -- is reject it all the same. -/

/--
error: The proof field `h` of `MumiTests.Boundary.Gap.Ctx.many` mentions a data member of the block in its type, so erasing it would not be definitionally invisible:
  Ok (List.headD Γs Γ)
-/
#guard_msgs in
set_option mumi.partialRecursors true in
mutual
inductive Ctx : Type where
  | nil : Ctx
  | many (Γ : Ctx) (Γs : List Ctx) (h : Ok (Γs.headD Γ)) : Ctx
inductive Ok : Ctx → Prop where
  | nil : Ok .nil
end

end Gap

end MumiTests.Boundary
