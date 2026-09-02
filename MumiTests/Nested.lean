import Mumi

/-!
# Rescued nested inductives

A nested inductive whose denesting is universe-heterogeneous is rejected by the
kernel.  `Mumi.elabDeclarationRescuingNested` catches that and denests the block
itself, so the declaration goes through.

Everything here is a declaration Lean rejects.  The cases Lean *accepts* are in
`MumiTests.NonInterference`, where the point is that nothing about them changes.
-/

/-! ## The classic case

`Nonempty T` is a `Prop`, `T` is a `Type`, so the block the kernel builds --
`T` together with a copy of `Nonempty` specialised to `T` -- is heterogeneous.
-/

inductive T : Type where
  | mk1 : T
  | mkT : Nonempty T → T

/-- info: T.mk1 : T -/
#guard_msgs in
#check @T.mk1

/-- info: T.mkT : Nonempty T → T -/
#guard_msgs in
#check @T.mkT

-- the copy is displayed as the type it copies, so the constructor reads the way
-- it was written; `mumi.pp.nested` is what shows the block as it is built
/-- info: T.mkT : T.nested_Nonempty_1 → T -/
#guard_msgs in
set_option mumi.pp.nested false in
#check @T.mkT

/-- info: Nonempty T : Prop -/
#guard_msgs in
#check @T.nested_Nonempty_1

/-- info: T.nested_Nonempty_1.intro : ∀ (val : T), Nonempty T -/
#guard_msgs in
#check @T.nested_Nonempty_1.intro

-- the block-wide recursor eliminates `T` into any sort and the nested `Prop`
-- into `Prop`, which is what the kernel would have given had the universes
-- lined up
/--
info: @T.mutualRec : {motive_1 : T → Sort u_1} →
  {motive_2 : Nonempty T → Prop} →
    motive_1 T.mk1 →
      ((a : Nonempty T) → motive_2 a → motive_1 (T.mkT a)) →
        (∀ (val : T) (ih_1 : motive_1 val), motive_2 ⋯) → (t : T) → motive_1 t
-/
#guard_msgs in
#check @T.mutualRec

-- the copy is a `Prop` with the same constructors as the original, so the two
-- are equal, and saying so lets the original type back into the user's code.
-- It reads as a triviality precisely because it holds: both sides display as
-- the original.
/-- info: T.nested_Nonempty_1.eq_orig : Nonempty T = Nonempty T -/
#guard_msgs in
#check @T.nested_Nonempty_1.eq_orig

/-- info: T.nested_Nonempty_1.eq_orig : T.nested_Nonempty_1 = Nonempty T -/
#guard_msgs in
set_option mumi.pp.nested false in
#check @T.nested_Nonempty_1.eq_orig

/-- info: 'T.nested_Nonempty_1.eq_orig' depends on axioms: [propext] -/
#guard_msgs in
#print axioms T.nested_Nonempty_1.eq_orig

/-! ## The copy's name is never needed

The equality is what makes the copy usable, but rewriting along it by hand would
still mean naming the copy at every use.  A coercion in each direction removes
that: the original can be handed to a constructor that asks for the copy, and a
field bound by a pattern match can be handed to anything that asks for the
original.
-/

example (h : Nonempty T) : T := T.mkT h
example : T := T.mkT (Nonempty.intro T.mk1)

-- `propext` is what makes the two *types* equal, but moving a value between
-- them does not need it: each coercion is one half of the `Iff`, a recursor
-- call, rather than a `cast` along `eq_orig`
def T.coerced : T := T.mkT (Nonempty.intro T.mk1)

/-- info: 'T.coerced' does not depend on any axioms -/
#guard_msgs in
#print axioms T.coerced

def T.witnessed (_ : Nonempty T) : Prop := True

def T.probe : T → Prop
  | .mk1 => False
  | .mkT h => T.witnessed h

-- a coercion needs somewhere to go, so a consumer whose type argument is still
-- open does not get one; ascribing the field is enough, and the copy's name is
-- still not what gets written
example (x : T) : True :=
  match x with
  | .mk1 => trivial
  | .mkT h => Nonempty.elim (h : Nonempty T) fun _ => trivial

/--
error: Application type mismatch: The argument
  h
has type
  Nonempty T
but is expected to have type
  Nonempty (?m.6 h)
in the application
  Nonempty.elim h
-/
#guard_msgs in
example (x : T) : True :=
  match x with
  | .mk1 => trivial
  | .mkT h => Nonempty.elim h fun _ => trivial

-- rewriting along the equality still works, for anyone who wants it
example (h : Nonempty T) : T := T.mkT (T.nested_Nonempty_1.eq_orig ▸ h)

-- a genuine mismatch is still reported against the original, not the copy
/--
error: Application type mismatch: The argument
  h
has type
  Nonempty Nat
but is expected to have type
  Nonempty T
in the application
  T.mkT h
-/
#guard_msgs in
example (h : Nonempty Nat) : T := T.mkT h

-- `pp.explicit` asks for the term as it is, so the copy is not dressed up: that
-- is what keeps a mismatch whose two sides would both read `Nonempty T` from
-- being reported as one against itself, since Lean turns the option on for
-- exactly that case
/-- info: T.mkT : T.nested_Nonempty_1 → T -/
#guard_msgs in
set_option pp.explicit true in
#check @T.mkT

/-- info: T.mkT : T.nested_Nonempty_1 → T -/
#guard_msgs in
set_option pp.all true in
#check @T.mkT

-- anonymous constructor notation reads the expected type instead of being
-- coerced afterwards, so it needs its own detour: without one it reaches past
-- the copy into the block the lowering builds and asks for a `T._shadow`
example : T := T.mkT ⟨T.mk1⟩

example : T := T.mkT (⟨T.mk1⟩ : Nonempty T)

example : T := by
  apply T.mkT
  exact ⟨T.mk1⟩

-- the detour is only for a copy: everything else is Lean's
/--
error: Invalid `⟨...⟩` notation: The expected type `T` has more than one constructor

Note: This notation can only be used when the expected type is an inductive type with a single constructor
-/
#guard_msgs in
example : T := ⟨⟨T.mk1⟩⟩

/-- error: Invalid `⟨...⟩` notation: The expected type of this term could not be determined -/
#guard_msgs in
example := (⟨T.mk1⟩)

-- and it is off with the rest of the library
/--
error: Application type mismatch: The argument
  T.mk1
has type
  T
of sort `Type` but is expected to have type
  T._shadow
of sort `Prop` in the application
  T.nested_Nonempty_1._shadow.intro T.mk1
-/
#guard_msgs in
set_option mumi.enabled false in
example : T := T.mkT ⟨T.mk1⟩

/-! ## Recursion and computation

The rescued type is an ordinary inductive: it pattern-matches, it recurses
structurally, and it runs.
-/

inductive U : Type where
  | leaf : Nat → U
  | node : U → U → U
  | ghost : Nonempty U → U

def U.size : U → Nat
  | .leaf n => n
  | .node a b => a.size + b.size
  | .ghost _ => 0

def U.big : U := .node (.leaf 3) (.node (.leaf 4) (.ghost ⟨.leaf 0⟩))

/-- info: 7 -/
#guard_msgs in
#eval U.size U.big

-- and a value that went through the coercion still reduces in the kernel
example : U.size U.big = 7 := rfl

/-- info: 'U.big' does not depend on any axioms -/
#guard_msgs in
#print axioms U.big

example : U.size (.node (.leaf 1) (.leaf 2)) = 3 := rfl

/-! ## Other `Prop` wrappers

Any inductive `Prop` nests the same way; `Nonempty` is not special.  `Exists`
mentions the member inside a binder's domain rather than as a bare parameter.
-/

inductive V : Type where
  | mk0 : V
  | mkE : (∃ _ : V, True) → V

/-- info: V.mkE : (∃ x, True) → V -/
#guard_msgs in
#check @V.mkE

inductive Box (α : Type) : Prop where
  | intro : α → Box α

inductive W : Type where
  | mk0 : Nat → W
  | mkB : Box W → W

/-- info: W.mkB : Box W → W -/
#guard_msgs in
#check @W.mkB

/-- info: W.nested_Box_1.intro : ∀ (a : W), Box W -/
#guard_msgs in
#check @W.nested_Box_1.intro

/-- info: V.nested_Exists_1.eq_orig : (∃ x, True) = ∃ x, True -/
#guard_msgs in
#check @V.nested_Exists_1.eq_orig

/-- info: W.nested_Box_1.eq_orig : Box W = Box W -/
#guard_msgs in
#check @W.nested_Box_1.eq_orig

-- more than one constructor, so the bridge has to pair them up in order
inductive Two (α : Type) : Prop where
  | l : α → Two α
  | r : Nat → α → Two α

inductive X2 : Type where
  | mk0 : X2
  | mkT : Two X2 → X2

/-- info: X2.nested_Two_1.eq_orig : Two X2 = Two X2 -/
#guard_msgs in
#check @X2.nested_Two_1.eq_orig

example (h : Two X2) : X2 := X2.mkT (X2.nested_Two_1.eq_orig ▸ h)

/-! ## Parameters

A parameter is implicit in a constructor and explicit in the type former, and
rescuing the block has to leave it that way -- it decides whether the
constructor is written `P.ghost h` or `P.ghost α h`.
-/

inductive P (α : Type) : Type where
  | leaf : α → P α
  | ghost : Nonempty (P α) → P α

/-- info: @P.ghost : {α : Type} → Nonempty (P α) → P α -/
#guard_msgs in
#check @P.ghost

/-- info: P.ghost {α : Type} : Nonempty (P α) → P α -/
#guard_msgs in
#check P.ghost

-- the constructor that was not touched keeps the same annotations
/-- info: P.leaf {α : Type} : α → P α -/
#guard_msgs in
#check P.leaf

example (α : Type) (h : Nonempty (P α)) : P α := P.ghost h

/-- info: P.nested_Nonempty_1 : Type → Prop -/
#guard_msgs in
#check @P.nested_Nonempty_1

-- a partially applied copy is shown under its own name: its original's
-- parameters may mention the arguments it has not been given
/-- info: @P.nested_Nonempty_1.intro : ∀ {α : Type} (val : P α), Nonempty (P α) -/
#guard_msgs in
#check @P.nested_Nonempty_1.intro

/-- info: P.nested_Nonempty_1.eq_orig : ∀ (α : Type), Nonempty (P α) = Nonempty (P α) -/
#guard_msgs in
#check @P.nested_Nonempty_1.eq_orig

/-- An instance parameter is an instance parameter on the other side too. -/
inductive PI (α : Type) [Inhabited α] : Type where
  | leaf : α → PI α
  | ghost : Nonempty (PI α) → PI α

/-- info: PI.ghost {α : Type} [Inhabited α] : Nonempty (PI α) → PI α -/
#guard_msgs in
#check PI.ghost

/-! ## Indices

Here the nested application's parameter `Ix n` mentions a constructor field, so
there is no single member it could become.  The field is abstracted and becomes
an index of the auxiliary member.  The kernel refuses this outright, even when
the universes do line up: *nested inductive datatypes parameters cannot contain
local variables*.
-/

inductive Ix : Nat → Type where
  | base : Ix 0
  | step : (n : Nat) → Nonempty (Ix n) → Ix (n + 1)

/-- info: Ix.step : (n : Nat) → Nonempty (Ix n) → Ix (n + 1) -/
#guard_msgs in
#check @Ix.step

/-- info: Ix.nested_Nonempty_1 : Nat → Prop -/
#guard_msgs in
#check @Ix.nested_Nonempty_1

/-- info: Ix.nested_Nonempty_1.intro : ∀ (n : Nat) (val : Ix n), Nonempty (Ix n) -/
#guard_msgs in
#check @Ix.nested_Nonempty_1.intro

-- the generalised index is quantified in the bridge too
/-- info: Ix.nested_Nonempty_1.eq_orig : ∀ (n : Nat), Nonempty (Ix n) = Nonempty (Ix n) -/
#guard_msgs in
#check @Ix.nested_Nonempty_1.eq_orig

example (n : Nat) (h : Nonempty (Ix n)) : Ix (n + 1) :=
  Ix.step n (Ix.nested_Nonempty_1.eq_orig n ▸ h)

-- an indexed copy is passed the index before it is looked up, so `⟨...⟩` finds
-- its original the same way
example : Ix 1 := Ix.step 0 ⟨Ix.base⟩

/-- Two occurrences that differ only in which local they mention share a member. -/
inductive Iy : Nat → Type where
  | base : Iy 0
  | l : (n : Nat) → Nonempty (Iy n) → Iy (n + 1)
  | r : (m : Nat) → Nonempty (Iy m) → Iy (m + 2)

/-- info: Iy.r : (m : Nat) → Nonempty (Iy m) → Iy (m + 2) -/
#guard_msgs in
#check @Iy.r

/-- error: Unknown constant `Iy.nested_Nonempty_2` -/
#guard_msgs in
#check @Iy.nested_Nonempty_2

/-! ## Nesting inside an already-heterogeneous block

Here it is the hand-written `mutual` block that is heterogeneous, and the
nesting is incidental.  `List D5B` is at `D5B`'s own universe, so the auxiliary
member is a data member, with data constructors and a computable recursor.
-/

mutual
inductive D5A : Prop where
  | mk : D5B → D5A
inductive D5B : Type where
  | leaf : Nat → D5B
  | node : List D5B → D5B
  | back : D5A → D5B
end

/-- info: D5A.nested_List_1 : Type -/
#guard_msgs in
#check @D5A.nested_List_1

/-- info: D5A.nested_List_1.cons : D5B → D5A.nested_List_1 → D5A.nested_List_1 -/
#guard_msgs in
#check @D5A.nested_List_1.cons

def D5B.total : D5B → Nat :=
  fun t => D5B.mutualRec (motive_1 := fun _ => True) (motive_2 := fun _ => Nat)
    (motive_3 := fun _ => Nat)
    (fun _ _ => trivial) (fun n => n) (fun _ ih => ih) (fun _ _ => 0)
    0 (fun _ _ h t => h + t) t

/-- info: 7 -/
#guard_msgs in
#eval D5B.total (.node (.cons (.leaf 3) (.cons (.leaf 4) .nil)))

/-! ## Nesting inside nesting -/

inductive N : Type where
  | mk0 : N
  | mkL : Nonempty (List N) → N

/-! The outer copy is a `Prop`, so it is *equal* to what it copies and is
displayed as it: the constructor reads back exactly as it was written, even
though its field's type had to be replaced twice over. -/

/-- info: N.mkL : Nonempty (List N) → N -/
#guard_msgs in
#check @N.mkL

/-! ## A copy that lives in the shadow alone

The `List N` beneath the `Nonempty` is copied too, and the shadow cannot do
without it: the shadow redirects every member occurrence to a member, and
`List N._shadow` is not a thing to write.  But that argument is about the
shadow.  The real world writes the copy only in the `Prop` member's
constructor, which the lowering emits as a *definition*, so there it can be
stated at `List N` itself -- and then the copy need not be declared at all.
Such a member is a *ghost*: present in the shadow, and standing for `List N`
everywhere the writer can see. -/

/-- error: Unknown constant `N.nested_List_2` -/
#guard_msgs in
#check @N.nested_List_2

/-- info: N.nested_Nonempty_1.intro : ∀ (val : List N), Nonempty (List N) -/
#guard_msgs in
#check @N.nested_Nonempty_1.intro

/-! A ghost is still a member, so the block's recursion still crosses it -- with
`List N` as the type it crosses at.  Its own block-wide recursor takes the name
a recursor over a type the kernel denested would have taken, which is free here
precisely because a block with a `Prop` member is one the kernel denested
nothing for. -/

/--
info: @N.mutualRec : {motive_1 : N → Sort u_1} →
  {motive_2 : Nonempty (List N) → Prop} →
    {motive_3 : List N → Sort u_2} →
      motive_1 N.mk0 →
        ((a : Nonempty (List N)) → motive_2 a → motive_1 (N.mkL a)) →
          (∀ (val : List N) (ih_1 : motive_3 val), motive_2 ⋯) →
            motive_3 [] →
              ((head : N) → (tail : List N) → motive_1 head → motive_3 tail → motive_3 (head :: tail)) →
                (t : N) → motive_1 t
-/
#guard_msgs in
#check @N.mutualRec

/--
info: @N.mutualRec_1 : {motive_1 : N → Sort u_1} →
  {motive_2 : Nonempty (List N) → Prop} →
    {motive_3 : List N → Sort u_2} →
      motive_1 N.mk0 →
        ((a : Nonempty (List N)) → motive_2 a → motive_1 (N.mkL a)) →
          (∀ (val : List N) (ih_1 : motive_3 val), motive_2 ⋯) →
            motive_3 [] →
              ((head : N) → (tail : List N) → motive_1 head → motive_3 tail → motive_3 (head :: tail)) →
                (t : List N) → motive_3 t
-/
#guard_msgs in
#check @N.mutualRec_1

/-! The ghost's recursor is built from `List.rec`, so its iota rules hold by
`rfl`, and it computes. -/

def N.count : List N → Nat :=
  N.mutualRec_1 (motive_1 := fun _ => Nat) (motive_2 := fun _ => True)
    (motive_3 := fun _ => Nat)
    0 (fun _ _ => 1) (fun _ _ => trivial) 0 (fun _ _ h t => h + t + 1)

example : N.count [] = 0 := rfl

/-- info: 3 -/
#guard_msgs in
#eval N.count [.mk0, .mkL ⟨[]⟩]

/-- info: 'N.count' does not depend on any axioms -/
#guard_msgs in
#print axioms N.count

/-! ## Where a copy is only isomorphic

A `Prop` copy is *equal* to what it copies, proof irrelevance and all, so it
gets an `eq_orig` and `Mumi.Bridge` displays it as the original. -/

/-- info: N.nested_Nonempty_1.eq_orig : Nonempty (List N) = Nonempty (List N) -/
#guard_msgs in
#check @N.nested_Nonempty_1.eq_orig

/-- info: N.nested_Nonempty_1.coeToOrig : CoeOut (Nonempty (List N)) (Nonempty (List N)) -/
#guard_msgs in
#check @N.nested_Nonempty_1.coeToOrig

/-! A data member is only isomorphic to what it copies: it has constructors of
its own, distinct constants from the original's, and no equation between the
two types is true.  So it gets no `eq_orig` and is displayed as itself, which
is the honest answer.  What it does get is the isomorphism, and a coercion each
way, so its name need not be written at a use site.  `MumiTests.NestedIndInd`
has those: an induction-inductive copy is indexed by a sibling, which is what
keeps it from being a ghost. -/

/-- info: N.nested_Nonempty_1.eq_orig : Nonempty (List N) = Nonempty (List N) -/
#guard_msgs in
#check @N.nested_Nonempty_1.eq_orig

/-! Both sides of that equation print the same, which is the point: with
`mumi.pp.nested` off, the copy shows through. -/

set_option mumi.pp.nested false in
/-- info: N.nested_Nonempty_1.eq_orig : N.nested_Nonempty_1 = Nonempty (List N) -/
#guard_msgs in
#check @N.nested_Nonempty_1.eq_orig

/-! ## How far a denesting reaches

Three deep: `List (Option (List T3))`, `Option (List T3)` and `List T3`.  Every
head in the chain is data, so the kernel denests the lot when the widened block
is handed to it, and the constructor and the recursion are stated in the
writer's own types all the way down. -/

mutual
inductive T3 : Type 1 where
  | tip : T3
  | mk : List (Option (List T3)) → T3
inductive U3 : Type where
  | u : U3
end

/-- info: T3.mk : List (Option (List T3)) → T3 -/
#guard_msgs in
#check @T3.mk

def T3.count : T3 → Nat
  | .tip => 0
  | .mk xs => (xs.filterMap id).length

/-- info: 2 -/
#guard_msgs in
#eval T3.count (T3.mk [some [.tip], none, some []])

/-- info: 'T3.count' does not depend on any axioms -/
#guard_msgs in
#print axioms T3.count

/-! A `Prop` over a `Prop` over data.  The field of the outer copy is at
`Nonempty` -- the very type being recursed on -- without being a recursive
occurrence, so which hypothesis belongs to which field has to be read off the
recursor rather than guessed from a field's head. -/

mutual
inductive V3 : Type 1 where
  | tip : V3
  | mk : Nonempty (Nonempty (List V3)) → V3
inductive W3 : Type where
  | w : W3
end

/-- info: V3.mk : Nonempty (Nonempty (List V3)) → V3 -/
#guard_msgs in
#check @V3.mk

/--
info: V3.nested_Nonempty_1.eq_orig : Nonempty (Nonempty (List V3)) = Nonempty (Nonempty (List V3))
-/
#guard_msgs in
#check @V3.nested_Nonempty_1.eq_orig

/-! Two nestings sharing one denesting.  `List (List C3)` and `List C3` both
appear, and the inner one is what the outer one recurses through, so the two
end up as one denested family rather than two. -/

mutual
inductive C3 : Type 1 where
  | tip : C3
  | one : List C3 → C3
  | two : List (List C3) → C3
inductive D3 : Type where
  | d : D3
end

/-- info: C3.one : List C3 → C3 -/
#guard_msgs in
#check @C3.one

/-- info: C3.two : List (List C3) → C3 -/
#guard_msgs in
#check @C3.two

def C3.deep : C3 → Nat
  | .tip => 0
  | .one xs => xs.length
  | .two xss => (xss.map (·.length)).sum

/-- info: 3 -/
#guard_msgs in
#eval C3.deep (C3.two [[.tip, .tip], [.tip]])

/-- info: 'C3.deep' does not depend on any axioms -/
#guard_msgs in
#print axioms C3.deep

/-! A chain where the inner copy is *indexed*.  Its indices are the copied
type's own, not the block's, so it too can be a ghost, and the recursion the
block gets back crosses `Vek3 B3` at them. -/

inductive Vek3 (α : Type) : Nat → Type where
  | nil : Vek3 α 0
  | cons : (n : Nat) → α → Vek3 α n → Vek3 α (n + 1)

mutual
inductive A3 : Type 1 where
  | tip : A3
  | mk : (n : Nat) → Nonempty (Vek3 B3 n) → A3
inductive B3 : Type where
  | tip : B3
end

/-- info: A3.mk : (n : Nat) → Nonempty (Vek3 B3 n) → A3 -/
#guard_msgs in
#check @A3.mk

/--
info: @A3.mutualRec_1 : {motive_1 : A3 → Sort u_1} →
  {motive_2 : B3 → Sort u_2} →
    {motive_3 : (n : Nat) → Nonempty (Vek3 B3 n) → Prop} →
      {motive_4 : (a : Nat) → Vek3 B3 a → Sort u_3} →
        motive_1 A3.tip →
          ((n : Nat) → (a : Nonempty (Vek3 B3 n)) → motive_3 n a → motive_1 (A3.mk n a)) →
            motive_2 B3.tip →
              (∀ (n : Nat) (val : Vek3 B3 n) (ih_2 : motive_4 n val), motive_3 n ⋯) →
                motive_4 0 Vek3.nil →
                  ((n : Nat) →
                      (a : B3) →
                        (a_1 : Vek3 B3 n) → motive_2 a → motive_4 n a_1 → motive_4 (n + 1) (Vek3.cons n a a_1)) →
                    {a : Nat} → (t : Vek3 B3 a) → motive_4 a t
-/
#guard_msgs in
#check @A3.mutualRec_1

/-- info: A3.nested_Nonempty_1.intro : ∀ (n : Nat) (val : Vek3 B3 n), Nonempty (Vek3 B3 n) -/
#guard_msgs in
#check @A3.nested_Nonempty_1.intro

/--
info: A3.nested_Nonempty_1.eq_orig : ∀ (n : Nat), Nonempty (Vek3 B3 n) = Nonempty (Vek3 B3 n)
-/
#guard_msgs in
#check @A3.nested_Nonempty_1.eq_orig

/-! ## Nesting over a mutual family

Nesting `FamRose` drags in `FamForest` too, since that is where `FamRose`'s own
recursion goes.  The two reach each other -- `node` has a field at the forest,
`cons` one at the tree -- so the denesting has to take them together, and the
recursion the block gets back ranges over the whole family at once. -/

mutual
inductive FamRose (α : Type u) : Type u where
  | node : α → FamForest α → FamRose α
inductive FamForest (α : Type u) : Type u where
  | nil : FamForest α
  | cons : FamRose α → FamForest α → FamForest α
end

mutual
def FamRose.size {α} : FamRose α → Nat
  | .node _ f => 1 + FamForest.size f
def FamForest.size {α} : FamForest α → Nat
  | .nil => 0
  | .cons r f => FamRose.size r + FamForest.size f
end

mutual
inductive Mu1A : Type 1 where
  | tip : Mu1A
  | mk : FamRose Mu1A → Mu1A
inductive Mu1B : Type where
  | b : Mu1B
end

/-- info: Mu1A.mk : FamRose Mu1A → Mu1A -/
#guard_msgs in
#check @Mu1A.mk

/-! The recursor is the whole family's: a motive for the block's own member and
one for each member of the family it nests, with the tree's cases and the
forest's side by side. -/

/--
info: @Mu1A.rec : {motive_1 : Mu1A → Sort u_1} →
  {motive_2 : FamRose Mu1A → Sort u_1} →
    {motive_3 : FamForest Mu1A → Sort u_1} →
      motive_1 Mu1A.tip →
        ((a : FamRose Mu1A) → motive_2 a → motive_1 (Mu1A.mk a)) →
          ((a : Mu1A) → (a_1 : FamForest Mu1A) → motive_1 a → motive_3 a_1 → motive_2 (FamRose.node a a_1)) →
            motive_3 FamForest.nil →
              ((a : FamRose Mu1A) →
                  (a_1 : FamForest Mu1A) → motive_2 a → motive_3 a_1 → motive_3 (FamForest.cons a a_1)) →
                (t : Mu1A) → motive_1 t
-/
#guard_msgs in
#check @Mu1A.rec

/-! A function written against the family runs on what comes out of the
constructor, with nothing to convert on the way in or out. -/

def Mu1A.count : Mu1A → Nat
  | .tip => 0
  | .mk r => FamRose.size r

/-- info: 3 -/
#guard_msgs in
#eval Mu1A.count (Mu1A.mk
  (.node .tip (.cons (.node .tip .nil) (.cons (.node .tip .nil) .nil))))

/-- info: 'Mu1A.count' does not depend on any axioms -/
#guard_msgs in
#print axioms Mu1A.count

/-! A family of propositions is *equal* to its copies rather than merely
isomorphic, so the constructor reads back as it was written -- both members at
once, since the equalities are proved together. -/

mutual
inductive FamPA (α : Type u) : Prop where
  | mk : α → FamPB α → FamPA α
inductive FamPB (α : Type u) : Prop where
  | nil : FamPB α
  | cons : FamPA α → FamPB α → FamPB α
end

mutual
inductive Mu2A : Type 1 where
  | tip : Mu2A
  | mk : FamPA Mu2A → Mu2A
inductive Mu2B : Type where
  | b : Mu2B
end

/-- info: Mu2A.mk : FamPA Mu2A → Mu2A -/
#guard_msgs in
#check @Mu2A.mk

/-- info: Mu2A.nested_FamPB_2.eq_orig : FamPB Mu2A = FamPB Mu2A -/
#guard_msgs in
#check @Mu2A.nested_FamPB_2.eq_orig

example (h : FamPA Mu2A) : Mu2A := Mu2A.mk h
example : Mu2A := Mu2A.mk (.mk .tip .nil)

/-! Three members work the same way; nothing about the group is a pair. -/

mutual
inductive FamT1 (α : Type u) : Type u where
  | a : α → FamT2 α → FamT1 α
inductive FamT2 (α : Type u) : Type u where
  | b : FamT3 α → FamT2 α
  | b0 : FamT2 α
inductive FamT3 (α : Type u) : Type u where
  | c : FamT1 α → FamT3 α
  | c0 : FamT3 α
end

mutual
inductive Mu3A : Type 1 where
  | tip : Mu3A
  | mk : FamT1 Mu3A → Mu3A
inductive Mu3B : Type where
  | b : Mu3B
end

/-- info: Mu3A.mk : FamT1 Mu3A → Mu3A -/
#guard_msgs in
#check @Mu3A.mk

/-! Being written in one `mutual` block is not what makes a cycle.  `FamS2` does
not reach back into `FamS1`, so the two are denested one after the other rather
than together. -/

mutual
inductive FamS1 (α : Type u) : Type u where
  | s : α → FamS2 α → FamS1 α
inductive FamS2 (α : Type u) : Type u where
  | t : FamS2 α
end

mutual
inductive Mu4A : Type 1 where
  | tip : Mu4A
  | mk : FamS1 Mu4A → Mu4A
inductive Mu4B : Type where
  | b : Mu4B
end

/-- info: Mu4A.mk : FamS1 Mu4A → Mu4A -/
#guard_msgs in
#check @Mu4A.mk

/--
info: @Mu4A.rec : {motive_1 : Mu4A → Sort u_1} →
  {motive_2 : FamS1 Mu4A → Sort u_1} →
    {motive_3 : FamS2 Mu4A → Sort u_1} →
      motive_1 Mu4A.tip →
        ((a : FamS1 Mu4A) → motive_2 a → motive_1 (Mu4A.mk a)) →
          ((a : Mu4A) → (a_1 : FamS2 Mu4A) → motive_1 a → motive_3 a_1 → motive_2 (FamS1.s a a_1)) →
            motive_3 FamS2.t → (t : Mu4A) → motive_1 t
-/
#guard_msgs in
#check @Mu4A.rec

/-! The family may be indexed, and the denesting carries the indices. -/

mutual
inductive FamIA (α : Type u) : Nat → Type u where
  | z : α → FamIA α 0
  | s : (n : Nat) → FamIB α n → FamIA α (n + 1)
inductive FamIB (α : Type u) : Nat → Type u where
  | mk : (n : Nat) → FamIA α n → FamIB α n
end

mutual
inductive Mu5A : Type 1 where
  | tip : Mu5A
  | mk : FamIA Mu5A 3 → Mu5A
inductive Mu5B : Type where
  | b : Mu5B
end

/-- info: Mu5A.mk : FamIA Mu5A 3 → Mu5A -/
#guard_msgs in
#check @Mu5A.mk

/--
info: @Mu5A.rec : {motive_1 : Mu5A → Sort u_1} →
  {motive_2 : (a : Nat) → FamIA Mu5A a → Sort u_1} →
    {motive_3 : (a : Nat) → FamIB Mu5A a → Sort u_1} →
      motive_1 Mu5A.tip →
        ((a : FamIA Mu5A 3) → motive_2 3 a → motive_1 (Mu5A.mk a)) →
          ((a : Mu5A) → motive_1 a → motive_2 0 (FamIA.z a)) →
            ((n : Nat) → (a : FamIB Mu5A n) → motive_3 n a → motive_2 (n + 1) (FamIA.s n a)) →
              ((n : Nat) → (a : FamIA Mu5A n) → motive_2 n a → motive_3 n (FamIB.mk n a)) → (t : Mu5A) → motive_1 t
-/
#guard_msgs in
#check @Mu5A.rec

/-! One family at two different parameters is two denestings, not one: what
they share is the whole nested application, not just its head. -/

mutual
inductive Mu6A : Type 1 where
  | tip : Mu6A
  | one : FamRose Mu6A → Mu6A
  | two : FamRose (List Mu6A) → Mu6A
inductive Mu6B : Type where
  | b : Mu6B
end

/-- info: Mu6A.one : FamRose Mu6A → Mu6A -/
#guard_msgs in
#check @Mu6A.one

/-- info: Mu6A.two : FamRose (List Mu6A) → Mu6A -/
#guard_msgs in
#check @Mu6A.two

def Mu6A.count : Mu6A → Nat
  | .tip => 0
  | .one r => FamRose.size r
  | .two r => FamRose.size r

/-- info: 2 -/
#guard_msgs in
#eval Mu6A.count (Mu6A.two (.node [.tip] (.cons (.node [] .nil) .nil)))

/-- info: 'Mu6A.count' does not depend on any axioms -/
#guard_msgs in
#print axioms Mu6A.count

/-! The parameter may be the family's own other member, which makes two
denestings of two members each, the outer one over the types the inner one
introduced. -/

mutual
inductive Mu7A : Type 1 where
  | tip : Mu7A
  | mk : FamRose (FamForest Mu7A) → Mu7A
inductive Mu7B : Type where
  | b : Mu7B
end

/-- info: Mu7A.mk : FamRose (FamForest Mu7A) → Mu7A -/
#guard_msgs in
#check @Mu7A.mk

/-! ## Nesting inside a bundle

`Prod`, `Sigma` and `Subtype` carry their second component as a *parameter* that
is a function, so fixing that parameter leaves the copy's own fields as redexes:
`Sigma`'s `snd` arrives as `(fun n => BunVek Bn1 n) fst`, whose head is a lambda
and not an inductive at all.  What a field is, is its beta-normal form, and the
nesting is only there to be seen once it is reduced.  Reducing also exposes a
second nesting under the first, at an index the enclosing constructor supplies.
-/

inductive BunTree (α : Type u) : Type u where
  | leaf : α → BunTree α
  | node : BunTree α → BunTree α → BunTree α

def BunTree.size {α} : BunTree α → Nat
  | .leaf _ => 1
  | .node a b => BunTree.size a + BunTree.size b

inductive BunVek (α : Type u) : Nat → Type u where
  | nil : BunVek α 0
  | cons : α → BunVek α n → BunVek α (n + 1)

mutual
inductive Bn1 : Type 1 where
  | tip : Bn1
  | pr : BunTree Bn1 × Nat → Bn1
  | sg : (Sigma fun (n : Nat) => BunVek Bn1 n) → Bn1
  | sub : { _t : BunTree Bn1 // 0 = 0 } → Bn1
  | fn : (Nat → BunTree Bn1) → Bn1
inductive Bn2 : Type where
  | b : Bn2
end

/-- info: Bn1.pr : BunTree Bn1 × Nat → Bn1 -/
#guard_msgs in
#check @Bn1.pr

/-- info: Bn1.sg : (n : Nat) × BunVek Bn1 n → Bn1 -/
#guard_msgs in
#check @Bn1.sg

/-! The `BunVek` under the `Sigma` is a nesting of its own, indexed by the `Nat`
the `Sigma` supplies, and it is denested along with the bundle that reaches it. -/

/-- info: Bn1.sub : { _t // 0 = 0 } → Bn1 -/
#guard_msgs in
#check @Bn1.sub

/-! A nesting in the codomain of a function is found under the binder. -/

/-- info: Bn1.fn : (Nat → BunTree Bn1) → Bn1 -/
#guard_msgs in
#check @Bn1.fn

def Bn1.weigh : Bn1 → Nat
  | .tip => 0
  | .pr p => BunTree.size p.1
  | .sg _ => 0
  | .sub _ => 0
  | .fn _ => 0

/-- info: 2 -/
#guard_msgs in
#eval Bn1.weigh (.pr (BunTree.node (.leaf .tip) (.leaf .tip), 5))

/-- info: 'Bn1.weigh' does not depend on any axioms -/
#guard_msgs in
#print axioms Bn1.weigh

/-! ## Nesting over a type that is itself nested

`RL` is defined through `List (RL α)`, so writing `RL Z` in the block copies
`List (RL Z)` as well.  The two copies reach each other and neither is a member
of the other's family, so nothing about being one `mutual` block decides which
recursor settles which: `RL.rec` has a motive at `List (RL α)` as well as at
`RL α` -- Lean's own denesting put it there -- while `List.rec` has only the one.
Which copies a pass settles is therefore read off the recursor, by matching each
motive to the application it quantifies over.  `List`'s copy, which its own
recursor cannot reach past, crosses the shortfall on `RL`'s copy's way back, and
so the two go in one after the other rather than together. -/

inductive RL (α : Type u) : Type u where
  | mk : α → List (RL α) → RL α

def RL.size {α} : RL α → Nat
  | .mk _ l => 1 + go l
where go : List (RL α) → Nat
  | [] => 0
  | r :: rs => r.size + go rs

mutual
inductive Nn1 : Type 1 where
  | tip : Nn1
  | mk : RL Nn1 → Nn1
inductive Nn2 : Type where
  | b : Nn2
end

/-- info: Nn1.mk : RL Nn1 → Nn1
-/
#guard_msgs in
#check @Nn1.mk

/-! The recursor is the one Lean would have given the block had the universes
allowed it: a motive for the member, one for `RL` and one for the `List` it
recurses through, and the `List` cases printed in list notation because that is
what they are. -/

/--
info: @Nn1.rec : {motive_1 : Nn1 → Sort u_1} →
  {motive_2 : RL Nn1 → Sort u_1} →
    {motive_3 : List (RL Nn1) → Sort u_1} →
      motive_1 Nn1.tip →
        ((a : RL Nn1) → motive_2 a → motive_1 (Nn1.mk a)) →
          ((a : Nn1) → (a_1 : List (RL Nn1)) → motive_1 a → motive_3 a_1 → motive_2 (RL.mk a a_1)) →
            motive_3 [] →
              ((head : RL Nn1) → (tail : List (RL Nn1)) → motive_2 head → motive_3 tail → motive_3 (head :: tail)) →
                (t : Nn1) → motive_1 t
-/
#guard_msgs in
#check @Nn1.rec

/-! A value written with the original's constructors goes in and comes back out
through a function that only ever sees the original. -/

def Nn1.count : Nn1 → Nat
  | .tip => 0
  | .mk r => RL.size r

/-- info: 3 -/
#guard_msgs in
#eval Nn1.count (Nn1.mk (.mk .tip [.mk .tip [], .mk .tip []]))

/-- info: 'Nn1.count' does not depend on any axioms -/
#guard_msgs in
#print axioms Nn1.count

/-! Nesting twice over brings in three types at once -- `LL`, and a `List` at
each depth -- and they go in in the order their definitions need. -/

inductive LL (α : Type u) : Type u where
  | mk : α → List (List (LL α)) → LL α

mutual
inductive Nn3 : Type 1 where
  | tip : Nn3
  | mk : LL Nn3 → Nn3
inductive Nn4 : Type where
  | b : Nn4
end

/-- info: Nn3.mk : LL Nn3 → Nn3 -/
#guard_msgs in
#check @Nn3.mk

/-- info: @LL.mk : {α : Type u_1} → α → List (List (LL α)) → LL α -/
#guard_msgs in
#check @LL.mk

def LL.size {α} : LL α → Nat
  | .mk _ l => 1 + outer l
where
  outer : List (List (LL α)) → Nat
    | [] => 0
    | l :: ls => inner l + outer ls
  inner : List (LL α) → Nat
    | [] => 0
    | r :: rs => r.size + inner rs

def Nn3.count : Nn3 → Nat
  | .tip => 0
  | .mk r => LL.size r

/-- info: 3 -/
#guard_msgs in
#eval Nn3.count (Nn3.mk (.mk .tip [[.mk .tip [], .mk .tip []]]))

/-- info: 'Nn3.count' does not depend on any axioms -/
#guard_msgs in
#print axioms Nn3.count

/-! The type nested through may be a family of its own, and the recursor that
reaches furthest is then the one whose family it is. -/

mutual
inductive MA (α : Type u) : Type u where
  | a : α → List (MB α) → MA α
inductive MB (α : Type u) : Type u where
  | b : MA α → MB α
  | b0 : MB α
end

mutual
inductive Nn5 : Type 1 where
  | tip : Nn5
  | mk : MA Nn5 → Nn5
inductive Nn6 : Type where
  | b : Nn6
end

/-- info: Nn5.mk : MA Nn5 → Nn5 -/
#guard_msgs in
#check @Nn5.mk

mutual
def MA.size {α} : MA α → Nat
  | .a _ l => 1 + MA.sizes l
def MA.sizes {α} : List (MB α) → Nat
  | [] => 0
  | m :: ms => MB.size m + MA.sizes ms
def MB.size {α} : MB α → Nat
  | .b a => MA.size a
  | .b0 => 1
end

def Nn5.count : Nn5 → Nat
  | .tip => 0
  | .mk a => MA.size a

/-- info: 3 -/
#guard_msgs in
#eval Nn5.count (Nn5.mk (.a .tip [.b (.a .tip []), .b0]))

/-- info: 'Nn5.count' does not depend on any axioms -/
#guard_msgs in
#print axioms Nn5.count


/-! ## The same head twice over

`Xrose (Xrose Z)` is two nestings, not one: the outer `Xrose` and the inner one
are different applications and get different motives, and each drags in the
`List` it recurses through.  Four types are denested, in two groups -- outer
with its list, inner with its -- and the outer group is built over the inner. -/

inductive Xrose (α : Type u) : Type u where
  | node : α → List (Xrose α) → Xrose α

def Xrose.size {α} (f : α → Nat) : Xrose α → Nat
  | .node a l => f a + go l
where go : List (Xrose α) → Nat
  | [] => 0
  | r :: rs => r.size f + go rs

mutual
inductive Xn1 : Type 1 where
  | tip : Xn1
  | mk : Xrose (Xrose Xn1) → Xn1
inductive Xn2 : Type where
  | b : Xn2
end

/-- info: Xn1.mk : Xrose (Xrose Xn1) → Xn1 -/
#guard_msgs in
#check @Xn1.mk

def Xn1.count : Xn1 → Nat
  | .tip => 1
  | .mk r => Xrose.size (Xrose.size (fun _ => 1)) r

/-- info: 3 -/
#guard_msgs in
#eval Xn1.count (Xn1.mk
  (.node (.node .tip [.node .tip []]) [.node (.node .tip []) []]))

/-- info: 'Xn1.count' does not depend on any axioms -/
#guard_msgs in
#print axioms Xn1.count

/-! ## Nesting in less usual company

A section variable is a parameter of the block, and so of everything the
nesting brings in with it. -/

section
variable (σ : Type)

mutual
inductive Xv1 : Type 1 where
  | tip : σ → Xv1
  | mk : Xrose Xv1 → Xv1
inductive Xv2 : Type where
  | b : Xv2
end

end

/-- info: @Xv1.mk : {σ : Type} → Xrose (Xv1 σ) → Xv1 σ -/
#guard_msgs in
#check @Xv1.mk

/--
info: @Xv1.rec : {σ : Type} →
  {motive_1 : Xv1 σ → Sort u_1} →
    {motive_2 : Xrose (Xv1 σ) → Sort u_1} →
      {motive_3 : List (Xrose (Xv1 σ)) → Sort u_1} →
        ((a : σ) → motive_1 (Xv1.tip a)) →
          ((a : Xrose (Xv1 σ)) → motive_2 a → motive_1 (Xv1.mk a)) →
            ((a : Xv1 σ) → (a_1 : List (Xrose (Xv1 σ))) → motive_1 a → motive_3 a_1 → motive_2 (Xrose.node a a_1)) →
              motive_3 [] →
                ((head : Xrose (Xv1 σ)) →
                    (tail : List (Xrose (Xv1 σ))) → motive_2 head → motive_3 tail → motive_3 (head :: tail)) →
                  (t : Xv1 σ) → motive_1 t
-/
#guard_msgs in
#check @Xv1.rec

/-! A wrapper polymorphic in `Sort` can be nested at a data member and at a
proposition about it in the one block, and the two are told apart by the whole
application rather than by the head. -/

inductive Xbox (α : Sort u) : Sort (max 1 u) where
  | mk : α → Xbox α

mutual
inductive Xs1 : Type 1 where
  | tip : Xs1
  | d : Xbox Xs1 → Xs1
  | p : Xbox (Nonempty Xs1) → Xs1
inductive Xs2 : Type where
  | b : Xs2
end

/-- info: Xs1.nested_Xbox_1.toOrig : Xs1.nested_Xbox_1 → Xbox Xs1 -/
#guard_msgs in
#check @Xs1.nested_Xbox_1.toOrig

/-- info: Xs1.nested_Xbox_2.toOrig : Xs1.nested_Xbox_2 → Xbox (Nonempty Xs1) -/
#guard_msgs in
#check @Xs1.nested_Xbox_2.toOrig

/-! `PProd` and `PSum` carry their components in `Sort`, so nesting through them
lands the copy wherever the block's member is. -/

mutual
inductive Xp1 : Type 1 where
  | tip : Xp1
  | p : PProd Xp1 Nat → Xp1
  | s : PSum Xp1 Nat → Xp1
inductive Xp2 : Type where
  | b : Xp2
end

/-- info: Xp1.p : Xp1 ×' Nat → Xp1 -/
#guard_msgs in
#check @Xp1.p

/-- info: Xp1.s : Xp1 ⊕' Nat → Xp1 -/
#guard_msgs in
#check @Xp1.s

def Xp1.count : Xp1 → Nat
  | .tip => 0
  | .p q => q.2
  | .s q => match q with | .inl _ => 1 | .inr n => n

/-- info: 7 -/
#guard_msgs in
#eval Xp1.count (Xp1.p ⟨.tip, 7⟩)

/-- info: 'Xp1.count' does not depend on any axioms -/
#guard_msgs in
#print axioms Xp1.count

/-! Three universes are no different from two, and `deriving` still runs on the
block that comes out. -/

mutual
inductive Xu1 : Type 2 where
  | tip : Xu1
  | mk : Xrose Xu1 → Xu1
  deriving Inhabited
inductive Xu2 : Type 1 where
  | b : Xu2
inductive Xu3 : Type where
  | c : Xu3
end

/-- info: Xu1.mk : Xrose Xu1 → Xu1 -/
#guard_msgs in
#check @Xu1.mk

/-- info: inferInstance : Inhabited Xu1 -/
#guard_msgs in
#check (inferInstance : Inhabited Xu1)


/-! ## Nesting over a type this elaborator lowered

A member of a block `lower` took over is a reducible alias for a shadow
inductive, so the type the writer names is not itself what the denester finds.
It sees through the alias -- it has to, since the shadow is where the
constructors are -- but the copy is still named after, and identified with, what
was written.  Stacking a block on a block therefore reads no differently from
stacking one on an ordinary type. -/

inductive SList (α : Sort u) : Sort (max 1 u) where
  | nil : SList α
  | cons : α → SList α → SList α

/-- `Sp` is itself a rescued nesting: `SList (Sp α)` is data and `Sp α` is a
proposition, so the block the kernel would have built is heterogeneous. -/
inductive Sp (α : Type u) : Prop where
  | nil : Sp α
  | mk : α → SList (Sp α) → Sp α

mutual
inductive St1 : Type 1 where
  | tip : St1
  | mk : Sp St1 → St1
inductive St2 : Type where
  | b : St2
end

/-- info: St1.mk : Sp St1 → St1 -/
#guard_msgs in
#check @St1.mk

/-- info: St1.nested_Sp_1.eq_orig : Sp St1 = Sp St1 -/
#guard_msgs in
#check @St1.nested_Sp_1.eq_orig

example (h : Sp St1) : St1 := St1.mk h
example : St1 := St1.mk (Sp.nil : Sp St1)

/-! A data member of a lowered block is only isomorphic to its copy, as any data
type is, but it is the member's own name the copy is isomorphic *to*. -/

mutual
inductive Wrap (α : Type u) : Type u where
  | mk : α → WrapP α → Wrap α
inductive WrapP (α : Type u) : Prop where
  | p : WrapP α
end

mutual
inductive St3 : Type 1 where
  | tip : St3
  | mk : Wrap St3 → St3
inductive St4 : Type where
  | b : St4
end

/-- info: St3.nested_Wrap_1.toOrig : St3.nested_Wrap_1 → Wrap St3 -/
#guard_msgs in
#check @St3.nested_Wrap_1.toOrig

def St3.count : St3 → Nat
  | .tip => 0
  | .mk w => match (w : Wrap St3) with | .mk _ _ => 1

/-- info: 1 -/
#guard_msgs in
#eval St3.count (St3.mk (St3.nested_Wrap_1.ofOrig (.mk .tip .p)))

/-- info: 'St3.count' does not depend on any axioms -/
#guard_msgs in
#print axioms St3.count


/-! ## The rest of the shapes a nesting comes in

Nothing below is a special case in the elaborator; the point of pinning them is
that they are the shapes people write, and a change that breaks one of them
should say so here rather than downstream.

Several nestings in one member, at different heads, are several denestings,
each stated at what was written. -/

mutual
inductive Wa1 : Type 1 where
  | tip : Wa1
  | a : Option Wa1 → Wa1
  | b : Except Nat Wa1 → Wa1
  | c : Wa1 ⊕ Nat → Wa1
inductive Wa2 : Type where
  | y : Wa2
end

/-- info: Wa1.a : Option Wa1 → Wa1 -/
#guard_msgs in
#check @Wa1.a

/-- info: Wa1.b : Except Nat Wa1 → Wa1 -/
#guard_msgs in
#check @Wa1.b

/-- info: Wa1.c : Wa1 ⊕ Nat → Wa1 -/
#guard_msgs in
#check @Wa1.c

/-! A structure is an inductive, and one of its fields being a proposition
changes nothing. -/

structure WHolder (α : Type 1) where
  val : α
  ok  : True

mutual
inductive Wb1 : Type 1 where
  | tip : Wb1
  | mk : WHolder Wb1 → Wb1
inductive Wb2 : Type where
  | y : Wb2
end

/-- info: Wb1.mk : WHolder Wb1 → Wb1 -/
#guard_msgs in
#check @Wb1.mk

/-- info: 'Wb1' does not depend on any axioms -/
#guard_msgs in
#print axioms Wb1

/-! `Thunk` holds its contents behind a function, so the nesting is under a
binder rather than at the head of the field. -/

mutual
inductive Wc1 : Type 1 where
  | tip : Wc1
  | mk : Thunk Wc1 → Wc1
inductive Wc2 : Type where
  | y : Wc2
end

/-- info: Wc1.mk : Thunk Wc1 → Wc1 -/
#guard_msgs in
#check @Wc1.mk

/-! Every member of a block may nest, at three universes, and each member's
nesting is denested at that member. -/

mutual
inductive Wd1 : Type 2 where
  | tip : Wd1
  | mk : List Wd1 → Wd1
inductive Wd2 : Type 1 where
  | tip : Wd2
  | mk : List Wd2 → Wd2
inductive Wd3 : Type where
  | tip : Wd3
  | mk : List Wd3 → Wd3
end

/-- info: Wd1.mk : List Wd1 → Wd1 -/
#guard_msgs in
#check @Wd1.mk

/-- info: Wd3.mk : List Wd3 → Wd3 -/
#guard_msgs in
#check @Wd3.mk

/-! A nesting may be at a fixed index of an indexed type, and the constructor
names the value that was written. -/

inductive WVek (α : Type 1) : Nat → Type 1 where
  | nil : WVek α 0
  | cons : α → WVek α n → WVek α (n + 1)

mutual
inductive We1 : Type 1 where
  | tip : We1
  | mk : WVek We1 2 → We1
inductive We2 : Type where
  | y : We2
end

/-- info: We1.mk : WVek We1 2 → We1 -/
#guard_msgs in
#check @We1.mk

/-! The member need not be in a *parameter* of the nesting type.  `WIdx` takes
its argument as an index, and it is denested at it all the same. -/

inductive WIdx : Type 1 → Type 1 where
  | mk : {β : Type 1} → β → WIdx β

mutual
inductive Wf1 : Type 1 where
  | tip : Wf1
  | mk : WIdx Wf1 → Wf1
inductive Wf2 : Type where
  | y : Wf2
end

/-- info: Wf1.mk : WIdx Wf1 → Wf1 -/
#guard_msgs in
#check @Wf1.mk

/-! A block with a universe parameter of its own may nest over `ULift`, so long
as the level is written: `ULift`'s own first level is not fixed by its argument,
and a nesting whose type still has a universe metavariable in it is refused by
Lean before this elaborator is reached. -/

universe u

mutual
inductive Wg1 : Type (u + 1) where
  | tip : Wg1
  | mk : ULift.{u + 1} Wg1 → Wg1
inductive Wg2 : Type u where
  | y : Wg2
end

/-- info: Wg1.mk : ULift Wg1 → Wg1 -/
#guard_msgs in
#check @Wg1.mk

/-! ## Where there is no bridge at all

A bridge needs every field of the copy to be one the original also takes, to be
recursive in the member being bridged, or to be a copy with a bridge of its own.
A field that mentions a copy anywhere else -- in the domain of one of its own
binders, or in a nested position -- has nothing to be handed over as. -/

/-- error: Unknown constant `D5A.nested_List_1.eq_orig` -/
#guard_msgs in
#check @D5A.nested_List_1.eq_orig

/-- info: 1 -/
#guard_msgs in
#eval (D5A.nested_List_1.cons (.leaf 3) .nil : List D5B).length

/-! A nesting is copied by specialising it to the block, and what it is
specialised at has to be fixed before the constructors are known.  A parameter
that mentions a field of the constructor is still fine -- the field becomes an
index of the copy -- and it stays fine when the field's own type mentions the
block, which only says the copy is indexed by a member.  An equation between two
members is that case: the denested block is induction-inductive, so the erasure
that route already runs takes the copy along with everything else. -/

mutual
inductive EqZ : Type 1 where
  | tip : EqZ
  | mk : (a : EqZ) → (b : EqZ) → a = b → EqZ
inductive EqY : Type where
  | y : EqY
end

/-- info: EqZ.mk : (a b : EqZ) → a = b → EqZ -/
#guard_msgs in
#check @EqZ.mk

-- the copy of `Eq` is a proposition, so it is erased and never reaches a motive
/--
info: @EqZ.rec : {motive_1 : EqZ → Sort u_1} →
  {motive_2 : EqY → Sort u_1} →
    motive_1 EqZ.tip →
      ((a b : EqZ) → (a_1 : a = b) → motive_1 a → motive_1 b → motive_1 (a.mk b a_1)) →
        motive_2 EqY.y → (t : EqZ) → motive_1 t
-/
#guard_msgs in
#check @EqZ.rec

/-- info: 'EqZ.rec' does not depend on any axioms -/
#guard_msgs in
#print axioms EqZ.rec

/-! One shape has no copy to bridge in the first place: a head that is not an
inductive at all.  `Quot` is a primitive,
so there are no constructors to copy and nothing to specialise; this one is out
and stays out. -/

/--
error: Unsupported constructor field in a multiuniverse block: field 1 of `QuZ.mk` mentions a member of the block in a nested position, in the type
  Quot fun x x_1 => True

Note: The head of the occurrence is not an inductive type, so there is nothing to denest and nothing to copy
-/
#guard_msgs in
mutual
inductive QuZ : Type 1 where
  | tip : QuZ
  | mk : Quot (fun (_ _ : QuZ) => True) → QuZ
inductive QuY : Type where
  | y : QuY
end

/-! ## A nesting parameter that mentions a constructor's own field

The kernel's denesting refuses one of these outright -- *nested inductive
datatypes parameters cannot contain local variables* -- however homogeneous the
block would have been.  `Mumi.Denest` handles it by making the local an *index*
of the copy, so a retry takes such a block even though it comes out homogeneous:
being homogeneous is only evidence that Lean could have done it when the
denesting is one Lean could have done.

Both retries recognise the shape, and the induction-inductive one is offered it
first, because it can state the block back over the type that was copied.  For a
*data* copy that is what it buys: `Mumi.Lowering` relates a data copy to its
original by an isomorphism, which is the most two distinct data types can be,
and so leaves the copy's own name in the signature; this route puts `List`
itself there.  The price is the one that route always charges: the constructors
are `def`s, so `match` and `cases` do not work, and one recursor serves the
whole block.

`n` below is bound by `LocA.mk`, and `List`'s parameter mentions it. -/

inductive LocWrap (α : Type) (n : Nat) : Type where
  | mk (a : α) : LocWrap α n

inductive LocA : Type where
  | tip
  | mk (n : Nat) (v : List (LocWrap LocA n))

/-- info: LocA.mk : (n : Nat) → List (LocWrap LocA n) → LocA -/
#guard_msgs in
#check @LocA.mk

/-! The copies are what the block is really built from, and they stay declared;
nothing the writer sees mentions them. -/

/-- info: LocA.nested_List_1 (n : Nat) : Type -/
#guard_msgs in
#check LocA.nested_List_1

/-- info: LocA.nested_LocWrap_2 (n : Nat) : Type -/
#guard_msgs in
#check LocA.nested_LocWrap_2

/-- info: @LocA.nested_List_1.ofOrig : {n : Nat} → List (LocWrap LocA n) → LocA.nested_List_1 n -/
#guard_msgs in
#check @LocA.nested_List_1.ofOrig

/-- info: @LocA.nested_List_1.toOrig : {n : Nat} → LocA.nested_List_1 n → List (LocWrap LocA n) -/
#guard_msgs in
#check @LocA.nested_List_1.toOrig

/-- info: @LocA.nested_LocWrap_2.ofOrig : {n : Nat} → LocWrap LocA n → LocA.nested_LocWrap_2 n -/
#guard_msgs in
#check @LocA.nested_LocWrap_2.ofOrig

/-! The generalised local is a leading index of each motive that needs one, and
the minor premises are stated at `List`'s own constructors. -/

/--
info: @LocA.rec : {motive_1 : LocA → Sort u_1} →
  {motive_2 : (n : Nat) → List (LocWrap LocA n) → Sort u_1} →
    {motive_3 : (n : Nat) → LocWrap LocA n → Sort u_1} →
      motive_1 LocA.tip →
        ((n : Nat) → (v : List (LocWrap LocA n)) → motive_2 n v → motive_1 (LocA.mk n v)) →
          ((n : Nat) → motive_2 n []) →
            ((n : Nat) →
                (head : LocWrap LocA n) →
                  (tail : List (LocWrap LocA n)) → motive_3 n head → motive_2 n tail → motive_2 n (head :: tail)) →
              ((n : Nat) → (a : LocA) → motive_1 a → motive_3 n (LocWrap.mk a)) → (t : LocA) → motive_1 t
-/
#guard_msgs in
#check @LocA.rec

/-! So a value is written with list syntax, and the recursion computes. -/

def locSize : LocA → Nat :=
  LocA.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    (motive_3 := fun _ _ => Nat)
    1 (fun _ _ ih => ih + 1) (fun _ => 0) (fun _ _ _ hd tl => hd + tl) (fun _ _ ih => ih)

example : locSize .tip = 1 := rfl
example : locSize (.mk 3 [.mk .tip]) = 2 := rfl

/-- info: 3 -/
#guard_msgs in
#eval locSize (.mk 3 [.mk .tip, .mk .tip])

/-- info: 'locSize' does not depend on any axioms -/
#guard_msgs in
#print axioms locSize

/-! `LocA.mk` is a `def`, so `cases` would reach past it for the underlying
subtype's own `casesOn`, which has a single alternative.  It does not, because
the block leaves behind an eliminator with the copies' motives discharged --
which for a case split costs nothing, since it uses no hypothesis at any of
them.  What survives is stated at `List (LocWrap LocA n)`, the type that was
written, and not at the copy the block was built from. -/

/--
info: @LocA.casesD : {motive : LocA → Sort u_1} →
  motive LocA.tip → ((n : Nat) → (v : List (LocWrap LocA n)) → motive (LocA.mk n v)) → (t : LocA) → motive t
-/
#guard_msgs in
#check @LocA.casesD

example (r : LocA) : True := by
  cases r with
  | tip => trivial
  | mk n v => trivial

def locTag (r : LocA) : Nat :=
  LocA.casesD (motive := fun _ => Nat) 0 (fun n _ => n) r

example : locTag (.mk 3 [.mk .tip]) = 3 := rfl

/-- info: 'locTag' does not depend on any axioms -/
#guard_msgs in
#print axioms locTag

/-! The same in a `mutual`, where the local is a sibling member's index. -/

mutual
inductive LocB : Type where
  | tip
  | mk (n : Nat) (v : List (LocC n))
inductive LocC : Nat → Type where
  | mk (n : Nat) (b : LocB) : LocC n
end

/-- info: LocB.mk : (n : Nat) → List (LocC n) → LocB -/
#guard_msgs in
#check @LocB.mk

example : LocB := .mk 2 [.mk 2 .tip]

/-! The local may be the writer's *own* index, which is the harder-sounding
version of the same thing: the copy of the nesting type would have to be
parameterised by a value only the constructor knows.  It is not parameterised by
it -- it is *indexed* by it, and that a copy can be. -/

inductive LocIx : Nat → Type where
  | tip : LocIx 0
  | mk (n : Nat) (v : List (LocIx n)) : LocIx (n + 1)

/--
info: @LocIx.rec : {motive_1 : (a : Nat) → LocIx a → Sort u_1} →
  {motive_2 : (n : Nat) → List (LocIx n) → Sort u_1} →
    motive_1 0 LocIx.tip →
      ((n : Nat) → (v : List (LocIx n)) → motive_2 n v → motive_1 (n + 1) (LocIx.mk n v)) →
        ((n : Nat) → motive_2 n []) →
          ((n : Nat) →
              (head : LocIx n) →
                (tail : List (LocIx n)) → motive_1 n head → motive_2 n tail → motive_2 n (head :: tail)) →
            {a : Nat} → (t : LocIx a) → motive_1 a t
-/
#guard_msgs in
#check @LocIx.rec

def locIxSize {n : Nat} (r : LocIx n) : Nat :=
  LocIx.rec (motive_1 := fun _ _ => Nat) (motive_2 := fun _ _ => Nat)
    1 (fun _ _ ih => ih + 1) (fun _ => 0) (fun _ _ _ hd tl => hd + tl) r

example : locIxSize .tip = 1 := rfl
example : locIxSize (.mk 0 [.tip]) = 2 := rfl

/-- info: 2 -/
#guard_msgs in
#eval locIxSize (.mk 0 [.tip])

/-- info: 'locIxSize' does not depend on any axioms -/
#guard_msgs in
#print axioms locIxSize

/-! The nesting type does not have to be `List`. -/

inductive LocTree (α : Type) : Type where
  | tip
  | node (l : α) (r : LocTree α)

inductive LocS : Nat → Type where
  | base : LocS 0
  | mk (n : Nat) (x : LocTree (LocS n)) : LocS n

/-- info: LocS.mk : (n : Nat) → LocTree (LocS n) → LocS n -/
#guard_msgs in
#check @LocS.mk

/--
info: @LocS.rec : {motive_1 : (a : Nat) → LocS a → Sort u_1} →
  {motive_2 : (n : Nat) → LocTree (LocS n) → Sort u_1} →
    motive_1 0 LocS.base →
      ((n : Nat) → (x : LocTree (LocS n)) → motive_2 n x → motive_1 n (LocS.mk n x)) →
        ((n : Nat) → motive_2 n LocTree.tip) →
          ((n : Nat) →
              (l : LocS n) → (r : LocTree (LocS n)) → motive_1 n l → motive_2 n r → motive_2 n (LocTree.node l r)) →
            {a : Nat} → (t : LocS a) → motive_1 a t
-/
#guard_msgs in
#check @LocS.rec

def locSNodes {n : Nat} (s : LocS n) : Nat :=
  LocS.rec (motive_1 := fun _ _ => Nat) (motive_2 := fun _ _ => Nat)
    1 (fun _ _ ih => ih) (fun _ => 0) (fun _ _ _ hl hr => hl + hr + 1) s

example : locSNodes .base = 1 := rfl

/-- info: 2 -/
#guard_msgs in
#eval locSNodes (.mk 0 (.node .base .tip))

/-- info: 'locSNodes' does not depend on any axioms -/
#guard_msgs in
#print axioms locSNodes

/-! Only the copies that need the local get it.  `LocMix` nests twice, once
under the local and once not, and the second copy stays unindexed. -/

inductive LocMix : Type where
  | tip
  | mk (n : Nat) (v : List (LocWrap LocMix n)) (w : List LocMix)

/-- info: LocMix.mk : (n : Nat) → List (LocWrap LocMix n) → List LocMix → LocMix -/
#guard_msgs in
#check @LocMix.mk

/-- info: LocMix.nested_List_3 : Type -/
#guard_msgs in
#check LocMix.nested_List_3

/-! A local under two layers of nesting reaches both. -/

inductive LocDeep : Type where
  | tip
  | mk (n : Nat) (v : List (List (LocWrap LocDeep n)))

/-- info: LocDeep.mk : (n : Nat) → List (List (LocWrap LocDeep n)) → LocDeep -/
#guard_msgs in
#check @LocDeep.mk

/-- info: LocDeep.nested_List_2 (n : Nat) : Type -/
#guard_msgs in
#check LocDeep.nested_List_2

/-! Two different nesting types may hang off the one local. -/

inductive LocTwo where
  | tip
  | mk (n : Nat) (v : List (LocWrap LocTwo n)) (o : Option (LocWrap LocTwo n))

/--
info: LocTwo.mk : (n : Nat) → List (LocWrap LocTwo n) → Option (LocWrap LocTwo n) → LocTwo
-/
#guard_msgs in
#check @LocTwo.mk

/--
info: @LocTwo.rec : {motive_1 : LocTwo → Sort u_1} →
  {motive_2 : (n : Nat) → List (LocWrap LocTwo n) → Sort u_1} →
    {motive_3 : (n : Nat) → LocWrap LocTwo n → Sort u_1} →
      {motive_4 : (n : Nat) → Option (LocWrap LocTwo n) → Sort u_1} →
        motive_1 LocTwo.tip →
          ((n : Nat) →
              (v : List (LocWrap LocTwo n)) →
                (o : Option (LocWrap LocTwo n)) → motive_2 n v → motive_4 n o → motive_1 (LocTwo.mk n v o)) →
            ((n : Nat) → motive_2 n []) →
              ((n : Nat) →
                  (head : LocWrap LocTwo n) →
                    (tail : List (LocWrap LocTwo n)) → motive_3 n head → motive_2 n tail → motive_2 n (head :: tail)) →
                ((n : Nat) → (a : LocTwo) → motive_1 a → motive_3 n (LocWrap.mk a)) →
                  ((n : Nat) → motive_4 n none) →
                    ((n : Nat) → (val : LocWrap LocTwo n) → motive_3 n val → motive_4 n (some val)) →
                      (t : LocTwo) → motive_1 t
-/
#guard_msgs in
#check @LocTwo.rec

/-! The same nesting type may appear at a local in one constructor and at a
value in another.  Those are two members, because `List (LocWrap R 0)` is one
type where `List (LocWrap R n)` is a family, and the narrower one has to win:
sending `at_0`'s list to the family at `0` would give that member's own `nil` a
conclusion at a different type than the member it belongs to. -/

inductive LocBoth where
  | tip
  | at_n (n : Nat) (v : List (LocWrap LocBoth n))
  | at_0 (v : List (LocWrap LocBoth 0))

/-- info: LocBoth.at_n : (n : Nat) → List (LocWrap LocBoth n) → LocBoth -/
#guard_msgs in
#check @LocBoth.at_n

/-- info: LocBoth.at_0 : List (LocWrap LocBoth 0) → LocBoth -/
#guard_msgs in
#check @LocBoth.at_0

/--
info: @LocBoth.rec : {motive_1 : LocBoth → Sort u_1} →
  {motive_2 : (n : Nat) → List (LocWrap LocBoth n) → Sort u_1} →
    {motive_3 : (n : Nat) → LocWrap LocBoth n → Sort u_1} →
      {motive_4 : List (LocWrap LocBoth 0) → Sort u_1} →
        {motive_5 : LocWrap LocBoth 0 → Sort u_1} →
          motive_1 LocBoth.tip →
            ((n : Nat) → (v : List (LocWrap LocBoth n)) → motive_2 n v → motive_1 (LocBoth.at_n n v)) →
              ((v : List (LocWrap LocBoth 0)) → motive_4 v → motive_1 (LocBoth.at_0 v)) →
                ((n : Nat) → motive_2 n []) →
                  ((n : Nat) →
                      (head : LocWrap LocBoth n) →
                        (tail : List (LocWrap LocBoth n)) →
                          motive_3 n head → motive_2 n tail → motive_2 n (head :: tail)) →
                    ((n : Nat) → (a : LocBoth) → motive_1 a → motive_3 n (LocWrap.mk a)) →
                      motive_4 [] →
                        ((head : LocWrap LocBoth 0) →
                            (tail : List (LocWrap LocBoth 0)) →
                              motive_5 head → motive_4 tail → motive_4 (head :: tail)) →
                          ((a : LocBoth) → motive_1 a → motive_5 (LocWrap.mk a)) → (t : LocBoth) → motive_1 t
-/
#guard_msgs in
#check @LocBoth.rec

def bothSize : LocBoth → Nat :=
  LocBoth.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    (motive_3 := fun _ _ => Nat) (motive_4 := fun _ => Nat) (motive_5 := fun _ => Nat)
    1 (fun _ _ ih => ih + 1) (fun _ ih => ih + 1)
    (fun _ => 0) (fun _ _ _ h t => h + t) (fun _ _ ih => ih)
    0 (fun _ _ h t => h + t) (fun _ ih => ih)

/-- info: 3 -/
#guard_msgs in
#eval bothSize (.at_0 [.mk .tip, .mk .tip])

/-- info: 'bothSize' does not depend on any axioms -/
#guard_msgs in
#print axioms bothSize

/-! The nesting may sit under a function type, where the recursion it drives is
infinitary and the round trip costs `Quot.sound`. -/

inductive LocFun where
  | tip
  | mk (n : Nat) (f : Nat → List (LocWrap LocFun n))

/--
info: @LocFun.rec : {motive_1 : LocFun → Sort u_1} →
  {motive_2 : (n : Nat) → List (LocWrap LocFun n) → Sort u_1} →
    {motive_3 : (n : Nat) → LocWrap LocFun n → Sort u_1} →
      motive_1 LocFun.tip →
        ((n : Nat) → (f : Nat → List (LocWrap LocFun n)) → ((a : Nat) → motive_2 n (f a)) → motive_1 (LocFun.mk n f)) →
          ((n : Nat) → motive_2 n []) →
            ((n : Nat) →
                (head : LocWrap LocFun n) →
                  (tail : List (LocWrap LocFun n)) → motive_3 n head → motive_2 n tail → motive_2 n (head :: tail)) →
              ((n : Nat) → (a : LocFun) → motive_1 a → motive_3 n (LocWrap.mk a)) → (t : LocFun) → motive_1 t
-/
#guard_msgs in
#check @LocFun.rec

/-- info: 'LocFun.rec' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms LocFun.rec

/-! A local's own type may mention an earlier local, so long as none of them
mentions the block. -/

inductive LocTag (α : Type) {k : Nat} (i : Fin k) : Type where
  | mk (a : α)

inductive LocFin where
  | tip
  | mk (k : Nat) (i : Fin k) (v : List (LocTag LocFin i))

/-- info: LocFin.mk : (k : Nat) → (i : Fin k) → List (LocTag LocFin i) → LocFin -/
#guard_msgs in
#check @LocFin.mk

/-- info: 'LocFin.rec' does not depend on any axioms -/
#guard_msgs in
#print axioms LocFin.rec

/-! The nesting's parameter may be a *function* of which the local is only part,
as `Sigma`'s second one is.  The local then sits under a lambda, one binder
deeper than the occurrence that has to carry it out. -/

inductive LocSig where
  | tip
  | mk (n : Nat) (p : Σ _ : Nat, LocWrap LocSig n)

/-- info: LocSig.mk : (n : Nat) → (_ : Nat) × LocWrap LocSig n → LocSig -/
#guard_msgs in
#check @LocSig.mk

/-! `Sigma.mk`'s second field is `β fst`, so the copy's own constructor is the
one that has to come out beta-normal, and the minor for it is stated at `⟨_, _⟩`
over the real `Sigma`. -/

/--
info: @LocSig.rec : {motive_1 : LocSig → Sort u_1} →
  {motive_2 : (n : Nat) → (_ : Nat) × LocWrap LocSig n → Sort u_1} →
    {motive_3 : (n : Nat) → LocWrap LocSig n → Sort u_1} →
      motive_1 LocSig.tip →
        ((n : Nat) → (p : (_ : Nat) × LocWrap LocSig n) → motive_2 n p → motive_1 (LocSig.mk n p)) →
          ((n fst : Nat) → (snd : LocWrap LocSig n) → motive_3 n snd → motive_2 n ⟨fst, snd⟩) →
            ((n : Nat) → (a : LocSig) → motive_1 a → motive_3 n (LocWrap.mk a)) → (t : LocSig) → motive_1 t
-/
#guard_msgs in
#check @LocSig.rec

def sigSize : LocSig → Nat :=
  LocSig.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat) (motive_3 := fun _ _ => Nat)
    1 (fun _ _ ih => ih) (fun _ _ _ ih => ih + 1) (fun _ _ ih => ih)

/-- info: 2 -/
#guard_msgs in
#eval sigSize (.mk 3 ⟨7, .mk .tip⟩)

/-- info: 'sigSize' does not depend on any axioms -/
#guard_msgs in
#print axioms sigSize

/-! The block may just as well be in the component that is *not* under the
lambda. -/

inductive LocSigFst where
  | tip
  | mk (n : Nat) (p : Σ _ : LocWrap LocSigFst n, Nat)

/-- info: LocSigFst.mk : (n : Nat) → (_ : LocWrap LocSigFst n) × Nat → LocSigFst -/
#guard_msgs in
#check @LocSigFst.mk

/-- info: 'LocSigFst.rec' does not depend on any axioms -/
#guard_msgs in
#print axioms LocSigFst.rec

/-! Nothing about this is `Sigma`'s: any nesting type whose parameter is a
function does it. -/

inductive LocFn (f : Nat → Type) where
  | mk (g : f 0)

inductive LocFBox where
  | tip
  | mk (n : Nat) (x : LocFn (fun _ => LocWrap LocFBox n))

/-- info: LocFBox.mk : (n : Nat) → (LocFn fun x => LocWrap LocFBox n) → LocFBox -/
#guard_msgs in
#check @LocFBox.mk

/--
info: @LocFBox.rec : {motive_1 : LocFBox → Sort u_1} →
  {motive_2 : (n : Nat) → (LocFn fun x => LocWrap LocFBox n) → Sort u_1} →
    {motive_3 : (n : Nat) → LocWrap LocFBox n → Sort u_1} →
      motive_1 LocFBox.tip →
        ((n : Nat) → (x : LocFn fun x => LocWrap LocFBox n) → motive_2 n x → motive_1 (LocFBox.mk n x)) →
          ((n : Nat) → (g : LocWrap LocFBox n) → motive_3 n g → motive_2 n (LocFn.mk g)) →
            ((n : Nat) → (a : LocFBox) → motive_1 a → motive_3 n (LocWrap.mk a)) → (t : LocFBox) → motive_1 t
-/
#guard_msgs in
#check @LocFBox.rec

/-- info: 'LocFBox.rec' does not depend on any axioms -/
#guard_msgs in
#print axioms LocFBox.rec

/-! The block may be universe-polymorphic.  A copy's universe arrives as a
metavariable -- the nesting type was applied at one, and nothing before the
erasure's same-universe rule has to pin it down -- and that rule is what pins
it. -/

section

inductive LocWrapU (α : Type u) (n : Nat) : Type u where
  | mk (a : α)

inductive LocU : Type u where
  | tip
  | mk (n : Nat) (v : List (LocWrapU LocU n)) : LocU

/-- info: LocU.mk : (n : Nat) → List (LocWrapU LocU n) → LocU -/
#guard_msgs in
#check @LocU.mk

/--
info: @LocU.rec : {motive_1 : LocU → Sort u_1} →
  {motive_2 : (n : Nat) → List (LocWrapU LocU n) → Sort u_1} →
    {motive_3 : (n : Nat) → LocWrapU LocU n → Sort u_1} →
      motive_1 LocU.tip →
        ((n : Nat) → (v : List (LocWrapU LocU n)) → motive_2 n v → motive_1 (LocU.mk n v)) →
          ((n : Nat) → motive_2 n []) →
            ((n : Nat) →
                (head : LocWrapU LocU n) →
                  (tail : List (LocWrapU LocU n)) → motive_3 n head → motive_2 n tail → motive_2 n (head :: tail)) →
              ((n : Nat) → (a : LocU) → motive_1 a → motive_3 n (LocWrapU.mk a)) → (t : LocU) → motive_1 t
-/
#guard_msgs in
#check @LocU.rec

/-- info: 'LocU.rec' does not depend on any axioms -/
#guard_msgs in
#print axioms LocU.rec

end

/-! The nesting type may itself be a nested inductive.  Lean denests `LocRose`
when it is declared; this denests it again, at the local. -/

inductive LocRose (α : Type) (n : Nat) where
  | node (a : α) (cs : List (LocRose α n))

inductive LocNest where
  | tip
  | mk (n : Nat) (r : LocRose LocNest n) : LocNest

/-- info: LocNest.mk : (n : Nat) → LocRose LocNest n → LocNest -/
#guard_msgs in
#check @LocNest.mk

/--
info: @LocNest.rec : {motive_1 : LocNest → Sort u_1} →
  {motive_2 : (n : Nat) → LocRose LocNest n → Sort u_1} →
    {motive_3 : (n : Nat) → List (LocRose LocNest n) → Sort u_1} →
      motive_1 LocNest.tip →
        ((n : Nat) → (r : LocRose LocNest n) → motive_2 n r → motive_1 (LocNest.mk n r)) →
          ((n : Nat) →
              (a : LocNest) →
                (cs : List (LocRose LocNest n)) → motive_1 a → motive_3 n cs → motive_2 n (LocRose.node a cs)) →
            ((n : Nat) → motive_3 n []) →
              ((n : Nat) →
                  (head : LocRose LocNest n) →
                    (tail : List (LocRose LocNest n)) → motive_2 n head → motive_3 n tail → motive_3 n (head :: tail)) →
                (t : LocNest) → motive_1 t
-/
#guard_msgs in
#check @LocNest.rec

/-! Two constructors whose locals differ only in name are one occurrence, so
they share a copy and the recursor asks for one motive, not two. -/

inductive LocShare where
  | tip
  | mk1 (n : Nat) (v : List (LocWrap LocShare n))
  | mk2 (m : Nat) (v : List (LocWrap LocShare m))

/--
info: @LocShare.rec : {motive_1 : LocShare → Sort u_1} →
  {motive_2 : (n : Nat) → List (LocWrap LocShare n) → Sort u_1} →
    {motive_3 : (n : Nat) → LocWrap LocShare n → Sort u_1} →
      motive_1 LocShare.tip →
        ((n : Nat) → (v : List (LocWrap LocShare n)) → motive_2 n v → motive_1 (LocShare.mk1 n v)) →
          ((m : Nat) → (v : List (LocWrap LocShare m)) → motive_2 m v → motive_1 (LocShare.mk2 m v)) →
            ((n : Nat) → motive_2 n []) →
              ((n : Nat) →
                  (head : LocWrap LocShare n) →
                    (tail : List (LocWrap LocShare n)) →
                      motive_3 n head → motive_2 n tail → motive_2 n (head :: tail)) →
                ((n : Nat) → (a : LocShare) → motive_1 a → motive_3 n (LocWrap.mk a)) → (t : LocShare) → motive_1 t
-/
#guard_msgs in
#check @LocShare.rec

/-! The one field may be both a parameter of the nesting type and an index of
it, and then it leads the copy's motive twice over -- once as the local it
generalises, once as the index it always was. -/

inductive LocVec (α : Type) : Nat → Type where
  | nil : LocVec α 0
  | cons (a : α) {k : Nat} (v : LocVec α k) : LocVec α (k + 1)

inductive LocIxNest where
  | tip
  | mk (n : Nat) (v : LocVec (LocWrap LocIxNest n) n) : LocIxNest

/-- info: LocIxNest.mk : (n : Nat) → LocVec (LocWrap LocIxNest n) n → LocIxNest -/
#guard_msgs in
#check @LocIxNest.mk

/--
info: @LocIxNest.rec : {motive_1 : LocIxNest → Sort u_1} →
  {motive_2 : (n a : Nat) → LocVec (LocWrap LocIxNest n) a → Sort u_1} →
    {motive_3 : (n : Nat) → LocWrap LocIxNest n → Sort u_1} →
      motive_1 LocIxNest.tip →
        ((n : Nat) → (v : LocVec (LocWrap LocIxNest n) n) → motive_2 n n v → motive_1 (LocIxNest.mk n v)) →
          ((n : Nat) → motive_2 n 0 LocVec.nil) →
            ((n : Nat) →
                (a : LocWrap LocIxNest n) →
                  {k : Nat} →
                    (v : LocVec (LocWrap LocIxNest n) k) →
                      motive_3 n a → motive_2 n k v → motive_2 n (k + 1) (LocVec.cons a v)) →
              ((n : Nat) → (a : LocIxNest) → motive_1 a → motive_3 n (LocWrap.mk a)) → (t : LocIxNest) → motive_1 t
-/
#guard_msgs in
#check @LocIxNest.rec

/-! A `Subtype` reaches the local from both of its parameters at once, the
second under a lambda. -/

inductive LocSub where
  | tip
  | mk (n : Nat) (p : { _x : LocWrap LocSub n // n = n }) : LocSub

/-- info: LocSub.mk : (n : Nat) → { _x // n = n } → LocSub -/
#guard_msgs in
#check @LocSub.mk

/-! And two locals may be reached at two different depths of the one
occurrence. -/

inductive LocPair where
  | tip
  | mk (n m : Nat) (p : Σ _ : LocWrap LocPair n, LocWrap LocPair m) : LocPair

/-- info: LocPair.mk : (n m : Nat) → (_ : LocWrap LocPair n) × LocWrap LocPair m → LocPair -/
#guard_msgs in
#check @LocPair.mk

/-! Without the local there is nothing the kernel could not have done, so the
retry still declines and Lean's own message stands. -/

/--
error: (kernel) arg #1 of 'PlainBad.mk' has a non positive occurrence of the datatypes being declared
-/
#guard_msgs in
inductive PlainBad : Type where
  | mk : (PlainBad → PlainBad) → PlainBad

/-! ## Section variables

Denesting a nesting at a constructor-local is the route this file is about, and
a block written under a `variable` reaches it the same way any other does: the
variables the block uses become its leading parameters before anything is
copied, so the copies are parameterised by them too.
-/

inductive SVWrap (β : Type) (n : Nat) where
  | mk (a : β) : SVWrap β n

section
variable (α : Type)
inductive SVR where
  | tip (a : α)
  | mk (n : Nat) (v : List (SVWrap SVR n)) : SVR
end

/-- info: @SVR.mk : {α : Type} → (n : Nat) → List (SVWrap (SVR α) n) → SVR α -/
#guard_msgs in
#check @SVR.mk

/--
info: @SVR.rec : {α : Type} →
  {motive_1 : SVR α → Sort u_1} →
    {motive_2 : (n : Nat) → List (SVWrap (SVR α) n) → Sort u_1} →
      {motive_3 : (n : Nat) → SVWrap (SVR α) n → Sort u_1} →
        ((a : α) → motive_1 (SVR.tip a)) →
          ((n : Nat) → (v : List (SVWrap (SVR α) n)) → motive_2 n v → motive_1 (SVR.mk n v)) →
            ((n : Nat) → motive_2 n []) →
              ((n : Nat) →
                  (head : SVWrap (SVR α) n) →
                    (tail : List (SVWrap (SVR α) n)) → motive_3 n head → motive_2 n tail → motive_2 n (head :: tail)) →
                ((n : Nat) → (a : SVR α) → motive_1 a → motive_3 n (SVWrap.mk a)) → (t : SVR α) → motive_1 t
-/
#guard_msgs in
#check @SVR.rec

/-! ## The off switch -/

/--
error: (kernel) mutually inductive types must live in the same universe
-/
#guard_msgs in
set_option mumi.enabled false in
inductive Off : Type where
  | mk1 : Off
  | mkT : Nonempty Off → Off
