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

/-- info: N.mkL : N.nested_Nonempty_1 → N -/
#guard_msgs in
#check @N.mkL

/-- info: N.nested_Nonempty_1.intro : ∀ (val : N.nested_List_2), N.nested_Nonempty_1 -/
#guard_msgs in
#check @N.nested_Nonempty_1.intro

/-- info: N.nested_List_2.cons : N → N.nested_List_2 → N.nested_List_2 -/
#guard_msgs in
#check @N.nested_List_2.cons

/-! ## Where there is no bridge

A bridge needs the copy and the original to take the same constructor
arguments.  `N.nested_List_2` is a data member -- only isomorphic to `List N`,
not equal to it -- and `N.nested_Nonempty_1`'s field is that copy rather than a
`List N`, so neither gets one.  The types themselves are unaffected.

A member with no bridge keeps its own name, in the coercion that is not there
and in what is displayed: showing `List N` for something merely isomorphic to it
would be a lie, and the `#check`s above say `N.nested_List_2`. -/

/-- error: Unknown constant `N.nested_List_2.coeToOrig` -/
#guard_msgs in
#check @N.nested_List_2.coeToOrig


/-- error: Unknown constant `N.nested_List_2.eq_orig` -/
#guard_msgs in
#check @N.nested_List_2.eq_orig

/-- error: Unknown constant `N.nested_Nonempty_1.eq_orig` -/
#guard_msgs in
#check @N.nested_Nonempty_1.eq_orig

/-- error: Unknown constant `D5A.nested_List_1.eq_orig` -/
#guard_msgs in
#check @D5A.nested_List_1.eq_orig

/-! ## The off switch -/

/--
error: (kernel) mutually inductive types must live in the same universe
-/
#guard_msgs in
set_option mumi.enabled false in
inductive Off : Type where
  | mk1 : Off
  | mkT : Nonempty Off → Off
