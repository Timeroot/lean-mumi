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

/-- info: T.mkT : T.nested_Nonempty_1 → T -/
#guard_msgs in
#check @T.mkT

/-- info: T.nested_Nonempty_1 : Prop -/
#guard_msgs in
#check @T.nested_Nonempty_1

/-- info: T.nested_Nonempty_1.intro : ∀ (val : T), T.nested_Nonempty_1 -/
#guard_msgs in
#check @T.nested_Nonempty_1.intro

-- the block-wide recursor eliminates `T` into any sort and the nested `Prop`
-- into `Prop`, which is what the kernel would have given had the universes
-- lined up
/--
info: @T.mutualRec : {motive_1 : T → Sort u_1} →
  {motive_2 : T.nested_Nonempty_1 → Prop} →
    motive_1 T.mk1 →
      ((a : T.nested_Nonempty_1) → motive_2 a → motive_1 (T.mkT a)) →
        (∀ (val : T) (ih_1 : motive_1 val), motive_2 ⋯) → (t : T) → motive_1 t
-/
#guard_msgs in
#check @T.mutualRec

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

/-- info: 7 -/
#guard_msgs in
#eval U.size (.node (.leaf 3) (.node (.leaf 4) (.ghost ⟨.leaf 0⟩)))

example : U.size (.node (.leaf 1) (.leaf 2)) = 3 := rfl

/-! ## Other `Prop` wrappers

Any inductive `Prop` nests the same way; `Nonempty` is not special.  `Exists`
mentions the member inside a binder's domain rather than as a bare parameter.
-/

inductive V : Type where
  | mk0 : V
  | mkE : (∃ _ : V, True) → V

/-- info: V.mkE : V.nested_Exists_1 → V -/
#guard_msgs in
#check @V.mkE

inductive Box (α : Type) : Prop where
  | intro : α → Box α

inductive W : Type where
  | mk0 : Nat → W
  | mkB : Box W → W

/-- info: W.mkB : W.nested_Box_1 → W -/
#guard_msgs in
#check @W.mkB

/-- info: W.nested_Box_1.intro : ∀ (a : W), W.nested_Box_1 -/
#guard_msgs in
#check @W.nested_Box_1.intro

/-! ## Parameters -/

inductive P (α : Type) : Type where
  | leaf : α → P α
  | ghost : Nonempty (P α) → P α

/-- info: P.ghost : (α : Type) → P.nested_Nonempty_1 α → P α -/
#guard_msgs in
#check @P.ghost

/-- info: P.nested_Nonempty_1 : Type → Prop -/
#guard_msgs in
#check @P.nested_Nonempty_1

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

/-- info: Ix.step : (n : Nat) → Ix.nested_Nonempty_1 n → Ix (n + 1) -/
#guard_msgs in
#check @Ix.step

/-- info: Ix.nested_Nonempty_1 : Nat → Prop -/
#guard_msgs in
#check @Ix.nested_Nonempty_1

/-- info: Ix.nested_Nonempty_1.intro : ∀ (n : Nat) (val : Ix n), Ix.nested_Nonempty_1 n -/
#guard_msgs in
#check @Ix.nested_Nonempty_1.intro

/-- Two occurrences that differ only in which local they mention share a member. -/
inductive Iy : Nat → Type where
  | base : Iy 0
  | l : (n : Nat) → Nonempty (Iy n) → Iy (n + 1)
  | r : (m : Nat) → Nonempty (Iy m) → Iy (m + 2)

/-- info: Iy.r : (m : Nat) → Iy.nested_Nonempty_1 m → Iy (m + 2) -/
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

/-! ## The off switch -/

/--
error: (kernel) mutually inductive types must live in the same universe
-/
#guard_msgs in
set_option mumi.enabled false in
inductive Off : Type where
  | mk1 : Off
  | mkT : Nonempty Off → Off
