import MumiTests.Spec.Harness

/-!
# Nested occurrences in an IR block

A carrier may occur nested in another inductive type, `(fs : List U)`, and a
decoder may recurse over that type, with Lean's own patterns.  What the block
gets is what Lean gives a nested inductive: the constructor takes the original
`List U`, the decoder is over `List U`, `U.rec` has a motive for `List U` with
cases for `[]` and `::`, and `U.rec_1` enters the same recursion at a list.

Underneath, the kernel sees a copy of `List` specialised to `U`, as it does for
any nested inductive.  A value stores the copy, so the recursor's rule at the
nested constructor itself, `U.rec … (U.tuple fs)`, holds as the equation
`U.rec_tuple`, and by `rfl` once `fs` is closed; every other rule, and every
decoder equation, is `rfl`.  `mumi_spec` checks all of it, the nested rules
named; what follows each block is what that leaves out.
-/

set_option autoImplicit false

namespace Codes
set_option mumi.mahlo false

mumi_spec (simp := [U.rec_tuple, U.rec_opt]) (unproven := [U.casesOn_tuple, U.casesOn_opt]) (xfail := [recOn, injEq, axioms])
mutual
inductive U : Type where
  | nat : U
  | tuple (fs : List U) : U
  | opt (o : Option U) : U
  | pi (a : U) (b : El a → U) : U
def El : U → Type
  | .nat => Nat
  | .tuple fs => Els fs
  | .opt o => Elo o
  | .pi a b => (x : El a) → El (b x)
def Els : List U → Type
  | [] => Unit
  | a :: as => El a × Els as
def Elo : Option U → Type
  | none => Unit
  | some a => El a
end

-- the decoders compute at a closed value
example : El (.tuple [.nat, .opt (some .nat)]) = (Nat × Nat × Unit) := rfl

def size : U → Nat :=
  U.rec (motive_2 := fun _ => Nat) (motive_3 := fun _ => Nat)
    1 (fun _ ih => ih + 1) (fun _ ih => ih + 1) (fun _ _ ih _ => ih + 1)
    0 (fun _ _ ih ihs => ih + ihs) 0 (fun _ ih => ih)
def sizes : List U → Nat :=
  U.rec_1 (motive_1 := fun _ => Nat) (motive_3 := fun _ => Nat)
    1 (fun _ ih => ih + 1) (fun _ ih => ih + 1) (fun _ _ ih _ => ih + 1)
    0 (fun _ _ ih ihs => ih + ihs) 0 (fun _ ih => ih)

-- the rules at every constructor but the nested one are `rfl`
example (a : U) (b : El a → U) : size (.pi a b) = size a + 1 := rfl
example (a : U) (as : List U) : sizes (a :: as) = size a + sizes as := rfl
example : sizes [] = 0 := rfl
-- the nested one is an equation, and `rfl` at a closed list
example (fs : List U) : size (.tuple fs) = sizes fs + 1 := by
  simp only [size, sizes, U.rec_tuple]
example : size (.tuple [.nat, .nat]) = 3 := rfl

/-- info: 4 -/
#guard_msgs in
#eval size (.tuple [.nat, .opt (some .nat)])

example (t : U) : True := by cases t <;> trivial

end Codes

namespace CodesLower
set_option mumi.mahlo true
set_option maxRecDepth 8000

mumi_spec (simp := [U.rec_tuple, U.rec_opt]) (unproven := [U.casesOn_tuple, U.casesOn_opt]) (xfail := [recOn, injEq, axioms])
mutual
inductive U : Type where
  | nat : U
  | tuple (fs : List U) : U
  | opt (o : Option U) : U
  | pi (a : U) (b : El a → U) : U
def El : U → Type
  | .nat => Nat
  | .tuple fs => Els fs
  | .opt o => Elo o
  | .pi a b => (x : El a) → El (b x)
def Els : List U → Type
  | [] => Unit
  | a :: as => El a × Els as
def Elo : Option U → Type
  | none => Unit
  | some a => El a
end

def size : U → Nat :=
  U.rec (motive_2 := fun _ => Nat) (motive_3 := fun _ => Nat)
    1 (fun _ ih => ih + 1) (fun _ ih => ih + 1) (fun _ _ ih _ => ih + 1)
    0 (fun _ _ ih ihs => ih + ihs) 0 (fun _ ih => ih)
def sizes : List U → Nat :=
  U.rec_1 (motive_1 := fun _ => Nat) (motive_3 := fun _ => Nat)
    1 (fun _ ih => ih + 1) (fun _ ih => ih + 1) (fun _ _ ih _ => ih + 1)
    0 (fun _ _ ih ihs => ih + ihs) 0 (fun _ ih => ih)

example (a : U) (b : El a → U) : size (.pi a b) = size a + 1 := rfl
example (a : U) (as : List U) : sizes (a :: as) = size a + sizes as := rfl
example (fs : List U) : size (.tuple fs) = sizes fs + 1 := by
  simp only [size, sizes, U.rec_tuple]

/-- info: 4 -/
#guard_msgs in
#eval size (.tuple [.nat, .opt (some .nat)])

end CodesLower

/-! ## Parameters, nesting within nesting, several arguments -/

namespace Shapes
set_option mumi.mahlo false

-- one motive per nested application, in the order they are met: the inner
-- `Option (U α)` last
mumi_spec (simp := [U.rec_tuple]) (unproven := [U.casesOn_tuple]) (xfail := [recOn, injEq, axioms])
mutual
inductive U (α : Type) : Type where
  | atom (a : α) : U α
  | tuple (fs : List (Option (U α))) : U α
  | pair (p : U α × U α) : U α
def El (α : Type) : U α → Type
  | .atom a => α
  | .tuple fs => Elss α fs
  | .pair p => Elp α p
def Elss (α : Type) : List (Option (U α)) → Type
  | [] => Unit
  | o :: os => Elo α o × Elss α os
def Elo (α : Type) : Option (U α) → Type
  | none => PUnit
  | some u => El α u
def Elp (α : Type) : U α × U α → Type
  | (a, b) => El α a ⊕ El α b
end

example : El Nat (.tuple [some (.atom 1), none]) = (Nat × PUnit × Unit) := rfl

def leaves {α : Type} : U α → Nat :=
  U.rec (motive_2 := fun _ => Nat) (motive_3 := fun _ => Nat) (motive_4 := fun _ => Nat)
    (fun _ => 1) (fun _ ih => ih) (fun _ ih => ih)
    0 (fun _ _ ih ihs => ih + ihs) (fun _ _ iha ihb => iha + ihb) 0 (fun _ ih => ih)
example : leaves (U.tuple [some (.atom 1), none, some (.pair (.atom 2, .atom 3))]) = 3 := rfl
example {α : Type} (a b : U α) : leaves (.pair (a, b)) = leaves a + leaves b := by
  simp only [leaves, U.rec_pair, U.rec_2_mk]

end Shapes

namespace ShapesLower
set_option mumi.mahlo true
set_option maxRecDepth 8000

mumi_spec (simp := [U.rec_tuple]) (unproven := [U.casesOn_tuple]) (xfail := [recOn, injEq, axioms])
mutual
inductive U (α : Type) : Type where
  | atom (a : α) : U α
  | tuple (fs : List (U α)) : U α
def El (α : Type) : U α → Type
  | .atom a => α
  | .tuple fs => Els α fs
def Els (α : Type) : List (U α) → Type
  | [] => Unit
  | a :: as => El α a × Els α as
end

end ShapesLower

/-! ## Minor premises named twice

`nil` is `U`'s and `List`'s, and Lean binds both under it. -/

namespace NamesTwice
set_option mumi.mahlo false

mumi_spec (simp := [U.rec_tuple]) (unproven := [U.casesOn_tuple]) (xfail := [recOn, injEq, axioms])
mutual
inductive U : Type where
  | nil : U
  | tuple (fs : List U) : U
def El : U → Type
  | .nil => Unit
  | .tuple fs => Els fs
def Els : List U → Type
  | [] => Unit
  | a :: as => El a × Els as
end

end NamesTwice
