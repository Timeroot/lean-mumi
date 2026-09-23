import Mumi

set_option maxRecDepth 6000

namespace IRShapesUpper
set_option mumi.mahlo false

universe u
mutual
  inductive Tree : Type u where
    | leaf (n : Nat) : Tree
    | node (t : Tree) (children : ∀ (i : Fin (width t)) (j : Fin (i.val+1)), Tree) : Tree
    | checked (t : Tree) (h : width t = width t) : Tree
  def width : Tree → Nat
    | .leaf n => n
    | .node t children => width t + 1
    | .checked t h => width t
end

example (n : Nat) : width (Tree.leaf.{u} n) = n := rfl
example (t : Tree.{u}) (f : ∀ (i : Fin (width t)) (_j : Fin (i.val+1)), Tree.{u}) :
    width (Tree.node t f) = width t + 1 := rfl
example (t : Tree.{u}) (h : width t = width t) : width (Tree.checked t h) = width t := rfl

mutual
  inductive Ty : Type where
    | nat : Ty
    | forget (p : Point) : Ty
  inductive Point : Type where
    | mark (a : Ty) (x : El a) : Point
  def El : Ty → Type
    | .nat => Nat
    | .forget p => pointType p
  def pointType : Point → Type
    | .mark a x => El a
  def pointValue : (p : Point) → pointType p
    | .mark a x => x
end

example (a : Ty) (x : El a) : pointValue (Point.mark a x) = x := rfl
example (p : Point) : El (Ty.forget p) = pointType p := rfl

namespace Names
mutual
  inductive Value : Type where
    | leaf (n : Nat) : Value
  def get : Value → Nat
    | .leaf k => let q := k; match q with | .zero => 0 | .succ v => v + 1
  def add : Value → Nat → Nat
    | .leaf k => fun x => k + x
end
example (n : Nat) : get (Value.leaf n) = n := by cases n <;> rfl
example (n x : Nat) : add (Value.leaf n) x = n + x := rfl
end Names

end IRShapesUpper

namespace IRShapesLower
set_option mumi.mahlo true

universe u
mutual
  inductive Tree : Type u where
    | leaf (n : Nat) : Tree
    | node (t : Tree) (children : ∀ (i : Fin (width t)) (j : Fin (i.val+1)), Tree) : Tree
    | checked (t : Tree) (h : width t = width t) : Tree
  def width : Tree → Nat
    | .leaf n => n
    | .node t children => width t + 1
    | .checked t h => width t
end

example (n : Nat) : width (Tree.leaf.{u} n) = n := rfl
example (t : Tree.{u}) (f : ∀ (i : Fin (width t)) (_j : Fin (i.val+1)), Tree.{u}) :
    width (Tree.node t f) = width t + 1 := rfl
example (t : Tree.{u}) (h : width t = width t) : width (Tree.checked t h) = width t := rfl

mutual
  inductive Ty : Type where
    | nat : Ty
    | forget (p : Point) : Ty
  inductive Point : Type where
    | mark (a : Ty) (x : El a) : Point
  def El : Ty → Type
    | .nat => Nat
    | .forget p => pointType p
  def pointType : Point → Type
    | .mark a x => El a
  def pointValue : (p : Point) → pointType p
    | .mark a x => x
end

example (a : Ty) (x : El a) : pointValue (Point.mark a x) = x := rfl
example (p : Point) : El (Ty.forget p) = pointType p := rfl

namespace Names
mutual
  inductive Value : Type where
    | leaf (n : Nat) : Value
  def get : Value → Nat
    | .leaf k => let q := k; match q with | .zero => 0 | .succ v => v + 1
  def add : Value → Nat → Nat
    | .leaf k => fun x => k + x
end
example (n : Nat) : get (Value.leaf n) = n := by cases n <;> rfl
example (n x : Nat) : add (Value.leaf n) x = n + x := rfl
end Names

end IRShapesLower
