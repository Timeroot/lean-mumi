import MumiTests.Spec.Harness

/-!
# Shapes of fields and clauses

A field whose domain reads a decoder twice over, a proof field about a decoder,
a carrier holding a value of a decoder of another, a decoder into the values of
another (`pointValue`), and clauses with `let` and `match` inside.  `mumi_spec`
checks each block's declarations and equations.
-/

set_option maxRecDepth 6000

namespace IRShapesUpper
set_option mumi.mahlo false

universe u
mumi_spec
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

mumi_spec
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

namespace Names
mumi_spec
mutual
  inductive Value : Type where
    | leaf (n : Nat) : Value
  def get : Value → Nat
    | .leaf k => let q := k; match q with | .zero => 0 | .succ v => v + 1
  def add : Value → Nat → Nat
    | .leaf k => fun x => k + x
end
example (n : Nat) : get (Value.leaf n) = n := by cases n <;> rfl
end Names

end IRShapesUpper

namespace IRShapesLower
set_option mumi.mahlo true

universe u
mumi_spec
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

mumi_spec
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

namespace Names
mumi_spec
mutual
  inductive Value : Type where
    | leaf (n : Nat) : Value
  def get : Value → Nat
    | .leaf k => let q := k; match q with | .zero => 0 | .succ v => v + 1
  def add : Value → Nat → Nat
    | .leaf k => fun x => k + x
end
example (n : Nat) : get (Value.leaf n) = n := by cases n <;> rfl
end Names

end IRShapesLower
