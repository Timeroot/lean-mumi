import Mumi

/-!
# Heterogeneous `mutual` blocks

Each test asserts twice where it can: an `example ... := rfl` exercises the
recursor's iota rule in the kernel, and an `#eval` exercises the compiled code
that `@[csimp]` redirects to.
-/

/-! ## A `Prop` and a `Type` -/

mutual
inductive A : Prop where
  | mk : B → A
inductive B : Type where
  | leaf : Nat → B
  | fromA : A → B
end

def bTag : B → Nat :=
  @B.mutualRec (fun _ => True) (fun _ => Nat) (fun _ _ => trivial) (fun n => n) (fun _ _ => 0)

example : bTag (B.leaf 7) = 7 := rfl
example : bTag (B.fromA (A.mk (B.leaf 7))) = 0 := rfl

/-- info: 7 -/
#guard_msgs in
#eval bTag (B.leaf 7)

/-- info: 'bTag' does not depend on any axioms -/
#guard_msgs in
#print axioms bTag

/-! The data member's recursor is a genuine large elimination, and the `Prop`
member gets one too. -/

/-- info: 'B.mutualRec' does not depend on any axioms -/
#guard_msgs in
#print axioms B.mutualRec

/-- info: 'A.mutualRec' does not depend on any axioms -/
#guard_msgs in
#print axioms A.mutualRec

/-! ## Three members, three universes -/

mutual
inductive P3 : Prop where
  | fromQ : Q3 → P3
  | fromR : R3 → P3
inductive Q3 : Type 0 where
  | leaf : Nat → Q3
  | fromP : P3 → Q3
  | wrap : Q3 → Q3
inductive R3 : Type 2 where
  | fromP : P3 → R3
  | higher : Type 1 → R3
  | pair : Q3 → R3 → R3
end

def r3Depth : R3 → Nat :=
  @R3.mutualRec (fun _ => True) (fun _ => Nat) (fun _ => Nat)
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun n => n) (fun _ _ => 0) (fun _ ih => ih + 1)
    (fun _ _ => 0) (fun _ => 0) (fun _ _ ihq ihr => ihq + ihr)

example : r3Depth (R3.pair (Q3.wrap (Q3.leaf 4)) (R3.fromP (P3.fromQ (Q3.leaf 3)))) = 5 := rfl

/-- info: 5 -/
#guard_msgs in
#eval r3Depth (R3.pair (Q3.wrap (Q3.leaf 4)) (R3.fromP (P3.fromQ (Q3.leaf 3))))

/-- info: 'r3Depth' does not depend on any axioms -/
#guard_msgs in
#print axioms r3Depth

/-! ## Indices, with the data member carrying data -/

mutual
inductive Ev : Nat → Prop where
  | zero : Ev 0
  | succ : (n : Nat) → Od n → Ev (n + 1)
inductive Od : Nat → Type 0 where
  | one : Od 1
  | succ : (n : Nat) → Ev (n + 1) → Od n → Nat → Od (n + 2)
end

def odSum : (n : Nat) → Od n → Nat :=
  fun n t => @Od.mutualRec (fun _ _ => True) (fun _ _ => Nat)
    trivial (fun _ _ _ => trivial) 0 (fun _ _ _ k _ ih => ih + k) n t

def od5 : Od 5 :=
  .succ 3 (.succ 3 (.succ 1 (.succ 1 .one) .one 4)) (.succ 1 (.succ 1 .one) .one 4) 6

example : odSum 5 od5 = 10 := rfl

/-- info: 10 -/
#guard_msgs in
#eval odSum 5 od5

/-! ## Parameters -/

mutual
inductive Wrap (α : Type) : Prop where
  | mk : Box α → Wrap α
inductive Box (α : Type) : Type 1 where
  | val : α → Type → Box α
  | back : Wrap α → Box α
end

def boxTag {α : Type} : Box α → Nat :=
  @Box.mutualRec α (fun _ => True) (fun _ => Nat)
    (fun _ _ => trivial) (fun _ _ => 0) (fun _ _ => 1)

example : boxTag (Box.val (3 : Nat) Nat) = 0 := rfl
example : boxTag (Box.back (Wrap.mk (Box.val (3 : Nat) Nat))) = 1 := rfl

/-- info: 1 -/
#guard_msgs in
#eval boxTag (Box.back (Wrap.mk (Box.val (3 : Nat) Nat)))

/-! ## A function *into* a data member

An infinitary field forces the `Prop` member's recursor through `Classical.choice`;
the data member's recursor stays clean, and so does anything defined from it. -/

mutual
inductive Total : Prop where
  | mk : Stream' → Total
inductive Stream' : Type 0 where
  | nil : Stream'
  | cons : (Nat → Stream') → Stream'
  | back : Total → Stream'
end

def sDepth : Stream' → Nat :=
  @Stream'.mutualRec (fun _ => True) (fun _ => Nat)
    (fun _ _ => trivial) 0 (fun _ ih => ih 3 + 1) (fun _ _ => 0)

example : sDepth (Stream'.cons fun _ => Stream'.cons fun _ => Stream'.nil) = 2 := rfl

/-- info: 2 -/
#guard_msgs in
#eval sDepth (Stream'.cons fun _ => Stream'.cons fun _ => Stream'.nil)

/-- info: 'Total.mutualRec' depends on axioms: [Classical.choice] -/
#guard_msgs in
#print axioms Total.mutualRec

/-! `Stream'` is data, but it has a field of the `Prop` member's type, so its
recursor goes through that member's and inherits the choice.  A data recursor is
clean only when the member has no `Prop` field at all -- `B` above. -/

/-- info: 'Stream'.mutualRec' depends on axioms: [Classical.choice] -/
#guard_msgs in
#print axioms Stream'.mutualRec

/-- info: 'sDepth' depends on axioms: [Classical.choice] -/
#guard_msgs in
#print axioms sDepth

/-! ## What makes it computable

Each data member gets an implementation and a kernel-checked theorem tying the
recursor to it, registered with `@[csimp]`. -/

/-- info: B.mutualRec.eq_impl : @B.mutualRec = @B.mutualRec.impl -/
#guard_msgs in
#check @B.mutualRec.eq_impl

/-- info: 'B.mutualRec.impl' does not depend on any axioms -/
#guard_msgs in
#print axioms B.mutualRec.impl
