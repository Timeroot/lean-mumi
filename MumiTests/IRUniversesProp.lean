import Mumi

/-!
# A `Prop` running a dependency between universes

`A : Type 1` cannot take a `B : Type 3` as a field, but it can take a proof of
`P x`, and `P`'s constructors may take a `B` and a value of its decoder `G`,
so the three are one component: `A` needs `P`, `P` needs `B`, `B` needs `A`.
Lean's `mutual` refuses it twice over -- one universe for the block, and
`P` indexed by `A` -- and the encoding one universe up takes it: the graphs of
`A` and `B` are declared by `Mumi` across the two universes, and the proofs
go into well-formedness predicates over the graphs, `P` among them, which
Lean's own `mutual` takes in `Prop`.  Each carrier lands one above where it
was written.
-/

set_option autoImplicit false
set_option mumi.mahlo false

namespace UnivProp

mutual
inductive A : Type 1 where
  | a0 : A
  | a1 (x : A) (f : F x → A) (h : P x) : A
inductive B : Type 3 where
  | b0 : B
  | b1 (x : A) (v : F x) (b : B) (g : G b → B) : B
inductive P : A → Prop where
  | zero : P .a0
  | one (x : A) (f : F x → A) (h : P x) (b : B) (k : G b) (hx : P x) : P (.a1 x f h)
def F : A → Type 1
  | .a0 => Type
  | .a1 x f h => (y : F x) → F (f y)
def G : B → Type 3
  | .b0 => Type 2
  | .b1 x v b g => F x × ((z : G b) → G (g z))
end

example : Type 2 := A
example : Type 4 := B
example (x : A) : Prop := P x
example (x : A) (f : F x → A) (h : P x) : F (A.a1 x f h) = ((y : F x) → F (f y)) := rfl
example (x : A) (v : F x) (b : B) (g : G b → B) : G (B.b1 x v b g) = (F x × ((z : G b) → G (g z))) := rfl
example : F A.a0 = Type := rfl
example (x : A) (f : F x → A) (h : P x) (b : B) (k : G b) (hx : P x) : P (A.a1 x f h) := P.one x f h b k hx

/-- `A` and `B` are each their own recursion, as `B` reads `A` but not back:
`A.rec` has one motive, and `B.rec` one, with no hypothesis at its `A`. -/
def depth : A → Nat := A.rec 0 (fun _ _ _ ih _ => ih + 1)
def sizeB : B → Nat := B.rec 0 (fun x _ _ _ ih _ => depth x + ih + 1)

example (x : A) (f : F x → A) (h : P x) : depth (A.a1 x f h) = depth x + 1 := rfl
example (x : A) (v : F x) (b : B) (g : G b → B) : sizeB (B.b1 x v b g) = depth x + sizeB b + 1 := rfl

def a1 : A := A.a1 A.a0 (fun _ => A.a0) P.zero
def b1 : B := B.b1 a1 (fun x => x) B.b0 fun _ => B.b0
example : depth a1 = 1 := rfl
example : sizeB b1 = 2 := rfl

/-- info: 2 -/
#guard_msgs in
#eval sizeB b1

/-- The predicate's own recursor, with a hypothesis at each proof of `P` a
constructor takes: `h`, which the conclusion is at, and `hx`. -/
theorem P.depth_pos (a : A) (h : P a) : a = A.a0 ∨ 0 < depth a := by
  induction h with
  | zero => exact .inl rfl
  | one x f h b k hx ih ihx => exact .inr (Nat.succ_pos _)

theorem P.cases_test (a : A) (h : P a) : a = A.a0 ∨ ∃ x f h', a = A.a1 x f h' := by
  cases h with
  | zero => exact .inl rfl
  | one x f h b k hx => exact .inr ⟨x, f, h, rfl⟩

example : P a1 := P.one A.a0 (fun _ => A.a0) P.zero B.b0 (Type 1) P.zero

/-- info: 'UnivProp.sizeB' does not depend on any axioms -/
#guard_msgs in
#print axioms sizeB

/-- info: 'UnivProp.P.depth_pos' does not depend on any axioms -/
#guard_msgs in
#print axioms P.depth_pos

end UnivProp

/-! At the written universe each carrier stays where it was written: one stage
engine per universe, `A`'s first and `B`'s reading `A`'s raw terms and
decoder as values of a type already there, and the certificates of all three
in one `mutual` after both engines.  As above, on the one axiom. -/

namespace UnivPropLower
set_option mumi.mahlo true
set_option maxRecDepth 6000

mutual
inductive A : Type 1 where
  | a0 : A
  | a1 (x : A) (f : F x → A) (h : P x) : A
inductive B : Type 3 where
  | b0 : B
  | b1 (x : A) (v : F x) (b : B) (g : G b → B) : B
inductive P : A → Prop where
  | zero : P .a0
  | one (x : A) (f : F x → A) (h : P x) (b : B) (k : G b) (hx : P x) : P (.a1 x f h)
def F : A → Type 1
  | .a0 => Type
  | .a1 x f h => (y : F x) → F (f y)
def G : B → Type 3
  | .b0 => Type 2
  | .b1 x v b g => F x × ((z : G b) → G (g z))
end

example : Type 1 := A
example : Type 3 := B
example (x : A) (f : F x → A) (h : P x) : F (A.a1 x f h) = ((y : F x) → F (f y)) := rfl
example (x : A) (v : F x) (b : B) (g : G b → B) : G (B.b1 x v b g) = (F x × ((z : G b) → G (g z))) := rfl

def depth : A → Nat := A.rec 0 (fun _ _ _ ih _ => ih + 1)
def sizeB : B → Nat := B.rec 0 (fun x _ _ _ ih _ => depth x + ih + 1)
example (x : A) (f : F x → A) (h : P x) : depth (A.a1 x f h) = depth x + 1 := rfl
example (x : A) (v : F x) (b : B) (g : G b → B) : sizeB (B.b1 x v b g) = depth x + sizeB b + 1 := rfl

theorem P.depth_pos (a : A) (h : P a) : a = A.a0 ∨ 0 < depth a := by
  induction h with
  | zero => exact .inl rfl
  | one x f h b k hx ih ihx => exact .inr (Nat.succ_pos _)

theorem P.cases_test (a : A) (h : P a) : a = A.a0 ∨ ∃ x f h', a = A.a1 x f h' := by
  cases h with
  | zero => exact .inl rfl
  | one x f h b k hx => exact .inr ⟨x, f, h, rfl⟩

def a1 : A := A.a1 A.a0 (fun _ => A.a0) P.zero
-- a closed `F` does not normalise here; its values go through the equations
def v0 : F A.a0 := cast F_a0.symm Nat
def b1 : B := B.b1 a1 (cast (F_a1 A.a0 (fun _ => A.a0) P.zero).symm fun _ => v0) B.b0 fun _ => B.b0
example : P a1 := P.one A.a0 (fun _ => A.a0) P.zero B.b0 (cast G_b0.symm (Type 1)) P.zero

/-- info: 2 -/
#guard_msgs in
#eval sizeB b1

/-- info: 'UnivPropLower.sizeB' depends on axioms: [IR.mahlo] -/
#guard_msgs in
#print axioms sizeB

/-- info: 'UnivPropLower.P.depth_pos' depends on axioms: [IR.mahlo] -/
#guard_msgs in
#print axioms P.depth_pos

end UnivPropLower
