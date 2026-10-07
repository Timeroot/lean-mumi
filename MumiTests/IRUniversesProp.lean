import MumiTests.Spec.Harness

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
was written.  `mumi_spec` checks each block; what follows is what that leaves out.
-/

set_option autoImplicit false
set_option mumi.mahlo false

namespace UnivProp

mumi_spec (xfail := [rec, recOn, casesOn])
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

example : F A.a0 = Type := rfl
example (x : A) (f : F x → A) (h : P x) (b : B) (k : G b) (hx : P x) : P (A.a1 x f h) := P.one x f h b k hx

/-- `A.rec` and `B.rec` are one recursion over the carriers, with a motive at
each, as a `mutual` block's are; the motive a function does not need is
discharged at `Unit`. -/
def depth : A → Nat :=
  A.rec (motive_2 := fun _ => Unit) 0 (fun _ _ _ ih _ => ih + 1) () (fun _ _ _ _ _ _ _ => ())
def sizeB : B → Nat :=
  B.rec (motive_1 := fun _ => Unit) () (fun _ _ _ _ _ => ()) 0
    (fun x _ _ _ _ ih _ => depth x + ih + 1)

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

mumi_spec (xfail := [rec, recOn, casesOn])
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

/-! An indexed carrier of the lower universe as a field of the higher one,
and the proof tying them back: `Big.over` takes a context and a type over it,
`Fine` takes a `Big`.  One universe up `Ctx` and `Ty` are induction-inductive
and `Big` leaves that block; at the written universe `Big`'s engine reads
`Ty`'s raw terms with their coherence.  Either way the recursion is one per
universe, as a `mutual` has one: `Ctx.rec` over `Ctx` and `Ty`, `Big.rec` over
`Big`, with no hypothesis at its `Ctx` or `Ty`. -/

namespace MixIdx
set_option mumi.mahlo false

mumi_spec (xfail := [rec, recOn, casesOn])
mutual
inductive Ctx : Type where
  | nil : Ctx
  | snoc (Γ : Ctx) (A : Ty Γ) (h : Fine Γ A) : Ctx
inductive Ty : Ctx → Type where
  | base (Γ : Ctx) : Ty Γ
  | pi (Γ : Ctx) (A : Ty Γ) (h : Fine Γ A) (B : Ty (.snoc Γ A h)) : Ty Γ
inductive Big : Type 2 where
  | top : Big
  | over (Γ : Ctx) (A : Ty Γ) (v : Val Γ A) (b : Big) (g : Large b → Big) : Big
inductive Fine : (Γ : Ctx) → Ty Γ → Prop where
  | base (Γ : Ctx) : Fine Γ (.base Γ)
  | pi (Γ : Ctx) (A : Ty Γ) (h : Fine Γ A) (B : Ty (.snoc Γ A h)) (hB : Fine (.snoc Γ A h) B) (b : Big) (w : Large b) : Fine Γ (.pi Γ A h B)
def El : Ctx → Type
  | .nil => Unit
  | .snoc Γ A h => El Γ × Val Γ A
def Val : (Γ : Ctx) → Ty Γ → Type
  | _, .base Γ => Nat
  | _, .pi Γ A h B => (x : Val Γ A) → Val (.snoc Γ A h) B
def Large : Big → Type 2
  | .top => Type 1
  | .over Γ A v b g => Val Γ A × ((z : Large b) → Large (g z))
end

/-- One recursion over the three, as `Mumi.IndInd` declares the graphs. -/
def clen : Ctx → Nat :=
  Ctx.rec (motive_2 := fun _ _ => Nat) (motive_3 := fun _ => Nat) 0 (fun _ _ _ ih _ => ih + 1)
    (fun _ _ => 0) (fun _ _ _ _ _ ihA ihB => ihA + ihB + 1) 0 (fun _ _ _ _ _ _ _ ih _ => ih + 1)
example (Γ : Ctx) (A : Ty Γ) (h : Fine Γ A) : clen (Ctx.snoc Γ A h) = clen Γ + 1 := rfl

theorem Fine.base_or_pi (Γ : Ctx) (A : Ty Γ) (h : Fine Γ A) : A = Ty.base Γ ∨ ∃ A' h' B, A = Ty.pi Γ A' h' B := by
  induction h with
  | base Γ => exact .inl rfl
  | pi Γ A h B hB b w ih ihB => exact .inr ⟨A, h, B, rfl⟩

/-- info: 1 -/
#guard_msgs in
#eval clen (Ctx.snoc .nil (.base .nil) (.base .nil))

/-- info: 'MixIdx.clen' does not depend on any axioms -/
#guard_msgs in
#print axioms clen

end MixIdx

namespace MixIdxLower
set_option mumi.mahlo true
set_option maxRecDepth 6000

mumi_spec (xfail := [rec, recOn, casesOn])
mutual
inductive Ctx : Type where
  | nil : Ctx
  | snoc (Γ : Ctx) (A : Ty Γ) (h : Fine Γ A) : Ctx
inductive Ty : Ctx → Type where
  | base (Γ : Ctx) : Ty Γ
  | pi (Γ : Ctx) (A : Ty Γ) (h : Fine Γ A) (B : Ty (.snoc Γ A h)) : Ty Γ
inductive Big : Type 2 where
  | top : Big
  | over (Γ : Ctx) (A : Ty Γ) (v : Val Γ A) (b : Big) (g : Large b → Big) : Big
inductive Fine : (Γ : Ctx) → Ty Γ → Prop where
  | base (Γ : Ctx) : Fine Γ (.base Γ)
  | pi (Γ : Ctx) (A : Ty Γ) (h : Fine Γ A) (B : Ty (.snoc Γ A h)) (hB : Fine (.snoc Γ A h) B) (b : Big) (w : Large b) : Fine Γ (.pi Γ A h B)
def El : Ctx → Type
  | .nil => Unit
  | .snoc Γ A h => El Γ × Val Γ A
def Val : (Γ : Ctx) → Ty Γ → Type
  | _, .base Γ => Nat
  | _, .pi Γ A h B => (x : Val Γ A) → Val (.snoc Γ A h) B
def Large : Big → Type 2
  | .top => Type 1
  | .over Γ A v b g => Val Γ A × ((z : Large b) → Large (g z))
end

def clen : Ctx → Nat :=
  Ctx.rec (motive_2 := fun _ _ => Nat) 0 (fun _ _ _ ih _ => ih + 1) (fun _ _ => 0) (fun _ _ _ _ _ ihA ihB => ihA + ihB + 1)
def bsize : Big → Nat := Big.rec 0 (fun Γ _ _ _ _ ih _ => clen Γ + ih + 1)
example (Γ : Ctx) (A : Ty Γ) (v : Val Γ A) (b : Big) (g : Large b → Big) :
    bsize (Big.over Γ A v b g) = clen Γ + bsize b + 1 := rfl

theorem Fine.base_or_pi (Γ : Ctx) (A : Ty Γ) (h : Fine Γ A) : A = Ty.base Γ ∨ ∃ A' h' B, A = Ty.pi Γ A' h' B := by
  induction h with
  | base Γ => exact .inl rfl
  | pi Γ A h B hB b w ih ihB => exact .inr ⟨A, h, B, rfl⟩

/-- info: 1 -/
#guard_msgs in
#eval bsize (Big.over .nil (.base .nil) (cast (Val_base .nil).symm 3) .top fun _ => .top)

/-- info: 'MixIdxLower.bsize' depends on axioms: [IR.mahlo] -/
#guard_msgs in
#print axioms bsize

end MixIdxLower

/-! Polymorphic universes, `Type u` and `Type (u+1)`, tied by the `Prop`: the
generated declarations name the block's constants at their universes
explicitly, which is what keeps `u` and `u+1` apart under inference. -/

universe u

namespace PolyMix
set_option mumi.mahlo false

mumi_spec (xfail := [rec, recOn, casesOn])
mutual
inductive A : Type u where
  | a0 : A
  | a1 (x : A) (f : F x → A) (h : P x) : A
inductive B : Type (u+1) where
  | b0 : B
  | b1 (x : A) (b : B) (g : G b → B) : B
inductive P : A → Prop where
  | zero : P .a0
  | one (x : A) (f : F x → A) (h : P x) (b : B) (k : G b) : P (.a1 x f h)
def F : A → Type u
  | .a0 => PUnit
  | .a1 x f h => (y : F x) → F (f y)
def G : B → Type (u+1)
  | .b0 => Type u
  | .b1 x b g => F x × ((z : G b) → G (g z))
end

def depth : A.{u} → Nat :=
  A.rec (motive_2 := fun _ => Unit) 0 (fun _ _ _ ih _ => ih + 1) () (fun _ _ _ _ _ _ => ())
def sizeB : B.{u} → Nat :=
  B.rec (motive_1 := fun _ => Unit) () (fun _ _ _ _ _ => ()) 0
    (fun x _ _ _ ih _ => depth x + ih + 1)
example (x : A.{u}) (b : B) (g : G b → B) : sizeB (B.b1 x b g) = depth x + sizeB b + 1 := rfl
theorem P.t (a : A.{u}) (h : P a) : a = A.a0 ∨ 0 < depth a := by
  induction h with
  | zero => exact .inl rfl
  | one x f h b k ih => exact .inr (Nat.succ_pos _)

/-- info: 'PolyMix.sizeB' does not depend on any axioms -/
#guard_msgs in
#print axioms sizeB

end PolyMix

namespace PolyMixLower
set_option mumi.mahlo true
set_option maxRecDepth 6000

mumi_spec (xfail := [rec, recOn, casesOn])
mutual
inductive A : Type u where
  | a0 : A
  | a1 (x : A) (f : F x → A) (h : P x) : A
inductive B : Type (u+1) where
  | b0 : B
  | b1 (x : A) (b : B) (g : G b → B) : B
inductive P : A → Prop where
  | zero : P .a0
  | one (x : A) (f : F x → A) (h : P x) (b : B) (k : G b) : P (.a1 x f h)
def F : A → Type u
  | .a0 => PUnit
  | .a1 x f h => (y : F x) → F (f y)
def G : B → Type (u+1)
  | .b0 => Type u
  | .b1 x b g => F x × ((z : G b) → G (g z))
end

def depth : A.{u} → Nat := A.rec 0 (fun _ _ _ ih _ => ih + 1)
def sizeB : B.{u} → Nat := B.rec 0 (fun x _ _ ih _ => depth x + ih + 1)
example (x : A.{u}) (b : B) (g : G b → B) : sizeB (B.b1 x b g) = depth x + sizeB b + 1 := rfl
theorem P.t (a : A.{u}) (h : P a) : a = A.a0 ∨ 0 < depth a := by
  induction h with
  | zero => exact .inl rfl
  | one x f h b k ih => exact .inr (Nat.succ_pos _)

/-- info: 'PolyMixLower.sizeB' depends on axioms: [IR.mahlo] -/
#guard_msgs in
#print axioms sizeB

end PolyMixLower

/-! Two universe parameters: `A : Type u`, `B : Type (max u v + 1)`. -/

universe v

namespace TwoParams
set_option mumi.mahlo false
set_option linter.unusedVariables false

mumi_spec (xfail := [rec, recOn, casesOn])
mutual
inductive A : Type u where
  | a0 : A
  | a1 (x : A) (f : F x → A) (h : P x) : A
inductive B : Type (max u v + 1) where
  | b0 : B
  | b1 (x : A) (b : B) (g : G b → B) : B
inductive P : A → Prop where
  | zero : P .a0
  | one (x : A) (f : F x → A) (h : P x) (b : B) (k : G b) : P (.a1 x f h)
def F : A → Type u
  | .a0 => PUnit
  | .a1 x f h => (y : F x) → F (f y)
def G : B → Type (max u v + 1)
  | .b0 => Type (max u v)
  | .b1 x b g => F x × ((z : G b) → G (g z))
end

def depth : A.{u} → Nat :=
  A.rec (motive_2 := fun _ => Unit) 0 (fun _ _ _ ih _ => ih + 1) () (fun _ _ _ _ _ _ => ())
def sizeB : B.{u, v} → Nat :=
  B.rec (motive_1 := fun _ => Unit) () (fun _ _ _ _ _ => ()) 0
    (fun x _ _ _ ih _ => depth x + ih + 1)
example (x : A.{u}) (b : B.{u, v}) (g : G b → B) : sizeB (B.b1 x b g) = depth x + sizeB b + 1 := rfl

end TwoParams

namespace TwoParamsLower
set_option mumi.mahlo true
set_option maxRecDepth 6000
set_option linter.unusedVariables false

mumi_spec (xfail := [rec, recOn, casesOn])
mutual
inductive A : Type u where
  | a0 : A
  | a1 (x : A) (f : F x → A) (h : P x) : A
inductive B : Type (max u v + 1) where
  | b0 : B
  | b1 (x : A) (b : B) (g : G b → B) : B
inductive P : A → Prop where
  | zero : P .a0
  | one (x : A) (f : F x → A) (h : P x) (b : B) (k : G b) : P (.a1 x f h)
def F : A → Type u
  | .a0 => PUnit
  | .a1 x f h => (y : F x) → F (f y)
def G : B → Type (max u v + 1)
  | .b0 => Type (max u v)
  | .b1 x b g => F x × ((z : G b) → G (g z))
end

def depth : A.{u} → Nat := A.rec 0 (fun _ _ _ ih _ => ih + 1)
def sizeB : B.{u, v} → Nat := B.rec 0 (fun x _ _ ih _ => depth x + ih + 1)
example (x : A.{u}) (b : B.{u, v}) (g : G b → B) : sizeB (B.b1 x b g) = depth x + sizeB b + 1 := rfl

end TwoParamsLower
