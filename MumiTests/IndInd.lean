import Mumi

/-!
# Induction-induction through `Prop`

`Mumi.IndInd` handles a `mutual` block one of whose members' *arities* mentions
a sibling, provided the dependency runs only through proofs.  Lean rejects every
block in this file outright -- a member's arity names a constant that is not yet
in scope -- so there is nothing here whose behaviour could have changed.

The point of each test is that the *visible* declarations are the ones written,
that both iota rules hold by `rfl`, that the result computes, and that no axiom
is added.
-/

/-! ## The motivating block

A context, and the proposition that a name is fresh for it.  `Fresh`'s arity
mentions `Ctx`, and `Ctx.snoc` carries a `Fresh`.
-/

mutual
inductive Ctx : Type where
  | nil : Ctx
  | snoc : (Γ : Ctx) → (x : String) → Fresh x Γ → Ctx
inductive Fresh : String → Ctx → Prop where
  | nil : (x : String) → Fresh x .nil
  | snoc : (x y : String) → (Γ : Ctx) → (h : Fresh y Γ) → x ≠ y → Fresh x Γ →
    Fresh x (.snoc Γ y h)
end

/-- info: Ctx : Type -/
#guard_msgs in
#check @Ctx

/-- info: Fresh : String → Ctx → Prop -/
#guard_msgs in
#check @Fresh

/-- info: Ctx.nil : Ctx -/
#guard_msgs in
#check @Ctx.nil

/-- info: Ctx.snoc : (Γ : Ctx) → (x : String) → Fresh x Γ → Ctx -/
#guard_msgs in
#check @Ctx.snoc

/-- info: Fresh.nil : ∀ (x : String), Fresh x Ctx.nil -/
#guard_msgs in
#check @Fresh.nil

/--
info: Fresh.snoc : ∀ (x y : String) (Γ : Ctx) (h : Fresh y Γ), x ≠ y → Fresh x Γ → Fresh x (Γ.snoc y h)
-/
#guard_msgs in
#check @Fresh.snoc

/--
info: @Ctx.recursor : {C : Ctx → Sort u_1} →
  C Ctx.nil → ((Γ : Ctx) → (x : String) → (a : Fresh x Γ) → C Γ → C (Γ.snoc x a)) → (t : Ctx) → C t
-/
#guard_msgs in
#check @Ctx.recursor

/-! ### The recursor computes, and both iota rules are definitional -/

def Ctx.length (Γ : Ctx) : Nat :=
  Ctx.recursor (C := fun _ => Nat) 0 (fun _ _ _ ih => ih + 1) Γ

example {C : Ctx → Sort u} (n : C .nil)
    (s : (Γ : Ctx) → (x : String) → (h : Fresh x Γ) → C Γ → C (.snoc Γ x h)) :
    Ctx.recursor n s .nil = n := rfl

example {C : Ctx → Sort u} (n : C .nil)
    (s : (Γ : Ctx) → (x : String) → (h : Fresh x Γ) → C Γ → C (.snoc Γ x h))
    (Γ : Ctx) (x : String) (h : Fresh x Γ) :
    Ctx.recursor n s (.snoc Γ x h) = s Γ x h (Ctx.recursor n s Γ) := rfl

/-- A closed term, built through the `Fresh` obligations. -/
def ex : Ctx :=
  .snoc (.snoc .nil "x" (.nil "x")) "y"
    (.snoc "y" "x" .nil (.nil "x") (by decide) (.nil "y"))

/-- info: 2 -/
#guard_msgs in
#eval ex.length

example : ex.length = 2 := rfl

/-- info: 'Ctx.recursor' does not depend on any axioms -/
#guard_msgs in
#print axioms Ctx.recursor

/-- info: 'ex' does not depend on any axioms -/
#guard_msgs in
#print axioms ex

/-- info: 'Ctx.length' does not depend on any axioms -/
#guard_msgs in
#print axioms Ctx.length

/-! ### `induction ... using` is the way to reason about it

The constructors are `def`s, so `match` and a bare `cases` do not see them.  The
recursor's minor premises are named after the constructors, so `induction using`
reads the way it would for a real inductive.
-/

example (Γ : Ctx) : 0 ≤ Γ.length := by
  induction Γ using Ctx.recursor with
  | nil => simp [Ctx.length]
  | snoc Γ x h ih => simp

/-! ## Several `Prop` members

One data member is the limit; the propositions it depends on may be any number.
-/

mutual
inductive Tm : Type where
  | var : Nat → Tm
  | app : (f : Tm) → (a : Tm) → Ok f → Ok a → Tm
  | lam : (b : Tm) → Closed b → Tm
inductive Ok : Tm → Prop where
  | var : (n : Nat) → Ok (.var n)
  | lam : (b : Tm) → (h : Closed b) → Ok (.lam b h)
inductive Closed : Tm → Prop where
  | var : (n : Nat) → Closed (.var n)
  | lam : (b : Tm) → (h : Closed b) → Closed (.lam b h)
end

/-- info: Tm.app : (f a : Tm) → Ok f → Ok a → Tm -/
#guard_msgs in
#check @Tm.app

/-- info: Tm.lam : (b : Tm) → Closed b → Tm -/
#guard_msgs in
#check @Tm.lam

/-- info: Closed.lam : ∀ (b : Tm) (h : Closed b), Closed (b.lam h) -/
#guard_msgs in
#check @Closed.lam

def Tm.size (t : Tm) : Nat :=
  Tm.recursor (C := fun _ => Nat) (fun _ => 1) (fun _ _ _ _ i j => i + j + 1)
    (fun _ _ i => i + 1) t

example : Tm.size (.var 3) = 1 := rfl

example (f a : Tm) (hf : Ok f) (ha : Ok a) :
    Tm.size (.app f a hf ha) = Tm.size f + Tm.size a + 1 := rfl

/-- info: 4 -/
#guard_msgs in
#eval Tm.size (.app (.lam (.var 0) (.var 0)) (.var 1) (.lam (.var 0) (.var 0)) (.var 1))

/-- info: 'Tm.size' does not depend on any axioms -/
#guard_msgs in
#print axioms Tm.size

/-! ## The `Prop` member may come first -/

mutual
inductive Ok3 : Vec3 → Prop where
  | nil : Ok3 .nil
inductive Vec3 : Type where
  | nil : Vec3
  | cons : (v : Vec3) → Ok3 v → Vec3
end

/-- info: Vec3.cons : (v : Vec3) → Ok3 v → Vec3 -/
#guard_msgs in
#check @Vec3.cons

def Vec3.size (v : Vec3) : Nat :=
  Vec3.recursor (C := fun _ => Nat) 0 (fun _ _ ih => ih + 1) v

/-- info: 1 -/
#guard_msgs in
#eval Vec3.size (.cons .nil .nil)

example : Vec3.size (.cons .nil .nil) = 1 := rfl

/-! ## A block we must not claim

An arity mentioning a member's short name is only the *signature* of
induction-induction.  Here `Tag` in `Uses`'s arity means the global `Tag`, not
the sibling being declared, so the block elaborates the way Lean elaborates it
and we never see it: the routing asks whether the headers failed first, and only
then whether an arity names a sibling.
-/

def Tag : Type := Nat

namespace Inner

mutual
inductive Tag : Type where
  | mk : Tag
inductive Uses : Tag → Type where
  | mk : (n : Nat) → Uses n
end

-- the arity resolved to the global, exactly as it does without `Mumi` imported
/-- info: Uses : _root_.Tag → Type -/
#guard_msgs in
#check @Uses

-- and Lean's own elaborator ran: a genuine mutual recursor, with two motives
/--
info: @Uses.rec : {motive_1 : Tag → Sort u_1} →
  {motive_2 : (a : _root_.Tag) → Uses a → Sort u_1} →
    motive_1 Tag.mk → ((n : Nat) → motive_2 n (Uses.mk n)) → {a : _root_.Tag} → (t : Uses a) → motive_2 a t
-/
#guard_msgs in
#check @Uses.rec

-- real constructors, so `match` works -- which is what our lowering gives up
example : (match Uses.mk 3 with | .mk n => n) = 3 := rfl

end Inner

/-! ## Outside the narrow class

Both of these are rejected with an explanation rather than lowered wrongly.  The
first is genuine induction-induction through *data*; the second hides a
proposition of the block inside a piece of data, so erasing it would change the
constructor's arity.
-/

/--
error: This induction-inductive block has 2 members that are not propositions; exactly one is supported
-/
#guard_msgs in
mutual
inductive Vec : Type where
  | nil : Vec
  | cons : (v : Vec) → (n : Len v) → Vec
inductive Len : Vec → Type where
  | nil : Len .nil
end

/--
error: The field `n` of `Vec2.cons` mentions the block, but is neither `Vec2` nor a proof, so this lowering cannot erase it:
  { m // Ok2 v }
-/
#guard_msgs in
mutual
inductive Vec2 : Type where
  | nil : Vec2
  | cons : (v : Vec2) → (n : { m : Nat // Ok2 v }) → Vec2
inductive Ok2 : Vec2 → Prop where
  | nil : Ok2 .nil
end
