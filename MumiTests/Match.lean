/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import Mumi

/-!
# `match` on a member

A member of an induction-inductive block is a definition over a subtype, so the
equation compiler cannot split on it: it reduces the discriminant's type until
it reaches `Subtype` and then offers `Subtype.mk`.  `Mumi.View` puts a real
inductive over the member in the way and `Mumi.MatchView` rewrites `match` to
go through it, so that a block reads and matches the way it was written.

Every function below is written with an ordinary `match`, with no mention of
the view anywhere.  Most of them are checked by `#eval`, because the point is
not only that they elaborate but that they run: a view is a genuine inductive
and everything built from one has a compiler implementation.

The two things a view cannot do are here as well, near the end -- a constructor
nested inside another pattern, and a promoted argument bound by the pattern
rather than by the type -- so that a change in either shows up as a test
failure.
-/

namespace MumiTests.Match

/-! ## The family

`Ctx` and `Tm` are data and get views; `Ok` is a `Prop` and does not need one. -/

mutual
inductive Ctx : Type where
  | nil
  | snoc (Γ : Ctx) (h : Ok Γ) : Ctx
inductive Ok : Ctx → Prop where
  | nil : Ok .nil
  | snoc (Γ : Ctx) (h : Ok Γ) : Ok (.snoc Γ h)
inductive Tm : (Γ : Ctx) → Ok Γ → Type where
  | var (Γ : Ctx) (h : Ok Γ) : Tm Γ h
  | wk (Γ : Ctx) (h : Ok Γ) (t : Tm Γ h) : Tm Γ h
end

def c1 : Ctx := .snoc .nil .nil
def c2 : Ctx := .snoc c1 (.snoc .nil .nil)
theorem o1 : Ok c1 := .snoc .nil .nil
theorem o2 : Ok c2 := .snoc c1 o1

/-! ## What the rewrite is written against

The view is an inductive over the member itself, so its constructors carry the
same fields under the same names, and an alternative that names one of its
constructors reads as the member's. -/

/-- info: inductive MumiTests.Match.Ctx.View : Ctx → Type
number of parameters: 0
constructors:
MumiTests.Match.Ctx.View.nil : Ctx.nil.View
MumiTests.Match.Ctx.View.snoc : (Γ : Ctx) → (h : Ok Γ) → (Γ.snoc h).View -/
#guard_msgs in
#print Ctx.View

/-- info: Ctx.view : (x : Ctx) → x.View -/
#guard_msgs in
#check @Ctx.view

/-! ## Splitting without recursing -/

def isNil (c : Ctx) : Bool :=
  match c with
  | .nil => true
  | .snoc _ _ => false

/-- info: true -/
#guard_msgs in
#eval isNil .nil

/-- info: false -/
#guard_msgs in
#eval isNil c2

/-! ## Recursion

A view is not a subterm of what it presents, so recursion through one is
well-founded rather than structural.  The `SizeOf` instance and the
`sizeOf_spec` lemmas the block emits are what makes it go through unaided. -/

def len (c : Ctx) : Nat :=
  match c with
  | .nil => 0
  | .snoc Γ _ => len Γ + 1

/-- info: 2 -/
#guard_msgs in
#eval len c2

/-- A `def` by equations is the same `match` and goes the same way. -/
def len' : Ctx → Nat
  | .nil => 0
  | .snoc Γ _ => len' Γ + 1

/-- info: 2 -/
#guard_msgs in
#eval len' c2

/-- `fun` with alternatives, likewise. -/
def len'' : Ctx → Nat := fun
  | .nil => 0
  | .snoc Γ _ => len'' Γ + 1

/-- info: 2 -/
#guard_msgs in
#eval len'' c2

/-! ## Mutual recursion across two members -/

mutual

def cSize (c : Ctx) : Nat :=
  match c with
  | .nil => 1
  | .snoc Γ _ => cSize Γ + 1

def tSize {Γ : Ctx} {h : Ok Γ} (t : Tm Γ h) : Nat :=
  match t with
  | .var Δ _ => cSize Δ
  | .wk _ _ u => tSize u + 1

end

/-- info: 3 -/
#guard_msgs in
#eval cSize c2

/-- info: 3 -/
#guard_msgs in
#eval tSize (Tm.wk c1 o1 (.var c1 o1))

/-! ## Promoted arguments

`Tm`'s indices include a proof, so the view carries the indices before it as
parameters rather than as fields -- a parameter cannot depend on an index --
and drops the constructor fields that pinned them.  This is what Lean's own
`cases` presents too.  The rewrite hides the difference: the fields are still
written, and one given a name is bound on the right-hand side instead, to what
the discriminant's own type says it is. -/

def depth {Γ : Ctx} {h : Ok Γ} (t : Tm Γ h) : Nat :=
  match t with
  | .var _ _ => 0
  | .wk _ _ u => depth u + 1

/-- info: 2 -/
#guard_msgs in
#eval depth (Tm.wk c2 o2 (.wk c2 o2 (.var c2 o2)))

/-- The promoted fields under names, used on the right. -/
def ctxLen {Γ : Ctx} {h : Ok Γ} (t : Tm Γ h) : Nat :=
  match t with
  | .var Δ _ => len Δ
  | .wk Δ _ _ => len Δ + 100

/-- info: 2 -/
#guard_msgs in
#eval ctxLen (Tm.var c2 o2)

/-- info: 102 -/
#guard_msgs in
#eval ctxLen (Tm.wk c2 o2 (.var c2 o2))

/-! ## More than one discriminant -/

def both (a b : Ctx) : Nat :=
  match a, b with
  | .nil, .nil => 0
  | .nil, .snoc _ _ => 1
  | .snoc _ _, .nil => 2
  | .snoc x _, .snoc y _ => len x + len y

/-- info: 2 -/
#guard_msgs in
#eval both c2 c2

/-- info: 1 -/
#guard_msgs in
#eval both .nil c1

/-- A member next to an ordinary type. -/
def mixed (n : Nat) (c : Ctx) : Nat :=
  match n, c with
  | 0, .nil => 0
  | 0, .snoc Γ _ => len Γ
  | _ + 1, x => len x + 100

/-- info: 1 -/
#guard_msgs in
#eval mixed 0 c2

/-- info: 102 -/
#guard_msgs in
#eval mixed 3 c2

/-! ## The shapes a `match` can otherwise take -/

/-- A wildcard alternative alongside a constructor. -/
def isNil' : Ctx → Bool
  | .nil => true
  | _ => false

/-- info: false -/
#guard_msgs in
#eval isNil' c1

/-- `h :` names the equation, and still does. -/
def withEq (c : Ctx) : Nat :=
  match h : c with
  | .nil => 0
  | .snoc Γ _ => len Γ + (by cases h; exact 7)

/-- info: 8 -/
#guard_msgs in
#eval withEq c2

/-- A motive that mentions the discriminant. -/
def okOf (c : Ctx) : PLift (Ok c) :=
  match c with
  | .nil => ⟨.nil⟩
  | .snoc Γ h => ⟨.snoc Γ h⟩

/-- `match` in tactic position is the same elaborator and goes the same way. -/
theorem always_ok (c : Ctx) : Ok c := by
  match c with
  | .nil => exact .nil
  | .snoc Γ h => exact .snoc Γ h

/-! ## Inside a `do` block

A `do` block's `match` is a `do` element and not a term, with an elaborator of
its own, so it takes a second override.  The rewritten `match` goes back to that
elaborator rather than to a term one, which is what keeps everything a `do`
block's `match` is allowed to contain working inside an alternative. -/

def viaDo (c : Ctx) : Option Nat := do
  match c with
  | .nil => none
  | .snoc Γ _ => return len Γ

/-- info: none -/
#guard_msgs in
#eval viaDo .nil

/-- info: some 1 -/
#guard_msgs in
#eval viaDo c2

/-- `return` out of the block, and a mutable variable written in an alternative. -/
def viaDoMut (c : Ctx) : Id Nat := do
  let mut n := 0
  match c with
  | .nil => return 100
  | .snoc Γ _ =>
    n := n + len Γ
    n := n + 1
  return n

/-- info: 100 -/
#guard_msgs in
#eval viaDoMut .nil

/-- info: 2 -/
#guard_msgs in
#eval viaDoMut c2

/-- `continue`, which only means anything to the `for` the `match` is under. -/
def viaDoFor (cs : List Ctx) : Id Nat := do
  let mut n := 0
  for c in cs do
    match c with
    | .nil => continue
    | .snoc Γ _ => n := n + len Γ + 1
  return n

/-- info: 3 -/
#guard_msgs in
#eval viaDoFor [c1, .nil, c2]

/-- A promoted argument under a name, bound in front of the sequence. -/
def viaDoCtxLen {Γ : Ctx} {h : Ok Γ} (t : Tm Γ h) : Id Nat := do
  match t with
  | .var Δ _ => return len Δ
  | .wk Δ _ _ => return len Δ + 100

/-- info: 2 -/
#guard_msgs in
#eval viaDoCtxLen (Tm.var c2 o2)

/-- info: 102 -/
#guard_msgs in
#eval viaDoCtxLen (Tm.wk c2 o2 (.var c2 o2))

/-- A sequence written with braces keeps its elements somewhere else. -/
def viaDoBraces {Γ : Ctx} {h : Ok Γ} (t : Tm Γ h) : Id Nat := do
  match t with
  | .var Δ _ => { return len Δ }
  | .wk Δ _ _ => { return len Δ + 100 }

/-- info: 2 -/
#guard_msgs in
#eval viaDoBraces (Tm.var c2 o2)

/-- A member next to an ordinary type, and `h :` alongside. -/
def viaDoMixed (c : Ctx) (n : Nat) : Id Nat := do
  match h : c, n with
  | .nil, _ => return 0
  | .snoc Γ _, 0 => return len Γ + (by cases h; exact 7)
  | .snoc Γ _, k + 1 => return len Γ + k

/-- info: 8 -/
#guard_msgs in
#eval viaDoMixed c2 0

/-- info: 6 -/
#guard_msgs in
#eval viaDoMixed c2 6

/-! ## Nothing sorried

A view is a plain inductive and `Ctx.view` a plain definition over `Ctx.casesD`,
so a function written through one rests on no more than the block itself does.
`propext` is what well-founded recursion brings in. -/

/-- info: 'MumiTests.Match.isNil' does not depend on any axioms -/
#guard_msgs in
#print axioms isNil

/-- info: 'MumiTests.Match.len' depends on axioms: [propext] -/
#guard_msgs in
#print axioms len

/-- info: 'MumiTests.Match.tSize' depends on axioms: [propext] -/
#guard_msgs in
#print axioms tSize

/-- info: 'MumiTests.Match.ctxLen' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ctxLen

/-- info: 'MumiTests.Match.okOf' does not depend on any axioms -/
#guard_msgs in
#print axioms okOf

/-- info: 'MumiTests.Match.always_ok' does not depend on any axioms -/
#guard_msgs in
#print axioms always_ok

/-- info: 'MumiTests.Match.viaDoMut' depends on axioms: [propext] -/
#guard_msgs in
#print axioms viaDoMut

/-! ## What a view cannot present

A view is one layer deep, so a constructor written inside another pattern is
out of its reach.  Saying so is better than letting the equation compiler
report it, which it would do in terms of the view. -/

/--
error: A constructor of `MumiTests.Match.Ctx` cannot be written inside another pattern. `MumiTests.Match.Ctx` is matched through a view, which presents one constructor and stops, so this one has to be reached by a `match` of its own.
-/
#guard_msgs in
example (c : Ctx) : Nat :=
  match c with
  | .snoc (.snoc Γ _) _ => len Γ
  | _ => 0

/-- The same split, written as the two `match`es it is. -/
def twoDeep (c : Ctx) : Nat :=
  match c with
  | .snoc Γ _ =>
    match Γ with
    | .snoc Δ _ => len Δ + 10
    | .nil => 1
  | .nil => 0

/-- info: 10 -/
#guard_msgs in
#eval twoDeep c2

-- a promoted argument is settled by the discriminant's type, so a pattern that
-- would constrain it rather than name it is not something a view can carry
/--
error: This argument of `MumiTests.Match.Tm.var` is settled by the type of what is being matched rather than by the pattern, so it can be written only as `_`, or as a name to have it under.
-/
#guard_msgs in
example {Γ : Ctx} {h : Ok Γ} (t : Tm Γ h) : Nat :=
  match t with
  | .var .nil _ => 0
  | _ => 1

-- an alternative left out is still an alternative left out, but the equation
-- compiler counts the alternatives it was given, which are the view's: one slot
-- for the member, matched by nothing, and one for the view
/--
error: Missing cases:
_, Ctx.View.nil
-/
#guard_msgs in
example (c : Ctx) : Nat :=
  match c with
  | .snoc Γ _ => len Γ

/-! ## Other blocks

The view comes from the block, not from the shape of the member, so the same
`match` works wherever a block does. -/

/-! ### Parameters -/

namespace Param

mutual
inductive Ctx (α : Type) : Type where
  | nil
  | snoc (Γ : Ctx α) (a : α) (h : Ok α Γ) : Ctx α
inductive Ok (α : Type) : Ctx α → Prop where
  | nil : Ok α .nil
  | snoc (Γ : Ctx α) (a : α) (h : Ok α Γ) : Ok α (.snoc Γ a h)
end

def sum (c : Ctx Nat) : Nat :=
  match c with
  | .nil => 0
  | .snoc Γ a _ => sum Γ + a

/-- info: 3 -/
#guard_msgs in
#eval sum (.snoc (.snoc .nil 1 .nil) 2 (.snoc .nil 1 .nil))

end Param

/-! ### An index that is data rather than a proof

Nothing is promoted here, so every field stays in the pattern. -/

namespace Typed

mutual
inductive Ty : Type where
  | base
  | arr (a b : Ty) : Ty
inductive Ctx : Type where
  | nil
  | snoc (Γ : Ctx) (t : Ty) (h : Ok Γ) : Ctx
inductive Ok : Ctx → Prop where
  | nil : Ok .nil
  | snoc (Γ : Ctx) (t : Ty) (h : Ok Γ) : Ok (.snoc Γ t h)
inductive Tm : Ctx → Ty → Type where
  | var (Γ : Ctx) (t : Ty) : Tm Γ t
  | app (Γ : Ctx) (a b : Ty) (f : Tm Γ (.arr a b)) (x : Tm Γ a) : Tm Γ b
end

def size {Γ : Ctx} {t : Ty} (e : Tm Γ t) : Nat :=
  match e with
  | .var _ _ => 1
  | .app _ _ _ f x => size f + size x

/-- info: 2 -/
#guard_msgs in
#eval size (Tm.app .nil .base .base (.var .nil (.arr .base .base)) (.var .nil .base))

end Typed

/-! ### A member reached through a container -/

namespace Nested

mutual
inductive Ctx : Type where
  | mk (ts : List Tm) : Ctx
inductive Tm : Type where
  | var
  | node (c : Ctx) : Tm
end

def width (c : Ctx) : Nat :=
  match c with
  | .mk ts => ts.length

/-- info: 2 -/
#guard_msgs in
#eval width (.mk [.var, .node (.mk [])])

end Nested

/-! ### Abstract universes -/

namespace Poly

mutual
inductive Ctx : Type u where
  | nil
  | snoc (Γ : Ctx.{u}) (h : Ok Γ) : Ctx
inductive Ok : Ctx.{u} → Prop where
  | nil : Ok (.nil : Ctx.{u})
  | snoc (Γ : Ctx.{u}) (h : Ok Γ) : Ok (.snoc Γ h)
end

def len (c : Ctx.{u}) : Nat :=
  match c with
  | .nil => 0
  | .snoc Γ _ => len Γ + 1

/-- info: 1 -/
#guard_msgs in
#eval len (Ctx.snoc .nil .nil : Ctx.{0})

end Poly

/-! ## Everything else is untouched

The rewrite only looks at a `match` whose discriminant is a member with a view,
and only at one whose alternatives name a constructor of it.  Both of these are
in the same file as the blocks above. -/

def double : Nat → Nat
  | 0 => 1
  | n + 1 => double n * 2

/-- info: 32 -/
#guard_msgs in
#eval double 5

example : double 5 = 32 := rfl

def total : List Nat → Nat
  | [] => 0
  | x :: r => x + total r

/-- info: 6 -/
#guard_msgs in
#eval total [1, 2, 3]

example : total [1, 2, 3] = 6 := rfl

/-- A member as a discriminant, but with no constructor named: nothing to do. -/
def constant (c : Ctx) : Nat :=
  match c with
  | _ => 4

/-- info: 4 -/
#guard_msgs in
#eval constant c2

example : constant c2 = 4 := rfl

end MumiTests.Match
