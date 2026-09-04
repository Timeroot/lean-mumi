import Mumi

/-!
# Induction-induction through `Prop`

`Mumi.IndInd` handles a `mutual` block one of whose members' *arities* mentions
a sibling, provided the dependency runs only through proofs.  Lean rejects every
block in this file outright -- a member's arity names a constant that is not yet
in scope -- so there is nothing here whose behaviour could have changed.

The point of each test is that the *visible* declarations are the ones written,
that both iota rules hold by `rfl`, and that the result computes.

An unindexed block adds no axiom.  An indexed one adds `propext`: building the
recursor inverts a proof of an indexed proposition, and Lean's `cases` unifies
the indices through the `injEq` lemmas, which are proved by `propext`.  It is
in the recursor, not in anything the recursor is used for.
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
info: @Ctx.rec : {motive_1 : Ctx → Sort u_1} →
  {motive_2 : (a : String) → (a_1 : Ctx) → motive_1 a_1 → Fresh a a_1 → Prop} →
    (nil : motive_1 Ctx.nil) →
      (snoc :
          (Γ : Ctx) →
            (x : String) → (a : Fresh x Γ) → (Γ_ih : motive_1 Γ) → motive_2 x Γ Γ_ih a → motive_1 (Γ.snoc x a)) →
        (∀ (x : String), motive_2 x Ctx.nil nil ⋯) →
          (∀ (x y : String) (Γ : Ctx) (h : Fresh y Γ) (a : x ≠ y) (a_1 : Fresh x Γ) (Γ_ih : motive_1 Γ)
              (h_ih : motive_2 y Γ Γ_ih h), motive_2 x Γ Γ_ih a_1 → motive_2 x (Γ.snoc y h) (snoc Γ y h Γ_ih h_ih) ⋯) →
            (t : Ctx) → motive_1 t
-/
#guard_msgs in
#check @Ctx.rec

/-! ### One recursion over the whole block

`Fresh`'s motive takes the value `Ctx`'s motive produced at the context it is
about, and `Ctx.snoc`'s minor gets an induction hypothesis for the proof it
carries.  The two members share their motives and minors, and differ only in
what they are eliminating -- which is what Lean's own recursors for a `mutual`
block do, and is what lets a proof by `Fresh.rec` say something about a function
defined by `Ctx.rec`.
-/

/--
info: @Fresh.rec : ∀ {motive_1 : Ctx → Sort u_1} {motive_2 : (a : String) → (a_1 : Ctx) → motive_1 a_1 → Fresh a a_1 → Prop}
  (nil : motive_1 Ctx.nil)
  (snoc :
    (Γ : Ctx) → (x : String) → (a : Fresh x Γ) → (Γ_ih : motive_1 Γ) → motive_2 x Γ Γ_ih a → motive_1 (Γ.snoc x a))
  (nil_1 : ∀ (x : String), motive_2 x Ctx.nil nil ⋯)
  (snoc_1 :
    ∀ (x y : String) (Γ : Ctx) (h : Fresh y Γ) (a : x ≠ y) (a_1 : Fresh x Γ) (Γ_ih : motive_1 Γ)
      (h_ih : motive_2 y Γ Γ_ih h), motive_2 x Γ Γ_ih a_1 → motive_2 x (Γ.snoc y h) (snoc Γ y h Γ_ih h_ih) ⋯)
  {a : String} {a_1 : Ctx} (h : Fresh a a_1), motive_2 a a_1 (Ctx.rec nil snoc nil_1 snoc_1 a_1) h
-/
#guard_msgs in
#check @Fresh.rec

/-! ### The recursor computes, and both iota rules are definitional -/

/-- The names in a context, and the proof that a fresh name is not among them. -/
def Ctx.names : Ctx → List String :=
  Ctx.rec (motive_1 := fun _ => List String) (motive_2 := fun x _ ns _ => x ∉ ns)
    [] (fun _ x _ ih _ => x :: ih)
    (fun _ => by simp)
    (fun _ _ _ _ hne _ _ _ ih => by simp only [List.mem_cons, not_or]; exact ⟨hne, ih⟩)

theorem Fresh.not_mem {x : String} {Γ : Ctx} (h : Fresh x Γ) : x ∉ Γ.names :=
  Fresh.rec (motive_1 := fun _ => List String) (motive_2 := fun x _ ns _ => x ∉ ns)
    [] (fun _ x _ ih _ => x :: ih)
    (fun _ => by simp)
    (fun _ _ _ _ hne _ _ _ ih => by simp only [List.mem_cons, not_or]; exact ⟨hne, ih⟩)
    h

/-- A motive for `Fresh` no one cares about, for a recursion that only computes. -/
abbrev Ctx.trivialMotive {C : Ctx → Sort u} : (x : String) → (Γ : Ctx) → C Γ → Fresh x Γ → Prop :=
  fun _ _ _ _ => True

def Ctx.length (Γ : Ctx) : Nat :=
  Ctx.rec (motive_1 := fun _ => Nat) (motive_2 := Ctx.trivialMotive)
    0 (fun _ _ _ ih _ => ih + 1)
    (fun _ => trivial) (fun _ _ _ _ _ _ _ _ _ => trivial) Γ

section
variable {C : Ctx → Sort u} {D : (x : String) → (Γ : Ctx) → C Γ → Fresh x Γ → Prop}
  (n : C .nil)
  (s : (Γ : Ctx) → (x : String) → (h : Fresh x Γ) → (ih : C Γ) → D x Γ ih h → C (.snoc Γ x h))
  (dn : ∀ x, D x .nil n (.nil x))
  (ds : ∀ (x y : String) (Γ : Ctx) (h : Fresh y Γ) (hne : x ≠ y) (h' : Fresh x Γ) (ih : C Γ)
    (hih : D y Γ ih h), D x Γ ih h' → D x (.snoc Γ y h) (s Γ y h ih hih) (.snoc x y Γ h hne h'))

example : Ctx.rec (motive_1 := C) (motive_2 := D) n s dn ds .nil = n := rfl

example (Γ : Ctx) (x : String) (h : Fresh x Γ) :
    Ctx.rec (motive_1 := C) (motive_2 := D) n s dn ds (.snoc Γ x h)
      = s Γ x h (Ctx.rec (motive_1 := C) (motive_2 := D) n s dn ds Γ)
          (Fresh.rec (motive_1 := C) (motive_2 := D) n s dn ds h) := rfl
end

/-- A closed term, built through the `Fresh` obligations. -/
def ex : Ctx :=
  .snoc (.snoc .nil "x" (.nil "x")) "y"
    (.snoc "y" "x" .nil (.nil "x") (by decide) (.nil "y"))

/-- info: 2 -/
#guard_msgs in
#eval ex.length

example : ex.length = 2 := rfl

/-- info: 'Ctx.rec' does not depend on any axioms -/
#guard_msgs in
#print axioms Ctx.rec

/-- info: 'ex' does not depend on any axioms -/
#guard_msgs in
#print axioms ex

/-- info: 'Ctx.length' does not depend on any axioms -/
#guard_msgs in
#print axioms Ctx.length

/-! ### `induction ... using` is the way to reason about it

The constructors are `def`s, so `match` does not see them; a bare `cases` does,
through the eliminator the next section pins.  The recursor's minor premises are
named after the constructors, so `induction using` reads the way it would for a
real inductive; a name two members share is numbered, again as it would be for a
Lean `mutual`.  The motives the goal does not fix have to be given, since one
recursor serves the whole block.

The `Prop` members' recursors are for term mode, not for `induction using`:
`getElimInfo` reads the motive's arguments up to the first that is not a local,
and a predicate motive's third argument is the *value* the data motive produced,
which never is one.  `Fresh.not_mem` above is the term-mode form.
-/

example (Γ : Ctx) : 0 ≤ Γ.length := by
  induction Γ using Ctx.rec (motive_2 := Ctx.trivialMotive) with
  | nil => simp [Ctx.length]
  | snoc Γ x h ih ih' => simp
  | nil_1 => trivial
  | snoc_1 => intros; trivial

/-! ### `@[elab_as_elim]`

A data recursor is tagged, so a term-mode application generalises its motive
over the major premise instead of taking whatever unification pins down from the
expected type.  Written `@Ctx.rec`, which bypasses that, the example below infers
`fun _ => Ctx.nil = Γ` and neither the minors nor the result typecheck.

A predicate recursor is not tagged: its motive is applied to the value the data
motive computed, which is not a target to abstract over, so eliminator
elaboration has nothing to generalise.  This is the same limit that keeps it out
of `induction ... using`.
-/

example (Γ : Ctx) : Γ.names = Γ.names :=
  Ctx.rec (motive_2 := Ctx.trivialMotive) rfl (fun _ _ _ _ _ => rfl)
    (fun _ => trivial) (fun _ _ _ _ _ _ _ _ _ => trivial) Γ

open Lean Elab Term in
/-- info: Ctx.rec true, Fresh.rec false -/
#guard_msgs in
run_meta do
  let env ← getEnv
  logInfo s!"Ctx.rec {elabAsElim.hasTag env `Ctx.rec}, \
    Fresh.rec {elabAsElim.hasTag env `Fresh.rec}"

/-! ### A bare `cases`

A data member is a subtype of its pre-type, so what `cases` finds by unfolding
it is `Subtype.mk`, whose two arguments are a pre-term and a proof rather than
the constructor's own.  `Ctx.casesD` is registered instead: the one-motive
recursor with the induction hypotheses dropped, which is exactly what a case
split is entitled to.  So the `with` clause names the constructors that were
written, and binds their fields.

A `Prop` member needs the same, for a different reason.  It is a real inductive
underneath, but its index is a data member, and splitting a `Fresh x Γ` whose
`Γ` is a variable asks the tactic to solve `Γ.1 = Ctx._pre.nil` -- the subtype
showing through again.  `Fresh.casesP` has the constructors as its cases
already, so nothing has to be unified through the encoding.
-/

/--
info: @Ctx.casesD : {motive : Ctx → Sort u_1} →
  motive Ctx.nil → ((Γ : Ctx) → (x : String) → (a : Fresh x Γ) → motive (Γ.snoc x a)) → (t : Ctx) → motive t
-/
#guard_msgs in
#check @Ctx.casesD

/--
info: @Fresh.casesP : ∀ {motive : (a : String) → (a_1 : Ctx) → Fresh a a_1 → Prop},
  (∀ (x : String), motive x Ctx.nil ⋯) →
    (∀ (x y : String) (Γ : Ctx) (h : Fresh y Γ) (a : x ≠ y) (a_1 : Fresh x Γ), motive x (Γ.snoc y h) ⋯) →
      ∀ {a : String} {a_1 : Ctx} (h : Fresh a a_1), motive a a_1 h
-/
#guard_msgs in
#check @Fresh.casesP

example (Γ : Ctx) : Γ = Γ := by
  cases Γ with
  | nil => rfl
  | snoc Δ x h => rfl

example (x : String) (Γ : Ctx) (h : Fresh x Γ) : h = h := by
  cases h with
  | nil y => rfl
  | snoc y z Δ hz hne hy => rfl

/-- The head of a context, by a case split rather than a recursion. -/
def Ctx.head? (Γ : Ctx) : Option String :=
  Ctx.casesD (motive := fun _ => Option String) none (fun _ x _ => some x) Γ

/-- info: some "y" -/
#guard_msgs in
#eval (Ctx.nil.snoc "y" (.nil "y")).head?

example : (Ctx.nil.snoc "y" (.nil "y")).head? = some "y" := rfl

example : Ctx.nil.head? = none := rfl

/-- info: 'Ctx.head?' does not depend on any axioms -/
#guard_msgs in
#print axioms Ctx.head?

/-! ## Several `Prop` members

Any number of propositions may hang off one data member; each gets a motive of
its own, and a data constructor's minor premise gets one induction hypothesis
per erased field.
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

/--
info: @Tm.rec : {motive_1 : Tm → Sort u_1} →
  {motive_2 : (a : Tm) → motive_1 a → Ok a → Prop} →
    {motive_3 : (a : Tm) → motive_1 a → Closed a → Prop} →
      (var : (a : Nat) → motive_1 (Tm.var a)) →
        ((f a : Tm) →
            (a_1 : Ok f) →
              (a_2 : Ok a) →
                (f_ih : motive_1 f) →
                  (a_ih : motive_1 a) → motive_2 f f_ih a_1 → motive_2 a a_ih a_2 → motive_1 (f.app a a_1 a_2)) →
          (lam : (b : Tm) → (a : Closed b) → (b_ih : motive_1 b) → motive_3 b b_ih a → motive_1 (b.lam a)) →
            (∀ (n : Nat), motive_2 (Tm.var n) (var n) ⋯) →
              (∀ (b : Tm) (h : Closed b) (b_ih : motive_1 b) (h_ih : motive_3 b b_ih h),
                  motive_2 (b.lam h) (lam b h b_ih h_ih) ⋯) →
                (∀ (n : Nat), motive_3 (Tm.var n) (var n) ⋯) →
                  (∀ (b : Tm) (h : Closed b) (b_ih : motive_1 b) (h_ih : motive_3 b b_ih h),
                      motive_3 (b.lam h) (lam b h b_ih h_ih) ⋯) →
                    (t : Tm) → motive_1 t
-/
#guard_msgs in
#check @Tm.rec

/-- A recursion that only computes still has to say what the propositions mean. -/
abbrev Tm.trivialOk {C : Tm → Sort u} : (t : Tm) → C t → Ok t → Prop := fun _ _ _ => True

abbrev Tm.trivialClosed {C : Tm → Sort u} : (t : Tm) → C t → Closed t → Prop := fun _ _ _ => True

def Tm.size (t : Tm) : Nat :=
  Tm.rec (motive_1 := fun _ => Nat) (motive_2 := Tm.trivialOk) (motive_3 := Tm.trivialClosed)
    (fun _ => 1) (fun _ _ _ _ i j _ _ => i + j + 1) (fun _ _ i _ => i + 1)
    (fun _ => trivial) (fun _ _ _ _ => trivial)
    (fun _ => trivial) (fun _ _ _ _ => trivial) t

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

-- the motives come in block order, so `Ok3`'s is second even though `Ok3` is
-- written first: a predicate's motive has to follow the data motive it mentions
/--
info: @Vec3.rec : {motive_1 : Vec3 → Sort u_1} →
  {motive_2 : (a : Vec3) → motive_1 a → Ok3 a → Prop} →
    (nil : motive_1 Vec3.nil) →
      ((v : Vec3) → (a : Ok3 v) → (v_ih : motive_1 v) → motive_2 v v_ih a → motive_1 (v.cons a)) →
        motive_2 Vec3.nil nil Ok3.nil → (t : Vec3) → motive_1 t
-/
#guard_msgs in
#check @Vec3.rec

def Vec3.size (v : Vec3) : Nat :=
  Vec3.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ _ => True)
    0 (fun _ _ ih _ => ih + 1) trivial v

/-- info: 1 -/
#guard_msgs in
#eval Vec3.size (.cons .nil .nil)

example : Vec3.size (.cons .nil .nil) = 1 := rfl

/-! ## Indices

Both members are indexed, and the `Prop` member is indexed by the data member at
one of its own indices.
-/

mutual
inductive IVec : Nat → Type where
  | nil : IVec 0
  | cons : (n : Nat) → (v : IVec n) → (x : Nat) → IFresh x n v → IVec (n + 1)
inductive IFresh : Nat → (n : Nat) → IVec n → Prop where
  | nil : (x : Nat) → IFresh x 0 .nil
  | cons : (x y n : Nat) → (v : IVec n) → (h : IFresh y n v) → x ≠ y → IFresh x n v →
      IFresh x (n + 1) (.cons n v y h)
end

/-- info: IVec.cons : (n : Nat) → (v : IVec n) → (x : Nat) → IFresh x n v → IVec (n + 1) -/
#guard_msgs in
#check @IVec.cons

/--
info: IFresh.cons : ∀ (x y n : Nat) (v : IVec n) (h : IFresh y n v),
  x ≠ y → IFresh x n v → IFresh x (n + 1) (IVec.cons n v y h)
-/
#guard_msgs in
#check @IFresh.cons

/--
info: @IVec.rec : {motive_1 : (a : Nat) → IVec a → Sort u_1} →
  {motive_2 : (a n : Nat) → (a_1 : IVec n) → motive_1 n a_1 → IFresh a n a_1 → Prop} →
    (nil : motive_1 0 IVec.nil) →
      (cons :
          (n : Nat) →
            (v : IVec n) →
              (x : Nat) →
                (a : IFresh x n v) →
                  (v_ih : motive_1 n v) → motive_2 x n v v_ih a → motive_1 (n + 1) (IVec.cons n v x a)) →
        (∀ (x : Nat), motive_2 x 0 IVec.nil nil ⋯) →
          (∀ (x y n : Nat) (v : IVec n) (h : IFresh y n v) (a : x ≠ y) (a_1 : IFresh x n v) (v_ih : motive_1 n v)
              (h_ih : motive_2 y n v v_ih h),
              motive_2 x n v v_ih a_1 → motive_2 x (n + 1) (IVec.cons n v y h) (cons n v y h v_ih h_ih) ⋯) →
            {a : Nat} → (t : IVec a) → motive_1 a t
-/
#guard_msgs in
#check @IVec.rec

/-- `IFresh`'s own index `x` leads the list, then `IVec`'s. -/
abbrev IVec.trivialFresh {C : (n : Nat) → IVec n → Sort u} :
    (x n : Nat) → (v : IVec n) → C n v → IFresh x n v → Prop :=
  fun _ _ _ _ _ => True

def IVec.sum : (n : Nat) → IVec n → Nat :=
  fun _ v => IVec.rec (motive_1 := fun _ _ => Nat) (motive_2 := IVec.trivialFresh)
    0 (fun _ _ x _ ih _ => ih + x)
    (fun _ => trivial) (fun _ _ _ _ _ _ _ _ _ _ => trivial) v

def exVec : IVec 1 := .cons 0 .nil 5 (.nil 5)

/-- info: 5 -/
#guard_msgs in
#eval exVec.sum

example : IVec.sum 1 exVec = 5 := rfl

section
variable {C : (n : Nat) → IVec n → Sort u}
  {D : (x n : Nat) → (v : IVec n) → C n v → IFresh x n v → Prop}
  (nil : C 0 .nil)
  (cons : (n : Nat) → (v : IVec n) → (x : Nat) → (h : IFresh x n v) → (ih : C n v) →
    D x n v ih h → C (n + 1) (.cons n v x h))
  (dnil : ∀ x, D x 0 .nil nil (.nil x))
  (dcons : ∀ (x y n : Nat) (v : IVec n) (h : IFresh y n v) (hne : x ≠ y) (h' : IFresh x n v)
    (ih : C n v) (hih : D y n v ih h), D x n v ih h' →
    D x (n + 1) (.cons n v y h) (cons n v y h ih hih) (.cons x y n v h hne h'))

example (n : Nat) (v : IVec n) (x : Nat) (h : IFresh x n v) :
    IVec.rec nil cons dnil dcons (IVec.cons n v x h)
      = cons n v x h (IVec.rec nil cons dnil dcons v)
          (IFresh.rec nil cons dnil dcons h) := rfl
end

-- indexed, so the recursor carries `propext` and everything built from it does too
/-- info: 'IVec.rec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms IVec.rec

/-- info: 'IVec.sum' depends on axioms: [propext] -/
#guard_msgs in
#print axioms IVec.sum

-- the indices are generalised along with the major premise
example (n : Nat) (v : IVec n) : 0 ≤ IVec.sum n v := by
  induction v using IVec.rec (motive_2 := IVec.trivialFresh) with
  | nil => exact Nat.zero_le _
  | cons n v x h ih ihh => exact Nat.zero_le _
  | nil_1 => intros; trivial
  | cons_1 => intros; trivial

/-! ### An index of the `Prop` member's own that moves under the recursion

`IFresh` above carries an index `x`, but every recursive occurrence of `IFresh`
keeps it.  Here `Closed`'s own index is a binder depth, and the constructor for
`lam` recurses at `k + 1`: the minor premise is handed a hypothesis at a
*different* index from the one it must produce.  The bundle the recursion
carries is over the data member alone, so the `Prop` motive has to stay
quantified over its own indices -- which is what lets the same bundle answer at
`k` and at `k + 1`.

The pair below is the point of the whole construction.  `Tm.bump` is a map, and
`Closed.bump` says the map takes a term closed at `k` to one closed at `k + 1`;
neither can be had without the other, because the proof is about the term the
map produced.  Both come out of the one recursion, at the same motives.
-/

namespace Bump

mutual
inductive Tm : Type where
  | var : Nat → Tm
  | app : Tm → Tm → Tm
  | lam : Tm → Tm
inductive Closed : Nat → Tm → Prop where
  | var : (n k : Nat) → n < k → Closed k (.var n)
  | app : (k : Nat) → (s t : Tm) → Closed k s → Closed k t → Closed k (.app s t)
  | lam : (k : Nat) → (t : Tm) → Closed (k + 1) t → Closed k (.lam t)
end

/--
info: @Tm.rec : {motive_1 : Tm → Sort u_1} →
  {motive_2 : (a : Nat) → (a_1 : Tm) → motive_1 a_1 → Closed a a_1 → Prop} →
    (var : (a : Nat) → motive_1 (Tm.var a)) →
      (app : (a a_1 : Tm) → motive_1 a → motive_1 a_1 → motive_1 (a.app a_1)) →
        (lam : (a : Tm) → motive_1 a → motive_1 a.lam) →
          (∀ (n k : Nat) (a : n < k), motive_2 k (Tm.var n) (var n) ⋯) →
            (∀ (k : Nat) (s t : Tm) (a : Closed k s) (a_1 : Closed k t) (s_ih : motive_1 s) (t_ih : motive_1 t),
                motive_2 k s s_ih a → motive_2 k t t_ih a_1 → motive_2 k (s.app t) (app s t s_ih t_ih) ⋯) →
              (∀ (k : Nat) (t : Tm) (a : Closed (k + 1) t) (t_ih : motive_1 t),
                  motive_2 (k + 1) t t_ih a → motive_2 k t.lam (lam t t_ih) ⋯) →
                (t : Tm) → motive_1 t
-/
#guard_msgs in
#check @Tm.rec

/--
info: @Closed.rec : ∀ {motive_1 : Tm → Sort u_1} {motive_2 : (a : Nat) → (a_1 : Tm) → motive_1 a_1 → Closed a a_1 → Prop}
  (var : (a : Nat) → motive_1 (Tm.var a)) (app : (a a_1 : Tm) → motive_1 a → motive_1 a_1 → motive_1 (a.app a_1))
  (lam : (a : Tm) → motive_1 a → motive_1 a.lam) (var_1 : ∀ (n k : Nat) (a : n < k), motive_2 k (Tm.var n) (var n) ⋯)
  (app_1 :
    ∀ (k : Nat) (s t : Tm) (a : Closed k s) (a_1 : Closed k t) (s_ih : motive_1 s) (t_ih : motive_1 t),
      motive_2 k s s_ih a → motive_2 k t t_ih a_1 → motive_2 k (s.app t) (app s t s_ih t_ih) ⋯)
  (lam_1 :
    ∀ (k : Nat) (t : Tm) (a : Closed (k + 1) t) (t_ih : motive_1 t),
      motive_2 (k + 1) t t_ih a → motive_2 k t.lam (lam t t_ih) ⋯)
  {a : Nat} {a_1 : Tm} (h : Closed a a_1), motive_2 a a_1 (Tm.rec var app lam var_1 app_1 lam_1 a_1) h
-/
#guard_msgs in
#check @Closed.rec

/-- Add one to every variable. -/
def Tm.bump (t : Tm) : Tm :=
  Tm.rec (motive_1 := fun _ => Tm) (motive_2 := fun k _ t' _ => Closed (k + 1) t')
    (fun n => .var (n + 1))
    (fun _ _ s' t' => .app s' t')
    (fun _ t' => .lam t')
    (fun n k h => .var (n + 1) (k + 1) (by omega))
    (fun k _ _ _ _ s' t' hs ht => .app (k + 1) s' t' hs ht)
    (fun k _ _ t' ht => .lam (k + 1) t' ht)
    t

-- the statement only typechecks because the value `Closed.rec` computes at the
-- data motive is the one `Tm.bump` was defined to be
theorem Closed.bump {k : Nat} {t : Tm} (h : Closed k t) : Closed (k + 1) t.bump :=
  Closed.rec (motive_1 := fun _ => Tm) (motive_2 := fun k _ t' _ => Closed (k + 1) t')
    (fun n => .var (n + 1))
    (fun _ _ s' t' => .app s' t')
    (fun _ t' => .lam t')
    (fun n k h => .var (n + 1) (k + 1) (by omega))
    (fun k _ _ _ _ s' t' hs ht => .app (k + 1) s' t' hs ht)
    (fun k _ _ t' ht => .lam (k + 1) t' ht)
    h

example : (Tm.lam (.app (.var 0) (.var 3))).bump = Tm.lam (.app (.var 1) (.var 4)) := rfl

/-- info: 'Bump.Tm.bump' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Tm.bump

/-- info: 'Bump.Closed.bump' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Closed.bump

end Bump

/-! ### A data member at `Sort u`, with a `Prop` member beside it

The data member is declared over a `Sort` parameter rather than a `Type` one,
so it lands at `max 1 u` and the block is heterogeneous whatever `u` is.  The
`Prop` member is free-standing -- no data member is indexed by it -- so there is
no bundle to build and `C` keeps a recursor with a single motive, the one Lean
would have given it had the universes lined up.
-/

mutual
inductive SortC (α : Sort u) : Sort (max 1 u) where
  | nil
  | ext : SortC α → α → SortP α → SortC α
inductive SortP (α : Sort u) : Prop where
  | mk
end

/-- info: SortC : Sort u_1 → Sort (max 1 u_1) -/
#guard_msgs in
#check @SortC

/-- info: SortP : Sort u_1 → Prop -/
#guard_msgs in
#check @SortP

/-- info: @SortC.ext : {α : Sort u_1} → SortC α → α → SortP α → SortC α -/
#guard_msgs in
#check @SortC.ext

/--
info: @SortC.rec : {α : Sort u_2} →
  {motive : SortC α → Sort u_1} →
    motive SortC.nil →
      ((a : SortC α) → (a_1 : α) → (a_2 : SortP α) → motive a → motive (a.ext a_1 a_2)) → (t : SortC α) → motive t
-/
#guard_msgs in
#check @SortC.rec

-- `α` may be a proposition, and then so is every field of `ext` but the first
example (p : Prop) (h : p) : SortC p := .ext .nil h .mk

/-! ## Several data members

The data members become one mutual pre-block, so each of their recursors takes
one motive per data member and one minor premise per constructor of any of them.

`Wf` is indexed by *two* data members, and a predicate's motive is carried in
the recursion on the one data member it is indexed by -- there is no one member
to hang this on.  So this block keeps the split recursors: a data recursor with
no predicate motives, and a `Prop` recursor of its own.  `set_option
trace.Mumi.indind true` says so while the block elaborates.  The consolation is
that `Wf.rec` is then free to eliminate into `Sort u`, which a joint recursor
could not offer.
-/

mutual
inductive Ctx2 : Type where
  | nil : Ctx2
  | snoc : (Γ : Ctx2) → (t : Ty) → Wf Γ t → Ctx2
inductive Ty : Type where
  | base : Ty
  | arr : (a b : Ty) → Ty
inductive Wf : Ctx2 → Ty → Prop where
  | base : (Γ : Ctx2) → Wf Γ .base
end

/--
info: @Ctx2.rec : {motive_1 : Ctx2 → Sort u_1} →
  {motive_2 : Ty → Sort u_1} →
    motive_1 Ctx2.nil →
      ((Γ : Ctx2) → (t : Ty) → (a : Wf Γ t) → motive_1 Γ → motive_2 t → motive_1 (Γ.snoc t a)) →
        motive_2 Ty.base → ((a b : Ty) → motive_2 a → motive_2 b → motive_2 (a.arr b)) → (t : Ctx2) → motive_1 t
-/
#guard_msgs in
#check @Ctx2.rec

/--
info: @Ty.rec : {motive_1 : Ctx2 → Sort u_1} →
  {motive_2 : Ty → Sort u_1} →
    motive_1 Ctx2.nil →
      ((Γ : Ctx2) → (t : Ty) → (a : Wf Γ t) → motive_1 Γ → motive_2 t → motive_1 (Γ.snoc t a)) →
        motive_2 Ty.base → ((a b : Ty) → motive_2 a → motive_2 b → motive_2 (a.arr b)) → (t : Ty) → motive_2 t
-/
#guard_msgs in
#check @Ty.rec

def Ctx2.length (Γ : Ctx2) : Nat :=
  Ctx2.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat)
    0 (fun _ _ _ ih _ => ih + 1) 1 (fun _ _ i j => i + j + 1) Γ

def Ty.size (t : Ty) : Nat :=
  Ty.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat)
    0 (fun _ _ _ ih _ => ih + 1) 1 (fun _ _ i j => i + j + 1) t

def exCtx2 : Ctx2 := .snoc .nil .base (.base .nil)

/-- info: 1 -/
#guard_msgs in
#eval exCtx2.length

/-- info: 3 -/
#guard_msgs in
#eval (Ty.arr .base .base).size

example : exCtx2.length = 1 := rfl

/-- info: 'Ctx2.length' does not depend on any axioms -/
#guard_msgs in
#print axioms Ctx2.length

/-! ## Data members in different universes

The data members end up in the erased pre-block, and a mutual inductive's
members have to share a universe -- but that is the rule `Mumi.Lowering` exists
to lift, so the pre-block goes to it rather than straight to the kernel.
Erasure takes out the dependency of one member's arity on another; the lowering
takes out the universe difference in what erasure left behind.  Neither pass has
to know anything about the other's problem.

`HFresh`'s arity mentions `HCtx`, so this block is induction-inductive; `HBig`
sits at `Type 1` beside `HCtx` at `Type`, so it is heterogeneous as well.
-/

mutual
inductive HCtx : Type where
  | nil : HCtx
  | snoc : (Γ : HCtx) → (x : String) → HFresh x Γ → HCtx
inductive HBig : Type 1 where
  | of : Type → HBig
  | ctx : HCtx → HBig
inductive HFresh : String → HCtx → Prop where
  | nil : HFresh x .nil
  | snoc : HFresh x Γ → x ≠ y → (h : HFresh y Γ) → HFresh x (.snoc Γ y h)
end

/-- info: HCtx.snoc : (Γ : HCtx) → (x : String) → HFresh x Γ → HCtx -/
#guard_msgs in
#check @HCtx.snoc

/-- info: HBig.ctx : HCtx → HBig -/
#guard_msgs in
#check @HBig.ctx

/-! Still one recursion over the whole block: the two data motives at a common
eliminated universe, and the `Prop` one where it belongs. -/

/--
info: @HCtx.rec : {motive_1 : HCtx → Sort u_1} →
  {motive_2 : HBig → Sort u_1} →
    {motive_3 : (a : String) → (a_1 : HCtx) → motive_1 a_1 → HFresh a a_1 → Prop} →
      (nil : motive_1 HCtx.nil) →
        (snoc :
            (Γ : HCtx) →
              (x : String) → (a : HFresh x Γ) → (Γ_ih : motive_1 Γ) → motive_3 x Γ Γ_ih a → motive_1 (Γ.snoc x a)) →
          ((a : Type) → motive_2 (HBig.of a)) →
            ((a : HCtx) → motive_1 a → motive_2 (HBig.ctx a)) →
              (∀ {x : String}, motive_3 x HCtx.nil nil ⋯) →
                (∀ {x : String} {Γ : HCtx} {y : String} (a : HFresh x Γ) (a_1 : x ≠ y) (h : HFresh y Γ)
                    (Γ_ih : motive_1 Γ),
                    motive_3 x Γ Γ_ih a →
                      ∀ (h_ih : motive_3 y Γ Γ_ih h), motive_3 x (Γ.snoc y h) (snoc Γ y h Γ_ih h_ih) ⋯) →
                  (t : HCtx) → motive_1 t
-/
#guard_msgs in
#check @HCtx.rec

/-! And it computes.  `X._wf` recurses with the lowered pre-block's `mutualRec`,
which is a definition rather than a recursor the kernel knows; it unfolds where
the kernel's own would have reduced, so iota still holds by `rfl`. -/

def HCtx.size (Γ : HCtx) : Nat :=
  HCtx.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat)
    (motive_3 := fun _ _ _ _ => True)
    0 (fun _ _ _ ih _ => ih + 1) (fun _ => 0) (fun _ ih => ih)
    trivial (fun _ _ _ _ _ _ => trivial) Γ

def HBig.size (B : HBig) : Nat :=
  HBig.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat)
    (motive_3 := fun _ _ _ _ => True)
    0 (fun _ _ _ ih _ => ih + 1) (fun _ => 0) (fun _ ih => ih)
    trivial (fun _ _ _ _ _ _ => trivial) B

example : HCtx.size .nil = 0 := rfl
example : HCtx.size (.snoc .nil "x" .nil) = 1 := rfl
example : HCtx.size (.snoc (.snoc .nil "x" .nil) "y" (.snoc .nil (by simp) .nil)) = 2 := rfl

example : HBig.size (.of Nat) = 0 := rfl
example : HBig.size (.ctx (.snoc .nil "x" .nil)) = 1 := rfl

/-- info: 2 -/
#guard_msgs in
#eval HCtx.size (.snoc (.snoc .nil "x" .nil) "y" (.snoc .nil (by simp) .nil))

/-- info: 1 -/
#guard_msgs in
#eval HBig.size (.ctx (.snoc .nil "x" .nil))

/-! ### Three of them, at three universes

Nothing about the composition counts to two: the lowering emits one ordinary
block per component of the pre-block, in topological order, however many that
comes to. -/

mutual
inductive U3a : Type where
  | nil : U3a
  | snoc : (Γ : U3a) → U3ok Γ → U3a
inductive U3b : Type 1 where
  | of : Type → U3b
  | c : U3a → U3b
inductive U3c : Type 2 where
  | of : Type 1 → U3c
  | c : U3b → U3c
inductive U3ok : U3a → Prop where
  | nil : U3ok .nil
end

/-- info: U3a.snoc : (Γ : U3a) → U3ok Γ → U3a -/
#guard_msgs in
#check @U3a.snoc

/-- info: U3c.c : U3b → U3c -/
#guard_msgs in
#check @U3c.c

/-! ### With a parameter, and universe-polymorphic

`UPBig` is one universe above `UPCtx` whatever `v` turns out to be, so the two
disagree symbolically rather than at a literal. -/

section
universe v

mutual
inductive UPCtx (α : Type v) : Type v where
  | nil : UPCtx α
  | snoc : (Γ : UPCtx α) → (a : α) → UPFresh α a Γ → UPCtx α
inductive UPBig (α : Type v) : Type (v + 1) where
  | of : Type v → UPBig α
  | c : UPCtx α → UPBig α
inductive UPFresh (α : Type v) : α → UPCtx α → Prop where
  | nil : UPFresh α a .nil
end
end

/-- info: @UPCtx.snoc : {α : Type u_1} → (Γ : UPCtx α) → (a : α) → UPFresh α a Γ → UPCtx α -/
#guard_msgs in
#check @UPCtx.snoc

/-- info: @UPBig.c : {α : Type u_1} → UPCtx α → UPBig α -/
#guard_msgs in
#check @UPBig.c

def UPCtx.len {α : Type} (Γ : UPCtx α) : Nat :=
  UPCtx.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat)
    (motive_3 := fun _ _ _ _ => True)
    0 (fun _ _ _ ih _ => ih + 1) (fun _ => 0) (fun _ ih => ih)
    trivial Γ

example : (UPCtx.nil (α := Nat)).len = 0 := rfl
example : (UPCtx.snoc (UPCtx.nil (α := Nat)) 3 .nil).len = 1 := rfl

/-! ### Indices on the data members, and a proposition over the bigger one -/

mutual
inductive UIVec : Nat → Type where
  | nil : UIVec 0
  | cons : (n : Nat) → (v : UIVec n) → UIok n v → UIVec (n + 1)
inductive UIBig : Type 1 where
  | of : Type → UIBig
  | c : (n : Nat) → UIVec n → UIBig
inductive UIok : (n : Nat) → UIVec n → Prop where
  | nil : UIok 0 .nil
end

/-- info: UIVec.cons : (n : Nat) → (v : UIVec n) → UIok n v → UIVec (n + 1) -/
#guard_msgs in
#check @UIVec.cons

mutual
inductive UBSmall : Type 2 where
  | nil : UBSmall
  | wrap : (b : UBBig) → UBok b → UBSmall
inductive UBBig : Type 1 where
  | of : Type → UBBig
inductive UBok : UBBig → Prop where
  | of : UBok (.of α)
end

/-- info: UBSmall.wrap : (b : UBBig) → UBok b → UBSmall -/
#guard_msgs in
#check @UBSmall.wrap

/-! ### A nesting as well

All three restrictions at once: the arity dependency erasure lifts, the
universe difference the lowering lifts, and a `Wrap UNCtx` the kernel would
have had to denest.  The constructor still reads the way it was written. -/

inductive UWrap (α : Type u) : Type u where
  | mk : α → UWrap α

mutual
inductive UNCtx : Type where
  | nil : UNCtx
  | snoc : (w : UWrap UNCtx) → (Γ : UNCtx) → UNok Γ → UNCtx
inductive UNBig : Type 1 where
  | of : Type → UNBig
  | c : UNCtx → UNBig
inductive UNok : UNCtx → Prop where
  | nil : UNok .nil
end

/-- info: UNCtx.snoc : UWrap UNCtx → (Γ : UNCtx) → UNok Γ → UNCtx -/
#guard_msgs in
#check @UNCtx.snoc

/-! ### `deriving`, on top of all that -/

mutual
inductive UDCtx : Type where
  | nil : UDCtx
  | snoc : (Γ : UDCtx) → UDok Γ → UDCtx
  deriving DecidableEq, Repr
inductive UDBig : Type 1 where
  | of : Type → UDBig
  | c : UDCtx → UDBig
inductive UDok : UDCtx → Prop where
  | nil : UDok .nil
end

example : DecidableEq UDCtx := inferInstance

/-! ### What the composition does not buy

Lifting the same-universe rule for the *members* leaves the rules underneath
it standing.  Two data members that recurse into each other have to agree
anyway -- an edge puts one universe at or below the other, so a cycle makes
them equal -- and the lowering says so rather than pretending otherwise. -/

/--
error: Invalid universe level in constructor `UCyA.b`: Parameter has type
  UCyB
at universe level
  2
which is not less than or equal to the inductive type's resulting universe level
  1

Hint: The data members `UCyA` and `UCyB` live in different universes, `Type` and `Type 1`.  Lowering the erased pre-block into ordinary inductives is what lifts the kernel's same-universe rule, and here it did not go through:
  (kernel) mutually inductive types must live in the same universe

Note: What the lowering lifts is the rule that the *members* of a mutual block agree about their universe.  The two rules underneath it stand: members that recurse into one another have to agree anyway -- an edge puts one universe at or below the other, so a cycle makes them equal -- and a field still has to fit inside the member it belongs to.  `X._pre` above is the erased form of `X`
-/
#guard_msgs in
mutual
inductive UCyA : Type where
  | nil : UCyA
  | b : UCyB → UCyOk → UCyA
inductive UCyB : Type 1 where
  | of : Type → UCyB
  | a : UCyA → UCyB
inductive UCyOk : Prop where
  | mk : UCyOk
end

/-! ### The two members the arity runs between are the two that disagree

Everywhere above, the arity dependency is at a `Prop` member and the universe
difference is between two data members that never mention one another.  Here
they are the same pair: `UDDTy` is indexed by `UDDCtx` *and* lives above it.
Erasure takes out the index, the lowering takes out the difference, and neither
has any of the other's work to do.

Nothing may come back the other way, though.  `UDDCtx` has no `UDDTy` field, so
there is no cycle to force the two universes together. -/

section
universe v

mutual
inductive UDDCtx : Type where
  | nil : UDDCtx
  | more : (Γ : UDDCtx) → UDDCtx
inductive UDDTy : UDDCtx → Type (v + 1) where
  | base : (Γ : UDDCtx) → UDDTy Γ
  | of : Type v → UDDTy Γ
end
end

/-- info: @UDDTy.of : {Γ : UDDCtx} → Type u_1 → UDDTy Γ -/
#guard_msgs in
#check @UDDTy.of

/--
info: @UDDCtx.rec : {motive_1 : UDDCtx → Sort u_1} →
  {motive_2 : (a : UDDCtx) → UDDTy a → Sort u_1} →
    motive_1 UDDCtx.nil →
      ((Γ : UDDCtx) → motive_1 Γ → motive_1 Γ.more) →
        ((Γ : UDDCtx) → motive_1 Γ → motive_2 Γ (UDDTy.base Γ)) →
          ({Γ : UDDCtx} → (a : Type u_2) → motive_1 Γ → motive_2 Γ (UDDTy.of a)) → (t : UDDCtx) → motive_1 t
-/
#guard_msgs(whitespace := lax) in
#check @UDDCtx.rec

def UDDCtx.len : UDDCtx → Nat :=
  UDDCtx.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    0 (fun _ ih => ih + 1) (fun _ ih => ih) (fun _ ih => ih)

example : UDDCtx.len (.more (.more .nil)) = 2 := rfl

/-! Put the field back and the cycle is there again.  What is worth pinning is
that the reason survives the trip: a member's own type names its siblings, and
at the point the lowering gives up not one of them is in the environment, so
saying which two members disagreed has to be read off their pre-types. -/

/--
error: The data members `UDDBad` and `UDDBadTy` live in different universes, `Type` and `Type 1`.  Lowering the erased pre-block into ordinary inductives is what lifts the kernel's same-universe rule, and here it did not go through:
  (kernel) universe level of type_of(arg #2) of 'UDDBad._pre.ext' is too big for the corresponding inductive datatype

Note: What the lowering lifts is the rule that the *members* of a mutual block agree about their universe.  The two rules underneath it stand: members that recurse into one another have to agree anyway -- an edge puts one universe at or below the other, so a cycle makes them equal -- and a field still has to fit inside the member it belongs to.  `X._pre` above is the erased form of `X`
-/
#guard_msgs in
mutual
inductive UDDBad : Type where
  | nil : UDDBad
  | ext : (Γ : UDDBad) → UDDBadTy Γ → UDDBad
inductive UDDBadTy : UDDBad → Type 1 where
  | base : (Γ : UDDBad) → UDDBadTy Γ
end

/-! ## Infinitary recursive fields

`Nat → Tree` recurses under a binder, and the induction hypothesis follows it.

`Good`'s index is `Nat → Tree`, not a `Tree`, so again there is no data member
to carry its motive and the block keeps the split recursors.
-/

mutual
inductive Tree : Type where
  | leaf : Tree
  | node : (f : Nat → Tree) → Good f → Tree
inductive Good : (Nat → Tree) → Prop where
  | leaf : Good (fun _ => .leaf)
end

/-- info: Tree.node : (f : Nat → Tree) → Good f → Tree -/
#guard_msgs in
#check @Tree.node

/--
info: @Tree.rec : {motive : Tree → Sort u_1} →
  motive Tree.leaf →
    ((f : Nat → Tree) → (a : Good f) → ((a : Nat) → motive (f a)) → motive (Tree.node f a)) → (t : Tree) → motive t
-/
#guard_msgs in
#check @Tree.rec

def Tree.depthAt (t : Tree) (k : Nat) : Nat :=
  Tree.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun _ _ ih k => ih k k + 1) t k

/-- info: 1 -/
#guard_msgs in
#eval Tree.depthAt (.node (fun _ => .leaf) .leaf) 3

example : Tree.depthAt (.node (fun _ => .leaf) .leaf) 3 = 1 := rfl

/-! ### One the whole block does recurse over

Above, `Good`'s index is a function, so no data member carries its motive and
the block keeps the split recursors.  Here `Sound`'s index is a `Skel`, so the
recursion over the whole block does form -- and it has to carry the higher-order
field through it.  `Skel.fan`'s minor gets a hypothesis under the binder, and
`Sound.fan`'s proof component is stated at `fan f fun a => f_ih a`: the value the
data recursion computes at `Skel.fan f`, eta-expanded, which is the only term
that could stand there.
-/

mutual
inductive Skel : Type where
  | tip
  | fan : (Nat → Skel) → Skel
  | ok : (s : Skel) → Sound s → Skel
inductive Sound : Skel → Prop where
  | tip : Sound .tip
  | fan : (f : Nat → Skel) → ((n : Nat) → Sound (f n)) → Sound (.fan f)
end

/--
info: @Skel.rec : {motive_1 : Skel → Sort u_1} →
  {motive_2 : (a : Skel) → motive_1 a → Sound a → Prop} →
    (tip : motive_1 Skel.tip) →
      (fan : (a : Nat → Skel) → ((a_1 : Nat) → motive_1 (a a_1)) → motive_1 (Skel.fan a)) →
        ((s : Skel) → (a : Sound s) → (s_ih : motive_1 s) → motive_2 s s_ih a → motive_1 (s.ok a)) →
          motive_2 Skel.tip tip Sound.tip →
            (∀ (f : Nat → Skel) (a : ∀ (n : Nat), Sound (f n)) (f_ih : (a : Nat) → motive_1 (f a)),
                (∀ (n : Nat), motive_2 (f n) (f_ih n) ⋯) → motive_2 (Skel.fan f) (fan f fun a => f_ih a) ⋯) →
              (t : Skel) → motive_1 t
-/
#guard_msgs in
#check @Skel.rec

-- the hypothesis under the binder is dropped along with the rest
/--
info: @Skel.casesD : {motive : Skel → Sort u_1} →
  motive Skel.tip →
    ((a : Nat → Skel) → motive (Skel.fan a)) → ((s : Skel) → (a : Sound s) → motive (s.ok a)) → (t : Skel) → motive t
-/
#guard_msgs in
#check @Skel.casesD

def Skel.width (s : Skel) : Nat :=
  Skel.casesD (motive := fun _ => Nat) 0 (fun _ => 1) (fun _ _ => 2) s

example : (Skel.fan (fun _ => .tip)).width = 1 := rfl

/-! ## A `Prop` member over two data members

`propSlots?` asks each proposition for exactly one data index, because a bundle
carries one value and a motive over two members would ask for two.  `Matches` has
two, so no recursion over the whole block forms and the split recursors stand:
`Val` and `Pat` recurse together, as the mutual data block they are, and
`Matches` gets a recursor of its own that mentions neither of their motives.

That recursor already has one motive, so there is no other to discharge -- but
its hypotheses are still there to drop, and dropping them is the whole of what
`Matches.casesP` is, which is what lets `cases` split a proof here at all.
-/

mutual
inductive Val : Type where
  | unit
  | pair : Val → Val → Val
inductive Pat : Type where
  | any
  | both : Pat → Pat → Pat
inductive Matches : Pat → Val → Prop where
  | any : (v : Val) → Matches .any v
  | both : (p q : Pat) → (u v : Val) → Matches p u → Matches q v →
      Matches (.both p q) (.pair u v)
end

/--
info: @Val.rec : {motive_1 : Val → Sort u_1} →
  {motive_2 : Pat → Sort u_1} →
    motive_1 Val.unit →
      ((a a_1 : Val) → motive_1 a → motive_1 a_1 → motive_1 (a.pair a_1)) →
        motive_2 Pat.any → ((a a_1 : Pat) → motive_2 a → motive_2 a_1 → motive_2 (a.both a_1)) → (t : Val) → motive_1 t
-/
#guard_msgs in
#check @Val.rec

/--
info: @Matches.rec : ∀ {motive : (a : Pat) → (a_1 : Val) → Matches a a_1 → Prop},
  (∀ (v : Val), motive Pat.any v ⋯) →
    (∀ (p q : Pat) (u v : Val) (a : Matches p u) (a_1 : Matches q v),
        motive p u a → motive q v a_1 → motive (p.both q) (u.pair v) ⋯) →
      ∀ {a : Pat} {a_1 : Val} (h : Matches a a_1), motive a a_1 h
-/
#guard_msgs in
#check @Matches.rec

example {p : Pat} {v : Val} (h : Matches p v) : True := by
  cases h with
  | any u => trivial
  | both a b c d e f => trivial

/-! ### What two data members costs `induction`

A case split uses no induction hypothesis at any member, so discharging a second
*data* motive to get one costs nothing there.  Both data members have a `casesD`
saying what mainline's `casesOn` says for a `mutual`, and `cases` names the
constructors that were written.
-/

/--
info: @Val.casesD : {motive : Val → Sort u_1} → motive Val.unit → ((a a_1 : Val) → motive (a.pair a_1)) → (t : Val) → motive t
-/
#guard_msgs in
#check @Val.casesD

/--
info: @Pat.casesD : {motive : Pat → Sort u_1} → motive Pat.any → ((a a_1 : Pat) → motive (a.both a_1)) → (t : Pat) → motive t
-/
#guard_msgs in
#check @Pat.casesD

example (v : Val) : v = v := by
  cases v with
  | unit => rfl
  | pair a b => rfl

/-! `induction` is the one that pays, though here the bill comes to nothing:
discharging `Pat`'s motive drops the hypotheses at `Pat`, and no constructor of
`Val` has a field there, so `recD` is as strong as the recursion over the whole
block restricted to `Val`.  Where a block does cross over the loss is real, and
the recursion is written all the same.  Mainline can afford to refuse -- "does
not support the type `Val` because it is mutually inductive" -- because a
member of a `mutual` is an inductive and refusing sends the caller to the
recursor; a member here is a `def`, and a tactic that finds no eliminator of
its own does not stop but unfolds it, and offers a split on the subtype. -/

/--
info: @Val.recD : {motive : Val → Sort u_1} →
  motive Val.unit → ((a a_1 : Val) → motive a → motive a_1 → motive (a.pair a_1)) → (t : Val) → motive t
-/
#guard_msgs in
#check @Val.recD

example (v : Val) : v = v := by
  induction v with
  | unit => rfl
  | pair a b ha hb => rfl

/-! The recursion over the whole block is still the strong one, and naming the
sibling motive is the whole of what it asks for. -/

example (v : Val) : v = v := by
  induction v using Val.rec (motive_2 := fun _ => PUnit) with
  | unit => rfl
  | pair a b ha hb => rfl
  | any => exact .unit
  | both => intros; exact .unit

/-! ### Two data members and a proposition over one of them

`WfU` is indexed by `TmU` and by nothing else, so the block does form the
recursion over the whole of it, and the proposition gets the one-motive
recursion a data member cannot -- discharging a *data* motive to state a `Prop`
costs a proof nothing.  What is new here is that there are two of them to
discharge, and that the sort they live in is still a parameter the surviving
motive needs, so what fills them in is the one-element type at that sort rather
than `Unit`.
-/

mutual
inductive TmU (α : Type u) : Type u where
  | var : α → TmU α
  | app : TmU α → TyU α → TmU α
inductive TyU (α : Type u) : Type u where
  | base : TyU α
  | arr : TyU α → TyU α → TyU α
inductive WfU (α : Type u) : TmU α → Prop where
  | var : (a : α) → WfU α (.var a)
  | app : (t : TmU α) → (s : TyU α) → WfU α t → WfU α (.app t s)
end

/--
info: @TmU.casesD : {α : Type u_2} →
  {motive : TmU α → Sort u_1} →
    ((a : α) → motive (TmU.var a)) → ((a : TmU α) → (a_1 : TyU α) → motive (a.app a_1)) → (t : TmU α) → motive t
-/
#guard_msgs in
#check @TmU.casesD

/-! The two read side by side are the whole of the difference: `app` keeps its
`motive t a` for the recursion and loses it for the case split. -/

/--
info: @WfU.recP : ∀ {α : Type u_1} {motive : (a : TmU α) → WfU α a → Prop},
  (∀ (a : α), motive (TmU.var a) ⋯) →
    (∀ (t : TmU α) (s : TyU α) (a : WfU α t), motive t a → motive (t.app s) ⋯) → ∀ {a : TmU α} (h : WfU α a), motive a h
-/
#guard_msgs in
#check @WfU.recP

/--
info: @WfU.casesP : ∀ {α : Type u_1} {motive : (a : TmU α) → WfU α a → Prop},
  (∀ (a : α), motive (TmU.var a) ⋯) →
    (∀ (t : TmU α) (s : TyU α) (a : WfU α t), motive (t.app s) ⋯) → ∀ {a : TmU α} (h : WfU α a), motive a h
-/
#guard_msgs in
#check @WfU.casesP

example {α : Type u} (t : TmU α) : True := by
  cases t with
  | var a => trivial
  | app f s => trivial

/-! The index is a variable, which is the split that reached for the encoding
before there was an eliminator to pin. -/

example {α : Type u} (t : TmU α) (h : WfU α t) : True := by
  cases h with
  | var a => trivial
  | app f s ih => trivial

def TmU.head {α : Type u} (t : TmU α) : Option α :=
  TmU.casesD (motive := fun _ => Option α) some (fun _ _ => none) t

example : (TmU.var (α := Nat) 7).head = some 7 := rfl
example : (TmU.app (TmU.var (α := Nat) 7) .base).head = none := rfl

/-- info: 'TmU.head' does not depend on any axioms -/
#guard_msgs in
#print axioms TmU.head

/-! ## Parameters and universe parameters

The parameters lead every arity, every constructor and the recursor, and are
implicit on the last two.  The universe parameters are shared by the whole
block, as they are for a Lean `mutual`.

`OkB` is indexed by both `Bag` and `Tag2`, so this is a third block on the
split recursors.
-/

mutual
inductive Bag (α : Type u) (β : Type v) : Nat → Type (max u v) where
  | nil : Bag α β 0
  | cons : (n : Nat) → (b : Bag α β n) → (t : Tag2 α β) → OkB α β n b t → Bag α β (n + 1)
inductive Tag2 (α : Type u) (β : Type v) : Type (max u v) where
  | mk : α → β → Tag2 α β
inductive OkB (α : Type u) (β : Type v) : (n : Nat) → Bag α β n → Tag2 α β → Prop where
  | nil : (t : Tag2 α β) → OkB α β 0 .nil t
end

/-- info: Bag : Type u_1 → Type u_2 → Nat → Type (max u_1 u_2) -/
#guard_msgs in
#check @Bag

/-- info: OkB : (α : Type u_1) → (β : Type u_2) → (n : Nat) → Bag α β n → Tag2 α β → Prop -/
#guard_msgs in
#check @OkB

/--
info: @Bag.cons : {α : Type u_1} →
  {β : Type u_2} → (n : Nat) → (b : Bag α β n) → (t : Tag2 α β) → OkB α β n b t → Bag α β (n + 1)
-/
#guard_msgs in
#check @Bag.cons

/-- info: @OkB.nil : ∀ {α : Type u_1} {β : Type u_2} (t : Tag2 α β), OkB α β 0 Bag.nil t -/
#guard_msgs in
#check @OkB.nil

/--
info: @Bag.rec : {α : Type u_2} →
  {β : Type u_3} →
    {motive_1 : (a : Nat) → Bag α β a → Sort u_1} →
      {motive_2 : Tag2 α β → Sort u_1} →
        motive_1 0 Bag.nil →
          ((n : Nat) →
              (b : Bag α β n) →
                (t : Tag2 α β) →
                  (a : OkB α β n b t) → motive_1 n b → motive_2 t → motive_1 (n + 1) (Bag.cons n b t a)) →
            ((a : α) → (a_1 : β) → motive_2 (Tag2.mk a a_1)) → {a : Nat} → (t : Bag α β a) → motive_1 a t
-/
#guard_msgs in
#check @Bag.rec

def Bag.count {α : Type u} {β : Type v} : (n : Nat) → Bag α β n → Nat :=
  fun _ b => Bag.rec (motive_1 := fun _ _ => Nat) (motive_2 := fun _ => Nat)
    0 (fun _ _ _ _ ih _ => ih + 1) (fun _ _ => 0) b

def exBag : Bag String Nat 1 := .cons 0 .nil (.mk "a" 3) (.nil (.mk "a" 3))

/-- info: 1 -/
#guard_msgs in
#eval exBag.count

example : Bag.count 1 exBag = 1 := rfl

/-- info: 'exBag' does not depend on any axioms -/
#guard_msgs in
#print axioms exBag

/-- info: 'Bag.count' does not depend on any axioms -/
#guard_msgs in
#print axioms Bag.count

/-! ## The level list the scratch axioms are declared over

A member is stubbed as a scratch axiom the moment its arity is known, and the
only level list available then is every universe name in scope.  That is not
the list the block ends up with, and the two shapes below are the ways it can
differ: a `universe` line the rest of the file needs is in scope whether the
block uses it or not, and a name can be auto-bound *after* an earlier member
has already been stubbed.  Either way `restub` moves the axioms once the real
list is known; without it neither block typechecks.
-/

section
universe u₀ v₀ w₀

mutual
inductive UCtx : Type where
  | nil : UCtx
  | snoc : (Γ : UCtx) → (x : String) → UFresh x Γ → UCtx
inductive UFresh : String → UCtx → Prop where
  | nil : (x : String) → UFresh x .nil
  | snoc : (x y : String) → (Γ : UCtx) → (h : UFresh y Γ) → x ≠ y → UFresh x Γ →
    UFresh x (.snoc Γ y h)
end

/-- info: UCtx : Type -/
#guard_msgs in
#check @UCtx

/-- info: UFresh : String → UCtx → Prop -/
#guard_msgs in
#check @UFresh

example : UCtx := .snoc .nil "x" (.nil "x")

end

-- `u` is auto-bound by a field of `VOk`'s second constructor, long after `VBag`
-- was stubbed over the empty list; the block's own list is `[u]`
mutual
inductive VBag : Type where
  | nil : VBag
  | cons : (Γ : VBag) → VOk Γ → VBag
inductive VOk : VBag → Prop where
  | nil : VOk .nil
  | cons : (Γ : VBag) → (h : VOk Γ) → (α : Type u) → (a : α) → VOk (.cons Γ h)
end

/-- info: VBag.{u_1} : Type -/
#guard_msgs in
set_option pp.universes true in
#check @VBag

/-- info: VOk.cons : ∀ (Γ : VBag) (h : VOk Γ) (α : Type u_1) (a : α), VOk (Γ.cons h) -/
#guard_msgs in
#check @VOk.cons

example : VBag := .cons (.cons .nil .nil) (.cons .nil .nil Nat 3)

/-! ## Resulting types left out, and members named under one another

A member that gives no resulting type at all is read as `Type`, which is what
`inductive Tree where` means.  This block also names two of its `Prop` members
*under* a data member -- `TreeNested.WF` beside `TreeNested` -- so "this type
mentions a data member" has to be decided by exact name and not by prefix; and
its three data members form a cycle that runs through both `Prop` members.

All five recursors are pinned below.  What that is checking, beyond the shapes,
is that none of them mentions a name the user did not write: no `_pre`, no
`_wf`, no `nested_` copy.
-/

mutual
inductive TreeNested where
  | empty
  | node (key : Nat) (value : RecWFTree) (l r : TreeNested)
inductive TreeNested.WFWith : TreeNested → List Nat → Prop where
  | empty : TreeNested.WFWith .empty []
  | node {llist rlist : List Nat} (key : Nat) (value : RecWFTree) (l r : TreeNested)
    (hl : TreeNested.WFWith l llist) (hr : TreeNested.WFWith r rlist)
    (hl' : ∀ a ∈ llist, a < key) (hr' : ∀ a ∈ rlist, key < a) :
    TreeNested.WFWith (.node key value l r) (llist ++ key :: rlist)
inductive TreeNested.WF : TreeNested → Prop where
  | intro (l : List Nat) (t : TreeNested) (h : TreeNested.WFWith t l) : TreeNested.WF t
inductive WFTreeNested where
  | mk (x : TreeNested) (h : TreeNested.WF x) : WFTreeNested
inductive RecWFTree where
  | mk (x : WFTreeNested)
end

/-- info: TreeNested : Type -/
#guard_msgs in
#check @TreeNested

/-- info: TreeNested.node : Nat → RecWFTree → TreeNested → TreeNested → TreeNested -/
#guard_msgs in
#check @TreeNested.node

/-- info: TreeNested.WFWith : TreeNested → List Nat → Prop -/
#guard_msgs in
#check @TreeNested.WFWith

/-- info: WFTreeNested.mk : (x : TreeNested) → x.WF → WFTreeNested -/
#guard_msgs in
#check @WFTreeNested.mk

/--
info: @TreeNested.rec : {motive_1 : TreeNested → Sort u_1} →
  {motive_2 : (a : TreeNested) → (a_1 : List Nat) → motive_1 a → a.WFWith a_1 → Prop} →
    {motive_3 : (a : TreeNested) → motive_1 a → a.WF → Prop} →
      {motive_4 : WFTreeNested → Sort u_1} →
        {motive_5 : RecWFTree → Sort u_1} →
          (empty : motive_1 TreeNested.empty) →
            (node :
                (key : Nat) →
                  (value : RecWFTree) →
                    (l r : TreeNested) →
                      motive_5 value → motive_1 l → motive_1 r → motive_1 (TreeNested.node key value l r)) →
              motive_2 TreeNested.empty [] empty TreeNested.WFWith.empty →
                (∀ {llist rlist : List Nat} (key : Nat) (value : RecWFTree) (l r : TreeNested) (hl : l.WFWith llist)
                    (hr : r.WFWith rlist) (hl' : ∀ (a : Nat), a ∈ llist → a < key)
                    (hr' : ∀ (a : Nat), a ∈ rlist → key < a) (value_ih : motive_5 value) (l_ih : motive_1 l)
                    (r_ih : motive_1 r),
                    motive_2 l llist l_ih hl →
                      motive_2 r rlist r_ih hr →
                        motive_2 (TreeNested.node key value l r) (llist ++ key :: rlist)
                          (node key value l r value_ih l_ih r_ih) ⋯) →
                  (∀ (l : List Nat) (t : TreeNested) (h : t.WFWith l) (t_ih : motive_1 t),
                      motive_2 t l t_ih h → motive_3 t t_ih ⋯) →
                    ((x : TreeNested) →
                        (h : x.WF) → (x_ih : motive_1 x) → motive_3 x x_ih h → motive_4 (WFTreeNested.mk x h)) →
                      ((x : WFTreeNested) → motive_4 x → motive_5 (RecWFTree.mk x)) → (t : TreeNested) → motive_1 t
-/
#guard_msgs in
#check @TreeNested.rec

/--
info: @WFTreeNested.rec : {motive_1 : TreeNested → Sort u_1} →
  {motive_2 : (a : TreeNested) → (a_1 : List Nat) → motive_1 a → a.WFWith a_1 → Prop} →
    {motive_3 : (a : TreeNested) → motive_1 a → a.WF → Prop} →
      {motive_4 : WFTreeNested → Sort u_1} →
        {motive_5 : RecWFTree → Sort u_1} →
          (empty : motive_1 TreeNested.empty) →
            (node :
                (key : Nat) →
                  (value : RecWFTree) →
                    (l r : TreeNested) →
                      motive_5 value → motive_1 l → motive_1 r → motive_1 (TreeNested.node key value l r)) →
              motive_2 TreeNested.empty [] empty TreeNested.WFWith.empty →
                (∀ {llist rlist : List Nat} (key : Nat) (value : RecWFTree) (l r : TreeNested) (hl : l.WFWith llist)
                    (hr : r.WFWith rlist) (hl' : ∀ (a : Nat), a ∈ llist → a < key)
                    (hr' : ∀ (a : Nat), a ∈ rlist → key < a) (value_ih : motive_5 value) (l_ih : motive_1 l)
                    (r_ih : motive_1 r),
                    motive_2 l llist l_ih hl →
                      motive_2 r rlist r_ih hr →
                        motive_2 (TreeNested.node key value l r) (llist ++ key :: rlist)
                          (node key value l r value_ih l_ih r_ih) ⋯) →
                  (∀ (l : List Nat) (t : TreeNested) (h : t.WFWith l) (t_ih : motive_1 t),
                      motive_2 t l t_ih h → motive_3 t t_ih ⋯) →
                    ((x : TreeNested) →
                        (h : x.WF) → (x_ih : motive_1 x) → motive_3 x x_ih h → motive_4 (WFTreeNested.mk x h)) →
                      ((x : WFTreeNested) → motive_4 x → motive_5 (RecWFTree.mk x)) → (t : WFTreeNested) → motive_4 t
-/
#guard_msgs in
#check @WFTreeNested.rec

/--
info: @RecWFTree.rec : {motive_1 : TreeNested → Sort u_1} →
  {motive_2 : (a : TreeNested) → (a_1 : List Nat) → motive_1 a → a.WFWith a_1 → Prop} →
    {motive_3 : (a : TreeNested) → motive_1 a → a.WF → Prop} →
      {motive_4 : WFTreeNested → Sort u_1} →
        {motive_5 : RecWFTree → Sort u_1} →
          (empty : motive_1 TreeNested.empty) →
            (node :
                (key : Nat) →
                  (value : RecWFTree) →
                    (l r : TreeNested) →
                      motive_5 value → motive_1 l → motive_1 r → motive_1 (TreeNested.node key value l r)) →
              motive_2 TreeNested.empty [] empty TreeNested.WFWith.empty →
                (∀ {llist rlist : List Nat} (key : Nat) (value : RecWFTree) (l r : TreeNested) (hl : l.WFWith llist)
                    (hr : r.WFWith rlist) (hl' : ∀ (a : Nat), a ∈ llist → a < key)
                    (hr' : ∀ (a : Nat), a ∈ rlist → key < a) (value_ih : motive_5 value) (l_ih : motive_1 l)
                    (r_ih : motive_1 r),
                    motive_2 l llist l_ih hl →
                      motive_2 r rlist r_ih hr →
                        motive_2 (TreeNested.node key value l r) (llist ++ key :: rlist)
                          (node key value l r value_ih l_ih r_ih) ⋯) →
                  (∀ (l : List Nat) (t : TreeNested) (h : t.WFWith l) (t_ih : motive_1 t),
                      motive_2 t l t_ih h → motive_3 t t_ih ⋯) →
                    ((x : TreeNested) →
                        (h : x.WF) → (x_ih : motive_1 x) → motive_3 x x_ih h → motive_4 (WFTreeNested.mk x h)) →
                      ((x : WFTreeNested) → motive_4 x → motive_5 (RecWFTree.mk x)) → (t : RecWFTree) → motive_5 t
-/
#guard_msgs in
#check @RecWFTree.rec

-- the minors of a `Prop` recursor conclude at a constructor application, which
-- is what this test is about; without `pp.proofs` they all print as `⋯`
/--
info: @TreeNested.WFWith.rec : ∀ {motive_1 : TreeNested → Sort u_1}
  {motive_2 : (a : TreeNested) → (a_1 : List Nat) → motive_1 a → a.WFWith a_1 → Prop}
  {motive_3 : (a : TreeNested) → motive_1 a → a.WF → Prop} {motive_4 : WFTreeNested → Sort u_1}
  {motive_5 : RecWFTree → Sort u_1} (empty : motive_1 TreeNested.empty)
  (node :
    (key : Nat) →
      (value : RecWFTree) →
        (l r : TreeNested) → motive_5 value → motive_1 l → motive_1 r → motive_1 (TreeNested.node key value l r))
  (empty_1 : motive_2 TreeNested.empty [] empty TreeNested.WFWith.empty)
  (node_1 :
    ∀ {llist rlist : List Nat} (key : Nat) (value : RecWFTree) (l r : TreeNested) (hl : l.WFWith llist)
      (hr : r.WFWith rlist) (hl' : ∀ (a : Nat), a ∈ llist → a < key) (hr' : ∀ (a : Nat), a ∈ rlist → key < a)
      (value_ih : motive_5 value) (l_ih : motive_1 l) (r_ih : motive_1 r),
      motive_2 l llist l_ih hl →
        motive_2 r rlist r_ih hr →
          motive_2 (TreeNested.node key value l r) (llist ++ key :: rlist) (node key value l r value_ih l_ih r_ih)
            (TreeNested.WFWith.node key value l r hl hr hl' hr'))
  (intro :
    ∀ (l : List Nat) (t : TreeNested) (h : t.WFWith l) (t_ih : motive_1 t),
      motive_2 t l t_ih h → motive_3 t t_ih (TreeNested.WF.intro l t h))
  (mk : (x : TreeNested) → (h : x.WF) → (x_ih : motive_1 x) → motive_3 x x_ih h → motive_4 (WFTreeNested.mk x h))
  (mk_1 : (x : WFTreeNested) → motive_4 x → motive_5 (RecWFTree.mk x)) {a : TreeNested} {a_1 : List Nat}
  (h : a.WFWith a_1), motive_2 a a_1 (TreeNested.rec empty node empty_1 node_1 intro mk mk_1 a) h
-/
#guard_msgs in
set_option pp.proofs true in
#check @TreeNested.WFWith.rec

/--
info: @TreeNested.WF.rec : ∀ {motive_1 : TreeNested → Sort u_1}
  {motive_2 : (a : TreeNested) → (a_1 : List Nat) → motive_1 a → a.WFWith a_1 → Prop}
  {motive_3 : (a : TreeNested) → motive_1 a → a.WF → Prop} {motive_4 : WFTreeNested → Sort u_1}
  {motive_5 : RecWFTree → Sort u_1} (empty : motive_1 TreeNested.empty)
  (node :
    (key : Nat) →
      (value : RecWFTree) →
        (l r : TreeNested) → motive_5 value → motive_1 l → motive_1 r → motive_1 (TreeNested.node key value l r))
  (empty_1 : motive_2 TreeNested.empty [] empty TreeNested.WFWith.empty)
  (node_1 :
    ∀ {llist rlist : List Nat} (key : Nat) (value : RecWFTree) (l r : TreeNested) (hl : l.WFWith llist)
      (hr : r.WFWith rlist) (hl' : ∀ (a : Nat), a ∈ llist → a < key) (hr' : ∀ (a : Nat), a ∈ rlist → key < a)
      (value_ih : motive_5 value) (l_ih : motive_1 l) (r_ih : motive_1 r),
      motive_2 l llist l_ih hl →
        motive_2 r rlist r_ih hr →
          motive_2 (TreeNested.node key value l r) (llist ++ key :: rlist) (node key value l r value_ih l_ih r_ih)
            (TreeNested.WFWith.node key value l r hl hr hl' hr'))
  (intro :
    ∀ (l : List Nat) (t : TreeNested) (h : t.WFWith l) (t_ih : motive_1 t),
      motive_2 t l t_ih h → motive_3 t t_ih (TreeNested.WF.intro l t h))
  (mk : (x : TreeNested) → (h : x.WF) → (x_ih : motive_1 x) → motive_3 x x_ih h → motive_4 (WFTreeNested.mk x h))
  (mk_1 : (x : WFTreeNested) → motive_4 x → motive_5 (RecWFTree.mk x)) {a : TreeNested} (h : a.WF),
  motive_3 a (TreeNested.rec empty node empty_1 node_1 intro mk mk_1 a) h
-/
#guard_msgs in
set_option pp.proofs true in
#check @TreeNested.WF.rec

theorem leafWF : TreeNested.WF .empty := .intro [] _ .empty

def leaf : RecWFTree := .mk (.mk .empty leafWF)

def one : TreeNested := .node 3 leaf .empty .empty

theorem oneWFWith : TreeNested.WFWith one [3] :=
  .node 3 leaf .empty .empty .empty .empty (by simp) (by simp)

theorem oneWF : TreeNested.WF one := .intro _ _ oneWFWith

def oneR : RecWFTree := .mk (.mk one oneWF)

/-! ### A predicate motive that says something about the computed value

The block is elaborated once, so `TreeNested.size` and the theorem below are two
projections of a *single* recursion: they name the same seven minor premises
under the same five motives.  `M2` is where the point is -- it is a statement
about the `Nat` that `M1`'s minors produced, so proving it is proving something
about `TreeNested.size` while `TreeNested.size` is being defined.

Two recursions with *different* motive sets are not defeq, exactly as for Lean's
own mutual recursors; that is the price of one recursor for the whole block.
-/

abbrev M1 : TreeNested → Type := fun _ => Nat
abbrev M4 : WFTreeNested → Type := fun _ => Nat
abbrev M5 : RecWFTree → Type := fun _ => Nat
abbrev M2 : (x : TreeNested) → (l : List Nat) → M1 x → x.WFWith l → Prop :=
  fun _ l n _ => l.length ≤ n
abbrev M3 : (x : TreeNested) → M1 x → x.WF → Prop := fun _ _ _ => True

def sEmpty : M1 .empty := 0

def sNode : (key : Nat) → (value : RecWFTree) → (l r : TreeNested) →
    M5 value → M1 l → M1 r → M1 (.node key value l r) :=
  fun _ _ _ _ v l r => v + l + r + 1

theorem sEmptyW : M2 .empty [] sEmpty .empty := by simp [sEmpty]

theorem sNodeW : ∀ {ll rl : List Nat} (key : Nat) (value : RecWFTree) (l r : TreeNested)
    (hl : l.WFWith ll) (hr : r.WFWith rl) (hl' : ∀ a ∈ ll, a < key) (hr' : ∀ a ∈ rl, key < a)
    (vih : M5 value) (lih : M1 l) (rih : M1 r), M2 l ll lih hl → M2 r rl rih hr →
      M2 (.node key value l r) (ll ++ key :: rl) (sNode key value l r vih lih rih)
      (TreeNested.WFWith.node key value l r hl hr hl' hr') := by
  intro ll rl k v l r hl hr _ _ vih lih rih ihl ihr
  simp only [M2, sNode, List.length_append, List.length_cons] at *
  omega

theorem sIntro : ∀ (l : List Nat) (t : TreeNested) (h : t.WFWith l) (t_ih : M1 t),
    M2 t l t_ih h → M3 t t_ih (.intro l t h) := fun _ _ _ _ _ => trivial

def sMk : (x : TreeNested) → (h : x.WF) → (x_ih : M1 x) → M3 x x_ih h → M4 (.mk x h) :=
  fun _ _ n _ => n

def sMk2 : (x : WFTreeNested) → M4 x → M5 (.mk x) := fun _ n => n

def TreeNested.size : TreeNested → Nat :=
  TreeNested.rec (motive_1 := M1) (motive_2 := M2) (motive_3 := M3) (motive_4 := M4)
    (motive_5 := M5) sEmpty sNode sEmptyW sNodeW sIntro sMk sMk2

def RecWFTree.size : RecWFTree → Nat :=
  RecWFTree.rec (motive_1 := M1) (motive_2 := M2) (motive_3 := M3) (motive_4 := M4)
    (motive_5 := M5) sEmpty sNode sEmptyW sNodeW sIntro sMk sMk2

example : TreeNested.size .empty = 0 := rfl
example : TreeNested.size one = 1 := rfl

-- the iota rule crosses members: `value` is a `RecWFTree`, three members away
example (k : Nat) (v : RecWFTree) (l r : TreeNested) :
    TreeNested.size (.node k v l r)
      = RecWFTree.size v + TreeNested.size l + TreeNested.size r + 1 := rfl

/-- info: 3 -/
#guard_msgs in
#eval TreeNested.size (.node 1 oneR one .empty)

-- `propext` from the indexed recursor, `Quot.sound` from `sNodeW`'s `omega`
/-- info: 'TreeNested.size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TreeNested.size

/-- The predicate recursor, at a motive that mentions the data recursor's value. -/
theorem wfwith_le (t : TreeNested) (l : List Nat) (h : t.WFWith l) : l.length ≤ t.size :=
  TreeNested.WFWith.rec (motive_1 := M1) (motive_2 := M2) (motive_3 := M3) (motive_4 := M4)
    (motive_5 := M5) sEmpty sNode sEmptyW sNodeW sIntro sMk sMk2 h

/-- info: 'wfwith_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms wfwith_le

/-- info: 'leafWF' does not depend on any axioms -/
#guard_msgs in
#print axioms leafWF

example (t : TreeNested) (h : t.WF) : True := by cases h; trivial

/-! ### The same, where the block has universe parameters

A constructor with no resulting type is read as the member applied to its
parameters, and the member is in scope only as a scratch axiom -- declared over
every universe name that was around when its arity was read.  So the guess has
to carry a level for each of them.  What the levels *are* is not knowable yet
and does not matter, since the whole block is moved to its own list once the
constructors have been read; what matters is that there are the right number of
them, and that they are not the names, which would make the block depend on
universes it never uses.

Nothing notices until a second member names the constructor -- which is what a
proposition indexed by `.nil` does. -/

mutual
inductive NoResTy (α : Type u) : Type u where
  | nil
  | ext : (Γ : NoResTy α) → α → NoResOk α Γ → NoResTy α
inductive NoResOk (α : Type u) : NoResTy α → Prop where
  | nil : NoResOk α .nil
end

/-- info: NoResTy : Type u_1 → Type u_1 -/
#guard_msgs in
#check @NoResTy

/-- info: @NoResTy.nil : {α : Type u_1} → NoResTy α -/
#guard_msgs in
#check @NoResTy.nil

/-- info: @NoResOk.nil : ∀ {α : Type u_1}, NoResOk α NoResTy.nil -/
#guard_msgs in
#check @NoResOk.nil

/--
info: @NoResTy.rec : {α : Type u_2} →
  {motive_1 : NoResTy α → Sort u_1} →
    {motive_2 : (a : NoResTy α) → motive_1 a → NoResOk α a → Prop} →
      (nil : motive_1 NoResTy.nil) →
        ((Γ : NoResTy α) →
            (a : α) → (a_1 : NoResOk α Γ) → (Γ_ih : motive_1 Γ) → motive_2 Γ Γ_ih a_1 → motive_1 (Γ.ext a a_1)) →
          motive_2 NoResTy.nil nil ⋯ → (t : NoResTy α) → motive_1 t
-/
#guard_msgs in
#check @NoResTy.rec

def NoResTy.len {α : Type u} (Γ : NoResTy α) : Nat :=
  NoResTy.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ _ => True)
    0 (fun _ _ _ ih _ => ih + 1) trivial Γ

/-- info: 1 -/
#guard_msgs in
#eval (NoResTy.ext (.nil (α := Nat)) 3 .nil).len

example : (NoResTy.nil (α := Nat)).len = 0 := rfl

-- and the block really is polymorphic in `u` alone: no universe the file
-- happens to have in scope came along for the ride
/-- info: 'NoResTy' does not depend on any axioms -/
#guard_msgs in
#print axioms NoResTy

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

/-! ## Data indexed by data

The other kernel rule the erasure lifts.  A mutual inductive may not name one of
its own members in another's *arity*, which is exactly what `Ty : Ctx → Type`
does -- and there is no `Prop` anywhere in it to blame, so the crossing the rest
of this file buys is no help.

Erasure reaches it by deleting two things rather than one.  The index goes from
the arity, so that `Ty._pre : Type` no longer says which context it is a type
of; and the constructor field that *was* that index goes with it, since there is
nothing left for it to index.  Both come back from `_wf`, which takes the
deleted index as an argument of its own -- `Ty._wf : Ctx._pre → Ty._pre → Prop`
-- and `Ty Γ` is the subtype of `Ty._pre` that `Ty._wf Γ.val` cuts out.  There
are no equations anywhere in it, which is the reason to do it this way at all.
-/

namespace DataOnData

mutual
inductive Ctx : Type where
  | nil  : Ctx
  | snoc : (Γ : Ctx) → Ty Γ → Ctx
inductive Ty : Ctx → Type where
  | base : (Γ : Ctx) → Ty Γ
  | pi   : (Γ : Ctx) → (A : Ty Γ) → Ty (Ctx.snoc Γ A) → Ty Γ
end

-- the two pre-types are one ordinary mutual block, and neither arity mentions
-- the other.  `Ty._pre.base` has lost the context it was a type of, and
-- `Ty._pre.pi` has lost it twice: once as its own first field, once out of the
-- `Ctx.snoc Γ A` its second argument was a type of
/--
info: inductive DataOnData.Ctx._pre : Type
number of parameters: 0
constructors:
DataOnData.Ctx._pre.nil : Ctx._pre
DataOnData.Ctx._pre.snoc : Ctx._pre → Ty._pre → Ctx._pre
-/
#guard_msgs in
#print Ctx._pre

/--
info: inductive DataOnData.Ty._pre : Type
number of parameters: 0
constructors:
DataOnData.Ty._pre.base : Ty._pre
DataOnData.Ty._pre.pi : Ty._pre → Ty._pre → Ty._pre
-/
#guard_msgs in
#print Ty._pre

-- and `_wf` puts every one of them back.  `Ty._wf` takes the deleted index in
-- front of the pre-term it is about, and the recursion inside supplies it after
-- the major premise, since there is nothing to say about an index until the
-- recursion has one to say it at
/--
info: def DataOnData.Ctx._wf : Ctx._pre → Prop :=
Ctx._pre.rec True (fun Γ a ih ih_1 => ih ∧ ih_1 Γ) (fun Γ => True) fun A a ih ih_1 Γ => ih Γ ∧ ih_1 (Γ.snoc A)
-/
#guard_msgs in
#print Ctx._wf

/--
info: def DataOnData.Ty._wf : Ctx._pre → Ty._pre → Prop :=
fun a t =>
  Ty._pre.rec True (fun Γ a ih ih_1 => ih ∧ ih_1 Γ) (fun Γ => True) (fun A a ih ih_1 Γ => ih Γ ∧ ih_1 (Γ.snoc A)) t a
-/
#guard_msgs in
#print Ty._wf

-- what the writer sees is the block they wrote, at one recursion over both
/--
info: @Ctx.rec : {motive_1 : Ctx → Sort u_1} →
  {motive_2 : (a : Ctx) → Ty a → Sort u_1} →
    motive_1 Ctx.nil →
      ((Γ : Ctx) → (a : Ty Γ) → motive_1 Γ → motive_2 Γ a → motive_1 (Γ.snoc a)) →
        ((Γ : Ctx) → motive_1 Γ → motive_2 Γ (Ty.base Γ)) →
          ((Γ : Ctx) →
              (A : Ty Γ) →
                (a : Ty (Γ.snoc A)) → motive_1 Γ → motive_2 Γ A → motive_2 (Γ.snoc A) a → motive_2 Γ (Ty.pi Γ A a)) →
            (t : Ctx) → motive_1 t
-/
#guard_msgs in
#check @Ctx.rec

/--
info: @Ty.rec : {motive_1 : Ctx → Sort u_1} →
  {motive_2 : (a : Ctx) → Ty a → Sort u_1} →
    motive_1 Ctx.nil →
      ((Γ : Ctx) → (a : Ty Γ) → motive_1 Γ → motive_2 Γ a → motive_1 (Γ.snoc a)) →
        ((Γ : Ctx) → motive_1 Γ → motive_2 Γ (Ty.base Γ)) →
          ((Γ : Ctx) →
              (A : Ty Γ) →
                (a : Ty (Γ.snoc A)) → motive_1 Γ → motive_2 Γ A → motive_2 (Γ.snoc A) a → motive_2 Γ (Ty.pi Γ A a)) →
            {a : Ctx} → (t : Ty a) → motive_2 a t
-/
#guard_msgs in
#check @Ty.rec

def Ctx.len : Ctx → Nat :=
  Ctx.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    0 (fun _ _ n _ => n + 1) (fun _ _ => 0) (fun _ _ _ _ _ b => b)

def Ty.depth {Γ : Ctx} (A : Ty Γ) : Nat :=
  Ty.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    0 (fun _ _ n _ => n + 1) (fun _ _ => 0) (fun _ _ _ _ a b => a + b + 1) A

-- both iota rules are definitional, including the one at a compound index:
-- `B` is a type of `Γ.snoc A`, and the hypothesis for it arrives there
example : Ctx.len .nil = 0 := rfl
example (Γ : Ctx) (A : Ty Γ) : (Γ.snoc A).len = Γ.len + 1 := rfl
example (Γ : Ctx) : (Ty.base Γ).depth = 0 := rfl
example (Γ : Ctx) (A : Ty Γ) (B : Ty (Γ.snoc A)) :
    (Ty.pi Γ A B).depth = A.depth + B.depth + 1 := rfl

/-- info: 2 -/
#guard_msgs in
#eval Ctx.len (.snoc (.snoc .nil (.base .nil)) (.base (.snoc .nil (.base .nil))))

end DataOnData

/-! ### A third member indexed by both of the others

Nothing in the block names `Tm`, so `Tm` is a sink: once the two members it is
indexed by are there, it can be declared on its own.  It is, and the writer's
name is given to a definition unfolding to the inductive that was really
declared.  The erasure is never asked about a member that leaves -- there is no
`Tm._pre` and no `Tm._wf` -- and in exchange `Tm` is something `match` can take
apart, which an erased member is not.  What the erasure would have said is
pinned in `DataOnDataBuiltKept` below, where a partner names `Tm` and so keeps
it in the block.
-/

namespace DataOnDataTm

mutual
inductive Ctx : Type where
  | nil  : Ctx
  | snoc : (Γ : Ctx) → Ty Γ → Ctx
inductive Ty : Ctx → Type where
  | base : (Γ : Ctx) → Ty Γ
  | pi   : (Γ : Ctx) → (A : Ty Γ) → Ty (Ctx.snoc Γ A) → Ty Γ
inductive Tm : (Γ : Ctx) → Ty Γ → Type where
  | var  : (Γ : Ctx) → (A : Ty Γ) → Tm Γ A
  | body : (Γ : Ctx) → (A : Ty Γ) → (B : Ty (Ctx.snoc Γ A)) →
             Tm (Ctx.snoc Γ A) B → Tm Γ A
end

-- what stands under the writer's name is a definition, and the inductive it
-- unfolds to is one name over.  The name has to move because the kernel writes
-- `X.rec` for whatever it is handed as an inductive `X`, and `Tm.rec` is wanted
-- for the recursion over the whole block
/--
info: def DataOnDataTm.Tm : (Γ : Ctx) → Ty Γ → Type :=
Tm._ind
-/
#guard_msgs in
#print Tm

-- so the erasure has nothing to say about it
/-- error: Unknown constant `DataOnDataTm.Tm._wf` -/
#guard_msgs in
#check DataOnDataTm.Tm._wf

-- and the recursor is the block's all the same, motives and all.  That is what
-- Lean does for a `mutual` block that is not really mutual, and a member that
-- can be lifted out is exactly that case
/--
info: @Tm.rec : {motive_1 : Ctx → Sort u_1} →
  {motive_2 : (a : Ctx) → Ty a → Sort u_1} →
    {motive_3 : (Γ : Ctx) → (a : Ty Γ) → Tm Γ a → Sort u_1} →
      motive_1 Ctx.nil →
        ((Γ : Ctx) → (a : Ty Γ) → motive_1 Γ → motive_2 Γ a → motive_1 (Γ.snoc a)) →
          ((Γ : Ctx) → motive_1 Γ → motive_2 Γ (Ty.base Γ)) →
            ((Γ : Ctx) →
                (A : Ty Γ) →
                  (a : Ty (Γ.snoc A)) → motive_1 Γ → motive_2 Γ A → motive_2 (Γ.snoc A) a → motive_2 Γ (Ty.pi Γ A a)) →
              ((Γ : Ctx) → (A : Ty Γ) → motive_1 Γ → motive_2 Γ A → motive_3 Γ A (Tm.var Γ A)) →
                ((Γ : Ctx) →
                    (A : Ty Γ) →
                      (B : Ty (Γ.snoc A)) →
                        (a : Tm (Γ.snoc A) B) →
                          motive_1 Γ →
                            motive_2 Γ A →
                              motive_2 (Γ.snoc A) B → motive_3 (Γ.snoc A) B a → motive_3 Γ A (Tm.body Γ A B a)) →
                  {Γ : Ctx} → {a : Ty Γ} → (t : Tm Γ a) → motive_3 Γ a t
-/
#guard_msgs in
#check @Tm.rec

-- and here is what the move buys.  `Tm.var` and `Tm.body` are constructors of a
-- real inductive, so they are patterns, and the equation compiler will recurse
-- over them.  Against an erased member none of this can be written at all: its
-- constructors are `Subtype.mk`s whose arguments sit inside a proof, and a
-- pattern variable cannot be found in an inaccessible position
def size : {Γ : Ctx} → {A : Ty Γ} → Tm Γ A → Nat
  | _, _, .var _ _      => 1
  | _, _, .body _ _ _ t => size t + 1

example (Γ : Ctx) (A : Ty Γ) : size (Tm.var Γ A) = 1 := rfl
example (Γ : Ctx) (A : Ty Γ) (B : Ty (Ctx.snoc Γ A)) (t : Tm (Ctx.snoc Γ A) B) :
    size (Tm.body Γ A B t) = size t + 1 := rfl

/-- info: 2 -/
#guard_msgs in
#eval size (Tm.body .nil (.base .nil) (.base _) (.var _ (.base _)))

/-- info: 'DataOnDataTm.size' does not depend on any axioms -/
#guard_msgs in
#print axioms size

-- `induction` and `cases` are pointed at these, so a goal about `Tm` is stated
-- in the writer's names rather than in the inductive one name over.  They lose
-- nothing: discharging the other motives only drops hypotheses at fields the
-- kernel's own recursor over `Tm._ind` never offered one at either
/--
info: @Tm.recD : {motive : (Γ : Ctx) → (a : Ty Γ) → Tm Γ a → Sort u_1} →
  ((Γ : Ctx) → (A : Ty Γ) → motive Γ A (Tm.var Γ A)) →
    ((Γ : Ctx) →
        (A : Ty Γ) →
          (B : Ty (Γ.snoc A)) → (a : Tm (Γ.snoc A) B) → motive (Γ.snoc A) B a → motive Γ A (Tm.body Γ A B a)) →
      {Γ : Ctx} → {a : Ty Γ} → (t : Tm Γ a) → motive Γ a t
-/
#guard_msgs in
#check @Tm.recD

/--
info: @Tm.casesD : {motive : (Γ : Ctx) → (a : Ty Γ) → Tm Γ a → Sort u_1} →
  ((Γ : Ctx) → (A : Ty Γ) → motive Γ A (Tm.var Γ A)) →
    ((Γ : Ctx) → (A : Ty Γ) → (B : Ty (Γ.snoc A)) → (a : Tm (Γ.snoc A) B) → motive Γ A (Tm.body Γ A B a)) →
      {Γ : Ctx} → {a : Ty Γ} → (t : Tm Γ a) → motive Γ a t
-/
#guard_msgs in
#check @Tm.casesD

theorem size_pos {Γ : Ctx} {A : Ty Γ} (t : Tm Γ A) : 0 < size t := by
  induction t with
  | var Γ A => simp [size]
  | body Γ A B t ih => simp [size]

example {Γ : Ctx} {A : Ty Γ} (t : Tm Γ A) : True := by
  cases t with
  | var Γ A => trivial
  | body Γ A B t => trivial

-- the derived theorems come out under the writer's names too
example (Γ : Ctx) (A : Ty Γ) : Tm.var Γ A ≠ Tm.var Γ A → False := by simp

end DataOnDataTm

/-! ### A kept index beside a deleted one

Only an index whose type mentions the block has to go.  `Ty`'s `Nat` stays where
it was, in the arity and in the pre-type both, and the recursor's motive keeps
it in the position the writer put it in rather than after the one that left.
-/

namespace DataOnDataMixed

mutual
inductive Ctx : Type where
  | nil  : Ctx
  | snoc : Ctx → Ctx
inductive Ty : Nat → Ctx → Type where
  | base : (n : Nat) → (Γ : Ctx) → Ty n Γ
  | up   : (n : Nat) → (Γ : Ctx) → Ty n Γ → Ty (n + 1) Γ
end

/--
info: inductive DataOnDataMixed.Ty._pre : Nat → Type
number of parameters: 0
constructors:
DataOnDataMixed.Ty._pre.base : (n : Nat) → Ty._pre n
DataOnDataMixed.Ty._pre.up : (n : Nat) → Ty._pre n → Ty._pre (n + 1)
-/
#guard_msgs in
#print Ty._pre

/--
info: def DataOnDataMixed.Ty._wf : (a : Nat) → Ctx._pre → Ty._pre a → Prop :=
fun a a_1 t => Ty._pre.rec True (fun a ih => ih) (fun n Γ => True) (fun n a ih Γ => ih Γ) t a_1
-/
#guard_msgs in
#print Ty._wf

/--
info: @Ty.rec : {motive_1 : Ctx → Sort u_1} →
  {motive_2 : (a : Nat) → (a_1 : Ctx) → Ty a a_1 → Sort u_1} →
    motive_1 Ctx.nil →
      ((a : Ctx) → motive_1 a → motive_1 a.snoc) →
        ((n : Nat) → (Γ : Ctx) → motive_1 Γ → motive_2 n Γ (Ty.base n Γ)) →
          ((n : Nat) → (Γ : Ctx) → (a : Ty n Γ) → motive_1 Γ → motive_2 n Γ a → motive_2 (n + 1) Γ (Ty.up n Γ a)) →
            {a : Nat} → {a_1 : Ctx} → (t : Ty a a_1) → motive_2 a a_1 t
-/
#guard_msgs in
#check @Ty.rec

end DataOnDataMixed

/-! ### A kept index the deleted one is stated at

A context that carries its own length is how this shape is usually written, and
until now it was refused.  `Ty`'s deleted index is a `Ctx n`, and what the
erasure leaves of it, `Ctx._pre n`, still names `n` -- an index that stayed,
because a `Nat` is nothing the erasure deletes.

There is nothing wrong with that.  What the erasure really needs is that a
deleted index not name *another deleted* one, since the deleted indices are
handed round as an array and an array has nowhere for one entry to have bound
another.  A kept index is not in that array: it stays at the binder the arity
gave it, and everyone who has to state a deleted index's type has a value for it
to hand -- the motive at the arity's own binders, a minor premise at the
constructor's conclusion.
-/

namespace DataOnDataLength

mutual
inductive Ctx : Nat → Type where
  | nil  : Ctx 0
  | snoc : (n : Nat) → (Γ : Ctx n) → Ty n Γ → Ctx (n + 1)
inductive Ty : (n : Nat) → Ctx n → Type where
  | base : (n : Nat) → (Γ : Ctx n) → Ty n Γ
  | pi   : (n : Nat) → (Γ : Ctx n) → (A : Ty n Γ) → Ty (n + 1) (Ctx.snoc n Γ A) → Ty n Γ
end

/--
info: inductive DataOnDataLength.Ctx._pre : Nat → Type
number of parameters: 0
constructors:
DataOnDataLength.Ctx._pre.nil : Ctx._pre 0
DataOnDataLength.Ctx._pre.snoc : (n : Nat) → Ctx._pre n → Ty._pre n → Ctx._pre (n + 1)
-/
#guard_msgs in
#print Ctx._pre

/--
info: inductive DataOnDataLength.Ty._pre : Nat → Type
number of parameters: 0
constructors:
DataOnDataLength.Ty._pre.base : (n : Nat) → Ty._pre n
DataOnDataLength.Ty._pre.pi : (n : Nat) → Ty._pre n → Ty._pre (n + 1) → Ty._pre n
-/
#guard_msgs in
#print Ty._pre

/--
info: def DataOnDataLength.Ty._wf : (n : Nat) → Ctx._pre n → Ty._pre n → Prop :=
fun n a t =>
  Ty._pre.rec True (fun n Γ a ih ih_1 => ih ∧ ih_1 Γ) (fun n Γ => True)
    (fun n A a ih ih_1 Γ => ih Γ ∧ ih_1 (Ctx._pre.snoc n Γ A)) t a
-/
#guard_msgs in
#print Ty._wf

/--
info: @Ctx.rec : {motive_1 : (a : Nat) → Ctx a → Sort u_1} →
  {motive_2 : (n : Nat) → (a : Ctx n) → Ty n a → Sort u_1} →
    motive_1 0 Ctx.nil →
      ((n : Nat) → (Γ : Ctx n) → (a : Ty n Γ) → motive_1 n Γ → motive_2 n Γ a → motive_1 (n + 1) (Ctx.snoc n Γ a)) →
        ((n : Nat) → (Γ : Ctx n) → motive_1 n Γ → motive_2 n Γ (Ty.base n Γ)) →
          ((n : Nat) →
              (Γ : Ctx n) →
                (A : Ty n Γ) →
                  (a : Ty (n + 1) (Ctx.snoc n Γ A)) →
                    motive_1 n Γ →
                      motive_2 n Γ A → motive_2 (n + 1) (Ctx.snoc n Γ A) a → motive_2 n Γ (Ty.pi n Γ A a)) →
            {a : Nat} → (t : Ctx a) → motive_1 a t
-/
#guard_msgs in
#check @Ctx.rec

-- and it computes: the length of the context, read off the recursion rather
-- than off the index
def size : {n : Nat} → Ctx n → Nat :=
  fun {_} Γ => Ctx.rec (motive_1 := fun _ _ => Nat) (motive_2 := fun _ _ _ => Nat)
    0 (fun _ _ _ ih _ => ih + 1) (fun _ _ _ => 0) (fun _ _ _ _ _ _ ih => ih + 1) Γ

example : size .nil = 0 := rfl
example (n) (Γ : Ctx n) (A : Ty n Γ) : size (.snoc n Γ A) = size Γ + 1 := rfl
example : size (.snoc 0 .nil (.base 0 .nil)) = 1 := by decide

/-- info: 'DataOnDataLength.size' does not depend on any axioms -/
#guard_msgs in
#print axioms size

end DataOnDataLength

/-! ### A term layer over it, whose constructor builds a length-indexed type

`Tm.lam` ends in `Tm n Γ (Ty.pi n Γ A B)`, so its last index is no field of it
and the alternative binds one.  The type it is bound at, `Ty n Γ`, names the
kept index `n` as well as the deleted `Γ`, and is read at the values the
constructor's own conclusion gives them.
-/

namespace DataOnDataLengthTm

mutual
inductive Ctx : Nat → Type where
  | nil  : Ctx 0
  | snoc : (n : Nat) → (Γ : Ctx n) → Ty n Γ → Ctx (n + 1)
inductive Ty : (n : Nat) → Ctx n → Type where
  | base : (n : Nat) → (Γ : Ctx n) → Ty n Γ
  | pi   : (n : Nat) → (Γ : Ctx n) → (A : Ty n Γ) → Ty (n + 1) (Ctx.snoc n Γ A) → Ty n Γ
inductive Tm : (n : Nat) → (Γ : Ctx n) → Ty n Γ → Type where
  | var : (n : Nat) → (Γ : Ctx n) → (A : Ty n Γ) → Tm n Γ A
  | lam : (n : Nat) → (Γ : Ctx n) → (A : Ty n Γ) → (B : Ty (n + 1) (Ctx.snoc n Γ A)) →
      Tm (n + 1) (Ctx.snoc n Γ A) B → Tm n Γ (Ty.pi n Γ A B)
end

/--
info: @Tm.rec : {motive_1 : (a : Nat) → Ctx a → Sort u_1} →
  {motive_2 : (n : Nat) → (a : Ctx n) → Ty n a → Sort u_1} →
    {motive_3 : (n : Nat) → (Γ : Ctx n) → (a : Ty n Γ) → Tm n Γ a → Sort u_1} →
      motive_1 0 Ctx.nil →
        ((n : Nat) → (Γ : Ctx n) → (a : Ty n Γ) → motive_1 n Γ → motive_2 n Γ a → motive_1 (n + 1) (Ctx.snoc n Γ a)) →
          ((n : Nat) → (Γ : Ctx n) → motive_1 n Γ → motive_2 n Γ (Ty.base n Γ)) →
            ((n : Nat) →
                (Γ : Ctx n) →
                  (A : Ty n Γ) →
                    (a : Ty (n + 1) (Ctx.snoc n Γ A)) →
                      motive_1 n Γ →
                        motive_2 n Γ A → motive_2 (n + 1) (Ctx.snoc n Γ A) a → motive_2 n Γ (Ty.pi n Γ A a)) →
              ((n : Nat) → (Γ : Ctx n) → (A : Ty n Γ) → motive_1 n Γ → motive_2 n Γ A → motive_3 n Γ A (Tm.var n Γ A)) →
                ((n : Nat) →
                    (Γ : Ctx n) →
                      (A : Ty n Γ) →
                        (B : Ty (n + 1) (Ctx.snoc n Γ A)) →
                          (a : Tm (n + 1) (Ctx.snoc n Γ A) B) →
                            motive_1 n Γ →
                              motive_2 n Γ A →
                                motive_2 (n + 1) (Ctx.snoc n Γ A) B →
                                  motive_3 (n + 1) (Ctx.snoc n Γ A) B a →
                                    motive_3 n Γ (Ty.pi n Γ A B) (Tm.lam n Γ A B a)) →
                  {n : Nat} → {Γ : Ctx n} → {a : Ty n Γ} → (t : Tm n Γ a) → motive_3 n Γ a t
-/
#guard_msgs in
#check @Tm.rec

def size : {n : Nat} → {Γ : Ctx n} → {A : Ty n Γ} → Tm n Γ A → Nat :=
  fun {_} {_} {_} t => Tm.rec (motive_1 := fun _ _ => Nat) (motive_2 := fun _ _ _ => Nat)
    (motive_3 := fun _ _ _ _ => Nat)
    0 (fun _ _ _ a b => a + b + 1) (fun _ _ _ => 1) (fun _ _ _ _ _ a b => a + b + 1)
    (fun _ _ _ _ _ => 1) (fun _ _ _ _ _ _ _ _ ih => ih + 1) t

example (n) (Γ : Ctx n) (A : Ty n Γ) : size (.var n Γ A) = 1 := rfl
example (n) (Γ : Ctx n) (A : Ty n Γ) (B : Ty (n + 1) (.snoc n Γ A))
    (t : Tm (n + 1) (.snoc n Γ A) B) : size (.lam n Γ A B t) = size t + 1 := rfl

/-- info: 2 -/
#guard_msgs in
#eval size (.lam 0 .nil (.base 0 .nil) (.base 1 (.snoc 0 .nil (.base 0 .nil)))
  (.var 1 (.snoc 0 .nil (.base 0 .nil)) (.base 1 (.snoc 0 .nil (.base 0 .nil)))))

/-- info: 'DataOnDataLengthTm.size' does not depend on any axioms -/
#guard_msgs in
#print axioms size

end DataOnDataLengthTm

/-! ### The same, under a parameter and a universe parameter -/

namespace DataOnDataLengthUniv

universe u

mutual
inductive Ctx (α : Type u) : Nat → Type u where
  | nil  : Ctx α 0
  | snoc : (n : Nat) → (Γ : Ctx α n) → α → Ty α n Γ → Ctx α (n + 1)
inductive Ty (α : Type u) : (n : Nat) → Ctx α n → Type u where
  | base : (n : Nat) → (Γ : Ctx α n) → Ty α n Γ
end

/--
info: @Ty.rec : {α : Type u_2} →
  {motive_1 : (a : Nat) → Ctx α a → Sort u_1} →
    {motive_2 : (n : Nat) → (a : Ctx α n) → Ty α n a → Sort u_1} →
      motive_1 0 Ctx.nil →
        ((n : Nat) →
            (Γ : Ctx α n) →
              (a : α) → (a_1 : Ty α n Γ) → motive_1 n Γ → motive_2 n Γ a_1 → motive_1 (n + 1) (Ctx.snoc n Γ a a_1)) →
          ((n : Nat) → (Γ : Ctx α n) → motive_1 n Γ → motive_2 n Γ (Ty.base n Γ)) →
            {n : Nat} → {a : Ctx α n} → (t : Ty α n a) → motive_2 n a t
-/
#guard_msgs in
#check @Ty.rec

end DataOnDataLengthUniv

/-! ### A proposition over a context that carries its own length

The proposition is erased outright, so `Ok` is no index of anything, but it is
still stated at a `Ctx n` -- and its own recursion has to hand the data
recursion the length along with the context.
-/

namespace DataOnDataLengthProp

mutual
inductive Ctx : Nat → Type where
  | nil  : Ctx 0
  | snoc : (n : Nat) → (Γ : Ctx n) → Ty n Γ → Ctx (n + 1)
inductive Ty : (n : Nat) → Ctx n → Type where
  | base : (n : Nat) → (Γ : Ctx n) → Ty n Γ
inductive Ok : (n : Nat) → Ctx n → Prop where
  | nil  : Ok 0 Ctx.nil
  | snoc : (n : Nat) → (Γ : Ctx n) → (A : Ty n Γ) → Ok n Γ → Ok (n + 1) (Ctx.snoc n Γ A)
end

/--
info: @Ok.rec : ∀ {motive_1 : (a : Nat) → Ctx a → Sort u_1} {motive_2 : (n : Nat) → (a : Ctx n) → Ty n a → Sort u_1}
  {motive_3 : (n : Nat) → (a : Ctx n) → motive_1 n a → Ok n a → Prop} (nil : motive_1 0 Ctx.nil)
  (snoc : (n : Nat) → (Γ : Ctx n) → (a : Ty n Γ) → motive_1 n Γ → motive_2 n Γ a → motive_1 (n + 1) (Ctx.snoc n Γ a))
  (base : (n : Nat) → (Γ : Ctx n) → motive_1 n Γ → motive_2 n Γ (Ty.base n Γ)) (nil_1 : motive_3 0 Ctx.nil nil Ok.nil)
  (snoc_1 :
    ∀ (n : Nat) (Γ : Ctx n) (A : Ty n Γ) (a : Ok n Γ) (Γ_ih : motive_1 n Γ) (A_ih : motive_2 n Γ A),
      motive_3 n Γ Γ_ih a → motive_3 (n + 1) (Ctx.snoc n Γ A) (snoc n Γ A Γ_ih A_ih) ⋯)
  {n : Nat} {a : Ctx n} (h : Ok n a), motive_3 n a (Ctx.rec nil snoc base nil_1 snoc_1 a) h
-/
#guard_msgs in
#check @Ok.rec

/--
info: @Ctx.rec : {motive_1 : (a : Nat) → Ctx a → Sort u_1} →
  {motive_2 : (n : Nat) → (a : Ctx n) → Ty n a → Sort u_1} →
    {motive_3 : (n : Nat) → (a : Ctx n) → motive_1 n a → Ok n a → Prop} →
      (nil : motive_1 0 Ctx.nil) →
        (snoc :
            (n : Nat) →
              (Γ : Ctx n) → (a : Ty n Γ) → motive_1 n Γ → motive_2 n Γ a → motive_1 (n + 1) (Ctx.snoc n Γ a)) →
          ((n : Nat) → (Γ : Ctx n) → motive_1 n Γ → motive_2 n Γ (Ty.base n Γ)) →
            motive_3 0 Ctx.nil nil Ok.nil →
              (∀ (n : Nat) (Γ : Ctx n) (A : Ty n Γ) (a : Ok n Γ) (Γ_ih : motive_1 n Γ) (A_ih : motive_2 n Γ A),
                  motive_3 n Γ Γ_ih a → motive_3 (n + 1) (Ctx.snoc n Γ A) (snoc n Γ A Γ_ih A_ih) ⋯) →
                {a : Nat} → (t : Ctx a) → motive_1 a t
-/
#guard_msgs in
#check @Ctx.rec

-- every context is well-formed, which is the induction the block was written
-- for.  The recursion runs over the data and the proposition at once, so the
-- proof has to say something at `Ok` too, even when what it says is nothing
theorem ok : ∀ {n : Nat} (Γ : Ctx n), Ok n Γ :=
  fun {_} Γ => Ctx.rec (motive_1 := fun n Γ => Ok n Γ) (motive_2 := fun _ _ _ => True)
    (motive_3 := fun _ _ _ _ => True)
    Ok.nil (fun n Γ A ih _ => Ok.snoc n Γ A ih) (fun _ _ _ => trivial)
    trivial (fun _ _ _ _ _ _ _ => trivial) Γ

end DataOnDataLengthProp

/-! ### Two kept indices, one of which the deleted one is stated at -/

namespace DataOnDataLengthTwo

mutual
inductive Ctx : Nat → Bool → Type where
  | nil  : (b : Bool) → Ctx 0 b
  | snoc : (n : Nat) → (b : Bool) → (Γ : Ctx n b) → Ty n b Γ → Ctx (n + 1) b
inductive Ty : (n : Nat) → (b : Bool) → Ctx n b → Type where
  | base : (n : Nat) → (b : Bool) → (Γ : Ctx n b) → Ty n b Γ
end

/--
info: @Ty.rec : {motive_1 : (a : Nat) → (a_1 : Bool) → Ctx a a_1 → Sort u_1} →
  {motive_2 : (n : Nat) → (b : Bool) → (a : Ctx n b) → Ty n b a → Sort u_1} →
    ((b : Bool) → motive_1 0 b (Ctx.nil b)) →
      ((n : Nat) →
          (b : Bool) →
            (Γ : Ctx n b) →
              (a : Ty n b Γ) → motive_1 n b Γ → motive_2 n b Γ a → motive_1 (n + 1) b (Ctx.snoc n b Γ a)) →
        ((n : Nat) → (b : Bool) → (Γ : Ctx n b) → motive_1 n b Γ → motive_2 n b Γ (Ty.base n b Γ)) →
          {n : Nat} → {b : Bool} → {a : Ctx n b} → (t : Ty n b a) → motive_2 n b a t
-/
#guard_msgs in
#check @Ty.rec

end DataOnDataLengthTwo

/-! ### What else a kept index survives

The four things most likely to have been quietly relying on a deleted index
standing alone: a denesting over one, a conclusion that computes its kept index
out of two fields, a kept index written after the deleted one rather than
before, and a proposition stated at a member whose constructor builds a
length-indexed index.
-/

namespace DataOnDataLengthNest

mutual
inductive Ctx : Nat → Type where
  | nil  : Ctx 0
  | snoc : (n : Nat) → (Γ : Ctx n) → List (Ty n Γ) → Ctx (n + 1)
inductive Ty : (n : Nat) → Ctx n → Type where
  | base : (n : Nat) → (Γ : Ctx n) → Ty n Γ
end

-- the denested copy gets a motive of its own, stated over `List` at the kept
-- index as well as the deleted one
/--
info: @Ctx.rec : {motive_1 : (a : Nat) → Ctx a → Sort u_1} →
  {motive_2 : (n : Nat) → (a : Ctx n) → Ty n a → Sort u_1} →
    {motive_3 : (n : Nat) → (Γ : Ctx n) → List (Ty n Γ) → Sort u_1} →
      motive_1 0 Ctx.nil →
        ((n : Nat) →
            (Γ : Ctx n) → (a : List (Ty n Γ)) → motive_1 n Γ → motive_3 n Γ a → motive_1 (n + 1) (Ctx.snoc n Γ a)) →
          ((n : Nat) → (Γ : Ctx n) → motive_1 n Γ → motive_2 n Γ (Ty.base n Γ)) →
            ((n : Nat) → (Γ : Ctx n) → motive_1 n Γ → motive_3 n Γ []) →
              ((n : Nat) →
                  (Γ : Ctx n) →
                    (head : Ty n Γ) →
                      (tail : List (Ty n Γ)) →
                        motive_1 n Γ → motive_2 n Γ head → motive_3 n Γ tail → motive_3 n Γ (head :: tail)) →
                {a : Nat} → (t : Ctx a) → motive_1 a t
-/
#guard_msgs in
#check @Ctx.rec

end DataOnDataLengthNest

namespace DataOnDataLengthSum

mutual
inductive Ctx : Nat → Type where
  | nil  : Ctx 0
  | join : (n m : Nat) → (Γ : Ctx n) → (Δ : Ctx m) → Ty n Γ → Ctx (n + m)
inductive Ty : (n : Nat) → Ctx n → Type where
  | base : (n : Nat) → (Γ : Ctx n) → Ty n Γ
end

-- two recursive fields at two different lengths, and a conclusion at a third
/--
info: @Ctx.rec : {motive_1 : (a : Nat) → Ctx a → Sort u_1} →
  {motive_2 : (n : Nat) → (a : Ctx n) → Ty n a → Sort u_1} →
    motive_1 0 Ctx.nil →
      ((n m : Nat) →
          (Γ : Ctx n) →
            (Δ : Ctx m) →
              (a : Ty n Γ) → motive_1 n Γ → motive_1 m Δ → motive_2 n Γ a → motive_1 (n + m) (Ctx.join n m Γ Δ a)) →
        ((n : Nat) → (Γ : Ctx n) → motive_1 n Γ → motive_2 n Γ (Ty.base n Γ)) → {a : Nat} → (t : Ctx a) → motive_1 a t
-/
#guard_msgs in
#check @Ctx.rec

end DataOnDataLengthSum

namespace DataOnDataLengthAfter

mutual
inductive Ctx : Type where
  | nil  : Ctx
  | snoc : (Γ : Ctx) → Ty Γ 0 → Ctx
inductive Ty : Ctx → Nat → Type where
  | base : (Γ : Ctx) → (n : Nat) → Ty Γ n
end

-- the kept index is the second one, and `snoc` reads its field at a literal
/--
info: @Ty.rec : {motive_1 : Ctx → Sort u_1} →
  {motive_2 : (a : Ctx) → (a_1 : Nat) → Ty a a_1 → Sort u_1} →
    motive_1 Ctx.nil →
      ((Γ : Ctx) → (a : Ty Γ 0) → motive_1 Γ → motive_2 Γ 0 a → motive_1 (Γ.snoc a)) →
        ((Γ : Ctx) → (n : Nat) → motive_1 Γ → motive_2 Γ n (Ty.base Γ n)) →
          {a : Ctx} → {a_1 : Nat} → (t : Ty a a_1) → motive_2 a a_1 t
-/
#guard_msgs in
#check @Ty.rec

end DataOnDataLengthAfter

namespace DataOnDataLengthOk

mutual
inductive Ctx : Nat → Type where
  | nil  : Ctx 0
  | snoc : (n : Nat) → (Γ : Ctx n) → Ty n Γ → Ctx (n + 1)
inductive Ty : (n : Nat) → Ctx n → Type where
  | base : (n : Nat) → (Γ : Ctx n) → Ty n Γ
  | pi   : (n : Nat) → (Γ : Ctx n) → (A : Ty n Γ) → Ty (n + 1) (Ctx.snoc n Γ A) → Ty n Γ
inductive Ok : (n : Nat) → (Γ : Ctx n) → Ty n Γ → Prop where
  | base : (n : Nat) → (Γ : Ctx n) → Ok n Γ (Ty.base n Γ)
  | pi   : (n : Nat) → (Γ : Ctx n) → (A : Ty n Γ) → (B : Ty (n + 1) (Ctx.snoc n Γ A)) →
      Ok n Γ A → Ok (n + 1) (Ctx.snoc n Γ A) B → Ok n Γ (Ty.pi n Γ A B)
end

/--
info: @Ok.rec : ∀ {motive_1 : (a : Nat) → Ctx a → Sort u_1} {motive_2 : (n : Nat) → (a : Ctx n) → Ty n a → Sort u_1}
  {motive_3 : (n : Nat) → (Γ : Ctx n) → (a : Ty n Γ) → motive_2 n Γ a → Ok n Γ a → Prop} (nil : motive_1 0 Ctx.nil)
  (snoc : (n : Nat) → (Γ : Ctx n) → (a : Ty n Γ) → motive_1 n Γ → motive_2 n Γ a → motive_1 (n + 1) (Ctx.snoc n Γ a))
  (base : (n : Nat) → (Γ : Ctx n) → motive_1 n Γ → motive_2 n Γ (Ty.base n Γ))
  (pi :
    (n : Nat) →
      (Γ : Ctx n) →
        (A : Ty n Γ) →
          (a : Ty (n + 1) (Ctx.snoc n Γ A)) →
            motive_1 n Γ → motive_2 n Γ A → motive_2 (n + 1) (Ctx.snoc n Γ A) a → motive_2 n Γ (Ty.pi n Γ A a))
  (base_1 : ∀ (n : Nat) (Γ : Ctx n) (Γ_ih : motive_1 n Γ), motive_3 n Γ (Ty.base n Γ) (base n Γ Γ_ih) ⋯)
  (pi_1 :
    ∀ (n : Nat) (Γ : Ctx n) (A : Ty n Γ) (B : Ty (n + 1) (Ctx.snoc n Γ A)) (a : Ok n Γ A)
      (a_1 : Ok (n + 1) (Ctx.snoc n Γ A) B) (Γ_ih : motive_1 n Γ) (A_ih : motive_2 n Γ A)
      (B_ih : motive_2 (n + 1) (Ctx.snoc n Γ A) B),
      motive_3 n Γ A A_ih a →
        motive_3 (n + 1) (Ctx.snoc n Γ A) B B_ih a_1 → motive_3 n Γ (Ty.pi n Γ A B) (pi n Γ A B Γ_ih A_ih B_ih) ⋯)
  {n : Nat} {Γ : Ctx n} {a : Ty n Γ} (h : Ok n Γ a), motive_3 n Γ a (Ty.rec nil snoc base pi base_1 pi_1 a) h
-/
#guard_msgs in
#check @Ok.rec

-- and the proposition really is provable of everything, which is the recursion
-- the block was written to have
theorem ok : ∀ {n : Nat} {Γ : Ctx n} (A : Ty n Γ), Ok n Γ A :=
  fun {_} {_} A => Ty.rec (motive_1 := fun _ _ => True) (motive_2 := fun n Γ A => Ok n Γ A)
    (motive_3 := fun _ _ _ _ _ => True)
    trivial (fun _ _ _ _ _ => trivial)
    (fun n Γ _ => Ok.base n Γ) (fun n Γ A B _ ihA ihB => Ok.pi n Γ A B ihA ihB)
    (fun _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ _ _ _ => trivial) A

end DataOnDataLengthOk

/-! ### The tactics on a length-indexed block

Two data members, so both one-motive recursions have paid a sibling's
hypotheses -- and both remain what `induction` and `cases` reach for without
being told.  What is worth pinning here is the index: `Ctx.recD`'s conclusion
is at `motive a t` for an implicit `a`, so the tactic has two targets to
generalise rather than one, and `Ty.recD`'s minor for `pi` states its
hypothesis at the *built* index `Ctx.snoc n Γ A`.
-/

namespace DataOnDataLengthTac

mutual
inductive Ctx : Nat → Type where
  | nil  : Ctx 0
  | snoc : (n : Nat) → (Γ : Ctx n) → Ty n Γ → Ctx (n + 1)
inductive Ty : (n : Nat) → Ctx n → Type where
  | base : (n : Nat) → (Γ : Ctx n) → Ty n Γ
  | pi   : (n : Nat) → (Γ : Ctx n) → (A : Ty n Γ) → Ty (n + 1) (Ctx.snoc n Γ A) → Ty n Γ
end

/--
info: @Ctx.recD : {motive : (a : Nat) → Ctx a → Sort u_1} →
  motive 0 Ctx.nil →
    ((n : Nat) → (Γ : Ctx n) → (a : Ty n Γ) → motive n Γ → motive (n + 1) (Ctx.snoc n Γ a)) →
      {a : Nat} → (t : Ctx a) → motive a t
-/
#guard_msgs in
#check @Ctx.recD

/--
info: @Ty.recD : {motive : (n : Nat) → (a : Ctx n) → Ty n a → Sort u_1} →
  ((n : Nat) → (Γ : Ctx n) → motive n Γ (Ty.base n Γ)) →
    ((n : Nat) →
        (Γ : Ctx n) →
          (A : Ty n Γ) →
            (a : Ty (n + 1) (Ctx.snoc n Γ A)) →
              motive n Γ A → motive (n + 1) (Ctx.snoc n Γ A) a → motive n Γ (Ty.pi n Γ A a)) →
      {n : Nat} → {a : Ctx n} → (t : Ty n a) → motive n a t
-/
#guard_msgs in
#check @Ty.recD

def size : {n : Nat} → Ctx n → Nat := fun {_} Γ =>
  Ctx.recD (motive := fun _ _ => Nat) 0 (fun _ _ _ ih => ih + 1) Γ

example : size (.snoc 0 .nil (.base 0 .nil)) = 1 := rfl

-- no `using`, and the hypothesis is there
example {n : Nat} (Γ : Ctx n) : 0 ≤ size Γ := by
  induction Γ with
  | nil => simp [size]
  | snoc m Δ A ih => simp

-- the same for the member whose index the other one builds
example {n : Nat} (Γ : Ctx n) (A : Ty n Γ) : True := by
  induction A with
  | base m Δ => trivial
  | pi m Δ B C ihB ihC => trivial

-- and a case split, whose index here is built rather than a variable
example {n : Nat} (Γ : Ctx n) (B : Ty n Γ) (A : Ty (n + 1) (Ctx.snoc n Γ B)) : True := by
  cases A with
  | base m Δ => trivial
  | pi m Δ C D => trivial

end DataOnDataLengthTac

/-! ### A parameter and a universe parameter

A motive of the `_wf` recursion ends in the deleted indices, so it lands in the
`max` of their sorts and `Prop`'s own; a motive of a member that deleted nothing
lands in `Type` flat.  At `Type 0` those are the same sort and nothing shows.
Above it they are not, and since one recursion has one motive universe, every
motive is brought up to the highest by ending in a `PUnit` nobody reads.  It
appears in `_wf`'s body and nowhere in its statement.
-/

namespace DataOnDataUniv

universe u

mutual
inductive Ctx (α : Type u) : Type u where
  | nil  : Ctx α
  | snoc : (Γ : Ctx α) → α → Ty α Γ → Ctx α
inductive Ty (α : Type u) : Ctx α → Type u where
  | base : (Γ : Ctx α) → Ty α Γ
  | pi   : (Γ : Ctx α) → (a : α) → (A : Ty α Γ) → Ty α (Ctx.snoc Γ a A) → Ty α Γ
end

/--
info: def DataOnDataUniv.Ctx._wf.{u} : (α : Type u) → Ctx._pre α → Prop :=
fun α t =>
  Ctx._pre.rec (fun _pad => True) (fun Γ a a_1 ih ih_1 _pad => ih PUnit.unit ∧ ih_1 Γ PUnit.unit) (fun Γ _pad => True)
    (fun a A a_1 ih ih_1 Γ _pad => ih Γ PUnit.unit ∧ ih_1 (Γ.snoc a A) PUnit.unit) t PUnit.unit
-/
#guard_msgs in
#print Ctx._wf

/--
info: @Ctx.rec : {α : Type u_2} →
  {motive_1 : Ctx α → Sort u_1} →
    {motive_2 : (a : Ctx α) → Ty α a → Sort u_1} →
      motive_1 Ctx.nil →
        ((Γ : Ctx α) → (a : α) → (a_1 : Ty α Γ) → motive_1 Γ → motive_2 Γ a_1 → motive_1 (Γ.snoc a a_1)) →
          ((Γ : Ctx α) → motive_1 Γ → motive_2 Γ (Ty.base Γ)) →
            ((Γ : Ctx α) →
                (a : α) →
                  (A : Ty α Γ) →
                    (a_1 : Ty α (Γ.snoc a A)) →
                      motive_1 Γ → motive_2 Γ A → motive_2 (Γ.snoc a A) a_1 → motive_2 Γ (Ty.pi Γ a A a_1)) →
              (t : Ctx α) → motive_1 t
-/
#guard_msgs in
#check @Ctx.rec

def Ctx.len {α : Type u} : Ctx α → Nat :=
  Ctx.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    0 (fun _ _ _ n _ => n + 1) (fun _ _ => 0) (fun _ _ _ _ _ _ _ => 0)

/-- info: 1 -/
#guard_msgs in
#eval Ctx.len (α := Nat) (.snoc .nil 3 (.base .nil))

end DataOnDataUniv

/-! ### The same block a universe higher -/

namespace DataOnDataBig

mutual
inductive Ctx : Type 1 where
  | nil  : Ctx
  | snoc : (Γ : Ctx) → Ty Γ → Ctx
inductive Ty : Ctx → Type 1 where
  | base : (Γ : Ctx) → (α : Type) → Ty Γ
  | pi   : (Γ : Ctx) → (A : Ty Γ) → Ty (Ctx.snoc Γ A) → Ty Γ
end

/--
info: def DataOnDataBig.Ctx._wf : Ctx._pre → Prop :=
fun t =>
  Ctx._pre.rec (fun _pad => True) (fun Γ a ih ih_1 _pad => ih PUnit.unit ∧ ih_1 Γ PUnit.unit) (fun α Γ _pad => True)
    (fun A a ih ih_1 Γ _pad => ih Γ PUnit.unit ∧ ih_1 (Γ.snoc A) PUnit.unit) t PUnit.unit
-/
#guard_msgs in
#print Ctx._wf

/--
info: @Ty.rec : {motive_1 : Ctx → Sort u_1} →
  {motive_2 : (a : Ctx) → Ty a → Sort u_1} →
    motive_1 Ctx.nil →
      ((Γ : Ctx) → (a : Ty Γ) → motive_1 Γ → motive_2 Γ a → motive_1 (Γ.snoc a)) →
        ((Γ : Ctx) → (α : Type) → motive_1 Γ → motive_2 Γ (Ty.base Γ α)) →
          ((Γ : Ctx) →
              (A : Ty Γ) →
                (a : Ty (Γ.snoc A)) → motive_1 Γ → motive_2 Γ A → motive_2 (Γ.snoc A) a → motive_2 Γ (Ty.pi Γ A a)) →
            {a : Ctx} → (t : Ty a) → motive_2 a t
-/
#guard_msgs in
#check @Ty.rec

end DataOnDataBig

/-! ### A proposition over the whole thing

Both rules at once: the block indexes data by data *and* carries a proposition
over it.  A `Prop` constructor has no well-formedness of its own, so a data
field of one is put back at its subtype out of what the conclusion's indices
carry -- and where the member that field belongs to deleted an index, the fact
wanted is the one that names the deleted index too.

Such a block still gets the recursor over the whole block, which is the shape
that lets a `Prop` motive speak about the value the recursion produced.  Only
`Ty`'s minor is short of a hypothesis, and for the reason erasure gives: the
pre-constructor `Ty._pre.base` has no field where the context was, so there is
nothing the recursion recursed at to have one about.
-/

namespace DataOnDataProp

mutual
inductive Ctx : Type where
  | nil  : Ctx
  | snoc : (Γ : Ctx) → Ty Γ → Ctx
inductive Ty : Ctx → Type where
  | base : (Γ : Ctx) → Ty Γ
  | pi   : (Γ : Ctx) → (A : Ty Γ) → Ty (Ctx.snoc Γ A) → Ty Γ
inductive Ok : Ctx → Prop where
  | nil  : Ok Ctx.nil
  | snoc : (Γ : Ctx) → (A : Ty Γ) → Ok Γ → Ok (Ctx.snoc Γ A)
end

/--
info: @Ctx.rec : {motive_1 : Ctx → Sort u_1} →
  {motive_2 : (a : Ctx) → Ty a → Sort u_1} →
    {motive_3 : (a : Ctx) → motive_1 a → Ok a → Prop} →
      (nil : motive_1 Ctx.nil) →
        (snoc : (Γ : Ctx) → (a : Ty Γ) → motive_1 Γ → motive_2 Γ a → motive_1 (Γ.snoc a)) →
          ((Γ : Ctx) → motive_1 Γ → motive_2 Γ (Ty.base Γ)) →
            ((Γ : Ctx) →
                (A : Ty Γ) →
                  (a : Ty (Γ.snoc A)) → motive_1 Γ → motive_2 Γ A → motive_2 (Γ.snoc A) a → motive_2 Γ (Ty.pi Γ A a)) →
              motive_3 Ctx.nil nil Ok.nil →
                (∀ (Γ : Ctx) (A : Ty Γ) (a : Ok Γ) (Γ_ih : motive_1 Γ) (A_ih : motive_2 Γ A),
                    motive_3 Γ Γ_ih a → motive_3 (Γ.snoc A) (snoc Γ A Γ_ih A_ih) ⋯) →
                  (t : Ctx) → motive_1 t
-/
#guard_msgs in
#check @Ctx.rec

/--
info: @Ok.rec : ∀ {motive_1 : Ctx → Sort u_1} {motive_2 : (a : Ctx) → Ty a → Sort u_1}
  {motive_3 : (a : Ctx) → motive_1 a → Ok a → Prop} (nil : motive_1 Ctx.nil)
  (snoc : (Γ : Ctx) → (a : Ty Γ) → motive_1 Γ → motive_2 Γ a → motive_1 (Γ.snoc a))
  (base : (Γ : Ctx) → motive_1 Γ → motive_2 Γ (Ty.base Γ))
  (pi :
    (Γ : Ctx) →
      (A : Ty Γ) → (a : Ty (Γ.snoc A)) → motive_1 Γ → motive_2 Γ A → motive_2 (Γ.snoc A) a → motive_2 Γ (Ty.pi Γ A a))
  (nil_1 : motive_3 Ctx.nil nil Ok.nil)
  (snoc_1 :
    ∀ (Γ : Ctx) (A : Ty Γ) (a : Ok Γ) (Γ_ih : motive_1 Γ) (A_ih : motive_2 Γ A),
      motive_3 Γ Γ_ih a → motive_3 (Γ.snoc A) (snoc Γ A Γ_ih A_ih) ⋯)
  {a : Ctx} (h : Ok a), motive_3 a (Ctx.rec nil snoc base pi nil_1 snoc_1 a) h
-/
#guard_msgs in
#check @Ok.rec

example : Ok (Ctx.snoc Ctx.nil (Ty.base Ctx.nil)) := Ok.snoc _ _ Ok.nil

-- and the data recursion can be run at a proposition, which is where the two
-- halves have to agree about what a `Ty Γ` is
theorem ok_all : ∀ Γ : Ctx, Ok Γ :=
  Ctx.rec (motive_1 := fun Γ => Ok Γ) (motive_2 := fun _ _ => PUnit)
    (motive_3 := fun _ _ _ => True)
    Ok.nil (fun Γ A h _ => Ok.snoc Γ A h) (fun _ _ => ⟨⟩) (fun _ _ _ _ _ _ => ⟨⟩)
    trivial (fun _ _ _ _ _ _ => trivial)

-- and it still computes, with the bundle the proposition rides in and the index
-- `Ty` deleted both in the way.  The `Prop` motive is what the length is
-- declared *about*: `n` is the number the recursion produced, so the minors
-- below prove it non-negative as they go
def Ctx.len : Ctx → Nat :=
  Ctx.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    (motive_3 := fun _ n _ => 0 ≤ n)
    0 (fun _ _ n _ => n + 1) (fun _ _ => 0) (fun _ _ _ _ _ b => b)
    (Nat.le_refl 0) (fun _ _ _ _ _ h => Nat.le_trans h (Nat.le_succ _))

example : Ctx.len Ctx.nil = 0 := rfl
example (Γ : Ctx) (A : Ty Γ) : Ctx.len (Γ.snoc A) = Ctx.len Γ + 1 := rfl

/-- info: 2 -/
#guard_msgs in
#eval Ctx.len (.snoc (.snoc .nil (.base .nil)) (.base (.snoc .nil (.base .nil))))

-- and the proposition comes back out at the very function that was declared
-- with it, which is the whole point of the one recursion: `Ok.rec` at these
-- motives and minors concludes about `Ctx.rec` at the same ones, and that is
-- what `Ctx.len` unfolds to
theorem ok_pos : ∀ {Γ : Ctx}, Ok Γ → 0 ≤ Ctx.len Γ :=
  Ok.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    (motive_3 := fun _ n _ => 0 ≤ n)
    0 (fun _ _ n _ => n + 1) (fun _ _ => 0) (fun _ _ _ _ _ b => b)
    (Nat.le_refl 0) (fun _ _ _ _ _ h => Nat.le_trans h (Nat.le_succ _))

end DataOnDataProp

/-! ### A proposition indexed by two data members

`Ok`'s second index is a `Ty Γ`, so putting it back takes the first index with
it -- which is exactly what makes one bundle enough.  A bundle holds the
hypotheses about a single data value, and here the later index settles the
earlier one: fixing the `Ty` fixes the `Ctx` it is over.  So the proposition
rides in the `Ty` bundle, and its motive takes the value of the `Ty` half.

`Ok.base`'s only field is the very index `Ty.base` deleted, so nothing in the
recursion recursed at it; the hypothesis the deleted index arrived with is what
stands in, which is why the minor has a `Γ_ih` its constructor has no field for.

`Ok` is a subsingleton, and a subsingleton's own recursor eliminates into any
sort.  Joining the recursion costs that: a bundle's proof components are
conjuncts, so a `Prop` member in one is eliminated into `Prop`.  What it buys is
the other half -- a data function may be declared with this proposition's motive
on it, which is the only way to say anything about the function itself.
-/

namespace DataOnDataTwo

mutual
inductive Ctx : Type where
  | nil  : Ctx
  | snoc : (Γ : Ctx) → Ty Γ → Ctx
inductive Ty : Ctx → Type where
  | base : (Γ : Ctx) → Ty Γ
inductive Ok : (Γ : Ctx) → Ty Γ → Prop where
  | base : (Γ : Ctx) → Ok Γ (Ty.base Γ)
end

/--
info: @Ok.rec : ∀ {motive_1 : Ctx → Sort u_1} {motive_2 : (a : Ctx) → Ty a → Sort u_1}
  {motive_3 : (Γ : Ctx) → (a : Ty Γ) → motive_2 Γ a → Ok Γ a → Prop} (nil : motive_1 Ctx.nil)
  (snoc : (Γ : Ctx) → (a : Ty Γ) → motive_1 Γ → motive_2 Γ a → motive_1 (Γ.snoc a))
  (base : (Γ : Ctx) → motive_1 Γ → motive_2 Γ (Ty.base Γ))
  (base_1 : ∀ (Γ : Ctx) (Γ_ih : motive_1 Γ), motive_3 Γ (Ty.base Γ) (base Γ Γ_ih) ⋯) {Γ : Ctx} {a : Ty Γ} (h : Ok Γ a),
  motive_3 Γ a (Ty.rec nil snoc base base_1 a) h
-/
#guard_msgs in
#check @Ok.rec

/--
info: @Ok.casesP : ∀ {motive : (Γ : Ctx) → (a : Ty Γ) → Ok Γ a → Prop},
  (∀ (Γ : Ctx), motive Γ (Ty.base Γ) ⋯) → ∀ {Γ : Ctx} {a : Ty Γ} (h : Ok Γ a), motive Γ a h
-/
#guard_msgs in
#check @Ok.casesP

-- the size of a type, declared with the proposition it is about, so that the
-- one recursion serves both halves.  `Ty.size` is what `Ok.rec` at the same
-- motives and minors concludes about
def Ty.size : {Γ : Ctx} → Ty Γ → Nat :=
  fun {_} t =>
    Ty.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
      (motive_3 := fun _ _ n _ => 0 < n)
      0 (fun _ _ n _ => n + 1) (fun _ _ => 1)
      (fun _ _ => Nat.zero_lt_one) t

example (Γ : Ctx) : (Ty.base Γ).size = 1 := rfl

theorem Ok.size_pos : ∀ {Γ : Ctx} {A : Ty Γ}, Ok Γ A → 0 < A.size :=
  Ok.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    (motive_3 := fun _ _ n _ => 0 < n)
    0 (fun _ _ n _ => n + 1) (fun _ _ => 1)
    (fun _ _ => Nat.zero_lt_one)

end DataOnDataTwo

/-! ### A judgement over three data indices

The shape a type theory is actually written in: a term judgement standing over
a context, a type in it, and a term of that type.  The last index is the one
that settles the rest, and it settles them completely -- a `Tm Γ A` names both
the `Γ` and the `A` -- so the whole judgement rides in the `Tm` bundle, and its
motive reads the value of the `Tm` half.

`Good.wk` shows both ways a hypothesis can arrive at once.  `Tm.wk` deleted the
`Γ` and the target `B`, so those two come in as hypotheses of their own,
`Γ_ih` and `B_ih`, ahead of the ones the fields bring; `A` and `t` are ordinary
fields and bring `A_ih` and `t_ih`.  Only the field hypotheses reach the data
minor's value, which is why the conclusion is about `wk Γ A B t A_ih t_ih` and
not about the other two.
-/

namespace DataOnDataJudge

mutual
inductive Ctx : Type where
  | nil  : Ctx
  | snoc : (Γ : Ctx) → Ty Γ → Ctx
inductive Ty : Ctx → Type where
  | base : (Γ : Ctx) → Ty Γ
inductive Tm : (Γ : Ctx) → Ty Γ → Type where
  | var : (Γ : Ctx) → (A : Ty Γ) → Tm Γ A
  | wk  : (Γ : Ctx) → (A : Ty Γ) → (B : Ty Γ) → Tm Γ A → Tm Γ B
inductive Good : (Γ : Ctx) → (A : Ty Γ) → Tm Γ A → Prop where
  | var : (Γ : Ctx) → (A : Ty Γ) → Good Γ A (Tm.var Γ A)
  | wk  : (Γ : Ctx) → (A : Ty Γ) → (B : Ty Γ) → (t : Tm Γ A) →
      Good Γ A t → Good Γ B (Tm.wk Γ A B t)
end

/--
info: @Good.rec : ∀ {motive_1 : Ctx → Sort u_1} {motive_2 : (a : Ctx) → Ty a → Sort u_1}
  {motive_3 : (Γ : Ctx) → (a : Ty Γ) → Tm Γ a → Sort u_1}
  {motive_4 : (Γ : Ctx) → (A : Ty Γ) → (a : Tm Γ A) → motive_3 Γ A a → Good Γ A a → Prop} (nil : motive_1 Ctx.nil)
  (snoc : (Γ : Ctx) → (a : Ty Γ) → motive_1 Γ → motive_2 Γ a → motive_1 (Γ.snoc a))
  (base : (Γ : Ctx) → motive_1 Γ → motive_2 Γ (Ty.base Γ))
  (var : (Γ : Ctx) → (A : Ty Γ) → motive_1 Γ → motive_2 Γ A → motive_3 Γ A (Tm.var Γ A))
  (wk :
    (Γ : Ctx) →
      (A B : Ty Γ) →
        (a : Tm Γ A) → motive_1 Γ → motive_2 Γ A → motive_2 Γ B → motive_3 Γ A a → motive_3 Γ B (Tm.wk Γ A B a))
  (var_1 :
    ∀ (Γ : Ctx) (A : Ty Γ) (Γ_ih : motive_1 Γ) (A_ih : motive_2 Γ A), motive_4 Γ A (Tm.var Γ A) (var Γ A Γ_ih A_ih) ⋯)
  (wk_1 :
    ∀ (Γ : Ctx) (A B : Ty Γ) (t : Tm Γ A) (a : Good Γ A t) (Γ_ih : motive_1 Γ) (A_ih : motive_2 Γ A)
      (B_ih : motive_2 Γ B) (t_ih : motive_3 Γ A t),
      motive_4 Γ A t t_ih a → motive_4 Γ B (Tm.wk Γ A B t) (wk Γ A B t Γ_ih A_ih B_ih t_ih) ⋯)
  {Γ : Ctx} {A : Ty Γ} {a : Tm Γ A} (h : Good Γ A a), motive_4 Γ A a (Tm.rec nil snoc base var wk var_1 wk_1 a) h
-/
#guard_msgs in
#check @Good.rec

/--
info: @Good.casesP : ∀ {motive : (Γ : Ctx) → (A : Ty Γ) → (a : Tm Γ A) → Good Γ A a → Prop},
  (∀ (Γ : Ctx) (A : Ty Γ), motive Γ A (Tm.var Γ A) ⋯) →
    (∀ (Γ : Ctx) (A B : Ty Γ) (t : Tm Γ A) (a : Good Γ A t), motive Γ B (Tm.wk Γ A B t) ⋯) →
      ∀ {Γ : Ctx} {A : Ty Γ} {a : Tm Γ A} (h : Good Γ A a), motive Γ A a h
-/
#guard_msgs in
#check @Good.casesP

def Tm.size : {Γ : Ctx} → {A : Ty Γ} → Tm Γ A → Nat :=
  fun {_} {_} t =>
    Tm.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
      (motive_3 := fun _ _ _ => Nat) (motive_4 := fun _ _ _ n _ => 0 < n)
      0 (fun _ _ n _ => n + 1) (fun _ _ => 0)
      (fun _ _ _ _ => 1) (fun _ _ _ _ _ _ _ n => n + 1)
      (fun _ _ _ _ => Nat.zero_lt_one)
      (fun _ _ _ _ _ _ _ _ _ _ => Nat.succ_pos _) t

example (Γ : Ctx) (A : Ty Γ) : (Tm.var Γ A).size = 1 := rfl
example (Γ : Ctx) (A B : Ty Γ) : (Tm.wk Γ A B (Tm.var Γ A)).size = 2 := rfl

theorem Good.size_pos : ∀ {Γ : Ctx} {A : Ty Γ} {t : Tm Γ A}, Good Γ A t → 0 < t.size :=
  Good.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    (motive_3 := fun _ _ _ => Nat) (motive_4 := fun _ _ _ n _ => 0 < n)
    0 (fun _ _ n _ => n + 1) (fun _ _ => 0)
    (fun _ _ _ _ => 1) (fun _ _ _ _ _ _ _ n => n + 1)
    (fun _ _ _ _ => Nat.zero_lt_one)
    (fun _ _ _ _ _ _ _ _ _ _ => Nat.succ_pos _)

end DataOnDataJudge

/-! ### Two propositions with different data hosts

Nothing about a bundle is per-proposition: a data member's bundle holds
whichever propositions chose it, and each proposition chooses by its own last
data index.  Here they choose differently -- `Ok` rides in `Ctx`'s bundle and
`Wf` in `Ty`'s -- and the recursion is still the one recursion.  `Ok.rec` and
`Wf.rec` take the same four motives and the same six minors as each other and
as `Ctx.rec`; all that differs is which of the two data recursors the
conclusion is stated about.

So the four declarations below are the same recursion read four ways: two
functions and the two propositions about them, off one set of minors.
-/

namespace DataOnDataTwoProps

mutual
inductive Ctx : Type where
  | nil  : Ctx
  | snoc : (Γ : Ctx) → Ty Γ → Ctx
inductive Ty : Ctx → Type where
  | base : (Γ : Ctx) → Ty Γ
inductive Ok : Ctx → Prop where
  | nil  : Ok Ctx.nil
  | snoc : (Γ : Ctx) → (A : Ty Γ) → Ok Γ → Ok (Ctx.snoc Γ A)
inductive Wf : (Γ : Ctx) → Ty Γ → Prop where
  | base : (Γ : Ctx) → Wf Γ (Ty.base Γ)
end

/--
info: @Ok.rec : ∀ {motive_1 : Ctx → Sort u_1} {motive_2 : (a : Ctx) → Ty a → Sort u_1}
  {motive_3 : (a : Ctx) → motive_1 a → Ok a → Prop} {motive_4 : (Γ : Ctx) → (a : Ty Γ) → motive_2 Γ a → Wf Γ a → Prop}
  (nil : motive_1 Ctx.nil) (snoc : (Γ : Ctx) → (a : Ty Γ) → motive_1 Γ → motive_2 Γ a → motive_1 (Γ.snoc a))
  (base : (Γ : Ctx) → motive_1 Γ → motive_2 Γ (Ty.base Γ)) (nil_1 : motive_3 Ctx.nil nil Ok.nil)
  (snoc_1 :
    ∀ (Γ : Ctx) (A : Ty Γ) (a : Ok Γ) (Γ_ih : motive_1 Γ) (A_ih : motive_2 Γ A),
      motive_3 Γ Γ_ih a → motive_3 (Γ.snoc A) (snoc Γ A Γ_ih A_ih) ⋯)
  (base_1 : ∀ (Γ : Ctx) (Γ_ih : motive_1 Γ), motive_4 Γ (Ty.base Γ) (base Γ Γ_ih) ⋯) {a : Ctx} (h : Ok a),
  motive_3 a (Ctx.rec nil snoc base nil_1 snoc_1 base_1 a) h
-/
#guard_msgs in
#check @Ok.rec

/--
info: @Wf.rec : ∀ {motive_1 : Ctx → Sort u_1} {motive_2 : (a : Ctx) → Ty a → Sort u_1}
  {motive_3 : (a : Ctx) → motive_1 a → Ok a → Prop} {motive_4 : (Γ : Ctx) → (a : Ty Γ) → motive_2 Γ a → Wf Γ a → Prop}
  (nil : motive_1 Ctx.nil) (snoc : (Γ : Ctx) → (a : Ty Γ) → motive_1 Γ → motive_2 Γ a → motive_1 (Γ.snoc a))
  (base : (Γ : Ctx) → motive_1 Γ → motive_2 Γ (Ty.base Γ)) (nil_1 : motive_3 Ctx.nil nil Ok.nil)
  (snoc_1 :
    ∀ (Γ : Ctx) (A : Ty Γ) (a : Ok Γ) (Γ_ih : motive_1 Γ) (A_ih : motive_2 Γ A),
      motive_3 Γ Γ_ih a → motive_3 (Γ.snoc A) (snoc Γ A Γ_ih A_ih) ⋯)
  (base_1 : ∀ (Γ : Ctx) (Γ_ih : motive_1 Γ), motive_4 Γ (Ty.base Γ) (base Γ Γ_ih) ⋯) {Γ : Ctx} {a : Ty Γ} (h : Wf Γ a),
  motive_4 Γ a (Ty.rec nil snoc base nil_1 snoc_1 base_1 a) h
-/
#guard_msgs in
#check @Wf.rec

def Ctx.size : Ctx → Nat :=
  Ctx.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    (motive_3 := fun _ n _ => 0 < n) (motive_4 := fun _ _ m _ => 0 < m)
    1 (fun _ _ n _ => n + 1) (fun _ _ => 1)
    Nat.zero_lt_one (fun _ _ _ _ _ _ => Nat.succ_pos _)
    (fun _ _ => Nat.zero_lt_one)

def Ty.size : {Γ : Ctx} → Ty Γ → Nat :=
  fun {_} A =>
    Ty.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
      (motive_3 := fun _ n _ => 0 < n) (motive_4 := fun _ _ m _ => 0 < m)
      1 (fun _ _ n _ => n + 1) (fun _ _ => 1)
      Nat.zero_lt_one (fun _ _ _ _ _ _ => Nat.succ_pos _)
      (fun _ _ => Nat.zero_lt_one) A

/-- info: 3 -/
#guard_msgs in
#eval Ctx.size (.snoc (.snoc .nil (.base .nil)) (.base (.snoc .nil (.base .nil))))

example (Γ : Ctx) : (Ty.base Γ).size = 1 := rfl

theorem Ok.size_pos : ∀ {Γ : Ctx}, Ok Γ → 0 < Γ.size :=
  Ok.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    (motive_3 := fun _ n _ => 0 < n) (motive_4 := fun _ _ m _ => 0 < m)
    1 (fun _ _ n _ => n + 1) (fun _ _ => 1)
    Nat.zero_lt_one (fun _ _ _ _ _ _ => Nat.succ_pos _)
    (fun _ _ => Nat.zero_lt_one)

theorem Wf.size_pos : ∀ {Γ : Ctx} {A : Ty Γ}, Wf Γ A → 0 < A.size :=
  Wf.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    (motive_3 := fun _ n _ => 0 < n) (motive_4 := fun _ _ m _ => 0 < m)
    1 (fun _ _ n _ => n + 1) (fun _ _ => 1)
    Nat.zero_lt_one (fun _ _ _ _ _ _ => Nat.succ_pos _)
    (fun _ _ => Nat.zero_lt_one)

end DataOnDataTwoProps

/-! ### A proposition naming another at a deleted index

`Wf.base : (Γ : Ctx) → Ok Γ → Wf Γ (Ty.base Γ)` -- a base type is well formed in
a well-formed context -- wants a proof about the very `Γ` that `Ty.base` deleted.
So the hypothesis a deleted index arrives under has to carry the propositions
about that index and not just the motive's value, or there is nothing to state
the `Ok` field's induction hypothesis over.

Carrying them is not free: what carries them is the bundle, and a bundle can be
recursed into but not rebuilt out of a minor, so a deleted index built out of a
constructor -- the `Ty.pi` shape a few sections up -- can no longer be handed
one.  Neither reading covers the other, so the elaborator tries this one and
falls back to the plain one.  Which it settled on is invisible either way: the
minor below reads `∀ (Γ : Ctx) (a : Ok Γ) (Γ_ih : motive_1 Γ), motive_3 Γ Γ_ih a
→ ...`, with the `Ok` hypothesis stated over the deleted index's own and no
bundle in sight.
-/

namespace DataOnDataPropOnProp

mutual
inductive Ctx : Type where
  | nil  : Ctx
  | snoc : (Γ : Ctx) → Ty Γ → Ctx
inductive Ty : Ctx → Type where
  | base : (Γ : Ctx) → Ty Γ
inductive Ok : Ctx → Prop where
  | nil  : Ok Ctx.nil
  | snoc : (Γ : Ctx) → (A : Ty Γ) → Ok Γ → Ok (Ctx.snoc Γ A)
inductive Wf : (Γ : Ctx) → Ty Γ → Prop where
  | base : (Γ : Ctx) → Ok Γ → Wf Γ (Ty.base Γ)
end

/--
info: @Wf.rec : ∀ {motive_1 : Ctx → Sort u_1} {motive_2 : (a : Ctx) → Ty a → Sort u_1}
  {motive_3 : (a : Ctx) → motive_1 a → Ok a → Prop} {motive_4 : (Γ : Ctx) → (a : Ty Γ) → motive_2 Γ a → Wf Γ a → Prop}
  (nil : motive_1 Ctx.nil) (snoc : (Γ : Ctx) → (a : Ty Γ) → motive_1 Γ → motive_2 Γ a → motive_1 (Γ.snoc a))
  (base : (Γ : Ctx) → motive_1 Γ → motive_2 Γ (Ty.base Γ)) (nil_1 : motive_3 Ctx.nil nil Ok.nil)
  (snoc_1 :
    ∀ (Γ : Ctx) (A : Ty Γ) (a : Ok Γ) (Γ_ih : motive_1 Γ) (A_ih : motive_2 Γ A),
      motive_3 Γ Γ_ih a → motive_3 (Γ.snoc A) (snoc Γ A Γ_ih A_ih) ⋯)
  (base_1 : ∀ (Γ : Ctx) (a : Ok Γ) (Γ_ih : motive_1 Γ), motive_3 Γ Γ_ih a → motive_4 Γ (Ty.base Γ) (base Γ Γ_ih) ⋯)
  {Γ : Ctx} {a : Ty Γ} (h : Wf Γ a), motive_4 Γ a (Ty.rec nil snoc base nil_1 snoc_1 base_1 a) h
-/
#guard_msgs in
#check @Wf.rec

-- the inversion lemma, which is what the new hypothesis is for: the `Ok` of
-- `Wf.base` is about a `Γ` no data field of `Ty.base` mentions, so without an
-- induction hypothesis at it there is nothing to conclude from
theorem Wf.ok : ∀ {Γ : Ctx} {A : Ty Γ}, Wf Γ A → Ok Γ :=
  Wf.rec (motive_1 := fun _ => Unit) (motive_2 := fun _ _ => Unit)
    (motive_3 := fun Γ _ _ => Ok Γ) (motive_4 := fun Γ _ _ _ => Ok Γ)
    () (fun _ _ _ _ => ()) (fun _ _ => ())
    Ok.nil (fun Γ A _ _ _ h => Ok.snoc Γ A h)
    (fun _ _ _ h => h)

def Ctx.size : Ctx → Nat :=
  Ctx.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    (motive_3 := fun _ n _ => 0 < n) (motive_4 := fun _ _ m _ => 0 < m)
    1 (fun _ _ n _ => n + 1) (fun _ _ => 1)
    Nat.zero_lt_one (fun _ _ _ _ _ _ => Nat.succ_pos _)
    (fun _ _ _ _ => Nat.zero_lt_one)

/-- info: 2 -/
#guard_msgs in
#eval Ctx.size (.snoc .nil (.base .nil))

theorem Ok.size_pos : ∀ {Γ : Ctx}, Ok Γ → 0 < Γ.size :=
  Ok.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    (motive_3 := fun _ n _ => 0 < n) (motive_4 := fun _ _ m _ => 0 < m)
    1 (fun _ _ n _ => n + 1) (fun _ _ => 1)
    Nat.zero_lt_one (fun _ _ _ _ _ _ => Nat.succ_pos _)
    (fun _ _ _ _ => Nat.zero_lt_one)

end DataOnDataPropOnProp

/-! ### A derivation stack

Three data members and three propositions, each proposition naming the one below
it: a context is well formed, a type is well formed in a well-formed context, a
term is good at a well-formed type.  That is a whole judgement stack, and it is
one recursion over six motives -- each proposition rides the bundle of the data
member its last index names, and the hypothesis it wants about the proposition
below is in the bundle it already has.

The two theorems below are the same recursion at two sets of motives.  The
second is the one the stack exists for: `Good Γ A t → Ok Γ` reaches down two
levels, through the `Wf` a good term's type carries and the `Ok` a well-formed
type's context carries, and neither step is a separate induction.
-/

namespace DataOnDataStack

mutual
inductive Ctx : Type where
  | nil  : Ctx
  | snoc : (Γ : Ctx) → Ty Γ → Ctx
inductive Ty : Ctx → Type where
  | base : (Γ : Ctx) → Ty Γ
inductive Tm : (Γ : Ctx) → Ty Γ → Type where
  | var : (Γ : Ctx) → (A : Ty Γ) → Tm Γ A
inductive Ok : Ctx → Prop where
  | nil  : Ok Ctx.nil
  | snoc : (Γ : Ctx) → (A : Ty Γ) → Ok Γ → Ok (Ctx.snoc Γ A)
inductive Wf : (Γ : Ctx) → Ty Γ → Prop where
  | base : (Γ : Ctx) → Ok Γ → Wf Γ (Ty.base Γ)
inductive Good : (Γ : Ctx) → (A : Ty Γ) → Tm Γ A → Prop where
  | var : (Γ : Ctx) → (A : Ty Γ) → Wf Γ A → Good Γ A (Tm.var Γ A)
end

/--
info: @Good.rec : ∀ {motive_1 : Ctx → Sort u_1} {motive_2 : (a : Ctx) → Ty a → Sort u_1}
  {motive_3 : (Γ : Ctx) → (a : Ty Γ) → Tm Γ a → Sort u_1} {motive_4 : (a : Ctx) → motive_1 a → Ok a → Prop}
  {motive_5 : (Γ : Ctx) → (a : Ty Γ) → motive_2 Γ a → Wf Γ a → Prop}
  {motive_6 : (Γ : Ctx) → (A : Ty Γ) → (a : Tm Γ A) → motive_3 Γ A a → Good Γ A a → Prop} (nil : motive_1 Ctx.nil)
  (snoc : (Γ : Ctx) → (a : Ty Γ) → motive_1 Γ → motive_2 Γ a → motive_1 (Γ.snoc a))
  (base : (Γ : Ctx) → motive_1 Γ → motive_2 Γ (Ty.base Γ))
  (var : (Γ : Ctx) → (A : Ty Γ) → motive_1 Γ → motive_2 Γ A → motive_3 Γ A (Tm.var Γ A))
  (nil_1 : motive_4 Ctx.nil nil Ok.nil)
  (snoc_1 :
    ∀ (Γ : Ctx) (A : Ty Γ) (a : Ok Γ) (Γ_ih : motive_1 Γ) (A_ih : motive_2 Γ A),
      motive_4 Γ Γ_ih a → motive_4 (Γ.snoc A) (snoc Γ A Γ_ih A_ih) ⋯)
  (base_1 : ∀ (Γ : Ctx) (a : Ok Γ) (Γ_ih : motive_1 Γ), motive_4 Γ Γ_ih a → motive_5 Γ (Ty.base Γ) (base Γ Γ_ih) ⋯)
  (var_1 :
    ∀ (Γ : Ctx) (A : Ty Γ) (a : Wf Γ A) (Γ_ih : motive_1 Γ) (A_ih : motive_2 Γ A),
      motive_5 Γ A A_ih a → motive_6 Γ A (Tm.var Γ A) (var Γ A Γ_ih A_ih) ⋯)
  {Γ : Ctx} {A : Ty Γ} {a : Tm Γ A} (h : Good Γ A a),
  motive_6 Γ A a (Tm.rec nil snoc base var nil_1 snoc_1 base_1 var_1 a) h
-/
#guard_msgs in
#check @Good.rec

def Tm.size : {Γ : Ctx} → {A : Ty Γ} → Tm Γ A → Nat :=
  fun {_} {_} t =>
    Tm.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
      (motive_3 := fun _ _ _ => Nat) (motive_4 := fun _ n _ => 0 < n)
      (motive_5 := fun _ _ m _ => 0 < m) (motive_6 := fun _ _ _ k _ => 0 < k)
      1 (fun _ _ n _ => n + 1) (fun _ _ => 1) (fun _ _ _ _ => 1)
      Nat.zero_lt_one (fun _ _ _ _ _ _ => Nat.succ_pos _)
      (fun _ _ _ _ => Nat.zero_lt_one) (fun _ _ _ _ _ _ => Nat.zero_lt_one) t

example (Γ : Ctx) (A : Ty Γ) : (Tm.var Γ A).size = 1 := rfl

theorem Good.size_pos : ∀ {Γ : Ctx} {A : Ty Γ} {t : Tm Γ A}, Good Γ A t → 0 < t.size :=
  Good.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    (motive_3 := fun _ _ _ => Nat) (motive_4 := fun _ n _ => 0 < n)
    (motive_5 := fun _ _ m _ => 0 < m) (motive_6 := fun _ _ _ k _ => 0 < k)
    1 (fun _ _ n _ => n + 1) (fun _ _ => 1) (fun _ _ _ _ => 1)
    Nat.zero_lt_one (fun _ _ _ _ _ _ => Nat.succ_pos _)
    (fun _ _ _ _ => Nat.zero_lt_one) (fun _ _ _ _ _ _ => Nat.zero_lt_one)

-- two levels down in one step: through the `Wf` a good term's type carries and
-- the `Ok` a well-formed type's context carries
theorem Good.ok : ∀ {Γ : Ctx} {A : Ty Γ} {t : Tm Γ A}, Good Γ A t → Ok Γ :=
  Good.rec (motive_1 := fun _ => Unit) (motive_2 := fun _ _ => Unit)
    (motive_3 := fun _ _ _ => Unit) (motive_4 := fun Γ _ _ => Ok Γ)
    (motive_5 := fun Γ _ _ _ => Ok Γ) (motive_6 := fun Γ _ _ _ _ => Ok Γ)
    () (fun _ _ _ _ => ()) (fun _ _ => ()) (fun _ _ _ _ => ())
    Ok.nil (fun Γ A _ _ _ h => Ok.snoc Γ A h)
    (fun _ _ _ h => h) (fun _ _ _ _ _ h => h)

end DataOnDataStack

/-! ### A proposition naming another, under a parameter

The same shape a universe up and under a type parameter.  A parameter is in the
pre-world and the real one alike, so the reading that carries a proposition
about a deleted index is indifferent to it, and the recursion is the one two
sections up with an `α` threaded through.
-/

namespace DataOnDataPropOnPropUniv

universe u

mutual
inductive Ctx (α : Type u) : Type u where
  | nil  : Ctx α
  | snoc : (Γ : Ctx α) → α → Ty α Γ → Ctx α
inductive Ty (α : Type u) : Ctx α → Type u where
  | base : (Γ : Ctx α) → Ty α Γ
inductive Ok (α : Type u) : Ctx α → Prop where
  | nil  : Ok α Ctx.nil
  | snoc : (Γ : Ctx α) → (a : α) → (A : Ty α Γ) → Ok α Γ → Ok α (Ctx.snoc Γ a A)
inductive Wf (α : Type u) : (Γ : Ctx α) → Ty α Γ → Prop where
  | base : (Γ : Ctx α) → Ok α Γ → Wf α Γ (Ty.base Γ)
end

/--
info: @Wf.rec : ∀ {α : Type u_2} {motive_1 : Ctx α → Sort u_1} {motive_2 : (a : Ctx α) → Ty α a → Sort u_1}
  {motive_3 : (a : Ctx α) → motive_1 a → Ok α a → Prop}
  {motive_4 : (Γ : Ctx α) → (a : Ty α Γ) → motive_2 Γ a → Wf α Γ a → Prop} (nil : motive_1 Ctx.nil)
  (snoc : (Γ : Ctx α) → (a : α) → (a_1 : Ty α Γ) → motive_1 Γ → motive_2 Γ a_1 → motive_1 (Γ.snoc a a_1))
  (base : (Γ : Ctx α) → motive_1 Γ → motive_2 Γ (Ty.base Γ)) (nil_1 : motive_3 Ctx.nil nil ⋯)
  (snoc_1 :
    ∀ (Γ : Ctx α) (a : α) (A : Ty α Γ) (a_1 : Ok α Γ) (Γ_ih : motive_1 Γ) (A_ih : motive_2 Γ A),
      motive_3 Γ Γ_ih a_1 → motive_3 (Γ.snoc a A) (snoc Γ a A Γ_ih A_ih) ⋯)
  (base_1 : ∀ (Γ : Ctx α) (a : Ok α Γ) (Γ_ih : motive_1 Γ), motive_3 Γ Γ_ih a → motive_4 Γ (Ty.base Γ) (base Γ Γ_ih) ⋯)
  {Γ : Ctx α} {a : Ty α Γ} (h : Wf α Γ a), motive_4 Γ a (Ty.rec nil snoc base nil_1 snoc_1 base_1 a) h
-/
#guard_msgs in
#check @Wf.rec

end DataOnDataPropOnPropUniv

/-! ### A proposition naming itself at a sibling's term

`Wf.unit : (Γ : Ctx) → Wf Γ (Ty.base Γ) → Wf Γ (Ty.unit Γ)` is where the grand
recursion stops, and the reason is what it recurses on.  A proposition's half of
a bundle is proved while recursing at the *data* term its index names, so the
hypothesis for a field is whatever the recursion has at that field's index --
and `Ty.base Γ` is no part of `Ty.unit Γ`.  There is no call at it, and nowhere
one could come from: a proposition that steps sideways across a data member's
constructors is not following that member's recursion at all.

So the block takes the split recursors.  `Wf.rec` recurses on the proof instead
and is a perfectly good induction principle -- it is only the joint recursion,
the one that would let a `Ty` function be declared with `Wf`'s motive on it,
that is not available.  The data recursors are untouched.
-/

namespace DataOnDataPropSibling

mutual
inductive Ctx : Type where
  | nil  : Ctx
  | snoc : (Γ : Ctx) → Ty Γ → Ctx
inductive Ty : Ctx → Type where
  | base : (Γ : Ctx) → Ty Γ
  | unit : (Γ : Ctx) → Ty Γ
inductive Wf : (Γ : Ctx) → Ty Γ → Prop where
  | base : (Γ : Ctx) → Wf Γ (Ty.base Γ)
  | unit : (Γ : Ctx) → Wf Γ (Ty.base Γ) → Wf Γ (Ty.unit Γ)
end

/--
info: @Ty.rec : {motive_1 : Ctx → Sort u_1} →
  {motive_2 : (a : Ctx) → Ty a → Sort u_1} →
    motive_1 Ctx.nil →
      ((Γ : Ctx) → (a : Ty Γ) → motive_1 Γ → motive_2 Γ a → motive_1 (Γ.snoc a)) →
        ((Γ : Ctx) → motive_1 Γ → motive_2 Γ (Ty.base Γ)) →
          ((Γ : Ctx) → motive_1 Γ → motive_2 Γ (Ty.unit Γ)) → {a : Ctx} → (t : Ty a) → motive_2 a t
-/
#guard_msgs in
#check @Ty.rec

/--
info: @Wf.rec : ∀ {motive : (Γ : Ctx) → (a : Ty Γ) → Wf Γ a → Prop},
  (∀ (Γ : Ctx), motive Γ (Ty.base Γ) ⋯) →
    (∀ (Γ : Ctx) (a : Wf Γ (Ty.base Γ)), motive Γ (Ty.base Γ) a → motive Γ (Ty.unit Γ) ⋯) →
      ∀ {Γ : Ctx} {a : Ty Γ} (h : Wf Γ a), motive Γ a h
-/
#guard_msgs in
#check @Wf.rec

end DataOnDataPropSibling

/-! ### A proposition over a longer chain

Members of one block need not have deleted the same number of indices, and one
grand recursion has to serve all of them at once.  `Tm` here deleted both of
its indices and so is recursed over under two hypotheses it was handed rather
than found; `Ty` deleted one; `Ok` deleted none and is where the propositional
half lives.  The three meet in the same recursor, and the only sign of it in
the visible declaration is which minors are short of an induction hypothesis.
-/

namespace DataOnDataPropTm

mutual
inductive Ctx : Type where
  | nil  : Ctx
  | snoc : (Γ : Ctx) → Ty Γ → Ctx
inductive Ty : Ctx → Type where
  | base : (Γ : Ctx) → Ty Γ
inductive Tm : (Γ : Ctx) → Ty Γ → Type where
  | var : (Γ : Ctx) → (A : Ty Γ) → Tm Γ A
inductive Ok : Ctx → Prop where
  | nil  : Ok Ctx.nil
  | snoc : (Γ : Ctx) → (A : Ty Γ) → Ok Γ → Ok (Ctx.snoc Γ A)
end

/--
info: @Tm.rec : {motive_1 : Ctx → Sort u_1} →
  {motive_2 : (a : Ctx) → Ty a → Sort u_1} →
    {motive_3 : (Γ : Ctx) → (a : Ty Γ) → Tm Γ a → Sort u_1} →
      {motive_4 : (a : Ctx) → motive_1 a → Ok a → Prop} →
        (nil : motive_1 Ctx.nil) →
          (snoc : (Γ : Ctx) → (a : Ty Γ) → motive_1 Γ → motive_2 Γ a → motive_1 (Γ.snoc a)) →
            ((Γ : Ctx) → motive_1 Γ → motive_2 Γ (Ty.base Γ)) →
              ((Γ : Ctx) → (A : Ty Γ) → motive_1 Γ → motive_2 Γ A → motive_3 Γ A (Tm.var Γ A)) →
                motive_4 Ctx.nil nil Ok.nil →
                  (∀ (Γ : Ctx) (A : Ty Γ) (a : Ok Γ) (Γ_ih : motive_1 Γ) (A_ih : motive_2 Γ A),
                      motive_4 Γ Γ_ih a → motive_4 (Γ.snoc A) (snoc Γ A Γ_ih A_ih) ⋯) →
                    {Γ : Ctx} → {a : Ty Γ} → (t : Tm Γ a) → motive_3 Γ a t
-/
#guard_msgs in
#check @Tm.rec

/--
info: @Ok.rec : ∀ {motive_1 : Ctx → Sort u_1} {motive_2 : (a : Ctx) → Ty a → Sort u_1}
  {motive_3 : (Γ : Ctx) → (a : Ty Γ) → Tm Γ a → Sort u_1} {motive_4 : (a : Ctx) → motive_1 a → Ok a → Prop}
  (nil : motive_1 Ctx.nil) (snoc : (Γ : Ctx) → (a : Ty Γ) → motive_1 Γ → motive_2 Γ a → motive_1 (Γ.snoc a))
  (base : (Γ : Ctx) → motive_1 Γ → motive_2 Γ (Ty.base Γ))
  (var : (Γ : Ctx) → (A : Ty Γ) → motive_1 Γ → motive_2 Γ A → motive_3 Γ A (Tm.var Γ A))
  (nil_1 : motive_4 Ctx.nil nil Ok.nil)
  (snoc_1 :
    ∀ (Γ : Ctx) (A : Ty Γ) (a : Ok Γ) (Γ_ih : motive_1 Γ) (A_ih : motive_2 Γ A),
      motive_4 Γ Γ_ih a → motive_4 (Γ.snoc A) (snoc Γ A Γ_ih A_ih) ⋯)
  {a : Ctx} (h : Ok a), motive_4 a (Ctx.rec nil snoc base var nil_1 snoc_1 a) h
-/
#guard_msgs in
#check @Ok.rec

def Ctx.len : Ctx → Nat :=
  Ctx.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    (motive_3 := fun _ _ _ => Nat) (motive_4 := fun _ _ _ => True)
    0 (fun _ _ n _ => n + 1) (fun _ _ => 0) (fun _ _ _ _ => 0)
    trivial (fun _ _ _ _ _ _ => trivial)

/-- info: 2 -/
#guard_msgs in
#eval Ctx.len (.snoc (.snoc .nil (.base .nil)) (.base (.snoc .nil (.base .nil))))

theorem ok_all : ∀ Γ : Ctx, Ok Γ :=
  Ctx.rec (motive_1 := fun Γ => Ok Γ) (motive_2 := fun _ _ => PUnit)
    (motive_3 := fun _ _ _ => PUnit) (motive_4 := fun _ _ _ => True)
    Ok.nil (fun Γ A h _ => Ok.snoc Γ A h) (fun _ _ => ⟨⟩) (fun _ _ _ _ => ⟨⟩)
    trivial (fun _ _ _ _ _ _ => trivial)

end DataOnDataPropTm

/-! ### A proposition beside a parameter

The pre-world and the real world are told apart by which arguments a member's
head is applied to, and a parameter is in both of them, unchanged.  So the same
recursion runs a universe up and under a type parameter with nothing new to
say, and the proposition still reads the value the data half produced.
-/

namespace DataOnDataPropUniv

universe u

mutual
inductive Ctx (α : Type u) : Type u where
  | nil  : Ctx α
  | snoc : (Γ : Ctx α) → α → Ty α Γ → Ctx α
inductive Ty (α : Type u) : Ctx α → Type u where
  | base : (Γ : Ctx α) → Ty α Γ
inductive Ok (α : Type u) : Ctx α → Prop where
  | nil  : Ok α Ctx.nil
  | snoc : (Γ : Ctx α) → (a : α) → (A : Ty α Γ) → Ok α Γ → Ok α (Ctx.snoc Γ a A)
end

/--
info: @Ok.rec : ∀ {α : Type u_2} {motive_1 : Ctx α → Sort u_1} {motive_2 : (a : Ctx α) → Ty α a → Sort u_1}
  {motive_3 : (a : Ctx α) → motive_1 a → Ok α a → Prop} (nil : motive_1 Ctx.nil)
  (snoc : (Γ : Ctx α) → (a : α) → (a_1 : Ty α Γ) → motive_1 Γ → motive_2 Γ a_1 → motive_1 (Γ.snoc a a_1))
  (base : (Γ : Ctx α) → motive_1 Γ → motive_2 Γ (Ty.base Γ)) (nil_1 : motive_3 Ctx.nil nil ⋯)
  (snoc_1 :
    ∀ (Γ : Ctx α) (a : α) (A : Ty α Γ) (a_1 : Ok α Γ) (Γ_ih : motive_1 Γ) (A_ih : motive_2 Γ A),
      motive_3 Γ Γ_ih a_1 → motive_3 (Γ.snoc a A) (snoc Γ a A Γ_ih A_ih) ⋯)
  {a : Ctx α} (h : Ok α a), motive_3 a (Ctx.rec nil snoc base nil_1 snoc_1 a) h
-/
#guard_msgs in
#check @Ok.rec

def Ctx.len {α : Type u} : Ctx α → Nat :=
  Ctx.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    (motive_3 := fun _ _ _ => True)
    0 (fun _ _ _ n _ => n + 1) (fun _ _ => 0)
    trivial (fun _ _ _ _ _ _ _ => trivial)

/-- info: 1 -/
#guard_msgs in
#eval Ctx.len (α := Nat) (.snoc .nil 3 (.base .nil))

end DataOnDataPropUniv

/-! ### Members that shadow globals

Lean reads every arity before any member is in scope, so a member whose name is
also a global's is read as the global in the arities and as the member in the
constructors.  Such a block fails at its constructors rather than at its
headers, and it is the headers failing that says a block is an
induction-induction, so nothing routes it to erasure.  It arrives as a *retry*
instead, once Lean has turned it down and some arity is seen to name a sibling.

Every block in the section above came that way, since `Ctx`, `Ty`, `Tm` and `Ok`
are all globals of this file already.
-/

namespace Shadowed

mutual
inductive Ctx : Type where
  | nil  : Ctx
  | snoc : (Γ : Ctx) → Ty Γ → Ctx
inductive Ty : Ctx → Type where
  | base : (Γ : Ctx) → Ty Γ
end

set_option pp.fullNames true in
/-- info: Shadowed.Ty : Shadowed.Ctx → Type -/
#guard_msgs in
#check @Ty

end Shadowed

/-! ### Naming the global on purpose

`_root_` is how Lean itself is told which one was meant, and it goes on meaning
that here: the arity below does not name a sibling, so the retry is never
offered the block and Lean's own elaborator keeps it.
-/

namespace Rooted

mutual
inductive Ctx : Type where
  | nil : Ctx
inductive Ty : _root_.Ctx → Type where
  | base : (Γ : _root_.Ctx) → Ty Γ
end

set_option pp.fullNames true in
/-- info: Rooted.Ty : _root_.Ctx → Type -/
#guard_msgs in
#check @Ty

-- and it is an ordinary inductive, with no pre-type standing behind it
/-- error: Unknown constant `Rooted.Ty._pre` -/
#guard_msgs in
#check Rooted.Ty._pre

end Rooted

/-! ### An index the constructor builds

The block every account of induction-induction opens with.  `Tm.lam` ends in
`Tm Γ (Ty.pi Γ A B)`, and that index is a term the constructor *builds* out of
its fields rather than one of the fields standing on its own.  That is the whole
point of the shape -- a well-typed term carries its type, and the type of a
lambda is made out of the pieces the lambda was made out of.

Nothing names `Tm`, so it leaves the block and the built index is a kernel index
like any other: what the erasure would have had to do with it is the subject of
`DataOnDataBuiltKept` just below, where a partner holds `Tm` in.  What is worth
checking here is that leaving costs the block nothing.  `Ctx.rec` and `Tm.rec`
are both the recursion over all three members, the minor premise for `lam` is
the one a well-typed-syntax development would write by hand, and the iota rules
hold with the indices left free -- which is the case a closed-term test would
miss.
-/

namespace DataOnDataBuilt

mutual
inductive Ctx : Type where
  | nil  : Ctx
  | snoc : (Γ : Ctx) → Ty Γ → Ctx
inductive Ty : Ctx → Type where
  | base : (Γ : Ctx) → Ty Γ
  | pi   : (Γ : Ctx) → (A : Ty Γ) → Ty (Ctx.snoc Γ A) → Ty Γ
inductive Tm : (Γ : Ctx) → Ty Γ → Type where
  | var : (Γ : Ctx) → (A : Ty Γ) → Tm Γ A
  | lam : (Γ : Ctx) → (A : Ty Γ) → (B : Ty (Ctx.snoc Γ A)) →
      Tm (Ctx.snoc Γ A) B → Tm Γ (Ty.pi Γ A B)
end

/--
info: def DataOnDataBuilt.Tm : (Γ : Ctx) → Ty Γ → Type :=
Tm._ind
-/
#guard_msgs in
#print Tm

-- nothing was erased, so there is no pre-type to ask about
/-- error: Unknown constant `DataOnDataBuilt.Tm._pre` -/
#guard_msgs in
#check DataOnDataBuilt.Tm._pre

-- `Tm.lam` is a constructor of `Tm._ind` and the kernel will not let a
-- definition stand in for an inductive's own occurrences in its constructors,
-- so this one place prints the name the type moved to.  Everywhere else -- the
-- recursors, the eliminators, the goals `induction` leaves -- reads `Tm`
/--
info: Tm.lam : (Γ : Ctx) → (A : Ty Γ) → (B : Ty (Γ.snoc A)) → Tm._ind (Γ.snoc A) B → Tm._ind Γ (Ty.pi Γ A B)
-/
#guard_msgs in
#check @Tm.lam

-- one recursion over the three members, and the `lam` minor premise is the one
-- a well-typed-syntax development would write by hand
/--
info: @Ctx.rec : {motive_1 : Ctx → Sort u_1} →
  {motive_2 : (a : Ctx) → Ty a → Sort u_1} →
    {motive_3 : (Γ : Ctx) → (a : Ty Γ) → Tm Γ a → Sort u_1} →
      motive_1 Ctx.nil →
        ((Γ : Ctx) → (a : Ty Γ) → motive_1 Γ → motive_2 Γ a → motive_1 (Γ.snoc a)) →
          ((Γ : Ctx) → motive_1 Γ → motive_2 Γ (Ty.base Γ)) →
            ((Γ : Ctx) →
                (A : Ty Γ) →
                  (a : Ty (Γ.snoc A)) → motive_1 Γ → motive_2 Γ A → motive_2 (Γ.snoc A) a → motive_2 Γ (Ty.pi Γ A a)) →
              ((Γ : Ctx) → (A : Ty Γ) → motive_1 Γ → motive_2 Γ A → motive_3 Γ A (Tm.var Γ A)) →
                ((Γ : Ctx) →
                    (A : Ty Γ) →
                      (B : Ty (Γ.snoc A)) →
                        (a : Tm (Γ.snoc A) B) →
                          motive_1 Γ →
                            motive_2 Γ A →
                              motive_2 (Γ.snoc A) B →
                                motive_3 (Γ.snoc A) B a → motive_3 Γ (Ty.pi Γ A B) (Tm.lam Γ A B a)) →
                  (t : Ctx) → motive_1 t
-/
#guard_msgs in
#check @Ctx.rec

-- `Tm.rec` is the same recursion, ending at the third motive instead of the
-- first, so the minor premises are shared
/--
info: @Tm.rec : {motive_1 : Ctx → Sort u_1} →
  {motive_2 : (a : Ctx) → Ty a → Sort u_1} →
    {motive_3 : (Γ : Ctx) → (a : Ty Γ) → Tm Γ a → Sort u_1} →
      motive_1 Ctx.nil →
        ((Γ : Ctx) → (a : Ty Γ) → motive_1 Γ → motive_2 Γ a → motive_1 (Γ.snoc a)) →
          ((Γ : Ctx) → motive_1 Γ → motive_2 Γ (Ty.base Γ)) →
            ((Γ : Ctx) →
                (A : Ty Γ) →
                  (a : Ty (Γ.snoc A)) → motive_1 Γ → motive_2 Γ A → motive_2 (Γ.snoc A) a → motive_2 Γ (Ty.pi Γ A a)) →
              ((Γ : Ctx) → (A : Ty Γ) → motive_1 Γ → motive_2 Γ A → motive_3 Γ A (Tm.var Γ A)) →
                ((Γ : Ctx) →
                    (A : Ty Γ) →
                      (B : Ty (Γ.snoc A)) →
                        (a : Tm (Γ.snoc A) B) →
                          motive_1 Γ →
                            motive_2 Γ A →
                              motive_2 (Γ.snoc A) B →
                                motive_3 (Γ.snoc A) B a → motive_3 Γ (Ty.pi Γ A B) (Tm.lam Γ A B a)) →
                  {Γ : Ctx} → {a : Ty Γ} → (t : Tm Γ a) → motive_3 Γ a t
-/
#guard_msgs in
#check @Tm.rec

-- one set of six alternatives, read off at each of the three members in turn
def csize : Ctx → Nat :=
  Ctx.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    (motive_3 := fun _ _ _ => Nat)
    0 (fun _ _ n m => n + m + 1)
    (fun _ _ => 1) (fun _ _ _ _ n m => n + m + 1)
    (fun _ _ _ _ => 1) (fun _ _ _ _ _ _ _ k => k + 1)

def tsize : {Γ : Ctx} → Ty Γ → Nat := fun {_} A =>
  Ty.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    (motive_3 := fun _ _ _ => Nat)
    0 (fun _ _ n m => n + m + 1)
    (fun _ _ => 1) (fun _ _ _ _ n m => n + m + 1)
    (fun _ _ _ _ => 1) (fun _ _ _ _ _ _ _ k => k + 1) A

def size : {Γ : Ctx} → {A : Ty Γ} → Tm Γ A → Nat := fun {_} {_} t =>
  Tm.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    (motive_3 := fun _ _ _ => Nat)
    0 (fun _ _ n m => n + m + 1)
    (fun _ _ => 1) (fun _ _ _ _ n m => n + m + 1)
    (fun _ _ _ _ => 1) (fun _ _ _ _ _ _ _ k => k + 1) t

example : csize Ctx.nil = 0 := rfl
example (Γ : Ctx) (A : Ty Γ) : csize (Ctx.snoc Γ A) = csize Γ + tsize A + 1 := rfl
example (Γ : Ctx) : tsize (Ty.base Γ) = 1 := rfl
example (Γ : Ctx) (A : Ty Γ) : size (Tm.var Γ A) = 1 := rfl

-- the two that matter, both with the indices free, so nothing here is
-- closed-term evaluation getting lucky.  `Ty` stayed in the block and is
-- erased, so its alternative is handed an index of its own and transports along
-- the equation the well-formedness carries; `Tm` left, so its `lam` is a
-- constructor with a built index and the kernel's own iota rule applies
example (Γ : Ctx) (A : Ty Γ) (B : Ty (Ctx.snoc Γ A)) :
    tsize (Ty.pi Γ A B) = tsize A + tsize B + 1 := rfl

example (Γ : Ctx) (A : Ty Γ) (B : Ty (Ctx.snoc Γ A)) (t : Tm (Ctx.snoc Γ A) B) :
    size (Tm.lam Γ A B t) = size t + 1 := rfl

-- and a `match` over a constructor whose index is built, which is the case the
-- pattern elaborator would refuse against an erased member
def lams : {Γ : Ctx} → {A : Ty Γ} → Tm Γ A → Nat
  | _, _, .var _ _     => 0
  | _, _, .lam _ _ _ t => lams t + 1

example (Γ : Ctx) (A : Ty Γ) (B : Ty (Ctx.snoc Γ A)) (t : Tm (Ctx.snoc Γ A) B) :
    lams (Tm.lam Γ A B t) = lams t + 1 := rfl

-- and a closed term reduces all the way, in the kernel and in the compiler
def idTm : Tm Ctx.nil (Ty.pi Ctx.nil (Ty.base Ctx.nil) (Ty.base _)) :=
  Tm.lam Ctx.nil (Ty.base Ctx.nil) (Ty.base _)
    (Tm.var (Ctx.snoc Ctx.nil (Ty.base Ctx.nil)) (Ty.base _))

example : size idTm = 2 := rfl
/-- info: 2 -/
#guard_msgs in
#eval size idTm

end DataOnDataBuilt

/-! ### The same block, with the built index held in

`DataOnDataBuilt` lifts `Tm` out because nothing names it.  Give it a partner
that does -- a `Sp` of spines, which `Tm.ofSp` reads and which reads a `Tm` back
-- and `Tm` is genuinely mutual with something, so it stays, and the erasure has
to deal with the built index after all.  This is the section that documents how.

The erasure deletes the index, and `Tm._pre.lam` has nothing left to say it
with, so the well-formedness carries an equation instead: the pre-world's
reading of what the constructor built, against the index the proposition was
stated at.  The constructor proves it by `rfl`, since at a real term the two are
the same term.  An alternative of the recursion is handed an index of its own --
there being no field for it to be -- and transports along that equation to reach
the constructor's reading.  The transport costs nothing: where the equation is
`x = x` the kernel replaces the proof by `Eq.refl` and reduces the transport
away before the alternative is ever applied.
-/

namespace DataOnDataBuiltKept

mutual
inductive Ctx : Type where
  | nil  : Ctx
  | snoc : (Γ : Ctx) → Ty Γ → Ctx
inductive Ty : Ctx → Type where
  | base : (Γ : Ctx) → Ty Γ
  | pi   : (Γ : Ctx) → (A : Ty Γ) → Ty (Ctx.snoc Γ A) → Ty Γ
inductive Tm : (Γ : Ctx) → Ty Γ → Type where
  | var  : (Γ : Ctx) → (A : Ty Γ) → Tm Γ A
  | lam  : (Γ : Ctx) → (A : Ty Γ) → (B : Ty (Ctx.snoc Γ A)) →
      Tm (Ctx.snoc Γ A) B → Tm Γ (Ty.pi Γ A B)
  | ofSp : (Γ : Ctx) → (A : Ty Γ) → Sp Γ A → Tm Γ A
inductive Sp : (Γ : Ctx) → Ty Γ → Type where
  | mk : (Γ : Ctx) → (A : Ty Γ) → Tm Γ A → Sp Γ A
end

-- `Tm` stayed, so it is the subtype the erasure builds rather than a definition
-- unfolding to an inductive of its own
/--
info: def DataOnDataBuiltKept.Tm : (Γ : Ctx) → Ty Γ → Type :=
fun Γ a => Subtype (Tm._wf Γ.val a.val)
-/
#guard_msgs in
#print Tm

-- the index is gone from the pre-constructor, and so is the context: what is
-- left of `lam` is the two types and the body
/-- info: DataOnDataBuiltKept.Tm._pre.lam (A B : Ty._pre) : Tm._pre → Tm._pre -/
#guard_msgs in
#check Tm._pre.lam

-- `Tm._pre` deleted both of its indices, so `Tm._wf` takes both back, and the
-- `lam` clause ends in the equation that stands in for the deleted index:
-- `A.pi B = d`, the built type against the one the proposition was stated at
/--
info: def DataOnDataBuiltKept.Tm._wf : Ctx._pre → Ty._pre → Tm._pre → Prop :=
fun Γ a t =>
  Tm._pre.rec True (fun Γ a ih ih_1 => ih ∧ ih_1 Γ) (fun Γ => True) (fun A a ih ih_1 Γ => ih Γ ∧ ih_1 (Γ.snoc A))
    (fun Γ A => True) (fun A B a ih ih_1 ih_2 Γ d => ih Γ ∧ ih_1 (Γ.snoc A) ∧ ih_2 (Γ.snoc A) B ∧ A.pi B = d)
    (fun a ih Γ A => ih Γ A) (fun a ih Γ A => ih Γ A) t Γ a
-/
#guard_msgs in
#print Tm._wf

-- four members, four motives, and the `lam` minor premise still ends at the
-- type the constructor built
/--
info: @Tm.rec : {motive_1 : Ctx → Sort u_1} →
  {motive_2 : (a : Ctx) → Ty a → Sort u_1} →
    {motive_3 : (Γ : Ctx) → (a : Ty Γ) → Tm Γ a → Sort u_1} →
      {motive_4 : (Γ : Ctx) → (a : Ty Γ) → Sp Γ a → Sort u_1} →
        motive_1 Ctx.nil →
          ((Γ : Ctx) → (a : Ty Γ) → motive_1 Γ → motive_2 Γ a → motive_1 (Γ.snoc a)) →
            ((Γ : Ctx) → motive_1 Γ → motive_2 Γ (Ty.base Γ)) →
              ((Γ : Ctx) →
                  (A : Ty Γ) →
                    (a : Ty (Γ.snoc A)) →
                      motive_1 Γ → motive_2 Γ A → motive_2 (Γ.snoc A) a → motive_2 Γ (Ty.pi Γ A a)) →
                ((Γ : Ctx) → (A : Ty Γ) → motive_1 Γ → motive_2 Γ A → motive_3 Γ A (Tm.var Γ A)) →
                  ((Γ : Ctx) →
                      (A : Ty Γ) →
                        (B : Ty (Γ.snoc A)) →
                          (a : Tm (Γ.snoc A) B) →
                            motive_1 Γ →
                              motive_2 Γ A →
                                motive_2 (Γ.snoc A) B →
                                  motive_3 (Γ.snoc A) B a → motive_3 Γ (Ty.pi Γ A B) (Tm.lam Γ A B a)) →
                    ((Γ : Ctx) →
                        (A : Ty Γ) →
                          (a : Sp Γ A) → motive_1 Γ → motive_2 Γ A → motive_4 Γ A a → motive_3 Γ A (Tm.ofSp Γ A a)) →
                      ((Γ : Ctx) →
                          (A : Ty Γ) →
                            (a : Tm Γ A) → motive_1 Γ → motive_2 Γ A → motive_3 Γ A a → motive_4 Γ A (Sp.mk Γ A a)) →
                        {Γ : Ctx} → {a : Ty Γ} → (t : Tm Γ a) → motive_3 Γ a t
-/
#guard_msgs in
#check @Tm.rec

-- one set of eight alternatives, read off at each of the four members in turn
def tsize : {Γ : Ctx} → Ty Γ → Nat := fun {_} A =>
  Ty.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    (motive_3 := fun _ _ _ => Nat) (motive_4 := fun _ _ _ => Nat)
    0 (fun _ _ n m => n + m + 1)
    (fun _ _ => 1) (fun _ _ _ _ n m => n + m + 1)
    (fun _ _ _ _ => 1) (fun _ _ _ _ _ _ _ k => k + 1)
    (fun _ _ _ _ _ k => k) (fun _ _ _ _ _ k => k + 1) A

def size : {Γ : Ctx} → {A : Ty Γ} → Tm Γ A → Nat := fun {_} {_} t =>
  Tm.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    (motive_3 := fun _ _ _ => Nat) (motive_4 := fun _ _ _ => Nat)
    0 (fun _ _ n m => n + m + 1)
    (fun _ _ => 1) (fun _ _ _ _ n m => n + m + 1)
    (fun _ _ _ _ => 1) (fun _ _ _ _ _ _ _ k => k + 1)
    (fun _ _ _ _ _ k => k) (fun _ _ _ _ _ k => k + 1) t

-- the transport reduces away with the indices left free, which is the point
example (Γ : Ctx) (A : Ty Γ) (B : Ty (Ctx.snoc Γ A)) :
    tsize (Ty.pi Γ A B) = tsize A + tsize B + 1 := rfl

example (Γ : Ctx) (A : Ty Γ) (B : Ty (Ctx.snoc Γ A)) (t : Tm (Ctx.snoc Γ A) B) :
    size (Tm.lam Γ A B t) = size t + 1 := rfl

-- and the iota rules across the mutual pair, in both directions: the same eight
-- alternatives read off at `Sp` give a recursion that agrees with the one read
-- off at `Tm` wherever the two constructors hand over to each other
def spSize : {Γ : Ctx} → {A : Ty Γ} → Sp Γ A → Nat := fun {_} {_} s =>
  Sp.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    (motive_3 := fun _ _ _ => Nat) (motive_4 := fun _ _ _ => Nat)
    0 (fun _ _ n m => n + m + 1)
    (fun _ _ => 1) (fun _ _ _ _ n m => n + m + 1)
    (fun _ _ _ _ => 1) (fun _ _ _ _ _ _ _ k => k + 1)
    (fun _ _ _ _ _ k => k) (fun _ _ _ _ _ k => k + 1) s

example (Γ : Ctx) (A : Ty Γ) (s : Sp Γ A) : size (Tm.ofSp Γ A s) = spSize s := rfl
example (Γ : Ctx) (A : Ty Γ) (t : Tm Γ A) : spSize (Sp.mk Γ A t) = size t + 1 := rfl

/-- info: 'DataOnDataBuiltKept.size' does not depend on any axioms -/
#guard_msgs in
#print axioms size

end DataOnDataBuiltKept

/-! ### The smallest blocks that build one

`Len.nil : Len .nil` builds its only index out of a constructor with no fields
at all, and `Tm7.mk` builds one out of a constructor applied to a field it does
have.  Neither needs a context or a type to show the shape, and both were hard
rejections until the well-formedness learned to carry an equation.
-/

namespace BuiltSmall

mutual
inductive Vec4 : Type where
  | nil : Vec4
  | cons : (v : Vec4) → (n : Len v) → Vec4
inductive Len : Vec4 → Type where
  | nil : Len .nil
end

/--
info: @Len.rec : {motive_1 : Vec4 → Sort u_1} →
  {motive_2 : (a : Vec4) → Len a → Sort u_1} →
    motive_1 Vec4.nil →
      ((v : Vec4) → (n : Len v) → motive_1 v → motive_2 v n → motive_1 (v.cons n)) →
        motive_2 Vec4.nil Len.nil → {a : Vec4} → (t : Len a) → motive_2 a t
-/
#guard_msgs in
#check @Len.rec

def Vec4.len : Vec4 → Nat :=
  Vec4.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Unit)
    0 (fun _ _ n _ => n + 1) ()

example : Vec4.len Vec4.nil = 0 := rfl
example (v : Vec4) (n : Len v) : Vec4.len (Vec4.cons v n) = Vec4.len v + 1 := rfl

mutual
inductive Ctx7 : Type where
  | nil  : Ctx7
  | snoc : (Γ : Ctx7) → Ty7 Γ → Ctx7
inductive Ty7 : Ctx7 → Type where
  | base : (Γ : Ctx7) → Ty7 Γ
inductive Tm7 : (Γ : Ctx7) → Ty7 Γ → Type where
  | mk : (Γ : Ctx7) → Tm7 Γ (Ty7.base Γ)
end

/--
info: @Tm7.rec : {motive_1 : Ctx7 → Sort u_1} →
  {motive_2 : (a : Ctx7) → Ty7 a → Sort u_1} →
    {motive_3 : (Γ : Ctx7) → (a : Ty7 Γ) → Tm7 Γ a → Sort u_1} →
      motive_1 Ctx7.nil →
        ((Γ : Ctx7) → (a : Ty7 Γ) → motive_1 Γ → motive_2 Γ a → motive_1 (Γ.snoc a)) →
          ((Γ : Ctx7) → motive_1 Γ → motive_2 Γ (Ty7.base Γ)) →
            ((Γ : Ctx7) → motive_1 Γ → motive_3 Γ (Ty7.base Γ) (Tm7.mk Γ)) →
              {Γ : Ctx7} → {a : Ty7 Γ} → (t : Tm7 Γ a) → motive_3 Γ a t
-/
#guard_msgs in
#check @Tm7.rec

end BuiltSmall

/-! ### A constructor that builds two of them

Nothing says a constructor builds only one of the indices the erasure deletes.
`Pair.mk` builds both of its types out of the context it was handed, `Sub.ext`
builds both of its contexts out of fields it does have -- the shape a
substitution between two contexts takes in every written-down type theory -- and
`P.mk` does it in a block a proposition is part of, so the readings it moves
between are readings of a bundle the well-formedness sits inside.

The well-formedness always had one equation per built index; what it took to use
them was carrying more than one.  The alternative is handed a binder for each
built index and transports across the equations one after another, each one
stated at the readings its predecessors already moved to, which is why the goal
is abstracted over every built value at once rather than each transport being
closed off on its own.
-/

namespace BuiltTwo

mutual
inductive Ctx : Type where
  | nil  : Ctx
  | snoc : (Γ : Ctx) → Ty Γ → Ctx
inductive Ty : Ctx → Type where
  | base : (Γ : Ctx) → Ty Γ
inductive Pair : (Γ : Ctx) → Ty Γ → Ty Γ → Type where
  | mk : (Γ : Ctx) → Pair Γ (Ty.base Γ) (Ty.base Γ)
end

/--
info: @Pair.rec : {motive_1 : Ctx → Sort u_1} →
  {motive_2 : (a : Ctx) → Ty a → Sort u_1} →
    {motive_3 : (Γ : Ctx) → (a a_1 : Ty Γ) → Pair Γ a a_1 → Sort u_1} →
      motive_1 Ctx.nil →
        ((Γ : Ctx) → (a : Ty Γ) → motive_1 Γ → motive_2 Γ a → motive_1 (Γ.snoc a)) →
          ((Γ : Ctx) → motive_1 Γ → motive_2 Γ (Ty.base Γ)) →
            ((Γ : Ctx) → motive_1 Γ → motive_3 Γ (Ty.base Γ) (Ty.base Γ) (Pair.mk Γ)) →
              {Γ : Ctx} → {a a_1 : Ty Γ} → (t : Pair Γ a a_1) → motive_3 Γ a a_1 t
-/
#guard_msgs in
#check @Pair.rec

def psize : {Γ : Ctx} → {A B : Ty Γ} → Pair Γ A B → Nat := fun p =>
  Pair.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    (motive_3 := fun _ _ _ _ => Nat)
    0 (fun _ _ n m => n + m + 1) (fun _ _ => 1) (fun _ _ => 7) p

example (Γ : Ctx) : psize (Pair.mk Γ) = 7 := rfl

-- both built out of fields rather than out of the one index that was kept, and
-- both at the same member, so the two transports are along equations about the
-- same pre-type
mutual
inductive Cx : Type where
  | nil  : Cx
  | snoc : (Γ : Cx) → Tp Γ → Cx
inductive Tp : Cx → Type where
  | base : (Γ : Cx) → Tp Γ
inductive Sub : Cx → Cx → Type where
  | ext : (Γ Δ : Cx) → (A : Tp Γ) → (B : Tp Δ) → Sub Γ Δ → Sub (Cx.snoc Γ A) (Cx.snoc Δ B)
end

/--
info: @Sub.rec : {motive_1 : Cx → Sort u_1} →
  {motive_2 : (a : Cx) → Tp a → Sort u_1} →
    {motive_3 : (a a_1 : Cx) → Sub a a_1 → Sort u_1} →
      motive_1 Cx.nil →
        ((Γ : Cx) → (a : Tp Γ) → motive_1 Γ → motive_2 Γ a → motive_1 (Γ.snoc a)) →
          ((Γ : Cx) → motive_1 Γ → motive_2 Γ (Tp.base Γ)) →
            ((Γ Δ : Cx) →
                (A : Tp Γ) →
                  (B : Tp Δ) →
                    (a : Sub Γ Δ) →
                      motive_1 Γ →
                        motive_1 Δ →
                          motive_2 Γ A →
                            motive_2 Δ B → motive_3 Γ Δ a → motive_3 (Γ.snoc A) (Δ.snoc B) (Sub.ext Γ Δ A B a)) →
              {a a_1 : Cx} → (t : Sub a a_1) → motive_3 a a_1 t
-/
#guard_msgs in
#check @Sub.rec

def depth : {Γ Δ : Cx} → Sub Γ Δ → Nat := fun s =>
  Sub.rec (motive_1 := fun _ => Unit) (motive_2 := fun _ _ => Unit)
    (motive_3 := fun _ _ _ => Nat)
    () (fun _ _ _ _ => ()) (fun _ _ => ())
    (fun _ _ _ _ _ _ _ _ _ n => n + 1) s

example (Γ Δ : Cx) (A : Tp Γ) (B : Tp Δ) (s : Sub Γ Δ) :
    depth (Sub.ext Γ Δ A B s) = depth s + 1 := rfl

/-- info: 'BuiltTwo.depth' does not depend on any axioms -/
#guard_msgs in
#print axioms depth

-- and with a proposition in the block, so what the transports move is the
-- bundle of the data value with the proof, whose type names the well-formedness
mutual
inductive T where
  | tip
  | node (t : T) : T
inductive P : T → T → Type where
  | mk (a b : T) : P (T.node a) (T.node b)
inductive Ok : T → Prop where
  | tip : Ok .tip
  | node (t : T) : Ok t → Ok (.node t)
end

/--
info: @Ok.rec : ∀ {motive_1 : T → Sort u_1} {motive_2 : (a a_1 : T) → P a a_1 → Sort u_1}
  {motive_3 : (a : T) → motive_1 a → Ok a → Prop} (tip : motive_1 T.tip) (node : (t : T) → motive_1 t → motive_1 t.node)
  (mk : (a b : T) → motive_1 a → motive_1 b → motive_2 a.node b.node (P.mk a b)) (tip_1 : motive_3 T.tip tip Ok.tip)
  (node_1 : ∀ (t : T) (a : Ok t) (t_ih : motive_1 t), motive_3 t t_ih a → motive_3 t.node (node t t_ih) ⋯) {a : T}
  (h : Ok a), motive_3 a (T.rec tip node mk tip_1 node_1 a) h
-/
#guard_msgs in
#check @Ok.rec

def size : T → Nat :=
  T.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ _ => Nat)
    (motive_3 := fun _ n _ => 0 < n)
    1 (fun _ n => n + 1) (fun _ _ _ _ => 0)
    Nat.zero_lt_one (fun _ _ _ h => Nat.lt_of_lt_of_le h (Nat.le_succ _))

example (t : T) : size (T.node t) = size t + 1 := rfl

theorem Ok.size_pos : ∀ {t : T}, Ok t → 0 < size t :=
  Ok.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ _ => Nat)
    (motive_3 := fun _ n _ => 0 < n)
    1 (fun _ n => n + 1) (fun _ _ _ _ => 0)
    Nat.zero_lt_one (fun _ _ _ h => Nat.lt_of_lt_of_le h (Nat.le_succ _))

/--
info: 'BuiltTwo.Ok.size_pos' does not depend on any axioms
-/
#guard_msgs in
#print axioms Ok.size_pos

end BuiltTwo

/-! ### A field given as two of them

`Sub.id : (Γ : Ctx) → Sub Γ Γ` gives one field as both of the indices the
erasure deletes, and a field can stand for only one of them: the pre-world
constructor drops it once, and nothing in the erased world is left to say the
two readings agree.  Nothing, that is, except the equation the well-formedness
already carries for an index the constructor *built* -- so the second reading is
treated as one built out of the field, and the transport written for `Tm.lam`
does the rest.  With the last section that is the whole substitution calculus:
`Sub.id` repeats an index and `Sub.ext` builds two.

Which reading is the field is not a free choice.  `Q.mk : (Γ : Ctx) → (A : Ty Γ)
→ Q Γ Γ A` has a third index stated at its second, and its `A` is typed at the
first, so only the second reading can be the field -- an alternative has a bare
binder for whichever reading it is not, and `A` would be at a term it does not
have.  The reading another deleted index is stated at is therefore the one kept,
and the block is refused only when two of them are.
-/

namespace RepeatedIdx

mutual
inductive Ctx : Type where
  | nil  : Ctx
  | snoc : (Γ : Ctx) → Ty Γ → Ctx
inductive Ty : Ctx → Type where
  | base : (Γ : Ctx) → Ty Γ
inductive Sub : Ctx → Ctx → Type where
  | id  : (Γ : Ctx) → Sub Γ Γ
  | ext : (Γ Δ : Ctx) → (A : Ty Γ) → (B : Ty Δ) → Sub Γ Δ → Sub (Ctx.snoc Γ A) (Ctx.snoc Δ B)
end

/--
info: @Sub.rec : {motive_1 : Ctx → Sort u_1} →
  {motive_2 : (a : Ctx) → Ty a → Sort u_1} →
    {motive_3 : (a a_1 : Ctx) → Sub a a_1 → Sort u_1} →
      motive_1 Ctx.nil →
        ((Γ : Ctx) → (a : Ty Γ) → motive_1 Γ → motive_2 Γ a → motive_1 (Γ.snoc a)) →
          ((Γ : Ctx) → motive_1 Γ → motive_2 Γ (Ty.base Γ)) →
            ((Γ : Ctx) → motive_1 Γ → motive_3 Γ Γ (Sub.id Γ)) →
              ((Γ Δ : Ctx) →
                  (A : Ty Γ) →
                    (B : Ty Δ) →
                      (a : Sub Γ Δ) →
                        motive_1 Γ →
                          motive_1 Δ →
                            motive_2 Γ A →
                              motive_2 Δ B → motive_3 Γ Δ a → motive_3 (Γ.snoc A) (Δ.snoc B) (Sub.ext Γ Δ A B a)) →
                {a a_1 : Ctx} → (t : Sub a a_1) → motive_3 a a_1 t
-/
#guard_msgs in
#check @Sub.rec

def depth : {Γ Δ : Ctx} → Sub Γ Δ → Nat := fun s =>
  Sub.rec (motive_1 := fun _ => Unit) (motive_2 := fun _ _ => Unit)
    (motive_3 := fun _ _ _ => Nat)
    () (fun _ _ _ _ => ()) (fun _ _ => ())
    (fun _ _ => 0) (fun _ _ _ _ _ _ _ _ _ n => n + 1) s

example (Γ : Ctx) : depth (Sub.id Γ) = 0 := rfl
example (Γ Δ : Ctx) (A : Ty Γ) (B : Ty Δ) (s : Sub Γ Δ) :
    depth (Sub.ext Γ Δ A B s) = depth s + 1 := rfl

/-- info: 'RepeatedIdx.depth' does not depend on any axioms -/
#guard_msgs in
#print axioms depth

-- three readings of the one field, so two of them are carried
namespace Three
mutual
inductive Ctx : Type where
  | nil  : Ctx
  | snoc : (Γ : Ctx) → Ty Γ → Ctx
inductive Ty : Ctx → Type where
  | base : (Γ : Ctx) → Ty Γ
inductive Tri : Ctx → Ctx → Ctx → Type where
  | all : (Γ : Ctx) → Tri Γ Γ Γ
end

/--
info: @Tri.rec : {motive_1 : Ctx → Sort u_1} →
  {motive_2 : (a : Ctx) → Ty a → Sort u_1} →
    {motive_3 : (a a_1 a_2 : Ctx) → Tri a a_1 a_2 → Sort u_1} →
      motive_1 Ctx.nil →
        ((Γ : Ctx) → (a : Ty Γ) → motive_1 Γ → motive_2 Γ a → motive_1 (Γ.snoc a)) →
          ((Γ : Ctx) → motive_1 Γ → motive_2 Γ (Ty.base Γ)) →
            ((Γ : Ctx) → motive_1 Γ → motive_3 Γ Γ Γ (Tri.all Γ)) →
              {a a_1 a_2 : Ctx} → (t : Tri a a_1 a_2) → motive_3 a a_1 a_2 t
-/
#guard_msgs in
#check @Tri.rec

end Three

-- a repeat and a genuinely built index in the same constructor
namespace Mixed
mutual
inductive Ctx : Type where
  | nil  : Ctx
  | snoc : (Γ : Ctx) → Ty Γ → Ctx
inductive Ty : Ctx → Type where
  | base : (Γ : Ctx) → Ty Γ
inductive J : Ctx → Ctx → Ctx → Type where
  | mk : (Γ : Ctx) → (A : Ty Γ) → J Γ Γ (Ctx.snoc Γ A)
end

/--
info: @J.rec : {motive_1 : Ctx → Sort u_1} →
  {motive_2 : (a : Ctx) → Ty a → Sort u_1} →
    {motive_3 : (a a_1 a_2 : Ctx) → J a a_1 a_2 → Sort u_1} →
      motive_1 Ctx.nil →
        ((Γ : Ctx) → (a : Ty Γ) → motive_1 Γ → motive_2 Γ a → motive_1 (Γ.snoc a)) →
          ((Γ : Ctx) → motive_1 Γ → motive_2 Γ (Ty.base Γ)) →
            ((Γ : Ctx) → (A : Ty Γ) → motive_1 Γ → motive_2 Γ A → motive_3 Γ Γ (Γ.snoc A) (J.mk Γ A)) →
              {a a_1 a_2 : Ctx} → (t : J a a_1 a_2) → motive_3 a a_1 a_2 t
-/
#guard_msgs in
#check @J.rec

end Mixed

-- and the case where only the second reading can be the field
namespace Choice
mutual
inductive Ctx : Type where
  | nil  : Ctx
  | snoc : (Γ : Ctx) → Ty Γ → Ctx
inductive Ty : Ctx → Type where
  | base : (Γ : Ctx) → Ty Γ
inductive Q : (Γ Δ : Ctx) → Ty Δ → Type where
  | mk : (Γ : Ctx) → (A : Ty Γ) → Q Γ Γ A
end

/--
info: @Q.rec : {motive_1 : Ctx → Sort u_1} →
  {motive_2 : (a : Ctx) → Ty a → Sort u_1} →
    {motive_3 : (Γ Δ : Ctx) → (a : Ty Δ) → Q Γ Δ a → Sort u_1} →
      motive_1 Ctx.nil →
        ((Γ : Ctx) → (a : Ty Γ) → motive_1 Γ → motive_2 Γ a → motive_1 (Γ.snoc a)) →
          ((Γ : Ctx) → motive_1 Γ → motive_2 Γ (Ty.base Γ)) →
            ((Γ : Ctx) → (A : Ty Γ) → motive_1 Γ → motive_2 Γ A → motive_3 Γ Γ A (Q.mk Γ A)) →
              {Γ Δ : Ctx} → {a : Ty Δ} → (t : Q Γ Δ a) → motive_3 Γ Δ a t
-/
#guard_msgs in
#check @Q.rec

def qsize : {Γ Δ : Ctx} → {A : Ty Δ} → Q Γ Δ A → Nat := fun t =>
  Q.rec (motive_1 := fun _ => Unit) (motive_2 := fun _ _ => Unit)
    (motive_3 := fun _ _ _ _ => Nat) () (fun _ _ _ _ => ()) (fun _ _ => ()) (fun _ _ _ _ => 8) t

example (Γ : Ctx) (A : Ty Γ) : qsize (Q.mk Γ A) = 8 := rfl

end Choice

-- and one in a block a proposition is part of, where the transport moves the
-- bundle rather than the value
mutual
inductive T where
  | tip
  | node (t : T) : T
inductive P : T → T → Type where
  | dup (a : T) : P a a
inductive Ok : T → Prop where
  | tip : Ok .tip
  | node (t : T) : Ok t → Ok (.node t)
end

/--
info: @Ok.rec : ∀ {motive_1 : T → Sort u_1} {motive_2 : (a a_1 : T) → P a a_1 → Sort u_1}
  {motive_3 : (a : T) → motive_1 a → Ok a → Prop} (tip : motive_1 T.tip) (node : (t : T) → motive_1 t → motive_1 t.node)
  (dup : (a : T) → motive_1 a → motive_2 a a (P.dup a)) (tip_1 : motive_3 T.tip tip Ok.tip)
  (node_1 : ∀ (t : T) (a : Ok t) (t_ih : motive_1 t), motive_3 t t_ih a → motive_3 t.node (node t t_ih) ⋯) {a : T}
  (h : Ok a), motive_3 a (T.rec tip node dup tip_1 node_1 a) h
-/
#guard_msgs in
#check @Ok.rec

def size : T → Nat :=
  T.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ _ => Nat) (motive_3 := fun _ n _ => 0 < n)
    1 (fun _ n => n + 1) (fun _ _ => 0)
    Nat.zero_lt_one (fun _ _ _ h => Nat.lt_of_lt_of_le h (Nat.le_succ _))

example (t : T) : size (T.node t) = size t + 1 := rfl

theorem Ok.size_pos : ∀ {t : T}, Ok t → 0 < size t :=
  Ok.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ _ => Nat) (motive_3 := fun _ n _ => 0 < n)
    1 (fun _ n => n + 1) (fun _ _ => 0)
    Nat.zero_lt_one (fun _ _ _ h => Nat.lt_of_lt_of_le h (Nat.le_succ _))

/-- info: 'RepeatedIdx.Ok.size_pos' does not depend on any axioms -/
#guard_msgs in
#print axioms Ok.size_pos

end RepeatedIdx

/-! ### The tower

`Ctx`, then `Ty` over a context, then `Tm` over a context and a type in it, is
the shape every dependent type theory is written in, and `Tm.var` is the reason
it took this long.  It ends in `Tm (Γ.snoc A) (Ty.base (Γ.snoc A))`: both indices
are built, and the second is built *out of* the first, so the two transports are
not independent.  The one for the type has to read the context at whatever the
transport before it moved it to, not at the `Γ.snoc A` the constructor wrote,
because by then the alternative is holding a binder there.  Their pre-types name
no index at all -- the erasure would have refused the block otherwise -- so it is
only the well-formedness and the subtype element that have to follow along.

With this the whole tower comes out with the alternative the block was written
with, and terms compute.
-/

namespace Tower

mutual
inductive Ctx : Type where
  | nil  : Ctx
  | snoc : (Γ : Ctx) → Ty Γ → Ctx
inductive Ty : Ctx → Type where
  | base : (Γ : Ctx) → Ty Γ
  | pi   : (Γ : Ctx) → (A : Ty Γ) → Ty (Ctx.snoc Γ A) → Ty Γ
inductive Tm : (Γ : Ctx) → Ty Γ → Type where
  | var : (Γ : Ctx) → (A : Ty Γ) → Tm (Ctx.snoc Γ A) (Ty.base (Ctx.snoc Γ A))
  | lam : (Γ : Ctx) → (A : Ty Γ) → (B : Ty (Ctx.snoc Γ A)) →
      Tm (Ctx.snoc Γ A) B → Tm Γ (Ty.pi Γ A B)
  | app : (Γ : Ctx) → (A : Ty Γ) → (B : Ty (Ctx.snoc Γ A)) →
      Tm Γ (Ty.pi Γ A B) → Tm Γ A → Tm Γ (Ty.base Γ)
end

/--
info: @Tm.rec : {motive_1 : Ctx → Sort u_1} →
  {motive_2 : (a : Ctx) → Ty a → Sort u_1} →
    {motive_3 : (Γ : Ctx) → (a : Ty Γ) → Tm Γ a → Sort u_1} →
      motive_1 Ctx.nil →
        ((Γ : Ctx) → (a : Ty Γ) → motive_1 Γ → motive_2 Γ a → motive_1 (Γ.snoc a)) →
          ((Γ : Ctx) → motive_1 Γ → motive_2 Γ (Ty.base Γ)) →
            ((Γ : Ctx) →
                (A : Ty Γ) →
                  (a : Ty (Γ.snoc A)) → motive_1 Γ → motive_2 Γ A → motive_2 (Γ.snoc A) a → motive_2 Γ (Ty.pi Γ A a)) →
              ((Γ : Ctx) →
                  (A : Ty Γ) → motive_1 Γ → motive_2 Γ A → motive_3 (Γ.snoc A) (Ty.base (Γ.snoc A)) (Tm.var Γ A)) →
                ((Γ : Ctx) →
                    (A : Ty Γ) →
                      (B : Ty (Γ.snoc A)) →
                        (a : Tm (Γ.snoc A) B) →
                          motive_1 Γ →
                            motive_2 Γ A →
                              motive_2 (Γ.snoc A) B →
                                motive_3 (Γ.snoc A) B a → motive_3 Γ (Ty.pi Γ A B) (Tm.lam Γ A B a)) →
                  ((Γ : Ctx) →
                      (A : Ty Γ) →
                        (B : Ty (Γ.snoc A)) →
                          (a : Tm Γ (Ty.pi Γ A B)) →
                            (a_1 : Tm Γ A) →
                              motive_1 Γ →
                                motive_2 Γ A →
                                  motive_2 (Γ.snoc A) B →
                                    motive_3 Γ (Ty.pi Γ A B) a →
                                      motive_3 Γ A a_1 → motive_3 Γ (Ty.base Γ) (Tm.app Γ A B a a_1)) →
                    {Γ : Ctx} → {a : Ty Γ} → (t : Tm Γ a) → motive_3 Γ a t
-/
#guard_msgs in
#check @Tm.rec

def tmSize : {Γ : Ctx} → {A : Ty Γ} → Tm Γ A → Nat := fun t =>
  Tm.rec (motive_1 := fun _ => Unit) (motive_2 := fun _ _ => Unit)
    (motive_3 := fun _ _ _ => Nat)
    () (fun _ _ _ _ => ()) (fun _ _ => ()) (fun _ _ _ _ _ _ => ())
    (fun _ _ _ _ => 1)
    (fun _ _ _ _ _ _ _ n => n + 1)
    (fun _ _ _ _ _ _ _ _ m n => m + n) t

example (Γ : Ctx) (A : Ty Γ) : tmSize (Tm.var Γ A) = 1 := rfl
example (Γ : Ctx) (A : Ty Γ) (B : Ty (Ctx.snoc Γ A)) (t : Tm (Ctx.snoc Γ A) B) :
    tmSize (Tm.lam Γ A B t) = tmSize t + 1 := rfl
example (Γ : Ctx) (A : Ty Γ) (B : Ty (Ctx.snoc Γ A))
    (f : Tm Γ (Ty.pi Γ A B)) (a : Tm Γ A) :
    tmSize (Tm.app Γ A B f a) = tmSize f + tmSize a := rfl

/-- info: 'Tower.tmSize' does not depend on any axioms -/
#guard_msgs in
#print axioms tmSize

-- two built indices reading a third, rather than one reading one
namespace Chain
mutual
inductive Ctx : Type where
  | nil  : Ctx
  | snoc : (Γ : Ctx) → Ty Γ → Ctx
inductive Ty : Ctx → Type where
  | base : (Γ : Ctx) → Ty Γ
inductive Three : (Γ : Ctx) → Ty Γ → Ty Γ → Type where
  | mk : (Γ : Ctx) → (A : Ty Γ) →
      Three (Ctx.snoc Γ A) (Ty.base (Ctx.snoc Γ A)) (Ty.base (Ctx.snoc Γ A))
end

/--
info: @Three.rec : {motive_1 : Ctx → Sort u_1} →
  {motive_2 : (a : Ctx) → Ty a → Sort u_1} →
    {motive_3 : (Γ : Ctx) → (a a_1 : Ty Γ) → Three Γ a a_1 → Sort u_1} →
      motive_1 Ctx.nil →
        ((Γ : Ctx) → (a : Ty Γ) → motive_1 Γ → motive_2 Γ a → motive_1 (Γ.snoc a)) →
          ((Γ : Ctx) → motive_1 Γ → motive_2 Γ (Ty.base Γ)) →
            ((Γ : Ctx) →
                (A : Ty Γ) →
                  motive_1 Γ →
                    motive_2 Γ A → motive_3 (Γ.snoc A) (Ty.base (Γ.snoc A)) (Ty.base (Γ.snoc A)) (Three.mk Γ A)) →
              {Γ : Ctx} → {a a_1 : Ty Γ} → (t : Three Γ a a_1) → motive_3 Γ a a_1 t
-/
#guard_msgs in
#check @Three.rec
end Chain

-- the context the type is read in is itself two extensions deep, so what the
-- transport substitutes is a term the earlier transport built and not a binder
-- the constructor was handed
namespace FromField
mutual
inductive Ctx : Type where
  | nil  : Ctx
  | snoc : (Γ : Ctx) → Ty Γ → Ctx
inductive Ty : Ctx → Type where
  | base : (Γ : Ctx) → Ty Γ
inductive Tm : (Γ : Ctx) → Ty Γ → Type where
  | mk : (Γ : Ctx) → (A : Ty Γ) → (B : Ty (Ctx.snoc Γ A)) →
      Tm (Ctx.snoc (Ctx.snoc Γ A) B) (Ty.base (Ctx.snoc (Ctx.snoc Γ A) B))
end

/--
info: @Tm.rec : {motive_1 : Ctx → Sort u_1} →
  {motive_2 : (a : Ctx) → Ty a → Sort u_1} →
    {motive_3 : (Γ : Ctx) → (a : Ty Γ) → Tm Γ a → Sort u_1} →
      motive_1 Ctx.nil →
        ((Γ : Ctx) → (a : Ty Γ) → motive_1 Γ → motive_2 Γ a → motive_1 (Γ.snoc a)) →
          ((Γ : Ctx) → motive_1 Γ → motive_2 Γ (Ty.base Γ)) →
            ((Γ : Ctx) →
                (A : Ty Γ) →
                  (B : Ty (Γ.snoc A)) →
                    motive_1 Γ →
                      motive_2 Γ A →
                        motive_2 (Γ.snoc A) B →
                          motive_3 ((Γ.snoc A).snoc B) (Ty.base ((Γ.snoc A).snoc B)) (Tm.mk Γ A B)) →
              {Γ : Ctx} → {a : Ty Γ} → (t : Tm Γ a) → motive_3 Γ a t
-/
#guard_msgs in
#check @Tm.rec
end FromField

-- and with a proposition in the block, so the transports carry the bundle the
-- joint recursion runs on rather than a bare value
namespace WithProp
mutual
inductive Ctx : Type where
  | nil  : Ctx
  | snoc : (Γ : Ctx) → Ty Γ → Ctx
inductive Ty : Ctx → Type where
  | base : (Γ : Ctx) → Ty Γ
inductive Tm : (Γ : Ctx) → Ty Γ → Type where
  | var : (Γ : Ctx) → (A : Ty Γ) → Tm (Ctx.snoc Γ A) (Ty.base (Ctx.snoc Γ A))
inductive Ok : Ctx → Prop where
  | nil : Ok Ctx.nil
  | snoc : (Γ : Ctx) → (A : Ty Γ) → Ok Γ → Ok (Ctx.snoc Γ A)
end

/--
info: @Ok.rec : ∀ {motive_1 : Ctx → Sort u_1} {motive_2 : (a : Ctx) → Ty a → Sort u_1}
  {motive_3 : (Γ : Ctx) → (a : Ty Γ) → Tm Γ a → Sort u_1} {motive_4 : (a : Ctx) → motive_1 a → Ok a → Prop}
  (nil : motive_1 Ctx.nil) (snoc : (Γ : Ctx) → (a : Ty Γ) → motive_1 Γ → motive_2 Γ a → motive_1 (Γ.snoc a))
  (base : (Γ : Ctx) → motive_1 Γ → motive_2 Γ (Ty.base Γ))
  (var : (Γ : Ctx) → (A : Ty Γ) → motive_1 Γ → motive_2 Γ A → motive_3 (Γ.snoc A) (Ty.base (Γ.snoc A)) (Tm.var Γ A))
  (nil_1 : motive_4 Ctx.nil nil Ok.nil)
  (snoc_1 :
    ∀ (Γ : Ctx) (A : Ty Γ) (a : Ok Γ) (Γ_ih : motive_1 Γ) (A_ih : motive_2 Γ A),
      motive_4 Γ Γ_ih a → motive_4 (Γ.snoc A) (snoc Γ A Γ_ih A_ih) ⋯)
  {a : Ctx} (h : Ok a), motive_4 a (Ctx.rec nil snoc base var nil_1 snoc_1 a) h
-/
#guard_msgs in
#check @Ok.rec

def csize : Ctx → Nat :=
  Ctx.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Unit)
    (motive_3 := fun _ _ _ => Unit) (motive_4 := fun _ n _ => 0 < n)
    1 (fun _ _ n _ => n + 1) (fun _ _ => ()) (fun _ _ _ _ => ())
    Nat.zero_lt_one (fun _ _ _ _ _ h => Nat.lt_of_lt_of_le h (Nat.le_succ _))

example (Γ : Ctx) (A : Ty Γ) : csize (Ctx.snoc Γ A) = csize Γ + 1 := rfl

theorem Ok.size_pos : ∀ {Γ : Ctx}, Ok Γ → 0 < csize Γ :=
  Ok.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Unit)
    (motive_3 := fun _ _ _ => Unit) (motive_4 := fun _ n _ => 0 < n)
    1 (fun _ _ n _ => n + 1) (fun _ _ => ()) (fun _ _ _ _ => ())
    Nat.zero_lt_one (fun _ _ _ _ _ h => Nat.lt_of_lt_of_le h (Nat.le_succ _))

/-- info: 'Tower.WithProp.Ok.size_pos' does not depend on any axioms -/
#guard_msgs in
#print axioms Ok.size_pos
end WithProp

end Tower

/-! ### A field at an index the constructor built

`Tm.mk : (Γ : Ctx) → (B : Ty Γ) → (A : Ty (Γ.snoc B)) → Tm (Γ.snoc B) A` is the
shape of any rule that extends the context and then names something in the
extension.  Its context is built and its type is a field, and the field's own
type reads the context the constructor built -- so a field deleted along with
the index would have been left at a term the alternative only has a binder for.

A field in that position stops being deleted and goes back to being a field the
constructor keeps, with the index *built out of it*; the equation the
well-formedness carries for a built index is then what says the two agree, and
the transports move them together.  Which is the same move that let a field
stand at two indices, and it costs nothing that was not already there.  The
alternative comes out binding the field where the constructor wrote it, and with
an induction hypothesis for it -- `motive_2 (Γ.snoc B) A` -- that the deleted
reading never gave.

Since a binder in an arity can only name the ones before it, one pass in arity
order settles every promotion this sets off, and nothing in this family is
turned away any more.
-/

namespace Promoted

namespace AtBuilt
mutual
inductive Ctx : Type where
  | nil  : Ctx
  | snoc : (Γ : Ctx) → Ty Γ → Ctx
inductive Ty : Ctx → Type where
  | base : (Γ : Ctx) → Ty Γ
inductive Tm : (Γ : Ctx) → Ty Γ → Type where
  | mk : (Γ : Ctx) → (B : Ty Γ) → (A : Ty (Ctx.snoc Γ B)) → Tm (Ctx.snoc Γ B) A
end

/--
info: @Tm.rec : {motive_1 : Ctx → Sort u_1} →
  {motive_2 : (a : Ctx) → Ty a → Sort u_1} →
    {motive_3 : (Γ : Ctx) → (a : Ty Γ) → Tm Γ a → Sort u_1} →
      motive_1 Ctx.nil →
        ((Γ : Ctx) → (a : Ty Γ) → motive_1 Γ → motive_2 Γ a → motive_1 (Γ.snoc a)) →
          ((Γ : Ctx) → motive_1 Γ → motive_2 Γ (Ty.base Γ)) →
            ((Γ : Ctx) →
                (B : Ty Γ) →
                  (A : Ty (Γ.snoc B)) →
                    motive_1 Γ → motive_2 Γ B → motive_2 (Γ.snoc B) A → motive_3 (Γ.snoc B) A (Tm.mk Γ B A)) →
              {Γ : Ctx} → {a : Ty Γ} → (t : Tm Γ a) → motive_3 Γ a t
-/
#guard_msgs in
#check @Tm.rec

def tsize : {Γ : Ctx} → {A : Ty Γ} → Tm Γ A → Nat := fun t =>
  Tm.rec (motive_1 := fun _ => Unit) (motive_2 := fun _ _ => Unit)
    (motive_3 := fun _ _ _ => Nat)
    () (fun _ _ _ _ => ()) (fun _ _ => ())
    (fun _ _ _ _ _ _ => 1) t

example (Γ : Ctx) (B : Ty Γ) (A : Ty (Ctx.snoc Γ B)) : tsize (Tm.mk Γ B A) = 1 := rfl

/-- info: 'Promoted.AtBuilt.tsize' does not depend on any axioms -/
#guard_msgs in
#print axioms tsize
end AtBuilt

-- a field given as two indices, with a type at each of them.  Whichever reading
-- stays the field, the other's type is promoted rather than stranded
namespace BothRead
mutual
inductive Ctx : Type where
  | nil  : Ctx
  | snoc : (Γ : Ctx) → Ty Γ → Ctx
inductive Ty : Ctx → Type where
  | base : (Γ : Ctx) → Ty Γ
inductive R : (Γ Δ : Ctx) → Ty Γ → Ty Δ → Type where
  | mk : (Γ : Ctx) → (A B : Ty Γ) → R Γ Γ A B
end

/--
info: @R.rec : {motive_1 : Ctx → Sort u_1} →
  {motive_2 : (a : Ctx) → Ty a → Sort u_1} →
    {motive_3 : (Γ Δ : Ctx) → (a : Ty Γ) → (a_1 : Ty Δ) → R Γ Δ a a_1 → Sort u_1} →
      motive_1 Ctx.nil →
        ((Γ : Ctx) → (a : Ty Γ) → motive_1 Γ → motive_2 Γ a → motive_1 (Γ.snoc a)) →
          ((Γ : Ctx) → motive_1 Γ → motive_2 Γ (Ty.base Γ)) →
            ((Γ : Ctx) → (A B : Ty Γ) → motive_1 Γ → motive_2 Γ A → motive_2 Γ B → motive_3 Γ Γ A B (R.mk Γ A B)) →
              {Γ Δ : Ctx} → {a : Ty Γ} → {a_1 : Ty Δ} → (t : R Γ Δ a a_1) → motive_3 Γ Δ a a_1 t
-/
#guard_msgs in
#check @R.rec
end BothRead

-- two fields promoted at once, at a member with three indices
namespace Three
mutual
inductive Ctx : Type where
  | nil  : Ctx
  | snoc : (Γ : Ctx) → Ty Γ → Ctx
inductive Ty : Ctx → Type where
  | base : (Γ : Ctx) → Ty Γ
inductive Tm : (Γ : Ctx) → Ty Γ → Type where
  | lam : (Γ : Ctx) → (A : Ty Γ) → Tm Γ A
inductive Pf : (Γ : Ctx) → (A : Ty Γ) → Tm Γ A → Type where
  | mk : (Γ : Ctx) → (A : Ty Γ) → (B : Ty (Ctx.snoc Γ A)) →
      (t : Tm (Ctx.snoc Γ A) B) → Pf (Ctx.snoc Γ A) B t
end

/--
info: @Pf.rec : {motive_1 : Ctx → Sort u_1} →
  {motive_2 : (a : Ctx) → Ty a → Sort u_1} →
    {motive_3 : (Γ : Ctx) → (a : Ty Γ) → Tm Γ a → Sort u_1} →
      {motive_4 : (Γ : Ctx) → (A : Ty Γ) → (a : Tm Γ A) → Pf Γ A a → Sort u_1} →
        motive_1 Ctx.nil →
          ((Γ : Ctx) → (a : Ty Γ) → motive_1 Γ → motive_2 Γ a → motive_1 (Γ.snoc a)) →
            ((Γ : Ctx) → motive_1 Γ → motive_2 Γ (Ty.base Γ)) →
              ((Γ : Ctx) → (A : Ty Γ) → motive_1 Γ → motive_2 Γ A → motive_3 Γ A (Tm.lam Γ A)) →
                ((Γ : Ctx) →
                    (A : Ty Γ) →
                      (B : Ty (Γ.snoc A)) →
                        (t : Tm (Γ.snoc A) B) →
                          motive_1 Γ →
                            motive_2 Γ A →
                              motive_2 (Γ.snoc A) B →
                                motive_3 (Γ.snoc A) B t → motive_4 (Γ.snoc A) B t (Pf.mk Γ A B t)) →
                  {Γ : Ctx} → {A : Ty Γ} → {a : Tm Γ A} → (t : Pf Γ A a) → motive_4 Γ A a t
-/
#guard_msgs in
#check @Pf.rec
end Three

end Promoted

/-! ### A built index beside a proposition

`Ok : Ctx → Prop` next to the block above is the case where the two hard things
meet.  `Tm.lam` *builds* its second index out of its own fields rather than
taking it as one, so the alternative for it is handed a binder where the
constructor has a term; and the joint recursion has to state the proposition at
the value the data recursion returned, which is exactly the thing that reading
of the index decides.

Both readings are available, and the well-formedness says they agree, so what
the alternative produces at the constructor's reading is carried across that
equation to the binder's -- the whole of it, index and term and proof together,
since in the joint recursion the well-formedness sits inside the type of what
comes back.  That is what lets `Ok` join the recursion instead of being pushed
out of it: `motive_4` reads the `Nat` that `motive_1` computed.
-/

namespace BuiltBesideProp

mutual
inductive Ctx : Type where
  | nil  : Ctx
  | snoc : (Γ : Ctx) → Ty Γ → Ctx
inductive Ty : Ctx → Type where
  | base : (Γ : Ctx) → Ty Γ
  | pi   : (Γ : Ctx) → (A : Ty Γ) → Ty (Ctx.snoc Γ A) → Ty Γ
inductive Tm : (Γ : Ctx) → Ty Γ → Type where
  | var : (Γ : Ctx) → (A : Ty Γ) → Tm Γ A
  | lam : (Γ : Ctx) → (A : Ty Γ) → (B : Ty (Ctx.snoc Γ A)) →
      Tm (Ctx.snoc Γ A) B → Tm Γ (Ty.pi Γ A B)
inductive Ok : Ctx → Prop where
  | nil  : Ok Ctx.nil
  | snoc : (Γ : Ctx) → (A : Ty Γ) → Ok Γ → Ok (Ctx.snoc Γ A)
end

-- all four motives, and `motive_4` reads the value `motive_1` returned: the
-- proposition is being proved *about* the function, in the one recursion
/--
info: @Ok.rec : ∀ {motive_1 : Ctx → Sort u_1} {motive_2 : (a : Ctx) → Ty a → Sort u_1}
  {motive_3 : (Γ : Ctx) → (a : Ty Γ) → Tm Γ a → Sort u_1} {motive_4 : (a : Ctx) → motive_1 a → Ok a → Prop}
  (nil : motive_1 Ctx.nil) (snoc : (Γ : Ctx) → (a : Ty Γ) → motive_1 Γ → motive_2 Γ a → motive_1 (Γ.snoc a))
  (base : (Γ : Ctx) → motive_1 Γ → motive_2 Γ (Ty.base Γ))
  (pi :
    (Γ : Ctx) →
      (A : Ty Γ) → (a : Ty (Γ.snoc A)) → motive_1 Γ → motive_2 Γ A → motive_2 (Γ.snoc A) a → motive_2 Γ (Ty.pi Γ A a))
  (var : (Γ : Ctx) → (A : Ty Γ) → motive_1 Γ → motive_2 Γ A → motive_3 Γ A (Tm.var Γ A))
  (lam :
    (Γ : Ctx) →
      (A : Ty Γ) →
        (B : Ty (Γ.snoc A)) →
          (a : Tm (Γ.snoc A) B) →
            motive_1 Γ →
              motive_2 Γ A →
                motive_2 (Γ.snoc A) B → motive_3 (Γ.snoc A) B a → motive_3 Γ (Ty.pi Γ A B) (Tm.lam Γ A B a))
  (nil_1 : motive_4 Ctx.nil nil Ok.nil)
  (snoc_1 :
    ∀ (Γ : Ctx) (A : Ty Γ) (a : Ok Γ) (Γ_ih : motive_1 Γ) (A_ih : motive_2 Γ A),
      motive_4 Γ Γ_ih a → motive_4 (Γ.snoc A) (snoc Γ A Γ_ih A_ih) ⋯)
  {a : Ctx} (h : Ok a), motive_4 a (Ctx.rec nil snoc base pi var lam nil_1 snoc_1 a) h
-/
#guard_msgs in
#check @Ok.rec

-- the same eight alternatives seen from the data side, and `lam` still builds
-- its index: the constructor written is the constructor that came out
/--
info: @Tm.rec : {motive_1 : Ctx → Sort u_1} →
  {motive_2 : (a : Ctx) → Ty a → Sort u_1} →
    {motive_3 : (Γ : Ctx) → (a : Ty Γ) → Tm Γ a → Sort u_1} →
      {motive_4 : (a : Ctx) → motive_1 a → Ok a → Prop} →
        (nil : motive_1 Ctx.nil) →
          (snoc : (Γ : Ctx) → (a : Ty Γ) → motive_1 Γ → motive_2 Γ a → motive_1 (Γ.snoc a)) →
            ((Γ : Ctx) → motive_1 Γ → motive_2 Γ (Ty.base Γ)) →
              ((Γ : Ctx) →
                  (A : Ty Γ) →
                    (a : Ty (Γ.snoc A)) →
                      motive_1 Γ → motive_2 Γ A → motive_2 (Γ.snoc A) a → motive_2 Γ (Ty.pi Γ A a)) →
                ((Γ : Ctx) → (A : Ty Γ) → motive_1 Γ → motive_2 Γ A → motive_3 Γ A (Tm.var Γ A)) →
                  ((Γ : Ctx) →
                      (A : Ty Γ) →
                        (B : Ty (Γ.snoc A)) →
                          (a : Tm (Γ.snoc A) B) →
                            motive_1 Γ →
                              motive_2 Γ A →
                                motive_2 (Γ.snoc A) B →
                                  motive_3 (Γ.snoc A) B a → motive_3 Γ (Ty.pi Γ A B) (Tm.lam Γ A B a)) →
                    motive_4 Ctx.nil nil Ok.nil →
                      (∀ (Γ : Ctx) (A : Ty Γ) (a : Ok Γ) (Γ_ih : motive_1 Γ) (A_ih : motive_2 Γ A),
                          motive_4 Γ Γ_ih a → motive_4 (Γ.snoc A) (snoc Γ A Γ_ih A_ih) ⋯) →
                        {Γ : Ctx} → {a : Ty Γ} → (t : Tm Γ a) → motive_3 Γ a t
-/
#guard_msgs in
#check @Tm.rec

-- a context weighs one for itself plus its types, a `pi` one for itself plus
-- its two halves, and `lam` recurses through the term the builder built
def size : Ctx → Nat :=
  Ctx.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    (motive_3 := fun _ _ _ => Nat) (motive_4 := fun _ n _ => 0 < n)
    1 (fun _ _ n m => n + m) (fun _ _ => 1) (fun _ _ _ _ n m => n + m + 1)
    (fun _ _ _ _ => 1) (fun _ _ _ _ _ n m k => n + m + k + 1)
    Nat.zero_lt_one (fun _ _ _ _ _ h => Nat.lt_of_lt_of_le h (Nat.le_add_right _ _))

example : size Ctx.nil = 1 := rfl
example (Γ : Ctx) : size (Ctx.snoc Γ (Ty.base Γ)) = size Γ + 1 := rfl

-- the same eight alternatives again, read off at `Ok` instead of at `Ctx`; the
-- statement is about `size`, so this only typechecks because the major premise
-- of `Ok.rec` returns the motive at the very term `size` was defined as
theorem Ok.size_pos : ∀ {Γ : Ctx}, Ok Γ → 0 < size Γ :=
  Ok.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    (motive_3 := fun _ _ _ => Nat) (motive_4 := fun _ n _ => 0 < n)
    1 (fun _ _ n m => n + m) (fun _ _ => 1) (fun _ _ _ _ n m => n + m + 1)
    (fun _ _ _ _ => 1) (fun _ _ _ _ _ n m k => n + m + k + 1)
    Nat.zero_lt_one (fun _ _ _ _ _ h => Nat.lt_of_lt_of_le h (Nat.le_add_right _ _))

end BuiltBesideProp

/-! ### A built index at the proposition's own index

The section before builds an index of one member while the proposition is
indexed by another.  Here they are the same one: `U.mk` builds `T.node n t` out
of its own fields, and `Ok` is a proposition about `T`.  So the reading of the
index that the transport has to settle is the reading the proposition's motive
is stated at, and the two cannot be kept apart by looking at which member they
belong to.

`Ok` recurses here as well, which the section before could not: `Ok.node` holds
a proof about the field the index was built out of, and that proof arrives at
the recursion as an ordinary hypothesis.
-/

namespace BuiltAtThePropIndex

mutual
inductive T where
  | tip
  | node (n : Nat) (t : T) : T
inductive U : T → Type where
  | tip : U .tip
  | mk (n : Nat) (t : T) : U (.node n t)
inductive Ok : T → Prop where
  | tip : Ok .tip
  | node (n : Nat) (t : T) : Ok t → Ok (.node n t)
end

/-- info: U.mk : (n : Nat) → (t : T) → U (T.node n t) -/
#guard_msgs in
#check @U.mk

/--
info: @Ok.rec : ∀ {motive_1 : T → Sort u_1} {motive_2 : (a : T) → U a → Sort u_1}
  {motive_3 : (a : T) → motive_1 a → Ok a → Prop} (tip : motive_1 T.tip)
  (node : (n : Nat) → (t : T) → motive_1 t → motive_1 (T.node n t)) (tip_1 : motive_2 T.tip U.tip)
  (mk : (n : Nat) → (t : T) → motive_1 t → motive_2 (T.node n t) (U.mk n t)) (tip_2 : motive_3 T.tip tip Ok.tip)
  (node_1 :
    ∀ (n : Nat) (t : T) (a : Ok t) (t_ih : motive_1 t), motive_3 t t_ih a → motive_3 (T.node n t) (node n t t_ih) ⋯)
  {a : T} (h : Ok a), motive_3 a (T.rec tip node tip_1 mk tip_2 node_1 a) h
-/
#guard_msgs in
#check @Ok.rec

def size : T → Nat :=
  T.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    (motive_3 := fun _ n _ => 0 < n)
    1 (fun _ _ ih => ih + 1) 0 (fun _ _ ih => ih)
    Nat.zero_lt_one (fun _ _ _ _ h => Nat.lt_of_lt_of_le h (Nat.le_succ _))

example : size (T.node 1 (T.node 2 T.tip)) = 3 := rfl

-- the same six alternatives again, read off at `Ok` instead of at `T`
theorem Ok.size_pos : ∀ {t : T}, Ok t → 0 < size t :=
  Ok.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    (motive_3 := fun _ n _ => 0 < n)
    1 (fun _ _ ih => ih + 1) 0 (fun _ _ ih => ih)
    Nat.zero_lt_one (fun _ _ _ _ h => Nat.lt_of_lt_of_le h (Nat.le_succ _))

/-- info: 'BuiltAtThePropIndex.Ok.size_pos' does not depend on any axioms -/
#guard_msgs in
#print axioms Ok.size_pos

end BuiltAtThePropIndex

/-! ### A built index with an argument that is no field at all

Every built index so far has been a constructor at the fields around it.  This
one passes `true` as well, and a literal is not a field: the check that the
recursion can name a hypothesis at each argument of the index reads the fields
off the arguments, and there is no field to read off `true`.

There need not be one either.  The argument is at a position the erasure keeps,
so the recursion never has to descend into it, and the block goes through with
`Ty.pi` stated exactly as it was written.
-/

namespace BuiltWithALiteral

mutual
inductive Ctx : Nat → Type where
  | nil  : Ctx 0
  | snoc : (n : Nat) → (Γ : Ctx n) → (tag : Bool) → Ty n Γ → Ctx (n + 1)
inductive Ty : (n : Nat) → Ctx n → Type where
  | base : (n : Nat) → (Γ : Ctx n) → Ty n Γ
  | pi   : (n : Nat) → (Γ : Ctx n) → (A : Ty n Γ) → Ty (n + 1) (Ctx.snoc n Γ true A) → Ty n Γ
end

/--
info: Ty.pi : (n : Nat) → (Γ : Ctx n) → (A : Ty n Γ) → Ty (n + 1) (Ctx.snoc n Γ true A) → Ty n Γ
-/
#guard_msgs in
#check @Ty.pi

-- and the recursion over the whole block computes at it
def depth : {n : Nat} → {Γ : Ctx n} → Ty n Γ → Nat :=
  Ty.rec (motive_1 := fun _ _ => Nat) (motive_2 := fun _ _ _ => Nat)
    0 (fun _ _ _ _ ihΓ ihA => ihΓ + ihA) (fun _ _ _ => 0)
    (fun _ _ _ _ _ _ ihB => ihB + 1)

example : depth (.pi 0 .nil (.base 0 .nil) (.base 1 _)) = 1 := rfl

/-- info: 'BuiltWithALiteral.depth' does not depend on any axioms -/
#guard_msgs in
#print axioms depth

end BuiltWithALiteral

/-! ### A built index under denesting

All three at once: `U.mk` builds the index `T.node n v`, the field it builds it
out of sits at a denested copy of `List (Wrap T n)`, and `Ok` is a proposition
about the result.  Each of the three costs a transport, and they meet in the
same alternative.

The proposition's recursor is the one to look at.  A block with copies in it
gets its recursors twice -- once over the copies, and once restated over the
types the writer wrote -- and the restatement for a `Prop` member is built from
the recursion over the whole block, not from that member's split recursor.  That
is why `Ok.rec` below carries the data motives and reads `T.rec` in its
conclusion, rather than being the ordinary induction principle on the proof.
-/

namespace BuiltIndexUnderDenesting

inductive Wrap (α : Type) (n : Nat) where
  | mk (a : α) : Wrap α n

mutual
inductive T where
  | tip
  | node (n : Nat) (v : List (Wrap T n)) : T
inductive U : T → Type where
  | tip : U .tip
  | mk (n : Nat) (v : List (Wrap T n)) : U (.node n v)
inductive Ok : T → Prop where
  | tip : Ok .tip
  | node (n : Nat) (v : List (Wrap T n)) : 0 < n → Ok (.node n v)
end

/-- info: T.node : (n : Nat) → List (Wrap T n) → T -/
#guard_msgs in
#check @T.node

/-- info: U.mk : (n : Nat) → (v : List (Wrap T n)) → U (T.node n v) -/
#guard_msgs in
#check @U.mk

/-- info: Ok.node : ∀ (n : Nat) (v : List (Wrap T n)), 0 < n → Ok (T.node n v) -/
#guard_msgs in
#check @Ok.node

/--
info: @Ok.rec : ∀ {motive_1 : T → Sort u_1} {motive_2 : (a : T) → U a → Sort u_1}
  {motive_3 : (a : T) → motive_1 a → Ok a → Prop} {motive_4 : (n : Nat) → List (Wrap T n) → Sort u_1}
  {motive_5 : (n : Nat) → Wrap T n → Sort u_1} (tip : motive_1 T.tip)
  (node : (n : Nat) → (v : List (Wrap T n)) → motive_4 n v → motive_1 (T.node n v)) (tip_1 : motive_2 T.tip U.tip)
  (mk : (n : Nat) → (v : List (Wrap T n)) → motive_4 n v → motive_2 (T.node n v) (U.mk n v))
  (tip_2 : motive_3 T.tip tip Ok.tip)
  (node_1 :
    ∀ (n : Nat) (v : List (Wrap T n)) (a : 0 < n) (v_ih : motive_4 n v), motive_3 (T.node n v) (node n v v_ih) ⋯)
  (nil : (n : Nat) → motive_4 n [])
  (cons :
    (n : Nat) →
      (head : Wrap T n) → (tail : List (Wrap T n)) → motive_5 n head → motive_4 n tail → motive_4 n (head :: tail))
  (mk_1 : (n : Nat) → (a : T) → motive_1 a → motive_5 n (Wrap.mk a)) {a : T} (t : Ok a),
  motive_3 a (T.rec tip node tip_1 mk tip_2 node_1 nil cons mk_1 a) t
-/
#guard_msgs in
#check @Ok.rec

def size : T → Nat :=
  T.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    (motive_3 := fun _ m _ => 0 < m)
    (motive_4 := fun _ _ => Nat) (motive_5 := fun _ _ => Nat)
    1 (fun _ _ ih => ih + 1)
    0 (fun _ _ ih => ih)
    Nat.zero_lt_one (fun _ _ _ _ => Nat.succ_pos _)
    (fun _ => 0) (fun _ _ _ ih ihs => ih + ihs) (fun _ _ ih => ih)

example : size (T.node 3 [Wrap.mk T.tip]) = 2 := rfl

-- the same nine alternatives again, read off at `Ok` instead of at `T`
theorem Ok.size_pos : ∀ {t : T}, Ok t → 0 < size t :=
  Ok.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    (motive_3 := fun _ m _ => 0 < m)
    (motive_4 := fun _ _ => Nat) (motive_5 := fun _ _ => Nat)
    1 (fun _ _ ih => ih + 1)
    0 (fun _ _ ih => ih)
    Nat.zero_lt_one (fun _ _ _ _ => Nat.succ_pos _)
    (fun _ => 0) (fun _ _ _ ih ihs => ih + ihs) (fun _ _ ih => ih)

/-- info: 'BuiltIndexUnderDenesting.size' does not depend on any axioms -/
#guard_msgs in
#print axioms size

/-- info: 'BuiltIndexUnderDenesting.Ok.size_pos' does not depend on any axioms -/
#guard_msgs in
#print axioms Ok.size_pos

end BuiltIndexUnderDenesting

/-! ### A proposition that recurses in a context it built

`Wf.pi` is the well-formedness a type theory actually writes down: a `pi` is
well formed when its domain is and its codomain is *in the extended context*.
That second hypothesis is stated at `Γ.snoc A`, a context the constructor built
out of its own fields, and no proof about it was handed to the constructor.

It does not have to be.  What the erasure needs is that `Γ.snoc A` is a
well-formed pre-context, and `Ctx._wf` at a pre-constructor is by definition the
conjunction of the facts about that constructor's arguments -- here that `Γ` is
a well-formed context and `A` a well-formed type in it, both of which the
constructor is holding, since a real value is a pre-term paired with its own
proof.  So the fact is assembled rather than looked up.

The pay-off is the joint recursion: `size` is defined by recursion on `Ty` and
`Wf.size_pos` is proved by the same recursion, with the proposition's motive
reading the value the data motive computed.
-/

namespace PropInBuiltCtx

mutual
inductive Ctx : Type where
  | nil  : Ctx
  | snoc : (Γ : Ctx) → Ty Γ → Ctx
inductive Ty : Ctx → Type where
  | base : (Γ : Ctx) → Ty Γ
  | pi   : (Γ : Ctx) → (A : Ty Γ) → Ty (Ctx.snoc Γ A) → Ty Γ
inductive Wf : (Γ : Ctx) → Ty Γ → Prop where
  | base : (Γ : Ctx) → Wf Γ (Ty.base Γ)
  | pi   : (Γ : Ctx) → (A : Ty Γ) → (B : Ty (Ctx.snoc Γ A)) →
      Wf Γ A → Wf (Ctx.snoc Γ A) B → Wf Γ (Ty.pi Γ A B)
end

-- `motive_3` takes the value `motive_2` computed, which is what lets a
-- proposition say something about a function defined in the same recursion
/--
info: @Ty.rec : {motive_1 : Ctx → Sort u_1} →
  {motive_2 : (a : Ctx) → Ty a → Sort u_1} →
    {motive_3 : (Γ : Ctx) → (a : Ty Γ) → motive_2 Γ a → Wf Γ a → Prop} →
      motive_1 Ctx.nil →
        ((Γ : Ctx) → (a : Ty Γ) → motive_1 Γ → motive_2 Γ a → motive_1 (Γ.snoc a)) →
          (base : (Γ : Ctx) → motive_1 Γ → motive_2 Γ (Ty.base Γ)) →
            (pi :
                (Γ : Ctx) →
                  (A : Ty Γ) →
                    (a : Ty (Γ.snoc A)) →
                      motive_1 Γ → motive_2 Γ A → motive_2 (Γ.snoc A) a → motive_2 Γ (Ty.pi Γ A a)) →
              (∀ (Γ : Ctx) (Γ_ih : motive_1 Γ), motive_3 Γ (Ty.base Γ) (base Γ Γ_ih) ⋯) →
                (∀ (Γ : Ctx) (A : Ty Γ) (B : Ty (Γ.snoc A)) (a : Wf Γ A) (a_1 : Wf (Γ.snoc A) B) (Γ_ih : motive_1 Γ)
                    (A_ih : motive_2 Γ A) (B_ih : motive_2 (Γ.snoc A) B),
                    motive_3 Γ A A_ih a →
                      motive_3 (Γ.snoc A) B B_ih a_1 → motive_3 Γ (Ty.pi Γ A B) (pi Γ A B Γ_ih A_ih B_ih) ⋯) →
                  {a : Ctx} → (t : Ty a) → motive_2 a t
-/
#guard_msgs in
#check @Ty.rec

def size : {Γ : Ctx} → Ty Γ → Nat := fun {_} A =>
  Ty.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    (motive_3 := fun _ _ n _ => 0 < n)
    0 (fun _ _ n m => n + m + 1) (fun _ _ => 1) (fun _ _ _ _ n m => n + m + 1)
    (fun _ _ => Nat.zero_lt_one) (fun _ _ _ _ _ _ _ _ _ _ => Nat.succ_pos _) A

example (Γ : Ctx) : size (Ty.base Γ) = 1 := rfl
example (Γ : Ctx) (A : Ty Γ) (B : Ty (Ctx.snoc Γ A)) :
    size (Ty.pi Γ A B) = size A + size B + 1 := rfl

-- the same six alternatives again, read off at `Wf` instead of at `Ty`
theorem Wf.size_pos : ∀ {Γ : Ctx} {A : Ty Γ}, Wf Γ A → 0 < size A :=
  Wf.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    (motive_3 := fun _ _ n _ => 0 < n)
    0 (fun _ _ n m => n + m + 1) (fun _ _ => 1) (fun _ _ _ _ n m => n + m + 1)
    (fun _ _ => Nat.zero_lt_one) (fun _ _ _ _ _ _ _ _ _ _ => Nat.succ_pos _)

end PropInBuiltCtx

/-! ### Well-formed contexts and well-formed types

The pair the last section was half of.  `Ok` and `Wf` name each other -- a
context is well formed when the type it was extended by is, and a base type is
well formed when its context is -- so neither is an induction principle on its
own, and what the block owes is a *mutual* one over both.

That is what comes out: `Ok.rec` and `Wf.rec` share two motives and four minor
premises, which is exactly the induction a metatheory does over a derivation.
The data half keeps its own recursors, and the recursion over the whole block
is not available here -- it would have to recurse on a `Subtype`, which has no
`brecOn` -- so `Ok` and `Wf` come out as a recursion between themselves.
-/

namespace OkAndWf

mutual
inductive Ctx : Type where
  | nil  : Ctx
  | snoc : (Γ : Ctx) → Ty Γ → Ctx
inductive Ty : Ctx → Type where
  | base : (Γ : Ctx) → Ty Γ
  | pi   : (Γ : Ctx) → (A : Ty Γ) → Ty (Ctx.snoc Γ A) → Ty Γ
inductive Ok : Ctx → Prop where
  | nil  : Ok Ctx.nil
  | snoc : (Γ : Ctx) → (A : Ty Γ) → Ok Γ → Wf Γ A → Ok (Ctx.snoc Γ A)
inductive Wf : (Γ : Ctx) → Ty Γ → Prop where
  | base : (Γ : Ctx) → Ok Γ → Wf Γ (Ty.base Γ)
  | pi   : (Γ : Ctx) → (A : Ty Γ) → (B : Ty (Ctx.snoc Γ A)) →
      Wf Γ A → Wf (Ctx.snoc Γ A) B → Wf Γ (Ty.pi Γ A B)
end

/--
info: @Ok.rec : ∀ {motive_1 : (a : Ctx) → Ok a → Prop} {motive_2 : (Γ : Ctx) → (a : Ty Γ) → Wf Γ a → Prop},
  motive_1 Ctx.nil Ok.nil →
    (∀ (Γ : Ctx) (A : Ty Γ) (a : Ok Γ) (a_1 : Wf Γ A), motive_1 Γ a → motive_2 Γ A a_1 → motive_1 (Γ.snoc A) ⋯) →
      (∀ (Γ : Ctx) (a : Ok Γ), motive_1 Γ a → motive_2 Γ (Ty.base Γ) ⋯) →
        (∀ (Γ : Ctx) (A : Ty Γ) (B : Ty (Γ.snoc A)) (a : Wf Γ A) (a_1 : Wf (Γ.snoc A) B),
            motive_2 Γ A a → motive_2 (Γ.snoc A) B a_1 → motive_2 Γ (Ty.pi Γ A B) ⋯) →
          ∀ {a : Ctx} (h : Ok a), motive_1 a h
-/
#guard_msgs in
#check @Ok.rec

/--
info: @Wf.rec : ∀ {motive_1 : (a : Ctx) → Ok a → Prop} {motive_2 : (Γ : Ctx) → (a : Ty Γ) → Wf Γ a → Prop},
  motive_1 Ctx.nil Ok.nil →
    (∀ (Γ : Ctx) (A : Ty Γ) (a : Ok Γ) (a_1 : Wf Γ A), motive_1 Γ a → motive_2 Γ A a_1 → motive_1 (Γ.snoc A) ⋯) →
      (∀ (Γ : Ctx) (a : Ok Γ), motive_1 Γ a → motive_2 Γ (Ty.base Γ) ⋯) →
        (∀ (Γ : Ctx) (A : Ty Γ) (B : Ty (Γ.snoc A)) (a : Wf Γ A) (a_1 : Wf (Γ.snoc A) B),
            motive_2 Γ A a → motive_2 (Γ.snoc A) B a_1 → motive_2 Γ (Ty.pi Γ A B) ⋯) →
          ∀ {Γ : Ctx} {a : Ty Γ} (h : Wf Γ a), motive_2 Γ a h
-/
#guard_msgs in
#check @Wf.rec

/--
info: @Ty.rec : {motive_1 : Ctx → Sort u_1} →
  {motive_2 : (a : Ctx) → Ty a → Sort u_1} →
    motive_1 Ctx.nil →
      ((Γ : Ctx) → (a : Ty Γ) → motive_1 Γ → motive_2 Γ a → motive_1 (Γ.snoc a)) →
        ((Γ : Ctx) → motive_1 Γ → motive_2 Γ (Ty.base Γ)) →
          ((Γ : Ctx) →
              (A : Ty Γ) →
                (a : Ty (Γ.snoc A)) → motive_1 Γ → motive_2 Γ A → motive_2 (Γ.snoc A) a → motive_2 Γ (Ty.pi Γ A a)) →
            {a : Ctx} → (t : Ty a) → motive_2 a t
-/
#guard_msgs in
#check @Ty.rec

-- the data half is a recursion between `Ctx` and `Ty`, and it computes: `Ty.pi`
-- is the constructor that recurses in a context it built, so the equation at it
-- is the one that says the transport left nothing behind
def csize : Ctx → Nat :=
  Ctx.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    0 (fun _ _ n m => n + m + 1) (fun _ _ => 1) (fun _ _ _ _ n m => n + m + 1)

def tsize : {Γ : Ctx} → Ty Γ → Nat := fun {_} A =>
  Ty.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    0 (fun _ _ n m => n + m + 1) (fun _ _ => 1) (fun _ _ _ _ n m => n + m + 1) A

example (Γ : Ctx) : tsize (Ty.base Γ) = 1 := rfl
example (Γ : Ctx) (A : Ty Γ) (B : Ty (Ctx.snoc Γ A)) :
    tsize (Ty.pi Γ A B) = tsize A + tsize B + 1 := rfl
example : csize (Ctx.snoc Ctx.nil (Ty.base Ctx.nil)) = 2 := rfl

-- and it is a usable induction principle: every well-formed type sits in a
-- well-formed context, which needs both halves at once
theorem Wf.ok : ∀ {Γ : Ctx} {A : Ty Γ}, Wf Γ A → Ok Γ :=
  Wf.rec (motive_1 := fun _ _ => True) (motive_2 := fun Γ _ _ => Ok Γ)
    trivial (fun _ _ _ _ _ _ => trivial)
    (fun _ h _ => h) (fun _ _ _ _ _ h _ => h)

-- the two halves meet: what the propositional recursion proves is a statement
-- about what the data one computes
theorem Wf.size_pos : ∀ {Γ : Ctx} {A : Ty Γ}, Wf Γ A → 0 < tsize A :=
  Wf.rec (motive_1 := fun _ _ => True) (motive_2 := fun _ A _ => 0 < tsize A)
    trivial (fun _ _ _ _ _ _ => trivial)
    (fun _ _ _ => Nat.zero_lt_one)
    (fun _ _ _ _ _ _ _ => Nat.succ_pos _)

end OkAndWf

/-! ## Blocks of the shape people write them in

Two that are not a variation on anything above: the category-with-families
skeleton, which is what induction-induction is usually introduced with, and a
family of variables, whose constructors give their deleted index as a value of a
*sibling's* constructor rather than as a field.
-/

namespace CwF

mutual
inductive Con : Type where
  | nil  : Con
  | ext  : (Γ : Con) → Ty Γ → Con
inductive Ty : Con → Type where
  | base : (Γ : Con) → Ty Γ
  | pi   : (Γ : Con) → (A : Ty Γ) → Ty (Con.ext Γ A) → Ty Γ
inductive Sub : Con → Con → Type where
  | id  : (Γ : Con) → Sub Γ Γ
  | wk  : (Γ : Con) → (A : Ty Γ) → Sub (Con.ext Γ A) Γ
inductive Tm : (Γ : Con) → Ty Γ → Type where
  | var : (Γ : Con) → (A : Ty Γ) → Tm (Con.ext Γ A) (Ty.base (Con.ext Γ A))
  | lam : (Γ : Con) → (A : Ty Γ) → (B : Ty (Con.ext Γ A)) →
      Tm (Con.ext Γ A) B → Tm Γ (Ty.pi Γ A B)
end

-- four members, one motive each, and `Sub`'s two indices are two deleted
-- values of the same member
/--
info: @Tm.rec : {motive_1 : Con → Sort u_1} →
  {motive_2 : (a : Con) → Ty a → Sort u_1} →
    {motive_3 : (a a_1 : Con) → Sub a a_1 → Sort u_1} →
      {motive_4 : (Γ : Con) → (a : Ty Γ) → Tm Γ a → Sort u_1} →
        motive_1 Con.nil →
          ((Γ : Con) → (a : Ty Γ) → motive_1 Γ → motive_2 Γ a → motive_1 (Γ.ext a)) →
            ((Γ : Con) → motive_1 Γ → motive_2 Γ (Ty.base Γ)) →
              ((Γ : Con) →
                  (A : Ty Γ) →
                    (a : Ty (Γ.ext A)) → motive_1 Γ → motive_2 Γ A → motive_2 (Γ.ext A) a → motive_2 Γ (Ty.pi Γ A a)) →
                ((Γ : Con) → motive_1 Γ → motive_3 Γ Γ (Sub.id Γ)) →
                  ((Γ : Con) → (A : Ty Γ) → motive_1 Γ → motive_2 Γ A → motive_3 (Γ.ext A) Γ (Sub.wk Γ A)) →
                    ((Γ : Con) →
                        (A : Ty Γ) → motive_1 Γ → motive_2 Γ A → motive_4 (Γ.ext A) (Ty.base (Γ.ext A)) (Tm.var Γ A)) →
                      ((Γ : Con) →
                          (A : Ty Γ) →
                            (B : Ty (Γ.ext A)) →
                              (a : Tm (Γ.ext A) B) →
                                motive_1 Γ →
                                  motive_2 Γ A →
                                    motive_2 (Γ.ext A) B →
                                      motive_4 (Γ.ext A) B a → motive_4 Γ (Ty.pi Γ A B) (Tm.lam Γ A B a)) →
                        {Γ : Con} → {a : Ty Γ} → (t : Tm Γ a) → motive_4 Γ a t
-/
#guard_msgs in
#check @Tm.rec

-- and the recursion computes over all four at once
def size : {Γ : Con} → {A : Ty Γ} → Tm Γ A → Nat := fun {_} {_} t =>
  Tm.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    (motive_3 := fun _ _ _ => Nat) (motive_4 := fun _ _ _ => Nat)
    0 (fun _ _ a b => a + b + 1) (fun _ _ => 1) (fun _ _ _ _ a b => a + b + 1)
    (fun _ _ => 0) (fun _ _ _ _ => 0)
    (fun _ _ _ _ => 1) (fun _ _ _ _ _ _ _ ih => ih + 1) t

example (Γ : Con) (A : Ty Γ) : size (Tm.var Γ A) = 1 := rfl
example (Γ : Con) (A : Ty Γ) (B : Ty (Con.ext Γ A)) (t : Tm (Con.ext Γ A) B) :
    size (Tm.lam Γ A B t) = size t + 1 := rfl

/-- info: 'CwF.size' does not depend on any axioms -/
#guard_msgs in
#print axioms size

end CwF

namespace Vars

mutual
inductive Ctx : Type where
  | nil  : Ctx
  | snoc : (Γ : Ctx) → Ty Γ → Ctx
inductive Ty : Ctx → Type where
  | base : (Γ : Ctx) → Ty Γ
  | wk   : (Γ : Ctx) → (A : Ty Γ) → Ty Γ → Ty (Ctx.snoc Γ A)
inductive Var : (Γ : Ctx) → Ty Γ → Type where
  | zero : (Γ : Ctx) → (A : Ty Γ) → Var (Ctx.snoc Γ A) (Ty.wk Γ A A)
  | succ : (Γ : Ctx) → (A B : Ty Γ) → Var Γ B → Var (Ctx.snoc Γ A) (Ty.wk Γ A B)
end

-- both of `Var`'s indices are built rather than given: the context out of
-- `Ctx.snoc` and the type out of `Ty.wk`, and neither is a field
/--
info: @Var.rec : {motive_1 : Ctx → Sort u_1} →
  {motive_2 : (a : Ctx) → Ty a → Sort u_1} →
    {motive_3 : (Γ : Ctx) → (a : Ty Γ) → Var Γ a → Sort u_1} →
      motive_1 Ctx.nil →
        ((Γ : Ctx) → (a : Ty Γ) → motive_1 Γ → motive_2 Γ a → motive_1 (Γ.snoc a)) →
          ((Γ : Ctx) → motive_1 Γ → motive_2 Γ (Ty.base Γ)) →
            ((Γ : Ctx) → (A a : Ty Γ) → motive_1 Γ → motive_2 Γ A → motive_2 Γ a → motive_2 (Γ.snoc A) (Ty.wk Γ A a)) →
              ((Γ : Ctx) → (A : Ty Γ) → motive_1 Γ → motive_2 Γ A → motive_3 (Γ.snoc A) (Ty.wk Γ A A) (Var.zero Γ A)) →
                ((Γ : Ctx) →
                    (A B : Ty Γ) →
                      (a : Var Γ B) →
                        motive_1 Γ →
                          motive_2 Γ A →
                            motive_2 Γ B → motive_3 Γ B a → motive_3 (Γ.snoc A) (Ty.wk Γ A B) (Var.succ Γ A B a)) →
                  {Γ : Ctx} → {a : Ty Γ} → (t : Var Γ a) → motive_3 Γ a t
-/
#guard_msgs in
#check @Var.rec

def depth : {Γ : Ctx} → {A : Ty Γ} → Var Γ A → Nat := fun {_} {_} v =>
  Var.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat) (motive_3 := fun _ _ _ => Nat)
    0 (fun _ _ a b => a + b + 1) (fun _ _ => 1) (fun _ _ _ _ a b => a + b)
    (fun _ _ _ _ => 0) (fun _ _ _ _ _ _ _ ih => ih + 1) v

example (Γ : Ctx) (A : Ty Γ) : depth (Var.zero Γ A) = 0 := rfl
example (Γ : Ctx) (A B : Ty Γ) (v : Var Γ B) : depth (Var.succ Γ A B v) = depth v + 1 := rfl

/-- info: 'Vars.depth' does not depend on any axioms -/
#guard_msgs in
#print axioms depth

end Vars

/-! ### Two members leaving together

A member the block still reaches cannot leave -- but the member reaching it may
be leaving too, and then there is nothing holding it in after all.  `Sub.ext`
reads a `Tm`, so `Tm` is no candidate to begin with; `Sub` is one, and once `Sub`
is out, `Tm` is a candidate in its turn.  Both go, and what stays -- `Ctx` and
`Ty`, the pair that is genuinely induction-inductive -- is what the erasure was
for in the first place.

They are declared separately rather than as one block, since only a member
genuinely mutual with another has to share a declaration with it.  That is what
gives each of them a kernel recursor at a single motive, which is the shape the
compiled companion is written out of, and it is why `Sub.ext`'s field reads `Tm`
rather than the inductive one name over.
-/

namespace TwoLeave

mutual
inductive Ctx : Type where
  | nil  : Ctx
  | snoc : (Γ : Ctx) → Ty Γ → Ctx
inductive Ty : Ctx → Type where
  | base : (Γ : Ctx) → Ty Γ
  | pi   : (Γ : Ctx) → (A : Ty Γ) → Ty (Ctx.snoc Γ A) → Ty Γ
inductive Tm : (Γ : Ctx) → Ty Γ → Type where
  | var : (Γ : Ctx) → (A : Ty Γ) → Tm Γ A
inductive Sub : Ctx → Ctx → Type where
  | id  : (Γ : Ctx) → Sub Γ Γ
  | ext : (Γ Δ : Ctx) → (A : Ty Δ) → Sub Γ Δ → Tm Γ (Ty.base Γ) → Sub Γ (Ctx.snoc Δ A)
end

/--
info: def TwoLeave.Tm : (Γ : Ctx) → Ty Γ → Type :=
Tm._ind
-/
#guard_msgs in
#print Tm

/--
info: def TwoLeave.Sub : Ctx → Ctx → Type :=
Sub._ind
-/
#guard_msgs in
#print Sub

-- four motives all the same, and the `ext` minor is handed a hypothesis at both
-- of its recursive fields: the one at `Sub`, which the kernel's own recursor
-- over `Sub._ind` supplies, and the one at `Tm`, which this recursor works out
-- for itself by calling the widened `Tm.rec` on the same motives and minors
/--
info: @Sub.rec : {motive_1 : Ctx → Sort u_1} →
  {motive_2 : (a : Ctx) → Ty a → Sort u_1} →
    {motive_3 : (Γ : Ctx) → (a : Ty Γ) → Tm Γ a → Sort u_1} →
      {motive_4 : (a a_1 : Ctx) → Sub a a_1 → Sort u_1} →
        motive_1 Ctx.nil →
          ((Γ : Ctx) → (a : Ty Γ) → motive_1 Γ → motive_2 Γ a → motive_1 (Γ.snoc a)) →
            ((Γ : Ctx) → motive_1 Γ → motive_2 Γ (Ty.base Γ)) →
              ((Γ : Ctx) →
                  (A : Ty Γ) →
                    (a : Ty (Γ.snoc A)) →
                      motive_1 Γ → motive_2 Γ A → motive_2 (Γ.snoc A) a → motive_2 Γ (Ty.pi Γ A a)) →
                ((Γ : Ctx) → (A : Ty Γ) → motive_1 Γ → motive_2 Γ A → motive_3 Γ A (Tm.var Γ A)) →
                  ((Γ : Ctx) → motive_1 Γ → motive_4 Γ Γ (Sub.id Γ)) →
                    ((Γ Δ : Ctx) →
                        (A : Ty Δ) →
                          (a : Sub Γ Δ) →
                            (a_1 : Tm Γ (Ty.base Γ)) →
                              motive_1 Γ →
                                motive_1 Δ →
                                  motive_2 Δ A →
                                    motive_4 Γ Δ a →
                                      motive_3 Γ (Ty.base Γ) a_1 → motive_4 Γ (Δ.snoc A) (Sub.ext Γ Δ A a a_1)) →
                      {a a_1 : Ctx} → (t : Sub a a_1) → motive_4 a a_1 t
-/
#guard_msgs in
#check @Sub.rec

-- and a `match` over each of them, one calling the other
def tsize : {Γ : Ctx} → {A : Ty Γ} → Tm Γ A → Nat
  | _, _, .var _ _ => 1

def ssize : {Γ Δ : Ctx} → Sub Γ Δ → Nat
  | _, _, .id _          => 0
  | _, _, .ext _ _ _ s t => ssize s + tsize t

/-- info: 1 -/
#guard_msgs in
#eval ssize (Sub.ext .nil .nil (.base .nil) (.id .nil) (.var .nil (.base .nil)))

/-- info: 'TwoLeave.ssize' does not depend on any axioms -/
#guard_msgs in
#print axioms ssize

example {Γ Δ : Ctx} (s : Sub Γ Δ) : True := by
  induction s with
  | id Γ => trivial
  | ext Γ Δ A s t ih => trivial

end TwoLeave

/-! ### An index no erasure could have stated

`F13`'s index is a `Nat → Ctx13`: it binds an argument before it reaches a
member of the block, and there is no pre-type to state that at, so the erasure
has to refuse it.  A member that leaves the block is never erased, and nothing
names `F13`, so it leaves -- and the index is just an index.  The whole shape is
accepted on the strength of one member not having to take part.

This also fixes the reach of the recursion: the `mk` alternative is handed a
hypothesis at `Ctx13` for every `Nat`, which is what a function-valued index
into the block ought to give and what no erasure of `F13` could have produced.
-/

namespace FnIndex

mutual
inductive Ctx13 : Type where
  | nil  : Ctx13
  | snoc : (Γ : Ctx13) → Ty13 Γ → Ctx13
inductive Ty13 : Ctx13 → Type where
  | base : (Γ : Ctx13) → Ty13 Γ
inductive F13 : (Nat → Ctx13) → Type where
  | mk : (f : Nat → Ctx13) → F13 f
end

/--
info: def FnIndex.F13 : (Nat → Ctx13) → Type :=
F13._ind
-/
#guard_msgs in
#print F13

/--
info: @F13.rec : {motive_1 : Ctx13 → Sort u_1} →
  {motive_2 : (a : Ctx13) → Ty13 a → Sort u_1} →
    {motive_3 : (a : Nat → Ctx13) → F13 a → Sort u_1} →
      motive_1 Ctx13.nil →
        ((Γ : Ctx13) → (a : Ty13 Γ) → motive_1 Γ → motive_2 Γ a → motive_1 (Γ.snoc a)) →
          ((Γ : Ctx13) → motive_1 Γ → motive_2 Γ (Ty13.base Γ)) →
            ((f : Nat → Ctx13) → ((a : Nat) → motive_1 (f a)) → motive_3 f (F13.mk f)) →
              {a : Nat → Ctx13} → (t : F13 a) → motive_3 a t
-/
#guard_msgs in
#check @F13.rec

-- the block's recursion is unchanged by the member that left: `Ctx13.rec` takes
-- the same three motives and the same four alternatives
/--
info: @Ctx13.rec : {motive_1 : Ctx13 → Sort u_1} →
  {motive_2 : (a : Ctx13) → Ty13 a → Sort u_1} →
    {motive_3 : (a : Nat → Ctx13) → F13 a → Sort u_1} →
      motive_1 Ctx13.nil →
        ((Γ : Ctx13) → (a : Ty13 Γ) → motive_1 Γ → motive_2 Γ a → motive_1 (Γ.snoc a)) →
          ((Γ : Ctx13) → motive_1 Γ → motive_2 Γ (Ty13.base Γ)) →
            ((f : Nat → Ctx13) → ((a : Nat) → motive_1 (f a)) → motive_3 f (F13.mk f)) → (t : Ctx13) → motive_1 t
-/
#guard_msgs in
#check @Ctx13.rec

-- and the index is reachable by `match`, which is what makes the acceptance
-- worth anything
def head : {f : Nat → Ctx13} → F13 f → Ctx13
  | _, .mk f => f 0

def len : Ctx13 → Nat :=
  Ctx13.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    (motive_3 := fun _ _ => Nat)
    0 (fun _ _ n _ => n + 1) (fun _ _ => 0) (fun _ g => g 0)

/-- info: 1 -/
#guard_msgs in
#eval len (head (F13.mk (fun _ => Ctx13.snoc .nil (.base .nil))))

end FnIndex

/-! ## Outside the narrow class

Every one of these is rejected with an explanation of what erasure could not do,
rather than lowered wrongly.
-/

-- a nesting of one is not one either, and this is the case that needs saying
-- out loud: denesting would happily turn the index into a copy and hand back a
-- `Ty14` indexed by a name nobody wrote
/--
error: The index `a✝` of `Ty14` is
  List Ctx14
which mentions a member of the block without being one, so the erasure has no pre-type to state it at
-/
#guard_msgs in
mutual
inductive Ctx14 : Type where
  | nil : Ctx14
inductive Ty14 : List Ctx14 → Type where
  | base : (Γs : List Ctx14) → Ty14 Γs
end

-- what the constructor builds, the well-formedness has to restate in the
-- pre-world, so every part of it needs a pre-world reading.  An erased proof
-- has none: the pre-constructor drops it
/--
error: The resulting type of `Tm10.mk` builds the index
  Ty10.wit Γ h
which the erasure has to delete, and the field `h` in it is an erased proof, which the pre-world drops
-/
#guard_msgs in
mutual
inductive Ctx10 : Type where
  | nil  : Ctx10
  | snoc : (Γ : Ctx10) → Ty10 Γ → Ctx10
inductive Ty10 : Ctx10 → Type where
  | base : (Γ : Ctx10) → Ty10 Γ
  | wit  : (Γ : Ctx10) → Ok10 Γ → Ty10 Γ
inductive Ok10 : Ctx10 → Prop where
  | nil : Ok10 Ctx10.nil
inductive Tm10 : (Γ : Ctx10) → Ty10 Γ → Type where
  | mk : (Γ : Ctx10) → (h : Ok10 Γ) → Tm10 Γ (Ty10.wit Γ h)
end

-- induction-induction through `Prop` twice over.  Erasure buys the one crossing
-- from data to `Prop`; the propositions it lands on are a mutual block of their
-- own, and that block is subject to the same arity rule the whole exercise is
-- here to get around.  `Ctx6.dep` is what keeps `Sub6` in the block: without it
-- nothing else is stated with `Sub6` and it would leave rather than be refused,
-- which is the `PeelPropOnProp` case below.
/--
error: The arity of `Sub6` mentions `Ty6`, which is another proposition of the block.  Erasure sends the data members to one mutual inductive and the propositions to a second one, and a mutual inductive's members may not appear in one another's arities -- so a proposition may be indexed by the block's data, but not by another of its propositions.  One that nothing else in the block is stated with leaves the block before this rule reaches it; this one is named by something that stays
-/
#guard_msgs in
mutual
inductive Ctx6 : Type where
  | nil : Ctx6
  | ext : (Γ : Ctx6) → Ty6 Γ → Ctx6
  | dep : (Γ : Ctx6) → (A : Ty6 Γ) → Sub6 Γ A → Ctx6
inductive Ty6 : Ctx6 → Prop where
  | base : Ty6 Γ
inductive Sub6 : (Γ : Ctx6) → Ty6 Γ → Prop where
  | id : Sub6 Γ A
end

-- nothing but propositions.  Erasure keeps the data and rebuilds it as a
-- subtype of what it kept, so a block with no data member gives it nothing to
-- work on -- and the arity rule it would be lifting is `Prop` on `Prop` again.
-- `AP7` naming `AQ7` is what keeps them together: a chain of propositions comes
-- apart under the peel instead, which is `PeelAllProps` below.
/--
error: Every member of this induction-inductive block is a proposition; there is nothing for the erasure to keep
-/
#guard_msgs in
mutual
inductive AP7 : Prop where
  | mk : (h : AP7) → AQ7 h → AP7
inductive AQ7 : AP7 → Prop where
  | mk : AQ7 h
end

-- a recursive field that *binds* a member: there is no way back from the
-- pre-world without a well-formedness proof, so `f` could not be applied
/--
error: The field `f` of `T3.node` binds a member of the block before recursing, which erasure cannot follow: a pre-world value cannot be turned back into a real one without its well-formedness proof.
  T3 → T3
-/
#guard_msgs in
mutual
inductive T3 : Type where
  | leaf : T3
  | node : (f : T3 → T3) → G3 f → T3
inductive G3 : (T3 → T3) → Prop where
  | id : G3 id
end

-- The data members disagree about their universe, so the pre-block goes to the
-- lowering -- but `A4 : Type` has a `B4 : Type 1` field, and no amount of
-- lowering makes a field fit inside a type smaller than it is.
/--
error: The data members `A4` and `B4` live in different universes, `Type` and `Type 1`.  Lowering the erased pre-block into ordinary inductives is what lifts the kernel's same-universe rule, and here it did not go through:
  (kernel) universe level of type_of(arg #1) of 'A4._pre.mk' is too big for the corresponding inductive datatype

Note: What the lowering lifts is the rule that the *members* of a mutual block agree about their universe.  The two rules underneath it stand: members that recurse into one another have to agree anyway -- an edge puts one universe at or below the other, so a cycle makes them equal -- and a field still has to fit inside the member it belongs to.  `X._pre` above is the erased form of `X`
-/
#guard_msgs in
mutual
inductive A4 : Type where
  | mk : (b : B4) → P4 b → A4
inductive B4 : Type 1 where
  | mk : B4
inductive P4 : B4 → Prop where
  | mk : P4 .mk
end

-- `List C5` denests into a member, so `P5` is a proposition indexed by data
-- after all; what stops the block is the field, which pins the copy's `cons`
-- rather than naming a field of the constructor it stands in
/--
error: The proof field `a✝` of `C5.snoc` mentions a data member of the block in its type, so erasing it would not be definitionally invisible:
  P5 (C5.nested_List_1.cons a C5.nested_List_1.nil)
-/
#guard_msgs in
mutual
inductive C5 : Type where
  | nil : C5
  | snoc : (a : C5) → P5 [a] → C5
inductive P5 : List C5 → Prop where
  | nil : P5 []
end

-- a data member is encoded as a `Subtype`, which lands in `Sort (max 1 u)`
/--
error: The data member `S` lives at `Sort u`, which could still be `Prop`.  It is encoded as a subtype, and `Subtype` lands one universe up from `Prop`, so a data member's universe has to be visibly non-zero -- `Type v` rather than `Sort v`
-/
#guard_msgs in
mutual
inductive S (α : Sort u) : Sort u where
  | mk : (a : S α) → PS α a → S α
inductive PS (α : Sort u) : S α → Prop where
  | mk : (a : S α) → PS α a
end

-- the whole encoding runs under one telescope of parameters
/--
error: `P7` takes 1 parameter(s) and `Q7` takes 0; every member of a mutual block must take the same ones
-/
#guard_msgs in
mutual
inductive P7 (α : Type) : Type where
  | nil : P7 α
  | mk : (x : P7 α) → Q7 x → P7 α
inductive Q7 : P7 Nat → Prop where
  | nil : Q7 .nil
end

-- and one list of universe parameters
/--
error: `K1` and `K2` declare different universe parameters; every member of a mutual block must declare the same ones
-/
#guard_msgs in
mutual
inductive K1.{u} : Type u where
  | mk : (k : K1.{u}) → K2 k → K1
inductive K2.{u, v} : K1.{u} → Prop where
  | mk : (k : K1.{u}) → K2 k
end

-- a constructor of an indexed family has to say what its indices are, or the
-- resulting type would be the unapplied family, which is not a proposition
/--
error: Missing resulting type for constructor `Q8.mk`.  It must be given because `Q8` is an inductive family
-/
#guard_msgs in
mutual
inductive P8 where
  | nil
  | mk : (x : P8) → Q8 x → P8
inductive Q8 : P8 → Prop where
  | mk
end

-- a resulting type left out is read as `Type`, and the fields have to fit: the
-- guess is already in the sibling's elaborated fields by the time we know
/--
error: `Cell` gives no resulting type, so it was read as `Type`; but the field `α` of `Cell.mk` lives in `Type 1`, which does not fit.  Write the resulting type out: `inductive Cell : Type 1`
-/
#guard_msgs in
mutual
inductive Cell where
  | mk : (α : Type) → (c : Cell) → CellOk c → Cell
inductive CellOk : Cell → Prop where
  | mk : (c : Cell) → CellOk c
end

/-! ## A nesting whose parameter mentions a constructor-local

Erasure alone cannot reach the field `v : List (LocalWrap Cx n)` -- it is neither
a member's type nor a proof of one of the block's propositions -- so the block
has to be denested first.  But the nesting's parameter mentions `n`, a field of
the constructor it sits in, so there is no single `List (LocalWrap Cx ·)` to
copy: the copy is indexed by `n` and stands for all of them at once, and so is
the copy of `LocalWrap` inside it.

Every copy stays hidden.  `motive_3` and `motive_4` below are over the originals,
`List (LocalWrap Cx n)` and `LocalWrap Cx n`, with the `n` in front.
-/

inductive LocalWrap (α : Type) (n : Nat) : Type where
  | mk (a : α) : LocalWrap α n

mutual
inductive Cx : Type where
  | nil
  | snoc (n : Nat) (v : List (LocalWrap Cx n)) (Γ : Cx) (h : CxOk Γ) : Cx
inductive CxOk : Cx → Prop where
  | nil : CxOk .nil
end

/-- info: Cx.snoc : (n : Nat) → List (LocalWrap Cx n) → (Γ : Cx) → CxOk Γ → Cx -/
#guard_msgs in
#check @Cx.snoc

/-- info: CxOk.nil : CxOk Cx.nil -/
#guard_msgs in
#check @CxOk.nil

/--
info: @Cx.rec : {motive_1 : Cx → Sort u_1} →
  {motive_2 : (a : Cx) → motive_1 a → CxOk a → Prop} →
    {motive_3 : (n : Nat) → List (LocalWrap Cx n) → Sort u_1} →
      {motive_4 : (n : Nat) → LocalWrap Cx n → Sort u_1} →
        (nil : motive_1 Cx.nil) →
          ((n : Nat) →
              (v : List (LocalWrap Cx n)) →
                (Γ : Cx) →
                  (h : CxOk Γ) → motive_3 n v → (Γ_ih : motive_1 Γ) → motive_2 Γ Γ_ih h → motive_1 (Cx.snoc n v Γ h)) →
            motive_2 Cx.nil nil CxOk.nil →
              ((n : Nat) → motive_3 n []) →
                ((n : Nat) →
                    (head : LocalWrap Cx n) →
                      (tail : List (LocalWrap Cx n)) → motive_4 n head → motive_3 n tail → motive_3 n (head :: tail)) →
                  ((n : Nat) → (a : Cx) → motive_1 a → motive_4 n (LocalWrap.mk a)) → (t : Cx) → motive_1 t
-/
#guard_msgs in
#check @Cx.rec

/-- info: @Cx.nested_List_1.ofOrig : {n : Nat} → List (LocalWrap Cx n) → Cx.nested_List_1 n -/
#guard_msgs in
#check @Cx.nested_List_1.ofOrig

/--
info: @Cx.nested_LocalWrap_2.toOrig : {n : Nat} → Cx.nested_LocalWrap_2 n → LocalWrap Cx n
-/
#guard_msgs in
#check @Cx.nested_LocalWrap_2.toOrig

namespace Cx

def size (Γ : Cx) : Nat :=
  Cx.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ _ => True)
    (motive_3 := fun _ _ => Nat) (motive_4 := fun _ _ => Nat)
    1 (fun _ _ _ _ ihv ihΓ _ => ihv + ihΓ) trivial
    (fun _ => 0) (fun _ _ _ ihh iht => ihh + iht)
    (fun _ _ ih => ih)
    Γ

example : size .nil = 1 := rfl

/-- info: 3 -/
#guard_msgs in
#eval size (.snoc 3 [.mk .nil, .mk .nil] .nil .nil)

/-- info: 'Cx.size' does not depend on any axioms -/
#guard_msgs in
#print axioms size

end Cx

/-! ## A nesting whose parameter mentions a member of the block

The section above copies a nesting at a constructor-local by making the local an
index of the copy, and that needed the local's own type to be free of the block.
When it is not -- `List (Ty Γ)` in a block where `Ty` is indexed by `Ctx`, so the
copy is indexed by a `Γ : Ctx` -- the copy is induction-inductive in its own
right.  Which is no obstacle, because the whole of this file is the erasure of
exactly that: the copy joins the block as an ordinary member and is erased with
the rest of it.

So a nesting need not be at anything in particular.  The three blocks here nest
`List` at a member indexed by another member, `Subtype` at a *proposition* of the
block, and `Eq` at two data members, and each one keeps the declaration the user
wrote.
-/

namespace NestAtMember

mutual
inductive Ctx : Type where
  | nil  : Ctx
  | snoc : (Γ : Ctx) → Ty Γ → Ctx
inductive Ty : Ctx → Type where
  | base : (Γ : Ctx) → Ty Γ
  | tup  : (Γ : Ctx) → List (Ty Γ) → Ty Γ
end

/-- info: Ty.tup : (Γ : Ctx) → List (Ty Γ) → Ty Γ -/
#guard_msgs in
#check @Ty.tup

-- the copy is hidden: `motive_3` is over `List (Ty Γ)` itself, with the `Γ` the
-- nesting was found at in front, and the minors are `List`'s own constructors
/--
info: @Ty.rec : {motive_1 : Ctx → Sort u_1} →
  {motive_2 : (a : Ctx) → Ty a → Sort u_1} →
    {motive_3 : (Γ : Ctx) → List (Ty Γ) → Sort u_1} →
      motive_1 Ctx.nil →
        ((Γ : Ctx) → (a : Ty Γ) → motive_1 Γ → motive_2 Γ a → motive_1 (Γ.snoc a)) →
          ((Γ : Ctx) → motive_1 Γ → motive_2 Γ (Ty.base Γ)) →
            ((Γ : Ctx) → (a : List (Ty Γ)) → motive_1 Γ → motive_3 Γ a → motive_2 Γ (Ty.tup Γ a)) →
              ((Γ : Ctx) → motive_1 Γ → motive_3 Γ []) →
                ((Γ : Ctx) →
                    (head : Ty Γ) →
                      (tail : List (Ty Γ)) →
                        motive_1 Γ → motive_2 Γ head → motive_3 Γ tail → motive_3 Γ (head :: tail)) →
                  {a : Ctx} → (t : Ty a) → motive_2 a t
-/
#guard_msgs in
#check @Ty.rec

def tsize : {Γ : Ctx} → Ty Γ → Nat := fun {_} A =>
  Ty.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    (motive_3 := fun _ _ => Nat)
    0 (fun _ _ n m => n + m + 1) (fun _ _ => 1) (fun _ _ _ n => n + 1)
    (fun _ _ => 0) (fun _ _ _ _ n m => n + m) A

example (Γ : Ctx) : tsize (Ty.base Γ) = 1 := rfl
example (Γ : Ctx) : tsize (Ty.tup Γ []) = 1 := rfl
example (Γ : Ctx) (A B : Ty Γ) : tsize (Ty.tup Γ [A, B]) = tsize A + tsize B + 1 := rfl

/-- info: 3 -/
#guard_msgs in
#eval tsize (Ty.tup Ctx.nil [Ty.base Ctx.nil, Ty.base Ctx.nil])

/-- info: 'NestAtMember.tsize' does not depend on any axioms -/
#guard_msgs in
#print axioms tsize

end NestAtMember

-- a proposition of the block hidden inside a piece of data.  `Subtype` is nested
-- at `Ok2 v`, so the copy is indexed by the `v` it was found at -- and `Ok2 v` is
-- a proposition *of this block*, which is what the erasure is in the middle of
-- deciding.  The copy comes out indexed by the erased `Vec2` all the same
namespace SubAtProp

-- the subtype's binder `m` is unused on purpose: the point is the `Ok2 v`
set_option linter.unusedVariables false

mutual
inductive Vec2 : Type where
  | nil : Vec2
  | cons : (v : Vec2) → (n : { m : Nat // Ok2 v }) → Vec2
inductive Ok2 : Vec2 → Prop where
  | nil : Ok2 .nil
end

/-- info: Vec2.cons : (v : Vec2) → { m // Ok2 v } → Vec2 -/
#guard_msgs in
#check @Vec2.cons

/--
info: @Vec2.rec : {motive_1 : Vec2 → Sort u_1} →
  {motive_2 : (v : Vec2) → { m // Ok2 v } → Sort u_1} →
    motive_1 Vec2.nil →
      ((v : Vec2) → (n : { m // Ok2 v }) → motive_1 v → motive_2 v n → motive_1 (v.cons n)) →
        ((v : Vec2) → (val : Nat) → (property : Ok2 v) → motive_1 v → motive_2 v ⟨val, property⟩) →
          (t : Vec2) → motive_1 t
-/
#guard_msgs in
#check @Vec2.rec

def vlen : Vec2 → Nat :=
  Vec2.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    0 (fun _ _ ih k => ih + k) (fun _ val _ _ => val)

example : vlen Vec2.nil = 0 := rfl
example (v : Vec2) (n : { m : Nat // Ok2 v }) : vlen (Vec2.cons v n) = vlen v + n.val := rfl

/-- info: 7 -/
#guard_msgs in
#eval vlen (Vec2.cons Vec2.nil ⟨7, Ok2.nil⟩)

/-- info: 'SubAtProp.vlen' does not depend on any axioms -/
#guard_msgs in
#print axioms vlen

end SubAtProp

-- `Eq` at two data members.  The copy of a proposition is a proposition, so it
-- is erased along with the block's own and never reaches a motive: the recursor
-- is over `C1` alone, and the field is still the equation that was written
namespace EqAtData

mutual
inductive C1 : Type where
  | nil : C1
  | snoc : (a : C1) → (b : C1) → (h : a = b) → P1 a → C1
inductive P1 : C1 → Prop where
  | nil : P1 .nil
end

/-- info: C1.snoc : (a b : C1) → a = b → P1 a → C1 -/
#guard_msgs in
#check @C1.snoc

/--
info: @C1.rec : {motive : C1 → Sort u_1} →
  motive C1.nil →
    ((a b : C1) → (h : a = b) → (a_1 : P1 a) → motive a → motive b → motive (a.snoc b h a_1)) → (t : C1) → motive t
-/
#guard_msgs in
#check @C1.rec

def csize : C1 → Nat := C1.rec 0 (fun _ _ _ _ x y => x + y + 1)

example : csize C1.nil = 0 := rfl
example (a b : C1) (h : a = b) (p : P1 a) :
    csize (C1.snoc a b h p) = csize a + csize b + 1 := rfl

/-- info: 'EqAtData.csize' does not depend on any axioms -/
#guard_msgs in
#print axioms csize

end EqAtData

/-! ### The nesting sits under an index the constructor built

`Ty.pi` nests `List` at `Ctx.snoc Γ A`, so the copy's leading locals are both
`Γ` and the `A` the context was built from, and the element type is `Ty` at the
built context.  Nothing about the copy has to know that: it gains the two locals
the parameter mentions, in dependency order, and the erasure deletes the built
index in the copy's constructors exactly as it does in the block's own.
-/

namespace BuiltUnderNesting

mutual
inductive Ctx : Type where
  | nil  : Ctx
  | snoc : (Γ : Ctx) → Ty Γ → Ctx
inductive Ty : Ctx → Type where
  | base : (Γ : Ctx) → Ty Γ
  | pi   : (Γ : Ctx) → (A : Ty Γ) → List (Ty (Ctx.snoc Γ A)) → Ty Γ
end

/-- info: Ty.pi : (Γ : Ctx) → (A : Ty Γ) → List (Ty (Γ.snoc A)) → Ty Γ -/
#guard_msgs in
#check @Ty.pi

-- `motive_3` carries both locals, and the `cons` minor recurses at the built
-- context -- `motive_2 (Γ.snoc A) head`, not `motive_2 Γ head`
/--
info: @Ty.rec : {motive_1 : Ctx → Sort u_1} →
  {motive_2 : (a : Ctx) → Ty a → Sort u_1} →
    {motive_3 : (Γ : Ctx) → (A : Ty Γ) → List (Ty (Γ.snoc A)) → Sort u_1} →
      motive_1 Ctx.nil →
        ((Γ : Ctx) → (a : Ty Γ) → motive_1 Γ → motive_2 Γ a → motive_1 (Γ.snoc a)) →
          ((Γ : Ctx) → motive_1 Γ → motive_2 Γ (Ty.base Γ)) →
            ((Γ : Ctx) →
                (A : Ty Γ) →
                  (a : List (Ty (Γ.snoc A))) → motive_1 Γ → motive_2 Γ A → motive_3 Γ A a → motive_2 Γ (Ty.pi Γ A a)) →
              ((Γ : Ctx) → (A : Ty Γ) → motive_1 Γ → motive_2 Γ A → motive_3 Γ A []) →
                ((Γ : Ctx) →
                    (A : Ty Γ) →
                      (head : Ty (Γ.snoc A)) →
                        (tail : List (Ty (Γ.snoc A))) →
                          motive_1 Γ →
                            motive_2 Γ A → motive_2 (Γ.snoc A) head → motive_3 Γ A tail → motive_3 Γ A (head :: tail)) →
                  {a : Ctx} → (t : Ty a) → motive_2 a t
-/
#guard_msgs in
#check @Ty.rec

def tsize : {Γ : Ctx} → Ty Γ → Nat := fun {_} A =>
  Ty.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    (motive_3 := fun _ _ _ => Nat)
    0 (fun _ _ n m => n + m + 1) (fun _ _ => 1) (fun _ _ _ _ n m => n + m + 1)
    (fun _ _ _ _ => 0) (fun _ _ _ _ _ _ n m => n + m) A

example (Γ : Ctx) (A : Ty Γ) : tsize (Ty.pi Γ A []) = tsize A + 0 + 1 := rfl
example (Γ : Ctx) (A : Ty Γ) (x y : Ty (Ctx.snoc Γ A)) :
    tsize (Ty.pi Γ A [x, y]) = tsize A + (tsize x + tsize y) + 1 := rfl

/-- info: 4 -/
#guard_msgs in
#eval tsize (Ty.pi Ctx.nil (Ty.base Ctx.nil) [Ty.base _, Ty.base _])

/-- info: 'BuiltUnderNesting.tsize' does not depend on any axioms -/
#guard_msgs in
#print axioms tsize

end BuiltUnderNesting

/-! ### A whole mutual family nested at a member

Copying one member of a mutual container copies all of them, since they name each
other, and each copy picks up the same locals.  Both come back as themselves.
-/

namespace FamilyAtMember

mutual
inductive RoseA (α : Type) : Type where
  | node : α → RoseB α → RoseA α
inductive RoseB (α : Type) : Type where
  | nil : RoseB α
  | cons : RoseA α → RoseB α → RoseB α
end

mutual
inductive Ctx : Type where
  | nil  : Ctx
  | snoc : (Γ : Ctx) → Ty Γ → Ctx
inductive Ty : Ctx → Type where
  | base : (Γ : Ctx) → Ty Γ
  | rose : (Γ : Ctx) → RoseA (Ty Γ) → Ty Γ
end

/-- info: Ty.rose : (Γ : Ctx) → RoseA (Ty Γ) → Ty Γ -/
#guard_msgs in
#check @Ty.rose

/--
info: @Ty.rec : {motive_1 : Ctx → Sort u_1} →
  {motive_2 : (a : Ctx) → Ty a → Sort u_1} →
    {motive_3 : (Γ : Ctx) → RoseA (Ty Γ) → Sort u_1} →
      {motive_4 : (Γ : Ctx) → RoseB (Ty Γ) → Sort u_1} →
        motive_1 Ctx.nil →
          ((Γ : Ctx) → (a : Ty Γ) → motive_1 Γ → motive_2 Γ a → motive_1 (Γ.snoc a)) →
            ((Γ : Ctx) → motive_1 Γ → motive_2 Γ (Ty.base Γ)) →
              ((Γ : Ctx) → (a : RoseA (Ty Γ)) → motive_1 Γ → motive_3 Γ a → motive_2 Γ (Ty.rose Γ a)) →
                ((Γ : Ctx) →
                    (a : Ty Γ) →
                      (a_1 : RoseB (Ty Γ)) →
                        motive_1 Γ → motive_2 Γ a → motive_4 Γ a_1 → motive_3 Γ (RoseA.node a a_1)) →
                  ((Γ : Ctx) → motive_1 Γ → motive_4 Γ RoseB.nil) →
                    ((Γ : Ctx) →
                        (a : RoseA (Ty Γ)) →
                          (a_1 : RoseB (Ty Γ)) →
                            motive_1 Γ → motive_3 Γ a → motive_4 Γ a_1 → motive_4 Γ (RoseB.cons a a_1)) →
                      {a : Ctx} → (t : Ty a) → motive_2 a t
-/
#guard_msgs in
#check @Ty.rec

end FamilyAtMember

/-! ### The same, through a parameter, a universe and a second layer

A nesting at a member is not a special case of anything, so the things that were
already invisible to the rest of this file stay invisible to it: a parameter of
the block, a universe parameter, and a container nested inside a container.
-/

namespace NestVariations

mutual
inductive PCtx (α : Type) : Type where
  | nil  : PCtx α
  | snoc : (Γ : PCtx α) → PTy α Γ → PCtx α
inductive PTy (α : Type) : PCtx α → Type where
  | base : (Γ : PCtx α) → α → PTy α Γ
  | tup  : (Γ : PCtx α) → List (PTy α Γ) → PTy α Γ
end

/-- info: @PTy.tup : {α : Type} → (Γ : PCtx α) → List (PTy α Γ) → PTy α Γ -/
#guard_msgs in
#check @PTy.tup

mutual
inductive UCtx : Type u where
  | nil  : UCtx
  | snoc : (Γ : UCtx) → UTy Γ → UCtx
inductive UTy : UCtx.{u} → Type u where
  | base : (Γ : UCtx) → UTy Γ
  | tup  : (Γ : UCtx) → List (UTy Γ) → UTy Γ
end

/-- info: UTy.tup : (Γ : UCtx) → List (UTy Γ) → UTy Γ -/
#guard_msgs in
#check @UTy.tup

-- the level really is a parameter, not one that quietly collapsed
/-- info: UCtx : Type 5 -/
#guard_msgs in
#check UCtx.{5}

mutual
inductive DCtx : Type where
  | nil  : DCtx
  | snoc : (Γ : DCtx) → DTy Γ → DCtx
inductive DTy : DCtx → Type where
  | base : (Γ : DCtx) → DTy Γ
  | tup  : (Γ : DCtx) → List (List (DTy Γ)) → DTy Γ
end

/-- info: DTy.tup : (Γ : DCtx) → List (List (DTy Γ)) → DTy Γ -/
#guard_msgs in
#check @DTy.tup

def dsize : {Γ : DCtx} → DTy Γ → Nat := fun {_} A =>
  DTy.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    (motive_3 := fun _ _ => Nat) (motive_4 := fun _ _ => Nat)
    0 (fun _ _ n m => n + m + 1) (fun _ _ => 1) (fun _ _ _ n => n + 1)
    (fun _ _ => 0) (fun _ _ _ _ n m => n + m)
    (fun _ _ => 0) (fun _ _ _ _ n m => n + m) A

example (Γ : DCtx) (x y : DTy Γ) :
    dsize (DTy.tup Γ [[x], [y]]) = dsize x + dsize y + 1 := rfl

/-- info: 'NestVariations.dsize' does not depend on any axioms -/
#guard_msgs in
#print axioms dsize

end NestVariations

/-! ### A proposition whose recursion runs through a copy

`Ok.node` holds a whole list of proofs, so recursing on `Ok` means recursing on
the list too, and the list is a denested copy.  The recursor gets a motive for
it -- stated over `PL`, the container that was written, not over the copy -- and
minors for `PL`'s own constructors.

The `Prop` side of the bridge is cheaper than the data side here.  A copy a
proposition's recursion reaches is a copy of a proposition, so a minor concludes
at a *proof*, and the constructor the bridge renamed and the raw one behind it
are the same proof to the kernel.  Nothing has to be transported back -- which
holds only because no index of `Ok` was built out of a copy; the next section is
where that stops being true.
-/

namespace PropThroughCopy

inductive PL (α : Sort u) (n : Nat) : Prop where
  | nil
  | cons (a : α) (r : PL α n)

/--
trace: [Mumi.indind] no recursor over the whole block: `PropThroughCopy.T.nested_PL_1` is wanted at the very term it is being proved at, and is not settled yet
-/
#guard_msgs(whitespace := lax) in
set_option trace.Mumi.indind true in
mutual
inductive T where
  | tip
  | node (t : T) : T
inductive Ok : T → Prop where
  | tip : Ok .tip
  | node (t : T) (h : PL (Ok t) 0) : Ok (.node t)
end

/-- info: Ok.node : ∀ (t : T), PL (Ok t) 0 → Ok t.node -/
#guard_msgs in
#check @Ok.node

-- the copy is nowhere in it: the second motive is over `PL`, and the third and
-- fourth minors are `PL.nil` and `PL.cons`
/--
info: @Ok.rec : ∀ {motive_1 : (a : T) → Ok a → Prop} {motive_2 : (t : T) → PL (Ok t) 0 → Prop},
  motive_1 T.tip Ok.tip →
    (∀ (t : T) (h : PL (Ok t) 0), motive_2 t h → motive_1 t.node (Ok.node t h)) →
      (∀ (t : T), motive_2 t PL.nil) →
        (∀ (t : T) (a : Ok t) (r : PL (Ok t) 0), motive_1 t a → motive_2 t r → motive_2 t (PL.cons a r)) →
          ∀ {a : T} (h : Ok a), motive_1 a h
-/
#guard_msgs in
set_option pp.proofs true in
#check @Ok.rec

-- the data recursor is untouched, and `Ok` is still provable by recursing on it
/-- info: @T.rec : {motive : T → Sort u_1} → motive T.tip → ((t : T) → motive t → motive t.node) → (t : T) → motive t -/
#guard_msgs in
#check @T.rec

theorem all_ok : ∀ t : T, Ok t := by
  intro t
  induction t with
  | tip => exact Ok.tip
  | node t ih => exact Ok.node t (PL.cons ih PL.nil)

/-- info: 'PropThroughCopy.all_ok' does not depend on any axioms -/
#guard_msgs in
#print axioms all_ok

-- and the recursion runs both ways round: rebuilding the proof puts the list
-- back together out of the minors for `PL`
theorem ok_id {t : T} (h : Ok t) : Ok t :=
  Ok.rec (motive_1 := fun t _ => Ok t) (motive_2 := fun t _ => PL (Ok t) 0)
    Ok.tip (fun t _ ih => Ok.node t ih)
    (fun _ => PL.nil) (fun _ _ _ iha ihr => PL.cons iha ihr) h

/-- info: 'PropThroughCopy.ok_id' does not depend on any axioms -/
#guard_msgs in
#print axioms ok_id

end PropThroughCopy

/-! ### A proposition whose index is built from a copy

`Ok.node`'s index is `T.node n v`, and `v` sits at a denested copy, so the index
the raw constructor carries is not the one the written constructor carries.
Proof irrelevance settles the proof itself, but not the index: the index is
data, and the recursor over the whole block looks at it twice over -- once as
the index, and once as whatever the data recursor returned there.

So the equation the bridge travels along is bound inside the motive rather than
applied to it, and every argument standing on the index rides across with it.
-/

namespace PropIndexFromCopy

inductive Wrap (α : Type) (n : Nat) where
  | mk (a : α) : Wrap α n

mutual
inductive T where
  | tip
  | node (n : Nat) (v : List (Wrap T n)) : T
inductive Ok : T → Prop where
  | tip : Ok .tip
  | node (n : Nat) (v : List (Wrap T n)) : Ok (.node n v)
end

/-- info: T.node : (n : Nat) → List (Wrap T n) → T -/
#guard_msgs in
#check @T.node

/-- info: Ok.node : ∀ (n : Nat) (v : List (Wrap T n)), Ok (T.node n v) -/
#guard_msgs in
#check @Ok.node

-- the proposition's own recursor says `Ok (T.node n v)`, not the raw index, and
-- it is the recursion over the whole block seen from the proposition's side:
-- the copies are in it, and the conclusion reads the value `T.rec` returned
/--
info: @Ok.rec : ∀ {motive_1 : T → Sort u_1} {motive_2 : (a : T) → motive_1 a → Ok a → Prop}
  {motive_3 : (n : Nat) → List (Wrap T n) → Sort u_1} {motive_4 : (n : Nat) → Wrap T n → Sort u_1}
  (tip : motive_1 T.tip) (node : (n : Nat) → (v : List (Wrap T n)) → motive_3 n v → motive_1 (T.node n v))
  (tip_1 : motive_2 T.tip tip Ok.tip)
  (node_1 :
    ∀ (n : Nat) (v : List (Wrap T n)) (v_ih : motive_3 n v), motive_2 (T.node n v) (node n v v_ih) (Ok.node n v))
  (nil : (n : Nat) → motive_3 n [])
  (cons :
    (n : Nat) →
      (head : Wrap T n) → (tail : List (Wrap T n)) → motive_4 n head → motive_3 n tail → motive_3 n (head :: tail))
  (mk : (n : Nat) → (a : T) → motive_1 a → motive_4 n (Wrap.mk a)) {a : T} (t : Ok a),
  motive_2 a (T.rec tip node tip_1 node_1 nil cons mk a) t
-/
#guard_msgs in
set_option pp.proofs true in
#check @Ok.rec

-- and so does the one over the whole block, where `motive_2` is stated at the
-- index, at what `motive_1` returned there, and at the proof
/--
info: @T.rec : {motive_1 : T → Sort u_1} →
  {motive_2 : (a : T) → motive_1 a → Ok a → Prop} →
    {motive_3 : (n : Nat) → List (Wrap T n) → Sort u_1} →
      {motive_4 : (n : Nat) → Wrap T n → Sort u_1} →
        (tip : motive_1 T.tip) →
          (node : (n : Nat) → (v : List (Wrap T n)) → motive_3 n v → motive_1 (T.node n v)) →
            motive_2 T.tip tip Ok.tip →
              (∀ (n : Nat) (v : List (Wrap T n)) (v_ih : motive_3 n v),
                  motive_2 (T.node n v) (node n v v_ih) (Ok.node n v)) →
                ((n : Nat) → motive_3 n []) →
                  ((n : Nat) →
                      (head : Wrap T n) →
                        (tail : List (Wrap T n)) → motive_4 n head → motive_3 n tail → motive_3 n (head :: tail)) →
                    ((n : Nat) → (a : T) → motive_1 a → motive_4 n (Wrap.mk a)) → (t : T) → motive_1 t
-/
#guard_msgs in
set_option pp.proofs true in
#check @T.rec

-- proving the proposition by recursion on the data, which is what the grand
-- recursor is for even when only its first motive is wanted
theorem all_ok (t : T) : Ok t :=
  T.rec (motive_1 := fun t => Ok t) (motive_2 := fun _ _ _ => True)
    (motive_3 := fun _ _ => True) (motive_4 := fun _ _ => True)
    Ok.tip (fun n v _ => Ok.node n v)
    trivial (fun _ _ _ => trivial)
    (fun _ => trivial) (fun _ _ _ _ _ => trivial) (fun _ _ _ => trivial) t

/-- info: 'PropIndexFromCopy.all_ok' does not depend on any axioms -/
#guard_msgs in
#print axioms all_ok

-- and taking a proof apart and putting it back, which is what needs the index
-- to arrive at the written constructor.  The data motives are along for the
-- ride here, since nothing about the term is wanted -- but they are what the
-- proposition's minor is allowed to read, and the copies come with them
theorem ok_id {t : T} (h : Ok t) : Ok t :=
  Ok.rec (motive_1 := fun _ => Unit) (motive_2 := fun t _ _ => Ok t)
    (motive_3 := fun _ _ => Unit) (motive_4 := fun _ _ => Unit)
    () (fun _ _ _ => ())
    Ok.tip (fun n v _ => Ok.node n v)
    (fun _ => ()) (fun _ _ _ _ _ => ()) (fun _ _ _ => ()) h

/-- info: 'PropIndexFromCopy.ok_id' does not depend on any axioms -/
#guard_msgs in
#print axioms ok_id

end PropIndexFromCopy

/-! ### A data member whose index is built from a copy

The same index as the section before, carrying a member that is data rather than
a proposition.  Nothing is settled for free here: `U.mk` concludes at `U (T.node
n v)`, and both the constructor in the index and the one the minor built are
renames, so the two have to move together.

They do, because they came from the same place.  A renamed constructor is by
definition the raw one at its fields sent to the original and back, so the raw
conclusion with `v` replaced by that round trip *is* what the written
constructors say -- index, term and all -- and closing the round trip once
closes the whole conclusion.
-/

namespace DataIndexFromCopy

inductive Wrap (α : Type) (n : Nat) where
  | mk (a : α) : Wrap α n

mutual
inductive T where
  | tip
  | node (n : Nat) (v : List (Wrap T n)) : T
inductive U : T → Type where
  | tip : U .tip
  | mk (n : Nat) (v : List (Wrap T n)) : U (.node n v)
end

/-- info: T.node : (n : Nat) → List (Wrap T n) → T -/
#guard_msgs in
#check @T.node

/-- info: U.mk : (n : Nat) → (v : List (Wrap T n)) → U (T.node n v) -/
#guard_msgs in
#check @U.mk

-- the minor for `U.mk` concludes at both written constructors at once
/--
info: @U.rec : {motive_1 : T → Sort u_1} →
  {motive_2 : (a : T) → U a → Sort u_1} →
    {motive_3 : (n : Nat) → List (Wrap T n) → Sort u_1} →
      {motive_4 : (n : Nat) → Wrap T n → Sort u_1} →
        motive_1 T.tip →
          ((n : Nat) → (v : List (Wrap T n)) → motive_3 n v → motive_1 (T.node n v)) →
            motive_2 T.tip U.tip →
              ((n : Nat) → (v : List (Wrap T n)) → motive_3 n v → motive_2 (T.node n v) (U.mk n v)) →
                ((n : Nat) → motive_3 n []) →
                  ((n : Nat) →
                      (head : Wrap T n) →
                        (tail : List (Wrap T n)) → motive_4 n head → motive_3 n tail → motive_3 n (head :: tail)) →
                    ((n : Nat) → (a : T) → motive_1 a → motive_4 n (Wrap.mk a)) → {a : T} → (t : U a) → motive_2 a t
-/
#guard_msgs in
#check @U.rec

/--
info: @T.rec : {motive_1 : T → Sort u_1} →
  {motive_2 : (a : T) → U a → Sort u_1} →
    {motive_3 : (n : Nat) → List (Wrap T n) → Sort u_1} →
      {motive_4 : (n : Nat) → Wrap T n → Sort u_1} →
        motive_1 T.tip →
          ((n : Nat) → (v : List (Wrap T n)) → motive_3 n v → motive_1 (T.node n v)) →
            motive_2 T.tip U.tip →
              ((n : Nat) → (v : List (Wrap T n)) → motive_3 n v → motive_2 (T.node n v) (U.mk n v)) →
                ((n : Nat) → motive_3 n []) →
                  ((n : Nat) →
                      (head : Wrap T n) →
                        (tail : List (Wrap T n)) → motive_4 n head → motive_3 n tail → motive_3 n (head :: tail)) →
                    ((n : Nat) → (a : T) → motive_1 a → motive_4 n (Wrap.mk a)) → (t : T) → motive_1 t
-/
#guard_msgs in
#check @T.rec

-- and both recursors still compute: the bridge is a transport along an equation
-- that is reflexivity on a constructor, so it disappears when one is supplied
def tips {a : T} (u : U a) : Nat :=
  U.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    (motive_3 := fun _ _ => Nat) (motive_4 := fun _ _ => Nat)
    1 (fun _ _ ih => ih)
    0 (fun _ _ ih => ih)
    (fun _ => 0) (fun _ _ _ ih ihs => ih + ihs) (fun _ _ ih => ih) u

example : tips (U.mk 3 [Wrap.mk T.tip, Wrap.mk T.tip]) = 2 := rfl

/-- info: 'DataIndexFromCopy.tips' does not depend on any axioms -/
#guard_msgs in
#print axioms tips

def nodes (t : T) : Nat :=
  T.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    (motive_3 := fun _ _ => Nat) (motive_4 := fun _ _ => Nat)
    1 (fun _ _ ih => ih + 1)
    0 (fun _ _ ih => ih)
    (fun _ => 0) (fun _ _ _ ih ihs => ih + ihs) (fun _ _ ih => ih) t

example : nodes (T.node 3 [Wrap.mk T.tip]) = 2 := rfl

/-- info: 'DataIndexFromCopy.nodes' does not depend on any axioms -/
#guard_msgs in
#print axioms nodes

end DataIndexFromCopy

/-! ### A nesting whose second field is indexed by its first

`MumiTests.Nested` has the nesting whose second field is under a lambda over the
first -- `Sigma`, and anything else whose parameter is a function.  Here the
lambda is the block's own: `DepPair`'s two parameters are `DPCtx` and `DPTy`,
and `DPTy`'s arity is `DPCtx`.  So the copy's constructor has a field at one
member indexed by a field at another, which is the induction-induction of the
block turning up again inside a copy of something else.

Four motives, and the copy's minor is the one that carries it. -/

namespace DepPairNest

inductive DepPair (α : Type) (β : α → Type) where
  | mk (a : α) (b : β a) : DepPair α β

mutual
inductive DPCtx : Type where
  | nil
  | ext (d : List (DepPair DPCtx DPTy)) : DPCtx
inductive DPTy : DPCtx → Type where
  | base (Γ : DPCtx) : DPTy Γ
end

/-- info: DPCtx.ext : List (DepPair DPCtx DPTy) → DPCtx -/
#guard_msgs in
#check @DPCtx.ext

/--
info: @DPCtx.rec : {motive_1 : DPCtx → Sort u_1} →
  {motive_2 : (a : DPCtx) → DPTy a → Sort u_1} →
    {motive_3 : List (DepPair DPCtx DPTy) → Sort u_1} →
      {motive_4 : DepPair DPCtx DPTy → Sort u_1} →
        motive_1 DPCtx.nil →
          ((d : List (DepPair DPCtx DPTy)) → motive_3 d → motive_1 (DPCtx.ext d)) →
            ((Γ : DPCtx) → motive_1 Γ → motive_2 Γ (DPTy.base Γ)) →
              motive_3 [] →
                ((head : DepPair DPCtx DPTy) →
                    (tail : List (DepPair DPCtx DPTy)) → motive_4 head → motive_3 tail → motive_3 (head :: tail)) →
                  ((a : DPCtx) → (b : DPTy a) → motive_1 a → motive_2 a b → motive_4 (DepPair.mk a b)) →
                    (t : DPCtx) → motive_1 t
-/
#guard_msgs(whitespace := lax) in
#check @DPCtx.rec

def DPCtx.size : DPCtx → Nat :=
  DPCtx.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    (motive_3 := fun _ => Nat) (motive_4 := fun _ => Nat)
    1 (fun _ ih => ih + 1) (fun _ ih => ih)
    0 (fun _ _ ih ihs => ih + ihs) (fun _ _ ih _ => ih)

example : DPCtx.size .nil = 1 := rfl
example : DPCtx.size (.ext [⟨.nil, .base .nil⟩]) = 2 := rfl

/-- info: 3 -/
#guard_msgs in
#eval DPCtx.size (.ext [⟨.nil, .base .nil⟩, ⟨.nil, .base .nil⟩])

-- the field is at the copy of `List`, and reading the equation back is that
-- copy's `ofOrig_inj`; nothing here is heterogeneous, `d` being no index
/--
info: DPCtx.ext.injEq : ∀ (d d_1 : List (DepPair DPCtx DPTy)), (DPCtx.ext d = DPCtx.ext d_1) = (d = d_1)
-/
#guard_msgs(whitespace := lax) in
#check @DPCtx.ext.injEq

/-- info: 'DepPairNest.DPCtx.ext.injEq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms DPCtx.ext.injEq

end DepPairNest

/-! ## Section variables

A block written inside a `variable` means the same as one that takes the
variables by hand, and it is spelled the way Lean spells it: the arity takes them
with the binder kinds they were declared with, a constructor takes them
implicitly, and an unused one is left out.  Which are used cannot be settled
before the constructors are read -- `T.base` below names `α` in a field and in no
arity -- so the fold-in happens once the whole block is elaborated.
-/

namespace SectionVars

section
variable (α : Type) [Inhabited α] (unusedβ : Type)
mutual
inductive C : Type where
  | nil  : C
  | snoc : (Γ : C) → T Γ → C
inductive T : C → Type where
  | base : (Γ : C) → α → T Γ
end
end

-- `unusedβ` is nowhere; `[Inhabited α]` came along because `α` did
/-- info: C : (α : Type) → [Inhabited α] → Type -/
#guard_msgs in
#check @C

/-- info: @C.snoc : {α : Type} → [inst : Inhabited α] → (Γ : C α) → T α Γ → C α -/
#guard_msgs in
#check @C.snoc

/--
info: @T.rec : {α : Type} →
  [inst : Inhabited α] →
    {motive_1 : C α → Sort u_1} →
      {motive_2 : (a : C α) → T α a → Sort u_1} →
        motive_1 C.nil →
          ((Γ : C α) → (a : T α Γ) → motive_1 Γ → motive_2 Γ a → motive_1 (Γ.snoc a)) →
            ((Γ : C α) → (a : α) → motive_1 Γ → motive_2 Γ (T.base Γ a)) → {a : C α} → (t : T α a) → motive_2 a t
-/
#guard_msgs in
#check @T.rec

def csize {α : Type} [Inhabited α] : C α → Nat :=
  C.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    0 (fun _ _ n m => n + m + 1) (fun _ _ _ => 1)

example (α : Type) [Inhabited α] : csize (α := α) C.nil = 0 := rfl
example (α : Type) [Inhabited α] (Γ : C α) (x : α) :
    csize (C.snoc Γ (T.base Γ x)) = csize Γ + 1 + 1 := rfl

/-- info: 4 -/
#guard_msgs in
#eval csize (C.snoc (C.snoc C.nil (T.base C.nil 1)) (T.base _ (2 : Nat)))

/-- info: 'SectionVars.csize' does not depend on any axioms -/
#guard_msgs in
#print axioms csize

-- a variable the block does not use is left out even when a variable it does
-- use is declared before it
section
variable (α : Type) (a₀ : α)
mutual
inductive C3 : Type where
  | nil  : C3
  | snoc : (Γ : C3) → T3 Γ → C3
inductive T3 : C3 → Type where
  | at : (Γ : C3) → (x : α) → T3 Γ
end
end

/-- info: C3 : Type → Type -/
#guard_msgs in
#check @C3

-- and they compose with a nesting at a member
section
variable (α : Type)
mutual
inductive C4 : Type where
  | nil  : C4
  | snoc : (Γ : C4) → T4 Γ → C4
inductive T4 : C4 → Type where
  | base : (Γ : C4) → α → T4 Γ
  | tup  : (Γ : C4) → List (T4 Γ) → T4 Γ
end
end

/-- info: @T4.tup : {α : Type} → (Γ : C4 α) → List (T4 α Γ) → T4 α Γ -/
#guard_msgs in
#check @T4.tup

end SectionVars

/-! ## `deriving` on one of these

A data member is a `def` here -- the subtype of its pre-type -- so a handler
that wants constructors has nothing to look at, and the class has to arrive by
`Subtype`.  So the pre-type is derived for first, quietly, and the member is
then delta derived onto it. -/

mutual
inductive DVec : Type where
  | nil : DVec
  | cons : (v : DVec) → DOk v → DVec
  deriving DecidableEq, Repr
inductive DOk : DVec → Prop where
  | nil : DOk .nil
end

/-- info: true -/
#guard_msgs in
#eval decide (DVec.nil = DVec.nil)

/-- info: false -/
#guard_msgs in
#eval decide (DVec.nil = DVec.cons DVec.nil DOk.nil)

/-! What `Repr` is handed is the pre-term, so that is what it prints: the
proof field is gone and the constructors are the pre-type's. -/

/-- info: DVec._pre.cons (DVec._pre.nil) -/
#guard_msgs in
#eval repr (DVec.cons DVec.nil DOk.nil)

/-! Two members may ask for the same class; they are derived for together where
that works and one at a time where it does not, since the data pre-types and
the `Prop` pre-types are two separate blocks. -/

mutual
inductive EVec : Type where
  | nil : EVec
  | cons : (v : EVec) → EOk v → EVec
  deriving DecidableEq
inductive EOk : EVec → Prop where
  | nil : EOk .nil
  deriving DecidableEq
end

/-- info: true -/
#guard_msgs in
#eval decide (EVec.nil = EVec.nil)

/-! `Inhabited` is not a class the subtype lifts, so the delta route cannot
reach it -- and does not have to.  A member's visible constructors are ordinary
functions into it, so the instance is written from whichever of them can be
applied, which is the instance the writer would have written by hand. -/

mutual
inductive FVec : Type where
  | nil : FVec
  | cons : (v : FVec) → FOk v → FVec
  deriving Inhabited
inductive FOk : FVec → Prop where
  | nil : FOk .nil
end

/-- info: FVec.cons : (v : FVec) → FOk v → FVec -/
#guard_msgs in
#check @FVec.cons

/-- info: FOk.nil : FOk FVec.nil -/
#guard_msgs in
#check @FOk.nil

/-- info: FVec.instInhabited : Inhabited FVec -/
#guard_msgs in
#check @FVec.instInhabited

example : (default : FVec) = FVec.nil := rfl

/-! A field is filled with whatever `Inhabited` says its own type is, so a
constructor with fields serves as well as a nullary one, and a parameter that is
a type gets a hypothesis apiece -- the same instance Lean's own handler states
for an ordinary inductive. -/

mutual
inductive F2Vec (β : Type) : Type where
  | tip (b : β) (n : Nat) : F2Vec β
  | cons (v : F2Vec β) (h : F2Ok v) : F2Vec β
  deriving Inhabited
inductive F2Ok {β : Type} : F2Vec β → Prop where
  | tip (b : β) (n : Nat) : F2Ok (.tip b n)
end

/-- info: @F2Vec.instInhabited : {β : Type} → [inst : Inhabited β] → Inhabited (F2Vec β) -/
#guard_msgs in
#check @F2Vec.instInhabited

/-! A member no constructor can fill gets nothing, and the delta route it falls
through to says why.  The block is in the environment by then, so the complaint
costs the writer the instance and not the type -- and the type may in any case
be the empty one they wrote. -/

/--
error: failed to synthesize instance of type class
  Inhabited (Subtype F3Vec._wf)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
---
error: Failed to delta derive `Inhabited` instance for `F3Vec`.

Note: Delta deriving tries the following strategies: (1) inserting the definition into each explicit non-out-param parameter of a class and (2) unfolding definitions further.

Note: A data member of an induction-inductive block is the subtype of its pre-type, so `deriving` reaches it only through an instance `Subtype` already has -- `DecidableEq` and `Repr` do, and a class that does not has to be instanced by hand
-/
#guard_msgs in
mutual
inductive F3Vec : Type where
  | cons : (v : F3Vec) → F3Ok v → F3Vec
  deriving Inhabited
inductive F3Ok : F3Vec → Prop where
  | cons : (v : F3Vec) → (h : F3Ok v) → F3Ok (.cons v h)
end

/-- info: F3Vec.cons : (v : F3Vec) → F3Ok v → F3Vec -/
#guard_msgs in
#check @F3Vec.cons

/-! A block that is only induction-inductive once it has been denested takes
`deriving` the same way.  The copy denesting added is a member like any other,
so it has a pre-type of its own, and the class reaches it along with the rest
of the pre-block. -/

inductive GWrap (α : Type) : Type where
  | mk : α → GWrap α

mutual
inductive GVec : Type where
  | nil : GVec
  | cons : (v : GWrap GVec) → GOk v → GVec
  deriving DecidableEq, Repr
inductive GOk : GWrap GVec → Prop where
  | nil : GOk (.mk .nil)
end

/-- info: GVec.cons : (v : GWrap GVec) → GOk v → GVec -/
#guard_msgs in
#check @GVec.cons

/-! The proposition is indexed by the nesting, so it too is emitted over the copy
and restated afterwards -- `GOk` under the plain name is the hidden one at the
copy-world image of its index, and the constructor typechecks against that
because the image of a written constructor reduces to the copy's. -/

/-- info: GOk : GWrap GVec → Prop -/
#guard_msgs in
#check @GOk

/-- info: GOk.nil : GOk (GWrap.mk GVec.nil) -/
#guard_msgs in
#check @GOk.nil

/--
info: @GVec.rec : {motive_1 : GVec → Sort u_1} →
  {motive_2 : GWrap GVec → Sort u_1} →
    motive_1 GVec.nil →
      ((v : GWrap GVec) → (a : GOk v) → motive_2 v → motive_1 (GVec.cons v a)) →
        ((a : GVec) → motive_1 a → motive_2 (GWrap.mk a)) → (t : GVec) → motive_1 t
-/
#guard_msgs in
#check @GVec.rec

/-- info: true -/
#guard_msgs in
#eval decide (GVec.nil = GVec.nil)

/-- info: false -/
#guard_msgs in
#eval decide (GVec.nil = GVec.cons (.mk .nil) .nil)

/-- info: GVec._pre.cons (GVec.nested_GWrap_1._pre.mk (GVec._pre.nil)) -/
#guard_msgs in
#eval repr (GVec.cons (.mk .nil) .nil)

/-! The nesting `GWrap` was is not recursive, so its copy is only one layer deep.
`List` is the other case: the copy recurses, the proposition indexed by it
recurses along with it, and its constructor's index is built out of the copy's
own constructor rather than being pinned to a closed term.  Everything the writer
named still comes out over `List LTree`. -/

mutual
inductive LTree : Type where
  | node : (cs : List LTree) → LOk cs → LTree
inductive LOk : List LTree → Prop where
  | nil : LOk []
  | cons : (t : LTree) → (ts : List LTree) → LOk ts → LOk (t :: ts)
end

/-- info: LTree.node : (cs : List LTree) → LOk cs → LTree -/
#guard_msgs in
#check @LTree.node

/-- info: LOk : List LTree → Prop -/
#guard_msgs in
#check @LOk

/-- info: LOk.cons : ∀ (t : LTree) (ts : List LTree), LOk ts → LOk (t :: ts) -/
#guard_msgs in
#check @LOk.cons

/-! The recursion over the whole block goes across as well, and it is the whole
block: the proposition gets a motive of its own, and that motive is stated over
the value the recursion returned at the index it is about -- `motive_3 : (a :
List LTree) → motive_2 a → LOk a → Prop`.  Its second minor is the shape all of
this was for, the proof of `LOk (t :: ts)` coming with the value the `cons` minor
built out of the two below it. -/

/--
info: @LTree.rec : {motive_1 : LTree → Sort u_1} →
  {motive_2 : List LTree → Sort u_1} →
    {motive_3 : (a : List LTree) → motive_2 a → LOk a → Prop} →
      ((cs : List LTree) → (a : LOk cs) → (cs_ih : motive_2 cs) → motive_3 cs cs_ih a → motive_1 (LTree.node cs a)) →
        (nil : motive_2 []) →
          (cons : (head : LTree) → (tail : List LTree) → motive_1 head → motive_2 tail → motive_2 (head :: tail)) →
            motive_3 [] nil LOk.nil →
              (∀ (t : LTree) (ts : List LTree) (a : LOk ts) (t_ih : motive_1 t) (ts_ih : motive_2 ts),
                  motive_3 ts ts_ih a → motive_3 (t :: ts) (cons t ts t_ih ts_ih) ⋯) →
                (t : LTree) → motive_1 t
-/
#guard_msgs in
#check @LTree.rec

/-! The proposition's own recursor is stated over the originals too.  It is the
raw one at the copy-world images of the indices, and what that gives back is the
motive at the images read out again, so the value is carried onto the writer's
indices by the round trip the other way. -/

/--
info: @LOk.rec : ∀ {motive : (a : List LTree) → LOk a → Prop},
  motive [] LOk.nil →
    (∀ (t : LTree) (ts : List LTree) (a : LOk ts), motive ts a → motive (t :: ts) ⋯) →
      ∀ {a : List LTree} (h : LOk a), motive a h
-/
#guard_msgs in
#check @LOk.rec

/-- The recursion over the block computes, one layer of the nesting at a time.
Nothing here needs the proposition, so its motive is `True`. -/
def LTree.size (t : LTree) : Nat :=
  LTree.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat)
    (motive_3 := fun _ _ _ => True)
    (fun _ _ n _ => n + 1) 0 (fun _ _ a b => a + b) trivial (fun _ _ _ _ _ _ => trivial) t

example : (LTree.node [] LOk.nil).size = 1 := rfl
example : (LTree.node [LTree.node [] LOk.nil] (LOk.cons _ _ LOk.nil)).size = 2 := rfl

/-- And so does the proposition's, on both of its constructors. -/
example {p : (l : List LTree) → LOk l → Prop} (hn : p [] LOk.nil)
    (hc : (t : LTree) → (ts : List LTree) → (h : LOk ts) → p ts h → p (t :: ts) (LOk.cons t ts h)) :
    LOk.rec (motive := p) hn hc LOk.nil = hn := rfl

example {p : (l : List LTree) → LOk l → Prop} (hn : p [] LOk.nil)
    (hc : (t : LTree) → (ts : List LTree) → (h : LOk ts) → p ts h → p (t :: ts) (LOk.cons t ts h))
    (t : LTree) (ts : List LTree) (h : LOk ts) :
    LOk.rec (motive := p) hn hc (LOk.cons t ts h) = hc t ts h (LOk.rec (motive := p) hn hc h) := rfl

/-! ## A proposition over a nesting, in the shapes a writer would have

`LTree` is the smallest block of this kind there is.  What follows are six that
are not: a parameter and a universe parameter, two propositions over the one
nesting, a nesting inside a nesting, the classic `Ctx`/`Ty` pair with a
proposition alongside, an indexed data member, and members in two universes.
Each is pinned at the places the denesting could show through -- the constructor
the writer wrote, the proposition's arity, and both recursors -- and the ones
with something to compute are asked to. -/

namespace ParamNested

/-! A parameter and a universe parameter go through untouched.  The copy takes
them as parameters of its own, and the proposition's arity comes back reading
`List (PTree α)` at the parameter the writer gave it rather than at whatever the
copy was made to take. -/

mutual
inductive PTree (α : Type u) : Type u where
  | node : (cs : List (PTree α)) → POk α cs → PTree α
inductive POk (α : Type u) : List (PTree α) → Prop where
  | nil  : POk α []
  | cons : (t : PTree α) → (ts : List (PTree α)) → POk α ts → POk α (t :: ts)
end

/-- info: @PTree.node : {α : Type u_1} → (cs : List (PTree α)) → POk α cs → PTree α -/
#guard_msgs in
#check @PTree.node

/-- info: POk : (α : Type u_1) → List (PTree α) → Prop -/
#guard_msgs in
#check @POk

/--
info: @POk.cons : ∀ {α : Type u_1} (t : PTree α) (ts : List (PTree α)), POk α ts → POk α (t :: ts)
-/
#guard_msgs in
#check @POk.cons

/--
info: @PTree.rec : {α : Type u_2} →
  {motive_1 : PTree α → Sort u_1} →
    {motive_2 : List (PTree α) → Sort u_1} →
      {motive_3 : (a : List (PTree α)) → motive_2 a → POk α a → Prop} →
        ((cs : List (PTree α)) →
            (a : POk α cs) → (cs_ih : motive_2 cs) → motive_3 cs cs_ih a → motive_1 (PTree.node cs a)) →
          (nil : motive_2 []) →
            (cons :
                (head : PTree α) → (tail : List (PTree α)) → motive_1 head → motive_2 tail → motive_2 (head :: tail)) →
              motive_3 [] nil ⋯ →
                (∀ (t : PTree α) (ts : List (PTree α)) (a : POk α ts) (t_ih : motive_1 t) (ts_ih : motive_2 ts),
                    motive_3 ts ts_ih a → motive_3 (t :: ts) (cons t ts t_ih ts_ih) ⋯) →
                  (t : PTree α) → motive_1 t
-/
#guard_msgs in
#check @PTree.rec

/--
info: @POk.rec : ∀ {α : Type u_1} {motive : (a : List (PTree α)) → POk α a → Prop},
  motive [] ⋯ →
    (∀ (t : PTree α) (ts : List (PTree α)) (a : POk α ts), motive ts a → motive (t :: ts) ⋯) →
      ∀ {a : List (PTree α)} (h : POk α a), motive a h
-/
#guard_msgs in
#check @POk.rec

/-- The recursion computes at the parameters too, one layer of the nesting at a
time.  Nothing here needs the proposition, so its motive is `True`. -/
def PTree.size {α : Type u} (t : PTree α) : Nat :=
  PTree.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat) (motive_3 := fun _ _ _ => True)
    (fun _ _ n _ => n + 1) 0 (fun _ _ a b => a + b) trivial (fun _ _ _ _ _ _ => trivial) t

example : (PTree.node (α := Nat) [] POk.nil).size = 1 := rfl

example : (PTree.node (α := Nat) [PTree.node [] POk.nil] (POk.cons _ _ POk.nil)).size = 2 := rfl

end ParamNested

namespace TwoOverOne

/-! Two propositions over the same nesting.  Each gets a motive of its own in the
recursion over the whole block, and both are stated over the one value the copy's
recursion returned -- there is only one nesting, so there is only one such value
to be stated over.  Their own recursors come out as the pair they are: either
name asks for both motives and both sets of minors, and hands back the one it is
named for. -/

mutual
inductive QTree : Type where
  | node : (cs : List QTree) → QA cs → QB cs → QTree
inductive QA : List QTree → Prop where
  | nil  : QA []
  | cons : (t : QTree) → (ts : List QTree) → QA ts → QA (t :: ts)
inductive QB : List QTree → Prop where
  | any : (cs : List QTree) → QB cs
end

/-- info: QTree.node : (cs : List QTree) → QA cs → QB cs → QTree -/
#guard_msgs in
#check @QTree.node

/-- info: QA : List QTree → Prop -/
#guard_msgs in
#check @QA

/-- info: QB : List QTree → Prop -/
#guard_msgs in
#check @QB

/--
info: @QTree.rec : {motive_1 : QTree → Sort u_1} →
  {motive_2 : List QTree → Sort u_1} →
    {motive_3 : (a : List QTree) → motive_2 a → QA a → Prop} →
      {motive_4 : (a : List QTree) → motive_2 a → QB a → Prop} →
        ((cs : List QTree) →
            (a : QA cs) →
              (a_1 : QB cs) →
                (cs_ih : motive_2 cs) → motive_3 cs cs_ih a → motive_4 cs cs_ih a_1 → motive_1 (QTree.node cs a a_1)) →
          (nil : motive_2 []) →
            (cons : (head : QTree) → (tail : List QTree) → motive_1 head → motive_2 tail → motive_2 (head :: tail)) →
              motive_3 [] nil QA.nil →
                (∀ (t : QTree) (ts : List QTree) (a : QA ts) (t_ih : motive_1 t) (ts_ih : motive_2 ts),
                    motive_3 ts ts_ih a → motive_3 (t :: ts) (cons t ts t_ih ts_ih) ⋯) →
                  (∀ (cs : List QTree) (cs_ih : motive_2 cs), motive_4 cs cs_ih ⋯) → (t : QTree) → motive_1 t
-/
#guard_msgs in
#check @QTree.rec

/--
info: @QA.rec : ∀ {motive_1 : (a : List QTree) → QA a → Prop} {motive_2 : (a : List QTree) → QB a → Prop},
  motive_1 [] QA.nil →
    (∀ (t : QTree) (ts : List QTree) (a : QA ts), motive_1 ts a → motive_1 (t :: ts) ⋯) →
      (∀ (cs : List QTree), motive_2 cs ⋯) → ∀ {a : List QTree} (h : QA a), motive_1 a h
-/
#guard_msgs in
#check @QA.rec

/--
info: @QB.rec : ∀ {motive_1 : (a : List QTree) → QA a → Prop} {motive_2 : (a : List QTree) → QB a → Prop},
  motive_1 [] QA.nil →
    (∀ (t : QTree) (ts : List QTree) (a : QA ts), motive_1 ts a → motive_1 (t :: ts) ⋯) →
      (∀ (cs : List QTree), motive_2 cs ⋯) → ∀ {a : List QTree} (h : QB a), motive_2 a h
-/
#guard_msgs in
#check @QB.rec

end TwoOverOne

namespace NestedNested

/-! A nesting inside a nesting.  Denesting makes a copy per layer, so the block
grows two members rather than one, and the recursion gets a motive and a pair of
minors for each -- `motive_2` at `List (List ATree)` and `motive_3` at
`List ATree`.  The proposition is indexed by the outer one. -/

mutual
inductive ATree : Type where
  | node : (cs : List (List ATree)) → AOk cs → ATree
inductive AOk : List (List ATree) → Prop where
  | nil  : AOk []
  | cons : (t : List ATree) → (ts : List (List ATree)) → AOk ts → AOk (t :: ts)
end

/-- info: ATree.node : (cs : List (List ATree)) → AOk cs → ATree -/
#guard_msgs in
#check @ATree.node

/-- info: AOk : List (List ATree) → Prop -/
#guard_msgs in
#check @AOk

/-- info: AOk.cons : ∀ (t : List ATree) (ts : List (List ATree)), AOk ts → AOk (t :: ts) -/
#guard_msgs in
#check @AOk.cons

/--
info: @ATree.rec : {motive_1 : ATree → Sort u_1} →
  {motive_2 : List (List ATree) → Sort u_1} →
    {motive_3 : List ATree → Sort u_1} →
      {motive_4 : (a : List (List ATree)) → motive_2 a → AOk a → Prop} →
        ((cs : List (List ATree)) →
            (a : AOk cs) → (cs_ih : motive_2 cs) → motive_4 cs cs_ih a → motive_1 (ATree.node cs a)) →
          (nil : motive_2 []) →
            (cons :
                (head : List ATree) →
                  (tail : List (List ATree)) → motive_3 head → motive_2 tail → motive_2 (head :: tail)) →
              motive_3 [] →
                ((head : ATree) → (tail : List ATree) → motive_1 head → motive_3 tail → motive_3 (head :: tail)) →
                  motive_4 [] nil AOk.nil →
                    (∀ (t : List ATree) (ts : List (List ATree)) (a : AOk ts) (t_ih : motive_3 t) (ts_ih : motive_2 ts),
                        motive_4 ts ts_ih a → motive_4 (t :: ts) (cons t ts t_ih ts_ih) ⋯) →
                      (t : ATree) → motive_1 t
-/
#guard_msgs in
#check @ATree.rec

/--
info: @AOk.rec : ∀ {motive : (a : List (List ATree)) → AOk a → Prop},
  motive [] AOk.nil →
    (∀ (t : List ATree) (ts : List (List ATree)) (a : AOk ts), motive ts a → motive (t :: ts) ⋯) →
      ∀ {a : List (List ATree)} (h : AOk a), motive a h
-/
#guard_msgs in
#check @AOk.rec

/-- Both layers compute. -/
def ATree.size (t : ATree) : Nat :=
  ATree.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat) (motive_3 := fun _ => Nat)
    (motive_4 := fun _ _ _ => True)
    (fun _ _ n _ => n + 1) 0 (fun _ _ a b => a + b) 0 (fun _ _ a b => a + b)
    trivial (fun _ _ _ _ _ _ => trivial) t

example : (ATree.node [] AOk.nil).size = 1 := rfl

example : (ATree.node [[ATree.node [] AOk.nil]] (AOk.cons _ _ AOk.nil)).size = 2 := rfl

end NestedNested

namespace CtxTyNested

/-! The block this elaborator was written for, with a proposition over a nesting
put beside it.  `DTy` is indexed by `DCtx`, which is the rule the erasure lifts;
`DOk` is indexed by `List DCtx`, which is the rule lowering lifts.  Both at once
is the case worth having, and the two data members each get the recursion over
the whole block. -/

mutual
inductive DCtx : Type where
  | nil  : DCtx
  | snoc : (Γ : DCtx) → DTy Γ → DCtx
inductive DTy : DCtx → Type where
  | base : (Γ : DCtx) → DTy Γ
  | pack : (Γ : DCtx) → (ts : List DCtx) → DOk ts → DTy Γ
inductive DOk : List DCtx → Prop where
  | nil  : DOk []
  | cons : (Γ : DCtx) → (Γs : List DCtx) → DOk Γs → DOk (Γ :: Γs)
end

/-- info: DTy.pack : (Γ : DCtx) → (ts : List DCtx) → DOk ts → DTy Γ -/
#guard_msgs in
#check @DTy.pack

/-- info: DOk : List DCtx → Prop -/
#guard_msgs in
#check @DOk

/--
info: @DCtx.rec : {motive_1 : DCtx → Sort u_1} →
  {motive_2 : (a : DCtx) → DTy a → Sort u_1} →
    {motive_3 : List DCtx → Sort u_1} →
      {motive_4 : (a : List DCtx) → motive_3 a → DOk a → Prop} →
        motive_1 DCtx.nil →
          ((Γ : DCtx) → (a : DTy Γ) → motive_1 Γ → motive_2 Γ a → motive_1 (Γ.snoc a)) →
            ((Γ : DCtx) → motive_1 Γ → motive_2 Γ (DTy.base Γ)) →
              ((Γ : DCtx) →
                  (ts : List DCtx) →
                    (a : DOk ts) →
                      motive_1 Γ → (ts_ih : motive_3 ts) → motive_4 ts ts_ih a → motive_2 Γ (DTy.pack Γ ts a)) →
                (nil_1 : motive_3 []) →
                  (cons :
                      (head : DCtx) → (tail : List DCtx) → motive_1 head → motive_3 tail → motive_3 (head :: tail)) →
                    motive_4 [] nil_1 DOk.nil →
                      (∀ (Γ : DCtx) (Γs : List DCtx) (a : DOk Γs) (Γ_ih : motive_1 Γ) (Γs_ih : motive_3 Γs),
                          motive_4 Γs Γs_ih a → motive_4 (Γ :: Γs) (cons Γ Γs Γ_ih Γs_ih) ⋯) →
                        (t : DCtx) → motive_1 t
-/
#guard_msgs in
#check @DCtx.rec

/--
info: @DTy.rec : {motive_1 : DCtx → Sort u_1} →
  {motive_2 : (a : DCtx) → DTy a → Sort u_1} →
    {motive_3 : List DCtx → Sort u_1} →
      {motive_4 : (a : List DCtx) → motive_3 a → DOk a → Prop} →
        motive_1 DCtx.nil →
          ((Γ : DCtx) → (a : DTy Γ) → motive_1 Γ → motive_2 Γ a → motive_1 (Γ.snoc a)) →
            ((Γ : DCtx) → motive_1 Γ → motive_2 Γ (DTy.base Γ)) →
              ((Γ : DCtx) →
                  (ts : List DCtx) →
                    (a : DOk ts) →
                      motive_1 Γ → (ts_ih : motive_3 ts) → motive_4 ts ts_ih a → motive_2 Γ (DTy.pack Γ ts a)) →
                (nil_1 : motive_3 []) →
                  (cons :
                      (head : DCtx) → (tail : List DCtx) → motive_1 head → motive_3 tail → motive_3 (head :: tail)) →
                    motive_4 [] nil_1 DOk.nil →
                      (∀ (Γ : DCtx) (Γs : List DCtx) (a : DOk Γs) (Γ_ih : motive_1 Γ) (Γs_ih : motive_3 Γs),
                          motive_4 Γs Γs_ih a → motive_4 (Γ :: Γs) (cons Γ Γs Γ_ih Γs_ih) ⋯) →
                        {a : DCtx} → (t : DTy a) → motive_2 a t
-/
#guard_msgs in
#check @DTy.rec

/--
info: @DOk.rec : ∀ {motive : (a : List DCtx) → DOk a → Prop},
  motive [] DOk.nil →
    (∀ (Γ : DCtx) (Γs : List DCtx) (a : DOk Γs), motive Γs a → motive (Γ :: Γs) ⋯) →
      ∀ {a : List DCtx} (h : DOk a), motive a h
-/
#guard_msgs in
#check @DOk.rec

/-- A recursion that runs through all three members at once. -/
def DCtx.len (Γ : DCtx) : Nat :=
  DCtx.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat) (motive_3 := fun _ => Nat)
    (motive_4 := fun _ _ _ => True)
    0 (fun _ _ n _ => n + 1) (fun _ n => n) (fun _ _ _ n m _ => n + m) 0 (fun _ _ a b => a + b)
    trivial (fun _ _ _ _ _ _ => trivial) Γ

example : DCtx.nil.len = 0 := rfl

example : (DCtx.snoc .nil (.base .nil)).len = 1 := rfl

/-- And the proposition's own iota rule holds where the recursion runs into
itself, which is the constructor built out of the copy's own. -/
example {p : (l : List DCtx) → DOk l → Prop} (hn : p [] DOk.nil)
    (hc : ∀ Γ Γs h, p Γs h → p (Γ :: Γs) (DOk.cons Γ Γs h)) (Γ : DCtx) (Γs : List DCtx)
    (h : DOk Γs) :
    DOk.rec (motive := p) hn hc (DOk.cons Γ Γs h) = hc Γ Γs h (DOk.rec (motive := p) hn hc h) :=
  rfl

end CtxTyNested

namespace IndexedNested

/-! An indexed data member, with the proposition over a nesting of it at a fixed
index.  The copy is indexed by that index as well -- `List (EVec n)` is a family
in `n` -- so the recursion carries it through both the copy's motive and the
proposition's. -/

mutual
inductive EVec : Nat → Type where
  | nil  : EVec 0
  | cons : (n : Nat) → (cs : List (EVec n)) → EOk n cs → EVec (n + 1)
inductive EOk : (n : Nat) → List (EVec n) → Prop where
  | nil  : (n : Nat) → EOk n []
  | cons : (n : Nat) → (t : EVec n) → (ts : List (EVec n)) → EOk n ts → EOk n (t :: ts)
end

/-- info: EVec.cons : (n : Nat) → (cs : List (EVec n)) → EOk n cs → EVec (n + 1) -/
#guard_msgs in
#check @EVec.cons

/-- info: EOk : (n : Nat) → List (EVec n) → Prop -/
#guard_msgs in
#check @EOk

/-- info: EOk.cons : ∀ (n : Nat) (t : EVec n) (ts : List (EVec n)), EOk n ts → EOk n (t :: ts) -/
#guard_msgs in
#check @EOk.cons

/--
info: @EVec.rec : {motive_1 : (a : Nat) → EVec a → Sort u_1} →
  {motive_2 : (n : Nat) → List (EVec n) → Sort u_1} →
    {motive_3 : (n : Nat) → (a : List (EVec n)) → motive_2 n a → EOk n a → Prop} →
      motive_1 0 EVec.nil →
        ((n : Nat) →
            (cs : List (EVec n)) →
              (a : EOk n cs) → (cs_ih : motive_2 n cs) → motive_3 n cs cs_ih a → motive_1 (n + 1) (EVec.cons n cs a)) →
          (nil_1 : (n : Nat) → motive_2 n []) →
            (cons_1 :
                (n : Nat) →
                  (head : EVec n) →
                    (tail : List (EVec n)) → motive_1 n head → motive_2 n tail → motive_2 n (head :: tail)) →
              (∀ (n : Nat), motive_3 n [] (nil_1 n) ⋯) →
                (∀ (n : Nat) (t : EVec n) (ts : List (EVec n)) (a : EOk n ts) (t_ih : motive_1 n t)
                    (ts_ih : motive_2 n ts),
                    motive_3 n ts ts_ih a → motive_3 n (t :: ts) (cons_1 n t ts t_ih ts_ih) ⋯) →
                  {a : Nat} → (t : EVec a) → motive_1 a t
-/
#guard_msgs in
#check @EVec.rec

/--
info: @EOk.rec : ∀ {motive : (n : Nat) → (a : List (EVec n)) → EOk n a → Prop},
  (∀ (n : Nat), motive n [] ⋯) →
    (∀ (n : Nat) (t : EVec n) (ts : List (EVec n)) (a : EOk n ts), motive n ts a → motive n (t :: ts) ⋯) →
      ∀ {n : Nat} {a : List (EVec n)} (h : EOk n a), motive n a h
-/
#guard_msgs in
#check @EOk.rec

example {p : (n : Nat) → (a : List (EVec n)) → EOk n a → Prop} (hn : ∀ n, p n [] (EOk.nil n))
    (hc : ∀ n t ts h, p n ts h → p n (t :: ts) (EOk.cons n t ts h)) (n : Nat) :
    EOk.rec (motive := p) hn hc (EOk.nil n) = hn n := rfl

example {p : (n : Nat) → (a : List (EVec n)) → EOk n a → Prop} (hn : ∀ n, p n [] (EOk.nil n))
    (hc : ∀ n t ts h, p n ts h → p n (t :: ts) (EOk.cons n t ts h))
    (n : Nat) (t : EVec n) (ts : List (EVec n)) (h : EOk n ts) :
    EOk.rec (motive := p) hn hc (EOk.cons n t ts h)
      = hc n t ts h (EOk.rec (motive := p) hn hc h) := rfl

end IndexedNested

namespace HeteroNested

/-! Members in two universes, which is the rule lowering lifts, on top of the
nesting and the proposition.  `FBig` holds a `Type` and so lives in `Type 1`;
`FOk` is a proposition; the copy follows `FBig`. -/

mutual
inductive FBig : Type 1 where
  | ty   : Type → FBig
  | node : (cs : List FBig) → FOk cs → FBig
inductive FOk : List FBig → Prop where
  | nil  : FOk []
  | cons : (t : FBig) → (ts : List FBig) → FOk ts → FOk (t :: ts)
end

/-- info: FBig.node : (cs : List FBig) → FOk cs → FBig -/
#guard_msgs in
#check @FBig.node

/-- info: FOk : List FBig → Prop -/
#guard_msgs in
#check @FOk

/--
info: @FBig.rec : {motive_1 : FBig → Sort u_1} →
  {motive_2 : List FBig → Sort u_1} →
    {motive_3 : (a : List FBig) → motive_2 a → FOk a → Prop} →
      ((a : Type) → motive_1 (FBig.ty a)) →
        ((cs : List FBig) → (a : FOk cs) → (cs_ih : motive_2 cs) → motive_3 cs cs_ih a → motive_1 (FBig.node cs a)) →
          (nil : motive_2 []) →
            (cons : (head : FBig) → (tail : List FBig) → motive_1 head → motive_2 tail → motive_2 (head :: tail)) →
              motive_3 [] nil FOk.nil →
                (∀ (t : FBig) (ts : List FBig) (a : FOk ts) (t_ih : motive_1 t) (ts_ih : motive_2 ts),
                    motive_3 ts ts_ih a → motive_3 (t :: ts) (cons t ts t_ih ts_ih) ⋯) →
                  (t : FBig) → motive_1 t
-/
#guard_msgs in
#check @FBig.rec

/--
info: @FOk.rec : ∀ {motive : (a : List FBig) → FOk a → Prop},
  motive [] FOk.nil →
    (∀ (t : FBig) (ts : List FBig) (a : FOk ts), motive ts a → motive (t :: ts) ⋯) →
      ∀ {a : List FBig} (h : FOk a), motive a h
-/
#guard_msgs in
#check @FOk.rec

end HeteroNested

/-! ### Indexed by a member rather than by the nesting

Every proposition above is indexed by the nesting, and its own recursor is the
split one: the recursion at `List LTree` is neither `LTree.rec` nor `List.rec`
but the recursion over the denesting, and the writer has no name for it, so
there is nothing over the originals for the motive to be stated over.  The
proposition keeps the recursor that does not ask for one, and the recursion over
the whole block -- which does have a name for every motive it takes -- carries
the other reading.

Index the proposition by a member instead, in a block that still has a nesting
in it, and the name is there: `NTm.rec`.  Then the proposition's own recursor is
the one over the whole block, concluding at the motive taken at the value the
data recursion returned, which is the shape a block with no denesting in it has
always had. -/

namespace ByMember

mutual
inductive NTm : Type where
  | app : (ts : List NTm) → NTm
  | var : NTm
inductive NOk : NTm → Prop where
  | var : NOk .var
  | app : (ts : List NTm) → NOk (.app ts)
end

/-- info: NTm.app : List NTm → NTm -/
#guard_msgs in
#check @NTm.app

/-- info: NOk : NTm → Prop -/
#guard_msgs in
#check @NOk

/--
info: @NTm.rec : {motive_1 : NTm → Sort u_1} →
  {motive_2 : (a : NTm) → motive_1 a → NOk a → Prop} →
    {motive_3 : List NTm → Sort u_1} →
      (app : (ts : List NTm) → motive_3 ts → motive_1 (NTm.app ts)) →
        (var : motive_1 NTm.var) →
          motive_2 NTm.var var NOk.var →
            (∀ (ts : List NTm) (ts_ih : motive_3 ts), motive_2 (NTm.app ts) (app ts ts_ih) ⋯) →
              motive_3 [] →
                ((head : NTm) → (tail : List NTm) → motive_1 head → motive_3 tail → motive_3 (head :: tail)) →
                  (t : NTm) → motive_1 t
-/
#guard_msgs in
#check @NTm.rec

/--
info: @NOk.rec : ∀ {motive_1 : NTm → Sort u_1} {motive_2 : (a : NTm) → motive_1 a → NOk a → Prop}
  {motive_3 : List NTm → Sort u_1} (app : (ts : List NTm) → motive_3 ts → motive_1 (NTm.app ts))
  (var : motive_1 NTm.var) (var_1 : motive_2 NTm.var var NOk.var)
  (app_1 : ∀ (ts : List NTm) (ts_ih : motive_3 ts), motive_2 (NTm.app ts) (app ts ts_ih) ⋯) (nil : motive_3 [])
  (cons : (head : NTm) → (tail : List NTm) → motive_1 head → motive_3 tail → motive_3 (head :: tail)) {a : NTm}
  (t : NOk a), motive_2 a (NTm.rec app var var_1 app_1 nil cons a) t
-/
#guard_msgs in
#check @NOk.rec

/-- It computes, and at a motive that mentions the data recursion. -/
example {motive_1 : NTm → Sort u} {motive_2 : (a : NTm) → motive_1 a → NOk a → Prop}
    {motive_3 : List NTm → Sort u}
    (app : (ts : List NTm) → motive_3 ts → motive_1 (NTm.app ts)) (var : motive_1 NTm.var)
    (var_1 : motive_2 NTm.var var NOk.var)
    (app_1 : ∀ ts ts_ih, motive_2 (NTm.app ts) (app ts ts_ih) (NOk.app ts)) (nil : motive_3 [])
    (cons : (head : NTm) → (tail : List NTm) → motive_1 head → motive_3 tail →
      motive_3 (head :: tail)) :
    NOk.rec app var var_1 app_1 nil cons NOk.var = var_1 := rfl

end ByMember

/-! ## Nestings that are not one `List`, and indices that are more than one

Everything above nests through `List`, once, at the whole of the nesting type's
argument, and indexes the proposition by that one nesting.  Each of those is a
coincidence of the example rather than something the denesting relies on, so
here is one block per coincidence dropped. -/

namespace BagNest

/-! The nesting type is one the writer defined a moment ago.  Nothing looks it up
by name -- a copy is made of whatever the member is nested through, and `Bag`'s
constructors come back as minors the same way `List`'s do. -/

inductive Bag (α : Type u) : Type u where
  | none : Bag α
  | two  : α → α → Bag α

mutual
inductive UTree : Type where
  | node : (cs : Bag UTree) → UOk cs → UTree
inductive UOk : Bag UTree → Prop where
  | none : UOk .none
  | two  : (a b : UTree) → UOk (.two a b)
end

/-- info: UTree.node : (cs : Bag UTree) → UOk cs → UTree -/
#guard_msgs in
#check @UTree.node

/-- info: UOk : Bag UTree → Prop -/
#guard_msgs in
#check @UOk

/--
info: @UTree.rec : {motive_1 : UTree → Sort u_1} →
  {motive_2 : Bag UTree → Sort u_1} →
    {motive_3 : (a : Bag UTree) → motive_2 a → UOk a → Prop} →
      ((cs : Bag UTree) → (a : UOk cs) → (cs_ih : motive_2 cs) → motive_3 cs cs_ih a → motive_1 (UTree.node cs a)) →
        (none : motive_2 Bag.none) →
          (two : (a a_1 : UTree) → motive_1 a → motive_1 a_1 → motive_2 (Bag.two a a_1)) →
            motive_3 Bag.none none UOk.none →
              (∀ (a b : UTree) (a_ih : motive_1 a) (b_ih : motive_1 b), motive_3 (Bag.two a b) (two a b a_ih b_ih) ⋯) →
                (t : UTree) → motive_1 t
-/
#guard_msgs in
#check @UTree.rec

/--
info: @UOk.rec : ∀ {motive : (a : Bag UTree) → UOk a → Prop},
  motive Bag.none UOk.none → (∀ (a b : UTree), motive (Bag.two a b) ⋯) → ∀ {a : Bag UTree} (h : UOk a), motive a h
-/
#guard_msgs in
#check @UOk.rec

end BagNest

namespace TwoNestings

/-! Two nesting types in the one constructor.  Each gets a copy and so a motive
of its own, and the proposition is over only the first of them -- which is what
makes this worth pinning, since the recursion has to know which copy the
proposition's motive stands on. -/

mutual
inductive VTree : Type where
  | node : (cs : List VTree) → (o : Option VTree) → VOk cs → VTree
inductive VOk : List VTree → Prop where
  | nil  : VOk []
  | cons : (t : VTree) → (ts : List VTree) → VOk ts → VOk (t :: ts)
end

/-- info: VTree.node : (cs : List VTree) → Option VTree → VOk cs → VTree -/
#guard_msgs in
#check @VTree.node

/--
info: @VTree.rec : {motive_1 : VTree → Sort u_1} →
  {motive_2 : List VTree → Sort u_1} →
    {motive_3 : Option VTree → Sort u_1} →
      {motive_4 : (a : List VTree) → motive_2 a → VOk a → Prop} →
        ((cs : List VTree) →
            (o : Option VTree) →
              (a : VOk cs) → (cs_ih : motive_2 cs) → motive_3 o → motive_4 cs cs_ih a → motive_1 (VTree.node cs o a)) →
          (nil : motive_2 []) →
            (cons : (head : VTree) → (tail : List VTree) → motive_1 head → motive_2 tail → motive_2 (head :: tail)) →
              motive_3 none →
                ((val : VTree) → motive_1 val → motive_3 (some val)) →
                  motive_4 [] nil VOk.nil →
                    (∀ (t : VTree) (ts : List VTree) (a : VOk ts) (t_ih : motive_1 t) (ts_ih : motive_2 ts),
                        motive_4 ts ts_ih a → motive_4 (t :: ts) (cons t ts t_ih ts_ih) ⋯) →
                      (t : VTree) → motive_1 t
-/
#guard_msgs in
#check @VTree.rec

/--
info: @VOk.rec : ∀ {motive : (a : List VTree) → VOk a → Prop},
  motive [] VOk.nil →
    (∀ (t : VTree) (ts : List VTree) (a : VOk ts), motive ts a → motive (t :: ts) ⋯) →
      ∀ {a : List VTree} (h : VOk a), motive a h
-/
#guard_msgs in
#check @VOk.rec

end TwoNestings

namespace PairNest

/-! The member is not the whole of what is nested through: `List (XTree × Nat)`
nests through `Prod` and then through `List`, and the copy of `Prod` is a
one-constructor type carrying a `Nat` that has nothing to do with the block.

This is the one block in the section whose recursion over the whole of it leaves
the proposition out, and the reason is the two layers: `XOk.cons` is indexed at
`(t, n) :: ts`, a constructor of the `List` copy at a constructor of the `Prod`
copy, and the recursion filling in the `List` copy's step has a call at its own
fields and none at what is inside them.  So `XTree.rec` recurses over the data
and `XOk.rec` is the split one. -/

mutual
inductive XTree : Type where
  | node : (cs : List (XTree × Nat)) → XOk cs → XTree
inductive XOk : List (XTree × Nat) → Prop where
  | nil  : XOk []
  | cons : (t : XTree) → (n : Nat) → (ts : List (XTree × Nat)) → XOk ts → XOk ((t, n) :: ts)
end

/-- info: XTree.node : (cs : List (XTree × Nat)) → XOk cs → XTree -/
#guard_msgs in
#check @XTree.node

/--
info: @XTree.rec : {motive_1 : XTree → Sort u_1} →
  {motive_2 : List (XTree × Nat) → Sort u_1} →
    {motive_3 : XTree × Nat → Sort u_1} →
      ((cs : List (XTree × Nat)) → (a : XOk cs) → motive_2 cs → motive_1 (XTree.node cs a)) →
        motive_2 [] →
          ((head : XTree × Nat) →
              (tail : List (XTree × Nat)) → motive_3 head → motive_2 tail → motive_2 (head :: tail)) →
            ((fst : XTree) → (snd : Nat) → motive_1 fst → motive_3 (fst, snd)) → (t : XTree) → motive_1 t
-/
#guard_msgs in
#check @XTree.rec

/--
info: @XOk.rec : ∀ {motive : (a : List (XTree × Nat)) → XOk a → Prop},
  motive [] XOk.nil →
    (∀ (t : XTree) (n : Nat) (ts : List (XTree × Nat)) (a : XOk ts), motive ts a → motive ((t, n) :: ts) ⋯) →
      ∀ {a : List (XTree × Nat)} (h : XOk a), motive a h
-/
#guard_msgs in
#check @XOk.rec

end PairNest

namespace BothKinds

/-! Both readings in the one block.  `YOk` is over the nesting and keeps the
split recursor; `YGood` is over a member and gets the recursion over the whole
block, concluding at the motive taken at what the data recursion returned.  The
two sit side by side without either one deciding for the other. -/

mutual
inductive YTm : Type where
  | app : (ts : List YTm) → YOk ts → YTm
  | var : YTm
inductive YOk : List YTm → Prop where
  | nil  : YOk []
  | cons : (t : YTm) → (ts : List YTm) → YOk ts → YOk (t :: ts)
inductive YGood : YTm → Prop where
  | var : YGood .var
end

/--
info: @YTm.rec : {motive_1 : YTm → Sort u_1} →
  {motive_2 : (a : YTm) → motive_1 a → YGood a → Prop} →
    {motive_3 : List YTm → Sort u_1} →
      {motive_4 : (a : List YTm) → motive_3 a → YOk a → Prop} →
        ((ts : List YTm) → (a : YOk ts) → (ts_ih : motive_3 ts) → motive_4 ts ts_ih a → motive_1 (YTm.app ts a)) →
          (var : motive_1 YTm.var) →
            motive_2 YTm.var var YGood.var →
              (nil : motive_3 []) →
                (cons : (head : YTm) → (tail : List YTm) → motive_1 head → motive_3 tail → motive_3 (head :: tail)) →
                  motive_4 [] nil YOk.nil →
                    (∀ (t : YTm) (ts : List YTm) (a : YOk ts) (t_ih : motive_1 t) (ts_ih : motive_3 ts),
                        motive_4 ts ts_ih a → motive_4 (t :: ts) (cons t ts t_ih ts_ih) ⋯) →
                      (t : YTm) → motive_1 t
-/
#guard_msgs in
#check @YTm.rec

/--
info: @YOk.rec : ∀ {motive_1 : (a : List YTm) → YOk a → Prop} {motive_2 : (a : YTm) → YGood a → Prop},
  motive_1 [] YOk.nil →
    (∀ (t : YTm) (ts : List YTm) (a : YOk ts), motive_1 ts a → motive_1 (t :: ts) ⋯) →
      motive_2 YTm.var YGood.var → ∀ {a : List YTm} (h : YOk a), motive_1 a h
-/
#guard_msgs in
#check @YOk.rec

/--
info: @YGood.rec : ∀ {motive_1 : YTm → Sort u_1} {motive_2 : (a : YTm) → motive_1 a → YGood a → Prop}
  {motive_3 : List YTm → Sort u_1} {motive_4 : (a : List YTm) → motive_3 a → YOk a → Prop}
  (app : (ts : List YTm) → (a : YOk ts) → (ts_ih : motive_3 ts) → motive_4 ts ts_ih a → motive_1 (YTm.app ts a))
  (var : motive_1 YTm.var) (var_1 : motive_2 YTm.var var YGood.var) (nil : motive_3 [])
  (cons : (head : YTm) → (tail : List YTm) → motive_1 head → motive_3 tail → motive_3 (head :: tail))
  (nil_1 : motive_4 [] nil YOk.nil)
  (cons_1 :
    ∀ (t : YTm) (ts : List YTm) (a : YOk ts) (t_ih : motive_1 t) (ts_ih : motive_3 ts),
      motive_4 ts ts_ih a → motive_4 (t :: ts) (cons t ts t_ih ts_ih) ⋯)
  {a : YTm} (t : YGood a), motive_2 a (YTm.rec app var var_1 nil cons nil_1 cons_1 a) t
-/
#guard_msgs in
#check @YGood.rec

end BothKinds

/-! ### More than one index at a nesting

A proposition may be indexed by two nestings at once, and then a proof of it is
a proof standing on two round trips rather than one.  Bringing it back to the
writer's own fields is one transport per field, and each of those moves the
proof as well, so a step has to read the proof's statement at where the earlier
steps left it rather than at where it started.  Getting that wrong is not a
statement that says too little -- it is a term the kernel rejects, and the whole
bridge with it, so these are pinned as much as a regression as for the shape. -/

namespace TwoIndices

mutual
inductive T : Type where
  | node : (a b : List T) → Ok a b → T
inductive Ok : List T → List T → Prop where
  | nil   : Ok [] []
  | consL : (t : T) → (a b : List T) → Ok a b → Ok (t :: a) b
  | consR : (t : T) → (a b : List T) → Ok a b → Ok a (t :: b)
end

/-- info: T.node : (a b : List T) → Ok a b → T -/
#guard_msgs in
#check @T.node

/-- info: Ok.consL : ∀ (t : T) (a b : List T), Ok a b → Ok (t :: a) b -/
#guard_msgs in
#check @Ok.consL

/--
info: @T.rec : {motive_1 : T → Sort u_1} →
  {motive_2 : List T → Sort u_1} →
    ((a b : List T) → (a_1 : Ok a b) → motive_2 a → motive_2 b → motive_1 (T.node a b a_1)) →
      motive_2 [] →
        ((head : T) → (tail : List T) → motive_1 head → motive_2 tail → motive_2 (head :: tail)) → (t : T) → motive_1 t
-/
#guard_msgs in
#check @T.rec

/--
info: @Ok.rec : ∀ {motive : (a a_1 : List T) → Ok a a_1 → Prop},
  motive [] [] Ok.nil →
    (∀ (t : T) (a b : List T) (a_1 : Ok a b), motive a b a_1 → motive (t :: a) b ⋯) →
      (∀ (t : T) (a b : List T) (a_1 : Ok a b), motive a b a_1 → motive a (t :: b) ⋯) →
        ∀ {a a_1 : List T} (h : Ok a a_1), motive a a_1 h
-/
#guard_msgs in
#check @Ok.rec

/-- The iota rule holds on the constructor that steps in the second index, which
is the one that had to be carried furthest. -/
example {p : (a b : List T) → Ok a b → Prop} (hn : p [] [] Ok.nil)
    (hl : ∀ t a b h, p a b h → p (t :: a) b (Ok.consL t a b h))
    (hr : ∀ t a b h, p a b h → p a (t :: b) (Ok.consR t a b h))
    (t : T) (a b : List T) (h : Ok a b) :
    Ok.rec (motive := p) hn hl hr (Ok.consR t a b h)
      = hr t a b h (Ok.rec (motive := p) hn hl hr h) := rfl

end TwoIndices

namespace MixedIndices

/-! Three indices, at two nesting types, one of them a nesting of a nesting. -/

mutual
inductive U : Type where
  | node : (a : List U) → (b : List (List U)) → (c : Option U) → Ok a b c → U
inductive Ok : List U → List (List U) → Option U → Prop where
  | nil  : Ok [] [] none
  | cons : (t : List U) → (a : List U) → (b : List (List U)) → (c : Option U) →
      Ok a b c → Ok a (t :: b) c
end

/-- info: U.node : (a : List U) → (b : List (List U)) → (c : Option U) → Ok a b c → U -/
#guard_msgs in
#check @U.node

/--
info: @U.rec : {motive_1 : U → Sort u_1} →
  {motive_2 : List U → Sort u_1} →
    {motive_3 : List (List U) → Sort u_1} →
      {motive_4 : Option U → Sort u_1} →
        ((a : List U) →
            (b : List (List U)) →
              (c : Option U) → (a_1 : Ok a b c) → motive_2 a → motive_3 b → motive_4 c → motive_1 (U.node a b c a_1)) →
          motive_2 [] →
            ((head : U) → (tail : List U) → motive_1 head → motive_2 tail → motive_2 (head :: tail)) →
              motive_3 [] →
                ((head : List U) → (tail : List (List U)) → motive_2 head → motive_3 tail → motive_3 (head :: tail)) →
                  motive_4 none → ((val : U) → motive_1 val → motive_4 (some val)) → (t : U) → motive_1 t
-/
#guard_msgs in
#check @U.rec

/--
info: @Ok.rec : ∀ {motive : (a : List U) → (a_1 : List (List U)) → (a_2 : Option U) → Ok a a_1 a_2 → Prop},
  motive [] [] none Ok.nil →
    (∀ (t a : List U) (b : List (List U)) (c : Option U) (a_1 : Ok a b c), motive a b c a_1 → motive a (t :: b) c ⋯) →
      ∀ {a : List U} {a_1 : List (List U)} {a_2 : Option U} (h : Ok a a_1 a_2), motive a a_1 a_2 h
-/
#guard_msgs in
#check @Ok.rec

example {p : (a : List U) → (b : List (List U)) → (c : Option U) → Ok a b c → Prop}
    (hn : p [] [] none Ok.nil)
    (hc : ∀ t a b c h, p a b c h → p a (t :: b) c (Ok.cons t a b c h))
    (t : List U) (a : List U) (b : List (List U)) (c : Option U) (h : Ok a b c) :
    Ok.rec (motive := p) hn hc (Ok.cons t a b c h)
      = hc t a b c h (Ok.rec (motive := p) hn hc h) := rfl

end MixedIndices

/-! A block Lean rejected and this elaborator picked up gets the same treatment,
and which route picks it up now depends on the `deriving` clause as well.  This
one nests at a local, so both routes can take it: the induction-inductive one
states the field as it was written and lowering does not, so it is tried first
and, `DecidableEq` being a class the subtype lifts, it takes. -/

inductive HWrap (α : Type) (n : Nat) where
  | mk (a : α) : HWrap α n

inductive HVec where
  | tip
  | mk (n : Nat) (v : List (HWrap HVec n)) : HVec
  deriving DecidableEq

/-- info: HVec.mk : (n : Nat) → List (HWrap HVec n) → HVec -/
#guard_msgs in
#check @HVec.mk

/-- info: false -/
#guard_msgs in
#eval decide (HVec.tip = HVec.mk 0 [])

/-! Ask that one for `Inhabited` and it stays where it was.  It used to not:
the class was one only lowering could answer, a failure to derive is how a route
declines, and the block came back with `JVec.nested_List_1` visible in the
constructor it had been written with `List (HWrap JVec n)` in.  Deriving the
class from a constructor settles it on the route that keeps the written type. -/

inductive JVec where
  | tip
  | mk (n : Nat) (v : List (HWrap JVec n)) : JVec
  deriving Inhabited

/-- info: JVec.mk : (n : Nat) → List (HWrap JVec n) → JVec -/
#guard_msgs in
#check @JVec.mk

example : (default : JVec) = JVec.tip := rfl

/-! Both classes at once, to check the constructor route and the delta route do
not tread on each other: `Inhabited` is taken off the list before the rest of it
is delta derived. -/

inductive KVec where
  | tip
  | mk (n : Nat) (v : List (HWrap KVec n)) : KVec
  deriving Inhabited, DecidableEq

/-- info: KVec.mk : (n : Nat) → List (HWrap KVec n) → KVec -/
#guard_msgs in
#check @KVec.mk

/-- info: false -/
#guard_msgs in
#eval decide ((default : KVec) = KVec.mk 0 [])

/-! And a block of this shape that nothing inhabits keeps its type all the same.
The class cannot be derived on any of the three routes, so the last of them --
which has no fourth to hand the block on to -- warns instead of failing, since
a block with a class missing beats no block at all. -/

/--
warning: Failed to delta derive `Inhabited` instance for `LVec`.

Note: Delta deriving tries the following strategies: (1) inserting the definition into each explicit non-out-param parameter of a class and (2) unfolding definitions further.

Note: A data member of an induction-inductive block is the subtype of its pre-type, so `deriving` reaches it only through an instance `Subtype` already has -- `DecidableEq` and `Repr` do, and a class that does not has to be instanced by hand
-/
#guard_msgs in
inductive LVec where
  | mk (n : Nat) (v : List (HWrap LVec n)) (w : LVec) : LVec
  deriving Inhabited

/-- info: LVec.mk : (n : Nat) → List (HWrap LVec n) → LVec → LVec -/
#guard_msgs in
#check @LVec.mk


/-! ## Universes the block does not share, and nestings that are not inductive

A member's result universe reaches the nesting: `List (T α β)` with
`T : Type (max u v)` is `List.{max u v}`, and that level gets written down once
per place the occurrence appears.  It does not come out spelled the same way
twice -- `max` collects its arguments into a set, and the order they leave in is
whatever order they went in -- so a copy has to be recognised up to the normal
form of its levels and not up to how they were written.  Recognising it by the
spelling puts the copy in the member's arity, where the occurrence was written
one way, and leaves the original standing in a constructor's index, where it was
written the other; the two then disagree about what the constructor concludes
at, and the kernel says so.

After that, three nestings that are not the plain `List` of a member: a member
under an arrow, a member under a dependent pair, and a member under a `List`
that is itself indexed. -/

namespace MaxUniverse

mutual
inductive T (α : Type u) (β : Type v) : Type (max u v) where
  | node : (a : α) → (b : β) → (cs : List (T α β)) → Ok α β cs → T α β
inductive Ok (α : Type u) (β : Type v) : List (T α β) → Prop where
  | nil  : Ok α β []
  | cons : (t : T α β) → (ts : List (T α β)) → Ok α β ts → Ok α β (t :: ts)
end

/--
info: @T.node : {α : Type u_1} → {β : Type u_2} → α → β → (cs : List (T α β)) → Ok α β cs → T α β
-/
#guard_msgs in
#check @T.node

/-- info: Ok : (α : Type u_1) → (β : Type u_2) → List (T α β) → Prop -/
#guard_msgs in
#check @Ok

/--
info: @T.rec : {α : Type u_2} →
  {β : Type u_3} →
    {motive_1 : T α β → Sort u_1} →
      {motive_2 : List (T α β) → Sort u_1} →
        {motive_3 : (a : List (T α β)) → motive_2 a → Ok α β a → Prop} →
          ((a : α) →
              (b : β) →
                (cs : List (T α β)) →
                  (a_1 : Ok α β cs) → (cs_ih : motive_2 cs) → motive_3 cs cs_ih a_1 → motive_1 (T.node a b cs a_1)) →
            (nil : motive_2 []) →
              (cons :
                  (head : T α β) → (tail : List (T α β)) → motive_1 head → motive_2 tail → motive_2 (head :: tail)) →
                motive_3 [] nil ⋯ →
                  (∀ (t : T α β) (ts : List (T α β)) (a : Ok α β ts) (t_ih : motive_1 t) (ts_ih : motive_2 ts),
                      motive_3 ts ts_ih a → motive_3 (t :: ts) (cons t ts t_ih ts_ih) ⋯) →
                    (t : T α β) → motive_1 t
-/
#guard_msgs in
#check @T.rec

/--
info: @Ok.rec : ∀ {α : Type u_1} {β : Type u_2} {motive : (a : List (T α β)) → Ok α β a → Prop},
  motive [] ⋯ →
    (∀ (t : T α β) (ts : List (T α β)) (a : Ok α β ts), motive ts a → motive (t :: ts) ⋯) →
      ∀ {a : List (T α β)} (h : Ok α β a), motive a h
-/
#guard_msgs in
#check @Ok.rec

example {α : Type u} {β : Type v} {p : (ts : List (T α β)) → Ok α β ts → Prop}
    (hn : p [] Ok.nil) (hc : ∀ t ts h, p ts h → p (t :: ts) (Ok.cons t ts h))
    (t : T α β) (ts : List (T α β)) (h : Ok α β ts) :
    Ok.rec (motive := p) hn hc (Ok.cons t ts h)
      = hc t ts h (Ok.rec (motive := p) hn hc h) := rfl

end MaxUniverse

namespace PhantomUniverse

/-! The same block with a universe the parameters do not mention at all.  `v` is
there only in the result, so every occurrence of the block carries it explicitly
and there is no second way to arrive at it. -/

mutual
inductive T (α : Type u) : Type (max u v) where
  | node : (a : α) → (cs : List (T.{u, v} α)) → Ok.{u, v} α cs → T α
inductive Ok (α : Type u) : List (T.{u, v} α) → Prop where
  | nil  : Ok.{u, v} α []
  | cons : (t : T.{u, v} α) → (ts : List (T.{u, v} α)) → Ok.{u, v} α ts →
      Ok.{u, v} α (t :: ts)
end

/-- info: @T.node : {α : Type u_1} → α → (cs : List (T α)) → Ok α cs → T α -/
#guard_msgs in
#check @T.node

/--
info: @Ok.rec : ∀ {α : Type u_1} {motive : (a : List (T α)) → Ok α a → Prop},
  motive [] ⋯ →
    (∀ (t : T α) (ts : List (T α)) (a : Ok α ts), motive ts a → motive (t :: ts) ⋯) →
      ∀ {a : List (T α)} (h : Ok α a), motive a h
-/
#guard_msgs in
#check @Ok.rec

end PhantomUniverse

namespace ArrowIndex

/-! A member under an arrow rather than under an inductive.  There is nothing to
denest -- an arrow is not a type a copy can be made of, and it is not one the
kernel refuses either -- so the proposition keeps `Nat → T` as its index and
nothing is added to the block.  What the data recursion gains is the hypothesis
at every argument the function could be applied to. -/

mutual
inductive T : Type where
  | node : (f : Nat → T) → Ok f → T
  | leaf : T
inductive Ok : (Nat → T) → Prop where
  | mk : (f : Nat → T) → Ok f
end

/-- info: T.node : (f : Nat → T) → Ok f → T -/
#guard_msgs in
#check @T.node

/--
info: @T.rec : {motive : T → Sort u_1} →
  ((f : Nat → T) → (a : Ok f) → ((a : Nat) → motive (f a)) → motive (T.node f a)) → motive T.leaf → (t : T) → motive t
-/
#guard_msgs in
#check @T.rec

/--
info: @Ok.rec : {motive : (a : Nat → T) → Ok a → Sort u_1} →
  ((f : Nat → T) → motive f ⋯) → {a : Nat → T} → (h : Ok a) → motive a h
-/
#guard_msgs in
#check @Ok.rec

end ArrowIndex

namespace SigmaNest

/-! A member under core's `Sigma`, under a `List`, with the proposition over the
whole of it.  Both get copies, so the block gains two members the writer did not
write, and the proposition's `cons` indexes at a pair rather than at a bare
member. -/

mutual
inductive T : Type where
  | node : (cs : List ((_ : Nat) × T)) → Ok cs → T
  | leaf : T
inductive Ok : List ((_ : Nat) × T) → Prop where
  | nil  : Ok []
  | cons : (c : (_ : Nat) × T) → (cs : List ((_ : Nat) × T)) → Ok cs → Ok (c :: cs)
end

/-- info: T.node : (cs : List ((_ : Nat) × T)) → Ok cs → T -/
#guard_msgs in
#check @T.node

/--
info: @T.rec : {motive_1 : T → Sort u_1} →
  {motive_2 : List ((_ : Nat) × T) → Sort u_1} →
    {motive_3 : (_ : Nat) × T → Sort u_1} →
      {motive_4 : (a : List ((_ : Nat) × T)) → motive_2 a → Ok a → Prop} →
        ((cs : List ((_ : Nat) × T)) →
            (a : Ok cs) → (cs_ih : motive_2 cs) → motive_4 cs cs_ih a → motive_1 (T.node cs a)) →
          motive_1 T.leaf →
            (nil : motive_2 []) →
              (cons :
                  (head : (_ : Nat) × T) →
                    (tail : List ((_ : Nat) × T)) → motive_3 head → motive_2 tail → motive_2 (head :: tail)) →
                ((fst : Nat) → (snd : T) → motive_1 snd → motive_3 ⟨fst, snd⟩) →
                  motive_4 [] nil Ok.nil →
                    (∀ (c : (_ : Nat) × T) (cs : List ((_ : Nat) × T)) (a : Ok cs) (c_ih : motive_3 c)
                        (cs_ih : motive_2 cs), motive_4 cs cs_ih a → motive_4 (c :: cs) (cons c cs c_ih cs_ih) ⋯) →
                      (t : T) → motive_1 t
-/
#guard_msgs in
#check @T.rec

/--
info: @Ok.rec : ∀ {motive : (a : List ((_ : Nat) × T)) → Ok a → Prop},
  motive [] Ok.nil →
    (∀ (c : (_ : Nat) × T) (cs : List ((_ : Nat) × T)) (a : Ok cs), motive cs a → motive (c :: cs) ⋯) →
      ∀ {a : List ((_ : Nat) × T)} (h : Ok a), motive a h
-/
#guard_msgs in
#check @Ok.rec

example {p : (cs : List ((_ : Nat) × T)) → Ok cs → Prop} (hn : p [] Ok.nil)
    (hc : ∀ c cs h, p cs h → p (c :: cs) (Ok.cons c cs h))
    (c : (_ : Nat) × T) (cs : List ((_ : Nat) × T)) (h : Ok cs) :
    Ok.rec (motive := p) hn hc (Ok.cons c cs h)
      = hc c cs h (Ok.rec (motive := p) hn hc h) := rfl

end SigmaNest

namespace ComputedIndex

/-! The index a constructor concludes at is computed from a field rather than
being one of them: `V.cons` at `n` lands in `V (n + n)`.  The nesting is indexed
as well -- `List (V n)` is a copy carrying an `n` of its own -- so the copy, the
proposition and the constructor all have to be standing at the same one. -/

mutual
inductive V : Nat → Type where
  | nil  : V 0
  | cons : (n : Nat) → (cs : List (V n)) → Ok n cs → V (n + n)
inductive Ok : (n : Nat) → List (V n) → Prop where
  | nil  : (n : Nat) → Ok n []
  | cons : (n : Nat) → (t : V n) → (ts : List (V n)) → Ok n ts → Ok n (t :: ts)
end

/-- info: V.cons : (n : Nat) → (cs : List (V n)) → Ok n cs → V (n + n) -/
#guard_msgs in
#check @V.cons

/--
info: @V.rec : {motive_1 : (a : Nat) → V a → Sort u_1} →
  {motive_2 : (n : Nat) → List (V n) → Sort u_1} →
    {motive_3 : (n : Nat) → (a : List (V n)) → motive_2 n a → Ok n a → Prop} →
      motive_1 0 V.nil →
        ((n : Nat) →
            (cs : List (V n)) →
              (a : Ok n cs) → (cs_ih : motive_2 n cs) → motive_3 n cs cs_ih a → motive_1 (n + n) (V.cons n cs a)) →
          (nil_1 : (n : Nat) → motive_2 n []) →
            (cons_1 :
                (n : Nat) →
                  (head : V n) → (tail : List (V n)) → motive_1 n head → motive_2 n tail → motive_2 n (head :: tail)) →
              (∀ (n : Nat), motive_3 n [] (nil_1 n) ⋯) →
                (∀ (n : Nat) (t : V n) (ts : List (V n)) (a : Ok n ts) (t_ih : motive_1 n t) (ts_ih : motive_2 n ts),
                    motive_3 n ts ts_ih a → motive_3 n (t :: ts) (cons_1 n t ts t_ih ts_ih) ⋯) →
                  {a : Nat} → (t : V a) → motive_1 a t
-/
#guard_msgs in
#check @V.rec

/--
info: @Ok.rec : ∀ {motive : (n : Nat) → (a : List (V n)) → Ok n a → Prop},
  (∀ (n : Nat), motive n [] ⋯) →
    (∀ (n : Nat) (t : V n) (ts : List (V n)) (a : Ok n ts), motive n ts a → motive n (t :: ts) ⋯) →
      ∀ {n : Nat} {a : List (V n)} (h : Ok n a), motive n a h
-/
#guard_msgs in
#check @Ok.rec

example {p : (n : Nat) → (ts : List (V n)) → Ok n ts → Prop}
    (hn : ∀ n, p n [] (Ok.nil n))
    (hc : ∀ n t ts h, p n ts h → p n (t :: ts) (Ok.cons n t ts h))
    (n : Nat) (t : V n) (ts : List (V n)) (h : Ok n ts) :
    Ok.rec (motive := p) hn hc (Ok.cons n t ts h)
      = hc n t ts h (Ok.rec (motive := p) hn hc h) := rfl

end ComputedIndex

namespace ThreeSorts

/-! Three data members, each indexed by the one before it, and a proposition
over a nesting of the first.  Every member's recursor is the one recursion over
the whole block read at a different conclusion, so the proposition's minors
appear in `Ctx.rec` and `Tm.rec` alike -- and `Ok.rec`, which is over the
nesting rather than over a member, stays the split one the writer can state. -/

mutual
inductive Ctx : Type where
  | nil  : Ctx
  | snoc : (Γ : Ctx) → Ty Γ → Ctx
inductive Ty : Ctx → Type where
  | base : (Γ : Ctx) → Ty Γ
inductive Tm : (Γ : Ctx) → Ty Γ → Type where
  | var  : (Γ : Ctx) → (A : Ty Γ) → Tm Γ A
  | pack : (Γ : Ctx) → (A : Ty Γ) → (cs : List Ctx) → Ok cs → Tm Γ A
inductive Ok : List Ctx → Prop where
  | nil  : Ok []
  | cons : (Γ : Ctx) → (Γs : List Ctx) → Ok Γs → Ok (Γ :: Γs)
end

/-- info: Tm.pack : (Γ : Ctx) → (A : Ty Γ) → (cs : List Ctx) → Ok cs → Tm Γ A -/
#guard_msgs in
#check @Tm.pack

/--
info: @Ctx.rec : {motive_1 : Ctx → Sort u_1} →
  {motive_2 : (a : Ctx) → Ty a → Sort u_1} →
    {motive_3 : (Γ : Ctx) → (a : Ty Γ) → Tm Γ a → Sort u_1} →
      {motive_4 : List Ctx → Sort u_1} →
        {motive_5 : (a : List Ctx) → motive_4 a → Ok a → Prop} →
          motive_1 Ctx.nil →
            ((Γ : Ctx) → (a : Ty Γ) → motive_1 Γ → motive_2 Γ a → motive_1 (Γ.snoc a)) →
              ((Γ : Ctx) → motive_1 Γ → motive_2 Γ (Ty.base Γ)) →
                ((Γ : Ctx) → (A : Ty Γ) → motive_1 Γ → motive_2 Γ A → motive_3 Γ A (Tm.var Γ A)) →
                  ((Γ : Ctx) →
                      (A : Ty Γ) →
                        (cs : List Ctx) →
                          (a : Ok cs) →
                            motive_1 Γ →
                              motive_2 Γ A →
                                (cs_ih : motive_4 cs) → motive_5 cs cs_ih a → motive_3 Γ A (Tm.pack Γ A cs a)) →
                    (nil_1 : motive_4 []) →
                      (cons :
                          (head : Ctx) → (tail : List Ctx) → motive_1 head → motive_4 tail → motive_4 (head :: tail)) →
                        motive_5 [] nil_1 Ok.nil →
                          (∀ (Γ : Ctx) (Γs : List Ctx) (a : Ok Γs) (Γ_ih : motive_1 Γ) (Γs_ih : motive_4 Γs),
                              motive_5 Γs Γs_ih a → motive_5 (Γ :: Γs) (cons Γ Γs Γ_ih Γs_ih) ⋯) →
                            (t : Ctx) → motive_1 t
-/
#guard_msgs in
#check @Ctx.rec

/--
info: @Tm.rec : {motive_1 : Ctx → Sort u_1} →
  {motive_2 : (a : Ctx) → Ty a → Sort u_1} →
    {motive_3 : (Γ : Ctx) → (a : Ty Γ) → Tm Γ a → Sort u_1} →
      {motive_4 : List Ctx → Sort u_1} →
        {motive_5 : (a : List Ctx) → motive_4 a → Ok a → Prop} →
          motive_1 Ctx.nil →
            ((Γ : Ctx) → (a : Ty Γ) → motive_1 Γ → motive_2 Γ a → motive_1 (Γ.snoc a)) →
              ((Γ : Ctx) → motive_1 Γ → motive_2 Γ (Ty.base Γ)) →
                ((Γ : Ctx) → (A : Ty Γ) → motive_1 Γ → motive_2 Γ A → motive_3 Γ A (Tm.var Γ A)) →
                  ((Γ : Ctx) →
                      (A : Ty Γ) →
                        (cs : List Ctx) →
                          (a : Ok cs) →
                            motive_1 Γ →
                              motive_2 Γ A →
                                (cs_ih : motive_4 cs) → motive_5 cs cs_ih a → motive_3 Γ A (Tm.pack Γ A cs a)) →
                    (nil_1 : motive_4 []) →
                      (cons :
                          (head : Ctx) → (tail : List Ctx) → motive_1 head → motive_4 tail → motive_4 (head :: tail)) →
                        motive_5 [] nil_1 Ok.nil →
                          (∀ (Γ : Ctx) (Γs : List Ctx) (a : Ok Γs) (Γ_ih : motive_1 Γ) (Γs_ih : motive_4 Γs),
                              motive_5 Γs Γs_ih a → motive_5 (Γ :: Γs) (cons Γ Γs Γ_ih Γs_ih) ⋯) →
                            {Γ : Ctx} → {a : Ty Γ} → (t : Tm Γ a) → motive_3 Γ a t
-/
#guard_msgs in
#check @Tm.rec

/--
info: @Ok.rec : ∀ {motive : (a : List Ctx) → Ok a → Prop},
  motive [] Ok.nil →
    (∀ (Γ : Ctx) (Γs : List Ctx) (a : Ok Γs), motive Γs a → motive (Γ :: Γs) ⋯) →
      ∀ {a : List Ctx} (h : Ok a), motive a h
-/
#guard_msgs in
#check @Ok.rec

/-- The length of a context.  It looks at one member of five, but the recursion
is over the whole block, so all five motives have to be given something -- the
proposition's is filled with `True`, which is the cheapest thing that typechecks
and says how little the answer depends on it. -/
def Ctx.len (Γ : Ctx) : Nat :=
  Ctx.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ _ => Nat)
    (motive_3 := fun _ _ _ => Nat) (motive_4 := fun _ => Nat)
    (motive_5 := fun _ _ _ => True)
    0 (fun _ _ n _ => n + 1) (fun _ n => n) (fun _ _ n _ => n)
    (fun _ _ _ _ n _ _ _ => n) 0 (fun _ _ n m => n + m)
    trivial (fun _ _ _ _ _ _ => trivial) Γ

example : Ctx.nil.len = 0 := rfl

example : (Ctx.snoc (Ctx.snoc .nil (.base .nil)) (.base _)).len = 2 := rfl

end ThreeSorts

/-! ## Propositions the block is not stated with

A proposition can be written inside one of these blocks without being part of
what makes it induction-inductive.  If no data member's arity or field mentions
it, and neither does any proposition that stays, then it is a *consumer* of the
block: everything it is about exists once the rest of the block does, and it can
be declared afterwards as the ordinary inductive it already is.

Doing that for every such proposition would be a loss.  One the erasure carries
comes back with the recursion over the whole block -- the data recursion and the
proof stepping together -- which is worth more than the plain recursor it would
get outside, and the blocks above were written for it.  So the peel is kept for
the one case where the erasure has nothing to offer at all: a constructor with a
data-typed field its own conclusion says nothing about.  There is no
well-formedness in reach for such a field, so no minor premise can be stated,
and until this section such a member came out with no recursor whatsoever.

What it comes out with instead is everything: a real recursor, `casesOn`,
`brecOn` -- and so `match` and `induction` -- `noConfusion`, and `deriving` that
goes through the ordinary handlers rather than through the subtype. -/

namespace PeelUnpinned

mutual
inductive T : Type where
  | node : (cs : List T) → Ok cs → T
  | leaf : T
inductive Ok : List T → Prop where
  | nil  : Ok []
  | cons : (t : T) → (ts : List T) → Ok ts → Ok (t :: ts)
/-- Documented, to check that the doc string is still attached afterwards. -/
inductive Big : T → Prop where
  | node : (cs : List T) → (hs : List T) → (h : Ok cs) → Big (.node cs h)
  | leaf : Big .leaf
end

/-! `hs` is a field of `Big.node` that `Big (.node cs h)` says nothing about, so
`Big` leaves the block.  `T` and `Ok` are unaffected: the block that stays is the
one the erasure was for, and `Ok.rec` is the split recursor it always was. -/

/-- info: Big.node : ∀ (cs hs : List T) (h : Ok cs), Big (T.node cs h) -/
#guard_msgs in
#check @Big.node

/--
info: @Big.rec : ∀ {motive : (a : T) → Big a → Prop},
  (∀ (cs hs : List T) (h : Ok cs), motive (T.node cs h) ⋯) → motive T.leaf Big.leaf → ∀ {a : T} (t : Big a), motive a t
-/
#guard_msgs in
#check @Big.rec

/--
info: @Ok.rec : ∀ {motive : (a : List T) → Ok a → Prop},
  motive [] Ok.nil →
    (∀ (t : T) (ts : List T) (a : Ok ts), motive ts a → motive (t :: ts) ⋯) → ∀ {a : List T} (h : Ok a), motive a h
-/
#guard_msgs in
#check @Ok.rec

/--
info: inductive PeelUnpinned.Big : T → Prop
number of parameters: 0
constructors:
PeelUnpinned.Big.node : ∀ (cs hs : List T) (h : Ok cs), Big (T.node cs h)
PeelUnpinned.Big.leaf : Big T.leaf
-/
#guard_msgs in
#print Big

example {p : (t : T) → Big t → Prop} (hn : ∀ cs hs h, p _ (Big.node cs hs h))
    (hl : p _ Big.leaf) (cs hs : List T) (h : Ok cs) :
    Big.rec (motive := p) hn hl (Big.node cs hs h) = hn cs hs h := rfl

/-- The tactics an ordinary inductive answers to, which nothing that goes
through the erasure does. -/
example (t : T) (h : Big t) : t = .leaf ∨ ∃ cs h', t = .node cs h' := by
  induction h with
  | node cs hs h => exact Or.inr ⟨cs, h, rfl⟩
  | leaf => exact Or.inl rfl

theorem Big.byMatch (t : T) (h : Big t) : True :=
  match h with
  | .node _ _ _ => trivial
  | .leaf => trivial

end PeelUnpinned

namespace PeelNestIndexed

/-! The same shape one level out: `Long` is indexed by a *nesting* rather than by
a member.  That on its own is no obstacle -- denesting makes `List T` a member of
the block like any other, and `Ok` above is indexed by it and comes back fine --
so what peels `Long` is `extra` again.  Once it is out, its index really is a
`List T`, since a peeled member is not denested and has nothing rewritten. -/

mutual
inductive T : Type where
  | node : (cs : List T) → Ok cs → T
  | leaf : T
inductive Ok : List T → Prop where
  | nil  : Ok []
  | cons : (t : T) → (ts : List T) → Ok ts → Ok (t :: ts)
inductive Long : List T → Prop where
  | mk : (cs : List T) → (extra : T) → Long cs
end

/-- info: Long : List T → Prop -/
#guard_msgs in
#check @Long

/--
info: @Long.rec : ∀ {motive : (a : List T) → Long a → Prop},
  (∀ (cs : List T) (extra : T), motive cs ⋯) → ∀ {a : List T} (t : Long a), motive a t
-/
#guard_msgs in
#check @Long.rec

end PeelNestIndexed

namespace PeelWholeProp

/-! The block's only proposition is the one that leaves, so what stays is
induction-inductive and nothing else: `Ctx` indexed by nothing and `Ty` indexed
by `Ctx`, whose recursor is the plain two-motive one with no proposition in it
at all.  `Inhab` is the shape that made this worth doing -- a witness that
some type over `Γ` exists is the natural thing to write, and `A` is exactly the
field the conclusion cannot mention. -/

mutual
inductive Ctx : Type where
  | nil  : Ctx
  | snoc : (Γ : Ctx) → Ty Γ → Ctx
inductive Ty : Ctx → Type where
  | base : (Γ : Ctx) → Ty Γ
inductive Inhab : Ctx → Prop where
  | mk : (Γ : Ctx) → (A : Ty Γ) → Inhab Γ
end

/-- info: Inhab.mk : ∀ (Γ : Ctx) (A : Ty Γ), Inhab Γ -/
#guard_msgs in
#check @Inhab.mk

/--
info: @Inhab.rec : ∀ {motive : (a : Ctx) → Inhab a → Prop},
  (∀ (Γ : Ctx) (A : Ty Γ), motive Γ ⋯) → ∀ {a : Ctx} (t : Inhab a), motive a t
-/
#guard_msgs in
#check @Inhab.rec

/--
info: @Ctx.rec : {motive_1 : Ctx → Sort u_1} →
  {motive_2 : (a : Ctx) → Ty a → Sort u_1} →
    motive_1 Ctx.nil →
      ((Γ : Ctx) → (a : Ty Γ) → motive_1 Γ → motive_2 Γ a → motive_1 (Γ.snoc a)) →
        ((Γ : Ctx) → motive_1 Γ → motive_2 Γ (Ty.base Γ)) → (t : Ctx) → motive_1 t
-/
#guard_msgs in
#check @Ctx.rec

end PeelWholeProp

namespace PeelMutual

/-! Two propositions that leave together.  Neither is named by anything staying,
and each is named by the other, so the peel keeps them as the one mutual group
they were written as and their recursors share both motives. -/

mutual
inductive T : Type where
  | node : (cs : List T) → Ok cs → T
  | leaf : T
inductive Ok : List T → Prop where
  | nil  : Ok []
  | cons : (t : T) → (ts : List T) → Ok ts → Ok (t :: ts)
inductive A : T → Prop where
  | mk : (t : T) → (u : T) → B u → A t
inductive B : T → Prop where
  | mk : (t : T) → (u : T) → A u → B t
end

/--
info: @A.rec : ∀ {motive_1 : (a : T) → A a → Prop} {motive_2 : (a : T) → B a → Prop},
  (∀ (t u : T) (a : B u), motive_2 u a → motive_1 t ⋯) →
    (∀ (t u : T) (a : A u), motive_1 u a → motive_2 t ⋯) → ∀ {a : T} (t : A a), motive_1 a t
-/
#guard_msgs in
#check @A.rec

/--
info: @B.rec : ∀ {motive_1 : (a : T) → A a → Prop} {motive_2 : (a : T) → B a → Prop},
  (∀ (t u : T) (a : B u), motive_2 u a → motive_1 t ⋯) →
    (∀ (t u : T) (a : A u), motive_1 u a → motive_2 t ⋯) → ∀ {a : T} (t : B a), motive_2 a t
-/
#guard_msgs in
#check @B.rec

end PeelMutual

namespace PeelNotForProofs

/-! What must not peel.  A field whose type mentions the block but is itself a
*proof* travels erased and whole -- nothing has to be put back at a subtype for
it -- so `h : t = t` is no reason to take `Same` out of the block, and `Same`
keeps the recursion over the whole of it.  `Eq` is a nesting here, so the
recursor carries its motive too. -/

mutual
inductive T : Type where
  | node : (cs : List T) → Ok cs → T
  | leaf : T
inductive Ok : List T → Prop where
  | nil  : Ok []
  | cons : (t : T) → (ts : List T) → Ok ts → Ok (t :: ts)
inductive Same : T → Prop where
  | mk : (t : T) → (h : t = t) → Same t
end

/--
info: @Same.rec : ∀ {motive_1 : (a : List T) → Ok a → Prop} {motive_2 : (a : T) → Same a → Prop}
  {motive_3 : (t a : T) → t = a → Prop},
  motive_1 [] Ok.nil →
    (∀ (t : T) (ts : List T) (a : Ok ts), motive_1 ts a → motive_1 (t :: ts) ⋯) →
      (∀ (t : T) (h : t = t), motive_3 t t h → motive_2 t ⋯) →
        (∀ (t : T), motive_3 t t ⋯) → ∀ {a : T} (h : Same a), motive_2 a h
-/
#guard_msgs in
#check @Same.rec

end PeelNotForProofs

namespace PeelDeclined

/-! And what the peel offers to do and cannot.  `Deep` nests *itself*, under a
proposition-valued container, and a peeled member is declared straight at the
kernel, which does not denest.  The block is read a second time with no peel in
it, and comes out with every member present under the name it was written with.
`set_option trace.Mumi.indind true` is where the second reading says so.

`Deep` still has no recursor -- `u` is the field that started all this, and a
`Prop` constructor carries no well-formedness for a data field its conclusion
does not reach -- but that is `Deep`'s own loss.  `Ok` does not recurse into it,
so `Ok` is asked again on its own and keeps the recursor it can have. -/

inductive Wrap (p : Prop) : Prop where
  | mk : p → Wrap p

mutual
inductive T : Type where
  | node : (cs : List T) → Ok cs → T
  | leaf : T
inductive Ok : List T → Prop where
  | nil  : Ok []
  | cons : (t : T) → (ts : List T) → Ok ts → Ok (t :: ts)
inductive Deep : T → Prop where
  | mk : (t : T) → (u : T) → Wrap (Deep u) → Deep t
end

/-- info: Deep.mk : ∀ (t u : T), Wrap (Deep u) → Deep t -/
#guard_msgs in
#check @Deep.mk

/-- info: T.node : (cs : List T) → Ok cs → T -/
#guard_msgs in
#check @T.node

/--
info: @Ok.rec : ∀ {motive : (a : List T) → Ok a → Prop},
  motive [] Ok.nil →
    (∀ (t : T) (ts : List T) (a : Ok ts), motive ts a → motive (t :: ts) ⋯) → ∀ {a : List T} (h : Ok a), motive a h
-/
#guard_msgs in
#check @Ok.rec

/-- error: Unknown constant `PeelDeclined.Deep.rec` -/
#guard_msgs in
#check PeelDeclined.Deep.rec

end PeelDeclined

namespace PeelLeavesLean

/-! What the peel can hand back entirely.  The arity that named a sibling was
sometimes the peeled member's own, and then what stays is not
induction-inductive any more.  There is nothing left here for it to gain: the
recursion over the whole block needs a proposition indexed by a member to have
any content, and no such proposition remains.  So both halves go back to Lean --
the core first, since what left the block is stated over it -- and come out as
Lean's own inductives, with everything that implies. -/

mutual
inductive Tm : Type where
  | var : Nat → Tm
  | app : Tm → Tm → Tm
inductive Big : Tm → Prop where
  | mk : (t : Tm) → (extra : Tm) → Big t
end

/--
info: inductive PeelLeavesLean.Tm : Type
number of parameters: 0
constructors:
PeelLeavesLean.Tm.var : Nat → Tm
PeelLeavesLean.Tm.app : Tm → Tm → Tm
-/
#guard_msgs in
#print Tm

/--
info: @Tm.rec : {motive : Tm → Sort u_1} →
  ((a : Nat) → motive (Tm.var a)) → ((a a_1 : Tm) → motive a → motive a_1 → motive (a.app a_1)) → (t : Tm) → motive t
-/
#guard_msgs in
#check @Tm.rec

/--
info: @Big.rec : ∀ {a : Tm} {motive : Big a → Prop}, (∀ (extra : Tm), motive ⋯) → ∀ (t : Big a), motive t
-/
#guard_msgs in
#check @Big.rec

/-! `Tm` is an inductive and not a subtype, so it computes by `match` and the
value of a closed term is the value it should be. -/

def Tm.size : Tm → Nat
  | .var _ => 1
  | .app f a => f.size + a.size

example : (Tm.app (.var 0) (.var 1)).size = 2 := rfl

example (t : Tm) : Big t := by
  induction t with
  | var n => exact .mk _ (.var n)
  | app f a hf ha => exact .mk _ f

end PeelLeavesLean

namespace PeelLeavesNested

/-! And with a nesting in the core.  `T` reaches Lean whole, so it is Lean that
denests it: the recursor is stated over `List T` with a motive for the list, and
no copy of the list is made under a name of ours. -/

mutual
inductive T : Type where
  | node : List T → T
  | leaf : T
inductive Ok : T → Prop where
  | mk : (t : T) → (u : T) → Ok t
end

/--
info: @T.rec : {motive_1 : T → Sort u_1} →
  {motive_2 : List T → Sort u_1} →
    ((a : List T) → motive_2 a → motive_1 (T.node a)) →
      motive_1 T.leaf →
        motive_2 [] →
          ((head : T) → (tail : List T) → motive_1 head → motive_2 tail → motive_2 (head :: tail)) →
            (t : T) → motive_1 t
-/
#guard_msgs in
#check @T.rec

/--
info: @Ok.rec : ∀ {a : T} {motive : Ok a → Prop}, (∀ (u : T), motive ⋯) → ∀ (t : Ok a), motive t
-/
#guard_msgs in
#check @Ok.rec

/--
info: inductive PeelLeavesNested.T : Type
number of parameters: 0
constructors:
PeelLeavesNested.T.node : List T → T
PeelLeavesNested.T.leaf : T
-/
#guard_msgs in
#print T

end PeelLeavesNested

namespace PeelPropOnProp

/-! The other thing the erasure has nothing to offer.  A proposition indexed by
another proposition of the block is the block's own obstruction one level up --
erasure buys the one crossing from the data to the propositions, and the
propositions are a mutual inductive of their own, subject to the arity rule
again -- so such a member is refused outright.  Nothing else here is stated with
`Sub`, so it leaves instead, and outside the block `Ty Γ` is a proposition like
any other to be indexed by.

What stays is the entangled pair, with the recursion over both of them intact. -/

mutual
inductive Ctx : Type where
  | nil : Ctx
  | ext : (Γ : Ctx) → Ty Γ → Ctx
inductive Ty : Ctx → Prop where
  | base : Ty Γ
inductive Sub : (Γ : Ctx) → Ty Γ → Prop where
  | id : Sub Γ A
end

/--
info: inductive PeelPropOnProp.Sub : (Γ : Ctx) → Ty Γ → Prop
number of parameters: 0
constructors:
PeelPropOnProp.Sub.id : ∀ {Γ : Ctx} {A : Ty Γ}, Sub Γ A
-/
#guard_msgs in
#print Sub

/--
info: @Sub.rec : {motive : (Γ : Ctx) → (a : Ty Γ) → Sub Γ a → Sort u_1} →
  ({Γ : Ctx} → {A : Ty Γ} → motive Γ A ⋯) → {Γ : Ctx} → {a : Ty Γ} → (t : Sub Γ a) → motive Γ a t
-/
#guard_msgs in
#check @Sub.rec

/--
info: @Ctx.rec : {motive_1 : Ctx → Sort u_1} →
  {motive_2 : (a : Ctx) → motive_1 a → Ty a → Prop} →
    motive_1 Ctx.nil →
      ((Γ : Ctx) → (a : Ty Γ) → (Γ_ih : motive_1 Γ) → motive_2 Γ Γ_ih a → motive_1 (Γ.ext a)) →
        (∀ {Γ : Ctx} (Γ_ih : motive_1 Γ), motive_2 Γ Γ_ih ⋯) → (t : Ctx) → motive_1 t
-/
#guard_msgs in
#check @Ctx.rec

/-! `Sub` is indexed by a member that came back from the erasure as a subtype
and by one that stayed a proposition, and it is an inductive over both.  Its
recursor is the real one, so it eliminates into `Type` -- `Sub` has the one
constructor and no data in it -- and the iota rule holds by `rfl`. -/

noncomputable def Sub.tag {Γ : Ctx} {A : Ty Γ} (h : Sub Γ A) : Nat :=
  Sub.rec (motive := fun _ _ _ => Nat) 0 h

example {Γ : Ctx} {A : Ty Γ} : (Sub.id (Γ := Γ) (A := A)).tag = 0 := rfl

example (Γ : Ctx) (A : Ty Γ) (h : Sub Γ A) : h.tag = 0 := by
  induction h with
  | id => rfl

end PeelPropOnProp

namespace PeelAllProps

/-! And the block with no data in it at all.  There the erasure has nothing to
keep -- what it does is rebuild the data as a subtype of what it kept -- so such
a block is refused as well.  But a chain of propositions is not entangled, it is
merely written together, and every member after the first is a proposition
indexed by a proposition and so leaves on the rule above.  What is left is a
single ordinary `Prop`, which is Lean's to read, and the peeled members follow
it one group at a time. -/

mutual
inductive P : Prop where
  | mk : P
inductive Q : P → Prop where
  | mk : (h : P) → Q h
inductive R : (h : P) → Q h → Prop where
  | mk : (h : P) → (q : Q h) → R h q
end

/--
info: inductive PeelAllProps.P : Prop
number of parameters: 0
constructors:
PeelAllProps.P.mk : P
-/
#guard_msgs in
#print P

/-- info: R : (h : P) → Q h → Prop -/
#guard_msgs in
#check @R

/--
info: @R.rec : {h : P} → {a : Q h} → {motive : R h a → Sort u_1} → motive ⋯ → (t : R h a) → motive t
-/
#guard_msgs in
#check @R.rec

/-! Every one of them is an inductive, so `Q` and `R` recurse over their own
constructors and not over anything the others contributed. -/

theorem R.elim {h : P} {q : Q h} (r : R h q) : ∃ h' q', r = R.mk h' q' := by
  induction r with
  | mk => exact ⟨h, q, rfl⟩

end PeelAllProps

/-! ## A proposition whose constructor forgets one of its fields

A data field that a `Prop` constructor's conclusion does not reach is a field
with no well-formedness in reach to put it back at its subtype with: the
constructor carries no `_wf` of its own, and its own type says nothing about
where the field came from.  What rescues it is that such a field is exactly what
stops the proposition from being a subsingleton, so the recursor eliminates only
into `Prop` and every minor premise for it is a proof.  Two proofs of one
proposition are definitionally equal, so any element of the field's type serves
as well as the one that was meant, and the recursion is stated with whichever one
the search behind `Inhabited` turns up.
-/

namespace Forgotten

/-! `Big` is the member with the forgotten field: `hs` is a `List T` its
conclusion says nothing about.  `Watch` recurses into `Big`, so it would go down
with it.  Both keep their recursors, and so does `Ok`, which recurses into
nothing but itself.

None of the three leaves the block the way a peeled proposition does -- `Watch`
names `Big`, so they are still what the block is stated with, and they share the
one erased recursion. -/

mutual
inductive T : Type where
  | node : (cs : List T) → Ok cs → T
  | leaf : T
inductive Ok : List T → Prop where
  | nil  : Ok []
  | cons : (t : T) → (ts : List T) → Ok ts → Ok (t :: ts)
inductive Big : T → Prop where
  | node : (cs : List T) → (hs : List T) → (h : Ok cs) → Big (.node cs h)
  | leaf : Big .leaf
inductive Watch : T → Prop where
  | mk : (t : T) → (h : Big t) → Watch t
end

/--
info: @Ok.rec : ∀ {motive_1 : (a : List T) → Ok a → Prop} {motive_2 : (a : T) → Big a → Prop}
  {motive_3 : (a : T) → Watch a → Prop},
  motive_1 [] Ok.nil →
    (∀ (t : T) (ts : List T) (a : Ok ts), motive_1 ts a → motive_1 (t :: ts) ⋯) →
      (∀ (cs hs : List T) (h : Ok cs), motive_1 cs h → motive_2 (T.node cs h) ⋯) →
        motive_2 T.leaf Big.leaf →
          (∀ (t : T) (h : Big t), motive_2 t h → motive_3 t ⋯) → ∀ {a : List T} (h : Ok a), motive_1 a h
-/
#guard_msgs in
#check @Ok.rec

/-! `Big` and `Watch` get the recursor over the whole block, the one whose `Prop`
motives can mention the value the recursion produced at the data member.  Its
minor for `Big.node` binds `hs` and offers no `hs_ih`: that is the one thing the
forgotten field costs. -/

/--
info: @Big.rec : ∀ {motive_1 : T → Sort u_1} {motive_2 : (a : T) → motive_1 a → Big a → Prop}
  {motive_3 : (a : T) → motive_1 a → Watch a → Prop} {motive_4 : List T → Sort u_1}
  {motive_5 : (a : List T) → motive_4 a → Ok a → Prop}
  (node : (cs : List T) → (a : Ok cs) → (cs_ih : motive_4 cs) → motive_5 cs cs_ih a → motive_1 (T.node cs a))
  (leaf : motive_1 T.leaf)
  (node_1 :
    ∀ (cs hs : List T) (h : Ok cs) (cs_ih : motive_4 cs) (h_ih : motive_5 cs cs_ih h),
      motive_2 (T.node cs h) (node cs h cs_ih h_ih) ⋯)
  (leaf_1 : motive_2 T.leaf leaf Big.leaf)
  (mk : ∀ (t : T) (h : Big t) (t_ih : motive_1 t), motive_2 t t_ih h → motive_3 t t_ih ⋯) (nil : motive_4 [])
  (cons : (head : T) → (tail : List T) → motive_1 head → motive_4 tail → motive_4 (head :: tail))
  (nil_1 : motive_5 [] nil Ok.nil)
  (cons_1 :
    ∀ (t : T) (ts : List T) (a : Ok ts) (t_ih : motive_1 t) (ts_ih : motive_4 ts),
      motive_5 ts ts_ih a → motive_5 (t :: ts) (cons t ts t_ih ts_ih) ⋯)
  {a : T} (t : Big a), motive_2 a (T.rec node leaf node_1 leaf_1 mk nil cons nil_1 cons_1 a) t
-/
#guard_msgs in
#check @Big.rec

/--
info: @Watch.rec : ∀ {motive_1 : T → Sort u_1} {motive_2 : (a : T) → motive_1 a → Big a → Prop}
  {motive_3 : (a : T) → motive_1 a → Watch a → Prop} {motive_4 : List T → Sort u_1}
  {motive_5 : (a : List T) → motive_4 a → Ok a → Prop}
  (node : (cs : List T) → (a : Ok cs) → (cs_ih : motive_4 cs) → motive_5 cs cs_ih a → motive_1 (T.node cs a))
  (leaf : motive_1 T.leaf)
  (node_1 :
    ∀ (cs hs : List T) (h : Ok cs) (cs_ih : motive_4 cs) (h_ih : motive_5 cs cs_ih h),
      motive_2 (T.node cs h) (node cs h cs_ih h_ih) ⋯)
  (leaf_1 : motive_2 T.leaf leaf Big.leaf)
  (mk : ∀ (t : T) (h : Big t) (t_ih : motive_1 t), motive_2 t t_ih h → motive_3 t t_ih ⋯) (nil : motive_4 [])
  (cons : (head : T) → (tail : List T) → motive_1 head → motive_4 tail → motive_4 (head :: tail))
  (nil_1 : motive_5 [] nil Ok.nil)
  (cons_1 :
    ∀ (t : T) (ts : List T) (a : Ok ts) (t_ih : motive_1 t) (ts_ih : motive_4 ts),
      motive_5 ts ts_ih a → motive_5 (t :: ts) (cons t ts t_ih ts_ih) ⋯)
  {a : T} (t : Watch a), motive_3 a (T.rec node leaf node_1 leaf_1 mk nil cons nil_1 cons_1 a) t
-/
#guard_msgs in
#check @Watch.rec

/-! The data member and the constructors are untouched by any of this. -/

/--
info: @T.rec : {motive_1 : T → Sort u_1} →
  {motive_2 : (a : T) → motive_1 a → Big a → Prop} →
    {motive_3 : (a : T) → motive_1 a → Watch a → Prop} →
      {motive_4 : List T → Sort u_1} →
        {motive_5 : (a : List T) → motive_4 a → Ok a → Prop} →
          (node : (cs : List T) → (a : Ok cs) → (cs_ih : motive_4 cs) → motive_5 cs cs_ih a → motive_1 (T.node cs a)) →
            (leaf : motive_1 T.leaf) →
              (∀ (cs hs : List T) (h : Ok cs) (cs_ih : motive_4 cs) (h_ih : motive_5 cs cs_ih h),
                  motive_2 (T.node cs h) (node cs h cs_ih h_ih) ⋯) →
                motive_2 T.leaf leaf Big.leaf →
                  (∀ (t : T) (h : Big t) (t_ih : motive_1 t), motive_2 t t_ih h → motive_3 t t_ih ⋯) →
                    (nil : motive_4 []) →
                      (cons : (head : T) → (tail : List T) → motive_1 head → motive_4 tail → motive_4 (head :: tail)) →
                        motive_5 [] nil Ok.nil →
                          (∀ (t : T) (ts : List T) (a : Ok ts) (t_ih : motive_1 t) (ts_ih : motive_4 ts),
                              motive_5 ts ts_ih a → motive_5 (t :: ts) (cons t ts t_ih ts_ih) ⋯) →
                            (t : T) → motive_1 t
-/
#guard_msgs in
#check @T.rec

/-- info: Big.node : ∀ (cs hs : List T) (h : Ok cs), Big (T.node cs h) -/
#guard_msgs in
#check @Big.node

/-- info: Watch.mk : ∀ (t : T), Big t → Watch t -/
#guard_msgs in
#check @Watch.mk

/-! The recursors are the ones the tactics reach for, so `induction` and `cases`
work on the member with the forgotten field.  Both bind it -- it is a field like
any other to whoever is taking the constructor apart; what the recursion cannot
do is hand back an induction hypothesis at it, and neither does Lean's own
recursor for such a proposition. -/

theorem Big.elim {t : T} (h : Big t) : t = .leaf ∨ ∃ cs, ∃ hc : Ok cs, t = .node cs hc := by
  induction h with
  | node cs hs hc => exact .inr ⟨cs, hc, rfl⟩
  | leaf => exact .inl rfl

theorem Watch.toBig {t : T} (h : Watch t) : Big t := by
  induction h with
  | mk t hb => exact hb

/-! `Ok` keeps the recursion over the propositions alone, which is the one to
reach for when there is no data to produce -- and taken by hand it wants every
proposition's motive at once, which is what sharing one erased recursion means. -/

theorem Ok.elim {cs : List T} (h : Ok cs) : cs = [] ∨ cs ≠ [] :=
  Ok.rec (motive_2 := fun _ _ => True) (motive_3 := fun _ _ => True)
    (motive_1 := fun cs _ => cs = [] ∨ cs ≠ [])
    (.inl rfl) (fun t ts _ _ => .inr (by simp))
    (fun _ _ _ _ => trivial) trivial (fun _ _ _ => trivial) h

end Forgotten

/-! ## Injectivity of the constructors

A data member's constructors are `def`s, so nothing hands them the `inj`/`injEq`
pair a real inductive's constructors get, and without it `simp` knows nothing
whatever about a constructor equation.  It gets them here, stated the way
mainline states them: an equation per field, except that a field the resulting
type pins is shared between the two sides rather than compared, a proof field is
left out, and a field whose type moved with an earlier one is compared with
`HEq`.
-/

namespace Inj

mutual
inductive Ctx : Type where
  | nil  : Ctx
  | snoc : (Γ : Ctx) → Ty Γ → Ctx
inductive Ty : Ctx → Type where
  | base : (Γ : Ctx) → Ty Γ
  | pi   : (Γ : Ctx) → (A : Ty Γ) → Ty (Ctx.snoc Γ A) → Ty Γ
end

/--
info: Ctx.snoc.injEq : ∀ (Γ : Ctx) (a : Ty Γ) (Γ_1 : Ctx) (a_1 : Ty Γ_1), (Γ.snoc a = Γ_1.snoc a_1) = (Γ = Γ_1 ∧ a ≍ a_1)
-/
#guard_msgs in
#check @Ctx.snoc.injEq

-- `Γ` is `Ty.pi`'s conclusion index, so it is shared and only `A` is compared
/--
info: Ty.pi.injEq : ∀ (Γ : Ctx) (A : Ty Γ) (a : Ty (Γ.snoc A)) (A_1 : Ty Γ) (a_1 : Ty (Γ.snoc A_1)),
  (Ty.pi Γ A a = Ty.pi Γ A_1 a_1) = (A = A_1 ∧ a ≍ a_1)
-/
#guard_msgs in
#check @Ty.pi.injEq

/-- info: @Ctx.snoc.inj : ∀ {Γ : Ctx} {a : Ty Γ} {Γ_1 : Ctx} {a_1 : Ty Γ_1}, Γ.snoc a = Γ_1.snoc a_1 → Γ = Γ_1 ∧ a ≍ a_1 -/
#guard_msgs in
#check @Ctx.snoc.inj

/-- info: 'Inj.Ctx.snoc.injEq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Ctx.snoc.injEq

-- `injEq` is a `simp` lemma, so this is what it is for
example (Γ Δ : Ctx) (A : Ty Γ) (B : Ty Δ) (h : Ctx.snoc Γ A = Ctx.snoc Δ B) : Γ = Δ := by
  simp at h; exact h.1

example (Γ : Ctx) (A : Ty Γ) : (Ctx.snoc Γ A = Ctx.snoc Γ A) = True := by simp

end Inj

/-! An indexed block, with a field at neither `Prop` nor the block, and a
constructor whose last field sits at an index built out of two earlier ones. -/

namespace InjIndexed

mutual
inductive Ctx : Nat → Type where
  | nil  : Ctx 0
  | snoc : (n : Nat) → (Γ : Ctx n) → (tag : Bool) → Ty n Γ → Ctx (n + 1)
inductive Ty : (n : Nat) → Ctx n → Type where
  | base : (n : Nat) → (Γ : Ctx n) → Ty n Γ
  | pi   : (n : Nat) → (Γ : Ctx n) → (b : Bool) → (A : Ty n Γ) →
      Ty (n + 1) (Ctx.snoc n Γ b A) → Ty n Γ
end

-- `n` is pinned by the conclusion `Ctx (n + 1)`, so it is shared; `tag` is an
-- ordinary field and gets an ordinary equation
/--
info: Ctx.snoc.injEq : ∀ (n : Nat) (Γ : Ctx n) (tag : Bool) (a : Ty n Γ) (Γ_1 : Ctx n) (tag_1 : Bool) (a_1 : Ty n Γ_1),
  (Ctx.snoc n Γ tag a = Ctx.snoc n Γ_1 tag_1 a_1) = (Γ = Γ_1 ∧ tag = tag_1 ∧ a ≍ a_1)
-/
#guard_msgs in
#check @Ctx.snoc.injEq

/-- info: 'InjIndexed.Ctx.snoc.injEq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Ctx.snoc.injEq

-- `b` and `A` are what the last field's index is built out of, so both are
-- compared and the field itself only heterogeneously
/--
info: Ty.pi.injEq : ∀ (n : Nat) (Γ : Ctx n) (b : Bool) (A : Ty n Γ) (a : Ty (n + 1) (Ctx.snoc n Γ b A)) (b_1 : Bool)
  (A_1 : Ty n Γ) (a_1 : Ty (n + 1) (Ctx.snoc n Γ b_1 A_1)),
  (Ty.pi n Γ b A a = Ty.pi n Γ b_1 A_1 a_1) = (b = b_1 ∧ A = A_1 ∧ a ≍ a_1)
-/
#guard_msgs in
#check @Ty.pi.injEq

/-- info: 'InjIndexed.Ty.pi.injEq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Ty.pi.injEq

example (n : Nat) (Γ : Ctx n) (A B : Ty n Γ) (h : Ctx.snoc n Γ true A = Ctx.snoc n Γ false B) :
    False := by
  simp at h

end InjIndexed

/-! A constructor with one field to compare and one erased proof beside it.
Proof irrelevance settles the second, so there is a single conjunct and no
mention of the proof at all. -/

namespace InjProp

mutual
inductive Ctx : Type where
  | nil  : Ctx
  | snoc : (Γ : Ctx) → (h : Ok Γ) → Ctx
inductive Ok : Ctx → Prop where
  | nil : Ok .nil
end

/--
info: Ctx.snoc.injEq : ∀ (Γ : Ctx) (h : Ok Γ) (Γ_1 : Ctx) (h_1 : Ok Γ_1), (Γ.snoc h = Γ_1.snoc h_1) = (Γ = Γ_1)
-/
#guard_msgs in
#check @Ctx.snoc.injEq

/-- info: 'InjProp.Ctx.snoc.injEq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Ctx.snoc.injEq

end InjProp

/-! A field at a denested copy, where the equation `injection` leaves is between
the two sides' images in the copy.  What reads it back is `ofOrig_inj`, which the
bridge proves out of the round trip taken from the original. -/

#guard_msgs in
inductive InjNested.RVec where
  | tip
  | mk (n : Nat) (v : List (HWrap InjNested.RVec n)) : InjNested.RVec

/--
info: @InjNested.RVec.nested_List_1.toOrig_ofOrig : ∀ {n : Nat} (x : List (HWrap InjNested.RVec n)),
  (InjNested.RVec.nested_List_1.ofOrig x).toOrig = x
-/
#guard_msgs in
#check @InjNested.RVec.nested_List_1.toOrig_ofOrig

/--
info: @InjNested.RVec.nested_List_1.ofOrig_inj : ∀ {n : Nat} {a b : List (HWrap InjNested.RVec n)},
  InjNested.RVec.nested_List_1.ofOrig a = InjNested.RVec.nested_List_1.ofOrig b → a = b
-/
#guard_msgs in
#check @InjNested.RVec.nested_List_1.ofOrig_inj

-- `n` is no index here, so both copies of it are compared and the field itself
-- only heterogeneously; what the writer sees mentions the original `List`
/--
info: InjNested.RVec.mk.injEq : ∀ (n : Nat) (v : List (HWrap InjNested.RVec n)) (n_1 : Nat)
  (v_1 : List (HWrap InjNested.RVec n_1)), (InjNested.RVec.mk n v = InjNested.RVec.mk n_1 v_1) = (n = n_1 ∧ v ≍ v_1)
-/
#guard_msgs(whitespace := lax) in
#check @InjNested.RVec.mk.injEq

/-- info: 'InjNested.RVec.mk.injEq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms InjNested.RVec.mk.injEq

example (n : Nat) (v w : List (HWrap InjNested.RVec n)) (h : InjNested.RVec.mk n v = .mk n w) :
    v = w := by
  simp at h; exact h

/-! The round trip is proved at the copy's own constructors, so a field there at
*another* copy wants that one's round trip in turn -- which nothing the writer
declared ever asks for, and so is closed over.  An infinitary field wants
`funext` besides, and that is where `Quot.sound` comes in. -/

inductive InjNested.Pair (α β : Type) where
  | mk (a : α) (b : β)

inductive InjNested.PVec where
  | mk (n : Nat) (v : List (InjNested.Pair (HWrap InjNested.PVec n) (HWrap InjNested.PVec n)))

example (n : Nat) (v w : List (InjNested.Pair (HWrap InjNested.PVec n) (HWrap InjNested.PVec n)))
    (h : InjNested.PVec.mk n v = .mk n w) : v = w := by
  simp at h; exact h

inductive InjNested.FTree (α : Type) where
  | leaf
  | node (f : Nat → InjNested.FTree α) (a : α)

inductive InjNested.FVec where
  | mk (n : Nat) (v : InjNested.FTree (HWrap InjNested.FVec n))

example (n : Nat) (v w : InjNested.FTree (HWrap InjNested.FVec n))
    (h : InjNested.FVec.mk n v = .mk n w) : v = w := by
  simp at h; exact h

/-- info: 'InjNested.FVec.mk.injEq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms InjNested.FVec.mk.injEq

/-! Disjointness is the other half, and it is not a theorem anywhere: a member's
constructors are `def`s, so core's `reduceCtorEq` passes them by, and a lemma per
pair of them would be quadratically many declarations nobody wrote.  A simproc
says it instead, by pushing the equation through `Subtype.val` and asking the
pre-world's `noConfusion`. -/

-- injectivity was out of reach at this constructor and disjointness is not: what
-- the two sides reduce to is still two different pre-world constructors
example (n : Nat) (v : List (HWrap InjNested.RVec n)) :
    InjNested.RVec.tip ≠ InjNested.RVec.mk n v := by simp

namespace Disjoint

mutual
inductive Ctx : Type where
  | nil  : Ctx
  | snoc : (Γ : Ctx) → (h : Ok Γ) → Ctx
inductive Ok : Ctx → Prop where
  | nil  : Ok .nil
  | also : Ok .nil
end

theorem twoWays (Γ : Ctx) (h : Ok Γ) : Ctx.nil ≠ Ctx.snoc Γ h := by simp

/-- info: 'Disjoint.twoWays' depends on axioms: [propext] -/
#guard_msgs in
#print axioms twoWays

example (Γ : Ctx) (h : Ok Γ) : Ctx.snoc Γ h ≠ Ctx.nil := by simp

-- and in a hypothesis, where what it leaves behind is `False`
example (Γ : Ctx) (h : Ok Γ) (e : Ctx.nil = Ctx.snoc Γ h) : (0 : Nat) = 1 := by
  simp at e

-- a `Prop` member's constructors are proofs, and any two of them at one index are
-- equal.  The simproc must leave those alone, and does: what `Ok Γ` unfolds to is
-- the pre-world proposition itself rather than a subtype
example : Ok.nil = Ok.also := by simp

end Disjoint

/-! Indexed members, where the equation `noConfusion` is asked about carries the
indices too. -/

namespace DisjointIndexed

mutual
inductive Ctx : Nat → Type where
  | nil  : Ctx 0
  | dup  : (n : Nat) → Ctx n → Ctx (n + 1)
  | snoc : (n : Nat) → (Γ : Ctx n) → Ty n Γ → Ctx (n + 1)
inductive Ty : (n : Nat) → Ctx n → Type where
  | base : (n : Nat) → (Γ : Ctx n) → Ty n Γ
  | arr  : (n : Nat) → (Γ : Ctx n) → Ty n Γ → Ty n Γ → Ty n Γ
end

example (n : Nat) (Γ : Ctx n) (A : Ty n Γ) : Ctx.dup n Γ ≠ Ctx.snoc n Γ A := by simp

example (n : Nat) (Γ : Ctx n) (A B : Ty n Γ) : Ty.base n Γ ≠ Ty.arr n Γ A B := by simp

-- both halves at once: `simp` takes the outer equation apart and closes on the
-- inner one, which is between two different constructors
example (n : Nat) (Γ : Ctx n) (A B : Ty n Γ)
    (e : Ty.arr n Γ (Ty.base n Γ) A = Ty.arr n Γ (Ty.arr n Γ A B) B) : False := by
  simp at e

end DisjointIndexed
