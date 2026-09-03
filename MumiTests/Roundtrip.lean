/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import Mumi
import MumiTests.NestedIndInd

/-!
# Initiality: the predicates really are pinned down

A lowered block hands out one recursor per member, and all of them are over the same
motives: a `Sort u` motive for each data member, and for each predicate a `Prop`
motive that also takes the *value* the data motive produced at the data index it is
about.  That is the induction-inductive eliminator, and it is what makes a proof by
`Fresh.rec` able to say something about a function defined by `Ctx.rec`.

The worry this file answers is that a lowering might constrain the predicates only
*from below* -- the introduction rules say what is in them, and if nothing eliminates
them then `fun _ _ => True` or a greatest fixed point would satisfy the same
specification, and two copies of the same block written under different names could
fail to be isomorphic.  Everything below is built from `Ctx.rec` and `Fresh.rec`
alone -- no `_pre`, no subtype, no internal name.

* `Ctx.toCtx'_toCtx` / `Ctx'.toCtx_toCtx'` -- two renamed copies of one
  induction-inductive block are isomorphic, and
* `fresh_iff` / `fresh'_iff` -- the isomorphism carries the predicates both ways.
* `fresh_iff_not_mem` -- the predicate is *exactly* non-membership, so it is the least
  fixed point and not the greatest, and certainly not trivial.

The second half does the same for the denested nested type of `MumiTests.NestedIndInd`,
where the predicates are Lean's own inductives at a new parameter.
-/

namespace MumiTests.Roundtrip

/-! ## An induction-inductive block, and a renaming of it -/

mutual
inductive Ctx : Type where
  | nil
  | snoc (Γ : Ctx) (x : String) (h : Fresh x Γ)
inductive Fresh : String → Ctx → Prop where
  | nil (x : String) : Fresh x .nil
  | snoc (x y : String) (Γ : Ctx) (h : Fresh y Γ) (hne : x ≠ y) (hΓ : Fresh x Γ) :
      Fresh x (.snoc Γ y h)
end

mutual
inductive Ctx' : Type where
  | nil
  | snoc (Δ : Ctx') (a : String) (p : Fresh' a Δ)
inductive Fresh' : String → Ctx' → Prop where
  | nil (a : String) : Fresh' a .nil
  | snoc (a b : String) (Δ : Ctx') (p : Fresh' b Δ) (hne : a ≠ b) (pΔ : Fresh' a Δ) :
      Fresh' a (.snoc Δ b p)
end

/-! ## Driving the recursor

One recursor serves the whole block, so every use of `Ctx.rec` supplies a motive for
`Ctx` *and* a motive for `Fresh`.  Alongside it the block gets `Ctx.recD` and
`Fresh.recP`, which fix the motive that is not interesting -- `True` for the
proposition, `Unit` for the data -- and the rest of the file recurses with those.

They are also what `induction` drives, and `Ctx.recD` is registered as the default
eliminator for `Ctx`.  `Ctx.rec` could not be: nothing in the goal determines the
`Fresh` motive.  Nor could `Fresh.rec`, because Lean reads an eliminator's targets
only up to the first argument of the motive that is not a local variable, and a
predicate motive's third argument is the value the data motive produced.
`Fresh.recP` has that argument already discharged, so its targets are the three Lean
expects.
-/

/--
info: @Ctx.recD : {motive : Ctx → Sort u_1} →
  motive Ctx.nil → ((Γ : Ctx) → (x : String) → (h : Fresh x Γ) → motive Γ → motive (Γ.snoc x h)) → (t : Ctx) → motive t
-/
#guard_msgs in
#check @Ctx.recD

/--
info: @Fresh.recP : ∀ {motive : (a : String) → (a_1 : Ctx) → Fresh a a_1 → Prop},
  (∀ (x : String), motive x Ctx.nil ⋯) →
    (∀ (x y : String) (Γ : Ctx) (h : Fresh y Γ) (hne : x ≠ y) (hΓ : Fresh x Γ),
        motive y Γ h → motive x Γ hΓ → motive x (Γ.snoc y h) ⋯) →
      ∀ {a : String} {a_1 : Ctx} (h : Fresh a a_1), motive a a_1 h
-/
#guard_msgs in
#check @Fresh.recP

/-! ## No confusion

The members of a lowered block are `def`s, so what tells two constructors apart
is a simproc rather than a `noConfusion`, and the `injEq` they do get is proved
through the subtype rather than out of the block's own constants.  Both come out
of `Ctx.rec` by hand here, which is what this file is for: its iota rule holds by
`rfl`, and that is all either proof needs.
-/

private def Ctx.head? : Ctx → Option String :=
  Ctx.recD (motive := fun _ => Option String) none (fun _ x _ _ => some x)
private def Ctx.tail : Ctx → Ctx :=
  Ctx.recD (motive := fun _ => Ctx) Ctx.nil (fun Γ₀ _ _ _ => Γ₀)

theorem Ctx.nil_ne_snoc (Γ x h) : Ctx.nil ≠ Ctx.snoc Γ x h := by
  intro e
  have : (none : Option String) = some x := congrArg Ctx.head? e
  nomatch this

theorem Ctx.snoc_inj {Γ₁ Γ₂ x₁ x₂ h₁ h₂} (e : Ctx.snoc Γ₁ x₁ h₁ = Ctx.snoc Γ₂ x₂ h₂) :
    Γ₁ = Γ₂ ∧ x₁ = x₂ :=
  ⟨congrArg Ctx.tail e, Option.some_inj.mp (show some x₁ = some x₂ from congrArg Ctx.head? e)⟩

theorem Ctx.snoc_congr {Γ₁ Γ₂ : Ctx} (e : Γ₁ = Γ₂) (x) (h₁ : Fresh x Γ₁) (h₂ : Fresh x Γ₂) :
    Ctx.snoc Γ₁ x h₁ = Ctx.snoc Γ₂ x h₂ := by
  subst e; rfl

private def Ctx'.head? : Ctx' → Option String :=
  Ctx'.recD (motive := fun _ => Option String) none (fun _ a _ _ => some a)
private def Ctx'.tail : Ctx' → Ctx' :=
  Ctx'.recD (motive := fun _ => Ctx') Ctx'.nil (fun Δ₀ _ _ _ => Δ₀)

theorem Ctx'.nil_ne_snoc (Δ a p) : Ctx'.nil ≠ Ctx'.snoc Δ a p := by
  intro e
  have : (none : Option String) = some a := congrArg Ctx'.head? e
  nomatch this

theorem Ctx'.snoc_inj {Δ₁ Δ₂ a₁ a₂ p₁ p₂} (e : Ctx'.snoc Δ₁ a₁ p₁ = Ctx'.snoc Δ₂ a₂ p₂) :
    Δ₁ = Δ₂ ∧ a₁ = a₂ :=
  ⟨congrArg Ctx'.tail e, Option.some_inj.mp (show some a₁ = some a₂ from congrArg Ctx'.head? e)⟩

theorem Ctx'.snoc_congr {Δ₁ Δ₂ : Ctx'} (e : Δ₁ = Δ₂) (a) (p₁ : Fresh' a Δ₁) (p₂ : Fresh' a Δ₂) :
    Ctx'.snoc Δ₁ a p₁ = Ctx'.snoc Δ₂ a p₂ := by
  subst e; rfl

/-! ## Inversion, out of the `Prop` recursor -/

theorem Fresh.snoc_inv {y : String} {Δ : Ctx} (hy : Fresh y Δ) :
    ∀ (Γ : Ctx) (x : String) (h : Fresh x Γ), Δ = Ctx.snoc Γ x h → y ≠ x ∧ Fresh y Γ := by
  induction hy using Fresh.recP with
  | nil z => intro Γ x h e; exact absurd e (Ctx.nil_ne_snoc Γ x h)
  | snoc z w Γ₀ h₀ hne hΓ _ _ =>
    intro Γ x h e
    obtain ⟨eΓ, ex⟩ := Ctx.snoc_inj e
    subst eΓ; subst ex
    exact ⟨hne, hΓ⟩

theorem Fresh.snoc_inv' {y x : String} {Γ : Ctx} {h : Fresh x Γ}
    (hy : Fresh y (Ctx.snoc Γ x h)) : y ≠ x ∧ Fresh y Γ :=
  hy.snoc_inv Γ x h rfl

theorem Fresh'.snoc_inv {b : String} {Δ : Ctx'} (pb : Fresh' b Δ) :
    ∀ (Δ₀ : Ctx') (a : String) (p : Fresh' a Δ₀), Δ = Ctx'.snoc Δ₀ a p → b ≠ a ∧ Fresh' b Δ₀ := by
  induction pb using Fresh'.recP with
  | nil c => intro Δ₀ a p e; exact absurd e (Ctx'.nil_ne_snoc Δ₀ a p)
  | snoc c d Δ₀ p₀ hne pΔ _ _ =>
    intro Δ₀' a p e
    obtain ⟨eΔ, ea⟩ := Ctx'.snoc_inj e
    subst eΔ; subst ea
    exact ⟨hne, pΔ⟩

theorem Fresh'.snoc_inv' {b a : String} {Δ : Ctx'} {p : Fresh' a Δ}
    (pb : Fresh' b (Ctx'.snoc Δ a p)) : b ≠ a ∧ Fresh' b Δ :=
  pb.snoc_inv Δ a p rfl

/-! ## The morphism

`Ctx.rec`'s predicate motive would do this in one pass -- it is handed the data
motive's value at the index, which is exactly the `Δ` the map on proofs has to land
in.  It is written the other way here on purpose, as a subtype in the data motive, to
show the file does not depend on the predicate motive existing; `fresh_iff_not_mem`
below is the one that does.
-/

private def toC' (Γ : Ctx) : { Δ : Ctx' // ∀ x, Fresh x Γ → Fresh' x Δ } :=
  Ctx.recD (motive := fun Γ => { Δ : Ctx' // ∀ x, Fresh x Γ → Fresh' x Δ })
    ⟨.nil, fun x _ => .nil x⟩
    (fun _Γ x h ih =>
      ⟨.snoc ih.val x (ih.property x h), fun y hy =>
        have inv := Fresh.snoc_inv' hy
        .snoc y x ih.val (ih.property x h) inv.1 (ih.property y inv.2)⟩)
    Γ

def Ctx.toCtx' (Γ : Ctx) : Ctx' := (toC' Γ).val
theorem Fresh.toFresh' {x Γ} (h : Fresh x Γ) : Fresh' x Γ.toCtx' := (toC' Γ).property x h

private def toC (Δ : Ctx') : { Γ : Ctx // ∀ a, Fresh' a Δ → Fresh a Γ } :=
  Ctx'.recD (motive := fun Δ => { Γ : Ctx // ∀ a, Fresh' a Δ → Fresh a Γ })
    ⟨.nil, fun a _ => .nil a⟩
    (fun _Δ a p ih =>
      ⟨.snoc ih.val a (ih.property a p), fun b pb =>
        have inv := Fresh'.snoc_inv' pb
        .snoc b a ih.val (ih.property a p) inv.1 (ih.property b inv.2)⟩)
    Δ

def Ctx'.toCtx (Δ : Ctx') : Ctx := (toC Δ).val
theorem Fresh'.toFresh {a Δ} (p : Fresh' a Δ) : Fresh a Δ.toCtx := (toC Δ).property a p

-- the morphism commutes with the constructors definitionally
example : Ctx.nil.toCtx' = Ctx'.nil := rfl
example (Γ x h) : (Ctx.snoc Γ x h).toCtx' = Ctx'.snoc Γ.toCtx' x h.toFresh' := rfl

/-! ## The roundtrip -/

theorem Ctx.toCtx'_toCtx (Γ : Ctx) : Γ.toCtx'.toCtx = Γ := by
  induction Γ using Ctx.recD with
  | nil => rfl
  | snoc Γ x h ih => exact Ctx.snoc_congr ih x h.toFresh'.toFresh h

theorem Ctx'.toCtx_toCtx' (Δ : Ctx') : Δ.toCtx.toCtx' = Δ := by
  induction Δ using Ctx'.recD with
  | nil => rfl
  | snoc Δ a p ih => exact Ctx'.snoc_congr ih a p.toFresh.toFresh' p

/-- The predicates correspond, in both directions. -/
theorem fresh_iff (x : String) (Γ : Ctx) : Fresh x Γ ↔ Fresh' x Γ.toCtx' :=
  ⟨Fresh.toFresh', fun p => Γ.toCtx'_toCtx ▸ p.toFresh⟩

theorem fresh'_iff (a : String) (Δ : Ctx') : Fresh' a Δ ↔ Fresh a Δ.toCtx :=
  ⟨Fresh'.toFresh, fun h => Δ.toCtx_toCtx' ▸ h.toFresh'⟩

/-! ## The predicate is the least fixed point, not the greatest -/

def Ctx.names : Ctx → List String :=
  Ctx.recD (motive := fun _ => List String) [] (fun _ x _ ih => x :: ih)

theorem Ctx.names_nil : Ctx.nil.names = [] := rfl
theorem Ctx.names_snoc (Γ x h) : (Ctx.snoc Γ x h).names = x :: Γ.names := rfl

/-- `Fresh` is *exactly* non-membership.  Read left to right this is the induction that
only the least fixed point admits; a `Fresh` interpreted trivially, or coinductively,
would not satisfy it. -/
theorem fresh_iff_not_mem (x : String) (Γ : Ctx) : Fresh x Γ ↔ x ∉ Γ.names := by
  constructor
  · intro h
    induction h using Fresh.recP with
    | nil z => simp [Ctx.names_nil]
    | snoc z w Γ₀ h₀ hne hΓ _ ih => simp [Ctx.names_snoc, hne, ih]
  · induction Γ using Ctx.recD with
    | nil => intro _; exact .nil x
    | snoc Γ y h ih =>
      intro hm
      rw [Ctx.names_snoc, List.mem_cons] at hm
      exact .snoc x y Γ h (fun e => hm (Or.inl e)) (ih (fun e => hm (Or.inr e)))

example : ¬ Fresh "a" (Ctx.snoc Ctx.nil "a" (Fresh.nil "a")) := by
  simp [fresh_iff_not_mem, Ctx.names_snoc, Ctx.names_nil]

def Ctx'.names : Ctx' → List String :=
  Ctx'.recD (motive := fun _ => List String) [] (fun _ a _ ih => a :: ih)

theorem names_toCtx' (Γ : Ctx) : Γ.toCtx'.names = Γ.names := by
  induction Γ using Ctx.recD with
  | nil => rfl
  | snoc Γ x h ih => show x :: Γ.toCtx'.names = x :: Γ.names; rw [ih]

end MumiTests.Roundtrip

/-! ## The same, for the denested nested type

`RecWFTree` denests into copies, but its recursor is stated over the types the
block was written with: motives for `RecWFTree`, `WFTree RecWFTree` and
`Tree RecWFTree`, and motives for `Tree.WF` and `Tree.WFWith` that each take the
value the data motive produced.  So the same two questions can be asked of it as
of `Ctx`, and answered the same way -- out of the recursor alone, with no copy
name anywhere below.

That the predicate motives are there is the whole point.  Without them a
recursion can rebuild the tree but cannot carry its well-formedness across, and
the map to a second copy of the block is not merely hard to write but
impossible: the residual obligation is false.  `MumiTests.NestedIndInd` shows
the rebuild; this shows the isomorphism.

`Tree`, `Tree.WFWith`, `Tree.WF` and `WFTree` are ordinary Lean inductives
declared before the block, so Lean's own recursors apply at `α := RecWFTree`
and are used freely.
-/

namespace RecWFTree

noncomputable def Tree.size {α : Type u} : Tree α → Nat :=
  fun t => Tree.rec (motive := fun _ => Nat) 0 (fun _ _ _ _ nl nr => nl + nr + 1) t

/-- Lean's own recursor for the predicate, used at the block's own type. -/
theorem wfWith_size {t : Tree RecWFTree} {l : List Nat} (h : Tree.WFWith RecWFTree t l) :
    Tree.size t = l.length := by
  induction h with
  | empty => rfl
  | node key value tl tr hl hr hl' hr' ihl ihr =>
    show Tree.size tl + Tree.size tr + 1 = _
    simp [ihl, ihr, List.length_append]
    omega

/-- The predicate is the least fixed point and not the trivial one: a tree whose
left child holds a larger key is not well-formed. -/
example : ¬ Tree.WF RecWFTree
    (.node 0 bottom (.node 5 bottom .empty .empty) .empty) := by
  rintro ⟨l, t, hw⟩
  cases hw with
  | node k v tl tr hl hr hl' hr' =>
    cases hl with
    | node k2 v2 tl2 tr2 hl2 hr2 hl2' hr2' =>
      cases hl2; cases hr2
      exact absurd (hl' 5 (by simp)) (by omega)

end RecWFTree

/-! ## A second copy of the block, and the map both ways

Written out again under other names, so that the two blocks share nothing but
their shape.  The maps are one recursor application each: `motive_4` and
`motive_5` say that the rebuilt tree is well-formed in the *other* copy, and the
`Tree.WF` and `Tree.WFWith` minors are what discharge that.  This is the
definition that cannot be written when the recursor stops at the data members.
-/

namespace Copy

inductive Tree (α : Type u) where
  | empty
  | node (key : Nat) (value : α) (l r : Tree α)

inductive Tree.WFWith (α : Type u) : Tree α → List Nat → Prop where
  | empty : Tree.WFWith α .empty []
  | node {llist rlist} (key : Nat) (value : α) (l r : Tree α)
      (hl : Tree.WFWith α l llist) (hr : Tree.WFWith α r rlist)
      (hl' : ∀ a ∈ llist, a < key) (hr' : ∀ a ∈ rlist, key < a) :
      Tree.WFWith α (.node key value l r) (llist ++ key :: rlist)

inductive Tree.WF (α : Type u) : Tree α → Prop where
  | intro (l : List Nat) (t : Tree α) (h : Tree.WFWith α t l) : Tree.WF α t

inductive WFTree (α : Type u) : Type u where
  | mk (x : Tree α) (h : x.WF)

inductive RecWFTree where
  | mk (x : WFTree RecWFTree)

end Copy

/-- Both maps are named at the root: inside `namespace Copy.RecWFTree` the
return type `RecWFTree` would resolve to `Copy.RecWFTree` and the map would
quietly become an endomap. -/
noncomputable def toCopy : RecWFTree → Copy.RecWFTree :=
  RecWFTree.rec
    (motive_1 := fun _ => Copy.RecWFTree)
    (motive_2 := fun _ => Copy.WFTree Copy.RecWFTree)
    (motive_3 := fun _ => Copy.Tree Copy.RecWFTree)
    (motive_4 := fun _ ih _ => Copy.Tree.WF Copy.RecWFTree ih)
    (motive_5 := fun _ l ih _ => Copy.Tree.WFWith Copy.RecWFTree ih l)
    (fun _ ih => .mk ih)
    (fun _ _ ih hih => .mk ih hih)
    .empty
    (fun key _ _ _ vih lih rih => .node key vih lih rih)
    (fun l _ _ tih hih => .intro l tih hih)
    .empty
    (fun key _ _ _ _ _ hl' hr' vih lih rih ihl ihr =>
      .node key vih lih rih ihl ihr hl' hr')

noncomputable def ofCopy : Copy.RecWFTree → RecWFTree :=
  Copy.RecWFTree.rec
    (motive_1 := fun _ => RecWFTree)
    (motive_2 := fun _ => WFTree RecWFTree)
    (motive_3 := fun _ => Tree RecWFTree)
    (motive_4 := fun _ ih _ => Tree.WF RecWFTree ih)
    (motive_5 := fun _ l ih _ => Tree.WFWith RecWFTree ih l)
    (fun _ ih => .mk ih)
    (fun _ _ ih hih => .mk ih hih)
    .empty
    (fun key _ _ _ vih lih rih => .node key vih lih rih)
    (fun l _ _ tih hih => .intro l tih hih)
    .empty
    (fun key _ _ _ _ _ hl' hr' vih lih rih ihl ihr =>
      .node key vih lih rih ihl ihr hl' hr')

/-- info: toCopy : RecWFTree → Copy.RecWFTree -/
#guard_msgs in
#check @toCopy

/-- info: ofCopy : Copy.RecWFTree → RecWFTree -/
#guard_msgs in
#check @ofCopy

-- and the round trip is definitional, so the two blocks really are the same one
open RecWFTree in
example : ofCopy (toCopy bottom) = bottom := rfl

open RecWFTree in
example : ofCopy (toCopy (wrap bottom)) = wrap bottom := rfl

open RecWFTree in
example : ofCopy (toCopy (wrap (wrap bottom))) = wrap (wrap bottom) := rfl

/-- info: 'toCopy' does not depend on any axioms -/
#guard_msgs in
#print axioms toCopy

/-- info: 'ofCopy' does not depend on any axioms -/
#guard_msgs in
#print axioms ofCopy
