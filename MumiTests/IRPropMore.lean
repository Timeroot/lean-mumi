import MumiTests.Spec.Harness

/-!
# More `Prop` members: indexed by proofs, relating values, eliminating large

* A `Prop` member may be indexed by a proof of another, `Deep : (Γ : Ctx) → Ok Γ
  → Prop`; the proof is no data, as it is no data of a data member.
* A `Prop` member may relate several values of the block, `Conv : (A : Ty) →
  Tm A → Tm A → Prop`.
* A `Prop` member that Lean would let eliminate into any sort -- a syntactic
  subsingleton: one constructor, whose fields are proofs or appear in its
  indices, as `Acc` -- does so here too: Lean's kernel decides it, on a copy
  of the member declared on its own after the block.  Its recursor's rule is
  an equation.  A decoder may recurse over such a member, and only over such a
  one: over any other, equal proofs could decode differently.

`mumi_spec` checks each block, the `Prop` members' recursor into `Prop` or into
any sort as Lean's own rule decides; what follows is what that leaves out.
-/

set_option autoImplicit false

/-! ## A proposition indexed by a proof of another -/

namespace Deep
set_option mumi.mahlo false

mumi_spec
mutual
inductive Ctx : Type where
  | nil : Ctx
  | snoc (Γ : Ctx) (A : Ty Γ) (h : Ok Γ) : Ctx
inductive Ty : Ctx → Type where
  | base (Γ : Ctx) : Ty Γ
  | checked (Γ : Ctx) (h : Ok Γ) (s : Sound Γ h) : Ty Γ
inductive Ok : Ctx → Prop where
  | nil : Ok .nil
  | snoc (Γ : Ctx) (A : Ty Γ) (h : Ok Γ) : Ok (.snoc Γ A h)
inductive Sound : (Γ : Ctx) → Ok Γ → Prop where
  | nil : Sound .nil .nil
  | snoc (Γ : Ctx) (A : Ty Γ) (h : Ok Γ) (s : Sound Γ h) : Sound (.snoc Γ A h) (.snoc Γ A h)
def El : Ctx → Type
  | .nil => Unit
  | .snoc Γ A h => El Γ × Val Γ A
def Val : (Γ : Ctx) → Ty Γ → Type
  | _, .base Γ => Nat
  | _, .checked Γ h s => Unit
end

-- `Sound` is in the block: a type may be built under a proof of it.  Its proof
-- index is irrelevant
example (Γ : Ctx) (h h' : Ok Γ) : Sound Γ h = Sound Γ h' := rfl

-- the block's recursion: `Ok`'s motive and `Sound`'s take the value at their context
theorem sound (Γ : Ctx) (h : Ok Γ) : Sound Γ h :=
  Ok.rec (motive_1 := fun _ => Unit) (motive_2 := fun _ _ => Unit)
    (motive_3 := fun Γ _ h => Sound Γ h) (motive_4 := fun _ _ _ _ => True)
    () (fun _ _ _ _ _ _ => ()) (fun _ _ => ()) (fun _ _ _ _ _ _ => ())
    .nil (fun Γ A h _ _ ih => .snoc Γ A h ih) trivial (fun _ _ _ _ _ _ _ _ => trivial) h

theorem Sound.ok {Γ : Ctx} {h : Ok Γ} (s : Sound Γ h) : True := by
  cases s <;> trivial

end Deep

namespace DeepLower
set_option mumi.mahlo true
set_option maxRecDepth 8000

mumi_spec
mutual
inductive Ctx : Type where
  | nil : Ctx
  | snoc (Γ : Ctx) (A : Ty Γ) (h : Ok Γ) : Ctx
inductive Ty : Ctx → Type where
  | base (Γ : Ctx) : Ty Γ
  | checked (Γ : Ctx) (h : Ok Γ) (s : Sound Γ h) : Ty Γ
inductive Ok : Ctx → Prop where
  | nil : Ok .nil
  | snoc (Γ : Ctx) (A : Ty Γ) (h : Ok Γ) : Ok (.snoc Γ A h)
inductive Sound : (Γ : Ctx) → Ok Γ → Prop where
  | nil : Sound .nil .nil
  | snoc (Γ : Ctx) (A : Ty Γ) (h : Ok Γ) (s : Sound Γ h) : Sound (.snoc Γ A h) (.snoc Γ A h)
def El : Ctx → Type
  | .nil => Unit
  | .snoc Γ A h => El Γ × Val Γ A
def Val : (Γ : Ctx) → Ty Γ → Type
  | _, .base Γ => Nat
  | _, .checked Γ h s => Unit
end

example (Γ : Ctx) (h h' : Ok Γ) : Sound Γ h = Sound Γ h' := rfl

-- the block's recursion: `Ok`'s motive and `Sound`'s take the value at their context
theorem sound (Γ : Ctx) (h : Ok Γ) : Sound Γ h :=
  Ok.rec (motive_1 := fun _ => Unit) (motive_2 := fun _ _ => Unit)
    (motive_3 := fun Γ _ h => Sound Γ h) (motive_4 := fun _ _ _ _ => True)
    () (fun _ _ _ _ _ _ => ()) (fun _ _ => ()) (fun _ _ _ _ _ _ => ())
    .nil (fun Γ A h _ _ ih => .snoc Γ A h ih) trivial (fun _ _ _ _ _ _ _ _ => trivial) h

end DeepLower

/-! ## A proposition relating two values

`Conv A t t'` relates two terms, and a constructor of the data takes a proof of
it, which ties it into the block. -/

namespace Rel
set_option mumi.mahlo false

mumi_spec
mutual
inductive Ty : Type where
  | base : Ty
  | arr (A B : Ty) : Ty
inductive Tm : Ty → Type where
  | var (A : Ty) : Tm A
  | lam (A B : Ty) (t : Tm B) : Tm (.arr A B)
  | coe (A : Ty) (t t' : Tm A) (h : Conv A t t') : Tm A
inductive Conv : (A : Ty) → Tm A → Tm A → Prop where
  | refl (A : Ty) (t : Tm A) : Conv A t t
  | lam (A B : Ty) (t t' : Tm B) (h : Conv B t t') : Conv (.arr A B) (.lam A B t) (.lam A B t')
def Den : Ty → Type
  | .base => Nat
  | .arr A B => Den A → Den B
end

theorem Conv.symm' {A : Ty} {t t' : Tm A} (h : Conv A t t') : Conv A t' t :=
  Conv.rec (motive_1 := fun _ => Unit) (motive_2 := fun _ _ => Unit) (motive_3 := fun A _ t _ t' _ _ => Conv A t' t)
    () (fun _ _ _ _ => ()) (fun _ _ => ()) (fun _ _ _ _ _ _ => ()) (fun _ _ _ _ _ _ _ _ => ())
    (fun A t _ _ => .refl A t) (fun A B t t' _ _ _ _ _ ih => .lam A B t' t ih) h

def size {A : Ty} (t : Tm A) : Nat :=
  Tm.rec (motive_1 := fun _ => Unit) (motive_2 := fun _ _ => Nat) (motive_3 := fun _ _ _ _ _ _ _ => True)
    () (fun _ _ _ _ => ()) (fun _ _ => 1) (fun _ _ _ _ _ ih => ih + 1) (fun _ _ _ _ _ iht iht' _ => iht + iht')
    (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ _ _ => trivial) t
example (A : Ty) (t t' : Tm A) (h : Conv A t t') : size (Tm.coe A t t' h) = size t + size t' := rfl

end Rel

namespace RelLower
set_option mumi.mahlo true
set_option maxRecDepth 8000

mumi_spec
mutual
inductive Ty : Type where
  | base : Ty
  | arr (A B : Ty) : Ty
inductive Tm : Ty → Type where
  | var (A : Ty) : Tm A
  | lam (A B : Ty) (t : Tm B) : Tm (.arr A B)
  | coe (A : Ty) (t t' : Tm A) (h : Conv A t t') : Tm A
inductive Conv : (A : Ty) → Tm A → Tm A → Prop where
  | refl (A : Ty) (t : Tm A) : Conv A t t
  | lam (A B : Ty) (t t' : Tm B) (h : Conv B t t') : Conv (.arr A B) (.lam A B t) (.lam A B t')
def Den : Ty → Type
  | .base => Nat
  | .arr A B => Den A → Den B
end

theorem Conv.symm' {A : Ty} {t t' : Tm A} (h : Conv A t t') : Conv A t' t :=
  Conv.rec (motive_1 := fun _ => Unit) (motive_2 := fun _ _ => Unit) (motive_3 := fun A _ t _ t' _ _ => Conv A t' t)
    () (fun _ _ _ _ => ()) (fun _ _ => ()) (fun _ _ _ _ _ _ => ()) (fun _ _ _ _ _ _ _ _ => ())
    (fun A t _ _ => .refl A t) (fun A B t t' _ _ _ _ _ ih => .lam A B t' t ih) h

end RelLower

/-! ## Large elimination

`Pos a` says a code's decode is inhabited, and a code may be built only at such
a one.  It is a subsingleton -- one constructor; its field `a` is its index, `h`
a proof -- so it eliminates into any sort, as Lean's would. -/

namespace Large
set_option mumi.mahlo false

mumi_spec (xfail := [rec, recOn, casesOn, axioms])
mutual
inductive U : Type where
  | nat : U
  | pi (a : U) (b : El a → U) : U
  | some (a : U) (p : Pos a) : U
inductive Pos : U → Prop where
  | mk (a : U) (h : Nonempty (El a)) : Pos a
def El : U → Type
  | .nat => Nat
  | .pi a b => (x : El a) → El (b x)
  | .some a p => El a
def Wit : (a : U) → Pos a → Type
  | _, .mk a h => PLift (Nonempty (El a))
end

-- a definition by a large recursor is `noncomputable`, as one by `Acc.rec` is
noncomputable def tag (a : U) (p : Pos a) : Nat := Pos.rec (motive := fun _ _ => Nat) (fun _ _ => 7) p
example (a : U) (h : Nonempty (El a)) : tag a (.mk a h) = 7 := by
  simp only [tag, Pos.rec_mk]

end Large

namespace LargeLower
set_option mumi.mahlo true
set_option maxRecDepth 8000

mumi_spec (xfail := [rec, recOn, casesOn])
mutual
inductive U : Type where
  | nat : U
  | pi (a : U) (b : El a → U) : U
  | some (a : U) (p : Pos a) : U
inductive Pos : U → Prop where
  | mk (a : U) (h : Nonempty (El a)) : Pos a
def El : U → Type
  | .nat => Nat
  | .pi a b => (x : El a) → El (b x)
  | .some a p => El a
end

-- a definition by a large recursor is `noncomputable`, as one by `Acc.rec` is
noncomputable def tag (a : U) (p : Pos a) : Nat := Pos.rec (motive := fun _ _ => Nat) (fun _ _ => 7) p
example (a : U) (h : Nonempty (El a)) : tag a (.mk a h) = 7 := by
  simp only [tag, Pos.rec_mk]

end LargeLower

/-! ### Recursive, as `Acc`

`Fin' a` holds when every code below `a` holds it -- `Acc` of the subcode
relation.  Its recursion is well-founded recursion on codes, into any sort. -/

namespace LargeAcc
set_option mumi.mahlo false

mumi_spec (xfail := [rec, recOn, casesOn])
mutual
inductive U : Type where
  | nat : U
  | pi (a : U) (b : El a → U) : U
  | boxed (a : U) (h : Fin' a) : U
inductive Fin' : U → Prop where
  | intro (a : U) (below : ∀ x : El a, Fin' a) : Fin' a
def El : U → Type
  | .nat => Nat
  | .pi a b => (x : El a) → El (b x)
  | .boxed a h => El a
end

noncomputable def count (a : U) (h : Fin' a) : Nat := Fin'.rec (motive := fun _ _ => Nat) (fun _ _ _ => 0) h

end LargeAcc

/-! ### Not a subsingleton: no large elimination, no decoder -/

namespace NotLarge
set_option mumi.mahlo false

-- `Inh .nat` has a proof for each `n`: eliminating into `Nat` would tell them
-- apart, so its recursor is into `Prop`
mumi_spec
mutual
inductive U : Type where
  | nat : U
  | some (a : U) (p : Inh a) : U
inductive Inh : U → Prop where
  | nat (n : Nat) : Inh .nat
  | some (a : U) (p : Inh a) (h : Inh a) : Inh (.some a p)
def El : U → Type
  | .nat => Nat
  | .some a p => El a
end

end NotLarge

/--
error: A decoder may recurse over the `Prop` member `Inh` only if it is a subsingleton, as Lean would let it eliminate into any sort: one constructor, whose fields are proofs or appear in its indices. Over `Inh`, equal proofs could decode differently
-/
#guard_msgs in
set_option mumi.mahlo false in
mutual
inductive U : Type where
  | nat : U
  | some (a : U) (p : Inh a) : U
inductive Inh : U → Prop where
  | nat (n : Nat) : Inh .nat
  | some (a : U) (p : Inh a) : Inh (.some a p)
def El : U → Type
  | .nat => Nat
  | .some a p => El a
def Which : (a : U) → Inh a → Nat
  | _, .nat n => n
  | _, .some a p => 0
end

/-! ## Mixed: an implicit type parameter, a varying index, a proof index, nesting -/

namespace Mixed
set_option mumi.mahlo false

mumi_spec (simp := [Code.casesOn_list]) (xfail := [rec, recOn, casesOn])
mutual
inductive Code {σ : Type} (n : Nat) : Type where
  | base (s : σ) : Code n
  | succ (c : Code (n + 1)) : Code n
  | list (cs : List (Code 0)) : Code n
  | checked (c : Code 0) (h : Good c) : Code n
inductive Good {σ : Type} : Code (σ := σ) 0 → Prop where
  | base (s : σ) : Good (.base s)
def Den {σ : Type} (n : Nat) : Code (σ := σ) n → Type
  | .base s => Fin (n + 1)
  | .succ c => Den (n + 1) c
  | .list cs => Dens cs
  | .checked c h => Den 0 c
def Dens {σ : Type} : List (Code (σ := σ) 0) → Type
  | [] => Unit
  | c :: cs => Den 0 c × Dens cs
end

example (s : Bool) : Den 2 (Code.checked (.base s) (.base s)) = Den 0 (Code.base (σ := Bool) s) := rfl

end Mixed

-- a carrier indexed by a nested application would need its own API over the original
/--
error: IR prototype does not yet take a carrier indexed by a nested application, as `Good` by `List Code`
-/
#guard_msgs in
set_option mumi.mahlo false in
mutual
inductive Code : Type where
  | list (cs : List Code) (h : Good cs) : Code
inductive Good : List Code → Prop where
  | nil : Good []
def Den : Code → Type
  | .list cs h => Unit
end
