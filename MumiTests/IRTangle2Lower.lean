import MumiTests.Spec.Harness

/-!
# A data decoder the rest of the block reads

In `IRTangle` the decoder `G : … → Nat` is only ever used by itself, so it
could have been a plain recursive definition after the fact.  Here a data
decoder feeds the rest of the block: `G` types a constructor field (`v : Fin
(G x c b e + 1)`), is the index a constructor of `W` sits at (`W.top : W x c b
e (G x c b e)`), and is what two type-valued decoders compute with -- `H` by a
function type over `Fin (G …)`, `K` by `Nat.rec` on it -- while `L` reads `G`
back out of a `W`.  This is the file at the written universe. `mumi_spec` checks every declaration
and equation; what follows is what that leaves out.
-/

set_option autoImplicit false
set_option mumi.mahlo true

namespace Tangle2L

mumi_spec (xfail := [sizeOf, matching])
mutual
inductive A : Type where
  | nil : A
  | cons (x : A) (c : F x) (b : B x c) (d : D x c b) : A
inductive B : (x : A) → F x → Type where
  | leaf (x : A) (c : F x) : B x c
  | node (x : A) (c : F x) (b : B x c) (e : D x c b)
      (f : (y : D x c b) → B (A.cons x c b y) (c, y)) : B x c
inductive E : (x : A) → (c : F x) → B x c → Type where
  | mk (x : A) (c : F x) (b : B x c) (d : D x c b) : E x c b
  | up (x : A) (c : F x) (b : B x c) (e : E x c b) (d : D x c b) (v : Fin (G x c b e + 1)) :
      E (A.cons x c b d) (c, d) (B.leaf (A.cons x c b d) (c, d))
inductive W : (x : A) → (c : F x) → (b : B x c) → (e : E x c b) → Nat → Type where
  | top (x : A) (c : F x) (b : B x c) (e : E x c b) : W x c b e (G x c b e)
  | step (x : A) (c : F x) (b : B x c) (e : E x c b) (n : Nat) (w : W x c b e n) (h : H x c b e) :
      W x c b e (n + 1)
def F : A → Type
  | .nil => PUnit
  | .cons x c b d => F x × D x c b
def D : (x : A) → (c : F x) → B x c → Type
  | _, _, .leaf x c => F x
  | _, _, .node x c b e f => (y : D x c b) → D (A.cons x c b y) (c, y) (f y)
def G : (x : A) → (c : F x) → (b : B x c) → E x c b → Nat
  | _, _, _, .mk x c b d => 0
  | _, _, _, .up x c b e d v => G x c b e + v.val + 1
def H : (x : A) → (c : F x) → (b : B x c) → E x c b → Type
  | _, _, _, .mk x c b d => PUnit
  | _, _, _, .up x c b e d v => Fin (G x c b e) → H x c b e
def K : (x : A) → (c : F x) → (b : B x c) → E x c b → Type
  | _, _, _, .mk x c b d => PUnit
  | _, _, _, .up x c b e d v => Nat.rec (motive := fun _ => Type) PUnit (fun _ T => Option T) (G x c b e)
def L : (x : A) → (c : F x) → (b : B x c) → (e : E x c b) → (n : Nat) → W x c b e n → Nat
  | _, _, _, _, _, .top x c b e => G x c b e
  | _, _, _, _, _, .step x c b e n w h => L x c b e n w + 1
end

/-! ## The recursors, and running -/

/-- Through the data: the number of `step`s above the `top`. -/
def height : (x : A) → (c : F x) → (b : B x c) → (e : E x c b) → (n : Nat) → W x c b e n → Nat :=
  fun _ _ _ _ _ w =>
    W.recD (motive := fun _ _ _ _ _ _ => Nat) w (fun _ _ _ _ => 0) (fun _ _ _ _ _ _ _ ih => ih + 1)

def d0 : D A.nil PUnit.unit (B.leaf A.nil PUnit.unit) := cast (D_leaf A.nil PUnit.unit).symm PUnit.unit
def e0 : E A.nil PUnit.unit (B.leaf A.nil PUnit.unit) := E.mk A.nil PUnit.unit (B.leaf A.nil PUnit.unit) d0
def h0 : H A.nil PUnit.unit (B.leaf A.nil PUnit.unit) e0 := cast (H_mk A.nil PUnit.unit (B.leaf A.nil PUnit.unit) d0).symm PUnit.unit
def w2 : W A.nil PUnit.unit (B.leaf A.nil PUnit.unit) e0 (G _ _ _ e0 + 1 + 1) :=
  W.step _ _ _ _ _ (W.step _ _ _ _ _ (W.top _ _ _ e0) h0) h0

/-- info: 2 -/
#guard_msgs in
#eval L _ _ _ _ _ w2

/-- info: 2 -/
#guard_msgs in
#eval height _ _ _ _ _ w2

-- a closed `E.up` sits at a nested index, where the kernel cannot see the
-- closed `F (A.cons …)` its index needs, so it is not run here; see the file
-- one universe up
/-- info: 'Tangle2L.height' depends on axioms: [IR.mahlo] -/
#guard_msgs in
#print axioms height

example (x : A) (c : F x) (b : B x c) (e : E x c b) (n : Nat) (w : W x c b e n) : True := by
  induction w with
  | top _ _ _ _ => trivial
  | step _ _ _ _ _ _ _ ih => trivial
example (x : A) (c : F x) (b : B x c) (e : E x c b) (n : Nat) (w : W x c b e n) : True := by
  cases w <;> trivial

end Tangle2L
