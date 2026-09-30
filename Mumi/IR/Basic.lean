module

public import Mumi.IR.Elimination

@[expose] public section

/-! Shared vocabulary for the experimental IR frontend. The upper representation
is a graph family; the lower representation uses the single `IR.mahlo` axiom.
Block-specific graphs, canonical predicates, and eliminators are generated.
-/

universe u v w

namespace Mumi.IR

abbrev Desc {S : Type u} (D : S → Type v) := _root_.IR.Desc D
abbrev Signature (S : Type u) (D : S → Type v) := _root_.IR.Signature S D
abbrev Args {S : Type u} {D : S → Type v} (X : S → Type u)
    (decode : (s : S) → X s → D s) {s : S} (d : Desc D s) := _root_.IR.Desc.Args X decode d

namespace Graph

def Carrier {D : Type u} (G : D → Type v) := (d : D) × G d
def decode {D : Type u} {G : D → Type v} (a : Carrier G) : D := a.1
def pack {D : Type u} {G : D → Type v} (d : D) (g : G d) : Carrier G := ⟨d, g⟩

@[elab_as_elim] def induction {D : Type u} {G : D → Type v}
    {C : Carrier G → Sort w} (f : ∀ d g, C (pack d g)) (a : Carrier G) : C a :=
  f a.1 a.2

end Graph

variable {S : Type u} {D : S → Type (u+1)} (sig : Signature S D)

noncomputable def model : _root_.IR.StageModel sig := _root_.IR.model sig
noncomputable def Raw : S → Type u := _root_.IR.Raw.U sig

/-! Every primitive has a run-time implementation on `IR.Stage.Runtime`, so
that what a lower block generates compiles: a value is its arguments with its
outputs, a field is the same object, and the reflection axiom is never run. -/

unsafe def decodeImpl (s : S) (a : Raw sig s) : D s :=
  (unsafeCast a : _root_.IR.Stage.Runtime (D s)).value

@[implemented_by decodeImpl]
def decode : (s : S) → Raw sig s → D s := _root_.IR.Raw.decode sig

unsafe def rollImpl (s : S) (args : _root_.IR.Desc.Args (Raw sig) (decode sig) (sig s)) : Raw sig s :=
  unsafeCast (_root_.IR.Stage.Runtime.mk (β := D s) (unsafeCast args)
    (_root_.IR.Desc.eval (Raw sig) (decode sig) (sig s) args))

@[implemented_by rollImpl]
def roll (s : S) (args : _root_.IR.Desc.Args (Raw sig) (decode sig) (sig s)) : Raw sig s :=
  _root_.IR.Raw.roll sig s args

unsafe def viewImpl (s : S) (a : Raw sig s) : _root_.IR.Desc.Args (Raw sig) (decode sig) (sig s) :=
  unsafeCast (unsafeCast a : _root_.IR.Stage.Runtime (D s)).args

@[implemented_by viewImpl]
def view (s : S) (a : Raw sig s) :
    _root_.IR.Desc.Args (Raw sig) (decode sig) (sig s) := _root_.IR.Raw.view sig s a

unsafe def inductionImpl {C : (s : S) → Raw sig s → Sort w}
    (step : _root_.IR.Stage.Step sig (model sig).lt C) (s : S) (a : Raw sig s) : C s a :=
  unsafeCast (step (unsafeCast ()) (unsafeCast ()) s (unsafeCast (viewImpl sig s a))
    (fun t p => unsafeCast (inductionImpl step t (unsafeCast p))))

@[elab_as_elim, implemented_by inductionImpl]
def induction {C : (s : S) → Raw sig s → Sort w}
    (step : _root_.IR.Stage.Step sig (model sig).lt C) (s : S) (a : Raw sig s) : C s a :=
  _root_.IR.Raw.induction sig step s a

variable {I : Type u} (r : I → I → Prop)

unsafe def packImpl (i : I) (children : ∀ j, r j i → Acc r j) (s : S)
    (args : Args (_root_.IR.Stage.Pred r i (fun j h => _root_.IR.Stage.build sig r j (children j h)))
      (_root_.IR.Stage.predDecode r) (sig s)) : _root_.IR.Stage.U sig r s :=
  -- the fields are values, and read as such
  unsafeCast (_root_.IR.Stage.Runtime.mk (β := D s) (unsafeCast args)
    (_root_.IR.Desc.eval (Raw sig) (decode sig) (sig s) (unsafeCast args)))

@[implemented_by packImpl]
def pack (i : I) (children : ∀ j, r j i → Acc r j) (s : S)
    (args : Args (_root_.IR.Stage.Pred r i (fun j h => _root_.IR.Stage.build sig r j (children j h)))
      (_root_.IR.Stage.predDecode r) (sig s)) : _root_.IR.Stage.U sig r s :=
  _root_.IR.Stage.pack sig r i children s args

unsafe def raiseImpl {i : I} {children : ∀ j, r j i → Acc r j} (s : S)
    (p : _root_.IR.Stage.Pred r i (fun j h => _root_.IR.Stage.build sig r j (children j h)) s) :
    _root_.IR.Stage.U sig r s := unsafeCast p

@[implemented_by raiseImpl]
def raise {i : I} {children : ∀ j, r j i → Acc r j} (s : S)
    (p : _root_.IR.Stage.Pred r i (fun j h => _root_.IR.Stage.build sig r j (children j h)) s) :
    _root_.IR.Stage.U sig r s := _root_.IR.Stage.raise sig r s p

end Mumi.IR
