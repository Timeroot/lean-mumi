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
noncomputable def decode : (s : S) → Raw sig s → D s := _root_.IR.Raw.decode sig
noncomputable def roll (s : S)
    (args : _root_.IR.Desc.Args (Raw sig) (decode sig) (sig s)) : Raw sig s :=
  _root_.IR.Raw.roll sig s args
noncomputable def view (s : S) (a : Raw sig s) :
    _root_.IR.Desc.Args (Raw sig) (decode sig) (sig s) := _root_.IR.Raw.view sig s a

@[elab_as_elim] noncomputable def induction {C : (s : S) → Raw sig s → Sort w}
    (step : _root_.IR.Stage.Step sig (model sig).lt C) (s : S) (a : Raw sig s) : C s a :=
  _root_.IR.Raw.induction sig step s a

variable {I : Type u} (r : I → I → Prop)

noncomputable def pack (i : I) (children : ∀ j, r j i → Acc r j) (s : S)
    (args : Args (_root_.IR.Stage.Pred r i (fun j h => _root_.IR.Stage.build sig r j (children j h)))
      (_root_.IR.Stage.predDecode r) (sig s)) : _root_.IR.Stage.U sig r s :=
  _root_.IR.Stage.pack sig r i children s args

noncomputable def raise {i : I} {children : ∀ j, r j i → Acc r j} (s : S)
    (p : _root_.IR.Stage.Pred r i (fun j h => _root_.IR.Stage.build sig r j (children j h)) s) :
    _root_.IR.Stage.U sig r s := _root_.IR.Stage.raise sig r s p

end Mumi.IR
