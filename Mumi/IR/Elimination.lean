module

public import Mumi.IR.Mahlo

@[expose] public section

/-!
Generic stage-aware dependent elimination and a one-layer view.

The step is stated in the predecessor family at a stage. This low-level interface
works for every description, including value-dependent delta continuations;
it does not assert canonical initiality of the redundant raw carrier.
-/

set_option maxRecDepth 3000
set_option linter.defProp false

universe u v w

namespace IR.Stage

variable {S : Type u} {D : S → Type v} (sig : Signature S D)
variable {I : Type u} (r : I → I → Prop)

noncomputable def raise {i : I} {children : ∀ j, r j i → Acc r j} (s : S)
    (p : Pred r i (fun j h => build sig r j (children j h)) s) : U sig r s :=
  ⟨p.stage, children p.stage p.lower, p.code⟩

theorem decode_raise {i : I} {children : ∀ j, r j i → Acc r j} :
    (fun s p => decode sig r s (raise sig r (children := children) s p)) = predDecode r := rfl

def _expandAccess {i : I} (h : Acc r i) : Acc r i :=
  .intro i (fun _ p => Acc.inv h p)

noncomputable def _exposeFamily {i : I} (h : Acc r i) (s : S)
    (x : carrier (build sig r i h) s) : carrier (build sig r i (_expandAccess r h)) s := x

noncomputable def _exposeArgs {i : I} (h : Acc r i) (s : S)
    (x : carrier (build sig r i (_expandAccess r h)) s) :
    Desc.Args (Pred r i (fun j p => build sig r j (Acc.inv h p))) (predDecode r) (sig s) := x

noncomputable def view (s : S) (a : U sig r s) : Desc.Args (U sig r) (decode sig r) (sig s) :=
  Desc.map (raise sig r) (decode_raise sig r) (sig s)
    (_exposeArgs sig r (getAcc sig r a) s (_exposeFamily sig r (getAcc sig r a) s a.code))

noncomputable def _exposedDecode {i : I} (h : Acc r i) (s : S)
    (x : carrier (build sig r i h) s) : D s :=
  decoder (build sig r i (_expandAccess r h)) s (_exposeFamily sig r h s x)

private theorem exposedDecode_eq {i : I} (h : Acc r i) (s : S)
    (x : carrier (build sig r i h) s) :
    _exposedDecode sig r h s x = decoder (build sig r i h) s x := rfl

theorem decode_view (s : S) (a : U sig r s) :
    Desc.eval (U sig r) (decode sig r) (sig s) (view sig r s a) = decode sig r s a :=
  (Desc.eval_map (raise sig r) (decode_raise sig r) (sig s) _).trans
    (exposedDecode_eq sig r (getAcc sig r a) s a.code)

theorem view_pack (i : I) (children : ∀ j, r j i → Acc r j) (s : S)
    (args : Desc.Args (Pred r i (fun j h => build sig r j (children j h))) (predDecode r) (sig s)) :
    view sig r s (pack sig r i children s args) =
      Desc.map (raise sig r) (decode_raise sig r) (sig s) args := rfl

/-- A dependent induction step with access to every earlier-stage recursive result. -/
def Step (C : (s : S) → U sig r s → Sort w) :=
  ∀ (i : I) (children : ∀ j, r j i → Acc r j) (s : S)
    (args : Desc.Args (Pred r i (fun j h => build sig r j (children j h))) (predDecode r) (sig s)),
    (∀ t (p : Pred r i (fun j h => build sig r j (children j h)) t), C t (raise sig r t p)) →
      C s (pack sig r i children s args)

noncomputable def _inductionAt {C : (s : S) → U sig r s → Sort w}
    (step : Step sig r C) (i : I) (h : Acc r i) :
    (s : S) → (x : carrier (build sig r i h) s) → C s ⟨i, h, x⟩ :=
  @Acc.rec I r (fun i h => (s : S) → (x : carrier (build sig r i h) s) → C s ⟨i, h, x⟩)
    (fun i children ih s args => step i children s args (fun t p => ih p.stage p.lower t p.code)) i h

noncomputable def induction {C : (s : S) → U sig r s → Sort w}
    (step : Step sig r C) (s : S) (a : U sig r s) : C s a :=
  _inductionAt sig r step a.stage (getAcc sig r a) s a.code

theorem induction_pack {C : (s : S) → U sig r s → Sort w} (step : Step sig r C)
    (i : I) (children : ∀ j, r j i → Acc r j) (s : S)
    (args : Desc.Args (Pred r i (fun j h => build sig r j (children j h))) (predDecode r) (sig s)) :
    induction sig r step s (pack sig r i children s args) =
      step i children s args (fun t p => induction sig r step t (raise sig r t p)) := rfl

end IR.Stage

namespace IR.Raw

variable {S : Type u} {D : S → Type (u+1)} (sig : Signature S D)

noncomputable def view (s : S) (a : U sig s) : Desc.Args (U sig) (decode sig) (sig s) :=
  Stage.view sig (model sig).lt s a

theorem decode_view (s : S) (a : U sig s) :
    Desc.eval (U sig) (decode sig) (sig s) (view sig s a) = decode sig s a :=
  Stage.decode_view sig (model sig).lt s a

@[elab_as_elim] noncomputable def induction {C : (s : S) → U sig s → Sort w}
    (step : Stage.Step sig (model sig).lt C) (s : S) (a : U sig s) : C s a :=
  Stage.induction sig (model sig).lt step s a

end IR.Raw
