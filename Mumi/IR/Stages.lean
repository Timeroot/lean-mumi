module

public import Mumi.IR.Description

@[expose] public section

/-! The axiom-free accessibility construction for an arbitrary indexed IR signature. -/

set_option maxRecDepth 3000
set_option linter.defProp false

universe u v

namespace IR

structure Family (S : Type u) (D : S → Type v) where
  carrier : S → Type u
  decode : (s : S) → carrier s → D s

def carrier {S : Type u} {D : S → Type v} (f : Family S D) := f.carrier
def decoder {S : Type u} {D : S → Type v} (f : Family S D) := f.decode

namespace Stage

variable {S : Type u} {D : S → Type v} (sig : Signature S D)
variable {I : Type u} (r : I → I → Prop)

structure Pred (i : I) (prev : ∀ j, r j i → Family S D) (s : S) : Type u where
  stage : I
  lower : r stage i
  code : carrier (prev stage lower) s

def predDecode {i : I} {prev : ∀ j, r j i → Family S D} (s : S) (p : Pred r i prev s) : D s :=
  decoder (prev p.stage p.lower) s p.code

def step (i : I) (prev : ∀ j, r j i → Family S D) : Family S D :=
  ⟨fun s => Desc.Args (Pred r i prev) (predDecode r) (sig s),
    fun s => Desc.eval (Pred r i prev) (predDecode r) (sig s)⟩

noncomputable def build (i : I) (h : Acc r i) : Family S D :=
  @Acc.rec I r (fun _ _ => Family S D) (fun i _ ih => step sig r i ih) i h

structure U (s : S) : Type u where
  stage : I
  access : Acc r stage
  code : carrier (build sig r stage access) s

def getAcc {s : S} (a : U sig r s) : Acc r a.stage :=
  @U.rec S D sig I r s (fun a => Acc r a.stage) (fun _ ac _ => ac) a

noncomputable def decode (s : S) (a : U sig r s) : D s :=
  decoder (build sig r a.stage (getAcc sig r a)) s a.code

noncomputable def pack (i : I) (children : ∀ j, r j i → Acc r j) (s : S)
    (args : Desc.Args (Pred r i (fun j h => build sig r j (children j h))) (predDecode r) (sig s)) :
    U sig r s := ⟨i, .intro i children, args⟩

variable (wf : WellFounded r)

noncomputable def lower {i : I} (s : S) (a : U sig r s) (h : r a.stage i) :
    Pred r i (fun j _ => build sig r j (wf.apply j)) s := ⟨a.stage, h, a.code⟩

theorem decode_lower {i : I} (s : S) (a : U sig r s) (h : r a.stage i) :
    predDecode r s (lower sig r wf (i := i) s a h) = decode sig r s a := rfl

/-- Function-level preservation avoids assuming function extensionality in the backend. -/
theorem decode_lowerAll {i : I} :
    (fun s (a : U sig r s) (h : r a.stage i) => predDecode r s (lower sig r wf s a h)) =
      (fun s (a : U sig r s) (_ : r a.stage i) => decode sig r s a) := rfl

noncomputable def rollAt (i : I) (s : S)
    (args : Desc.Args (U sig r) (decode sig r) (sig s))
    (bound : Desc.All (U sig r) (decode sig r) (fun _ a => r a.stage i) (sig s) args) : U sig r s :=
  pack sig r i (fun j _ => wf.apply j) s
    (Desc.mapAll (lower sig r wf) (decode_lowerAll sig r wf) (sig s) args bound)

theorem decode_rollAt (i : I) (s : S)
    (args : Desc.Args (U sig r) (decode sig r) (sig s))
    (bound : Desc.All (U sig r) (decode sig r) (fun _ a => r a.stage i) (sig s) args) :
    decode sig r s (rollAt sig r wf i s args bound) = Desc.eval (U sig r) (decode sig r) (sig s) args :=
  Desc.eval_mapAll (lower sig r wf) (decode_lowerAll sig r wf) (sig s) args bound

end Stage

/-- Only stage existence and closure are assumed; the IR types and equations are derived. -/
structure StageModel {S : Type u} {D : S → Type v} (sig : Signature S D) where
  Level : Type u
  lt : Level → Level → Prop
  wf : WellFounded lt
  bound : ∀ s (args : Desc.Args (Stage.U sig lt) (Stage.decode sig lt) (sig s)),
    {i : Level // Desc.All (Stage.U sig lt) (Stage.decode sig lt) (fun _ a => lt a.stage i) (sig s) args}

end IR
