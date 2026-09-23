module

public import Mumi.IR.Stages

@[expose] public section

/-!
One universe-polymorphic operational reflection principle, only at `(u, u+1)`.

This is a proposed Mahlo-style interface, NOT a formalization or a proved
equivalence with a set-theoretic Mahlo cardinal axiom. Reflection chooses stages
for each positive description. It does not postulate IR carriers, decoders,
eliminators, or their computation rules.
-/

universe u v

namespace IR

-- The two independent levels occur in the structure's sort through a maximum.
set_option linter.checkUnivs false in
structure Reflection where
  reflect : ∀ (S : Type u) (D : S → Type v) (sig : Signature S D), StageModel sig

/-- The sole additional axiom: small carriers and successor-universe outputs. -/
axiom mahlo : Reflection.{u, u+1}

/-- Smaller semantic outputs can be lifted into `Type (u+1)` using `ULift`. -/
noncomputable def model {S : Type u} {D : S → Type (u+1)} (sig : Signature S D) : StageModel sig :=
  mahlo.{u}.reflect S D sig

namespace Raw

variable {S : Type u} {D : S → Type (u+1)} (sig : Signature S D)

noncomputable def U : S → Type u := Stage.U sig (model sig).lt
noncomputable def decode : (s : S) → U sig s → D s := Stage.decode sig (model sig).lt

noncomputable def roll (s : S) (args : Desc.Args (U sig) (decode sig) (sig s)) : U sig s :=
  Stage.rollAt sig (model sig).lt (model sig).wf
    ((model sig).bound s args).val s args ((model sig).bound s args).property

theorem decode_roll (s : S) (args : Desc.Args (U sig) (decode sig) (sig s)) :
    decode sig s (roll sig s args) = Desc.eval (U sig) (decode sig) (sig s) args :=
  Stage.decode_rollAt sig (model sig).lt (model sig).wf
    ((model sig).bound s args).val s args ((model sig).bound s args).property

end Raw
end IR
