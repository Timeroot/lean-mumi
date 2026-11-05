module

public import Mumi

/-! The same across the module system: the equations of an exposed definition, asked for
by an importer of its public scope (`MumiTests.EqnsModuleUse`). -/

public section

namespace EqnsModule

mutual
inductive T : Type where
  | node : (cs : List T) → Ok cs → T
  | leaf : T
inductive Ok : List T → Prop where
  | nil  : Ok []
end

@[expose] def isLeaf : T → Bool
  | .node _ _ => false
  | .leaf => true

end EqnsModule
