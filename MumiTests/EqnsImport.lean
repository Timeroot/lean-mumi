import Mumi

/-! Definitions whose equations nothing here asks for: `MumiTests.EqnsImportUse` is the
first to, in another module, where they are generated on demand. -/

namespace EqnsImport

mutual
inductive T : Type where
  | node : (cs : List T) → Ok cs → T
  | leaf : T
inductive Ok : List T → Prop where
  | nil  : Ok []
  | cons : (t : T) → (ts : List T) → Ok ts → Ok (t :: ts)
end

mutual
def size : T → Nat
  | .node cs _ => 1 + sizes cs
  | .leaf => 1
def sizes : List T → Nat
  | [] => 0
  | t :: ts => size t + sizes ts
end

def isLeaf : T → Bool
  | .node _ _ => false
  | .leaf => true

mutual
inductive U : Type 1 where
  | z : U
  | s : List U → V → U
inductive V : Type where
  | v : V
end

def n : U → Nat
  | .z => 0
  | .s us _ => us.length

end EqnsImport
