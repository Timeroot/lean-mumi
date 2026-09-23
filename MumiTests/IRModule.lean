module

public import Mumi

public section

namespace IRModuleUpper
set_option mumi.mahlo false
mutual
  inductive U : Type where
    | base : U
    | pi (a : U) (b : El a → U) : U
  def El : U → Type
    | .base => Nat
    | .pi a b => (x : El a) → El (b x)
end
end IRModuleUpper

namespace IRModuleLower
set_option mumi.mahlo true
set_option maxRecDepth 4000
mutual
  inductive U : Type where
    | base : U
    | pi (a : U) (b : El a → U) : U
  def El : U → Type
    | .base => Nat
    | .pi a b => (x : El a) → El (b x)
end
end IRModuleLower
