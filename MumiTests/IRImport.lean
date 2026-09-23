import MumiTests.IRModule

namespace IRModuleUpper
example : El (U.pi U.base (fun _ => U.base)) = (Nat → Nat) := rfl
example (a : U) (b : El a → U) : El (U.pi a b) = ((x : El a) → El (b x)) := rfl
example (a : U) : True := by induction a <;> trivial
example (a : U) : True := by cases a <;> trivial
end IRModuleUpper

namespace IRModuleLower
example : Type := U
example (a : U) (b : El a → U) : El (U.pi a b) = ((x : El a) → El (b x)) := rfl
example (a : U) : True := by induction a <;> trivial
example (a : U) : True := by cases a <;> trivial
end IRModuleLower
