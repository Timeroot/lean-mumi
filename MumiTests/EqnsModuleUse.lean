import MumiTests.EqnsModule

namespace EqnsModule

/-- info: isLeaf.eq_1 : ∀ (cs : List T) (a : Ok cs), isLeaf (T.node cs a) = false -/
#guard_msgs in
#check @isLeaf.eq_1

example (c : List T) (h : Ok c) : isLeaf (.node c h) = false := by simp [isLeaf]

end EqnsModule
