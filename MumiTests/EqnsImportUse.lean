import MumiTests.EqnsImport

namespace EqnsImport

/-- info: size.eq_1 : ∀ (cs : List T) (a : Ok cs), size (T.node cs a) = 1 + sizes cs -/
#guard_msgs in
#check @size.eq_1

example (cs : List T) (h : Ok cs) : size (.node cs h) = 1 + sizes cs := by simp [size]
example (cs : List T) (h : Ok cs) : size (.node cs h) = 1 + sizes cs := by rw [size]

/-- info: isLeaf.eq_1 : ∀ (cs : List T) (a : Ok cs), isLeaf (T.node cs a) = false -/
#guard_msgs in
#check @isLeaf.eq_1

example (c : List T) (h : Ok c) : isLeaf (.node c h) = false := by simp [isLeaf]

/-- info: n.eq_1 : n U.z = 0 -/
#guard_msgs in
#check @n.eq_1

example (us : List U) (w : V) : n (.s us w) = us.length := by simp [n]

end EqnsImport
