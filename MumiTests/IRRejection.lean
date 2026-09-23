import Mumi

open Lean Elab Command

-- Check the diagnostic and that a failed transaction leaves no partial IR API.
elab "reject_ir " expected:str " [" names:ident,* "]" " in " c:command : command => do
  let saved ← get
  let ns ← getCurrNamespace
  let count := saved.messages.reportedPlusUnreported.size
  try elabCommand c
  catch ex => logException ex
  let after ← getEnv
  let errors := ((← get).messages.reportedPlusUnreported.toList.drop count).filter (·.severity == .error)
  let messages ← errors.mapM (fun e => e.data.toString)
  set saved
  unless messages.any (fun s => (s.splitOn expected.getString).length > 1) do
    throwError "Expected IR rejection containing {expected.getString}, got {messages}"
  for n in names.getElems do
    if after.contains (ns ++ n.getId) then throwError "Failed IR block leaked declaration {n.getId}"

namespace IRRejected

reject_ir "domains cannot contain the carriers" [Negative, _ir_Negative_Sem] in
mutual
  inductive Negative : Type where
    | bad (f : Negative → Negative) : Negative
  def size : Negative → Nat
    | .bad f => 0
end

reject_ir "exactly one equation" [Missing, _ir_Missing_Sem] in
mutual
  inductive Missing : Type where
    | left : Missing
    | right : Missing
  def size : Missing → Nat
    | .left => 0
end

reject_ir "While generating IR declaration" [BadOutput, _ir_BadOutput_Sem, _ir_BadOutput] in
mutual
  inductive BadOutput : Type where
    | base : BadOutput
  def El : BadOutput → Type
    | .base => (37 : Nat)
end

set_option mumi.mahlo true in
reject_ir "While generating IR declaration" [TooLarge, _ir_TooLarge_Sem, _ir_TooLarge_sig] in
mutual
  inductive TooLarge : Type where
    | code (A : Type) : TooLarge
  def El : TooLarge → Type
    | .code A => A
end

set_option mumi.enabled false in
reject_ir "invalid mutual block" [Disabled, _ir_Disabled_Sem] in
mutual
  inductive Disabled : Type where
    | base : Disabled
  def El : Disabled → Type
    | .base => Nat
end

reject_ir "shadowing" [Shadow0, _ir_Shadow0_Sem] in
mutual
  inductive Shadow0 : Type where
    | leaf (n : Nat) : Shadow0
  def get : Shadow0 → Nat → Nat
    | .leaf k => fun n => n
end

reject_ir "shadowing" [Shadow1, _ir_Shadow1_Sem] in
mutual
  inductive Shadow1 : Type where
    | leaf (n : Nat) : Shadow1
  def get : Shadow1 → Nat → Nat
    | .leaf k => fun (n : Nat) => n
end

reject_ir "shadowing" [Shadow2, _ir_Shadow2_Sem] in
mutual
  inductive Shadow2 : Type where
    | leaf (n : Nat) : Shadow2
  def get : Shadow2 → Nat
    | .leaf k => let n := 5; n
end

reject_ir "shadowing" [Shadow3, _ir_Shadow3_Sem] in
mutual
  inductive Shadow3 : Type where
    | leaf (n : Nat) : Shadow3
  def get : Shadow3 → Nat
    | .leaf k => match k with | .zero => 0 | .succ n => n
end

def n : Nat := 19

reject_ir "would capture constructor field name" [Captured, _ir_Captured_Sem] in
mutual
  inductive Captured : Type where
    | leaf (n : Nat) : Captured
  def get : Captured → Nat
    | .leaf k => n + k
end

reject_ir "distinct binder names" [Duplicated, _ir_Duplicated_Sem] in
mutual
  inductive Duplicated : Type where
    | node (x y : Nat) : Duplicated
  def get : Duplicated → Nat
    | .node z z => z
end

end IRRejected
