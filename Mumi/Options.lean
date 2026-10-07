/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Lean.Data.Options

/-! # Options -/

public section

register_option mumi.enabled : Bool := {
  defValue := true
  descr := "enable Mumi's heterogeneous, induction-inductive, nested, and experimental \
    induction-recursion elaboration"
}

register_option mumi.separate : Bool := {
  defValue := true
  descr := "hand a `mutual` block whose members have no cyclic dependency back to Lean, one \
    declaration at a time, instead of reading it as an induction-induction.  Turn this off to \
    keep the block's joint recursor"
}

register_option mumi.pp.nested : Bool := {
  defValue := true
  descr := "display a rescued nested inductive's auxiliary member as the type it is a copy \
    of, rather than under its internal name"
}

register_option mumi.ir.debug : Bool := {
  defValue := false
  descr := "keep the declarations an induction-recursion block managed to emit when a later one fails, \
    instead of rolling the block back, so that they can be inspected"
}

register_option mumi.ir.equations : Bool := {
  defValue := true
  descr := "at the universe an induction-recursion block is written at, state each decoder and \
    recursor equation and hand its `rfl` to the kernel, skipping the ones it rejects; off, state \
    none of them"
}

register_option mumi.mahlo : Bool := {
  defValue := false
  descr := "lower experimental induction-recursion blocks using IR.mahlo; when false, use an axiom-free graph one universe up"
}

register_option mumi.partialRecursors : Bool := {
  defValue := false
  descr := "declare a block whose recursor cannot state every inductive hypothesis -- a proof \
    field whose index the recursion cannot follow, as `Ok (f Γ)` for a function `f` from \
    outside the block -- with those hypotheses left out, instead of rejecting it"
}

register_option mumi.roundTripRules : Bool := {
  defValue := true
  descr := "state each recursor and `casesOn` rule that a round trip through a nested copy keeps \
    from holding by `rfl` as a `@[simp]` lemma under the rule's name, `X.rec_c` or `X.casesOn_c`"
}
