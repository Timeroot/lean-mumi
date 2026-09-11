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
  descr := "allow the members of a `mutual` inductive block to live in different universes, \
    by lowering the block to declarations the kernel accepts"
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
