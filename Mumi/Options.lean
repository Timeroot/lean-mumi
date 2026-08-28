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

register_option mumi.pp.nested : Bool := {
  defValue := true
  descr := "display a rescued nested inductive's auxiliary member as the type it is a copy \
    of, rather than under its internal name"
}
