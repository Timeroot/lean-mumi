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

register_option mumi.pp.nested : Bool := {
  defValue := true
  descr := "display a rescued nested inductive's auxiliary member as the type it is a copy \
    of, rather than under its internal name"
}

register_option mumi.mahlo : Bool := {
  defValue := false
  descr := "lower experimental induction-recursion blocks using IR.mahlo; when false, use an axiom-free graph one universe up"
}
