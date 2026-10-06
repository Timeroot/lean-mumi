/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Mumi.Lowering
public import Mumi.View

public section

/-!
# The declarations an aliased member answers to

A data member whose `X.rec` is owed to a recursion over more than its own kernel
block is declared as `X._ind`, and the writer's `X` and `X.c` are reducible
definitions unfolding to it (`addAliasedInds`).  Lean builds everything an
inductive comes with for `X._ind`; this module restates each piece under the
name an inductive `X` would have given it, with `X._ind` and its constructors
read back as `X` and `X.c` wherever they appear.  Every restatement is the
original constant at a type it already has up to unfolding, so nothing here is
proved twice:

* `X.casesOn`, `X.noConfusionType`, `X.noConfusion`, `X.ctorIdx`, `X.below`
  and `X.brecOn`;
* `X.c.inj`, `X.c.injEq` and `X.c.sizeOf_spec`, the last two `@[simp]` as Lean
  makes them.

`X.recOn` is not among them: it is the block's `X.rec` with the major premise
first, as `Lean.mkRecOn` builds it, and the kernel's would be over `X._ind`'s
block alone.  A `Prop` member of such a block has no inductive of its own under
its name either, so its `casesOn` is cut out of the block's recursor.

A `casesOn` names its motive the way the block's recursor names the member's,
as Lean's does for a `mutual` block.
-/

namespace Mumi

open Lean Meta Lean.Elab Lean.Elab.MultiuniverseInductive

/-- The writer's name for a constant of an aliased inductive: `X` for `X._ind`,
and `X.c` for `X._ind.c` -- each only where the writer's name exists. -/
def publicName? (env : Environment) (n : Name) : Option Name :=
  match n with
  | .str p@(.str q "_ind") c =>
    let pub := Name.str q c
    if env.contains pub && env.contains p then some pub else none
  | .str q "_ind" => if env.contains q then some q else none
  | _ => none

/-- `e` with every constant of an aliased inductive read back under the writer's name. -/
def publicize (e : Expr) : MetaM Expr := do
  let env ← getEnv
  return e.replace fun
    | .const n us => (publicName? env n).map (.const · us)
    | _ => none

/-- Rename the `∀`-binder at position `i` of `e`. -/
private partial def renameBinder (i : Nat) (nm : Name) : Expr → Expr
  | .forallE n d b bi =>
    if i == 0 then .forallE nm d b bi else .forallE n d (renameBinder (i - 1) nm b) bi
  | e => e

/--
Restate `src` as `dst`, at its own type read back under the writer's names.
`motiveAt` renames one binder, which is how a one-motive eliminator takes the
name the block's recursor gives the member's motive. -/
def restate (src dst : Name) (motiveAt : Option (Nat × Name) := none) (simp := false)
    (reducible := true) : MetaM Unit := do
  let env ← getEnv
  if env.contains dst then return
  let some info := env.find? src | return
  let lps := info.levelParams
  let mut type ← publicize info.type
  if let some (i, nm) := motiveAt then type := renameBinder i nm type
  let value := mkConst src (lps.map Level.param)
  if info.isTheorem || (← isProp type) then
    addDecl (.thmDecl { name := dst, levelParams := lps, type, value })
  else
    addDef dst lps type value (hints := .abbrev) (compile := false)
    if reducible then setReducibleAttribute dst
    -- compiled where the original is, so that a use of the restatement runs
    unless isNoncomputable env src do
      try compileDecl (.defnDecl (← getConstInfoDefn dst)) (logErrors := false) catch _ => pure ()
  modifyEnv fun env => addProtected env dst
  if simp then
    let simpAttr ← ofExcept <| getAttributeImpl (← getEnv) `simp
    simpAttr.add dst default .global

/--
Everything Lean built for `X._ind`, under the names it would have built it under
for an inductive `X`, for each aliased data member of a block with `numParams`
parameters; and for each `Prop` member, the one-motive `casesOn` the block's
recursor cuts down to. -/
def publishAliased (numParams : Nat) (members : Array Name) : TermElabM Unit := do
  for mem in members do
    let ind := aliasIndName mem
    let env ← getEnv
    unless env.contains mem do continue
    match env.find? ind with
    | some (.inductInfo ii) =>
      let motive? ← motiveNameOf? numParams mem
      discard <| attempt? `Mumi m!"no `casesOn` for `{mem}`" <|
        restate (ind ++ `casesOn) (mem ++ `casesOn) (motive?.map (numParams, ·))
      for s in [`noConfusionType, `noConfusion, `ctorIdx, `below, `brecOn] do
        discard <| attempt? `Mumi m!"no `{s}` for `{mem}`" <| restate (ind ++ s) (mem ++ s)
      for c in ii.ctors do
        let pub := Name.str mem c.getString!
        discard <| attempt? `Mumi m!"no injectivity for `{pub}`" do
          restate (c ++ `inj) (pub ++ `inj)
          restate (c ++ `injEq) (pub ++ `injEq) (simp := true)
        discard <| attempt? `Mumi m!"no `sizeOf` lemma for `{pub}`" <|
          restate (c ++ `sizeOf_spec) (pub ++ `sizeOf_spec) (simp := true)
    | _ =>
      -- a `Prop` member, whose name is its shadow's: its case split is the
      -- block's recursion with every hypothesis and every other motive dropped
      unless ← forallTelescope (← getConstInfo mem).type fun _ s => pure s.isProp do
        continue
      unless env.contains (mem ++ `rec) do continue
      -- the recursor's own universe is the first, as Lean orders them
      let elim := (← getConstInfo (mem ++ `rec)).levelParams.take 1
      discard <| attempt? `Mumi m!"no `casesOn` for `{mem}`" do
        addSoloElim numParams elim.toArray true (mem ++ `rec) (mem ++ `casesP)
          (forCases := true) (evenIfWeaker := true)
        addMajorFirst numParams mem (mem ++ `casesP) (mem ++ `casesOn)
    discard <| attempt? `Mumi m!"no `recOn` for `{mem}`" <|
      addMajorFirst numParams mem (mem ++ `rec) (mem ++ `recOn)

end Mumi
