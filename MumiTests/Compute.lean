/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import MumiTests.Spec.Harness

/-!
# What a function over a member computes

A member of an induction-inductive block is a definition over a wrapper, and the
wrapper takes its context as a datatype *parameter*.  Lean's structural recursion
requires a datatype parameter to be fixed across the recursive calls, so a
function whose context argument varies is compiled by well-founded recursion
instead.  Lean seals a well-founded definition, and that is what stops `rfl` and
`decide`.

No computation is out of reach, and the encoding adds no axiom of its own.  There
are five cases, all pinned below:

* a recursion over an unindexed member is structural;
* a recursion over an indexed member is structural when the context is a *fixed
  parameter* in Lean's sense: bound outside the `match`, and passed back
  unchanged by every recursive call;
* a recursion whose context varies is well-founded.  It runs under `#eval` and
  rewrites under `simp`, and `unseal` gives back `rfl` and `decide` wherever the
  measure can be read off the term.  It costs the axioms any well-founded
  definition costs;
* a recursion that descends through a *nesting* is well-founded, on `sizeOf`;
* a definition written on `recD` computes in every case, and costs nothing.

The parameter cannot be turned into an index.  Lean requires an index to be a
variable, and a member's context reaches the wrapper as `Γ.val`.  An indexed
wrapper would also lose definitional eta, and eta is what gives every member's
recursor its `rfl` iota rule -- see the module doc of `Mumi.IndInd`.
-/

namespace MumiTests.Compute

/-! ## The block

`up` crosses the index: its second field is stated one context along from the
one the constructor concludes at. -/

mumi_spec
mutual
inductive Ctx : Type where
  | nil : Ctx
  | snoc (Γ : Ctx) (A : Ty Γ) : Ctx
inductive Ty : Ctx → Type where
  | base (Γ : Ctx) : Ty Γ
  | pair (Γ : Ctx) (A B : Ty Γ) : Ty Γ
  | up (Γ : Ctx) (A : Ty Γ) (B : Ty (.snoc Γ A)) : Ty Γ
end

/-! ## An unindexed member

The wrapper has no parameter to hold fixed, so the recursion is structural and
the equations hold by `rfl`. -/

/-- The number of `snoc`s in a context. -/
def clen : Ctx → Nat
  | .nil => 0
  | .snoc Γ _ => clen Γ + 1

example : clen .nil = 0 := rfl
example (Γ : Ctx) (A : Ty Γ) : clen (.snoc Γ A) = clen Γ + 1 := rfl
example : clen (.snoc .nil (.base .nil)) = 1 := by decide

/-! ## An indexed member with the context fixed

`Γ` is a parameter of the function, not a matched argument, and every recursive
call passes it unchanged.  That is what the wrapper's parameter needs, so this is
structural too. -/

/-- The number of constructors in a type, counting `up` as one and skipping the
field that crosses the index. -/
def tlen (Γ : Ctx) : Ty Γ → Nat
  | .base _ => 1
  | .pair _ A B => tlen Γ A + tlen Γ B
  | .up _ A _ => tlen Γ A + 1

example (Γ : Ctx) : tlen Γ (.base Γ) = 1 := rfl
example (Γ : Ctx) (A B : Ty Γ) : tlen Γ (.pair Γ A B) = tlen Γ A + tlen Γ B := rfl
example : tlen .nil (.pair .nil (.base .nil) (.base .nil)) = 2 := by decide

/-! ## What makes the context fixed

Neither the colon nor the arrow.  `Γ` is fixed when it is bound outside the
`match` and every recursive call passes it back unchanged.  Binding it before the
colon is one way to keep it out of the `match`; a `fun` in front of the `match` is
another, and gives the same structural recursion. -/

/-- `tlen` again, declared with the context after the colon. -/
def tlen' : (Γ : Ctx) → Ty Γ → Nat := fun Γ t =>
  match t with
  | .base _ => 1
  | .pair _ A B => tlen' Γ A + tlen' Γ B
  | .up _ A _ => tlen' Γ A + 1

example (Γ : Ctx) : tlen' Γ (.base Γ) = 1 := rfl

/-- info: 'MumiTests.Compute.tlen'' does not depend on any axioms -/
#guard_msgs in
#print axioms tlen'

/-! Conversely, binding it before the colon does not make it fixed if a recursive
call changes it. -/

/-- The index-crossing recursion, written with the context before the colon.  It
is still well-founded, because `up`'s call passes `Γ.snoc A`. -/
def tsizePre (Γ : Ctx) : Ty Γ → Nat
  | .base _ => 1
  | .pair _ A B => tsizePre Γ A + tsizePre Γ B
  | .up _ A B => tsizePre Γ A + tsizePre (.snoc Γ A) B

/-- info: 'MumiTests.Compute.tsizePre' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tsizePre

/-! The third way to lose it is to match on the context, even under a wildcard.
The recursive calls then pass the `match`'s own binder rather than the function's
parameter, so the analysis cannot see the two as the same.  Asking for structural
recursion explicitly reports it: -/

/--
error: cannot use specified measure for structural recursion:
  its type is an inductive datatype
    Ty._sub x✝¹.val
  and the datatype parameter
    x✝¹.val
  depends on the function parameter
    x✝¹
  which is not fixed.
-/
#guard_msgs in
def tlenM : (Γ : Ctx) → Ty Γ → Nat
  | _, .base _ => 1
  | Γ, .pair _ A B => tlenM Γ A + tlenM Γ B
  | Γ, .up _ A _ => tlenM Γ A + 1
  termination_by structural _ t => t

/-! This is where the encoding differs from a genuine inductive family.  There the
context is an *index*, and a structural recursion may vary an index freely.  Here
it reaches the wrapper as the datatype *parameter* `Γ.val`, and a parameter has to
be fixed.

The rule itself is not this library's.  Lean treats a datatype parameter the same
way wherever it comes from, and the same two definitions split the same way with
no erased block in sight. -/

namespace Stock

mumi_spec
inductive P (n : Nat) : Type where
  | mk : P n
  | wrap : P n → P n

/-- `n` is bound outside the match, so the recursion is structural. -/
def f1 (n : Nat) : P n → Nat
  | .mk => 0
  | .wrap x => f1 n x + 1

example (n : Nat) (x : P n) : f1 n (.wrap x) = f1 n x + 1 := rfl

/-! The same type, and every call passes the same `n` back.  Matching on it is the
whole difference, and the error is the one above. -/

/--
error: cannot use specified measure for structural recursion:
  its type is an inductive datatype
    P x✝¹
  and the datatype parameter
    x✝¹
  depends on the function parameter
    x✝¹
  which is not fixed.
-/
#guard_msgs in
def f2 : (n : Nat) → P n → Nat
  | _, .mk => 0
  | n, .wrap x => f2 n x + 1
  termination_by structural _ x => x

end Stock

/-! ## An indexed member with the context varying

`up`'s second field sits at `Γ.snoc A`, so the recursion cannot hold `Γ` fixed
and Lean compiles it by well-founded recursion. -/

/-- The number of constructors in a type, following the field that crosses the
index. -/
def tsize : (Γ : Ctx) → Ty Γ → Nat
  | _, .base _ => 1
  | Γ, .pair _ A B => tsize Γ A + tsize Γ B
  | Γ, .up _ A B => tsize Γ A + tsize (.snoc Γ A) B

/-! It runs, and it rewrites. -/

/-- info: 3 -/
#guard_msgs in
#eval tsize .nil (.pair .nil (.base .nil) (.up .nil (.base .nil) (.base _)))

example (Γ : Ctx) : tsize Γ (.base Γ) = 1 := by simp [tsize]

/-! What the seal costs is `rfl`, and `unseal` gives it back.  A well-founded
recursion unfolds by counting its measure down, so what comes back is reduction
on a term the measure can be read off, which is a closed one: `sizeOf (.base Γ)` is
`1 + sizeOf Γ`, as Lean counts it, and that is stuck at a variable `Γ`. -/

unseal tsize in
example : tsize .nil (.base .nil) = 1 := rfl

unseal tsize in
example : tsize .nil (.up .nil (.base .nil) (.base _)) = 2 := rfl

unseal tsize in
example : tsize .nil (.pair .nil (.base .nil) (.base .nil)) = 2 := by decide

/-! A step equation at an open context is the one thing that stays out of reach:
the measure is `sizeOf A`, and there is no reading that off a variable.  `simp`
proves it, and `recD` below has it by `rfl`. -/

example (Γ : Ctx) (A : Ty Γ) (B : Ty (.snoc Γ A)) :
    tsize Γ (.up Γ A B) = tsize Γ A + tsize (.snoc Γ A) B := by simp [tsize]

/-! Including where the value is a type's index. -/

/-- A vector as long as the type is big. -/
def vec (Γ : Ctx) (A : Ty Γ) : Type := Vector Nat (tsize Γ A)

unseal tsize in
example : vec .nil (.base .nil) := #v[7]

/-! ## Recursion through a nesting

A member may nest itself under a container.  The constructor's field is then
packed as a copy of that container, and a recursion that descends into the field
needs a measure.  `sizeOf` is that measure: the block emits a `SizeOf` instance
for every member and a `sizeOf_spec` for every constructor, in the form Lean's
termination tactic expects. -/

mumi_spec
inductive Wrap (α : Type) where
  | mk : α → Wrap α

mumi_spec
mutual
inductive WT : Type where
  | leaf : WT
  | node (w : Wrap WT) (h : WOk w) : WT
inductive WOk : Wrap WT → Prop where
  | mk (w : Wrap WT) : WOk w
end

/-- info: WT.node.sizeOf_spec : ∀ (w : Wrap WT) (h : WOk w), sizeOf (WT.node w h) = 1 + sizeOf w + sizeOf h -/
#guard_msgs in
#check @WT.node.sizeOf_spec

/-- The number of `node`s in a `WT`. -/
def wsize : WT → Nat
  | .leaf => 1
  | .node (.mk t) _ => wsize t + 1

/-- info: 2 -/
#guard_msgs in
#eval wsize (.node (.mk .leaf) (.mk _))

example (t : WT) (h : WOk (.mk t)) : wsize (.node (.mk t) h) = wsize t + 1 := by
  simp [wsize]

/-! A copy of a *recursive* container is only provably the same size as what it
copies: the two agree on a constructor by computation apart from the recursive
positions.  The block closes that gap with a `sizeOf_ofOrig` lemma per copy, and
proves the constructor's `sizeOf_spec` by rewriting with it. -/

mumi_spec (simp := [LstT.casesOn_node, LstT.rec_node, LstT.rec_1_cons])
mutual
inductive LstT : Type where
  | node (cs : List LstT) (h : LOk cs) : LstT
inductive LOk : List LstT → Prop where
  | mk (cs : List LstT) : LOk cs
end

/-- info: LstT.nested_List_1.sizeOf_ofOrig : ∀ (x : List LstT), sizeOf (LstT.nested_List_1.ofOrig x).val = sizeOf x -/
#guard_msgs in
#check @LstT.nested_List_1.sizeOf_ofOrig

/-- info: LstT.node.sizeOf_spec : ∀ (cs : List LstT) (h : LOk cs), sizeOf (LstT.node cs h) = 1 + sizeOf cs + sizeOf h -/
#guard_msgs in
#check @LstT.node.sizeOf_spec

/-- The number of `node`s in a `LstT`. -/
def lsize : LstT → Nat
  | .node cs _ => (cs.map lsize).sum + 1

/-- info: 3 -/
#guard_msgs in
#eval lsize (.node [.node [] (.mk _), .node [] (.mk _)] (.mk _))

/-! Mapping the recursion over the container is what vanilla Lean compiles by
well-founded recursion too, on the same measure and for the same reason, so the
axioms here are the ones the idiom costs anywhere. -/

namespace Stock

mumi_spec
inductive LT : Type where
  | node : List LT → LT

def lsize : LT → Nat
  | .node cs => (cs.map lsize).sum + 1

/-- info: 'MumiTests.Compute.Stock.lsize' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lsize

end Stock

/-- info: 'MumiTests.Compute.lsize' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lsize

/-! ## Or write the recursion on `recD`

The recursor's iota rules are definitional, so a definition built on it computes
whether or not the context varies, and needs no `unseal`. -/

/-- `tsize` again, on the recursor. -/
def tsize' {Γ : Ctx} (t : Ty Γ) : Nat :=
  Ty.recD (motive := fun _ _ => Nat) (fun _ => 1) (fun _ _ _ a b => a + b)
    (fun _ _ _ a b => a + b) t

example (Γ : Ctx) : tsize' (Ty.base Γ) = 1 := rfl
example (Γ : Ctx) (A B : Ty Γ) : tsize' (Ty.pair Γ A B) = tsize' A + tsize' B := rfl
example (Γ : Ctx) (A : Ty Γ) (B : Ty (.snoc Γ A)) :
    tsize' (Ty.up Γ A B) = tsize' A + tsize' B := rfl
example : tsize' (Ty.up .nil (.base .nil) (.base _)) = 2 := by decide

/-- info: 3 -/
#guard_msgs in
#eval tsize' (Ty.pair .nil (.base .nil) (.up .nil (.base .nil) (.base _)))

/-! ## What each one costs in axioms

The two structural recursions and the one on `recD` are axiom-free.  The
well-founded one reaches `Acc`, and with it the axioms `WellFounded` is stated
over -- which is what Lean charges for any well-founded definition, not
something the encoding adds. -/

/-- info: 'MumiTests.Compute.tlen' does not depend on any axioms -/
#guard_msgs in
#print axioms tlen

/-- info: 'MumiTests.Compute.tsize' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tsize

/-- info: 'MumiTests.Compute.tsize'' does not depend on any axioms -/
#guard_msgs in
#print axioms tsize'

/-! ## Termination through a container that is itself nested or mutual

A copy of `Rose RT` measures the same as `Rose RT`, but neither `Rose.rec`'s case nor
the copy's says so on its own: `Rose`'s field `cs : List (Rose α)` needs the same fact
of `List (Rose RT)`, and that one of `Rose RT` again.  The proof is `Rose.rec`, with the
motive for each type of `Rose`'s block speaking of the copy that takes it.  Without it
the block had no `sizeOf_spec`, and a definition as plain as `RT.count` failed its
termination check. -/

namespace SizeThrough

inductive Rose (α : Type) : Type where
  | node (a : α) (cs : List (Rose α))

mutual
inductive EvenT (α : Type) where
  | nil
  | cons (a : α) (o : OddT α)
inductive OddT (α : Type) where
  | cons (a : α) (e : EvenT α)
end

inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons {n} (a : α) (v : Vec α n) : Vec α (n + 1)

mutual
inductive RT : Type where
  | tip
  | mk (r : Rose RT) (t : RT) (h : RP t) : RT
inductive RP : RT → Prop where
  | tip : RP .tip
end

/-- info: RT.mk.sizeOf_spec : ∀ (r : Rose RT) (t : RT) (h : RP t), sizeOf (RT.mk r t h) = 1 + sizeOf r + sizeOf t + sizeOf h -/
#guard_msgs in
#check @RT.mk.sizeOf_spec

/-- info: RT.nested_Rose_1.sizeOf_ofOrig : ∀ (x : Rose RT), sizeOf (RT.nested_Rose_1.ofOrig x).val = sizeOf x -/
#guard_msgs in
#check @RT.nested_Rose_1.sizeOf_ofOrig

mutual
def RT.count : RT → Nat
  | .tip => 1
  | .mk r t _ => countR r + t.count
def countR : Rose RT → Nat
  | .node a cs => a.count + countL cs
def countL : List (Rose RT) → Nat
  | [] => 0
  | r :: rs => countR r + countL rs
end

/-- info: 3 -/
#guard_msgs in
#eval RT.count (.mk (.node .tip [.node .tip []]) .tip .tip)

-- the container's list straight in a field: its copy goes through `List.rec`, and
-- from there to the lemma of the copy of `Rose`
mutual
inductive LT : Type where
  | mk (l : List (Rose LT)) (ts : List LT) (h : LP l) : LT
inductive LP : List (Rose LT) → Prop where
  | nil : LP []
end

/-- info: LT.mk.sizeOf_spec : ∀ (l : List (Rose LT)) (ts : List LT) (h : LP l),
  sizeOf (LT.mk l ts h) = 1 + sizeOf l + sizeOf ts + sizeOf h -/
#guard_msgs in
#check @LT.mk.sizeOf_spec

-- a mutual container: `EvenT.rec`'s second motive speaks of the copy of `OddT`
mutual
inductive MT : Type where
  | tip
  | mk (e : EvenT MT) (t : MT) (h : MP t) : MT
inductive MP : MT → Prop where
  | tip : MP .tip
end

mutual
def MT.count : MT → Nat
  | .tip => 1
  | .mk e _ _ => countE e + 1
def countE : EvenT MT → Nat
  | .nil => 0
  | .cons a o => a.count + countO o
def countO : OddT MT → Nat
  | .cons a e => a.count + countE e
end

/-- info: 1 -/
#guard_msgs in
#eval MT.count (.mk .nil .tip .tip)

-- an indexed container, whose copy is taken at an index the constructor binds
mutual
inductive VT : Type where
  | tip
  | mk (n : Nat) (v : Vec VT n) (t : VT) (h : VP t) : VT
inductive VP : VT → Prop where
  | tip : VP .tip
end

/-- info: VT.mk.sizeOf_spec : ∀ (n : Nat) (v : Vec VT n) (t : VT) (h : VP t),
  sizeOf (VT.mk n v t h) = 1 + sizeOf n + sizeOf v + sizeOf t + sizeOf h -/
#guard_msgs in
#check @VT.mk.sizeOf_spec

/-! A copy taken at a local stores that local at every node, since its pre-type is
indexed by it: as a copy `[]` at `n` is `_pre.nil n`.  Lean's measure of the pre-term
would count `n` there, where the list `[]` has size `1`, so such a block is measured by
what was written instead (`addPreMeasure`), and the copy measures what the list does. -/

inductive RV (α : Type) : Nat → Type where
  | mk {n} (a : α) (cs : List (RV α n)) : RV α (n + 1)

/--
info: @RV.mk.sizeOf_spec : ∀ {α : Type} [inst : SizeOf α] {n : Nat} (a : α) (cs : List (RV α n)),
  sizeOf (RV.mk a cs) = 1 + sizeOf n + sizeOf a + sizeOf cs
-/
#guard_msgs in
#check @RV.mk.sizeOf_spec

-- the measure at a list is the list's, whatever the local
example {α : Type} [SizeOf α] {n : Nat} :
    sizeOf (RV.nested_List_1.ofOrig (α := α) (n := n) []).val = 1 := rfl

/-! Typed syntax, the shape this is for: `lam` varies the context, so it is a real index,
and `app` nests at it.  (With no `lam` the context is fixed, Lean promotes it to a
parameter, and there is no local to store.) -/

inductive Term : List Nat → Type where
  | var {Γ} (i : Nat) : Term Γ
  | lam {Γ} (A : Nat) (b : Term (A :: Γ)) : Term Γ
  | app {Γ} (f : Term Γ) (args : List (Term Γ)) : Term Γ

/--
info: @Term.app.sizeOf_spec : ∀ {Γ : List Nat} (f : Term Γ) (args : List (Term Γ)),
  sizeOf (f.app args) = 1 + sizeOf Γ + sizeOf f + sizeOf args
-/
#guard_msgs in
#check @Term.app.sizeOf_spec

mutual
def Term.size {Γ} : Term Γ → Nat
  | .var _ => 1
  | .lam _ b => b.size + 1
  | .app f args => f.size + sizes args
def sizes {Γ} : List (Term Γ) → Nat
  | [] => 0
  | t :: ts => t.size + sizes ts
end

/-- info: 4 -/
#guard_msgs in
#eval (Term.app (.lam 0 (.var 0)) [.var 1, .var 2] : Term []).size

-- a type parameter's measure is the use's own, through the copy too
inductive PT (α : Type) : Nat → Type where
  | leaf (a : α) : PT α 0
  | node {n} (cs : List (PT α n)) : PT α (n + 1)

example (n : Nat) (cs : List (PT Nat n)) : sizeOf cs < sizeOf (PT.node cs) := by
  simp; omega

/-! A recursion into an index.  A pre-term has no room for what an index already says, so
`Γ` in `ITy.base Γ` is not in it, and a measure of pre-terms would call `ITy.base Γ` smaller
than `Γ`.  The block's recursor has a hypothesis at every field, so the measure is that. -/

mutual
inductive ICtx : Type where
  | nil
  | snoc (Γ : ICtx) (A : ITy Γ)
inductive ITy : ICtx → Type where
  | base (Γ : ICtx) : ITy Γ
  | pi (Γ : ICtx) (A : ITy Γ) (B : ITy (.snoc Γ A)) : ITy Γ
end

/-- info: ITy.base.sizeOf_spec : ∀ (Γ : ICtx), sizeOf (ITy.base Γ) = 1 + sizeOf Γ -/
#guard_msgs in
#check @ITy.base.sizeOf_spec

mutual
def ICtx.count : ICtx → Nat
  | .nil => 0
  | .snoc Γ A => Γ.count + A.count + 1
def ITy.count {Γ : ICtx} : ITy Γ → Nat
  | .base Γ => Γ.count
  | .pi _ A B => A.count + B.count
end

/-- info: 3 -/
#guard_msgs in
#eval (ICtx.snoc (.snoc .nil (.base .nil)) (.base _)).count

end SizeThrough

end MumiTests.Compute
