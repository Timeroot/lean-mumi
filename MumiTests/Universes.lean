import Mumi

/-!
# Universe polymorphism

The universes have to be declared up front: with auto-bound implicits each
member gets its own level parameter, and a block whose members disagree about
their level parameters is rejected before we ever see it.
-/

universe u v w

/-! ## Three universes at once -/

mutual
inductive PA : Prop where
  | fromB : PB → PA
  | fromC : PC → PA
inductive PB : Type u where
  | leaf : Nat → PB
  | fromA : PA → PB
  | wrap : PB → PB
inductive PC : Type (u + 1) where
  | fromA : PA → PC
  | higher : Type u → PC
  | pair : PB → PC → PC
end

/-- info: PC.{u} : Type (u + 1) -/
#guard_msgs in
#check PC

section
variable {mA : PA.{u} → Prop} {mB : PB.{u} → Sort w} {mC : PC.{u} → Sort v}
  (fAB : (b : PB) → mB b → mA (PA.fromB b))
  (fAC : (c : PC) → mC c → mA (PA.fromC c))
  (fBl : (n : Nat) → mB (PB.leaf n))
  (fBa : (a : PA) → mA a → mB (PB.fromA a))
  (fBw : (b : PB) → mB b → mB (PB.wrap b))
  (fCa : (a : PA) → mA a → mC (PC.fromA a))
  (fCh : (t : Type u) → mC (PC.higher t))
  (fCp : (b : PB) → (c : PC) → mB b → mC c → mC (PC.pair b c))

-- the iota rule holds at a *variable* universe, not just at instantiations of it
example (b : PB.{u}) (c : PC.{u}) :
    @PC.mutualRec mA mB mC fAB fAC fBl fBa fBw fCa fCh fCp (PC.pair b c)
      = fCp b c (@PB.mutualRec mA mB mC fAB fAC fBl fBa fBw fCa fCh fCp b)
               (@PC.mutualRec mA mB mC fAB fAC fBl fBa fBw fCa fCh fCp c) := rfl
end

def cDepth : PC.{u} → Nat :=
  @PC.mutualRec (fun _ => True) (fun _ => Nat) (fun _ => Nat)
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun n => n) (fun _ _ => 0) (fun _ ih => ih + 1)
    (fun _ _ => 0) (fun _ => 0) (fun _ _ ihb ihc => ihb + ihc)

-- a universe-polymorphic definition has to be instantiated to be evaluated
/-- info: 5 -/
#guard_msgs in
#eval cDepth.{0} (PC.pair (PB.wrap (PB.leaf 4)) (PC.fromA (PA.fromB (PB.leaf 3))))

/-- info: 5 -/
#guard_msgs in
#eval cDepth.{3} (PC.pair (PB.wrap (PB.leaf 4)) (PC.fromA (PA.fromB (PB.leaf 3))))

/-- info: 'cDepth' does not depend on any axioms -/
#guard_msgs in
#print axioms cDepth

/-! ## The `csimp` pair is polymorphic too

`isConstantReplacement?` insists that the two sides of the equation be bare
constants with the same level parameters, so the theorem is stated about the
whole polymorphic family rather than an instantiation of it. -/

/-- info: PB.mutualRec.eq_impl : @PB.mutualRec = @PB.mutualRec.impl -/
#guard_msgs in
#check @PB.mutualRec.eq_impl

/-- info: 'PB.mutualRec.impl' does not depend on any axioms -/
#guard_msgs in
#print axioms PB.mutualRec.impl

/-! ## `imax` in a field

A dependent function `(a : α) → P a` lives at `Sort (imax (u+1) v)`, which is
`Prop` when `v` is.  That is fine here: it is the *member's* universe that has
to be decidably `Prop`-or-not, and `IB` is declared at `Type (max u v)`. -/

mutual
inductive IA (α : Type u) (P : α → Sort v) : Prop where
  | mk : IB α P → IA α P
inductive IB (α : Type u) (P : α → Sort v) : Type (max u v) where
  | fn : ((a : α) → P a) → IB α P
  | back : IA α P → IB α P
  | tag : Nat → IB α P
end

/-- info: IB.{u, v} (α : Type u) (P : α → Sort v) : Type (max u v) -/
#guard_msgs in
#check IB

def iTag {α : Type u} {P : α → Sort v} : IB α P → Nat :=
  @IB.mutualRec α P (fun _ => True) (fun _ => Nat)
    (fun _ _ => trivial) (fun _ => 0) (fun _ _ => 1) (fun n => n)

/-- info: 7 -/
#guard_msgs in
#eval iTag.{0, 0} (α := Nat) (P := fun _ => True) (IB.tag 7)

-- at a `Prop`-valued `P`, so the `imax` collapses to `0` and the field is erased
/-- info: 0 -/
#guard_msgs in
#eval iTag.{0, 0} (α := Nat) (P := fun _ => True) (IB.fn fun _ => trivial)

-- and at a `Type`-valued `P`, so it does not
/-- info: 0 -/
#guard_msgs in
#eval iTag.{0, 1} (α := Nat) (P := fun _ => Nat) (IB.fn fun n => n)

/-! ## Three universe parameters, used unevenly

`MB` uses only `u` and `MC` uses all three.  They are in different components of
the data-only dependency graph, which is what lets them sit at different
universes.  Note that a field of type `Type v` needs the member at `v + 1`. -/

-- all three appear only inside the `max`, which is exactly what is being tested
set_option linter.checkUnivs false in
mutual
inductive MA : Prop where
  | fromB : MB → MA
  | fromC : MC → MA
inductive MB : Type u where
  | leaf : Nat → MB
  | fromA : MA → MB
inductive MC : Type (max u (max (v + 1) (w + 1))) where
  | fromB : MB → MC
  | big : Type v → Type w → MC
end

/-- info: MC.{u, v, w} : Type (max u (v + 1) (w + 1)) -/
#guard_msgs in
#check MC

def mTag : MC.{u, v, w} → Nat :=
  @MC.mutualRec (fun _ => True) (fun _ => Nat) (fun _ => Nat)
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun n => n) (fun _ _ => 0) (fun _ ih => ih + 1) (fun _ _ => 0)

/-- info: 5 -/
#guard_msgs in
#eval mTag.{0, 0, 0} (MC.fromB (MB.leaf 4))

/-! ## Members of one data component share a universe

`KB` and `KC` hold each other, so each one's universe has to be at least the
other's -- they have to be equal.  That still leaves them polymorphic. -/

mutual
inductive KA : Prop where
  | mk : KB → KA
inductive KB : Type u where
  | leaf : Nat → KB
  | toC : KC → KB
inductive KC : Type u where
  | fromB : KB → KC
  | fromA : KA → KC
end

def kTag : KB.{u} → Nat :=
  @KB.mutualRec (fun _ => True) (fun _ => Nat) (fun _ => Nat)
    (fun _ _ => trivial) (fun n => n) (fun _ ih => ih + 1)
    (fun _ ih => ih + 1) (fun _ _ => 0)

/-- info: 8 -/
#guard_msgs in
#eval kTag.{0} (KB.toC (KC.fromB (KB.leaf 6)))

/-! ## `Sort (max 1 u)`

Not syntactically `Type _`, but never `Prop` either, so it is a data member. -/

mutual
inductive SA : Prop where
  | mk : SB → SA
inductive SB : Sort (max 1 u) where
  | leaf : Nat → SB
  | fromA : SA → SB
end

/-- info: SB.{u} : Sort (max 1 u) -/
#guard_msgs in
#check SB

def sbTag : SB.{u} → Nat :=
  @SB.mutualRec (fun _ => True) (fun _ => Nat) (fun _ _ => trivial)
    (fun n => n) (fun _ _ => 0)

/-- info: 4 -/
#guard_msgs in
#eval sbTag.{0} (SB.leaf 4)

/-! ## Indices and universe polymorphism together -/

mutual
inductive XEv : Nat → Prop where
  | zero : XEv 0
  | succ : (n : Nat) → XOd n → XEv (n + 1)
inductive XOd : Nat → Type u where
  | one : XOd 1
  | succ : (n : Nat) → XEv (n + 1) → XOd n → Nat → XOd (n + 2)
end

/-- info: XOd.{u} : Nat → Type u -/
#guard_msgs in
#check XOd

def xSum : (n : Nat) → XOd.{u} n → Nat :=
  fun n t => @XOd.mutualRec (fun _ _ => True) (fun _ _ => Nat)
    trivial (fun _ _ _ => trivial) 0 (fun _ _ _ k _ ih => ih + k) n t

/-- info: 10 -/
#guard_msgs in
#eval xSum.{0} 5 (.succ 3 (.succ 3 (.succ 1 (.succ 1 .one) .one 4)) (.succ 1 (.succ 1 .one) .one 4) 6)

/-! ## Small elimination at a variable universe

Universes are derived per member, elimination is not: the motives may all land
in `Prop` whatever `u` is. -/

example (b : PB.{u}) : True :=
  @PB.mutualRec (fun _ => True) (fun _ => True) (fun _ => True)
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial)
    (fun _ _ => trivial) (fun _ => trivial) (fun _ _ _ _ => trivial) b
