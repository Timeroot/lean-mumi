module

@[expose] public section

/-!
Shared positive, indexed induction–recursion descriptions.

`S` indexes the mutually defined carriers. `D s` bundles all recursive outputs
for carrier `s`; it may itself contain types and values depending on those types.
Recursive occurrences are introduced only by `delta`, never by an arbitrary
endofunctor. Its continuation may inspect the recursive outputs.
-/

universe u v

namespace IR

inductive Desc {S : Type u} (D : S → Type v) (s : S) : Type (max (u + 1) v) where
  | ret (value : D s)
  | sigma (A : Type u) (next : A → Desc D s)
  | delta (A : Type u) (sort : A → S) (next : ((a : A) → D (sort a)) → Desc D s)

abbrev Signature (S : Type u) (D : S → Type v) := (s : S) → Desc D s

namespace Desc

variable {S : Type u} {D : S → Type v}

/-- One recursive argument, exposing its whole bundle of recursive outputs. -/
def one {s : S} (t : S) (next : D t → Desc D s) : Desc D s :=
  .delta PUnit (fun _ => t) (fun values => next (values PUnit.unit))

/-- Choose a constructor tag from a base-universe datatype without explicit lifts. -/
def choose {s : S} (Tag : Type) (next : Tag → Desc D s) : Desc D s :=
  .sigma (ULift.{u} Tag) (fun tag => next tag.down)

variable (X : S → Type u) (decode : (s : S) → X s → D s)

/-- Constructor arguments at a candidate family and its recursive interpretation. -/
def Args {s : S} : Desc D s → Type u
  | .ret _ => PUnit
  | .sigma A next => (a : A) × Args (next a)
  | .delta A sort next => (xs : (a : A) → X (sort a)) × Args (next (fun a => decode _ (xs a)))

/-- The simultaneous recursive outputs prescribed by one constructor layer. -/
def eval {s : S} : (d : Desc D s) → Args X decode d → D s
  | .ret value, _ => value
  | .sigma _ next, ⟨a, rest⟩ => eval (next a) rest
  | .delta _ _ next, ⟨xs, rest⟩ => eval (next (fun a => decode _ (xs a))) rest

/-- A predicate on every recursive occurrence, including those in continuations. -/
def All (P : (s : S) → X s → Prop) {s : S} : (d : Desc D s) → Args X decode d → Prop
  | .ret _, _ => True
  | .sigma _ next, ⟨a, rest⟩ => All P (next a) rest
  | .delta _ sort next, ⟨xs, rest⟩ =>
      (∀ a, P (sort a) (xs a)) ∧ All P (next (fun a => decode _ (xs a))) rest

variable {X decode}

private theorem eval_transport {B : Sort _} {P : B → Sort _} {R : Sort _}
    (f : (b : B) → P b → R) {b c : B} (h : b = c) (x : P b) :
    f c ((congrArg P h) ▸ x) = f b x := by cases h; rfl

/-- Change recursive carriers along a map preserving every recursive output. -/
def map {Y : S → Type u} {decodeY : (s : S) → Y s → D s}
    (f : (s : S) → X s → Y s) (hf : (fun s x => decodeY s (f s x)) = decode)
    {s : S} : (d : Desc D s) → Args X decode d → Args Y decodeY d
  | .ret _, _ => PUnit.unit
  | .sigma _ next, ⟨a, rest⟩ => ⟨a, map f hf (next a) rest⟩
  | .delta _ sort next, ⟨xs, rest⟩ =>
      ⟨fun a => f (sort a) (xs a),
        (congrArg (fun values => Args Y decodeY (next values))
          (congrArg (fun interpretation => fun a => interpretation (sort a) (xs a)) hf)).symm ▸
            map f hf (next (fun a => decode _ (xs a))) rest⟩

theorem eval_map {Y : S → Type u} {decodeY : (s : S) → Y s → D s}
    (f : (s : S) → X s → Y s) (hf : (fun s x => decodeY s (f s x)) = decode)
    {s : S} (d : Desc D s) (args : Args X decode d) :
    eval Y decodeY d (map f hf d args) = eval X decode d args := by
  induction d with
  | ret value => rfl
  | sigma A next ih => exact ih args.1 args.2
  | delta A sort next ih =>
    rcases args with ⟨xs, rest⟩
    dsimp only [map, eval]
    exact (eval_transport (fun values => eval Y decodeY (next values))
      (congrArg (fun interpretation => fun a => interpretation (sort a) (xs a)) hf).symm _).trans (ih _ rest)

/-- Map only the recursive occurrences in this argument, using their certificates. -/
def mapAll {Y : S → Type u} {decodeY : (s : S) → Y s → D s}
    {P : (s : S) → X s → Prop}
    (f : (s : S) → (x : X s) → P s x → Y s)
    (hf : (fun s x h => decodeY s (f s x h)) = (fun s x (_ : P s x) => decode s x))
    {s : S} : (d : Desc D s) → (args : Args X decode d) → All X decode P d args → Args Y decodeY d
  | .ret _, _, _ => PUnit.unit
  | .sigma _ next, ⟨a, rest⟩, h => ⟨a, mapAll f hf (next a) rest h⟩
  | .delta _ sort next, ⟨xs, rest⟩, h =>
      ⟨fun a => f (sort a) (xs a) (h.1 a),
        (congrArg (fun values => Args Y decodeY (next values))
          (congrArg (fun interpretation => fun a => interpretation (sort a) (xs a) (h.1 a)) hf)).symm ▸
            mapAll f hf (next (fun a => decode _ (xs a))) rest h.2⟩

theorem eval_mapAll {Y : S → Type u} {decodeY : (s : S) → Y s → D s}
    {P : (s : S) → X s → Prop}
    (f : (s : S) → (x : X s) → P s x → Y s)
    (hf : (fun s x h => decodeY s (f s x h)) = (fun s x (_ : P s x) => decode s x))
    {s : S} (d : Desc D s) (args : Args X decode d) (h : All X decode P d args) :
    eval Y decodeY d (mapAll f hf d args h) = eval X decode d args := by
  induction d with
  | ret value => rfl
  | sigma A next ih => exact ih args.1 args.2 h
  | delta A sort next ih =>
    rcases args with ⟨xs, rest⟩
    dsimp only [mapAll, eval]
    exact (eval_transport (fun values => eval Y decodeY (next values))
      (congrArg (fun interpretation => fun a => interpretation (sort a) (xs a) (h.1 a)) hf).symm _).trans
        (ih _ rest h.2)

end Desc
end IR
