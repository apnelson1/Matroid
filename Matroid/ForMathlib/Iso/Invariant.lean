/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Matroid.ForMathlib.Iso.Equiv

/-!
# Generic isomorphism-invariant observables

An `Observable F` is a section of an object-indexed family. `IsoInvariant f f'` says that the two
sections commute with a chosen weak `IsoEquiv`. No identity or composition law is required.

This file also contains the structural/logical closure machinery shared by graph and matroid
invariants, including recursive quantification over transported types and bounded quantification
through transported supported subtypes.
-/

@[expose] public section

open Set Function

/-- A chosen element in every fiber of an object-indexed family. -/
abbrev Observable {C : Type*} (F : Family C) := (X : C) → F X

variable {C₁ : Type*} {C₂ : Type*} [R : IsoRel C₁ C₂]

/-- Two observables are invariant when they commute with the chosen equivalences along every
chosen object isomorphism. -/
class IsoInvariant {F : Family C₁} {F' : Family C₂} [e : IsoEquiv F F']
    (f : Observable F) (f' : Observable F') : Prop where
  map_eq : ∀ {X : C₁} {Y : C₂} (i : R.Iso X Y), e.map i (f X) = f' Y

namespace IsoInvariant

/-- Precompose an invariant observable by an isomorphism-preserving object map.

The result is stated over the explicit `Reindex` family so the canonical transport is retained
rather than reconstructed from an expanded lambda. -/
theorem reindex {D₁ : Type*} {D₂ : Type*} [rD : IsoRel D₁ D₂]
    {f : C₁ → D₁} {f' : C₂ → D₂} [m : IsoMap f f'] {F : Family D₁} {F' : Family D₂} [IsoEquiv F F']
    {x : Observable F} {x' : Observable F'} [h : IsoInvariant x x'] :
    IsoInvariant (F := Reindex f F) (F' := Reindex f' F')
      (fun X ↦ x (f X)) (fun Y ↦ x' (f' Y)) where
  map_eq i := h.map_eq (m.map i)

/-! ## Constructors and pointwise evaluation -/

section SortValued

variable {A : Family C₁} {A' : Family C₂} {B : Family C₁} {B' : Family C₂}
  {D : Family C₁} {D' : Family C₂} [a : IsoEquiv A A'] [b : IsoEquiv B B'] [d : IsoEquiv D D']

/-- Construct invariance of a function-valued observable from its pointwise commuting square. -/
theorem of_map_apply (f : Observable (fun X ↦ A X → B X)) (f' : Observable (fun Y ↦ A' Y → B' Y))
    (h : ∀ {X : C₁} {Y : C₂} (i : R.Iso X Y) (x : A X), b.map i (f X x) = f' Y (a.map i x)) :
    IsoInvariant f f' where
  map_eq i := by
    funext y
    obtain ⟨x, rfl⟩ := (a.map i).surjective y
    simpa only [IsoEquiv.map_arrow_apply] using h i x

/-- Binary pointwise constructor. -/
theorem of_map_apply₂ (f : Observable (fun X ↦ A X → B X → D X))
    (f' : Observable (fun Y ↦ A' Y → B' Y → D' Y))
    (h : ∀ {X : C₁} {Y : C₂} (i : R.Iso X Y) (x : A X) (y : B X),
      d.map i (f X x y) = f' Y (a.map i x) (b.map i y)) : IsoInvariant f f' := by
  apply of_map_apply f f'
  intro X Y i x
  funext y'
  obtain ⟨y, rfl⟩ := (b.map i).surjective y'
  simpa only [IsoEquiv.map_arrow_apply] using h i x y

/-- Evaluate an invariant function-valued observable at a transported argument. -/
theorem map_apply {f : Observable (fun X ↦ A X → B X)}
    {f' : Observable (fun Y ↦ A' Y → B' Y)} [IsoInvariant f f']
    {X : C₁} {Y : C₂} (i : R.Iso X Y) (x : A X) : b.map i (f X x) = f' Y (a.map i x) := by
  simpa only [IsoEquiv.map_arrow_apply] using
    congrFun (IsoInvariant.map_eq (f := f) (f' := f') i) (a.map i x)

/-- Evaluate an invariant binary function at transported arguments. -/
theorem map_apply₂ {f : Observable (fun X ↦ A X → B X → D X)}
    {f' : Observable (fun Y ↦ A' Y → B' Y → D' Y)} [IsoInvariant f f']
    {X : C₁} {Y : C₂} (i : R.Iso X Y) (x : A X) (y : B X) :
    d.map i (f X x y) = f' Y (a.map i x) (b.map i y) := by
  simpa only [IsoEquiv.map_arrow_apply] using (congrFun
    (map_apply (B := fun X ↦ B X → D X) (B' := fun Y ↦ B' Y → D' Y) i x) (b.map i y))

/-- Build a proposition-valued invariant directly from an iff. -/
theorem of_iff (P : Observable (fun _ : C₁ ↦ Prop)) (P' : Observable (fun _ : C₂ ↦ Prop))
    (h : ∀ {X : C₁} {Y : C₂}, R.Iso X Y → (P X ↔ P' Y)) : IsoInvariant P P' where
  map_eq i := by
    change P _ = P' _
    exact propext (h i)

/-- Construct invariance of a unary predicate from its transported iff. -/
theorem of_iff_map (P : Observable (fun X ↦ A X → Prop)) (P' : Observable (fun Y ↦ A' Y → Prop))
    (h : ∀ {X : C₁} {Y : C₂} (i : R.Iso X Y) (x : A X), P X x ↔ P' Y (a.map i x)) :
    IsoInvariant P P' := of_map_apply P P' fun i x ↦ propext (h i x)

/-- Construct invariance of a binary predicate from its transported iff. -/
theorem of_iff_map₂ (P : Observable (fun X ↦ A X → B X → Prop))
    (P' : Observable (fun Y ↦ A' Y → B' Y → Prop))
    (h : ∀ {X : C₁} {Y : C₂} (i : R.Iso X Y) (x : A X) (y : B X),
      P X x y ↔ P' Y (a.map i x) (b.map i y)) : IsoInvariant P P' :=
  of_map_apply₂ P P' fun i x y ↦ propext (h i x y)

/-- A proposition-valued invariant supplies an iff along any isomorphism. -/
theorem iff_of_iso {P : Observable (fun _ : C₁ ↦ Prop)} {P' : Observable (fun _ : C₂ ↦ Prop)}
    [IsoInvariant P P'] {X : C₁} {Y : C₂} (i : R.Iso X Y) : P X ↔ P' Y := by
  have h := IsoInvariant.map_eq (f := P) (f' := P') i
  change P X = P' Y at h
  simp only [h]

/-- Pointwise iff for an invariant unary predicate. -/
theorem iff_map {P : Observable (fun X ↦ A X → Prop)} {P' : Observable (fun Y ↦ A' Y → Prop)}
    [IsoInvariant P P'] {X : C₁} {Y : C₂} (i : R.Iso X Y) (x : A X) : P X x ↔ P' Y (a.map i x) := by
  have h := map_apply (A := A) (A' := A') (B := fun _ ↦ Prop) (B' := fun _ ↦ Prop)
    (f := P) (f' := P') i x
  change P X x = P' Y (a.map i x) at h
  simp only [h]

/-- Pointwise iff phrased at an arbitrary target argument.  This is often the most convenient
form when recovering map-style APIs from an intrinsic equivalence. -/
theorem iff_comap {P : Observable (fun X ↦ A X → Prop)} {P' : Observable (fun Y ↦ A' Y → Prop)}
    [IsoInvariant P P'] {X : C₁} {Y : C₂} (i : R.Iso X Y) (y : A' Y) :
    P X ((a.map i).symm y) ↔ P' Y y := by
  simpa using (iff_map (P := P) (P' := P') i ((a.map i).symm y))

/-- Pointwise iff for an invariant binary predicate. -/
theorem iff_map₂ {P : Observable (fun X ↦ A X → B X → Prop)}
    {P' : Observable (fun Y ↦ A' Y → B' Y → Prop)} [IsoInvariant P P']
    {X : C₁} {Y : C₂} (i : R.Iso X Y) (x : A X) (y : B X) :
    P X x y ↔ P' Y (a.map i x) (b.map i y) := by
  have h := map_apply₂ (A := A) (A' := A') (B := B) (B' := B')
    (D := fun _ ↦ Prop) (D' := fun _ ↦ Prop) (f := P) (f' := P') i x y
  change P X x y = P' Y (a.map i x) (b.map i y) at h
  simp only [h]

end SortValued

/-! ## Generic observable combinators -/

section SortValued

variable {A : Family C₁} {A' : Family C₂} {B : Family C₁} {B' : Family C₂}
  [a : IsoEquiv A A'] [b : IsoEquiv B B']

/-- Applying an invariant function-valued observable to an invariant argument preserves
invariance. This is the generic form of composition used by many domain-specific constructions. -/
theorem app (f : Observable (fun X ↦ A X → B X)) (f' : Observable (fun Y ↦ A' Y → B' Y))
    (x : Observable A) (x' : Observable A') [IsoInvariant f f'] [IsoInvariant x x'] :
    IsoInvariant (fun X ↦ f X (x X)) (fun Y ↦ f' Y (x' Y)) where
  map_eq i := by
    rw [map_apply (f := f) (f' := f') i (x _), IsoInvariant.map_eq (f := x) (f' := x') i]

end SortValued

section TypeValued

variable {A : TypeFamily C₁} {A' : TypeFamily C₂} {B : TypeFamily C₁} {B' : TypeFamily C₂}
  [a : IsoEquiv A A'] [b : IsoEquiv B B']

/-- Pair two invariant observables. -/
theorem pair (x : Observable A) (x' : Observable A') (y : Observable B) (y' : Observable B')
    [IsoInvariant x x'] [IsoInvariant y y'] :
    IsoInvariant (fun X ↦ (x X, y X)) (fun Y ↦ (x' Y, y' Y)) where
  map_eq i := by
    change (a.map i (x _), b.map i (y _)) = (x' _, y' _)
    rw [IsoInvariant.map_eq (f := x) (f' := x') i, IsoInvariant.map_eq (f := y) (f' := y') i]

/-- Turn an invariant predicate into the invariant set it defines. -/
theorem setOf (P : Observable (fun X ↦ A X → Prop))
    (P' : Observable (fun Y ↦ A' Y → Prop)) [IsoInvariant P P'] :
    IsoInvariant (fun X ↦ {x : A X | P X x}) (fun Y ↦ {y : A' Y | P' Y y}) where
  map_eq i := by
    change (a.map i '' {x | P _ x}) = {y | P' _ y}
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (iff_map (P := P) (P' := P') i x).mp hx
    · intro hy
      let x := (a.map i).symm y
      refine ⟨x, (iff_map (P := P) (P' := P') i x).mpr ?_, ?_⟩
      · simpa [x] using hy
      · simp [x]

end TypeValued

end IsoInvariant

/-! ## Generic invariant observables -/

instance instIsoInvariantConst (S : Sort*) (x : S) :
    IsoInvariant (F := fun _ : C₁ ↦ S) (F' := fun _ : C₂ ↦ S) (fun _ ↦ x) (fun _ ↦ x) where
  map_eq _ := rfl

instance instIsoInvariantId (A : Family C₁) (A' : Family C₂) [IsoEquiv A A'] :
    IsoInvariant (fun X ↦ fun x : A X ↦ x) (fun Y ↦ fun y : A' Y ↦ y) :=
  IsoInvariant.of_map_apply _ _ fun _ _ ↦ rfl

/-! ## Proposition algebra -/

section PropAlgebra

variable (P Q : Observable (fun _ : C₁ ↦ Prop)) (P' Q' : Observable (fun _ : C₂ ↦ Prop))
  [IsoInvariant P P'] [IsoInvariant Q Q']

instance instIsoInvariantNot : IsoInvariant (fun X ↦ ¬ P X) (fun Y ↦ ¬ P' Y) :=
  IsoInvariant.of_iff _ _ fun i ↦ not_congr (IsoInvariant.iff_of_iso i)

instance instIsoInvariantAnd : IsoInvariant (fun X ↦ P X ∧ Q X) (fun Y ↦ P' Y ∧ Q' Y) :=
  IsoInvariant.of_iff _ _ fun i ↦
    and_congr (IsoInvariant.iff_of_iso (P := P) i) (IsoInvariant.iff_of_iso (P := Q) i)

instance instIsoInvariantOr : IsoInvariant (fun X ↦ P X ∨ Q X) (fun Y ↦ P' Y ∨ Q' Y) :=
  IsoInvariant.of_iff _ _ fun i ↦
    or_congr (IsoInvariant.iff_of_iso (P := P) i) (IsoInvariant.iff_of_iso (P := Q) i)

instance instIsoInvariantImp : IsoInvariant (fun X ↦ P X → Q X) (fun Y ↦ P' Y → Q' Y) :=
  IsoInvariant.of_iff _ _ fun i ↦
    imp_congr (IsoInvariant.iff_of_iso (P := P) i) (IsoInvariant.iff_of_iso (P := Q) i)

instance instIsoInvariantIff : IsoInvariant (fun X ↦ P X ↔ Q X) (fun Y ↦ P' Y ↔ Q' Y) :=
  IsoInvariant.of_iff _ _ fun i ↦
    iff_congr (IsoInvariant.iff_of_iso (P := P) i) (IsoInvariant.iff_of_iso (P := Q) i)

end PropAlgebra

/-! ## Intrinsic equality and set relations -/

section SetRelations

variable (A : TypeFamily C₁) (A' : TypeFamily C₂) [a : IsoEquiv A A']

instance instIsoInvariantEq :
    IsoInvariant (fun X (x y : A X) ↦ x = y) (fun Y (x y : A' Y) ↦ x = y) :=
  IsoInvariant.of_iff_map₂ _ _ fun i x y ↦
    ⟨congrArg (a.map i), fun h ↦ (a.map i).injective (by simpa using h)⟩

instance instIsoInvariantMem : IsoInvariant (fun X (x : A X) (S : Set (A X)) ↦ x ∈ S)
      (fun Y (x : A' Y) (S : Set (A' Y)) ↦ x ∈ S) := IsoInvariant.of_iff_map₂ _ _ fun i x S ↦ by
    change x ∈ S ↔ a.map i x ∈ a.map i '' S
    simp

instance instIsoInvariantSubset : IsoInvariant (fun X (S T : Set (A X)) ↦ S ⊆ T)
      (fun Y (S T : Set (A' Y)) ↦ S ⊆ T) := IsoInvariant.of_iff_map₂ _ _ fun i S T ↦ by
    change S ⊆ T ↔ a.map i '' S ⊆ a.map i '' T
    exact ((a.map i).injective.injOn.image_subset_image_iff (subset_univ S) (subset_univ T)).symm

end SetRelations

/-! ## Quantifier closure -/

section Quantifiers

variable (A : TypeFamily C₁) (A' : TypeFamily C₂) [a : IsoEquiv A A']
  (P : Observable (fun X ↦ A X → Prop)) (P' : Observable (fun Y ↦ A' Y → Prop)) [IsoInvariant P P']

instance instIsoInvariantForall : IsoInvariant (fun X ↦ ∀ x, P X x) (fun Y ↦ ∀ y, P' Y y) := by
  refine IsoInvariant.of_iff _ _ fun i ↦ (⟨fun h y ↦ ?_,
    fun h x ↦ (IsoInvariant.iff_map i x).mpr (h (a.map i x))⟩)
  obtain ⟨x, rfl⟩ := (a.map i).surjective y
  exact (IsoInvariant.iff_map i x).mp (h x)

instance instIsoInvariantExists : IsoInvariant (fun X ↦ ∃ x, P X x) (fun Y ↦ ∃ y, P' Y y) := by
  refine IsoInvariant.of_iff _ _ fun i ↦ (⟨fun ⟨x, hx⟩ ↦ ⟨a.map i x,
    (IsoInvariant.iff_map i x).mp hx⟩, fun ⟨y, hy⟩ ↦ ?_⟩)
  let x := (a.map i).symm y
  refine ⟨x, (IsoInvariant.iff_map (P := P) (P' := P') i x).mpr ?_⟩
  simpa [x] using hy

end Quantifiers

section QuantifiersPointwise

variable (Ctx : TypeFamily C₁) (Ctx' : TypeFamily C₂) (A : TypeFamily C₁) (A' : TypeFamily C₂)
  [c : IsoEquiv Ctx Ctx'] [a : IsoEquiv A A'] (P : Observable (fun X ↦ Ctx X → A X → Prop))
  (P' : Observable (fun Y ↦ Ctx' Y → A' Y → Prop)) [IsoInvariant P P']

instance instIsoInvariantForallPointwise :
    IsoInvariant (fun X z ↦ ∀ x, P X z x) (fun Y z ↦ ∀ y, P' Y z y) := by
  refine IsoInvariant.of_map_apply _ _ fun i z ↦ propext ⟨fun h y ↦ ?_,
    fun h x ↦ (IsoInvariant.iff_map₂ i z x).mpr (h (a.map i x))⟩
  obtain ⟨x, rfl⟩ := (a.map i).surjective y
  exact (IsoInvariant.iff_map₂ i z x).mp (h x)

instance instIsoInvariantExistsPointwise :
    IsoInvariant (fun X z ↦ ∃ x, P X z x) (fun Y z ↦ ∃ y, P' Y z y) := by
  refine IsoInvariant.of_map_apply _ _ fun i z ↦ propext
    ⟨fun ⟨x, hx⟩ ↦ ⟨a.map i x, (IsoInvariant.iff_map₂ i z x).mp hx⟩, fun ⟨y, hy⟩ ↦ ?_⟩
  let x := (a.map i).symm y
  refine ⟨x, (IsoInvariant.iff_map₂ (P := P) (P' := P') i z x).mpr ?_⟩
  simpa [x] using hy

end QuantifiersPointwise

/-! ## Generic bounded quantifiers

The ambient family itself need not transport. Only the subtype cut out by the guard must have an
`IsoEquiv`. This is what handles ambient graph vertices and ambient matroid elements uniformly.
-/

section Bounded

variable (A : TypeFamily C₁) (A' : TypeFamily C₂)
  (B : Observable (fun X ↦ A X → Prop)) (B' : Observable (fun Y ↦ A' Y → Prop))
  [s : IsoEquiv (fun X ↦ {x : A X // B X x}) (fun Y ↦ {y : A' Y // B' Y y})]
  (P : Observable (fun X ↦ A X → Prop)) (P' : Observable (fun Y ↦ A' Y → Prop))
  [IsoInvariant (fun X (x : {x : A X // B X x}) ↦ P X x.1)
    (fun Y (y : {y : A' Y // B' Y y}) ↦ P' Y y.1)]

instance instIsoInvariantForallBounded :
    IsoInvariant (fun X ↦ ∀ x, B X x → P X x) (fun Y ↦ ∀ y, B' Y y → P' Y y) := by
  refine IsoInvariant.of_iff _ _ fun i ↦ ⟨fun h y hy ↦ ?_, fun h x hx ↦ ?_⟩
  · let sy : {z : A' _ // B' _ z} := ⟨y, hy⟩
    let sx := (s.map i).symm sy
    simpa [sx, sy] using ((IsoInvariant.iff_map (P := fun X (x : {x : A X // B X x}) ↦ P X x.1)
      (P' := fun Y (y : {y : A' Y // B' Y y}) ↦ P' Y y.1) i sx).mp (h sx.1 sx.2))
  let sx : {z : A _ // B _ z} := ⟨x, hx⟩
  exact (IsoInvariant.iff_map (P := fun X (z : {z : A X // B X z}) ↦ P X z.1)
    (P' := fun Y (z : {z : A' Y // B' Y z}) ↦ P' Y z.1) i sx).mpr (h (s.map i sx).1 (s.map i sx).2)

instance instIsoInvariantExistsBounded :
    IsoInvariant (fun X ↦ ∃ x, B X x ∧ P X x) (fun Y ↦ ∃ y, B' Y y ∧ P' Y y) := by
  refine IsoInvariant.of_iff _ _ fun i ↦ ⟨fun ⟨x, hxB, hxP⟩ ↦ ?_, fun ⟨y, hyB, hyP⟩ ↦ ?_⟩
  · let sx : {z : A _ // B _ z} := ⟨x, hxB⟩
    exact ⟨(s.map i sx).1, (s.map i sx).2, ((IsoInvariant.iff_map
      (P := fun X (z : {z : A X // B X z}) ↦ P X z.1)
      (P' := fun Y (z : {z : A' Y // B' Y z}) ↦ P' Y z.1) i sx).mp hxP)⟩
  let sy : {z : A' _ // B' _ z} := ⟨y, hyB⟩
  let sx := (s.map i).symm sy
  refine ⟨sx.1, sx.2, ?_⟩
  apply (IsoInvariant.iff_map (P := fun X (z : {z : A X // B X z}) ↦ P X z.1)
    (P' := fun Y (z : {z : A' Y // B' Y z}) ↦ P' Y z.1) i sx).mpr
  simpa [sx, sy] using hyP

end Bounded

section BoundedPointwise

variable (Ctx : TypeFamily C₁) (Ctx' : TypeFamily C₂) [c : IsoEquiv Ctx Ctx']
  (A : TypeFamily C₁) (A' : TypeFamily C₂)
  (B : Observable (fun X ↦ A X → Prop)) (B' : Observable (fun Y ↦ A' Y → Prop))
  [s : IsoEquiv (fun X ↦ {x : A X // B X x}) (fun Y ↦ {y : A' Y // B' Y y})]
  (P : Observable (fun X ↦ Ctx X → A X → Prop)) (P' : Observable (fun Y ↦ Ctx' Y → A' Y → Prop))
  [IsoInvariant (fun X (z : Ctx X) (x : {x : A X // B X x}) ↦ P X z x.1)
    (fun Y (z : Ctx' Y) (y : {y : A' Y // B' Y y}) ↦ P' Y z y.1)]

instance instIsoInvariantForallBoundedPointwise : IsoInvariant (fun X z ↦ ∀ x, B X x → P X z x)
      (fun Y z ↦ ∀ y, B' Y y → P' Y z y) := IsoInvariant.of_map_apply _ _ fun i z ↦ by
    apply propext
    constructor
    · intro h y hy
      let sy : {w : A' _ // B' _ w} := ⟨y, hy⟩
      let sx := (s.map i).symm sy
      simpa [sx, sy] using ((IsoInvariant.iff_map₂
        (P := fun X (z : Ctx X) (x : {x : A X // B X x}) ↦ P X z x.1)
        (P' := fun Y (z : Ctx' Y) (y : {y : A' Y // B' Y y}) ↦ P' Y z y.1)
        i z sx).mp (h sx.1 sx.2))
    · intro h x hx
      let sx : {w : A _ // B _ w} := ⟨x, hx⟩
      exact (IsoInvariant.iff_map₂
        (P := fun X (z : Ctx X) (w : {w : A X // B X w}) ↦ P X z w.1)
        (P' := fun Y (z : Ctx' Y) (w : {w : A' Y // B' Y w}) ↦ P' Y z w.1)
        i z sx).mpr (h (s.map i sx).1 (s.map i sx).2)

instance instIsoInvariantExistsBoundedPointwise : IsoInvariant (fun X z ↦ ∃ x, B X x ∧ P X z x)
      (fun Y z ↦ ∃ y, B' Y y ∧ P' Y z y) := IsoInvariant.of_map_apply _ _ fun i z ↦ by
    apply propext
    constructor
    · rintro ⟨x, hxB, hxP⟩
      let sx : {w : A _ // B _ w} := ⟨x, hxB⟩
      exact ⟨(s.map i sx).1, (s.map i sx).2, ((IsoInvariant.iff_map₂
        (P := fun X (z : Ctx X) (w : {w : A X // B X w}) ↦ P X z w.1)
        (P' := fun Y (z : Ctx' Y) (w : {w : A' Y // B' Y w}) ↦ P' Y z w.1) i z sx).mp hxP)⟩
    · rintro ⟨y, hyB, hyP⟩
      let sy : {w : A' _ // B' _ w} := ⟨y, hyB⟩
      let sx := (s.map i).symm sy
      refine ⟨sx.1, sx.2, ?_⟩
      apply (IsoInvariant.iff_map₂ (P := fun X (z : Ctx X) (w : {w : A X // B X w}) ↦ P X z w.1)
        (P' := fun Y (z : Ctx' Y) (w : {w : A' Y // B' Y w}) ↦ P' Y z w.1) i z sx).mpr
      simpa [sx, sy] using hyP

end BoundedPointwise

/-! ## Higher-level closure shared by the old graph/matroid use-cases -/

namespace IsoInvariant

/-- Postcompose a fixed-output invariant observable by an arbitrary fixed function.
This subsumes the `InvariantFun.comp_right` use-case from the old matroid API. -/
theorem comp_right {A : Family C₁} {A' : Family C₂} [IsoEquiv A A'] {B : Sort*} {D : Sort*}
    (f : Observable (fun X ↦ A X → B)) (f' : Observable (fun Y ↦ A' Y → B)) [IsoInvariant f f']
    (s : B → D) : IsoInvariant (fun X x ↦ s (f X x)) (fun Y y ↦ s (f' Y y)) :=
  of_map_apply _ _ fun i x ↦ by
    have h := map_apply (f := f) (f' := f') i x
    change f _ x = f' _ (_root_.IsoEquiv.map i x) at h
    exact congrArg s h

/-- Precompose an invariant function-valued observable by an invariant endomorphism-valued
observable. This is the intrinsic version of the old `InvariantFun.comp` pattern. -/
theorem comp {A : Family C₁} {A' : Family C₂} {B : Family C₁} {B' : Family C₂}
    [IsoEquiv A A'] [IsoEquiv B B'] (f : Observable (fun X ↦ A X → B X))
    (f' : Observable (fun Y ↦ A' Y → B' Y)) [IsoInvariant f f'] (a : Observable (fun X ↦ A X → A X))
    (a' : Observable (fun Y ↦ A' Y → A' Y)) [IsoInvariant a a'] :
    IsoInvariant (fun X x ↦ f X (a X x)) (fun Y y ↦ f' Y (a' Y y)) := of_map_apply _ _ fun i x ↦ by
    rw [map_apply (f := f) (f' := f') i (a _ x), map_apply (f := a) (f' := a') i x]

/-- Combine two invariant function-valued observables sharing the same transported argument by
an arbitrary fixed binary operation. This is the intrinsic version of the old
`InvariantFun.combine`. -/
theorem combine {Ctx : Family C₁} {Ctx' : Family C₂} [c : IsoEquiv Ctx Ctx']
    {A : Sort*} {B : Sort*} {D : Sort*} (f : Observable (fun X ↦ Ctx X → A))
    (f' : Observable (fun Y ↦ Ctx' Y → A)) (g : Observable (fun X ↦ Ctx X → B))
    (g' : Observable (fun Y ↦ Ctx' Y → B))
    [IsoInvariant f f'] [IsoInvariant g g'] (op : A → B → D) : IsoInvariant
      (fun X x ↦ op (f X x) (g X x)) (fun Y y ↦ op (f' Y y) (g' Y y)) :=
  of_map_apply _ _ fun i x ↦ by
    have hf := map_apply (f := f) (f' := f') i x
    have hg := map_apply (f := g) (f' := g') i x
    change f _ x = f' _ (c.map i x) at hf
    change g _ x = g' _ (c.map i x) at hg
    change op (f _ x) (g _ x) = op (f' _ (c.map i x)) (g' _ (c.map i x))
    rw [hf, hg]

end IsoInvariant

/-! ## Generic set constructions -/

section SetConstructions

variable (A : TypeFamily C₁) (A' : TypeFamily C₂) [a : IsoEquiv A A']
  (P : Observable (fun X ↦ Set (A X) → Prop))
  (P' : Observable (fun Y ↦ Set (A' Y) → Prop)) [IsoInvariant P P']

instance instIsoInvariantSetEmpty :
    IsoInvariant (fun X ↦ (∅ : Set (A X))) (fun Y ↦ (∅ : Set (A' Y))) where
  map_eq i := by
    change a.map i '' ∅ = ∅
    simp

instance instIsoInvariantSetUniv :
    IsoInvariant (fun X ↦ (Set.univ : Set (A X))) (fun Y ↦ (Set.univ : Set (A' Y))) where
  map_eq i := by
    change a.map i '' Set.univ = Set.univ
    apply Set.eq_univ_of_forall
    intro y
    obtain ⟨x, rfl⟩ := (a.map i).surjective y
    exact ⟨x, Set.mem_univ x, rfl⟩

/-- Complement of an intrinsic set is invariant under equivalence. -/
instance instIsoInvariantSetCompl :
    IsoInvariant (fun X (S : Set (A X)) ↦ Sᶜ) (fun Y (S : Set (A' Y)) ↦ Sᶜ) :=
  IsoInvariant.of_map_apply _ _ fun i S ↦ by
    change a.map i '' Sᶜ = (a.map i '' S)ᶜ
    ext y
    obtain ⟨x, rfl⟩ := (a.map i).surjective y
    simp

instance instIsoInvariantSetUnion : IsoInvariant (fun X (S T : Set (A X)) ↦ S ∪ T)
      (fun Y (S T : Set (A' Y)) ↦ S ∪ T) := IsoInvariant.of_map_apply₂ _ _ fun i S T ↦ by
    change a.map i '' (S ∪ T) = (a.map i '' S) ∪ (a.map i '' T)
    ext y
    obtain ⟨x, rfl⟩ := (a.map i).surjective y
    simp

instance instIsoInvariantSetInter : IsoInvariant (fun X (S T : Set (A X)) ↦ S ∩ T)
      (fun Y (S T : Set (A' Y)) ↦ S ∩ T) := IsoInvariant.of_map_apply₂ _ _ fun i S T ↦ by
    change a.map i '' (S ∩ T) = (a.map i '' S) ∩ (a.map i '' T)
    ext y
    obtain ⟨x, rfl⟩ := (a.map i).surjective y
    simp

instance instIsoInvariantSetDiff : IsoInvariant (fun X (S T : Set (A X)) ↦ S \ T)
      (fun Y (S T : Set (A' Y)) ↦ S \ T) := IsoInvariant.of_map_apply₂ _ _ fun i S T ↦ by
    change a.map i '' (S \ T) = (a.map i '' S) \ (a.map i '' T)
    ext y
    obtain ⟨x, rfl⟩ := (a.map i).surjective y
    simp

/-- `encard` is generic on any transported intrinsic set; it is not matroid-specific. -/
instance instIsoInvariantSetEncard : IsoInvariant (fun X (_S : Set (A X)) ↦ (_S).encard)
      (fun Y (_S : Set (A' Y)) ↦ (_S).encard) := IsoInvariant.of_map_apply _ _ fun i S ↦ by
    simp only [IsoEquiv.map_const, IsoEquiv.map_set]
    exact ((a.map i).injective.encard_image S).symm

/-! `Minimal` and `Maximal` are consequences of the already-generic proposition, quantifier, and
subset machinery. These instances subsume the old matroid-specific closure lemmas. -/

instance instIsoInvariantMinimal : IsoInvariant (fun X (S : Set (A X)) ↦ Minimal (P X) S)
      (fun Y (S : Set (A' Y)) ↦ Minimal (P' Y) S) := IsoInvariant.of_iff_map _ _ fun {X Y} i S ↦ by
    let m := IsoEquiv.map (F := fun X ↦ Set (A X)) (F' := fun Y ↦ Set (A' Y)) i
    have hP (T : Set (A X)) : P X T ↔ P' Y (m T) := IsoInvariant.iff_map (P := P) (P' := P') i T
    have hss (S T : Set (A X)) : S ⊆ T ↔ m S ⊆ m T := IsoInvariant.iff_map₂
        (P := fun X (S T : Set (A X)) ↦ S ⊆ T) (P' := fun Y (S T : Set (A' Y)) ↦ S ⊆ T) i S T
    rw [minimal_subset_iff, minimal_subset_iff]
    constructor
    · refine fun ⟨hPS, hmin⟩ ↦ ⟨(hP S).mp hPS, ?_⟩
      rintro T' hPT' hT'S
      obtain ⟨T, rfl⟩ := m.surjective T'
      obtain rfl := hmin ((hP T).mpr hPT') ((hss T S).mpr hT'S)
      rfl
    · exact fun ⟨hPS, hmin⟩ ↦ ⟨(hP S).mpr hPS,
      (fun T hPT hTS ↦ m.injective (hmin ((hP T).mp hPT) ((hss T S).mp hTS)))⟩

instance instIsoInvariantMaximal : IsoInvariant (fun X (S : Set (A X)) ↦ Maximal (P X) S)
      (fun Y (S : Set (A' Y)) ↦ Maximal (P' Y) S) := IsoInvariant.of_iff_map _ _ fun {X Y} i S ↦ by
    let m := IsoEquiv.map (F := fun X ↦ Set (A X)) (F' := fun Y ↦ Set (A' Y)) i
    have hP (T : Set (A X)) : P X T ↔ P' Y (m T) := IsoInvariant.iff_map (P := P) (P' := P') i T
    have hss (S T : Set (A X)) : S ⊆ T ↔ m S ⊆ m T := IsoInvariant.iff_map₂
        (P := fun X (S T : Set (A X)) ↦ S ⊆ T) (P' := fun Y (S T : Set (A' Y)) ↦ S ⊆ T) i S T
    rw [maximal_subset_iff, maximal_subset_iff]
    constructor
    · refine fun ⟨hPS, hmax⟩ ↦ ⟨(hP S).mp hPS, ?_⟩
      rintro T' hPT' hST'
      obtain ⟨T, rfl⟩ := m.surjective T'
      obtain rfl := hmax ((hP T).mpr hPT') ((hss S T).mpr hST')
      rfl
    · exact fun ⟨hPS, hmax⟩ ↦ ⟨(hP S).mpr hPS,
      (fun T hPT hST ↦ m.injective (hmax ((hP T).mp hPT) ((hss S T).mp hST)))⟩

end SetConstructions

/-! ## Pointwise proposition algebra

These are the function-valued analogues of the top-level proposition instances. They subsume the
old `InvariantFun.and` / negation-style combinators without closing over a free transported
argument too early. -/

section PropAlgebraPointwise

variable (Ctx : TypeFamily C₁) (Ctx' : TypeFamily C₂) [c : IsoEquiv Ctx Ctx']
  (P Q : Observable (fun X ↦ Ctx X → Prop))
  (P' Q' : Observable (fun Y ↦ Ctx' Y → Prop)) [IsoInvariant P P'] [IsoInvariant Q Q']

instance instIsoInvariantNotPointwise : IsoInvariant (fun X z ↦ ¬ P X z) (fun Y z ↦ ¬ P' Y z) :=
  IsoInvariant.of_iff_map _ _ fun i z ↦ not_congr (IsoInvariant.iff_map (P := P) (P' := P') i z)

instance instIsoInvariantAndPointwise :
    IsoInvariant (fun X z ↦ P X z ∧ Q X z) (fun Y z ↦ P' Y z ∧ Q' Y z) :=
  IsoInvariant.of_iff_map _ _ fun i z ↦ and_congr (IsoInvariant.iff_map (P := P) (P' := P') i z)
      (IsoInvariant.iff_map (P := Q) (P' := Q') i z)

instance instIsoInvariantOrPointwise :
    IsoInvariant (fun X z ↦ P X z ∨ Q X z) (fun Y z ↦ P' Y z ∨ Q' Y z) :=
  IsoInvariant.of_iff_map _ _ fun i z ↦ or_congr (IsoInvariant.iff_map (P := P) (P' := P') i z)
      (IsoInvariant.iff_map (P := Q) (P' := Q') i z)

instance instIsoInvariantImpPointwise :
    IsoInvariant (fun X z ↦ P X z → Q X z) (fun Y z ↦ P' Y z → Q' Y z) :=
  IsoInvariant.of_iff_map _ _ fun i z ↦ imp_congr (IsoInvariant.iff_map (P := P) (P' := P') i z)
      (IsoInvariant.iff_map (P := Q) (P' := Q') i z)

instance instIsoInvariantIffPointwise :
    IsoInvariant (fun X z ↦ P X z ↔ Q X z) (fun Y z ↦ P' Y z ↔ Q' Y z) :=
  IsoInvariant.of_iff_map _ _ fun i z ↦ iff_congr (IsoInvariant.iff_map (P := P) (P' := P') i z)
      (IsoInvariant.iff_map (P := Q) (P' := Q') i z)

end PropAlgebraPointwise
