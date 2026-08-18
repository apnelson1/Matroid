module

import all Matroid.ForMathlib.Geometry.Polygon.Crosscut

/-!
# Compatibility layer for polygonal theta/crosscut topology

The graph namespace exposes wrappers for the graph-free results in `ForMathlib`:

* `PolygonalPath.exists_three_regions_theta`
* `Polygon.IsSimple.exists_two_regions_crosscut`
* `Polygon.IsSimple.not_alternating_crosscut`

The wrappers keep the existing `Graph.*` names for planarity code; new graph-free code should use
the `ForMathlib` declarations directly.
-/

open Function Set Topology

namespace Graph

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (Module.finrank ℝ V = 2)] {a b s t s₁ s₂ t₁ t₂ : V}

theorem exists_three_regions_theta (hab : a ≠ b) (A : Fin 3 → PolygonalPath a b)
    (hsimple : ∀ i, (A i).IsSimple)
    (hmeet : ∀ i j, i ≠ j → (A i).toSet ∩ (A j).toSet = {a, b}) :
    ∃ W : Fin 3 → Set (OnePoint V),
      (∀ i, IsOpen (W i)) ∧
      (∀ i, IsConnected (W i)) ∧
      (Pairwise fun i j ↦ Disjoint (W i) (W j)) ∧
      (⋃ i, W i) = ((↑) '' (⋃ i, (A i).toSet))ᶜ ∧
      ∀ i, frontier (W i) =
        (↑) '' ⋃ j ∈ ({i}ᶜ : Set (Fin 3)), (A j).toSet := by
  exact PolygonalPath.exists_three_regions_theta hab A hsimple hmeet

theorem exists_two_regions_crosscut {n : ℕ} {p : Polygon V n} (hp : p.IsSimple ℝ)
    {F : Set (OnePoint V)} {q : OnePoint V} (hq : q ∈ ((↑) '' p.boundary ℝ)ᶜ)
    {A : PolygonalPath s t} (hF : F = connectedComponentIn ((↑) '' p.boundary ℝ)ᶜ q) (hst : s ≠ t)
    (hs : s ∈ p.boundary ℝ) (ht : t ∈ p.boundary ℝ) (hA : A.IsSimple)
    (hAJ : A.toSet ∩ p.boundary ℝ = {s, t}) (hAF : (↑) '' (A.toSet \ {s, t}) ⊆ F) :
    ∃ (J₁ : PolygonalPath s t) (J₂ : PolygonalPath t s) (W₁ W₂ : Set (OnePoint V)),
      J₁.IsSimple ∧ J₂.IsSimple ∧ J₁.toSet ∩ J₂.toSet = {s, t} ∧
      J₁.toSet ∪ J₂.toSet = p.boundary ℝ ∧
      IsOpen W₁ ∧ IsOpen W₂ ∧ IsConnected W₁ ∧ IsConnected W₂ ∧
      Disjoint W₁ W₂ ∧ W₁ ∪ W₂ = F \ ((↑) '' A.toSet) ∧
      frontier W₁ = (↑) '' (J₁.toSet ∪ A.toSet) ∧
      frontier W₂ = (↑) '' (J₂.toSet ∪ A.toSet) := by
  exact hp.exists_two_regions_crosscut hq hF hst hs ht hA hAJ hAF

theorem not_alternating_crosscut {n : ℕ} {p : Polygon V n} (hp : p.IsSimple ℝ)
    {F : Set (OnePoint V)} {q : OnePoint V} (hq : q ∈ ((↑) '' p.boundary ℝ)ᶜ)
    {A : PolygonalPath s₁ s₂}
    (hF : F = connectedComponentIn ((↑) '' p.boundary ℝ)ᶜ q)
    {B : PolygonalPath t₁ t₂}
    (hA : A.IsSimple) (hB : B.IsSimple) (hAB : Disjoint A.toSet B.toSet)
    (hAJ : A.toSet ∩ p.boundary ℝ = {s₁, s₂})
    (hBJ : B.toSet ∩ p.boundary ℝ = {t₁, t₂})
    (hAF : (↑) '' (A.toSet \ {s₁, s₂}) ⊆ F)
    (hBF : (↑) '' (B.toSet \ {t₁, t₂}) ⊆ F)
    {J₁ : PolygonalPath s₁ s₂} {J₂ : PolygonalPath s₂ s₁}
    (hJ₁ : J₁.IsSimple) (hJ₂ : J₂.IsSimple)
    (hJmeet : J₁.toSet ∩ J₂.toSet = {s₁, s₂})
    (hJcover : J₁.toSet ∪ J₂.toSet = p.boundary ℝ) :
    ¬ (t₁ ∈ J₁.toSet \ {s₁, s₂} ∧ t₂ ∈ J₂.toSet \ {s₁, s₂}) := by
  exact hp.not_alternating_crosscut hq hF hA hB hAB hAJ hBJ hAF hBF
    hJ₁ hJ₂ hJmeet hJcover

end

end Graph
