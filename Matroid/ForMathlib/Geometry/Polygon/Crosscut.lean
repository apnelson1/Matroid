module

public import Matroid.ForMathlib.Geometry.PolygonalPath.ThetaCurve

/-!
# Polygonal crosscuts

The theta-curve theorem gives the standard crosscut theorem for a polygonal Jordan curve: an
embedded arc across one complementary region splits that region into two.  A second disjoint
crosscut cannot have alternating endpoints.

The proofs split the polygon boundary into two arcs and apply the polygonal theta-curve theorem.

-/

open Function Set Topology

namespace Polygon

public noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (Module.finrank ℝ V = 2)] {s t s₁ s₂ t₁ t₂ : V}

/-- **Crosscut theorem.** A simple polygon bounds two regions; a simple arc through one region,
meeting the polygon exactly at its endpoints, splits that region into two. -/
theorem IsSimple.exists_two_regions_crosscut {n : ℕ} {p : Polygon V n} (hp : p.IsSimple ℝ)
    {F : Set (OnePoint V)} {q : OnePoint V} (hq : q ∈ ((↑) '' p.boundary ℝ)ᶜ) {A : PolygonalPath s t}
    (hF : F = connectedComponentIn ((↑) '' p.boundary ℝ)ᶜ q) (hst : s ≠ t)
    (hs : s ∈ p.boundary ℝ) (ht : t ∈ p.boundary ℝ)
    (hA : A.IsSimple) (hAJ : A.toSet ∩ p.boundary ℝ = {s, t})
    (hAF : (↑) '' (A.toSet \ {s, t}) ⊆ F) :
    ∃ (J₁ : PolygonalPath s t) (J₂ : PolygonalPath t s) (W₁ W₂ : Set (OnePoint V)),
      J₁.IsSimple ∧ J₂.IsSimple ∧
      J₁.toSet ∩ J₂.toSet = {s, t} ∧
      J₁.toSet ∪ J₂.toSet = p.boundary ℝ ∧
      IsOpen W₁ ∧ IsOpen W₂ ∧
      IsConnected W₁ ∧ IsConnected W₂ ∧
      Disjoint W₁ W₂ ∧
      W₁ ∪ W₂ = F \ ((↑) '' A.toSet) ∧
      frontier W₁ = (↑) '' (J₁.toSet ∪ A.toSet) ∧
      frontier W₂ = (↑) '' (J₂.toSet ∪ A.toSet) := by
  /-
  1. `hp.exists_arcs hs ht` splits the polygon boundary into simple arcs `J₁,J₂`.
  2. `J₁`, `J₂.reverse` (as needed for endpoint orientation), and `A` form the three arms of a
     theta curve.
  3. Apply `PolygonalPath.exists_three_regions_theta`.
  4. The theta region bounded by `J₁ ∪ J₂` is the *other* JCT side of the original polygon.
     Therefore the remaining two theta regions are exactly the two components of
     `F \ ((↑) '' A.toSet)`.
  5. Read their frontiers from the theta theorem.

  Keep the region-identification step separate if it grows: it is a connected-component equality,
  not polygon bookkeeping.
  -/
  sorry

/-- Two disjoint crosscuts of the same polygonal region cannot have alternating endpoints. -/
theorem IsSimple.not_alternating_crosscut {n : ℕ} {p : Polygon V n} (hp : p.IsSimple ℝ)
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
  /-
  Apply `hp.exists_two_regions_crosscut` to `A`.  Its two open components are separated by `A`.
  The connected interior of `B`, being disjoint from `A`, must lie entirely in one of them.
  Alternating endpoints force its two ends into closures of different components, a contradiction.

  This theorem is not currently needed for the 3-connected Kuratowski dependency chain; do not let
  its proof block `FaceCycle`.
  -/
  sorry

end

end Polygon
