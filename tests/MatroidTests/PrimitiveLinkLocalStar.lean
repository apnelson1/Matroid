module

public import Matroid.ForMathlib.Geometry.PolygonalPath.PrimitivePath
public import Matroid.ForMathlib.Geometry.PolygonalPath.SegmentFigure
public import Matroid.ForMathlib.Geometry.PrimitiveLink

/-!
# Primitive-link local-star consumers

These tests use the sphere section rather than a chosen finset of radii, include a loop's
basepoint, and use a polygonal parametrization with a repeated vertex.
-/

open Set Metric

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {L : Set V} {a b p : V}

-- No condition excluding the loop's basepoint is needed, even at a prescribed scale.
example (hL : IsPrimitiveLink L a a) (hpoly : IsSegmentFigure L) {ε : ℝ} (hε : 0 < ε) :
    ∃ r, 0 < r ∧ r ≤ ε ∧ (sphere a r ∩ L).ncard = 2 := by
  obtain ⟨r, hr, hle, Y, hcard, hY, hstar⟩ :=
    hL.exists_local_star_two_le hpoly hL.left_mem (Or.inl rfl) hε
  refine ⟨r, hr, hle, ?_⟩
  rw [← coe_eq_sphere_inter_of_star hr hY hstar, Set.ncard_coe_finset, hcard]

-- One threshold controls every smaller radius, with a canonical two-point sphere section.
example (hL : IsPrimitiveLink L a b) (hpoly : IsSegmentFigure L) (hp : p ∈ L \ {a, b}) :
    ∃ r₀ > 0, ∀ r, 0 < r → r ≤ r₀ → (sphere p r ∩ L).ncard = 2 := by
  obtain ⟨r₀, hr₀, hstar⟩ := hL.exists_local_star_two hpoly hp.1 (Or.inr hp.2)
  refine ⟨r₀, hr₀, fun r hr hle ↦ ?_⟩
  obtain ⟨Y, hcard, hY, heq⟩ := hstar r hr hle
  rw [← coe_eq_sphere_inter_of_star hr hY heq, Set.ncard_coe_finset, hcard]

-- Reversing the link gives the exact radius at the other endpoint, with uniqueness.
example (hL : IsPrimitiveLink L a b) (hab : a ≠ b) (hpoly : IsSegmentFigure L) :
    ∃ r₀ > 0, ∀ r, 0 < r → r ≤ r₀ → ∃! y,
      y ∈ sphere b r ∧ closedBall b r ∩ L = segment ℝ b y :=
  hL.symm.exists_local_star_one hab.symm hpoly

-- A stationary first segment destroys primitive parametrization, but preserves the link.
example (hab : a ≠ b) :
    let P := PolygonalPath.cons a a (PolygonalPath.direct a b)
    ¬ P.toPath.IsPrimitive ∧ ∃ r > 0, (sphere a r ∩ P.toSet).ncard = 1 := by
  intro P
  have hset : P.toSet = segment ℝ a b := by
    simp only [P, PolygonalPath.toSet_cons, PolygonalPath.toSet_direct, segment_same,
      singleton_union, insert_eq_of_mem (left_mem_segment ℝ a b)]
  have hL : IsPrimitiveLink P.toSet a b := by
    rw [hset, ← Path.range_segment]
    exact IsPrimitiveLink.of_injective (Path.segment_injective_of_ne hab)
  constructor
  · intro hP
    have hs := (PolygonalPath.isPrimitive_iff_isSimple hab).mp hP
    exact hs.hasNondegenerateEdges (a, a) (by simp [P]) rfl
  obtain ⟨r, hr, hstar⟩ := hL.exists_local_star P.isSegmentFigure_toSet hL.left_mem
  obtain ⟨Y, hcard, hY, heq⟩ := hstar r hr le_rfl
  refine ⟨r, hr, ?_⟩
  rw [← coe_eq_sphere_inter_of_star hr hY heq, Set.ncard_coe_finset]
  simpa [hab] using hcard

/-- info: 'IsPrimitiveLink.exists_local_star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsPrimitiveLink.exists_local_star
