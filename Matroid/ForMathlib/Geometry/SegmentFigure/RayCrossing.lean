module

public import Matroid.ForMathlib.Geometry.RayCrossing
public import Matroid.ForMathlib.Geometry.SegmentFigure.Crossing
public import Matroid.ForMathlib.Geometry.SegmentFigure.Transverse

/-! # Singleton-ray intervals of segment figures

An infinite area-coordinate image characterizes directions admitting an interval of
exterior origins whose rays each meet exactly one crossing.
-/

@[expose] public section

open Set Module Function Metric

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

namespace Orientation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (finrank ℝ E = 2)] (o : Orientation ℝ E (Fin 2))

private theorem infinite_image_of_crossing {X : Type*} [TopologicalSpace X]
    {S : Set X} {f : X → ℝ} (hf : Continuous f) {p : X}
    (hp : p ∈ boundaryCrossings S {q | f p < f q}) : (f '' S).Infinite := by
  intro hfinite
  let A := S ∩ interior {q | f p < f q}
  have hA : (f '' A).Finite := hfinite.subset (image_mono inter_subset_left)
  have hpc : f p ∈ f '' A := closure_minimal
    (show A ⊆ f ⁻¹' (f '' A) from fun q hq ↦ ⟨q, hq, rfl⟩)
    (hA.isClosed.preimage hf) hp.2.1
  obtain ⟨q, hq, heq⟩ := hpc
  have hlt : f p < f q := interior_subset hq.2
  exact hlt.ne heq.symm

/-- A direction admits a singleton-ray interval exactly when its area-coordinate image
is infinite. -/
theorem exists_singleton_interval_iff_infinite_image
    {S : Set E} (hS : IsSegmentFigure S) {v : E} :
    (∃ q ∈ S, ∃ ε : ℝ, 0 < ε ∧ ∀ d ∈ Ioo 0 ε,
      q - d • v ∉ S ∧ o.rayCrossings S (q - d • v) v = {q}) ↔
        ((o.areaForm v) '' S).Infinite := by
  constructor
  · rintro ⟨q, _, ε, hε, hinterval⟩
    obtain ⟨d, hd⟩ := exists_between hε
    have hmem : q ∈ o.rayCrossings S (q - d • v) v :=
      (hinterval d hd).2 ▸ mem_singleton q
    exact infinite_image_of_crossing (LinearMap.continuous_of_finiteDimensional _)
      ((o.mem_rayCrossings_iff.mp hmem).2)
  · intro hi
    obtain ⟨B, hB, hregular⟩ := hS.exists_finite_exceptional_levels
      (o.areaForm v).toAffineMap (LinearMap.continuous_of_finiteDimensional _)
    obtain ⟨c, ⟨p, hpS, hpc⟩, hcB⟩ := hi.exists_notMem_finite hB
    obtain ⟨hfinite, hcross⟩ := hregular c hcB
    change (o.areaForm v).toAffineMap p = c at hpc
    have hp : p ∈ boundaryCrossings S {r | o.areaForm v p < o.areaForm v r} := by
      change p ∈ boundaryCrossings S ((o.areaForm v).toAffineMap ⁻¹'
        Ioi ((o.areaForm v).toAffineMap p))
      rw [hpc, hcross]
      exact ⟨hpS, hpc⟩
    obtain ⟨q, hq, ε, hε, hinterval⟩ :=
      exists_singleton_interval_of_finite_fiber o hp (hpc ▸ hfinite)
    exact ⟨q, hq.2.1.1, ε, hε, hinterval⟩

/-- A contained transverse open segment supplies a singleton-ray interval. -/
theorem exists_singleton_interval_of_openSegment
    {S : Set E} (hS : IsSegmentFigure S) {a b v : E}
    (hseg : openSegment ℝ a b ⊆ S) (hab : o.areaForm v a ≠ o.areaForm v b) :
    ∃ q ∈ S, ∃ ε : ℝ, 0 < ε ∧ ∀ d ∈ Ioo 0 ε,
      q - d • v ∉ S ∧ o.rayCrossings S (q - d • v) v = {q} := by
  apply (o.exists_singleton_interval_iff_infinite_image hS).mpr
  have hi : (openSegment ℝ (o.areaForm v a) (o.areaForm v b)).Infinite := by
    rw [openSegment_eq_Ioo' hab]
    exact Ioo_infinite (min_lt_max.mpr hab)
  change (openSegment ℝ ((o.areaForm v).toAffineMap a)
    ((o.areaForm v).toAffineMap b)).Infinite at hi
  rw [← image_openSegment ℝ (o.areaForm v).toAffineMap a b] at hi
  exact hi.mono (image_mono hseg)

/-- An infinite segment figure admits a transverse direction and a singleton-ray interval. -/
theorem exists_direction_singleton_interval
    {S : Set E} (hS : IsSegmentFigure S) (hi : S.Infinite) :
    ∃ v : E, v ≠ 0 ∧
      (∀ a b, a ≠ b → segment ℝ a b ⊆ S → o.areaForm v a ≠ o.areaForm v b) ∧
      ∃ q ∈ S, ∃ ε : ℝ, 0 < ε ∧ ∀ d ∈ Ioo 0 ε,
        q - d • v ∉ S ∧ o.rayCrossings S (q - d • v) v = {q} := by
  obtain ⟨a, b, hab, hseg⟩ := hS.infinite_iff.mp hi
  obtain ⟨v, hv, htrans⟩ := o.exists_transverse_direction hS
  exact ⟨v, hv, htrans, exists_singleton_interval_of_openSegment o hS
    ((openSegment_subset_segment ℝ a b).trans hseg) (htrans a b hab hseg)⟩

end Orientation
