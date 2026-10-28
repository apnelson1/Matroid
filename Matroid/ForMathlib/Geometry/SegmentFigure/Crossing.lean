module

public import Matroid.ForMathlib.Geometry.SegmentFigure.Affine
public import Matroid.ForMathlib.Geometry.AffineCrossing

/-! # Affine levels of segment figures

Away from finitely many levels, affine fibres are finite and equal the crossing set.
For a Hausdorff carrier, crossings are finite even at exceptional levels.
-/

@[expose] public section

open Set AffineMap

/-- A Hausdorff segment figure has finitely many crossings at every affine level. -/
theorem IsSegmentFigure.finite_boundaryCrossings_preimage_Ioi {V : Type*}
    [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [ContinuousConstVAdd V V] [ContinuousSMul ℝ V]
    {S : Set V} [T2Space S] (hS : IsSegmentFigure S)
    (f : V →ᵃ[ℝ] ℝ) (hf : Continuous f) (c : ℝ) :
    (boundaryCrossings S (f ⁻¹' Ioi c)).Finite := by
  obtain ⟨E, hE, hpres⟩ := hS
  apply AffineMap.finite_boundaryCrossings_of_cover hE hpres.subset f hf _ c
  intro e he _
  have heS : segment ℝ e.1 e.2 ⊆ S := fun r hr ↦
    hpres ▸ mem_iUnion₂.mpr ⟨e, he, hr⟩
  have hline : Continuous (lineMap e.1 e.2 : ℝ → V) := by
    have hsmul : Continuous (fun t : ℝ ↦ t • (e.2 - e.1)) :=
      continuous_id.smul continuous_const
    have htrans : Continuous (fun x : V ↦ e.1 +ᵥ x) := continuous_const_vadd e.1
    change Continuous (fun t : ℝ ↦ t • (e.2 - e.1) + e.1)
    simpa only [Function.comp_def, lineMap_apply_module', vadd_eq_add, add_comm]
      using htrans.comp hsmul
  have hcompact : IsCompact (segment ℝ e.1 e.2) := by
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image hline
  exact (Topology.IsInducing.subtypeVal.isCompact_preimage' hcompact
    (by simpa using heS)).isClosed

/-- Outside finitely many levels, each fibre is finite and equals the crossing set. -/
theorem IsSegmentFigure.exists_finite_exceptional_levels {V : Type*} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [ContinuousConstVAdd V V] [ContinuousSMul ℝ V]
    {S : Set V} (hS : IsSegmentFigure S) (f : V →ᵃ[ℝ] ℝ) (hf : Continuous f) :
    ∃ B : Set ℝ, B.Finite ∧ ∀ c ∉ B,
      (S ∩ f ⁻¹' {c}).Finite ∧ boundaryCrossings S (f ⁻¹' Ioi c) = S ∩ f ⁻¹' {c} := by
  obtain ⟨E, hE, heq⟩ := hS
  refine ⟨(fun e : V × V ↦ f e.1) '' E ∪ (fun e : V × V ↦ f e.2) '' E,
    (hE.image _).union (hE.image _), fun c hc ↦ ?_⟩
  have hleft : ∀ e ∈ E, f e.1 ≠ c := fun e he h ↦ hc (Or.inl ⟨e, he, h⟩)
  have hright : ∀ e ∈ E, f e.2 ≠ c := fun e he h ↦ hc (Or.inr ⟨e, he, h⟩)
  exact ⟨AffineMap.finite_fiber_of_cover hE heq.subset f c (fun e he _ h ↦ (hleft e he h).elim),
    f.boundaryCrossings_eq_fiber_of_regular_level hf heq fun e he ↦ ⟨hleft e he, hright e he⟩⟩

