module

public import Matroid.ForMathlib.Geometry.SegmentFigure.Basic
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Affine sections and changes of ambient space

Affine sections and injective affine preimages preserve segment figures without topology.
Every figure also has finite-dimensional span, regardless of its ambient space.
-/

@[expose] public section

open Set AffineSubspace

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W] {a b : V}
  {S : Set V} {T : Set W}

/-- A nonempty affine section of a segment is a segment (possibly a singleton). -/
theorem segment_inter_affineSubspace_eq_segment (A : AffineSubspace ℝ V)
    (hne : (segment ℝ a b ∩ (A : Set V)).Nonempty) :
    ∃ p q, segment ℝ a b ∩ (A : Set V) = segment ℝ p q := by
  by_cases hsub : segment ℝ a b ⊆ A
  · exact ⟨a, b, inter_eq_left.mpr hsub⟩
  have hs : (segment ℝ a b ∩ (A : Set V)).Subsingleton := by
    intro x hx y hy
    by_contra hxy
    have hseg : segment ℝ a b ⊆ (affineSpan ℝ {a, b} : Set V) := by
      rw [← convexHull_pair]
      exact convexHull_subset_affineSpan _
    have heq := affineSpan_pair_eq_of_mem_of_mem_of_ne (hseg hx.left) (hseg hy.left) hxy
    exact hsub (hseg.trans (show (affineSpan ℝ {a, b} : Set V) ⊆ A from
      heq ▸ affineSpan_pair_le_of_mem_of_mem hx.right hy.right))
  obtain ⟨p, hp⟩ := hne
  exact ⟨p, p, (hs.eq_singleton_of_mem hp).trans (segment_same ℝ p).symm⟩

namespace IsSegmentFigure

theorem inter_affineSubspace (hS : IsSegmentFigure S) (A : AffineSubspace ℝ V) :
    IsSegmentFigure (S ∩ A) := by
  refine hS.induction_on (by simp) fun a b S _ ih ↦ ?_
  rw [union_inter_distrib_right]
  refine union ?_ ih
  obtain h | h := (segment ℝ a b ∩ (A : Set V)).eq_empty_or_nonempty
  · exact h ▸ isSegmentFigure_empty
  obtain ⟨p, q, hpq⟩ := segment_inter_affineSubspace_eq_segment A h
  exact hpq ▸ isSegmentFigure_segment p q

/-- An injective affine preimage preserves segment figures, even for discontinuous maps. -/
theorem preimage (hT : IsSegmentFigure T) (f : V →ᵃ[ℝ] W) (hf : Function.Injective f) :
    IsSegmentFigure (f ⁻¹' T) := by
  refine hT.induction_on (by simp) fun a b T _ ih ↦ ?_
  rw [preimage_union]
  refine union ?_ ih
  let A : AffineSubspace ℝ W := (⊤ : AffineSubspace ℝ V).map f
  have hA : (A : Set W) = range f := by simp [A, coe_map]
  obtain h | h := (segment ℝ a b ∩ (A : Set W)).eq_empty_or_nonempty
  · convert isSegmentFigure_empty
    refine eq_empty_iff_forall_notMem.mpr fun x hx ↦ ?_
    have : f x ∈ segment ℝ a b ∩ (A : Set W) := ⟨hx, hA ▸ mem_range_self x⟩
    simp [h] at this
  obtain ⟨p, q, hpq⟩ := segment_inter_affineSubspace_eq_segment A h
  obtain ⟨x, rfl⟩ := hA ▸ (hpq ▸ left_mem_segment ℝ p q).right
  obtain ⟨y, rfl⟩ := hA ▸ (hpq ▸ right_mem_segment ℝ _ q).right
  convert isSegmentFigure_segment x y
  rw [← hf.preimage_image (segment ℝ x y), image_segment, ← hpq]
  simp [hA, preimage_inter]

theorem image_iff (f : V →ᵃ[ℝ] W) (hf : Function.Injective f) :
    IsSegmentFigure (f '' S) ↔ IsSegmentFigure S :=
  ⟨fun h ↦ hf.preimage_image S ▸ h.preimage f hf, fun h ↦ h.image f⟩

open Submodule in
/-- All the ambient linear algebra of a figure occurs in a finite-dimensional span. -/
theorem finiteDimensional_span (hS : IsSegmentFigure S) : FiniteDimensional ℝ (span ℝ S) := by
  obtain ⟨F, hF, hFS, heq⟩ := hS.exists_finite_convexHull_eq
  suffices hspan : span ℝ S = span ℝ F from hspan ▸ FiniteDimensional.span_of_finite ℝ hF
  refine (span_le.mpr <| (subset_convexHull ℝ S).trans ?_).antisymm (span_mono hFS)
  exact heq ▸ convexHull_min subset_span (Submodule.convex _)

end IsSegmentFigure

end
