module

public import Matroid.ForMathlib.Geometry.SegmentFigure.Basic
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Algebra.Module.Submodule.Union
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-!
# Affine sections and changes of ambient space

Affine sections and injective affine preimages preserve segment figures without topology.
Affine maps collapsing no nondegenerate contained segment have finite fibers, in arbitrary
real affine codomains. Finite covers supply construction proofs, while intrinsic criteria
characterize all finite fibers.
Every figure also has finite-dimensional span, regardless of its ambient space.
-/

@[expose] public section

open Set AffineSubspace Module

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

section Fibers

variable {Q : Type*} [AddTorsor W Q]

theorem finite_fibers_iff (hS : IsSegmentFigure S) (f : V →ᵃ[ℝ] Q) :
    (∀ c, (S ∩ f ⁻¹' {c}).Finite) ↔
      ∀ a b, a ≠ b → segment ℝ a b ⊆ S → f a ≠ f b := by
  constructor
  · intro h a b hab hseg heq
    apply hab
    apply (finite_segment_iff (K := ℝ)).mp
    apply (h (f a)).subset
    intro p hp
    refine ⟨hseg hp, ?_⟩
    obtain ⟨t, -, rfl⟩ := segment_eq_image_lineMap ℝ a b ▸ hp
    simp only [mem_preimage, mem_singleton_iff, f.apply_lineMap, ← heq,
      AffineMap.lineMap_same_apply]
  · intro h c
    obtain ⟨E, hE, hpres⟩ := hS
    apply AffineMap.finite_fiber_of_cover hE hpres.subset f c
    intro e he hab ha hb
    exact h e.1 e.2 hab (fun p hp ↦ hpres ▸ mem_iUnion₂.mpr ⟨e, he, hp⟩)
      (ha.trans hb.symm)

theorem finite_infinite_fiber_values (hS : IsSegmentFigure S) (f : V →ᵃ[ℝ] Q) :
    {c | (S ∩ f ⁻¹' {c}).Infinite}.Finite := by
  obtain ⟨E, hE, hpres⟩ := hS
  rw [AffineMap.infinite_fiber_values_eq hE hpres f]
  exact (hE.sep _).image _

end Fibers

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

private theorem exists_direction (hS : IsSegmentFigure S) (hdim : 1 < Module.rank ℝ V) :
    ∃ v : V, v ≠ 0 ∧ ∀ a b, a ≠ b → segment ℝ a b ⊆ S →
      ∀ t : ℝ, b - a ≠ t • v := by
  classical
  have hproper (w : V) : Submodule.span ℝ {w} ≠ ⊤ := by
    intro hw
    apply hdim.not_ge
    apply rank_le_one w
    intro x
    exact Submodule.mem_span_singleton.mp
      (hw ▸ Submodule.mem_top : x ∈ Submodule.span ℝ {w})
  obtain ⟨E, hE, hpres⟩ := hS
  have := hE.to_subtype
  let p : Option E → Submodule ℝ V
    | none => ⊥
    | some e => Submodule.span ℝ {e.val.2 - e.val.1}
  obtain ⟨v, hv⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p (by
    rintro (_ | e)
    · simpa [p] using hproper 0
    · exact hproper _)
  have hv0 : v ≠ 0 := fun h ↦ hv none (by simp [p, h])
  let f := (Submodule.span ℝ {v}).mkQ
  have hgen (e : V × V) (he : e ∈ E) (hab : e.1 ≠ e.2) : f e.1 ≠ f e.2 := by
    intro h
    have hz : f (e.2 - e.1) = 0 := by rw [map_sub, h, sub_self]
    have hm : e.2 - e.1 ∈ Submodule.span ℝ {v} :=
      (Submodule.Quotient.mk_eq_zero _).mp hz
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hm
    have ht0 : t ≠ 0 := by
      intro hzero
      exact hab (sub_eq_zero.mp (by simpa [hzero] using ht.symm)).symm
    apply hv (some ⟨e, he⟩)
    change v ∈ Submodule.span ℝ {e.2 - e.1}
    rw [← ht]
    exact Submodule.mem_span_singleton.mpr ⟨t⁻¹, by simp [smul_smul, ht0]⟩
  have hfin (c) := AffineMap.finite_fiber_of_cover hE hpres.subset f.toAffineMap c
    (fun e he hab ha hb ↦ hgen e he hab (ha.trans hb.symm))
  have hsep := (finite_fibers_iff ⟨E, hE, hpres⟩ f.toAffineMap).mp hfin
  refine ⟨v, hv0, fun a b hab hseg t ht ↦ hsep a b hab hseg ?_⟩
  change f a = f b
  have hzero : f (b - a) = 0 := by
    rw [ht, map_smul]
    have hz : f v = 0 := (Submodule.Quotient.mk_eq_zero _).mpr
      (Submodule.mem_span_singleton_self v)
    rw [hz, smul_zero]
  exact (sub_eq_zero.mp (by simpa only [map_sub] using hzero)).symm

theorem exists_direction_not_parallel_iff (hS : IsSegmentFigure S) :
    (∃ v : V, v ≠ 0 ∧ ∀ a b, a ≠ b → segment ℝ a b ⊆ S →
      ∀ t : ℝ, b - a ≠ t • v) ↔
      Nontrivial V ∧ (S.Finite ∨ 1 < Module.rank ℝ V) := by
  constructor
  · rintro ⟨v, hv, htrans⟩
    refine ⟨⟨⟨v, 0, hv⟩⟩, ?_⟩
    by_cases hdim : 1 < Module.rank ℝ V
    · exact Or.inr hdim
    left
    apply hS.finite_iff.mpr
    intro a b hseg
    by_contra hab
    obtain ⟨w, hw⟩ := rank_le_one_iff.mp (le_of_not_gt hdim)
    obtain ⟨c, hc⟩ := hw v
    have hc0 : c ≠ 0 := by
      intro hzero
      exact hv (by simpa [hzero] using hc.symm)
    obtain ⟨d, hd⟩ := hw (b - a)
    exact htrans a b hab hseg (d / c) (by
      rw [← hc, smul_smul, div_mul_cancel₀ _ hc0, hd])
  · rintro ⟨hV, hfinite | hdim⟩
    · let := hV
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      exact ⟨v, hv, fun a b hab hseg _ ↦
        (hab (finite_segment_iff.mp (hfinite.subset hseg))).elim⟩
    · exact exists_direction hS hdim

theorem exists_linear_finite_fibers (hS : IsSegmentFigure S) :
    ∃ f : V →ₗ[ℝ] ℝ, ∀ c, (S ∩ f ⁻¹' {c}).Finite := by
  classical
  obtain ⟨E, hE, hpres⟩ := hS
  let D := {e ∈ E | e.1 ≠ e.2}
  have hD : D.Finite := hE.subset fun _ he ↦ he.1
  have := hD.to_subtype
  obtain ⟨f, hf⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℝ)
    (fun e : D ↦ e.val.2 - e.val.1)
    (fun e ↦ sub_ne_zero.mpr e.property.2.symm)
  refine ⟨f, fun c ↦ AffineMap.finite_fiber_of_cover hE hpres.subset f.toAffineMap c ?_⟩
  intro e he hab ha hb
  have heq := ha.trans hb.symm
  apply hf ⟨e, he, hab⟩
  simp only [map_sub]
  exact sub_eq_zero.mpr heq.symm

end IsSegmentFigure

end
