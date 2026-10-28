module

public import Matroid.ForMathlib.Geometry.SegmentFigure.Maximal

/-!
# Convex and collinear segment figures

A nonempty convex segment figure is a single segment. Convexity cannot produce a filled
triangle inside a finite union of segments: segments joining an off-line point to a
nondegenerate segment would require infinitely many supporting lines.
-/

@[expose] public section

open Set

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {S : Set V}

namespace IsSegmentFigure

theorem exists_segment_of_convex (hS : IsSegmentFigure S) (hconv : Convex ℝ S)
    (hne : S.Nonempty) : ∃ a b, S = segment ℝ a b := by
  by_cases hs : S.Subsingleton
  · obtain ⟨a, ha⟩ := hne
    exact ⟨a, a, (hs.eq_singleton_of_mem ha).trans (segment_same ℝ a).symm⟩
  obtain ⟨a, ha, b, hb, hab⟩ := not_subsingleton_iff.mp hs
  have habS := hconv.segment_subset ha hb
  have hspan (u v : V) : segment ℝ u v ⊆ (affineSpan ℝ {u, v} : Set V) := by
    rw [← convexHull_pair]
    exact convexHull_subset_affineSpan _
  have hline : S ⊆ (affineSpan ℝ {a, b} : Set V) := by
    intro y hy
    by_contra hyL
    let M := {T ∈ maximalSegments S | y ∈ T}
    have hM : M.Finite := hS.finite_maximalSegments.subset (sep_subset _ _)
    have hfin (T) (hT : T ∈ M) : (segment ℝ a b ∩ T).Finite := by
      obtain ⟨c, d, rfl⟩ := hT.1.1.2
      apply Set.Subsingleton.finite
      intro p hp q hq
      by_contra hpq
      have heq : affineSpan ℝ {c, d} = affineSpan ℝ {a, b} :=
        (affineSpan_pair_eq_of_mem_of_mem_of_ne (hspan _ _ hp.2)
          (hspan _ _ hq.2) hpq).symm.trans
          (affineSpan_pair_eq_of_mem_of_mem_of_ne (hspan _ _ hp.1) (hspan _ _ hq.1) hpq)
      exact hyL (heq ▸ hspan _ _ hT.2)
    apply hab
    apply (finite_segment_iff (K := ℝ)).mp ((hM.biUnion hfin).subset ?_)
    intro x hx
    obtain ⟨T, hT, hxy⟩ := hS.exists_maximalSegment (hconv.segment_subset (habS hx) hy)
    exact mem_biUnion ⟨hT, hxy (right_mem_segment ℝ x y)⟩
      ⟨hx, hxy (left_mem_segment ℝ x y)⟩
  let f : ℝ →ᵃ[ℝ] V := AffineMap.lineMap a b
  have hf : Function.Injective f := AffineMap.lineMap_injective ℝ hab
  have hT := hS.preimage f hf
  have hTne : (f ⁻¹' S).Nonempty := ⟨0, by simpa [f] using ha⟩
  have heq := hT.eq_Icc_of_isConnected ((hconv.affine_preimage f).isConnected hTne)
  have hle : sInf (f ⁻¹' S) ≤ sSup (f ⁻¹' S) := nonempty_Icc.mp (heq ▸ hTne)
  have him : f '' (f ⁻¹' S) = S := image_preimage_eq_of_subset fun x hx ↦
    mem_affineSpan_pair_iff_exists_lineMap_eq.mp (hline hx)
  refine ⟨f (sInf (f ⁻¹' S)), f (sSup (f ⁻¹' S)), ?_⟩
  calc
    S = f '' (f ⁻¹' S) := him.symm
    _ = f '' Icc (sInf (f ⁻¹' S)) (sSup (f ⁻¹' S)) := congrArg (fun T ↦ f '' T) heq
    _ = _ := by rw [← segment_eq_Icc hle, image_segment]

theorem convex_iff (hS : IsSegmentFigure S) :
    Convex ℝ S ↔ S = ∅ ∨ ∃ a b, S = segment ℝ a b := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain rfl | hne := S.eq_empty_or_nonempty
    · exact Or.inl rfl
    exact Or.inr (hS.exists_segment_of_convex h hne)
  rintro (rfl | ⟨a, b, rfl⟩)
  · exact convex_empty
  · exact convex_segment a b

/-- A connected collinear figure is a segment, independently of its ambient dimension. -/
theorem exists_segment_of_isConnected [TopologicalSpace V] [IsTopologicalAddGroup V]
    [ContinuousSMul ℝ V] [T2Space V] (hS : IsSegmentFigure S) (hconn : IsConnected S)
    (hcol : Collinear ℝ S) : ∃ a b, S = segment ℝ a b := by
  by_cases hs : S.Subsingleton
  · obtain ⟨a, ha⟩ := hconn.nonempty
    exact ⟨a, a, (hs.eq_singleton_of_mem ha).trans (segment_same ℝ a).symm⟩
  obtain ⟨a, ha, b, hb, hab⟩ := not_subsingleton_iff.mp hs
  let f : ℝ →ᵃ[ℝ] V := AffineMap.lineMap a b
  have hf : Function.Injective f := AffineMap.lineMap_injective ℝ hab
  have hrange : S ⊆ range f := fun x hx ↦
    mem_affineSpan_pair_iff_exists_lineMap_eq.mp
      (hcol.mem_affineSpan_of_mem_of_ne ha hb hx hab)
  have hclosed : IsClosedMap f := by
    have hfun : (f : ℝ → V) = fun t ↦ t • (b - a) + a :=
      funext (AffineMap.lineMap_apply_module' a b)
    rw [hfun]
    exact (isClosedMap_add_right a).comp (isClosedMap_smul_left (𝕜 := ℝ) (b - a))
  have hconv := (hconn.isPreconnected.preimage_of_isClosedMap hf hclosed hrange).convex
  apply hS.exists_segment_of_convex _ hconn.nonempty
  exact image_preimage_eq_of_subset hrange ▸ hconv.affine_image f

end IsSegmentFigure

end
