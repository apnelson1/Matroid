module

public import Matroid.ForMathlib.Geometry.SegmentFigure.Affine
public import Matroid.ForMathlib.Geometry.SegmentFigure.Real

/-!
# Maximal segments of a figure

The maximal segments are intrinsic subsets of the figure. Unlike a subdivision, this
normal form does not split a straight segment at a crossing.
-/

@[expose] public section

open Set

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- The segment subsets of `S` that are maximal under inclusion. Degenerate segments are allowed. -/
def maximalSegments (S : Set V) : Set (Set V) :=
  {T | Maximal (fun T ↦ T ⊆ S ∧ (∃ a b, T = segment ℝ a b)) T}

/-- The endpoint-based characterization of membership in the maximal-segment family. -/
theorem mem_maximalSegments_iff {S T : Set V} :
    T ∈ maximalSegments S ↔ (∃ a b, T = segment ℝ a b) ∧ T ⊆ S ∧
      ∀ a b, T ⊆ segment ℝ a b → segment ℝ a b ⊆ S → segment ℝ a b = T := by
  change Maximal (fun T ↦ T ⊆ S ∧ (∃ a b, T = segment ℝ a b)) T ↔ _
  refine ⟨fun h ↦ ⟨h.prop.right, h.prop.1, fun a b hT hS ↦ h.eq_of_superset ⟨hS, ⟨a, b, rfl⟩⟩ hT⟩,
    fun ⟨hseg, hsub, hmax⟩ ↦ ⟨⟨hsub, hseg⟩, ?_⟩⟩
  rintro U ⟨hUS, ⟨a, b, rfl⟩⟩ hTU
  exact (hmax a b hTU hUS).subset

@[simp]
theorem maximalSegments_empty : maximalSegments (∅ : Set V) = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  rintro T ⟨⟨hsub, ⟨a, b, rfl⟩⟩, _⟩
  exact hsub (left_mem_segment ℝ a b)

@[simp]
theorem maximalSegments_segment (a b : V) : maximalSegments (segment ℝ a b) = {segment ℝ a b} := by
  ext T
  refine ⟨fun h ↦ subset_antisymm h.left.left (h.2 ⟨subset_rfl, ⟨a, b, rfl⟩⟩ h.1.1), ?_⟩
  rintro rfl
  exact ⟨⟨subset_rfl, ⟨a, b, rfl⟩⟩, fun _ hU _ ↦ hU.1⟩

@[simp]
theorem maximalSegments_singleton (a : V) : maximalSegments ({a} : Set V) = {{a}} := by
  simpa only [segment_same] using maximalSegments_segment a a

private theorem exists_finite_interval_extension {S : Set ℝ} (hS : IsSegmentFigure S) :
    ∃ E : Set (ℝ × ℝ), E.Finite ∧ (∀ e ∈ E, segment ℝ e.1 e.2 ⊆ S) ∧
      ∀ a b, segment ℝ a b ⊆ S → ∃ e ∈ E, segment ℝ a b ⊆ segment ℝ e.1 e.2 := by
  let C := {C ∈ range (connectedComponentIn S) | C.Nonempty}
  have hC : C.Finite := hS.finite_range_connectedComponentIn.subset (sep_subset _ _)
  have hseg (T) (hT : T ∈ C) : T = segment ℝ (sInf T) (sSup T) := by
    obtain ⟨⟨x, rfl⟩, hne⟩ := hT
    have heq := (hS.connectedComponentIn x).eq_Icc_of_isConnected
      ⟨hne, isPreconnected_connectedComponentIn⟩
    have hle : sInf (connectedComponentIn S x) ≤ sSup (connectedComponentIn S x) :=
      nonempty_Icc.mp (heq ▸ hne)
    exact heq.trans (segment_eq_Icc hle).symm
  refine ⟨(fun T ↦ (sInf T, sSup T)) '' C, hC.image _, ?_, fun a b hab ↦ ?_⟩
  · rintro e ⟨T, hT, rfl⟩
    rw [← hseg T hT]
    obtain ⟨⟨x, rfl⟩, _⟩ := hT
    exact connectedComponentIn_subset S x
  have hcomp : connectedComponentIn S a ∈ C :=
    ⟨mem_range_self _, connectedComponentIn_nonempty_iff.mpr <| hab (left_mem_segment ℝ a b)⟩
  refine ⟨_, mem_image_of_mem _ hcomp, ?_⟩
  rw [← hseg _ hcomp]
  exact (convex_segment a b).isPreconnected.subset_connectedComponentIn (left_mem_segment ℝ a b) hab

private theorem exists_generator_line {E : Set (V × V)} (hE : E.Finite) {a b : V}
    (hsub : segment ℝ a b ⊆ ⋃ e ∈ E, segment ℝ e.1 e.2) :
    ∃ e ∈ E, a ∈ affineSpan ℝ {e.1, e.2} ∧ b ∈ affineSpan ℝ {e.1, e.2} := by
  have hspan (u v : V) : segment ℝ u v ⊆ (affineSpan ℝ {u, v} : Set V) := by
    rw [← convexHull_pair]
    exact convexHull_subset_affineSpan _
  obtain rfl | hab := eq_or_ne a b
  · obtain ⟨e, he, hae⟩ := mem_iUnion₂.mp (hsub (left_mem_segment ℝ a a))
    exact ⟨e, he, hspan _ _ hae, hspan _ _ hae⟩
  obtain ⟨e, he, hne⟩ : ∃ e ∈ E, ¬ (segment ℝ a b ∩ segment ℝ e.1 e.2).Subsingleton := by
    by_contra! h
    have hfin := hE.biUnion (fun e he ↦ (h e he).finite)
    refine hab <| (finite_segment_iff (K := ℝ)).mp (hfin.subset fun x hx ↦ ?_)
    obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp (hsub hx)
    exact mem_biUnion he ⟨hx, hxe⟩
  change ¬ ∀ ⦃x⦄, x ∈ segment ℝ a b ∩ segment ℝ e.1 e.2 →
    ∀ ⦃y⦄, y ∈ segment ℝ a b ∩ segment ℝ e.1 e.2 → x = y at hne
  push Not at hne
  obtain ⟨x, hx, y, hy, hxy⟩ := hne
  have heq : affineSpan ℝ {a, b} = affineSpan ℝ {e.1, e.2} :=
    (affineSpan_pair_eq_of_mem_of_mem_of_ne (hspan _ _ hx.1) (hspan _ _ hy.1) hxy).symm.trans
      (affineSpan_pair_eq_of_mem_of_mem_of_ne (hspan _ _ hx.2) (hspan _ _ hy.2) hxy)
  exact ⟨e, he, heq ▸ left_mem_affineSpan_pair ℝ a b, heq ▸ right_mem_affineSpan_pair ℝ a b⟩

private theorem exists_finite_segment_extension {S : Set V} (hS : IsSegmentFigure S) :
    ∃ D : Set (Set V), D.Finite ∧ (∀ d ∈ D, (∃ a b, d = segment ℝ a b) ∧ d ⊆ S) ∧
      ∀ a b, segment ℝ a b ⊆ S → ∃ d ∈ D, segment ℝ a b ⊆ d := by
  obtain ⟨E, hE, heq⟩ := hS
  have hS : IsSegmentFigure S := ⟨E, hE, heq⟩
  let J := {e ∈ E | e.1 ≠ e.2}
  have hJ : J.Finite := hE.subset (sep_subset _ _)
  let := hJ.to_subtype
  let f (e : J) : ℝ →ᵃ[ℝ] V := AffineMap.lineMap e.1.1 e.1.2
  choose A hA hAS hcover using fun e : J ↦ exists_finite_interval_extension
    (hS.preimage (f e) (AffineMap.lineMap_injective ℝ e.2.2))
  let D := (fun e : V × V ↦ ({e.1} : Set V)) '' E ∪
    ⋃ e : J, (fun t : ℝ × ℝ ↦ segment ℝ (f e t.1) (f e t.2)) '' A e
  have hDS : ∀ d ∈ D, (∃ a b, d = segment ℝ a b) ∧ d ⊆ S := by
    rintro d (⟨e, he, rfl⟩ | hd)
    · exact ⟨⟨e.1, e.1, (segment_same ℝ e.1).symm⟩,
        singleton_subset_iff.mpr (heq ▸ mem_biUnion he (left_mem_segment ℝ e.1 e.2))⟩
    obtain ⟨e, t, ht, rfl⟩ := mem_iUnion.mp hd
    refine ⟨⟨_, _, rfl⟩, ?_⟩
    change segment ℝ (f e t.1) (f e t.2) ⊆ S
    rw [← image_segment]
    exact image_subset_iff.mpr (hAS e t ht)
  refine ⟨D, (hE.image _).union (finite_iUnion fun e ↦ (hA e).image _), hDS, ?_⟩
  intro a b hab
  obtain ⟨e, he, ha, hb⟩ := exists_generator_line hE (heq ▸ hab)
  by_cases heq' : e.1 = e.2
  · have ha' : a = e.1 := by simpa [← heq', AffineSubspace.mem_affineSpan_singleton] using ha
    have hb' : b = e.1 := by simpa [← heq', AffineSubspace.mem_affineSpan_singleton] using hb
    refine ⟨{e.1}, Or.inl ⟨e, he, rfl⟩, ?_⟩
    simp [ha', hb']
  let j : J := ⟨e, he, heq'⟩
  obtain ⟨u, rfl⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp ha
  obtain ⟨v, rfl⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hb
  have huv : segment ℝ u v ⊆ (f j) ⁻¹' S := by
    rw [← image_subset_iff, image_segment]
    exact hab
  obtain ⟨t, ht, hsub⟩ := hcover j u v huv
  refine ⟨segment ℝ (f j t.1) (f j t.2), Or.inr (mem_iUnion.mpr ⟨j, t, ht, rfl⟩), ?_⟩
  rw [← image_segment, ← image_segment]
  exact image_mono hsub

namespace IsSegmentFigure

variable {S : Set V}

theorem finite_maximalSegments (hS : IsSegmentFigure S) : (maximalSegments S).Finite := by
  obtain ⟨D, hD, hDS, hcover⟩ := exists_finite_segment_extension hS
  refine hD.subset ?_
  intro T hT
  obtain ⟨a, b, rfl⟩ := hT.1.2
  obtain ⟨d, hd, habd⟩ := hcover a b hT.1.1
  have hdT := hT.2 ⟨(hDS d hd).2, (hDS d hd).1⟩ habd
  exact subset_antisymm hdT habd ▸ hd

/-- Every segment contained in a figure extends to a maximal segment. -/
theorem exists_maximalSegment (hS : IsSegmentFigure S) {a b : V}
    (hab : segment ℝ a b ⊆ S) :
    ∃ T ∈ maximalSegments S, segment ℝ a b ⊆ T := by
  obtain ⟨D, hD, hDS, hcover⟩ := exists_finite_segment_extension hS
  obtain ⟨d, hd, habd⟩ := hcover a b hab
  obtain ⟨T, hdT, hT⟩ := hD.exists_le_maximal hd
  refine ⟨T, ⟨⟨(hDS T hT.1).2, (hDS T hT.1).1⟩, ?_⟩, habd.trans hdT⟩
  rintro U ⟨hceS, ⟨c, e, rfl⟩⟩ hTce
  obtain ⟨d', hd', hced⟩ := hcover c e hceS
  exact hced.trans (hT.2 hd' (hTce.trans hced))

theorem sUnion_maximalSegments (hS : IsSegmentFigure S) : ⋃₀ maximalSegments S = S := by
  refine subset_antisymm (sUnion_subset fun T hT ↦ hT.1.1) ?_
  intro x hx
  obtain ⟨T, hT, hxT⟩ := hS.exists_maximalSegment
    (show segment ℝ x x ⊆ S by simpa using singleton_subset_iff.mpr hx)
  exact mem_sUnion.mpr ⟨T, hT, hxT (left_mem_segment ℝ x x)⟩

end IsSegmentFigure

/-- Singleton maximal segments are exactly the isolated points of the figure. -/
theorem IsSegmentFigure.singleton_mem_maximalSegments_iff [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V] {S : Set V}
    (hS : IsSegmentFigure S) (x : S) :
    ({(x : V)} : Set V) ∈ maximalSegments S ↔ IsOpen ({x} : Set S) := by
  constructor
  · intro h
    let M := {T ∈ maximalSegments S | T ≠ {(x : V)}}
    let K := ⋃ T ∈ M, T
    have hM : M.Finite := hS.finite_maximalSegments.subset (sep_subset _ _)
    have hK : IsClosed K := hM.isClosed_biUnion fun T hT ↦ by
      obtain ⟨a, b, rfl⟩ := hT.1.1.2
      exact (isCompact_segment a b).isClosed
    have hxK : (x : V) ∉ K := by
      intro hxK
      obtain ⟨T, ⟨hT, hne⟩, hxT⟩ := mem_iUnion₂.mp hxK
      have hxT' := singleton_subset_iff.mpr hxT
      exact hne (subset_antisymm (h.2 hT.1 hxT') hxT')
    have heq : (Subtype.val : S → V) ⁻¹' Kᶜ = {x} := by
      ext y
      constructor
      · intro hy
        have hyS : (y : V) ∈ ⋃₀ maximalSegments S := by
          rw [hS.sUnion_maximalSegments]
          exact y.2
        obtain ⟨T, hT, hyT⟩ := mem_sUnion.mp hyS
        by_cases hTx : T = {(x : V)}
        · exact Subtype.ext (show (y : V) ∈ {(x : V)} from hTx ▸ hyT)
        exact (hy (mem_biUnion ⟨hT, hTx⟩ hyT)).elim
      · rintro rfl
        exact hxK
    rw [← heq]
    exact hK.isOpen_compl.preimage continuous_subtype_val
  · intro hx
    apply mem_maximalSegments_iff.mpr
    refine ⟨⟨(x : V), (x : V), (segment_same ℝ _).symm⟩,
      singleton_subset_iff.mpr x.2, ?_⟩
    intro a b hxseg hsegS
    have hpre : IsPreconnected ((Subtype.val : S → V) ⁻¹' segment ℝ a b) := by
      apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
      rw [Subtype.image_preimage_coe, inter_eq_right.mpr hsegS]
      exact (convex_segment a b).isPreconnected
    have hsub := hpre.subset_isClopen ⟨isClosed_singleton, hx⟩
      ⟨x, hxseg (mem_singleton _), rfl⟩
    refine subset_antisymm (fun y hy ↦ ?_) hxseg
    have heq : (⟨y, hsegS hy⟩ : S) = x := hsub hy
    exact congrArg Subtype.val heq

/-- Injective affine maps transport the intrinsic maximal-segment family exactly. -/
theorem maximalSegments_image (S : Set V) (f : V →ᵃ[ℝ] W) (hf : Function.Injective f) :
    maximalSegments (f '' S) = (fun T ↦ f '' T) '' maximalSegments S := by
  ext U
  constructor
  · intro hU
    obtain ⟨⟨p, q, rfl⟩, hsub, hmax⟩ := mem_maximalSegments_iff.mp hU
    obtain ⟨a, ha, rfl⟩ := hsub (left_mem_segment ℝ p q)
    obtain ⟨b, hb, rfl⟩ := hsub (right_mem_segment ℝ (f a) q)
    refine ⟨segment ℝ a b, mem_maximalSegments_iff.mpr ⟨⟨a, b, rfl⟩, ?_, ?_⟩,
      image_segment ℝ f a b⟩
    · exact (image_subset_image_iff hf).mp (by rwa [image_segment])
    intro c d hab hcd
    apply hf.image_injective
    rw [image_segment, image_segment]
    exact hmax (f c) (f d) (by simpa only [← image_segment] using image_mono hab)
      (by simpa only [← image_segment] using image_mono hcd)
  · rintro ⟨T, hT, rfl⟩
    obtain ⟨⟨a, b, rfl⟩, hsub, hmax⟩ := mem_maximalSegments_iff.mp hT
    apply mem_maximalSegments_iff.mpr
    refine ⟨⟨f a, f b, image_segment ℝ f a b⟩, image_mono hsub, ?_⟩
    intro p q hpq hpqS
    obtain ⟨c, hc, rfl⟩ := hpqS (left_mem_segment ℝ p q)
    obtain ⟨d, hd, rfl⟩ := hpqS (right_mem_segment ℝ (f c) q)
    rw [← image_segment] at hpq hpqS ⊢
    exact congrArg (fun T ↦ f '' T)
      (hmax c d ((image_subset_image_iff hf).mp hpq) ((image_subset_image_iff hf).mp hpqS))

end
