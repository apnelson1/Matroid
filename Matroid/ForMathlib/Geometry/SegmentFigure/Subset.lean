module

public import Matroid.ForMathlib.Geometry.SegmentFigure.Subdivision
public import Matroid.ForMathlib.Geometry.SegmentFigure.Real

/-!
# Closed subsets of segment figures

Closed connected subsets of a figure are figures. More generally, closed subsets with
finitely many connected components are figures. The key restriction is connectedness:
arbitrary closed subsets of a segment need not be finite unions of segments.
-/

@[expose] public section

open Set

private theorem real_isSegmentFigure_of_isCompact_isPreconnected {C : Set ℝ}
    (hc : IsCompact C) (hconn : IsPreconnected C) : IsSegmentFigure C := by
  obtain rfl | hne := C.eq_empty_or_nonempty
  · exact isSegmentFigure_empty
  rw [eq_Icc_of_connected_compact ⟨hne, hconn⟩ hc]
  exact isSegmentFigure_Icc _ _

/-- A compact subset of an interval with a convex gap has at most two interval pieces. -/
private theorem real_isSegmentFigure_of_convex_gap {C : Set ℝ} {a b : ℝ}
    (hc : IsCompact C) (hsub : C ⊆ Icc a b) (hgap : Convex ℝ (Icc a b \ C)) :
    IsSegmentFigure C := by
  obtain h | ⟨r, hr, hrC⟩ := (Icc a b \ C).eq_empty_or_nonempty
  · have heq : C = Icc a b := subset_antisymm hsub (sdiff_eq_empty.mp h)
    rw [heq]
    exact isSegmentFigure_Icc _ _
  have hleft : Convex ℝ (C ∩ Iic r) := convex_iff_ordConnected.mpr ⟨by
    intro u hu v hv t ht
    refine ⟨?_, ht.2.trans hv.2⟩
    by_contra htC
    have htI : t ∈ Icc a b := ⟨(hsub hu.1).1.trans ht.1, ht.2.trans (hsub hv.1).2⟩
    exact (hgap.ordConnected.out ⟨htI, htC⟩ ⟨hr, hrC⟩ ⟨ht.2, hv.2⟩).2 hv.1⟩
  have hright : Convex ℝ (C ∩ Ici r) := convex_iff_ordConnected.mpr ⟨by
    intro u hu v hv t ht
    refine ⟨?_, hu.2.trans ht.1⟩
    by_contra htC
    have htI : t ∈ Icc a b := ⟨(hsub hu.1).1.trans ht.1, ht.2.trans (hsub hv.1).2⟩
    exact (hgap.ordConnected.out ⟨hr, hrC⟩ ⟨htI, htC⟩ ⟨hu.2, ht.1⟩).2 hu.1⟩
  have heq : C = (C ∩ Iic r) ∪ (C ∩ Ici r) := by
    ext x
    simp only [mem_union, mem_inter_iff, mem_Iic, mem_Ici]
    exact ⟨fun hx ↦ (le_total x r).elim (fun h ↦ Or.inl ⟨hx, h⟩)
      (fun h ↦ Or.inr ⟨hx, h⟩), fun h ↦ h.elim And.left And.left⟩
  rw [heq]
  exact (real_isSegmentFigure_of_isCompact_isPreconnected (hc.inter_right isClosed_Iic)
    hleft.isPreconnected).union
    (real_isSegmentFigure_of_isCompact_isPreconnected (hc.inter_right isClosed_Ici)
      hright.isPreconnected)

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]

/-- If a segment meets the rest of a closed cover only at its endpoints, a connected set
that reaches the rest cannot have two separated gaps in the segment. -/
private theorem convex_segment_parameter_gap {C K : Set V} {a b : V} (hab : a ≠ b)
    (hK : IsClosed K) (hattach : segment ℝ a b ∩ K ⊆ {a, b})
    (hconn : IsPreconnected C) (hsub : C ⊆ segment ℝ a b ∪ K)
    (hout : ¬ C ⊆ segment ℝ a b) :
    Convex ℝ (Icc (0 : ℝ) 1 \ (AffineMap.lineMap a b : ℝ → V) ⁻¹' C) := by
  let f : ℝ →ᵃ[ℝ] V := AffineMap.lineMap a b
  have hf : Function.Injective f := AffineMap.lineMap_injective ℝ hab
  have h0 : f 0 = a := by simp [f]
  have h1 : f 1 = b := by simp [f]
  obtain ⟨w, hwC, hw⟩ := not_subset.mp hout
  have hwK := (hsub hwC).resolve_left hw
  apply convex_iff_ordConnected.mpr
  refine ⟨?_⟩
  intro u hu v hv t ht
  refine ⟨⟨hu.1.1.trans ht.1, ht.2.trans hv.1.2⟩, ?_⟩
  intro htC
  let H := f '' Icc u v
  let L := (K ∪ f '' Icc 0 u) ∪ f '' Icc v 1
  have hH : IsClosed H := (isCompact_Icc.image AffineMap.lineMap_continuous).isClosed
  have hL : IsClosed L :=
    (hK.union (isCompact_Icc.image AffineMap.lineMap_continuous).isClosed).union
      (isCompact_Icc.image AffineMap.lineMap_continuous).isClosed
  have hcover : C ⊆ H ∪ L := by
    intro x hx
    obtain hx | hx := hsub hx
    · rw [segment_eq_image_lineMap] at hx
      obtain ⟨r, hr, rfl⟩ := hx
      by_cases hru : r ≤ u
      · exact Or.inr (Or.inl (Or.inr ⟨r, ⟨hr.1, hru⟩, rfl⟩))
      by_cases hvr : v ≤ r
      · exact Or.inr (Or.inr ⟨r, ⟨hvr, hr.2⟩, rfl⟩)
      exact Or.inl ⟨r, ⟨(lt_of_not_ge hru).le, (lt_of_not_ge hvr).le⟩, rfl⟩
    · exact Or.inr (Or.inl (Or.inl hx))
  obtain ⟨z, hzC, ⟨s, hs, rfl⟩, hzL⟩ := isPreconnected_closed_iff.mp hconn H L hH hL
    hcover ⟨f t, htC, t, ht, rfl⟩ ⟨w, hwC, Or.inl (Or.inl hwK)⟩
  have hsu : s = u ∨ s = v := by
    obtain (hzK | ⟨r, hr, hrs⟩) | ⟨r, hr, hrs⟩ := hzL
    · have hsI : s ∈ Icc (0 : ℝ) 1 := ⟨hu.1.1.trans hs.1, hs.2.trans hv.1.2⟩
      have hsseg : f s ∈ segment ℝ a b := lineMap_mem_segment ℝ a b hsI
      obtain h | h : f s = a ∨ f s = b := hattach ⟨hsseg, hzK⟩
      · have := hf (h.trans h0.symm)
        left
        linarith [hu.1.1, hs.1]
      · have := hf (h.trans h1.symm)
        right
        linarith [hv.1.2, hs.2]
    · have := hf hrs
      left
      linarith [hr.2, hs.1]
    · have := hf hrs
      right
      linarith [hr.1, hs.2]
  exact hsu.elim (fun h ↦ hu.2 (h ▸ hzC)) (fun h ↦ hv.2 (h ▸ hzC))

namespace IsSegmentFigure

variable {S C : Set V}

/-- Closed preconnected subsets inherit the finite-segment geometry. The empty subset is allowed. -/
theorem of_isClosed_isPreconnected (hS : IsSegmentFigure S) (hCS : C ⊆ S)
    (hc : IsClosed C) (hconn : IsPreconnected C) : IsSegmentFigure C := by
  obtain ⟨B, hB, _, hBS, D, hD, hSD, hpieces, hpair⟩ :=
    hS.exists_subdivision finite_empty (empty_subset S)
  have hCeq : C = ⋃ d ∈ D, C ∩ d := by
    rw [← inter_iUnion₂, ← sUnion_eq_biUnion, ← hSD, inter_eq_left.mpr hCS]
  rw [hCeq]
  refine IsSegmentFigure.biUnion hD ?_
  intro d hd
  obtain ⟨a, ha, b, hb, rfl, hav⟩ := hpieces d hd
  by_cases hab : a = b
  · subst b
    exact of_finite ((finite_singleton a).subset (by simp))
  let f : ℝ →ᵃ[ℝ] V := AffineMap.lineMap a b
  have hf : Function.Injective f := AffineMap.lineMap_injective ℝ hab
  let T := Icc (0 : ℝ) 1 ∩ f ⁻¹' C
  have hTcompact : IsCompact T := isCompact_Icc.inter_right
    (hc.preimage AffineMap.lineMap_continuous)
  have him : f '' T = C ∩ segment ℝ a b := by
    rw [image_inter_preimage, ← segment_eq_image_lineMap, inter_comm]
  rw [← him]
  apply IsSegmentFigure.image (f := f)
  by_cases hCe : C ⊆ segment ℝ a b
  · have hpre : f ⁻¹' C ⊆ Icc (0 : ℝ) 1 := by
      intro t ht
      have := hCe ht
      rw [segment_eq_image_lineMap] at this
      exact hf.mem_set_image.mp this
    have hT : T = f ⁻¹' C := inter_eq_right.mpr hpre
    have hclosed : IsClosedMap f := by
      have hfun : (f : ℝ → V) = fun t ↦ t • (b - a) + a :=
        funext (AffineMap.lineMap_apply_module' a b)
      rw [hfun]
      exact (isClosedMap_add_right a).comp (isClosedMap_smul_left (𝕜 := ℝ) (b - a))
    apply real_isSegmentFigure_of_isCompact_isPreconnected hTcompact
    rw [hT]
    exact hconn.preimage_of_isClosedMap hf hclosed fun x hx ↦
      (segment_eq_image_lineMap ℝ a b ▸ hCe hx).elim fun t ht ↦ ⟨t, ht.2⟩
  let K := ⋃ d ∈ D \ {segment ℝ a b}, d
  have hK : IsClosed K := by
    apply IsCompact.isClosed
    refine (hD.subset sdiff_subset).isCompact_biUnion ?_
    intro d hd
    obtain ⟨c, _, e, _, rfl, _⟩ := hpieces d hd.1
    exact isCompact_segment c e
  have hattach : segment ℝ a b ∩ K ⊆ {a, b} := by
    rintro x ⟨hx, hxK⟩
    obtain ⟨d, hd', hxd⟩ := mem_iUnion₂.mp hxK
    exact hav ⟨hx, hpair hd hd'.1 (Ne.symm (by simpa using hd'.2)) ⟨hx, hxd⟩⟩
  have hcover : C ⊆ segment ℝ a b ∪ K := by
    intro x hx
    have hxS := hCS hx
    rw [hSD] at hxS
    obtain ⟨d, hd', hxd⟩ := mem_sUnion.mp hxS
    by_cases heq : d = segment ℝ a b
    · exact Or.inl (heq ▸ hxd)
    exact Or.inr (mem_biUnion ⟨hd', heq⟩ hxd)
  apply real_isSegmentFigure_of_convex_gap hTcompact inter_subset_left
  have hgap := convex_segment_parameter_gap hab hK hattach hconn hcover hCe
  convert hgap using 1
  ext t
  simp [T, f]

/-- The intrinsic characterization of the subsets that retain finite-segment geometry. -/
theorem iff_isClosed_finite_connectedComponents (hS : IsSegmentFigure S) (hCS : C ⊆ S) :
    IsSegmentFigure C ↔ IsClosed C ∧ Finite (ConnectedComponents C) := by
  refine ⟨fun h ↦ ⟨h.isClosed, h.finite_connectedComponents⟩, ?_⟩
  rintro ⟨hc, hfin⟩
  let := hfin
  choose r hr using (ConnectedComponents.surjective_coe (α := C))
  have heq : C = ⋃ q : ConnectedComponents C,
      Subtype.val '' connectedComponent (r q) := by
    apply subset_antisymm
    · intro x hx
      let y : C := ⟨x, hx⟩
      refine mem_iUnion.mpr ⟨ConnectedComponents.mk y, y, ?_, rfl⟩
      have heq := ConnectedComponents.coe_eq_coe.mp (hr (ConnectedComponents.mk y))
      rw [heq]
      exact mem_connectedComponent
    · intro x hx
      obtain ⟨q, y, _, rfl⟩ := mem_iUnion.mp hx
      exact y.2
  rw [heq]
  refine IsSegmentFigure.iUnion fun q ↦ hS.of_isClosed_isPreconnected ?_ ?_ ?_
  · rintro x ⟨y, _, rfl⟩
    exact hCS y.2
  · exact hc.isClosedEmbedding_subtypeVal.isClosedMap _ isClosed_connectedComponent
  · exact isPreconnected_connectedComponent.image _ continuous_subtype_val.continuousOn

end IsSegmentFigure

end
