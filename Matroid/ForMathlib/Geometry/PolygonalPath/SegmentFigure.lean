module

public import Matroid.ForMathlib.Geometry.PolygonalPath.Basic
public import Matroid.ForMathlib.Geometry.PolygonalPath.PrimitivePath
public import Matroid.ForMathlib.Geometry.SegmentFigure.Star
public import Matroid.ForMathlib.Geometry.SegmentFigure.Subset
public import Matroid.ForMathlib.Topology.PrimitiveLink

/-!
# Polygonal representatives of primitive links

Polygonal paths trace segment figures. Conversely, a primitive link contained in a segment figure
has a primitive polygonal representative. This includes loops and subarcs of figures that branch.
-/

@[expose] public section

open Set Path

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {a b p x y : V} {γ : Path a b} {r : ℝ}

/-- The set traced by a polygonal path is a segment figure. -/
@[grind .]
theorem PolygonalPath.isSegmentFigure_toSet (P : PolygonalPath x y) : IsSegmentFigure P.toSet := by
  rw [PolygonalPath.toSet_eq_insert_biUnion]
  exact (IsSegmentFigure.biUnion P.edges.finite_toSet
    (fun s _ ↦ isSegmentFigure_segment s.1 s.2)).insert y

open Function Metric unitInterval PolygonalPath Or

open Classical in
private lemma exists_polygonalPath_in_star (hγ : γ.IsPrimitive) (hr : 0 < r) {Y : Finset V}
    (hY : ↑Y ⊆ sphere p r) (hsub : range γ ⊆ {p} ∪ ⋃ y ∈ Y, segment ℝ p y) :
    ∃ P : PolygonalPath a b, P.toSet = range γ := by
  refine γ.exists_polygonalPath_of_finite_cuts
    ((hγ.finite_preimage <| finite_singleton p).insert half) fun s t hst hcut ↦ ?_
  have hne : γ s ≠ γ t := by
    intro heq
    obtain heq | heq := hγ heq
    · exact hst.ne heq
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := pair_eq_pair_iff.mp heq
    · exact hcut half ⟨zero_lt_half, half_lt_one⟩ <| inl rfl
    exact hst.not_ge zero_le_one
  let K := γ '' Ioo s t
  have hK : IsConnected K := (isConnected_Ioo hst).image γ γ.continuous.continuousOn
  have hp : p ∉ K := fun ⟨u, hu, heq⟩ ↦ hcut u hu <| inr heq
  have hcover : K ⊆ ⋃ y ∈ Y, segment ℝ p y :=
    fun z hz ↦ (hsub <| image_subset_range _ _ hz).resolve_left (hp <| · ▸ hz)
  obtain ⟨z, hz⟩ := hK.nonempty
  obtain ⟨y, hy, hzy⟩ := mem_iUnion₂.mp <| hcover hz
  have hseg : K ⊆ segment ℝ p y := by
    intro w hw
    by_contra hwy
    have hKB : K ⊆ segment ℝ p y ∪ ⋃ v ∈ Y.erase y, segment ℝ p v := by
      intro q hq
      obtain ⟨v, hv, hqv⟩ := mem_iUnion₂.mp <| hcover hq
      by_cases hvy : v = y
      · exact inl <| hvy ▸ hqv
      exact inr <| mem_iUnion₂.mpr ⟨v, Finset.mem_erase.mpr ⟨hvy, hv⟩, hqv⟩
    obtain ⟨q, hq, hqy, hqB⟩ := isPreconnected_closed_iff.mp hK.isPreconnected
      _ _ (isCompact_segment p y).isClosed ((Y.erase y).finite_toSet.isClosed_biUnion
        fun v _ ↦ (isCompact_segment p v).isClosed) hKB ⟨z, hz, hzy⟩
      ⟨w, hw, (hKB hw).resolve_left hwy⟩
    obtain ⟨v, hv, hqv⟩ := mem_iUnion₂.mp hqB
    exact hp <| eq_center_of_mem_two_radii (ne_of_mem_sphere (hY hy) hr.ne')
      ((hY (Finset.mem_erase.mp hv).right).trans (hY hy).symm) (Finset.mem_erase.mp hv).left.symm hqy hqv ▸ hq
  have hpiece : range (γ.subpath s t) ⊆ segment ℝ p y := by
    simpa only [γ.range_subpath_of_le _ _ hst.le, ← closure_Ioo hst.ne] using
      (image_closure_subset_closure_image γ.continuous).trans <|
        (isCompact_segment p y).isClosed.closure_subset_iff.mpr hseg
  exact ⟨direct (γ s) <| γ t,
    (toSet_direct ..).trans (range_eq_segment_of_subset (hγ.injective_subpath hne) hpiece).symm⟩

/-- Every primitive path contained in a segment figure has a polygonal representative with
exactly the same image. The parametrization is used only to select finitely many pieces. -/
private theorem Path.IsPrimitive.exists_polygonalPath_of_isSegmentFigure (hγ : γ.IsPrimitive)
    {S : Set V} (hS : IsSegmentFigure S) (hsub : range γ ⊆ S) :
    ∃ P : PolygonalPath a b, P.toSet = range γ := open Nat in by
  choose r hr Y hY hstar using (hS.exists_radius <| hsub <| mem_range_self ·)
  obtain ⟨t, ht0, hmono, ⟨N, hN⟩, hcover⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (fun u : I ↦ isOpen_ball.preimage γ.continuous)
      (fun u _ ↦ mem_iUnion.mpr ⟨u, mem_ball_self <| hr u⟩)
  have hpieces (n) : ∃ P : PolygonalPath (γ <| t n) <| γ <| t <| n + 1,
      P.toSet = γ '' (Icc (t n) <| t <| n + 1) := by
    obtain heq | hlt := (hmono <| le_succ n).eq_or_lt
    · exact ⟨(nil <| γ <| t n).cast rfl <| congrArg γ heq, by
      simp only [toSet_cast, toSet_nil, heq, Icc_self, image_singleton]⟩
    obtain ⟨u, hu⟩ := hcover n
    obtain ⟨P, hP⟩ := exists_polygonalPath_in_star (hγ.subpath hlt.ne) (hr u) (hY u) (by
      rw [range_subpath_of_le _ _ _ hlt.le]
      rintro z ⟨v, hv, rfl⟩
      exact (hstar u).subset ⟨ball_subset_closedBall <| hu hv, hsub <| mem_range_self v⟩)
    exact ⟨P, hP.trans <| γ.range_subpath_of_le _ _ hlt.le⟩
  have hprefix (n) : ∃ P : PolygonalPath (γ <| t 0) <| γ <| t n,
      P.toSet = γ '' Icc (t 0) (t n) := by
    induction n with
    | zero => exact ⟨nil _, by
      simp only [toSet_nil, Icc_self, image_singleton]⟩
    | succ n ih =>
      obtain ⟨P, hP⟩ := ih
      obtain ⟨Q, hQ⟩ := hpieces n
      exact ⟨P.append Q, by
        rw [toSet_append, hP, hQ, ← image_union,
          Icc_union_Icc_eq_Icc (hmono <| zero_le n) <| hmono <| le_succ n]⟩
  obtain ⟨P, hP⟩ := hprefix N
  refine ⟨P.cast (ht0 ▸ γ.source) <| hN N le_rfl ▸ γ.target, ?_⟩
  simpa only [toSet_cast, ht0, hN N le_rfl, Icc_eq_univ, image_univ] using hP

/-- A set is a primitive link and a segment figure if and only if it has a primitive
polygonal representative. -/
theorem isPrimitiveLink_and_isSegmentFigure_iff {L : Set V} :
    IsPrimitiveLink L a b ∧ IsSegmentFigure L ↔
      ∃ P : PolygonalPath a b, P.toPath.IsPrimitive ∧ P.toSet = L := by
  constructor
  · rintro ⟨⟨γ, hγ, rfl⟩, hpoly⟩
    have hγ' := γ.firstHalf_range_union_secondHalf_range
    obtain ⟨A, hA⟩ := IsPrimitive.of_injective hγ.injective_firstHalf
      |>.exists_polygonalPath_of_isSegmentFigure hpoly (hγ' ▸ subset_union_left)
    obtain ⟨B, hB⟩ := IsPrimitive.of_injective hγ.injective_secondHalf
      |>.exists_polygonalPath_of_isSegmentFigure hpoly (hγ' ▸ subset_union_right)
    obtain ⟨A, hAp, hA⟩ :=
      γ.firstHalf.exists_primitive_polygonalPath_of_toSet_subset hγ.injective_firstHalf A hA.le
    obtain ⟨B, hBp, hB⟩ :=
      γ.secondHalf.exists_primitive_polygonalPath_of_toSet_subset hγ.injective_secondHalf B hB.le
    refine ⟨A.append B, ?_, by rw [toSet_append, hA, hB, hγ']⟩
    rw [isPrimitive_append_iff hγ.half_ne_source.symm]
    refine ⟨(isPrimitive_iff_isSimple hγ.half_ne_source.symm).mp hAp,
      (isPrimitive_iff_isSimple hγ.half_ne_target).mp hBp, ?_⟩
    rw [hA, hB, hγ.firstHalf_range_inter_secondHalf_range]
    intro z hz
    obtain rfl | ⟨rfl, hz⟩ := hz <;> simp_all
  rintro ⟨P, hP, rfl⟩
  exact ⟨⟨P.toPath, hP, P.toSet_eq_range_toPath.symm⟩, P.isSegmentFigure_toSet⟩

/-- A primitive link that is a segment figure has a primitive polygonal representative,
including when its endpoints coincide. -/
theorem IsPrimitiveLink.exists_polygonalPath {L : Set V} (hL : IsPrimitiveLink L a b)
    (hpoly : IsSegmentFigure L) :
    ∃ P : PolygonalPath a b, P.toPath.IsPrimitive ∧ P.toSet = L :=
  isPrimitiveLink_and_isSegmentFigure_iff.mp ⟨hL, hpoly⟩

/-- A primitive link contained in a segment figure is itself a segment figure. -/
theorem IsSegmentFigure.of_isPrimitiveLink_subset {S L : Set V} {a b : V}
    (hS : IsSegmentFigure S) (hL : IsPrimitiveLink L a b) (hsub : L ⊆ S) :
    IsSegmentFigure L :=
  hS.of_isClosed_isPreconnected hsub hL.isCompact.isClosed hL.isConnected.isPreconnected

end
