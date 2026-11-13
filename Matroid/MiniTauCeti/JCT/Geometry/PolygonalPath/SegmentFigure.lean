module

public import Matroid.MiniTauCeti.JCT.Geometry.PolygonalPath.Basic
public import Matroid.MiniTauCeti.JCT.Geometry.PolygonalPath.PrimitivePath
public import Matroid.MiniTauCeti.JCT.Geometry.SegmentFigure.Star
public import Matroid.MiniTauCeti.JCT.Geometry.SegmentFigure.Subset
public import Matroid.MiniTauCeti.JCT.Topology.PrimitiveLink

/-!
# Polygonal representatives of primitive links

Polygonal paths trace segment figures. Conversely, a primitive link contained in a segment figure
has a primitive polygonal representative. This includes loops and subarcs of figures that branch.
-/

@[expose] public section

open Set Path

/-- The set traced by a polygonal path is a segment figure. -/
@[grind .]
theorem PolygonalPath.isSegmentFigure_toSet {V : Type*} [AddCommGroup V] [Module ℝ V]
    {x y : V} (P : PolygonalPath x y) : IsSegmentFigure P.toSet := by
  rw [PolygonalPath.toSet_eq_insert_biUnion]
  exact (IsSegmentFigure.biUnion P.edges.finite_toSet
    (fun s _ ↦ isSegmentFigure_segment s.fst s.snd)).insert y

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {a b p x y : V} {γ : Path a b} {r : ℝ}

open Function Metric unitInterval PolygonalPath Or

open Classical Finset in
private lemma exists_polygonalPath_in_star (hγ : γ.IsPrimitive) (hr : 0 < r) {Y : Finset V}
    (hY : ↑Y ⊆ sphere p r) (hsub : range γ ⊆ {p} ∪ ⋃ y ∈ Y, segment ℝ p y) :
    ∃ P : PolygonalPath a b, P.toSet = range γ := by
  refine γ.exists_polygonalPath_of_finite_cuts
    ((hγ.finite_preimage <| finite_singleton p).insert half) fun s t hst hcut ↦ ?_
  have hne : γ s ≠ γ t := by
    intro heq
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := pair_eq_pair_iff.mp <| (hγ heq).resolve_left hst.ne
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
      obtain rfl | hvy := eq_or_ne v y
      · exact inl hqv
      exact inr <| mem_iUnion₂.mpr ⟨v, mem_erase.mpr ⟨hvy, hv⟩, hqv⟩
    obtain ⟨q, hq, hqy, hqB⟩ :=
      isPreconnected_closed_iff.mp hK.isPreconnected _ _ (isCompact_segment p y).isClosed
      ((Y.erase y).finite_toSet.isClosed_biUnion fun v _ ↦ (isCompact_segment p v).isClosed) hKB
      ⟨z, hz, hzy⟩ ⟨w, hw, (hKB hw).resolve_left hwy⟩
    obtain ⟨v, hv, hqv⟩ := mem_iUnion₂.mp hqB
    exact hp <| eq_center_of_mem_two_radii (ne_of_mem_sphere (hY hy) hr.ne')
      ((hY (mem_erase.mp hv).right).trans (hY hy).symm) (mem_erase.mp hv).left.symm
        hqy hqv ▸ hq
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
    · refine ⟨(nil <| γ <| t n).cast rfl <| congrArg γ heq, ?_⟩
      simp only [toSet_cast, toSet_nil, heq, Icc_self, image_singleton]
    obtain ⟨u, hu⟩ := hcover n
    obtain ⟨P, hP⟩ := exists_polygonalPath_in_star (hγ.subpath hlt.ne) (hr u) (hY u) (by
      rw [range_subpath_of_le _ _ _ hlt.le]
      rintro z ⟨v, hv, rfl⟩
      exact (hstar u).subset ⟨ball_subset_closedBall <| hu hv, hsub <| mem_range_self v⟩)
    exact ⟨P, hP.trans <| γ.range_subpath_of_le _ _ hlt.le⟩
  have hprfix (n) : ∃ P : PolygonalPath (γ <| t 0) <| γ <| t n, P.toSet = γ '' Icc (t 0) (t n) := by
    induction n with
    | zero =>
      refine ⟨nil _, ?_⟩
      simp only [toSet_nil, Icc_self, image_singleton]
    | succ n ih =>
      obtain ⟨P, hP⟩ := ih
      obtain ⟨Q, hQ⟩ := hpieces n
      refine ⟨P.append Q, ?_⟩
      rw [toSet_append, hP, hQ, ← image_union,
        Icc_union_Icc_eq_Icc (hmono <| zero_le n) <| hmono <| le_succ n]
  obtain ⟨P, hP⟩ := hprfix N
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
    have hAp := A.isPrimitive_simpleArc hγ.half_ne_source.symm
    have hBp := B.isPrimitive_simpleArc hγ.half_ne_target
    have hA := γ.firstHalf.toSet_simpleArc_eq_range hγ.injective_firstHalf A hA.le
    have hB := γ.secondHalf.toSet_simpleArc_eq_range hγ.injective_secondHalf B hB.le
    refine ⟨A.simpleArc.append B.simpleArc, ?_, by rw [toSet_append, hA, hB, hγ']⟩
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
    (hpoly : IsSegmentFigure L) : ∃ P : PolygonalPath a b, P.toPath.IsPrimitive ∧ P.toSet = L :=
  isPrimitiveLink_and_isSegmentFigure_iff.mp ⟨hL, hpoly⟩

/-- A primitive link contained in a segment figure is itself a segment figure. -/
theorem IsSegmentFigure.of_isPrimitiveLink_subset {S L : Set V} {a b : V}
    (hS : IsSegmentFigure S) (hL : IsPrimitiveLink L a b) (hsub : L ⊆ S) : IsSegmentFigure L :=
  hS.of_isClosed_isPreconnected hsub hL.isCompact.isClosed hL.isConnected.isPreconnected

private theorem simple_first_contact {X : Type*} [AddCommGroup X] [Module ℝ X]
    [TopologicalSpace X] [ContinuousAdd X] [ContinuousSMul ℝ X] {p r : X}
    {P : PolygonalPath p r} [T2Space P.toSet] (hP : P.IsSimple) {C : Set X} (hC : IsClosed C)
    (hp : p ∉ C) (hr : r ∈ C) :
    ∃ q ∈ P.toSet ∩ C, ∃ L : Set X, IsPrimitiveLink L p q ∧ IsSegmentFigure L ∧
      L ⊆ P.toSet ∧ L \ {q} ⊆ connectedComponentIn Cᶜ p := by
  obtain ⟨t, ht, htc, hbefore⟩ := P.toPath.exists_first_contact
    (hC.preimage P.toPath.continuous) hp ⟨r, P.toPath.target_mem_range, hr⟩
  have hqt : P.toPath t ∈ P.toSet := P.toSet_eq_range_toPath.symm ▸ mem_range_self t
  let A := (P.breakAt hqt).1
  have hAsimple : A.IsSimple := (hP.breakAt hqt).1
  have hAset : A.toSet = P.toPath '' Icc 0 t := (hP.toSet_breakAt_eq hqt rfl).1
  have hpq : p ≠ P.toPath t := fun heq ↦ hp (heq ▸ htc)
  have hAsub : A.toSet ⊆ P.toSet := by
    rw [hAset, P.toSet_eq_range_toPath]
    exact image_subset_range ..
  refine ⟨P.toPath t, ⟨hqt, htc⟩, A.toSet, ?_, A.isSegmentFigure_toSet, hAsub, ?_⟩
  · rw [A.toSet_eq_range_toPath]
    exact (hAsimple.isPrimitive (A.length_pos_of_ne hpq)).isPrimitiveLink
  · rintro z ⟨hz, hzq⟩
    rw [hAset] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    exact hbefore ⟨u, ⟨hu.1, lt_of_le_of_ne hu.2 (fun h ↦ hzq (congrArg P.toPath h))⟩, rfl⟩

/-- A polygonal path meeting a closed set contains a polygonal arc from its source to that set.
All other points of the arc lie in the source's complementary component. -/
theorem PolygonalPath.exists_primitiveLink_first_contact {X : Type*}
    [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    [ContinuousAdd X] [ContinuousSMul ℝ X]
    {p r : X} (P : PolygonalPath p r) [T2Space P.toSet] {C : Set X} (hC : IsClosed C)
    (hp : p ∉ C) (hmeet : (P.toSet ∩ C).Nonempty) :
    ∃ q ∈ P.toSet ∩ C, ∃ L : Set X, IsPrimitiveLink L p q ∧ IsSegmentFigure L ∧
      L ⊆ P.toSet ∧ L \ {q} ⊆ connectedComponentIn Cᶜ p := by
  obtain ⟨z, hzP, hzC⟩ := hmeet
  let Q := (P.breakAt hzP).1.simpleArc
  have hQ := (P.breakAt hzP).1.isSimple_simpleArc
  have hQP := (P.breakAt hzP).1.toSet_simpleArc_subset
  have hsub : Q.toSet ⊆ P.toSet := hQP.trans
    (subset_union_left.trans (P.breakAt_toSet_union hzP).subset)
  have : T2Space Q.toSet := (Topology.IsEmbedding.inclusion hsub).t2Space
  obtain ⟨q, hq, L, hL, hpoly, hLQ, hbefore⟩ := simple_first_contact hQ hC hp hzC
  exact ⟨q, ⟨hsub hq.1, hq.2⟩, L, hL, hpoly, hLQ.trans hsub, hbefore⟩

end
