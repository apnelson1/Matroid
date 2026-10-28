module

public import Matroid.ForMathlib.Topology.Order
public import Matroid.ForMathlib.Analysis.Convex.SegmentCover
public import Mathlib.Analysis.Convex.Between
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.UnitInterval

/-!
# Unions, intersections, and compact connected subsets of segments

This file collects the facts about `segment` that are needed for polygonal curves, and that belong
in `Mathlib.Analysis.Convex.Segment`.

## Main statements

The imported `SegmentCover` module supplies affine injectivity and fiber criteria without topology.

* `segment_union_eq_segment`, `affineSegment_union_eq_affineSegment` : splitting a segment at one
  of its points, in a module and in an affine space respectively.
* `segment_subset_segment_right` : shortening a segment at its right endpoint.
* `IsCompact.exists_eq_segment_of_isConnected_of_subset_segment` : a nonempty compact connected
  subset of a Hausdorff segment is a segment; ambient Hausdorffness is not required.
* `isCompact_setOf_lineMap_mem_segment`, `convex_setOf_lineMap_mem_segment` : the set of
  parameters `t ∈ [0,1]` with `lineMap a b t ∈ [c, d]` is compact and convex, hence a closed
  interval (`exists_eq_Icc_setOf_lineMap_mem_segment`).
* `segment_inter_segment_eq_segment_of_nonempty` : a nonempty intersection of two segments is a
  segment.
* `exists_last_mem_segment_inter_segment` : the intersection of `[a, b]` with a segment has a last
  point along `[a, b]`.

## Implementation notes

No topology on `E` is assumed for the results about intersections: the parameter set
`{t ∈ [0,1] | lineMap a b t ∈ [c, d]}` is the projection of the intersection of `[0,1]²` with an
affine subspace of `ℝ × ℝ`, which is closed because `ℝ × ℝ` is finite-dimensional. Everything else
(compactness, connectedness, the extreme value theorem) then happens in `ℝ`.

`isCompact_setOf_lineMap_mem_segment` is the only place where that argument is made; the
intersection results below are corollaries of it together with the — purely algebraic — convexity
of the same set.
-/

@[expose] public section

open Set Function AffineMap Topology Path

/-! ### Splitting a segment -/

/-- Shortening a segment at its right endpoint. The containment half of
`segment_union_eq_segment`, but with far weaker hypotheses — no order on `𝕜` beyond
`IsOrderedRing`, since it is only convexity of the target. -/
lemma segment_subset_segment_right {𝕜 E : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]
    [AddCommMonoid E] [Module 𝕜 E] {x y z : E} (hz : z ∈ segment 𝕜 x y) :
    segment 𝕜 x z ⊆ segment 𝕜 x y := (convex_segment x y).segment_subset (left_mem_segment 𝕜 x y) hz

/-- Splitting a segment at one of its points. -/
lemma segment_union_eq_segment {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommGroup E] [Module 𝕜 E] {x y z : E} (hz : z ∈ segment 𝕜 x y) :
    segment 𝕜 x z ∪ segment 𝕜 z y = segment 𝕜 x y := by
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hz
  trans ⇑(lineMap x y) '' (Icc 0 t ∪ Icc t 1)
  · simp [image_union, image_segment, ← segment_eq_Icc ht0, ← segment_eq_Icc ht1]
  rw [Icc_union_Icc_eq_Icc ht0 ht1, segment_eq_image_lineMap]

/-- Splitting an affine segment at one of its points. -/
lemma affineSegment_union_eq_affineSegment {R V P : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [AddTorsor V P] {x y z : P}
    (hz : z ∈ affineSegment R x y) :
    affineSegment R x z ∪ affineSegment R z y = affineSegment R x y := by
  rw [← mem_vsub_const_affineSegment x, vsub_self, affineSegment_eq_segment] at hz
  ext w
  simp only [mem_union, ← mem_vsub_const_affineSegment (R := R) x, vsub_self,
    affineSegment_eq_segment]
  exact Set.ext_iff.mp (segment_union_eq_segment hz) (w -ᵥ x)

/-- Splitting a segment at an *interior* point: the two halves meet only in that point. The
companion to `segment_union_eq_segment`, which says they cover it. -/
lemma segment_inter_subsegments_eq_singleton {E : Type*} [AddCommGroup E] [Module ℝ E]
    {u v a : E} (huv : u ≠ v) (ha : a ∈ openSegment ℝ u v) :
    segment ℝ u a ∩ segment ℝ a v = {a} := by
  rw [openSegment_eq_image_lineMap] at ha
  obtain ⟨t, ⟨_, _⟩, rfl⟩ := ha
  refine subset_antisymm (fun w ⟨hwu, hwv⟩ ↦ ?_) (by simp [right_mem_segment, left_mem_segment])
  rw [segment_eq_image_lineMap] at hwu hwv
  obtain ⟨r, ⟨_, _⟩, rfl⟩ := hwu
  obtain ⟨s, ⟨_, _⟩, heq⟩ := hwv
  rw [lineMap_lineMap_right u v t r, lineMap_lineMap_left u v t s,
    (lineMap_injective ℝ huv).eq_iff] at heq
  obtain rfl : r = 1 := by nlinarith
  simp

/-! ### Compactness -/

/-- A segment is compact as the image of the unit interval. -/
lemma isCompact_segment {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [ContinuousAdd E] [ContinuousSMul ℝ E] (u v : E) : IsCompact (segment ℝ u v) := by
  rw [← Path.range_segment]
  exact isCompact_range (Path.segment u v).continuous

lemma Path.segment_isEmbedding {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [ContinuousAdd V] [ContinuousSMul ℝ V] {a b : V} [T2Space ↑(segment ℝ a b)] (hab : a ≠ b) :
    IsEmbedding (Path.segment a b) := by
  let f : unitInterval → segment ℝ a b :=
    fun t ↦ ⟨Path.segment a b t, range_segment a b ▸ mem_range_self t⟩
  have hf : Continuous f := (Path.segment a b).continuous.subtype_mk _
  have hinj : Injective f := fun _ _ h ↦ segment_injective_of_ne hab (congrArg Subtype.val h)
  exact IsEmbedding.subtypeVal.comp (hf.isClosedEmbedding hinj).isEmbedding

/-- A compact connected subset of a Hausdorff segment is a segment, including the
singleton case. Only the segment, not the ambient vector space, must be Hausdorff. -/
lemma IsCompact.exists_eq_segment_of_isConnected_of_subset_segment {V : Type*}
    [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [ContinuousAdd V] [ContinuousSMul ℝ V]
    {C : Set V} {a b : V} [T2Space ↥(segment ℝ a b)] (hc : IsCompact C) (hconn : IsConnected C)
    (hsub : C ⊆ segment ℝ a b) : ∃ x y, C = segment ℝ x y := by
  obtain rfl | hab := eq_or_ne a b
  · use a, a
    rw [segment_same] at hsub ⊢
    exact hconn.nonempty.subset_singleton_iff.mp hsub
  obtain ⟨s, t, hst, rfl⟩ :=
    (segment_isEmbedding hab).exists_eq_image_Icc_of_isConnected_isCompact
    (by rwa [range_segment]) hconn hc
  refine ⟨Path.segment a b s, Path.segment a b t, Eq.symm ?_⟩
  simp only [segment_apply] -- this also probably should be an API about segment and Path.segment
  rw [← image_image, image_subtype_val_Icc,
    ← segment_eq_Icc (show (s : ℝ) ≤ t from hst), image_segment]

/-! ### Approaching a strict halfspace along an open segment -/

section OrderedRing

variable {K V : Type*} [Ring K] [LinearOrder K] [IsStrictOrderedRing K]
  [DenselyOrdered K] [TopologicalSpace K] [OrderTopology K]
  [AddCommGroup V] [Module K V] [TopologicalSpace V]
  [ContinuousConstVAdd V V] [ContinuousSMul K V] {S : Set V}

theorem AffineMap.mem_closure_lt_of_openSegment_subset (f : V →ᵃ[K] K) {p a : V}
    (hseg : openSegment K p a ⊆ S) (hfa : f p < f a) :
    p ∈ closure {q | q ∈ S ∧ f p < f q} := by
  have hline : Continuous (lineMap p a : K → V) := by
    have hsmul : Continuous (fun t : K ↦ t • (a - p)) :=
      continuous_id.smul continuous_const
    have htrans : Continuous (fun x : V ↦ p +ᵥ x) := continuous_const_vadd p
    change Continuous (fun t : K ↦ t • (a - p) + p)
    simpa only [Function.comp_def, lineMap_apply_module', vadd_eq_add, add_comm]
      using htrans.comp hsmul
  have hpcl : p ∈ closure (openSegment K p a) := by
    rw [openSegment_eq_image_lineMap]
    apply image_closure_subset_closure_image hline
    refine ⟨0, ?_, by simp⟩
    rw [closure_Ioo (zero_ne_one' K)]
    exact ⟨le_rfl, zero_le_one⟩
  refine closure_mono ?_ hpcl
  intro q hq
  refine ⟨hseg hq, ?_⟩
  exact (openSegment_subset_Ioo hfa (image_openSegment K f p a ▸ mem_image_of_mem f hq)).1

end OrderedRing

theorem openSegment_subset_openSegment_right_of_mem {K V : Type*}
    [Ring K] [LinearOrder K] [IsStrictOrderedRing K] [AddCommGroup V] [Module K V]
    {a b p : V} (hp : p ∈ openSegment K a b) :
    openSegment K p b ⊆ openSegment K a b := by
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := openSegment_eq_image_lineMap K a b ▸ hp
  intro q hq
  obtain ⟨s, ⟨hs0, hs1⟩, rfl⟩ := openSegment_eq_image_lineMap K _ b ▸ hq
  rw [lineMap_lineMap_left]
  apply lineMap_mem_openSegment
  refine ⟨?_, sub_lt_self _ (mul_pos (sub_pos.mpr hs1) (sub_pos.mpr ht1))⟩
  refine sub_pos.mpr <| (mul_lt_mul_of_pos_left (sub_lt_self _ ht0) (sub_pos.mpr hs1)).trans ?_
  rw [mul_one]
  exact sub_lt_self 1 hs0

/-! ### Intersections of segments

The parameters of `[a, b]` that land on `[c, d]` form a compact convex subset of `[0, 1]`, i.e. a
closed subinterval. Both results below read off a consequence of that. -/

section Real

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {a b c d : E}

/-- The parameters of `[a, b]` landing on `[c, d]` form a compact set.

No topology on `E` is needed: the argument takes place in the parameter space `ℝ × ℝ`. -/
lemma isCompact_setOf_lineMap_mem_segment (a b c d : E) :
    IsCompact {t : ℝ | t ∈ Icc 0 1 ∧ AffineMap.lineMap a b t ∈ segment ℝ c d} := by
  -- `Φ (t, s) = lineMap a b t - lineMap c d s`, so the pairs of parameters describing the same
  -- point are the zeros of the affine map `Φ`.
  set Φ : ℝ × ℝ →ᵃ[ℝ] E :=
    (AffineMap.lineMap a b).comp AffineMap.fst - (AffineMap.lineMap c d).comp AffineMap.snd with hΦ
  have hΦ_iff (z : ℝ × ℝ) :
      z ∈ Φ ⁻¹' {0} ↔ AffineMap.lineMap a b z.1 = AffineMap.lineMap c d z.2 := by
    simp [hΦ, sub_eq_zero]
  -- The zero set is an affine subspace of `ℝ × ℝ`, hence closed.
  have hA : IsCompact ((Icc 0 1 ×ˢ Icc 0 1 : Set (ℝ × ℝ)) ∩ Φ ⁻¹' {0}) := by
    refine (isCompact_Icc.prod isCompact_Icc).inter_right (?_)
    obtain h | ⟨z₀, hz₀⟩ := eq_empty_or_nonempty (Φ ⁻¹' {0})
    · exact h ▸ isClosed_empty
    have hlin (z : ℝ × ℝ) : Φ.linear (z - z₀) = Φ z := by
      rw [show z - z₀ = z -ᵥ z₀ from rfl, Φ.linear_apply_vsub, hz₀, vsub_eq_sub, sub_zero]
    refine (show Φ ⁻¹' {0} = (· - z₀) ⁻¹' (LinearMap.ker Φ.linear : Set (ℝ × ℝ)) from ?_) ▸
      Φ.linear.ker.closed_of_finiteDimensional.preimage (continuous_sub_right z₀)
    ext z
    simp [← hlin z]
  refine (show {t : ℝ | t ∈ Icc 0 1 ∧ AffineMap.lineMap a b t ∈ segment ℝ c d} =
      Prod.fst '' ((Icc 0 1 ×ˢ Icc 0 1 : Set (ℝ × ℝ)) ∩ Φ ⁻¹' {0}) from ?_) ▸ hA.image
        continuous_fst
  ext t
  simp only [mem_ofPred_eq, segment_eq_image_lineMap, mem_image, mem_inter_iff, mem_prod,
    Prod.exists, exists_and_right]
  exact ⟨fun ⟨ht, s, hs, hts⟩ ↦ ⟨t, ⟨s, ⟨⟨ht, hs⟩, (hΦ_iff (t, s)).mpr hts.symm⟩⟩, rfl⟩,
    fun ⟨t, ⟨s, ⟨⟨ht, hs⟩, hts⟩⟩, heq⟩ ↦ ⟨heq ▸ ht, s, hs, heq ▸ ((hΦ_iff (t, s)).mp hts).symm⟩⟩

/-- The parameters of `[a, b]` landing on `[c, d]` form a convex set. -/
lemma convex_setOf_lineMap_mem_segment (a b c d : E) :
    Convex ℝ {t : ℝ | t ∈ Icc 0 1 ∧ AffineMap.lineMap a b t ∈ segment ℝ c d} :=
  (convex_Icc 0 1).inter ((convex_segment c d).affine_preimage (AffineMap.lineMap a b))

/-- The parameters of `[a, b]` landing on `[c, d]` form a closed interval, as soon as there is
one. -/
lemma exists_eq_Icc_setOf_lineMap_mem_segment
    (h : {t : ℝ | t ∈ Icc 0 1 ∧ AffineMap.lineMap a b t ∈ segment ℝ c d}.Nonempty) :
    ∃ u v : ℝ, u ≤ v ∧
      {t : ℝ | t ∈ Icc 0 1 ∧ AffineMap.lineMap a b t ∈ segment ℝ c d} = Icc u v := by
  set T := {t : ℝ | t ∈ Icc 0 1 ∧ AffineMap.lineMap a b t ∈ segment ℝ c d}
  have hIcc : T = Icc (sInf T) (sSup T) :=
    eq_Icc_of_connected_compact ((convex_setOf_lineMap_mem_segment a b c d).isConnected h)
      (isCompact_setOf_lineMap_mem_segment a b c d)
  exact ⟨sInf T, sSup T, by rw [← nonempty_Icc, ← hIcc]; exact h, hIcc⟩

/-- The points of `[a, b]` lying on `[c, d]`, as an image of the parameter set. -/
lemma segment_inter_eq_image_setOf_lineMap_mem_segment (a b c d : E) :
    segment ℝ a b ∩ segment ℝ c d =
      AffineMap.lineMap a b '' {t : ℝ | t ∈ Icc 0 1 ∧ AffineMap.lineMap a b t ∈ segment ℝ c d} := by
  rw [show {t : ℝ | t ∈ Icc 0 1 ∧ AffineMap.lineMap a b t ∈ segment ℝ c d} =
      Icc 0 1 ∩ AffineMap.lineMap a b ⁻¹' segment ℝ c d from rfl,
    image_inter_preimage, ← segment_eq_image_lineMap]

/-- A nonempty intersection of two segments is a segment. -/
lemma segment_inter_segment_eq_segment_of_nonempty
    (hne : (segment ℝ a b ∩ segment ℝ c d).Nonempty) :
    ∃ p q, segment ℝ a b ∩ segment ℝ c d = segment ℝ p q := by
  rw [segment_inter_eq_image_setOf_lineMap_mem_segment] at hne ⊢
  obtain ⟨u, v, huv, hT⟩ := exists_eq_Icc_setOf_lineMap_mem_segment (image_nonempty.mp hne)
  exact ⟨_, _, by rw [hT, ← segment_eq_Icc huv, image_segment]⟩

/-- The intersection of `[a, b]` with a segment has a *last* point along `[a, b]`: a point `q` of
the intersection beyond which `[a, b]` never meets the other segment again. -/
lemma exists_last_mem_segment_inter_segment (h : (segment ℝ a b ∩ segment ℝ c d).Nonempty) :
    ∃ q ∈ segment ℝ a b ∩ segment ℝ c d, Disjoint (openSegment ℝ q b \ {b}) (segment ℝ c d) := by
  set T := {t : ℝ | t ∈ Icc 0 1 ∧ lineMap a b t ∈ segment ℝ c d}
  have hTne : T.Nonempty := by
    obtain ⟨w, hwab, hwcd⟩ := h
    obtain ⟨t, ht, rfl⟩ := segment_eq_image_lineMap ℝ a b ▸ hwab
    exact ⟨t, ht, hwcd⟩
  obtain ⟨m, ⟨⟨hm0, hm1⟩, hmcd⟩, hm⟩ :=
    (isCompact_setOf_lineMap_mem_segment a b c d).exists_isMaxOn hTne continuousOn_id
  refine ⟨lineMap a b m, ⟨lineMap_mem_segment ℝ a b ⟨hm0, hm1⟩, hmcd⟩,
    disjoint_left.mpr fun w ⟨hwopen, hwb⟩ hwcd ↦ ?_⟩
  obtain rfl | _ := hm1.eq_or_lt
  · simp only [lineMap_apply_one, openSegment_same, hwb] at hwopen
  obtain ⟨r, ⟨_, _⟩, rfl⟩ := openSegment_eq_image_lineMap ℝ _ b ▸ hwopen
  have : 1 - (1 - r) * (1 - m) ≤ m := hm ⟨⟨?_, ?_⟩, lineMap_lineMap_left a b m r ▸ hwcd⟩
  all_goals nlinarith

end Real

/-! ### Endpoints of an open segment -/

section OpenSegment

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {p a b : E}

/-- An interior point of a segment differs from its left endpoint. -/
@[grind →]
lemma ne_of_mem_openSegment_left (hab : a ≠ b) (hp : p ∈ openSegment ℝ a b) : a ≠ p := by
  obtain ⟨t, ⟨ht0, _⟩, rfl⟩ := (openSegment_eq_image_lineMap (𝕜 := ℝ) a b).symm ▸ hp
  intro h
  obtain h' | ht := (AffineMap.lineMap_eq_left_iff (k := ℝ)).mp h.symm
  · exact hab h'
  exact ht0.ne' ht

/-- An interior point of a segment differs from its right endpoint. -/
@[grind →]
lemma ne_of_mem_openSegment_right (hab : a ≠ b) (hp : p ∈ openSegment ℝ a b) : b ≠ p := by
  obtain ⟨t, ⟨_, ht1⟩, rfl⟩ := (openSegment_eq_image_lineMap (𝕜 := ℝ) a b).symm ▸ hp
  intro h
  obtain h' | ht := (AffineMap.lineMap_eq_right_iff (k := ℝ)).mp h.symm
  · exact hab h'
  exact ht1.ne ht

/-- Removing the endpoints of a nondegenerate segment leaves its open segment. -/
lemma segment_sdiff_pair (hab : a ≠ b) : segment ℝ a b \ {a, b} = openSegment ℝ a b := by
  ext x
  refine ⟨fun ⟨hx, hn⟩ ↦ mem_openSegment_of_ne_left_right (fun h ↦ hn (Or.inl h.symm))
    (fun h ↦ hn (Or.inr h.symm)) hx, fun hx ↦ ⟨openSegment_subset_segment ℝ a b hx, ?_⟩⟩
  rintro (rfl | rfl)
  · exact ne_of_mem_openSegment_left hab hx rfl
  exact ne_of_mem_openSegment_right hab hx rfl

/-- A segment carrying an interior point other than its left endpoint is nondegenerate.
The converse direction to `ne_of_mem_openSegment_left`, which needs `a ≠ b` to start with. -/
lemma ne_of_mem_openSegment_of_ne (hap : a ≠ p) (hp : p ∈ openSegment ℝ a b) : a ≠ b := by
  rintro rfl
  rw [openSegment_same] at hp
  exact hap (mem_singleton_iff.mp hp).symm

/-- Splitting `[a, b]` at an interior point `p`, at the level of the intersection condition that
says a segment meets a set only in permitted points.

`T` is the extra set of permitted points, beside the far endpoint. It is `∅` when the condition is
`PolygonalPath.isSimple_cons_iff` and `{a}` when it is `PolygonalPath.isSimpleLoop_cons_iff`, which
differ in exactly that way; `hT` is what both instances satisfy. This is the geometric core shared
by `PolygonalPath.isSimple_subdivide_iff` and `PolygonalPath.isSimpleLoop_subdivide_iff`. -/
lemma segment_split_inter_subset_iff {S T : Set E} (hap : a ≠ p) (hp : p ∈ openSegment ℝ a b)
    (hT : T ⊆ {a}) : (segment ℝ a p ∩ (segment ℝ p b ∪ S) ⊆ insert p T ∧ segment ℝ p b ∩ S ⊆ {b}) ↔
      segment ℝ a b ∩ S ⊆ insert b T := by
  have hab : a ≠ b := ne_of_mem_openSegment_of_ne hap hp
  have hpb : p ≠ b := (ne_of_mem_openSegment_right hab hp).symm
  have hinter : segment ℝ a p ∩ segment ℝ p b = {p} := segment_inter_subsegments_eq_singleton hab hp
  have hsplit : segment ℝ a p ∪ segment ℝ p b = segment ℝ a b :=
    segment_union_eq_segment (openSegment_subset_segment ℝ a b hp)
  constructor
  · rintro ⟨hleft, hright⟩ w ⟨hwab, hwS⟩
    obtain hwap | hwpb := hsplit ▸ hwab
    · obtain rfl | hwT := hleft ⟨hwap, Or.inr hwS⟩
      · exact Or.inl (hright ⟨left_mem_segment ℝ w b, hwS⟩)
      · exact Or.inr hwT
    · exact Or.inl (hright ⟨hwpb, hwS⟩)
  refine fun hwhole ↦ ⟨fun w ⟨hwap, hw⟩ ↦ ?_, fun w ⟨hwpb, hwS⟩ ↦ ?_⟩
  · obtain hwpb | hwS := hw
    · exact Or.inl (hinter.subset ⟨hwap, hwpb⟩)
    obtain rfl | hwT := hwhole ⟨hsplit ▸ subset_union_left hwap, hwS⟩
    · exact absurd (hinter.subset ⟨hwap, right_mem_segment ℝ p w⟩) hpb.symm
    · exact Or.inr hwT
  obtain rfl | hwT := hwhole ⟨hsplit ▸ subset_union_right hwpb, hwS⟩
  · rfl
  obtain rfl := hT hwT
  exact absurd (hinter.subset ⟨left_mem_segment ℝ w p, hwpb⟩) hap

end OpenSegment
