module

public import Mathlib.Analysis.Convex.Between
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Unions and intersections of segments

This file collects the facts about `segment` that are needed for polygonal curves, and that belong
in `Mathlib.Analysis.Convex.Segment`.

## Main statements

* `segment_union_eq_segment`, `affineSegment_union_eq_affineSegment` : splitting a segment at one
  of its points, in a module and in an affine space respectively.
* `segment_subset_segment_right` : shortening a segment at its right endpoint.
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

`isCompact_setOf_lineMap_mem_segment` is the only place where that argument is made; all the
statements below are corollaries of it together with the — purely algebraic — convexity of the same
set.
-/

@[expose] public section

open Set Function

/-! ### Splitting a segment -/

/-- Shortening a segment at its right endpoint. The containment half of
`segment_union_eq_segment`, but with far weaker hypotheses — no order on `𝕜` beyond
`IsOrderedRing`, since it is only convexity of the target. -/
lemma segment_subset_segment_right {𝕜 E : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]
    [AddCommMonoid E] [Module 𝕜 E] {x y z : E} (hz : z ∈ segment 𝕜 x y) :
    segment 𝕜 x z ⊆ segment 𝕜 x y :=
  (convex_segment x y).segment_subset (left_mem_segment 𝕜 x y) hz

/-- Splitting a segment at one of its points. -/
lemma segment_union_eq_segment {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommGroup E] [Module 𝕜 E] {x y z : E} (hz : z ∈ segment 𝕜 x y) :
    segment 𝕜 x z ∪ segment 𝕜 z y = segment 𝕜 x y := by
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  have h₁ : AffineMap.lineMap x y '' segment 𝕜 0 t = segment 𝕜 x (AffineMap.lineMap x y t) := by
    simp [image_segment]
  have h₂ : AffineMap.lineMap x y '' segment 𝕜 t 1 = segment 𝕜 (AffineMap.lineMap x y t) y := by
    simp [image_segment]
  rw [← h₁, ← h₂, ← image_union, segment_eq_Icc ht.1, segment_eq_Icc ht.2,
    Icc_union_Icc_eq_Icc ht.1 ht.2, ← segment_eq_image_lineMap]

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
  obtain ⟨t, ht, rfl⟩ := ha
  apply Set.Subset.antisymm
  · rintro w ⟨hw₁, hw₂⟩
    rw [segment_eq_image_lineMap] at hw₁ hw₂
    obtain ⟨r, hr, rfl⟩ := hw₁
    obtain ⟨s, hs, heq⟩ := hw₂
    have hleft : AffineMap.lineMap u (AffineMap.lineMap u v t) r =
        AffineMap.lineMap u v (r * t) := by
      simp only [AffineMap.lineMap_apply_module]
      module
    have hright : AffineMap.lineMap (AffineMap.lineMap u v t) v s =
        AffineMap.lineMap u v (t + s * (1 - t)) := by
      simp only [AffineMap.lineMap_apply_module]
      module
    rw [hleft, hright] at heq
    have hparam : r * t = t + s * (1 - t) :=
      (AffineMap.lineMap_injective ℝ huv) heq.symm
    have hr_eq : r = 1 := by nlinarith [hr.1, hr.2, hs.1, hs.2, ht.1, ht.2]
    subst r
    simp
  · simp [right_mem_segment, left_mem_segment]

/-! ### Compactness -/

/-- A segment is compact: it is the image of `[0, 1]` under `lineMap`. Mathlib has no such lemma,
and every caller that has wanted one so far has reproved it locally. -/
lemma isCompact_segment {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] (u v : E) : IsCompact (segment ℝ u v) := by
  rw [segment_eq_image_lineMap]
  exact isCompact_Icc.image AffineMap.lineMap_continuous

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
  have hclosed : IsClosed (Φ ⁻¹' {0}) := by
    rcases eq_empty_or_nonempty (Φ ⁻¹' {0}) with h | ⟨z₀, hz₀⟩
    · exact h ▸ isClosed_empty
    have hlin (z : ℝ × ℝ) : Φ.linear (z - z₀) = Φ z := by
      rw [show z - z₀ = z -ᵥ z₀ from rfl, Φ.linearMap_vsub, hz₀, vsub_eq_sub, sub_zero]
    have heq : Φ ⁻¹' {0} = (· - z₀) ⁻¹' (LinearMap.ker Φ.linear : Set (ℝ × ℝ)) := by
      ext z
      simp [← hlin z]
    exact heq ▸ Φ.linear.ker.closed_of_finiteDimensional.preimage (continuous_sub_right z₀)
  have hA : IsCompact ((Icc 0 1 ×ˢ Icc 0 1 : Set (ℝ × ℝ)) ∩ Φ ⁻¹' {0}) :=
    (isCompact_Icc.prod isCompact_Icc).inter_right hclosed
  have himage : {t : ℝ | t ∈ Icc 0 1 ∧ AffineMap.lineMap a b t ∈ segment ℝ c d} =
      Prod.fst '' ((Icc 0 1 ×ˢ Icc 0 1 : Set (ℝ × ℝ)) ∩ Φ ⁻¹' {0}) := by
    ext t
    simp only [mem_ofPred_eq, segment_eq_image_lineMap, mem_image, mem_inter_iff, mem_prod,
      Prod.exists, exists_and_right]
    exact ⟨fun ⟨ht, s, hs, hts⟩ ↦ ⟨t, ⟨s, ⟨⟨ht, hs⟩, (hΦ_iff (t, s)).mpr hts.symm⟩⟩, rfl⟩,
      fun ⟨t, ⟨s, ⟨⟨ht, hs⟩, hts⟩⟩, heq⟩ ↦ ⟨heq ▸ ht, s, hs, heq ▸ ((hΦ_iff (t, s)).mp hts).symm⟩⟩
  exact himage ▸ hA.image continuous_fst

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
    ∃ q ∈ segment ℝ a b ∩ segment ℝ c d,
      Disjoint (openSegment ℝ q b \ {b}) (segment ℝ c d) := by
  set T := {t : ℝ | t ∈ Icc 0 1 ∧ AffineMap.lineMap a b t ∈ segment ℝ c d}
  have hTne : T.Nonempty := by
    obtain ⟨w, hwab, hwcd⟩ := h
    obtain ⟨t, ht, rfl⟩ := segment_eq_image_lineMap ℝ a b ▸hwab
    exact ⟨t, ht, hwcd⟩
  obtain ⟨m, hmT, hm⟩ :=
    (isCompact_setOf_lineMap_mem_segment a b c d).exists_isMaxOn hTne continuousOn_id
  refine ⟨AffineMap.lineMap a b m, ⟨lineMap_mem_segment ℝ a b hmT.1, hmT.2⟩,
    disjoint_left.mpr fun w ⟨hwopen, hwb⟩ hwcd ↦ ?_⟩
  by_cases hm1 : m = 1
  · rw [hm1] at hwopen
    simp only [AffineMap.lineMap_apply_one, openSegment_same, mem_singleton_iff] at hwopen
    exact hwb hwopen
  obtain ⟨r, hr, rfl⟩ := openSegment_eq_image_lineMap ℝ _ b ▸ hwopen
  have hnested : AffineMap.lineMap (AffineMap.lineMap a b m) b r =
      AffineMap.lineMap a b (m + r * (1 - m)) := by
    simp only [AffineMap.lineMap_apply_module]
    module
  have hmlt : m < 1 := lt_of_le_of_ne hmT.1.2 hm1
  have htT : m + r * (1 - m) ∈ T :=
    ⟨⟨by nlinarith [hmT.1.1, hr.1, hr.2], by nlinarith [hr.2]⟩, by rw [← hnested]; exact hwcd⟩
  have hle : m + r * (1 - m) ≤ m := hm htT
  nlinarith [hr.1]

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

end OpenSegment
