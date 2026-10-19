module

public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Separating points and compact sets from closed sets

## Main statements

* `exists_pos_le_dist_of_notMem` : a point off a closed set stays a fixed positive distance from
  all of it.
* `exists_pos_le_dist_of_disjoint` : the same for a compact set and a disjoint closed set.
* `exists_disjoint_closedBall_avoiding` : disjoint small balls around finitely many points,
  avoiding every member of a finite closed family that does not contain the center.

The bounds are pointwise inequalities, so empty sets are handled vacuously. The proofs use
`infDist` for a point off a closed set and attain a positive minimum on a compact set.
-/

@[expose] public section

open Metric Set

/-- A point off a closed set stays a fixed positive distance from all of it. -/
@[grind →]
lemma exists_pos_le_dist_of_notMem {X : Type*} [PseudoMetricSpace X] {K : Set X} (hK : IsClosed K)
    {p : X} (hp : p ∉ K) : ∃ δ > 0, ∀ x ∈ K, δ ≤ dist p x := by
  obtain rfl | hne := K.eq_empty_or_nonempty
  · exact ⟨1, one_pos, by simp⟩
  exact ⟨infDist p K, (hK.notMem_iff_infDist_pos hne).mp hp, fun _ hx ↦ infDist_le_dist_of_mem hx⟩

/-- A compact set stays a fixed positive distance from a disjoint closed set.

Compactness is needed on one side only, and only to attain the minimum of `infDist · t`; the other
side may be any closed set. As above, both degenerate cases are absorbed by the pointwise form. -/
@[grind →]
lemma exists_pos_le_dist_of_disjoint {X : Type*} [PseudoMetricSpace X] {s t : Set X}
    (hs : IsCompact s) (ht : IsClosed t) (hst : Disjoint s t) :
    ∃ δ > 0, ∀ x ∈ s, ∀ y ∈ t, δ ≤ dist x y := by
  obtain rfl | hsne := s.eq_empty_or_nonempty
  · exact ⟨1, one_pos, by simp⟩
  obtain rfl | htne := t.eq_empty_or_nonempty
  · exact ⟨1, one_pos, by simp⟩
  obtain ⟨x, hx, hmin⟩ := hs.exists_isMinOn hsne (continuous_infDist_pt (s := t)).continuousOn
  exact ⟨infDist x t, (ht.notMem_iff_infDist_pos htne).mp (hst.notMem_of_mem_left hx),
    fun _ hy _ hz ↦ (hmin hy).trans (infDist_le_dist_of_mem hz)⟩

/-- Around finitely many points, choose disjoint closed balls below prescribed positive radii,
each avoiding every member of a finite closed family that does not contain its center. -/
theorem exists_disjoint_closedBall_avoiding
    {W ι : Type*} [MetricSpace W] [Finite ι] {Z : Set W} [Finite Z]
    (L : ι → Set W) (hL : ∀ i, IsClosed (L i))
    (ε : Z → ℝ) (hε : ∀ x, 0 < ε x) :
    ∃ r : Z → ℝ, (∀ x, 0 < r x) ∧ (∀ x, r x < ε x) ∧
      (Pairwise fun x y ↦ Disjoint (closedBall x.1 (r x)) (closedBall y.1 (r y))) ∧
      ∀ i x, x.1 ∉ L i → Disjoint (L i) (closedBall x.1 (r x)) := by
  classical
  let K (x : Z) : Set W := (Z \ {x.1}) ∪
    ⋃ i ∈ {i | x.1 ∉ L i}, L i
  have hKclosed (x) : IsClosed (K x) :=
    (toFinite Z).sdiff.isClosed.union
      ((toFinite _).isClosed_biUnion fun i _ ↦ hL i)
  have hxK (x : Z) : x.1 ∉ K x := by
    rintro (⟨_, hx⟩ | hx)
    · exact hx (mem_singleton _)
    · obtain ⟨i, hi, hxL⟩ := mem_iUnion₂.mp hx
      exact hi hxL
  choose δ hδ hsep using fun x ↦ exists_pos_le_dist_of_notMem (hKclosed x) (hxK x)
  let r (x : Z) := min (δ x / 3) (ε x / 2)
  have hrpos (x) : 0 < r x := lt_min (div_pos (hδ x) (by norm_num)) (half_pos (hε x))
  have hrsmall (x) : r x < ε x := (min_le_right _ _).trans_lt (half_lt_self (hε x))
  have hrδ (x) : r x ≤ δ x / 3 := min_le_left _ _
  have hrsep (x y : Z) (hxy : x ≠ y) : r x ≤ dist x.1 y.1 / 3 := by
    apply (hrδ x).trans
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact hsep x y.1 (Or.inl ⟨y.2, fun hy ↦ hxy (Subtype.ext (mem_singleton_iff.mp hy).symm)⟩)
  refine ⟨r, hrpos, hrsmall, fun x y hxy ↦ closedBall_disjoint_closedBall ?_, ?_⟩
  · have hd : 0 < dist x.1 y.1 := dist_pos.mpr (fun h ↦ hxy (Subtype.ext h))
    have h1 := hrsep x y hxy
    have h2 := hrsep y x hxy.symm
    rw [dist_comm y.1 x.1] at h2
    linarith
  · intro i x hxL
    refine disjoint_left.mpr fun w hwL hwB ↦ ?_
    have hd : δ x ≤ dist x.1 w :=
      hsep x w (Or.inr (mem_iUnion₂.mpr ⟨i, hxL, hwL⟩))
    have hB := mem_closedBall.mp hwB
    rw [dist_comm w x.1] at hB
    have hr := hrδ x
    have hp := hδ x
    linarith

end
