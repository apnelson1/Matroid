module

public import Matroid.ForMathlib.Geometry.SegmentFigure

/-!
# Local structure of a simple polygonal arc

At a point of a simple polygonal path other than its endpoints, the path has exactly two local
germs. This is a fact about simple polygonal arcs in a real normed space, independent of dimension.

The theorem allows the radius to be bounded by any prescribed positive scale, so the local star can
be combined with other radius bounds.
-/

@[expose] public section

open Set Metric

namespace PolygonalPath

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {x y q : V} {P : PolygonalPath x y}

/-- A nonendpoint point of a simple polygonal path has, at every sufficiently small requested
scale, a neighborhood consisting of exactly two radial segments, expressed by the star equation. -/
theorem IsSimple.exists_local_star_two (hP : P.IsSimple) (hqP : q ∈ P.toSet) (hqx : q ≠ x)
    (hqy : q ≠ y) {ε : ℝ} (hε : 0 < ε) : ∃ ρ, 0 < ρ ∧ ρ ≤ ε ∧ ∃ Y : Finset V, Y.card = 2 ∧
    (Y : Set V) ⊆ sphere q ρ ∧ closedBall q ρ ∩ P.toSet = {q} ∪ ⋃ z ∈ Y, segment ℝ q z := by
  obtain ⟨hL, hR, hmeet⟩ := hP.breakAt hqP
  set L := (P.breakAt hqP).1
  set R := (P.breakAt hqP).2
  set A := L.reverse
  have hA : A.IsSimple := isSimple_reverse.mpr hL
  have hAlen : 0 < A.length := A.length_pos_of_ne hqx
  have hRlen : 0 < R.length := R.length_pos_of_ne hqy
  obtain ⟨ρA, hρA, hAball⟩ := exists_ball_inter_subset_firstSegment hA hqx
  obtain ⟨ρR, hρR, hRball⟩ := exists_ball_inter_subset_firstSegment hR hqy
  obtain ⟨ρ0, hρ0, Y0, hY0, hstar0⟩ := P.isSegmentFigure_toSet.exists_radius hqP
  let ρ := min ε (min ρ0 (min ρA ρR))
  have hρ : 0 < ρ := lt_min hε (lt_min hρ0 (lt_min hρA hρR))
  have hρ_le_ε : ρ ≤ ε := min_le_left _ _
  have hρ_le_ρ0 : ρ ≤ ρ0 := (min_le_right ε _).trans (min_le_left _ _)
  have hρ_le_ρA : ρ ≤ ρA :=
    (min_le_right ε _).trans ((min_le_right ρ0 _).trans (min_le_left _ _))
  have hρ_le_ρR : ρ ≤ ρR :=
    (min_le_right ε _).trans ((min_le_right ρ0 _).trans (min_le_right _ _))
  obtain ⟨Y, hY, -, hstar⟩ := exists_radius_of_le hρ0 hY0 hstar0 hρ hρ_le_ρ0
  let U : Bool → Set V := fun b => if b then R.toSet else A.toSet
  let z : Bool → V := fun b => if b then R.firstTip else A.firstTip
  have hunion : L.toSet ∪ R.toSet = P.toSet := breakAt_toSet_union (P := P) (ha := hqP)
  have hAto : A.toSet = L.toSet := toSet_reverse L
  have hUT : ∀ b, U b ⊆ P.toSet := by
    intro b
    cases b
    · exact hAto.trans_subset (hunion ▸ subset_union_left)
    · exact hunion ▸ subset_union_right
  have hUp : ∀ b, ∃ w ≠ q, segment ℝ q w ⊆ U b := by
    intro b
    cases b
    · exact ⟨A.firstTip, hA.firstTip_ne hAlen, segment_firstTip_subset_toSet A hAlen⟩
    · exact ⟨R.firstTip, hR.firstTip_ne hRlen, segment_firstTip_subset_toSet R hRlen⟩
  have hUmeet : ∀ b₁ b₂, b₁ ≠ b₂ → U b₁ ∩ U b₂ ⊆ {q} := by
    intro b₁ b₂ hne
    cases b₁ <;> cases b₂
    · exact (hne rfl).elim
    · rw [show U false ∩ U true = A.toSet ∩ R.toSet from rfl, hAto]
      exact hmeet.subset
    · rw [show U true ∩ U false = R.toSet ∩ A.toSet from rfl, hAto, inter_comm]
      exact hmeet.subset
    · exact (hne rfl).elim
  have hge : Fintype.card Bool ≤ Y.card :=
    le_card_radii_of_pairwise (T := P.toSet) hρ hY hstar hUT hUp hUmeet
  have hcover : P.toSet ∩ closedBall q ρ ⊆ {q} ∪ ⋃ b, U b := by
    intro u ⟨huP, _⟩
    refine Or.inr ?_
    have huLR : u ∈ L.toSet ∪ R.toSet := hunion ▸ huP
    rw [← hAto] at huLR
    obtain huA | huR := huLR
    · exact mem_iUnion.mpr ⟨false, huA⟩
    · exact mem_iUnion.mpr ⟨true, huR⟩
  have hzne : ∀ b, z b ≠ q := by
    intro b
    cases b
    · exact hA.firstTip_ne hAlen
    · exact hR.firstTip_ne hRlen
  have hUz : ∀ b, U b ∩ closedBall q ρ ⊆ segment ℝ q (z b) := by
    intro b
    cases b
    · intro u ⟨huU, huball⟩
      exact hAball ⟨huU, closedBall_subset_closedBall hρ_le_ρA huball⟩
    · intro u ⟨huU, huball⟩
      exact hRball ⟨huU, closedBall_subset_closedBall hρ_le_ρR huball⟩
  have hle : Y.card ≤ Fintype.card Bool :=
    card_radii_le_of_cover (T := P.toSet) hρ hY hstar hcover hzne hUz
  refine ⟨ρ, hρ, hρ_le_ε, Y, ?_, hY, hstar⟩
  rw [← Fintype.card_bool]
  exact Nat.le_antisymm hle hge

end PolygonalPath
