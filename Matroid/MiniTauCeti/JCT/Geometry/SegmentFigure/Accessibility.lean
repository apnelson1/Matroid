module

public import Matroid.MiniTauCeti.JCT.Geometry.SegmentFigure.Star
public import Matroid.MiniTauCeti.JCT.Topology.OnePoint

/-! # Straight access to complementary components of segment figures -/

@[expose] public section

open Function Set Topology Metric

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {S : Set V} {p : V}

/-- Inside a star ball, the segment from the centre to a point off the figure meets the figure
only at the centre. -/
theorem segment_sdiff_subset_compl_of_star {ρ : ℝ} {Y : Finset V} (hρ : 0 < ρ)
    (hY : ↑Y ⊆ sphere p ρ) (hstar : closedBall p ρ ∩ S = {p} ∪ ⋃ y ∈ Y, segment ℝ p y)
    {z : V} (hzball : z ∈ ball p ρ) (hzS : z ∉ S) :
    segment ℝ p z \ {p} ⊆ Sᶜ := by
  intro w ⟨hwseg, hwp⟩ hwS
  have hwball : w ∈ closedBall p ρ :=
    ball_subset_closedBall <| (convex_ball p ρ).segment_subset (mem_ball_self hρ) hzball hwseg
  have hwstar : w ∈ ({p} ∪ ⋃ y ∈ Y, segment ℝ p y : Set V) := by
    rw [← hstar]; exact ⟨hwball, hwS⟩
  rcases hwstar with rfl | hwY
  · exact hwp rfl
  · obtain ⟨y, hyY, hwy⟩ := mem_iUnion₂.mp hwY
    obtain ⟨t, ⟨ht0, _⟩, rfl⟩ := (segment_eq_image_lineMap (𝕜 := ℝ) p y).symm ▸ hwy
    obtain ⟨s, ⟨hs0, _⟩, hseq⟩ := (segment_eq_image_lineMap (𝕜 := ℝ) p z).symm ▸ hwseg
    have htpos : 0 < t :=
      lt_of_le_of_ne ht0 fun ht ↦ hwp (by simp [AffineMap.lineMap_apply, ht])
    have hspos : 0 < s :=
      lt_of_le_of_ne hs0 fun hs ↦ hwp <|
        hseq.symm.trans (by simp [AffineMap.lineMap_apply, hs])
    have hvec : t • (y - p) = s • (z - p) := by
      have h1 := congrArg (fun u : V ↦ u - p) hseq
      -- hseq : lineMap p z s = lineMap p y t, so s • (z-p) = t • (y-p)
      simp only [AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub, add_sub_cancel_right] at h1
      exact h1.symm
    have hcoef_vec : z - p = (t / s) • (y - p) := by
      calc
        z - p = s⁻¹ • (s • (z - p)) := (inv_smul_smul₀ hspos.ne' _).symm
        _ = s⁻¹ • (t • (y - p)) := by rw [hvec]
        _ = (s⁻¹ * t) • (y - p) := by rw [smul_smul]
        _ = (t / s) • (y - p) := by rw [div_eq_mul_inv, mul_comm]
    have hz_eq : z = AffineMap.lineMap p y (t / s) := by
      rw [AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub, ← hcoef_vec]
      abel
    have hty : dist p y = ρ := by
      simpa [PseudoMetricSpace.dist_comm] using mem_sphere.mp (hY hyY)
    have hdist : dist p z = (t / s) * dist p y := by
      rw [hz_eq, ← PseudoMetricSpace.dist_comm,
        dist_lineMap_left_of_nonneg p y (div_nonneg htpos.le hspos.le),
        PseudoMetricSpace.dist_comm]
    have hzt : dist p z < ρ := by
      simpa [PseudoMetricSpace.dist_comm] using mem_ball.mp hzball
    have hcoef : t / s ≤ 1 := by
      have hypos : 0 < dist p y := by rw [hty]; exact hρ
      have hlt : (t / s) * dist p y < dist p y := by
        calc
          (t / s) * dist p y = dist p z := hdist.symm
          _ < ρ := hzt
          _ = dist p y := hty.symm
      exact (mul_lt_iff_lt_one_left hypos).mp hlt |>.le
    have hzseg : z ∈ segment ℝ p y := by
      rw [hz_eq, segment_eq_image_lineMap]
      exact ⟨t / s, ⟨div_nonneg htpos.le hspos.le, hcoef⟩, rfl⟩
    have : z ∈ closedBall p ρ ∩ S := by
      rw [hstar]; exact Or.inr (mem_iUnion₂.mpr ⟨y, hyY, hzseg⟩)
    exact hzS this.2

/-- A segment with its left endpoint removed is connected when the endpoints differ. -/
theorem isConnected_segment_sdiff_left {z : V} (hzne : z ≠ p) :
    IsConnected (segment ℝ p z \ {p}) := by
  have hseg_eq : segment ℝ p z \ {p} = AffineMap.lineMap p z '' Ioc (0 : ℝ) 1 := by
    ext w
    simp only [mem_sdiff, mem_singleton_iff, mem_image, mem_Ioc, segment_eq_image_lineMap]
    constructor
    · rintro ⟨⟨t, ⟨ht0, ht1⟩, rfl⟩, hwp⟩
      refine ⟨t, ⟨lt_of_le_of_ne ht0 ?_, ht1⟩, rfl⟩
      exact fun ht ↦ hwp (by simp [AffineMap.lineMap_apply, ht])
    · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
      refine ⟨⟨t, ⟨ht0.le, ht1⟩, rfl⟩, ?_⟩
      intro h
      have hsmul : t • (z - p) = 0 := by
        have := congrArg (fun u : V ↦ u - p) h
        simpa [AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub] using this
      exact hzne (sub_eq_zero.mp ((smul_eq_zero.mp hsmul).resolve_left ht0.ne'))
  rw [hseg_eq]
  exact (isConnected_Ioc (show (0 : ℝ) < 1 by norm_num)).image _
    AffineMap.lineMap_continuous.continuousOn

/-- A point on the frontier of a complementary component of a segment figure can enter that
component along a straight segment. -/
theorem IsSegmentFigure.exists_segment_sdiff_subset_connectedComponentIn_compl
    (hS : IsSegmentFigure S) (hp : p ∈ S) {q : V}
    (hpF : p ∈ frontier (connectedComponentIn Sᶜ q)) :
    ∃ y : V, y ≠ p ∧ segment ℝ p y \ {p} ⊆ connectedComponentIn Sᶜ q := by
  obtain ⟨ρ, hρ, Y, hY, hstar⟩ := hS.exists_radius hp
  obtain ⟨z, hzball, hzK⟩ :=
    mem_closure_iff.mp (frontier_subset_closure hpF) (ball p ρ) isOpen_ball (mem_ball_self hρ)
  have hzS : z ∉ S := connectedComponentIn_subset _ _ hzK
  have hzne : z ≠ p := fun h ↦ hzS (h ▸ hp)
  refine ⟨z, hzne, ?_⟩
  rw [connectedComponentIn_eq hzK]
  exact (isConnected_segment_sdiff_left hzne).isPreconnected.subset_connectedComponentIn
    ⟨right_mem_segment ℝ p z, hzne⟩ (segment_sdiff_subset_compl_of_star hρ hY hstar hzball hzS)

/-- A point on the boundary of a complementary component of a segment figure can enter that
component along a straight segment. The component is taken in the one-point compactification. -/
theorem IsSegmentFigure.exists_segment_sdiff_subset_connectedComponentIn
    (hS : IsSegmentFigure S) (hp : p ∈ S) {q : OnePoint V}
    (hpF : (p : OnePoint V) ∈ frontier (connectedComponentIn ((↑) '' S)ᶜ q)) :
    ∃ y : V, y ≠ p ∧ (↑) '' (segment ℝ p y \ {p}) ⊆
      connectedComponentIn ((↑) '' S)ᶜ q := by
  obtain ⟨ρ, hρ, Y, hY, hstar⟩ := hS.exists_radius hp
  have hnhds : (↑) '' (ball p ρ) ∈ 𝓝 (p : OnePoint V) := by
    rw [OnePoint.nhds_coe_eq]
    exact Filter.image_mem_map (ball_mem_nhds _ hρ)
  obtain ⟨z', ⟨hzU, hzF⟩⟩ :=
    mem_closure_iff_nhds.mp (frontier_subset_closure hpF) ((↑) '' ball p ρ) hnhds
  obtain ⟨z, hzball, rfl⟩ := hzU
  have hzS : z ∉ S := fun hz ↦ connectedComponentIn_subset _ _ hzF ⟨z, hz, rfl⟩
  have hzne : z ≠ p := fun h ↦ hzS (h ▸ hp)
  have hseg_off := segment_sdiff_subset_compl_of_star hρ hY hstar hzball hzS
  refine ⟨z, hzne, ?_⟩
  have hconn : IsConnected ((↑) '' (segment ℝ p z \ {p}) : Set (OnePoint V)) :=
    (isConnected_segment_sdiff_left hzne).image _ OnePoint.continuous_coe.continuousOn
  have himg : (↑) '' (segment ℝ p z \ {p}) ⊆ ((↑) '' S : Set (OnePoint V))ᶜ := by
    intro w hw
    obtain ⟨w0, hw0, rfl⟩ := hw
    exact fun ⟨w1, hw1, hqw⟩ ↦ hseg_off hw0 (OnePoint.coe_injective hqw ▸ hw1)
  have hz_mem : (z : OnePoint V) ∈ (↑) '' (segment ℝ p z \ {p}) :=
    ⟨z, ⟨right_mem_segment ℝ p z, hzne⟩, rfl⟩
  rw [connectedComponentIn_eq hzF]
  exact hconn.isPreconnected.subset_connectedComponentIn hz_mem himg
