import Mathlib.Geometry.Polygon.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
import Mathlib.Geometry.Convex.Cone.Basic

open Set RealInnerProductSpace Metric

section RealAffineSpace

variable {V P : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V P] {u v x y z : P}

def halfRay (v : V) (x : P) : Set P := (· • v +ᵥ x) '' Set.Ici (0 : ℝ)

lemma mem_halfRay (v : V) (x : P) : x ∈ halfRay v x := by
  use 0
  simp

@[simp]
lemma halfRay_zero (x : P) : halfRay 0 x = {x} := by
  ext y
  simp [halfRay]

lemma halfRay_eq_lineMap_image (v : V) (x : P) :
  halfRay v x = (AffineMap.lineMap x (v +ᵥ x) '' Set.Ici (0 : ℝ)) := by
  ext y
  constructor <;> rintro ⟨t, ht, rfl⟩
  · exact ⟨t, ht, by simp [AffineMap.lineMap_apply]⟩
  · exact ⟨t, ht, by simp [AffineMap.lineMap_apply]⟩

lemma halfRay_convex (v x : V) : Convex ℝ (halfRay v x) := by
  simpa [halfRay_eq_lineMap_image] using
    Convex.affine_image (f := AffineMap.lineMap x (v +ᵥ x)) (convex_Ici (0 : ℝ))

end RealAffineSpace

section RealVectorSpace

variable {α : Type*} [NormedAddCommGroup α] [InnerProductSpace ℝ α] {x y n : α} {r : ℝ}

@[simp]
lemma segment_isClosed (x y : α) : IsClosed (segment ℝ x y) := by
  rw [← Path.range_segment]
  exact isCompact_range (Path.segment x y).continuous |>.isClosed

def halfSpace (n : α) (r : ℝ) : Set α := {z | ⟪n, z⟫ < r}

def hyperplane (n : α) (r : ℝ) : Set α := {z | ⟪n, z⟫ = r}

lemma halfSpace_neg (n : α) (r : ℝ) : halfSpace (-n) r = {z | -r < ⟪n, z⟫} := by
  ext z
  simp [halfSpace, inner_neg_left, neg_lt]

lemma hyperplane_neg (n : α) (r : ℝ) : hyperplane (-n) r = hyperplane n (-r) := by
  ext z
  simp [hyperplane, inner_neg_left, neg_eq_iff_eq_neg]

@[simp]
lemma hyperplane_neg_neg (n : α) (r : ℝ) : hyperplane (-n) (-r) = hyperplane n r := by
  simp [hyperplane_neg]

lemma halfSpace_convex (n : α) (r : ℝ) : Convex ℝ (halfSpace n r) := by
  simpa [halfSpace] using (convex_halfSpace_lt (innerₗ _ n).isLinear r)

lemma hyperplane_convex (n : α) (r : ℝ) : Convex ℝ (hyperplane n r) := by
  simpa [hyperplane] using (convex_hyperplane (innerₗ _ n).isLinear r)

lemma halfSpace_isOpen (n : α) (r : ℝ) : IsOpen (halfSpace n r) := by
  simpa [halfSpace] using (isOpen_lt (continuous_const.inner continuous_id) continuous_const)

lemma hyperplane_isClosed (n : α) (r : ℝ) : IsClosed (hyperplane n r) := by
  simpa [hyperplane] using (isClosed_eq (continuous_const.inner continuous_id) continuous_const)

lemma halfSpace_closure (hn : n ≠ 0) (r : ℝ) : closure (halfSpace n r) = {z : α | ⟪n, z⟫ ≤ r} := by
  ext z
  have hnpos : 0 < ‖n‖ := norm_pos_iff.2 hn
  refine ⟨(closure_minimal (fun w hw ↦ ?_) (isClosed_le (continuous_const.inner continuous_id)
    continuous_const) ·), fun hzle ↦ ?_⟩
  · have : ⟪n, w⟫ < r := by simpa [halfSpace] using hw
    exact this.le
  obtain hz | rfl := lt_or_eq_of_le (by exact hzle : ⟪n, z⟫ ≤ r)
  · exact subset_closure (by simpa [halfSpace] using hz)
  refine Metric.mem_closure_iff.2 fun ε εpos ↦ ?_
  let t : ℝ := (ε / 2) / ‖n‖
  have htpos : 0 < t := div_pos (half_pos εpos) hnpos
  refine ⟨z - t • n, ?_, ?_⟩
  · simp only [halfSpace, mem_setOf_eq, inner_sub_right, inner_smul_right,
    inner_self_eq_norm_sq_to_K, RCLike.ofReal_real_eq_id, id_eq, sub_lt_self_iff]
    linarith [mul_pos htpos (sq_pos_of_pos hnpos)]
  · simpa [norm_smul, t, div_mul_cancel₀ _ hnpos.ne', abs_of_nonneg εpos.le]

lemma frontier_halfSpace (hn : n ≠ 0) (r : ℝ) : frontier (halfSpace n r) = hyperplane n r := by
  rw [frontier, (halfSpace_isOpen n r).interior_eq, halfSpace_closure hn r]
  ext z
  simp [halfSpace, hyperplane, not_lt, le_antisymm_iff]

lemma halfSpace_cover (n : α) (r : ℝ) :
    halfSpace n r ∪ hyperplane n r ∪ halfSpace (-n) (-r) = univ := by
  ext z
  rcases lt_trichotomy ⟪n, z⟫ r with hlt | heq | hgt <;> simp_all [halfSpace, hyperplane]

lemma halfSpace_disjoint_hyperplane (n : α) (r : ℝ) :
    Disjoint (halfSpace n r) (hyperplane n r) := by
  refine disjoint_left.2 ?_
  rintro z hzHS rfl
  simp [halfSpace] at hzHS

lemma hyperplane_disjoint_halfSpace_neg (n : α) (r : ℝ) :
    Disjoint (hyperplane n r) (halfSpace (-n) (-r)) := by
  refine disjoint_left.2 ?_
  rintro z rfl hzHS
  simp [halfSpace] at hzHS

lemma halfSpace_disjoint_halfSpace_neg (n : α) (r : ℝ) :
    Disjoint (halfSpace n r) (halfSpace (-n) (-r)) := by
  refine disjoint_left.2 fun z hz₁ hz₂ ↦ ?_
  simp only [halfSpace, mem_setOf_eq, inner_neg_left, neg_lt_neg_iff] at hz₁ hz₂
  linarith

lemma ball_diff_hyperplane_two_regions (n x : α) (r : ℝ) :
    connectedComponentIn (ball x r \ hyperplane n ⟪n, x⟫) '' (ball x r \ hyperplane n ⟪n, x⟫) =
    {ball x r ∩ halfSpace n ⟪n, x⟫, ball x r ∩ halfSpace (-n) (-⟪n, x⟫)} := by
  sorry

lemma ball_diff_hyperplane_frontier (n x : α) (r : ℝ) :
    ball x r ∩ hyperplane n ⟪n, x⟫ ⊆ frontier (ball x r ∩ halfSpace n ⟪n, x⟫) := by
  sorry

/-- The unit vector pointing from `x` to `y` along the segment. -/
noncomputable def segmentTangent (x y : α) : α :=
  ‖y - x‖⁻¹ • (y - x)

@[simp]
lemma segmentTangent_eq_zero_iff (x y : α) : segmentTangent x y = 0 ↔ x = y := by
  rw [segmentTangent, smul_eq_zero]
  simp [sub_eq_zero, eq_comm]

-- alias doesn't let me x and y to be implicit
lemma segmentTangent_eq_zero {x y : α} (hxy : x = y) : segmentTangent x y = 0 :=
  (segmentTangent_eq_zero_iff x y).mpr hxy

@[simp]
lemma segmentTangent_norm (hxy : x ≠ y) : ‖segmentTangent x y‖ = 1 := by
  rw [segmentTangent, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀]
  exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy.symm)

lemma segmentTangent_flip (x y : α) : segmentTangent y x = -segmentTangent x y := by
  unfold segmentTangent
  rw [← smul_neg, neg_sub, norm_sub_rev x y]

lemma segment_subset_halfRay (x y : α) :
    segment ℝ x y ⊆ halfRay (segmentTangent x y) x := by
  refine halfRay_convex (segmentTangent x y) x |>.segment_subset (mem_halfRay ..) ?_
  obtain rfl | hxy := eq_or_ne x y
  · simp_all [segmentTangent_eq_zero]
  use ‖y - x‖
  simp [segmentTangent]
  rw [smul_inv_smul₀ (by simp [sub_eq_zero, hxy.symm]), sub_add_cancel]

lemma segment_eq_segmentTangent (x y : α) :
    segment ℝ x y = (· • segmentTangent x y +ᵥ x) '' Icc 0 ‖y - x‖ := by
  obtain rfl | hxy := eq_or_ne x y
  · simp [segmentTangent_eq_zero]
  simp_rw [segment_eq_image', segmentTangent, vadd_eq_add, add_comm, smul_smul]
  rw [← image_image (f := (·  * ‖y - x‖⁻¹)) (g := (x + · • (y - x))), image_mul_right_Icc,
    zero_mul, mul_inv_cancel₀] <;> simp_all [sub_ne_zero, eq_comm]

lemma ball_inter_segment_eq_inter_halfRay (hr : r ≤ ‖y - x‖) :
    ball x r ∩ segment ℝ x y = ball x r ∩ halfRay (segmentTangent x y) x := by
  obtain rfl | hxy := eq_or_ne x y
  · simp [segmentTangent_eq_zero]
  ext z
  simp only [segment_eq_segmentTangent, vadd_eq_add, mem_inter_iff, mem_ball, mem_image, mem_Icc,
    halfRay, mem_Ici, and_congr_right_iff]
  refine fun hz ↦ exists_congr fun t ↦ ⟨?_, ?_⟩
  · rintro ⟨ht, rfl⟩
    simp [ht.1]
  rintro ⟨ht, rfl⟩
  simp only [dist_add_self_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht,
    segmentTangent_norm hxy, mul_one] at hz
  simp [ht, hz.le.trans hr]

end RealVectorSpace

namespace Plane

scoped notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

variable {x y : ℝ²} {S T : Set ℝ²}

noncomputable def segmentNormal (x y : ℝ²) : ℝ² :=
  !₂[- (segmentTangent x y) 1, (segmentTangent x y) 0]

lemma segmentNormal_norm (hxy : x ≠ y) : ‖segmentNormal x y‖ = 1 := by
  have hsq : ‖segmentNormal x y‖ ^ 2 = ‖segmentTangent x y‖ ^ 2 := by
    simp [segmentNormal, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, add_comm]
  rw [segmentTangent_norm hxy, one_pow 2, sq_eq_one_iff] at hsq
  grind [norm_nonneg (segmentNormal x y)]

lemma segmentNormal_orthogonal (x y : ℝ²) : ⟪segmentNormal x y, segmentTangent x y⟫ = 0 := by
  simp only [segmentNormal, Fin.isValue, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    Fin.sum_univ_two, Matrix.cons_val_zero, mul_neg, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

lemma segmentNormal_flip (x y : ℝ²) : segmentNormal y x = -segmentNormal x y := by
  ext i
  fin_cases i <;> simp [segmentNormal, segmentTangent_flip x]

lemma segment_subset_hyperplane (x y : ℝ²) :
    segment ℝ x y ⊆ hyperplane (segmentNormal x y) ⟪segmentNormal x y, x⟫ := by
  intro z hzxy
  rw [segment_eq_segmentTangent] at hzxy
  simp only [vadd_eq_add, mem_image, mem_Icc] at hzxy
  obtain ⟨t, ht, rfl⟩ := hzxy
  simp only [hyperplane, mem_setOf_eq, inner_add_right, inner_smul_right, segmentNormal_orthogonal,
    mul_zero, zero_add]

lemma clock_frontier {x u v : ℝ²} {r : ℝ} (hy : y ∈ (ball x r \ halfRay u x) \ halfRay v x) :
    ball x r ∩ (halfRay u x ∪ halfRay v x) ⊆ frontier (connectedComponentIn
    ((ball x r \ halfRay u x) \ halfRay v x) y) := by

  sorry



lemma exists_angle_fst_ne {S : Set ℝ²} (hS : S.Finite) :
    let A := EuclideanSpace.instFactEqNatFinrankFin 2
    let B := (A.out ▸ (stdOrthonormalBasis ℝ ℝ²).toBasis).orientation
    ∃ θ : Real.Angle, S.InjOn (B.rotation θ · 0) := by
  intro A B
  -- 1. Define the set of bad angles for a pair (u, v)
  let bad_angles (u v : ℝ²) : Set Real.Angle := {θ | B.rotation θ u 0  = B.rotation θ v 0}

  have hb (u v : ℝ²) :
      bad_angles u v = {θ | (θ.cos • (u - v) + θ.sin • B.rightAngleRotation (u - v)) 0 = 0} := by
    ext θ
    simp only [Fin.isValue, B.rotation_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      mem_setOf_eq, map_sub, PiLp.sub_apply, bad_angles]
    rw [← sub_eq_zero]
    ring_nf

  -- 2. Show bad_angles is finite for distinct u, v
  have h_finite_pair {u v : ℝ²} (h : u ≠ v) : (bad_angles u v).Finite := by
    rw [hb u v]
    simp only [Fin.isValue, map_sub, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    
    sorry

  -- 3. Define the set of all bad angles
  let all_bad_angles := ⋃ (u ∈ S) (v ∈ S) (_ : u ≠ v), bad_angles u v
  -- 4. Show the union is finite
  have h_finite_all : all_bad_angles.Finite := by
    refine Set.Finite.biUnion hS fun u _ ↦ Set.Finite.biUnion hS fun v _ ↦ ?_
    simp only [finite_iUnion_of_subsingleton]
    exact h_finite_pair
  -- 5. Conclude existence
  have h_infinite : (Set.univ : Set Real.Angle).Infinite := by
    have : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
    rw [infinite_univ_iff, Real.Angle, (AddCircle.equivIco _ 0).infinite_iff]
    apply Set.Ico.infinite
    positivity
  obtain ⟨θ, _, hθ⟩ := (h_infinite.diff h_finite_all).nonempty
  refine ⟨θ, fun x hxS y hyS hxy ↦ ?_⟩
  contrapose! hθ
  simp only [ne_eq, mem_iUnion, exists_prop, all_bad_angles]
  use x, hxS, y, hyS, hθ, hxy
