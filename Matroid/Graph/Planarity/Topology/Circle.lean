import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
import Matroid.Graph.Planarity.Topology.Path

open Set Function TopologicalSpace Topology Metric Nat Complex Real

instance (x : ℝ) : LocPathConnectedSpace (AddCircle x) := LocPathConnectedSpace.coinduced _

instance : LocPathConnectedSpace Circle := by
  convert LocPathConnectedSpace.coinduced AddCircle.homeomorphCircle'
  exact AddCircle.homeomorphCircle'.coinduced_eq.symm

lemma Complex.im_eq_zero (x : ℂ) : x.im = 0 ↔ x.re = x := by
  rw [im_eq_zero_iff_isSelfAdjoint]
  exact ⟨conj_eq_iff_re.mp, fun h => h ▸ (im_eq_zero_iff_isSelfAdjoint ↑x.re).mp rfl⟩

namespace Circle

variable {x y z : Circle} {a b : ℝ} {s : Set ℝ}

-- noncomputable instance : InvolutiveNeg Circle := inferInstanceAs <| InvolutiveNeg (sphere _ _)

-- noncomputable instance : InvolutiveNeg ↥(Submonoid.unitSphere ℂ) :=
--   inferInstanceAs <| InvolutiveNeg (sphere _ _)

lemma path_isClosedEmbedding_of_ne (hne : x ≠ y) : IsClosedEmbedding (path x y) :=
  (path x y).continuous.isClosedEmbedding (path_injective_of_ne hne)

@[simp] lemma coe_neg_one : (↑(-1 : Circle) : ℂ) = (-1 : ℂ) := rfl

@[simp]
lemma im_val_eq_zero_iff (x : Circle) : x.val.im = 0 ↔ x = 1 ∨ x = -1 := by
  refine ⟨fun h => ?_, by rintro (rfl | rfl) <;> simp⟩
  suffices x.val = 1 ∨ x.val = -1 by
    obtain h | h := this
    · simp only [OneMemClass.coe_eq_one] at h
      tauto
    simp_rw [← neg_eq_iff_eq_neg, ← coe_neg, OneMemClass.coe_eq_one] at h
    exact Or.inr <| neg_eq_iff_eq_neg.mp h
  rw [im_eq_zero] at h
  have hnorm : ‖x.val‖ = 1 := norm_coe x
  rw [← h] at hnorm ⊢
  simp_rw [← neg_eq_iff_eq_neg, ← ofReal_neg, ofReal_eq_one, neg_eq_iff_eq_neg]
  simpa [abs_eq] using hnorm

@[simp]
lemma angleDiff_neg (x : Circle) : angleDiff x (-x) = π := by
  simp only [angleDiff, coe_neg]
  obtain h | h | h := lt_trichotomy x.val.im 0
  · simp [x.val.arg_neg_eq_arg_add_pi_of_im_neg h, pi_pos.not_gt]
  · obtain rfl | rfl := (im_val_eq_zero_iff x).mp h <;> simp [pi_pos.not_ge, two_mul, pi_nonneg]
  simp only [x.val.arg_neg_eq_arg_sub_pi_of_im_pos h, le_sub_self_iff, pi_pos.not_ge, ↓reduceIte]
  ring

@[simp]
lemma angleDiff_neg' (x : Circle) : angleDiff (-x) x = π := by
  nth_rw 2 [← neg_neg x]
  exact angleDiff_neg ..

noncomputable def fullPath (x : Circle) : Path x x :=
  (Path.segment x.val.arg <| x.val.arg + 2 * π).map exp.continuous
    |>.cast (by simp) (by simp)

lemma coe_fullPath (x : Circle) : (fullPath x : _ → _) =
    exp ∘ ⇑(Path.segment x.val.arg (x.val.arg + 2 * π)) := by
  ext t
  simp [fullPath]

lemma fullPath_eq_path_trans_path (x : Circle) :fullPath x = (path x (-x)).trans (path (-x) x) := by
  ext t
  simp only [fullPath, Path.cast_coe, Path.map_coe, comp_apply, Path.segment_apply, coe_exp,
    Path.trans_apply, one_div, path_apply, angleDiff_neg, coe_neg]
  split_ifs with hle <;> simp only [coe_exp]
  · congr 3
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    ring
  obtain h1 | h2 : (x.val.im < 0 ∨ x.val.im = 0 ∧ 0 < x.val.re) ∨
      (0 < x.val.im ∨ x.val.im = 0 ∧ x.val.re < 0) := by
    have : x.val.re ≠ 0 ∨ x.val.im ≠ 0 := by_contra fun h ↦ coe_ne_zero x <| Complex.ext_iff.mpr
      (by tauto)
    grind
  · congr 3
    conv_rhs => exact Path.segment_apply (-x.val).arg ..
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, add_sub_cancel_left, smul_eq_mul, vadd_eq_add,
      angleDiff_neg', add_sub_cancel_right, x.val.arg_neg_eq_arg_add_pi_iff.mpr h1]
    ring
  conv_rhs => apply (mul_one _).symm
  rw [← exp_two_pi_mul_I, ← Complex.exp_add]
  congr 3
  conv_rhs => left; left; args; exact Path.segment_apply ..
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, add_sub_cancel_left, smul_eq_mul, vadd_eq_add,
    ofReal_add, ofReal_mul, ofReal_ofNat, angleDiff_neg', add_sub_cancel, sub_sub_cancel,
    ofReal_sub, ofReal_one, x.val.arg_neg_eq_arg_sub_pi_iff.mpr h2]
  ring

-- lemma fullPath_injOn_Ico (x : Circle) : InjOn (fullPath x) (Ico 0 1) := by
--   sorry

end Circle
