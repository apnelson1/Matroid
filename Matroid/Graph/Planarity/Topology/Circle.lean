import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
import Matroid.Graph.Planarity.Topology.Path

namespace Circle

variable {x y z : Circle} {a b : ℝ} {s : Set ℝ}

open Set Function TopologicalSpace Topology Metric Nat Complex

@[simp]
lemma unitary_eq_sphere : unitary ℂ = Metric.sphere (0 : ℂ) 1 := by
  ext x
  simp only [unitary, RCLike.star_def, mul_comm, Complex.mul_conj', sq_eq_one_iff,
    Complex.ofReal_eq_one, and_self, mem_sphere_iff_norm, sub_zero]
  norm_cast
  grind [norm_nonneg x]

noncomputable def unitaryCircleIsometryEquiv : unitary ℂ ≃ᵢ Circle :=
  ⟨Equiv.setCongr unitary_eq_sphere, fun _ ↦ congrFun rfl⟩

instance : LocPathConnectedSpace Circle := by
  convert LocPathConnectedSpace.coinduced unitaryCircleIsometryEquiv
  exact unitaryCircleIsometryEquiv.toHomeomorph.coinduced_eq.symm

noncomputable instance : HasDistribNeg Circle := inferInstanceAs <| HasDistribNeg (sphere _ _)
noncomputable instance : ContinuousNeg Circle := inferInstanceAs <| ContinuousNeg (sphere _ _)

@[simp, norm_cast] lemma coe_neg (x : Circle) : ↑(-x) = -(x : ℂ) := rfl

lemma neg_ne_self (x : Circle) : -x ≠ x :=
  fun h ↦ coe_ne_zero x <| neg_eq_self.mp <| coe_neg x ▸ congrArg Subtype.val h

lemma exp_injOn_of_diff_lt (hs : ∀ x ∈ s, ∀ y ∈ s, x - y ∈ Ioo (-2 * Real.pi) (2 * Real.pi)) :
    InjOn exp s := by
  intro t₁ ht₁ t₂ ht₂ heq
  obtain ⟨h1, h2⟩ := hs t₁ ht₁ t₂ ht₂
  rw [neg_mul] at h1
  rw [← sub_eq_zero, ← Real.cos_eq_one_iff_of_lt_of_lt h1 h2, ← exp_ofReal_mul_I_re]
  replace heq : cexp _ = cexp _ := congrArg Subtype.val heq
  rw [exp_eq_exp_iff_exp_sub_eq_one, ← sub_mul, ← ofReal_sub, Complex.ext_iff] at heq
  exact heq.1

lemma exp_injOn_Icc (h : b - a < 2 * Real.pi) : InjOn exp (Icc a b) :=
  exp_injOn_of_diff_lt <| fun x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩ ↦ by constructor <;> linarith

lemma exp_injOn_Ico (h : b - a ≤ 2 * Real.pi) : InjOn exp (Ico a b) :=
  exp_injOn_of_diff_lt <| fun x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩ ↦ by constructor <;> linarith

lemma exp_injOn_Ioc (h : b - a ≤ 2 * Real.pi) : InjOn exp (Ioc a b) :=
  exp_injOn_of_diff_lt <| fun x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩ ↦ by constructor <;> linarith

lemma surjective_exp : Surjective exp := fun z => ⟨z.val.arg, exp_arg z⟩

/-- Directed angle length from `x` to `y` along the anti-clockwise arc (principal `arg`). -/
noncomputable abbrev angleDiff (x y : Circle) : ℝ :=
  if x.val.arg ≤ y.val.arg then y.val.arg - x.val.arg else 2 * Real.pi + y.val.arg - x.val.arg

lemma angleDiff_nonneg (x y : Circle) : 0 ≤ angleDiff x y := by
  grind [neg_pi_lt_arg y.val, arg_le_pi x.val]

lemma angleDiff_pos (h : x ≠ y) : 0 < angleDiff x y := by
  grind [arg_eq_arg, neg_pi_lt_arg y.val, arg_le_pi x.val]

lemma arg_lt_arg_add_two_pi (x y : Circle) : x.val.arg < y.val.arg + 2 * Real.pi := by
  grind [arg_le_pi x.val, neg_pi_lt_arg y.val]

lemma angleDiff_lt_two_pi (x y : Circle) : angleDiff x y < 2 * Real.pi := by
  grind [neg_pi_lt_arg x.val, arg_le_pi y.val]

@[simp]
lemma angleDiff_add_symm (h : x ≠ y) : angleDiff x y + angleDiff y x = 2 * Real.pi := by
  grind [arg_eq_arg, neg_pi_lt_arg x.val, arg_le_pi y.val]

@[simp]
lemma cexp_angleDiff_add_symm : Complex.exp (angleDiff x y * I) * x.val = y.val := by
  rw [← coe_exp, ← exp_arg x, ← coe_mul, ← exp_add, angleDiff]
  split_ifs with hxy <;> simp

lemma Icc_angleDiff_union (h : x ≠ y) :
    Icc x.val.arg (x.val.arg + angleDiff x y) ∪ Icc y.val.arg (y.val.arg + angleDiff y x) =
    Icc (min x.val.arg y.val.arg) (min x.val.arg y.val.arg + 2 * Real.pi) := by
  grind [arg_eq_arg, arg_lt_arg_add_two_pi y x, arg_lt_arg_add_two_pi x y]

lemma Ico_angleDiff_union (h : x ≠ y) :
    Ico x.val.arg (x.val.arg + angleDiff x y) ∪ Ico y.val.arg (y.val.arg + angleDiff y x) =
    Ico (min x.val.arg y.val.arg) (min x.val.arg y.val.arg + 2 * Real.pi) := by
  grind [arg_eq_arg, arg_lt_arg_add_two_pi y x, arg_lt_arg_add_two_pi x y]

lemma Ioc_angleDiff_union (h : x ≠ y) :
    Ioc x.val.arg (x.val.arg + angleDiff x y) ∪ Ioc y.val.arg (y.val.arg + angleDiff y x) =
    Ioc (min x.val.arg y.val.arg) (min x.val.arg y.val.arg + 2 * Real.pi) := by
  grind [arg_eq_arg, arg_lt_arg_add_two_pi y x, arg_lt_arg_add_two_pi x y]

private lemma angleDiff_add_arg_image_Icc (x y : Circle) :
    (angleDiff x y * · + x.val.arg) '' Icc 0 1 = Icc x.val.arg (x.val.arg + angleDiff x y) := by
  by_cases h : 0 < angleDiff x y
  · simpa [add_comm] using image_affine_Icc' h x.val.arg 0 1
  simp [(not_lt.mp h).antisymm (angleDiff_nonneg x y)]

private lemma angleDiff_add_arg_image_Ico (h : x ≠ y) :
    (angleDiff x y * · + x.val.arg) '' Ico 0 1 = Ico x.val.arg (x.val.arg + angleDiff x y) := by
  simpa [add_comm] using (image_affine_Ico (angleDiff_pos h) x.val.arg 0 1)

private lemma angleDiff_add_arg_image_Ioc (h : x ≠ y) :
    (angleDiff x y * · + x.val.arg) '' Ioc 0 1 = Ioc x.val.arg (x.val.arg + angleDiff x y) := by
  simpa [add_comm] using (image_affine_Ioc (angleDiff_pos h) x.val.arg 0 1)

/-- Path from `x` to `y` on the circle traversing in anti-clockwise direction. -/
noncomputable def path (x y : Circle) : Path x y where
  toFun a := exp (angleDiff x y * a + x.val.arg)
  source' := by simp
  target' := Subtype.ext <| by simp
  continuous_toFun :=
    exp.continuous.comp ((continuous_const.mul continuous_subtype_val).add continuous_const)

lemma joined (x y : Circle) : Joined x y := ⟨path x y⟩

instance : PathConnectedSpace Circle where
  nonempty := ⟨1, by simp⟩
  joined x y := joined x y

@[simp]
lemma path_apply (x y : Circle) (a : unitInterval) :
    path x y a = exp (angleDiff x y * a + x.val.arg) := rfl

lemma path_apply_of_le (h : x.val.arg ≤ y.val.arg) (a : unitInterval) :
    path x y a = exp ((y.val.arg - x.val.arg) * a.val + x.val.arg) := by
  simp [path, angleDiff, h]

lemma path_apply_of_lt (h : y.val.arg < x.val.arg) (a : unitInterval) :
    path x y a = exp ((2 * Real.pi + y.val.arg - x.val.arg) * a.val + x.val.arg) := by
  simp [path, angleDiff, not_le.mpr h]

@[simp]
lemma path_self (x : Circle) : path x x = Path.refl x := by
  ext a
  simp [path, angleDiff]

lemma path_injective_of_ne (hne : x ≠ y) : Injective (path x y) := by
  intro a b (heq : exp _ = exp _)
  have hinj : Injective (angleDiff x y * · + x.val.arg) :=
    fun a b h ↦ by nlinarith [angleDiff_pos hne]
  refine Subtype.ext <| hinj ?_
  suffices hIcc : ∀ c : unitInterval, angleDiff x y * c.val + x.val.arg ∈
      Icc x.val.arg (x.val.arg + angleDiff x y) by
    rwa [exp_injOn_Icc (by linarith [angleDiff_lt_two_pi x y]) |>.eq_iff (hIcc a) (hIcc b)] at heq
  refine fun c ↦ ⟨?_, ?_⟩ <;> nlinarith [angleDiff_nonneg x y, c.prop.1, c.prop.2]

@[simp]
lemma path_range (x y : Circle) :
    range (path x y) = exp '' Icc x.val.arg (x.val.arg + angleDiff x y) := by
  ext z
  simp [← angleDiff_add_arg_image_Icc]

lemma path_image_Ico_of_ne (h : x ≠ y) :
    path x y '' Ico 0 1 = exp '' Ico x.val.arg (x.val.arg + angleDiff x y) := by
  ext z
  rw [path, Path.coe_mk', ContinuousMap.coe_mk, ← image_image, ← angleDiff_add_arg_image_Ico h,
    ← image_image (angleDiff x y * · + x.val.arg)]
  simp

lemma path_image_Ioc_of_ne (h : x ≠ y) :
    path x y '' Ioc 0 1 = exp '' Ioc x.val.arg (x.val.arg + angleDiff x y) := by
  ext z
  rw [path, Path.coe_mk', ContinuousMap.coe_mk, ← image_image, ← angleDiff_add_arg_image_Ioc h,
    ← image_image (angleDiff x y * · + x.val.arg)]
  simp

lemma path_range_union (h : x ≠ y) : range (path x y) ∪ range (path y x) = univ := by
  rw [path_range, path_range, ← image_union, Icc_angleDiff_union h,
    periodic_exp.image_Icc Real.two_pi_pos]
  exact surjective_exp.range_eq

lemma path_image_Ioc_union (h : x ≠ y) : path x y '' Ioc 0 1 ∪ path y x '' Ioc 0 1 = univ := by
  rw [path_image_Ioc_of_ne h, path_image_Ioc_of_ne h.symm, ← image_union, Ioc_angleDiff_union h,
    periodic_exp.image_Ioc Real.two_pi_pos]
  exact surjective_exp.range_eq

lemma path_disjoint_Ioc (h : x ≠ y) : Disjoint (path x y '' Ioc 0 1) (path y x '' Ioc 0 1) := by
  rw [disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
  rintro z ⟨⟨a, ha, rfl⟩, ⟨b, hb, heq⟩⟩
  have hdisj : Disjoint (Ioc x.val.arg (x.val.arg + angleDiff x y))
      (Ioc y.val.arg (y.val.arg + angleDiff y x)) := by grind
  rw [← angleDiff_add_arg_image_Ioc h, ← angleDiff_add_arg_image_Ioc h.symm] at hdisj
  refine hdisj.ne_of_mem ⟨a.val, ⟨ha.1, a.prop.2⟩, rfl⟩ ⟨b.val, ⟨hb.1, b.prop.2⟩, rfl⟩
  <| exp_injOn_Ioc (a := min x.val.arg y.val.arg) (b := min x.val.arg y.val.arg + 2 * Real.pi)
    (by simp) ?_ ?_ heq.symm
  <;> rw [← Ioc_angleDiff_union h, ← angleDiff_add_arg_image_Ioc h,
    ← angleDiff_add_arg_image_Ioc h.symm]
  · exact Or.inl <| mem_image_of_mem _ ha
  exact Or.inr <| mem_image_of_mem _ hb

lemma path_range_inter (h : x ≠ y) : range (path x y) ∩ range (path y x) = {x, y} := by
  rw [← image_univ, ← image_univ, unitInterval.univ_eq_Icc, ← Ioc_insert_left (by simp),
    ← Ioo_insert_right (by simp)]
  simp_rw [image_insert_eq]
  have h : Disjoint ((x.path y) '' Ioo 0 1) ((y.path x) '' Ioo 0 1) := by
    refine (path_disjoint_Ioc h).mono ?_ ?_ <;> exact image_mono Ioo_subset_Ioc_self
  grind

lemma singleton_compl_isPathConnected (x : Circle) : IsPathConnected {x}ᶜ := by
  refine ⟨-x, neg_ne_self x, fun y (hyx : y ≠ x) ↦ ?_⟩
  obtain hxP | hxP := (em (x ∈ range (path (-x) y))).symm
  · exact ⟨(path (-x) y), fun t ↦ by grind⟩
  refine ⟨(path y (-x)).symm, ?_⟩
  have hne : -x ≠ y := by
    rintro rfl
    simp [(neg_ne_self x).symm] at hxP
  have hP₂ : x ∉ range (path y (-x)) := by
    rintro hP₂
    have h : x ∈ range _ ∩ _ := ⟨hxP, hP₂⟩
    rw [path_range_inter hne] at h
    simp [(neg_ne_self x).symm, hyx.symm] at h
  grind

lemma compl_not_isPreconnected_of_nontrivial (hxy : x ≠ y) : ¬ IsPreconnected {x, y}ᶜ := by
  rintro h
  replace h : PreconnectedSpace ({x, y}ᶜ : Set Circle) := Subtype.preconnectedSpace h
  rw [preconnectedSpace_iff_clopen] at h
  specialize h ((Subtype.val : ({x, y}ᶜ : Set Circle) → Circle) ⁻¹' range (path x y)) ⟨?_, ?_⟩
  · exact (isCompact_range (path x y).continuous).isClosed.preimage continuous_subtype_val
  · have : ((Subtype.val : ({x, y}ᶜ : Set Circle) → Circle) ⁻¹' range (path y x))ᶜ =
      (Subtype.val : ({x, y}ᶜ : Set Circle) → Circle) ⁻¹' range (path x y) := by
      ext ⟨z, hz⟩
      have h1 := Set.ext_iff.mp (path_range_union hxy) z |>.mpr (mem_univ z)
      have h2 := Set.ext_iff.mp (path_range_inter hxy) z |>.not.mpr hz
      grind
    rw [← this, isOpen_compl_iff]
    exact (isCompact_range (path y x).continuous).isClosed.preimage continuous_subtype_val
  absurd h
  push Not
  rw [ne_univ_iff_exists_notMem]
  refine ⟨⟨⟨x.path y unitInterval.half, ?_⟩, unitInterval.half, rfl⟩,
    ⟨⟨y.path x unitInterval.half, ?_⟩, ?_⟩⟩
  · simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or, ← ne_eq]
    nth_rw 4 [← (x.path y).source]
    nth_rw 10 [← (x.path y).target]
    constructor <;> exact ((path_injective_of_ne hxy).ne <| by simp)
  · simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or, ← ne_eq]
    nth_rw 4 [← (y.path x).target]
    nth_rw 10 [← (y.path x).source]
    constructor <;> exact (path_injective_of_ne hxy.symm).ne <| by simp
  rintro ⟨t, ht⟩
  have h1 : _ ∈ range (path x y) ∩ range (path y x) := ⟨⟨t, ht⟩, ⟨unitInterval.half, rfl⟩⟩
  obtain h1 | h1 := path_range_inter hxy ▸ h1
  · exact (path_injective_of_ne hxy.symm).ne unitInterval.half_ne_one
    <| h1.trans (y.path x).target.symm
  exact (path_injective_of_ne hxy.symm).ne unitInterval.half_ne_zero
  <| h1.trans (y.path x).source.symm

end Circle
