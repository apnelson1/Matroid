import Mathlib.Analysis.InnerProductSpace.PiL2 -- inefficient import
import Mathlib.Topology.UniformSpace.Path
import Mathlib.Topology.Separation.Connected
import Mathlib.Geometry.Polygon.Basic -- inefficient import
import Matroid.ForMathlib.List
import Mathlib.Probability.ProbabilityMassFunction.Basic

universe u
variable {α β : Type u} {a b c x y z w : α} {C L : List α} {X Y : Set α} {N : ℕ}

open Set Function TopologicalSpace Topology Metric Nat unitInterval

lemma IsOpen.sSup_notMem {α : Type*} [CompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [DenselyOrdered α] {s : Set α} (hs : ∃ x, sSup s < x) (h : IsOpen s) : sSup s ∉ s := by
  intro m
  obtain ⟨ub, hub, hubs⟩ := exists_Ico_subset_of_mem_nhds (mem_nhds h m) hs
  obtain ⟨x, hssx, hxub⟩ := exists_between hub
  exact (le_sSup <| hubs ⟨hssx.le, hxub⟩).not_gt hssx

lemma IsOpen.sInf_notMem {α : Type*} [CompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [DenselyOrdered α] {s : Set α} (hs : ∃ x, x < sInf s) (h : IsOpen s) : sInf s ∉ s := by
  intro m
  obtain ⟨lb, lbl, hbls⟩ := exists_Ioc_subset_of_mem_nhds (mem_nhds h m) hs
  obtain ⟨x, hxlb, hxbls⟩ := exists_between lbl
  exact (sInf_le <| hbls ⟨hxlb, hxbls.le⟩).not_gt hxbls

namespace unitInterval
variable {t t₁ t₂ : I}

@[simp] lemma one_le (t : I) : 1 ≤ t ↔ t = 1 := top_le_iff
@[simp] lemma le_zero (t : I) : t ≤ 0 ↔ t = 0 := le_bot_iff

noncomputable def squishLeft : I → I := fun t =>
  ⟨(t : ℝ) / 2, by constructor <;> nlinarith [t.2.1, t.2.2]⟩
noncomputable def squishRight : I → I := fun t =>
  ⟨((t : ℝ) + 1) / 2, by constructor <;> nlinarith [t.2.1, t.2.2]⟩
noncomputable def half : I := ⟨2⁻¹, by constructor <;> linarith⟩

@[simp]
lemma squishLeft_le_half (t : I) : squishLeft t ≤ half := by
  simp only [half, squishLeft, Subtype.mk_le_mk]
  linarith [t.2.2]

@[simp]
lemma half_le_squishRight (t : I) : half ≤ squishRight t := by
  simp only [half, squishRight, Subtype.mk_le_mk]
  linarith [t.2.1]

@[simp]
lemma squishLeft_zero : squishLeft 0 = 0 := by
  simp [squishLeft]

@[simp]
lemma squishLeft_one : squishLeft 1 = half := by
  simp [half, squishLeft]

@[simp]
lemma squishRight_zero : squishRight 0 = half := by
  simp [half, squishRight]

@[simp]
lemma squishRight_one : squishRight 1 = 1 := by
  simp [squishRight]

@[simp]
lemma zero_lt_half : 0 < half := by
  simp only [half, ← Subtype.coe_lt_coe, Icc.coe_zero]
  positivity

@[simp]
lemma half_lt_one : half < 1 := by
  simp only [half, ← Subtype.coe_lt_coe, Icc.coe_one]
  exact two_inv_lt_one

lemma squishRight_lt_one (ht : t < 1) : squishRight t < 1 := by
  change t.val < 1 at ht
  simp only [squishRight, ← Subtype.coe_lt_coe, Icc.coe_one]
  exact (div_lt_one₀ (by positivity)).mpr <| by linarith

lemma squishLeft_injective : Injective squishLeft :=
  fun s t hst ↦ Subtype.ext <| by simpa [squishLeft] using hst

lemma squishRight_injective : Injective squishRight :=
  fun s t hst ↦ Subtype.ext <| by simpa [squishRight] using hst

lemma squishLeft_Icc (i j : I) : squishLeft '' Icc i j = Icc (squishLeft i) (squishLeft j) := by
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  ext t
  obtain ⟨t, ht⟩ := t
  simp only [squishLeft, mem_image, mem_Icc, Subtype.mk.injEq, Subtype.exists, Subtype.mk_le_mk,
    exists_and_left, exists_prop]
  refine ⟨fun h => ?_, fun ⟨hit, htj⟩ => ?_⟩
  · obtain ⟨x, ⟨hxi, hxj⟩, ⟨hx0, hx1⟩, rfl⟩ := h
    constructor <;> linarith
  refine ⟨2 * t, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> linarith [hj.2, ht.1]

lemma squishRight_Icc (i j : I) : squishRight '' Icc i j = Icc (squishRight i) (squishRight j) := by
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  ext t
  obtain ⟨t, ht⟩ := t
  simp only [squishRight, mem_image, mem_Icc, Subtype.mk.injEq, Subtype.exists, Subtype.mk_le_mk,
    exists_and_left, exists_prop]
  refine ⟨fun h => ?_, fun ⟨hit, htj⟩ => ?_⟩
  · obtain ⟨x, ⟨hxi, hxj⟩, ⟨hx0, hx1⟩, rfl⟩ := h
    constructor <;> linarith
  refine ⟨2 * t - 1, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> linarith [hj.2, hi.1]

end unitInterval

namespace Path

@[simp]
lemma refl_not_injective [AddCommGroup α] [Module ℝ α] [TopologicalSpace α] [ContinuousAdd α]
    [ContinuousSMul ℝ α] (x : α) : ¬ Injective (Path.refl x) := by
  intro h
  simpa using h (a₁ := 0) (a₂ := 1) (by simp)

@[simp]
lemma segment_injective [AddCommGroup α] [Module ℝ α] [TopologicalSpace α] [ContinuousAdd α]
    [ContinuousSMul ℝ α] (x y : α) : Injective (Path.segment x y) ↔ x ≠ y := by
  refine ⟨fun h => ?_, fun h s t hst => ?_⟩
  · rintro rfl
    simp at h
  simpa [h, Subtype.val_inj] using hst

@[simp]
lemma eq_zero_iff_of_injective [TopologicalSpace α] {P : Path x y} (h : Injective P) (t : I) :
    P t = x ↔ t = 0 := by
  nth_rw 3 [← P.source]
  rw [h.eq_iff]

@[simp]
lemma eq_one_iff_of_injective [TopologicalSpace α] {P : Path x y} (h : Injective P) (t : I) :
    P t = y ↔ t = 1 := by
  nth_rw 3 [← P.target]
  rw [h.eq_iff]

lemma trans_apply_ite_lt [TopologicalSpace α] {P : Path x y} {Q : Path y z} (i : I) :
    (P.trans Q) i = if h : i.val < 1/2 then
    P ⟨2 * i.val, (mul_pos_mem_iff zero_lt_two).2 ⟨i.2.1, h.le⟩⟩ else
    Q ⟨2 * i.val - 1, two_mul_sub_one_mem_iff.2 ⟨(not_lt.1 h), i.2.2⟩⟩ := by
  obtain hi | hi | hi := lt_trichotomy i.val 2⁻¹
  · simp [hi.le, hi, trans_apply]
  · simp [trans_apply, hi]
  simp [hi.not_ge, hi.not_gt, trans_apply]

lemma trans_squishLeft [TopologicalSpace α] {P : Path x y} {Q : Path y z} (i : I) :
    (P.trans Q) (squishLeft i) = P i := by
  have ht : i / 2 ≤ (2 : ℝ)⁻¹ := by linarith [i.2.2]
  simp [trans, squishLeft, comp_apply, ht]
  rw [mul_div_cancel₀ _ (by simp)]
  exact extend_extends' P i

lemma trans_squishRight [TopologicalSpace α] {P : Path x y} {Q : Path y z} (i : I) :
    (P.trans Q) (squishRight i) = Q i := by
  obtain rfl | ht0 := eq_or_ne i 0
  · simp [trans, squishRight]
  replace ht0 : i.val ≠ 0 := coe_ne_zero.mpr ht0
  have ht : ¬ ((↑i + 1) / 2 ≤ (2 : ℝ)⁻¹) := by
    rw [← lt_iff_not_ge, ← mul_lt_mul_iff_of_pos_left (a := 2) (by simp),
      mul_div_cancel₀ _ (by simp), mul_inv_cancel₀ (by simp)]
    linarith [i.prop.1.lt_of_ne' ht0]
  simp only [trans, one_div, coe_mk', ContinuousMap.coe_mk, comp_apply, squishRight, ht, ↓reduceIte]
  rw [mul_div_cancel₀ _ (by simp), add_sub_cancel_right]
  exact extend_extends' Q i

lemma trans_injective_iff [TopologicalSpace α] {P : Path x y} {Q : Path y z} :
    Injective (P.trans Q) ↔ Injective P ∧ Injective Q ∧ Disjoint (range P \ {y}) (range Q) := by
  refine ⟨fun h => ⟨fun s t hst ↦ ?_, fun s t hst ↦ ?_, ?_⟩, fun ⟨hP, hQ, hdj⟩ t₁ t₂ ht => ?_⟩
  · simpa [squishLeft, Subtype.val_inj] using h (a₁ := squishLeft s) (a₂ := squishLeft t)
      (by simpa [trans_squishLeft])
  · simpa [squishRight, Subtype.val_inj] using h (a₁ := squishRight s) (a₂ := squishRight t)
      (by simpa [trans_squishRight])
  · by_contra! hdj
    rw [not_disjoint_iff] at hdj
    obtain ⟨a, ⟨⟨t1, hPQ⟩, hay⟩, t2, rfl⟩ := hdj
    rw [← trans_squishRight t2, ← trans_squishLeft t1] at hPQ
    replace hPQ := by simpa [squishLeft, squishRight] using h hPQ
    obtain rfl : t2 = 0 := by
      apply Subtype.ext
      change t2.val = 0
      linarith [hPQ ▸ t1.prop.2, t2.prop.1]
    simp at hay
  by_cases ht₁ : (t₁ : ℝ) ≤ 2⁻¹ <;> by_cases ht₂ : (t₂ : ℝ) ≤ 2⁻¹ <;> simp only [trans_apply,
    one_div, ht₁, ↓reduceDIte, ht₂] at ht
  · simpa [Subtype.val_inj] using hP ht
  on_goal 3 => simpa [Subtype.val_inj] using hQ ht
  all_goals
  · have := ht ▸ (hdj.notMem_of_mem_right (a := Q _) (by simp))
    simp only [mem_diff, mem_range, exists_apply_eq_apply, mem_singleton_iff,
      Path.eq_one_iff_of_injective hP, Subtype.ext_iff, Icc.coe_one, true_and,
      Decidable.not_not] at this
    simp only [this, Icc.mk_one, Path.target, eq_comm (a := y), Q.eq_zero_iff_of_injective hQ,
      Subtype.ext_iff, Icc.coe_zero] at ht
    linarith

lemma injOn_ico_iff_injOn_ioc [TopologicalSpace α] (P : Path x x) :
    InjOn P (Ico 0 1) ↔ InjOn P (Ioc 0 1) := by
  wlog hoo : InjOn P (Ioo 0 1)
  · exact iff_of_false (hoo <| ·.mono Ioo_subset_Ico_self) (hoo <| ·.mono Ioo_subset_Ioc_self)
  refine ⟨fun h s hs t ht hst ↦ ?_, fun h s hs t ht hst ↦ ?_⟩
  · obtain rfl | hs1 := eq_or_ne s 1 <;> obtain rfl | ht1 := eq_or_ne t 1
    · rfl
    · rw [Path.target] at hst
      have := by simpa [hst] using h (by simp : (0 : I) ∈ _) ⟨ht.1.le, lt_of_le_of_ne ht.2 ht1⟩
      exact ht.1.ne this |>.elim
    · rw [Path.target] at hst
      have := by simpa [hst] using h ⟨hs.1.le, lt_of_le_of_ne hs.2 hs1⟩ (by simp : (0 : I) ∈ _)
      exact hs.1.ne' this |>.elim
    exact hoo ⟨hs.1, lt_of_le_of_ne hs.2 hs1⟩ ⟨ht.1, lt_of_le_of_ne ht.2 ht1⟩ hst
  obtain rfl | hs0 := eq_or_ne s 0 <;> obtain rfl | ht0 := eq_or_ne t 0
  · rfl
  · simp only [Path.source] at hst
    have := by simpa [hst] using h (by simp : (1 : I) ∈ _) ⟨ht.1.lt_of_ne' ht0, ht.2.le⟩
    exact ht.2.ne' this |>.elim
  · simp only [Path.source] at hst
    have := by simpa [hst] using h ⟨hs.1.lt_of_ne' hs0, hs.2.le⟩ (by simp : (1 : I) ∈ _)
    exact hs.2.ne this |>.elim
  exact hoo ⟨lt_of_le_of_ne' hs.1 hs0, hs.2⟩ ⟨lt_of_le_of_ne' ht.1 ht0, ht.2⟩ hst

lemma injective_left_iff_trans_injOn [TopologicalSpace α] (P : Path x y) (Q : Path y x) :
    InjOn (P.trans Q) (Icc 0 half) ↔ Injective P := by
  refine ⟨fun h s t hst ↦ ?_, fun h s hs t ht hst ↦ ?_⟩
  · rw [← trans_squishLeft (Q := Q), ← trans_squishLeft (Q := Q)] at hst
    refine squishLeft_injective.eq_iff.mp <| h ?_ ?_ hst <;> simp
  rw [← squishLeft_zero, ← squishLeft_one, ← squishLeft_Icc] at hs ht
  obtain ⟨s, hs, rfl⟩ := hs
  obtain ⟨t, ht, rfl⟩ := ht
  rw [trans_squishLeft, trans_squishLeft, h.eq_iff] at hst
  exact congrArg _ hst

lemma injective_right_iff_trans_injOn [TopologicalSpace α] (P : Path x y) (Q : Path y x) :
    InjOn (P.trans Q) (Icc half 1) ↔ Injective Q := by
  refine ⟨fun h s t hst ↦ ?_, fun h s hs t ht hst ↦ ?_⟩
  · rw [← trans_squishRight (P := P), ← trans_squishRight (P := P)] at hst
    refine squishRight_injective.eq_iff.mp <| h ?_ ?_ hst <;> simp [le_one']
  rw [← squishRight_zero, ← squishRight_one, ← squishRight_Icc] at hs ht
  obtain ⟨s, hs, rfl⟩ := hs
  obtain ⟨t, ht, rfl⟩ := ht
  rw [trans_squishRight, trans_squishRight, h.eq_iff] at hst
  exact congrArg _ hst

lemma trans_injOn_ico_iff [TopologicalSpace α] {P : Path x y} {Q : Path y x} :
    InjOn (P.trans Q) (Ico 0 1) ↔ Injective P ∧ Injective Q ∧
    Disjoint (range P \ {y}) (range Q \ {x}) := by
  refine ⟨fun h => ⟨fun s t hst ↦ ?_, fun s t hst ↦ ?_, ?_⟩,
    fun ⟨hP, hQ, hdj⟩ t₁ ht₁ t₂ ht₂ ht => ?_⟩
  · exact (P.injective_left_iff_trans_injOn Q).mp (h.mono <| Icc_subset_Ico_right half_lt_one)
    |>.eq_iff.mp hst
  · rw [injOn_ico_iff_injOn_ioc] at h
    have := h.mono ((Icc_subset_Ioc_iff le_one').mpr ⟨zero_lt_half, le_rfl⟩)
    exact ((P.injective_right_iff_trans_injOn Q).mp this).eq_iff.mp hst
  · by_contra! hdj
    rw [not_disjoint_iff] at hdj
    obtain ⟨a, ⟨⟨t1, hPQ⟩, hay⟩, ⟨t2, rfl⟩, hax⟩ := hdj
    rw [← trans_squishRight (P := P) t2, ← trans_squishLeft (Q := Q) t1] at hPQ
    have ht2 : t2 < 1 := by
      by_contra! ht2
      obtain rfl := ht2.antisymm t2.prop.2
      simp at hax
    replace hPQ := h (by simpa using squishLeft_le_half t1 |>.trans_lt half_lt_one)
      (by simpa using squishRight_lt_one ht2) hPQ
    simp only [squishLeft, squishRight, Subtype.mk.injEq, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, div_left_inj'] at hPQ
    obtain rfl : t2 = 0 := by
      apply Subtype.ext
      change t2.val = 0
      linarith [hPQ ▸ t1.prop.2, t2.prop.1]
    simp at hay
  obtain ht₁1 : (t₁ : ℝ) < 1 := ht₁.2
  obtain ht₂1 : (t₂ : ℝ) < 1 := ht₂.2
  by_cases ht₁ : (t₁ : ℝ) < 2⁻¹ <;> by_cases ht₂ : (t₂ : ℝ) < 2⁻¹ <;>
    simp only [trans_apply_ite_lt, one_div, ht₁, ↓reduceDIte, ht₂] at ht
  · simpa [Subtype.val_inj] using hP.eq_iff.mp ht
  on_goal 3 => simpa [hQ.eq_iff, Subtype.ext_iff] using ht
  on_goal 2 => rw [eq_comm] at ht
  all_goals
    refine (hdj.ne_of_mem ?_ ?_ ht).elim <;>
    · simp only [← P.target, ← Q.target, mem_diff, mem_range, hP.eq_iff, hQ.eq_iff,
      exists_apply_eq_apply, mem_singleton_iff, true_and]
      rw [Subtype.ext_iff, Icc.coe_one]
      linarith

lemma sSup_notMem {α : Type*} [TopologicalSpace α] {S : Set α} {x y : α} (P : Path x y)
    (hS : IsOpen S) (hy : y ∉ S) : P (sSup (P ⁻¹' S)) ∉ S := by
  by_cases h : sSup (P ⁻¹' S) = 1
  · simpa [h]
  replace h : sSup (P ⁻¹' S) < 1 := by
    by_contra! h'
    rw [one_le] at h'
    exact h h'
  simpa [h] using (P.continuous.isOpen_preimage _ hS).sSup_notMem ⟨1, h⟩

lemma sInf_notMem {α : Type*} [TopologicalSpace α] {S : Set α} {x y : α} (P : Path x y)
    (hS : IsOpen S) (hx : x ∉ S) : P (sInf (P ⁻¹' S)) ∉ S := by
  by_cases h : sInf (P ⁻¹' S) = 0
  · simpa [h]
  replace h : 0 < sInf (P ⁻¹' S) := by
    by_contra! h'
    rw [unitInterval.le_zero] at h'
    exact h h'
  simpa [h] using (P.continuous.isOpen_preimage _ hS).sInf_notMem ⟨0, h⟩
