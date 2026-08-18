module

public import Mathlib.Analysis.InnerProductSpace.PiL2 -- inefficient import

@[expose] public section

variable {α β : Type*} {a b c x y z w : α} {C L : List α} {X Y : Set α} {N : ℕ}

open Set Function TopologicalSpace Topology Metric Nat unitInterval Set.Notation

lemma pathConnectedSpace_Ioo {E} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [ContinuousAdd E] [PartialOrder E] [ContinuousSMul ℝ E] [IsOrderedCancelAddMonoid E]
    [PosSMulStrictMono ℝ E] [DenselyOrdered E] {a b : E} (hab : a < b) :
    PathConnectedSpace (Ioo a b) :=
  isPathConnected_iff_pathConnectedSpace.mp <| (convex_Ioo a b).isPathConnected
  <| Set.nonempty_Ioo.mpr hab

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

@[simp] lemma one_le : 1 ≤ t ↔ t = 1 := top_le_iff
@[simp] lemma le_zero : t ≤ 0 ↔ t = 0 := le_bot_iff

@[simp]
lemma val_le_zero_iff : t.val ≤ 0 ↔ t = 0 := by
  simp only [t.prop.1.ge_iff_eq, eq_comm, Icc.coe_eq_zero]

@[simp]
lemma one_le_val_iff : 1 ≤ t.val ↔ t = 1 := by
  simp only [t.prop.2.ge_iff_eq, Icc.coe_eq_one]

lemma Icc_eq_univ : Icc (0 : I) 1 = univ := by
  ext t
  have := mem_univ t
  have := t.prop
  tauto

/-- Every parameter of `I` is an endpoint or lies in its open interior. -/
lemma eq_zero_or_eq_one_or_mem_Ioo (t : I) : t = 0 ∨ t = 1 ∨ t ∈ Ioo (0 : I) 1 :=
  Set.eq_endpoints_or_mem_Ioo_of_mem_Icc (Icc_eq_univ ▸ mem_univ t)

instance : ContinuousMul I := submonoid.continuousMul
instance : PathConnectedSpace I :=
  isPathConnected_iff_pathConnectedSpace.mp <| (convex_Icc 0 1).isPathConnected ⟨0, by simp⟩
instance : LocallyPathConnectedSpace I := (convex_Icc 0 1).locallyPathConnectedSpace

noncomputable def squishLeft : I → I := fun t =>
  ⟨(t : ℝ) / 2, by constructor <;> nlinarith [t.2.1, t.2.2]⟩
noncomputable def squishRight : I → I := fun t =>
  ⟨((t : ℝ) + 1) / 2, by constructor <;> nlinarith [t.2.1, t.2.2]⟩
noncomputable def half : I := ⟨2⁻¹, by constructor <;> linarith⟩

@[simp]
lemma squishLeft_le_half (t : I) : squishLeft t ≤ half := by
  simp only [half, squishLeft, ← Subtype.coe_le_coe]
  linarith [t.2.2]

@[simp]
lemma half_le_squishRight (t : I) : half ≤ squishRight t := by
  simp only [half, squishRight, ← Subtype.coe_le_coe]
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

@[simp] lemma half_ne_zero : half ≠ 0 := zero_lt_half.ne'

@[simp]
lemma half_lt_one : half < 1 := by
  simp only [half, ← Subtype.coe_lt_coe, Icc.coe_one]
  exact two_inv_lt_one

@[simp] lemma half_ne_one : half ≠ 1 := half_lt_one.ne

lemma squishRight_lt_one (ht : t < 1) : squishRight t < 1 := by
  change t.val < 1 at ht
  simp only [squishRight, ← Subtype.coe_lt_coe, Icc.coe_one]
  exact (div_lt_one₀ (by positivity)).mpr <| by linarith

lemma squishLeft_injective : Injective squishLeft :=
  fun s t hst ↦ Subtype.ext <| by grind [squishLeft]

lemma squishRight_injective : Injective squishRight :=
  fun s t hst ↦ Subtype.ext <| by grind [squishRight]

lemma squishLeft_Icc (i j : I) : squishLeft '' Icc i j = Icc (squishLeft i) (squishLeft j) := by
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  ext ⟨t, ht⟩
  simp only [squishLeft, mem_image, mem_Icc, ← Subtype.coe_le_coe, Subtype.exists, exists_and_left]
  refine ⟨fun h => ?_, fun ⟨hit, htj⟩ => ?_⟩
  · grind
  refine ⟨2 * t, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> grind

lemma squishRight_Icc (i j : I) : squishRight '' Icc i j = Icc (squishRight i) (squishRight j) := by
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  ext ⟨t, ht⟩
  simp only [squishRight, mem_image, mem_Icc, Subtype.exists, ← Subtype.coe_le_coe,
    exists_and_left]
  refine ⟨fun h => ?_, fun ⟨hit, htj⟩ => ?_⟩
  · grind
  refine ⟨2 * t - 1, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> grind

end unitInterval

namespace Path

lemma range_isPathConnected [TopologicalSpace α] (P : Path x y) : IsPathConnected (range P) :=
  image_univ ▸ isPathConnected_univ.image P.continuous

-- lemma extend_image [TopologicalSpace α] (P : Path x y) (s : Set ℝ) :
--     P.extend '' s = P '' (Icc (0 : ℝ) 1 ↓∩ s) := by
--   ext z
--   simp only [mem_image, mem_preimage, Subtype.exists, mem_Icc, exists_and_left]
--   constructor
--   · rintro ⟨t, ht, rfl⟩
--     use t, ht

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
  · exact squishLeft_injective <| h (by simpa [trans_squishLeft] using hst)
  · exact squishRight_injective <| h (by simpa [trans_squishRight] using hst)
  · by_contra! hdj
    rw [not_disjoint_iff] at hdj
    obtain ⟨a, ⟨⟨t1, hPQ⟩, hay⟩, t2, rfl⟩ := hdj
    rw [← trans_squishRight t2, ← trans_squishLeft t1] at hPQ
    replace hPQ := by simpa [squishLeft, squishRight] using h hPQ
    replace hPQ : (t1 : ℝ) / 2 = (t2 + 1) / 2 := by
      simpa [squishLeft, squishRight, Subtype.ext_iff] using hPQ
    obtain rfl : t2 = 0 := by
      have : (t2 : ℝ) = 0 := by linarith [hPQ, t1.prop.2, t2.prop.1]
      exact Subtype.ext (by simpa [Icc.coe_zero])
    simp at hay
  by_cases ht₁ : (t₁ : ℝ) ≤ 2⁻¹ <;> by_cases ht₂ : (t₂ : ℝ) ≤ 2⁻¹ <;> simp only [trans_apply,
    one_div, ht₁, ↓reduceDIte, ht₂] at ht
  · simpa [Subtype.val_inj] using hP ht
  on_goal 3 => simpa [Subtype.val_inj] using hQ ht
  all_goals
  have := ht ▸ (hdj.notMem_of_mem_right (a := Q _) (by simp))
  simp only [mem_sdiff, mem_range, exists_apply_eq_apply, mem_singleton_iff,
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
    replace hPQ : (t1 : ℝ) / 2 = (t2 + 1) / 2 := by
      simpa [squishLeft, squishRight, Subtype.ext_iff] using hPQ
    obtain rfl : t2 = 0 := by
      have : (t2 : ℝ) = 0 := by linarith [hPQ, t1.prop.2, t2.prop.1]
      exact Subtype.ext (by simpa [Icc.coe_zero])
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
    · simp only [← P.target, ← Q.target, mem_sdiff, mem_range, hP.eq_iff, hQ.eq_iff,
      exists_apply_eq_apply, mem_singleton_iff, true_and]
      rw [Subtype.ext_iff, Icc.coe_one]
      linarith

lemma sSup_notMem {α : Type*} [TopologicalSpace α] {S : Set α} {x y : α} (P : Path x y)
    (hS : IsOpen S) (hy : y ∉ S) : P (sSup (P ⁻¹' S)) ∉ S := by
  by_cases h : sSup (P ⁻¹' S) = 1
  · simpa [h]
  replace h : sSup (P ⁻¹' S) < 1 := by
    contrapose! h
    exact unitInterval.one_le.mp h
  simpa [h] using (P.continuous.isOpen_preimage _ hS).sSup_notMem ⟨1, h⟩

lemma sInf_notMem {α : Type*} [TopologicalSpace α] {S : Set α} {x y : α} (P : Path x y)
    (hS : IsOpen S) (hx : x ∉ S) : P (sInf (P ⁻¹' S)) ∉ S := by
  by_cases h : sInf (P ⁻¹' S) = 0
  · simpa [h]
  replace h : 0 < sInf (P ⁻¹' S) := by
    contrapose! h
    exact unitInterval.le_zero.mp h
  simpa [h] using (P.continuous.isOpen_preimage _ hS).sInf_notMem ⟨0, h⟩


variable {α : Type*} [TopologicalSpace α] {x : α}

/-- A loop is a *simple loop* if it does not visit any point twice, except that it ends where it
started. -/
def IsSimpleLoop (P : Path x x) : Prop := InjOn P (Ico 0 1)

lemma isSimpleLoop_iff_injOn_ioc {P : Path x x} : P.IsSimpleLoop ↔ InjOn P (Ioc 0 1) := by
  change InjOn P (Ico 0 1) ↔ InjOn P (Ioc 0 1)
  wlog hoo : InjOn P (Ioo 0 1)
  · exact iff_of_false (hoo <| ·.mono Ioo_subset_Ico_self) (hoo <| ·.mono Ioo_subset_Ioc_self)
  refine ⟨fun h s hs t ht hst ↦ ?_, fun h s hs t ht hst ↦ ?_⟩
  · obtain rfl | hs1 := eq_or_ne s 1 <;> obtain rfl | ht1 := eq_or_ne t 1
    · rfl
    · rw [Path.target] at hst
      have := by simpa [hst] using h (by simp : (0 : I) ∈ _) ⟨ht.1.le,
        lt_of_le_of_ne ht.2 ht1⟩
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

lemma IsSimpleLoop.injOn_ioo {P : Path x x} (h : P.IsSimpleLoop) : InjOn P (Ioo 0 1) :=
  h.mono Ioo_subset_Ico_self

@[simp] lemma not_isSimpleLoop_refl : ¬ (Path.refl x).IsSimpleLoop := by
  intro h
  have heq := h (x₁ := 0) (x₂ := half) (by simp) (by simp) (by rfl)
  exact half_ne_zero heq.symm

/-! ### Cutting a path at a metric ball -/

/-- On an injectively parametrised path, a connected piece of the image containing `γ t₁` and
`γ t₂` contains the whole parameter interval between them.

The preimage inherits connectedness from the piece only because `γ` is a closed embedding, which on
the compact domain `I` is exactly injectivity. This is the step that turns "two subarcs meet in a
single point" into "two subarcs are the two parameter halves". -/
@[grind →]
lemma image_Icc_subset_of_isConnected [T2Space α] {y : α} {γ : Path x y} (hinj : Injective γ)
    {S : Set α} (hS : IsConnected S) (hSsub : S ⊆ range γ) {t₁ t₂ : I}
    (h₁ : γ t₁ ∈ S) (h₂ : γ t₂ ∈ S) : γ '' Icc t₁ t₂ ⊆ S := by
  have hpre : IsConnected (γ ⁻¹' S) :=
    hS.preimage_of_isClosedMap hinj (γ.continuous.isClosedEmbedding hinj).isClosedMap hSsub
  rintro w ⟨t, ht, rfl⟩
  obtain ⟨s, hs, hseq⟩ := (hpre.image _ continuous_subtype_val.continuousOn).Icc_subset
    (mem_image_of_mem _ h₁) (mem_image_of_mem _ h₂) ⟨ht.1, ht.2⟩
  exact (Subtype.ext hseq) ▸ hs

/-- Last exit from `closedBall c rc` and first subsequent entry into `closedBall d rd` along a path
from `a` to `b`, where `a` starts in the first ball and `b` ends in the second. Both parameter sets
are closed and nonempty, so the extrema exist; disjointness of the balls forces the exit time to
precede the entry time and puts both endpoints on the spheres.

The centres may differ from the path endpoints. The proof takes the greatest parameter in the first
closed-ball preimage and the least subsequent parameter in the second; compactness gives both
extrema, and disjointness puts the two parameters in order. -/
lemma exists_lastExit_firstEntry {α : Type*} [PseudoMetricSpace α] {a b c d : α} (γ : Path a b)
    {rc rd : ℝ} (hdisj : Disjoint (closedBall c rc) (closedBall d rd)) (ha : a ∈ closedBall c rc)
    (hb : b ∈ closedBall d rd) : ∃ (t s : I), t < s ∧ dist (γ t) c = rc ∧ dist (γ s) d = rd ∧
    (γ '' Icc t s) ∩ closedBall c rc = {γ t} ∧ (γ '' Icc t s) ∩ closedBall d rd = {γ s} := by
  let Su : Set I := {u | γ u ∈ closedBall c rc}
  have hSu_ne : Su.Nonempty := ⟨0, by simpa [Su, Path.source] using ha⟩
  obtain ⟨t, ht1, ht2⟩ :=
    (isClosed_closedBall.preimage γ.continuous).isCompact.exists_isGreatest hSu_ne
  let Sv : Set I := {u | t ≤ u ∧ γ u ∈ closedBall d rd}
  have hSv_closed : IsClosed Sv := isClosed_Ici.inter (isClosed_closedBall.preimage γ.continuous)
  have hSv_ne : Sv.Nonempty := ⟨1, ⟨t.2.2, by simpa [Path.target] using hb⟩⟩
  obtain ⟨s, hs⟩ := hSv_closed.isCompact.exists_isLeast hSv_ne
  have hts : t < s := hs.1.1.lt_of_ne (hdisj.notMem_of_mem_left ht1 <| · ▸ hs.1.2)
  refine ⟨t, s, hts, ?_, ?_, ?_, ?_⟩
  · have hle : dist (γ t) c ≤ rc := Metric.mem_closedBall.mp ht1
    refine hle.antisymm ?_
    by_contra hlt'
    have hlt : dist (γ t) c < rc := lt_of_not_ge hlt'
    have ht_ne_one : t ≠ 1 := by
      rintro rfl
      exact hdisj.notMem_of_mem_left (γ.target ▸ ht1) hb
    have hcont : Continuous fun u : I ↦ dist (γ u) c := γ.continuous.dist continuous_const
    obtain ⟨δ, δpos, hδ⟩ := continuousAt_iff.mp (hcont.continuousAt (x := t)) (rc - dist (γ t) c)
      (sub_pos.mpr hlt)
    obtain ⟨t0, ht0a, ht0b⟩ := exists_between <|
      lt_min (lt_add_of_pos_right _ (half_pos δpos)) <| unitInterval.lt_one_iff_ne_one.mpr ht_ne_one
    have ht0I : t0 ∈ (I : Set ℝ) :=
      ⟨t.2.1.trans (le_of_lt ht0a), (le_of_lt ht0b).trans (min_le_right _ _)⟩
    set u : I := ⟨t0, ht0I⟩
    have hparamI : dist u t < δ := by
      have habs : dist t0 (t : ℝ) = t0 - t := by
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (le_of_lt ht0a))]
      have : t0 < t + δ / 2 := (lt_min_iff.mp ht0b).1
      change dist (u : ℝ) (t : ℝ) < δ
      linarith
    exact ht0a.not_ge <| show u ≤ t from ht2 <| mem_closedBall.2 (by grind [abs_lt.mp (hδ hparamI)])
  · have hle : dist (γ s) d ≤ rd := Metric.mem_closedBall.mp hs.1.2
    refine le_antisymm hle ?_
    by_contra hlt'
    have hlt : dist (γ s) d < rd := lt_of_not_ge hlt'
    have hcont : Continuous fun u : I ↦ dist (γ u) d := γ.continuous.dist continuous_const
    have hc := hcont.continuousAt (x := s)
    rw [Metric.continuousAt_iff] at hc
    obtain ⟨δ, δpos, hδ⟩ := hc (rd - dist (γ s) d) (sub_pos.mpr hlt)
    have hε : 0 < min (δ / 2) (((s : ℝ) - t) / 2) :=
      lt_min (half_pos δpos) (half_pos (sub_pos.mpr hts))
    set t0 : ℝ := (s : ℝ) - min (δ / 2) (((s : ℝ) - t) / 2)
    have ht0_lt : t0 < s := sub_lt_self _ hε
    have ht0_gt : (t : ℝ) < t0 := by
      have : min (δ / 2) (((s : ℝ) - t) / 2) ≤ ((s : ℝ) - t) / 2 := min_le_right _ _
      linarith
    have ht0I : t0 ∈ (I : Set ℝ) :=
      ⟨t.2.1.trans (le_of_lt ht0_gt), (le_of_lt ht0_lt).trans s.2.2⟩
    set u : I := ⟨t0, ht0I⟩
    have hparamI : dist u s < δ := by
      have habs : dist t0 (s : ℝ) = s - t0 := by
        rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (le_of_lt ht0_lt))]
      have : s - t0 = min (δ / 2) (((s : ℝ) - t) / 2) := by simp [t0]
      change dist (u : ℝ) (s : ℝ) < δ
      calc dist t0 (s : ℝ)
          = min (δ / 2) (((s : ℝ) - t) / 2) := by rw [habs, this]
        _ ≤ δ / 2 := min_le_left _ _
        _ < δ := half_lt_self δpos
    have hclose := hδ hparamI
    have hu_ball : dist (γ u) d < rd := by
      have := abs_lt.mp hclose; linarith
    have hu_mem : u ∈ Sv := ⟨le_of_lt ht0_gt, Metric.mem_closedBall.mpr (le_of_lt hu_ball)⟩
    have : s ≤ u := hs.2 hu_mem
    exact (lt_of_le_of_lt this ht0_lt).false
  · ext z; constructor
    · intro hz
      obtain ⟨⟨u, hu, rfl⟩, hzB⟩ := hz
      have : u ≤ t := ht2 hzB
      have : u = t := le_antisymm this hu.1
      simp [this]
    · intro hz
      rw [hz]
      exact ⟨⟨t, ⟨le_rfl, le_of_lt hts⟩, rfl⟩, ht1⟩
  ext z; constructor
  · intro hz
    obtain ⟨⟨u, hu, rfl⟩, hzB⟩ := hz
    have : s ≤ u := hs.2 ⟨hu.1, hzB⟩
    have : u = s := le_antisymm hu.2 this
    simp [this]
  intro hz
  rw [hz]
  exact ⟨⟨s, ⟨le_of_lt hts, le_rfl⟩, rfl⟩, hs.1.2⟩

end Path

/-! ### The interior of a path

`Path.Interior` is the image of the open parameter interval, with both endpoints omitted. -/

/-- The open image of a path, with both endpoints omitted. -/
def Path.Interior {X : Type*} [TopologicalSpace X] {x y : X} (P : Path x y) : Set X :=
  P '' Ioo (0 : unitInterval) 1

lemma Path.interior_subset_range {X : Type*} [TopologicalSpace X] {x y : X} (P : Path x y) :
    P.Interior ⊆ range P := by
  rintro _ ⟨t, ht, rfl⟩
  exact ⟨t, rfl⟩

lemma Path.mem_range_iff_mem_interior_or_source_or_target {X : Type*} [TopologicalSpace X]
    {x y} (P : Path x y) (z : X) : z ∈ range P ↔ z = x ∨ z = y ∨ z ∈ P.Interior := by
  constructor
  · rintro ⟨t, rfl⟩
    obtain rfl | rfl | ht := eq_zero_or_eq_one_or_mem_Ioo t
    · simp
    · simp
    · exact Or.inr (Or.inr ⟨t, ht, rfl⟩)
  rintro (rfl | rfl | h)
  · exact ⟨0, P.source⟩
  · exact ⟨1, P.target⟩
  · exact P.interior_subset_range h
