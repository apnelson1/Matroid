module

public import Matroid.ForMathlib.Topology.Order
public import Mathlib.Analysis.InnerProductSpace.PiL2 -- inefficient import
public import Mathlib.Topology.Subpath

@[expose] public section

variable {α β : Type*} {a b c x y z w : α} {C L : List α} {S T X Y : Set α} {N : ℕ}

open Set Function TopologicalSpace Topology Metric Nat unitInterval Set.Notation
open scoped Sym2

lemma pathConnectedSpace_Ioo {E} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [ContinuousAdd E] [PartialOrder E] [ContinuousSMul ℝ E] [IsOrderedCancelAddMonoid E]
    [PosSMulStrictMono ℝ E] [DenselyOrdered E] {a b : E} (hab : a < b) :
    PathConnectedSpace <| Ioo a b :=
  isPathConnected_iff_pathConnectedSpace.mp <| (convex_Ioo a b).isPathConnected
  <| Set.nonempty_Ioo.mpr hab

namespace unitInterval
variable {t t₁ t₂ : I}

@[simp] lemma one_le : 1 ≤ t ↔ t = 1 := top_le_iff
@[simp] lemma le_zero : t ≤ 0 ↔ t = 0 := le_bot_iff

@[simp]
lemma val_le_zero_iff : t.val ≤ 0 ↔ t = 0 := by
  simp only [t.prop.left.ge_iff_eq, eq_comm, Icc.coe_eq_zero]

@[simp]
lemma one_le_val_iff : 1 ≤ t.val ↔ t = 1 := by
  simp only [t.prop.right.ge_iff_eq, Icc.coe_eq_one]

lemma Icc_eq_univ : Icc (0 : I) 1 = univ := by
  ext t
  have := mem_univ t
  have := t.prop
  tauto

/-- Every parameter of `I` is an endpoint or lies in its open interior. -/
lemma eq_zero_or_eq_one_or_mem_Ioo (t : I) : t = 0 ∨ t = 1 ∨ t ∈ Ioo (0 : I) 1 :=
  eq_endpoints_or_mem_Ioo_of_mem_Icc (Icc_eq_univ ▸ mem_univ t)

instance : ContinuousMul I := submonoid.continuousMul
instance : PathConnectedSpace I :=
  isPathConnected_iff_pathConnectedSpace.mp <| (convex_Icc 0 1).isPathConnected ⟨0, by simp⟩
instance : LocallyPathConnectedSpace I := (convex_Icc 0 1).locallyPathConnectedSpace

/-- A parameter is interior exactly when it is neither endpoint. -/
lemma mem_Ioo_iff : t ∈ Ioo (0 : I) 1 ↔ t ≠ 0 ∧ t ≠ 1 := by
  rw [mem_Ioo, unitInterval.pos_iff_ne_zero, unitInterval.lt_one_iff_ne_one]

@[simp]
lemma symm_mem_Ioo_iff : σ t ∈ Ioo (0 : I) 1 ↔ t ∈ Ioo (0 : I) 1 := by
  rw [mem_Ioo_iff, mem_Ioo_iff, ne_eq, ne_eq, ne_eq, ne_eq, symm_eq_zero, symm_eq_one, and_comm]

lemma closure_Ioo_zero_one : (closure <| Ioo (0 : I) 1) = univ := by
  simp [eq_univ_iff_forall, le_one']

/-- Every nonempty open subinterval of the unit interval is path-connected, by transferring
path-connectedness of the corresponding real interval to the subtype. -/
lemma isPathConnected_Ioo {a b : I} (hab : a < b) : IsPathConnected <| Ioo a b :=
  ((convex_Ioo (a : ℝ) (b : ℝ)).isPathConnected
    (nonempty_Ioo.mpr (Subtype.coe_lt_coe.mpr hab))).preimage_coe
    (fun _ ht ↦ ⟨a.prop.left.trans ht.left.le, ht.right.le.trans b.prop.right⟩)

noncomputable def squishLeft : I → I :=
  fun t ↦ ⟨(t : ℝ) / 2, by constructor <;> nlinarith [t.prop.left, t.prop.right]⟩

lemma continuous_squishLeft : Continuous squishLeft :=
  Continuous.subtype_mk (continuous_subtype_val.div_const 2) _

lemma strictMono_squishLeft : StrictMono squishLeft :=
  fun _ _ h ↦ div_lt_div_of_pos_right h zero_lt_two

@[simp]
lemma squishLeft_zero : squishLeft 0 = 0 := by
  simp [squishLeft]

lemma squishLeft_injective : Injective squishLeft :=
  strictMono_squishLeft.injective

@[simp]
lemma squishLeft_eq_zero_iff : squishLeft t = 0 ↔ t = 0 :=
  ⟨fun h ↦ squishLeft_injective (show squishLeft t = squishLeft 0 by rw [h, squishLeft_zero]),
    fun h ↦ h ▸squishLeft_zero⟩

noncomputable def squishRight : I → I :=
  fun t ↦ ⟨((t : ℝ) + 1) / 2, by constructor <;> nlinarith [t.prop.left, t.prop.right]⟩

lemma continuous_squishRight : Continuous squishRight :=
  Continuous.subtype_mk ((continuous_subtype_val.add continuous_const).div_const 2) _

lemma strictMono_squishRight : StrictMono squishRight :=
  fun _ _ h ↦ div_lt_div_of_pos_right (add_lt_add_left (Subtype.coe_lt_coe.mpr h) 1) zero_lt_two

@[simp]
lemma squishRight_one : squishRight 1 = 1 := by
  simp [squishRight]

lemma squishRight_eq_one_iff : squishRight t = 1 ↔ t = 1 :=
  ⟨fun h ↦ strictMono_squishRight.injective (h.trans squishRight_one.symm),
    fun h ↦ h ▸ squishRight_one⟩

noncomputable def half : I := ⟨2⁻¹, by constructor <;> linarith⟩

@[simp]
lemma squishLeft_le_half (t) : squishLeft t ≤ half := by
  simp only [half, squishLeft, ← Subtype.coe_le_coe]
  linarith [t.prop.right]

@[simp]
lemma half_le_squishRight (t) : half ≤ squishRight t := by
  simp only [half, squishRight, ← Subtype.coe_le_coe]
  linarith [t.prop.left]

@[simp]
lemma squishLeft_one : squishLeft 1 = half := by
  simp [half, squishLeft]

@[simp]
lemma squishRight_zero : squishRight 0 = half := by
  simp [half, squishRight]

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

/-- `squishLeft` lands in the interior exactly when it is not squishing the left endpoint;
the upper bound is automatic, since `squishLeft` never exceeds `half`. -/
lemma squishLeft_mem_Ioo_iff : squishLeft t ∈ Ioo (0 : I) 1 ↔ t ≠ 0 := by
  rw [mem_Ioo, and_iff_left <| (squishLeft_le_half t).trans_lt half_lt_one,
    unitInterval.pos_iff_ne_zero, ne_eq, ne_eq, squishLeft_eq_zero_iff]

/-- `squishRight` lands in the interior exactly when it is not squishing the right endpoint. -/
lemma squishRight_mem_Ioo_iff : squishRight t ∈ Ioo (0 : I) 1 ↔ t ≠ 1 := by
  rw [mem_Ioo, and_iff_right <| zero_lt_half.trans_le <| half_le_squishRight t,
    unitInterval.lt_one_iff_ne_one, ne_eq, ne_eq, squishRight_eq_one_iff]

/-- Every interior parameter is `squishLeft` of an interior parameter, the midpoint, or
`squishRight` of an interior parameter.  This is the trichotomy that `Path.trans` induces on its
parameter.  Like `eq_zero_or_eq_one_or_mem_Ioo` it is a splitter, so it carries no attribute and
is passed to `grind` explicitly where it is wanted. -/
lemma mem_Ioo_iff_exists_squishLeft_or_eq_half_or_exists_squishRight :
    t ∈ Ioo (0 : I) 1 ↔ (∃ s ∈ Ioo (0 : I) 1, squishLeft s = t) ∨ t = half ∨
      (∃ s ∈ Ioo (0 : I) 1, squishRight s = t) := by
  refine ⟨fun ht ↦ ?_, ?_⟩
  · unfold squishLeft squishRight half
    simp_rw [mem_Ioo_iff]
    obtain h | h | h := lt_trichotomy (t : ℝ) (1 / 2)
    · refine Or.inl ⟨⟨2 * t.val, (mul_pos_mem_iff zero_lt_two).mpr ⟨t.prop.left, h.le⟩⟩, ?_, ?_⟩
      · constructor <;> simp only [ne_eq, Subtype.ext_iff, Icc.coe_zero, Icc.coe_one]
        <;> linarith [coe_pos.mpr ht.left]
      exact Subtype.ext (by ring)
    · exact Or.inr <| Or.inl <| Subtype.ext (by linarith)
    refine Or.inr <|
      Or.inr ⟨⟨2 * t.val - 1, two_mul_sub_one_mem_iff.mpr ⟨h.le, t.prop.right⟩⟩, ?_, ?_⟩
    · constructor <;> simp only [ne_eq, Subtype.ext_iff, Icc.coe_zero, Icc.coe_one]
      <;> linarith [coe_lt_one.mpr ht.right]
    exact Subtype.ext (by ring)
  rintro (⟨s, hs, rfl⟩ | rfl | ⟨s, hs, rfl⟩)
  · exact squishLeft_mem_Ioo_iff.2 (mem_Ioo_iff.1 hs).left
  · exact ⟨zero_lt_half, half_lt_one⟩
  exact squishRight_mem_Ioo_iff.2 (mem_Ioo_iff.1 hs).right

variable (i j : I)

lemma squishLeft_Icc : squishLeft '' Icc i j = (Icc (squishLeft i) <| squishLeft j) :=
  continuous_squishLeft.image_Icc_of_strictMono strictMono_squishLeft

lemma squishRight_Icc : squishRight '' Icc i j = (Icc (squishRight i) <| squishRight j) :=
  continuous_squishRight.image_Icc_of_strictMono strictMono_squishRight

lemma squishLeft_Ioo : squishLeft '' Ioo i j = Ioo (squishLeft i) (squishLeft j) :=
  continuous_squishLeft.image_Ioo_of_strictMono strictMono_squishLeft

lemma squishRight_Ioo : squishRight '' Ioo i j = Ioo (squishRight i) (squishRight j) :=
  continuous_squishRight.image_Ioo_of_strictMono strictMono_squishRight

end unitInterval

/-- Any subset of the unit interval containing its relative interior is open. -/
lemma isOpen_of_Ioo_subset {U : Set I} (h : Ioo (0 : I) 1 ⊆ U) : IsOpen U := by
  rw [← isClosed_compl_iff]
  refine finite_singleton 1 |>.insert 0 |>.subset ?_ |>.isClosed
  refine fun t ht ↦ by_contra fun hne ↦ ht <| h ?_
  simpa [← unitInterval.mem_Ioo_iff] using hne

namespace Path

variable [TopologicalSpace α] {P : Path x y} {Q : Path y z} {γ : Path x y} {η : Path a b}

lemma range_isPathConnected (P : Path x y) : IsPathConnected <| range P :=
  image_univ ▸ isPathConnected_univ.image P.continuous

@[simp]
lemma refl_not_injective (x : α) : ¬ Injective (refl x) := by
  intro h
  simpa using h (a₁ := 0) (a₂ := 1) (by simp)

@[simp]
lemma segment_injective [AddCommGroup α] [Module ℝ α] [ContinuousAdd α]
    [ContinuousSMul ℝ α] (x y : α) : Injective (Path.segment x y) ↔ x ≠ y := by
  refine ⟨fun h => ?_, fun h s t hst => ?_⟩
  · rintro rfl
    simp at h
  simpa [h, Subtype.val_inj] using hst

@[simp]
lemma eq_zero_iff_of_injective (h : Injective P) (t : I) : P t = x ↔ t = 0 := by
  nth_rw 3 [← P.source]
  rw [h.eq_iff]

@[simp]
lemma eq_one_iff_of_injective (h : Injective P) (t : I) : P t = y ↔ t = 1 := by
  nth_rw 3 [← P.target]
  rw [h.eq_iff]

lemma trans_apply_ite_lt (i : I) : (P.trans Q) i = if h : i.val < 1/2 then
    P ⟨2 * i.val, (mul_pos_mem_iff zero_lt_two).2 ⟨i.prop.left, h.le⟩⟩ else
    Q ⟨2 * i.val - 1, two_mul_sub_one_mem_iff.2 ⟨(not_lt.1 h), i.prop.right⟩⟩ := by
  obtain hi | hi | hi := lt_trichotomy i.val 2⁻¹
  · simp [hi.le, hi, trans_apply]
  · simp [trans_apply, hi]
  simp [hi.not_ge, hi.not_gt, trans_apply]

lemma injOn_ico_iff_injOn_ioc (P : Path x x) : InjOn P (Ico 0 1) ↔ InjOn P (Ioc 0 1) := by
  rw [← Ioo_insert_left (show (0 : I) < 1 from zero_lt_one),
    ← Ioo_insert_right (show (0 : I) < 1 from zero_lt_one),
    injOn_insert (by simp), injOn_insert (by simp), P.source, P.target]

lemma sSup_notMem (P : Path x y) (hS : IsOpen S) (hy : y ∉ S) : P (sSup <| P ⁻¹' S) ∉ S := by
  by_cases h : sSup (P ⁻¹' S) = 1
  · simpa [h]
  replace h : sSup (P ⁻¹' S) < 1 := by
    contrapose! h
    exact unitInterval.one_le.mp h
  exact (P.continuous.isOpen_preimage _ hS).sSup_notMem ⟨1, h⟩

lemma sInf_notMem (P : Path x y) (hS : IsOpen S) (hx : x ∉ S) : P (sInf <| P ⁻¹' S) ∉ S := by
  by_cases h : sInf (P ⁻¹' S) = 0
  · simpa [h]
  replace h : 0 < sInf (P ⁻¹' S) := by
    contrapose! h
    exact unitInterval.le_zero.mp h
  exact (P.continuous.isOpen_preimage _ hS).sInf_notMem ⟨0, h⟩

lemma trans_squishLeft (i : I) : P.trans Q (squishLeft i) = P i := by
  simp [trans, squishLeft, comp_apply, (show i / 2 ≤ (2 : ℝ)⁻¹ by linarith [i.prop.right])]
  rw [mul_div_cancel₀ _ (by simp)]
  exact extend_extends' P i

lemma trans_squishRight (i : I) : P.trans Q (squishRight i) = Q i := by
  obtain rfl | ht0 := eq_or_ne i 0
  · simp [trans, squishRight]
  replace ht0 : i.val ≠ 0 := coe_ne_zero.mpr ht0
  simp only [trans, one_div, coe_mk', ContinuousMap.coe_mk, comp_apply, squishRight,
    (show ¬ ((↑i + 1) / 2 ≤ (2 : ℝ)⁻¹) by linarith [i.prop.left.lt_of_ne' ht0]), ↓reduceIte]
  rw [mul_div_cancel₀ _ (by simp), add_sub_cancel_right]
  exact extend_extends' Q i

lemma trans_injective_iff : Injective (P.trans Q) ↔
    Injective P ∧ Injective Q ∧ (Disjoint (range P \ {y}) <| range Q) := by
  refine ⟨fun h => ⟨fun s t hst ↦ ?_, fun s t hst ↦ ?_, ?_⟩, fun ⟨hP, hQ, hdj⟩ t₁ t₂ ht => ?_⟩
  · have h1 : P.trans Q (squishLeft s) = P.trans Q (squishLeft t) := by
      simpa [trans_squishLeft] using hst
    exact squishLeft_injective <| h h1
  · refine strictMono_squishRight.injective <| h ?_
    simpa [trans_squishRight] using hst
  · by_contra! hdj
    rw [not_disjoint_iff] at hdj
    obtain ⟨-, ⟨⟨t1, hPQ⟩, hay⟩, t2, rfl⟩ := hdj
    rw [← trans_squishRight t2, ← trans_squishLeft t1] at hPQ
    replace hPQ : (t1 : ℝ) / 2 = (t2 + 1) / 2 := by
      simpa [squishLeft, squishRight, Subtype.ext_iff] using h hPQ
    obtain rfl : t2 = 0 := by
      rw [← Subtype.coe_inj, Icc.coe_zero]
      linarith [hPQ, t1.prop.right, t2.prop.left]
    simp at hay
  by_cases ht₁ : (t₁ : ℝ) ≤ 2⁻¹ <;> by_cases ht₂ : (t₂ : ℝ) ≤ 2⁻¹ <;> simp only [trans_apply,
    one_div, ht₁, ↓reduceDIte, ht₂] at ht
  · simpa [Subtype.val_inj] using hP ht
  on_goal 3 => simpa [Subtype.val_inj] using hQ ht
  all_goals
  have := ht ▸ (hdj.notMem_of_mem_right (a := Q _) (by simp))
  simp only [mem_sdiff, mem_range, exists_apply_eq_apply, mem_singleton_iff,
    eq_one_iff_of_injective hP, Subtype.ext_iff, Icc.coe_one, true_and, Decidable.not_not] at this
  simp only [this, Icc.mk_one, Path.target, eq_comm (a := y), Q.eq_zero_iff_of_injective hQ,
    Subtype.ext_iff, Icc.coe_zero] at ht
  linarith

lemma injective_left_iff_trans_injOn (P : Path x y) (Q : Path y z) :
    InjOn (P.trans Q) (Icc 0 half) ↔ Injective P := by
  rw [← squishLeft_zero, ← squishLeft_one, ← squishLeft_Icc, ← squishLeft_injective.injOn.comp_iff]
  simp only [comp_def, trans_squishLeft, unitInterval.Icc_eq_univ, injOn_univ]

lemma injective_right_iff_trans_injOn (P : Path x y) (Q : Path y z) :
    InjOn (P.trans Q) (Icc half 1) ↔ Injective Q := by
  rw [← squishRight_zero, ← squishRight_one, ← squishRight_Icc,
    ← strictMono_squishRight.injective.injOn.comp_iff]
  simp only [comp_def, trans_squishRight, unitInterval.Icc_eq_univ, injOn_univ]

lemma trans_injOn_ico_iff {Q : Path y x} : InjOn (P.trans Q) (Ico 0 1) ↔
    Injective P ∧ Injective Q ∧ Disjoint (range P \ {y}) (range Q \ {x}) := by
  refine
    ⟨fun h => ⟨fun s t hst ↦ ?_, fun s t hst ↦ ?_, ?_⟩, fun ⟨hP, hQ, hdj⟩ t₁ ht₁ t₂ ht₂ ht => ?_⟩
  · exact (P.injective_left_iff_trans_injOn Q).mp (h.mono <| Icc_subset_Ico_right half_lt_one)
    |>.eq_iff.mp hst
  · rw [injOn_ico_iff_injOn_ioc] at h
    replace h : InjOn (⇑(P.trans Q)) <| Icc half 1 :=
      h.mono <| (Icc_subset_Ioc_iff le_one').mpr ⟨zero_lt_half, le_rfl⟩
    exact ((P.injective_right_iff_trans_injOn Q).mp h).eq_iff.mp hst
  · by_contra! hdj
    rw [not_disjoint_iff] at hdj
    obtain ⟨-, ⟨⟨t1, hPQ⟩, hay⟩, ⟨t2, rfl⟩, hax⟩ := hdj
    rw [← trans_squishRight t2, ← trans_squishLeft t1] at hPQ
    have ht2 : t2 < 1 := by
      by_contra! ht2
      obtain rfl := ht2.antisymm t2.prop.right
      simp at hax
    replace hPQ :=
      h (show squishLeft t1 ∈ Ico 0 1 by simpa using squishLeft_le_half t1 |>.trans_lt half_lt_one)
      (show squishRight t2 ∈ Ico 0 1 by simpa using squishRight_lt_one ht2) hPQ
    replace hPQ : (t1 : ℝ) / 2 = (t2 + 1) / 2 := by
      simpa [squishLeft, squishRight, Subtype.ext_iff] using hPQ
    obtain rfl : t2 = 0 := by
      rw [← Subtype.coe_inj, Icc.coe_zero]
      linarith [hPQ, t1.prop.right, t2.prop.left]
    simp at hay
  obtain ht₁1 : (t₁ : ℝ) < 1 := ht₁.right
  obtain ht₂1 : (t₂ : ℝ) < 1 := ht₂.right
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

section

/-- A loop is a *simple loop* if it does not visit any point twice, except that it ends where it
started. -/
def IsSimpleLoop (P : Path x x) : Prop := InjOn P <| Ico 0 1

variable {P : Path x x}

lemma isSimpleLoop_iff_injOn_ioc : P.IsSimpleLoop ↔ InjOn P (Ioc 0 1) :=
  P.injOn_ico_iff_injOn_ioc

lemma IsSimpleLoop.injOn_ioo (h : P.IsSimpleLoop) : InjOn P <| Ioo 0 1 := h.mono Ioo_subset_Ico_self

@[simp] lemma not_isSimpleLoop_refl : ¬ (Path.refl x).IsSimpleLoop := by
  intro h
  replace h : 0 = half := h (x₁ := 0) (x₂ := half) (by simp) (by simp) (by rfl)
  exact half_ne_zero h.symm

end

/-! ### Connected subsets of an injective path -/

/-- An injective path is an embedding if its range is Hausdorff. -/
lemma isEmbedding_of_injective [T2Space ↥(range γ)] (hinj : Injective γ) : IsEmbedding γ :=
  IsEmbedding.subtypeVal.comp <| (γ.continuous.subtype_mk mem_range_self).isClosedEmbedding
    (fun _ _ h ↦ hinj (congrArg Subtype.val h)) |>.isEmbedding

/-- On an injectively parametrised path, a connected piece of the image containing `γ t₁` and
`γ t₂` contains the whole parameter interval between them. -/
@[grind →]
lemma image_Icc_subset_of_isConnected [T2Space α] (hinj : Injective γ) (hS : IsConnected S)
    (hSsub : S ⊆ range γ) {t₁ t₂ : I} (h₁ : γ t₁ ∈ S) (h₂ : γ t₂ ∈ S) : γ '' Icc t₁ t₂ ⊆ S :=
  (isEmbedding_of_injective hinj).image_Icc_subset_of_isPreconnected hSsub hS.isPreconnected h₁ h₂

/-- A path in the range of an injective path fills the interval between the infimum and
supremum of the parameters it visits. The contained path may have arbitrary endpoints
and need not be injective. -/
theorem range_eq_image_Icc_of_subset_injective [T2Space ↥(range γ)] (hinj : Injective γ)
    (hsub : range η ⊆ range γ) : range η = γ '' Icc (sInf (γ ⁻¹' range η)) (sSup (γ ⁻¹' range η)) :=
  (isEmbedding_of_injective hinj).eq_image_Icc_of_isConnected_isCompact hsub
    η.range_isPathConnected.isConnected (isCompact_range η.continuous)

theorem range_eq_of_subset_injective {W : Type*} [TopologicalSpace W]
    {x y : W} {γ η : Path x y} (hinj : Injective γ) (hsub : range η ⊆ range γ)
    [T2Space ↥(range γ)] : range η = range γ := by
  have hfull := (isEmbedding_of_injective hinj).image_Icc_subset_of_isPreconnected
    hsub η.range_isPathConnected.isConnected.isPreconnected (a := 0) (b := 1)
    (γ.source.symm ▸ η.source_mem_range) (γ.target.symm ▸ η.target_mem_range)
  rw [unitInterval.Icc_eq_univ, image_univ] at hfull
  exact hsub.antisymm hfull

/-- An injective path in a linearly ordered space fills the unordered interval between
its endpoints. -/
theorem range_eq_uIcc_of_injective {L : Type*} [LinearOrder L] [TopologicalSpace L]
    [OrderTopology L] {a b : L} {γ : Path a b} (hinj : Injective γ) : range γ = uIcc a b := by
  have h : γ '' uIcc (0 : I) 1 = uIcc (γ 0) (γ 1) := by
    obtain hmono | hanti := γ.continuous.strictMono_of_inj hinj
    · exact γ.continuous.continuousOn.image_uIcc_of_monotoneOn (hmono.monotone.monotoneOn _)
    · exact γ.continuous.continuousOn.image_uIcc_of_antitoneOn (hanti.antitone.antitoneOn _)
  simpa only [uIcc_of_le (show (0 : I) ≤ 1 from zero_le_one), unitInterval.Icc_eq_univ,
    image_univ, Path.source, Path.target] using h

/-- An injective path in an embedded linear order fills the image of the unordered interval
between its endpoint coordinates. -/
theorem range_eq_image_uIcc_of_isEmbedding {L : Type*} [LinearOrder L] [TopologicalSpace L]
    [OrderTopology L] {f : L → α} {a b : L} {γ : Path (f a) (f b)}
    (hf : IsEmbedding f) (hinj : Injective γ) (hsub : range γ ⊆ range f) :
    range γ = f '' uIcc a b := by
  let δ : Path a b := {
    toFun := fun t ↦ hf.toHomeomorph.symm ⟨γ t, hsub (mem_range_self t)⟩
    continuous_toFun := hf.toHomeomorph.symm.continuous.comp (γ.continuous.subtype_mk _)
    source' := by simp only [γ.source, hf.toHomeomorph_symm_apply]
    target' := by simp only [γ.target, hf.toHomeomorph_symm_apply] }
  have hδ (t : I) : f (δ t) = γ t :=
    congrArg Subtype.val (hf.toHomeomorph.apply_symm_apply ⟨γ t, hsub (mem_range_self t)⟩)
  rw [← δ.range_eq_uIcc_of_injective (fun s t ↦ by grind), ← range_comp]
  exact congrArg range (funext hδ).symm

/-- An injective path contained in another injective path fills the subarc between its
endpoint parameters, in either orientation. -/
theorem range_eq_image_uIcc_of_subset_injective {s t : I} {η : Path (γ s) (γ t)}
    [T2Space ↥(range γ)] (hγ : Injective γ) (hη : Injective η) (hsub : range η ⊆ range γ) :
    range η = γ '' uIcc s t :=
  range_eq_image_uIcc_of_isEmbedding (isEmbedding_of_injective hγ) hη hsub

theorem range_eq_segment_of_subset {W : Type*} [TopologicalSpace W] [AddCommGroup W] [Module ℝ W]
    [ContinuousSMul ℝ W] [ContinuousAdd W] {x y a b : W} {γ : Path x y} (hinj : Injective γ)
    (hsub : range γ ⊆ segment ℝ a b) [T2Space ↥(segment ℝ a b)] : range γ = segment ℝ x y := by
  have hab : a ≠ b := by
    rintro rfl
    obtain rfl := segment_same ℝ a ▸ hsub (mem_range_self (1 : unitInterval))
    exact zero_ne_one <| hinj (segment_same ℝ (γ 1) ▸ hsub (mem_range_self 0) : γ 0 ∈ {γ 1})
  rw [← Path.range_segment a b] at hsub
  have : T2Space ↥(range (Path.segment a b)) := by rwa [Path.range_segment]
  obtain ⟨s, rfl⟩ := hsub γ.source_mem_range
  obtain ⟨t, rfl⟩ := hsub γ.target_mem_range
  simp_rw [range_eq_image_uIcc_of_subset_injective (Path.segment_injective_of_ne hab) hinj hsub,
    Path.segment_apply]
  rw [← image_image, image_subtype_val_uIcc, ← segment_eq_uIcc, image_segment]

/-! ### Cutting a path between disjoint closed sets -/

/-- A path from one closed set to a disjoint closed set has a subpath between their frontiers
which meets each set only at the corresponding endpoint. The parameters are obtained by taking
the last exit from the first set and the first subsequent entry into the second. -/
lemma exists_lastExit_firstEntry_of_isClosed (γ : Path a b) (hS : IsClosed S) (hT : IsClosed T)
    (hdisj : Disjoint S T) (ha : a ∈ S) (hb : b ∈ T) :
    ∃ (t s : I), t < s ∧ γ t ∈ frontier S ∧ γ s ∈ frontier T ∧
      (γ '' Icc t s) ∩ S = {γ t} ∧ (γ '' Icc t s) ∩ T = {γ s} := by
  obtain ⟨t, ht1, ht2⟩ := (hS.preimage γ.continuous).isCompact.exists_isGreatest
    (show (γ ⁻¹' S).Nonempty from ⟨0, by simpa using ha⟩)
  obtain ⟨s, hs⟩ := (isClosed_Ici.inter (hT.preimage γ.continuous)).isCompact.exists_isLeast
    (show (Ici t ∩ γ ⁻¹' T).Nonempty from ⟨1, t.2.2, by simpa using hb⟩)
  have hts : t < s := lt_of_le_of_ne hs.1.1 (hdisj.notMem_of_mem_left ht1 <| · ▸ hs.1.2)
  refine ⟨t, s, hts, ?_, ?_, ?_, ?_⟩
  · rw [mem_frontier_iff_notMem_interior (s := S) ht1]
    intro ht
    obtain ⟨u, hu, htu⟩ := nonempty_nhds_inter_Ioi
      ((isOpen_interior.preimage γ.continuous).mem_nhds ht) hts.not_isMax
    exact htu.not_ge (ht2 (interior_subset (s := S) hu))
  · rw [mem_frontier_iff_notMem_interior (s := T) hs.1.2]
    intro hsint
    have hnhds : (γ ⁻¹' interior T) ∩ Ioi t ∈ 𝓝 s :=
      ((isOpen_interior.preimage γ.continuous).inter isOpen_Ioi).mem_nhds ⟨hsint, hts⟩
    obtain ⟨u, ⟨huT, htu⟩, hus⟩ := nonempty_nhds_inter_Iio hnhds hts.not_isMin
    exact hus.not_ge (hs.2 ⟨htu.le, interior_subset (s := T) huT⟩)
  · ext z
    constructor
    · rintro ⟨⟨u, hu, rfl⟩, huS⟩
      obtain rfl := (ht2 huS).antisymm hu.1
      rfl
    rintro rfl
    exact ⟨⟨t, ⟨le_rfl, hts.le⟩, rfl⟩, ht1⟩
  ext z
  constructor
  · rintro ⟨⟨u, hu, rfl⟩, huT⟩
    obtain rfl := hu.2.antisymm (hs.2 ⟨hu.1, huT⟩)
    rfl
  rintro rfl
  exact ⟨⟨s, ⟨hts.le, le_rfl⟩, rfl⟩, hs.1.2⟩

/-- Last exit from one closed ball and first subsequent entry into a disjoint closed ball.
The cut points lie on the corresponding spheres, and the subpath meets each ball only at its
corresponding endpoint. The centres may differ from the path endpoints. -/
lemma exists_lastExit_firstEntry {α : Type*} [PseudoMetricSpace α] {a b c d : α} (γ : Path a b)
    {rc rd : ℝ} (hdisj : Disjoint (closedBall c rc) (closedBall d rd)) (ha : a ∈ closedBall c rc)
    (hb : b ∈ closedBall d rd) : ∃ (t s : I), t < s ∧ dist (γ t) c = rc ∧ dist (γ s) d = rd ∧
    (γ '' Icc t s) ∩ closedBall c rc = {γ t} ∧ (γ '' Icc t s) ∩ closedBall d rd = {γ s} := by
  obtain ⟨t, s, hts, ht, hs, hS, hT⟩ :=
    γ.exists_lastExit_firstEntry_of_isClosed isClosed_closedBall isClosed_closedBall hdisj ha hb
  exact ⟨t, s, hts, frontier_closedBall_subset_sphere ht,
    frontier_closedBall_subset_sphere hs, hS, hT⟩

/-! ### The interior of a path

`Path.Interior` is the image of the open parameter interval. -/

lemma trans_apply_half : (P.trans Q) half = y := by
  rw [← squishLeft_one, trans_squishLeft, P.target]

/-- The image of the open parameter interval. -/
def Interior (P : Path x y) : Set α :=
  P '' Ioo (0 : unitInterval) 1

lemma interior_nonempty (P : Path x y) : P.Interior.Nonempty :=
  (nonempty_Ioo.2 (zero_lt_one : (0 : I) < 1)).image P

lemma isPathConnected_interior (P : Path x y) : IsPathConnected P.Interior :=
  (unitInterval.isPathConnected_Ioo zero_lt_one).image P.continuous

lemma interior_segment [AddCommGroup α] [Module ℝ α] [ContinuousAdd α] [ContinuousSMul ℝ α]
    (a b : α) : (Path.segment a b).Interior = openSegment ℝ a b := by
  change (fun t : I ↦ AffineMap.lineMap a b (t : ℝ)) '' Ioo 0 1 = _
  rw [← image_image, image_subtype_val_Ioo, openSegment_eq_image_lineMap]
  rfl

lemma range_subset_closure_interior (P : Path x y) : range P ⊆ closure P.Interior := by
  rintro z ⟨i, rfl⟩
  refine ((image_closure_subset_closure_image P.continuous ⟨i, ?_, rfl⟩))
  grind [unitInterval.closure_Ioo_zero_one]

lemma interior_subset_range (P : Path x y) : P.Interior ⊆ range P := by
  rintro _ ⟨t, ht, rfl⟩
  exact ⟨t, rfl⟩

lemma mem_range_iff_mem_interior_or_source_or_target (P : Path x y) (z : α) :
    z ∈ range P ↔ z = x ∨ z = y ∨ z ∈ P.Interior := by
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

/-- If neither endpoint is visited in the open parameter interval, deleting the endpoints from
the range leaves exactly the interior. -/
lemma range_diff_endpoints (hx : x ∉ P.Interior) (hy : y ∉ P.Interior) :
    range P \ {x, y} = P.Interior := by
  ext z
  simp only [mem_sdiff, mem_range_iff_mem_interior_or_source_or_target, mem_insert_iff,
    mem_singleton_iff]
  grind

/-- Recasting the endpoints of a path does not move its interior. -/
lemma cast_interior {x' y' : α} (P : Path x y) (h1 : x' = x) (h2 : y' = y) :
    (P.cast h1 h2).Interior = P.Interior := by
  simp [Interior, Path.cast_coe]

/-- Reversing a path does not move its interior. -/
@[simp]
lemma symm_interior (P : Path x y) : P.symm.Interior = P.Interior := by
  ext z
  simp only [Interior, mem_image, Path.symm_apply]
  refine ⟨fun ⟨t, ht, h⟩ ↦ ⟨σ t, symm_mem_Ioo_iff.2 ht, h⟩, fun ⟨t, ht, h⟩ ↦ ⟨σ t, ?_, ?_⟩⟩
  · exact symm_mem_Ioo_iff.2 ht
  · simpa only [Function.comp_apply, unitInterval.symm_symm] using h

/-- The interior of a concatenation is the two interiors together with the junction point. -/
lemma trans_interior : (P.trans Q).Interior = P.Interior ∪ {y} ∪ Q.Interior := by
  have hparam : Ioo (0 : I) 1 =
      squishLeft '' Ioo 0 1 ∪ {half} ∪ squishRight '' Ioo 0 1 := by
    ext t
    simpa only [mem_union, mem_image, mem_singleton_iff, or_assoc] using
      (mem_Ioo_iff_exists_squishLeft_or_eq_half_or_exists_squishRight (t := t))
  change (P.trans Q) '' _ = _
  rw [hparam, image_union, image_union, image_singleton, trans_apply_half]
  simp only [image_image, trans_squishLeft, trans_squishRight, Interior]

/-- A concatenation is injective on the open parameter interval exactly when both halves are, the
two interiors are disjoint, and neither contains the junction point.  Equivalently, the union
displayed by `Path.trans_interior` is a disjoint one. -/
lemma trans_injOn_ioo_iff : InjOn (P.trans Q) (Ioo 0 1) ↔ InjOn P (Ioo 0 1) ∧ InjOn Q (Ioo 0 1) ∧
      y ∉ P.Interior ∧ y ∉ Q.Interior ∧ Disjoint P.Interior Q.Interior := by
  have hparam : Ioo (0 : I) 1 = insert half (squishLeft '' Ioo 0 1 ∪ squishRight '' Ioo 0 1) := by
    ext t
    simpa only [mem_insert_iff, mem_union, mem_image, or_left_comm] using
      (mem_Ioo_iff_exists_squishLeft_or_eq_half_or_exists_squishRight (t := t))
  have hhalf : half ∉ squishLeft '' Ioo (0 : I) 1 ∪ squishRight '' Ioo (0 : I) 1 := by
    simp [squishLeft_Ioo, squishRight_Ioo]
  have hdisj : Disjoint (squishLeft '' Ioo (0 : I) 1) (squishRight '' Ioo (0 : I) 1) := by
    simp only [squishLeft_Ioo, squishRight_Ioo, squishLeft_zero, squishLeft_one,
      squishRight_zero, squishRight_one]
    exact disjoint_left.mpr fun _ ht hs ↦ ht.2.not_gt hs.1
  conv_lhs => rw [hparam, injOn_insert hhalf, injOn_union hdisj]
  simp only [← squishLeft_injective.injOn.comp_iff, comp_def, trans_squishLeft,
    ← strictMono_squishRight.injective.injOn.comp_iff, trans_squishRight, forall_mem_image,
    image_union, image_image, trans_apply_half, mem_union, not_or, Interior, disjoint_iff_forall_ne]
  tauto

open Classical in
/-- Reorient a path to a prescribed ordering of the same unordered pair of endpoints. -/
noncomputable def reorient (γ : Path a b) (h : s(x, y) = s(a, b)) : Path x y :=
  if hx : x = a ∧ y = b then γ.cast hx.1 hx.2
  else
    have h' : x = b ∧ y = a := (Sym2.eq_iff.mp h).resolve_left hx
    γ.symm.cast h'.1 h'.2

@[simp]
lemma range_reorient (γ : Path a b) (h : s(x, y) = s(a, b)) : range (γ.reorient h) = range γ := by
  rw [reorient]
  split_ifs <;> simp

@[simp]
lemma reorient_interior (γ : Path a b) (h : s(x, y) = s(a, b)) :
    (γ.reorient h).Interior = γ.Interior := by
  rw [reorient]
  split_ifs <;> simp only [cast_interior, symm_interior]

lemma injOn_reorient {γ : Path a b} (h : s(x, y) = s(a, b))
    (hγ : InjOn γ (Ioo (0 : I) 1)) : InjOn (γ.reorient h) (Ioo (0 : I) 1) := by
  rw [reorient]
  split_ifs
  · exact hγ
  intro s hs t ht hst
  simpa using congrArg σ <| hγ (symm_mem_Ioo_iff.2 hs) (symm_mem_Ioo_iff.2 ht) hst

/-! ### Subpaths and halves -/

variable {s t : I}

/-- A subpath is injective exactly when its parameters are distinct and the original path is
injective on the interval between them. -/
lemma injective_subpath_iff : Injective (γ.subpath s t) ↔ s ≠ t ∧ InjOn γ (uIcc s t) := by
  refine ⟨fun h ↦ ⟨?_, range_subpathAux .. ▸ Injective.injOn_range h⟩, fun ⟨hst, hγ⟩ u v huv ↦ ?_⟩
  · rintro rfl
    exact refl_not_injective _ (subpath_self γ s ▸ h)
  have hmem (r : I) : Icc.convexComb s t r ∈ uIcc s t :=
    range_subpathAux s t ▸ mem_range_self r
  refine segment_injective_of_ne (Subtype.coe_injective.ne hst) ?_
  simpa only [segment_apply, AffineMap.lineMap_apply_module, smul_eq_mul,
    Icc.coe_convexComb] using congrArg Subtype.val (hγ (hmem u) (hmem v) huv)

/-- An injective path has injective subpaths between distinct parameters. -/
lemma injective_subpath (hγ : Injective γ) (hst : s ≠ t) : Injective (γ.subpath s t) :=
  injective_subpath_iff.mpr ⟨hst, hγ.injOn⟩

/-- The subpath from the source to the midpoint. -/
noncomputable def firstHalf (γ : Path x y) : Path x (γ half) :=
  (γ.subpath 0 half).cast γ.source.symm rfl

lemma range_firstHalf (γ : Path x y) : range γ.firstHalf = γ '' Icc 0 half :=
  γ.range_subpath_of_le _ _ zero_lt_half.le

/-- The subpath from the midpoint to the target. -/
noncomputable def secondHalf (γ : Path x y) : Path (γ half) y :=
  (γ.subpath half 1).cast rfl γ.target.symm

lemma range_secondHalf (γ : Path x y) : range γ.secondHalf = γ '' Icc half 1 :=
  γ.range_subpath_of_le _ _ half_lt_one.le

lemma firstHalf_range_union_secondHalf_range (γ : Path x y) :
    range γ.firstHalf ∪ range γ.secondHalf = range γ := by
  rw [range_firstHalf, range_secondHalf, ← image_union,
    Icc_union_Icc_eq_Icc zero_lt_half.le half_lt_one.le, unitInterval.Icc_eq_univ, image_univ]

end Path
