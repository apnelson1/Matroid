module

public import Matroid.ForMathlib.Other
public import Matroid.Flat.LowRank
public import Matroid.Flat.Hyperplane
public import Matroid.Equiv
public import Matroid.Simple

@[expose] public section

variable {α : Type*} {M N M₀ : Matroid α} {e f g : α} {I F X Y D : Set α} {P : Set α → Prop}
    {cl : Set α → Set α}

namespace Matroid

open Set

/-- A `SeriesParallelMinor` is a matroid obtained from `M` by repeatedly removing proper subsets
of series and parallel classes. -/
def IsSeriesParallelMinor :=
  Relation.ReflTransGen (fun (N M : Matroid α) ↦ ∃ b, N.bDual b ≤si M.bDual b)

scoped infix:50  " ≤sp " => IsSeriesParallelMinor

lemma Simplifies.isSeriesParallelMinor (hNM : N ≤si M) : N ≤sp M :=
  Relation.ReflTransGen.single ⟨false, hNM⟩

lemma IsSeriesParallelMinor.trans {M₁ M₂ M₃ : Matroid α} (h₁ : M₁ ≤sp M₂) (h₂ : M₂ ≤sp M₃) :
    M₁ ≤sp M₃ :=
  Relation.ReflTransGen.trans h₁ h₂

lemma IsSeriesParallelMinor.dual (h : N ≤sp M) : N✶ ≤sp M✶ := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ h ih => exact
    ih.trans <| Relation.ReflTransGen.single <| Exists.imp' Bool.not (by simp) h

lemma IsSeriesParallelMinor.refl (M : Matroid α) : M ≤sp M :=
  Relation.ReflTransGen.single ⟨false, Simplifies.refl⟩

@[simp]
lemma isSeriesParallelMinor_dual_iff : N✶ ≤sp M✶ ↔ N ≤sp M :=
  ⟨fun h ↦ by simpa using h.dual, IsSeriesParallelMinor.dual⟩

alias ⟨IsSeriesParallelMinor.of_dual, _⟩ := isSeriesParallelMinor_dual_iff

@[simp]
lemma isSeriesParallelMinor_bDual_iff {b : Bool} : (N.bDual b) ≤sp (M.bDual b) ↔ N ≤sp M := by
  cases b with simp

alias ⟨IsSeriesParallelMinor.of_bDual, _⟩ := isSeriesParallelMinor_bDual_iff

lemma IsSeriesParallelMinor.bDual (h : N ≤sp M) (b : Bool) : N.bDual b ≤sp M.bDual b := by
  simpa

@[elab_as_elim]
lemma IsSeriesParallelMinor.induction (motive : ∀ (N M : Matroid α), N ≤sp M → Prop)
    (refl : ∀ M, motive M M Relation.ReflTransGen.refl)
    (of_simplifies : ∀ N M M' (h : N ≤sp M) (h' : M ≤si M') (_ih : motive N M h),
      motive N M' (h.trans h'.isSeriesParallelMinor))
    (of_cosimplifies : ∀ N M M' (h : N ≤sp M) (h' : M✶ ≤si M'✶) (_ih : motive N M h),
      motive N M' (h.trans (h'.isSeriesParallelMinor.of_dual)))
    {N M : Matroid α} (hNM : N ≤sp M) : motive N M hNM := by
  induction hNM with
  | refl => exact refl _
  | @tail M M' h₁ h₂ h₃ =>
    obtain ⟨rfl | rfl, h₂⟩ := h₂
    · exact of_simplifies _ _ _ h₁ h₂ h₃
    exact of_cosimplifies _ _ _ h₁ h₂ h₃

/-- To show something for every series-parallel minor, it suffices to show that the something
is closed under taking simplifications and duality. -/
@[elab_as_elim]
lemma IsSeriesParallelMinor.induction_dual (motive : ∀ (N M : Matroid α), N ≤sp M → Prop)
    (refl : ∀ M, motive M M Relation.ReflTransGen.refl)
    (trans : ∀ N M M' (h : N ≤sp M) (h' : M ≤si M') (_ih : motive N M h),
      motive N M' (h.trans h'.isSeriesParallelMinor))
    (of_dual : ∀ N M (h : N ≤sp M) (_ih : motive N✶ M✶ h.dual), motive N M h)
    {N M : Matroid α} (hNM : N ≤sp M) : motive N M hNM := by
  induction hNM with
  | refl => exact refl _
  | @tail M M' h₁ h₂ h₃ =>
    change _ ≤sp _ at h₁
    obtain ⟨rfl | rfl, h₂⟩ := h₂
    · exact trans _ _ _ h₁ h₂ h₃
    exact of_dual _ _ _ <| trans N✶ M✶ M'✶ _ h₂ <| of_dual N✶ M✶ h₁.dual (by simpa)

@[elab_as_elim]
lemma IsSeriesParallelMinor.induction_dual_head (motive : ∀ (N M : Matroid α), N ≤sp M → Prop)
    (refl : ∀ M, motive M M Relation.ReflTransGen.refl)
    (trans : ∀ M₀ N M (h : M₀ ≤si N) (h' : N ≤sp M) (_ih : motive N M h'),
      motive M₀ M (h.isSeriesParallelMinor.trans h'))
    (of_dual : ∀ N M (h : N ≤sp M) (_ih : motive N✶ M✶ h.dual), motive N M h)
    {N M : Matroid α} (hNM : N ≤sp M) : motive N M hNM := by
  induction hNM using Relation.ReflTransGen.head_induction_on with
  | refl => exact refl _
  | @head M₀ N h₁ h₂ h₃ =>
    change _ ≤sp _ at h₂
    obtain ⟨rfl | rfl, h₁⟩ := h₁
    · exact trans M₀ N M h₁ _ h₃
    exact of_dual _ _ _ <| trans M₀✶ N✶ M✶ h₁ _ <| of_dual _ _ h₂.dual <| by simpa

lemma IsSeriesParallelMinor.isMinor (h : N ≤sp M) : N ≤m M := by
  induction h using IsSeriesParallelMinor.induction_dual with
  | refl M => exact IsMinor.refl
  | trans N M M' h h' ih => exact ih.trans h'.isRestriction.isMinor
  | of_dual N M h ih => simpa using ih


-- lemma IsSeriesParallelMinor.bay {C} (h : M₀ ≤sp M) (hM₀C : M₀ ≤m M ／ C) : M₀ ≤sp M ／ C := by
--   wlog hCE : C ⊆ M.E generalizing C with aux
--   · rw [← contract_inter_ground_eq] at ⊢ hM₀C
--     exact aux hM₀C <| by simp
--   induction h using IsSeriesParallelMinor.induction_dual with
--   | refl M =>
--     sorry
--   | trans N M M' h h' ih =>
--     sorry
--   | of_dual N M h ih =>

-- --     _

lemma Simplifies.isSeriesParallelMinor_iff_of_subset (hNM : N ≤si M) (hM₀ : M₀.E ⊆ N.E) :
    M₀ ≤sp N ↔ M₀ ≤sp M := by
  refine ⟨fun h ↦ h.trans hNM.isSeriesParallelMinor, fun h ↦ ?_⟩
  induction h using IsSeriesParallelMinor.induction with
  | refl M => sorry
  | of_simplifies N' M M' h h' ih =>
    rw [h'.simplifies_right_iff_of_subset] at ih
    -- have := (hNM.simplifies_right_iff_of_subset hM₀).2 <| h
    -- have := ih hNM hM₀
    _
  | of_cosimplifies N M M' h h' ih => sorry

lemma IsSeriesParallelMinor.exists_isSeriesParallelMinor_ground_eq (h : M₀ ≤sp M) (hNX : M₀.E ⊆ X)
    (hXM : X ⊆ M.E) : ∃ N, M₀ ≤sp N ∧ N ≤m M ∧ N.E = X := by
  induction h using IsSeriesParallelMinor.induction_dual generalizing X with
  | refl M => exact ⟨M, IsSeriesParallelMinor.refl M, IsMinor.refl, hNX.antisymm hXM⟩
  | trans M₀ M' M h h' ih =>
    obtain ⟨N, hM₀N, hNM', hNE⟩ := ih (subset_inter hNX h.isMinor.subset) inter_subset_right
    obtain ⟨P, rfl, hPi, hP⟩ := h'.exists_eq_delete
    rw [delete_ground, ← inter_sdiff_assoc, inter_eq_self_of_subset_left hXM] at hNE
    obtain ⟨C, D, hC, hD, hCD, rfl⟩ := hNM'.exists_contract_indep_delete_coindep
    clear hNM'
    refine ⟨M ／ (C \ X) ＼ ((D ∪ P) \ X) , h.trans ?_, contract_delete_isMinor .., ?_⟩
    ·
      sorry
    simp only [delete_ground, contract_ground, sdiff_sdiff, ← union_sdiff_distrib]
    rw [sdiff_sdiff_right, inter_eq_self_of_subset_right hXM, union_eq_right]
    rw [delete_ground, contract_ground, delete_ground, sdiff_sdiff, sdiff_sdiff] at hNE
    grind

    -- obtain ⟨φ, hM_eq, hφ₁, hφ₂, hφ₃, hφ₄⟩ := h'.exists_eq_comapOn
    -- sorry



  | of_dual N M h ih =>
    obtain ⟨N', hN', hN'M, rfl⟩ := ih hNX hXM
    exact ⟨N'✶, by simpa using hN'.dual, by simpa using hN'M.dual, rfl⟩


#exit

lemma baz {M M₀ : Matroid α} {D P : Set α} (hD : D ⊆ M.E) (hP : P ⊆ M.E) (hdj : Disjoint P D)
    (hM₀ : M₀ ≤sp M ＼ P) (hPM : M ＼ P ≤si M) : ∃ N, N ≤sp M ＼ D ∧ N.E = M.E \ (P ∪ D) := by
  sorry

lemma bar {M₀} (hM₀ : M₀ ≤sp M) (hN : M₀ ≤m N) (hNM : N ≤m M) : M₀ ≤sp N := by
  obtain ⟨C, D, hC, hD, hCD, rfl⟩ := hNM.exists_contract_indep_delete_coindep
  wlog hC0 : C = ∅ generalizing M₀ M C D with aux
  · have h1 := IsSeriesParallelMinor.dual <| aux hM₀.dual ∅ C (by simp) (by simpa) (by simp)
      (by simpa using (hN.trans (delete_isMinor ..)).dual) (by simp [delete_isMinor]) rfl
    simp only [dual_dual, contract_empty, dual_delete] at h1
    have hci : (M ／ C).Coindep D := by simp [coindep_contract_iff, hD, hCD.symm]
    simpa using aux h1 ∅ D (by simp) hci (by simp) (by simpa) (by simp [delete_isMinor]) rfl
  subst hC0
  rw [contract_empty] at hNM hN ⊢
  clear hCD hC hNM
  induction hM₀ generalizing D with
  | refl =>
    sorry

  | @tail N M h₁ h₂ ih =>
    change _ ≤sp _ at h₁
    obtain hNM | hNM : N ≤si M ∨ N✶ ≤si M✶ := by simpa using h₂
    · obtain ⟨P, hPE, rfl, hP⟩ := hNM.exists_eq_delete
      sorry
    obtain ⟨C, hCE, h_eq, hC⟩ := hNM.exists_eq_delete

    -- have := hNM.contract (C ＼ D)
    -- rw [← eq_dual_iff_dual_eq, dual_delete_dual] at h_eq
    _



    -- sorry
    -- have := (hN.trans (delete_isMinor ..)).dual
    -- have := aux hM₀.dual D C (by simpa) (by simpa) hCD.symm (by simpa using hN.dual)
    --   (contract_delete_isMinor ..)

  induction hM₀ using IsSeriesParallelMinor.induction_dual generalizing N with
  | refl M =>
    rw [hN.antisymm hNM]
    exact IsSeriesParallelMinor.refl N
  | trans M₀ N' M hM₀N' hN' h =>

    obtain ⟨P, hPE, rfl, hP⟩ := hN'.exists_eq_delete

    have := baz (M := M ／ C ＼ (P ∩ D)) (M₀ := M₀) (D := D \ P) (P := P \ (C ∪ D)) (by grind)
      (by grind) (by grind)
    rw [delete_delete, union_comm C D, ← sdiff_inter_sdiff, union_inter_distrib_left,
      inter_union_sdiff, inter_union_distrib_left, inter_eq_self_of_subset_right inter_subset_left,
      inter_eq_self_of_subset_right sdiff_subset] at this

    sorry
  | of_dual M₀ M h ih => simpa using ih hN.dual hNM.dual

alias ⟨IsSeriesParallelMinor.of_dual, _⟩ := isSeriesParallelMinor_dual_iff

lemma Coindep.delete_isSeriesParallelMinor_iff : (M ＼ D) ≤sp M ↔ M ＼ D ≤si M := by
  refine ⟨fun h ↦ ?_, Simplifies.isSeriesParallelMinor⟩

def IsSeriesParallel (M : Matroid α) : Prop := emptyOn α ≤sp M

lemma IsSeriesParallel.minor (hM : M.IsSeriesParallel) (hNM : N ≤m M) :
    N.IsSeriesParallel := by
  simp [IsSeriesParallel] at hM ⊢
  induction hM generalizing N with
  | @single M h =>
    obtain ⟨b, hb⟩ := h
    rw [← isSeriesParallelMinor_bDual_iff (b := b)]
    simp only [emptyOn_bDual, emptyOn_simplifies_iff, eRank_eq_zero_iff, bDual_ground] at hb
    replace hNM := hb ▸ (hNM.bDual b)
    simp only [isMinor_loopyOn_iff, bDual_ground] at hNM

    rw [hNM.1, ← isSeriesParallelMinor_bDual_iff (b := b), emptyOn_bDual,
      isSeriesParallelMinor_bDual_iff]
    refine Simplifies.isSeriesParallelMinor <| by simp
  | @tail M N' h hb h' =>
    refine h' <| hNM.trans ?_


/-


-- @[mk_iff]
-- structure IsSeriesParallelMinor (N M : Matroid α) : Prop where
--   isMinor : N ≤m M
--   closure_eq : M.seriesParallelClosure N.E = M.E

scoped infix:50  " ≤sp " => IsSeriesParallelMinor

@[simp]
lemma isSeriesParallelMinor_dual_iff : N✶ ≤sp M✶ ↔ N ≤sp M := by
  simp [isSeriesParallelMinor_iff, dual_isMinor_iff]

lemma IsSeriesParallelMinor.trans {M₁ M₂ M₃ : Matroid α} (h₁ : M₁ ≤sp M₂) (h₂ : M₂ ≤sp M₃) :
    M₁ ≤sp M₃ := by
  refine ⟨h₁.isMinor.trans h₂.isMinor, ?_⟩
  nth_grw 1 [← h₂.closure_eq, ← h₁.closure_eq, subset_antisymm_iff,
    ← M₂.subset_seriesParallelClosure _ h₁.isMinor.subset, and_iff_right subset_rfl]
  refine seriesParallelClosure_subset_of_subset _ <| le_sInf fun X hX ↦ sInf_le ?_
  simp [inter_eq_self_of_subset_left (h₁.isMinor.subset.trans h₂.isMinor.subset)] at hX ⊢




lemma deleteElem_isSeriesParallelMinor (hef : M.Parallel e f) (hne : e ≠ f) : (M ＼ {e}) ≤sp M := by
  refine ⟨delete_isMinor .., subset_antisymm (closureBy_subset_ground _ ?_) fun x hx ↦ ?_⟩
  · simp [M.closure_subset_ground]
  obtain hne | rfl := ne_or_eq x e
  · exact mem_of_mem_of_subset (show x ∈ (M ＼ {e}).E from ⟨hx, hne⟩)
      (subset_seriesParallelClosure M _ sdiff_subset)
  have hcl := M.isSeriesParallelClosed_seriesParallelClosure (M ＼ {x}).E
  have hu := hcl.closed {f} (singleton_subset_iff.2 ?_) (by simp)
  · exact mem_of_mem_of_subset (.inl hef.mem_closure) hu
  exact mem_of_mem_of_subset (show f ∈ (M ＼ {x}).E from ⟨hef.mem_ground_right, hne.symm⟩)
    <| subset_seriesParallelClosure _ _ sdiff_subset

lemma contractElem_isSeriesParallelMinor (hef : M.Series e f) (hne : e ≠ f) : (M ／ {e}) ≤sp M := by
  rw [← isSeriesParallelMinor_dual_iff, dual_contract]
  exact deleteElem_isSeriesParallelMinor hef hne

-/
