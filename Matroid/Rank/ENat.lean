import Mathlib.Combinatorics.Matroid.Rank.ENat -- inefficient import
import Mathlib.Combinatorics.Matroid.Rank.Finite -- inefficient import
import Matroid.Loop
import Matroid.OnUniv
import Matroid.ForMathlib.Other
import Matroid.ForMathlib.Matroid.Closure
import Matroid.Closure
import Matroid.Sum

/- The rank `M.eRk X` of a set `X` in a matroid `M` is the size of one of its bases,
as a term in `ℕ∞`.
When such bases are infinite, this quantity is too coarse to be useful for building API,
even though it is often the easiest way to do things for finite matroids. -/

open Set ENat

namespace Matroid

universe u v

variable {α ι : Type*} {M N : Matroid α} {I B X X' Y Y' Z R : Set α} {n : ℕ∞} {e f : α}

section Basic


@[gcongr]
lemma eRk_subset_le (M : Matroid α) (hXY : X ⊆ Y) : M.eRk X ≤ M.eRk Y :=
  M.eRk_mono hXY

lemma spanning_iff_eRk' [RankFinite M] : M.Spanning X ↔ M.eRank ≤ M.eRk X ∧ X ⊆ M.E := by
  refine ⟨fun h ↦ ⟨h.eRk_eq.symm.le, h.subset_ground⟩, fun ⟨h, hX⟩ ↦ ?_⟩
  obtain ⟨I, hI⟩ := M.exists_isBasis X
  exact (hI.indep.isBase_of_eRk_ge
    hI.indep.finite (h.trans hI.eRk_eq_eRk.symm.le)).spanning_of_superset hI.subset

lemma spanning_iff_eRk [RankFinite M] (hX : X ⊆ M.E := by aesop_mat) :
    M.Spanning X ↔ M.eRank ≤ M.eRk X := by
  rw [spanning_iff_eRk', and_iff_left hX]

lemma Nonspanning.eRk_add_one_le (h : M.Nonspanning X) : M.eRk X + 1 ≤ M.eRank := by
  obtain hM | hM := M.rankFinite_or_rankInfinite
  · have hXE := h.subset_ground
    rw [← not_spanning_iff, spanning_iff_eRk, not_le] at h
    exact Order.add_one_le_of_lt h
  simp

lemma IsLoopEquiv.eRk_eq_eRk (h : M.IsLoopEquiv X Y) : M.eRk X = M.eRk Y := by
  rw [← M.eRk_closure_eq, h.closure_eq_closure, M.eRk_closure_eq]

@[simp]
lemma eRank_lt_top [M.RankFinite] : M.eRank < ⊤ := by
  obtain ⟨B, hB⟩ := M.exists_isBase
  rw [← hB.encard_eq_eRank, encard_lt_top_iff]
  exact hB.finite

@[simp]
lemma eRk_lt_top [M.RankFinite] {X} : M.eRk X < ⊤ :=
  (M.isRkFinite_set X).eRk_lt_top

@[simp]
lemma eRk_ne_top [M.RankFinite] {X} : M.eRk X ≠ ⊤ :=
  (M.isRkFinite_set X).eRk_lt_top.ne

lemma Nonspanning.eRk_lt [M.RankFinite] (h : M.Nonspanning X) : M.eRk X < M.eRank := by
  rw [← ENat.add_one_le_iff]
  · exact h.eRk_add_one_le
  exact ((M.eRk_le_eRank X).trans_lt M.eRank_lt_top).ne

lemma nonspanning_iff_eRk_lt [M.RankFinite] (hXE : X ⊆ M.E := by aesop_mat) :
    M.Nonspanning X ↔ M.eRk X < M.eRank :=
  ⟨Nonspanning.eRk_lt, fun h ↦ by rwa [← not_spanning_iff, spanning_iff_eRk, not_le]⟩

lemma nonspanning_of_eRk_ne (hX : M.eRk X ≠ M.eRank) (hXE : X ⊆ M.E := by aesop_mat) :
    M.Nonspanning X := by
  rw [← not_spanning_iff]
  exact fun h ↦ hX h.eRk_eq

lemma eRank_pos (M : Matroid α) [M.RankPos] : 0 < M.eRank := by
  obtain ⟨B, hB⟩ := M.exists_isBase
  rw [← hB.encard_eq_eRank, encard_pos]
  exact hB.nonempty

lemma eRank_ne_zero (M : Matroid α) [M.RankPos] : M.eRank ≠ 0 :=
  M.eRank_pos.ne.symm

lemma eRank_ne_zero_iff (M : Matroid α) : M.eRank ≠ 0 ↔ M.RankPos := by
  refine ⟨fun h ↦ (rankPos_iff _).2 fun hb ↦ ?_, fun h ↦ M.eRank_ne_zero⟩
  simp [← hb.encard_eq_eRank] at h

instance [M.RankInfinite] : M.RankPos where
  empty_not_isBase := fun h ↦ by simpa using h.infinite

@[simp]
lemma rankPos_restrict_iff : (M ↾ X).RankPos ↔ M.eRk X ≠ 0 := by
  rw [← eRank_ne_zero_iff, eRank_restrict]

lemma Dep.eRk_add_one_le_encard (h : M.Dep X) : M.eRk X + 1 ≤ X.encard := by
  obtain hinf | hfin := X.finite_or_infinite.symm
  · simp [hinf.encard_eq]
  by_contra! hlt
  have hi := (M.isRkFinite_of_finite hfin).indep_of_encard_le_eRk (Order.le_of_lt_add_one hlt)
  exact hi.not_dep h

lemma IsNonloop.subset_closure_of_eRk_le_one (he : M.IsNonloop e) (hX : M.eRk X ≤ 1) (heX : e ∈ X)
    (hXE : X ⊆ M.E := by aesop_mat) : X ⊆ M.closure {e} :=
  (he.indep.isBasis_of_eRk_ge (by simp) (by simpa) <| by grw [hX, he.eRk_eq]).subset_closure

end Basic

section Constructions


variable {E : Set α}


@[simp] lemma disjointSum_eRk_eq (M N : Matroid α) (hMN : Disjoint M.E N.E) (X : Set α) :
    (M.disjointSum N hMN).eRk X = M.eRk (X ∩ M.E) + N.eRk (X ∩ N.E) := by
  obtain ⟨B₁, hB₁⟩ := M.exists_isBasis (X ∩ M.E)
  obtain ⟨B₂, hB₂⟩ := N.exists_isBasis (X ∩ N.E)
  rw [← eRk_inter_ground, disjointSum_ground_eq, inter_union_distrib_left,
    (hB₁.disjointSum_isBasis_union hB₂ hMN).eRk_eq_encard, hB₁.eRk_eq_encard, hB₂.eRk_eq_encard,
    encard_union_eq (hMN.mono hB₁.indep.subset_ground hB₂.indep.subset_ground)]

@[simp] lemma disjointSum_eRank_eq (M N : Matroid α) (hMN : Disjoint M.E N.E) :
    (M.disjointSum N hMN).eRank = M.eRank + N.eRank := by
  rw [eRank_def, eRank_def, eRank_def, disjointSum_eRk_eq, disjointSum_ground_eq,
    inter_eq_self_of_subset_right subset_union_left,
    inter_eq_self_of_subset_right subset_union_right]

end Constructions


lemma eRk_eq_iSup_finset_eRk (M : Matroid α) (X : Set α) :
    M.eRk X = ⨆ Y ∈ {S : Finset α | (S : Set α) ⊆ X}, M.eRk Y := by
  simp only [mem_setOf_eq, le_antisymm_iff, iSup_le_iff]
  refine ⟨?_, fun S hSX ↦ M.eRk_mono hSX⟩

  by_cases hX : M.IsRkFinite X
  · obtain ⟨I, hI⟩ := hX.exists_finset_isBasis'
    exact le_iSup₂_of_le (i := I) hI.subset <| by rw [hI.eRk_eq_eRk]

  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [← eRk_eq_top_iff] at hX
  rw [hX, top_le_iff, ENat.eq_top_iff_forall_ge]
  intro n
  rw [hI.eRk_eq_encard, encard_eq_top_iff] at hX
  obtain ⟨J, hJI, rfl⟩ := hX.exists_subset_card_eq n
  apply le_iSup₂_of_le J (hJI.trans hI.subset)
  rw [(hI.indep.subset hJI).eRk_eq_encard, encard_coe_eq_coe_finsetCard]

lemma eRk_union_eq_of_subset_of_eRk_le_eRk (Z : Set α) (hXY : X ⊆ Y) (hr : M.eRk Y ≤ M.eRk X) :
    M.eRk (X ∪ Z) = M.eRk (Y ∪ Z) := by
  obtain hX' | hX' := em (M.IsRkFinite X)
  · rw [← eRk_union_closure_left_eq, hX'.closure_eq_closure_of_subset_of_eRk_ge_eRk hXY hr,
      eRk_union_closure_left_eq]
  rw [eRk_eq_top_iff.2, eRk_eq_top_iff.2]
  · contrapose! hX'
    exact hX'.subset (hXY.trans subset_union_left)
  contrapose! hX'
  exact hX'.subset subset_union_left

lemma eRk_union_eq_of_subsets_of_eRks_le (hX : X ⊆ X') (hY : Y ⊆ Y') (hXX' : M.eRk X' ≤ M.eRk X)
    (hYY' : M.eRk Y' ≤ M.eRk Y) : M.eRk (X ∪ Y) = M.eRk (X' ∪ Y') := by
  rw [eRk_union_eq_of_subset_of_eRk_le_eRk _ hX hXX', union_comm,
    eRk_union_eq_of_subset_of_eRk_le_eRk _ hY hYY', union_comm]

lemma not_isRkFinite_of_eRk_ge (h : ¬M.IsRkFinite X) (hXY : M.eRk X ≤ M.eRk Y) :
    ¬M.IsRkFinite Y := by
  contrapose! h
  exact eRk_lt_top_iff.1 <| hXY.trans_lt h.eRk_lt_top

lemma eRk_restrict (M : Matroid α) (R X : Set α) : (M ↾ R).eRk X = M.eRk (X ∩ R) := by
  rw [← eRk_inter_ground, restrict_ground_eq, inter_comm, ← eRank_restrict,
    restrict_restrict_eq _ inter_subset_left, eRank_restrict]

@[simp]
lemma eRk_restrict_univ (M : Matroid α) (X : Set α) : (M ↾ univ).eRk X = M.eRk (X) := by
  rw [eRk_restrict, inter_univ]

lemma IsRestriction.eRk_eq (h : N ≤r M) {X : Set α} (hX : X ⊆ N.E) : N.eRk X = M.eRk X := by
  obtain ⟨R, hR, rfl⟩ := h.exists_eq_restrict
  rw [eRk_restrict, inter_eq_self_of_subset_left (by simpa)]

lemma IsSpanningRestriction.eRank_eq {N : Matroid α} (h : N ≤sr M) : N.eRank = M.eRank := by
  rw [← eRk_ground, h.isRestriction.eRk_eq rfl.subset, h.spanning.eRk_eq]

lemma eRank_comapOn {β : Type*} {M : Matroid β} {E : Set α} (f : α → β) (hM : SurjOn f E M.E) :
    (M.comapOn E f).eRank = M.eRank := by
  obtain ⟨B, hB⟩ := M.exists_isBase
  obtain ⟨B', hB'E, hbij⟩ := (hM.mono rfl.subset hB.subset_ground).exists_bijOn_subset
  have hB' : (M.comapOn E f).IsBase B' := by
    rwa [comapOn_isBase_iff_of_surjOn hM, hbij.image_eq, and_iff_left hB'E, and_iff_left hbij.injOn]
  rw [← hB'.encard_eq_eRank, ← hB.encard_eq_eRank, ← hbij.image_eq, hbij.injOn.encard_image]

lemma eRank_comap {β : Type*} {M : Matroid β} (f : α → β) (hM : M.E ⊆ range f) :
    (M.comap f).eRank = M.eRank := by
  obtain ⟨B, hB⟩ := M.exists_isBase
  obtain ⟨B, rfl, hfB⟩ := exists_image_eq_injOn_of_subset_range (hB.subset_ground.trans hM)
  rw [← hB.encard_eq_eRank, ← IsBase.encard_eq_eRank (B := B), hfB.encard_image]
  grw [comap_isBase_iff, and_iff_right hfB, ← image_subset_iff, and_iff_left hB.subset_ground]
  refine hB.isBasis_of_subset (image_preimage_subset ..) <| image_mono ?_
  grw [← image_subset_iff, hB.subset_ground]

variable {k : ℕ∞}

/-- The property of having rank at most `k` in a matroid `M`. -/
def RkLE (M : Matroid α) (k : ℕ∞) (X : Set α) : Prop := M.eRk X ≤ k

lemma RkLE.le (h : M.RkLE k X) : M.eRk X ≤ k := h

lemma rkLE_self (M : Matroid α) (X : Set α) : M.RkLE (M.eRk X) X := rfl.le

@[simp]
lemma rkLE_empty : M.RkLE k ∅ := by
  simp [RkLE]

@[simp]
lemma rkLE_singleton : M.RkLE 1 {e} := by
  simp [RkLE]

@[gcongr]
lemma RkLE.mono {l k : ℕ∞} (h : M.RkLE l X) (hlk : l ≤ k) : M.RkLE k X :=
  h.trans hlk

lemma rkLE_eRank (M : Matroid α) (X : Set α) : M.RkLE (M.eRank) X :=
  (rkLE_self M X).mono <| M.eRk_le_eRank X

@[gcongr]
lemma RkLE.subset (h : M.RkLE k X) (hYX : Y ⊆ X) : M.RkLE k Y :=
  (M.eRk_mono hYX).trans h

@[simp]
lemma antitone_rkLE : Antitone (M.RkLE k) :=
  fun _ _ hXY h ↦ h.subset hXY

lemma RkLE.closure (h : M.RkLE k X) : M.RkLE k (M.closure X) := by
  grw [RkLE, eRk_closure_eq, h.le]

@[simp]
lemma rkLE_closure_iff : M.RkLE k (M.closure X) ↔ M.RkLE k X :=
  ⟨fun h ↦ by grw [RkLE, ← h.le, eRk_closure_eq], RkLE.closure⟩

lemma eRk_insert_of_mem_closure (he : e ∈ M.closure X) : M.eRk (insert e X) = M.eRk X := by
  rw [← eRk_insert_closure_eq, insert_eq_of_mem he, eRk_closure_eq]

lemma IsRkFinite.mem_closure_iff (h : M.IsRkFinite X) (he : e ∈ M.E := by aesop_mat) :
    e ∈ M.closure X ↔ M.eRk (Insert.insert e X) = M.eRk X := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [← eRk_insert_closure_eq, ← hI.closure_eq_closure, eRk_insert_closure_eq, hI.eRk_eq_encard]
  by_cases heI : e ∈ I
  · rw [insert_eq_of_mem heI, hI.indep.eRk_eq_encard]
    simp [M.mem_closure_of_mem' heI]
  by_cases heI' : e ∈ M.closure I
  · rw [← eRk_insert_closure_eq, insert_eq_of_mem heI', eRk_closure_eq, hI.indep.eRk_eq_encard]
    simpa
  rw [eRk_insert_eq_add_one ⟨he, heI'⟩, hI.indep.eRk_eq_encard]
  simp [heI', hI.finite_of_isRkFinite h]

lemma IsRkFinite.mem_closure_iff_le (h : M.IsRkFinite X) (he : e ∈ M.E := by aesop_mat) :
    e ∈ M.closure X ↔ M.eRk (Insert.insert e X) ≤ M.eRk X := by
  rw [h.mem_closure_iff, le_antisymm_iff, and_iff_left (M.eRk_subset_le (subset_insert ..))]

  -- refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  -- ·
  -- rw [hI.indep.mem_closure_iff_of_notMem heI]

  -- obtain ⟨B, rfl, hfB⟩ := exists_image_eq_injOn_of_subset_range (hB.subset_ground.trans hM)
  -- have := exists_image_eq_and_injOn _(hB.subset_ground.trans hM)
