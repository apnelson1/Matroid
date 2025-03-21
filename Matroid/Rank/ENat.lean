import Mathlib.Data.Matroid.Rank.Finite
import Matroid.Loop
import Matroid.OnUniv
import Matroid.ForMathlib.Other
import Matroid.ForMathlib.Matroid.Sum
import Mathlib.Tactic.TautoSet

/- The rank `M.eRk X` of a set `X` in a matroid `M` is the size of one of its bases,
as a term in `ℕ∞`.
When such bases are infinite, this quantity is too coarse to be useful for building API,
even though it is often the easiest way to do things for finite matroids. -/

open Set ENat

namespace Matroid

universe u v

variable {α ι : Type*} {M N : Matroid α} {I B X X' Y Y' Z R : Set α} {n : ℕ∞} {e f : α}

section Basic

/-- The rank `Matroid.eRank M` of `M` is the `ℕ∞`-valued cardinality of each base of `M`. -/
noncomputable def eRank (M : Matroid α) : ℕ∞ := ⨆ (B : {B // M.IsBase B}), B.1.encard

/-- The rank `Matroid.eRk M X` of a set `X` is the `ℕ∞`-valued cardinality of each basis of `X`. -/
noncomputable abbrev eRk (M : Matroid α) (X : Set α) : ℕ∞ := (M ↾ X).eRank

lemma eRank_def (M : Matroid α) : M.eRank = M.eRk M.E := by
  rw [eRk, restrict_ground_eq_self]

@[simp] lemma eRank_restrict (M : Matroid α) (X : Set α) : (M ↾ X).eRank = M.eRk X := rfl

lemma IsBase.encard_eq_eRank (hB : M.IsBase B) : B.encard = M.eRank := by
  simp [eRank, show ∀ B' : {B // M.IsBase B}, B'.1.encard = B.encard from
    fun B' ↦ B'.2.encard_eq_encard_of_isBase hB]

lemma IsBasis'.encard_eq_eRk (hI : M.IsBasis' I X) : I.encard = M.eRk X :=
  hI.isBase_restrict.encard_eq_eRank

lemma IsBasis.encard_eq_eRk (hI : M.IsBasis I X) : I.encard = M.eRk X :=
  hI.isBasis'.encard_eq_eRk

lemma eq_eRk_iff (hX : X ⊆ M.E := by aesop_mat) :
    M.eRk X = n ↔ ∃ I, M.IsBasis I X ∧ I.encard = n :=
  ⟨fun h ↦ (M.exists_isBasis X).elim (fun I hI ↦ ⟨I, hI, by rw [hI.encard_eq_eRk, ← h]⟩),
    fun ⟨I, hI, hIc⟩ ↦ by rw [← hI.encard_eq_eRk, hIc]⟩

lemma Indep.eRk_eq_encard (hI : M.Indep I) : M.eRk I = I.encard :=
  (eq_eRk_iff hI.subset_ground).mpr ⟨I, hI.isBasis_self, rfl⟩

lemma IsBasis'.eRk_eq_eRk (hIX : M.IsBasis' I X) : M.eRk I = M.eRk X := by
  rw [← hIX.encard_eq_eRk, hIX.indep.eRk_eq_encard]

lemma IsBasis.eRk (hIX : M.IsBasis I X) : M.eRk I = M.eRk X := by
  rw [← hIX.encard_eq_eRk, hIX.indep.eRk_eq_encard]

lemma IsBasis'.eRk_eq_encard (hIX : M.IsBasis' I X) : M.eRk X = I.encard := by
  rw [← hIX.eRk_eq_eRk, hIX.indep.eRk_eq_encard]

lemma IsBasis.eRk_eq_encard (hIX : M.IsBasis I X) : M.eRk X = I.encard := by
  rw [← hIX.eRk, hIX.indep.eRk_eq_encard]

lemma IsBase.eRk (hB : M.IsBase B) : M.eRk B = M.eRank := by
  rw [hB.indep.eRk_eq_encard, eRank_def, hB.isBasis_ground.encard_eq_eRk]

@[simp] lemma eRank_map {β : Type*} (M : Matroid α) (f : α → β) (hf : InjOn f M.E) :
    (M.map f hf).eRank = M.eRank := by
  obtain ⟨B, hB⟩ := M.exists_isBase
  rw [← (hB.map hf).encard_eq_eRank, ← hB.encard_eq_eRank, (hf.mono hB.subset_ground).encard_image]

@[simp] lemma eRank_loopyOn (E : Set α) : (loopyOn E).eRank = 0 := by
  simp [← (show (loopyOn E).IsBase ∅ by simp).encard_eq_eRank]

@[simp] lemma eRank_emptyOn (α : Type*) : (emptyOn α).eRank = 0 := by
  simp [← (show (emptyOn α).IsBase ∅ by simp).encard_eq_eRank]

@[simp] lemma eRk_ground (M : Matroid α) : M.eRk M.E = M.eRank :=
  M.eRank_def.symm

@[simp] lemma eRk_inter_ground (M : Matroid α) (X : Set α) : M.eRk (X ∩ M.E) = M.eRk X := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [← hI.eRk_eq_eRk, hI.isBasis_inter_ground.eRk]

@[simp] lemma eRk_ground_inter (M : Matroid α) (X : Set α) : M.eRk (M.E ∩ X) = M.eRk X := by
  rw [inter_comm, eRk_inter_ground]

lemma eRk_eq_eRank (hX : M.E ⊆ X) : M.eRk X = M.eRank := by
  rw [← eRk_inter_ground, inter_eq_self_of_subset_right hX, eRank_def]

@[simp]
lemma eRk_union_ground (M : Matroid α) (X : Set α) : M.eRk (X ∪ M.E) = M.eRank := by
  rw [← eRk_inter_ground, inter_eq_self_of_subset_right subset_union_right, eRank_def]

@[simp]
lemma eRk_ground_union (M : Matroid α) (X : Set α) : M.eRk (M.E ∪ X) = M.eRank := by
  rw [union_comm, eRk_union_ground]

lemma eRk_insert_of_not_mem_ground (X : Set α) (he : e ∉ M.E) : M.eRk (insert e X) = M.eRk X := by
  rw [← eRk_inter_ground, insert_inter_of_not_mem he, eRk_inter_ground]

lemma eRk_compl_union_of_disjoint (M : Matroid α) (hXY : Disjoint X Y) :
    M.eRk (M.E \ X ∪ Y) = M.eRk (M.E \ X) := by
  rw [← eRk_inter_ground, union_inter_distrib_right, inter_eq_self_of_subset_left diff_subset,
    union_eq_self_of_subset_right
      (subset_diff.2 ⟨inter_subset_right, hXY.symm.mono_left inter_subset_left⟩)]

lemma one_le_eRank (M : Matroid α) [RankPos M] : 1 ≤ M.eRank := by
  obtain ⟨B, hB⟩ := M.exists_isBase
  rw [← hB.encard_eq_eRank, one_le_encard_iff_nonempty]
  exact hB.nonempty

lemma rankFinite_iff_eRank_ne_top : M.RankFinite ↔ M.eRank ≠ ⊤ := by
  obtain ⟨B, hB⟩ := M.exists_isBase
  rw [← hB.encard_eq_eRank, encard_ne_top_iff]
  exact ⟨fun h ↦ hB.finite, fun h ↦ hB.rankFinite_of_finite h⟩

@[simp] lemma eRk_map_eq {β : Type*} {f : α → β} (M : Matroid α) (hf : InjOn f M.E)
    (hX : X ⊆ M.E := by aesop_mat) : (M.map f hf).eRk (f '' X) = M.eRk X := by
  obtain ⟨I, hI⟩ := M.exists_isBasis X
  rw [hI.eRk_eq_encard, (hI.map hf).eRk_eq_encard, (hf.mono hI.indep.subset_ground).encard_image]

@[simp] lemma eRk_comap_eq {β : Type*} {f : α → β} (M : Matroid β) (X : Set α) :
    (M.comap f).eRk X = M.eRk (f '' X) := by
  obtain ⟨I, hI⟩ := (M.comap f).exists_isBasis' X
  obtain ⟨hI', hinj, -⟩ := comap_isBasis'_iff.1 hI
  rw [← hI.encard_eq_eRk, ← hI'.encard_eq_eRk, hinj.encard_image]

-- lemma Iso.eRk_image_eq {α β : Type*} {M : Matroid α} {N : Matroid β} (e : Iso M N) (X : Set α)
--     (hX : X ⊆ M.E := by aesop_mat) : N.eRk (e '' X) = M.eRk X := by
--   obtain ⟨I,hI⟩ := M.exists_isBasis X
--   rw [hI.eRk_eq_encard, (e.on_isBasis hI).eRk_eq_encard,
--     (e.injOn_ground.mono hI.subset_ground).encard_image]

@[simp] lemma eRk_univ_eq (M : Matroid α) : M.eRk univ = M.eRank := by
  rw [← eRk_inter_ground, univ_inter, eRank_def]


-- lemma Iso.eRank_eq_eRank {α β : Type*} {M : Matroid α} {N : Matroid β} (e : Iso M N) :
--     M.eRank = N.eRank := by
--   rw [eRank_def, ← e.eRk_image_eq M.E, e.image_ground, eRank_def]

@[simp] lemma eRk_empty (M : Matroid α) : M.eRk ∅ = 0 := by
  rw [← M.empty_indep.isBasis_self.encard_eq_eRk, encard_empty]

@[simp] lemma eRk_closure_eq (M : Matroid α) (X : Set α) : M.eRk (M.closure X) = M.eRk X := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [← hI.closure_eq_closure, ← hI.indep.isBasis_closure.encard_eq_eRk, hI.encard_eq_eRk]

@[simp] lemma eRk_union_closure_right_eq (M : Matroid α) (X Y : Set α) :
    M.eRk (X ∪ M.closure Y) = M.eRk (X ∪ Y) :=
  by rw [← eRk_closure_eq, closure_union_closure_right_eq, eRk_closure_eq]

@[simp] lemma eRk_union_closure_left_eq (M : Matroid α) (X Y : Set α) :
    M.eRk (M.closure X ∪ Y) = M.eRk (X ∪ Y) := by
  rw [← eRk_closure_eq, closure_union_closure_left_eq, eRk_closure_eq]

@[simp] lemma eRk_insert_closure_eq (M : Matroid α) (e : α) (X : Set α) :
    M.eRk (insert e (M.closure X)) = M.eRk (insert e X) := by
  rw [← union_singleton, eRk_union_closure_left_eq, union_singleton]

@[simp] lemma restrict_eRk_eq' (M : Matroid α) (R X : Set α) : (M ↾ R).eRk X = M.eRk (X ∩ R) := by
  obtain ⟨I, hI⟩ := (M ↾ R).exists_isBasis' X
  rw [hI.eRk_eq_encard]
  rw [isBasis'_iff_isBasis_inter_ground, isBasis_restrict_iff', restrict_ground_eq] at hI
  rw [← eRk_inter_ground, ← hI.1.eRk_eq_encard]

@[simp] lemma restrict_eRk_eq (M : Matroid α) (h : X ⊆ R) : (M ↾ R).eRk X = M.eRk X := by
  rw [restrict_eRk_eq', inter_eq_self_of_subset_left h]

lemma eRk_lt_top_of_finite (M : Matroid α) (hX : X.Finite) : M.eRk X < ⊤ := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [hI.eRk_eq_encard, encard_lt_top_iff]
  exact hX.subset hI.subset

lemma IsBasis'.eRk_eq_eRk_union (hIX : M.IsBasis' I X) (Y : Set α) :
    M.eRk (I ∪ Y) = M.eRk (X ∪ Y) := by
  rw [← eRk_union_closure_left_eq, hIX.closure_eq_closure, eRk_union_closure_left_eq]

lemma IsBasis'.eRk_eq_eRk_insert (hIX : M.IsBasis' I X) (e : α) :
    M.eRk (insert e I) = M.eRk (insert e X) := by
  rw [← union_singleton, hIX.eRk_eq_eRk_union, union_singleton]

lemma IsBasis.eRk_eq_eRk_union (hIX : M.IsBasis I X) (Y : Set α) : M.eRk (I ∪ Y) = M.eRk (X ∪ Y) :=
  hIX.isBasis'.eRk_eq_eRk_union Y

lemma IsBasis.eRk_eq_eRk_insert (hIX : M.IsBasis I X) (e : α) :
    M.eRk (insert e I) = M.eRk (insert e X) :=
  by rw [← union_singleton, hIX.eRk_eq_eRk_union, union_singleton]

lemma eRk_le_encard (M : Matroid α) (X : Set α) : M.eRk X ≤ X.encard := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [hI.eRk_eq_encard]
  exact encard_mono hI.subset

lemma eRank_le_encard_ground (M : Matroid α) : M.eRank ≤ M.E.encard :=
  M.eRank_def.trans_le <| M.eRk_le_encard M.E

lemma eRk_mono (M : Matroid α) : Monotone M.eRk := by
  rintro X Y (hXY : X ⊆ Y)
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_isBasis'_of_subset (hI.subset.trans hXY)
  rw [hI.eRk_eq_encard, hJ.eRk_eq_encard]
  exact encard_mono hIJ

lemma eRk_le_eRank (M : Matroid α) (X : Set α) : M.eRk X ≤ M.eRank := by
  rw [eRank_def, ← eRk_inter_ground]; exact M.eRk_mono inter_subset_right

lemma le_eRk_iff : n ≤ M.eRk X ↔ ∃ I, I ⊆ X ∧ M.Indep I ∧ I.encard = n := by
  refine ⟨fun h ↦ ?_, fun ⟨I, hIX, hI, hIc⟩ ↦ ?_⟩
  · obtain ⟨J, hJ⟩ := M.exists_isBasis' X
    rw [← hJ.encard_eq_eRk] at h
    obtain ⟨I, hIJ, rfl⟩ :=  exists_subset_encard_eq h
    exact ⟨_, hIJ.trans hJ.subset, hJ.indep.subset hIJ, rfl⟩
  rw [← hIc, ← hI.eRk_eq_encard]
  exact M.eRk_mono hIX

lemma eRk_le_iff : M.eRk X ≤ n ↔ ∀ {I}, I ⊆ X → M.Indep I → I.encard ≤ n := by
  refine ⟨fun h I hIX hI ↦ (hI.eRk_eq_encard.symm.trans_le ((M.eRk_mono hIX).trans h)), fun h ↦ ?_⟩
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [← hI.encard_eq_eRk]
  exact h hI.subset hI.indep

lemma Indep.encard_le_eRk_of_subset (hI : M.Indep I) (hIX : I ⊆ X) : I.encard ≤ M.eRk X :=
  hI.eRk_eq_encard ▸ M.eRk_mono hIX

lemma Indep.encard_le_eRank (hI : M.Indep I) : I.encard ≤ M.eRank := by
  rw [← hI.eRk_eq_encard, eRank_def]
  exact M.eRk_mono hI.subset_ground

/-- The `ℕ∞`-valued rank function is submodular. -/
lemma eRk_inter_add_eRk_union_le (M : Matroid α) (X Y : Set α) :
    M.eRk (X ∩ Y) + M.eRk (X ∪ Y) ≤ M.eRk X + M.eRk Y := by
  obtain ⟨Ii, hIi⟩ := M.exists_isBasis' (X ∩ Y)
  obtain ⟨IX, hIX, hIX'⟩ :=
    hIi.indep.subset_isBasis'_of_subset (hIi.subset.trans inter_subset_left)
  obtain ⟨IY, hIY, hIY'⟩ :=
    hIi.indep.subset_isBasis'_of_subset (hIi.subset.trans inter_subset_right)
  rw [← hIX.eRk_eq_eRk_union, union_comm, ← hIY.eRk_eq_eRk_union, ← hIi.encard_eq_eRk,
    ← hIX.encard_eq_eRk, ← hIY.encard_eq_eRk, union_comm, ← encard_union_add_encard_inter, add_comm]
  exact add_le_add (eRk_le_encard _ _) (encard_mono (subset_inter hIX' hIY'))

alias eRk_submod := eRk_inter_add_eRk_union_le

-- The next three lemmas are convenient for the calculations that show up in connectivity arguments.
lemma eRk_submod_insert (M : Matroid α) (X Y : Set α) :
    M.eRk (insert e (X ∩ Y)) + M.eRk (insert e (X ∪ Y))
      ≤ M.eRk (insert e X) + M.eRk (insert e Y) := by
  rw [insert_inter_distrib, insert_union_distrib]
  apply M.eRk_submod

lemma eRk_submod_compl (M : Matroid α) (X Y : Set α) :
    M.eRk (M.E \ (X ∪ Y)) + M.eRk (M.E \ (X ∩ Y)) ≤ M.eRk (M.E \ X) + M.eRk (M.E \ Y) := by
  rw [← diff_inter_diff, diff_inter]
  apply M.eRk_submod

lemma eRk_submod_insert_compl (M : Matroid α) (X Y : Set α) :
    M.eRk (M.E \ insert e (X ∪ Y)) + M.eRk (M.E \ insert e (X ∩ Y)) ≤
      M.eRk (M.E \ insert e X) + M.eRk (M.E \ insert e Y) := by
  rw [insert_union_distrib, insert_inter_distrib]
  exact M.eRk_submod_compl (insert e X) (insert e Y)

lemma eRk_eq_eRk_of_subset_le (hXY : X ⊆ Y) (hYX : M.eRk Y ≤ M.eRk X) : M.eRk X = M.eRk Y :=
  (M.eRk_mono hXY).antisymm hYX

lemma eRk_union_le_eRk_add_eRk (M : Matroid α) (X Y : Set α) : M.eRk (X ∪ Y) ≤ M.eRk X + M.eRk Y :=
  le_add_self.trans (M.eRk_submod X Y)

lemma eRk_eq_eRk_union_eRk_le_zero (X : Set α) (hY : M.eRk Y ≤ 0) : M.eRk (X ∪ Y) = M.eRk X :=
  (((M.eRk_union_le_eRk_add_eRk X Y).trans (add_le_add_left hY _)).trans_eq (add_zero _)).antisymm
    (M.eRk_mono subset_union_left)

lemma eRk_eq_eRk_diff_eRk_le_zero (X : Set α) (hY : M.eRk Y ≤ 0) : M.eRk (X \ Y) = M.eRk X := by
  rw [← eRk_eq_eRk_union_eRk_le_zero (X \ Y) hY, diff_union_self, eRk_eq_eRk_union_eRk_le_zero _ hY]

lemma eRk_le_eRk_inter_add_eRk_diff (X Y : Set α) : M.eRk X ≤ M.eRk (X ∩ Y) + M.eRk (X \ Y) := by
  nth_rw 1 [← inter_union_diff X Y]; apply eRk_union_le_eRk_add_eRk

lemma eRk_le_eRk_add_eRk_diff (h : Y ⊆ X) : M.eRk X ≤ M.eRk Y + M.eRk (X \ Y) := by
  nth_rw 1 [← union_diff_cancel h]; apply eRk_union_le_eRk_add_eRk

lemma indep_iff_eRk_eq_encard_of_finite (hI : I.Finite) : M.Indep I ↔ M.eRk I = I.encard := by
  refine ⟨fun h ↦ by rw [h.eRk_eq_encard], fun h ↦ ?_⟩
  obtain ⟨J, hJ⟩ := M.exists_isBasis' I
  rw [← hI.eq_of_subset_of_encard_le hJ.subset]
  · exact hJ.indep
  rw [← h, ← hJ.eRk_eq_encard]

lemma indep_iff_eRk_eq_card [M.Finite] (hI : I ⊆ M.E := by aesop_mat) :
    M.Indep I ↔ M.eRk I = I.encard :=
  indep_iff_eRk_eq_encard_of_finite (M.set_finite I)

lemma eRk_singleton_le (M : Matroid α) (e : α) : M.eRk {e} ≤ 1 := by
  obtain ⟨J, hJ⟩ := M.exists_isBasis' {e}
  rw [hJ.eRk_eq_encard, ← encard_singleton e]
  exact encard_mono hJ.subset

lemma eRk_lt_encard_of_dep_of_finite (h : X.Finite) (hX : M.Dep X) : M.eRk X < X.encard :=
  lt_of_le_of_ne (M.eRk_le_encard X) fun h' ↦
    ((indep_iff_eRk_eq_encard_of_finite h).mpr h').not_dep hX

lemma eRk_lt_encard_iff_dep_of_finite (hX : X.Finite) (hXE : X ⊆ M.E := by aesop_mat) :
    M.eRk X < X.encard ↔ M.Dep X := by
  refine ⟨fun h ↦ ?_, fun h ↦ eRk_lt_encard_of_dep_of_finite hX h⟩
  rw [← not_indep_iff, indep_iff_eRk_eq_encard_of_finite hX]
  exact h.ne

lemma eRk_lt_encard_of_dep [Matroid.Finite M] (hX : M.Dep X) : M.eRk X < X.encard :=
  eRk_lt_encard_of_dep_of_finite (M.set_finite X hX.subset_ground) hX

lemma eRk_lt_encard_iff_dep [Matroid.Finite M] (hXE : X ⊆ M.E := by aesop_mat) :
    M.eRk X < X.encard ↔ M.Dep X :=
  eRk_lt_encard_iff_dep_of_finite (M.set_finite X)

lemma isBasis'_iff_indep_encard_eq_of_finite (hIfin : I.Finite) :
    M.IsBasis' I X ↔ I ⊆ X ∧ M.Indep I ∧ I.encard = M.eRk X := by
  refine ⟨fun h ↦ ⟨h.subset,h.indep, h.eRk_eq_encard.symm⟩, fun ⟨hIX, hI, hcard⟩ ↦ ?_⟩
  rw [isBasis'_iff_isBasis_inter_ground]
  obtain ⟨J, hJ, hIJ⟩ := hI.subset_isBasis_of_subset (subset_inter hIX hI.subset_ground)
  apply hI.isBasis_of_subset_of_subset_closure (subset_inter hIX hI.subset_ground)
  obtain rfl := hIfin.eq_of_subset_of_encard_le' hIJ
    (by rw [hcard, ← hJ.eRk_eq_encard, eRk_inter_ground ])
  exact hJ.subset_closure

lemma isBasis_iff_indep_encard_eq_of_finite (hIfin : I.Finite) (hX : X ⊆ M.E := by aesop_mat) :
    M.IsBasis I X ↔ I ⊆ X ∧ M.Indep I ∧ I.encard = M.eRk X := by
  rw [← isBasis'_iff_isBasis, isBasis'_iff_indep_encard_eq_of_finite hIfin]

lemma Indep.isBasis_of_subset_of_eRk_le_of_finite (hI : M.Indep I) (hIX : I ⊆ X)
    (h : M.eRk X ≤ M.eRk I) (hIfin : I.Finite) (hX : X ⊆ M.E := by aesop_mat) : M.IsBasis I X := by
  rw [isBasis_iff_indep_encard_eq_of_finite hIfin hX, and_iff_right hIX, and_iff_right hI,
     le_antisymm_iff, and_iff_left (h.trans hI.eRk_eq_encard.le), ← hI.eRk_eq_encard]
  exact M.eRk_mono hIX

lemma Indep.isBase_of_encard (hI : M.Indep I) (hIfin : I.Finite) (hIcard : M.eRank ≤ I.encard) :
    M.IsBase I := by
  rw [← isBasis_ground_iff]
  refine hI.isBasis_of_subset_of_eRk_le_of_finite hI.subset_ground ?_ hIfin
  rwa [← eRank_def, hI.eRk_eq_encard]

lemma eRk_insert_le_add_one (M : Matroid α) (e : α) (X : Set α) :
    M.eRk (insert e X) ≤ M.eRk X + 1 := by
  rw [← union_singleton]
  exact (M.eRk_union_le_eRk_add_eRk _ _).trans (add_le_add_left (eRk_singleton_le _ _) _)

lemma eRk_union_le_encard_add_eRk (M : Matroid α) (X Y : Set α) :
    M.eRk (X ∪ Y) ≤ X.encard + M.eRk Y :=
  (M.eRk_union_le_eRk_add_eRk X Y).trans (add_le_add_right (M.eRk_le_encard _) _)

lemma eRk_union_le_eRk_add_encard (M : Matroid α) (X Y : Set α) :
    M.eRk (X ∪ Y) ≤ M.eRk X + Y.encard :=
  (M.eRk_union_le_eRk_add_eRk X Y).trans (add_le_add_left (M.eRk_le_encard _) _)

lemma eRank_le_encard_add_eRk_compl (M : Matroid α) (X : Set α) :
    M.eRank ≤ X.encard + M.eRk (M.E \ X) :=
  le_trans (by rw [← eRk_inter_ground, eRank_def, union_diff_self,
    union_inter_cancel_right]) (M.eRk_union_le_encard_add_eRk X (M.E \ X))

lemma eRk_insert_eq_add_one (M : Matroid α) (X : Set α) (he : e ∈ M.E \ M.closure X) :
    M.eRk (insert e X) = M.eRk X + 1 := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [← hI.closure_eq_closure] at he
  rw [← eRk_closure_eq, ← closure_insert_closure_eq_closure_insert, ← hI.closure_eq_closure,
    hI.eRk_eq_encard, closure_insert_closure_eq_closure_insert, eRk_closure_eq, Indep.eRk_eq_encard,
    encard_insert_of_not_mem]
  · exact fun heI ↦ he.2 (M.subset_closure I hI.indep.subset_ground heI)
  rw [hI.indep.insert_indep_iff]
  exact Or.inl he

lemma eRk_augment (h : M.eRk X < M.eRk Z) : ∃ z ∈ Z \ X, M.eRk (insert z X) = M.eRk X + 1 := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_isBasis'_of_subset (hI.subset.trans subset_union_left)
  have hlt := h.trans_le (M.eRk_mono (subset_union_right (s := X)))
  rw [hI.eRk_eq_encard, hJ.eRk_eq_encard] at hlt
  obtain ⟨e, heJ, heI⟩ := exists_of_ssubset (hIJ.ssubset_of_ne (by rintro rfl; exact hlt.ne rfl))
  have heIi : M.Indep (insert e I) := hJ.indep.subset (insert_subset heJ hIJ)
  have heX : e ∉ X := fun h ↦
    heI (hI.isBasis_inter_ground.mem_of_insert_indep ⟨h, hJ.indep.subset_ground heJ⟩ heIi)
  refine ⟨e, ⟨Or.elim (hJ.subset heJ) (False.elim ∘ heX) id, heX⟩, ?_⟩
  rw [← hI.eRk_eq_eRk_insert, hI.eRk_eq_encard, heIi.eRk_eq_encard, encard_insert_of_not_mem heI]

lemma eRk_eq_of_eRk_insert_le_forall (hXY : X ⊆ Y)
    (hY : ∀ e ∈ Y \ X, M.eRk (insert e X) ≤ M.eRk X) : M.eRk X = M.eRk Y := by
  refine (M.eRk_mono hXY).eq_of_not_lt (fun hlt ↦ ?_)
  obtain ⟨e, he, hins⟩ := eRk_augment hlt
  specialize hY e he
  rw [← add_zero (M.eRk X), hins,
    WithTop.add_le_add_iff_left (fun htop ↦ not_top_lt (htop ▸ hlt))] at hY
  simp at hY

lemma Indep.exists_insert_of_encard_lt {I J : Set α} (hI : M.Indep I) (hJ : M.Indep J)
    (hcard : I.encard < J.encard) : ∃ e ∈ J \ I, M.Indep (insert e I) := by
  have hIfin : I.Finite := encard_lt_top_iff.1 <| hcard.trans_le le_top
  rw [← hI.eRk_eq_encard, ← hJ.eRk_eq_encard] at hcard
  obtain ⟨e, he, hIe⟩ := eRk_augment hcard
  refine ⟨e, he, ?_⟩
  rw [indep_iff_eRk_eq_encard_of_finite (hIfin.insert e), hIe, encard_insert_of_not_mem he.2,
    hI.eRk_eq_encard]

lemma spanning_iff_eRk' [RankFinite M] : M.Spanning X ↔ M.eRank ≤ M.eRk X ∧ X ⊆ M.E := by
  refine ⟨fun h ↦ ?_, fun ⟨hr, hX⟩ ↦ ?_⟩
  · rw [eRank_def, ← eRk_closure_eq _ X, h.closure_eq]; exact ⟨rfl.le, h.subset_ground⟩
  obtain ⟨J, hJ⟩ := M.exists_isBasis X
  obtain ⟨B, hB, hJB⟩ := hJ.indep.exists_isBase_superset
  rw [← hJ.encard_eq_eRk, ← hB.encard_eq_eRank] at hr
  obtain rfl := hB.finite.eq_of_subset_of_encard_le hJB hr
  rw [spanning_iff_exists_isBase_subset]
  exact ⟨J, hB, hJ.subset⟩

lemma spanning_iff_eRk [RankFinite M] (hX : X ⊆ M.E := by aesop_mat) :
    M.Spanning X ↔ M.eRank ≤ M.eRk X := by
  rw [spanning_iff_eRk', and_iff_left hX]

lemma Spanning.eRk_eq (hX : M.Spanning X) : M.eRk X = M.eRank := by
  obtain ⟨B, hB, hBX⟩ := hX.exists_isBase_subset
  rw [le_antisymm_iff, and_iff_right (M.eRk_le_eRank _), ← hB.eRk]
  exact M.eRk_mono hBX

lemma Spanning.eRank_restrict (hX : M.Spanning X) : (M ↾ X).eRank = M.eRank := by
  rw [eRank_def, restrict_ground_eq, restrict_eRk_eq _ rfl.subset, hX.eRk_eq]

lemma IsLoop.eRk_eq (he : M.IsLoop e) : M.eRk {e} = 0 := by
  rw [← eRk_closure_eq, he.closure, eRk_closure_eq, eRk_empty]

lemma IsNonloop.eRk_eq (he : M.IsNonloop e) : M.eRk {e} = 1 := by
  rw [← he.indep.isBasis_self.encard_eq_eRk, encard_singleton]

lemma eRk_singleton_eq [Loopless M] (he : e ∈ M.E := by aesop_mat) :
    M.eRk {e} = 1 :=
  (M.toIsNonloop he).eRk_eq

@[simp] lemma eRk_singleton_eq_one_iff {e : α} : M.eRk {e} = 1 ↔ M.IsNonloop e := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.eRk_eq⟩
  rwa [← indep_singleton, indep_iff_eRk_eq_encard_of_finite (by simp), encard_singleton]

lemma IsLoopEquiv.eRk_eq_eRk (h : M.IsLoopEquiv X Y) : M.eRk X = M.eRk Y := by
  rw [← M.eRk_closure_eq, h.closure_eq_closure, M.eRk_closure_eq]

lemma eRk_eq_zero_iff (hX : X ⊆ M.E := by aesop_mat) :
    M.eRk X = 0 ↔ X ⊆ M.loops := by
  obtain ⟨I, hI⟩ := M.exists_isBasis X
  rw [← hI.encard_eq_eRk, encard_eq_zero]
  exact ⟨by rintro rfl; exact hI.subset_closure, fun h ↦ eq_empty_of_forall_not_mem
    fun x hx ↦ (hI.indep.isNonloop_of_mem hx).not_isLoop (h (hI.subset hx))⟩

lemma eRk_eq_zero_iff' : M.eRk X = 0 ↔ X ∩ M.E ⊆ M.loops := by
  rw [← eRk_inter_ground, eRk_eq_zero_iff]

@[simp] lemma eRk_loops (M : Matroid α) : M.eRk M.loops = 0 := by
  rw [eRk_eq_zero_iff]

lemma eRk_eq_one_iff (hX : X ⊆ M.E := by aesop_mat) :
    M.eRk X = 1 ↔ ∃ e ∈ X, M.IsNonloop e ∧ X ⊆ M.closure {e} := by
  refine ⟨?_, fun ⟨e, heX, he, hXe⟩ ↦ ?_⟩
  · obtain ⟨I, hI⟩ := M.exists_isBasis X
    rw [hI.eRk_eq_encard, encard_eq_one]
    rintro ⟨e, rfl⟩
    exact ⟨e, singleton_subset_iff.1 hI.subset, indep_singleton.1 hI.indep, hI.subset_closure⟩
  rw [← he.eRk_eq]
  exact ((M.eRk_mono hXe).trans (M.eRk_closure_eq _).le).antisymm
    (M.eRk_mono (singleton_subset_iff.2 heX))

lemma eRk_le_one_iff [M.Nonempty] (hX : X ⊆ M.E := by aesop_mat) :
    M.eRk X ≤ 1 ↔ ∃ e ∈ M.E, X ⊆ M.closure {e} := by
  refine ⟨fun h ↦ ?_, fun ⟨e, _, he⟩ ↦ ?_⟩
  · obtain ⟨I, hI⟩ := M.exists_isBasis X
    rw [hI.eRk_eq_encard, encard_le_one_iff_eq] at h
    obtain (rfl | ⟨e, rfl⟩) := h
    · exact ⟨M.ground_nonempty.some, M.ground_nonempty.some_mem,
        hI.subset_closure.trans ((M.closure_subset_closure (empty_subset _)))⟩
    exact ⟨e, hI.indep.subset_ground rfl,  hI.subset_closure⟩
  refine (M.eRk_mono he).trans ?_
  rw [eRk_closure_eq, ← encard_singleton e]
  exact M.eRk_le_encard {e}

lemma IsBase.encard_compl_eq (hB : M.IsBase B) : (M.E \ B).encard = M✶.eRank :=
  (hB.compl_isBase_dual).encard_eq_eRank

lemma dual_eRk_add_eRank (M : Matroid α) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    M✶.eRk X + M.eRank = M.eRk (M.E \ X) + X.encard := by
  obtain ⟨I, hI⟩ := M✶.exists_isBasis X
  obtain ⟨B, hB, hIB⟩ := hI.indep.exists_isBase_superset
  obtain rfl : I = X ∩ B :=
    hI.eq_of_subset_indep (hB.indep.inter_left X) (subset_inter hI.subset hIB) inter_subset_left
  rw [inter_comm] at hI
  have hIdual : M.IsBasis (M.E \ B ∩ (M.E \ X)) (M.E \ X) :=
    by simpa using hB.inter_isBasis_iff_compl_inter_isBasis_dual.1 hI
  rw [← hIdual.encard_eq_eRk, ← hI.encard_eq_eRk, ← hB.compl_isBase_of_dual.encard_eq_eRank,
    ← encard_union_eq, ← encard_union_eq]
  · convert rfl using 2
    ext x
    simp only [mem_union, mem_inter_iff, mem_diff]
    tauto
  · exact disjoint_sdiff_left.mono_left inter_subset_right
  exact disjoint_sdiff_right.mono_left inter_subset_left

lemma dual_eRk_add_eRank' (M : Matroid α) (X : Set α) :
    M✶.eRk X + M.eRank = M.eRk (M.E \ X) + (X ∩ M.E).encard := by
  rw [← diff_inter_self_eq_diff, ← dual_eRk_add_eRank .., ← dual_ground, eRk_inter_ground]

lemma eRank_add_dual_eRank (M : Matroid α) : M.eRank + M✶.eRank = M.E.encard := by
  obtain ⟨B, hB⟩ := M.exists_isBase
  rw [← hB.encard_eq_eRank, ← hB.compl_isBase_dual.encard_eq_eRank,
    ← encard_union_eq disjoint_sdiff_right, union_diff_cancel hB.subset_ground]

lemma IsCircuit.eRk_add_one_eq {C : Set α} (hC : M.IsCircuit C) : M.eRk C + 1 = C.encard := by
  obtain ⟨I, hI⟩ := M.exists_isBasis C
  obtain ⟨e, ⟨heC, heI⟩, rfl⟩ := hC.isBasis_iff_insert_eq.1 hI
  rw [hI.eRk_eq_encard, encard_insert_of_not_mem heI]

end Basic

section Constructions

variable {E : Set α}

@[simp] lemma loopyOn_eRk_eq (E X : Set α) : (loopyOn E).eRk X = 0 := by
  obtain ⟨I, hI⟩ := (loopyOn E).exists_isBasis' X
  rw [hI.eRk_eq_encard, loopyOn_indep_iff.1 hI.indep, encard_empty]

@[simp] lemma loopyOn_eRank_eq (E : Set α) : (loopyOn E).eRank = 0 := by
  rw [eRank_def, loopyOn_eRk_eq]

-- @[simp] lemma loopyOn_rk_eq (E X : Set α) : (loopyOn E).r X = 0 := by
--   rw [← eRk_toNat_eq_rk, loopyOn_eRk_eq]; rfl

@[simp] lemma eRank_eq_zero_iff : M.eRank = 0 ↔ M = loopyOn M.E := by
  refine ⟨fun h ↦ closure_empty_eq_ground_iff.1 ?_, fun h ↦ by rw [h, loopyOn_eRank_eq]⟩
  obtain ⟨B, hB⟩ := M.exists_isBase
  rw [← hB.encard_eq_eRank, encard_eq_zero] at h
  rw [← h, hB.closure_eq]

lemma exists_of_eRank_eq_zero (h : M.eRank = 0) : ∃ E, M = loopyOn E :=
  ⟨M.E, by simpa using h⟩

@[simp] lemma eRank_loopyOn_eq_zero (α : Type*) : (emptyOn α).eRank = 0 := by
  rw [eRank_eq_zero_iff, emptyOn_ground, loopyOn_empty]

lemma eq_loopyOn_iff_eRank : M = loopyOn E ↔ M.eRank = 0 ∧ M.E = E :=
  ⟨fun h ↦ by rw [h]; simp, fun ⟨h,h'⟩ ↦ by rw [← h', ← eRank_eq_zero_iff, h]⟩

@[simp] lemma freeOn_eRank_eq (E : Set α) : (freeOn E).eRank = E.encard := by
  rw [eRank_def, freeOn_ground, (freeOn_indep_iff.2 rfl.subset).eRk_eq_encard]

lemma freeOn_eRk_eq (hXE : X ⊆ E) : (freeOn E).eRk X = X.encard := by
  obtain ⟨I, hI⟩ := (freeOn E).exists_isBasis X
  rw [hI.eRk_eq_encard, (freeOn_indep hXE).eq_of_isBasis hI]

-- lemma freeOn_rk_eq (hXE : X ⊆ E) : (freeOn E).r X = X.ncard := by
--   rw [← eRk_toNat_eq_rk, freeOn_eRk_eq hXE, ncard_def]

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

section Nullity
/-- The rank-deficiency of a set, as a term in `ℕ∞`. Cannot be defined with subtraction.
For the `ℕ` version, the simpler expression `X.ncard - M.r X` is preferable.

To reduce the number of `X ⊆ M.E` assumptions needed for lemmas,
this is defined so that junk elements in `X \ M.E` contribute to the nullity of `X` in `M`,
so `M.nullity X = M.nullity (X ∩ M.E) + (X \ M.E).encard`.
(see `Matroid.nullity_eq_nullity_inter_ground_add_encard_diff` )-/
noncomputable def nullity (M : Matroid α) (X : Set α) : ℕ∞ := (M ↾ X)✶.eRank

lemma nullity_eq_eRank_restrict_dual (M : Matroid α) (X : Set α) :
    M.nullity X = (M ↾ X)✶.eRank := rfl

lemma nullity_restrict_of_subset (M : Matroid α) (hXY : X ⊆ Y) :
    (M ↾ Y).nullity X = M.nullity X := by
  rw [nullity, restrict_restrict_eq _ hXY, nullity]

lemma nullity_restrict_self (M : Matroid α) (X : Set α) : (M ↾ X).nullity X = M.nullity X :=
  M.nullity_restrict_of_subset rfl.subset

lemma IsBasis'.nullity_eq (hIX : M.IsBasis' I X) : M.nullity X = (X \ I).encard := by
  rw [M.nullity_eq_eRank_restrict_dual,
    ← hIX.isBase_restrict.compl_isBase_dual.encard_eq_eRank, restrict_ground_eq]

lemma IsBasis.nullity_eq (hIX : M.IsBasis I X) : M.nullity X = (X \ I).encard :=
  hIX.isBasis'.nullity_eq

lemma eRk_add_nullity_eq_encard (M : Matroid α) (X : Set α) :
    M.eRk X + M.nullity X = X.encard := by
  have h := (M ↾ X)✶.eRank_add_dual_eRank
  simp only [dual_dual, eRank_restrict, dual_ground, restrict_ground_eq] at h
  rw [← h, add_comm, nullity_eq_eRank_restrict_dual]

lemma Indep.nullity_eq (hI : M.Indep I) : M.nullity I = 0 := by
  rw [hI.isBasis_self.nullity_eq, diff_self, encard_empty]

@[simp] lemma nullity_eq_zero : M.nullity I = 0 ↔ M.Indep I := by
  rw [iff_def, and_iff_left Indep.nullity_eq]
  obtain ⟨J, hJI⟩ := M.exists_isBasis' I
  rw [hJI.nullity_eq, encard_eq_zero, diff_eq_empty]
  exact hJI.indep.subset

lemma IsCircuit.nullity_eq {C : Set α} (hC : M.IsCircuit C) : M.nullity C = 1 := by
  rw [(hC.diff_singleton_isBasis hC.nonempty.some_mem).nullity_eq, diff_diff_cancel_left
     (by simpa using hC.nonempty.some_mem)]
  simp

lemma nullity_le_of_subset (M : Matroid α) (hXY : X ⊆ Y) : M.nullity X ≤ M.nullity Y := by
  rw [← M.nullity_restrict_of_subset hXY, ← M.nullity_restrict_self Y]
  obtain ⟨I, hI⟩ := (M ↾ Y).exists_isBasis X
  obtain ⟨B, hB, rfl⟩ := hI.exists_isBase
  rw [← isBasis_ground_iff, restrict_ground_eq] at hB
  rw [hI.nullity_eq, hB.nullity_eq, diff_inter_self_eq_diff]
  exact encard_le_encard (diff_subset_diff_left hXY)

lemma nullity_supermodular (M : Matroid α) (X Y : Set α) :
    M.nullity X + M.nullity Y ≤ M.nullity (X ∪ Y) + M.nullity (X ∩ Y) := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' (X ∩ Y)
  obtain ⟨Ix, hIx, hIIx⟩ := hI.exists_isBasis'_inter_eq_of_superset inter_subset_left
  obtain ⟨Iy, hIy, hIIy⟩ := hI.exists_isBasis'_inter_eq_of_superset inter_subset_right
  obtain ⟨Iu, hIu, hIxIu⟩ := hIx.exists_isBasis'_inter_eq_of_superset (Y := X ∪ Iy)
    subset_union_left
  have hIu' : M.IsBasis' Iu (X ∪ Y) := by
    rw [isBasis'_iff_isBasis_closure, ← closure_union_congr_right hIy.closure_eq_closure,
      and_iff_left (hIu.subset.trans (union_subset_union_right X hIy.subset))]
    exact hIu.isBasis_closure_right
  rw [hIx.nullity_eq, hIy.nullity_eq, hI.nullity_eq, hIu'.nullity_eq,
    ← encard_union_add_encard_inter]
  refine add_le_add (encard_le_encard ?_) (encard_le_encard ?_)
  · suffices Disjoint (X \ Ix) Iu ∧ Disjoint (Y \ Iy) Iu by
      simpa [subset_diff, diff_subset.trans subset_union_left, diff_subset.trans subset_union_right]
    rw [← hIxIu, diff_inter_self_eq_diff, and_iff_right disjoint_sdiff_left, disjoint_iff_forall_ne]
    rintro e ⟨heY, heIy⟩ _ heIu rfl
    have heX : e ∈ X := by simpa [heIy] using hIu.subset heIu
    exact heIy <| (hIIy.symm.subset <| hIIx.subset ⟨hIxIu.subset ⟨heIu, heX⟩, ⟨heX, heY⟩⟩).1
  rw [← hIIx, diff_inter_self_eq_diff, ← inter_diff_assoc, diff_eq, diff_eq, diff_eq,
    inter_assoc (a := X), inter_assoc X Y, inter_comm _ Y]
  exact inter_subset_left

lemma nullity_insert_eq_add_one (hecl : e ∈ M.closure X) (heX : e ∉ X) :
    M.nullity (insert e X) = M.nullity X + 1 := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  have hI' : M.IsBasis' I (insert e X) := by
    rw [isBasis'_iff_isBasis_closure, closure_insert_eq_of_mem_closure hecl]
    exact ⟨hI.isBasis_closure_right, hI.subset.trans <| subset_insert ..⟩
  rw [hI.nullity_eq, hI'.nullity_eq, insert_diff_of_not_mem _ (not_mem_subset hI.subset heX),
    encard_insert_of_not_mem (not_mem_subset diff_subset heX)]

lemma nullity_eq_nullity_inter_ground_add_encard_diff :
    M.nullity X = M.nullity (X ∩ M.E) + (X \ M.E).encard := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [hI.nullity_eq, hI.isBasis_inter_ground.nullity_eq, ← encard_union_eq]
  · nth_rw 1 [← inter_union_diff X M.E, union_diff_distrib, diff_diff,
      union_eq_self_of_subset_right hI.indep.subset_ground]
  exact disjoint_sdiff_right.mono_left (diff_subset.trans inter_subset_right)

lemma nullity_corestrict_univ_eq (M : Matroid α) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    (M✶ ↾ univ)✶.nullity X = M.nullity X := by
  nth_rw 2 [← M.corestrict_univ_restrict_ground]
  rw [nullity_restrict_of_subset _ hX]

lemma nullity_corestrict_univ_eq_nullity_inter (M : Matroid α) (X : Set α) :
    (M✶ ↾ univ)✶.nullity X = M.nullity (X ∩ M.E) := by
  obtain ⟨B, hB⟩ := M.exists_isBasis' X
  rw [hB.corestrict_univ_isBasis.nullity_eq, union_comm, ← diff_diff, sdiff_sdiff_right_self,
    hB.isBasis_inter_ground.nullity_eq]
  rfl

lemma nullity_insert (heX : e ∉ M.closure X) (heE : e ∈ M.E := by aesop_mat) :
    M.nullity (insert e X) = M.nullity X := by
  wlog hXE : X ⊆ M.E generalizing X with aux
  · rw [nullity_eq_nullity_inter_ground_add_encard_diff,
      insert_inter_of_mem heE, insert_diff_of_mem _ heE, aux (by simpa) (by simp),
      ← nullity_eq_nullity_inter_ground_add_encard_diff]
  obtain ⟨I, hI⟩ := M.exists_isBasis X
  rw [(hI.insert_isBasis_insert_of_not_mem_closure (by rwa [hI.closure_eq_closure])).nullity_eq,
    hI.nullity_eq]
  simp only [mem_insert_iff, true_or, insert_diff_of_mem]
  rw [diff_insert_of_not_mem (not_mem_subset (subset_closure ..) heX)]

lemma nullity_union_eq_nullity_add_encard_diff (hYX : Y ⊆ M.closure X) :
    M.nullity (X ∪ Y) = M.nullity X + (Y \ X).encard := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  have hI' : M.IsBasis' I (X ∪ Y) := by
    rw [isBasis'_iff_isBasis_closure, and_iff_left (hI.subset.trans subset_union_left),
      ← closure_union_closure_left_eq, union_eq_self_of_subset_right hYX, closure_closure]
    exact hI.isBasis_closure_right
  rw [hI.nullity_eq, hI'.nullity_eq, ← encard_union_eq (disjoint_sdiff_right.mono_left diff_subset)]
  congr
  have := hI.subset
  tauto_set

lemma nullity_eq_nullity_add_encard_diff (hXY : X ⊆ Y) (hYX : Y ⊆ M.closure X) :
    M.nullity Y = M.nullity X + (Y \ X).encard := by
  nth_rw 1 [← union_eq_self_of_subset_left hXY]
  exact nullity_union_eq_nullity_add_encard_diff hYX

lemma Disjoint.nullity_union_eq_of_subset_closure (hXY : Disjoint X Y) (hYX : Y ⊆ M.closure X) :
    M.nullity (X ∪ Y) = M.nullity X + Y.encard := by
  rw [nullity_union_eq_nullity_add_encard_diff hYX, hXY.sdiff_eq_right]

end Nullity

@[simp] lemma eRk_eq_top_iff : M.eRk X = ⊤ ↔ ¬ M.IsRkFinite X := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [hI.eRk_eq_encard, encard_eq_top_iff, ← hI.finite_iff_isRkFinite, Set.Infinite]

@[simp] lemma eRk_ne_top_iff : M.eRk X ≠ ⊤ ↔ M.IsRkFinite X := by
  rw [ne_eq, eRk_eq_top_iff, not_not]

@[simp] lemma eRk_lt_top_iff : M.eRk X < ⊤ ↔ M.IsRkFinite X := by
  rw [lt_top_iff_ne_top, eRk_ne_top_iff]

lemma IsRkFinite.eRk_lt_top (h : M.IsRkFinite X) : M.eRk X < ⊤ :=
  eRk_lt_top_iff.2 h

lemma IsRkFinite.eRk_ne_top (h : M.IsRkFinite X) : M.eRk X ≠ ⊤ :=
  h.eRk_lt_top.ne

lemma eRk_eq_iSup_finset_eRk (M : Matroid α) (X : Set α) :
    M.eRk X = ⨆ Y ∈ {S : Finset α | (S : Set α) ⊆ X}, M.eRk Y := by
  simp only [mem_setOf_eq, le_antisymm_iff, iSup_le_iff]
  refine ⟨?_, fun S hSX ↦ M.eRk_mono hSX⟩

  by_cases hX : M.IsRkFinite X
  · obtain ⟨I, hI⟩ := hX.exists_finset_isBasis'
    exact le_iSup₂_of_le (i := I) hI.subset <| by rw [hI.eRk_eq_eRk]

  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [← eRk_eq_top_iff] at hX
  rw [hX, top_le_iff, WithTop.eq_top_iff_forall_le]
  intro n
  rw [hI.eRk_eq_encard, encard_eq_top_iff] at hX
  obtain ⟨J, hJI, rfl⟩ := hX.exists_subset_card_eq n
  apply le_iSup₂_of_le J (hJI.trans hI.subset)
  rw [(hI.indep.subset hJI).eRk_eq_encard, encard_coe_eq_coe_finsetCard]
  rfl

lemma IsRkFinite.isBasis_of_subset_closure_of_subset_of_encard_le (hX : M.IsRkFinite X)
    (hXI : X ⊆ M.closure I) (hIX : I ⊆ X) (hI : I.encard ≤ M.eRk X) : M.IsBasis I X := by
  obtain ⟨J, hJ⟩ := M.exists_isBasis (I ∩ M.E)
  have hIJ := hJ.subset.trans inter_subset_left
  rw [← closure_inter_ground] at hXI
  replace hXI := hXI.trans <| M.closure_subset_closure_of_subset_closure hJ.subset_closure
  have hJX := hJ.indep.isBasis_of_subset_of_subset_closure (hIJ.trans hIX) hXI
  rw [← hJX.encard_eq_eRk] at hI
  rwa [← Finite.eq_of_subset_of_encard_le' (hX.finite_of_isBasis hJX) hIJ hI]

lemma IsRkFinite.closure_eq_closure_of_subset_of_eRk_ge_eRk (hX : M.IsRkFinite X) (hXY : X ⊆ Y)
    (hr : M.eRk Y ≤ M.eRk X) : M.closure X = M.closure Y := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_isBasis'_of_subset (hI.subset.trans hXY)
  rw [hI.eRk_eq_encard, hJ.eRk_eq_encard] at hr
  rw [← closure_inter_ground, ← M.closure_inter_ground Y,
    ← hI.isBasis_inter_ground.closure_eq_closure,
    ← hJ.isBasis_inter_ground.closure_eq_closure, Finite.eq_of_subset_of_encard_le'
      (hI.indep.finite_of_subset_isRkFinite hI.subset hX) hIJ hr]

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

lemma eRank_lt_top (M : Matroid α) [RankFinite M] : M.eRank < ⊤ := by
  rwa [eRank_def, eRk_lt_top_iff, isRkFinite_ground_iff_rankFinite]

lemma IsRkFinite.indep_of_encard_le_eRk (hX : M.IsRkFinite I) (h : encard I ≤ M.eRk I) :
    M.Indep I := by
  rw [indep_iff_eRk_eq_encard_of_finite _]
  · exact (M.eRk_le_encard I).antisymm h
  simpa using h.trans_lt hX.eRk_lt_top
