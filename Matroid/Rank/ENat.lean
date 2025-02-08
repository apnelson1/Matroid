import Matroid.Rank.Finite
import Matroid.Loop
import Matroid.ForMathlib.Other
import Matroid.ForMathlib.Matroid.Sum

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
noncomputable def eRank (M : Matroid α) : ℕ∞ := ⨆ (B : {B // M.Base B}), B.1.encard

/-- The rank `Matroid.eRk M X` of a set `X` is the `ℕ∞`-valued cardinality of each basis of `X`. -/
noncomputable abbrev eRk (M : Matroid α) (X : Set α) : ℕ∞ := (M ↾ X).eRank

lemma eRank_def (M : Matroid α) : M.eRank = M.eRk M.E := by
  rw [eRk, restrict_ground_eq_self]

@[simp] lemma eRank_restrict (M : Matroid α) (X : Set α) : (M ↾ X).eRank = M.eRk X := rfl

lemma Base.encard_eq_eRank (hB : M.Base B) : B.encard = M.eRank := by
  simp [eRank, show ∀ B' : {B // M.Base B}, B'.1.encard = B.encard from
    fun B' ↦ B'.2.card_eq_card_of_base hB]

lemma Basis'.encard_eq_eRk (hI : M.Basis' I X) : I.encard = M.eRk X :=
  hI.base_restrict.encard_eq_eRank

lemma Basis.encard_eq_eRk (hI : M.Basis I X) : I.encard = M.eRk X :=
  hI.basis'.encard_eq_eRk

lemma eq_eRk_iff (hX : X ⊆ M.E := by aesop_mat) :
    M.eRk X = n ↔ ∃ I, M.Basis I X ∧ I.encard = n :=
  ⟨fun h ↦ (M.exists_basis X).elim (fun I hI ↦ ⟨I, hI, by rw [hI.encard_eq_eRk, ← h]⟩),
    fun ⟨I, hI, hIc⟩ ↦ by rw [← hI.encard_eq_eRk, hIc]⟩

lemma Indep.eRk_eq_encard (hI : M.Indep I) : M.eRk I = I.encard :=
  (eq_eRk_iff hI.subset_ground).mpr ⟨I, hI.basis_self, rfl⟩

lemma Basis'.eRk_eq_eRk (hIX : M.Basis' I X) : M.eRk I = M.eRk X := by
  rw [← hIX.encard_eq_eRk, hIX.indep.eRk_eq_encard]

lemma Basis.eRk (hIX : M.Basis I X) : M.eRk I = M.eRk X := by
  rw [← hIX.encard_eq_eRk, hIX.indep.eRk_eq_encard]

lemma Basis'.eRk_eq_encard (hIX : M.Basis' I X) : M.eRk X = I.encard := by
  rw [← hIX.eRk_eq_eRk, hIX.indep.eRk_eq_encard]

lemma Basis.eRk_eq_encard (hIX : M.Basis I X) : M.eRk X = I.encard := by
  rw [← hIX.eRk, hIX.indep.eRk_eq_encard]

lemma Base.eRk (hB : M.Base B) : M.eRk B = M.eRank := by
  rw [hB.indep.eRk_eq_encard, eRank_def, hB.basis_ground.encard_eq_eRk]

@[simp] lemma eRank_map {β : Type*} (M : Matroid α) (f : α → β) (hf : InjOn f M.E) :
    (M.map f hf).eRank = M.eRank := by
  obtain ⟨B, hB⟩ := M.exists_base
  rw [← (hB.map hf).encard_eq_eRank, ← hB.encard_eq_eRank, (hf.mono hB.subset_ground).encard_image]

@[simp] lemma eRank_loopyOn (E : Set α) : (loopyOn E).eRank = 0 := by
  simp [← (show (loopyOn E).Base ∅ by simp).encard_eq_eRank]

@[simp] lemma eRank_emptyOn (α : Type*) : (emptyOn α).eRank = 0 := by
  simp [← (show (emptyOn α).Base ∅ by simp).encard_eq_eRank]

@[simp] lemma eRk_ground (M : Matroid α) : M.eRk M.E = M.eRank :=
  M.eRank_def.symm

@[simp] lemma eRk_inter_ground (M : Matroid α) (X : Set α) : M.eRk (X ∩ M.E) = M.eRk X := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  rw [← hI.eRk_eq_eRk, hI.basis_inter_ground.eRk]

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

lemma one_le_eRank (M : Matroid α) [RkPos M] : 1 ≤ M.eRank := by
  obtain ⟨B, hB⟩ := M.exists_base
  rw [← hB.encard_eq_eRank, one_le_encard_iff_nonempty]
  exact hB.nonempty

lemma finiteRk_iff_eRank_ne_top : M.FiniteRk ↔ M.eRank ≠ ⊤ := by
  obtain ⟨B, hB⟩ := M.exists_base
  rw [← hB.encard_eq_eRank, encard_ne_top_iff]
  exact ⟨fun h ↦ hB.finite, fun h ↦ hB.finiteRk_of_finite h⟩

@[simp] lemma eRk_map_eq {β : Type*} {f : α → β} (M : Matroid α) (hf : InjOn f M.E)
    (hX : X ⊆ M.E := by aesop_mat) : (M.map f hf).eRk (f '' X) = M.eRk X := by
  obtain ⟨I, hI⟩ := M.exists_basis X
  rw [hI.eRk_eq_encard, (hI.map hf).eRk_eq_encard, (hf.mono hI.indep.subset_ground).encard_image]

@[simp] lemma eRk_comap_eq {β : Type*} {f : α → β} (M : Matroid β) (X : Set α) :
    (M.comap f).eRk X = M.eRk (f '' X) := by
  obtain ⟨I, hI⟩ := (M.comap f).exists_basis' X
  obtain ⟨hI', hinj, -⟩ := comap_basis'_iff.1 hI
  rw [← hI.encard_eq_eRk, ← hI'.encard_eq_eRk, hinj.encard_image]

-- lemma Iso.eRk_image_eq {α β : Type*} {M : Matroid α} {N : Matroid β} (e : Iso M N) (X : Set α)
--     (hX : X ⊆ M.E := by aesop_mat) : N.eRk (e '' X) = M.eRk X := by
--   obtain ⟨I,hI⟩ := M.exists_basis X
--   rw [hI.eRk_eq_encard, (e.on_basis hI).eRk_eq_encard,
--     (e.injOn_ground.mono hI.subset_ground).encard_image]

@[simp] lemma eRk_univ_eq (M : Matroid α) : M.eRk univ = M.eRank := by
  rw [← eRk_inter_ground, univ_inter, eRank_def]


-- lemma Iso.eRank_eq_eRank {α β : Type*} {M : Matroid α} {N : Matroid β} (e : Iso M N) :
--     M.eRank = N.eRank := by
--   rw [eRank_def, ← e.eRk_image_eq M.E, e.image_ground, eRank_def]

@[simp] lemma eRk_empty (M : Matroid α) : M.eRk ∅ = 0 := by
  rw [← M.empty_indep.basis_self.encard_eq_eRk, encard_empty]

@[simp] lemma eRk_closure_eq (M : Matroid α) (X : Set α) : M.eRk (M.closure X) = M.eRk X := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  rw [← hI.closure_eq_closure, ← hI.indep.basis_closure.encard_eq_eRk, hI.encard_eq_eRk]

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
  obtain ⟨I, hI⟩ := (M ↾ R).exists_basis' X
  rw [hI.eRk_eq_encard]
  rw [basis'_iff_basis_inter_ground, basis_restrict_iff', restrict_ground_eq] at hI
  rw [← eRk_inter_ground, ← hI.1.eRk_eq_encard]

@[simp] lemma restrict_eRk_eq (M : Matroid α) (h : X ⊆ R) : (M ↾ R).eRk X = M.eRk X := by
  rw [restrict_eRk_eq', inter_eq_self_of_subset_left h]

lemma eRk_lt_top_of_finite (M : Matroid α) (hX : X.Finite) : M.eRk X < ⊤ := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  rw [hI.eRk_eq_encard, encard_lt_top_iff]
  exact hX.subset hI.subset

lemma Basis'.eRk_eq_eRk_union (hIX : M.Basis' I X) (Y : Set α) : M.eRk (I ∪ Y) = M.eRk (X ∪ Y) := by
  rw [← eRk_union_closure_left_eq, hIX.closure_eq_closure, eRk_union_closure_left_eq]

lemma Basis'.eRk_eq_eRk_insert (hIX : M.Basis' I X) (e : α) :
    M.eRk (insert e I) = M.eRk (insert e X) := by
  rw [← union_singleton, hIX.eRk_eq_eRk_union, union_singleton]

lemma Basis.eRk_eq_eRk_union (hIX : M.Basis I X) (Y : Set α) : M.eRk (I ∪ Y) = M.eRk (X ∪ Y) :=
  hIX.basis'.eRk_eq_eRk_union Y

lemma Basis.eRk_eq_eRk_insert (hIX : M.Basis I X) (e : α) :
    M.eRk (insert e I) = M.eRk (insert e X) :=
  by rw [← union_singleton, hIX.eRk_eq_eRk_union, union_singleton]

lemma eRk_le_encard (M : Matroid α) (X : Set α) : M.eRk X ≤ X.encard := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  rw [hI.eRk_eq_encard]
  exact encard_mono hI.subset

lemma eRank_le_encard_ground (M : Matroid α) : M.eRank ≤ M.E.encard :=
  M.eRank_def.trans_le <| M.eRk_le_encard M.E

lemma eRk_mono (M : Matroid α) : Monotone M.eRk := by
  rintro X Y (hXY : X ⊆ Y)
  obtain ⟨I, hI⟩ := M.exists_basis' X
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_basis'_of_subset (hI.subset.trans hXY)
  rw [hI.eRk_eq_encard, hJ.eRk_eq_encard]
  exact encard_mono hIJ

lemma eRk_le_eRank (M : Matroid α) (X : Set α) : M.eRk X ≤ M.eRank := by
  rw [eRank_def, ← eRk_inter_ground]; exact M.eRk_mono inter_subset_right

lemma le_eRk_iff : n ≤ M.eRk X ↔ ∃ I, I ⊆ X ∧ M.Indep I ∧ I.encard = n := by
  refine ⟨fun h ↦ ?_, fun ⟨I, hIX, hI, hIc⟩ ↦ ?_⟩
  · obtain ⟨J, hJ⟩ := M.exists_basis' X
    rw [← hJ.encard_eq_eRk] at h
    obtain ⟨I, hIJ, rfl⟩ :=  exists_subset_encard_eq h
    exact ⟨_, hIJ.trans hJ.subset, hJ.indep.subset hIJ, rfl⟩
  rw [← hIc, ← hI.eRk_eq_encard]
  exact M.eRk_mono hIX

lemma eRk_le_iff : M.eRk X ≤ n ↔ ∀ {I}, I ⊆ X → M.Indep I → I.encard ≤ n := by
  refine ⟨fun h I hIX hI ↦ (hI.eRk_eq_encard.symm.trans_le ((M.eRk_mono hIX).trans h)), fun h ↦ ?_⟩
  obtain ⟨I, hI⟩ := M.exists_basis' X
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
  obtain ⟨Ii, hIi⟩ := M.exists_basis' (X ∩ Y)
  obtain ⟨IX, hIX, hIX'⟩ :=
    hIi.indep.subset_basis'_of_subset (hIi.subset.trans inter_subset_left)
  obtain ⟨IY, hIY, hIY'⟩ :=
    hIi.indep.subset_basis'_of_subset (hIi.subset.trans inter_subset_right)
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
  obtain ⟨J, hJ⟩ := M.exists_basis' I
  rw [← hI.eq_of_subset_of_encard_le hJ.subset]
  · exact hJ.indep
  rw [← h, ← hJ.eRk_eq_encard]

lemma indep_iff_eRk_eq_card [M.Finite] (hI : I ⊆ M.E := by aesop_mat) :
    M.Indep I ↔ M.eRk I = I.encard :=
  indep_iff_eRk_eq_encard_of_finite (M.set_finite I)

lemma eRk_singleton_le (M : Matroid α) (e : α) : M.eRk {e} ≤ 1 := by
  obtain ⟨J, hJ⟩ := M.exists_basis' {e}
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

lemma basis'_iff_indep_encard_eq_of_finite (hIfin : I.Finite) :
    M.Basis' I X ↔ I ⊆ X ∧ M.Indep I ∧ I.encard = M.eRk X := by
  refine ⟨fun h ↦ ⟨h.subset,h.indep, h.eRk_eq_encard.symm⟩, fun ⟨hIX, hI, hcard⟩ ↦ ?_⟩
  rw [basis'_iff_basis_inter_ground]
  obtain ⟨J, hJ, hIJ⟩ := hI.subset_basis_of_subset (subset_inter hIX hI.subset_ground)
  apply hI.basis_of_subset_of_subset_closure (subset_inter hIX hI.subset_ground)
  obtain rfl := hIfin.eq_of_subset_of_encard_le' hIJ
    (by rw [hcard, ← hJ.eRk_eq_encard, eRk_inter_ground ])
  exact hJ.subset_closure

lemma basis_iff_indep_encard_eq_of_finite (hIfin : I.Finite) (hX : X ⊆ M.E := by aesop_mat) :
    M.Basis I X ↔ I ⊆ X ∧ M.Indep I ∧ I.encard = M.eRk X := by
  rw [← basis'_iff_basis, basis'_iff_indep_encard_eq_of_finite hIfin]

lemma Indep.basis_of_subset_of_eRk_le_of_finite (hI : M.Indep I) (hIX : I ⊆ X)
    (h : M.eRk X ≤ M.eRk I) (hIfin : I.Finite) (hX : X ⊆ M.E := by aesop_mat) : M.Basis I X := by
  rw [basis_iff_indep_encard_eq_of_finite hIfin hX, and_iff_right hIX, and_iff_right hI,
     le_antisymm_iff, and_iff_left (h.trans hI.eRk_eq_encard.le), ← hI.eRk_eq_encard]
  exact M.eRk_mono hIX

lemma Indep.base_of_encard (hI : M.Indep I) (hIfin : I.Finite) (hIcard : M.eRank ≤ I.encard) :
    M.Base I := by
  rw [← basis_ground_iff]
  refine hI.basis_of_subset_of_eRk_le_of_finite hI.subset_ground ?_ hIfin
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
  obtain ⟨I, hI⟩ := M.exists_basis' X
  rw [← hI.closure_eq_closure] at he
  rw [← eRk_closure_eq, ← closure_insert_closure_eq_closure_insert, ← hI.closure_eq_closure,
    hI.eRk_eq_encard, closure_insert_closure_eq_closure_insert, eRk_closure_eq, Indep.eRk_eq_encard,
    encard_insert_of_not_mem]
  · exact fun heI ↦ he.2 (M.subset_closure I hI.indep.subset_ground heI)
  rw [hI.indep.insert_indep_iff]
  exact Or.inl he

lemma eRk_augment (h : M.eRk X < M.eRk Z) : ∃ z ∈ Z \ X, M.eRk (insert z X) = M.eRk X + 1 := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_basis'_of_subset (hI.subset.trans subset_union_left)
  have hlt := h.trans_le (M.eRk_mono (subset_union_right (s := X)))
  rw [hI.eRk_eq_encard, hJ.eRk_eq_encard] at hlt
  obtain ⟨e, heJ, heI⟩ := exists_of_ssubset (hIJ.ssubset_of_ne (by rintro rfl; exact hlt.ne rfl))
  have heIi : M.Indep (insert e I) := hJ.indep.subset (insert_subset heJ hIJ)
  have heX : e ∉ X := fun h ↦
    heI (hI.basis_inter_ground.mem_of_insert_indep ⟨h, hJ.indep.subset_ground heJ⟩ heIi)
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

lemma spanning_iff_eRk' [FiniteRk M] : M.Spanning X ↔ M.eRank ≤ M.eRk X ∧ X ⊆ M.E := by
  refine ⟨fun h ↦ ?_, fun ⟨hr, hX⟩ ↦ ?_⟩
  · rw [eRank_def, ← eRk_closure_eq _ X, h.closure_eq]; exact ⟨rfl.le, h.subset_ground⟩
  obtain ⟨J, hJ⟩ := M.exists_basis X
  obtain ⟨B, hB, hJB⟩ := hJ.indep.exists_base_superset
  rw [← hJ.encard_eq_eRk, ← hB.encard_eq_eRank] at hr
  obtain rfl := hB.finite.eq_of_subset_of_encard_le hJB hr
  rw [spanning_iff_exists_base_subset]
  exact ⟨J, hB, hJ.subset⟩

lemma spanning_iff_eRk [FiniteRk M] (hX : X ⊆ M.E := by aesop_mat) :
    M.Spanning X ↔ M.eRank ≤ M.eRk X := by
  rw [spanning_iff_eRk', and_iff_left hX]

lemma Spanning.eRk_eq (hX : M.Spanning X) : M.eRk X = M.eRank := by
  obtain ⟨B, hB, hBX⟩ := hX.exists_base_subset
  rw [le_antisymm_iff, and_iff_right (M.eRk_le_eRank _), ← hB.eRk]
  exact M.eRk_mono hBX

lemma Spanning.eRank_restrict (hX : M.Spanning X) : (M ↾ X).eRank = M.eRank := by
  rw [eRank_def, restrict_ground_eq, restrict_eRk_eq _ rfl.subset, hX.eRk_eq]

lemma Loop.eRk_eq (he : M.Loop e) : M.eRk {e} = 0 := by
  rw [← eRk_closure_eq, he.closure, eRk_closure_eq, eRk_empty]

lemma Nonloop.eRk_eq (he : M.Nonloop e) : M.eRk {e} = 1 := by
  rw [← he.indep.basis_self.encard_eq_eRk, encard_singleton]

lemma eRk_singleton_eq [Loopless M] (he : e ∈ M.E := by aesop_mat) :
    M.eRk {e} = 1 :=
  (M.toNonloop he).eRk_eq

@[simp] lemma eRk_singleton_eq_one_iff {e : α} : M.eRk {e} = 1 ↔ M.Nonloop e := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.eRk_eq⟩
  rwa [← indep_singleton, indep_iff_eRk_eq_encard_of_finite (by simp), encard_singleton]

lemma LoopEquiv.eRk_eq_eRk (h : M.LoopEquiv X Y) : M.eRk X = M.eRk Y := by
  rw [← M.eRk_closure_eq, h.closure_eq_closure, M.eRk_closure_eq]

lemma eRk_eq_zero_iff (hX : X ⊆ M.E := by aesop_mat) :
    M.eRk X = 0 ↔ X ⊆ M.closure ∅ := by
  obtain ⟨I, hI⟩ := M.exists_basis X
  rw [← hI.encard_eq_eRk, encard_eq_zero]
  exact ⟨by rintro rfl; exact hI.subset_closure, fun h ↦ eq_empty_of_forall_not_mem
    fun x hx ↦ (hI.indep.nonloop_of_mem hx).not_loop (h (hI.subset hx))⟩

lemma eRk_eq_zero_iff' : M.eRk X = 0 ↔ X ∩ M.E ⊆ M.closure ∅ := by
  rw [← eRk_inter_ground, eRk_eq_zero_iff]

@[simp] lemma eRk_loops (M : Matroid α) : M.eRk (M.closure ∅) = 0 := by
  rw [eRk_eq_zero_iff]

lemma eRk_eq_one_iff (hX : X ⊆ M.E := by aesop_mat) :
    M.eRk X = 1 ↔ ∃ e ∈ X, M.Nonloop e ∧ X ⊆ M.closure {e} := by
  refine ⟨?_, fun ⟨e, heX, he, hXe⟩ ↦ ?_⟩
  · obtain ⟨I, hI⟩ := M.exists_basis X
    rw [hI.eRk_eq_encard, encard_eq_one]
    rintro ⟨e, rfl⟩
    exact ⟨e, singleton_subset_iff.1 hI.subset, indep_singleton.1 hI.indep, hI.subset_closure⟩
  rw [← he.eRk_eq]
  exact ((M.eRk_mono hXe).trans (M.eRk_closure_eq _).le).antisymm
    (M.eRk_mono (singleton_subset_iff.2 heX))

lemma eRk_le_one_iff [M.Nonempty] (hX : X ⊆ M.E := by aesop_mat) :
    M.eRk X ≤ 1 ↔ ∃ e ∈ M.E, X ⊆ M.closure {e} := by
  refine ⟨fun h ↦ ?_, fun ⟨e, _, he⟩ ↦ ?_⟩
  · obtain ⟨I, hI⟩ := M.exists_basis X
    rw [hI.eRk_eq_encard, encard_le_one_iff_eq] at h
    obtain (rfl | ⟨e, rfl⟩) := h
    · exact ⟨M.ground_nonempty.some, M.ground_nonempty.some_mem,
        hI.subset_closure.trans ((M.closure_subset_closure (empty_subset _)))⟩
    exact ⟨e, hI.indep.subset_ground rfl,  hI.subset_closure⟩
  refine (M.eRk_mono he).trans ?_
  rw [eRk_closure_eq, ← encard_singleton e]
  exact M.eRk_le_encard {e}

lemma Base.encard_compl_eq (hB : M.Base B) : (M.E \ B).encard = M✶.eRank :=
  (hB.compl_base_dual).encard_eq_eRank

lemma dual_eRk_add_eRank (M : Matroid α) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    M✶.eRk X + M.eRank = M.eRk (M.E \ X) + X.encard := by
  obtain ⟨I, hI⟩ := M✶.exists_basis X
  obtain ⟨B, hB, hIB⟩ := hI.indep.exists_base_superset
  obtain rfl : I = X ∩ B :=
    hI.eq_of_subset_indep (hB.indep.inter_left X) (subset_inter hI.subset hIB) inter_subset_left
  rw [inter_comm] at hI
  have hIdual : M.Basis (M.E \ B ∩ (M.E \ X)) (M.E \ X) :=
    by simpa using hB.inter_basis_iff_compl_inter_basis_dual.1 hI
  rw [← hIdual.encard_eq_eRk, ← hI.encard_eq_eRk, ← hB.compl_base_of_dual.encard_eq_eRank,
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
  obtain ⟨B, hB⟩ := M.exists_base
  rw [← hB.encard_eq_eRank, ← hB.compl_base_dual.encard_eq_eRank,
    ← encard_union_eq disjoint_sdiff_right, union_diff_cancel hB.subset_ground]

lemma Circuit.eRk_add_one_eq {C : Set α} (hC : M.Circuit C) : M.eRk C + 1 = C.encard := by
  obtain ⟨I, hI⟩ := M.exists_basis C
  obtain ⟨e, ⟨heC, heI⟩, rfl⟩ := hC.basis_iff_insert_eq.1 hI
  rw [hI.eRk_eq_encard, encard_insert_of_not_mem heI]

end Basic

section Constructions

variable {E : Set α}

@[simp] lemma loopyOn_eRk_eq (E X : Set α) : (loopyOn E).eRk X = 0 := by
  obtain ⟨I, hI⟩ := (loopyOn E).exists_basis' X
  rw [hI.eRk_eq_encard, loopyOn_indep_iff.1 hI.indep, encard_empty]

@[simp] lemma loopyOn_eRank_eq (E : Set α) : (loopyOn E).eRank = 0 := by
  rw [eRank_def, loopyOn_eRk_eq]

-- @[simp] lemma loopyOn_rk_eq (E X : Set α) : (loopyOn E).r X = 0 := by
--   rw [← eRk_toNat_eq_rk, loopyOn_eRk_eq]; rfl

@[simp] lemma eRank_eq_zero_iff : M.eRank = 0 ↔ M = loopyOn M.E := by
  refine ⟨fun h ↦ closure_empty_eq_ground_iff.1 ?_, fun h ↦ by rw [h, loopyOn_eRank_eq]⟩
  obtain ⟨B, hB⟩ := M.exists_base
  rw [← hB.encard_eq_eRank, encard_eq_zero] at h
  rw [← h, hB.closure_eq]

lemma exists_of_eRank_eq_zero (h : M.eRank = 0) : ∃ E, M = loopyOn E :=
  ⟨M.E, by simpa using h⟩

@[simp] lemma eRank_loopyOn_eq_zero (α : Type*) : (emptyOn α).eRank = 0 := by
  rw [eRank_eq_zero_iff, emptyOn_ground, loopyOn_empty]

lemma eq_loopyOn_iff_closure : M = loopyOn E ↔ M.closure ∅ = E ∧ M.E = E :=
  ⟨fun h ↦ by rw [h]; simp, fun ⟨h,h'⟩ ↦ by rw [← h', ← closure_empty_eq_ground_iff, h, h']⟩

lemma eq_loopyOn_iff_eRank : M = loopyOn E ↔ M.eRank = 0 ∧ M.E = E :=
  ⟨fun h ↦ by rw [h]; simp, fun ⟨h,h'⟩ ↦ by rw [← h', ← eRank_eq_zero_iff, h]⟩

@[simp] lemma freeOn_eRank_eq (E : Set α) : (freeOn E).eRank = E.encard := by
  rw [eRank_def, freeOn_ground, (freeOn_indep_iff.2 rfl.subset).eRk_eq_encard]

lemma freeOn_eRk_eq (hXE : X ⊆ E) : (freeOn E).eRk X = X.encard := by
  obtain ⟨I, hI⟩ := (freeOn E).exists_basis X
  rw [hI.eRk_eq_encard, (freeOn_indep hXE).eq_of_basis hI]

-- lemma freeOn_rk_eq (hXE : X ⊆ E) : (freeOn E).r X = X.ncard := by
--   rw [← eRk_toNat_eq_rk, freeOn_eRk_eq hXE, ncard_def]

@[simp] lemma disjointSum_eRk_eq (M N : Matroid α) (hMN : Disjoint M.E N.E) (X : Set α) :
    (M.disjointSum N hMN).eRk X = M.eRk (X ∩ M.E) + N.eRk (X ∩ N.E) := by
  obtain ⟨B₁, hB₁⟩ := M.exists_basis (X ∩ M.E)
  obtain ⟨B₂, hB₂⟩ := N.exists_basis (X ∩ N.E)
  rw [← eRk_inter_ground, disjointSum_ground_eq, inter_union_distrib_left,
    (hB₁.disjointSum_basis_union hB₂ hMN).eRk_eq_encard, hB₁.eRk_eq_encard, hB₂.eRk_eq_encard,
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

lemma Basis'.nullity_eq (hIX : M.Basis' I X) : M.nullity X = (X \ I).encard := by
  rw [M.nullity_eq_eRank_restrict_dual,
    ← (base_restrict_iff'.2 hIX).compl_base_dual.encard_eq_eRank, restrict_ground_eq]

lemma Basis.nullity_eq (hIX : M.Basis I X) : M.nullity X = (X \ I).encard :=
  hIX.basis'.nullity_eq

lemma eRk_add_nullity_eq_encard (M : Matroid α) (X : Set α) :
    M.eRk X + M.nullity X = X.encard := by
  have h := (M ↾ X)✶.eRank_add_dual_eRank
  simp only [dual_dual, eRank_restrict, dual_ground, restrict_ground_eq] at h
  rw [← h, add_comm, nullity_eq_eRank_restrict_dual]

lemma Indep.nullity_eq (hI : M.Indep I) : M.nullity I = 0 := by
  rw [hI.basis_self.nullity_eq, diff_self, encard_empty]

@[simp] lemma nullity_eq_zero : M.nullity I = 0 ↔ M.Indep I := by
  rw [iff_def, and_iff_left Indep.nullity_eq]
  obtain ⟨J, hJI⟩ := M.exists_basis' I
  rw [hJI.nullity_eq, encard_eq_zero, diff_eq_empty]
  exact hJI.indep.subset

lemma nullity_eq_nullity_inter_ground_add_encard_diff :
    M.nullity X = M.nullity (X ∩ M.E) + (X \ M.E).encard := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  rw [hI.nullity_eq, hI.basis_inter_ground.nullity_eq, ← encard_union_eq]
  · nth_rw 1 [← inter_union_diff X M.E, union_diff_distrib, diff_diff,
      union_eq_self_of_subset_right hI.indep.subset_ground]
  exact disjoint_sdiff_right.mono_left (diff_subset.trans inter_subset_right)

lemma nullity_le_of_subset (M : Matroid α) (hXY : X ⊆ Y) : M.nullity X ≤ M.nullity Y := by
  rw [← M.nullity_restrict_of_subset hXY, ← M.nullity_restrict_self Y]
  obtain ⟨I, hI⟩ := (M ↾ Y).exists_basis X
  obtain ⟨B, hB, rfl⟩ := hI.exists_base
  rw [← basis_ground_iff, restrict_ground_eq] at hB
  rw [hI.nullity_eq, hB.nullity_eq, diff_inter_self_eq_diff]
  exact encard_le_encard (diff_subset_diff_left hXY)

end Nullity

@[simp] lemma eRk_eq_top_iff : M.eRk X = ⊤ ↔ ¬ M.FinRk X := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  rw [hI.eRk_eq_encard, encard_eq_top_iff, ← hI.finite_iff_finRk, Set.Infinite]

@[simp] lemma eRk_ne_top_iff : M.eRk X ≠ ⊤ ↔ M.FinRk X := by
  rw [ne_eq, eRk_eq_top_iff, not_not]

@[simp] lemma eRk_lt_top_iff : M.eRk X < ⊤ ↔ M.FinRk X := by
  rw [lt_top_iff_ne_top, eRk_ne_top_iff]

lemma FinRk.eRk_lt_top (h : M.FinRk X) : M.eRk X < ⊤ :=
  eRk_lt_top_iff.2 h

lemma FinRk.eRk_ne_top (h : M.FinRk X) : M.eRk X ≠ ⊤ :=
  h.eRk_lt_top.ne

lemma eRk_eq_iSup_finset_eRk (M : Matroid α) (X : Set α) :
    M.eRk X = ⨆ Y ∈ {S : Finset α | (S : Set α) ⊆ X}, M.eRk Y := by
  simp only [mem_setOf_eq, le_antisymm_iff, iSup_le_iff]
  refine ⟨?_, fun S hSX ↦ M.eRk_mono hSX⟩

  by_cases hX : M.FinRk X
  · obtain ⟨I, hI⟩ := hX.exists_finset_basis'
    exact le_iSup₂_of_le (i := I) hI.subset <| by rw [hI.eRk_eq_eRk]

  obtain ⟨I, hI⟩ := M.exists_basis' X
  rw [← eRk_eq_top_iff] at hX
  rw [hX, top_le_iff, ← WithTop.forall_ge_iff_eq_top]
  intro n
  rw [hI.eRk_eq_encard, encard_eq_top_iff] at hX
  obtain ⟨J, hJI, rfl⟩ := hX.exists_subset_card_eq n
  apply le_iSup₂_of_le J (hJI.trans hI.subset)
  rw [(hI.indep.subset hJI).eRk_eq_encard, encard_coe_eq_coe_finsetCard]
  rfl

lemma FinRk.basis_of_subset_closure_of_subset_of_encard_le (hX : M.FinRk X) (hXI : X ⊆ M.closure I)
    (hIX : I ⊆ X) (hI : I.encard ≤ M.eRk X) : M.Basis I X := by
  obtain ⟨J, hJ⟩ := M.exists_basis (I ∩ M.E)
  have hIJ := hJ.subset.trans inter_subset_left
  rw [← closure_inter_ground] at hXI
  replace hXI := hXI.trans <| M.closure_subset_closure_of_subset_closure hJ.subset_closure
  have hJX := hJ.indep.basis_of_subset_of_subset_closure (hIJ.trans hIX) hXI
  rw [← hJX.encard_eq_eRk] at hI
  rwa [← Finite.eq_of_subset_of_encard_le' (hX.finite_of_basis hJX) hIJ hI]

lemma FinRk.closure_eq_closure_of_subset_of_eRk_ge_eRk (hX : M.FinRk X) (hXY : X ⊆ Y)
    (hr : M.eRk Y ≤ M.eRk X) : M.closure X = M.closure Y := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_basis'_of_subset (hI.subset.trans hXY)
  rw [hI.eRk_eq_encard, hJ.eRk_eq_encard] at hr
  rw [← closure_inter_ground, ← M.closure_inter_ground Y,
    ← hI.basis_inter_ground.closure_eq_closure,
    ← hJ.basis_inter_ground.closure_eq_closure, Finite.eq_of_subset_of_encard_le'
      (hI.indep.finite_of_subset_finRk hI.subset hX) hIJ hr]

lemma eRk_union_eq_of_subset_of_eRk_le_eRk (Z : Set α) (hXY : X ⊆ Y) (hr : M.eRk Y ≤ M.eRk X) :
    M.eRk (X ∪ Z) = M.eRk (Y ∪ Z) := by
  obtain hX' | hX' := em (M.FinRk X)
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

lemma not_finRk_of_eRk_ge (h : ¬M.FinRk X) (hXY : M.eRk X ≤ M.eRk Y) : ¬M.FinRk Y := by
  contrapose! h
  exact eRk_lt_top_iff.1 <| hXY.trans_lt h.eRk_lt_top

lemma eRank_lt_top (M : Matroid α) [FiniteRk M] : M.eRank < ⊤ := by
  rwa [eRank_def, eRk_lt_top_iff, finRk_ground_iff_finiteRk]

lemma FinRk.indep_of_encard_le_eRk (hX : M.FinRk I) (h : encard I ≤ M.eRk I) : M.Indep I := by
  rw [indep_iff_eRk_eq_encard_of_finite _]
  · exact (M.eRk_le_encard I).antisymm h
  simpa using h.trans_lt hX.eRk_lt_top
