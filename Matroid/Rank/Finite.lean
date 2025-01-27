import Mathlib.Data.Matroid.Closure

variable {α ι : Type*} {M : Matroid α} {B X X' Y Y' I J : Set α} {e : α}

open Set Cardinal

@[simp] lemma Cardinal.toENat_mk (X : Set α) : (Cardinal.mk X).toENat = X.encard := rfl

namespace Matroid

lemma Basis'.base_restrict (hI : M.Basis' I X) : (M ↾ X).Base I :=
  hI

lemma Basis'.finite_of_finite (hI : M.Basis' I X) (hIfin : I.Finite) (hJ : M.Basis' J X) :
    J.Finite :=
  hI.base_restrict.finite_of_finite hIfin hJ

lemma Basis.finite_of_finite (hI : M.Basis I X) (hIfin : I.Finite) (hJ : M.Basis J X) :
    J.Finite :=
  hI.base_restrict.finite_of_finite hIfin hJ.base_restrict

section FinRk

/-- a `FinRk` set in `M` is one whose bases are all finite. -/
def FinRk (M : Matroid α) (X : Set α) := (M ↾ X).FiniteRk

lemma FinRk.finiteRk (hX : M.FinRk X) : (M ↾ X).FiniteRk :=
  hX

lemma FinRk.finite_of_basis' (h : M.FinRk X) (hI : M.Basis' I X) : I.Finite :=
  have := h.finiteRk
  (base_restrict_iff'.2 hI).finite

lemma FinRk.finite_of_basis (h : M.FinRk X) (hI : M.Basis I X) : I.Finite :=
  h.finite_of_basis' hI.basis'

lemma Basis'.finite_of_finRk (hI : M.Basis' I X) (h : M.FinRk X) : I.Finite :=
  h.finite_of_basis' hI

lemma Basis.finite_of_finRk (hI : M.Basis I X) (h : M.FinRk X) : I.Finite :=
  h.finite_of_basis hI

lemma Basis'.finRk_of_finite (hI : M.Basis' I X) (hIfin : I.Finite) : M.FinRk X :=
  ⟨I, hI, hIfin⟩

lemma Basis.finRk_of_finite (hI : M.Basis I X) (hIfin : I.Finite) : M.FinRk X :=
  ⟨I, hI.basis', hIfin⟩

lemma Basis'.finite_iff_finRk (hI : M.Basis' I X) : I.Finite ↔ M.FinRk X :=
  ⟨hI.finRk_of_finite, fun h ↦ h.finite_of_basis' hI⟩

lemma Basis.finite_iff_finRk (hI : M.Basis I X) : I.Finite ↔ M.FinRk X :=
  hI.basis'.finite_iff_finRk

lemma FinRk.exists_finite_basis' (h : M.FinRk X) : ∃ I, M.Basis' I X ∧ I.Finite :=
  h.exists_finite_base

lemma FinRk.exists_finset_basis' (h : M.FinRk X) : ∃ (I : Finset α), M.Basis' I X := by
  obtain ⟨I, hI⟩ := h.exists_finite_basis'
  exact ⟨hI.2.toFinset, by simpa using hI.1⟩

lemma finRk_iff_exists_basis' : M.FinRk X ↔ ∃ I, M.Basis' I X ∧ I.Finite :=
  ⟨FinRk.exists_finite_basis', fun ⟨_, hIX, hI⟩ ↦ hIX.finRk_of_finite hI⟩

lemma FinRk.subset (h : M.FinRk X) (hXY : Y ⊆ X) : M.FinRk Y := by
  obtain ⟨I, hI⟩ := M.exists_basis' Y
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_basis'_of_subset (hI.subset.trans hXY)
  exact hI.finRk_of_finite <| (hJ.finite_of_finRk h).subset hIJ

@[simp] lemma finRk_inter_ground_iff : M.FinRk (X ∩ M.E) ↔ M.FinRk X :=
  let ⟨_I, hI⟩ := M.exists_basis' X
  ⟨fun h ↦ hI.finRk_of_finite (hI.basis_inter_ground.finite_of_finRk h),
    fun h ↦ h.subset inter_subset_left⟩

lemma FinRk.to_inter_ground (h : M.FinRk X) : M.FinRk (X ∩ M.E) :=
  finRk_inter_ground_iff.2 h

lemma finRk_iff (hX : X ⊆ M.E := by aesop_mat) : M.FinRk X ↔ ∃ I, M.Basis I X ∧ I.Finite := by
  simp_rw [finRk_iff_exists_basis', M.basis'_iff_basis hX]

lemma Indep.finRk_iff_finite (hI : M.Indep I) : M.FinRk I ↔ I.Finite :=
  hI.basis_self.finite_iff_finRk.symm

lemma Indep.finite_of_finRk (hI : M.Indep I) (hfin : M.FinRk I) : I.Finite :=
  hI.basis_self.finite_of_finRk hfin

lemma finRk_of_finite (M : Matroid α) (hX : X.Finite) : M.FinRk X :=
  let ⟨_, hI⟩ := M.exists_basis' X
  hI.finRk_of_finite (hX.subset hI.subset)

lemma Indep.subset_finite_basis'_of_subset_of_finRk (hI : M.Indep I) (hIX : I ⊆ X)
    (hX : M.FinRk X) : ∃ J, M.Basis' J X ∧ I ⊆ J ∧ J.Finite :=
  (hI.subset_basis'_of_subset hIX).imp fun _ hJ => ⟨hJ.1, hJ.2, hJ.1.finite_of_finRk hX⟩

lemma Indep.subset_finite_basis_of_subset_of_finRk (hI : M.Indep I) (hIX : I ⊆ X)
    (hX : M.FinRk X) (hXE : X ⊆ M.E := by aesop_mat) : ∃ J, M.Basis J X ∧ I ⊆ J ∧ J.Finite :=
  (hI.subset_basis_of_subset hIX).imp fun _ hJ => ⟨hJ.1, hJ.2, hJ.1.finite_of_finRk hX⟩

lemma finRk_singleton (M : Matroid α) (e : α) : M.FinRk {e} :=
  finRk_of_finite M (finite_singleton e)

@[simp] lemma FinRk.empty (M : Matroid α) : M.FinRk ∅ :=
  finRk_of_finite M finite_empty

lemma not_finRk_superset (h : ¬M.FinRk X) (hXY : X ⊆ Y) : ¬M.FinRk Y :=
  fun h' ↦ h (h'.subset hXY)

lemma FinRk.finite_of_indep_subset (hX : M.FinRk X) (hI : M.Indep I) (hIX : I ⊆ X) : I.Finite :=
  hI.finite_of_finRk (hX.to_inter_ground.subset (subset_inter hIX hI.subset_ground))

@[simp] lemma finRk_ground_iff_finiteRk : M.FinRk M.E ↔ M.FiniteRk := by
  rw [FinRk, restrict_ground_eq_self]

lemma finRk_ground (M : Matroid α) [FiniteRk M] : M.FinRk M.E := by
  rwa [finRk_ground_iff_finiteRk]

lemma Indep.finite_of_subset_finRk (hI : M.Indep I) (hIX : I ⊆ X) (hX : M.FinRk X) : I.Finite :=
  hX.finite_of_indep_subset hI hIX

lemma FinRk.closure (h : M.FinRk X) : M.FinRk (M.closure X) :=
  let ⟨_, hI⟩ := M.exists_basis' X
  hI.basis_closure_right.finRk_of_finite <| hI.finite_of_finRk h

@[simp] lemma FinRk.closure_iff : M.FinRk (M.closure X) ↔ M.FinRk X := by
  rw [← finRk_inter_ground_iff (X := X)]
  exact ⟨fun h ↦ h.subset <| M.inter_ground_subset_closure X, fun h ↦ by simpa using h.closure⟩

lemma FinRk.union (hX : M.FinRk X) (hY : M.FinRk Y) : M.FinRk (X ∪ Y) := by
  obtain ⟨I, hI, hIfin⟩ := hX.exists_finite_basis'
  obtain ⟨J, hJ, hJfin⟩ := hY.exists_finite_basis'
  rw [← finRk_inter_ground_iff]
  refine (M.finRk_of_finite (hIfin.union hJfin)).closure.subset ?_
  rw [closure_union_congr_left hI.closure_eq_closure,
    closure_union_congr_right hJ.closure_eq_closure]
  exact inter_ground_subset_closure M (X ∪ Y)

lemma FinRk.finRk_union_iff (hX : M.FinRk X) : M.FinRk (X ∪ Y) ↔ M.FinRk Y :=
  ⟨fun h ↦ h.subset subset_union_right, fun h ↦ hX.union h⟩

lemma FinRk.finRk_diff_iff (hX : M.FinRk X) : M.FinRk (Y \ X) ↔ M.FinRk Y := by
  rw [← hX.finRk_union_iff, union_diff_self, hX.finRk_union_iff]

lemma FinRk.inter_right (hX : M.FinRk X) : M.FinRk (X ∩ Y) :=
  hX.subset inter_subset_left

lemma FinRk.inter_left (hX : M.FinRk X) : M.FinRk (Y ∩ X) :=
  hX.subset inter_subset_right

lemma FinRk.diff (hX : M.FinRk X) : M.FinRk (X \ Y) :=
  hX.subset diff_subset

lemma FinRk.insert (hX : M.FinRk X) (e : α) : M.FinRk (insert e X) := by
  rw [← union_singleton]; exact hX.union (M.finRk_singleton e)

@[simp] lemma finRk_insert_iff {e : α} : M.FinRk (insert e X) ↔ M.FinRk X := by
  rw [← singleton_union, (M.finRk_singleton e).finRk_union_iff]

@[simp] lemma FinRk.diff_singleton_iff : M.FinRk (X \ {e}) ↔ M.FinRk X := by
  rw [(M.finRk_singleton e).finRk_diff_iff]

lemma to_finRk (M : Matroid α) [FiniteRk M] (X : Set α) : M.FinRk X :=
  let ⟨_, hI⟩ := M.exists_basis' X
  hI.finRk_of_finite hI.indep.finite

lemma FinRk.iUnion [Fintype ι] {Xs : ι → Set α} (h : ∀ i, M.FinRk (Xs i)) :
    M.FinRk (⋃ i, Xs i) := by
  choose Is hIs using fun i ↦ M.exists_basis' (Xs i)
  have hfin : (⋃ i, Is i).Finite := finite_iUnion <| fun i ↦ (h i).finite_of_basis' (hIs i)
  refine finRk_inter_ground_iff.1 <| (M.finRk_of_finite hfin).closure.subset ?_
  rw [iUnion_inter, iUnion_subset_iff]
  exact fun i ↦ (hIs i).basis_inter_ground.subset_closure.trans <| M.closure_subset_closure <|
    subset_iUnion ..


end FinRk
